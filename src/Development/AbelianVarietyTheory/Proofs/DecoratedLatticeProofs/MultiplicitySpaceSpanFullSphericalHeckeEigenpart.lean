module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrXLeKOOfPrCat
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdeleCharacterEqOneIntegralUnitsUnramifiedAdelic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CuspidalSubspaceClosedRightTranslationStable
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CountedVectorIsCuspForm
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnLevelStabTriv
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TranslateToSecondModelCuspFormMapValueAutomorphi
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelIteratedIntegralsSwap
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteResidueField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffHeckePolyOfComplex

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MultiplicitySpaceSpanFullSphericalHeckeEigenpart
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MultiplicitySpaceSpanFullSphericalHeckeEigenpart
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OntoDecomp

theorem iSup_jointEigenspace_eq_top {E I : Type} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    (ip : E → E → ℂ) (hlin : ∀ x y z (c : ℂ), ip x (y + c • z) = ip x y + c * ip x z)
    (hherm : ∀ x y, ip y x = star (ip x y)) (hpos : ∀ x, x ≠ 0 → 0 < (ip x x).re)
    (op : I → Module.End ℂ E) (hc : ∀ i j, Commute (op i) (op j))
    (hadj : ∀ i, ∃ i', ∀ x y, ip (op i x) y = ip x (op i' y)) :
    (⨆ x : I → ℂ, ⨅ i, (op i).eigenspace (x i)) = ⊤ := by
  have hzero : ∀ x, ip x 0 = 0 := fun x => by
    have := hlin x 0 0 1
    simp only [one_smul, add_zero, one_mul] at this
    linear_combination (-1 : ℂ) * this
  have hadd : ∀ x y z, ip (x + y) z = ip x z + ip y z := fun x y z => by
    rw [hherm z (x + y), hherm z x, hherm z y]
    have := hlin z x y 1
    simp only [one_smul, one_mul] at this
    rw [this, star_add]
  have hsmul : ∀ x y (r : ℂ), ip (r • x) y = conj r * ip x y := fun x y r => by
    rw [hherm y (r • x), hherm y x]
    have := hlin y 0 x r
    simp only [zero_add, hzero, zero_add] at this
    rw [this, star_mul, mul_comm]
    rfl
  let core : InnerProductSpace.Core ℂ E :=
    { inner := ip
      conj_inner_symm := fun x y => by rw [hherm y x]; rfl
      re_inner_nonneg := fun x => by
        by_cases h : x = 0
        · subst h
          have := hzero 0
          simp [this]
        · exact (hpos x h).le
      add_left := hadd
      smul_left := hsmul
      definite := fun x hx => by
        by_contra h
        have := hpos x h
        rw [hx] at this
        simp at this }
  letI : NormedAddCommGroup E := InnerProductSpace.Core.toNormedAddCommGroup (cd := core)
  letI : InnerProductSpace ℂ E := InnerProductSpace.ofCore core.toCore
  have hin : ∀ x y : E, inner ℂ x y = ip x y := fun _ _ => rfl
  have h := GlobalTheory.normalFamily_orthogonal_decomposition op (fun i j => hc i j) (fun i => by
    obtain ⟨i', hi'⟩ := hadj i
    refine ⟨i', (LinearMap.eq_adjoint_iff _ _).2 fun x y => ?_⟩
    rw [hin, hin, hherm, ← hi' y x, hherm (op i y)])
  rw [← h.2.1]
  exact iSup_congr fun x => (h.1 x).symm

end GlobalTheory.OntoDecomp

namespace GlobalTheory.OntoDecomp

theorem multT_span_partFull : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, FinDim D → LevFacts D → ForStage D fun c _ s =>
    Submodule.span ℂ {u : s.CC c | ∃ e : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ,
      PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) ∈
        partFull c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) c.S e} = ⊤ := by
  classical
  intro hP D hfd hlev c hc j hj s hs
  obtain ⟨-, -, hsplit, -, hunif⟩ := GlobalTheory.T.thetaChainStage_level_spherical_off_set D c hc j hj s hs
  have hmul := (hlev c hc j hj s hs).2.2.2.2.1
  have hops := GlobalTheory.SphericalOps.spherical_ops s.V c.θ s.M (Lev.levG s.V s.β s.L) (Lev.levChi s.V s.β s.L) c.S
    hunif hc.inf hmul hsplit
  have hJ : levS s.V s.β s.L = ((Lev.levG s.V s.β s.L : Subgroup (GA D s.V)) : Set (GA D s.V)) := rfl
  rw [← hJ] at hops
  obtain ⟨hLU, -, hH⟩ := hops
  by_cases hsm : ∀ τ, s.M.sm τ ≠ ⊥
  swap
  · push_neg at hsm
    obtain ⟨τ, hτ⟩ := hsm
    refine Submodule.eq_top_iff'.2 fun u => ?_
    have h0 : PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) = 0 := by
      refine MultilinearMap.ext fun v => ?_
      rw [MultilinearMap.zero_apply]
      have hv : ((v τ : s.M.sm τ) : s.M.H τ) = 0 := (Submodule.eq_bot_iff _).1 hτ _ (v τ).2
      exact MultilinearMap.map_coord_zero (PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ))) τ
        (Subtype.ext hv)
    have h1 := LinearEquiv.apply_symm_apply PiTensorProduct.lift (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ))
    rw [h0, map_zero] at h1
    have : u = 0 := Subtype.ext h1.symm
    rw [this]
    exact zero_mem _
  have hschur := GlobalTheory.MultFinite.schurMult (θ := c.θ) (M := s.M) (J := levS s.V s.β s.L)
    (χ := Lev.levChi s.V s.β s.L) hP s.ν s.fd
  haveI := hs.haar
  have hright : s.ν.IsMulRightInvariant := Formalism.IndefR.Eqv.unimodGA_holds s.V s.ν hs.haar
  obtain ⟨hlin, hpos⟩ := GlobalTheory.SchurConst.ipM_posDef D c.θ s.V s.par s.M (levS s.V s.β s.L)
    (Lev.levChi s.V s.β s.L) s.ν s.fd hc.inf hs.haar hs.fund hschur hsm
  obtain ⟨v0, hv0⟩ := GlobalTheory.SchurConst.exists_vec s.M hsm
  have hspec : ∀ T ∈ Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L),
      ∀ T' ∈ Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L),
      IsMultIP s.M s.ν s.fd T T' (ipM s.M s.ν s.fd T T') := fun T hT T' hT' =>
    ipM_spec _ _ _ _ _ (hschur hc.inf hs.haar hs.fund T hT T' hT')
  let φ := Submodule.equivMapOfInjective (PiTensorProduct.lift : MMap s.M ≃ₗ[ℂ] _).toLinearMap
    (LinearEquiv.injective _) (Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L))
  haveI : FiniteDimensional ℂ ((Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L)).map
      (PiTensorProduct.lift : MMap s.M ≃ₗ[ℂ] _).toLinearMap) := hfd c hc j hj s hs
  haveI : FiniteDimensional ℂ (Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L)) :=
    LinearEquiv.finiteDimensional φ.symm
  let I := {t : HeightOneSpectrum (𝓞 D.host.E) × List ℤ × Finset (GA D s.V) //
    Hecke₂ s.V (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) c.S t.1 t.2.1 t.2.2}
  let op : I → Module.End ℂ (Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L)) := fun t =>
    (heckeOn s.M t.1.2.2).restrict fun T hT => (hH _ _ _ t.2).1 T hT
  have hcomm : ∀ i j, Commute (op i) (op j) := fun i j => by
    refine LinearMap.ext fun T => Subtype.ext ?_
    exact (hH _ _ _ i.2).2.1 _ _ _ j.2 T T.2
  have hadj : ∀ i, ∃ i', ∀ x y : Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L),
      ipM s.M s.ν s.fd (op i x : MMap s.M) y = ipM s.M s.ν s.fd x (op i' y : MMap s.M) := fun i => by
    obtain ⟨R', h', hip⟩ := (hH _ _ _ i.2).2.2
    refine ⟨⟨(i.1.1, dualLab i.1.2.1, R'), h'⟩, fun x y => ?_⟩
    have h1 := hspec _ ((hH _ _ _ i.2).1 x x.2) y y.2
    have h2 := (hip s.ν s.fd hs.haar hright hs.fund hschur x x.2 y y.2 _).1 h1
    have h3 := hspec x x.2 _ ((hH _ _ _ h').1 y y.2)
    exact hasPeterssonInner_unique s.M s.ν s.fd _ _ v0 hv0 h2 h3
  have htop := iSup_jointEigenspace_eq_top
    (fun x y : Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) => ipM s.M s.ν s.fd x y)
    (fun x y z a => (hlin x x.2 y y.2 z z.2 a).1) (fun x y => (hlin x x.2 y y.2 y y.2 0).2)
    (fun x hx => hpos x x.2 fun h => hx (Subtype.ext h)) op hcomm hadj
  have hsub : ∀ x : I → ℂ, ∀ T ∈ ⨅ i, (op i).eigenspace (x i), ∃ e : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ,
      (T : MMap s.M) ∈ partFull c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) c.S e := by
    classical
    intro x T hT
    refine ⟨fun P d => if h : ∃ R, Hecke₂ s.V (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) c.S P d R
      then x ⟨(P, d, h.choose), h.choose_spec⟩ else 0, ?_⟩
    rw [mem_partFull]
    refine ⟨T.2, fun P d R hR v => ?_⟩
    have hex : ∃ R, Hecke₂ s.V (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) c.S P d R := ⟨R, hR⟩
    rw [dite_eq_left hex]
    have hlevT := ((GlobalTheory.MultMem.mem_mult_iff ..).1 T.2).lev v
    rw [hLU P d R hex.choose hR hex.choose_spec _ hlevT]
    have h1 := (Submodule.mem_iInf _).1 hT ⟨(P, d, hex.choose), hex.choose_spec⟩
    rw [Module.End.mem_eigenspace_iff] at h1
    exact congrArg (fun U : Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) => (U : MMap s.M) v) h1
  rw [eq_top_iff]
  rintro u -
  obtain ⟨T, rfl⟩ := φ.surjective u
  have hT : T ∈ (⊤ : Submodule ℂ (Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L))) := trivial
  rw [← htop] at hT
  refine Submodule.iSup_induction (fun x : I → ℂ => ⨅ i, (op i).eigenspace (x i))
    (motive := fun T => φ T ∈ Submodule.span ℂ {u : s.CC c | ∃ e : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ,
      PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) ∈
        partFull c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) c.S e}) hT ?_ ?_ ?_
  · intro x T hT
    obtain ⟨e, he⟩ := hsub x T hT
    refine Submodule.subset_span ⟨e, ?_⟩
    have : ((φ T : s.CC c) : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) = PiTensorProduct.lift (T : MMap s.M) := rfl
    rw [this, LinearEquiv.symm_apply_apply]
    exact he
  · rw [φ.map_zero]; exact zero_mem _
  · intro a b ha hb; rw [φ.map_add]; exact add_mem ha hb

end GlobalTheory.OntoDecomp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MultiplicitySpaceSpanFullSphericalHeckeEigenpartStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicitySpace_span_fullSphericalHecke_eigenparts : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, FinDim D → LevFacts D → ForStage D fun c _ s => Submodule.span ℂ {u : s.CC c | ∃ e : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ, PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) ∈ partFull c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) c.S e} = ⊤ := by
  first | exact @GlobalTheory.OntoDecomp.multT_span_partFull | exact GlobalTheory.OntoDecomp.multT_span_partFull | (intros; apply GlobalTheory.OntoDecomp.multT_span_partFull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SatakeEsymmScaledMultisetAddSegment
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SatakeEsymmScaledMultisetAddSegment
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto

theorem esymm_cons_succ_C (a : ℂ) (s : Multiset ℂ) (n : ℕ) :
    (a ::ₘ s).esymm (n + 1) = s.esymm (n + 1) + a * s.esymm n := by
  simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_map, Multiset.sum_map_mul_left]

theorem coeff_prod_one_add_C (s : Multiset ℂ) (n : ℕ) :
    ((s.map fun a => (1 + Polynomial.C a * Polynomial.X : Polynomial ℂ)).prod).coeff n = s.esymm n := by
  induction s using Multiset.induction_on generalizing n with
  | empty =>
    cases n with
    | zero => simp [Multiset.esymm]
    | succ n => simp [Multiset.esymm, Polynomial.coeff_one, Multiset.powersetCard_zero_right]
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, add_mul, one_mul, mul_assoc, Polynomial.coeff_add,
      Polynomial.coeff_C_mul]
    cases n with
    | zero => simp [ih, Multiset.esymm]
    | succ n => rw [Polynomial.coeff_X_mul, ih, ih, esymm_cons_succ_C]

theorem esymm_add_C (s t : Multiset ℂ) (n : ℕ) :
    (s + t).esymm n = ∑ i ∈ Finset.range (n + 1), s.esymm i * t.esymm (n - i) := by
  rw [← coeff_prod_one_add_C, Multiset.map_add (f := _), Multiset.prod_add, Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_prod_one_add_C]

theorem esymm_map_mul_C (c : ℂ) (s : Multiset ℂ) (k : ℕ) :
    (s.map (fun x => c * x)).esymm k = c ^ k * s.esymm k := by
  have h := Multiset.pow_smul_esymm c k s
  simpa [smul_eq_mul] using h.symm

theorem esymm_eq_zero_of_lt (s : Multiset ℂ) {k : ℕ} (h : s.card < k) : s.esymm k = 0 := by
  simp [Multiset.esymm, Multiset.powersetCard_eq_empty k h]

theorem natCast_cpow_half (Q : ℕ) (m : ℤ) :
    (Q : ℂ) ^ ((m : ℂ) / 2) = ((Real.sqrt Q : ℝ) : ℂ) ^ m := by
  have h1 : ((Real.sqrt Q : ℝ) : ℂ) = (Q : ℂ) ^ ((1 / 2 : ℂ)) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (Nat.cast_nonneg _)]
    push_cast
    rfl
  rw [h1, ← Complex.cpow_int_mul]
  congr 1
  ring

theorem sqrt_sq_C (Q : ℕ) : ((Real.sqrt Q : ℝ) : ℂ) ^ 2 = (Q : ℂ) := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  push_cast
  rfl

theorem esymm_string (Q : ℕ) (s z : ℂ) (hs : s ≠ 0) (hQ : s ^ 2 = (Q : ℂ)) (t : ℕ) :
    ∀ l : ℕ, ((Finset.range t).val.map fun i : ℕ => z * s ^ ((t : ℤ) - 1 - 2 * i)).esymm l =
      z ^ l * s ^ (-((l : ℤ) * ((t : ℤ) - l))) * (Formalism.L2.Col.gaussBin Q t l : ℂ) := by
  induction t with
  | zero =>
    intro l
    cases l with
    | zero => simp [Multiset.esymm, Formalism.L2.Col.gaussBin]
    | succ l => simp [Multiset.esymm, Formalism.L2.Col.gaussBin, Multiset.powersetCard_zero_right]
  | succ t ih =>
    intro l
    have hm : ((Finset.range (t + 1)).val.map fun i : ℕ => z * s ^ (((t + 1 : ℕ) : ℤ) - 1 - 2 * i)) =
        (z * s ^ (-(t : ℤ))) ::ₘ (((Finset.range t).val.map fun i : ℕ => z * s ^ ((t : ℤ) - 1 - 2 * i)).map
          fun x => s * x) := by
      rw [Finset.range_val, Finset.range_val, Multiset.range_succ, Multiset.map_cons, Multiset.map_map]
      congr 1
      · congr 1; congr 1; push_cast; ring
      · refine Multiset.map_congr rfl fun i _ => ?_
        simp only [Function.comp_apply]
        rw [mul_left_comm]
        congr 1
        rw [show (((t + 1 : ℕ) : ℤ) - 1 - 2 * i) = 1 + ((t : ℤ) - 1 - 2 * i) by push_cast; ring,
          zpow_add₀ hs, zpow_one]
    rw [hm]
    cases l with
    | zero => simp [Multiset.esymm, Formalism.L2.Col.gaussBin]
    | succ l =>
      rw [esymm_cons_succ_C, esymm_map_mul_C, esymm_map_mul_C, ih, ih, Formalism.L2.Col.gaussBin]
      push_cast
      rw [← hQ]
      have h1 : s ^ (l + 1) * s ^ (-(((l : ℤ) + 1) * ((t : ℤ) - ((l : ℤ) + 1)))) =
          s ^ (-(((l : ℤ) + 1) * ((t : ℤ) + 1 - ((l : ℤ) + 1)))) * (s ^ 2) ^ (l + 1) := by
        rw [← pow_mul, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hs, ← zpow_add₀ hs]
        congr 1; push_cast; ring
      have h2 : s ^ (-(t : ℤ)) * s ^ l * s ^ (-((l : ℤ) * ((t : ℤ) - l))) =
          s ^ (-(((l : ℤ) + 1) * ((t : ℤ) + 1 - ((l : ℤ) + 1)))) := by
        rw [← zpow_natCast, ← zpow_add₀ hs, ← zpow_add₀ hs]
        congr 1; push_cast; ring
      linear_combination (z ^ (l + 1) * (Formalism.L2.Col.gaussBin Q t (l + 1) : ℂ)) * h1 +
        (z ^ (l + 1) * (Formalism.L2.Col.gaussBin Q t l : ℂ)) * h2

theorem map_coe_seg (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (z : ℂˣ) (t : ℕ) :
    (seg w z t).map (fun b : ℂˣ => (b : ℂ)) =
      (Finset.range t).val.map fun i : ℕ => (z : ℂ) * ((Real.sqrt (qV E w) : ℝ) : ℂ) ^ ((t : ℤ) - 1 - 2 * i) := by
  rw [seg, Multiset.map_map]
  refine Multiset.map_congr rfl fun i _ => ?_
  simp only [Function.comp_apply, Units.val_mul, coe_npowU, npow]
  congr 1
  rw [← natCast_cpow_half]
  show ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ _ = ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ _
  congr 1
  push_cast
  ring

theorem satEig_map_add_seg : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (a t k : ℕ) (B : Multiset ℂˣ) (z y : ℂˣ), B.card = a → k ≤ a + t → satEig (qV E w) (a + t) (B.map (z * y⁻¹ * ·) + seg w z t) k = ∑ j ∈ Finset.range (a + 1), (if j ≤ k then (qV E w : ℂ) ^ ((a - j) * (k - j)) * (Formalism.L2.Col.gaussBin (qV E w) t (k - j) : ℂ) * ((z : ℂ) * ((Real.sqrt (qV E w) : ℂ) ^ a)⁻¹) ^ k * (((y : ℂ))⁻¹ * (Real.sqrt (qV E w) : ℂ) ^ (a + t)) ^ j else 0) * satEig (qV E w) a B j := by
  intro E _ _ w a t k B z y hB _
  have hsQ := sqrt_sq_C (qV E w)
  have hs : ((Real.sqrt (qV E w) : ℝ) : ℂ) ≠ 0 := by
    intro h0
    rw [h0] at hsQ
    have h1 : 1 < qV E w := one_lt_absNorm w
    have : ((qV E w : ℕ) : ℂ) = 0 := by rw [← hsQ]; ring
    exact (by omega : qV E w ≠ 0) (by exact_mod_cast this)
  have hA : (B.map (z * y⁻¹ * ·)).map (fun b : ℂˣ => (b : ℂ)) =
      (B.map fun b : ℂˣ => (b : ℂ)).map fun x => ((z : ℂ) * (y : ℂ)⁻¹) * x := by
    simp [Multiset.map_map, Function.comp_def]
  have hBc : (B.map fun b : ℂˣ => (b : ℂ)).card = a := by simp [hB]
  set Q := qV E w with hQdef
  set s : ℂ := ((Real.sqrt Q : ℝ) : ℂ) with hsdef
  set F : ℕ → ℂ := fun j => (if j ≤ k then (Q : ℂ) ^ ((a - j) * (k - j)) * (Formalism.L2.Col.gaussBin Q t (k - j) : ℂ) *
    ((z : ℂ) * (s ^ a)⁻¹) ^ k * (((y : ℂ))⁻¹ * s ^ (a + t)) ^ j else 0) * satEig Q a B j with hF
  have hFa : ∀ j, a < j → F j = 0 := by
    intro j hj
    simp only [hF, satEig, esymm_eq_zero_of_lt _ (hBc ▸ hj), mul_zero]
  have hFk : ∀ j, k < j → F j = 0 := by
    intro j hj
    simp only [hF, if_neg (show ¬ j ≤ k by omega), zero_mul]
  have hR : ∑ j ∈ Finset.range (a + 1), F j = ∑ j ∈ Finset.range (k + 1), F j := by
    rw [Finset.sum_subset (Finset.range_mono (show a + 1 ≤ a + k + 1 by omega))
        (fun j _ hn => hFa j (by simp at hn; omega)),
      Finset.sum_subset (Finset.range_mono (show k + 1 ≤ a + k + 1 by omega))
        (fun j _ hn => hFk j (by simp at hn; omega))]
  rw [hR, satEig, Multiset.map_add (f := _), esymm_add_C, Finset.mul_sum, hA, map_coe_seg]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjk : j ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  rw [esymm_map_mul_C, esymm_string Q s z hs hsQ t]
  by_cases hja : j ≤ a
  · simp only [hF, if_pos hjk, satEig]
    have c1 : (Q : ℂ) ^ (((k : ℂ) * (((a + t : ℕ) : ℂ) - k)) / 2) = s ^ ((k : ℤ) * ((a : ℤ) + t - k)) := by
      rw [← natCast_cpow_half]; congr 1; push_cast; ring
    have c2 : (Q : ℂ) ^ (((j : ℂ) * ((a : ℂ) - j)) / 2) = s ^ ((j : ℤ) * ((a : ℤ) - j)) := by
      rw [← natCast_cpow_half]; congr 1; push_cast; ring
    rw [c1, c2]
    have hz : ((z : ℂ) * (y : ℂ)⁻¹) ^ j * (z : ℂ) ^ (k - j) = (z : ℂ) ^ k * ((y : ℂ)⁻¹) ^ j := by
      rw [mul_pow, mul_right_comm, ← pow_add, Nat.add_sub_cancel' hjk]
    have hsI : s ^ ((k : ℤ) * ((a : ℤ) + t - k)) * s ^ (-(((k - j : ℕ) : ℤ) * ((t : ℤ) - ((k - j : ℕ) : ℤ)))) =
        (s ^ 2) ^ ((a - j) * (k - j)) * ((s ^ a)⁻¹) ^ k * (s ^ (a + t)) ^ j * s ^ ((j : ℤ) * ((a : ℤ) - j)) := by
      simp only [← pow_mul, inv_pow, ← zpow_natCast, ← _root_.zpow_neg, ← _root_.zpow_mul, ← zpow_add₀ hs]
      congr 1
      push_cast [Nat.cast_sub hja, Nat.cast_sub hjk]
      ring
    calc _ = (s ^ ((k : ℤ) * ((a : ℤ) + t - k)) * s ^ (-(((k - j : ℕ) : ℤ) * ((t : ℤ) - ((k - j : ℕ) : ℤ))))) *
          (((z : ℂ) * (y : ℂ)⁻¹) ^ j * (z : ℂ) ^ (k - j)) *
          ((Formalism.L2.Col.gaussBin Q t (k - j) : ℂ) * (B.map fun b : ℂˣ => (b : ℂ)).esymm j) := by ring
      _ = ((s ^ 2) ^ ((a - j) * (k - j)) * ((s ^ a)⁻¹) ^ k * (s ^ (a + t)) ^ j * s ^ ((j : ℤ) * ((a : ℤ) - j))) *
          ((z : ℂ) ^ k * ((y : ℂ)⁻¹) ^ j) *
          ((Formalism.L2.Col.gaussBin Q t (k - j) : ℂ) * (B.map fun b : ℂˣ => (b : ℂ)).esymm j) := by rw [hsI, hz]
      _ = _ := by rw [hsQ]; ring
  · rw [esymm_eq_zero_of_lt _ (by omega), hFa j (by omega)]
    ring

end GlobalTheory.ChainOnto
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SatakeEsymmScaledMultisetAddSegmentStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.satake_esymm_scaled_multiset_add_segment : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (a t k : ℕ) (B : Multiset ℂˣ) (z y : ℂˣ), B.card = a → k ≤ a + t → satEig (qV E w) (a + t) (B.map (z * y⁻¹ * ·) + seg w z t) k = ∑ j ∈ Finset.range (a + 1), (if j ≤ k then (qV E w : ℂ) ^ ((a - j) * (k - j)) * (Formalism.L2.Col.gaussBin (qV E w) t (k - j) : ℂ) * ((z : ℂ) * ((Real.sqrt (qV E w) : ℂ) ^ a)⁻¹) ^ k * (((y : ℂ))⁻¹ * (Real.sqrt (qV E w) : ℂ) ^ (a + t)) ^ j else 0) * satEig (qV E w) a B j := by
  first | exact @GlobalTheory.ChainOnto.satEig_map_add_seg | exact GlobalTheory.ChainOnto.satEig_map_add_seg | (intros; apply GlobalTheory.ChainOnto.satEig_map_add_seg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateIntertwinerValuesIsCuspFun
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneMemKg
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.Dec.CuspAll

theorem one_mem_Kg (I : AutInst) (g : ℕ) : (1 : I.Gf) ∈ I.Kg g := by
  refine ⟨(Formalism.UG.stabGL I.Lf).one_mem, fun y _ => ⟨0, I.Lf.zero_mem, ?_⟩⟩
  have : I.fmat 1 = 1 := rfl
  simp [this]

theorem re_fixed (B : RowsAut) : ∀ k ∈ B.I.Kg B.g, (B.R (1, k)).comp B.Re = B.Re := by
  intro k hk
  obtain ⟨hT2, -, hsc, -⟩ := GlobalTheory.CongTop.adelic_topology B.I
  obtain ⟨R1, Rm, Rn, -⟩ := GlobalTheory.RightRegFund.rightReg_unitary_continuous B
  obtain ⟨-, -, -, -, -, hinv, -⟩ := B.e_adm
  obtain ⟨-, hT⟩ := B.Re_spec
  have p1 : (fun g : B.I.Gf => B.R (1, g)) 1 = 1 := R1
  have pm : ∀ a b : B.I.Gf, B.R (1, a * b) = B.R (1, a) * B.R (1, b) := by
    intro a b; rw [← Rm]; simp
  have pn : ∀ (g : B.I.Gf) v, ‖B.R (1, g) v‖ = ‖v‖ := fun g v => Rn _ v
  exact GlobalTheory.IdemProj.op_fixed B.μf (fun g => B.R (1, g)) p1 pm pn B.e B.Re hT k
    (fun x => by simpa using hinv x k hk 1 (one_mem_Kg B.I B.g))

theorem integrable_ph (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ) (hd : IsDSData B d)
    (hl : LocDec B h) (hb : HBig B 40 h) : Integrable (ph B d) (muInf B.I) := by
  obtain ⟨hc, hm, hi⟩ := GlobalTheory.Dec.PhMajProof.phMaj B d h hd hl
  have h0 := hi 0 le_rfl (fun v => by
    rcases Nat.eq_zero_or_pos (rkR (B.I.ε v)) with hq | hq
    · exact Or.inl hq
    · right
      have hle : rkR (B.I.ε v) ≤ B.I.n := by
        unfold rkR
        refine (min_le_left _ _).trans ((Finset.card_filter_le _ _).trans (by simp))
      have h1 : (0 : ℝ) < rkR (B.I.ε v) := by exact_mod_cast hq
      have h2 : ((rkR (B.I.ε v) : ℕ) : ℝ) ≤ B.I.n := by exact_mod_cast hle
      have h3 := Real.sqrt_pos.2 h1
      have h4 := hb v
      have h5 : (0 : ℝ) < B.I.n := h1.trans_le h2
      have h6 : (B.I.n : ℝ) * rkR (B.I.ε v) ≤ (B.I.n : ℝ) ^ 2 := by nlinarith
      have h7 : 0 < (B.I.n : ℝ) ^ 2 * Real.sqrt (rkR (B.I.ε v)) := by positivity
      nlinarith [mul_le_mul_of_nonneg_right h6 h3.le])
  simp only [zero_mul, Real.exp_zero, mul_one] at h0
  exact h0.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall hm)

theorem cusp_all : GlobalTheory.DSId.StrictLow → ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → 1 ≤ B.g → (∀ v, 120 * (B.I.n : ℝ) * ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) → LocDec B h → HBig B 40 h → ∀ A ∈ B.I.eHom B.σs B.μf B.fund B.R B.Re, A ∈ B.I.HomS B.σs B.μf B.fund B.R ∧ ∀ u, B.I.IsCuspFn (B.I.muA B.μf) (B.I.ext (A u)) ∧ ∀ k ∈ B.I.Kg B.g, B.R (1, k) (A u) = A u := by
  intro hS B d h hd hg hgap hl hb T hT
  obtain ⟨-, hcomm, ⟨Rφ, hR⟩, -⟩ := GlobalTheory.GlobProj.globalProj_holds B d hd (integrable_ph B d h hd hl hb)
  obtain ⟨-, hirr, -, hw, -⟩ := GlobalTheory.Dec.tensorRep B d hd
  have hle : B.I.eHom B.σs B.μf B.fund B.R B.Re ≤ B.I.HomS B.σs B.μf B.fund B.R := by
    rintro _ ⟨A, hA, rfl⟩ g
    show (B.Re.comp A).comp (B.σs g) = (B.R (g, 1)).comp (B.Re.comp A)
    rw [ContinuousLinearMap.comp_assoc, hA g, ← ContinuousLinearMap.comp_assoc, hcomm g,
      ContinuousLinearMap.comp_assoc]
  obtain ⟨S, hSm, hScl, hSst, -⟩ := GlobalTheory.CuspSubspace.cuspidal_closed_stable B
  refine ⟨hle hT, fun u => ⟨?_, fun k hk => ?_⟩⟩
  · have hw' : T (B.tens B.w) ∈ S := by
      rw [hSm]
      exact GlobalTheory.T.countedVector_isCuspForm hS B d h hd hg hgap hl hb Rφ hR T hT
    have hcl : IsClosed ((S.comap (T : B.Hs →ₗ[ℂ] B.I.L2 B.μf B.fund) : Submodule ℂ B.Hs) : Set B.Hs) :=
      hScl.preimage T.continuous
    rcases hirr _ hcl (fun g v hv => by
      have e := congrArg (fun A : B.Hs →L[ℂ] B.I.L2 B.μf B.fund => A v) (hle hT g)
      simp only [ContinuousLinearMap.comp_apply] at e
      show T (B.σs g v) ∈ S
      rw [e]
      exact hSst _ _ hv) with h0 | h0
    · have : B.tens B.w ∈ S.comap (T : B.Hs →ₗ[ℂ] B.I.L2 B.μf B.fund) := hw'
      rw [h0, Submodule.mem_bot] at this
      rw [this] at hw
      simp at hw
    · have : u ∈ S.comap (T : B.Hs →ₗ[ℂ] B.I.L2 B.μf B.fund) := by rw [h0]; trivial
      exact (hSm _).1 this
  · obtain ⟨A, -, hA⟩ := hT
    rw [← hA]
    exact congrArg (fun C : B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund => C (A u)) (re_fixed B k hk)

end GlobalTheory.Dec.CuspAll
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateIntertwinerValuesIsCuspFun
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ConjRowMultCusp

theorem mem_NI_iff_iota : ∀ (D : D7) {r : ℕ} (C : Matrix (Fin (D.sp.Y 0).rank) (Fin r) D.host.E), IsIsoFrame (D.sp.Y 0) C → ∀ g : GA D (D.sp.Y 0), g ∈ NI (D.sp.Y 0) C ↔ Formalism.IndefR.RationalEmbedding.iota D g ∈ (Formalism.IndefR.RationalEmbedding.inst D).NA (Submodule.span (Formalism.IndefR.RationalEmbedding.inst D).E (Set.range (C : Matrix (Fin (Formalism.IndefR.RationalEmbedding.inst D).n) (Fin r) (Formalism.IndefR.RationalEmbedding.inst D).E).col)) := by
  intro D r C hC g
  let I := Formalism.IndefR.RationalEmbedding.inst D
  let T := (Formalism.IndefR.RationalEmbedding.iota D).toMulEquiv
  obtain ⟨L, R, hL, hR⟩ :=
    GlobalTheory.CuspCompare.exists_inverses (starRingEnd D.host.E) (J := (D.sp.Y 0).gram) I.J_det hC.2.1
  have key : ∀ h : GA D (D.sp.Y 0),
      T h ∈ I.NA (Submodule.span I.E (Set.range (C : Matrix (Fin I.n) (Fin r) I.E).col)) ↔
      GlobalTheory.CuspCompare.UnipEq (incA D) C R (Formalism.UG.cT (starRingEnd D.host.E) C * (D.sp.Y 0).gram) L
        ((matHom (D.sp.Y 0) h).1 - 1) := fun h => by
    have hs : (Formalism.IndefR.RationalEmbedding.iota D).symm (T h) = h := (Formalism.IndefR.RationalEmbedding.iota D).symm_apply_apply h
    refine GlobalTheory.CuspCompare.mem_NA_iff I (fun v => Formalism.IndefR.Eqv.thetaC D ((Formalism.L2.Host.tauPl D).symm v))
      (fun v => Formalism.IndefR.Eqv.isInfFam_thetaC D ((Formalism.L2.Host.tauPl D).symm v)) h (T h) ?_ (fun v => ?_) hL hR
    · have hb := (Formalism.IndefR.RationalEmbedding.iota_symm_isBridge D (T h)).2
      have h2 := hb.trans (congrArg (Formalism.L2.SG.AdBridge.ofHAFin I) hs)
      unfold Formalism.L2.SG.AdBridge.ofHAFin at h2
      rw [Formalism.L2.SG.EvalTIota.tauF_eq_i] at h2
      exact h2
    · obtain ⟨ρ, rfl⟩ := (Formalism.L2.Host.tauPl D).surjective v
      have hb := Formalism.L2.SG.EvalTIota.infMat_brg_i (T h) ρ
      rw [hs] at hb
      simp only [Equiv.symm_apply_apply]
      exact hb.symm
  have hW : I.IsIsot (Submodule.span I.E (Set.range (C : Matrix (Fin I.n) (Fin r) I.E).col)) :=
    (GlobalTheory.CuspCompare.isIsot_iff I _).2 ⟨r, C, hC, rfl⟩
  refine GlobalTheory.CuspCompare.mem_closure_iff_of_equiv T (GlobalTheory.T.strong_approximation_unitaryUnipotentRadical I _ hW).1 (fun g => ?_) g
  rw [key]
  exact and_congr Iff.rfl (and_congr Iff.rfl (GlobalTheory.CuspCompare.perp_cond (incA D) hL hR _).2)

theorem isCuspFun_of_isCuspFn_iota : ∀ (D : D7) (I : Formalism.MainNotions.S.AutInst) (hI : I = Formalism.L2.SG.InstExistsPf.instOf D)
    (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf] (f : I.GA → ℂ), Continuous f →
    (∀ γ ∈ I.GFset, ∀ y, f (γ * y) = f y) → I.IsCuspFn (I.muA μf) f →
    IsCuspFun (D.sp.Y 0) (fun y => f (((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA hI.symm)) y)) := by
  intro D I hI μf _ _ f hf hi hcusp
  subst hI
  have : BorelSpace (GA D (D.sp.Y 0)) := ⟨rfl⟩
  intro r C hC μ 𝓕 hμ h𝓕 g
  have hW : (Formalism.IndefR.RationalEmbedding.inst D).IsIsot (Submodule.span (Formalism.IndefR.RationalEmbedding.inst D).E (Set.range (C : Matrix (Fin (Formalism.IndefR.RationalEmbedding.inst D).n) (Fin r) (Formalism.IndefR.RationalEmbedding.inst D).E).col)) :=
    (GlobalTheory.CuspCompare.isIsot_iff _ _).2 ⟨r, C, hC, rfl⟩
  have key := (GlobalTheory.CuspCompare.constTerm_iff_inst (Formalism.IndefR.RationalEmbedding.inst D) μf
    (Formalism.IndefR.RationalEmbedding.iota D).toMulEquiv ⟨(Formalism.IndefR.RationalEmbedding.iota D).continuous,
      (Formalism.IndefR.RationalEmbedding.iota D).symm.continuous⟩ (GQ (D.sp.Y 0)) (NI (D.sp.Y 0) C)
    (fun g => Formalism.IndefR.RationalEmbedding.iota_rat D g) _ hW (mem_NI_iff_iota D C hC) f hf hi).2
    (fun ν hν => hcusp _ hW ν hν)
  exact key μ 𝓕 hμ h𝓕 g

theorem isCuspFn_of_contRep {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) {F : L2X X} {ψ : X.B.I.GA → ℂ}
    (hψ : Formalism.L2.SG.EvalTOntoRep.IsContRep X F ψ) (hF : X.B.I.IsCuspFn (X.B.I.muA X.B.μf) (X.B.I.ext F)) :
    X.B.I.IsCuspFn (X.B.I.muA X.B.μf) ψ := by
  obtain ⟨hc, hi, he⟩ := hψ
  have hfund := X.B.fund_spec
  obtain ⟨hT, hL, hS, -⟩ := GlobalTheory.CongTop.adelic_topology X.B.I
  obtain ⟨Γ, hΓ, hcΓ, -⟩ := GlobalTheory.T.rationalUnitaryPoints_discrete_fundamentalDomain X.B.I
  obtain ⟨hl, -, -, -, hop⟩ := GlobalTheory.T.adelicUnitaryHaar_bi_invariant X.B.I X.B.μf
  have : BorelSpace X.B.I.GA := inferInstance
  have : (X.B.I.muA X.B.μf).IsMulLeftInvariant := ⟨hl⟩
  have : SFinite (X.B.I.muA X.B.μf) := by unfold Formalism.MainNotions.S.AutInst.muA; infer_instance
  have hr : ∀ y, ∃ γ : Γ, X.B.I.rep X.B.fund y = (γ : X.B.I.GA) * y ∧ X.B.I.rep X.B.fund y ∈ X.B.fund := by
    intro y
    have h := hfund.2.1 y
    have e : X.B.I.rep X.B.fund y = h.choose * y := by
      unfold Formalism.MainNotions.S.AutInst.rep; exact dif_pos h
    have hm : h.choose ∈ (Γ : Set X.B.I.GA) := by
      have k := h.choose_spec.1
      generalize h.choose = z at k ⊢
      rw [hΓ]; exact k
    exact ⟨⟨h.choose, hm⟩, e, e ▸ h.choose_spec.2⟩
  have hext : X.B.I.ext F =ᵐ[X.B.I.muA X.B.μf] ψ := by
    filter_upwards [GlobalTheory.RightRegFund.ae_rep hfund.1 hr he] with y hy
    obtain ⟨γ, h1, -⟩ := hr y
    unfold Formalism.MainNotions.S.AutInst.ext
    rw [hy, h1, hi _ (hΓ ▸ γ.2)]
  intro W hW ν hν
  have := hν.1
  filter_upwards [hF W hW ν hν, GlobalTheory.CuspSubspace.constTerm_congr ν hext] with x a b
  rw [← b, a]

theorem conjMap_isCuspFun : GlobalTheory.Published.DiscreteSeriesClassification → ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D) (S : D.what₂.Tau → SPar) (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)) (c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), S = parB (Ptw D) 0 → IsInfFam θ → GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) → GlobalTheory.Core.Mi.IdE X → Matches X h J χ t → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ (M.rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : M.Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X M c u))) ψ) → ∀ u : M.Vec, IsCuspFun (D.sp.Y 0) (GlobalTheory.ConjRowMult.conjMap X M c Φ h t u) := by
  intro hDSC D X h θ S M J χ t c hS hθ hgap hE hM hrep Φ hΦ hcont u
  obtain ⟨ψ, hψ⟩ := hcont u
  obtain ⟨hd, hl, hH, hb, -⟩ := GlobalTheory.Core.Mi.seeData_of_gap D X hgap
  have hSL : GlobalTheory.DSId.StrictLow := GlobalTheory.ClassificationConsequences.strictLow_of_dsClass
    (GlobalTheory.Published.discreteSeriesClassification_iff.1 hDSC)
  have hL2 := ((GlobalTheory.Dec.CuspAll.cusp_all hSL X.B X.dv _ hd (GlobalTheory.PinScale.one_le_g X) hb hl hH Φ hΦ).2
    (X.B.tens (GlobalTheory.ConjRowMult.vecC X M c u))).1
  have hψc := isCuspFn_of_contRep X hψ hL2
  have hY := isCuspFun_of_isCuspFn_iota D X.B.I h X.B.μf ψ hψ.1 hψ.2.1 hψc
  have e : GlobalTheory.ConjRowMult.conjMap X M c Φ h t u = fun y => star (ψ (iotaX X h (y * t⁻¹))) := by
    funext y
    rw [GlobalTheory.ConjRowMult.conjMap_apply, GlobalTheory.ConjRowMult.contRepL_spec X hψ]
  rw [e]
  intro r C hC μ 𝓕 hμ h𝓕 g
  have hz : ∫ n in 𝓕, ψ (iotaX X h ((n : GA D (D.sp.Y 0)) * (g * t⁻¹))) ∂μ = 0 := hY r C hC μ 𝓕 hμ h𝓕 (g * t⁻¹)
  show ∫ n in 𝓕, star (ψ (iotaX X h ((n : GA D (D.sp.Y 0)) * g * t⁻¹))) ∂μ = 0
  simp only [mul_assoc]
  have := congrArg (starRingEnd ℂ) hz
  rw [← integral_conj, map_zero] at this
  exact this

end GlobalTheory.ConjRowMultCusp

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateIntertwinerValuesIsCuspFunStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugateIntertwiner_values_isCuspFun : GlobalTheory.Published.DiscreteSeriesClassification → ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D) (S : D.what₂.Tau → SPar) (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)) (c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), S = parB (Ptw D) 0 → IsInfFam θ → GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) → GlobalTheory.Core.Mi.IdE X → Matches X h J χ t → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ (M.rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : M.Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X M c u))) ψ) → ∀ u : M.Vec, IsCuspFun (D.sp.Y 0) (GlobalTheory.ConjRowMult.conjMap X M c Φ h t u) := by
  first | exact @GlobalTheory.ConjRowMultCusp.conjMap_isCuspFun | exact GlobalTheory.ConjRowMultCusp.conjMap_isCuspFun | (intros; apply GlobalTheory.ConjRowMultCusp.conjMap_isCuspFun <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjTranslatedEvaluationMemAllRowsSpace
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjTranslatedEvaluationMemAllRowsSpace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Mi.SeeHH

theorem inner_antiunitary_swap {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] (U : E ≃ₗᵢ⋆[ℂ] F) (x y : E) : ⟪U x, U y⟫_ℂ = ⟪y, x⟫_ℂ := by
  have hI : ∀ z : E, U (Complex.I • z) = (-Complex.I) • U z := by
    intro z; rw [map_smulₛₗ]; simp
  have h1 : ‖U x + U y‖ = ‖y + x‖ := by rw [← map_add (f := _), U.norm_map, add_comm]
  have h2 : ‖U x - U y‖ = ‖y - x‖ := by rw [← map_sub, U.norm_map, norm_sub_rev]
  have h3 : ‖U x - Complex.I • U y‖ = ‖y - Complex.I • x‖ := by
    have e1 : U x - Complex.I • U y = U (x + Complex.I • y) := by
      rw [map_add (f := _), hI, neg_smul, sub_eq_add_neg]
    have e2 : y - Complex.I • x = (-Complex.I) • (x + Complex.I • y) := by
      rw [smul_add, smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul, neg_smul]; abel
    rw [e1, U.norm_map, e2, norm_smul]; simp
  have h4 : ‖U x + Complex.I • U y‖ = ‖y + Complex.I • x‖ := by
    have e1 : U x + Complex.I • U y = U (x - Complex.I • y) := by
      rw [map_sub, hI, neg_smul, sub_neg_eq_add]
    have e2 : y + Complex.I • x = Complex.I • (x - Complex.I • y) := by
      rw [smul_sub, smul_smul, Complex.I_mul_I, neg_smul, one_smul, sub_neg_eq_add]; abel
    rw [e1, U.norm_map, e2, norm_smul]; simp
  rw [inner_eq_sum_norm_sq_div_four (U x) (U y), inner_eq_sum_norm_sq_div_four y x]
  simp only [RCLike.I_to_complex]
  rw [h1, h2, h3, h4]

end GlobalTheory.Core.Mi.SeeHH

namespace GlobalTheory.Core.Mi.SeeHH

theorem star_toLp_eq {D : D7} (X : HidaSetting D) {f : X.B.I.GA → ℂ} (hm : MemLp f 2 (muX X))
    (hs : MemLp (fun x => star (f x)) 2 (muX X)) :
    star (hm.toLp f) = hs.toLp (fun x => star (f x)) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (hm.toLp f), hm.coeFn_toLp, hs.coeFn_toLp] with x a1 a2 a3
  rw [a1, a3, Pi.star_apply, a2]

theorem re_fix_of_row {D : D7} (X : HidaSetting D) {f : X.B.I.GA → ℂ} (hf : RowFun X f) (hm : MemLp f 2 (muX X)) :
    X.B.Re (star (hm.toLp f)) = star (hm.toLp f) := by
  have hs : MemLp (fun x => star (f x)) 2 (muX X) := hm.star
  rw [star_toLp_eq X hm hs]
  have hK := Formalism.L2.SG.Closed.level_subgroup_is_group X
  have hKL := Formalism.L2.SG.Closed.level_subgroup_properties X
  have hKM : MeasurableSet X.K2 := (Formalism.L2.SG.PoincareInHH.Cut.level_subgroup_isClopen X hK hKL).isOpen.measurableSet
  have hvol : (X.B.μf X.K2).toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hKL.2.2.1.ne', hKL.2.2.2.ne⟩
  refine Formalism.L2.SG.Pf.idempotent_fixes_invariant_L2 X (fun x => star (f x)) ?_ ?_ hs ?_
  · exact (continuous_star.comp hf.cont).measurable
  · intro γ hγ y
    rw [hf.left γ hγ y]
  · refine Filter.Eventually.of_forall fun y => ?_
    have hfun : (fun g => X.B.e g * star (f (y * (1, g)))) =
        X.K2.indicator (fun _ => star (f y) / ((X.B.μf X.K2).toReal : ℂ)) := by
      funext g
      rw [X.e_eq g]
      by_cases hg : g ∈ X.K2
      · have hg' : g ∈ K2set X.B.I X.B.g X.e0 X.z0 X.bw := hg
        rw [if_pos hg', Set.indicator_of_mem hg, hf.right g hg y]
        have hn : ‖X.chi2 g‖ = 1 := hK.2.2.2.2 g hg
        have hc : star (X.chi2 g) * X.chi2 g = 1 := by
          rw [← starRingEnd_apply, Complex.conj_mul', hn]; simp
        have e2 : chi2f X.B.I X.psiEf X.B.g X.e0 X.f0 X.z0 X.bw X.bwd g = X.chi2 g := rfl
        have ev : X.B.μf (K2set X.B.I X.B.g X.e0 X.z0 X.bw) = X.B.μf X.K2 := rfl
        rw [e2, ev, star_mul', star_star, div_eq_mul_inv, div_eq_mul_inv]
        linear_combination (star (f y) * (((X.B.μf X.K2).toReal : ℂ))⁻¹) * hc
      · have hg' : g ∉ K2set X.B.I X.B.g X.e0 X.z0 X.bw := hg
        rw [if_neg hg', Set.indicator_of_notMem hg, zero_mul]
    rw [hfun, integral_indicator hKM, setIntegral_const]
    simp only [Measure.real]
    rw [Complex.real_smul]
    have hvc : ((X.B.μf X.K2).toReal : ℂ) ≠ 0 := by exact_mod_cast hvol
    rw [mul_comm, div_mul_cancel₀ _ hvc]

end GlobalTheory.Core.Mi.SeeHH

namespace GlobalTheory.Core.Mi.SeeHH

theorem real_shift {D : D7} (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D)
    {S : D.what₂.Tau → SPar} (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ)
    (t : GA D (D.sp.Y 0)) (ht : t ∈ GfC (D.sp.Y 0)) (hR : RealSplit X h θ) (v₀ : M.Vec) (g : X.B.I.Ginf) :
    ∃ a : D.what₂.Tau → Matrix (Fin (D.sp.Y 0).rank) (Fin (D.sp.Y 0).rank) ℂ,
      (∀ τ, a τ ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ)) ∧
      (∀ τ, (iotaX X h (atTau θ (D.sp.Y 0) τ (a τ))).1 (X.pl.symm τ) = g (X.pl.symm τ)) ∧
      ∃ w : M.Vec, (∀ τ, (w τ : M.H τ) = M.rep τ (a τ) (v₀ τ : M.H τ)) ∧
        ∀ U ∈ Mult θ M J χ, ∀ x, U v₀ ((iotaX X h).symm (x * (g, 1)) * t) = U w ((iotaX X h).symm x * t) := by
  classical
  choose a ha hb using fun τ => hR.2.2.2 τ (g (X.pl.symm τ))
  have hsm : ∀ τ, M.rep τ (a τ) (v₀ τ : M.H τ) ∈ M.sm τ := fun τ =>
    GlobalTheory.SmoothStable.rep_mem_sm D (D.sp.Y 0) S M τ (a τ) (ha τ) _ (v₀ τ).2
  let gs : Finset D.what₂.Tau → X.B.I.GA := fun s => ((fun v => if X.pl v ∈ s then g v else 1), 1)
  let ws : Finset D.what₂.Tau → M.Vec := fun s τ => if τ ∈ s then ⟨_, hsm τ⟩ else v₀ τ
  have key : ∀ s : Finset D.what₂.Tau, ∀ U ∈ Mult θ M J χ, ∀ x,
      U v₀ ((iotaX X h).symm (x * gs s) * t) = U (ws s) ((iotaX X h).symm x * t) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro U _ x
      have e1 : gs ∅ = 1 := Prod.ext (funext fun v => by simp [gs]) rfl
      have e2 : ws ∅ = v₀ := funext fun τ => by simp [ws]
      rw [e1, e2, mul_one]
    | insert τ s hτ ih =>
      intro U hU x
      obtain ⟨he2, hoth, -⟩ := hR.2.2.1 τ (a τ) (ha τ)
      have hws : ws s τ = v₀ τ := by simp [ws, hτ]
      have hupd : ws (insert τ s) = Function.update (ws s) τ ⟨_, hsm τ⟩ := by
        funext σ
        by_cases hσ : σ = τ
        · subst hσ; simp [ws]
        · simp [ws, hσ, Function.update_of_ne hσ]
      have hE := Formalism.IndefR.Eqv.KerDiag.mult_equiv θ M J χ hU τ (ha τ) (ws s) ⟨_, hsm τ⟩
        (by simp only [hws])
      have hmul : iotaX X h (atTau θ (D.sp.Y 0) τ (a τ)) * gs s = gs (insert τ s) := by
        refine Prod.ext (funext fun v => ?_) ?_
        · simp only [gs, Prod.fst_mul, Pi.mul_apply]
          by_cases hv : v = X.pl.symm τ
          · subst hv
            have hm : X.pl (X.pl.symm τ) ∈ insert τ s := by simp
            have hn : X.pl (X.pl.symm τ) ∉ s := by simpa using hτ
            rw [if_pos hm, if_neg hn, hb τ, mul_one]
          · have hpv : X.pl v ≠ τ := fun e => hv (by rw [← e, Equiv.symm_apply_apply])
            rw [hoth v hv, one_mul]
            simp [Finset.mem_insert, hpv]
        · simp only [gs, Prod.snd_mul, he2, mul_one]
      rw [hupd, hE]
      show U v₀ ((iotaX X h).symm (x * gs (insert τ s)) * t) =
        U (ws s) ((iotaX X h).symm x * t * atTau θ (D.sp.Y 0) τ (a τ))
      rw [mul_assoc, ← GlobalTheory.HeckeParts.comm_atTau ht τ (a τ), ← mul_assoc]
      have hι : (iotaX X h).symm x * atTau θ (D.sp.Y 0) τ (a τ) =
          (iotaX X h).symm (x * iotaX X h (atTau θ (D.sp.Y 0) τ (a τ))) := by
        rw [map_mul, ContinuousMulEquiv.symm_apply_apply]
      rw [hι, ← ih U hU, mul_assoc, hmul]
  have eu : gs Finset.univ = (g, 1) := Prod.ext (funext fun v => by simp [gs]) rfl
  refine ⟨a, ha, hb, ws Finset.univ, fun τ => by simp [ws], fun U hU x => ?_⟩
  rw [← key Finset.univ U hU x, eu]

theorem coef_eq {D : D7} (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D)
    {S : D.what₂.Tau → SPar} (M : DSModel (D.sp.Y 0) S) (v₀ : M.Vec) (hCV : ConjVec X h θ M v₀) (g : X.B.I.Ginf)
    (a : D.what₂.Tau → Matrix (Fin (D.sp.Y 0).rank) (Fin (D.sp.Y 0).rank) ℂ)
    (ha : ∀ τ, a τ ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ))
    (hb : ∀ τ, (iotaX X h (atTau θ (D.sp.Y 0) τ (a τ))).1 (X.pl.symm τ) = g (X.pl.symm τ))
    (w : M.Vec) (hw : ∀ τ, (w τ : M.H τ) = M.rep τ (a τ) (v₀ τ : M.H τ)) :
    ∏ τ, ⟪(w τ : M.H τ), (v₀ τ : M.H τ)⟫_ℂ = Formalism.L2.SG.ProjRows.mInf X.B.I X.B.σ X.B.w g := by
  obtain ⟨c, hc1, hc2⟩ := hCV
  have e : ∀ τ, ⟪(w τ : M.H τ), (v₀ τ : M.H τ)⟫_ℂ =
      ⟪X.B.w (X.pl.symm τ), X.B.σ (X.pl.symm τ) (uMat (g (X.pl.symm τ))) (X.B.w (X.pl.symm τ))⟫_ℂ := by
    intro τ
    rw [← inner_antiunitary_swap (c τ) (v₀ τ : M.H τ) (w τ : M.H τ), hw τ,
      hc1 τ (a τ) (ha τ), hb τ, hc2 τ]
  simp_rw [e]
  exact Fintype.prod_equiv X.pl.symm _ _ (fun _ => rfl)

end GlobalTheory.Core.Mi.SeeHH


open GlobalTheory.Core.Mi.SeeHH in
theorem GlobalTheory.Core.Mi.SeeHH.conj_evS_mem_HHX : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D) (S : D.what₂.Tau → SPar) (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)) (v₀ : M.Vec), S = parB (Ptw D) 0 → IsInfFam θ → GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) → GlobalTheory.Core.Mi.IdE X → Matches X h J χ t → ConjVec X h θ M v₀ → ∀ T ∈ MultT θ M J χ, ∀ φ : L2X X, (φ : X.B.I.GA → ℂ) =ᵐ[muX X] evS X h t (T (PiTensorProduct.tprod ℂ v₀)) → star φ ∈ HHX X := by
  intro hP D X h θ S M J χ t v₀ hS hθ hGap hIdE hMat hCV T hT φ hφ
  obtain ⟨-, -, -, -, -, hL⟩ := GlobalTheory.T.discreteSeriesTestData_of_noncompactGaps D X hGap
  have hR := GlobalTheory.T.modelIdentification_respects_real_and_finite D X h θ hθ hIdE
  have hTm : PiTensorProduct.lift.symm T ∈ Mult θ M J χ := (mem_multT θ M J χ T).1 hT
  obtain ⟨hRow, hMem⟩ := GlobalTheory.T.translateToSecondModel_cuspFormMap_value_automorphic hP D X h θ S M J χ t hθ hMat T hT (PiTensorProduct.tprod ℂ v₀)
  have hfx : ∀ x, evS X h t (T (PiTensorProduct.tprod ℂ v₀)) x =
      (PiTensorProduct.lift.symm T) v₀ ((iotaX X h).symm x * t) := fun x => rfl
  generalize PiTensorProduct.lift.symm T = U at hTm hfx
  generalize evS X h t (T (PiTensorProduct.tprod ℂ v₀)) = f at hRow hMem hφ hfx
  have hφ' : φ = hMem.toLp f := Lp.ext (hφ.trans hMem.coeFn_toLp.symm)
  have hRe := re_fix_of_row X hRow hMem
  have hι : ∀ g, g ∈ GQ (D.sp.Y 0) ↔ iotaX X h g ∈ X.B.I.GFset := by
    intro g
    rw [Formalism.IndefR.RationalEmbedding.iota_rat]
    exact GlobalTheory.Mem.SJ.SchurMove.castGA_mem_GFset _ _
  obtain ⟨κ, hκ⟩ := GlobalTheory.Mem.SJ.HaarMove.schur_of_bridge M θ J χ (fun μ 𝓕 => GlobalTheory.MultFinite.schurMult hP μ 𝓕) hθ
    X.B.I X.B.μf X.B.fund X.B.fund_spec (iotaX X h) hι t U hTm U hTm
  have hv₀ : ∏ τ, ⟪(v₀ τ : M.H τ), (v₀ τ : M.H τ)⟫_ℂ = 1 := by
    obtain ⟨c, -, hc2⟩ := hCV
    refine Finset.prod_eq_one fun τ _ => ?_
    have hn : ‖(v₀ τ : M.H τ)‖ = 1 := by
      rw [← (c τ).norm_map, hc2 τ]
      exact (X.low _).1
    rw [inner_self_eq_norm_sq_to_K, hn]
    simp
  have hs : MemLp (fun x => star (f x)) 2 (muX X) := hMem.star
  have hinv : ∀ γ ∈ X.B.I.GFset, ∀ y, star (f (γ * y)) = star (f y) := fun γ hγ y => by
    rw [hRow.left γ hγ y]
  have hnorm : (((‖hs.toLp (fun x => star (f x))‖ ^ 2 : ℝ)) : ℂ) = κ := by
    rw [Formalism.IndefR.AutomorphicEvaluation.norm_sq_toLp hs, ← integral_complex_ofReal]
    have e := hκ v₀ v₀
    rw [hv₀, mul_one] at e
    rw [← e]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    beta_reduce
    rw [norm_star, hfx x, ← starRingEnd_apply, Complex.conj_mul']
    push_cast
    ring
  have hRph : X.Rph (star (hMem.toLp f)) = star (hMem.toLp f) := by
    rw [star_toLp_eq X hMem hs]
    refine Formalism.L2.SG.EvalTRph.rph_fix_of_coef X hL _ (fun g => ?_)
    obtain ⟨a, ha, hb, w, hw, hsh⟩ := real_shift X h θ M J χ t hMat.1 hR v₀ g
    have hco := coef_eq X h θ M v₀ hCV g a ha hb w hw
    have hRg := Formalism.L2.SG.EvalTReg.reg_toLp_X X (fun x => star (f x)) hinv hs (g, 1)
    have hpair : ⟪hs.toLp (fun x => star (f x)), X.B.R (g, 1) (hs.toLp (fun x => star (f x)))⟫_ℂ =
        ∫ x, star (U w ((iotaX X h).symm x * t)) * U v₀ ((iotaX X h).symm x * t) ∂(muX X) := by
      rw [MeasureTheory.L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [hs.coeFn_toLp, hRg] with x a1 a2
      rw [a1, a2]
      simp only [RCLike.inner_apply, hfx]
      rw [hsh U hTm x, starRingEnd_apply, star_star, mul_comm]
    rw [hpair, hκ w v₀, hco, hnorm]
  rw [hφ']
  refine ⟨star (hMem.toLp f), ?_⟩
  show X.B.Re (X.Rph _) = _
  rw [hRph, hRe]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjTranslatedEvaluationMemAllRowsSpaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_translated_evaluation_mem_all_rows_space : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D) (S : D.what₂.Tau → SPar) (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)) (v₀ : M.Vec), S = parB (Ptw D) 0 → IsInfFam θ → GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) → GlobalTheory.Core.Mi.IdE X → Matches X h J χ t → ConjVec X h θ M v₀ → ∀ T ∈ MultT θ M J χ, ∀ φ : L2X X, (φ : X.B.I.GA → ℂ) =ᵐ[muX X] evS X h t (T (PiTensorProduct.tprod ℂ v₀)) → star φ ∈ HHX X := by
  first | exact @GlobalTheory.Core.Mi.SeeHH.conj_evS_mem_HHX | exact GlobalTheory.Core.Mi.SeeHH.conj_evS_mem_HHX | (intros; apply GlobalTheory.Core.Mi.SeeHH.conj_evS_mem_HHX <;> assumption)
end
end
