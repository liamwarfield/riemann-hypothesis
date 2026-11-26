module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSolvableCmExtensionAbelianCompletion
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalArtinCompNormCompat
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChainChartFramesBadPrimeCongruentOneOfAdelicAgre
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PolarizedPairBaseChangePolarizedSameWeight
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartFunctionalEqOfAgreeBadPlacesAllSteps
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.Chl
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOpenSubgroupWeilElementCharacterKernel
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenStringOfAgreement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIsWeight

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedCompNormOfKilledInertiaFixing
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedCompNormOfKilledInertiaFixing
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RoadU

theorem unram_comp_normU_of_fix : ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [Algebra E Ω] [IsAlgClosure E Ω] (M : Type) [Field M] [NumberField M] [Algebra M Ω] [IsAlgClosure M Ω] [Algebra E M] [IsScalarTower E M Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (u : HeightOneSpectrum (𝓞 M)) (h : IsPlaceOver A w) (h' : IsPlaceOver A u) [u.asIdeal.LiesOver w.asIdeal] (n : ℕ) (ξ : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ)) (a : Weil h →* (w.adicCompletion E)ˣ), IsLocalArtin h a → (∀ t : Weil h, deg t = 0 → (∀ x : M, (t : G E Ω) (algebraMap M Ω x) = algebraMap M Ω x) → ∀ j, ξ j (a t) = 1) → ∀ j (x : (u.adicCompletion M)ˣ), Valued.v (x : u.adicCompletion M) = 1 → ξ j (GlobalTheory.BCChar.normU w u x) = 1 := by
  intro Ω _ E _ _ _ _ M _ _ _ _ _ _ A w u h h' _ n ξ a ha H j x hx
  obtain ⟨a', ha'⟩ := GlobalTheory.localArtinExists_holds M Ω A u h'
  have h1 : ValuativeRel.valuation (u.adicCompletion M) (x : u.adicCompletion M) = 1 := by
    have : (Valued.v : Valuation (u.adicCompletion M) (WithZero (Multiplicative ℤ))).Compatible :=
      Valuation.Compatible.ofValuation _
    exact (ValuativeRel.isEquiv (ValuativeRel.valuation (u.adicCompletion M))
      (Valued.v : Valuation (u.adicCompletion M) (WithZero (Multiplicative ℤ)))).eq_one_iff_eq_one.2 hx
  obtain ⟨τ, rfl⟩ := ha'.surj x
  have hdeg : deg τ = 0 := by
    have := ha'.ord_eq τ
    rw [GlobalTheory.SmGL.ord_eq_zero_iff.2 h1] at this
    omega
  obtain ⟨t, ht, hd⟩ := GlobalTheory.AboveL.exists_weil_restrict E M Ω A w u h h' τ
  rw [← GlobalTheory.ArtinNormU.localArtin_normU E M Ω A w u h h' a a' ha ha' t τ ht]
  exact H t (hd.2 hdeg) (fun y => by rw [ht]; exact AlgEquiv.commutes _ y) j

end GlobalTheory.RoadU
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedCompNormOfKilledInertiaFixingStatement
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_comp_norm_of_killed_inertia_fixing : ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [Algebra E Ω] [IsAlgClosure E Ω] (M : Type) [Field M] [NumberField M] [Algebra M Ω] [IsAlgClosure M Ω] [Algebra E M] [IsScalarTower E M Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (u : HeightOneSpectrum (𝓞 M)) (h : IsPlaceOver A w) (h' : IsPlaceOver A u) [u.asIdeal.LiesOver w.asIdeal] (n : ℕ) (ξ : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ)) (a : Weil h →* (w.adicCompletion E)ˣ), IsLocalArtin h a → (∀ t : Weil h, deg t = 0 → (∀ x : M, (t : G E Ω) (algebraMap M Ω x) = algebraMap M Ω x) → ∀ j, ξ j (a t) = 1) → ∀ j (x : (u.adicCompletion M)ˣ), Valued.v (x : u.adicCompletion M) = 1 → ξ j (GlobalTheory.BCChar.normU w u x) = 1 := by
  first | (exact @GlobalTheory.RoadU.unram_comp_normU_of_fix) | (exact GlobalTheory.RoadU.unram_comp_normU_of_fix) | (intros; apply GlobalTheory.RoadU.unram_comp_normU_of_fix  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnlinkedCharsCompNormU
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RoadU

theorem unlinked_chars_comp_normU : ∀ (E M : Type) [Field E] [NumberField E] [Field M] [NumberField M] [Algebra E M] (w : HeightOneSpectrum (𝓞 E)) (u : HeightOneSpectrum (𝓞 M)) [u.asIdeal.LiesOver w.asIdeal] (n : ℕ) (c : ℝ), ∀ (ξ : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)), (∀ j, ∃ e : ℝ, |e| < 1 / 2 ∧ ∀ x, ‖((ξ j x : ℂˣ) : ℂ)‖ = ‖((absPow (w.adicCompletion E) ((e - c : ℝ) : ℂ) x : ℂˣ) : ℂ)‖) → Unlinked (chars (fun j => (ξ j).comp (GlobalTheory.BCChar.normU w u)) fun j => GlobalTheory.BCChar.isSmoothChar_comp_normU w u (hξ j)) := by
  intro E M _ _ _ _ _ w u _ n c ξ hξ he
  letI : Algebra (w.adicCompletion E) (u.adicCompletion M) := (GroundTheory.Global.adicCompletionMap w u).toAlgebra
  have hf := GroundTheory.Global.continuous_adicCompletionMap w u
  haveI : ContinuousSMul (w.adicCompletion E) (u.adicCompletion M) := _root_.continuousSMul_of_algebraMap _ _ hf
  haveI : IsScalarTower E (w.adicCompletion E) (u.adicCompletion M) :=
    .of_algebraMap_eq fun x => by
      show _ = GroundTheory.Global.adicCompletionMap w u _
      rw [GroundTheory.Global.adicCompletionMap_algebraMap, IsScalarTower.algebraMap_apply E M (u.adicCompletion M)]
  haveI : FiniteDimensional (w.adicCompletion E) (u.adicCompletion M) := GroundTheory.Global.finite_adicCompletion w u
  haveI : IsModuleTopology (w.adicCompletion E) (u.adicCompletion M) := by
    letI : NontriviallyNormedField (w.adicCompletion E) := Valued.toNontriviallyNormedField _ _
    exact isModuleTopologyOfFiniteDimensional
  have hN : ∀ t : ℂ, (absPow (w.adicCompletion E) t).comp (GlobalTheory.BCChar.normU w u) = absPow (u.adicCompletion M) t :=
    fun t => GlobalTheory.LBCNu.absPow_comp_norm t
  have hval : ∀ (s : ℝ) (x : (u.adicCompletion M)ˣ), ‖((absPow (u.adicCompletion M) (s : ℂ) x : ℂˣ) : ℂ)‖ =
      nabs (u.adicCompletion M) x ^ s := fun s x => by
    rw [val_absPow_ofReal, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (nabs_pos' _ x).le _)]
  have key : ∀ j, ∃ e : ℝ, |e| < 1 / 2 ∧ ∀ x, ‖(((ξ j).comp (GlobalTheory.BCChar.normU w u) x : ℂˣ) : ℂ)‖ =
      nabs (u.adicCompletion M) x ^ (e - c) := by
    intro j
    obtain ⟨e, he1, he2⟩ := he j
    refine ⟨e, he1, fun x => ?_⟩
    rw [MonoidHom.comp_apply, he2, ← MonoidHom.comp_apply, hN, hval]
  intro y hy z hz hyz
  simp only [chars, Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and] at hy hz
  obtain ⟨i, rfl⟩ := hy
  obtain ⟨j, rfl⟩ := hz
  rw [IrrGL.nu, IrrGL.tw_ofChar, IrrGL.ofChar_inj] at hyz
  obtain ⟨a, ha, ha'⟩ := key i
  obtain ⟨b, hb, hb'⟩ := key j
  have h1 : absPow (u.adicCompletion M) ((a - b - 1 : ℝ) : ℂ) = 1 := by
    ext x
    have hx := congrArg (fun χ : (u.adicCompletion M)ˣ →* ℂˣ => ‖((χ x : ℂˣ) : ℂ)‖) hyz
    simp only [MonoidHom.mul_apply, Units.val_mul, norm_mul] at hx
    have h1' : ‖((absPow (u.adicCompletion M) 1 x : ℂˣ) : ℂ)‖ = nabs (u.adicCompletion M) x ^ (1 : ℝ) := by
      rw [← hval]; simp
    rw [ha', hb', h1'] at hx
    have ht := nabs_pos' (u.adicCompletion M) x
    rw [val_absPow_ofReal, MonoidHom.one_apply, Units.val_one]
    have : nabs (u.adicCompletion M) x ^ (a - b - 1) = 1 := by
      rw [show a - b - 1 = (a - c) - ((b - c) + 1) by ring, Real.rpow_sub ht, Real.rpow_add ht, hx,
        div_self (by positivity)]
    rw [this, Complex.ofReal_one]
  have h2 := (absPow_ofReal_eq_one (k := u.adicCompletion M)).1 h1
  rw [abs_lt] at ha hb
  linarith [ha.1, ha.2, hb.1, hb.2]

end GlobalTheory.RoadU
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOpenGaloisSubgroupTraceNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOpenGaloisSubgroupTraceNeZero
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.AboveL

theorem exists_open_trace_ne_zero (Ω : Type) [Field Ω] (K : Type) [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω]
    (l : ℕ) [Fact l.Prime] (a : ℕ) (ha : 1 ≤ a) (r : G K Ω →* GL (Fin a) (Qbar l)) (hr : Continuous r) :
    ∃ N : Subgroup (G K Ω), IsOpen (N : Set (G K Ω)) ∧ ∀ n ∈ N, (r n).val.trace ≠ 0 := by
  have hc : Continuous fun g : G K Ω => (r g).val.trace :=
    (Units.continuous_val.comp hr).matrix_trace
  set U : Set (G K Ω) := {g | (r g).val.trace ≠ 0} with hU
  have hUo : IsOpen U := isOpen_ne_fun hc continuous_const
  have h1 : (1 : G K Ω) ∈ U := by
    simp only [hU, Set.mem_setOf_eq, map_one, Units.val_one, Matrix.trace_one, Fintype.card_fin]
    exact_mod_cast (by omega : a ≠ 0)
  obtain ⟨E, hE, hEU⟩ := (krullTopology_mem_nhds_one_iff K Ω U).mp (hUo.mem_nhds h1)
  exact ⟨E.fixingSubgroup, E.fixingSubgroup_isOpen, fun n hn => hEU hn⟩

end GlobalTheory.AboveL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOpenGaloisSubgroupTraceNeZeroStatement
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_galoisSubgroup_trace_ne_zero : ∀ (Ω : Type) [Field Ω] (K : Type) [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (a : ℕ), 1 ≤ a → ∀ r : G K Ω →* GL (Fin a) (Qbar l), Continuous r → ∃ N : Subgroup (G K Ω), IsOpen (N : Set (G K Ω)) ∧ ∀ n ∈ N, (r n).val.trace ≠ 0 := by
  first | exact @GlobalTheory.AboveL.exists_open_trace_ne_zero | exact GlobalTheory.AboveL.exists_open_trace_ne_zero | (intros; apply GlobalTheory.AboveL.exists_open_trace_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOfHasSupportSingleton
noncomputable section

open ValuativeRel GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.PRep GlobalTheory.SmGL

namespace GlobalTheory.DZeroDegOne

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem eq_of_hasSupport_singleton {y z : IrrGL (k := k)} (h : HasSupport y.rep {z}) : y = z := by
  obtain ⟨r, u, hu, hi, hc, e, hsub⟩ := h
  obtain rfl : r = 1 := by simpa using congrArg Multiset.card hu
  obtain rfl : u = fun _ => z := funext fun i => by
    rw [Subsingleton.elim i 0]
    simpa using hu
  obtain ⟨d, c⟩ := y
  obtain rfl : z.1 = d := by simpa using Fintype.card_congr e
  have hd : ∑ _ : Fin 1, z.1 = z.1 := by simp
  let e' := stdBlocks (fun _ : Fin 1 => z.1) hd
  obtain ⟨φ⟩ : Nonempty ((multiProd e fun _ => z.rep).Equiv (multiProd e' fun _ => z.rep)) := by
    obtain ⟨w, hw⟩ := Placing.exists_moves (R := k) e' e
    have hw' : Placing.Moves e e' w⁻¹ := by
      intro g x y
      rw [← hw (w⁻¹ * g * w⁻¹⁻¹) x y]
      simp [mul_assoc]
    let ρ := GlobalTheory.SmGL.twist (piTensor fun _ : Fin 1 => z.rep) (deltaHalf k fun _ : Fin 1 => Fin z.1)
    have conjugate {f f' : (Σ _ : Fin 1, Fin z.1) ≃ Fin z.1} {v : GL (Fin z.1) k}
        (hv : Placing.Moves f f' v) (p : parab k f) :
        ∃ q : parab k f', (q : GL (Fin z.1) k) = v * p * v⁻¹ ∧
          (ρ.comp (leviProj k f')) q = (ρ.comp (leviProj k f)) p := by
      have hq : v * (p : GL (Fin z.1) k) * v⁻¹ ∈ parab k f' := by
        rw [mem_parab]
        intro i j hij
        exact (hij.ne (Subsingleton.elim _ _)).elim
      refine ⟨⟨_, hq⟩, rfl, ?_⟩
      simp only [MonoidHom.comp_apply]
      congr 1
      refine funext fun a => Units.ext (Matrix.ext fun i j => ?_)
      simpa only [leviProj_apply] using hv (p : GL (Fin z.1) k) ⟨a, i⟩ ⟨a, j⟩
    exact Placing.smInd_equiv w (conjugate hw) (conjugate hw')
  obtain ⟨ψ⟩ := nonempty_equiv_prodIrr_one z hd
  let χ := φ.trans ψ.symm
  obtain ⟨θ⟩ := IsSubquotient.nonempty_equiv
    (hsub.trans (.of_injective χ.toIntertwiningMap χ.toLinearEquiv.injective)) hi z.2.rep.irr
  exact ((IrrGL.of_rep z).symm.trans ((IrrGL.of_eq_of.2 ⟨θ⟩).trans (IrrGL.of_rep ⟨_, c⟩))).symm

end GlobalTheory.DZeroDegOne
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.ToralDeRham.WeaklyAttachedToralOfCmLift
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.ToralDeRham.ExistsCuspidalCharLiftOfSolvableCmExtension
namespace GalTw

noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RoadU

theorem isWeaklyAttached_of_cmBaseChange_of_finrank (hI : UpperTheory.Gal.ToralGalois.Inq) (Ω : Type) [Field Ω] (M : Type) [Field M] [NumberField M] [IsCMField M]
    [Algebra M Ω] [IsAlgClosure M Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (ha : 1 ≤ a) (d : ℕ) :
    ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra K Ω] [IsAlgClosure K Ω] [Algebra K M]
      [IsScalarTower K M Ω], Module.finrank K M = d → ∀ (π : CuspSub K a) (χ : HChar (maximalRealSubfield K)),
      InScope .all l π χ → ∀ r : G K Ω →* GL (Fin a) (Qbar l), Weak π ι r → ∀ N : Subgroup (G K Ω),
      (∀ x ∈ N, (r x).val.trace ≠ 0) → SolvDisj M N →
      ∃ (P : CuspSub M a) (χ' : HChar (maximalRealSubfield M)), InScope .all l P χ' ∧ CharLift π P := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro K _ _ _ _ _ _ _ hd π χ hsc r hr N hN hS
  obtain ⟨hgal, hsol, hdec⟩ := hS
  by_cases h1 : Module.finrank K M = 1
  · obtain ⟨P, hP⟩ := GlobalTheory.T.exists_characterSupportBaseChangeLift_degreeOne K M h1 a ha π
    obtain ⟨⟨χ', hχ'⟩, -⟩ := GlobalTheory.T.polarizedPair_baseChange_polarized_same_weight GlobalTheory.automorphicFormsFiniteGL hI.js hI.gk K M l a ha π χ P hP.1 hsc
    exact ⟨P, χ', hχ', hP⟩
  haveI : Group.IsSolvable (M ≃ₐ[K] M) := hsol
  haveI : Nontrivial (M ≃ₐ[K] M) := by
    rw [← Finite.one_lt_card_iff_nontrivial, IsGalois.card_aut_eq_finrank]
    have := Module.finrank_pos (R := K) (M := M)
    omega
  obtain ⟨H, hH, hp⟩ := GlobalTheory.SolvUp.exists_normal_prime_index (M ≃ₐ[K] M)
  let K₁ := IntermediateField.fixedField H
  haveI : IsGalois K K₁ := IsGalois.of_fixedField_normal_subgroup H
  haveI : IsCMField K₁ := GlobalTheory.SolvUp.isCMField_intermediate Ω K M K₁
  haveI : Module.IsTorsionFree K₁ Ω := DivisionSemiring.to_moduleIsTorsionFree
  haveI : IsAlgClosure K₁ Ω := ⟨IsAlgClosure.isAlgClosed K, Algebra.IsAlgebraic.tower_top (K := K) K₁⟩
  haveI : Group.IsSolvable (M ≃ₐ[K₁] M) :=
    Group.isSolvable_of_isSolvable_injective (f := AlgEquiv.restrictScalarsHom K) (AlgEquiv.restrictScalars_injective K)
  have hdeg : Module.finrank K K₁ = H.index := by
    have h2 := Module.finrank_mul_finrank K K₁ M
    rw [IntermediateField.finrank_fixedField_eq_card, ← IsGalois.card_aut_eq_finrank K M, ← H.index_mul_card] at h2
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h2
  have hp₁ : (Module.finrank K K₁).Prime := hdeg ▸ hp
  have hlt : Module.finrank K₁ M < d := by
    rw [← hd, ← Module.finrank_mul_finrank K K₁ M, hdeg]
    exact lt_mul_of_one_lt_left Module.finrank_pos hp.one_lt

  have hmove : ∃ g : G K Ω, (∃ x : K₁, g (algebraMap K₁ Ω x) ≠ algebraMap K₁ Ω x) ∧ (r g).val.trace ≠ 0 := by
    obtain ⟨x, hx⟩ : ∃ x : K₁, x ∉ Set.range (algebraMap K K₁) := by
      by_contra hc
      push_neg at hc
      have hb : Function.Bijective (algebraMap K K₁) := ⟨(algebraMap K K₁).injective, fun y => hc y⟩
      exact hp.one_lt.ne' (hdeg ▸ Algebra.finrank_eq_one_iff_bijective_algebraMap.2 hb)
    by_contra hc
    push_neg at hc
    have hfixN : ∀ n ∈ N, n (algebraMap K₁ Ω x) = algebraMap K₁ Ω x := by
      intro n hn
      by_contra hne
      exact hN n hn (hc n ⟨x, hne⟩)
    have hfix : ∀ g : G K Ω, g (algebraMap K₁ Ω x) = algebraMap K₁ Ω x := by
      intro g
      obtain ⟨z, n, hn, rfl⟩ := hdec g
      have hz : algebraMap K₁ Ω x = algebraMap M Ω (x : M) := IsScalarTower.algebraMap_apply K₁ M Ω x
      show z (n (algebraMap K₁ Ω x)) = _
      rw [hfixN n hn, hz]
      exact z.commutes _
    have hmem : algebraMap K₁ Ω x ∈ (⊥ : IntermediateField K Ω) := by
      rw [← InfiniteGalois.fixedField_fixingSubgroup (⊥ : IntermediateField K Ω), IntermediateField.fixingSubgroup_bot,
        IntermediateField.mem_fixedField_iff]
      intro g _
      exact hfix g
    obtain ⟨k, hk⟩ := IntermediateField.mem_bot.1 hmem
    apply hx
    refine ⟨k, (algebraMap K₁ Ω).injective ?_⟩
    rw [← hk, ← IsScalarTower.algebraMap_apply]

  have hnotw : ∀ η : HChar K, UpperTheory.V.Published.IsNormChar K₁ η → ¬ UpperTheory.V.Published.SelfTw (CG.mk π).HasSat η := by
    intro η hη hst
    obtain ⟨g, hgM, htr⟩ := hmove
    exact htr (GlobalTheory.T.trace_eq_zero_off_subgroup_of_selfTwist Ω K K₁ hp₁ l ι a π r hr η hη hst g hgM)
  obtain ⟨P₁, hP₁⟩ := hI.ac K K₁ hp₁ a ha π hnotw
  have hc₁ : CharLift π P₁ := hI.chl K K₁ hp₁ a ha π P₁ hP₁
  obtain ⟨⟨χ₁, hχ₁⟩, -⟩ := GlobalTheory.T.polarizedPair_baseChange_polarized_same_weight GlobalTheory.automorphicFormsFiniteGL hI.js hI.gk K K₁ l a ha π χ P₁ hP₁ hsc
  have hr₁ : Weak P₁ ι (resTo K₁ r) := GlobalTheory.T.weaklyAttachedGaloisRepresentation_baseChange_restrict K K₁ Ω l ι a π P₁ hP₁ r hr
  let N₁ : Subgroup (G K₁ Ω) := N.comap (AlgEquiv.restrictScalarsHom K)
  have hS₁ : SolvDisj M N₁ := by
    refine ⟨inferInstance, ‹Group.IsSolvable (M ≃ₐ[K₁] M)›, fun g₁ => ?_⟩
    obtain ⟨z, n, hn, he⟩ := hdec (AlgEquiv.restrictScalarsHom K g₁)
    have hn₁ : ∀ y : K₁, n (algebraMap K₁ Ω y) = algebraMap K₁ Ω y := by
      intro y
      have hy : algebraMap K₁ Ω y = algebraMap M Ω (y : M) := IsScalarTower.algebraMap_apply K₁ M Ω y
      have h3 := DFunLike.congr_fun he (algebraMap K₁ Ω y)
      change g₁ (algebraMap K₁ Ω y) = z (n (algebraMap K₁ Ω y)) at h3
      rw [g₁.commutes] at h3
      apply z.injective
      rw [← h3, hy]
      exact (z.commutes _).symm
    let n₁ : G K₁ Ω := AlgEquiv.ofRingEquiv (f := n.toRingEquiv) hn₁
    refine ⟨z, n₁, ?_, ?_⟩
    · show AlgEquiv.restrictScalarsHom K n₁ ∈ N
      convert hn using 1
      ext w
      rfl
    · ext w
      have h3 := DFunLike.congr_fun he w
      exact h3
  obtain ⟨P, χ', hsc', hc'⟩ := ih _ hlt K₁ rfl P₁ χ₁ hχ₁ (resTo K₁ r) hr₁ N₁ (fun n hn => hN _ hn) hS₁
  exact ⟨P, χ', hsc', GlobalTheory.T.cuspRep_characterSupportLift_trans_tower K K₁ M a π P₁ P hc₁ hc'⟩

theorem upWeak : UpperTheory.Gal.ToralGalois.Inq → ∀ (Ω : Type) [Field Ω] (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra K Ω] [IsAlgClosure K Ω] (M : Type) [Field M] [NumberField M] [IsCMField M] [Algebra M Ω] [IsAlgClosure M Ω] [Algebra K M] [IsScalarTower K M Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ (π : CuspSub K a) (χ : HChar (maximalRealSubfield K)), InScope .all l π χ → ∀ r : G K Ω →* GL (Fin a) (Qbar l), Weak π ι r → ∀ N : Subgroup (G K Ω), (∀ x ∈ N, (r x).val.trace ≠ 0) → SolvDisj M N → ∃ (P : CuspSub M a) (χ' : HChar (maximalRealSubfield M)), InScope .all l P χ' ∧ CharLift π P := by
  intro hI Ω _ K _ _ _ _ _ M _ _ _ _ _ _ _ l _ ι a ha π χ hsc r hr N hN hS
  exact isWeaklyAttached_of_cmBaseChange_of_finrank hI Ω M l ι a ha _ K rfl π χ hsc r hr N hN hS

end GlobalTheory.RoadU

section
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem GlobalTheory.T.exists_cuspidal_charLift_of_solvable_cmExtension : UpperTheory.Gal.ToralGalois.Inq → ∀ (Ω : Type) [Field Ω] (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra K Ω] [IsAlgClosure K Ω] (M : Type) [Field M] [NumberField M] [IsCMField M] [Algebra M Ω] [IsAlgClosure M Ω] [Algebra K M] [IsScalarTower K M Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ (π : CuspSub K a) (χ : HChar (maximalRealSubfield K)), InScope .all l π χ → ∀ r : G K Ω →* GL (Fin a) (Qbar l), Weak π ι r → ∀ N : Subgroup (G K Ω), (∀ x ∈ N, (r x).val.trace ≠ 0) → SolvDisj M N → ∃ (P : CuspSub M a) (χ' : HChar (maximalRealSubfield M)), InScope .all l P χ' ∧ CharLift π P := by
  first | (exact @GlobalTheory.RoadU.upWeak) | (exact GlobalTheory.RoadU.upWeak) | (intros; apply GlobalTheory.RoadU.upWeak  <;> assumption)

end
end
end GalTw
end

open GlobalTheory.RoadU

namespace GalTw
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RoadU.TorLiftC

theorem exists_cm_lift_fix_charKer : UpperTheory.Gal.ToralGalois.Inq → ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ (π : CuspSub E n) (χ : HChar (maximalRealSubfield E)), InScope .all l π χ → ∀ r : G E Ω →* GL (Fin n) (Qbar l), Weak π ι r → ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (ξ : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ)), (∀ j, IsSmoothChar (ξ j)) → ∀ a : Weil h →* (w.adicCompletion E)ˣ, IsLocalArtin h a → ∀ g : Weil h, deg g ≠ 0 → ∃ (M : Type) (_ : Field M) (_ : NumberField M) (_ : IsCMField M) (_ : Algebra M Ω) (_ : IsAlgClosure M Ω) (_ : Algebra E M) (_ : IsScalarTower E M Ω) (P : CuspSub M n) (χ' : HChar (maximalRealSubfield M)), InScope .all l P χ' ∧ CharLift π P ∧ (∀ x : M, (g : G E Ω) (algebraMap M Ω x) = algebraMap M Ω x) ∧ ∀ t : Weil h, deg t = 0 → (∀ x : M, (t : G E Ω) (algebraMap M Ω x) = algebraMap M Ω x) → ∀ j, ξ j (a t) = 1 := by
  intro hI Ω _ E _ _ _ _ _ l _ ι n hn π χ hπ r hr w A h ξ hξ a ha g hg
  have lies : ∀ {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
      [Algebra K L] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω]
      {v : HeightOneSpectrum (𝓞 K)} {u : HeightOneSpectrum (𝓞 L)},
      IsPlaceOver A v → IsPlaceOver A u → u.asIdeal.LiesOver v.asIdeal := by
    intro K L _ _ _ _ _ _ _ _ v u hv hu
    refine ⟨?_⟩
    ext x
    rw [← hv x, Ideal.under, Ideal.mem_comap, ← hu, IsScalarTower.algebraMap_apply K L Ω]
    rfl
  obtain ⟨N₀, hN₀o, hN₀⟩ := GlobalTheory.T.exists_open_galoisSubgroup_trace_ne_zero Ω E l n hn r hr.1
  obtain ⟨M₀, _, _, _, _, _, _, _, hsd₀, hfix₀, hfixR₀⟩ := GlobalTheory.T.exists_solvable_cm_extension_split_place Ω E A w h N₀ hN₀o
  obtain ⟨π₀, χ₀, hπ₀, hl₀⟩ := GlobalTheory.T.exists_cuspidal_charLift_of_solvable_cmExtension hI Ω E M₀ l ι n hn π χ hπ r hr N₀ hN₀ hsd₀
  obtain ⟨v₀, h₀, -⟩ := GlobalTheory.T.exists_isPlaceOver_finiteExtension_of_isPlaceOver E M₀ Ω A w h
  haveI : v₀.asIdeal.LiesOver w.asIdeal := lies h h₀
  obtain ⟨a₀, ha₀⟩ := GlobalTheory.localArtinExists_holds M₀ Ω A v₀ h₀
  have hgfix : ∀ z : M₀, (g : G E Ω) (algebraMap M₀ Ω z) = algebraMap M₀ Ω z := hfix₀ g (Weil_le_Dec h g.2)
  have hg₀ : (AlgEquiv.ofRingEquiv (f := (g : G E Ω).toRingEquiv) hgfix : G M₀ Ω) ∈ Weil h₀ :=
    GlobalTheory.T.mem_weilGroupAtPlace_of_fixes_extension E M₀ Ω A w v₀ h h₀ g _ (fun z => rfl)
  let g₀ : Weil h₀ := ⟨_, hg₀⟩
  have hdeg₀ : deg g₀ ≠ 0 := by
    obtain ⟨t, ht, hd⟩ := GlobalTheory.T.exists_weilGroup_restrict_extension E M₀ Ω A w v₀ h h₀ g₀
    have : t = g := Subtype.ext (AlgEquiv.ext fun z => ht z)
    subst this
    exact fun h0 => hg (hd.2 h0)
  obtain ⟨V, hVo, hVc, hgV, hVine⟩ := GlobalTheory.T.exists_open_subgroup_weilElement_characterKernel Ω M₀ v₀ A h₀ n (fun j => (ξ j).comp (GlobalTheory.BCChar.normU w v₀))
    (fun j => GlobalTheory.BCChar.isSmoothChar_comp_normU w v₀ (hξ j)) a₀ ha₀ g₀ hdeg₀
  have hr₀ : Weak π₀ ι (r.comp (UpperTheory.V.Af.Bc.res E Ω M₀)) := GlobalTheory.T.weaklyAttachedGaloisRepresentation_baseChange_restrict E M₀ Ω l ι n π π₀ hl₀.1 r hr
  obtain ⟨N₁, hN₁o, hN₁⟩ := GlobalTheory.T.exists_open_galoisSubgroup_trace_ne_zero Ω M₀ l n hn _ hr₀.1
  obtain ⟨M₁, _, _, _, _, _, _, _, hsd₁, hV₁⟩ := GlobalTheory.T.exists_solvable_cm_extension_abelianCompletion Ω M₀ A v₀ h₀ hfixR₀ V hVo hVc N₁ hN₁o
  obtain ⟨P, χ₁, hP, hl₁⟩ := GlobalTheory.T.exists_cuspidal_charLift_of_solvable_cmExtension hI Ω M₀ M₁ l ι n hn π₀ χ₀ hπ₀ _ hr₀ N₁ hN₁ hsd₁
  letI : Algebra E M₁ := ((algebraMap M₀ M₁).comp (algebraMap E M₀)).toAlgebra
  haveI : IsScalarTower E M₀ M₁ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower E M₁ Ω := IsScalarTower.of_algebraMap_eq fun z => by
    rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply M₀ M₁ Ω,
      ← IsScalarTower.algebraMap_apply E M₀ Ω]
  have hl : CharLift π P := GlobalTheory.T.cuspRep_characterSupportLift_trans_tower E M₀ M₁ n π π₀ P hl₀ hl₁
  have hg₁fix : ∀ z : M₁, (g : G E Ω) (algebraMap M₁ Ω z) = algebraMap M₁ Ω z :=
    (hV₁ ⟨(g₀ : G M₀ Ω), Weil_le_Dec h₀ g₀.2⟩).2 hgV
  refine ⟨M₁, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    P, χ₁, hP, hl, hg₁fix, ?_⟩
  intro t ht0 htfix j
  have htfix₀ : ∀ z : M₀, (t : G E Ω) (algebraMap M₀ Ω z) = algebraMap M₀ Ω z := fun z => by
    rw [IsScalarTower.algebraMap_apply M₀ M₁ Ω]
    exact htfix _
  have ht₀ : (AlgEquiv.ofRingEquiv (f := (t : G E Ω).toRingEquiv) htfix₀ : G M₀ Ω) ∈ Weil h₀ :=
    GlobalTheory.T.mem_weilGroupAtPlace_of_fixes_extension E M₀ Ω A w v₀ h h₀ t _ (fun z => rfl)
  let t₀ : Weil h₀ := ⟨_, ht₀⟩
  have hdt₀ : deg t₀ = 0 := by
    obtain ⟨s, hs, hd⟩ := GlobalTheory.T.exists_weilGroup_restrict_extension E M₀ Ω A w v₀ h h₀ t₀
    have : s = t := Subtype.ext (AlgEquiv.ext fun z => hs z)
    subst this
    exact hd.1 ht0
  have ht₀i : (t₀ : G M₀ Ω) ∈ Ine (F := M₀) A := deg_eq_zero_iff.1 hdt₀
  have hinV : (⟨(t₀ : G M₀ Ω), Weil_le_Dec h₀ t₀.2⟩ : Dec (F := M₀) A) ∈ V :=
    (hV₁ _).1 fun z => htfix z
  have h1 := hVine ⟨_, ht₀i⟩ _ hinV rfl j
  have h2 : ineIncl h₀ ⟨_, ht₀i⟩ = t₀ := Subtype.ext rfl
  rw [h2] at h1
  have h3 := GlobalTheory.T.localArtin_comp_norm_compat E M₀ Ω A w v₀ h h₀ a a₀ ha ha₀ t t₀ (fun z => rfl)
  rw [h3]
  simpa using h1

end GlobalTheory.RoadU.TorLiftC

section
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem GlobalTheory.T.weaklyAttached_toral_of_cm_lift : UpperTheory.Gal.ToralGalois.Inq → ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ (π : CuspSub E n) (χ : HChar (maximalRealSubfield E)), InScope .all l π χ → ∀ r : G E Ω →* GL (Fin n) (Qbar l), Weak π ι r → ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (ξ : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ)), (∀ j, IsSmoothChar (ξ j)) → ∀ a : Weil h →* (w.adicCompletion E)ˣ, IsLocalArtin h a → ∀ g : Weil h, deg g ≠ 0 → ∃ (M : Type) (_ : Field M) (_ : NumberField M) (_ : IsCMField M) (_ : Algebra M Ω) (_ : IsAlgClosure M Ω) (_ : Algebra E M) (_ : IsScalarTower E M Ω) (P : CuspSub M n) (χ' : HChar (maximalRealSubfield M)), InScope .all l P χ' ∧ CharLift π P ∧ (∀ x : M, (g : G E Ω) (algebraMap M Ω x) = algebraMap M Ω x) ∧ ∀ t : Weil h, deg t = 0 → (∀ x : M, (t : G E Ω) (algebraMap M Ω x) = algebraMap M Ω x) → ∀ j, ξ j (a t) = 1 := by
  first | (exact @GlobalTheory.RoadU.TorLiftC.exists_cm_lift_fix_charKer) | (exact GlobalTheory.RoadU.TorLiftC.exists_cm_lift_fix_charKer) | (intros; apply GlobalTheory.RoadU.TorLiftC.exists_cm_lift_fix_charKer  <;> assumption)

end
end
end GalTw
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.ToralDeRham.FrobeniusCharpolyEqSatakeOfPlaceAbove
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.ToralDeRham.NormEqOneOfIsUnitarisable
open GlobalTheory.RoadU

namespace GalTw
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RoadU.Window

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem norm_absPow_ofReal (r : ℝ) (z : kˣ) : ‖((absPow k (r : ℂ) z : ℂˣ) : ℂ)‖ = nabs k z ^ r := by
  rw [val_absPow_ofReal, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (GlobalTheory.SmGL.nabs_pos' k z).le _)]

theorem len_eq_one {Δ : Segment k} {s : ℂ} {S : Multiset (IrrGL (k := k))} (hS : Unlinked S)
    (hm : ∀ a, (Δ.term a).nu s ∈ S) : Δ.len = 1 := by
  by_contra hne
  have h2 : 2 ≤ Δ.len := by have := Δ.len_pos; omega
  refine hS _ (hm ⟨1, by omega⟩) _ (hm ⟨0, by omega⟩) ?_
  simp only [Segment.term, IrrGL.nu_nu]
  congr 1
  push_cast
  ring

theorem norm_eq_one_of_isUnitarisable {μ : kˣ →* ℂˣ} (hμ : IsSmoothChar μ)
    (hu : IsUnitarisable (IrrGL.ofChar μ hμ).rep) (z : kˣ) : ‖((μ z : ℂˣ) : ℂ)‖ = 1 := by
  have h1 : IsUnitarisable (detRep (Fin 1) μ) :=
    GlobalTheory.GenericUnitary.isUnitarisable_of_equiv (equivRep (IrrRep.det (Fin 1) μ hμ)).symm hu
  have h := (isUnitarisable_ofChar_iff _).1 h1 (Matrix.GeneralLinearGroup.scalar (Fin 1) z)
  have h2 : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 1) z) = z := by
    ext; simp [Matrix.GeneralLinearGroup.scalar]
  rwa [detChar_apply, h2] at h

theorem exponents_of_genericUnitary (hGU : GlobalTheory.Published.GenericUnitaryDualGL) (hZ : GlobalTheory.Published.ZelevinskyPolynomialRing)
    [CharZero k] (x : IrrGL (k := k)) (hg : IsGeneric x.rep) (hu : IsUnitarisable x.rep) {n : ℕ}
    (ξ : Fin n → (kˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)) (hx : HasSupport x.rep (chars ξ hξ))
    (hU : Unlinked (chars ξ hξ)) (j : Fin n) :
    ∃ e : ℝ, |e| < 1 / 2 ∧ ∀ z, ‖((ξ j z : ℂˣ) : ℂ)‖ = ‖((absPow k (e : ℂ) z : ℂˣ) : ℂ)‖ := by
  obtain ⟨h, δ, Δ, s, hΔ, hδu, hs, hd, ⟨φ⟩⟩ := hGU.exists_prod x.2.rep.smooth x.2.rep.irr hu hg
  obtain ⟨Z, Ψ, -, hΨ, -⟩ := hZ k
  have hsupp : HasSupport x.rep (∑ i, (Δ i).ms.map fun y => y.nu (s i)) :=
    GlobalTheory.LocGL.SupportRing.hasSupport_of_isSubquotient_prodIrr hΨ
      (fun i => GlobalTheory.LocGL.SupportRing.hasSupport_nu (hΔ i).hasSupport (s i)) x.2.rep.irr
      (.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective)
  have heq : chars ξ hξ = ∑ i, (Δ i).ms.map fun y => y.nu (s i) :=
    GlobalTheory.LocGL.SupportUnique.eq_of_hasSupport GlobalTheory.RecT.geometricLemma_holds hZ _ x rfl _ _ hx hsupp
  have hj : IrrGL.ofChar (ξ j) (hξ j) ∈ ∑ i, (Δ i).ms.map fun y => y.nu (s i) :=
    heq ▸ Multiset.mem_map_of_mem _ (Finset.mem_univ_val j)
  obtain ⟨i, -, hi⟩ := Multiset.mem_sum.1 hj
  have hm : ∀ a, ((Δ i).term a).nu (s i) ∈ chars ξ hξ := fun a => heq ▸ Multiset.mem_sum.2
    ⟨i, Finset.mem_univ _, Multiset.mem_map_of_mem _ (Multiset.mem_map_of_mem _ (Finset.mem_univ_val a))⟩
  have hlen := len_eq_one hU hm
  have hfirst : (Δ i).first ∈ (Δ i).ms := by
    have h0 : (Δ i).term ⟨0, (Δ i).len_pos⟩ ∈ (Δ i).ms := Multiset.mem_map_of_mem _ (Finset.mem_univ_val _)
    have e0 : (Δ i).term ⟨0, (Δ i).len_pos⟩ = (Δ i).first := by simp [Segment.term]
    rwa [e0] at h0
  have hms : (Δ i).ms = {(Δ i).first} := by
    obtain ⟨z, hz⟩ := Multiset.card_eq_one.1 (by simp [Segment.ms, hlen] : Multiset.card (Δ i).ms = 1)
    rw [hz] at hfirst ⊢
    rw [Multiset.mem_singleton.1 hfirst]
  have hδ : δ i = (Δ i).first := GlobalTheory.DZeroDegOne.eq_of_hasSupport_singleton (hms ▸ (hΔ i).hasSupport)
  obtain ⟨y, hy, hyc⟩ := Multiset.mem_map.1 hi
  rw [hms, Multiset.mem_singleton] at hy
  subst hy
  have hμ : IsSmoothChar (ξ j * absPow k ((-(s i) : ℝ) : ℂ)) := (hξ j).mul (isSmoothChar_absPow _)
  have hc : IrrGL.ofChar (ξ j * absPow k ((-(s i) : ℝ) : ℂ)) hμ = δ i := by
    rw [hδ, ← IrrGL.tw_ofChar _ _ (hξ j) (isSmoothChar_absPow _)]
    change (IrrGL.ofChar (ξ j) (hξ j)).nu _ = _
    rw [← hyc, IrrGL.nu_nu]
    push_cast
    simp
  have h1 := norm_eq_one_of_isUnitarisable hμ (hc ▸ hδu i)
  refine ⟨s i, hs i, fun z => ?_⟩
  have h2 := h1 z
  rw [MonoidHom.mul_apply, Units.val_mul, norm_mul, norm_absPow_ofReal] at h2
  rw [norm_absPow_ofReal]
  have hp : 0 < nabs k z := GlobalTheory.SmGL.nabs_pos' k z
  rw [Real.rpow_neg hp.le] at h2
  have hq : 0 < nabs k z ^ s i := Real.rpow_pos_of_pos hp _
  field_simp at h2
  exact h2

end GlobalTheory.RoadU.Window


open GlobalTheory.RoadU.Window in
theorem GlobalTheory.RoadU.window : UpperTheory.Gal.ToralGalois.Inq → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l n : ℕ), 1 ≤ n → ∀ (π : CuspSub E n) (χ : HChar (maximalRealSubfield E)), InScope .all l π χ → ∀ wt : ℤ, IsWeight π wt → ∀ w : HeightOneSpectrum (𝓞 E), ∀ σ : SmIrr (GL (Fin n) (w.adicCompletion E)), π.IsLocComp w σ → ∀ (ξ : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)), HasSupport (algNorm σ).rep (chars ξ hξ) → Unlinked (chars ξ hξ) → (∀ j, ∃ e : ℝ, |e| < 1 / 2 ∧ ∀ x, ‖((ξ j x : ℂˣ) : ℂ)‖ = ‖((absPow (w.adicCompletion E) ((e - (wt : ℝ) / 2 : ℝ) : ℂ) x : ℂˣ) : ℂ)‖) := by
  intro hI E _ _ _ l n hn π χ _ wt hwt w σ hσ ξ hξ hS hU j
  set c : ℂ := (((wt : ℝ) / 2 : ℝ) : ℂ) with hc
  let ξ' : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ) := fun j => ξ j * absPow (w.adicCompletion E) c
  have hξ' : ∀ j, IsSmoothChar (ξ' j) := fun j => (hξ j).mul (isSmoothChar_absPow _)
  have hT := GlobalTheory.T.supercuspidalSupport_twist_nu_characters (w.adicCompletion E) (algNorm σ) n ξ ξ' hξ hξ' c (fun _ => rfl)
  have hg : IsGeneric ((algNorm σ).nu c).rep := by
    refine GlobalTheory.GalCut.AwayMono.isGeneric_nu (GlobalTheory.GalCut.AwayMono.isGeneric_nu ?_ _) _
    exact (isGeneric_congr (IrrGL.equivOf σ.ρ σ.smooth σ.irred)).1
      (GlobalTheory.CuspRep.Generic.isGeneric_of_isLocComp E n π w σ hσ)
  have hu := GlobalTheory.GalCut7.SizeAway.isUnitarisable E n hn π wt hwt w σ hσ
  obtain ⟨e, he, hx⟩ := exponents_of_genericUnitary hI.gen hI.zel _ hg hu ξ' hξ' (hT.1.1 hS) (hT.2.1 hU) j
  refine ⟨e, he, fun x => ?_⟩
  have h1 := hx x
  simp only [ξ', MonoidHom.mul_apply, Units.val_mul, norm_mul, hc, norm_absPow_ofReal] at h1
  rw [norm_absPow_ofReal]
  have hp : 0 < nabs (w.adicCompletion E) x := GlobalTheory.SmGL.nabs_pos' _ x
  rw [Real.rpow_sub hp, eq_div_iff (Real.rpow_pos_of_pos hp _).ne']
  exact h1

end

section

end
end GalTw
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.ToralDeRham.LocalComponentsOfSmoothCharacters
open GlobalTheory.RoadU
namespace GalTw
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.SphUnr

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_equiv_of_eq {N h : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (GL (Fin N) k) V} {x y : Fin h → IrrGL (k := k)} {hd : ∑ a, (x a).1 = N}
    (φ : Nonempty (ρ.Equiv (prodIrr x hd))) (e : x = y) :
    ∃ hd' : ∑ a, (y a).1 = N, Nonempty (ρ.Equiv (prodIrr y hd')) := by
  subst e
  exact ⟨hd, φ⟩

theorem sum_singleton_eq_map {α : Type*} {h : ℕ} (f : Fin h → α) :
    (∑ i, ({f i} : Multiset α)) = Finset.univ.val.map f := by
  rw [Finset.sum_eq_multiset_sum, ← Multiset.sum_map_singleton (Finset.univ.val.map f), Multiset.map_map]
  rfl

theorem ms_eq_singleton {Δ : Segment k} (h1 : Δ.len = 1) : Δ.ms = {Δ.first} := by
  obtain ⟨z, hz⟩ := Multiset.card_eq_one.1 ((Segment.card_ms Δ).trans h1)
  have h3 : z = Δ.first := by
    have hm : z ∈ Δ.ms := by rw [hz]; exact Multiset.mem_singleton_self z
    obtain ⟨a, ha, rfl⟩ := Segment.mem_carrier.1 (Segment.mem_ms.1 hm)
    obtain rfl : a = 0 := by omega
    simp
  rw [hz, h3]

theorem equiv_prodIrr_chars (hGU : GlobalTheory.Published.GenericUnitaryDualGL) [CharZero k] {N : ℕ} {V : Type}
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth ρ)
    (hi : ρ.IsIrreducible) (hu : IsUnitarisable ρ) (hg : IsGeneric ρ) {n : ℕ} (ξ : Fin n → (kˣ →* ℂˣ))
    (hξ : ∀ j, IsSmoothChar (ξ j)) (hsup : HasSupport ρ (chars ξ hξ)) (hun : Unlinked (chars ξ hξ)) :
    ∃ (h : ℕ) (τ : Fin h → Fin n) (hd : ∑ i, (IrrGL.ofChar (ξ (τ i)) (hξ (τ i))).1 = N),
      Nonempty (ρ.Equiv (prodIrr (fun i => IrrGL.ofChar (ξ (τ i)) (hξ (τ i))) hd)) ∧
      Finset.univ.val.map (fun i => IrrGL.ofChar (ξ (τ i)) (hξ (τ i))) = chars ξ hξ := by
  obtain ⟨h, δ, Δ, s, hL, -, -, hd, ⟨φ⟩⟩ := hGU.exists_prod hs hi hu hg
  let D : Fin h → Segment k := fun i => (Δ i).nu ((s i : ℝ) : ℂ)
  have hL' : ∀ i, IsLSeg (D i) ((δ i).nu ((s i : ℝ) : ℂ)).rep := fun i => GlobalTheory.isLSeg_nu (hL i) _
  have hG : GlobalTheory.Published.GeometricLemma :=
    GlobalTheory.geometricLemma_of_filtration GlobalTheory.Laid.bzfin_holds GlobalTheory.geometricLemmaFiltration_holds
  have hs2 : HasSupport ρ (∑ i, (D i).ms) :=
    GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_of_isSubquotient_prodIrr (fun i => (hL' i).hasSupport) hi
      (IsSubquotient.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective)
  have he := GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_unique hG GlobalTheory.Laid.bzfin_holds hs2 hsup
  have hmem : ∀ i (a : ℕ), a < (D i).len → (D i).first.nu (a : ℂ) ∈ chars ξ hξ := fun i a ha => by
    rw [← he]
    exact Multiset.mem_sum.2 ⟨i, Finset.mem_univ _, Segment.mem_ms.2 (Segment.mem_carrier.2 ⟨a, ha, rfl⟩)⟩
  have hlen : ∀ i, (D i).len = 1 := fun i => by
    by_contra hne
    have h2 : 1 < (D i).len := by have := (D i).len_pos; omega
    have h0 := hmem i 0 (D i).len_pos
    have h1 := hmem i 1 h2
    rw [Nat.cast_zero, IrrGL.nu_zero] at h0
    rw [Nat.cast_one] at h1
    exact hun _ h1 _ h0 rfl
  have hex : ∀ i, ∃ j, (D i).first = IrrGL.ofChar (ξ j) (hξ j) := fun i => by
    have h0 := hmem i 0 (D i).len_pos
    rw [Nat.cast_zero, IrrGL.nu_zero] at h0
    obtain ⟨j, -, hj⟩ := Multiset.mem_map.1 h0
    exact ⟨j, hj.symm⟩
  choose τ hτ using hex
  have hfam : (fun i => (δ i).nu ((s i : ℝ) : ℂ)) = fun i => IrrGL.ofChar (ξ (τ i)) (hξ (τ i)) :=
    funext fun i => (GlobalTheory.GenSph.eq_first_of_isLSeg (hL' i) (hlen i)).trans (hτ i)
  obtain ⟨hd', hφ⟩ := exists_equiv_of_eq ⟨φ⟩ hfam
  refine ⟨h, τ, hd', hφ, ?_⟩
  rw [← he, ← sum_singleton_eq_map]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ms_eq_singleton (hlen i), hτ i]

theorem equiv_prodIrr_untwist {N h : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin N) k) V) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) (x : Fin h → IrrGL (k := k))
    (hd : ∑ a, (x a).1 = N) (φ : Nonempty ((twist ρ (detChar (Fin N) χ)).Equiv (prodIrr x hd))) :
    Nonempty (ρ.Equiv (prodIrr (fun a => (x a).tw χ⁻¹ hχ.inv) hd)) := by
  obtain ⟨φ⟩ := φ
  have e : twist (twist ρ (detChar (Fin N) χ)) (detChar (Fin N) χ⁻¹) = ρ := by
    rw [twist_twist]
    convert twist_one ρ
    ext g
    simp [detChar_apply]
  refine ⟨?_⟩
  rw [← e]
  exact (twistEquiv φ _).trans (prodIrrTwistEquiv x hd χ⁻¹ hχ.inv)


open scoped Classical in
noncomputable def valAt (ϖ : kˣ) (y : IrrGL (k := k)) : ℂˣ := by
  classical
  exact if h : ∃ (μ : kˣ →* ℂˣ) (hμ : IsSmoothChar μ), y = IrrGL.ofChar μ hμ then h.choose ϖ else 1

theorem valAt_ofChar (ϖ : kˣ) (μ : kˣ →* ℂˣ) (hμ : IsSmoothChar μ) : valAt ϖ (IrrGL.ofChar μ hμ) = μ ϖ := by
  have h : ∃ (μ' : kˣ →* ℂˣ) (hμ' : IsSmoothChar μ'), IrrGL.ofChar μ hμ = IrrGL.ofChar μ' hμ' := ⟨μ, hμ, rfl⟩
  rw [valAt, dite_eq_left h]
  obtain ⟨hμ', e⟩ := h.choose_spec
  exact (congrArg (fun f : kˣ →* ℂˣ => f ϖ) (IrrGL.ofChar_inj.1 e)).symm

end Local

section Sph

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))

theorem hasSatGL_of_equiv_prodIrr {n h : ℕ} (σ : SmIrr (GL (Fin n) (w.adicCompletion E)))
    (ζ : Fin h → ((w.adicCompletion E)ˣ →* ℂˣ)) (hζ : ∀ i, IsSmoothChar (ζ i))
    (hd : ∑ i, (IrrGL.ofChar (ζ i) (hζ i)).1 = n)
    (φ : Nonempty (σ.ρ.Equiv (prodIrr (fun i => IrrGL.ofChar (ζ i) (hζ i)) hd)))
    (hunr : ∀ i (x : (w.adicCompletion E)ˣ), Valued.v (x : w.adicCompletion E) = 1 → ζ i x = 1)
    (ϖ : (w.adicCompletion E)ˣ) (hϖ : Valued.v (ϖ : w.adicCompletion E) = WithZero.exp (-1 : ℤ)) :
    GlobalTheory.LFun.HasSatGL w σ.ρ (Finset.univ.val.map fun i => ζ i ϖ) := by
  obtain rfl : h = n := by rw [← hd]; simp [IrrGL.ofChar]
  have hu : ∀ i, IrrGL.ofChar (ζ i) (hζ i) = GlobalTheory.GenSph.uc (w.adicCompletion E) (ζ i ϖ) := fun i =>
    IrrGL.ofChar_inj.2 (eq_unrChar (fun x hx => hunr i x (GlobalTheory.MuInert.valued_eq_one w hx))
      (GlobalTheory.MuInert.valuation_eq_uniformizer w hϖ))
  obtain ⟨hd', ⟨ψ⟩⟩ := GlobalTheory.SphUnr.exists_equiv_of_eq φ (funext hu)
  have hsph : IsSpherical σ.ρ := by
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 (GlobalTheory.GenSph.isSpherical_prodIrr_uc (fun i => ζ i ϖ) hd')
    refine (Submodule.ne_bot_iff _).2 ⟨ψ.symm v, GlobalTheory.LGrp.mem_fixed.2 fun g hg => ?_, fun e => hv0 ?_⟩
    · exact (ψ.symm.toIntertwiningMap.isIntertwining _ _ g v).symm.trans
        (congrArg ψ.symm (GlobalTheory.LGrp.mem_fixed.1 hv g hg))
    · exact ψ.symm.toLinearEquiv.injective (e.trans ψ.symm.toLinearEquiv.map_zero.symm)
  have hS : HasSatake σ.ρ (fun i => ζ i ϖ) := ⟨σ.irred, hsph,
    (IsSubquotient.of_injective ψ.toIntertwiningMap ψ.toLinearEquiv.injective).trans
      (GlobalTheory.GenSph.isSubquotient_prodIrr_uc (fun i => ζ i ϖ) hd')⟩
  exact GlobalTheory.LFun.SatCompare.hasSatGL_of_hasSatakeGL
    ((GlobalTheory.LGrp.SatakeCompare.hasSatakeGL_iff _ _ _ σ.ρ _).2 ⟨_, rfl, hS⟩)

end Sph

section Glob

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem exists_isUnitarisable_twist {a : ℕ} (ha : 1 ≤ a) (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E))
    (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) (hσ : π.IsLocComp w σ) :
    ∃ t : ℝ, IsUnitarisable (twist σ.ρ (detChar (Fin a) (absPow (w.adicCompletion E) ((t : ℝ) : ℂ)))) := by
  obtain ⟨π₀, t, hu, he⟩ := CG.exists_isUnitary_twist_absPow (CG.mk π) ha
  obtain ⟨π₀, rfl⟩ : ∃ p : CuspSub E a, CG.mk p = π₀ := ⟨π₀.out, Quotient.out_eq π₀⟩
  have hiso : CG.mk (π.twist (Model.absPow E (-t))) = CG.mk π₀ := by
    have e1 : CG.mk (π.twist (Model.absPow E (-t))) = (CG.mk π).twist (Model.absPow E (-t)) := rfl
    rw [e1, he, ← CG.twist_mul, mul_comm, CG.absPow_neg_mul, CG.twist_one]
  have hlc := (hσ.twist (Model.absPow E (-t))).congr (Quotient.exact hiso) ⟨Representation.Equiv.refl _⟩
  have hU := GlobalTheory.ResW.isUnitarisable_of_isLocComp_cusp E a π₀ ha ((CG.isUnitary_mk π₀).1 hu) w _ hlc
  refine ⟨-t, ?_⟩
  have hl := GlobalTheory.HeightCounting.Blocks.loc_of_isAbsPow (Model.absPow_isAbsPow E (-t)) w
  change IsUnitarisable (twRep σ.ρ ((GlobalTheory.HeckeGal.Model.absPow E (-t)).loc w |>.comp Matrix.GeneralLinearGroup.det)) at hU
  rw [hl] at hU
  exact hU

end Glob

end GlobalTheory.SphUnr

namespace GlobalTheory.SphUnr

theorem hasSat_of_unlinked_unr : UpperTheory.Gal.ToralGalois.Inq → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n →
    ∀ (π : CuspSub E n) (w : HeightOneSpectrum (𝓞 E)), ∀ σ : SmIrr (GL (Fin n) (w.adicCompletion E)),
    π.IsLocComp w σ → ∀ (ξ : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)),
    HasSupport σ.ρ (chars ξ hξ) → Unlinked (chars ξ hξ) →
    (∀ j (x : (w.adicCompletion E)ˣ), Valued.v (x : w.adicCompletion E) = 1 → ξ j x = 1) →
    ∀ ϖ : (w.adicCompletion E)ˣ, Valued.v (ϖ : w.adicCompletion E) = WithZero.exp (-1 : ℤ) →
    (CG.mk π).HasSat w (Finset.univ.val.map fun j => ξ j ϖ) := by
  intro hI E _ _ _ n hn π w σ hσ ξ hξ hsup hun hunr ϖ hϖ
  have : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  obtain ⟨t, hU⟩ := exists_isUnitarisable_twist hn π w σ hσ
  set χ : (w.adicCompletion E)ˣ →* ℂˣ := absPow (w.adicCompletion E) ((t : ℝ) : ℂ) with hχdef
  have hχ : IsSmoothChar χ := isSmoothChar_absPow _
  have hg : IsGeneric σ.ρ := Generic.isGeneric_of_isLocComp E n π w σ hσ
  have hc := TwistSupp.chars_eq_map_nu ξ (fun j => ξ j * χ) hξ (fun j => (hξ j).mul hχ) ((t : ℝ) : ℂ) fun j => rfl
  have hsup' : HasSupport (twist σ.ρ (detChar (Fin n) χ)) (chars (fun j => ξ j * χ) fun j => (hξ j).mul hχ) := by
    rw [hc]
    exact hsup.tw χ hχ
  have hun' : Unlinked (chars (fun j => ξ j * χ) fun j => (hξ j).mul hχ) := by
    rw [hc, TwistSupp.unlinked_map_nu]
    exact hun
  obtain ⟨h, τ, hd, hφ, hmap⟩ := equiv_prodIrr_chars hI.gen _ (isSmooth_twist σ.smooth hχ.detChar)
    (isIrreducible_twist σ.irred _) hU ((isGeneric_twist_iff χ).2 hg) _ _ hsup' hun'
  have hφ' := equiv_prodIrr_untwist σ.ρ χ hχ _ hd hφ
  have hfam : (fun i => (IrrGL.ofChar (ξ (τ i) * χ) ((hξ (τ i)).mul hχ)).tw χ⁻¹ hχ.inv) =
      fun i => IrrGL.ofChar (ξ (τ i)) (hξ (τ i)) := funext fun i => by
    rw [IrrGL.tw_ofChar]
    exact IrrGL.ofChar_inj.2 (by rw [mul_assoc, mul_inv_cancel, mul_one])
  obtain ⟨hd2, hφ2⟩ := exists_equiv_of_eq hφ' hfam
  have hS := hasSatGL_of_equiv_prodIrr w σ (fun i => ξ (τ i)) (fun i => hξ (τ i)) hd2 hφ2 (fun i => hunr (τ i)) ϖ hϖ
  have hm : Finset.univ.val.map (fun i => ξ (τ i) ϖ) = Finset.univ.val.map fun j => ξ j ϖ := by
    have e := congrArg (Multiset.map fun y => valAt ϖ y * (χ ϖ)⁻¹) hmap
    simp only [chars, Multiset.map_map, Function.comp_def, valAt_ofChar, MonoidHom.mul_apply,
      mul_inv_cancel_right] at e
    exact e
  rw [CG.hasSat_mk, ← hm]
  exact GlobalTheory.HeightCounting.Blocks.hasSatGL_locRep hσ hS

end GlobalTheory.SphUnr

section
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

end
end
end GalTw
end

open GlobalTheory.RoadU

namespace GalTw
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RoadU.TorLift

theorem hasSat_charPol_above : UpperTheory.Gal.ToralGalois.Inq → ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra E Ω] [IsAlgClosure E Ω] (M : Type) [Field M] [NumberField M] [IsCMField M] [Algebra M Ω] [IsAlgClosure M Ω] [Algebra E M] [IsScalarTower E M Ω] (l : ℕ) [Fact l.Prime] (n : ℕ), 1 ≤ n → ∀ (π : CuspSub E n) (χ : HChar (maximalRealSubfield E)), InScope .all l π χ → ∀ (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (u : HeightOneSpectrum (𝓞 M)) (h : IsPlaceOver A w) (h' : IsPlaceOver A u) [u.asIdeal.LiesOver w.asIdeal], ∀ σ : SmIrr (GL (Fin n) (w.adicCompletion E)), π.IsLocComp w σ → ∀ (ξ : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)), HasSupport (algNorm σ).rep (chars ξ hξ) → Unlinked (chars ξ hξ) → ∀ a : Weil h →* (w.adicCompletion E)ˣ, IsLocalArtin h a → ∀ P : CuspSub M n, CharLift π P → (∀ j (x : (u.adicCompletion M)ˣ), Valued.v (x : u.adicCompletion M) = 1 → (ξ j * absPow (w.adicCompletion E) (-((((1 : ℝ) - n) / 2 : ℝ) : ℂ))) (GlobalTheory.BCChar.normU w u x) = 1) → ∃ B : Multiset ℂˣ, (CG.mk P).HasSat u B ∧ ∀ (g₀ : Weil h) (g' : Weil h'), (∀ z : Ω, (g₀ : G E Ω) z = (g' : G M Ω) z) → (satWD h' n B).charPol g' = ∏ j, (X - C ((ξ j (a g₀) : ℂˣ) : ℂ)) := by
  intro hI Ω _ E _ _ _ _ _ M _ _ _ _ _ _ _ l _ n hn π χ hsc A w u h h' _ σ hσ ξ hξ hsup hun a ha P hcl hunr
  classical
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  set s₀ : ℂ := ((((1 : ℝ) - n) / 2 : ℝ) : ℂ) with hs₀
  let ξ0 : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ) := fun j => ξ j * absPow (w.adicCompletion E) (-s₀)
  have hξ0 : ∀ j, IsSmoothChar (ξ0 j) := fun j => (hξ j).mul (isSmoothChar_absPow _)
  have hback : ∀ j, ξ j = ξ0 j * absPow (w.adicCompletion E) s₀ := fun j => by
    simp only [ξ0, mul_assoc, ← absPow_add, neg_add_cancel, absPow_zero, mul_one]

  have hN : ∀ t : ℂ, (absPow (w.adicCompletion E) t).comp (GlobalTheory.BCChar.normU w u) = absPow (u.adicCompletion M) t := by
    letI : Algebra (w.adicCompletion E) (u.adicCompletion M) := (GroundTheory.Global.adicCompletionMap w u).toAlgebra
    have hf := GroundTheory.Global.continuous_adicCompletionMap w u
    haveI : ContinuousSMul (w.adicCompletion E) (u.adicCompletion M) := continuousSMul_of_algebraMap _ _ hf
    haveI : IsScalarTower E (w.adicCompletion E) (u.adicCompletion M) :=
      .of_algebraMap_eq fun x => by
        show _ = GroundTheory.Global.adicCompletionMap w u _
        rw [GroundTheory.Global.adicCompletionMap_algebraMap, IsScalarTower.algebraMap_apply E M (u.adicCompletion M)]
    haveI : FiniteDimensional (w.adicCompletion E) (u.adicCompletion M) := GroundTheory.Global.finite_adicCompletion w u
    haveI : IsModuleTopology (w.adicCompletion E) (u.adicCompletion M) := by
      letI : NontriviallyNormedField (w.adicCompletion E) := Valued.toNontriviallyNormedField _ _
      exact isModuleTopologyOfFiniteDimensional
    exact fun t => GlobalTheory.LBCNu.absPow_comp_norm t

  have hx := (GlobalTheory.RoadU.TwistSupp.supp_nu_chars (w.adicCompletion E) (IrrGL.of σ.ρ σ.smooth σ.irred) n ξ0 ξ hξ0 hξ s₀
    hback).1
  have hsupσ : HasSupport σ.ρ (chars ξ0 hξ0) :=
    (hx.2 hsup).of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred).symm

  obtain ⟨T, hT, -⟩ := LocEx.exists_isLocComp GlobalTheory.automorphicFormsFiniteGL M n P u
  have hsupT := hcl.2 w u σ T hσ hT ξ0 hξ0 hsupσ

  obtain ⟨wt, hwt⟩ := GlobalTheory.PolarizedWeight.exists_isWeight E l n hn π χ hsc
  have hwin := GlobalTheory.RoadU.window hI E l n hn π χ hsc wt hwt w σ hσ ξ hξ hsup hun
  have hunlN := GlobalTheory.RoadU.unlinked_chars_comp_normU E M w u n ((wt : ℝ) / 2) ξ hξ hwin
  have hunl0 : Unlinked (chars (fun j => (ξ0 j).comp (GlobalTheory.BCChar.normU w u))
      fun j => GlobalTheory.BCChar.isSmoothChar_comp_normU w u (hξ0 j)) := by
    rw [GlobalTheory.RoadU.TwistSupp.chars_eq_map_nu (fun j => (ξ j).comp (GlobalTheory.BCChar.normU w u))
      (fun j => (ξ0 j).comp (GlobalTheory.BCChar.normU w u)) (fun j => GlobalTheory.BCChar.isSmoothChar_comp_normU w u (hξ j))
      (fun j => GlobalTheory.BCChar.isSmoothChar_comp_normU w u (hξ0 j)) (-s₀) (fun j => by
        rw [← hN (-s₀)]
        ext x
        rfl), GlobalTheory.RoadU.TwistSupp.unlinked_map_nu]
    exact hunlN

  obtain ⟨ϖ0, hϖ0⟩ := u.valuation_exists_uniformizer M
  have hv : Valued.v ((ϖ0 : M) : u.adicCompletion M) = WithZero.exp (-1 : ℤ) := by
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hϖ0]
  have hne : ((ϖ0 : M) : u.adicCompletion M) ≠ 0 := (Valuation.ne_zero_iff _).1 (by rw [hv]; exact WithZero.exp_ne_zero)
  let ϖ' : (u.adicCompletion M)ˣ := Units.mk0 _ hne
  have hϖ' : Valued.v (ϖ' : u.adicCompletion M) = WithZero.exp (-1 : ℤ) := hv
  have hunrN : ∀ j (x : (u.adicCompletion M)ˣ), Valued.v (x : u.adicCompletion M) = 1 →
      (ξ0 j).comp (GlobalTheory.BCChar.normU w u) x = 1 := hunr
  have hsat := GlobalTheory.SphUnr.hasSat_of_unlinked_unr hI M n hn P u T hT (fun j => (ξ0 j).comp (GlobalTheory.BCChar.normU w u))
    (fun j => GlobalTheory.BCChar.isSmoothChar_comp_normU w u (hξ0 j)) hsupT hunl0 hunrN ϖ' hϖ'
  refine ⟨_, hsat, ?_⟩

  obtain ⟨a', ha'⟩ := GlobalTheory.localArtinExists_holds M Ω A u h'
  intro g₀ g' hgg
  rw [GlobalTheory.SatChar.satWD_charPol_chars Ω M u A h' n (fun j => (ξ0 j).comp (GlobalTheory.BCChar.normU w u))
    (fun j => (ξ0 j).comp (GlobalTheory.BCChar.normU w u) * absPow (u.adicCompletion M) s₀) (fun j => rfl) hunrN ϖ' hϖ' a' ha' g']
  have hart := GlobalTheory.ArtinNormU.localArtin_normU E M Ω A w u h h' a a' ha ha' g₀ g' hgg
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [hart, hback j, ← hN s₀]
  rfl

end GlobalTheory.RoadU.TorLift

section
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem GlobalTheory.T.frobenius_charpoly_eq_satake_of_place_above : UpperTheory.Gal.ToralGalois.Inq → ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra E Ω] [IsAlgClosure E Ω] (M : Type) [Field M] [NumberField M] [IsCMField M] [Algebra M Ω] [IsAlgClosure M Ω] [Algebra E M] [IsScalarTower E M Ω] (l : ℕ) [Fact l.Prime] (n : ℕ), 1 ≤ n → ∀ (π : CuspSub E n) (χ : HChar (maximalRealSubfield E)), InScope .all l π χ → ∀ (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (u : HeightOneSpectrum (𝓞 M)) (h : IsPlaceOver A w) (h' : IsPlaceOver A u) [u.asIdeal.LiesOver w.asIdeal], ∀ σ : SmIrr (GL (Fin n) (w.adicCompletion E)), π.IsLocComp w σ → ∀ (ξ : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)), HasSupport (algNorm σ).rep (chars ξ hξ) → Unlinked (chars ξ hξ) → ∀ a : Weil h →* (w.adicCompletion E)ˣ, IsLocalArtin h a → ∀ P : CuspSub M n, CharLift π P → (∀ j (x : (u.adicCompletion M)ˣ), Valued.v (x : u.adicCompletion M) = 1 → (ξ j * absPow (w.adicCompletion E) (-((((1 : ℝ) - n) / 2 : ℝ) : ℂ))) (GlobalTheory.BCChar.normU w u x) = 1) → ∃ B : Multiset ℂˣ, (CG.mk P).HasSat u B ∧ ∀ (g₀ : Weil h) (g' : Weil h'), (∀ z : Ω, (g₀ : G E Ω) z = (g' : G M Ω) z) → (satWD h' n B).charPol g' = ∏ j, (X - C ((ξ j (a g₀) : ℂˣ) : ℂ)) := by
  first | (exact @GlobalTheory.RoadU.TorLift.hasSat_charPol_above) | (exact GlobalTheory.RoadU.TorLift.hasSat_charPol_above) | (intros; apply GlobalTheory.RoadU.TorLift.hasSat_charPol_above  <;> assumption)

end
end
end GalTw
end

open GlobalTheory.RoadU

namespace GalTw
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RoadU

theorem liesOver_of_isPlaceOver {E M Ω : Type} [Field E] [NumberField E] [Field M] [NumberField M] [Field Ω]
    [Algebra E Ω] [Algebra M Ω] [Algebra E M] [IsScalarTower E M Ω] {A : ValuationSubring Ω}
    {w : HeightOneSpectrum (𝓞 E)} {u : HeightOneSpectrum (𝓞 M)} (h : IsPlaceOver A w) (h' : IsPlaceOver A u) :
    u.asIdeal.LiesOver w.asIdeal := by
  refine ⟨Ideal.ext fun x => ?_⟩
  rw [Ideal.under, Ideal.mem_comap, ← h x, ← h' _]
  have : algebraMap M Ω ((algebraMap (𝓞 E) (𝓞 M) x : 𝓞 M) : M) = algebraMap E Ω (x : E) := by
    rw [IsScalarTower.algebraMap_apply E M Ω]
    rfl
  rw [this]

theorem exists_sph_lift_of_toral : UpperTheory.Gal.ToralGalois.Inq → ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ (π : CuspSub E n) (χ : HChar (maximalRealSubfield E)), InScope .all l π χ → ∀ r : G E Ω →* GL (Fin n) (Qbar l), Weak π ι r → ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w), ∀ σ : SmIrr (GL (Fin n) (w.adicCompletion E)), π.IsLocComp w σ → ∀ (ξ : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)), HasSupport (algNorm σ).rep (chars ξ hξ) → Unlinked (chars ξ hξ) → ∀ a : Weil h →* (w.adicCompletion E)ˣ, IsLocalArtin h a → ∀ g : Weil h, deg g ≠ 0 → ∃ (M : Type) (_ : Field M) (_ : NumberField M) (_ : IsCMField M) (_ : Algebra M Ω) (_ : IsAlgClosure M Ω) (_ : Algebra E M) (_ : IsScalarTower E M Ω) (u : HeightOneSpectrum (𝓞 M)) (h' : IsPlaceOver A u) (P : CuspSub M n) (χ' : HChar (maximalRealSubfield M)), InScope .all l P χ' ∧ IsLift π P ∧ (∀ x : M, (g : G E Ω) (algebraMap M Ω x) = algebraMap M Ω x) ∧ ∃ B : Multiset ℂˣ, (CG.mk P).HasSat u B ∧ ∀ (g₀ : Weil h) (g' : Weil h'), (∀ z : Ω, (g₀ : G E Ω) z = (g' : G M Ω) z) → (satWD h' n B).charPol g' = ∏ j, (X - C ((ξ j (a g₀) : ℂˣ) : ℂ)) := by
  intro hI Ω _ E _ _ _ _ _ l _ ι n hn π χ hπ r hr w A h σ hσ ξ hξ hsupp hunl a ha g hg
  let ξ₀ : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ) := fun j =>
    ξ j * absPow (w.adicCompletion E) (-((((1 : ℝ) - n) / 2 : ℝ) : ℂ))
  have hξ₀ : ∀ j, IsSmoothChar (ξ₀ j) := fun j => (hξ j).mul (isSmoothChar_absPow _)
  obtain ⟨M, _, _, _, _, _, _, _, P, χ', hP, hcl, hfix, hkill⟩ :=
    GlobalTheory.T.weaklyAttached_toral_of_cm_lift hI Ω E l ι n hn π χ hπ r hr w A h ξ₀ hξ₀ a ha g hg
  obtain ⟨u, h', -⟩ := GlobalTheory.T.exists_isPlaceOver_finiteExtension_of_isPlaceOver E M Ω A w h
  haveI := liesOver_of_isPlaceOver (M := M) h h'
  have hunr := GlobalTheory.T.unramified_comp_norm_of_killed_inertia_fixing Ω E M A w u h h' n ξ₀ a ha hkill
  obtain ⟨B, hB, hch⟩ :=
    GlobalTheory.T.frobenius_charpoly_eq_satake_of_place_above hI Ω E M l n hn π χ hπ A w u h h' σ hσ ξ hξ hsupp hunl a ha P hcl hunr
  exact ⟨M, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    u, h', P, χ', hP, hcl.1, hfix, B, hB, hch⟩

end GlobalTheory.RoadU

end

section
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem GlobalTheory.T.frobenius_charpoly_of_unlinked_unramified_support : UpperTheory.Gal.ToralGalois.Inq → ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ (π : CuspSub E n) (χ : HChar (maximalRealSubfield E)), InScope .all l π χ → ∀ r : G E Ω →* GL (Fin n) (Qbar l), Weak π ι r → ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w), ∀ σ : SmIrr (GL (Fin n) (w.adicCompletion E)), π.IsLocComp w σ → ∀ (ξ : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)), HasSupport (algNorm σ).rep (chars ξ hξ) → Unlinked (chars ξ hξ) → ∀ a : Weil h →* (w.adicCompletion E)ˣ, IsLocalArtin h a → ∀ g : Weil h, deg g ≠ 0 → ∃ (M : Type) (_ : Field M) (_ : NumberField M) (_ : IsCMField M) (_ : Algebra M Ω) (_ : IsAlgClosure M Ω) (_ : Algebra E M) (_ : IsScalarTower E M Ω) (u : HeightOneSpectrum (𝓞 M)) (h' : IsPlaceOver A u) (P : CuspSub M n) (χ' : HChar (maximalRealSubfield M)), InScope .all l P χ' ∧ IsLift π P ∧ (∀ x : M, (g : G E Ω) (algebraMap M Ω x) = algebraMap M Ω x) ∧ ∃ B : Multiset ℂˣ, (CG.mk P).HasSat u B ∧ ∀ (g₀ : Weil h) (g' : Weil h'), (∀ z : Ω, (g₀ : G E Ω) z = (g' : G M Ω) z) → (satWD h' n B).charPol g' = ∏ j, (X - C ((ξ j (a g₀) : ℂˣ) : ℂ)) := by
  first | (exact @GlobalTheory.RoadU.exists_sph_lift_of_toral) | (exact GlobalTheory.RoadU.exists_sph_lift_of_toral) | (intros; apply GlobalTheory.RoadU.exists_sph_lift_of_toral  <;> assumption)

end
