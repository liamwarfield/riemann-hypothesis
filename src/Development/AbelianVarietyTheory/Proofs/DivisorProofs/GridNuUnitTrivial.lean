module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAffineNeighbourhoodExists
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OmPinsTr

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridNuUnitTrivial
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.BotPairSmall.CondNu
variable {D : D7}

open GlobalTheory.Mem.Col2.SplitChar in
theorem vl_le_of_mem_hatId {I : Ideal (𝓞 D.host.E)} {PP : HeightOneSpectrum (𝓞 D.host.E)} {n : ℕ}
    (hI : I ≤ PP.asIdeal ^ n) {x : AE D} (hx : x ∈ hatId D I) : vl D PP x ≤ WithZero.exp (-(n : ℤ)) := by
  induction hx using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, s, hs, rfl⟩ := hy
    rw [map_mul, vl_inc]
    refine (mul_le_of_le_one_right' (vl_le hs PP)).trans ?_
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact (HeightOneSpectrum.intValuation_le_pow_iff_mem PP b n).2 (hI hb)
  | zero => simp
  | add a b _ _ ha hb => exact (Valuation.map_add _ _ _).trans (max_le ha hb)
  | neg a _ ha => rwa [Valuation.map_neg]

theorem sgA_mem_hatId {I : Ideal (𝓞 D.host.E)} {x : AE D} (hx : x ∈ hatId D I) : sgA D x ∈ hatId D (D.host.conj • I) := by
  induction hx using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, s, hs, rfl⟩ := hy
    refine AddSubgroup.subset_closure ⟨D.host.conj • b, Ideal.smul_mem_pointwise_smul _ _ _ hb, sgA D s,
      GlobalTheory.NormSum.UnramHecke.sgA_mem D hs, ?_⟩
    rw [map_mul, GlobalTheory.Mem.Col2.SplitChar.sgA_inc]
    rfl
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | neg a _ ha => rw [map_neg]; exact neg_mem ha

theorem conj_mul_conj (D : D7) : D.host.conj * D.host.conj = 1 :=
  AlgEquiv.ext fun z => GlobalTheory.NormSum.UnramHecke.conj_conj D z

theorem conj_smul_le (𝔪 : Ideal (𝓞 D.host.E)) : D.host.conj • (𝔪 * D.host.conj • 𝔪) ≤ 𝔪 := by
  have e : D.host.conj • D.host.conj • 𝔪 = 𝔪 := by rw [smul_smul, conj_mul_conj, one_smul]
  calc D.host.conj • (𝔪 * D.host.conj • 𝔪) ≤ D.host.conj • D.host.conj • 𝔪 :=
        Ideal.map_mono (Ideal.mul_le_inf.trans inf_le_right)
    _ = 𝔪 := e


open GlobalTheory.Mem.Col2.SplitChar in
theorem vl_sub_le {T : Type} {L : LevCh D T} (P : Places L) {u : (AE D)ˣ}
    (hu : (u : AE D) - 1 ∈ hatId D (condE P * D.host.conj • condE P)) {PP : HeightOneSpectrum (𝓞 D.host.E)}
    (hv : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∈ P.S0) :
    vl D PP ((u : AE D) - 1) ≤ WithZero.exp (-(condExp P ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) : ℤ)) := by
  obtain ⟨c, hc, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm D.R D.host
  set v := (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) with hvdef
  have hw : (P.w v).under (𝓞 D.host.F) = v := P.under_w hv
  have hle : condE P ≤ (P.w v).asIdeal ^ condExp P v := Ideal.le_of_dvd (Finset.dvd_prod_of_mem _ hv)
  rcases (GlobalTheory.Mem.Chr.under_eq_iff_conjPl c hcm.rank hcm.ne (P.w v) PP).1 (by rw [hw]) with e | h
  · rw [e]
    exact vl_le_of_mem_hatId ((Ideal.mul_le_inf.trans inf_le_left).trans (e ▸ hle)) hu
  · have e : c.toRingEquiv = D.host.conj.toRingEquiv := RingEquiv.ext hc
    rw [e] at h
    rw [← GlobalTheory.NormSum.UnramHecke.sgA_sgA D ((u : AE D) - 1), vl_sgA h]
    exact vl_le_of_mem_hatId ((conj_smul_le _).trans hle) (sgA_mem_hatId hu)


open GlobalTheory.Mem.Col2.SplitChar Formalism.L2.Host in
theorem nuH_inv_eq_one_of_cong : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ → ∀ (G : GridData L sc) (i j : Fin D.R.m) (u : (AE D)ˣ), IntU D u → (u : AE D) - 1 ∈ hatId D (condE G.pl * D.host.conj • condE G.pl) → (nuH G μ₀ i j)⁻¹.1 (finIdl D u) = 1 := by
  intro D T L sc μ₀ hL G i j u hu hc
  refine GlobalTheory.Mem.LocTriv.eq_one_of_local D.host.E _ (nuH G μ₀ i j)⁻¹.2.1 (finIdl D u) (finIdl_unit hu)
    (fun w => by rw [finIdl_fst]; rfl) fun PP x hx => ?_
  have hunit : IsUnitAt PP x := by
    unfold IsUnitAt
    rw [hx]
    exact finIdl_unit hu PP
  have hsub : Valued.v ((x : PP.adicCompletion D.host.E) - 1) = vl D PP ((u : AE D) - 1) := by
    rw [hx, vl_sub_one]
  have hμ : (L.C.mu0 j).loc PP x = 1 := by
    by_cases hg : ∃ k, OverP D.host (D.host.g k) PP
    · obtain ⟨k, hk⟩ := hg
      have hS : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∈ G.pl.S0 := by
        refine G.pl.mem_S0_of_sum_eq.2 (Or.inr ((S1_mem_OmF D).2 ?_))
        have : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)).asIdeal := by
          change _ ∈ PP.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))
          rw [Ideal.mem_comap, map_natCast]
          exact hk
        fin_cases k
        · exact Or.inl this
        · exact Or.inr (Or.inl this)
      refine (L.C.isMu0 j).tame PP x hunit ?_
      rw [hsub]
      refine (vl_sub_le G.pl hc hS).trans ?_
      have : 1 ≤ condExp G.pl ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) := by unfold condExp; split_ifs <;> omega
      exact WithZero.exp_le_exp.2 (by omega)
    · push_neg at hg
      exact (L.C.isMu0 j).unr PP hg x hunit
  have hχ : (G.ch.chiH (D.R.m - i)).loc PP x = 1 := by
    have h1 : 1 ≤ D.R.m - (i : ℕ) := by omega
    have h2 : D.R.m - (i : ℕ) ≤ D.R.m := by omega
    by_cases hS : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∈ G.pl.S0
    · have hb := vl_sub_le G.pl hc hS
      rw [← hsub] at hb
      rcases G.pl.mem_S0_of_sum_eq.1 hS with h0 | h1'
      · rw [condExp, if_pos h0] at hb
        exact (G.ch.lev0 _ h1 h2 PP h0).1 x hunit (by simpa using hb)
      · have hne : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ G.pl.v0 := fun e => G.ch.basePlace_not_mem_chiGridBadPlaces (e ▸ h1')
        rw [condExp, if_neg hne] at hb
        exact (G.ch.lev1 _ h1 h2 PP h1').1 x hunit (by simpa using hb)
    · exact G.ch.unr _ h1 h2 PP hS x hunit
  show ((nuH G μ₀ i j).loc PP x)⁻¹ = 1
  rw [nuH, hL.xi_base, mul_one, div_eq_mul_inv]
  change ((L.C.mu0 j).loc PP x * ((G.ch.chiH (D.R.m - i)).loc PP x)⁻¹)⁻¹ = 1
  rw [hμ, hχ]
  simp
end GlobalTheory.BotPairSmall.CondNu

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUpperOfMulEqOne
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.BotPairSmall

theorem hatId_mul_of_mem_OhE (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) {x y : AE D} (hx : x ∈ OhE D)
    (hy : y ∈ hatId D 𝔪) : x * y ∈ hatId D 𝔪 := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, s, hs, rfl⟩ := hy
    exact AddSubgroup.subset_closure ⟨b, hb, x * s, (OhE D).mul_mem hx hs, by ring⟩
  | zero => simp
  | add y z _ _ h1 h2 => rw [mul_add]; exact add_mem h1 h2
  | neg y _ h => rw [mul_neg]; exact neg_mem h

def blockUpperSub (R : Type) [CommRing R] (N a : ℕ) : Subalgebra R (Matrix (Fin N) (Fin N) R) where
  carrier := {A | ∀ i j : Fin N, j.1 < a → a ≤ i.1 → A i j = 0}
  mul_mem' {A B} hA hB i j hj hi := by
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : l.1 < a
    · rw [hA i l hl hi, zero_mul]
    · rw [hB l j hj (not_lt.1 hl), mul_zero]
  add_mem' {A B} hA hB i j hj hi := by simp [hA i j hj hi, hB i j hj hi]
  algebraMap_mem' r i j hj hi := by
    have : i ≠ j := fun e => by subst e; omega
    simp [Algebra.algebraMap_eq_smul_one, Matrix.one_apply_ne this]

theorem blockUpper_of_mul_eq_one {R : Type} [CommRing R] {N a : ℕ} {A B : Matrix (Fin N) (Fin N) R}
    (hAB : A * B = 1) (hA : ∀ i j : Fin N, j.1 < a → a ≤ i.1 → A i j = 0) :
    ∀ i j : Fin N, j.1 < a → a ≤ i.1 → B i j = 0 := by
  have hA' : A ∈ blockUpperSub R N a := hA
  have hBA : B * A = 1 := mul_eq_one_comm.1 hAB
  set p := A.charpoly
  have hq : Polynomial.aeval A p.divX ∈ blockUpperSub R N a :=
    Algebra.adjoin_le (Set.singleton_subset_iff.2 hA') (Polynomial.aeval_mem_adjoin_singleton R _)
  have hCH : Polynomial.aeval A p = 0 := Matrix.aeval_self_charpoly A
  rw [← Polynomial.X_mul_divX_add p, map_add (f := _), map_mul, Polynomial.aeval_X, Polynomial.aeval_C] at hCH
  have h2 : p.coeff 0 • B = -Polynomial.aeval A p.divX := by
    have := congrArg (fun M => B * M) hCH
    simp only [mul_add, ← mul_assoc, hBA, one_mul, mul_zero, Algebra.algebraMap_eq_smul_one, Matrix.mul_smul,
      mul_one] at this
    rw [eq_neg_iff_add_eq_zero, add_comm]; exact this
  have hdet : A.det * B.det = 1 := by rw [← Matrix.det_mul, hAB, Matrix.det_one]
  rw [Matrix.det_eq_sign_charpoly_coeff] at hdet
  have hB : B ∈ blockUpperSub R N a := by
    have hu : ((-1) ^ Fintype.card (Fin N) * B.det) * p.coeff 0 = 1 := by linear_combination hdet
    have : B = ((-1) ^ Fintype.card (Fin N) * B.det) • (p.coeff 0 • B) := by rw [smul_smul, hu, one_smul]
    rw [this, h2]
    exact Subalgebra.smul_mem _ (neg_mem hq) _
  exact hB

def blockLevelSub (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (a N : ℕ) : Subgroup (GA D N) where
  carrier := blockSet D 𝔪 a N
  one_mem' := by
    refine ⟨one_mem _, fun i j hj hi => ?_⟩
    have hij : i ≠ j := fun e => by subst e; omega
    simp [Matrix.one_apply_ne hij]
  mul_mem' {x y} hx hy := by
    have hX := (GlobalTheory.NormSum.mem_intG x).1 hx.1
    have hY := (GlobalTheory.NormSum.mem_intG y).1 hy.1
    refine ⟨mul_mem hx.1 hy.1, fun i j hj hi => ?_⟩
    rw [Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply]
    refine sum_mem fun l _ => ?_
    by_cases hl : l.1 < a
    · rw [mul_comm]; exact hatId_mul_of_mem_OhE D 𝔪 (hY l j).1 (hx.2 i l hl hi)
    · exact hatId_mul_of_mem_OhE D 𝔪 (hX i l).1 (hy.2 l j hj (not_lt.1 hl))
  inv_mem' {x} hx := by
    refine ⟨inv_mem hx.1, fun i j hj hi => ?_⟩
    have hI := (GlobalTheory.NormSum.mem_intG x).1 hx.1
    let J : Ideal (OhE D) :=
      { carrier := {z | (z : AE D) ∈ hatId D 𝔪}
        add_mem' := fun {u v} hu hv => by simpa using add_mem hu hv
        zero_mem' := by simp
        smul_mem' := fun c z hz => by simpa using hatId_mul_of_mem_OhE D 𝔪 c.2 hz }
    let M : Matrix (Fin N) (Fin N) (OhE D) := fun i j => ⟨_, (hI i j).1⟩
    let M' : Matrix (Fin N) (Fin N) (OhE D) := fun i j => ⟨_, (hI i j).2⟩
    have hMM : M * M' = 1 := by
      have hinj : Function.Injective fun A : Matrix (Fin N) (Fin N) (OhE D) => A.map (OhE D).subtype :=
        fun A B e => by
          ext i j
          exact congrFun (congrFun e i) j
      apply hinj
      change (M * M').map (OhE D).subtype = (1 : Matrix (Fin N) (Fin N) (OhE D)).map (OhE D).subtype
      rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
      have e1 : M.map (OhE D).subtype = ((x : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) := by
        ext; rfl
      have e2 : M'.map (OhE D).subtype =
          (((x : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) := by
        ext; rfl
      rw [e1, e2, Units.mul_inv]
    have hred := blockUpper_of_mul_eq_one (a := a) (A := M.map (Ideal.Quotient.mk J))
      (B := M'.map (Ideal.Quotient.mk J))
      (by rw [← Matrix.map_mul, hMM, Matrix.map_one _ (map_zero _) (map_one _)])
      (fun i j hj hi => by
        rw [Matrix.map_apply]
        exact Ideal.Quotient.eq_zero_iff_mem.2 (hx.2 i j hj hi)) i j hj hi
    rw [Matrix.map_apply] at hred
    have hm := Ideal.Quotient.eq_zero_iff_mem.1 hred
    exact hm

theorem blockJ_mem_iff_blockSet : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (a N : ℕ) (h : GA D N),
    h ∈ GlobalTheory.BotPairSmall.blockJ D 𝔪 a N ↔ h ∈ GlobalTheory.BotPairSmall.blockSet D 𝔪 a N := by
  intro D 𝔪 a N h
  constructor
  · intro hh
    exact (Subgroup.closure_le (blockLevelSub D 𝔪 a N)).2 (fun _ hx => hx) hh
  · intro hh
    exact Subgroup.subset_closure hh

end GlobalTheory.BotPairSmall
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeGenericNeZeroEquidimensional
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeGenericNeZeroEquidimensional
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GenFinite

theorem finiteDimensional_of_trdeg_eq (F A B K L : Type) [Field F] [CommRing A] [IsDomain A]
    [CommRing B] [IsDomain B] [Field K] [Field L] [Algebra F A] [Algebra A B] [Algebra F B]
    [IsScalarTower F A B] [Algebra A K] [Algebra B L] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L] [IsFractionRing A K] [IsFractionRing B L]
    [Algebra.FiniteType A B] (n : ℕ) (hA : Algebra.trdeg F A = n) (hB : Algebra.trdeg F B = n) :
    FiniteDimensional K L := by
  letI : Algebra F K := ((algebraMap A K).comp (algebraMap F A)).toAlgebra
  letI : Algebra F L := ((algebraMap B L).comp (algebraMap F B)).toAlgebra
  haveI : IsScalarTower F A K := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower F B L := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower F K L := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    change algebraMap B L (algebraMap F B x) = algebraMap K L (algebraMap A K (algebraMap F A x))
    rw [← IsScalarTower.algebraMap_apply A K L, IsScalarTower.algebraMap_apply A B L,
      ← IsScalarTower.algebraMap_apply F A B]
  haveI : FaithfulSMul F A := (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap F A).injective
  haveI : FaithfulSMul F B := (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap F B).injective
  haveI : FaithfulSMul A K := (faithfulSMul_iff_algebraMap_injective _ _).mpr (IsFractionRing.injective A K)
  haveI : FaithfulSMul B L := (faithfulSMul_iff_algebraMap_injective _ _).mpr (IsFractionRing.injective B L)
  haveI : Algebra.IsAlgebraic A K := IsLocalization.isAlgebraic K (nonZeroDivisors A)
  haveI : Algebra.IsAlgebraic B L := IsLocalization.isAlgebraic L (nonZeroDivisors B)
  have hK : Algebra.trdeg F K = n := (trdeg_eq_of_isAlgebraic_top F A K).trans hA
  have hL : Algebra.trdeg F L = n := (trdeg_eq_of_isAlgebraic_top F B L).trans hB
  have h0 : Algebra.trdeg K L = 0 := by
    have e := trdeg_add_eq F K (A := L)
    rw [hK, hL] at e
    rcases (Cardinal.add_eq_left_iff).1 e with h | h
    · exact absurd (le_trans (le_max_left _ _) h) (not_le.2 (Cardinal.natCast_lt_aleph0))
    · exact h
  haveI : Algebra.IsAlgebraic K L := trdeg_eq_zero_iff.1 h0
  obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType A B).out
  let g : B →ₐ[A] L := IsScalarTower.toAlgHom A B L
  let T : IntermediateField K L := IntermediateField.adjoin K (g '' (s : Set B))
  have hfin : FiniteDimensional K T :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have hrange : ∀ b : B, algebraMap B L b ∈ T := by
    intro b
    have hb : b ∈ Algebra.adjoin A (s : Set B) := hs ▸ Algebra.mem_top
    have : g b ∈ (Algebra.adjoin A (s : Set B)).map g := Subalgebra.mem_map.2 ⟨b, hb, rfl⟩
    rw [AlgHom.map_adjoin] at this
    have hle : Algebra.adjoin A (g '' (s : Set B)) ≤ T.toSubalgebra.restrictScalars A :=
      Algebra.adjoin_le (IntermediateField.subset_adjoin K _)
    exact hle this
  have htop : T = ⊤ := by
    refine eq_top_iff.2 fun l _ => ?_
    obtain ⟨x, y, _, rfl⟩ := IsFractionRing.div_surjective (A := B) l
    exact T.div_mem (hrange x) (hrange y)
  rw [htop] at hfin
  exact LinearEquiv.finiteDimensional (IntermediateField.topEquiv (F := K) (E := L)).toLinearEquiv

end GlobalTheory.GenFinite

namespace GlobalTheory.GenFinite

theorem trdeg_affineOpen_eq (F : Type) [Field F] {Y : Scheme.{0}} [IsIntegral Y]
    (q : Y ⟶ Sp F) [LocallyOfFiniteType q] {U : Y.Opens} (hU : IsAffineOpen U)
    (hne : (U : Set Y).Nonempty) [Algebra F Γ(Y, U)] [Algebra.FiniteType F Γ(Y, U)] (n : ℕ)
    (hn : topologicalKrullDim Y = n) : Algebra.trdeg F Γ(Y, U) = n := by
  haveI : Nonempty U := ⟨⟨hne.some, hne.some_mem⟩⟩
  obtain ⟨d, h₁, h₂⟩ := exists_ringKrullDim_eq_and_trdeg_eq F Γ(Y, U)
  have e : topologicalKrullDim (U : Set Y) = d := by
    rw [← h₁, ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact topologicalKrullDim_eq_of_isEmbedding hU.fromSpec.isOpenEmbedding.isEmbedding
      hU.range_fromSpec
  rw [GlobalTheory.OpenDim.topologicalKrullDim_open F q U hne, hn] at e
  have hd : d = n := by exact_mod_cast e.symm
  rw [h₂, hd]

theorem residueDegree_genericPoint_ne_zero : ∀ (F : Type) [Field F] (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (p : W ⟶ Sp F) (f : M ⟶ W) (n : ℕ), LocallyOfFiniteType p → LocallyOfFiniteType f → Surjective f → topologicalKrullDim M = n → topologicalKrullDim W = n → f.residueDegree (genericPoint M) ≠ 0 := by
  intro F _ M W _ _ p f n hp hf hs hM hW
  have hη : f (genericPoint M) = genericPoint W := by
    have := (genericPoint_spec M).image f.continuous
    rw [Set.image_univ, f.surjective.range_eq, closure_univ] at this
    exact this.eq (genericPoint_spec W)
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ := W.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (genericPoint W)) isOpen_univ
  have hV : IsAffineOpen V := hV
  have hx : f (genericPoint M) ∈ V := hη ▸ hxV
  obtain ⟨_, ⟨U, hU, rfl⟩, hy, hUV⟩ := M.isBasis_affineOpens.exists_subset_of_mem_open
    (show genericPoint M ∈ f ⁻¹ᵁ V from hx) (f ⁻¹ᵁ V).isOpen
  have hU : IsAffineOpen U := hU
  haveI : Nonempty V := ⟨⟨_, hx⟩⟩
  haveI : Nonempty U := ⟨⟨_, hy⟩⟩
  have e : U ≤ f ⁻¹ᵁ V := hUV
  let φ := Spec.preimage (hV.fromSpec ≫ p)
  have hφ : Spec.map φ = hV.fromSpec ≫ p := Spec.map_preimage _
  letI : Algebra F Γ(W, V) := φ.hom.toAlgebra
  have hftA : Algebra.FiniteType F Γ(W, V) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := φ)).mp (hφ ▸ inferInstance)
  letI : Algebra Γ(W, V) Γ(M, U) := (f.appLE V U e).hom.toAlgebra
  have hftB : Algebra.FiniteType Γ(W, V) Γ(M, U) :=
    HasRingHomProperty.appLE @LocallyOfFiniteType f hf ⟨V, hV⟩ ⟨U, hU⟩ e
  letI : Algebra F Γ(M, U) := (φ ≫ f.appLE V U e).hom.toAlgebra
  haveI : IsScalarTower F Γ(W, V) Γ(M, U) := IsScalarTower.of_algebraMap_eq' rfl
  have hftC : Algebra.FiniteType F Γ(M, U) := Algebra.FiniteType.trans hftA hftB
  have hA : Algebra.trdeg F Γ(W, V) = n := trdeg_affineOpen_eq F p hV ⟨_, hx⟩ n hW
  have hB : Algebra.trdeg F Γ(M, U) = n := trdeg_affineOpen_eq F (f ≫ p) hU ⟨_, hy⟩ n hM
  letI := (W.evaluation V _ hx).hom.toAlgebra
  letI := (M.evaluation U _ hy).hom.toAlgebra
  letI := (f.residueFieldMap (genericPoint M)).hom.toAlgebra
  letI : Algebra Γ(W, V) (M.residueField (genericPoint M)) :=
    (f.appLE V U e ≫ M.evaluation U _ hy).hom.toAlgebra
  haveI : IsScalarTower Γ(W, V) Γ(M, U) (M.residueField (genericPoint M)) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have nat : f.appLE V U e ≫ M.evaluation U _ hy =
      W.evaluation V _ hx ≫ f.residueFieldMap (genericPoint M) := by
    rw [Scheme.evaluation_naturality f _ hx, Scheme.Hom.appLE, Category.assoc]
    congr 1
    simp only [Scheme.evaluation]
    rw [← Category.assoc, TopCat.Presheaf.germ_res]
  haveI : IsScalarTower Γ(W, V) (W.residueField (f (genericPoint M)))
      (M.residueField (genericPoint M)) :=
    IsScalarTower.of_algebraMap_eq' congr($(nat).hom)
  haveI := GenFiniteEtale.isFractionRing_eval W hV hη hx
  haveI := GenFiniteEtale.isFractionRing_eval M hU rfl hy
  have := finiteDimensional_of_trdeg_eq F Γ(W, V) Γ(M, U) (W.residueField (f (genericPoint M)))
    (M.residueField (genericPoint M)) n hA hB
  change Module.finrank (W.residueField (f (genericPoint M))) (M.residueField (genericPoint M)) ≠ 0
  exact Module.finrank_pos.ne'

end GlobalTheory.GenFinite
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeGenericNeZeroEquidimensionalStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residue_degree_generic_ne_zero_equidimensional : ∀ (F : Type) [Field F] (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (p : W ⟶ Sp F) (f : M ⟶ W) (n : ℕ), LocallyOfFiniteType p → LocallyOfFiniteType f → Surjective f → topologicalKrullDim M = n → topologicalKrullDim W = n → f.residueDegree (genericPoint M) ≠ 0 := by
  first | exact @GlobalTheory.GenFinite.residueDegree_genericPoint_ne_zero | exact GlobalTheory.GenFinite.residueDegree_genericPoint_ne_zero | (intros; apply GlobalTheory.GenFinite.residueDegree_genericPoint_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicThetaSumNormLePolynomialScale
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicThetaSumNormLePolynomialScale
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
namespace GlobalTheory.LatScaleSum

open mixedEmbedding

theorem evI_algebraMap (F : Type) [Field F] [NumberField F] (x : F) :
    evI F (algebraMap F (AF F) x) = mixedEmbedding F x := by
  unfold evI
  simp [InfiniteAdeleRing.ringEquiv_mixedSpace]
  rfl

noncomputable abbrev latPi (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    Submodule ℤ (κ → mixedSpace F) :=
  Submodule.span ℤ (Set.range (Pi.basis (fun _ : κ => latticeBasis F)))

theorem mem_latPi (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (y : κ → F)
    (hy : ∀ i, IsIntegral ℤ (y i)) : (fun i => mixedEmbedding F (y i)) ∈ latPi F κ := by
  rw [Module.Basis.mem_span_iff_repr_mem]
  intro ji
  rw [Pi.basis_repr]
  have h1 : mixedEmbedding F (y ji.1) ∈ mixedEmbedding.integerLattice F := by
    exact ⟨⟨y ji.1, hy ji.1⟩, rfl⟩
  have h2 := (mem_span_latticeBasis F).mpr h1
  exact (Module.Basis.mem_span_iff_repr_mem ℤ _ _).mp h2 ji.2

theorem summable_inv_one_add_pow (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    Summable fun z : latPi F κ =>
      ((1 + ‖(z : κ → mixedSpace F)‖) ^ (Module.finrank ℤ (latPi F κ) + 1))⁻¹ := by
  set N : ℕ := Module.finrank ℤ (latPi F κ) + 1 with hN
  have h0 := ZLattice.summable_norm_rpow (latPi F κ) (-(N : ℝ)) (by rw [hN]; push_cast; linarith)
  have h1 : Summable fun z : latPi F κ => (if z = 0 then (1 : ℝ) else 0) := by
    apply summable_of_ne_finset_zero (s := {0})
    intro z hz
    have : z ≠ 0 := by simpa using hz
    simp [this]
  refine Summable.of_nonneg_of_le (fun z => by positivity) (fun z => ?_) (h0.add h1)
  have hr : 0 ≤ ‖z‖ ^ (-(N : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
  by_cases hz : z = 0
  · subst hz
    simp
  · simp only [hz, if_false, add_zero]
    have hpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
    rw [Real.rpow_neg hpos.le, Real.rpow_natCast]
    have : ‖z‖ = ‖(z : κ → mixedSpace F)‖ := rfl
    rw [← this]
    gcongr
    linarith

end GlobalTheory.LatScaleSum

namespace GlobalTheory.LatScaleSum

open mixedEmbedding

theorem thetaSum_norm_le_pow :
    ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∃ (N₀ k : ℕ) (C : ℝ), ∀ (A : ℝ) (m : ℕ) (Ψ : (κ → AF F) → ℂ), 1 ≤ m →
    (∀ ξ : κ → F, ‖Ψ (fun i => algebraMap F (AF F) (ξ i))‖ * (1 + ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖) ^ N₀ ≤ A) →
    (∀ ξ : κ → F, Ψ (fun i => algebraMap F (AF F) (ξ i)) ≠ 0 → ∀ i, IsIntegral ℤ ((m : F) * ξ i)) →
    ‖thetaSum F Ψ‖ ≤ C * A * (m : ℝ) ^ k := by
  intro F _ _ κ _
  set L := latPi F κ with hL
  set N₀ : ℕ := Module.finrank ℤ L + 1 with hN
  set H : (κ → mixedSpace F) → ℝ := fun v => ((1 + ‖v‖) ^ N₀)⁻¹ with hH
  have hHs : Summable fun z : L => H z := summable_inv_one_add_pow F κ
  refine ⟨N₀, N₀, ∑' z : L, H z, ?_⟩
  intro A m Ψ hm hb hint
  set f : (κ → F) → ℂ := fun ξ => Ψ (fun i => algebraMap F (AF F) (ξ i)) with hf
  set ψ : (κ → F) → (κ → mixedSpace F) := fun ξ i => mixedEmbedding F (ξ i) with hψdef
  have hψ : ∀ ξ : κ → F, (fun i => evI F (algebraMap F (AF F) (ξ i))) = ψ ξ :=
    fun ξ => funext fun i => evI_algebraMap F (ξ i)
  set g : (κ → F) → (κ → mixedSpace F) := fun ξ => ψ (fun i => (m : F) * ξ i) with hgdef
  have hm0 : (m : F) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hm)
  have hginj : Function.Injective g := by
    intro ξ η h
    funext i
    have := congrFun h i
    simp only [hgdef, hψdef] at this
    exact mul_left_cancel₀ hm0 (mixedEmbedding_injective F this)
  have hgsmul : ∀ ξ, g ξ = m • ψ ξ := by
    intro ξ
    funext i
    simp only [hgdef, hψdef, Pi.smul_apply]
    rw [← nsmul_eq_mul, map_nsmul]
  set Lind : (κ → mixedSpace F) → ℝ := (L : Set (κ → mixedSpace F)).indicator H with hLind
  have hLs : Summable Lind := summable_subtype_iff_indicator.mp hHs
  have hLnn : ∀ v, 0 ≤ Lind v := fun v => Set.indicator_nonneg (fun v _ => by positivity) v
  have hA : 0 ≤ A := le_trans (by positivity) (hb 0)
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have key : ∀ ξ, ‖f ξ‖ ≤ A * (m : ℝ) ^ N₀ * Lind (g ξ) := by
    intro ξ
    by_cases h : f ξ = 0
    · rw [h, norm_zero]
      have := hLnn (g ξ)
      positivity
    · have hi := hint ξ h
      have hmem : g ξ ∈ L := mem_latPi F κ _ hi
      rw [hLind, Set.indicator_of_mem hmem]
      have hb' := hb ξ
      rw [hψ ξ] at hb'
      have hpos : 0 < (1 + ‖ψ ξ‖) ^ N₀ := by positivity
      have e1 : ‖f ξ‖ ≤ A * ((1 + ‖ψ ξ‖) ^ N₀)⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ hpos]; exact hb'
      have hgn : ‖g ξ‖ ≤ m * ‖ψ ξ‖ := by rw [hgsmul]; exact norm_nsmul_le
      have hmpos : (0 : ℝ) < m := by linarith
      have e2 : ((1 + ‖ψ ξ‖) ^ N₀)⁻¹ ≤ (m : ℝ) ^ N₀ * H (g ξ) := by
        simp only [hH]
        calc ((1 + ‖ψ ξ‖) ^ N₀)⁻¹ = (m : ℝ) ^ N₀ * (((m : ℝ) * (1 + ‖ψ ξ‖)) ^ N₀)⁻¹ := by
              rw [mul_pow, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hmpos.ne'), one_mul]
          _ ≤ (m : ℝ) ^ N₀ * ((1 + ‖g ξ‖) ^ N₀)⁻¹ := by
              gcongr
              nlinarith [norm_nonneg (ψ ξ)]
      calc ‖f ξ‖ ≤ A * ((1 + ‖ψ ξ‖) ^ N₀)⁻¹ := e1
        _ ≤ A * ((m : ℝ) ^ N₀ * H (g ξ)) := mul_le_mul_of_nonneg_left e2 hA
        _ = _ := by ring
  have hu : Summable fun ξ => A * (m : ℝ) ^ N₀ * Lind (g ξ) :=
    (hLs.comp_injective hginj).mul_left _
  have hfs : Summable fun ξ => ‖f ξ‖ := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) key hu
  have hcomp : ∑' ξ, Lind (g ξ) ≤ ∑' v, Lind v := tsum_comp_le_tsum_of_inj hLs hLnn hginj
  have hsub : ∑' v, Lind v = ∑' z : L, H z := (tsum_subtype (L : Set (κ → mixedSpace F)) H).symm
  have hmk : 0 ≤ A * (m : ℝ) ^ N₀ := by positivity
  calc ‖thetaSum F Ψ‖ = ‖∑' ξ, f ξ‖ := rfl
    _ ≤ ∑' ξ, ‖f ξ‖ := norm_tsum_le_tsum_norm hfs
    _ ≤ ∑' ξ, A * (m : ℝ) ^ N₀ * Lind (g ξ) := hfs.tsum_le_tsum key hu
    _ = A * (m : ℝ) ^ N₀ * ∑' ξ, Lind (g ξ) := tsum_mul_left
    _ ≤ A * (m : ℝ) ^ N₀ * ∑' z : L, H z := by
        rw [← hsub]; exact mul_le_mul_of_nonneg_left hcomp hmk
    _ = (∑' z : L, H z) * A * (m : ℝ) ^ N₀ := by ring

end GlobalTheory.LatScaleSum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicThetaSumNormLePolynomialScaleStatement
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicThetaSum_norm_le_polynomial_scale : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∃ (N₀ k : ℕ) (C : ℝ), ∀ (A : ℝ) (m : ℕ) (Ψ : (κ → AF F) → ℂ), 1 ≤ m →
    (∀ ξ : κ → F, ‖Ψ (fun i => algebraMap F (AF F) (ξ i))‖ * (1 + ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖) ^ N₀ ≤ A) →
    (∀ ξ : κ → F, Ψ (fun i => algebraMap F (AF F) (ξ i)) ≠ 0 → ∀ i, IsIntegral ℤ ((m : F) * ξ i)) →
    ‖thetaSum F Ψ‖ ≤ C * A * (m : ℝ) ^ k := by
  first | exact @GlobalTheory.LatScaleSum.thetaSum_norm_le_pow | exact GlobalTheory.LatScaleSum.thetaSum_norm_le_pow | (intros; apply GlobalTheory.LatScaleSum.thetaSum_norm_le_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicHeightBlockDiagonalEmbeddingLeMul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicHeightBlockDiagonalEmbeddingLeMul
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.BlockHeight

open scoped NNReal
open GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation Formalism.UG

section Generic

variable {p q d : ℕ} (e : Fin p ⊕ Fin q ≃ Fin d)

theorem htOf_blk_le {R : Type} [CommRing R] {N₁ : Matrix (Fin p) (Fin p) R → ℝ≥0} {N₂ : Matrix (Fin q) (Fin q) R → ℝ≥0}
    {N : Matrix (Fin d) (Fin d) R → ℝ≥0} (hN : ∀ a b, N (blk e a b) ≤ max (N₁ a) (N₂ b))
    (X : GL (Fin d) R) (x : GL (Fin p) R) (y : GL (Fin q) R)
    (h1 : (X : Matrix (Fin d) (Fin d) R) = blk e (x : Matrix (Fin p) (Fin p) R) (y : Matrix (Fin q) (Fin q) R))
    (h2 : ((X⁻¹ : GL (Fin d) R) : Matrix (Fin d) (Fin d) R) =
      blk e ((x⁻¹ : GL (Fin p) R) : Matrix (Fin p) (Fin p) R) ((y⁻¹ : GL (Fin q) R) : Matrix (Fin q) (Fin q) R)) :
    htOf N X ≤ htOf N₁ x * htOf N₂ y := by
  have hx := one_le_htOf N₁ x
  have hy := one_le_htOf N₂ y
  refine max_le (one_le_mul_of_one_le_of_one_le hx hy) (max_le ?_ ?_)
  · rw [h1]
    refine (hN _ _).trans (max_le ?_ ?_)
    · exact (le_htOf N₁ x).trans (le_mul_of_one_le_right' hy)
    · exact (le_htOf N₂ y).trans (le_mul_of_one_le_left' hx)
  · rw [h2]
    refine (hN _ _).trans (max_le ?_ ?_)
    · exact (inv_le_htOf N₁ x).trans (le_mul_of_one_le_right' hy)
    · exact (inv_le_htOf N₂ y).trans (le_mul_of_one_le_left' hx)

theorem bc_val_blk {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') {X : GL (Fin d) R} {x : GL (Fin p) R}
    {y : GL (Fin q) R}
    (h1 : (X : Matrix (Fin d) (Fin d) R) = blk e (x : Matrix (Fin p) (Fin p) R) (y : Matrix (Fin q) (Fin q) R)) :
    ((bc φ X : GL (Fin d) R') : Matrix (Fin d) (Fin d) R') =
      blk e ((bc φ x : GL (Fin p) R') : Matrix (Fin p) (Fin p) R') ((bc φ y : GL (Fin q) R') : Matrix (Fin q) (Fin q) R') := by
  show (X : Matrix (Fin d) (Fin d) R).map φ = _
  rw [h1, blk_map _ _ _ (map_zero φ)]
  rfl

theorem bc_inv_blk {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') {X : GL (Fin d) R} {x : GL (Fin p) R}
    {y : GL (Fin q) R}
    (h2 : ((X⁻¹ : GL (Fin d) R) : Matrix (Fin d) (Fin d) R) =
      blk e ((x⁻¹ : GL (Fin p) R) : Matrix (Fin p) (Fin p) R) ((y⁻¹ : GL (Fin q) R) : Matrix (Fin q) (Fin q) R)) :
    (((bc φ X)⁻¹ : GL (Fin d) R') : Matrix (Fin d) (Fin d) R') =
      blk e (((bc φ x)⁻¹ : GL (Fin p) R') : Matrix (Fin p) (Fin p) R')
        (((bc φ y)⁻¹ : GL (Fin q) R') : Matrix (Fin q) (Fin q) R') := by
  simp only [← map_inv]
  exact bc_val_blk e φ h2

theorem opNorm_blk_le (a : Matrix (Fin p) (Fin p) ℂ) (b : Matrix (Fin q) (Fin q) ℂ) :
    opNorm (blk e a b) ≤ max (opNorm a) (opNorm b) := by
  refine ContinuousLinearMap.opNNNorm_le_bound _ _ fun x => ?_
  rw [← NNReal.coe_le_coe, NNReal.coe_mul, coe_nnnorm, coe_nnnorm]
  obtain ⟨v, rfl⟩ : ∃ v : Fin d → ℂ, x = WithLp.toLp 2 v := ⟨x.ofLp, rfl⟩
  set c : ℝ := ((max (opNorm a) (opNorm b) : ℝ≥0) : ℝ) with hcdef
  have hc : 0 ≤ c := NNReal.coe_nonneg _
  have ha : ‖(WithLp.toLp 2 (a *ᵥ fun i => v (e (.inl i))) : EuclideanSpace ℂ (Fin p))‖ ≤
      c * ‖(WithLp.toLp 2 (fun i => v (e (.inl i))) : EuclideanSpace ℂ (Fin p))‖ := by
    rw [← Matrix.toEuclideanCLM_toLp]
    refine (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    have : ((opNorm a : ℝ≥0) : ℝ) ≤ c := by rw [hcdef]; exact_mod_cast le_max_left _ _
    exact this
  have hb : ‖(WithLp.toLp 2 (b *ᵥ fun i => v (e (.inr i))) : EuclideanSpace ℂ (Fin q))‖ ≤
      c * ‖(WithLp.toLp 2 (fun i => v (e (.inr i))) : EuclideanSpace ℂ (Fin q))‖ := by
    rw [← Matrix.toEuclideanCLM_toLp]
    refine (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    have : ((opNorm b : ℝ≥0) : ℝ) ≤ c := by rw [hcdef]; exact_mod_cast le_max_right _ _
    exact this
  have key : ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) (blk e a b) (WithLp.toLp 2 v)‖ ^ 2 =
      ‖(WithLp.toLp 2 (a *ᵥ fun i => v (e (.inl i))) : EuclideanSpace ℂ (Fin p))‖ ^ 2 +
      ‖(WithLp.toLp 2 (b *ᵥ fun i => v (e (.inr i))) : EuclideanSpace ℂ (Fin q))‖ ^ 2 := by
    rw [Matrix.toEuclideanCLM_toLp, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
      ← e.sum_comp, Fintype.sum_sum_type]
    congr 1 <;> refine Finset.sum_congr rfl fun i _ => ?_ <;>
      simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk, mulVec, dotProduct, ← e.sum_comp, Fintype.sum_sum_type]
  have knorm : ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin d))‖ ^ 2 =
      ‖(WithLp.toLp 2 (fun i => v (e (.inl i))) : EuclideanSpace ℂ (Fin p))‖ ^ 2 +
      ‖(WithLp.toLp 2 (fun i => v (e (.inr i))) : EuclideanSpace ℂ (Fin q))‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, ← e.sum_comp,
      Fintype.sum_sum_type]
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg _)) two_ne_zero).1 ?_
  rw [key, mul_pow, knorm, mul_add, ← mul_pow, ← mul_pow]
  exact add_le_add (pow_le_pow_left₀ (norm_nonneg _) ha 2) (pow_le_pow_left₀ (norm_nonneg _) hb 2)

end Generic

variable (F : Type) [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]
variable {p q d : ℕ} (e : Fin p ⊕ Fin q ≃ Fin d)

theorem normFin_blk_le (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
    (a : Matrix (Fin p) (Fin p) (Fv F v ⊗[F] E)) (b : Matrix (Fin q) (Fin q) (Fv F v ⊗[F] E)) :
    normFin F v (blk e a b) ≤ max (normFin F v a) (normFin F v b) := by
  refine (normFin_le_iff F v).2 fun i j => ?_
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk, reindex_apply, submatrix_apply]
  rcases e.symm i with i | i <;> rcases e.symm j with j | j
  · rw [fromBlocks_apply₁₁]; exact (absFin_le_normFin F v a i j).trans (le_max_left _ _)
  · rw [fromBlocks_apply₁₂, Matrix.zero_apply, absFin_zero]; exact zero_le
  · rw [fromBlocks_apply₂₁, Matrix.zero_apply, absFin_zero]; exact zero_le
  · rw [fromBlocks_apply₂₂]; exact (absFin_le_normFin F v b i j).trans (le_max_right _ _)

theorem normInf_blk_le (w : InfinitePlace F) (a : Matrix (Fin p) (Fin p) (w.Completion ⊗[F] E))
    (b : Matrix (Fin q) (Fin q) (w.Completion ⊗[F] E)) :
    normInf F w (blk e a b) ≤ max (normInf F w a) (normInf F w b) :=
  (normInf_le_iff F w).2 fun τ => by
    rw [blk_map _ _ _ (map_zero (infEmb τ))]
    exact (opNorm_blk_le e _ _).trans
      (max_le_max ((normInf_le_iff F w).1 le_rfl τ) ((normInf_le_iff F w).1 le_rfl τ))

theorem heightGL_blk_le (X : GL (Fin d) (AF F ⊗[F] E)) (x : GL (Fin p) (AF F ⊗[F] E)) (y : GL (Fin q) (AF F ⊗[F] E))
    (h1 : (X : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)) =
      blk e (x : Matrix (Fin p) (Fin p) (AF F ⊗[F] E)) (y : Matrix (Fin q) (Fin q) (AF F ⊗[F] E)))
    (h2 : ((X⁻¹ : GL (Fin d) (AF F ⊗[F] E)) : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)) =
      blk e ((x⁻¹ : GL (Fin p) (AF F ⊗[F] E)) : Matrix (Fin p) (Fin p) (AF F ⊗[F] E))
        ((y⁻¹ : GL (Fin q) (AF F ⊗[F] E)) : Matrix (Fin q) (Fin q) (AF F ⊗[F] E))) :
    heightGL F X ≤ heightGL F x * heightGL F y := by
  unfold heightGL
  rw [mul_mul_mul_comm, ← Finset.prod_mul_distrib,
    ← finprod_mul_distrib (finite_mulSupport_htFin F x) (finite_mulSupport_htFin F y)]
  refine mul_le_mul' (Finset.prod_le_prod' fun w _ => ?_)
    (finprod_le_finprod' (finite_mulSupport_htFin F _) ?_ fun v => ?_)
  · exact htOf_blk_le e (normInf_blk_le F e w) _ _ _ (bc_val_blk e _ h1) (bc_inv_blk e _ h2)
  · exact ((finite_mulSupport_htFin F x).union (finite_mulSupport_htFin F y)).subset (Function.mulSupport_mul _ _)
  · exact htOf_blk_le e (normFin_blk_le F e v) _ _ _ (bc_val_blk e _ h1) (bc_inv_blk e _ h2)

theorem ht_blkU_le : ∀ {D : D7} (A B : HSp D) {d : ℕ} (e : Fin A.rank ⊕ Fin B.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (hJ : J = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram A B e) (g : GA D A) (g₁ : GA D B),
    (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ht (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU A B e hJ (g, g₁)) : ℝ) ≤ GlobalTheory.Grow.height A g * GlobalTheory.Grow.height B g₁ := by
  intro D A B d e J hJ g g₁
  have h := heightGL_blk_le D.host.F e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU A B e hJ (g, g₁)).1 (Formalism.L2.Theta.matHom A g)
    (Formalism.L2.Theta.matHom B g₁) rfl (by
      show blk e (Formalism.L2.Theta.mt A g⁻¹) (Formalism.L2.Theta.mt B g₁⁻¹) = _
      simp only [Formalism.L2.Theta.mt, map_inv])
  show ((heightGL D.host.F _ : ℝ≥0) : ℝ) ≤ ((heightGL D.host.F _ : ℝ≥0) : ℝ) * ((heightGL D.host.F _ : ℝ≥0) : ℝ)
  exact_mod_cast h

end GlobalTheory.BlockHeight

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicHeightBlockDiagonalEmbeddingLeMulStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryAdelicHeight_blockDiagonalEmbedding_le_mul : ∀ {D : D7} (A B : HSp D) {d : ℕ} (e : Fin A.rank ⊕ Fin B.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (hJ : J = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram A B e) (g : GA D A) (g₁ : GA D B),
    (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ht (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU A B e hJ (g, g₁)) : ℝ) ≤ GlobalTheory.Grow.height A g * GlobalTheory.Grow.height B g₁ := by
  first | exact @GlobalTheory.BlockHeight.ht_blkU_le | exact GlobalTheory.BlockHeight.ht_blkU_le | (intros; apply GlobalTheory.BlockHeight.ht_blkU_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormLeIncInf
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ThK.EvAt0

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def colEq {d d₁ : ℕ} (h : d = d₁ + 2) : Fin d ≃ Fin d₁ ⊕ Fin 2 := (finCongr h).trans finSumFinEquiv.symm

def idx {n d d₁ : ℕ} (h : d = d₁ + 2) : Fin n × Fin d ≃ (Fin n × Fin d₁) ⊕ (Fin n × Fin 2) :=
  (Equiv.prodCongr (Equiv.refl _) (colEq h)).trans (Equiv.prodSumDistrib _ _ _)


variable (σ : E →ₐ[F] E) {n d d₁ : ℕ} (h2 : Module.finrank F E = 2) (X : Spc F E n) (W : Spc F E d) {W₁ : Spc F E d₁}
  (h : d = d₁ + 2) (H' : Plane E d d₁) (M₁ : Model σ X W₁)

omit σ h2 X W H' M₁




end GlobalTheory.ThK.EvAt0
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneComplementForm
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.LeviPlaneSection

open Matrix

section Alg

variable {S : Type*} [CommRing S] {m : Type*} [Fintype m] [DecidableEq m] {k : ℕ}

end Alg

section Forms

variable {F E : Type} [Field F] [Field E] [Algebra F E]

end Forms


end GlobalTheory.LeviPlaneSection

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularCoverOfAlteration
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.RegCoverExists

set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry in
private theorem isSeparated_spMap {R R' : Type} [CommRing R] [CommRing R'] (c : R →+* R') :
    IsSeparated (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap c) := by
  have : IsAffine (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R) := by
    show IsAffine (Spec (CommRingCat.of R)); infer_instance
  have : IsAffine (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R') := by
    show IsAffine (Spec (CommRingCat.of R')); infer_instance
  infer_instance


set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry in
theorem _root_.GlobalTheory.RegCoverExists.isProjOver_of_comp_spMap {R R' : Type} [CommRing R] [CommRing R'] (c : R →+* R')
    {Y : Scheme.{0}} {f : Y ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R'} (h : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver (f ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap c)) : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver f := by
  obtain ⟨N, i, hi, hif⟩ := h
  have hP := _root_.GlobalTheory.ProjSpace.isPullback_baseChange N c
  haveI := isSeparated_spMap c
  haveI : IsSeparated (_root_.GlobalTheory.ProjSpace.baseChange N c) :=
    MorphismProperty.of_isPullback (P := @IsSeparated) hP.flip inferInstance
  refine ⟨N, hP.lift i f hif, ?_, hP.lift_snd _ _ _⟩
  haveI : IsClosedImmersion (hP.lift i f hif ≫ _root_.GlobalTheory.ProjSpace.baseChange N c) := by
    rw [hP.lift_fst]; exact hi
  exact IsClosedImmersion.of_comp _ (_root_.GlobalTheory.ProjSpace.baseChange N c)

end GlobalTheory.RegCoverExists

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntAddConjEqOneOfBaseGood
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory

theorem exists_int_add_conj_eq_one_of_base_good : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : Base F E), B.IsGood σ → ∃ θ : 𝓞 E, (θ : E) + σ θ = 1 := by
  intro F E _ _ _ _ _ σ B hB
  haveI : Algebra.Unramified (𝓞 F) (𝓞 E) := hB.unram
  exact exists_integer_add_conj_eq_one_of_formallyUnramified F E σ hB.cm inferInstance

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvFinMkPt
noncomputable section

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.VacLine

variable {F : Type} [Field F] [NumberField F]

theorem at_latAtV {E : Type} [Field E] [NumberField E] [Algebra F E] {n d : ℕ} {X : Spc F E n}
    {W : Spc F E d} {v : Pl (F := F)} {γ : Matrix (Fin n) (Fin d) (AE F E)} (hγ : γ ∈ latAtV X W v) :
    At (evFin F v) γ := by
  induction hγ using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, -, x, -, y, -, rfl⟩ := hz
    intro u hu
    rw [← smul_assoc, ha u hu, zero_smul]
  | zero => intro u _; exact smul_zero u
  | add z z' _ _ hz hz' => intro u hu; rw [smul_add, hz u hu, hz' u hu, add_zero]
  | neg z _ hz => intro u hu; rw [smul_neg, hz u hu, neg_zero]

end GlobalTheory.VacLine
end
end
