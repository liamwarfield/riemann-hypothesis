module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertiaLiftOfResidualTrivial
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertiaLiftOfResidualTrivial
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne Pointwise

namespace GlobalTheory.InertiaLift

theorem exists_mem_Ine_eq_on : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)), IsPlaceOver A w →
    ∀ (L : IntermediateField E Ω) (ψ : G E Ω), ψ ∈ Dec (F := E) A →
    (∀ x ∈ L, IsIntegral ℤ x → A.valuation (ψ x - x) < 1) →
    ∃ ι ∈ Ine (F := E) A, ∀ x ∈ L, ι x = ψ x := by
  intro E Ω _ _ _ _ _ A w _ L ψ hψ hL
  letI : TopologicalSpace (IntCl E Ω) := ⊥
  haveI : DiscreteTopology (IntCl E Ω) := ⟨rfl⟩
  haveI := continuousSMul_intCl E Ω
  let H := L.fixingSubgroup
  have hH : IsClosed (H : Set (Ω ≃ₐ[E] Ω)) := by
    have e : (H : Set (Ω ≃ₐ[E] Ω)) = ⋂ x : L, ((MulAction.stabilizer (Ω ≃ₐ[E] Ω) (x : Ω) :
        Subgroup (Ω ≃ₐ[E] Ω)) : Set (Ω ≃ₐ[E] Ω)) := by
      ext σ
      simp only [Set.mem_iInter, SetLike.mem_coe, MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]
      rw [IntermediateField.mem_fixingSubgroup_iff]
      exact ⟨fun h x => h x x.2, fun h x hx => h ⟨x, hx⟩⟩
    rw [e]
    exact isClosed_iInter fun x =>
      (MulAction.stabilizer (Ω ≃ₐ[E] Ω) (x : Ω)).isClosed_of_isOpen
        (stabilizer_isOpen_of_isIntegral (K := E) (x : Ω))
  haveI : CompactSpace H := isCompact_iff_compactSpace.mp hH.isCompact
  let Q := primeBelow (F := E) A
  let R' := FixedPoints.subalgebra (𝓞 E) (IntCl E Ω) H
  have hR' : ∀ b : R', ∀ k ∈ H, k • (b : IntCl E Ω) = b := fun b k hk => b.2 ⟨k, hk⟩
  have : SMulCommClass H R' (IntCl E Ω) := ⟨fun k r b => by
    change (k : Ω ≃ₐ[E] Ω) • ((r : IntCl E Ω) * b) = (r : IntCl E Ω) * (k : Ω ≃ₐ[E] Ω) • b
    rw [smul_mul', hR' r k k.2]⟩
  have : Algebra.IsInvariant R' (IntCl E Ω) H := ⟨fun b hb => ⟨⟨b, hb⟩, rfl⟩⟩
  have : Q.LiesOver (Q.under R') := ⟨rfl⟩
  have hψQ : ψ • Q = Q := by
    have h1 : ψ • A = A := hψ
    rw [← primeBelow_smul, h1]
  have hfix : ∀ r : R', ψ • (r : IntCl E Ω) - r ∈ Q := by
    intro r
    have hrL : ((r : IntCl E Ω) : Ω) ∈ L := by
      rw [← InfiniteGalois.fixedField_fixingSubgroup L, IntermediateField.mem_fixedField_iff]
      intro f hf
      exact congrArg Subtype.val (hR' r f hf)
    exact hL _ hrL (isIntegral_int_of_isIntegral (r : IntCl E Ω).2)
  let φ : (IntCl E Ω ⧸ Q) ≃ₐ[R' ⧸ Q.under R'] (IntCl E Ω ⧸ Q) := AlgEquiv.ofRingEquiv
    (f := Ideal.quotientEquiv Q Q (MulSemiringAction.toRingEquiv (Ω ≃ₐ[E] Ω) (IntCl E Ω) ψ)
      hψQ.symm)
    (fun r => by
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
      change Ideal.Quotient.mk Q (ψ • (r : IntCl E Ω)) = Ideal.Quotient.mk Q (r : IntCl E Ω)
      rw [Ideal.Quotient.eq]
      exact hfix r)
  obtain ⟨⟨v, hvQ⟩, hv⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite (G := H)
    (Q.under R') Q φ
  refine ⟨ψ * (v : Ω ≃ₐ[E] Ω)⁻¹, GlobalTheory.InertiaMovesRoot.mem_Ine_of_cong fun b => ?_, fun x hx => ?_⟩
  · have h1 : Ideal.Quotient.mk Q ((v : Ω ≃ₐ[E] Ω) • ((v : Ω ≃ₐ[E] Ω)⁻¹ • b)) =
        Ideal.Quotient.mk Q (ψ • ((v : Ω ≃ₐ[E] Ω)⁻¹ • b)) :=
      DFunLike.congr_fun hv (Ideal.Quotient.mk Q ((v : Ω ≃ₐ[E] Ω)⁻¹ • b))
    rw [smul_inv_smul, eq_comm, Ideal.Quotient.eq] at h1
    rwa [mul_smul]
  · have hv' : ((v : Ω ≃ₐ[E] Ω)⁻¹) x = x :=
      (IntermediateField.mem_fixingSubgroup_iff L _).mp (H.inv_mem v.2) x hx
    rw [AlgEquiv.mul_apply, hv']

end GlobalTheory.InertiaLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertiaLiftOfResidualTrivialStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertia_lift_of_residual_trivial : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)), IsPlaceOver A w → ∀ (L : IntermediateField E Ω) (ψ : G E Ω), ψ ∈ Dec (F := E) A → (∀ x ∈ L, IsIntegral ℤ x → A.valuation (ψ x - x) < 1) → ∃ ι ∈ Ine (F := E) A, ∀ x ∈ L, ι x = ψ x := by
  first | exact @GlobalTheory.InertiaLift.exists_mem_Ine_eq_on | exact GlobalTheory.InertiaLift.exists_mem_Ine_eq_on | (intros; apply GlobalTheory.InertiaLift.exists_mem_Ine_eq_on <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecompositionElementFrobeniusPower
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecompositionElementFrobeniusPower
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

noncomputable section

namespace GlobalTheory.WeilDeligne

theorem frobAlg_pow_apply (K L : Type*) [Field K] [Fintype K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] (m : ℕ) (a : L) :
    (FiniteField.frobeniusAlgEquivOfAlgebraic K L ^ m) a = a ^ (Fintype.card K ^ m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', AlgEquiv.mul_apply, ih, FiniteField.frobeniusAlgEquivOfAlgebraic_apply,
      ← pow_mul, pow_succ]

end GlobalTheory.WeilDeligne


open GlobalTheory.WeilDeligne Pointwise in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem GlobalTheory.WeilDeligne.exists_pow_normV_resPow (E Ω : Type) [Field E] [NumberField E] [Field Ω]
    [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) :
    IsPlaceOver A w → ∀ (L : IntermediateField E Ω), FiniteDimensional E L → ∀ g : G E Ω,
      g ∈ Dec (F := E) A → ∃ k : ℕ, ∀ x ∈ L, IsIntegral ℤ x →
        A.valuation ((g x) ^ (normV w ^ k) - x) < 1 := by
  intro hA L hL g hg
  classical
  set Q := primeBelow (F := E) A with hQ
  haveI : w.asIdeal.IsMaximal := w.isMaximal
  haveI : Q.LiesOver w.asIdeal := ⟨(under_primeBelow hA).symm⟩
  haveI : Q.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := 𝓞 E) Q
    (by rw [show Ideal.under (𝓞 E) Q = w.asIdeal from under_primeBelow hA]
        exact w.isMaximal)
  letI : Field (IntCl E Ω ⧸ Q) := Ideal.Quotient.field Q
  letI : Field (𝓞 E ⧸ w.asIdeal) := Ideal.Quotient.field w.asIdeal
  haveI : Finite (𝓞 E ⧸ w.asIdeal) := w.asIdeal.finiteQuotientOfFreeOfNeBot w.ne_bot
  letI : Fintype (𝓞 E ⧸ w.asIdeal) := Fintype.ofFinite _
  haveI : Algebra.IsIntegral (𝓞 E ⧸ w.asIdeal) (IntCl E Ω ⧸ Q) :=
    Ideal.Quotient.algebra_isIntegral_of_liesOver Q w.asIdeal
  haveI : Algebra.IsAlgebraic (𝓞 E ⧸ w.asIdeal) (IntCl E Ω ⧸ Q) := Algebra.IsIntegral.isAlgebraic
  have hqc : Fintype.card (𝓞 E ⧸ w.asIdeal) = normV w := Fintype.card_eq_nat_card
  have hq1 : 1 < normV w := one_lt_normV w

  have hgQ : g • Q = Q := by rw [hQ, ← primeBelow_smul, (mem_Dec.mp hg)]
  let ψ := Ideal.Quotient.stabilizerHom Q w.asIdeal (Ω ≃ₐ[E] Ω) ⟨g, hgQ⟩
  have hψ : ∀ b : IntCl E Ω, ψ (Ideal.Quotient.mk Q b) = Ideal.Quotient.mk Q (g • b) :=
    fun b => Ideal.Quotient.stabilizerHom_apply _ _ _ _ b

  set n := Module.finrank E L with hn
  set M := n.factorial with hM

  have hres : ∀ b : IntCl E Ω, (b : Ω) ∈ L →
      (Ideal.Quotient.mk Q b) ^ (normV w ^ M) = Ideal.Quotient.mk Q b := by
    intro b hbL
    set y := Ideal.Quotient.mk Q b with hy
    have hbi : IsIntegral (𝓞 E) (b : Ω) := b.2
    set f := minpoly (𝓞 E) (b : Ω) with hf
    have hdeg : f.natDegree ≤ n := by
      have h1 := minpoly.isIntegrallyClosed_eq_field_fractions' E hbi
      have h2 : (minpoly E (b : Ω)).natDegree ≤ n := by
        have h3 := minpoly.algebraMap_eq (A := E) (algebraMap L Ω).injective (⟨b, hbL⟩ : L)
        rw [show (b : Ω) = algebraMap L Ω ⟨b, hbL⟩ from rfl, h3]
        exact minpoly.natDegree_le _
      rwa [h1, (minpoly.monic hbi).natDegree_map] at h2
    have hbf : Polynomial.aeval b f = 0 := by
      apply Subtype.ext
      rw [Polynomial.aeval_subalgebra_coe]
      exact minpoly.aeval _ _
    have hy0 : Polynomial.aeval y (f.map (algebraMap (𝓞 E) (𝓞 E ⧸ w.asIdeal))) = 0 := by
      rw [Polynomial.aeval_map_algebraMap, hy, ← Ideal.Quotient.mkₐ_eq_mk (𝓞 E),
        Polynomial.aeval_algHom_apply, hbf, map_zero]
    have hmon := (minpoly.monic hbi).map (algebraMap (𝓞 E) (𝓞 E ⧸ w.asIdeal))
    have hyInt : IsIntegral (𝓞 E ⧸ w.asIdeal) y := ⟨_, hmon, hy0⟩
    have hdvd := minpoly.dvd (𝓞 E ⧸ w.asIdeal) y hy0
    have hle : (minpoly (𝓞 E ⧸ w.asIdeal) y).natDegree ≤ n := by
      have := Polynomial.natDegree_le_of_dvd hdvd hmon.ne_zero
      rw [(minpoly.monic hbi).natDegree_map] at this
      exact this.trans hdeg
    have hpos := minpoly.natDegree_pos hyInt
    set K' := IntermediateField.adjoin (𝓞 E ⧸ w.asIdeal) ({y} : Set (IntCl E Ω ⧸ Q))
    haveI : FiniteDimensional (𝓞 E ⧸ w.asIdeal) K' := IntermediateField.adjoin.finiteDimensional hyInt
    haveI : Finite K' := Module.finite_of_finite (𝓞 E ⧸ w.asIdeal)
    letI : Fintype K' := Fintype.ofFinite _
    have hcard : Fintype.card K' = normV w ^ (minpoly (𝓞 E ⧸ w.asIdeal) y).natDegree := by
      rw [Module.card_eq_pow_finrank (K := 𝓞 E ⧸ w.asIdeal), hqc,
        IntermediateField.adjoin.finrank hyInt]
    obtain ⟨m, hm⟩ := Nat.dvd_factorial hpos hle
    have key := FiniteField.pow_card_pow m
      (⟨y, IntermediateField.mem_adjoin_simple_self _ y⟩ : K')
    rw [hcard, ← pow_mul, ← hm] at key
    exact congrArg Subtype.val key

  let frob := FiniteField.frobeniusAlgEquivOfAlgebraic (𝓞 E ⧸ w.asIdeal) (IntCl E Ω ⧸ Q)
  let τ := frob ^ M
  have hτ : ∀ y, τ y = y ^ (normV w ^ M) := fun y => by
    rw [frobAlg_pow_apply, hqc]
  let R := IntermediateField.fixedField (Subgroup.zpowers τ)
  have hmemR : ∀ y, y ∈ R ↔ y ^ (normV w ^ M) = y := by
    intro y
    rw [← hτ]
    constructor
    · intro h; exact (IntermediateField.mem_fixedField_iff _ _).mp h τ (Subgroup.mem_zpowers τ)
    · intro h
      rw [IntermediateField.mem_fixedField_iff]
      intro f hf
      have hs : τ ∈ MulAction.stabilizer
        ((IntCl E Ω ⧸ Q) ≃ₐ[𝓞 E ⧸ w.asIdeal] (IntCl E Ω ⧸ Q)) y := h
      exact (Subgroup.zpowers_le.mpr hs) hf
  have hqM : 1 < normV w ^ M := Nat.one_lt_pow (Nat.factorial_ne_zero n) hq1
  haveI : Finite R := by
    have hfin := (Polynomial.X ^ (normV w ^ M) - Polynomial.X :
      Polynomial (𝓞 E ⧸ w.asIdeal)).rootSet_finite (IntCl E Ω ⧸ Q)
    refine Set.Finite.to_subtype (hfin.subset fun y hy => ?_)
    rw [Polynomial.mem_rootSet]
    refine ⟨Polynomial.X_pow_sub_X_ne_zero hqM, ?_⟩
    simp only [map_sub, map_pow, Polynomial.aeval_X]
    rw [(hmemR y).mp hy, sub_self]

  obtain ⟨j, hj⟩ :=
    (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (𝓞 E ⧸ w.asIdeal) R).2 (ψ.restrictNormal R)
  have hj' : FiniteField.frobeniusAlgEquivOfAlgebraic (𝓞 E ⧸ w.asIdeal) R ^ (j : ℕ) =
      ψ.restrictNormal R := hj
  have hψR : ∀ y ∈ R, ψ y = y ^ (normV w ^ (j : ℕ)) := by
    intro y hy
    have h1 := AlgEquiv.restrictNormal_commutes ψ R ⟨y, hy⟩
    rw [← hj', frobAlg_pow_apply, hqc] at h1
    simpa [IntermediateField.algebraMap_apply] using h1.symm

  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.factorial_ne_zero n)
  refine ⟨m * (j : ℕ), fun x hxL hx => ?_⟩
  let b : IntCl E Ω := ⟨x, hx.tower_top⟩
  have hbR : Ideal.Quotient.mk Q b ∈ R := (hmemR _).mpr (hres b hxL)
  have hfix : ∀ t : ℕ, (Ideal.Quotient.mk Q b) ^ (normV w ^ (M * t)) = Ideal.Quotient.mk Q b := by
    intro t
    induction t with
    | zero => simp
    | succ t ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, hres b hxL]
  have h2 : (g • b) ^ (normV w ^ (m * (j : ℕ))) - b ∈ Q := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, ← hψ, hψR _ hbR, ← pow_mul, ← pow_add,
      show (j : ℕ) + m * j = M * j by rw [hM, hm, Nat.succ_mul, add_comm], hfix, sub_self]
  exact h2
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecompositionElementFrobeniusPowerStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.decomposition_element_frobenius_power : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)), IsPlaceOver A w → ∀ (L : IntermediateField E Ω), FiniteDimensional E L → ∀ g : G E Ω, g ∈ Dec (F := E) A → ∃ k : ℕ, ∀ x ∈ L, IsIntegral ℤ x → A.valuation ((g x) ^ (normV w ^ k) - x) < 1 := by
  first | exact @GlobalTheory.WeilDeligne.exists_pow_normV_resPow | exact GlobalTheory.WeilDeligne.exists_pow_normV_resPow | (intros; apply GlobalTheory.WeilDeligne.exists_pow_normV_resPow <;> assumption)
end
end

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ConjWD

section

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

end

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

end GlobalTheory.ConjWD

namespace GlobalTheory.ConjWD

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem exists_weil_eq_on {g : G E Ω} (hg : g ∈ Dec (F := E) A) (L : IntermediateField E Ω)
    [FiniteDimensional E L] : ∃ τ : Weil h, ∀ x ∈ L, (τ : G E Ω) x = g x := by
  obtain ⟨k, hk⟩ := GlobalTheory.T.decomposition_element_frobenius_power E Ω A w h L inferInstance g hg
  set φ : Weil h := frob h ^ k
  have hφ : ActsAs A (normV w) (φ : G E Ω) k 0 := actsAs_of_deg (by simp [φ])
  have hψ : ((φ : G E Ω) * g) ∈ Dec (F := E) A := (Dec (F := E) A).mul_mem hφ.1 hg
  obtain ⟨ι, hι, hιL⟩ := GlobalTheory.T.inertia_lift_of_residual_trivial E Ω A w h L _ hψ fun x hx hxi => by
    have hx1 : A.valuation x ≤ 1 := (A.valuation_le_one_iff x).mpr (mem_of_isIntegral_int A hxi)
    have hgx : A.valuation (g x) ≤ 1 := val_apply_le_one hg hx1
    have h1 := hφ.2 _ hgx
    simp only [pow_zero, pow_one] at h1
    exact cong_trans h1 (hk x hx hxi)
  refine ⟨φ⁻¹ * ineIncl h ⟨ι, hι⟩, fun x hx => ?_⟩
  show (φ : G E Ω)⁻¹ (ι x) = g x
  rw [hιL x hx, AlgEquiv.mul_apply]
  show ((φ : G E Ω)⁻¹ * (φ : G E Ω)) (g x) = g x
  simp

end GlobalTheory.ConjWD
