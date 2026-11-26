module

public import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NcardPrimesOverOfStabilizer
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspidalCharacterLabelUniqueGLn

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OpenKerCharWildEqOneOfPowEqOne
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OpenKerCharWildEqOneOfPowEqOne
open NumberField IsDedekindDomain

namespace GlobalTheory.WildOpenKernel

theorem eq_one_of_wild_prime {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] {M : Type} [CommGroup M] (φ : Formalism.ConjugateSelfDual.G E Ω →* M)
    (P : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (hA : Formalism.ConjugateSelfDual.IsPlaceOver A P)
    (hop : IsOpen (φ.ker : Set (Formalism.ConjugateSelfDual.G E Ω))) (l : ℕ) (hl : l.Prime)
    (hlv : ((l : ℕ) : 𝓞 E) ∉ P.asIdeal) (σ : Formalism.ConjugateSelfDual.G E Ω)
    (hσ : ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) (hσl : φ σ ^ l = 1) : φ σ = 1 := by
  have hvl : ¬ A.valuation (l : Ω) < 1 := by
    intro h
    apply hlv
    rw [← hA]
    simpa using h
  have hvl1 : A.valuation (l : Ω) = 1 :=
    le_antisymm ((A.valuation_le_one_iff _).mpr (natCast_mem A l)) (not_lt.mp hvl)
  obtain ⟨L, hL, hsub⟩ := (krullTopology_mem_nhds_one_iff E Ω _).mp
    (hop.mem_nhds (by simp))
  have : IsGalois E Ω := IsAlgClosure.isGalois E Ω
  have hidx : L.fixingSubgroup.index ≠ 0 := by
    rw [← IntermediateField.finrank_eq_fixingSubgroup_index]
    exact Module.finrank_pos.ne'
  obtain ⟨N, hN, -, hmem⟩ := Subgroup.exists_pow_mem_of_index_ne_zero hidx σ
  obtain ⟨a, n, hn, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN.ne' l hl.ne_one
  have hτ : σ ^ n ∈ L.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff] at hmem ⊢
    intro x hx
    refine GlobalTheory.WildInertiaChar.fixed_of_pow_fixed A (σ ^ n)
      (GlobalTheory.WildInertiaChar.wild_pow A σ hσ n) (l ^ a) ?_ x ?_
    · rw [Nat.cast_pow, map_pow, hvl1, one_pow]; exact lt_irrefl _
    · rw [← pow_mul, mul_comm]; exact hmem x hx
  have h1 : φ σ ^ n = 1 := by
    have h2 : σ ^ n ∈ φ.ker := hsub hτ
    rw [MonoidHom.mem_ker, map_pow] at h2
    exact h2
  have hc : Nat.Coprime l n := (Nat.Prime.coprime_iff_not_dvd hl).mpr hn
  have := (pow_gcd_eq_one (a := φ σ) (m := l) (n := n)).mpr ⟨hσl, h1⟩
  rwa [hc, pow_one] at this

theorem eq_one_of_wild : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {M : Type} [CommGroup M] (φ : Formalism.ConjugateSelfDual.G E Ω →* M) (P : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (m : ℕ),
    Formalism.ConjugateSelfDual.IsPlaceOver A P → IsOpen (φ.ker : Set (Formalism.ConjugateSelfDual.G E Ω)) → ((m : ℕ) : 𝓞 E) ∉ P.asIdeal →
    ∀ τ : Formalism.ConjugateSelfDual.G E Ω, (∀ y : Ω, y ≠ 0 → A.valuation (τ y / y - 1) < 1) → (∃ N : ℕ, φ τ ^ (m ^ N) = 1) → φ τ = 1 := by
  intro E Ω _ _ _ _ _ M _ φ P A m hA hop hm τ hτ ⟨N, hN⟩
  by_contra hne
  have hd : orderOf (φ τ) ∣ m ^ N := orderOf_dvd_of_pow_eq_one hN
  have hne1 : orderOf (φ τ) ≠ 1 := by rwa [Ne, orderOf_eq_one_iff]
  obtain ⟨l, hl, k, hk⟩ := Nat.exists_prime_and_dvd hne1
  have hlm : l ∣ m := hl.dvd_of_dvd_pow (dvd_trans ⟨k, hk⟩ hd)
  have hlv : ((l : ℕ) : 𝓞 E) ∉ P.asIdeal := by
    intro h
    apply hm
    obtain ⟨c, hc⟩ := hlm
    rw [hc]
    push_cast
    exact Ideal.mul_mem_right _ _ h
  have h1 : φ (τ ^ k) = 1 := by
    refine eq_one_of_wild_prime φ P A hA hop l hl hlv _
      (GlobalTheory.WildInertiaChar.wild_pow A τ hτ k) ?_
    rw [map_pow, ← pow_mul, mul_comm, ← hk, pow_orderOf_eq_one]
  rw [map_pow] at h1
  have h2 := orderOf_dvd_of_pow_eq_one h1
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (by simp)
  have ho : orderOf (φ τ) ≠ 0 := fun h =>
    pow_ne_zero N hm0 (Nat.eq_zero_of_zero_dvd (h ▸ hd))
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact ho (by simpa using hk)
  have h3 := Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) h2
  rw [hk] at h3
  have := hl.two_le
  have := Nat.pos_of_ne_zero hk0
  nlinarith

end GlobalTheory.WildOpenKernel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OpenKerCharWildEqOneOfPowEqOneStatement
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.openKerChar_wild_eq_one_of_pow_eq_one : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {M : Type} [CommGroup M] (φ : Formalism.ConjugateSelfDual.G E Ω →* M) (P : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (m : ℕ),
    Formalism.ConjugateSelfDual.IsPlaceOver A P → IsOpen (φ.ker : Set (Formalism.ConjugateSelfDual.G E Ω)) → ((m : ℕ) : 𝓞 E) ∉ P.asIdeal →
    ∀ τ : Formalism.ConjugateSelfDual.G E Ω, (∀ y : Ω, y ≠ 0 → A.valuation (τ y / y - 1) < 1) → (∃ N : ℕ, φ τ ^ (m ^ N) = 1) → φ τ = 1 := by
  first | exact @GlobalTheory.WildOpenKernel.eq_one_of_wild | exact GlobalTheory.WildOpenKernel.eq_one_of_wild | (intros; apply GlobalTheory.WildOpenKernel.eq_one_of_wild <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInertiaTameCharPrimitiveRootOfUniformizerR
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInertiaTameCharPrimitiveRootOfUniformizerR
open NumberField IsDedekindDomain

namespace GlobalTheory.TameRootSurj

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

theorem irreducible_X_pow_sub_C {E : Type} [Field E] [NumberField E]
    (P : HeightOneSpectrum (𝓞 E)) {L : ℕ} (hL : 0 < L) {ϖ : 𝓞 E}
    (hmem : ϖ ∈ P.asIdeal) (hnot : ϖ ∉ P.asIdeal ^ 2) :
    Irreducible (X ^ L - C (ϖ : E)) := by
  have hmon : (X ^ L - C ϖ : (𝓞 E)[X]).Monic := monic_X_pow_sub_C ϖ hL.ne'
  have hdeg : (X ^ L - C ϖ : (𝓞 E)[X]).natDegree = L := natDegree_X_pow_sub_C _
  have hEis : (X ^ L - C ϖ : (𝓞 E)[X]).IsEisensteinAt P.asIdeal := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hmon.leadingCoeff]; exact fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
    · intro m hm
      rw [hdeg] at hm
      rw [coeff_sub, coeff_X_pow, coeff_C, if_neg hm.ne]
      by_cases h0 : m = 0
      · subst h0; simpa using P.asIdeal.neg_mem_iff.2 hmem
      · simp [h0]
    · rw [coeff_sub, coeff_X_pow, coeff_C, if_neg hL.ne, if_pos rfl, zero_sub]
      rwa [Ideal.neg_mem_iff]
  have hirr : Irreducible (X ^ L - C ϖ : (𝓞 E)[X]) :=
    hEis.irreducible P.isPrime hmon.isPrimitive (by rw [hdeg]; exact hL)
  have hmap : (X ^ L - C ϖ : (𝓞 E)[X]).map (algebraMap (𝓞 E) E) = X ^ L - C (ϖ : E) := by
    simp [Polynomial.map_sub]
  rw [← hmap]; exact (hmon.irreducible_iff_irreducible_map_fraction_map (K := E)).1 hirr

theorem main : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (P : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (L : ℕ) (ϖ : 𝓞 E) (π : Ω),
    Formalism.ConjugateSelfDual.IsPlaceOver A P → ((L : ℕ) : 𝓞 E) ∉ P.asIdeal → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 →
    π ^ L = algebraMap E Ω (ϖ : E) → ∃ σ ∈ ReciprocityTheory.Gal.Ine (F := E) A, IsPrimitiveRoot (σ π / π) L := by
  intro E Ω _ _ _ _ _ P A L ϖ π hA hL h1 h2 hπ
  have hϖ0 : ϖ ≠ 0 := by rintro rfl; exact h2 (zero_mem _)
  have hL0 : L ≠ 0 := by rintro rfl; exact hL (by simp)
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [zero_pow hL0, eq_comm, map_eq_zero] at hπ
    exact hϖ0 (by simpa using hπ)
  rcases Nat.lt_or_ge L 2 with hL2 | hL2
  · have hL1 : L = 1 := by omega
    subst hL1
    refine ⟨1, one_mem _, ?_⟩
    rw [AlgEquiv.one_apply, div_self hπ0]
    exact IsPrimitiveRoot.one
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  haveI : NeZero ((L : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hL0⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω L
  have hirr := irreducible_X_pow_sub_C P (Nat.pos_of_ne_zero hL0) h1 h2
  have hmon : (X ^ L - C (ϖ : E)).Monic := monic_X_pow_sub_C _ hL0
  have hr1 : aeval π (X ^ L - C (ϖ : E)) = 0 := by simp [hπ]
  have hr2 : aeval (ζ * π) (X ^ L - C (ϖ : E)) = 0 := by simp [mul_pow, hζ.pow_eq_one, hπ]
  have hm1 := minpoly.eq_of_irreducible_of_monic hirr hr1 hmon
  have hm2 := minpoly.eq_of_irreducible_of_monic hirr hr2 hmon
  haveI : IsGalois E Ω := IsAlgClosure.isGalois E Ω
  obtain ⟨g, hg⟩ : ∃ g : Ω ≃ₐ[E] Ω, g π = ζ * π := by
    obtain ⟨g, hg⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := E) (E := Ω)).1 (hm2.symm.trans hm1)
    exact ⟨g, hg⟩
  obtain ⟨-, hx2⟩ := GlobalTheory.InertiaMovesRoot.cong_on_adjoin hA hL2 h1 h2 hπ
  letI : TopologicalSpace (IntCl E Ω) := ⊥
  haveI : DiscreteTopology (IntCl E Ω) := ⟨rfl⟩
  haveI := continuousSMul_intCl E Ω
  let H := MulAction.stabilizer (Ω ≃ₐ[E] Ω) π
  have hH : IsClosed (H : Set (Ω ≃ₐ[E] Ω)) :=
    H.isClosed_of_isOpen (stabilizer_isOpen_of_isIntegral (K := E) π)
  haveI : CompactSpace H := isCompact_iff_compactSpace.mp hH.isCompact
  obtain ⟨k, hk, k', hk', hc⟩ := GlobalTheory.InertiaMovesRoot.exists_cong_of_cong_on_fixed (R := 𝓞 E) H
    (primeBelow (F := E) A) g (fun b hb => by
      refine hx2 g b ?_ (valuation_le_one_intCl A b)
      rw [← InfiniteGalois.fixedField_fixingSubgroup (IntermediateField.adjoin E {π}),
        IntermediateField.mem_fixedField_iff]
      intro f hf
      exact congrArg Subtype.val (hb f (hf ⟨π, IntermediateField.mem_adjoin_simple_self E π⟩)))
  refine ⟨k' * g * k, GlobalTheory.InertiaMovesRoot.mem_Ine_of_cong hc, ?_⟩
  have e1 : k π = π := hk
  have e2 : k' π = π := hk'
  have e3 : (k' * g * k) π / π = k' ζ := by
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, e1, hg, map_mul, e2, mul_div_cancel_right₀ _ hπ0]
  rw [e3]
  exact hζ.map_of_injective k'.injective

end GlobalTheory.TameRootSurj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInertiaTameCharPrimitiveRootOfUniformizerRStatement
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_inertia_tameChar_primitiveRoot_of_uniformizerRoot : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (P : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (L : ℕ) (ϖ : 𝓞 E) (π : Ω),
    Formalism.ConjugateSelfDual.IsPlaceOver A P → ((L : ℕ) : 𝓞 E) ∉ P.asIdeal → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 →
    π ^ L = algebraMap E Ω (ϖ : E) → ∃ σ ∈ ReciprocityTheory.Gal.Ine (F := E) A, IsPrimitiveRoot (σ π / π) L := by
  first | exact @GlobalTheory.TameRootSurj.main | exact GlobalTheory.TameRootSurj.main | (intros; apply GlobalTheory.TameRootSurj.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsZetaPowCloseToUnitZpow
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsZetaPowCloseToUnitZpow
open NumberField IsDedekindDomain

namespace GlobalTheory.TamePowTeich

variable {Ω : Type} [Field Ω]

theorem valuation_pow_sub_lt (A : ValuationSubring Ω) {x y : Ω} (hx : A.valuation x = 1) (hy : A.valuation y = 1)
    (hxy : A.valuation (x - y) < 1) : ∀ k : ℕ, A.valuation (x ^ k - y ^ k) < 1 := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have h : x ^ (k + 1) - y ^ (k + 1) = x * (x ^ k - y ^ k) + (x - y) * y ^ k := by ring
    rw [h]
    apply Valuation.map_add_lt
    · rw [map_mul, hx, one_mul]; exact ih
    · rw [map_mul, map_pow, hy, one_pow, mul_one]; exact hxy

theorem valuation_zpow_sub_lt (A : ValuationSubring Ω) {x y : Ω} (hx : A.valuation x = 1) (hy : A.valuation y = 1)
    (hxy : A.valuation (x - y) < 1) (e : ℤ) : A.valuation (x ^ e - y ^ e) < 1 := by
  cases e with
  | ofNat k => simpa using valuation_pow_sub_lt A hx hy hxy k
  | negSucc k =>
    simp only [zpow_negSucc]
    have hxk : A.valuation (x ^ (k + 1)) = 1 := by rw [map_pow, hx, one_pow]
    have hyk : A.valuation (y ^ (k + 1)) = 1 := by rw [map_pow, hy, one_pow]
    have hx0 : x ^ (k + 1) ≠ 0 := by
      intro h0; rw [h0, map_zero] at hxk; exact zero_ne_one hxk
    have hy0 : y ^ (k + 1) ≠ 0 := by
      intro h0; rw [h0, map_zero] at hyk; exact zero_ne_one hyk
    rw [inv_sub_inv hx0 hy0, map_div₀, map_mul, hxk, hyk, mul_one, div_one, Valuation.map_sub_swap]
    exact valuation_pow_sub_lt A hx hy hxy (k + 1)

end GlobalTheory.TamePowTeich

open GlobalTheory.TamePowTeich in
theorem GlobalTheory.TamePowTeich.exists_zeta_pow_close : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    (P : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (ζ : Ω),
    Formalism.ConjugateSelfDual.IsPlaceOver A P → IsPrimitiveRoot ζ (Formalism.ConjugateSelfDual.normV P - 1) → ∀ (u : 𝓞 E) (e : ℤ), u ∉ P.asIdeal →
    ∃ a : ℕ, A.valuation (ζ ^ a - (algebraMap E Ω (u : E)) ^ e) < 1 := by
  intro E Ω _ _ _ _ P A ζ hA hζ u e hu
  classical
  set n := Formalism.ConjugateSelfDual.normV P - 1 with hn_def
  letI : Field (𝓞 E ⧸ P.asIdeal) := @Ideal.Quotient.field _ _ P.asIdeal P.isMaximal
  haveI : Finite (𝓞 E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot P.asIdeal P.ne_bot
  letI : Fintype (𝓞 E ⧸ P.asIdeal) := Fintype.ofFinite _
  have hcard : Formalism.ConjugateSelfDual.normV P = Fintype.card (𝓞 E ⧸ P.asIdeal) := by
    show Nat.card _ = _
    exact Nat.card_eq_fintype_card
  have hn : 0 < n := by
    have : 1 < Fintype.card (𝓞 E ⧸ P.asIdeal) := Fintype.one_lt_card
    omega

  have hmem : u ^ n - 1 ∈ P.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_one, sub_eq_zero, hn_def, hcard]
    apply FiniteField.pow_card_sub_one_eq_one
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  set U : Ω := algebraMap E Ω (u : E) with hU
  have hUn : A.valuation (U ^ n - 1) < 1 := by
    have := (hA (u ^ n - 1)).2 hmem
    simpa [hU] using this
  have hUint : U ∈ A := by
    apply ReciprocityTheory.Gal.mem_of_isIntegral_int
    exact (u.isIntegral_coe).algebraMap
  have hU1 : A.valuation U = 1 := by
    apply le_antisymm ((A.valuation_le_one_iff U).2 hUint)
    rw [← not_lt]
    intro h
    exact hu ((hA u).1 h)
  have hζ1 : A.valuation ζ = 1 :=
    ReciprocityTheory.Gal.valuation_eq_one_of_pow_eq_one A hn.ne' hζ.pow_eq_one

  have hprod : U ^ n - 1 = ∏ μ ∈ Polynomial.nthRootsFinset n (1 : Ω), (U - μ) := by
    have := congrArg (Polynomial.eval U) (Polynomial.X_pow_sub_one_eq_prod hn hζ)
    simpa [Polynomial.eval_prod] using this
  have hex : ∃ μ ∈ Polynomial.nthRootsFinset n (1 : Ω), A.valuation (U - μ) < 1 := by
    by_contra hcon
    push_neg at hcon
    have : 1 ≤ A.valuation (U ^ n - 1) := by
      rw [hprod, map_prod]
      exact Finset.one_le_prod' hcon
    exact absurd hUn (not_lt.2 this)
  obtain ⟨μ, hμ, hμU⟩ := hex
  haveI : NeZero n := ⟨hn.ne'⟩
  obtain ⟨b, -, hb⟩ := hζ.eq_pow_of_pow_eq_one ((Polynomial.mem_nthRootsFinset hn 1).1 hμ)
  have hb1 : A.valuation (ζ ^ b) = 1 := by rw [map_pow, hζ1, one_pow]
  have hclose : A.valuation (ζ ^ b - U) < 1 := by
    rw [Valuation.map_sub_swap, hb]; exact hμU
  have key := valuation_zpow_sub_lt A hb1 hU1 hclose e

  have hζ0 : ζ ≠ 0 := hζ.ne_zero hn.ne'
  refine ⟨((b * e) % (n : ℤ)).toNat, ?_⟩
  have hnz : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  have hnonneg : 0 ≤ (b * e) % (n : ℤ) := Int.emod_nonneg _ hnz
  have hpow : (ζ ^ b) ^ e = ζ ^ ((b * e) % (n : ℤ)).toNat := by
    have h1 : ζ ^ ((b * e) % (n : ℤ)).toNat = ζ ^ ((b * e) % (n : ℤ)) := by
      rw [← zpow_natCast, Int.toNat_of_nonneg hnonneg]
    rw [h1, ← zpow_natCast ζ b, ← zpow_mul]
    conv_lhs => rw [← Int.emod_add_mul_ediv ((b : ℤ) * e) n]
    rw [zpow_add₀ hζ0, zpow_mul, zpow_natCast, hζ.pow_eq_one, one_zpow, mul_one]
  rw [← hpow]
  exact key
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsZetaPowCloseToUnitZpowStatement
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_zeta_pow_close_to_unit_zpow : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    (P : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (ζ : Ω),
    Formalism.ConjugateSelfDual.IsPlaceOver A P → IsPrimitiveRoot ζ (Formalism.ConjugateSelfDual.normV P - 1) → ∀ (u : 𝓞 E) (e : ℤ), u ∉ P.asIdeal →
    ∃ a : ℕ, A.valuation (ζ ^ a - (algebraMap E Ω (u : E)) ^ e) < 1 := by
  first | exact @GlobalTheory.TamePowTeich.exists_zeta_pow_close | exact GlobalTheory.TamePowTeich.exists_zeta_pow_close | (intros; apply GlobalTheory.TamePowTeich.exists_zeta_pow_close <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSstResToOfIsPst
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial TensorProduct Module GlobalTheory.Pst

namespace GlobalTheory.PstSst

variable {l : ℕ} [Fact l.Prime]

theorem apply_mem_kur (g : GQ l) (c : ↥(MaximalUnramifiedExtension l)) : g (c : Om l) ∈ MaximalUnramifiedExtension l := by
  have h : (MaximalUnramifiedExtension l).map (g : Om l →ₐ[ℚ_[l]] Om l) ≤ MaximalUnramifiedExtension l := by
    conv_lhs => rw [MaximalUnramifiedExtension, IntermediateField.adjoin_map]
    refine IntermediateField.adjoin.mono _ _ _ ?_
    rintro _ ⟨x, ⟨m, h0, hm, hx⟩, rfl⟩
    exact ⟨m, h0, hm, by rw [← map_pow, hx, map_one]⟩
  exact h ⟨c, c.2, rfl⟩

theorem mem_of_fixed (K : FinExt l) (x : Om l) (hx : ∀ g ∈ GK K, g x = x) : x ∈ K.1 := by
  have : IsGalois ℚ_[l] (Om l) := {}
  rw [← InfiniteGalois.fixedField_fixingSubgroup K.1, IntermediateField.mem_fixedField_iff]
  exact hx

def incl (K : FinExt l) : ↥(K0 K) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l) :=
  IntermediateField.inclusion (inf_le_right : K.1 ⊓ MaximalUnramifiedExtension l ≤ MaximalUnramifiedExtension l)

section

variable (P : LocPrime l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL]
  (V : Type) [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]

theorem mulV_smul (q : ℚ_[l]) (c : ↥(MaximalUnramifiedExtension l)) (x : V ⊗[ℚ_[l]] Bst P) :
    mulV P LL V (q • c) x = q • mulV P LL V c x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b =>
    rw [mulV_tmul, mulV_tmul, ← tmul_smul, ← smul_mul_assoc]
    congr 2
    rw [Polynomial.algebraMap_apply, Polynomial.algebraMap_apply, smul_C]
    congr 1
    exact map_smul (IsScalarTower.toAlgHom ℚ_[l] ↥(MaximalUnramifiedExtension l) P.R.B) q c
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, smul_add]

def comb (K' : FinExt l) {n : ℕ} (b : Fin n → V ⊗[ℚ_[l]] Bst P) :
    (Fin n → ↥(K0 K')) →ₗ[ℚ_[l]] V ⊗[ℚ_[l]] Bst P where
  toFun c := ∑ i, mulV P LL V (incl K' (c i)) (b i)
  map_add' c d := by simp [Finset.sum_add_distrib]
  map_smul' q c := by
    rw [RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mulV_smul]
    exact congrArg (fun a => mulV P LL V a (b i)) (map_smul (incl K').toLinearMap q (c i))

variable {LL V} {K : FinExt l} (ρ : Representation LL ↥(GK K) V)

theorem coe_sum {n : ℕ} (b : Fin n → DpstUr P ρ) (c : Fin n → ↥(MaximalUnramifiedExtension l)) :
    (((toUr P ρ).symm (∑ i, c i • b i) : ↥(Dpst P ρ)) : V ⊗[ℚ_[l]] Bst P) =
      ∑ i, mulV P LL V (c i) (((toUr P ρ).symm (b i) : ↥(Dpst P ρ)) : V ⊗[ℚ_[l]] Bst P) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Submodule.coe_sum]
  rfl

theorem finrank_dst {n : ℕ} (b : Basis (Fin n) ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)) (K' : FinExt l) (h : K.1 ≤ K'.1)
    (hb : ∀ i (g : ↥(GK K)), (g : GQ l) ∈ GK K' →
      stRep P ρ g ((toUr P ρ).symm (b i) : ↥(Dpst P ρ)) = ((toUr P ρ).symm (b i) : ↥(Dpst P ρ))) :
    finrank ℚ_[l] ↥(Dst P (resTo ρ h)) = n * finrank ℚ_[l] ↥(K0 K') := by
  have := K'.2
  have hle : K0 K' ≤ K'.1 := inf_le_left
  have : FiniteDimensional ℚ_[l] ↥(K0 K') :=
    FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap
      (IntermediateField.inclusion_injective hle)
  set β : Fin n → V ⊗[ℚ_[l]] Bst P := fun i => ((toUr P ρ).symm (b i) : ↥(Dpst P ρ)) with hβ
  have huniq : ∀ c d : Fin n → ↥(MaximalUnramifiedExtension l),
      ∑ i, mulV P LL V (c i) (β i) = ∑ i, mulV P LL V (d i) (β i) → c = d := by
    intro c d hcd
    rw [← coe_sum, ← coe_sum] at hcd
    have h1 := (toUr P ρ).symm.injective (Subtype.ext hcd)
    rw [← b.equivFun_symm_apply, ← b.equivFun_symm_apply] at h1
    exact b.equivFun.symm.injective h1
  have hact : ∀ (g : ↥(GK K)), (g : GQ l) ∈ GK K' → ∀ c : Fin n → ↥(MaximalUnramifiedExtension l),
      stRep P ρ g (∑ i, mulV P LL V (c i) (β i)) =
        ∑ i, mulV P LL V ⟨_, apply_mem_kur (g : GQ l) (c i)⟩ (β i) := by
    intro g hg c
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← End.mul_apply, stRep_mulV P ρ g (c i) ⟨_, apply_mem_kur (g : GQ l) (c i)⟩ rfl, End.mul_apply,
      hb i g hg]
  have hinj : Function.Injective (comb P LL V K' β) := fun c d hcd =>
    funext fun i => (incl K').injective (congrFun (huniq _ _ hcd) i)
  have hrange : LinearMap.range (comb P LL V K' β) = (Dst P (resTo ρ h)).restrictScalars ℚ_[l] := by
    ext x
    rw [Submodule.restrictScalars_mem]
    constructor
    · rintro ⟨c, rfl⟩
      refine (mem_Dst_resTo P ρ h).mpr fun g hg => ?_
      refine (hact g hg fun i => incl K' (c i)).trans (Finset.sum_congr rfl fun i _ => ?_)
      congr 2
      exact Subtype.ext (mem_GK.mp hg _ (c i).2.1)
    · intro hx
      let c : Fin n → ↥(MaximalUnramifiedExtension l) := b.repr (toUr P ρ ⟨x, Dst_resTo_le P ρ h hx⟩)
      have hc : ∑ i, mulV P LL V (c i) (β i) = x := by
        rw [← coe_sum, b.sum_repr, AddEquiv.symm_apply_apply]
      have hK : ∀ i, (c i : Om l) ∈ K'.1 := fun i => mem_of_fixed K' _ fun g hg => by
        have h1 := hact ⟨g, GK_le h hg⟩ hg c
        rw [hc, (mem_Dst_resTo P ρ h).mp hx ⟨g, GK_le h hg⟩ hg, ← hc] at h1
        exact (congrArg Subtype.val (congrFun (huniq _ _ h1) i)).symm
      exact ⟨fun i => ⟨c i, hK i, (c i).2⟩, hc⟩
  have h1 := LinearMap.finrank_range_of_inj hinj
  rw [hrange, finrank_pi_fintype] at h1
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h1
  exact h1

end

theorem isSst_resTo_of_isPst (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (V : Type)
    [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V]
    [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (hV : IsPst P ρ) :
    ∃ (K₁ : FinExt l), K.1 ≤ K₁.1 ∧
      ∀ (K' : FinExt l) (h : K.1 ≤ K'.1), K₁.1 ≤ K'.1 → IsSst P (resTo ρ h) := by
  have := LL.2
  have : FiniteDimensional ℚ_[l] V := Module.Finite.trans ↥LL.1 V
  obtain ⟨_, hdim⟩ := (isPst_iff P ρ).mp hV
  let b := finBasis ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)
  choose F hF using fun i => (mem_Dpst P ρ).mp ((toUr P ρ).symm (b i)).2
  have := fun i => (F i).2
  refine ⟨supExt K ⟨⨆ i, (F i).1, inferInstance⟩, le_sup_left, fun K' h h₁ => ?_⟩
  have h1 := finrank_dst P ρ b K' h fun i g hg =>
    hF i g (GK_le (K := F i) (((le_iSup (fun i => (F i).1) i).trans le_sup_right).trans h₁) hg)
  rw [hdim, ← finrank_mul_finrank ℚ_[l] ↥LL.1 V, ← finrank_mul_finrank ℚ_[l] ↥LL.1, mul_assoc] at h1
  rw [IsSst, mul_comm]
  exact Nat.eq_of_mul_eq_mul_left finrank_pos h1

end GlobalTheory.PstSst
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjInertiaTameCharOtherPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjInertiaTameCharOtherPlace
open NumberField IsDedekindDomain

open Pointwise

namespace GlobalTheory.TameMove

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

theorem val_smul_lt_one_iff (A : ValuationSubring Ω) (g : Formalism.ConjugateSelfDual.G E Ω) (y : Ω) :
    (g • A).valuation (g y) < 1 ↔ A.valuation y < 1 := by
  have h1 : ∀ z : Ω, g z ∈ g • A ↔ z ∈ A := by
    intro z
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def,
      ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  rw [ReciprocityTheory.Gal.valuation_lt_one_iff', ReciprocityTheory.Gal.valuation_lt_one_iff', h1, ← map_inv₀, h1,
    map_eq_zero_iff _ g.injective]

theorem val_smul_le_one_iff (A : ValuationSubring Ω) (g : Formalism.ConjugateSelfDual.G E Ω) (y : Ω) :
    (g • A).valuation (g y) ≤ 1 ↔ A.valuation y ≤ 1 := by
  rw [ValuationSubring.valuation_le_one_iff, ValuationSubring.valuation_le_one_iff,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def,
    ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]

theorem conj_mem_Ine_smul {A : ValuationSubring Ω} {g σ : Formalism.ConjugateSelfDual.G E Ω}
    (hσ : σ ∈ ReciprocityTheory.Gal.Ine (F := E) A) : g * σ * g⁻¹ ∈ ReciprocityTheory.Gal.Ine (F := E) (g • A) := by
  refine ⟨?_, fun x hx => ?_⟩
  · show (g * σ * g⁻¹) • (g • A) = g • A
    have h : σ • A = A := hσ.1
    rw [← mul_smul, inv_mul_cancel_right, mul_smul, h]
  · have hy : A.valuation (g⁻¹ x) ≤ 1 := by
      rw [← val_smul_le_one_iff A g, ReciprocityTheory.Gal.mul_inv_apply]; exact hx
    have e : (g * σ * g⁻¹) x - x = g (σ (g⁻¹ x) - g⁻¹ x) := by
      rw [map_sub, ReciprocityTheory.Gal.mul_inv_apply]; rfl
    rw [e, val_smul_lt_one_iff]
    exact hσ.2 _ hy

theorem exists_mul_eq_of_not_mem_sq (P : HeightOneSpectrum (𝓞 E)) {ϖ ϖ₀ : 𝓞 E}
    (h₀ : ϖ₀ ∈ P.asIdeal) (h : ϖ ∈ P.asIdeal) (h2 : ϖ ∉ P.asIdeal ^ 2) :
    ∃ s t : 𝓞 E, s ∉ P.asIdeal ∧ s * ϖ₀ = t * ϖ := by
  have hle : Ideal.span {ϖ} ≤ P.asIdeal := (Ideal.span_singleton_le_iff_mem _).mpr h
  obtain ⟨I, hI⟩ := Ideal.dvd_iff_le.mpr hle
  have hIP : ¬ I ≤ P.asIdeal := by
    intro hIP
    apply h2
    have : Ideal.span {ϖ} ≤ P.asIdeal ^ 2 := by
      rw [hI, pow_two]; exact Ideal.mul_mono_right hIP
    exact this (Ideal.mem_span_singleton_self ϖ)
  obtain ⟨s, hsI, hsP⟩ := Set.not_subset.mp hIP
  have hm : s * ϖ₀ ∈ Ideal.span {ϖ} := by
    rw [hI, mul_comm s]; exact Ideal.mul_mem_mul h₀ hsI
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hm
  exact ⟨s, t, hsP, ht.symm⟩

theorem val_le_one (A : ValuationSubring Ω) (t : 𝓞 E) : A.valuation (algebraMap E Ω (t : E)) ≤ 1 := by
  rw [A.valuation_le_one_iff]
  apply ReciprocityTheory.Gal.mem_of_isIntegral_int
  exact (NumberField.RingOfIntegers.isIntegral_coe t).map (algebraMap E Ω).toIntAlgHom

theorem val_eq_of_not_mem_sq (A : ValuationSubring Ω) (P : HeightOneSpectrum (𝓞 E))
    (hA : Formalism.ConjugateSelfDual.IsPlaceOver A P) {ϖ ϖ₀ : 𝓞 E} (h : ϖ ∈ P.asIdeal) (h2 : ϖ ∉ P.asIdeal ^ 2)
    (h₀ : ϖ₀ ∈ P.asIdeal) (h02 : ϖ₀ ∉ P.asIdeal ^ 2) :
    A.valuation (algebraMap E Ω (ϖ : E)) = A.valuation (algebraMap E Ω (ϖ₀ : E)) := by
  have key : ∀ a b : 𝓞 E, a ∈ P.asIdeal → b ∈ P.asIdeal → b ∉ P.asIdeal ^ 2 →
      A.valuation (algebraMap E Ω (a : E)) ≤ A.valuation (algebraMap E Ω (b : E)) := by
    intro a b ha hb hb2
    obtain ⟨s, t, hs, hst⟩ := exists_mul_eq_of_not_mem_sq P ha hb hb2
    have hvs : A.valuation (algebraMap E Ω (s : E)) = 1 :=
      le_antisymm (val_le_one A s) (not_lt.mp fun hlt => hs ((hA s).mp hlt))
    have e : algebraMap E Ω (s : E) * algebraMap E Ω (a : E) =
        algebraMap E Ω (t : E) * algebraMap E Ω (b : E) := by
      have := congrArg (fun z : 𝓞 E => algebraMap E Ω (z : E)) hst
      simpa using this
    have e2 := congrArg A.valuation e
    rw [Valuation.map_mul, Valuation.map_mul, hvs, one_mul] at e2
    rw [e2]
    calc A.valuation (algebraMap E Ω (t : E)) * A.valuation (algebraMap E Ω (b : E))
        ≤ 1 * A.valuation (algebraMap E Ω (b : E)) := mul_le_mul_left (val_le_one A t) _
      _ = _ := one_mul _
  exact le_antisymm (key _ _ h h₀ h02) (key _ _ h₀ h h2)

end GlobalTheory.TameMove

open Pointwise

namespace GlobalTheory.TameMove

theorem tameRep_move : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (P : HeightOneSpectrum (𝓞 E)) (e : ℤ) (σ : Formalism.ConjugateSelfDual.G E Ω) (u : 𝓞 E) (A₀ : ValuationSubring Ω) (ϖ₀ : 𝓞 E) (π₀ : Ω),
    Formalism.ConjugateSelfDual.IsPlaceOver A₀ P → ϖ₀ ∈ P.asIdeal → ϖ₀ ∉ P.asIdeal ^ 2 →
    π₀ ^ (Formalism.ConjugateSelfDual.normV P - 1) = algebraMap E Ω (ϖ₀ : E) → Formalism.L2.NX.TameRep P e σ u →
    ∃ g : Formalism.ConjugateSelfDual.G E Ω, g * σ * g⁻¹ ∈ ReciprocityTheory.Gal.Ine (F := E) A₀ ∧
      A₀.valuation ((g * σ * g⁻¹) π₀ / π₀ - (algebraMap E Ω (u : E)) ^ e) < 1 := by
  intro E Ω _ _ _ _ _ P e σ u A₀ ϖ₀ π₀ hA₀ h₀ h02 hπ₀ hT
  obtain ⟨A, hA, hσ, ϖ, π, h, h2, hπ, hv⟩ := hT
  obtain ⟨g, rfl⟩ := ReciprocityTheory.Gal.exists_smul_eq_of_isPlaceOver hA hA₀
  have hσ'I : g * σ * g⁻¹ ∈ ReciprocityTheory.Gal.Ine (F := E) (g • A) := conj_mem_Ine_smul hσ
  refine ⟨g, hσ'I, ?_⟩
  set B := g • A with hB
  set σ' := g * σ * g⁻¹ with hσ'
  set N := Formalism.ConjugateSelfDual.normV P - 1 with hN
  set U := (algebraMap E Ω (u : E)) ^ e with hU
  have hne : ∀ b : 𝓞 E, b ∉ P.asIdeal ^ 2 → algebraMap E Ω (b : E) ≠ 0 := by
    intro b hb hz
    apply hb
    have hb0 : b = 0 := by
      have : (b : E) = 0 := (map_eq_zero_iff _ (algebraMap E Ω).injective).mp hz
      exact_mod_cast this
    rw [hb0]; exact Ideal.zero_mem _
  have hw : algebraMap E Ω (ϖ : E) ≠ 0 := hne ϖ h2
  have hw₀ : algebraMap E Ω (ϖ₀ : E) ≠ 0 := hne ϖ₀ h02
  have hN0 : N ≠ 0 := by
    intro hz
    rw [hz, pow_zero] at hπ₀
    have := (hA₀ ϖ₀).mpr h₀
    rw [← hπ₀, map_one] at this
    exact lt_irrefl _ this
  have hπ₀0 : π₀ ≠ 0 := by
    rintro rfl; rw [zero_pow hN0] at hπ₀; exact hw₀ hπ₀.symm

  have hπ' : (g π) ^ N = algebraMap E Ω (ϖ : E) := by
    rw [← map_pow, hπ]; exact AlgEquiv.commutes g _
  have hπ'0 : g π ≠ 0 := by
    intro hz; rw [hz, zero_pow hN0] at hπ'; exact hw hπ'.symm
  have hgg : g⁻¹ (g π) = π := by
    rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  have ha : B.valuation (σ' (g π) / g π - U) < 1 := by
    have e1 : σ' (g π) / g π - U = g (σ π / π - U) := by
      have e2 : σ' (g π) = g (σ π) := by
        show g (σ (g⁻¹ (g π))) = g (σ π)
        rw [hgg]
      have e3 : g U = U := by
        rw [hU, map_zpow₀]; congr 1; exact AlgEquiv.commutes g _
      rw [map_sub, map_div₀, e2, e3]
    rw [e1, hB, val_smul_lt_one_iff]; exact hv

  set x := g π / π₀ with hx
  have hxπ : g π = x * π₀ := by rw [hx, div_mul_cancel₀ _ hπ₀0]
  have hx0 : x ≠ 0 := div_ne_zero hπ'0 hπ₀0
  have hvx : B.valuation x = 1 := by
    have hxN : x ^ N = algebraMap E Ω (ϖ : E) / algebraMap E Ω (ϖ₀ : E) := by
      rw [hx, div_pow, hπ', hπ₀]
    have hvN : B.valuation x ^ N = 1 := by
      rw [← Valuation.map_pow, hxN, map_div₀, val_eq_of_not_mem_sq B P hA₀ h h2 h₀ h02,
        div_self ((Valuation.ne_zero_iff _).mpr hw₀)]
    rcases lt_trichotomy (B.valuation x) 1 with h1 | h1 | h1
    · exact absurd hvN (pow_lt_one₀ zero_le h1 hN0).ne
    · exact h1
    · exact absurd hvN (one_lt_pow₀ h1 hN0).ne'
  have hc : B.valuation (σ' x / x - 1) < 1 := by
    have e : σ' x / x - 1 = (σ' x - x) / x := by field_simp
    rw [e, map_div₀, hvx, div_one]
    exact hσ'I.2 x hvx.le

  have hb : (σ' π₀ / π₀) ^ N = 1 := by
    rw [div_pow, ← map_pow, hπ₀, AlgEquiv.commutes, div_self hw₀]
  have hvb : B.valuation (σ' π₀ / π₀) = 1 := ReciprocityTheory.Gal.valuation_eq_one_of_pow_eq_one B hN0 hb
  have hprod : σ' (g π) / g π = (σ' x / x) * (σ' π₀ / π₀) := by
    rw [hxπ, map_mul]; field_simp
  have e4 : σ' π₀ / π₀ - U = (σ' (g π) / g π - U) + -((σ' x / x - 1) * (σ' π₀ / π₀)) := by
    rw [hprod]; ring
  rw [e4]
  refine Valuation.map_add_lt _ ha ?_
  rw [Valuation.map_neg, Valuation.map_mul, hvb, mul_one]
  exact hc

end GlobalTheory.TameMove
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjInertiaTameCharOtherPlaceStatement
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conj_inertia_tameChar_other_place : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (P : HeightOneSpectrum (𝓞 E)) (e : ℤ) (σ : Formalism.ConjugateSelfDual.G E Ω) (u : 𝓞 E) (A₀ : ValuationSubring Ω) (ϖ₀ : 𝓞 E) (π₀ : Ω),
    Formalism.ConjugateSelfDual.IsPlaceOver A₀ P → ϖ₀ ∈ P.asIdeal → ϖ₀ ∉ P.asIdeal ^ 2 →
    π₀ ^ (Formalism.ConjugateSelfDual.normV P - 1) = algebraMap E Ω (ϖ₀ : E) → Formalism.L2.NX.TameRep P e σ u →
    ∃ g : Formalism.ConjugateSelfDual.G E Ω, g * σ * g⁻¹ ∈ ReciprocityTheory.Gal.Ine (F := E) A₀ ∧
      A₀.valuation ((g * σ * g⁻¹) π₀ / π₀ - (algebraMap E Ω (u : E)) ^ e) < 1 := by
  first | exact @GlobalTheory.TameMove.tameRep_move | exact GlobalTheory.TameMove.tameRep_move | (intros; apply GlobalTheory.TameMove.tameRep_move <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CuspidalLabelPolynomialUniqueAllPrimes
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EsymmEqOfPsumEq
namespace GlobalTheory.EsymmOfPowerSums

open MvPolynomial

theorem esymm_eq_of_psum_eq {d : ℕ} (a b : Fin d → ℂ)
    (h : ∀ k : ℕ, 1 ≤ k → k ≤ d → ∑ i : Fin d, a i ^ k = ∑ i : Fin d, b i ^ k) :
    ∀ k ≤ d, (MvPolynomial.aeval a : MvPolynomial (Fin d) ℂ → ℂ) (MvPolynomial.esymm (Fin d) ℂ k)
      = (MvPolynomial.aeval b : MvPolynomial (Fin d) ℂ → ℂ) (MvPolynomial.esymm (Fin d) ℂ k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · simp
    have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hpos.ne'
    apply mul_left_cancel₀ hk0
    have key := MvPolynomial.mul_esymm_eq_sum (Fin d) ℂ k
    have ha := congrArg (MvPolynomial.aeval a) key
    have hb := congrArg (MvPolynomial.aeval b) key
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_mul, map_natCast, map_pow, map_neg, map_one, map_sum] at ha hb
    rw [ha, hb]
    congr 1
    refine Finset.sum_congr rfl ?_
    intro p hp
    rw [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at hp
    obtain ⟨h1, h2⟩ := hp
    rw [ih p.1 h2 (by omega)]
    congr 1
    have := h p.2 (by omega) (by omega)
    simpa [MvPolynomial.psum] using this

end GlobalTheory.EsymmOfPowerSums
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CuspidalLabelPolynomialUniqueAllPrimes
open CategoryTheory Polynomial
open scoped Classical

noncomputable section

namespace GlobalTheory.GLq.LabelUniqueAll

open Finset

theorem esymm_eq_of_psum_eq {d : ℕ} (a b : Fin d → ℂ)
    (h : ∀ k, 1 ≤ k → k ≤ d → ∑ i, a i ^ k = ∑ i, b i ^ k) :
    ∀ k, k ≤ d → MvPolynomial.aeval a (MvPolynomial.esymm (Fin d) ℂ k) =
      MvPolynomial.aeval b (MvPolynomial.esymm (Fin d) ℂ k) := by
  first
  | exact @_root_.GlobalTheory.EsymmOfPowerSums.esymm_eq_of_psum_eq
  | exact _root_.GlobalTheory.EsymmOfPowerSums.esymm_eq_of_psum_eq
  | (apply _root_.GlobalTheory.EsymmOfPowerSums.esymm_eq_of_psum_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.EsymmOfPowerSums.esymm_eq_of_psum_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.EsymmOfPowerSums.esymm_eq_of_psum_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.EsymmOfPowerSums.esymm_eq_of_psum_eq ..)

theorem map_eq_of_psum_eq {d : ℕ} (a b : Fin d → ℂ)
    (h : ∀ k, 1 ≤ k → k ≤ d → ∑ i, a i ^ k = ∑ i, b i ^ k) :
    Finset.univ.val.map a = Finset.univ.val.map b := by
  have he := esymm_eq_of_psum_eq a b h
  have hp : ((Finset.univ.val.map a).map fun t => X - C t).prod =
      ((Finset.univ.val.map b).map fun t => X - C t).prod := by
    rw [Multiset.prod_X_sub_X_eq_sum_esymm, Multiset.prod_X_sub_X_eq_sum_esymm]
    simp only [Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_fin]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [← MvPolynomial.aeval_esymm_eq_multiset_esymm (σ := Fin d) (R := ℂ), ← MvPolynomial.aeval_esymm_eq_multiset_esymm (σ := Fin d) (R := ℂ),
      he j (by simpa [Nat.lt_succ_iff] using hj)]
  have := congrArg Polynomial.roots hp
  rw [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at this
  exact this

theorem two_mul_le_two_pow (n : ℕ) : 2 * n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    rw [pow_succ]; omega

variable {g : ℕ} [Fact g.Prime]

theorem natDegree_minpoly_gen_pow (L : LabelDatum g) {d : ℕ} (hd : 0 < d) {k : ℕ} (hk1 : 1 ≤ k)
    (hkd : k ≤ d) : (minpoly (ZMod g) (L.gen d ^ k)).natDegree = d := by
  set γ := L.gen d
  set m := g ^ d - 1 with hmdef
  have hg2 : 2 ≤ g := (Fact.out : g.Prime).two_le
  have hgd : 2 ≤ g ^ d := le_trans hg2 (Nat.le_self_pow hd.ne' g)
  have hord : orderOf γ = m := L.gen_order d hd
  have hγm : γ ^ m = 1 := by rw [← hord]; exact pow_orderOf_eq_one _
  have hγ0 : γ ≠ 0 := by
    intro h0; rw [h0, zero_pow (by omega)] at hγm; exact zero_ne_one hγm
  have hfix : (γ ^ k) ^ (g ^ d) = γ ^ k := by
    rw [← pow_mul, mul_comm, pow_mul, show g ^ d = m + 1 by omega, pow_succ, hγm, one_mul]
  have hdvd : (minpoly (ZMod g) (γ ^ k)).natDegree ∣ d :=
    (GlobalTheory.GLm.SubfieldCount.natDegree_dvd_iff _ d).2 hfix
  have hfe : (γ ^ k) ^ (g ^ (minpoly (ZMod g) (γ ^ k)).natDegree) = γ ^ k :=
    (GlobalTheory.GLm.SubfieldCount.natDegree_dvd_iff _ _).1 dvd_rfl
  have he0 : 0 < (minpoly (ZMod g) (γ ^ k)).natDegree :=
    minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral _)
  generalize (minpoly (ZMod g) (γ ^ k)).natDegree = e at hdvd hfe he0 ⊢
  by_contra hne
  obtain ⟨c, hc⟩ := hdvd
  have hc2 : 2 ≤ c := by
    rcases c with _ | _ | c
    · simp at hc; omega
    · simp at hc; omega
    · omega
  have hge : 2 ≤ g ^ e := le_trans hg2 (Nat.le_self_pow he0.ne' g)
  have hone : γ ^ (k * (g ^ e - 1)) = 1 := by
    have : γ ^ k * γ ^ (k * (g ^ e - 1)) = γ ^ k * 1 := by
      rw [mul_one, ← pow_add]
      conv_rhs => rw [← hfe, ← pow_mul]
      congr 1
      have : g ^ e = (g ^ e - 1) + 1 := by omega
      conv_rhs => rw [this]
      ring
    exact mul_left_cancel₀ (pow_ne_zero _ hγ0) this
  have hmd : m ∣ k * (g ^ e - 1) := hord ▸ orderOf_dvd_of_pow_eq_one hone
  have hpos : 0 < k * (g ^ e - 1) := Nat.mul_pos (by omega) (by omega)
  have hle := Nat.le_of_dvd hpos hmd
  have hec : e * 2 ≤ e * c := Nat.mul_le_mul_left e hc2
  have h2 : d ≤ 2 * (d - e) := by omega
  have h3 : 2 * (d - e) ≤ 2 ^ (d - e) := two_mul_le_two_pow _
  have h4 : 2 ^ (d - e) ≤ g ^ (d - e) := Nat.pow_le_pow_left hg2 _
  have h5 : d * g ^ e ≤ g ^ d := by
    calc d * g ^ e ≤ g ^ (d - e) * g ^ e := Nat.mul_le_mul_right _ (by omega)
      _ = g ^ d := by rw [← pow_add, Nat.sub_add_cancel (by omega)]
  have h6 : k * (g ^ e - 1) ≤ d * (g ^ e - 1) := Nat.mul_le_mul_right _ hkd
  have h7 : d * (g ^ e - 1) = d * g ^ e - d := Nat.mul_sub_one _ _
  omega

theorem label_eq (L : LabelDatum g) (d : ℕ) (P P' : (ZMod g)[X]) (χ : Gn g d → ℂ)
    (h : IsCuspOf L P χ) (h' : IsCuspOf L P' χ) : P = P' := by
  obtain ⟨hPl, hc, hval⟩ := h
  obtain ⟨hPl', -, hval'⟩ := h'
  have hd : 0 < d := hc.1
  obtain ⟨x, hx⟩ := LabelUnique.exists_mem hd hPl
  obtain ⟨x', hx'⟩ := LabelUnique.exists_mem hd hPl'
  have hx1 := LabelUnique.pow_sub_one_eq_one hPl hx
  have hx1' := LabelUnique.pow_sub_one_eq_one hPl' hx'
  have hteich : ∀ w : Formalism.CyclotomicNorms.Fbar g, w ^ (g ^ d - 1) = 1 → L.teich w ^ (g ^ d - 1) = 1 := fun w hw => by
    rw [← map_pow, hw, map_one]
  have hg2 : 2 ≤ g := (Fact.out : g.Prime).two_le
  have hgd : 2 ≤ g ^ d := le_trans hg2 (Nat.le_self_pow hd.ne' g)
  have hγ0 : L.gen d ≠ 0 := by
    have hγm : L.gen d ^ (g ^ d - 1) = 1 := by rw [← L.gen_order d hd]; exact pow_orderOf_eq_one _
    intro h0; rw [h0, zero_pow (by omega)] at hγm; exact zero_ne_one hγm
  have hsums : ∀ k, 1 ≤ k → k ≤ d → ∑ i : Fin d, L.teich (x ^ (g ^ (i : ℕ))) ^ k =
      ∑ i : Fin d, L.teich (x' ^ (g ^ (i : ℕ))) ^ k := by
    intro k hk1 hkd
    have hdeg := natDegree_minpoly_gen_pow L hd hk1 hkd
    obtain ⟨y, hy, hz⟩ := GlobalTheory.GLm.exists_irreducible_charpoly_mem_rootsBar g d (L.gen d ^ k)
      (pow_ne_zero _ hγ0) hdeg
    have e1 := hval x hx y hy _ hz
    have e2 := hval' x' hx' y hy _ hz
    rw [e1] at e2
    have e3 := mul_left_cancel₀ (pow_ne_zero (d - 1) (by norm_num : (-1 : ℂ) ≠ 0)) e2
    have conv : ∀ w : Formalism.CyclotomicNorms.Fbar g, w ^ (g ^ d - 1) = 1 → ∀ i : ℕ,
        thetaOf L d w ((L.gen d ^ k) ^ (g ^ i)) = L.teich (w ^ (g ^ i)) ^ k := by
      intro w hw i
      rw [← pow_mul, LabelUnique.thetaOf_gen_pow L d hd w (hteich w hw), map_pow, ← pow_mul,
        Nat.mul_comm]
    simp only [conv x hx1, conv x' hx1'] at e3
    rw [Fin.sum_univ_eq_sum_range (fun i => L.teich (x ^ g ^ i) ^ k),
      Fin.sum_univ_eq_sum_range (fun i => L.teich (x' ^ g ^ i) ^ k)]
    exact e3
  have hm := map_eq_of_psum_eq _ _ hsums
  have hmem : L.teich x ∈ Finset.univ.val.map (fun i : Fin d => L.teich (x ^ (g ^ (i : ℕ)))) :=
    Multiset.mem_map.2 ⟨⟨0, hd⟩, Finset.mem_univ_val _, by simp⟩
  rw [hm] at hmem
  obtain ⟨i, -, hi⟩ := Multiset.mem_map.1 hmem
  have hxe : x = x' ^ (g ^ (i : ℕ)) :=
    L.teich_inj _ _ (LabelUnique.ne_zero_of_mem hPl hx)
      (pow_ne_zero _ (LabelUnique.ne_zero_of_mem hPl' hx')) hi.symm
  have h1 : aeval x P' = 0 := by
    rw [hxe]; exact LabelUnique.aeval_pow_eq_zero (LabelUnique.aeval_eq_zero_of_mem hPl'.1.ne_zero hx') i
  have h2 := minpoly.eq_of_irreducible_of_monic hPl'.2.1 h1 hPl'.1
  rw [h2, LabelUnique.minpoly_eq_of_mem hPl hx]

end GlobalTheory.GLq.LabelUniqueAll

namespace GlobalTheory.GLq

theorem isCuspOf_label_unique_allPrimes : GlobalTheory.Published.GreenCuspidal → ∀ (g : ℕ) [Fact g.Prime]
    (L : GlobalTheory.GLq.LabelDatum g) (d : ℕ) (P P' : (ZMod g)[X]) (χ : GlobalTheory.GLq.Gn g d → ℂ),
    GlobalTheory.GLq.IsCuspOf L P χ → GlobalTheory.GLq.IsCuspOf L P' χ → P = P' :=
  fun _ _ _ L d P P' χ h h' => LabelUniqueAll.label_eq L d P P' χ h h'

end GlobalTheory.GLq
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CuspidalLabelPolynomialUniqueAllPrimesStatement
open CategoryTheory Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_label_polynomial_unique_all_primes : GlobalTheory.Published.GreenCuspidal → ∀ (g : ℕ) [Fact g.Prime] (L : GlobalTheory.GLq.LabelDatum g) (d : ℕ) (P P' : (ZMod g)[X]) (χ : GlobalTheory.GLq.Gn g d → ℂ), GlobalTheory.GLq.IsCuspOf L P χ → GlobalTheory.GLq.IsCuspOf L P' χ → P = P' := by
  first | exact @GlobalTheory.GLq.isCuspOf_label_unique_allPrimes | exact GlobalTheory.GLq.isCuspOf_label_unique_allPrimes | (intros; apply GlobalTheory.GLq.isCuspOf_label_unique_allPrimes <;> assumption)
end
end
