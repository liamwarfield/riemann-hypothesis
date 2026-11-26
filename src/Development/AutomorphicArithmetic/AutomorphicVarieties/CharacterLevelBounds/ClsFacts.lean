module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ShaFamMono
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.KerResCyc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ContTw

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr

private theorem exists_primitiveRoot_of_isAlgClosure' (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (N : ℕ) [NeZero N] : ∃ ζ : Ω, IsPrimitiveRoot ζ N := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k Ω).injective
  exact HasEnoughRootsOfUnity.exists_primitiveRoot Ω N

private theorem cls_apply_root_of_unity_eq_pow (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (N : ℕ) [NeZero N] (σ : G k Ω) (ζ : Ω) (hζ : ζ ^ N = 1) :
    σ ζ = ζ ^ ((cls k Ω N σ : (ZMod N)ˣ) : ZMod N).val := by
  have h0 : ζ ≠ 0 := by
    rintro rfl
    simp [NeZero.ne N] at hζ
  have ht : Units.mk0 ζ h0 ∈ rootsOfUnity N Ω := by
    rw [mem_rootsOfUnity]
    ext
    simpa using hζ
  obtain ⟨ξ, hξ⟩ := exists_primitiveRoot_of_isAlgClosure' k Ω N
  have := modularCyclotomicCharacter.spec Ω hξ.card_rootsOfUnity
    (MulSemiringAction.toRingAut (G k Ω) Ω σ) ht
  exact this

private theorem cls_eq_of_forall_root_of_unity_apply_eq_pow (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (N : ℕ) [NeZero N] (σ : G k Ω) (u : (ZMod N)ˣ)
    (h : ∀ ζ : Ω, ζ ^ N = 1 → σ ζ = ζ ^ (u : ZMod N).val) : cls k Ω N σ = u := by
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_of_isAlgClosure' k Ω N
  ext1
  refine (modularCyclotomicCharacter.unique Ω hζ.card_rootsOfUnity
    (MulSemiringAction.toRingAut (G k Ω) Ω σ) (c := (u : ZMod N)) ?_).symm
  intro t ht
  rw [mem_rootsOfUnity] at ht
  have ht' : (t : Ω) ^ N = 1 := by rw [← Units.val_pow_eq_pow_val, ht, Units.val_one]
  exact h t ht'

private theorem root_of_unity_pow_natCast_zmod_val {Ω : Type} [Field Ω] (N : ℕ) [NeZero N] (ζ : Ω) (hζ : ζ ^ N = 1)
    (b : ℕ) : ζ ^ ((b : ZMod N)).val = ζ ^ b := by
  rw [ZMod.val_natCast]
  conv_rhs => rw [← Nat.mod_add_div b N, pow_add, pow_mul, hζ, one_pow, mul_one]

private theorem cls_eq_one_of_fixes_primitiveRoot (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (N : ℕ) [NeZero N] (σ : G k Ω) (ζ : Ω) (hζ : IsPrimitiveRoot ζ N)
    (hσ : σ ζ = ζ) : cls k Ω N σ = 1 := by
  apply cls_eq_of_forall_root_of_unity_apply_eq_pow
  intro ξ hξ
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hξ
  have h1 := root_of_unity_pow_natCast_zmod_val N _ hξ 1
  rw [Nat.cast_one, pow_one] at h1
  rw [map_pow, hσ, Units.val_one, h1]

theorem UpperTheory.V.Chr.clsFacts :
    ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (N : ℕ) [NeZero N],
          IsOpen ((cls k Ω N).ker : Set (G k Ω)) ∧ (∀ (M : ℕ) [NeZero M] (h : M ∣ N), (ZMod.unitsMap h).comp (cls k Ω N) = cls k Ω M) ∧
          (∀ (σ : G k Ω) (u : (ZMod N)ˣ), (∀ ζ : Ω, ζ ^ N = 1 → σ ζ = ζ ^ (u : ZMod N).val) → cls k Ω N σ = u) ∧
          (∀ σ : G k Ω, IsConjOm σ.toRingEquiv → cls k Ω N σ = -1) ∧
          ∀ A : ValuationSubring Ω, ¬ A.valuation (N : Ω) < 1 → Ine (F := k) A ≤ (cls k Ω N).ker := by
  intro k Ω _ _ _ _ _ N _
  refine ⟨?_, ?_, fun σ u h => cls_eq_of_forall_root_of_unity_apply_eq_pow k Ω N σ u h, ?_, ?_⟩
  · obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_of_isAlgClosure' k Ω N
    haveI : Algebra.IsAlgebraic k Ω := IsAlgClosure.isAlgebraic
    have hi : IsIntegral k ζ := (Algebra.IsAlgebraic.isAlgebraic ζ).isIntegral
    haveI : FiniteDimensional k (IntermediateField.adjoin k {ζ}) :=
      IntermediateField.adjoin.finiteDimensional hi
    refine Subgroup.isOpen_mono ?_
      (IntermediateField.fixingSubgroup_isOpen (IntermediateField.adjoin k {ζ}))
    intro σ hσ
    rw [MonoidHom.mem_ker]
    exact cls_eq_one_of_fixes_primitiveRoot k Ω N σ ζ hζ ((IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ ζ
      (IntermediateField.mem_adjoin_simple_self k ζ))
  · intro M _ hMN
    ext1 σ
    symm
    apply cls_eq_of_forall_root_of_unity_apply_eq_pow
    intro ζ hζ
    rw [MonoidHom.comp_apply, ZMod.unitsMap_val, ZMod.cast_eq_val, root_of_unity_pow_natCast_zmod_val M ζ hζ]
    obtain ⟨d, hd⟩ := hMN
    exact cls_apply_root_of_unity_eq_pow k Ω N σ ζ (by rw [hd, pow_mul, hζ, one_pow])
  · intro σ hσ
    obtain ⟨j, hj⟩ := hσ
    apply cls_eq_of_forall_root_of_unity_apply_eq_pow
    intro ζ hζ
    have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
    have h0 : ζ ≠ 0 := by
      rintro rfl
      simp [NeZero.ne N] at hζ
    have hval : ((-1 : (ZMod N)ˣ) : ZMod N) = ((N - 1 : ℕ) : ZMod N) := by
      rw [Units.val_neg, Units.val_one, Nat.cast_sub hN1, ZMod.natCast_self, Nat.cast_one, zero_sub]
    rw [hval, root_of_unity_pow_natCast_zmod_val N ζ hζ, pow_sub₀ ζ h0 hN1, hζ, pow_one, one_mul]
    apply j.injective
    have hjζ := hj ζ
    simp only [AlgEquiv.coe_toRingEquiv, AlgEquiv.coe_ringEquiv] at hjζ
    rw [hjζ, map_inv₀]
    have hz : (j ζ) ^ N = 1 := by rw [← map_pow, hζ, map_one]
    have hn : ‖j ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hz (NeZero.ne N)
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hn]
    simp
  · intro A hA σ hσ
    rw [MonoidHom.mem_ker]
    obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_of_isAlgClosure' k Ω N
    apply cls_eq_one_of_fixes_primitiveRoot k Ω N σ ζ hζ
    have hin : ∀ x : Ω, A.valuation x ≤ 1 → A.valuation (σ x - x) < 1 := hσ.2
    by_contra hne
    have h0 : ζ ≠ 0 := hζ.ne_zero (NeZero.ne N)
    set ξ := σ ζ * ζ⁻¹ with hξdef
    have hξN : ξ ^ N = 1 := by
      rw [hξdef, mul_pow, inv_pow, ← map_pow, hζ.pow_eq_one, map_one, one_mul, inv_one]
    have hξ1 : ξ ≠ 1 := by
      intro h
      apply hne
      rw [hξdef, mul_inv_eq_one₀ h0] at h
      exact h
    have hv1 : ∀ x : Ω, x ^ N = 1 → A.valuation x = 1 := by
      intro x hx
      have hp : A.valuation x ^ N = 1 := by rw [← map_pow, hx, map_one]
      exact (pow_eq_one_iff.1 hp).resolve_right (NeZero.ne N)
    have hsum : ∑ i ∈ Finset.range N, ξ ^ i = 0 := by
      have hg := geom_sum_mul ξ N
      rw [hξN, sub_self] at hg
      exact (mul_eq_zero.1 hg).resolve_right (sub_ne_zero.2 hξ1)
    have hNeq : (N : Ω) = (1 - ξ) * ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range i, ξ ^ j := by
      rw [Finset.mul_sum]
      simp_rw [mul_neg_geom_sum]
      rw [Finset.sum_sub_distrib, hsum]
      simp
    have hξA : ξ ∈ A := (A.valuation_le_one_iff ξ).1 (hv1 ξ hξN).le
    have hSA : (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range i, ξ ^ j) ∈ A :=
      sum_mem fun i _ => sum_mem fun j _ => pow_mem hξA j
    have hS : A.valuation (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range i, ξ ^ j) ≤ 1 :=
      (A.valuation_le_one_iff _).2 hSA
    have hdiff : σ ζ - ζ = -(ζ * (1 - ξ)) := by
      rw [hξdef]
      field_simp
      ring
    have hlt : A.valuation (1 - ξ) < 1 := by
      have := hin ζ (hv1 ζ hζ.pow_eq_one).le
      rw [hdiff, Valuation.map_neg, map_mul, hv1 ζ hζ.pow_eq_one, one_mul] at this
      exact this
    apply hA
    rw [hNeq, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' hS) hlt
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.PlacesQ
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr
open scoped Pointwise

namespace UpperTheory.V.Chr.RationalPlaces

variable (l : ℕ) [hl : Fact l.Prime]

private theorem prime_l : Prime ((l : ℕ) : 𝓞 ℚ) := by
  have h : Prime ((l : ℤ)) := Nat.prime_iff_prime_int.mp hl.out
  have e : Rat.ringOfIntegersEquiv ((l : ℕ) : 𝓞 ℚ) = (l : ℤ) := map_natCast _ l
  rw [← e] at h
  exact (MulEquiv.prime_iff (Rat.ringOfIntegersEquiv : 𝓞 ℚ ≃+* ℤ)).mp h

private noncomputable def vQ : HeightOneSpectrum (𝓞 ℚ) where
  asIdeal := Ideal.span {((l : ℕ) : 𝓞 ℚ)}
  isPrime := (Ideal.span_singleton_prime (prime_l l).ne_zero).mpr (prime_l l)
  ne_bot := by rw [Ne, Ideal.span_singleton_eq_bot]; exact (prime_l l).ne_zero

variable {l} {Ω : Type} [Field Ω]

private theorem isPlaceOver_vQ [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω)
    (hA : A.valuation ((l : ℕ) : Ω) < 1) : IsPlaceOver (F := ℚ) A (vQ l) := by
  unfold IsPlaceOver
  intro x
  set m : ℤ := Rat.ringOfIntegersEquiv x with hmdef
  have hx : algebraMap ℚ Ω (x : ℚ) = (m : Ω) := by
    have e : ((m : ℤ) : ℚ) = (x : ℚ) := by
      rw [hmdef, Rat.ringOfIntegersEquiv_apply_coe]
    rw [← e, map_intCast]
  have hmem : x ∈ (vQ l).asIdeal ↔ (l : ℤ) ∣ m := by
    change x ∈ Ideal.span {((l : ℕ) : 𝓞 ℚ)} ↔ _
    rw [Ideal.mem_span_singleton, ← map_dvd_iff Rat.ringOfIntegersEquiv, map_natCast]
  have hA' : A.valuation ((l : ℤ) : Ω) < 1 := by
    rw [Int.cast_natCast]
    exact hA
  have hint : ∀ k : ℤ, A.valuation (k : Ω) ≤ 1 := fun k =>
    (ValuationSubring.valuation_le_one_iff A _).mpr (intCast_mem A k)
  rw [hx, hmem]
  constructor
  · intro hm
    by_contra hnd
    have hirr : Irreducible (l : ℤ) := (Nat.prime_iff_prime_int.mp hl.out).irreducible
    obtain ⟨a, b, hab⟩ := (hirr.coprime_iff_not_dvd).mpr hnd
    have h1 : ((a : Ω) * (l : ℤ) + (b : Ω) * (m : Ω)) = 1 := by
      have := congrArg (fun z : ℤ => (z : Ω)) hab
      push_cast at this ⊢
      exact this
    have hle : A.valuation (1 : Ω) < 1 := by
      rw [← h1]
      refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
      · rw [map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' (hint a)) hA'
      · rw [map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' (hint b)) hm
    rw [map_one] at hle
    exact lt_irrefl _ hle
  · rintro ⟨k, hk⟩
    rw [hk, Int.cast_mul, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (hint k)) hA'

private theorem val_natCast_le_one (A : ValuationSubring Ω) (n : ℕ) : A.valuation (n : Ω) ≤ 1 :=
  (A.valuation_le_one_iff _).mpr (natCast_mem A n)

private theorem val_lt_one_iff (A : ValuationSubring Ω) (n : ℕ) (hn : n ≠ 0) :
    A.valuation (n : Ω) < 1 ↔ ∃ p ∈ n.primeFactors, A.valuation (p : Ω) < 1 := by
  revert hn
  induction n using Nat.recOnMul with
  | zero => intro h; exact absurd rfl h
  | one => intro _; simp
  | prime p hp =>
    intro _
    rw [hp.primeFactors]
    simp
  | mul a b iha ihb =>
    intro hab
    have ha : a ≠ 0 := left_ne_zero_of_mul hab
    have hb : b ≠ 0 := right_ne_zero_of_mul hab
    have key : A.valuation (a : Ω) * A.valuation (b : Ω) < 1 ↔
        A.valuation (a : Ω) < 1 ∨ A.valuation (b : Ω) < 1 := by
      constructor
      · intro h
        by_contra hc
        push_neg at hc
        have e1 : A.valuation (a : Ω) = 1 := le_antisymm (val_natCast_le_one A a) hc.1
        have e2 : A.valuation (b : Ω) = 1 := le_antisymm (val_natCast_le_one A b) hc.2
        rw [e1, e2, one_mul] at h
        exact lt_irrefl _ h
      · rintro (h | h)
        · exact lt_of_le_of_lt (mul_le_of_le_one_right' (val_natCast_le_one A b)) h
        · exact lt_of_le_of_lt (mul_le_of_le_one_left' (val_natCast_le_one A a)) h
    rw [Nat.cast_mul, map_mul, Nat.primeFactors_mul ha hb, key, iha ha, ihb hb]
    simp only [Finset.mem_union]
    constructor
    · rintro (⟨p, hp, h⟩ | ⟨p, hp, h⟩)
      exacts [⟨p, Or.inl hp, h⟩, ⟨p, Or.inr hp, h⟩]
    · rintro ⟨p, hp | hp, h⟩
      exacts [Or.inl ⟨p, hp, h⟩, Or.inr ⟨p, hp, h⟩]

private theorem exists_place [CharZero Ω] (p : ℕ) (hp : p.Prime) :
    ∃ A : ValuationSubring Ω, A.valuation (p : Ω) < 1 := by
  let x : (⊥ : Subring Ω) := ⟨(p : Ω), natCast_mem _ p⟩
  have hI : Ideal.span {x} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    intro hu
    obtain ⟨y, hy⟩ := hu.exists_right_inv
    obtain ⟨m, hm⟩ := Subring.mem_bot.mp y.2
    have h1 : (((p : ℤ) * m : ℤ) : Ω) = ((1 : ℤ) : Ω) := by
      have hv := congrArg Subtype.val hy
      push_cast
      rw [hm]
      exact hv
    have h2 : (p : ℤ) * m = 1 := Int.cast_injective h1
    have h3 : IsUnit (p : ℤ) := isUnit_iff_exists_inv.mpr ⟨m, h2⟩
    rw [Int.isUnit_iff_natAbs_eq, Int.natAbs_natCast] at h3
    exact hp.ne_one h3
  obtain ⟨B, -, hB⟩ := Ideal.image_subset_nonunits_valuationSubring _ hI
  exact ⟨B, (B.mem_nonunits_iff).mp (hB ⟨x, Ideal.subset_span rfl, rfl⟩)⟩

end UpperTheory.V.Chr.RationalPlaces

open UpperTheory.V.Chr.RationalPlaces in
theorem UpperTheory.V.Chr.placesQ :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω], (∀ p : ℕ, p.Prime → ∃ A : ValuationSubring Ω, A.valuation (p : Ω) < 1) ∧
          (∀ (A : ValuationSubring Ω) (n : ℕ), n ≠ 0 → (A.valuation (n : Ω) < 1 ↔ ∃ p ∈ n.primeFactors, A.valuation (p : Ω) < 1)) ∧
          ∀ (p : ℕ) (A A' : ValuationSubring Ω), p.Prime → A.valuation (p : Ω) < 1 → A'.valuation (p : Ω) < 1 →
            ∃ u : G ℚ Ω, (∀ x ∈ Dec (F := ℚ) A, u⁻¹ * x * u ∈ Dec (F := ℚ) A') ∧ ∀ x ∈ Ine (F := ℚ) A, u⁻¹ * x * u ∈ Ine (F := ℚ) A' := by
  intro Ω _ _ _
  refine ⟨fun p hp => exists_place p hp, fun A n hn => val_lt_one_iff A n hn, ?_⟩
  intro p A A' hp hA hA'
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver (isPlaceOver_vQ A hA) (isPlaceOver_vQ A' hA')
  have hL : IsLift (RingEquiv.refl ℚ) (σ⁻¹ : G ℚ Ω).toRingEquiv := fun x =>
    AlgEquiv.commutes _ x
  have hmem : ∀ x : Ω, (σ⁻¹ : G ℚ Ω).toRingEquiv x ∈ A ↔ x ∈ A' := by
    intro x
    rw [← hσ, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    rfl
  have hconj : ∀ g : G ℚ Ω, (σ⁻¹)⁻¹ * g * σ⁻¹ = conjGal hL g := by
    intro g
    ext x
    rfl
  refine ⟨σ⁻¹, ?_, ?_⟩
  · intro g hg
    rw [hconj]
    exact conjGal_mem_Dec hL hmem hg
  · intro g hg
    rw [hconj]
    exact conjGal_mem_Ine hL hmem hg
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.RootVal
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr

private theorem sub_one_dvd {O : Type} [CommRing O] [IsDomain O] {n : ℕ} {ζ : O} (h : ζ ^ n = 1) (h1 : ζ ≠ 1) :
    ζ - 1 ∣ (n : O) := by
  have hS : ∑ i ∈ Finset.range n, ζ ^ i = 0 := by
    have hg := mul_geom_sum ζ n
    rw [h, sub_self] at hg
    exact (mul_eq_zero.mp hg).resolve_left (sub_ne_zero.mpr h1)
  have hn : (n : O) = ∑ i ∈ Finset.range n, (1 - ζ ^ i) := by
    rw [Finset.sum_sub_distrib, hS, sub_zero, Finset.sum_const, Finset.card_range, nsmul_one]
  rw [hn]
  apply Finset.dvd_sum
  intro i _
  have hd := sub_dvd_pow_sub_pow ζ 1 i
  rw [one_pow] at hd
  rw [← neg_sub (ζ ^ i) 1]
  exact (dvd_neg).mpr hd

theorem UpperTheory.V.Chr.rootVal :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (n : ℕ), n ≠ 0 → IsDiscreteValuationRing.addVal O (n : O) = (n.factorization l : ℕ∞) * eO l O ∧
          (∀ ζ : O, ζ ^ n = 1 → ζ ≠ 1 → IsDiscreteValuationRing.addVal O (ζ - 1) ≤ (n.factorization l : ℕ∞) * eO l O) ∧ eO l O ≠ ⊤ ∧ CharZero O := by
  intro l _ O _ _ _ _ _ n hn
  obtain ⟨hiO, -, -, -, -, -, -, hvO, hunit⟩ := dvrFacts l O
  have hp : l.Prime := Fact.out
  have hl0 : (l : ℤ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hlO : (l : O) ≠ 0 := by
    intro h
    apply hl0
    apply hiO
    rw [map_natCast, h, map_zero]
  have hval : IsDiscreteValuationRing.addVal O (n : O) = (n.factorization l : ℕ∞) * eO l O := by
    have hu : IsUnit ((n / l ^ n.factorization l : ℕ) : O) := hunit _ (Nat.not_dvd_ordCompl hp hn)
    conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self n l]
    rw [Nat.cast_mul, Nat.cast_pow, IsDiscreteValuationRing.addVal_mul,
      IsDiscreteValuationRing.addVal_pow, (IsDiscreteValuationRing.addVal_eq_zero_iff).mpr hu,
      add_zero, hvO, nsmul_eq_mul]
  refine ⟨hval, ?_, ?_, ?_⟩
  · intro ζ hζ h1
    rw [← hval]
    exact (IsDiscreteValuationRing.addVal_le_iff_dvd).mpr (sub_one_dvd hζ h1)
  · rw [hvO]
    exact fun h => hlO ((IsDiscreteValuationRing.addVal_eq_top_iff).mp h)
  · exact charZero_of_injective_algebraMap hiO
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.LevGal
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr

theorem UpperTheory.V.Chr.levGal :
    ∀ (E : Type) [Field E] [NumberField E] (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ), HasLevel E N H → IsAbelianGalois ℚ E ∧ Module.finrank ℚ E = H.index ∧
          ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra E Ω], galOf ℚ E Ω = levH ℚ Ω H ∧ (levH ℚ Ω H).index = H.index ∧ IsOpen (levH ℚ Ω H : Set (G ℚ Ω)) := by
  intro E _ _ N _ H hlev
  obtain ⟨j, ζ, hζ, hj⟩ := hlev
  haveI : NeZero ((N : ℕ) : ℚ) := ⟨by exact_mod_cast NeZero.ne N⟩
  haveI : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) :=
    CyclotomicField.isCyclotomicExtension N ℚ
  haveI : IsAbelianGalois ℚ (CyclotomicField N ℚ) :=
    IsCyclotomicExtension.isAbelianGalois {N} ℚ (CyclotomicField N ℚ)
  have hfs : KStar.TotallyRealRoots.fieldSubgroup N (CyclotomicField N ℚ) j.fieldRange = H := by
    ext u
    unfold KStar.TotallyRealRoots.fieldSubgroup
    rw [Subgroup.mem_map_equiv]
    set τ := (IsCyclotomicExtension.Rat.galEquivZMod N (CyclotomicField N ℚ)).symm u with hτdef
    have hu : IsCyclotomicExtension.Rat.galEquivZMod N (CyclotomicField N ℚ) τ = u := by
      rw [hτdef]
      exact MulEquiv.apply_symm_apply _ u
    have hτ : τ ζ = ζ ^ (u : ZMod N).val := by
      rw [IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq N _ τ hζ.pow_eq_one, hu]
    rw [← hj τ u hτ, IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro h x
      exact h (j x) ⟨x, rfl⟩
    · rintro h _ ⟨x, rfl⟩
      exact h x
  have hfr : Module.finrank ℚ j.fieldRange = Module.finrank ℚ E := by
    rw [(AlgEquiv.ofInjectiveField j).toLinearEquiv.finrank_eq]
    rfl
  have hfin : Module.finrank ℚ E = H.index := by
    rw [← hfr, IntermediateField.finrank_eq_fixingSubgroup_index, ← hfs]
    unfold KStar.TotallyRealRoots.fieldSubgroup
    exact (Subgroup.index_map_of_bijective (MulEquiv.bijective _) _).symm
  refine ⟨IsAbelianGalois.of_algHom j, hfin, ?_⟩
  intro Ω _ _ _ _
  haveI : IsScalarTower ℚ E Ω := inferInstance
  haveI : IsAlgClosure E Ω :=
    ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) E⟩
  have heq : galOf ℚ E Ω = levH ℚ Ω H := by
    ext σ
    rw [mem_galOf]
    unfold levH
    rw [Subgroup.mem_comap, ← hfs]
    exact LDataCardLeFinrank.classFix E Ω N (CyclotomicField N ℚ) j σ.toRingEquiv (cls ℚ Ω N σ)
      (fun z hz => cls_spec N σ z hz)
  obtain ⟨-, hopen, hidx⟩ := galEmbTop ℚ E Ω
  refine ⟨heq, ?_, ?_⟩
  · rw [← heq, hidx, hfin]
  · rw [← heq]
    exact hopen
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.EigV
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.SelEigBase
open ReciprocityTheory.Gal UpperTheory.V.Base

theorem UpperTheory.V.Base.selEigBase :
    ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup M] [Module R M]
      [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M] (ρ : Representation R G M) (ρ' : Representation R G M) (θ : G →* Rˣ), (∀ g m, ρ g m = ((θ g : Rˣ) : R) • ρ' g m) → ContAction ρ' →
      ∀ (U W : Subgroup G) [U.Normal], U ≤ W → (∀ u ∈ U, θ u = 1) → IsOpen (U.subgroupOf W : Set W) → IsUnit (U.relIndex W : R) →
      ∀ (𝒟 : Set (Subgroup G)) (h𝒟 : ConjStable 𝒟), Module.length R (selEig ρ U h𝒟 W (θ.comp W.subtype)) = Module.length R (LocSel ρ' W 𝒟) := by
  intro R G M _ _ _ _ _ _ _ _ _ _ ρ ρ' θ hρ hc U W _ hUW hθ ho hu 𝒟 h𝒟
  have h1 := (selTwist R G M ρ ρ' θ hρ U hθ 𝒟 h𝒟).2 W 1
  obtain ⟨hi, hr⟩ := selUnit R G M ρ' hc U W hUW ho hu 𝒟 h𝒟
  have e : θ.comp W.subtype * (1 : W →* Rˣ) = θ.comp W.subtype := mul_one _
  rw [e] at h1
  rw [h1, ← hr]
  exact (LinearEquiv.ofInjective _ hi).length_eq.symm
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr

theorem UpperTheory.V.Chr.eigV :
    ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (e : ℕ) (ψ : G k Ω →* Oˣ) (U : Subgroup (G k Ω)) [U.Normal],
          IsOpen (U : Set (G k Ω)) → U ≤ ψ.ker → ¬ l ∣ U.index → eigL l e U ψ = V l e ψ := by
  intro k Ω _ _ _ _ _ l _ O _ _ _ _ _ e ψ U _ hU hker hind
  obtain ⟨-, -, -, -, -, -, -, -, hunit⟩ := dvrFacts l O
  have hopen : IsOpen ((ψ⁻¹).ker : Set (G k Ω)) := by
    have hk : (ψ⁻¹).ker = ψ.ker := by
      ext g
      simp [MonoidHom.mem_ker]
    rw [hk]
    exact Subgroup.isOpen_mono hker hU
  have hcont := (contTw k Ω l).2.2 O ψ⁻¹ (-(e : ℤ)) hopen
  unfold eigL V VS
  exact selEigBase O (G k Ω) (QO l O) _ (rho l e ψ) ψ (tw_apply l e ψ) hcont U ⊤ le_top
    (fun u hu => hker hu) (hU.preimage continuous_subtype_val)
    (by rw [Subgroup.relIndex_top_right]; exact hunit _ hind) _ (conjStable_shaFam k Ω l)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.LevChange
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr

private theorem level_iff (E : Type) [Field E] [NumberField E] (N : ℕ) [NeZero N]
    [hc : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ)] (H : Subgroup (ZMod N)ˣ) :
    HasLevel E N H ↔ ∃ j : E →ₐ[ℚ] CyclotomicField N ℚ, ∀ τ : CyclotomicField N ℚ ≃ₐ[ℚ] CyclotomicField N ℚ,
      (∀ x : E, τ (j x) = j x) ↔ IsCyclotomicExtension.Rat.galEquivZMod N (CyclotomicField N ℚ) τ ∈ H := by
  constructor
  · rintro ⟨j, ζ, hζ, h⟩
    exact ⟨j, fun τ => h τ _ (IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq N _ τ hζ.pow_eq_one)⟩
  · rintro ⟨j, h⟩
    have hζ := IsCyclotomicExtension.zeta_spec N ℚ (CyclotomicField N ℚ)
    refine ⟨j, _, hζ, fun τ u hu => ?_⟩
    rw [IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq N _ τ hζ.pow_eq_one,
      (hζ.isOfFinOrder (NeZero.ne _)).pow_inj_mod, ← hζ.eq_orderOf,
      ← ZMod.natCast_eq_natCast_iff', ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ← Units.ext_iff] at hu
    rw [← hu]
    exact h τ

private theorem change (E F K : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Field K] [NumberField K]
    (M N : ℕ) [NeZero M] [NeZero N] [IsCyclotomicExtension {M} ℚ F] [IsCyclotomicExtension {N} ℚ K]
    (h : M ∣ N) (H : Subgroup (ZMod M)ˣ) :
    (∃ j : E →ₐ[ℚ] F, ∀ τ : F ≃ₐ[ℚ] F,
      (∀ x : E, τ (j x) = j x) ↔ IsCyclotomicExtension.Rat.galEquivZMod M F τ ∈ H) ↔
    (∃ j : E →ₐ[ℚ] K, ∀ τ : K ≃ₐ[ℚ] K,
      (∀ x : E, τ (j x) = j x) ↔
        IsCyclotomicExtension.Rat.galEquivZMod N K τ ∈ H.comap (ZMod.unitsMap h)) := by
  haveI : IsGalois ℚ F := IsCyclotomicExtension.isGalois {M} ℚ F
  haveI : IsGalois ℚ K := IsCyclotomicExtension.isGalois {N} ℚ K
  obtain ⟨c, hc⟩ := id h
  have hη : IsPrimitiveRoot (IsCyclotomicExtension.zeta N ℚ K ^ c) M :=
    (IsCyclotomicExtension.zeta_spec N ℚ K).pow (NeZero.pos N) (hc.trans (mul_comm _ _))
  let i : F →ₐ[ℚ] K := ((IsCyclotomicExtension.zeta_spec M ℚ F).embeddingsEquivPrimitiveRoots K
    (Polynomial.cyclotomic.irreducible_rat (NeZero.pos M))).symm ⟨_, (mem_primitiveRoots (NeZero.pos M)).2 hη⟩
  letI : Algebra F K := i.toRingHom.toAlgebra
  haveI : IsGalois F K := IsGalois.tower_top_of_isGalois ℚ F K
  haveI : FiniteDimensional F K := Module.Finite.of_restrictScalars_finite ℚ F K
  have hinj := (algebraMap F K).injective
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨i.comp j, fun τ => ?_⟩
    rw [Subgroup.mem_comap, ← IsCyclotomicExtension.Rat.galEquivZMod_restrictNormal_apply N K F h τ, ← hj]
    refine forall_congr' fun x => ?_
    rw [← hinj.eq_iff, AlgEquiv.restrictNormal_commutes]
    rfl
  · rintro ⟨j, hj⟩
    have hr : ∀ x : E, ∃ y : F, algebraMap F K y = j x := by
      intro x
      have : j x ∈ Set.range (algebraMap F K) := by
        rw [IsGalois.mem_range_algebraMap_iff_fixed]
        intro σ
        refine (hj (σ.restrictScalars ℚ)).2 ?_ x
        have h1 : (σ.restrictScalars ℚ).restrictNormal F = 1 := by
          ext y
          apply hinj
          rw [AlgEquiv.restrictNormal_commutes]
          exact σ.commutes y
        rw [Subgroup.mem_comap, ← IsCyclotomicExtension.Rat.galEquivZMod_restrictNormal_apply N K F h, h1, map_one]
        exact H.one_mem
      exact this
    choose f hf using hr
    let j0 : E →+* F :=
      { toFun := f
        map_one' := hinj (by simp [hf])
        map_mul' := fun x y => hinj (by simp [hf])
        map_zero' := hinj (by simp [hf])
        map_add' := fun x y => hinj (by simp [hf]) }
    refine ⟨j0.toRatAlgHom, fun τ => ?_⟩
    have h2 := hj (τ.liftNormal K)
    rw [Subgroup.mem_comap, ← IsCyclotomicExtension.Rat.galEquivZMod_restrictNormal_apply N K F h,
      AlgEquiv.restrict_liftNormal] at h2
    rw [← h2]
    refine forall_congr' fun x => ?_
    rw [← hf x, ← hinj.eq_iff, ← τ.liftNormal_commutes K]
    rfl

theorem UpperTheory.V.Chr.levChange :
    ∀ (E : Type) [Field E] [NumberField E] (N : ℕ) [NeZero N], (Nonempty (E →ₐ[ℚ] CyclotomicField N ℚ) → ∃ H : Subgroup (ZMod N)ˣ, HasLevel E N H) ∧
          ∀ (M : ℕ) [NeZero M] (h : M ∣ N) (H : Subgroup (ZMod M)ˣ), HasLevel E M H ↔ HasLevel E N (H.comap (ZMod.unitsMap h)) := by
  intro E _ _ N _
  haveI : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) := CyclotomicField.isCyclotomicExtension N ℚ
  constructor
  · rintro ⟨j⟩
    refine ⟨j.fieldRange.fixingSubgroup.map
      (IsCyclotomicExtension.Rat.galEquivZMod N (CyclotomicField N ℚ)).toMonoidHom, (level_iff E N _).2 ⟨j, fun τ => ?_⟩⟩
    refine Iff.trans ?_ (Subgroup.mem_map_iff_mem (f := (IsCyclotomicExtension.Rat.galEquivZMod N (CyclotomicField N ℚ)).toMonoidHom)
      (IsCyclotomicExtension.Rat.galEquivZMod N (CyclotomicField N ℚ)).injective).symm
    rw [IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · rintro h _ ⟨x, rfl⟩
      exact h x
    · intro h x
      exact h _ ⟨x, rfl⟩
  · intro M _ h H
    haveI : IsCyclotomicExtension {M} ℚ (CyclotomicField M ℚ) := CyclotomicField.isCyclotomicExtension M ℚ
    rw [level_iff, level_iff]
    exact change E _ _ M N h H
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.H0Nu
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr

theorem UpperTheory.V.Chr.h0Nu :
    ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (e : ℕ) (ψ : G k Ω →* Oˣ) (U : Subgroup (G k Ω)),
          (∀ U' : Subgroup (G k Ω), U' ≤ U → h0 l e ψ U ≤ h0 l e ψ U') ∧
          (U ≤ ψ.ker → h0 l e ψ U ≤ KStar.TotallyRealRoots.nu l (U.map (cycZ k Ω l)) e * eO l O) := by
  intro k Ω _ _ _ _ _ l _ O _ _ _ _ _ e ψ U
  refine ⟨fun U' h => ?_, fun h => ?_⟩
  · have hle : H0U (rho l e ψ) U ≤ H0U (rho l e ψ) U' := fun m hm =>
      (mem_riemannRochSpace_iff_regularAt_everywhere _ _).2 fun g => (mem_riemannRochSpace_iff_regularAt_everywhere _ _).1 hm ⟨g.1, h g.2⟩
    exact Module.length_le_of_injective _ (Submodule.inclusion_injective hle)
  · obtain ⟨-, -, -, -, -, h0', -, hval, -⟩ := dvrFacts l O
    by_cases ht : KStar.TotallyRealRoots.nu l (U.map (cycZ k Ω l)) e = ⊤
    · rw [ht, ENat.top_mul h0']
      exact le_top
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp ht
    have hle : H0U (rho l e ψ) U ≤
        LinearMap.ker (((l : O) ^ n) • (LinearMap.id : QO l O →ₗ[O] QO l O)) := by
      intro m hm
      have h1 : m ∈ KStar.TotallyRealRoots.twistInvOver l O (QO l O) (U.map (cycZ k Ω l)) e := by
        rw [KStar.TotallyRealRoots.mem_twistInvOver]
        rintro u ⟨g, hg, rfl⟩
        have h2 : rho l e ψ g⁻¹ m = m := (mem_riemannRochSpace_iff_regularAt_everywhere _ _).1 hm ⟨g⁻¹, U.inv_mem hg⟩
        have h3 : ψ g = 1 := h hg
        rw [rho_eq, scalRep_apply, MonoidHom.inv_apply, map_inv, inv_inv, Psi, MonoidHom.mul_apply, h3, mul_one,
          zpow_natCast, MonoidHom.pow_apply, Units.val_pow_eq_pow_val] at h2
        exact h2
      rw [KStar.TotallyRealRoots.twistInvOver_eq_torsionBy _ hn.symm, Submodule.mem_torsionBy_iff] at h1
      exact h1
    refine (Module.length_le_of_injective _ (Submodule.inclusion_injective hle)).trans ?_
    rw [(qoFacts l O).2.2.2, IsDiscreteValuationRing.addVal_pow, nsmul_eq_mul, ← hn, hval]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.SumBack
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr

private theorem sumBack_one {ι : Type} (S : Finset ι) (f : ι → ℕ∞) (a : ℕ∞) (b E : ℕ) (hE : E ≠ 0)
    (hf : ∀ i ∈ S, f i ≠ ⊤) (h : a * (E : ℕ∞) ≤ ∑ i ∈ S, (f i + (b : ℕ∞) * (E : ℕ∞))) :
    a ≠ ⊤ ∧ (a.toNat : ℝ) ≤ ∑ i ∈ S, ((f i).toNat : ℝ) / (E : ℝ) + S.card * (b : ℝ) := by
  have hsum : ∑ i ∈ S, (f i + (b : ℕ∞) * (E : ℕ∞)) = ((∑ i ∈ S, ((f i).toNat + b * E) : ℕ) : ℕ∞) := by
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    push_cast
    rw [ENat.coe_toNat (hf i hi)]
  rw [hsum] at h
  have ha : a ≠ ⊤ := by
    rintro rfl
    rw [ENat.top_mul (by exact_mod_cast hE)] at h
    exact absurd h (not_le.2 (ENat.coe_lt_top _))
  refine ⟨ha, ?_⟩
  have h2 : a.toNat * E ≤ ∑ i ∈ S, ((f i).toNat + b * E) := by
    rw [← ENat.coe_toNat ha] at h
    exact_mod_cast h
  have hE' : (0 : ℝ) < E := by exact_mod_cast Nat.pos_of_ne_zero hE
  have h3 : (a.toNat : ℝ) * E ≤ ∑ i ∈ S, (((f i).toNat : ℝ) + b * E) := by exact_mod_cast h2
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at h3
  rw [← Finset.sum_div]
  have h4 : (∑ i ∈ S, ((f i).toNat : ℝ)) / E + S.card * (b : ℝ) = ((∑ i ∈ S, ((f i).toNat : ℝ)) + S.card * ((b : ℝ) * E)) / E := by
    field_simp
  rw [h4, le_div_iff₀ hE']
  exact h3

theorem UpperTheory.V.Chr.sumBack :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (ι : Type) (T : ℕ → Finset ι) (T₀ : Finset ι) (f : ι → ℕ → ℕ∞) (a : ℕ → ℕ∞) (b : ℕ → ℕ) (t : ℕ),
          (∀ e, T e ⊆ T₀) → (∀ e, 0 < e → e < t → (∀ i ∈ T e, f i e ≠ ⊤) ∧ a e * eO l O ≤ ∑ i ∈ T e, (f i e + (b e : ℕ∞) * eO l O)) →
          (∀ e, 0 < e → e < t → a e ≠ ⊤) ∧
            ∑ e ∈ Finset.Ico 1 t, ((a e).toNat : ℝ) ≤ ∑ e ∈ Finset.Ico 1 t, ∑ i ∈ T e, nrm l O (f i e) + T₀.card * ∑ e ∈ Finset.Ico 1 t, (b e : ℝ) := by
  intro l _ O _ _ _ _ _ ι T T₀ f a b t hT h
  obtain ⟨-, -, -, -, -, hne, hle, -, -⟩ := dvrFacts l O
  have htop : eO l O ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top _) hle
  have hEO : eO l O = (((eO l O).toNat : ℕ) : ℕ∞) := (ENat.coe_toNat htop).symm
  have hE : (eO l O).toNat ≠ 0 := by
    intro h0
    apply hne
    rw [hEO, h0]
    rfl
  have key : ∀ e ∈ Finset.Ico 1 t, a e ≠ ⊤ ∧ ((a e).toNat : ℝ) ≤ ∑ i ∈ T e, ((f i e).toNat : ℝ) / ((eO l O).toNat : ℝ) + (T e).card * (b e : ℝ) := by
    intro e he
    rw [Finset.mem_Ico] at he
    obtain ⟨h1, h2⟩ := h e (by omega) he.2
    rw [hEO] at h2
    exact sumBack_one (T e) (fun i => f i e) (a e) (b e) _ hE h1 h2
  refine ⟨fun e he0 het => (key e (Finset.mem_Ico.2 ⟨he0, het⟩)).1, ?_⟩
  have hn : ∀ x, nrm l O x = (x.toNat : ℝ) / ((eO l O).toNat : ℝ) := fun x => rfl
  simp only [hn]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun e he => (key e he).2.trans ?_
  gcongr
  exact hT e
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.FactLeLog
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr

private theorem fact_le_log {l e t : ℕ} (hl : l.Prime) (he : e ≠ 0) (het : e < t) :
    (e.factorization l : ℝ) * Real.log 2 ≤ Real.log t := by
  have h2 : 2 ^ e.factorization l ≤ e :=
    le_trans (Nat.pow_le_pow_left hl.two_le _) (Nat.ordProj_le l he)
  rw [← Real.log_pow]
  apply Real.log_le_log (by positivity)
  exact_mod_cast h2.trans het.le

private theorem nu_sum (l N : ℕ) (hl : l.Prime) : ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℕ, 2 ≤ t →
    ∑ e ∈ Finset.Ico 1 t, (LDataCardLeFinrank.nuBound l N e : ℝ) ≤ C * (t * Real.log t) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨((max (N.factorization l) (if l = 2 then 2 else 1) : ℕ) + 1 : ℝ) / Real.log 2,
    div_nonneg (by positivity) hlog2.le, ?_⟩
  intro t ht
  set M : ℕ := max (N.factorization l) (if l = 2 then 2 else 1) with hM
  have hlogt : Real.log 2 ≤ Real.log t :=
    Real.log_le_log (by norm_num) (by exact_mod_cast ht)
  have hterm : ∀ e ∈ Finset.Ico 1 t,
      (LDataCardLeFinrank.nuBound l N e : ℝ) ≤ ((M : ℝ) + 1) / Real.log 2 * Real.log t := by
    intro e he
    rw [Finset.mem_Ico] at he
    have hv := fact_le_log hl (by omega) he.2
    have hnbN : LDataCardLeFinrank.nuBound l N e ≤ M + e.factorization l := by
      unfold LDataCardLeFinrank.nuBound
      rw [hM]
      split_ifs <;> first | exact le_refl _ | exact Nat.zero_le _
    have hnb : (LDataCardLeFinrank.nuBound l N e : ℝ) ≤ (M : ℝ) + e.factorization l := by
      exact_mod_cast hnbN
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
    calc (LDataCardLeFinrank.nuBound l N e : ℝ) * Real.log 2
        ≤ ((M : ℝ) + e.factorization l) * Real.log 2 :=
          mul_le_mul_of_nonneg_right hnb hlog2.le
      _ = (M : ℝ) * Real.log 2 + (e.factorization l : ℝ) * Real.log 2 := by ring
      _ ≤ (M : ℝ) * Real.log t + Real.log t :=
          add_le_add (mul_le_mul_of_nonneg_left hlogt (by positivity)) hv
      _ = ((M : ℝ) + 1) * Real.log t := by ring
  have hC : 0 ≤ ((M : ℝ) + 1) / Real.log 2 * Real.log t :=
    mul_nonneg (div_nonneg (by positivity) hlog2.le) (hlog2.le.trans hlogt)
  calc ∑ e ∈ Finset.Ico 1 t, (LDataCardLeFinrank.nuBound l N e : ℝ)
      ≤ ∑ e ∈ Finset.Ico 1 t, ((M : ℝ) + 1) / Real.log 2 * Real.log t := Finset.sum_le_sum hterm
    _ = ((t - 1 : ℕ) : ℝ) * (((M : ℝ) + 1) / Real.log 2 * Real.log t) := by
        rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    _ ≤ (t : ℝ) * (((M : ℝ) + 1) / Real.log 2 * Real.log t) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le t 1) hC
    _ = ((M : ℝ) + 1) / Real.log 2 * (t * Real.log t) := by ring

theorem UpperTheory.V.Chr.nuSum :
    (∀ l N : ℕ, l.Prime → ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℕ, 2 ≤ t → ∑ e ∈ Finset.Ico 1 t, (LDataCardLeFinrank.nuBound l N e : ℝ) ≤ C * (t * Real.log t)) ∧
          ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (f a : ℕ → ℕ∞) (b : ℕ → ℕ) (t : ℕ) (B B' : ℝ), (∀ e, 0 < e → e < t → a e ≠ ⊤ ∧ f e ≤ a e * eO l O + (b e : ℕ∞) * eO l O) →
            ∑ e ∈ Finset.Ico 1 t, ((a e).toNat : ℝ) ≤ B → ∑ e ∈ Finset.Ico 1 t, (b e : ℝ) ≤ B' → SumLe l O f t (B + B') := by
  refine ⟨nu_sum, ?_⟩
  intro l _ O _ _ _ _ _ f a b t B B' h hB hB'
  obtain ⟨-, -, -, -, -, hne0, hle, -, -⟩ := dvrFacts l O
  have hfin : eO l O ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top _) hle
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfin
  have hn0 : (n : ℝ) ≠ 0 := by
    have : n ≠ 0 := by
      rintro rfl
      exact hne0 (by rw [← hn]; rfl)
    exact_mod_cast this
  apply SumLe.mono l (g := fun e => a e * eO l O + (b e : ℕ∞) * eO l O)
  · refine ⟨fun e h0 ht => ?_, ?_⟩
    · obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (h e h0 ht).1
      show a e * eO l O + (b e : ℕ∞) * eO l O ≠ ⊤
      rw [← hm, ← hn]
      exact_mod_cast ENat.coe_ne_top (m * n + b e * n)
    · calc ∑ e ∈ Finset.Ico 1 t, nrm l O (a e * eO l O + (b e : ℕ∞) * eO l O)
          = ∑ e ∈ Finset.Ico 1 t, (((a e).toNat : ℝ) + (b e : ℝ)) := by
            apply Finset.sum_congr rfl
            intro e he
            rw [Finset.mem_Ico] at he
            obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (h e (by omega) he.2).1
            unfold nrm
            rw [← hm, ← hn]
            rw [show (m : ℕ∞) * (n : ℕ∞) + ((b e : ℕ) : ℕ∞) * (n : ℕ∞) = ((m * n + b e * n : ℕ) : ℕ∞) by
              push_cast; rfl]
            rw [ENat.toNat_coe, ENat.toNat_coe, ENat.toNat_coe]
            push_cast
            field_simp
        _ = ∑ e ∈ Finset.Ico 1 t, ((a e).toNat : ℝ) + ∑ e ∈ Finset.Ico 1 t, (b e : ℝ) :=
            Finset.sum_add_distrib
        _ ≤ B + B' := add_le_add hB hB'
  · intro e h0 ht
    exact (h e h0 ht).2
end
