module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IsClassFieldHilbert
public import CompanionTheory.AutomorphicTheory.PlaceSeparation.ArtinA
public import GroundTheory.GlobalFields.TateThesis.Chebotarev
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.CycInertia

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IneAbs
open NumberField IsDedekindDomain IntermediateField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

theorem UpperTheory.V.CF.ineAbs :
    ∀ (K L Ω : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω] [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsAlgClosure K Ω] [IsGalois K L] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 L)), IsPlaceOver A w → (Ine (F := K) A).map (resTo K L Ω) = w.asIdeal.inertia Gal(L/K) := by
  intro K L Ω _ _ _ _ _ _ _ _ _ _ _ A w hw
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  haveI : Algebra.IsAlgebraic L Ω := Algebra.IsAlgebraic.tower_top (K := K) L
  haveI : IsAlgClosure L Ω := ⟨inferInstance, inferInstance⟩
  ext τ
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    exact CompanionTheory.FamInh.res_mem_inertia hw hσ
  · intro hτ
    exact CompanionTheory.FamInh.exists_lift_ine hw hτ
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IneCard
open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

theorem UpperTheory.V.CF.ineCard :
    (∀ (k L : Type) [Field k] [NumberField k] [Field L] [NumberField L] [Algebra k L] [IsGalois k L] (w : HeightOneSpectrum (𝓞 L)), Nat.card (w.asIdeal.inertia Gal(L/k)) = w.asIdeal.ramificationIdx (𝓞 k)) ∧ ∀ (L : Type) [Field L] [NumberField L] [IsGalois ℚ L] (w : HeightOneSpectrum (𝓞 L)), Nat.card (w.asIdeal.inertia Gal(L/ℚ)) = w.asIdeal.ramificationIdx ℤ := by
  refine ⟨fun k L _ _ _ _ _ _ w => ?_, fun L _ _ _ w => ?_⟩
  · rw [Ideal.card_inertia_eq_ramificationIdxIn (w.asIdeal.under (𝓞 k)) w.asIdeal,
      Ideal.ramificationIdxIn_eq_ramificationIdx (w.asIdeal.under (𝓞 k)) w.asIdeal Gal(L/k)]
  · rw [Ideal.card_inertia_eq_ramificationIdxIn (w.asIdeal.under ℤ) w.asIdeal,
      Ideal.ramificationIdxIn_eq_ramificationIdx (w.asIdeal.under ℤ) w.asIdeal Gal(L/ℚ)]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.ExistsQuadraticGaussSum
open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

private theorem UpperTheory.V.CF.exists_quadratic_gauss_sum {K : Type} [Field K] [CharZero K] {d : ℕ} [hd : Fact d.Prime]
    (hd2 : d ≠ 2) {ζ : K} (hζ : IsPrimitiveRoot ζ d) :
    ∃ G : K, G ^ 2 = (pStar d : ℤ) ∧ G ∈ ℚ⟮ζ⟯ ∧ ∀ (σ : K →+* K) (a : ℕ), σ ζ = ζ ^ a →
      σ G = (legendreSym d a : ℤ) * G := by
  classical
  haveI : NeZero d := ⟨hd.out.ne_zero⟩
  have hζd : ζ ^ d = 1 := hζ.pow_eq_one
  let χ : MulChar (ZMod d) K := (quadraticChar (ZMod d)).ringHomComp (Int.castRingHom K)
  let ψ : AddChar (ZMod d) K := AddChar.zmodChar d hζd
  have hψp : ψ.IsPrimitive := AddChar.zmodChar_primitive_of_primitive_root d hζ
  have hchar : ringChar (ZMod d) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hd2
  have hχ1 : χ ≠ 1 :=
    (MulChar.ringHomComp_ne_one_iff (f := Int.castRingHom K) Int.cast_injective).2
      (quadraticChar_ne_one hchar)
  have hχq : χ.IsQuadratic := (quadraticChar_isQuadratic (ZMod d)).comp _
  have hχa : ∀ a : ZMod d, χ a = ((quadraticChar (ZMod d) a : ℤ) : K) := fun a => by
    simp [χ, MulChar.ringHomComp_apply]
  have hψa : ∀ n : ℕ, ψ (n : ZMod d) = ζ ^ n := fun n => AddChar.zmodChar_apply' hζd n
  refine ⟨gaussSum χ ψ, ?_, ?_, ?_⟩
  · rw [gaussSum_sq hχ1 hχq hψp, hχa, ZMod.card]
    have h1 : quadraticChar (ZMod d) (-1) = legendreSym d (-1) := by
      simp [legendreSym]
    rw [h1, legendreSym.at_neg_one hd2, ZMod.χ₄_nat_eq_if_mod_four, pStar]
    have hodd : d % 2 = 1 := hd.out.eq_two_or_odd.resolve_left hd2
    have h4 : d % 4 = 1 ∨ d % 4 = 3 := by omega
    rcases h4 with h4 | h4
    · have he : Even (d / 2) := by rw [Nat.even_iff]; omega
      simp [hodd, h4, he.neg_one_pow]
    · have ho : Odd (d / 2) := by rw [Nat.odd_iff]; omega
      simp [hodd, h4, ho.neg_one_pow]
  · unfold gaussSum
    refine IntermediateField.sum_mem _ fun a _ => IntermediateField.mul_mem _ ?_ ?_
    · rw [hχa]; exact IntermediateField.intCast_mem _ _
    · rw [← ZMod.natCast_zmod_val a, hψa]
      exact pow_mem (IntermediateField.mem_adjoin_simple_self ℚ ζ) _
  · intro σ b hσ
    have hG : σ (gaussSum χ ψ) = gaussSum χ (ψ.mulShift (b : ZMod d)) := by
      unfold gaussSum
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [map_mul, hχa, map_intCast, AddChar.mulShift_apply]
      congr 1
      rw [← ZMod.natCast_zmod_val a, hψa, map_pow, hσ, ← pow_mul, ← Nat.cast_mul, hψa]
    have hb : (b : ZMod d) ≠ 0 := by
      intro h0
      have h1 : σ ζ = 1 := by
        rw [hσ]
        rw [ZMod.natCast_eq_zero_iff] at h0
        obtain ⟨k, rfl⟩ := h0
        rw [pow_mul, hζd, one_pow]
      have h2 : ζ = 1 := σ.injective (by rw [h1, map_one])
      exact hζ.ne_one hd.out.one_lt h2
    have hmul : χ (b : ZMod d) * gaussSum χ (ψ.mulShift (b : ZMod d)) = gaussSum χ ψ :=
      gaussSum_mulShift χ ψ (Units.mk0 _ hb)
    have hu2 : χ (b : ZMod d) * χ (b : ZMod d) = 1 := by
      rw [hχa, ← Int.cast_mul, ← sq, quadraticChar_sq_one hb, Int.cast_one]
    have hleg : ((legendreSym d b : ℤ) : K) = χ (b : ZMod d) := by
      rw [hχa]; simp [legendreSym]
    rw [hG, hleg, ← hmul, ← mul_assoc, hu2, one_mul]

theorem UpperTheory.V.CF.gauss :
    ∀ (K : Type) [Field K] [CharZero K] (p : ℕ) [Fact p.Prime] (ζ : K), p ≠ 2 → IsPrimitiveRoot ζ p → (∃ x : K, x ^ 2 = (pStar p : ℤ)) ∧ ∀ x : K, x ^ 2 = (pStar p : ℤ) → x ∈ ℚ⟮ζ⟯ ∧ ∀ (σ : K →+* K) (b : ℕ), σ ζ = ζ ^ b → σ x = (legendreSym p b : ℤ) * x := by
  intro K _ _ p _ ζ hp hζ
  obtain ⟨G, hG, hmem, hσ⟩ := UpperTheory.V.CF.exists_quadratic_gauss_sum hp hζ
  refine ⟨⟨G, hG⟩, fun x hx => ?_⟩
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hx.trans hG.symm) with rfl | rfl
  · exact ⟨hmem, hσ⟩
  · refine ⟨neg_mem hmem, fun σ b h => ?_⟩
    rw [map_neg, hσ σ b h, mul_neg]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.UnramIff
open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

theorem UpperTheory.V.CF.unramIff :
    (∀ (L : Type) [Field L] [NumberField L] [IsGalois ℚ L] (p : ℕ), p.Prime → (UnramAt L p ↔ ∀ w : HeightOneSpectrum (𝓞 L), (p : 𝓞 L) ∈ w.asIdeal → w.asIdeal.inertia Gal(L/ℚ) = ⊥)) ∧ (∀ (L : Type) [Field L] [NumberField L] (p : ℕ), p.Prime → (UnramAt L p ↔ ¬ (p : ℤ) ∣ NumberField.discr L)) ∧ ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (p : ℕ), p.Prime → UnramAt L p → UnramAt K p := by
  have h2 : ∀ (L : Type) [Field L] [NumberField L] (p : ℕ), p.Prime →
      (UnramAt L p ↔ ¬ (p : ℤ) ∣ NumberField.discr L) := by
    intro L _ _ p hp
    have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    rw [NumberField.not_dvd_discr_iff_forall_mem L (𝓞 L) hpZ]
    unfold UnramAt
    refine forall_congr' fun P => forall_congr' fun hP => ?_
    haveI := hP
    rw [Int.cast_natCast, Ideal.ramificationIdx_eq_one_iff]
  refine ⟨?_, h2, ?_⟩
  · intro L _ _ _ p hp
    unfold UnramAt
    constructor
    · intro h w hw
      haveI := w.isPrime
      rw [← Subgroup.card_eq_one,
        Ideal.card_inertia_eq_ramificationIdxIn (w.asIdeal.under ℤ) w.asIdeal,
        Ideal.ramificationIdxIn_eq_ramificationIdx (w.asIdeal.under ℤ) w.asIdeal Gal(L/ℚ)]
      exact h w.asIdeal w.isPrime hw
    · intro h P hP hpP
      haveI := hP
      have hne : P ≠ ⊥ := by
        intro hb
        rw [hb, Ideal.mem_bot] at hpP
        exact hp.ne_zero (by exact_mod_cast hpP)
      have hw := h ⟨P, hP, hne⟩ hpP
      rw [← Subgroup.card_eq_one,
        Ideal.card_inertia_eq_ramificationIdxIn (P.under ℤ) P,
        Ideal.ramificationIdxIn_eq_ramificationIdx (P.under ℤ) P Gal(L/ℚ)] at hw
      exact hw
  · intro K L _ _ _ _ _ p hp hL
    exact (h2 K p hp).2 fun hd => (h2 L p hp).1 hL (hd.trans (NumberField.discr_dvd_discr K L))
end
