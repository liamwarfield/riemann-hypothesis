module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PlaceBasic
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

namespace UpperTheory.V.ML.PlaceBasics

section Rat

variable (l : ℕ) [hl : Fact l.Prime]

private theorem prime_l : Prime ((l : ℕ) : 𝓞 ℚ) := by
  have h : Prime ((l : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp hl.out
  have e : ((l : ℕ) : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm ((l : ℕ) : ℤ) := by simp
  rw [e]
  exact (MulEquiv.prime_iff Rat.ringOfIntegersEquiv.symm.toMulEquiv).mpr h

private noncomputable def vQ : HeightOneSpectrum (𝓞 ℚ) where
  asIdeal := Ideal.span {((l : ℕ) : 𝓞 ℚ)}
  isPrime := (Ideal.span_singleton_prime (prime_l l).ne_zero).mpr (prime_l l)
  ne_bot := by rw [Ne, Ideal.span_singleton_eq_bot]; exact (prime_l l).ne_zero

private theorem normV_vQ : normV (vQ l) = l := by
  have h : normV (vQ l) = Ideal.absNorm (vQ l).asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
  rw [h]
  show Ideal.absNorm (Ideal.span {((l : ℕ) : 𝓞 ℚ)}) = l
  rw [Ideal.absNorm_span_natCast, NumberField.RingOfIntegers.rank]
  simp

private theorem mem_vQ : ((l : ℕ) : 𝓞 ℚ) ∈ (vQ l).asIdeal := Ideal.mem_span_singleton_self _

variable {l} {Ω : Type} [Field Ω]

private theorem intCast_mem_vQ (n : ℤ) : ((n : ℤ) : 𝓞 ℚ) ∈ (vQ l).asIdeal ↔ ((l : ℕ) : ℤ) ∣ n := by
  show ((n : ℤ) : 𝓞 ℚ) ∈ Ideal.span {((l : ℕ) : 𝓞 ℚ)} ↔ _
  rw [Ideal.mem_span_singleton]
  have e1 : ((l : ℕ) : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm ((l : ℕ) : ℤ) := by simp
  have e2 : ((n : ℤ) : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm n := by simp
  rw [e1, e2]
  exact map_dvd_iff Rat.ringOfIntegersEquiv.symm

private theorem val_intCast_le_one (A : ValuationSubring Ω) (n : ℤ) : A.valuation (n : Ω) ≤ 1 :=
  (A.valuation_le_one_iff _).mpr (intCast_mem A n)

private theorem not_of_coprime (A : ValuationSubring Ω) {m n : ℤ} (hc : IsCoprime m n)
    (hm : A.valuation (m : Ω) < 1) : ¬ A.valuation (n : Ω) < 1 := by
  intro h
  obtain ⟨a, b, hab⟩ := hc
  have h1 : A.valuation ((a : Ω) * (m : Ω) + (b : Ω) * (n : Ω)) < 1 := by
    refine Valuation.map_add_lt _ ?_ ?_
    · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (val_intCast_le_one A a)) hm
    · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (val_intCast_le_one A b)) h
  have h2 : (a : Ω) * (m : Ω) + (b : Ω) * (n : Ω) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → Ω) hab
  rw [h2, map_one] at h1
  exact lt_irrefl _ h1

private theorem val_intCast_lt_one_iff (A : ValuationSubring Ω) (hA : A.valuation ((l : ℕ) : Ω) < 1) (n : ℤ) :
    A.valuation (n : Ω) < 1 ↔ ((l : ℕ) : ℤ) ∣ n := by
  constructor
  · intro h
    by_contra hnd
    exact not_of_coprime A (((Nat.prime_iff_prime_int.mp hl.out).coprime_iff_not_dvd).mpr hnd)
      (by rwa [Int.cast_natCast]) h
  · rintro ⟨k, rfl⟩
    push_cast
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (val_intCast_le_one A k)) hA

private theorem isPlaceOver_vQ [Algebra ℚ Ω] (A : ValuationSubring Ω) (hA : A.valuation ((l : ℕ) : Ω) < 1) :
    IsPlaceOver (F := ℚ) A (vQ l) := by
  intro x
  obtain ⟨n, rfl⟩ : ∃ n : ℤ, x = ((n : ℤ) : 𝓞 ℚ) :=
    ⟨Rat.ringOfIntegersEquiv x, by
      have := Rat.ringOfIntegersEquiv.symm_apply_apply x
      rw [← this]; simp⟩
  rw [intCast_mem_vQ, ← val_intCast_lt_one_iff A hA]
  simp

end Rat

section Roots

variable {Ω : Type} [Field Ω] (A : ValuationSubring Ω)

private theorem val_root {m : ℕ} (hv : ¬ A.valuation (m : Ω) < 1) {ζ : Ω} (h : ζ ^ m = 1) : A.valuation ζ = 1 := by
  have hm : m ≠ 0 := by
    rintro rfl
    exact hv (by simp)
  have h1 : A.valuation ζ ^ m = 1 := by rw [← map_pow, h, map_one]
  exact (pow_eq_one_iff_left hm).1 h1

private theorem one_sub_pow {η : Ω} (h1 : A.valuation η = 1) (h : A.valuation (η - 1) < 1) (i : ℕ) :
    A.valuation (1 - η ^ i) < 1 := by
  induction i with
  | zero => simp
  | succ i ih =>
    have e : 1 - η ^ (i + 1) = η * (1 - η ^ i) - (η - 1) := by ring
    rw [e]
    refine A.valuation.map_sub_lt ?_ h
    rw [map_mul, h1, one_mul]; exact ih

private theorem root_eq_one {m : ℕ} (hv : ¬ A.valuation (m : Ω) < 1) {η : Ω} (hη : η ^ m = 1)
    (h : A.valuation (η - 1) < 1) : η = 1 := by
  by_contra hne
  apply hv
  have hs : ∑ i ∈ Finset.range m, η ^ i = 0 := by
    have := mul_geom_sum η m
    rw [hη, sub_self] at this
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)
  have e : (m : Ω) = ∑ i ∈ Finset.range m, (1 - η ^ i) := by
    rw [Finset.sum_sub_distrib, hs]; simp
  rw [e]
  exact A.valuation.map_sum_lt one_ne_zero fun i _ => one_sub_pow A (val_root A hv hη) h i

private theorem root_eq {m : ℕ} (hv : ¬ A.valuation (m : Ω) < 1) {ξ ζ : Ω} (hξ : ξ ^ m = 1) (hζ : ζ ^ m = 1)
    (h : A.valuation (ξ - ζ) < 1) : ξ = ζ := by
  have h1 := val_root A hv hζ
  have h0 : ζ ≠ 0 := by
    rintro rfl
    simp at h1
  have e : ξ / ζ - 1 = (ξ - ζ) / ζ := by field_simp
  have : ξ / ζ = 1 := by
    refine root_eq_one A hv (by rw [div_pow, hξ, hζ, div_one]) ?_
    rw [e, map_div₀, h1, div_one]; exact h
  exact (div_eq_one_iff_eq h0).1 this

end Roots

section Conj

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) (g : G ℚ Ω)

private theorem smul_mem (y : Ω) : g y ∈ g • A ↔ y ∈ A := by
  rw [← AlgEquiv.smul_def]
  exact ValuationSubring.smul_mem_pointwise_smul_iff

private theorem smul_le (y : Ω) : (g • A).valuation (g y) ≤ 1 ↔ A.valuation y ≤ 1 := by
  rw [ValuationSubring.valuation_le_one_iff, ValuationSubring.valuation_le_one_iff, smul_mem]

private theorem smul_lt (y : Ω) : (g • A).valuation (g y) < 1 ↔ A.valuation y < 1 := by
  rw [valuation_lt_one_iff', valuation_lt_one_iff', smul_mem, ← map_inv₀, smul_mem, map_eq_zero_iff _ g.injective]

private theorem smul_eq (y : Ω) : (g • A).valuation (g y) = 1 ↔ A.valuation y = 1 := by
  rw [eq_iff_le_not_lt, eq_iff_le_not_lt, smul_le, smul_lt]

private theorem dec_iff (x : G ℚ Ω) : x ∈ Dec (F := ℚ) (g • A) ↔ g⁻¹ * x * g ∈ Dec (F := ℚ) A := by
  rw [mem_Dec, mem_Dec, mul_smul, mul_smul, inv_smul_eq_iff]

private theorem pow_iff (x : G ℚ Ω) (q : ℕ) :
    (∀ y : Ω, (g • A).valuation y ≤ 1 → (g • A).valuation (x y - y ^ q) < 1) ↔
      ∀ y : Ω, A.valuation y ≤ 1 → A.valuation ((g⁻¹ * x * g) y - y ^ q) < 1 := by
  rw [g.surjective.forall]
  refine forall_congr' fun y => ?_
  have e : x (g y) - g y ^ q = g ((g⁻¹ * x * g) y - y ^ q) := by
    rw [map_sub, map_pow, ← AlgEquiv.mul_apply g, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul,
      AlgEquiv.mul_apply]
  rw [e, smul_le, smul_lt]

end Conj

end UpperTheory.V.ML.PlaceBasics

open UpperTheory.V.ML.PlaceBasics in
theorem UpperTheory.V.ML.placeBasic :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω],
    (∀ q : ℕ, q.Prime → ∃ A : ValuationSubring Ω, Over A q) ∧
    (∀ (A : ValuationSubring Ω) (q : ℕ), q.Prime → Over A q → ∃ φ : G ℚ Ω, IsFrob (F := ℚ) A q φ) ∧
    (∀ (A : ValuationSubring Ω) (m n : ℕ), Over A (m * n) ↔ Over A m ∨ Over A n) ∧
    (∀ (A : ValuationSubring Ω) (m n : ℕ), m.Coprime n → Over A m → ¬ Over A n) ∧
    (∀ (A : ValuationSubring Ω) (k : ℕ), ¬ Over A k → Ine (F := ℚ) A ≤ fixMu ℚ Ω k) ∧
    (∀ (A : ValuationSubring Ω) (k : ℕ) (ζ : Ω), ¬ Over A k → ζ ^ k = 1 → A.valuation (ζ - 1) < 1 → ζ = 1) ∧
    (∀ (A : ValuationSubring Ω) (q k : ℕ) (φ : G ℚ Ω), IsFrob (F := ℚ) A q φ → ¬ Over A k → Pows k q φ) ∧
    (∀ (A A' : ValuationSubring Ω) (q : ℕ), q.Prime → Over A q → Over A' q → ∃ g : G ℚ Ω, A' = g • A) ∧
    (∀ (A : ValuationSubring Ω) (q : ℕ), q.Prime → Over A q → ∃ v : HeightOneSpectrum (𝓞 ℚ), IsPlaceOver A v ∧ normV v = q ∧ (q : 𝓞 ℚ) ∈ v.asIdeal) ∧
    ∀ (A : ValuationSubring Ω) (g : G ℚ Ω), (∀ x, x ∈ Dec (F := ℚ) (g • A) ↔ g⁻¹ * x * g ∈ Dec (F := ℚ) A) ∧ (∀ x, x ∈ Ine (F := ℚ) (g • A) ↔ g⁻¹ * x * g ∈ Ine (F := ℚ) A) ∧
      (∀ q x, IsFrob (F := ℚ) (g • A) q x ↔ IsFrob (F := ℚ) A q (g⁻¹ * x * g)) ∧ (∀ y : Ω, (g • A).valuation (g y) < 1 ↔ A.valuation y < 1) ∧ ∀ y : Ω, (g • A).valuation (g y) = 1 ↔ A.valuation y = 1 := by
  intro Ω _ _ _
  refine ⟨fun q hq => ?_, fun A q hq hA => ?_, fun A m n => ?_, fun A m n hc hm => ?_, fun A k hk g hg x hx => ?_,
    fun A k ζ hk hζ h => root_eq_one A hk hζ h, fun A q k φ hφ hk x hx => ?_, fun A A' q hq hA hA' => ?_,
    fun A q hq hA => ?_, fun A g => ⟨dec_iff A g, fun x => ?_, fun q x => and_congr (dec_iff A g x) (pow_iff A g x q),
      smul_lt A g, smul_eq A g⟩⟩
  · haveI := Fact.mk hq
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω (vQ q)
    refine ⟨A, ?_⟩
    simpa using (hA ((q : ℕ) : 𝓞 ℚ)).2 (mem_vQ q)
  · haveI := Fact.mk hq
    obtain ⟨g, hg⟩ := exists_isFrob (isPlaceOver_vQ A hA)
    rw [normV_vQ] at hg
    exact ⟨g, hg⟩
  · have hm : A.valuation (m : Ω) ≤ 1 := by simpa using val_intCast_le_one A m
    have hn : A.valuation (n : Ω) ≤ 1 := by simpa using val_intCast_le_one A n
    simp only [Over, Nat.cast_mul, map_mul]
    refine ⟨fun h => ?_, fun h => h.elim (lt_of_le_of_lt (mul_le_of_le_one_right' hn))
      (lt_of_le_of_lt (mul_le_of_le_one_left' hm))⟩
    by_contra h'
    rw [not_or] at h'
    rw [hm.eq_of_not_lt h'.1, hn.eq_of_not_lt h'.2, one_mul] at h
    exact lt_irrefl _ h
  · have := not_of_coprime A (Nat.isCoprime_iff_coprime.2 hc) (by rwa [Int.cast_natCast])
    rwa [Int.cast_natCast] at this
  · exact root_eq A hk (by rw [← map_pow, hx, map_one]) hx (hg.2 x (val_root A hk hx).le)
  · exact root_eq A hk (by rw [← map_pow, hx, map_one]) (by rw [← pow_mul, mul_comm, pow_mul, hx, one_pow])
      (hφ.2 x (val_root A hk hx).le)
  · haveI := Fact.mk hq
    obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver (F := ℚ) (isPlaceOver_vQ A hA) (isPlaceOver_vQ A' hA')
    exact ⟨g, hg.symm⟩
  · haveI := Fact.mk hq
    exact ⟨vQ q, isPlaceOver_vQ A hA, normV_vQ q, mem_vQ q⟩
  · have h := pow_iff A g x 1
    simp only [pow_one] at h
    exact and_congr (dec_iff A g x) h
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.QocEquiv
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise TensorProduct

section

variable (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O]
  [Module.Finite ℤ_[l] O]

private theorem qoc_inj : Function.Injective (algebraMap ℤ_[l] O) := by
  have hl : (l : O) ≠ 0 := by
    intro h0
    have hz : ∀ t : O ⊗[ℤ_[l]] (ℚ_[l] ⧸ ZlSub l), t = 0 := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => rfl
      | tmul o q =>
        obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ q
        have hlq : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
        have hr : (Submodule.Quotient.mk r : ℚ_[l] ⧸ ZlSub l) =
            (l : ℤ_[l]) • Submodule.Quotient.mk (r / l) := by
          rw [← Submodule.Quotient.mk_smul]
          congr 1
          rw [Algebra.smul_def, map_natCast, mul_div_cancel₀ _ hlq]
        rw [hr, ← TensorProduct.smul_tmul, Algebra.smul_def, map_natCast, h0, zero_mul,
          TensorProduct.zero_tmul]
      | add x y hx hy => rw [hx, hy, add_zero]
    haveI : Subsingleton (QO l O) := ⟨fun x y => (hz x).trans (hz y).symm⟩
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
    have h4 := (UpperTheory.V.Base.qoFacts l O).2.2.2 ϖ
    rw [IsDiscreteValuationRing.addVal_uniformizer hϖ, Module.length_eq_zero] at h4
    exact zero_ne_one h4
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra hne
  rw [PadicInt.unitCoeff_spec hne, map_mul, map_pow, map_natCast] at hx
  rcases mul_eq_zero.mp hx with h | h
  · exact ((PadicInt.unitCoeff hne).isUnit.map (algebraMap ℤ_[l] O)).ne_zero h
  · exact hl ((pow_eq_zero_iff' (M₀ := O)).mp h).1

private theorem qoc_ann (w : QO l O) : ∃ a : O, a ≠ 0 ∧ ∀ y : O, y • w = 0 ↔ a ∣ y := by
  obtain ⟨n, hn⟩ := (UpperTheory.V.Base.qoFacts l O).2.1 w
  set I : Ideal O := LinearMap.ker (LinearMap.toSpanSingleton O (QO l O) w) with hI
  have key : ∀ y : O, y • w = 0 ↔ Submodule.IsPrincipal.generator I ∣ y := by
    intro y
    rw [← Ideal.mem_span_singleton, Ideal.span_singleton_generator, hI, LinearMap.mem_ker,
      LinearMap.toSpanSingleton_apply]
  refine ⟨Submodule.IsPrincipal.generator I, ?_, key⟩
  intro h0
  have h1 : ((l : O) ^ n) • w = 0 := by
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
    exact hn
  rw [key, h0, zero_dvd_iff] at h1
  have hl : (l : O) ≠ 0 := by
    intro h
    apply (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero : (l : ℤ_[l]) ≠ 0)
    apply qoc_inj l O
    rw [map_natCast, map_zero]
    exact h
  exact hl ((pow_eq_zero_iff' (M₀ := O)).mp h1).1

private theorem qoc_ex (a : O) (ha : a ≠ 0) : ∃ w : QO l O, ∀ y : O, y • w = 0 ↔ a ∣ y := by
  by_cases hu : IsUnit a
  · exact ⟨0, fun y => by simp [hu.dvd]⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hϖa : ϖ ∣ a := by
    rw [← IsDiscreteValuationRing.addVal_le_iff_dvd, IsDiscreteValuationRing.addVal_uniformizer hϖ]
    rw [← IsDiscreteValuationRing.addVal_eq_zero_iff] at hu
    exact ENat.one_le_iff_ne_zero.mpr hu
  obtain ⟨b, rfl⟩ := hϖa
  have hb : b ≠ 0 := right_ne_zero_of_mul ha
  have hT : Module.length O (LinearMap.ker (ϖ • LinearMap.id : QO l O →ₗ[O] QO l O)) = 1 := by
    rw [(UpperTheory.V.Base.qoFacts l O).2.2.2 ϖ, IsDiscreteValuationRing.addVal_uniformizer hϖ]
  have hnt : Nontrivial (LinearMap.ker (ϖ • LinearMap.id : QO l O →ₗ[O] QO l O)) := by
    rw [← Module.length_pos_iff (R := O), hT]
    exact zero_lt_one
  obtain ⟨z, hz⟩ := exists_ne (0 : LinearMap.ker (ϖ • LinearMap.id : QO l O →ₗ[O] QO l O))
  have hz1 : ϖ • (z : QO l O) = 0 := LinearMap.mem_ker.mp z.2
  have hz2 : (z : QO l O) ≠ 0 := fun h => hz (Subtype.ext h)
  obtain ⟨w, hw⟩ := (UpperTheory.V.Base.qoFacts l O).2.2.1 b hb (z : QO l O)
  obtain ⟨c, hc, hC⟩ := qoc_ann l O w
  refine ⟨w, fun y => ?_⟩
  have hca : c ∣ ϖ * b := (hC _).mp (by rw [mul_smul, hw, hz1])
  have hcb : ¬ c ∣ b := fun h => hz2 (by rw [← hw]; exact (hC b).mpr h)
  have hac : ϖ * b ∣ c := by
    rw [← IsDiscreteValuationRing.addVal_le_iff_dvd] at hca hcb ⊢
    rw [IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_uniformizer hϖ, add_comm]
    exact Order.add_one_le_of_lt (not_le.mp hcb)
  rw [hC y]
  exact ⟨fun h => hac.trans h, fun h => hca.trans h⟩

private theorem length_quotient_span_eq_addVal' {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (a : R) (ha : a ≠ 0) :
    Module.length R (R ⧸ Ideal.span {a}) = IsDiscreteValuationRing.addVal R a := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  rw [Ideal.span_singleton_mul_left_unit u.isUnit, ← Ideal.span_singleton_pow, ← hϖ.maximalIdeal_eq,
    IsDiscreteValuationRing.length_quotient_pow_maximalIdeal, IsDiscreteValuationRing.addVal_mul,
    IsDiscreteValuationRing.addVal_eq_zero_iff.mpr u.isUnit, zero_add,
    IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_uniformizer hϖ, nsmul_one]

private theorem qoc_gen (a : O) (w : QO l O) (ha : a ≠ 0) (h : ∀ y : O, y • w = 0 ↔ a ∣ y) (w' : QO l O)
    (h' : a • w' = 0) : ∃ y : O, w' = y • w := by
  set T := LinearMap.ker (a • LinearMap.id : QO l O →ₗ[O] QO l O) with hT
  have hTlen : Module.length O T = IsDiscreteValuationRing.addVal O a :=
    (UpperTheory.V.Base.qoFacts l O).2.2.2 a
  have hfin : Module.length O T ≠ ⊤ := by
    rw [hTlen, Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
    exact ha
  have hwT : w ∈ T := by simp [hT, (h a).mpr dvd_rfl]
  let g : O →ₗ[O] T := LinearMap.toSpanSingleton O T ⟨w, hwT⟩
  have hker : LinearMap.ker g = Ideal.span {a} := by
    ext y
    rw [LinearMap.mem_ker, Ideal.mem_span_singleton, ← h y]
    simp [g, Subtype.ext_iff]
  have hrange : Module.length O (LinearMap.range g) = Module.length O T := by
    rw [← (LinearMap.quotKerEquivRange g).length_eq, hker, length_quotient_span_eq_addVal' a ha, hTlen]
  have htop : LinearMap.range g = ⊤ := by
    have hfl : IsFiniteLength O T := Module.length_ne_top_iff.mp hfin
    haveI := (isFiniteLength_iff_isNoetherian_isArtinian.mp hfl).1
    haveI := (isFiniteLength_iff_isNoetherian_isArtinian.mp hfl).2
    by_contra hne
    have hlt := Submodule.length_lt hne
    rw [hrange] at hlt
    exact lt_irrefl _ hlt
  have hw'T : w' ∈ T := by simp [hT, h']
  have hmem : (⟨w', hw'T⟩ : T) ∈ LinearMap.range g := by
    rw [htop]
    exact Submodule.mem_top
  obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hmem
  exact ⟨y, by simpa [g] using (congrArg Subtype.val hy).symm⟩

end

theorem UpperTheory.V.ML.qoCyc :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O],
    (∀ w : QO l O, ∃ a : O, a ≠ 0 ∧ ∀ y : O, y • w = 0 ↔ a ∣ y) ∧ (∀ a : O, a ≠ 0 → ∃ w : QO l O, ∀ y : O, y • w = 0 ↔ a ∣ y) ∧
    (∀ (a : O) (w : QO l O), a ≠ 0 → (∀ y : O, y • w = 0 ↔ a ∣ y) → ∀ w' : QO l O, a • w' = 0 → ∃ y : O, w' = y • w) ∧
    (∀ w w' : QO l O, (∃ y : O, w' = y • w) ∨ ∃ y : O, w = y • w') ∧
    ∀ (V : Type) [AddCommGroup V] [Module O V] (f : V →ₗ[O] QO l O) (y : O), (∀ v, y • f v = 0) → Module.length O V ≤ Module.length O (LinearMap.ker f) + IsDiscreteValuationRing.addVal O y := by
  intro l _ O _ _ _ _ _
  refine ⟨qoc_ann l O, qoc_ex l O, fun a w ha h w' h' => qoc_gen l O a w ha h w' h', ?_, ?_⟩
  · intro w w'
    obtain ⟨a, ha, hA⟩ := qoc_ann l O w
    obtain ⟨b, hb, hB⟩ := qoc_ann l O w'
    rcases le_total (IsDiscreteValuationRing.addVal O a) (IsDiscreteValuationRing.addVal O b) with hab | hab
    · rw [IsDiscreteValuationRing.addVal_le_iff_dvd] at hab
      right
      exact qoc_gen l O b w' hb hB w ((hA b).mpr hab)
    · rw [IsDiscreteValuationRing.addVal_le_iff_dvd] at hab
      left
      exact qoc_gen l O a w ha hA w' ((hB a).mpr hab)
  · intro V _ _ f y hy
    have hle : LinearMap.range f ≤ LinearMap.ker (y • LinearMap.id : QO l O →ₗ[O] QO l O) := by
      rintro _ ⟨v, rfl⟩
      simp [hy v]
    rw [Module.length_eq_add_of_exact (LinearMap.ker f).subtype (LinearMap.ker f).mkQ
      (Submodule.subtype_injective _) (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _),
      (LinearMap.quotKerEquivRange f).length_eq, ← (UpperTheory.V.Base.qoFacts l O).2.2.2 y]
    exact add_le_add le_rfl
      (Module.length_le_of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle))
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.AdmProd
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

theorem UpperTheory.V.ML.isCrys_isDR_prod :
    ∀ (l F r : ℕ) (L : List ℕ), AdmL l F r L → admitted l F r L.prod ∧ L.prod ≠ 0 ∧ (∀ q, AdmL l F r (q :: L) → q.Coprime L.prod) ∧ ∀ q, AdmL l F r (q :: L) → AdmL l F r L := by
  intro l F r L hL
  induction L with
  | nil =>
    refine ⟨⟨squarefree_one, fun q hq hd => absurd (Nat.eq_one_of_dvd_one hd) hq.ne_one⟩, by simp, fun q _ => by simp, fun q _ => ⟨List.nodup_nil, by simp⟩⟩
  | cons a L ih =>
    have tail : ∀ (b : ℕ) (M : List ℕ), AdmL l F r (b :: M) → AdmL l F r M := fun b M h =>
      ⟨(List.nodup_cons.mp h.1).2, fun q hq => h.2 q (List.mem_cons_of_mem b hq)⟩
    obtain ⟨hA, hne, hcop, -⟩ := ih (tail a L hL)
    have haP : AdmP l F r a := hL.2 a List.mem_cons_self
    have ha : a.Prime := haP.1
    have haL : a.Coprime L.prod := hcop a hL
    rw [List.prod_cons]
    refine ⟨⟨?_, ?_⟩, mul_ne_zero ha.ne_zero hne, ?_, fun q hq => tail q _ hq⟩
    · exact Nat.squarefree_mul_iff.mpr ⟨haL, ha.prime.squarefree, hA.1⟩
    · intro q hq hd
      rcases (Nat.Prime.dvd_mul hq).mp hd with h | h
      · rw [(Nat.prime_dvd_prime_iff_eq hq ha).mp h]
        exact haP
      · exact hA.2 q hq h
    · intro q hq
      have hqa : q ≠ a := fun h => (List.nodup_cons.mp hq.1).1 (h ▸ List.mem_cons_self)
      have hqP : q.Prime := (hq.2 q List.mem_cons_self).1
      have hqL : AdmL l F r (q :: L) :=
        ⟨List.nodup_cons.mpr ⟨fun h => (List.nodup_cons.mp hq.1).1 (List.mem_cons_of_mem a h), (List.nodup_cons.mp (List.nodup_cons.mp hq.1).2).2⟩,
          fun p hp => by
            rcases List.mem_cons.mp hp with h | h
            · exact h ▸ hq.2 q List.mem_cons_self
            · exact hq.2 p (List.mem_cons_of_mem q (List.mem_cons_of_mem a h))⟩
      exact Nat.Coprime.mul_right ((Nat.coprime_primes hqP ha).mpr hqa) (hcop q hqL)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.XMulConjIMul
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

section aux

variable (M : ℕ) [NeZero M] (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K]

private theorem xMul_conjI_eq (P : Ideal (𝓞 K)) (t : (ZMod M)ˣ) :
    conjI M K P t = P.map (sgO M K t).symm := (Ideal.map_symm (sgO M K t)).symm

private theorem xMul_conjI_mul (P Q : Ideal (𝓞 K)) (t : (ZMod M)ˣ) :
    conjI M K (P * Q) t = conjI M K P t * conjI M K Q t := by
  simp only [xMul_conjI_eq, Ideal.map_mul]

private theorem xMul_conjI_pow (P : Ideal (𝓞 K)) (n : ℕ) (t : (ZMod M)ˣ) :
    conjI M K (P ^ n) t = conjI M K P t ^ n := by
  simp only [xMul_conjI_eq, Ideal.map_pow]

private theorem xMul_conj (φ : K →+* ℂ) (x : K) : φ (sg M K (-1) x) = (starRingEnd ℂ) (φ x) := by
  have hζ := IsCyclotomicExtension.zeta_spec M ℚ K
  set ζ := IsCyclotomicExtension.zeta M ℚ K
  have h : φ.toRatAlgHom.comp (sg M K (-1) : K →ₐ[ℚ] K) = ((starRingEnd ℂ).comp φ).toRatAlgHom := by
    apply (hζ.powerBasis ℚ).algHom_ext
    rw [IsPrimitiveRoot.powerBasis_gen]
    have h1 : sg M K (-1) ζ * ζ = 1 := by
      rw [sg_apply M K _ hζ.pow_eq_one, ← pow_succ, hζ.pow_eq_one_iff_dvd, ← ZMod.natCast_eq_zero_iff]
      simp
    have h2 : (φ ζ) ^ M = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
    have h3 : ‖φ ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one h2 (NeZero.ne M)
    have h4 : φ (sg M K (-1) ζ) * φ ζ = 1 := by rw [← map_mul, h1, map_one]
    change φ (sg M K (-1) ζ) = (starRingEnd ℂ) (φ ζ)
    rw [eq_inv_of_mul_eq_one_left h4, Complex.inv_eq_conj h3]
  exact DFunLike.congr_fun h x

private theorem xMul_root (ζ : K) (k : ℕ) (hk : k ≠ 0) (h : ζ ^ k = 1) : ζ * sg M K (-1) ζ = 1 := by
  obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
  apply φ.injective
  have h2 : (φ ζ) ^ k = 1 := by rw [← map_pow, h, map_one]
  have h3 : ‖φ ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one h2 hk
  have h0 : φ ζ ≠ 0 := by
    intro h0
    simp [h0] at h3
  rw [map_mul, xMul_conj, map_one, ← Complex.inv_eq_conj h3, mul_inv_cancel₀ h0]

private noncomputable def xMul_sp : K →*₀ FractionalIdeal (𝓞 K)⁰ K where
  toFun x := FractionalIdeal.spanSingleton (𝓞 K)⁰ x
  map_zero' := FractionalIdeal.spanSingleton_zero
  map_one' := FractionalIdeal.spanSingleton_one
  map_mul' x y := (FractionalIdeal.spanSingleton_mul_spanSingleton x y).symm

private theorem xMul_sp_eq (x : K) : FractionalIdeal.spanSingleton (𝓞 K)⁰ x = xMul_sp K x := rfl

end aux

theorem UpperTheory.V.ML.xMul :
    ∀ (M : ℕ) [NeZero M] (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K] (b : ℕ),
    (∀ (𝔞 𝔟 : Ideal (𝓞 K)) (X Y : K), 𝔞 ≠ ⊥ → 𝔟 ≠ ⊥ → IsX M K b 𝔞 X → IsX M K b 𝔟 Y → IsX M K b (𝔞 * 𝔟) (X * Y)) ∧
    (∀ (𝔞 𝔟 : Ideal (𝓞 K)) (Z Y : K), 𝔞 ≠ ⊥ → 𝔟 ≠ ⊥ → IsX M K b (𝔞 * 𝔟) Z → IsX M K b 𝔟 Y → IsX M K b 𝔞 (Z / Y)) ∧
    (∀ (𝔞 : Ideal (𝓞 K)) (X : K) (n : ℕ), 𝔞 ≠ ⊥ → IsX M K b 𝔞 X → IsX M K b (𝔞 ^ n) (X ^ n)) ∧
    (∀ (𝔞 : Ideal (𝓞 K)) (X ζ : K) (k : ℕ), k ≠ 0 → ζ ^ k = 1 → IsX M K b 𝔞 X → IsX M K b 𝔞 (ζ * X)) ∧
    ∀ y : 𝓞 K, y ≠ 0 → IsX M K b (Ideal.span {y}) (∏ t : (ZMod M)ˣ, (sg M K t)⁻¹ (y : K) ^ th M b t) := by
  intro M _ K _ _ _ b
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro 𝔞 𝔟 X Y - - ⟨hX, hX'⟩ ⟨hY, hY'⟩
    refine ⟨?_, ?_⟩
    · rw [map_mul, mul_mul_mul_comm, hX, hY, one_mul]
    · rw [← FractionalIdeal.spanSingleton_mul_spanSingleton, hX', hY', ← Finset.prod_mul_distrib]
      simp only [xMul_conjI_mul, FractionalIdeal.coeIdeal_mul, mul_zpow]
  · rintro 𝔞 𝔟 Z Y - - ⟨hZ, hZ'⟩ ⟨hY, hY'⟩
    have hY0 : Y ≠ 0 := by
      rintro rfl
      simp at hY
    refine ⟨?_, ?_⟩
    · rw [map_div₀, div_mul_div_comm, hZ, hY, div_one]
    · have h0 : xMul_sp K Y ≠ 0 := (map_ne_zero _).2 hY0
      rw [xMul_sp_eq] at hZ' hY' ⊢
      rw [map_div₀, div_eq_iff h0, hZ', hY', ← Finset.prod_mul_distrib]
      simp only [xMul_conjI_mul, FractionalIdeal.coeIdeal_mul, mul_zpow]
  · rintro 𝔞 X n - ⟨hX, hX'⟩
    refine ⟨?_, ?_⟩
    · rw [map_pow, ← mul_pow, hX, one_pow]
    · rw [xMul_sp_eq] at hX' ⊢
      rw [map_pow, hX', ← Finset.prod_pow]
      refine Finset.prod_congr rfl fun t _ => ?_
      rw [xMul_conjI_pow, FractionalIdeal.coeIdeal_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
  · rintro 𝔞 X ζ k hk hζ ⟨hX, hX'⟩
    refine ⟨?_, ?_⟩
    · rw [map_mul, mul_mul_mul_comm, hX, xMul_root M K ζ k hk hζ, one_mul]
    · rw [← hX', eq_comm, FractionalIdeal.spanSingleton_eq_spanSingleton]
      have hi : IsIntegral ℤ ζ := IsIntegral.of_pow (Nat.pos_of_ne_zero hk) (hζ ▸ isIntegral_one)
      obtain ⟨z, rfl⟩ : ∃ z : 𝓞 K, (z : K) = ζ := ⟨⟨ζ, hi⟩, rfl⟩
      have hu : IsUnit z := IsUnit.of_pow_eq_one (n := k) (Subtype.ext hζ) hk
      obtain ⟨u, rfl⟩ := hu
      refine ⟨u, ?_⟩
      rw [Units.smul_def, Algebra.smul_def]
  · intro y hy
    have hy' : (y : K) ≠ 0 := by exact_mod_cast hy
    refine ⟨?_, ?_⟩
    · rw [map_prod, ← Equiv.prod_comp (Equiv.neg (ZMod M)ˣ) (fun t => sg M K (-1) ((sg M K t)⁻¹ (y : K) ^ th M b t)),
        ← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one fun t _ => ?_
      have h1 : sg M K (-1) ((sg M K (-t))⁻¹ (y : K)) = (sg M K t)⁻¹ (y : K) := by
        rw [← AlgEquiv.mul_apply, ← map_inv, ← map_inv, ← map_mul]
        congr 2
        simp [inv_neg]
      have h2 : (sg M K t)⁻¹ (y : K) ≠ 0 := (map_ne_zero _).2 hy'
      rw [Equiv.neg_apply, map_zpow₀, h1, Units.val_neg, th_neg, zpow_neg]
      exact mul_inv_cancel₀ (zpow_ne_zero _ h2)
    · rw [xMul_sp_eq, map_prod]
      refine Finset.prod_congr rfl fun t _ => ?_
      rw [map_zpow₀, xMul_conjI_eq, Ideal.map_span, Set.image_singleton, FractionalIdeal.coeIdeal_span_singleton]
      rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.XUniqConj
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

private theorem UpperTheory.V.ML.xUniq_conj (M : ℕ) [NeZero M] (K : Type) [Field K] [NumberField K]
    [IsCyclotomicExtension {M} ℚ K] (φ : K →+* ℂ) (x : K) : φ (sg M K (-1) x) = starRingEnd ℂ (φ x) := by
  have hζ := IsCyclotomicExtension.zeta_spec M ℚ K
  set ζ := IsCyclotomicExtension.zeta M ℚ K
  have hz : (φ ζ) ^ M = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
  have key : φ (sg M K (-1) ζ) = starRingEnd ℂ (φ ζ) := by
    rw [sg_apply M K (-1) hζ.pow_eq_one, map_pow]
    have hM : M ∣ ((-1 : (ZMod M)ˣ) : ZMod M).val + 1 := by
      rw [← ZMod.natCast_eq_zero_iff]
      push_cast
      simp
    have hnorm : ‖φ ζ‖ = 1 := by
      have h1 := congrArg norm hz
      rw [norm_pow, norm_one] at h1
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (NeZero.ne M)).mp h1
    have hinv : starRingEnd ℂ (φ ζ) = (φ ζ)⁻¹ := by
      rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hnorm]
      simp
    rw [hinv]
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ]
    obtain ⟨k, hk⟩ := hM
    rw [hk, pow_mul, hz, one_pow]
  have hext := AlgHom.ext_of_adjoin_eq_top (R := ℚ)
    (IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ)
    (φ₁ := (φ.comp (sg M K (-1)).toAlgHom.toRingHom).toRatAlgHom)
    (φ₂ := ((starRingEnd ℂ).comp φ).toRatAlgHom)
    (by
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact key)
  have h2 := DFunLike.congr_fun hext x
  simpa using h2

theorem UpperTheory.V.ML.xUniq :
    ∀ (M : ℕ) [NeZero M] (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K] (b : ℕ) (𝔞 : Ideal (𝓞 K)) (X X' : K), 𝔞 ≠ ⊥ → IsX M K b 𝔞 X → IsX M K b 𝔞 X' → ∃ ζ : K, ζ ^ (2 * M) = 1 ∧ X' = ζ * X := by
  intro M _ K _ _ _ b 𝔞 X X' _ hX hX'
  obtain ⟨z, hz⟩ := (FractionalIdeal.spanSingleton_eq_spanSingleton).mp (hX.2.trans hX'.2.symm)
  set w : K := ((z : 𝓞 K) : K) with hw
  have hX'eq : X' = w * X := by
    rw [← hz, Units.smul_def, Algebra.smul_def]
  have hww : w * sg M K (-1) w = 1 := by
    have h1 := hX'.1
    rw [hX'eq, map_mul] at h1
    have h2 := hX.1
    calc w * sg M K (-1) w = w * sg M K (-1) w * (X * sg M K (-1) X) := by rw [h2, mul_one]
      _ = 1 := by rw [← h1]; ring
  have hnorm : ∀ φ : K →+* ℂ, ‖φ w‖ = 1 := by
    intro φ
    have h3 : φ w * starRingEnd ℂ (φ w) = 1 := by
      rw [← UpperTheory.V.ML.xUniq_conj M K φ w, ← map_mul, hww, map_one]
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at h3
    have h4 : ‖φ w‖ ^ 2 = 1 := by exact_mod_cast h3
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h4
  obtain ⟨n, hn, hwn⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one K ℂ
    (RingOfIntegers.isIntegral_coe (z : 𝓞 K)) hnorm
  have hzt : z ∈ NumberField.Units.torsion K := by
    rw [NumberField.Units.torsion, CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
    refine ⟨n, hn, ?_⟩
    apply Units.ext
    apply RingOfIntegers.coe_injective
    simpa using hwn
  have hpow : w ^ NumberField.Units.torsionOrder K = 1 := by
    have h5 := pow_card_eq_one' (x := (⟨z, hzt⟩ : NumberField.Units.torsion K))
    have h6 : z ^ Nat.card (NumberField.Units.torsion K) = 1 := by
      have h7 := congrArg Subtype.val h5
      rwa [SubgroupClass.coe_pow, OneMemClass.coe_one] at h7
    have h8 := congrArg (fun t : (𝓞 K)ˣ => ((t : 𝓞 K) : K)) h6
    simp only [Units.val_pow_eq_pow_val, Units.val_one, map_pow, map_one] at h8
    exact h8
  refine ⟨w, ?_, hX'eq⟩
  have hdvd : NumberField.Units.torsionOrder K ∣ 2 * M := by
    rw [IsCyclotomicExtension.Rat.torsionOrder_eq (n := M)]
    split_ifs with he
    · exact dvd_mul_left M 2
    · exact dvd_rfl
  obtain ⟨k, hk⟩ := hdvd
  rw [hk, pow_mul, hpow, one_pow]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.ThDist
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

private theorem modSum (q b c : ℕ) (hq : q.Prime) (hb0 : b ≠ 0) (hb : b < q) :
    ∑ i ∈ Finset.range q, (c + i * b) % q = ∑ i ∈ Finset.range q, i := by
  have hinj : Set.InjOn (fun i => (c + i * b) % q) (Finset.range q : Set ℕ) := by
    intro i hi j hj h
    have h1 : c + i * b ≡ c + j * b [MOD q] := h
    have h2 : i * b ≡ j * b [MOD q] := Nat.ModEq.add_left_cancel' c h1
    have hc : Nat.gcd q b = 1 := (Nat.coprime_of_lt_prime hb0 hb hq)
    have h3 : i ≡ j [MOD q] := Nat.ModEq.cancel_right_of_coprime hc h2
    exact Nat.ModEq.eq_of_lt_of_lt h3 (by simpa using hi) (by simpa using hj)
  have him : (Finset.range q).image (fun i => (c + i * b) % q) = Finset.range q := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
      exact Finset.mem_range.2 (Nat.mod_lt _ hq.pos)
    · rw [Finset.card_image_of_injOn hinj]
  have := Finset.sum_image (f := fun x : ℕ => x) hinj
  rw [him] at this
  exact this.symm

private theorem divSum (q b c : ℕ) (hq : q.Prime) (hb0 : b ≠ 0) (hb : b < q) :
    ∑ i ∈ Finset.range q, (c + i * b) / q = c + ∑ i ∈ Finset.range q, (i * b) / q := by
  have key : ∀ c : ℕ, q * ∑ i ∈ Finset.range q, (c + i * b) / q + ∑ i ∈ Finset.range q, i
      = q * c + ∑ i ∈ Finset.range q, i * b := by
    intro c
    rw [← modSum q b c hq hb0 hb, Finset.mul_sum, ← Finset.sum_add_distrib]
    simp only [Nat.div_add_mod]
    rw [Finset.sum_add_distrib]
    simp
  have h1 := key c
  have h2 := key 0
  simp only [zero_add, mul_zero] at h2
  apply Nat.eq_of_mul_eq_mul_left hq.pos
  rw [mul_add]
  omega

private theorem divSum' (M q b a : ℕ) (hM : 0 < M) (hq : q.Prime) (hb : b < q) :
    ∑ i ∈ Finset.range q, (a + i * M) * b / (q * M) = a * b / M + ∑ i ∈ Finset.range q, (i * b) / q := by
  rcases eq_or_ne b 0 with rfl | hb0
  · simp
  rw [← divSum q b _ hq hb0 hb]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm q M, ← Nat.div_div_eq_div_mul]
  congr 1
  rw [show (a + i * M) * b = a * b + i * b * M by ring, Nat.add_mul_div_right _ _ hM]

private theorem classSum (M q a : ℕ) (ha : a < M) (g : ℕ → ℕ) :
    ∑ n ∈ (Finset.range (q * M)).filter (fun n => n % M = a), g n = ∑ i ∈ Finset.range q, g (a + i * M) := by
  have hM : 0 < M := by omega
  symm
  refine Finset.sum_nbij' (fun i => a + i * M) (fun n => n / M) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_range, Finset.mem_filter] at hi ⊢
    refine ⟨by nlinarith, by simp [Nat.mod_eq_of_lt ha]⟩
  · intro n hn
    simp only [Finset.mem_range, Finset.mem_filter] at hn ⊢
    exact (Nat.div_lt_iff_lt_mul hM).2 hn.1
  · intro i _
    rw [Nat.add_mul_div_right _ _ hM, Nat.div_eq_of_lt ha, zero_add]
  · intro n hn
    simp only [Finset.mem_range, Finset.mem_filter] at hn ⊢
    rw [← hn.2, mul_comm]
    exact Nat.mod_add_div n M
  · intro i _
    rfl

private theorem unitSum (M q : ℕ) [NeZero M] [NeZero (q * M)] (hq : q.Prime) (u : (ZMod M)ˣ) (hu : (u : ZMod M) = q)
    (t : (ZMod M)ˣ) (g : ℕ → ℕ) :
    ∑ t' ∈ Finset.univ.filter (fun t' : (ZMod (q * M))ˣ => ZMod.unitsMap (Dvd.intro_left q rfl) t' = t),
      g (t' : ZMod (q * M)).val + g (q * ((u⁻¹ * t : (ZMod M)ˣ) : ZMod M).val)
      = ∑ i ∈ Finset.range q, g ((t : ZMod M).val + i * M) := by
  rw [← classSum M q _ (ZMod.val_lt _) g]
  set s : (ZMod M)ˣ := u⁻¹ * t with hs
  have hst : (q : ZMod M) * s = t := by
    rw [← hu, hs, ← Units.val_mul, mul_inv_cancel_left]
  have hmod : ∀ n : ℕ, n % M = (t : ZMod M).val ↔ (n : ZMod M) = t := by
    intro n
    rw [← ZMod.val_natCast]
    exact (ZMod.val_injective M).eq_iff
  have hmem : q * (s : ZMod M).val ∈ (Finset.range (q * M)).filter (fun n => n % M = (t : ZMod M).val) := by
    simp only [Finset.mem_range, Finset.mem_filter]
    refine ⟨Nat.mul_lt_mul_of_pos_left (ZMod.val_lt _) hq.pos, ?_⟩
    rw [hmod]
    push_cast
    rw [ZMod.natCast_zmod_val, hst]
  rw [← Finset.sum_erase_add _ _ hmem]
  congr 1
  refine Finset.sum_bij (fun t' _ => (t' : ZMod (q * M)).val) ?_ ?_ ?_ ?_
  · intro t' ht'
    simp only [Finset.mem_range, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase] at ht' ⊢
    refine ⟨?_, ZMod.val_lt _, ?_⟩
    · intro h
      have hc := ZMod.val_coe_unit_coprime t'
      rw [h] at hc
      exact hq.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left (Dvd.intro _ rfl) hc) (Dvd.intro _ rfl))
    · rw [hmod, ← ht', ZMod.unitsMap_val, ZMod.natCast_val]
  · intro x _ y _ h
    exact Units.ext (ZMod.val_injective _ h)
  · intro n hn
    simp only [Finset.mem_range, Finset.mem_filter, Finset.mem_erase] at hn
    obtain ⟨h1, h2, h3⟩ := hn
    rw [hmod] at h3
    have hcM : n.Coprime M := by
      rw [← ZMod.isUnit_iff_coprime, h3]
      exact t.isUnit
    have hcq : n.Coprime q := by
      rw [Nat.coprime_comm, hq.coprime_iff_not_dvd]
      rintro ⟨k, rfl⟩
      apply h1
      congr 1
      have hk : k < M := Nat.lt_of_mul_lt_mul_left h2
      have : (k : ZMod M) = s := by
        apply u.isUnit.mul_left_cancel
        rw [hu, hst, ← h3]
        push_cast
        rfl
      rw [← this, ZMod.val_natCast, Nat.mod_eq_of_lt hk]
    have hv : ((ZMod.unitOfCoprime n (Nat.Coprime.mul_right hcq hcM) : (ZMod (q * M))ˣ) : ZMod (q * M)).val = n := by
      rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt h2]
    refine ⟨ZMod.unitOfCoprime n (Nat.Coprime.mul_right hcq hcM), ?_, hv⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    apply Units.ext
    rw [ZMod.unitsMap_val, ← ZMod.natCast_val, hv, h3]
  · intro _ _
    rfl

private theorem halfSum (M q b : ℕ) [NeZero M] [NeZero (q * M)] (hq : q.Prime) (hb : b < q) (u : (ZMod M)ˣ)
    (hu : (u : ZMod M) = q) (t : (ZMod M)ˣ) :
    ∑ t' ∈ Finset.univ.filter (fun t' : (ZMod (q * M))ˣ => ZMod.unitsMap (Dvd.intro_left q rfl) t' = t),
      (((t' : ZMod (q * M)).val * b / (q * M) : ℕ) : ℤ) + ((((u⁻¹ * t : (ZMod M)ˣ) : ZMod M).val * b / M : ℕ) : ℤ)
      = (((t : ZMod M).val * b / M : ℕ) : ℤ) + ((∑ i ∈ Finset.range q, (i * b) / q : ℕ) : ℤ) := by
  have h := unitSum M q hq u hu t (fun n => n * b / (q * M))
  rw [divSum' M q b _ (Nat.pos_of_ne_zero (NeZero.ne M)) hq hb, mul_assoc, Nat.mul_div_mul_left _ _ hq.pos] at h
  rw [← Nat.cast_sum, ← Nat.cast_add, h, Nat.cast_add]

theorem UpperTheory.V.ML.thDist :
    ∀ (M q b : ℕ) [NeZero M] [NeZero (q * M)], q.Prime → b < q → ∀ u : (ZMod M)ˣ, (u : ZMod M) = q → ∀ t : (ZMod M)ˣ,
    ∑ t' ∈ Finset.univ.filter (fun t' : (ZMod (q * M))ˣ => ZMod.unitsMap (Dvd.intro_left q rfl) t' = t), th (q * M) b t' = th M b t - th M b (u⁻¹ * t : (ZMod M)ˣ) := by
  intro M q b _ _ hq hb u hu t
  have h1 := halfSum M q b hq hb u hu t
  have h2 := halfSum M q b hq hb u hu (-t)
  have hneg : ∀ x : (ZMod (q * M))ˣ, ZMod.unitsMap (Dvd.intro_left q rfl) (-x) = -ZMod.unitsMap (Dvd.intro_left q rfl) x := by
    intro x
    apply Units.ext
    rw [Units.val_neg, ZMod.unitsMap_val, ZMod.unitsMap_val, Units.val_neg, ZMod.cast_neg (Dvd.intro_left q rfl)]
  have h3 : ∑ t' ∈ Finset.univ.filter (fun t' : (ZMod (q * M))ˣ => ZMod.unitsMap (Dvd.intro_left q rfl) t' = t),
      (((-(t' : ZMod (q * M))).val * b / (q * M) : ℕ) : ℤ) =
      ∑ t' ∈ Finset.univ.filter (fun t' : (ZMod (q * M))ˣ => ZMod.unitsMap (Dvd.intro_left q rfl) t' = -t),
      (((t' : ZMod (q * M)).val * b / (q * M) : ℕ) : ℤ) := by
    refine Finset.sum_equiv (Equiv.neg _) ?_ ?_
    · intro x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.neg_apply, hneg, neg_inj]
    · intro x _
      simp only [Equiv.neg_apply, Units.val_neg]
  rw [mul_neg, Units.val_neg, Units.val_neg] at h2
  simp only [th]
  rw [Finset.sum_sub_distrib, h3]
  linarith
end
