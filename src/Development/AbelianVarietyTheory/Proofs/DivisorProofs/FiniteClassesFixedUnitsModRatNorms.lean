module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IwahoriEigenvalues

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeMapPrimeMap
open NumberField IsDedekindDomain
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.FixNormCls

variable {E : Type} [Field E] [NumberField E]

def ord (P : HeightOneSpectrum (𝓞 E)) (x : E) : ℤ :=
  FractionalIdeal.count E P (FractionalIdeal.spanSingleton (𝓞 E)⁰ x)

def primeMap (τ : E ≃+* E) (P : HeightOneSpectrum (𝓞 E)) : HeightOneSpectrum (𝓞 E) where
  asIdeal := P.asIdeal.comap (RingOfIntegers.mapRingEquiv τ.symm : 𝓞 E →+* 𝓞 E)
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    intro h
    apply P.ne_bot
    rw [eq_bot_iff] at h ⊢
    intro x hx
    have : (RingOfIntegers.mapRingEquiv τ) x ∈
        P.asIdeal.comap (RingOfIntegers.mapRingEquiv τ.symm : 𝓞 E →+* 𝓞 E) := by
      rw [Ideal.mem_comap]
      convert hx using 1
      exact (RingOfIntegers.mapRingEquiv τ).symm_apply_apply x
    have h2 := h this
    rw [Submodule.mem_bot, map_eq_zero_iff _ (RingOfIntegers.mapRingEquiv τ).injective] at h2
    rw [Submodule.mem_bot]; exact h2

theorem mem_primeMap (τ : E ≃+* E) (P : HeightOneSpectrum (𝓞 E)) (a : 𝓞 E) :
    a ∈ (primeMap τ P).asIdeal ↔ RingOfIntegers.mapRingEquiv τ.symm a ∈ P.asIdeal :=
  Ideal.mem_comap

theorem ord_zero (P : HeightOneSpectrum (𝓞 E)) : ord P (0 : E) = 0 := by
  simp [ord, FractionalIdeal.count_zero]

theorem ord_mul (P : HeightOneSpectrum (𝓞 E)) {x y : E} (hx : x ≠ 0) (hy : y ≠ 0) :
    ord P (x * y) = ord P x + ord P y := by
  unfold ord
  rw [← FractionalIdeal.spanSingleton_mul_spanSingleton]
  exact FractionalIdeal.count_mul E P (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx)
    (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hy)

theorem ord_inv (P : HeightOneSpectrum (𝓞 E)) (x : E) : ord P x⁻¹ = - ord P x := by
  unfold ord
  rw [← FractionalIdeal.spanSingleton_inv, FractionalIdeal.count_inv]

theorem ord_div (P : HeightOneSpectrum (𝓞 E)) {x y : E} (hx : x ≠ 0) (hy : y ≠ 0) :
    ord P (x / y) = ord P x - ord P y := by
  rw [div_eq_mul_inv, ord_mul P hx (inv_ne_zero hy), ord_inv, sub_eq_add_neg]

theorem ord_one (P : HeightOneSpectrum (𝓞 E)) : ord P (1 : E) = 0 := by
  simp [ord, FractionalIdeal.spanSingleton_one, FractionalIdeal.count_one]

theorem ord_primeMap (τ : E ≃+* E) (P : HeightOneSpectrum (𝓞 E)) (x : E) :
    ord (primeMap τ P) (τ x) = ord P x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [ord_zero]
  exact GlobalTheory.OrdTransport.count_spanSingleton_ringEquiv (𝓞 E) E (RingOfIntegers.mapRingEquiv τ) τ
    (fun a => rfl) P (primeMap τ P)
    (fun a => by
      rw [mem_primeMap]
      have : RingOfIntegers.mapRingEquiv τ.symm (RingOfIntegers.mapRingEquiv τ a) = a :=
        RingOfIntegers.ext (by change τ.symm (τ (a : E)) = (a : E); exact τ.symm_apply_apply _)
      rw [this]) x hx

theorem primeMap_primeMap (τ : E ≃+* E) (hτ : ∀ x, τ (τ x) = x) (P : HeightOneSpectrum (𝓞 E)) :
    primeMap τ (primeMap τ P) = P := by
  ext a
  rw [mem_primeMap, mem_primeMap]
  have : RingOfIntegers.mapRingEquiv τ.symm (RingOfIntegers.mapRingEquiv τ.symm a) = a := by
    apply RingOfIntegers.ext
    change τ.symm (τ.symm (a : E)) = (a : E)
    rw [RingEquiv.symm_apply_eq, RingEquiv.symm_apply_eq, hτ]
  rw [this]

end GlobalTheory.FixNormCls
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteClassesModuloInvolutionNorms
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteFixedUnitsModFixedSquares
open NumberField IsDedekindDomain GlobalTheory.FixNormCls
open scoped Classical nonZeroDivisors

noncomputable section

namespace GlobalTheory.UnitSq

def fixedUnits (E : Type) [Field E] [NumberField E] (τ : E ≃+* E) : Subgroup (𝓞 E)ˣ where
  carrier := {u | τ ((u : 𝓞 E) : E) = ((u : 𝓞 E) : E)}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Units.val_mul, map_mul] at *
    rw [ha, hb]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    have h1 : ((a⁻¹ : (𝓞 E)ˣ) : 𝓞 E) * (a : 𝓞 E) = 1 := by simp
    have h1' : (((a⁻¹ : (𝓞 E)ˣ) : 𝓞 E) : E) * (((a : 𝓞 E) : E)) = 1 := by
      exact_mod_cast congrArg (fun x : 𝓞 E => (x : E)) h1
    have h2 : (((a⁻¹ : (𝓞 E)ˣ) : 𝓞 E) : E) = (((a : 𝓞 E) : E))⁻¹ :=
      eq_inv_of_mul_eq_one_left h1'
    rw [h2, map_inv₀, ha]

end GlobalTheory.UnitSq
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteClassesModuloInvolutionNorms
open NumberField IsDedekindDomain GlobalTheory.FixNormCls
open scoped TensorProduct Classical nonZeroDivisors

namespace GlobalTheory.FixNormField

open NumberField IsDedekindDomain in
open scoped Classical nonZeroDivisors in
open NumberField IsDedekindDomain in
open scoped TensorProduct Classical nonZeroDivisors in
private theorem finite_heightOneSpectrum_containing_finset_nat (K : Type) [Field K] [NumberField K] (S : Finset ℕ) :
    {P : HeightOneSpectrum (𝓞 K) | ∃ ℓ ∈ S, ℓ ≠ 0 ∧ (ℓ : 𝓞 K) ∈ P.asIdeal}.Finite := by
  have : {P : HeightOneSpectrum (𝓞 K) | ∃ ℓ ∈ S, ℓ ≠ 0 ∧ (ℓ : 𝓞 K) ∈ P.asIdeal} ⊆
      ⋃ ℓ ∈ S.filter (· ≠ 0), {P | P.asIdeal ∣ Ideal.span {(ℓ : 𝓞 K)}} := by
    rintro P ⟨ℓ, hS, h0, hP⟩
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Finset.mem_filter]
    exact ⟨ℓ, ⟨hS, h0⟩, Ideal.dvd_span_singleton.2 hP⟩
  refine Set.Finite.subset (Set.Finite.biUnion (Finset.finite_toSet _) fun ℓ hℓ => ?_) this
  refine Ideal.finite_factors ?_
  rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  exact_mod_cast (Finset.mem_filter.1 hℓ).2

open NumberField IsDedekindDomain in
open scoped Classical nonZeroDivisors in
open NumberField IsDedekindDomain in
open scoped TensorProduct Classical nonZeroDivisors in
private theorem exists_finset_submodule_eq_add_two_smul {M : Type*} [AddCommGroup M]
    [Module.Finite ℤ M] (N : Submodule ℤ M) :
    ∃ V : Finset M, (∀ v ∈ V, v ∈ N) ∧ ∀ h ∈ N, ∃ v ∈ V, ∃ w ∈ N, h = v + 2 • w := by
  classical
  haveI := isNoetherian_of_isNoetherianRing_of_finite ℤ M
  haveI : Module.Finite ℤ N := Module.IsNoetherian.finite ℤ N
  let D : Submodule ℤ N := LinearMap.range ((2 : ℤ) • LinearMap.id)
  haveI : Finite (N ⧸ D) := by
    refine Module.finite_of_fg_torsion _ fun q => ?_
    refine ⟨⟨2, mem_nonZeroDivisors_of_ne_zero two_ne_zero⟩, ?_⟩
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective D q
    show (2 : ℤ) • (Submodule.Quotient.mk x : N ⧸ D) = 0
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact ⟨x, rfl⟩
  haveI := Fintype.ofFinite (N ⧸ D)
  refine ⟨(Finset.univ : Finset (N ⧸ D)).image fun q => ((Quotient.out q : N) : M), ?_, ?_⟩
  · intro v hv
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hv
    exact (Quotient.out q).2
  · intro h hh
    let q : N ⧸ D := Submodule.Quotient.mk ⟨h, hh⟩
    have hq : Submodule.Quotient.mk (Quotient.out q) = q := Quotient.out_eq q
    rw [Submodule.Quotient.eq] at hq
    obtain ⟨w, hw⟩ := hq
    refine ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ q), -(w : M), N.neg_mem w.2, ?_⟩
    have := congrArg (fun z : N => (z : M)) hw
    simp only [LinearMap.smul_apply, LinearMap.id_apply, Submodule.coe_smul, Submodule.coe_sub] at this
    have h2 : (2 : ℕ) • (w : M) = (2 : ℤ) • (w : M) := by rw [two_smul, two_smul]
    rw [smul_neg, h2, this]
    abel

open NumberField IsDedekindDomain in
open scoped Classical nonZeroDivisors in
open NumberField IsDedekindDomain in
open scoped TensorProduct Classical nonZeroDivisors in
private theorem exists_finset_fixedUnit_eq_mul_fixed_sq (K : Type) [Field K] [NumberField K]
    (τ : K ≃+* K) : ∃ V : Finset K, ∀ u ∈ _root_.GlobalTheory.UnitSq.fixedUnits K τ, ∃ v ∈ V, ∃ w : K,
      w ≠ 0 ∧ τ w = w ∧ ((u : 𝓞 K) : K) = v * w ^ 2 := by
  classical
  obtain ⟨V, -, hV⟩ := exists_finset_submodule_eq_add_two_smul (M := Additive (𝓞 K)ˣ)
    (AddSubgroup.toIntSubmodule (_root_.GlobalTheory.UnitSq.fixedUnits K τ).toAddSubgroup)
  refine ⟨V.image fun v => (((Additive.toMul v : (𝓞 K)ˣ) : 𝓞 K) : K), fun u hu => ?_⟩
  obtain ⟨v, hv, w, hw, huv⟩ := hV (Additive.ofMul u) hu
  refine ⟨_, Finset.mem_image_of_mem _ hv, (((Additive.toMul w : (𝓞 K)ˣ) : 𝓞 K) : K), ?_, hw, ?_⟩
  · simp
  · have h := congrArg Additive.toMul huv
    simp only [toMul_ofMul, toMul_add, toMul_nsmul] at h
    rw [h]
    push_cast
    ring

open NumberField IsDedekindDomain in
open scoped Classical nonZeroDivisors in
open NumberField IsDedekindDomain in
open scoped TensorProduct Classical nonZeroDivisors in
private theorem ord_apply_involution_eq_ord_primeMap {K : Type} [Field K] [NumberField K] (τ : K ≃+* K)
    (hτ : ∀ x, τ (τ x) = x) (P : HeightOneSpectrum (𝓞 K)) (x : K) :
    _root_.GlobalTheory.FixNormCls.ord P (τ x) =
      _root_.GlobalTheory.FixNormCls.ord (_root_.GlobalTheory.FixNormCls.primeMap τ P) x := by
  have h := _root_.GlobalTheory.FixNormCls.ord_primeMap τ
    (_root_.GlobalTheory.FixNormCls.primeMap τ P) x
  rwa [_root_.GlobalTheory.FixNormCls.primeMap_primeMap τ hτ] at h

open NumberField IsDedekindDomain in
open scoped Classical nonZeroDivisors in
open NumberField IsDedekindDomain in
open scoped TensorProduct Classical nonZeroDivisors in
private theorem exists_nat_prime_mem_heightOneSpectrum (K : Type) [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K)) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ (ℓ : 𝓞 K) ∈ P.asIdeal := by
  haveI : P.asIdeal.IsMaximal := P.isMaximal
  letI : Field (𝓞 K ⧸ P.asIdeal) := Ideal.Quotient.field _
  haveI : Finite (𝓞 K ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  obtain ⟨p, hp⟩ := CharP.exists (𝓞 K ⧸ P.asIdeal)
  have hp0 : p ≠ 0 := CharP.char_ne_zero_of_finite (𝓞 K ⧸ P.asIdeal) p
  haveI : NeZero p := ⟨hp0⟩
  refine ⟨p, (CharP.char_is_prime_of_pos (𝓞 K ⧸ P.asIdeal) p).out, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact CharP.cast_eq_zero _ p

open NumberField IsDedekindDomain in
open scoped Classical nonZeroDivisors in
open NumberField IsDedekindDomain in
open scoped TensorProduct Classical nonZeroDivisors in
private theorem ord_eq_zero_of_not_mem_of_ne_zero {K : Type} [Field K] [NumberField K]
    (P : HeightOneSpectrum (𝓞 K)) (z : 𝓞 K) (h0 : z ≠ 0) (hz : z ∉ P.asIdeal) :
    _root_.GlobalTheory.FixNormCls.ord P (z : K) = 0 := by
  classical
  unfold _root_.GlobalTheory.FixNormCls.ord
  rw [← FractionalIdeal.coeIdeal_span_singleton]
  have hI : ((Ideal.span {z} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero, Ideal.span_singleton_eq_bot]; exact h0
  rw [FractionalIdeal.count_well_defined K P hI (a := 1) (J := Ideal.span {z}) (by simp),
    Ideal.span_singleton_one, ← Ideal.one_eq_top, Associates.mk_one, Associates.factors_one,
    Associates.count_zero P.associates_irreducible]
  rw [Nat.cast_zero, sub_zero, Nat.cast_eq_zero]
  by_contra hc
  have hspan : Ideal.span {z} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact h0
  have := (Associates.count_ne_zero_iff_dvd hspan P.irreducible).1 hc
  exact hz (Ideal.span_singleton_le_iff_mem _ |>.1 (Ideal.le_of_dvd this))

open NumberField IsDedekindDomain in
open scoped Classical nonZeroDivisors in
open NumberField IsDedekindDomain in
open scoped TensorProduct Classical nonZeroDivisors in
private theorem natCast_not_mem_of_prime_mem_not_dvd {K : Type} [Field K] [NumberField K]
    (P : HeightOneSpectrum (𝓞 K)) {ℓ d : ℕ} (hℓ : ℓ.Prime) (hP : (ℓ : 𝓞 K) ∈ P.asIdeal)
    (hd : ¬ ℓ ∣ d) : (d : 𝓞 K) ∉ P.asIdeal := by
  intro hdP
  have hcop : IsCoprime (ℓ : ℤ) (d : ℤ) :=
    Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hℓ).2 hd)
  obtain ⟨u, v, huv⟩ := hcop
  have h1 : ((u : 𝓞 K) * (ℓ : 𝓞 K) + (v : 𝓞 K) * (d : 𝓞 K)) = 1 := by
    exact_mod_cast congrArg (fun n : ℤ => (n : 𝓞 K)) huv
  apply P.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← h1]
  exact P.asIdeal.add_mem (P.asIdeal.mul_mem_left _ hP) (P.asIdeal.mul_mem_left _ hdP)

open NumberField IsDedekindDomain in
open scoped Classical nonZeroDivisors in
open NumberField IsDedekindDomain in
open scoped TensorProduct Classical nonZeroDivisors in
private theorem ord_nonneg_of_isIntegral' {K : Type} [Field K] [NumberField K]
    (P : HeightOneSpectrum (𝓞 K)) {z : K} (hz : IsIntegral ℤ z) :
    0 ≤ _root_.GlobalTheory.FixNormCls.ord P z := by
  obtain ⟨w, rfl⟩ : ∃ w : 𝓞 K, (w : K) = z := ⟨⟨z, hz⟩, rfl⟩
  unfold _root_.GlobalTheory.FixNormCls.ord
  rw [← FractionalIdeal.coeIdeal_span_singleton]
  exact FractionalIdeal.count_coe_nonneg K P _

open NumberField IsDedekindDomain in
open scoped Classical nonZeroDivisors in
open NumberField IsDedekindDomain in
open scoped TensorProduct Classical nonZeroDivisors in
private theorem ord_eq_ord_add_ord_primeMap_of_isIntegral_mul {K : Type} [Field K] [NumberField K] (τ : K ≃+* K)
    (hτ : ∀ x, τ (τ x) = x) (P : HeightOneSpectrum (𝓞 K)) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hP : (ℓ : 𝓞 K) ∈ P.asIdeal) {a b x y : K} (ha0 : a ≠ 0) (hb : b ≠ 0)
    (hax : a = x * (b * τ b)) (hby : b * τ b = y * a) {d : ℕ} (hd : ¬ ℓ ∣ d)
    (hdx : IsIntegral ℤ ((d : K) * x)) (hdy : IsIntegral ℤ ((d : K) * y)) :
    _root_.GlobalTheory.FixNormCls.ord P a = _root_.GlobalTheory.FixNormCls.ord P b +
      _root_.GlobalTheory.FixNormCls.ord (_root_.GlobalTheory.FixNormCls.primeMap τ P) b := by
  have hτb : τ b ≠ 0 := by simpa using hb
  have hN : b * τ b ≠ 0 := mul_ne_zero hb hτb
  have hx0 : x ≠ 0 := by rintro rfl; simp at hax; exact ha0 hax
  have hy0 : y ≠ 0 := by rintro rfl; rw [zero_mul] at hby; exact hN hby
  have hxy : x * y = 1 := by
    exact mul_right_cancel₀ ha0 (by rw [one_mul, mul_assoc, ← hby, ← hax])
  have hd0 : d ≠ 0 := by rintro rfl; exact hd (dvd_zero ℓ)
  have hdK : (d : K) ≠ 0 := by exact_mod_cast hd0
  have hord_d : _root_.GlobalTheory.FixNormCls.ord P (d : K) = 0 := by
    have h := ord_eq_zero_of_not_mem_of_ne_zero P (d : 𝓞 K) (by exact_mod_cast hd0)
      (natCast_not_mem_of_prime_mem_not_dvd P hℓ hP hd)
    simpa using h
  have h1 := ord_nonneg_of_isIntegral' P hdx
  have h2 := ord_nonneg_of_isIntegral' P hdy
  rw [_root_.GlobalTheory.FixNormCls.ord_mul P hdK hx0, hord_d] at h1
  rw [_root_.GlobalTheory.FixNormCls.ord_mul P hdK hy0, hord_d] at h2
  have h3 : _root_.GlobalTheory.FixNormCls.ord P x + _root_.GlobalTheory.FixNormCls.ord P y = 0 := by
    rw [← _root_.GlobalTheory.FixNormCls.ord_mul P hx0 hy0, hxy, _root_.GlobalTheory.FixNormCls.ord_one]
  rw [hax, _root_.GlobalTheory.FixNormCls.ord_mul P hx0 hN, _root_.GlobalTheory.FixNormCls.ord_mul P hb hτb,
    ord_apply_involution_eq_ord_primeMap τ hτ]
  omega

open NumberField IsDedekindDomain in
open scoped Classical nonZeroDivisors in
open NumberField IsDedekindDomain in
open scoped TensorProduct Classical nonZeroDivisors in
private theorem exists_unit_eq_of_forall_ord_eq_zero {K : Type} [Field K] [NumberField K] {x : K} (hx : x ≠ 0)
    (h : ∀ P : HeightOneSpectrum (𝓞 K), _root_.GlobalTheory.FixNormCls.ord P x = 0) :
    ∃ u : (𝓞 K)ˣ, ((u : 𝓞 K) : K) = x := by
  have hI : FractionalIdeal.spanSingleton (𝓞 K)⁰ x ≠ 0 := by
    rwa [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]
  have key := FractionalIdeal.finprod_heightOneSpectrum_factorization' (K := K) hI
  have h' : ∀ P : HeightOneSpectrum (𝓞 K),
      FractionalIdeal.count K P (FractionalIdeal.spanSingleton (𝓞 K)⁰ x) = 0 := h
  simp only [h', zpow_zero, finprod_one] at key
  rw [← FractionalIdeal.spanSingleton_one, FractionalIdeal.spanSingleton_eq_spanSingleton] at key
  obtain ⟨z, hz⟩ := key
  exact ⟨z, by simpa [Units.smul_def, Algebra.smul_def] using hz⟩


open NumberField IsDedekindDomain in
open scoped Classical nonZeroDivisors in
open NumberField IsDedekindDomain in
open scoped TensorProduct Classical nonZeroDivisors in
theorem _root_.GlobalTheory.FixNormField.fixed_classes_mod_norms : ∀ (K : Type) [Field K] [NumberField K]
    (τ : K ≃+* K), (∀ x, τ (τ x) = x) → ∀ S : Finset ℕ,
    ∃ M : Finset K, ∀ a : K, a ≠ 0 → τ a = a →
    (∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ∃ (b x y : K), b ≠ 0 ∧ a = x * (b * τ b) ∧ b * τ b = y * a ∧
      ∃ d : ℕ, ¬ ℓ ∣ d ∧ IsIntegral ℤ ((d : K) * x) ∧ IsIntegral ℤ ((d : K) * y)) →
    ∃ m ∈ M, ∃ e : K, e ≠ 0 ∧ a = e * m * τ e := by
  intro K _ _ τ hτ S
  classical
  have hσσ := _root_.GlobalTheory.FixNormCls.primeMap_primeMap τ hτ
  letI : LinearOrder (HeightOneSpectrum (𝓞 K)) := IsWellOrder.linearOrder WellOrderingRel
  have hTfin := finite_heightOneSpectrum_containing_finset_nat K S
  set T := hTfin.toFinset with hT
  have hrep : ∀ c : ClassGroup (𝓞 K), ∃ I : (FractionalIdeal (𝓞 K)⁰ K)ˣ, ClassGroup.mk K I = c :=
    fun c => ClassGroup.induction K (fun I => ⟨I, rfl⟩) c
  choose rep hrep using hrep
  let prof : ClassGroup (𝓞 K) × Finset (HeightOneSpectrum (𝓞 K)) → HeightOneSpectrum (𝓞 K) → ℤ :=
    fun κ P => (if P ∈ κ.2 then 1 else 0) +
      FractionalIdeal.count K P (rep κ.1 : FractionalIdeal (𝓞 K)⁰ K) +
      FractionalIdeal.count K (_root_.GlobalTheory.FixNormCls.primeMap τ P) (rep κ.1 : FractionalIdeal (𝓞 K)⁰ K)
  let good : ClassGroup (𝓞 K) × Finset (HeightOneSpectrum (𝓞 K)) → K → Prop :=
    fun κ c => c ≠ 0 ∧ τ c = c ∧ ∀ P, _root_.GlobalTheory.FixNormCls.ord P c = prof κ P
  let rep2 : ClassGroup (𝓞 K) × Finset (HeightOneSpectrum (𝓞 K)) → K :=
    fun κ => if h : ∃ c, good κ c then h.choose else 1
  have hrep2 : ∀ κ c, good κ c → good κ (rep2 κ) := fun κ c hc => by
    have h : ∃ c, good κ c := ⟨c, hc⟩
    dsimp only [rep2]
    rw [dite_eq_left h]
    exact h.choose_spec
  obtain ⟨V, hV⟩ := exists_finset_fixedUnit_eq_mul_fixed_sq K τ
  refine ⟨(((Finset.univ ×ˢ T.powerset).image rep2) ×ˢ V).image (fun p => p.1 * p.2), ?_⟩
  intro a ha0 hτa hloc
  have hσa : ∀ P, _root_.GlobalTheory.FixNormCls.ord (_root_.GlobalTheory.FixNormCls.primeMap τ P) a =
      _root_.GlobalTheory.FixNormCls.ord P a := by
    intro P; rw [← ord_apply_involution_eq_ord_primeMap τ hτ, hτa]
  have hsplit : ∀ P, P ∉ T → _root_.GlobalTheory.FixNormCls.primeMap τ P = P →
      _root_.GlobalTheory.FixNormCls.ord P a % 2 = 0 := by
    intro P hP hfix
    obtain ⟨ℓ, hℓ, hℓP⟩ := exists_nat_prime_mem_heightOneSpectrum K P
    have hℓS : ℓ ∉ S := fun hS => hP (by
      rw [hT, Set.Finite.mem_toFinset]; exact ⟨ℓ, hS, hℓ.ne_zero, hℓP⟩)
    obtain ⟨b, x, y, hb, hax, hby, d, hd, hdx, hdy⟩ := hloc ℓ hℓ hℓS
    rw [ord_eq_ord_add_ord_primeMap_of_isIntegral_mul τ hτ P hℓ hℓP ha0 hb hax hby hd hdx hdy, hfix]
    omega
  let k : HeightOneSpectrum (𝓞 K) → ℤ := fun P =>
    if _root_.GlobalTheory.FixNormCls.primeMap τ P = P then _root_.GlobalTheory.FixNormCls.ord P a / 2
    else if P < _root_.GlobalTheory.FixNormCls.primeMap τ P then _root_.GlobalTheory.FixNormCls.ord P a else 0
  have hk : ∀ P, k P + k (_root_.GlobalTheory.FixNormCls.primeMap τ P) = _root_.GlobalTheory.FixNormCls.ord P a -
      (if _root_.GlobalTheory.FixNormCls.primeMap τ P = P then _root_.GlobalTheory.FixNormCls.ord P a % 2 else 0) := by
    intro P
    by_cases hfix : _root_.GlobalTheory.FixNormCls.primeMap τ P = P
    · simp only [k, hfix, if_true]; omega
    · have e1 : k P = if P < _root_.GlobalTheory.FixNormCls.primeMap τ P then
          _root_.GlobalTheory.FixNormCls.ord P a else 0 := by
        simp only [k]; rw [if_neg hfix]
      have e2 : k (_root_.GlobalTheory.FixNormCls.primeMap τ P) = if _root_.GlobalTheory.FixNormCls.primeMap τ P < P then
          _root_.GlobalTheory.FixNormCls.ord P a else 0 := by
        simp only [k, hσσ, hσa]; rw [if_neg fun h => hfix h.symm]
      rw [e1, e2, if_neg hfix, sub_zero]
      rcases lt_trichotomy P (_root_.GlobalTheory.FixNormCls.primeMap τ P) with h | h | h
      · rw [if_pos h, if_neg (lt_asymm h), add_zero]
      · exact absurd h.symm hfix
      · rw [if_neg (lt_asymm h), if_pos h, zero_add]
  have hkfin : ∀ᶠ P in Filter.cofinite, k P = 0 := by
    filter_upwards [FractionalIdeal.finite_factors (K := K)
      (FractionalIdeal.spanSingleton (𝓞 K)⁰ a)] with P hP
    have hP' : _root_.GlobalTheory.FixNormCls.ord P a = 0 := hP
    simp [k, hP']
  set J : FractionalIdeal (𝓞 K)⁰ K :=
    ∏ᶠ P : HeightOneSpectrum (𝓞 K), (P.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ k P with hJ
  have hJ0 : J ≠ 0 := finprod_ne_zero fun P => zpow_ne_zero _ (by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]; exact P.ne_bot)
  have hJcount : ∀ P, FractionalIdeal.count K P J = k P := fun P =>
    FractionalIdeal.count_finprod K P k hkfin
  set c0 := ClassGroup.mk K (Units.mk0 J hJ0) with hc0def
  set I := rep c0 with hIdef
  have hprin : ClassGroup.mk K (Units.mk0 J hJ0 * I⁻¹) = 1 := by
    rw [map_mul, map_inv, hIdef, hrep c0, mul_inv_cancel]
  rw [ClassGroup.mk_eq_one_iff, FractionalIdeal.isPrincipal_iff] at hprin
  obtain ⟨e, he⟩ := hprin
  have hI0 : (I : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := I.ne_zero
  have he' : FractionalIdeal.spanSingleton (𝓞 K)⁰ e = J * (I : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
    rw [← he]; simp
  have he0 : e ≠ 0 := by
    rintro rfl
    rw [FractionalIdeal.spanSingleton_zero] at he'
    exact mul_ne_zero hJ0 (inv_ne_zero hI0) he'.symm
  have heord : ∀ P, _root_.GlobalTheory.FixNormCls.ord P e =
      k P - FractionalIdeal.count K P (I : FractionalIdeal (𝓞 K)⁰ K) := by
    intro P
    show FractionalIdeal.count K P (FractionalIdeal.spanSingleton (𝓞 K)⁰ e) = _
    rw [he', FractionalIdeal.count_mul K P hJ0 (inv_ne_zero hI0), FractionalIdeal.count_inv,
      hJcount]
    ring
  have hτe0 : τ e ≠ 0 := by simpa using he0
  set c := a / (e * τ e) with hc
  have hc0 : c ≠ 0 := div_ne_zero ha0 (mul_ne_zero he0 hτe0)
  have hτc : τ c = c := by rw [hc, map_div₀, map_mul, hτ, hτa, mul_comm (τ e)]
  set Rset := T.filter (fun P => _root_.GlobalTheory.FixNormCls.primeMap τ P = P ∧
    _root_.GlobalTheory.FixNormCls.ord P a % 2 = 1) with hRset
  have hgood : good (c0, Rset) c := by
    refine ⟨hc0, hτc, fun P => ?_⟩
    have hr : (if P ∈ Rset then (1 : ℤ) else 0) =
        (if _root_.GlobalTheory.FixNormCls.primeMap τ P = P then _root_.GlobalTheory.FixNormCls.ord P a % 2 else 0) := by
      by_cases hfix : _root_.GlobalTheory.FixNormCls.primeMap τ P = P
      · rw [if_pos hfix]
        by_cases hPT : P ∈ T
        · have h2 := Int.emod_two_eq_zero_or_one (_root_.GlobalTheory.FixNormCls.ord P a)
          rcases h2 with h2 | h2
          · rw [if_neg (by simp [hRset, h2]), h2]
          · rw [if_pos (by simp [hRset, hPT, hfix, h2]), h2]
        · rw [if_neg (by simp [hRset, hPT]), hsplit P hPT hfix]
      · rw [if_neg hfix, if_neg (by simp [hRset, hfix])]
    have h1 := hk P
    show _root_.GlobalTheory.FixNormCls.ord P c = (if P ∈ Rset then 1 else 0) +
      FractionalIdeal.count K P (I : FractionalIdeal (𝓞 K)⁰ K) +
      FractionalIdeal.count K (_root_.GlobalTheory.FixNormCls.primeMap τ P) (I : FractionalIdeal (𝓞 K)⁰ K)
    rw [hc, _root_.GlobalTheory.FixNormCls.ord_div P ha0 (mul_ne_zero he0 hτe0),
      _root_.GlobalTheory.FixNormCls.ord_mul P he0 hτe0, ord_apply_involution_eq_ord_primeMap τ hτ, heord, heord, hr]
    linarith
  obtain ⟨hc10, hτc1, hc1ord⟩ := hrep2 _ _ hgood
  set c1 := rep2 (c0, Rset) with hc1def
  have hq : ∀ P, _root_.GlobalTheory.FixNormCls.ord P (c / c1) = 0 := by
    intro P
    rw [_root_.GlobalTheory.FixNormCls.ord_div P hc0 hc10, hgood.2.2 P, hc1ord P, sub_self]
  obtain ⟨u, hu⟩ := exists_unit_eq_of_forall_ord_eq_zero (div_ne_zero hc0 hc10) hq
  have hufix : u ∈ _root_.GlobalTheory.UnitSq.fixedUnits K τ := by
    show τ ((u : 𝓞 K) : K) = ((u : 𝓞 K) : K)
    rw [hu, map_div₀, hτc, hτc1]
  obtain ⟨v, hvV, w, hw0, hτw, huvw⟩ := hV u hufix
  refine ⟨c1 * v, Finset.mem_image.2 ⟨(c1, v), Finset.mem_product.2
    ⟨Finset.mem_image.2 ⟨(c0, Rset), Finset.mem_product.2 ⟨Finset.mem_univ _,
      Finset.mem_powerset.2 (Finset.filter_subset _ _)⟩, rfl⟩, hvV⟩, rfl⟩,
    e * w, mul_ne_zero he0 hw0, ?_⟩
  rw [hu] at huvw
  have hcv : c = c1 * (v * w ^ 2) := by rw [← huvw]; field_simp
  have hac : a = c * (e * τ e) := by rw [hc]; field_simp
  rw [hac, hcv, map_mul, hτw]
  ring

end GlobalTheory.FixNormField
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteClassesModuloInvolutionNormsStatement
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_classes_modulo_involutionNorms : ∀ (K : Type) [Field K] [NumberField K] (τ : K ≃+* K), (∀ x, τ (τ x) = x) → ∀ S : Finset ℕ,
    ∃ M : Finset K, ∀ a : K, a ≠ 0 → τ a = a →
    (∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ∃ (b x y : K), b ≠ 0 ∧ a = x * (b * τ b) ∧ b * τ b = y * a ∧
      ∃ d : ℕ, ¬ ℓ ∣ d ∧ IsIntegral ℤ ((d : K) * x) ∧ IsIntegral ℤ ((d : K) * y)) →
    ∃ m ∈ M, ∃ e : K, e ≠ 0 ∧ a = e * m * τ e := by
  first | (exact @GlobalTheory.FixNormField.fixed_classes_mod_norms) | (exact GlobalTheory.FixNormField.fixed_classes_mod_norms) | (intros; apply GlobalTheory.FixNormField.fixed_classes_mod_norms  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvolutionNormClassRemoveRationalFactor
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvolutionNormClassRemoveRationalFactor
open scoped TensorProduct Classical

namespace GlobalTheory.RatRed

def LUnit (ℓ : ℕ) (r : ℚ) : Prop :=
  ∃ N : ℕ, ¬ ℓ ∣ N ∧ (∃ m : ℤ, (N : ℚ) * r = m) ∧ ∃ m : ℤ, (N : ℚ) * r⁻¹ = m

theorem lunit_one (ℓ : ℕ) (hℓ : ℓ.Prime) : LUnit ℓ 1 :=
  ⟨1, hℓ.not_dvd_one, ⟨1, by simp⟩, ⟨1, by simp⟩⟩

theorem lunit_mul {ℓ : ℕ} (hℓ : ℓ.Prime) {r s : ℚ} (hr : LUnit ℓ r) (hs : LUnit ℓ s) :
    LUnit ℓ (r * s) := by
  obtain ⟨N, hN, ⟨m₁, h₁⟩, ⟨m₂, h₂⟩⟩ := hr
  obtain ⟨M, hM, ⟨k₁, g₁⟩, ⟨k₂, g₂⟩⟩ := hs
  refine ⟨N * M, fun h => (hℓ.dvd_mul.1 h).elim hN hM, ⟨m₁ * k₁, ?_⟩, ⟨m₂ * k₂, ?_⟩⟩
  · push_cast; rw [← h₁, ← g₁]; ring
  · push_cast; rw [← h₂, ← g₂, mul_inv]; ring

theorem lunit_inv {ℓ : ℕ} {r : ℚ} (hr : LUnit ℓ r) : LUnit ℓ r⁻¹ := by
  obtain ⟨N, hN, h₁, h₂⟩ := hr
  exact ⟨N, hN, h₂, by simpa using h₁⟩

theorem lunit_neg {ℓ : ℕ} {r : ℚ} (hr : LUnit ℓ r) : LUnit ℓ (-r) := by
  obtain ⟨N, hN, ⟨m₁, h₁⟩, ⟨m₂, h₂⟩⟩ := hr
  refine ⟨N, hN, ⟨-m₁, ?_⟩, ⟨-m₂, ?_⟩⟩
  · push_cast; rw [← h₁]; ring
  · push_cast; rw [← h₂, inv_neg]; ring

theorem lunit_nat {ℓ : ℕ} {n : ℕ} (hn : ¬ ℓ ∣ n) : LUnit ℓ (n : ℚ) := by
  have hn0 : (n : ℚ) ≠ 0 := by
    rintro h; exact hn (by rw [Nat.cast_eq_zero.1 h]; exact dvd_zero _)
  refine ⟨n, hn, ⟨(n : ℤ) * n, by push_cast; ring⟩, ⟨1, by rw [mul_inv_cancel₀ hn0]; simp⟩⟩

theorem lunit_pow {ℓ : ℕ} (hℓ : ℓ.Prime) {r : ℚ} (hr : LUnit ℓ r) (k : ℕ) : LUnit ℓ (r ^ k) := by
  induction k with
  | zero => simpa using lunit_one ℓ hℓ
  | succ k ih => rw [pow_succ]; exact lunit_mul hℓ ih hr

theorem lunit_zpow {ℓ : ℕ} (hℓ : ℓ.Prime) {r : ℚ} (hr : LUnit ℓ r) (k : ℤ) : LUnit ℓ (r ^ k) := by
  rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
  · simpa using lunit_pow hℓ hr n
  · simpa [zpow_neg] using lunit_inv (lunit_pow hℓ hr n)

theorem lunit_prime {ℓ p : ℕ} (hℓ : ℓ.Prime) (hp : p.Prime) (hne : p ≠ ℓ) : LUnit ℓ (p : ℚ) :=
  lunit_nat (fun h => hne ((Nat.prime_dvd_prime_iff_eq hℓ hp).1 h).symm)

theorem lunit_decomp {ℓ : ℕ} (hℓ : ℓ.Prime) {c : ℚ} (hc : c ≠ 0) :
    ∃ k : ℤ, LUnit ℓ (c / (ℓ : ℚ) ^ k) := by
  have hnum : c.num.natAbs ≠ 0 := by simpa using Rat.num_ne_zero.2 hc
  obtain ⟨e₁, n, hn, hne⟩ := Nat.exists_eq_pow_mul_and_not_dvd hnum ℓ hℓ.ne_one
  obtain ⟨e₂, m, hm, hme⟩ := Nat.exists_eq_pow_mul_and_not_dvd c.den_nz ℓ hℓ.ne_one
  have hℓ0 : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hℓ.ne_zero
  have hm0 : (m : ℚ) ≠ 0 := by
    rintro h; exact hm (by rw [Nat.cast_eq_zero.1 h]; exact dvd_zero _)
  refine ⟨(e₁ : ℤ) - e₂, ?_⟩
  have hden : (c.den : ℚ) = (ℓ : ℚ) ^ e₂ * m := by rw [hme]; push_cast; ring
  have key : c * ((ℓ : ℚ) ^ e₂ * m) = (c.num : ℚ) := by rw [← hden]; exact Rat.mul_den_eq_num c
  rw [zpow_sub₀ hℓ0, zpow_natCast, zpow_natCast]
  rcases Int.natAbs_eq c.num with h | h
  · have hv : c / ((ℓ : ℚ) ^ e₁ / (ℓ : ℚ) ^ e₂) = (n : ℚ) * (m : ℚ)⁻¹ := by
      have : (c.num : ℚ) = (ℓ : ℚ) ^ e₁ * n := by rw [h, hne]; push_cast; ring
      rw [this] at key
      have hp : (ℓ : ℚ) ^ e₁ ≠ 0 := pow_ne_zero _ hℓ0
      field_simp at key ⊢
      linear_combination key
    rw [hv]; exact lunit_mul hℓ (lunit_nat hn) (lunit_inv (lunit_nat hm))
  · have hv : c / ((ℓ : ℚ) ^ e₁ / (ℓ : ℚ) ^ e₂) = -((n : ℚ) * (m : ℚ)⁻¹) := by
      have : (c.num : ℚ) = -((ℓ : ℚ) ^ e₁ * n) := by rw [h, hne]; push_cast; ring
      rw [this] at key
      have hp : (ℓ : ℚ) ^ e₁ ≠ 0 := pow_ne_zero _ hℓ0
      field_simp at key ⊢
      linear_combination key
    rw [hv]; exact lunit_neg (lunit_mul hℓ (lunit_nat hn) (lunit_inv (lunit_nat hm)))

theorem lunit_integral {E : Type} [CommRing E] [Algebra ℚ E] {ℓ : ℕ} (hℓ : ℓ.Prime) {r : ℚ}
    (hr : LUnit ℓ r) {d : ℕ} (hd : ¬ ℓ ∣ d) {x y : E} (hx : IsIntegral ℤ ((d : E) * x))
    (hy : IsIntegral ℤ ((d : E) * y)) :
    ∃ d' : ℕ, ¬ ℓ ∣ d' ∧ IsIntegral ℤ ((d' : E) * (algebraMap ℚ E r * x)) ∧
      IsIntegral ℤ ((d' : E) * (algebraMap ℚ E r⁻¹ * y)) := by
  obtain ⟨N, hN, ⟨m₁, h₁⟩, ⟨m₂, h₂⟩⟩ := hr
  refine ⟨d * N, fun h => (hℓ.dvd_mul.1 h).elim hd hN, ?_, ?_⟩
  · have e : ((d * N : ℕ) : E) * (algebraMap ℚ E r * x) = (m₁ : E) * ((d : E) * x) := by
      have : (m₁ : E) = algebraMap ℚ E ((N : ℚ) * r) := by rw [h₁]; simp
      rw [this, map_mul, map_natCast]; push_cast; ring
    rw [e]; exact (isIntegral_intCast m₁).mul hx
  · have e : ((d * N : ℕ) : E) * (algebraMap ℚ E r⁻¹ * y) = (m₂ : E) * ((d : E) * y) := by
      have : (m₂ : E) = algebraMap ℚ E ((N : ℚ) * r⁻¹) := by rw [h₂]; simp
      rw [this, map_mul, map_natCast]; push_cast; ring
    rw [e]; exact (isIntegral_intCast m₂).mul hy

theorem exists_nat_mul_integral {E : Type} [CommRing E] [Algebra ℚ E] [FiniteDimensional ℚ E]
    (z : E) : ∃ D : ℕ, D ≠ 0 ∧ IsIntegral ℤ ((D : E) * z) := by
  have hz : IsAlgebraic ℤ z :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic z)
  obtain ⟨y, hy, hint⟩ := hz.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_ne_zero.2 hy, ?_⟩
  rw [zsmul_eq_mul] at hint
  rcases Int.natAbs_eq y with h | h
  · have := congrArg (Int.cast : ℤ → E) h
    rw [Int.cast_natCast] at this
    rwa [this] at hint
  · have := congrArg (Int.cast : ℤ → E) h
    rw [Int.cast_neg, Int.cast_natCast] at this
    rw [this, neg_mul] at hint
    simpa using hint.neg

theorem ratred : ∀ (E : Type) [CommRing E] [Algebra ℚ E] [FiniteDimensional ℚ E] (τ : E ≃ₐ[ℚ] E) (S : Finset ℕ) (A : Finset E),
    (∀ a : E, IsUnit a → τ a = a →
      (∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ∃ (b x y : E), IsUnit b ∧ a = x * (b * τ b) ∧ b * τ b = y * a ∧
        ∃ d : ℕ, ¬ ℓ ∣ d ∧ IsIntegral ℤ ((d : E) * x) ∧ IsIntegral ℤ ((d : E) * y)) →
      ∃ a₀ ∈ A, ∃ e : Eˣ, a = (e : E) * a₀ * τ e) →
    ∀ a : E, IsUnit a → τ a = a →
    (∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ∃ (c : ℚ) (b x y : E), c ≠ 0 ∧ IsUnit b ∧ a = x * (algebraMap ℚ E c * (b * τ b)) ∧
      algebraMap ℚ E c * (b * τ b) = y * a ∧ ∃ d : ℕ, ¬ ℓ ∣ d ∧ IsIntegral ℤ ((d : E) * x) ∧ IsIntegral ℤ ((d : E) * y)) →
    ∃ a₀ ∈ A, ∃ (r : ℚˣ) (e : Eˣ), a = algebraMap ℚ E (r : ℚ) * ((e : E) * a₀ * τ e) := by
  intro E _ _ _ τ S A hA a ha hτa hloc
  obtain ⟨u, rfl⟩ := ha
  obtain ⟨D₁, hD₁, hi₁⟩ := exists_nat_mul_integral (u : E)
  obtain ⟨D₂, hD₂, hi₂⟩ := exists_nat_mul_integral ((u⁻¹ : Eˣ) : E)
  have hD0 : D₁ * D₂ ≠ 0 := mul_ne_zero hD₁ hD₂
  have hDu : IsIntegral ℤ (((D₁ * D₂ : ℕ) : E) * u) := by
    have e : (((D₁ * D₂ : ℕ) : E) * u) = (D₂ : E) * ((D₁ : E) * u) := by push_cast; ring
    rw [e]; exact (isIntegral_natCast D₂).mul hi₁
  have hDu' : IsIntegral ℤ (((D₁ * D₂ : ℕ) : E) * ((u⁻¹ : Eˣ) : E)) := by
    have e : (((D₁ * D₂ : ℕ) : E) * ((u⁻¹ : Eˣ) : E)) = (D₁ : E) * ((D₂ : E) * ((u⁻¹ : Eˣ) : E)) := by
      push_cast; ring
    rw [e]; exact (isIntegral_natCast D₁).mul hi₂
  choose! c b x y hc hb h₁ h₂ d hd hix hiy using hloc
  have hk : ∀ ℓ, ℓ.Prime → ℓ ∉ S → ∃ k : ℤ, LUnit ℓ (c ℓ / (ℓ : ℚ) ^ k) :=
    fun ℓ hℓ hS => lunit_decomp hℓ (hc ℓ hℓ hS)
  choose! k hk using hk
  let T : Finset ℕ := (D₁ * D₂).primeFactors.filter (· ∉ S)
  have hTmem : ∀ p, p ∈ T ↔ p.Prime ∧ p ∣ D₁ * D₂ ∧ p ∉ S := by
    intro p
    simp only [T, Finset.mem_filter, Nat.mem_primeFactors]
    tauto
  let q : ℚ := ∏ p ∈ T, (p : ℚ) ^ (k p)
  have hq0 : q ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun p hp => zpow_ne_zero _ ?_
    exact_mod_cast ((hTmem p).1 hp).1.ne_zero
  have hqU : ∀ ℓ, ℓ.Prime → ℓ ∉ T → LUnit ℓ q := by
    intro ℓ hℓ hT
    refine Finset.prod_induction _ (LUnit ℓ) (fun _ _ => lunit_mul hℓ) (lunit_one ℓ hℓ) ?_
    intro p hp
    exact lunit_zpow hℓ (lunit_prime hℓ ((hTmem p).1 hp).1 (fun h => hT (h ▸ hp))) _
  have hcqU : ∀ ℓ ∈ T, LUnit ℓ (c ℓ / q) := by
    intro ℓ hℓT
    obtain ⟨hℓ, -, hS⟩ := (hTmem ℓ).1 hℓT
    have e : c ℓ / q = c ℓ / (ℓ : ℚ) ^ (k ℓ) * (∏ p ∈ T.erase ℓ, (p : ℚ) ^ (k p))⁻¹ := by
      simp only [q]
      rw [← Finset.mul_prod_erase T (fun p => (p : ℚ) ^ (k p)) hℓT, div_mul_eq_div_div, div_eq_mul_inv]
    rw [e]
    refine lunit_mul hℓ (hk ℓ hℓ hS) (lunit_inv ?_)
    refine Finset.prod_induction _ (LUnit ℓ) (fun _ _ => lunit_mul hℓ) (lunit_one ℓ hℓ) ?_
    intro p hp
    obtain ⟨hpl, hpT⟩ := Finset.mem_erase.1 hp
    exact lunit_zpow hℓ (lunit_prime hℓ ((hTmem p).1 hpT).1 hpl) _
  have hq1 : algebraMap ℚ E q * algebraMap ℚ E q⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hq0, map_one]
  have ha' : IsUnit (algebraMap ℚ E q⁻¹ * (u : E)) :=
    ((isUnit_iff_ne_zero.2 (inv_ne_zero hq0)).map (algebraMap ℚ E)).mul u.isUnit
  have hτ' : τ (algebraMap ℚ E q⁻¹ * (u : E)) = algebraMap ℚ E q⁻¹ * (u : E) := by
    rw [map_mul, AlgEquiv.commutes, hτa]
  obtain ⟨a₀, ha₀, e, he⟩ := hA _ ha' hτ' (by
    intro ℓ hℓ hS
    by_cases hT : ℓ ∈ T
    · obtain ⟨d', hd', hx', hy'⟩ :=
        lunit_integral hℓ (hcqU ℓ hT) (hd ℓ hℓ hS) (hix ℓ hℓ hS) (hiy ℓ hℓ hS)
      refine ⟨b ℓ, _, _, hb ℓ hℓ hS, ?_, ?_, d', hd', hx', hy'⟩
      · rw [div_eq_mul_inv, map_mul, h₁ ℓ hℓ hS]; ring
      · have hc1 : algebraMap ℚ E (c ℓ) * algebraMap ℚ E (c ℓ)⁻¹ = 1 := by
          rw [← map_mul, mul_inv_cancel₀ (hc ℓ hℓ hS), map_one]
        rw [inv_div, div_eq_mul_inv, map_mul]
        linear_combination (-(b ℓ * τ (b ℓ))) * hc1 + algebraMap ℚ E (c ℓ)⁻¹ * h₂ ℓ hℓ hS -
          (algebraMap ℚ E (c ℓ)⁻¹ * y ℓ * (u : E)) * hq1
    · have hD : ¬ ℓ ∣ D₁ * D₂ := fun h => hT ((hTmem ℓ).2 ⟨hℓ, h, hS⟩)
      obtain ⟨d', hd', hx', hy'⟩ := lunit_integral hℓ (lunit_inv (hqU ℓ hℓ hT)) hD hDu hDu'
      refine ⟨1, _, _, isUnit_one, ?_, ?_, d', hd', hx', hy'⟩
      · simp
      · rw [inv_inv, map_one, mul_one]
        linear_combination (-((u : E) * ((u⁻¹ : Eˣ) : E))) * hq1 - u.mul_inv)
  refine ⟨a₀, ha₀, Units.mk0 q hq0, e, ?_⟩
  rw [← he, Units.val_mk0, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hq0, map_one, one_mul]

end GlobalTheory.RatRed
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvolutionNormClassRemoveRationalFactorStatement
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.involution_norm_class_remove_rational_factor : ∀ (E : Type) [CommRing E] [Algebra ℚ E] [FiniteDimensional ℚ E] (τ : E ≃ₐ[ℚ] E) (S : Finset ℕ) (A : Finset E),
    (∀ a : E, IsUnit a → τ a = a →
      (∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ∃ (b x y : E), IsUnit b ∧ a = x * (b * τ b) ∧ b * τ b = y * a ∧
        ∃ d : ℕ, ¬ ℓ ∣ d ∧ IsIntegral ℤ ((d : E) * x) ∧ IsIntegral ℤ ((d : E) * y)) →
      ∃ a₀ ∈ A, ∃ e : Eˣ, a = (e : E) * a₀ * τ e) →
    ∀ a : E, IsUnit a → τ a = a →
    (∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ∃ (c : ℚ) (b x y : E), c ≠ 0 ∧ IsUnit b ∧ a = x * (algebraMap ℚ E c * (b * τ b)) ∧
      algebraMap ℚ E c * (b * τ b) = y * a ∧ ∃ d : ℕ, ¬ ℓ ∣ d ∧ IsIntegral ℤ ((d : E) * x) ∧ IsIntegral ℤ ((d : E) * y)) →
    ∃ a₀ ∈ A, ∃ (r : ℚˣ) (e : Eˣ), a = algebraMap ℚ E (r : ℚ) * ((e : E) * a₀ * τ e) := by
  first | (exact @GlobalTheory.RatRed.ratred) | (exact GlobalTheory.RatRed.ratred) | (intros; apply GlobalTheory.RatRed.ratred  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormClassFiniteOfReducedRatAlgebra
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormClassFiniteOfReducedRatAlgebra
open scoped TensorProduct Classical

namespace GlobalTheory
namespace ReducedInvolutionNormClass

variable {E : Type} [CommRing E] [Algebra ℚ E] [FiniteDimensional ℚ E]

theorem numberField_quot (I : Ideal E) [I.IsMaximal] :
    @NumberField (E ⧸ I) (Ideal.Quotient.field I) := by
  letI := Ideal.Quotient.field I
  have hfin : Module.Finite ℚ (E ⧸ I) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℚ I).toLinearMap Ideal.Quotient.mk_surjective
  haveI : CharZero (E ⧸ I) := charZero_of_injective_ringHom (algebraMap ℚ (E ⧸ I)).injective
  exact @NumberField.mk _ _ _ (by
    convert hfin
    exact congrArg (fun A : Algebra ℚ (E ⧸ I) => A.toModule) (Subsingleton.elim _ (Ideal.Quotient.algebra ℚ)))

theorem stable_factor (H : (∀ (K : Type) [Field K] [NumberField K] (τ : K ≃+* K), (∀ x, τ (τ x) = x) → ∀ S : Finset ℕ,
    ∃ M : Finset K, ∀ a : K, a ≠ 0 → τ a = a →
    (∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ∃ (b x y : K), b ≠ 0 ∧ a = x * (b * τ b) ∧ b * τ b = y * a ∧
      ∃ d : ℕ, ¬ ℓ ∣ d ∧ IsIntegral ℤ ((d : K) * x) ∧ IsIntegral ℤ ((d : K) * y)) →
    ∃ m ∈ M, ∃ e : K, e ≠ 0 ∧ a = e * m * τ e)) (τ : E ≃ₐ[ℚ] E) (hτ : ∀ x, τ (τ x) = x) (S : Finset ℕ)
    (I : Ideal E) [I.IsMaximal] (hI : ∀ x ∈ I, τ x ∈ I) :
    ∃ M : Finset E, ∀ a : E, IsUnit a → τ a = a →
    (∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ∃ (b x y : E), IsUnit b ∧ a = x * (b * τ b) ∧ b * τ b = y * a ∧
      ∃ d : ℕ, ¬ ℓ ∣ d ∧ IsIntegral ℤ ((d : E) * x) ∧ IsIntegral ℤ ((d : E) * y)) →
    ∃ m ∈ M, ∃ e : E, e ∉ I ∧ a - e * m * τ e ∈ I := by
  letI := Ideal.Quotient.field I
  haveI := numberField_quot I
  have hmap : I = I.map (τ : E ≃+* E) := by
    apply le_antisymm
    · intro x hx
      have : x = (τ : E ≃+* E) (τ x) := (hτ x).symm
      rw [this]; exact Ideal.mem_map_of_mem _ (hI x hx)
    · rw [Ideal.map_le_iff_le_comap]; intro x hx; exact hI x hx
  let τI := Ideal.quotientEquiv I I (τ : E ≃+* E) hmap
  have hτmk : ∀ x, τI (Ideal.Quotient.mk I x) = Ideal.Quotient.mk I (τ x) := fun x => rfl
  have hτI : ∀ z, τI (τI z) = z := by
    intro z; obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [hτmk, hτmk, hτ]
  obtain ⟨M, hM⟩ := H (E ⧸ I) τI hτI S
  let lift : E ⧸ I → E := fun z => Classical.choose (Ideal.Quotient.mk_surjective z)
  have hlift : ∀ z, Ideal.Quotient.mk I (lift z) = z :=
    fun z => Classical.choose_spec (Ideal.Quotient.mk_surjective z)
  refine ⟨M.image lift, fun a ha hτa hyp => ?_⟩
  have ha0 : Ideal.Quotient.mk I a ≠ 0 := (ha.map _).ne_zero
  obtain ⟨m, hm, e', he', hae⟩ := hM (Ideal.Quotient.mk I a) ha0 (by rw [hτmk, hτa]) (by
    intro ℓ hℓ hS
    obtain ⟨b, x, y, hb, h1, h2, d, hd, hx, hy⟩ := hyp ℓ hℓ hS
    refine ⟨Ideal.Quotient.mk I b, Ideal.Quotient.mk I x, Ideal.Quotient.mk I y,
      (hb.map _).ne_zero, ?_, ?_, d, hd, ?_, ?_⟩
    · rw [hτmk, h1, map_mul, map_mul]
    · rw [hτmk, ← map_mul, h2, map_mul]
    · have := hx.map (Ideal.Quotient.mk I).toIntAlgHom
      simp only [map_mul, map_natCast, RingHom.toIntAlgHom_apply] at this
      convert this using 1
      all_goals first | rfl | exact Subsingleton.elim _ _ | (congr; exact Subsingleton.elim _ _)
    · have := hy.map (Ideal.Quotient.mk I).toIntAlgHom
      simp only [map_mul, map_natCast, RingHom.toIntAlgHom_apply] at this
      convert this using 1
      all_goals first | rfl | exact Subsingleton.elim _ _ | (congr; exact Subsingleton.elim _ _))
  obtain ⟨e, rfl⟩ := Ideal.Quotient.mk_surjective e'
  refine ⟨lift m, Finset.mem_image_of_mem _ hm, e, ?_, ?_⟩
  · intro he; exact he' (Ideal.Quotient.eq_zero_iff_mem.2 he)
  · rw [← Ideal.Quotient.eq, map_mul, map_mul, hlift, hae, hτmk]

variable [IsReduced E]

theorem crt (c : MaximalSpectrum E → E) : ∃ u : E, ∀ I : MaximalSpectrum E, u - c I ∈ I.asIdeal := by
  haveI : IsArtinianRing E := IsArtinianRing.of_finite ℚ E
  refine ⟨(IsArtinianRing.equivPi E).symm (fun I => Ideal.Quotient.mk I.asIdeal (c I)), fun I => ?_⟩
  rw [← Ideal.Quotient.eq]
  exact congrFun ((IsArtinianRing.equivPi E).apply_symm_apply
    (fun I => Ideal.Quotient.mk I.asIdeal (c I))) I

theorem eq_zero_of_mem_all (x : E) (h : ∀ I : MaximalSpectrum E, x ∈ I.asIdeal) : x = 0 := by
  haveI : IsArtinianRing E := IsArtinianRing.of_finite ℚ E
  apply (IsArtinianRing.equivPi E).injective
  rw [map_zero]; funext I; exact Ideal.Quotient.eq_zero_iff_mem.2 (h I)

end ReducedInvolutionNormClass


open ReducedInvolutionNormClass in
theorem normClassFinite_of_reduced : (∀ (K : Type) [Field K] [NumberField K] (τ : K ≃+* K), (∀ x, τ (τ x) = x) → ∀ S : Finset ℕ,
    ∃ M : Finset K, ∀ a : K, a ≠ 0 → τ a = a →
    (∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ∃ (b x y : K), b ≠ 0 ∧ a = x * (b * τ b) ∧ b * τ b = y * a ∧
      ∃ d : ℕ, ¬ ℓ ∣ d ∧ IsIntegral ℤ ((d : K) * x) ∧ IsIntegral ℤ ((d : K) * y)) →
    ∃ m ∈ M, ∃ e : K, e ≠ 0 ∧ a = e * m * τ e) →
  ∀ (E : Type) [CommRing E] [Algebra ℚ E] [FiniteDimensional ℚ E] [IsReduced E] (τ : E ≃ₐ[ℚ] E),
    (∀ x, τ (τ x) = x) → ∀ S : Finset ℕ, ∃ A : Finset E, ∀ a : E, IsUnit a → τ a = a →
    (∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ∃ (b x y : E), IsUnit b ∧ a = x * (b * τ b) ∧ b * τ b = y * a ∧
      ∃ d : ℕ, ¬ ℓ ∣ d ∧ IsIntegral ℤ ((d : E) * x) ∧ IsIntegral ℤ ((d : E) * y)) →
    ∃ a₀ ∈ A, ∃ e : Eˣ, a = (e : E) * a₀ * τ e := by
  intro H E _ _ _ _ τ hτ S
  haveI : IsArtinianRing E := IsArtinianRing.of_finite ℚ E
  haveI : Fintype (MaximalSpectrum E) := Fintype.ofFinite _
  let σ : MaximalSpectrum E → MaximalSpectrum E := fun I =>
    ⟨I.asIdeal.comap (τ : E ≃+* E), Ideal.comap_isMaximal_of_surjective _ (τ : E ≃+* E).surjective⟩
  have hσ : ∀ I x, x ∈ (σ I).asIdeal ↔ τ x ∈ I.asIdeal := fun I x => Iff.rfl
  have hσσ : ∀ I, σ (σ I) = I := fun I =>
    MaximalSpectrum.ext (Ideal.ext fun x => by rw [hσ, hσ, hτ])
  have hst : ∀ I, σ I = I → ∀ x ∈ I.asIdeal, τ x ∈ I.asIdeal := by
    intro I h x hx; rw [← hσ, h]; exact hx
  let n := Fintype.equivFin (MaximalSpectrum E)
  let ch : MaximalSpectrum E → Prop := fun I => n I < n (σ I)
  let Mset : MaximalSpectrum E → Finset E := fun I =>
    if h : σ I = I then Classical.choose (stable_factor H τ hτ S I.asIdeal (hst I h)) else {1}
  let F : (MaximalSpectrum E → E) → E := fun f => Classical.choose (crt f)
  have hF : ∀ f I, F f - f I ∈ I.asIdeal := fun f => Classical.choose_spec (crt f)
  refine ⟨(Fintype.piFinset Mset).image F, fun a ha hτa hyp => ?_⟩
  have key : ∀ I, ∃ m ∈ Mset I, ∃ e : E, e ∉ I.asIdeal ∧ (σ I = I → a - e * m * τ e ∈ I.asIdeal) ∧
      (σ I ≠ I → m = 1 ∧ e = if ch I then a else 1) := by
    intro I
    by_cases h : σ I = I
    · obtain ⟨m, hm, e, he, hae⟩ :=
        Classical.choose_spec (stable_factor H τ hτ S I.asIdeal (hst I h)) a ha hτa hyp
      refine ⟨m, by simp only [Mset, dif_pos h]; exact hm, e, he, fun _ => hae, fun h' => absurd h h'⟩
    · refine ⟨1, by simp [Mset, h], if ch I then a else 1, ?_, fun h' => absurd h' h, fun _ => ⟨rfl, rfl⟩⟩
      split_ifs
      · exact fun hmem => I.isMaximal.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem ha)
      · exact fun hmem => I.isMaximal.ne_top ((Ideal.eq_top_iff_one _).2 hmem)
  choose m hm e he hst1 hst2 using key
  obtain ⟨u, hu⟩ := crt e
  have hunit : IsUnit u := by
    by_contra hn
    obtain ⟨J, hJ, huJ⟩ := exists_max_ideal_of_mem_nonunits hn
    apply he ⟨J, hJ⟩
    have := J.sub_mem huJ (hu ⟨J, hJ⟩)
    simpa using this
  refine ⟨F m, Finset.mem_image_of_mem _ (Fintype.mem_piFinset.2 hm), hunit.unit, ?_⟩
  simp only [IsUnit.unit_spec]
  rw [← sub_eq_zero]
  apply eq_zero_of_mem_all
  intro I
  have hu' : ∀ J : MaximalSpectrum E, Ideal.Quotient.mk J.asIdeal u = Ideal.Quotient.mk J.asIdeal (e J) :=
    fun J => Ideal.Quotient.eq.2 (hu J)
  have hF' : Ideal.Quotient.mk I.asIdeal (F m) = Ideal.Quotient.mk I.asIdeal (m I) :=
    Ideal.Quotient.eq.2 (hF m I)
  have hτu : ∀ J, Ideal.Quotient.mk J.asIdeal (τ u) = Ideal.Quotient.mk J.asIdeal (τ (e (σ J))) := by
    intro J; rw [Ideal.Quotient.eq, ← map_sub, ← hσ]; exact hu (σ J)
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_mul, hu', hF', hτu, sub_eq_zero]
  by_cases h : σ I = I
  · rw [h, ← map_mul, ← map_mul, Ideal.Quotient.eq]
    exact hst1 I h
  · obtain ⟨hm1, he1⟩ := hst2 I h
    have hJ : σ (σ I) ≠ σ I := by rw [hσσ]; exact fun h' => h h'.symm
    obtain ⟨_, he2⟩ := hst2 (σ I) hJ
    rw [hm1, he1, he2]
    have hne : n I ≠ n (σ I) := fun h' => h (n.injective h').symm
    by_cases hc : ch I
    · have hc' : ¬ ch (σ I) := by
        show ¬ n (σ I) < n (σ (σ I)); rw [hσσ]; exact not_lt.2 hc.le
      rw [if_pos hc, if_neg hc']
      simp
    · have hc' : ch (σ I) := by
        show n (σ I) < n (σ (σ I)); rw [hσσ]; exact lt_of_le_of_ne (not_lt.1 hc) hne.symm
      rw [if_neg hc, if_pos hc', hτa]
      simp

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormClassFiniteOfReducedRatAlgebraStatement
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normClassFinite_of_reduced_rat_algebra : (∀ (K : Type) [Field K] [NumberField K] (τ : K ≃+* K), (∀ x, τ (τ x) = x) → ∀ S : Finset ℕ,
    ∃ M : Finset K, ∀ a : K, a ≠ 0 → τ a = a →
    (∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ∃ (b x y : K), b ≠ 0 ∧ a = x * (b * τ b) ∧ b * τ b = y * a ∧
      ∃ d : ℕ, ¬ ℓ ∣ d ∧ IsIntegral ℤ ((d : K) * x) ∧ IsIntegral ℤ ((d : K) * y)) →
    ∃ m ∈ M, ∃ e : K, e ≠ 0 ∧ a = e * m * τ e) →
  ∀ (E : Type) [CommRing E] [Algebra ℚ E] [FiniteDimensional ℚ E] [IsReduced E] (τ : E ≃ₐ[ℚ] E),
    (∀ x, τ (τ x) = x) → ∀ S : Finset ℕ, ∃ A : Finset E, ∀ a : E, IsUnit a → τ a = a →
    (∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ∃ (b x y : E), IsUnit b ∧ a = x * (b * τ b) ∧ b * τ b = y * a ∧
      ∃ d : ℕ, ¬ ℓ ∣ d ∧ IsIntegral ℤ ((d : E) * x) ∧ IsIntegral ℤ ((d : E) * y)) →
    ∃ a₀ ∈ A, ∃ e : Eˣ, a = (e : E) * a₀ * τ e := by
  first | (exact @GlobalTheory.normClassFinite_of_reduced) | (exact GlobalTheory.normClassFinite_of_reduced) | (intros; apply GlobalTheory.normClassFinite_of_reduced  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteClassesFixedUnitsModRatNorms
open scoped TensorProduct Classical

namespace GlobalTheory.EtaleCls

theorem classes_mod_rat_norms : ∀ (E : Type) [CommRing E] [Algebra ℚ E] [FiniteDimensional ℚ E] [IsReduced E] (τ : E ≃ₐ[ℚ] E),
    (∀ x, τ (τ x) = x) → ∀ j : E, IsUnit j → τ j = -j → ∀ S : Finset ℕ, ∃ A : Finset E, ∀ a : E, IsUnit a → τ a = a →
    (∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ∃ (c : ℚ) (b x y : E), c ≠ 0 ∧ IsUnit b ∧ a = x * (algebraMap ℚ E c * (b * τ b)) ∧
      algebraMap ℚ E c * (b * τ b) = y * a ∧ ∃ d : ℕ, ¬ ℓ ∣ d ∧ IsIntegral ℤ ((d : E) * x) ∧ IsIntegral ℤ ((d : E) * y)) →
    ∃ a₀ ∈ A, ∃ (r : ℚˣ) (e : Eˣ), a = algebraMap ℚ E (r : ℚ) * ((e : E) * a₀ * τ e) := by
  intro E _ _ _ _ τ hτ _j _ _ S
  obtain ⟨A, hA⟩ := GlobalTheory.T.normClassFinite_of_reduced_rat_algebra GlobalTheory.T.exists_finite_classes_modulo_involutionNorms E τ hτ S
  exact ⟨A, GlobalTheory.T.involution_norm_class_remove_rational_factor E τ S A hA⟩

end GlobalTheory.EtaleCls
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteClassesFixedUnitsModRatNormsStatement
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_classes_fixedUnits_mod_rat_norms : ∀ (E : Type) [CommRing E] [Algebra ℚ E] [FiniteDimensional ℚ E] [IsReduced E] (τ : E ≃ₐ[ℚ] E),
    (∀ x, τ (τ x) = x) → ∀ j : E, IsUnit j → τ j = -j → ∀ S : Finset ℕ, ∃ A : Finset E, ∀ a : E, IsUnit a → τ a = a →
    (∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ∃ (c : ℚ) (b x y : E), c ≠ 0 ∧ IsUnit b ∧ a = x * (algebraMap ℚ E c * (b * τ b)) ∧
      algebraMap ℚ E c * (b * τ b) = y * a ∧ ∃ d : ℕ, ¬ ℓ ∣ d ∧ IsIntegral ℤ ((d : E) * x) ∧ IsIntegral ℤ ((d : E) * y)) →
    ∃ a₀ ∈ A, ∃ (r : ℚˣ) (e : Eˣ), a = algebraMap ℚ E (r : ℚ) * ((e : E) * a₀ * τ e) := by
  first | (exact @GlobalTheory.EtaleCls.classes_mod_rat_norms) | (exact GlobalTheory.EtaleCls.classes_mod_rat_norms) | (intros; apply GlobalTheory.EtaleCls.classes_mod_rat_norms  <;> assumption)
end
