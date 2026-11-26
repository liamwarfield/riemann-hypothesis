module

public import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
public import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
public import Formalism.SharpRestriction.InertJacobiLevels.HostFam
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRootQuadratic
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open scoped TensorProduct

namespace GlobalTheory.LocalNormNegOne

open Polynomial IsLocalRing

theorem exists_sq_sub_finite {k : Type*} [Field k] [Finite k] (h2 : (2 : k) ≠ 0) (D : k) (hD : D ≠ 0) :
    ∃ x y : k, x ^ 2 - (D * y ^ 2 - 4) = 0 := by
  classical
  have := Fintype.ofFinite k
  have hc : ringChar k ≠ 2 := fun h => h2 (by
    have := ringChar.Nat.cast_ringChar (R := k)
    rw [h] at this
    exact_mod_cast this)
  have hodd : Fintype.card k % 2 = 1 := FiniteField.odd_card_of_char_ne_two hc
  obtain ⟨x, y, h⟩ := FiniteField.exists_root_sum_quadratic (R := k) (f := X ^ 2)
    (g := C (-D) * X ^ 2 + C 0 * X + C 4) (degree_X_pow 2) (degree_quadratic (neg_ne_zero.2 hD)) hodd
  refine ⟨x, y, ?_⟩
  simp only [eval_pow, eval_X, eval_add, eval_mul, eval_C] at h
  linear_combination h

variable {R : Type*} [CommRing R] [IsLocalRing R] [HenselianRing R (maximalIdeal R)]

theorem exists_root_quadratic (p q x₀ : R) (h₀ : x₀ ^ 2 + p * x₀ + q ∈ maximalIdeal R)
    (h₁ : IsUnit (2 * x₀ + p)) : ∃ x : R, x ^ 2 + p * x + q = 0 ∧ x - x₀ ∈ maximalIdeal R := by
  obtain ⟨x, hx, hx'⟩ := HenselianRing.is_henselian (I := maximalIdeal R)
    (X ^ 2 + C p * X + C q) (by monicity!) x₀ (by simpa using h₀) (by
      have : (X ^ 2 + C p * X + C q : R[X]).derivative.eval x₀ = 2 * x₀ + p := by
        simp [one_add_one_eq_two]
      rw [this]
      exact h₁.map _)
  exact ⟨x, by simpa [IsRoot] using hx, hx'⟩

theorem exists_eq_neg_one [Finite (ResidueField R)] (t n : R) (hD : IsUnit (t ^ 2 - 4 * n)) :
    ∃ a b : R, a ^ 2 + a * b * t + b ^ 2 * n = -1 := by
  by_cases h2 : IsUnit (2 : R)
  · obtain ⟨u, hu⟩ := h2.exists_left_inv
    have key : ∃ x b : R, x ^ 2 - ((t ^ 2 - 4 * n) * b ^ 2 - 4) = 0 := by
      generalize t ^ 2 - 4 * n = D at hD
      obtain ⟨x, y, h⟩ := exists_sq_sub_finite (k := ResidueField R)
        (by have := (h2.map (residue R)).ne_zero; rwa [map_ofNat] at this) (residue R D) (hD.map _).ne_zero
      obtain ⟨x, rfl⟩ := residue_surjective x
      obtain ⟨y, rfl⟩ := residue_surjective y
      have hm : x ^ 2 - (D * y ^ 2 - 4) ∈ maximalIdeal R := by
        rw [← residue_eq_zero_iff, ← h]
        simp [map_ofNat]
      by_cases hx : IsUnit x
      · obtain ⟨z, hz, -⟩ := exists_root_quadratic 0 (-(D * y ^ 2 - 4)) x
          (by simpa [sub_eq_add_neg] using hm) (by simpa using h2.mul hx)
        exact ⟨z, y, by linear_combination hz⟩
      · have hxm : x ∈ maximalIdeal R := hx
        have hm' : D * y ^ 2 - 4 ∈ maximalIdeal R := by
          have := (maximalIdeal R).sub_mem (Ideal.mul_mem_left _ x hxm) hm
          convert this using 1; ring
        obtain ⟨d, hd⟩ := hD.exists_left_inv
        have hy : IsUnit y := by
          by_contra hy
          have hym : y ∈ maximalIdeal R := hy
          have h4 : (2 * 2 : R) ∈ maximalIdeal R := by
            have := (maximalIdeal R).sub_mem (Ideal.mul_mem_left _ (D * y) hym) hm'
            convert this using 1; ring
          exact h4 (h2.mul h2)
        obtain ⟨z, hz, -⟩ := exists_root_quadratic 0 (-(4 * d)) y
          (by
            have := Ideal.mul_mem_left _ d hm'
            convert this using 1
            linear_combination (-y ^ 2) * hd) (by simpa using h2.mul hy)
        exact ⟨0, z, by linear_combination (-D) * hz - 4 * hd⟩
    obtain ⟨x, b, h⟩ := key
    refine ⟨u * (x - t * b), b, ?_⟩
    linear_combination u ^ 2 * h
      - (u * (x - t * b) * b * t + (b ^ 2 * n + 1) * (u * 2 + 1)) * hu
  · have h2m : (2 : R) ∈ maximalIdeal R := h2
    have ht : IsUnit t := by
      by_contra ht
      have htm : t ∈ maximalIdeal R := ht
      have : t ^ 2 - 4 * n ∈ maximalIdeal R := by
        have := (maximalIdeal R).sub_mem (Ideal.mul_mem_left _ t htm) (Ideal.mul_mem_left _ (2 * n) h2m)
        convert this using 1; ring
      exact this hD
    obtain ⟨c, hc, hc'⟩ := exists_root_quadratic t (2 * n) (-t)
      (by
        have := Ideal.mul_mem_left _ n h2m
        convert this using 1; ring)
      (by
        have : 2 * -t + t = -t := by ring
        rw [this]; exact ht.neg)
    have hcu : IsUnit c := by
      by_contra hcu
      have hcm : c ∈ maximalIdeal R := hcu
      have : t ∈ maximalIdeal R := by
        have := (maximalIdeal R).sub_mem hc' hcm
        convert this using 1; ring
      exact this ht
    obtain ⟨e, he⟩ := hcu.exists_left_inv
    refine ⟨1, 2 * e, ?_⟩
    linear_combination 2 * e ^ 2 * hc - (2 * e * t + 2 * (e * c + 1)) * he

theorem main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (v : HeightOneSpectrum (𝓞 F)) (θ : 𝓞 E), (∃ t : 𝓞 F, ∃ n : 𝓞 F, (θ : E) + star (θ : E) = algebraMap F E t ∧ (θ : E) * star (θ : E) = algebraMap F E n ∧ t ^ 2 - 4 * n ∉ v.asIdeal) → ∃ a b : v.adicCompletionIntegers F, ∃ t n : 𝓞 F, (θ : E) + star (θ : E) = algebraMap F E t ∧ (θ : E) * star (θ : E) = algebraMap F E n ∧ a ^ 2 + a * b * algebraMap (𝓞 F) (v.adicCompletionIntegers F) t + b ^ 2 * algebraMap (𝓞 F) (v.adicCompletionIntegers F) n = -1 := by
  rintro F E _ _ _ _ _ _ - v θ ⟨t, n, h1, h2, h3⟩
  have := GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers v
  have := GlobalTheory.SelfDualGenus.finite_residueField_adicCompletionIntegers v
  have hD := (GlobalTheory.SelfDualGenus.isUnit_algebraMap_iff v _).2 h3
  rw [map_sub, map_pow, map_mul, map_ofNat] at hD
  obtain ⟨a, b, h⟩ := exists_eq_neg_one _ _ hD
  exact ⟨a, b, t, n, h1, h2, h⟩

end GlobalTheory.LocalNormNegOne
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NegOneNormFromCmFieldFiniteAdeles
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open scoped TensorProduct

namespace GlobalTheory

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem cm_fixed_integer (cm : CMData F E) (x : 𝓞 E) (hx : star (x : E) = (x : E)) :
    ∃ t : 𝓞 F, (x : E) = algebraMap F E t := by
  obtain ⟨t, ht⟩ := (cm.fixed x).1 hx
  have hi : IsIntegral ℤ t := by
    have h1 : IsIntegral ℤ (algebraMap F E t) := by
      rw [ht]; exact RingOfIntegers.isIntegral_coe x
    exact (isIntegral_algHom_iff (algebraMap F E).toIntAlgHom (algebraMap F E).injective).1 h1
  exact ⟨⟨t, hi⟩, ht.symm⟩

theorem cm_exists_unit_disc (cm : CMData F E) (M : Ideal (𝓞 F)) (hM : M.IsMaximal) :
    ∃ θ : 𝓞 E, ∃ t : 𝓞 F, ∃ n : 𝓞 F, (θ : E) + star (θ : E) = algebraMap F E t ∧
      (θ : E) * star (θ : E) = algebraMap F E n ∧ t ^ 2 - 4 * n ∉ M := by
  obtain ⟨P, hP, hPM⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 E) M (by
    rw [(RingHom.injective_iff_ker_eq_bot _).1 (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))]
    exact bot_le)
  obtain ⟨θ, s, hs, hθ⟩ := cm.cmUnram.2.2 P hP
  have hs' : (s : E) = star (θ : E) := hs
  obtain ⟨t, ht⟩ := cm_fixed_integer cm (θ + s) (by
    change star ((θ : E) + s) = (θ : E) + s
    rw [hs', star_add, star_star, add_comm])
  obtain ⟨n, hn⟩ := cm_fixed_integer cm (θ * s) (by
    change star ((θ : E) * s) = (θ : E) * s
    rw [hs', star_mul, star_star])
  change (θ : E) + s = _ at ht
  change (θ : E) * s = _ at hn
  refine ⟨θ, t, n, hs' ▸ ht, hs' ▸ hn, fun h => hθ ?_⟩
  rw [← hPM, Ideal.mem_comap] at h
  have e : algebraMap (𝓞 F) (𝓞 E) (t ^ 2 - 4 * n) = (θ - s) ^ 2 := by
    apply RingOfIntegers.coe_injective
    have h1 : ∀ z : 𝓞 F, algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) z) = algebraMap F E (z : F) :=
      fun z => rfl
    rw [h1]
    simp only [map_sub, map_pow, map_mul, map_ofNat]
    change algebraMap F E t ^ 2 - 4 * algebraMap F E n = ((θ : E) - s) ^ 2
    rw [← ht, ← hn]; ring
  rw [e] at h
  exact hP.isPrime.mem_of_pow_mem 2 h

theorem cm_exists_coords (cm : CMData F E) (θ : E) (hθ : θ - star θ ≠ 0) (x : E) :
    ∃ p q : F, x = algebraMap F E p + algebraMap F E q * θ := by
  have hθ' : star θ - θ ≠ 0 := fun h => hθ (by linear_combination -h)
  have hq : star ((x - star x) / (θ - star θ)) = (x - star x) / (θ - star θ) := by
    rw [star_div₀, star_sub, star_sub, star_star, star_star]
    field_simp
    ring
  obtain ⟨q, hq'⟩ := (cm.fixed _).1 hq
  have hp : star (x - (x - star x) / (θ - star θ) * θ) = x - (x - star x) / (θ - star θ) * θ := by
    rw [star_sub, star_mul, hq]
    field_simp
    ring
  obtain ⟨p, hp'⟩ := (cm.fixed _).1 hp
  exact ⟨p, q, by rw [hp', hq']; ring⟩

theorem cm_local_neg_one (cm : CMData F E) (θ : 𝓞 E) (t n : 𝓞 F)
    (ht : (θ : E) + star (θ : E) = algebraMap F E t) (hn : (θ : E) * star (θ : E) = algebraMap F E n)
    (hθ : (θ : E) - star (θ : E) ≠ 0) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ A B : v.adicCompletion F,
      A ^ 2 + A * B * algebraMap F (v.adicCompletion F) t + B ^ 2 * algebraMap F (v.adicCompletion F) n = -1 ∧
      (t ^ 2 - 4 * n ∉ v.asIdeal → A ∈ v.adicCompletionIntegers F ∧ B ∈ v.adicCompletionIntegers F) := by
  have key : ∀ (a b : v.adicCompletionIntegers F) (t n : 𝓞 F),
      a ^ 2 + a * b * algebraMap (𝓞 F) (v.adicCompletionIntegers F) t +
        b ^ 2 * algebraMap (𝓞 F) (v.adicCompletionIntegers F) n = -1 →
      (a : v.adicCompletion F) ^ 2 + a * b * algebraMap F (v.adicCompletion F) t +
        b ^ 2 * algebraMap F (v.adicCompletion F) n = -1 := by
    intro a b t n h
    have h2 := congrArg (fun z : v.adicCompletionIntegers F => (z : v.adicCompletion F)) h
    have h1 : ∀ z : 𝓞 F, ((algebraMap (𝓞 F) (v.adicCompletionIntegers F) z : v.adicCompletionIntegers F) :
        v.adicCompletion F) = algebraMap F (v.adicCompletion F) (z : F) := fun z => rfl
    push_cast at h2
    rw [h1, h1] at h2
    exact h2
  by_cases hd : t ^ 2 - 4 * n ∈ v.asIdeal
  · obtain ⟨θ', h⟩ := cm_exists_unit_disc cm v.asIdeal v.isMaximal
    obtain ⟨a, b, t', n', ht', hn', h⟩ := GlobalTheory.LocalNormNegOne.main F E cm v θ' h
    have h := key a b t' n' h
    obtain ⟨p, q, hpq⟩ := cm_exists_coords cm θ hθ θ'
    have hs : ∀ z : F, star (algebraMap F E z) = algebraMap F E z := fun z => (cm.fixed _).2 ⟨z, rfl⟩
    have hst : star (θ' : E) = algebraMap F E p + algebraMap F E q * star (θ : E) := by
      rw [hpq, star_add, star_mul, hs, hs, mul_comm]
    have e1 : (t' : F) = 2 * p + q * t := by
      apply (algebraMap F E).injective
      simp only [map_add (f := _), map_mul, map_ofNat]
      rw [← ht', ← ht, hst, hpq]; ring
    have e2 : (n' : F) = p ^ 2 + p * q * t + q ^ 2 * n := by
      apply (algebraMap F E).injective
      simp only [map_add (f := _), map_mul, map_pow]
      rw [← hn', ← ht, ← hn, hst, hpq]; ring
    rw [e1, e2] at h
    simp only [map_add (f := _), map_mul, map_pow, map_ofNat] at h
    refine ⟨a + b * algebraMap F _ p, b * algebraMap F _ q, ?_, fun h => (h hd).elim⟩
    linear_combination h
  · obtain ⟨a, b, t', n', ht', hn', h⟩ := GlobalTheory.LocalNormNegOne.main F E cm v θ ⟨t, n, ht, hn, hd⟩
    have h := key a b t' n' h
    have e1 : (t' : F) = t := (algebraMap F E).injective (ht'.symm.trans ht)
    have e2 : (n' : F) = n := (algebraMap F E).injective (hn'.symm.trans hn)
    rw [e1, e2] at h
    exact ⟨a, b, h, fun _ => ⟨a.2, b.2⟩⟩

end

theorem neg_one_norm_finiteAdele : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E), ∃ y : E ⊗[F] FiniteAdeleRing (𝓞 F) F, Formalism.UG.sigR cm.sig (FiniteAdeleRing (𝓞 F) F) y * y = -1 := by
  intro F E _ _ _ _ _ _ cm
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 F)
  obtain ⟨θ, t, n, ht, hn, hd⟩ := cm_exists_unit_disc cm M hM
  have hd0 : t ^ 2 - 4 * n ≠ 0 := fun h => hd (h ▸ M.zero_mem)
  have hθ : (θ : E) - star (θ : E) ≠ 0 := by
    intro h
    apply hd0
    apply RingOfIntegers.coe_injective
    apply (algebraMap F E).injective
    simp only [map_sub, map_pow, map_mul, map_ofNat, map_zero]
    change algebraMap F E t ^ 2 - 4 * algebraMap F E n = 0
    rw [← ht, ← hn]
    linear_combination ((θ : E) - star (θ : E)) * h
  choose A B hAB hint using cm_local_neg_one cm θ t n ht hn hθ
  have hfin : {v : HeightOneSpectrum (𝓞 F) | t ^ 2 - 4 * n ∈ v.asIdeal}.Finite := by
    have := Ideal.finite_factors (R := 𝓞 F) (I := Ideal.span {t ^ 2 - 4 * n})
      (by simpa only [Submodule.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot] using hd0)
    simpa only [Ideal.dvd_span_singleton] using this
  have hev : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, t ^ 2 - 4 * n ∉ v.asIdeal := by
    simpa only [Filter.eventually_cofinite, not_not] using hfin
  let a : FiniteAdeleRing (𝓞 F) F := ⟨A, hev.mono fun v hv => (hint v hv).1⟩
  let b : FiniteAdeleRing (𝓞 F) F := ⟨B, hev.mono fun v hv => (hint v hv).2⟩
  have hab : a ^ 2 + a * b * algebraMap F (FiniteAdeleRing (𝓞 F) F) t +
      b ^ 2 * algebraMap F (FiniteAdeleRing (𝓞 F) F) n = -1 := by
    apply FiniteAdeleRing.ext
    intro v
    have := hAB v
    rw [sq, sq] at this ⊢
    exact this
  let L : E →ₐ[F] E ⊗[F] FiniteAdeleRing (𝓞 F) F := Algebra.TensorProduct.includeLeft
  let Rr : FiniteAdeleRing (𝓞 F) F →ₐ[F] E ⊗[F] FiniteAdeleRing (𝓞 F) F :=
    Algebra.TensorProduct.includeRight
  refine ⟨Rr a + L θ * Rr b, ?_⟩
  have hL : ∀ x, Formalism.UG.sigR cm.sig (FiniteAdeleRing (𝓞 F) F) (L x) = L (star x) := fun x => by
    simp [Formalism.UG.sigR, L, CMData.sig, starRingEnd_apply]
  have hR : ∀ x, Formalism.UG.sigR cm.sig (FiniteAdeleRing (𝓞 F) F) (Rr x) = Rr x := fun x => by
    simp [Formalism.UG.sigR, Rr]
  have h1 := congrArg L ht
  have h2 := congrArg L hn
  have h3 := congrArg Rr hab
  simp only [map_add (f := _), map_mul, map_pow, map_neg, map_one, AlgHom.commutes] at h1 h2 h3
  rw [map_add (f := _), map_mul, hL, hR, hR]
  rw [← h1, ← h2] at h3
  linear_combination h3

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NegOneNormFromCmFieldFiniteAdelesStatement
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.neg_one_norm_from_cmField_finiteAdeles : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E), ∃ y : E ⊗[F] FiniteAdeleRing (𝓞 F) F, Formalism.UG.sigR cm.sig (FiniteAdeleRing (𝓞 F) F) y * y = -1 := by
  first | exact @GlobalTheory.neg_one_norm_finiteAdele | exact GlobalTheory.neg_one_norm_finiteAdele | (intros; apply GlobalTheory.neg_one_norm_finiteAdele <;> assumption)
end
