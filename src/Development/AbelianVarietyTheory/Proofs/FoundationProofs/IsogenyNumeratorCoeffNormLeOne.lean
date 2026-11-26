module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsogenyNumeratorCoeffNormLeOne
open Polynomial

namespace GlobalTheory

theorem exists_gauss_size_polynomial (K : Type) [NormedField K] [IsUltrametricDist K] :
    ∃ G : K[X] → ℝ, (∀ p, 0 ≤ G p) ∧ (∀ p i, ‖p.coeff i‖ ≤ G p) ∧
      (∀ p r, (∀ i, ‖p.coeff i‖ ≤ r) → G p ≤ r) ∧
      (∀ p q, G (p * q) = G p * G q) ∧ (∀ p q, G (p + q) ≤ max (G p) (G q)) ∧
      (∀ a, G (C a) = ‖a‖) ∧ G X = 1 := by
  let v : AbsoluteValue K ℝ := NormedField.toAbsoluteValue K
  have hv : ∀ a, v a = ‖a‖ := fun _ => rfl
  have hna : IsNonarchimedean v := fun a b => IsUltrametricDist.norm_add_le_max a b
  refine ⟨gaussNorm v 1, fun p => gaussNorm_nonneg v p zero_le_one, fun p i => ?_,
    fun p r hr => ?_, fun p q => gaussNorm_mul hna one_pos p q,
    fun p q => isNonarchimedean_gaussNorm v hna zero_le_one p q, fun a => ?_, ?_⟩
  · simpa [hv] using le_gaussNorm v p zero_le_one i
  · obtain ⟨i, hi⟩ := exists_eq_gaussNorm v 1 p
    rw [hi, hv, one_pow, mul_one]
    exact hr i
  · rw [gaussNorm_C, hv]
  · rw [← monomial_one_one_eq_X, gaussNorm_monomial, hv]
    simp

theorem isogeny_numerator_coeff_norm_le_one :
    ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (A B A' B' : K) (n h : K[X]),
      ‖A‖ ≤ 1 → ‖B‖ ≤ 1 → ‖A'‖ ≤ 1 → ‖B'‖ ≤ 1 → (∀ i, ‖h.coeff i‖ ≤ 1) →
      (X ^ 3 + C A * X + C B) * (derivative n * h - 2 * n * derivative h) ^ 2
        = n ^ 3 + C A' * n * h ^ 4 + C B' * h ^ 6 → ∀ i, ‖n.coeff i‖ ≤ 1 := by
  intro K _ _ A B A' B' n h hA hB hA' hB' hh heq
  obtain ⟨G, h0, hle, hub, hmul, hadd, hC, hX⟩ := exists_gauss_size_polynomial K
  have hone : G 1 = 1 := by simpa using hC 1
  have hpow : ∀ p (k : ℕ), G (p ^ k) = G p ^ k := by
    intro p k
    induction k with
    | zero => simpa using hone
    | succ k ih => rw [pow_succ, hmul, ih, pow_succ]
  have hneg : ∀ p, G (-p) ≤ G p := fun p =>
    hub _ _ fun i => by rw [coeff_neg, norm_neg]; exact hle p i
  have hadd' : ∀ p q r, G p ≤ r → G q ≤ r → G (p + q) ≤ r := fun p q r hp hq =>
    (hadd p q).trans (max_le hp hq)
  have hsub : ∀ p q r, G p ≤ r → G q ≤ r → G (p - q) ≤ r := fun p q r hp hq => by
    rw [sub_eq_add_neg]
    exact hadd' _ _ _ hp ((hneg q).trans hq)
  have hmul' : ∀ p q r s, G p ≤ r → G q ≤ s → G (p * q) ≤ r * s := fun p q r s hp hq => by
    rw [hmul]
    exact mul_le_mul hp hq (h0 q) ((h0 p).trans hp)
  have hpow' : ∀ p r (k : ℕ), G p ≤ r → G (p ^ k) ≤ r ^ k := fun p r k hp => by
    rw [hpow]
    exact pow_le_pow_left₀ (h0 p) hp k
  have hder : ∀ p, G (derivative p) ≤ G p := fun p =>
    hub _ _ fun i => by
      rw [coeff_derivative, norm_mul]
      have h1 : ‖((i : K) + 1)‖ ≤ 1 := by
        exact_mod_cast IsUltrametricDist.norm_natCast_le_one K (i + 1)
      calc ‖p.coeff (i + 1)‖ * ‖((i : K) + 1)‖ ≤ G p * 1 :=
            mul_le_mul (hle p _) h1 (norm_nonneg _) (h0 p)
        _ = G p := mul_one _
  have hh1 : G h ≤ 1 := hub _ _ hh
  suffices hn : G n ≤ 1 from fun i => (hle n i).trans hn
  by_contra hg
  push Not at hg
  set g := G n with hgdef
  have hX1 : G X ≤ 1 := hX.le
  have hcub : G (X ^ 3 + C A * X + C B) ≤ 1 := by
    refine hadd' _ _ _ (hadd' _ _ _ ?_ ?_) ?_
    · simpa using hpow' X 1 3 hX1
    · simpa using hmul' (C A) X 1 1 (by rw [hC]; exact hA) hX1
    · rw [hC]; exact hB
  have h2n : G (2 * n) ≤ g := by
    rw [two_mul]
    exact hadd' _ _ _ le_rfl le_rfl
  have hW : G (derivative n * h - 2 * n * derivative h) ≤ g := by
    refine hsub _ _ _ ?_ ?_
    · simpa using hmul' _ _ g 1 (hder n) hh1
    · simpa using hmul' _ _ g 1 h2n ((hder h).trans hh1)
  have hL : G ((X ^ 3 + C A * X + C B) * (derivative n * h - 2 * n * derivative h) ^ 2)
      ≤ g ^ 2 := by
    simpa using hmul' _ _ 1 (g ^ 2) hcub (hpow' _ g 2 hW)
  have hgg : g ≤ g ^ 2 := by nlinarith
  have h1g : 1 ≤ g ^ 2 := hg.le.trans hgg
  have hA2 : G (C A' * n * h ^ 4) ≤ g ^ 2 := by
    refine le_trans ?_ hgg
    simpa using hmul' _ _ (1 * g) (1 ^ 4)
      (hmul' (C A') n 1 g (by rw [hC]; exact hA') le_rfl) (hpow' h 1 4 hh1)
  have hB2 : G (C B' * h ^ 6) ≤ g ^ 2 := by
    refine le_trans ?_ h1g
    simpa using hmul' (C B') _ 1 (1 ^ 6) (by rw [hC]; exact hB') (hpow' h 1 6 hh1)
  have hn3 : n ^ 3 = (X ^ 3 + C A * X + C B) * (derivative n * h - 2 * n * derivative h) ^ 2
      - C A' * n * h ^ 4 - C B' * h ^ 6 := by
    rw [heq]; ring
  have h3 : G (n ^ 3) ≤ g ^ 2 := by
    rw [hn3]
    exact hsub _ _ _ (hsub _ _ _ hL hA2) hB2
  rw [hpow, ← hgdef] at h3
  nlinarith

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HermitianLatticeNormOneOfNormOneModPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HermitianLatticeNormOneOfNormOneModPrime
namespace GlobalTheory

theorem exists_lattice_norm_one_of_norm_one_mod (K V : Type) [Field K] [CharZero K]
    [AddCommGroup V] [Module K V] (σ : K →+* K) (h : V →ₗ[K] V →ₛₗ[σ] K) (p d : ℕ) (θ : K)
    (O : Subring K) (L : AddSubgroup V) (hp : p.Prime) (_hd : d.Prime) (hθ : θ ^ 2 = -(d : K))
    (hσ : σ θ = -θ) (hK : ∀ x : K, ∃ a b : ℚ, x = (a : K) + (b : K) * θ)
    (hOσ : ∀ x ∈ O, σ x ∈ O) (hω : (1 + θ) / 2 ∈ O)
    (hO : ∀ r : ℚ, (r : K) ∈ O ↔ padicNorm p r ≤ 1) (hh : ∀ x y : V, h y x = σ (h x y))
    (_hdef : ∀ x : V, h x x = 0 → x = 0) (hL : ∀ a ∈ O, ∀ x ∈ L, a • x ∈ L)
    (_hint : ∀ x ∈ L, ∀ y ∈ L, h x y ∈ O) (hfull : ∀ x : V, ∃ m : ℕ, (p : K) ^ m • x ∈ L)
    (W : Submodule K V) (he : ∃ e ∈ W, h e e = 1)
    (hy : ∃ y ∈ L, y ∈ W ∧ ∃ u : ℚ, h y y = (u : K) ∧ padicNorm p (u - 1) < 1) :
    ∃ z ∈ L, z ∈ W ∧ h z z = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨e, heW, hee⟩ := he
  obtain ⟨y₀, hy₀L, hy₀W, u₀, hu₀, hr⟩ := hy
  have hσω : σ ((1 + θ) / 2) = (1 - θ) / 2 := by
    rw [map_div₀, map_add (f := _), map_one, hσ, map_ofNat, sub_eq_add_neg]
  have hn : padicNorm p ((1 + d) / 4) ≤ 1 := by
    rw [← hO]
    have := O.mul_mem hω (hOσ _ hω)
    rw [hσω] at this
    convert this using 1
    push_cast
    linear_combination (1 / 4 : K) * hθ

  have step : ∀ y ∈ L, y ∈ W → ∀ u : ℚ, h y y = (u : K) → padicNorm p (u - 1) ≤ 1 →
      ∃ y' ∈ L, y' ∈ W ∧ ∃ u' : ℚ, h y' y' = (u' : K) ∧
        padicNorm p (u' - 1) ≤ padicNorm p (u - 1) * padicNorm p (u - 1) := by
    intro y hyL hyW u hu hu1
    have hc : ((1 - u : ℚ) : K) ∈ O := by
      rw [hO, ← padicNorm.neg]; simpa using hu1
    have hu' : padicNorm p u ≤ 1 := by
      have := padicNorm.nonarchimedean (p := p) (q := u - 1) (r := 1)
      rw [sub_add_cancel, padicNorm.one] at this
      exact this.trans (max_le hu1 le_rfl)
    refine ⟨(1 + ((1 - u : ℚ) : K) * ((1 + θ) / 2)) • y,
      hL _ (O.add_mem O.one_mem (O.mul_mem hc hω)) y hyL, W.smul_mem _ hyW,
      1 + (u - 1) * (u - 1) * ((1 + d) / 4 * u - 1), ?_, ?_⟩
    · simp only [map_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hu, map_add (f := _), map_mul,
        map_one, hσω, map_ratCast]
      push_cast
      linear_combination (-(1 - (u : K)) ^ 2 * u / 4) * hθ
    · rw [add_sub_cancel_left, padicNorm.mul, padicNorm.mul]
      have h1 : padicNorm p ((1 + d) / 4 * u - 1) ≤ 1 := by
        refine padicNorm.sub.trans (max_le ?_ (by rw [padicNorm.one]))
        rw [padicNorm.mul]
        exact mul_le_one₀ hn (padicNorm.nonneg _) hu'
      exact mul_le_of_le_one_right
        (mul_nonneg (padicNorm.nonneg _) (padicNorm.nonneg _)) h1
  have hr0 : 0 ≤ padicNorm p (u₀ - 1) := padicNorm.nonneg _
  have iter : ∀ k : ℕ, ∃ y ∈ L, y ∈ W ∧ ∃ u : ℚ, h y y = (u : K) ∧
      padicNorm p (u - 1) ≤ padicNorm p (u₀ - 1) ^ (k + 1) := by
    intro k
    induction k with
    | zero => exact ⟨y₀, hy₀L, hy₀W, u₀, hu₀, by simp⟩
    | succ k ih =>
      obtain ⟨y, hyL, hyW, u, hu, hk⟩ := ih
      have hk1 : padicNorm p (u - 1) ≤ padicNorm p (u₀ - 1) :=
        hk.trans (by
          rw [pow_succ]
          exact mul_le_of_le_one_left hr0 (pow_le_one₀ hr0 hr.le))
      obtain ⟨y', hy'L, hy'W, u', hu', hle⟩ := step y hyL hyW u hu (hk1.trans hr.le)
      refine ⟨y', hy'L, hy'W, u', hu', hle.trans ?_⟩
      rw [pow_succ _ (k + 1)]
      exact mul_le_mul hk hk1 (padicNorm.nonneg _) (pow_nonneg hr0 _)
  obtain ⟨m, hm⟩ := hfull e
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hpos : ∀ q : ℚ, q ≠ 0 → 0 < padicNorm p q := fun q hq =>
    lt_of_le_of_ne (padicNorm.nonneg _) (padicNorm.nonzero hq).symm
  have hP0 : 0 < padicNorm p ((p : ℚ) ^ m) := hpos _ (pow_ne_zero _ hp0)
  have hP1 : padicNorm p ((p : ℚ) ^ m) ≤ 1 := by
    have := padicNorm.of_nat (p := p) (p ^ m)
    rwa [Nat.cast_pow] at this
  have h40 : 0 < padicNorm p 4 := hpos _ (by norm_num)
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (mul_pos h40 hP0) hr
  obtain ⟨y, hyL, hyW, u, hu, hyk⟩ := iter k
  have hsmall : padicNorm p (u - 1) < padicNorm p 4 * padicNorm p ((p : ℚ) ^ m) := by
    refine lt_of_le_of_lt (hyk.trans ?_) hk
    rw [pow_succ]
    exact mul_le_of_le_one_right (pow_nonneg hr0 _) hr.le

  have secant : ∀ y ∈ L, y ∈ W → h y y = (u : K) → ∀ T : ℚ, h e y + h y e = (T : K) →
      padicNorm p 4 ≤ padicNorm p (u + 1 - T) → ∃ z ∈ L, z ∈ W ∧ h z z = 1 := by
    intro y hyL hyW hu T hT hQ
    have hQpos : 0 < padicNorm p (u + 1 - T) := h40.trans_le hQ
    have hQ0 : u + 1 - T ≠ 0 := by
      intro h0; rw [h0, padicNorm.zero] at hQpos; exact lt_irrefl _ hQpos
    set t : ℚ := (1 - u) / ((u + 1 - T) * (p : ℚ) ^ m) with ht
    have htO : (t : K) ∈ O := by
      rw [hO, ht, padicNorm.div, padicNorm.mul, div_le_one (mul_pos hQpos hP0), ← padicNorm.neg,
        neg_sub]
      exact hsmall.le.trans (mul_le_mul_of_nonneg_right hQ hP0.le)
    have hpO : (p : K) ^ m ∈ O := O.pow_mem (natCast_mem O p) m
    have hs : t * (p : ℚ) ^ m * (u + 1 - T) = 1 - u := by
      rw [ht]; field_simp
    have hs' : (t : K) * (p : K) ^ m * (u + 1 - T) = 1 - u := by
      exact_mod_cast congrArg (fun q : ℚ => (q : K)) hs
    refine ⟨y + ((t : K) * (p : K) ^ m) • y - (t : K) • ((p : K) ^ m • e),
      L.sub_mem (L.add_mem hyL (hL _ (O.mul_mem htO hpO) y hyL)) (hL _ htO _ hm),
      W.sub_mem (W.add_mem hyW (W.smul_mem _ hyW)) (W.smul_mem _ (W.smul_mem _ heW)), ?_⟩
    simp only [map_smul, map_smulₛₗ, map_add (f := _), map_sub, LinearMap.smul_apply, LinearMap.add_apply,
      LinearMap.sub_apply, smul_eq_mul, hu, hee, map_mul, map_pow, map_ratCast, map_natCast,
      RingHom.id_apply]
    linear_combination (1 + (t : K) * (p : K) ^ m) * hs' -
      ((t : K) * (p : K) ^ m) * (1 + (t : K) * (p : K) ^ m) * hT
  obtain ⟨T, hT⟩ : ∃ T : ℚ, h e y + h y e = (T : K) := by
    obtain ⟨a, b, hab⟩ := hK (h e y)
    refine ⟨2 * a, ?_⟩
    rw [hh e y, hab, map_add (f := _), map_mul, map_ratCast, map_ratCast, hσ]
    push_cast
    ring
  by_cases hQ : padicNorm p 4 ≤ padicNorm p (u + 1 - T)
  · exact secant y hyL hyW hu T hT hQ
  · refine secant (-y) (L.neg_mem hyL) (W.neg_mem hyW) (by simpa using hu) (-T)
      (by
        simp only [map_neg, LinearMap.neg_apply]
        push_cast
        linear_combination -hT) ?_
    by_contra hQ'
    push Not at hQ hQ'
    have h2 : padicNorm p (2 * (u - 1)) < padicNorm p 4 := by
      rw [padicNorm.mul]
      have h21 : padicNorm p 2 ≤ 1 := by simpa using padicNorm.of_nat (p := p) 2
      refine lt_of_le_of_lt (mul_le_of_le_one_left (padicNorm.nonneg _) h21) ?_
      exact hsmall.trans_le (mul_le_of_le_one_right h40.le hP1)
    have h3 : padicNorm p 4 < padicNorm p 4 := by
      calc padicNorm p 4
          = padicNorm p ((u + 1 - T) + (u + 1 - -T) - 2 * (u - 1)) := by congr 1; ring
        _ ≤ _ := padicNorm.sub
        _ < padicNorm p 4 :=
          max_lt (lt_of_le_of_lt padicNorm.nonarchimedean (max_lt hQ hQ')) h2
    exact lt_irrefl _ h3

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HermitianLatticeNormOneOfNormOneModPrimeStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianLattice_norm_one_of_norm_one_mod_prime : ∀ (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] (σ : K →+* K) (h : V →ₗ[K] V →ₛₗ[σ] K) (p d : ℕ) (θ : K) (O : Subring K) (L : AddSubgroup V), p.Prime → d.Prime → θ ^ 2 = -(d : K) → σ θ = -θ → (∀ x : K, ∃ a b : ℚ, x = (a : K) + (b : K) * θ) → (∀ x ∈ O, σ x ∈ O) → (1 + θ) / 2 ∈ O → (∀ r : ℚ, (r : K) ∈ O ↔ padicNorm p r ≤ 1) → (∀ x y : V, h y x = σ (h x y)) → (∀ x : V, h x x = 0 → x = 0) → (∀ a ∈ O, ∀ x ∈ L, a • x ∈ L) → (∀ x ∈ L, ∀ y ∈ L, h x y ∈ O) → (∀ x : V, ∃ m : ℕ, (p : K) ^ m • x ∈ L) → ∀ W : Submodule K V, (∃ e ∈ W, h e e = 1) → (∃ y ∈ L, y ∈ W ∧ ∃ u : ℚ, h y y = (u : K) ∧ padicNorm p (u - 1) < 1) → ∃ z ∈ L, z ∈ W ∧ h z z = 1 := by
  first | exact @GlobalTheory.exists_lattice_norm_one_of_norm_one_mod | exact GlobalTheory.exists_lattice_norm_one_of_norm_one_mod | (intros; apply GlobalTheory.exists_lattice_norm_one_of_norm_one_mod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TorsionPointsDistinctModMaximalIdeal
namespace GlobalTheory

open WeierstrassCurve WeierstrassCurve.Affine

namespace TorsionUnit

variable {K : Type} [NormedField K] [IsUltrametricDist K]

end TorsionUnit

section
variable {K : Type} [NormedField K] [IsUltrametricDist K]

private lemma short_negY_eq (A B x y : K) :
    ((⟨0, 0, 0, A, B⟩ : WeierstrassCurve K).toAffine).negY x y = -y := by
  simp [Affine.negY]

private lemma short_addX_eq (A B x₁ x₂ l : K) :
    ((⟨0, 0, 0, A, B⟩ : WeierstrassCurve K).toAffine).addX x₁ x₂ l = l ^ 2 - x₁ - x₂ := by
  simp [Affine.addX]

private lemma norm_add_le_one_of_le_one {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    ‖a + b‖ ≤ 1 :=
  (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)

private lemma norm_le_one_of_norm_sq_sub_le_one {l s : K} (h : ‖l ^ 2 - s‖ ≤ 1) (hs : ‖s‖ ≤ 1) :
    ‖l‖ ≤ 1 := by
  have hsq : ‖l ^ 2‖ ≤ 1 := by
    have := norm_add_le_one_of_le_one h hs
    rwa [sub_add_cancel] at this
  rw [norm_pow] at hsq
  exact (pow_le_one_iff_of_nonneg (norm_nonneg l) two_ne_zero).mp hsq

private lemma norm_mul_le_one_of_le_one {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    ‖a * b‖ ≤ 1 := by
  rw [norm_mul]
  exact mul_le_one₀ ha (norm_nonneg _) hb

private lemma short_equation_of_nonsingular {A B x y : K}
    (h : (⟨0, 0, 0, A, B⟩ : WeierstrassCurve K).toAffine.Nonsingular x y) :
    y ^ 2 = x ^ 3 + A * x + B := by
  have := h.1
  simp [Affine.equation_iff] at this
  linear_combination this

private lemma norm_sub_le_one_of_le_one {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    ‖a - b‖ ≤ 1 := by
  rw [sub_eq_add_neg]
  exact norm_add_le_one_of_le_one ha (by rwa [norm_neg])

private lemma norm_ofNat_le_one (n : ℕ) [n.AtLeastTwo] : ‖(OfNat.ofNat n : K)‖ ≤ 1 := by
  exact_mod_cast IsUltrametricDist.norm_natCast_le_one K n

private lemma norm_y_eq_one_of_nsmul_eq_zero [DecidableEq K] {A B : K} {N : ℕ} (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1)
    (h2 : ‖(2 : K)‖ = 1) (hD : ‖4 * A ^ 3 + 27 * B ^ 2‖ = 1) (hN : Odd N)
    (hT : ∀ (x y : K) (h : (⟨0, 0, 0, A, B⟩ : WeierstrassCurve K).toAffine.Nonsingular x y),
      N • (WeierstrassCurve.Affine.Point.some x y h) = 0 → ‖x‖ ≤ 1)
    {x y : K} (h : (⟨0, 0, 0, A, B⟩ : WeierstrassCurve K).toAffine.Nonsingular x y)
    (hP : N • (WeierstrassCurve.Affine.Point.some x y h) = 0) : ‖y‖ = 1 := by
  have hx := hT _ _ h hP
  have h2ne : (2 : K) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at h2
    exact zero_ne_one h2
  have hy : y ≠ ((⟨0, 0, 0, A, B⟩ : WeierstrassCurve K).toAffine).negY x y := by
    intro hyy
    have hneg : -Point.some x y h = Point.some x y h := by
      rw [Point.neg_some]
      congr 1
      exact hyy.symm
    obtain ⟨k, rfl⟩ := hN
    have hPP : Point.some x y h + Point.some x y h = 0 := by
      nth_rewrite 1 [← hneg]
      exact neg_add_cancel _
    rw [add_smul, one_smul, mul_comm, mul_smul, two_smul, hPP, smul_zero, zero_add] at hP
    simp at hP
  have hy0 : y ≠ 0 := by
    intro h0
    apply hy
    rw [short_negY_eq, h0, neg_zero]
  have hdbl := Point.add_of_Y_ne (h₁ := h) (h₂ := h) hy
  have h3 := hT _ _ _ (by rw [← hdbl, smul_add, hP, add_zero])
  rw [short_addX_eq] at h3
  set l := ((⟨0, 0, 0, A, B⟩ : WeierstrassCurve K).toAffine).slope x x y y with hl
  have hlrel : l * (2 * y) = 3 * x ^ 2 + A := by
    rw [hl, slope_of_Y_ne rfl hy, short_negY_eq, sub_neg_eq_add, ← two_mul,
      div_mul_cancel₀ _ (mul_ne_zero h2ne hy0)]
    simp
  have hlle : ‖l‖ ≤ 1 :=
    norm_le_one_of_norm_sq_sub_le_one (s := x + x) (by rw [← sub_sub]; exact h3)
      (norm_add_le_one_of_le_one hx hx)
  have hder : ‖3 * x ^ 2 + A‖ ≤ ‖y‖ := by
    rw [← hlrel, norm_mul, norm_mul, h2, one_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) hlle
  have hx2 : ‖x ^ 2‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx
  have hx3 : ‖x ^ 3‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx
  have hf : ‖x ^ 3 + A * x + B‖ ≤ 1 :=
    norm_add_le_one_of_le_one (norm_add_le_one_of_le_one hx3 (norm_mul_le_one_of_le_one hA hx)) hB
  have hyeq := short_equation_of_nonsingular h
  have hyle : ‖y‖ ≤ 1 := by
    have : ‖y‖ ^ 2 ≤ 1 := by rw [← norm_pow, hyeq]; exact hf
    exact (pow_le_one_iff_of_nonneg (norm_nonneg y) two_ne_zero).mp this
  refine le_antisymm hyle (not_lt.mp fun hlt => ?_)
  have hflt : ‖x ^ 3 + A * x + B‖ < 1 := by
    rw [← hyeq, norm_pow]
    nlinarith [norm_nonneg y]
  have hderlt : ‖3 * x ^ 2 + A‖ < 1 := hder.trans_lt hlt
  have ha : ‖27 * B - 18 * A * x‖ ≤ 1 :=
    norm_sub_le_one_of_le_one (norm_mul_le_one_of_le_one (norm_ofNat_le_one 27) hB)
      (norm_mul_le_one_of_le_one (norm_mul_le_one_of_le_one (norm_ofNat_le_one 18) hA) hx)
  have hb : ‖6 * A * x ^ 2 - 9 * B * x + 4 * A ^ 2‖ ≤ 1 := by
    refine norm_add_le_one_of_le_one (norm_sub_le_one_of_le_one ?_ ?_) ?_
    · exact norm_mul_le_one_of_le_one (norm_mul_le_one_of_le_one (norm_ofNat_le_one 6) hA) hx2
    · exact norm_mul_le_one_of_le_one (norm_mul_le_one_of_le_one (norm_ofNat_le_one 9) hB) hx
    · refine norm_mul_le_one_of_le_one (norm_ofNat_le_one 4) ?_
      rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hA
  have hid : 4 * A ^ 3 + 27 * B ^ 2 = (27 * B - 18 * A * x) * (x ^ 3 + A * x + B) +
      (6 * A * x ^ 2 - 9 * B * x + 4 * A ^ 2) * (3 * x ^ 2 + A) := by ring
  have hlt1 : ‖4 * A ^ 3 + 27 * B ^ 2‖ < 1 := by
    rw [hid]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
    · rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) ha).trans_lt hflt
    · rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) hb).trans_lt hderlt
  rw [hD] at hlt1
  exact lt_irrefl _ hlt1

private lemma norm_sub_y_le_norm_sub_x_of_torsion [DecidableEq K] {A B : K} {N : ℕ}
    (hT : ∀ (x y : K) (h : (⟨0, 0, 0, A, B⟩ : WeierstrassCurve K).toAffine.Nonsingular x y),
      N • (WeierstrassCurve.Affine.Point.some x y h) = 0 → ‖x‖ ≤ 1)
    {x₁ y₁ x₂ y₂ : K} (h₁ : (⟨0, 0, 0, A, B⟩ : WeierstrassCurve K).toAffine.Nonsingular x₁ y₁)
    (h₂ : (⟨0, 0, 0, A, B⟩ : WeierstrassCurve K).toAffine.Nonsingular x₂ y₂)
    (hP : N • (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁) = 0)
    (hQ : N • (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂) = 0) (hx : x₁ ≠ x₂) :
    ‖y₁ - y₂‖ ≤ ‖x₁ - x₂‖ := by
  have hsum := Point.add_of_X_ne (h₁ := h₁) (h₂ := h₂) hx
  have h3 := hT _ _ _ (by rw [← hsum, smul_add, hP, hQ, add_zero])
  rw [short_addX_eq, slope_of_X_ne hx] at h3
  have hl : ‖(y₁ - y₂) / (x₁ - x₂)‖ ≤ 1 :=
    norm_le_one_of_norm_sq_sub_le_one (s := x₁ + x₂) (by rw [← sub_sub]; exact h3)
      (norm_add_le_one_of_le_one (hT _ _ h₁ hP) (hT _ _ h₂ hQ))
  have hne : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
  have : y₁ - y₂ = (y₁ - y₂) / (x₁ - x₂) * (x₁ - x₂) := by field_simp
  rw [this, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) hl

theorem _root_.GlobalTheory.torsion_points_distinct_mod_maximal_ideal : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [DecidableEq K] (A B : K) (N : ℕ), ‖A‖ ≤ 1 → ‖B‖ ≤ 1 → ‖(2 : K)‖ = 1 → ‖4 * A ^ 3 + 27 * B ^ 2‖ = 1 → Odd N → (∀ (x y : K) (h : (⟨0, 0, 0, A, B⟩ : WeierstrassCurve K).toAffine.Nonsingular x y), N • (WeierstrassCurve.Affine.Point.some x y h) = 0 → ‖x‖ ≤ 1) → ∀ (x y : K) (h : (⟨0, 0, 0, A, B⟩ : WeierstrassCurve K).toAffine.Nonsingular x y), N • (WeierstrassCurve.Affine.Point.some x y h) = 0 → ‖x ^ 3 + A * x + B‖ = 1 ∧ ∀ (x' y' : K) (h' : (⟨0, 0, 0, A, B⟩ : WeierstrassCurve K).toAffine.Nonsingular x' y'), N • (WeierstrassCurve.Affine.Point.some x' y' h') = 0 → x ≠ x' → ‖x - x'‖ = 1 := by
  intro K _ _ _ A B N hA hB h2 hD hN hT x y h hP
  have hy1 := norm_y_eq_one_of_nsmul_eq_zero hA hB h2 hD hN hT h hP
  refine ⟨?_, ?_⟩
  · rw [← short_equation_of_nonsingular h, norm_pow, hy1, one_pow]
  · intro x' y' h' hP' hx
    have hxx : ‖x - x'‖ ≤ 1 := norm_sub_le_one_of_le_one (hT _ _ h hP) (hT _ _ h' hP')
    refine le_antisymm hxx (not_lt.mp fun hlt => ?_)
    have hsub := norm_sub_y_le_norm_sub_x_of_torsion hT h h' hP hP' hx
    have hnegP : N • Point.some x' _
        (((⟨0, 0, 0, A, B⟩ : WeierstrassCurve K).toAffine.nonsingular_neg x' y').mpr h') = 0 := by
      rw [← Point.neg_some h', smul_neg, hP', neg_zero]
    have hadd := norm_sub_y_le_norm_sub_x_of_torsion hT h _ hP hnegP hx
    rw [short_negY_eq, sub_neg_eq_add] at hadd
    have h2y : ‖2 * y‖ < 1 := by
      have : 2 * y = (y - y') + (y + y') := by ring
      rw [this]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt
        (max_lt (hsub.trans_lt hlt) (hadd.trans_lt hlt))
    rw [norm_mul, h2, hy1, one_mul] at h2y
    exact lt_irrefl _ h2y
end

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FirstOrderRigid
open Polynomial

namespace GlobalTheory.TangentRigid

def Top {k : Type} [Field k] (p : k[X]) (d : ℕ) (c : k) : Prop :=
  p.natDegree ≤ d ∧ p.coeff d = c

section
variable {k : Type} [Field k] {p q : k[X]} {d e : ℕ} {c c' : k}

theorem Top.mul (hp : Top p d c) (hq : Top q e c') : Top (p * q) (d + e) (c * c') :=
  ⟨natDegree_mul_le.trans (add_le_add hp.1 hq.1), by
    rw [coeff_mul_add_eq_of_natDegree_le hp.1 hq.1, hp.2, hq.2]⟩

theorem Top.add (hp : Top p d c) (hq : Top q d c') : Top (p + q) d (c + c') :=
  ⟨(natDegree_add_le _ _).trans (max_le hp.1 hq.1), by rw [coeff_add, hp.2, hq.2]⟩

theorem Top.sub (hp : Top p d c) (hq : Top q d c') : Top (p - q) d (c - c') :=
  ⟨(natDegree_sub_le _ _).trans (max_le hp.1 hq.1), by rw [coeff_sub, hp.2, hq.2]⟩

theorem Top.cmul (a : k) (hp : Top p d c) : Top (C a * p) d (a * c) :=
  ⟨(natDegree_C_mul_le _ _).trans hp.1, by rw [coeff_C_mul, hp.2]⟩

theorem Top.raise (hp : Top p d c) (h : d < e) : Top p e 0 :=
  ⟨hp.1.trans h.le, coeff_eq_zero_of_natDegree_lt (hp.1.trans_lt h)⟩

theorem Top.cast {p' : k[X]} (hp : Top p d c) (h0 : p = p') (h : d = e) (h' : c = c') :
    Top p' e c' := by
  subst h0 h h'; exact hp

theorem top_X : Top (X : k[X]) 1 1 := ⟨natDegree_X_le, by simp⟩

theorem top_one : Top (1 : k[X]) 0 1 := ⟨by simp, by simp⟩

theorem top_of_monic (hp : p.Monic) (h : p.natDegree = d) : Top p d 1 :=
  ⟨h.le, by rw [← h]; exact hp⟩

theorem top_of_degree_lt (h : p.degree < (d : WithBot ℕ)) : Top p d 0 :=
  ⟨natDegree_le_of_degree_le h.le, coeff_eq_zero_of_degree_lt h⟩

theorem Top.xder (hp : Top p d c) : Top (X * derivative p) d (d * c) := by
  have key : ∀ j : ℕ, (X * derivative p).coeff j = j * p.coeff j := by
    intro j
    cases j with
    | zero => simp
    | succ j => rw [coeff_X_mul, coeff_derivative]; push_cast; ring
  refine ⟨natDegree_le_iff_coeff_eq_zero.2 fun j hj => ?_, by rw [key, hp.2]⟩
  rw [key, coeff_eq_zero_of_natDegree_lt (hp.1.trans_lt hj), mul_zero]

theorem Top.natDegree_eq (hp : Top p d 1) : p.natDegree = d :=
  le_antisymm hp.1 (le_natDegree_of_ne_zero (by rw [hp.2]; exact one_ne_zero))

end

theorem exists_param {k : Type} [Field k] (A B a dA dB : k) (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0)
    (ha : a ≠ 0) (hD : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0) (hd : 12 * A ^ 2 * dA + 54 * B * dB = 0) :
    ∃ w : k, dA = 9 * B * a ^ 2 * w ∧ dB = -2 * A ^ 2 * a ^ 2 * w := by
  have h6 : (6 : k) ≠ 0 := by
    have : (6 : k) = 2 * 3 := by norm_num
    rw [this]; exact mul_ne_zero h2 h3
  have hd' : 2 * A ^ 2 * dA + 9 * B * dB = 0 := by
    apply mul_left_cancel₀ h6
    linear_combination hd
  refine ⟨(3 * B * dA - 2 * A * dB) / ((4 * A ^ 3 + 27 * B ^ 2) * a ^ 2), ?_, ?_⟩
  · rw [← mul_div_assoc, eq_div_iff (mul_ne_zero hD (pow_ne_zero 2 ha))]
    linear_combination (2 * A * a ^ 2) * hd'
  · rw [← mul_div_assoc, eq_div_iff (mul_ne_zero hD (pow_ne_zero 2 ha))]
    linear_combination (3 * B * a ^ 2) * hd'

theorem first_order_rigid : ∀ (k : Type) [Field k] (m : ℕ) (A B a dA dB : k) (n h dn dh : k[X]), (2 : k) ≠ 0 → (3 : k) ≠ 0 → a ≠ 0 → a ^ 2 = -(2 * (m : k) + 1) → 4 * A ^ 3 + 27 * B ^ 2 ≠ 0 → 12 * A ^ 2 * dA + 54 * B * dB = 0 → n.Monic → h.Monic → n.natDegree = 2 * m + 1 → h.natDegree = m → dn.degree < ((2 * m + 1 : ℕ) : WithBot ℕ) → dh.degree < (m : WithBot ℕ) → IsCoprime n h → (X ^ 3 + C A * X + C B) * (derivative n * h - 2 * n * derivative h) ^ 2 = n ^ 3 + C (a ^ 4 * A) * n * h ^ 4 + C (a ^ 6 * B) * h ^ 6 → (C dA * X + C dB) * (derivative n * h - 2 * n * derivative h) ^ 2 + 2 * (X ^ 3 + C A * X + C B) * (derivative n * h - 2 * n * derivative h) * (derivative dn * h + derivative n * dh - 2 * dn * derivative h - 2 * n * derivative dh) = 3 * n ^ 2 * dn + C (a ^ 4 * dA) * n * h ^ 4 + C (a ^ 4 * A) * (dn * h ^ 4 + 4 * n * h ^ 3 * dh) + C (a ^ 6 * dB) * h ^ 6 + 6 * C (a ^ 6 * B) * h ^ 5 * dh → dA = 0 ∧ dB = 0 ∧ dn = 0 ∧ dh = 0 := by
  intro k _ m A B a dA dB n h dn dh h2 h3 ha ha2 hD hd hn hh hnd hhd hdn hdh hco E Ed
  obtain ⟨w, rfl, rfl⟩ := exists_param A B a dA dB h2 h3 ha hD hd
  obtain ⟨q, hq⟩ : ∃ q, q = derivative n * h - 2 * n * derivative h := ⟨_, rfl⟩
  obtain ⟨qd, hqd⟩ : ∃ qd, qd = derivative dn * h + derivative n * dh - 2 * dn * derivative h
      - 2 * n * derivative dh := ⟨_, rfl⟩
  rw [← hq] at E Ed
  rw [← hqd] at Ed
  have c2 : (C (2 : k) : k[X]) = 2 := rfl
  have c3 : (C (3 : k) : k[X]) = 3 := rfl
  have c4 : (C (4 : k) : k[X]) = 4 := rfl
  have c6 : (C (6 : k) : k[X]) = 6 := rfl
  have c9 : (C (9 : k) : k[X]) = 9 := rfl
  have c27 : (C (27 : k) : k[X]) = 27 := rfl
  have E' : (3 * X ^ 2 + C A) * q ^ 2 + 2 * (X ^ 3 + C A * X + C B) * q * derivative q
      = 3 * n ^ 2 * derivative n
        + C (a ^ 4 * A) * (derivative n * h ^ 4 + 4 * n * h ^ 3 * derivative h)
        + 6 * C (a ^ 6 * B) * h ^ 5 * derivative h := by
    have := congrArg derivative E
    simp only [derivative_mul, derivative_add, derivative_pow, derivative_X, derivative_C,
      Nat.cast_ofNat, c2, c3, c4, c6] at this
    norm_num only at this
    linear_combination this
  simp only [map_mul, map_pow, map_neg, c2, c9] at E E' Ed
  set F : k[X] := X ^ 3 + C A * X + C B with hF
  set r : k[X] := dn * h - 2 * n * dh with hr
  set V : k[X] := C a ^ 2 * C w * (3 * X ^ 2 + 2 * C A) with hV
  set V' : k[X] := C w * (3 * n ^ 2 + 2 * (C a ^ 4 * C A) * h ^ 4) with hV'
  set G : k[X] := n ^ 3 + C a ^ 4 * C A * n * h ^ 4 + C a ^ 6 * C B * h ^ 6 with hG
  set G₁ : k[X] := 3 * n ^ 2 + C a ^ 4 * C A * h ^ 4 with hG₁
  set P : k[X] := h * r + V * h * q - V' with hP
  have key : G₁ * P = F * q * (9 * C a ^ 2 * C w * X * h ^ 2 * q + 2 * h ^ 2 * qd - 6 * h * dh * q
      + 2 * V * h ^ 2 * derivative q - 6 * V * h * derivative h * q - 9 * C w * n * q) := by
    simp only [hG₁, hP, hr, hV', hV, hF, hG] at E E' Ed ⊢
    linear_combination (-h ^ 2) * Ed
      - (C a ^ 2 * C w * (3 * X ^ 2 + 2 * C A) * h ^ 2) * E'
      + (6 * h * dh + 6 * (C a ^ 2 * C w * (3 * X ^ 2 + 2 * C A)) * h * derivative h
          + 9 * C w * n) * E
      + ((3 * n ^ 2 + C a ^ 4 * C A * h ^ 4) * (C a ^ 2 * C w * (3 * X ^ 2 + 2 * C A)) * h) * hq
  have hGh : IsCoprime G h := by
    have : G = n ^ 3 + h * (C a ^ 4 * C A * n * h ^ 3 + C a ^ 6 * C B * h ^ 5) := by
      rw [hG]; ring
    rw [this]
    exact IsCoprime.add_mul_left_left hco.pow_left _
  have hGG : IsCoprime G G₁ := by
    have hu : IsUnit (C (a ^ 12 * (4 * A ^ 3 + 27 * B ^ 2)) : k[X]) :=
      isUnit_C.2 (mul_ne_zero (pow_ne_zero _ ha) hD).isUnit
    have h1 : IsCoprime G (C (a ^ 12 * (4 * A ^ 3 + 27 * B ^ 2)) * h ^ 8) :=
      (isCoprime_mul_unit_left_right hu _ _).2 hGh.pow_right
    have h2' : C (a ^ 12 * (4 * A ^ 3 + 27 * B ^ 2)) * h ^ 8 =
        (6 * (C a ^ 4 * C A) * n ^ 2 - 9 * (C a ^ 6 * C B) * n * h ^ 2
          + 4 * (C a ^ 4 * C A) ^ 2 * h ^ 4) * G₁
        + G * (27 * (C a ^ 6 * C B) * h ^ 2 - 18 * (C a ^ 4 * C A) * n) := by
      simp only [map_mul, map_pow, map_add (f := _), c4, c27, hG, hG₁]
      ring
    rw [h2'] at h1
    exact (IsCoprime.of_add_mul_left_right h1).of_mul_right_right
  have hdv : F * q ∣ G := ⟨q, by rw [← E]; ring⟩
  have hc1 : IsCoprime (F * q) G₁ := hGG.of_isCoprime_of_dvd_left hdv
  have hc2 : IsCoprime (F * q) h := hGh.of_isCoprime_of_dvd_left hdv
  have hFP : F * q ∣ P := hc1.dvd_of_dvd_mul_left ⟨_, key⟩
  set R : k[X] := P - 6 * C w * (F * q) * derivative h with hR
  have hFR : F * q ∣ R := dvd_sub hFP ⟨6 * C w * derivative h, by ring⟩
  have hhR : h ∣ R := by
    refine hco.symm.dvd_of_dvd_mul_left ⟨n * r + n * V * q + C w * (C a ^ 4 * C A) * n * h ^ 3
      + 3 * C w * (C a ^ 6 * C B) * h ^ 5 - 3 * C w * F * q * derivative n, ?_⟩
    simp only [hR, hP, hV', hG] at E ⊢
    linear_combination (3 * C w) * E - (3 * C w * F * q) * hq
  have hdR : F * q * h ∣ R := hc2.mul_dvd hFR hhR
  have tn := top_of_monic hn hnd
  have th := top_of_monic hh hhd
  have tX := top_X (k := k)
  have tF : Top F 3 1 := by
    refine ((((tX.mul tX).mul tX).add ((tX.cmul A).raise (by norm_num))).add
      (((top_one (k := k)).cmul B).raise (by norm_num))).cast ?_ rfl (by ring)
    rw [hF]; ring
  have tq : Top (X * q) (3 * m + 1) 1 := by
    refine ((tn.xder.mul th).sub ((tn.mul th.xder).cmul 2)).cast ?_ (by ring) (by push_cast; ring)
    rw [hq, c2]; ring
  have tr : Top r (3 * m + 1) 0 := by
    refine (((top_of_degree_lt hdn).mul th).sub
      ((tn.mul (top_of_degree_lt hdh)).cmul 2)).cast ?_ (by ring) (by ring)
    rw [hr, c2]; ring
  have tV : Top V 2 (3 * a ^ 2 * w) := by
    refine ((((tX.mul tX).cmul 3).add
      (((top_one (k := k)).cmul (2 * A)).raise (by norm_num))).cmul (a ^ 2 * w)).cast ?_ rfl
        (by ring)
    simp only [hV, map_mul, map_pow, c2, c3]; ring
  have tV' : Top V' (4 * m + 2) (3 * w) := by
    refine (((((tn.mul tn).cmul 3).cast rfl (show _ = 4 * m + 2 by ring) rfl).add
      ((((th.mul th).mul (th.mul th)).cmul (2 * (a ^ 4 * A))).raise (by omega))).cmul w).cast
        ?_ rfl (by ring)
    simp only [hV', map_mul, map_pow, c2, c3]; ring
  have tR : Top (X * X * R) (4 * m + 4) (3 * a ^ 2 * w - 3 * w - 6 * w * m) := by
    have t1 := (((tX.mul tX).mul th).mul tr).raise (show _ < 4 * m + 4 by omega)
    have t2 := (((tX.mul tV).mul th).mul tq).cast rfl (show _ = 4 * m + 4 by omega) rfl
    have t3 := ((tX.mul tX).mul tV').cast rfl (show _ = 4 * m + 4 by omega) rfl
    have t4 := (((tF.mul tq).mul th.xder).cmul (6 * w)).cast rfl
      (show _ = 4 * m + 4 by omega) rfl
    refine (((t1.add t2).sub t3).sub t4).cast ?_ rfl (by ring)
    simp only [hR, hP, map_mul, c6]; ring
  have tD : Top (X * (F * (X * q) * h)) (4 * m + 5) 1 :=
    (tX.mul ((tF.mul tq).mul th)).cast rfl (by omega) (by ring)
  have hXR : X * X * R = 0 := by
    refine eq_zero_of_dvd_of_natDegree_lt (p := X * (F * (X * q) * h)) ?_ ?_
    · obtain ⟨T, hT⟩ := hdR
      exact ⟨T, by rw [hT]; ring⟩
    · rw [tD.natDegree_eq]; have := tR.1; omega
  have hR0 : R = 0 := by simpa using hXR
  have hw : w = 0 := by
    have h0 := tR.2
    rw [hXR, coeff_zero] at h0
    have h1 : 2 * 3 * a ^ 2 * w = 0 := by linear_combination (3 * w) * ha2 - h0
    exact (mul_eq_zero.1 h1).resolve_left (mul_ne_zero (mul_ne_zero h2 h3) (pow_ne_zero _ ha))
  have hr0 : r = 0 := by
    have : h * r = 0 := by
      rw [← hR0]; simp [hR, hP, hV, hV', hw]
    exact (mul_eq_zero.1 this).resolve_left hh.ne_zero
  have hdh0 : dh = 0 := by
    have h1 : h ∣ n * dh := ⟨C (2 : k)⁻¹ * dn, by
      have : (C (2 : k)⁻¹ : k[X]) * 2 = 1 := by rw [← c2, ← map_mul, inv_mul_cancel₀ h2, map_one]
      linear_combination (-C (2 : k)⁻¹) * hr0 + (C (2 : k)⁻¹) * hr - (n * dh) * this⟩
    refine eq_zero_of_dvd_of_degree_lt (hco.symm.dvd_of_dvd_mul_left h1) ?_
    rwa [degree_eq_natDegree hh.ne_zero, hhd]
  refine ⟨by simp [hw], by simp [hw], ?_, hdh0⟩
  have : dn * h = 0 := by rw [← hr0, hr, hdh0]; ring
  exact (mul_eq_zero.1 this).resolve_right hh.ne_zero

end GlobalTheory.TangentRigid
end
