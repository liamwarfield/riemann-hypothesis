module

public import Development.AbelianVarietyTheory.Definitions.Foundations.TupleConstantsNeZero
public import Formalism.QuotientMetricDivisors.ReductionLemmaZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaussSumMulGaussSumInvOfIsPrimitive
open NumberField IsDedekindDomain Finset GlobalTheory.Square
open Formalism.DivisionValues (vw conjPl)
open Formalism.PairingDivisionLocalBalance (Pl wt)

namespace GlobalTheory.GaussInt

theorem gaussSum_mul_gaussSum_inv_of_isPrimitive {K : Type} [Field K] {N : ℕ} [NeZero N]
    {χ : DirichletCharacter K N} {ψ : AddChar (ZMod N) K} (hχ : χ.IsPrimitive)
    (hψ : ψ.IsPrimitive) : gaussSum χ ψ * gaussSum χ⁻¹ ψ⁻¹ = (N : K) := by
  have h1 : gaussSum χ ψ * gaussSum χ⁻¹ ψ⁻¹
      = ∑ b : ZMod N, ∑ a : ZMod N, χ a * ψ (b * (a - 1)) := by
    conv_lhs => rw [gaussSum.eq_1 χ⁻¹, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← mul_assoc, mul_comm (gaussSum χ ψ), ← gaussSum_mulShift_of_isPrimitive ψ hχ b,
      gaussSum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [AddChar.mulShift_apply, AddChar.inv_apply, mul_assoc, ← AddChar.map_add_eq_mul]
    congr 2
    ring
  rw [h1, Finset.sum_comm]
  simp_rw [← Finset.mul_sum, AddChar.sum_mulShift _ hψ, sub_eq_zero]
  rw [Finset.sum_eq_single (1 : ZMod N)]
  · simp
  · intro a _ ha
    simp [ha]
  · simp

end GlobalTheory.GaussInt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SumIntervalIntegralLeOfSpaced
open Complex DirichletCharacter ArithmeticFunction MeasureTheory

namespace GlobalTheory

theorem gallagher_interval (f f' h : ℝ → ℝ) (hf : ∀ t, HasDerivAt f (f' t) t)
    (hf' : Continuous f') (hh : Continuous h) (hb : ∀ t, |f' t| ≤ h t) (x δ : ℝ) (hδ : 0 < δ) :
    f x ≤ ∫ t in x..(x + δ), (f t / δ + h t) := by
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun t => (hf t).continuousAt
  have hF : ∀ t, HasDerivAt (fun t => (t - x - δ) / δ * f t) (f t / δ + (t - x - δ) / δ * f' t) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => (t - x - δ) / δ) (1 / δ) t :=
      (((hasDerivAt_id t).sub_const x).sub_const δ).div_const δ
    exact (h1.fun_mul (hf t)).congr_deriv (by ring)
  have hc : Continuous fun t => f t / δ + (t - x - δ) / δ * f' t := by fun_prop
  have h2 := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := x) (b := x + δ)
    (fun t _ => hF t) (hc.intervalIntegrable _ _)
  have h3 : (x + δ - x - δ) / δ * f (x + δ) - (x - x - δ) / δ * f x = f x := by
    field_simp
    ring
  rw [h3] at h2
  rw [← h2]
  apply intervalIntegral.integral_mono_on (by linarith) (hc.intervalIntegrable _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _)
  intro t ht
  have h4 : |(t - x - δ) / δ| ≤ 1 := by
    rw [abs_div, abs_of_pos hδ, div_le_one hδ, abs_le]
    constructor <;> linarith [ht.1, ht.2]
  have h5 : (t - x - δ) / δ * f' t ≤ h t := by
    calc _ ≤ |(t - x - δ) / δ * f' t| := le_abs_self _
      _ = |(t - x - δ) / δ| * |f' t| := abs_mul _ _
      _ ≤ 1 * h t := mul_le_mul h4 (hb t) (abs_nonneg _) zero_le_one
      _ = h t := one_mul _
  linarith

theorem integral_exp_two_pi_sub (n m : ℕ) (y : ℝ) :
    ∫ t in y..(y + 1), Complex.exp (2 * Real.pi * I * ((n : ℂ) - m) * t) = if n = m then 1 else 0 := by
  split_ifs with h
  · subst h; simp
  · have hc : (2 * Real.pi * I * ((n : ℂ) - m)) ≠ 0 := by
      have : (n : ℂ) - m ≠ 0 := sub_ne_zero.2 (by exact_mod_cast h)
      have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      simp [this, hpi, I_ne_zero]
    rw [integral_exp_mul_complex hc]
    have : Complex.exp (2 * Real.pi * I * ((n : ℂ) - m) * ((y + 1 : ℝ) : ℂ))
        = Complex.exp (2 * Real.pi * I * ((n : ℂ) - m) * (y : ℂ)) := by
      have h1 := Complex.exp_int_mul_two_pi_mul_I ((n : ℤ) - m)
      rw [show 2 * Real.pi * I * ((n : ℂ) - m) * ((y + 1 : ℝ) : ℂ)
        = 2 * Real.pi * I * ((n : ℂ) - m) * (y : ℂ) + (((n : ℤ) - m : ℤ) : ℂ) * (2 * Real.pi * I) by
          push_cast; ring, Complex.exp_add, h1, mul_one]
    rw [this]; simp

theorem norm_expSum_shift (s : Finset ℕ) (b : ℕ → ℂ) (c t : ℝ) :
    ‖∑ n ∈ s, b n * Complex.exp (2 * Real.pi * I * ((n : ℂ) - c) * t)‖
      = ‖∑ n ∈ s, b n * Complex.exp (2 * Real.pi * I * n * t)‖ := by
  have : ∑ n ∈ s, b n * Complex.exp (2 * Real.pi * I * ((n : ℂ) - c) * t)
      = Complex.exp (((-(2 * Real.pi * c * t) : ℝ) : ℂ) * I) *
        ∑ n ∈ s, b n * Complex.exp (2 * Real.pi * I * n * t) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [mul_left_comm, ← Complex.exp_add]
    congr 2
    push_cast; ring
  rw [this, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

theorem integral_norm_sq_expSum (s : Finset ℕ) (b : ℕ → ℂ) (y : ℝ) :
    ∫ t in y..(y + 1), ‖∑ n ∈ s, b n * Complex.exp (2 * Real.pi * I * n * t)‖ ^ 2
      = ∑ n ∈ s, ‖b n‖ ^ 2 := by
  have key : ∀ t : ℝ, ((‖∑ n ∈ s, b n * Complex.exp (2 * Real.pi * I * n * t)‖ ^ 2 : ℝ) : ℂ)
      = ∑ n ∈ s, ∑ m ∈ s, b n * (starRingEnd ℂ) (b m) *
        Complex.exp (2 * Real.pi * I * ((n : ℂ) - m) * t) := by
    intro t
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
    rw [map_mul, ← Complex.exp_conj]
    simp only [map_mul, conj_ofReal, conj_I, map_natCast, map_ofNat]
    rw [mul_mul_mul_comm, ← Complex.exp_add]
    congr 2
    ring
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  simp_rw [key]
  rw [intervalIntegral.integral_finsetSum (fun n _ => Continuous.intervalIntegrable (by fun_prop) _ _)]
  push_cast
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [intervalIntegral.integral_finsetSum (fun n _ => Continuous.intervalIntegrable (by fun_prop) _ _)]
  simp_rw [intervalIntegral.integral_const_mul, integral_exp_two_pi_sub]
  simp [hn, Complex.mul_conj']

theorem sum_intervalIntegral_le_of_spaced (g : ℝ → ℝ) (hg : Continuous g) (h0 : ∀ t, 0 ≤ g t)
    (S : Finset ℝ) (p : ℝ → ℝ) (δ y : ℝ) (hδ : 0 < δ)
    (h1 : ∀ x ∈ S, y ≤ p x) (h2 : ∀ x ∈ S, p x + δ ≤ y + 1)
    (h3 : ∀ x ∈ S, ∀ z ∈ S, x ≠ z → δ ≤ |p x - p z|) :
    ∑ x ∈ S, ∫ t in (p x)..(p x + δ), g t ≤ ∫ t in y..(y + 1), g t := by
  have hi : ∀ u v : ℝ, IntegrableOn g (Set.Ioc u v) := fun u v =>
    (hg.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  rw [intervalIntegral.integral_of_le (by linarith : y ≤ y + 1)]
  rw [Finset.sum_congr rfl fun x _ =>
    intervalIntegral.integral_of_le (by linarith : p x ≤ p x + δ)]
  rw [← integral_biUnion_finset S (s := fun x => Set.Ioc (p x) (p x + δ))
    (fun _ _ => measurableSet_Ioc) ?_ (fun x _ => hi _ _)]
  · apply setIntegral_mono_set (hi _ _) (Filter.Eventually.of_forall h0)
    apply Filter.Eventually.of_forall
    intro t ht
    simp only [Set.mem_iUnion] at ht
    obtain ⟨x, hx, ht⟩ := ht
    exact ⟨lt_of_le_of_lt (h1 x hx) ht.1, ht.2.trans (h2 x hx)⟩
  · intro x hx z hz hxz
    have := h3 x hx z hz hxz
    rw [Function.onFun, Set.disjoint_left]
    intro t ht ht'
    have : |p x - p z| < δ := by
      rw [abs_lt]; constructor <;> linarith [ht.1, ht.2, ht'.1, ht'.2]
    linarith

theorem expSum_sub_int (s : Finset ℕ) (b : ℕ → ℂ) (x : ℝ) (k : ℤ) :
    ∑ n ∈ s, b n * Complex.exp (2 * Real.pi * I * n * ((x - k : ℝ) : ℂ))
      = ∑ n ∈ s, b n * Complex.exp (2 * Real.pi * I * n * x) := by
  refine Finset.sum_congr rfl fun n _ => ?_
  have h1 := Complex.exp_int_mul_two_pi_mul_I (-(n * k))
  rw [show 2 * Real.pi * I * (n : ℂ) * ((x - k : ℝ) : ℂ)
    = 2 * Real.pi * I * n * x + ((-(n * k) : ℤ) : ℂ) * (2 * Real.pi * I) by
      push_cast; ring, Complex.exp_add, h1, mul_one]

theorem additive_large_sieve : ∀ (M N : ℕ) (a : ℕ → ℂ) (S : Finset ℝ) (δ : ℝ), 0 < δ → δ ≤ 1 → (∀ x ∈ S, ∀ y ∈ S, x ≠ y → ∀ k : ℤ, δ ≤ |x - y - k|) → ∑ x ∈ S, ‖∑ n ∈ Finset.Ioc M (M + N), a n * Complex.exp (2 * Real.pi * I * n * x)‖ ^ 2 ≤ (1 / δ + 2 * Real.pi * N) * ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2 := by
  intro M N a S δ hδ hδ1 hS
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  rcases S.eq_empty_or_nonempty with rfl | ⟨y, hy⟩
  · simp only [Finset.sum_empty]; positivity
  set s := Finset.Ioc M (M + N) with hs
  set c : ℝ := M + N / 2 with hc
  set L : ℝ := Real.pi * N with hL
  have hL0 : 0 < L := by positivity
  set b : ℕ → ℂ := fun n => a n * (2 * Real.pi * I * ((n : ℂ) - c)) with hb
  set T : ℝ → ℂ := fun t => ∑ n ∈ s, a n * Complex.exp (2 * Real.pi * I * ((n : ℂ) - c) * t) with hT
  set T' : ℝ → ℂ := fun t => ∑ n ∈ s, b n * Complex.exp (2 * Real.pi * I * ((n : ℂ) - c) * t) with hT'
  have hd : ∀ t, HasDerivAt T (T' t) t := by
    intro t
    apply HasDerivAt.fun_sum
    intro n _
    have h1 : HasDerivAt (fun t : ℝ => 2 * Real.pi * I * ((n : ℂ) - c) * (t : ℂ))
        (2 * Real.pi * I * ((n : ℂ) - c)) t := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (2 * Real.pi * I * ((n : ℂ) - c))
    exact ((h1.cexp).const_mul (a n)).congr_deriv (by simp only [hb]; ring)
  have hTc : Continuous T := by simp only [hT]; fun_prop
  have hTc' : Continuous T' := by simp only [hT']; fun_prop
  have hG : ∀ x, ‖T x‖ ^ 2 ≤ ∫ t in x..(x + δ), (‖T t‖ ^ 2 / δ + (L * ‖T t‖ ^ 2 + ‖T' t‖ ^ 2 / L)) := by
    intro x
    refine gallagher_interval (fun t => ‖T t‖ ^ 2) (fun t => 2 * inner ℝ (T t) (T' t))
      (fun t => L * ‖T t‖ ^ 2 + ‖T' t‖ ^ 2 / L) (fun t => (hd t).norm_sq) (by fun_prop) (by fun_prop) ?_ x δ hδ
    intro t
    have h1 := abs_real_inner_le_norm (T t) (T' t)
    rw [abs_mul, abs_two]
    have h2 : L * ‖T t‖ ^ 2 + ‖T' t‖ ^ 2 / L - 2 * (‖T t‖ * ‖T' t‖)
        = (L * ‖T t‖ - ‖T' t‖) ^ 2 / L := by field_simp; ring
    have h3 : 0 ≤ (L * ‖T t‖ - ‖T' t‖) ^ 2 / L := by positivity
    linarith
  set p : ℝ → ℝ := fun x => x - (⌊x - y⌋ : ℤ) with hp
  have hsum := sum_intervalIntegral_le_of_spaced
    (fun t => ‖T t‖ ^ 2 / δ + (L * ‖T t‖ ^ 2 + ‖T' t‖ ^ 2 / L)) (by fun_prop) (fun t => by positivity)
    S p δ y hδ (fun x _ => by simp only [hp]; linarith [Int.floor_le (x - y)]) ?_ ?_
  · have e1 : ∫ t in y..(y + 1), ‖T t‖ ^ 2 = ∑ n ∈ s, ‖a n‖ ^ 2 := by
      simp only [hT, norm_expSum_shift]; exact integral_norm_sq_expSum s a y
    have e2 : ∫ t in y..(y + 1), ‖T' t‖ ^ 2 = ∑ n ∈ s, ‖b n‖ ^ 2 := by
      simp only [hT', norm_expSum_shift]; exact integral_norm_sq_expSum s b y
    have e3 : ∑ n ∈ s, ‖b n‖ ^ 2 ≤ L ^ 2 * ∑ n ∈ s, ‖a n‖ ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun n hn => ?_
      rw [hs, Finset.mem_Ioc] at hn
      have hn1 : (M : ℝ) < n := by exact_mod_cast hn.1
      have hn2 : (n : ℝ) ≤ M + N := by exact_mod_cast hn.2
      have h4 : ‖(n : ℂ) - c‖ ≤ N / 2 := by
        rw [show (n : ℂ) - c = ((n - c : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
          Real.norm_eq_abs, abs_le]
        constructor <;> linarith
      have h5 : ‖b n‖ ≤ L * ‖a n‖ := by
        simp only [hb, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos Real.pi_pos, Complex.norm_ofNat]
        calc ‖a n‖ * (2 * Real.pi * 1 * ‖(n : ℂ) - c‖) ≤ ‖a n‖ * (2 * Real.pi * 1 * (N / 2)) := by
              gcongr
          _ = L * ‖a n‖ := by rw [hL]; ring
      rw [← mul_pow]
      gcongr
    have e4 : ∫ t in y..(y + 1), (‖T t‖ ^ 2 / δ + (L * ‖T t‖ ^ 2 + ‖T' t‖ ^ 2 / L))
        = (∑ n ∈ s, ‖a n‖ ^ 2) / δ + (L * ∑ n ∈ s, ‖a n‖ ^ 2 + (∑ n ∈ s, ‖b n‖ ^ 2) / L) := by
      rw [intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
        (Continuous.intervalIntegrable (by fun_prop) _ _),
        intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
        (Continuous.intervalIntegrable (by fun_prop) _ _), intervalIntegral.integral_div,
        intervalIntegral.integral_div, intervalIntegral.integral_const_mul, e1, e2]
    have e5 : (∑ n ∈ s, ‖b n‖ ^ 2) / L ≤ L * ∑ n ∈ s, ‖a n‖ ^ 2 := by
      rw [div_le_iff₀ hL0]; nlinarith
    calc _ = ∑ x ∈ S, ‖T (p x)‖ ^ 2 := by
          refine Finset.sum_congr rfl fun x _ => ?_
          simp only [hT, hp]
          rw [norm_expSum_shift, expSum_sub_int]
      _ ≤ _ := Finset.sum_le_sum fun x _ => hG (p x)
      _ ≤ _ := hsum
      _ = _ := e4
      _ ≤ (∑ n ∈ s, ‖a n‖ ^ 2) / δ + (L * ∑ n ∈ s, ‖a n‖ ^ 2 + L * ∑ n ∈ s, ‖a n‖ ^ 2) := by
          linarith
      _ = _ := by rw [hL]; ring
  · intro x hx
    simp only [hp]
    by_cases hxy : x = y
    · subst hxy; simp [hδ1]
    · have h1 := hS x hx y hy hxy (⌊x - y⌋ + 1)
      have h2 := Int.lt_floor_add_one (x - y)
      push_cast at h1
      rw [abs_of_neg (by linarith)] at h1
      linarith
  · intro x hx z hz hxz
    have h1 := hS x hx z hz hxz (⌊x - y⌋ - ⌊z - y⌋)
    simp only [hp]
    convert h1 using 2
    push_cast; ring

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MultiplicativeLargeSieve
open Complex DirichletCharacter ArithmeticFunction MeasureTheory

namespace GlobalTheory.MultSieve

theorem norm_sq_gaussSum {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) :
    ‖gaussSum χ (ZMod.stdAddChar (N := q))‖ ^ 2 = q := by
  have h := GlobalTheory.GaussInt.gaussSum_mul_gaussSum_inv_of_isPrimitive hχ (ZMod.isPrimitive_stdAddChar q)
  rw [← star_gaussSum_eq] at h
  apply Complex.ofReal_injective
  rw [Complex.ofReal_pow, ← Complex.mul_conj']
  simpa using h

theorem sum_norm_sq_char {q : ℕ} [NeZero q] (F : ZMod q → ℂ) :
    ∑ χ : DirichletCharacter ℂ q, ‖∑ b : ZMod q, χ⁻¹ b * F b‖ ^ 2
      = q.totient * ∑ b : ZMod q, if IsUnit b then ‖F b‖ ^ 2 else 0 := by
  classical
  apply Complex.ofReal_injective
  have key : ∀ χ : DirichletCharacter ℂ q, ((‖∑ b : ZMod q, χ⁻¹ b * F b‖ ^ 2 : ℝ) : ℂ)
      = ∑ b : ZMod q, ∑ c : ZMod q, (χ⁻¹ b * χ c) * (F b * (starRingEnd ℂ) (F c)) := by
    intro χ
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
    have : (starRingEnd ℂ) (χ⁻¹ c) = χ c := by
      have := MulChar.star_apply' χ⁻¹ c
      rwa [inv_inv] at this
    rw [map_mul, this]; ring
  rw [Complex.ofReal_sum]
  simp_rw [key]
  rw [Finset.sum_comm, Complex.ofReal_mul, Complex.ofReal_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul]
  by_cases hb : IsUnit b
  · have h1 : ∀ c : ZMod q, ∑ χ : DirichletCharacter ℂ q, χ⁻¹ b * χ c
        = if b = c then (q.totient : ℂ) else 0 := by
      intro c
      rw [← DirichletCharacter.sum_char_inv_mul_char_eq ℂ hb c]
      refine Finset.sum_congr rfl fun χ _ => ?_
      obtain ⟨u, rfl⟩ := hb
      rw [MulChar.inv_apply, Ring.inverse_unit, ZMod.inv_coe_unit]
    simp [h1, hb, Complex.mul_conj']
  · simp [hb, MulChar.map_nonunit _ hb]

theorem sum_primitive_le {q : ℕ} [NeZero q] (s : Finset ℕ) (a : ℕ → ℂ) :
    ∑ᶠ χ ∈ {χ : DirichletCharacter ℂ q | χ.IsPrimitive}, ‖∑ n ∈ s, a n * χ (n : ZMod q)‖ ^ 2
      ≤ ∑ b ∈ (Finset.range q).filter (fun b => Nat.Coprime b q),
        ‖∑ n ∈ s, a n * Complex.exp (2 * Real.pi * I * n * (((b : ℝ) / q : ℝ) : ℂ))‖ ^ 2 := by
  classical
  set F : ZMod q → ℂ := fun b => ∑ n ∈ s, a n * ZMod.stdAddChar ((n : ZMod q) * b) with hF
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have h1 : ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive →
      q * ‖∑ n ∈ s, a n * χ (n : ZMod q)‖ ^ 2 = ‖∑ b : ZMod q, χ⁻¹ b * F b‖ ^ 2 := by
    intro χ hχ
    have hχ' : (χ⁻¹).IsPrimitive := by
      rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]; exact hχ
    rw [← norm_sq_gaussSum hχ', ← mul_pow, ← norm_mul]
    congr 2
    simp only [hF, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => ?_
    have h := gaussSum_mulShift_of_isPrimitive (ZMod.stdAddChar (N := q)) hχ' (n : ZMod q)
    rw [inv_inv] at h
    rw [mul_left_comm, mul_comm (gaussSum _ _), ← h, gaussSum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [AddChar.mulShift_apply]; ring
  have h2 : ∑ b : ZMod q, (if IsUnit b then ‖F b‖ ^ 2 else 0)
      = ∑ b ∈ (Finset.range q).filter (fun b => Nat.Coprime b q),
        ‖∑ n ∈ s, a n * Complex.exp (2 * Real.pi * I * n * (((b : ℝ) / q : ℝ) : ℂ))‖ ^ 2 := by
    rw [Finset.sum_filter]
    symm
    refine Finset.sum_nbij' (fun b => (b : ZMod q)) (fun b => b.val) (by simp)
      (fun b _ => by simpa using ZMod.val_lt b)
      (fun b hb => ZMod.val_cast_of_lt (by simpa using hb)) (by simp) ?_
    intro b _
    refine if_congr (ZMod.isUnit_iff_coprime b q).symm ?_ rfl
    congr 2
    refine Finset.sum_congr rfl fun n _ => ?_
    have := ZMod.stdAddChar_coe (N := q) ((n * b : ℕ) : ℤ)
    push_cast at this
    rw [this]
    congr 2
    push_cast; ring
  rw [← h2]
  have h3 : {χ : DirichletCharacter ℂ q | χ.IsPrimitive}
      = ↑(Finset.univ.filter fun χ : DirichletCharacter ℂ q => χ.IsPrimitive) := by simp
  rw [h3, finsum_mem_coe_finset]
  refine le_of_mul_le_mul_left ?_ hq
  rw [Finset.mul_sum, Finset.sum_congr rfl fun χ hχ => h1 χ (Finset.mem_filter.1 hχ).2]
  refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    fun _ _ _ => by positivity).trans ?_
  rw [sum_norm_sq_char]
  refine mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.totient_le q)
    (Finset.sum_nonneg fun b _ => by split_ifs <;> positivity)

theorem farey_spaced (Q q r b c : ℕ) (hq : q ≤ Q) (hr : r ≤ Q) (hb : b < q) (hc : c < r)
    (hne : (b : ℝ) / q ≠ (c : ℝ) / r) (k : ℤ) :
    1 / (Q : ℝ) ^ 2 ≤ |(b : ℝ) / q - (c : ℝ) / r - k| := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hb1 : (b : ℝ) / q < 1 := (div_lt_one hq0).2 (by exact_mod_cast hb)
  have hc1 : (c : ℝ) / r < 1 := (div_lt_one hr0).2 (by exact_mod_cast hc)
  have hb0 : 0 ≤ (b : ℝ) / q := by positivity
  have hc0 : 0 ≤ (c : ℝ) / r := by positivity
  have hk : (b : ℝ) / q - (c : ℝ) / r - k ≠ 0 := by
    intro h
    have h1 : (k : ℝ) < 1 := by linarith
    have h2 : (-1 : ℝ) < k := by linarith
    have h1' : k < 1 := by exact_mod_cast h1
    have h2' : -1 < k := by exact_mod_cast h2
    have : k = 0 := by omega
    subst this
    apply hne
    simp at h
    linarith
  have he : (b : ℝ) / q - (c : ℝ) / r - k = ((b * r - c * q - k * q * r : ℤ) : ℝ) / (q * r) := by
    push_cast; field_simp
  rw [he] at hk ⊢
  have hm : (b * r - c * q - k * q * r : ℤ) ≠ 0 := by
    intro h; rw [h] at hk; simp at hk
  have hm1 : (1 : ℝ) ≤ |((b * r - c * q - k * q * r : ℤ) : ℝ)| := by
    exact_mod_cast Int.one_le_abs hm
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < q * r)]
  have hq' : (q : ℝ) ≤ Q := by exact_mod_cast hq
  have hr' : (r : ℝ) ≤ Q := by exact_mod_cast hr
  rw [sq]
  gcongr

theorem reduced_inj {q r b c : ℕ} (hq : 0 < q) (hr : 0 < r) (hb : Nat.Coprime b q)
    (hc : Nat.Coprime c r) (h : (b : ℝ) / q = (c : ℝ) / r) : q = r ∧ b = c := by
  have := Rat.div_int_inj (a := b) (b := q) (c := c) (d := r) (by exact_mod_cast hq)
    (by exact_mod_cast hr) (by simpa using hb) (by simpa using hc)
    (by apply Rat.cast_injective (α := ℝ); push_cast; exact h)
  omega

end GlobalTheory.MultSieve

namespace GlobalTheory

theorem multiplicative_large_sieve : ∀ (Q M N : ℕ) (a : ℕ → ℂ), 1 ≤ Q → ∑ q ∈ Finset.range Q, ∑ᶠ χ ∈ {χ : DirichletCharacter ℂ (q + 1) | χ.IsPrimitive}, ‖∑ n ∈ Finset.Ioc M (M + N), a n * χ (n : ZMod (q + 1))‖ ^ 2 ≤ ((Q : ℝ) ^ 2 + 2 * Real.pi * N) * ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2 := by
  intro Q M N a hQ
  classical
  have hQ' : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  set P := (Finset.range Q).sigma
    (fun q => (Finset.range (q + 1)).filter (fun b => Nat.Coprime b (q + 1))) with hP
  set φ : (Σ _ : ℕ, ℕ) → ℝ := fun p => (p.2 : ℝ) / ((p.1 + 1 : ℕ) : ℝ) with hφ
  have hmem : ∀ p ∈ P, p.1 < Q ∧ p.2 < p.1 + 1 ∧ Nat.Coprime p.2 (p.1 + 1) := by
    intro p hp
    simpa only [hP, Finset.mem_sigma, Finset.mem_range, Finset.mem_filter] using hp
  have hinj : Set.InjOn φ P := by
    rintro ⟨q, b⟩ hp ⟨r, c⟩ hp' h
    obtain ⟨h1, h2⟩ := MultSieve.reduced_inj (Nat.succ_pos q) (Nat.succ_pos r)
      (hmem _ hp).2.2 (hmem _ hp').2.2 h
    obtain rfl : q = r := by omega
    obtain rfl : b = c := h2
    rfl
  have h := additive_large_sieve M N a (P.image φ) (1 / (Q : ℝ) ^ 2) (by positivity)
    (by rw [div_le_one (by positivity)]; nlinarith) ?_
  · rw [Finset.sum_image hinj, one_div_one_div, hP, Finset.sum_sigma] at h
    exact (Finset.sum_le_sum fun q _ => MultSieve.sum_primitive_le _ a).trans h
  · intro x hx y hy hxy k
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨p', hp', rfl⟩ := Finset.mem_image.1 hy
    exact MultSieve.farey_spaced Q _ _ _ _ (hmem _ hp).1 (hmem _ hp').1 (hmem _ hp).2.1
      (hmem _ hp').2.1 hxy k

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MultiplicativeLargeSieveStatement
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_norm_sq_primitive_char_sum_le : ∀ (Q M N : ℕ) (a : ℕ → ℂ), 1 ≤ Q → ∑ q ∈ Finset.range Q, ∑ᶠ χ ∈ {χ : DirichletCharacter ℂ (q + 1) | χ.IsPrimitive}, ‖∑ n ∈ Finset.Ioc M (M + N), a n * χ (n : ZMod (q + 1))‖ ^ 2 ≤ ((Q : ℝ) ^ 2 + 2 * Real.pi * N) * ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2 := by
  first | exact @GlobalTheory.multiplicative_large_sieve | exact GlobalTheory.multiplicative_large_sieve | (intros; apply GlobalTheory.multiplicative_large_sieve <;> assumption)
end
