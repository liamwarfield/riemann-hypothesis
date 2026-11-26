module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHSt
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MSqCount

@[expose] public section

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTPiC
section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTPiA
section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTPiB
open Finset Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

theorem abel_log (c : ℕ → ℝ) (h0 : c 0 = 0) (h1 : c 1 = 0) {X : ℝ} (hX : 2 ≤ X) :
    ∑ n ∈ Icc 0 ⌊X⌋₊, (Real.log n)⁻¹ * c n = (∑ n ∈ Icc 0 ⌊X⌋₊, c n) / Real.log X +
      ∫ t in (2 : ℝ)..X, (∑ n ∈ Icc 0 ⌊t⌋₊, c n) / (t * Real.log t ^ 2) := by
  rw [sum_mul_eq_sub_integral_mul₁ c (f := fun n ↦ (Real.log n)⁻¹) h0 h1,
    ← intervalIntegral.integral_of_le hX]
  · have int_deriv (f : ℝ → ℝ) :
        ∫ u in (2 : ℝ)..X, deriv (fun x ↦ (Real.log x)⁻¹) u * f u =
        ∫ u in (2 : ℝ)..X, -(f u / (u * Real.log u ^ 2)) :=
      intervalIntegral.integral_congr fun u _ ↦ by simp [field]
    rw [int_deriv, intervalIntegral.integral_neg]
    ring
  · intro z ⟨_, _⟩
    have : z ≠ 0 := by linarith
    have : Real.log z ≠ 0 := by apply Real.log_ne_zero_of_pos_of_ne_one <;> linarith
    fun_prop
  · refine ContinuousOn.integrableOn_Icc fun z ⟨_, _⟩ ↦ ContinuousWithinAt.congr ?_
      (fun _ _ ↦ Real.deriv_inv_log_apply) Real.deriv_inv_log_apply
    have : z ≠ 0 := by linarith
    have : Real.log z ^ 2 ≠ 0 := by
      refine pow_ne_zero 2 <| Real.log_ne_zero_of_pos_of_ne_one ?_ ?_ <;> linarith
    exact ContinuousAt.continuousWithinAt <| by fun_prop

theorem intervalIntegrable_sum_div (c : ℕ → ℝ) {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t => (∑ n ∈ Icc 0 ⌊t⌋₊, c n) / (t * Real.log t ^ 2)) MeasureTheory.volume a b := by
  have hmeas : Measurable (fun t : ℝ => ∑ n ∈ Icc 0 ⌊t⌋₊, c n) :=
    (measurable_from_nat (f := fun m => ∑ n ∈ Icc 0 m, c n)).comp Nat.measurable_floor
  set B : ℝ := ∑ n ∈ Icc 0 ⌊b⌋₊, |c n| with hB
  have hbound : IntervalIntegrable (fun t : ℝ => (∑ n ∈ Icc 0 ⌊t⌋₊, c n)) MeasureTheory.volume a b := by
    refine IntervalIntegrable.mono_fun' (f := fun t => (∑ n ∈ Icc 0 ⌊t⌋₊, c n)) (g := fun _ => B)
      intervalIntegrable_const hmeas.aestronglyMeasurable ?_
    refine (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mpr (Filter.Eventually.of_forall fun t ht => ?_)
    have htb : t ≤ b := by
      have := ht.2
      simpa [max_eq_right hab] using this
    show ‖∑ n ∈ Icc 0 ⌊t⌋₊, c n‖ ≤ B
    rw [Real.norm_eq_abs]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.Icc_subset_Icc le_rfl (Nat.floor_mono htb)) (fun _ _ _ => abs_nonneg _)
  have hc : ContinuousOn (fun t : ℝ => 1 / (t * Real.log t ^ 2)) (Set.uIcc a b) := by
    have hpos : ∀ t ∈ Set.uIcc a b, 2 ≤ t := fun t ht => le_trans (le_trans ha (le_min le_rfl hab)) ht.1
    apply ContinuousOn.div continuousOn_const
    · exact continuousOn_id.mul ((Real.continuousOn_log.mono
        (fun t ht => by simp; linarith [hpos t ht])).pow 2)
    · intro t ht
      have h2 := hpos t ht
      exact mul_ne_zero (by linarith) (pow_ne_zero 2 (Real.log_pos (by linarith)).ne')
  have he : (fun t : ℝ => (∑ n ∈ Icc 0 ⌊t⌋₊, c n) / (t * Real.log t ^ 2)) =
      fun t => (∑ n ∈ Icc 0 ⌊t⌋₊, c n) * (1 / (t * Real.log t ^ 2)) := by
    funext t
    ring
  rw [he]
  exact hbound.mul_continuousOn hc

theorem intervalIntegrable_inv_log' {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    IntervalIntegrable (fun t => 1 / Real.log t) MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  have h1 : ∀ t ∈ Set.uIcc a b, 1 < t := fun t ht => lt_of_lt_of_le (lt_min ha hb) ht.1
  apply ContinuousOn.div continuousOn_const
  · exact Real.continuousOn_log.mono (fun t ht => ne_of_gt (lt_trans zero_lt_one (h1 t ht)))
  · intro t ht
    exact ne_of_gt (Real.log_pos (h1 t ht))

theorem integral_rpow_div_log {β X : ℝ} (hβ : 0 < β) (hX : 2 ≤ X) :
    ∫ t in (2 : ℝ)..X, t ^ (β - 1) / Real.log t = liX (X ^ β) - liX ((2 : ℝ) ^ β) := by
  have h1X : 1 < X ^ β := Real.one_lt_rpow (by linarith) hβ
  have h12 : 1 < (2 : ℝ) ^ β := Real.one_lt_rpow (by norm_num) hβ
  have hsub : liX (X ^ β) - liX ((2 : ℝ) ^ β) = ∫ u in ((2 : ℝ) ^ β)..(X ^ β), 1 / Real.log u := by
    unfold liX
    exact intervalIntegral.integral_interval_sub_left (intervalIntegrable_inv_log' (by norm_num) h1X)
      (intervalIntegrable_inv_log' (by norm_num) h12)
  rw [hsub]
  have key := intervalIntegral.integral_comp_mul_deriv' (a := 2) (b := X) (f := fun t : ℝ => t ^ β)
    (f' := fun t : ℝ => β * t ^ (β - 1)) (g := fun u : ℝ => 1 / Real.log u) ?_ ?_ ?_
  · rw [← key]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hX] at ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hl : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
    simp only [Function.comp]
    rw [Real.log_rpow ht0]
    field_simp
  · intro t ht
    rw [Set.uIcc_of_le hX] at ht
    exact Real.hasDerivAt_rpow_const (Or.inl (by linarith [ht.1]))
  · intro t ht
    rw [Set.uIcc_of_le hX] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    exact (continuousAt_const.mul (Real.continuousAt_rpow_const t (β - 1) (Or.inl ht0))).continuousWithinAt
  · rintro u ⟨t, ht, rfl⟩
    rw [Set.uIcc_of_le hX] at ht
    have h1 : 1 < t ^ β := Real.one_lt_rpow (by linarith [ht.1]) hβ
    exact ((continuousAt_const).div (Real.continuousAt_log (by linarith)) (Real.log_pos h1).ne').continuousWithinAt

def Fm (K θ β t : ℝ) : ℝ := K * (t - θ * t ^ β / β)

theorem continuousOn_Fm_div_mul_log_sq (K θ β : ℝ) {a b : ℝ} (ha : 2 ≤ a) :
    ContinuousOn (fun t => Fm K θ β t / (t * Real.log t ^ 2)) (Set.Icc a b) := by
  have hpos : ∀ t ∈ Set.Icc a b, 2 ≤ t := fun t ht => le_trans ha ht.1
  apply ContinuousOn.div
  · change ContinuousOn (fun t : ℝ => K * (t - θ * t ^ β / β)) (Set.Icc a b)
    exact continuousOn_const.mul (continuousOn_id.sub
      ((continuousOn_const.mul (ContinuousOn.rpow_const continuousOn_id
        (fun t ht => Or.inl (by simp; linarith [hpos t ht])))).div_const β))
  · exact continuousOn_id.mul ((Real.continuousOn_log.mono
      (fun t ht => by simp; linarith [hpos t ht])).pow 2)
  · intro t ht
    have h2 := hpos t ht
    exact mul_ne_zero (by linarith) (pow_ne_zero 2 (Real.log_pos (by linarith)).ne')

theorem intervalIntegrable_Fm_div_mul_log_sq (K θ β : ℝ) {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t => Fm K θ β t / (t * Real.log t ^ 2)) MeasureTheory.volume a b := by
  exact (continuousOn_Fm_div_mul_log_sq K θ β ha).intervalIntegrable_of_Icc hab

theorem Fm_parts (K θ : ℝ) {β X : ℝ} (hβ : 0 < β) (hX : 2 ≤ X) :
    Fm K θ β X / Real.log X + ∫ t in (2 : ℝ)..X, Fm K θ β t / (t * Real.log t ^ 2) =
      Fm K θ β 2 / Real.log 2 + K * (liX X - θ * (liX (X ^ β) - liX ((2 : ℝ) ^ β))) := by
  have hder : ∀ t ∈ Set.uIcc 2 X, HasDerivAt (fun t => Fm K θ β t / Real.log t)
      (K * (1 / Real.log t) - K * θ * (t ^ (β - 1) / Real.log t) - Fm K θ β t / (t * Real.log t ^ 2)) t := by
    intro t ht
    rw [Set.uIcc_of_le hX] at ht
    have h0 : t ≠ 0 := by linarith [ht.1]
    have h1 : Real.log t ≠ 0 := by apply Real.log_ne_zero_of_pos_of_ne_one <;> linarith [ht.1]
    have hp : HasDerivAt (fun t : ℝ => t ^ β) (β * t ^ (β - 1)) t := Real.hasDerivAt_rpow_const (Or.inl h0)
    have hF : HasDerivAt (fun t => Fm K θ β t) (K * (1 - θ * (β * t ^ (β - 1)) / β)) t := by
      unfold Fm
      exact (((hasDerivAt_id t).sub ((hp.const_mul θ).div_const β)).const_mul K)
    have := hF.div (Real.hasDerivAt_log h0) h1
    have hβ0 : β ≠ 0 := hβ.ne'
    refine HasDerivAt.congr_deriv (f := fun t => Fm K θ β t / Real.log t) this ?_
    generalize Fm K θ β t = F
    field_simp
  have hi1 : IntervalIntegrable (fun t => K * (1 / Real.log t)) MeasureTheory.volume 2 X :=
    (intervalIntegrable_inv_log le_rfl hX).const_mul K
  have hi2' : IntervalIntegrable (fun t : ℝ => t ^ (β - 1) / Real.log t) MeasureTheory.volume 2 X := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [Set.uIcc_of_le hX] at ht
    have h0 : t ≠ 0 := by linarith [ht.1]
    have h1 : Real.log t ≠ 0 := by apply Real.log_ne_zero_of_pos_of_ne_one <;> linarith [ht.1]
    exact ((Real.continuousAt_rpow_const t (β - 1) (Or.inl h0)).div (Real.continuousAt_log h0) h1).continuousWithinAt
  have hi2 := hi2'.const_mul (K * θ)
  have hi3 := intervalIntegrable_Fm_div_mul_log_sq K θ β le_rfl hX
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hder ((hi1.sub hi2).sub hi3)
  rw [intervalIntegral.integral_sub (hi1.sub hi2) hi3, intervalIntegral.integral_sub hi1 hi2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_rpow_div_log hβ hX] at hftc
  have hli : ∫ t in (2 : ℝ)..X, 1 / Real.log t = liX X := rfl
  rw [hli] at hftc
  linarith

theorem Fm_abs_le {K θ β t : ℝ} (hK0 : 0 ≤ K) (hK1 : K ≤ 1) (hθ : |θ| ≤ 1) (hβ : 1 / 2 ≤ β) (hβ1 : β ≤ 1)
    (ht : 1 ≤ t) : |Fm K θ β t| ≤ 3 * t := by
  have hb : 0 < β := by linarith
  have htb : t ^ β ≤ t := by
    have := Real.rpow_le_rpow_of_exponent_le ht hβ1
    rwa [Real.rpow_one] at this
  have htpos : 0 ≤ t ^ β := Real.rpow_nonneg (by linarith) _
  unfold Fm
  rw [abs_mul, abs_of_nonneg hK0]
  have h3 : |θ * t ^ β / β| ≤ 2 * t := by
    rw [abs_div, abs_mul, abs_of_nonneg htpos, abs_of_pos hb, div_le_iff₀ hb]
    nlinarith [mul_le_mul_of_nonneg_right hθ htpos, abs_nonneg θ]
  have h2 : |t - θ * t ^ β / β| ≤ 3 * t := by
    calc |t - θ * t ^ β / β| ≤ |t| + |θ * t ^ β / β| := abs_sub _ _
      _ ≤ t + 2 * t := by rw [abs_of_nonneg (by linarith)]; linarith
      _ = 3 * t := by ring
  calc K * |t - θ * t ^ β / β| ≤ 1 * (3 * t) := mul_le_mul hK1 h2 (abs_nonneg _) (by norm_num)
    _ = 3 * t := one_mul _

theorem liX_two_rpow_abs {β : ℝ} (hβ : 1 / 2 ≤ β) (hβ1 : β ≤ 1) : |liX ((2 : ℝ) ^ β)| ≤ 4 := by
  unfold liX
  have h1 : (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 ^ β := Real.rpow_le_rpow_of_exponent_le (by norm_num) hβ
  have h2 : (2 : ℝ) ^ β ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hβ1
  have h3 : (1 : ℝ) < 2 ^ (1 / 2 : ℝ) := Real.one_lt_rpow (by norm_num) (by norm_num)
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 2) (b := (2 : ℝ) ^ β)
    (f := fun t => 1 / Real.log t) (C := 4) ?_
  · rw [Real.norm_eq_abs] at this
    calc _ ≤ 4 * |(2 : ℝ) ^ β - 2| := this
      _ ≤ 4 * 1 := by
          gcongr
          rw [abs_le]; constructor <;> linarith
      _ = 4 := by norm_num
  · intro t ht
    rw [Set.uIoc_of_ge h2] at ht
    have hl : Real.log 2 / 2 ≤ Real.log t := by
      have : Real.log ((2 : ℝ) ^ (1 / 2 : ℝ)) ≤ Real.log t := Real.log_le_log (by positivity) (by linarith [ht.1])
      rw [Real.log_rpow (by norm_num)] at this; linarith
    have hl2 := Real.log_two_gt_d9
    have hl3 : 0 < Real.log t := by linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_iff₀ hl3]
    linarith

theorem abel_core (c : ℕ → ℝ) (hc0 : ∀ n, 0 ≤ c n) (hcΛ : ∀ n, c n ≤ ArithmeticFunction.vonMangoldt n)
    {K θ β D X : ℝ} (hK0 : 0 ≤ K) (hK1 : K ≤ 1) (hθ : |θ| ≤ 1) (hβ : 1 / 2 ≤ β) (hβ1 : β ≤ 1) (hX : 16 ≤ X)
    (hD : 0 ≤ D)
    (h : ∀ t, √X ≤ t → t ≤ X → |(∑ n ∈ Icc 0 ⌊t⌋₊, c n) - Fm K θ β t| ≤ D * t) :
    |∑ n ∈ Icc 0 ⌊X⌋₊, (Real.log n)⁻¹ * c n - K * (liX X - θ * liX (X ^ β))| ≤
      5 * D * X / Real.log X + 40 * √X := by
  have h0 : c 0 = 0 := le_antisymm (by simpa using hcΛ 0) (hc0 0)
  have h1 : c 1 = 0 := le_antisymm (by simpa using hcΛ 1) (hc0 1)
  have hX2 : 2 ≤ X := by linarith
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hs4 : 4 ≤ √X := by rw [Real.le_sqrt' (by norm_num)]; linarith
  have hss : √X * √X = X := Real.mul_self_sqrt (by linarith)
  have hsX : √X ≤ X := by nlinarith
  have hL : 1 ≤ Real.log X := by
    have h16 : Real.log 16 = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
    have := Real.log_le_log (by norm_num) hX
    linarith
  have hL0 : 0 < Real.log X := by linarith
  have habel := abel_log c h0 h1 hX2
  have hparts := Fm_parts K θ (by linarith : 0 < β) hX2
  set Ψ : ℝ → ℝ := fun t => ∑ n ∈ Icc 0 ⌊t⌋₊, c n with hΨ
  set g : ℝ → ℝ := fun t => Ψ t / (t * Real.log t ^ 2) - Fm K θ β t / (t * Real.log t ^ 2) with hg
  have hgi : ∀ a b : ℝ, 2 ≤ a → a ≤ b → IntervalIntegrable g MeasureTheory.volume a b := fun a b ha hab =>
    (intervalIntegrable_sum_div c ha hab).sub (intervalIntegrable_Fm_div_mul_log_sq K θ β ha hab)
  have hI : ∫ t in (2 : ℝ)..X, g t = (∫ t in (2 : ℝ)..X, Ψ t / (t * Real.log t ^ 2)) -
      ∫ t in (2 : ℝ)..X, Fm K θ β t / (t * Real.log t ^ 2) :=
    intervalIntegral.integral_sub (intervalIntegrable_sum_div c le_rfl hX2) (intervalIntegrable_Fm_div_mul_log_sq K θ β le_rfl hX2)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (hgi 2 (√X) le_rfl (by linarith))
    (hgi (√X) X (by linarith) hsX)
  have hΨle : ∀ t : ℝ, 0 ≤ t → |Ψ t| ≤ 6 * t := by
    intro t ht
    have hn : 0 ≤ Ψ t := Finset.sum_nonneg (fun n _ => hc0 n)
    rw [abs_of_nonneg hn]
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    calc Ψ t ≤ ∑ n ∈ Icc 0 ⌊t⌋₊, ArithmeticFunction.vonMangoldt n := Finset.sum_le_sum (fun n _ => hcΛ n)
      _ = Chebyshev.psi t := (Chebyshev.psi_eq_sum_Icc t).symm
      _ ≤ (Real.log 4 + 4) * t := Chebyshev.psi_le_const_mul_self ht
      _ ≤ 6 * t := by gcongr; linarith
  have hI1 : |∫ t in (2 : ℝ)..√X, g t| ≤ 36 * |√X - 2| := by
    rw [← Real.norm_eq_abs]
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t ht
    rw [Set.uIoc_of_le (by linarith)] at ht
    have ht2 : 2 < t := ht.1
    have hlt : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht2.le
    have hsq : 1 / 4 ≤ Real.log t ^ 2 := by nlinarith
    have hpos : 0 < t * Real.log t ^ 2 := by positivity
    have ha := hΨle t (by linarith)
    have hb := Fm_abs_le hK0 hK1 hθ hβ hβ1 (by linarith : 1 ≤ t)
    rw [Real.norm_eq_abs, hg]
    simp only []
    rw [← sub_div, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
    have hab : |Ψ t - Fm K θ β t| ≤ 9 * t := by
      rw [abs_le] at ha hb ⊢
      constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]
    nlinarith
  have hI2 : |∫ t in (√X)..X, g t| ≤ 4 * D / Real.log X ^ 2 * |X - √X| := by
    rw [← Real.norm_eq_abs]
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t ht
    rw [Set.uIoc_of_le hsX] at ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hlt : Real.log X / 2 ≤ Real.log t := by
      rw [← Real.log_sqrt (by linarith)]
      exact Real.log_le_log (by linarith) ht.1.le
    have hlt0 : 0 < Real.log t := by linarith
    have hsq : Real.log X ^ 2 ≤ 4 * Real.log t ^ 2 := by nlinarith
    have hpos : 0 < t * Real.log t ^ 2 := by positivity
    rw [Real.norm_eq_abs, hg]
    simp only []
    rw [← sub_div, abs_div, abs_of_pos hpos, div_le_iff₀ hpos, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    calc |Ψ t - Fm K θ β t| * Real.log X ^ 2 ≤ (D * t) * (4 * Real.log t ^ 2) := by
          gcongr
          exact h t ht.1.le ht.2
      _ = 4 * D * (t * Real.log t ^ 2) := by ring
  have heq : ∑ n ∈ Icc 0 ⌊X⌋₊, (Real.log n)⁻¹ * c n - K * (liX X - θ * liX (X ^ β)) =
      (Ψ X - Fm K θ β X) / Real.log X + ((∫ t in (2 : ℝ)..√X, g t) + ∫ t in (√X)..X, g t) +
        Fm K θ β 2 / Real.log 2 + K * θ * liX ((2 : ℝ) ^ β) := by
    have e1 : K * (liX X - θ * (liX (X ^ β) - liX ((2 : ℝ) ^ β))) =
        K * (liX X - θ * liX (X ^ β)) + K * θ * liX ((2 : ℝ) ^ β) := by ring
    have e2 : (Ψ X - Fm K θ β X) / Real.log X = Ψ X / Real.log X - Fm K θ β X / Real.log X := sub_div _ _ _
    linarith [habel, hparts, hI, hsplit]
  have b1 : |(Ψ X - Fm K θ β X) / Real.log X| ≤ D * X / Real.log X := by
    rw [abs_div, abs_of_pos hL0]
    gcongr
    exact h X hsX le_rfl
  have b2 : |Fm K θ β 2 / Real.log 2| ≤ 12 := by
    have := Fm_abs_le hK0 hK1 hθ hβ hβ1 (by norm_num : (1 : ℝ) ≤ 2)
    rw [abs_div, abs_of_pos (by linarith : 0 < Real.log 2), div_le_iff₀ (by linarith)]
    linarith
  have b3 : |K * θ * liX ((2 : ℝ) ^ β)| ≤ 4 := by
    rw [abs_mul, abs_mul, abs_of_nonneg hK0]
    calc K * |θ| * |liX ((2 : ℝ) ^ β)| ≤ 1 * 1 * 4 := by
          gcongr
          exact liX_two_rpow_abs hβ hβ1
      _ = 4 := by norm_num
  have b4 : 4 * D / Real.log X ^ 2 * |X - √X| ≤ 4 * (D * X / Real.log X) := by
    rw [abs_of_nonneg (by linarith)]
    have hDX : 0 ≤ D * X := by positivity
    have : D * X / Real.log X ^ 2 ≤ D * X / Real.log X := by
      apply div_le_div_of_nonneg_left hDX hL0
      nlinarith
    calc 4 * D / Real.log X ^ 2 * (X - √X) ≤ 4 * D / Real.log X ^ 2 * X := by
          gcongr
          linarith
      _ = 4 * (D * X / Real.log X ^ 2) := by ring
      _ ≤ _ := by linarith
  have b5 : 36 * |√X - 2| ≤ 36 * √X - 72 := by
    rw [abs_of_nonneg (by linarith)]; linarith
  rw [heq]
  have e5 : 5 * D * X / Real.log X = 5 * (D * X / Real.log X) := by ring
  rw [e5]
  rw [abs_le] at *
  constructor <;> linarith [b1.1, b1.2, b2.1, b2.2, b3.1, b3.2, hI1.1, hI1.2, hI2.1, hI2.2]

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet ArithmeticFunction

def cAP (M b n : ℕ) : ℝ := if n ≡ b [MOD M] then Λ n else 0

theorem vonMangoldtAP_nonneg (M b n : ℕ) : 0 ≤ cAP M b n := by
  unfold cAP
  split_ifs
  · exact vonMangoldt_nonneg
  · exact le_refl _

theorem vonMangoldtAP_le (M b n : ℕ) : cAP M b n ≤ Λ n := by
  unfold cAP
  split_ifs
  · exact le_refl _
  · exact vonMangoldt_nonneg

theorem sum_cAP (M b : ℕ) (t : ℝ) : ∑ n ∈ Icc 0 ⌊t⌋₊, cAP M b n = psiAP M b t := by
  unfold cAP Formalism.ZeroFreeDirichlet.psiAP
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_subset
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_Icc] at hx ⊢
    exact ⟨⟨Nat.zero_le _, hx.1.2⟩, hx.2⟩
  · intro x hx hnx
    simp only [Finset.mem_filter, Finset.mem_Icc] at hx hnx
    have hx0 : x = 0 := by
      by_contra h
      exact hnx ⟨⟨Nat.pos_of_ne_zero h, hx.1.2⟩, hx.2⟩
    subst hx0
    simp

theorem abs_piAP_sub_le (M b : ℕ) {X : ℝ} (hX : 1 ≤ X) :
    |(piAP X M b : ℝ) - ∑ n ∈ Icc 0 ⌊X⌋₊, (Real.log n)⁻¹ * cAP M b n| ≤ 4 * √X * Real.log X := by
  have hpi : (piAP X M b : ℝ) = ∑ n ∈ Icc 0 ⌊X⌋₊, (if n.Prime ∧ n % M = b % M then (1 : ℝ) else 0) := by
    unfold piAP
    rw [Finset.card_filter]
    push_cast
    apply Finset.sum_subset (Finset.Icc_subset_Icc (by norm_num) le_rfl)
    intro n hn hn'
    have : n = 0 := by
      rw [Finset.mem_Icc] at hn hn'
      omega
    subst this
    simp [Nat.not_prime_zero]
  have hl2 := Real.log_two_gt_d9
  have hterm : ∀ n : ℕ, 0 ≤ (Real.log n)⁻¹ * cAP M b n - (if n.Prime ∧ n % M = b % M then (1 : ℝ) else 0) ∧
      (Real.log n)⁻¹ * cAP M b n - (if n.Prime ∧ n % M = b % M then (1 : ℝ) else 0) ≤
        2 * (if ¬ n.Prime then Λ n else 0) := by
    intro n
    by_cases hp : n.Prime
    · have hlog : Real.log n ≠ 0 := (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
      by_cases hm : n % M = b % M
      · have hm' : n ≡ b [MOD M] := hm
        simp [cAP, hp, hm, hm', vonMangoldt_apply_prime hp, hlog]
      · have hm' : ¬ n ≡ b [MOD M] := hm
        simp [cAP, hp, hm, hm']
    · simp only [hp, false_and, if_false, sub_zero, not_false_eq_true, if_true]
      rcases Nat.lt_or_ge n 2 with h2 | h2
      · have h0 : Λ n = 0 := by
          interval_cases n <;> simp
        have h0' : cAP M b n = 0 := le_antisymm (h0 ▸ vonMangoldtAP_le M b n) (vonMangoldtAP_nonneg M b n)
        simp [h0, h0']
      · have hln : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast h2)
        have hpos : 0 < Real.log n := by linarith
        have hinv : (Real.log n)⁻¹ ≤ 2 := by
          rw [inv_le_comm₀ hpos (by norm_num)]; linarith
        constructor
        · exact mul_nonneg (inv_nonneg.2 hpos.le) (vonMangoldtAP_nonneg M b n)
        · exact mul_le_mul hinv (vonMangoldtAP_le M b n) (vonMangoldtAP_nonneg M b n) (by norm_num)
  have hsum : ∑ n ∈ Icc 0 ⌊X⌋₊, (if ¬ n.Prime then Λ n else 0) = Chebyshev.psi X - Chebyshev.theta X := by
    rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Finset.sum_filter]
    symm
    apply Finset.sum_subset
    · intro n hn
      rw [Finset.mem_Ioc] at hn
      exact Finset.mem_Icc.2 ⟨by omega, hn.2⟩
    · intro n hn hn'
      have : n = 0 := by
        rw [Finset.mem_Icc] at hn
        rw [Finset.mem_Ioc] at hn'
        omega
      subst this
      simp
  have hpt := Chebyshev.psi_sub_theta_le hX
  rw [hpi, abs_sub_comm, ← Finset.sum_sub_distrib, abs_of_nonneg (Finset.sum_nonneg fun n _ => (hterm n).1)]
  calc _ ≤ ∑ n ∈ Icc 0 ⌊X⌋₊, 2 * (if ¬ n.Prime then Λ n else 0) := Finset.sum_le_sum fun n _ => (hterm n).2
    _ = 2 * (Chebyshev.psi X - Chebyshev.theta X) := by rw [← Finset.mul_sum, hsum]
    _ ≤ _ := by linarith

theorem abs_psiAP_sub_le (M : ℕ) [NeZero M] (b : ℕ) (hb : b.Coprime M) (e : Option (DirichletCharacter ℂ M × ℝ))
    (θ β t : ℝ)
    (hmain : ∑ χ : DirichletCharacter ℂ M, χ ((b : ZMod M)⁻¹) * mainPsi e χ t =
      ((t - θ * t ^ β / β : ℝ) : ℂ)) :
    |psiAP M b t - Fm (1 / (M.totient : ℝ)) θ β t| ≤
      (∑ χ : DirichletCharacter ℂ M, ‖psiChi χ t - mainPsi e χ t‖) / (M.totient : ℝ) := by
  have hφ : (0 : ℝ) < M.totient := by exact_mod_cast Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne M))
  have hid := chebyshev_progression_orthogonality M b hb t
  have h1 : (((M.totient : ℝ) * psiAP M b t - (t - θ * t ^ β / β) : ℝ) : ℂ) =
      ∑ χ : DirichletCharacter ℂ M, χ ((b : ZMod M)⁻¹) * (psiChi χ t - mainPsi e χ t) := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [← hid, hmain]
    push_cast
    ring
  have h2 : |(M.totient : ℝ) * psiAP M b t - (t - θ * t ^ β / β)| ≤
      ∑ χ : DirichletCharacter ℂ M, ‖psiChi χ t - mainPsi e χ t‖ := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real, h1]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun χ _ => ?_)
    rw [norm_mul]
    calc ‖χ ((b : ZMod M)⁻¹)‖ * ‖psiChi χ t - mainPsi e χ t‖ ≤ 1 * ‖psiChi χ t - mainPsi e χ t‖ := by
          gcongr
          exact χ.norm_le_one _
      _ = _ := one_mul _
  rw [le_div_iff₀ hφ]
  have h3 : (psiAP M b t - Fm (1 / (M.totient : ℝ)) θ β t) * (M.totient : ℝ) =
      (M.totient : ℝ) * psiAP M b t - (t - θ * t ^ β / β) := by
    unfold Fm
    field_simp
  calc |psiAP M b t - Fm (1 / (M.totient : ℝ)) θ β t| * (M.totient : ℝ)
      = |(psiAP M b t - Fm (1 / (M.totient : ℝ)) θ β t) * (M.totient : ℝ)| := by
        rw [abs_mul, abs_of_pos hφ]
    _ ≤ _ := by rw [h3]; exact h2

theorem mainPsi_sum_none (M : ℕ) [NeZero M] (b : ℕ) (hb : b.Coprime M) (t β : ℝ) :
    ∑ χ : DirichletCharacter ℂ M, χ ((b : ZMod M)⁻¹) * mainPsi none χ t = ((t - 0 * t ^ β / β : ℝ) : ℂ) := by
  have hu : IsUnit ((b : ZMod M)⁻¹) := by
    have h1 : IsUnit (b : ZMod M) := (ZMod.isUnit_iff_coprime b M).mpr hb
    obtain ⟨u, hu⟩ := h1
    rw [← hu, ZMod.inv_coe_unit]
    exact Units.isUnit _
  simp only [mainPsi]
  simp [Finset.sum_ite_eq', MulChar.one_apply hu]

theorem mainPsi_sum_some (M : ℕ) [NeZero M] (b : ℕ) (hb : b.Coprime M) (χ₁ : DirichletCharacter ℂ M)
    (β t : ℝ) (ht : 0 ≤ t) (hχ : χ₁ (b : ZMod M) = 1 ∨ χ₁ (b : ZMod M) = -1) :
    ∑ χ : DirichletCharacter ℂ M, χ ((b : ZMod M)⁻¹) * mainPsi (some (χ₁, β)) χ t =
      ((t - (χ₁ (b : ZMod M)).re * t ^ β / β : ℝ) : ℂ) := by
  have hbu : (b : ZMod M) * (b : ZMod M)⁻¹ = 1 := ZMod.coe_mul_inv_eq_one b hb
  have hunit : IsUnit ((b : ZMod M)⁻¹) :=
    ⟨⟨(b : ZMod M)⁻¹, (b : ZMod M), by rw [mul_comm]; exact hbu, hbu⟩, rfl⟩
  have h1 : (1 : DirichletCharacter ℂ M) ((b : ZMod M)⁻¹) = 1 := MulChar.one_apply hunit
  have h2 : χ₁ ((b : ZMod M)⁻¹) = χ₁ (b : ZMod M) := by
    have h3 := congrArg χ₁ hbu
    rw [map_mul, map_one] at h3
    rcases hχ with h | h
    · rw [h, one_mul] at h3
      rw [h3, h]
    · rw [h] at h3 ⊢
      linear_combination -h3
  have hre : ((χ₁ (b : ZMod M)).re : ℂ) = χ₁ (b : ZMod M) := by
    rcases hχ with h | h <;> simp [h]
  simp only [mainPsi, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, h1, h2]
  push_cast
  rw [hre, Complex.ofReal_cpow ht]
  ring

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet ArithmeticFunction

theorem main_lower {θ β η l X : ℝ} (hθ : |θ| ≤ 1) (hβ : 1 / 2 ≤ β) (hβ1 : β ≤ 1) (hX : 16 ≤ X)
    (hl : l ≤ Real.log X) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hη : θ ≤ 0 ∨ η ≤ (1 - β) * l) :
    X * η / (2 * Real.log X) ≤ liX X - θ * liX (X ^ β) := by
  have hX0 : 0 < X := by linarith
  have hL0 : 0 < Real.log X := Real.log_pos (by linarith)
  have h2 : 2 ≤ X ^ β := by
    calc (2 : ℝ) ≤ 4 := by norm_num
      _ = √16 := by
          rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      _ ≤ √X := Real.sqrt_le_sqrt hX
      _ = X ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow X
      _ ≤ X ^ β := Real.rpow_le_rpow_of_exponent_le (by linarith) hβ
  have hXβ : X ^ β ≤ X := by
    calc X ^ β ≤ X ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) hβ1
      _ = X := Real.rpow_one X
  have hli := liX_nonneg h2
  rcases hη with h | h
  · have h1 := liX_lower (by linarith : 4 ≤ X)
    have h3 : X * η / (2 * Real.log X) ≤ X / (2 * Real.log X) := by
      gcongr
      nlinarith
    nlinarith
  · have h1 := liX_sub_ge h2 hXβ
    have hθ1 : θ ≤ 1 := (abs_le.1 hθ).2
    have h3 : liX X - liX (X ^ β) ≤ liX X - θ * liX (X ^ β) := by nlinarith
    have hw : η ≤ (1 - β) * Real.log X := h.trans (mul_le_mul_of_nonneg_left hl (by linarith))
    have he : X ^ β = X * Real.exp (-((1 - β) * Real.log X)) := by
      rw [Real.rpow_def_of_pos hX0]
      nth_rw 2 [← Real.exp_log hX0]
      rw [← Real.exp_add]
      congr 1
      ring
    have he2 : Real.exp (-((1 - β) * Real.log X)) ≤ 1 - η / 2 :=
      (Real.exp_le_exp.2 (by linarith)).trans (exp_neg_le_one_sub_half hη0 hη1)
    have h4 : X * η / 2 ≤ X - X ^ β := by
      rw [he]
      nlinarith
    have h5 : X * η / (2 * Real.log X) ≤ (X - X ^ β) / Real.log X := by
      rw [show X * η / (2 * Real.log X) = (X * η / 2) / Real.log X by field_simp]
      gcongr
    linarith

theorem exp_sum_le_min_exponent {c l L u : ℝ} (hc : 0 < c) (hl : 0 < l) (hL : 0 ≤ L) (hu : L / 2 ≤ u) :
    Real.exp (-(c * u / l)) + Real.exp (-(c * Real.sqrt u)) ≤
      Real.exp (-(min (c / 2) (c ^ 2 / 2) * L / l)) + Real.exp (-Real.sqrt (min (c / 2) (c ^ 2 / 2) * L)) := by
  have hu0 : 0 ≤ u := by linarith
  have hm1 : min (c / 2) (c ^ 2 / 2) ≤ c / 2 := min_le_left _ _
  have hm2 : min (c / 2) (c ^ 2 / 2) ≤ c ^ 2 / 2 := min_le_right _ _
  have hm0 : 0 ≤ min (c / 2) (c ^ 2 / 2) := le_min (by positivity) (by positivity)
  apply add_le_add
  · apply Real.exp_le_exp.mpr
    rw [neg_le_neg_iff]
    apply div_le_div_of_nonneg_right _ hl.le
    have h1 := mul_le_mul_of_nonneg_right hm1 hL
    nlinarith
  · apply Real.exp_le_exp.mpr
    rw [neg_le_neg_iff]
    rw [show c * Real.sqrt u = Real.sqrt (c ^ 2 * u) by
      rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc.le]]
    apply Real.sqrt_le_sqrt
    have h1 := mul_le_mul_of_nonneg_right hm2 hL
    nlinarith

theorem small_terms {c₃ c₁ L l η φ : ℝ} (hc₃ : 0 ≤ c₃) (hc₁ : 0 < c₁) (hL : 16 * l ≤ L) (hL1 : 1 ≤ L)
    (hη : c₁ * Real.exp (-l) ≤ η) (hφ0 : 0 < φ) (hφ : φ ≤ Real.exp l) :
    44 * Real.exp (L / 2) * L ≤
      5632 * Real.exp (2 * c₃) / c₁ * Real.exp (-Real.sqrt (c₃ * L)) * (Real.exp L * η / (2 * L) / φ) := by
  have hL0 : 0 < L := by linarith
  have hsq : Real.sqrt (c₃ * L) ≤ 2 * c₃ + L / 8 := by
    calc Real.sqrt (c₃ * L) ≤ Real.sqrt ((2 * c₃ + L / 8) ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (2 * c₃ - L / 8)])
      _ = 2 * c₃ + L / 8 := Real.sqrt_sq (by positivity)
  have hexpL : L ^ 2 ≤ 64 * Real.exp (L / 4) := by
    have h := Real.quadratic_le_exp_of_nonneg (x := L / 4) (by positivity)
    nlinarith
  have hsplit : Real.exp (3 * L / 4) = Real.exp (L / 2) * Real.exp (L / 4) := by
    rw [← Real.exp_add]
    ring_nf
  have key : 2816 * Real.exp (2 * c₃ - Real.sqrt (c₃ * L) + L - 2 * l) / L =
      5632 * Real.exp (2 * c₃) / c₁ * Real.exp (-Real.sqrt (c₃ * L)) *
        (Real.exp L * (c₁ * Real.exp (-l)) / (2 * L) / Real.exp l) := by
    have e : Real.exp (2 * c₃ - Real.sqrt (c₃ * L) + L - 2 * l) =
        Real.exp (2 * c₃) * Real.exp (-Real.sqrt (c₃ * L)) * Real.exp L * Real.exp (-l) / Real.exp l := by
      rw [show 2 * c₃ - Real.sqrt (c₃ * L) + L - 2 * l = 2 * c₃ + -Real.sqrt (c₃ * L) + L + -l - l by ring,
        Real.exp_sub, Real.exp_add, Real.exp_add, Real.exp_add]
    rw [e]
    field_simp
    ring
  calc 44 * Real.exp (L / 2) * L ≤ 2816 * Real.exp (3 * L / 4) / L := by
        rw [le_div_iff₀ hL0, hsplit]
        have hp := Real.exp_pos (L / 2)
        nlinarith
    _ ≤ 2816 * Real.exp (2 * c₃ - Real.sqrt (c₃ * L) + L - 2 * l) / L := by
        apply div_le_div_of_nonneg_right _ hL0.le
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Real.exp_le_exp.mpr
        linarith
    _ = 5632 * Real.exp (2 * c₃) / c₁ * Real.exp (-Real.sqrt (c₃ * L)) *
        (Real.exp L * (c₁ * Real.exp (-l)) / (2 * L) / Real.exp l) := key
    _ ≤ 5632 * Real.exp (2 * c₃) / c₁ * Real.exp (-Real.sqrt (c₃ * L)) * (Real.exp L * η / (2 * L) / φ) := by
        gcongr
        exact div_nonneg (mul_nonneg (Real.exp_pos L).le (le_trans (mul_pos hc₁ (Real.exp_pos _)).le hη)) (by positivity)

theorem pi_core (M : ℕ) [NeZero M] (h8 : 8 ∣ M) (b : ℕ) (hb : b.Coprime M)
    (e : Option (DirichletCharacter ℂ M × ℝ)) {θ β η c A c₁ X : ℝ}
    (hθ : |θ| ≤ 1) (hβ : 1 / 2 ≤ β) (hβ1 : β ≤ 1)
    (hmain : ∀ t : ℝ, 0 ≤ t → ∑ χ : DirichletCharacter ℂ M, χ ((b : ZMod M)⁻¹) * mainPsi e χ t =
      ((t - θ * t ^ β / β : ℝ) : ℂ))
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hη : θ ≤ 0 ∨ η ≤ (1 - β) * Real.log M) (hc₁ : 0 < c₁)
    (hηl : c₁ * (M : ℝ) ^ (-1 : ℝ) ≤ η) (hc : 0 < c) (hA : 0 ≤ A) (hX : 0 < X)
    (hL : 16 * Real.log M ≤ Real.log X)
    (hP : ∀ y : ℝ, √X ≤ y → y ≤ X → ∑ χ : DirichletCharacter ℂ M, ‖psiChi χ y - mainPsi e χ y‖ ≤
      A * y * η * (Real.exp (-(c * Real.log y / Real.log M)) + Real.exp (-(c * Real.sqrt (Real.log y))))) :
    |(piAP X M b : ℝ) - (liX X - θ * liX (X ^ β)) / (M.totient : ℝ)| ≤
      (10 * A + 5632 * Real.exp (2 * min (c / 2) (c ^ 2 / 2)) / c₁) *
        (Real.exp (-(min (c / 2) (c ^ 2 / 2) * Real.log X / Real.log M)) +
          Real.exp (-Real.sqrt (min (c / 2) (c ^ 2 / 2) * Real.log X))) *
        ((liX X - θ * liX (X ^ β)) / (M.totient : ℝ)) := by
  have hMpos : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hM8 : (8 : ℝ) ≤ M := by exact_mod_cast Nat.le_of_dvd hMpos h8
  have hM0 : (0 : ℝ) < M := by linarith
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hl : 2 ≤ Real.log M := by
    have h88 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
    have := Real.log_le_log (by norm_num) hM8
    linarith
  have hX16 : 16 ≤ X := by
    have h16 : Real.log 16 = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
    rw [← Real.log_le_log_iff (by norm_num) hX]
    linarith
  have hφ1 : (1 : ℝ) ≤ M.totient := by exact_mod_cast Nat.totient_pos.2 hMpos
  have hφM : (M.totient : ℝ) ≤ M := by exact_mod_cast Nat.totient_le M
  have hφ0 : (0 : ℝ) < M.totient := by linarith
  set l := Real.log M with hldef
  set L := Real.log X with hLdef
  set φ : ℝ := (M.totient : ℝ) with hφdef
  set c₃ := min (c / 2) (c ^ 2 / 2) with hc₃def
  have hc₃ : 0 ≤ c₃ := le_min (by positivity) (by positivity)
  set E := Real.exp (-(c₃ * L / l)) + Real.exp (-Real.sqrt (c₃ * L)) with hEdef
  have hE0 : 0 ≤ E := by positivity
  have hL32 : 32 ≤ L := by linarith
  have hs0 : 0 ≤ √X := Real.sqrt_nonneg X
  have hcore := abel_core (cAP M b) (vonMangoldtAP_nonneg M b) (vonMangoldtAP_le M b) (K := 1 / φ) (θ := θ) (β := β)
    (D := A * η * E / φ) (X := X) (by positivity) (by rw [div_le_one hφ0]; exact hφ1) hθ hβ hβ1 hX16
    (by positivity) (by
      intro t h1 h2
      have hs4 : 0 < √X := Real.sqrt_pos.2 hX
      have ht0 : 0 < t := by linarith
      have hu : L / 2 ≤ Real.log t := by
        rw [hLdef, ← Real.log_sqrt hX.le]
        exact Real.log_le_log hs4 h1
      rw [sum_cAP]
      calc |psiAP M b t - Fm (1 / φ) θ β t|
          ≤ (∑ χ : DirichletCharacter ℂ M, ‖psiChi χ t - mainPsi e χ t‖) / φ :=
            abs_psiAP_sub_le M b hb e θ β t (hmain t ht0.le)
        _ ≤ (A * t * η * E) / φ := by
            gcongr
            refine (hP t h1 h2).trans ?_
            gcongr
            exact exp_sum_le_min_exponent hc (by linarith) (by linarith) hu
        _ = A * η * E / φ * t := by ring)
  have hpp := abs_piAP_sub_le M b (by linarith : 1 ≤ X)
  have hm := main_lower hθ hβ hβ1 hX16 (by linarith : l ≤ L) hη0 hη1 hη
  have hexpl : Real.exp l = M := Real.exp_log hM0
  have hst := small_terms (c₃ := c₃) (c₁ := c₁) (L := L) (l := l) (η := η) (φ := φ) hc₃ hc₁ hL (by linarith)
    (by
      have : (M : ℝ) ^ (-1 : ℝ) = Real.exp (-l) := by
        rw [Real.rpow_def_of_pos hM0]; congr 1; ring
      rw [← this]; exact hηl) hφ0 (by rw [hexpl]; exact hφM)
  rw [Real.exp_half, Real.exp_log hX] at hst
  set m := liX X - θ * liX (X ^ β) with hmdef
  set P := X * η / (2 * L) / φ with hPdef
  have hP0 : 0 ≤ P := by positivity
  have hPm : P ≤ m / φ := by
    rw [hPdef]
    gcongr
  have hKm : 1 / φ * m = m / φ := by ring
  rw [hKm] at hcore
  have h5 : 5 * (A * η * E / φ) * X / L = 10 * A * E * P := by
    rw [hPdef]
    field_simp
    ring
  rw [h5] at hcore
  have h40 : 40 * √X ≤ 40 * √X * L := by nlinarith
  have hEs : Real.exp (-Real.sqrt (c₃ * L)) ≤ E := by
    rw [hEdef]
    have := Real.exp_pos (-(c₃ * L / l))
    linarith
  have hA2 : 0 ≤ 5632 * Real.exp (2 * c₃) / c₁ := by positivity
  have hst2 : 44 * √X * L ≤ 5632 * Real.exp (2 * c₃) / c₁ * E * P :=
    hst.trans (by gcongr)
  have htot : |(piAP X M b : ℝ) - m / φ| ≤ (10 * A + 5632 * Real.exp (2 * c₃) / c₁) * E * P := by
    have hexp : (10 * A + 5632 * Real.exp (2 * c₃) / c₁) * E * P =
        10 * A * E * P + 5632 * Real.exp (2 * c₃) / c₁ * E * P := by ring
    have h44 : 44 * √X * L = 4 * √X * L + 40 * √X * L := by ring
    rw [hexp]
    rw [abs_le] at hcore hpp ⊢
    constructor <;> linarith [hcore.1, hcore.2, hpp.1, hpp.2]
  exact htot.trans (by gcongr)

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet

theorem prime_count_of_psi : PiOf := by
  rintro ⟨c, A, C₀, hc, hP⟩
  obtain ⟨c₁, hc₁, hηl⟩ := etaOf_lower 1 one_pos
  refine ⟨min (c / 2) (c ^ 2 / 2), 10 * |A| + 5632 * Real.exp (2 * min (c / 2) (c ^ 2 / 2)) / c₁,
    max (2 * C₀) 16, lt_min (by positivity) (by positivity), ?_⟩
  intro M _ h8
  refine ⟨eOf M, fun p hp => eOf_exc M p hp, fun h χ₁ β₁ => eOf_none M h χ₁ β₁, ?_⟩
  intro X b hX2 hrange hb
  have hMpos : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hM8n : 8 ≤ M := Nat.le_of_dvd hMpos h8
  have hM8 : (8 : ℝ) ≤ M := by exact_mod_cast hM8n
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hl : 2 ≤ Real.log M := by
    have h88 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
    have := Real.log_le_log (by norm_num) hM8
    linarith
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hll : 1 ≤ Real.log (Real.log M + 2) := by
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 4) (by linarith : (4 : ℝ) ≤ Real.log M + 2)
    linarith
  have hprod : Real.log M ≤ Real.log M * Real.log (Real.log M + 2) := by nlinarith
  have hprod0 : 0 ≤ Real.log M * Real.log (Real.log M + 2) := by linarith
  have hrange' : max (2 * C₀) 16 * (Real.log M * Real.log (Real.log M + 2)) ≤ Real.log X := by
    rw [← mul_assoc]; exact hrange
  have hL16 : 16 * Real.log M ≤ Real.log X := by
    have := mul_le_mul_of_nonneg_right (le_max_right (2 * C₀) 16) hprod0
    linarith
  have hLC : C₀ * Real.log M * Real.log (Real.log M + 2) ≤ Real.log X / 2 := by
    have := mul_le_mul_of_nonneg_right (le_max_left (2 * C₀) 16) hprod0
    have e : C₀ * Real.log M * Real.log (Real.log M + 2) =
        2 * C₀ * (Real.log M * Real.log (Real.log M + 2)) / 2 := by ring
    rw [e]
    linarith
  have hX0 : 0 < X := by linarith
  have hX4 : 4 ≤ X := by
    rw [← Real.log_le_log_iff (by norm_num) hX0]
    linarith
  have hs2 : 2 ≤ √X := by
    rw [Real.le_sqrt' (by norm_num)]; linarith
  have hη0 : 0 ≤ etaOf M := (etaOf_pos M (by omega)).le
  have hη1 := etaOf_le_one M
  have hηl' := hηl M (by omega)
  have hP' : ∀ y : ℝ, √X ≤ y → y ≤ X →
      ∑ χ : DirichletCharacter ℂ M, ‖psiChi χ y - mainPsi (eOf M) χ y‖ ≤
      |A| * y * etaOf M *
        (Real.exp (-(c * Real.log y / Real.log M)) + Real.exp (-(c * Real.sqrt (Real.log y)))) := by
    intro y h1 h2
    have hy2 : 2 ≤ y := hs2.trans h1
    have hly : Real.log X / 2 ≤ Real.log y := by
      rw [← Real.log_sqrt hX0.le]
      exact Real.log_le_log (by linarith) h1
    refine (hP M h8 y hy2 (by linarith)).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self A) (by linarith)) hη0) (by positivity)
  rcases he : eOf M with _ | ⟨χ₁, β₁⟩
  · rw [he] at hP'
    have e0 : mainAP (none : Option (DirichletCharacter ℂ M × ℝ)) b X =
        (liX X - 0 * liX (X ^ (1 : ℝ))) / (M.totient : ℝ) := by simp [mainAP]
    rw [e0]
    exact pi_core M h8 b hb none (by simp) (by norm_num) le_rfl
      (fun t _ => mainPsi_sum_none M b hb t 1) hη0 hη1 (Or.inl le_rfl) hc₁ hηl' hc (abs_nonneg A) hX0 hL16 hP'
  · rw [he] at hP'
    obtain ⟨_, _, _, hβlo, hβ1⟩ := eOf_exc M _ he
    have hχ := eOf_char_sq M χ₁ β₁ he b ((ZMod.isUnit_iff_coprime b M).mpr hb)
    have hθ : |(χ₁ (b : ZMod M)).re| ≤ 1 := by rcases hχ with h | h <;> simp [h]
    have hβ : 1 / 2 ≤ β₁ := by
      have : 1 / (8 * Real.log M) ≤ 1 / 16 := by
        apply one_div_le_one_div_of_le (by norm_num); linarith
      simp only [] at hβlo
      linarith
    have hηe := etaOf_some M χ₁ β₁ he
    have e1 : mainAP (some (χ₁, β₁)) b X =
        (liX X - (χ₁ (b : ZMod M)).re * liX (X ^ β₁)) / (M.totient : ℝ) := rfl
    rw [e1]
    exact pi_core M h8 b hb (some (χ₁, β₁)) hθ hβ hβ1.le
      (fun t ht => mainPsi_sum_some M b hb χ₁ β₁ t ht hχ) hη0 hη1
      (Or.inr (by rw [hηe]; exact min_le_right _ _)) hc₁ hηl' hc (abs_nonneg A) hX0 hL16 hP'

end Formalism.HermitianLattices.Ext.PrimesInProgressions
