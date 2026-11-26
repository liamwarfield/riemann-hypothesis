module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHSt
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.CountZMoll

@[expose] public section

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDensLs
section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDensLsA
open Complex Filter Topology

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.EtaPartialSums

open Formalism.FX.LFunctionPartialSum

variable (f : ℕ → ℂ)

def Ap (n : ℕ) : ℂ := ∑ k ∈ Finset.Icc 1 n, f k

def dterm (s : ℂ) (n : ℕ) : ℂ := Ap f n * ((n : ℂ) ^ (-s) - ((n : ℂ) + 1) ^ (-s))

def G (s : ℂ) : ℂ := ∑' n, dterm f s n

lemma Ap_zero : Ap f 0 = 0 := by
  unfold Ap
  exact Finset.sum_eq_zero (fun i hi => by rw [Finset.mem_Icc] at hi; omega)

lemma Ap_succ (n : ℕ) : Ap f (n + 1) = Ap f n + f (n + 1) := by
  unfold Ap
  exact Finset.sum_Icc_succ_top (by omega) f

lemma dterm_zero (s : ℂ) : dterm f s 0 = 0 := by
  rw [dterm, Ap_zero, zero_mul]

private lemma natCast_cpow_neg_sub_succ_eq_mul_integral (s : ℂ) (hs : 0 < s.re) (n : ℕ) (hn : 1 ≤ n) :
    (n : ℂ) ^ (-s) - ((n : ℂ) + 1) ^ (-s) = s * ∫ t in (n : ℝ)..((n : ℝ) + 1), (t : ℂ) ^ (-s - 1) := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at hs
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have h0 : (0 : ℝ) ∉ Set.uIcc (n : ℝ) ((n : ℝ) + 1) := by
    rw [Set.uIcc_of_le (by linarith)]
    intro h
    linarith [h.1]
  have hne : -s - 1 ≠ -1 := by
    intro h
    apply hs0
    linear_combination -h
  rw [integral_cpow (Or.inr ⟨hne, h0⟩)]
  have e : -s - 1 + 1 = -s := by ring
  rw [e]
  push_cast
  field_simp
  ring

private lemma norm_cpow_neg_sub_succ_le_norm_mul_rpow (s : ℂ) (hs : 0 < s.re) (n : ℕ) (hn : 1 ≤ n) :
    ‖(n : ℂ) ^ (-s) - ((n : ℂ) + 1) ^ (-s)‖ ≤ ‖s‖ * (n : ℝ) ^ (-s.re - 1) := by
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  rw [natCast_cpow_neg_sub_succ_eq_mul_integral s hs n hn, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine le_trans (intervalIntegral.norm_integral_le_of_norm_le_const
    (C := (n : ℝ) ^ (-s.re - 1)) ?_) (le_of_eq ?_)
  · intro t ht
    rw [Set.uIoc_of_le (by linarith)] at ht
    have htp : 0 < t := lt_trans hnpos ht.1
    show ‖(t : ℂ) ^ (-s - 1)‖ ≤ (n : ℝ) ^ (-s.re - 1)
    rw [Complex.norm_cpow_eq_rpow_re_of_pos htp]
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
    exact Real.rpow_le_rpow_of_nonpos hnpos (le_of_lt ht.1) (by linarith)
  · rw [add_sub_cancel_left, abs_one, mul_one]

lemma norm_dterm_le {B : ℝ} (hB : ∀ M, ‖Ap f M‖ ≤ B) {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    ‖dterm f s n‖ ≤ B * (‖s‖ * (n : ℝ) ^ (-s.re - 1)) := by
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [dterm_zero, norm_zero]
    exact mul_nonneg hB0 (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  · rw [dterm, norm_mul]
    exact mul_le_mul (hB n) (norm_cpow_neg_sub_succ_le_norm_mul_rpow s hs n (by omega)) (norm_nonneg _) hB0

private lemma norm_cpow_neg_sub_succ_le_telescoping (s : ℂ) (hs : 0 < s.re) (n : ℕ) (hn : 1 ≤ n) :
    ‖(n : ℂ) ^ (-s) - ((n : ℂ) + 1) ^ (-s)‖ ≤
      ‖s‖ / s.re * ((n : ℝ) ^ (-s.re) - ((n : ℝ) + 1) ^ (-s.re)) := by
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have h0 : (0 : ℝ) ∉ Set.uIcc (n : ℝ) ((n : ℝ) + 1) := by
    rw [Set.uIcc_of_le (by linarith)]
    intro h
    linarith [h.1]
  rw [natCast_cpow_neg_sub_succ_eq_mul_integral s hs n hn, norm_mul]
  have hI : ‖∫ t in (n : ℝ)..((n : ℝ) + 1), (t : ℂ) ^ (-s - 1)‖ ≤
      ∫ t in (n : ℝ)..((n : ℝ) + 1), t ^ (-s.re - 1) := by
    refine le_trans (intervalIntegral.norm_integral_le_integral_norm (by linarith)) (le_of_eq ?_)
    refine intervalIntegral.integral_congr ?_
    intro t ht
    rw [Set.uIcc_of_le (by linarith)] at ht
    have htp : 0 < t := lt_of_lt_of_le hnpos ht.1
    show ‖(t : ℂ) ^ (-s - 1)‖ = t ^ (-s.re - 1)
    rw [Complex.norm_cpow_eq_rpow_re_of_pos htp]
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
  have hval : ∫ t in (n : ℝ)..((n : ℝ) + 1), t ^ (-s.re - 1) =
      ((n : ℝ) ^ (-s.re) - ((n : ℝ) + 1) ^ (-s.re)) / s.re := by
    rw [integral_rpow (Or.inr ⟨(by linarith : -s.re - 1 < -1).ne, h0⟩)]
    have e : -s.re - 1 + 1 = -s.re := by ring
    rw [e, div_neg]
    ring
  calc ‖s‖ * ‖∫ t in (n : ℝ)..((n : ℝ) + 1), (t : ℂ) ^ (-s - 1)‖
        ≤ ‖s‖ * (((n : ℝ) ^ (-s.re) - ((n : ℝ) + 1) ^ (-s.re)) / s.re) := by
          rw [← hval]
          exact mul_le_mul_of_nonneg_left hI (norm_nonneg _)
    _ = ‖s‖ / s.re * ((n : ℝ) ^ (-s.re) - ((n : ℝ) + 1) ^ (-s.re)) := by ring

lemma norm_dterm_le' {B : ℝ} (hB : ∀ M, ‖Ap f M‖ ≤ B) {s : ℂ} (hs : 0 < s.re) {n : ℕ}
    (hn : 1 ≤ n) :
    ‖dterm f s n‖ ≤ B * (‖s‖ / s.re * ((n : ℝ) ^ (-s.re) - ((n : ℝ) + 1) ^ (-s.re))) := by
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  rw [dterm, norm_mul]
  exact mul_le_mul (hB n) (norm_cpow_neg_sub_succ_le_telescoping s hs n hn) (norm_nonneg _) hB0

lemma summable_norm_dterm {B : ℝ} (hB : ∀ M, ‖Ap f M‖ ≤ B) {s : ℂ} (hs : 0 < s.re) :
    Summable (fun n => ‖dterm f s n‖) := by
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => norm_dterm_le f hB hs n) ?_
  exact ((Real.summable_nat_rpow.2 (by linarith)).mul_left ‖s‖).mul_left B

lemma summable_dterm {B : ℝ} (hB : ∀ M, ‖Ap f M‖ ≤ B) {s : ℂ} (hs : 0 < s.re) :
    Summable (dterm f s) := (summable_norm_dterm f hB hs).of_norm

lemma partial_identity (s : ℂ) (M : ℕ) :
    ∑ n ∈ Finset.range (M + 1), dterm f s n + Ap f M * ((M : ℂ) + 1) ^ (-s) =
      ∑ n ∈ Finset.Icc 1 M, f n * (n : ℂ) ^ (-s) := by
  induction M with
  | zero =>
    rw [Finset.sum_range_succ, Finset.sum_range_zero, dterm_zero, Ap_zero, zero_mul, add_zero, add_zero]
    exact (Finset.sum_eq_zero (fun i hi => by rw [Finset.mem_Icc] at hi; omega)).symm
  | succ M ih =>
    rw [Finset.sum_range_succ, Finset.sum_Icc_succ_top (by omega : 1 ≤ M + 1), ← ih, dterm, Ap_succ]
    push_cast
    ring

lemma G_differentiableOn {B : ℝ} (hB : ∀ M, ‖Ap f M‖ ≤ B) :
    DifferentiableOn ℂ (G f) {s : ℂ | 0 < s.re} := by
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  intro s0 hs0
  have hσ : 0 < s0.re := hs0
  have hU : IsOpen ({w : ℂ | s0.re / 2 < w.re} ∩ Metric.ball s0 1) :=
    (isOpen_lt continuous_const Complex.continuous_re).inter Metric.isOpen_ball
  have hmem : s0 ∈ ({w : ℂ | s0.re / 2 < w.re} ∩ Metric.ball s0 1) :=
    ⟨show s0.re / 2 < s0.re by linarith, Metric.mem_ball_self one_pos⟩
  have hD : DifferentiableOn ℂ (fun w => ∑' n, dterm f w n)
      ({w : ℂ | s0.re / 2 < w.re} ∩ Metric.ball s0 1) := by
    refine Complex.differentiableOn_tsum_of_summable_norm (F := fun n w => dterm f w n)
      (u := fun n : ℕ => B * ((‖s0‖ + 1) * (n : ℝ) ^ (-(s0.re / 2) - 1))) ?_ ?_ hU ?_
    · exact ((Real.summable_nat_rpow.2 (by linarith)).mul_left _).mul_left _
    · intro n w hw
      have h1 : s0.re / 2 < w.re := hw.1
      have hw0 : -w ≠ 0 := by
        intro h
        rw [neg_eq_zero] at h
        rw [h, Complex.zero_re] at h1
        linarith
      refine DifferentiableAt.differentiableWithinAt ?_
      show DifferentiableAt ℂ (fun w => Ap f n * ((n : ℂ) ^ (-w) - ((n : ℂ) + 1) ^ (-w))) w
      have hneg : DifferentiableAt ℂ (fun w : ℂ => -w) w := differentiableAt_id.neg
      have ha : DifferentiableAt ℂ (fun w : ℂ => (n : ℂ) ^ (-w)) w := hneg.const_cpow (Or.inr hw0)
      have hb : DifferentiableAt ℂ (fun w : ℂ => ((n : ℂ) + 1) ^ (-w)) w :=
        hneg.const_cpow (Or.inr hw0)
      exact (ha.sub hb).const_mul (Ap f n)
    · intro n w hw
      have h1 : s0.re / 2 < w.re := hw.1
      have h2 : dist w s0 < 1 := hw.2
      have hwre : 0 < w.re := by linarith
      show ‖dterm f w n‖ ≤ B * ((‖s0‖ + 1) * (n : ℝ) ^ (-(s0.re / 2) - 1))
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · rw [dterm_zero, norm_zero]
        exact mul_nonneg hB0 (mul_nonneg (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      · refine le_trans (norm_dterm_le f hB hwre n) (mul_le_mul_of_nonneg_left ?_ hB0)
        have h3 : ‖w - s0‖ < 1 := by rwa [dist_eq_norm] at h2
        have h4 := norm_sub_norm_le w s0
        have hw1 : ‖w‖ ≤ ‖s0‖ + 1 := by linarith
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
        have hpow : (n : ℝ) ^ (-w.re - 1) ≤ (n : ℝ) ^ (-(s0.re / 2) - 1) :=
          Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
        exact mul_le_mul hw1 hpow (Real.rpow_nonneg (Nat.cast_nonneg _) _) (by positivity)
  exact (hD.differentiableAt (hU.mem_nhds hmem)).differentiableWithinAt

private lemma norm_Ap_mul_succ_cpow_neg_le {B : ℝ} (hB : ∀ M, ‖Ap f M‖ ≤ B) (s : ℂ) (M : ℕ) :
    ‖Ap f M * ((M : ℂ) + 1) ^ (-s)‖ ≤ B * ((M : ℝ) + 1) ^ (-s.re) := by
  have e : ((M : ℂ) + 1) = (((M : ℝ) + 1 : ℝ) : ℂ) := by simp
  rw [norm_mul, e, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
  simp only [Complex.neg_re]
  exact mul_le_mul_of_nonneg_right (hB M) (Real.rpow_nonneg (by positivity) _)

lemma partial_tendsto_G {B : ℝ} (hB : ∀ M, ‖Ap f M‖ ≤ B) {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun M : ℕ => ∑ n ∈ Finset.Icc 1 M, f n * (n : ℂ) ^ (-s)) atTop (𝓝 (G f s)) := by
  have e : (fun M : ℕ => ∑ n ∈ Finset.Icc 1 M, f n * (n : ℂ) ^ (-s)) =
      fun M => ∑ n ∈ Finset.range (M + 1), dterm f s n + Ap f M * ((M : ℂ) + 1) ^ (-s) :=
    funext fun M => (partial_identity f s M).symm
  rw [e, ← add_zero (G f s)]
  refine Filter.Tendsto.add ?_ ?_
  · exact ((summable_dterm f hB hs).hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
  · have h3 : Tendsto (fun M : ℕ => (M : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    have h4 := ((tendsto_rpow_neg_atTop hs).comp h3).const_mul B
    rw [mul_zero] at h4
    exact squeeze_zero_norm (norm_Ap_mul_succ_cpow_neg_le f hB s) h4

private lemma sum_range_rpow_neg_telescope (σ : ℝ) (N M : ℕ) :
    ∑ i ∈ Finset.range M, ((((i + (N + 1) : ℕ) : ℝ)) ^ (-σ) - ((((i + (N + 1) : ℕ) : ℝ)) + 1) ^ (-σ)) =
      ((N : ℝ) + 1) ^ (-σ) - (((M + N + 1 : ℕ) : ℝ)) ^ (-σ) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring_nf

lemma norm_tail_le {B : ℝ} (hB : ∀ M, ‖Ap f M‖ ≤ B) {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    ‖∑' i, dterm f s (i + (N + 1))‖ ≤ B * (‖s‖ / s.re) * ((N : ℝ) + 1) ^ (-s.re) := by
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  have hc : 0 ≤ ‖s‖ / s.re := div_nonneg (norm_nonneg _) hs.le
  have hsum : Summable (fun i => dterm f s (i + (N + 1))) :=
    (summable_nat_add_iff (N + 1)).2 (summable_dterm f hB hs)
  refine le_of_tendsto' (hsum.hasSum.tendsto_sum_nat.norm) (fun M => ?_)
  calc ‖∑ i ∈ Finset.range M, dterm f s (i + (N + 1))‖
        ≤ ∑ i ∈ Finset.range M, ‖dterm f s (i + (N + 1))‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range M, B * (‖s‖ / s.re * ((((i + (N + 1) : ℕ) : ℝ)) ^ (-s.re) -
          ((((i + (N + 1) : ℕ) : ℝ)) + 1) ^ (-s.re))) :=
        Finset.sum_le_sum fun i _ => norm_dterm_le' f hB hs (by omega)
    _ = B * (‖s‖ / s.re) * (((N : ℝ) + 1) ^ (-s.re) - (((M + N + 1 : ℕ) : ℝ)) ^ (-s.re)) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum, sum_range_rpow_neg_telescope]
        ring
    _ ≤ B * (‖s‖ / s.re) * ((N : ℝ) + 1) ^ (-s.re) := by
        have h5 : 0 ≤ (((M + N + 1 : ℕ) : ℝ)) ^ (-s.re) := Real.rpow_nonneg (Nat.cast_nonneg _) _
        have h6 : 0 ≤ B * (‖s‖ / s.re) := mul_nonneg hB0 hc
        nlinarith

lemma norm_G_sub_partial_le {B : ℝ} (hB : ∀ M, ‖Ap f M‖ ≤ B) {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    ‖G f s - ∑ n ∈ Finset.Icc 1 N, f n * (n : ℂ) ^ (-s)‖ ≤
      B * (1 + ‖s‖ / s.re) * ((N : ℝ) + 1) ^ (-s.re) := by
  rw [← partial_identity f s N]
  have hsum := summable_dterm f hB hs
  have hG : G f s = ∑ n ∈ Finset.range (N + 1), dterm f s n + ∑' i, dterm f s (i + (N + 1)) :=
    (hsum.sum_add_tsum_nat_add (N + 1)).symm
  rw [hG]
  have e : ∑ n ∈ Finset.range (N + 1), dterm f s n + ∑' i, dterm f s (i + (N + 1)) -
      (∑ n ∈ Finset.range (N + 1), dterm f s n + Ap f N * ((N : ℂ) + 1) ^ (-s)) =
      ∑' i, dterm f s (i + (N + 1)) - Ap f N * ((N : ℂ) + 1) ^ (-s) := by ring
  rw [e]
  have h1 := norm_tail_le f hB hs N
  have h2 : ‖Ap f N * ((N : ℂ) + 1) ^ (-s)‖ ≤ B * ((N : ℝ) + 1) ^ (-s.re) := by
    rw [norm_mul, natCast_add_one_eq, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    simp only [Complex.neg_re]
    exact mul_le_mul_of_nonneg_right (hB N) (Real.rpow_nonneg (by positivity) _)
  calc ‖∑' i, dterm f s (i + (N + 1)) - Ap f N * ((N : ℂ) + 1) ^ (-s)‖
      ≤ ‖∑' i, dterm f s (i + (N + 1))‖ + ‖Ap f N * ((N : ℂ) + 1) ^ (-s)‖ := norm_sub_le _ _
    _ ≤ B * (‖s‖ / s.re) * ((N : ℝ) + 1) ^ (-s.re) + B * ((N : ℝ) + 1) ^ (-s.re) := add_le_add h1 h2
    _ = B * (1 + ‖s‖ / s.re) * ((N : ℝ) + 1) ^ (-s.re) := by ring

end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.EtaPartialSums
end
end

open Complex Filter Topology

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.EtaPartialSums

def Φe (j : ZMod 2) : ℂ := if j = 0 then -1 else 1

def eps (n : ℕ) : ℂ := Φe (n : ZMod 2)

lemma Φe_sum : ∑ j, Φe j = 0 := by
  show ∑ j : Fin 2, (if j = 0 then (-1 : ℂ) else 1) = 0
  simp [Fin.sum_univ_two]

lemma eps_eq (n : ℕ) : eps n = if n % 2 = 0 then -1 else 1 := by
  unfold eps Φe
  have h : ((n : ZMod 2) = 0) ↔ n % 2 = 0 := by rw [ZMod.natCast_eq_zero_iff]; omega
  by_cases hn : n % 2 = 0
  · rw [if_pos (h.mpr hn), if_pos hn]
  · rw [if_neg (fun h' => hn (h.mp h')), if_neg hn]

lemma Ap_eps (n : ℕ) : Ap eps n = ((n % 2 : ℕ) : ℂ) := by
  induction n with
  | zero => simp [Ap_zero]
  | succ n ih =>
    rw [Ap_succ, ih, eps_eq]
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · have h' : (n + 1) % 2 = 1 := by omega
      rw [h, h']
      norm_num
    · have h' : (n + 1) % 2 = 0 := by omega
      rw [h, h']
      norm_num

lemma norm_Ap_eps_le (M : ℕ) : ‖Ap eps M‖ ≤ 1 := by
  rw [Ap_eps]
  rcases Nat.mod_two_eq_zero_or_one M with h | h <;> rw [h] <;> simp

lemma LFunction_eq_G_of_one_lt {s : ℂ} (hs : 1 < s.re) : ZMod.LFunction Φe s = G eps s := by
  rw [ZMod.LFunction_eq_LSeries Φe hs]
  have h1 : Tendsto (fun M : ℕ => ∑ n ∈ Finset.Icc 1 M, eps n * (n : ℂ) ^ (-s)) atTop
      (𝓝 (LSeries (fun n => Φe n) s)) := by
    have hsum := (ZMod.LSeriesSummable_of_one_lt_re Φe hs).hasSum.tendsto_sum_nat
    have h2 := hsum.comp (tendsto_add_atTop_nat 1)
    refine h2.congr (fun M => ?_)
    simp only [Function.comp_apply]
    rw [← Formalism.FX.LFunctionPartialSum.sum_Icc_eq_sum_range _ (LSeries.term_zero _ _)]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    have hn0 : n ≠ 0 := by
      simp only [Finset.mem_Icc] at hn
      omega
    rw [LSeries.term_of_ne_zero hn0, Complex.cpow_neg, div_eq_mul_inv]
    rfl
  exact tendsto_nhds_unique h1 (partial_tendsto_G eps norm_Ap_eps_le (by linarith))

lemma LFunction_eq_G {s : ℂ} (hs : 0 < s.re) : ZMod.LFunction Φe s = G eps s := by
  have hU : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hconn : IsPreconnected {s : ℂ | 0 < s.re} := (convex_halfSpace_re_gt 0).isPreconnected
  have hf : AnalyticOnNhd ℂ (ZMod.LFunction Φe) {s : ℂ | 0 < s.re} :=
    (ZMod.differentiable_LFunction_of_sum_zero Φe_sum).differentiableOn.analyticOnNhd hU
  have hg : AnalyticOnNhd ℂ (G eps) {s : ℂ | 0 < s.re} :=
    (G_differentiableOn eps norm_Ap_eps_le).analyticOnNhd hU
  have h2 : (2 : ℂ) ∈ {s : ℂ | 0 < s.re} := by simp
  have hev : ZMod.LFunction Φe =ᶠ[𝓝 (2 : ℂ)] G eps := by
    have : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [this] with s hs
    exact LFunction_eq_G_of_one_lt hs
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hconn h2 hev hs

lemma two_cpow_one_sub (s : ℂ) : (2 : ℂ) ^ (1 - s) = 2 * (2 : ℂ) ^ (-s) := by
  rw [sub_eq_add_neg, Complex.cpow_add _ _ two_ne_zero, Complex.cpow_one]

lemma Φe_eq (j : ZMod 2) :
    Φe j = (1 : DirichletCharacter ℂ 2) j - (if j = 0 then 1 else 0) := by
  by_cases hj : j = 0
  · subst hj
    rw [MulChar.map_nonunit _ not_isUnit_zero]
    simp [Φe]
  · rw [MulChar.one_apply (isUnit_iff_ne_zero.mpr hj)]
    simp [Φe, hj]

lemma LFunction_Φe {s : ℂ} (hs : s ≠ 1) :
    ZMod.LFunction Φe s = (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s := by
  have h2 : ZMod.LFunction Φe s =
      DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 2) s - (2 : ℂ) ^ (-s) * riemannZeta s := by
    rw [DirichletCharacter.LFunction, ZMod.LFunction, ZMod.LFunction]
    simp_rw [Φe_eq, sub_mul, Finset.sum_sub_distrib, mul_sub, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, map_zero, HurwitzZeta.hurwitzZeta_zero]
    push_cast
    ring
  have h3 := DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta (N := 2) hs
  rw [DirichletCharacter.LFunctionTrivChar, Nat.Prime.primeFactors Nat.prime_two,
    Finset.prod_singleton] at h3
  rw [h2, h3, two_cpow_one_sub]
  push_cast
  ring

lemma alt_sum (s : ℂ) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 (2 * N), (n : ℂ) ^ (-s) - (2 : ℂ) ^ (1 - s) * ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s) =
      ∑ n ∈ Finset.Icc 1 (2 * N), eps n * (n : ℂ) ^ (-s) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hA : ∀ g : ℕ → ℂ, (Finset.Icc 1 (2 * (N + 1))).sum g =
        (Finset.Icc 1 (2 * N)).sum g + g (2 * N + 1) + g (2 * N + 2) := by
      intro g
      rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, Finset.sum_Icc_succ_top (by omega),
        Finset.sum_Icc_succ_top (by omega)]
    have hB : ∀ g : ℕ → ℂ, (Finset.Icc 1 (N + 1)).sum g = (Finset.Icc 1 N).sum g + g (N + 1) :=
      fun g => Finset.sum_Icc_succ_top (by omega) _
    rw [hA (fun n => (n : ℂ) ^ (-s)), hA (fun n => eps n * (n : ℂ) ^ (-s)),
      hB (fun n => (n : ℂ) ^ (-s))]
    have e1 : eps (2 * N + 1) = 1 := by rw [eps_eq, if_neg (by omega)]
    have e2 : eps (2 * N + 2) = -1 := by rw [eps_eq, if_pos (by omega)]
    have hb : ((2 * N + 2 : ℕ) : ℂ) ^ (-s) = (2 : ℂ) ^ (-s) * ((N + 1 : ℕ) : ℂ) ^ (-s) := by
      have h := natCast_mul_natCast_cpow 2 (N + 1) (-s)
      rw [show ((2 * N + 2 : ℕ) : ℂ) = ((2 : ℕ) : ℂ) * ((N + 1 : ℕ) : ℂ) by push_cast; ring, h]
      norm_num
    rw [e1, e2, hb]
    rw [two_cpow_one_sub] at ih ⊢
    linear_combination ih

end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.EtaPartialSums

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens

open Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD Formalism.ZeroFreeDirichlet EtaPartialSums

theorem eta_partial_sums : EtaPartial := by
  intro s hs hs1 N hN
  have hG : (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s = EtaPartialSums.G eps s := by
    rw [← LFunction_Φe hs1, LFunction_eq_G hs]
  rw [hG, alt_sum]
  refine (norm_G_sub_partial_le eps norm_Ap_eps_le hs (2 * N)).trans ?_
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have h3 : (((2 * N : ℕ) : ℝ) + 1) ^ (-s.re) ≤ (N : ℝ) ^ (-s.re) := by
    apply Real.rpow_le_rpow_of_nonpos hNpos _ (by linarith)
    push_cast
    linarith
  have hq : 0 ≤ 1 + ‖s‖ / s.re := by
    have := div_nonneg (norm_nonneg s) hs.le
    linarith
  have h4 : 0 ≤ (N : ℝ) ^ (-s.re) := Real.rpow_nonneg hNpos.le _
  calc 1 * (1 + ‖s‖ / s.re) * (((2 * N : ℕ) : ℝ) + 1) ^ (-s.re)
      ≤ 1 * (1 + ‖s‖ / s.re) * (N : ℝ) ^ (-s.re) :=
        mul_le_mul_of_nonneg_left h3 (by linarith)
    _ ≤ 4 * (1 + ‖s‖ / s.re) * (N : ℝ) ^ (-s.re) := by
        have := mul_nonneg hq h4
        nlinarith

theorem principal_zeta_bound : PrincipalZeta := by
  intro M _ s hs hz
  have hs1 : s ≠ 1 := by
    rcases hz.1 with h | h
    · exact absurd rfl h
    · exact h
  have h := hz.2
  rw [← DirichletCharacter.LFunctionTrivChar, DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hs1] at h
  rcases mul_eq_zero.mp h with h | h
  · exfalso
    rw [Finset.prod_eq_zero_iff] at h
    obtain ⟨p, hp, hp0⟩ := h
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hlt : ‖(p : ℂ) ^ (-s)‖ < 1 := by
      rw [Complex.norm_natCast_cpow_of_pos hpp.pos]
      simp only [Complex.neg_re]
      exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hpp.one_lt) (by linarith)
    have : (p : ℂ) ^ (-s) = 1 := by linear_combination -hp0
    rw [this, norm_one] at hlt
    exact lt_irrefl _ hlt
  · exact h

end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
end
end

open Complex Finset

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens

open Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD Formalism.ZeroFreeDirichlet

lemma one_char_apply (x : ZMod 1) : (1 : DirichletCharacter ℂ 1) x = 1 := by
  rw [Subsingleton.elim x 1, map_one]

lemma block_pigeon (Y J' N' : ℕ) (f : ℕ → ℂ) (ρ : ℂ) (hN : N' = 2 ^ J') (hJ : 0 < J') (θ : ℝ)
    (h : θ ≤ ‖∑ n ∈ Ioc Y (Y * N'), mco Y N' n * f n * (n : ℂ) ^ (-ρ)‖) :
    ∃ j ∈ range J', θ / (J' : ℝ) ≤ ‖blkD Y N' (Y * 2 ^ j) f ρ‖ := by
  by_contra hcon
  push Not at hcon
  have hsplit : ∑ n ∈ Ioc Y (Y * N'), mco Y N' n * f n * (n : ℂ) ^ (-ρ) =
      ∑ j ∈ range J', blkD Y N' (Y * 2 ^ j) f ρ := by
    have h0 := sum_blocks (fun n => mco Y N' n * f n * (n : ℂ) ^ (-ρ)) Y J'
    rw [← hN] at h0
    exact h0
  have hJpos : (0 : ℝ) < J' := by exact_mod_cast hJ
  have hlt : ‖∑ n ∈ Ioc Y (Y * N'), mco Y N' n * f n * (n : ℂ) ^ (-ρ)‖ < θ := by
    rw [hsplit]
    refine (norm_sum_le _ _).trans_lt ?_
    calc ∑ j ∈ range J', ‖blkD Y N' (Y * 2 ^ j) f ρ‖
        < ∑ j ∈ range J', θ / (J' : ℝ) := sum_lt_sum_of_nonempty (nonempty_range_iff.mpr hJ.ne') hcon
      _ = θ := by rw [sum_const, card_range, nsmul_eq_mul]; field_simp
  linarith

lemma two_cpow_norm (ρ : ℂ) : ‖(2 : ℂ) ^ (1 - ρ)‖ = (2 : ℝ) ^ (1 - ρ.re) := by
  have h := Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2) (1 - ρ)
  simpa using h

lemma one_sub_two_cpow_lower (ρ : ℂ) (hρ : ρ.re ≤ 1) : (1 - ρ.re) / 2 ≤ ‖1 - (2 : ℂ) ^ (1 - ρ)‖ := by
  have h1 : ‖(2 : ℂ) ^ (1 - ρ)‖ - ‖(1 : ℂ)‖ ≤ ‖(2 : ℂ) ^ (1 - ρ) - 1‖ := norm_sub_norm_le _ _
  rw [norm_sub_rev, two_cpow_norm, norm_one] at h1
  have h2 : Real.log 2 * (1 - ρ.re) + 1 ≤ (2 : ℝ) ^ (1 - ρ.re) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    exact Real.add_one_le_exp _
  have h3 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have h4 : (1 / 2 : ℝ) * (1 - ρ.re) ≤ Real.log 2 * (1 - ρ.re) :=
    mul_le_mul_of_nonneg_right h3 (by linarith)
  linarith

lemma two_cpow_norm_le (ρ : ℂ) (hρ : 0 ≤ ρ.re) : ‖(2 : ℂ) ^ (1 - ρ)‖ ≤ 2 := by
  rw [two_cpow_norm]
  calc (2 : ℝ) ^ (1 - ρ.re) ≤ (2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = 2 := Real.rpow_one 2

attribute [local irreducible] qd pYd pJd pNd in
theorem zero_detection_first : Detect0 := by
  obtain ⟨c₀, hc₀, hZ⟩ := zFRDirichlet
  refine ⟨c₀ / 24, by positivity, ⌈96 / c₀⌉₊, ?_⟩
  intro M _ T hT hM hq ρ hρ hρim hL
  obtain ⟨X, hX⟩ : ∃ X : ℕ, qd M T = X := ⟨_, rfl⟩
  rw [hX] at hq ⊢
  have hMT : (M : ℝ) * T ≤ X := by rw [← hX]; unfold qd; exact Nat.le_ceil _
  have hM3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hX6 : (6 : ℝ) ≤ X := by nlinarith
  have hXpos : (0 : ℝ) < X := by linarith
  have hX1 : 1 ≤ X := by exact_mod_cast (show (1 : ℝ) ≤ X by linarith)
  have hTX : T ≤ X := by nlinarith
  have hre0 : 0 < ρ.re := by linarith
  have hNX : X ^ 8 ≤ pNd M T := by
    have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) X
    unfold pNd pJd
    rw [hX, mul_comm 8, pow_mul]
    exact Nat.pow_le_pow_left h.le 8
  have hY : pYd M T = X ^ 3 := by unfold pYd; rw [hX]
  have hYN : pYd M T ≤ pNd M T := by
    rw [hY]; exact le_trans (Nat.pow_le_pow_right hX1 (by norm_num)) hNX
  have hY1 : 1 ≤ pYd M T := by rw [hY]; exact Nat.one_le_pow _ _ (by omega)
  have hN1 : 1 ≤ pNd M T := le_trans hY1 hYN
  have hJ8 : 8 ≤ pJd M T := by unfold pJd; omega
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)

  have hnot : ¬ InRegion c₀ M ρ := fun h => (hZ M 1 ρ h hL).2.1 rfl
  unfold InRegion at hnot
  push Not at hnot
  have harg1 : (1 : ℝ) < (M : ℝ) * (|ρ.im| + 2) := by
    have := abs_nonneg ρ.im
    nlinarith
  have harg2 : (M : ℝ) * (|ρ.im| + 2) ≤ (X : ℝ) ^ 2 := by
    have h1 : (M : ℝ) * (|ρ.im| + 2) ≤ (M : ℝ) * (T + 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    nlinarith
  have hlog2 : Real.log ((M : ℝ) * (|ρ.im| + 2)) ≤ 2 * Real.log X := by
    have h := Real.log_le_log (by linarith) harg2
    rwa [Real.log_pow, Nat.cast_ofNat] at h
  have hbeta : c₀ / (2 * Real.log X) < 1 - ρ.re := by
    have h1 : c₀ / (2 * Real.log X) ≤ c₀ / Real.log ((M : ℝ) * (|ρ.im| + 2)) :=
      div_le_div_of_nonneg_left hc₀.le (Real.log_pos harg1) hlog2
    linarith
  have hbeta0 : ρ.re ≤ 1 := by
    have : 0 < c₀ / (2 * Real.log X) := by positivity
    linarith

  have hζ := principal_zeta_bound M ρ hre0 hL
  have hρ1 : ρ ≠ 1 := hL.1.resolve_left (fun h => h rfl)
  have hE := eta_partial_sums ρ hre0 hρ1 (pNd M T) hN1
  rw [hζ, mul_zero, zero_sub, norm_neg] at hE

  have hP : ∀ K : ℕ, ∑ n ∈ Icc 1 K, (1 : DirichletCharacter ℂ 1) (n : ZMod 1) * (n : ℂ) ^ (-ρ) =
      ∑ n ∈ Icc 1 K, (n : ℂ) ^ (-ρ) :=
    fun K => sum_congr rfl (fun n _ => by rw [one_char_apply, one_mul])
  have hMI1 := mollifier_identity 1 (1 : DirichletCharacter ℂ 1) ρ (pYd M T) (pNd M T) (pYd M T * pNd M T)
    hY1 hYN le_rfl
  have hMI2 := mollifier_identity 1 (1 : DirichletCharacter ℂ 1) ρ (pYd M T) (2 * pNd M T)
    (pYd M T * (2 * pNd M T)) hY1 (by omega) le_rfl
  rw [hP] at hMI1 hMI2
  have hMo := mollM_norm_le (1 : DirichletCharacter ℂ 1) ρ hre0.le (pYd M T)
  have hz2 := two_cpow_norm_le ρ hre0.le
  have hzl := one_sub_two_cpow_lower ρ hbeta0
  set z : ℂ := (2 : ℂ) ^ (1 - ρ) with hz
  set P1 := ∑ n ∈ Icc 1 (pNd M T), (n : ℂ) ^ (-ρ) with hP1
  set P2 := ∑ n ∈ Icc 1 (2 * pNd M T), (n : ℂ) ^ (-ρ) with hP2
  set Mo := ∑ d ∈ Icc 1 (pYd M T), (((ArithmeticFunction.moebius d : ℤ)) : ℂ) *
    (1 : DirichletCharacter ℂ 1) (d : ZMod 1) * (d : ℂ) ^ (-ρ) with hMdef
  set D1 := ∑ n ∈ Ioc (pYd M T) (pYd M T * pNd M T), mco (pYd M T) (pNd M T) n *
    (1 : DirichletCharacter ℂ 1) (n : ZMod 1) * (n : ℂ) ^ (-ρ) with hD1
  set D2 := ∑ n ∈ Ioc (pYd M T) (pYd M T * (2 * pNd M T)), mco (pYd M T) (2 * pNd M T) n *
    (1 : DirichletCharacter ℂ 1) (n : ZMod 1) * (n : ℂ) ^ (-ρ) with hD2
  have hEY : ‖P2 - z * P1‖ * (pYd M T : ℝ) ≤ 12 / (X : ℝ) ^ 2 := by
    have hNpos : (0 : ℝ) < pNd M T := by exact_mod_cast hN1
    have hrho : 1 + ‖ρ‖ / ρ.re ≤ 3 * T := by
      have h1 : ‖ρ‖ ≤ ρ.re + T := by
        refine (Complex.norm_le_abs_re_add_abs_im ρ).trans ?_
        rw [abs_of_pos hre0]; linarith
      have h2 : ‖ρ‖ / ρ.re ≤ 1 + T / ρ.re := by
        rw [div_le_iff₀ hre0, add_mul, one_mul, div_mul_cancel₀ _ hre0.ne']; linarith
      have h3 : T / ρ.re ≤ 4 / 3 * T := by
        rw [div_le_iff₀ hre0]; nlinarith
      linarith
    have hpow : ((pNd M T : ℕ) : ℝ) ^ (-ρ.re) ≤ ((pNd M T : ℕ) : ℝ) ^ (-(3 / 4 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1) (by linarith)
    have hN8 : (X : ℝ) ^ (8 : ℕ) ≤ (pNd M T : ℝ) := by exact_mod_cast hNX
    have hpow2 : (X : ℝ) ^ (6 : ℕ) ≤ ((pNd M T : ℕ) : ℝ) ^ (3 / 4 : ℝ) := by
      have e : ((X : ℝ) ^ (8 : ℕ)) ^ (3 / 4 : ℝ) = (X : ℝ) ^ (6 : ℕ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hXpos.le, ← Real.rpow_natCast]
        norm_num
      rw [← e]
      exact Real.rpow_le_rpow (by positivity) hN8 (by norm_num)
    have hinv : ((pNd M T : ℕ) : ℝ) ^ (-(3 / 4 : ℝ)) ≤ 1 / (X : ℝ) ^ (6 : ℕ) := by
      rw [Real.rpow_neg hNpos.le, one_div]
      exact inv_anti₀ (by positivity) hpow2
    have hYr : (pYd M T : ℝ) = (X : ℝ) ^ (3 : ℕ) := by rw [hY, Nat.cast_pow]
    have hc : 4 * (1 + ‖ρ‖ / ρ.re) ≤ 12 * X := by linarith
    have hPle : ‖P2 - z * P1‖ ≤ 12 * X * (1 / (X : ℝ) ^ (6 : ℕ)) := by
      refine hE.trans ?_
      have a3 : ((pNd M T : ℕ) : ℝ) ^ (-ρ.re) ≤ 1 / (X : ℝ) ^ (6 : ℕ) := hpow.trans hinv
      calc 4 * (1 + ‖ρ‖ / ρ.re) * ((pNd M T : ℕ) : ℝ) ^ (-ρ.re)
          ≤ 12 * X * ((pNd M T : ℕ) : ℝ) ^ (-ρ.re) :=
            mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        _ ≤ 12 * X * (1 / (X : ℝ) ^ (6 : ℕ)) := mul_le_mul_of_nonneg_left a3 (by positivity)
    rw [hYr]
    calc ‖P2 - z * P1‖ * (X : ℝ) ^ (3 : ℕ) ≤ 12 * X * (1 / (X : ℝ) ^ (6 : ℕ)) * (X : ℝ) ^ (3 : ℕ) :=
          mul_le_mul_of_nonneg_right hPle (by positivity)
      _ = 12 / (X : ℝ) ^ 2 := by
          have hX0 : (X : ℝ) ≠ 0 := hXpos.ne'
          field_simp
  have hsmall : 12 / (X : ℝ) ^ 2 ≤ c₀ / (8 * Real.log X) := by
    have h96 : 96 ≤ (X : ℝ) * c₀ := by
      have h := Nat.ceil_le.mp hq
      rwa [div_le_iff₀ hc₀] at h
    have hl : Real.log X ≤ X := (Real.log_le_sub_one_of_pos hXpos).trans (by linarith)
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hkey : 1 - z = (P2 - z * P1) * Mo - D2 + z * D1 := by
    linear_combination (-1 : ℂ) * hMI2 + z * hMI1
  have hnorm : ‖1 - z‖ ≤ 12 / (X : ℝ) ^ 2 + ‖D2‖ + 2 * ‖D1‖ := by
    rw [hkey]
    calc ‖(P2 - z * P1) * Mo - D2 + z * D1‖ ≤ ‖(P2 - z * P1) * Mo - D2‖ + ‖z * D1‖ := norm_add_le _ _
      _ ≤ ‖(P2 - z * P1) * Mo‖ + ‖D2‖ + ‖z * D1‖ := by
          have := norm_sub_le ((P2 - z * P1) * Mo) D2
          linarith
      _ ≤ 12 / (X : ℝ) ^ 2 + ‖D2‖ + 2 * ‖D1‖ := by
          rw [norm_mul, norm_mul]
          have a1 : ‖P2 - z * P1‖ * ‖Mo‖ ≤ ‖P2 - z * P1‖ * (pYd M T : ℝ) :=
            mul_le_mul_of_nonneg_left hMo (norm_nonneg _)
          have a2 : ‖z‖ * ‖D1‖ ≤ 2 * ‖D1‖ := mul_le_mul_of_nonneg_right hz2 (norm_nonneg _)
          linarith
  set θ : ℝ := c₀ / (24 * Real.log X) with hθ
  have hθ0 : 0 < θ := by positivity
  have hsum : 3 * θ < ‖D2‖ + 2 * ‖D1‖ := by
    have e1 : c₀ / (2 * Real.log X) / 2 = 6 * θ := by rw [hθ]; field_simp; norm_num
    have e2 : c₀ / (8 * Real.log X) = 3 * θ := by rw [hθ]; field_simp; norm_num
    have : c₀ / (2 * Real.log X) / 2 < (1 - ρ.re) / 2 := by linarith
    linarith
  have hJpos : (0 : ℝ) < pJd M T := by exact_mod_cast (by omega : 0 < pJd M T)
  have hgoal : c₀ / 24 / (((pJd M T : ℝ) + 1) * Real.log X) = θ / ((pJd M T : ℝ) + 1) := by
    rw [hθ]; field_simp
  rw [hgoal]
  by_cases hc2 : θ ≤ ‖D2‖
  · obtain ⟨j, hj, hjb⟩ := block_pigeon (pYd M T) (pJd M T + 1) (2 * pNd M T)
      (fun n => (1 : DirichletCharacter ℂ 1) (n : ZMod 1)) ρ
      (by unfold pNd; rw [pow_succ]; ring) (by omega) θ hc2
    refine ⟨1, by simp, j, hj, ?_⟩
    rw [pow_one]
    push_cast at hjb
    exact hjb
  · have hc1 : θ ≤ ‖D1‖ := by
      push Not at hc2
      linarith
    obtain ⟨j, hj, hjb⟩ := block_pigeon (pYd M T) (pJd M T) (pNd M T)
      (fun n => (1 : DirichletCharacter ℂ 1) (n : ZMod 1)) ρ
      (by unfold pNd; rfl) (by omega) θ hc1
    refine ⟨0, by simp, j, ?_, ?_⟩
    · rw [mem_range] at hj ⊢; omega
    rw [pow_zero, one_mul]
    refine le_trans ?_ hjb
    exact div_le_div_of_nonneg_left hθ0.le hJpos (by linarith)

end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
