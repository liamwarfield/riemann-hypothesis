module

public import Mathlib

@[expose] public section

section -- merged from Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.NormCpowSubLePoint
open Complex Filter Topology

noncomputable section

namespace Formalism.ZF

namespace ComplexPowerDifferenceIntegral

lemma cpow_sub_eq_integral' {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) {s : ℂ} (hs : s ≠ 0) :
    (x : ℂ) ^ (-s) - (y : ℂ) ^ (-s) = s * ∫ t in x..y, (t : ℂ) ^ (-s - 1) := by
  have h0 : (0:ℝ) ∉ Set.uIcc x y := by
    rw [Set.uIcc_of_le hxy]; intro h; exact absurd h.1 (not_le.mpr hx)
  have hr : (-s - 1) ≠ -1 := by intro h; apply hs; linear_combination -h
  have hs' : -s ≠ 0 := neg_ne_zero.mpr hs
  rw [integral_cpow (Or.inr ⟨hr, h0⟩)]
  have e : -s - 1 + 1 = -s := by ring
  rw [e, mul_div_assoc', eq_div_iff hs']
  ring

lemma norm_cpow_sub_le_point {a x : ℝ} (ha : 0 < a) (hax : a ≤ x) (hxa : x ≤ a + 1) {s : ℂ}
    (hs : 0 < s.re) :
    ‖(x : ℂ) ^ (-s) - ((a + 1 : ℝ) : ℂ) ^ (-s)‖ ≤ ‖s‖ * a ^ (-s.re - 1) := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  have hxpos : 0 < x := lt_of_lt_of_le ha hax
  rw [cpow_sub_eq_integral' hxpos hxa hs0, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hC : ∀ t ∈ Set.uIoc x (a + 1), ‖(t : ℂ) ^ (-s - 1)‖ ≤ a ^ (-s.re - 1) := by
    intro t ht
    rw [Set.uIoc_of_le hxa] at ht
    have hta : a ≤ t := le_trans hax ht.1.le
    have ht0 : 0 < t := lt_of_lt_of_le ha hta
    rw [Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    have hre : (-s - 1).re = -s.re - 1 := by simp
    rw [hre]
    exact Real.rpow_le_rpow_of_nonpos ha hta (by linarith)
  calc ‖∫ t in x..(a + 1), (t : ℂ) ^ (-s - 1)‖ ≤ a ^ (-s.re - 1) * |a + 1 - x| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hC
    _ ≤ a ^ (-s.re - 1) * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg ha.le _)
        rw [abs_of_nonneg (by linarith)]; linarith
    _ = a ^ (-s.re - 1) := mul_one _

def eint (s : ℂ) (a : ℝ) : ℂ := ∫ x in a..(a + 1), ((x : ℂ) ^ (-s) - ((a + 1 : ℝ) : ℂ) ^ (-s))

lemma norm_eint_le {a : ℝ} (ha : 0 < a) {s : ℂ} (hs : 0 < s.re) :
    ‖eint s a‖ ≤ ‖s‖ * a ^ (-s.re - 1) := by
  unfold eint
  have hC : ∀ x ∈ Set.uIoc a (a + 1),
      ‖((x : ℂ) ^ (-s) - ((a + 1 : ℝ) : ℂ) ^ (-s))‖ ≤ ‖s‖ * a ^ (-s.re - 1) := by
    intro x hx
    rw [Set.uIoc_of_le (by linarith)] at hx
    exact norm_cpow_sub_le_point ha hx.1.le hx.2 hs
  calc _ ≤ ‖s‖ * a ^ (-s.re - 1) * |a + 1 - a| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hC
    _ = _ := by rw [show a + 1 - a = 1 by ring, abs_one, mul_one]

lemma d_eq {a : ℝ} (ha : 0 < a) (s : ℂ) :
    (a : ℂ) ^ (1 - s) - ((a + 1 : ℝ) : ℂ) ^ (1 - s) - (s - 1) * ((a + 1 : ℝ) : ℂ) ^ (-s) =
      (s - 1) * eint s a := by
  unfold eint
  by_cases hs1 : s = 1
  · subst hs1; simp
  have h0 : (0:ℝ) ∉ Set.uIcc a (a + 1) := by
    rw [Set.uIcc_of_le (by linarith)]; intro h; linarith [h.1]
  have hr : -s ≠ -1 := by intro h; apply hs1; linear_combination -h
  have hint1 : IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ (-s)) MeasureTheory.volume a (a + 1) :=
    intervalIntegral.intervalIntegrable_cpow (Or.inr h0)
  rw [intervalIntegral.integral_sub hint1 intervalIntegrable_const,
    integral_cpow (Or.inr ⟨hr, h0⟩), intervalIntegral.integral_const]
  have e : -s + 1 = 1 - s := by ring
  rw [e]
  have hs' : (1 - s) ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  rw [Complex.real_smul]
  push_cast
  field_simp
  ring

end ComplexPowerDifferenceIntegral

end Formalism.ZF
end
end

open Complex Filter Topology

noncomputable section

namespace Formalism.ZF

namespace ComplexPowerDifferenceIntegral

def dz (s : ℂ) (n : ℕ) : ℂ :=
  (((n : ℝ) + 1 : ℝ) : ℂ) ^ (1 - s) - ((((n : ℝ) + 1) + 1 : ℝ) : ℂ) ^ (1 - s) -
    (s - 1) * ((((n : ℝ) + 1) + 1 : ℝ) : ℂ) ^ (-s)

def Dz (s : ℂ) : ℂ := ∑' n, dz s n

lemma norm_dz_le {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    ‖dz s n‖ ≤ ‖s - 1‖ * ‖s‖ * ((n : ℝ) + 1) ^ (-s.re - 1) := by
  have ha : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [dz, d_eq ha s, norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (norm_eint_le ha hs) (norm_nonneg _)

lemma summable_shift {p : ℝ} (hp : p < -1) : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ p) := by
  have h := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr hp)
  simpa [Nat.cast_add, Nat.cast_one] using h

lemma summable_norm_dz {s : ℂ} (hs : 0 < s.re) : Summable (fun n => ‖dz s n‖) :=
  Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => norm_dz_le hs n)
    ((summable_shift (by linarith : -s.re - 1 < -1)).mul_left _)

lemma Dz_differentiableOn : DifferentiableOn ℂ Dz {s : ℂ | 0 < s.re} := by
  intro s0 hs0
  have hs0' : 0 < s0.re := hs0
  let U : Set ℂ := {s | s0.re / 2 < s.re} ∩ Metric.ball s0 1
  have hU : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter Metric.isOpen_ball
  have hmem : s0 ∈ U := ⟨by show s0.re / 2 < s0.re; linarith, Metric.mem_ball_self one_pos⟩
  have hdiff : ∀ n : ℕ, DifferentiableOn ℂ (fun s => dz s n) U := by
    intro n
    apply Differentiable.differentiableOn
    intro s
    have h1 : (((n : ℝ) + 1 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (by positivity : ((n : ℝ) + 1) ≠ 0)
    have h2 : ((((n : ℝ) + 1) + 1 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (by positivity : ((n : ℝ) + 1 + 1) ≠ 0)
    unfold dz
    refine ((DifferentiableAt.sub ?_ ?_).sub ((differentiableAt_id.sub_const 1).mul ?_))
    · exact ((differentiableAt_const _).sub differentiableAt_id).const_cpow (Or.inl h1)
    · exact ((differentiableAt_const _).sub differentiableAt_id).const_cpow (Or.inl h2)
    · exact differentiableAt_id.neg.const_cpow (Or.inl h2)
  have hbound : ∀ n : ℕ, ∀ s ∈ U,
      ‖dz s n‖ ≤ (‖s0‖ + 1 + 1) * (‖s0‖ + 1) * ((n : ℝ) + 1) ^ (-(s0.re / 2) - 1) := by
    intro n s hs
    have hre : s0.re / 2 < s.re := hs.1
    have hd : ‖s - s0‖ < 1 := by
      have := hs.2
      rwa [Metric.mem_ball, dist_eq_norm] at this
    have hpos : 0 < s.re := by linarith
    have hsR : ‖s‖ ≤ ‖s0‖ + 1 := by
      have := norm_sub_norm_le s s0
      linarith
    have hs1 : ‖s - 1‖ ≤ ‖s0‖ + 1 + 1 := by
      have := norm_sub_le s 1
      rw [norm_one] at this
      linarith
    have hp : ((n : ℝ) + 1) ^ (-s.re - 1) ≤ ((n : ℝ) + 1) ^ (-(s0.re / 2) - 1) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) (by linarith)
    calc ‖dz s n‖ ≤ ‖s - 1‖ * ‖s‖ * ((n : ℝ) + 1) ^ (-s.re - 1) := norm_dz_le hpos n
      _ ≤ (‖s0‖ + 1 + 1) * (‖s0‖ + 1) * ((n : ℝ) + 1) ^ (-(s0.re / 2) - 1) := by gcongr
  have hsum : Summable (fun n : ℕ =>
      (‖s0‖ + 1 + 1) * (‖s0‖ + 1) * ((n : ℝ) + 1) ^ (-(s0.re / 2) - 1)) :=
    (summable_shift (by linarith)).mul_left _
  have hD : DifferentiableOn ℂ (fun s => ∑' n, dz s n) U :=
    differentiableOn_tsum_of_summable_norm hsum hdiff hU hbound
  exact (hD.differentiableAt (hU.mem_nhds hmem)).differentiableWithinAt

end ComplexPowerDifferenceIntegral

end Formalism.ZF
