module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperLiftTraitOfGenericLift

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothLogTwistInequalities
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConcaveTwistEtaInequalities
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConcaveTwistEtaInequalities
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.ConcaveTwist

noncomputable def twShift (T : ℝ) : ℝ := Real.log (1 + Real.exp (-T))

noncomputable def twV (T y : ℝ) : ℝ := y + twShift T - Real.log (1 + Real.exp (y - T))

noncomputable def twP (T y : ℝ) : ℝ := (1 + Real.exp (y - T))⁻¹

noncomputable def twEta (T y : ℝ) : ℝ := 2 + twV T y + Real.log (1 + twV T y)

noncomputable def twEta1 (T y : ℝ) : ℝ := twP T y * (1 + (1 + twV T y)⁻¹)

noncomputable def twEta2 (T y : ℝ) : ℝ :=
  -(twP T y * (1 - twP T y)) * (1 + (1 + twV T y)⁻¹) - twP T y * (twP T y * ((1 + twV T y) ^ 2)⁻¹)

lemma logistic_pos (T y : ℝ) : 0 < twP T y := inv_pos.mpr (by positivity)

lemma twistMap_add_mul (T y : ℝ) : (1 + Real.exp (y - T)) * twP T y = 1 := by
  unfold twP; exact mul_inv_cancel₀ (by positivity)

lemma logistic_lt_one (T y : ℝ) : twP T y < 1 := by
  have h := twistMap_add_mul T y
  have := logistic_pos T y
  nlinarith [Real.exp_pos (y - T)]

lemma twShift_nonneg (T : ℝ) : 0 ≤ twShift T :=
  Real.log_nonneg (by linarith [Real.exp_pos (-T)])

lemma twShift_le_one (T : ℝ) (hT : 0 ≤ T) : twShift T ≤ 1 := by
  have h1 := Real.log_le_sub_one_of_pos (show 0 < 1 + Real.exp (-T) by positivity)
  have h2 : Real.exp (-T) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  unfold twShift; linarith

lemma twV_ge_self (T y : ℝ) (hy : y ≤ 0) : y ≤ twV T y := by
  have : Real.log (1 + Real.exp (y - T)) ≤ twShift T := by
    unfold twShift
    apply Real.log_le_log (by positivity)
    have := Real.exp_le_exp.mpr (show y - T ≤ -T by linarith)
    linarith
  unfold twV; linarith

lemma twV_nonneg (T y : ℝ) (hy : 0 ≤ y) : 0 ≤ twV T y := by
  have he : Real.exp (y - T) = Real.exp y * Real.exp (-T) := by
    rw [← Real.exp_add]; ring_nf
  have h1 : 1 ≤ Real.exp y := Real.one_le_exp hy
  have : Real.log (1 + Real.exp (y - T)) ≤ y + twShift T := by
    have hr : y + twShift T = Real.log (Real.exp y * (1 + Real.exp (-T))) := by
      rw [Real.log_mul (Real.exp_pos y).ne' (by positivity), Real.log_exp]; rfl
    rw [hr]
    apply Real.log_le_log (by positivity)
    rw [he]; nlinarith [Real.exp_pos (-T)]
  unfold twV; linarith

lemma twV_le (T y : ℝ) (hT : 0 ≤ T) : twV T y ≤ T + 1 := by
  have : y - T ≤ Real.log (1 + Real.exp (y - T)) := by
    calc y - T = Real.log (Real.exp (y - T)) := (Real.log_exp _).symm
      _ ≤ _ := Real.log_le_log (Real.exp_pos _) (by linarith)
  have := twShift_le_one T hT
  unfold twV; linarith

lemma twV_le_self (T y : ℝ) (hy : 0 ≤ y) : twV T y ≤ y := by
  have : twShift T ≤ Real.log (1 + Real.exp (y - T)) := by
    unfold twShift
    apply Real.log_le_log (by positivity)
    have := Real.exp_le_exp.mpr (show -T ≤ y - T by linarith)
    linarith
  unfold twV; linarith

lemma twV_gt (T y : ℝ) (hy : -1/4 < y) : -1/4 < twV T y := by
  rcases le_total y 0 with h | h
  · linarith [twV_ge_self T y h]
  · linarith [twV_nonneg T y h]

lemma twV_ge_T_sub_two (T y : ℝ) (h1 : T - 1 ≤ y) (h2 : y ≤ T + 1) : T - 2 ≤ twV T y := by
  set q := Real.exp (y - T) with hq
  have hq0 : 0 < q := Real.exp_pos _
  have he2 : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hqe : 1 ≤ q * Real.exp 1 := by
    rw [hq, ← Real.exp_add]; exact Real.one_le_exp (by linarith)
  have hE : Real.exp (y - T + 2) = q * Real.exp 1 * Real.exp 1 := by
    rw [show y - T + 2 = (y - T) + 1 + 1 by ring, Real.exp_add, Real.exp_add]
  have : Real.log (1 + q) ≤ y - T + 2 := by
    calc Real.log (1 + q) ≤ Real.log (Real.exp (y - T + 2)) := by
          apply Real.log_le_log (by positivity)
          rw [hE]
          nlinarith [mul_nonneg hq0.le (show 0 ≤ Real.exp 1 * Real.exp 1 - Real.exp 1 - 1 by nlinarith)]
      _ = y - T + 2 := Real.log_exp _
  have := twShift_nonneg T
  unfold twV; rw [← hq]; linarith

lemma hasDerivAt_twV (T y : ℝ) : HasDerivAt (twV T) (twP T y) y := by
  have h1 : HasDerivAt (fun y => Real.exp (y - T)) (Real.exp (y - T)) y := by
    simpa using ((hasDerivAt_id y).sub_const T).exp
  have h2 : HasDerivAt (fun y => Real.log (1 + Real.exp (y - T)))
      (Real.exp (y - T) / (1 + Real.exp (y - T))) y := by
    simpa using (h1.const_add 1).log (by positivity)
  have h3 := ((hasDerivAt_id y).add_const (twShift T)).sub h2
  refine h3.congr_deriv ?_
  have : (1 + Real.exp (y - T)) ≠ 0 := by positivity
  unfold twP; field_simp; ring

lemma hasDerivAt_twP (T y : ℝ) : HasDerivAt (twP T) (-(twP T y * (1 - twP T y))) y := by
  have h1 : HasDerivAt (fun y => Real.exp (y - T)) (Real.exp (y - T)) y := by
    simpa using ((hasDerivAt_id y).sub_const T).exp
  have h2 := (h1.const_add 1).inv (show (1 + Real.exp (y - T)) ≠ 0 by positivity)
  refine h2.congr_deriv ?_
  have : (1 + Real.exp (y - T)) ≠ 0 := by positivity
  unfold twP; field_simp; ring

lemma hasDerivAt_twEta (T y : ℝ) (h : 0 < 1 + twV T y) :
    HasDerivAt (twEta T) (twEta1 T y) y := by
  have hv := hasDerivAt_twV T y
  have h2 := (hv.const_add 2).add ((hv.const_add 1).log h.ne')
  refine h2.congr_deriv ?_
  unfold twEta1; ring

lemma hasDerivAt_twEta1 (T y : ℝ) (h : 0 < 1 + twV T y) :
    HasDerivAt (twEta1 T) (twEta2 T y) y := by
  have hv := hasDerivAt_twV T y
  have hp := hasDerivAt_twP T y
  have h2 := hp.mul (((hv.const_add 1).inv h.ne').const_add 1)
  refine h2.congr_deriv ?_
  unfold twEta2; simp only [Pi.inv_apply]; ring

lemma contDiff_twV (T : ℝ) : ContDiff ℝ ∞ (twV T) := by
  have h : ContDiff ℝ ∞ (fun y : ℝ => 1 + Real.exp (y - T)) :=
    contDiff_const.add ((contDiff_id.sub contDiff_const).exp)
  exact (contDiff_id.add contDiff_const).sub (h.log fun y => by positivity)

end GlobalTheory.ConcaveTwist

namespace GlobalTheory.ConcaveTwist

lemma contDiffOn_twEta (T : ℝ) : ContDiffOn ℝ ∞ (twEta T) (Set.Ioi (-1/4)) := by
  have hv := contDiff_twV T
  have h1 : ContDiff ℝ ∞ (fun y => 1 + twV T y) := contDiff_const.add hv
  exact ((contDiff_const.add hv).contDiffOn).add
    (h1.contDiffOn.log fun y hy => by have := twV_gt T y hy; linarith)

lemma twEta_pos (T y : ℝ) (hy : -1/4 < y) : 0 < twEta T y := by
  have hv := twV_gt T y hy
  have hw : 0 < 1 + twV T y := by linarith
  have hl := Real.one_sub_inv_le_log_of_pos hw
  have hi : (1 + twV T y)⁻¹ < 4/3 := by
    rw [inv_lt_comm₀ hw (by norm_num)]; linarith
  unfold twEta; linarith

lemma twEta_bounds (T y : ℝ) (hT : 0 ≤ T) (hy : 0 ≤ y) :
    0 ≤ twEta1 T y ∧ twEta1 T y ≤ 2 ∧ 2 ≤ twEta T y ∧ twEta2 T y < 0 ∧
      twEta T y ≤ 2 + 2 * min y (T + 1) ∧
      twEta T y + twEta1 T y ^ 2 / (-twEta2 T y) ≤ 8 * (1 + (min y (T + 1)) ^ 2) := by
  have hv0 := twV_nonneg T y hy
  have hvm : twV T y ≤ min y (T + 1) := le_min (twV_le_self T y hy) (twV_le T y hT)
  have hp0 := logistic_pos T y
  have hp1 := logistic_lt_one T y
  set v := twV T y with hvdef
  set p := twP T y with hpdef
  set m := min y (T + 1) with hmdef
  have hw : 0 < 1 + v := by linarith
  set r := (1 + v)⁻¹ with hrdef
  have hr0 : 0 < r := inv_pos.mpr hw
  have hwr : (1 + v) * r = 1 := mul_inv_cancel₀ hw.ne'
  have hr1 : r ≤ 1 := by nlinarith
  have hr2 : ((1 + v) ^ 2)⁻¹ = r ^ 2 := by rw [inv_pow]
  have hη1 : twEta1 T y = p * (1 + r) := rfl
  have hη2 : -twEta2 T y = p * (1 - p) * (1 + r) + p ^ 2 * r ^ 2 := by
    unfold twEta2; rw [← hvdef, ← hpdef, hr2]; ring
  have hη : twEta T y = 2 + v + Real.log (1 + v) := rfl
  have hlog0 : 0 ≤ Real.log (1 + v) := Real.log_nonneg (by linarith)
  have hlogv : Real.log (1 + v) ≤ v := by
    have := Real.log_le_sub_one_of_pos hw; linarith
  have hneg : 0 < -twEta2 T y := by
    rw [hη2]; have := mul_pos (mul_pos hp0 (sub_pos.mpr hp1)) (by linarith : (0:ℝ) < 1 + r)
    positivity
  have key : (2 + v) * r = 1 + r := by linear_combination hwr
  have key2 : ((2 + v) * r) ^ 2 = (1 + r) ^ 2 := by rw [key]
  have hratio : twEta1 T y ^ 2 / (-twEta2 T y) ≤ (2 + v) ^ 2 := by
    rw [div_le_iff₀ hneg]
    have e : (2 + v) ^ 2 * (-twEta2 T y) - twEta1 T y ^ 2 = (2 + v) ^ 2 * (p * (1 - p) * (1 + r)) := by
      rw [hη2, hη1]; linear_combination p ^ 2 * key2
    have : 0 ≤ (2 + v) ^ 2 * (p * (1 - p) * (1 + r)) := by
      have := sub_pos.mpr hp1; positivity
    linarith
  have hvm2 : v ^ 2 ≤ m ^ 2 := pow_le_pow_left₀ hv0 hvm 2
  refine ⟨by rw [hη1]; positivity, by rw [hη1]; nlinarith, by rw [hη]; linarith, by linarith,
    by rw [hη]; linarith, ?_⟩
  rw [hη]
  nlinarith [sq_nonneg (v - 3/7)]

lemma twEta_mid (T y : ℝ) (hT : 2 ≤ T) (h1 : T - 1 ≤ y) (h2 : y ≤ T + 1) :
    3 / 16 ≤ -twEta2 T y ∧ T ≤ twEta T y := by
  have hv := twV_ge_T_sub_two T y h1 h2
  have hv0 : 0 ≤ twV T y := by linarith
  have hp0 := logistic_pos T y
  have hp1 := logistic_lt_one T y
  have hpw := twistMap_add_mul T y
  set v := twV T y with hvdef
  set p := twP T y with hpdef
  set q := Real.exp (y - T) with hq
  have hq0 : 0 < q := Real.exp_pos _
  have he3 : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
  have hq3 : q ≤ 3 := by
    have : q ≤ Real.exp 1 := Real.exp_le_exp.mpr (by linarith)
    linarith
  have hqe : 1 ≤ q * Real.exp 1 := by
    rw [hq, ← Real.exp_add]; exact Real.one_le_exp (by linarith)
  have hq13 : 1 / 3 ≤ q := by nlinarith
  have hw : 0 < 1 + v := by linarith
  set r := (1 + v)⁻¹ with hrdef
  have hr0 : 0 < r := inv_pos.mpr hw
  have hr2 : ((1 + v) ^ 2)⁻¹ = r ^ 2 := by rw [inv_pow]
  have hη2 : -twEta2 T y = p * (1 - p) * (1 + r) + p ^ 2 * r ^ 2 := by
    unfold twEta2; rw [← hvdef, ← hpdef, hr2]; ring
  have h1p : 1 - p = q * p := by linear_combination (-1 : ℝ) * hpw
  have hpw2 : ((1 + q) * p) ^ 2 = 1 := by rw [hpw]; norm_num
  have e : q * p ^ 2 * 16 - 3 = p ^ 2 * (3 * q - 1) * (3 - q) := by
    linear_combination 3 * hpw2
  have hmain : 3 / 16 ≤ p * (1 - p) := by
    rw [h1p]
    have : 0 ≤ p ^ 2 * (3 * q - 1) * (3 - q) := by
      have a : 0 ≤ 3 * q - 1 := by linarith
      have b : 0 ≤ 3 - q := by linarith
      positivity
    nlinarith
  refine ⟨?_, ?_⟩
  · rw [hη2]
    have : 0 ≤ p * (1 - p) * r := by have := sub_pos.mpr hp1; positivity
    nlinarith [sq_nonneg (p * r)]
  · have hlog0 : 0 ≤ Real.log (1 + v) := Real.log_nonneg (by linarith)
    show T ≤ 2 + v + Real.log (1 + v)
    linarith

end GlobalTheory.ConcaveTwist


open GlobalTheory.ConcaveTwist in
theorem GlobalTheory.concave_twist_exists : ∀ T : ℝ, 300 ≤ T → ∃ η η1 η2 : ℝ → ℝ, ContDiffOn ℝ ∞ η (Set.Ioi (-1/4)) ∧ (∀ y, -1/4 < y → 0 < η y ∧ HasDerivAt η (η1 y) y ∧ HasDerivAt η1 (η2 y) y) ∧ (∀ y, 0 ≤ y → 0 ≤ η1 y ∧ η1 y ≤ 2 ∧ 2 ≤ η y ∧ η2 y < 0 ∧ η y ≤ 2 + 2 * min y (T + 1) ∧ η y + η1 y ^ 2 / (-η2 y) ≤ 8 * (1 + (min y (T + 1)) ^ 2)) ∧ (∀ y, T - 1 ≤ y → y ≤ T + 1 → 3 / 16 ≤ -η2 y ∧ T ≤ η y) := by
  intro T hT
  refine ⟨twEta T, twEta1 T, twEta2 T, contDiffOn_twEta T, ?_, ?_, ?_⟩
  · intro y hy
    have hw : 0 < 1 + twV T y := by linarith [twV_gt T y hy]
    exact ⟨twEta_pos T y hy, hasDerivAt_twEta T y hw, hasDerivAt_twEta1 T y hw⟩
  · intro y hy
    exact twEta_bounds T y (by linarith) hy
  · intro y h1 h2
    exact twEta_mid T y (by linarith) h1 h2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConcaveTwistEtaInequalitiesStatement
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_concaveTwist_eta_inequalities : ∀ T : ℝ, 300 ≤ T → ∃ η η1 η2 : ℝ → ℝ, ContDiffOn ℝ ∞ η (Set.Ioi (-1/4)) ∧ (∀ y, -1/4 < y → 0 < η y ∧ HasDerivAt η (η1 y) y ∧ HasDerivAt η1 (η2 y) y) ∧ (∀ y, 0 ≤ y → 0 ≤ η1 y ∧ η1 y ≤ 2 ∧ 2 ≤ η y ∧ η2 y < 0 ∧ η y ≤ 2 + 2 * min y (T + 1) ∧ η y + η1 y ^ 2 / (-η2 y) ≤ 8 * (1 + (min y (T + 1)) ^ 2)) ∧ (∀ y, T - 1 ≤ y → y ≤ T + 1 → 3 / 16 ≤ -η2 y ∧ T ≤ η y) := by
  first | exact @GlobalTheory.concave_twist_exists | exact GlobalTheory.concave_twist_exists | (intros; apply GlobalTheory.concave_twist_exists <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothLogTwistInequalities
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

private lemma twist_estimate_first (a b e M : ℝ) (ha : 0 ≤ a) (ha2 : a ≤ 2) (he : 2 ≤ e) (hb : 0 < b)
    (hM : 0 ≤ M) (h : e + a ^ 2 / b ≤ 8 * (1 + M)) :
    0 ≤ a / e ∧ a / e ≤ 1 ∧ 0 < (b * e + a ^ 2) / e ^ 2 ∧ (a / e) ^ 2 ≤ (b * e + a ^ 2) / e ^ 2 ∧
      1 / (1 + M) / 8 ≤ (1 - (a / e) ^ 2 / ((b * e + a ^ 2) / e ^ 2)) * e⁻¹ := by
  have he0 : 0 < e := by linarith
  have hD : 0 < b * e + a ^ 2 := by positivity
  refine ⟨by positivity, ?_, by positivity, ?_, ?_⟩
  · rw [div_le_one he0]; linarith
  · rw [div_pow]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have : 0 < b * e := by positivity
    linarith
  · have e1 : (1 - (a / e) ^ 2 / ((b * e + a ^ 2) / e ^ 2)) * e⁻¹ = 1 / (e + a ^ 2 / b) := by
      field_simp
      ring
    have e2 : 1 / (1 + M) / 8 = 1 / (8 * (1 + M)) := by
      field_simp
    rw [e1, e2]
    exact one_div_le_one_div_of_le (by positivity) h

private lemma twist_estimate_second (a b e m : ℝ) (ha : 0 ≤ a) (ha2 : a ≤ 2) (he : 300 ≤ e) (hb : 3 / 16 ≤ b)
    (h : e ≤ 2 + 2 * m) :
    e⁻¹ / ((b * e + a ^ 2) / e ^ 2) ≤ 16 / 3 ∧
      1 / (1 + m ^ 2) / 8 ≤ (1 - 5 * ((a / e) ^ 2 / ((b * e + a ^ 2) / e ^ 2))) * e⁻¹ := by
  have he0 : 0 < e := by linarith
  have hb0 : 0 < b := by linarith
  have hD : 0 < b * e + a ^ 2 := by positivity
  have hbe : 3 / 16 * e ≤ b * e := mul_le_mul_of_nonneg_right hb he0.le
  have ha4 : a ^ 2 ≤ 4 := by nlinarith
  have ha0 : 0 ≤ a ^ 2 := by positivity
  constructor
  · have e1 : e⁻¹ / ((b * e + a ^ 2) / e ^ 2) = e / (b * e + a ^ 2) := by
      field_simp
    rw [e1, div_le_iff₀ hD]
    linarith
  · have e1 : (a / e) ^ 2 / ((b * e + a ^ 2) / e ^ 2) = a ^ 2 / (b * e + a ^ 2) := by
      field_simp
    have h1 : a ^ 2 / (b * e + a ^ 2) ≤ 1 / 10 := by
      rw [div_le_iff₀ hD]; linarith
    have e2 : 1 / (1 + m ^ 2) / 8 = 1 / 2 * (4 * (1 + m ^ 2))⁻¹ := by
      field_simp
      norm_num
    have h2 : (4 * (1 + m ^ 2))⁻¹ ≤ e⁻¹ := by
      apply inv_anti₀ he0
      nlinarith [sq_nonneg (m - 1 / 4)]
    rw [e1, e2]
    apply mul_le_mul (by linarith) h2 (by positivity) (by linarith)

theorem exists_log_twist : ∀ T : ℝ, 300 ≤ T → ∃ κ : ℝ → ℝ, ContDiff ℝ ∞ κ ∧ (∃ C : ℝ, ∀ x, x ≤ 0 → |κ x| ≤ C) ∧ (∀ x, x ≤ 0 → 0 ≤ deriv κ x ∧ deriv κ x ≤ 1 ∧ 0 < deriv (deriv κ) x ∧ deriv κ x ^ 2 ≤ deriv (deriv κ) x ∧ wT T x / 8 ≤ (1 - deriv κ x ^ 2 / deriv (deriv κ) x) * Real.exp (κ x)) ∧ (∀ x, -T - 1 ≤ x → x ≤ -T + 1 → Real.exp (κ x) / deriv (deriv κ) x ≤ 16 / 3 ∧ wT T x / 8 ≤ (1 - 5 * (deriv κ x ^ 2 / deriv (deriv κ) x)) * Real.exp (κ x)) := by
  intro T hT
  obtain ⟨η, η1, η2, hs, hd, hp, hw⟩ := GlobalTheory.T.exists_concaveTwist_eta_inequalities T hT
  set κ : ℝ → ℝ := fun x => Real.smoothTransition (2 - 16 * x) * (-Real.log (η (-x))) with hκ
  have hloc : ∀ x : ℝ, x < 1 / 16 → κ x = -Real.log (η (-x)) := by
    intro x hx
    simp only [hκ]
    rw [Real.smoothTransition.one_of_one_le (by linarith), one_mul]
  have hη : ∀ x : ℝ, x < 1 / 16 → HasDerivAt (fun x => η (-x)) (-η1 (-x)) x := by
    intro x hx
    have h := (hd (-x) (by linarith)).2.1
    have h' := HasDerivAt.comp x (h₂ := η) (h := fun x : ℝ => -x) h (hasDerivAt_neg x)
    simpa [Function.comp_def] using h'
  have hη1 : ∀ x : ℝ, x < 1 / 16 → HasDerivAt (fun x => η1 (-x)) (-η2 (-x)) x := by
    intro x hx
    have h := (hd (-x) (by linarith)).2.2
    have h' := HasDerivAt.comp x (h₂ := η1) (h := fun x : ℝ => -x) h (hasDerivAt_neg x)
    simpa [Function.comp_def] using h'
  have hd1 : ∀ x : ℝ, x < 1 / 16 → deriv κ x = η1 (-x) / η (-x) := by
    intro x hx
    have hev : κ =ᶠ[𝓝 x] fun x => -Real.log (η (-x)) := by
      filter_upwards [Iio_mem_nhds hx] with y hy using hloc y hy
    rw [hev.deriv_eq]
    have h := ((hη x hx).log (hd (-x) (by linarith)).1.ne').neg
    have h2 : HasDerivAt (fun x => -Real.log (η (-x))) (-(-η1 (-x) / η (-x))) x := h
    rw [h2.deriv]; ring
  have hd2 : ∀ x : ℝ, x < 1 / 16 →
      deriv (deriv κ) x = ((-η2 (-x)) * η (-x) + η1 (-x) ^ 2) / η (-x) ^ 2 := by
    intro x hx
    have hev : deriv κ =ᶠ[𝓝 x] fun x => η1 (-x) / η (-x) := by
      filter_upwards [Iio_mem_nhds hx] with y hy using hd1 y hy
    rw [hev.deriv_eq]
    have h2 : HasDerivAt (fun x => η1 (-x) / η (-x)) _ x :=
      (hη1 x hx).div (hη x hx) (hd (-x) (by linarith)).1.ne'
    rw [h2.deriv]; ring
  have hexp : ∀ x : ℝ, x < 1 / 16 → Real.exp (κ x) = (η (-x))⁻¹ := by
    intro x hx
    rw [hloc x hx, Real.exp_neg, Real.exp_log (hd (-x) (by linarith)).1]
  have hwT : ∀ x : ℝ, x ≤ 0 → wT T x = 1 / (1 + (min (-x) (T + 1)) ^ 2) := by
    intro x hx
    unfold wT
    congr 2
    rcases le_total (-x) (T + 1) with h | h
    · rw [min_eq_left h, min_eq_left (by nlinarith)]; ring
    · rw [min_eq_right h, min_eq_right (by nlinarith)]
  refine ⟨κ, ?_, ⟨Real.log (2 * T + 4), ?_⟩, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x < 1 / 4
    · have h1 : ContDiffAt ℝ ∞ η (-x) :=
        hs.contDiffAt (Ioi_mem_nhds (by linarith))
      have h2 : ContDiffAt ℝ ∞ (fun x : ℝ => η (-x)) x :=
        ContDiffAt.comp x (g := η) (f := fun x : ℝ => -x) h1 contDiff_neg.contDiffAt
      have h3 := (h2.log (hd (-x) (by linarith)).1.ne').neg
      have h4 : ContDiff ℝ ∞ (fun x : ℝ => Real.smoothTransition (2 - 16 * x)) :=
        Real.smoothTransition.contDiff.comp (by fun_prop)
      exact h4.contDiffAt.mul h3
    · have hev : κ =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [Ioi_mem_nhds (show (1 / 8 : ℝ) < x by linarith)] with y hy
        have hy' : (1 / 8 : ℝ) < y := hy
        simp only [hκ]
        rw [Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  · intro x hx
    obtain ⟨-, -, h2, -, h3, -⟩ := hp (-x) (by linarith)
    rw [hloc x (by linarith), abs_neg, abs_of_nonneg (Real.log_nonneg (by linarith))]
    apply Real.log_le_log (by linarith)
    have := min_le_right (-x) (T + 1)
    linarith
  · intro x hx
    have hx' : x < 1 / 16 := by linarith
    obtain ⟨h0, h1, h2, h3, -, h5⟩ := hp (-x) (by linarith)
    rw [hd1 x hx', hd2 x hx', hexp x hx', hwT x hx]
    exact twist_estimate_first _ _ _ _ h0 h1 h2 (by linarith) (sq_nonneg _) h5
  · intro x hx1 hx2
    have hx : x ≤ 0 := by linarith
    have hx' : x < 1 / 16 := by linarith
    obtain ⟨h0, h1, -, -, h4, -⟩ := hp (-x) (by linarith)
    obtain ⟨h6, h7⟩ := hw (-x) (by linarith) (by linarith)
    rw [hd2 x hx', hd1 x hx', hexp x hx', hwT x hx]
    exact twist_estimate_second _ _ _ _ h0 h1 (by linarith) h6 h4

end GlobalTheory.OTY
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothLogTwistInequalitiesStatement
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smooth_log_twist_inequalities : ∀ T : ℝ, 300 ≤ T → ∃ κ : ℝ → ℝ, ContDiff ℝ ∞ κ ∧ (∃ C : ℝ, ∀ x, x ≤ 0 → |κ x| ≤ C) ∧ (∀ x, x ≤ 0 → 0 ≤ deriv κ x ∧ deriv κ x ≤ 1 ∧ 0 < deriv (deriv κ) x ∧ deriv κ x ^ 2 ≤ deriv (deriv κ) x ∧ wT T x / 8 ≤ (1 - deriv κ x ^ 2 / deriv (deriv κ) x) * Real.exp (κ x)) ∧ (∀ x, -T - 1 ≤ x → x ≤ -T + 1 → Real.exp (κ x) / deriv (deriv κ) x ≤ 16 / 3 ∧ wT T x / 8 ≤ (1 - 5 * (deriv κ x ^ 2 / deriv (deriv κ) x)) * Real.exp (κ x)) := by
  first | exact @GlobalTheory.OTY.exists_log_twist | exact GlobalTheory.OTY.exists_log_twist | (intros; apply GlobalTheory.OTY.exists_log_twist <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointwiseAbsorptionTwisted
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointwiseAbsorptionTwisted
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

theorem pointwise_absorption_twisted :
    ∀ (T x u g t k1 k2 E : ℝ), 0 ≤ u → 0 ≤ g → 0 < k2 → 0 < E → |t| ≤ 3 / 4 →
      wT T x / 8 ≤ (1 - k1 ^ 2 / k2) * E →
      ((-T - 1 ≤ x ∧ x ≤ -T + 1) → E / k2 ≤ 16 / 3 ∧ wT T x / 8 ≤ (1 - 5 * (k1 ^ 2 / k2)) * E) →
      (¬ (-T - 1 ≤ x ∧ x ≤ -T + 1) → t = 0) →
      (Real.sqrt (t ^ 2 * g ^ 2 / k2) + u * Real.sqrt (k1 ^ 2 / k2)) ^ 2 * E + u ^ 2 * (wT T x / 8)
        ≤ u ^ 2 * E + (if (-T - 1 ≤ x ∧ x ≤ -T + 1) then 15 / 4 * g ^ 2 else 0) := by
  intro T x u g t k1 k2 E hu hg hk2 hE ht hw hwin hoff
  have ha : 0 ≤ t ^ 2 * g ^ 2 / k2 := by positivity
  have hb : 0 ≤ k1 ^ 2 / k2 := by positivity
  have hA := Real.sq_sqrt ha
  have hB := Real.sq_sqrt hb
  have hA0 := Real.sqrt_nonneg (t ^ 2 * g ^ 2 / k2)
  have hB0 := Real.sqrt_nonneg (k1 ^ 2 / k2)
  by_cases h : (-T - 1 ≤ x ∧ x ≤ -T + 1)
  · rw [if_pos h]
    obtain ⟨h1, h2⟩ := hwin h
    have ht2 : t ^ 2 ≤ 9 / 16 := by
      have h0 : 0 ≤ |t| := abs_nonneg t
      have : |t| ^ 2 ≤ (3 / 4) ^ 2 := by nlinarith
      rw [sq_abs] at this
      linarith
    have haE : t ^ 2 * g ^ 2 / k2 * E ≤ 3 * g ^ 2 := by
      have e : t ^ 2 * g ^ 2 / k2 * E = t ^ 2 * g ^ 2 * (E / k2) := by ring
      rw [e]
      calc t ^ 2 * g ^ 2 * (E / k2) ≤ (9 / 16) * g ^ 2 * (16 / 3) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_right ht2 (sq_nonneg g)) h1
              (by positivity) (by positivity)
        _ = 3 * g ^ 2 := by ring
    have key : (Real.sqrt (t ^ 2 * g ^ 2 / k2) + u * Real.sqrt (k1 ^ 2 / k2)) ^ 2
        ≤ 5 / 4 * (t ^ 2 * g ^ 2 / k2) + 5 * (k1 ^ 2 / k2) * u ^ 2 := by
      nlinarith [sq_nonneg (Real.sqrt (t ^ 2 * g ^ 2 / k2) / 2 - 2 * u * Real.sqrt (k1 ^ 2 / k2))]
    have k1' := mul_le_mul_of_nonneg_right key hE.le
    have k2' := mul_le_mul_of_nonneg_left h2 (sq_nonneg u)
    nlinarith
  · rw [if_neg h]
    have t0 := hoff h
    subst t0
    have z : Real.sqrt ((0:ℝ) ^ 2 * g ^ 2 / k2) = 0 := by simp
    rw [z]
    have k2' := mul_le_mul_of_nonneg_left hw (sq_nonneg u)
    have e : (0 + u * Real.sqrt (k1 ^ 2 / k2)) ^ 2 * E = u ^ 2 * (k1 ^ 2 / k2) * E := by
      rw [zero_add, mul_pow, hB]
    rw [e]
    nlinarith

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointwiseAbsorptionTwistedStatement
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sq_sqrt_add_mul_le_of_twisted_absorption : ∀ (T x u g t k1 k2 E : ℝ), 0 ≤ u → 0 ≤ g → 0 < k2 → 0 < E → |t| ≤ 3 / 4 → wT T x / 8 ≤ (1 - k1 ^ 2 / k2) * E → ((-T - 1 ≤ x ∧ x ≤ -T + 1) → E / k2 ≤ 16 / 3 ∧ wT T x / 8 ≤ (1 - 5 * (k1 ^ 2 / k2)) * E) → (¬ (-T - 1 ≤ x ∧ x ≤ -T + 1) → t = 0) → (Real.sqrt (t ^ 2 * g ^ 2 / k2) + u * Real.sqrt (k1 ^ 2 / k2)) ^ 2 * E + u ^ 2 * (wT T x / 8) ≤ u ^ 2 * E + (if (-T - 1 ≤ x ∧ x ≤ -T + 1) then 15 / 4 * g ^ 2 else 0) := by
  first | exact @GlobalTheory.pointwise_absorption_twisted | exact GlobalTheory.pointwise_absorption_twisted | (intros; apply GlobalTheory.pointwise_absorption_twisted <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviFormTwistedWeightLowerBound
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviFormTwistedWeightLowerBound
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.LeviTwistLower

theorem main : ∀ (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M], ∀ (z : M → V n) (φ ψ : M → ℝ) (δ : ℝ) (κ : ℝ → ℝ), IsLocalHomeomorph z → SmoothR n z φ → SmoothR n z ψ → (∀ x, ψ x ≤ 0) → 0 < δ → ContDiff ℝ ∞ κ → (∀ t, t ≤ 0 → 0 ≤ deriv κ t ∧ deriv κ t ≤ 1) → (∀ α ∈ Set.Icc (1 : ℝ) (1 + δ), LeviNonneg n z (fun x => φ x + α * ψ x)) → SmoothR n z (fun x => κ (δ * ψ x)) ∧ ∀ (x : M) (ξ : Fin n → ℂ), dbarDot n z (fun y => ((κ (δ * ψ y) : ℝ) : ℂ)) x ξ = ((deriv κ (δ * ψ x) * δ : ℝ) : ℂ) * dbarDot n z (fun y => (ψ y : ℂ)) x ξ ∧ deriv (deriv κ) (δ * ψ x) * (δ ^ 2 * ‖dbarDot n z (fun y => (ψ y : ℂ)) x ξ‖ ^ 2) ≤ (Levi n z (fun y => (φ y + ψ y) + κ (δ * ψ y)) x ξ).re := by
  intro n M _ _ _ _ _ z φ ψ δ κ hz hφ hψ hψ0 hδ hκ hκ' hL
  obtain ⟨hκd, hκ1⟩ := contDiff_infty_iff_deriv.1 hκ
  have hκdd : Differentiable ℝ (deriv κ) := (contDiff_infty_iff_deriv.1 hκ1).1
  set k : ℝ → ℝ := fun t => κ (δ * t) with hkdef
  have hk : ContDiff ℝ ∞ k := hκ.comp (contDiff_const.mul contDiff_id)
  have hD : ∀ t, HasDerivAt k (deriv κ (δ * t) * δ) t := by
    intro t
    have h := (hκd (δ * t)).hasDerivAt.comp t ((hasDerivAt_id t).const_mul δ)
    simpa [hkdef, Function.comp_def] using h
  have hDk : deriv k = fun t => deriv κ (δ * t) * δ := funext fun t => (hD t).deriv
  have hDD : ∀ t, deriv (deriv k) t = deriv (deriv κ) (δ * t) * δ ^ 2 := by
    intro t
    rw [hDk]
    have h := ((hκdd (δ * t)).hasDerivAt.comp t ((hasDerivAt_id t).const_mul δ)).mul_const δ
    exact h.deriv.trans (by ring)
  have hks : SmoothR n z (fun x => κ (δ * ψ x)) := SmoothR.comp n z k hk ψ hψ
  refine ⟨hks, fun x ξ => ⟨?_, ?_⟩⟩
  · unfold dbarDot
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have := db_comp_real n z k hk ψ (SmoothR.ckR n z 1 _ hψ) j x
    rw [(hD (ψ x)).deriv] at this
    change db n z j (fun y => ((k (ψ y) : ℝ) : ℂ)) x * _ = _
    rw [this]; ring
  · have hC := chain n M z hz k ψ (contDiff_infty.1 hk 2) hψ x ξ
    rw [(hD (ψ x)).deriv, hDD (ψ x)] at hC
    have hnorm : ‖dbarDot n z (fun y => (ψ y : ℂ)) x ξ‖ = ‖dDot n z (fun y => (ψ y : ℂ)) x ξ‖ := by
      have : dbarDot n z (fun y => (ψ y : ℂ)) x ξ = (starRingEnd ℂ) (dDot n z (fun y => (ψ y : ℂ)) x ξ) := by
        unfold dbarDot dDot
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [db_ofReal n z ψ j x, map_mul]
      rw [this, Complex.norm_conj]
    have hsum : Levi n z (fun y => (φ y + ψ y) + κ (δ * ψ y)) x ξ =
        Levi n z φ x ξ + Levi n z ψ x ξ + Levi n z (fun y => k (ψ y)) x ξ := by
      rw [levi_add n z (fun y => φ y + ψ y) (fun y => κ (δ * ψ y))
        (SmoothR.ckR n z 2 _ (SmoothR.add n z _ _ hφ hψ)) (SmoothR.ckR n z 2 _ hks) x ξ,
        levi_add n z φ ψ (SmoothR.ckR n z 2 _ hφ) (SmoothR.ckR n z 2 _ hψ) x ξ]
    set α : ℝ := 1 + δ * deriv κ (δ * ψ x) with hα
    have hmem : α ∈ Set.Icc (1 : ℝ) (1 + δ) := by
      obtain ⟨h0, h1⟩ := hκ' (δ * ψ x) (mul_nonpos_of_nonneg_of_nonpos hδ.le (hψ0 x))
      constructor
      · nlinarith
      · nlinarith
    have hnn := hL α hmem x ξ
    rw [levi_add n z φ (fun y => α * ψ y) (SmoothR.ckR n z 2 _ hφ)
      (SmoothR.ckR n z 2 _ (SmoothR.mul n z _ _ (smoothR_const n z α) hψ)) x ξ,
      levi_const_mul n z α ψ (SmoothR.ckR n z 2 _ hψ) x ξ] at hnn
    rw [hsum, hC, hnorm]
    simp only [Complex.add_re, Complex.re_ofReal_mul, Complex.ofReal_re] at hnn ⊢
    rw [hα] at hnn
    nlinarith

end GlobalTheory.LeviTwistLower
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviFormTwistedWeightLowerBoundStatement
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leviForm_twisted_weight_lower_bound : ∀ (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M], ∀ (z : M → V n) (φ ψ : M → ℝ) (δ : ℝ) (κ : ℝ → ℝ), IsLocalHomeomorph z → SmoothR n z φ → SmoothR n z ψ → (∀ x, ψ x ≤ 0) → 0 < δ → ContDiff ℝ ∞ κ → (∀ t, t ≤ 0 → 0 ≤ deriv κ t ∧ deriv κ t ≤ 1) → (∀ α ∈ Set.Icc (1 : ℝ) (1 + δ), LeviNonneg n z (fun x => φ x + α * ψ x)) → SmoothR n z (fun x => κ (δ * ψ x)) ∧ ∀ (x : M) (ξ : Fin n → ℂ), dbarDot n z (fun y => ((κ (δ * ψ y) : ℝ) : ℂ)) x ξ = ((deriv κ (δ * ψ x) * δ : ℝ) : ℂ) * dbarDot n z (fun y => (ψ y : ℂ)) x ξ ∧ deriv (deriv κ) (δ * ψ x) * (δ ^ 2 * ‖dbarDot n z (fun y => (ψ y : ℂ)) x ξ‖ ^ 2) ≤ (Levi n z (fun y => (φ y + ψ y) + κ (δ * ψ y)) x ξ).re := by
  first | exact @GlobalTheory.LeviTwistLower.main | exact GlobalTheory.LeviTwistLower.main | (intros; apply GlobalTheory.LeviTwistLower.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedExtensionEtaleSteinSqIntegrable
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

theorem twEst_cancel {M : Type} [MeasurableSpace M] (μ : Measure M) (A B W S : M → ℝ≥0∞)
    (hS : Measurable S) (hpt : ∀ x, A x + W x ≤ B x + S x)
    (hBA : ∫⁻ x, B x ∂μ ≤ ∫⁻ x, A x ∂μ) (hB : ∫⁻ x, B x ∂μ ≠ ⊤) :
    ∫⁻ x, W x ∂μ ≤ ∫⁻ x, S x ∂μ := by
  have h1 : ∫⁻ x, A x ∂μ + ∫⁻ x, W x ∂μ ≤ ∫⁻ x, B x ∂μ + ∫⁻ x, S x ∂μ :=
    (le_lintegral_add A W).trans ((lintegral_mono hpt).trans_eq (lintegral_add_right _ hS))
  have h2 : ∫⁻ x, B x ∂μ + ∫⁻ x, W x ∂μ ≤ ∫⁻ x, B x ∂μ + ∫⁻ x, S x ∂μ :=
    (add_le_add hBA le_rfl).trans h1
  exact (ENNReal.add_le_add_iff_left hB).1 h2

theorem twEst_deriv_cut_zero (T : ℝ) (θ : ℝ → ℝ) (hθ : IsCut T θ) (s : ℝ)
    (hs : ¬ (-T - 1 ≤ s ∧ s ≤ -T + 1)) : deriv θ s = 0 := by
  obtain ⟨_, hθ1, hθ0, _, _⟩ := hθ
  rcases not_and_or.1 hs with h | h
  · push_neg at h
    have he : θ =ᶠ[𝓝 s] fun _ => (1 : ℝ) := by
      filter_upwards [Iio_mem_nhds h] with y hy using hθ1 y (le_of_lt hy)
    rw [he.deriv_eq]; simp
  · push_neg at h
    have he : θ =ᶠ[𝓝 s] fun _ => (0 : ℝ) := by
      filter_upwards [Ioi_mem_nhds h] with y hy using hθ0 y (le_of_lt hy)
    rw [he.deriv_eq]; simp

theorem twistedExtension_sqInt : ∀ (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M], ∀ (X : EtaleStein n M) (φ ψ : M → ℝ) (G : M → ℂ) (Ω : Set M) (δ T : ℝ) (θ : ℝ → ℝ), SmoothR n X.z φ → SmoothR n X.z ψ → (∀ x, ψ x ≤ 0) → 0 < δ → 300 ≤ T → IsCut T θ → (∀ α ∈ Set.Icc (1 : ℝ) (1 + δ), LeviNonneg n X.z (fun x => φ x + α * ψ x)) → IsOpen Ω → Measurable G → (∀ e : OpenPartialHomeomorph M (V n), IsChart n X.z e → DifferentiableOn ℂ (G ∘ e.symm) (e.target ∩ e.symm ⁻¹' Ω)) → (∀ x, δ * ψ x ≤ -T + 1 → x ∈ Ω) → wint n X.z (fun x => (θ (δ * ψ x) : ℂ) * G x) (fun x => φ x + ψ x) < ⊤ → ∃ F : M → ℂ, Holo n X.z F ∧ ∫⁻ x, ENNReal.ofReal (‖(θ (δ * ψ x) : ℂ) * G x - F x‖ ^ 2 * (wT T (δ * ψ x) * Real.exp (-(φ x + ψ x)))) ∂vol n X.z ≤ 30 * ∫⁻ x in {x | -T - 1 ≤ δ * ψ x ∧ δ * ψ x ≤ -T + 1}, ENNReal.ofReal (‖G x‖ ^ 2 * Real.exp (-(φ x + ψ x))) ∂vol n X.z := by
  intro n M _ _ _ _ _ X φ ψ G Ω δ T θ hφ hψ hψ0 hδ hT hθ hlevi hΩ hG hGh hΩsub hint
  have hz := X.isLocalHomeomorph
  obtain ⟨κ, hκ, ⟨C, hC⟩, hκ1, hκ2⟩ := GlobalTheory.T.exists_smooth_log_twist_inequalities T hT
  have hθ' := hθ
  obtain ⟨hθs, hθ1, hθ0, hθb, hθd⟩ := hθ'
  have hδψ : ∀ x, δ * ψ x ≤ 0 := fun x => mul_nonpos_of_nonneg_of_nonpos hδ.le (hψ0 x)
  have hk2 : ∀ x, 0 < deriv (deriv κ) (δ * ψ x) := fun x => (hκ1 _ (hδψ x)).2.2.1
  have h6 := GlobalTheory.T.leviForm_twisted_weight_lower_bound n M X.z φ ψ δ κ hz hφ hψ hψ0 hδ hκ
    (fun t ht => ⟨(hκ1 t ht).1, (hκ1 t ht).2.1⟩) hlevi
  have h7 := GlobalTheory.T.cutoff_holo_smooth_dbar_formula n M X ψ G Ω δ (-T + 1) θ hψ hθs (fun t ht => hθ0 t ht) hΩ hGh hΩsub
  have hψc : Continuous ψ := ReciprocityTheory.L2DbarEstimates.F.smoothReal_continuous n X.z hz ψ hψ
  have hφc : Continuous φ := ReciprocityTheory.L2DbarEstimates.F.smoothReal_continuous n X.z hz φ hφ
  have hψm : Measurable ψ := hψc.measurable
  have hφm : Measurable φ := hφc.measurable
  have hθm : Measurable θ := hθs.continuous.measurable
  have hdθ : Measurable (deriv θ) := measurable_deriv θ
  have hdk : Measurable (deriv (deriv κ)) := measurable_deriv _
  have hdk1 : Measurable (deriv κ) := measurable_deriv _
  have hκm : Measurable κ := hκ.continuous.measurable
  have hLevi : ∀ x ξ, deriv (deriv κ) (δ * ψ x) *
      (δ ^ 2 * ‖dbarDot n X.z (fun y => (ψ y : ℂ)) x ξ‖ ^ 2) ≤
      (Levi n X.z (fun y => (φ y + ψ y) + κ (δ * ψ y)) x ξ).re := fun x ξ => (h6.2 x ξ).2
  have hLnn : ∀ x ξ, 0 ≤ (Levi n X.z (fun y => (φ y + ψ y) + κ (δ * ψ y)) x ξ).re := by
    intro x ξ
    exact le_trans (mul_nonneg (hk2 x).le (by positivity)) (hLevi x ξ)
  obtain ⟨⟨F, hF⟩, hbd⟩ := ReciprocityTheory.L2DbarEstimates.tw n M X (fun x => φ x + ψ x) (fun x => κ (δ * ψ x))
    (fun x => (θ (δ * ψ x) : ℂ) * G x)
    (fun x => deriv θ (δ * ψ x) ^ 2 * ‖G x‖ ^ 2 / deriv (deriv κ) (δ * ψ x))
    (fun x => deriv κ (δ * ψ x) ^ 2 / deriv (deriv κ) (δ * ψ x))
    (SmoothR.add n X.z φ ψ hφ hψ) h6.1 ⟨C, fun x => hC _ (hδψ x)⟩ hLnn h7.1 hint
    (by fun_prop) (by fun_prop)
    (fun x => div_nonneg (by positivity) (hk2 x).le)
    (fun x => div_nonneg (by positivity) (hk2 x).le)
    (fun x => (div_le_one (hk2 x)).2 (hκ1 _ (hδψ x)).2.2.2.1)
    (by
      intro x ξ
      rw [(h7.2 x ξ)]
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc (|deriv θ (δ * ψ x)| * |δ| * ‖G x‖ * ‖dbarDot n X.z (fun y => (ψ y : ℂ)) x ξ‖) ^ 2
          = deriv θ (δ * ψ x) ^ 2 * ‖G x‖ ^ 2 / deriv (deriv κ) (δ * ψ x) *
            (deriv (deriv κ) (δ * ψ x) *
              (δ ^ 2 * ‖dbarDot n X.z (fun y => (ψ y : ℂ)) x ξ‖ ^ 2)) := by
            simp only [mul_pow, sq_abs]
            field_simp [(hk2 x).ne']
        _ ≤ _ := mul_le_mul_of_nonneg_left (hLevi x ξ) (div_nonneg (by positivity) (hk2 x).le))
    (by
      intro x ξ
      rw [(h6.2 x ξ).1]
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc (|deriv κ (δ * ψ x)| * |δ| * ‖dbarDot n X.z (fun y => (ψ y : ℂ)) x ξ‖) ^ 2
          = deriv κ (δ * ψ x) ^ 2 / deriv (deriv κ) (δ * ψ x) *
            (deriv (deriv κ) (δ * ψ x) *
              (δ ^ 2 * ‖dbarDot n X.z (fun y => (ψ y : ℂ)) x ξ‖ ^ 2)) := by
            simp only [mul_pow, sq_abs]
            field_simp [(hk2 x).ne']
        _ ≤ _ := mul_le_mul_of_nonneg_left (hLevi x ξ) (div_nonneg (by positivity) (hk2 x).le))
  refine ⟨F, hF.1, ?_⟩
  have hB := hbd F hF
  beta_reduce at hB
  have hsh : MeasurableSet {x | -T - 1 ≤ δ * ψ x ∧ δ * ψ x ≤ -T + 1} := by
    have h1 : Measurable (fun x => δ * ψ x) := by fun_prop
    exact (measurableSet_le measurable_const h1).inter (measurableSet_le h1 measurable_const)
  have hw : ∀ s, 0 ≤ wT T s := fun s => by unfold wT; positivity
  have hfin : ∫⁻ x, ENNReal.ofReal (‖(θ (δ * ψ x) : ℂ) * G x - F x‖ ^ 2 *
      Real.exp (κ (δ * ψ x) - (φ x + ψ x))) ∂vol n X.z ≠ ⊤ := by
    have hF0 : ∫⁻ x, ENNReal.ofReal (‖(θ (δ * ψ x) : ℂ) * G x‖ ^ 2 *
        Real.exp (-(φ x + ψ x))) ∂vol n X.z < ⊤ := hint
    have hF1 : ∫⁻ x, ENNReal.ofReal (‖F x‖ ^ 2 * Real.exp (-(φ x + ψ x))) ∂vol n X.z < ⊤ :=
      hF.2.1
    refine ne_of_lt (lt_of_le_of_lt (lintegral_mono (g := fun x =>
      ENNReal.ofReal (2 * Real.exp C) *
        (ENNReal.ofReal (‖(θ (δ * ψ x) : ℂ) * G x‖ ^ 2 * Real.exp (-(φ x + ψ x))) +
          ENNReal.ofReal (‖F x‖ ^ 2 * Real.exp (-(φ x + ψ x))))) ?_) ?_)
    · intro x
      beta_reduce
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have hu : ‖(θ (δ * ψ x) : ℂ) * G x - F x‖ ^ 2 ≤
          2 * (‖(θ (δ * ψ x) : ℂ) * G x‖ ^ 2 + ‖F x‖ ^ 2) := by
        have h0 := norm_sub_le ((θ (δ * ψ x) : ℂ) * G x) (F x)
        have h1 := pow_le_pow_left₀ (norm_nonneg _) h0 2
        nlinarith [sq_nonneg (‖(θ (δ * ψ x) : ℂ) * G x‖ - ‖F x‖)]
      have hk : Real.exp (κ (δ * ψ x)) ≤ Real.exp C :=
        Real.exp_le_exp.2 (le_trans (le_abs_self _) (hC _ (hδψ x)))
      have he : Real.exp (κ (δ * ψ x) - (φ x + ψ x)) =
          Real.exp (κ (δ * ψ x)) * Real.exp (-(φ x + ψ x)) := by
        rw [sub_eq_add_neg, Real.exp_add]
      rw [he]
      have hpos := Real.exp_pos (-(φ x + ψ x))
      calc ‖(θ (δ * ψ x) : ℂ) * G x - F x‖ ^ 2 *
            (Real.exp (κ (δ * ψ x)) * Real.exp (-(φ x + ψ x)))
          ≤ (2 * (‖(θ (δ * ψ x) : ℂ) * G x‖ ^ 2 + ‖F x‖ ^ 2)) *
            (Real.exp C * Real.exp (-(φ x + ψ x))) :=
            mul_le_mul hu (mul_le_mul_of_nonneg_right hk hpos.le) (by positivity) (by positivity)
        _ = _ := by ring
    · rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left (by fun_prop)]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.add_lt_top.2 ⟨hF0, hF1⟩)
  have hcan := twEst_cancel (vol n X.z)
    (fun x => ENNReal.ofReal ((Real.sqrt (deriv θ (δ * ψ x) ^ 2 * ‖G x‖ ^ 2 /
        deriv (deriv κ) (δ * ψ x)) + ‖(θ (δ * ψ x) : ℂ) * G x - F x‖ *
        Real.sqrt (deriv κ (δ * ψ x) ^ 2 / deriv (deriv κ) (δ * ψ x))) ^ 2 *
        Real.exp (κ (δ * ψ x) - (φ x + ψ x))))
    (fun x => ENNReal.ofReal (‖(θ (δ * ψ x) : ℂ) * G x - F x‖ ^ 2 *
        Real.exp (κ (δ * ψ x) - (φ x + ψ x))))
    (fun x => ENNReal.ofReal (‖(θ (δ * ψ x) : ℂ) * G x - F x‖ ^ 2 * (wT T (δ * ψ x) / 8) *
        Real.exp (-(φ x + ψ x))))
    (Set.indicator {x | -T - 1 ≤ δ * ψ x ∧ δ * ψ x ≤ -T + 1}
      (fun x => ENNReal.ofReal (15 / 4 * (‖G x‖ ^ 2 * Real.exp (-(φ x + ψ x))))))
    ((by fun_prop : Measurable (fun x =>
      ENNReal.ofReal (15 / 4 * (‖G x‖ ^ 2 * Real.exp (-(φ x + ψ x)))))).indicator hsh)
    (by
      intro x
      beta_reduce
      have h8 := GlobalTheory.T.sq_sqrt_add_mul_le_of_twisted_absorption T (δ * ψ x) ‖(θ (δ * ψ x) : ℂ) * G x - F x‖ ‖G x‖
        (deriv θ (δ * ψ x)) (deriv κ (δ * ψ x)) (deriv (deriv κ) (δ * ψ x))
        (Real.exp (κ (δ * ψ x))) (norm_nonneg _) (norm_nonneg _) (hk2 x) (Real.exp_pos _)
        (hθd _) (hκ1 _ (hδψ x)).2.2.2.2 (fun h => hκ2 _ h.1 h.2)
        (fun h => twEst_deriv_cut_zero T θ hθ _ h)
      have he : Real.exp (κ (δ * ψ x) - (φ x + ψ x)) =
          Real.exp (κ (δ * ψ x)) * Real.exp (-(φ x + ψ x)) := by
        rw [sub_eq_add_neg, Real.exp_add]
      have hp := Real.exp_pos (-(φ x + ψ x))
      have hreal := mul_le_mul_of_nonneg_right h8 hp.le
      have hwx := hw (δ * ψ x)
      rw [he]
      by_cases hx : -T - 1 ≤ δ * ψ x ∧ δ * ψ x ≤ -T + 1
      · rw [Set.indicator_of_mem (show x ∈ {x | -T - 1 ≤ δ * ψ x ∧ δ * ψ x ≤ -T + 1} from hx),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        rw [if_pos hx] at hreal
        linear_combination hreal
      · rw [Set.indicator_of_notMem (show x ∉ {x | -T - 1 ≤ δ * ψ x ∧ δ * ψ x ≤ -T + 1} from hx),
          ← ENNReal.ofReal_add (by positivity) (by positivity), add_zero]
        apply ENNReal.ofReal_le_ofReal
        rw [if_neg hx] at hreal
        linear_combination hreal)
    hB hfin
  have hLHS : ∫⁻ x, ENNReal.ofReal (‖(θ (δ * ψ x) : ℂ) * G x - F x‖ ^ 2 *
      (wT T (δ * ψ x) * Real.exp (-(φ x + ψ x)))) ∂vol n X.z =
      ENNReal.ofReal 8 * ∫⁻ x, ENNReal.ofReal (‖(θ (δ * ψ x) : ℂ) * G x - F x‖ ^ 2 *
        (wT T (δ * ψ x) / 8) * Real.exp (-(φ x + ψ x))) ∂vol n X.z := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr (fun x => ?_)
    rw [← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    ring
  have hRHS : ∫⁻ x, Set.indicator {x | -T - 1 ≤ δ * ψ x ∧ δ * ψ x ≤ -T + 1}
      (fun x => ENNReal.ofReal (15 / 4 * (‖G x‖ ^ 2 * Real.exp (-(φ x + ψ x))))) x ∂vol n X.z =
      ENNReal.ofReal (15 / 4) * ∫⁻ x in {x | -T - 1 ≤ δ * ψ x ∧ δ * ψ x ≤ -T + 1},
        ENNReal.ofReal (‖G x‖ ^ 2 * Real.exp (-(φ x + ψ x))) ∂vol n X.z := by
    rw [lintegral_indicator hsh, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr (fun x => ?_)
    rw [ENNReal.ofReal_mul (by norm_num)]
  rw [hLHS]
  calc ENNReal.ofReal 8 * ∫⁻ x, ENNReal.ofReal (‖(θ (δ * ψ x) : ℂ) * G x - F x‖ ^ 2 *
        (wT T (δ * ψ x) / 8) * Real.exp (-(φ x + ψ x))) ∂vol n X.z
      ≤ ENNReal.ofReal 8 * ∫⁻ x, Set.indicator {x | -T - 1 ≤ δ * ψ x ∧ δ * ψ x ≤ -T + 1}
        (fun x => ENNReal.ofReal (15 / 4 * (‖G x‖ ^ 2 * Real.exp (-(φ x + ψ x))))) x
          ∂vol n X.z := by gcongr
    _ = _ := by
      rw [hRHS, ← mul_assoc, ← ENNReal.ofReal_mul (by norm_num)]
      norm_num

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedExtensionEtaleSteinSqIntegrableStatement
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedExtension_etaleStein_sqIntegrable : ∀ (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M], ∀ (X : EtaleStein n M) (φ ψ : M → ℝ) (G : M → ℂ) (Ω : Set M) (δ T : ℝ) (θ : ℝ → ℝ), SmoothR n X.z φ → SmoothR n X.z ψ → (∀ x, ψ x ≤ 0) → 0 < δ → 300 ≤ T → IsCut T θ → (∀ α ∈ Set.Icc (1 : ℝ) (1 + δ), LeviNonneg n X.z (fun x => φ x + α * ψ x)) → IsOpen Ω → Measurable G → (∀ e : OpenPartialHomeomorph M (V n), IsChart n X.z e → DifferentiableOn ℂ (G ∘ e.symm) (e.target ∩ e.symm ⁻¹' Ω)) → (∀ x, δ * ψ x ≤ -T + 1 → x ∈ Ω) → wint n X.z (fun x => (θ (δ * ψ x) : ℂ) * G x) (fun x => φ x + ψ x) < ⊤ → ∃ F : M → ℂ, Holo n X.z F ∧ ∫⁻ x, ENNReal.ofReal (‖(θ (δ * ψ x) : ℂ) * G x - F x‖ ^ 2 * (wT T (δ * ψ x) * Real.exp (-(φ x + ψ x)))) ∂vol n X.z ≤ 30 * ∫⁻ x in {x | -T - 1 ≤ δ * ψ x ∧ δ * ψ x ≤ -T + 1}, ENNReal.ofReal (‖G x‖ ^ 2 * Real.exp (-(φ x + ψ x))) ∂vol n X.z := by
  first | exact @GlobalTheory.twistedExtension_sqInt | exact GlobalTheory.twistedExtension_sqInt | (intros; apply GlobalTheory.twistedExtension_sqInt <;> assumption)
end
