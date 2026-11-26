module

public import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.HoloWeakStatement

@[expose] public section

section -- merged from ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.ExtCutB
section -- merged from ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.ExtCutA
namespace ReciprocityTheory.L2DbarEstimates.C

open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal

noncomputable section

def cutL (ε s : ℝ) : ℝ := Real.log (s + ε) - Real.log ε

def cutP (ε s : ℝ) : ℝ := cutL ε s ^ 2 / 2

def halfLogRatioSqDeriv (ε s : ℝ) : ℝ := cutL ε s / (s + ε)

def halfLogRatioSqSecondDeriv (ε s : ℝ) : ℝ := (1 - cutL ε s) / (s + ε) ^ 2

lemma hasDerivAt_cutL {ε s : ℝ} (h : 0 < s + ε) : HasDerivAt (cutL ε) (s + ε)⁻¹ s := by
  have h1 := (((hasDerivAt_id s).add_const ε).log h.ne').sub_const (Real.log ε)
  show HasDerivAt (fun s => Real.log (s + ε) - Real.log ε) _ s
  simpa [one_div] using h1

lemma hasDerivAt_cutP {ε s : ℝ} (h : 0 < s + ε) : HasDerivAt (cutP ε) (halfLogRatioSqDeriv ε s) s := by
  have h1 := ((hasDerivAt_cutL h).pow 2).div_const 2
  show HasDerivAt (fun s => cutL ε s ^ 2 / 2) _ s
  refine h1.congr_deriv ?_
  unfold halfLogRatioSqDeriv
  field_simp
  ring

lemma hasDerivAt_halfLogRatioSqDeriv {ε s : ℝ} (h : 0 < s + ε) : HasDerivAt (halfLogRatioSqDeriv ε) (halfLogRatioSqSecondDeriv ε s) s := by
  have h1 := (hasDerivAt_cutL h).div ((hasDerivAt_id s).add_const ε) h.ne'
  show HasDerivAt (fun s => cutL ε s / (s + ε)) _ s
  refine h1.congr_deriv ?_
  unfold halfLogRatioSqSecondDeriv
  simp only [id]
  field_simp

lemma cutL_nonneg {ε s : ℝ} (hε : 0 < ε) (hs : 0 ≤ s) : 0 ≤ cutL ε s := by
  unfold cutL
  exact sub_nonneg.2 (Real.log_le_log hε (by linarith))

lemma cutL_mono {ε s t : ℝ} (hε : 0 < ε) (hs : 0 ≤ s) (hst : s ≤ t) : cutL ε s ≤ cutL ε t := by
  unfold cutL
  exact sub_le_sub_right (Real.log_le_log (by linarith) (by linarith)) _

lemma polydiscCutoff_nonneg (ε s : ℝ) : 0 ≤ cutP ε s := by
  unfold cutP
  positivity

lemma cutP_mono {ε s t : ℝ} (hε : 0 < ε) (hs : 0 ≤ s) (hst : s ≤ t) : cutP ε s ≤ cutP ε t := by
  unfold cutP
  nlinarith [cutL_nonneg hε hs, cutL_mono hε hs hst]

lemma cut_rho_eq {ε s : ℝ} (h : 0 < s + ε) :
    s * halfLogRatioSqSecondDeriv ε s + halfLogRatioSqDeriv ε s = (s + ε * cutL ε s) / (s + ε) ^ 2 := by
  unfold halfLogRatioSqSecondDeriv halfLogRatioSqDeriv
  field_simp
  ring

lemma cut_rho_nonneg {ε s : ℝ} (hε : 0 < ε) (hs : 0 ≤ s) : 0 ≤ s * halfLogRatioSqSecondDeriv ε s + halfLogRatioSqDeriv ε s := by
  rw [cut_rho_eq (by linarith)]
  exact div_nonneg (add_nonneg hs (mul_nonneg hε.le (cutL_nonneg hε hs))) (by positivity)

lemma cut_rho_ge {ε s : ℝ} (hε : 0 < ε) (hs : ε ≤ s) :
    s⁻¹ ≤ 4 * (s * halfLogRatioSqSecondDeriv ε s + halfLogRatioSqDeriv ε s) := by
  have hs0 : 0 < s := lt_of_lt_of_le hε hs
  have hL := cutL_nonneg hε hs0.le
  rw [cut_rho_eq (by linarith), inv_eq_one_div, mul_div_assoc', div_le_div_iff₀ hs0 (by positivity)]
  nlinarith [mul_nonneg (sub_nonneg.2 hs) (by linarith : (0 : ℝ) ≤ 3 * s + ε),
    mul_nonneg hs0.le (mul_nonneg hε.le hL)]

lemma cutP_le {k m : ℝ} (hk : 1 ≤ k) (hm : 0 ≤ m) :
    cutP (Real.exp (-2 * k)) m ≤ (m + 2) ^ 2 / 2 * k ^ 2 := by
  have hε : 0 < Real.exp (-2 * k) := Real.exp_pos _
  have hε1 : Real.exp (-2 * k) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hLe : cutL (Real.exp (-2 * k)) m = Real.log (m + Real.exp (-2 * k)) + 2 * k := by
    unfold cutL
    rw [Real.log_exp]
    ring
  have hlog : Real.log (m + Real.exp (-2 * k)) ≤ m + Real.exp (-2 * k) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have hL0 := cutL_nonneg hε hm
  have hLup : cutL (Real.exp (-2 * k)) m ≤ (m + 2) * k := by
    rw [hLe]
    nlinarith
  unfold cutP
  nlinarith [mul_le_mul hLup hLup hL0 (by positivity : (0 : ℝ) ≤ (m + 2) * k)]

lemma continuousAt_cutP {ε s : ℝ} (h : 0 < s + ε) : ContinuousAt (cutP ε) s :=
  (hasDerivAt_cutP h).continuousAt

lemma continuousAt_halfLogRatioSqDeriv {ε s : ℝ} (h : 0 < s + ε) : ContinuousAt (halfLogRatioSqDeriv ε) s :=
  (hasDerivAt_halfLogRatioSqDeriv h).continuousAt

lemma continuousAt_halfLogRatioSqSecondDeriv {ε s : ℝ} (h : 0 < s + ε) : ContinuousAt (halfLogRatioSqSecondDeriv ε) s := by
  show ContinuousAt (fun s => (1 - cutL ε s) / (s + ε) ^ 2) s
  exact (continuousAt_const.sub (hasDerivAt_cutL h).continuousAt).div (by fun_prop)
    (pow_ne_zero 2 h.ne')

variable {n : ℕ}

def complexLineSecondDeriv (F : V n → ℂ) (z e : V n) : ℂ := deriv (deriv (fun l : ℂ => F (z + l • e))) 0

lemma real_smul_smul (t : ℝ) (μ : ℂ) (e : V n) : t • (μ • e) = ((t : ℂ) * μ) • e := by
  rw [← Complex.coe_smul, smul_smul]

lemma deriv_slice {Ω : Set (V n)} {F : V n → ℂ} (hΩ : IsOpen Ω) (hF : DifferentiableOn ℂ F Ω)
    {z e : V n} {l : ℂ} (hw : z + l • e ∈ Ω) :
    deriv (fun m : ℂ => F (z + m • e)) l = fderiv ℂ F (z + l • e) e := by
  have hd : DifferentiableAt ℂ F (z + l • e) := hF.differentiableAt (hΩ.mem_nhds hw)
  have hl : HasDerivAt (fun m : ℂ => z + m • e) e l := by
    simpa using ((hasDerivAt_id l).smul_const e).const_add z
  exact (hd.hasFDerivAt.comp_hasDerivAt l hl).deriv

lemma hasDerivAt_line {Ω : Set (V n)} {F : V n → ℂ} (hΩ : IsOpen Ω) (hF : DifferentiableOn ℂ F Ω)
    {z : V n} (hz : z ∈ Ω) (e : V n) (μ : ℂ) :
    HasDerivAt (fun t : ℝ => F (z + t • (μ • e))) (fderiv ℂ F z e * μ) 0 := by
  have hd : DifferentiableAt ℂ F z := hF.differentiableAt (hΩ.mem_nhds hz)
  have hl : HasDerivAt (fun t : ℝ => z + t • (μ • e)) ((1 : ℝ) • (μ • e)) 0 :=
    ((hasDerivAt_id (0 : ℝ)).smul_const (μ • e)).const_add z
  have h1 := (hd.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  refine h1.congr_deriv ?_
  rw [one_smul, ContinuousLinearMap.coe_restrictScalars', map_smul, smul_eq_mul, mul_comm]

lemma hasDerivAt_realLine_fderiv {Ω : Set (V n)} {F : V n → ℂ} (hΩ : IsOpen Ω)
    (hF : DifferentiableOn ℂ F Ω) {z : V n} (hz : z ∈ Ω) (e : V n) (μ : ℂ) :
    HasDerivAt (fun t : ℝ => fderiv ℂ F (z + t • (μ • e)) e) (complexLineSecondDeriv F z e * μ) 0 := by
  have hU : IsOpen {l : ℂ | z + l • e ∈ Ω} := hΩ.preimage (by fun_prop)
  have h0 : (0 : ℂ) ∈ {l : ℂ | z + l • e ∈ Ω} := by simpa using hz
  have hg : DifferentiableOn ℂ (fun l : ℂ => F (z + l • e)) {l : ℂ | z + l • e ∈ Ω} :=
    hF.comp (by fun_prop) (fun l hl => hl)
  have hg' := hg.deriv hU

  have hder : HasDerivAt (deriv fun l : ℂ => F (z + l • e)) (complexLineSecondDeriv F z e) (((0 : ℝ) : ℂ) * μ) := by
    have h1 := ((hg' 0 h0).differentiableAt (hU.mem_nhds h0)).hasDerivAt
    simpa [complexLineSecondDeriv] using h1
  have hc : HasDerivAt (fun t : ℝ => (t : ℂ) * μ) μ 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).ofReal_comp).mul_const μ
  have hcomp := hder.comp (0 : ℝ) hc
  refine hcomp.congr_of_eventuallyEq ?_
  have h0' : ((0 : ℝ) : ℂ) * μ ∈ {l : ℂ | z + l • e ∈ Ω} := by simpa using hz
  filter_upwards [hc.continuousAt.preimage_mem_nhds (hU.mem_nhds h0')] with t ht
  show fderiv ℂ F (z + t • (μ • e)) e = deriv (fun l : ℂ => F (z + l • e)) ((t : ℂ) * μ)
  rw [real_smul_smul]
  exact (deriv_slice hΩ hF ht).symm

lemma cauchy_deriv_le {g : ℂ → ℂ} {c : ℂ} {R M : ℝ} (hR : 0 < R)
    (hg : DifferentiableOn ℂ g (closedBall c R)) (hM : ∀ w ∈ closedBall c R, ‖g w‖ ≤ M) :
    ‖deriv g c‖ ≤ M / R := by
  have hd : DiffContOnCl ℂ g (ball c R) :=
    ⟨hg.mono ball_subset_closedBall, by rw [closure_ball c hR.ne']; exact hg.continuousOn⟩
  exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR hd
    (fun w hw => hM w (sphere_subset_closedBall hw))

lemma cauchy_line {Ω : Set (V n)} {F : V n → ℂ} (hΩ : IsOpen Ω) (hF : DifferentiableOn ℂ F Ω)
    {z e : V n} (he : ‖e‖ = 1) {r M : ℝ} (hr : 0 < r) (hsub : closedBall z r ⊆ Ω)
    (hM : ∀ w ∈ closedBall z r, ‖F w‖ ≤ M) :
    ‖fderiv ℂ F z e‖ ≤ M / r ∧ ‖complexLineSecondDeriv F z e‖ ≤ 4 * M / r ^ 2 := by
  have hU : IsOpen {l : ℂ | z + l • e ∈ Ω} := hΩ.preimage (by fun_prop)
  have hg : DifferentiableOn ℂ (fun l : ℂ => F (z + l • e)) {l : ℂ | z + l • e ∈ Ω} :=
    hF.comp (by fun_prop) (fun l hl => hl)
  have hball : ∀ l ∈ closedBall (0 : ℂ) r, z + l • e ∈ closedBall z r := by
    intro l hl
    rw [mem_closedBall, dist_eq_norm] at hl ⊢
    simpa [norm_smul, he] using hl
  have hsubU : closedBall (0 : ℂ) r ⊆ {l : ℂ | z + l • e ∈ Ω} := fun l hl => hsub (hball l hl)
  have hM' : ∀ l ∈ closedBall (0 : ℂ) r, ‖F (z + l • e)‖ ≤ M := fun l hl => hM _ (hball l hl)
  have hd0 : deriv (fun l : ℂ => F (z + l • e)) 0 = fderiv ℂ F z e := by
    have h1 := deriv_slice hΩ hF (z := z) (e := e) (l := 0)
      (by simpa using hsub (mem_closedBall_self hr.le))
    simpa using h1
  refine ⟨?_, ?_⟩
  · rw [← hd0]
    exact cauchy_deriv_le hr (hg.mono hsubU) hM'
  · have hr2 : 0 < r / 2 := by positivity

    have hb2 : ∀ w ∈ closedBall (0 : ℂ) (r / 2),
        ‖deriv (fun l : ℂ => F (z + l • e)) w‖ ≤ M / (r / 2) := by
      intro w hw
      have hsub2 : closedBall w (r / 2) ⊆ closedBall (0 : ℂ) r := by
        intro l hl
        rw [mem_closedBall] at hl hw ⊢
        calc dist l 0 ≤ dist l w + dist w 0 := dist_triangle _ _ _
          _ ≤ r / 2 + r / 2 := add_le_add hl hw
          _ = r := by ring
      exact cauchy_deriv_le hr2 ((hg.mono hsubU).mono hsub2) (fun l hl => hM' l (hsub2 hl))
    have hdd := cauchy_deriv_le hr2 ((hg.deriv hU).mono
      (fun l hl => hsubU (closedBall_subset_closedBall (by linarith) hl))) hb2
    show ‖deriv (deriv fun l : ℂ => F (z + l • e)) 0‖ ≤ 4 * M / r ^ 2
    calc ‖deriv (deriv fun l : ℂ => F (z + l • e)) 0‖ ≤ M / (r / 2) / (r / 2) := hdd
      _ = 4 * M / r ^ 2 := by field_simp; ring

lemma measurable_mul_complexLineSecondDeriv {Ω : Set (V n)} {F : V n → ℂ} (hΩ : IsOpen Ω)
    (hF : DifferentiableOn ℂ F Ω) (e : V n) {χ : V n → ℂ} (hχ : Measurable χ)
    (hχΩ : ∀ z, χ z ≠ 0 → z ∈ Ω) : Measurable (fun z => χ z * complexLineSecondDeriv F z e) := by

  have hΦ : Measurable (fun w => fderiv ℂ F w e) := measurable_fderiv_apply_const ℂ F e
  have hu0 : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun k => Set.mem_compl_singleton_iff.2 (by positivity)⟩
  refine measurable_of_tendsto_metrizable
    (f := fun (k : ℕ) z => χ z * ((1 / ((k : ℝ) + 1))⁻¹ •
      (fderiv ℂ F (z + (1 / ((k : ℝ) + 1)) • ((1 : ℂ) • e)) e - fderiv ℂ F z e)))
    (fun k => ?_) (tendsto_pi_nhds.2 fun z => ?_)
  · refine hχ.mul ?_
    have hm := ((hΦ.comp (measurable_add_const ((1 / ((k : ℝ) + 1)) • ((1 : ℂ) • e)))).sub hΦ).const_smul
      ((1 / ((k : ℝ) + 1))⁻¹)
    exact hm
  · by_cases hz : χ z = 0
    · simp only [hz, zero_mul]
      exact tendsto_const_nhds
    · have hd := hasDerivAt_realLine_fderiv hΩ hF (hχΩ z hz) e 1
      have hs := (hd.tendsto_slope_zero.comp hu0).const_mul (χ z)
      simpa using hs

end

end ReciprocityTheory.L2DbarEstimates.C
end

namespace ReciprocityTheory.L2DbarEstimates.C

open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal

noncomputable section

variable {n : ℕ}

def lineFirstVariation (ε : ℝ) (x y : ℂ) : ℝ := halfLogRatioSqDeriv ε (‖x‖ ^ 2) * (2 * inner ℝ x y)

def lineSecondVariation (ε : ℝ) (x y w : ℂ) : ℝ :=
  halfLogRatioSqSecondDeriv ε (‖x‖ ^ 2) * (2 * inner ℝ x y) * (2 * inner ℝ x y) +
    halfLogRatioSqDeriv ε (‖x‖ ^ 2) * (2 * (inner ℝ x w + inner ℝ y y))

lemma lineSecondVariation_add_I (ε : ℝ) (x a S : ℂ) :
    lineSecondVariation ε x (a * 1) (S * 1 * 1) + lineSecondVariation ε x (a * I) (S * I * I) =
      4 * ‖a‖ ^ 2 * (‖x‖ ^ 2 * halfLogRatioSqSecondDeriv ε (‖x‖ ^ 2) + halfLogRatioSqDeriv ε (‖x‖ ^ 2)) := by
  have hi : ∀ u v : ℂ, inner ℝ u v = u.re * v.re + u.im * v.im := by
    intro u v
    first
    | (rw [Complex.inner]; simp; ring)
    | (simp [Complex.inner_def]; ring)
    | (rw [Complex.real_inner_eq_re_inner]; simp; ring)
  unfold lineSecondVariation
  simp only [hi, Complex.mul_re, Complex.mul_im, Complex.one_re, Complex.one_im, Complex.I_re,
    Complex.I_im]
  rw [Complex.sq_norm a, Complex.sq_norm x, Complex.normSq_apply, Complex.normSq_apply]
  ring

lemma hasLineDerivAt_halfLogRatioSq_comp {Ω : Set (V n)} {F : V n → ℂ} (hΩ : IsOpen Ω)
    (hF : DifferentiableOn ℂ F Ω) {z : V n} (hz : z ∈ Ω) {ε : ℝ} (hε : 0 < ε) (e : V n)
    (μ : ℂ) :
    HasLineDerivAt ℝ (fun w => cutP ε (‖F w‖ ^ 2)) (lineFirstVariation ε (F z) (fderiv ℂ F z e * μ)) z
      (μ • e) := by
  have hs : 0 < ‖F z‖ ^ 2 + ε := by positivity
  have hFd : HasFDerivAt F (fderiv ℂ F z) z :=
    (hF.differentiableAt (hΩ.mem_nhds hz)).hasFDerivAt
  have hFR := hFd.restrictScalars ℝ
  have hN := hFR.norm_sq
  have hC := (hasDerivAt_cutP hs).comp_hasFDerivAt z hN
  have hL := hC.hasLineDerivAt (μ • e)
  refine HasDerivAt.congr_deriv hL ?_
  simp only [lineFirstVariation, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', innerSL_apply_apply, map_smul, smul_eq_mul,
    nsmul_eq_mul, Nat.cast_ofNat]
  ring

lemma hasLineDerivAt_lineFirstVariation {Ω : Set (V n)} {F : V n → ℂ} (hΩ : IsOpen Ω)
    (hF : DifferentiableOn ℂ F Ω) {z : V n} (hz : z ∈ Ω) {ε : ℝ} (hε : 0 < ε) (e : V n)
    (μ : ℂ) :
    HasLineDerivAt ℝ (fun w => lineFirstVariation ε (F w) (fderiv ℂ F w e * μ))
      (lineSecondVariation ε (F z) (fderiv ℂ F z e * μ) (complexLineSecondDeriv F z e * μ * μ)) z (μ • e) := by
  have hp := hasDerivAt_line hΩ hF hz e μ
  have hq := (hasDerivAt_realLine_fderiv hΩ hF hz e μ).mul_const μ
  have hs : HasDerivAt (fun t : ℝ => ‖F (z + t • (μ • e))‖ ^ 2)
      (2 * inner ℝ (F z) (fderiv ℂ F z e * μ)) 0 := by
    simpa using hp.norm_sq
  have h1' : HasDerivAt (halfLogRatioSqDeriv ε) (halfLogRatioSqSecondDeriv ε (‖F z‖ ^ 2))
      ((fun t : ℝ => ‖F (z + t • (μ • e))‖ ^ 2) 0) := by
    simpa using hasDerivAt_halfLogRatioSqDeriv (ε := ε) (s := ‖F z‖ ^ 2) (by positivity)
  have h1 := h1'.comp 0 hs
  have h2 := (hp.inner (𝕜 := ℝ) hq).const_mul 2
  show HasDerivAt (fun t : ℝ => halfLogRatioSqDeriv ε (‖F (z + t • (μ • e))‖ ^ 2) *
    (2 * inner ℝ (F (z + t • (μ • e))) (fderiv ℂ F (z + t • (μ • e)) e * μ))) _ 0
  refine (h1.mul h2).congr_deriv ?_
  simp only [zero_smul, add_zero, Function.comp_apply]
  unfold lineSecondVariation
  ring

lemma integrable_of_bounded_of_isCompact {T : Set (V n)} (hT : IsCompact T) {h : V n → ℝ}
    (hm : AEStronglyMeasurable h (volume.restrict T)) {C : ℝ} (hb : ∀ z ∈ T, ‖h z‖ ≤ C)
    (h0 : ∀ z ∉ T, h z = 0) : Integrable h := by
  have hTm : MeasurableSet T := hT.isClosed.measurableSet
  haveI : IsFiniteMeasure (volume.restrict T) := isFiniteMeasure_restrict.2 hT.measure_lt_top.ne
  have hb' : ∀ᵐ z ∂(volume.restrict T), ‖h z‖ ≤ C :=
    (ae_restrict_iff' hTm).2 (Filter.Eventually.of_forall hb)
  have hon : IntegrableOn h T := by
    first
    | exact Integrable.of_bound hm C hb'
    | exact Integrable.of_bound hm hb'
    | exact Measure.integrableOn_of_bounded (M := C) hT.measure_lt_top.ne hm hb'
  have he : h = T.indicator h := by
    funext z
    by_cases hz : z ∈ T
    · simp [hz]
    · simp [hz, h0 z hz]
  rw [he]
  exact (integrable_indicator_iff hTm).2 hon

lemma continuousOn_cutComp {T : Set (V n)} {F : V n → ℂ} (hFc : ContinuousOn F T) {g : ℝ → ℝ}
    (hg : ∀ s, 0 ≤ s → ContinuousAt g s) : ContinuousOn (fun z => g (‖F z‖ ^ 2)) T := by
  intro z hz
  have h1 : ContinuousWithinAt (fun z => ‖F z‖ ^ 2) T z := ((hFc z hz).norm).pow 2
  exact (hg _ (by positivity)).comp_continuousWithinAt h1

lemma abs_mul_two_mul_le {p x c X : ℝ} (hp : |p| ≤ c) (hx : |x| ≤ X) : |p * (2 * x)| ≤ c * (2 * X) := by
  have hx2 : 2 * |x| ≤ 2 * X := by linarith
  calc |p * (2 * x)| = |p| * (2 * |x|) := by rw [abs_mul, abs_mul, abs_two]
    _ ≤ c * (2 * X) := mul_le_mul hp hx2 (by positivity) ((abs_nonneg p).trans hp)

lemma abs_second_variation_le {p1 p2 x y z c1 c2 X Y Z : ℝ} (h1 : |p1| ≤ c1) (h2 : |p2| ≤ c2) (hx : |x| ≤ X)
    (hy : |y| ≤ Y) (hz : |z| ≤ Z) :
    |p2 * (2 * x) * (2 * x) + p1 * (2 * (y + z))| ≤ c2 * (2 * X) * (2 * X) + c1 * (2 * (Y + Z)) := by
  have hX : 0 ≤ X := (abs_nonneg x).trans hx
  have hc2 : 0 ≤ c2 := (abs_nonneg _).trans h2
  have hc1 : 0 ≤ c1 := (abs_nonneg _).trans h1
  have hx2 : 2 * |x| ≤ 2 * X := by linarith
  have hA : |p2 * (2 * x) * (2 * x)| ≤ c2 * (2 * X) * (2 * X) := by
    rw [abs_mul, abs_mul, abs_mul, abs_two]
    exact mul_le_mul (mul_le_mul h2 hx2 (by positivity) hc2) hx2 (by positivity)
      (mul_nonneg hc2 (by linarith))
  have hyz : |y + z| ≤ Y + Z := (abs_add_le _ _).trans (add_le_add hy hz)
  have hB : |p1 * (2 * (y + z))| ≤ c1 * (2 * (Y + Z)) := by
    rw [abs_mul, abs_mul, abs_two]
    exact mul_le_mul h1 (by linarith) (by positivity) hc1
  exact (abs_add_le _ _).trans (add_le_add hA hB)

theorem green_dir {Ω : Set (V n)} {F : V n → ℂ} (hΩ : IsOpen Ω) (hF : DifferentiableOn ℂ F Ω)
    {T : Set (V n)} (hT : IsCompact T) (hTΩ : T ⊆ Ω) {ψ : V n → ℝ} (hψ : ContDiff ℝ 2 ψ)
    (hψT : tsupport ψ ⊆ T) {ε : ℝ} (hε : 0 < ε) (e : V n) (μ : ℂ) (hμ : ‖μ‖ = 1)
    {M A B : ℝ} (hM : ∀ z ∈ T, ‖F z‖ ≤ M) (hA : ∀ z ∈ T, ‖fderiv ℂ F z e‖ ≤ A)
    (hB : ∀ z ∈ T, ‖complexLineSecondDeriv F z e‖ ≤ B) :
    Integrable (fun z => ψ z * lineSecondVariation ε (F z) (fderiv ℂ F z e * μ) (complexLineSecondDeriv F z e * μ * μ)) ∧
    Integrable (fun z => fderiv ℝ (fun w => fderiv ℝ ψ w (μ • e)) z (μ • e) *
      cutP ε (‖F z‖ ^ 2)) ∧
    Integrable (fun z => fderiv ℝ (fun w => fderiv ℝ ψ w (μ • e)) z (μ • e)) ∧
    (∀ z ∉ T, fderiv ℝ (fun w => fderiv ℝ ψ w (μ • e)) z (μ • e) = 0) ∧
    ∫ z, ψ z * lineSecondVariation ε (F z) (fderiv ℂ F z e * μ) (complexLineSecondDeriv F z e * μ * μ) =
      ∫ z, fderiv ℝ (fun w => fderiv ℝ ψ w (μ • e)) z (μ • e) * cutP ε (‖F z‖ ^ 2) := by
  set v : V n := μ • e with hv
  set D1 : V n → ℝ := fun w => fderiv ℝ ψ w v with hD1
  set D2 : V n → ℝ := fun w => fderiv ℝ D1 w v with hD2
  have hψd : Differentiable ℝ ψ := hψ.differentiable (by norm_num)
  have hD1c : ContDiff ℝ 1 D1 :=
    (hψ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hD1d : Differentiable ℝ D1 := hD1c.differentiable (by norm_num)
  have hD2c : Continuous D2 := (hD1c.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hsD1 : tsupport D1 ⊆ T := by
    have : tsupport D1 ⊆ tsupport (fderiv ℝ ψ) :=
      tsupport_comp_subset (g := fun L : V n →L[ℝ] ℝ => L v) (by simp) _
    exact this.trans ((tsupport_fderiv_subset ℝ).trans hψT)
  have hsD2 : tsupport D2 ⊆ T := by
    have : tsupport D2 ⊆ tsupport (fderiv ℝ D1) :=
      tsupport_comp_subset (g := fun L : V n →L[ℝ] ℝ => L v) (by simp) _
    exact this.trans ((tsupport_fderiv_subset ℝ).trans hsD1)
  have z0 : ∀ {w : V n → ℝ}, tsupport w ⊆ T → ∀ z ∉ T, w z = 0 :=
    fun hw z hz => image_eq_zero_of_notMem_tsupport (fun h => hz (hw h))
  have hFc : ContinuousOn F T := hF.continuousOn.mono hTΩ
  have hTm := hT.measurableSet
  have mF : AEStronglyMeasurable F (volume.restrict T) := hFc.aestronglyMeasurable hTm
  have ma : AEStronglyMeasurable (fun z => fderiv ℂ F z e * μ) (volume.restrict T) :=
    ((measurable_fderiv_apply_const ℂ F e).mul_const μ).aestronglyMeasurable
  have cP : ContinuousOn (fun z => cutP ε (‖F z‖ ^ 2)) T :=
    continuousOn_cutComp hFc (fun s hs => continuousAt_cutP (by linarith))
  have cP1 : ContinuousOn (fun z => halfLogRatioSqDeriv ε (‖F z‖ ^ 2)) T :=
    continuousOn_cutComp hFc (fun s hs => continuousAt_halfLogRatioSqDeriv (by linarith))
  have cP2 : ContinuousOn (fun z => halfLogRatioSqSecondDeriv ε (‖F z‖ ^ 2)) T :=
    continuousOn_cutComp hFc (fun s hs => continuousAt_halfLogRatioSqSecondDeriv (by linarith))
  obtain ⟨c0, hc0⟩ := hT.exists_bound_of_continuousOn cP
  obtain ⟨c1, hc1⟩ := hT.exists_bound_of_continuousOn cP1
  obtain ⟨c2, hc2⟩ := hT.exists_bound_of_continuousOn cP2
  have hin : ∀ z ∈ T, |inner ℝ (F z) (fderiv ℂ F z e * μ)| ≤ M * A := fun z hz => by
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [norm_mul, hμ, mul_one]
    exact mul_le_mul (hM z hz) (hA z hz) (norm_nonneg _) ((norm_nonneg _).trans (hM z hz))
  have hinS : ∀ z ∈ T, |inner ℝ (F z) (complexLineSecondDeriv F z e * μ * μ)| ≤ M * B := fun z hz => by
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [norm_mul, norm_mul, hμ, mul_one, mul_one]
    exact mul_le_mul (hM z hz) (hB z hz) (norm_nonneg _) ((norm_nonneg _).trans (hM z hz))
  have hinA : ∀ z ∈ T, |inner ℝ (fderiv ℂ F z e * μ) (fderiv ℂ F z e * μ)| ≤ A * A :=
    fun z hz => by
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [norm_mul, hμ, mul_one]
    exact mul_le_mul (hA z hz) (hA z hz) (norm_nonneg _) ((norm_nonneg _).trans (hA z hz))

  have intP : ∀ w : V n → ℝ, Continuous w → tsupport w ⊆ T →
      Integrable (fun z => w z * cutP ε (‖F z‖ ^ 2)) := by
    intro w hw hwT
    obtain ⟨bw, hbw⟩ := hT.exists_bound_of_continuousOn hw.continuousOn
    refine integrable_of_bounded_of_isCompact hT (hw.aestronglyMeasurable.mul (cP.aestronglyMeasurable hTm))
      (C := bw * c0) (fun z hz => ?_) (fun z hz => by simp [z0 hwT z hz])
    rw [norm_mul]
    exact mul_le_mul (hbw z hz) (hc0 z hz) (norm_nonneg _) ((norm_nonneg _).trans (hbw z hz))
  have intQ1 : ∀ w : V n → ℝ, Continuous w → tsupport w ⊆ T →
      Integrable (fun z => w z * lineFirstVariation ε (F z) (fderiv ℂ F z e * μ)) := by
    intro w hw hwT
    obtain ⟨bw, hbw⟩ := hT.exists_bound_of_continuousOn hw.continuousOn
    refine integrable_of_bounded_of_isCompact hT ?_ (C := bw * (c1 * (2 * (M * A)))) (fun z hz => ?_)
      (fun z hz => by simp [z0 hwT z hz])
    · unfold lineFirstVariation
      exact hw.aestronglyMeasurable.mul ((cP1.aestronglyMeasurable hTm).mul
        (aestronglyMeasurable_const.mul (mF.inner ma)))
    · rw [norm_mul]
      refine mul_le_mul (hbw z hz) ?_ (norm_nonneg _) ((norm_nonneg _).trans (hbw z hz))
      rw [Real.norm_eq_abs]
      exact abs_mul_two_mul_le (by simpa [Real.norm_eq_abs] using hc1 z hz) (hin z hz)
  have intQ2 : ∀ w : V n → ℝ, Continuous w → tsupport w ⊆ T →
      Integrable (fun z => w z * lineSecondVariation ε (F z) (fderiv ℂ F z e * μ) (complexLineSecondDeriv F z e * μ * μ)) := by
    intro w hw hwT
    obtain ⟨bw, hbw⟩ := hT.exists_bound_of_continuousOn hw.continuousOn
    have hid : (fun z => w z * lineSecondVariation ε (F z) (fderiv ℂ F z e * μ) (complexLineSecondDeriv F z e * μ * μ)) =
        fun z => (w z * (halfLogRatioSqSecondDeriv ε (‖F z‖ ^ 2) * (2 * inner ℝ (F z) (fderiv ℂ F z e * μ)) *
          (2 * inner ℝ (F z) (fderiv ℂ F z e * μ))) + w z * (halfLogRatioSqDeriv ε (‖F z‖ ^ 2) *
          (2 * inner ℝ (fderiv ℂ F z e * μ) (fderiv ℂ F z e * μ)))) +
          (((halfLogRatioSqDeriv ε (‖F z‖ ^ 2) * 2 : ℝ) : ℂ) * (μ * μ * (starRingEnd ℂ) (F z)) *
            (((w z : ℝ) : ℂ) * complexLineSecondDeriv F z e)).re := by
      funext z
      unfold lineSecondVariation
      simp only [Complex.inner, mul_re, mul_im, ofReal_re, ofReal_im, conj_re, conj_im]
      ring
    have hS : Measurable (fun z => ((w z : ℝ) : ℂ) * complexLineSecondDeriv F z e) :=
      measurable_mul_complexLineSecondDeriv hΩ hF e (Complex.measurable_ofReal.comp hw.measurable)
        (fun z hz => by
          by_contra h
          exact hz (by simp [z0 hwT z (fun h' => h (hTΩ h'))]))
    have cX : ContinuousOn (fun z => ((halfLogRatioSqDeriv ε (‖F z‖ ^ 2) * 2 : ℝ) : ℂ) *
        (μ * μ * (starRingEnd ℂ) (F z))) T :=
      (Complex.continuous_ofReal.comp_continuousOn (cP1.mul continuousOn_const)).mul
        (continuousOn_const.mul (Complex.continuous_conj.comp_continuousOn hFc))
    refine integrable_of_bounded_of_isCompact hT ?_ (C := bw * (c2 * (2 * (M * A)) * (2 * (M * A)) +
      c1 * (2 * (M * B + A * A)))) (fun z hz => ?_) (fun z hz => by simp [z0 hwT z hz])
    · rw [hid]
      refine ((hw.aestronglyMeasurable.mul (((cP2.aestronglyMeasurable hTm).mul
        (aestronglyMeasurable_const.mul (mF.inner ma))).mul
        (aestronglyMeasurable_const.mul (mF.inner ma)))).add
        (hw.aestronglyMeasurable.mul ((cP1.aestronglyMeasurable hTm).mul
        (aestronglyMeasurable_const.mul (ma.inner ma))))).add ?_
      exact Complex.continuous_re.comp_aestronglyMeasurable
        ((cX.aestronglyMeasurable hTm).mul hS.aestronglyMeasurable)
    · rw [norm_mul]
      refine mul_le_mul (hbw z hz) ?_ (norm_nonneg _) ((norm_nonneg _).trans (hbw z hz))
      rw [Real.norm_eq_abs]
      unfold lineSecondVariation
      exact abs_second_variation_le (by simpa [Real.norm_eq_abs] using hc1 z hz)
        (by simpa [Real.norm_eq_abs] using hc2 z hz) (hin z hz) (hinS z hz) (hinA z hz)
  refine ⟨intQ2 ψ hψd.continuous hψT, intP D2 hD2c hsD2,
    hD2c.integrable_of_hasCompactSupport (IsCompact.of_isClosed_subset hT (isClosed_tsupport _) hsD2),
    z0 hsD2, ?_⟩

  have ibp1 := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable (μ := volume)
    (B := ContinuousLinearMap.mul ℝ ℝ) (f := ψ) (f' := D1)
    (g := fun w => lineFirstVariation ε (F w) (fderiv ℂ F w e * μ))
    (g' := fun z => lineSecondVariation ε (F z) (fderiv ℂ F z e * μ) (complexLineSecondDeriv F z e * μ * μ)) (v := v)
    (by simpa using intQ1 D1 hD1d.continuous hsD1)
    (by simpa using intQ2 ψ hψd.continuous hψT)
    (by simpa using intQ1 ψ hψd.continuous hψT)
    (fun x _ => (hψd x).hasFDerivAt.hasLineDerivAt v)
    (fun x hx => hasLineDerivAt_lineFirstVariation hΩ hF (hTΩ (hψT hx)) hε e μ)
  have ibp2 := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable (μ := volume)
    (B := ContinuousLinearMap.mul ℝ ℝ) (f := D1) (f' := D2)
    (g := fun w => cutP ε (‖F w‖ ^ 2))
    (g' := fun w => lineFirstVariation ε (F w) (fderiv ℂ F w e * μ)) (v := v)
    (by simpa using intP D2 hD2c hsD2)
    (by simpa using intQ1 D1 hD1d.continuous hsD1)
    (by simpa using intP D1 hD1d.continuous hsD1)
    (fun x _ => (hD1d x).hasFDerivAt.hasLineDerivAt v)
    (fun x hx => hasLineDerivAt_halfLogRatioSq_comp hΩ hF (hTΩ (hsD1 hx)) hε e μ)
  simp only [ContinuousLinearMap.mul_apply'] at ibp1 ibp2
  rw [ibp1, ibp2, neg_neg]

end

end ReciprocityTheory.L2DbarEstimates.C
end

namespace ReciprocityTheory.L2DbarEstimates.C

open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal Manifold

noncomputable section

variable {n : ℕ}

lemma norm_sq_clm (L : V n →L[ℂ] ℂ) :
    ‖L‖ ^ 2 = ∑ j, ‖L (EuclideanSpace.basisFun (Fin n) ℂ j)‖ ^ 2 := by

  set v : V n := (InnerProductSpace.toDual ℂ (V n)).symm L with hv
  have hL : ‖L‖ = ‖v‖ := by
    rw [hv, LinearIsometryEquiv.norm_map]
  have hco : ∀ j, ‖L (EuclideanSpace.basisFun (Fin n) ℂ j)‖ = ‖v j‖ := by
    intro j
    rw [← InnerProductSpace.toDual_symm_apply, ← hv, EuclideanSpace.basisFun_apply,
      EuclideanSpace.inner_single_right]
    simp
  rw [hL, EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp only [hco]

lemma grad_log_sq {Ω : Set (V n)} {F : V n → ℂ} (hΩ : IsOpen Ω) (hF : DifferentiableOn ℂ F Ω)
    {z : V n} (hz : z ∈ Ω) (h0 : F z ≠ 0) :
    ‖fderiv ℝ (fun w => Real.log (‖F w‖ ^ 2)) z‖ ^ 2 ≤
      4 * (∑ j, ‖fderiv ℂ F z (EuclideanSpace.basisFun (Fin n) ℂ j)‖ ^ 2) / ‖F z‖ ^ 2 := by
  have hDa : DifferentiableAt ℂ F z := hF.differentiableAt (hΩ.mem_nhds hz)
  have hpos : 0 < ‖F z‖ := norm_pos_iff.mpr h0
  have h1 : HasFDerivAt F ((fderiv ℂ F z).restrictScalars ℝ) z :=
    hDa.hasFDerivAt.restrictScalars ℝ
  have h2 := h1.norm_sq
  have h3 := h2.log (by positivity)
  rw [← norm_sq_clm, h3.fderiv]
  set D := fderiv ℂ F z

  have hM : ‖(‖F z‖ ^ 2)⁻¹ • (2 • (innerSL ℝ (F z)).comp (D.restrictScalars ℝ))‖ ≤
      2 * ‖D‖ / ‖F z‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
    have hi : |inner ℝ (F z) (D h)| ≤ ‖F z‖ * (‖D‖ * ‖h‖) :=
      (abs_real_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_left (D.le_opNorm h) (norm_nonneg _))
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_restrictScalars', innerSL_apply_apply, nsmul_eq_mul, smul_eq_mul,
      Real.norm_eq_abs, abs_mul, abs_inv, Nat.cast_ofNat]
    rw [abs_of_pos (by positivity : (0:ℝ) < ‖F z‖ ^ 2), abs_two]
    calc (‖F z‖ ^ 2)⁻¹ * (2 * |inner ℝ (F z) (D h)|)
        ≤ (‖F z‖ ^ 2)⁻¹ * (2 * (‖F z‖ * (‖D‖ * ‖h‖))) := by gcongr
      _ = 2 * ‖D‖ / ‖F z‖ * ‖h‖ := by field_simp
  calc _ ≤ (2 * ‖D‖ / ‖F z‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hM 2
    _ = 4 * ‖D‖ ^ 2 / ‖F z‖ ^ 2 := by ring

end

theorem ext_cut {n : ℕ} {Ω : Set (V n)} {F : V n → ℂ} (hΩ : IsOpen Ω)
    (hF : DifferentiableOn ℂ F Ω) {K : Set (V n)} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ k : ℝ, 1 ≤ k →
      ∫⁻ z in K ∩ {z | F z ≠ 0 ∧ k ≤ -Real.log (‖F z‖ ^ 2) ∧ -Real.log (‖F z‖ ^ 2) ≤ 2 * k},
        ‖fderiv ℝ (fun w => Real.log (‖F w‖ ^ 2)) z‖ₑ ^ 2 ≤ C * ENNReal.ofReal (k ^ 2) := by
  classical
  obtain ⟨δ0, hδ0, hδ0Ω⟩ := hK.exists_cthickening_subset_open hΩ hKΩ
  set δ := δ0 / 2 with hδdef
  have hδ : 0 < δ := by positivity
  set T := cthickening δ K with hTdef
  have hT : IsCompact T := hK.cthickening
  have hTΩ : T ⊆ Ω := (cthickening_mono (by linarith) K).trans hδ0Ω
  have hball : ∀ z ∈ T, closedBall z δ ⊆ cthickening δ0 K := fun z hz =>
    (closedBall_subset_cthickening hz δ).trans
      ((cthickening_cthickening_subset hδ.le hδ.le K).trans (by rw [hδdef]; ring_nf; rfl))
  obtain ⟨M0, hM0⟩ := (hK.cthickening (r := δ0)).exists_bound_of_continuousOn
    (hF.continuousOn.mono hδ0Ω)
  set M := max M0 0
  have hM : ∀ z ∈ cthickening δ0 K, ‖F z‖ ≤ M := fun z hz => (hM0 z hz).trans (le_max_left _ _)
  have hM0' : 0 ≤ M := le_max_right _ _

  obtain ⟨f, hf0, hf1, hf01⟩ := exists_contMDiffMap_zero_one_of_isClosed (𝓘(ℝ, V n)) (n := 2)
    (isOpen_thickening (δ := δ) (E := K)).isClosed_compl hK.isClosed
    (disjoint_compl_left_iff_subset.2 (self_subset_thickening hδ K))
  set ψ : V n → ℝ := ⇑f with hψdef
  have hψ : ContDiff ℝ 2 ψ := by
    have := contMDiff_iff_contDiff.1 f.contMDiff
    exact_mod_cast this
  have hψT : tsupport ψ ⊆ T := by
    refine (closure_mono ?_).trans (closure_thickening_subset_cthickening δ K)
    intro x hx
    by_contra h
    exact hx (hf0 h)
  have hψ1 : ∀ z ∈ K, ψ z = 1 := fun z hz => hf1 hz
  have hψ0 : ∀ z, 0 ≤ ψ z := fun z => (hf01 z).1

  set b := EuclideanSpace.basisFun (Fin n) ℂ
  have hb1 : ∀ j, ‖b j‖ = 1 := fun j => b.orthonormal.1 j
  have hcau : ∀ j, ∀ z ∈ T, ‖fderiv ℂ F z (b j)‖ ≤ M / δ ∧ ‖complexLineSecondDeriv F z (b j)‖ ≤ 4 * M / δ ^ 2 :=
    fun j z hz => cauchy_line hΩ hF (hb1 j) hδ ((hball z hz).trans hδ0Ω)
      (fun w hw => hM w (hball z hz hw))
  have hMT : ∀ z ∈ T, ‖F z‖ ≤ M := fun z hz => hM z (hball z hz (mem_closedBall_self hδ.le))
  set D : Fin n → ℂ → V n → ℝ := fun j μ z =>
    fderiv ℝ (fun w => fderiv ℝ ψ w (μ • b j)) z (μ • b j) with hDdef
  set C0 : ℝ := 4 * (∑ j, ((∫ z, |D j 1 z|) + ∫ z, |D j I z|)) * ((M ^ 2 + 2) ^ 2 / 2) with hC0def
  have hC0 : 0 ≤ C0 := by
    have : 0 ≤ ∑ j, ((∫ z, |D j 1 z|) + ∫ z, |D j I z|) :=
      Finset.sum_nonneg fun j _ => add_nonneg (integral_nonneg fun _ => abs_nonneg _)
        (integral_nonneg fun _ => abs_nonneg _)
    positivity
  refine ⟨ENNReal.ofReal C0, ENNReal.ofReal_lt_top, fun k hk => ?_⟩
  set ε := Real.exp (-2 * k) with hεdef
  have hε : 0 < ε := Real.exp_pos _
  have gr : ∀ j, ∀ μ : ℂ, ‖μ‖ = 1 → _ := fun j μ hμ =>
    green_dir hΩ hF hT hTΩ hψ hψT hε (b j) μ hμ hMT (fun z hz => (hcau j z hz).1)
      (fun z hz => (hcau j z hz).2)
  have g1 := fun j => gr j 1 norm_one
  have gI := fun j => gr j I Complex.norm_I
  have hQi : ∀ j, Integrable (fun z => ψ z * lineSecondVariation ε (F z) (fderiv ℂ F z (b j) * 1)
      (complexLineSecondDeriv F z (b j) * 1 * 1) + ψ z * lineSecondVariation ε (F z) (fderiv ℂ F z (b j) * I)
      (complexLineSecondDeriv F z (b j) * I * I)) := fun j => (g1 j).1.add (gI j).1
  have hGi : Integrable (fun z => ∑ j, (ψ z * lineSecondVariation ε (F z) (fderiv ℂ F z (b j) * 1)
      (complexLineSecondDeriv F z (b j) * 1 * 1) + ψ z * lineSecondVariation ε (F z) (fderiv ℂ F z (b j) * I)
      (complexLineSecondDeriv F z (b j) * I * I))) := integrable_finsetSum _ fun j _ => hQi j
  have hGeq : ∀ z, (∑ j, (ψ z * lineSecondVariation ε (F z) (fderiv ℂ F z (b j) * 1)
      (complexLineSecondDeriv F z (b j) * 1 * 1) + ψ z * lineSecondVariation ε (F z) (fderiv ℂ F z (b j) * I)
      (complexLineSecondDeriv F z (b j) * I * I))) = ψ z * (4 * (‖F z‖ ^ 2 * halfLogRatioSqSecondDeriv ε (‖F z‖ ^ 2) +
        halfLogRatioSqDeriv ε (‖F z‖ ^ 2)) * ∑ j, ‖fderiv ℂ F z (b j)‖ ^ 2) := by
    intro z
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← mul_add, lineSecondVariation_add_I]
    ring
  have hG0 : ∀ z, 0 ≤ ∑ j, (ψ z * lineSecondVariation ε (F z) (fderiv ℂ F z (b j) * 1)
      (complexLineSecondDeriv F z (b j) * 1 * 1) + ψ z * lineSecondVariation ε (F z) (fderiv ℂ F z (b j) * I)
      (complexLineSecondDeriv F z (b j) * I * I)) := fun z => by
    rw [hGeq z]
    have := cut_rho_nonneg hε (by positivity : (0 : ℝ) ≤ ‖F z‖ ^ 2)
    exact mul_nonneg (hψ0 z) (mul_nonneg (by positivity)
      (Finset.sum_nonneg fun j _ => by positivity))
  have hIG : (∫ z, ∑ j, (ψ z * lineSecondVariation ε (F z) (fderiv ℂ F z (b j) * 1)
      (complexLineSecondDeriv F z (b j) * 1 * 1) + ψ z * lineSecondVariation ε (F z) (fderiv ℂ F z (b j) * I)
      (complexLineSecondDeriv F z (b j) * I * I))) = ∑ j, ((∫ z, D j 1 z * cutP ε (‖F z‖ ^ 2)) +
        ∫ z, D j I z * cutP ε (‖F z‖ ^ 2)) := by
    rw [integral_finsetSum _ fun j _ => hQi j]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_add (g1 j).1 (gI j).1]
    exact congrArg₂ (· + ·) (g1 j).2.2.2.2 (gI j).2.2.2.2
  have hDb : ∀ j, ∀ μ : ℂ, ‖μ‖ = 1 → ∫ z, D j μ z * cutP ε (‖F z‖ ^ 2) ≤
      (∫ z, |D j μ z|) * ((M ^ 2 + 2) ^ 2 / 2 * k ^ 2) := by
    intro j μ hμ
    obtain ⟨_, hi, hiD, hz0, _⟩ := gr j μ hμ
    rw [← integral_mul_const]
    refine integral_mono hi (hiD.abs.mul_const _) (fun z => ?_)
    by_cases hz : z ∈ T
    · have h1 : cutP ε (‖F z‖ ^ 2) ≤ (M ^ 2 + 2) ^ 2 / 2 * k ^ 2 :=
        (cutP_mono hε (by positivity) (pow_le_pow_left₀ (norm_nonneg _) (hMT z hz) 2)).trans
          (cutP_le hk (by positivity))
      have h2 := polydiscCutoff_nonneg ε (‖F z‖ ^ 2)
      calc D j μ z * cutP ε (‖F z‖ ^ 2) ≤ |D j μ z| * cutP ε (‖F z‖ ^ 2) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) h2
        _ ≤ |D j μ z| * ((M ^ 2 + 2) ^ 2 / 2 * k ^ 2) :=
            mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    · have : D j μ z = 0 := hz0 z hz
      simp [this]
  have hbound : 4 * (∫ z, ∑ j, (ψ z * lineSecondVariation ε (F z) (fderiv ℂ F z (b j) * 1)
      (complexLineSecondDeriv F z (b j) * 1 * 1) + ψ z * lineSecondVariation ε (F z) (fderiv ℂ F z (b j) * I)
      (complexLineSecondDeriv F z (b j) * I * I))) ≤ C0 * k ^ 2 := by
    rw [hIG, hC0def]
    have : ∑ j, ((∫ z, D j 1 z * cutP ε (‖F z‖ ^ 2)) + ∫ z, D j I z * cutP ε (‖F z‖ ^ 2)) ≤
        ∑ j, ((∫ z, |D j 1 z|) + ∫ z, |D j I z|) * ((M ^ 2 + 2) ^ 2 / 2 * k ^ 2) :=
      Finset.sum_le_sum fun j _ => by
        rw [add_mul]; exact add_le_add (hDb j 1 norm_one) (hDb j I Complex.norm_I)
    rw [← Finset.sum_mul] at this
    nlinarith
  have hpt : ∀ z ∈ K ∩ {z | F z ≠ 0 ∧ k ≤ -Real.log (‖F z‖ ^ 2) ∧
      -Real.log (‖F z‖ ^ 2) ≤ 2 * k},
      ‖fderiv ℝ (fun w => Real.log (‖F w‖ ^ 2)) z‖ₑ ^ 2 ≤
        ENNReal.ofReal (4 * ∑ j, (ψ z * lineSecondVariation ε (F z) (fderiv ℂ F z (b j) * 1)
          (complexLineSecondDeriv F z (b j) * 1 * 1) + ψ z * lineSecondVariation ε (F z) (fderiv ℂ F z (b j) * I)
          (complexLineSecondDeriv F z (b j) * I * I))) := by
    rintro z ⟨hzK, hz0, -, hz2⟩
    have hzΩ := hKΩ hzK
    have hF0 : 0 < ‖F z‖ := norm_pos_iff.2 hz0
    have hs0 : 0 < ‖F z‖ ^ 2 := by positivity
    have hεs : ε ≤ ‖F z‖ ^ 2 := by
      rw [hεdef, ← Real.exp_log hs0]
      exact Real.exp_le_exp.2 (by linarith)
    have hg := grad_log_sq hΩ hF hzΩ hz0
    have hr := cut_rho_ge hε hεs
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    rw [hGeq z, hψ1 z hzK, one_mul]
    have hsum : 0 ≤ ∑ j, ‖fderiv ℂ F z (b j)‖ ^ 2 := Finset.sum_nonneg fun j _ => by positivity
    calc ‖fderiv ℝ (fun w => Real.log (‖F w‖ ^ 2)) z‖ ^ 2
        ≤ 4 * (∑ j, ‖fderiv ℂ F z (b j)‖ ^ 2) / ‖F z‖ ^ 2 := hg
      _ = 4 * (∑ j, ‖fderiv ℂ F z (b j)‖ ^ 2) * (‖F z‖ ^ 2)⁻¹ := by ring
      _ ≤ 4 * (∑ j, ‖fderiv ℂ F z (b j)‖ ^ 2) *
          (4 * (‖F z‖ ^ 2 * halfLogRatioSqSecondDeriv ε (‖F z‖ ^ 2) + halfLogRatioSqDeriv ε (‖F z‖ ^ 2))) :=
          mul_le_mul_of_nonneg_left hr (by positivity)
      _ = _ := by ring
  have hGi4 := hGi.const_mul 4
  calc ∫⁻ z in K ∩ {z | F z ≠ 0 ∧ k ≤ -Real.log (‖F z‖ ^ 2) ∧
        -Real.log (‖F z‖ ^ 2) ≤ 2 * k}, ‖fderiv ℝ (fun w => Real.log (‖F w‖ ^ 2)) z‖ₑ ^ 2
      ≤ ∫⁻ z in K ∩ {z | F z ≠ 0 ∧ k ≤ -Real.log (‖F z‖ ^ 2) ∧
        -Real.log (‖F z‖ ^ 2) ≤ 2 * k}, ENNReal.ofReal (4 * ∑ j, (ψ z * lineSecondVariation ε (F z)
          (fderiv ℂ F z (b j) * 1) (complexLineSecondDeriv F z (b j) * 1 * 1) + ψ z * lineSecondVariation ε (F z)
          (fderiv ℂ F z (b j) * I) (complexLineSecondDeriv F z (b j) * I * I))) :=
        setLIntegral_mono_ae hGi4.aestronglyMeasurable.aemeasurable.ennreal_ofReal.restrict
          (Eventually.of_forall hpt)
    _ ≤ ∫⁻ z, ENNReal.ofReal (4 * ∑ j, (ψ z * lineSecondVariation ε (F z)
          (fderiv ℂ F z (b j) * 1) (complexLineSecondDeriv F z (b j) * 1 * 1) + ψ z * lineSecondVariation ε (F z)
          (fderiv ℂ F z (b j) * I) (complexLineSecondDeriv F z (b j) * I * I))) := setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal (∫ z, 4 * ∑ j, (ψ z * lineSecondVariation ε (F z)
          (fderiv ℂ F z (b j) * 1) (complexLineSecondDeriv F z (b j) * 1 * 1) + ψ z * lineSecondVariation ε (F z)
          (fderiv ℂ F z (b j) * I) (complexLineSecondDeriv F z (b j) * I * I))) :=
        (ofReal_integral_eq_lintegral_ofReal hGi4
          (Eventually.of_forall fun z => mul_nonneg (by norm_num) (hG0 z))).symm
    _ ≤ ENNReal.ofReal (C0 * k ^ 2) := by
        apply ENNReal.ofReal_le_ofReal
        rw [integral_const_mul]
        exact hbound
    _ = ENNReal.ofReal C0 * ENNReal.ofReal (k ^ 2) := ENNReal.ofReal_mul hC0

end ReciprocityTheory.L2DbarEstimates.C
