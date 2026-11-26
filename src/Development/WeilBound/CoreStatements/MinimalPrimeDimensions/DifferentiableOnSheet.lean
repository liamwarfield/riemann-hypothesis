module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeMapAreaOne
public import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.EvaluationGenEqZero

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.MinimalPrimeDimensions.IntegralBallPow
set_option autoImplicit false

noncomputable section

open MeasureTheory GroundTheory.Heights₂.Heights Metric Set Filter Topology Matrix
open ReciprocityTheory.L2DbarEstimates (V cHess wd wdb bas)
open ReciprocityTheory.ChartRestriction.G.Geo (cxHessian maDensity)
open scoped ENNReal ComplexOrder

namespace ChowFormHeightComparison₂.CF.C

theorem integral_ball_pow (e : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    ∫ t : ℂ, (ball (0 : ℂ) R).indicator (fun t => ‖t‖ ^ (2 * e)) t =
      Real.pi * R ^ (2 * (e + 1)) / (e + 1) := by
  have hfun : (ball (0 : ℂ) R).indicator (fun t => ‖t‖ ^ (2 * e)) =
      fun t => (Iio R).indicator (fun r : ℝ => r ^ (2 * e)) ‖t‖ := by
    ext t
    simp [Set.indicator]
  rw [hfun, integral_fun_norm_addHaar (volume : Measure ℂ)
    (fun r : ℝ => (Iio R).indicator (fun r : ℝ => r ^ (2 * e)) r)]
  have hvol : (volume : Measure ℂ).real (ball 0 1) = Real.pi := by
    simp [Measure.real]
  have hint : ∫ y in Ioi (0 : ℝ), y ^ (Module.finrank ℝ ℂ - 1) •
      (Iio R).indicator (fun r : ℝ => r ^ (2 * e)) y = R ^ (2 * e + 2) / (2 * e + 2) := by
    have hpt : (fun y : ℝ => y ^ (Module.finrank ℝ ℂ - 1) •
        (Iio R).indicator (fun r : ℝ => r ^ (2 * e)) y) =
        (Iio R).indicator (fun y : ℝ => y ^ (2 * e + 1)) := by
      ext y
      by_cases hy : y < R
      · simp [Set.indicator, hy, Complex.finrank_real_complex, pow_succ]
        ring
      · simp [Set.indicator, hy]
    rw [hpt, setIntegral_indicator measurableSet_Iio, Ioi_inter_Iio,
      ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hR, integral_pow]
    push_cast
    ring_nf
  rw [hint, hvol, Complex.finrank_real_complex]
  simp only [nsmul_eq_mul, smul_eq_mul]
  push_cast
  field_simp
  ring

theorem gram_nonneg {e n : ℕ} (v : (Fin e → ℂ) → (Fin n → ℂ)) (y : Fin e → ℂ) :
    0 ≤ gramVol v y := by
  unfold gramVol
  dsimp only
  set w : Fin (e + 1) → Fin n → ℂ := Fin.cons (v y) fun j => fderiv ℂ v y (Pi.single j 1)
  have hM : (Matrix.of fun a b => ∑ i, star (w a i) * w b i) =
      (Matrix.of fun (i : Fin n) (a : Fin (e + 1)) => w a i)ᴴ *
        Matrix.of fun (i : Fin n) (a : Fin (e + 1)) => w a i := by
    ext a b
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
  have h := (Matrix.posSemidef_conjTranspose_mul_self
    (Matrix.of fun (i : Fin n) (a : Fin (e + 1)) => w a i)).det_nonneg
  rw [← hM] at h
  exact (Complex.nonneg_iff.1 h).1

def fsDens {e n : ℕ} (v : (Fin e → ℂ) → (Fin n → ℂ)) (x : Fin e → ℂ) : ℝ :=
  (e.factorial : ℝ) / Real.pi ^ e * gramVol v x / ‖WithLp.toLp 2 (v x)‖ ^ (2 * (e + 1))

theorem fsDens_nonneg {e n : ℕ} (v : (Fin e → ℂ) → (Fin n → ℂ)) (x : Fin e → ℂ) : 0 ≤ fsDens v x :=
  div_nonneg (mul_nonneg (by positivity) (gram_nonneg v x)) (by positivity)

theorem cHess_two_mul {D : ℕ} {ψ : (Fin D → ℂ) → ℝ} {v : V D} (hψ : ContDiffAt ℝ 2 ψ v.ofLp) :
    cHess D (fun w => ((2 * ψ w.ofLp : ℝ) : ℂ)) v = (2 : ℂ) • cxHessian ψ v.ofLp := by
  let L : V D →L[ℝ] (Fin D → ℂ) := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin D => ℂ) : V D →L[ℝ] (Fin D → ℂ))
  have hL (w : V D) : L w = w.ofLp := rfl
  have hd : DifferentiableAt ℝ (fderiv ℝ ψ) v.ofLp :=
    (hψ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hev : ∀ᶠ w in 𝓝 v, DifferentiableAt ℝ ψ (L w) :=
    L.continuous.continuousAt.eventually
      ((hψ.eventually (by simp)).mono fun x hx => hx.differentiableAt (by norm_num))
  have h1 : ∀ᶠ w in 𝓝 v, ∀ b, fderiv ℝ (fun w : V D => ((2 * ψ w.ofLp : ℝ) : ℂ)) w b =
      2 * ((fderiv ℝ ψ (L w) (L b) : ℝ) : ℂ) := by
    filter_upwards [hev] with w hw b
    have := Complex.ofRealCLM.hasFDerivAt.comp w ((hw.hasFDerivAt.comp w L.hasFDerivAt).const_mul 2)
    have e : HasFDerivAt (fun w : V D => ((2 * ψ w.ofLp : ℝ) : ℂ)) _ w := this
    rw [e.fderiv]
    simp
  have h2 (c : Fin D → ℂ) : HasFDerivAt (fun w : V D => ((fderiv ℝ ψ (L w) c : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (((fderiv ℝ (fderiv ℝ ψ) v.ofLp).flip c).comp L)) v := by
    have a1 : HasFDerivAt (fun x => fderiv ℝ ψ x c) ((fderiv ℝ (fderiv ℝ ψ) v.ofLp).flip c) (L v) := by
      have := (ContinuousLinearMap.apply ℝ ℝ c).hasFDerivAt.comp _ hd.hasFDerivAt
      exact this
    exact Complex.ofRealCLM.hasFDerivAt.comp v (a1.comp v L.hasFDerivAt)
  ext j k
  have h3 : wdb D k (fun w : V D => ((2 * ψ w.ofLp : ℝ) : ℂ)) =ᶠ[𝓝 v] fun w =>
      ((fderiv ℝ ψ (L w) (L (bas D k)) : ℝ) : ℂ) + Complex.I * ((fderiv ℝ ψ (L w) (L (Complex.I • bas D k)) : ℝ) : ℂ) := by
    filter_upwards [h1] with w hw
    rw [wdb, hw, hw]
    ring
  have h4 := (h2 (L (bas D k))).add ((h2 (L (Complex.I • bas D k))).const_mul Complex.I)
  have h5 : HasFDerivAt (wdb D k (fun w : V D => ((2 * ψ w.ofLp : ℝ) : ℂ))) _ v := h4.congr_of_eventuallyEq h3
  have hb (i : Fin D) : L (bas D i) = Pi.single i 1 := by
    rw [hL]; simp [bas]
  have hb' (i : Fin D) : L (Complex.I • bas D i) = Complex.I • Pi.single i 1 := by
    rw [hL, WithLp.ofLp_smul, ← hL, hb]
  rw [cHess, Matrix.of_apply, wd, h5.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, Complex.ofRealCLM_apply, hb, hb', smul_eq_mul, Matrix.smul_apply, cxHessian]
  push_cast
  linear_combination (-(((fderiv ℝ (fderiv ℝ ψ) v.ofLp) (Complex.I • Pi.single j 1)
    (Complex.I • Pi.single k 1) : ℝ) : ℂ) / 2) * Complex.I_mul_I

theorem dens_eq {e n : ℕ} {w : (Fin e → ℂ) → Fin n → ℂ} {x : V e}
    (hw : ∀ᶠ y in 𝓝 x.ofLp, DifferentiableAt ℂ w y) (h0 : w x.ofLp ≠ 0) {G : V e → ℂ}
    (hG : G =ᶠ[𝓝 x] fun v => ((Real.log (‖WithLp.toLp 2 (w v.ofLp)‖ ^ 2) : ℝ) : ℂ)) :
    (e.factorial : ℝ) / Real.pi ^ e * (cHess e G x).det.re = fsDens w x.ofLp := by
  obtain ⟨t, ht, hto, hyt⟩ := _root_.eventually_nhds_iff.1 hw
  have han : AnalyticOnNhd ℂ w t := by
    have hd : DifferentiableOn ℂ w t := fun y' hy' => (ht y' hy').differentiableWithinAt
    exact AnalyticOnNhd.pi fun j =>
      ReciprocityTheory.AnForm.Osgood.osgood e t _ hto (differentiableOn_pi.mp hd j)
  have hc : ContDiffAt ℝ 2 (fun y => Real.log ‖WithLp.toLp 2 (w y)‖) x.ofLp := by
    have h1 : ContDiffAt ℝ 2 (fun y => (WithLp.toLp 2 (w y) : EuclideanSpace ℂ (Fin n))) x.ofLp :=
      (PiLp.contDiff_toLp (𝕜 := ℝ)).contDiffAt.comp _ (((han _ hyt).contDiffAt (n := 2)).restrict_scalars ℝ)
    have h2 : (WithLp.toLp 2 (w x.ofLp) : EuclideanSpace ℂ (Fin n)) ≠ 0 := by simpa using h0
    exact (h1.norm ℂ h2).log (norm_ne_zero_iff.2 h2)
  have e1 : (fun v : V e => ((Real.log (‖WithLp.toLp 2 (w v.ofLp)‖ ^ 2) : ℝ) : ℂ)) =
      fun v : V e => ((2 * Real.log ‖WithLp.toLp 2 (w v.ofLp)‖ : ℝ) : ℂ) := by
    funext v
    rw [Real.log_pow]
    norm_num
  rw [ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr hG, e1,
    cHess_two_mul (ψ := fun y => Real.log ‖WithLp.toLp 2 (w y)‖) hc, fsDens, ← ChartGramMA.proof e n w _ hw h0,
    maDensity, ChartGram.mixedDisc_const, Matrix.det_smul, Fintype.card_fin,
    show (2 : ℂ) ^ e = ((2 ^ e : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul, div_pow]
  ring

theorem lintegral_line {e n : ℕ} {F : EuclideanSpace ℂ (Fin n) → ℝ≥0∞} (hF : ∀ t : ℂ, t ≠ 0 → ∀ x, F (t • x) = F x)
    {w : EuclideanSpace ℂ (Fin n)} (hw : w ≠ 0) {G : ℝ} (hG : 0 ≤ G) :
    ∫⁻ t : ℂ, (ball (0 : EuclideanSpace ℂ (Fin n)) 1).indicator F (t • w) * ENNReal.ofReal (‖t‖ ^ (2 * e) * G) =
      ENNReal.ofReal (Real.pi ^ (e + 1) / ((e + 1).factorial : ℝ)) *
        (F w * ENNReal.ofReal ((e.factorial : ℝ) / Real.pi ^ e * G / ‖w‖ ^ (2 * (e + 1)))) := by
  have hn : 0 < ‖w‖ := norm_pos_iff.2 hw
  have hae : (fun t : ℂ => (ball (0 : EuclideanSpace ℂ (Fin n)) 1).indicator F (t • w) *
      ENNReal.ofReal (‖t‖ ^ (2 * e) * G)) =ᵐ[volume] fun t => F w * (ENNReal.ofReal G *
        ENNReal.ofReal ((ball (0 : ℂ) ‖w‖⁻¹).indicator (fun t => ‖t‖ ^ (2 * e)) t)) := by
    have h0 : ∀ᵐ t : ℂ, t ≠ 0 := by simp [ae_iff]
    filter_upwards [h0] with t ht
    have hiff : t • w ∈ ball (0 : EuclideanSpace ℂ (Fin n)) 1 ↔ t ∈ ball (0 : ℂ) ‖w‖⁻¹ := by
      rw [mem_ball_zero_iff, mem_ball_zero_iff, norm_smul, ← one_div, lt_div_iff₀ hn]
    by_cases h : t ∈ ball (0 : ℂ) ‖w‖⁻¹
    · rw [indicator_of_mem h, indicator_of_mem (hiff.2 h), hF t ht, mul_comm _ G, ENNReal.ofReal_mul hG]
    · rw [indicator_of_notMem h, indicator_of_notMem (mt hiff.1 h)]
      simp
  have hm : Measurable fun t : ℂ => ENNReal.ofReal ((ball (0 : ℂ) ‖w‖⁻¹).indicator (fun t => ‖t‖ ^ (2 * e)) t) :=
    ENNReal.measurable_ofReal.comp ((measurable_norm.pow_const _).indicator measurableSet_ball)
  have hint : Integrable ((ball (0 : ℂ) ‖w‖⁻¹).indicator fun t => ‖t‖ ^ (2 * e)) :=
    (integrable_indicator_iff measurableSet_ball).2
      (((continuous_norm.pow _).continuousOn.integrableOn_compact (isCompact_closedBall _ _)).mono_set
        ball_subset_closedBall)
  rw [lintegral_congr_ae hae, lintegral_const_mul _ (hm.const_mul _), lintegral_const_mul _ hm,
    ← ofReal_integral_eq_lintegral_ofReal hint (.of_forall fun t => indicator_nonneg (fun _ _ => by positivity) t),
    integral_ball_pow e (inv_nonneg.2 hn.le), ← ENNReal.ofReal_mul hG, mul_left_comm (ENNReal.ofReal _) (F w),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  have := Real.pi_pos
  rw [Nat.factorial_succ, inv_pow]
  push_cast
  field_simp
  ring

theorem area_ball {n e : ℕ} {ι : Type} [Countable ι] {U D : ι → Set (Fin e → ℂ)}
    {v : ι → (Fin e → ℂ) → (Fin n → ℂ)} {F : EuclideanSpace ℂ (Fin n) → ℝ≥0∞}
    (hUD : ∀ i, IsOpen (U i) ∧ MeasurableSet (D i) ∧ D i ⊆ U i ∧ DifferentiableOn ℂ (v i) (U i))
    (hinj : Set.InjOn (fun q : ι × (Fin e → ℂ) × ℂ => q.2.2 • WithLp.toLp 2 (v q.1 q.2.1))
      {q | q.2.1 ∈ D q.1 ∧ q.2.2 ≠ 0}) (h0 : ∀ i, ∀ x ∈ D i, v i x ≠ 0)
    (hm : Measurable F) (hF : ∀ t : ℂ, t ≠ 0 → ∀ x, F (t • x) = F x) :
    ∫⁻ y in ball 0 1 ∩ (fun q : ι × (Fin e → ℂ) × ℂ => q.2.2 • WithLp.toLp 2 (v q.1 q.2.1)) ''
        {q | q.2.1 ∈ D q.1 ∧ q.2.2 ≠ 0}, F y ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) =
      Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
          {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ j : Fin n, e + 1 ≤ (j : ℕ) → y j = 0} *
        ∑' i, ∫⁻ x in D i, F (WithLp.toLp 2 (v i x)) * ENNReal.ofReal (fsDens (v i) x) := by
  have hA := ConeMapArea.proof (ConeMapAreaOne.proof (AreaFormulaInj.proof (AreaFormulaInjSet.proof
    AreaFormulaLocal.proof))) n e ι U D v _ hUD hinj (hm.indicator (measurableSet_ball (x := 0) (ε := 1)))
  have hc0 : ENNReal.ofReal (Real.pi ^ (e + 1) / ((e + 1).factorial : ℝ)) ≠ 0 := by
    have := Real.pi_pos
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    positivity
  have e1 (i : ι) : ∫⁻ x in D i, ∫⁻ t : ℂ, (ball (0 : EuclideanSpace ℂ (Fin n)) 1).indicator F
      (t • WithLp.toLp 2 (v i x)) * ENNReal.ofReal (‖t‖ ^ (2 * e) * gramVol (v i) x) =
      ENNReal.ofReal (Real.pi ^ (e + 1) / ((e + 1).factorial : ℝ)) *
        ∫⁻ x in D i, F (WithLp.toLp 2 (v i x)) * ENNReal.ofReal (fsDens (v i) x) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact setLIntegral_congr_fun (hUD i).2.1 fun x hx =>
      lintegral_line hF (by simpa using h0 i x hx) (gram_nonneg _ _)
  simp only [e1] at hA
  rw [ENNReal.tsum_mul_left, mul_left_comm, ENNReal.mul_right_inj hc0 ENNReal.ofReal_ne_top,
    lintegral_indicator measurableSet_ball, Measure.restrict_restrict measurableSet_ball] at hA
  exact hA

end ChowFormHeightComparison₂.CF.C
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier
open MeasureTheory Set Filter Topology Matrix GlobalTheory.ChartGlue
open ReciprocityTheory.L2DbarEstimates (V cHess)
open GroundTheory.Heights₂.Heights (HermNorm coneBall)
open scoped ENNReal ContDiff

namespace ChowFormHeightComparison₂.CF.C

variable {R : Type} [CommRing R] {m e : ℕ}

def euc (h : HermNorm m) (x : Fin m → ℂ) : EuclideanSpace ℂ (Fin m) := WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x)

theorem isUnit_det_transpose (h : HermNorm m) : IsUnit (h.matᵀ).det := by
  rw [Matrix.det_transpose]; exact h.isUnit_det

theorem pointOf_euc (h : HermNorm m) (x : Fin m → ℂ) : h.pointOf (euc h x) = x := by
  change h.matᵀ *ᵥ ((h.matᵀ)⁻¹ *ᵥ x) = x
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_det_transpose h), Matrix.one_mulVec]

theorem euc_pointOf (h : HermNorm m) (y : EuclideanSpace ℂ (Fin m)) : euc h (h.pointOf y) = y := by
  have hu := isUnit_det_transpose h
  simp only [HermNorm.pointOf, euc]
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]

theorem euc_smul (h : HermNorm m) (c : ℂ) (x : Fin m → ℂ) : euc h (c • x) = c • euc h x := by
  simp only [euc, Matrix.mulVec_smul]
  rfl

theorem euc_injective (h : HermNorm m) : Function.Injective (euc h) :=
  Function.LeftInverse.injective (pointOf_euc h)

theorem norm_euc (h : HermNorm m) (x : Fin m → ℂ) : ‖euc h x‖ = h.dualNorm x := EuclideanSpace.norm_eq _

theorem continuous_euc (h : HermNorm m) : Continuous (euc h) := by
  unfold euc
  fun_prop

variable {Z : Scheme.{0}} {B : LB Z} {p : Z ⟶ Sp R} {s : Fin m → B.Sec} {σ : R →+* ℂ}


variable (s) in
def sheet (h : HermNorm m) (c : AlgChart p σ e) (i : B.ι) (x : Fin e → ℂ) : Fin m → ℂ :=
  (h.matᵀ)⁻¹ *ᵥ loc p s σ i (c.e.symm (WithLp.toLp 2 x))

variable {h : HermNorm m} {φ : Weight p σ B}

theorem isOpen_dom (c : AlgChart p σ e) (i : B.ι) :
    IsOpen ((WithLp.toLp 2 : (Fin e → ℂ) → V e) ⁻¹' (c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ (B.U i))) := by
  exact (c.e.isOpen_inter_preimage_symm (isOpen_ptsIn _)).preimage (PiLp.continuous_toLp 2 _)

theorem differentiableOn_sheet (c : AlgChart p σ e) (i : B.ι) : DifferentiableOn ℂ (sheet s h c i)
    ((WithLp.toLp 2 : (Fin e → ℂ) → V e) ⁻¹' (c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ (B.U i))) := by
  have hL : Differentiable ℂ (WithLp.toLp 2 : (Fin e → ℂ) → V e) :=
    (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin e => ℂ)).symm.differentiable
  have hg : ∀ k, DifferentiableOn ℂ (fun x : Fin e → ℂ => loc p s σ i (c.e.symm (WithLp.toLp 2 x)) k)
      ((WithLp.toLp 2 : (Fin e → ℂ) → V e) ⁻¹' (c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ (B.U i))) := by
    intro k
    exact (c.holo (B.U i) ((s k).f i)).comp hL.differentiableOn (fun x hx => hx)
  rw [differentiableOn_pi]
  intro j
  simp only [sheet, Matrix.mulVec, dotProduct]
  exact DifferentiableOn.fun_sum fun k _ => (hg k).const_mul _

theorem toLp_sheet (c : AlgChart p σ e) (i : B.ι) {y : CxPts p σ} (hy : y ∈ c.e.source) :
    WithLp.toLp 2 (sheet s h c i (c.e y).ofLp) = euc h (loc p s σ i y) := by
  simp only [sheet, euc, WithLp.toLp_ofLp, c.e.left_inv hy]

theorem sheet_ne_zero (hE : Emb p s) (c : AlgChart p σ e) {i : B.ι} {y : CxPts p σ} (hy : y ∈ c.e.source)
    (hi : y ∈ ptsIn p σ (B.U i)) : sheet s h c i (c.e y).ofLp ≠ 0 := by
  intro h0
  apply loc_ne_zero hE hi
  have h1 := congrArg (WithLp.toLp 2) h0
  rw [toLp_sheet c i hy] at h1
  apply euc_injective h
  rw [h1]
  simp [euc]

theorem chernDens_eq_fsDens (hE : Emb p s) (hφ : φ.IsCInf) (hF : IsFS φ s h) (c : AlgChart p σ e) {i : B.ι}
    {y : CxPts p σ} (hy : y ∈ c.e.source) (hi : y ∈ ptsIn p σ (B.U i)) :
    c.chernDens φ y = fsDens (sheet s h c i) (c.e y).ofLp := by
  have hO := c.e.isOpen_inter_preimage_symm (isOpen_ptsIn (B.U i))
  have hmem : c.e y ∈ c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ (B.U i) := by
    refine ⟨c.e.map_source hy, ?_⟩
    rw [Set.mem_preimage, c.e.left_inv hy]
    exact hi
  rw [c.chernDens_eq hφ hy hi]
  unfold AlgChart.hess
  apply dens_eq
  · have hmem' : (c.e y).ofLp ∈ (WithLp.toLp 2 : (Fin e → ℂ) → V e) ⁻¹'
        (c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ (B.U i)) := by
      rw [Set.mem_preimage, WithLp.toLp_ofLp]
      exact hmem
    filter_upwards [(isOpen_dom c i).mem_nhds hmem'] with x hx
    exact (differentiableOn_sheet (s := s) (h := h) c i).differentiableAt ((isOpen_dom c i).mem_nhds hx)
  · exact sheet_ne_zero hE c hy hi
  · filter_upwards [hO.mem_nhds hmem] with v hv
    rw [hF i _ hv.2, ← norm_euc h]
    simp only [sheet, WithLp.toLp_ofLp]
    rfl

theorem chernPart_neg (hE : Emb p s) (hφ : φ.IsCInf) (hF : IsFS φ s h) : φ.chernPart e (-1) = 0 := by
  have hc : ∀ c : AlgChart p σ e,
      chartMeas c.e (fun y => ENNReal.ofReal (((-1 : ℤˣ) : ℤ) * c.chernDens φ y)) = 0 := by
    intro c
    unfold chartMeas
    have h0 : (volume.restrict c.e.target).withDensity
        ((fun y => ENNReal.ofReal (((-1 : ℤˣ) : ℤ) * c.chernDens φ y)) ∘ c.e.symm) = 0 := by
      rw [withDensity_congr_ae (g := 0), withDensity_zero]
      filter_upwards [ae_restrict_mem c.e.open_target.measurableSet] with v hv
      have hs := c.e.map_target hv
      simp only [Function.comp_apply, Pi.zero_apply]
      rw [chernDens_eq_fsDens hE hφ hF c hs (mem_pick hE.isLB _)]
      apply ENNReal.ofReal_eq_zero.2
      have := fsDens_nonneg (sheet s h c (pick hE.isLB (c.e.symm v))) (c.e (c.e.symm v)).ofLp
      simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_one_mul]
      linarith
    rw [h0, Measure.map_zero]
  unfold Weight.chernPart glueMeas
  exact le_antisymm (iSup_le fun c => (hc c).le) (Measure.zero_le _)

theorem measurable_ev (U : Z.Opens) (f : Γ(Z, U)) : Measurable (ev p σ U f) := by
  classical
  have hs : MeasurableSet (ptsIn p σ U) := (isOpen_ptsIn U).measurableSet
  have he : ev p σ U f = (ptsIn p σ U).piecewise (ev p σ U f) 0 := by
    funext y
    by_cases hy : y ∈ ptsIn p σ U
    · simp [Set.piecewise, hy]
    · simp [Set.piecewise, hy, ev_of_notMem hy]
  rw [he]
  exact (continuousOn_ev f).measurable_piecewise continuousOn_const hs

variable [SecondCountableTopology (CxPts p σ)]

theorem measurable_coords {β : Type} [MeasurableSpace β] (hB : B.IsLB) {F : EuclideanSpace ℂ (Fin m) → β}
    (hm : Measurable F) (hF : ∀ t : ℂ, t ≠ 0 → ∀ x, F (t • x) = F x) :
    Measurable fun y => F (euc h (coords p σ hB s y)) := by
  obtain ⟨T, hT, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun i : B.ι => ptsIn p σ (B.U i)) (fun i => isOpen_ptsIn _)
  have hcov : ∀ y : CxPts p σ, ∃ i ∈ T, y ∈ ptsIn p σ (B.U i) := by
    intro y
    have hy : y ∈ ⋃ i ∈ T, ptsIn p σ (B.U i) := by
      rw [hTU]
      exact mem_iUnion.2 ⟨_, mem_pick hB y⟩
    simpa using hy
  have hloc : ∀ i, Measurable fun y => F (euc h (loc p s σ i y)) := by
    intro i
    refine hm.comp ((continuous_euc h).measurable.comp ?_)
    exact Measurable.of_eval fun k => measurable_ev (B.U i) ((s k).f i)
  have heq : ∀ i, ∀ y ∈ ptsIn p σ (B.U i),
      F (euc h (coords p σ hB s y)) = F (euc h (loc p s σ i y)) := by
    intro i y hy
    obtain ⟨c, hc, hcl⟩ := loc_eq_smul (s := s) (mem_pick hB y) hy
    have hco : coords p σ hB s y = loc p s σ (pick hB y) y := rfl
    rw [hco, hcl, euc_smul, hF c hc]
  intro t ht
  have hpre : (fun y => F (euc h (coords p σ hB s y))) ⁻¹' t =
      ⋃ i ∈ T, ptsIn p σ (B.U i) ∩ (fun y => F (euc h (loc p s σ i y))) ⁻¹' t := by
    ext y
    simp only [mem_preimage, mem_iUnion, mem_inter_iff, exists_prop]
    constructor
    · intro hy
      obtain ⟨i, hi, hyi⟩ := hcov y
      exact ⟨i, hi, hyi, by rw [← heq i y hyi]; exact hy⟩
    · rintro ⟨i, hi, hyi, hy⟩
      rw [heq i y hyi]
      exact hy
  rw [hpre]
  exact MeasurableSet.biUnion hT fun i _ => (isOpen_ptsIn _).measurableSet.inter (hloc i ht)

private theorem aemeasurable_ofReal_fsDens {e n : ℕ} {v : (Fin e → ℂ) → Fin n → ℂ} {D : Set (Fin e → ℂ)}
    (hv : ContinuousOn v D) (hD : MeasurableSet D) :
    AEMeasurable (fun x => ENNReal.ofReal (fsDens v x)) (volume.restrict D) := by
  have h1 : AEMeasurable v (volume.restrict D) := hv.aemeasurable hD
  have h2 : Measurable fun x => fun j : Fin e => fderiv ℂ v x (Pi.single j 1) :=
    Measurable.of_eval fun j => measurable_fderiv_apply_const ℂ v _
  have hpair : AEMeasurable (fun x => (v x, fun j : Fin e => fderiv ℂ v x (Pi.single j 1)))
      (volume.restrict D) := h1.prodMk h2.aemeasurable
  have hcons : Continuous fun q : (Fin n → ℂ) × (Fin e → Fin n → ℂ) =>
      (Fin.cons q.1 q.2 : Fin (e + 1) → Fin n → ℂ) :=
    Continuous.finCons (A := fun _ => Fin n → ℂ) continuous_fst continuous_snd
  have hw : ∀ a : Fin (e + 1), Continuous fun q : (Fin n → ℂ) × (Fin e → Fin n → ℂ) =>
      (Fin.cons q.1 q.2 : Fin (e + 1) → Fin n → ℂ) a := fun a =>
    (continuous_apply a).comp hcons
  have hM : Continuous fun q : (Fin n → ℂ) × (Fin e → Fin n → ℂ) =>
      (Matrix.of fun a b : Fin (e + 1) => ∑ i : Fin n,
        star ((Fin.cons q.1 q.2 : Fin (e + 1) → Fin n → ℂ) a i) *
          (Fin.cons q.1 q.2 : Fin (e + 1) → Fin n → ℂ) b i).det.re := by
    refine Complex.continuous_re.comp (Continuous.matrix_det ?_)
    refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [Matrix.of_apply]
    exact continuous_finsetSum _ fun i _ =>
      ((continuous_apply i).comp (hw a)).star.mul ((continuous_apply i).comp (hw b))
  have hψ : Measurable fun q : (Fin n → ℂ) × (Fin e → Fin n → ℂ) =>
      ENNReal.ofReal ((e.factorial : ℝ) / Real.pi ^ e *
        (Matrix.of fun a b : Fin (e + 1) => ∑ i : Fin n,
          star ((Fin.cons q.1 q.2 : Fin (e + 1) → Fin n → ℂ) a i) *
            (Fin.cons q.1 q.2 : Fin (e + 1) → Fin n → ℂ) b i).det.re /
        ‖WithLp.toLp 2 q.1‖ ^ (2 * (e + 1))) :=
    ENNReal.measurable_ofReal.comp ((measurable_const.mul hM.measurable).div
      (((continuous_norm.comp ((PiLp.continuous_toLp 2 _).comp continuous_fst)).pow _).measurable))
  refine (hψ.comp_aemeasurable hpair).congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [Function.comp_apply, fsDens, GroundTheory.Heights₂.Heights.gramVol]

theorem lintegral_chart (hE : Emb p s) (hφ : φ.IsCInf) (hF : IsFS φ s h) (c : AlgChart p σ e) {i : B.ι}
    (hc : c.e.source ⊆ ptsIn p σ (B.U i)) {A : Set (CxPts p σ)} (hA : MeasurableSet A) (hAc : A ⊆ c.e.source)
    {Φ : CxPts p σ → ℝ≥0∞} (hΦ : Measurable Φ) :
    ∫⁻ y in A, Φ y ∂φ.chernPart e 1 = ∫⁻ x in (WithLp.toLp 2 : (Fin e → ℂ) → V e) ⁻¹' (c.e '' A),
      Φ (c.e.symm (WithLp.toLp 2 x)) * ENNReal.ofReal (fsDens (sheet s h c i) x) := by
  set ρ : AlgChart p σ e → CxPts p σ → ℝ≥0∞ :=
    fun c' y => ENNReal.ofReal (((((1 : ℤˣ) : ℤ) : ℝ)) * c'.chernDens φ y) with hρ
  have hglue : ∀ S, MeasurableSet S → S ⊆ c.e.source → φ.chernPart e 1 S = chartMeas c.e (ρ c) S := by
    intro S hS hSs
    refine glueMeas_apply (fun c' : AlgChart p σ e => c'.e) ρ (fun a b => a.holo_trans b) ?_ c hS hSs
    intro a b y ha hb
    simp only [hρ, Units.val_one, Int.cast_one, one_mul]
    rw [a.chernDens_trans b hφ ha hb, ENNReal.ofReal_mul (sq_nonneg _)]
  set D := (WithLp.toLp 2 : (Fin e → ℂ) → V e) ⁻¹' (c.e '' A) with hDdef
  set g : (Fin e → ℂ) → CxPts p σ := fun x => c.e.symm (WithLp.toLp 2 x) with hgdef
  set dens : (Fin e → ℂ) → ℝ≥0∞ := fun x => ENNReal.ofReal (fsDens (sheet s h c i) x) with hdensdef
  have hAi : MeasurableSet (c.e '' A) := measurableSet_image c.e hA hAc
  have hD : MeasurableSet D := hAi.preimage (PiLp.continuous_toLp 2 _).measurable
  have hpt : ∀ x ∈ D, ∃ a ∈ A, c.e a = WithLp.toLp 2 x ∧ g x = a := by
    intro x hx
    obtain ⟨a, ha, hax⟩ := hx
    exact ⟨a, ha, hax, by simp only [hgdef]; rw [← hax, c.e.left_inv (hAc ha)]⟩
  have hDT : D ⊆ (WithLp.toLp 2 : (Fin e → ℂ) → V e) ⁻¹'
      (c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ (B.U i)) := by
    intro x hx
    obtain ⟨a, ha, hax, hga⟩ := hpt x hx
    refine ⟨?_, ?_⟩
    · rw [← hax]
      exact c.e.map_source (hAc ha)
    · show g x ∈ ptsIn p σ (B.U i)
      rw [hga]
      exact hc (hAc ha)
  have hgc : ContinuousOn g D :=
    c.e.continuousOn_symm.comp (PiLp.continuous_toLp 2 _).continuousOn (fun x hx => (hDT hx).1)
  have hg : AEMeasurable g ((volume.restrict D).withDensity dens) :=
    (hgc.aemeasurable hD).mono_ac (withDensity_absolutelyContinuous _ _)
  have hdens : AEMeasurable dens (volume.restrict D) :=
    aemeasurable_ofReal_fsDens ((differentiableOn_sheet (s := s) (h := h) c i).continuousOn.mono hDT) hD
  have hval : ∀ x ∈ D, ρ c (c.e.symm (WithLp.toLp 2 x)) = dens x := by
    intro x hx
    obtain ⟨a, ha, hax, hga⟩ := hpt x hx
    have hga' : c.e.symm (WithLp.toLp 2 x) = a := hga
    simp only [hρ, hdensdef, Units.val_one, Int.cast_one, one_mul]
    rw [hga', chernDens_eq_fsDens hE hφ hF c (hAc ha) (hc (hAc ha)), hax, WithLp.ofLp_toLp]
  have hmeas : (φ.chernPart e 1).restrict A = Measure.map g ((volume.restrict D).withDensity dens) := by
    ext S hS
    rw [Measure.restrict_apply hS, Measure.map_apply_of_aemeasurable hg hS, withDensity_apply',
      Measure.restrict_restrict' hD]
    have hSA : S ∩ A ⊆ c.e.source := inter_subset_right.trans hAc
    have hset : g ⁻¹' S ∩ D = (WithLp.toLp 2 : (Fin e → ℂ) → V e) ⁻¹' (c.e '' (S ∩ A)) := by
      ext x
      constructor
      · rintro ⟨hxS, hxD⟩
        obtain ⟨a, ha, hax, hga⟩ := hpt x hxD
        refine ⟨a, ⟨?_, ha⟩, hax⟩
        rw [← hga]
        exact hxS
      · rintro ⟨a, ⟨haS, ha⟩, hax⟩
        have hxD : x ∈ D := ⟨a, ha, hax⟩
        obtain ⟨a', ha', hax', hga'⟩ := hpt x hxD
        refine ⟨?_, hxD⟩
        show g x ∈ S
        have : a' = a := c.e.injOn (hAc ha') (hAc ha) (hax'.trans hax.symm)
        rw [hga', this]
        exact haS
    rw [hset, hglue (S ∩ A) (hS.inter hA) hSA, chartMeas_apply_of_subset _ _ (hS.inter hA) hSA,
      ← (GroundTheory.Heights₂.Heights.ConeMapAreaFormula.measurePreserving_toLp e).setLIntegral_comp_preimage_emb
        (MeasurableEquiv.toLp 2 (Fin e → ℂ)).measurableEmbedding]
    refine setLIntegral_congr_fun ((measurableSet_image c.e (hS.inter hA) hSA).preimage
      (PiLp.continuous_toLp 2 _).measurable) fun x hx => ?_
    have hxD : x ∈ D := by
      obtain ⟨a, ⟨_, ha⟩, hax⟩ := hx
      exact ⟨a, ha, hax⟩
    exact hval x hxD
  rw [hmeas, lintegral_map' hΦ.aemeasurable hg]
  have hmul := lintegral_withDensity_eq_lintegral_mul₀ hdens (hΦ.comp_aemeasurable (hgc.aemeasurable hD))
  exact hmul.trans (lintegral_congr fun x => mul_comm _ _)

theorem exists_parts (hB : B.IsLB) : ∃ (ι : Type) (_ : Countable ι) (c : ι → AlgChart p σ e) (i : ι → B.ι)
    (A : ι → Set (CxPts p σ)), (∀ a, (c a).e.source ⊆ ptsIn p σ (B.U (i a))) ∧ (∀ a, MeasurableSet (A a)) ∧
      (∀ a, A a ⊆ (c a).e.source) ∧ Pairwise (Function.onFun Disjoint A) ∧
      ∀ c' : AlgChart p σ e, c'.e.source ⊆ ⋃ a, A a := by
  classical
  let S : AlgChart p σ e × B.ι → Set (CxPts p σ) := fun q =>
    (q.1.restr (ptsIn p σ (B.U q.2)) (isOpen_ptsIn _)).e.source
  have hSo : ∀ q, IsOpen (S q) := fun q => (q.1.restr (ptsIn p σ (B.U q.2)) (isOpen_ptsIn _)).e.open_source
  obtain ⟨T, hT, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable S hSo
  have hmemT : ∀ c' : AlgChart p σ e, ∀ y ∈ c'.e.source, ∃ q ∈ T, y ∈ S q := by
    intro c' y hy
    have hyS : y ∈ S (c', pick hB y) := by
      show y ∈ (c'.restr (ptsIn p σ (B.U (pick hB y))) (isOpen_ptsIn _)).e.source
      rw [AlgChart.restr_source]
      exact ⟨hy, mem_pick hB y⟩
    have hy' : y ∈ ⋃ q ∈ T, S q := by
      rw [hTU]
      exact mem_iUnion.2 ⟨_, hyS⟩
    simpa using hy'
  rcases T.eq_empty_or_nonempty with hTe | hTn
  · refine ⟨Empty, inferInstance, fun a => a.elim, fun a => a.elim, fun a => a.elim,
      fun a => a.elim, fun a => a.elim, fun a => a.elim, fun a => a.elim, ?_⟩
    intro c' y hy
    obtain ⟨q, hq, _⟩ := hmemT c' y hy
    rw [hTe] at hq
    exact hq.elim
  · obtain ⟨f, hf⟩ := hT.exists_eq_range hTn
    let c : ℕ → AlgChart p σ e := fun n =>
      (f n).1.restr (ptsIn p σ (B.U (f n).2)) (isOpen_ptsIn _)
    refine ⟨ℕ, inferInstance, c, fun n => (f n).2, disjointed fun n => (c n).e.source, ?_, ?_, ?_, ?_, ?_⟩
    · intro n
      show (c n).e.source ⊆ _
      simp only [c]
      rw [AlgChart.restr_source]
      exact inter_subset_right
    · exact MeasurableSet.disjointed fun n => (c n).e.open_source.measurableSet
    · exact fun n => disjointed_subset _ n
    · exact disjoint_disjointed _
    · intro c' y hy
      rw [iUnion_disjointed]
      obtain ⟨q, hq, hyq⟩ := hmemT c' y hy
      rw [hf] at hq
      obtain ⟨n, rfl⟩ := hq
      exact mem_iUnion.2 ⟨n, hyq⟩

theorem lintegral_cone [IsIntegral Z] (hE : Emb p s) (hφ : φ.IsCInf) (hF : IsFS φ s h)
    {J : Ideal (MvPolynomial (Fin m) ℂ)}
    (hJ : ∀ x, (∀ r ∈ J, eval x r = 0) ↔ ∀ q ∈ ptIdeal p s (genericPoint Z), eval₂ σ x q = 0)
    {n : ℕ} {q : MvPolynomial (Fin m) R} (hn : q.IsHomogeneous n)
    (hq : ∀ y : CxPts p σ, eval₂ σ (coords p σ hE.isLB s y) q ≠ 0 → ∃ c : AlgChart p σ e, y ∈ c.e.source)
    (hnull : Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
      ({0} ∪ coneBall h J ∩ {y | eval₂ σ (h.pointOf y) q = 0}) = 0)
    {F : EuclideanSpace ℂ (Fin m) → ℝ≥0∞} (hm : Measurable F) (h0 : ∀ t : ℂ, t ≠ 0 → ∀ x, F (t • x) = F x) :
    ∫⁻ y in coneBall h J, F y ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) =
      Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
          {y : EuclideanSpace ℂ (Fin m) | ‖y‖ < 1 ∧ ∀ j : Fin m, e + 1 ≤ (j : ℕ) → y j = 0} *
        ∫⁻ y, F (euc h (coords p σ hE.isLB s y)) ∂φ.chernPart e 1 := by
  classical
  obtain ⟨ι, hι, c, ia, A, hsub, hAm, hAs, hdisj, hcov⟩ := exists_parts (p := p) (σ := σ) (e := e) hE.isLB
  haveI := hι
  have hpt_smul : ∀ (t : ℂ) (w : EuclideanSpace ℂ (Fin m)), h.pointOf (t • w) = t • h.pointOf w := by
    intro t w
    conv_lhs => rw [← euc_pointOf h w]
    rw [← euc_smul, pointOf_euc]
  have hFco : ∀ j y, y ∈ ptsIn p σ (B.U j) →
      F (euc h (coords p σ hE.isLB s y)) = F (euc h (loc p s σ j y)) := by
    intro j y hy
    obtain ⟨k, hk, hkl⟩ := loc_eq_smul (s := s) (mem_pick hE.isLB y) hy
    have hco : coords p σ hE.isLB s y = loc p s σ (pick hE.isLB y) y := rfl
    rw [hco, hkl, euc_smul, h0 k hk]
  have hvx : ∀ a, ∀ y ∈ A a, WithLp.toLp 2 (sheet s h (c a) (ia a) ((c a).e y).ofLp) =
      euc h (loc p s σ (ia a) y) := fun a y hy => toLp_sheet (c a) (ia a) (hAs a hy)
  have hx_of : ∀ a (x : Fin e → ℂ) y, (c a).e y = WithLp.toLp 2 x → x = ((c a).e y).ofLp := by
    intro a x y hyx
    rw [hyx, WithLp.ofLp_toLp]
  have hcond : ∀ a, IsOpen ((WithLp.toLp 2 : (Fin e → ℂ) → V e) ⁻¹'
        ((c a).e.target ∩ (c a).e.symm ⁻¹' ptsIn p σ (B.U (ia a)))) ∧
      MeasurableSet ((WithLp.toLp 2 : (Fin e → ℂ) → V e) ⁻¹' ((c a).e '' A a)) ∧
      (WithLp.toLp 2 : (Fin e → ℂ) → V e) ⁻¹' ((c a).e '' A a) ⊆
        (WithLp.toLp 2 : (Fin e → ℂ) → V e) ⁻¹' ((c a).e.target ∩ (c a).e.symm ⁻¹' ptsIn p σ (B.U (ia a))) ∧
      DifferentiableOn ℂ (sheet s h (c a) (ia a)) ((WithLp.toLp 2 : (Fin e → ℂ) → V e) ⁻¹'
        ((c a).e.target ∩ (c a).e.symm ⁻¹' ptsIn p σ (B.U (ia a)))) := by
    intro a
    refine ⟨isOpen_dom (c a) (ia a), (measurableSet_image (c a).e (hAm a) (hAs a)).preimage
      (PiLp.continuous_toLp 2 _).measurable, ?_, differentiableOn_sheet (c a) (ia a)⟩
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hx
    refine ⟨?_, ?_⟩
    · rw [← hyx]
      exact (c a).e.map_source (hAs a hy)
    · rw [← hyx, Set.mem_preimage, (c a).e.left_inv (hAs a hy)]
      exact hsub a (hAs a hy)
  have hne : ∀ a, ∀ x ∈ (WithLp.toLp 2 : (Fin e → ℂ) → V e) ⁻¹' ((c a).e '' A a),
      sheet s h (c a) (ia a) x ≠ 0 := by
    intro a x hx
    obtain ⟨y, hy, hyx⟩ := hx
    rw [hx_of a x y hyx]
    exact sheet_ne_zero hE (c a) (hAs a hy) (hsub a (hAs a hy))
  have hinj : InjOn (fun q : ι × (Fin e → ℂ) × ℂ => q.2.2 • WithLp.toLp 2 (sheet s h (c q.1) (ia q.1) q.2.1))
      {q | q.2.1 ∈ (WithLp.toLp 2 : (Fin e → ℂ) → V e) ⁻¹' ((c q.1).e '' A q.1) ∧ q.2.2 ≠ 0} := by
    rintro ⟨a, x, t⟩ ⟨hx, ht⟩ ⟨a', x', t'⟩ ⟨hx', ht'⟩ heq
    simp only at heq hx hx' ht ht'
    obtain ⟨y, hy, hyx⟩ := hx
    obtain ⟨y', hy', hyx'⟩ := hx'
    rw [hx_of a x y hyx, hvx a y hy, hx_of a' x' y' hyx', hvx a' y' hy'] at heq
    have h2 := congrArg h.pointOf heq
    rw [hpt_smul, hpt_smul, pointOf_euc, pointOf_euc] at h2
    have hyy : y = y' := eq_of_loc hE (hsub a (hAs a hy)) (hsub a' (hAs a' hy')) ht ht' h2
    subst hyy
    have haa : a = a' := by
      by_contra hna
      exact Set.disjoint_left.1 (hdisj hna) hy hy'
    subst haa
    have hxx : x = x' := (hx_of a x y hyx).trans (hx_of a x' y hyx').symm
    subst hxx
    have hw : euc h (loc p s σ (ia a) y) ≠ 0 := by
      intro hz
      apply loc_ne_zero hE (hsub a (hAs a hy))
      apply euc_injective h
      rw [hz]
      simp [euc]
    have htt : t = t' := smul_left_injective ℂ hw heq
    subst htt
    rfl
  have hFm : Measurable fun y => F (euc h (coords p σ hE.isLB s y)) := measurable_coords hE.isLB hm h0
  have harea := area_ball (U := fun a => (WithLp.toLp 2 : (Fin e → ℂ) → V e) ⁻¹'
        ((c a).e.target ∩ (c a).e.symm ⁻¹' ptsIn p σ (B.U (ia a))))
    (D := fun a => (WithLp.toLp 2 : (Fin e → ℂ) → V e) ⁻¹' ((c a).e '' A a))
    (v := fun a => sheet s h (c a) (ia a)) hcond hinj hne hm h0
  have hsub1 : Metric.ball 0 1 ∩ (fun q : ι × (Fin e → ℂ) × ℂ => q.2.2 • WithLp.toLp 2 (sheet s h (c q.1) (ia q.1) q.2.1)) ''
      {q | q.2.1 ∈ (WithLp.toLp 2 : (Fin e → ℂ) → V e) ⁻¹' ((c q.1).e '' A q.1) ∧ q.2.2 ≠ 0} ⊆ coneBall h J := by
    rintro z ⟨hz1, ⟨⟨a, x, t⟩, ⟨hx, ht⟩, rfl⟩⟩
    obtain ⟨y, hy, hyx⟩ := hx
    have hz : t • WithLp.toLp 2 (sheet s h (c a) (ia a) x) = t • euc h (loc p s σ (ia a) y) := by
      rw [hx_of a x y hyx, hvx a y hy]
    refine ⟨mem_ball_zero_iff.1 hz1, ?_⟩
    intro r hr
    show MvPolynomial.eval (h.pointOf (t • WithLp.toLp 2 (sheet s h (c a) (ia a) x))) r = 0
    rw [hz, hpt_smul, pointOf_euc]
    exact (hJ _).2 (fun q' hq' => eval₂_loc_eq_zero (hsub a (hAs a hy)) hq' t) r hr
  have hsub2 : coneBall h J \ (Metric.ball 0 1 ∩ (fun q : ι × (Fin e → ℂ) × ℂ => q.2.2 • WithLp.toLp 2 (sheet s h (c q.1) (ia q.1) q.2.1)) ''
      {q | q.2.1 ∈ (WithLp.toLp 2 : (Fin e → ℂ) → V e) ⁻¹' ((c q.1).e '' A q.1) ∧ q.2.2 ≠ 0}) ⊆
      {0} ∪ coneBall h J ∩ {y | eval₂ σ (h.pointOf y) q = 0} := by
    rintro z ⟨hzc, hzn⟩
    by_contra hcon
    have hz0 : z ≠ 0 := fun hz => hcon (Or.inl hz)
    have hq0 : eval₂ σ (h.pointOf z) q ≠ 0 := fun hz => hcon (Or.inr ⟨hzc, hz⟩)
    apply hzn
    refine ⟨mem_ball_zero_iff.2 hzc.1, ?_⟩
    have hx'0 : h.pointOf z ≠ 0 := by
      intro hz
      apply hz0
      rw [← euc_pointOf h z, hz]
      simp [euc]
    have hx'J : ∀ q' ∈ ptIdeal p s (genericPoint Z), eval₂ σ (h.pointOf z) q' = 0 := (hJ _).1 hzc.2
    obtain ⟨y, k, hk, hxk⟩ := exists_loc hE hx'0 hx'J
    have hco : coords p σ hE.isLB s y = loc p s σ (pick hE.isLB y) y := rfl
    have hqy : eval₂ σ (coords p σ hE.isLB s y) q ≠ 0 := by
      intro hz
      apply hq0
      rw [hxk]
      have hfun : (k • loc p s σ (pick hE.isLB y) y) = fun l => k * loc p s σ (pick hE.isLB y) y l := rfl
      rw [hfun, eval₂_mul_of_isHomogeneous σ k _ hn, ← hco, hz, mul_zero]
    obtain ⟨c', hc'⟩ := hq y hqy
    obtain ⟨a, hya⟩ := mem_iUnion.1 (hcov c' hc')
    obtain ⟨k', hk', hkl⟩ := loc_eq_smul (s := s) (mem_pick hE.isLB y) (hsub a (hAs a hya))
    refine ⟨(a, ((c a).e y).ofLp, k * k'), ⟨⟨y, hya, (WithLp.toLp_ofLp 2 _).symm⟩, mul_ne_zero hk hk'⟩, ?_⟩
    show (k * k') • WithLp.toLp 2 (sheet s h (c a) (ia a) ((c a).e y).ofLp) = z
    rw [hvx a y hya, mul_smul, ← euc_smul, ← euc_smul, ← hkl, ← hxk, euc_pointOf]
  have hae : coneBall h J =ᵐ[Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)]
      (Metric.ball 0 1 ∩ (fun q : ι × (Fin e → ℂ) × ℂ => q.2.2 • WithLp.toLp 2 (sheet s h (c q.1) (ia q.1) q.2.1)) ''
      {q | q.2.1 ∈ (WithLp.toLp 2 : (Fin e → ℂ) → V e) ⁻¹' ((c q.1).e '' A q.1) ∧ q.2.2 ≠ 0} : Set _) := by
    rw [ae_eq_set]
    refine ⟨measure_mono_null hsub2 hnull, ?_⟩
    rw [diff_eq_empty.2 hsub1, measure_empty]
  have hpiece : ∀ a, ∫⁻ x in (WithLp.toLp 2 : (Fin e → ℂ) → V e) ⁻¹' ((c a).e '' A a),
      F (WithLp.toLp 2 (sheet s h (c a) (ia a) x)) * ENNReal.ofReal (fsDens (sheet s h (c a) (ia a)) x) =
      ∫⁻ y in A a, F (euc h (coords p σ hE.isLB s y)) ∂φ.chernPart e 1 := by
    intro a
    rw [lintegral_chart hE hφ hF (c a) (hsub a) (hAm a) (hAs a) hFm]
    refine setLIntegral_congr_fun (hcond a).2.1 fun x hx => ?_
    obtain ⟨y, hy, hyx⟩ := hx
    have hsy : (c a).e.symm (WithLp.toLp 2 x) = y := by rw [← hyx, (c a).e.left_inv (hAs a hy)]
    simp only
    rw [hsy, hFco (ia a) y (hsub a (hAs a hy)), ← hvx a y hy, ← hx_of a x y hyx]
  have hWm : MeasurableSet (⋃ a, A a) := MeasurableSet.iUnion hAm
  have hres : (φ.chernPart e 1).restrict (⋃ a, A a) = φ.chernPart e 1 := by
    apply Measure.restrict_eq_self_of_ae_mem
    rw [ae_iff]
    have hcm : ∀ c' : AlgChart p σ e, ∀ ρ : CxPts p σ → ℝ≥0∞,
        chartMeas c'.e ρ ≤ (chartMeas c'.e ρ).restrict (⋃ a, A a) := by
      intro c' ρ
      rw [Measure.restrict_eq_self_of_ae_mem]
      rw [ae_iff]
      show chartMeas c'.e ρ (⋃ a, A a)ᶜ = 0
      rw [chartMeas_apply _ _ hWm.compl]
      have hemp : c'.e.source ∩ (⋃ a, A a)ᶜ = ∅ := by
        ext y
        simp only [mem_inter_iff, mem_compl_iff, mem_empty_iff_false, iff_false, not_and, not_not]
        exact fun hy => hcov c' hy
      rw [hemp, Set.image_empty, Measure.restrict_empty, lintegral_zero_measure]
    have key : ∀ μs : AlgChart p σ e → Measure (CxPts p σ), (∀ c', μs c' ≤ (μs c').restrict (⋃ a, A a)) →
        (⨆ c', μs c') (⋃ a, A a)ᶜ = 0 := by
      intro μs hμ
      have hle : (⨆ c', μs c') ≤ (⨆ c', μs c').restrict (⋃ a, A a) :=
        iSup_le fun c' => (hμ c').trans (Measure.restrict_mono subset_rfl (le_iSup μs c'))
      refine le_antisymm ((Measure.le_iff'.1 hle _).trans ?_) (zero_le)
      rw [Measure.restrict_apply' hWm, compl_inter_self, measure_empty]
    unfold Weight.chernPart glueMeas
    exact key _ fun c' => hcm c' _
  rw [setLIntegral_congr hae, harea]
  congr 1
  rw [tsum_congr hpiece, ← lintegral_iUnion hAm hdisj, hres]

end ChowFormHeightComparison₂.CF.C
