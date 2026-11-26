module

public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.NatCastMulCoeffOfPderivEq
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EnormPowLeInvMeasureMulLintegralBall
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ConjTransposeBoostMulSignatureMulBoost
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.MulConjTransposeEqOneOfOrthonormal
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIdealInClassOfNormLeSqrtDiscr
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsLinearIndependentNormLeSuccMin

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FormalExpMulFormalExpNeg
namespace GlobalTheory.FormalCalc

open MvPowerSeries

variable {σ τ A B : Type*} [CommRing A] [Algebra ℚ A] [CommRing B] [Algebra ℚ B]

noncomputable def formalExp (f : MvPowerSeries σ A) : MvPowerSeries σ A :=
  (PowerSeries.exp A).subst f

noncomputable def formalLog (g : MvPowerSeries σ A) : MvPowerSeries σ A :=
  (PowerSeries.log A).subst (g - 1)

omit [Algebra ℚ A] in
private theorem hasSubst_sub_one {g : MvPowerSeries σ A} (hg : constantCoeff g = 1) :
    PowerSeries.HasSubst (g - 1) :=
  PowerSeries.HasSubst.of_constantCoeff_zero (by simp [hg])

theorem constantCoeff_formalExp {f : MvPowerSeries σ A} (hf : constantCoeff f = 0) :
    constantCoeff (formalExp f) = 1 := by
  have h := constantCoeff_subst_of_zero (σ := Unit) (a := fun _ => f)
    (PowerSeries.HasSubst.of_constantCoeff_zero hf).const (fun _ => hf) (PowerSeries.exp A)
  rw [formalExp, PowerSeries.subst, h, ← PowerSeries.constantCoeff_eq]
  simp

theorem constantCoeff_formalLog {g : MvPowerSeries σ A} (hg : constantCoeff g = 1) :
    constantCoeff (formalLog g) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero (by simp [hg]) _ PowerSeries.constantCoeff_log

theorem isUnit_formalExp {f : MvPowerSeries σ A} (hf : constantCoeff f = 0) :
    IsUnit (formalExp f) :=
  isUnit_iff_constantCoeff.mpr (by rw [constantCoeff_formalExp hf]; exact isUnit_one)

theorem pderiv_formalExp {f : MvPowerSeries σ A} (hf : constantCoeff f = 0) (i : σ) :
    pderiv (R := A) i (formalExp f) = formalExp f * pderiv (R := A) i f := by
  rw [formalExp, pderiv_powerSeries_subst (PowerSeries.HasSubst.of_constantCoeff_zero hf),
    PowerSeries.derivative_exp]

private theorem one_add_X_mul_deriv_log :
    (1 + PowerSeries.X) * PowerSeries.derivative (R := A) (PowerSeries.log A) = 1 := by
  rw [PowerSeries.deriv_log]
  ext n
  rw [add_mul, one_mul, map_add (f := _)]
  cases n with
  | zero => simp
  | succ n => simp [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_one, pow_succ]

theorem mul_pderiv_formalLog {g : MvPowerSeries σ A} (hg : constantCoeff g = 1) (i : σ) :
    g * pderiv (R := A) i (formalLog g) = pderiv (R := A) i g := by
  have hs := hasSubst_sub_one hg
  have h := congrArg (PowerSeries.substAlgHom (R := A) hs) (one_add_X_mul_deriv_log (A := A))
  rw [map_mul, map_add (f := _), map_one, PowerSeries.substAlgHom_X, add_sub_cancel,
    PowerSeries.coe_substAlgHom] at h
  rw [formalLog, pderiv_powerSeries_subst hs, ← mul_assoc, h, map_sub, pderiv_one, sub_zero,
    one_mul]

theorem eq_formalExp_of_pderiv {f u : MvPowerSeries σ A} (hf : constantCoeff f = 0)
    (hu : constantCoeff u = 1) (h : ∀ i, pderiv (R := A) i u = u * pderiv (R := A) i f) :
    u = formalExp f := by
  haveI : HasUniqueDiv A := IsAddTorsionFree.of_module_rat A
  have hn : constantCoeff (-f) = 0 := by simp [hf]
  have key : ∀ v : MvPowerSeries σ A, constantCoeff v = 1 →
      (∀ i, pderiv (R := A) i v = v * pderiv (R := A) i f) → v * formalExp (-f) = 1 := by
    intro v hv hd
    refine pderiv.ext (fun i => ?_) (by simp [hv, constantCoeff_formalExp hn])
    rw [Derivation.leibniz, pderiv_formalExp hn, hd, map_neg, pderiv_one, smul_eq_mul,
      smul_eq_mul]
    ring
  exact (isUnit_formalExp hn).mul_right_cancel
    ((key u hu h).trans (key _ (constantCoeff_formalExp hf) (pderiv_formalExp hf)).symm)

theorem eq_formalLog_of_pderiv {g u : MvPowerSeries σ A} (hg : constantCoeff g = 1)
    (hu : constantCoeff u = 0) (h : ∀ i, g * pderiv (R := A) i u = pderiv (R := A) i g) :
    u = formalLog g := by
  haveI : HasUniqueDiv A := IsAddTorsionFree.of_module_rat A
  have hunit : IsUnit g := isUnit_iff_constantCoeff.mpr (hg ▸ isUnit_one)
  refine pderiv.ext (fun i => hunit.mul_left_cancel ?_) (by rw [hu, constantCoeff_formalLog hg])
  rw [h, mul_pderiv_formalLog hg]

@[simp] theorem formalExp_zero : formalExp (0 : MvPowerSeries σ A) = 1 :=
  (eq_formalExp_of_pderiv (by simp) (by simp) fun i => by simp).symm

@[simp] theorem formalLog_one : formalLog (1 : MvPowerSeries σ A) = 0 :=
  (eq_formalLog_of_pderiv (by simp) (by simp) fun i => by simp).symm

theorem formalLog_mul {f g : MvPowerSeries σ A} (hf : constantCoeff f = 1)
    (hg : constantCoeff g = 1) : formalLog (f * g) = formalLog f + formalLog g := by
  refine (eq_formalLog_of_pderiv (by simp [hf, hg])
    (by simp [constantCoeff_formalLog hf, constantCoeff_formalLog hg]) fun i => ?_).symm
  rw [Derivation.leibniz, ← mul_pderiv_formalLog hf, ← mul_pderiv_formalLog hg, map_add (f := _),
    smul_eq_mul, smul_eq_mul]
  ring

theorem formalLog_prod {κ : Type*} (s : Finset κ) {g : κ → MvPowerSeries σ A}
    (hg : ∀ k ∈ s, constantCoeff (g k) = 1) :
    formalLog (∏ k ∈ s, g k) = ∑ k ∈ s, formalLog (g k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert k s hk ih =>
    have h' : ∀ j ∈ s, constantCoeff (g j) = 1 := fun j hj => hg j (Finset.mem_insert_of_mem hj)
    rw [Finset.sum_insert hk, Finset.prod_insert hk, formalLog_mul
      (hg k (Finset.mem_insert_self _ _)) (by rw [map_prod]; exact Finset.prod_eq_one h'), ih h']

theorem formalLog_pow (n : ℕ) {g : MvPowerSeries σ A} (hg : constantCoeff g = 1) :
    formalLog (g ^ n) = n • formalLog g := by
  simpa using formalLog_prod (Finset.range n) (g := fun _ => g) fun _ _ => hg

theorem subst_formalExp {a : σ → MvPowerSeries τ A} (ha : HasSubst a)
    {f : MvPowerSeries σ A} (hf : constantCoeff f = 0) :
    subst a (formalExp f) = formalExp (subst a f) := by
  rw [formalExp, formalExp, PowerSeries.subst, PowerSeries.subst,
    subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero hf).const ha]

theorem subst_formalLog {a : σ → MvPowerSeries τ A} (ha : HasSubst a)
    {g : MvPowerSeries σ A} (hg : constantCoeff g = 1) :
    subst a (formalLog g) = formalLog (subst a g) := by
  rw [formalLog, formalLog, PowerSeries.subst, PowerSeries.subst,
    subst_comp_subst_apply (hasSubst_sub_one hg).const ha, subst_sub ha, subst_one' ha]

theorem map_formalLog (φ : A →+* B) {g : MvPowerSeries σ A} (hg : constantCoeff g = 1) :
    map φ (formalLog g) = formalLog (map φ g) := by
  refine eq_formalLog_of_pderiv (by simp [hg]) (by simp [constantCoeff_formalLog hg]) fun i => ?_
  rw [pderiv_map, pderiv_map, ← map_mul, mul_pderiv_formalLog hg]

end GlobalTheory.FormalCalc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EventuallyIteratedFDerivEqZeroOfRealSubspace
open Metric Set Filter
open scoped Topology

namespace GlobalTheory.SCV

section General

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem fderiv_apply_eq_zero_of_frequently {f : E → V} {x s : E} (hf : DifferentiableAt ℂ f x)
    (h : ∃ᶠ t in 𝓝[≠] (0 : ℂ), f (x + t • s) = f x) : fderiv ℂ f x s = 0 := by
  have h1 : HasDerivAt (fun t : ℂ => f (x + t • s)) (fderiv ℂ f x s) 0 :=
    hf.hasFDerivAt.hasLineDerivAt s
  rw [hasDerivAt_iff_tendsto_slope_zero] at h1
  refine tendsto_nhds_unique_of_frequently_eq h1 tendsto_const_nhds (h.mono fun t ht => ?_)
  simp [ht]

theorem frequently_nhdsNE_of_eventually_ofReal {p : ℂ → Prop}
    (h : ∀ᶠ t : ℝ in 𝓝 0, p t) : ∃ᶠ t in 𝓝[≠] (0 : ℂ), p t := by
  have h1 : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[≠] 0) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · exact (Complex.continuous_ofReal.tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simpa using ht
  exact h1.frequently (h.filter_mono nhdsWithin_le_nhds).frequently

theorem fderiv_eq_zero_of_real_lines {f : E → V} {x : E} {S : Set E}
    (hS : Submodule.span ℂ S = ⊤) (hf : DifferentiableAt ℂ f x)
    (h : ∀ s ∈ S, ∀ᶠ t : ℝ in 𝓝 0, f (x + (t : ℂ) • s) = f x) : fderiv ℂ f x = 0 := by
  have : (fderiv ℂ f x : E →ₗ[ℂ] V) = 0 :=
    LinearMap.ext_on hS fun s hs => fderiv_apply_eq_zero_of_frequently hf
      (frequently_nhdsNE_of_eventually_ofReal (p := fun t => f (x + t • s) = f x) (h s hs))
  ext v
  exact LinearMap.congr_fun this v

theorem eq_of_eventually_real_lines {f : E → V} {U S : Set E}
    (hS : Submodule.span ℂ S = ⊤) (hU : IsOpen U) (hU' : IsPreconnected U)
    (hf : DifferentiableOn ℂ f U)
    (h : ∀ z ∈ U, ∀ s ∈ S, ∀ᶠ t : ℝ in 𝓝 0, f (z + (t : ℂ) • s) = f z)
    {z w : E} (hz : z ∈ U) (hw : w ∈ U) : f z = f w :=
  hU.is_const_of_fderiv_eq_zero hU' hf
    (fun x hx => fderiv_eq_zero_of_real_lines hS (hf.differentiableAt (hU.mem_nhds hx)) (h x hx))
    hz hw

theorem eq_of_invariant_real_lines {f : E → V} {U S : Set E}
    (hS : Submodule.span ℂ S = ⊤) (hU : IsOpen U) (hU' : IsPreconnected U)
    (hf : DifferentiableOn ℂ f U)
    (h : ∀ z ∈ U, ∀ s ∈ S, ∀ t : ℝ, z + (t : ℂ) • s ∈ U → f (z + (t : ℂ) • s) = f z)
    {z w : E} (hz : z ∈ U) (hw : w ∈ U) : f z = f w := by
  refine eq_of_eventually_real_lines hS hU hU' hf (fun x hx s hs => ?_) hz hw
  have h1 : Tendsto (fun t : ℝ => x + (t : ℂ) • s) (𝓝 0) (𝓝 x) :=
    Continuous.tendsto' (by fun_prop) _ _ (by simp)
  exact (h1.eventually (hU.mem_nhds hx)).mono fun t ht => h x hx s hs t ht

variable [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

theorem eq_of_invariant_realSubspace {f : E → V} {U : Set E} {S : Submodule ℝ E}
    (hS : Submodule.span ℂ (S : Set E) = ⊤) (hU : IsOpen U) (hU' : IsPreconnected U)
    (hf : DifferentiableOn ℂ f U) (h : ∀ z ∈ U, ∀ s ∈ S, z + s ∈ U → f (z + s) = f z)
    {z w : E} (hz : z ∈ U) (hw : w ∈ U) : f z = f w := by
  refine eq_of_invariant_real_lines hS hU hU' hf (fun x hx s hs t ht => h x hx _ ?_ ht) hz hw
  rw [show (t : ℂ) • s = t • s from algebraMap_smul ℂ t s]
  exact S.smul_mem t hs

variable [FiniteDimensional ℂ E] [CompleteSpace V]

end General

section Coordinates

variable {ι V : Type*} [Fintype ι] [NormedAddCommGroup V] [NormedSpace ℂ V]

noncomputable def scaledRealPoints (ι : Type*) (a : ℂ) : Submodule ℝ (ι → ℂ) where
  carrier := {z | ∃ x : ι → ℝ, z = fun i => a * x i}
  add_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, by ext i; simp [mul_add]⟩
  zero_mem' := ⟨0, by ext i; simp⟩
  smul_mem' := by
    rintro t _ ⟨x, rfl⟩
    exact ⟨t • x, by ext i; simp [mul_left_comm]⟩


omit [Fintype ι] in
theorem span_scaledRealPoints {a : ℂ} (ha : a ≠ 0) :
    Submodule.span ℂ (scaledRealPoints ι a : Set (ι → ℂ)) = ⊤ := by
  refine eq_top_iff.mpr fun z _ => ?_
  have e : z = a⁻¹ • (fun i => a * ((z i).re : ℂ))
      + (a⁻¹ * Complex.I) • (fun i => a * ((z i).im : ℂ)) := by
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [← Complex.re_add_im (z i)]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Complex.add_im,
      Complex.mul_im, zero_add]
    field_simp
  rw [e]
  exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))

theorem eq_of_invariant_real {f : (ι → ℂ) → V} {U : Set (ι → ℂ)}
    (hU : IsOpen U) (hU' : IsPreconnected U) (hf : DifferentiableOn ℂ f U)
    (h : ∀ z ∈ U, ∀ x : ι → ℝ, (z + fun i => (x i : ℂ)) ∈ U → f (z + fun i => (x i : ℂ)) = f z)
    {z w : ι → ℂ} (hz : z ∈ U) (hw : w ∈ U) : f z = f w := by
  refine eq_of_invariant_realSubspace (span_scaledRealPoints one_ne_zero) hU hU' hf ?_ hz hw
  rintro y hy _ ⟨x, rfl⟩
  simpa only [one_mul] using h y hy x

variable [CompleteSpace V]

end Coordinates

end GlobalTheory.SCV
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegrableOnOfNormLeSumAbsLogAddLogLog
open MeasureTheory Metric Set Filter Topology
open scoped ENNReal Real

namespace GlobalTheory

section Holomorphic

theorem log_norm_le_circleAverage_log_norm {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g (closedBall 0 1))
    (h0 : g 0 ≠ 0) : Real.log ‖g 0‖ ≤ Real.circleAverage (fun z => Real.log ‖g z‖) 0 1 := by
  have hg' : AnalyticOnNhd ℂ g (closedBall 0 |(1 : ℝ)|) := by simpa using hg
  rw [hg'.circleAverage_log_norm h0, le_add_iff_nonneg_left]
  refine finsum_nonneg fun u => ?_
  by_cases hu : u ∈ closedBall (0 : ℂ) |(1 : ℝ)|
  · refine mul_nonneg (by exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hg' u) ?_
    rcases eq_or_ne u 0 with rfl | h
    · simp
    · refine Real.log_nonneg ?_
      have h1 : ‖u‖ ≤ 1 := by simpa using hu
      simpa using (one_le_inv₀ (norm_pos_iff.2 h)).2 h1
  · simp [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu]

private noncomputable def logGap (M : ℝ) (y : ℂ) : ℝ≥0∞ :=
  if y = 0 then ∞ else ENNReal.ofReal (Real.log M - Real.log ‖y‖)

private theorem measurable_logGap (M : ℝ) : Measurable (logGap M) :=
  Measurable.ite (measurableSet_singleton 0) measurable_const (by fun_prop)

private theorem lintegral_logGap_circle_le {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g (closedBall 0 1))
    (h0 : g 0 ≠ 0) {M : ℝ} (hM : ∀ z ∈ closedBall (0 : ℂ) 1, ‖g z‖ ≤ M) :
    ∫⁻ t in Ioc 0 (2 * π), logGap M (g (circleMap 0 1 t)) ≤
      ENNReal.ofReal (2 * π * (Real.log M - Real.log ‖g 0‖)) := by
  have h2 : (0 : ℝ) < 2 * π := by positivity
  have hne : ∀ᵐ t ∂(volume.restrict (Ioc 0 (2 * π))), g (circleMap 0 1 t) ≠ 0 := by
    have h1 := hg.preimage_zero_mem_codiscreteWithin h0 (mem_closedBall_self zero_le_one)
      (isConnected_closedBall zero_le_one)
    have h3 : g ⁻¹' {0}ᶜ ∈ codiscreteWithin (sphere (0 : ℂ) |(1 : ℝ)|) :=
      codiscreteWithin_mono (by simpa using sphere_subset_closedBall) h1
    exact ae_restrict_le_codiscreteWithin measurableSet_Ioc
      (codiscreteWithin_mono (subset_univ _) (circleMap_preimage_codiscrete one_ne_zero h3))
  have hint : IntegrableOn (fun t => Real.log ‖g (circleMap 0 1 t)‖) (Ioc 0 (2 * π)) := by
    have h1 : CircleIntegrable (fun z => Real.log ‖g z‖) 0 1 :=
      MeromorphicOn.circleIntegrable_log_norm
        (hg.mono (by simpa using sphere_subset_closedBall)).meromorphicOn
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le h2.le).1 h1
  have hc : IntegrableOn (fun _ : ℝ => Real.log M) (Ioc 0 (2 * π)) :=
    integrableOn_const measure_Ioc_lt_top.ne
  have hJ := log_norm_le_circleAverage_log_norm hg h0
  rw [Real.circleAverage, intervalIntegral.integral_of_le h2.le, smul_eq_mul,
    le_inv_mul_iff₀ h2] at hJ
  calc ∫⁻ t in Ioc 0 (2 * π), logGap M (g (circleMap 0 1 t))
      = ∫⁻ t in Ioc 0 (2 * π), ENNReal.ofReal (Real.log M - Real.log ‖g (circleMap 0 1 t)‖) := by
        refine lintegral_congr_ae ?_
        filter_upwards [hne] with t ht
        simp [logGap, ht]
    _ = ENNReal.ofReal (∫ t in Ioc 0 (2 * π), (Real.log M - Real.log ‖g (circleMap 0 1 t)‖)) := by
        refine (ofReal_integral_eq_lintegral_ofReal (hc.sub hint) ?_).symm
        filter_upwards [hne] with t ht
        exact sub_nonneg.2 (Real.log_le_log (norm_pos_iff.2 ht)
          (hM _ (sphere_subset_closedBall (circleMap_mem_sphere 0 zero_le_one t))))
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [integral_sub hc hint]
        simp only [integral_const, MeasurableSet.univ, measureReal_restrict_apply, univ_inter,
          Real.volume_real_Ioc, sub_zero, max_eq_left h2.le, smul_eq_mul]
        linarith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [MeasurableSpace E] [BorelSpace E]

theorem integrableOn_log_norm_ball_zero (μ : Measure E) [μ.IsAddHaarMeasure] {f : E → ℂ}
    {r M : ℝ} (hf : DifferentiableOn ℂ f (ball 0 r)) (hM : ∀ z ∈ ball (0 : E) r, ‖f z‖ ≤ M)
    (h0 : f 0 ≠ 0) :
    (∀ᵐ z ∂(μ.restrict (ball 0 r)), f z ≠ 0) ∧
      IntegrableOn (fun z => Real.log ‖f z‖) (ball 0 r) μ := by
  classical
  have : ProperSpace E := FiniteDimensional.proper ℂ E
  have h2 : (0 : ℝ) < 2 * π := by positivity
  have hn : ∀ t, ‖circleMap 0 1 t‖ = 1 := fun t => by simp
  set F : E → ℂ := (ball (0 : E) r).piecewise f 0 with hF
  have hFm : Measurable F :=
    hf.continuousOn.measurable_piecewise continuousOn_const measurableSet_ball
  set G : E → ℝ≥0∞ := (ball (0 : E) r).indicator fun z => logGap M (F z) with hG
  have hGm : Measurable G := ((measurable_logGap M).comp hFm).indicator measurableSet_ball
  have hj : Measurable fun p : ℝ × E => G (circleMap 0 1 p.1 • p.2) := by
    refine hGm.comp (Continuous.measurable ?_)
    exact ((continuous_circleMap 0 1).comp continuous_fst).smul continuous_snd
  have hA : ∫⁻ t in Ioc 0 (2 * π), ∫⁻ z, G (circleMap 0 1 t • z) ∂μ =
      (∫⁻ z in ball 0 r, logGap M (F z) ∂μ) * ENNReal.ofReal (2 * π) := by
    have h4 : ∀ t, ∫⁻ z, G (circleMap 0 1 t • z) ∂μ = ∫⁻ z in ball 0 r, logGap M (F z) ∂μ :=
      fun t => by
        rw [(measurePreserving_smul_of_norm_eq_one μ (hn t)).lintegral_comp hGm, hG,
          lintegral_indicator measurableSet_ball]
    simp [h4]
  have hsm : ∀ z ∈ ball (0 : E) r, ∀ c ∈ closedBall (0 : ℂ) 1, c • z ∈ ball (0 : E) r := by
    intro z hz c hc
    rw [mem_ball_zero_iff] at hz ⊢
    rw [mem_closedBall_zero_iff] at hc
    calc ‖c • z‖ ≤ 1 * ‖z‖ := by rw [norm_smul]; gcongr
      _ < r := by simpa using hz
  have hB : ∫⁻ t in Ioc 0 (2 * π), ∫⁻ z, G (circleMap 0 1 t • z) ∂μ < ∞ := by
    rw [lintegral_lintegral_swap hj.aemeasurable]
    calc ∫⁻ z, ∫⁻ t in Ioc 0 (2 * π), G (circleMap 0 1 t • z) ∂volume ∂μ
        ≤ ∫⁻ z, (ball (0 : E) r).indicator
          (fun _ => ENNReal.ofReal (2 * π * (Real.log M - Real.log ‖f 0‖))) z ∂μ := by
          refine lintegral_mono fun z => ?_
          by_cases hz : z ∈ ball (0 : E) r
          · have h5 : ∀ t, G (circleMap 0 1 t • z) = logGap M (f (circleMap 0 1 t • z)) :=
              fun t => by
                have := hsm z hz _ (mem_closedBall_zero_iff.2 (hn t).le)
                rw [hG, indicator_of_mem this, hF, piecewise_eq_of_mem _ _ _ this]
            have h6 : AnalyticOnNhd ℂ (fun c : ℂ => f (c • z)) (closedBall 0 1) := by
              have ho : IsOpen ((fun c : ℂ => c • z) ⁻¹' ball 0 r) :=
                isOpen_ball.preimage (by fun_prop)
              have hd : DifferentiableOn ℂ (fun c : ℂ => f (c • z))
                  ((fun c : ℂ => c • z) ⁻¹' ball 0 r) :=
                hf.comp (by fun_prop) (mapsTo_preimage _ _)
              exact (hd.analyticOnNhd ho).mono fun c hc => hsm z hz c hc
            simp only [indicator_of_mem hz, h5]
            simpa using lintegral_logGap_circle_le h6 (by simpa using h0)
              (fun c hc => hM _ (hsm z hz c hc))
          · have h5 : ∀ t, G (circleMap 0 1 t • z) = 0 := fun t => by
              rw [hG, indicator_of_notMem]
              simpa [norm_smul, hn] using hz
            simp [h5]
      _ < ∞ := by
          rw [lintegral_indicator_const measurableSet_ball]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_ball_lt_top
  rw [hA] at hB
  have hC : ∫⁻ z in ball 0 r, logGap M (F z) ∂μ < ∞ :=
    (ENNReal.lt_top_of_mul_ne_top_left hB.ne (ENNReal.ofReal_pos.2 h2).ne')
  have hFf : F =ᵐ[μ.restrict (ball 0 r)] f :=
    piecewise_ae_eq_restrict measurableSet_ball.nullMeasurableSet
  have hne : ∀ᵐ z ∂(μ.restrict (ball 0 r)), f z ≠ 0 := by
    filter_upwards [ae_lt_top ((measurable_logGap M).comp hFm) hC.ne, hFf] with z hz hz' h
    simp [hz', logGap, h] at hz
  refine ⟨hne, ?_⟩
  have hmeas : AEStronglyMeasurable (fun z => Real.log ‖f z‖) (μ.restrict (ball 0 r)) := by
    have : AEMeasurable f (μ.restrict (ball 0 r)) := ⟨F, hFm, hFf.symm⟩
    exact (Real.measurable_log.comp_aemeasurable this.norm).aestronglyMeasurable
  have hc : IntegrableOn (fun _ : E => Real.log M) (ball 0 r) μ :=
    integrableOn_const measure_ball_lt_top.ne
  have hsub : IntegrableOn (fun z => Real.log M - Real.log ‖f z‖) (ball 0 r) μ := by
    refine ⟨aestronglyMeasurable_const.sub hmeas, ?_⟩
    refine lt_of_eq_of_lt (lintegral_congr_ae ?_) hC
    filter_upwards [hne, hFf, ae_restrict_mem measurableSet_ball] with z hz hz' hzb
    rw [hz', logGap, ite_eq_right hz, Real.eNorm_eq_ofReal]
    exact sub_nonneg.2 (Real.log_le_log (norm_pos_iff.2 hz) (hM z hzb))
  exact (hc.sub hsub).congr (Eventually.of_forall fun z => by simp)

theorem integrableOn_log_norm_ball (μ : Measure E) [μ.IsAddHaarMeasure] {f : E → ℂ} {a : E}
    {r M : ℝ} (hf : DifferentiableOn ℂ f (ball a r)) (hM : ∀ z ∈ ball a r, ‖f z‖ ≤ M)
    (h0 : f a ≠ 0) :
    (∀ᵐ z ∂(μ.restrict (ball a r)), f z ≠ 0) ∧
      IntegrableOn (fun z => Real.log ‖f z‖) (ball a r) μ := by
  have : ProperSpace E := FiniteDimensional.proper ℂ E
  have hm : MapsTo (fun z : E => z + a) (ball 0 r) (ball a r) := fun z hz => by simpa using hz
  obtain ⟨h1, h2⟩ := integrableOn_log_norm_ball_zero μ (f := fun z => f (z + a)) (r := r) (M := M)
    (hf.comp (by fun_prop) hm) (fun z hz => hM _ (hm hz)) (by simpa using h0)
  have hp : MeasurePreserving (fun z : E => z - a) (μ.restrict (ball a r))
      (μ.restrict (ball 0 r)) := by
    have := (measurePreserving_sub_right μ a).restrict_preimage (s := ball 0 r) measurableSet_ball
    convert this using 2
    ext z
    simp [dist_eq_norm]
  refine ⟨?_, ?_⟩
  · simpa using hp.quasiMeasurePreserving.ae h1
  · simpa [Function.comp_def, IntegrableOn] using hp.integrable_comp_of_integrable h2

theorem exists_integrableOn_log_norm_of_frequently_ne_zero (μ : Measure E) [μ.IsAddHaarMeasure]
    {f : E → ℂ} {x : E} (hf : ∀ᶠ z in 𝓝 x, DifferentiableAt ℂ f z) (hx : ∃ᶠ z in 𝓝 x, f z ≠ 0) :
    ∃ r > 0, (∀ᵐ z ∂(μ.restrict (ball x r)), f z ≠ 0) ∧
      IntegrableOn (fun z => Real.log ‖f z‖) (ball x r) μ := by
  have hb : ∀ᶠ z in 𝓝 x, ‖f z‖ ≤ ‖f x‖ + 1 :=
    (hf.self_of_nhds.continuousAt.norm.eventually (gt_mem_nhds (lt_add_one _))).mono
      fun _ h => h.le
  obtain ⟨R, hR, hB⟩ := Metric.eventually_nhds_iff_ball.1 (hf.and hb)
  obtain ⟨a, ha, hax⟩ := (hx.and_eventually (ball_mem_nhds x (by positivity : 0 < R / 3))).exists
  have h1 : ball a (2 * R / 3) ⊆ ball x R := ball_subset_ball' (by linarith)
  have h2 : ball x (R / 3) ⊆ ball a (2 * R / 3) :=
    ball_subset_ball' (by rw [dist_comm] at hax; linarith)
  obtain ⟨h3, h4⟩ := integrableOn_log_norm_ball μ (f := f) (a := a) (r := 2 * R / 3)
    (fun z hz => (hB z (h1 hz)).1.differentiableWithinAt) (fun z hz => (hB z (h1 hz)).2) ha
  exact ⟨R / 3, by positivity, ae_restrict_of_ae_restrict_of_subset h2 h3, h4.mono_set h2⟩

theorem exists_integrableOn_log_norm_div (μ : Measure E) [μ.IsAddHaarMeasure]
    {g h : E → ℂ} {x : E} (hg : ∀ᶠ z in 𝓝 x, DifferentiableAt ℂ g z)
    (hh : ∀ᶠ z in 𝓝 x, DifferentiableAt ℂ h z) (hg0 : ∃ᶠ z in 𝓝 x, g z ≠ 0)
    (hh0 : ∃ᶠ z in 𝓝 x, h z ≠ 0) :
    ∃ r > 0, (∀ᵐ z ∂(μ.restrict (ball x r)), g z ≠ 0 ∧ h z ≠ 0) ∧
      IntegrableOn (fun z => Real.log ‖g z / h z‖) (ball x r) μ := by
  obtain ⟨r, hr, h1, h2⟩ := exists_integrableOn_log_norm_of_frequently_ne_zero μ hg hg0
  obtain ⟨s, hs, h3, h4⟩ := exists_integrableOn_log_norm_of_frequently_ne_zero μ hh hh0
  have e1 : ball x (min r s) ⊆ ball x r := ball_subset_ball (min_le_left _ _)
  have e2 : ball x (min r s) ⊆ ball x s := ball_subset_ball (min_le_right _ _)
  have h5 := (ae_restrict_of_ae_restrict_of_subset e1 h1).and
    (ae_restrict_of_ae_restrict_of_subset e2 h3)
  refine ⟨min r s, lt_min hr hs, h5, ((h2.mono_set e1).sub (h4.mono_set e2)).congr ?_⟩
  filter_upwards [h5] with z hz
  simp [Real.log_div, hz.1, hz.2]

end Holomorphic

section Coordinates

open Bornology

variable {ι : Type*} [Fintype ι]

variable {F : Type*} [NormedAddCommGroup F]

end Coordinates

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsNeZeroForallNormLeOfCovolumeLe
open NumberField Module MeasureTheory Metric Set
open scoped Real ENNReal

namespace GlobalTheory

section Lattice

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

variable [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure]


set_option backward.isDefEq.respectTransparency.types false in
theorem covolume_eq_relIndex_mul_of_haar (L' L : Submodule ℤ V) [DiscreteTopology L']
    [IsZLattice ℝ L'] [DiscreteTopology L] [IsZLattice ℝ L] (h : L' ≤ L) :
    ZLattice.covolume L' μ =
      (L'.toAddSubgroup.relIndex L.toAddSubgroup : ℝ) * ZLattice.covolume L μ := by
  classical
  let b : Basis (Fin (finrank ℝ V)) ℤ L := finBasisOfFinrankEq ℤ L (ZLattice.rank ℝ L)
  let b' : Basis (Fin (finrank ℝ V)) ℤ L' := finBasisOfFinrankEq ℤ L' (ZLattice.rank ℝ L')
  rw [AddSubgroup.relIndex_eq_natAbs_det L'.toAddSubgroup L.toAddSubgroup h b' b,
    Nat.cast_natAbs, Int.cast_abs,
    ZLattice.covolume_eq_det_mul_measureReal L' μ b' (b.ofZLatticeBasis ℝ),
    ZLattice.covolume_eq_measure_fundamentalDomain L μ (ZLattice.isAddFundamentalDomain b μ)]
  congr 2
  rw [Basis.det_apply, Basis.det_apply, Int.cast_det]
  congr; ext i j
  rw [Matrix.map_apply, Basis.toMatrix_apply, Basis.toMatrix_apply]
  exact (b.ofZLatticeBasis_repr_apply ℝ L ⟨b' j, h (SetLike.coe_mem _)⟩ i)

end Lattice

section Strip

end Strip

section TotallyComplex

open InfinitePlace

end TotallyComplex

section CM

open InfinitePlace IsCMField
open scoped nonZeroDivisors

variable {E : Type*} [Field E] [NumberField E] [IsCMField E]

end CM

section Constant

end Constant

section Balls

variable {ι : Type*} [Fintype ι] {W : ι → Type*} [∀ i, NormedAddCommGroup (W i)]
  [∀ i, InnerProductSpace ℝ (W i)] [∀ i, FiniteDimensional ℝ (W i)]
  [∀ i, MeasurableSpace (W i)] [∀ i, BorelSpace (W i)]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

end Balls

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsLinearIndependentSqrtEqSuccMinQuad
noncomputable section

open Module Submodule

namespace GlobalTheory

section General

variable {K : Type*} [DivisionRing K] {V : Type*} [AddCommGroup V] [Module K V]
  {N : V → ℝ} {S : Set V} {n : ℕ}

theorem mem_span_of_lt_succMinOf {v : Fin n → V} (hv : LinearIndependent K v) (hS : ∀ j, v j ∈ S)
    (hN : ∀ j : Fin n, N (v j) ≤ succMinOf K N S (j + 1)) {i : ℕ} (hi : i ≤ n) {x : V}
    (hx : x ∈ S) (hx0 : 0 ≤ N x) (h : N x < succMinOf K N S (i + 1)) :
    x ∈ span K (v '' {j | (j : ℕ) < i}) := by
  have hrank : (n : Cardinal) ≤ Module.rank K (span K S) :=
    natCast_le_rank_span_iff.2 ⟨v, hv, hS⟩
  have key : ∀ i ≤ n, succMinOf K N S i ≤ N x → N x < succMinOf K N S (i + 1) →
      x ∈ span K (v '' {j | (j : ℕ) < i}) := by
    intro i hi h1 h2
    by_contra hx'
    have hw : LinearIndependent K (fun j : Fin i => v (Fin.castLE hi j)) :=
      hv.comp _ (Fin.castLE_injective hi)
    have hr : Set.range (fun j : Fin i => v (Fin.castLE hi j)) = v '' {j | (j : ℕ) < i} := by
      ext y
      constructor
      · rintro ⟨j, rfl⟩; exact ⟨_, j.2, rfl⟩
      · rintro ⟨j, hj, rfl⟩; exact ⟨⟨j, hj⟩, rfl⟩
    have hli : LinearIndependent K
        (Fin.cons x (fun j : Fin i => v (Fin.castLE hi j)) : Fin (i + 1) → V) :=
      linearIndependent_finCons.2 ⟨hw, by rwa [hr]⟩
    refine absurd (succMinOf_le_of_linearIndependent (N := N) (S := S) (i := i + 1) hli (by simp)
      hx0 ?_ ?_) (not_le.2 h2)
    · intro k
      refine Fin.cases hx (fun j => hS _) k
    · intro k
      refine Fin.cases le_rfl (fun j => ?_) k
      exact (hN _).trans ((succMinOf_mono (show (j : ℕ) + 1 ≤ i from j.2)
        ((Nat.cast_le.2 hi).trans hrank)).trans h1)
  induction i with
  | zero => exact key 0 hi (succMinOf_zero.le.trans hx0) h
  | succ m ih =>
    rcases lt_or_ge (N x) (succMinOf K N S (m + 1)) with h1 | h1
    · have hsub : {j : Fin n | (j : ℕ) < m} ⊆ {j : Fin n | (j : ℕ) < m + 1} :=
        fun j hj => Nat.lt_succ_of_lt hj
      exact span_mono (Set.image_mono hsub) (ih (Nat.le_of_succ_le hi) h1)
    · exact key (m + 1) hi h1 h

theorem exists_linearIndependent_eq_succMinOf (hfin : ∀ R, {x | x ∈ S ∧ N x ≤ R}.Finite)
    (hN : ∀ x ∈ S, 0 ≤ N x) (hn : (n : Cardinal) ≤ Module.rank K (span K S)) :
    ∃ v : Fin n → V, LinearIndependent K v ∧ (∀ j, v j ∈ S) ∧
      ∀ j : Fin n, N (v j) = succMinOf K N S (j + 1) := by
  induction n with
  | zero => exact ⟨Fin.elim0, linearIndependent_empty_type, fun j => j.elim0, fun j => j.elim0⟩
  | succ m ih =>
    obtain ⟨v, hv, hS, hvN⟩ := ih ((Nat.cast_le.2 (Nat.le_succ m)).trans hn)
    obtain ⟨-, w, hw, hwS⟩ := mem_succMinRadii_iff.1 (succMinOf_mem hfin hn)
    obtain ⟨k, hk⟩ : ∃ k, w k ∉ span K (Set.range v) := by
      by_contra! h
      have h1 : span K (Set.range w) ≤ span K (Set.range v) :=
        span_le.2 (Set.range_subset_iff.2 h)
      have : Module.Finite K (span K (Set.range v)) :=
        Module.Finite.span_of_finite K (Set.finite_range v)
      have h2 := Submodule.finrank_mono h1
      rw [finrank_span_eq_card hw, finrank_span_eq_card hv] at h2
      simp at h2
    have hk' : N (w k) = succMinOf K N S (m + 1) := by
      refine le_antisymm (hwS k).2 (not_lt.1 fun h => hk ?_)
      exact span_mono (Set.image_subset_range _ _)
        (mem_span_of_lt_succMinOf hv hS (fun j => (hvN j).le) le_rfl (hwS k).1
          (hN _ (hwS k).1) h)
    refine ⟨Fin.snoc v (w k), linearIndependent_finSnoc.2 ⟨hv, hk⟩, fun j => ?_, fun j => ?_⟩
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa using (hwS k).1
      · simpa using hS j
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa using hk'
      · simpa using hvN j

end General

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {L : Submodule ℤ E} {n : ℕ}

theorem mem_span_of_norm_lt_succMin {v : Fin n → E} (hv : LinearIndependent ℝ v)
    (hL : ∀ j, v j ∈ L) (hN : ∀ j : Fin n, ‖v j‖ ≤ succMin L (j + 1)) {i : ℕ} (hi : i ≤ n) {x : E}
    (hx : x ∈ L) (h : ‖x‖ < succMin L (i + 1)) : x ∈ span ℝ (v '' {j | (j : ℕ) < i}) :=
  mem_span_of_lt_succMinOf (N := fun x : E => ‖x‖) (S := (L : Set E)) hv hL hN hi hx
    (norm_nonneg x) h

theorem succMin_le_norm_of_notMem_span {v : Fin n → E} (hv : LinearIndependent ℝ v)
    (hL : ∀ j, v j ∈ L) (hN : ∀ j : Fin n, ‖v j‖ ≤ succMin L (j + 1)) {i : ℕ} (hi : i ≤ n) {x : E}
    (hx : x ∈ L) (h : x ∉ span ℝ (v '' {j | (j : ℕ) < i})) : succMin L (i + 1) ≤ ‖x‖ :=
  not_lt.1 fun h' => h (mem_span_of_norm_lt_succMin hv hL hN hi hx h')

variable [FiniteDimensional ℝ E] [DiscreteTopology L]

theorem exists_linearIndependent_norm_eq_succMin (hn : n ≤ finrank ℝ (span ℝ (L : Set E))) :
    ∃ v : Fin n → E, LinearIndependent ℝ v ∧ (∀ j, v j ∈ L) ∧
      ∀ j : Fin n, ‖v j‖ = succMin L (j + 1) :=
  exists_linearIndependent_eq_succMinOf (N := fun x : E => ‖x‖) (S := (L : Set E))
    (finite_mem_and_norm_le L) (fun x _ => norm_nonneg x) (natCast_le_rank_of_le_finrank hn)

variable (L) [IsZLattice ℝ L]

theorem exists_basis_norm_eq_succMin :
    ∃ b : Basis (Fin (finrank ℝ E)) ℝ E, (∀ j, b j ∈ L) ∧
      ∀ j : Fin (finrank ℝ E), ‖b j‖ = succMin L (j + 1) := by
  obtain ⟨v, hv, hL, hN⟩ :=
    exists_linearIndependent_norm_eq_succMin (L := L) (finrank_span_of_isZLattice L).ge
  have htop : ⊤ ≤ span ℝ (Set.range v) := by
    rw [top_le_iff]
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_eq_card hv, Fintype.card_fin]
  exact ⟨Basis.mk hv htop, by simpa using hL, by simpa using hN⟩

end Normed

section Quadratic

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {Q : QuadraticForm ℝ V} {L : Submodule ℤ V}
  {n : ℕ}

end Quadratic

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DiscreteTopologySpanOfLinearIndependent
open scoped InnerProductSpace
open Module Submodule Matrix

namespace GlobalTheory

section Gram

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem det_gram_real_sum_smul (e : ι → E) (m : Matrix ι ι ℝ) :
    (gram ℝ (fun j => ∑ i, m i j • e i)).det = m.det ^ 2 * (gram ℝ e).det := by
  simpa using Hadamard.re_det_gram_sum_smul (𝕜 := ℝ) e m

end Gram

section Def

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem free_of_fg {V : Type*} [AddCommGroup V] [Module ℝ V] {L : Submodule ℤ V} (h : L.FG) :
    Module.Free ℤ L := by
  have : Module.Finite ℤ L := .of_fg h
  have : HasUniqueDiv V := .of_isTorsionFree ℝ V
  infer_instance


open Classical in
noncomputable def spanCovol (L : Submodule ℤ E) : ℝ :=
  letI : Decidable L.FG := Classical.propDecidable _
  if h : L.FG then
    haveI : Module.Finite ℤ L := .of_fg h
    haveI : Module.Free ℤ L := free_of_fg h
    √(gram ℝ fun i => (finBasis ℤ L i : E)).det
  else 0

theorem sqrt_det_gram_eq_relIndex_mul {L' L : Submodule ℤ E} (h : L' ≤ L) (b' : Basis ι ℤ L')
    (b : Basis ι ℤ L) :
    √(gram ℝ fun i => (b' i : E)).det =
      (L'.toAddSubgroup.relIndex L.toAddSubgroup : ℝ) * √(gram ℝ fun i => (b i : E)).det := by
  let w : ι → L := fun j => ⟨b' j, h (b' j).2⟩
  have h1 : L'.toAddSubgroup.relIndex L.toAddSubgroup = (b.det w).natAbs :=
    AddSubgroup.relIndex_eq_natAbs_det L'.toAddSubgroup L.toAddSubgroup h b' b
  have h2 : (fun j => (b' j : E)) =
      fun j => ∑ i, ((b.toMatrix w).map (Int.cast : ℤ → ℝ)) i j • (b i : E) := by
    funext j
    have := congrArg (fun x : L => (x : E)) (b.sum_repr (w j))
    simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] at this
    simp only [map_apply, Basis.toMatrix_apply, Int.cast_smul_eq_zsmul]
    exact this.symm
  rw [h2, det_gram_real_sum_smul, h1, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,
    ← Int.cast_det, Nat.cast_natAbs, Int.cast_abs, Basis.det_apply]

theorem spanCovol_eq_sqrt_det_gram {L : Submodule ℤ E} (b : Basis ι ℤ L) :
    spanCovol L = √(gram ℝ fun i => (b i : E)).det := by
  have hf : Module.Finite ℤ L := .of_basis b
  have hfg : L.FG := Module.Finite.iff_fg.1 hf
  have : Module.Free ℤ L := .of_basis b
  let e := (finBasis ℤ L).indexEquiv b
  rw [spanCovol, dite_eq_left hfg, sqrt_det_gram_eq_relIndex_mul le_rfl b ((finBasis ℤ L).reindex e),
    AddSubgroup.relIndex_self, Nat.cast_one, one_mul, ← Hadamard.det_gram_comp_equiv _ e]
  congr 3
  ext i
  simp

theorem spanCovol_span {v : ι → E} (hv : LinearIndependent ℤ v) :
    spanCovol (span ℤ (Set.range v)) = √(gram ℝ v).det := by
  rw [spanCovol_eq_sqrt_det_gram (Basis.span hv)]
  simp

theorem spanCovol_map_linearIsometry {L : Submodule ℤ E} (hL : L.FG) (T : E →ₗᵢ[ℝ] F) :
    spanCovol (L.map (T.toLinearMap.restrictScalars ℤ)) = spanCovol L := by
  have : Module.Finite ℤ L := .of_fg hL
  have : Module.Free ℤ L := free_of_fg hL
  let b := finBasis ℤ L
  rw [spanCovol_eq_sqrt_det_gram
    (b.map (L.equivMapOfInjective (T.toLinearMap.restrictScalars ℤ) T.injective)),
    spanCovol_eq_sqrt_det_gram b]
  congr 2
  ext i j
  exact T.inner_map_map _ _

end Def

section Discrete

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem discreteTopology_of_le {N L : Submodule ℤ V} [DiscreteTopology L] (h : N ≤ L) :
    DiscreteTopology N :=
  DiscreteTopology.of_continuous_injective (β := L) (f := Set.inclusion h)
    (continuous_inclusion h) (Set.inclusion_injective h)

variable [FiniteDimensional ℝ V]

theorem fg_of_discrete (L : Submodule ℤ V) [DiscreteTopology L] : L.FG :=
  Module.Finite.iff_fg.1 inferInstance

theorem exists_basis_range_subset {ι : Type*} {v : ι → V} (hv : LinearIndependent ℝ v) :
    ∃ β : Basis (Fin (finrank ℝ V)) ℝ V, Set.range v ⊆ Set.range β := by
  let β := Basis.extend hv.linearIndepOn_id
  refine ⟨β.reindex (β.indexEquiv (finBasis ℝ V)), ?_⟩
  rw [Basis.range_reindex, Basis.range_extend]
  exact Basis.subset_extend _

theorem discreteTopology_span_of_linearIndependent {ι : Type*} {v : ι → V}
    (hv : LinearIndependent ℝ v) : DiscreteTopology (span ℤ (Set.range v)) := by
  obtain ⟨β, hβ⟩ := exists_basis_range_subset hv
  exact discreteTopology_of_le (span_mono hβ)

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
theorem span_range_coe_basis {ι : Type*} {L : Submodule ℤ V} (b : Basis ι ℤ L) :
    span ℤ (Set.range fun i => (b i : V)) = L := by
  have := congrArg (Submodule.map L.subtype) b.span_eq
  rwa [Submodule.map_span, ← Set.range_comp, map_subtype_top] at this

theorem linearIndependent_real_coe_basis {ι : Type*} [Fintype ι] {L : Submodule ℤ V}
    [DiscreteTopology L] (b : Basis ι ℤ L) : LinearIndependent ℝ fun i => (b i : V) :=
  linearIndependent_real_of_int_of_discrete L (fun i => (b i).2)
    (b.linearIndependent.map' L.subtype (ker_subtype L))

end Discrete

section Main

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem spanCovol_eq_covolume [MeasurableSpace E] [BorelSpace E] (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] : spanCovol L = ZLattice.covolume L := by
  rw [spanCovol_eq_sqrt_det_gram (finBasis ℤ L), covolume_eq_sqrt_det_gram L (finBasis ℤ L)]

instance discreteTopology_comap_subtype (L : Submodule ℤ E) [DiscreteTopology L]
    (S : Submodule ℝ E) : DiscreteTopology (ZLattice.comap ℝ L S.subtype) :=
  ZLattice.comap_discreteTopology ℝ L continuous_subtype_val S.injective_subtype

instance isZLattice_comap_subtype_span (L : Submodule ℤ E) [DiscreteTopology L] :
    IsZLattice ℝ (ZLattice.comap ℝ L (span ℝ (L : Set E)).subtype) :=
  ⟨span_span_coe_preimage⟩

theorem spanCovol_comap_subtype (L : Submodule ℤ E) [DiscreteTopology L] (S : Submodule ℝ E)
    (h : (L : Set E) ⊆ S) : spanCovol (ZLattice.comap ℝ L S.subtype) = spanCovol L := by
  rw [← spanCovol_map_linearIsometry (fg_of_discrete _) S.subtypeₗᵢ]
  congr 1
  exact map_comap_eq_self fun x hx => ⟨⟨x, h hx⟩, rfl⟩

theorem spanCovol_eq_covolume_comap_span [MeasurableSpace E] [BorelSpace E] (L : Submodule ℤ E)
    [DiscreteTopology L] :
    spanCovol L = ZLattice.covolume (ZLattice.comap ℝ L (span ℝ (L : Set E)).subtype) := by
  rw [← spanCovol_eq_covolume, spanCovol_comap_subtype L _ subset_span]

end Main

end GlobalTheory
end
