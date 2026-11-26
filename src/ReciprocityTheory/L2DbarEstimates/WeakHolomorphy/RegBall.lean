module

public import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.ImportsAlt

@[expose] public section

section -- merged from ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.RegIndep
section -- merged from ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.RegConv
namespace ReciprocityTheory.L2DbarEstimates.C

open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal

noncomputable def smulFlip : ℂ →L[ℝ] ℝ →L[ℝ] ℂ :=
  (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ).flip

theorem smulFlip_apply (a : ℂ) (r : ℝ) : smulFlip a r = (r : ℂ) * a := by
  simp only [smulFlip, ContinuousLinearMap.flip_apply, ContinuousLinearMap.lsmul_apply,
    Complex.real_smul]

theorem mollify_eq_convolution_smulFlip (n : ℕ) (t : ℝ) (u : V n → ℂ) :
    mollify n t u = convolution u (moll n t) smulFlip volume := by
  ext x
  simp only [mollify, convolution_def, smulFlip_apply]

theorem moll_contDiff_one (n : ℕ) (t : ℝ) : ContDiff ℝ 1 (moll n t) := (moll_contDiff n t).of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))

theorem moll_sub_eq_zero {n : ℕ} {t : ℝ} (ht : 0 < t) {x y : V n}
    (hy : y ∉ closedBall x (t / 2)) : moll n t (x - y) = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro h
  apply hy
  have := moll_tsupport n ht h
  rw [mem_closedBall, dist_zero_right] at this
  rw [mem_closedBall, dist_eq_norm, norm_sub_rev]
  exact this

theorem isTest_moll_sub {n : ℕ} {Ω : Set (V n)} {t : ℝ} {x : V n} (ht : 0 < t)
    (hx : closedBall x t ⊆ Ω) : IsTest Ω (fun y => ((moll n t (x - y) : ℝ) : ℂ)) := by
  have hz : ∀ y ∉ closedBall x (t / 2), ((moll n t (x - y) : ℝ) : ℂ) = 0 := fun y hy => by
    rw [moll_sub_eq_zero ht hy, Complex.ofReal_zero]
  refine ⟨?_, HasCompactSupport.intro (isCompact_closedBall x (t / 2)) hz, ?_⟩
  · exact Complex.ofRealCLM.contDiff.comp ((moll_contDiff n t).comp (contDiff_const.sub contDiff_id))
  · exact (closure_minimal (Function.support_subset_iff'.2 hz) isClosed_closedBall).trans
      ((closedBall_subset_closedBall (by linarith)).trans hx)

theorem fderiv_moll_sub {n : ℕ} {t : ℝ} (x y w : V n) :
    fderiv ℝ (fun y => ((moll n t (x - y) : ℝ) : ℂ)) y w
      = -((fderiv ℝ (moll n t) (x - y) w : ℝ) : ℂ) := by
  have hd : DifferentiableAt ℝ (moll n t) (x - y) :=
    (moll_contDiff_one n t).differentiable one_ne_zero (x - y)
  have h1 : HasFDerivAt (fun y : V n => x - y) (-ContinuousLinearMap.id ℝ (V n)) y :=
    (hasFDerivAt_id y).const_sub x
  have h2 := Complex.ofRealCLM.hasFDerivAt.comp y (hd.hasFDerivAt.comp y h1)
  rw [show (fun y => ((moll n t (x - y) : ℝ) : ℂ)) =
    Complex.ofRealCLM ∘ (moll n t ∘ fun y => x - y) from rfl, h2.fderiv]
  simp

theorem differentiableAt_of_fderiv_I {n : ℕ} {f : V n → ℂ} {x : V n}
    (hf : DifferentiableAt ℝ f x)
    (h : ∀ v, fderiv ℝ f x (I • v) = I * fderiv ℝ f x v) : DifferentiableAt ℂ f x := by
  have hsmul : ∀ (c : ℂ) (v : V n), fderiv ℝ f x (c • v) = c * fderiv ℝ f x v := by
    intro c v
    conv_lhs => rw [← Complex.re_add_im c, add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]
    rw [map_add (f := _), map_smul, map_smul, h, Complex.real_smul, Complex.real_smul]
    conv_rhs => rw [← Complex.re_add_im c]
    ring
  let g' : V n →L[ℂ] ℂ :=
    ⟨⟨⟨fderiv ℝ f x, (fderiv ℝ f x).map_add⟩, fun c v => by simpa using hsmul c v⟩,
      (fderiv ℝ f x).continuous⟩
  exact (differentiableAt_iff_restrictScalars ℝ hf).2 ⟨g', ContinuousLinearMap.ext fun _ => rfl⟩

theorem mollify_differentiableAt {n : ℕ} {Ω : Set (V n)} {u : V n → ℂ} {t : ℝ} {x : V n}
    (hΩ : IsOpen Ω) (hu : Integrable u) (hw : WeakHolo Ω u) (ht : 0 < t)
    (hx : closedBall x t ⊆ Ω) :
    DifferentiableAt ℂ (mollify n t u) x := by
  have hcs := moll_hasCompactSupport n ht
  have hc1 := moll_contDiff_one n t
  have hli : LocallyIntegrable u volume := hu.locallyIntegrable
  have hD := hcs.hasFDerivAt_convolution_right (L := smulFlip) hli hc1 x
  have hcont : ∀ v, Continuous (fun a => fderiv ℝ (moll n t) a v) := fun v =>
    (hc1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hint : ∀ v, Integrable (fun s => ((fderiv ℝ (moll n t) (x - s) v : ℝ) : ℂ) * u s) := by
    intro v
    have := (((hcs.fderiv_apply (𝕜 := ℝ) v).convolutionExists_right smulFlip hli (hcont v)) x)
    simpa [ConvolutionExistsAt, smulFlip_apply] using this
  rw [mollify_eq_convolution_smulFlip]
  apply differentiableAt_of_fderiv_I hD.differentiableAt
  intro w
  rw [hD.fderiv, convolution_precompR_apply smulFlip hli (hcs.fderiv (𝕜 := ℝ)) (hc1.continuous_fderiv one_ne_zero),
    convolution_precompR_apply smulFlip hli (hcs.fderiv (𝕜 := ℝ)) (hc1.continuous_fderiv one_ne_zero)]
  simp only [convolution_def, smulFlip_apply]

  have h0 := hw.2 (fun y => ((moll n t (x - y) : ℝ) : ℂ)) (isTest_moll_sub ht hx) w
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero] at h0
  · simp only [dbarDir, fderiv_moll_sub] at h0
    have hsplit : ∫ z, u z * (-((fderiv ℝ (moll n t) (x - z) (I • w) : ℝ) : ℂ) -
        I * -((fderiv ℝ (moll n t) (x - z) w : ℝ) : ℂ)) =
        I * (∫ z, ((fderiv ℝ (moll n t) (x - z) w : ℝ) : ℂ) * u z) -
          ∫ z, ((fderiv ℝ (moll n t) (x - z) (I • w) : ℝ) : ℂ) * u z := by
      rw [← integral_const_mul, ← integral_sub ((hint w).const_mul I) (hint (I • w))]
      congr 1
      ext z
      ring
    rw [hsplit] at h0
    linear_combination -h0
  · intro z hz
    have hxz : x - z ∉ tsupport (moll n t) := fun h => hz (hx (by
      have := moll_tsupport n ht h
      rw [mem_closedBall, dist_zero_right] at this
      rw [mem_closedBall, dist_eq_norm, norm_sub_rev]
      linarith))
    have h0 : fderiv ℝ (moll n t) (x - z) = 0 := by
      by_contra hne
      exact hxz (support_fderiv_subset ℝ (Function.mem_support.2 hne))
    simp [dbarDir, fderiv_moll_sub, h0]

end ReciprocityTheory.L2DbarEstimates.C
end

namespace ReciprocityTheory.L2DbarEstimates.C

open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal

theorem moll_integrable (n : ℕ) {t : ℝ} (ht : 0 < t) : Integrable (moll n t) := by
  exact (moll_contDiff n t).continuous.integrable_of_hasCompactSupport (moll_hasCompactSupport n ht)

theorem mollify_mollify_swap {n : ℕ} {u : V n → ℂ} (hu : Integrable u) {s t : ℝ} (hs : 0 < s)
    (ht : 0 < t) (x : V n) :
    ∫ w, (moll n s (x - w) : ℂ) * ∫ y, (moll n t (w - y) : ℂ) * u y =
      ∫ y, ((∫ w, moll n s (x - w) * moll n t (w - y) : ℝ) : ℂ) * u y := by
  obtain ⟨C, hC⟩ := (moll_contDiff n s).continuous.bounded_above_of_compact_support
    (moll_hasCompactSupport n hs)
  have hg : Integrable (fun v : V n => (moll n t v : ℂ)) := (moll_integrable n ht).ofReal
  have hI := hu.convolution_integrand (ContinuousLinearMap.mul ℂ ℂ) hg
  have hc : Continuous (fun p : V n × V n => (moll n s (x - p.1) : ℂ)) :=
    Complex.continuous_ofReal.comp
      ((moll_contDiff n s).continuous.comp (continuous_const.sub continuous_fst))
  set F : V n × V n → ℂ := fun p => (moll n s (x - p.1) : ℂ) *
    (ContinuousLinearMap.mul ℂ ℂ) (u p.2) ((fun v : V n => (moll n t v : ℂ)) (p.1 - p.2)) with hFdef
  have hF : Integrable F (volume.prod volume) := by
    refine (hI.norm.const_mul C).mono' (hc.aestronglyMeasurable.mul hI.aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall (fun p => ?_)
    rw [hFdef, norm_mul]
    gcongr
    have h1 := hC (x - p.1)
    simpa using h1
  calc ∫ w, (moll n s (x - w) : ℂ) * ∫ y, (moll n t (w - y) : ℂ) * u y
      = ∫ w, ∫ y, F (w, y) := by
        congr 1; funext w
        rw [← integral_const_mul]
        congr 1; funext y
        simp only [hFdef, ContinuousLinearMap.mul_apply']
        ring
    _ = ∫ y, ∫ w, F (w, y) := integral_integral_swap hF
    _ = ∫ y, ((∫ w, moll n s (x - w) * moll n t (w - y) : ℝ) : ℂ) * u y := by
        congr 1; funext y
        rw [← integral_complex_ofReal, ← integral_mul_const]
        congr 1; funext w
        simp only [hFdef, ContinuousLinearMap.mul_apply', Complex.ofReal_mul]
        ring

theorem moll_conv_symm (n : ℕ) (s t : ℝ) (x y : V n) :
    ∫ w, moll n s (x - w) * moll n t (w - y) = ∫ w, moll n t (x - w) * moll n s (w - y) := by
  calc ∫ w, moll n s (x - w) * moll n t (w - y)
      = ∫ w, moll n s (x - (x + y - w)) * moll n t ((x + y - w) - y) :=
        (integral_sub_left_eq_self (fun w => moll n s (x - w) * moll n t (w - y)) volume
          (x + y)).symm
    _ = ∫ w, moll n t (x - w) * moll n s (w - y) := by
        congr 1; funext w
        rw [mul_comm]
        congr 2 <;> abel

private theorem integral_circleMap_smul_eq_two_pi_mul {n : ℕ} {a : ℝ} {h : V n → ℂ} {x z : V n}
    (hh : DifferentiableOn ℂ h (ball x a)) (hz : ‖z‖ < a) :
    ∫ θ in (0 : ℝ)..2 * Real.pi, h (x + circleMap 0 1 θ • z) = 2 * Real.pi * h x := by
  have hd : DifferentiableOn ℂ (fun l : ℂ => h (x + l • z)) (closedBall (0 : ℂ) 1) := by
    intro l hl
    have hl1 : ‖l‖ ≤ 1 := by simpa using hl
    have hmem : x + l • z ∈ ball x a := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
      calc ‖l‖ * ‖z‖ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right hl1 (norm_nonneg z)
        _ < a := by rw [one_mul]; exact hz
    have h1 : DifferentiableAt ℂ h (x + l • z) := hh.differentiableAt (isOpen_ball.mem_nhds hmem)
    have h2 : DifferentiableAt ℂ (fun l : ℂ => x + l • z) l :=
      (differentiableAt_id.smul_const z).const_add x
    exact (h1.comp l h2).differentiableWithinAt
  have hdc : DiffContOnCl ℂ (fun l : ℂ => h (x + l • z)) (ball (0 : ℂ) 1) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball (0 : ℂ) one_ne_zero]
    exact hd
  have hC := hdc.circleIntegral_sub_inv_smul (mem_ball_self one_pos)
  have e0 : h (x + (0 : ℂ) • z) = h x := by rw [zero_smul, add_zero]
  have key : Complex.I * ∫ θ in (0 : ℝ)..2 * Real.pi, h (x + circleMap 0 1 θ • z)
      = 2 * Real.pi * Complex.I * h x := by
    calc Complex.I * ∫ θ in (0 : ℝ)..2 * Real.pi, h (x + circleMap 0 1 θ • z)
        = ∫ θ in (0 : ℝ)..2 * Real.pi, deriv (circleMap 0 1) θ •
            ((circleMap 0 1 θ - 0)⁻¹ • h (x + circleMap 0 1 θ • z)) := by
          rw [← intervalIntegral.integral_const_mul]
          refine intervalIntegral.integral_congr fun θ _ => ?_
          have hne : circleMap 0 1 θ ≠ 0 := circleMap_ne_center one_ne_zero
          simp only [deriv_circleMap, sub_zero, smul_eq_mul]
          first
          | (rw [mul_comm (circleMap 0 1 θ) Complex.I, mul_assoc, mul_inv_cancel_left₀ hne])
          | field_simp
          | (field_simp; ring)
      _ = ∮ l in C(0, 1), (l - 0)⁻¹ • h (x + l • z) := rfl
      _ = (2 * Real.pi * Complex.I : ℂ) • h (x + (0 : ℂ) • z) := hC
      _ = 2 * Real.pi * Complex.I * h x := by rw [e0, smul_eq_mul]
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  apply mul_left_cancel₀ hI
  rw [key]
  ring

private theorem integral_comp_smul_of_norm_eq_one {n : ℕ} (c : ℂ) (hc : ‖c‖ = 1) (f : V n → ℂ) :
    ∫ z, f (c • z) = ∫ z, f z := by
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hc
    exact zero_ne_one hc
  let e : V n ≃ₗᵢ[ℝ] V n :=
    { toLinearEquiv := (LinearEquiv.smulOfNeZero ℂ (V n) c hc0).restrictScalars ℝ
      norm_map' := fun z => by
        show ‖c • z‖ = ‖z‖
        rw [norm_smul, hc, one_mul] }
  show ∫ z, f (e z) = ∫ z, f z
  exact e.measurePreserving.integral_comp e.toHomeomorph.measurableEmbedding f

private theorem moll_eq_zero_of_half_lt_norm {n : ℕ} {t : ℝ} (ht : 0 < t) {z : V n} (hz : t / 2 < ‖z‖) :
    moll n t z = 0 := by
  have h1 : 1 - 4 * (‖z‖ / t) ^ 2 ≤ 0 := by
    have h2 : 1 / 2 < ‖z‖ / t := by
      rw [lt_div_iff₀ ht]; linarith
    nlinarith
  simp only [moll, mollProf, bumpProf, Real.smoothTransition.zero_of_nonpos h1, mul_zero]

theorem moll_mean {n : ℕ} {a : ℝ} (ha : 0 < a) {h : V n → ℂ} {x : V n}
    (hh : DifferentiableOn ℂ h (ball x a)) :
    ∫ w, (moll n a (x - w) : ℂ) * h w = h x := by
  have hA : ∫ w, (moll n a (x - w) : ℂ) * h w = ∫ z, (moll n a z : ℂ) * h (x + z) := by
    have e1 := integral_add_left_eq_self (μ := volume) (fun w => (moll n a (x - w) : ℂ) * h w) x
    try beta_reduce at e1
    rw [← e1]
    congr 1
    funext z
    congr 1
    · unfold moll
      congr 1
      rw [show x - (x + z) = -z by abel, norm_neg]
  rw [hA]
  have hB : ∀ θ : ℝ, ∫ z, (moll n a z : ℂ) * h (x + circleMap 0 1 θ • z)
      = ∫ z, (moll n a z : ℂ) * h (x + z) := by
    intro θ
    have hc : ‖circleMap 0 1 θ‖ = 1 := by simp
    have e2 := integral_comp_smul_of_norm_eq_one (circleMap 0 1 θ) hc (fun z => (moll n a z : ℂ) * h (x + z))
    try beta_reduce at e2
    rw [← e2]
    congr 1
    funext z
    congr 1
    unfold moll
    rw [norm_smul, hc, one_mul]
  obtain ⟨C, hC⟩ := (isCompact_closedBall x (a / 2)).exists_bound_of_continuousOn
    (hh.continuousOn.mono (closedBall_subset_ball (by linarith)))
  have hcont : Continuous (fun p : ℝ × V n => (moll n a p.2 : ℂ) * h (x + circleMap 0 1 p.1 • p.2)) := by
    rw [continuous_iff_continuousAt]
    rintro ⟨θ0, z0⟩
    by_cases hz0 : ‖z0‖ < a
    · have hmc : Continuous fun p : ℝ × V n => (moll n a p.2 : ℂ) :=
        Complex.continuous_ofReal.comp ((moll_contDiff n a).continuous.comp continuous_snd)
      have hg : Continuous fun p : ℝ × V n => x + circleMap 0 1 p.1 • p.2 :=
        continuous_const.add (((continuous_circleMap 0 1).comp continuous_fst).smul continuous_snd)
      have hmem : x + circleMap 0 1 θ0 • z0 ∈ ball x a := by
        rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, norm_circleMap_zero, abs_one,
          one_mul]
        exact hz0
      have hhc : ContinuousAt h (x + circleMap 0 1 θ0 • z0) :=
        (hh.differentiableAt (isOpen_ball.mem_nhds hmem)).continuousAt
      exact hmc.continuousAt.mul (hhc.comp_of_eq hg.continuousAt rfl)
    · push_neg at hz0
      have hopen : IsOpen {p : ℝ × V n | a / 2 < ‖p.2‖} :=
        isOpen_lt continuous_const (continuous_norm.comp continuous_snd)
      have hmem : (θ0, z0) ∈ {p : ℝ × V n | a / 2 < ‖p.2‖} := by
        show a / 2 < ‖z0‖
        linarith
      have hev : (fun p : ℝ × V n => (moll n a p.2 : ℂ) * h (x + circleMap 0 1 p.1 • p.2))
          =ᶠ[𝓝 (θ0, z0)] fun _ => 0 := by
        filter_upwards [hopen.mem_nhds hmem] with p hp
        rw [moll_eq_zero_of_half_lt_norm ha hp]
        simp
      exact (continuousAt_congr hev).mpr continuousAt_const
  have hInt : Integrable
      (Function.uncurry fun (θ : ℝ) (z : V n) => (moll n a z : ℂ) * h (x + circleMap 0 1 θ • z))
      ((volume.restrict (Set.Ioc 0 (2 * Real.pi))).prod volume) := by
    have hg1 : Integrable (fun _ : ℝ => C) (volume.restrict (Set.Ioc 0 (2 * Real.pi))) :=
      integrable_const C
    have hbd : Integrable (fun p : ℝ × V n => C * |moll n a p.2|)
        ((volume.restrict (Set.Ioc 0 (2 * Real.pi))).prod volume) := by
      first
      | exact MeasureTheory.Integrable.prod_mul hg1 (moll_integrable n ha).abs
      | exact MeasureTheory.Integrable.mul_prod hg1 (moll_integrable n ha).abs
      | exact MeasureTheory.Integrable.prod_smul hg1 (moll_integrable n ha).abs
      | exact MeasureTheory.Integrable.comp_snd ((moll_integrable n ha).abs.const_mul C) _
      | exact ((moll_integrable n ha).abs.const_mul C).comp_snd
    refine Integrable.mono' hbd
      hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
    show ‖(moll n a p.2 : ℂ) * h (x + circleMap 0 1 p.1 • p.2)‖ ≤ C * |moll n a p.2|
    by_cases hp : ‖p.2‖ ≤ a / 2
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      apply hC
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, norm_circleMap_zero,
        abs_one, one_mul]
      exact hp
    · push_neg at hp
      rw [moll_eq_zero_of_half_lt_norm ha hp]
      simp
  have hswap := integral_integral_swap hInt
  try beta_reduce at hswap
  have hz : ∀ z : V n, ∫ θ in Set.Ioc 0 (2 * Real.pi), (moll n a z : ℂ) * h (x + circleMap 0 1 θ • z)
      = (moll n a z : ℂ) * (2 * Real.pi * h x) := by
    intro z
    rw [integral_const_mul]
    by_cases hz : ‖z‖ ≤ a / 2
    · rw [← intervalIntegral.integral_of_le Real.two_pi_pos.le, integral_circleMap_smul_eq_two_pi_mul hh (by linarith)]
    · push_neg at hz
      rw [moll_eq_zero_of_half_lt_norm ha hz]
      simp
  rw [← intervalIntegral.integral_of_le Real.two_pi_pos.le,
    show (fun θ : ℝ => ∫ z, (moll n a z : ℂ) * h (x + circleMap 0 1 θ • z))
      = fun _ => ∫ z, (moll n a z : ℂ) * h (x + z) from funext hB,
    intervalIntegral.integral_const,
    show (fun z : V n => ∫ θ in Set.Ioc 0 (2 * Real.pi), (moll n a z : ℂ) * h (x + circleMap 0 1 θ • z))
      = fun z => (moll n a z : ℂ) * (2 * Real.pi * h x) from funext hz,
    integral_mul_const, integral_complex_ofReal, moll_integral n ha, sub_zero,
    Complex.real_smul] at hswap
  have h2pi : (2 * Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.two_pi_pos.ne'
  apply mul_left_cancel₀ h2pi
  push_cast at hswap ⊢
  linear_combination hswap

theorem mollify_indep {n : ℕ} {Ω : Set (V n)} {u : V n → ℂ} {s t : ℝ} {x : V n}
    (hΩ : IsOpen Ω) (hu : Integrable u) (hw : WeakHolo Ω u) (hs : 0 < s) (ht : 0 < t)
    (hx : closedBall x (s + t) ⊆ Ω) :
    mollify n s u x = mollify n t u x := by
  have hA : DifferentiableOn ℂ (mollify n t u) (ball x s) := by
    intro w hwb
    rw [Metric.mem_ball] at hwb
    refine (mollify_differentiableAt hΩ hu hw ht ((Metric.closedBall_subset_closedBall' ?_).trans hx)).differentiableWithinAt
    linarith
  have hB : DifferentiableOn ℂ (mollify n s u) (ball x t) := by
    intro w hwb
    rw [Metric.mem_ball] at hwb
    refine (mollify_differentiableAt hΩ hu hw hs ((Metric.closedBall_subset_closedBall' ?_).trans hx)).differentiableWithinAt
    linarith
  calc mollify n s u x = ∫ w, (moll n t (x - w) : ℂ) * mollify n s u w := (moll_mean ht hB).symm
    _ = ∫ y, ((∫ w, moll n t (x - w) * moll n s (w - y) : ℝ) : ℂ) * u y :=
        mollify_mollify_swap hu ht hs x
    _ = ∫ y, ((∫ w, moll n s (x - w) * moll n t (w - y) : ℝ) : ℂ) * u y := by
        congr 1; funext y; rw [moll_conv_symm n t s x y]
    _ = ∫ w, (moll n s (x - w) : ℂ) * mollify n t u w := (mollify_mollify_swap hu hs ht x).symm
    _ = mollify n t u x := moll_mean hs hA

end ReciprocityTheory.L2DbarEstimates.C
end

section -- merged from ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.MollLeClosedBall
namespace ReciprocityTheory.L2DbarEstimates.C

open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal

theorem moll_le_closedBall (n : ℕ) :
    ∃ C : ℝ, ∀ t : ℝ, 0 < t → ∀ x z : V n,
      moll n t z ≤ C / volume.real (closedBall x t) := by
  obtain ⟨C, hC⟩ := moll_le n
  refine ⟨C, fun t ht x z => ?_⟩
  have hvol : volume.real (closedBall x t) = volume.real (ball (0 : V n) t) := by
    rcases subsingleton_or_nontrivial (V n) with hV | hV
    · have h1 : closedBall x t = univ := eq_univ_of_forall fun y => by
        rw [Subsingleton.elim y x]; exact mem_closedBall_self ht.le
      have h2 : ball (0 : V n) t = univ := eq_univ_of_forall fun y => by
        rw [Subsingleton.elim y 0]; exact mem_ball_self ht
      rw [h1, h2]
    · simp only [measureReal_def]
      rw [Measure.addHaar_closedBall_eq_addHaar_ball, Measure.addHaar_ball_center]
  rw [hvol]
  exact hC t ht z

theorem mollify_tendsto_ae {n : ℕ} {u : V n → ℂ} (hu : Integrable u) :
    ∀ᵐ x, Tendsto (fun t => mollify n t u x) (𝓝[>] 0) (𝓝 (u x)) := by
  obtain ⟨C, hC⟩ := moll_le_closedBall n
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub (μ := volume)
    hu.locallyIntegrable 1] with x hx
  have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  have hav : Tendsto (fun t : ℝ => ⨍ y in closedBall x t, ‖u y - u x‖) (𝓝[>] 0) (𝓝 0) :=
    hx (l := 𝓝[>] (0 : ℝ)) (fun _ => x) id tendsto_id (by
      filter_upwards [hpos] with t ht
      exact mem_closedBall_self (by simp only [id, one_mul]; exact ht.le))
  have hg : Tendsto (fun t : ℝ => ∫ y, moll n t (x - y)) (𝓝[>] 0) (𝓝 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hpos] with t ht
    show (1 : ℝ) = ∫ y, moll n t (x - y)
    rw [integral_sub_left_eq_self (moll n t) volume x, moll_integral n ht]
  have hsupp : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      Function.support (fun y => moll n t (x - y)) ⊆ closedBall x t := by
    filter_upwards [hpos] with t ht
    intro y hy
    have h := moll_tsupport n ht (subset_tsupport (moll n t) (show x - y ∈ Function.support (moll n t) from hy))
    rw [mem_closedBall, dist_zero_right] at h
    rw [mem_closedBall, dist_comm, dist_eq_norm]
    linarith
  have hbd : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ y, |moll n t (x - y)| ≤ C / volume.real (closedBall x t) := by
    filter_upwards [hpos] with t ht
    intro y
    rw [abs_of_nonneg (moll_nonneg _ _ _)]
    exact hC t ht x _
  have key := tendsto_integral_smul_of_tendsto_average_norm_sub (μ := volume)
    (a := fun t => closedBall x t) (g := fun t y => moll n t (x - y)) C hav
    (Eventually.of_forall fun _ => hu.integrableOn) hg hsupp hbd
  refine key.congr (fun t => ?_)
  simp only [mollify, Complex.real_smul]

end ReciprocityTheory.L2DbarEstimates.C
end

namespace ReciprocityTheory.L2DbarEstimates.C

open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal

theorem reg_ball {n : ℕ} {Ω : Set (V n)} {u : V n → ℂ} (hΩ : IsOpen Ω) (hu : Integrable u)
    (hw : WeakHolo Ω u) (c : V n) (r : ℝ) (hr : closedBall c (3 * r) ⊆ Ω) :
    ∃ U : V n → ℂ, DifferentiableOn ℂ U (ball c r) ∧ u =ᵐ[volume.restrict (ball c r)] U := by
  by_cases hr0 : 0 < r
  · refine ⟨mollify n r u, fun x hx => ?_, ?_⟩
    · have hx' : closedBall x r ⊆ Ω := by
        refine (Metric.closedBall_subset_closedBall' ?_).trans hr
        rw [Metric.mem_ball] at hx; linarith
      exact (mollify_differentiableAt hΩ hu hw hr0 hx').differentiableWithinAt
    · rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_ball]
      filter_upwards [mollify_tendsto_ae hu] with x hx hxb
      rw [Metric.mem_ball] at hxb
      have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), mollify n t u x = mollify n r u x := by
        filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hr0)] with t ht1 ht2
        have ht1' : 0 < t := ht1
        have ht2' : t < r := ht2
        refine mollify_indep hΩ hu hw ht1' hr0 ((Metric.closedBall_subset_closedBall' ?_).trans hr)
        linarith
      have h2 : Tendsto (fun t => mollify n t u x) (𝓝[>] 0) (𝓝 (mollify n r u x)) :=
        tendsto_const_nhds.congr' (hev.mono fun t ht => ht.symm)
      exact tendsto_nhds_unique hx h2
  · have h0 : ball c r = ∅ := Metric.ball_eq_empty.2 (not_lt.1 hr0)
    refine ⟨u, ?_, ?_⟩
    · rw [h0]; exact differentiableOn_empty
    · rw [h0, Measure.restrict_empty]

theorem reg : RegStatement := by
  intro n Ω u hΩ hw
  apply reg_glue hΩ
  intro x hx
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hΩ x hx
  have hr0 : 0 < ε / 8 := by positivity
  have h5 : closedBall x (5 * (ε / 8)) ⊆ Ω :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  have h4 : ball x (4 * (ε / 8)) ⊆ closedBall x (5 * (ε / 8)) :=
    Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith))
  have h4Ω : ball x (4 * (ε / 8)) ⊆ Ω := h4.trans h5
  set u' := (closedBall x (5 * (ε / 8))).indicator u with hu'def
  have hu' : Integrable u' := by
    rw [hu'def, integrable_indicator_iff measurableSet_closedBall]
    exact hw.1.integrableOn_compact_subset h5 (isCompact_closedBall _ _)
  have hw' : WeakHolo (ball x (4 * (ε / 8))) u' := by
    refine ⟨hu'.locallyIntegrable.locallyIntegrableOn _, fun g hg v => ?_⟩
    have hzero : ∀ z, z ∉ tsupport g → dbarDir g z v = 0 := by
      intro z hz
      have h0 : fderiv ℝ g z = 0 := by
        rw [(notMem_tsupport_iff_eventuallyEq.mp hz).fderiv_eq]; simp
      simp [dbarDir, h0]
    have hts : tsupport g ⊆ ball x (4 * (ε / 8)) := hg.2.2
    have hpt : ∀ z, u' z * dbarDir g z v = u z * dbarDir g z v := by
      intro z
      by_cases hz : z ∈ tsupport g
      · rw [hu'def, Set.indicator_of_mem (h4 (hts hz))]
      · simp [hzero z hz]
    have h1 := hw.2 g ⟨hg.1, hg.2.1, hts.trans h4Ω⟩ v
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun z hz => by simp [hzero z (fun h => hz (hts.trans h4Ω h))])] at h1
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun z hz => by simp [hzero z (fun h => hz (hts h))])]
    simp_rw [hpt]
    exact h1
  obtain ⟨U, hU, hae⟩ := reg_ball (Ω := ball x (4 * (ε / 8))) Metric.isOpen_ball hu' hw' x (ε / 8)
    (Metric.closedBall_subset_ball (by linarith))
  refine ⟨ε / 8, hr0, (Metric.ball_subset_ball (by linarith)).trans h4Ω, U, hU, ?_⟩
  refine Filter.EventuallyEq.trans ?_ hae
  refine ae_restrict_of_forall_mem measurableSet_ball (fun z hz => ?_)
  rw [hu'def, Set.indicator_of_mem (h4 (Metric.ball_subset_ball (by linarith) hz))]

end ReciprocityTheory.L2DbarEstimates.C
