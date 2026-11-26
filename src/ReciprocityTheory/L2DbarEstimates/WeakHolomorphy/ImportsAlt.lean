module

public import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.HoloWeakStatement

@[expose] public section

section -- merged from ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.ImportsAlt
namespace ReciprocityTheory.L2DbarEstimates.C

open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal

theorem ident : IdentStatement := by
  intro n Ω F a hΩ hc hF ha h0 x hx
  set L : ℂ → V n := fun t => a + t • (x - a) with hL
  have hLd : Differentiable ℂ L := (differentiable_const a).add (differentiable_id.smul_const (x - a))
  have hLc : Continuous L := hLd.continuous
  set U : Set ℂ := L ⁻¹' Ω with hU
  have hUo : IsOpen U := hΩ.preimage hLc
  have hUconv : Convex ℝ U := by
    intro t1 ht1 t2 ht2 s1 s2 hs1 hs2 hs
    show L (s1 • t1 + s2 • t2) ∈ Ω
    have key : L (s1 • t1 + s2 • t2) = s1 • L t1 + s2 • L t2 := by
      have e : s1 • L t1 + s2 • L t2 = (s1 + s2) • a + (s1 • t1 + s2 • t2) • (x - a) := by
        simp only [hL, smul_add, add_smul, smul_assoc]
        abel
      rw [e, hs, one_smul]
    rw [key]
    exact hc ht1 ht2 hs1 hs2 hs
  have hG : DifferentiableOn ℂ (F ∘ L) U := hF.comp hLd.differentiableOn (fun t ht => ht)
  have hA : AnalyticOnNhd ℂ (F ∘ L) U := hG.analyticOnNhd hUo
  have h0U : (0 : ℂ) ∈ U := by
    show L 0 ∈ Ω
    simpa [hL] using ha
  have h1U : (1 : ℂ) ∈ U := by
    show L 1 ∈ Ω
    simpa [hL] using hx
  have hL0 : L 0 = a := by simp [hL]
  have hev : F ∘ L =ᶠ[𝓝 0] 0 := by
    have ht : Filter.Tendsto L (𝓝 0) (𝓝 a) := by
      rw [← hL0]
      exact hLc.continuousAt.tendsto
    exact ht.eventually h0
  have hEq := hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUconv.isPreconnected h0U hev
  have h1 := hEq h1U
  simpa [hL] using h1

end ReciprocityTheory.L2DbarEstimates.C
end

section -- merged from ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.MeasurableEmbeddingRotAbout
section -- merged from ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.Circle
namespace ReciprocityTheory.L2DbarEstimates.C

open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal

theorem measurePreserving_smul_unit {n : ℕ} (a : ℂ) (ha : ‖a‖ = 1) :
    MeasurePreserving (fun z : V n => a • z) volume volume := by
  have ha0 : a ≠ 0 := by
    intro h
    simp [h] at ha
  let L : V n ≃ₗᵢ[ℝ] V n :=
    { toLinearEquiv := (LinearEquiv.smulOfNeZero ℂ (V n) a ha0).restrictScalars ℝ
      norm_map' := fun z => by simp [norm_smul, ha] }
  have hL : (fun z : V n => a • z) = L := by
    funext z
    rfl
  rw [hL]
  exact L.measurePreserving

theorem circle_mean {n : ℕ} {c w : V n} {R : ℝ} {u : V n → ℂ}
    (hu : DifferentiableOn ℂ u (ball c R)) (hw : ‖w‖ < R) :
    ∫ θ in (0 : ℝ)..2 * Real.pi, u (c + Complex.exp ((θ : ℂ) * I) • w) =
      ((2 * Real.pi : ℝ) : ℂ) * u c := by
  by_cases hw0 : w = 0
  · subst hw0
    simp
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hρ1 : 1 < R / ‖w‖ := by
    rw [lt_div_iff₀ hwpos]
    linarith
  have hg : DifferentiableOn ℂ (fun ζ : ℂ => u (c + ζ • w)) (Metric.ball 0 (R / ‖w‖)) := by
    intro ζ hζ
    have hmem : c + ζ • w ∈ ball c R := by
      rw [Metric.mem_ball, dist_zero_right, lt_div_iff₀ hwpos] at hζ
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
      exact hζ
    have h1 : DifferentiableAt ℂ u (c + ζ • w) := hu.differentiableAt (isOpen_ball.mem_nhds hmem)
    have h2 : DifferentiableAt ℂ (fun ζ : ℂ => c + ζ • w) ζ :=
      (differentiableAt_id.smul_const w).const_add c
    exact (h1.comp ζ h2).differentiableWithinAt
  have hcl : DifferentiableOn ℂ (fun ζ : ℂ => u (c + ζ • w)) (Metric.closedBall 0 1) :=
    hg.mono (Metric.closedBall_subset_ball hρ1)
  have key := hcl.circleIntegral_sub_inv_smul (w := 0) (by simp)
  simp only [circleIntegral, deriv_circleMap, sub_zero, smul_eq_mul, zero_smul, add_zero] at key
  have hcm : ∀ θ : ℝ, circleMap 0 1 θ = Complex.exp ((θ : ℂ) * I) := by
    intro θ
    simp [circleMap]
  have h3 : ∀ θ : ℝ, circleMap 0 1 θ * I * ((circleMap 0 1 θ)⁻¹ * u (c + circleMap 0 1 θ • w)) =
      I * u (c + Complex.exp ((θ : ℂ) * I) • w) := by
    intro θ
    have hne : circleMap 0 1 θ ≠ 0 := circleMap_ne_center one_ne_zero
    rw [hcm θ] at hne ⊢
    calc Complex.exp ((θ : ℂ) * I) * I * ((Complex.exp ((θ : ℂ) * I))⁻¹ * u (c + Complex.exp ((θ : ℂ) * I) • w))
        = I * u (c + Complex.exp ((θ : ℂ) * I) • w) * (Complex.exp ((θ : ℂ) * I) * (Complex.exp ((θ : ℂ) * I))⁻¹) := by ring
      _ = I * u (c + Complex.exp ((θ : ℂ) * I) • w) := by rw [mul_inv_cancel₀ hne, mul_one]
  simp only [h3, intervalIntegral.integral_const_mul] at key
  apply mul_left_cancel₀ Complex.I_ne_zero
  rw [key]
  push_cast
  ring

theorem circle_mean_sq {n : ℕ} {c w : V n} {R : ℝ} {u : V n → ℂ}
    (hu : DifferentiableOn ℂ u (ball c R)) (hw : ‖w‖ < R) :
    ‖u c‖ₑ ^ 2 * ENNReal.ofReal (2 * Real.pi) ≤
      ∫⁻ θ in Ioc (0 : ℝ) (2 * Real.pi), ‖u (c + Complex.exp ((θ : ℂ) * I) • w)‖ₑ ^ 2 := by
  have hmem : ∀ θ : ℝ, c + Complex.exp ((θ : ℂ) * I) • w ∈ ball c R := by
    intro θ
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Complex.norm_exp_ofReal_mul_I, one_mul]
    exact hw
  set F : ℝ → ℂ := fun θ => u (c + Complex.exp ((θ : ℂ) * I) • w) with hF
  have hcont : Continuous F := by
    refine continuous_iff_continuousAt.2 fun θ => ?_
    have h1 := (hu.differentiableAt (isOpen_ball.mem_nhds (hmem θ))).continuousAt
    have h2 : Continuous fun θ : ℝ => c + Complex.exp ((θ : ℂ) * I) • w := by fun_prop
    show ContinuousAt (u ∘ fun θ : ℝ => c + Complex.exp ((θ : ℂ) * I) • w) θ
    exact ContinuousAt.comp (f := fun θ : ℝ => c + Complex.exp ((θ : ℂ) * I) • w) (x := θ) h1
      h2.continuousAt
  have hpi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hI : ∫ θ in Ioc (0 : ℝ) (2 * Real.pi), F θ = ((2 * Real.pi : ℝ) : ℂ) * u c := by
    rw [← intervalIntegral.integral_of_le hpi]
    exact circle_mean hu hw
  have hint : IntegrableOn F (Ioc (0 : ℝ) (2 * Real.pi)) :=
    (hcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hint2 : IntegrableOn (fun θ => ‖F θ‖ ^ 2) (Ioc (0 : ℝ) (2 * Real.pi)) :=
    ((hcont.norm.pow 2).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hcr : Continuous fun θ => (F θ * (starRingEnd ℂ) (u c)).re :=
    Complex.continuous_re.comp (hcont.mul continuous_const)
  have hint3 : IntegrableOn (fun θ => (F θ * (starRingEnd ℂ) (u c)).re) (Ioc (0 : ℝ) (2 * Real.pi)) :=
    (hcr.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hpt : ∀ θ, 2 * (F θ * (starRingEnd ℂ) (u c)).re - ‖u c‖ ^ 2 ≤ ‖F θ‖ ^ 2 := by
    intro θ
    have h := Complex.normSq_nonneg (F θ - u c)
    rw [Complex.normSq_sub] at h
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    linarith
  have hre : ∫ θ in Ioc (0 : ℝ) (2 * Real.pi), (F θ * (starRingEnd ℂ) (u c)).re =
      2 * Real.pi * ‖u c‖ ^ 2 := by
    have h1 : ∫ θ in Ioc (0 : ℝ) (2 * Real.pi), (F θ * (starRingEnd ℂ) (u c)).re =
        (∫ θ in Ioc (0 : ℝ) (2 * Real.pi), F θ * (starRingEnd ℂ) (u c)).re :=
      integral_re (hint.mul_const _)
    rw [h1, integral_mul_const, hI, mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  have hreal : ‖u c‖ ^ 2 * (2 * Real.pi) ≤ ∫ θ in Ioc (0 : ℝ) (2 * Real.pi), ‖F θ‖ ^ 2 := by
    have h : ∫ θ in Ioc (0 : ℝ) (2 * Real.pi), (2 * (F θ * (starRingEnd ℂ) (u c)).re - ‖u c‖ ^ 2) ≤
        ∫ θ in Ioc (0 : ℝ) (2 * Real.pi), ‖F θ‖ ^ 2 :=
      integral_mono ((hint3.const_mul 2).sub (integrable_const (‖u c‖ ^ 2))) hint2 hpt
    rw [integral_sub (hint3.const_mul 2) (integrable_const _), integral_const_mul, hre,
      integral_const] at h
    simp only [Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero, smul_eq_mul] at h
    have hv : (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))).real univ = 2 * Real.pi := by
      simp [Measure.real, Real.volume_Ioc, hpi, Real.pi_pos.le]
    rw [hv] at h
    linarith
  have hen : ∀ θ, ‖F θ‖ₑ ^ 2 = ENNReal.ofReal (‖F θ‖ ^ 2) := fun θ => by
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  show ‖u c‖ₑ ^ 2 * ENNReal.ofReal (2 * Real.pi) ≤
    ∫⁻ θ in Ioc (0 : ℝ) (2 * Real.pi), ‖F θ‖ₑ ^ 2
  simp_rw [hen]
  rw [← ofReal_integral_eq_lintegral_ofReal hint2 (ae_of_all _ fun θ => by positivity),
    ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal hreal

end ReciprocityTheory.L2DbarEstimates.C
end

namespace ReciprocityTheory.L2DbarEstimates.C

open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal

noncomputable def rotAbout {n : ℕ} (c : V n) (a : ℂ) (z : V n) : V n := c + a • (z - c)

theorem rotAbout_sub {n : ℕ} (c : V n) {a : ℂ} (ha : ‖a‖ = 1) (z : V n) :
    ‖rotAbout c a z - c‖ = ‖z - c‖ := by
  simp [rotAbout, norm_smul, ha]

theorem rotAbout_mem_ball_iff {n : ℕ} (c : V n) {a : ℂ} (ha : ‖a‖ = 1) (R : ℝ) (z : V n) :
    rotAbout c a z ∈ ball c R ↔ z ∈ ball c R := by
  rw [mem_ball, mem_ball, dist_eq_norm, dist_eq_norm, rotAbout_sub c ha]

theorem measurePreserving_rotAbout {n : ℕ} (c : V n) {a : ℂ} (ha : ‖a‖ = 1) :
    MeasurePreserving (rotAbout c a) volume volume :=
  (measurePreserving_add_left volume c).comp
    ((measurePreserving_smul_unit a ha).comp (measurePreserving_sub_right volume c))

theorem measurableEmbedding_rotAbout {n : ℕ} (c : V n) {a : ℂ} (ha : ‖a‖ = 1) :
    MeasurableEmbedding (rotAbout c a) := by
  have ha0 : a ≠ 0 := by rintro rfl; simp at ha
  let h : V n ≃ₜ V n :=
    { toFun := rotAbout c a
      invFun := fun z => c + a⁻¹ • (z - c)
      left_inv := fun z => by simp [rotAbout, smul_smul, inv_mul_cancel₀ ha0]
      right_inv := fun z => by simp [rotAbout, smul_smul, mul_inv_cancel₀ ha0]
      continuous_toFun := by unfold rotAbout; fun_prop
      continuous_invFun := by fun_prop }
  exact h.measurableEmbedding

theorem indicator_rotAbout {n : ℕ} (c : V n) {a : ℂ} (ha : ‖a‖ = 1) (R : ℝ) {β : Type*}
    [Zero β] (g : V n → β) (z : V n) :
    (ball c R).indicator (fun z => g (rotAbout c a z)) z =
      (ball c R).indicator g (rotAbout c a z) := by
  by_cases hz : z ∈ ball c R
  · rw [indicator_of_mem hz, indicator_of_mem ((rotAbout_mem_ball_iff c ha R z).2 hz)]
  · rw [indicator_of_notMem hz,
      indicator_of_notMem (fun h => hz ((rotAbout_mem_ball_iff c ha R z).1 h))]

theorem setLIntegral_rotAbout {n : ℕ} (c : V n) {a : ℂ} (ha : ‖a‖ = 1) (R : ℝ)
    (g : V n → ℝ≥0∞) :
    ∫⁻ z in ball c R, g (rotAbout c a z) = ∫⁻ z in ball c R, g z := by
  rw [← lintegral_indicator measurableSet_ball, ← lintegral_indicator measurableSet_ball,
    lintegral_congr fun z => indicator_rotAbout c ha R g z]
  exact (measurePreserving_rotAbout c ha).lintegral_comp_emb (measurableEmbedding_rotAbout c ha) _

theorem norm_exp_mul_I_eq_one (θ : ℝ) : ‖Complex.exp ((θ : ℂ) * I)‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I θ

theorem continuous_rotAbout_exp {n : ℕ} (c : V n) :
    Continuous (fun p : ℝ × V n => rotAbout c (Complex.exp ((p.1 : ℂ) * I)) p.2) := by
  unfold rotAbout; fun_prop

theorem continuousOn_comp_rotAbout {n : ℕ} {c : V n} {R : ℝ} {u : V n → ℂ}
    (hu : DifferentiableOn ℂ u (ball c R)) (s : Set ℝ) :
    ContinuousOn (fun p : ℝ × V n => u (rotAbout c (Complex.exp ((p.1 : ℂ) * I)) p.2))
      (s ×ˢ ball c R) := by
  refine hu.continuousOn.comp (continuous_rotAbout_exp c).continuousOn ?_
  rintro ⟨θ, z⟩ ⟨_, hz⟩
  exact (rotAbout_mem_ball_iff c (norm_exp_mul_I_eq_one θ) R z).2 hz

theorem mv : MVStatement := by
  intro n c R u r hu hr
  have hT1 := norm_exp_mul_I_eq_one
  have hrot : ∀ θ : ℝ, ∫⁻ z in ball c R,
      ‖u (rotAbout c (Complex.exp ((θ : ℂ) * I)) z)‖ₑ ^ 2 * r ‖z - c‖ =
        ∫⁻ z in ball c R, ‖u z‖ₑ ^ 2 * r ‖z - c‖ := by
    intro θ
    have h := setLIntegral_rotAbout c (hT1 θ) R (fun z => ‖u z‖ₑ ^ 2 * r ‖z - c‖)
    simp only [rotAbout_sub c (hT1 θ)] at h
    exact h
  have hmeas : AEMeasurable (Function.uncurry fun (θ : ℝ) (z : V n) =>
      ‖u (rotAbout c (Complex.exp ((θ : ℂ) * I)) z)‖ₑ ^ 2 * r ‖z - c‖)
      ((volume.restrict (Ioc 0 (2 * Real.pi))).prod (volume.restrict (ball c R))) := by
    rw [Measure.prod_restrict]
    have h1 := ((continuousOn_comp_rotAbout hu (Ioc 0 (2 * Real.pi))).aemeasurable
      (μ := volume.prod volume) (measurableSet_Ioc.prod measurableSet_ball)).enorm.pow_const 2
    have h2 : Measurable fun p : ℝ × V n => r ‖p.2 - c‖ :=
      hr.comp ((measurable_snd.sub_const c).norm)
    exact h1.mul h2.aemeasurable
  have hvol : volume (Ioc (0 : ℝ) (2 * Real.pi)) = ENNReal.ofReal (2 * Real.pi) := by
    rw [Real.volume_Ioc, sub_zero]
  have key : (∫⁻ z in ball c R, ‖u z‖ₑ ^ 2 * r ‖z - c‖) * ENNReal.ofReal (2 * Real.pi) =
      ∫⁻ z in ball c R, ∫⁻ θ in Ioc 0 (2 * Real.pi),
        ‖u (rotAbout c (Complex.exp ((θ : ℂ) * I)) z)‖ₑ ^ 2 * r ‖z - c‖ := by
    rw [← hvol, ← setLIntegral_const, ← lintegral_lintegral_swap hmeas]
    exact lintegral_congr fun θ => (hrot θ).symm
  have hmr : Measurable fun z : V n => r ‖z - c‖ := hr.comp (measurable_id.sub_const c).norm
  have low : ‖u c‖ₑ ^ 2 * ENNReal.ofReal (2 * Real.pi) * ∫⁻ z in ball c R, r ‖z - c‖ ≤
      ∫⁻ z in ball c R, ∫⁻ θ in Ioc 0 (2 * Real.pi),
        ‖u (rotAbout c (Complex.exp ((θ : ℂ) * I)) z)‖ₑ ^ 2 * r ‖z - c‖ := by
    rw [← lintegral_const_mul _ hmr]
    refine setLIntegral_mono' measurableSet_ball fun z hz => ?_
    have hw : ‖z - c‖ < R := by rw [mem_ball, dist_eq_norm] at hz; exact hz
    have hcz : Continuous fun θ : ℝ => u (rotAbout c (Complex.exp ((θ : ℂ) * I)) z) :=
      hu.continuousOn.comp_continuous (by unfold rotAbout; fun_prop)
        (fun θ => (rotAbout_mem_ball_iff c (hT1 θ) R z).2 hz)
    have hm : Measurable fun θ : ℝ =>
        ‖u (rotAbout c (Complex.exp ((θ : ℂ) * I)) z)‖ₑ ^ 2 :=
      hcz.measurable.enorm.pow_const 2
    rw [lintegral_mul_const _ hm]
    gcongr
    exact circle_mean_sq hu hw
  have h0 : ENNReal.ofReal (2 * Real.pi) ≠ 0 := (ENNReal.ofReal_pos.2 Real.two_pi_pos).ne'
  refine (ENNReal.mul_le_mul_iff_left h0 ENNReal.ofReal_ne_top).1 ?_
  calc ‖u c‖ₑ ^ 2 * (∫⁻ z in ball c R, r ‖z - c‖) * ENNReal.ofReal (2 * Real.pi)
      = ‖u c‖ₑ ^ 2 * ENNReal.ofReal (2 * Real.pi) * ∫⁻ z in ball c R, r ‖z - c‖ := by ring
    _ ≤ _ := low
    _ = _ := key.symm

end ReciprocityTheory.L2DbarEstimates.C
end

section -- merged from ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.MvDivIntegrand
namespace ReciprocityTheory.L2DbarEstimates.C

open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal

theorem finrank_real_V {n : ℕ} : Module.finrank ℝ (V n) = 2 * n := by
  rw [← Module.finrank_mul_finrank ℝ ℂ (V n), Complex.finrank_real_complex, finrank_euclideanSpace_fin]

theorem mvPow : MVPowStatement := by
  intro n s hn
  haveI : Nontrivial (V n) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_real_V]; omega)
  have hind : (ball (0 : V n) 1).indicator (fun z : V n => ‖z‖ ^ (-2 * s)) =
      fun z => (Iio (1 : ℝ)).indicator (fun y : ℝ => y ^ (-2 * s)) ‖z‖ := by
    funext z
    by_cases h : ‖z‖ < 1 <;> simp [Set.indicator, mem_ball_zero_iff, h]
  rw [← integrable_indicator_iff measurableSet_ball, hind, integrable_fun_norm_addHaar,
    finrank_real_V]
  have hfun : (fun y : ℝ => y ^ (2 * n - 1) • (Iio (1 : ℝ)).indicator (fun y : ℝ => y ^ (-2 * s)) y) =
      (Iio (1 : ℝ)).indicator (fun y : ℝ => y ^ (2 * n - 1) * y ^ (-2 * s)) := by
    funext y
    simp only [indicator_apply, smul_eq_mul]
    split_ifs <;> simp
  rw [hfun, IntegrableOn, integrable_indicator_iff measurableSet_Iio, IntegrableOn,
    Measure.restrict_restrict measurableSet_Iio, Set.inter_comm, Set.Ioi_inter_Iio, ← IntegrableOn]
  have hcongr : EqOn (fun y : ℝ => y ^ (2 * n - 1) * y ^ (-2 * s))
      (fun y : ℝ => y ^ ((2 * n : ℝ) - 1 - 2 * s)) (Ioo 0 1) := by
    intro y hy
    have hy0 : 0 < y := hy.1
    simp only
    rw [← Real.rpow_natCast, ← Real.rpow_add hy0]
    congr 1
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * n)]
    push_cast
    ring
  rw [integrableOn_congr_fun hcongr measurableSet_Ioo,
    intervalIntegral.integrableOn_Ioo_rpow_iff one_pos]
  constructor <;> intro h <;> linarith

theorem mvDiv : MVDivStatement := by
  intro n hn
  have hpow := mvPow n n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set f : ℕ → V n → ℝ≥0∞ := fun k z => ENNReal.ofReal ((‖z‖ ^ 2 + 1 / ((k : ℝ) + 1)) ^ (-(n : ℝ)))
    with hf
  have hmeas : ∀ k, Measurable (f k) := fun k =>
    (by fun_prop : Measurable fun z : V n => ENNReal.ofReal ((‖z‖ ^ 2 + 1 / ((k : ℝ) + 1)) ^ (-(n : ℝ))))
  have hmono : Monotone f := by
    intro k m hkm z
    show ENNReal.ofReal _ ≤ ENNReal.ofReal _
    apply ENNReal.ofReal_le_ofReal
    have hkm' : (k : ℝ) ≤ m := by exact_mod_cast hkm
    apply Real.rpow_le_rpow_of_nonpos (add_pos_of_nonneg_of_pos (sq_nonneg _) (by positivity)) _
      (neg_nonpos.mpr (Nat.cast_nonneg _))
    gcongr
  have hinf : ∫⁻ z in ball (0 : V n) 1, ENNReal.ofReal (‖z‖ ^ (-2 * (n : ℝ))) = ∞ := by
    by_contra h
    have hlt := lt_top_iff_ne_top.mpr h
    have hint : IntegrableOn (fun z : V n => ‖z‖ ^ (-2 * (n : ℝ))) (ball 0 1) := by
      refine ⟨(measurable_norm.pow_const _).aestronglyMeasurable,
        (hasFiniteIntegral_iff_ofReal ?_).mpr hlt⟩
      exact ae_of_all _ fun z => Real.rpow_nonneg (norm_nonneg z) _
    exact lt_irrefl _ (hpow.mp hint)
  have hsup : ∀ z : V n, ENNReal.ofReal (‖z‖ ^ (-2 * (n : ℝ))) ≤ ⨆ k, f k z := by
    intro z
    by_cases hz : z = 0
    · subst hz
      rw [norm_zero, Real.zero_rpow (by linarith), ENNReal.ofReal_zero]
      exact zero_le
    · have hz' : 0 < ‖z‖ := norm_pos_iff.mpr hz
      have h1 : Tendsto (fun k : ℕ => ‖z‖ ^ 2 + 1 / ((k : ℝ) + 1)) atTop (𝓝 (‖z‖ ^ 2 + 0)) :=
        tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
      have h2 := h1.rpow_const (p := -(n : ℝ)) (Or.inl (by positivity))
      have ht : Tendsto (fun k : ℕ => f k z) atTop (𝓝 (ENNReal.ofReal (‖z‖ ^ (-2 * (n : ℝ))))) := by
        show Tendsto (fun k : ℕ => ENNReal.ofReal ((‖z‖ ^ 2 + 1 / ((k : ℝ) + 1)) ^ (-(n : ℝ)))) atTop _
        apply ENNReal.tendsto_ofReal
        convert h2 using 2
        rw [add_zero, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg z)]
        congr 1
        push_cast
        ring
      exact le_of_tendsto' ht (fun k => le_iSup (fun k => f k z) k)
  have hbig : ⨆ k, ∫⁻ z in ball (0 : V n) 1, f k z = ∞ := by
    rw [← lintegral_iSup hmeas hmono]
    refine top_le_iff.mp ?_
    rw [← hinf]
    exact lintegral_mono hsup
  rw [ENNReal.tendsto_nhds_top_iff_nnreal]
  intro M
  have hM : (M : ℝ≥0∞) < ⨆ k, ∫⁻ z in ball (0 : V n) 1, f k z := by
    rw [hbig]
    exact ENNReal.coe_lt_top
  obtain ⟨k, hk⟩ := lt_iSup_iff.mp hM
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / ((k : ℝ) + 1) by positivity)] with δ hδ
  refine hk.trans_le (lintegral_mono fun z => ?_)
  show ENNReal.ofReal _ ≤ ENNReal.ofReal _
  apply ENNReal.ofReal_le_ofReal
  exact Real.rpow_le_rpow_of_nonpos (add_pos_of_nonneg_of_pos (sq_nonneg _) hδ.1)
    (by linarith [hδ.2]) (neg_nonpos.mpr (Nat.cast_nonneg _))

end ReciprocityTheory.L2DbarEstimates.C
end

section -- merged from ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.RegGlue
namespace ReciprocityTheory.L2DbarEstimates.C

open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal

theorem ae_eq_eqOn {n : ℕ} {Ω : Set (V n)} {U U' : V n → ℂ} (hΩ : IsOpen Ω)
    (hU : ContinuousOn U Ω) (hU' : ContinuousOn U' Ω) (h : U =ᵐ[volume.restrict Ω] U') :
    EqOn U U' Ω := by
  exact Measure.eqOn_open_of_ae_eq h hΩ hU hU'

theorem reg_glue {n : ℕ} {Ω : Set (V n)} {u : V n → ℂ} (hΩ : IsOpen Ω)
    (hloc : ∀ x ∈ Ω, ∃ r > 0, ball x r ⊆ Ω ∧
      ∃ U : V n → ℂ, DifferentiableOn ℂ U (ball x r) ∧ u =ᵐ[volume.restrict (ball x r)] U) :
    ∃ U : V n → ℂ, DifferentiableOn ℂ U Ω ∧ u =ᵐ[volume.restrict Ω] U := by
  classical
  choose! r hr hsub U hU hae using hloc
  have agree : ∀ x ∈ Ω, ∀ y ∈ Ω, EqOn (U x) (U y) (ball x (r x) ∩ ball y (r y)) := by
    intro x hx y hy
    apply ae_eq_eqOn (isOpen_ball.inter isOpen_ball)
    · exact ((hU x hx).mono inter_subset_left).continuousOn
    · exact ((hU y hy).mono inter_subset_right).continuousOn
    · have h1 : u =ᵐ[volume.restrict (ball x (r x) ∩ ball y (r y))] U x :=
        ae_restrict_of_ae_restrict_of_subset inter_subset_left (hae x hx)
      have h2 : u =ᵐ[volume.restrict (ball x (r x) ∩ ball y (r y))] U y :=
        ae_restrict_of_ae_restrict_of_subset inter_subset_right (hae y hy)
      exact h1.symm.trans h2
  have loc : ∀ y ∈ Ω, ∀ x ∈ ball y (r y), U x x = U y x := by
    intro y hy x hx
    have hxΩ : x ∈ Ω := hsub y hy hx
    exact agree x hxΩ y hy ⟨mem_ball_self (hr x hxΩ), hx⟩
  refine ⟨fun x => U x x, ?_, ?_⟩
  · intro y hy
    have hnhds : ball y (r y) ∈ 𝓝 y := isOpen_ball.mem_nhds (mem_ball_self (hr y hy))
    have hev : (fun x => U x x) =ᶠ[𝓝 y] U y :=
      Filter.eventually_of_mem hnhds (fun x hx => loc y hy x hx)
    exact (((hU y hy).differentiableAt hnhds).congr_of_eventuallyEq hev).differentiableWithinAt
  · obtain ⟨T, hTc, hT⟩ := TopologicalSpace.isOpen_iUnion_countable
      (fun x : Ω => ball (x : V n) (r x)) (fun _ => isOpen_ball)
    have hcov : Ω = ⋃ x ∈ T, ball ((x : Ω) : V n) (r x) := by
      rw [hT]
      ext z
      simp only [mem_iUnion]
      constructor
      · intro hz
        exact ⟨⟨z, hz⟩, mem_ball_self (hr z hz)⟩
      · rintro ⟨x, hx⟩
        exact hsub x x.2 hx
    rw [hcov, Filter.EventuallyEq, ae_restrict_biUnion_iff _ hTc]
    intro x _
    filter_upwards [hae x x.2, self_mem_ae_restrict (measurableSet_ball (x := (x : V n)) (ε := r x))]
      with z hz hzb
    rw [hz]
    exact (loc x x.2 z hzb).symm

end ReciprocityTheory.L2DbarEstimates.C
end

section -- merged from ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.IntegralBumpProfOnePos
namespace ReciprocityTheory.L2DbarEstimates.C

open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal

variable {n : ℕ}

noncomputable def bumpProf (t s : ℝ) : ℝ := Real.smoothTransition (1 - 4 * (s / t) ^ 2)

noncomputable def mollConst (n : ℕ) : ℝ := (∫ z : V n, bumpProf 1 ‖z‖)⁻¹

noncomputable def mollProf (n : ℕ) (t s : ℝ) : ℝ := mollConst n * (t ^ (2 * n))⁻¹ * bumpProf t s

noncomputable def moll (n : ℕ) (t : ℝ) (z : V n) : ℝ := mollProf n t ‖z‖

noncomputable def mollify (n : ℕ) (t : ℝ) (u : V n → ℂ) (x : V n) : ℂ :=
  ∫ y, (moll n t (x - y) : ℂ) * u y

theorem finrank_V (n : ℕ) : Module.finrank ℝ (V n) = 2 * n := by
  rw [← Module.finrank_mul_finrank ℝ ℂ (V n), Complex.finrank_real_complex, finrank_euclideanSpace,
    Fintype.card_fin]

theorem bumpProf_scale {t : ℝ} (ht : 0 < t) (z : V n) : bumpProf t ‖z‖ = bumpProf 1 ‖t⁻¹ • z‖ := by
  simp only [bumpProf, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ht, div_one]
  congr 1
  ring

theorem integral_bumpProf {t : ℝ} (ht : 0 < t) :
    ∫ z : V n, bumpProf t ‖z‖ = t ^ (2 * n) * ∫ z : V n, bumpProf 1 ‖z‖ := by
  simp_rw [bumpProf_scale ht]
  rw [Measure.integral_comp_inv_smul_of_nonneg volume (fun z : V n => bumpProf 1 ‖z‖) ht.le,
    finrank_V, smul_eq_mul]

private lemma bumpProf_eq_zero_of_half_lt {t s : ℝ} (ht : 0 < t) (hs : t / 2 < s) : bumpProf t s = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have h1 : 1 / 2 < s / t := by rw [lt_div_iff₀ ht]; linarith
  nlinarith

private lemma continuous_bumpProf_norm (n : ℕ) (t : ℝ) : Continuous (fun z : V n => bumpProf t ‖z‖) :=
  Real.smoothTransition.continuous.comp (by fun_prop)

theorem integral_bumpProf_one_pos (n : ℕ) : 0 < ∫ z : V n, bumpProf 1 ‖z‖ := by
  have hcs : HasCompactSupport (fun z : V n => bumpProf 1 ‖z‖) := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : V n) (1 / 2)) fun z hz => ?_
    rw [mem_closedBall, dist_zero_right, not_le] at hz
    exact bumpProf_eq_zero_of_half_lt one_pos hz
  refine (continuous_bumpProf_norm n 1).integral_pos_of_hasCompactSupport_nonneg_nonzero hcs
    (fun z => Real.smoothTransition.nonneg _) (x := 0) ?_
  simp [bumpProf]

theorem mollConst_nonneg (n : ℕ) : 0 ≤ mollConst n := by
  unfold mollConst
  exact inv_nonneg.mpr (integral_nonneg fun z => Real.smoothTransition.nonneg _)

theorem moll_nonneg (n : ℕ) (t : ℝ) (z : V n) : 0 ≤ moll n t z := by
  have h : 0 ≤ t ^ (2 * n) := by rw [pow_mul]; positivity
  exact mul_nonneg (mul_nonneg (mollConst_nonneg n) (inv_nonneg.mpr h)) (Real.smoothTransition.nonneg _)

theorem moll_contDiff (n : ℕ) (t : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (moll n t) := by
  have h : moll n t = fun z => mollConst n * (t ^ (2 * n))⁻¹ *
      Real.smoothTransition (1 - 4 * (‖z‖ ^ 2 / t ^ 2)) := by
    funext z
    simp only [moll, mollProf, bumpProf, div_pow]
  rw [h]
  exact contDiff_const.mul (Real.smoothTransition.contDiff.comp
    (contDiff_const.sub (contDiff_const.mul ((contDiff_norm_sq ℂ).div_const _))))

theorem moll_tsupport (n : ℕ) {t : ℝ} (ht : 0 < t) : tsupport (moll n t) ⊆ closedBall 0 (t / 2) := by
  refine closure_minimal (fun z hz => ?_) isClosed_closedBall
  by_contra hnot
  rw [mem_closedBall, dist_zero_right, not_le] at hnot
  apply hz
  simp only [moll, mollProf, bumpProf_eq_zero_of_half_lt ht hnot, mul_zero]

theorem moll_hasCompactSupport (n : ℕ) {t : ℝ} (ht : 0 < t) : HasCompactSupport (moll n t) := by
  exact (isCompact_closedBall (0 : V n) (t / 2)).of_isClosed_subset (isClosed_tsupport _)
    (moll_tsupport n ht)

theorem moll_integral (n : ℕ) {t : ℝ} (ht : 0 < t) : ∫ z : V n, moll n t z = 1 := by
  simp only [moll, mollProf]
  rw [integral_const_mul, integral_bumpProf ht, mollConst]
  have h1 := integral_bumpProf_one_pos n
  have h2 : t ^ (2 * n) ≠ 0 := pow_ne_zero _ ht.ne'
  field_simp

theorem moll_le (n : ℕ) :
    ∃ C : ℝ, ∀ t : ℝ, 0 < t → ∀ z : V n, moll n t z ≤ C / volume.real (ball (0 : V n) t) := by
  refine ⟨mollConst n * volume.real (ball (0 : V n) 1), fun t ht z => ?_⟩
  have hv : 0 < volume.real (ball (0 : V n) 1) :=
    ENNReal.toReal_pos (measure_ball_pos volume (0 : V n) one_pos).ne' measure_ball_lt_top.ne
  have hball : volume.real (ball (0 : V n) t) = t ^ (2 * n) * volume.real (ball (0 : V n) 1) := by
    rw [measureReal_def, measureReal_def, Measure.addHaar_ball_of_pos volume (0 : V n) ht, finrank_V,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_pos ht _).le]
  rw [hball, mul_div_mul_right _ _ hv.ne']
  have htp : 0 < t ^ (2 * n) := pow_pos ht _
  have hb : bumpProf t ‖z‖ ≤ 1 := Real.smoothTransition.le_one _
  have hc := mollConst_nonneg n
  simp only [moll, mollProf]
  calc mollConst n * (t ^ (2 * n))⁻¹ * bumpProf t ‖z‖
      ≤ mollConst n * (t ^ (2 * n))⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left hb (mul_nonneg hc (inv_nonneg.mpr htp.le))
    _ = mollConst n / t ^ (2 * n) := by ring

end ReciprocityTheory.L2DbarEstimates.C
end
