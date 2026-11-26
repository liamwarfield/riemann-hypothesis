module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionsDimZero
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionsRank
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLiftBirationalNef

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockResolutionImageSup
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M MeasureTheory Set Filter Topology

noncomputable section

namespace BlockResolutionImageSup

theorem analyticOnNhd_eval {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {σ : Type*} {V : Set E}
    {g : E → σ → ℂ} (hg : ∀ i, AnalyticOnNhd ℂ (fun w => g w i) V) (f : MvPolynomial σ ℂ) :
    AnalyticOnNhd ℂ (fun w => eval (g w) f) V := by
  induction f using MvPolynomial.induction_on with
  | C a => simpa using (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : E => a) V)
  | add p q hp hq => exact fun w hw => by simpa using (hp w hw).fun_add (hq w hw)
  | mul_X p i hp => exact fun w hw => by simpa using (hp w hw).fun_mul (hg i w hw)

theorem sq_div_pow_eq {a r : ℝ} (hr : 0 < r) (n : ℕ) :
    (a / r ^ n) ^ 2 = a ^ 2 * Real.exp (-(n : ℝ) * (2 * Real.log r)) := by
  have h : Real.exp (-(n : ℝ) * (2 * Real.log r)) = ((r ^ n) ^ 2)⁻¹ := by
    rw [show -(n : ℝ) * (2 * Real.log r) = -Real.log ((r ^ n) ^ 2) by
      rw [Real.log_pow, Real.log_pow]; push_cast; ring, Real.exp_neg, Real.exp_log (by positivity)]
  rw [h, div_pow, div_eq_mul_inv]

theorem lintegral_chart_le {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] {e : ℕ}
    (φ : OpenPartialHomeomorph X (Fin e → ℂ)) (μ : Measure X) {ν : (Fin e → ℂ) → ℝ}
    (hν : ContinuousOn ν φ.target)
    (hμ : ∀ S : Set X, MeasurableSet S → S ⊆ φ.source →
      μ S = ∫⁻ y in φ.target ∩ φ.symm ⁻¹' S, ENNReal.ofReal (ν y))
    {g : X → ENNReal} (hg : Measurable g) :
    ∫⁻ z in φ.target, ENNReal.ofReal (ν z) * g (φ.symm z) ≤ ∫⁻ y, g y ∂μ := by
  have hT : MeasurableSet φ.target := φ.open_target.measurableSet
  have hs : AEMeasurable φ.symm (volume.restrict φ.target) := φ.continuousOn_symm.aemeasurable hT
  have hνm : AEMeasurable (fun z => ENNReal.ofReal (ν z)) (volume.restrict φ.target) :=
    ENNReal.measurable_ofReal.comp_aemeasurable (hν.aemeasurable hT)
  have hs' : AEMeasurable φ.symm
      ((volume.restrict φ.target).withDensity fun z => ENNReal.ofReal (ν z)) :=
    hs.mono_ac (withDensity_absolutelyContinuous _ _)
  have hmap : Measure.map φ.symm ((volume.restrict φ.target).withDensity fun z => ENNReal.ofReal (ν z)) =
      μ.restrict φ.source := by
    ext S hS
    have hset : φ.symm ⁻¹' S ∩ φ.target = φ.target ∩ φ.symm ⁻¹' (S ∩ φ.source) := by
      ext z
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h2, h1, φ.map_target h2⟩
      · rintro ⟨h2, h1, -⟩
        exact ⟨h1, h2⟩
    rw [Measure.map_apply_of_aemeasurable hs' hS, withDensity_apply' _ _, Measure.restrict_restrict' hT,
      Measure.restrict_apply hS, hμ _ (hS.inter φ.open_source.measurableSet) inter_subset_right, hset]
  calc ∫⁻ z in φ.target, ENNReal.ofReal (ν z) * g (φ.symm z)
      = ∫⁻ z, g (φ.symm z) ∂((volume.restrict φ.target).withDensity fun z => ENNReal.ofReal (ν z)) :=
        (lintegral_withDensity_eq_lintegral_mul₀ hνm (hg.comp_aemeasurable hs)).symm
    _ = ∫⁻ y, g y ∂(Measure.map φ.symm
          ((volume.restrict φ.target).withDensity fun z => ENNReal.ofReal (ν z))) :=
        (lintegral_map' hg.aemeasurable hs').symm
    _ = ∫⁻ y in φ.source, g y ∂μ := by rw [hmap]
    _ ≤ ∫⁻ y, g y ∂μ := setLIntegral_le_lintegral _ _

variable {D : ℕ} {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {Ω : Type} [Field Ω] [CharZero Ω]


omit [DecidableEq K] [∀ k, Fintype (ι k)] in
theorem isOpen_blockNonzero : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  simp only [Set.ofPred_forall, Set.ofPred_exists]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

theorem eval_torus {f : MRingOver ℂ ι} {k₀ : K} {n : ℕ} (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f (blockDeg k₀ n))
    (c : K → ℂ) (z : (Σ k, ι k) → ℂ) :
    eval (fun p => c p.1 * z p) f = c k₀ ^ n * eval z f := by
  rw [eval_eq', eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg := hf m hm
  have hc : ∏ p : (Σ k, ι k), c p.1 ^ m p = c k₀ ^ n := by
    rw [Fintype.prod_sigma]
    simp_rw [Finset.prod_pow_eq_pow_sum, hdeg]
    rw [Fintype.prod_eq_single k₀ fun k hk => by simp [blockDeg, hk]]
    simp [blockDeg]
  simp_rw [mul_pow, Finset.prod_mul_distrib, hc]
  ring

theorem normRatio_torus {f : MRingOver ℂ ι} {k₀ : K} {n : ℕ} (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f (blockDeg k₀ n))
    (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (hA : A.a = unitDeg k₀) {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    ‖eval z f‖ / A.h z ^ n = ‖eval z' f‖ / A.h z' ^ n := by
  obtain ⟨c, hc, rfl⟩ := h
  rw [eval_torus hf, A.smul c z' hc, hA]
  have hprod : ∏ k, ‖c k‖ ^ unitDeg k₀ k = ‖c k₀‖ := by
    rw [Fintype.prod_eq_single k₀ fun k hk => by simp [unitDeg, hk]]
    simp [unitDeg]
  rw [hprod, norm_mul, norm_pow, mul_pow]
  have : ‖c k₀‖ ^ n ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 (hc k₀))
  rw [mul_div_mul_left _ _ this]

theorem lift_blockNonzero (d : HSMBlockDatum D K ι Ω) {x y : d.R.X} (hy : y ∈ d.R.U x) :
    ∀ k, ∃ i, d.R.lift x y ⟨k, i⟩ ≠ 0 :=
  (d.R.mem x y hy).1

theorem ratio_blockPt_eq (d : HSMBlockDatum D K ι Ω) {n : ℕ} {f : MRingOver ℂ ι}
    (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f (blockDeg d.k₀ n)) {x y : d.R.X} (hy : y ∈ d.R.U x) :
    ‖eval (blockPt d y) f‖ / d.A.h (blockPt d y) ^ n =
      ‖eval (d.R.lift x y) f‖ / d.A.h (d.R.lift x y) ^ n :=
  normRatio_torus hf d.A d.deg (d.R.compat y x y ⟨d.R.mem_U y, hy⟩)

theorem continuous_ratio (d : HSMBlockDatum D K ι Ω) {n : ℕ} {f : MRingOver ℂ ι}
    (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f (blockDeg d.k₀ n)) :
    Continuous fun y => ‖eval (blockPt d y) f‖ / d.A.h (blockPt d y) ^ n := by
  rw [continuous_iff_continuousAt]
  intro y₀
  obtain ⟨j, hj⟩ := d.R.A.cover y₀
  set e := d.R.A.chart j with he
  have hL : ContinuousAt (d.R.lift y₀) y₀ := by
    rw [continuousAt_pi]
    intro p
    have ha : AnalyticAt ℂ ((fun y => d.R.lift y₀ y p) ∘ e.symm) (e y₀) :=
      d.R.holo y₀ p j (e y₀) ⟨e.map_source hj, by rw [mem_preimage, e.left_inv hj]; exact d.R.mem_U y₀⟩
    refine (ha.continuousAt.comp (e.continuousAt hj)).congr ?_
    filter_upwards [e.open_source.mem_nhds hj] with y hy
    simp only [Function.comp_apply, e.left_inv hy]
  have hne := lift_blockNonzero d (d.R.mem_U y₀)
  have hh : ContinuousAt d.A.h (d.R.lift y₀ y₀) :=
    d.semipos.1.continuousOn.continuousAt (isOpen_blockNonzero.mem_nhds hne)
  have hcont : ContinuousAt (fun y => ‖eval (d.R.lift y₀ y) f‖ / d.A.h (d.R.lift y₀ y) ^ n) y₀ :=
    (((MvPolynomial.continuous_eval f).continuousAt.comp hL).norm).div ((hh.comp hL).pow n)
      (pow_pos (d.A.pos _ hne) n).ne'
  refine hcont.congr ?_
  filter_upwards [(d.R.isOpen_U y₀).mem_nhds (d.R.mem_U y₀)] with y hy
  exact (ratio_blockPt_eq d hf hy).symm

theorem local_bound (hC : ChartSupBound.Statement) (d : HSMBlockDatum D K ι Ω) (x₀ : d.R.X) :
    ∃ N : Set d.R.X, IsOpen N ∧ x₀ ∈ N ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n →
      ∀ f : MRingOver ℂ ι, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f (blockDeg d.k₀ n) → ∀ y ∈ N,
        (‖eval (blockPt d y) f‖ / d.A.h (blockPt d y) ^ n) ^ 2 ≤
          C * (n : ℝ) ^ D * blockL2NormComplex d n f ^ 2 := by
  have : IsProbabilityMeasure d.dV := d.vol.1
  obtain ⟨j, hj⟩ := d.R.A.cover x₀
  set e := d.R.A.chart j with he
  obtain ⟨ν, hνs, hνpos, hνV⟩ := d.vol.2 j
  have hVo : IsOpen (e.target ∩ e.symm ⁻¹' d.R.U x₀) := e.isOpen_inter_preimage_symm (d.R.isOpen_U x₀)
  have hx₀V : e x₀ ∈ e.target ∩ e.symm ⁻¹' d.R.U x₀ :=
    ⟨e.map_source hj, by rw [mem_preimage, e.left_inv hj]; exact d.R.mem_U x₀⟩
  obtain ⟨δ, hδ, hδV⟩ := Metric.isOpen_iff.1 hVo _ hx₀V
  have hKV : Metric.closedBall (e x₀) (δ / 2) ⊆ e.target ∩ e.symm ⁻¹' d.R.U x₀ :=
    (Metric.closedBall_subset_ball (half_lt_self hδ)).trans hδV
  have hLa : ∀ p, AnalyticOnNhd ℂ (fun w => d.R.lift x₀ (e.symm w) p) (e.target ∩ e.symm ⁻¹' d.R.U x₀) :=
    fun p => d.R.holo x₀ p j
  have hLne : ∀ w ∈ e.target ∩ e.symm ⁻¹' d.R.U x₀, ∀ k, ∃ i, d.R.lift x₀ (e.symm w) ⟨k, i⟩ ≠ 0 :=
    fun w hw => lift_blockNonzero d hw.2
  have hψ : ContDiffOn ℝ 2 (fun w => 2 * Real.log (d.A.h (d.R.lift x₀ (e.symm w))))
      (e.target ∩ e.symm ⁻¹' d.R.U x₀) := by
    have hL2 : ContDiffOn ℝ 2 (fun w => d.R.lift x₀ (e.symm w)) (e.target ∩ e.symm ⁻¹' d.R.U x₀) :=
      contDiffOn_pi.2 fun p => ((hLa p).contDiffOn_of_completeSpace).restrict_scalars ℝ
    have hh : ContDiffOn ℝ 2 (fun w => d.A.h (d.R.lift x₀ (e.symm w))) (e.target ∩ e.symm ⁻¹' d.R.U x₀) :=
      (d.semipos.1.of_le (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))).comp hL2 fun w hw => hLne w hw
    exact contDiffOn_const.mul (hh.log fun w hw => (d.A.pos _ (hLne w hw)).ne')
  obtain ⟨C₀, hC₀⟩ := hC D (e.target ∩ e.symm ⁻¹' d.R.U x₀) (Metric.closedBall (e x₀) (δ / 2)) _ ν hVo
    (isCompact_closedBall _ _) hKV hψ (hνs.continuousOn.mono inter_subset_left) fun z hz => hνpos z hz.1
  refine ⟨e.source ∩ e ⁻¹' Metric.ball (e x₀) (δ / 2), e.isOpen_inter_preimage Metric.isOpen_ball,
    ⟨hj, Set.mem_preimage.mpr (Metric.mem_ball_self (half_pos hδ))⟩, max C₀ 0, le_max_right _ _, fun n hn f hf y hy => ?_⟩
  have hgc := (continuous_ratio d hf).pow 2
  have hgm : Measurable fun y => ENNReal.ofReal ((‖eval (blockPt d y) f‖ / d.A.h (blockPt d y) ^ n) ^ 2) :=
    ENNReal.measurable_ofReal.comp hgc.measurable
  have hgi : Integrable (fun y => (‖eval (blockPt d y) f‖ / d.A.h (blockPt d y) ^ n) ^ 2) d.dV :=
    hgc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hI0 : 0 ≤ ∫ y, (‖eval (blockPt d y) f‖ / d.A.h (blockPt d y) ^ n) ^ 2 ∂d.dV :=
    integral_nonneg fun y => sq_nonneg _
  have hres : blockL2NormComplex d n f ^ 2 = ∫ y, (‖eval (blockPt d y) f‖ / d.A.h (blockPt d y) ^ n) ^ 2 ∂d.dV := by
    rw [blockL2NormComplex, Real.sq_sqrt hI0]
  have hid : ∀ w ∈ e.target ∩ e.symm ⁻¹' d.R.U x₀,
      ‖eval (d.R.lift x₀ (e.symm w)) f‖ ^ 2 *
          Real.exp (-(n : ℝ) * (2 * Real.log (d.A.h (d.R.lift x₀ (e.symm w))))) =
        (‖eval (blockPt d (e.symm w)) f‖ / d.A.h (blockPt d (e.symm w)) ^ n) ^ 2 := by
    intro w hw
    rw [ratio_blockPt_eq d hf hw.2]
    exact (sq_div_pow_eq (d.A.pos _ (hLne w hw)) n).symm
  have key := hC₀ n hn _ (analyticOnNhd_eval hLa f) (e y) (Metric.ball_subset_closedBall hy.2)
  have hyV : e y ∈ e.target ∩ e.symm ⁻¹' d.R.U x₀ := hKV (Metric.ball_subset_closedBall hy.2)
  rw [hid _ hyV, e.left_inv hy.1] at key
  have hint : ∫⁻ z in e.target ∩ e.symm ⁻¹' d.R.U x₀,
      ENNReal.ofReal (‖eval (d.R.lift x₀ (e.symm z)) f‖ ^ 2 *
        Real.exp (-(n : ℝ) * (2 * Real.log (d.A.h (d.R.lift x₀ (e.symm z))))) * ν z) ≤
      ENNReal.ofReal (blockL2NormComplex d n f ^ 2) := by
    rw [hres, ofReal_integral_eq_lintegral_ofReal hgi (Eventually.of_forall fun y => sq_nonneg _)]
    calc _ = ∫⁻ z in e.target ∩ e.symm ⁻¹' d.R.U x₀, ENNReal.ofReal (ν z) *
            ENNReal.ofReal ((‖eval (blockPt d (e.symm z)) f‖ / d.A.h (blockPt d (e.symm z)) ^ n) ^ 2) := by
          refine setLIntegral_congr_fun hVo.measurableSet fun z hz => ?_
          rw [hid z hz, mul_comm, ENNReal.ofReal_mul (hνpos z hz.1).le]
      _ ≤ ∫⁻ z in e.target, ENNReal.ofReal (ν z) *
            ENNReal.ofReal ((‖eval (blockPt d (e.symm z)) f‖ / d.A.h (blockPt d (e.symm z)) ^ n) ^ 2) :=
          lintegral_mono_set inter_subset_left
      _ ≤ _ := lintegral_chart_le e d.dV hνs.continuousOn hνV hgm
  have hn0 : (0 : ℝ) ≤ (n : ℝ) ^ D := by positivity
  have h2 : ENNReal.ofReal ((‖eval (blockPt d y) f‖ / d.A.h (blockPt d y) ^ n) ^ 2) ≤
      ENNReal.ofReal (max C₀ 0 * (n : ℝ) ^ D * blockL2NormComplex d n f ^ 2) := by
    rw [ENNReal.ofReal_mul (by positivity)]
    exact key.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hn0)) hint)
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h2

end BlockResolutionImageSup


open BlockResolutionImageSup in
theorem BlockResolutionImageSup.proof (hC : ChartSupBound.Statement) : BlockResolutionImageSup.Statement := by
  intro D K _ _ ι _ Ω _ _ d
  choose N hNo hxN C hC0 hCb using fun x => local_bound hC d x
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover N hNo fun x _ => mem_iUnion.2 ⟨x, hxN x⟩
  refine ⟨Real.sqrt (∑ x ∈ t, C x), fun n hn f hf y => ?_⟩
  obtain ⟨x, hxt, hyx⟩ := mem_iUnion₂.1 (ht (mem_univ y))
  have hS : C x ≤ ∑ x ∈ t, C x := Finset.single_le_sum (fun i _ => hC0 i) hxt
  have hS0 : 0 ≤ ∑ x ∈ t, C x := Finset.sum_nonneg fun i _ => hC0 i
  have hr0 : 0 ≤ blockL2NormComplex d n f := Real.sqrt_nonneg _
  have hn0 : (0 : ℝ) ≤ (n : ℝ) ^ D := by positivity
  have h2 : (‖eval (blockPt d y) f‖ / d.A.h (blockPt d y) ^ n) ^ 2 ≤
      (∑ x ∈ t, C x) * (n : ℝ) ^ D * blockL2NormComplex d n f ^ 2 :=
    (hCb x n hn f hf y hyx).trans (by gcongr)
  have hp : 0 ≤ ‖eval (blockPt d y) f‖ / d.A.h (blockPt d y) ^ n :=
    div_nonneg (norm_nonneg _) (pow_nonneg (d.A.pos _ (lift_blockNonzero d (d.R.mem_U y))).le n)
  have hpow : Real.sqrt ((n : ℝ) ^ D) = (n : ℝ) ^ ((D : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
    ring_nf
  calc ‖eval (blockPt d y) f‖ / d.A.h (blockPt d y) ^ n
      = Real.sqrt ((‖eval (blockPt d y) f‖ / d.A.h (blockPt d y) ^ n) ^ 2) := (Real.sqrt_sq hp).symm
    _ ≤ Real.sqrt ((∑ x ∈ t, C x) * (n : ℝ) ^ D * blockL2NormComplex d n f ^ 2) := Real.sqrt_le_sqrt h2
    _ = Real.sqrt (∑ x ∈ t, C x) * (n : ℝ) ^ ((D : ℝ) / 2) * blockL2NormComplex d n f := by
      rw [Real.sqrt_mul (mul_nonneg hS0 hn0), Real.sqrt_mul hS0, Real.sqrt_sq hr0, hpow]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionProduct
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace SectionProduct

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


omit [Fintype K] in
theorem isMultiHomog_pow {g : MRing ι} {d : K → ℕ} (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g d) (j : ℕ) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (g ^ j) (j • d) := by
  induction j with
  | zero =>
    rw [pow_zero, zero_smul]
    classical
    intro m hm k
    have h : (1 : MRing ι) = monomial 0 1 := by simp
    rw [h] at hm
    rw [Finset.mem_singleton.mp (support_monomial_subset hm)]
    simp
  | succ j ih =>
    rw [pow_succ, succ_nsmul]
    classical
    intro m hm k
    obtain ⟨m₁, hm₁, m₂, hm₂, rfl⟩ := Finset.mem_add.mp (support_mul _ _ hm)
    simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply]
    rw [ih m₁ hm₁ k, hg m₂ hm₂ k]

end SectionProduct


open SectionBoundedMul SectionProduct in
theorem SectionProduct.proof : SectionProduct.Statement := open SectionBoundedMul in by
  intro K _ ι _ Ω _ y A B C n j τ s t hdeg hmet hs ht
  have hdk : ∀ k, (τ : ℤ) * C.a k = (n : ℤ) * A.a k + (j : ℤ) * B.a k := fun k => by
    have := congrFun hdeg k
    simpa [smul_eq_mul] using this
  refine ⟨?_, ?_⟩
  ·
    intro c hc
    have hs' := hs c hc
    have ht' := ht c hc
    have heq : s * t ^ j * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * C.a k)) =
        (s * ∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * A.a k))) *
          (t * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * B.a k))) ^ j := by
      have hp : ∀ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * C.a k)) =
          y ⟨k, c k⟩ ^ (-((n : ℤ) * A.a k)) * (y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * B.a k))) ^ j := fun k => by
        have h0 := hc k
        rw [← zpow_natCast (y ⟨k, c k⟩ ^ _) j, ← zpow_mul, ← zpow_add₀ h0, hdk k]
        congr 1
        push_cast
        ring
      simp only [hp, Finset.prod_mul_distrib, Finset.prod_pow]
      ring
    rw [heq]
    exact mul_mem hs' (pow_mem ht' j)
  ·
    intro cc cc' hbs hbt dG dH G H z hG hH hdGH hrep hz
    choose c hc using hz.1
    have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := by
      intro k h0
      have hX := isMultiHomog_monomial (ι := ι) (Finsupp.single (⟨k, c k⟩ : Σ k, ι k) 1) 1
      rw [← X] at hX
      have hmem := mem_mCoordIdeal_of_aeval_eq_zero y hX (by rw [aeval_X, h0])
      have hz0 := hz.2 _ hmem
      simp only [map_X, eval_X] at hz0
      exact hc k hz0
    obtain ⟨N, dgs, gs, hgs, hdgs, hvs⟩ := exists_chartForm y A.a n hs c hy
    obtain ⟨M, dgt, gt, hgt, hdgt, hvt⟩ := exists_chartForm y B.a 1 ht c hy
    have bs := hbs dgs N gs (chartMono c N) z hgs (isMultiHomog_chartMono c N) hdgs hvs hz
    have bt := hbt dgt M gt (chartMono c M) z hgt (isMultiHomog_chartMono c M) hdgt hvt hz

    have hdeq : dgs + j • dgt + dH = dG + (N + j • M) := by
      funext k
      have e1 := hdgs k
      have e2 := hdgt k
      have e3 := hdGH k
      have e4 := hdk k
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have : ((dgs k + j * dgt k + dH k : ℕ) : ℤ) = ((dG k + (N k + j * M k) : ℕ) : ℤ) := by
        push_cast at e1 e2 e3 ⊢
        linear_combination e1 + (j : ℤ) * e2 - e3 - e4
      exact_mod_cast this
    have hF : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (gs * gt ^ j * H - G * chartMono c (N + j • M)) (dgs + j • dgt + dH) := by
      refine isMultiHomog_sub (isMultiHomog_mul (isMultiHomog_mul hgs (isMultiHomog_pow hgt j)) hH) ?_
      rw [hdeq]
      exact isMultiHomog_mul hG (isMultiHomog_chartMono c (N + j • M))
    have hmono : ∀ {R : Type} [CommRing R] (w : (Σ k, ι k) → R),
        ∏ k, w ⟨k, c k⟩ ^ (N + j • M) k = (∏ k, w ⟨k, c k⟩ ^ N k) * (∏ k, w ⟨k, c k⟩ ^ M k) ^ j := by
      intro R _ w
      rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun k _ => by
        rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul, pow_add, pow_mul']
    have hF0 : aeval y (gs * gt ^ j * H - G * chartMono c (N + j • M)) = 0 := by
      rw [map_sub, map_mul, map_mul, map_pow, map_mul, hvs, hvt, hrep, aeval_chartMono, aeval_chartMono,
        aeval_chartMono, hmono]
      ring
    have hz0 := hz.2 _ (mem_mCoordIdeal_of_aeval_eq_zero y hF hF0)
    simp only [map_sub, map_mul, map_pow] at hz0
    rw [sub_eq_zero] at hz0

    set ev : MRing ι → ℂ := fun f => eval z (map (Int.castRingHom ℂ) f) with hev
    have hmz : ev (chartMono c (N + j • M)) = ev (chartMono c N) * ev (chartMono c M) ^ j := by
      simp only [hev, eval_chartMono]
      exact hmono z
    have hpos : 0 < ‖ev (chartMono c N)‖ * ‖ev (chartMono c M)‖ ^ j := by
      refine mul_pos (norm_pos_iff.mpr ?_) (pow_pos (norm_pos_iff.mpr ?_) j) <;>
      · simp only [hev, eval_chartMono]
        exact Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
    have key : ‖ev G‖ * (‖ev (chartMono c N)‖ * ‖ev (chartMono c M)‖ ^ j) =
        ‖ev gs‖ * ‖ev gt‖ ^ j * ‖ev H‖ := by
      rw [← norm_pow, ← norm_mul, ← hmz, ← norm_mul, ← norm_pow, ← norm_mul, ← norm_mul]
      exact congrArg norm hz0.symm
    have hprod : ‖ev gs‖ * ‖ev gt‖ ^ j ≤
        (cc * ‖ev (chartMono c N)‖ * A.h z ^ n) * (cc' * ‖ev (chartMono c M)‖ * B.h z ^ 1) ^ j :=
      mul_le_mul bs (pow_le_pow_left₀ (norm_nonneg _) bt j) (pow_nonneg (norm_nonneg _) j)
        ((norm_nonneg _).trans bs)
    rw [hmet z hz]
    refine le_of_mul_le_mul_right ?_ hpos
    rw [key]
    calc ‖ev gs‖ * ‖ev gt‖ ^ j * ‖ev H‖
        ≤ (cc * ‖ev (chartMono c N)‖ * A.h z ^ n) * (cc' * ‖ev (chartMono c M)‖ * B.h z ^ 1) ^ j * ‖ev H‖ :=
          mul_le_mul_of_nonneg_right hprod (norm_nonneg _)
      _ = cc * cc' ^ j * ‖ev H‖ * (A.h z ^ n * B.h z ^ j) *
            (‖ev (chartMono c N)‖ * ‖ev (chartMono c M)‖ ^ j) := by
          ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PAnResNullForm
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M MeasureTheory Filter Topology Set

noncomputable section

namespace AnResNullForm

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem sameOrbit_trans_nf {a b c : (Σ k, ι k) → ℂ} (h1 : SameOrbit a b) (h2 : SameOrbit b c) :
    SameOrbit a c := by
  obtain ⟨c1, hc1, rfl⟩ := h1
  obtain ⟨c2, hc2, rfl⟩ := h2
  exact ⟨fun k => c1 k * c2 k, fun k => mul_ne_zero (hc1 k) (hc2 k), by funext q; simp [mul_assoc]⟩

theorem sameOrbit_symm_nf {a b : (Σ k, ι k) → ℂ} (h : SameOrbit a b) : SameOrbit b a := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), ?_⟩
  funext q
  simp [← mul_assoc, inv_mul_cancel₀ (hc q.1)]

theorem isClosed_blockProportional :
    IsClosed {q : ((Σ k, ι k) → ℂ) × ((Σ k, ι k) → ℂ) |
      ∀ k (i i' : ι k), q.1 ⟨k, i⟩ * q.2 ⟨k, i'⟩ = q.1 ⟨k, i'⟩ * q.2 ⟨k, i⟩} := by
  simp only [ofPred_forall]
  refine isClosed_iInter fun k => isClosed_iInter fun i => isClosed_iInter fun i' => isClosed_eq ?_ ?_ <;>
    fun_prop

theorem blockProportional_of_sameOrbit {a b : (Σ k, ι k) → ℂ} (h : SameOrbit a b) :
    ∀ k (i i' : ι k), a ⟨k, i⟩ * b ⟨k, i'⟩ = a ⟨k, i'⟩ * b ⟨k, i⟩ := by
  obtain ⟨c, -, rfl⟩ := h
  intro k i i'
  ring

theorem sameOrbit_of_blockProportional {a b : (Σ k, ι k) → ℂ} (ha : ∀ k, ∃ i, a ⟨k, i⟩ ≠ 0)
    (hb : ∀ k, ∃ i, b ⟨k, i⟩ ≠ 0) (h : ∀ k (i i' : ι k), a ⟨k, i⟩ * b ⟨k, i'⟩ = a ⟨k, i'⟩ * b ⟨k, i⟩) :
    SameOrbit a b := by
  choose p hp using hb
  refine ⟨fun k => a ⟨k, p k⟩ / b ⟨k, p k⟩, fun k => ?_, ?_⟩
  · intro h0
    obtain ⟨i, hi⟩ := ha k
    have h1 := h k i (p k)
    rcases div_eq_zero_iff.1 h0 with h0 | h0
    · rw [h0, zero_mul] at h1
      exact hi ((mul_eq_zero_iff_right (hp k)).1 h1)
    · exact hp k h0
  · funext ⟨k, i⟩
    show a ⟨k, i⟩ = a ⟨k, p k⟩ / b ⟨k, p k⟩ * b ⟨k, i⟩
    rw [div_mul_eq_mul_div, eq_div_iff (hp k)]
    exact h k i (p k)

theorem eval_eq_zero_iff_of_sameOrbit {G : MRing ι} {dG : K → ℕ} (hG : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog G dG)
    {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    eval z (map (Int.castRingHom ℂ) G) = 0 ↔ eval z' (map (Int.castRingHom ℂ) G) = 0 := by
  obtain ⟨c, hc, rfl⟩ := h
  rw [eval_smul_of_isMultiHomog hG,
    mul_eq_zero_iff_left (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k))]

variable {P J : Ideal (MRing ι)} {e : ℕ}

theorem continuousAt_lift (R : AnRes P J e) (x y : R.X) (hy : y ∈ R.U x) : ContinuousAt (R.lift x) y := by
  obtain ⟨j, hj⟩ := R.A.cover y
  rw [continuousAt_pi]
  intro p
  have hya : R.A.chart j y ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x :=
    ⟨(R.A.chart j).map_source hj, by simpa [(R.A.chart j).left_inv hj] using hy⟩
  have h1 : ContinuousAt ((fun y' => R.lift x y' p) ∘ (R.A.chart j).symm) (R.A.chart j y) :=
    (R.holo x p j _ hya).continuousAt
  have h2 := h1.comp ((R.A.chart j).continuousAt hj)
  refine h2.congr ?_
  filter_upwards [(R.A.chart j).open_source.mem_nhds hj] with y' hy'
  simp [(R.A.chart j).left_inv hy']

theorem isAnalyticSubset (R : AnRes P J e) {G : MRing ι} {dG : K → ℕ} (hG : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog G dG) :
    R.A.IsAnalyticSubset {x | eval (R.lift x x) (map (Int.castRingHom ℂ) G) = 0} := by
  intro x
  refine ⟨R.U x, R.isOpen_U x, R.mem_U x, 1, fun _ y => eval (R.lift x y) (map (Int.castRingHom ℂ) G),
    fun _ j y hy => ?_, ?_⟩
  · exact analyticAt_eval_comp (F := fun y' => R.lift x ((R.A.chart j).symm y')) (fun p => R.holo x p j y hy) G
  · ext y
    simp only [mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨h0, hy⟩
      exact ⟨hy, fun _ => (eval_eq_zero_iff_of_sameOrbit hG (R.compat x y y ⟨hy, R.mem_U y⟩)).2 h0⟩
    · rintro ⟨hy, h0⟩
      exact ⟨(eval_eq_zero_iff_of_sameOrbit hG (R.compat x y y ⟨hy, R.mem_U y⟩)).1 (h0 0), hy⟩

theorem interior_eq_empty (hND : NonvanishingDense.Statement) (R : AnRes P J e) (hP : IsArithVar P (e + 1))
    {G : MRing ι} {dG : K → ℕ} (hG : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog G dG) (hGP : G ∉ P) :
    interior {x | eval (R.lift x x) (map (Int.castRingHom ℂ) G) = 0} = ∅ := by
  set S := {x | eval (R.lift x x) (map (Int.castRingHom ℂ) G) = 0} with hS
  by_contra hne
  obtain ⟨x0, hx0⟩ := nonempty_iff_ne_empty.2 hne

  obtain ⟨x, hxW, hxJ⟩ : ∃ x ∈ interior S, R.lift x x ∉ mcPts J := by
    by_contra! hall
    obtain ⟨j, hj⟩ := R.A.cover x0
    have hopen : IsOpen (R.A.chart j '' (interior S ∩ (R.A.chart j).source)) :=
      ((R.A.chart j).isOpen_image_iff_of_subset_source inter_subset_right).2
        (isOpen_interior.inter (R.A.chart j).open_source)
    have hpos : 0 < volume (R.A.chart j '' (interior S ∩ (R.A.chart j).source)) :=
      hopen.measure_pos volume ⟨R.A.chart j x0, x0, ⟨hx0, hj⟩, rfl⟩
    have hsub : R.A.chart j '' (interior S ∩ (R.A.chart j).source) ⊆
        (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' {x | R.lift x x ∈ mcPts J} := by
      rintro _ ⟨y, ⟨hyW, hys⟩, rfl⟩
      exact ⟨(R.A.chart j).map_source hys, by simpa [(R.A.chart j).left_inv hys] using hall y hyW⟩
    exact hpos.ne' (measure_mono_null hsub (R.null j))
  set z := R.lift x x with hzdef
  have hzP : z ∈ mcPts P := R.mem x x (R.mem_U x)

  set C := {z' : (Σ k, ι k) → ℂ | ∀ f ∈ J, eval z' (map (Int.castRingHom ℂ) f) = 0} with hC
  have hCc : IsClosed C := by
    simp only [hC, ofPred_forall]
    exact isClosed_iInter fun f => isClosed_iInter fun _ => isClosed_eq (MvPolynomial.continuous_eval _)
      continuous_const
  have hzC : z ∉ C := fun h => hxJ ⟨hzP.1, h⟩
  set T := {z' | z' ∈ mcPts P ∧ eval z' (map (Int.castRingHom ℂ) G) ≠ 0} ∩ Cᶜ with hT
  have hzT : z ∈ closure T := by
    rw [mem_closure_iff_nhds]
    intro t ht
    obtain ⟨w, ⟨hwt, hwC⟩, hw⟩ :=
      mem_closure_iff_nhds.1 (hND K ι P (e + 1) G hP hGP hzP) (t ∩ Cᶜ)
        (inter_mem ht (hCc.isOpen_compl.mem_nhds hzC))
    exact ⟨w, hwt, hw, hwC⟩

  have hex : ∀ z', ∃ x', z' ∈ T → SameOrbit (R.lift x' x') z' := fun z' => by
    by_cases h : z' ∈ T
    · obtain ⟨x', hx'⟩ := R.surj z' h.1.1 (fun hJ => h.2 hJ.2)
      exact ⟨x', fun _ => hx'⟩
    · exact ⟨x, fun h' => absurd h' h⟩
  choose xc hxc using hex
  have hxcW : ∀ z' ∈ T, xc z' ∉ interior S := fun z' hz' hW =>
    hz'.1.2 ((eval_eq_zero_iff_of_sameOrbit hG (hxc z' hz')).1 (show xc z' ∈ S from interior_subset hW))
  have : NeBot (𝓝[T] z) := mem_closure_iff_nhdsWithin_neBot.1 hzT
  obtain ⟨x', hx'⟩ := exists_clusterPt_of_compactSpace (map xc (𝓝[T] z))

  have hprop : (R.lift x' x', z) ∈ {q : ((Σ k, ι k) → ℂ) × ((Σ k, ι k) → ℂ) |
      ∀ k (i i' : ι k), q.1 ⟨k, i⟩ * q.2 ⟨k, i'⟩ = q.1 ⟨k, i'⟩ * q.2 ⟨k, i⟩} := by
    refine isClosed_blockProportional.closure_subset (mem_closure_iff_nhds.2 fun t ht => ?_)
    obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.1 ht
    have hU : R.U x' ∩ R.lift x' ⁻¹' u ∈ 𝓝 x' :=
      inter_mem ((R.isOpen_U x').mem_nhds (R.mem_U x')) (continuousAt_lift R x' x' (R.mem_U x') hu)
    have hV : xc '' (v ∩ T) ∈ map xc (𝓝[T] z) :=
      mem_map.2 (mem_of_superset (inter_mem_nhdsWithin T hv) fun z' hz' => ⟨z', ⟨hz'.2, hz'.1⟩, rfl⟩)
    obtain ⟨_, ⟨hyU, hyu⟩, z', ⟨hz'v, hz'T⟩, rfl⟩ := clusterPt_iff_nonempty.1 hx' hU hV
    refine ⟨(R.lift x' (xc z'), z'), huv ⟨hyu, hz'v⟩, ?_⟩
    exact blockProportional_of_sameOrbit
      (sameOrbit_trans_nf (R.compat x' (xc z') (xc z') ⟨hyU, R.mem_U _⟩) (hxc z' hz'T))
  have horb : SameOrbit (R.lift x' x') z :=
    sameOrbit_of_blockProportional (R.mem x' x' (R.mem_U x')).1 hzP.1 hprop
  have hxx' : x = x' := R.inj x x' hxJ (sameOrbit_symm_nf horb)
  subst hxx'
  obtain ⟨_, hyW, z', hz'T, rfl⟩ :=
    clusterPt_iff_nonempty.1 hx' (isOpen_interior.mem_nhds hxW)
      (mem_map.2 (mem_of_superset self_mem_nhdsWithin fun z' hz' => ⟨z', hz', rfl⟩) :
        xc '' T ∈ map xc (𝓝[T] z))
  exact hxcW z' hz'T hyW

end AnResNullForm

theorem AnResNullForm.proof (hND : NonvanishingDense.Statement) : AnResNullForm.Statement := by
  intro e K _ ι _ P J R G dG hP hG hGP j
  have h := analyticNull R.A _ (AnResNullForm.isAnalyticSubset R hG)
    (AnResNullForm.interior_eq_empty hND R hP hG hGP) j
  refine measure_mono_null ?_ h
  rintro a ⟨ha, haS⟩
  exact ⟨(R.A.chart j).symm a, ⟨haS, (R.A.chart j).map_target ha⟩, (R.A.chart j).right_inv ha⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockImageGenDeg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace BlockImageGenDeg

open GroundTheory.Heights₂.Heights.NumbersDVR (hilbFn mixedDiff diffStep eventualValue intNum)
open fwdDiff

theorem mixedDiff_line {K : Type*} (b m₀ : K → ℤ) (h : (K → ℤ) → ℤ) (D : ℕ) (t : ℤ) :
    mixedDiff (fun _ : Fin D => b) h (m₀ + t • b) = ((fwdDiff 1)^[D] fun s : ℤ => h (m₀ + s • b)) (t - D) := by
  induction D generalizing t with
  | zero => simp [mixedDiff]
  | succ D ih =>
    have hs : mixedDiff (fun _ : Fin (D + 1) => b) h = diffStep b (mixedDiff (fun _ : Fin D => b) h) := by
      simp [mixedDiff, List.ofFn_succ]
    have h1 : m₀ + t • b - b = m₀ + (t - 1) • b := by rw [sub_smul, one_smul, add_sub_assoc]
    have e1 : t - ((D + 1 : ℕ) : ℤ) + 1 = t - D := by push_cast; ring
    have e2 : t - ((D + 1 : ℕ) : ℤ) = t - 1 - D := by push_cast; ring
    rw [hs, diffStep, h1, ih, ih, Function.iterate_succ_apply', fwdDiff, e1, e2]

theorem fwdDiff_iter_eq_poly (φ : ℤ → ℤ) (q : Polynomial ℚ) (D : ℕ) (s : ℤ)
    (h : ∀ j ≤ D, (φ (s + j) : ℚ) = q.eval ((s : ℚ) + j)) :
    (((fwdDiff 1)^[D] φ) s : ℚ) = ((fwdDiff 1)^[D] q.eval) (s : ℚ) := by
  rw [fwdDiff_iter_eq_sum_shift, fwdDiff_iter_eq_sum_shift]
  push_cast
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ D := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  simp only [zsmul_eq_mul, nsmul_eq_mul, mul_one, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
    Int.cast_natCast]
  rw [h j hj']

theorem fwdDiff_iter_poly (q : Polynomial ℚ) {D : ℕ} (hq : q.natDegree ≤ D) (x : ℚ) :
    ((fwdDiff 1)^[D] q.eval) x = q.coeff D * D.factorial := by
  rcases hq.lt_or_eq with h | h
  · rw [Polynomial.fwdDiff_iter_eq_zero_of_degree_lt h, Polynomial.coeff_eq_zero_of_natDegree_lt h]
    simp
  · subst h
    rw [q.fwdDiff_iter_degree_eq_factorial]
    rw [Pi.smul_apply, Pi.natCast_apply, smul_eq_mul]
    rfl

def lineRestr {K : Type*} [DecidableEq K] (p : MvPolynomial K ℚ) (k₀ : K) (m : K → ℚ) : Polynomial ℚ :=
  MvPolynomial.aeval (fun k => if k = k₀ then Polynomial.X else Polynomial.C (m k)) p

theorem eval_lineRestr {K : Type*} [DecidableEq K] (p : MvPolynomial K ℚ) (k₀ : K) (m : K → ℚ) (t : ℚ) :
    (lineRestr p k₀ m).eval t = MvPolynomial.eval (fun k => if k = k₀ then t else m k) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [lineRestr]
  | add p q hp hq => simp only [lineRestr, map_add (f := _), Polynomial.eval_add] at *; rw [hp, hq]
  | mul_X p k hp =>
    simp only [lineRestr, map_mul, Polynomial.eval_mul] at *
    rw [hp]
    by_cases hk : k = k₀ <;> simp [hk]

theorem natDegree_lineRestr_le {K : Type*} [DecidableEq K] (p : MvPolynomial K ℚ) (k₀ : K) (m : K → ℚ) :
    (lineRestr p k₀ m).natDegree ≤ p.totalDegree := by
  rw [lineRestr]
  conv_lhs => rw [p.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun s hs => ?_
  rw [MvPolynomial.aeval_monomial, Polynomial.algebraMap_eq]
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  refine le_trans ?_ (MvPolynomial.le_totalDegree hs)
  refine Finset.sum_le_sum fun k _ => (Polynomial.natDegree_pow_le).trans ?_
  have : (if k = k₀ then (Polynomial.X : Polynomial ℚ) else Polynomial.C (m k)).natDegree ≤ 1 := by
    split_ifs <;> simp
  simpa using Nat.mul_le_mul_left (s k) this

theorem eventualValue_eq {K : Type*} (f : (K → ℤ) → ℤ) (e : ℚ) (h : ∀ᶠ m in Filter.atTop, (f m : ℚ) = e) :
    (eventualValue f : ℚ) = e := by
  have hex : ∃ c, ∀ᶠ m in Filter.atTop, f m = c := by
    obtain ⟨m, hm⟩ := h.exists
    exact ⟨f m, h.mono fun m' hm' => by exact_mod_cast hm'.trans hm.symm⟩
  unfold eventualValue
  rw [dite_eq_left hex]
  obtain ⟨m, hm1, hm2⟩ := (hex.choose_spec.and h).exists
  rw [← hm1]
  exact hm2

end BlockImageGenDeg


open GroundTheory.Heights₂.Heights.NumbersDVR (hilbFn mixedDiff eventualValue) in
open BlockImageGenDeg in
theorem BlockImageGenDeg.proof (hMHP : MultigradedHilbertPolynomial.Statement.{0})
    (hGFV : GenericFibreVar.Statement) (hHEP : GroundTheory.Heights₂.Heights.FieldNumbers.HilbEventuallyPoly.Statement.{0})
    (hHom : GenFibreHomog.Statement) (hImg : BlockImageHilb.Statement) (hBir : BlockBirationalHilbert.Statement)
    (hSand : PolySandwich.Statement) : BlockImageGenDeg.Statement := by
  intro D K _ _ ι _ Ω _ _ κ _ y k₀ M N x hA hB hI
  set PY := (mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ)) with hPY
  set PX := (coordIdeal ℤ x).map (MvPolynomial.map (Int.castRingHom ℚ)) with hPX

  obtain ⟨⟨hprime, -, hrel⟩, hdim⟩ := hGFV K ι Ω y D hA
  obtain ⟨pY, a₀, hdeg, hpY⟩ := hMHP ℚ K ι PY D ⟨hprime, hHom K ι Ω y, hrel⟩ hdim

  have hXhom : GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomogIdeal (ι := GlobalTheory κ) PX := by
    rw [hPX, coordIdeal_eq_mCoordIdeal]; exact hHom Unit (GlobalTheory κ) Ω x
  obtain ⟨pX, hpX⟩ := hHEP ℚ Unit (GlobalTheory κ) PX hXhom
  obtain ⟨aX, haX⟩ := Filter.eventually_atTop.mp hpX
  set p₁ := lineRestr pX () 0 with hp₁
  have hX1 : ∀ n : ℕ, (aX ()).toNat ≤ n → (hilbFn PX (fun _ => (n : ℤ)) : ℚ) = p₁.eval (n : ℚ) := by
    intro n hn
    rw [haX (fun _ => (n : ℤ)) (fun u => by cases u; show aX () ≤ (n : ℤ); omega), hp₁, eval_lineRestr]
    simp

  have hnz : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := by
    intro k
    obtain ⟨i, hi⟩ := hA.2.1.2.2 k
    refine ⟨i, fun h0 => hi ?_⟩
    show mConeMap y (X ⟨k, i⟩) = 0
    simp [mConeMap, h0]

  have hY1 : ∀ (m : K → ℕ) (s : ℕ), (∀ k, k ≠ k₀ → a₀ ≤ m k) → a₀ ≤ s →
      (hilbFn PY (fun k => if k = k₀ then (s : ℤ) else m k) : ℚ) =
        (lineRestr pY k₀ fun k => (m k : ℚ)).eval (s : ℚ) := by
    intro m s hm hs
    have := hpY (fun k => if k = k₀ then s else m k) fun k => by
      by_cases hk : k = k₀ <;> simp [hk, hs, hm k]
    rw [eval_lineRestr]
    convert this using 3 <;> (funext k; by_cases hk : k = k₀ <;> simp [hk])

  have hsand : ∀ m : K → ℕ, (∀ k, k ≠ k₀ → a₀ ≤ m k) →
      p₁.natDegree ≤ D ∧ p₁.coeff D = (lineRestr pY k₀ fun k => (m k : ℚ)).coeff D := by
    intro m hm
    obtain ⟨c, hc⟩ := hBir K ι Ω y k₀ hnz hB m
    refine hSand D c _ _ ((natDegree_lineRestr_le _ _ _).trans hdeg) ?_
    filter_upwards [Filter.eventually_ge_atTop (max a₀ (aX ()).toNat)] with n hn
    have h1 := hX1 n (le_of_max_le_right hn)
    have h2 := hX1 (n + c) ((le_of_max_le_right hn).trans (Nat.le_add_right _ _))
    rw [hImg K ι Ω κ y k₀ M N x hI] at h1 h2
    rw [← hY1 m n hm (le_of_max_le_left hn)]
    push_cast at h2
    rw [← h1, ← h2]
    exact ⟨by exact_mod_cast (hc n).1, by exact_mod_cast (hc n).2⟩
  have hdegX : p₁.natDegree ≤ D := (hsand (fun _ => a₀) fun _ _ => le_rfl).1

  have key : (eventualValue (mixedDiff (fun _ : Fin D => (1 : Unit → ℤ)) (hilbFn PX)) : ℚ) =
      eventualValue (mixedDiff (fun _ : Fin D => ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg k₀) (hilbFn PY)) := by
    rw [eventualValue_eq (e := p₁.coeff D * D.factorial), eventualValue_eq (e := p₁.coeff D * D.factorial)]
    · rw [Filter.eventually_atTop]
      refine ⟨fun _ => ((a₀ : ℤ) + D), fun m hm => ?_⟩
      have hm' : ∀ k, (a₀ : ℤ) + D ≤ m k := hm
      have hline : m = (fun k => if k = k₀ then 0 else m k) + m k₀ • ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg k₀ := by
        funext k; by_cases hk : k = k₀ <;> simp [hk, ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg]
      rw [hline, mixedDiff_line, fwdDiff_iter_eq_poly _ (lineRestr pY k₀ fun k => ((m k).toNat : ℚ)) D,
        fwdDiff_iter_poly _ ((natDegree_lineRestr_le _ _ _).trans hdeg),
        (hsand (fun k => (m k).toNat) fun k _ => by have := hm' k; omega).2]
      intro j hj
      have hs : 0 ≤ m k₀ - D + j := by have := hm' k₀; omega
      have hkey : (fun k => if k = k₀ then 0 else m k) + (m k₀ - D + j) • ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg k₀ =
          fun k => if k = k₀ then (((m k₀ - D + j).toNat : ℕ) : ℤ) else (((m k).toNat : ℕ) : ℤ) := by
        funext k
        by_cases hk : k = k₀
        · simp [hk, ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg, Int.toNat_of_nonneg hs]
        · have := hm' k
          simp [hk, ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg]
          omega
      rw [hkey, hY1 (fun k => (m k).toNat) _ (fun k _ => by have := hm' k; omega) (by have := hm' k₀; omega)]
      congr 1
      rw [show (((m k₀ - D + j).toNat : ℕ) : ℚ) = ((m k₀ - D + j : ℤ) : ℚ) by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg hs]]
      push_cast; ring
    · rw [Filter.eventually_atTop]
      refine ⟨fun _ => ((aX ()).toNat + D : ℤ), fun m hm => ?_⟩
      have hm' : ((aX ()).toNat + D : ℤ) ≤ m () := hm ()
      have hline : m = 0 + m () • (1 : Unit → ℤ) := by funext u; cases u; simp
      rw [hline, mixedDiff_line, fwdDiff_iter_eq_poly _ p₁ D, fwdDiff_iter_poly _ hdegX]
      intro j hj
      have hs : 0 ≤ m () - D + j := by omega
      have hkey : (0 : Unit → ℤ) + (m () - D + j) • (1 : Unit → ℤ) = fun _ => (((m () - D + j).toNat : ℕ) : ℤ) := by
        funext u; simp [Int.toNat_of_nonneg hs]
      rw [hkey, hX1 _ (by omega)]
      congr 1
      rw [show (((m () - D + j).toNat : ℕ) : ℚ) = ((m () - D + j : ℤ) : ℚ) by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg hs]]
      push_cast; ring

  apply Int.cast_injective (α := ℚ)
  unfold genDeg GroundTheory.Heights₂.Heights.NumbersDVR.intNum
  convert key using 6 <;> first | rfl | (funext k'; simp [unitDeg, ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg, Pi.single_apply])

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
