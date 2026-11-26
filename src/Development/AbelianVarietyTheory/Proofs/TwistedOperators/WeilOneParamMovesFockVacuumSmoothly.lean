module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVacuaSmoothFamilyComplexGaussians

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContDiffContinuousOneParameterFiniteDimensionalL
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContDiffContinuousOneParameterFiniteDimensionalL
open MeasureTheory

namespace GlobalTheory

theorem contDiff_toCLM_of_continuous_oneParameter {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] (A : ℝ → W →ₗ[ℝ] W)
    (hc : ∀ w, Continuous fun t => A t w) (hadd : ∀ s t, A (s + t) = (A s).comp (A t)) (h0 : A 0 = LinearMap.id) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => LinearMap.toContinuousLinearMap (A t)) := by
  have hT : Continuous fun t => LinearMap.toContinuousLinearMap (A t) :=
    continuous_clm_apply.2 fun w => by simpa using hc w
  refine contDiff_of_continuous_oneParameter (W →L[ℝ] W) _ hT ?_ ?_
  · ext w; simp [h0]
  · intro s t; ext w; simp [hadd]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContDiffContinuousOneParameterFiniteDimensionalLStatement
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiff_continuous_oneParameter_finiteDimensional_linear : ∀ {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (A : ℝ → W →ₗ[ℝ] W),
    (∀ w, Continuous fun t => A t w) → (∀ s t, A (s + t) = (A s).comp (A t)) → A 0 = LinearMap.id →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => LinearMap.toContinuousLinearMap (A t)) := by
  first | exact @GlobalTheory.contDiff_toCLM_of_continuous_oneParameter | exact GlobalTheory.contDiff_toCLM_of_continuous_oneParameter | (intros; apply GlobalTheory.contDiff_toCLM_of_continuous_oneParameter <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContDiffOfContinuousQuasiMultiplicativeSmoothDef
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContDiffOfContinuousQuasiMultiplicativeSmoothDef
open MeasureTheory

open Metric Set Filter Topology Convolution

namespace GlobalTheory.FuncEqSmooth

theorem contDiff_of_func_eq (c : ℝ → ℂ) (E : ℝ → ℝ → ℂ) (U : Set (ℝ × ℝ)) (hc : Continuous c)
    (hc0 : c 0 ≠ 0) (hU : IsOpen U) (hUs : ∀ s, (s, 0) ∈ U)
    (hE : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => E p.1 p.2) U)
    (hfe : ∀ p ∈ U, c (p.1 + p.2) = c p.1 * c p.2 * E p.1 p.2) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c := by
  have h00 : ((0:ℝ), (0:ℝ)) ∈ U := hUs 0
  have hw0 : c 0 * E 0 0 = 1 := by
    have h1 := hfe (0,0) h00
    simp only [add_zero] at h1
    have h2 : c 0 * (c 0 * E 0 0) = c 0 * 1 := by rw [mul_one, ← mul_assoc]; exact h1.symm
    exact mul_left_cancel₀ hc0 h2
  have hEcont : ContinuousAt (fun p : ℝ × ℝ => E p.1 p.2) (0,0) :=
    hE.continuousOn.continuousAt (hU.mem_nhds h00)
  have hwcont : ContinuousAt (fun v : ℝ => c v * E 0 v) 0 := by
    have h1 : ContinuousAt (fun v : ℝ => E (0:ℝ) v) 0 :=
      hEcont.comp (f := fun v : ℝ => ((0:ℝ), v)) (by fun_prop)
    exact hc.continuousAt.mul h1
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU _ h00
  obtain ⟨δ, hδ, hwδ⟩ := Metric.continuousAt_iff.1 hwcont (1/2) (by norm_num)
  set r := min ε δ with hr
  have hr0 : 0 < r := lt_min hε hδ
  have hbox : ∀ a b : ℝ, |a| < r → |b| < r → (a, b) ∈ U := by
    intro a b ha hb
    apply hball
    rw [mem_ball, Prod.dist_eq, max_lt_iff]
    simp only [Real.dist_eq, sub_zero]
    exact ⟨lt_of_lt_of_le ha (min_le_left _ _), lt_of_lt_of_le hb (min_le_left _ _)⟩

  let ψ : ContDiffBump (0:ℝ) := ⟨r/4, r/2, by positivity, by linarith⟩
  set φ : ℝ → ℝ := ψ.normed volume with hφdef
  have hφ0 : ∀ x : ℝ, r/2 ≤ |x| → φ x = 0 := by
    intro x hx
    rw [← Function.notMem_support, hφdef, ψ.support_normed_eq, mem_ball, Real.dist_eq, sub_zero]
    show ¬ |x| < r/2
    linarith
  have hφs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ := ψ.contDiff_normed
  let φr : ℝ → ℂ := fun y => ((φ y : ℝ) : ℂ)
  have hφr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φr := Complex.ofRealCLM.contDiff.comp hφs
  have hφr0 : ∀ x : ℝ, r/2 ≤ |x| → φr x = 0 := by
    intro x hx; simp [φr, hφ0 x hx]

  let A : ℝ → ℂ := c ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] (fun y => φr (-y))
  have hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A := by
    have hcs : HasCompactSupport (fun y => φr (-y)) := by
      refine HasCompactSupport.intro (isCompact_closedBall (0:ℝ) (r/2)) (fun y hy => ?_)
      rw [mem_closedBall, Real.dist_eq, sub_zero, not_le] at hy
      exact hφr0 _ (by rw [abs_neg]; exact hy.le)
    exact hcs.contDiff_convolution_right (L := ContinuousLinearMap.mul ℝ ℂ) hc.locallyIntegrable
      (hφr.comp contDiff_neg)

  let G : ℝ → ℝ → ℂ := fun t y => φr (-y) * E t (-y)
  let h : ℝ → ℂ := fun t => (c ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] G t) 0
  have hG : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry G) (ball (0:ℝ) r ×ˢ univ) := by
    intro q hq
    apply ContDiffAt.contDiffWithinAt
    have hq1 : |q.1| < r := by
      have := hq.1; rw [mem_ball, Real.dist_eq, sub_zero] at this; exact this
    by_cases hq2 : |q.2| < r
    · have hmem : (q.1, -q.2) ∈ U := hbox _ _ hq1 (by rw [abs_neg]; exact hq2)
      have hEat : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => E p.1 p.2) (q.1, -q.2) :=
        hE.contDiffAt (hU.mem_nhds hmem)
      have h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × ℝ => E q.1 (-q.2)) q :=
        hEat.comp (f := fun q : ℝ × ℝ => (q.1, -q.2)) q (by fun_prop)
      have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × ℝ => φr (-q.2)) q :=
        (hφr.comp (contDiff_snd.neg)).contDiffAt
      exact h1.mul h2
    · push_neg at hq2
      have hev : ∀ᶠ q' in 𝓝 q, r/2 < |q'.2| :=
        continuousAt_const.eventually_lt (by fun_prop) (by linarith)
      refine contDiffAt_const (c := (0:ℂ)).congr_of_eventuallyEq ?_
      filter_upwards [hev] with q' hq'
      show φr (-q'.2) * E q'.1 (-q'.2) = 0
      rw [hφr0 _ (by rw [abs_neg]; exact hq'.le), zero_mul]
  have hparam := contDiffOn_convolution_right_with_param (μ := volume) (n := ⊤)
    (ContinuousLinearMap.mul ℝ ℂ) (f := c) (g := G) (s := ball (0:ℝ) r) (k := closedBall (0:ℝ) (r/2))
    isOpen_ball (isCompact_closedBall _ _)
    (fun p x _ hx => by
      rw [mem_closedBall, Real.dist_eq, sub_zero, not_le] at hx
      show φr (-x) * E p (-x) = 0
      rw [hφr0 _ (by rw [abs_neg]; exact hx.le), zero_mul])
    hc.locallyIntegrable hG
  have hh : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h (ball (0:ℝ) r) := by
    have hemb : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => (t, (0:ℝ))) (ball (0:ℝ) r) :=
      (contDiff_id.prodMk contDiff_const).contDiffOn
    have h3 := ContDiffOn.comp (g := fun q : ℝ × ℝ => (c ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] G q.1) q.2)
      hparam hemb (fun t ht => ⟨ht, mem_univ _⟩)
    exact h3
  have hrδ : r ≤ δ := min_le_right _ _

  let cl : ℝ → ℝ := fun v => max (-(r/2)) (min v (r/2))
  have hclc : Continuous cl := continuous_const.max (continuous_id.min continuous_const)
  have hcl : ∀ v, cl v ∈ Icc (-(r/2)) (r/2) := fun v =>
    ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩
  have hclid : ∀ v, |v| ≤ r/2 → cl v = v := by
    intro v hv
    obtain ⟨h1, h2⟩ := abs_le.1 hv
    show max (-(r/2)) (min v (r/2)) = v
    rw [min_eq_left h2, max_eq_right h1]
  have hE0on : ContinuousOn (fun v : ℝ => E 0 v) (Icc (-(r/2)) (r/2)) := by
    have h3 := hE.continuousOn.comp (f := fun v : ℝ => ((0:ℝ), v))
      (by fun_prop : Continuous fun v : ℝ => ((0:ℝ), v)).continuousOn
      (fun v (hv : v ∈ Icc (-(r/2)) (r/2)) => hbox 0 v (by simp [hr0]) (abs_lt.2 ⟨by linarith [hv.1], by linarith [hv.2]⟩))
    exact h3
  let Ehat : ℝ → ℂ := fun v => E 0 (cl v)
  have hEhat : Continuous Ehat := hE0on.comp_continuous hclc hcl
  let g : ℝ → ℂ := fun x => c (-x) * Ehat (-x)
  have hgc : Continuous g := (hc.comp continuous_neg).mul (hEhat.comp continuous_neg)
  have hg0 : g 0 = 1 := by
    show c (-0) * E 0 (cl (-0)) = 1
    rw [neg_zero, hclid 0 (by simp; positivity), hw0]
  have hdist := ψ.dist_normed_convolution_le (μ := volume) (x₀ := 0) (ε := 1/2) hgc.aestronglyMeasurable
    (fun x hx => by
      have hx' : |x| < r/2 := by
        have h6 := hx; rw [mem_ball, Real.dist_eq, sub_zero] at h6; exact h6
      have e1 : g x = c (-x) * E 0 (-x) := by
        show c (-x) * E 0 (cl (-x)) = _
        rw [hclid _ (by rw [abs_neg]; exact hx'.le)]
      rw [e1, hg0, ← hw0]
      exact (hwδ (by rw [Real.dist_eq, sub_zero, abs_neg]; linarith)).le)
  have hconv : (ψ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) 0 = h 0 := by
    show _ = (c ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] G 0) 0
    rw [convolution_def, convolution_def]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [ContinuousLinearMap.lsmul_apply, ContinuousLinearMap.mul_apply', zero_sub, neg_neg, g, G, Ehat, φr]
    by_cases hu : |u| < r/2
    · rw [hclid u hu.le, Complex.real_smul]; ring
    · have hz : ψ.normed volume u = 0 := hφ0 u (not_lt.1 hu)
      have hz' : φ u = 0 := hφ0 u (not_lt.1 hu)
      rw [hz, hz']; simp
  have h0ne : h 0 ≠ 0 := by
    intro h0
    rw [hconv, hg0, h0] at hdist
    norm_num at hdist

  have hAh : ∀ t, |t| < r → A t = c t * h t := by
    intro t ht
    show (c ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] (fun y => φr (-y))) t
      = c t * (c ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] G t) 0
    rw [convolution_def, convolution_def, ← integral_const_mul,
      ← integral_add_right_eq_self (μ := volume)
        (fun u => (ContinuousLinearMap.mul ℝ ℂ) (c u) (φr (-(t - u)))) t]
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    simp only [ContinuousLinearMap.mul_apply', G, zero_sub, neg_neg]
    have e : -(t - (s + t)) = s := by ring
    rw [e]
    by_cases hs : |s| < r/2
    · have h7 := hfe (t, s) (hbox t s ht (by linarith))
      simp only at h7
      rw [add_comm s t, h7]; ring
    · rw [hφr0 s (not_lt.1 hs)]; ring

  have hcont_h : ContinuousOn h (ball (0:ℝ) r) := hh.continuousOn
  set V := ball (0:ℝ) r ∩ h ⁻¹' {0}ᶜ with hV
  have hVo : IsOpen V := hcont_h.isOpen_inter_preimage isOpen_ball isOpen_compl_singleton
  have h0V : (0:ℝ) ∈ V := ⟨mem_ball_self hr0, h0ne⟩
  have hcV : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c V := by
    have h4 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => A t * (h t)⁻¹) V :=
      hA.contDiffOn.mul ((hh.mono inter_subset_left).inv (fun t ht => ht.2))
    refine h4.congr (fun t ht => ?_)
    have ht1 : |t| < r := by
      have h8 := ht.1; rw [mem_ball, Real.dist_eq, sub_zero] at h8; exact h8
    have hne : h t ≠ 0 := ht.2
    show c t = A t * (h t)⁻¹
    rw [hAh t ht1, mul_inv_cancel_right₀ hne]

  rw [contDiff_iff_contDiffAt]
  intro t₀
  set W := (fun t : ℝ => (t₀, t)) ⁻¹' U ∩ V with hW
  have hWo : IsOpen W := (hU.preimage (by fun_prop)).inter hVo
  have h0W : (0:ℝ) ∈ W := ⟨hUs t₀, h0V⟩
  have hFW : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => c (t₀ + t)) W := by
    have hE' : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => E t₀ t) W :=
      hE.comp (f := fun t : ℝ => (t₀, t)) (contDiff_const.prodMk contDiff_id).contDiffOn (fun t ht => ht.1)
    have h5 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => c t₀ * c t * E t₀ t) W :=
      (contDiffOn_const.mul (hcV.mono inter_subset_right)).mul hE'
    refine h5.congr (fun t ht => ?_)
    exact hfe (t₀, t) ht.1
  have hF0 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => c (t₀ + t)) 0 := hFW.contDiffAt (hWo.mem_nhds h0W)
  have hsub : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => x - t₀) t₀ := (contDiff_id.sub contDiff_const).contDiffAt
  have hF0' : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => c (t₀ + t)) ((fun x : ℝ => x - t₀) t₀) := by
    simpa using hF0
  have h9 := ContDiffAt.comp (f := fun x : ℝ => x - t₀) t₀ hF0' hsub
  simpa [Function.comp_def, add_sub_cancel_left] using h9

end GlobalTheory.FuncEqSmooth
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContDiffOfContinuousQuasiMultiplicativeSmoothDefStatement
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiff_of_continuous_quasiMultiplicative_smoothDefect : ∀ (c : ℝ → ℂ) (E : ℝ → ℝ → ℂ) (U : Set (ℝ × ℝ)), Continuous c → c 0 ≠ 0 → IsOpen U → (∀ s, (s, 0) ∈ U) →
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => E p.1 p.2) U → (∀ p ∈ U, c (p.1 + p.2) = c p.1 * c p.2 * E p.1 p.2) →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c := by
  first | exact @GlobalTheory.FuncEqSmooth.contDiff_of_func_eq | exact GlobalTheory.FuncEqSmooth.contDiff_of_func_eq | (intros; apply GlobalTheory.FuncEqSmooth.contDiff_of_func_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzIsometryInnerProductEq
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzIsometryInnerProductEq
open MeasureTheory

namespace GlobalTheory

theorem complex_mul_conj_eq_polarization (a b : ℂ) :
    a * starRingEnd ℂ b = (1 / 4 : ℂ) * ∑ k ∈ Finset.range 4,
      Complex.I ^ k * ((‖a + Complex.I ^ k * b‖ ^ 2 : ℝ) : ℂ) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Complex.sq_norm]
  apply Complex.ext <;>
    simp [Complex.normSq_apply, pow_succ, Complex.mul_re, Complex.mul_im] <;> ring

theorem schwartz_integrable_sq_norm_of_addHaar {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V)
    [μ.IsAddHaarMeasure] (h : SchwartzMap V ℂ) :
    Integrable (fun x => ‖h x‖ ^ 2) μ := by
  have := (h.memLp 2 μ).integrable_norm_pow (by norm_num)
  simpa using this

theorem schwartz_integral_mul_conj_eq_polarization {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V)
    [μ.IsAddHaarMeasure] (u v : SchwartzMap V ℂ) :
    ∫ x, u x * starRingEnd ℂ (v x) ∂μ = (1 / 4 : ℂ) * ∑ k ∈ Finset.range 4,
      Complex.I ^ k * ((∫ x, ‖(u + (Complex.I ^ k) • v) x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
  simp_rw [complex_mul_conj_eq_polarization (u _)]
  rw [integral_const_mul, integral_finsetSum]
  · congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_const_mul]
    congr 1
    rw [← integral_complex_ofReal]
    simp [smul_eq_mul]
  · intro k _
    refine Integrable.const_mul ?_ _
    have := (schwartz_integrable_sq_norm_of_addHaar μ (u + (Complex.I ^ k) • v)).ofReal (𝕜 := ℂ)
    simpa using this

theorem schwartz_L2_isometry_preserves_inner {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (T : SchwartzMap V ℂ →ₗ[ℂ] SchwartzMap V ℂ) :
    (∀ f, ∫ x, ‖T f x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ) →
    ∀ f g : SchwartzMap V ℂ, ∫ x, T f x * starRingEnd ℂ (T g x) ∂μ = ∫ x, f x * starRingEnd ℂ (g x) ∂μ := by
  intro hT f g
  rw [schwartz_integral_mul_conj_eq_polarization, schwartz_integral_mul_conj_eq_polarization]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← map_smul, ← map_add (f := _), hT]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzIsometryInnerProductEqStatement
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_isometry_inner_product_eq : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (T : SchwartzMap V ℂ →ₗ[ℂ] SchwartzMap V ℂ),
    (∀ f, ∫ x, ‖T f x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ) →
    ∀ f g : SchwartzMap V ℂ, ∫ x, T f x * starRingEnd ℂ (T g x) ∂μ = ∫ x, f x * starRingEnd ℂ (g x) ∂μ := by
  first | exact @GlobalTheory.schwartz_L2_isometry_preserves_inner | exact GlobalTheory.schwartz_L2_isometry_preserves_inner | (intros; apply GlobalTheory.schwartz_L2_isometry_preserves_inner <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GaussianPairingIntegralContDiffNeZeroDiag
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GaussianPairingIntegralContDiffNeZeroDiag
open MeasureTheory

noncomputable section

namespace GlobalTheory.GaussPairing

open Metric Filter Topology

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

def evalDiag (x : V) : (V →L[ℝ] V →L[ℝ] ℂ) →L[ℝ] ℂ :=
  (ContinuousLinearMap.apply ℝ ℂ x).comp (ContinuousLinearMap.apply ℝ (V →L[ℝ] ℂ) x)

@[simp] theorem evalDiag_apply (x : V) (B : V →L[ℝ] V →L[ℝ] ℂ) : evalDiag x B = B x x := rfl

theorem norm_evalDiag_le (x : V) : ‖evalDiag x‖ ≤ ‖x‖ * ‖x‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    (fun B => (B.le_opNorm₂ x x).trans_eq (by ring))

theorem continuous_evalDiag : Continuous (evalDiag (V := V)) :=
  continuous_clm_apply.2 fun B => by simpa using B.continuous.clm_apply continuous_id

def diagProd (ys : List (V →L[ℝ] V →L[ℝ] ℂ)) (x : V) : ℂ := (ys.map fun y => y x x).prod

theorem continuous_diagProd (ys : List (V →L[ℝ] V →L[ℝ] ℂ)) : Continuous (diagProd ys) :=
  continuous_list_prod ys fun y _ => y.continuous.clm_apply continuous_id

theorem prod_norm_nonneg (ys : List (V →L[ℝ] V →L[ℝ] ℂ)) : 0 ≤ (ys.map (‖·‖)).prod :=
  List.prod_nonneg (by simp)

theorem norm_diagProd_le (ys : List (V →L[ℝ] V →L[ℝ] ℂ)) (x : V) :
    ‖diagProd ys x‖ ≤ (ys.map (‖·‖)).prod * ‖x‖ ^ (2 * ys.length) := by
  induction ys with
  | nil => simp [diagProd]
  | cons y ys ih =>
    simp only [diagProd, List.map_cons, List.prod_cons, List.length_cons] at ih ⊢
    rw [norm_mul]
    have h0 := prod_norm_nonneg ys
    calc ‖y x x‖ * ‖(ys.map fun y => y x x).prod‖
        ≤ (‖y‖ * ‖x‖ * ‖x‖) * ((ys.map (‖·‖)).prod * ‖x‖ ^ (2 * ys.length)) :=
          mul_le_mul (y.le_opNorm₂ x x) ih (norm_nonneg _) (by positivity)
      _ = _ := by ring

def negDef : Set (V →L[ℝ] V →L[ℝ] ℂ) := {B | ∃ ε > 0, ∀ x, (B x x).re ≤ -(ε * ‖x‖ ^ 2)}

theorem re_le_of_norm_sub_le {B B' : V →L[ℝ] V →L[ℝ] ℂ} {ε : ℝ}
    (hB : ∀ x, (B x x).re ≤ -(ε * ‖x‖ ^ 2)) (hB' : ‖B' - B‖ ≤ ε / 2) (x : V) :
    (B' x x).re ≤ -(ε / 2 * ‖x‖ ^ 2) := by
  have h1 : (B' x x).re = (B x x).re + ((B' - B) x x).re := by simp
  have h2 : ((B' - B) x x).re ≤ ε / 2 * ‖x‖ ^ 2 := by
    calc ((B' - B) x x).re ≤ ‖(B' - B) x x‖ := Complex.re_le_norm _
      _ ≤ ‖B' - B‖ * ‖x‖ * ‖x‖ := (B' - B).le_opNorm₂ x x
      _ ≤ ε / 2 * ‖x‖ * ‖x‖ := by gcongr
      _ = ε / 2 * ‖x‖ ^ 2 := by ring
  rw [h1]; linarith [hB x]

theorem isOpen_negDef : IsOpen (negDef (V := V)) := by
  rw [Metric.isOpen_iff]
  rintro B ⟨ε, hε, hB⟩
  refine ⟨ε / 2, by positivity, fun B' hB' => ⟨ε / 2, by positivity, re_le_of_norm_sub_le hB ?_⟩⟩
  rw [mem_ball, dist_eq_norm] at hB'
  exact hB'.le

variable [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure]

theorem integrable_norm_pow_mul_exp (n : ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : V => ‖x‖ ^ n * Real.exp (-b * ‖x‖ ^ 2)) μ := by
  rcases subsingleton_or_nontrivial V with h | h
  · exact Integrable.of_finite
  rw [integrable_fun_norm_addHaar μ (f := fun r => r ^ n * Real.exp (-b * r ^ 2))]
  have := integrableOn_rpow_mul_exp_neg_mul_sq hb
    (s := ((Module.finrank ℝ V - 1 + n : ℕ) : ℝ)) (lt_of_lt_of_le neg_one_lt_zero (by positivity))
  refine this.congr_fun (fun x _ => ?_) measurableSet_Ioi
  simp only [Real.rpow_natCast, smul_eq_mul, pow_add, mul_assoc]

def gaussMoment (ys : List (V →L[ℝ] V →L[ℝ] ℂ)) (B : V →L[ℝ] V →L[ℝ] ℂ) : ℂ :=
  ∫ x, Complex.exp (B x x) * diagProd ys x ∂μ

omit [MeasurableSpace V] [BorelSpace V] in
theorem norm_integrand_le {B : V →L[ℝ] V →L[ℝ] ℂ} {ε : ℝ} (hB : ∀ x, (B x x).re ≤ -(ε * ‖x‖ ^ 2))
    (ys : List (V →L[ℝ] V →L[ℝ] ℂ)) (x : V) :
    ‖Complex.exp (B x x) * diagProd ys x‖ ≤
      (ys.map (‖·‖)).prod * (‖x‖ ^ (2 * ys.length) * Real.exp (-ε * ‖x‖ ^ 2)) := by
  rw [norm_mul, Complex.norm_exp]
  have h0 := prod_norm_nonneg ys
  calc Real.exp (B x x).re * ‖diagProd ys x‖
      ≤ Real.exp (-ε * ‖x‖ ^ 2) * ((ys.map (‖·‖)).prod * ‖x‖ ^ (2 * ys.length)) :=
        mul_le_mul (Real.exp_le_exp.2 (by linarith [hB x])) (norm_diagProd_le ys x) (norm_nonneg _)
          (Real.exp_pos _).le
    _ = _ := by ring

theorem continuous_integrand (B : V →L[ℝ] V →L[ℝ] ℂ) (ys : List (V →L[ℝ] V →L[ℝ] ℂ)) :
    Continuous fun x => Complex.exp (B x x) * diagProd ys x :=
  (Complex.continuous_exp.comp (B.continuous.clm_apply continuous_id)).mul (continuous_diagProd ys)

theorem integrable_integrand {B : V →L[ℝ] V →L[ℝ] ℂ} {ε : ℝ} (hε : 0 < ε)
    (hB : ∀ x, (B x x).re ≤ -(ε * ‖x‖ ^ 2)) (ys : List (V →L[ℝ] V →L[ℝ] ℂ)) :
    Integrable (fun x => Complex.exp (B x x) * diagProd ys x) μ :=
  ((integrable_norm_pow_mul_exp μ _ hε).const_mul _).mono'
    (continuous_integrand B ys).aestronglyMeasurable (Eventually.of_forall (norm_integrand_le hB ys))

def integrandDeriv (ys : List (V →L[ℝ] V →L[ℝ] ℂ)) (B : V →L[ℝ] V →L[ℝ] ℂ) (x : V) :
    (V →L[ℝ] V →L[ℝ] ℂ) →L[ℝ] ℂ :=
  (Complex.exp (B x x) * diagProd ys x) • evalDiag x

theorem hasFDerivAt_integrand (ys : List (V →L[ℝ] V →L[ℝ] ℂ)) (B : V →L[ℝ] V →L[ℝ] ℂ) (x : V) :
    HasFDerivAt (fun B' : V →L[ℝ] V →L[ℝ] ℂ => Complex.exp (B' x x) * diagProd ys x)
      (integrandDeriv ys B x) B := by
  have := ((evalDiag x).hasFDerivAt (x := B)).cexp.mul_const (diagProd ys x)
  refine this.congr_fderiv ?_
  ext B'
  simp [integrandDeriv]
  try ring

theorem norm_integrandDeriv_le {B : V →L[ℝ] V →L[ℝ] ℂ} {ε : ℝ}
    (hB : ∀ x, (B x x).re ≤ -(ε * ‖x‖ ^ 2)) (ys : List (V →L[ℝ] V →L[ℝ] ℂ)) (x : V) :
    ‖integrandDeriv ys B x‖ ≤
      (ys.map (‖·‖)).prod * (‖x‖ ^ (2 * ys.length + 2) * Real.exp (-ε * ‖x‖ ^ 2)) := by
  rw [integrandDeriv, norm_smul]
  calc ‖Complex.exp (B x x) * diagProd ys x‖ * ‖evalDiag x‖
      ≤ ((ys.map (‖·‖)).prod * (‖x‖ ^ (2 * ys.length) * Real.exp (-ε * ‖x‖ ^ 2))) * (‖x‖ * ‖x‖) :=
        mul_le_mul (norm_integrand_le hB ys x) (norm_evalDiag_le x) (norm_nonneg _)
          (by have := prod_norm_nonneg ys; positivity)
    _ = _ := by ring

theorem integrable_integrandDeriv {B : V →L[ℝ] V →L[ℝ] ℂ} {ε : ℝ} (hε : 0 < ε)
    (hB : ∀ x, (B x x).re ≤ -(ε * ‖x‖ ^ 2)) (ys : List (V →L[ℝ] V →L[ℝ] ℂ)) :
    Integrable (integrandDeriv ys B) μ :=
  ((integrable_norm_pow_mul_exp μ _ hε).const_mul _).mono'
    (((continuous_integrand B ys).smul continuous_evalDiag).aestronglyMeasurable)
    (Eventually.of_forall (norm_integrandDeriv_le hB ys))

theorem hasFDerivAt_gaussMoment (ys : List (V →L[ℝ] V →L[ℝ] ℂ)) {B : V →L[ℝ] V →L[ℝ] ℂ}
    (hB : B ∈ negDef) :
    HasFDerivAt (gaussMoment μ ys) (∫ x, integrandDeriv ys B x ∂μ) B := by
  obtain ⟨ε, hε, hBε⟩ := hB
  have hball : ∀ B' ∈ ball B (ε / 2), ∀ x, (B' x x).re ≤ -(ε / 2 * ‖x‖ ^ 2) := fun B' hB' =>
    re_le_of_norm_sub_le hBε (by rw [mem_ball, dist_eq_norm] at hB'; exact hB'.le)
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun B' x => Complex.exp (B' x x) * diagProd ys x)
    (ball_mem_nhds B (by positivity : 0 < ε / 2))
    (bound := fun x => (ys.map (‖·‖)).prod *
      (‖x‖ ^ (2 * ys.length + 2) * Real.exp (-(ε / 2) * ‖x‖ ^ 2)))
    (Eventually.of_forall fun B' => (continuous_integrand B' ys).aestronglyMeasurable)
    (integrable_integrand μ hε hBε ys)
    (integrable_integrandDeriv μ hε hBε ys).aestronglyMeasurable
    (Eventually.of_forall fun x B' hB' => norm_integrandDeriv_le (hball B' hB') ys x)
    ((integrable_norm_pow_mul_exp μ _ (by positivity)).const_mul _)
    (Eventually.of_forall fun x B' _ => hasFDerivAt_integrand ys B' x)

theorem fderiv_gaussMoment_apply (ys : List (V →L[ℝ] V →L[ℝ] ℂ)) {B : V →L[ℝ] V →L[ℝ] ℂ}
    (hB : B ∈ negDef) (y : V →L[ℝ] V →L[ℝ] ℂ) :
    fderiv ℝ (gaussMoment μ ys) B y = gaussMoment μ (y :: ys) B := by
  obtain ⟨ε, hε, hBε⟩ := id hB
  rw [(hasFDerivAt_gaussMoment μ ys hB).fderiv,
    ContinuousLinearMap.integral_apply (integrable_integrandDeriv μ hε hBε ys)]
  unfold gaussMoment
  congr 1
  funext x
  simp [integrandDeriv, diagProd]
  ring

theorem contDiffOn_gaussMoment (n : ℕ) :
    ∀ ys : List (V →L[ℝ] V →L[ℝ] ℂ), ContDiffOn ℝ n (gaussMoment μ ys) negDef := by
  induction n with
  | zero =>
    intro ys
    exact contDiffOn_zero.2 fun B hB =>
      (hasFDerivAt_gaussMoment μ ys hB).continuousAt.continuousWithinAt
  | succ n ih =>
    intro ys
    have := contDiffOn_succ_of_fderiv_apply (n := (n : WithTop ℕ∞)) (f := gaussMoment μ ys)
      (s := negDef)
      (fun B hB => (hasFDerivAt_gaussMoment μ ys hB).differentiableAt.differentiableWithinAt)
      (fun h => by simp at h)
      (fun y => (ih (y :: ys)).congr fun B hB => by
        rw [fderivWithin_of_isOpen isOpen_negDef hB, fderiv_gaussMoment_apply μ ys hB])
    exact_mod_cast this


omit [MeasurableSpace V] [BorelSpace V] in
def toCont (N : V →ₗ[ℝ] V →ₗ[ℝ] ℂ) : V →L[ℝ] V →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (V →ₗ[ℝ] ℂ) ≃ₗ[ℝ] (V →L[ℝ] ℂ)).toLinearMap ∘ₗ N)



omit [MeasurableSpace V] [BorelSpace V] in
def pairForm (M : ℝ → V →ₗ[ℝ] V →ₗ[ℝ] ℂ) (p : ℝ × ℝ) : V →L[ℝ] V →L[ℝ] ℂ :=
  toCont (M p.1 + (M p.2).compr₂ (Complex.conjAe.toLinearMap))

omit [MeasurableSpace V] [BorelSpace V] in
@[simp] theorem pairForm_apply (M : ℝ → V →ₗ[ℝ] V →ₗ[ℝ] ℂ) (p : ℝ × ℝ) (x y : V) :
    pairForm M p x y = M p.1 x y + starRingEnd ℂ (M p.2 x y) := by
  simp [pairForm, toCont]

theorem gauss_pairing_smooth_ne_zero (M : ℝ → V →ₗ[ℝ] V →ₗ[ℝ] ℂ)
    (hM : ∀ x y, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => M t x y)
    (hneg : ∀ t₀ : ℝ, ∃ ε > 0, ∀ᶠ t in nhds t₀, ∀ x, (M t x x).re ≤ -(ε * ‖x‖ ^ 2)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ =>
      ∫ x, Complex.exp (M p.1 x x) * starRingEnd ℂ (Complex.exp (M p.2 x x)) ∂μ) ∧
    ∀ u, ∫ x, Complex.exp (M u x x) * starRingEnd ℂ (Complex.exp (M u x x)) ∂μ ≠ 0 := by
  have hneg' : ∀ t, ∃ ε > 0, ∀ x, (M t x x).re ≤ -(ε * ‖x‖ ^ 2) := fun t => by
    obtain ⟨ε, hε, h⟩ := hneg t
    exact ⟨ε, hε, h.self_of_nhds⟩
  constructor
  · have hP : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (pairForm M) := by
      rw [contDiff_clm_apply_iff]
      intro x
      rw [contDiff_clm_apply_iff]
      intro y
      simp only [pairForm_apply]
      exact ((hM x y).comp contDiff_fst).add
        (Complex.conjCLE.contDiff.comp ((hM x y).comp contDiff_snd))
    have hmem : ∀ p, pairForm M p ∈ negDef := fun p => by
      obtain ⟨ε₁, h₁, hb₁⟩ := hneg' p.1
      obtain ⟨ε₂, h₂, hb₂⟩ := hneg' p.2
      refine ⟨ε₁ + ε₂, by positivity, fun x => ?_⟩
      simp only [pairForm_apply, Complex.add_re, Complex.conj_re]
      linarith [hb₁ x, hb₂ x]
    have heq : (fun p : ℝ × ℝ =>
        ∫ x, Complex.exp (M p.1 x x) * starRingEnd ℂ (Complex.exp (M p.2 x x)) ∂μ) =
        gaussMoment μ [] ∘ pairForm M := by
      funext p
      simp only [Function.comp, gaussMoment, diagProd, List.map_nil, List.prod_nil, mul_one,
        pairForm_apply]
      congr 1
      funext x
      rw [← Complex.exp_conj, ← Complex.exp_add]
    rw [heq]
    exact contDiff_infty.2 fun n =>
      (contDiffOn_gaussMoment μ n []).comp_contDiff (contDiff_infty.1 hP n) hmem
  · intro u
    obtain ⟨ε, hε, hb⟩ := hneg' u
    have hpt : ∀ x, Complex.exp (M u x x) * starRingEnd ℂ (Complex.exp (M u x x)) =
        ((Real.exp (2 * (M u x x).re) : ℝ) : ℂ) := fun x => by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.norm_exp, sq, ← Real.exp_add,
        two_mul]
    simp only [hpt]
    rw [integral_complex_ofReal, Complex.ofReal_ne_zero]
    have hc : Continuous fun x => M u x x := (toCont (M u)).continuous.clm_apply continuous_id
    refine (integral_exp_pos ?_).ne'
    refine (integrable_norm_pow_mul_exp μ 0 (by positivity : 0 < 2 * ε)).mono'
      ((Real.continuous_exp.comp (continuous_const.mul
        (Complex.continuous_re.comp hc))).aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), pow_zero, one_mul]
    exact Real.exp_le_exp.2 (by linarith [hb x])

end GlobalTheory.GaussPairing
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GaussianPairingIntegralContDiffNeZeroDiagStatement
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussianPairingIntegral_contDiff_ne_zero_diag : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (M : ℝ → V →ₗ[ℝ] V →ₗ[ℝ] ℂ),
    (∀ x y, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => M t x y) →
    (∀ t₀ : ℝ, ∃ ε > 0, ∀ᶠ t in nhds t₀, ∀ x, (M t x x).re ≤ -(ε * ‖x‖ ^ 2)) →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => ∫ x, Complex.exp (M p.1 x x) * starRingEnd ℂ (Complex.exp (M p.2 x x)) ∂μ) ∧
    ∀ u, ∫ x, Complex.exp (M u x x) * starRingEnd ℂ (Complex.exp (M u x x)) ∂μ ≠ 0 := by
  first | exact @GlobalTheory.GaussPairing.gauss_pairing_smooth_ne_zero | exact GlobalTheory.GaussPairing.gauss_pairing_smooth_ne_zero | (intros; apply GlobalTheory.GaussPairing.gauss_pairing_smooth_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSchwartzHeisenbergOperatorDerivative
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSchwartzHeisenbergOperatorDerivative
open MeasureTheory

namespace GlobalTheory

open LineDeriv

theorem dHeis_schwartz {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (w : V × V) (f : SchwartzMap V ℂ) :
    ∃ g : SchwartzMap V ℂ, ∀ x, g x = GlobalTheory.GaussLine.dHeis β w ⇑f x := by
  let L : V →L[ℝ] ℂ := Complex.ofRealCLM.comp (LinearMap.toContinuousLinearMap (β.flip w.2))
  have hL : Function.HasTemperateGrowth (fun x : V => (L x : ℂ)) := L.hasTemperateGrowth
  refine ⟨∂_{w.1} f - (2 * Real.pi * Complex.I) • SchwartzMap.smulLeftCLM ℂ (fun x : V => (L x : ℂ)) f, ?_⟩
  intro x
  rw [SchwartzMap.sub_apply, SchwartzMap.smul_apply, SchwartzMap.smulLeftCLM_apply_apply hL,
    SchwartzMap.lineDerivOp_apply_eq_fderiv]
  simp [GlobalTheory.GaussLine.dHeis, L, smul_eq_mul]
  ring

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSchwartzHeisenbergOperatorDerivativeStatement
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_schwartz_heisenbergOperatorDerivative : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (w : V × V) (f : SchwartzMap V ℂ),
    ∃ g : SchwartzMap V ℂ, ∀ x, g x = GlobalTheory.GaussLine.dHeis β w ⇑f x := by
  first | exact @GlobalTheory.dHeis_schwartz | exact GlobalTheory.dHeis_schwartz | (intros; apply GlobalTheory.dHeis_schwartz <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilOneParamMovesFockVacuumSmoothly
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical

noncomputable section

theorem GlobalTheory.WeilVacuum.smooth_flow : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [μ.IsAddHaarMeasure] (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ), (∀ q, (∀ x, β x q = 0) → q = 0) →
    ∀ T : ℝ → SchwartzMap V ℂ →ₗ[ℂ] SchwartzMap V ℂ, (∀ s t f, T (s + t) f = T s (T t f)) → (∀ f, T 0 f = f) →
    (∀ t f, ∫ x, ‖T t f x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ) →
    ∀ A : ℝ → (V × V) →ₗ[ℝ] (V × V), (∀ w, Continuous fun t => A t w) → (∀ s t, A (s + t) = (A s).comp (A t)) →
    A 0 = LinearMap.id →
    (∀ (t : ℝ) (p q : V) (f g : SchwartzMap V ℂ), ⇑g = GlobalTheory.GaussLine.heisFun β p q ⇑f →
      ⇑(T t g) = GlobalTheory.GaussLine.heisFun β (A t (p, q)).1 (A t (p, q)).2 ⇑(T t f)) →
    (∀ f x, Continuous fun t => T t f x) →
    ∀ J₀ : (V × V) →ₗ[ℝ] (V × V), (∀ w, J₀ (J₀ w) = -w) →
    ∀ f₀ : SchwartzMap V ℂ, (∀ w x, GlobalTheory.GaussLine.dHeis β (J₀ w) ⇑f₀ x = Complex.I * GlobalTheory.GaussLine.dHeis β w ⇑f₀ x) →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × V => T p.1 f₀ p.2) ∧
    ∃ (n : ℕ) (qs qs' : Fin n → V) (cs : Fin n → ℂ) (c : ℂ), ∀ x,
      HasDerivAt (fun t => T t f₀ x) (∑ i, cs i * (β x (qs i) : ℂ) * (β x (qs' i) : ℂ) * f₀ x + c * f₀ x) 0 := by
  intro V _ _ _ _ _ μ _ β hβ T hadd h0 hunit A hAc hAadd hA0 hint hcont J₀ hJ₀ f₀ hf₀
  by_cases hz : f₀ = 0
  · subst hz
    have hT0 : ∀ t, T t 0 = 0 := fun t => map_zero _
    refine ⟨?_, 0, Fin.elim0, Fin.elim0, Fin.elim0, 0, fun x => ?_⟩
    · simp only [hT0, SchwartzMap.zero_apply]; exact contDiff_const
    · simp only [hT0, SchwartzMap.zero_apply, Finset.univ_eq_empty, Finset.sum_empty, zero_mul, add_zero]
      exact hasDerivAt_const _ _
  have hAsm := GlobalTheory.T.contDiff_continuous_oneParameter_finiteDimensional_linear A hAc hAadd hA0
  have hinv : ∀ t w, A t (A (-t) w) = w := by
    intro t w
    have := congrArg (fun L => L w) (hAadd t (-t))
    simp only [add_neg_cancel, hA0, LinearMap.id_apply, LinearMap.comp_apply] at this
    exact this.symm
  have hinv' : ∀ t w, A (-t) (A t w) = w := by
    intro t w
    have := congrArg (fun L => L w) (hAadd (-t) t)
    simp only [neg_add_cancel, hA0, LinearMap.id_apply, LinearMap.comp_apply] at this
    exact this.symm
  set J : ℝ → (V × V) →ₗ[ℝ] (V × V) := fun t => (A t).comp (J₀.comp (A (-t))) with hJdef
  have hJapp : ∀ t w, J t w = A t (J₀ (A (-t) w)) := fun t w => rfl
  have hJsm : ∀ w, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => J t w := by
    intro w
    have e : (fun t => J t w) = fun t => (LinearMap.toContinuousLinearMap (A t))
        ((LinearMap.toContinuousLinearMap J₀) ((LinearMap.toContinuousLinearMap (A (-t))) w)) := by
      funext t; simp [hJapp]
    rw [e]
    exact hAsm.clm_apply ((LinearMap.toContinuousLinearMap J₀).contDiff.comp
      ((hAsm.comp contDiff_neg).clm_apply contDiff_const))
  have hJsq : ∀ t w, J t (J t w) = -w := by
    intro t w; simp only [hJapp, hinv', hJ₀, map_neg, hinv]
  have hFock : ∀ t w x, GlobalTheory.GaussLine.dHeis β (J t w) ⇑(T t f₀) x =
      Complex.I * GlobalTheory.GaussLine.dHeis β w ⇑(T t f₀) x := by
    intro t w x
    set u := A (-t) w
    obtain ⟨g1, hg1⟩ := GlobalTheory.T.exists_schwartz_heisenbergOperatorDerivative β (J₀ u) f₀
    obtain ⟨g2, hg2⟩ := GlobalTheory.T.exists_schwartz_heisenbergOperatorDerivative β u f₀
    have hg12 : g1 = Complex.I • g2 := by
      ext y; rw [SchwartzMap.smul_apply, hg1, hg2, hf₀, smul_eq_mul]
    have hI : ∀ w₁ : V × V, ∀ (s : ℝ) (f g : SchwartzMap V ℂ),
        ⇑g = GlobalTheory.GaussLine.heisFun β (s • w₁).1 (s • w₁).2 ⇑f →
        ⇑(T t g) = GlobalTheory.GaussLine.heisFun β (s • A t w₁).1 (s • A t w₁).2 ⇑(T t f) := by
      intro w₁ s f g h
      have := hint t (s • w₁).1 (s • w₁).2 f g h
      rwa [Prod.mk.eta, map_smul] at this
    have h1 := GlobalTheory.T.heisenberg_equivariant_isometry μ β (T t) (hunit t) (J₀ u) (A t (J₀ u)) (hI _) f₀ g1 hg1 x
    have h2 := GlobalTheory.T.heisenberg_equivariant_isometry μ β (T t) (hunit t) u (A t u) (hI _) f₀ g2 hg2 x
    have hu : A t u = w := hinv t w
    rw [hu] at h2
    rw [hJapp, ← h1, ← h2, hg12, map_smul, SchwartzMap.smul_apply, smul_eq_mul]
  have hne : ∀ t, T t f₀ ≠ 0 := by
    intro t h
    apply hz
    have := hadd (-t) t f₀
    rw [neg_add_cancel, h0, h, map_zero] at this
    exact this
  obtain ⟨M, hMs, hMj, hMdec, hMuniq, n, qs, qs', cs, hMder⟩ :=
    GlobalTheory.T.fockVacua_smooth_family_complexGaussians β hβ J hJsm hJsq (fun t => ⟨T t f₀, hne t, hFock t⟩)
  set cc : ℝ → ℂ := fun t => T t f₀ 0 with hccdef
  have hrep : ∀ t x, T t f₀ x = cc t * Complex.exp (M t x x) := fun t x => hMuniq t (T t f₀) (hFock t) x
  obtain ⟨hK, hKne⟩ := GlobalTheory.T.gaussianPairingIntegral_contDiff_ne_zero_diag μ M hMs hMdec
  set K : ℝ → ℝ → ℂ := fun u v => ∫ x, Complex.exp (M u x x) * starRingEnd ℂ (Complex.exp (M v x x)) ∂μ with hKdef
  have hexp : ∀ u v, ∫ x, T u f₀ x * starRingEnd ℂ (T v f₀ x) ∂μ = cc u * starRingEnd ℂ (cc v) * K u v := by
    intro u v
    simp_rw [hrep, map_mul]
    rw [hKdef, ← integral_const_mul]
    congr 1; funext x; ring
  have hpol := fun s => GlobalTheory.T.schwartz_isometry_inner_product_eq μ (T s) (hunit s)
  have eq1 : ∀ s t, cc (s + t) * starRingEnd ℂ (cc s) * K (s + t) s = cc t * starRingEnd ℂ (cc 0) * K t 0 := by
    intro s t
    have := hpol s (T t f₀) (T 0 f₀)
    rw [← hadd, ← hadd, add_zero] at this
    rw [← hexp, ← hexp, this]
  have eq2 : ∀ s, cc s * starRingEnd ℂ (cc s) * K s s = cc 0 * starRingEnd ℂ (cc 0) * K 0 0 := by
    intro s
    have := hpol s f₀ f₀
    rw [← hexp, ← hexp, this, h0]
  have hc0 : cc 0 ≠ 0 := by
    intro h; apply hz; ext x
    rw [← h0 f₀, hrep, h, zero_mul, SchwartzMap.zero_apply]
  have hcs : ∀ s, cc s ≠ 0 := by
    intro s h
    have := eq2 s
    rw [h, zero_mul, zero_mul] at this
    exact mul_ne_zero (mul_ne_zero hc0 ((map_ne_zero _).2 hc0)) (hKne 0) this.symm
  have hKc : Continuous fun p : ℝ × ℝ => K p.1 p.2 := hK.continuous
  set U : Set (ℝ × ℝ) := {p | K (p.1 + p.2) p.1 ≠ 0} with hUdef
  have hUo : IsOpen U := isOpen_ne_fun (hKc.comp ((continuous_fst.add continuous_snd).prodMk continuous_fst)) continuous_const
  have hU0 : ∀ s, (s, 0) ∈ U := by intro s; simp only [hUdef, Set.mem_setOf_eq, add_zero]; exact hKne s
  set E : ℝ → ℝ → ℂ := fun s t => K s s * K t 0 / (cc 0 * K 0 0 * K (s + t) s) with hEdef
  have hEsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => E p.1 p.2) U := by
    have k1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => K p.1 p.1) := hK.comp (contDiff_fst.prodMk contDiff_fst)
    have k2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => K p.2 0) := hK.comp (contDiff_snd.prodMk contDiff_const)
    have k3 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => K (p.1 + p.2) p.1) :=
      hK.comp ((contDiff_fst.add contDiff_snd).prodMk contDiff_fst)
    have hinvd : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => (cc 0 * K 0 0 * K (p.1 + p.2) p.1)⁻¹) U :=
      ((contDiff_const.mul k3).contDiffOn).inv (fun p hp => mul_ne_zero (mul_ne_zero hc0 (hKne 0)) hp)
    have := (k1.mul k2).contDiffOn.mul hinvd
    simpa only [hEdef, div_eq_mul_inv] using this
  have hfe : ∀ p ∈ U, cc (p.1 + p.2) = cc p.1 * cc p.2 * E p.1 p.2 := by
    rintro ⟨s, t⟩ hp
    simp only [hUdef, Set.mem_setOf_eq] at hp
    simp only [hEdef]
    have hd : starRingEnd ℂ (cc 0) ≠ 0 := (map_ne_zero _).2 hc0
    rw [mul_div_assoc', eq_div_iff (mul_ne_zero (mul_ne_zero hc0 (hKne 0)) hp)]
    apply mul_left_cancel₀ hd
    linear_combination (-(cc (s + t) * K (s + t) s)) * eq2 s + (cc s * K s s) * eq1 s t
  have hccc : Continuous cc := by
    have := hcont f₀ 0
    exact this
  have hcsm := GlobalTheory.T.contDiff_of_continuous_quasiMultiplicative_smoothDefect cc E U hccc hc0 hUo hU0 hEsm hfe
  have hfun : (fun p : ℝ × V => T p.1 f₀ p.2) = fun p => cc p.1 * Complex.exp (M p.1 p.2 p.2) := by
    funext p; exact hrep p.1 p.2
  refine ⟨?_, n, qs, qs', cs, deriv cc 0 / cc 0, fun x => ?_⟩
  · rw [hfun]; exact (hcsm.comp contDiff_fst).mul hMj.cexp
  · have hft : (fun t => T t f₀ x) = fun t => cc t * Complex.exp (M t x x) := by funext t; exact hrep t x
    rw [hft]
    have hdc : HasDerivAt cc (deriv cc 0) 0 := ((hcsm.differentiable (by simp)) 0).hasDerivAt
    refine (hdc.mul (hMder x).cexp).congr_deriv ?_
    have hf0x : f₀ x = cc 0 * Complex.exp (M 0 x x) := by rw [← hrep 0 x, h0]
    rw [hf0x, ← Finset.sum_mul]
    field_simp
    ring

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilOneParamMovesFockVacuumSmoothlyStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilOneParam_moves_fockVacuum_smoothly : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [μ.IsAddHaarMeasure] (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ), (∀ q, (∀ x, β x q = 0) → q = 0) →
    ∀ T : ℝ → SchwartzMap V ℂ →ₗ[ℂ] SchwartzMap V ℂ, (∀ s t f, T (s + t) f = T s (T t f)) → (∀ f, T 0 f = f) →
    (∀ t f, ∫ x, ‖T t f x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ) →
    ∀ A : ℝ → (V × V) →ₗ[ℝ] (V × V), (∀ w, Continuous fun t => A t w) → (∀ s t, A (s + t) = (A s).comp (A t)) →
    A 0 = LinearMap.id →
    (∀ (t : ℝ) (p q : V) (f g : SchwartzMap V ℂ), ⇑g = GlobalTheory.GaussLine.heisFun β p q ⇑f →
      ⇑(T t g) = GlobalTheory.GaussLine.heisFun β (A t (p, q)).1 (A t (p, q)).2 ⇑(T t f)) →
    (∀ f x, Continuous fun t => T t f x) →
    ∀ J₀ : (V × V) →ₗ[ℝ] (V × V), (∀ w, J₀ (J₀ w) = -w) →
    ∀ f₀ : SchwartzMap V ℂ, (∀ w x, GlobalTheory.GaussLine.dHeis β (J₀ w) ⇑f₀ x = Complex.I * GlobalTheory.GaussLine.dHeis β w ⇑f₀ x) →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × V => T p.1 f₀ p.2) ∧
    ∃ (n : ℕ) (qs qs' : Fin n → V) (cs : Fin n → ℂ) (c : ℂ), ∀ x,
      HasDerivAt (fun t => T t f₀ x) (∑ i, cs i * (β x (qs i) : ℂ) * (β x (qs' i) : ℂ) * f₀ x + c * f₀ x) 0 := by
  first | exact @GlobalTheory.WeilVacuum.smooth_flow | exact GlobalTheory.WeilVacuum.smooth_flow | (intros; apply GlobalTheory.WeilVacuum.smooth_flow <;> assumption)
end
