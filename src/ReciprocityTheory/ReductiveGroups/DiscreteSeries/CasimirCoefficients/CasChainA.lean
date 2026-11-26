module

public import Mathlib

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.CasChainA
noncomputable section

open Metric Set Filter Topology MeasureTheory Complex
open scoped ContDiff Real

namespace ReciprocityTheory.ChartRestriction.DS.S7

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma cca_cont_theta {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] {F : X → G} {U : Set X}
    (hF : ContinuousOn F U) {κ a : ℝ → ℂ} (hκ : Continuous κ) (ha : Continuous a) {z u : X}
    (hz : ∀ θ, z + a θ • u ∈ U) : Continuous (fun θ => κ θ • F (z + a θ • u)) := hκ.smul (hF.comp_continuous (continuous_const.add (ha.smul continuous_const)) hz)

lemma cca_bounds {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ X]
    {F : X → G} {U : Set X} (hF : ContinuousOn F U) {κ a : ℝ → ℂ} (hκ : Continuous κ)
    (ha : Continuous a) {z₀ u : X} {δ : ℝ} (hsub : ∀ z ∈ closedBall z₀ δ, ∀ θ, z + a θ • u ∈ U) :
    ∃ B : ℝ, ∀ z ∈ closedBall z₀ δ, ∀ θ ∈ Set.uIoc (0 : ℝ) (2 * π), ‖κ θ • F (z + a θ • u)‖ ≤ B := by
  have hK : IsCompact (closedBall z₀ δ ×ˢ Set.uIcc (0 : ℝ) (2 * π)) :=
    (isCompact_closedBall z₀ δ).prod isCompact_uIcc
  have hc : ContinuousOn (fun p : X × ℝ => κ p.2 • F (p.1 + a p.2 • u))
      (closedBall z₀ δ ×ˢ Set.uIcc (0 : ℝ) (2 * π)) := by
    refine (hκ.comp continuous_snd).continuousOn.smul ?_
    refine hF.comp (f := fun p : X × ℝ => p.1 + a p.2 • u)
      (continuous_fst.add ((ha.comp continuous_snd).smul continuous_const)).continuousOn ?_
    intro p hp
    exact hsub p.1 hp.1 p.2
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hc
  exact ⟨B, fun z hz θ hθ => hB (z, θ) ⟨hz, Set.uIoc_subset_uIcc hθ⟩⟩

lemma cca_contAt [FiniteDimensional ℂ X] {F : X → E} {U : Set X} (hU : IsOpen U)
    (hF : ContinuousOn F U) {κ a : ℝ → ℂ} (hκ : Continuous κ) (ha : Continuous a) {z₀ u : X}
    {δ : ℝ} (hδ : 0 < δ) (hsub : ∀ z ∈ closedBall z₀ δ, ∀ θ, z + a θ • u ∈ U) :
    ContinuousAt (fun z => ∫ θ in (0 : ℝ)..2 * π, κ θ • F (z + a θ • u)) z₀ := by
  obtain ⟨B, hB⟩ := cca_bounds hF hκ ha hsub
  have hball : closedBall z₀ δ ∈ 𝓝 z₀ := closedBall_mem_nhds z₀ hδ
  apply intervalIntegral.continuousAt_of_dominated_interval (bound := fun _ => B)
  · filter_upwards [hball] with z hz
    exact (cca_cont_theta hF hκ ha (hsub z hz)).aestronglyMeasurable
  · filter_upwards [hball] with z hz
    exact Filter.Eventually.of_forall (fun θ hθ => hB z hz θ hθ)
  · exact intervalIntegrable_const
  · refine Filter.Eventually.of_forall (fun θ _ => ?_)
    have hmem : z₀ + a θ • u ∈ U := hsub z₀ (mem_closedBall_self hδ.le) θ
    exact continuousAt_const.smul (ContinuousAt.comp (g := F) (f := fun z => z + a θ • u)
      (hF.continuousAt (hU.mem_nhds hmem)) (continuous_add_const _).continuousAt)

lemma cca_hasFDerivAt [FiniteDimensional ℂ X] {F : X → E} {U : Set X} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) (hD : ContinuousOn (fderiv ℂ F) U) {κ a : ℝ → ℂ}
    (hκ : Continuous κ) (ha : Continuous a) {z₀ u : X} {δ : ℝ} (hδ : 0 < δ)
    (hsub : ∀ z ∈ closedBall z₀ δ, ∀ θ, z + a θ • u ∈ U) :
    HasFDerivAt (fun z => ∫ θ in (0 : ℝ)..2 * π, κ θ • F (z + a θ • u))
      (∫ θ in (0 : ℝ)..2 * π, κ θ • fderiv ℂ F (z₀ + a θ • u)) z₀ := by
  obtain ⟨B, hB⟩ := cca_bounds hD hκ ha hsub
  have hball : closedBall z₀ δ ∈ 𝓝 z₀ := closedBall_mem_nhds z₀ hδ
  have hd : ∀ z ∈ closedBall z₀ δ, ∀ θ, HasFDerivAt (fun x => κ θ • F (x + a θ • u))
      (κ θ • fderiv ℂ F (z + a θ • u)) z := by
    intro z hz θ
    have h1 : HasFDerivAt F (fderiv ℂ F (z + a θ • u)) (z + a θ • u) :=
      (hF.differentiableAt (hU.mem_nhds (hsub z hz θ))).hasFDerivAt
    have h2 := h1.comp z ((hasFDerivAt_id z).add_const (a θ • u))
    have h3 := h2.const_smul (κ θ)
    simp only [ContinuousLinearMap.comp_id] at h3
    exact h3
  refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℂ)
    (F' := fun z θ => κ θ • fderiv ℂ F (z + a θ • u)) (bound := fun _ => B)
    hball ?_ ?_ ?_ ?_ ?_ ?_
  · filter_upwards [hball] with z hz
    exact (cca_cont_theta hF.continuousOn hκ ha (hsub z hz)).aestronglyMeasurable
  · exact (cca_cont_theta hF.continuousOn hκ ha
      (hsub z₀ (mem_closedBall_self hδ.le))).intervalIntegrable _ _
  · exact (cca_cont_theta hD hκ ha (hsub z₀ (mem_closedBall_self hδ.le))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun θ hθ z hz => hB z hz θ hθ)
  · exact intervalIntegrable_const
  · exact Filter.Eventually.of_forall (fun θ _ z hz => hd z hz θ)

lemma cca_loc {U : Set X} (hU : IsOpen U) {z₀ : X} (hz₀ : z₀ ∈ U) (u : X) :
    ∃ δ > 0, ∃ ρ > 0, ∀ z ∈ closedBall z₀ δ, ∀ t ∈ closedBall (0 : ℂ) ρ, z + t • u ∈ U := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU z₀ hz₀
  refine ⟨ε / 2, by positivity, ε / (2 * (‖u‖ + 1)), by positivity, fun z hz t ht => hball ?_⟩
  rw [Metric.mem_ball, dist_eq_norm]
  rw [Metric.mem_closedBall, dist_eq_norm] at hz ht
  rw [sub_zero] at ht
  have h1 : ‖t • u‖ ≤ ε / (2 * (‖u‖ + 1)) * ‖u‖ := by
    rw [norm_smul]; exact mul_le_mul_of_nonneg_right ht (norm_nonneg _)
  have h2 : ε / (2 * (‖u‖ + 1)) * ‖u‖ < ε / 2 := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg u]
  calc ‖z + t • u - z₀‖ = ‖(z - z₀) + t • u‖ := by congr 1; abel
    _ ≤ ‖z - z₀‖ + ‖t • u‖ := norm_add_le _ _
    _ < ε := by linarith

def ccaKappa (ρ : ℝ) (θ : ℝ) : ℂ := deriv (circleMap 0 ρ) θ * (1 / (circleMap 0 ρ θ - 0) ^ 2)

lemma cca_kappa_cont {ρ : ℝ} (hρ : 0 < ρ) : Continuous (ccaKappa ρ) := by
  show Continuous fun θ => ccaKappa ρ θ
  simp only [ccaKappa, deriv_circleMap, sub_zero]
  refine ((continuous_circleMap 0 ρ).mul continuous_const).mul ?_
  refine continuous_const.div ((continuous_circleMap 0 ρ).pow 2) (fun θ => ?_)
  exact pow_ne_zero 2 (circleMap_ne_center hρ.ne')

lemma cca_mem_disc {ρ : ℝ} (hρ : 0 < ρ) (θ : ℝ) : circleMap 0 ρ θ ∈ closedBall (0 : ℂ) ρ := circleMap_mem_closedBall 0 hρ.le θ

lemma cca_fderiv_eq [CompleteSpace E] {F : X → E} {U : Set X} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) {z u : X} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : ∀ t ∈ closedBall (0 : ℂ) ρ, z + t • u ∈ U) :
    fderiv ℂ F z u = (2 * π * I)⁻¹ •
      ∫ θ in (0 : ℝ)..2 * π, ccaKappa ρ θ • F (z + circleMap 0 ρ θ • u) := by
  have hU' : IsOpen {t : ℂ | z + t • u ∈ U} :=
    hU.preimage (continuous_const.add (continuous_id.smul continuous_const))
  have hg : DifferentiableOn ℂ (fun t : ℂ => F (z + t • u)) {t : ℂ | z + t • u ∈ U} :=
    hF.comp (((differentiable_id.smul_const u).const_add z).differentiableOn) (fun t ht => ht)
  have hz : z ∈ U := by simpa using hsub 0 (mem_closedBall_self hρ.le)
  have hderiv : deriv (fun t : ℂ => F (z + t • u)) 0 = fderiv ℂ F z u := by
    have hF' : HasFDerivAt F (fderiv ℂ F z) (z + (0 : ℂ) • u) := by
      simpa using (hF.differentiableAt (hU.mem_nhds hz)).hasFDerivAt
    have hl : HasDerivAt (fun t : ℂ => z + t • u) u 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).smul_const u).const_add z
    exact (hF'.comp_hasDerivAt (0 : ℂ) hl).deriv
  rw [← hderiv, ← two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable hU'
    (fun t ht => hsub t ht) hg (mem_ball_self hρ)]
  congr 1
  simp only [circleIntegral]
  refine intervalIntegral.integral_congr (fun θ _ => ?_)
  simp only [ccaKappa, smul_smul, one_div]

lemma cca_local_formula [CompleteSpace E] {F : X → E} {U : Set X} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) {z₀ : X} (hz₀ : z₀ ∈ U) (u : X) :
    ∃ δ > 0, ∃ ρ > 0, (∀ z ∈ closedBall z₀ δ, ∀ θ, z + circleMap 0 ρ θ • u ∈ U) ∧
      ∀ z ∈ closedBall z₀ δ, fderiv ℂ F z u = (2 * π * I)⁻¹ •
        ∫ θ in (0 : ℝ)..2 * π, ccaKappa ρ θ • F (z + circleMap 0 ρ θ • u) := by
  obtain ⟨δ, hδ, ρ, hρ, h⟩ := cca_loc hU hz₀ u
  exact ⟨δ, hδ, ρ, hρ, fun z hz θ => h z hz _ (cca_mem_disc hρ θ),
    fun z hz => cca_fderiv_eq hU hF hρ (h z hz)⟩

theorem cca_continuousOn_fderiv [FiniteDimensional ℂ X] [CompleteSpace E] {F : X → E} {U : Set X}
    (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) : ContinuousOn (fderiv ℂ F) U := by
  rw [continuousOn_clm_apply]
  intro u z₀ hz₀
  obtain ⟨δ, hδ, ρ, hρ, hsub, heq⟩ := cca_local_formula hU hF hz₀ u
  have hc := cca_contAt hU hF.continuousOn (cca_kappa_cont hρ) (continuous_circleMap 0 ρ) hδ hsub
  have hev : (fun z => fderiv ℂ F z u) =ᶠ[𝓝 z₀] fun z => (2 * π * I)⁻¹ •
      ∫ θ in (0 : ℝ)..2 * π, ccaKappa ρ θ • F (z + circleMap 0 ρ θ • u) := by
    filter_upwards [closedBall_mem_nhds z₀ hδ] with z hz using heq z hz
  exact ((hc.const_smul ((2 * π * I)⁻¹)).congr hev.symm).continuousWithinAt

theorem cca_differentiableOn_fderiv_apply [FiniteDimensional ℂ X] [CompleteSpace E] {F : X → E}
    {U : Set X} (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) (u : X) :
    DifferentiableOn ℂ (fun z => fderiv ℂ F z u) U := by
  intro z₀ hz₀
  obtain ⟨δ, hδ, ρ, hρ, hsub, heq⟩ := cca_local_formula hU hF hz₀ u
  have hD := cca_continuousOn_fderiv hU hF
  have hfd := cca_hasFDerivAt hU hF hD (cca_kappa_cont hρ) (continuous_circleMap 0 ρ) hδ hsub
  have hev : (fun z => fderiv ℂ F z u) =ᶠ[𝓝 z₀] fun z => (2 * π * I)⁻¹ •
      ∫ θ in (0 : ℝ)..2 * π, ccaKappa ρ θ • F (z + circleMap 0 ρ θ • u) := by
    filter_upwards [closedBall_mem_nhds z₀ hδ] with z hz using heq z hz
  exact ((hfd.const_smul ((2 * π * I)⁻¹)).differentiableAt.congr_of_eventuallyEq hev).differentiableWithinAt

theorem cca_contDiffOn_nat [FiniteDimensional ℂ X] [CompleteSpace E] {U : Set X} (hU : IsOpen U) :
    ∀ (k : ℕ) {F : X → E}, DifferentiableOn ℂ F U → ContDiffOn ℂ k F U := by
  intro k
  induction k with
  | zero => intro F hF; exact contDiffOn_zero.2 hF.continuousOn
  | succ k ih =>
    intro F hF
    have hk : ContDiffOn ℂ k (fderiv ℂ F) U := by
      rw [contDiffOn_clm_apply]
      intro u
      exact ih (cca_differentiableOn_fderiv_apply hU hF u)
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hU]
    exact ⟨hF, fun h => absurd h (by simp), hk⟩

theorem cca_contDiffOn [FiniteDimensional ℂ X] [CompleteSpace E] {F : X → E} {U : Set X}
    (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) : ContDiffOn ℂ ∞ F U := contDiffOn_infty.2 fun k => cca_contDiffOn_nat hU k hF

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.GelfandGB
noncomputable section

open MeasureTheory Filter Topology
open scoped ContDiff

namespace ReciprocityTheory.ChartRestriction.DS.S7.GelfandGB

variable {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] [ProperSpace H] [FiniteDimensional ℂ H]
  {K : Type} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [OpensMeasurableSpace K]
  [T2Space K]
  (ν : Measure K) [IsFiniteMeasure ν]
  (c : K → H →L[ℂ] H) (hc : Continuous c) {U Ω : Set H} (hU : IsOpen U) (hΩ : IsOpen Ω)
  (hUΩ : ∀ x ∈ U, ∀ k, c k x ∈ Ω)

def Mop {E' E : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E'] [NormedAddCommGroup E] [NormedSpace ℂ E]
    (L : K → E' →L[ℂ] E) (k : K) : (H →L[ℂ] E') →L[ℂ] (H →L[ℂ] E) :=
  (ContinuousLinearMap.compL ℂ H E' E (L k)).comp ((ContinuousLinearMap.compL ℂ H H E').flip (c k))

omit [ProperSpace H] [FiniteDimensional ℂ H] [CompactSpace K] [MeasurableSpace K] [OpensMeasurableSpace K]
  [T2Space K] in
lemma mop_apply {E' E : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E'] [NormedAddCommGroup E]
    [NormedSpace ℂ E] (L : K → E' →L[ℂ] E) (k : K) (T : H →L[ℂ] E') :
    Mop c L k T = (L k).comp (T.comp (c k)) := rfl

include hc in
omit [ProperSpace H] [FiniteDimensional ℂ H] [CompactSpace K] [MeasurableSpace K] [OpensMeasurableSpace K]
  [T2Space K] in
lemma continuous_mop {E' E : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E'] [NormedAddCommGroup E]
    [NormedSpace ℂ E] {L : K → E' →L[ℂ] E} (hL : Continuous L) : Continuous (Mop c L) := by
  have h1 : Continuous fun k => ContinuousLinearMap.compL ℂ H E' E (L k) :=
    (ContinuousLinearMap.compL ℂ H E' E).continuous.comp hL
  have h2 : Continuous fun k => (ContinuousLinearMap.compL ℂ H H E').flip (c k) :=
    (ContinuousLinearMap.compL ℂ H H E').flip.continuous.comp hc
  exact h1.clm_comp h2

include hc hU hΩ hUΩ in
lemma hasFDerivAt_param {E' E : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E'] [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E] (f : H → E') (L : K → E' →L[ℂ] E) (hf : ContDiffOn ℂ 1 f Ω)
    (hL : Continuous L) {x₀ : H} (hx₀ : x₀ ∈ U) :
    HasFDerivAt (fun x => ∫ k, L k (f (c k x)) ∂ν)
      (∫ k, Mop c L k (fderiv ℂ f (c k x₀)) ∂ν) x₀ := by
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU x₀ hx₀
  have hSU : Metric.closedBall x₀ (ε / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (half_lt_self hε)).trans hεU
  have hfc : ContinuousOn f Ω := hf.continuousOn
  have hfd : ContinuousOn (fderiv ℂ f) Ω := hf.continuousOn_fderiv_of_isOpen hΩ le_rfl
  have hdiff : ∀ y ∈ Ω, DifferentiableAt ℂ f y := fun y hy =>
    (hf.differentiableOn one_ne_zero).differentiableAt (hΩ.mem_nhds hy)
  have hcont : ∀ x ∈ U, Continuous fun k => L k (f (c k x)) := fun x hx =>
    hL.clm_apply (hfc.comp_continuous (hc.clm_apply continuous_const) fun k => hUΩ x hx k)
  have hcont' : Continuous fun k => Mop c L k (fderiv ℂ f (c k x₀)) :=
    (continuous_mop c hc hL).clm_apply
      (hfd.comp_continuous (hc.clm_apply continuous_const) fun k => hUΩ x₀ hx₀ k)
  have hcj : Continuous fun p : K × H => c p.1 p.2 := (hc.comp continuous_fst).clm_apply continuous_snd
  obtain ⟨C, hC⟩ := (isCompact_univ.prod (isCompact_closedBall x₀ (ε / 2))).exists_bound_of_continuousOn
    (f := fun p : K × H => Mop c L p.1 (fderiv ℂ f (c p.1 p.2)))
    (((continuous_mop c hc hL).comp continuous_fst).continuousOn.clm_apply
      (hfd.comp hcj.continuousOn fun p hp => hUΩ p.2 (hSU hp.2) p.1))
  have hI : Integrable (fun k => L k (f (c k x₀))) ν := by
    obtain ⟨C0, hC0⟩ := (isCompact_range (hcont x₀ hx₀)).isBounded.exists_norm_le
    exact Integrable.of_bound (hcont x₀ hx₀).aestronglyMeasurable C0
      (Filter.Eventually.of_forall fun k => hC0 _ (Set.mem_range_self k))
  have hD : ∀ k, ∀ x ∈ U,
      HasFDerivAt (fun x => L k (f (c k x))) (Mop c L k (fderiv ℂ f (c k x))) x := by
    intro k x hx
    rw [mop_apply]
    exact (L k).hasFDerivAt.comp x ((hdiff _ (hUΩ x hx k)).hasFDerivAt.comp x (c k).hasFDerivAt)
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := ν) (bound := fun _ => C)
    (F := fun x k => L k (f (c k x))) (F' := fun x k => Mop c L k (fderiv ℂ f (c k x)))
    (Metric.ball_mem_nhds x₀ (half_pos hε))
    (Filter.eventually_of_mem (Metric.ball_mem_nhds x₀ (half_pos hε)) fun x hx =>
      (hcont x (hSU (Metric.ball_subset_closedBall hx))).aestronglyMeasurable)
    hI hcont'.aestronglyMeasurable
    (Filter.Eventually.of_forall fun k x hx =>
      hC (k, x) ⟨Set.mem_univ _, Metric.ball_subset_closedBall hx⟩)
    (integrable_const C)
    (Filter.Eventually.of_forall fun k x hx => hD k x (hSU (Metric.ball_subset_closedBall hx)))

include hc hU hΩ hUΩ in
theorem contDiffOn_param_nat (m : ℕ) : ∀ {E' E : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E']
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E] (f : H → E') (L : K → E' →L[ℂ] E),
    ContDiffOn ℂ ∞ f Ω → Continuous L → ContDiffOn ℂ m (fun x => ∫ k, L k (f (c k x)) ∂ν) U := by
  induction m with
  | zero =>
    intro E' E _ _ _ _ _ _ f L hf hL
    have hf1 : ContDiffOn ℂ 1 f Ω := hf.of_le (by first | exact WithTop.coe_le_coe.mpr le_top | simp | decide : (1 : WithTop ℕ∞) ≤ ∞)
    have h0 : ContDiffOn ℂ 0 (fun x => ∫ k, L k (f (c k x)) ∂ν) U :=
      contDiffOn_zero.mpr fun x hx =>
        (hasFDerivAt_param ν c hc hU hΩ hUΩ f L hf1 hL hx).continuousAt.continuousWithinAt
    exact_mod_cast h0
  | succ m ih =>
    intro E' E _ _ _ _ _ _ f L hf hL
    have hf1 : ContDiffOn ℂ 1 f Ω := hf.of_le (by first | exact WithTop.coe_le_coe.mpr le_top | simp | decide : (1 : WithTop ℕ∞) ≤ ∞)
    have hd := fun x (hx : x ∈ U) => hasFDerivAt_param ν c hc hU hΩ hUΩ f L hf1 hL hx
    have hf' : ContDiffOn ℂ ∞ (fderiv ℂ f) Ω := ((contDiffOn_infty_iff_fderiv_of_isOpen hΩ).mp hf).2
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hU]
    refine ⟨fun x hx => (hd x hx).differentiableAt.differentiableWithinAt,
      fun h => absurd h (by simp), ?_⟩
    exact (ih (fderiv ℂ f) (fun k => Mop c L k) hf' (continuous_mop c hc hL)).congr
      fun x hx => (hd x hx).fderiv

include hc hU hΩ hUΩ in
theorem contDiffOn_param {E' E : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E']
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E] (f : H → E') (L : K → E' →L[ℂ] E)
    (hf : ContDiffOn ℂ ∞ f Ω) (hL : Continuous L) :
    ContDiffOn ℂ ∞ (fun x => ∫ k, L k (f (c k x)) ∂ν) U :=
  contDiffOn_infty.mpr fun m => contDiffOn_param_nat ν c hc hU hΩ hUΩ m f L hf hL

end ReciprocityTheory.ChartRestriction.DS.S7.GelfandGB
end
end
