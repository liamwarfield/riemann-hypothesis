module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.GradientAtPoint

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBrouwerFixedPoint
set_option maxSynthPendingDepth 1

open scoped ContDiff
open Metric

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

theorem BrouwerFixedPoint.smooth_of_changeOfVariablesDegree
    (hL : ChangeOfVariablesDegree.Statement) (n : ℕ) (g : (Fin n → ℝ) → Fin n → ℝ)
    (hg : ContDiff ℝ ∞ g) (hgb : ∀ x, ‖g x‖ ≤ 1) : ∃ x, g x = x := by
  by_contra hne
  push Not at hne
  have hcont : ContinuousOn (fun x => ‖x - g x‖) (closedBall (0 : Fin n → ℝ) 2) :=
    (continuous_id.sub hg.continuous).norm.continuousOn
  obtain ⟨x₀, -, hmin⟩ := (isCompact_closedBall (0 : Fin n → ℝ) 2).exists_isMinOn
    (nonempty_closedBall.2 zero_le_two) hcont
  have hε : 0 < ‖x₀ - g x₀‖ := norm_pos_iff.2 (sub_ne_zero.2 (hne x₀).symm)
  set δ := min ‖x₀ - g x₀‖ 1 with hδ_def
  have hδ : 0 < δ := lt_min hε one_pos

  let χ : ContDiffBump (0 : Fin n → ℝ) := ⟨2, 3, two_pos, by norm_num⟩
  let φ : (Fin n → ℝ) → Fin n → ℝ := fun x => x - χ x • g x
  have hφ : ContDiff ℝ ∞ φ := contDiff_id.sub (χ.contDiff.smul hg)
  have hφc : HasCompactSupport (fun x => φ x - x) := by
    have h : (fun x => φ x - x) = -((fun x => χ x) • g) := by
      funext x; simp [φ]
    rw [h]
    exact χ.hasCompactSupport.smul_right.neg
  have hφδ : ∀ x, δ ≤ ‖φ x‖ := by
    intro x
    by_cases hx : ‖x‖ ≤ 2
    · have hχ : χ x = 1 := χ.one_of_mem_closedBall (mem_closedBall_zero_iff.2 hx)
      have h2 : ‖x₀ - g x₀‖ ≤ ‖x - g x‖ :=
        isMinOn_iff.1 hmin x (mem_closedBall_zero_iff.2 hx)
      simp only [φ, hχ, one_smul]
      exact (min_le_left _ _).trans h2
    · push Not at hx
      have h1 : ‖χ x • g x‖ ≤ 1 := by
        rw [norm_smul, Real.norm_of_nonneg χ.nonneg]
        exact mul_le_one₀ χ.le_one (norm_nonneg _) (hgb x)
      have h3 : ‖x‖ - ‖χ x • g x‖ ≤ ‖φ x‖ := norm_sub_norm_le _ _
      have h4 : δ ≤ 1 := min_le_right _ _
      linarith

  let ψ : ContDiffBump (0 : Fin n → ℝ) := ⟨δ / 2, δ, half_pos hδ, half_lt_self hδ⟩
  have hzero : ∀ x, ψ (φ x) = 0 := by
    intro x
    by_contra h
    have hmem : φ x ∈ ball (0 : Fin n → ℝ) δ := by
      rw [← ψ.support_eq]; exact h
    rw [mem_ball_zero_iff] at hmem
    exact absurd (hφδ x) (not_le.2 hmem)
  have hL' := hL n φ hφ hφc ψ ψ.contDiff ψ.hasCompactSupport
  simp only [hzero, zero_mul, MeasureTheory.integral_zero] at hL'
  exact (ψ.integral_pos (μ := MeasureTheory.volume)).ne hL'

theorem BrouwerFixedPoint.proof (hL : ChangeOfVariablesDegree.Statement) :
    BrouwerFixedPoint.Statement := by
  intro n f hf hmaps
  by_contra hne
  push Not at hne
  set B := closedBall (0 : Fin n → ℝ) 1 with hB_def
  have hB : IsCompact B := isCompact_closedBall _ _
  have hcont : ContinuousOn (fun x => ‖f x - x‖) B := (hf.sub continuousOn_id).norm
  obtain ⟨x₀, hx₀, hmin⟩ := hB.exists_isMinOn (nonempty_closedBall.2 zero_le_one) hcont
  have hε : 0 < ‖f x₀ - x₀‖ := norm_pos_iff.2 (sub_ne_zero.2 (hne x₀ hx₀))

  let P : (Fin n → ℝ) → Fin n → ℝ := fun x i => max (min (x i) 1) (-1)
  have hPB : ∀ x, P x ∈ B := by
    intro x
    rw [hB_def, mem_closedBall_zero_iff]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨le_max_right _ _, max_le (min_le_right _ _) (by norm_num)⟩
  have hPid : ∀ x ∈ B, P x = x := by
    intro x hx
    funext i
    have hi : |x i| ≤ 1 := by
      have h := (norm_le_pi_norm x i).trans (mem_closedBall_zero_iff.1 hx)
      rwa [Real.norm_eq_abs] at h
    rw [abs_le] at hi
    simp only [P, min_eq_left hi.2, max_eq_left hi.1]
  have hPlip : ∀ x y, dist (P x) (P y) ≤ dist x y := by
    intro x y
    refine (dist_pi_le_iff dist_nonneg).2 fun i => ?_
    calc dist (P x i) (P y i) = |max (min (x i) 1) (-1) - max (min (y i) 1) (-1)| :=
          Real.dist_eq _ _
      _ ≤ |min (x i) 1 - min (y i) 1| := abs_max_sub_max_le_abs _ _ _
      _ ≤ max |x i - y i| |1 - 1| := abs_min_sub_min_le_max _ _ _ _
      _ = dist (x i) (y i) := by simp [Real.dist_eq]
      _ ≤ dist x y := dist_le_pi_dist x y i

  let F : (Fin n → ℝ) → Fin n → ℝ := fun x => f (P x)
  have hFu : UniformContinuous F := by
    have hfu : UniformContinuousOn f B := hB.uniformContinuousOn_of_continuous hf
    rw [Metric.uniformContinuous_iff]
    intro η hη
    obtain ⟨d, hd, hfd⟩ := Metric.uniformContinuousOn_iff.1 hfu η hη
    exact ⟨d, hd, fun {a b} hab => hfd _ (hPB a) _ (hPB b) ((hPlip a b).trans_lt hab)⟩
  have hFB : ∀ x, ‖F x‖ ≤ 1 := fun x => mem_closedBall_zero_iff.1 (hmaps (hPB x))

  set a := ‖f x₀ - x₀‖ / 3 with ha_def
  have ha : 0 < a := by positivity
  obtain ⟨G, hG, hGF⟩ := hFu.exists_contDiff_dist_le ha
  set c := (1 + a)⁻¹ with hc_def
  have hc : c * (1 + a) = 1 := inv_mul_cancel₀ (by positivity)
  have hc0 : 0 < c := by positivity
  have hc1 : c ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have hGb : ∀ x, ‖G x‖ ≤ 1 + a := by
    intro x
    have h1 : ‖G x‖ ≤ ‖F x‖ + ‖G x - F x‖ := norm_le_norm_add_norm_sub' _ _
    have h2 : ‖G x - F x‖ < a := by rw [← dist_eq_norm]; exact hGF x
    linarith [hFB x]
  have hgb : ∀ x, ‖c • G x‖ ≤ 1 := by
    intro x
    rw [norm_smul, Real.norm_of_nonneg hc0.le]
    calc c * ‖G x‖ ≤ c * (1 + a) := mul_le_mul_of_nonneg_left (hGb x) hc0.le
      _ = 1 := hc
  obtain ⟨x, hx⟩ := BrouwerFixedPoint.smooth_of_changeOfVariablesDegree hL n (fun x => c • G x)
    (hG.const_smul c) hgb
  have hx' : c • G x = x := hx
  have hxB : x ∈ B := by
    rw [hB_def, mem_closedBall_zero_iff, ← hx']
    exact hgb x
  have hFx : F x = f x := by simp only [F, hPid x hxB]
  have h1 : ‖f x - G x‖ < a := by
    rw [← hFx, ← dist_eq_norm, dist_comm]; exact hGF x
  have h2 : ‖G x - x‖ ≤ a := by
    have h : G x - x = (1 - c) • G x := by
      rw [sub_smul, one_smul, hx']
    rw [h, norm_smul, Real.norm_of_nonneg (by linarith)]
    have := hGb x
    nlinarith
  have h3 : ‖f x - x‖ ≤ ‖f x - G x‖ + ‖G x - x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
  have h4 : ‖f x₀ - x₀‖ ≤ ‖f x - x‖ := isMinOn_iff.1 hmin x hxB
  linarith

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PWeightedAreaFormula
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Set Filter Function Topology

open scoped ENNReal NNReal

noncomputable section

theorem WeightedAreaFormula.proof : WeightedAreaFormula.Statement := by
  intro E _ _ _ _ _ μ _ A f H hA hf hfin hint
  classical
  have hder : ∀ x ∈ A, HasFDerivAt f (fderiv ℝ f x) x := fun x hx =>
    ((hf x hx).differentiableAt (hA.mem_nhds hx)).hasFDerivAt
  set B : Set E := {x ∈ A | (fderiv ℝ f x).det ≠ 0} with hBdef
  have hBA : B ⊆ A := sep_subset _ _

  have hBm : MeasurableSet B := by
    have hm : Measurable fun x => (fderiv ℝ f x).det :=
      ContinuousLinearMap.continuous_det.measurable.comp (measurable_fderiv ℝ f)
    exact hA.measurableSet.inter (hm (measurableSet_singleton 0).compl)

  have hZ : μ (f '' {x ∈ A | (fderiv ℝ f x).det = 0}) = 0 :=
    addHaar_image_eq_zero_of_det_fderivWithin_eq_zero μ
      (fun x hx => (hder x hx.1).hasFDerivWithinAt) (fun x hx => hx.2)

  let r : (E →L[ℝ] E) → ℝ≥0 := fun L => (‖L.inverse‖₊ + 1)⁻¹
  obtain ⟨t, L, htd, htm, hcov, happ, hL⟩ :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f B (fderiv ℝ f)
      (fun x hx => (hder x hx.1).hasFDerivWithinAt) r (fun _ => inv_ne_zero (by positivity))
  set P : ℕ → Set E := fun n => B ∩ t n with hPdef
  have hPm : ∀ n, MeasurableSet (P n) := fun n => hBm.inter (htm n)
  have hPd : Pairwise (Disjoint on P) := fun m n hmn =>
    (htd hmn).mono inter_subset_right inter_subset_right
  have hPA : ∀ n, P n ⊆ A := fun n => inter_subset_left.trans hBA
  have hderP : ∀ n, ∀ x ∈ P n, HasFDerivWithinAt f (fderiv ℝ f x) (P n) x := fun n x hx =>
    (hder x (hPA n hx)).hasFDerivWithinAt
  have hinj : ∀ n, InjOn f (P n) := by
    intro n
    rcases (P n).eq_empty_or_nonempty with h | ⟨x, hx⟩
    · rw [h]; exact injOn_empty f
    obtain ⟨y, hy, hLy⟩ := hL ⟨x, hx.1⟩ n
    set e := (fderiv ℝ f y).toContinuousLinearEquivOfDetNeZero hy.2
    have he : (e : E →L[ℝ] E) = L n := by
      rw [hLy]; exact ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _ _
    have ha := happ n
    rw [← he] at ha
    refine ha.injOn ?_
    rcases subsingleton_or_nontrivial E with hE | hE
    · exact Or.inl hE
    right
    have hr : r (e : E →L[ℝ] E) = (‖(e.symm : E →L[ℝ] E)‖₊ + 1)⁻¹ := by
      simp only [r, ContinuousLinearMap.inverse_equiv]
    rw [hr]
    have hpos : 0 < ‖(e.symm : E →L[ℝ] E)‖₊ := by
      rw [pos_iff_ne_zero, ne_eq, nnnorm_eq_zero]
      intro h0
      obtain ⟨z, hz⟩ := exists_ne (0 : E)
      apply hz
      simpa using congrArg (fun T : E →L[ℝ] E => T (e z)) h0
    exact (inv_lt_inv₀ (by positivity) hpos).2 (lt_add_one _)
  have hBU : B = ⋃ n, P n := by
    rw [← inter_iUnion]; exact (inter_eq_left.2 hcov).symm
  have himg : ∀ n, MeasurableSet (f '' P n) := fun n =>
    measurable_image_of_fderivWithin (hPm n) (hderP n) (hinj n)

  let g : ℕ → E → ℝ := fun n y => H (invFunOn f (P n) y)
  have hgP : ∀ n, ∀ x ∈ P n, g n (f x) = H x := fun n x hx =>
    congrArg H (hinj n (invFunOn_mem ⟨x, hx, rfl⟩) hx (invFunOn_eq ⟨x, hx, rfl⟩))
  let F : ℕ → E → ℝ := fun n => (f '' P n).indicator (g n)
  have hFint : ∀ n, Integrable (F n) μ := fun n =>
    (integrable_indicator_iff (himg n)).2
      ((integrableOn_image_iff_integrableOn_abs_det_fderiv_smul μ (hPm n) (hderP n) (hinj n)
        (g n)).2 ((hint.mono_set (hPA n)).congr_fun
          (fun x hx => by simp only [smul_eq_mul, hgP n x hx]) (hPm n)))
  have hFint_eq : ∀ n, ∫ y, F n y ∂μ = ∫ x in P n, |(fderiv ℝ f x).det| * H x ∂μ := fun n => by
    calc ∫ y, F n y ∂μ = ∫ y in f '' P n, g n y ∂μ := integral_indicator (himg n)
      _ = ∫ x in P n, |(fderiv ℝ f x).det| • g n (f x) ∂μ :=
        integral_image_eq_integral_abs_det_fderiv_smul μ (hPm n) (hderP n) (hinj n) (g n)
      _ = ∫ x in P n, |(fderiv ℝ f x).det| * H x ∂μ :=
        setIntegral_congr_fun (hPm n) fun x hx => by simp only [smul_eq_mul, hgP n x hx]
  have hFlint : ∀ n, ∫⁻ y, ‖F n y‖ₑ ∂μ = ∫⁻ x in P n, ‖|(fderiv ℝ f x).det| * H x‖ₑ ∂μ :=
    fun n => by
    calc ∫⁻ y, ‖F n y‖ₑ ∂μ = ∫⁻ y, (f '' P n).indicator (fun z => ‖g n z‖ₑ) y ∂μ :=
          lintegral_congr fun y => enorm_indicator_eq_indicator_enorm (g n) y
      _ = ∫⁻ y in f '' P n, ‖g n y‖ₑ ∂μ := lintegral_indicator (himg n) _
      _ = ∫⁻ x in P n, ENNReal.ofReal |(fderiv ℝ f x).det| * ‖g n (f x)‖ₑ ∂μ :=
        lintegral_image_eq_lintegral_abs_det_fderiv_mul μ (hPm n) (hderP n) (hinj n)
          (fun z => ‖g n z‖ₑ)
      _ = ∫⁻ x in P n, ‖|(fderiv ℝ f x).det| * H x‖ₑ ∂μ := by
        refine setLIntegral_congr_fun (hPm n) fun x hx => ?_
        simp only [hgP n x hx, enorm_mul, Real.enorm_eq_ofReal_abs, abs_abs]
  have hsumlint : ∑' n, ∫⁻ y, ‖F n y‖ₑ ∂μ ≠ ∞ := by
    simp_rw [hFlint]
    rw [← lintegral_iUnion hPm hPd, ← hBU]
    exact (lt_of_le_of_lt (lintegral_mono_set hBA) (hasFiniteIntegral_iff_enorm.1 hint.2)).ne

  have hinjT : ∀ y, InjOn (fun n => invFunOn f (P n) y) {n | y ∈ f '' P n} := by
    intro y m hm n hn hmn
    by_contra hne
    refine Set.disjoint_left.1 (hPd hne) (invFunOn_mem hm) ?_
    simp only at hmn
    rw [hmn]; exact invFunOn_mem hn
  have hT : ∀ y, {n | y ∈ f '' P n}.Finite := by
    intro y
    refine Set.Finite.of_finite_image ((hfin y).subset ?_) (hinjT y)
    rintro _ ⟨n, hn, rfl⟩
    exact ⟨hPA n (invFunOn_mem hn), invFunOn_eq hn⟩
  have hsum : ∀ y, HasSum (fun n => F n y) (∑ n ∈ (hT y).toFinset, F n y) := fun y =>
    hasSum_sum_of_ne_finset_zero fun n hn =>
      show (f '' P n).indicator (g n) y = 0 from
        indicator_of_notMem (s := f '' P n) (fun h => hn ((hT y).mem_toFinset.2 h)) (g n)

  have hae : ∀ᵐ y ∂μ, ∑' n, F n y = ∑ᶠ x ∈ {x | x ∈ A ∧ f x = y}, H x := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hZ] with y hy
    have hbij : BijOn (fun n => invFunOn f (P n) y) {n | y ∈ f '' P n}
        {x | x ∈ A ∧ f x = y} := by
      refine ⟨fun n hn => ⟨hPA n (invFunOn_mem hn), invFunOn_eq hn⟩, hinjT y, ?_⟩
      rintro x ⟨hxA, hxy⟩
      have hxB : x ∈ B := ⟨hxA, fun hd => hy ⟨x, ⟨hxA, hd⟩, hxy⟩⟩
      obtain ⟨n, hn⟩ := mem_iUnion.1 (hcov hxB)
      have hxP : x ∈ P n := ⟨hxB, hn⟩
      have hyn : y ∈ f '' P n := ⟨x, hxP, hxy⟩
      exact ⟨n, hyn, hinj n (invFunOn_mem hyn) hxP ((invFunOn_eq hyn).trans hxy.symm)⟩
    rw [(hsum y).tsum_eq]
    change _ = ∑ᶠ (x : E) (_ : x ∈ {x | x ∈ A ∧ f x = y}), H x
    rw [← finsum_mem_eq_of_bijOn _ hbij
      (f := fun n => H (invFunOn f (P n) y)) (fun n _ => rfl),
      finsum_mem_eq_finite_toFinset_sum _ (hT y)]
    exact Finset.sum_congr rfl fun n hn =>
      indicator_of_mem (s := f '' P n) ((hT y).mem_toFinset.1 hn) (g n)

  have hGm : AEStronglyMeasurable (fun y => ∑' n, F n y) μ :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun N => (integrable_finsetSum (Finset.range N) fun n _ => hFint n).1)
      (ae_of_all _ fun y => (hsum y).summable.hasSum.tendsto_sum_nat)
  have hGfin : HasFiniteIntegral (fun y => ∑' n, F n y) μ := by
    rw [hasFiniteIntegral_iff_enorm]
    calc ∫⁻ y, ‖∑' n, F n y‖ₑ ∂μ ≤ ∫⁻ y, ∑' n, ‖F n y‖ₑ ∂μ := by
          refine lintegral_mono fun y => ?_
          rw [(hsum y).tsum_eq]
          exact (enorm_sum_le _ _).trans (ENNReal.sum_le_tsum _)
      _ = ∑' n, ∫⁻ y, ‖F n y‖ₑ ∂μ := lintegral_tsum fun n => (hFint n).1.enorm
      _ < ∞ := hsumlint.lt_top

  have hIA : ∫ x in A, |(fderiv ℝ f x).det| * H x ∂μ =
      ∫ x in B, |(fderiv ℝ f x).det| * H x ∂μ :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hA.measurableSet hBA fun x hx => by
      have h0 : (fderiv ℝ f x).det = 0 := by
        by_contra h; exact hx.2 ⟨hx.1, h⟩
      simp [h0]
  have hBint : IntegrableOn (fun x => |(fderiv ℝ f x).det| * H x) (⋃ n, P n) μ := by
    rw [← hBU]; exact hint.mono_set hBA
  refine ⟨Integrable.congr (⟨hGm, hGfin⟩ : Integrable (fun y => ∑' n, F n y) μ) hae, ?_⟩
  rw [← integral_congr_ae hae, integral_tsum (fun n => (hFint n).1) hsumlint, hIA, hBU]
  simp_rw [hFint_eq]
  exact (hasSum_integral_iUnion hPm hPd hBint).tsum_eq

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PAreaMultiplicity
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Module Set Filter Function

open scoped ENNReal NNReal

noncomputable section

theorem areaJacobian_eq_abs_det_comp {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (φ : F ≃ₗᵢ[ℝ] E) (L : E →ₗ[ℝ] F) :
    areaJacobian L = |LinearMap.det (φ.toLinearIsometry.toLinearMap ∘ₗ L)| := by
  have h1 : areaJacobian L = L.normDet := by
    have h := L.normDet_sq
    simp only [RCLike.ofReal_real_eq_id, id_eq] at h
    rw [areaJacobian, ← h, Real.sqrt_sq L.normDet_nonneg]
  rw [h1, ← LinearMap.normDet_eq_abs_det,
    LinearMap.normDet_comp_of_finrank_eq _ _ φ.toLinearEquiv.finrank_eq.symm,
    φ.toLinearIsometry.normDet_eq_one, one_mul]

theorem encard_iUnion_nat_eq_tsum {α : Type*} (s : ℕ → Set α) (hs : Pairwise (Disjoint on s)) :
    (((⋃ n, s n).encard : ℕ∞) : ℝ≥0∞) = ∑' n, (((s n).encard : ℕ∞) : ℝ≥0∞) := by
  let _ : MeasurableSpace α := ⊤
  have hm : ∀ t : Set α, MeasurableSet t := fun _ => MeasurableSpace.measurableSet_top
  rw [← Measure.count_apply (hm _), measure_iUnion hs (fun _ => hm _)]
  simp only [Measure.count_apply (hm _)]

theorem lintegral_abs_det_eq_lintegral_encard {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {A : Set E} {f : E → E} {f' : E → E →L[ℝ] E}
    (hA : MeasurableSet A) (hf' : ∀ x ∈ A, HasFDerivWithinAt f (f' x) A x) :
    ∫⁻ x in A, ENNReal.ofReal |(f' x).det| ∂μ =
      ∫⁻ y, (({x ∈ A | f x = y}.encard : ℕ∞) : ℝ≥0∞) ∂μ := by
  classical
  set B : Set E := {x ∈ A | (f' x).det ≠ 0} with hBdef
  have hBA : B ⊆ A := sep_subset _ _

  have hB : NullMeasurableSet B μ := by
    obtain ⟨d, hdm, hfd⟩ : AEMeasurable (fun x => (f' x).det) (μ.restrict A) :=
      ContinuousLinearMap.continuous_det.measurable.comp_aemeasurable
        (aemeasurable_fderivWithin μ hA hf')
    refine (hA.inter (hdm (measurableSet_singleton 0).compl)).nullMeasurableSet.congr ?_
    filter_upwards [(ae_restrict_iff' hA).1 hfd] with x hx
    change (x ∈ A ∩ d ⁻¹' {0}ᶜ) ↔ (x ∈ B)
    by_cases hxA : x ∈ A
    · simp [B, hxA, hx hxA]
    · simp [B, hxA]

  have hZ : μ (f '' {x ∈ A | (f' x).det = 0}) = 0 :=
    addHaar_image_eq_zero_of_det_fderivWithin_eq_zero μ
      (fun x hx => (hf' x hx.1).mono (sep_subset _ _)) (fun x hx => hx.2)

  let r : (E →L[ℝ] E) → ℝ≥0 := fun L => (‖L.inverse‖₊ + 1)⁻¹
  obtain ⟨t, L, htd, htm, hcov, happ, hL⟩ :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f B f'
      (fun x hx => (hf' x hx.1).mono hBA) r (fun _ => inv_ne_zero (by positivity))
  set P : ℕ → Set E := fun n => B ∩ t n with hPdef
  have hPm : ∀ n, NullMeasurableSet (P n) μ := fun n => hB.inter (htm n).nullMeasurableSet
  have hPd : Pairwise (Disjoint on P) := fun m n hmn =>
    (htd hmn).mono inter_subset_right inter_subset_right
  have hPA : ∀ n, P n ⊆ A := fun n => inter_subset_left.trans hBA
  have hderP : ∀ n, ∀ x ∈ P n, HasFDerivWithinAt f (f' x) (P n) x := fun n x hx =>
    (hf' x (hPA n hx)).mono (hPA n)
  have hinj : ∀ n, InjOn f (P n) := by
    intro n
    rcases (P n).eq_empty_or_nonempty with h | ⟨x, hx⟩
    · rw [h]; exact injOn_empty f
    obtain ⟨y, hy, hLy⟩ := hL ⟨x, hx.1⟩ n
    set e := (f' y).toContinuousLinearEquivOfDetNeZero hy.2
    have he : (e : E →L[ℝ] E) = L n := by
      rw [hLy]; exact ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _ _
    have ha := happ n
    rw [← he] at ha
    refine ha.injOn ?_
    rcases subsingleton_or_nontrivial E with hE | hE
    · exact Or.inl hE
    right
    have hr : r (e : E →L[ℝ] E) = (‖(e.symm : E →L[ℝ] E)‖₊ + 1)⁻¹ := by
      simp only [r, ContinuousLinearMap.inverse_equiv]
    rw [hr]
    have hpos : 0 < ‖(e.symm : E →L[ℝ] E)‖₊ := by
      rw [pos_iff_ne_zero, ne_eq, nnnorm_eq_zero]
      intro h0
      obtain ⟨z, hz⟩ := exists_ne (0 : E)
      apply hz
      simpa using congrArg (fun T : E →L[ℝ] E => T (e z)) h0
    exact (inv_lt_inv₀ (by positivity) hpos).2 (lt_add_one _)
  have hBU : B = ⋃ n, P n := by
    rw [← inter_iUnion]; exact (inter_eq_left.2 hcov).symm
  have himg : ∀ n, NullMeasurableSet (f '' P n) μ := fun n =>
    nullMeasurable_image_of_fderivWithin μ (hPm n) (hderP n) (hinj n)
  calc ∫⁻ x in A, ENNReal.ofReal |(f' x).det| ∂μ
      = ∫⁻ x in B, ENNReal.ofReal |(f' x).det| ∂μ := by
        rw [← lintegral_indicator hA, ← lintegral_indicator₀ hB]
        congr 1; ext x
        by_cases hx : x ∈ A
        · by_cases hd : (f' x).det = 0
          · simp [indicator, hx, hd, B]
          · simp [indicator, hx, hd, B]
        · have : x ∉ B := fun h => hx h.1
          simp [hx, this]
    _ = ∑' n, ∫⁻ x in P n, ENNReal.ofReal |(f' x).det| ∂μ := by
        rw [hBU]; exact lintegral_iUnion₀ hPm (fun m n hmn => (hPd hmn).aedisjoint) _
    _ = ∑' n, μ (f '' P n) := tsum_congr fun n =>
        lintegral_abs_det_fderiv_eq_addHaar_image₀ μ (hPm n) (hderP n) (hinj n)
    _ = ∑' n, ∫⁻ y, (f '' P n).indicator 1 y ∂μ :=
        tsum_congr fun n => (lintegral_indicator_one₀ (himg n)).symm
    _ = ∫⁻ y, ∑' n, (f '' P n).indicator 1 y ∂μ :=
        (lintegral_tsum fun n => aemeasurable_one.indicator₀ (himg n)).symm
    _ = ∫⁻ y, (({x ∈ A | f x = y}.encard : ℕ∞) : ℝ≥0∞) ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [measure_eq_zero_iff_ae_notMem.1 hZ] with y hy
        have hU : {x ∈ A | f x = y} = ⋃ n, {x ∈ P n | f x = y} := by
          ext x
          simp only [mem_ofPred_eq, mem_iUnion]
          constructor
          · rintro ⟨hxA, hxy⟩
            have hxB : x ∈ B := ⟨hxA, fun hd => hy ⟨x, ⟨hxA, hd⟩, hxy⟩⟩
            obtain ⟨n, hn⟩ := mem_iUnion.1 (hcov hxB)
            exact ⟨n, ⟨hxB, hn⟩, hxy⟩
          · rintro ⟨n, hxP, hxy⟩
            exact ⟨hPA n hxP, hxy⟩
        rw [hU, encard_iUnion_nat_eq_tsum _ (fun m n hmn => (hPd hmn).mono (sep_subset _ _)
          (sep_subset _ _))]
        refine tsum_congr fun n => ?_
        by_cases hyn : y ∈ f '' P n
        · obtain ⟨x, hx, rfl⟩ := hyn
          have hs : {z ∈ P n | f z = f x} = {x} := by
            ext z
            simp only [mem_ofPred_eq, mem_singleton_iff]
            exact ⟨fun h => hinj n h.1 hx h.2, fun h => by subst h; exact ⟨hx, rfl⟩⟩
          rw [hs, encard_singleton, indicator_of_mem (mem_image_of_mem f hx)]
          simp
        · have hs : {z ∈ P n | f z = y} = ∅ := by
            ext z
            simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
            exact fun hz e => hyn ⟨z, hz, e⟩
          rw [hs, encard_empty]
          simp [hyn]

theorem AreaMultiplicity.proof : AreaMultiplicity.Statement := by
  intro E F _ _ _ _ _ _ _ _ _ _ k hE hF A f f' hA hf'
  subst hE
  let φ : F ≃ₗᵢ[ℝ] E := (stdOrthonormalBasis ℝ F).equiv (stdOrthonormalBasis ℝ E) (finCongr hF)
  let g : E → E := fun x => φ (f x)
  let g' : E → E →L[ℝ] E := fun x => (φ.toContinuousLinearEquiv : F →L[ℝ] E).comp (f' x)
  have hg' : ∀ x ∈ A, HasFDerivWithinAt g (g' x) A x := fun x hx =>
    (φ.toContinuousLinearEquiv : F →L[ℝ] E).hasFDerivAt.comp_hasFDerivWithinAt x (hf' x hx)
  have hJ : ∀ x, ENNReal.ofReal (areaJacobian (f' x : E →ₗ[ℝ] F)) =
      ENNReal.ofReal |(g' x).det| := by
    intro x
    rw [areaJacobian_eq_abs_det_comp φ]
    rfl
  have hN : ∀ y, {x ∈ A | f x = y} = {x ∈ A | g x = φ y} := by
    intro y; ext x; simp [g]
  simp_rw [hJ, hN]
  rw [lintegral_abs_det_eq_lintegral_encard μH[(finrank ℝ E : ℝ)] hA hg']
  have hφ : MeasurePreserving φ (μH[(finrank ℝ E : ℝ)] : Measure F) μH[(finrank ℝ E : ℝ)] :=
    φ.toIsometryEquiv.measurePreserving_hausdorffMeasure _
  have hφe : MeasurableEmbedding φ := φ.toHomeomorph.measurableEmbedding
  exact (hφ.lintegral_comp_emb hφe (fun z => (({x ∈ A | g x = z}.encard : ℕ∞) : ℝ≥0∞))).symm

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PProperSheetedFibreEsymm
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Set Complex

open scoped Real

namespace ProperSheetedFibreEsymm


open Classical in
noncomputable def fibreEsymm {σ : Type} {d : ℕ} (Y : Set (σ → ℂ)) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ))
    (l : (σ → ℂ) →L[ℂ] ℂ) (j : ℕ) (t : Fin d → ℂ) : ℂ :=
  if h : {x | x ∈ Y ∧ A x = t}.Finite then (h.toFinset.val.map l).esymm j else 0

theorem fibreEsymm_eq {σ : Type} {d : ℕ} {Y : Set (σ → ℂ)} {A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)}
    {l : (σ → ℂ) →L[ℂ] ℂ} {j : ℕ} {t : Fin d → ℂ} (s : Finset (σ → ℂ))
    (hs : (↑s : Set (σ → ℂ)) = {x | x ∈ Y ∧ A x = t}) : fibreEsymm Y A l j t = (s.val.map l).esymm j := by
  have h : {x | x ∈ Y ∧ A x = t}.Finite := hs ▸ s.finite_toSet
  have hs' : h.toFinset = s := Finset.coe_injective (by rw [Set.Finite.coe_toFinset, hs])
  rw [fibreEsymm, dite_eq_left h, hs']

theorem fibre_sections {σ : Type} [Fintype σ] {Y : Set (σ → ℂ)} {d : ℕ} {A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)}
    {D : Set (Fin d → ℂ)} {δ : (Fin d → ℂ) → ℂ} (hD : IsOpen D)
    (hprop : ∀ K ⊆ D, IsCompact K → IsCompact {x | x ∈ Y ∧ A x ∈ K})
    (hchart : ∀ x ∈ Y, δ (A x) ≠ 0 → ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (g : (Fin d → ℂ) → σ → ℂ),
      IsOpen O ∧ IsOpen V ∧ x ∈ V ∧ AnalyticOnNhd ℂ g O ∧ (∀ y ∈ O, A (g y) = y) ∧ Y ∩ V = g '' O)
    {y : Fin d → ℂ} (hyD : y ∈ D) (hδy : δ y ≠ 0) :
    ∃ (F : Finset (σ → ℂ)) (g : (σ → ℂ) → (Fin d → ℂ) → σ → ℂ), (∀ x ∈ F, AnalyticAt ℂ (g x) y) ∧
      ∀ᶠ y' in 𝓝 y, Set.InjOn (fun x => g x y') ↑F ∧
        {x | x ∈ Y ∧ A x = y'} = (fun x => g x y') '' ↑F := by
  choose! O V g hO hV hxV hg hsec hYV using hchart

  have key : ∀ x ∈ Y, δ (A x) ≠ 0 → ∀ z ∈ Y, z ∈ V x → A z ∈ O x ∧ g x (A z) = z := by
    intro x hx hδ z hz hzV
    obtain ⟨w, hw, rfl⟩ : z ∈ g x '' O x := hYV x hx hδ ▸ ⟨hz, hzV⟩
    rw [hsec x hx hδ w hw]; exact ⟨hw, rfl⟩
  set F := {x | x ∈ Y ∧ A x = y} with hFdef
  have hFδ : ∀ x ∈ F, δ (A x) ≠ 0 := fun x hx => hx.2 ▸ hδy
  have hyO : ∀ x ∈ F, y ∈ O x := fun x hx => hx.2 ▸ (key x hx.1 (hFδ x hx) x hx.1 (hxV x hx.1 (hFδ x hx))).1
  have hgy : ∀ x ∈ F, g x y = x := fun x hx => hx.2 ▸ (key x hx.1 (hFδ x hx) x hx.1 (hxV x hx.1 (hFδ x hx))).2

  have hFc : IsCompact F := by
    simpa [hFdef] using hprop {y} (singleton_subset_iff.2 hyD) isCompact_singleton
  have hFfin : F.Finite := by
    obtain ⟨t, htF, hcov⟩ := hFc.elim_nhds_subcover V
      (fun x hx => (hV x hx.1 (hFδ x hx)).mem_nhds (hxV x hx.1 (hFδ x hx)))
    refine t.finite_toSet.subset fun z hz => ?_
    obtain ⟨x, hxt, hzx⟩ := mem_iUnion₂.1 (hcov hz)
    have hx := htF x hxt
    have := (key x hx.1 (hFδ x hx) z hz.1 hzx).2
    rw [hz.2, hgy x hx] at this
    exact this ▸ hxt
  refine ⟨hFfin.toFinset, g, fun x hx => ?_, ?_⟩
  · rw [Set.Finite.mem_toFinset] at hx
    exact hg x hx.1 (hFδ x hx) y (hyO x hx)
  rw [Set.Finite.coe_toFinset]

  have hev1 : ∀ᶠ y' in 𝓝 y, ∀ x ∈ F, y' ∈ O x :=
    (eventually_all_finite hFfin).2 fun x hx => (hO x hx.1 (hFδ x hx)).mem_nhds (hyO x hx)

  have hev2 : ∀ᶠ y' in 𝓝 y, ∀ p ∈ F ×ˢ F, p.1 ≠ p.2 → g p.1 y' ≠ g p.2 y' := by
    refine (eventually_all_finite (hFfin.prod hFfin)).2 fun p hp => ?_
    by_cases hne : p.1 = p.2
    · exact Eventually.of_forall fun _ h => absurd hne h
    have c1 := (hg p.1 hp.1.1 (hFδ _ hp.1) y (hyO _ hp.1)).continuousAt
    have c2 := (hg p.2 hp.2.1 (hFδ _ hp.2) y (hyO _ hp.2)).continuousAt
    have hne' : g p.1 y ≠ g p.2 y := by rwa [hgy _ hp.1, hgy _ hp.2]
    exact ((c1.tendsto.prodMk_nhds c2.tendsto).eventually
      (isClosed_diagonal.isOpen_compl.mem_nhds hne')).mono fun _ h _ => h

  have hev3 : ∀ᶠ y' in 𝓝 y, ∀ z ∈ Y, A z = y' → ∃ x ∈ F, z ∈ V x := by
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hD y hyD
    set K := Metric.closedBall y (ε / 2)
    have hKD : K ⊆ D := (Metric.closedBall_subset_ball (by linarith)).trans hball
    set W := ⋃ x ∈ F, V x
    have hW : IsOpen W := isOpen_biUnion fun x hx => hV x hx.1 (hFδ x hx)
    have hC : IsCompact ({z | z ∈ Y ∧ A z ∈ K} \ W) :=
      (hprop K hKD (isCompact_closedBall y _)).diff hW
    have hyn : y ∉ A '' ({z | z ∈ Y ∧ A z ∈ K} \ W) := by
      rintro ⟨z, ⟨⟨hzY, -⟩, hzW⟩, hzy⟩
      exact hzW (mem_iUnion₂.2 ⟨z, ⟨hzY, hzy⟩, hxV z hzY (hzy ▸ hδy)⟩)
    filter_upwards [Metric.closedBall_mem_nhds y (half_pos hε),
      (hC.image A.continuous).isClosed.isOpen_compl.mem_nhds hyn] with y' hy'K hy'C z hzY hzy
    by_contra hno
    exact hy'C ⟨z, ⟨⟨hzY, hzy ▸ hy'K⟩, fun h => hno (by simpa [W] using h)⟩, hzy⟩
  filter_upwards [hev1, hev2, hev3] with y' h1 h2 h3
  refine ⟨fun a ha b hb hab => ?_, ?_⟩
  · by_contra hne
    exact h2 (a, b) ⟨ha, hb⟩ hne hab
  ext z
  constructor
  · rintro ⟨hzY, hzy⟩
    obtain ⟨x, hx, hzx⟩ := h3 z hzY hzy
    exact ⟨x, hx, by simpa [hzy] using (key x hx.1 (hFδ x hx) z hzY hzx).2⟩
  · rintro ⟨x, hx, rfl⟩
    have hm : g x y' ∈ Y ∩ V x := hYV x hx.1 (hFδ x hx) ▸ mem_image_of_mem _ (h1 x hx)
    exact ⟨hm.1, hsec x hx.1 (hFδ x hx) y' (h1 x hx)⟩

theorem fibreEsymm_analyticAt {σ : Type} [Fintype σ] {Y : Set (σ → ℂ)} {d : ℕ}
    {A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)} {D : Set (Fin d → ℂ)} {δ : (Fin d → ℂ) → ℂ} (l : (σ → ℂ) →L[ℂ] ℂ) (j : ℕ)
    (hD : IsOpen D) (hprop : ∀ K ⊆ D, IsCompact K → IsCompact {x | x ∈ Y ∧ A x ∈ K})
    (hchart : ∀ x ∈ Y, δ (A x) ≠ 0 → ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (g : (Fin d → ℂ) → σ → ℂ),
      IsOpen O ∧ IsOpen V ∧ x ∈ V ∧ AnalyticOnNhd ℂ g O ∧ (∀ y ∈ O, A (g y) = y) ∧ Y ∩ V = g '' O)
    {y : Fin d → ℂ} (hyD : y ∈ D) (hδy : δ y ≠ 0) : AnalyticAt ℂ (fibreEsymm Y A l j) y := by
  classical
  obtain ⟨F, g, hga, hev⟩ := fibre_sections hD hprop hchart hyD hδy
  have hP : AnalyticAt ℂ (fun t => ∑ u ∈ F.powersetCard j, ∏ x ∈ u, l (g x t)) y :=
    Finset.analyticAt_fun_sum _ fun u hu => Finset.analyticAt_fun_prod _ fun x hx =>
      (l.analyticAt _).comp (hga x ((Finset.mem_powersetCard.1 hu).1 hx))
  refine hP.congr ?_
  filter_upwards [hev] with t ht
  rw [fibreEsymm_eq (F.image fun x => g x t) (by rw [Finset.coe_image, ht.2]),
    Finset.image_val_of_injOn ht.1, Multiset.map_map, Finset.esymm_map_val]
  rfl

theorem norm_esymm_map_le {ι : Type*} (S : Finset ι) (f : ι → ℂ) (j : ℕ) {C : ℝ} (hC : ∀ x ∈ S, ‖f x‖ ≤ C) :
    ‖(S.val.map f).esymm j‖ ≤ (S.card.choose j : ℝ) * C ^ j := by
  rw [Finset.esymm_map_val]
  calc ‖∑ u ∈ S.powersetCard j, ∏ x ∈ u, f x‖ ≤ ∑ u ∈ S.powersetCard j, ‖∏ x ∈ u, f x‖ := norm_sum_le _ _
    _ ≤ ∑ u ∈ S.powersetCard j, C ^ j := by
        refine Finset.sum_le_sum fun u hu => ?_
        obtain ⟨hu1, hu2⟩ := Finset.mem_powersetCard.1 hu
        rw [norm_prod, ← hu2, ← Finset.prod_const]
        exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun x hx => hC x (hu1 hx)
    _ = _ := by rw [Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul]

theorem fibreEsymm_locally_bounded (hcount : UnbranchedProperCountConstant.Statement) {σ : Type} [Fintype σ]
    {Y : Set (σ → ℂ)} {d : ℕ} {A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)} {D : Set (Fin d → ℂ)} {δ : (Fin d → ℂ) → ℂ}
    (l : (σ → ℂ) →L[ℂ] ℂ) (j : ℕ) (hD : IsOpen D)
    (hprop : ∀ K ⊆ D, IsCompact K → IsCompact {x | x ∈ Y ∧ A x ∈ K}) (hδ : AnalyticOnNhd ℂ δ D)
    (hchart : ∀ x ∈ Y, δ (A x) ≠ 0 → ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (g : (Fin d → ℂ) → σ → ℂ),
      IsOpen O ∧ IsOpen V ∧ x ∈ V ∧ AnalyticOnNhd ℂ g O ∧ (∀ y ∈ O, A (g y) = y) ∧ Y ∩ V = g '' O)
    {τ : Fin d → ℂ} (hτ : τ ∈ D) :
    ∃ N ∈ 𝓝 τ, Bornology.IsBounded (fibreEsymm Y A l j '' (N ∩ D ∩ {t | δ t ≠ 0})) := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hD τ hτ
  set B := Metric.ball τ (ε / 2)
  have hKD : Metric.closedBall τ (ε / 2) ⊆ D := (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hBD : B ⊆ D := Metric.ball_subset_closedBall.trans hKD

  obtain ⟨n, hn⟩ := hcount σ (Y ∩ A ⁻¹' B) d A B δ Metric.isOpen_ball (convex_ball τ _).isPreconnected
    (fun x hx => hx.2) (fun K hK hKc => by
      convert hprop K (hK.trans hBD) hKc using 1
      ext x; exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hK h.2⟩, h.2⟩⟩) (hδ.mono hBD) (by
      intro x hx hδx
      obtain ⟨O, V, g, hO, hV, hxV, hg, hsec, hYV⟩ := hchart x hx.1 hδx
      refine ⟨O ∩ B, V, g, hO.inter Metric.isOpen_ball, hV, hxV, hg.continuousOn.mono inter_subset_left,
        fun y hy => hsec y hy.1, ?_⟩
      ext z
      constructor
      · rintro ⟨⟨hzY, hzB⟩, hzV⟩
        obtain ⟨w, hw, rfl⟩ : z ∈ g '' O := hYV ▸ ⟨hzY, hzV⟩
        refine ⟨w, ⟨hw, ?_⟩, rfl⟩
        have : A (g w) ∈ B := hzB
        rwa [hsec w hw] at this
      · rintro ⟨w, ⟨hw, hwB⟩, rfl⟩
        have hm : g w ∈ Y ∩ V := hYV ▸ mem_image_of_mem g hw
        refine ⟨⟨hm.1, ?_⟩, hm.2⟩
        show A (g w) ∈ B
        rwa [hsec w hw])

  obtain ⟨C, hC⟩ := (hprop _ hKD (isCompact_closedBall τ _)).exists_bound_of_continuousOn
    l.continuous.continuousOn
  refine ⟨B, Metric.ball_mem_nhds τ (half_pos hε), (Metric.isBounded_iff_subset_closedBall 0).2
    ⟨(n.choose j : ℝ) * C ^ j, ?_⟩⟩
  rintro _ ⟨t, ⟨⟨htB, -⟩, htδ⟩, rfl⟩
  have hfib : {x | x ∈ Y ∩ A ⁻¹' B ∧ A x = t} = {x | x ∈ Y ∧ A x = t} := by
    ext x; exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, show A x ∈ B from h.2 ▸ htB⟩, h.2⟩⟩
  have hcard := hn t htB htδ
  rw [hfib] at hcard
  have hfin : {x | x ∈ Y ∧ A x = t}.Finite := Set.finite_of_encard_eq_coe hcard
  rw [hfin.encard_eq_coe_toFinset_card, Nat.cast_inj] at hcard
  rw [Metric.mem_closedBall, dist_zero_right, fibreEsymm_eq hfin.toFinset hfin.coe_toFinset, ← hcard]
  refine norm_esymm_map_le _ _ _ fun x hx => hC x ?_
  rw [Set.Finite.mem_toFinset] at hx
  exact ⟨hx.1, hx.2 ▸ Metric.ball_subset_closedBall htB⟩

theorem analyticOnNhd_of_differentiableOn (hcirc : ParametricCircleIntegralAnalytic.Statement) {k : ℕ}
    {U : Set (Fin k → ℂ)} {F : (Fin k → ℂ) → ℂ} (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) :
    AnalyticOnNhd ℂ F U := by
  have h := hcirc (Fin k) (fun p => F p.1 * p.2⁻¹) (U ×ˢ {s | s ≠ 0}) U 0 1 zero_le_one
    (hU.prod isOpen_ne) hU
    ((hF.fun_comp differentiable_fst.differentiableOn mapsTo_fst_prod).mul
      (differentiable_snd.differentiableOn.inv fun _ hp => (mem_prod.1 hp).2))
    (fun x hx s hs => ⟨hx, by rintro rfl; simp at hs⟩)
  have hinv : (∮ z in C(0, 1), z⁻¹) = 2 * π * I := by
    simpa using circleIntegral.integral_sub_inv_of_mem_ball (c := 0) (w := 0) (R := 1) (by simp)
  intro x hx
  refine ((h x hx).mul (analyticAt_const (v := (2 * π * I)⁻¹))).congr (Eventually.of_forall fun y => ?_)
  have h2 : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  simp only [Pi.mul_apply, circleIntegral.integral_const_mul, hinv]
  field_simp

end ProperSheetedFibreEsymm


open ProperSheetedFibreEsymm in
theorem ProperSheetedFibreEsymm.proof (hcount : UnbranchedProperCountConstant.Statement)
    (hriem : RiemannExtensionAnalytic.Statement) (hcirc : ParametricCircleIntegralAnalytic.Statement) :
    ProperSheetedFibreEsymm.Statement := by
  intro σ _ Y d A D δ l j hD _ hprop hδ hW hchart
  obtain ⟨F, hFd, hFeq⟩ := hriem d D δ (fibreEsymm Y A l j) hD hδ.differentiableOn hW
    (fun t ht => (fibreEsymm_analyticAt l j hD hprop hchart ht.1 ht.2).differentiableAt.differentiableWithinAt)
    (fun τ hτ => fibreEsymm_locally_bounded hcount l j hD hprop hδ hchart hτ)
  refine ⟨F, analyticOnNhd_of_differentiableOn hcirc hD hFd, fun t ht hδt s hs => ?_⟩
  rw [hFeq ⟨ht, hδt⟩, fibreEsymm_eq s hs]

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PAnalyticSimpleRootBranch
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Filter Topology
open scoped ContDiff

noncomputable section

theorem AnalyticSimpleRootBranch.proof : AnalyticSimpleRootBranch.Statement := by
  intro d N a y τ ha hroot hder
  set p : Polynomial ℂ := Polynomial.X ^ N + ∑ j, Polynomial.C (a j y) * Polynomial.X ^ (j : ℕ) with hp
  set F : (Fin d → ℂ) × ℂ → ℂ := fun v => v.2 ^ N + ∑ j, a j v.1 * v.2 ^ (j : ℕ) with hF
  have hFa : AnalyticAt ℂ F (y, τ) := by
    refine (analyticAt_snd.pow N).add (Finset.analyticAt_fun_sum _ fun j _ => ?_)
    exact ((ha j).comp (analyticAt_fst (p := (y, τ)))).mul (analyticAt_snd.pow _)
  have hcd : ContDiffAt ℂ ω F (y, τ) := hFa.contDiffAt
  have hpe : ∀ s, p.eval s = F (y, s) := by
    intro s
    simp [hp, hF, Polynomial.eval_finsetSum]

  have hpart : fderiv ℂ F (y, τ) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ =
      (1 : ℂ →L[ℂ] ℂ).smulRight (p.derivative.eval τ) := by
    have h1 : HasFDerivAt (fun s : ℂ => F (y, s))
        (fderiv ℂ F (y, τ) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ) τ :=
      (hFa.differentiableAt.hasFDerivAt).comp τ ((hasFDerivAt_const y τ).prodMk (hasFDerivAt_id τ))
    have h2 : (fun s : ℂ => F (y, s)) = fun s => p.eval s := funext fun s => (hpe s).symm
    rw [h2] at h1
    exact h1.unique (p.hasDerivAt τ).hasFDerivAt
  have hinv : (fderiv ℂ F (y, τ) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ).IsInvertible := by
    rw [hpart]
    refine ⟨ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 _ hder), ?_⟩
    ext; simp
  have hω : (ω : WithTop ℕ∞) ≠ 0 := by simp
  set ψ := hcd.implicitFunction hω hinv with hψdef
  have hψy : ψ y = τ := hcd.implicitFunction_apply_self hω hinv
  have hψa : AnalyticAt ℂ ψ y := (hcd.contDiffAt_implicitFunction hω hinv).analyticAt
  have hF0 : F (y, τ) = 0 := hroot
  obtain ⟨U₁, B, hU₁o, hyU₁, hBo, hτB, hsub⟩ :=
    mem_nhds_prod_iff'.mp (hcd.eventually_apply_eq_iff_implicitFunction hω hinv)
  set W : Set (Fin d → ℂ) := U₁ ∩ {x | AnalyticAt ℂ ψ x} with hW
  have hWo : IsOpen W := hU₁o.inter (isOpen_analyticAt ℂ ψ)
  have hWc : ContinuousOn ψ W := fun x hx => hx.2.continuousAt.continuousWithinAt
  refine ⟨W ∩ ψ ⁻¹' B, B, ψ, hWc.isOpen_inter_preimage hWo hBo, ⟨⟨hyU₁, hψa⟩, by simpa [hψy] using hτB⟩,
    hBo, hτB, fun x hx => hx.1.2, hψy, fun y' hy' => ⟨hy'.2, fun s hs => ?_⟩⟩
  have h := hsub (Set.mk_mem_prod hy'.1.1 hs)
  simp only [Set.mem_ofPred_eq] at h
  change F (y', s) = 0 ↔ s = ψ y'
  rw [← hF0, h]
  exact eq_comm

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPrimitiveFormRemainder
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Polynomial

def PrimitiveFormRemainder.analyticSubring (d : ℕ) (y₀ : Fin d → ℂ) : Subring ((Fin d → ℂ) → ℂ) where
  carrier := {g | AnalyticAt ℂ g y₀}
  mul_mem' ha hb := ha.mul hb
  one_mem' := analyticAt_const
  add_mem' ha hb := ha.add hb
  zero_mem' := analyticAt_const
  neg_mem' ha := ha.neg

theorem PrimitiveFormRemainder.proof (hSWD : SeparateWeierstrassDivision.Statement) :
    PrimitiveFormRemainder.Statement := by
  classical
  intro σ _ w d A ℓ N δ q n c f hδ hq hc hW hf
  obtain ⟨v, r, -, hr, hev⟩ := hSWD σ d (A w) w n c (fun x => f x.2) hc hW
    (hf.comp (analyticAt_snd (p := (A w, w))))
  set S := PrimitiveFormRemainder.analyticSubring d (A w)

  let s : ((i : σ) → Fin (n i)) → ℕ := fun α => ∑ i, (α i : ℕ)
  let M : ℕ := ∑ i, n i
  have hsM : ∀ α, s α ≤ M := fun α => Finset.sum_le_sum fun i _ => (α i).isLt.le
  let Q : σ → Polynomial ((Fin d → ℂ) → ℂ) := fun i => ∑ j, C (q i j) * X ^ (j : ℕ)
  let R : Polynomial ((Fin d → ℂ) → ℂ) :=
    ∑ α, C (r α * δ ^ (M - s α)) * ∏ i, Q i ^ (α i : ℕ)
  refine ⟨M, R, ?_, ?_⟩
  ·
    have hC : ∀ g : (Fin d → ℂ) → ℂ, AnalyticAt ℂ g (A w) → C g ∈ lifts S.subtype := fun g hg =>
      C_mem_lifts S.subtype ⟨g, hg⟩
    have hR : R ∈ lifts S.subtype := by
      refine Subsemiring.sum_mem _ fun α _ => Subsemiring.mul_mem _ (hC _ ((hr α).mul (hδ.pow _)))
        (Subsemiring.prod_mem _ fun i _ => Subsemiring.pow_mem _ ?_ _)
      exact Subsemiring.sum_mem _ fun j _ =>
        Subsemiring.mul_mem _ (hC _ (hq i j)) (X_pow_mem_lifts _ _)
    intro k
    obtain ⟨g, hg⟩ := (lifts_iff_coeff_lifts R).1 hR k
    rw [← hg]
    exact g.2
  ·
    have hcont : Continuous fun z : σ → ℂ => (A z, z) := A.continuous.prodMk continuous_id
    filter_upwards [(hcont.tendsto w).eventually hev] with z hz hWz hqz
    have hf' : f z = ∑ α, r α (A z) * ∏ i, z i ^ (α i : ℕ) := by
      rw [hz]; simp [hWz]
    have hQ : ∀ i, (Q i).eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ => ℂ) (A z)) (ℓ z) = δ (A z) * z i := by
      intro i
      simp [Q, eval₂_finsetSum, hqz i]
    simp only [R, eval₂_finsetSum, eval₂_mul, eval₂_C, eval₂_finsetProd, eval₂_pow, hQ, hf', Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    simp only [Pi.evalRingHom_apply, Pi.mul_apply, Pi.pow_apply, mul_pow, Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum]
    rw [← pow_mul_pow_sub (δ (A z)) (hsM α)]
    ring

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end
