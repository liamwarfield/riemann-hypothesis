module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ProjLaws

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ResCob
open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.resCob :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (F : Flow H) (k : H), F.Cob (k - F.av wR k) ∧
      ∫ t in Iic (0 : ℝ), Real.exp t * ‖F.U t k - k‖ ^ 2 = 2 * ‖k‖ ^ 2 - 2 * (⟪k, F.av wR k⟫_ℂ).re := by
  intro H _ _ _ F k
  have hw := (avSpec F).2.1
  have sp := fun h => ((avSpec F).2.2.2 _ hw).1 h
  have cg : Continuous fun r : ℝ => (Real.exp r : ℂ) • F.U r k := by
    have := F.cont k
    fun_prop
  have ig : ∀ t, IntegrableOn (fun r : ℝ => (Real.exp r : ℂ) • F.U r k) (Iic t) := fun t =>
    Integrable.mono' ((integrableOn_exp_Iic t).mul_const ‖k‖) cg.aestronglyMeasurable
      (Eventually.of_forall fun r => by simp [norm_smul, F.norm])
  have R0 : ∀ h, F.av wR h = ∫ r in Iic (0 : ℝ), (Real.exp r : ℂ) • F.U r h := fun h => by
    rw [(sp h).2, ← integral_indicator measurableSet_Iic]
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    by_cases hr : r ∈ Iic (0 : ℝ) <;> simp [wR, hr]
  constructor
  · set c := F.av wR k with hc
    have Ut : ∀ t, F.U t c = (Real.exp (-t) : ℂ) • (c + ∫ r in (0 : ℝ)..t, (Real.exp r : ℂ) • F.U r k) := fun t => by
      rw [hc, R0, ← intervalIntegral.integral_Iic_sub_Iic (ig 0) (ig t), add_sub_cancel,
        ← (F.U t).integral_comp_comm (ig 0), ← integral_smul, ← integral_indicator measurableSet_Iic,
        ← integral_indicator measurableSet_Iic, ← integral_add_right_eq_self _ (-t)]
      refine integral_congr_ae (Eventually.of_forall fun r => ?_)
      by_cases hr : r ≤ t
      · simp only [indicator_of_mem (show r + -t ∈ Iic (0 : ℝ) by simpa using hr), indicator_of_mem (show r ∈ Iic t from hr),
          map_smul, ← F.add, smul_smul, ← Complex.ofReal_mul, ← Real.exp_add]
        congr 3 <;> ring
      · simp only [indicator_of_notMem (show r + -t ∉ Iic (0 : ℝ) by simpa using hr), indicator_of_notMem (show r ∉ Iic t from hr)]
    have der : ∀ t, HasDerivAt (fun t => F.U t c) (F.U t (k - c)) t := fun t => by
      have d1 : HasDerivAt (fun t : ℝ => (Real.exp (-t) : ℂ)) (-(Real.exp (-t) : ℂ)) t := by
        simpa using ((hasDerivAt_neg t).exp).ofReal_comp
      have d2 := (cg.integral_hasStrictDerivAt 0 t).hasDerivAt.const_add c
      have d3 := d1.smul d2
      refine (d3.congr_of_eventuallyEq (Eventually.of_forall Ut)).congr_deriv ?_
      symm
      rw [map_sub, Ut, smul_smul, ← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, Complex.ofReal_one,
        one_smul, neg_smul, sub_eq_add_neg]
    refine ⟨c, fun t => ?_⟩
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => der s) ((F.cont _).intervalIntegrable _ _), F.zero]
  · have i1 : IntegrableOn (fun r : ℝ => ⟪k, (Real.exp r : ℂ) • F.U r k⟫_ℂ) (Iic 0) := (ig 0).const_inner k
    rw [R0, ← integral_inner (ig 0), ← RCLike.re_to_complex, ← integral_re i1, ← integral_const_mul]
    have e : 2 * ‖k‖ ^ 2 = ∫ t in Iic (0 : ℝ), Real.exp t * (2 * ‖k‖ ^ 2) := by
      rw [integral_mul_const, integral_exp_Iic_zero, one_mul]
    rw [e, ← integral_sub ((integrableOn_exp_Iic 0).mul_const _) (i1.re.const_mul 2)]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [norm_sub_rev (F.U t k) k, @norm_sub_sq ℂ, F.norm, inner_smul_right, RCLike.re_to_complex, Complex.re_ofReal_mul]
    ring
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ResInv
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ResBelow
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ConvNear
open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

private theorem ker_bd {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    {κ : ℝ → V →L[ℂ] W} (h : HasCompactSupport κ) : ∃ R : ℝ, 0 ≤ R ∧ ∀ t, R < |t| → κ t = 0 := by
  obtain ⟨R, hR⟩ := h.isCompact.isBounded.exists_norm_le
  refine ⟨|R|, abs_nonneg _, fun t ht => image_eq_zero_of_notMem_tsupport fun hm => ?_⟩
  exact absurd ((hR t hm).trans (le_abs_self R)) (not_le.2 ht)

theorem UpperTheory.V.Z.IntegralApplyAeEq.convNear :
    ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] (β : ℝ → V →L[ℂ] V), Ker β → ∃ C : ℝ, ∀ u : L V,
      ‖conv β u - (symb β 0).compLpL 2 volume u‖ ^ 2 ≤ C * ∫ t in Iic (0 : ℝ), Real.exp t * ‖sh V t u - u‖ ^ 2 := by
  intro V _ _ _ _ β hk
  obtain ⟨R, hR0, hR⟩ := ker_bd hk.2
  have hk1 : Integrable β := hk.1.integrable_of_hasCompactSupport hk.2
  obtain ⟨B, hB⟩ := hk.1.bounded_above_of_compact_support hk.2
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  let c : (V →L[ℂ] V) →L[ℂ] (L V →L[ℂ] L V) := LinearMap.mkContinuous
    { toFun := fun A => A.compLpL 2 volume
      map_add' := fun A B => ContinuousLinearMap.add_compLpL A B
      map_smul' := fun a A => ContinuousLinearMap.smul_compLpL a A } 1 fun A => by
      rw [one_mul]; exact ContinuousLinearMap.norm_compLpL_le A
  refine ⟨(2 * B) ^ 2 * (R * Real.exp R), fun u => ?_⟩
  set d : ℝ → ℝ := fun t => ‖sh V t u - u‖ with hd
  have dc : Continuous d := (((shF V).cont u).sub continuous_const).norm
  have dn : ∀ t, d (-t) = d t := fun t => by
    show ‖(shF V).U (-t) u - u‖ = ‖(shF V).U t u - u‖
    rw [← (shF V).norm t, map_sub, ← (shF V).add, add_neg_cancel, (shF V).zero, norm_sub_rev]
  have d2 : ∀ t, d t ≤ 2 * ‖u‖ := fun t => (norm_sub_le _ _).trans_eq (by
    rw [show ‖sh V t u‖ = ‖u‖ from (shF V).norm t u]; ring)
  have i2 : Integrable fun t => c (β t) u := (c.integrable_comp hk1).apply_continuousLinearMap u
  have e1 : (symb β 0).compLpL 2 volume u = ∫ t, c (β t) u := by
    rw [symb]
    simp only [zero_mul, Complex.exp_zero, one_smul]
    rw [← ContinuousLinearMap.integral_apply (c.integrable_comp hk1), c.integral_comp_comm hk1]
    rfl
  have e2 : ‖conv β u - (symb β 0).compLpL 2 volume u‖ ≤ 2 * B * ∫ t in (-R)..0, d t := by
    rw [(convSpec β hk u).2.2, e1, ← integral_sub (convSpec β hk u).2.1 i2]
    have hb : Integrable ((Icc (-R) R).indicator fun t => B * d t) :=
      (integrable_indicator_iff measurableSet_Icc).2 ((dc.const_mul B).integrableOn_Icc)
    refine (norm_integral_le_of_norm_le hb (Eventually.of_forall fun t => ?_)).trans_eq ?_
    · by_cases h : t ∈ Icc (-R) R
      · rw [indicator_of_mem h]
        show ‖c (β t) (sh V t u) - c (β t) u‖ ≤ _
        rw [← map_sub]
        refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
        gcongr
        exact (ContinuousLinearMap.norm_compLpL_le _).trans (hB t)
      · rw [indicator_of_notMem h]
        show ‖c (β t) (sh V t u) - c (β t) u‖ ≤ _
        rw [hR t (not_le.1 fun h' => h (abs_le.1 h')), map_zero]
        simp
    · rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_add_adjacent_intervals (dc.intervalIntegrable (-R) 0) (dc.intervalIntegrable 0 R)]
      have : ∫ t in (0 : ℝ)..R, d t = ∫ t in (-R)..0, d t := by
        rw [← neg_zero, ← intervalIntegral.integral_comp_neg, neg_zero]
        simp only [dn]
      rw [this]; ring
  have e3 : (∫ t in (-R)..0, d t) ^ 2 ≤ R * ∫ t in (-R)..0, d t ^ 2 := by
    set m := ∫ t in (-R)..0, d t with hm
    rcases hR0.eq_or_lt with rfl | hp
    · simp [hm]
    have h0 : 0 ≤ ∫ t in (-R)..0, (R * d t - m) ^ 2 := intervalIntegral.integral_nonneg (by linarith) fun _ _ => sq_nonneg _
    have h1 : ∫ t in (-R)..0, (R * d t - m) ^ 2 = R ^ 2 * (∫ t in (-R)..0, d t ^ 2) - 2 * R * m * m + R * m ^ 2 := by
      have : ∀ t, (R * d t - m) ^ 2 = R ^ 2 * d t ^ 2 - 2 * R * m * d t + m ^ 2 := fun t => by ring
      simp only [this]
      rw [intervalIntegral.integral_add, intervalIntegral.integral_sub, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
      · simp [hm]
      all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _
    rw [h1] at h0
    nlinarith
  have iw : IntegrableOn (fun t => Real.exp t * d t ^ 2) (Iic 0) := by
    refine ((integrableOn_exp_Iic 0).mul_const ((2 * ‖u‖) ^ 2)).mono' (by fun_prop) (Eventually.of_forall fun t => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    gcongr
    exact d2 t
  have e4 : ∫ t in (-R)..0, d t ^ 2 ≤ Real.exp R * ∫ t in Iic (0 : ℝ), Real.exp t * d t ^ 2 := by
    rw [intervalIntegral.integral_of_le (by linarith), ← integral_const_mul]
    refine (setIntegral_mono_on (g := fun t => Real.exp R * (Real.exp t * d t ^ 2)) (dc.pow 2).integrableOn_Ioc
      (Continuous.integrableOn_Ioc (by fun_prop)) measurableSet_Ioc fun t ht => ?_).trans
      (setIntegral_mono_set (iw.const_mul _) (Eventually.of_forall fun t => by positivity) (Eventually.of_forall fun _ ht => Ioc_subset_Iic_self ht))
    rw [← mul_assoc, ← Real.exp_add]
    exact le_mul_of_one_le_left (sq_nonneg _) (Real.one_le_exp (by linarith [ht.1]))
  calc _ ≤ (2 * B * ∫ t in (-R)..0, d t) ^ 2 := by gcongr
    _ = (2 * B) ^ 2 * (∫ t in (-R)..0, d t) ^ 2 := by ring
    _ ≤ (2 * B) ^ 2 * (R * (Real.exp R * ∫ t in Iic (0 : ℝ), Real.exp t * d t ^ 2)) := by
      gcongr
      exact e3.trans (by gcongr)
    _ = _ := by ring
end

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

private theorem side {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (M : Sc H V W)
    (B : H →L[ℂ] H) (β : ℝ → V →L[ℂ] V) (k : Ker β) (hB : ∀ u, B (M.J u) = M.J (conv β u)) (f : ℕ → H)
    (q0 : Tendsto (fun n => ∫ t in Iic (0 : ℝ), Real.exp t * ‖M.F.U t (f n) - f n‖ ^ 2) atTop (𝓝 0))
    (p : Tendsto (fun n => M.P (Ioi M.T₀) (f n)) atTop (𝓝 0)) :
    Tendsto (fun n => B (f n) - M.J ((symb β 0).compLpL 2 volume (M.J.symm (f n)))) atTop (𝓝 0) ∧
      Tendsto (fun n => M.P (Ioi M.T₀) (B (f n))) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := convNear β k
  have a : Tendsto (fun n => B (f n) - M.J ((symb β 0).compLpL 2 volume (M.J.symm (f n)))) atTop (𝓝 0) := by
    have := (q0.const_mul C).sqrt
    rw [mul_zero, Real.sqrt_zero] at this
    refine squeeze_zero_norm (fun n => Real.le_sqrt_of_sq_le ?_) this
    obtain ⟨u, hu⟩ := M.J.surjective (f n)
    simp only [← hu, hB, M.J.symm_apply_apply, M.hJ, ← map_sub, M.J.norm_map]
    exact hC u
  refine ⟨a, ?_⟩
  let G : H →L[ℂ] H := (M.J.toContinuousLinearEquiv : L V →L[ℂ] H) ∘L (symb β 0).compLpL 2 volume ∘L
    (M.J.symm.toContinuousLinearEquiv : H →L[ℂ] L V)
  have := (((M.P (Ioi M.T₀)).continuous.tendsto 0).comp a).add ((G.continuous.tendsto 0).comp p)
  simp only [map_zero, add_zero] at this
  refine this.congr fun n => ?_
  have e : G (M.P (Ioi M.T₀) (f n)) = M.P (Ioi M.T₀) (M.J ((symb β 0).compLpL 2 volume (M.J.symm (f n)))) := by
    show M.J ((symb β 0).compLpL 2 volume (M.J.symm (M.J (cut V _ _)))) = M.J (cut V _ (M.J.symm (M.J _)))
    rw [M.J.symm_apply_apply, M.J.symm_apply_apply]
    refine congrArg M.J (Lp.ext ?_)
    filter_upwards [(symb β 0).coeFn_compLpL (cut V (Ioi M.T₀) (M.J.symm (f n))), (symb β 0).coeFn_compLpL (M.J.symm (f n)),
      cutSpec (Ioi M.T₀) measurableSet_Ioi (M.J.symm (f n)),
      cutSpec (Ioi M.T₀) measurableSet_Ioi ((symb β 0).compLpL 2 volume (M.J.symm (f n)))] with x h1 h2 h3 h4
    erw [h1, h3, h4]
    by_cases hx : x ∈ Ioi M.T₀
    · rw [indicator_of_mem hx, indicator_of_mem hx, h2]
    · rw [indicator_of_notMem hx, indicator_of_notMem hx, map_zero]
  simp only [Function.comp_apply, map_sub, e, sub_add_cancel]

theorem UpperTheory.V.Z.IntegralApplyAeEq.resBelow :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (M : Sc H V W) (B : H →L[ℂ] H) (β : ℝ → V →L[ℂ] V) (β' : ℝ → W →L[ℂ] W), Ker β → Ker β' → IsUnit (symb β 0) → IsUnit (symb β' 0) → M.Acts B β β' → IsCompactOperator (M.abelian₂ M.T₀ M.T₀ ∘L B ∘L M.abelian₂ M.T₀ M.T₀) →
      ∀ f : ℕ → H, (∀ n, ‖f n‖ = 1) → Tendsto (fun n => M.abelian₂ M.T₀ M.T₀ (f n) - f n) atTop (𝓝 0) →
        Tendsto (fun n => (⟪f n, M.F.av wR (f n)⟫_ℂ).re) atTop (𝓝 1) → False := by
  intro H _ _ _ V _ _ _ _ W _ _ _ _ M B β β' k1 k2 u1 u2 ha hc f hf t1 t2
  set Λ := M.abelian₂ M.T₀ M.T₀ with hΛ
  obtain ⟨-, -, -, -, -, -, l2, -, l4⟩ := (projLaws M).2.2.2.2.2.2.2 M.T₀ M.T₀ (by linarith)
  let q : H → ℝ := fun h => ∫ t in Iic (0 : ℝ), Real.exp t * ‖M.F.U t h - h‖ ^ 2
  have q0 : Tendsto (fun n => q (f n)) atTop (𝓝 0) := by
    have := (tendsto_const_nhds (x := (2 : ℝ))).sub (t2.const_mul 2)
    simp only [mul_one, sub_self] at this
    exact this.congr fun n => by simp only [q, (resCob M.F _).2, hf]; ring
  have p1 : Tendsto (fun n => M.P (Ioi M.T₀) (f n)) atTop (𝓝 0) := by
    have := (((M.P (Ioi M.T₀)).continuous.tendsto 0).comp t1).neg
    simp only [map_zero, neg_zero] at this
    exact this.congr fun n => by
      have l : M.P (Ioi M.T₀) (Λ (f n)) = 0 := DFunLike.congr_fun l2 _
      simp [l]
  have p2 : Tendsto (fun n => M.P' (Ioi M.T₀) (f n)) atTop (𝓝 0) := by
    have := (((M.P' (Ioi M.T₀)).continuous.tendsto 0).comp t1).neg
    simp only [map_zero, neg_zero] at this
    exact this.congr fun n => by
      have l : M.P' (Ioi M.T₀) (Λ (f n)) = 0 := DFunLike.congr_fun l4 _
      simp [l]
  obtain ⟨a1, a2⟩ := side M B β k1 ha.1 f q0 p1
  obtain ⟨-, a3⟩ := side M.swap B β' k2 ha.2 f (q0.congr fun n => by
    refine setIntegral_congr_fun measurableSet_Iic fun t _ => ?_
    show _ = Real.exp t * ‖M.F.U (-t) (f n) - f n‖ ^ 2
    rw [← M.F.norm t (M.F.U (-t) (f n) - f n), map_sub, ← M.F.add, add_neg_cancel, M.F.zero, norm_sub_rev]) p2
  have a4 : Tendsto (fun n => B (f n) - (Λ ∘L B ∘L Λ) (f n)) atTop (𝓝 0) := by
    have := (a2.add a3).sub (((Λ ∘L B).continuous.tendsto 0).comp t1)
    simp only [map_zero, add_zero, sub_zero] at this
    refine this.congr fun n => ?_
    have e : Λ (B (f n)) = B (f n) - M.P (Ioi M.T₀) (B (f n)) - M.swap.P (Ioi M.swap.T₀) (B (f n)) := rfl
    simp only [Function.comp_apply, ContinuousLinearMap.comp_apply, map_sub, e]
    abel
  obtain ⟨S, hS, hsub⟩ := hc.image_closedBall_subset_compact 1
  obtain ⟨y, -, φ, hφ, hy⟩ := hS.tendsto_subseq fun n => hsub ⟨f n, by simp [hf], rfl⟩
  obtain ⟨s, hs⟩ := u1
  let G : H →L[ℂ] H := (M.J.toContinuousLinearEquiv : L V →L[ℂ] H) ∘L ((s⁻¹ : (V →L[ℂ] V)ˣ) : V →L[ℂ] V).compLpL 2 volume ∘L
    (M.J.symm.toContinuousLinearEquiv : H →L[ℂ] L V)
  have hG : ∀ h, G (M.J ((symb β 0).compLpL 2 volume (M.J.symm h))) = h := fun h => by
    show M.J (((s⁻¹ : (V →L[ℂ] V)ˣ) : V →L[ℂ] V).compLpL 2 volume (M.J.symm (M.J _))) = h
    rw [M.J.symm_apply_apply, ← M.J.eq_symm_apply]
    refine Lp.ext ?_
    filter_upwards [((s⁻¹ : (V →L[ℂ] V)ˣ) : V →L[ℂ] V).coeFn_compLpL ((symb β 0).compLpL 2 volume (M.J.symm h)),
      (symb β 0).coeFn_compLpL (M.J.symm h)] with x h1 h2
    rw [h1, h2, ← hs]
    exact DFunLike.congr_fun s.inv_mul _
  have c1 : Tendsto (fun n => f (φ n)) atTop (𝓝 (G y)) := by
    have := (G.continuous.tendsto _).comp ((hy.add (a4.comp hφ.tendsto_atTop)).sub (a1.comp hφ.tendsto_atTop))
    simp only [add_zero, sub_zero] at this
    refine this.congr fun n => ?_
    simp only [Function.comp_apply, ContinuousLinearMap.coe_coe, add_sub_cancel, sub_sub_cancel, hG]
  set g := G y
  have g1 : ‖g‖ = 1 := tendsto_nhds_unique c1.norm (by simp [hf])
  have qc : Continuous q := by
    simp only [q, (resCob M.F _).2]
    fun_prop
  have g2 : q g = 0 := tendsto_nhds_unique ((qc.tendsto g).comp c1) (q0.comp hφ.tendsto_atTop)
  have cg : Continuous fun t => Real.exp t * ‖M.F.U t g - g‖ ^ 2 := by
    have := M.F.cont g
    fun_prop
  have ig : IntegrableOn (fun t => Real.exp t * ‖M.F.U t g - g‖ ^ 2) (Iic 0) := by
    refine Integrable.mono' ((integrableOn_exp_Iic 0).mul_const 4) cg.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    have : ‖M.F.U t g - g‖ ≤ 2 := (norm_sub_le _ _).trans_eq (by rw [M.F.norm, g1]; norm_num)
    gcongr
    nlinarith [norm_nonneg (M.F.U t g - g)]
  have g3 := (setIntegral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall fun t => by positivity) ig).1 g2
  have g4 : EqOn (fun t => Real.exp t * ‖M.F.U t g - g‖ ^ 2) 0 (Iio 0) :=
    Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae_restrict_of_subset Iio_subset_Iic_self g3) isOpen_Iio cg.continuousOn
      continuousOn_const
  have g5 : ∀ᶠ t in atBot, ⟪g, M.F.U t g⟫_ℂ = 1 := by
    filter_upwards [eventually_lt_atBot (0 : ℝ)] with t ht
    have := g4 ht
    simp only [Pi.zero_apply, mul_eq_zero, (Real.exp_pos t).ne', false_or, pow_eq_zero_iff two_ne_zero, norm_eq_zero, sub_eq_zero] at this
    rw [this, inner_self_eq_norm_sq_to_K, g1]; simp
  exact one_ne_zero (tendsto_nhds_unique (tendsto_const_nhds.congr' (g5.mono fun _ h => h.symm)) ((projLaws M).1 g g).2)
end

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.resInv :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (M : Sc H V W) (B : H →L[ℂ] H) (β : ℝ → V →L[ℂ] V) (β' : ℝ → W →L[ℂ] W), Ker β → Ker β' → IsUnit (symb β 0) → IsUnit (symb β' 0) → M.Acts B β β' → IsCompactOperator (M.abelian₂ M.T₀ M.T₀ ∘L B ∘L M.abelian₂ M.T₀ M.T₀) →
      Function.Surjective (1 - M.abelian₂ M.T₀ M.T₀ ∘L M.F.av wR ∘L M.abelian₂ M.T₀ M.T₀ : H →L[ℂ] H) := by
  intro H _ _ _ V _ _ _ _ W _ _ _ _ M B β β' k1 k2 u1 u2 ha hc
  obtain ⟨-, -, l0, sa, ln, -⟩ := (projLaws M).2.2.2.2.2.2.2 M.T₀ M.T₀ (by linarith)
  set Λ := M.abelian₂ M.T₀ M.T₀ with hΛ
  set R := M.F.av wR with hR
  have hΛΛ : ∀ x, Λ (Λ x) = Λ x := fun x => DFunLike.congr_fun l0 x
  have below : ∀ S : H →L[ℂ] H, (∀ x, (⟪x, S x⟫_ℂ).re = (⟪x, R x⟫_ℂ).re) →
      ∃ c : ℝ, 0 < c ∧ ∀ x, c * ‖x‖ ≤ ‖x - Λ (S (Λ x))‖ := by
    intro S hS
    by_contra hcon
    push Not at hcon
    choose x hx using fun n : ℕ => hcon (1 / ((n : ℝ) + 1)) Nat.one_div_pos_of_nat
    have h0 : ∀ n, x n ≠ 0 := fun n h => by simpa [h] using hx n
    let f : ℕ → H := fun n => (‖x n‖⁻¹ : ℂ) • x n
    have hf : ∀ n, ‖f n‖ = 1 := fun n => norm_smul_inv_norm (h0 n)
    have t0 : Tendsto (fun n => f n - Λ (S (Λ (f n)))) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
      have e : f n - Λ (S (Λ (f n))) = (‖x n‖⁻¹ : ℂ) • (x n - Λ (S (Λ (x n)))) := by simp [f, smul_sub]
      rw [e, norm_smul, norm_inv, Complex.norm_real, norm_norm, inv_mul_le_iff₀ (norm_pos_iff.2 (h0 n)), mul_comm]
      exact (hx n).le
    have t1 : Tendsto (fun n => Λ (f n) - f n) atTop (𝓝 0) := by
      have := ((Λ.continuous.tendsto 0).comp t0).sub t0
      simpa [Function.comp_def, hΛΛ] using this
    have t2 : Tendsto (fun n => f n - Λ (S (f n))) atTop (𝓝 0) := by
      have := t0.add (((Λ ∘L S).continuous.tendsto 0).comp t1)
      simpa [Function.comp_def] using this
    have t3 : Tendsto (fun n => ⟪f n, f n - Λ (S (f n))⟫_ℂ + ⟪Λ (f n) - f n, S (f n)⟫_ℂ) atTop (𝓝 0) := by
      have a : Tendsto (fun n => ⟪f n, f n - Λ (S (f n))⟫_ℂ) atTop (𝓝 0) :=
        squeeze_zero_norm (fun n => (norm_inner_le_norm _ _).trans_eq (by rw [hf, one_mul])) (tendsto_zero_iff_norm_tendsto_zero.1 t2)
      have b : Tendsto (fun n => ⟪Λ (f n) - f n, S (f n)⟫_ℂ) atTop (𝓝 0) := by
        refine squeeze_zero_norm (a := fun n => ‖Λ (f n) - f n‖ * ‖S‖) (fun n => (norm_inner_le_norm _ _).trans ?_) ?_
        · gcongr; simpa [hf] using S.le_opNorm (f n)
        · simpa using (tendsto_zero_iff_norm_tendsto_zero.1 t1).mul_const ‖S‖
      simpa using a.add b
    refine resBelow M B β β' k1 k2 u1 u2 ha hc f hf t1 ?_
    have t4 := (tendsto_const_nhds (x := (1 : ℝ))).sub ((Complex.continuous_re.tendsto 0).comp t3)
    simp only [Complex.zero_re, sub_zero] at t4
    refine t4.congr fun n => ?_
    have e1 : ⟪f n, f n⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hf]; simp
    rw [← hS, Function.comp_apply, inner_sub_right, inner_sub_left, sa.isSymmetric.apply_clm, e1]
    simp
  obtain ⟨c, c0, h1⟩ := below R fun _ => rfl
  obtain ⟨c', c0', h2⟩ := below (ContinuousLinearMap.adjoint R) fun x => by
    rw [ContinuousLinearMap.adjoint_inner_right, ← inner_conj_symm, Complex.conj_re]
  set A : H →L[ℂ] H := 1 - Λ ∘L R ∘L Λ with hA
  have anti : AntilipschitzWith ⟨c⁻¹, by positivity⟩ A := A.antilipschitz_of_bound fun x => by
    show ‖x‖ ≤ c⁻¹ * ‖x - Λ (R (Λ x))‖
    rw [le_inv_mul_iff₀ c0]; exact h1 x
  have cl : IsClosed (LinearMap.range (A : H →ₗ[ℂ] H) : Set H) := anti.isClosed_range A.uniformContinuous
  have bot : (LinearMap.range (A : H →ₗ[ℂ] H))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    have h3 : y - Λ (ContinuousLinearMap.adjoint R (Λ y)) = 0 := ext_inner_left ℂ fun x => by
      have := hy (A x) ⟨x, rfl⟩
      rw [inner_sub_right, ← sa.isSymmetric.apply_clm, ContinuousLinearMap.adjoint_inner_right, ← sa.isSymmetric.apply_clm,
        ← inner_sub_left, inner_zero_right]
      exact this
    have := h2 y
    rw [h3, norm_zero] at this
    exact norm_le_zero_iff.1 (nonpos_of_mul_nonpos_right this c0')
  haveI := cl.completeSpace_coe
  exact LinearMap.range_eq_top.1 ((Submodule.orthogonal_eq_bot_iff).1 bot)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.NEx
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ResTail
open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.resTail :
    ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] (k : L V) (T : ℝ), cut V (Iic T) k = k → Tail (cut V (Ioi T) ((shF V).av wR k)) := by
  intro V _ _ _ _ k T hk
  obtain ⟨-, w1, w2, w3⟩ := avSpec (shF V)
  obtain ⟨a1, a2, -⟩ := w3 wR w1
  have cl := fun s t hs ht => cutLaws (V := V) s t hs ht
  refine ⟨Real.exp |T| * ‖k‖, fun ρ hρ => ?_⟩
  have e := DFunLike.congr_fun (cl (Icc (-ρ) ρ)ᶜ (Ioi T) measurableSet_Icc.compl measurableSet_Ioi).1 ((shF V).av wR k)
  rw [ContinuousLinearMap.comp_apply] at e
  rw [e]
  by_cases h : |T| ≤ ρ
  · have e2 : (Icc (-ρ) ρ)ᶜ ∩ Ioi T = Ioi ρ := by
      ext x
      have := abs_le.1 h
      simp only [mem_inter_iff, mem_compl_iff, mem_Icc, mem_Ioi, not_and_or, not_le]
      constructor
      · rintro ⟨h1 | h1, h2⟩ <;> linarith
      · exact fun h1 => ⟨Or.inr h1, by linarith⟩
    rw [e2, (a1 k).2]
    erw [← (cut V (Ioi ρ)).integral_comp_comm (a1 k).1]
    have ib : Integrable fun t => (Iic (T - ρ)).indicator Real.exp t * ‖k‖ :=
      ((integrable_indicator_iff measurableSet_Iic).2 (integrableOn_exp_Iic _)).mul_const _
    refine (norm_integral_le_of_norm_le ib (Eventually.of_forall fun t => ?_)).trans ?_
    · rw [map_smul, norm_smul]
      by_cases ht : t ≤ T - ρ
      · rw [indicator_of_mem (mem_Iic.2 ht)]
        refine mul_le_mul ?_ (((cl _ univ measurableSet_Ioi .univ).2.2.2.2.2.1 _).trans_eq ((shF V).norm t k)) (norm_nonneg _)
          (Real.exp_pos _).le
        refine (norm_indicator_le_norm_self _ _).trans_eq ?_
        simp
      · have h1 := DFunLike.congr_fun ((cl (Ioi (ρ + t)) univ measurableSet_Ioi .univ).2.2.2.2.2.2.1 t) k
        simp only [ContinuousLinearMap.comp_apply, preimage_add_const_Ioi, add_sub_cancel_right] at h1
        have h2 := DFunLike.congr_fun (cl (Ioi (ρ + t)) (Iic T) measurableSet_Ioi measurableSet_Iic).1 k
        rw [ContinuousLinearMap.comp_apply, hk, Ioi_inter_Iic, Ioc_eq_empty (by linarith [not_le.1 ht]),
          (cl univ univ .univ .univ).2.2.2.2.1] at h2
        have h3 : cut V (Ioi ρ) ((shF V).U t k) = 0 := by
          show cut V (Ioi ρ) (sh V t k) = 0
          rw [← h1, h2]; simp
        rw [h3, indicator_of_notMem (by simpa using ht)]; simp
    · rw [integral_mul_const, integral_indicator measurableSet_Iic, integral_exp_Iic, mul_right_comm, ← Real.exp_add]
      gcongr
      linarith [le_abs_self T]
  · refine ((cl _ univ (measurableSet_Icc.compl.inter measurableSet_Ioi) .univ).2.2.2.2.2.1 _).trans ?_
    refine (((shF V).av wR).le_of_opNorm_le (a2.trans_eq w2) k).trans ?_
    rw [mul_right_comm, ← Real.exp_add]
    gcongr
    exact Real.one_le_exp (by linarith [not_le.1 h])
end

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.nEx :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (M : Sc H V W), Function.Surjective (1 - M.abelian₂ M.T₀ M.T₀ ∘L M.F.av wR ∘L M.abelian₂ M.T₀ M.T₀ : H →L[ℂ] H) → ∃ N : W →ₗ[ℂ] V, M.IsN N := by
  intro H _ _ _ V _ _ _ _ W _ _ _ _ M hs
  obtain ⟨c0, cadd, csmul, -, csh, -, -, -⟩ := cobLaws M.F
  obtain ⟨-, -, -, -, hP, -, -, hL⟩ := projLaws M
  have hP' := (projLaws M.swap).2.2.2.2.1
  obtain ⟨o1, o2, l0, -, -, l1, l2, l3, l4⟩ := hL M.T₀ M.T₀ (by linarith)
  set T := M.T₀ with hT
  set Λ := M.abelian₂ T T with hΛ
  have mI : ∀ x : ℝ, MeasurableSet (Ioi x) := fun _ => measurableSet_Ioi
  have carry : ∀ p : L V, Tail p → M.F.Cob (M.J p - M.J (one V (∫ x, p x))) := fun p hp => by
    have := (cobLaws (shF V)).2.2.2.2.2.2.2 M.F (M.J.toContinuousLinearEquiv : L V →L[ℂ] H) (fun t h => (M.hJ t h).symm) _
      ((cobTail p).2 hp).2
    rwa [map_sub] at this
  have ex : ∀ w, ∃ n, M.F.Cob (M.J' (one W w) - M.J (one V n)) := by
    intro w
    set h := M.F.U (T - 1) (M.J' (one W w)) with hh
    have s0 : M.P' (Ioc 0 1) (M.J' (one W w)) = M.J' (one W w) := by
      show M.J' (cut W _ (M.J'.symm (M.J' _))) = _
      rw [M.J'.symm_apply_apply, ((cutLaws (Ioc 0 1) univ measurableSet_Ioc .univ).2.2.2.2.2.2.2.1 _).2]
      exact ((svSpec (V := W)).2 w).1.mono fun x hx hn => by rw [hx, indicator_of_notMem hn]
    have s1 : M.P' (Ioc (T - 1) T) h = h := by
      have := DFunLike.congr_fun ((hP _ _ (measurableSet_Ioc (a := (0 : ℝ)) (b := 1)) .univ).2.2.2.2 (T - 1)).2 (M.J' (one W w))
      have y : (fun x : ℝ => x - (T - 1)) ⁻¹' Ioc 0 1 = Ioc (T - 1) T := by
        ext x; simp only [mem_preimage, mem_Ioc]; constructor <;> rintro ⟨a, b⟩ <;> constructor <;> linarith
      rw [y] at this
      simp only [ContinuousLinearMap.comp_apply, s0] at this
      exact this.symm
    have s2 : M.P' (Ioi T) h = 0 := by
      have a : M.P' (Ioi T) ∘L M.P' (Ioc (T - 1) T) = M.P' (Ioi T ∩ Ioc (T - 1) T) := (hP' _ _ (mI T) measurableSet_Ioc).1
      have b : Ioi T ∩ Ioc (T - 1) T = ∅ := eq_empty_of_forall_notMem fun x hx => absurd hx.1 (not_lt.2 hx.2.2)
      rw [b, show M.P' ∅ = 0 from (projLaws M.swap).2.2.2.2.2.1] at a
      rw [← s1]; exact DFunLike.congr_fun a h
    have s3 : M.P (Ioi (T + 1)) h = 0 := by
      have a : M.P' (Ioi (T - 1)) ∘L M.P' (Ioc (T - 1) T) = M.P' (Ioi (T - 1) ∩ Ioc (T - 1) T) := (hP' _ _ (mI _) measurableSet_Ioc).1
      rw [inter_eq_right.2 Ioc_subset_Ioi_self] at a
      rw [← s1, ← a]
      exact DFunLike.congr_fun (hL (T + 1) (T - 1) (by linarith)).1 _
    obtain ⟨k, hk⟩ := hs (Λ h)
    set R := M.F.av wR with hR
    have hk' : k - Λ (R (Λ k)) = Λ h := hk
    have ΛΛ : ∀ x, Λ (Λ x) = Λ x := fun x => DFunLike.congr_fun l0 x
    have kΛ : Λ k = k := by
      have := congrArg Λ hk'
      rw [map_sub, ΛΛ, ΛΛ, ← hk'] at this
      exact sub_left_injective this
    rw [kΛ] at hk'
    have k1 : M.P (Ioi T) k = 0 := by rw [← kΛ]; exact DFunLike.congr_fun l2 k
    have k2 : M.P' (Ioi T) k = 0 := by rw [← kΛ]; exact DFunLike.congr_fun l4 k
    have r2 : M.P' (Ioi T) (R k) = 0 := by
      obtain ⟨i, e⟩ := ((avSpec M.F).2.2.2 _ (avSpec M.F).2.1).1 k
      rw [hR, e, ← (M.P' (Ioi T)).integral_comp_comm i]
      refine integral_eq_zero_of_ae (Eventually.of_forall fun r => ?_)
      by_cases hr : r ≤ 0
      · have a := DFunLike.congr_fun ((hP _ _ (mI (T - r)) .univ).2.2.2.2 r).2 k
        have y : (fun x : ℝ => x - r) ⁻¹' Ioi (T - r) = Ioi T := by ext x; simp
        have b : M.P' (Ioi (T - r)) ∘L M.P' (Ioi T) = M.P' (Ioi (T - r) ∩ Ioi T) := (hP' _ _ (mI _) (mI _)).1
        rw [inter_eq_left.2 (Ioi_subset_Ioi (by linarith))] at b
        rw [y, ← b] at a
        simp only [ContinuousLinearMap.comp_apply, k2, map_zero] at a
        simp [← a]
      · simp [wR, hr]
    have dec : h = (k - R k) + M.P (Ioi T) (R k) + M.P (Ioi T) h := by
      have a : Λ h = h - M.P (Ioi T) h - M.P' (Ioi T) h := rfl
      have b : Λ (R k) = R k - M.P (Ioi T) (R k) - M.P' (Ioi T) (R k) := rfl
      rw [a, b, s2, r2, sub_zero, sub_zero] at hk'
      linear_combination (norm := module) -hk'
    have cl := fun s t hs ht => cutLaws (V := V) s t hs ht
    set u := M.J.symm k with hu
    have u1 : cut V (Iic T) u = u := by
      have a := (cl (Iic T) (Ioi T) measurableSet_Iic (mI T)).2.2.1 (Iic_disjoint_Ioi le_rfl)
      rw [Iic_union_Ioi, (cl _ _ .univ .univ).2.2.2.1] at a
      have b : u = cut V (Iic T) u + cut V (Ioi T) u := DFunLike.congr_fun a u
      have c : cut V (Ioi T) u = 0 := M.J.injective (by rw [map_zero]; exact k1)
      rw [c, add_zero] at b
      exact b.symm
    have e1 : M.P (Ioi T) (R k) = M.J (cut V (Ioi T) ((shF V).av wR u)) := by
      have := DFunLike.congr_fun (((avSpec (shF V)).2.2.2 _ (avSpec M.F).2.1).2.2.2.2 M.F
        (M.J.toContinuousLinearEquiv : L V →L[ℂ] H) fun t h => (M.hJ t h).symm) u
      have a : M.J ((shF V).av wR u) = R (M.J u) := this
      rw [hu, M.J.apply_symm_apply] at a
      show M.J (cut V _ (M.J.symm (R k))) = _
      rw [← a, M.J.symm_apply_apply]
    set v := cut V (Ioi T) (M.J.symm h) with hv
    have e2 : M.P (Ioi T) h = M.J v := rfl
    have bv : Bdd v := by
      refine ⟨|T| + 1, ?_⟩
      have a := (cl (Ioc T (T + 1)) (Ioi (T + 1)) measurableSet_Ioc (mI _)).2.2.1 (Ioc_disjoint_Ioi le_rfl)
      rw [Ioc_union_Ioi_eq_Ioi (by linarith)] at a
      have c : cut V (Ioi (T + 1)) (M.J.symm h) = 0 := M.J.injective (by rw [map_zero]; exact s3)
      have b : v = cut V (Ioc T (T + 1)) (M.J.symm h) := by rw [hv, a, ContinuousLinearMap.add_apply, c, add_zero]
      have d := (cl (Icc (-(|T| + 1)) (|T| + 1)) (Ioc T (T + 1)) measurableSet_Icc measurableSet_Ioc).1
      have sub : Ioc T (T + 1) ⊆ Icc (-(|T| + 1)) (|T| + 1) := fun x hx =>
        ⟨by linarith [hx.1, neg_abs_le T], by linarith [hx.2, le_abs_self T]⟩
      rw [inter_eq_right.2 sub] at d
      rw [b]
      exact DFunLike.congr_fun d _
    have f1 := carry _ (resTail u T u1)
    have f2 := carry _ ((cobTail v).1 bv)
    have f3 := (cadd _ _ (cadd _ _ (cadd _ _ (csh (T - 1) (M.J' (one W w))) (resCob M.F k).1).1 f1).1 f2).1
    refine ⟨(∫ x, cut V (Ioi T) ((shF V).av wR u) x) + ∫ x, v x, ?_⟩
    convert f3 using 1
    rw [← e1, ← e2, map_add (f := _), map_add (f := _), ← hh, ← hR]
    linear_combination (norm := module) dec
  choose n hn using ex
  let b := Module.finBasis ℂ W
  refine ⟨b.constr ℂ fun i => n (b i), fun w => ?_⟩
  have e : M.J' (one W w) - M.J (one V (b.constr ℂ (fun i => n (b i)) w)) =
      ∑ i, b.repr w i • (M.J' (one W (b i)) - M.J (one V (n (b i)))) := by
    conv_lhs => rw [← b.sum_repr w]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Module.Basis.constr_basis, smul_sub, Finset.sum_sub_distrib]
  rw [e]
  exact Finset.sum_induction _ _ (fun x y hx hy => (cadd x y hx hy).1) c0 fun i _ => csmul _ _ (hn _)
end

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.nUnit :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (M : Sc H V W) (B : H →L[ℂ] H) (β : ℝ → V →L[ℂ] V) (β' : ℝ → W →L[ℂ] W), Ker β → Ker β' → IsUnit (symb β 0) → IsUnit (symb β' 0) → M.Acts B β β' → IsCompactOperator (M.abelian₂ M.T₀ M.T₀ ∘L B ∘L M.abelian₂ M.T₀ M.T₀) →
      ∃ N : W ≃ₗᵢ[ℂ] V, M.IsN (N.toLinearEquiv : W →ₗ[ℂ] V) := by
  intro H _ _ _ V _ _ _ _ W _ _ _ _ M B β β' k1 k2 u1 u2 ha hc
  obtain ⟨N, hN⟩ := nEx M (resInv M B β β' k1 k2 u1 u2 ha hc)
  have hl : M.swap.abelian₂ M.swap.T₀ M.swap.T₀ = M.abelian₂ M.T₀ M.T₀ := (projLaws M).2.2.2.1 _ _
  obtain ⟨N', hN'⟩ := nEx M.swap (resInv M.swap B β' β k2 k1 u2 u1 ⟨ha.2, ha.1⟩ (hl ▸ hc))
  have i1 := (nIso M).2 N hN
  have i2 := (nIso M.swap).2 N' hN'
  let A : W →ₗᵢ[ℂ] V := ⟨N, i1⟩
  let A' : V →ₗᵢ[ℂ] W := ⟨N', i2⟩
  have hd : Module.finrank ℂ W = Module.finrank ℂ V :=
    le_antisymm (LinearMap.finrank_le_finrank_of_injective A.injective) (LinearMap.finrank_le_finrank_of_injective A'.injective)
  exact ⟨A.toLinearIsometryEquiv hd, hN⟩
