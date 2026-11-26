module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ProjLaws
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.KvSpec

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.CarLaws
open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.carLaws :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (M : Sc H V W) (X : H →L[ℂ] H) (κ : ℝ → V →L[ℂ] W), Ker κ → M.Carries X κ →
      (∀ t h, X (M.F.U t h) = M.F.U (-t) (X h)) ∧ M.swap.Carries (ContinuousLinearMap.adjoint X) (sharp κ) ∧
      ∀ ρ T : ℝ, (∀ t, ρ < |t| → κ t = 0) → M.P' (Ioi (T + ρ)) ∘L X ∘L (1 - M.P (Ioi T)) = 0 := by
  intro H _ _ _ V _ _ _ _ W _ _ _ _ M X κ hk hX
  obtain ⟨c1, c2, -⟩ := convLaws κ hk
  refine ⟨fun t h => ?_, fun v => ?_, fun ρ T hρ => ?_⟩
  · obtain ⟨u, rfl⟩ := M.J.surjective h
    rw [M.hJ, hX, hX, M.hJ', neg_neg]
    exact congrArg M.J' (DFunLike.congr_fun (c1 t) u)
  · refine ext_inner_left ℂ fun h => ?_
    obtain ⟨u, rfl⟩ := M.J.surjective h
    show ⟪M.J u, ContinuousLinearMap.adjoint X (M.J' v)⟫_ℂ = ⟪M.J u, M.J (conv (sharp κ) v)⟫_ℂ
    rw [ContinuousLinearMap.adjoint_inner_right, hX, M.J'.inner_map_map, M.J.inner_map_map, ← (convAdj κ hk).2.1,
      ContinuousLinearMap.adjoint_inner_right]
  · ext h
    obtain ⟨u, rfl⟩ := M.J.surjective h
    have e : (1 - M.P (Ioi T)) (M.J u) = M.J (cut V (Iic T) u) := by
      have h1 := (cutLaws (V := V) (Iic T) (Ioi T) measurableSet_Iic measurableSet_Ioi)
      have h2 := h1.2.2.1 (Iic_disjoint_Ioi le_rfl)
      rw [Iic_union_Ioi, h1.2.2.2.1] at h2
      have h3 : u = cut V (Iic T) u + cut V (Ioi T) u := DFunLike.congr_fun h2 u
      simp only [Sc.P, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, ContinuousLinearMap.comp_apply]
      show M.J u - M.J (cut V (Ioi T) (M.J.symm (M.J u))) = _
      rw [M.J.symm_apply_apply, ← map_sub, sub_eq_of_eq_add h3]
    show M.P' (Ioi (T + ρ)) (X ((1 - M.P (Ioi T)) (M.J u))) = 0
    rw [e, hX]
    show M.J' (cut W (Ioi (T + ρ)) (M.J'.symm (M.J' _))) = 0
    rw [M.J'.symm_apply_apply]
    have := DFunLike.congr_fun (c2 ρ T hρ) u
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply] at this
    rw [this, map_zero]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.BandHS
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ScalSpec
open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.scalSpec :
    ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] (φ : ℝ → ℂ), Continuous φ → HasCompactSupport φ → Ker (scal V φ) ∧ (shF V).av φ = conv (scal V φ) ∧ kv (scal V φ) = sv V fun x => φ (-x) := by
  intro V _ _ _ _ φ h1 h2
  have hk : Ker (scal V φ) := ⟨h1.smul continuous_const, h2.smul_right (f' := fun _ => ContinuousLinearMap.id ℂ V)⟩
  refine ⟨hk, ?_, ?_⟩
  · ext1 u
    rw [(((avSpec (shF V)).2.2.2 φ (h1.integrable_of_hasCompactSupport h2)).1 u).2, (convSpec _ hk u).2.2]
    refine integral_congr_ae (Eventually.of_forall fun t => Lp.ext ?_)
    filter_upwards [Lp.coeFn_smul (φ t) (sh V t u), (scal V φ t).coeFn_compLpL (sh V t u)] with x a b
    rw [b]; exact a
  · ext1 e
    have hm : MemLp (fun x => φ (-x)) 2 volume :=
      (h1.comp continuous_neg).memLp_of_hasCompactSupport (h2.comp_homeomorph (Homeomorph.neg ℝ))
    refine Lp.ext ?_
    filter_upwards [((kvSpec _ hk).1 e).1, ((svSpec (V := V)).1 _ hm e).1] with x a b
    rw [a, b]; rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ContAdj
open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

section
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V]

private theorem cnt [TopologicalSpace.SeparableSpace H] {ι : Type} {v : ι → H} (hv : Orthonormal ℂ v) : Countable ι := by
  refine Pairwise.countable_of_isOpen_disjoint (s := fun i => Metric.ball (v i) (1 / 2)) (fun i j hij => ?_)
    (fun _ => Metric.isOpen_ball) fun i => Metric.nonempty_ball.2 (by norm_num)
  refine Metric.ball_disjoint_ball ?_
  have h := @norm_sub_sq ℂ H _ _ _ (v i) (v j)
  rw [hv.1, hv.1, hv.2 hij] at h
  simp only [map_zero] at h
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (v i - v j)]

private theorem contAdj {k : ℝ → V →L[ℂ] H} (hk : Continuous k) (c : H) : Continuous fun y => ContinuousLinearMap.adjoint (k y) c :=
  (ContinuousLinearMap.adjoint.continuous.comp hk).clm_apply continuous_const

private theorem cSq {k : ℝ → V →L[ℂ] H} (hk : Continuous k) (c : H) : Continuous fun y => ‖ContinuousLinearMap.adjoint (k y) c‖ ^ 2 :=
  (contAdj hk c).norm.pow 2

private theorem memL (a b : ℝ) {g : ℝ → V} (hg : Continuous g) : MemLp ((Ioc a b).indicator g) 2 volume := by
  rw [memLp_indicator_iff_restrict measurableSet_Ioc.nullMeasurableSet]
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hg.continuousOn (s := Icc a b))
  exact MemLp.of_bound hg.aestronglyMeasurable C
    ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun x hx => hC x (Ioc_subset_Icc_self hx)))

private theorem adjEq (J : L V ≃ₗᵢ[ℂ] H) (a b : ℝ) {k : ℝ → V →L[ℂ] H} {Y : H →L[ℂ] H} (hk : Continuous k)
    (hY : ∀ u : L V, Y (J u) = ∫ y in Ioc a b, k y (u y)) (c : H) : ContinuousLinearMap.adjoint Y c = J ((memL a b (contAdj hk c)).toLp _) := by
  refine ext_inner_right ℂ fun h => ?_
  obtain ⟨u, rfl⟩ := J.surjective h
  have hu : IntegrableOn (u : ℝ → V) (Ioc a b) := ((Lp.memLp u).restrict _).integrable one_le_two
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hk.continuousOn (s := Icc a b))
  have hi : IntegrableOn (fun y => k y (u y)) (Ioc a b) := by
    refine (hu.norm.const_mul C).mono' ?_ ?_
    · exact isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable (hk.aestronglyMeasurable.prodMk hu.1)
    · exact (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun x hx =>
        (k x).le_of_opNorm_le (hC x (Ioc_subset_Icc_self hx)) _)
  rw [ContinuousLinearMap.adjoint_inner_left, hY, ← integral_inner hi, J.inner_map_map, L2.inner_def,
    ← integral_indicator measurableSet_Ioc]
  refine integral_congr_ae ?_
  filter_upwards [(memL a b (contAdj hk c)).coeFn_toLp] with x hx
  rw [hx]
  by_cases h : x ∈ Ioc a b <;> simp [h, ContinuousLinearMap.adjoint_inner_left]

private theorem innEq (J : L V ≃ₗᵢ[ℂ] H) (a b : ℝ) {k k' : ℝ → V →L[ℂ] H} {Y Y' : H →L[ℂ] H} (hk : Continuous k) (hk' : Continuous k')
    (hY : ∀ u : L V, Y (J u) = ∫ y in Ioc a b, k y (u y)) (hY' : ∀ u : L V, Y' (J u) = ∫ y in Ioc a b, k' y (u y)) (c : H) :
    ⟪ContinuousLinearMap.adjoint Y c, ContinuousLinearMap.adjoint Y' c⟫_ℂ = ∫ y in Ioc a b, ⟪ContinuousLinearMap.adjoint (k y) c, ContinuousLinearMap.adjoint (k' y) c⟫_ℂ := by
  rw [adjEq J a b hk hY, adjEq J a b hk' hY', J.inner_map_map, L2.inner_def, ← integral_indicator measurableSet_Ioc]
  refine integral_congr_ae ?_
  filter_upwards [(memL a b (contAdj hk c)).coeFn_toLp, (memL a b (contAdj hk' c)).coeFn_toLp] with x hx hx'
  rw [hx, hx']
  by_cases h : x ∈ Ioc a b <;> simp [h]

private theorem normEq (J : L V ≃ₗᵢ[ℂ] H) (a b : ℝ) {k : ℝ → V →L[ℂ] H} {Y : H →L[ℂ] H} (hk : Continuous k)
    (hY : ∀ u : L V, Y (J u) = ∫ y in Ioc a b, k y (u y)) (c : H) : ‖ContinuousLinearMap.adjoint Y c‖ ^ 2 = ∫ y in Ioc a b, ‖ContinuousLinearMap.adjoint (k y) c‖ ^ 2 := by
  have h := innEq J a b hk hk hY hY c
  simp only [inner_self_eq_norm_sq_to_K] at h
  have e : ∀ x : ℝ, ((x : ℂ) ^ 2) = ((x ^ 2 : ℝ) : ℂ) := fun x => by push_cast; rfl
  change ((‖ContinuousLinearMap.adjoint Y c‖ : ℝ) : ℂ) ^ 2 = ∫ y in Ioc a b, ((‖ContinuousLinearMap.adjoint (k y) c‖ : ℝ) : ℂ) ^ 2 at h
  simp only [e] at h
  rw [integral_complex_ofReal] at h
  exact_mod_cast h

private theorem ptSum {ι : Type} (c : HilbertBasis ι ℂ H) (A A' : V →L[ℂ] H) :
    HasSum (fun m => ⟪ContinuousLinearMap.adjoint A (c m), ContinuousLinearMap.adjoint A' (c m)⟫_ℂ) (∑ i, ⟪A' (stdOrthonormalBasis ℂ V i), A (stdOrthonormalBasis ℂ V i)⟫_ℂ) := by
  have h := hasSum_sum (s := Finset.univ) fun i _ => c.hasSum_inner_mul_inner (A' (stdOrthonormalBasis ℂ V i)) (A (stdOrthonormalBasis ℂ V i))
  suffices e : ∀ m, ⟪ContinuousLinearMap.adjoint A (c m), ContinuousLinearMap.adjoint A' (c m)⟫_ℂ = ∑ i, ⟪A' (stdOrthonormalBasis ℂ V i), c m⟫_ℂ * ⟪c m, A (stdOrthonormalBasis ℂ V i)⟫_ℂ by
    simpa only [e] using h
  intro m
  rw [← (stdOrthonormalBasis ℂ V).sum_inner_mul_inner]
  exact Finset.sum_congr rfl fun i _ => by
    rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right, mul_comm]

private theorem ptSumR {ι : Type} (c : HilbertBasis ι ℂ H) (A : V →L[ℂ] H) :
    HasSum (fun m => ‖ContinuousLinearMap.adjoint A (c m)‖ ^ 2) (∑ i, ‖A (stdOrthonormalBasis ℂ V i)‖ ^ 2) := by
  have h := (ptSum c A A).mapL Complex.reCLM
  simpa [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow] using h

private theorem summ (J : L V ≃ₗᵢ[ℂ] H) (a b : ℝ) {k : ℝ → V →L[ℂ] H} {Y : H →L[ℂ] H} (hk : Continuous k)
    (hY : ∀ u : L V, Y (J u) = ∫ y in Ioc a b, k y (u y)) {ι : Type} (c : HilbertBasis ι ℂ H) :
    Summable fun m => ‖ContinuousLinearMap.adjoint Y (c m)‖ ^ 2 := by
  have ci : ∀ {f : ℝ → ℝ}, Continuous f → IntegrableOn f (Ioc a b) := fun hf => hf.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  refine summable_of_sum_le (c := ∫ y in Ioc a b, ∑ i, ‖k y (stdOrthonormalBasis ℂ V i)‖ ^ 2) (fun _ => sq_nonneg _) fun s => ?_
  simp only [normEq J a b hk hY]
  rw [← integral_finsetSum _ fun m _ => ci (cSq hk _)]
  refine integral_mono (integrable_finsetSum _ fun m _ => ci (cSq hk _))
    (ci (continuous_finsetSum _ fun i _ => (hk.clm_apply continuous_const).norm.pow 2)) fun y => ?_
  exact sum_le_hasSum s (fun _ _ => sq_nonneg _) (ptSumR c (k y))

private theorem isHS (J : L V ≃ₗᵢ[ℂ] H) (a b : ℝ) {k : ℝ → V →L[ℂ] H} {Y : H →L[ℂ] H} (hk : Continuous k)
    (hY : ∀ u : L V, Y (J u) = ∫ y in Ioc a b, k y (u y)) : IsHilbertSchmidt Y := by
  rw [← isHilbertSchmidt_adjoint_iff, isHilbertSchmidt_iff (stdHilbertBasis ℂ H)]
  have h := summ J a b hk hY (stdHilbertBasis ℂ H)
  have := h.tsum_ofReal_lt_top
  simpa [ENNReal.ofReal_pow] using this

private theorem trEq (J : L V ≃ₗᵢ[ℂ] H) (a b : ℝ) {k k' : ℝ → V →L[ℂ] H} {Y Y' : H →L[ℂ] H} (hk : Continuous k) (hk' : Continuous k')
    (hY : ∀ u : L V, Y (J u) = ∫ y in Ioc a b, k y (u y)) (hY' : ∀ u : L V, Y' (J u) = ∫ y in Ioc a b, k' y (u y)) :
    trace (ContinuousLinearMap.adjoint Y' ∘L Y) = ∫ y in Ioc a b, ∑ i, ⟪k' y (stdOrthonormalBasis ℂ V i), k y (stdOrthonormalBasis ℂ V i)⟫_ℂ := by
  have h1 := isHS J a b hk hY
  have h2 := (isHS J a b hk' hY').adjoint
  let c := stdHilbertBasis ℂ H
  haveI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
  haveI : ProperSpace V := FiniteDimensional.proper ℂ V
  haveI : TopologicalSpace.SeparableSpace H := J.surjective.denseRange.separableSpace J.continuous
  haveI := cnt c.orthonormal
  have s1 := (isTraceClass_comp h1 h2).hasSum_trace c
  have ci : ∀ {f : ℝ → ℝ}, Continuous f → IntegrableOn f (Ioc a b) := fun hf => hf.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have cg : ∀ m, Continuous fun y => ⟪ContinuousLinearMap.adjoint (k y) (c m), ContinuousLinearMap.adjoint (k' y) (c m)⟫_ℂ := fun m => (contAdj hk _).inner (contAdj hk' _)
  have s2 := hasSum_integral_of_summable_integral_norm (μ := volume.restrict (Ioc a b))
    (F := fun m y => ⟪ContinuousLinearMap.adjoint (k y) (c m), ContinuousLinearMap.adjoint (k' y) (c m)⟫_ℂ)
    (fun m => (cg m).integrableOn_Icc.mono_set Ioc_subset_Icc_self) (by
      refine Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _) (fun m => ?_)
        ((summ J a b hk hY c).add (summ J a b hk' hY' c))
      rw [normEq J a b hk hY, normEq J a b hk' hY', ← integral_add (ci (cSq hk _)) (ci (cSq hk' _))]
      refine integral_mono (ci (cg m).norm) ((ci (cSq hk _)).add (ci (cSq hk' _))) fun y => ?_
      refine (norm_inner_le_norm _ _).trans ?_
      show _ ≤ ‖ContinuousLinearMap.adjoint (k y) (c m)‖ ^ 2 + ‖ContinuousLinearMap.adjoint (k' y) (c m)‖ ^ 2
      nlinarith [sq_nonneg (‖ContinuousLinearMap.adjoint (k y) (c m)‖ - ‖ContinuousLinearMap.adjoint (k' y) (c m)‖), norm_nonneg (ContinuousLinearMap.adjoint (k y) (c m)), norm_nonneg (ContinuousLinearMap.adjoint (k' y) (c m))])
  simp only [← innEq J a b hk hk' hY hY', (ptSum c _ _).tsum_eq] at s2
  rw [trace_comp_comm_of_isHilbertSchmidt h2 h1]
  refine s1.unique ?_
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left] using s2
end

theorem UpperTheory.V.Z.IntegralApplyAeEq.kp :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] (J : L V ≃ₗᵢ[ℂ] H) (a b : ℝ) (k k' : ℝ → V →L[ℂ] H) (Y Y' : H →L[ℂ] H), a ≤ b → Continuous k → Continuous k' →
      (∀ u : L V, Y (J u) = ∫ y in Ioc a b, k y (u y)) → (∀ u : L V, Y' (J u) = ∫ y in Ioc a b, k' y (u y)) →
      IsHilbertSchmidt Y ∧ hsNorm Y ^ 2 = ∫ y in a..b, ∑ i, ‖k y (stdOrthonormalBasis ℂ V i)‖ ^ 2 ∧
        trace (ContinuousLinearMap.adjoint Y' ∘L Y) = ∫ y in a..b, ∑ i, ⟪k' y (stdOrthonormalBasis ℂ V i), k y (stdOrthonormalBasis ℂ V i)⟫_ℂ := by
  intro H _ _ _ V _ _ _ _ J a b k k' Y Y' hab hk hk' hY hY'
  have h1 := isHS J a b hk hY
  refine ⟨h1, ?_, by rw [intervalIntegral.integral_of_le hab]; exact trEq J a b hk hk' hY hY'⟩
  have s1 := (isTraceClass_comp h1.adjoint h1).hasSum_trace (stdHilbertBasis ℂ H)
  rw [trEq J a b hk hk hY hY] at s1
  have s2 := Complex.hasSum_ofReal.2 (h1.hasSum_norm_sq (stdHilbertBasis ℂ H))
  have e : ∀ x : H, ⟪x, x⟫_ℂ = ((‖x‖ ^ 2 : ℝ) : ℂ) := fun x => by rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right, e, ← Complex.ofReal_sum] at s1
  rw [integral_complex_ofReal] at s1
  rw [intervalIntegral.integral_of_le hab]
  exact_mod_cast s2.unique s1
end

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.bandHS :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (M : Sc H V W) (X : H →L[ℂ] H) (κ : ℝ → V →L[ℂ] W), Ker κ → M.Carries X κ → ∀ (φ : ℝ → ℂ) (a b : ℝ), Continuous φ → HasCompactSupport φ → a ≤ b →
      IsHilbertSchmidt (X ∘L M.P (Ioc a b)) ∧ hsNorm (X ∘L M.P (Ioc a b)) ^ 2 = (b - a) * ∑ i, ‖kv κ (stdOrthonormalBasis ℂ V i)‖ ^ 2 ∧
      IsHilbertSchmidt (M.F.av φ ∘L M.P (Ioc a b)) ∧
      hsNorm (M.F.av φ ∘L M.P (Ioc a b)) ^ 2 = (b - a) * (Module.finrank ℂ V * ∫ x, ‖φ x‖ ^ 2) ∧
      trace (ContinuousLinearMap.adjoint (M.F.av φ ∘L M.P (Ioc a b)) ∘L (X ∘L M.P (Ioc a b))) =
        ∫ y in a..b, ∑ i, M.cor (fun x => φ (-x)) (stdOrthonormalBasis ℂ V i) (kv κ (stdOrthonormalBasis ℂ V i)) (2 * y) := by
  intro H _ _ _ V _ _ _ _ W _ _ _ _ M X κ hk hX φ a b h1 h2 hab
  have cU : ∀ (F : Flow H) (A : V →L[ℂ] H), Continuous fun y => F.U y ∘L A := fun F A =>
    continuous_clm_apply.2 fun e => F.cont (A e)
  let A : V →L[ℂ] H := (M.J'.toContinuousLinearEquiv : L W →L[ℂ] H) ∘L kv κ
  let A' : V →L[ℂ] H := (M.J.toContinuousLinearEquiv : L V →L[ℂ] H) ∘L sv V fun x => φ (-x)
  have pa : ∀ u, M.P (Ioc a b) (M.J u) = M.J (cut V (Ioc a b) u) := fun u => congrArg M.J (congrArg _ (M.J.symm_apply_apply u))
  obtain ⟨s1, s2, s3⟩ := scalSpec (V := V) φ h1 h2
  have hi : Integrable φ := h1.integrable_of_hasCompactSupport h2
  have y1 : ∀ u : L V, (X ∘L M.P (Ioc a b)) (M.J u) = ∫ y in Ioc a b, (M.F.U y ∘L A) (u y) := fun u => by
    obtain ⟨i1, i2⟩ := (kvSpec κ hk).2 a b u
    rw [ContinuousLinearMap.comp_apply, pa, hX, i2]
    refine ((M.J'.toContinuousLinearEquiv : L W →L[ℂ] H).integral_comp_comm i1).symm.trans ?_
    exact integral_congr_ae (Eventually.of_forall fun y => (M.hJ' y _).symm)
  have y2 : ∀ u : L V, (M.F.av φ ∘L M.P (Ioc a b)) (M.J u) = ∫ y in Ioc a b, (M.F.rev.U y ∘L A') (u y) := fun u => by
    obtain ⟨i1, i2⟩ := (kvSpec _ s1).2 a b u
    have c := ((avSpec (shF V)).2.2.2 φ hi).2.2.2.2 M.F (M.J.toContinuousLinearEquiv : L V →L[ℂ] H) fun t h => (M.hJ t h).symm
    have c' : ∀ v, M.F.av φ (M.J v) = M.J ((shF V).av φ v) := fun v => (DFunLike.congr_fun c v).symm
    rw [ContinuousLinearMap.comp_apply, pa, c', s2, i2]
    refine ((M.J.toContinuousLinearEquiv : L V →L[ℂ] H).integral_comp_comm i1).symm.trans ?_
    rw [s3]
    exact integral_congr_ae (Eventually.of_forall fun y => (M.hJ (-y) _).symm)
  obtain ⟨k1, k2, k3⟩ := kp M.J a b _ _ _ _ hab (cU M.F A) (cU M.F.rev A') y1 y2
  obtain ⟨k4, k5, -⟩ := kp M.J a b _ _ _ _ hab (cU M.F.rev A') (cU M.F.rev A') y2 y2
  refine ⟨k1, ?_, k4, ?_, ?_⟩
  · rw [k2]
    simp [M.F.norm, A]
  · rw [k5]
    have m2 : MemLp (fun x => φ (-x)) 2 volume :=
      (h1.comp continuous_neg).memLp_of_hasCompactSupport (h2.comp_homeomorph (Homeomorph.neg ℝ))
    have n : ∀ i, ‖(M.F.rev.U 0 ∘L A') (stdOrthonormalBasis ℂ V i)‖ ^ 2 = ∫ x, ‖φ x‖ ^ 2 := fun i => by
      show ‖M.F.rev.U 0 (M.J (sv V (fun x => φ (-x)) (stdOrthonormalBasis ℂ V i)))‖ ^ 2 = _
      rw [Flow.norm, M.J.norm_map, ((svSpec (V := V)).1 _ m2 _).2, (stdOrthonormalBasis ℂ V).orthonormal.1,
        integral_neg_eq_self fun x => ‖φ x‖ ^ 2]
      simp
    simp only [ContinuousLinearMap.comp_apply, Flow.norm] at n ⊢
    simp [n, mul_left_comm]
  · rw [k3]
    refine intervalIntegral.integral_congr fun y _ => Finset.sum_congr rfl fun i _ => ?_
    show ⟪M.F.U (-y) (M.J _), M.F.U y (M.J' _)⟫_ℂ = ⟪M.J _, M.F.U (2 * y) (M.J' _)⟫_ℂ
    rw [← (avSpec M.F).1, ContinuousLinearMap.adjoint_inner_left, ← M.F.add, two_mul]
    rfl
end
