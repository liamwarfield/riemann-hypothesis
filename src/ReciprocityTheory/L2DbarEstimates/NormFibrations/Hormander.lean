module

public import ReciprocityTheory.L2DbarEstimates.Mollifiers.MollEnormSqLe
public import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.ExtNull
public import ReciprocityTheory.L2DbarEstimates.BasicIdentity.HasCompactSupportOfVanish
public import ReciprocityTheory.L2DbarEstimates.HormanderEstimate.HStatementOf
public import ReciprocityTheory.L2DbarEstimates.HormanderEstimate.Closed
public import ReciprocityTheory.L2DbarEstimates.SkodaWeights.VolProdFinApply
public import ReciprocityTheory.L2DbarEstimates.LeviForms.TwBound
public import ReciprocityTheory.L2DbarEstimates.LeviForms.DetMonoDetOneAdd
public import ReciprocityTheory.L2DbarEstimates.LeviForms.MacofFderivApplyContDiffOn
public import ReciprocityTheory.L2DbarEstimates.LeviForms.DetUpdateColEq

@[expose] public section

section -- merged from ReciprocityTheory.L2DbarEstimates.LeviForms.FixedA
namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology Set
open scoped ENNReal ContDiff

noncomputable section

theorem fx_wint_eq_withDensity {M : Type*} [MeasurableSpace M] (n : ℕ) (z : M → V n)
    (ps : M → ℝ) (hps : Measurable ps) (F : M → ℂ) :
    wint n z F ps = ∫⁻ x, ‖F x‖ₑ ^ 2 ∂(vol n z).withDensity
      (fun x => ENNReal.ofReal (Real.exp (-ps x))) := by
  unfold wint
  have hmeas : Measurable (fun x => ENNReal.ofReal (Real.exp (-ps x))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hps.neg)
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable _ hmeas
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  refine lintegral_congr fun x => ?_
  simp only [Pi.mul_apply, Function.comp]
  rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_mul (Real.exp_pos _).le, mul_comm]

theorem fx_lintegral_enorm_sq_eq {α : Type*} [MeasurableSpace α] (μ : Measure α) (F : α → ℂ) :
    ∫⁻ x, ‖F x‖ₑ ^ 2 ∂μ = eLpNorm' F 2 μ ^ (2 : ℝ) := by
  rw [MeasureTheory.eLpNorm'_eq_lintegral_eNorm, ← ENNReal.rpow_mul]
  norm_num

end

end ReciprocityTheory.L2DbarEstimates.I
end

section -- merged from ReciprocityTheory.L2DbarEstimates.Mollifiers.MollTendstoOfContinuous
namespace ReciprocityTheory.L2DbarEstimates.B

open MeasureTheory Filter Topology Set Metric
open scoped Convolution ContDiff ENNReal Pointwise

theorem moll_tendsto_of_continuous (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] {ι : Type*} {l : Filter ι} {K : ι → Kernel E μ}
    (hK : Tendsto (fun i => (K i).r) l (𝓝 0)) {g : E → ℂ} (hgs : HasCompactSupport g)
    (hgc : Continuous g) : Tendsto (fun i => eLpNorm (moll (K i) g - g) 2 μ) l (𝓝 0) := by
  have hgu : UniformContinuous g := hgs.uniformContinuous_of_continuous hgc
  set S := Metric.cthickening 1 (tsupport g) with hS
  have hSc : IsCompact S := hgs.isCompact.cthickening
  set C := μ S ^ ((2 : ℝ≥0∞).toReal⁻¹) with hC
  have hCfin : C ≠ (⊤ : ℝ≥0∞) :=
    ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg) hSc.measure_lt_top.ne
  have hgm : AEStronglyMeasurable g μ := hgc.aestronglyMeasurable
  have key : ∀ δ : ℝ, 0 < δ → ∀ᶠ i in l, eLpNorm (moll (K i) g - g) 2 μ ≤ C * ENNReal.ofReal δ := by
    intro δ hδ
    obtain ⟨ρ, hρ, hρg⟩ := Metric.uniformContinuous_iff.1 hgu δ hδ
    filter_upwards [hK.eventually (gt_mem_nhds (lt_min hρ one_pos))] with i hi
    have hr : (K i).r < ρ := lt_of_lt_of_le hi (min_le_left _ _)
    have hr1 : (K i).r < 1 := lt_of_lt_of_le hi (min_le_right _ _)
    have hbound : ∀ x, ‖(moll (K i) g - g) x‖ ≤ δ := by
      intro x
      rw [Pi.sub_apply, ← dist_eq_norm]
      simp only [moll]
      exact dist_convolution_le hδ.le (K i).support_subset (K i).nonneg (K i).integral_eq_one hgm
        (fun y hy => (hρg (lt_trans (mem_ball.1 hy) hr)).le)
    have hsupp : Function.support (moll (K i) g - g) ⊆ S := by
      intro x hx
      by_contra hxS
      apply hx
      have hx0 : ∀ y ∈ ball x (K i).r, g y = 0 := by
        intro y hy
        by_contra hy0
        apply hxS
        refine Metric.mem_cthickening_of_dist_le x y 1 _ (subset_tsupport _ hy0) ?_
        rw [dist_comm]; exact le_of_lt (lt_trans (mem_ball.1 hy) hr1)
      have hgx : g x = 0 := hx0 x (mem_ball_self (K i).r_pos)
      have h0 : dist (moll (K i) g x) (0 : ℂ) ≤ 0 := by
        simp only [moll]
        exact dist_convolution_le le_rfl (K i).support_subset (K i).nonneg (K i).integral_eq_one hgm
          (fun y hy => by rw [hx0 y hy, dist_self])
      rw [Pi.sub_apply, hgx, sub_zero]
      exact dist_le_zero.1 h0
    have hKcs : HasCompactSupport (K i).toFun :=
      HasCompactSupport.intro (isCompact_closedBall (0 : E) (K i).r) (fun x hx => by
        by_contra h
        exact hx (ball_subset_closedBall ((K i).support_subset h)))
    have hKc : Continuous (K i).toFun := (K i).smooth.continuous
    have hgL : LocallyIntegrable g μ := hgc.locallyIntegrable
    have hc : Continuous (moll (K i) g - g) :=
      (hKcs.continuous_convolution_left _ hKc hgL).sub hgc
    rw [← eLpNorm_restrict_eq_of_support_subset hc.aestronglyMeasurable hsupp]
    refine (eLpNorm_le_of_ae_bound (μ := μ.restrict S) hc.aestronglyMeasurable
      (Filter.Eventually.of_forall hbound)).trans ?_
    rw [Measure.restrict_apply_univ]
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨n, hn, hnε⟩ := ENNReal.exists_nnreal_pos_mul_lt hCfin hε.ne'
  filter_upwards [key n (NNReal.coe_pos.2 hn)] with i hi
  refine hi.trans ?_
  rw [ENNReal.ofReal_coe_nnreal, mul_comm]
  exact hnε.le

theorem moll_l2Tendsto (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (ι : Type*) : MollifierL2Tendsto E μ ι := by
  intro l K hK u hu
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hη : ε / 3 ≠ 0 := (ENNReal.div_pos hε.ne' (by simp)).ne'
  obtain ⟨g, hgs, hug, hgc, hgL⟩ := hu.exists_hasCompactSupport_eLpNorm_sub_le (by simp) hη
  have hmid := moll_tendsto_of_continuous E μ hK hgs hgc
  rw [ENNReal.tendsto_nhds_zero] at hmid
  filter_upwards [hmid (ε / 3) (pos_iff_ne_zero.2 hη)] with i hi
  have hcs : HasCompactSupport (K i).toFun :=
    HasCompactSupport.intro (isCompact_closedBall (0 : E) (K i).r) (fun x hx => by
      by_contra h
      exact hx (ball_subset_closedBall ((K i).support_subset h)))
  have hKc : Continuous (K i).toFun := (K i).smooth.continuous
  have hug' : MemLp (u - g) 2 μ := hu.sub hgL
  have hli : LocallyIntegrable (u - g) μ := hug'.locallyIntegrable (by norm_num)
  have hgli : LocallyIntegrable g μ := hgL.locallyIntegrable (by norm_num)
  have hlin : moll (K i) u = moll (K i) (u - g) + moll (K i) g := by
    simp only [moll]
    rw [← ConvolutionExists.distrib_add (hcs.convolutionExists_left _ hKc hli)
      (hcs.convolutionExists_left _ hKc hgli), sub_add_cancel]
  have hc1 : Continuous (moll (K i) (u - g)) := hcs.continuous_convolution_left _ hKc hli
  have hc2 : Continuous (moll (K i) g) := hcs.continuous_convolution_left _ hKc hgli
  have hdec : moll (K i) u - u = moll (K i) (u - g) + (moll (K i) g - g) + (g - u) := by
    rw [hlin]; abel
  have hY : eLpNorm (moll (K i) (u - g)) 2 μ ≤ eLpNorm (u - g) 2 μ := by
    have h := moll_young E μ (K i) (u - g) Set.univ MeasurableSet.univ hug'.aestronglyMeasurable
    have hth : thickening (K i).r (Set.univ : Set E) = Set.univ :=
      Set.eq_univ_of_forall fun x => Metric.self_subset_thickening (K i).r_pos _ (Set.mem_univ x)
    simp only [hth, Measure.restrict_univ] at h
    exact h
  rw [hdec]
  calc eLpNorm (moll (K i) (u - g) + (moll (K i) g - g) + (g - u)) 2 μ
      ≤ eLpNorm (moll (K i) (u - g) + (moll (K i) g - g)) 2 μ + eLpNorm (g - u) 2 μ :=
        eLpNorm_add_le (by norm_num : 1 ≤ (2 : ℝ≥0∞))
    _ ≤ eLpNorm (moll (K i) (u - g)) 2 μ + eLpNorm (moll (K i) g - g) 2 μ + eLpNorm (g - u) 2 μ := by
        gcongr
        exact eLpNorm_add_le (by norm_num : 1 ≤ (2 : ℝ≥0∞))
    _ ≤ ε / 3 + ε / 3 + ε / 3 := by
        gcongr
        · exact hY.trans hug
        · rw [eLpNorm_sub_comm]; exact hug
    _ = ε := ENNReal.add_thirds ε

end ReciprocityTheory.L2DbarEstimates.B
end

section -- merged from ReciprocityTheory.L2DbarEstimates.Mollifiers.FderivMollApply
namespace ReciprocityTheory.L2DbarEstimates.B

open MeasureTheory Filter Topology Set Metric
open scoped Convolution ContDiff ENNReal Pointwise

theorem fderiv_moll_apply (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (K : Kernel E μ) {u : E → ℂ} (hu : LocallyIntegrable u μ)
    (x a : E) :
    fderiv ℝ (moll K u) x a = ∫ y, (fderiv ℝ K.toFun (x - y) a) • u y ∂μ := by
  have hcs : HasCompactSupport K.toFun :=
    HasCompactSupport.intro (isCompact_closedBall (0 : E) K.r) fun y hy => by
      by_contra h
      exact hy (ball_subset_closedBall (K.support_subset h))
  have hd := hcs.hasFDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (K.smooth.of_le (by simp)) hu x
  have hmoll : moll K u = K.toFun ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] u := rfl
  rw [hmoll, hd.fderiv]
  have hex := (hcs.fderiv ℝ).convolutionExists_left
    ((ContinuousLinearMap.lsmul ℝ ℝ).precompL E) (K.smooth.continuous_fderiv (by simp)) hu x
  rw [convolution_def, ContinuousLinearMap.integral_apply hex]
  rw [← integral_sub_left_eq_self _ μ x]
  congr 1
  ext y
  rw [sub_sub_cancel]
  rfl

theorem moll_weakComm (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] : WeakCommSt E μ := by
  intro m c v g w hw K
  funext x
  have hd : ∀ k, fderiv ℝ (moll K (g k)) x (v k) =
      ∫ y, (fderiv ℝ K.toFun (x - y) (v k)) • g k y ∂μ :=
    fun k => fderiv_moll_apply E μ K (hw.1 k) x (v k)
  set φ : E → ℂ := fun y => ((K.toFun (x - y) : ℝ) : ℂ) with hφdef
  have hφs : ContDiff ℝ ∞ φ :=
    Complex.ofRealCLM.contDiff.comp (K.smooth.comp (contDiff_const.sub contDiff_id))
  have hφc : HasCompactSupport φ :=
    HasCompactSupport.intro (isCompact_closedBall x K.r) fun y hy => by
      simp only [hφdef, Complex.ofReal_eq_zero]
      by_contra h
      apply hy
      have h' := K.support_subset h
      rw [mem_ball_zero_iff] at h'
      rw [mem_closedBall, dist_eq_norm, ← norm_neg, neg_sub]
      exact h'.le
  have hw3 := hw.2.2 φ hφs hφc
  have hdφ : ∀ y a, fderiv ℝ φ y a = -((fderiv ℝ K.toFun (x - y) a : ℝ) : ℂ) := by
    intro y a
    have h1 : HasFDerivAt (fun y : E => x - y) (-ContinuousLinearMap.id ℝ E) y :=
      (hasFDerivAt_id y).const_sub x
    have h2 := ((K.smooth.differentiable (by simp)) (x - y)).hasFDerivAt.comp y h1
    have h3 := Complex.ofRealCLM.hasFDerivAt.comp y h2
    rw [(show HasFDerivAt φ _ y from h3).fderiv]
    simp
  have hm : moll K w x = ∫ y, w y * φ y ∂μ := by
    show ∫ t, K.toFun t • w (x - t) ∂μ = _
    rw [← integral_sub_left_eq_self (fun t => K.toFun t • w (x - t)) μ x]
    congr 1
    ext y
    simp only [hφdef, sub_sub_cancel, Complex.real_smul]
    ring
  simp only [Dop, hd]
  rw [hm, hw3, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← mul_neg, ← integral_neg]
  congr 2
  ext y
  rw [hdφ, Complex.real_smul]
  ring

end ReciprocityTheory.L2DbarEstimates.B
end

section -- merged from ReciprocityTheory.L2DbarEstimates.BasicIdentity.Imports
namespace ReciprocityTheory.L2DbarEstimates.E

open MeasureTheory
open scoped ComplexConjugate

noncomputable section

theorem ap (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M] : APStatement n M := by
  intro z hz ph ψ ε f hph hψ hε hf
  have hph1 : CkR n z 1 ph := Ck.mono n z 1 2 (by norm_num) _ hph
  have hf1 : ∀ j, Ck n z 1 (fun y => f y j) := fun j => Ck.mono n z 1 2 (by norm_num) _ (hf j).1

  have hphc : Continuous ph := Complex.continuous_re.comp (Ck.continuous n z hz 2 _ hph)
  have hEr : Continuous (fun x => Real.exp (-ph x)) := Real.continuous_exp.comp hphc.neg
  have hFc : ∀ j, Continuous (fun y => f y j) := fun j => Ck.continuous n z hz 2 _ (hf j).1
  have hTc : ∀ j, Continuous (dTw n z ph j (fun y => f y j)) :=
    fun j => Ck.continuous n z hz 1 _ (ck_dTw n z 1 ph j _ hph (hf j).1)
  have hDc : ∀ j k, Continuous (db n z k (fun y => f y j)) :=
    fun j k => Ck.continuous n z hz 1 _ (Ck.db n z 1 k _ (hf j).1)
  have hLc : ∀ j k, Continuous (d n z j (db n z k (fun y => (ph y : ℂ)))) :=
    fun j k => Ck.continuous n z hz 0 _ (Ck.d n z 0 j _ (Ck.db n z 1 k _ hph))
  have hψc : ∀ j, Continuous (d n z j (fun y => (ψ y : ℂ))) :=
    fun j => Ck.continuous n z hz 0 _ (Ck.d n z 0 j _ hψ)
  have hAc : Continuous (fun x => ∑ j, dTw n z ph j (fun y => f y j) x) :=
    continuous_finsetSum _ (fun j _ => hTc j)
  have hSc : Continuous (fun x => ∑ j, (dTw n z ph j (fun y => f y j) x +
      f x j * d n z j (fun y => (ψ y : ℂ)) x)) :=
    continuous_finsetSum _ (fun j _ => (hTc j).add ((hFc j).mul (hψc j)))
  have hLevic : Continuous (fun x => (Levi n z ph x (fun j => f x j)).re) := by
    unfold Levi
    exact Complex.continuous_re.comp (continuous_finsetSum _ (fun j _ =>
      continuous_finsetSum _ (fun k _ =>
        ((hLc j k).mul (hFc j)).mul (Complex.continuous_conj.comp (hFc k)))))
  have hGc : Continuous (fun x => ∑ j, ∑ k, ‖db n z k (fun y => f y j) x‖ ^ 2) :=
    continuous_finsetSum _ (fun j _ => continuous_finsetSum _ (fun k _ => (hDc j k).norm.pow 2))
  have hdSc : Continuous (fun x => dSqR n z ψ x) :=
    continuous_finsetSum _ (fun j _ => (hψc j).norm.pow 2)
  have hF2c : Continuous (fun x => ∑ j, ‖f x j‖ ^ 2) :=
    continuous_finsetSum _ (fun j _ => (hFc j).norm.pow 2)

  set K : Set M := ⋃ j, tsupport (fun y => f y j) with hKdef
  have hK : IsCompact K := isCompact_iUnion (fun j => (hf j).2)
  have hcs : ∀ g : M → ℝ, (∀ x, x ∉ K → g x = 0) → HasCompactSupport g :=
    fun g hg => HasCompactSupport.intro hK hg
  have v0 : ∀ x, x ∉ K → ∀ j, f x j = 0 := fun x hx j =>
    image_eq_zero_of_notMem_tsupport (f := fun y => f y j) (x := x)
      (fun h => hx (Set.mem_iUnion.2 ⟨j, h⟩))
  have vD : ∀ x, x ∉ K → ∀ j k, db n z k (fun y => f y j) x = 0 := fun x hx j k =>
    image_eq_zero_of_notMem_tsupport
      (fun h => hx (Set.mem_iUnion.2 ⟨j, tsupport_db_subset n z k _ h⟩))
  have vT : ∀ x, x ∉ K → ∀ j, dTw n z ph j (fun y => f y j) x = 0 := fun x hx j =>
    image_eq_zero_of_notMem_tsupport
      (fun h => hx (Set.mem_iUnion.2 ⟨j, tsupport_dTw_subset n z ph j _ h⟩))
  have hnf : ∀ x, ‖f x‖ ^ 2 = ∑ j, ‖f x j‖ ^ 2 := fun x => EuclideanSpace.norm_sq_eq (f x)

  have iL : Integrable (fun x => (Levi n z ph x (fun j => f x j)).re * Real.exp (-ph x))
      (vol n z) :=
    integrable_of_continuous_real n z hz _ (hLevic.mul hEr)
      (hcs _ (fun x hx => by simp [Levi, v0 x hx]))
  have iG : Integrable (fun x => (∑ j, ∑ k, ‖db n z k (fun y => f y j) x‖ ^ 2) *
      Real.exp (-ph x)) (vol n z) :=
    integrable_of_continuous_real n z hz _ (hGc.mul hEr)
      (hcs _ (fun x hx => by simp [vD x hx]))
  have iA : Integrable (fun x => ‖∑ j, dTw n z ph j (fun y => f y j) x‖ ^ 2 *
      Real.exp (-ph x)) (vol n z) :=
    integrable_of_continuous_real n z hz _ ((hAc.norm.pow 2).mul hEr)
      (hcs _ (fun x hx => by simp [vT x hx]))
  have iS : Integrable (fun x => ‖∑ j, (dTw n z ph j (fun y => f y j) x +
      f x j * d n z j (fun y => (ψ y : ℂ)) x)‖ ^ 2 * Real.exp (-ph x)) (vol n z) :=
    integrable_of_continuous_real n z hz _ ((hSc.norm.pow 2).mul hEr)
      (hcs _ (fun x hx => by simp [vT x hx, v0 x hx]))
  have i1 : Integrable (fun x => ((Levi n z ph x (fun j => f x j)).re -
      (1 + 1 / ε) * dSqR n z ψ x * ‖f x‖ ^ 2) * Real.exp (-ph x)) (vol n z) := by
    simp only [hnf]
    exact integrable_of_continuous_real n z hz _
      ((hLevic.sub ((continuous_const.mul hdSc).mul hF2c)).mul hEr)
      (hcs _ (fun x hx => by simp [Levi, v0 x hx]))

  have hpt : ∀ x, ((Levi n z ph x (fun j => f x j)).re -
      (1 + 1 / ε) * dSqR n z ψ x * ‖f x‖ ^ 2) * Real.exp (-ph x) ≤
      (Levi n z ph x (fun j => f x j)).re * Real.exp (-ph x) +
        (∑ j, ∑ k, ‖db n z k (fun y => f y j) x‖ ^ 2) * Real.exp (-ph x) -
        ‖∑ j, dTw n z ph j (fun y => f y j) x‖ ^ 2 * Real.exp (-ph x) +
        (1 + ε) * (‖∑ j, (dTw n z ph j (fun y => f y j) x +
          f x j * d n z j (fun y => (ψ y : ℂ)) x)‖ ^ 2 * Real.exp (-ph x)) := by
    intro x
    have hsplit : (∑ j, (dTw n z ph j (fun y => f y j) x +
        f x j * d n z j (fun y => (ψ y : ℂ)) x)) =
        (∑ j, dTw n z ph j (fun y => f y j) x) +
          ∑ j, f x j * d n z j (fun y => (ψ y : ℂ)) x := Finset.sum_add_distrib
    have h1 := norm_sq_le_split (∑ j, dTw n z ph j (fun y => f y j) x)
      (∑ j, f x j * d n z j (fun y => (ψ y : ℂ)) x) ε hε
    rw [← hsplit] at h1
    have h2 := norm_sum_mul_sq_le (fun j => f x j) (fun j => d n z j (fun y => (ψ y : ℂ)) x)
    have hc : 0 ≤ 1 + 1 / ε := by positivity
    have he : 0 < Real.exp (-ph x) := Real.exp_pos _
    have hG0 : 0 ≤ ∑ j, ∑ k, ‖db n z k (fun y => f y j) x‖ ^ 2 := by positivity
    have h3 : ‖∑ j, dTw n z ph j (fun y => f y j) x‖ ^ 2 ≤
        (1 + ε) * ‖∑ j, (dTw n z ph j (fun y => f y j) x +
          f x j * d n z j (fun y => (ψ y : ℂ)) x)‖ ^ 2 +
          (1 + 1 / ε) * (dSqR n z ψ x * ‖f x‖ ^ 2) := by
      rw [hnf x]
      unfold dSqR
      nlinarith [mul_le_mul_of_nonneg_left h2 hc]
    nlinarith [mul_le_mul_of_nonneg_right h3 he.le, mul_nonneg hG0 he.le]

  have hmono : ∫ x, ((Levi n z ph x (fun j => f x j)).re - (1 + 1 / ε) * dSqR n z ψ x * ‖f x‖ ^ 2) * Real.exp (-ph x) ∂vol n z ≤
      (∫ x, (Levi n z ph x (fun j => f x j)).re * Real.exp (-ph x) ∂vol n z) +
        (∫ x, (∑ j, ∑ k, ‖db n z k (fun y => f y j) x‖ ^ 2) * Real.exp (-ph x) ∂vol n z) -
        (∫ x, ‖∑ j, dTw n z ph j (fun y => f y j) x‖ ^ 2 * Real.exp (-ph x) ∂vol n z) +
        (1 + ε) * ∫ x, ‖∑ j, (dTw n z ph j (fun y => f y j) x + f x j * d n z j (fun y => (ψ y : ℂ)) x)‖ ^ 2 * Real.exp (-ph x) ∂vol n z := by
    have j1 : Integrable (fun x => (Levi n z ph x (fun j => f x j)).re * Real.exp (-ph x) +
        (∑ j, ∑ k, ‖db n z k (fun y => f y j) x‖ ^ 2) * Real.exp (-ph x)) (vol n z) := iL.add iG
    have j2 : Integrable (fun x => (Levi n z ph x (fun j => f x j)).re * Real.exp (-ph x) +
        (∑ j, ∑ k, ‖db n z k (fun y => f y j) x‖ ^ 2) * Real.exp (-ph x) - ‖∑ j, dTw n z ph j (fun y => f y j) x‖ ^ 2 * Real.exp (-ph x)) (vol n z) := j1.sub iA
    have j3 : Integrable (fun x => (1 + ε) * (‖∑ j, (dTw n z ph j (fun y => f y j) x + f x j * d n z j (fun y => (ψ y : ℂ)) x)‖ ^ 2 * Real.exp (-ph x))) (vol n z) := iS.const_mul (1 + ε)
    rw [← integral_add iL iG, ← integral_sub j1 iA, ← integral_const_mul, ← integral_add j2 j3]
    exact integral_mono i1 (j2.add j3) hpt
  have hB := basicIdentity n M z hz ph f hph hf
  have hT : ∫ x, ‖tstar n z (fun y => ph y - 2 * ψ y) (fun y => ph y - ψ y) f x‖ ^ 2 *
      Real.exp (-(ph x - 2 * ψ x)) ∂vol n z =
      ∫ x, ‖∑ j, (dTw n z ph j (fun y => f y j) x +
        f x j * d n z j (fun y => (ψ y : ℂ)) x)‖ ^ 2 * Real.exp (-ph x) ∂vol n z := by
    congr 1
    funext x
    exact tstar_norm_sq n z hz ph ψ f hph1 hψ hf1 x
  rw [hT]
  linarith

end

end ReciprocityTheory.L2DbarEstimates.E
end

section -- merged from ReciprocityTheory.L2DbarEstimates.LeviForms.IntegrableWd
universe u

namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology Set
open scoped ENNReal ContDiff

noncomputable section

namespace MongeAmpereIntegrability

variable {n : ℕ}

theorem integrable_wd {H : V n → ℂ} (hH : ContDiff ℝ 1 H) (hc : HasCompactSupport H)
    (j : Fin n) : Integrable (wd n j H) := by
  have h1 : Continuous fun y => fderiv ℝ H y (bas n j) :=
    (hH.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have h2 : Continuous fun y => fderiv ℝ H y (Complex.I • bas n j) :=
    (hH.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hcont : Continuous (wd n j H) := (h1.sub (continuous_const.mul h2)).div_const 2
  refine hcont.integrable_of_hasCompactSupport (HasCompactSupport.intro hc.isCompact fun y hy => ?_)
  exact (wd_zero_of_eqOn (isClosed_tsupport H).isOpen_compl
    (fun w hw => image_eq_zero_of_notMem_tsupport hw) j hy).1

end MongeAmpereIntegrability

theorem ma (n : ℕ) (hCof : MACofStatement n) : MAStatement n := by
  intro Ω ph v hΩ hph hv hvc hsub
  have hvo : ContDiffOn ℝ ∞ v Ω := hv.contDiffOn
  have hP : ContDiffOn ℝ ∞ (fun w => (ph w : ℂ)) Ω := MongeAmpereIntegrability.cdo_ofReal hph
  have hQ : ContDiffOn ℝ ∞ (fun w => (v w : ℂ)) univ := MongeAmpereIntegrability.cdo_ofReal hv.contDiffOn
  have hKc : IsOpen (tsupport v)ᶜ := (isClosed_tsupport v).isOpen_compl
  have hv0 : ∀ w ∈ (tsupport v)ᶜ, (v w : ℂ) = 0 := fun w hw => by
    simp [image_eq_zero_of_notMem_tsupport hw]
  have hQ1 : ∀ k, ∀ w ∈ (tsupport v)ᶜ, wdb n k (fun w => (v w : ℂ)) w = 0 := fun k w hw =>
    (MongeAmpereIntegrability.wd_zero_of_eqOn hKc hv0 k hw).2
  have hB0 : ∀ y ∉ tsupport v, cHess n (fun w => (v w : ℂ)) y = 0 := by
    intro y hy
    ext j k
    simp only [cHess, Matrix.of_apply, Matrix.zero_apply]
    exact (MongeAmpereIntegrability.wd_zero_of_eqOn hKc (hQ1 k) j hy).1
  have hQ1c : ∀ k, ContDiffOn ℝ ∞ (wdb n k (fun w => (v w : ℂ))) univ := fun k =>
    (MongeAmpereIntegrability.cdo_wd isOpen_univ hQ k).2
  have hBc : ∀ j k, ContDiffOn ℝ ∞ (fun y => cHess n (fun w => (v w : ℂ)) y j k) univ := by
    intro j k
    simp only [cHess, Matrix.of_apply]
    exact (MongeAmpereIntegrability.cdo_wd isOpen_univ (hQ1c k) j).1
  have hAc : ∀ j k, ContDiffOn ℝ ∞ (fun y => cHess n (fun w => (ph w : ℂ)) y j k) Ω := by
    intro j k
    simp only [cHess, Matrix.of_apply]
    exact (MongeAmpereIntegrability.cdo_wd hΩ (MongeAmpereIntegrability.cdo_wd hΩ hP k).2 j).1
  set D : ℝ → V n → ℂ := fun t y => ∑ k, ∑ j,
    (cHess n (fun w => (ph w : ℂ)) y + (t : ℂ) • cHess n (fun w => (v w : ℂ)) y).adjugate k j *
      cHess n (fun w => (v w : ℂ)) y j k with hD
  have hD0 : ∀ t, ∀ y ∉ tsupport v, D t y = 0 := by
    intro t y hy
    simp [hD, hB0 y hy]
  have hm : ∀ y (t : ℝ), cHess n (fun w => (ph w : ℂ)) y + (t : ℂ) • cHess n (fun w => (v w : ℂ)) y =
      Matrix.of fun i j => cHess n (fun w => (ph w : ℂ)) y i j +
        (t : ℂ) * cHess n (fun w => (v w : ℂ)) y i j := by
    intro y t; ext i j; simp
  have hDc : ContinuousOn (fun p : V n × ℝ => D p.2 p.1) (Ω ×ˢ univ) := by
    simp only [hD, hm]
    refine continuousOn_finsetSum _ fun k _ => continuousOn_finsetSum _ fun j _ =>
      ContinuousOn.mul ?_ ?_
    · refine MongeAmpereIntegrability.cont_adj (fun i l (p : V n × ℝ) => cHess n (fun w => (ph w : ℂ)) p.1 i l +
        (p.2 : ℂ) * cHess n (fun w => (v w : ℂ)) p.1 i l) (fun i l => ?_) k j
      have h1 : ContinuousOn (fun p : V n × ℝ => cHess n (fun w => (ph w : ℂ)) p.1 i l)
          (Ω ×ˢ univ) := (hAc i l).continuousOn.comp continuousOn_fst fun p hp => hp.1
      have h2 : ContinuousOn (fun p : V n × ℝ => cHess n (fun w => (v w : ℂ)) p.1 i l)
          (Ω ×ˢ univ) := (hBc i l).continuousOn.comp continuousOn_fst fun p _ => mem_univ _
      have h3 : ContinuousOn (fun p : V n × ℝ => (p.2 : ℂ)) (Ω ×ˢ univ) :=
        (Complex.continuous_ofReal.comp continuous_snd).continuousOn
      exact h1.add (h3.mul h2)
    · exact (hBc j k).continuousOn.comp continuousOn_fst fun p _ => mem_univ _
  have hFTC : ∀ y, ∫ t in (0 : ℝ)..1, D t y =
      (cHess n (fun w => (ph w : ℂ)) y + cHess n (fun w => (v w : ℂ)) y).det -
        (cHess n (fun w => (ph w : ℂ)) y).det := by
    intro y
    have hcont : Continuous fun t : ℝ => D t y := by
      rw [← continuousOn_univ]
      simp only [hD, hm]
      refine continuousOn_finsetSum _ fun k _ => continuousOn_finsetSum _ fun j _ =>
        ContinuousOn.mul ?_ continuousOn_const
      exact MongeAmpereIntegrability.cont_adj (fun i l (t : ℝ) => cHess n (fun w => (ph w : ℂ)) y i l +
        (t : ℂ) * cHess n (fun w => (v w : ℂ)) y i l)
        (fun i l => (continuous_const.add
          (Complex.continuous_ofReal.mul continuous_const)).continuousOn) k j
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => MongeAmpereIntegrability.hasDerivAt_det (cHess n (fun w => (ph w : ℂ)) y)
        (cHess n (fun w => (v w : ℂ)) y) t) (hcont.intervalIntegrable 0 1)]
    simp
  have hDint : ∀ t : ℝ, ∫ y in Ω, D t y = 0 := by
    intro t
    set f : V n → ℝ := fun w => ph w + t * v w with hf_def
    have hf : ContDiffOn ℝ ∞ f Ω := hph.add (contDiffOn_const.mul hvo)
    have hF : ContDiffOn ℝ ∞ (fun w => (f w : ℂ)) Ω := MongeAmpereIntegrability.cdo_ofReal hf
    have hHc : ∀ k j, ContDiffOn ℝ ∞
        (fun w => (cHess n (fun w' => (f w' : ℂ)) w).adjugate k j) Ω := fun k j =>
      MongeAmpereIntegrability.cdo_adj (fun i l w => wd n i (wdb n l (fun w' => (f w' : ℂ))) w)
        (fun i l => (MongeAmpereIntegrability.cdo_wd hΩ (MongeAmpereIntegrability.cdo_wd hΩ hF l).2 i).1) k j
    set G : Fin n → Fin n → V n → ℂ := fun k j w =>
      (cHess n (fun w' => (f w' : ℂ)) w).adjugate k j * wdb n k (fun w => (v w : ℂ)) w with hG
    have hG0 : ∀ k j, ∀ w ∉ tsupport v, G k j w = 0 := fun k j w hw => by
      simp [hG, hQ1 k w hw]
    have hGc : ∀ k j, ContDiff ℝ 1 (G k j) := by
      intro k j
      rw [contDiff_iff_contDiffAt]
      intro w
      by_cases hw : w ∈ Ω
      · exact (((hHc k j).mul ((hQ1c k).mono (subset_univ _))).contDiffAt
          (hΩ.mem_nhds hw)).of_le (by simp)
      · have hwK : w ∉ tsupport v := fun h => hw (hsub h)
        have he : G k j =ᶠ[𝓝 w] fun _ => (0 : ℂ) :=
          Filter.eventually_of_mem (hKc.mem_nhds hwK) fun x hx => hG0 k j x hx
        exact contDiffAt_const.congr_of_eventuallyEq he
    have hGs : ∀ k j, HasCompactSupport (G k j) := fun k j =>
      HasCompactSupport.intro hvc.isCompact (hG0 k j)
    have hpt : ∀ y, D t y = ∑ k, ∑ j, wd n j (G k j) y := by
      intro y
      by_cases hy : y ∈ Ω
      · have hHy : cHess n (fun w' => (f w' : ℂ)) y = cHess n (fun w => (ph w : ℂ)) y +
            (t : ℂ) • cHess n (fun w => (v w : ℂ)) y := MongeAmpereIntegrability.cHess_add_smul hΩ hph hvo t hy
        simp only [hD]
        rw [← hHy]
        refine Finset.sum_congr rfl fun k _ => ?_
        have hc := hCof Ω f hΩ hf y hy k
        have d1 : ∀ j, DifferentiableAt ℝ
            (fun w => (cHess n (fun w' => (f w' : ℂ)) w).adjugate k j) y := fun j =>
          ((hHc k j).differentiableOn (by simp)).differentiableAt (hΩ.mem_nhds hy)
        have d2 : DifferentiableAt ℝ (wdb n k (fun w => (v w : ℂ))) y :=
          ((hQ1c k).differentiableOn (by simp)).differentiableAt Filter.univ_mem
        have e : ∀ j, wd n j (G k j) y =
            wd n j (fun w => (cHess n (fun w' => (f w' : ℂ)) w).adjugate k j) y *
              wdb n k (fun w => (v w : ℂ)) y +
            (cHess n (fun w' => (f w' : ℂ)) y).adjugate k j *
              wd n j (wdb n k (fun w => (v w : ℂ))) y := fun j =>
          ChartWirtingerDerivatives.wd_mul' n j _ _ y (d1 j) d2
        simp only [e, Finset.sum_add_distrib, ← Finset.sum_mul, hc, zero_mul, zero_add]
        rfl
      · have hyK : y ∉ tsupport v := fun h => hy (hsub h)
        rw [hD0 t y hyK]
        symm
        refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun j _ => ?_
        exact (MongeAmpereIntegrability.wd_zero_of_eqOn hKc (hG0 k j) j hyK).1
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun y hy => hD0 t y (fun h => hy (hsub h)))]
    simp_rw [hpt]
    rw [integral_finsetSum _ (fun k _ => integrable_finsetSum _ fun j _ =>
      MongeAmpereIntegrability.integrable_wd (hGc k j) (hGs k j) j)]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [integral_finsetSum _ (fun j _ => MongeAmpereIntegrability.integrable_wd (hGc k j) (hGs k j) j)]
    exact Finset.sum_eq_zero fun j _ => integral_wd_eq_zero n j (G k j) (hGc k j) (hGs k j)
  have hInt : Integrable (Function.uncurry fun (y : V n) (t : ℝ) => D t y)
      ((volume.restrict Ω).prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
    rw [Measure.prod_restrict]
    refine IntegrableOn.of_forall_sdiff_eq_zero (s := tsupport v ×ˢ Icc (0 : ℝ) 1) ?_
      (hΩ.measurableSet.prod measurableSet_Ioc) ?_
    · exact ContinuousOn.integrableOn_compact (hvc.isCompact.prod isCompact_Icc)
        (hDc.mono fun p hp => ⟨hsub hp.1, mem_univ _⟩)
    · rintro ⟨y, t⟩ ⟨⟨_, ht⟩, hn⟩
      have hyK : y ∉ tsupport v := fun h => hn ⟨h, Ioc_subset_Icc_self ht⟩
      exact hD0 t y hyK
  calc ∫ y in Ω, ((cHess n (fun w => ((ph w + v w : ℝ) : ℂ)) y).det -
        (cHess n (fun w => (ph w : ℂ)) y).det)
      = ∫ y in Ω, ∫ t in Ioc (0 : ℝ) 1, D t y := by
        refine setIntegral_congr_fun hΩ.measurableSet fun y hy => ?_
        have h1 := MongeAmpereIntegrability.cHess_add_smul hΩ hph hvo 1 hy
        simp only [one_mul, Complex.ofReal_one, one_smul] at h1
        rw [h1, ← intervalIntegral.integral_of_le zero_le_one, hFTC y]
    _ = ∫ t in Ioc (0 : ℝ) 1, ∫ y in Ω, D t y := integral_integral_swap hInt
    _ = 0 := by simp [hDint]

end

end ReciprocityTheory.L2DbarEstimates.I
end

section -- merged from ReciprocityTheory.L2DbarEstimates.LeviForms.FixedC
universe u

namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology Set
open scoped ENNReal ContDiff

noncomputable section

theorem fx_lp_norm_sq_eq {α : Type*} [MeasurableSpace α] (μ : Measure α) (v : Lp ℂ 2 μ)
    (G : α → ℂ) (h : (v : α → ℂ) =ᵐ[μ] G) :
    eLpNorm G 2 μ ^ (2 : ℝ) = ENNReal.ofReal (‖v‖ ^ 2) := by
  rw [eLpNorm_congr_ae h.symm, Lp.norm_def, ENNReal.ofReal_pow ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top v), ENNReal.rpow_two]

end

end ReciprocityTheory.L2DbarEstimates.I
end

section -- merged from ReciprocityTheory.L2DbarEstimates.LeviForms.Bergman
universe u

namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff NNReal

noncomputable section

section
variable {M : Type u} [TopologicalSpace M] [MeasurableSpace M]

def bgDens (ps : M → ℝ) (x : M) : ℝ≥0 := Real.toNNReal (Real.exp (-ps x))

def bgMeas (n : ℕ) (z : M → V n) (ps : M → ℝ) : Measure M :=
  (vol n z).withDensity (fun x => (bgDens ps x : ℝ≥0∞))

theorem bg_wint_eq_lintegral (n : ℕ) (z : M → V n) (ps : M → ℝ) (hps : Measurable ps) (f : M → ℂ) :
    wint n z f ps = ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) ∂bgMeas n z ps := by
  have hm : Measurable (fun x => (bgDens ps x : ℝ≥0∞)) :=
    ((Real.measurable_exp.comp hps.neg).real_toNNReal).coe_nnreal_ennreal
  unfold bgMeas wint
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable _ hm
    (Filter.Eventually.of_forall fun x => ENNReal.coe_lt_top)]
  refine lintegral_congr fun x => ?_
  simp only [Pi.mul_apply, bgDens]
  rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
    Real.rpow_two, mul_comm (‖f x‖ ^ 2), ENNReal.ofReal_mul (Real.exp_pos _).le]
  rfl

theorem bg_eLpNorm_two_eq (n : ℕ) (z : M → V n) (ps : M → ℝ) (hps : Measurable ps) (f : M → ℂ) :
    eLpNorm' f 2 (bgMeas n z ps) = wint n z f ps ^ (1/(2:ℝ)) := by
  rw [eLpNorm'_eq_lintegral_eNorm, bg_wint_eq_lintegral n z ps hps f]

theorem bg_memLp_of_wint (n : ℕ) (z : M → V n) (ps : M → ℝ) (hps : Measurable ps) (f : M → ℂ)
    (hf : AEStronglyMeasurable f (bgMeas n z ps)) (h : wint n z f ps < ⊤) :
    MemLp f 2 (bgMeas n z ps) := by
  change eLpNorm f 2 (bgMeas n z ps) < ⊤
  rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num) hf, ENNReal.toReal_ofNat, bg_eLpNorm_two_eq n z ps hps f]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) h.ne

theorem bg_wint_lt_top_of_memLp (n : ℕ) (z : M → V n) (ps : M → ℝ) (hps : Measurable ps) (f : M → ℂ)
    (hf : MemLp f 2 (bgMeas n z ps)) : wint n z f ps < ⊤ := by
  have h : eLpNorm f 2 (bgMeas n z ps) < ⊤ := hf
  rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num) hf.aestronglyMeasurable, ENNReal.toReal_ofNat, bg_eLpNorm_two_eq n z ps hps f] at h
  exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num)).1 h

end

variable {M : Type u} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]

def bgHoloSub (n : ℕ) (z : M → V n) (ps : M → ℝ) : Submodule ℂ (Lp ℂ 2 (bgMeas n z ps)) where
  carrier := {f | ∃ G, Holo n z G ∧ (f : M → ℂ) =ᵐ[bgMeas n z ps] G}
  add_mem' := by
    rintro f g ⟨F, hF, hf⟩ ⟨G, hG, hg⟩
    refine ⟨F + G, fun e he => (hF e he).add (hG e he), ?_⟩
    filter_upwards [Lp.coeFn_add f g, hf, hg] with x h1 h2 h3
    rw [h1, Pi.add_apply, Pi.add_apply, h2, h3]
  zero_mem' := ⟨0, fun e _ => differentiableOn_const (0 : ℂ), Lp.coeFn_zero _ _ _⟩
  smul_mem' := by
    rintro c f ⟨F, hF, hf⟩
    refine ⟨c • F, fun e he => (hF e he).const_smul c, ?_⟩
    filter_upwards [Lp.coeFn_smul c f, hf] with x h1 h2
    rw [h1, Pi.smul_apply, Pi.smul_apply, h2]

theorem bgHoloSub_closed (n : ℕ) (X : EtaleStein n M) (ps : M → ℝ) (hps : SmoothR n X.z ps)
    (hpsm : Measurable ps) (hC : HoloClosedNeed n M) :
    IsClosed (bgHoloSub n X.z ps : Set (Lp ℂ 2 (bgMeas n X.z ps))) := by
  refine isClosed_of_closure_subset fun f hf => ?_
  obtain ⟨F, hFS, hF⟩ := mem_closure_iff_seq_limit.1 hf
  have hFS' : ∀ k, ∃ G, Holo n X.z G ∧ (F k : M → ℂ) =ᵐ[bgMeas n X.z ps] G := fun k => hFS k
  choose G hG hGe using hFS'
  have hfa := Lp.aestronglyMeasurable f
  have hf0m : Measurable (hfa.mk (f : M → ℂ)) := hfa.stronglyMeasurable_mk.measurable
  have hf0 : (f : M → ℂ) =ᵐ[bgMeas n X.z ps] hfa.mk (f : M → ℂ) := hfa.ae_eq_mk
  have hw : ∀ k, wint n X.z (fun x => G k x - hfa.mk (f : M → ℂ) x) ps =
      (eLpNorm (⇑(F k) - ⇑f) 2 (bgMeas n X.z ps)) ^ (2 : ℝ) := by
    intro k
    have h1 := bg_eLpNorm_two_eq n X.z ps hpsm (fun x => G k x - hfa.mk (f : M → ℂ) x)
    have h2 : eLpNorm' (fun x => G k x - hfa.mk (f : M → ℂ) x) 2 (bgMeas n X.z ps) =
        eLpNorm' (⇑(F k) - ⇑f) 2 (bgMeas n X.z ps) := by
      apply eLpNorm'_congr_ae
      filter_upwards [hGe k, hf0] with x h3 h4
      rw [Pi.sub_apply, h3, h4]
    rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num)
      ((Lp.aestronglyMeasurable (F k)).sub (Lp.aestronglyMeasurable f)), ENNReal.toReal_ofNat, ← h2, h1, ← ENNReal.rpow_mul]
    norm_num
  have ht := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' F f).1 hF
  have hw0 : Tendsto (fun k => wint n X.z (fun x => G k x - hfa.mk (f : M → ℂ) x) ps) atTop (𝓝 0) := by
    simp_rw [hw]
    have := ((ENNReal.continuous_rpow_const (y := (2 : ℝ))).tendsto 0).comp ht
    rw [ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2)] at this
    exact this
  obtain ⟨G0, hG0, hfe⟩ := hC X ps G (hfa.mk (f : M → ℂ)) hps hG hf0m hw0
  show ∃ G, Holo n X.z G ∧ (f : M → ℂ) =ᵐ[bgMeas n X.z ps] G
  refine ⟨G0, hG0, hf0.trans ?_⟩
  exact (withDensity_absolutelyContinuous (vol n X.z) _ : bgMeas n X.z ps ≪ vol n X.z).ae_eq hfe

theorem bergmanExists (n : ℕ) (M : Type u) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    (hC : HoloClosedNeed n M) : BergmanExistsStatement n M := by
  intro X ps F0 hps hF0 hw
  have hpsc : Continuous ps := by
    have := Smooth.continuous n X.z X.isLocalHomeomorph _ hps
    exact (Complex.continuous_re.comp this).congr fun x => by simp
  have hpsm : Measurable ps := hpsc.measurable
  have hF0L : MemLp F0 2 (bgMeas n X.z ps) :=
    bg_memLp_of_wint n X.z ps hpsm F0 hF0.aestronglyMeasurable hw
  have hK : IsClosed (bgHoloSub n X.z ps : Set (Lp ℂ 2 (bgMeas n X.z ps))) :=
    bgHoloSub_closed n X ps hps hpsm hC
  haveI : CompleteSpace (bgHoloSub n X.z ps) := hK.completeSpace_coe
  set K := bgHoloSub n X.z ps with hKdef
  set P : Lp ℂ 2 (bgMeas n X.z ps) := (K.orthogonalProjection (hF0L.toLp F0) : Lp ℂ 2 (bgMeas n X.z ps))
    with hPdef
  have hPK : ∃ G, Holo n X.z G ∧ (P : M → ℂ) =ᵐ[bgMeas n X.z ps] G :=
    (K.orthogonalProjection (hF0L.toLp F0)).2
  obtain ⟨G, hG, hPG⟩ := hPK
  refine ⟨G, hG, bg_wint_lt_top_of_memLp n X.z ps hpsm G (MemLp.ae_eq hPG (Lp.memLp P)), ?_⟩
  intro H hH hwH
  have hHc : Continuous H := Smooth.continuous n X.z X.isLocalHomeomorph H (Holo.smooth n X.z H hH)
  have hHL : MemLp H 2 (bgMeas n X.z ps) :=
    bg_memLp_of_wint n X.z ps hpsm H hHc.aestronglyMeasurable hwH
  have hHK : hHL.toLp H ∈ K := show ∃ G, Holo n X.z G ∧ _ from ⟨H, hH, hHL.coeFn_toLp⟩
  have horth : inner ℂ (hHL.toLp H : Lp ℂ 2 (bgMeas n X.z ps)) (hF0L.toLp F0 - P) = 0 := by
    first
    | exact Submodule.inner_right_of_mem_orthogonal hHK (K.sub_starProjection_mem_orthogonal _)
    | exact Submodule.inner_right_of_mem_orthogonal hHK (K.sub_orthogonalProjection_mem_orthogonal _)
    | exact Submodule.inner_right_of_mem_orthogonal hHK (sub_orthogonalProjection_mem_orthogonal _)
    | exact orthogonalProjection_inner_eq_zero _ _ hHK
  rw [MeasureTheory.L2.inner_def] at horth
  have hint : ∫ a, inner ℂ ((hHL.toLp H : Lp ℂ 2 (bgMeas n X.z ps)) a)
      ((hF0L.toLp F0 - P : Lp ℂ 2 (bgMeas n X.z ps)) a) ∂(bgMeas n X.z ps) =
      ∫ a, (starRingEnd ℂ) (H a) * (F0 a - G a) ∂(bgMeas n X.z ps) := by
    refine integral_congr_ae ?_
    filter_upwards [hHL.coeFn_toLp, hF0L.coeFn_toLp, Lp.coeFn_sub (hF0L.toLp F0) P, hPG] with a h1 h2 h3 h4
    rw [h3, Pi.sub_apply, h1, h2, h4]
    simp [RCLike.inner_apply]
    try ring
  have hdm : Measurable (bgDens ps) := (Real.measurable_exp.comp hpsm.neg).real_toNNReal
  have key : ∫ x, (F0 x - G x) * (starRingEnd ℂ) (H x) * (Real.exp (-ps x) : ℂ) ∂vol n X.z =
      ∫ a, (starRingEnd ℂ) (H a) * (F0 a - G a) ∂(bgMeas n X.z ps) := by
    rw [bgMeas, integral_withDensity_eq_integral_smul hdm]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [bgDens, NNReal.smul_def, Real.coe_toNNReal _ (Real.exp_pos _).le, Complex.real_smul]
    ring
  rw [key, ← hint]
  exact horth

end

end ReciprocityTheory.L2DbarEstimates.I
end

section -- merged from ReciprocityTheory.L2DbarEstimates.LeviForms.ImportsAlt
universe u

namespace ReciprocityTheory.L2DbarEstimates.I

theorem tw (n : ℕ) (M : Type u) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M] (hH : HStatement n M) (hC : HoloClosedNeed n M) :
    TWStatement n M := by
  intro X ps Ph F0 a b hps hPh hCb hlevi hF0 hF0w ha hb ha0 hb0 _ hA hB
  refine ⟨bergmanExists n M hC X ps F0 hps
    (Smooth.continuous n X.z X.isLocalHomeomorph F0 hF0).measurable hF0w, ?_⟩
  exact twBound n M hH X ps Ph F0 a b hps hPh hCb hlevi hF0 hF0w ha hb ha0 hb0 hA hB

end ReciprocityTheory.L2DbarEstimates.I
end

section -- merged from ReciprocityTheory.L2DbarEstimates.Mollifiers.MollGraph
namespace ReciprocityTheory.L2DbarEstimates.B

open MeasureTheory Filter Topology Set Metric
open scoped Convolution ContDiff ENNReal Pointwise

theorem moll_graph (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (ι : Type*) : GraphSt E μ ι := by
  intro l K hK m c v g w hw hg hw2
  refine ⟨fun k => moll_l2Tendsto E μ ι l K hK (g k) (hg k), ?_⟩
  refine (moll_l2Tendsto E μ ι l K hK w hw2).congr ?_
  intro i
  rw [moll_weakComm E μ m c v g w hw (K i)]

end ReciprocityTheory.L2DbarEstimates.B
end

section -- merged from ReciprocityTheory.L2DbarEstimates.LeviForms.PolarBallReal
universe u

namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology Module Set
open scoped ENNReal ContDiff

theorem polar_finrank (n : ℕ) : finrank ℝ (V n) = 2 * n := by
  rw [finrank_real_of_complex, finrank_euclideanSpace_fin]

private theorem nontrivial_V_of_one_le (n : ℕ) (hn : 1 ≤ n) : Nontrivial (ReciprocityTheory.L2DbarEstimates.V n) :=
  Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [polar_finrank]; omega)

theorem polar_ballReal (n : ℕ) (hn : 1 ≤ n) :
    (volume : Measure (V n)).real (ball 0 1) = Real.pi ^ n / (Nat.factorial n : ℝ) := by
  have hG : Real.Gamma (((2 * n : ℕ) : ℝ) / 2 + 1) = (n.factorial : ℝ) := by
    rw [show ((2 * n : ℕ) : ℝ) / 2 + 1 = (n : ℝ) + 1 by push_cast; ring]
    exact Real.Gamma_nat_eq_factorial n
  have hs : Real.sqrt Real.pi ^ (2 * n) = Real.pi ^ n := by
    rw [pow_mul, Real.sq_sqrt Real.pi_pos.le]
  have hpos : (0 : ℝ) ≤ Real.pi ^ n / (n.factorial : ℝ) := by positivity
  have := nontrivial_V_of_one_le n hn
  rw [measureReal_def, InnerProductSpace.volume_ball, polar_finrank, hG, hs,
    ENNReal.ofReal_one, one_pow, one_mul, ENNReal.toReal_ofReal hpos]

theorem polar_radial (n : ℕ) (hn : 1 ≤ n) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∫ y in Ioi (0:ℝ), y ^ (2 * n - 1) •
        (Icc (Real.sqrt a) (Real.sqrt b)).indicator (fun t : ℝ => (t ^ 2) ^ (-(n : ℝ))) y =
      Real.log (b / a) / 2 := by
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hb : 0 < b := ha.trans_le hab
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have hsab : Real.sqrt a ≤ Real.sqrt b := Real.sqrt_le_sqrt hab
  have hpt : ∀ y : ℝ, y ^ (2 * n - 1) •
      (Icc (Real.sqrt a) (Real.sqrt b)).indicator (fun t : ℝ => (t ^ 2) ^ (-(n : ℝ))) y =
        (Icc (Real.sqrt a) (Real.sqrt b)).indicator (fun t : ℝ => t⁻¹) y := by
    intro y
    classical
    rw [Set.indicator_apply, Set.indicator_apply]
    by_cases hy : y ∈ Icc (Real.sqrt a) (Real.sqrt b)
    · rw [if_pos hy, if_pos hy]
      have hy0 : 0 < y := hsa.trans_le hy.1
      rw [smul_eq_mul, Real.rpow_neg (by positivity), Real.rpow_natCast]
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega]
      have hsplit : (y ^ 2) ^ (k + 1) = y ^ (2 * k + 1) * y := by ring
      rw [hsplit, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hy0.ne'), one_mul]
    · rw [if_neg hy, if_neg hy, smul_zero]
  calc ∫ y in Ioi (0:ℝ), y ^ (2 * n - 1) •
        (Icc (Real.sqrt a) (Real.sqrt b)).indicator (fun t : ℝ => (t ^ 2) ^ (-(n : ℝ))) y
      = ∫ y in Ioi (0:ℝ), (Icc (Real.sqrt a) (Real.sqrt b)).indicator (fun t : ℝ => t⁻¹) y := by
        exact congrArg _ (funext hpt)
    _ = ∫ y in Icc (Real.sqrt a) (Real.sqrt b), y⁻¹ := by
        rw [integral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc,
          Set.inter_eq_left.mpr (show Icc (Real.sqrt a) (Real.sqrt b) ⊆ Ioi 0 from
            fun y hy => hsa.trans_le hy.1)]
    _ = Real.log (Real.sqrt b / Real.sqrt a) := by
        rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hsab,
          integral_inv_of_pos hsa hsb]
    _ = Real.log (b / a) / 2 := by
        rw [Real.log_div hsb.ne' hsa.ne', Real.log_sqrt hb.le, Real.log_sqrt ha.le,
          Real.log_div hb.ne' ha.ne']
        ring

theorem polar (n : ℕ) : PolarStatement n := by
  intro hn a b ha hab
  have := nontrivial_V_of_one_le n hn
  have hb : 0 < b := ha.trans_le hab
  have hsa0 := Real.sqrt_nonneg a
  have hsb0 := Real.sqrt_nonneg b
  have hsa : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha.le
  have hsb : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb.le
  have hmem : ∀ y : ReciprocityTheory.L2DbarEstimates.V n, (a ≤ ‖y‖ ^ 2 ∧ ‖y‖ ^ 2 ≤ b) ↔
      (Real.sqrt a ≤ ‖y‖ ∧ ‖y‖ ≤ Real.sqrt b) := by
    intro y
    have h0 := norm_nonneg y
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · calc Real.sqrt a ≤ Real.sqrt (‖y‖ ^ 2) := Real.sqrt_le_sqrt h1
          _ = ‖y‖ := Real.sqrt_sq h0
      · calc ‖y‖ = Real.sqrt (‖y‖ ^ 2) := (Real.sqrt_sq h0).symm
          _ ≤ Real.sqrt b := Real.sqrt_le_sqrt h2
    · rintro ⟨h1, h2⟩
      exact ⟨by nlinarith, by nlinarith⟩
  have hSc : IsClosed {y : ReciprocityTheory.L2DbarEstimates.V n | a ≤ ‖y‖ ^ 2 ∧ ‖y‖ ^ 2 ≤ b} := by
    have h1 : IsClosed {y : ReciprocityTheory.L2DbarEstimates.V n | a ≤ ‖y‖ ^ 2} :=
      isClosed_le continuous_const (continuous_norm.pow 2)
    have h2 : IsClosed {y : ReciprocityTheory.L2DbarEstimates.V n | ‖y‖ ^ 2 ≤ b} :=
      isClosed_le (continuous_norm.pow 2) continuous_const
    exact h1.inter h2
  have hsub : {y : ReciprocityTheory.L2DbarEstimates.V n | a ≤ ‖y‖ ^ 2 ∧ ‖y‖ ^ 2 ≤ b} ⊆ closedBall 0 (b + 1) := by
    intro y hy
    rw [mem_closedBall, dist_zero_right]
    have h0 := norm_nonneg y
    have h2 : ‖y‖ ^ 2 ≤ b := hy.2
    nlinarith [mul_self_nonneg (‖y‖ - 1)]
  have hK : IsCompact {y : ReciprocityTheory.L2DbarEstimates.V n | a ≤ ‖y‖ ^ 2 ∧ ‖y‖ ^ 2 ≤ b} :=
    (isCompact_closedBall (0 : ReciprocityTheory.L2DbarEstimates.V n) (b + 1)).of_isClosed_subset hSc hsub
  have hcont : ContinuousOn (fun y : ReciprocityTheory.L2DbarEstimates.V n => (‖y‖ ^ 2) ^ (-(n : ℝ)))
      {y : ReciprocityTheory.L2DbarEstimates.V n | a ≤ ‖y‖ ^ 2 ∧ ‖y‖ ^ 2 ≤ b} :=
    (continuous_norm.pow 2).continuousOn.rpow_const
      (fun y hy => Or.inl (ha.trans_le (hy : a ≤ ‖y‖ ^ 2 ∧ ‖y‖ ^ 2 ≤ b).1).ne')
  have hint_r : IntegrableOn (fun y : ReciprocityTheory.L2DbarEstimates.V n => (‖y‖ ^ 2) ^ (-(n : ℝ)))
      {y : ReciprocityTheory.L2DbarEstimates.V n | a ≤ ‖y‖ ^ 2 ∧ ‖y‖ ^ 2 ≤ b} volume :=
    hcont.integrableOn_compact hK
  have hnn : 0 ≤ᵐ[volume.restrict {y : ReciprocityTheory.L2DbarEstimates.V n | a ≤ ‖y‖ ^ 2 ∧ ‖y‖ ^ 2 ≤ b}]
      (fun y : ReciprocityTheory.L2DbarEstimates.V n => (‖y‖ ^ 2) ^ (-(n : ℝ))) :=
    ae_of_all _ (fun y => Real.rpow_nonneg (by positivity) _)
  rw [← ofReal_integral_eq_lintegral_ofReal hint_r hnn]
  congr 1
  have hpt : ∀ y : ReciprocityTheory.L2DbarEstimates.V n,
      {y : ReciprocityTheory.L2DbarEstimates.V n | a ≤ ‖y‖ ^ 2 ∧ ‖y‖ ^ 2 ≤ b}.indicator
          (fun y : ReciprocityTheory.L2DbarEstimates.V n => (‖y‖ ^ 2) ^ (-(n : ℝ))) y =
        (Icc (Real.sqrt a) (Real.sqrt b)).indicator (fun t : ℝ => (t ^ 2) ^ (-(n : ℝ))) ‖y‖ := by
    intro y
    classical
    rw [Set.indicator_apply, Set.indicator_apply]
    by_cases hy : y ∈ {y : ReciprocityTheory.L2DbarEstimates.V n | a ≤ ‖y‖ ^ 2 ∧ ‖y‖ ^ 2 ≤ b}
    · rw [if_pos hy, if_pos (show ‖y‖ ∈ Icc (Real.sqrt a) (Real.sqrt b) from (hmem y).1 hy)]
    · rw [if_neg hy, if_neg (show ‖y‖ ∉ Icc (Real.sqrt a) (Real.sqrt b) from
        fun h => hy ((hmem y).2 h))]
  have hI : ∫ y in {y : ReciprocityTheory.L2DbarEstimates.V n | a ≤ ‖y‖ ^ 2 ∧ ‖y‖ ^ 2 ≤ b}, (‖y‖ ^ 2) ^ (-(n : ℝ)) =
      ∫ y : ReciprocityTheory.L2DbarEstimates.V n, (Icc (Real.sqrt a) (Real.sqrt b)).indicator (fun t : ℝ => (t ^ 2) ^ (-(n : ℝ))) ‖y‖ := by
    rw [← integral_indicator hSc.measurableSet]
    exact congrArg _ (funext hpt)
  have hP : ∫ y : ReciprocityTheory.L2DbarEstimates.V n, (Icc (Real.sqrt a) (Real.sqrt b)).indicator (fun t : ℝ => (t ^ 2) ^ (-(n : ℝ))) ‖y‖ =
      (2 * n : ℕ) • (volume : Measure (ReciprocityTheory.L2DbarEstimates.V n)).real (ball 0 1) • ∫ y in Ioi (0:ℝ),
        y ^ (2 * n - 1) • (Icc (Real.sqrt a) (Real.sqrt b)).indicator (fun t : ℝ => (t ^ 2) ^ (-(n : ℝ))) y := by
    rw [integral_fun_norm_addHaar (volume : Measure (ReciprocityTheory.L2DbarEstimates.V n)), polar_finrank]
  rw [hI, hP, polar_ballReal n hn, polar_radial n hn a b ha hab,
    nsmul_eq_mul, smul_eq_mul]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel, Nat.factorial_succ]
  push_cast
  have hk : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  field_simp

end ReciprocityTheory.L2DbarEstimates.I
end

section -- merged from ReciprocityTheory.L2DbarEstimates.NormFibrations.Imports
namespace ReciprocityTheory.L2DbarEstimates

open Filter Topology

private theorem wd_wdb_ofReal_comp_of_differentiableAt {n : ℕ} {φ : ℝ → ℝ} {u : V n → ℝ} {y : V n}
    (hφ : DifferentiableAt ℝ φ (u y)) (hu : DifferentiableAt ℝ u y) (j : Fin n) :
    wd n j (fun w => (φ (u w) : ℂ)) y = ((deriv φ (u y) : ℝ) : ℂ) * wd n j (fun w => (u w : ℂ)) y ∧
      wdb n j (fun w => (φ (u w) : ℂ)) y = ((deriv φ (u y) : ℝ) : ℂ) * wdb n j (fun w => (u w : ℂ)) y := by
  have h1 : HasFDerivAt (fun w => (φ (u w) : ℂ))
      (Complex.ofRealCLM.comp (deriv φ (u y) • fderiv ℝ u y)) y :=
    Complex.ofRealCLM.hasFDerivAt.comp y (hφ.hasDerivAt.comp_hasFDerivAt y hu.hasFDerivAt)
  have h2 : HasFDerivAt (fun w => (u w : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ u y)) y :=
    Complex.ofRealCLM.hasFDerivAt.comp y hu.hasFDerivAt
  constructor <;>
    simp only [wd, wdb, h1.fderiv, h2.fderiv, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul, Complex.ofRealCLM_apply, Complex.ofReal_mul] <;> ring

private theorem wdb_ofReal_eq_conj_wd_ofReal {n : ℕ} {u : V n → ℝ} {y : V n} (hu : DifferentiableAt ℝ u y) (j : Fin n) :
    wdb n j (fun w => (u w : ℂ)) y = (starRingEnd ℂ) (wd n j (fun w => (u w : ℂ)) y) := by
  have h2 : HasFDerivAt (fun w => (u w : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ u y)) y :=
    Complex.ofRealCLM.hasFDerivAt.comp y hu.hasFDerivAt
  simp only [wd, wdb, h2.fderiv, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, map_div₀,
    map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  ring

private theorem wd_mul_apply {n : ℕ} {p q : V n → ℂ} {y : V n} (hp : DifferentiableAt ℝ p y)
    (hq : DifferentiableAt ℝ q y) (j : Fin n) :
    wd n j (fun w => p w * q w) y = wd n j p y * q y + p y * wd n j q y := by
  have hF : fderiv ℝ (fun w => p w * q w) y = p y • fderiv ℝ q y + q y • fderiv ℝ p y :=
    (hp.hasFDerivAt.mul hq.hasFDerivAt).fderiv
  simp only [wd, hF, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

private theorem differentiableAt_wdb_of_contDiffAt_two {n : ℕ} {g : V n → ℂ} {y : V n} (hg : ContDiffAt ℝ 2 g y) (k : Fin n) :
    DifferentiableAt ℝ (wdb n k g) y := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ g) y := hg.fderiv_right (by norm_num)
  have hb : ∀ u : V n, DifferentiableAt ℝ (fun v => fderiv ℝ g v u) y := fun u =>
    (h1.clm_apply contDiffAt_const).differentiableAt one_ne_zero
  have := ((hb (bas n k)).add ((hb (Complex.I • bas n k)).const_mul Complex.I)).mul_const (2⁻¹ : ℂ)
  unfold wdb
  simp only [div_eq_mul_inv]
  exact this

theorem chain (n : ℕ) (M : Type*) [TopologicalSpace M] : ChainStatement n M := by
  intro z hz φ v hφ hv x ξ
  obtain ⟨e, he, hx⟩ := exists_chart n z hz x
  have hT : e.target ∈ 𝓝 (z x) := by
    rw [he hx]; exact e.open_target.mem_nhds (e.map_source hx)
  have hx' : e.symm (z x) = x := by rw [he hx, e.left_inv hx]
  have hU : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => ((v (e.symm y) : ℝ) : ℂ)) e.target := hv e he
  have hur : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => v (e.symm y)) e.target := by
    have := Complex.reCLM.contDiff.comp_contDiffOn hU
    exact this.congr fun y _ => by simp
  have hu2 : ∀ y ∈ e.target, ContDiffAt ℝ 2 (fun y => v (e.symm y)) y := fun y hy =>
    (contDiffOn_infty.1 hur 2).contDiffAt (e.open_target.mem_nhds hy)
  have hud : ∀ y ∈ e.target, DifferentiableAt ℝ (fun y => v (e.symm y)) y := fun y hy =>
    (hu2 y hy).differentiableAt (by simp)
  have hz0 : z x ∈ e.target := mem_of_mem_nhds hT
  have hU2 : ContDiffAt ℝ 2 (fun y => ((v (e.symm y) : ℝ) : ℂ)) (z x) :=
    (contDiffOn_infty.1 hU 2).contDiffAt hT
  have hφ1 : ContDiff ℝ 1 (deriv φ) :=
    ((contDiff_succ_iff_deriv (n := 1)).1 (by rw [one_add_one_eq_two]; exact hφ)).2.2
  have hφd : ∀ t, DifferentiableAt ℝ φ t := fun t => hφ.differentiable (by simp) t
  have hφ1d : ∀ t, DifferentiableAt ℝ (deriv φ) t := fun t => hφ1.differentiable one_ne_zero t
  have ev : ∀ l, wdb n l (fun y => ((φ (v (e.symm y)) : ℝ) : ℂ)) =ᶠ[𝓝 (z x)]
      fun y => ((deriv φ (v (e.symm y)) : ℝ) : ℂ) * wdb n l (fun w => ((v (e.symm w) : ℝ) : ℂ)) y := by
    intro l
    filter_upwards [hT] with y hy
    exact (wd_wdb_ofReal_comp_of_differentiableAt (hφd _) (hud y hy) l).2
  have key : ∀ j l, wd n j (wdb n l (fun y => ((φ (v (e.symm y)) : ℝ) : ℂ))) (z x) =
      ((deriv φ (v (e.symm (z x))) : ℝ) : ℂ) * wd n j (wdb n l (fun w => ((v (e.symm w) : ℝ) : ℂ))) (z x) +
        ((deriv (deriv φ) (v (e.symm (z x))) : ℝ) : ℂ) *
          (wd n j (fun w => ((v (e.symm w) : ℝ) : ℂ)) (z x) *
            (starRingEnd ℂ) (wd n l (fun w => ((v (e.symm w) : ℝ) : ℂ)) (z x))) := by
    intro j l
    have e1 : wd n j (wdb n l (fun y => ((φ (v (e.symm y)) : ℝ) : ℂ))) (z x) =
        wd n j (fun y => ((deriv φ (v (e.symm y)) : ℝ) : ℂ) *
          wdb n l (fun w => ((v (e.symm w) : ℝ) : ℂ)) y) (z x) := by
      simp only [wd, (ev l).fderiv_eq]
    have hp : DifferentiableAt ℝ (fun y => ((deriv φ (v (e.symm y)) : ℝ) : ℂ)) (z x) :=
      Complex.ofRealCLM.differentiableAt.comp (z x) ((hφ1d _).comp (z x) (hud _ hz0))
    rw [e1, wd_mul_apply hp (differentiableAt_wdb_of_contDiffAt_two hU2 l) j, (wd_wdb_ofReal_comp_of_differentiableAt (hφ1d _) (hud _ hz0) j).1, ← wdb_ofReal_eq_conj_wd_ofReal (hud _ hz0) l]
    try beta_reduce
    ring
  have hdd : dDot n z (fun y => (v y : ℂ)) x ξ =
      ∑ j, wd n j (fun w => ((v (e.symm w) : ℝ) : ℂ)) (z x) * ξ j := by
    unfold dDot
    exact Finset.sum_congr rfl fun j _ => by rw [d_eq_wd n z e he j _ x hx]; rfl
  rw [levi_eq_leviV n z e he _ x hx ξ, levi_eq_leviV n z e he v x hx ξ, hdd, Complex.sq_norm,
    ← Complex.mul_conj]
  unfold leviV
  try beta_reduce
  simp only [key, hx']
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [map_mul]
  rw [Finset.sum_mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

end ReciprocityTheory.L2DbarEstimates
end

universe u

namespace ReciprocityTheory.L2DbarEstimates

open MeasureTheory

theorem regMAll (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : F.RegMStatement n M :=
  F.regM n M C.reg (F.extend n M)

theorem hormander (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : HStatement n M :=
  F.hStatement_of n M (E.ap n M) (E.tStarIbp n M) (chain n M) C.reg
    (B.moll_graph (V n) volume ℝ) (B.moll_smooth (V n) volume) (B.moll_support (V n) volume)
    (B.kernel_std (V n) volume)

theorem skoda (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : SStatement n M :=
  H.skoda n M (fun p => hormander n (M × Fin p))
    (fun p => F.needBergmanClosed n (M × Fin p) (regMAll n (M × Fin p)))

theorem tw (n : ℕ) (M : Type u) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : TWStatement n M :=
  I.tw n M (hormander n M) (F.holoClosedNeed n M (regMAll n M))

theorem ma (n : ℕ) : MAStatement n :=
  I.ma n (I.maCof n)

end ReciprocityTheory.L2DbarEstimates
