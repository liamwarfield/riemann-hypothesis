module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.VacuumNonvanishingOfFacts
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.FzSliceContDiffOn
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.FarRightAlt

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.FdAnalytic
noncomputable section

open MeasureTheory Matrix Filter Topology Set
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem Fd_analytic (m : ℕ) : AnalyticOnNhd ℂ (Fd (n := n) m) (DomZ n) := by
  letI : TopologicalSpace (M2 n) := (inferInstance : NormedAddCommGroup (M2 n)).toMetricSpace.toUniformSpace.toTopologicalSpace
  have hU := (fzHol n m 0).2.2
  intro y hy
  have h1 : AnalyticAt ℂ (fun p : ℂ × M2 n => fderiv ℂ (fun p : ℂ × M2 n => fz m 0 p.1 p.2) p (1, 0)) (0, y) :=
    (ContinuousLinearMap.apply ℂ ℂ ((1 : ℂ), (0 : M2 n))).analyticAt _ |>.comp (hU.fderiv (0, y) ⟨Set.mem_univ _, hy⟩)
  have hl : AnalyticAt ℂ (fun w : M2 n => ((0 : ℂ), w)) y := analyticAt_const.prod analyticAt_id
  have h2 := h1.comp hl
  refine h2.congr ?_
  filter_upwards [isOpen_domZ.mem_nhds hy] with w hw
  exact (Fd_eq m hw).symm

theorem fdProps : FdProps := by
  intro n m
  refine ⟨(Fd_analytic m).contDiffOn_of_completeSpace, ?_⟩
  intro Kg _ _ _ _ _ _ μ _ ι hι hK ρ ψ a b x hρ hψ hψs ha hb hx
  have hιG : ∀ k, InG (ι k) := fun k => ((hK (ι k)).2 ⟨k, rfl⟩).1
  set y : Kg × (Fin n → Fin n → ℝ) → M2 n := fun p => x * ι p.1 * a * nU (herm p.2) * b with hydef
  have hherm : Continuous (herm (n := n)) := by unfold herm; fun_prop
  have hnU : Continuous fun t : Fin n → Fin n → ℝ => nU (herm t) := by
    unfold nU; exact Continuous.matrix_fromBlocks continuous_const hherm continuous_const continuous_const
  have hy : Continuous y :=
    (((continuous_const.mul (hι.comp continuous_fst)).mul continuous_const).mul (hnU.comp continuous_snd)).mul
      continuous_const
  have hyD : ∀ p, y p ∈ DomZ n := fun p =>
    gset_sub_domZ (inG_mul (inG_mul (inG_mul (inG_mul hx (hιG p.1)) ha) (inG_nU_herm p.2)) hb)
  set U : ℂ × M2 n → ℂ := fun q => fz m 0 q.1 q.2 with hUdef
  have hU : ContDiffOn ℂ ∞ U (Set.univ ×ˢ DomZ n) := fz_contDiffOn m
  have hO : IsOpen (Set.univ ×ˢ DomZ n : Set (ℂ × M2 n)) := isOpen_univ.prod isOpen_domZ
  set U' : ℂ × M2 n → ℂ := fun q => fderiv ℂ U q (1, 0) with hU'def
  have hU' : ContinuousOn U' (Set.univ ×ˢ DomZ n) :=
    ((hU.fderiv_of_isOpen (m := ∞) hO (by simp)).clm_apply contDiffOn_const).continuousOn
  set F : ℂ → Kg × (Fin n → Fin n → ℝ) → ℂ := fun z p => ρ p.1 * (U (z, y p) * ψ p.2) with hFdef
  set F' : ℂ → Kg × (Fin n → Fin n → ℝ) → ℂ := fun z p => ρ p.1 * (U' (z, y p) * ψ p.2) with hF'def
  set S : Set (Kg × (Fin n → Fin n → ℝ)) := Set.univ ×ˢ tsupport ψ with hSdef
  have hS : IsCompact S := isCompact_univ.prod hψs
  have hzero : ∀ p, p ∉ S → ψ p.2 = 0 := fun p hp =>
    image_eq_zero_of_notMem_tsupport (fun h => hp ⟨Set.mem_univ _, h⟩)
  have hFc : ∀ z, Continuous (F z) := fun z =>
    (hρ.comp continuous_fst).mul ((hU.continuousOn.comp_continuous (continuous_const.prodMk hy)
      (fun p => ⟨Set.mem_univ _, hyD p⟩)).mul (hψ.comp continuous_snd))
  have hF'c : Continuous fun q : ℂ × (Kg × (Fin n → Fin n → ℝ)) => F' q.1 q.2 :=
    (hρ.comp (continuous_fst.comp continuous_snd)).mul ((hU'.comp_continuous (continuous_fst.prodMk
      (hy.comp continuous_snd)) (fun q => ⟨Set.mem_univ _, hyD q.2⟩)).mul (hψ.comp (continuous_snd.comp continuous_snd)))
  have hsupp : ∀ (G : Kg × (Fin n → Fin n → ℝ) → ℂ), Continuous G → (∀ p, p ∉ S → G p = 0) →
      Integrable G (μ.prod volume) := by
    intro G hG h0
    refine hG.integrable_of_hasCompactSupport (IsCompact.of_isClosed_subset hS (isClosed_tsupport G) ?_)
    refine closure_minimal (fun p hp => ?_) (isClosed_univ.prod (isClosed_tsupport ψ))
    by_contra h; exact hp (h0 p h)
  have hFi : ∀ z, Integrable (F z) (μ.prod volume) := fun z =>
    hsupp _ (hFc z) (fun p hp => by simp [hFdef, hzero p hp])
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) 1 |>.prod hS).exists_bound_of_continuousOn hF'c.continuousOn
  have hbound_int : Integrable (S.indicator fun _ => C) (μ.prod volume) :=
    (integrable_indicator_iff (isClosed_univ.prod (isClosed_tsupport ψ)).measurableSet).2 (integrableOn_const hS.measure_lt_top.ne)
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ.prod volume) (F := F) (F' := F')
    (x₀ := (0 : ℂ)) (s := Metric.ball 0 1) (bound := S.indicator fun _ => C) (Metric.ball_mem_nhds 0 one_pos)
    (Filter.Eventually.of_forall fun z => (hFc z).aestronglyMeasurable) (hFi 0)
    ((hF'c.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun p z hz => by
      by_cases hp : p ∈ S
      · rw [Set.indicator_of_mem hp]
        exact hC (z, p) ⟨Metric.ball_subset_closedBall hz, hp⟩
      · rw [Set.indicator_of_notMem hp]
        simp [hF'def, hzero p hp])
    hbound_int
    (Filter.Eventually.of_forall fun p z _ => by
      have hd : DifferentiableAt ℂ U (z, y p) :=
        (hU.contDiffAt (hO.mem_nhds ⟨Set.mem_univ _, hyD p⟩)).differentiableAt (by simp)
      have hl : HasDerivAt (fun z' : ℂ => (z', y p)) ((1 : ℂ), (0 : M2 n)) z :=
        (hasDerivAt_id z).prodMk (hasDerivAt_const z (y p))
      have h1 := hd.hasFDerivAt.comp_hasDerivAt z hl
      exact (h1.mul_const (ψ p.2)).const_mul (ρ p.1))
  have hT : ∀ (G : M2 n → ℂ), (Integrable (fun p : Kg × (Fin n → Fin n → ℝ) => ρ p.1 * (G (y p) * ψ p.2))
      (μ.prod volume)) → tOp μ ι ρ ψ a b G x = ∫ p, ρ p.1 * (G (y p) * ψ p.2) ∂(μ.prod volume) := by
    intro G hG
    rw [integral_prod _ hG]
    unfold tOp
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only [hydef]
    exact (integral_const_mul _ _).symm
  have e1 : (fun z => tOp μ ι ρ ψ a b (fz m 0 z) x) = fun z => ∫ p, F z p ∂(μ.prod volume) := by
    funext z; exact hT (fz m 0 z) (hFi z)
  have e2 : ∫ p, F' 0 p ∂(μ.prod volume) = tOp μ ι ρ ψ a b (Fd m) x := by
    have hF'0 : F' 0 = fun p => ρ p.1 * (Fd m (y p) * ψ p.2) := by
      funext p; simp only [hF'def, hU'def, Fd_eq m (hyD p)]; rfl
    rw [hF'0, hT (Fd m) (hF'0 ▸ hderiv.1)]
  rw [e1, hderiv.2.deriv, e2]

end PositivityTheory.Rg.Sw.HSt
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.SphU
noncomputable section

open MeasureTheory Matrix
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

private theorem finiteDimensional_continuousMultilinearMap {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (N : ℕ) : FiniteDimensional ℂ (ContinuousMultilinearMap ℂ (fun _ : Fin N => E) ℂ) :=
  FiniteDimensional.of_injective (ContinuousMultilinearMap.toMultilinearMapLinear (R' := ℂ) (A := ℂ))
    (fun _ _ h => ContinuousMultilinearMap.toMultilinearMap_injective h)

private theorem aestronglyMeasurable_of_continuous {Kg : Type} [TopologicalSpace Kg] [MeasurableSpace Kg] [BorelSpace Kg]
    (μ : Measure Kg) {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
    (f : Kg → W) (hf : Continuous f) : AEStronglyMeasurable f μ := by
  haveI : ProperSpace W := FiniteDimensional.proper ℂ W
  haveI : SecondCountableTopology W := secondCountable_of_proper
  exact hf.aestronglyMeasurable

private theorem integrable_of_continuous_isFiniteMeasure {Kg : Type} [TopologicalSpace Kg] [CompactSpace Kg] [MeasurableSpace Kg]
    [BorelSpace Kg] (μ : Measure Kg) [IsFiniteMeasure μ] {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
    [FiniteDimensional ℂ W] (f : Kg → W) (hf : Continuous f) : Integrable f μ := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  exact Integrable.of_bound (aestronglyMeasurable_of_continuous μ f hf) C (Filter.Eventually.of_forall fun k => hC k trivial)

private theorem matrix_mul_comm_of_mul_eq_smul_one_of_ne_zero {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {Kg : Type} [TopologicalSpace Kg] [CompactSpace Kg] [MeasurableSpace Kg]
    [BorelSpace Kg] (μ : Measure Kg) [IsFiniteMeasure μ] (Ω : Set E) (G : Kg → E → ℂ)
    (hΩ : IsOpen Ω)
    (hc : ∀ N : ℕ, ContinuousOn (fun y : Kg × E => iteratedFDeriv ℂ N (G y.1) y.2) (Set.univ ×ˢ Ω))
    (hd : ∀ k, ContDiffOn ℂ ∞ (G k) Ω) :
    (∀ N : ℕ, ∀ x ∈ Ω, iteratedFDeriv ℂ N (fun x => ∫ k, G k x ∂μ) x = ∫ k, iteratedFDeriv ℂ N (G k) x ∂μ) ∧
      ContDiffOn ℂ ∞ (fun x => ∫ k, G k x ∂μ) Ω := by
  haveI : ProperSpace E := FiniteDimensional.proper ℂ E
  have hck : ∀ (N : ℕ) (x : E), x ∈ Ω → Continuous (fun k => iteratedFDeriv ℂ N (G k) x) :=
    fun N x hx => (hc N).comp_continuous (continuous_id.prodMk continuous_const) (fun k => ⟨trivial, hx⟩)
  have hdiff : ∀ (N : ℕ) (k : Kg) (x : E), x ∈ Ω →
      HasFDerivAt (iteratedFDeriv ℂ N (G k)) (fderiv ℂ (iteratedFDeriv ℂ N (G k)) x) x := by
    intro N k x hx
    have h1 := (hd k).differentiableOn_iteratedFDerivWithin (m := N) (by exact_mod_cast WithTop.coe_lt_top _)
      hΩ.uniqueDiffOn
    have h2 : DifferentiableAt ℂ (iteratedFDerivWithin ℂ N (G k) Ω) x :=
      (h1 x hx).differentiableAt (hΩ.mem_nhds hx)
    have h3 : iteratedFDeriv ℂ N (G k) =ᶠ[nhds x] iteratedFDerivWithin ℂ N (G k) Ω :=
      Filter.eventually_of_mem (hΩ.mem_nhds hx) (fun y hy => (iteratedFDerivWithin_of_isOpen N hΩ hy).symm)
    exact (h2.congr_of_eventuallyEq h3).hasFDerivAt
  have hnorm : ∀ (N : ℕ) (k : Kg) (x : E),
      ‖fderiv ℂ (iteratedFDeriv ℂ N (G k)) x‖ = ‖iteratedFDeriv ℂ (N + 1) (G k) x‖ := by
    intro N k x
    rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, LinearIsometryEquiv.norm_map]
  have hsucc : ∀ (N : ℕ) (k : Kg) (x : E), fderiv ℂ (iteratedFDeriv ℂ N (G k)) x =
      continuousMultilinearCurryLeftEquiv ℂ (fun _ : Fin (N + 1) => E) ℂ (iteratedFDeriv ℂ (N + 1) (G k) x) := by
    intro N k x
    rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, LinearIsometryEquiv.apply_symm_apply]
  have hstep : ∀ (N : ℕ) (x : E), x ∈ Ω → HasFDerivAt (fun y => ∫ k, iteratedFDeriv ℂ N (G k) y ∂μ)
      (∫ k, fderiv ℂ (iteratedFDeriv ℂ N (G k)) x ∂μ) x := by
    intro N x hx
    haveI := finiteDimensional_continuousMultilinearMap (E := E) N
    haveI := finiteDimensional_continuousMultilinearMap (E := E) (N + 1)
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hΩ x hx
    have hcb : Metric.closedBall x (ε / 2) ⊆ Ω :=
      (Metric.closedBall_subset_ball (by linarith)).trans hball
    obtain ⟨C, hC⟩ := (isCompact_univ.prod (isCompact_closedBall x (ε / 2))).exists_bound_of_continuousOn
      ((hc (N + 1)).mono (Set.prod_mono le_rfl hcb))
    have hmeas' : AEStronglyMeasurable (fun k => fderiv ℂ (iteratedFDeriv ℂ N (G k)) x) μ := by
      have : (fun k => fderiv ℂ (iteratedFDeriv ℂ N (G k)) x) = fun k =>
          continuousMultilinearCurryLeftEquiv ℂ (fun _ : Fin (N + 1) => E) ℂ (iteratedFDeriv ℂ (N + 1) (G k) x) :=
        funext fun k => hsucc N k x
      rw [this]
      exact (LinearIsometryEquiv.continuous _).comp_aestronglyMeasurable (aestronglyMeasurable_of_continuous μ _ (hck (N + 1) x hx))
    exact hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := μ) (x₀ := x)
      (F := fun y k => iteratedFDeriv ℂ N (G k) y)
      (F' := fun y k => fderiv ℂ (iteratedFDeriv ℂ N (G k)) y) (bound := fun _ => C)
      (Metric.ball_mem_nhds x (half_pos hε))
      (Filter.eventually_of_mem (Metric.ball_mem_nhds x (half_pos hε))
        (fun y hy => aestronglyMeasurable_of_continuous μ _ (hck N y (hcb (Metric.ball_subset_closedBall hy)))))
      (integrable_of_continuous_isFiniteMeasure μ _ (hck N x hx)) hmeas'
      (Filter.Eventually.of_forall fun k y hy => by
        rw [hnorm]
        exact hC (k, y) ⟨trivial, Metric.ball_subset_closedBall hy⟩)
      (integrable_const C)
      (Filter.Eventually.of_forall fun k y hy => hdiff N k y (hcb (Metric.ball_subset_closedBall hy)))
  have key : ∀ N : ℕ, ∀ x ∈ Ω,
      iteratedFDeriv ℂ N (fun x => ∫ k, G k x ∂μ) x = ∫ k, iteratedFDeriv ℂ N (G k) x ∂μ := by
    intro N
    induction N with
    | zero =>
      intro x hx
      simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
      exact ((continuousMultilinearCurryFin0 ℂ E ℂ).symm.toContinuousLinearEquiv.integral_comp_comm _).symm
    | succ N ih =>
      intro x hx
      have hev : iteratedFDeriv ℂ N (fun x => ∫ k, G k x ∂μ) =ᶠ[nhds x]
          fun y => ∫ k, iteratedFDeriv ℂ N (G k) y ∂μ :=
        Filter.eventually_of_mem (hΩ.mem_nhds hx) ih
      rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, hev.fderiv_eq, (hstep N x hx).fderiv]
      have hcomm := (continuousMultilinearCurryLeftEquiv ℂ (fun _ : Fin (N + 1) => E) ℂ).symm.toContinuousLinearEquiv.integral_comp_comm
        (μ := μ) (fun k => fderiv ℂ (iteratedFDeriv ℂ N (G k)) x)
      refine hcomm.symm.trans ?_
      congr 1
  have hdΦ : ∀ (N : ℕ) (x : E), x ∈ Ω → DifferentiableAt ℂ (iteratedFDeriv ℂ N (fun x => ∫ k, G k x ∂μ)) x :=
    fun N x hx => (hstep N x hx).differentiableAt.congr_of_eventuallyEq
      (Filter.eventually_of_mem (hΩ.mem_nhds hx) (key N))
  refine ⟨key, ?_⟩
  apply contDiffOn_of_continuousOn_differentiableOn
  · intro m _
    exact ContinuousOn.congr (f := iteratedFDeriv ℂ m (fun x => ∫ k, G k x ∂μ))
      (fun x hx => (hdΦ m x hx).continuousAt.continuousWithinAt) (iteratedFDerivWithin_of_isOpen m hΩ)
  · intro m _
    exact DifferentiableOn.congr (f := iteratedFDeriv ℂ m (fun x => ∫ k, G k x ∂μ))
      (fun x hx => (hdΦ m x hx).differentiableWithinAt) (iteratedFDerivWithin_of_isOpen m hΩ)

private theorem iteratedFDeriv_comp_clm_mul_const {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (F : E → ℂ) (U : Set E) (hU : IsOpen U) (hF : ContDiffOn ℂ ∞ F U) (L : E →L[ℂ] E) (a : ℂ) (N : ℕ)
    (y : E) (hy : L y ∈ U) :
    iteratedFDeriv ℂ N (fun y => F (L y) * a) y =
      a • (iteratedFDeriv ℂ N F (L y)).compContinuousLinearMap (fun _ => L) := by
  have hopen : IsOpen (L ⁻¹' U) := hU.preimage L.continuous
  have hFL : ContDiffOn ℂ ∞ (F ∘ L) (L ⁻¹' U) := hF.comp L.contDiff.contDiffOn (fun _ h => h)
  have hfun : (fun y => F (L y) * a) = ((ContinuousLinearMap.mul ℂ ℂ).flip a) ∘ (F ∘ L) := by
    funext z
    simp [mul_comm]
  rw [← iteratedFDerivWithin_of_isOpen N hopen hy, hfun,
    ((ContinuousLinearMap.mul ℂ ℂ).flip a).iteratedFDerivWithin_comp_left (hFL y hy) hopen.uniqueDiffOn hy
      (by exact_mod_cast (WithTop.coe_lt_top _).le),
    L.iteratedFDerivWithin_comp_right hF hU.uniqueDiffOn hopen.uniqueDiffOn hy
      (by exact_mod_cast (WithTop.coe_lt_top _).le),
    iteratedFDerivWithin_of_isOpen N hU hy]
  ext v
  simp [mul_comm]

private theorem exists_ne_zero_smul_mem_of_mem_span' {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {Kg : Type} [TopologicalSpace Kg] [CompactSpace Kg] [MeasurableSpace Kg] [BorelSpace Kg]
    (μ : Measure Kg) [IsFiniteMeasure μ] (F : E → ℂ) (U : Set E) (hU : IsOpen U) (hF : ContDiffOn ℂ ∞ F U)
    (L : Kg → E →L[ℂ] E) (hL : Continuous L) (c : Kg → ℂ) (hc : Continuous c) :
    IsOpen {y | ∀ k, L k y ∈ U} ∧
      ContDiffOn ℂ ∞ (fun y => ∫ k, F (L k y) * c k ∂μ) {y | ∀ k, L k y ∈ U} ∧
      (∀ (N : ℕ) (y : E), (∀ k, L k y ∈ U) →
        iteratedFDeriv ℂ N (fun y => ∫ k, F (L k y) * c k ∂μ) y =
          ∫ k, iteratedFDeriv ℂ N (fun y => F (L k y) * c k) y ∂μ) ∧
      ∀ (N : ℕ) (y : E), (∀ k, L k y ∈ U) →
        Integrable (fun k => iteratedFDeriv ℂ N (fun y => F (L k y) * c k) y) μ := by
  have hW : IsOpen {y | ∀ k, L k y ∈ U} := by
    rw [isOpen_iff_mem_nhds]
    intro y0 hy0
    have hcont : Continuous fun z : E × Kg => L z.2 z.1 := (hL.comp continuous_snd).clm_apply continuous_fst
    have h := isCompact_univ.eventually_forall_of_forall_eventually (x₀ := y0) (P := fun y k => L k y ∈ U)
      (fun k _ => hcont.continuousAt.preimage_mem_nhds (hU.mem_nhds (hy0 k)))
    filter_upwards [h] with y hy
    exact fun k => hy k trivial
  have hG : ∀ N : ℕ, ContinuousOn (fun p : Kg × E => iteratedFDeriv ℂ N (fun y => F (L p.1 y) * c p.1) p.2)
      (Set.univ ×ˢ {y | ∀ k, L k y ∈ U}) := by
    intro N
    have hDF : ContinuousOn (iteratedFDeriv ℂ N F) U :=
      (hF.continuousOn_iteratedFDerivWithin (m := N) (by exact_mod_cast (WithTop.coe_lt_top _).le)
        hU.uniqueDiffOn).congr (fun x hx => (iteratedFDerivWithin_of_isOpen N hU hx).symm)
    have h1 : ContinuousOn (fun p : Kg × E => iteratedFDeriv ℂ N F (L p.1 p.2)) (Set.univ ×ˢ {y | ∀ k, L k y ∈ U}) :=
      hDF.comp ((hL.comp continuous_fst).clm_apply continuous_snd).continuousOn (fun p hp => hp.2 p.1)
    have h2 : Continuous (fun p : Kg × E => ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℂ
        (fun _ : Fin N => E) (fun _ => E) ℂ (fun _ => L p.1)) :=
      (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℂ
        (fun _ : Fin N => E) (fun _ => E) ℂ).cont.comp (continuous_pi fun _ => hL.comp continuous_fst)
    refine ContinuousOn.congr (((hc.comp continuous_fst).continuousOn).smul (h2.continuousOn.clm_apply h1)) ?_
    intro p hp
    dsimp only
    rw [iteratedFDeriv_comp_clm_mul_const F U hU hF (L p.1) (c p.1) N p.2 (hp.2 p.1)]
    simp
  have hdG : ∀ k, ContDiffOn ℂ ∞ (fun y => F (L k y) * c k) {y | ∀ k, L k y ∈ U} :=
    fun k => (hF.comp (L k).contDiff.contDiffOn (show Set.MapsTo (L k) {y | ∀ k, L k y ∈ U} U from fun y hy => hy k)).mul contDiffOn_const
  obtain ⟨key, hcd⟩ := matrix_mul_comm_of_mul_eq_smul_one_of_ne_zero μ {y | ∀ k, L k y ∈ U} (fun k y => F (L k y) * c k) hW hG hdG
  refine ⟨hW, hcd, fun N y hy => key N y hy, fun N y hy => ?_⟩
  haveI := finiteDimensional_continuousMultilinearMap (E := E) N
  exact integrable_of_continuous_isFiniteMeasure μ _ ((hG N).comp_continuous (continuous_id.prodMk continuous_const) (fun k => ⟨trivial, hy⟩))

private theorem exists_continuous_clm_of_bilinear {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (m : E →ₗ[ℂ] E →ₗ[ℂ] E) : ∃ Lc : E → E →L[ℂ] E, Continuous Lc ∧ ∀ a y, Lc a y = m a y := by
  refine ⟨fun a => LinearMap.toContinuousLinearMap (m a), ?_, fun a y => rfl⟩
  exact LinearMap.continuous_of_finiteDimensional
    ((LinearMap.toContinuousLinearMap : (E →ₗ[ℂ] E) ≃ₗ[ℂ] (E →L[ℂ] E)).toLinearMap ∘ₗ m)

theorem sphU : SphU := by
  intro n F U hU hF Kg _ _ _ _ μ _ _ ι hι c hc ιA ιB _ _ _ _ LA LB hLA hLB g hg
  have hF' : ContDiffOn ℂ ∞ F U := hF.of_le le_top
  obtain ⟨Lc, hLc, hLapp⟩ := exists_continuous_clm_of_bilinear (E := M2 n) (LinearMap.mul ℂ (M2 n))
  simp only [LinearMap.mul_apply'] at hLapp
  obtain ⟨hWo, hΦ, key, hint⟩ := exists_ne_zero_smul_mem_of_mem_span' (E := M2 n) μ F U hU hF' (fun k => Lc (ι k)) (hLc.comp hι) c hc
  simp only [hLapp] at hWo hΦ key hint
  have hgW : ∀ k, ι k * g ∈ U := hg
  have hL := detD_detD_comp (fun y => ∫ k, F (ι k * y) * c k ∂μ) _ hWo hΦ g hgW (LA g) (LB g)
  beta_reduce at hL
  simp only [hLA, hLB, ← mul_add]
  rw [hL, key _ g hgW]
  simp only [ContinuousMultilinearMap.integral_apply (hint _ g hgW)]
  have hR : ∀ k, (detD fun T : Matrix ιA ιA ℂ => detD fun S : Matrix ιB ιB ℂ =>
      F (ι k * (g + (LA g) T + (LB g) S))) * c k =
      ∑ σ : Equiv.Perm ιA, ∑ τ : Equiv.Perm ιB, ↑↑(Equiv.Perm.sign σ) * ↑↑(Equiv.Perm.sign τ) *
        (iteratedFDeriv ℂ (Fintype.card ιA + Fintype.card ιB) (fun y => F (ι k * y) * c k) g)
          (Fin.append (fun i => LA g (single ((Fintype.equivFin ιA).symm i) (σ ((Fintype.equivFin ιA).symm i)) 1))
            (fun i => LB g (single ((Fintype.equivFin ιB).symm i) (τ ((Fintype.equivFin ιB).symm i)) 1))) := by
    intro k
    have hFk : ContDiffOn ℂ ∞ (fun y => F (ι k * y)) {y : M2 n | ∀ k, ι k * y ∈ U} :=
      (hF'.comp (Lc (ι k)).contDiff.contDiffOn (show Set.MapsTo (Lc (ι k)) {y : M2 n | ∀ k, ι k * y ∈ U} U from fun y hy => by rw [hLapp]; exact hy k)).congr
        (fun y _ => by rw [Function.comp_apply, hLapp])
    have h1 := detD_detD_mul_const (fun y => F (ι k * y)) _ hWo hFk g hgW (LA g) (LB g) (c k)
    have h2 := detD_detD_comp (fun y => F (ι k * y) * c k) _ hWo (hFk.mul contDiffOn_const) g hgW (LA g) (LB g)
    beta_reduce at h1 h2
    rw [← h1, h2]
  simp only [hR]
  rw [integral_finsetSum _ (fun σ _ => ?_)]
  · refine Finset.sum_congr rfl fun σ _ => ?_
    rw [integral_finsetSum _ (fun τ _ => ?_)]
    · refine Finset.sum_congr rfl fun τ _ => ?_
      rw [integral_const_mul]
    · exact ((ContinuousMultilinearMap.apply ℂ _ ℂ _).integrable_comp (hint _ g hgW)).const_mul _
  · exact integrable_finsetSum _ fun τ _ =>
      ((ContinuousMultilinearMap.apply ℂ _ ℂ _).integrable_comp (hint _ g hgW)).const_mul _

end PositivityTheory.Rg.Sw.HSt
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.KsTraceSingle
noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

theorem ks_inv_eq {U : Matrix (Fin n) (Fin n) ℂ} (h : U * Uᴴ = 1) : U⁻¹ = Uᴴ := Matrix.inv_eq_right_inv h

theorem ks_trace_single (X : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) : (X * Matrix.single a b 1).trace = X b a := by
  rw [Matrix.trace_mul_single]
  simp

theorem ks_rhoP {Kg : Type} [Group Kg] (ι : Kg →* M2 n) (m : ℕ) (k k1 : Kg) (hk : InK (ι k))
    (N : Matrix (Fin n) (Fin n) ℂ) (hN : N ∈ unitaryGroup (Fin n) ℂ) (h1 : ι k1 = Proj.kM 1 N) :
    rhoP ι m 0 1 (k * k1) = fV (m : ℤ) 0 (ι k) * ((u1 (ι k))⁻¹ * u2 (ι k) * N).trace := by
  obtain ⟨kk, hkk, hmk⟩ := Proj.kM_of_unitary (1 : Matrix (Fin n) (Fin n) ℂ) N (one_mem _) hN
  have hu1 : u1 (ι (k * k1)) = u1 (ι k) := by
    rw [map_mul, h1, ← hmk, first_block_mul_compact (ι k) hkk, hmk, Proj.first_unitary_block_of_pair, Matrix.mul_one]
  have hu2 : u2 (ι (k * k1)) = u2 (ι k) * N := by
    rw [map_mul, h1, ← hmk, second_block_mul_compact (ι k) hkk, hmk, Proj.second_unitary_block_of_pair]
  have U1 : u1 (ι k) * (u1 (ι k))ᴴ = 1 := first_cayley_block_unitary hk
  have U2 : u2 (ι k) * (u2 (ι k))ᴴ = 1 := second_cayley_block_unitary hk
  have UN : N * Nᴴ = 1 := by
    have := Matrix.mem_unitaryGroup_iff.mp hN
    rwa [Matrix.star_eq_conjTranspose] at this
  have hfz : fz m 0 0 (ι (k * k1)) = (u1 (ι k)).det ^ (-(m : ℤ)) := by
    simp only [fz, zpow_zero, one_mul, neg_zero, Complex.cpow_zero, mul_one, hu1]
  have hne : (u1 (ι k)).det ≠ 0 := det_first_cayley_block_ne_zero hk.1
  have hd : star (u1 (ι k)).det = ((u1 (ι k)).det)⁻¹ := by
    have := congrArg Matrix.det U1
    rw [det_mul, det_one, det_conjTranspose] at this
    exact eq_inv_of_mul_eq_one_right this
  have hfV : fV (m : ℤ) 0 (ι k) = star ((u1 (ι k)).det ^ (-(m : ℤ))) := by
    have h := scalar_section_mul_conjugate_section hk (m : ℤ) 0
    have hf0 : f0 (m : ℤ) 0 (ι k) = (u1 (ι k)).det ^ (-(m : ℤ)) := by simp [f0]
    rw [hf0] at h
    rw [star_zpow₀, hd, eq_inv_of_mul_eq_one_right h]
    rw [_root_.zpow_neg, _root_.zpow_neg, _root_.inv_zpow, inv_inv]
  have htr : star ((u2 (ι (k * k1)))⁻¹ * 1 * u1 (ι (k * k1))).trace = ((u1 (ι k))⁻¹ * u2 (ι k) * N).trace := by
    rw [hu1, hu2, Matrix.mul_one, Matrix.mul_inv_rev, ← Matrix.trace_conjTranspose, ks_inv_eq UN, ks_inv_eq U2,
      ks_inv_eq U1]
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
  unfold rhoP
  rw [star_mul', hfz, htr, hfV]

theorem ks_perm_unitary (a b : Fin n) : (Equiv.swap a b).permMatrix ℂ ∈ unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, conjTranspose_permMatrix,
    PEquiv.toMatrix_toPEquiv_mul]
  ext i j
  simp [PEquiv.toMatrix_apply, Matrix.one_apply]

theorem ks_diag_unitary (b : Fin n) :
    Matrix.diagonal (fun i => if i = b then (1 : ℂ) else -1) ∈ unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  by_cases h : i = b <;> simp [h]

theorem ks_single_eq (a b : Fin n) :
    Matrix.single a b (1 : ℂ) = (1 / 2 : ℂ) • (Equiv.swap a b).permMatrix ℂ +
      (1 / 2 : ℂ) • ((Equiv.swap a b).permMatrix ℂ * Matrix.diagonal (fun i => if i = b then (1 : ℂ) else -1)) := by
  ext i j
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.mul_diagonal, Matrix.single_apply]
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq,
    smul_eq_mul]
  by_cases hj : j = b
  · subst hj
    by_cases hi : i = a
    · subst hi
      simp <;> norm_num
    · have : ¬ (Equiv.swap a j i = j) := by
        rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]
        exact hi
      simp [this, Ne.symm hi]
  · simp only [hj, if_false]
    by_cases h : Equiv.swap a b i = j
    · simp only [h, if_true]
      have : ¬ (a = i ∧ b = j) := fun h' => hj h'.2.symm
      rw [if_neg this]
      ring
    · simp only [h, if_false]
      have : ¬ (a = i ∧ b = j) := fun h' => hj h'.2.symm
      rw [if_neg this]
      ring

theorem kSplit : KSplit := by
  intro n m a0 b0 Kg _ ι hK
  classical
  set Pm : Matrix (Fin n) (Fin n) ℂ := (Equiv.swap a0 b0).permMatrix ℂ with hPmdef
  set D : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal (fun i => if i = b0 then (1 : ℂ) else -1) with hDdef
  have hPm : Pm ∈ unitaryGroup (Fin n) ℂ := ks_perm_unitary a0 b0
  have hD : D ∈ unitaryGroup (Fin n) ℂ := ks_diag_unitary b0
  set Nl : Fin 2 → Matrix (Fin n) (Fin n) ℂ := ![Pm, Pm * D] with hNldef
  have hNl : ∀ l, Nl l ∈ unitaryGroup (Fin n) ℂ := by
    intro l
    fin_cases l
    · exact hPm
    · exact mul_mem hPm hD
  have hex : ∀ l, ∃ k1 : Kg, ι k1 = Proj.kM 1 (Nl l) := fun l => by
    obtain ⟨kk, hkk, hmk⟩ := Proj.kM_of_unitary (1 : Matrix (Fin n) (Fin n) ℂ) (Nl l) (one_mem _) (hNl l)
    have : InK (Proj.kM 1 (Nl l)) := by rw [← hmk]; exact hkk
    exact (hK _).1 this
  choose kl hkl using hex
  refine ⟨2, fun _ => 1 / 2, kl, fun k => ?_⟩
  have hk : InK (ι k) := (hK _).2 ⟨k, rfl⟩
  rw [Fin.sum_univ_two, ks_rhoP ι m k (kl 0) hk _ (hNl 0) (hkl 0), ks_rhoP ι m k (kl 1) hk _ (hNl 1) (hkl 1)]
  rw [← ks_trace_single ((u1 (ι k))⁻¹ * u2 (ι k)) a0 b0, ks_single_eq a0 b0]
  simp only [hNldef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add,
    Matrix.trace_smul, smul_eq_mul, Matrix.mul_assoc]
  ring

end PositivityTheory.Rg.Sw.HSt
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.DetUnitOfInK
noncomputable section

open MeasureTheory Matrix

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {n : ℕ}

theorem det_nU (H : Matrix (Fin n) (Fin n) ℂ) : (nU H).det = 1 := by
  simp [nU, Matrix.det_fromBlocks_zero₂₁]

theorem fz_twist (m : ℕ) (e : ℤ) (z : ℂ) (y : M2 n) : fz m e z y = y.det ^ e * fz m 0 z y := by
  simp [fz, mul_assoc]

theorem det_unit_of_inK {k : M2 n} (hk : InK k) : star k.det * k.det = 1 := by
  have h := congrArg Matrix.det hk.2
  rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at h
  exact h

theorem rhoP_twist {Kg : Type} (ι : Kg → M2 n) (hK : ∀ k, InK (ι k)) (m : ℕ) (e : ℤ) (Y : Matrix (Fin n) (Fin n) ℂ)
    (k : Kg) : rhoP ι m e Y k * (ι k).det ^ e = rhoP ι m 0 Y k := by
  unfold rhoP
  rw [fz_twist m e 0 (ι k)]
  simp only [star_mul, star_zpow₀]
  have hu : star (ι k).det * (ι k).det = 1 := det_unit_of_inK (hK k)
  have h1 : star (ι k).det ^ e * (ι k).det ^ e = 1 := by
    rw [← mul_zpow, hu, _root_.one_zpow]
  linear_combination (star ((u2 (ι k))⁻¹ * Y * u1 (ι k)).trace * star (fz m 0 0 (ι k))) * h1

theorem tOp_twist {Kg : Type} [MeasurableSpace Kg] (μ : Measure Kg) (ι : Kg → M2 n) (hK : ∀ k, InK (ι k)) (m : ℕ)
    (e : ℤ) (Y : Matrix (Fin n) (Fin n) ℂ) (ψ : (Fin n → Fin n → ℝ) → ℂ) (a b x : M2 n) (z : ℂ) :
    tOp μ ι (rhoP ι m e Y) ψ a b (fz m e z) x =
      (x.det ^ e * a.det ^ e * b.det ^ e) * tOp μ ι (rhoP ι m 0 Y) ψ a b (fz m 0 z) x := by
  unfold tOp
  rw [← integral_const_mul]
  congr 1
  funext k
  have hin : (∫ (t : Fin n → Fin n → ℝ), fz m e z (x * ι k * a * nU (herm t) * b) * ψ t)
      = (x.det ^ e * (ι k).det ^ e * a.det ^ e * b.det ^ e) *
        ∫ (t : Fin n → Fin n → ℝ), fz m 0 z (x * ι k * a * nU (herm t) * b) * ψ t := by
    rw [← integral_const_mul]
    congr 1
    funext t
    rw [fz_twist m e z, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, det_nU, mul_one,
      mul_zpow, mul_zpow, mul_zpow]
    ring
  rw [hin, ← rhoP_twist ι hK m e Y k]
  ring

theorem eRed : ERed := by
  intro h n m e hmn Kg _ _ _ _ _ _ μ _ ι hι hK
  obtain ⟨P, ψ, a, b, x, h1, h2, h3, h4, h5⟩ := h n m hmn Kg μ ι hι hK
  refine ⟨P, ψ, a, b, x, h1, h2, h3, h4, ?_⟩
  have hKk : ∀ k, InK (ι k) := fun k => (hK (ι k)).2 ⟨k, rfl⟩
  have hfun : (fun z : ℂ => tOp μ (⇑ι) (rhoP (⇑ι) m e P) ψ a b (fz m e z) x)
      = fun z : ℂ => (x.det ^ e * a.det ^ e * b.det ^ e) * tOp μ (⇑ι) (rhoP (⇑ι) m 0 P) ψ a b (fz m 0 z) x := by
    funext z
    exact tOp_twist μ ι hKk m e P ψ a b x z
  rw [hfun, deriv_const_mul_field']
  refine mul_ne_zero ?_ h5
  refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
  · exact zpow_ne_zero _ (isUnit_det_of_InG h4).ne_zero
  · exact zpow_ne_zero _ (isUnit_det_of_InG h2).ne_zero
  · exact zpow_ne_zero _ (isUnit_det_of_InG h3).ne_zero

end PositivityTheory.Rg.Sw.HSt
end
end

namespace PositivityTheory.Rg.Sw.HSt

theorem crux : Crux := eRed (vacuum_nonvanishing_of_facts fdProps djFd kSplit sphU fzHol)

end PositivityTheory.Rg.Sw.HSt
