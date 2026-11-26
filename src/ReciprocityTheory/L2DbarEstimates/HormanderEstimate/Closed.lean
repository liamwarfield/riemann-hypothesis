module

public import ReciprocityTheory.L2DbarEstimates.SkodaWeights.NeedBergmanClosed
public import ReciprocityTheory.L2DbarEstimates.LeviForms.LogNormSq
public import ReciprocityTheory.L2DbarEstimates.HormanderEstimate.RegMDbEqZeroOfNotMem

@[expose] public section

section -- merged from ReciprocityTheory.L2DbarEstimates.HormanderEstimate.ExistsLintegralCompactLe
section -- merged from ReciprocityTheory.L2DbarEstimates.HormanderEstimate.ClosedSt
namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set
open scoped ENNReal

noncomputable section

def ClosedCoreStatement (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : Prop :=
  ∀ (z : M → V n), IsLocalHomeomorph z → ∀ (ψ : M → ℝ), Continuous ψ →
    ∀ (F : ℕ → M → ℂ) (f : M → ℂ), (∀ k, Holo n z (F k)) → AEStronglyMeasurable f (vol n z) →
    Tendsto (fun k => wint n z (fun x => F k x - f x) ψ) atTop (𝓝 0) →
    ∃ G : M → ℂ, Holo n z G ∧ f =ᵐ[vol n z] G

def EvalPtStatement (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : Prop :=
  ∀ (z : M → V n), IsLocalHomeomorph z → ∀ (ψ : M → ℝ), Continuous ψ → ∀ x0 : M,
    ∃ C : ℝ, 0 ≤ C ∧ ∀ F : M → ℂ, Holo n z F →
      ENNReal.ofReal (‖F x0‖ ^ 2) ≤ ENNReal.ofReal C * wint n z F ψ

end

end ReciprocityTheory.L2DbarEstimates.F
end

namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set
open scoped ENNReal

noncomputable section

theorem continuous_of_smoothR (n : ℕ) {M : Type*} [TopologicalSpace M] (z : M → V n)
    (hz : IsLocalHomeomorph z) (ψ : M → ℝ) (hψ : SmoothR n z ψ) : Continuous ψ := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨e, hxe, he⟩ := hz x
  have hc : IsChart n z e := fun y _ => by rw [he]
  have hf := (hψ e hc).continuousOn.continuousAt (e.open_target.mem_nhds (e.map_source hxe))
  have h2 := hf.comp (e.continuousAt hxe)
  have h3 : ContinuousAt (fun y => (ψ y : ℂ)) x := by
    refine h2.congr (Filter.eventually_of_mem (e.open_source.mem_nhds hxe) (fun y hy => ?_))
    simp [Function.comp, e.left_inv hy]
  have h4 : ContinuousAt (fun y => ((ψ y : ℂ)).re) x := Complex.continuous_re.continuousAt.comp h3
  simpa using h4

theorem exists_lintegral_compact_le (n : ℕ) {M : Type*} [TopologicalSpace M] [T2Space M]
    [MeasurableSpace M] [BorelSpace M] (z : M → V n) (ψ : M → ℝ) (hψ : Continuous ψ)
    (K : Set M) (hK : IsCompact K) :
    ∃ c : ℝ, ∀ g : M → ℂ, ∫⁻ x in K, ‖g x‖ₑ ^ 2 ∂vol n z ≤ ENNReal.ofReal c * wint n z g ψ := by
  obtain ⟨C, hC⟩ := hK.bddAbove_image hψ.continuousOn
  refine ⟨Real.exp C, fun g => ?_⟩
  unfold wint
  calc ∫⁻ x in K, ‖g x‖ₑ ^ 2 ∂vol n z
      ≤ ∫⁻ x in K, ENNReal.ofReal (Real.exp C) *
          ENNReal.ofReal (‖g x‖ ^ 2 * Real.exp (-ψ x)) ∂vol n z := by
        refine setLIntegral_mono' hK.measurableSet (fun x hx => ?_)
        have hψx : ψ x ≤ C := hC ⟨x, hx, rfl⟩
        rw [← ENNReal.ofReal_mul (Real.exp_pos C).le]
        have h1 : ‖g x‖ₑ ^ 2 = ENNReal.ofReal (‖g x‖ ^ 2) := by
          rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]
        rw [h1]
        apply ENNReal.ofReal_le_ofReal
        have hexp : 1 ≤ Real.exp C * Real.exp (-ψ x) := by
          rw [← Real.exp_add]
          exact Real.one_le_exp (by linarith)
        have h2 : Real.exp C * (‖g x‖ ^ 2 * Real.exp (-ψ x)) =
            ‖g x‖ ^ 2 * (Real.exp C * Real.exp (-ψ x)) := by ring
        rw [h2]
        exact le_mul_of_one_le_right (sq_nonneg _) hexp
    _ = ENNReal.ofReal (Real.exp C) *
          ∫⁻ x in K, ENNReal.ofReal (‖g x‖ ^ 2 * Real.exp (-ψ x)) ∂vol n z := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal (Real.exp C) *
          ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2 * Real.exp (-ψ x)) ∂vol n z :=
        mul_le_mul_of_nonneg_left (setLIntegral_le_lintegral _ _) (by simp)

private theorem chart_symm_eventuallyEq_of_mem_sources (n : ℕ) {M : Type*} [TopologicalSpace M] (z : M → V n)
    {e e' : OpenPartialHomeomorph M (V n)} (he : IsChart n z e) (he' : IsChart n z e') {x : M}
    (hx : x ∈ e.source) (hx' : x ∈ e'.source) : e.symm =ᶠ[𝓝 (z x)] e'.symm := by
  have h1 : e'.target ∈ 𝓝 (z x) := by
    rw [he' hx']
    exact e'.open_target.mem_nhds (e'.map_source hx')
  have h2 : ∀ᶠ w in 𝓝 (z x), e'.symm w ∈ e.source := by
    have hc := e'.continuousAt_symm (e'.map_source hx')
    rw [← he' hx'] at hc
    have hs : e.source ∈ 𝓝 (e'.symm (z x)) := by
      rw [he' hx', e'.left_inv hx']
      exact e.open_source.mem_nhds hx
    exact hc hs
  filter_upwards [h1, h2] with w hw1 hw2
  have h3 : e (e'.symm w) = w := by
    rw [← he hw2, he' (e'.map_target hw1), e'.right_inv hw1]
  calc e.symm w = e.symm (e (e'.symm w)) := by rw [h3]
    _ = e'.symm w := e.left_inv hw2

private theorem db_eq_wdb_of_mem_chart_source (n : ℕ) {M : Type*} [TopologicalSpace M] (z : M → V n)
    {e : OpenPartialHomeomorph M (V n)} (he : IsChart n z e) (j : Fin n) (f : M → ℂ) {x : M}
    (hx : x ∈ e.source) : db n z j f x = wdb n j (f ∘ e.symm) (z x) := by
  have hex : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source := ⟨e, he, hx⟩
  unfold db
  rw [dite_eq_left hex]
  have hspec := Classical.choose_spec hex
  have heq : (f ∘ (Classical.choose hex).symm) =ᶠ[𝓝 (z x)] (f ∘ e.symm) :=
    (chart_symm_eventuallyEq_of_mem_sources n z hspec.1 he hspec.2 hx).fun_comp f
  unfold wdb
  rw [heq.fderiv_eq]

private theorem continuous_db_of_smooth (n : ℕ) {M : Type*} [TopologicalSpace M] (z : M → V n)
    (hz : IsLocalHomeomorph z) (j : Fin n) (φ : M → ℂ) (hφ : Smooth n z φ) :
    Continuous (db n z j φ) := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨e, hxe, he⟩ := hz x
  have hc : IsChart n z e := fun y _ => by rw [he]
  have hsm := hφ e hc
  have hfd : ContinuousOn (fun w => fderiv ℝ (φ ∘ e.symm) w) e.target :=
    hsm.continuousOn_fderiv_of_isOpen e.open_target (by simp)
  have hw : ContinuousOn (wdb n j (φ ∘ e.symm)) e.target := by
    unfold wdb
    exact ((hfd.clm_apply continuousOn_const).add
      (continuousOn_const.mul (hfd.clm_apply continuousOn_const))).div_const 2
  have hat : ContinuousAt (fun y => wdb n j (φ ∘ e.symm) (e y)) x :=
    (hw.continuousAt (e.open_target.mem_nhds (e.map_source hxe))).comp (e.continuousAt hxe)
  refine hat.congr ?_
  filter_upwards [e.open_source.mem_nhds hxe] with y hy
  rw [db_eq_wdb_of_mem_chart_source n z hc j φ hy, hc hy]

private theorem db_eq_zero_of_not_mem_tsupport (n : ℕ) {M : Type*} [TopologicalSpace M] (z : M → V n)
    (hz : IsLocalHomeomorph z) (j : Fin n) (φ : M → ℂ) {x : M} (hx : x ∉ tsupport φ) :
    db n z j φ x = 0 := by
  obtain ⟨e, hxe, he⟩ := hz x
  have hc : IsChart n z e := fun y _ => by rw [he]
  rw [db_eq_wdb_of_mem_chart_source n z hc j φ hxe]
  have h0 : (φ ∘ e.symm) =ᶠ[𝓝 (z x)] fun _ => (0 : ℂ) := by
    have h1 : φ =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hx
    have hcont : Filter.Tendsto e.symm (𝓝 (e x)) (𝓝 x) := by
      have h2 := e.continuousAt_symm (e.map_source hxe)
      rwa [ContinuousAt, e.left_inv hxe] at h2
    rw [hc hxe]
    exact hcont.eventually h1
  unfold wdb
  rw [h0.fderiv_eq]
  simp

private theorem vol_lt_infty_of_isCompact (n : ℕ) {M : Type*} [TopologicalSpace M] [T2Space M]
    [MeasurableSpace M] [BorelSpace M] (z : M → V n) (hz : IsLocalHomeomorph z)
    (K : Set M) (hK : IsCompact K) : vol n z K < ⊤ := by
  classical
  unfold vol
  split_ifs with hadd
  · rw [Measure.ofMeasurable_apply _ hK.measurableSet]
    show volFun n z K < ⊤
    choose e hxe he using fun x => hz x
    obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x => (e x).source) (fun x => (e x).open_source)
      (fun x _ => Set.mem_iUnion.mpr ⟨x, hxe x⟩)
    have hbound : ∀ y, (((K ∩ z ⁻¹' {y}).encard : ℕ∞) : ℝ≥0∞) ≤
        (z '' K).indicator (fun _ => (t.card : ℝ≥0∞)) y := by
      intro y
      by_cases hy : y ∈ z '' K
      · rw [Set.indicator_of_mem hy]
        have hcov : ∀ p, ∃ x, p ∈ K → x ∈ t ∧ p ∈ (e x).source := fun p => by
          by_cases hp : p ∈ K
          · obtain ⟨x, hx⟩ : ∃ x ∈ t, p ∈ (e x).source := by simpa using ht hp
            exact ⟨x, fun _ => hx⟩
          · exact ⟨p, fun h => absurd h hp⟩
        choose g hg using hcov
        have key : (K ∩ z ⁻¹' {y}).encard ≤ (t : Set M).encard := by
          refine Set.encard_le_encard_of_injOn (f := g) ?_ ?_
          · intro p hp
            exact (hg p hp.1).1
          · intro p hp p' hp' hpp'
            have h1 := (hg p hp.1).2
            have h2 := (hg p' hp'.1).2
            rw [hpp'] at h1
            have e1 : z p = y := hp.2
            have e2 : z p' = y := hp'.2
            have hzp : z p = z p' := e1.trans e2.symm
            rw [he (g p')] at hzp
            exact (e (g p')).injOn h1 h2 hzp
        rw [Set.encard_coe_eq_coe_finsetCard] at key
        exact_mod_cast key
      · have hem : K ∩ z ⁻¹' {y} = ∅ := by
          ext p
          simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
            Set.mem_empty_iff_false, iff_false]
          rintro ⟨hp, hpy⟩
          exact hy ⟨p, hp, hpy⟩
        rw [hem]
        simp
    have hKc : IsCompact (z '' K) := hK.image hz.continuous
    calc volFun n z K = ∫⁻ y, (((K ∩ z ⁻¹' {y}).encard : ℕ∞) : ℝ≥0∞) := rfl
      _ ≤ ∫⁻ y, (z '' K).indicator (fun _ => (t.card : ℝ≥0∞)) y := lintegral_mono hbound
      _ = t.card * volume (z '' K) := lintegral_indicator_const hKc.measurableSet _
      _ < ⊤ := ENNReal.mul_lt_top (by simp) hKc.measure_lt_top
  · simp

theorem lintegral_db_test_lt_top (n : ℕ) {M : Type*} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (z : M → V n)
    (hz : IsLocalHomeomorph z) (ψ : M → ℝ) (hψ : Continuous ψ) (φ : M → ℂ)
    (hφ : IsTest n z φ) (j : Fin n) :
    ∫⁻ x, ENNReal.ofReal (‖db n z j φ x‖ ^ 2 * Real.exp (ψ x)) ∂vol n z < ⊤ := by
  have hdb := continuous_db_of_smooth n z hz j φ hφ.1
  have hK : IsCompact (tsupport φ) := hφ.2
  have hfc : ContinuousOn (fun x => ‖db n z j φ x‖ ^ 2 * Real.exp (ψ x)) (tsupport φ) :=
    ((hdb.norm.pow 2).mul (Real.continuous_exp.comp hψ)).continuousOn
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hfc
  have hle : ∀ x, ENNReal.ofReal (‖db n z j φ x‖ ^ 2 * Real.exp (ψ x)) ≤
      (tsupport φ).indicator (fun _ => ENNReal.ofReal C) x := by
    intro x
    by_cases hx : x ∈ tsupport φ
    · rw [Set.indicator_of_mem hx]
      apply ENNReal.ofReal_le_ofReal
      have h := hC x hx
      rw [Real.norm_eq_abs] at h
      exact (le_abs_self _).trans h
    · rw [db_eq_zero_of_not_mem_tsupport n z hz j φ hx]
      simp
  calc ∫⁻ x, ENNReal.ofReal (‖db n z j φ x‖ ^ 2 * Real.exp (ψ x)) ∂vol n z
      ≤ ∫⁻ x, (tsupport φ).indicator (fun _ => ENNReal.ofReal C) x ∂vol n z := lintegral_mono hle
    _ = ENNReal.ofReal C * vol n z (tsupport φ) := lintegral_indicator_const hK.measurableSet _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (vol_lt_infty_of_isCompact n z hz _ hK)

theorem integral_holo_mul_db (n : ℕ) {M : Type*} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (z : M → V n)
    (hz : IsLocalHomeomorph z) (F : M → ℂ) (hF : Holo n z F) (φ : M → ℂ) (hφ : IsTest n z φ)
    (j : Fin n) : ∫ x, F x * db n z j φ x ∂vol n z = 0 := by
  have h := integral_db_mul n z hz j F φ (Smooth.ck n z 1 F (Holo.smooth n z F hF))
    (Smooth.ck n z 1 φ hφ.1) hφ.2
  have h0 : (fun x => db n z j F x * φ x) = fun _ => 0 :=
    funext fun x => by simp [Holo.db_eq_zero n z F hF j x]
  rw [h0, integral_zero] at h
  exact neg_eq_zero.mp h.symm

end

end ReciprocityTheory.L2DbarEstimates.F
end

section -- merged from ReciprocityTheory.L2DbarEstimates.HormanderEstimate.ClosedEval
namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

noncomputable section

theorem evalPt (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (hMV : C.MVStatement) :
    EvalPtStatement n M := by
  intro z hz ψ hψ x0
  obtain ⟨e, hx0, hze⟩ := hz x0
  have he : IsChart n z e := fun x _ => by rw [hze]
  have hte : e x0 ∈ e.target := e.map_source hx0
  obtain ⟨r, hr, hrt⟩ := Metric.isOpen_iff.1 e.open_target (e x0) hte
  have hcb : Metric.closedBall (e x0) (r / 2) ⊆ e.target :=
    (Metric.closedBall_subset_ball (half_lt_self hr)).trans hrt
  set K : Set M := e.symm '' Metric.closedBall (e x0) (r / 2) with hKdef
  have hKc : IsCompact K :=
    (isCompact_closedBall _ _).image_of_continuousOn (e.continuousOn_symm.mono hcb)
  have hKs : K ⊆ e.source := by
    rintro _ ⟨y, hy, rfl⟩
    exact e.map_target (hcb hy)
  obtain ⟨c, hc⟩ := exists_lintegral_compact_le n z ψ hψ K hKc
  set Vb : ℝ≥0∞ := volume (Metric.ball (e x0) (r / 2)) with hVbdef
  have hVpos : 0 < Vb := Metric.measure_ball_pos _ _ (half_pos hr)
  have hVfin : Vb ≠ ⊤ := measure_ball_lt_top.ne
  refine ⟨max c 0 / Vb.toReal, div_nonneg (le_max_right c 0) ENNReal.toReal_nonneg,
    fun F hF => ?_⟩
  have hFc : Continuous F := by
    rw [continuous_iff_continuousAt]
    intro x
    obtain ⟨e', hx', hze'⟩ := hz x
    have he' : IsChart n z e' := fun y _ => by rw [hze']
    have h1 : ContinuousAt (F ∘ e'.symm) (e' x) :=
      (hF e' he').continuousOn.continuousAt (e'.open_target.mem_nhds (e'.map_source hx'))
    have h3 := h1.comp (e'.continuousAt hx')
    apply h3.congr
    filter_upwards [e'.open_source.mem_nhds hx'] with y hy
    simp [Function.comp, e'.left_inv hy]
  set f : M → ℝ≥0∞ := K.indicator (fun x => ‖F x‖ₑ ^ 2) with hfdef
  have hfm : Measurable f :=
    (hFc.measurable.enorm.pow_const 2).indicator hKc.isClosed.measurableSet
  have hdiff : DifferentiableOn ℂ (F ∘ e.symm) (Metric.ball (e x0) (r / 2)) :=
    (hF e he).mono (Metric.ball_subset_closedBall.trans hcb)
  have h1 := hMV n (e x0) (r / 2) (F ∘ e.symm) (fun _ => 1) hdiff measurable_const
  simp only [mul_one, lintegral_const, Measure.restrict_apply_univ, Function.comp_apply,
    e.left_inv hx0] at h1
  have h2 : ∫⁻ y in Metric.ball (e x0) (r / 2), ‖F (e.symm y)‖ₑ ^ 2 ≤
      ∫⁻ y in e.target, f (e.symm y) := by
    rw [← lintegral_indicator (hs := Metric.isOpen_ball.measurableSet),
      ← lintegral_indicator (hs := e.open_target.measurableSet)]
    apply lintegral_mono
    intro y
    by_cases hy : y ∈ Metric.ball (e x0) (r / 2)
    · have hyt : y ∈ e.target := hcb (Metric.ball_subset_closedBall hy)
      have hyK : e.symm y ∈ K := ⟨y, Metric.ball_subset_closedBall hy, rfl⟩
      simp [Set.indicator_apply, hy, hyt, hyK, hfdef]
    · simp [Set.indicator_apply, hy]
  have h3 : ∫⁻ y in e.target, f (e.symm y) = ∫⁻ x, f x ∂vol n z := by
    refine (lintegral_vol_chart n z hz e he f hfm (fun x hx => ?_)).symm
    have hxK : x ∉ K := fun h => hx (hKs h)
    simp [hfdef, Set.indicator_apply, hxK]
  have h4 : ∫⁻ x, f x ∂vol n z = ∫⁻ x in K, ‖F x‖ₑ ^ 2 ∂vol n z := by
    rw [hfdef, lintegral_indicator (hs := hKc.isClosed.measurableSet)]
  have h5 : ∫⁻ x in K, ‖F x‖ₑ ^ 2 ∂vol n z ≤ ENNReal.ofReal (max c 0) * wint n z F ψ :=
    (hc F).trans (by gcongr; exact le_max_left c 0)
  have hfin : ‖F x0‖ₑ ^ 2 * Vb ≤ ENNReal.ofReal (max c 0) * wint n z F ψ := by
    have h6 := h1.trans (h2.trans (h3.le.trans (h4.le.trans h5)))
    rwa [one_mul] at h6
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm,
    ENNReal.ofReal_div_of_pos (ENNReal.toReal_pos hVpos.ne' hVfin), ENNReal.ofReal_toReal hVfin,
    div_eq_mul_inv, mul_right_comm, ← div_eq_mul_inv,
    ENNReal.le_div_iff_mul_le (Or.inl hVpos.ne') (Or.inl hVfin)]
  exact hfin

end

end ReciprocityTheory.L2DbarEstimates.F
end

section -- merged from ReciprocityTheory.L2DbarEstimates.HormanderEstimate.ClosedCoreOfRegM
namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set
open scoped ENNReal

noncomputable section

theorem enorm_integral_sub_mul_le (n : ℕ) {M : Type*} [MeasurableSpace M] (z : M → V n)
    (ψ : M → ℝ) (hψ : Measurable ψ) (f F g : M → ℂ) (hf : AEStronglyMeasurable f (vol n z))
    (hF : AEStronglyMeasurable F (vol n z)) (hg : AEStronglyMeasurable g (vol n z)) :
    ‖∫ x, (f x - F x) * g x ∂vol n z‖ₑ ≤
      wint n z (fun x => F x - f x) ψ ^ (1 / 2 : ℝ) *
        (∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2 * Real.exp (ψ x)) ∂vol n z) ^ (1 / 2 : ℝ) := by
  have hw : AEMeasurable (fun x => ENNReal.ofReal (‖F x - f x‖ * Real.exp (-ψ x / 2))) (vol n z) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      ((hF.sub hf).norm.aemeasurable.mul (hψ.neg.div_const 2).exp.aemeasurable)
  have hv : AEMeasurable (fun x => ENNReal.ofReal (‖g x‖ * Real.exp (ψ x / 2))) (vol n z) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (hg.norm.aemeasurable.mul (hψ.div_const 2).exp.aemeasurable)
  have hpt : ∀ x, ‖(f x - F x) * g x‖ₑ = ENNReal.ofReal (‖F x - f x‖ * Real.exp (-ψ x / 2)) *
      ENNReal.ofReal (‖g x‖ * Real.exp (ψ x / 2)) := by
    intro x
    rw [← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ ‖F x - f x‖ * Real.exp (-ψ x / 2)),
      ← ofReal_norm_eq_enorm, norm_mul, norm_sub_rev (f x) (F x)]
    congr 1
    have h1 : Real.exp (-ψ x / 2) * Real.exp (ψ x / 2) = 1 := by
      rw [← Real.exp_add, show -ψ x / 2 + ψ x / 2 = 0 by ring, Real.exp_zero]
    calc ‖F x - f x‖ * ‖g x‖
        = ‖F x - f x‖ * ‖g x‖ * (Real.exp (-ψ x / 2) * Real.exp (ψ x / 2)) := by rw [h1, mul_one]
      _ = ‖F x - f x‖ * Real.exp (-ψ x / 2) * (‖g x‖ * Real.exp (ψ x / 2)) := by ring
  have hw2 : ∀ x, ENNReal.ofReal (‖F x - f x‖ * Real.exp (-ψ x / 2)) ^ (2:ℝ) =
      ENNReal.ofReal (‖F x - f x‖ ^ 2 * Real.exp (-ψ x)) := by
    intro x
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), Real.rpow_two, mul_pow,
      sq (Real.exp _), ← Real.exp_add]
    congr 3 <;> ring
  have hv2 : ∀ x, ENNReal.ofReal (‖g x‖ * Real.exp (ψ x / 2)) ^ (2:ℝ) =
      ENNReal.ofReal (‖g x‖ ^ 2 * Real.exp (ψ x)) := by
    intro x
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), Real.rpow_two, mul_pow,
      sq (Real.exp _), ← Real.exp_add]
    congr 3 <;> ring
  calc ‖∫ x, (f x - F x) * g x ∂vol n z‖ₑ
      ≤ ∫⁻ x, ‖(f x - F x) * g x‖ₑ ∂vol n z := by
        first
          | exact enorm_integral_le_lintegral_enorm _
          | exact ennnorm_integral_le_lintegral_ennnorm _
    _ = ∫⁻ x, ((fun x => ENNReal.ofReal (‖F x - f x‖ * Real.exp (-ψ x / 2))) *
          (fun x => ENNReal.ofReal (‖g x‖ * Real.exp (ψ x / 2)))) x ∂vol n z :=
        lintegral_congr (fun x => hpt x)
    _ ≤ (∫⁻ x, ENNReal.ofReal (‖F x - f x‖ * Real.exp (-ψ x / 2)) ^ (2:ℝ) ∂vol n z) ^ (1 / (2:ℝ)) *
          (∫⁻ x, ENNReal.ofReal (‖g x‖ * Real.exp (ψ x / 2)) ^ (2:ℝ) ∂vol n z) ^ (1 / (2:ℝ)) :=
        ENNReal.lintegral_mul_le_Lp_mul_Lq _
          (by first
            | exact Real.HolderConjugate.two_two
            | exact Real.IsConjExponent.two
            | (constructor <;> norm_num)) hw hv
    _ = _ := by simp only [hw2, hv2, wint]

theorem closedCore_of_regM (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (hReg : RegMStatement n M) :
    ClosedCoreStatement n M := by
  intro z hz ψ hψ F f hF hfm hlim
  haveI := vol_isFiniteMeasureOnCompacts n z hz
  have hψm : Measurable ψ := hψ.measurable
  have hFc : ∀ k, Continuous (F k) := fun k => Smooth.continuous n z hz _ (Holo.smooth n z _ (hF k))
  obtain ⟨k₀, hk₀⟩ : ∃ k₀, ∀ k ≥ k₀, wint n z (fun x => F k x - f x) ψ < ⊤ := by
    obtain ⟨k₀, hk⟩ := Filter.eventually_atTop.1 ((ENNReal.tendsto_nhds_zero.1 hlim) 1 one_pos)
    exact ⟨k₀, fun k hk' => lt_of_le_of_lt (hk k hk') ENNReal.one_lt_top⟩
  have hwsym : ∀ k, wint n z (fun x => f x - F k x) ψ = wint n z (fun x => F k x - f x) ψ := by
    intro k
    unfold wint
    congr 1
    funext x
    rw [norm_sub_rev]

  have hLoc : LocalL2Isometry (vol n z) (fun x => f x - F k₀ x) := by
    refine ⟨hfm.sub (hFc k₀).aestronglyMeasurable, fun C hC => ?_⟩
    obtain ⟨c, hc⟩ := exists_lintegral_compact_le n z ψ hψ C hC
    refine lt_of_le_of_lt (hc _) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_)
    rw [hwsym]
    exact hk₀ k₀ le_rfl

  have hweak : ∀ φ : M → ℂ, IsTest n z φ → ∀ j : Fin n,
      ∫ x, (f x - F k₀ x) * db n z j φ x ∂vol n z = 0 := by
    intro φ hφ j
    have hDc : Continuous (db n z j φ) := Smooth.continuous n z hz _ (Smooth.db n z j φ hφ.1)
    have hDs : HasCompactSupport (db n z j φ) := hφ.2.mono' ((subset_tsupport _).trans (tsupport_db_subset n z j φ))
    have hFD : ∀ k, Integrable (fun x => F k x * db n z j φ x) (vol n z) := fun k =>
      ((hFc k).mul hDc).integrable_of_hasCompactSupport hDs.mul_left
    by_cases hgi : Integrable (fun x => (f x - F k₀ x) * db n z j φ x) (vol n z)
    swap
    · exact integral_undef hgi
    have key : ∀ k, ∫ x, (f x - F k x) * db n z j φ x ∂vol n z =
        ∫ x, (f x - F k₀ x) * db n z j φ x ∂vol n z := by
      intro k
      have h0k := integral_holo_mul_db n z hz _ (hF k) φ hφ j
      have h00 := integral_holo_mul_db n z hz _ (hF k₀) φ hφ j
      calc ∫ x, (f x - F k x) * db n z j φ x ∂vol n z
          = ∫ x, ((f x - F k₀ x) * db n z j φ x -
              (F k x * db n z j φ x - F k₀ x * db n z j φ x)) ∂vol n z := by
            congr 1
            funext x
            ring
        _ = ∫ x, (f x - F k₀ x) * db n z j φ x ∂vol n z -
              ∫ x, (F k x * db n z j φ x - F k₀ x * db n z j φ x) ∂vol n z :=
            integral_sub hgi ((hFD k).sub (hFD k₀))
        _ = ∫ x, (f x - F k₀ x) * db n z j φ x ∂vol n z -
              (∫ x, F k x * db n z j φ x ∂vol n z - ∫ x, F k₀ x * db n z j φ x ∂vol n z) :=
            congrArg (fun s => ∫ x, (f x - F k₀ x) * db n z j φ x ∂vol n z - s)
              (integral_sub (hFD k) (hFD k₀))
        _ = ∫ x, (f x - F k₀ x) * db n z j φ x ∂vol n z := by
            rw [h0k, h00, sub_zero, sub_zero]
    have hB := lintegral_db_test_lt_top n z hz ψ hψ φ hφ j
    have hbound : ∀ k, ‖∫ x, (f x - F k₀ x) * db n z j φ x ∂vol n z‖ₑ ≤
        wint n z (fun x => F k x - f x) ψ ^ (1 / 2 : ℝ) *
          (∫⁻ x, ENNReal.ofReal (‖db n z j φ x‖ ^ 2 * Real.exp (ψ x)) ∂vol n z) ^ (1 / 2 : ℝ) := by
      intro k
      rw [← key k]
      exact enorm_integral_sub_mul_le n z ψ hψm f (F k) (db n z j φ) hfm
        (hFc k).aestronglyMeasurable hDc.aestronglyMeasurable
    have hlim2 : Tendsto (fun k => wint n z (fun x => F k x - f x) ψ ^ (1 / 2 : ℝ) *
        (∫⁻ x, ENNReal.ofReal (‖db n z j φ x‖ ^ 2 * Real.exp (ψ x)) ∂vol n z) ^ (1 / 2 : ℝ))
        atTop (𝓝 0) := by
      have h1 : Tendsto (fun k => wint n z (fun x => F k x - f x) ψ ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
        have := ((ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0).comp hlim
        rwa [ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at this
      have h2 := ENNReal.Tendsto.mul_const h1
        (Or.inr (ENNReal.rpow_ne_top_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) hB.ne))
      rwa [zero_mul] at h2
    have h0 : ‖∫ x, (f x - F k₀ x) * db n z j φ x ∂vol n z‖ₑ = 0 :=
      le_antisymm (ge_of_tendsto' hlim2 hbound) (zero_le')
    exact enorm_eq_zero.1 h0
  obtain ⟨G, hG, hfG⟩ := hReg z hz _ hLoc hweak
  refine ⟨fun x => G x + F k₀ x, fun e he => (hG e he).add (hF k₀ e he), ?_⟩
  filter_upwards [hfG] with x hx
  rw [← hx]
  ring

end

end ReciprocityTheory.L2DbarEstimates.F
end

namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set
open scoped ENNReal

noncomputable section

private lemma lintegral_enorm_sq_wvol_eq_wint (n : ℕ) {M : Type*} [MeasurableSpace M] (z : M → V n) (ψ : M → ℝ)
    (hψ : Measurable ψ) (u : M → ℂ) :
    ∫⁻ x, ‖u x‖ₑ ^ (2:ℝ) ∂(H.wvol n z ψ) = wint n z u ψ := by
  have hdm : Measurable fun x => ENNReal.ofReal (Real.exp (-ψ x)) :=
    (Real.measurable_exp.comp hψ.neg).ennreal_ofReal
  rw [H.wvol, lintegral_withDensity_eq_lintegral_mul_non_measurable _ hdm
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  unfold wint
  refine lintegral_congr fun x => ?_
  have h2 : ‖u x‖ₑ ^ (2:ℝ) = ENNReal.ofReal (‖u x‖ ^ 2) := by
    rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]
    norm_num
  simp only [Pi.mul_apply]
  rw [h2, ← ENNReal.ofReal_mul (Real.exp_pos _).le, mul_comm]

theorem needBergmanClosed (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (hReg : RegMStatement n M) :
    H.NeedBergmanClosed n M := by
  intro z hz ψ hψ
  have hdm : Measurable fun x => ENNReal.ofReal (Real.exp (-ψ x)) :=
    (Real.measurable_exp.comp hψ.measurable.neg).ennreal_ofReal
  have hac : vol n z ≪ H.wvol n z ψ :=
    withDensity_absolutelyContinuous' hdm.aemeasurable
      (ae_of_all _ fun x => (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne')
  have hac' : H.wvol n z ψ ≪ vol n z := withDensity_absolutelyContinuous _ _
  refine IsSeqClosed.isClosed ?_
  intro Fs F hFs hlim
  have hex : ∀ k, ∃ f : M → ℂ, Holo n z f ∧ (Fs k : M → ℂ) =ᵐ[H.wvol n z ψ] f := hFs
  choose fk hfk hFk using hex
  have hF : AEStronglyMeasurable (⇑F) (vol n z) := (Lp.aestronglyMeasurable F).mono_ac hac
  have key : ∀ k, eLpNorm (⇑(Fs k) - ⇑F) 2 (H.wvol n z ψ) =
      wint n z (fun x => fk k x - F x) ψ ^ (1 / (2:ℝ)) := by
    intro k
    rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal two_ne_zero ENNReal.ofNat_ne_top
      ((Lp.aestronglyMeasurable (Fs k)).sub (Lp.aestronglyMeasurable F))]
    simp only [ENNReal.toReal_ofNat]
    congr 1
    rw [lintegral_congr_ae (g := fun x => ‖fk k x - F x‖ₑ ^ (2:ℝ))
      ((hFk k).mono fun x hx => by simp only [Pi.sub_apply, hx])]
    exact lintegral_enorm_sq_wvol_eq_wint n z ψ hψ.measurable _
  have hT : Tendsto (fun k => wint n z (fun x => fk k x - F x) ψ) atTop (𝓝 0) := by
    have h1 := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).1 hlim
    have h2 := ((ENNReal.continuous_rpow_const (y := (2:ℝ))).tendsto 0).comp h1
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h2
    refine h2.congr fun k => ?_
    simp only [Function.comp_apply]
    rw [key k, ← ENNReal.rpow_mul]
    norm_num
  obtain ⟨G, hG, hFG⟩ := closedCore_of_regM n M hReg z hz ψ hψ fk (⇑F) hfk hF hT
  exact ⟨G, hG, hac'.ae_le hFG⟩

theorem holoClosedNeed (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (hReg : RegMStatement n M) :
    I.HoloClosedNeed n M := by
  intro X ps F f hps hF hf hT
  have hz : IsLocalHomeomorph X.z := X.isLocalHomeomorph
  have hc : Continuous ps := continuous_of_smoothR n X.z hz ps hps
  exact closedCore_of_regM n M hReg X.z hz ps hc F f hF hf.aestronglyMeasurable hT

theorem evalNeed (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (hMV : C.MVStatement) :
    I.EvalNeed n M := by
  intro X ps x0 hps
  have hz : IsLocalHomeomorph X.z := X.isLocalHomeomorph
  have hc : Continuous ps := continuous_of_smoothR n X.z hz ps hps
  obtain ⟨C, -, hC⟩ := evalPt n M hMV X.z hz ps hc x0
  exact ⟨C, hC⟩

end

end ReciprocityTheory.L2DbarEstimates.F
