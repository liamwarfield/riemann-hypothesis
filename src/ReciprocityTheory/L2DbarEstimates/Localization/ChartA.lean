module

public import ReciprocityTheory.L2DbarEstimates.Localization.UnweightBackStatement
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.IntegralFderivApplyEqZero

@[expose] public section

section -- merged from ReciprocityTheory.L2DbarEstimates.Localization.ChartA
namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set Function
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff

noncomputable section

section Tr

variable {M : Type*} [TopologicalSpace M] [SecondCountableTopology M] [MeasurableSpace M]
  [BorelSpace M] {n : ℕ} {z : M → V n} {e : OpenPartialHomeomorph M (V n)}

theorem chT_aem_symm : AEMeasurable (e.symm : V n → M) (volume.restrict e.target) := e.continuousOn_symm.aemeasurable e.open_target.measurableSet

theorem chT_lint (hz : IsLocalHomeomorph z) (he : IsChart n z e) (f : M → ℝ≥0∞)
    (hf : AEMeasurable f (vol n z)) (hs : ∀ x, x ∉ e.source → f x = 0) :
    ∫⁻ x, f x ∂vol n z = ∫⁻ y in e.target, f (e.symm y) := by
  have hsub : Function.support f ⊆ e.source := fun x hx => by
    by_contra h; exact hx (hs x h)
  rw [← setLIntegral_eq_of_support_subset hsub, vol_restrict_source n z hz e he]
  have hf' : AEMeasurable f (Measure.map e.symm (volume.restrict e.target)) := by
    rw [← vol_restrict_source n z hz e he]; exact hf.restrict
  exact lintegral_map' hf' (chT_aem_symm (e := e))

theorem chT_int {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (hz : IsLocalHomeomorph z)
    (he : IsChart n z e) (f : M → E)
    (hf : AEStronglyMeasurable f (vol n z)) (hs : ∀ x, x ∉ e.source → f x = 0) :
    ∫ x, f x ∂vol n z = ∫ y in e.target, f (e.symm y) := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hs, vol_restrict_source n z hz e he]
  have hf' : AEStronglyMeasurable f (Measure.map e.symm (volume.restrict e.target)) := by
    rw [← vol_restrict_source n z hz e he]; exact hf.restrict
  exact integral_map (chT_aem_symm (e := e)) hf'

theorem chT_aesm {E : Type*} [NormedAddCommGroup E] (hz : IsLocalHomeomorph z)
    (he : IsChart n z e) (f : M → E) (hf : AEStronglyMeasurable f (vol n z)) :
    AEStronglyMeasurable (e.target.indicator (f ∘ e.symm)) volume := by
  have hf' : AEStronglyMeasurable f (Measure.map e.symm (volume.restrict e.target)) := by
    rw [← vol_restrict_source n z hz e he]; exact hf.restrict
  exact (aestronglyMeasurable_indicator_iff e.open_target.measurableSet).2
    (hf'.comp_aemeasurable (chT_aem_symm (e := e)))

theorem chartTransport_indicator_memLp_two {E : Type*} [NormedAddCommGroup E] [T2Space M] (hz : IsLocalHomeomorph z)
    (he : IsChart n z e) (f : M → E) (hf : LocalL2Isometry (vol n z) f) (hc : HasCompactSupport f)
    (hsub : tsupport f ⊆ e.source) :
    MemLp (e.target.indicator (f ∘ e.symm)) 2 volume := by
  have hae := chT_aesm hz he f hf.1
  apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    two_ne_zero ENNReal.ofNat_ne_top hae).2
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  have hz0 : ∀ x, x ∉ tsupport f → f x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have hs : ∀ x, x ∉ e.source → ‖f x‖ₑ ^ 2 = 0 := by
    intro x hx
    simp [hz0 x (fun h => hx (hsub h))]
  have e1 : ∫⁻ y, ‖e.target.indicator (f ∘ e.symm) y‖ₑ ^ 2 =
      ∫⁻ y in e.target, ‖f (e.symm y)‖ₑ ^ 2 := by
    rw [← lintegral_indicator e.open_target.measurableSet]
    congr 1; funext y
    by_cases hy : y ∈ e.target <;> simp [hy]
  rw [e1, ← chT_lint hz he (fun x => ‖f x‖ₑ ^ 2) (hf.1.enorm.pow_const 2) hs]
  calc ∫⁻ x, ‖f x‖ₑ ^ 2 ∂vol n z = ∫⁻ x in tsupport f, ‖f x‖ₑ ^ 2 ∂vol n z := by
        rw [setLIntegral_eq_of_support_subset]
        intro x hx
        by_contra h
        exact hx (by simp [hz0 x h])
    _ < ⊤ := hf.2 _ hc

end Tr

theorem chT_plateau {n : ℕ} (K U : Set (V n)) (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ ρ : V n → ℝ, ContDiff ℝ ∞ ρ ∧ HasCompactSupport ρ ∧ tsupport ρ ⊆ U ∧
      ∃ O : Set (V n), IsOpen O ∧ K ⊆ O ∧ ∀ y ∈ O, ρ y = 1 := by
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  obtain ⟨t, htK, htf, hcov⟩ := hK.finite_cover_balls (e := δ / 3) (by positivity)
  let bx : ∀ x : V n, ContDiffBump x := fun x => ⟨δ / 3, 2 * δ / 3, by positivity, by linarith⟩
  let ψ : V n → ℝ := fun y => ∑ x ∈ htf.toFinset, bx x y
  let ρ : V n → ℝ := fun y => Real.smoothTransition (ψ y)
  have hψd : ContDiff ℝ ∞ ψ := ContDiff.sum fun x _ => (bx x).contDiff
  have hρd : ContDiff ℝ ∞ ρ := Real.smoothTransition.contDiff.comp hψd
  have hsuppψ : ∀ y, ψ y ≠ 0 → y ∈ Metric.cthickening (2 * δ / 3) K := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := Finset.exists_ne_zero_of_sum_ne_zero hy
    have hb : y ∈ Metric.ball x (bx x).rOut := by rw [← (bx x).support_eq]; exact hxy
    exact Metric.thickening_subset_cthickening _ _
      (Metric.ball_subset_thickening (htK (htf.mem_toFinset.1 hx)) _ hb)
  have hsuppρ : ∀ y, y ∉ Metric.cthickening (2 * δ / 3) K → ρ y = 0 := by
    intro y hy
    have : ψ y = 0 := by by_contra h; exact hy (hsuppψ y h)
    simp only [ρ, this, Real.smoothTransition.zero]
  have hts : tsupport ρ ⊆ Metric.cthickening (2 * δ / 3) K :=
    closure_minimal (fun y hy => by by_contra h; exact hy (hsuppρ y h)) Metric.isClosed_cthickening
  refine ⟨ρ, hρd, HasCompactSupport.intro hK.cthickening hsuppρ,
    hts.trans ((Metric.cthickening_mono (by linarith) K).trans hδU),
    ⋃ x ∈ t, Metric.ball x (δ / 3), isOpen_biUnion fun _ _ => Metric.isOpen_ball, hcov, ?_⟩
  intro y hy
  simp only [Set.mem_iUnion] at hy
  obtain ⟨x, hx, hxy⟩ := hy
  have h1 : bx x y = 1 := (bx x).one_of_mem_closedBall (Metric.ball_subset_closedBall hxy)
  have h2 : 1 ≤ ψ y := by
    calc (1 : ℝ) = bx x y := h1.symm
      _ ≤ ψ y := Finset.single_le_sum (f := fun x' => bx x' y) (fun x' _ => (bx x').nonneg)
          (htf.mem_toFinset.2 hx)
  exact Real.smoothTransition.one_of_one_le h2

theorem chT_comp {n : ℕ} {M : Type*} [MeasurableSpace M] (μ : Measure M) (G : M → V n)
    (hG : AEStronglyMeasurable G μ) (j : Fin n) : AEStronglyMeasurable (fun x => G x j) μ := (EuclideanSpace.proj (𝕜 := ℂ) j).continuous.comp_aestronglyMeasurable hG

section Main

variable {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M] {n : ℕ} {z : M → V n} {e : OpenPartialHomeomorph M (V n)}

theorem chT_test (hExt : ExtendStatement n M) (hz : IsLocalHomeomorph z) (he : IsChart n z e)
    (ψ : V n → ℂ) (hψd : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψt : tsupport ψ ⊆ e.target) :
    IsTest n z (e.source.indicator (ψ ∘ e)) ∧
    (∀ y ∈ e.target, e.source.indicator (ψ ∘ e) (e.symm y) = ψ y) ∧
    (∀ j, ∀ y ∈ e.target, d n z j (e.source.indicator (ψ ∘ e)) (e.symm y) = wd n j ψ y ∧
        db n z j (e.source.indicator (ψ ∘ e)) (e.symm y) = wdb n j ψ y) := by
  obtain ⟨h1, h2, -, h4⟩ := hExt z hz e ψ he hψd hψc hψt
  refine ⟨⟨h1, h2⟩, fun y hy => ?_, fun j y hy => ?_⟩
  · rw [Set.indicator_of_mem (e.map_target hy), Function.comp_apply, e.right_inv hy]
  · have := h4 j (e.symm y) (e.map_target hy)
    rw [e.right_inv hy] at this
    exact this

theorem chT_mulρ (ρ : V n → ℝ) (hρd : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ)
    (U : Set (V n)) (hρt : tsupport ρ ⊆ U) (φ : V n → ℂ) (hφd : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (fun y => (ρ y : ℂ) * φ y) ∧ HasCompactSupport (fun y => (ρ y : ℂ) * φ y) ∧
      tsupport (fun y => (ρ y : ℂ) * φ y) ⊆ U := by
  refine ⟨(Complex.ofRealCLM.contDiff.comp hρd).mul hφd, ?_, ?_⟩
  · exact (hρc.comp_left Complex.ofReal_zero).mul_right
  · exact tsupport_mul_subset_left.trans ((tsupport_comp_subset Complex.ofReal_zero ρ).trans hρt)

theorem chT_wd (ρ : V n → ℝ) (φ : V n → ℂ) (O : Set (V n)) (hOo : IsOpen O)
    (h1 : ∀ y ∈ O, ρ y = 1) (y : V n) (hy : y ∈ O) (j : Fin n) :
    wd n j (fun y => (ρ y : ℂ) * φ y) y = wd n j φ y ∧
      wdb n j (fun y => (ρ y : ℂ) * φ y) y = wdb n j φ y := by
  have hev : (fun y => (ρ y : ℂ) * φ y) =ᶠ[𝓝 y] φ := by
    filter_upwards [hOo.mem_nhds hy] with w hw
    rw [h1 w hw]; simp
  have := hev.fderiv_eq (𝕜 := ℝ)
  unfold wd wdb
  rw [this]
  exact ⟨rfl, rfl⟩

end Main

end

end ReciprocityTheory.L2DbarEstimates.F
end

section -- merged from ReciprocityTheory.L2DbarEstimates.Localization.Locality
namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff

noncomputable section

private lemma d_apply_eq_zero_of_eventuallyEq_zero {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (j : Fin n)
    (f : M → ℂ) (x : M) (hf : f =ᶠ[𝓝 x] 0) : d n z j f x = 0 := by
  unfold d
  split_ifs with h
  · set e := Classical.choose h
    have he := Classical.choose_spec h
    have hzx : z x = e x := he.1 he.2
    have ht : Tendsto e.symm (𝓝 (e x)) (𝓝 x) := by
      have hc := e.continuousAt_symm (e.map_source he.2)
      rw [ContinuousAt, e.left_inv he.2] at hc
      exact hc
    have hg : (f ∘ e.symm) =ᶠ[𝓝 (e x)] fun _ => (0 : ℂ) :=
      (ht.eventually hf).mono fun y hy => by simpa using hy
    rw [hzx]
    unfold wd
    rw [hg.fderiv_eq]
    simp
  · rfl

theorem locality (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : LocalityStatement n M := by
  intro z _ ph ph' ψ U f _ _ hsupp hph
  have hfz : ∀ x, x ∉ U → f x = 0 := by
    intro x hx
    by_contra h
    exact hx (hsupp (subset_tsupport _ h))
  have hfun : ∀ j, (fun y => (Real.exp (-(w2 ph' ψ y)) : ℂ) * f y j) =
      fun y => (Real.exp (-ph y) : ℂ) * f y j := by
    intro j
    funext y
    by_cases hy : y ∈ U
    · simp [w2, (hph y hy).1, (hph y hy).2]
    · simp [hfz y hy]
  refine ⟨?_, ?_⟩
  · intro v
    unfold ipV
    congr 1
    funext x
    by_cases hx : x ∈ U
    · simp [w2, (hph x hx).1, (hph x hx).2]
    · simp [hfz x hx]
  · unfold wint
    apply lintegral_congr
    intro x
    unfold tstar
    simp_rw [hfun]
    by_cases hx : x ∈ U
    · have h1 : w1 ph' ψ x = ph x := by simp [w1, (hph x hx).1, (hph x hx).2]
      rw [h1]
    · have hx' : x ∉ tsupport f := fun h => hx (hsupp h)
      have hev : f =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.1 hx'
      have hS : ∀ j, d n z j (fun y => (Real.exp (-ph y) : ℂ) * f y j) x = 0 := fun j =>
        d_apply_eq_zero_of_eventuallyEq_zero n z j _ x (hev.mono fun y hy => by simp [hy])
      rw [Finset.sum_eq_zero (fun j _ => hS j)]
      simp

end

end ReciprocityTheory.L2DbarEstimates.F
end

section -- merged from ReciprocityTheory.L2DbarEstimates.Localization.Extend
namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff

noncomputable section

theorem extend_support_subset {n : ℕ} {M : Type*} [TopologicalSpace M]
    (e : OpenPartialHomeomorph M (V n)) (G : V n → ℂ) (q : M)
    (hq : e.source.indicator (G ∘ e) q ≠ 0) : q ∈ e.symm '' tsupport G := by
  have hq' : q ∈ e.source := by
    by_contra h; exact hq (Set.indicator_of_notMem h _)
  rw [Set.indicator_of_mem hq'] at hq
  exact ⟨e q, subset_tsupport _ hq, e.left_inv hq'⟩

theorem extend_eventuallyEq {n : ℕ} {M : Type*} [TopologicalSpace M] (z : M → V n)
    (e e' : OpenPartialHomeomorph M (V n)) (G : V n → ℂ) (he : IsChart n z e)
    (he' : IsChart n z e') (y : V n) (hy : y ∈ e'.target) (hs : e'.symm y ∈ e.source) :
    (e.source.indicator (G ∘ e) ∘ e'.symm) =ᶠ[𝓝 y] G := by
  have hopen : IsOpen (e'.target ∩ e'.symm ⁻¹' e.source) :=
    e'.isOpen_inter_preimage_symm e.open_source
  filter_upwards [hopen.mem_nhds ⟨hy, hs⟩] with w hw
  obtain ⟨hw1, hw2⟩ := hw
  have hw3 : e'.symm w ∈ e'.source := e'.map_target hw1
  rw [Function.comp_apply, Set.indicator_of_mem (show e'.symm w ∈ e.source from hw2), Function.comp_apply, ← he hw2, he' hw3,
    e'.right_inv hw1]

theorem extend (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : ExtendStatement n M := by
  intro z _hz e G he hG hGc hGt
  have hK : IsCompact (e.symm '' tsupport G) :=
    hGc.image_of_continuousOn (e.continuousOn_symm.mono hGt)
  have hKs : e.symm '' tsupport G ⊆ e.source := by
    rintro _ ⟨y, hy, rfl⟩; exact e.map_target (hGt hy)
  have hts : tsupport (e.source.indicator (G ∘ e)) ⊆ e.symm '' tsupport G :=
    closure_minimal (fun q hq => extend_support_subset e G q hq) hK.isClosed
  have hw : ∀ e'' : OpenPartialHomeomorph M (V n), IsChart n z e'' → ∀ x ∈ e''.source, x ∈ e.source →
      (e.source.indicator (G ∘ e) ∘ e''.symm) =ᶠ[𝓝 (z x)] G ∧ z x = e x := by
    intro e'' h1 x h2 hx
    have hzx : z x = e'' x := h1 h2
    refine ⟨?_, he hx⟩
    rw [hzx]
    refine extend_eventuallyEq z e e'' G he h1 (e'' x) (e''.map_source h2) ?_
    rw [e''.left_inv h2]; exact hx
  refine ⟨?_, hK.of_isClosed_subset (isClosed_tsupport _) hts, hts.trans hKs, ?_⟩
  · intro e' he' y hy
    by_cases hs : e'.symm y ∈ e.source
    · exact (hG.contDiffAt.congr_of_eventuallyEq
        (extend_eventuallyEq z e e' G he he' y hy hs)).contDiffWithinAt
    · have hq : e'.symm y ∉ tsupport (e.source.indicator (G ∘ e)) := fun h => hs (hKs (hts h))
      have h0 := notMem_tsupport_iff_eventuallyEq.1 hq
      have h0' := h0.comp_tendsto (e'.continuousAt_symm hy).tendsto
      exact (contDiffAt_const.congr_of_eventuallyEq h0').contDiffWithinAt
  · intro j x hx
    have key : ∀ e'' : OpenPartialHomeomorph M (V n), IsChart n z e'' → x ∈ e''.source →
        wd n j (e.source.indicator (G ∘ e) ∘ e''.symm) (z x) = wd n j G (e x) ∧
        wdb n j (e.source.indicator (G ∘ e) ∘ e''.symm) (z x) = wdb n j G (e x) := by
      intro e'' h1 h2
      obtain ⟨hev, hzx⟩ := hw e'' h1 x h2 hx
      constructor
      · unfold wd; rw [hev.fderiv_eq, hzx]
      · unfold wdb; rw [hev.fderiv_eq, hzx]
    have hex : ∃ e'' : OpenPartialHomeomorph M (V n), IsChart n z e'' ∧ x ∈ e''.source := ⟨e, he, hx⟩
    constructor
    · simp only [d, dif_pos hex]
      exact (key _ (Classical.choose_spec hex).1 (Classical.choose_spec hex).2).1
    · simp only [db, dif_pos hex]
      exact (key _ (Classical.choose_spec hex).1 (Classical.choose_spec hex).2).2

end

end ReciprocityTheory.L2DbarEstimates.F
end

section -- merged from ReciprocityTheory.L2DbarEstimates.Localization.KPsiHasCompactSupport
namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff

noncomputable section

theorem wvol_finiteOnCompacts {M : Type*} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (ph : M → ℝ) (hph : Continuous ph) :
    IsFiniteMeasureOnCompacts (wvol n z ph) := by
  have := vol_isFiniteMeasureOnCompacts n z hz
  refine ⟨fun K hK => ?_⟩
  have hc : ContinuousOn (fun x => Real.exp (-ph x)) K :=
    (Real.continuous_exp.comp hph.neg).continuousOn
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc
  unfold wvol
  rw [withDensity_apply _ hK.measurableSet]
  calc ∫⁻ x in K, ENNReal.ofReal (Real.exp (-ph x)) ∂vol n z
      ≤ ∫⁻ _ in K, ENNReal.ofReal C ∂vol n z := by
        refine setLIntegral_mono' hK.measurableSet fun x hx => ENNReal.ofReal_le_ofReal ?_
        have h := hC x hx
        rwa [Real.norm_of_nonneg (Real.exp_pos _).le] at h
    _ = ENNReal.ofReal C * vol n z K := setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top

def kPsi {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (ph : M → ℝ) (φ : M → ℂ)
    (j k : Fin n) : M → V n :=
  fun x => ((Real.exp (ph x) : ℝ) : ℂ) •
    ((starRingEnd ℂ) (db n z j φ x) • bas n k - (starRingEnd ℂ) (db n z k φ x) • bas n j)

theorem kPsi_inner {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (ph : M → ℝ)
    (φ : M → ℂ) (j k : Fin n) (v : V n) (x : M) :
    (ENNReal.ofReal (Real.exp (-ph x))).toReal • ⟪kPsi n z ph φ j k x, v⟫_ℂ =
      v k * db n z j φ x - v j * db n z k φ x := by
  have h1 : (Real.exp (-ph x) : ℂ) * (Real.exp (ph x) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    simp
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le]
  simp only [kPsi, bas, inner_smul_left, inner_sub_left, EuclideanSpace.inner_single_left,
    Complex.conj_ofReal, Complex.conj_conj, map_one, one_mul, Complex.real_smul]
  linear_combination (v k * db n z j φ x - v j * db n z k φ x) * h1

theorem kPsi_continuous {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (ph : M → ℝ) (hph : Continuous ph) (φ : M → ℂ)
    (hφ : IsTest n z φ) (j k : Fin n) : Continuous (kPsi n z ph φ j k) := by
  have hj := Smooth.continuous n z hz _ (Smooth.db n z j φ hφ.1)
  have hk := Smooth.continuous n z hz _ (Smooth.db n z k φ hφ.1)
  unfold kPsi
  refine (Complex.continuous_ofReal.comp (Real.continuous_exp.comp hph)).smul ?_
  exact ((Complex.continuous_conj.comp hj).smul continuous_const).sub
    ((Complex.continuous_conj.comp hk).smul continuous_const)

theorem kPsi_hasCompactSupport {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (ph : M → ℝ) (φ : M → ℂ) (hφ : IsTest n z φ) (j k : Fin n) :
    HasCompactSupport (kPsi n z ph φ j k) := by
  refine hφ.2.mono' fun x hx => ?_
  by_contra hnot
  have hj : db n z j φ x = 0 := by
    by_contra h
    exact hnot (tsupport_db_subset n z j φ (subset_tsupport _ h))
  have hk : db n z k φ x = 0 := by
    by_contra h
    exact hnot (tsupport_db_subset n z k φ (subset_tsupport _ h))
  exact hx (by simp [kPsi, hj, hk])

theorem kSub (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : KSubStatement n M := by
  unfold KSubStatement
  intro z hz ph₂ hph
  have : IsFiniteMeasureOnCompacts (wvol n z ph₂) := wvol_finiteOnCompacts n z hz ph₂ hph
  have hmem : ∀ φ, IsTest n z φ → ∀ j k, MemLp (kPsi n z ph₂ φ j k) 2 (wvol n z ph₂) :=
    fun φ hφ j k => (kPsi_continuous n z hz ph₂ hph φ hφ j k).memLp_of_hasCompactSupport
      (kPsi_hasCompactSupport n z ph₂ φ hφ j k)
  have hmeas : Measurable fun x => ENNReal.ofReal (Real.exp (-ph₂ x)) :=
    (Real.continuous_exp.comp hph.neg).measurable.ennreal_ofReal

  have hw : ∀ g : M → ℂ, ∫ x, g x ∂wvol n z ph₂ =
      ∫ x, (ENNReal.ofReal (Real.exp (-ph₂ x))).toReal • g x ∂vol n z :=
    fun g => integral_withDensity_eq_integral_toReal_smul hmeas
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top) g
  have key : ∀ φ (hφ : IsTest n z φ) j k (F : Lp (V n) 2 (wvol n z ph₂)),
      ⟪(hmem φ hφ j k).toLp (kPsi n z ph₂ φ j k), F⟫_ℂ =
        ∫ x, (F x k * db n z j φ x - F x j * db n z k φ x) ∂vol n z := by
    intro φ hφ j k F
    rw [MeasureTheory.L2.inner_def]
    have hae := (hmem φ hφ j k).coeFn_toLp
    rw [integral_congr_ae (g := fun x => ⟪kPsi n z ph₂ φ j k x, F x⟫_ℂ)
      (by filter_upwards [hae] with x hx; rw [hx]), hw]
    exact integral_congr_ae (ae_of_all _ fun x => kPsi_inner n z ph₂ φ j k (F x) x)
  refine ⟨⨅ (φ : M → ℂ) (hφ : IsTest n z φ) (j : Fin n) (k : Fin n),
      LinearMap.ker ((innerSL ℂ ((hmem φ hφ j k).toLp (kPsi n z ph₂ φ j k)) :
        Lp (V n) 2 (wvol n z ph₂) →L[ℂ] ℂ) : Lp (V n) 2 (wvol n z ph₂) →ₗ[ℂ] ℂ), ?_, ?_⟩
  · simp only [Submodule.coe_iInf]
    exact isClosed_iInter fun φ => isClosed_iInter fun hφ => isClosed_iInter fun j =>
      isClosed_iInter fun k => ContinuousLinearMap.isClosed_ker _
  · intro F
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, innerSL_apply_apply]
    unfold IsWeakS
    refine forall_congr' fun φ => forall_congr' fun hφ => forall_congr' fun j =>
      forall_congr' fun k => ?_
    beta_reduce
    rw [key φ hφ j k F]
    simp

end

end ReciprocityTheory.L2DbarEstimates.F
end

section -- merged from ReciprocityTheory.L2DbarEstimates.Localization.Choice
namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff

noncomputable section

theorem smoothReal_continuous {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (f : M → ℝ) (hf : SmoothR n z f) : Continuous f := by
  have hc : Continuous (fun x => (f x : ℂ)) := by
    refine continuous_iff_continuousAt.mpr fun x => ?_
    obtain ⟨e, hxe, rfl⟩ := hz x
    have hch : IsChart n (⇑e) e := fun _ _ => rfl
    have h1 := (hf e hch).continuousOn
    have h2 : ContinuousOn (fun y => (f y : ℂ)) e.source := by
      refine (h1.comp e.continuousOn (fun y hy => e.map_source hy)).congr fun y hy => ?_
      simp [Function.comp, e.left_inv hy]
    exact h2.continuousAt (e.open_source.mem_nhds hxe)
  exact (Complex.continuous_re.comp hc).congr fun x => by simp

theorem sSup_image_le_max {M : Type*} (g : M → ℝ) (s : Set M) (B : ℝ)
    (hB : ∀ x ∈ s, g x ≤ B) : sSup (g '' s) ≤ max B 0 := by
  refine Real.sSup_le ?_ (le_max_right _ _)
  rintro _ ⟨x, hx, rfl⟩
  exact (hB x hx).trans (le_max_left _ _)

theorem choice (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (hChi : ChiStatement) (hPsi : PsiStatement n M)
    (hShell : ShellStatement n M) (hLZ : LeviNormSqStatement n M) (hChain : ChainStatement n M) :
    ChoiceStatement n M := by
  intro X ph v C ε hph hv hC hε
  have hz := X.isLocalHomeomorph

  have hE : SmoothR n X.z (fun y => X.e y + ‖X.z y‖ ^ 2) :=
    SmoothR.add n X.z _ _ X.smooth_e (hLZ X.z hz).1
  have hEc : Continuous (fun y => X.e y + ‖X.z y‖ ^ 2) := smoothReal_continuous n X.z hz _ hE
  have hExh : ∀ b : ℝ, IsCompact {x | X.e x + ‖X.z x‖ ^ 2 ≤ b} := by
    intro b
    refine (X.isCompact_le b).of_isClosed_subset (isClosed_le hEc continuous_const) ?_
    intro x hx
    simp only [mem_ofPred_eq] at hx ⊢
    nlinarith [sq_nonneg ‖X.z x‖]
  have hLeviE : ∀ x ξ, (∑ j, ‖ξ j‖ ^ 2) ≤ (Levi n X.z (fun y => X.e y + ‖X.z y‖ ^ 2) x ξ).re := by
    intro x ξ
    rw [levi_add n X.z X.e (fun y => ‖X.z y‖ ^ 2) (SmoothR.ckR n X.z 2 _ X.smooth_e)
      (SmoothR.ckR n X.z 2 _ (hLZ X.z hz).1) x ξ, (hLZ X.z hz).2 x ξ, Complex.add_re,
      Complex.ofReal_re]
    linarith [X.levi_e x ξ]

  obtain ⟨b0, hb0⟩ := hC.bddAbove_image hEc.continuousOn
  set a : ℝ := b0 + 1 with ha
  have hCa : ∀ x ∈ C, X.e x + ‖X.z x‖ ^ 2 < a := by
    intro x hx
    have := hb0 ⟨x, hx, rfl⟩
    linarith

  obtain ⟨ψ, hψ, hψ0, hcut⟩ := hPsi X.z hz (fun y => X.e y + ‖X.z y‖ ^ 2) a hE hExh
  have hψc : Continuous ψ := smoothReal_continuous n X.z hz _ hψ
  have hdc : Continuous (fun x => dSqR n X.z ψ x) := by
    unfold dSqR
    refine continuous_finsetSum _ (fun j _ => ?_)
    exact ((Smooth.continuous n X.z hz _ (Smooth.d n X.z j _ hψ)).norm).pow 2

  obtain ⟨R1, hR1, hR1χ⟩ := hShell X.z hz (fun y => X.e y + ‖X.z y‖ ^ 2) ph ψ v a hEc hExh
    (smoothReal_continuous n X.z hz _ hph) hψc hv
  set g : M → ℝ := fun x => max (2 * ψ x) ((1 + 1 / ε) * dSqR n X.z ψ x) with hg
  have hgc : Continuous g := (continuous_const.mul hψc).max (continuous_const.mul hdc)
  set R : ℝ → ℝ := fun t => max (R1 t) (sSup (g '' {x | X.e x + ‖X.z x‖ ^ 2 ≤ t})) with hR
  have hRb : ∀ b : ℝ, BddAbove (R '' Iic b) := by
    intro b
    obtain ⟨B1, hB1⟩ := hR1 b
    obtain ⟨B, hB⟩ := (hExh b).bddAbove_image hgc.continuousOn
    refine ⟨max B1 (max B 0), ?_⟩
    rintro y ⟨t, ht, rfl⟩
    refine max_le_max (hB1 ⟨t, ht, rfl⟩) (sSup_image_le_max g _ B ?_)
    intro x hx
    exact hB ⟨x, (show X.e x + ‖X.z x‖ ^ 2 ≤ b from le_trans hx ht), rfl⟩
  have hgR : ∀ x, g x ≤ R (X.e x + ‖X.z x‖ ^ 2) := by
    intro x
    refine le_max_of_le_right (le_csSup ((hExh _).bddAbove_image hgc.continuousOn) ⟨x, ?_, rfl⟩)
    exact (le_refl (X.e x + ‖X.z x‖ ^ 2))

  obtain ⟨χ, hχ, hχa, hχ0, hχ1, hχ2, hχR⟩ := hChi a R hRb
  have hχs : SmoothR n X.z (fun y => χ (X.e y + ‖X.z y‖ ^ 2)) := SmoothR.comp n X.z χ hχ _ hE
  refine ⟨fun x => ph x + χ (X.e x + ‖X.z x‖ ^ 2), ψ, fun y => X.e y + ‖X.z y‖ ^ 2,
    {x | X.e x + ‖X.z x‖ ^ 2 < a}, SmoothR.add n X.z _ _ hph hχs, hψ, hEc, hcut,
    isOpen_lt hEc continuous_const, hCa, ?_, ?_, ?_, ?_⟩
  · intro x hx
    simp only [mem_ofPred_eq] at hx
    refine ⟨?_, (hψ0 x (by linarith)).1⟩
    show ph x + χ (X.e x + ‖X.z x‖ ^ 2) = ph x
    rw [hχa _ hx.le, add_zero]
  · intro x
    have : 2 * ψ x ≤ χ (X.e x + ‖X.z x‖ ^ 2) := by
      by_cases h : X.e x + ‖X.z x‖ ^ 2 ≤ a + 1
      · rw [(hψ0 x h).1, mul_zero]; exact hχ0 _
      · push Not at h
        exact ((le_max_left _ _).trans (hgR x)).trans (hχR _ h.le).1
    linarith
  · intro x ξ
    have hχ2' : ContDiff ℝ 2 χ := hχ.of_le (by norm_cast)
    rw [levi_add n X.z ph (fun y => χ (X.e y + ‖X.z y‖ ^ 2)) (SmoothR.ckR n X.z 2 _ hph)
      (SmoothR.ckR n X.z 2 _ hχs) x ξ, Complex.add_re,
      hChain X.z hz χ (fun y => X.e y + ‖X.z y‖ ^ 2) hχ2' hE x ξ, Complex.add_re,
      Complex.re_ofReal_mul, Complex.re_ofReal_mul, Complex.ofReal_re]
    have hs : 0 ≤ ∑ j, ‖ξ j‖ ^ 2 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
    have h1 : (1 + 1 / ε) * dSqR n X.z ψ x * ∑ j, ‖ξ j‖ ^ 2 ≤
        deriv χ (X.e x + ‖X.z x‖ ^ 2) * ∑ j, ‖ξ j‖ ^ 2 := by
      by_cases h : X.e x + ‖X.z x‖ ^ 2 ≤ a + 1
      · rw [(hψ0 x h).2, mul_zero, zero_mul]
        exact mul_nonneg (hχ1 _) hs
      · push Not at h
        exact mul_le_mul_of_nonneg_right
          (((le_max_right _ _).trans (hgR x)).trans (hχR _ h.le).2) hs
    have h2 : deriv χ (X.e x + ‖X.z x‖ ^ 2) * ∑ j, ‖ξ j‖ ^ 2 ≤
        deriv χ (X.e x + ‖X.z x‖ ^ 2) *
          (Levi n X.z (fun y => X.e y + ‖X.z y‖ ^ 2) x ξ).re :=
      mul_le_mul_of_nonneg_left (hLeviE x ξ) (hχ1 _)
    have h3 : 0 ≤ deriv (deriv χ) (X.e x + ‖X.z x‖ ^ 2) *
        ‖dDot n X.z (fun y => ((X.e y + ‖X.z y‖ ^ 2 : ℝ) : ℂ)) x ξ‖ ^ 2 :=
      mul_nonneg (hχ2 _) (sq_nonneg _)
    linarith
  · refine ⟨hv.aestronglyMeasurable, ?_⟩
    exact hR1χ χ hχ0 (fun t ht => (hχR t ht).1.trans' (le_max_left _ _))

end

end ReciprocityTheory.L2DbarEstimates.F
end

section -- merged from ReciprocityTheory.L2DbarEstimates.Localization.SSmooth
namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff

noncomputable section

theorem weakSSmooth (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : WeakSSmoothStatement n M := by
  intro z hz f hf φ hφ j k
  have hφ1 : Ck n z 1 φ := Smooth.ck n z 1 φ hφ.1
  have hcd : ∀ i : Fin n, HasCompactSupport (db n z i φ) := fun i =>
    hφ.2.mono' ((subset_tsupport _).trans (tsupport_db_subset n z i φ))
  have hcont : ∀ i : Fin n, Continuous (db n z i φ) := fun i =>
    Ck.continuous n z hz 0 _ (Ck.db n z 0 i φ hφ1)
  have hfc : ∀ i : Fin n, Continuous (fun y => f y i) := fun i => Ck.continuous n z hz 1 _ (hf i)
  have hI1 : ∀ a b : Fin n, Integrable (fun x => f x a * db n z b φ x) (vol n z) := fun a b =>
    integrable_of_continuous n z hz _ ((hfc a).mul (hcont b)) ((hcd b).mul_left)
  have hI2 : ∀ a b : Fin n, Integrable (fun x => db n z b (fun y => f y a) x * φ x) (vol n z) :=
    fun a b => integrable_of_continuous n z hz _
      ((Ck.continuous n z hz 0 _ (Ck.db n z 0 b _ (hf a))).mul (Ck.continuous n z hz 1 _ hφ1))
      hφ.2.mul_left
  have h1 := integral_db_mul n z hz j (fun y => f y k) φ (hf k) hφ1 hφ.2
  have h2 := integral_db_mul n z hz k (fun y => f y j) φ (hf j) hφ1 hφ.2
  have hL : ∫ x, (f x k * db n z j φ x - f x j * db n z k φ x) ∂vol n z
      = ∫ x, f x k * db n z j φ x ∂vol n z - ∫ x, f x j * db n z k φ x ∂vol n z :=
    integral_sub (hI1 k j) (hI1 j k)
  have hR : ∫ x, sbar n z f x j k * φ x ∂vol n z
      = ∫ x, db n z j (fun y => f y k) x * φ x ∂vol n z
        - ∫ x, db n z k (fun y => f y j) x * φ x ∂vol n z := by
    rw [← integral_sub (hI2 k j) (hI2 j k)]
    congr 1
    funext x
    simp only [sbar, sub_mul]
  rw [hL, hR, h1, h2]
  ring

private lemma chart_symm_eventuallyEq_of_isChart {n : ℕ} {M : Type*} [TopologicalSpace M] (z : M → V n)
    (e e' : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (he' : IsChart n z e')
    (p : M) (hp : p ∈ e.source) (hp' : p ∈ e'.source) :
    e.symm =ᶠ[𝓝 (z p)] e'.symm := by
  have he0 : Set.EqOn z e e.source := he
  have he0' : Set.EqOn z e' e'.source := he'
  have hzp : z p = e' p := he0' hp'
  have h2 : e'.target ∩ e'.symm ⁻¹' e.source ∈ 𝓝 (z p) := by
    rw [hzp]
    refine (e'.isOpen_inter_preimage_symm e.open_source).mem_nhds ⟨e'.map_source hp', ?_⟩
    rw [Set.mem_preimage, e'.left_inv hp']
    exact hp
  filter_upwards [h2] with y hy
  have hs : e'.symm y ∈ e'.source := e'.map_target hy.1
  have h3 : e (e'.symm y) = y := by
    rw [← he0 hy.2, he0' hs, e'.right_inv hy.1]
  calc e.symm y = e.symm (e (e'.symm y)) := by rw [h3]
    _ = e'.symm y := e.left_inv hy.2

private lemma db_eq_wdb_comp_chart_symm {n : ℕ} {M : Type*} [TopologicalSpace M] (z : M → V n)
    (e0 : OpenPartialHomeomorph M (V n)) (he0 : IsChart n z e0) (k : Fin n) (g : M → ℂ)
    (p : M) (hp : p ∈ e0.source) : db n z k g p = wdb n k (g ∘ e0.symm) (z p) := by
  have hex : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ p ∈ e.source := ⟨e0, he0, hp⟩
  have hspec := Classical.choose_spec hex
  have hE : (g ∘ (Classical.choose hex).symm) =ᶠ[𝓝 (z p)] (g ∘ e0.symm) :=
    (chart_symm_eventuallyEq_of_isChart z _ e0 hspec.1 he0 p hspec.2 hp).fun_comp g
  rw [db, dite_eq_left hex]
  unfold wdb
  rw [hE.fderiv_eq]

private lemma fderiv_wdb_apply_eq {n : ℕ} (k : Fin n) (h : V n → ℂ) (y0 : V n)
    (hd : DifferentiableAt ℝ (fderiv ℝ h) y0) (v : V n) :
    fderiv ℝ (wdb n k h) y0 v =
      (fderiv ℝ (fderiv ℝ h) y0 v (bas n k) +
        Complex.I * fderiv ℝ (fderiv ℝ h) y0 v (Complex.I • bas n k)) / 2 := by
  have hA := hd.hasFDerivAt.clm_apply (hasFDerivAt_const (bas n k) y0)
  have hB := hd.hasFDerivAt.clm_apply (hasFDerivAt_const (Complex.I • bas n k) y0)
  have hW := HasFDerivAt.const_mul (HasFDerivAt.add hA (HasFDerivAt.const_mul hB Complex.I))
    ((2 : ℂ)⁻¹)
  have heq : wdb n k h = fun y =>
      (2 : ℂ)⁻¹ * (fderiv ℝ h y (bas n k) + Complex.I * fderiv ℝ h y (Complex.I • bas n k)) := by
    funext y
    rw [wdb, div_eq_inv_mul]
  have hF : fderiv ℝ (wdb n k h) y0 = (2 : ℂ)⁻¹ •
      ((fderiv ℝ h y0).comp (0 : V n →L[ℝ] V n) + (fderiv ℝ (fderiv ℝ h) y0).flip (bas n k) +
        Complex.I • ((fderiv ℝ h y0).comp (0 : V n →L[ℝ] V n) +
          (fderiv ℝ (fderiv ℝ h) y0).flip (Complex.I • bas n k))) := by
    rw [heq]
    exact HasFDerivAt.fderiv hW
  rw [hF]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply, map_zero, zero_add,
    ContinuousLinearMap.flip_apply, smul_eq_mul]
  ring

theorem sbarDbar (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : SbarDbarStatement n M := by
  intro z hz g hg x
  obtain ⟨e0, hx0, hze⟩ := hz x
  have he0 : IsChart n z e0 := by
    intro y _
    rw [hze]
  have he0' : Set.EqOn z e0 e0.source := he0
  have hy0 : z x ∈ e0.target := by
    rw [he0' hx0]
    exact e0.map_source hx0
  have hnb : e0.target ∈ 𝓝 (z x) := e0.open_target.mem_nhds hy0
  have hcd : ContDiffAt ℝ 2 (g ∘ e0.symm) (z x) := by
    have := (hg e0 he0).contDiffAt hnb
    simpa using this
  have hd : DifferentiableAt ℝ (fderiv ℝ (g ∘ e0.symm)) (z x) :=
    (hcd.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hsym : ∀ v w : V n, fderiv ℝ (fderiv ℝ (g ∘ e0.symm)) (z x) v w =
      fderiv ℝ (fderiv ℝ (g ∘ e0.symm)) (z x) w v := by
    intro v w
    first
      | exact hcd.isSymmSndFDerivAt (by simp) v w
      | exact hcd.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField]) v w
  have hloc : ∀ k : Fin n,
      ((fun y => db n z k g y) ∘ e0.symm) =ᶠ[𝓝 (z x)] wdb n k (g ∘ e0.symm) := by
    intro k
    filter_upwards [hnb] with y hy
    rw [Function.comp_apply, db_eq_wdb_comp_chart_symm z e0 he0 k g _ (e0.map_target hy),
      he0' (e0.map_target hy), e0.right_inv hy]
  funext j k
  show db n z j (fun y => db n z k g y) x - db n z k (fun y => db n z j g y) x = 0
  rw [db_eq_wdb_comp_chart_symm z e0 he0 j _ x hx0, db_eq_wdb_comp_chart_symm z e0 he0 k _ x hx0]
  unfold wdb
  rw [(hloc k).fderiv_eq, (hloc j).fderiv_eq,
    fderiv_wdb_apply_eq k _ _ hd (bas n j), fderiv_wdb_apply_eq k _ _ hd (Complex.I • bas n j),
    fderiv_wdb_apply_eq j _ _ hd (bas n k), fderiv_wdb_apply_eq j _ _ hd (Complex.I • bas n k),
    hsym (bas n k) (bas n j), hsym (bas n k) (Complex.I • bas n j),
    hsym (Complex.I • bas n k) (bas n j), hsym (Complex.I • bas n k) (Complex.I • bas n j)]
  ring

end

end ReciprocityTheory.L2DbarEstimates.F
end

section -- merged from ReciprocityTheory.L2DbarEstimates.Localization.TestIneq
namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff

noncomputable section

theorem ti_le_of_forall_pos (x c Y : ℝ≥0∞)
    (h : ∀ ε : ℝ, 0 < ε → x ≤ c * (ENNReal.ofReal (1 + ε) * Y)) : x ≤ c * Y := by
  have hc : Continuous fun ε : ℝ => ENNReal.ofReal (1 + ε) :=
    ENNReal.continuous_ofReal.comp (continuous_const.add continuous_id)
  have ht0 : Tendsto (fun ε : ℝ => ENNReal.ofReal (1 + ε)) (𝓝[>] 0) (𝓝 1) := by
    have h1 := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simpa using h1
  have ht : Tendsto (fun ε : ℝ => ENNReal.ofReal (1 + ε) * (c * Y)) (𝓝[>] 0) (𝓝 (c * Y)) := by
    have h1 := ENNReal.Tendsto.mul_const (b := c * Y) ht0 (Or.inl one_ne_zero)
    simpa using h1
  exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun ε hε => by
    calc x ≤ c * (ENNReal.ofReal (1 + ε) * Y) := h ε hε
      _ = ENNReal.ofReal (1 + ε) * (c * Y) := by ring)

theorem ti_hasCompactSupport {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (f : M → V n) (hf : IsTestForm n z f) : HasCompactSupport f := by
  have h : ∀ j, HasCompactSupport (fun x => f x j) := fun j => (hf j).2
  have hsub : Function.support f ⊆ ⋃ j, Function.support (fun x => f x j) := by
    intro x hx
    rw [Set.mem_iUnion]
    by_contra hne
    push_neg at hne
    apply hx
    ext j
    simpa [Function.mem_support] using hne j
  have hts : tsupport f ⊆ ⋃ j, tsupport (fun x => f x j) := by
    show closure (Function.support f) ⊆ ⋃ j, closure (Function.support fun x => f x j)
    rw [← closure_iUnion_of_finite]
    exact closure_mono hsub
  exact IsCompact.of_isClosed_subset (isCompact_iUnion fun j => h j) (isClosed_tsupport f) hts

private theorem db_eq_wdb_comp_symm_of_isChart {M : Type*} [TopologicalSpace M] {n : ℕ} {z : M → V n}
    (j : Fin n) (f : M → ℂ) (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) {x : M}
    (hx : x ∈ e.source) : db n z j f x = wdb n j (f ∘ e.symm) (z x) := by
  have hex : ∃ c : OpenPartialHomeomorph M (V n), IsChart n z c ∧ x ∈ c.source := ⟨e, he, hx⟩
  rw [db, dite_eq_left hex]
  obtain ⟨hc, hxc⟩ := Classical.choose_spec hex
  apply wdb_congr
  have hzx : z x = e x := he hx
  have hzc : z x = (Classical.choose hex) x := hc hxc
  have h1 : ∀ᶠ y in 𝓝 (z x), y ∈ e.target := by
    rw [hzx]
    exact e.open_target.mem_nhds (e.map_source hx)
  have h2 : ∀ᶠ y in 𝓝 (z x), y ∈ (Classical.choose hex).target := by
    rw [hzc]
    exact (Classical.choose hex).open_target.mem_nhds ((Classical.choose hex).map_source hxc)
  have h3 : ∀ᶠ y in 𝓝 (z x), e.symm y ∈ (Classical.choose hex).source := by
    have hca : ContinuousAt e.symm (z x) := by
      rw [hzx]
      exact e.continuousAt_symm (e.map_source hx)
    apply hca.preimage_mem_nhds
    rw [hzx, e.left_inv hx]
    exact (Classical.choose hex).open_source.mem_nhds hxc
  filter_upwards [h1, h2, h3] with y hy1 hy2 hy3
  show f ((Classical.choose hex).symm y) = f (e.symm y)
  congr 1
  apply (Classical.choose hex).injOn ((Classical.choose hex).map_target hy2) hy3
  rw [(Classical.choose hex).right_inv hy2, ← hc hy3, he (e.map_target hy1), e.right_inv hy1]

private theorem ck_one_db_of_smooth {M : Type*} [TopologicalSpace M] {n : ℕ} {z : M → V n} {F : M → ℂ}
    (hF : Smooth n z F) (j : Fin n) : Ck n z 1 (fun x => db n z j F x) := by
  intro e he
  have hG : ContDiffOn ℝ 2 (F ∘ e.symm) e.target := (hF e he).of_le (by first
      | exact_mod_cast (le_top : ((2 : ℕ) : ℕ∞) ≤ ⊤)
      | exact WithTop.coe_le_coe.mpr le_top
      | simp)
  have hD : ContDiffOn ℝ 1 (fun y => fderiv ℝ (F ∘ e.symm) y) e.target :=
    hG.fderiv_of_isOpen e.open_target (by norm_num)
  have hW : ContDiffOn ℝ 1 (fun y => wdb n j (F ∘ e.symm) y) e.target := by
    unfold wdb
    exact ((hD.clm_apply contDiffOn_const).add
      (contDiffOn_const.mul (hD.clm_apply contDiffOn_const))).div_const _
  refine hW.congr fun y hy => ?_
  show db n z j F (e.symm y) = wdb n j (F ∘ e.symm) y
  rw [db_eq_wdb_comp_symm_of_isChart j F e he (e.map_target hy), he (e.map_target hy), e.right_inv hy]

private theorem smoothR_sub_const_mul {M : Type*} [TopologicalSpace M] {n : ℕ} {z : M → V n}
    {a b : M → ℝ} (ha : SmoothR n z a) (hb : SmoothR n z b) (c : ℝ) :
    SmoothR n z (fun x => a x - c * b x) := by
  intro e he
  refine ((ha e he).sub ((contDiffOn_const (c := ((c : ℝ) : ℂ))).mul (hb e he))).congr
    fun y _ => ?_
  simp [Function.comp]

theorem testIneq (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (hCh : ChoiceStatement n M) (hP : PrimedIneqStatement n M)
    (hC : ClosureIneqStatement n M) (hS : SplitTestStatement n M) (hL : LocalityStatement n M)
    (hWS : WeakSSmoothStatement n M) (hSD : SbarDbarStatement n M) : TestIneqStatement n M := by
  intro X ph F0 h hph hlev hF0 hh hdom hI f hf
  have hz := X.isLocalHomeomorph
  apply ti_le_of_forall_pos
  intro ε hε
  have hck2 : Ck n X.z 2 F0 := fun e he => (hF0 e he).of_le (by first
      | exact_mod_cast (le_top : ((2 : ℕ) : ℕ∞) ≤ ⊤)
      | exact WithTop.coe_le_coe.mpr le_top
      | simp)
  have hcj : ∀ j, Continuous fun x => db n X.z j F0 x := by
    intro j
    rw [continuous_iff_continuousAt]
    intro x
    obtain ⟨e, hxe, hze⟩ := hz x
    have he : IsChart n X.z e := fun y _ => by rw [hze]
    have hC := (ck_one_db_of_smooth hF0 j e he).continuousOn
    have h1 : ContinuousOn (((fun x => db n X.z j F0 x) ∘ e.symm) ∘ e) e.source :=
      hC.comp e.continuousOn (fun y hy => e.map_source hy)
    have h2 : ContinuousOn (fun x => db n X.z j F0 x) e.source :=
      h1.congr fun y hy => by simp [e.left_inv hy]
    exact h2.continuousAt (e.open_source.mem_nhds hxe)
  have hcont : Continuous (dbarF n X.z F0) := by
    show Continuous fun x => WithLp.toLp 2 (fun j => db n X.z j F0 x)
    first
      | exact (PiLp.continuous_toLp 2 (fun _ : Fin n => ℂ)).comp (continuous_pi hcj)
      | exact (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin n => ℂ)).comp (continuous_pi hcj)
      | fun_prop
  obtain ⟨ph', ψ, e', U, hph', hψ, he', hcut, hU, hCU, hUeq, hle, hlevi, hL2⟩ :=
    hCh X ph (dbarF n X.z F0) (tsupport f) ε hph hcont (ti_hasCompactSupport n X.z f hf) hε
  have hprim := hP X.z hz ph ph' ψ F0 h ε hph hlev hph' hψ hF0 hh hdom hε hle hlevi hI
  have hclos := hC X.z hz e' ph' ψ (dbarF n X.z F0) _ ε he' hph' hψ hcut hL2 hI hε hprim
  have hw1 : SmoothR n X.z (w1 ph' ψ) := smoothR_sub_const_mul hph' hψ 2
  have hw2 : SmoothR n X.z (w2 ph' ψ) := by
    have h1 := smoothR_sub_const_mul hph' hψ 1
    simp only [one_mul] at h1
    exact h1
  have hWS0 : IsWeakS n X.z (dbarF n X.z F0) 0 := by
    have h1 := hWS X.z hz (dbarF n X.z F0) (fun j => ck_one_db_of_smooth hF0 j)
    have h0 : sbar n X.z (dbarF n X.z F0) = 0 := by
      funext x
      exact hSD X.z hz F0 hck2 x
    rwa [h0] at h1
  obtain ⟨hT, f₁, hf₁, hS1, hadj, hip⟩ :=
    hS X.z hz (w1 ph' ψ) (w2 ph' ψ) (dbarF n X.z F0) f hw1 hw2 hL2 hWS0 hf
  obtain ⟨hloc1, hloc2⟩ := hL X.z hz ph ph' ψ U f hU hf hCU hUeq
  have hfin := hclos f₁ (tstar n X.z (w1 ph' ψ) (w2 ph' ψ) f) hf₁ hT hadj hS1
  rw [← hip, hloc1, hloc2] at hfin
  exact hfin

end

end ReciprocityTheory.L2DbarEstimates.F
end
