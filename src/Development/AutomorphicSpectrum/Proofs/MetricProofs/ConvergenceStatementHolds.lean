module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagDimensionIndexEquiv
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.TailBoundStatementHolds

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.CompactPartIntegralsTendsto
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

noncomputable section

open scoped ENNReal

theorem cpt_chart_piece {e : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    {T O C : Set (Fin e → ℂ)} (hT : IsOpen T) {s : (Fin e → ℂ) → X} (hs : ContinuousOn s T)
    {w : (Fin e → ℂ) → ℝ} (hO : MeasurableSet O) (hCm : MeasurableSet C) (hCT : C ⊆ T)
    (hw : ContinuousOn w C) (hw0 : ∀ y ∈ T ∩ O, w y ≤ 0)
    {G : X → ℝ} (hG : Measurable G) (hGz : ∀ y ∈ T, y ∉ O → y ∉ C → G (s y) = 0) :
    (Integrable G (((volume.restrict T).withDensity fun y => ENNReal.ofReal (w y)).map s) ↔
      IntegrableOn (fun y => G (s y) * max (w y) 0) C) ∧
    ∫ x, G x ∂(((volume.restrict T).withDensity fun y => ENNReal.ofReal (w y)).map s) =
      ∫ y in C, G (s y) * max (w y) 0 := by
  have hTm : MeasurableSet T := hT.measurableSet
  have hsm : AEMeasurable s ((volume.restrict T).withDensity fun y => ENNReal.ofReal (w y)) :=
    (hs.aemeasurable hTm).mono_ac (withDensity_absolutelyContinuous _ _)
  have hGm := hG.aestronglyMeasurable
    (μ := ((volume.restrict T).withDensity fun y => ENNReal.ofReal (w y)).map s)
  have h1 : ((volume.restrict T).withDensity fun y => ENNReal.ofReal (w y)) (T ∩ O) = 0 := by
    rw [withDensity_apply _ (hTm.inter hO)]
    refine (setLIntegral_congr_fun (g := fun _ => 0) (hTm.inter hO) ?_).trans (by simp)
    intro y hy
    exact ENNReal.ofReal_of_nonpos (hw0 y hy)
  have h2 : ((volume.restrict T).withDensity fun y => ENNReal.ofReal (w y)) Tᶜ = 0 :=
    withDensity_absolutelyContinuous _ _ (by
      rw [Measure.restrict_apply hTm.compl]; simp)
  have hae : (G ∘ s) =ᵐ[(volume.restrict T).withDensity fun y => ENNReal.ofReal (w y)]
      C.indicator (G ∘ s) := by
    have h3 := measure_union_null h1 h2
    refine measure_mono_null (fun y hy => ?_) h3
    by_contra hcon
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff, not_or, not_and,
      not_not] at hcon
    have hyT : y ∈ T := hcon.2
    have hyO : y ∉ O := hcon.1 hyT
    apply hy
    by_cases hyC : y ∈ C
    · simp [Set.indicator_of_mem hyC]
    · simp [Set.indicator_of_notMem hyC, hGz y hyT hyO hyC]
  have hrest : ((volume.restrict T).withDensity fun y => ENNReal.ofReal (w y)).restrict C =
      (volume.restrict C).withDensity fun y => ENNReal.ofReal (w y) := by
    rw [restrict_withDensity hCm, Measure.restrict_restrict hCm, Set.inter_eq_left.2 hCT]
  have hwm : AEMeasurable (fun y => (w y).toNNReal) (volume.restrict C) :=
    (hw.aemeasurable hCm).real_toNNReal
  have hofR : (fun y => ENNReal.ofReal (w y)) = fun y => ((w y).toNNReal : ℝ≥0∞) := rfl
  have hsm2 : (fun y => (w y).toNNReal • (G ∘ s) y) = fun y => G (s y) * max (w y) 0 := by
    funext y
    simp [NNReal.smul_def, Real.coe_toNNReal', mul_comm]
  constructor
  · rw [integrable_map_measure hGm hsm, integrable_congr hae, integrable_indicator_iff hCm,
      IntegrableOn, hrest, hofR, integrable_withDensity_iff_integrable_smul₀ hwm, hsm2]
    rfl
  · rw [integral_map hsm hGm]
    refine Eq.trans (integral_congr_ae hae) ?_
    rw [integral_indicator hCm, hrest, hofR, integral_withDensity_eq_integral_smul₀ hwm, hsm2]

variable {e : ℕ} {X : Type} [TopologicalSpace X]

def cptSet (A : FinHolAtlas e X) (P : ChartPartition A) (K : Set X) (j : Fin A.n) :
    Set (Fin e → ℂ) :=
  A.chart j '' (K ∩ tsupport (P.χ j))

def cptW (A : FinHolAtlas e X) (P : ChartPartition A) (Φ : Fin e → LocPot X) (j : Fin A.n)
    (y : Fin e → ℂ) : ℝ :=
  P.χ j ((A.chart j).symm y) * locDens A Φ j y

theorem cptSet_symm_mem (A : FinHolAtlas e X) (P : ChartPartition A) (K : Set X) (j : Fin A.n)
    {y : Fin e → ℂ} (hy : y ∈ cptSet A P K j) : (A.chart j).symm y ∈ K := by
  obtain ⟨x, ⟨hxK, hxs⟩, rfl⟩ := hy
  rw [(A.chart j).left_inv (P.tsupport_subset j hxs)]
  exact hxK

theorem cptSet_subset_target (A : FinHolAtlas e X) (P : ChartPartition A) (K : Set X) (j : Fin A.n) :
    cptSet A P K j ⊆ (A.chart j).target := by
  rintro y ⟨x, ⟨-, hxs⟩, rfl⟩
  exact (A.chart j).map_source (P.tsupport_subset j hxs)

theorem cptSet_compact [CompactSpace X] (A : FinHolAtlas e X) (P : ChartPartition A) {K : Set X}
    (hK : IsClosed K) (j : Fin A.n) : IsCompact (cptSet A P K j) := by
  exact (hK.isCompact.inter_right (isClosed_tsupport _)).image_of_continuousOn
    ((A.chart j).continuousOn.mono fun x hx => P.tsupport_subset j hx.2)

theorem cptSet_subset (A : FinHolAtlas e X) (P : ChartPartition A) {K U : Set X} (hKU : K ⊆ U)
    (j : Fin A.n) : cptSet A P K j ⊆ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U := by
  intro y hy
  exact ⟨cptSet_subset_target A P K j hy, hKU (cptSet_symm_mem A P K j hy)⟩

theorem cptW_continuousOn (A : FinHolAtlas e X) (P : ChartPartition A) (Φ : Fin e → LocPot X)
    {K U : Set X} (hKU : K ⊆ U) (j : Fin A.n)
    (hc : ContinuousOn (locDens A Φ j) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U)) :
    ContinuousOn (cptW A P Φ j) (cptSet A P K j) := by
  have hχ : ContinuousOn (fun y => P.χ j ((A.chart j).symm y)) (cptSet A P K j) :=
    ((P.smooth j) j).continuousOn.mono fun y hy => ⟨cptSet_subset_target A P K j hy, Set.mem_univ _⟩
  exact hχ.mul (hc.mono (cptSet_subset A P hKU j))

variable [MeasurableSpace X] [BorelSpace X]

theorem cpt_chartMeasure [CompactSpace X] (A : FinHolAtlas e X) (P : ChartPartition A)
    (Φ : Fin e → LocPot X) {K U : Set X} (hK : IsClosed K) (hKU : K ⊆ U) (j : Fin A.n)
    (hc : ContinuousOn (locDens A Φ j) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U))
    {G : X → ℝ} (hG : Measurable G) (hGK : ∀ x, x ∉ K → G x = 0) :
    (Integrable G (chartMeasure A P Φ j) ↔
      IntegrableOn (fun y => G ((A.chart j).symm y) * max (cptW A P Φ j y) 0) (cptSet A P K j)) ∧
    ∫ x, G x ∂chartMeasure A P Φ j =
      ∫ y in cptSet A P K j, G ((A.chart j).symm y) * max (cptW A P Φ j y) 0 := by
  have key := cpt_chart_piece (w := cptW A P Φ j) (s := (A.chart j).symm) (G := G)
    (T := (A.chart j).target) (C := cptSet A P K j)
    (O := (A.chart j).target ∩ (A.chart j).symm ⁻¹' (tsupport (P.χ j))ᶜ)
    (A.chart j).open_target (A.chart j).continuousOn_symm
    ((A.chart j).isOpen_inter_preimage_symm (isClosed_tsupport _).isOpen_compl).measurableSet
    (cptSet_compact A P hK j).measurableSet (cptSet_subset_target A P K j)
    (cptW_continuousOn A P Φ hKU j hc)
    (by
      rintro y ⟨-, -, hy⟩
      have h0 : P.χ j ((A.chart j).symm y) = 0 := image_eq_zero_of_notMem_tsupport hy
      simp [cptW, h0])
    hG
    (by
      intro y hy hyO hyC
      by_contra hne
      have hxK : (A.chart j).symm y ∈ K := by
        by_contra h
        exact hne (hGK _ h)
      have hxs : (A.chart j).symm y ∈ tsupport (P.χ j) := by
        by_contra h
        exact hyO ⟨hy, h⟩
      exact hyC ⟨_, ⟨hxK, hxs⟩, (A.chart j).right_inv hy⟩)
  exact key

theorem cpt_aesm [CompactSpace X] (A : FinHolAtlas e X) (P : ChartPartition A)
    (Φ : Fin e → LocPot X) {K U : Set X} (hK : IsClosed K) (hKU : K ⊆ U) (j : Fin A.n)
    (hc : ContinuousOn (locDens A Φ j) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U))
    {G : X → ℝ} (hG : Measurable G) :
    AEStronglyMeasurable (fun y => G ((A.chart j).symm y) * max (cptW A P Φ j y) 0)
      (volume.restrict (cptSet A P K j)) := by
  have hCm : MeasurableSet (cptSet A P K j) := (cptSet_compact A P hK j).isClosed.measurableSet
  have hs : ContinuousOn (A.chart j).symm (cptSet A P K j) :=
    (A.chart j).continuousOn_symm.mono (cptSet_subset_target A P K j)
  have h1 : AEMeasurable (fun y => G ((A.chart j).symm y)) (volume.restrict (cptSet A P K j)) :=
    hG.comp_aemeasurable (hs.aemeasurable hCm)
  have h2 : AEMeasurable (fun y => max (cptW A P Φ j y) 0) (volume.restrict (cptSet A P K j)) :=
    ((cptW_continuousOn A P Φ hKU j hc).aemeasurable hCm).max aemeasurable_const
  exact (h1.mul h2).aestronglyMeasurable

theorem cpt_abs_max {c a B : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1) (h : |a| ≤ B) :
    |max (c * a) 0| ≤ B := by
  have hB : 0 ≤ B := le_trans (abs_nonneg a) h
  rw [abs_of_nonneg (le_max_right _ _)]
  refine max_le ?_ hB
  calc c * a ≤ |c * a| := le_abs_self _
    _ = c * |a| := by rw [abs_mul, abs_of_nonneg hc]
    _ ≤ 1 * |a| := mul_le_mul_of_nonneg_right hc1 (abs_nonneg a)
    _ ≤ B := by rw [one_mul]; exact h

theorem cpt_integrableOn [CompactSpace X] (A : FinHolAtlas e X) (P : ChartPartition A)
    (Φ : Fin e → LocPot X) {K U : Set X} (hK : IsClosed K) (hKU : K ⊆ U) (j : Fin A.n)
    (hc : ContinuousOn (locDens A Φ j) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U))
    {G : X → ℝ} (hG : Measurable G) {B : ℝ} (hB : ∀ x ∈ K, |G x| ≤ B) :
    IntegrableOn (fun y => G ((A.chart j).symm y) * max (cptW A P Φ j y) 0) (cptSet A P K j) := by
  have hCc := cptSet_compact A P hK j
  obtain ⟨L, hL⟩ := hCc.exists_bound_of_continuousOn
    (hc.mono (cptSet_subset A P hKU j))
  haveI : IsFiniteMeasure (volume.restrict (cptSet A P K j)) :=
    ⟨by simpa using hCc.measure_lt_top⟩
  refine Integrable.of_bound (cpt_aesm A P Φ hK hKU j hc hG) (B * L)
    (ae_restrict_of_forall_mem hCc.measurableSet fun y hy => ?_)
  have hx := cptSet_symm_mem A P K j hy
  have a2 : |max (cptW A P Φ j y) 0| ≤ L :=
    cpt_abs_max (P.nonneg j _) (chi_le_one P j _) (by simpa [Real.norm_eq_abs] using hL y hy)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (hB _ hx) a2 (abs_nonneg _) ((abs_nonneg _).trans (hB _ hx))

theorem cpt_maMeasure [CompactSpace X] (A : FinHolAtlas e X) (hne : Nonempty (ChartPartition A))
    (Φ : Fin e → LocPot X) {K U : Set X} (hK : IsClosed K) (hKU : K ⊆ U)
    (hc : ∀ j, ContinuousOn (locDens A Φ j) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U))
    {G : X → ℝ} (hG : Measurable G) (hGK : ∀ x, x ∉ K → G x = 0) {B : ℝ}
    (hB : ∀ x ∈ K, |G x| ≤ B) :
    Integrable G (maMeasure A Φ) ∧ ∫ x, G x ∂maMeasure A Φ =
      ∑ j, ∫ y in cptSet A hne.some K j,
        G ((A.chart j).symm y) * max (cptW A hne.some Φ j y) 0 := by
  have hint : ∀ j, Integrable G (chartMeasure A hne.some Φ j) := fun j =>
    (cpt_chartMeasure A hne.some Φ hK hKU j (hc j) hG hGK).1.2
      (cpt_integrableOn A hne.some Φ hK hKU j (hc j) hG hB)
  have hmeasure : maMeasure A Φ = ∑ j, chartMeasure A hne.some Φ j := by
    unfold maMeasure
    rw [dite_eq_left hne]
    rfl
  rw [hmeasure]
  refine ⟨integrable_finsetSum_measure.2 fun j _ => hint j, ?_⟩
  rw [integral_finsetSum_measure fun j _ => hint j]
  exact Finset.sum_congr rfl fun j _ => (cpt_chartMeasure A hne.some Φ hK hKU j (hc j) hG hGK).2

theorem cpt_meas {U S : Set X} (hU : IsOpen U) (hS : MeasurableSet S) (hSU : S ⊆ U) {f : X → ℝ}
    (hf : ContinuousOn f U) : Measurable (S.indicator f) := by
  classical
  have h1 : Measurable (U.piecewise f 0) :=
    hf.measurable_piecewise (continuousOn_const (c := (0 : ℝ))) hU.measurableSet
  have h2 : S.indicator f = S.indicator (U.piecewise f 0) := by
    funext x
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Set.piecewise_eq_of_mem _ _ _ (hSU hx)]
    · simp only [Set.indicator_apply, hx, if_false]
  rw [h2]
  exact h1.indicator hS

theorem cpt_ind [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
    (hne : Nonempty (ChartPartition A)) (Φ : Fin e → LocPot X) {K U S : Set X} (hU : IsOpen U)
    (hK : IsCompact K) (hKU : K ⊆ U)
    (hc : ∀ j, ContinuousOn (locDens A Φ j) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U))
    (hS : MeasurableSet S) (hSK : S ⊆ K) {f : X → ℝ} (hf : ContinuousOn f U) :
    Integrable (S.indicator f) (maMeasure A Φ) ∧ ∫ x in S, f x ∂maMeasure A Φ =
      ∑ j, ∫ y in cptSet A hne.some K j,
        S.indicator f ((A.chart j).symm y) * max (cptW A hne.some Φ j y) 0 := by
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hf.mono hKU)
  have hb : ∀ x ∈ K, |S.indicator f x| ≤ M := fun x hx => by
    by_cases hxS : x ∈ S
    · simpa [Set.indicator_of_mem hxS, Real.norm_eq_abs] using hM x hx
    · rw [Set.indicator_of_notMem hxS, abs_zero]
      exact (norm_nonneg _).trans (hM x hx)
  have key := cpt_maMeasure A hne Φ hK.isClosed hKU hc (cpt_meas hU hS (hSK.trans hKU) hf)
    (fun x hx => Set.indicator_of_notMem (fun h => hx (hSK h)) _) hb
  refine ⟨key.1, ?_⟩
  rw [← integral_indicator hS]
  exact key.2

theorem cpt_chart_tendsto [CompactSpace X] (A : FinHolAtlas e X) (P : ChartPartition A)
    (Φ : Fin e → LocPot X) (ΦT : ℝ → Fin e → LocPot X) {K U E : Set X} (hU : IsOpen U)
    (hK : IsCompact K) (hKc : IsClosed K) (hKU : K ⊆ U) (j : Fin A.n)
    (hc : ContinuousOn (locDens A Φ j) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U))
    (hpot : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i, IsPotential A (ΦT t i))
    (hld : TendstoUniformlyOn (fun t => locDens A (ΦT t) j) (locDens A Φ j) (𝓝[>] 0)
      (cptSet A P K j))
    {g : X → ℝ} {gT : ℝ → X → ℝ} (hgT : ∀ t, ContinuousOn (gT t) U) (hgc : ContinuousOn g U)
    (hgU : TendstoUniformlyOn gT g (𝓝[>] 0) K) (hE : MeasurableSet E) (hEK : E ⊆ K) :
    Tendsto (fun t => ∫ y in cptSet A P K j,
        E.indicator (gT t) ((A.chart j).symm y) * max (cptW A P (ΦT t) j y) 0) (𝓝[>] 0)
      (𝓝 (∫ y in cptSet A P K j,
        E.indicator g ((A.chart j).symm y) * max (cptW A P Φ j y) 0)) := by
  have hCc := cptSet_compact A P hKc j
  have hCm := hCc.measurableSet
  have hCV := cptSet_subset A P hKU j
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hgc.mono hKU)
  obtain ⟨L, hL⟩ := hCc.exists_bound_of_continuousOn (hc.mono hCV)
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => (M + 1) * (L + 1)) ?_ ?_ ?_ ?_
  · filter_upwards [hpot] with t ht
    exact cpt_aesm A P (ΦT t) hKc hKU j
      ((locDensCont A _ ht j).mono Set.inter_subset_left)
      (cpt_meas hU hE (hEK.trans hKU) (hgT t))
  · have h1 := Metric.tendstoUniformlyOn_iff.1 hgU 1 one_pos
    have h2 := Metric.tendstoUniformlyOn_iff.1 hld 1 one_pos
    filter_upwards [h1, h2] with t ht1 ht2
    refine ae_restrict_of_forall_mem hCm fun y hy => ?_
    have hx := cptSet_symm_mem A P K j hy
    have hMx := hM _ hx
    have hLy := hL y hy
    rw [Real.norm_eq_abs] at hMx hLy
    have hd1 := ht1 _ hx
    have hd2 := ht2 y hy
    rw [Real.dist_eq, abs_lt] at hd1 hd2
    have a1 : |E.indicator (gT t) ((A.chart j).symm y)| ≤ M + 1 := by
      by_cases hxE : (A.chart j).symm y ∈ E
      · rw [Set.indicator_of_mem hxE]
        rw [abs_le] at hMx ⊢
        constructor <;> linarith [hd1.1, hd1.2, hMx.1, hMx.2]
      · rw [Set.indicator_of_notMem hxE, abs_zero]
        linarith [abs_nonneg (g ((A.chart j).symm y))]
    have a2 : |max (cptW A P (ΦT t) j y) 0| ≤ L + 1 := by
      refine cpt_abs_max (P.nonneg j _) (chi_le_one P j _) ?_
      rw [abs_le] at hLy ⊢
      constructor <;> linarith [hd2.1, hd2.2, hLy.1, hLy.2]
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul a1 a2 (abs_nonneg _) ((abs_nonneg _).trans a1)
  · exact integrableOn_const hCc.measure_lt_top.ne
  · refine ae_restrict_of_forall_mem hCm fun y hy => ?_
    have hx := cptSet_symm_mem A P K j hy
    have l1 : Tendsto (fun t => E.indicator (gT t) ((A.chart j).symm y)) (𝓝[>] 0)
        (𝓝 (E.indicator g ((A.chart j).symm y))) := by
      by_cases hxE : (A.chart j).symm y ∈ E
      · simp only [Set.indicator_of_mem hxE]
        exact hgU.tendsto_at hx
      · simp only [Set.indicator_of_notMem hxE]
        exact tendsto_const_nhds
    have l2 : Tendsto (fun t => locDens A (ΦT t) j y) (𝓝[>] 0) (𝓝 (locDens A Φ j y)) :=
      hld.tendsto_at hy
    exact l1.mul (((l2.const_mul _)).max tendsto_const_nhds)

theorem compact_part_integrals_tendsto :
    ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
      [BorelSpace X] (A : FinHolAtlas e X) (U : Set X) (Φ : Fin e → LocPot X)
      (ΦT : ℝ → Fin e → LocPot X), IsOpen U →
      (∀ j, ContinuousOn (locDens A Φ j) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U)) →
      (∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i, IsPotential A (ΦT t i)) →
      (∀ j, ∀ K ⊆ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U, IsCompact K →
        TendstoUniformlyOn (fun t => locDens A (ΦT t) j) (locDens A Φ j) (𝓝[>] 0) K) →
      ∀ (g : X → ℝ) (gT : ℝ → X → ℝ), (∀ t, ContinuousOn (gT t) U) →
        TendstoLocallyUniformlyOn gT g (𝓝[>] 0) U →
        ∀ K E : Set X, IsCompact K → K ⊆ U → MeasurableSet E → E ⊆ K →
          maMeasure A Φ K < ⊤ ∧ IntegrableOn g K (maMeasure A Φ) ∧
            Tendsto (fun t => ∫ y in E, gT t y ∂maMeasure A (ΦT t)) (𝓝[>] 0)
              (𝓝 (∫ y in E, g y ∂maMeasure A Φ)) := by
  intro e X _ _ _ _ _ A U Φ ΦT hU hc hpot hunif g gT hgT hlim K E hK hKU hE hEK
  have hne : Nonempty (ChartPartition A) := existsPartition A
  have hKc : IsClosed K := hK.isClosed
  have hKm : MeasurableSet K := hKc.measurableSet
  have hgc : ContinuousOn g U := hlim.continuousOn (Eventually.of_forall hgT).frequently
  have hgU : TendstoUniformlyOn gT g (𝓝[>] 0) K :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).1 (hlim.mono hKU)
  have c1 := cpt_ind A hne Φ hU hK hKU hc hKm subset_rfl (f := fun _ => (1 : ℝ)) continuousOn_const
  have c2 := cpt_ind A hne Φ hU hK hKU hc hKm subset_rfl hgc
  have c3 := cpt_ind A hne Φ hU hK hKU hc hE hEK hgc
  refine ⟨?_, (integrable_indicator_iff hKm).1 c2.1, ?_⟩
  · have h := (integrable_indicator_iff hKm).1 c1.1
    exact ((integrableOn_const_iff (by simp)).1 h).resolve_left (by simp)
  · rw [c3.2]
    refine Tendsto.congr' ?_ (tendsto_finsetSum _ fun j _ =>
      cpt_chart_tendsto A hne.some Φ ΦT hU hK hKc hKU j (hc j) hpot
        (hunif j _ (cptSet_subset A hne.some hKU j) (cptSet_compact A hne.some hKc j))
        hgT hgc hgU hE hEK)
    filter_upwards [hpot] with t ht
    exact (cpt_ind A hne (ΦT t) hU hK hKU
      (fun j => (locDensCont A _ ht j).mono Set.inter_subset_left) hE hEK (hgT t)).2.symm

end

end GlobalTheory.CompanionTheory.Ar.Giv
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedEnergyRegularizationBound
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedEnergyRegularizationBound
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem maMeasure_bdry_eq_zero {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ) {n : ℕ}
    (m : Fin n → ℕ) (W : Fin n → Set X) (hS : IsSection A L s) (hSNC : IsSNC A L s m W)
    (Φ : Fin e → LocPot X) : maMeasure A Φ (bdry s) = 0 := by
  have hB := LeviFormBoundaryTopology.isClosed_bdry hS
  have hAn : A.IsAnalyticSubset (bdry s) := by
    intro x
    refine ⟨L.U x, L.isOpen_U x, L.mem_U x, 1, fun _ => s x, fun _ => hS.1 x, ?_⟩
    ext z
    constructor
    · rintro ⟨hz, hzU⟩
      exact ⟨hzU, fun _ => (LeviFormBoundaryTopology.bdry_iff hS hzU).1 hz⟩
    · rintro ⟨hzU, hz⟩
      exact ⟨(LeviFormBoundaryTopology.bdry_iff hS hzU).2 (hz 0), hzU⟩
  have hInt : interior (bdry s) = ∅ := LeviFormBoundaryTopology.interior_bdry_eq_empty hS hSNC
  unfold maMeasure
  split_ifs with h
  · simp only [Measure.coe_finsetSum, Finset.sum_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    have hT := (A.chart j).open_target.measurableSet
    rw [Measure.map_apply_of_aemeasurable (((A.chart j).continuousOn_symm.aemeasurable hT).mono_ac
      (withDensity_absolutelyContinuous _ _)) hB.measurableSet]
    refine withDensity_absolutelyContinuous _ _ ?_
    rw [Measure.restrict_apply' hT]
    have := analyticNull A (bdry s) hAn hInt j
    rw [Set.inter_comm, (A.chart j).image_source_inter_eq'] at this
    rwa [Set.inter_comm]
  · simp

theorem tail_lintegral_le_of_eventually {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [MeasurableSpace X] [BorelSpace X] (A : FinHolAtlas e X) (L : LocPot X)
    (s : X → X → ℂ) (hL : IsPotential A L) (hS : IsSection A L s) (Φ : Fin e → LocPot X)
    (ΦT : ℝ → Fin e → LocPot X)
    (hc : ∀ j, ContinuousOn (locDens A Φ j) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (bdry s)ᶜ))
    (hpot : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i, IsPotential A (ΦT t i))
    (hunif : ∀ j, ∀ K ⊆ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (bdry s)ᶜ, IsCompact K →
      TendstoUniformlyOn (fun t => locDens A (ΦT t) j) (locDens A Φ j) (𝓝[>] 0) K)
    (g : X → ℝ) (hgm : Measurable g) (hgc : ContinuousOn g (bdry s)ᶜ)
    (R B : ℝ)
    (hg1 : ∀ y ∉ bdry s, R ≤ rW L s y → 0 ≤ g y)
    (hB : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∫⁻ y in (bdry s)ᶜ ∩ {y | R ≤ rW L s y}, ENNReal.ofReal (g y)
      ∂maMeasure A (ΦT t) ≤ ENNReal.ofReal B) :
    ∫⁻ y in (bdry s)ᶜ ∩ {y | R ≤ rW L s y}, ENNReal.ofReal (g y) ∂maMeasure A Φ ≤
      ENNReal.ofReal B := by
  have hU : IsOpen (bdry s)ᶜ := (LeviFormBoundaryTopology.isClosed_bdry hS).isOpen_compl
  obtain ⟨hbm, hrm⟩ := TailBoundAlt.bdry_rW_meas A L s hL hS
  let Es : ℕ → Set X := fun N => ((bdry s)ᶜ ∩ {y | R ≤ rW L s y}) ∩ {y | rW L s y ≤ (N : ℝ)}
  have hun : (bdry s)ᶜ ∩ {y | R ≤ rW L s y} = ⋃ N, Es N := by
    ext y
    constructor
    · intro h
      obtain ⟨N, hN⟩ := exists_nat_ge (rW L s y)
      exact Set.mem_iUnion.2 ⟨N, h, hN⟩
    · intro h
      obtain ⟨N, hN⟩ := Set.mem_iUnion.1 h
      exact hN.1
  have hmono : Monotone Es := fun a b hab y hy =>
    ⟨hy.1, show rW L s y ≤ (b : ℝ) from
      le_trans (show rW L s y ≤ (a : ℝ) from hy.2) (Nat.cast_le.2 hab)⟩
  rw [hun, setLIntegral_iUnion_of_directed _ hmono.directed_le]
  refine iSup_le fun N => ?_
  have hEm : MeasurableSet (Es N) :=
    (hbm.compl.inter (measurableSet_le measurable_const hrm)).inter
      (measurableSet_le hrm measurable_const)
  have hKU : {y | y ∉ bdry s ∧ rW L s y ≤ (N : ℝ)} ⊆ (bdry s)ᶜ := fun y hy => hy.1
  have hEK : Es N ⊆ {y | y ∉ bdry s ∧ rW L s y ≤ (N : ℝ)} := fun y hy => ⟨hy.1.1, hy.2⟩
  obtain ⟨-, hint, hlim⟩ := compact_part_integrals_tendsto A (bdry s)ᶜ Φ ΦT hU hc hpot hunif g
    (fun _ => g) (fun _ => hgc)
    (fun u hu x _ => ⟨Set.univ, Filter.univ_mem,
      Eventually.of_forall fun t y _ => refl_mem_uniformity hu⟩)
    _ (Es N) (isCompact_rW_sublevel A L s hL hS (N : ℝ)) hKU hEm hEK
  have hnn : ∀ μ : Measure X, 0 ≤ᵐ[μ.restrict (Es N)] g := fun μ =>
    (ae_restrict_iff' hEm).2 (Eventually.of_forall fun y hy => hg1 y hy.1.1 hy.1.2)
  have hle : ∫ y in Es N, g y ∂maMeasure A Φ ≤ max B 0 := by
    refine le_of_tendsto hlim ?_
    filter_upwards [hB] with t ht
    rw [integral_eq_lintegral_of_nonneg_ae (hnn _) hgm.aestronglyMeasurable,
      ← ENNReal.toReal_ofReal']
    exact ENNReal.toReal_mono ENNReal.ofReal_ne_top
      ((lintegral_mono_set (show Es N ⊆ (bdry s)ᶜ ∩ {y | R ≤ rW L s y} from
        fun _ hy => hy.1)).trans ht)
  rw [← ofReal_integral_eq_lintegral_ofReal (hint.mono_set hEK) (hnn _)]
  refine (ENNReal.ofReal_le_ofReal hle).trans (le_of_eq ?_)
  rcases le_total B 0 with h | h
  · rw [max_eq_right h, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h]
  · rw [max_eq_left h]

theorem limit_measure_tail : TailBoundStatement → ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (A : FinHolAtlas e X) (Θ L : LocPot X) (s : X → X → ℂ) {n : ℕ} (m : Fin n → ℕ) (W : Fin n → Set X), IsPotential A Θ → IsPosPot A Θ → IsPotential A L → IsSection A L s → IsSNC A L s m W → (∀ y, logNormSec L s y ≤ 0) → ∀ (th : Fin e → LocPot X) (ph : Fin e → X → ℝ) (phT : Fin e → ℝ → X → ℝ) (C₅ C t₀ : ℝ), (∀ i, IsSingWeight A L s (th i) (ph i) C₅) → (∀ i, IsRegFamily A Θ L s (th i) (ph i) (phT i) C t₀) → (∀ i, IsRegFamilyC2 A s (ph i) (phT i)) → IsFiniteMeasure (maMeasure A (fun i => th i + LocPot.ofFun (ph i) + Θ)) ∧ ∃ K : ℝ, ∀ R : ℝ, Real.exp 1 ≤ R → maMeasure A (fun i => th i + LocPot.ofFun (ph i) + Θ) (bdry s ∪ {y | R ≤ rW L s y}) ≤ ENNReal.ofReal (K * Real.log R / R) ∧ ∫⁻ y in (bdry s)ᶜ ∩ {y | R ≤ rW L s y}, ENNReal.ofReal (Real.log (rW L s y)) ∂maMeasure A (fun i => th i + LocPot.ofFun (ph i) + Θ) ≤ ENNReal.ofReal (K * Real.log R ^ 2 / R) := by
  intro hTB e X _ _ _ _ _ A Θ L s n m W hΘ hpos hL hS hSNC hnorm th ph phT C₅ C t₀ hW hR hC2
  obtain ⟨K, t₁, ht₁, -, hT⟩ :=
    tail_uniform hTB A Θ L s m W hΘ hpos hL hS hSNC hnorm th ph phT C₅ C t₀ hW hR
  have hB := LeviFormBoundaryTopology.isClosed_bdry hS
  obtain ⟨-, hrm⟩ := TailBoundAlt.bdry_rW_meas A L s hL hS
  have hrc := (rW_open A L s hL hS).1
  have hge := rW_ge L s hnorm
  have hc := locDens_add_ofFun_continuousOn A (bdry s)ᶜ th ph Θ hB.isOpen_compl
    (fun i => (hW i).1) hΘ (fun i => (hW i).2.1)
  have hsm : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i, A.Smooth (phT i t) := eventually_all.2 fun i => by
    filter_upwards [Ioc_mem_nhdsGT (hR i).1] with t ht
    exact ((hR i).2.2 t ht.1 ht.2).1
  have hunif := conv_dens A Θ s th ph phT hB hΘ (fun i => (hW i).1) (fun i => (hW i).2.1) hsm hC2
  have hbd : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Set.Ioc 0 t₁ := Ioc_mem_nhdsGT ht₁
  have hpot : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i, IsPotential A (th i + LocPot.ofFun (phT i t) + Θ) := by
    filter_upwards [hbd] with t ht
    exact fun i => ((hT (fun _ => t) fun _ => ht).1 i).1
  have tail1 : ∀ R : ℝ, Real.exp 1 ≤ R →
      maMeasure A (fun i => th i + LocPot.ofFun (ph i) + Θ) ((bdry s)ᶜ ∩ {y | R ≤ rW L s y}) ≤
        ENNReal.ofReal (K * Real.log R / R) := by
    intro R hRe
    have h := tail_lintegral_le_of_eventually A L s hL hS
      (fun i => th i + LocPot.ofFun (ph i) + Θ) (fun t i => th i + LocPot.ofFun (phT i t) + Θ)
      hc hpot hunif (fun _ => 1) measurable_const continuousOn_const
      R (K * Real.log R / R)
      (fun _ _ _ => zero_le_one) (by
        filter_upwards [hbd] with t ht
        have h1 := ((hT (fun _ => t) fun _ => ht).2 R hRe).1
        simp only [ENNReal.ofReal_one, lintegral_const, one_mul, Measure.restrict_apply,
          MeasurableSet.univ, Set.univ_inter]
        exact (measure_mono (show (bdry s)ᶜ ∩ {y | R ≤ rW L s y} ⊆
          bdry s ∪ {y | R ≤ rW L s y} from fun _ hy => Or.inr hy.2)).trans h1)
    simpa using h
  have tail : ∀ R : ℝ, Real.exp 1 ≤ R →
      maMeasure A (fun i => th i + LocPot.ofFun (ph i) + Θ) (bdry s ∪ {y | R ≤ rW L s y}) ≤
        ENNReal.ofReal (K * Real.log R / R) := by
    intro R hRe
    refine (measure_mono (t := bdry s ∪ ((bdry s)ᶜ ∩ {y | R ≤ rW L s y})) ?_).trans
      ((measure_union_le _ _).trans ?_)
    · rintro y (hy | hy)
      · exact Or.inl hy
      · by_cases hb : y ∈ bdry s
        · exact Or.inl hb
        · exact Or.inr ⟨hb, hy⟩
    · rw [maMeasure_bdry_eq_zero A L s m W hS hSNC, zero_add]
      exact tail1 R hRe
  refine ⟨⟨?_⟩, K, fun R hRe => ⟨tail R hRe, ?_⟩⟩
  · refine lt_of_le_of_lt ((measure_mono fun y _ => Or.inr (hge y)).trans (tail _ le_rfl))
      ENNReal.ofReal_lt_top
  · refine tail_lintegral_le_of_eventually A L s hL hS
      (fun i => th i + LocPot.ofFun (ph i) + Θ) (fun t i => th i + LocPot.ofFun (phT i t) + Θ)
      hc hpot hunif (fun y => Real.log (rW L s y)) hrm.log ?_
      R _ ?_ ?_
    · exact hrc.log fun y hy => ((Real.exp_pos 1).trans_le (hge y)).ne'
    · intro y _ _
      exact Real.log_nonneg (le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) (hge y))
    · filter_upwards [hbd] with t ht
      exact ((hT (fun _ => t) fun _ => ht).2 R hRe).2

end GlobalTheory.CompanionTheory.Ar.Giv
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedEnergyRegularizationBoundStatement
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixed_energy_regularization_bound : TailBoundStatement → ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (A : FinHolAtlas e X) (Θ L : LocPot X) (s : X → X → ℂ) {n : ℕ} (m : Fin n → ℕ) (W : Fin n → Set X), IsPotential A Θ → IsPosPot A Θ → IsPotential A L → IsSection A L s → IsSNC A L s m W → (∀ y, logNormSec L s y ≤ 0) → ∀ (th : Fin e → LocPot X) (ph : Fin e → X → ℝ) (phT : Fin e → ℝ → X → ℝ) (C₅ C t₀ : ℝ), (∀ i, IsSingWeight A L s (th i) (ph i) C₅) → (∀ i, IsRegFamily A Θ L s (th i) (ph i) (phT i) C t₀) → (∀ i, IsRegFamilyC2 A s (ph i) (phT i)) → IsFiniteMeasure (maMeasure A (fun i => th i + LocPot.ofFun (ph i) + Θ)) ∧ ∃ K : ℝ, ∀ R : ℝ, Real.exp 1 ≤ R → maMeasure A (fun i => th i + LocPot.ofFun (ph i) + Θ) (bdry s ∪ {y | R ≤ rW L s y}) ≤ ENNReal.ofReal (K * Real.log R / R) ∧ ∫⁻ y in (bdry s)ᶜ ∩ {y | R ≤ rW L s y}, ENNReal.ofReal (Real.log (rW L s y)) ∂maMeasure A (fun i => th i + LocPot.ofFun (ph i) + Θ) ≤ ENNReal.ofReal (K * Real.log R ^ 2 / R) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.limit_measure_tail | exact GlobalTheory.CompanionTheory.Ar.Giv.limit_measure_tail | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.limit_measure_tail <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ConvergenceStatementHolds
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem conv_tail_split : ∀ {X : Type} [MeasurableSpace X] {l : Filter ℝ} (μT : ℝ → Measure X) (μ : Measure X) (gT : ℝ → X → ℝ) (g : X → ℝ) (E : ℝ → Set X) (b : ℝ → ℝ), Tendsto b atTop (𝓝 0) → (∀ R, MeasurableSet (E R)) → AEStronglyMeasurable g μ → (∀ᶠ t in l, AEStronglyMeasurable (gT t) (μT t)) → (∀ᶠ R in atTop, IntegrableOn g (E R) μ ∧ ∫⁻ y in (E R)ᶜ, ‖g y‖ₑ ∂μ ≤ ENNReal.ofReal (b R) ∧ (∀ᶠ t in l, IntegrableOn (gT t) (E R) (μT t) ∧ ∫⁻ y in (E R)ᶜ, ‖gT t y‖ₑ ∂μT t ≤ ENNReal.ofReal (b R)) ∧ Tendsto (fun t => ∫ y in E R, gT t y ∂μT t) l (𝓝 (∫ y in E R, g y ∂μ))) → Integrable g μ ∧ (∀ᶠ t in l, Integrable (gT t) (μT t)) ∧ Tendsto (fun t => ∫ y, gT t y ∂μT t) l (𝓝 (∫ y, g y ∂μ)) := by
  intro X _ l μT μ gT g E b hb hE hg hgT h
  have key : ∀ (ν : Measure X) (f : X → ℝ) (R : ℝ), AEStronglyMeasurable f ν →
      IntegrableOn f (E R) ν → ∫⁻ y in (E R)ᶜ, ‖f y‖ₑ ∂ν ≤ ENNReal.ofReal (b R) →
      Integrable f ν := by
    intro ν f R hm h1 h2
    have h3 : IntegrableOn f (E R)ᶜ ν := ⟨hm.restrict, lt_of_le_of_lt h2 ENNReal.ofReal_lt_top⟩
    have := h1.union h3
    rwa [Set.union_compl_self, integrableOn_univ] at this
  have tb : ∀ (ν : Measure X) (f : X → ℝ) (R : ℝ),
      ∫⁻ y in (E R)ᶜ, ‖f y‖ₑ ∂ν ≤ ENNReal.ofReal (b R) →
      ‖∫ y in (E R)ᶜ, f y ∂ν‖ ≤ max (b R) 0 := by
    intro ν f R h2
    have h5 := (enorm_integral_le_lintegral_enorm (μ := ν.restrict (E R)ᶜ) f).trans h2
    rw [← ofReal_norm_eq_enorm] at h5
    rcases (ENNReal.ofReal_le_ofReal_iff').1 h5 with h6 | h6
    · exact h6.trans (le_max_left _ _)
    · exact h6.trans (le_max_right _ _)
  obtain ⟨R₀, hR₀⟩ := h.exists
  have hgi₀ := key μ g R₀ hg hR₀.1 hR₀.2.1
  refine ⟨hgi₀, ?_, ?_⟩
  · filter_upwards [hR₀.2.2.1, hgT] with t h1 h2
    exact key _ _ R₀ h2 h1.1 h1.2
  · rw [Metric.tendsto_nhds]
    intro ε hε
    have hε3 : 0 < ε / 3 := by positivity
    have hbs : ∀ᶠ R in atTop, b R < ε / 3 := hb (Iio_mem_nhds hε3)
    obtain ⟨R, hR, hbR⟩ := (h.and hbs).exists
    have hgi := key μ g R hg hR.1 hR.2.1
    have hlim := Metric.tendsto_nhds.1 hR.2.2.2 (ε / 3) hε3
    filter_upwards [hR.2.2.1, hgT, hlim] with t h1 h2 h3
    have hti := key _ _ R h2 h1.1 h1.2
    rw [← integral_add_compl (hE R) hti, ← integral_add_compl (hE R) hgi]
    have e1 := tb (μT t) (gT t) R h1.2
    have e2 := tb μ g R hR.2.1
    have hm : max (b R) 0 < ε / 3 := max_lt hbR hε3
    rw [Real.dist_eq] at h3 ⊢
    rw [Real.norm_eq_abs] at e1 e2
    obtain ⟨a1, a2⟩ := abs_lt.1 h3
    obtain ⟨b1, b2⟩ := abs_le.1 e1
    obtain ⟨c1, c2⟩ := abs_le.1 e2
    rw [abs_lt]
    constructor <;> linarith

theorem conv_tail_enorm : ∀ {X : Type} [MeasurableSpace X] (ν : Measure X) (B : Set X) (r f : X → ℝ) (c R M : ℝ), MeasurableSet (Bᶜ ∩ {y | R ≤ r y}) → ν B = 0 → (∀ y ∉ B, |f y| ≤ c * Real.log (r y)) → (∀ y ∉ B, 0 ≤ Real.log (r y)) → ∫⁻ y in Bᶜ ∩ {y | R ≤ r y}, ENNReal.ofReal (Real.log (r y)) ∂ν ≤ ENNReal.ofReal M → ∫⁻ y in {y | y ∉ B ∧ r y ≤ R}ᶜ, ‖f y‖ₑ ∂ν ≤ ENNReal.ofReal (|c| * M) := by
  intro X _ ν B r f c R M hSm hB hf hl hM
  have hsub : {y | y ∉ B ∧ r y ≤ R}ᶜ ⊆ B ∪ (Bᶜ ∩ {y | R ≤ r y}) := by
    intro y hy
    by_cases hyB : y ∈ B
    · exact Or.inl hyB
    · refine Or.inr ⟨hyB, ?_⟩
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_and, not_le] at hy
      exact (hy hyB).le
  calc ∫⁻ y in {y | y ∉ B ∧ r y ≤ R}ᶜ, ‖f y‖ₑ ∂ν
      ≤ ∫⁻ y in B ∪ (Bᶜ ∩ {y | R ≤ r y}), ‖f y‖ₑ ∂ν := lintegral_mono_set hsub
    _ ≤ ∫⁻ y in B, ‖f y‖ₑ ∂ν + ∫⁻ y in Bᶜ ∩ {y | R ≤ r y}, ‖f y‖ₑ ∂ν := lintegral_union_le _ _ _
    _ = ∫⁻ y in Bᶜ ∩ {y | R ≤ r y}, ‖f y‖ₑ ∂ν := by
        rw [Measure.restrict_eq_zero.2 hB, lintegral_zero_measure, zero_add]
    _ ≤ ∫⁻ y in Bᶜ ∩ {y | R ≤ r y}, ENNReal.ofReal |c| * ENNReal.ofReal (Real.log (r y)) ∂ν := by
        refine setLIntegral_mono' hSm fun y hy => ?_
        rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_mul (abs_nonneg c)]
        exact ENNReal.ofReal_le_ofReal ((hf y hy.1).trans
          (mul_le_mul_of_nonneg_right (le_abs_self c) (hl y hy.1)))
    _ = ENNReal.ofReal |c| * ∫⁻ y in Bᶜ ∩ {y | R ≤ r y}, ENNReal.ofReal (Real.log (r y)) ∂ν :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal |c| * ENNReal.ofReal M := by gcongr
    _ = ENNReal.ofReal (|c| * M) := (ENNReal.ofReal_mul (abs_nonneg c)).symm

theorem conv_mass_approx : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (A : FinHolAtlas e X) (th : Fin e → LocPot X) (u : Fin e → X → ℝ) (Θ : LocPot X), (∀ i, IsPotential A (th i)) → IsPotential A Θ → (∀ i, A.Smooth (u i)) → (∀ i, IsPsh A (th i + LocPot.ofFun (u i) + Θ)) → (maMeasure A (fun i => th i + LocPot.ofFun (u i) + Θ) Set.univ).toReal = mInt A (fun i => th i + Θ) (fun _ => 1) := by
  intro e X _ _ _ _ _ A th u Θ hth hΘ hu hpsh
  have hpot : ∀ i, IsPotential A (th i + LocPot.ofFun (u i) + Θ) := fun i =>
    isPotentialAdd A _ _ (isPotentialAdd A _ _ (hth i) (isPotential_ofFun A _ (hu i))) hΘ
  obtain ⟨hfin, hint⟩ := maMeasure_thm A _ hpot hpsh
  have h1 := hint (fun _ => 1) measurable_const
  have hI : MIntegrable A (fun i => th i + LocPot.ofFun (u i) + Θ) (fun _ => 1) :=
    h1.1.2 (integrable_const 1)
  have hm := h1.2 hI
  rw [integral_const, smul_eq_mul, mul_one, measureReal_def] at hm
  rw [← hm, ← massIndep A (fun i => th i + Θ) u (fun i => isPotentialAdd A _ _ (hth i) hΘ) hu]
  have hD : ∀ j, locDens A (fun i => th i + LocPot.ofFun (u i) + Θ) j =
      locDens A (fun i => th i + Θ + LocPot.ofFun (u i)) j := by
    intro j
    funext y
    unfold locDens
    congr 1
    funext i y'
    show (th i).φ _ _ + u i _ + Θ.φ _ _ = (th i).φ _ _ + Θ.φ _ _ + u i _
    ring
  unfold mInt integralWith
  simp only [hD]

theorem conv_null_of_log_div {X : Type} [MeasurableSpace X] (ν : Measure X) (B : Set X) (K : ℝ)
    (h : ∀ R : ℝ, Real.exp 1 ≤ R → ν B ≤ ENNReal.ofReal (K * Real.log R / R)) : ν B = 0 := by
  have ht : Tendsto (fun R : ℝ => ENNReal.ofReal (K * Real.log R / R)) atTop (𝓝 0) := by
    have h1 := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).const_mul K
    simp only [pow_one, one_mul, add_zero, mul_zero] at h1
    rw [← ENNReal.ofReal_zero]
    refine ENNReal.tendsto_ofReal (h1.congr fun R => ?_)
    ring
  refine le_antisymm (ge_of_tendsto ht ?_) bot_le
  filter_upwards [eventually_ge_atTop (Real.exp 1)] with R hR
  exact h R hR

theorem conv_aesm {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] (ν : Measure X)
    {B : Set X} (hB : IsClosed B) (hν : ν B = 0) {f : X → ℝ} (hf : ContinuousOn f Bᶜ) :
    AEStronglyMeasurable f ν := by
  have h := hf.aestronglyMeasurable (μ := ν) hB.isOpen_compl.measurableSet
  rwa [Measure.restrict_eq_self_of_ae_mem (s := Bᶜ) (compl_mem_ae_iff.2 hν)] at h

theorem conv_limit_props {X : Type} [TopologicalSpace X] (U : Set X) (g : X → ℝ) (gT : ℝ → X → ℝ)
    (b : X → ℝ) (hc : ∀ t, ContinuousOn (gT t) U) (hb : ∀ t y, y ∈ U → |gT t y| ≤ b y)
    (hl : TendstoLocallyUniformlyOn gT g (𝓝[>] 0) U) :
    ContinuousOn g U ∧ ∀ y ∈ U, |g y| ≤ b y := by
  refine ⟨hl.continuousOn (Frequently.of_forall hc), fun y hy => ?_⟩
  have ht : Tendsto (fun t => gT t y) (𝓝[>] 0) (𝓝 (g y)) := hl.tendsto_at hy
  exact le_of_tendsto ht.abs (Eventually.of_forall fun t => hb t y hy)

theorem conv_core {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] (A : FinHolAtlas e X) (Θ L : LocPot X) (s : X → X → ℂ) {n : ℕ}
    (m : Fin n → ℕ) (W : Fin n → Set X) (hΘ : IsPotential A Θ) (hpos : IsPosPot A Θ)
    (hL : IsPotential A L) (hS : IsSection A L s) (hSNC : IsSNC A L s m W)
    (hnorm : ∀ y, logNormSec L s y ≤ 0)
    (th : Fin e → LocPot X) (ph : Fin e → X → ℝ) (phT : Fin e → ℝ → X → ℝ) (C₅ C t₀ : ℝ)
    (hW : ∀ i, IsSingWeight A L s (th i) (ph i) C₅)
    (hR : ∀ i, IsRegFamily A Θ L s (th i) (ph i) (phT i) C t₀)
    (hC2 : ∀ i, IsRegFamilyC2 A s (ph i) (phT i))
    (g : X → ℝ) (gT : ℝ → X → ℝ) (C₆ : ℝ) (hgc : ∀ t, ContinuousOn (gT t) (bdry s)ᶜ)
    (hgb : ∀ t y, y ∉ bdry s → |gT t y| ≤ C₆ * Real.log (rW L s y))
    (hgl : TendstoLocallyUniformlyOn gT g (𝓝[>] 0) (bdry s)ᶜ) :
    Integrable g (maMeasure A (fun i => th i + LocPot.ofFun (ph i) + Θ)) ∧
    (∀ᶠ t in 𝓝[>] 0, Integrable (gT t) (maMeasure A (fun i => th i + LocPot.ofFun (phT i t) + Θ))) ∧
    Tendsto (fun t => ∫ y, gT t y ∂maMeasure A (fun i => th i + LocPot.ofFun (phT i t) + Θ))
      (𝓝[>] 0) (𝓝 (∫ y, g y ∂maMeasure A (fun i => th i + LocPot.ofFun (ph i) + Θ))) := by
  obtain ⟨-, K₁, hK₁⟩ := GlobalTheory.T.mixed_energy_regularization_bound tailBound_holds A Θ L s m W hΘ hpos hL hS hSNC hnorm
    th ph phT C₅ C t₀ hW hR hC2
  obtain ⟨K₂, t₁, ht₁, ht₁₀, hU⟩ := tail_uniform tailBound_holds A Θ L s m W hΘ hpos hL hS hSNC
    hnorm th ph phT C₅ C t₀ hW hR
  have hB : IsClosed (bdry s) := LeviFormBoundaryTopology.isClosed_bdry hS
  have hUo : IsOpen (bdry s)ᶜ := hB.isOpen_compl
  have hlog : ∀ y, 0 ≤ Real.log (rW L s y) := fun y =>
    Real.log_nonneg (by linarith [rW_ge L s hnorm y, Real.add_one_le_exp (1 : ℝ)])
  obtain ⟨hgcont, hgbd⟩ := conv_limit_props (bdry s)ᶜ g gT (fun y => C₆ * Real.log (rW L s y))
    hgc (fun t y hy => hgb t y hy) hgl
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ t ≤ t₁ := by
    filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT ht₁] with t ht ht'
    exact ⟨ht, ht'.2.le⟩
  have hpot : ∀ t, 0 < t ∧ t ≤ t₁ → ∀ i, IsPotential A (th i + LocPot.ofFun (phT i t) + Θ) ∧
      IsPsh A (th i + LocPot.ofFun (phT i t) + Θ) := fun t ht => (hU (fun _ => t) (fun _ => ht)).1
  have htail : ∀ t, 0 < t ∧ t ≤ t₁ → ∀ R, Real.exp 1 ≤ R →
      ∫⁻ y in (bdry s)ᶜ ∩ {y | R ≤ rW L s y}, ENNReal.ofReal (Real.log (rW L s y))
        ∂maMeasure A (fun i => th i + LocPot.ofFun (phT i t) + Θ) ≤
        ENNReal.ofReal (K₂ * Real.log R ^ 2 / R) := fun t ht R hR =>
    ((hU (fun _ => t) (fun _ => ht)).2 R hR).2
  have hμT0 : ∀ t, 0 < t ∧ t ≤ t₁ →
      maMeasure A (fun i => th i + LocPot.ofFun (phT i t) + Θ) (bdry s) = 0 := fun t ht =>
    bdry_null A L s m W hL hS hSNC _ (fun i => (hpot t ht i).1)
  have hμTfin : ∀ t, 0 < t ∧ t ≤ t₁ →
      IsFiniteMeasure (maMeasure A (fun i => th i + LocPot.ofFun (phT i t) + Θ)) := fun t ht =>
    (maMeasure_thm A _ (fun i => (hpot t ht i).1) (fun i => (hpot t ht i).2)).1
  have hμ0 : maMeasure A (fun i => th i + LocPot.ofFun (ph i) + Θ) (bdry s) = 0 :=
    conv_null_of_log_div _ _ K₁ fun R hR => (measure_mono Set.subset_union_left).trans (hK₁ R hR).1
  have hsm : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i, A.Smooth (phT i t) := by
    rw [eventually_all]
    intro i
    filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (hR i).1] with t ht ht'
    exact ((hR i).2.2 t ht ht'.2.le).1
  set Kc : ℝ → Set X := fun R => {y | y ∉ bdry s ∧ rW L s y ≤ R} with hKc
  have hKcpt : ∀ R, IsCompact (Kc R) := fun R => isCompact_rW_sublevel A L s hL hS R
  have hKm : ∀ R, MeasurableSet (Kc R) := fun R => (hKcpt R).isClosed.measurableSet
  have hKU : ∀ R, Kc R ⊆ (bdry s)ᶜ := fun R y hy => hy.1
  have hSm : ∀ R : ℝ, MeasurableSet ((bdry s)ᶜ ∩ {y | R ≤ rW L s y}) := by
    intro R
    have : (bdry s)ᶜ ∩ {y | R ≤ rW L s y} = (bdry s)ᶜ \ {y | y ∉ bdry s ∧ rW L s y < R} := by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_diff, not_and,
        not_lt]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun _ => h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, h2 h1⟩
    rw [this]
    exact hUo.measurableSet.diff ((rW_open A L s hL hS).2 R).measurableSet
  have hcp := fun R => compact_part_integrals_tendsto A (bdry s)ᶜ
    (fun i => th i + LocPot.ofFun (ph i) + Θ) (fun t i => th i + LocPot.ofFun (phT i t) + Θ) hUo
    (fun j => locDens_add_ofFun_continuousOn A (bdry s)ᶜ th ph Θ hUo (fun i => (hW i).1) hΘ
      (fun i => (hW i).2.1) j)
    (hsm.mono fun t ht i => isPotentialAdd A _ _ (isPotentialAdd A _ _ (hW i).1
      (isPotential_ofFun A _ (ht i))) hΘ)
    (conv_dens A Θ s th ph phT hB hΘ (fun i => (hW i).1) (fun i => (hW i).2.1) hsm hC2)
    g gT hgc hgl (Kc R) (Kc R) (hKcpt R) (hKU R) (hKm R) subset_rfl
  set K := max K₁ K₂ with hK
  set b : ℝ → ℝ := fun R => |C₆| * (K * Real.log R ^ 2 / R) with hbdef
  have hb : Tendsto b atTop (𝓝 0) := by
    have h1 := ((Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).const_mul K).const_mul |C₆|
    simp only [one_mul, add_zero, mul_zero] at h1
    refine h1.congr fun R => ?_
    simp only [hbdef]
    ring
  refine conv_tail_split (fun t => maMeasure A (fun i => th i + LocPot.ofFun (phT i t) + Θ)) _ gT g Kc b hb hKm
    (conv_aesm _ hB hμ0 hgcont) (hev.mono fun t ht => conv_aesm _ hB (hμT0 t ht) (hgc t)) ?_
  filter_upwards [eventually_ge_atTop (Real.exp 1)] with R hR
  have hRpos : 0 ≤ Real.log R ^ 2 / R := div_nonneg (sq_nonneg _) ((Real.exp_pos 1).le.trans hR)
  have hKb : ∀ K', K' ≤ K → ENNReal.ofReal (K' * Real.log R ^ 2 / R) ≤
      ENNReal.ofReal (K * Real.log R ^ 2 / R) := fun K' hK' =>
    ENNReal.ofReal_le_ofReal (by
      rw [mul_div_assoc, mul_div_assoc]
      exact mul_le_mul_of_nonneg_right hK' hRpos)
  refine ⟨(hcp R).2.1, ?_, ?_, (hcp R).2.2⟩
  · exact conv_tail_enorm _ (bdry s) (rW L s) g C₆ R (K * Real.log R ^ 2 / R) (hSm R) hμ0
      (fun y hy => hgbd y hy) (fun y _ => hlog y)
      (((hK₁ R hR).2).trans (hKb K₁ (le_max_left _ _)))
  · filter_upwards [hev] with t ht
    haveI := hμTfin t ht
    refine ⟨ContinuousOn.integrableOn_compact (hKcpt R) ((hgc t).mono (hKU R)), ?_⟩
    exact conv_tail_enorm _ (bdry s) (rW L s) (gT t) C₆ R _ (hSm R) (hμT0 t ht) (fun y hy => hgb t y hy)
      (fun y _ => hlog y) ((htail t ht R hR).trans (hKb K₂ (le_max_right _ _)))

theorem convergence_holds : ConvergenceStatement := by
  intro e X _ _ _ _ _ A Θ L s n m W hΘ hpos hL hS hSNC hnorm th ph phT C₅ C t₀ hW hR hC2 g gT C₆
    hgc hgb hgl
  intro μT μ
  obtain ⟨hfin, -⟩ := GlobalTheory.T.mixed_energy_regularization_bound tailBound_holds A Θ L s m W hΘ hpos hL hS hSNC hnorm
    th ph phT C₅ C t₀ hW hR hC2
  obtain ⟨hg1, hg2, hg3⟩ := conv_core A Θ L s m W hΘ hpos hL hS hSNC hnorm th ph phT C₅ C t₀
    hW hR hC2 g gT C₆ hgc hgb hgl
  refine ⟨hfin, ?_, hg1, hg2, hg3⟩
  have hlog1 : ∀ y, 1 ≤ Real.log (rW L s y) := fun y => by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (rW_ge L s hnorm y)
  have hconst : TendstoLocallyUniformlyOn (fun (_ : ℝ) (_ : X) => (1 : ℝ)) (fun _ => 1)
      (𝓝[>] 0) (bdry s)ᶜ := by
    intro u hu x _
    exact ⟨Set.univ, Filter.univ_mem, Eventually.of_forall fun _ y _ => refl_mem_uniformity hu⟩
  have hc1 := (conv_core A Θ L s m W hΘ hpos hL hS hSNC hnorm th ph phT C₅ C t₀ hW hR hC2
    (fun _ => 1) (fun _ _ => 1) 1 (fun _ => continuousOn_const)
    (fun t y _ => by simpa using hlog1 y) hconst).2.2
  obtain ⟨K₂, t₁, ht₁, ht₁₀, hU⟩ := tail_uniform tailBound_holds A Θ L s m W hΘ hpos hL hS hSNC
    hnorm th ph phT C₅ C t₀ hW hR
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), mInt A (fun i => th i + Θ) (fun _ => 1) =
      ∫ y, (fun _ => (1 : ℝ)) y ∂maMeasure A (fun i => th i + LocPot.ofFun (phT i t) + Θ) := by
    filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT ht₁] with t ht ht'
    have hp := (hU (fun _ => t) (fun _ => ⟨ht, ht'.2.le⟩)).1
    rw [integral_const, smul_eq_mul, mul_one, measureReal_def]
    exact (conv_mass_approx A th (fun i => phT i t) Θ (fun i => (hW i).1) hΘ
      (fun i => ((hR i).2.2 t ht (ht'.2.le.trans (ht₁₀ (hR i).1))).1) (fun i => (hp i).2)).symm
  have h2 := tendsto_nhds_unique hc1 (tendsto_const_nhds.congr' hev)
  rw [integral_const, smul_eq_mul, mul_one, measureReal_def] at h2
  exact h2

end GlobalTheory.CompanionTheory.Ar.Giv
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ConvergenceStatementHoldsStatement
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.convergence_statement_holds : ConvergenceStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.convergence_holds | exact GlobalTheory.CompanionTheory.Ar.Giv.convergence_holds | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.convergence_holds <;> assumption)
end
