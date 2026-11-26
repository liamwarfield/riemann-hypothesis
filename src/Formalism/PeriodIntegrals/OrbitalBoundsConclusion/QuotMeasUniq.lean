module

public import Formalism.PeriodIntegrals.QuotInv

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuotientMeasureUniqueness.QmuWeight
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace PI.QuotMeasUniqW

def QmuWeight : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G), IsClosed (H : Set G) →
    ∀ ν : Measure H, ν.IsHaarMeasure →
      ∃ w : G → ℝ≥0∞, Measurable w ∧
        ∀ g : G, (∫⁻ h, w (g * (h : G)) ∂ν) ≠ 0 ∧ (∫⁻ h, w (g * (h : G)) ∂ν) ≠ ⊤

def QmuLift : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G), IsClosed (H : Set G) →
    ∀ ν : Measure H, ν.IsHaarMeasure →
    ∀ ρ : Measure (G ⧸ H), (∀ K : Set (G ⧸ H), IsCompact K → ρ K < ⊤) →
      (∀ (g : G) (s : Set (G ⧸ H)), MeasurableSet s → ρ ((fun y => g • y) ⁻¹' s) = ρ s) →
      ∃ l : Measure G, l.IsMulLeftInvariant ∧ IsFiniteMeasureOnCompacts l ∧
        ∀ f : G → ℝ≥0∞, Measurable f →
          ∫⁻ x, f x ∂l = ∫⁻ y, (∫⁻ h, f (y.out * (h : G)) ∂ν) ∂ρ

end PI.QuotMeasUniqW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuotientMeasureUniqueness.QLiftIsMulLeftInvariant
noncomputable section

open MeasureTheory Pointwise
open scoped ENNReal

namespace PI.QuotMeasUniqW

theorem indicator_preimage_one {α β : Type*} (f : α → β) (s : Set β) (x : α) :
    (f ⁻¹' s).indicator (1 : α → ℝ≥0∞) x = s.indicator 1 (f x) := by
  by_cases h : f x ∈ s
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show x ∈ f ⁻¹' s from h)]
    rfl
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (show x ∉ f ⁻¹' s from h)]

def hAvg {G : Type} [Group G] [MeasurableSpace G] {H : Subgroup G} (ν : Measure H) (f : G → ℝ≥0∞)
    (g : G) : ℝ≥0∞ :=
  ∫⁻ h, f (g * (h : G)) ∂ν

theorem measurable_hAvg {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {H : Subgroup G}
    (ν : Measure H) [SFinite ν] {f : G → ℝ≥0∞} (hf : Measurable f) : Measurable (hAvg ν f) := by
  unfold hAvg
  have hm : Measurable (fun p : G × H => f (p.1 * (p.2 : G))) :=
    hf.comp (measurable_fst.mul (measurable_subtype_coe.comp measurable_snd))
  exact hm.lintegral_prod_right'

theorem hAvg_mul_mem {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] {H : Subgroup G}
    (ν : Measure H) [ν.IsMulLeftInvariant] (f : G → ℝ≥0∞) (g : G) (h0 : H) :
    hAvg ν f (g * h0) = hAvg ν f g := by
  have key := lintegral_mul_left_eq_self (μ := ν) (fun x : H => f (g * (x : G))) h0
  simp only [hAvg, Subgroup.coe_mul, mul_assoc] at key ⊢
  exact key

private theorem exists_out_eq_mul {G : Type} [Group G] {H : Subgroup G} (g : G) :
    ∃ h : H, (g : G ⧸ H).out = g * (h : G) := by
  exact QuotientGroup.mk_out_eq_mul H g

theorem hAvg_out {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] {H : Subgroup G}
    (ν : Measure H) [ν.IsMulLeftInvariant] (f : G → ℝ≥0∞) (g : G) :
    hAvg ν f ((g : G ⧸ H).out) = hAvg ν f g := by
  obtain ⟨h0, hh⟩ := exists_out_eq_mul (H := H) g
  rw [hh]
  exact hAvg_mul_mem ν f g h0

theorem measurable_hAvg_out {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {H : Subgroup G}
    (ν : Measure H) [SFinite ν] [ν.IsMulLeftInvariant] {f : G → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun y : G ⧸ H => hAvg ν f y.out) := by
  refine QuotientGroup.measurable_from_quotient.2 ?_
  convert measurable_hAvg ν hf using 1
  funext g
  exact hAvg_out ν f g

private theorem lintegral_indicator_one_le' {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (S : Set α) : ∫⁻ a, S.indicator 1 a ∂μ ≤ μ S := by
  exact lintegral_indicator_one_le S

theorem hAvg_indicator_le {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] {H : Subgroup G}
    (ν : Measure H) [ν.IsMulLeftInvariant] (C K : Set G) (d g : G) (hC : ∀ x ∈ C, d⁻¹ * x ∈ K) :
    hAvg ν (C.indicator 1) g ≤ ν {h : H | (h : G) ∈ K⁻¹ * K} := by
  have hint_r : hAvg ν (C.indicator 1) g
      = ∫⁻ h, ((fun h : H => g * (h : G)) ⁻¹' C).indicator 1 h ∂ν := by
    unfold hAvg
    exact lintegral_congr fun h => (indicator_preimage_one (fun h : H => g * (h : G)) C h).symm
  rw [hint_r]
  refine (lintegral_indicator_one_le' ν _).trans ?_
  rcases ((fun h : H => g * (h : G)) ⁻¹' C).eq_empty_or_nonempty with h0 | ⟨h1, hh1⟩
  · rw [h0]; simp
  · have hsub : (fun h : H => g * (h : G)) ⁻¹' C
        ⊆ (fun h : H => h1⁻¹ * h) ⁻¹' {h : H | (h : G) ∈ K⁻¹ * K} := by
      intro h hh
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, Subgroup.coe_mul, Subgroup.coe_inv]
      have a1 : d⁻¹ * (g * (h1 : G)) ∈ K := hC (g * (h1 : G)) hh1
      have a2 : d⁻¹ * (g * (h : G)) ∈ K := hC (g * (h : G)) hh
      have e : (h1 : G)⁻¹ * (h : G) = (d⁻¹ * (g * (h1 : G)))⁻¹ * (d⁻¹ * (g * (h : G))) := by
        group
      rw [e]
      exact Set.mul_mem_mul (Set.inv_mem_inv.2 a1) a2
    calc ν ((fun h : H => g * (h : G)) ⁻¹' C)
        ≤ ν ((fun h : H => h1⁻¹ * h) ⁻¹' {h : H | (h : G) ∈ K⁻¹ * K}) := measure_mono hsub
      _ = ν {h : H | (h : G) ∈ K⁻¹ * K} := by
        exact measure_preimage_mul ν h1⁻¹ _

def qKer {G : Type} [Group G] [MeasurableSpace G] {H : Subgroup G} (ν : Measure H)
    (y : G ⧸ H) : Measure G :=
  Measure.map (fun h : H => y.out * (h : G)) ν

theorem lintegral_qKer {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] {H : Subgroup G} (ν : Measure H) {f : G → ℝ≥0∞}
    (hf : Measurable f) (y : G ⧸ H) : ∫⁻ x, f x ∂qKer ν y = hAvg ν f y.out := by
  unfold qKer hAvg
  exact lintegral_map hf ((measurable_const_mul _).comp measurable_subtype_coe)

theorem measurable_qKer {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {H : Subgroup G}
    (ν : Measure H) [SFinite ν] [ν.IsMulLeftInvariant] : Measurable (qKer (H := H) ν) := by
  refine Measure.measurable_of_measurable_coe _ (fun s hs => ?_)
  have hi : Measurable (s.indicator (1 : G → ℝ≥0∞)) := measurable_one.indicator hs
  have e : (fun y : G ⧸ H => qKer ν y s)
      = fun y : G ⧸ H => hAvg ν (s.indicator 1) y.out := by
    funext y
    rw [← lintegral_qKer ν hi y, lintegral_indicator_one hs]
  rw [e]
  exact measurable_hAvg_out ν hi

def qLift {G : Type} [Group G] [MeasurableSpace G] {H : Subgroup G} (ν : Measure H)
    (ρ : Measure (G ⧸ H)) : Measure G :=
  ρ.bind (qKer ν)

theorem lintegral_qLift {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {H : Subgroup G}
    (ν : Measure H) [SFinite ν] [ν.IsMulLeftInvariant] (ρ : Measure (G ⧸ H)) {f : G → ℝ≥0∞}
    (hf : Measurable f) : ∫⁻ x, f x ∂qLift ν ρ = ∫⁻ y, hAvg ν f y.out ∂ρ := by
  have hb : ∫⁻ x, f x ∂qLift ν ρ = ∫⁻ y, ∫⁻ x, f x ∂qKer ν y ∂ρ := by
    exact Measure.lintegral_bind (measurable_qKer ν).aemeasurable hf.aemeasurable
  rw [hb]
  exact lintegral_congr fun y => lintegral_qKer ν hf y

theorem measurable_smul_quot {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {H : Subgroup G} (g : G) :
    Measurable (fun y : G ⧸ H => g • y) := by
  refine QuotientGroup.measurable_from_quotient.2 ?_
  exact QuotientGroup.measurable_coe.comp (measurable_const_mul g)

theorem qLift_isMulLeftInvariant {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {H : Subgroup G}
    (ν : Measure H) [SFinite ν] [ν.IsMulLeftInvariant] (ρ : Measure (G ⧸ H))
    (hρg : ∀ (g : G) (s : Set (G ⧸ H)), MeasurableSet s → ρ ((fun y => g • y) ⁻¹' s) = ρ s) :
    (qLift ν ρ).IsMulLeftInvariant := by
  refine ⟨fun g => ?_⟩
  have hmap : Measure.map (fun y : G ⧸ H => g • y) ρ = ρ := by
    ext s hs
    rw [Measure.map_apply (measurable_smul_quot g) hs]
    exact hρg g s hs
  have key : ∀ f : G → ℝ≥0∞, Measurable f →
      ∫⁻ x, f x ∂Measure.map (fun x => g * x) (qLift ν ρ) = ∫⁻ x, f x ∂qLift ν ρ := by
    intro f hf
    have hfg : Measurable (fun x => f (g * x)) := hf.comp (measurable_const_mul g)
    have hF : Measurable (fun y : G ⧸ H => hAvg ν f y.out) :=
      measurable_hAvg_out ν hf
    have hpt : ∀ y : G ⧸ H,
        hAvg ν (fun x => f (g * x)) y.out = hAvg ν f (g • y).out := by
      intro y
      have h1 : hAvg ν (fun x => f (g * x)) y.out = hAvg ν f (g * y.out) := by
        simp only [hAvg, mul_assoc]
      have h2 : (g • y : G ⧸ H) = ((g * y.out : G) : G ⧸ H) := by
        calc (g • y : G ⧸ H) = g • ((y.out : G) : G ⧸ H) := by
              rw [QuotientGroup.out_eq']
          _ = ((g * y.out : G) : G ⧸ H) := by
              rfl
      rw [h1, h2, hAvg_out]
    calc ∫⁻ x, f x ∂Measure.map (fun x => g * x) (qLift ν ρ)
        = ∫⁻ x, f (g * x) ∂qLift ν ρ := lintegral_map hf (measurable_const_mul g)
      _ = ∫⁻ y, hAvg ν (fun x => f (g * x)) y.out ∂ρ := lintegral_qLift ν ρ hfg
      _ = ∫⁻ y, hAvg ν f (g • y).out ∂ρ := lintegral_congr hpt
      _ = ∫⁻ y, hAvg ν f y.out ∂Measure.map (fun y : G ⧸ H => g • y) ρ :=
          (lintegral_map hF (measurable_smul_quot (H := H) g)).symm
      _ = ∫⁻ y, hAvg ν f y.out ∂ρ := by rw [hmap]
      _ = ∫⁻ x, f x ∂qLift ν ρ := (lintegral_qLift ν ρ hf).symm
  ext s hs
  have e1 := lintegral_indicator_one (μ := Measure.map (fun x => g * x) (qLift ν ρ)) hs
  have e2 := lintegral_indicator_one (μ := qLift ν ρ) hs
  rw [← e1, ← e2]
  exact key _ (measurable_one.indicator hs)

theorem qLift_finite {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {H : Subgroup G}
    (hH : IsClosed (H : Set G)) (ν : Measure H) [SFinite ν] [ν.IsMulLeftInvariant]
    [IsFiniteMeasureOnCompacts ν] (ρ : Measure (G ⧸ H))
    (hρK : ∀ K : Set (G ⧸ H), IsCompact K → ρ K < ⊤) : IsFiniteMeasureOnCompacts (qLift ν ρ) := by
  refine ⟨?_⟩
  intro K hK
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hi : Measurable (K.indicator (1 : G → ℝ≥0∞)) := measurable_one.indicator hKm
  have hKK : IsCompact (K⁻¹ * K) := hK.inv.mul hK
  have hc : IsCompact {h : H | (h : G) ∈ K⁻¹ * K} := by
    exact hH.isClosedEmbedding_subtypeVal.isCompact_preimage hKK
  have hM : ν {h : H | (h : G) ∈ K⁻¹ * K} < ⊤ := hc.measure_lt_top
  have hP : ρ (QuotientGroup.mk '' K : Set (G ⧸ H)) < ⊤ := by
    exact hρK _ (hK.image QuotientGroup.continuous_mk)
  have hpt : ∀ y : G ⧸ H, hAvg ν (K.indicator 1) y.out
      ≤ (QuotientGroup.mk '' K : Set (G ⧸ H)).indicator
          (fun _ => ν {h : H | (h : G) ∈ K⁻¹ * K}) y := by
    intro y
    have hmk : ∀ h : H, ((y.out * (h : G) : G) : G ⧸ H) = y := by
      intro h
      exact (QuotientGroup.mk_mul_of_mem _ h.2).trans (QuotientGroup.out_eq' y)
    by_cases hy : y ∈ (QuotientGroup.mk '' K : Set (G ⧸ H))
    · rw [Set.indicator_of_mem hy]
      exact hAvg_indicator_le ν K K 1 y.out (fun x hx => by simpa using hx)
    · have hz : ∀ h : H, K.indicator (1 : G → ℝ≥0∞) (y.out * (h : G)) = 0 := by
        intro h
        rw [Set.indicator_apply_eq_zero]
        intro hmem
        exact (hy ⟨_, hmem, hmk h⟩).elim
      have hfz : hAvg ν (K.indicator 1) y.out = 0 := by
        simp only [hAvg, hz, lintegral_zero]
      rw [hfz]
      exact zero_le
  calc qLift ν ρ K = ∫⁻ x, K.indicator 1 x ∂qLift ν ρ :=
        (lintegral_indicator_one hKm).symm
    _ = ∫⁻ y, hAvg ν (K.indicator 1) y.out ∂ρ := lintegral_qLift ν ρ hi
    _ ≤ ∫⁻ y, (QuotientGroup.mk '' K : Set (G ⧸ H)).indicator
          (fun _ => ν {h : H | (h : G) ∈ K⁻¹ * K}) y ∂ρ := lintegral_mono hpt
    _ ≤ ν {h : H | (h : G) ∈ K⁻¹ * K} * ρ (QuotientGroup.mk '' K : Set (G ⧸ H)) :=
        lintegral_indicator_const_le _ _
    _ < ⊤ := by
        exact ENNReal.mul_lt_top hM hP

theorem qmuLift : QmuLift := by
  intro G _ _ _ _ _ _ _ _ H hH ν hν ρ hρK hρg
  have : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology H := TopologicalSpace.Subtype.secondCountableTopology (H : Set G)
  have : SigmaCompactSpace H := inferInstance
  have : SigmaFinite ν := inferInstance
  exact ⟨qLift ν ρ, qLift_isMulLeftInvariant ν ρ hρg,
    qLift_finite hH ν ρ hρK, fun f hf => lintegral_qLift ν ρ hf⟩

end PI.QuotMeasUniqW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuotientMeasureUniqueness.Weight
noncomputable section

open MeasureTheory Pointwise
open scoped ENNReal

namespace PI.QuotMeasUniqW

theorem qmuWeight : QmuWeight := by
  intro G _ _ _ _ _ _ _ _ H hH ν hν
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : G)
  have hVo : IsOpen (interior K) := isOpen_interior
  have hVK : interior K ⊆ K := interior_subset
  have h1V : (1 : G) ∈ interior K := mem_interior_iff_mem_nhds.2 hK1
  obtain ⟨d, hd⟩ := TopologicalSpace.exists_dense_seq G
  have hCo : ∀ n, IsOpen (d n • interior K) := fun n => hVo.smul (d n)
  have hCm : ∀ n, MeasurableSet (d n • interior K) := fun n => (hCo n).measurableSet
  have hind : ∀ n, Measurable ((d n • interior K).indicator (1 : G → ℝ≥0∞)) :=
    fun n => measurable_one.indicator (hCm n)
  refine ⟨fun x => ∑' n, (2⁻¹ : ℝ≥0∞) ^ n * (d n • interior K).indicator 1 x,
    Measurable.tsum fun n => (hind n).const_mul _, fun g => ?_⟩
  have hmg : ∀ n, Measurable fun h : H => (d n • interior K).indicator (1 : G → ℝ≥0∞) (g * (h : G)) :=
    fun n => (hind n).comp ((measurable_const_mul g).comp measurable_subtype_coe)
  have hterm : ∀ n, Measurable fun h : H =>
      (2⁻¹ : ℝ≥0∞) ^ n * (d n • interior K).indicator 1 (g * (h : G)) :=
    fun n => (hmg n).const_mul _
  have hM : ν {h : H | (h : G) ∈ K⁻¹ * K} ≠ ⊤ := by
    have hc : IsCompact (((↑) : H → G) ⁻¹' (K⁻¹ * K)) :=
      hH.isClosedEmbedding_subtypeVal.isCompact_preimage (hK.inv.mul hK)
    exact hc.measure_lt_top.ne
  have hle : ∀ n, ∫⁻ h, (d n • interior K).indicator 1 (g * (h : G)) ∂ν
      ≤ ν {h : H | (h : G) ∈ K⁻¹ * K} := by
    intro n
    refine hAvg_indicator_le ν (d n • interior K) K (d n) g ?_
    intro x hx
    rw [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul] at hx
    exact hVK hx
  show (∫⁻ h, ∑' n, (2⁻¹ : ℝ≥0∞) ^ n * (d n • interior K).indicator 1 (g * (h : G)) ∂ν) ≠ 0 ∧
    (∫⁻ h, ∑' n, (2⁻¹ : ℝ≥0∞) ^ n * (d n • interior K).indicator 1 (g * (h : G)) ∂ν) ≠ ⊤
  constructor
  · obtain ⟨n, hn⟩ : ∃ n, (d n)⁻¹ * g ∈ interior K := by
      have ho : IsOpen {x : G | x⁻¹ * g ∈ interior K} :=
        hVo.preimage (continuous_inv.mul continuous_const)
      exact hd.exists_mem_open ho ⟨g, by simpa using h1V⟩
    have hSo : IsOpen {h : H | g * (h : G) ∈ d n • interior K} :=
      (hCo n).preimage (continuous_const.mul continuous_subtype_val)
    have hS1 : (1 : H) ∈ {h : H | g * (h : G) ∈ d n • interior K} := by
      show g * ((1 : H) : G) ∈ d n • interior K
      rw [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul]
      simpa [mul_assoc] using hn
    have hpos : 0 < ν {h : H | g * (h : G) ∈ d n • interior K} := hSo.measure_pos ν ⟨1, hS1⟩
    have heq : ∫⁻ h, (d n • interior K).indicator 1 (g * (h : G)) ∂ν
        = ν {h : H | g * (h : G) ∈ d n • interior K} := by
      have hfun : (fun h : H => (d n • interior K).indicator (1 : G → ℝ≥0∞) (g * (h : G)))
          = ((fun h : H => g * (h : G)) ⁻¹' (d n • interior K)).indicator 1 := by
        funext h
        exact (indicator_preimage_one (fun h : H => g * (h : G)) (d n • interior K) h).symm
      rw [hfun]
      exact lintegral_indicator_one hSo.measurableSet
    apply ne_of_gt
    calc (0 : ℝ≥0∞) < (2⁻¹ : ℝ≥0∞) ^ n * ν {h : H | g * (h : G) ∈ d n • interior K} :=
          ENNReal.mul_pos (pow_ne_zero _ (by simp)) hpos.ne'
      _ = ∫⁻ h, (2⁻¹ : ℝ≥0∞) ^ n * (d n • interior K).indicator 1 (g * (h : G)) ∂ν := by
          rw [lintegral_const_mul _ (hmg n), heq]
      _ ≤ ∫⁻ h, ∑' m, (2⁻¹ : ℝ≥0∞) ^ m * (d m • interior K).indicator 1 (g * (h : G)) ∂ν :=
          lintegral_mono fun h => ENNReal.le_tsum
            (f := fun m => (2⁻¹ : ℝ≥0∞) ^ m * (d m • interior K).indicator 1 (g * (h : G))) n
  · rw [lintegral_tsum fun n => (hterm n).aemeasurable]
    refine ne_top_of_le_ne_top (b := ∑' n, (2⁻¹ : ℝ≥0∞) ^ n * ν {h : H | (h : G) ∈ K⁻¹ * K}) ?_ ?_
    · rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
      exact ENNReal.mul_ne_top (by simp) hM
    · refine ENNReal.tsum_le_tsum fun n => ?_
      rw [lintegral_const_mul _ (hmg n)]
      gcongr
      exact hle n

end PI.QuotMeasUniqW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuotientMeasureUniqueness.WqUniqueOf
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace PI.QuotMeasUniqW

theorem wqUnique_of (hw : QmuWeight) (hl : QmuLift) : PI.WeilQuotMeas.WqUnique := by
  unfold PI.WeilQuotMeas.WqUnique
  intro G _ _ _ _ _ _ _ _ H hH ρ ρ' hρ hK hinv hK' hinv'
  haveI : LocallyCompactSpace H := hH.locallyCompactSpace
  obtain ⟨ν, hνdef⟩ : ∃ ν : Measure H, ν = Measure.haar := ⟨_, rfl⟩
  have hν : ν.IsHaarMeasure := by rw [hνdef]; infer_instance
  haveI := hν
  haveI : SecondCountableTopology H := TopologicalSpace.Subtype.secondCountableTopology (H : Set G)
  haveI : SigmaFinite ν := inferInstance
  obtain ⟨w, hwm, hwW⟩ := hw G H hH ν hν
  obtain ⟨l, hlI, hlF, hlW⟩ := hl G H hH ν hν ρ hK hinv
  obtain ⟨l', hlI', hlF', hlW'⟩ := hl G H hH ν hν ρ' hK' hinv'

  obtain ⟨W, hW⟩ : ∃ W : G → ℝ≥0∞, ∀ g, W g = ∫⁻ h : H, w (g * h) ∂ν := ⟨_, fun _ => rfl⟩
  have hW0 : ∀ g, W g ≠ 0 := fun g => by rw [hW]; exact (hwW g).1
  have hWt : ∀ g, W g ≠ ∞ := fun g => by rw [hW]; exact (hwW g).2
  have hWmul : ∀ (g : G) (h₀ : H), W (g * h₀) = W g := by
    intro g h₀
    rw [hW, hW]
    have := lintegral_mul_left_eq_self (μ := ν) (fun h : H => w (g * h)) h₀
    simpa only [Subgroup.coe_mul, mul_assoc] using this
  have hwc : ∀ g : G, Measurable fun h : H => w (g * h) :=
    fun g => hwm.comp (measurable_const.mul measurable_subtype_coe)
  have hWm : Measurable W := by
    have e : W = fun g => ∫⁻ h : H, w (g * h) ∂ν := funext hW
    rw [e]
    exact (hwm.comp (measurable_fst.mul (measurable_subtype_coe.comp measurable_snd))).lintegral_prod_right'

  obtain ⟨f, hf⟩ : ∃ f : Set (G ⧸ H) → G → ℝ≥0∞, ∀ s x,
      f s x = s.indicator 1 (QuotientGroup.mk x : G ⧸ H) * (w x * (W x)⁻¹) := ⟨_, fun _ _ => rfl⟩
  have hfm : ∀ s, MeasurableSet s → Measurable (f s) := by
    intro s hs
    have e : f s = fun x => s.indicator 1 (QuotientGroup.mk x : G ⧸ H) * (w x * (W x)⁻¹) :=
      funext (hf s)
    rw [e]
    exact ((measurable_const.indicator hs).comp
      (measurable_quotient_mk'' : Measurable (QuotientGroup.mk : G → G ⧸ H))).mul (hwm.mul hWm.inv)
  have hrec : ∀ (μ : Measure (G ⧸ H)) (m : Measure G),
      (∀ φ : G → ℝ≥0∞, Measurable φ →
        ∫⁻ x, φ x ∂m = ∫⁻ y : G ⧸ H, ∫⁻ h : H, φ (@Quotient.out G (QuotientGroup.leftRel H) y * h) ∂ν ∂μ) →
      ∀ s, MeasurableSet s → μ s = ∫⁻ x, f s x ∂m := by
    intro μ m hm s hs
    rw [hm _ (hfm s hs), ← lintegral_indicator_one hs]
    refine lintegral_congr (fun y => ?_)
    have hy : ∀ h : H, (QuotientGroup.mk (@Quotient.out G (QuotientGroup.leftRel H) y * (h : G)) : G ⧸ H) = y := by
      intro h
      rw [QuotientGroup.mk_mul_of_mem _ h.2]
      exact @Quotient.out_eq G (QuotientGroup.leftRel H) y
    simp only [hf, hy, hWmul]
    rw [lintegral_const_mul _ ((hwc _).mul_const _), lintegral_mul_const _ (hwc _), ← hW,
      ENNReal.mul_inv_cancel (hW0 _) (hWt _), mul_one]

  haveI := hlI; haveI := hlF; haveI := hlI'; haveI := hlF'
  obtain ⟨μG, hμG⟩ : ∃ μG : Measure G, μG = Measure.haar := ⟨_, rfl⟩
  haveI : μG.IsHaarMeasure := by rw [hμG]; infer_instance
  obtain ⟨c, hc1⟩ : ∃ c : NNReal, l = c • μG := ⟨_, Measure.isMulLeftInvariant_eq_smul l μG⟩
  obtain ⟨c', hc2⟩ : ∃ c' : NNReal, l' = c' • μG := ⟨_, Measure.isMulLeftInvariant_eq_smul l' μG⟩
  have e1 : ∀ s, MeasurableSet s → ρ s = (c : ℝ≥0∞) * ∫⁻ x, f s x ∂μG := fun s hs => by
    rw [hrec ρ l hlW s hs, hc1, lintegral_smul_measure]
    rfl
  have e2 : ∀ s, MeasurableSet s → ρ' s = (c' : ℝ≥0∞) * ∫⁻ x, f s x ∂μG := fun s hs => by
    rw [hrec ρ' l' hlW' s hs, hc2, lintegral_smul_measure]
    rfl
  have hc : c ≠ 0 := by
    intro h0
    apply hρ
    refine Measure.ext fun s hs => ?_
    rw [e1 s hs, h0]
    simp
  refine ⟨((c' / c : NNReal) : ℝ≥0∞), Measure.ext fun s hs => ?_⟩
  rw [Measure.smul_apply, e1 s hs, e2 s hs, smul_eq_mul, ← mul_assoc, ← ENNReal.coe_mul,
    div_mul_cancel₀ _ hc]

end PI.QuotMeasUniqW
end
end

namespace PI

theorem wqUnique : PI.WeilQuotMeas.WqUnique :=
  PI.QuotMeasUniqW.wqUnique_of PI.QuotMeasUniqW.qmuWeight PI.QuotMeasUniqW.qmuLift

end PI
