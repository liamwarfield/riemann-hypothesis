module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.ConstCut
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniqueHaarDensityAtIdentity

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UpperDens
open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace GlobalTheory.HaarDensChart

def upperDens {V : Type} [PseudoMetricSpace V] [MeasurableSpace V] (l ν : Measure V) (x : V) : ℝ≥0∞ :=
  limsup (fun r : ℝ => ν (Metric.closedBall x r) / l (Metric.closedBall x r)) (𝓝[>] 0)

end GlobalTheory.HaarDensChart
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasureBallEqLintegralUpperMeasureDensity
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasureBallEqLintegralUpperMeasureDensity
open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace GlobalTheory

theorem measure_ball_eq_lintegral_upperDens : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (l ν : Measure V) [l.IsAddHaarMeasure] [IsFiniteMeasure ν] (η : ℝ) (C : ℝ≥0), (∀ x : V, ‖x‖ < η → GlobalTheory.HaarDensChart.upperDens l ν x < C) → ∀ ρ : ℝ, ρ ≤ η → ν (Metric.ball 0 ρ) = ∫⁻ x in Metric.ball 0 ρ, GlobalTheory.HaarDensChart.upperDens l ν x ∂l := by
  intro V _ _ _ _ _ l ν _ _ η C hC ρ hρ
  set U : Set V := Metric.ball (0 : V) η with hUdef
  have hUo : IsOpen U := Metric.isOpen_ball

  have key : ∀ x ∈ U, ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ν (Metric.closedBall x r) ≤ ((C : ℝ≥0) • l) (Metric.closedBall x r) := by
    intro x hx
    have h0 : limsup (fun r : ℝ => ν (Metric.closedBall x r) / l (Metric.closedBall x r))
        (𝓝[>] (0 : ℝ)) < (C : ℝ≥0∞) := hC x (mem_ball_zero_iff.1 hx)
    filter_upwards [Filter.eventually_lt_of_limsup_lt h0, self_mem_nhdsWithin] with r hr hr0
    have hpos : l (Metric.closedBall x r) ≠ 0 := (Metric.measure_closedBall_pos l x hr0).ne'
    have hfin : l (Metric.closedBall x r) ≠ ⊤ := measure_closedBall_lt_top.ne
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    exact ((ENNReal.div_lt_iff (Or.inl hpos) (Or.inl hfin)).1 hr).le

  have hle : ∀ s ⊆ U, ν s ≤ ((C : ℝ≥0) • l) s := fun s hs =>
    (Besicovitch.vitaliFamily ν).measure_le_of_frequently_le ((C : ℝ≥0) • l)
      Measure.AbsolutelyContinuous.rfl s
      (fun x hx => (Besicovitch.tendsto_filterAt ν x).frequently (key x (hs hx)).frequently)
  have hac : ν.restrict U ≪ l := by
    intro s hs
    rw [Measure.restrict_apply' hUo.measurableSet]
    refine le_antisymm ?_ (by simp)
    calc ν (s ∩ U) ≤ ((C : ℝ≥0) • l) (s ∩ U) := hle _ Set.inter_subset_right
      _ ≤ ((C : ℝ≥0) • l) s := measure_mono Set.inter_subset_left
      _ = 0 := by simp [hs]

  have hae : ∀ᵐ x ∂l, x ∈ U →
      GlobalTheory.HaarDensChart.upperDens l ν x = (ν.restrict U).rnDeriv l x := by
    filter_upwards [Besicovitch.ae_tendsto_rnDeriv (ν.restrict U) l] with x hx hxU
    have hev : (fun r : ℝ => ν.restrict U (Metric.closedBall x r) / l (Metric.closedBall x r))
        =ᶠ[𝓝[>] (0 : ℝ)] (fun r : ℝ => ν (Metric.closedBall x r) / l (Metric.closedBall x r)) := by
      obtain ⟨ε, εpos, hε⟩ := Metric.isOpen_iff.1 hUo x hxU
      filter_upwards [Ioo_mem_nhdsGT εpos] with r hr
      rw [Measure.restrict_eq_self _ ((Metric.closedBall_subset_ball hr.2).trans hε)]
    show limsup (fun r : ℝ => ν (Metric.closedBall x r) / l (Metric.closedBall x r))
        (𝓝[>] (0 : ℝ)) = _
    exact (hx.congr' hev).limsup_eq
  have hsub : Metric.ball (0 : V) ρ ⊆ U := Metric.ball_subset_ball hρ
  calc ν (Metric.ball 0 ρ) = ν.restrict U (Metric.ball 0 ρ) :=
        (Measure.restrict_eq_self _ hsub).symm
    _ = l.withDensity ((ν.restrict U).rnDeriv l) (Metric.ball 0 ρ) := by
        rw [Measure.withDensity_rnDeriv_eq _ _ hac]
    _ = ∫⁻ x in Metric.ball 0 ρ, (ν.restrict U).rnDeriv l x ∂l :=
        withDensity_apply _ Metric.isOpen_ball.measurableSet
    _ = ∫⁻ x in Metric.ball 0 ρ, GlobalTheory.HaarDensChart.upperDens l ν x ∂l := by
        refine setLIntegral_congr_fun_ae Metric.isOpen_ball.measurableSet ?_
        filter_upwards [hae] with x hx hxρ
        exact (hx (hsub hxρ)).symm

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasureBallEqLintegralUpperMeasureDensityStatement
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measure_ball_eq_lintegral_upperMeasureDensity : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (l ν : Measure V) [l.IsAddHaarMeasure] [IsFiniteMeasure ν] (η : ℝ) (C : ℝ≥0), (∀ x : V, ‖x‖ < η → GlobalTheory.HaarDensChart.upperDens l ν x < C) → ∀ ρ : ℝ, ρ ≤ η → ν (Metric.ball 0 ρ) = ∫⁻ x in Metric.ball 0 ρ, GlobalTheory.HaarDensChart.upperDens l ν x ∂l := by
  first | exact @GlobalTheory.measure_ball_eq_lintegral_upperDens | exact GlobalTheory.measure_ball_eq_lintegral_upperDens | (intros; apply GlobalTheory.measure_ball_eq_lintegral_upperDens <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UpperDensityBoundsAlmostHomogeneousMeasure
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UpperDensityBoundsAlmostHomogeneousMeasure
open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace GlobalTheory.UpperDensBounds

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem tendsto_const_mul_nhdsGT {k : ℝ} (hk : 0 < k) :
    Tendsto (fun r : ℝ => k * r) (𝓝[>] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have : Tendsto (fun r : ℝ => k * r) (𝓝 0) (𝓝 (k * 0)) :=
      (continuous_const.mul continuous_id).tendsto 0
    rw [mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with r hr
    exact mul_pos hk hr

theorem ball_scale (l : Measure V) [l.IsAddHaarMeasure] (x : V) {k s : ℝ} (hk : 0 < k) (hs : 0 < s) :
    l (Metric.ball 0 (k * s)) = ENNReal.ofReal (k ^ Module.finrank ℝ V) * l (Metric.closedBall x s) := by
  rw [Measure.addHaar_ball_of_pos l 0 (mul_pos hk hs), Measure.addHaar_closedBall l x hs.le, mul_pow,
    ENNReal.ofReal_mul (by positivity), mul_assoc]

theorem mul_div_scale (t : ℝ) (ht : 0 < t) (d : ℕ) (a b : ℝ≥0∞) :
    ENNReal.ofReal (t ^ d) * (a / (ENNReal.ofReal (t ^ d) * b)) = a / b := by
  have hp : ENNReal.ofReal (t ^ d) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; positivity
  rw [← mul_div_assoc, ENNReal.mul_div_mul_left _ _ hp ENNReal.ofReal_ne_top]

end GlobalTheory.UpperDensBounds


open GlobalTheory.UpperDensBounds in
theorem GlobalTheory.upperDens_bounds_of_almost_homogeneous : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (l ν : Measure V) [l.IsAddHaarMeasure] [IsFiniteMeasure ν] (c : ℝ≥0∞), c ≠ ⊤ → Tendsto (fun r : ℝ => ν (Metric.ball 0 r) / l (Metric.ball 0 r)) (𝓝[>] 0) (𝓝 c) → ∀ ε η : ℝ, 0 < ε → ε < 1 → (∀ x : V, ‖x‖ < η → ∀ᶠ r in 𝓝[>] (0:ℝ), ν (Metric.ball x ((1 - ε) * r)) ≤ ν (Metric.ball 0 r) ∧ ν (Metric.ball 0 r) ≤ ν (Metric.ball x ((1 + ε) * r))) → ∀ x : V, ‖x‖ < η → ENNReal.ofReal ((1 + ε)⁻¹ ^ Module.finrank ℝ V) * c ≤ GlobalTheory.HaarDensChart.upperDens l ν x ∧ GlobalTheory.HaarDensChart.upperDens l ν x ≤ ENNReal.ofReal (((1 + ε) / (1 - ε)) ^ Module.finrank ℝ V) * c := by
  intro V _ _ _ _ _ l ν _ _ c _ hc ε η h0 h1 H x hx
  have he : 0 < 1 - ε := by linarith
  have hp : 0 < 1 + ε := by linarith
  set d := Module.finrank ℝ V
  unfold GlobalTheory.HaarDensChart.upperDens
  constructor
  ·
    set u : ℝ := (1 + ε)⁻¹ with hu
    have hu0 : 0 < u := inv_pos.mpr hp
    have ht : Tendsto (fun s : ℝ => ENNReal.ofReal (u ^ d) *
        (ν (Metric.ball 0 (u * s)) / l (Metric.ball 0 (u * s)))) (𝓝[>] 0) (𝓝 (ENNReal.ofReal (u ^ d) * c)) :=
      ENNReal.Tendsto.const_mul (hc.comp (tendsto_const_mul_nhdsGT hu0)) (Or.inr ENNReal.ofReal_ne_top)
    rw [← ht.limsup_eq]
    refine limsup_le_limsup ?_
    filter_upwards [(tendsto_const_mul_nhdsGT hu0).eventually (H x hx), self_mem_nhdsWithin] with s hs hs0
    have hs0 : 0 < s := hs0
    rw [ball_scale l x hu0 hs0, mul_div_scale u hu0 d]
    refine ENNReal.div_le_div_right ?_ _
    have hr : (1 + ε) * (u * s) = s := by rw [hu, ← mul_assoc, mul_inv_cancel₀ hp.ne', one_mul]
    have := hs.2
    rw [hr] at this
    exact this.trans (measure_mono Metric.ball_subset_closedBall)
  ·
    set t : ℝ := (1 + ε) / (1 - ε) with htdef
    have ht0 : 0 < t := div_pos hp he
    have ht : Tendsto (fun s : ℝ => ENNReal.ofReal (t ^ d) *
        (ν (Metric.ball 0 (t * s)) / l (Metric.ball 0 (t * s)))) (𝓝[>] 0) (𝓝 (ENNReal.ofReal (t ^ d) * c)) :=
      ENNReal.Tendsto.const_mul (hc.comp (tendsto_const_mul_nhdsGT ht0)) (Or.inr ENNReal.ofReal_ne_top)
    rw [← ht.limsup_eq]
    refine limsup_le_limsup ?_
    filter_upwards [(tendsto_const_mul_nhdsGT ht0).eventually (H x hx), self_mem_nhdsWithin] with s hs hs0
    have hs0 : 0 < s := hs0
    rw [ball_scale l x ht0 hs0, mul_div_scale t ht0 d]
    refine ENNReal.div_le_div_right ?_ _
    have hr : (1 - ε) * (t * s) = (1 + ε) * s := by
      rw [htdef, ← mul_assoc, mul_div_cancel₀ _ he.ne']
    refine le_trans (measure_mono (Metric.closedBall_subset_ball ?_)) hs.1
    rw [hr]; nlinarith
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UpperDensityBoundsAlmostHomogeneousMeasureStatement
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.upperDensity_bounds_almost_homogeneous_measure : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (l ν : Measure V) [l.IsAddHaarMeasure] [IsFiniteMeasure ν] (c : ℝ≥0∞), c ≠ ⊤ → Tendsto (fun r : ℝ => ν (Metric.ball 0 r) / l (Metric.ball 0 r)) (𝓝[>] 0) (𝓝 c) → ∀ ε η : ℝ, 0 < ε → ε < 1 → (∀ x : V, ‖x‖ < η → ∀ᶠ r in 𝓝[>] (0:ℝ), ν (Metric.ball x ((1 - ε) * r)) ≤ ν (Metric.ball 0 r) ∧ ν (Metric.ball 0 r) ≤ ν (Metric.ball x ((1 + ε) * r))) → ∀ x : V, ‖x‖ < η → ENNReal.ofReal ((1 + ε)⁻¹ ^ Module.finrank ℝ V) * c ≤ GlobalTheory.HaarDensChart.upperDens l ν x ∧ GlobalTheory.HaarDensChart.upperDens l ν x ≤ ENNReal.ofReal (((1 + ε) / (1 - ε)) ^ Module.finrank ℝ V) * c := by
  first | exact @GlobalTheory.upperDens_bounds_of_almost_homogeneous | exact GlobalTheory.upperDens_bounds_of_almost_homogeneous | (intros; apply GlobalTheory.upperDens_bounds_of_almost_homogeneous <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousAtZeroOfSqueezePowBounds
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousAtZeroOfSqueezePowBounds
open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace GlobalTheory

theorem squeeze_continuousAt_zero (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (d : ℕ)
    (f : V → ℝ≥0∞) (c : ℝ≥0∞) (hc : c ≠ ⊤)
    (h : ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ η : ℝ, 0 < η ∧ ∀ x : V, ‖x‖ < η →
      ENNReal.ofReal ((1 + ε)⁻¹ ^ d) * c ≤ f x ∧ f x ≤ ENNReal.ofReal (((1 + ε) / (1 - ε)) ^ d) * c) :
    f 0 = c ∧ ContinuousAt f 0 := by
  have h1 : Tendsto (fun ε : ℝ => (1 + ε)⁻¹ ^ d) (𝓝 0) (𝓝 1) := by
    have : ContinuousAt (fun ε : ℝ => (1 + ε)⁻¹ ^ d) 0 :=
      ((continuous_const.add continuous_id).continuousAt.inv₀ (by
        change (1 + 0 : ℝ) ≠ 0
        simpa only [add_zero] using (one_ne_zero : (1 : ℝ) ≠ 0))).pow d
    simpa using this.tendsto
  have h2 : Tendsto (fun ε : ℝ => ((1 + ε) / (1 - ε)) ^ d) (𝓝 0) (𝓝 1) := by
    have : ContinuousAt (fun ε : ℝ => ((1 + ε) / (1 - ε)) ^ d) 0 :=
      ((continuous_const.add continuous_id).continuousAt.div
        (continuous_const.sub continuous_id).continuousAt (by
          change (1 - 0 : ℝ) ≠ 0
          simpa only [sub_zero] using (one_ne_zero : (1 : ℝ) ≠ 0))).pow d
    simpa using this.tendsto
  have hL : Tendsto (fun ε : ℝ => ENNReal.ofReal ((1 + ε)⁻¹ ^ d) * c) (𝓝 0) (𝓝 c) := by
    have := ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal h1) (Or.inr hc)
    simpa using this
  have hU : Tendsto (fun ε : ℝ => ENNReal.ofReal (((1 + ε) / (1 - ε)) ^ d) * c) (𝓝 0) (𝓝 c) := by
    have := ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal h2) (Or.inr hc)
    simpa using this
  have hI : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT zero_lt_one
  have hf : Tendsto f (𝓝 0) (𝓝 c) := by
    rw [tendsto_order]
    constructor
    · intro a ha
      have e1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), a < ENNReal.ofReal ((1 + ε)⁻¹ ^ d) * c :=
        nhdsWithin_le_nhds (hL.eventually (lt_mem_nhds ha))
      obtain ⟨ε, hε, hεI⟩ := (e1.and hI).exists
      obtain ⟨η, hη, hx⟩ := h ε hεI.1 hεI.2
      filter_upwards [Metric.ball_mem_nhds (0 : V) hη] with x hxb
      rw [mem_ball_zero_iff] at hxb
      exact lt_of_lt_of_le hε (hx x hxb).1
    · intro a ha
      have e1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ENNReal.ofReal (((1 + ε) / (1 - ε)) ^ d) * c < a :=
        nhdsWithin_le_nhds (hU.eventually (gt_mem_nhds ha))
      obtain ⟨ε, hε, hεI⟩ := (e1.and hI).exists
      obtain ⟨η, hη, hx⟩ := h ε hεI.1 hεI.2
      filter_upwards [Metric.ball_mem_nhds (0 : V) hη] with x hxb
      rw [mem_ball_zero_iff] at hxb
      exact lt_of_le_of_lt (hx x hxb).2 hε
  have h0 : f 0 = c := tendsto_nhds_unique (tendsto_pure_nhds f 0) (hf.mono_left (pure_le_nhds 0))
  refine ⟨h0, ?_⟩
  unfold ContinuousAt
  rw [h0]
  exact hf

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousAtZeroOfSqueezePowBoundsStatement
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuousAt_zero_of_squeeze_pow_bounds : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (d : ℕ) (f : V → ℝ≥0∞) (c : ℝ≥0∞), c ≠ ⊤ → (∀ ε : ℝ, 0 < ε → ε < 1 → ∃ η : ℝ, 0 < η ∧ ∀ x : V, ‖x‖ < η → ENNReal.ofReal ((1 + ε)⁻¹ ^ d) * c ≤ f x ∧ f x ≤ ENNReal.ofReal (((1 + ε) / (1 - ε)) ^ d) * c) → f 0 = c ∧ ContinuousAt f 0 := by
  first | exact @GlobalTheory.squeeze_continuousAt_zero | exact GlobalTheory.squeeze_continuousAt_zero | (intros; apply GlobalTheory.squeeze_continuousAt_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarUnitaryGroupWbDensityChart
open MeasureTheory Filter Topology Matrix
open scoped ENNReal NNReal

namespace GlobalTheory.HaarDensChart

open PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.HU

variable {k r : ℕ}

instance : LocallyCompactSpace (Gp k r) :=
  (amb_closed (k := k) (r := r)).isClosedEmbedding_subtypeVal.locallyCompactSpace

theorem isMatGroup_uwb : PI.IsMatGroup (UWb k r) :=
  ⟨amb_closed, uwb_one, fun _ ha _ hb => uwb_mul ha hb, fun a ha => ⟨uwb_inv ha, Matrix.mul_nonsing_inv _ (uwb_unit ha)⟩⟩

theorem exists_haarOn (k r : ℕ) : ∃ νh : Measure (Mt k r), IsHaarOn (UWb k r) νh := by
  let μ : Measure (Gp k r) := Measure.haar
  refine ⟨μ.map inc, inc_memb.sigmaFinite_map, ?_, ?_, fun s hs => ?_⟩
  · intro h
    have := congrArg (fun m : Measure (Mt k r) => m Set.univ) h
    simp only [inc_memb.map_apply, Set.preimage_univ, Measure.coe_zero, Pi.zero_apply] at this
    exact (IsOpen.measure_pos μ isOpen_univ Set.univ_nonempty).ne' this
  · rw [inc_memb.map_apply]
    have : (inc : Gp k r → Mt k r) ⁻¹' {x | Matrix.of x ∉ UWb k r} = ∅ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
      exact inc_mem x
    rw [this, measure_empty]
  · let a : Gp k r := ⟨s, hs⟩
    rw [Measure.map_map (lmulM_cont s).measurable inc_memb.measurable]
    have : lmulM s ∘ (inc : Gp k r → Mt k r) = inc ∘ fun x => a * x := by
      funext x; rfl
    rw [this, ← Measure.map_map inc_memb.measurable (measurable_const_mul a), map_mul_left_eq_self]

end GlobalTheory.HaarDensChart

namespace GlobalTheory.HaarDensChart

open PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.HU GlobalTheory.MatHaarDensity

theorem haarDens : HaarDens := by
  intro k r hk
  obtain ⟨νh, hνh⟩ := exists_haarOn k r
  have hS : PI.IsMatGroup (UWb k r) := isMatGroup_uwb
  have hμ : PI.IsHaarOnM (UWb k r) νh := hνh
  obtain ⟨hlie, hsurj⟩ := GlobalTheory.T.closed_matrix_subgroup_theorem _ (UWb k r) hS
  obtain ⟨-, hcpt, hop⟩ := GlobalTheory.MatHaar.haar_unique_locFinite_openPos _ (UWb k r) νh hS hμ
  have hmem : ∀ X, expL (UWb k r) X ∈ UWb k r := fun X => by simpa [expL] using hlie X 1
  have hsurj' : ∀ ρ : ℝ, 0 < ρ → ∃ δ : ℝ, 0 < δ ∧ ∀ g ∈ UWb k r, (∀ i j, ‖(g - 1) i j‖ < δ) →
      ∃ X : lieE (UWb k r), ‖X‖ < ρ ∧ expL (UWb k r) X = g := by
    intro ρ hρ
    obtain ⟨δ, hδ, h⟩ := hsurj ρ hρ
    refine ⟨δ, hδ, fun g hg hg' => ?_⟩
    obtain ⟨X, hX, e⟩ := h g hg hg'
    exact ⟨X, mem_ball_zero_iff.1 hX, e⟩
  obtain ⟨δ₀, hδ₀, hi⟩ := exists_injOn (UWb k r)
  let φ : lieE (UWb k r) → Mt k r := expC k r
  have hc : Continuous φ := continuous_expL (UWb k r)
  have hi' : Set.InjOn φ (Metric.ball 0 δ₀) := fun X hX Y hY h => hi hX hY h
  have hψ : MeasurableEmbedding ((Metric.ball (0 : lieE (UWb k r)) δ₀).restrict φ) :=
    hc.continuousOn.measurableEmbedding Metric.isOpen_ball.measurableSet hi'
  let ν : Measure (lieE (UWb k r)) := (νh.comap ((Metric.ball (0 : lieE (UWb k r)) δ₀).restrict φ)).map Subtype.val
  have hν : ∀ A : Set (lieE (UWb k r)), MeasurableSet A → ν A = νh (φ '' (A ∩ Metric.ball 0 δ₀)) := by
    intro A hA
    simp only [ν]
    rw [Measure.map_apply measurable_subtype_coe hA, hψ.comap_apply]
    congr 1
    rw [Set.inter_comm, ← Subtype.image_preimage_coe, Set.image_image]
    rfl
  have hνb : ∀ (x : lieE (UWb k r)) (ρ : ℝ), ‖x‖ + ρ ≤ δ₀ → ν (Metric.ball x ρ) = νh (φ '' Metric.ball x ρ) := by
    intro x ρ h
    rw [hν _ Metric.isOpen_ball.measurableSet, Set.inter_eq_left.2]
    exact Metric.ball_subset_ball' (by simpa [add_comm] using h)
  have hfin : νh (φ '' Metric.ball 0 δ₀) < ⊤ :=
    lt_of_le_of_lt (measure_mono (Set.image_mono Metric.ball_subset_closedBall))
      (hcpt _ ((isCompact_closedBall (0 : lieE (UWb k r)) δ₀).image hc) (by
        rintro _ ⟨X, -, rfl⟩
        exact hmem X))
  haveI : IsFiniteMeasure ν := ⟨by
    rw [hν _ MeasurableSet.univ, Set.univ_inter]
    exact hfin⟩
  have hposh : ∀ ρ : ℝ, 0 < ρ → νh (φ '' Metric.ball 0 ρ) ≠ 0 := by
    intro ρ hr h
    obtain ⟨η, hη, H⟩ := hsurj ρ hr
    have hp := hop {g | ∀ i j, ‖(Matrix.of g - 1) i j‖ < η} (isOpen_near_one η)
      ⟨Matrix.of.symm 1, by intro i j; simpa using hη, hS.2.1⟩
    refine hp.ne' (measure_mono_null (fun g hg => ?_) (measure_union_null h hνh.2.2.1))
    by_cases hgS : Matrix.of g ∈ UWb k r
    · exact Or.inl (H _ hgS hg)
    · exact Or.inr hgS
  have hpos : ∀ ρ : ℝ, 0 < ρ → ν (Metric.ball 0 ρ) ≠ 0 := by
    intro ρ hr
    rw [hν _ Metric.isOpen_ball.measurableSet]
    intro h
    refine hposh (min ρ δ₀) (lt_min hr hδ₀) (measure_mono_null (Set.image_mono ?_) h)
    exact Set.subset_inter (Metric.ball_subset_ball (min_le_left _ _)) (Metric.ball_subset_ball (min_le_right _ _))
  have hsν : ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ η : ℝ, 0 < η ∧ ∀ x : lieE (UWb k r), ‖x‖ < η →
      ∀ᶠ ρ in 𝓝[>] (0:ℝ), ν (Metric.ball x ((1 - ε) * ρ)) ≤ ν (Metric.ball 0 ρ) ∧
        ν (Metric.ball 0 ρ) ≤ ν (Metric.ball x ((1 + ε) * ρ)) := by
    intro ε h0 h1
    obtain ⟨η, hη, H⟩ := sandwich (UWb k r) hS hmem hsurj' ε h0 h1
    refine ⟨min η (δ₀ / 2), lt_min hη (by linarith), fun x hx => ?_⟩
    have hx1 : ‖x‖ < η := hx.trans_le (min_le_left _ _)
    have hx2 : ‖x‖ < δ₀ / 2 := hx.trans_le (min_le_right _ _)
    obtain ⟨hiS, hi1⟩ := hS.2.2.2 _ (hmem x)
    have hi2 : (expL (UWb k r) x)⁻¹ * expL (UWb k r) x = 1 := mul_eq_one_comm.1 hi1
    have hτ : Continuous (lmulM (expL (UWb k r) x)⁻¹ : Mt k r → Mt k r) := lmulM_cont _
    have hτμ : νh.map (lmulM (expL (UWb k r) x)⁻¹) = νh := hνh.2.2.2 _ hiS
    filter_upwards [H x hx1, Ioo_mem_nhdsGT (show (0:ℝ) < δ₀ / 4 by linarith)] with ρ hr hr'
    obtain ⟨hr0, hr1⟩ := hr'
    have hm : MeasurableSet (φ '' Metric.ball 0 ρ) :=
      Metric.isOpen_ball.measurableSet.image_of_continuousOn_injOn hc.continuousOn
        (hi'.mono (Metric.ball_subset_ball (by linarith)))
    have hinv : νh (φ '' Metric.ball 0 ρ) =
        νh ((lmulM (expL (UWb k r) x)⁻¹ : Mt k r → Mt k r) ⁻¹' (φ '' Metric.ball 0 ρ)) := by
      rw [← Measure.map_apply hτ.measurable hm, hτμ]
    have hA : φ '' Metric.ball x ((1 - ε) * ρ) ⊆
        (lmulM (expL (UWb k r) x)⁻¹ : Mt k r → Mt k r) ⁻¹' (φ '' Metric.ball 0 ρ) := by
      rintro _ ⟨Y, hY, rfl⟩
      obtain ⟨Z, hZ, e⟩ := hr.1 Y (mem_ball_iff_norm.1 hY)
      refine ⟨Z, mem_ball_zero_iff.2 hZ, ?_⟩
      change expL (UWb k r) Z = (expL (UWb k r) x)⁻¹ * expL (UWb k r) Y
      rw [e, ← Matrix.mul_assoc, hi2, Matrix.one_mul]
    have hB : (lmulM (expL (UWb k r) x)⁻¹ : Mt k r → Mt k r) ⁻¹' (φ '' Metric.ball 0 ρ) ⊆
        φ '' Metric.ball x ((1 + ε) * ρ) := by
      rintro g ⟨Z, hZ, e⟩
      obtain ⟨Y, hY, e'⟩ := hr.2 Z (mem_ball_zero_iff.1 hZ)
      refine ⟨Y, mem_ball_iff_norm.2 hY, ?_⟩
      change expL (UWb k r) Z = (expL (UWb k r) x)⁻¹ * Matrix.of g at e
      change expL (UWb k r) Y = Matrix.of g
      rw [e', e, ← Matrix.mul_assoc, hi1, Matrix.one_mul]
    rw [hνb x _ (by nlinarith), hνb x _ (by nlinarith), hνb 0 ρ (by simp; linarith), hinv]
    exact ⟨measure_mono hA, measure_mono hB⟩
  obtain ⟨c, hc0, hct, hlim⟩ :=
    GlobalTheory.exists_density_origin_of_almost_homogeneous (lieE (UWb k r)) volume ν hpos hsν
  have hb : ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ η : ℝ, 0 < η ∧ ∀ x : lieE (UWb k r), ‖x‖ < η →
      ENNReal.ofReal ((1 + ε)⁻¹ ^ Module.finrank ℝ (lieE (UWb k r))) * c ≤ upperDens volume ν x ∧
        upperDens volume ν x ≤ ENNReal.ofReal (((1 + ε) / (1 - ε)) ^ Module.finrank ℝ (lieE (UWb k r))) * c := by
    intro ε h0 h1
    obtain ⟨η, hη, H⟩ := hsν ε h0 h1
    exact ⟨η, hη, GlobalTheory.T.upperDensity_bounds_almost_homogeneous_measure _ volume ν c hct hlim ε η h0 h1 H⟩
  obtain ⟨hδ0, hδc⟩ := GlobalTheory.T.continuousAt_zero_of_squeeze_pow_bounds _ _ (upperDens volume ν) c hct hb
  obtain ⟨η₀, hη₀, H₀⟩ := hb (1 / 2) (by norm_num) (by norm_num)
  set a := ENNReal.ofReal (((1 + 1 / 2) / (1 - 1 / 2)) ^ Module.finrank ℝ (lieE (UWb k r)) : ℝ) * c with ha
  have hne : a ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hct
  have hC : ∀ x : lieE (UWb k r), ‖x‖ < η₀ → upperDens volume ν x < ((a.toNNReal + 1 : ℝ≥0) : ℝ≥0∞) := by
    intro x hx
    refine lt_of_le_of_lt (H₀ x hx).2 ?_
    have h := ENNReal.coe_lt_coe.2 (lt_add_one a.toNNReal)
    rwa [ENNReal.coe_toNNReal hne] at h
  refine ⟨νh, hνh, upperDens volume ν, hδc, by rw [hδ0]; exact hc0, by rw [hδ0]; exact hct,
    min η₀ δ₀, lt_min hη₀ hδ₀, fun ρ hρ hρε => ?_⟩
  have e1 : νh (bBall k r ρ) = ν (Metric.ball 0 ρ) := by
    rw [hν _ Metric.isOpen_ball.measurableSet,
      Set.inter_eq_left.2 (Metric.ball_subset_ball (hρε.le.trans (min_le_right _ _)))]
    rfl
  rw [e1]
  exact GlobalTheory.T.measure_ball_eq_lintegral_upperMeasureDensity _ volume ν η₀ _ hC ρ (hρε.le.trans (min_le_left _ _))

end GlobalTheory.HaarDensChart
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarUnitaryGroupWbDensityChartStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_unitaryGroupWb_density_chart : PI.RhsWLim.W.HaarDens := by
  first | exact @GlobalTheory.HaarDensChart.haarDens | exact GlobalTheory.HaarDensChart.haarDens | (intros; apply GlobalTheory.HaarDensChart.haarDens <;> assumption)
end
