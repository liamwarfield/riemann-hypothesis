module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaugeMeasureMatrixAlgebraSubgroupLocalAsymptotic

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TendstoRescaledMeasureGaugeUnitBody
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TendstoRescaledMeasureGaugeUnitBody
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst
open scoped Pointwise

noncomputable section

namespace GlobalTheory.IwConst.VagBody

theorem integral_squeeze {X : Type} [MeasurableSpace X] (ν : Measure X) (φ : X → ℝ) (A B : Set X)
    (hφ : Measurable φ) (hA : MeasurableSet A) (hB : MeasurableSet B) (hB' : ν B ≠ ⊤)
    (h0 : ∀ x, 0 ≤ φ x) (h1 : ∀ x, φ x ≤ 1) (hA1 : ∀ x ∈ A, φ x = 1) (hB0 : ∀ x, x ∉ B → φ x = 0) :
    ν.real A ≤ ∫ x, φ x ∂ν ∧ ∫ x, φ x ∂ν ≤ ν.real B := by
  have hsub : A ⊆ B := by
    intro x hx
    by_contra hxB
    have h := hA1 x hx
    rw [hB0 x hxB] at h
    exact zero_ne_one h
  have hA' : ν A ≠ ⊤ := ne_top_of_le_ne_top hB' (measure_mono hsub)
  have lo : ∀ x, A.indicator (fun _ => (1:ℝ)) x ≤ φ x := by
    intro x
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx, hA1 x hx]
    · simp only [Set.indicator, hx, if_false]
      exact h0 x
  have hi : ∀ x, φ x ≤ B.indicator (fun _ => (1:ℝ)) x := by
    intro x
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx]
      exact h1 x
    · simp only [Set.indicator, hx, if_false]
      exact le_of_eq (hB0 x hx)
  have iB : Integrable (B.indicator fun _ => (1:ℝ)) ν :=
    (integrable_indicator_iff hB).2 (integrableOn_const hB')
  have iA : Integrable (A.indicator fun _ => (1:ℝ)) ν :=
    (integrable_indicator_iff hA).2 (integrableOn_const hA')
  have iφ : Integrable φ ν := by
    refine iB.mono' hφ.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (h0 x)]
    exact hi x
  have eA : ∫ x, A.indicator (fun _ => (1:ℝ)) x ∂ν = ν.real A := by
    rw [integral_indicator_const _ hA, smul_eq_mul, mul_one]
  have eB : ∫ x, B.indicator (fun _ => (1:ℝ)) x ∂ν = ν.real B := by
    rw [integral_indicator_const _ hB, smul_eq_mul, mul_one]
  refine ⟨?_, ?_⟩
  · rw [← eA]
    exact integral_mono iA iφ lo
  · rw [← eB]
    exact integral_mono iφ iB hi

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

theorem isCompact_body (ρ : V → ℝ) (hc : Continuous ρ) (h0 : ∀ v, 0 ≤ ρ v)
    (hs : ∀ s : ℝ, 0 ≤ s → ∀ v, ρ (s • v) = s * ρ v) (hd : ∀ v, ρ v = 0 → v = 0) (t : ℝ) :
    IsCompact {v | ρ v ≤ t} := by
  obtain ⟨m, hm, hmρ⟩ : ∃ m : ℝ, 0 < m ∧ ∀ u ∈ Metric.sphere (0 : V) 1, m ≤ ρ u := by
    rcases (Metric.sphere (0 : V) 1).eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, by simp [he]⟩
    · obtain ⟨u0, hu0, hmin⟩ := (isCompact_sphere (0 : V) 1).exists_isMinOn hne hc.continuousOn
      refine ⟨ρ u0, ?_, fun u hu => isMinOn_iff.1 hmin u hu⟩
      rcases (h0 u0).lt_or_eq with h | h
      · exact h
      · exfalso
        have hz : u0 = 0 := hd u0 h.symm
        rw [mem_sphere_zero_iff_norm, hz, norm_zero] at hu0
        exact zero_ne_one hu0
  have hbd : ∀ v, m * ‖v‖ ≤ ρ v := by
    intro v
    by_cases hv : v = 0
    · rw [hv, norm_zero, mul_zero]
      exact h0 0
    · have hn : 0 < ‖v‖ := norm_pos_iff.2 hv
      have hu : ‖v‖⁻¹ • v ∈ Metric.sphere (0 : V) 1 := by
        rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
      have h1 := hmρ _ hu
      have h2 : ρ v = ‖v‖ * ρ (‖v‖⁻¹ • v) := by
        rw [← hs ‖v‖ (norm_nonneg v), smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
      rw [h2]
      nlinarith
  refine Metric.isCompact_of_isClosed_isBounded (isClosed_le hc continuous_const) ?_
  refine (Metric.isBounded_closedBall (x := (0 : V)) (r := t / m)).subset ?_
  intro v hv
  rw [Metric.mem_closedBall, dist_zero_right, le_div_iff₀ hm]
  have h3 := hbd v
  have h4 : ρ v ≤ t := hv
  nlinarith


omit [FiniteDimensional ℝ V] in
theorem body_eq_smul (ρ : V → ℝ) (hs : ∀ s : ℝ, 0 ≤ s → ∀ v, ρ (s • v) = s * ρ v) {t : ℝ} (ht : 0 < t) :
    {v | ρ v ≤ t} = t • {v | ρ v ≤ 1} := by
  ext v
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ ht.ne', Set.mem_setOf_eq, Set.mem_setOf_eq,
    hs _ (inv_nonneg.2 ht.le), inv_mul_le_iff₀ ht, mul_one]


omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
theorem exists_cutoff (ρ : V → ℝ) (hc : Continuous ρ) {s t : ℝ} (hst : s < t) :
    ∃ φ : V → ℝ, Continuous φ ∧ (∀ x, 0 ≤ φ x) ∧ (∀ x, φ x ≤ 1) ∧ (∀ x, ρ x ≤ s → φ x = 1) ∧
      ∀ x, ¬ ρ x ≤ t → φ x = 0 := by
  have hpos : 0 < t - s := sub_pos.2 hst
  refine ⟨fun x => max 0 (min 1 ((t - ρ x) / (t - s))), ?_, ?_, ?_, ?_, ?_⟩
  · exact continuous_const.max (continuous_const.min ((continuous_const.sub hc).div_const _))
  · intro x
    exact le_max_left _ _
  · intro x
    exact max_le zero_le_one (min_le_left _ _)
  · intro x hx
    have h1 : 1 ≤ (t - ρ x) / (t - s) := by
      rw [le_div_iff₀ hpos]
      linarith
    show max 0 (min 1 ((t - ρ x) / (t - s))) = 1
    rw [min_eq_left h1, max_eq_right zero_le_one]
  · intro x hx
    have h1 : (t - ρ x) / (t - s) ≤ 0 := by
      rw [div_le_iff₀ hpos]
      push_neg at hx
      linarith
    show max 0 (min 1 ((t - ρ x) / (t - s))) = 0
    exact max_eq_left (le_trans (min_le_right _ _) h1)

theorem tendsto_body : ∀ (α V : Type) [MeasurableSpace α] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure α) [IsFiniteMeasure μ] (c : α → V) (lam : Measure V) [lam.IsAddHaarMeasure] (d : ℕ) (ρ : V → ℝ), Measurable c → Continuous ρ → (∀ v, 0 ≤ ρ v) → (∀ (s : ℝ), 0 ≤ s → ∀ v, ρ (s • v) = s * ρ v) → (∀ v, ρ v = 0 → v = 0) → Vag μ c lam d → Filter.Tendsto (fun r : ℝ => μ {g | ρ (c g) ≤ r} / ENNReal.ofReal (r ^ d)) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (lam {v | ρ v ≤ 1})) := by
  intro α V _ _ _ _ _ _ μ _ c lam _ d ρ hcm hρ h0 hs hd hv
  have hK : ∀ t, IsCompact {v | ρ v ≤ t} := fun t => isCompact_body ρ hρ h0 hs hd t
  have hfin : ∀ t, lam {v | ρ v ≤ t} ≠ ⊤ := fun t => (hK t).measure_lt_top.ne
  have hmV : ∀ t, MeasurableSet {v | ρ v ≤ t} := fun t =>
    measurableSet_le hρ.measurable measurable_const
  have hmα : ∀ t, MeasurableSet {g | ρ (c g) ≤ t} := fun t =>
    measurableSet_le (hρ.measurable.comp hcm) measurable_const
  have hmβ : ∀ r t : ℝ, MeasurableSet {g | ρ (r • c g) ≤ t} := fun r t =>
    measurableSet_le (hρ.measurable.comp (hcm.const_smul r)) measurable_const
  have hhom : ∀ r : ℝ, 0 < r → ∀ v, ρ (r⁻¹ • v) = r⁻¹ * ρ v := fun r hr v =>
    hs _ (inv_nonneg.2 hr.le) v
  have hscale : ∀ x : ℝ, 0 < x →
      lam.real {v | ρ v ≤ x} = x ^ Module.finrank ℝ V * lam.real {v | ρ v ≤ 1} := by
    intro x hx
    simp only [measureReal_def]
    rw [body_eq_smul ρ hs hx, Measure.addHaar_smul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity), abs_of_pos (pow_pos hx _)]
  have hcont : Filter.Tendsto (fun x : ℝ => x ^ Module.finrank ℝ V * lam.real {v | ρ v ≤ 1})
      (nhds 1) (nhds (lam.real {v | ρ v ≤ 1})) := by
    have h : Filter.Tendsto (fun x : ℝ => x ^ Module.finrank ℝ V * lam.real {v | ρ v ≤ 1})
        (nhds 1) (nhds ((1 : ℝ) ^ Module.finrank ℝ V * lam.real {v | ρ v ≤ 1})) :=
      ((continuous_pow _).mul continuous_const).tendsto 1
    rwa [one_pow, one_mul] at h
  have up : ∀ a, lam.real {v | ρ v ≤ 1} < a → ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (r ^ d)⁻¹ * μ.real {g | ρ (c g) ≤ r} < a := by
    intro a ha
    have h2 := hcont.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 1))
    obtain ⟨x, hxa, hx⟩ := ((h2.eventually (gt_mem_nhds ha)).and (Ioo_mem_nhdsGT one_lt_two)).exists
    obtain ⟨φ, hφc, hφ0, hφ1, hφA, hφB⟩ := exists_cutoff ρ hρ hx.1
    have hsupp : HasCompactSupport φ := HasCompactSupport.intro (hK x) (fun v hv' => hφB v hv')
    have hlim : ∫ v, φ v ∂lam < a := by
      have h3 := (integral_squeeze lam φ _ _ hφc.measurable (hmV 1) (hmV x) (hfin x) hφ0 hφ1
        hφA hφB).2
      have h4 := hscale x (by linarith [hx.1])
      linarith
    filter_upwards [(hv φ hφc hsupp).eventually (gt_mem_nhds hlim), self_mem_nhdsWithin] with r hr hr0
    have hr0' : 0 < r := hr0
    have hsq := (integral_squeeze μ (fun g => φ (r⁻¹ • c g)) _ _
      (hφc.measurable.comp (hcm.const_smul r⁻¹)) (hmα r) (hmβ r⁻¹ x) (measure_ne_top _ _)
      (fun g => hφ0 _) (fun g => hφ1 _)
      (fun g hg => hφA _ (by rw [hhom r hr0', inv_mul_le_iff₀ hr0', mul_one]; exact hg))
      (fun g hg => hφB _ hg)).1
    calc (r ^ d)⁻¹ * μ.real {g | ρ (c g) ≤ r}
        ≤ (r ^ d)⁻¹ * ∫ g, φ (r⁻¹ • c g) ∂μ :=
          mul_le_mul_of_nonneg_left hsq (inv_nonneg.2 (pow_nonneg hr0'.le d))
      _ < a := hr
  have lo : ∀ a, a < lam.real {v | ρ v ≤ 1} → ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      a < (r ^ d)⁻¹ * μ.real {g | ρ (c g) ≤ r} := by
    intro a ha
    have h2 := hcont.mono_left (nhdsWithin_le_nhds (s := Set.Iio 1))
    obtain ⟨x, hxa, hx⟩ := ((h2.eventually (lt_mem_nhds ha)).and (Ioo_mem_nhdsLT zero_lt_one)).exists
    obtain ⟨φ, hφc, hφ0, hφ1, hφA, hφB⟩ := exists_cutoff ρ hρ hx.2
    have hsupp : HasCompactSupport φ := HasCompactSupport.intro (hK 1) (fun v hv' => hφB v hv')
    have hlim : a < ∫ v, φ v ∂lam := by
      have h3 := (integral_squeeze lam φ _ _ hφc.measurable (hmV x) (hmV 1) (hfin 1) hφ0 hφ1
        hφA hφB).1
      have h4 := hscale x hx.1
      linarith
    filter_upwards [(hv φ hφc hsupp).eventually (lt_mem_nhds hlim), self_mem_nhdsWithin] with r hr hr0
    have hr0' : 0 < r := hr0
    have hsq := (integral_squeeze μ (fun g => φ (r⁻¹ • c g)) _ _
      (hφc.measurable.comp (hcm.const_smul r⁻¹)) (hmβ r⁻¹ x) (hmα r) (measure_ne_top _ _)
      (fun g => hφ0 _) (fun g => hφ1 _) (fun g hg => hφA _ hg)
      (fun g hg => hφB _ (by rw [hhom r hr0', inv_mul_le_iff₀ hr0', mul_one]; exact hg))).2
    calc a < (r ^ d)⁻¹ * ∫ g, φ (r⁻¹ • c g) ∂μ := hr
      _ ≤ (r ^ d)⁻¹ * μ.real {g | ρ (c g) ≤ r} :=
          mul_le_mul_of_nonneg_left hsq (inv_nonneg.2 (pow_nonneg hr0'.le d))
  have hreal : Filter.Tendsto (fun r : ℝ => (r ^ d)⁻¹ * μ.real {g | ρ (c g) ≤ r})
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (lam.real {v | ρ v ≤ 1})) :=
    tendsto_order.2 ⟨lo, up⟩
  have h5 := ENNReal.tendsto_ofReal hreal
  rw [measureReal_def, ENNReal.ofReal_toReal (hfin 1)] at h5
  refine h5.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr0 : 0 < r := hr
  have hp : 0 < r ^ d := pow_pos hr0 d
  rw [measureReal_def, ENNReal.ofReal_mul (inv_nonneg.2 hp.le),
    ENNReal.ofReal_toReal (measure_ne_top _ _), div_eq_mul_inv, ENNReal.ofReal_inv_of_pos hp, mul_comm]

end GlobalTheory.IwConst.VagBody
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TendstoRescaledMeasureGaugeUnitBodyStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_rescaled_measure_gauge_unit_body : ∀ (α V : Type) [MeasurableSpace α] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure α) [IsFiniteMeasure μ] (c : α → V) (lam : Measure V) [lam.IsAddHaarMeasure] (d : ℕ) (ρ : V → ℝ), Measurable c → Continuous ρ → (∀ v, 0 ≤ ρ v) → (∀ (s : ℝ), 0 ≤ s → ∀ v, ρ (s • v) = s * ρ v) → (∀ v, ρ v = 0 → v = 0) → Vag μ c lam d → Filter.Tendsto (fun r : ℝ => μ {g | ρ (c g) ≤ r} / ENNReal.ofReal (r ^ d)) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (lam {v | ρ v ≤ 1})) := by
  first | exact @GlobalTheory.IwConst.VagBody.tendsto_body | exact GlobalTheory.IwConst.VagBody.tendsto_body | (intros; apply GlobalTheory.IwConst.VagBody.tendsto_body <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.VagueLimitRescaledMeasuresProd
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.VagueLimitRescaledMeasuresProd
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

noncomputable section

namespace GlobalTheory.IwConst

open Filter Topology

def prodFns (V W : Type) [TopologicalSpace V] [TopologicalSpace W] : Submonoid C(V × W, ℝ) where
  carrier := {g | ∃ a : C(V, ℝ), ∃ b : C(W, ℝ), ∀ z, g z = a z.1 * b z.2}
  one_mem' := ⟨1, 1, fun z => by simp⟩
  mul_mem' := by
    rintro g h ⟨a, b, hg⟩ ⟨a', b', hh⟩
    exact ⟨a * a', b * b', fun z => by simp [hg, hh]; ring⟩

theorem prodFns_separates (V W : Type) [MetricSpace V] [MetricSpace W] :
    (Algebra.adjoin ℝ (prodFns V W : Set C(V × W, ℝ))).SeparatesPoints := by
  intro p q hpq
  by_cases h1 : p.1 = q.1
  · have h2 : p.2 ≠ q.2 := fun h => hpq (Prod.ext h1 h)
    let g : C(V × W, ℝ) := ⟨fun z => dist z.2 q.2, by fun_prop⟩
    have hg : g ∈ (prodFns V W : Set C(V × W, ℝ)) := by
      show ∃ a : C(V, ℝ), ∃ b : C(W, ℝ), ∀ z, g z = a z.1 * b z.2
      exact ⟨1, ⟨fun y => dist y q.2, by fun_prop⟩, fun z => by simp [g]⟩
    refine ⟨g, ⟨g, Algebra.subset_adjoin hg, rfl⟩, ?_⟩
    simpa [g] using h2
  · let g : C(V × W, ℝ) := ⟨fun z => dist z.1 q.1, by fun_prop⟩
    have hg : g ∈ (prodFns V W : Set C(V × W, ℝ)) := by
      show ∃ a : C(V, ℝ), ∃ b : C(W, ℝ), ∀ z, g z = a z.1 * b z.2
      exact ⟨⟨fun x => dist x q.1, by fun_prop⟩, 1, fun z => by simp [g]⟩
    refine ⟨g, ⟨g, Algebra.subset_adjoin hg, rfl⟩, ?_⟩
    simpa [g] using h1

theorem hasCompactSupport_prod_mul {V W : Type} [MetricSpace V] [MetricSpace W] {a : V → ℝ} {b : W → ℝ}
    (ha : HasCompactSupport a) (hb : HasCompactSupport b) :
    HasCompactSupport (fun z : V × W => a z.1 * b z.2) := by
  refine HasCompactSupport.intro (ha.isCompact.prod hb.isCompact) fun z hz => ?_
  rcases not_and_or.mp (show ¬(z.1 ∈ tsupport a ∧ z.2 ∈ tsupport b) from hz) with h | h
  · simp [image_eq_zero_of_notMem_tsupport h]
  · simp [image_eq_zero_of_notMem_tsupport h]

theorem tendsto_integral_of_prod {ι V W : Type} [MetricSpace V] [MetricSpace W] [ProperSpace V] [ProperSpace W]
    [MeasurableSpace V] [BorelSpace V] [MeasurableSpace W] [BorelSpace W] (l : Filter ι)
    (M : ι → Measure (V × W)) (M₀ : Measure (V × W)) [∀ i, IsFiniteMeasureOnCompacts (M i)]
    [IsFiniteMeasureOnCompacts M₀]
    (h : ∀ (a : V → ℝ) (b : W → ℝ), Continuous a → HasCompactSupport a → Continuous b → HasCompactSupport b →
      Tendsto (fun i => ∫ z, a z.1 * b z.2 ∂M i) l (𝓝 (∫ z, a z.1 * b z.2 ∂M₀)))
    (F : V × W → ℝ) (hF : Continuous F) (hFc : HasCompactSupport F) :
    Tendsto (fun i => ∫ z, F z ∂M i) l (𝓝 (∫ z, F z ∂M₀)) := by
  have hKc : IsCompact (tsupport F) := hFc
  obtain ⟨χ₁, h1K, -, h1c, h1b⟩ := exists_continuous_one_zero_of_isCompact
    (hKc.image continuous_fst) isClosed_empty (Set.disjoint_empty _)
  obtain ⟨χ₂, h2K, -, h2c, h2b⟩ := exists_continuous_one_zero_of_isCompact
    (hKc.image continuous_snd) isClosed_empty (Set.disjoint_empty _)
  set χ : V × W → ℝ := fun z => χ₁ z.1 * χ₂ z.2 with hχ
  have hχc : Continuous χ := (χ₁.continuous.comp continuous_fst).mul (χ₂.continuous.comp continuous_snd)
  have hχs : HasCompactSupport χ := hasCompactSupport_prod_mul h1c h2c
  have hχ0 : ∀ z, 0 ≤ χ z := fun z => mul_nonneg (h1b _).1 (h2b _).1
  have hχF : ∀ z, χ z * F z = F z := by
    intro z
    by_cases hz : z ∈ tsupport F
    · have e1 : χ₁ z.1 = 1 := by simpa using h1K ⟨z, hz, rfl⟩
      have e2 : χ₂ z.2 = 1 := by simpa using h2K ⟨z, hz, rfl⟩
      simp [hχ, e1, e2]
    · simp [image_eq_zero_of_notMem_tsupport hz]
  have hX : IsCompact (tsupport χ₁ ×ˢ tsupport χ₂) := h1c.isCompact.prod h2c.isCompact
  have hχX : ∀ z, z ∉ tsupport χ₁ ×ˢ tsupport χ₂ → χ z = 0 := by
    intro z hz
    rcases not_and_or.mp (show ¬(z.1 ∈ tsupport χ₁ ∧ z.2 ∈ tsupport χ₂) from hz) with h | h
    · simp [hχ, image_eq_zero_of_notMem_tsupport h]
    · simp [hχ, image_eq_zero_of_notMem_tsupport h]
  have hint : ∀ (G : C(V × W, ℝ)) (m : Measure (V × W)) [IsFiniteMeasureOnCompacts m],
      Integrable (fun z => χ z * G z) m := fun G m _ =>
    (hχc.mul G.continuous).integrable_of_hasCompactSupport (hχs.mul_right (f' := G))
  have key : ∀ G ∈ Algebra.adjoin ℝ (prodFns V W : Set C(V × W, ℝ)),
      Tendsto (fun i => ∫ z, χ z * G z ∂M i) l (𝓝 (∫ z, χ z * G z ∂M₀)) := by
    intro G hG
    have hG' : G ∈ Submodule.span ℝ (prodFns V W : Set C(V × W, ℝ)) := by
      have : G ∈ Subalgebra.toSubmodule (Algebra.adjoin ℝ (prodFns V W : Set C(V × W, ℝ))) := hG
      rwa [Algebra.adjoin_eq_span, Submonoid.closure_eq] at this
    clear hG
    induction hG' using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨a, b, hab⟩ : ∃ a : C(V, ℝ), ∃ b : C(W, ℝ), ∀ z, g z = a z.1 * b z.2 := hg
      have e : (fun z => χ z * g z) = fun z : V × W => (χ₁ z.1 * a z.1) * (χ₂ z.2 * b z.2) := by
        funext z
        rw [hab, hχ]
        ring
      rw [e]
      exact h (fun x => χ₁ x * a x) (fun y => χ₂ y * b y) (χ₁.continuous.mul a.continuous)
        (h1c.mul_right (f' := a)) (χ₂.continuous.mul b.continuous) (h2c.mul_right (f' := b))
    | zero =>
      have e : ∀ m : Measure (V × W), ∫ z, χ z * (0 : C(V × W, ℝ)) z ∂m = 0 := fun m => by simp
      simp only [e]
      exact tendsto_const_nhds
    | add g g' _ _ hg hg' =>
      have e : ∀ (m : Measure (V × W)) [IsFiniteMeasureOnCompacts m],
          ∫ z, χ z * (g + g') z ∂m = ∫ z, χ z * g z ∂m + ∫ z, χ z * g' z ∂m := by
        intro m _
        rw [← integral_add (hint g m) (hint g' m)]
        congr 1
        funext z
        simp [mul_add]
      rw [e M₀]
      exact (hg.add hg').congr fun i => (e (M i)).symm
    | smul k g _ hg =>
      have e : ∀ m : Measure (V × W), ∫ z, χ z * (k • g) z ∂m = k * ∫ z, χ z * g z ∂m := by
        intro m
        rw [← integral_const_mul]
        congr 1
        funext z
        simp only [ContinuousMap.smul_apply, smul_eq_mul]
        ring
      rw [e M₀]
      exact (hg.const_mul k).congr fun i => (e (M i)).symm
  obtain ⟨L, hLdef⟩ : ∃ L, L = ∫ z, χ z ∂M₀ := ⟨_, rfl⟩
  have hL : Tendsto (fun i => ∫ z, χ z ∂M i) l (𝓝 L) := by
    rw [hLdef]
    exact h χ₁ χ₂ χ₁.continuous h1c χ₂.continuous h2c
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hpos : (0 : ℝ) < |L| + 1 := by positivity
  set δ := ε / 3 / (|L| + 1) with hδ
  have hδpos : 0 < δ := by positivity
  have hδ3 : δ * (|L| + 1) = ε / 3 := div_mul_cancel₀ _ (ne_of_gt hpos)
  obtain ⟨G, hGA, hGK⟩ :=
    ContinuousMap.exists_mem_subalgebra_near_continuous_of_isCompact_of_separatesPoints
      (prodFns_separates V W) ⟨F, hF⟩ hX hδpos
  have hb : ∀ z, ‖F z - χ z * G z‖ ≤ δ * χ z := by
    intro z
    have e : F z - χ z * G z = χ z * (F z - G z) := by rw [mul_sub, hχF]
    rw [e, norm_mul, Real.norm_of_nonneg (hχ0 z)]
    by_cases hz : z ∈ tsupport χ₁ ×ˢ tsupport χ₂
    · have hz' : ‖F z - G z‖ ≤ δ := by
        have := (hGK z hz).le
        rwa [norm_sub_rev] at this
      calc χ z * ‖F z - G z‖ ≤ χ z * δ := mul_le_mul_of_nonneg_left hz' (hχ0 z)
        _ = δ * χ z := mul_comm _ _
    · simp [hχX z hz]
  have hbI : ∀ (m : Measure (V × W)) [IsFiniteMeasureOnCompacts m],
      ‖∫ z, F z ∂m - ∫ z, χ z * G z ∂m‖ ≤ δ * ∫ z, χ z ∂m := by
    intro m _
    rw [← integral_sub (hF.integrable_of_hasCompactSupport hFc) (hint G m), ← integral_const_mul]
    exact norm_integral_le_of_norm_le ((hχc.integrable_of_hasCompactSupport hχs).const_mul δ)
      (Eventually.of_forall hb)
  filter_upwards [hL.eventually (gt_mem_nhds (lt_add_one L)),
    Metric.tendsto_nhds.mp (key G hGA) (ε / 3) (by positivity)] with i hi1 hi2
  have e1 := hbI (M i)
  have e2 := hbI M₀
  rw [← hLdef] at e2
  rw [Real.norm_eq_abs, abs_le] at e1 e2
  rw [Real.dist_eq, abs_lt] at hi2 ⊢
  have h3 : δ * ∫ z, χ z ∂M i < ε / 3 := by
    calc δ * ∫ z, χ z ∂M i < δ * (|L| + 1) :=
          mul_lt_mul_of_pos_left (by linarith [le_abs_self L]) hδpos
      _ = ε / 3 := hδ3
  have h4 : δ * L < ε / 3 := by
    calc δ * L ≤ δ * |L| := mul_le_mul_of_nonneg_left (le_abs_self L) hδpos.le
      _ < δ * (|L| + 1) := by linarith
      _ = ε / 3 := hδ3
  constructor <;> linarith [e1.1, e1.2, e2.1, e2.2, hi2.1, hi2.2]

theorem vag_prod (α β V W : Type) [MeasurableSpace α] [MeasurableSpace β] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W] (μ : Measure α) (ν : Measure β)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (c : α → V) (c' : β → W) (lam : Measure V) (lam' : Measure W)
    [IsLocallyFiniteMeasure lam] [IsLocallyFiniteMeasure lam'] (d d' : ℕ) (hc : Measurable c) (hc' : Measurable c')
    (h : Vag μ c lam d) (h' : Vag ν c' lam' d') :
    Vag (μ.prod ν) (Prod.map c c') (lam.prod lam') (d + d') := by
  intro φ hφ hφc
  let M : ℝ → Measure (V × W) := fun r =>
    Real.toNNReal ((r ^ (d + d'))⁻¹) • (μ.prod ν).map (fun g => (r⁻¹ • c g.1, r⁻¹ • c' g.2))
  have : ∀ r, IsFiniteMeasureOnCompacts (M r) := fun r => by dsimp only [M]; infer_instance
  have hmeas : ∀ r : ℝ, Measurable (fun g : α × β => (r⁻¹ • c g.1, r⁻¹ • c' g.2)) := fun r =>
    (((continuous_const_smul r⁻¹).measurable.comp hc).comp measurable_fst).prodMk
      (((continuous_const_smul r⁻¹).measurable.comp hc').comp measurable_snd)
  have hint : ∀ r : ℝ, 0 < r → ∀ f : V × W → ℝ, Continuous f →
      ∫ z, f z ∂M r = (r ^ (d + d'))⁻¹ * ∫ g, f (r⁻¹ • c g.1, r⁻¹ • c' g.2) ∂(μ.prod ν) := by
    intro r hr f hf
    dsimp only [M]
    rw [integral_smul_nnreal_measure, integral_map (hmeas r).aemeasurable hf.aestronglyMeasurable,
      NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (by positivity)]
  have key := tendsto_integral_of_prod (nhdsWithin (0 : ℝ) (Set.Ioi 0)) M (lam.prod lam') ?_ φ hφ hφc
  · refine key.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
    rw [hint r hr φ hφ]
    rfl
  · intro a b ha hac hb hbc
    have hprod := (h a ha hac).mul (h' b hb hbc)
    rw [integral_prod_mul a b]
    refine hprod.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
    rw [hint r hr (fun z => a z.1 * b z.2) ((ha.comp continuous_fst).mul (hb.comp continuous_snd))]
    have e := integral_prod_mul (μ := μ) (ν := ν) (fun x => a (r⁻¹ • c x)) (fun y => b (r⁻¹ • c' y))
    simp only at e ⊢
    rw [e, pow_add, mul_inv]
    ring

end GlobalTheory.IwConst
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.VagueLimitRescaledMeasuresProdStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vague_limit_rescaled_measures_prod : ∀ (α β V W : Type) [MeasurableSpace α] [MeasurableSpace β] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W] (μ : Measure α) (ν : Measure β) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (c : α → V) (c' : β → W) (lam : Measure V) (lam' : Measure W) [IsLocallyFiniteMeasure lam] [IsLocallyFiniteMeasure lam'] (d d' : ℕ), Measurable c → Measurable c' → Vag μ c lam d → Vag ν c' lam' d' → Vag (μ.prod ν) (Prod.map c c') (lam.prod lam') (d + d') := by
  first | exact @GlobalTheory.IwConst.vag_prod | exact GlobalTheory.IwConst.vag_prod | (intros; apply GlobalTheory.IwConst.vag_prod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TendstoProdGaugeMeasuresGaugeBody
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

namespace GlobalTheory.IwConstBox

theorem local_vag {n d : ℕ} {ε : Fin n → Bool} {S : Set (Formalism.REAL.UJ ε)} {E : Fin d → Matrix (Fin n) (Fin n) ℂ}
    (h : IsCut ε S E) (μ : Measure (Formalism.REAL.UJ ε)) (hμ : IsGaugeSub S d μ) :
    SigmaFinite μ ∧ ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t ≤ t₀ →
      IsFiniteMeasure (μ.restrict {g | nrm (uMat g - 1) < t}) ∧
      Vag (μ.restrict {g | nrm (uMat g - 1) < t}) (fun g => crd E (uMat g - 1)) volume d := by
  obtain ⟨A, hA, hON, hspan, rfl⟩ := h
  obtain ⟨hσ, hcpt, -, r₀, hr₀, hlim⟩ := GlobalTheory.T.gaugeMeasure_matrixAlgebraSubgroup_local_asymptotics n ε A d E hA hON hspan μ hμ
  refine ⟨hσ, Real.sqrt r₀, Real.sqrt_pos.2 hr₀, fun t ht htt => ⟨?_, ?_⟩⟩
  ·
    refine isFiniteMeasure_restrict.2 (ne_of_lt ?_)
    refine lt_of_le_of_lt (measure_mono ?_) (isCompact_hsBall ε t).measure_lt_top
    intro g hg
    exact (show nrm (uMat g - 1) < t from hg).le
  ·
    intro φ hφ hsupp
    have hset : {g : Formalism.REAL.UJ ε | nrm (uMat g - 1) < t} =
        {g | Formalism.REAL.hs (uMat g - 1) < t ^ 2} := by
      ext g
      exact Real.sqrt_lt' ht
    have h1 : 0 < t ^ 2 := by positivity
    have h2 : t ^ 2 ≤ r₀ := by
      calc t ^ 2 ≤ Real.sqrt r₀ ^ 2 := pow_le_pow_left₀ ht.le htt 2
        _ = r₀ := Real.sq_sqrt hr₀.le
    rw [hset]
    refine (hlim (t ^ 2) h1 h2 φ hφ hsupp).congr (fun r => ?_)
    congr 2
    funext g
    congr 1
    ext i
    simp [crd, div_eq_mul_inv, mul_comm]

theorem prod_gauge_body : ∀ (n : ℕ) (ε : Fin n → Bool) (SN SM MainNotions : Set (Formalism.REAL.UJ ε)), ∀ (dN dM dK dL : ℕ) (EN : Fin dN → Matrix (Fin n) (Fin n) ℂ) (EM : Fin dM → Matrix (Fin n) (Fin n) ℂ) (EK : Fin dK → Matrix (Fin n) (Fin n) ℂ) (EL : Fin dL → Matrix (Fin n) (Fin n) ℂ), IsCut ε SN EN → IsCut ε SM EM → IsCut ε MainNotions EK → (∀ v, gau EN EM EK EL v = 0 → v = 0) → ∀ μN μM μK : Measure (Formalism.REAL.UJ ε), IsGaugeSub SN dN μN → IsGaugeSub SM dM μM → IsGaugeSub MainNotions dK μK → ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t ≤ t₀ → Filter.Tendsto (fun r : ℝ => (μN.prod (μM.prod μK)) {x | (nrm (uMat x.1 - 1) < t ∧ nrm (uMat x.2.1 - 1) < t ∧ nrm (uMat x.2.2 - 1) < t) ∧ gau EN EM EK EL (crd EN (uMat x.1 - 1), crd EM (uMat x.2.1 - 1), crd EK (uMat x.2.2 - 1)) ≤ r} / ENNReal.ofReal (r ^ (dN + (dM + dK)))) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (volume {v | gau EN EM EK EL v ≤ 1})) := by
  intro n ε SN SM MainNotions dN dM dK dL EN EM EK EL hN hM hK hgau μN μM μK hμN hμM hμK
  obtain ⟨hσN, tN, htN, hN'⟩ := local_vag hN μN hμN
  obtain ⟨hσM, tM, htM, hM'⟩ := local_vag hM μM hμM
  obtain ⟨hσK, tK, htK, hK'⟩ := local_vag hK μK hμK
  refine ⟨min tN (min tM tK), lt_min htN (lt_min htM htK), fun t ht htt => ?_⟩
  obtain ⟨fN, vN⟩ := hN' t ht (htt.trans (min_le_left _ _))
  obtain ⟨fM, vM⟩ := hM' t ht (htt.trans ((min_le_right _ _).trans (min_le_left _ _)))
  obtain ⟨fK, vK⟩ := hK' t ht (htt.trans ((min_le_right _ _).trans (min_le_right _ _)))
  set s : Set (Formalism.REAL.UJ ε) := {g | nrm (uMat g - 1) < t} with hs
  have hsm : MeasurableSet s := (continuous_nrm_uMat ε).measurable measurableSet_Iio
  have mc : ∀ {e : ℕ} (E : Fin e → Matrix (Fin n) (Fin n) ℂ),
      Measurable fun g : Formalism.REAL.UJ ε => crd E (uMat g - 1) :=
    fun E => (continuous_crd_uMat ε E).measurable

  have vMK := GlobalTheory.T.vague_limit_rescaled_measures_prod _ _ _ _ (μM.restrict s) (μK.restrict s) (fun g => crd EM (uMat g - 1))
    (fun g => crd EK (uMat g - 1)) volume volume dM dK (mc EM) (mc EK) vM vK
  have vNMK := GlobalTheory.T.vague_limit_rescaled_measures_prod _ _ _ _ (μN.restrict s) ((μM.restrict s).prod (μK.restrict s))
    (fun g => crd EN (uMat g - 1)) (Prod.map (fun g => crd EM (uMat g - 1)) (fun g => crd EK (uMat g - 1)))
    volume (volume.prod volume) dN (dM + dK) (mc EN) (Measurable.prodMap (mc EM) (mc EK)) vN vMK
  have h2 : (volume.prod volume : Measure ((Fin dM → ℝ) × (Fin dK → ℝ))).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  have h3 : (volume.prod (volume.prod volume) :
      Measure ((Fin dN → ℝ) × (Fin dM → ℝ) × (Fin dK → ℝ))).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  have key := GlobalTheory.T.tendsto_rescaled_measure_gauge_unit_body _ _ ((μN.restrict s).prod ((μM.restrict s).prod (μK.restrict s)))
    (Prod.map (fun g => crd EN (uMat g - 1))
      (Prod.map (fun g => crd EM (uMat g - 1)) (fun g => crd EK (uMat g - 1))))
    (volume.prod (volume.prod volume)) (dN + (dM + dK)) (gau EN EM EK EL)
    (Measurable.prodMap (mc EN) (Measurable.prodMap (mc EM) (mc EK))) (continuous_gau EN EM EK EL)
    (gau_nonneg EN EM EK EL) (fun c hc v => gau_smul EN EM EK EL c hc v) hgau vNMK
  refine key.congr (fun r => ?_)
  congr 1
  rw [Measure.prod_restrict, Measure.prod_restrict,
    Measure.restrict_apply' (hsm.prod (hsm.prod hsm))]
  congr 1
  ext ⟨a, b, c⟩
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_prod, Prod.map_apply, hs]
  tauto

end GlobalTheory.IwConstBox
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TendstoProdGaugeMeasuresGaugeBodyStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_prod_gaugeMeasures_gaugeBody : ∀ (n : ℕ) (ε : Fin n → Bool) (SN SM MainNotions : Set (Formalism.REAL.UJ ε)), ∀ (dN dM dK dL : ℕ) (EN : Fin dN → Matrix (Fin n) (Fin n) ℂ) (EM : Fin dM → Matrix (Fin n) (Fin n) ℂ) (EK : Fin dK → Matrix (Fin n) (Fin n) ℂ) (EL : Fin dL → Matrix (Fin n) (Fin n) ℂ), IsCut ε SN EN → IsCut ε SM EM → IsCut ε MainNotions EK → (∀ v, gau EN EM EK EL v = 0 → v = 0) → ∀ μN μM μK : Measure (Formalism.REAL.UJ ε), IsGaugeSub SN dN μN → IsGaugeSub SM dM μM → IsGaugeSub MainNotions dK μK → ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t ≤ t₀ → Filter.Tendsto (fun r : ℝ => (μN.prod (μM.prod μK)) {x | (nrm (uMat x.1 - 1) < t ∧ nrm (uMat x.2.1 - 1) < t ∧ nrm (uMat x.2.2 - 1) < t) ∧ gau EN EM EK EL (crd EN (uMat x.1 - 1), crd EM (uMat x.2.1 - 1), crd EK (uMat x.2.2 - 1)) ≤ r} / ENNReal.ofReal (r ^ (dN + (dM + dK)))) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (volume {v | gau EN EM EK EL v ≤ 1})) := by
  first | exact @GlobalTheory.IwConstBox.prod_gauge_body | exact GlobalTheory.IwConstBox.prod_gauge_body | (intros; apply GlobalTheory.IwConstBox.prod_gauge_body <;> assumption)
end
