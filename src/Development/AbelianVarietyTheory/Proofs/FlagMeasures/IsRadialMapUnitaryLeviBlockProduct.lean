module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RiemannianHaarGaugeExistsPosUnique
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniquePlace

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasEuclideanBallVolumeSublevelAsymptoticsProd
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasEuclideanBallVolumeSublevelAsymptoticsProd
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso
open Filter Topology
open scoped ENNReal

namespace GlobalTheory.LeviIso

def SublevelLe {X X' : Type} [MeasurableSpace X] [MeasurableSpace X'] (c : ℝ≥0∞) (T : ℝ)
    (μ : Measure X) (q : X → ℝ) (μ' : Measure X') (q' : X' → ℝ) : Prop :=
  ∀ t ≤ T, μ {x | q x ≤ t} ≤ c * μ' {x | q' x ≤ t}

theorem SublevelLe.mono {X X' : Type} [MeasurableSpace X] [MeasurableSpace X'] {c : ℝ≥0∞}
    {T T' : ℝ} {μ : Measure X} {q : X → ℝ} {μ' : Measure X'} {q' : X' → ℝ}
    (h : SublevelLe c T μ q μ' q') (hT : T' ≤ T) : SublevelLe c T' μ q μ' q' :=
  fun t ht => h t (ht.trans hT)

theorem SublevelLe.prod {X X' Y Y' : Type} [MeasurableSpace X] [MeasurableSpace X']
    [MeasurableSpace Y] [MeasurableSpace Y'] {c : ℝ≥0∞} {T : ℝ}
    {μ : Measure X} {q : X → ℝ} {μ' : Measure X'} {q' : X' → ℝ}
    {ν : Measure Y} {p : Y → ℝ} {ν' : Measure Y'} {p' : Y' → ℝ}
    [SFinite μ] [SFinite μ'] [SFinite ν] [SFinite ν'] (hc : c ≠ ⊤)
    (hq : Measurable q) (hq' : Measurable q') (hp : Measurable p) (hp' : Measurable p')
    (hq0 : ∀ x, 0 ≤ q' x) (hp0 : ∀ y, 0 ≤ p y)
    (h1 : SublevelLe c T μ q μ' q') (h2 : SublevelLe c T ν p ν' p') :
    SublevelLe (c * c) T (μ.prod ν) (fun z => q z.1 + p z.2) (μ'.prod ν')
      (fun z => q' z.1 + p' z.2) := by
  intro t ht
  have m1 : MeasurableSet {z : X × Y | q z.1 + p z.2 ≤ t} :=
    measurableSet_le (by fun_prop) measurable_const
  have m2 : MeasurableSet {z : X' × Y | q' z.1 + p z.2 ≤ t} :=
    measurableSet_le (by fun_prop) measurable_const
  have m3 : MeasurableSet {z : X' × Y' | q' z.1 + p' z.2 ≤ t} :=
    measurableSet_le (by fun_prop) measurable_const
  have s1 : (μ.prod ν) {z : X × Y | q z.1 + p z.2 ≤ t}
      ≤ c * (μ'.prod ν) {z : X' × Y | q' z.1 + p z.2 ≤ t} := by
    rw [Measure.prod_apply_symm m1, Measure.prod_apply_symm m2, ← lintegral_const_mul' _ _ hc]
    refine lintegral_mono fun y => ?_
    have := h1 (t - p y) (by linarith [hp0 y])
    simpa only [Set.preimage_setOf_eq, le_sub_iff_add_le] using this
  have s2 : (μ'.prod ν) {z : X' × Y | q' z.1 + p z.2 ≤ t}
      ≤ c * (μ'.prod ν') {z : X' × Y' | q' z.1 + p' z.2 ≤ t} := by
    rw [Measure.prod_apply m2, Measure.prod_apply m3, ← lintegral_const_mul' _ _ hc]
    refine lintegral_mono fun x => ?_
    have := h2 (t - q' x) (by linarith [hq0 x])
    simpa only [Set.preimage_setOf_eq, le_sub_iff_add_le'] using this
  calc _ ≤ _ := s1
    _ ≤ c * (c * _) := by gcongr
    _ = _ := by rw [mul_assoc]

theorem volume_norm_sq_le (d : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    volume {u : EuclideanSpace ℝ (Fin d) | ‖u‖ ^ 2 ≤ r ^ 2}
      = ENNReal.ofReal (r ^ d) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) := by
  have : {u : EuclideanSpace ℝ (Fin d) | ‖u‖ ^ 2 ≤ r ^ 2} = Metric.closedBall 0 r := by
    ext u
    simp [sq_le_sq₀ (norm_nonneg u) hr]
  rw [this, Measure.addHaar_closedBall _ _ hr]
  simp

theorem setOf_sqrt_le {X : Type} (q : X → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    {x | √(q x) ≤ r} = {x | q x ≤ r ^ 2} := by
  ext x
  simp [Real.sqrt_le_left hr, Real.sqrt_le_iff, hr]

theorem volume_prod_norm_sq_le (d e : ℕ) (t : ℝ) :
    ((volume : Measure (EuclideanSpace ℝ (Fin d))).prod
      (volume : Measure (EuclideanSpace ℝ (Fin e)))) {z | ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 ≤ t}
      = volume {u : EuclideanSpace ℝ (Fin (d + e)) | ‖u‖ ^ 2 ≤ t} := by
  let f : WithLp 2 (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin e)) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin (d + e)) :=
    ((stdOrthonormalBasis ℝ _).reindex (finCongr (by
      rw [(WithLp.linearEquiv 2 ℝ _).finrank_eq]; simp))).repr
  have h := f.measurePreserving.comp (WithLp.volume_preserving_toLp _ _)
  rw [← h.measure_preimage (measurableSet_le (by fun_prop) measurable_const).nullMeasurableSet]
  congr 1
  ext z
  simp [WithLp.prod_norm_sq_eq_of_L2]

theorem exists_one_lt_mul_mul_lt {a b : ℝ≥0∞} (h : a < b) :
    ∃ c : ℝ≥0∞, 1 < c ∧ c ≠ ⊤ ∧ c * c * a < b := by
  have ha : a ≠ ⊤ := h.ne_top
  have t1 : Tendsto (fun c : ℝ≥0∞ => c * c * a) (𝓝 1) (𝓝 (1 * 1 * a)) :=
    ENNReal.Tendsto.mul_const
      (ENNReal.Tendsto.mul tendsto_id (by simp) tendsto_id (by simp)) (Or.inr ha)
  simp only [one_mul] at t1
  have e1 := t1.eventually (gt_mem_nhds h)
  have e2 : ∀ᶠ c : ℝ≥0∞ in 𝓝 1, c < ⊤ := gt_mem_nhds (by simp)
  haveI : (𝓝[>] (1 : ℝ≥0∞)).NeBot := nhdsGT_neBot_of_exists_gt ⟨⊤, by simp⟩
  obtain ⟨c, ⟨h1, h2⟩, h3⟩ := (((e1.and e2).filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin (s := Set.Ioi (1 : ℝ≥0∞)) (a := 1))).exists
  exact ⟨c, h3, h2.ne, h1⟩

theorem IsRadial.sublevelLe {X : Type} [MeasurableSpace X] {μ : Measure X} {q : X → ℝ} {d : ℕ}
    (hq : Measurable q) (hq0 : ∀ x, 0 ≤ q x) (h : IsRadial μ q d) {c : ℝ≥0∞} (hc : 1 < c)
    (hc' : c ≠ ⊤) :
    ∃ T > 0, SublevelLe c T μ q volume (fun u : EuclideanSpace ℝ (Fin d) => ‖u‖ ^ 2) ∧
      SublevelLe c T volume (fun u : EuclideanSpace ℝ (Fin d) => ‖u‖ ^ 2) μ q := by
  unfold IsRadial at h
  set ω := volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) with hω
  have ω0 : ω ≠ 0 := (Metric.measure_ball_pos _ _ one_pos).ne'
  have ωt : ω ≠ ⊤ := measure_ball_lt_top.ne
  have hlt : ω < c * ω := by
    simpa using ENNReal.mul_lt_mul_left ω0 ωt hc
  have e1 := h.eventually (gt_mem_nhds hlt)
  have e2 := (ENNReal.Tendsto.const_mul (a := c) h (Or.inl ω0)).eventually (lt_mem_nhds hlt)
  have e3 : ∀ᶠ r in 𝓝[>] (0 : ℝ), μ {x | √(q x) ≤ r} ≤ c * (ENNReal.ofReal (r ^ d) * ω) ∧
      ENNReal.ofReal (r ^ d) * ω ≤ c * μ {x | √(q x) ≤ r} := by
    filter_upwards [e1, e2, self_mem_nhdsWithin] with r h1 h2 hr
    have hr' : (0 : ℝ) < r := hr
    have n0 : ENNReal.ofReal (r ^ d) ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
    constructor
    · have := (ENNReal.div_le_iff n0 ENNReal.ofReal_ne_top).1 h1.le
      calc _ ≤ _ := this
        _ = _ := by ring
    · rw [← mul_div_assoc] at h2
      have := (ENNReal.le_div_iff_mul_le (Or.inl n0) (Or.inl ENNReal.ofReal_ne_top)).1 h2.le
      rwa [mul_comm] at this
  have tg : Tendsto (fun r : ℝ => μ {x | √(q x) ≤ r}) (𝓝[>] 0) (𝓝 (μ {x | √(q x) ≤ 0})) := by
    have hI : {x | √(q x) ≤ 0} = ⋂ r > (0 : ℝ), {x | √(q x) ≤ r} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      exact ⟨fun h r hr => h.trans hr.le, fun h => le_of_forall_gt_imp_ge_of_dense h⟩
    rw [hI]
    refine tendsto_measure_biInter_gt (s := fun r : ℝ => {x | √(q x) ≤ r})
      (fun r _ => (measurableSet_le (by fun_prop) measurable_const).nullMeasurableSet)
      (fun i j _ hij x hx => le_trans hx hij) ?_
    obtain ⟨r, h1, h2⟩ := (e3.and self_mem_nhdsWithin).exists
    exact ⟨r, h2, ne_top_of_le_ne_top
      (ENNReal.mul_ne_top hc' (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ωt)) h1.1⟩
  have th : Tendsto (fun r : ℝ => ENNReal.ofReal (r ^ d) * ω) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal ((0 : ℝ) ^ d) * ω)) :=
    ENNReal.Tendsto.mul_const
      (((ENNReal.continuous_ofReal.comp (continuous_pow d)).tendsto 0).mono_left
        nhdsWithin_le_nhds) (Or.inr ωt)
  have z1 := le_of_tendsto_of_tendsto tg (ENNReal.Tendsto.const_mul (a := c) th (Or.inr hc'))
    (e3.mono fun r h => h.1)
  have z2 := le_of_tendsto_of_tendsto th (ENNReal.Tendsto.const_mul (a := c) tg (Or.inr hc'))
    (e3.mono fun r h => h.2)
  obtain ⟨δ, hδ, hs⟩ := (mem_nhdsGT_iff_exists_Ioc_subset).1 e3
  have hδ' : (0 : ℝ) < δ := hδ
  have key : ∀ r, 0 ≤ r → r ≤ δ → μ {x | √(q x) ≤ r} ≤ c * (ENNReal.ofReal (r ^ d) * ω) ∧
      ENNReal.ofReal (r ^ d) * ω ≤ c * μ {x | √(q x) ≤ r} := by
    intro r h0 h1
    rcases h0.eq_or_lt with rfl | h0
    · exact ⟨z1, z2⟩
    · exact hs ⟨h0, h1⟩
  have key2 : ∀ t ≤ δ ^ 2,
      μ {x | q x ≤ t} ≤ c * volume {u : EuclideanSpace ℝ (Fin d) | ‖u‖ ^ 2 ≤ t} ∧
      volume {u : EuclideanSpace ℝ (Fin d) | ‖u‖ ^ 2 ≤ t} ≤ c * μ {x | q x ≤ t} := by
    intro t ht
    rcases lt_or_ge t 0 with h0 | h0
    · have a1 : {x | q x ≤ t} = ∅ := by
        ext x; simp; linarith [hq0 x]
      have a2 : {u : EuclideanSpace ℝ (Fin d) | ‖u‖ ^ 2 ≤ t} = ∅ := by
        ext x; simp; nlinarith [sq_nonneg ‖x‖]
      simp [a1, a2]
    · have := key (√t) (Real.sqrt_nonneg _) (Real.sqrt_le_iff.2 ⟨hδ'.le, ht⟩)
      rw [← volume_norm_sq_le d (Real.sqrt_nonneg _), setOf_sqrt_le q (Real.sqrt_nonneg _),
        Real.sq_sqrt h0] at this
      exact this
  exact ⟨δ ^ 2, by positivity, fun t ht => (key2 t ht).1, fun t ht => (key2 t ht).2⟩

theorem isRadial_of_sublevelLe {X : Type} [MeasurableSpace X] {μ : Measure X} {q : X → ℝ} {d : ℕ}
    (h : ∀ c : ℝ≥0∞, 1 < c → c ≠ ⊤ → ∃ T > 0,
      SublevelLe (c * c) T μ q volume (fun u : EuclideanSpace ℝ (Fin d) => ‖u‖ ^ 2) ∧
      SublevelLe (c * c) T volume (fun u : EuclideanSpace ℝ (Fin d) => ‖u‖ ^ 2) μ q) :
    IsRadial μ q d := by
  unfold IsRadial
  have hv := fun r => volume_norm_sq_le d (r := r)
  set ω := volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) with hω
  have ev : ∀ T > (0 : ℝ), ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < r ∧ r ^ 2 ≤ T := by
    intro T hT
    filter_upwards [Ioc_mem_nhdsGT (Real.sqrt_pos.2 hT)] with r hr
    exact ⟨hr.1, (Real.le_sqrt hr.1.le hT.le).1 hr.2⟩
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · obtain ⟨c, c1, c2, c3⟩ := exists_one_lt_mul_mul_lt ha
    obtain ⟨T, hT, -, h2⟩ := h c c1 c2
    filter_upwards [ev T hT] with r ⟨hr, hrT⟩
    have n0 : ENNReal.ofReal (r ^ d) ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
    have := h2 _ hrT
    rw [hv r hr.le, ← setOf_sqrt_le q hr.le, mul_comm,
      ← ENNReal.le_div_iff_mul_le (Or.inl n0) (Or.inl ENNReal.ofReal_ne_top),
      mul_div_assoc] at this
    by_contra hn
    have h3 : c * c * (μ {x | √(q x) ≤ r} / ENNReal.ofReal (r ^ d)) ≤ c * c * a := by
      gcongr; exact not_lt.1 hn
    exact absurd (c3.trans_le (this.trans h3)) (lt_irrefl _)
  · obtain ⟨c, c1, c2, c3⟩ := exists_one_lt_mul_mul_lt ha
    obtain ⟨T, hT, h1, -⟩ := h c c1 c2
    filter_upwards [ev T hT] with r ⟨hr, hrT⟩
    have n0 : ENNReal.ofReal (r ^ d) ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
    have := h1 _ hrT
    rw [hv r hr.le, ← setOf_sqrt_le q hr.le] at this
    refine lt_of_le_of_lt ?_ c3
    rw [ENNReal.div_le_iff n0 ENNReal.ofReal_ne_top]
    calc _ ≤ _ := this
      _ = _ := by ring

theorem isRadial_prod : ∀ (X Y : Type) [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν] (q : X → ℝ) (p : Y → ℝ) (d e : ℕ), Measurable q → Measurable p → (∀ x, 0 ≤ q x) → (∀ y, 0 ≤ p y) → IsRadial μ q d → IsRadial ν p e → IsRadial (μ.prod ν) (fun z => q z.1 + p z.2) (d + e) := by
  intro X Y _ _ μ ν _ _ q p d e hq hp hq0 hp0 h1 h2
  refine isRadial_of_sublevelLe fun c c1 c2 => ?_
  obtain ⟨T, hT, a1, a2⟩ := h1.sublevelLe hq hq0 c1 c2
  obtain ⟨T', hT', b1, b2⟩ := h2.sublevelLe hp hp0 c1 c2
  refine ⟨min T T', lt_min hT hT', fun t ht => ?_, fun t ht => ?_⟩
  · have := SublevelLe.prod c2 hq (by fun_prop) hp (by fun_prop) (fun _ => by positivity) hp0
      (a1.mono (min_le_left _ _)) (b1.mono (min_le_right _ _)) t ht
    rwa [volume_prod_norm_sq_le] at this
  · have := SublevelLe.prod c2 (by fun_prop) hq (by fun_prop) hp hq0 (fun _ => by positivity)
      (a2.mono (min_le_left _ _)) (b2.mono (min_le_right _ _)) t ht
    rwa [volume_prod_norm_sq_le] at this

end GlobalTheory.LeviIso
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasEuclideanBallVolumeSublevelAsymptoticsProdStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasEuclideanBallVolumeSublevelAsymptotics_prod : ∀ (X Y : Type) [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν] (q : X → ℝ) (p : Y → ℝ) (d e : ℕ), Measurable q → Measurable p → (∀ x, 0 ≤ q x) → (∀ y, 0 ≤ p y) → IsRadial μ q d → IsRadial ν p e → IsRadial (μ.prod ν) (fun z => q z.1 + p z.2) (d + e) := by
  first | exact @GlobalTheory.LeviIso.isRadial_prod | exact GlobalTheory.LeviIso.isRadial_prod | (intros; apply GlobalTheory.LeviIso.isRadial_prod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EuclideanBallAsymptoticsFinitePi
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EuclideanBallAsymptoticsFinitePi
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

namespace GlobalTheory.LeviIso

theorem IsRadial.comp_measurableEquiv {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X}
    {ν : Measure Y} (e : X ≃ᵐ Y) (he : MeasurePreserving e μ ν) {q : X → ℝ} {p : Y → ℝ} {d : ℕ}
    (hq : ∀ x, q x = p (e x)) (h : IsRadial ν p d) : IsRadial μ q d := by
  unfold IsRadial at *
  refine h.congr fun r => ?_
  rw [← he.measure_preimage_equiv]
  simp only [hq, Set.preimage_ofPred_eq]

theorem isRadial_pi : ∀ (a : ℕ) (X : Fin a → Type) [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i))
    [∀ i, SigmaFinite (μ i)] (q : ∀ i, X i → ℝ) (d : Fin a → ℕ), (∀ i, Measurable (q i)) →
    (∀ i x, 0 ≤ q i x) → (∀ i, IsRadial (μ i) (q i) (d i)) →
    IsRadial (Measure.pi μ) (fun x => ∑ i, q i (x i)) (∑ i, d i) := by
  intro a
  induction a with
  | zero =>
    intro X _ μ _ q d _ _ _
    rw [Fin.sum_univ_zero]
    unfold IsRadial
    rw [volume_euclideanSpace_eq_dirac, Measure.dirac_apply_of_mem (Metric.mem_ball_self one_pos)]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr' : (0 : ℝ) ≤ r := le_of_lt hr
    rw [Measure.pi_of_empty, Measure.dirac_apply_of_mem (by simpa using hr')]
    simp
  | succ a ih =>
    intro X _ μ _ q d hm h0 hr
    have h := GlobalTheory.T.hasEuclideanBallVolumeSublevelAsymptotics_prod _ _ (μ 0) (Measure.pi fun j => μ (Fin.succAbove 0 j)) (q 0)
      (fun x => ∑ j, q (Fin.succAbove 0 j) (x j)) (d 0) (∑ j, d (Fin.succAbove 0 j)) (hm 0)
      (Finset.measurable_sum _ fun j _ => (hm _).comp (measurable_pi_apply j)) (h0 0)
      (fun y => Finset.sum_nonneg fun j _ => h0 _ _) (hr 0)
      (ih _ _ _ _ (fun j => hm _) (fun j => h0 _) fun j => hr _)
    rw [Fin.sum_univ_succAbove d 0]
    exact h.comp_measurableEquiv _ (measurePreserving_piFinSuccAbove μ 0)
      fun x => Fin.sum_univ_succAbove (fun i => q i (x i)) 0

end GlobalTheory.LeviIso
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EuclideanBallAsymptoticsFinitePiStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.euclideanBallAsymptotics_finite_pi : ∀ (a : ℕ) (X : Fin a → Type) [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)] (q : ∀ i, X i → ℝ) (d : Fin a → ℕ), (∀ i, Measurable (q i)) → (∀ i x, 0 ≤ q i x) → (∀ i, IsRadial (μ i) (q i) (d i)) → IsRadial (Measure.pi μ) (fun x => ∑ i, q i (x i)) (∑ i, d i) := by
  first | exact @GlobalTheory.LeviIso.isRadial_pi | exact GlobalTheory.LeviIso.isRadial_pi | (intros; apply GlobalTheory.LeviIso.isRadial_pi <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HilbertSchmidtEqReTrace
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso
open Formalism.REAL (Jm hs Jm_mul_self Jm_conjTranspose)

namespace GlobalTheory.LeviIso

theorem trace_compress {n m : ℕ} (D : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin n) (Fin m) ℂ)
    (y : Matrix (Fin m) (Fin m) ℂ) (hC : Cᴴ * C = 1) (hD : D * C = C * y) :
    (Dᴴ * D * (C * Cᴴ)).trace = (yᴴ * y).trace := by
  have hcore : Cᴴ * (Dᴴ * D * C) = yᴴ * y :=
    calc Cᴴ * (Dᴴ * D * C) = (D * C)ᴴ * (D * C) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (C * y)ᴴ * (C * y) := by rw [hD]
      _ = yᴴ * (Cᴴ * C) * y := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = yᴴ * y := by rw [hC, Matrix.mul_one]
  rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, hcore]

private theorem hs_eq_re_trace_conjTranspose_mul {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) : hs X = (trace (Xᴴ * X)).re := by
  unfold hs
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [Complex.mul_re]

theorem hs_lev_sub_one : ∀ (n n₀ a : ℕ) (j : Fin a → ℕ) (ε : Fin n → Bool) (ε₀ : Fin n₀ → Bool)
    (B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (B₀ : Matrix (Fin n) (Fin n₀) ℂ), IsFrame ε ε₀ B B₀ →
    ∀ (x : ∀ i, Matrix (Fin (j i)) (Fin (j i)) ℂ) (g : Matrix (Fin n₀) (Fin n₀) ℂ),
    Formalism.REAL.hs (lev ε B B₀ x g - 1) =
      ∑ i, (Formalism.REAL.hs (x i - 1) + Formalism.REAL.hs ((x i)⁻¹ - 1)) + Formalism.REAL.hs (g - 1) := by
  intro n n₀ a j ε ε₀ B B₀ h x g
  have hJ : ∀ i, (Jm ε * B i)ᴴ * (Jm ε * B i) = 1 := fun i => by
    rw [Matrix.conjTranspose_mul, Jm_conjTranspose, Matrix.mul_assoc, ← Matrix.mul_assoc (Jm ε),
      Jm_mul_self, Matrix.one_mul, h.1 i]
  have hsplit : (1 : Matrix (Fin n) (Fin n) ℂ) =
      ∑ i, B i * (B i)ᴴ + ∑ i, (Jm ε * B i) * (Jm ε * B i)ᴴ + B₀ * B₀ᴴ := by
    rw [← h.2.2.2.2.2.2]
    congr 2
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.conjTranspose_mul, Jm_conjTranspose]
    simp only [Matrix.mul_assoc]
  have hsub : ∀ {m : ℕ} (C : Matrix (Fin n) (Fin m) ℂ) (y : Matrix (Fin m) (Fin m) ℂ),
      lev ε B B₀ x g * C = C * y → (lev ε B B₀ x g - 1) * C = C * (y - 1) := by
    intro m C y hy
    rw [Matrix.sub_mul, hy, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one]
  have hconj : ∀ {m : ℕ} (Y : Matrix (Fin m) (Fin m) ℂ), hs Yᴴ = hs Y := by
    intro m Y
    rw [hs_eq_re_trace_conjTranspose_mul, hs_eq_re_trace_conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.trace_mul_comm]
  set M := lev ε B B₀ x g - 1 with hM
  have eB : ∀ i, (Mᴴ * M * (B i * (B i)ᴴ)).trace = ((x i - 1)ᴴ * (x i - 1)).trace := fun i =>
    trace_compress M (B i) _ (h.1 i) (hsub _ _ (h.lev_mul_B x g i))
  have eJ : ∀ i, (Mᴴ * M * ((Jm ε * B i) * (Jm ε * B i)ᴴ)).trace =
      (((x i)⁻¹ᴴ - 1)ᴴ * ((x i)⁻¹ᴴ - 1)).trace := fun i =>
    trace_compress M (Jm ε * B i) _ (hJ i) (hsub _ _ (h.lev_mul_JB x g i))
  have e0 : (Mᴴ * M * (B₀ * B₀ᴴ)).trace = ((g - 1)ᴴ * (g - 1)).trace :=
    trace_compress M B₀ _ h.2.2.2.2.1 (hsub _ _ (h.lev_mul_B₀ x g))
  rw [hs_eq_re_trace_conjTranspose_mul, ← Matrix.mul_one (Mᴴ * M), hsplit]
  simp only [Matrix.mul_add, Matrix.mul_sum, Matrix.trace_add, Matrix.trace_sum, Complex.add_re,
    Complex.re_sum, eB, eJ, e0, Finset.sum_add_distrib]
  have hinv : ∀ i, (x i)⁻¹ᴴ - 1 = ((x i)⁻¹ - 1)ᴴ := fun i => by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one]
  simp only [hinv, ← hs_eq_re_trace_conjTranspose_mul, hconj]

end GlobalTheory.LeviIso
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasEuclideanBallVolumeHaarComplexGLInverse
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasEuclideanBallVolumeHaarComplexGLInverse
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso
open Formalism.REAL (hs)

noncomputable section

namespace GlobalTheory.LeviIso.RadLoc

section
open scoped Matrix.Norms.Frobenius

theorem hs_eq_norm_sq {j : ℕ} (M : Matrix (Fin j) (Fin j) ℂ) : hs M = ‖M‖ ^ 2 := by
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow, Real.sq_sqrt (by positivity)]
  simp [hs]

theorem hs_inv_compare {j : ℕ} (x : Matrix (Fin j) (Fin j) ℂ) (hx : x.det ≠ 0) {a : ℝ} (ha : 0 < a)
    (ha1 : a < 1) (h : hs (x⁻¹ - 1) ≤ (1 - a) ^ 2) :
    a ^ 2 * hs (x - 1) ≤ hs (x⁻¹ - 1) ∧ a ^ 2 * hs (x⁻¹ - 1) ≤ hs (x - 1) := by
  simp only [hs_eq_norm_sq] at *
  have e : (x⁻¹ - 1) + (x - 1) = -((x⁻¹ - 1) * (x - 1)) := by
    rw [sub_mul, mul_sub, Matrix.nonsing_inv_mul _ (Ne.isUnit hx)]
    simp
    abel
  have h1 : ‖(x⁻¹ - 1) + (x - 1)‖ ≤ ‖x⁻¹ - 1‖ * ‖x - 1‖ := by
    rw [e, norm_neg]; exact norm_mul_le _ _
  have h2 : ‖x⁻¹ - 1‖ ≤ ‖(x⁻¹ - 1) + (x - 1)‖ + ‖x - 1‖ := by
    simpa using norm_sub_le ((x⁻¹ - 1) + (x - 1)) (x - 1)
  have h3 : ‖x - 1‖ ≤ ‖(x⁻¹ - 1) + (x - 1)‖ + ‖x⁻¹ - 1‖ := by
    simpa using norm_sub_le ((x⁻¹ - 1) + (x - 1)) (x⁻¹ - 1)
  have hA := norm_nonneg (x - 1)
  have hB := norm_nonneg (x⁻¹ - 1)
  generalize ‖x - 1‖ = A at *
  generalize ‖x⁻¹ - 1‖ = B at *
  have h4 : B ≤ 1 - a := (sq_le_sq₀ hB (by linarith)).1 h
  have h5 : B * A ≤ (1 - a) * A := mul_le_mul_of_nonneg_right h4 hA
  rw [← mul_pow, ← mul_pow, sq_le_sq₀ (by positivity) hB, sq_le_sq₀ (by positivity) hA]
  constructor
  · linarith
  · have h6 : a * B ≤ a * ((2 - a) * A) := mul_le_mul_of_nonneg_left (by linarith) ha.le
    nlinarith [mul_nonneg (sq_nonneg (1 - a)) hA]

end

theorem hs_nonneg {j : ℕ} (M : Matrix (Fin j) (Fin j) ℂ) : 0 ≤ hs M := by
  unfold hs; positivity

theorem continuous_hs {j : ℕ} : Continuous (hs : Matrix (Fin j) (Fin j) ℂ → ℝ) := by
  unfold hs; fun_prop

def unitBallAt (j : ℕ) (s : ℝ) : Set (Fin j → Fin j → ℂ) := {x | hs (Matrix.of x - 1) ≤ s ^ 2}

theorem measurableSet_unitBallAt (j : ℕ) (s : ℝ) : MeasurableSet (unitBallAt j s) := by
  refine (isClosed_le (continuous_hs.comp ?_) continuous_const).measurableSet
  exact (continuous_id (X := Matrix (Fin j) (Fin j) ℂ)).sub continuous_const

theorem volume_unitBallAt (j : ℕ) {s : ℝ} (hs0 : 0 < s) :
    volume (unitBallAt j s) = ENNReal.ofReal (s ^ (2 * j ^ 2)) *
      volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (2 * j ^ 2))) 1) := by
  have hd : Module.finrank ℝ (EuclideanSpace ℂ (Fin j × Fin j)) = 2 * j ^ 2 := by
    rw [(WithLp.linearEquiv 2 ℝ (Fin j × Fin j → ℂ)).finrank_eq, Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex]
    ring
  set e := PoissonV.coords (Fin j) (Fin j) with he
  rw [← (PoissonV.measurePreserving_coords (Fin j) (Fin j)).measure_preimage
    (measurableSet_unitBallAt j s).nullMeasurableSet, ← he]
  have h1 : e ⁻¹' unitBallAt j s =
      Metric.closedBall (e.symm (Matrix.of.symm (1 : Matrix (Fin j) (Fin j) ℂ))) s := by
    ext z
    rw [mem_closedBall_iff_norm, ← sq_le_sq₀ (norm_nonneg _) hs0.le, ← PoissonV.norm_sq_coords, ← he,
      map_sub, e.apply_symm_apply]
    rfl
  rw [h1, Measure.addHaar_closedBall _ _ hs0.le, hd]
  congr 1
  rw [← hd]
  have h := (stdOrthonormalBasis ℝ (EuclideanSpace ℂ (Fin j × Fin j))).measurePreserving_repr
  rw [← h.measure_preimage measurableSet_ball.nullMeasurableSet]
  congr 1
  ext x
  simp

theorem exists_subset {j : ℕ} {P : (Fin j → Fin j → ℂ) → Prop}
    (h : ∀ᶠ x in nhds (Matrix.of.symm (1 : Matrix (Fin j) (Fin j) ℂ)), P x) :
    ∃ δ > 0, ∀ s, 0 ≤ s → s < δ → ∀ x ∈ unitBallAt j s, P x := by
  obtain ⟨δ, hδ, H⟩ := Metric.eventually_nhds_iff.1 h
  refine ⟨δ, hδ, fun s hs0 hsδ x hx => H (lt_of_le_of_lt ?_ hsδ)⟩
  rw [dist_eq_norm, pi_norm_le_iff_of_nonneg hs0]
  intro r
  rw [pi_norm_le_iff_of_nonneg hs0]
  intro c
  rw [← sq_le_sq₀ (norm_nonneg _) hs0]
  refine le_trans ?_ hx
  unfold hs
  refine le_trans ?_ (Finset.single_le_sum (fun i _ => by positivity) (Finset.mem_univ r))
  exact Finset.single_le_sum (f := fun c => ‖(Matrix.of x - 1) r c‖ ^ 2) (fun i _ => by positivity)
    (Finset.mem_univ c)

theorem eventually_good (j : ℕ) {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    ∀ᶠ x : Fin j → Fin j → ℂ in nhds (Matrix.of.symm (1 : Matrix (Fin j) (Fin j) ℂ)),
      (a ≤ (‖(Matrix.of x).det‖ ^ 2)⁻¹ ^ j ∧ (‖(Matrix.of x).det‖ ^ 2)⁻¹ ^ j ≤ a⁻¹) ∧
      a ^ 2 * hs (Matrix.of x - 1) ≤ hs ((Matrix.of x)⁻¹ - 1) ∧
      a ^ 2 * hs ((Matrix.of x)⁻¹ - 1) ≤ hs (Matrix.of x - 1) := by
  show ∀ᶠ x : Matrix (Fin j) (Fin j) ℂ in nhds 1,
      (a ≤ (‖x.det‖ ^ 2)⁻¹ ^ j ∧ (‖x.det‖ ^ 2)⁻¹ ^ j ≤ a⁻¹) ∧
      a ^ 2 * hs (x - 1) ≤ hs (x⁻¹ - 1) ∧ a ^ 2 * hs (x⁻¹ - 1) ≤ hs (x - 1)
  have hdet : Continuous fun x : Matrix (Fin j) (Fin j) ℂ => x.det := continuous_id.matrix_det
  have h1 : ContinuousAt (fun x : Matrix (Fin j) (Fin j) ℂ => (‖x.det‖ ^ 2)⁻¹ ^ j) 1 :=
    (((hdet.norm.pow 2).continuousAt).inv₀ (by simp)).pow j
  have h2 : ContinuousAt (fun x : Matrix (Fin j) (Fin j) ℂ => hs (x⁻¹ - 1)) 1 := by
    refine continuous_hs.continuousAt.comp (ContinuousAt.sub (continuousAt_matrix_inv _ ?_) continuousAt_const)
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ (by simp)
  have h3 := h1.eventually (lt_mem_nhds (a := a) (by simpa using ha1))
  have h4 := h1.eventually (gt_mem_nhds (a := a⁻¹) (by simpa using (one_lt_inv₀ ha).2 ha1))
  have h5 := h2.eventually (gt_mem_nhds (a := (1 - a) ^ 2) (by
    have : 0 < 1 - a := by linarith
    simpa [hs] using pow_pos this 2))
  have h6 := (hdet.continuousAt (x := 1)).eventually_ne (y := 0) (by simp)
  filter_upwards [h3, h4, h5, h6] with x x3 x4 x5 x6
  exact ⟨⟨x3.le, x4.le⟩, hs_inv_compare x x6 ha ha1 x5.le⟩

theorem sandwich (j : ℕ) {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    ∀ᶠ r : ℝ in nhdsWithin 0 (Set.Ioi 0),
      ENNReal.ofReal (a ^ (2 * j ^ 2 + 1)) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (2 * j ^ 2))) 1) ≤
        (ENNReal.ofReal (2 ^ (j ^ 2)) • haarLoc j)
          {x | Real.sqrt (hs (Matrix.of x - 1) + hs ((Matrix.of x)⁻¹ - 1)) ≤ r} /
          ENNReal.ofReal (r ^ (2 * j ^ 2)) ∧
      (ENNReal.ofReal (2 ^ (j ^ 2)) • haarLoc j)
          {x | Real.sqrt (hs (Matrix.of x - 1) + hs ((Matrix.of x)⁻¹ - 1)) ≤ r} /
          ENNReal.ofReal (r ^ (2 * j ^ 2)) ≤
      ENNReal.ofReal (a⁻¹ ^ (2 * j ^ 2 + 1)) *
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (2 * j ^ 2))) 1) := by
  obtain ⟨δ, hδ, H⟩ := exists_subset (eventually_good j ha ha1)
  filter_upwards [Ioo_mem_nhdsGT (mul_pos ha hδ)] with r ⟨hr, hrδ⟩
  have h2 : (0 : ℝ) < √2 := by positivity
  have h21 : (1 : ℝ) ≤ √2 := Real.one_le_sqrt.2 (by norm_num)
  have h22 : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hr1 : r < δ := by nlinarith
  have hr2 : a * r / √2 < δ := by
    refine lt_of_le_of_lt (div_le_self (by positivity) h21) (by nlinarith)
  have hr3 : a⁻¹ * r / √2 < δ := by
    refine lt_of_le_of_lt (div_le_self (by positivity) h21) ?_
    rwa [inv_mul_lt_iff₀ ha]
  have hrd : ENNReal.ofReal (r ^ (2 * j ^ 2)) ≠ 0 := by
    simpa using pow_pos hr _
  have hvol : ∀ b : ℝ, 0 < b → ENNReal.ofReal (2 ^ (j ^ 2)) * (ENNReal.ofReal b *
      volume (unitBallAt j (b * r / √2))) = ENNReal.ofReal (b ^ (2 * j ^ 2 + 1)) *
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (2 * j ^ 2))) 1) * ENNReal.ofReal (r ^ (2 * j ^ 2)) := by
    intro b hb
    rw [volume_unitBallAt j (by positivity), mul_right_comm, ← mul_assoc, ← mul_assoc,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 2
    rw [div_pow, pow_mul √2, h22, mul_pow]
    field_simp
    ring
  constructor
  · rw [ENNReal.le_div_iff_mul_le (Or.inl hrd) (Or.inl ENNReal.ofReal_ne_top), ← hvol a ha,
      Measure.smul_apply, smul_eq_mul]
    gcongr
    refine le_trans ?_ (measure_mono (s := unitBallAt j (a * r / √2)) fun x hx => ?_)
    · rw [haarLoc, withDensity_apply _ (measurableSet_unitBallAt j _), ← setLIntegral_const]
      exact setLIntegral_mono' (measurableSet_unitBallAt j _) fun x hx =>
        ENNReal.ofReal_le_ofReal (H _ (by positivity) hr2 x hx).1.1
    · have h3 := (H _ (by positivity) hr2 x hx).2.2
      have h4 : hs (Matrix.of x - 1) ≤ a ^ 2 * r ^ 2 / 2 := by
        have : hs (Matrix.of x - 1) ≤ (a * r / √2) ^ 2 := hx
        rwa [div_pow, h22, mul_pow] at this
      have h5 : hs ((Matrix.of x)⁻¹ - 1) ≤ r ^ 2 / 2 :=
        le_of_mul_le_mul_left (a := a ^ 2) (by linarith) (by positivity)
      have h6 : a ^ 2 * r ^ 2 ≤ r ^ 2 := mul_le_of_le_one_left (by positivity) (by nlinarith)
      refine Real.sqrt_le_iff.2 ⟨hr.le, by linarith⟩
  · rw [ENNReal.div_le_iff hrd ENNReal.ofReal_ne_top, ← hvol a⁻¹ (by positivity),
      Measure.smul_apply, smul_eq_mul]
    gcongr
    refine le_trans (measure_mono (t := unitBallAt j (a⁻¹ * r / √2)) fun x hx => ?_) ?_
    · have h1 := (Real.sqrt_le_iff.1 hx).2
      have h0 := hs_nonneg ((Matrix.of x)⁻¹ - 1)
      have h0' := hs_nonneg (Matrix.of x - 1)
      have h3 := (H r hr.le hr1 x (show hs (Matrix.of x - 1) ≤ r ^ 2 by linarith)).2.1
      have h6 : a ^ 2 * hs (Matrix.of x - 1) ≤ hs (Matrix.of x - 1) :=
        mul_le_of_le_one_left h0' (by nlinarith)
      show hs (Matrix.of x - 1) ≤ (a⁻¹ * r / √2) ^ 2
      rw [div_pow, h22, mul_pow, inv_pow, le_div_iff₀ (by norm_num), le_inv_mul_iff₀ (by positivity)]
      linarith
    · rw [haarLoc, withDensity_apply _ (measurableSet_unitBallAt j _), ← setLIntegral_const]
      exact setLIntegral_mono' (measurableSet_unitBallAt j _) fun x hx =>
        ENNReal.ofReal_le_ofReal (H _ (by positivity) hr3 x hx).1.2

end GlobalTheory.LeviIso.RadLoc

namespace GlobalTheory.LeviIso

open RadLoc

theorem isRadial_haarLoc (j : ℕ) : IsRadial (ENNReal.ofReal (2 ^ (j ^ 2)) • haarLoc j)
    (fun x => Formalism.REAL.hs (Matrix.of x - 1) + Formalism.REAL.hs ((Matrix.of x)⁻¹ - 1)) (2 * j ^ 2) := by
  unfold IsRadial
  set ω := volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (2 * j ^ 2))) 1) with hω
  have hωt : ω ≠ ⊤ := measure_ball_lt_top.ne
  have hc : Filter.Tendsto (fun a : ℝ => ENNReal.ofReal (a ^ (2 * j ^ 2 + 1)) * ω) (nhds 1) (nhds ω) := by
    have : Filter.Tendsto (fun a : ℝ => ENNReal.ofReal (a ^ (2 * j ^ 2 + 1))) (nhds 1) (nhds 1) := by
      simpa using ENNReal.tendsto_ofReal ((continuous_pow (2 * j ^ 2 + 1)).tendsto (1 : ℝ))
    simpa using ENNReal.Tendsto.mul_const this (Or.inl one_ne_zero)
  have hi : Filter.Tendsto (fun a : ℝ => a⁻¹) (nhds 1) (nhds 1) := by
    simpa using Filter.Tendsto.inv₀ (Filter.tendsto_id (x := nhds (1 : ℝ))) one_ne_zero
  refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
  · obtain ⟨a, h1, h2, h3⟩ := (((hc.eventually (lt_mem_nhds hb)).filter_mono nhdsWithin_le_nhds).and
      (Ioo_mem_nhdsLT (zero_lt_one' ℝ))).exists
    filter_upwards [sandwich j h2 h3] with r hr
    exact lt_of_lt_of_le h1 hr.1
  · obtain ⟨a, h1, h2, h3⟩ := ((((hc.comp hi).eventually (gt_mem_nhds hb)).filter_mono nhdsWithin_le_nhds).and
      (Ioo_mem_nhdsLT (zero_lt_one' ℝ))).exists
    filter_upwards [sandwich j h2 h3] with r hr
    exact lt_of_le_of_lt hr.2 h1

end GlobalTheory.LeviIso
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasEuclideanBallVolumeHaarComplexGLInverseStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasEuclideanBallVolume_haarComplexGL_inverse : ∀ j : ℕ, IsRadial (ENNReal.ofReal (2 ^ (j ^ 2)) • haarLoc j) (fun x => Formalism.REAL.hs (Matrix.of x - 1) + Formalism.REAL.hs ((Matrix.of x)⁻¹ - 1)) (2 * j ^ 2) := by
  first | exact @GlobalTheory.LeviIso.isRadial_haarLoc | exact GlobalTheory.LeviIso.isRadial_haarLoc | (intros; apply GlobalTheory.LeviIso.isRadial_haarLoc <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsRadialMapUnitaryLeviBlockProduct
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

namespace GlobalTheory.LeviIso.MapRadial

theorem continuous_hs {n : ℕ} : Continuous (Formalism.REAL.hs : Matrix (Fin n) (Fin n) ℂ → ℝ) := by
  unfold Formalism.REAL.hs
  fun_prop

theorem hs_nonneg' {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ Formalism.REAL.hs g := by
  unfold Formalism.REAL.hs
  positivity

theorem measurable_hs_uMat {n : ℕ} (ε : Fin n → Bool) :
    Measurable fun g : Formalism.REAL.UJ ε => Formalism.REAL.hs (uMat g - 1) := by
  have : Continuous fun g : Formalism.REAL.UJ ε => uMat g :=
    Units.continuous_val.comp continuous_subtype_val
  exact (continuous_hs.comp (this.sub continuous_const)).measurable

theorem measurable_hs_loc (j : ℕ) : Measurable fun x : Fin j → Fin j → ℂ =>
    Formalism.REAL.hs (Matrix.of x - 1) + Formalism.REAL.hs ((Matrix.of x)⁻¹ - 1) := by
  have h0 : Continuous fun x : Fin j → Fin j → ℂ => Matrix.of x := continuous_id
  have h1 : Measurable fun x : Fin j → Fin j → ℂ => (Matrix.of x).det := h0.matrix_det.measurable
  have h2 : ∀ r s, Measurable fun x : Fin j → Fin j → ℂ => (Matrix.of x).adjugate r s :=
    fun r s => (h0.matrix_adjugate.matrix_elem r s).measurable
  refine (continuous_hs.comp (h0.sub continuous_const)).measurable.add ?_
  unfold Formalism.REAL.hs
  refine Finset.measurable_sum _ fun r _ => Finset.measurable_sum _ fun s _ => ?_
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  exact (((h1.inv.mul (h2 r s)).sub measurable_const).norm).pow_const 2

theorem isRadial_map_lev : ∀ (n n₀ a : ℕ) (j : Fin a → ℕ) (ε : Fin n → Bool) (ε₀ : Fin n₀ → Bool) (B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (B₀ : Matrix (Fin n) (Fin n₀) ℂ), IsFrame ε ε₀ B B₀ → ∀ θ : (∀ i, Fin (j i) → Fin (j i) → ℂ) × Formalism.REAL.UJ ε₀ → Formalism.REAL.UJ ε, Measurable θ → (∀ z, (∀ i, (Matrix.of (z.1 i)).det ≠ 0) → uMat (θ z) = lev ε B B₀ (fun i => Matrix.of (z.1 i)) (uMat z.2)) → ∀ c : ℝ, IsGauge ε₀ c → IsRadial (((Measure.pi fun i => ENNReal.ofReal (2 ^ (j i ^ 2)) • haarLoc (j i)).prod (ENNReal.ofReal c • Formalism.REAL.muG ε₀)).map θ) (fun g => Formalism.REAL.hs (uMat g - 1)) (n₀ ^ 2 + 2 * ∑ i, j i ^ 2) := by
  intro n n₀ a j ε ε₀ B B₀ hF θ hθ hθe c hc
  have hG : IsRadial (ENNReal.ofReal c • Formalism.REAL.muG ε₀) (fun g => Formalism.REAL.hs (uMat g - 1)) (n₀ ^ 2) := by
    have := ((GlobalTheory.GaugeWhole.gauge_whole n₀ ε₀).1 c hc).2.2.2
    simpa [IsRadial] using this
  haveI : SigmaFinite (Formalism.REAL.muG ε₀) := by
    unfold Formalism.REAL.muG
    infer_instance
  have hP := GlobalTheory.T.euclideanBallAsymptotics_finite_pi a (fun i => Fin (j i) → Fin (j i) → ℂ)
    (fun i => ENNReal.ofReal (2 ^ (j i ^ 2)) • haarLoc (j i)) _ (fun i => 2 * j i ^ 2)
    (fun i => measurable_hs_loc (j i)) (fun i x => add_nonneg (hs_nonneg' _) (hs_nonneg' _))
    (fun i => GlobalTheory.T.hasEuclideanBallVolume_haarComplexGL_inverse (j i))
  have h2 := GlobalTheory.T.hasEuclideanBallVolumeSublevelAsymptotics_prod _ _ _ _ _ _ _ _
    (Finset.measurable_sum _ fun i _ => (measurable_hs_loc (j i)).comp (measurable_pi_apply i))
    (measurable_hs_uMat ε₀)
    (fun x => Finset.sum_nonneg fun i _ => add_nonneg (hs_nonneg' _) (hs_nonneg' _))
    (fun g => hs_nonneg' _) hP hG
  have hd : n₀ ^ 2 + 2 * ∑ i, j i ^ 2 = ∑ i, 2 * j i ^ 2 + n₀ ^ 2 := by
    rw [Finset.mul_sum, add_comm]
  rw [hd]
  have hae1 : ∀ᵐ x ∂(Measure.pi fun i => ENNReal.ofReal (2 ^ (j i ^ 2)) • haarLoc (j i)),
      ∀ i, (Matrix.of (x i)).det ≠ 0 := by
    refine ae_all_iff.2 fun i => ?_
    have h0 : ∀ᵐ y ∂(haarLoc (j i)), (Matrix.of y).det ≠ 0 := by
      rw [ae_iff]
      simpa using (haarLoc_conj_and_null (j i)).2
    exact (Measure.quasiMeasurePreserving_eval
      (fun i => ENNReal.ofReal (2 ^ (j i ^ 2)) • haarLoc (j i)) i).ae (Measure.ae_smul_measure h0 _)
  have hae := (Measure.quasiMeasurePreserving_fst (ν := ENNReal.ofReal c • Formalism.REAL.muG ε₀)).ae hae1
  unfold IsRadial at h2 ⊢
  refine h2.congr fun r => ?_
  rw [Measure.map_apply hθ (measurableSet_le (measurable_hs_uMat ε).sqrt measurable_const)]
  congr 1
  refine measure_congr ?_
  filter_upwards [hae] with z hz
  have e := hs_lev_sub_one n n₀ a j ε ε₀ B B₀ hF (fun i => Matrix.of (z.1 i)) (uMat z.2)
  rw [← hθe z hz] at e
  exact Iff.of_eq (congrArg (fun t => Real.sqrt t ≤ r) e.symm)

end GlobalTheory.LeviIso.MapRadial
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsRadialMapUnitaryLeviBlockProductStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isRadial_map_unitaryLeviBlockProduct : ∀ (n n₀ a : ℕ) (j : Fin a → ℕ) (ε : Fin n → Bool) (ε₀ : Fin n₀ → Bool) (B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (B₀ : Matrix (Fin n) (Fin n₀) ℂ), IsFrame ε ε₀ B B₀ → ∀ θ : (∀ i, Fin (j i) → Fin (j i) → ℂ) × Formalism.REAL.UJ ε₀ → Formalism.REAL.UJ ε, Measurable θ → (∀ z, (∀ i, (Matrix.of (z.1 i)).det ≠ 0) → uMat (θ z) = lev ε B B₀ (fun i => Matrix.of (z.1 i)) (uMat z.2)) → ∀ c : ℝ, IsGauge ε₀ c → IsRadial (((Measure.pi fun i => ENNReal.ofReal (2 ^ (j i ^ 2)) • haarLoc (j i)).prod (ENNReal.ofReal c • Formalism.REAL.muG ε₀)).map θ) (fun g => Formalism.REAL.hs (uMat g - 1)) (n₀ ^ 2 + 2 * ∑ i, j i ^ 2) := by
  first | exact @GlobalTheory.LeviIso.MapRadial.isRadial_map_lev | exact GlobalTheory.LeviIso.MapRadial.isRadial_map_lev | (intros; apply GlobalTheory.LeviIso.MapRadial.isRadial_map_lev <;> assumption)
end
