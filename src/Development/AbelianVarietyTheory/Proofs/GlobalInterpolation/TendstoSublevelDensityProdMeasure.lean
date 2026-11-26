module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ContinuousMatrixEntryAbsSum
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DisjointSpanPerpLat

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TendstoSublevelDensityProdMeasure
open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot
open scoped ENNReal NNReal

namespace GlobalTheory.SublevelDensity

private lemma mul_prod_sublevel_add_le_of_fst_sublevel_le {A A' B : Type*} [MeasurableSpace A] [MeasurableSpace A']
    [MeasurableSpace B] (m : Measure A) (m' : Measure A') (μ : Measure B) [SFinite m]
    [SFinite m'] [SFinite μ] (n : A → ℝ) (n' : A' → ℝ) (g : B → ℝ) (hn : Measurable n)
    (hn' : Measurable n') (hg : Measurable g) (hn0 : ∀ x, 0 ≤ n x) (hn0' : ∀ x, 0 ≤ n' x)
    (hg0 : ∀ y, 0 ≤ g y) (a b : ℝ≥0∞) (r : ℝ)
    (h : ∀ s, 0 < s → s ≤ r → a * m {x | n x < s} ≤ b * m' {x | n' x < s}) :
    a * (m.prod μ) {p | n p.1 + g p.2 < r} ≤ b * (m'.prod μ) {p | n' p.1 + g p.2 < r} := by
  have hS : MeasurableSet {p : A × B | n p.1 + g p.2 < r} :=
    measurableSet_lt ((hn.comp measurable_fst).add (hg.comp measurable_snd)) measurable_const
  have hS' : MeasurableSet {p : A' × B | n' p.1 + g p.2 < r} :=
    measurableSet_lt ((hn'.comp measurable_fst).add (hg.comp measurable_snd)) measurable_const
  rw [Measure.prod_apply_symm hS, Measure.prod_apply_symm hS']
  calc a * ∫⁻ y, m ((fun x => (x, y)) ⁻¹' {p : A × B | n p.1 + g p.2 < r}) ∂μ
      ≤ ∫⁻ y, a * m ((fun x => (x, y)) ⁻¹' {p : A × B | n p.1 + g p.2 < r}) ∂μ :=
        lintegral_const_mul_le _ _
    _ ≤ ∫⁻ y, b * m' ((fun x => (x, y)) ⁻¹' {p : A' × B | n' p.1 + g p.2 < r}) ∂μ := by
        refine lintegral_mono fun y => ?_
        simp only [Set.preimage_setOf_eq]
        by_cases hy : r ≤ g y
        · have e1 : {x | n x + g y < r} = ∅ := by
            ext x
            simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
            linarith [hn0 x]
          have e2 : {x | n' x + g y < r} = ∅ := by
            ext x
            simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
            linarith [hn0' x]
          rw [e1, e2]
          simp
        · push_neg at hy
          have e1 : {x | n x + g y < r} = {x | n x < r - g y} := by
            ext x
            simp only [Set.mem_setOf_eq]
            constructor <;> intro hx <;> linarith
          have e2 : {x | n' x + g y < r} = {x | n' x < r - g y} := by
            ext x
            simp only [Set.mem_setOf_eq]
            constructor <;> intro hx <;> linarith
          rw [e1, e2]
          exact h _ (by linarith) (by linarith [hg0 y])
    _ = b * ∫⁻ y, m' ((fun x => (x, y)) ⁻¹' {p : A' × B | n' p.1 + g p.2 < r}) ∂μ :=
        lintegral_const_mul _ (measurable_measure_prodMk_right hS')

private lemma mul_prod_sublevel_add_le_of_snd_sublevel_le {A B B' : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace B'] (μ : Measure A) (m : Measure B) (m' : Measure B') [SFinite m]
    [SFinite m'] (g : A → ℝ) (n : B → ℝ) (n' : B' → ℝ) (hg : Measurable g) (hn : Measurable n)
    (hn' : Measurable n') (hg0 : ∀ x, 0 ≤ g x) (hn0 : ∀ y, 0 ≤ n y) (hn0' : ∀ y, 0 ≤ n' y)
    (a b : ℝ≥0∞) (r : ℝ)
    (h : ∀ s, 0 < s → s ≤ r → a * m {y | n y < s} ≤ b * m' {y | n' y < s}) :
    a * (μ.prod m) {p | g p.1 + n p.2 < r} ≤ b * (μ.prod m') {p | g p.1 + n' p.2 < r} := by
  have hS : MeasurableSet {p : A × B | g p.1 + n p.2 < r} :=
    measurableSet_lt ((hg.comp measurable_fst).add (hn.comp measurable_snd)) measurable_const
  have hS' : MeasurableSet {p : A × B' | g p.1 + n' p.2 < r} :=
    measurableSet_lt ((hg.comp measurable_fst).add (hn'.comp measurable_snd)) measurable_const
  rw [Measure.prod_apply hS, Measure.prod_apply hS']
  calc a * ∫⁻ x, m (Prod.mk x ⁻¹' {p : A × B | g p.1 + n p.2 < r}) ∂μ
      ≤ ∫⁻ x, a * m (Prod.mk x ⁻¹' {p : A × B | g p.1 + n p.2 < r}) ∂μ :=
        lintegral_const_mul_le _ _
    _ ≤ ∫⁻ x, b * m' (Prod.mk x ⁻¹' {p : A × B' | g p.1 + n' p.2 < r}) ∂μ := by
        refine lintegral_mono fun x => ?_
        simp only [Set.preimage_setOf_eq]
        by_cases hx : r ≤ g x
        · have e1 : {y | g x + n y < r} = ∅ := by
            ext y
            simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
            linarith [hn0 y]
          have e2 : {y | g x + n' y < r} = ∅ := by
            ext y
            simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
            linarith [hn0' y]
          rw [e1, e2]
          simp
        · push_neg at hx
          have e1 : {y | g x + n y < r} = {y | n y < r - g x} := by
            ext y
            simp only [Set.mem_setOf_eq]
            constructor <;> intro hy <;> linarith
          have e2 : {y | g x + n' y < r} = {y | n' y < r - g x} := by
            ext y
            simp only [Set.mem_setOf_eq]
            constructor <;> intro hy <;> linarith
          rw [e1, e2]
          exact h _ (by linarith) (by linarith [hg0 x])
    _ = b * ∫⁻ x, m' (Prod.mk x ⁻¹' {p : A × B' | g p.1 + n' p.2 < r}) ∂μ :=
        lintegral_const_mul _ (measurable_measure_prodMk_left hS')

theorem _root_.GlobalTheory.SublevelDensity.tendsto_prod_density : ∀ (A₁ E₁ A₂ E₂ : Type) [MeasurableSpace A₁] [MeasurableSpace E₁] [MeasurableSpace A₂] [MeasurableSpace E₂] (m₁ : Measure A₁) (l₁ : Measure E₁) (m₂ : Measure A₂) (l₂ : Measure E₂) [SFinite m₁] [SFinite l₁] [SFinite m₂] [SFinite l₂] (n₁ : A₁ → ℝ) (N₁ : E₁ → ℝ) (n₂ : A₂ → ℝ) (N₂ : E₂ → ℝ) (c₁ c₂ : ℝ≥0∞), Measurable n₁ → Measurable N₁ → Measurable n₂ → Measurable N₂ → (∀ x, 0 ≤ n₁ x) → (∀ x, 0 ≤ N₁ x) → (∀ x, 0 ≤ n₂ x) → (∀ x, 0 ≤ N₂ x) → c₁ ≠ ⊤ → c₂ ≠ ⊤ → (∀ r : ℝ, 0 < r → l₁ {x | N₁ x < r} ≠ 0 ∧ l₁ {x | N₁ x < r} ≠ ⊤) → (∀ r : ℝ, 0 < r → l₂ {x | N₂ x < r} ≠ 0 ∧ l₂ {x | N₂ x < r} ≠ ⊤) → Tendsto (fun r : ℝ => m₁ {x | n₁ x < r} / l₁ {x | N₁ x < r}) (𝓝[>] 0) (𝓝 c₁) → Tendsto (fun r : ℝ => m₂ {x | n₂ x < r} / l₂ {x | N₂ x < r}) (𝓝[>] 0) (𝓝 c₂) → Tendsto (fun r : ℝ => (m₁.prod m₂) {p | n₁ p.1 + n₂ p.2 < r} / (l₁.prod l₂) {p | N₁ p.1 + N₂ p.2 < r}) (𝓝[>] 0) (𝓝 (c₁ * c₂)) := by
  intro A₁ E₁ A₂ E₂ _ _ _ _ m₁ l₁ m₂ l₂ _ _ _ _ n₁ N₁ n₂ N₂ c₁ c₂ hn₁ hN₁ hn₂ hN₂ hn₁0 hN₁0
    hn₂0 hN₂0 hc₁ hc₂ hl₁ hl₂ h₁ h₂
  have hG : ∀ r : ℝ, 0 < r → (l₁.prod l₂) {p | N₁ p.1 + N₂ p.2 < r} ≠ 0 ∧
      (l₁.prod l₂) {p | N₁ p.1 + N₂ p.2 < r} ≠ ⊤ := by
    intro r hr
    constructor
    · have hsub : {x | N₁ x < r / 2} ×ˢ {y | N₂ y < r / 2} ⊆
          {p : E₁ × E₂ | N₁ p.1 + N₂ p.2 < r} := by
        rintro ⟨x, y⟩ ⟨hx, hy⟩
        simp only [Set.mem_setOf_eq] at hx hy ⊢
        linarith
      refine ne_of_gt (lt_of_lt_of_le ?_ (measure_mono hsub))
      rw [Measure.prod_prod]
      exact ENNReal.mul_pos (hl₁ _ (half_pos hr)).1 (hl₂ _ (half_pos hr)).1
    · have hsub : {p : E₁ × E₂ | N₁ p.1 + N₂ p.2 < r} ⊆ {x | N₁ x < r} ×ˢ {y | N₂ y < r} := by
        rintro ⟨x, y⟩ hxy
        simp only [Set.mem_setOf_eq, Set.mem_prod] at hxy ⊢
        constructor <;> linarith [hN₁0 x, hN₂0 y]
      refine ne_top_of_le_ne_top ?_ (measure_mono hsub)
      rw [Measure.prod_prod]
      exact ENNReal.mul_ne_top (hl₁ r hr).2 (hl₂ r hr).2
  rw [tendsto_order]
  constructor
  · intro a ha
    have hc0 : c₁ * c₂ ≠ 0 := (lt_of_le_of_lt bot_le ha).ne'
    have hc₁0 : c₁ ≠ 0 := left_ne_zero_of_mul hc0
    have hc₂0 : c₂ ≠ 0 := right_ne_zero_of_mul hc0
    have hlim : Tendsto (fun t : ℝ≥0∞ => (c₁ - t) * (c₂ - t)) (𝓝[>] 0) (𝓝 (c₁ * c₂)) := by
      have t1 := (ENNReal.continuous_sub_left hc₁).tendsto 0
      have t2 := (ENNReal.continuous_sub_left hc₂).tendsto 0
      simp only [tsub_zero] at t1 t2
      exact ENNReal.Tendsto.mul (t1.mono_left nhdsWithin_le_nhds) (Or.inr hc₂)
        (t2.mono_left nhdsWithin_le_nhds) (Or.inr hc₁)
    obtain ⟨t, ht, htpos⟩ := ((hlim.eventually (lt_mem_nhds ha)).and self_mem_nhdsWithin).exists
    have htpos' : (0 : ℝ≥0∞) < t := htpos
    have ha₁ : c₁ - t < c₁ := ENNReal.sub_lt_self hc₁ hc₁0 htpos'.ne'
    have ha₂ : c₂ - t < c₂ := ENNReal.sub_lt_self hc₂ hc₂0 htpos'.ne'
    obtain ⟨δ₁, hδ₁, hsub₁⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 ((tendsto_order.1 h₁).1 _ ha₁)
    obtain ⟨δ₂, hδ₂, hsub₂⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 ((tendsto_order.1 h₂).1 _ ha₂)
    have hδ : (0 : ℝ) < min δ₁ δ₂ := lt_min hδ₁ hδ₂
    filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
    obtain ⟨hr0, hrδ⟩ := hr
    have k₁ : ∀ s, 0 < s → s ≤ r → (c₁ - t) * l₁ {x | N₁ x < s} ≤ 1 * m₁ {x | n₁ x < s} := by
      intro s hs hsr
      have hs' : (c₁ - t) < m₁ {x | n₁ x < s} / l₁ {x | N₁ x < s} :=
        hsub₁ ⟨hs, lt_of_le_of_lt hsr (lt_of_lt_of_le hrδ (min_le_left _ _))⟩
      rw [one_mul]
      exact ((ENNReal.lt_div_iff_mul_lt (Or.inl (hl₁ s hs).1) (Or.inl (hl₁ s hs).2)).1 hs').le
    have k₂ : ∀ s, 0 < s → s ≤ r → (c₂ - t) * l₂ {x | N₂ x < s} ≤ 1 * m₂ {x | n₂ x < s} := by
      intro s hs hsr
      have hs' : (c₂ - t) < m₂ {x | n₂ x < s} / l₂ {x | N₂ x < s} :=
        hsub₂ ⟨hs, lt_of_le_of_lt hsr (lt_of_lt_of_le hrδ (min_le_right _ _))⟩
      rw [one_mul]
      exact ((ENNReal.lt_div_iff_mul_lt (Or.inl (hl₂ s hs).1) (Or.inl (hl₂ s hs).2)).1 hs').le
    have s₁ := mul_prod_sublevel_add_le_of_fst_sublevel_le l₁ m₁ m₂ N₁ n₁ n₂ hN₁ hn₁ hn₂ hN₁0 hn₁0 hn₂0 _ 1 r k₁
    have s₂ := mul_prod_sublevel_add_le_of_snd_sublevel_le l₁ l₂ m₂ N₁ N₂ n₂ hN₁ hN₂ hn₂ hN₁0 hN₂0 hn₂0 _ 1 r k₂
    rw [one_mul] at s₁ s₂
    have key : ((c₁ - t) * (c₂ - t)) * (l₁.prod l₂) {p | N₁ p.1 + N₂ p.2 < r} ≤
        (m₁.prod m₂) {p | n₁ p.1 + n₂ p.2 < r} :=
      calc ((c₁ - t) * (c₂ - t)) * (l₁.prod l₂) {p | N₁ p.1 + N₂ p.2 < r}
          = (c₁ - t) * ((c₂ - t) * (l₁.prod l₂) {p | N₁ p.1 + N₂ p.2 < r}) := mul_assoc _ _ _
        _ ≤ (c₁ - t) * (l₁.prod m₂) {p | N₁ p.1 + n₂ p.2 < r} := by gcongr
        _ ≤ (m₁.prod m₂) {p | n₁ p.1 + n₂ p.2 < r} := s₁
    exact lt_of_lt_of_le ht
      ((ENNReal.le_div_iff_mul_le (Or.inl (hG r hr0).1) (Or.inl (hG r hr0).2)).2 key)
  · intro b hb
    have hlim : Tendsto (fun t : ℝ≥0∞ => (c₁ + t) * (c₂ + t)) (𝓝[>] 0) (𝓝 (c₁ * c₂)) := by
      have t1 : Tendsto (fun t : ℝ≥0∞ => c₁ + t) (𝓝 0) (𝓝 (c₁ + 0)) :=
        (continuous_const.add continuous_id).tendsto 0
      have t2 : Tendsto (fun t : ℝ≥0∞ => c₂ + t) (𝓝 0) (𝓝 (c₂ + 0)) :=
        (continuous_const.add continuous_id).tendsto 0
      rw [add_zero] at t1 t2
      exact ENNReal.Tendsto.mul (t1.mono_left nhdsWithin_le_nhds) (Or.inr hc₂)
        (t2.mono_left nhdsWithin_le_nhds) (Or.inr hc₁)
    obtain ⟨t, ht, htpos⟩ := ((hlim.eventually (gt_mem_nhds hb)).and self_mem_nhdsWithin).exists
    have htpos' : (0 : ℝ≥0∞) < t := htpos
    have hb₁ : c₁ < c₁ + t := ENNReal.lt_add_right hc₁ htpos'.ne'
    have hb₂ : c₂ < c₂ + t := ENNReal.lt_add_right hc₂ htpos'.ne'
    obtain ⟨δ₁, hδ₁, hsub₁⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 ((tendsto_order.1 h₁).2 _ hb₁)
    obtain ⟨δ₂, hδ₂, hsub₂⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 ((tendsto_order.1 h₂).2 _ hb₂)
    have hδ : (0 : ℝ) < min δ₁ δ₂ := lt_min hδ₁ hδ₂
    filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
    obtain ⟨hr0, hrδ⟩ := hr
    have k₁ : ∀ s, 0 < s → s ≤ r → 1 * m₁ {x | n₁ x < s} ≤ (c₁ + t) * l₁ {x | N₁ x < s} := by
      intro s hs hsr
      have hs' : m₁ {x | n₁ x < s} / l₁ {x | N₁ x < s} < c₁ + t :=
        hsub₁ ⟨hs, lt_of_le_of_lt hsr (lt_of_lt_of_le hrδ (min_le_left _ _))⟩
      rw [one_mul]
      exact ((ENNReal.div_lt_iff (Or.inl (hl₁ s hs).1) (Or.inl (hl₁ s hs).2)).1 hs').le
    have k₂ : ∀ s, 0 < s → s ≤ r → 1 * m₂ {x | n₂ x < s} ≤ (c₂ + t) * l₂ {x | N₂ x < s} := by
      intro s hs hsr
      have hs' : m₂ {x | n₂ x < s} / l₂ {x | N₂ x < s} < c₂ + t :=
        hsub₂ ⟨hs, lt_of_le_of_lt hsr (lt_of_lt_of_le hrδ (min_le_right _ _))⟩
      rw [one_mul]
      exact ((ENNReal.div_lt_iff (Or.inl (hl₂ s hs).1) (Or.inl (hl₂ s hs).2)).1 hs').le
    have s₁ := mul_prod_sublevel_add_le_of_fst_sublevel_le m₁ l₁ m₂ n₁ N₁ n₂ hn₁ hN₁ hn₂ hn₁0 hN₁0 hn₂0 1 _ r k₁
    have s₂ := mul_prod_sublevel_add_le_of_snd_sublevel_le l₁ m₂ l₂ N₁ n₂ N₂ hN₁ hn₂ hN₂ hN₁0 hn₂0 hN₂0 1 _ r k₂
    rw [one_mul] at s₁ s₂
    have key : (m₁.prod m₂) {p | n₁ p.1 + n₂ p.2 < r} ≤
        ((c₁ + t) * (c₂ + t)) * (l₁.prod l₂) {p | N₁ p.1 + N₂ p.2 < r} :=
      calc (m₁.prod m₂) {p | n₁ p.1 + n₂ p.2 < r}
          ≤ (c₁ + t) * (l₁.prod m₂) {p | N₁ p.1 + n₂ p.2 < r} := s₁
        _ ≤ (c₁ + t) * ((c₂ + t) * (l₁.prod l₂) {p | N₁ p.1 + N₂ p.2 < r}) :=
          by gcongr
        _ = ((c₁ + t) * (c₂ + t)) * (l₁.prod l₂) {p | N₁ p.1 + N₂ p.2 < r} :=
          (mul_assoc _ _ _).symm
    exact lt_of_le_of_lt (ENNReal.div_le_of_le_mul key) ht

end GlobalTheory.SublevelDensity
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RestrHomSurjective
noncomputable section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal

namespace GlobalTheory.UnitVectorStabiliser

section General

open Formalism.UG

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
  (s : A →+* A) (J : Matrix n n A)

theorem hf_add_right (x y z : n → A) : hform s J x (y + z) = hform s J x y + hform s J x z := by
  simp only [hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hf_add_left (x y z : n → A) : hform s J (x + y) z = hform s J x z + hform s J y z := by
  simp only [hform, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem hf_smul_right (c : A) (x y : n → A) : hform s J x (c • y) = c * hform s J x y := by
  simp only [hform, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hf_smul_left (c : A) (x y : n → A) : hform s J (c • x) y = s c * hform s J x y := by
  simp only [hform, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hf_herm (hs : ∀ a, s (s a) = a) (hJ : ∀ i j, s (J j i) = J i j) (x y : n → A) :
    s (hform s J x y) = hform s J y x := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hform, map_sum, map_mul, hs]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ]
  ring

theorem hf_eq (x y : n → A) : hform s J x y = (fun i => s (x i)) ⬝ᵥ (J *ᵥ y) := by
  simp only [hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hf_mulVec (g : Matrix n n A) (x y : n → A) :
    hform s J (g *ᵥ x) (g *ᵥ y) = hform s (cT s g * J * g) x y := by
  rw [hf_eq, hf_eq, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec _ (cT s g)]
  congr 1
  funext i
  simp [cT, Matrix.vecMul, Matrix.mulVec, dotProduct, mul_comm]

theorem hf_single (i j : n) : hform s J (Pi.single i 1) (Pi.single j 1) = J i j := by
  simp [hform, Pi.single_apply, apply_ite]

def hfLin (x : n → A) : (n → A) →ₗ[A] A where
  toFun := hform s J x
  map_add' := hf_add_right s J x
  map_smul' c y := hf_smul_right s J c x y

theorem exists_proj (x : n → A) (hx : IsUnit (hform s J x x)) (P : Submodule A (n → A))
    (hP : ∀ y, y ∈ P ↔ hform s J x y = 0) :
    ∃ (c : (n → A) →ₗ[A] A) (p : (n → A) →ₗ[A] P), (∀ y, y = c y • x + (p y : n → A)) ∧
      c x = 1 ∧ ∀ y : P, c y = 0 := by
  obtain ⟨b, hb⟩ := hx.exists_left_inv
  refine ⟨b • hfLin s J x,
    LinearMap.codRestrict P (LinearMap.id - (b • hfLin s J x).smulRight x) fun y => ?_,
    fun y => ?_, hb, fun y => ?_⟩
  · rw [hP]
    show hfLin s J x (y - (b * hfLin s J x y) • x) = 0
    rw [map_sub, map_smul, smul_eq_mul]
    have : b * hfLin s J x x = 1 := hb
    linear_combination (- hfLin s J x y) * this
  · show y = (b * hfLin s J x y) • x + (y - (b * hfLin s J x y) • x)
    abel
  · show b * hform s J x y = 0
    rw [(hP y).1 y.2, mul_zero]

theorem exists_extend (hs : ∀ a, s (s a) = a) (hJ : ∀ i j, s (J j i) = J i j)
    (hd : IsUnit J.det) (x : n → A) (hx : IsUnit (hform s J x x)) (P : Submodule A (n → A))
    (hP : ∀ y, y ∈ P ↔ hform s J x y = 0) (u : P →ₗ[A] P)
    (hu : ∀ y z : P, hform s J (u y) (u z) = hform s J y z) :
    ∃ g : GL n A, g ∈ UJ s J ∧ (g : Matrix n n A) *ᵥ x = x ∧
      ∀ y : P, (g : Matrix n n A) *ᵥ y = u y := by
  obtain ⟨c, p, h1, h2, h3⟩ := exists_proj s J x hx P hP
  let f : (n → A) →ₗ[A] (n → A) := c.smulRight x + P.subtype ∘ₗ u ∘ₗ p
  have hf : ∀ y, f y = c y • x + (u (p y) : n → A) := fun y => rfl
  have o1 : ∀ y : P, hform s J x y = 0 := fun y => (hP y).1 y.2
  have o2 : ∀ y : P, hform s J y x = 0 := fun y => by rw [← hf_herm s J hs hJ, o1, map_zero]
  have hiso : ∀ y z, hform s J (f y) (f z) = hform s J y z := by
    intro y z
    conv_rhs => rw [h1 y, h1 z]
    simp only [hf, hf_add_left, hf_add_right, hf_smul_left, hf_smul_right, o1, o2, hu]
  have hg : cT s (LinearMap.toMatrix' f) * J * LinearMap.toMatrix' f = J := by
    ext i j
    rw [← hf_single s (cT s (LinearMap.toMatrix' f) * J * LinearMap.toMatrix' f) i j, ← hf_mulVec, LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec, hiso,
      hf_single]
  have hdet : IsUnit (LinearMap.toMatrix' f).det := by
    rw [← hg, Matrix.det_mul] at hd
    exact isUnit_of_mul_isUnit_right hd
  obtain ⟨g, hg'⟩ := (Matrix.isUnit_iff_isUnit_det _).2 hdet
  refine ⟨g, ?_, ?_, fun y => ?_⟩
  · show cT s (g : Matrix n n A) * J * (g : Matrix n n A) = J
    rw [hg', hg]
  · have : p x = 0 := by
      have := h1 x
      rw [h2, one_smul] at this
      exact Subtype.ext (by simpa using this)
    rw [hg', LinearMap.toMatrix'_mulVec, hf, h2, this]
    simp
  · have : p y = y := by
      have := h1 y
      rw [h3, zero_smul, zero_add] at this
      exact Subtype.ext this.symm
    rw [hg', LinearMap.toMatrix'_mulVec, hf, h3, this]
    simp

end General

section Place

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (v : HeightOneSpectrum (𝓞 F))

theorem mem_stabVec (x : Fin M → Ev F E v) (g : HA (Fv F v) σ J) :
    g ∈ stabVec σ J v x ↔ act σ J v g x = x := by
  unfold stabVec
  rw [MulAction.mem_stabilizer_iff]
  exact ⟨fun h => congrFun h 0, fun h => funext fun _ => h⟩

theorem act_mul (g h : HA (Fv F v) σ J) (x : Fin M → Ev F E v) :
    act σ J v (g * h) x = act σ J v g (act σ J v h x) := by
  unfold act
  rw [Matrix.mulVec_mulVec]; rfl

theorem act_one (x : Fin M → Ev F E v) : act σ J v 1 x = x := Matrix.one_mulVec x

theorem hR_act (g : HA (Fv F v) σ J) (y z : Fin M → Ev F E v) :
    hR (Fv F v) σ J (act σ J v g y) (act σ J v g z) = hR (Fv F v) σ J y z := by
  unfold hR act
  rw [hf_mulVec]
  congr 1
  exact (show HR (Fv F v) σ J from g).2

theorem act_mem_perp_iff (x : Fin M → Ev F E v) (g : HA (Fv F v) σ J) (hg : g ∈ stabVec σ J v x)
    (y : Fin M → Ev F E v) : act σ J v g y ∈ perp σ J v x ↔ y ∈ perp σ J v x := by
  show hR (Fv F v) σ J x (act σ J v g y) = 0 ↔ hR (Fv F v) σ J x y = 0
  rw [← hR_act σ J v g x y, (mem_stabVec σ J v x g).1 hg]

def restr (x : Fin M → Ev F E v) (g : HA (Fv F v) σ J) (hg : g ∈ stabVec σ J v x) :
    perp σ J v x ≃ₗ[Ev F E v] perp σ J v x where
  toFun y := ⟨act σ J v g y, (act_mem_perp_iff σ J v x g hg y).2 y.2⟩
  invFun y := ⟨act σ J v g⁻¹ y, (act_mem_perp_iff σ J v x g⁻¹ (inv_mem hg) y).2 y.2⟩
  map_add' y z := Subtype.ext (by
    show act σ J v g (y.1 + z.1) = act σ J v g y.1 + act σ J v g z.1
    unfold act
    rw [Matrix.mulVec_add])
  map_smul' c y := Subtype.ext (by
    show act σ J v g (c • y.1) = c • act σ J v g y.1
    unfold act
    rw [Matrix.mulVec_smul])
  left_inv y := Subtype.ext (by
    show act σ J v g⁻¹ (act σ J v g y) = y
    rw [← act_mul, inv_mul_cancel, act_one])
  right_inv y := Subtype.ext (by
    show act σ J v g (act σ J v g⁻¹ y) = y
    rw [← act_mul, mul_inv_cancel, act_one])

def restrHom (L' : Submodule (OEv F E v) (Fin M → Ev F E v)) (x : Fin M → Ev F E v) :
    (stabLat σ J v L' ⊓ stabVec σ J v x : Subgroup (HA (Fv F v) σ J)) →*
      unitaryLatIn σ J v (perp σ J v x) L' where
  toFun g := ⟨restr σ J v x g g.2.2, fun y z => hR_act σ J v g y z, fun y => g.2.1 y⟩
  map_one' := Subtype.ext (LinearEquiv.ext fun y => Subtype.ext (act_one σ J v y))
  map_mul' g h := Subtype.ext (LinearEquiv.ext fun y => Subtype.ext (act_mul σ J v g h y))

theorem restrHom_injective (L' : Submodule (OEv F E v) (Fin M → Ev F E v)) (x : Fin M → Ev F E v)
    (hx : IsUnit (hR (Fv F v) σ J x x)) : Function.Injective (restrHom σ J v L' x) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  obtain ⟨c, p, h1, -, -⟩ := exists_proj _ _ x hx (perp σ J v x) (fun _ => Iff.rfl)
  have h0 : ∀ y : perp σ J v x, act σ J v g y = y := fun y =>
    congrArg (fun u : unitaryLatIn σ J v (perp σ J v x) L' =>
      ((u.1 y : perp σ J v x) : Fin M → Ev F E v)) hg
  have hx' := (mem_stabVec σ J v x g).1 g.2.2
  have h2 : ∀ y, act σ J v g y = y := by
    intro y
    rw [h1 y]
    have := h0 (p y)
    unfold act at *
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, hx', this]
  refine Subtype.ext (Subtype.ext (Units.ext ?_))
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun y => ?_
  exact (h2 y).trans (act_one σ J v y).symm

theorem restrHom_surjective (h : IsCMExt F E σ) (hJ : IsHermND σ J)
    (L : Submodule (OEv F E v) (Fin M → Ev F E v)) (x : Fin M → Ev F E v)
    (hx : IsUnit (hR (Fv F v) σ J x x)) :
    Function.Surjective (restrHom σ J v (perpLat σ J v L x) x) := by
  rintro ⟨u, hu, hu'⟩
  have hJ' : ∀ i j, sigR (Fv F v) σ (JR (Fv F v) J j i) = JR (Fv F v) J i j := by
    intro i j
    show (1 : Fv F v) ⊗ₜ[F] σ (J j i) = (1 : Fv F v) ⊗ₜ[F] J i j
    rw [hJ.1]
  have hd : IsUnit (JR (F := F) (Fv F v) J).det := by
    have := (RingHom.map_det (inclR (F := F) (Fv F v)) J)
    rw [show JR (F := F) (Fv F v) J = (inclR (F := F) (Fv F v)).mapMatrix J from rfl, ← this]
    exact (hJ.2.isUnit).map _
  obtain ⟨g, hg, hgx, hgu⟩ := exists_extend _ _
    (GlobalTheory.SelfDualLatticeCompare.sigR_sigR (Fv F v) h) hJ' hd x hx (perp σ J v x)
    (fun _ => Iff.rfl) u.toLinearMap hu
  let g' : HA (Fv F v) σ J := (⟨g, hg⟩ : HR (Fv F v) σ J)
  have hv : g' ∈ stabVec σ J v x := (mem_stabVec σ J v x g').2 hgx
  have hgu' : ∀ y : perp σ J v x, act σ J v g' y = u y := hgu
  have hl : g' ∈ stabLat σ J v (perpLat σ J v L x) := by
    show ∀ y, y ∈ perpLat σ J v L x ↔ act σ J v g' y ∈ perpLat σ J v L x
    intro y
    by_cases hy : y ∈ perp σ J v x
    · rw [hgu' ⟨y, hy⟩]
      exact hu' ⟨y, hy⟩
    · exact ⟨fun h => (hy h.1).elim,
        fun h => (hy ((act_mem_perp_iff σ J v x g' hv y).1 h.1)).elim⟩
  exact ⟨⟨g', hl, hv⟩, Subtype.ext (LinearEquiv.ext fun y => Subtype.ext (hgu' y))⟩

end Place

theorem stabiliser_iso : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)) (L : Submodule (OEv F E v) (Fin M → Ev F E v)), ∀ x : Fin M → Ev F E v, IsUnit (hR (Fv F v) σ J x x) → ∃ φ : (stabLat σ J v (perpLat σ J v L x) ⊓ stabVec σ J v x : Subgroup (HA (Fv F v) σ J)) ≃* unitaryLatIn σ J v (perp σ J v x) (perpLat σ J v L x), ∀ g (y : perp σ J v x), (((φ g : perp σ J v x ≃ₗ[Ev F E v] perp σ J v x) y : perp σ J v x) : Fin M → Ev F E v) = act σ J v (g : HA (Fv F v) σ J) y := by
  intro F E _ _ _ _ _ σ h M J hJ v L x hx
  exact ⟨MulEquiv.ofBijective (restrHom σ J v (perpLat σ J v L x) x)
    ⟨restrHom_injective σ J v _ x hx, restrHom_surjective σ J v h hJ L x hx⟩, fun _ _ => rfl⟩

end GlobalTheory.UnitVectorStabiliser
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HermitianNormFibreMeasureEqPolarCoordinates
noncomputable section

namespace GlobalTheory.FibrePolar

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding
  GlobalTheory.CompactDualQuot
open scoped ENNReal NNReal

theorem restrict_eq {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) (f : V → ℝ)
    (O U U' : Set V) (fib fib' : ℝ → Measure V) (β : ℝ)
    (hf : Measurable f) (hO : IsOpen O) (hU : O ⊆ U) (hU' : O ⊆ U')
    (h : IsFibreFamily μ f id U (volume : Measure ℝ) Set.univ fib)
    (h' : IsFibreFamily μ f id U' (volume : Measure ℝ) Set.univ fib') :
    (fib β).restrict O = (fib' β).restrict O := by
  haveI : ProperSpace V := FiniteDimensional.proper_real V
  have hc0 : ∀ n : Measure V, n.restrict O Oᶜ = 0 := fun n => by
    rw [Measure.restrict_apply hO.measurableSet.compl]; simp
  refine measure_eq_of_lintegral_eq_on_compactSupport _ _ O hO (hc0 _) (hc0 _) ?_
  intro φ hφ hc hs h0
  obtain ⟨hi, hg⟩ := h.2.2 φ hφ hc (hs.trans hU)
  obtain ⟨hi', hg'⟩ := h'.2.2 φ hφ hc (hs.trans hU')
  refine ⟨(hi β trivial).restrict, ?_⟩
  have hφm : Measurable fun v => ENNReal.ofReal (φ v) :=
    ENNReal.measurable_ofReal.comp hφ.measurable
  have hφ0 : ∀ v, v ∉ O → ENNReal.ofReal (φ v) = 0 := by
    intro v hv
    rw [image_eq_zero_of_notMem_tsupport fun h => hv (hs h), ENNReal.ofReal_zero]
  have hr : ∀ n : Measure V, ∫⁻ v in O, ENNReal.ofReal (φ v) ∂n =
      ∫⁻ v, ENNReal.ofReal (φ v) ∂n := fun n =>
    setLIntegral_eq_of_support_subset fun v hv => by
      by_contra hvO; exact hv (hφ0 v hvO)
  rw [hr, hr]
  have c : ContinuousOn (fun b => ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib b)) Set.univ :=
    (ENNReal.continuous_ofReal.comp_continuousOn hg).congr fun b hb =>
      (ofReal_integral_eq_lintegral_ofReal (hi b hb) (Filter.Eventually.of_forall h0)).symm
  have c' : ContinuousOn (fun b => ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib' b)) Set.univ :=
    (ENNReal.continuous_ofReal.comp_continuousOn hg').congr fun b hb =>
      (ofReal_integral_eq_lintegral_ofReal (hi' b hb) (Filter.Eventually.of_forall h0)).symm
  have hae : (fun b => ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib b)) =ᵐ[volume.restrict Set.univ]
      (fun b => ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib' b)) := by
    refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite₀ (c.aemeasurable MeasurableSet.univ)
      (c'.aemeasurable MeasurableSet.univ) fun S hS _ => ?_
    rw [Measure.restrict_univ,
      ← IsFibreFamily_lintegral_preimage hf hO hU h _ hφm hφ0 _ hS,
      ← IsFibreFamily_lintegral_preimage hf hO hU' h' _ hφm hφ0 _ hS]
  exact Measure.eqOn_open_of_ae_eq hae isOpen_univ c c' trivial

variable {P Q P' Q' : ℕ}

theorem continuous_qf : Continuous (qf : Sp P Q → ℝ) := by
  unfold qf
  fun_prop

def glue (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (p : ℂ × Sp P' Q') : Sp P Q :=
  fun i => (e.symm i).elim p.1 p.2

@[simp] theorem glue_none (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (p : ℂ × Sp P' Q') :
    glue e p (e none) = p.1 := by simp [glue]

@[simp] theorem glue_some (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (p : ℂ × Sp P' Q')
    (i : Fin P' ⊕ Fin Q') : glue e p (e (some i)) = p.2 i := by simp [glue]

theorem continuous_glue (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) :
    Continuous (glue e) := by
  refine continuous_pi fun i => ?_
  obtain ⟨j, rfl⟩ := e.surjective i
  rcases j with _ | j
  · simp only [glue_none]; fun_prop
  · simp only [glue_some]; fun_prop

theorem measurePreserving_glue (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) :
    MeasurePreserving (glue e) ((volume : Measure ℂ).prod volume) volume := by
  refine ⟨(continuous_glue e).measurable, ?_⟩
  rw [volume_pi (α := fun _ : Fin P ⊕ Fin Q => ℂ)]
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply (continuous_glue e).measurable (MeasurableSet.univ_pi hs)]
  have : glue e ⁻¹' Set.pi Set.univ s =
      s (e none) ×ˢ Set.pi Set.univ (fun i => s (e (some i))) := by
    ext p
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_imp_iff, Set.mem_prod]
    rw [e.surjective.forall, Option.forall]
    simp
  rw [this, Measure.prod_prod, volume_pi_pi, ← e.prod_comp, Fintype.prod_option]

theorem norm_le_glue (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (p : ℂ × Sp P' Q') :
    ‖p.2‖ ≤ ‖glue e p‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  simpa using norm_le_pi_norm (glue e p) (e (some i))

theorem qf_glue {e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)} (he : SignCompat e)
    (p : ℂ × Sp P' Q') : qf (glue e p) = sg (e none) * Complex.normSq p.1 + qf p.2 := by
  rw [qf_eq_sum, qf_eq_sum, ← e.sum_comp, Fintype.sum_option]
  simp only [glue_none, glue_some, he _]

def pt (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (a : ℝ × (ℝ × Sp P' Q')) : Sp P Q :=
  glue e ((Real.sqrt (sg (e none) * (a.1 - qf a.2.2)) : ℂ) *
    Complex.exp ((a.2.1 : ℂ) * Complex.I), a.2.2)

theorem continuous_pt (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) : Continuous (pt e) := by
  have := @continuous_qf P' Q'
  exact (continuous_glue e).comp (by fun_prop)

theorem pt_sg (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (p : ℝ × Sp P' Q') :
    pt e (sg (e none), p) = polarPt e p := by
  have : sg (e none) * (sg (e none) - qf p.2) = 1 - sg (e none) * qf p.2 := by
    rcases sg_eq (e none) with h | h <;> rw [h] <;> ring
  simp only [pt, this]
  rfl

def base (P' Q' : ℕ) : Measure (ℝ × Sp P' Q') :=
  ((volume : Measure ℝ).restrict (Set.Ioo (-Real.pi) Real.pi)).prod volume

def fam (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (t : ℝ) : Measure (Sp P Q) :=
  ((2 : ℝ≥0∞) ^ (P' + Q')) •
    ((base P' Q').map fun p => pt e (t, p)).restrict {y | y (e none) ≠ 0}

theorem isFibreFamily_fam {e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)} (he : SignCompat e) :
    IsFibreFamily (dx P Q) (qf : Sp P Q → ℝ) id {y | y (e none) ≠ 0} (volume : Measure ℝ)
      Set.univ (fam e) := by
  have hO : IsOpen {y : Sp P Q | y (e none) ≠ 0} :=
    isOpen_ne_fun (continuous_apply _) continuous_const
  set O := {y : Sp P Q | y (e none) ≠ 0} with hOdef
  have hk : ((2 : ℝ≥0∞) ^ (P' + Q')) ≠ ⊤ := by simp
  have hpt := continuous_pt e
  have hpt' : ∀ t, Continuous fun p => pt e (t, p) := fun t => hpt.comp (by fun_prop)
  have hε := sg_eq (e none)
  refine ⟨fun t => ?_, fun φ hφ => ?_, fun φ hφ hs ht => ?_⟩
  · have hS : MeasurableSet (qf ⁻¹' {id t} ∩ O)ᶜ :=
      ((continuous_qf.measurable (measurableSet_singleton t)).inter hO.measurableSet).compl
    rw [fam, Measure.smul_apply, Measure.restrict_apply hS,
      Measure.map_apply (hpt' t).measurable (hS.inter hO.measurableSet)]
    have : (fun p => pt e (t, p)) ⁻¹' ((qf ⁻¹' {id t} ∩ O)ᶜ ∩ O) = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun p hp => hp.1 ⟨?_, hp.2⟩
      have h : 0 < sg (e none) * (t - qf p.2) := by
        by_contra h
        exact hp.2 (by simp [pt, Real.sqrt_eq_zero_of_nonpos (not_lt.1 h)])
      have hn : Complex.normSq ((Real.sqrt (sg (e none) * (t - qf p.2)) : ℂ) *
          Complex.exp ((p.1 : ℂ) * Complex.I)) = sg (e none) * (t - qf p.2) := by
        rw [map_mul, Complex.normSq_ofReal, Real.mul_self_sqrt h.le, Complex.normSq_eq_norm_sq,
          Complex.norm_exp_ofReal_mul_I]; simp
      change qf (glue e _) = t
      rw [qf_glue he, hn]
      rcases hε with h1 | h1 <;> rw [h1] <;> ring
    rw [this, measure_empty, smul_zero]
  · have hG : Measurable (O.indicator φ) := hφ.indicator hO.measurableSet
    have hJ := hG.comp hpt.measurable
    have e1 : ∀ t, ∫⁻ v, φ v ∂(fam e t) = (2 : ℝ≥0∞) ^ (P' + Q') *
        ∫⁻ y, ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, O.indicator φ (pt e (t, θ, y)) := fun t => by
      rw [fam, lintegral_smul_measure, ← lintegral_indicator hO.measurableSet,
        lintegral_map hG (hpt' t).measurable, base,
        lintegral_prod_symm' (fun p => O.indicator φ (pt e (t, p)))
          (hG.comp (hpt' t).measurable), smul_eq_mul]
    simp only [e1]
    rw [lintegral_const_mul' _ _ hk, ← lintegral_indicator hO.measurableSet, dx,
      lintegral_smul_measure, smul_eq_mul, card_eq e, pow_succ, mul_assoc]
    congr 1
    rw [← (measurePreserving_glue e).lintegral_comp hG,
      lintegral_prod_symm' (fun a => O.indicator φ (glue e a))
        (hG.comp (continuous_glue e).measurable), ← lintegral_const_mul' _ _ (by simp)]
    symm
    rw [lintegral_lintegral_swap]
    · refine lintegral_congr fun y => Eq.symm ?_
      rw [lintegral_complex_eq_lintegral_sqrt_mul_exp (sg (e none)) (qf y) hε
        (fun z => O.indicator φ (glue e (z, y)))
        (hG.comp ((continuous_glue e).measurable.comp measurable_prodMk_right))
        (Set.indicator_of_notMem (by simp [hOdef]) _), ← lintegral_const_mul' _ _ (by simp)]
      refine lintegral_congr fun t => ?_
      rw [lintegral_const_mul' _ _ (by simp), ← mul_assoc,
        ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]
      rfl
    · refine Measurable.aemeasurable ?_
      refine Measurable.lintegral_prod_right' (f := fun a : (ℝ × Sp P' Q') × ℝ =>
        O.indicator φ (pt e (a.1.1, a.2, a.1.2))) ?_
      exact hJ.comp (by fun_prop)
  · obtain ⟨C, hC⟩ := hφ.bounded_above_of_compact_support hs
    obtain ⟨R, hR⟩ := hs.isCompact.isBounded.subset_closedBall 0
    let b : ℝ × Sp P' Q' → ℝ := (Set.univ ×ˢ Metric.closedBall 0 R).indicator fun _ => C
    have hb : Integrable b (base P' Q') := by
      refine (integrable_indicator_iff
        (MeasurableSet.univ.prod Metric.isClosed_closedBall.measurableSet)).2
        (integrableOn_const ?_ (by simp))
      rw [base, Measure.prod_prod]
      exact ENNReal.mul_ne_top (measure_ne_top _ _) measure_closedBall_lt_top.ne
    have hle : ∀ t p, ‖φ (pt e (t, p))‖ ≤ b p := fun t p => by
      by_cases h : p ∈ (Set.univ : Set ℝ) ×ˢ Metric.closedBall (0 : Sp P' Q') R
      · simp only [b, Set.indicator_of_mem h]; exact hC _
      · simp only [b, Set.indicator_of_notMem h]
        rw [image_eq_zero_of_notMem_tsupport (f := φ), norm_zero]
        intro h1
        exact h ⟨trivial, mem_closedBall_zero_iff.2 ((norm_le_glue e (_, p.2)).trans
          (mem_closedBall_zero_iff.1 (hR h1)))⟩
    have hm : ∀ t, AEStronglyMeasurable (fun p => φ (pt e (t, p))) (base P' Q') := fun t =>
      (hφ.comp (hpt' t)).aestronglyMeasurable
    constructor
    · intro t _
      refine Integrable.smul_measure (Integrable.restrict ?_) hk
      rw [integrable_map_measure hφ.aestronglyMeasurable (hpt' t).aemeasurable]
      exact hb.mono' (hm t) (ae_of_all _ (hle t))
    · have e2 : ∀ t, ∫ x, φ x ∂(fam e t) =
          ((2 : ℝ≥0∞) ^ (P' + Q')).toReal * ∫ p, φ (pt e (t, p)) ∂(base P' Q') := fun t => by
        rw [fam, integral_smul_measure, setIntegral_eq_integral_of_forall_compl_eq_zero
          (fun x hx => image_eq_zero_of_notMem_tsupport fun h => hx (ht h)),
          integral_map (hpt' t).aemeasurable hφ.aestronglyMeasurable, smul_eq_mul]
      simp only [e2]
      exact (continuous_const.mul (continuous_of_dominated hm (fun t => ae_of_all _ (hle t)) hb
        (ae_of_all _ fun p => hφ.comp (hpt.comp (by fun_prop))))).continuousOn

theorem fibre_eq_polar : ∀ (P Q P' Q' : ℕ) (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)),
    SignCompat e → ∀ fib : ℝ → Measure (Sp P Q), IsDxDq fib → ∀ S : Set (Sp P Q),
      MeasurableSet S → (∀ y ∈ S, y (e none) ≠ 0) →
      fib (sg (e none)) S = (2 : ℝ≥0∞) ^ (P' + Q') * (volume : Measure (ℝ × Sp P' Q'))
        {t | t.1 ∈ Set.Ioo (-Real.pi) Real.pi ∧ polarPt e t ∈ S} := by
  intro P Q P' Q' e he fib hfib S hS hS0
  have hO : IsOpen {y : Sp P Q | y (e none) ≠ 0} :=
    isOpen_ne_fun (continuous_apply _) continuous_const
  have key := restrict_eq (dx P Q) qf {y | y (e none) ≠ 0} {x | x ≠ 0} _ fib (fam e) (sg (e none))
    continuous_qf.measurable hO (fun y hy h0 => hy (congrFun h0 _)) subset_rfl hfib
    (isFibreFamily_fam he)
  have hsub : S ⊆ {y | y (e none) ≠ 0} := hS0
  have hm : Measurable fun p => pt e (sg (e none), p) :=
    ((continuous_pt e).comp (by fun_prop)).measurable
  rw [← Measure.restrict_eq_self _ hsub, key, Measure.restrict_eq_self _ hsub, fam,
    Measure.smul_apply, Measure.restrict_eq_self _ hsub, Measure.map_apply hm hS, smul_eq_mul,
    base, Measure.restrict_prod_eq_prod_univ, Measure.restrict_apply (hm hS),
    ← Measure.volume_eq_prod]
  congr 2
  ext p
  simp [pt_sg, and_comm]

end GlobalTheory.FibrePolar
end
end
