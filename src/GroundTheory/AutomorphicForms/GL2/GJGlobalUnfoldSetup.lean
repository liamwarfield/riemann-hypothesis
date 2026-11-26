module

public import GroundTheory.AutomorphicForms.GL2.GJGlobalDefs
public import GroundTheory.AutomorphicForms.GL2.GJGlobalUnfoldRank

@[expose] public section

section -- merged from GroundTheory.AutomorphicForms.GL2.GJGlobalUnfoldCount
open MeasureTheory Set Function
open scoped ENNReal

namespace GroundTheory.Automorphic.GJGlobal

noncomputable section

namespace Unfold

theorem tsum_eq_tsum_quotient {α : Type*} [Group α] (s : Subgroup α) (f : α → ℝ≥0∞) :
    ∑' a, f a = ∑' c : α ⧸ s, ∑' b : s, f (c.out * b) := by
  have hbij : Bijective (fun x : (α ⧸ s) × s => x.1.out * (x.2 : α)) := by
    constructor
    · rintro ⟨c, b⟩ ⟨c', b'⟩ hx
      simp only at hx
      have hc : c = c' := by
        have h1 : (QuotientGroup.mk (c.out * (b : α)) : α ⧸ s) = c := by
          rw [QuotientGroup.mk_mul_of_mem _ b.2, QuotientGroup.out_eq']
        have h2 : (QuotientGroup.mk (c'.out * (b' : α)) : α ⧸ s) = c' := by
          rw [QuotientGroup.mk_mul_of_mem _ b'.2, QuotientGroup.out_eq']
        rw [← h1, ← h2, hx]
      subst hc
      exact Prod.ext rfl (Subtype.ext (mul_left_cancel hx))
    · intro a
      refine ⟨(QuotientGroup.mk a, ⟨(QuotientGroup.mk a : α ⧸ s).out⁻¹ * a, ?_⟩), ?_⟩
      · rw [← QuotientGroup.eq, QuotientGroup.out_eq']
      · simp
  rw [← (Equiv.ofBijective _ hbij).tsum_eq]
  exact ENNReal.tsum_prod (f := fun (c : α ⧸ s) (b : s) => f (c.out * b))

variable {G : Type*} [Group G] [MeasurableSpace G]
  {V : Type*} [AddCommGroup V] [MeasurableSpace V]

structure Hyp (ν : Measure V) (u : V → G) (L : AddSubgroup V) (D : Set V) (Λ : Subgroup G)
    (E : Set G) (S : G → V →+ V) : Prop where
  map_add : ∀ X Y, u (X + Y) = u X * u Y
  injective : Injective u
  measurable : Measurable u
  isAddFundamentalDomain : IsAddFundamentalDomain L D ν
  measurableSet_D : MeasurableSet D
  measurableSet_E : MeasurableSet E
  existsUnique : ∀ g : G, ∃! p : Λ, (p : G) * g ∈ E
  mem : ∀ ξ ∈ L, u ξ ∈ Λ
  conj : ∀ q ∈ Λ, ∀ Z, q⁻¹ * u Z * q = u (S q Z)
  mapsTo : ∀ q ∈ Λ, ∀ ξ ∈ L, S q ξ ∈ L
  measurePreserving : ∀ q ∈ Λ, MeasurePreserving (S q) ν ν

namespace Hyp

variable {ν : Measure V} {u : V → G} {L : AddSubgroup V} {D : Set V} {Λ : Subgroup G} {E : Set G}
  {S : G → V →+ V}

theorem map_zero (h : Hyp ν u L D Λ E S) : u 0 = 1 := by
  have h0 := h.map_add 0 0
  rw [add_zero] at h0
  exact mul_eq_left.1 h0.symm

theorem map_neg (h : Hyp ν u L D Λ E S) (X : V) : u (-X) = (u X)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← h.map_add, neg_add_cancel, h.map_zero])

theorem S_S_inv (h : Hyp ν u L D Λ E S) {q : G} (hq : q ∈ Λ) (Z : V) : S q (S q⁻¹ Z) = Z := by
  apply h.injective
  rw [← h.conj q hq, ← h.conj q⁻¹ (inv_mem hq)]
  simp [mul_assoc]

def unipSubgroup (h : Hyp ν u L D Λ E S) : Subgroup Λ where
  carrier := {p | ∃ ξ ∈ L, u ξ = p}
  one_mem' := ⟨0, L.zero_mem, h.map_zero⟩
  mul_mem' := by
    rintro _ _ ⟨ξ, hξ, hξe⟩ ⟨η, hη, hηe⟩
    exact ⟨ξ + η, L.add_mem hξ hη, by rw [h.map_add, hξe, hηe]; rfl⟩
  inv_mem' := by
    rintro _ ⟨ξ, hξ, hξe⟩
    exact ⟨-ξ, L.neg_mem hξ, by rw [h.map_neg, hξe]; rfl⟩

def unipEquiv (h : Hyp ν u L D Λ E S) : L ≃ h.unipSubgroup :=
  Equiv.ofBijective (fun ξ => ⟨⟨u ξ, h.mem ξ ξ.2⟩, ⟨ξ, ξ.2, rfl⟩⟩)
    ⟨fun _ _ hξη => Subtype.ext (h.injective (congrArg (fun x : h.unipSubgroup => ((x : Λ) : G)) hξη)),
      fun ⟨_, ξ, hξ, hξe⟩ => ⟨⟨ξ, hξ⟩, Subtype.ext (Subtype.ext hξe)⟩⟩

theorem coe_unipEquiv (h : Hyp ν u L D Λ E S) (ξ : L) : (((h.unipEquiv ξ : h.unipSubgroup) : Λ) : G) = u ξ :=
  rfl

def latticeEquiv (h : Hyp ν u L D Λ E S) {q : G} (hq : q ∈ Λ) : L ≃ L where
  toFun η := ⟨S q (-η), h.mapsTo q hq _ (L.neg_mem η.2)⟩
  invFun ξ := ⟨-S q⁻¹ ξ, L.neg_mem (h.mapsTo q⁻¹ (inv_mem hq) _ ξ.2)⟩
  left_inv η := by
    refine Subtype.ext ?_
    have := h.S_S_inv (inv_mem hq) (-(η : V))
    rw [inv_inv] at this
    show -S q⁻¹ (S q (-(η : V))) = η
    rw [this, neg_neg]
  right_inv ξ := by
    refine Subtype.ext ?_
    simp [h.S_S_inv hq]

end Hyp

section Counting

set_option linter.unusedSectionVars false

variable [MeasurableMul G] [MeasurableAdd V] [MeasurableNeg V]
  {ν : Measure V} [ν.IsAddLeftInvariant] [ν.IsNegInvariant] [SFinite ν]
  {u : V → G} {L : AddSubgroup V} {D : Set V} {Λ : Subgroup G} {E : Set G} {S : G → V →+ V}
  [Countable Λ] [Countable L]

namespace Hyp

theorem measurable_indicator (h : Hyp ν u L D Λ E S) (q g : G) :
    Measurable (fun Z : V => E.indicator (1 : G → ℝ≥0∞) (q * u Z * g)) :=
  (measurable_one.indicator h.measurableSet_E).comp ((h.measurable.const_mul q).mul_const g)

theorem tsum_setLIntegral_right (h : Hyp ν u L D Λ E S) (q g : G) :
    ∑' ξ : L, ∫⁻ Y in D, E.indicator 1 (q * u ξ * u Y * g) ∂ν =
      ∫⁻ Z, E.indicator 1 (q * u Z * g) ∂ν := by
  rw [h.isAddFundamentalDomain.lintegral_eq_tsum'' (fun Z => E.indicator 1 (q * u Z * g))]
  refine tsum_congr fun ξ => setLIntegral_congr_fun h.measurableSet_D (fun Y _ => ?_)
  rw [AddSubgroup.vadd_def, vadd_eq_add, h.map_add, ← mul_assoc]

theorem tsum_setLIntegral_left (h : Hyp ν u L D Λ E S) {q : G} (hq : q ∈ Λ) (g : G) :
    ∑' ξ : L, ∫⁻ X in D, E.indicator 1 (u (-X) * (q * u ξ) * g) ∂ν =
      ∫⁻ Z, E.indicator 1 (q * u Z * g) ∂ν := by
  have key : ∀ (X : V) (η : L), u (-X) * (q * u ((h.latticeEquiv hq η : L) : V)) * g =
      q * u (S q (-((η : V) + X))) * g := by
    intro X η
    have e1 : ((h.latticeEquiv hq η : L) : V) = S q (-(η : V)) := rfl
    have e2 : S q (-((η : V) + X)) = S q (-X) + S q (-(η : V)) := by
      rw [neg_add, _root_.map_add (S q), add_comm]
    rw [e1, e2, h.map_add, ← h.conj q hq (-X)]
    simp only [mul_assoc, mul_inv_cancel_left]
  rw [← (h.latticeEquiv hq).tsum_eq]
  simp_rw [key]
  have hmp : MeasurePreserving (fun W : V => S q (-W)) ν ν :=
    (h.measurePreserving q hq).comp (Measure.measurePreserving_neg ν)
  rw [← hmp.lintegral_comp (h.measurable_indicator q g),
    h.isAddFundamentalDomain.lintegral_eq_tsum'' (fun W => E.indicator 1 (q * u (S q (-W)) * g))]
  refine tsum_congr fun η => setLIntegral_congr_fun h.measurableSet_D (fun X _ => ?_)
  rw [AddSubgroup.vadd_def, vadd_eq_add]

theorem tsum_setLIntegral_indicator (h : Hyp ν u L D Λ E S) (g : G) :
    ∑' p : Λ, ∫⁻ X in D, E.indicator 1 (u (-X) * p * g) ∂ν = ν D := by
  have hb : ∑' p : Λ, ∫⁻ Y in D, E.indicator 1 ((p : G) * u Y * g) ∂ν = ν D := by
    rw [← lintegral_tsum fun p : Λ => (h.measurable_indicator (p : G) g).aemeasurable]
    have hone : ∀ Y, ∑' p : Λ, E.indicator (1 : G → ℝ≥0∞) ((p : G) * u Y * g) = 1 := by
      intro Y
      obtain ⟨p, hp, hpu⟩ := h.existsUnique (u Y * g)
      rw [tsum_eq_single p]
      · rw [mul_assoc, indicator_of_mem hp]
        rfl
      · intro p' hp'
        rw [mul_assoc, indicator_of_notMem]
        exact fun hm => hp' (hpu p' hm)
    simp_rw [hone]
    simp
  rw [← hb, tsum_eq_tsum_quotient h.unipSubgroup,
    tsum_eq_tsum_quotient h.unipSubgroup (fun p : Λ => ∫⁻ Y in D, E.indicator 1 ((p : G) * u Y * g) ∂ν)]
  refine tsum_congr fun c => ?_
  rw [← h.unipEquiv.tsum_eq, ← h.unipEquiv.tsum_eq]
  simp only [Subgroup.coe_mul, coe_unipEquiv]
  rw [h.tsum_setLIntegral_left c.out.2 g, h.tsum_setLIntegral_right]

end Hyp

end Counting

section Integral

set_option linter.unusedSectionVars false

variable [MeasurableMul G] [MeasurableMul₂ G] [MeasurableAdd V] [MeasurableNeg V]
  {ν : Measure V} [ν.IsAddLeftInvariant] [ν.IsNegInvariant] [SFinite ν]
  {μ : Measure G} [μ.IsMulLeftInvariant] [SFinite μ]
  {u : V → G} {L : AddSubgroup V} {D : Set V} {Λ : Subgroup G} {E : Set G} {S : G → V →+ V}
  [Countable Λ] [Countable L]

namespace Hyp

theorem isFundamentalDomain (h : Hyp ν u L D Λ E S) : IsFundamentalDomain Λ E μ :=
  IsFundamentalDomain.mk' h.measurableSet_E.nullMeasurableSet h.existsUnique

theorem measurable_indicator_prod (h : Hyp ν u L D Λ E S) :
    Measurable (fun p : V × G => E.indicator (1 : G → ℝ≥0∞) (u (-p.1) * p.2)) :=
  (measurable_one.indicator h.measurableSet_E).comp
    (((h.measurable.comp measurable_neg).comp measurable_fst).mul measurable_snd)

def weight (ν : Measure V) (u : V → G) (D : Set V) (E : Set G) (g : G) : ℝ≥0∞ :=
  ∫⁻ X in D, E.indicator 1 (u (-X) * g) ∂ν

theorem measurable_weight (h : Hyp ν u L D Λ E S) : Measurable (weight ν u D E) :=
  (h.measurable_indicator_prod).lintegral_prod_left'

theorem tsum_weight (h : Hyp ν u L D Λ E S) (g : G) : ∑' p : Λ, weight ν u D E (p * g) = ν D := by
  rw [← h.tsum_setLIntegral_indicator g]
  refine tsum_congr fun p => ?_
  simp only [weight, mul_assoc]

omit [MeasurableMul G] [MeasurableMul₂ G] [MeasurableAdd V] [MeasurableNeg V] [ν.IsAddLeftInvariant]
  [ν.IsNegInvariant] [SFinite ν] [Countable Λ] [Countable L] in
theorem weight_le (g : G) : weight ν u D E g ≤ ν D := by
  calc weight ν u D E g ≤ ∫⁻ _ in D, 1 ∂ν :=
        lintegral_mono fun X => indicator_le_self' (fun _ _ => zero_le_one) _
    _ = ν D := by simp

theorem setLIntegral_comp_mul (h : Hyp ν u L D Λ E S) (X : V) (H : G → ℝ≥0∞) :
    ∫⁻ g in E, H (u X * g) ∂μ = ∫⁻ g, E.indicator 1 (u (-X) * g) * H g ∂μ := by
  rw [← lintegral_indicator h.measurableSet_E,
    ← lintegral_mul_left_eq_self (fun g => E.indicator 1 (u (-X) * g) * H g) (u X)]
  refine lintegral_congr fun g => ?_
  simp only [← mul_assoc]
  rw [← h.map_add, neg_add_cancel, h.map_zero, one_mul]
  by_cases hg : g ∈ E <;> simp [hg]

theorem lintegral_weight_mul (h : Hyp ν u L D Λ E S) {H : G → ℝ≥0∞} (hH : Measurable H)
    (hΛ : ∀ p ∈ Λ, ∀ g, H (p * g) = H g) :
    ∫⁻ g, weight ν u D E g * H g ∂μ = ν D * ∫⁻ g in E, H g ∂μ := by
  rw [(h.isFundamentalDomain (μ := μ)).lintegral_eq_tsum'', ← lintegral_tsum]
  · rw [← lintegral_const_mul _ hH]
    refine setLIntegral_congr_fun h.measurableSet_E (fun g _ => ?_)
    simp only [Subgroup.smul_def, smul_eq_mul]
    have : ∀ p : Λ, weight ν u D E (p * g) * H (p * g) = weight ν u D E (p * g) * H g :=
      fun p => by rw [hΛ p p.2 g]
    simp_rw [this]
    rw [ENNReal.tsum_mul_right, h.tsum_weight]
  · intro p
    exact ((h.measurable_weight.mul hH).comp (measurable_const_mul (p : G))).aemeasurable.restrict

theorem lintegral_indicator_mul (h : Hyp ν u L D Λ E S) {H : G → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ X in D, ∫⁻ g, E.indicator 1 (u (-X) * g) * H g ∂μ ∂ν = ∫⁻ g, weight ν u D E g * H g ∂μ := by
  rw [lintegral_lintegral_swap ((h.measurable_indicator_prod.mul (hH.comp measurable_snd)).aemeasurable)]
  refine lintegral_congr fun g => ?_
  have hm : Measurable (fun X : V => E.indicator (1 : G → ℝ≥0∞) (u (-X) * g)) :=
    h.measurable_indicator_prod.comp (measurable_id.prodMk measurable_const)
  rw [lintegral_mul_const _ hm]
  rfl

theorem lintegral_setLIntegral_eq (h : Hyp ν u L D Λ E S) {H : G → ℝ≥0∞} (hH : Measurable H)
    (hΛ : ∀ p ∈ Λ, ∀ g, H (p * g) = H g) :
    ∫⁻ X in D, ∫⁻ g in E, H (u X * g) ∂μ ∂ν = ν D * ∫⁻ g in E, H g ∂μ := by
  simp_rw [h.setLIntegral_comp_mul]
  rw [h.lintegral_indicator_mul hH, h.lintegral_weight_mul hH hΛ]

theorem enorm_indicator_real (x : G) :
    ‖((E.indicator (1 : G → ℝ) x : ℝ) : ℂ)‖ₑ = E.indicator (1 : G → ℝ≥0∞) x := by
  by_cases hx : x ∈ E <;> simp [hx]

omit [MeasurableMul G] [MeasurableMul₂ G] [MeasurableAdd V] [MeasurableNeg V] [ν.IsAddLeftInvariant]
  [ν.IsNegInvariant] [SFinite ν] [Countable Λ] [Countable L] [μ.IsMulLeftInvariant] [SFinite μ] in
theorem enorm_toReal_coe {w : ℝ≥0∞} (hw : w ≠ ∞) : ‖((w.toReal : ℝ) : ℂ)‖ₑ = w := by
  rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal hw]

theorem integral_indicator_real (h : Hyp ν u L D Λ E S) (g : G) :
    ∫ X in D, E.indicator (1 : G → ℝ) (u (-X) * g) ∂ν = (weight ν u D E g).toReal := by
  have hm : Measurable (fun X : V => E.indicator (1 : G → ℝ) (u (-X) * g)) :=
    (measurable_one.indicator h.measurableSet_E).comp
      ((h.measurable.comp measurable_neg).mul_const g)
  refine (integral_eq_lintegral_of_nonneg_ae (f := fun X => E.indicator (1 : G → ℝ) (u (-X) * g))
    (Filter.Eventually.of_forall fun X => indicator_nonneg (fun _ _ => zero_le_one) _)
    hm.aestronglyMeasurable).trans ?_
  congr 1
  refine lintegral_congr fun X => ?_
  by_cases hX : u (-X) * g ∈ E <;> simp [hX]

theorem integral_setIntegral_eq (h : Hyp ν u L D Λ E S) {Ψ : G → ℂ} (hΨ : Measurable Ψ)
    (hΛ : ∀ p ∈ Λ, ∀ g, Ψ (p * g) = Ψ g) (hint : ∫⁻ g in E, ‖Ψ g‖ₑ ∂μ < ∞) (hDtop : ν D ≠ ∞) :
    ∫ X in D, ∫ g in E, Ψ (u X * g) ∂μ ∂ν = (ν D).toReal * ∫ g in E, Ψ g ∂μ := by
  set ind : V → G → ℂ := fun X g => ((E.indicator (1 : G → ℝ) (u (-X) * g) : ℝ) : ℂ) with hind
  have hmind : Measurable (uncurry ind) := by
    refine Complex.measurable_ofReal.comp ?_
    exact (measurable_one.indicator h.measurableSet_E).comp
      (((h.measurable.comp measurable_neg).comp measurable_fst).mul measurable_snd)
  have hHm : Measurable fun g => ‖Ψ g‖ₑ := hΨ.enorm
  have hHΛ : ∀ p ∈ Λ, ∀ g, ‖Ψ (p * g)‖ₑ = ‖Ψ g‖ₑ := fun p hp g => by rw [hΛ p hp g]

  have hfin : ∫⁻ g, weight ν u D E g * ‖Ψ g‖ₑ ∂μ < ∞ := by
    rw [h.lintegral_weight_mul hHm hHΛ]
    exact ENNReal.mul_lt_top hDtop.lt_top hint

  have ha : ∀ X, ∫ g in E, Ψ (u X * g) ∂μ = ∫ g, ind X g * Ψ g ∂μ := by
    intro X
    rw [← integral_indicator h.measurableSet_E,
      ← integral_mul_left_eq_self (fun g => ind X g * Ψ g) (u X)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [hind, ← mul_assoc]
    rw [← h.map_add, neg_add_cancel, h.map_zero, one_mul]
    by_cases hg : g ∈ E <;> simp [hg]
  simp_rw [ha]

  have hm0 : Measurable (uncurry fun X g => ind X g * Ψ g) := hmind.mul (hΨ.comp measurable_snd)
  have hI : Integrable (uncurry fun X g => ind X g * Ψ g) ((ν.restrict D).prod μ) := by
    refine ⟨hm0.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral, lintegral_prod _ hm0.enorm.aemeasurable]
    simp only [uncurry_apply_pair, enorm_mul, hind, enorm_indicator_real]
    rw [h.lintegral_indicator_mul hHm]
    exact hfin
  rw [integral_integral_swap hI]

  have hc : ∀ g, ∫ X in D, ind X g * Ψ g ∂ν = ((weight ν u D E g).toReal : ℂ) * Ψ g := by
    intro g
    rw [integral_mul_const, hind]
    simp only
    rw [integral_complex_ofReal, h.integral_indicator_real]
  simp_rw [hc]

  have hwm : Measurable fun g => ((weight ν u D E g).toReal : ℂ) * Ψ g :=
    (Complex.measurable_ofReal.comp h.measurable_weight.ennreal_toReal).mul hΨ
  have hen : ∀ g, ‖((weight ν u D E g).toReal : ℂ) * Ψ g‖ₑ = weight ν u D E g * ‖Ψ g‖ₑ := by
    intro g
    rw [enorm_mul, enorm_toReal_coe (ne_top_of_le_ne_top hDtop (weight_le g))]
  have hInt : Integrable (fun g => ((weight ν u D E g).toReal : ℂ) * Ψ g) μ := by
    refine ⟨hwm.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    simp_rw [hen]
    exact hfin
  rw [(h.isFundamentalDomain (μ := μ)).integral_eq_tsum'' _ hInt]
  simp only [Subgroup.smul_def, smul_eq_mul]
  have hinv : ∀ (p : Λ) g, ((weight ν u D E (p * g)).toReal : ℂ) * Ψ (p * g) =
      ((weight ν u D E (p * g)).toReal : ℂ) * Ψ g := fun p g => by rw [hΛ p p.2 g]
  simp_rw [hinv]
  rw [← integral_tsum, ← integral_const_mul]
  · refine setIntegral_congr_fun h.measurableSet_E (fun g _ => ?_)
    rw [tsum_mul_right, ← Complex.ofReal_tsum, ← ENNReal.tsum_toReal_eq
      (fun p => ne_top_of_le_ne_top hDtop (weight_le _)), h.tsum_weight]
  · intro p
    exact ((Complex.measurable_ofReal.comp
      (h.measurable_weight.comp (measurable_const_mul (p : G))).ennreal_toReal).mul
        hΨ).aestronglyMeasurable.restrict
  · have : ∀ p : Λ, ∫⁻ g in E, ‖((weight ν u D E (p * g)).toReal : ℂ) * Ψ g‖ₑ ∂μ =
        ∫⁻ g in E, weight ν u D E (p * g) * ‖Ψ g‖ₑ ∂μ := by
      intro p
      refine lintegral_congr fun g => ?_
      rw [enorm_mul, enorm_toReal_coe (ne_top_of_le_ne_top hDtop (weight_le _))]
    simp_rw [this]
    rw [← lintegral_tsum]
    · simp_rw [ENNReal.tsum_mul_right, h.tsum_weight]
      rw [lintegral_const_mul _ hHm]
      exact (ENNReal.mul_lt_top hDtop.lt_top hint).ne
    · intro p
      exact ((h.measurable_weight.comp (measurable_const_mul (p : G))).mul hHm).aemeasurable.restrict

theorem setIntegral_mul_eq_zero (h : Hyp ν u L D Λ E S) {ψ F : G → ℂ} (hψ : Measurable ψ)
    (hF : Measurable F) (hΛ : ∀ p ∈ Λ, ∀ g, ψ (p * g) * F (p * g) = ψ g * F g)
    (hFu : ∀ X g, F (u X * g) = F g) (hint : ∫⁻ g in E, ‖ψ g * F g‖ₑ ∂μ < ∞)
    (hct : ∀ g, ∫ X in D, ψ (u X * g) ∂ν = 0) (hD0 : ν D ≠ 0) (hDtop : ν D ≠ ∞) :
    ∫ g in E, ψ g * F g ∂μ = 0 := by
  have key := h.integral_setIntegral_eq (μ := μ) (Ψ := fun g => ψ g * F g) (hψ.mul hF) hΛ hint hDtop
  have hm : Measurable (uncurry fun (X : V) (g : G) => ψ (u X * g) * F g) :=
    (hψ.comp ((h.measurable.comp measurable_fst).mul measurable_snd)).mul (hF.comp measurable_snd)
  have hI : Integrable (uncurry fun (X : V) (g : G) => ψ (u X * g) * F g)
      ((ν.restrict D).prod (μ.restrict E)) := by
    refine ⟨hm.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral, lintegral_prod _ hm.enorm.aemeasurable]
    simp only [uncurry_apply_pair]
    have : ∀ X g, ‖ψ (u X * g) * F g‖ₑ = ‖ψ (u X * g) * F (u X * g)‖ₑ := fun X g => by rw [hFu]
    simp_rw [this]
    rw [h.lintegral_setLIntegral_eq (H := fun g => ‖ψ g * F g‖ₑ) (hψ.mul hF).enorm
      (fun p hp g => by rw [hΛ p hp g])]
    exact ENNReal.mul_lt_top hDtop.lt_top hint
  have hzero : ∫ X in D, ∫ g in E, ψ (u X * g) * F (u X * g) ∂μ ∂ν = 0 := by
    simp_rw [hFu]
    rw [integral_integral_swap hI]
    simp_rw [integral_mul_const, hct, zero_mul, integral_zero]
  rw [hzero] at key
  have hne : ((ν D).toReal : ℂ) ≠ 0 := by
    exact_mod_cast (ENNReal.toReal_pos hD0 hDtop).ne'
  exact (mul_eq_zero.1 key.symm).resolve_left hne

end Hyp

end Integral

end Unfold

end

end GroundTheory.Automorphic.GJGlobal
end

open MeasureTheory Set Function NumberField
open scoped ENNReal NNReal NumberField.AdeleRing

namespace GroundTheory.Automorphic.GJGlobal

noncomputable section

namespace UnfoldGL

open Reduction AutomorphicForm RightCosetSpace RankDecomp CuspidalSpectrum

theorem measurePreserving_of_mapsTo_lattice {V : Type*} [AddCommGroup V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [LocallyCompactSpace V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V] (ν : Measure V) [ν.IsAddHaarMeasure]
    {L : AddSubgroup V} [Countable L] {D : Set V} (hD : IsAddFundamentalDomain L D ν)
    (hDm : MeasurableSet D) (hD0 : ν D ≠ 0) (hDtop : ν D ≠ ∞) (φ : V ≃ₜ+ V)
    (hφ : ∀ ξ ∈ L, φ ξ ∈ L) (hφ' : ∀ ξ ∈ L, φ.symm ξ ∈ L) :
    MeasurePreserving φ ν ν := by
  have heq : ν.map φ = Measure.addHaarScalarFactor (ν.map φ) ν • ν :=
    Measure.isAddLeftInvariant_eq_smul _ _
  set c := Measure.addHaarScalarFactor (ν.map φ) ν with hcdef
  have hqmp : QuasiMeasurePreserving φ ν ν :=
    ⟨(map_continuous φ).measurable.aemeasurable, by rw [heq]; exact Measure.smul_absolutelyContinuous⟩
  have hfd : IsAddFundamentalDomain L (φ ⁻¹' D) ν := by
    refine hD.preimage_of_equiv hqmp (e := fun ξ : L => (⟨φ.symm ξ, hφ' _ ξ.2⟩ : L)) ?_ ?_
    · refine ⟨fun a b hab => ?_, fun b => ⟨⟨φ b, hφ _ b.2⟩, ?_⟩⟩
      · have := congrArg (fun x : L => φ (x : V)) hab
        simp only [ContinuousAddEquiv.apply_symm_apply] at this
        exact Subtype.ext this
      · exact Subtype.ext (φ.symm_apply_apply _)
    · intro ξ x
      simp [AddSubgroup.vadd_def, map_add (f := _)]
  have hmeas : ν (φ ⁻¹' D) = ν D := hfd.measure_eq hD
  have hc : (c : ℝ≥0∞) * ν D = 1 * ν D := by
    have := congrArg (fun m : Measure V => m D) heq
    rw [Measure.map_apply (map_continuous φ).measurable hDm, hmeas, smul_apply,
      ENNReal.smul_def, smul_eq_mul] at this
    rw [one_mul]
    exact this.symm
  have hc1 : c = 1 := by
    have := (ENNReal.mul_left_inj hD0 hDtop).1 hc
    exact_mod_cast this
  refine ⟨(map_continuous φ).measurable, ?_⟩
  rw [heq, hc1, one_smul]

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

theorem unipMeasure_unipFundamentalDomain_ne_zero (k : ℕ) :
    unipMeasure K n k (unipFundamentalDomain K n k) ≠ 0 := by
  rw [unipMeasure_unipFundamentalDomain]
  exact one_ne_zero

theorem unipMeasure_unipFundamentalDomain_ne_top (k : ℕ) :
    unipMeasure K n k (unipFundamentalDomain K n k) ≠ ∞ := by
  rw [unipMeasure_unipFundamentalDomain]
  exact ENNReal.one_ne_top

instance isNegInvariant_unipMeasure (k : ℕ) : (unipMeasure K n k).IsNegInvariant := by
  let φ : (UPos n k → 𝔸[K]) ≃ₜ+ (UPos n k → 𝔸[K]) :=
    { AddEquiv.neg (UPos n k → 𝔸[K]) with
      continuous_toFun := continuous_neg
      continuous_invFun := continuous_neg }
  have h := measurePreserving_of_mapsTo_lattice (unipMeasure K n k)
    isAddFundamentalDomain_unipFundamentalDomain measurableSet_unipFundamentalDomain
    (unipMeasure_unipFundamentalDomain_ne_zero k) (unipMeasure_unipFundamentalDomain_ne_top k) φ
    (fun ξ hξ => (unipLattice K n k).neg_mem hξ) (fun ξ hξ => (unipLattice K n k).neg_mem hξ)
  exact ⟨h.map_eq⟩

theorem unipOne_injective (k : ℕ) : Injective (unipOne (K := K) (n := n) k) := fun _ _ h =>
  unipGL_injective (congrArg Subtype.val h)


variable (K n) in
def ratOne : GL (Fin n) K →* normOneGL (K := K) (n := n) :=
  (AdelicGLn.diagonal K n).codRestrict (normOneGL (K := K) (n := n))
    (fun γ => rationalGL_le_normOneGL ⟨γ, rfl⟩)

theorem ratOne_injective : Injective (ratOne K n) := fun _ _ h =>
  AdelicGLn.diagonal_injective K n (congrArg Subtype.val h)

theorem mem_rationalGLOne_iff {x : normOneGL (K := K) (n := n)} : x ∈ rationalGLOne (K := K) (n := n) ↔ ∃ γ, ratOne K n γ = x := by
  constructor
  · rintro ⟨γ, hγ⟩
    exact ⟨γ, Subtype.ext hγ⟩
  · rintro ⟨γ, rfl⟩
    exact ⟨γ, rfl⟩

theorem coe_ratOne_matrix (γ : GL (Fin n) K) :
    (((ratOne K n γ : normOneGL (K := K) (n := n)) : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) =
      ratMat (γ : Matrix (Fin n) (Fin n) K) :=
  coe_diagonal γ

instance countable_GL : Countable (GL (Fin n) K) := by
  have := GroundTheory.Global.countable_numberField K
  have : Countable (Matrix (Fin n) (Fin n) K) := inferInstanceAs (Countable (Fin n → Fin n → K))
  exact Function.Injective.countable (f := fun γ : GL (Fin n) K => (γ : Matrix (Fin n) (Fin n) K))
    Units.val_injective


variable (K n) in
def parabolicOne (k : ℕ) : Subgroup (normOneGL (K := K) (n := n)) :=
  (parabolic (K := K) (n := n) k).map (ratOne K n)

theorem parabolicOne_le (k : ℕ) : parabolicOne K n k ≤ rationalGLOne (K := K) (n := n) := by
  rintro _ ⟨γ, -, rfl⟩
  exact mem_rationalGLOne_iff.2 ⟨γ, rfl⟩

instance countable_parabolicOne (k : ℕ) : Countable (parabolicOne K n k) := by
  have : ((parabolicOne K n k : Set (normOneGL (K := K) (n := n)))).Countable := by
    rw [parabolicOne, Subgroup.coe_map]
    exact (Set.countable_univ.mono (Set.subset_univ _)).image _
  exact this.to_subtype

instance discreteTopology_parabolicOne (k : ℕ) : DiscreteTopology (parabolicOne K n k) :=
  DiscreteTopology.of_subset (s := (rationalGLOne (K := K) (n := n) : Set (normOneGL (K := K) (n := n))))
    discreteTopology_rationalGLOne (parabolicOne_le k)

theorem mem_parabolicOne_iff {k : ℕ} {q : normOneGL (K := K) (n := n)} :
    q ∈ parabolicOne K n k ↔ ∃ p ∈ parabolic (K := K) (n := n) k, ratOne K n p = q :=
  Subgroup.mem_map

theorem mul_blockEntry_mul {R : Type*} [CommRing R] {k : ℕ} {A B : Matrix (Fin n) (Fin n) R}
    (hA : ∀ i a : Fin n, k ≤ (i : ℕ) → (a : ℕ) < k → A i a = 0)
    (hB : ∀ b j : Fin n, k ≤ (b : ℕ) → (j : ℕ) < k → B b j = 0) (Z : UPos n k → R) :
    A * blockEntry Z * B = blockEntry (fun p : UPos n k => (A * blockEntry Z * B) p.1.1 p.1.2) := by
  ext i j
  rw [blockEntry_apply]
  split_ifs with h
  · rfl
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [Matrix.mul_apply]
    by_cases hi : k ≤ (i : ℕ)
    · rw [Finset.sum_eq_zero, zero_mul]
      intro a _
      by_cases ha : (a : ℕ) < k
      · rw [hA i a hi ha, zero_mul]
      · rw [blockEntry_apply, dite_eq_right (by omega), mul_zero]
    · have hj : (j : ℕ) < k := by omega
      by_cases hb : k ≤ (b : ℕ)
      · rw [hB b j hb hj, mul_zero]
      · rw [Finset.sum_eq_zero, zero_mul]
        intro a _
        rw [blockEntry_apply, dite_eq_right (by omega), mul_zero]

theorem blockEntry_injective {R : Type*} [CommRing R] {k : ℕ} :
    Injective (blockEntry : (UPos n k → R) → Matrix (Fin n) (Fin n) R) := by
  intro X Y h
  funext p
  have := congrFun (congrFun h p.1.1) p.1.2
  simpa [blockEntry_apply, p.2] using this

theorem entry_eq_zero_of_mem_parabolicOne {k : ℕ} {q : normOneGL (K := K) (n := n)} (hq : q ∈ parabolicOne K n k)
    {i j : Fin n} (hi : k ≤ (i : ℕ)) (hj : (j : ℕ) < k) :
    (((q : normOneGL (K := K) (n := n)) : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) i j = 0 := by
  obtain ⟨p, hp, rfl⟩ := mem_parabolicOne_iff.1 hq
  rw [coe_ratOne_matrix]
  simp [ratMat, hp.1 i j hi hj]

def conjUnip (k : ℕ) (q : normOneGL (K := K) (n := n)) : (UPos n k → 𝔸[K]) →+ (UPos n k → 𝔸[K]) where
  toFun Z p := ((((q⁻¹ : normOneGL (K := K) (n := n)) : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) *
    blockEntry Z * (((q : normOneGL (K := K) (n := n)) : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]))
      p.1.1 p.1.2
  map_zero' := by funext p; simp [blockEntry_zero]
  map_add' Z W := by funext p; simp [blockEntry_add, Matrix.mul_add, Matrix.add_mul]

theorem blockEntry_conjUnip {k : ℕ} {q : normOneGL (K := K) (n := n)} (hq : q ∈ parabolicOne K n k)
    (Z : UPos n k → 𝔸[K]) :
    blockEntry (conjUnip k q Z) =
      (((q⁻¹ : normOneGL (K := K) (n := n)) : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) *
        blockEntry Z * (((q : normOneGL (K := K) (n := n)) : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) :=
  (mul_blockEntry_mul (fun _ _ hi ha => entry_eq_zero_of_mem_parabolicOne (inv_mem hq) hi ha)
    (fun _ _ hb hj => entry_eq_zero_of_mem_parabolicOne hq hb hj) Z).symm

theorem coe_inv_mul_coe (q : normOneGL (K := K) (n := n)) :
    (((q⁻¹ : normOneGL (K := K) (n := n)) : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) *
      (((q : normOneGL (K := K) (n := n)) : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) = 1 := by
  rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one]

theorem conj_unipOne {k : ℕ} {q : normOneGL (K := K) (n := n)} (hq : q ∈ parabolicOne K n k) (Z : UPos n k → 𝔸[K]) :
    q⁻¹ * unipOne (K := _) (n := _) k Z * q = unipOne (K := _) (n := _) k (conjUnip k q Z) := by
  have hcoe (X : UPos n k → 𝔸[K]) : (unipOne (K := _) (n := _) k X : AdelicGLn.AdelicGL K n) = unipGL X := rfl
  refine Subtype.ext (Units.ext ?_)
  simp only [Subgroup.coe_mul, Units.val_mul, hcoe, coe_unipGL, unipMatrix]
  rw [blockEntry_conjUnip hq, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, coe_inv_mul_coe]

theorem conjUnip_conjUnip_inv {k : ℕ} {q : normOneGL (K := K) (n := n)} (hq : q ∈ parabolicOne K n k)
    (Z : UPos n k → 𝔸[K]) : conjUnip k q (conjUnip k q⁻¹ Z) = Z := by
  apply blockEntry_injective
  rw [blockEntry_conjUnip hq, blockEntry_conjUnip (inv_mem hq), inv_inv]
  simp only [← Matrix.mul_assoc]
  rw [coe_inv_mul_coe, Matrix.one_mul, Matrix.mul_assoc, coe_inv_mul_coe, Matrix.mul_one]

theorem conjUnip_mem_unipLattice {k : ℕ} {q : normOneGL (K := K) (n := n)} (hq : q ∈ parabolicOne K n k)
    {ξ : UPos n k → 𝔸[K]} (hξ : ξ ∈ unipLattice K n k) : conjUnip k q ξ ∈ unipLattice K n k := by
  obtain ⟨p, -, rfl⟩ := mem_parabolicOne_iff.1 hq
  obtain ⟨ξ₀, rfl⟩ := hξ
  have hξe : (AddMonoidHom.compLeft (algebraMap K 𝔸[K]).toAddMonoidHom (UPos n k)) ξ₀ =
      fun x => algebraMap K 𝔸[K] (ξ₀ x) := rfl
  rw [hξe]
  have hb : blockEntry (fun x => algebraMap K 𝔸[K] (ξ₀ x)) = ratMat (blockEntry ξ₀) := by
    ext i j
    simp only [blockEntry_apply, ratMat, Matrix.map_apply]
    split_ifs <;> simp
  refine ⟨fun x => ((p⁻¹ : GL (Fin n) K) * blockEntry ξ₀ * (p : GL (Fin n) K) :
    Matrix (Fin n) (Fin n) K) x.1.1 x.1.2, funext fun x => ?_⟩
  show algebraMap K 𝔸[K] _ = conjUnip k (ratOne K n p) (fun x => algebraMap K 𝔸[K] (ξ₀ x)) x
  have e : conjUnip k (ratOne K n p) (fun x => algebraMap K 𝔸[K] (ξ₀ x)) x =
      (ratMat ((p⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ratMat (blockEntry ξ₀) *
        ratMat ((p : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) x.1.1 x.1.2 := by
    show ((((ratOne K n p)⁻¹ : normOneGL (K := K) (n := n)) : AdelicGLn.AdelicGL K n) * _ * _ :
      Matrix (Fin n) (Fin n) 𝔸[K]) x.1.1 x.1.2 = _
    rw [← map_inv, coe_ratOne_matrix, coe_ratOne_matrix, hb]
  rw [e, ← ratMat_mul, ← ratMat_mul]
  rfl

theorem continuous_conjUnip (k : ℕ) (q : normOneGL (K := K) (n := n)) : Continuous (conjUnip (K := K) k q) := by
  refine continuous_pi fun p => ?_
  have hb : Continuous (blockEntry : (UPos n k → 𝔸[K]) → Matrix (Fin n) (Fin n) 𝔸[K]) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [blockEntry_apply]
    split_ifs
    · exact continuous_apply _
    · exact continuous_const
  set A₀ : Matrix (Fin n) (Fin n) 𝔸[K] :=
    (((q⁻¹ : normOneGL (K := K) (n := n)) : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])
  set B₀ : Matrix (Fin n) (Fin n) 𝔸[K] :=
    (((q : normOneGL (K := K) (n := n)) : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])
  have hm : Continuous (fun Z : UPos n k → 𝔸[K] => A₀ * blockEntry Z * B₀) :=
    ((continuous_const : Continuous fun _ : UPos n k → 𝔸[K] => A₀).matrix_mul hb).matrix_mul
      continuous_const
  exact (continuous_apply p.1.2).comp ((continuous_apply p.1.1).comp hm)

def conjUnipEquiv {k : ℕ} {q : normOneGL (K := K) (n := n)} (hq : q ∈ parabolicOne K n k) :
    (UPos n k → 𝔸[K]) ≃ₜ+ (UPos n k → 𝔸[K]) where
  toFun := conjUnip k q
  invFun := conjUnip k q⁻¹
  left_inv Z := by
    have := conjUnip_conjUnip_inv (inv_mem hq) Z
    rwa [inv_inv] at this
  right_inv Z := conjUnip_conjUnip_inv hq Z
  map_add' := (conjUnip k q).map_add
  continuous_toFun := continuous_conjUnip k q
  continuous_invFun := continuous_conjUnip k q⁻¹

theorem measurePreserving_conjUnip {k : ℕ} {q : normOneGL (K := K) (n := n)} (hq : q ∈ parabolicOne K n k) :
    MeasurePreserving (conjUnip k q) (unipMeasure K n k) (unipMeasure K n k) :=
  measurePreserving_of_mapsTo_lattice (unipMeasure K n k) isAddFundamentalDomain_unipFundamentalDomain
    measurableSet_unipFundamentalDomain (unipMeasure_unipFundamentalDomain_ne_zero k)
    (unipMeasure_unipFundamentalDomain_ne_top k) (conjUnipEquiv hq)
    (fun _ h => conjUnip_mem_unipLattice hq h) (fun _ h => conjUnip_mem_unipLattice (inv_mem hq) h)

omit [NumberField K] in
theorem isBlockUpper_unipMatrix {k : ℕ} (X : UPos n k → K) : IsBlockUpper k (unipMatrix X) := by
  intro i j hi hj
  simp only [unipMatrix, Matrix.add_apply, blockEntry_apply]
  rw [Matrix.one_apply, ite_eq_right (by intro h; subst h; omega), dite_eq_right (by omega), add_zero]

theorem unipOne_mem_parabolicOne {k : ℕ} {ξ : UPos n k → 𝔸[K]} (hξ : ξ ∈ unipLattice K n k) :
    unipOne (K := _) (n := _) k ξ ∈ parabolicOne K n k := by
  obtain ⟨ξ₀, rfl⟩ := hξ
  refine mem_parabolicOne_iff.2 ⟨unipGL ξ₀, ⟨?_, ?_⟩, Subtype.ext (diagonal_unipGL ξ₀)⟩
  · rw [coe_unipGL]
    exact isBlockUpper_unipMatrix ξ₀
  · rw [coe_unipGL_inv]
    exact isBlockUpper_unipMatrix (-ξ₀)

theorem hyp (k : ℕ) :
    Unfold.Hyp (unipMeasure K n k) (unipOne (K := _) (n := _) k) (unipLattice K n k) (unipFundamentalDomain K n k)
      (parabolicOne K n k) (fundamentalDomain (parabolicOne K n k)) (conjUnip k) := by
  refine
    { map_add := fun X Y => Subtype.ext (unipGL_add X Y)
      injective := unipOne_injective k
      measurable := ?_
      isAddFundamentalDomain := isAddFundamentalDomain_unipFundamentalDomain
      measurableSet_D := measurableSet_unipFundamentalDomain
      measurableSet_E := measurableSet_fundamentalDomain _
      existsUnique := existsUnique_smul_mem_fundamentalDomain _
      mem := fun _ hξ => unipOne_mem_parabolicOne hξ
      conj := fun _ hq Z => conj_unipOne hq Z
      mapsTo := fun _ hq _ hξ => conjUnip_mem_unipLattice hq hξ
      measurePreserving := fun _ hq => measurePreserving_conjUnip hq }
  have h : Continuous (unipOne (K := K) (n := n) k) :=
    continuous_induced_rng.2 continuous_unipGL
  exact h.measurable

end UnfoldGL

end

end GroundTheory.Automorphic.GJGlobal
