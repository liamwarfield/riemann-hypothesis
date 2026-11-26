module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelRowsOrthogonalSumOfParts

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AeMeasureSetOfSmulMemEqZero
open MeasureTheory
open scoped ENNReal Pointwise

namespace GlobalTheory.CovolIndep

theorem isFundamentalDomain_of_ae_eq {Γ X : Type} [Group Γ] [Countable Γ] [MeasurableSpace X]
    [MulAction Γ X] [MeasurableConstSMul Γ X] {μ : Measure X} [SMulInvariantMeasure Γ X μ]
    {s t : Set X} (h : IsFundamentalDomain Γ s μ) (hst : t =ᵐ[μ] s) :
    IsFundamentalDomain Γ t μ := by
  refine ⟨h.nullMeasurableSet.congr hst.symm, ?_, ?_⟩
  ·
    have hall : ∀ᵐ x ∂μ, ∀ g : Γ, (g • x ∈ t) = (g • x ∈ s) := by
      rw [ae_all_iff]
      intro g
      exact ((measurePreserving_smul g μ).quasiMeasurePreserving.ae hst).mono fun _ hx => propext hx
    filter_upwards [h.ae_covers, hall] with x ⟨g, hg⟩ hx
    exact ⟨g, by rw [hx g]; exact hg⟩
  · intro a b hab
    have key : ∀ c : Γ, (c • t : Set X) =ᵐ[μ] (c • s : Set X) := fun c => by
      rw [← Set.preimage_smul_inv, ← Set.preimage_smul_inv]
      exact (measurePreserving_smul c⁻¹ μ).quasiMeasurePreserving.preimage_ae_eq hst
    exact (h.aedisjoint hab).congr (key a) (key b)

variable {S X : Type} [Group S] [MeasurableSpace S] [MeasurableSpace X] [MulAction S X]
  [MeasurableSMul₂ S X]

theorem ae_measure_setOf_smul_mem_eq_zero (ν : Measure S) [SFinite ν] (μ : Measure X) [SFinite μ]
    [SMulInvariantMeasure S X μ] {W : Set X} (hW : μ W = 0) :
    ∀ᵐ y ∂μ, ν {s | s • y ∈ W} = 0 := by
  set W' := toMeasurable μ W
  have hW'm : MeasurableSet W' := measurableSet_toMeasurable μ W
  have hW'0 : μ W' = 0 := by rw [measure_toMeasurable]; exact hW
  have hQ : MeasurableSet {p : X × S | p.2 • p.1 ∈ W'} :=
    hW'm.preimage (measurable_snd.smul measurable_fst)
  have h0 : μ.prod ν {p : X × S | p.2 • p.1 ∈ W'} = 0 := by
    rw [Measure.prod_apply_symm hQ]
    have : ∀ s : S, μ ((fun x => (x, s)) ⁻¹' {p : X × S | p.2 • p.1 ∈ W'}) = 0 := fun s => by
      change μ ((fun x => s • x) ⁻¹' W') = 0
      rw [measure_preimage_smul]; exact hW'0
    exact (lintegral_congr this).trans lintegral_zero
  have h1 := (Measure.measure_prod_null hQ).1 h0
  filter_upwards [h1] with y hy
  exact measure_mono_null (fun s hs => subset_toMeasurable μ W hs) hy

end GlobalTheory.CovolIndep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralFundamentalDomainUnfoldRefoldMeasure
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralFundamentalDomainUnfoldRefoldMeasure
open MeasureTheory
open scoped ENNReal Pointwise

namespace GlobalTheory.CovolIndep

theorem lintegral_unfold_refold (S X : Type) [Group S] [MeasurableSpace S] [MeasurableSpace X]
    [MulAction S X] [MeasurableSMul₂ S X] [MeasurableMul₂ S] [MeasurableInv S] (ν : Measure S)
    [SFinite ν] [ν.IsMulLeftInvariant] (μ : Measure X) [SFinite μ] [SMulInvariantMeasure S X μ]
    (Γ : Subgroup S) [Countable Γ] (D₁ D₂ : Set X) (hD₁ : MeasurableSet D₁)
    (hD₂ : IsFundamentalDomain Γ D₂ μ) (E : Set S) (hE : MeasurableSet E)
    (hEf : IsFundamentalDomain Γ E ν) (ψ : X → ℝ≥0∞) (hψ : Measurable ψ)
    (hinv : ∀ (s : S) (x : X), ψ (s • x) = ψ x) :
    ∫⁻ y, ψ y * ν (E ∩ {s | s⁻¹ • y ∈ D₁}) ∂μ = ∫⁻ y in D₂, ψ y * ν {s | s⁻¹ • y ∈ D₁} ∂μ := by
  haveI : MeasurableConstSMul Γ X :=
    ⟨fun c => (measurable_const_smul (c : S) : Measurable fun x : X => (c : S) • x)⟩
  haveI : SMulInvariantMeasure Γ X μ :=
    ⟨fun c A hA => SMulInvariantMeasure.measure_preimage_smul (c : S) hA⟩
  haveI : MeasurableConstSMul Γ S :=
    ⟨fun c => (measurable_const_mul (c : S) : Measurable fun x : S => (c : S) * x)⟩
  haveI : SMulInvariantMeasure Γ S ν :=
    ⟨fun c A _ => measure_preimage_mul ν (c : S) A⟩
  set F : X → ℝ≥0∞ := fun y => ψ y * ν (E ∩ {s | s⁻¹ • y ∈ D₁}) with hF
  have hQ : MeasurableSet {p : X × S | p.2 ∈ E ∧ p.2⁻¹ • p.1 ∈ D₁} :=
    (measurable_snd hE).inter (hD₁.preimage (measurable_snd.inv.smul measurable_fst))
  have hmeasν : Measurable fun y : X => ν (E ∩ {s | s⁻¹ • y ∈ D₁}) := by
    have := measurable_measure_prodMk_left (ν := ν) hQ
    exact this
  have hFm : Measurable F := hψ.mul hmeasν
  have hstep : ∀ y : X, ∑' γ : Γ, F (γ • y) = ψ y * ν {s | s⁻¹ • y ∈ D₁} := by
    intro y
    have h1 : ∀ γ : Γ, F (γ • y) = ψ y * ν (E ∩ {s | s⁻¹ • ((γ : S) • y) ∈ D₁}) := by
      intro γ
      simp only [hF, Subgroup.smul_def, hinv]
    simp_rw [h1]
    rw [ENNReal.tsum_mul_left]
    congr 1
    rw [hEf.measure_eq_tsum {s | s⁻¹ • y ∈ D₁}]
    refine tsum_congr fun γ => ?_
    congr 1
    ext s
    simp only [Set.mem_inter_iff, Set.mem_smul_set_iff_inv_smul_mem, Set.mem_setOf_eq,
      Subgroup.smul_def, smul_eq_mul, mul_inv_rev, inv_inv, mul_smul]
    exact and_comm
  calc ∫⁻ y, F y ∂μ = ∑' γ : Γ, ∫⁻ y in D₂, F (γ • y) ∂μ := hD₂.lintegral_eq_tsum'' F
    _ = ∫⁻ y in D₂, ∑' γ : Γ, F (γ • y) ∂μ := by
      rw [lintegral_tsum]
      intro γ
      exact (hFm.comp (measurable_const_smul γ)).aemeasurable
    _ = ∫⁻ y in D₂, ψ y * ν {s | s⁻¹ • y ∈ D₁} ∂μ := by
      simp_rw [hstep]

end GlobalTheory.CovolIndep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralFundamentalDomainUnfoldRefoldMeasureStatement
open MeasureTheory
open scoped ENNReal Pointwise

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_fundamentalDomain_unfold_refold_measure : ∀ (S X : Type) [Group S] [MeasurableSpace S] [MeasurableSpace X] [MulAction S X] [MeasurableSMul₂ S X] [MeasurableMul₂ S] [MeasurableInv S] (ν : Measure S) [SFinite ν] [ν.IsMulLeftInvariant] (μ : Measure X) [SFinite μ] [SMulInvariantMeasure S X μ] (Γ : Subgroup S) [Countable Γ] (D₁ D₂ : Set X), MeasurableSet D₁ → IsFundamentalDomain Γ D₂ μ → ∀ (E : Set S), MeasurableSet E → IsFundamentalDomain Γ E ν → ∀ (ψ : X → ℝ≥0∞), Measurable ψ → (∀ (s : S) (x : X), ψ (s • x) = ψ x) → ∫⁻ y, ψ y * ν (E ∩ {s | s⁻¹ • y ∈ D₁}) ∂μ = ∫⁻ y in D₂, ψ y * ν {s | s⁻¹ • y ∈ D₁} ∂μ := by
  first | exact @GlobalTheory.CovolIndep.lintegral_unfold_refold | exact GlobalTheory.CovolIndep.lintegral_unfold_refold | (intros; apply GlobalTheory.CovolIndep.lintegral_unfold_refold <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AeMeasureSmulPreimageFundamentalDomainEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AeMeasureSmulPreimageFundamentalDomainEq
open MeasureTheory
open scoped ENNReal Pointwise

namespace GlobalTheory.CovolIndep

theorem ae_measure_slice_eq (S X : Type) [Group S] [MeasurableSpace S] [MeasurableSpace X]
    [MulAction S X] [MeasurableSMul₂ S X] [MeasurableMul₂ S] [MeasurableInv S] (ν : Measure S)
    [SFinite ν] [ν.IsMulLeftInvariant] (μ : Measure X) [SFinite μ] [SMulInvariantMeasure S X μ]
    (Γ : Subgroup S) [Countable Γ] (D : Set X) (hD : MeasurableSet D)
    (hDf : IsFundamentalDomain Γ D μ) (E : Set S) (hE : IsFundamentalDomain Γ E ν) :
    ∀ᵐ y ∂μ, ν {s | s • y ∈ D} = ν E := by
  set W₀ : Set X := {x | ¬ ∃ g : Γ, g • x ∈ D} with hW₀
  have hW₀0 : μ W₀ = 0 := ae_iff.1 hDf.ae_covers
  have h0 := ae_measure_setOf_smul_mem_eq_zero ν μ hW₀0
  have h1 : ∀ᵐ y ∂μ, ∀ p : Γ × Γ, p.1 ≠ p.2 →
      ν {s | s • y ∈ (p.1 • D ∩ p.2 • D : Set X)} = 0 := by
    rw [ae_all_iff]
    intro p
    by_cases hp : p.1 = p.2
    · exact Filter.Eventually.of_forall fun y h => absurd hp h
    · filter_upwards [ae_measure_setOf_smul_mem_eq_zero ν μ (hDf.aedisjoint hp)] with y hy
      exact fun _ => hy
  filter_upwards [h0, h1] with y hy0 hy1
  have hU : IsFundamentalDomain Γ {s : S | s • y ∈ D} ν := by
    refine ⟨(hD.preimage (measurable_smul_const y)).nullMeasurableSet, ?_, ?_⟩
    · rw [ae_iff]
      refine measure_mono_null (fun s hs => ?_) hy0
      simp only [Set.mem_setOf_eq, not_exists] at hs ⊢
      rintro ⟨g, hg⟩
      refine hs g ?_
      simpa [Subgroup.smul_def, mul_smul] using hg
    · intro a b hab
      have key : ∀ c : Γ, ∀ s : S, s ∈ (c • {s : S | s • y ∈ D} : Set S) ↔ s • y ∈ (c • D : Set X) := by
        intro c s
        rw [Set.mem_smul_set_iff_inv_smul_mem, Set.mem_smul_set_iff_inv_smul_mem]
        simp [Subgroup.smul_def, mul_smul]
      change ν _ = 0
      refine measure_mono_null (fun s hs => ?_) (hy1 (a, b) hab)
      exact ⟨(key a s).1 hs.1, (key b s).1 hs.2⟩
  exact hU.measure_eq hE

end GlobalTheory.CovolIndep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AeMeasureSmulPreimageFundamentalDomainEqStatement
open MeasureTheory
open scoped ENNReal Pointwise

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ae_measure_smul_preimage_fundamentalDomain_eq : ∀ (S X : Type) [Group S] [MeasurableSpace S] [MeasurableSpace X] [MulAction S X] [MeasurableSMul₂ S X] [MeasurableMul₂ S] [MeasurableInv S] (ν : Measure S) [SFinite ν] [ν.IsMulLeftInvariant] (μ : Measure X) [SFinite μ] [SMulInvariantMeasure S X μ] (Γ : Subgroup S) [Countable Γ] (D : Set X), MeasurableSet D → IsFundamentalDomain Γ D μ → ∀ (E : Set S), IsFundamentalDomain Γ E ν → ∀ᵐ y ∂μ, ν {s | s • y ∈ D} = ν E := by
  first | exact @GlobalTheory.CovolIndep.ae_measure_slice_eq | exact GlobalTheory.CovolIndep.ae_measure_slice_eq | (intros; apply GlobalTheory.CovolIndep.ae_measure_slice_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralMulMeasureInterSmulPreimageOfInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralMulMeasureInterSmulPreimageOfInvariant
open MeasureTheory
open scoped ENNReal Pointwise

namespace GlobalTheory

theorem lintegral_mul_measure_inter_smul_preimage :
    ∀ (S X : Type) [Group S] [MeasurableSpace S] [MeasurableSpace X] [MulAction S X] [MeasurableSMul₂ S X] [MeasurableInv S] (ν : Measure S) [SFinite ν] (μ : Measure X) [SFinite μ] [SMulInvariantMeasure S X μ] (D : Set X), MeasurableSet D → ∀ (E : Set S), MeasurableSet E → ∀ (ψ : X → ℝ≥0∞), Measurable ψ → (∀ (s : S) (x : X), ψ (s • x) = ψ x) → ν E * ∫⁻ x in D, ψ x ∂μ = ∫⁻ y, ψ y * ν (E ∩ {s | s⁻¹ • y ∈ D}) ∂μ := by
  intro S X _ _ _ _ _ _ ν _ μ _ _ D hD E hE ψ hψ hinv
  have hmeas : Measurable (Function.uncurry fun (s : S) (y : X) =>
      ψ y * (E.indicator (1 : S → ℝ≥0∞) s * D.indicator (1 : X → ℝ≥0∞) (s⁻¹ • y))) := by
    have hsm' : Measurable (fun p : S × X => p.1⁻¹ • p.2) :=
      (measurable_fst.inv).smul measurable_snd
    refine (hψ.comp measurable_snd).mul ?_
    exact ((measurable_one.indicator hE).comp measurable_fst).mul
      ((measurable_one.indicator hD).comp hsm')
  have h1 : ∀ y : X, ν (E ∩ {s | s⁻¹ • y ∈ D}) =
      ∫⁻ s, E.indicator (1 : S → ℝ≥0∞) s * D.indicator (1 : X → ℝ≥0∞) (s⁻¹ • y) ∂ν := by
    intro y
    have hm : MeasurableSet (E ∩ {s : S | s⁻¹ • y ∈ D}) :=
      hE.inter (hD.preimage (measurable_inv.smul_const y))
    rw [← lintegral_indicator_one hm]
    congr 1; ext s
    by_cases h1 : s ∈ E <;> by_cases h2 : s⁻¹ • y ∈ D <;> simp [Set.indicator, h1, h2]
  have h2 : ∀ s : S, ∫⁻ y, ψ y * D.indicator (1 : X → ℝ≥0∞) (s⁻¹ • y) ∂μ = ∫⁻ x in D, ψ x ∂μ := by
    intro s
    have hf : Measurable (fun x : X => ψ x * D.indicator (1 : X → ℝ≥0∞) x) :=
      hψ.mul (measurable_one.indicator hD)
    calc ∫⁻ y, ψ y * D.indicator (1 : X → ℝ≥0∞) (s⁻¹ • y) ∂μ
        = ∫⁻ y, (fun x : X => ψ x * D.indicator (1 : X → ℝ≥0∞) x) (s⁻¹ • y) ∂μ := by
          congr 1; ext y; simp only [hinv]
      _ = ∫⁻ x, ψ x * D.indicator (1 : X → ℝ≥0∞) x ∂μ :=
          (measurePreserving_smul s⁻¹ μ).lintegral_comp hf
      _ = ∫⁻ x in D, ψ x ∂μ := by
          rw [← lintegral_indicator hD]
          congr 1; ext x
          by_cases hx : x ∈ D <;> simp [Set.indicator, hx]
  calc ν E * ∫⁻ x in D, ψ x ∂μ
      = ∫⁻ s, E.indicator (1 : S → ℝ≥0∞) s * ∫⁻ y, ψ y * D.indicator (1 : X → ℝ≥0∞) (s⁻¹ • y) ∂μ ∂ν := by
        simp only [h2]
        rw [lintegral_mul_const _ (measurable_one.indicator hE), lintegral_indicator_one hE]
    _ = ∫⁻ s, ∫⁻ y, ψ y * (E.indicator (1 : S → ℝ≥0∞) s * D.indicator (1 : X → ℝ≥0∞) (s⁻¹ • y)) ∂μ ∂ν := by
        congr 1; ext s
        rw [← lintegral_const_mul' _ _ (by by_cases h : s ∈ E <;> simp [Set.indicator, h])]
        congr 1; ext y; ring
    _ = ∫⁻ y, ∫⁻ s, ψ y * (E.indicator (1 : S → ℝ≥0∞) s * D.indicator (1 : X → ℝ≥0∞) (s⁻¹ • y)) ∂ν ∂μ :=
        lintegral_lintegral_swap hmeas.aemeasurable
    _ = ∫⁻ y, ψ y * ν (E ∩ {s | s⁻¹ • y ∈ D}) ∂μ := by
        congr 1; ext y
        have hm : Measurable (fun s : S =>
            E.indicator (1 : S → ℝ≥0∞) s * D.indicator (1 : X → ℝ≥0∞) (s⁻¹ • y)) :=
          (measurable_one.indicator hE).mul
            ((measurable_one.indicator hD).comp (measurable_inv.smul_const y))
        rw [h1 y]
        exact lintegral_const_mul (ψ y) hm

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralMulMeasureInterSmulPreimageOfInvariantStatement
open MeasureTheory
open scoped ENNReal Pointwise

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_mul_measure_inter_smul_preimage_of_invariant : ∀ (S X : Type) [Group S] [MeasurableSpace S] [MeasurableSpace X] [MulAction S X] [MeasurableSMul₂ S X] [MeasurableInv S] (ν : Measure S) [SFinite ν] (μ : Measure X) [SFinite μ] [SMulInvariantMeasure S X μ] (D : Set X), MeasurableSet D → ∀ (E : Set S), MeasurableSet E → ∀ (ψ : X → ℝ≥0∞), Measurable ψ → (∀ (s : S) (x : X), ψ (s • x) = ψ x) → ν E * ∫⁻ x in D, ψ x ∂μ = ∫⁻ y, ψ y * ν (E ∩ {s | s⁻¹ • y ∈ D}) ∂μ := by
  first | exact @GlobalTheory.lintegral_mul_measure_inter_smul_preimage | exact GlobalTheory.lintegral_mul_measure_inter_smul_preimage | (intros; apply GlobalTheory.lintegral_mul_measure_inter_smul_preimage <;> assumption)
end
end

open MeasureTheory
open scoped ENNReal Pointwise

namespace GlobalTheory.CovolIndep
variable {S X : Type} [Group S] [MeasurableSpace S] [MeasurableSpace X] [MulAction S X]
  [MeasurableSMul₂ S X]

theorem measure_mul_setLIntegral_eq [MeasurableInv S] (ν : Measure S) [SFinite ν] (μ : Measure X) [SFinite μ]
    [SMulInvariantMeasure S X μ] (D : Set X) (hD : MeasurableSet D) (E : Set S)
    (hE : MeasurableSet E) (ψ : X → ℝ≥0∞) (hψ : Measurable ψ)
    (hinv : ∀ (s : S) (x : X), ψ (s • x) = ψ x) :
    ν E * ∫⁻ x in D, ψ x ∂μ = ∫⁻ y, ψ y * ν (E ∩ {s | s⁻¹ • y ∈ D}) ∂μ :=
  GlobalTheory.T.lintegral_mul_measure_inter_smul_preimage_of_invariant S X ν μ D hD E hE ψ hψ hinv

theorem lintegral_unfold_eq [MeasurableMul₂ S] [MeasurableInv S] (ν : Measure S) [SFinite ν]
    [ν.IsMulLeftInvariant] (μ : Measure X) [SFinite μ] [SMulInvariantMeasure S X μ]
    (Γ : Subgroup S) [Countable Γ] (D₁ D₂ : Set X) (hD₁ : MeasurableSet D₁)
    (hD₂ : IsFundamentalDomain Γ D₂ μ) (E : Set S) (hE : MeasurableSet E)
    (hEf : IsFundamentalDomain Γ E ν) (ψ : X → ℝ≥0∞) (hψ : Measurable ψ)
    (hinv : ∀ (s : S) (x : X), ψ (s • x) = ψ x) :
    ∫⁻ y, ψ y * ν (E ∩ {s | s⁻¹ • y ∈ D₁}) ∂μ = ∫⁻ y in D₂, ψ y * ν {s | s⁻¹ • y ∈ D₁} ∂μ :=
  GlobalTheory.T.lintegral_fundamentalDomain_unfold_refold_measure S X ν μ Γ D₁ D₂ hD₁ hD₂ E hE hEf ψ hψ hinv

theorem ae_measure_setOf_smul_mem_eq [MeasurableMul₂ S] [MeasurableInv S] (ν : Measure S) [SFinite ν]
    [ν.IsMulLeftInvariant] (μ : Measure X) [SFinite μ] [SMulInvariantMeasure S X μ]
    (Γ : Subgroup S) [Countable Γ] (D : Set X) (hD : MeasurableSet D)
    (hDf : IsFundamentalDomain Γ D μ) (E : Set S) (hE : IsFundamentalDomain Γ E ν) :
    ∀ᵐ y ∂μ, ν {s | s • y ∈ D} = ν E :=
  GlobalTheory.T.ae_measure_smul_preimage_fundamentalDomain_eq S X ν μ Γ D hD hDf E hE

theorem lintegral_mul_eq_of_measurable [MeasurableMul₂ S] [MeasurableInv S] (ν : Measure S)
    [SFinite ν] [ν.IsMulLeftInvariant] [ν.IsInvInvariant] (μ : Measure X) [SFinite μ]
    [SMulInvariantMeasure S X μ] (Γ₁ Γ₂ : Subgroup S) [Countable Γ₁] [Countable Γ₂]
    (D₁ D₂ : Set X) (E₁ E₂ : Set S) (hD₁m : MeasurableSet D₁) (hD₂m : MeasurableSet D₂)
    (hE₂m : MeasurableSet E₂)
    (hD₁ : IsFundamentalDomain Γ₁ D₁ μ) (hD₂ : IsFundamentalDomain Γ₂ D₂ μ)
    (hE₁ : IsFundamentalDomain Γ₁ E₁ ν) (hE₂ : IsFundamentalDomain Γ₂ E₂ ν)
    (ψ : X → ℝ≥0∞) (hψ : Measurable ψ) (hinv : ∀ (s : S) (x : X), ψ (s • x) = ψ x) :
    ν E₂ * ∫⁻ x in D₁, ψ x ∂μ = ν E₁ * ∫⁻ x in D₂, ψ x ∂μ := by
  rw [measure_mul_setLIntegral_eq ν μ D₁ hD₁m E₂ hE₂m ψ hψ hinv,
    lintegral_unfold_eq ν μ Γ₂ D₁ D₂ hD₁m hD₂ E₂ hE₂m hE₂ ψ hψ hinv, ← lintegral_const_mul _ hψ]
  refine lintegral_congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [ae_measure_setOf_smul_mem_eq ν μ Γ₁ D₁ hD₁m hD₁ E₁ hE₁] with y hy
  have : ν {s : S | s⁻¹ • y ∈ D₁} = ν {s : S | s • y ∈ D₁} := by
    change ν ({s : S | s • y ∈ D₁}⁻¹) = _
    exact Measure.measure_inv (μ := ν) _
  rw [this, hy, mul_comm]
end GlobalTheory.CovolIndep

namespace GlobalTheory.CovolIndep
variable {S X : Type} [Group S] [MeasurableSpace S] [MeasurableSpace X] [MulAction S X]
  [MeasurableSMul₂ S X]

theorem lintegral_mul_eq [MeasurableMul₂ S] [MeasurableInv S] (ν : Measure S)
    [SFinite ν] [ν.IsMulLeftInvariant] [ν.IsInvInvariant] (μ : Measure X) [SFinite μ]
    [SMulInvariantMeasure S X μ] (Γ₁ Γ₂ : Subgroup S) [Countable Γ₁] [Countable Γ₂]
    (D₁ D₂ : Set X) (E₁ E₂ : Set S)
    (hD₁ : IsFundamentalDomain Γ₁ D₁ μ) (hD₂ : IsFundamentalDomain Γ₂ D₂ μ)
    (hE₁ : IsFundamentalDomain Γ₁ E₁ ν) (hE₂ : IsFundamentalDomain Γ₂ E₂ ν)
    (ψ : X → ℝ≥0∞) (hψ : Measurable ψ) (hinv : ∀ (s : S) (x : X), ψ (s • x) = ψ x) :
    ν E₂ * ∫⁻ x in D₁, ψ x ∂μ = ν E₁ * ∫⁻ x in D₂, ψ x ∂μ := by
  have a₁ := hD₁.nullMeasurableSet.toMeasurable_ae_eq
  have a₂ := hD₂.nullMeasurableSet.toMeasurable_ae_eq
  have b₂ := hE₂.nullMeasurableSet.toMeasurable_ae_eq
  have key := lintegral_mul_eq_of_measurable ν μ Γ₁ Γ₂ (toMeasurable μ D₁) (toMeasurable μ D₂)
    E₁ (toMeasurable ν E₂) (measurableSet_toMeasurable _ _) (measurableSet_toMeasurable _ _)
    (measurableSet_toMeasurable _ _) (isFundamentalDomain_of_ae_eq hD₁ a₁)
    (isFundamentalDomain_of_ae_eq hD₂ a₂) hE₁ (isFundamentalDomain_of_ae_eq hE₂ b₂) ψ hψ hinv
  rwa [measure_toMeasurable, setLIntegral_congr a₁, setLIntegral_congr a₂] at key

end GlobalTheory.CovolIndep

namespace GlobalTheory

end GlobalTheory
