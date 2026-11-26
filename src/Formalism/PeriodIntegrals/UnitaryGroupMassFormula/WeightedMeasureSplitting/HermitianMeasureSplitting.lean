module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.ContinuousMeasureSplitting
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LevelKSplit

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.ProductDecompositionHolds
noncomputable section

namespace PI.UnitaryGroupMassFormula.MeasWCore

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures MeasureTheory NumberField

theorem amb_eq_map_mul_of_lintegral {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G]
    [MeasurableMul₂ G] {K N H : Subgroup G} (μK : Measure K) (μN : Measure N) (μH : Measure H)
    [SFinite μN] [SFinite μH]
    (h : ∀ f : G → ENNReal, Measurable f →
      ∫⁻ k, f (k : G) ∂μK = ∫⁻ m, ∫⁻ x, f ((m : G) * (x : G)) ∂μH ∂μN) :
    amb μK = ((amb μN).prod (amb μH)).map (fun p => p.1 * p.2) := by
  ext B hB
  have hf : Measurable (B.indicator (1 : G → ENNReal)) := measurable_one.indicator hB
  have hv : Measurable (Prod.map (Subtype.val : N → G) (Subtype.val : H → G)) :=
    measurable_subtype_coe.prodMap measurable_subtype_coe
  have hm : Measurable (fun p : G × G => p.1 * p.2) := measurable_mul
  calc amb μK B = ∫⁻ x, B.indicator 1 x ∂(amb μK) := (lintegral_indicator_one hB).symm
    _ = ∫⁻ k, B.indicator 1 (k : G) ∂μK := lintegral_map hf measurable_subtype_coe
    _ = ∫⁻ m, ∫⁻ x, B.indicator 1 ((m : G) * (x : G)) ∂μH ∂μN := h _ hf
    _ = ∫⁻ p, B.indicator 1 ((p.1 : G) * (p.2 : G)) ∂(μN.prod μH) :=
        (lintegral_prod _ (hf.comp (hm.comp hv)).aemeasurable).symm
    _ = ∫⁻ q, B.indicator 1 (q.1 * q.2) ∂((μN.prod μH).map
          (Prod.map (Subtype.val : N → G) (Subtype.val : H → G))) :=
        (lintegral_map (hf.comp hm) hv).symm
    _ = ∫⁻ q, B.indicator 1 (q.1 * q.2) ∂((amb μN).prod (amb μH)) := by
        rw [Measure.map_prod_map μN μH measurable_subtype_coe measurable_subtype_coe]
    _ = ∫⁻ x, B.indicator 1 x ∂(((amb μN).prod (amb μH)).map (fun p => p.1 * p.2)) :=
        (lintegral_map hf hm).symm
    _ = (((amb μN).prod (amb μH)).map (fun p => p.1 * p.2)) B := lintegral_indicator_one hB

theorem product_decomposition_holds : SProd := by
  intro F E _ _ _ _ _ σ n J r P T hCM hJ hStd μNf μHf hN hH
  obtain ⟨⟨μS, hμS, hprod⟩, -⟩ := level_s_all_split F E σ hCM n J hJ hJ r P T hStd ∅ ∅ ∅
    (by simp [PI.LevelKSplit.Adapted]) μNf hN μHf hH
  refine ⟨μS, hμS, ?_⟩
  have := hN
  have := hH
  exact amb_eq_map_mul_of_lintegral μS μNf μHf hprod

end PI.UnitaryGroupMassFormula.MeasWCore
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.MapSplitEq
noncomputable section

namespace PI.UnitaryGroupMassFormula.MeasWCore

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

theorem map_split_eq {X Y₁ Y₂ : Type} [MeasurableSpace X] [MeasurableSpace Y₁] [MeasurableSpace Y₂]
    {K : Set X} {K₁ : Set Y₁} {K₂ : Set Y₂} (s : X → Y₁ × Y₂) (hs : Measurable s)
    (e : K₁ × K₂ → K) (he : Measurable e) (hse : ∀ p, s (e p : X) = ((p.1 : Y₁), (p.2 : Y₂)))
    (μ₁ : Measure K₁) (μ₂ : Measure K₂) [SFinite μ₁] [SFinite μ₂] :
    (((μ₁.prod μ₂).map e).map Subtype.val).map s = (μ₁.map Subtype.val).prod (μ₂.map Subtype.val) := by
  rw [Measure.map_map measurable_subtype_coe he, Measure.map_map hs (measurable_subtype_coe.comp he),
    Measure.map_prod_map μ₁ μ₂ measurable_subtype_coe measurable_subtype_coe]
  congr 1
  funext p
  exact hse p

theorem mwCore_of (hH : SplitH) (hN : SplitN) (hC : ContSplit) (hS : SProd) :
    Formalism.L2.SG.Pf.MeasCore.MWCore := by
  intro F E _ _ _ _ _ σ n J r P T hCM hJ hP μNinf μHinf hNinf hHinf
  have : Module.Finite F E := PI.VolSemiDirect.W.Lc.finite_nf F E
  obtain ⟨eH, heH⟩ := hH F E σ n J r P T hCM hJ hP
  obtain ⟨eN, heN⟩ := hN F E σ n J r P T hCM hJ hP
  have hsm : Measurable (splitA σ J) := (hC F E σ n J hCM).measurable
  let μHf : Measure (Hsub (Af F) σ J P) := Measure.haar
  let μNf : Measure (Nsub (Af F) σ J P) := Measure.haar
  obtain ⟨μSf, hSH, hSeq⟩ := hS F E σ n J r P T hCM hJ hP μNf μHf inferInstance inferInstance
  have := hHinf
  have := hNinf
  have : SigmaCompactSpace (Hsub (Ainf F) σ J P) := inferInstance
  have : SigmaCompactSpace (Nsub (Ainf F) σ J P) := inferInstance
  have : SigmaCompactSpace (Hsub (Af F) σ J P) := inferInstance
  have : SigmaCompactSpace (Nsub (Af F) σ J P) := inferInstance
  have : SigmaFinite μHinf := inferInstance
  have : SigmaFinite μNinf := inferInstance
  have : SigmaFinite μHf := inferInstance
  have : SigmaFinite μNf := inferInstance
  refine ⟨{ μH := (μHinf.prod μHf).map eH, μHinf := μHinf, μHf := μHf,
            μN := (μNinf.prod μNf).map eN, μNinf := μNinf, μNf := μNf, μSf := μSf,
            μSv := fun v => Measure.haar }, ?_, rfl, rfl⟩
  refine ⟨?_, hHinf, inferInstance, ?_, hNinf, inferInstance, hSH, fun v => inferInstance, ?_, ?_, hSeq⟩
  · exact ContinuousMulEquiv.isHaarMeasure_map (μHinf.prod μHf) eH
  · exact ContinuousMulEquiv.isHaarMeasure_map (μNinf.prod μNf) eN
  · exact map_split_eq (splitA σ J) hsm eH eH.continuous.measurable heH μHinf μHf
  · exact map_split_eq (splitA σ J) hsm eN eN.continuous.measurable heN μNinf μNf

end PI.UnitaryGroupMassFormula.MeasWCore
end
end

noncomputable section

namespace PI.UnitaryGroupMassFormula.MeasWCore

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures NumberField

theorem hermitian_measure_splitting : SplitH := by
  intro F E _ _ _ _ _ σ n J r P T _ _ _
  have : Module.Finite F E := PI.VolSemiDirect.W.Lc.finite_nf F E
  exact splitEquiv _ _ _ (splitA_injective σ J splT_bijective.1)
    (continuous_haMap σ J (fstA F) (continuous_tensMap (AF F) _ continuous_fstA))
    (continuous_haMap σ J (sndA F) (continuous_tensMap (AF F) _ continuous_sndA))
    (mem_Hsub_iff σ J splT_bijective.1 P)

theorem nilpotent_measure_splitting : SplitN := by
  intro F E _ _ _ _ _ σ n J r P T _ _ _
  have : Module.Finite F E := PI.VolSemiDirect.W.Lc.finite_nf F E
  exact splitEquiv _ _ _ (splitA_injective σ J splT_bijective.1)
    (continuous_haMap σ J (fstA F) (continuous_tensMap (AF F) _ continuous_fstA))
    (continuous_haMap σ J (sndA F) (continuous_tensMap (AF F) _ continuous_sndA))
    (mem_Nsub_iff σ J splT_bijective P)

theorem measWCore_main : Formalism.L2.SG.Pf.MeasCore.MWCore :=
  mwCore_of hermitian_measure_splitting nilpotent_measure_splitting continuous_measure_splitting product_decomposition_holds

end PI.UnitaryGroupMassFormula.MeasWCore
