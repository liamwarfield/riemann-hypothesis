module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.WeilPairJ
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ChoiceFinal
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocFactorAll
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.ConvGG

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyFinal
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf
open scoped InnerProductSpace ENNReal

namespace Formalism.L2.SG.RealObj.EnergyFinal


variable [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] in
theorem stepIntG_holds (hI : Formalism.FourierDecayAlt.ThreeDimData.Inputs) : Formalism.L2.SG.RealObj.EnergyInt.StepIntG :=
  Formalism.L2.SG.RealObj.EnergyIntLoc.stepIntG_of hI Formalism.L2.SG.Pf.WuBL.reproduction_translation Formalism.L2.SG.Pf.WuBL.l2RightTranslation_thm
    Formalism.L2.SG.Pf.WuBL.parameter_gap_of_hypothesis (fun _ hG _ _ C => Formalism.L2.SG.Pf.LocF.locFactor_holds hG C)


variable [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] in
theorem weilPairJ_holds (hI : Formalism.FourierDecayAlt.ThreeDimData.Inputs) {D : D7} (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D)
    (X : HidaSetting D) (τ : D.what₂.Tau) :
    ∃ (μS ν : D.what₂.Word → Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))),
      (∀ u, SFinite (μS u) ∧ SFinite (ν u) ∧
        (∀ f : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) → ℝ≥0∞, Measurable f →
          ∫⁻ x, f x ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ))) = ∫⁻ x, ∫⁻ s, f (s * x) ∂(μS u) ∂(ν u)) ∧
        (μS u).map (fun x => x⁻¹) = μS u ∧ μS u (Formalism.L2.SG.Pf.WuDec.Sloc X u (vOf X τ))ᶜ = 0 ∧
        ∫⁻ z, ∫⁻ z', ∫⁻ s, ‖⟪X.B.σ (vOf X τ) (uMat z) (X.B.w (vOf X τ)),
            X.B.σ (vOf X τ) (uMat s) (X.B.σ (vOf X τ) (uMat z') (X.B.w (vOf X τ)))⟫_ℂ‖ₑ *
          ‖X.Wloc u (vOf X τ) z‖ₑ * ‖X.Wloc u (vOf X τ) z'‖ₑ ∂(μS u) ∂(ν u) ∂(ν u) < ⊤ ∧
        (∀ s ∈ Formalism.L2.SG.Pf.WuDec.Sloc X u (vOf X τ), (μS u).map (fun x => s * x) = μS u) ∧ μS u ≠ 0) ∧
      ∀ (u u' : D.what₂.Word) (sc : ℝ), 0 < sc → ∀ cv ∈ Formalism.L2.SG.RealObj.EnergyCut.GoodV (D := D) u u',
        ∀ g : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)),
          Formalism.L2.SG.RealObj.Zhat (X.B.I.ε (vOf X τ)) (Formalism.L2.SG.RealObj.frm X u sc (vOf X τ))
            (Formalism.L2.SG.RealObj.frm X u' sc (vOf X τ)) (uMat g) = Matrix.diagonal cv →
          ∫⁻ z, ∫⁻ z', ∫⁻ s, ∫⁻ s', ‖⟪X.B.σ (vOf X τ) (uMat z) (X.B.w (vOf X τ)),
              X.B.σ (vOf X τ) (uMat (s * g * s'⁻¹)) (X.B.σ (vOf X τ) (uMat z') (X.B.w (vOf X τ)))⟫_ℂ‖ₑ *
            ‖X.Wloc u (vOf X τ) z‖ₑ * ‖X.Wloc u' (vOf X τ) z'‖ₑ ∂(μS u') ∂(μS u) ∂(ν u') ∂(ν u) < ⊤ :=
  Formalism.L2.SG.RealObj.EnergyConvJ.weilPairJ hI Formalism.L2.SG.Pf.WuBL.reproduction_translation Formalism.L2.SG.Pf.WuBL.l2RightTranslation_thm
    Formalism.L2.SG.Pf.WuBL.parameter_gap_of_hypothesis (fun _ hG _ _ C => Formalism.L2.SG.Pf.LocF.locFactor_holds hG C) hG X τ

end Formalism.L2.SG.RealObj.EnergyFinal
end
end

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.S.Pv.ConvG
open scoped InnerProductSpace ENNReal

namespace Formalism.L2.SG.RealObj.EnergyConvJ


set_option maxHeartbeats 400000 in
variable [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] in
theorem locQuadGG_G_holds (hI : Formalism.FourierDecayAlt.ThreeDimData.Inputs) : LocQuadGG_G := by
  intro D hG X u u' sc hsc v cv hcv g hZ
  obtain ⟨τ, hτ⟩ : ∃ τ, vOf X τ = v := ⟨X.pl v, X.pl.symm_apply_apply v⟩
  subst hτ
  obtain ⟨μS, ν, hloc, h4⟩ := Formalism.L2.SG.RealObj.EnergyFinal.weilPairJ_holds hI hG X τ
  obtain ⟨hs1, hn1, hW1, hi1, h01, -⟩ := hloc u
  obtain ⟨hs2, hn2, hW2, hi2, h02, -⟩ := hloc u'
  have hfin := h4 u u' sc hsc cv hcv g hZ
  have hU := Formalism.L2.S.Pv.SchurTens.unitRep_of_URepOn (X.ds (vOf X τ)).2.2.1
  rw [quad_eq_GG (μ := Formalism.REAL.muG (X.B.I.ε (vOf X τ))) (μS := μS u) (μS' := μS u') (ν := ν u) (ν' := ν u')
    (S := Formalism.L2.SG.Pf.WuDec.Sloc X u (vOf X τ)) (S' := Formalism.L2.SG.Pf.WuDec.Sloc X u' (vOf X τ)) hU
    (X.B.w (vOf X τ)) (X.Wloc_cont u (vOf X τ)) (X.Wloc_cont u' (vOf X τ)) hW1 hW2 hi1 hi2 h01 h02
    (fun a ha => Formalism.L2.SG.Pf.WuDec.inv_mem_Sloc X u (vOf X τ) ha)
    (fun a ha => Formalism.L2.SG.Pf.WuDec.inv_mem_Sloc X u' (vOf X τ) ha)
    (fun s hs x => Formalism.L2.SG.Pf.WuDec.norm_Wloc_inv X u (vOf X τ) hs x)
    (fun s hs x => Formalism.L2.SG.Pf.WuDec.norm_Wloc_inv X u' (vOf X τ) hs x) g] at hfin
  unfold PhiGG at hfin
  exact hfin

end Formalism.L2.SG.RealObj.EnergyConvJ
