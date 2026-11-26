module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.L2SGPhiOfNeZeroAndLtInfty
public import Formalism.LocalToGlobal.SiegelLatticeTheory.WeightedGaugeFactors.FactsDS
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.HarishChandraMultiplicityBound
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.CoefWeightedLocHolds

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ChoiceFinal
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf

namespace Formalism.L2.SG.Pf

theorem wuBesselOfLoc_all {D : D7} {X : HidaSetting D} {θ : ℝ} (C : Choice X θ) : WuBesselOfLoc C :=
  Formalism.L2.SG.Pf.WuBL.wuBesselOfLoc Formalism.L2.SG.Pf.WuBL.reproduction_translation Formalism.L2.SG.Pf.WuBL.l2RightTranslation_thm
    Formalism.L2.SG.Pf.WuBL.parameter_gap_of_hypothesis C

theorem goodSRest_of_loc {D : D7} {X : HidaSetting D} {θ : ℝ} {C : Choice X θ} (hLF : LocFactor C) (hB : WuBessel C)
    (u u' : D.what₂.Word) (τ : D.what₂.Tau)
    (hsm : v0Of C τ ∈ smoothVecs (k := D.R.k) (r := D.R.rS) (sigB X (C.Q τ) (C.Qi τ) τ))
    (hT : Formalism.BasicNotions.dsigTie D) : GoodSRest hB u u' τ :=
  Formalism.L2.SG.Pf.GoodS.goodSRest_of hB u u' τ hsm (Formalism.L2.SG.Pf.GoodS.l2SG_phiOf_ne_zero_and_lt_infty C hLF hB u τ)
    (Formalism.L2.SG.Pf.GoodS.l2SG_phiOf_ne_zero_and_lt_infty C hLF hB u' τ) hT

end Formalism.L2.SG.Pf
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTPh
noncomputable section

open MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.ProjRows Formalism.MainNotions.S
open scoped InnerProductSpace TensorProduct

namespace Formalism.L2.SG.EvalTPh

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem phLoc_int_of_gap (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D)
    (v : NumberField.InfinitePlace X.B.I.F) :
    Integrable (phLoc (ε := X.B.I.ε v) (X.B.σ v) (X.B.w v) (X.dv v)) (Formalism.REAL.muG (X.B.I.ε v)) := by
  have h := Formalism.L2.SG.WuDecayPf.coef_integrable_of_weighted X
    (Formalism.L2.SG.Pf.WuDec.coefWeighted_of_gap X Formalism.L2.SG.Closed.CoefWeightedLoc_holds hG) v
  have hs : Integrable (star (Formalism.L2.SG.WuDecayPf.coefV X v)) (Formalism.REAL.muG (X.B.I.ε v)) :=
    memLp_one_iff_integrable.mp (memLp_one_iff_integrable.mpr h).star
  exact hs.const_mul (X.dv v : ℂ)

variable {S : D.what₂.Tau → SPar} {M : DSModel (D.sp.Y 0) S} {E : Submodule ℂ (MMap M)}
  {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {ι : GA D (D.sp.Y 0) ≃* X.B.I.GA} {t : GA D (D.sp.Y 0)} {v₀ : M.Vec}

end Formalism.L2.SG.EvalTPh

end
end
