module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectionStatementHolds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneFormMapRowThreeLevelOfCharacterisation
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReadCmpAt

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp GlobalTheory.BigOn.Exp.SerBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.readCmpAt_of_serBase : _root_.GlobalTheory.BigOn.Exp.SerBase.ReadComparisonAt := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.SerBase.readCmpAt_alt | exact _root_.GlobalTheory.BigOn.Exp.SerBase.readCmpAt_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.SerBase.readCmpAt_alt <;> assumption)
end
