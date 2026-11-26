module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsReducedNormalModelGenericCorrespondence
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicOfRoot
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoefAtOfTwAdm
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ConjTwOfOne

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_conj_coef_at' : _root_.GlobalTheory.BigOn.Exp.TwAdmAlt → _root_.GlobalTheory.BigOn.Exp.TwConj.CoefficientCondition := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.TwConj.coefAt_of_twAdm_alt | exact _root_.GlobalTheory.BigOn.Exp.TwConj.coefAt_of_twAdm_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.TwConj.coefAt_of_twAdm_alt <;> assumption)
end
