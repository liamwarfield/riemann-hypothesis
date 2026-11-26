module

public import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.NumericalSegre

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.NumericalSegreClosed
namespace GlobalTheory.CompanionTheory.Segre

theorem numericalSegre_closed : GroundTheory.Heights₂.Heights.NumbersDVR.NumericalSegre.Statement :=
  GroundTheory.Heights₂.Heights.NumbersDVR.NumericalSegre.full

end GlobalTheory.CompanionTheory.Segre
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ProjectionFormulaDegree
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ProjectionFormulaDegree
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.FieldNumbers

open GroundTheory.Heights₂.Heights.FieldNumbers GroundTheory.Heights₂.Heights.NumbersDVR

theorem projectionFormulaDegree :
    GroundTheory.Heights₂.Heights.FieldNumbers.ProjectionFormulaDegree.Statement.{0} :=
  ProjectionFormulaDegree.of_divPushForward
    (DivPushForward.proof ContractRelDimLe.proof DivPushForwardLocalZero)

end GlobalTheory.CompanionTheory.FieldNumbers
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ProjectionFormulaDegreeStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projection_formula_degree : GroundTheory.Heights₂.Heights.FieldNumbers.ProjectionFormulaDegree.Statement.{0} := by
  first | exact @GlobalTheory.CompanionTheory.FieldNumbers.projectionFormulaDegree | exact GlobalTheory.CompanionTheory.FieldNumbers.projectionFormulaDegree | (intros; apply GlobalTheory.CompanionTheory.FieldNumbers.projectionFormulaDegree <;> assumption)
end
end
