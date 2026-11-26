module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SiegelSetUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8ThetaSetupGenericPointExists
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodChernWeilOfGoodTopChernForm

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.AbelianHeightsDuality.PublishedTheoremStatements.SiegelSetUnitaryHolds
namespace PositivityTheory.Prw

theorem siegelCore_holds : PositivityTheory.ThKR.SiegelCore :=
  GlobalTheory.CompanionTheory.SiegelRed.siegelCore

end PositivityTheory.Prw
end

section -- merged from Development.WeilBound.CoreStatements.AbelianHeightsDuality.PublishedTheoremStatements.BridgesGeo
namespace PositivityTheory.Prw

theorem arDegree_of (h₁ : GlobalTheory.Published.HeightProjection) (h₂ : GlobalTheory.Published.ChernDegreeComplex) : GlobalTheory.Published.ArDegree :=
  GlobalTheory.T.projectionFormulaAndChernDegree_of_heightProjection h₁ h₂

end PositivityTheory.Prw
end
