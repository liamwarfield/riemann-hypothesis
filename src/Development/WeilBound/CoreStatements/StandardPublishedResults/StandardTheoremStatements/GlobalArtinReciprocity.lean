module

public import CompanionTheory.AutomorphicTheory.PlaceSeparation.IsOpenQuotientMapArt0
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrincipalIdealSt
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.HermitianHassePrincipleHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.ThetaRationalInvarianceHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.PlaneFormNondegenerate
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.FiniteDimensionalNablaSq

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.StandardPublishedResults.StandardTheoremStatements.GlobalArtinReciprocity
namespace PositivityTheory.Stage1.PM

theorem globalArtinReciprocity : GlobalTheory.Published.GlobalArtinReciprocity :=
  CompanionTheory.FamInh.globalArtin

theorem rayClassFieldSt : GlobalTheory.Published.RayClassFieldSt :=
  GlobalTheory.Published.GlobalArtinReciprocity.rayClassFieldSt CompanionTheory.FamInh.globalArtin

theorem heckeLAdicCharacter : GlobalTheory.Published.HeckeLAdicCharacter :=
  GlobalTheory.Published.GlobalArtinReciprocity.heckeLAdicCharacter CompanionTheory.FamInh.globalArtin

end PositivityTheory.Stage1.PM
end

section -- merged from Development.WeilBound.CoreStatements.StandardPublishedResults.StandardTheoremStatements.HermitianHassePrinciple
namespace PositivityTheory.Stage1.PM

theorem hermitianHassePrinciple : GlobalTheory.Published.HermitianHassePrinciple :=
  GlobalTheory.Published.hermitianHassePrinciple_holds

theorem thetaRationalInvariance : GlobalTheory.Published.ThetaRationalInvariance :=
  GlobalTheory.Published.thetaRationalInvariance_holds

theorem stoneVonNeumann : GlobalTheory.Published.StoneVonNeumann :=
  GlobalTheory.Published.StoneVonNeumann_holds

end PositivityTheory.Stage1.PM
end
