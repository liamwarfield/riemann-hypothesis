module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.ClosedHT
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.LocTowerHolds
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.CstSmooth2

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.CstSmoothOfSide
section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CstSmooth
noncomputable section

open AlgebraicGeometry

namespace CrystallineSemistableComparison.Out

def CstSmooth : Prop := SmoothModelCrystalline ∧ DeRhamComparisonSmooth ∧ CrysPhi

def EtSideS : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K],
  EtSide (Model.Sm (l := l) (K := K))

end CrystallineSemistableComparison.Out
end
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.OutBridge
noncomputable section

namespace CrystallineSemistableComparison.Out

theorem cstSmooth_of_side (h : EtSideS) : CstSmooth := CrystallineSemistableComparison.cstSmooth_of_side h

end CrystallineSemistableComparison.Out
end
end

namespace CrystallineSemistableComparison.Close

theorem cstSmooth_of_side (h : CrystallineSemistableComparison.Out.EtSideS) : CrystallineSemistableComparison.Out.CstSmooth := CrystallineSemistableComparison.Out.cstSmooth_of_side h

end CrystallineSemistableComparison.Close
end

namespace UpperTheory.Gal.Seam

theorem cstSmooth : CrystallineSemistableComparison.CstSmooth := CrystallineSemistableComparison.Close.cstSmooth_of_side HT.etSideS

theorem crysStep_holds : UpperTheory.Gal.Int.Geo.CrysStep := crysStep_of cstSmooth.1

end UpperTheory.Gal.Seam
