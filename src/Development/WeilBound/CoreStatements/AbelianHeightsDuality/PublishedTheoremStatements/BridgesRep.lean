module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymplOHZeroRight
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SqIntIrrPerm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqSmulOfStableGraph

@[expose] public section

namespace PositivityTheory.Prw

theorem flathFactorisation_of (h₁ : GlobalTheory.Published.FlathTensorProduct) (h₂ : GlobalTheory.Published.UnitaryIrreducibleAdmissible) :
    GlobalTheory.Published.FlathFactorisation :=
  GlobalTheory.flathFactorisation_of_tensorProduct h₁ h₂

end PositivityTheory.Prw
