module

public import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.BesselXiIntegrable
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsUnitaryOfGramEq
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.NatCastMulCoeffOfPderivEq
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedA

@[expose] public section

namespace GlobalTheory.HCXi

theorem xiExists_of_besselXiIntegrable : BesselXiIntegrable → Formalism.FourierDecayAlt.B.XiExists := fun h => h

end GlobalTheory.HCXi
