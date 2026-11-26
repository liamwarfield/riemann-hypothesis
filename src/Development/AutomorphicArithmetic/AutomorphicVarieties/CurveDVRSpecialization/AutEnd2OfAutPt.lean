module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.EveryPointSatisfiesFrameCondition
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.DatFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.SubSmulMulSubSmulEqZeroOfQuadratic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ExistsIsFlagOnOfEigenvectorNormalSubgroup

@[expose] public section

open NumberField IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Aut UpperTheory.V.Pr UpperTheory.V

namespace UpperTheory.V.Pr.LkAut2

open Matrix

section Red

variable {O A Γ : Type} [CommRing O] [IsLocalRing O] [CommRing A] [IsLocalRing A] [Algebra O A] [Group Γ]
  {η : Γ →* ℤˣ} {Ψ : Γ →* Oˣ} {r : Γ →* GG (m := 3) (R := A)}

end Red

end UpperTheory.V.Pr.LkAut2
