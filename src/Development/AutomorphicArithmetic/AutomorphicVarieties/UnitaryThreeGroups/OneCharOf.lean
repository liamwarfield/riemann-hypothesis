module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ModelEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ModelUpper
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.VlenLe
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.PtHypOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.AdmissibleOfTypeII

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

section Transfer

variable {O O' : Type} [CommRing O] [CommRing O'] {N : ℕ} (f : O →+* O')

end Transfer

