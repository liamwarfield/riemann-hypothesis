module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SymmetricSquareMixedExists
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.InducedFinalStatement
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.ClosedOneU
public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.MixSeedOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.InducedIrreducible
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.QuadraticSplitting.IndGlobOfKill
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.InducedFlagCondition
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.PropEG2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.QuadraticSplitting.Imports
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.QuadraticInductionGL2Alt

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.IndAut
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal
open GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Sd UpperTheory.V.Base
open scoped Pointwise

section Grp

variable {Γ Γ' k : Type} [Group Γ] [Group Γ'] [Field k] {e : Γ' →* Γ} {δ : Γ →* kˣ}

end Grp

section Places

variable {F E Ω : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Field Ω] [Algebra F E] [Algebra F Ω] [Algebra E Ω]
  [IsScalarTower F E Ω]

end Places

end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S2

section

variable {l : ℕ} [Fact l.Prime]

end
