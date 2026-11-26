module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.ArthurClozelDescent
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HermitianTwists.CentChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Places
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GuDefs

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.SymmetricAdjointFrobenius.IndInf
noncomputable section

open NumberField Formalism.REAL

namespace UpperTheory.V.Lit

section Alg

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

end Alg

variable {E : Type} [Field E] [NumberField E] [IsTotallyReal E] {a : ℕ}

end UpperTheory.V.Lit
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.SymmetricAdjointFrobenius.PullPar
noncomputable section

open NumberField IsDedekindDomain Topology Matrix Neutral.B1 Formalism.L2.Host Formalism.L2.Host.CT GlobalTheory.CuspRep
open scoped ContDiff

namespace UpperTheory.V.Lit

section Comp

variable {E : Type} [Field E] [NumberField E] [IsTotallyReal E]

variable {σ : E ≃+* E} {s : Ad E →+* Ad E} (hs : IsAdExt (σ : E →+* E) s)
include hs

end Comp

section Pull

variable {E : Type} [Field E] [NumberField E] [IsTotallyReal E] {a : ℕ}

variable {σ : E ≃+* E} {s : Ad E →+* Ad E} (hs : IsAdExt (σ : E →+* E) s)
include hs

end Pull

end UpperTheory.V.Lit
end
end

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.HeckeGal
  GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Lit

section Places

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

end Places

section Main

variable {F E : Type} [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E] [IsTotallyReal E] [Algebra F E] {a : ℕ}

end Main
