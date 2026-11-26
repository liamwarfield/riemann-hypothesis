module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.LogarithmicNormBounds.HostUnl
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.Number

@[expose] public section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing

open NumberField Matrix IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.Aut UpperTheory.V.UnitaryThreeInertia
open IsDedekindDomain

section Host

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N]
  {e : ℕ} {ψ : DirichletCharacter c.O N} {o₁ : ℕ} {S : Finset Pl} {A : S → ValuationSubring Ω}
  {F : Frame c.O (Formalism.ConjugateSelfDual.G ℚ Ω) (Gam Ω S) S}

variable {K : Type} [Field K] [NumberField K] [IsCMField K] [Algebra K Ω] [IsScalarTower ℚ K Ω]

end Host

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.HV GlobalTheory.GalOfCusp UpperTheory.V.Th UpperTheory.V.Z.J
