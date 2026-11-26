module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.SolvableEquivalenceOfBaseChange

@[expose] public section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.isLocalHom UpperTheory.V.Pr.IsCD.fin

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc UpperTheory.V.Af.Sol

namespace UpperTheory.V.Z.Bc

def ExRTwo : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (π : TR.CuspSub F 2) (χ : HChar F), π.IsRegAlg → π.Polarized χ →
    ∃ r : G F Ω →* GL (Fin 2) (Qbar l), Continuous r ∧ AttR ι r π

theorem galois_rep_rank_two_of_hypotheses (P : HypothesesH) : ExRTwo := fun F Ω _ _ _ _ _ _ l _ ι π χ h1 h2 =>
  let ⟨r, _, _, H, h, _⟩ := exR P F Ω l ι 2 one_le_two π χ h1 h2
  ⟨r, H.cont, h⟩

end UpperTheory.V.Z.Bc
