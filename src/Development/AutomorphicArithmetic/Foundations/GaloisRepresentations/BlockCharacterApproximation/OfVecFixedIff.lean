module

public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BlockCharacterApproximation.PolyApproxCut
noncomputable section

open Polynomial Finset GlobalTheory.Cong

namespace UpperTheory.Gal.CharacterCongruences

section Approx

variable {k : Type} [NormedField k] [IsUltrametricDist k] {J : Type}

def PolyApproxAt (ε : ℝ) (θ : J → k) (S : Set (J → k)) : Prop :=
  ∃ (s : Finset (J → k)) (c : (J → k) → k), (s : Set (J → k)) ⊆ S ∧
    ∀ P : MvPolynomial J ℤ, ‖MvPolynomial.aeval θ P - ∑ η ∈ s, c η * MvPolynomial.aeval η P‖ ≤ ε


end Approx

section Ring

variable (O : Type) [CommRing O] (l N m : ℕ)

end Ring

abbrev Ch (n : ℕ) : Type := Multiplicative (ZMod n) →* ℂˣ

end UpperTheory.Gal.CharacterCongruences

end
end

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.PRep
open ValuativeRel

namespace UpperTheory.Gal.CharacterCongruences

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

structure IsLevel (C : Subgroup (UA E a)) : Prop where
  fin : C ≤ finU (E := E) (n := a)
  compact : IsCompact (C : Set (UA E a))
  isOpen : ∃ N : Set (UA E a), IsOpen N ∧ 1 ∈ N ∧ N ∩ finU (E := E) (n := a) ⊆ C

def TorsFreeAt (K : Subgroup (UA E a)) (u : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∀ k ∈ K, IsOfFinOrder (cLoc u k) → cLoc u k = 1

def NeatOfPlace : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (C : Subgroup (UA E a)), IsLevel C → ∀ u, TorsFreeAt C u →
    ∀ g : UA E a, ∀ γ ∈ ratU E a, ∀ c ∈ C, ∀ x ∈ infU E a, γ * g = g * c * x → c = 1

end UpperTheory.Gal.CharacterCongruences

end
