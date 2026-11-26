module

public import Mathlib
public import Lemmata.MiscLemmasJ.Imports

@[expose] public section

open Module

namespace Bl.SecondBlockLemmaM

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]

theorem goal1 [IsDomain R] [IsFractionRing R C]
    {V : Type} [AddCommGroup V] [Module C V] [Module R V] [IsScalarTower R C V]
    (S : Submodule R V) {x : V} (hx : x ∈ Submodule.span C (S : Set V)) :
    ∃ r : R, r ≠ 0 ∧ r • x ∈ S := by
  exact Bl.SecondBlockLemmaK.goal1 S hx
end Bl.SecondBlockLemmaM
