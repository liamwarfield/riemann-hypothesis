module

public import Mathlib
public import Lemmata.MiscLemmasJ.Imports

@[expose] public section

open NumberField IsDedekindDomain

namespace Bl.SecondBlockLemmaE

variable {E V : Type} [Field E] [NumberField E] [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]

theorem goal1 {Λ : Submodule (𝓞 E) V} {v : V}
    (hv : v ∈ Submodule.span E (Λ : Set V)) : ∃ d : 𝓞 E, d ≠ 0 ∧ d • v ∈ Λ := by
  exact Bl.SecondBlockLemmaK.goal1 Λ hv
end Bl.SecondBlockLemmaE
