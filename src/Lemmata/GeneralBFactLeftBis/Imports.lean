module

public import Mathlib
public import Lemmata.MiscLemmasJ.Imports

@[expose] public section

namespace Bl.general_b_fact_left_bis

theorem goal1 :
    ∀ {E : Type} [inst : Field E] [NumberField E] {N : ℕ}
      (L'' : Submodule (NumberField.RingOfIntegers E) (Fin N → E)),
      Submodule.span E (SetLike.coe L'') = ⊤ →
        ∀ (v : Fin N → E), ∃ (d : NumberField.RingOfIntegers E), d ≠ 0 ∧ d • v ∈ L'' := by
  intro E _ _ N L'' hspan v
  exact Bl.SecondBlockLemmaK.goal1 L'' (by rw [hspan]; exact Submodule.mem_top)
end Bl.general_b_fact_left_bis
