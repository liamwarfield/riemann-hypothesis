module

public import Mathlib
public import Lemmata.MiscLemmasJ.Imports

@[expose] public section

namespace Bl.general_b_fact_third''''''

theorem goal1 :
    ∀ {E : Type} [inst : Field E] [NumberField E] {V : Type} [inst_2 : AddCommGroup V]
      [inst_3 : _root_.Module E V] [inst_4 : _root_.Module (NumberField.RingOfIntegers E) V]
      [IsScalarTower (NumberField.RingOfIntegers E) E V]
      (Λ : Submodule (NumberField.RingOfIntegers E) V),
      Submodule.span E (SetLike.coe Λ) = ⊤ → ∀ (x : V), ∃ (d : NumberField.RingOfIntegers E), d ≠ 0 ∧ d • x ∈ Λ := by
  intro E _ _ V _ _ _ _ Λ hΛ x
  exact Bl.SecondBlockLemmaK.goal1 Λ (by rw [hΛ]; exact Submodule.mem_top)
end Bl.general_b_fact_third''''''
