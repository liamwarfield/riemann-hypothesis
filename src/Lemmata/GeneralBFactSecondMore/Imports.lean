module

public import Mathlib
public import Lemmata.MiscLemmasJ.Imports

@[expose] public section

namespace Bl.general_b_fact_second'

theorem goal1 :
    ∀ {E U : Type} [inst : Field E] [NumberField E] [inst_2 : AddCommGroup U]
      [inst_3 : _root_.Module E U] [inst_4 : _root_.Module (NumberField.RingOfIntegers E) U]
      [IsScalarTower (NumberField.RingOfIntegers E) E U]
      (N : Submodule (NumberField.RingOfIntegers E) U),
      Submodule.span E (SetLike.coe N) = ⊤ → ∀ (x : U), ∃ (d : NumberField.RingOfIntegers E), d ≠ 0 ∧ d • x ∈ N := by
  intro E U _ _ _ _ _ _ M hM x
  exact Bl.SecondBlockLemmaK.goal1 M (by rw [hM]; exact Submodule.mem_top)
end Bl.general_b_fact_second'
