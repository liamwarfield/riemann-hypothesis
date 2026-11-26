module

public import Mathlib
public import Lemmata.MiscLemmasJ.Imports

@[expose] public section

namespace Bl.general_b_fact_right_alt_form

theorem goal1 :
    ∀ {E : Type} [inst : Field E] [NumberField E] {V : Type} [inst_2 : AddCommGroup V]
      [inst_3 : _root_.Module E V] [inst_4 : _root_.Module (NumberField.RingOfIntegers E) V]
      [IsScalarTower (NumberField.RingOfIntegers E) E V] (A : Set V),
      ∀ y ∈ Submodule.span E A,
        ∃ (d : NumberField.RingOfIntegers E),
          d ≠ 0 ∧ d • y ∈ Submodule.span (NumberField.RingOfIntegers E) A := by
  intro E _ _ V _ _ _ _ A y hy
  exact Bl.SecondBlockLemmaK.goal1 (Submodule.span (NumberField.RingOfIntegers E) A) (Submodule.span_mono Submodule.subset_span hy)
end Bl.general_b_fact_right_alt_form
