module

public import Mathlib
public import Lemmata.MiscLemmasJ.Imports

@[expose] public section

namespace Bl.general_b_fact_second''''''''

theorem goal1 :
    ∀ {K : Type} [inst : Field K] [NumberField K] {V : Type} [inst_2 : AddCommGroup V]
      [inst_3 : _root_.Module K V] [inst_4 : _root_.Module (NumberField.RingOfIntegers K) V]
      [IsScalarTower (NumberField.RingOfIntegers K) K V]
      (M : Submodule (NumberField.RingOfIntegers K) V) {x : V},
      x ∈ Submodule.span K ↑M → ∃ (d : NumberField.RingOfIntegers K), d ≠ 0 ∧ d • x ∈ M := by
  intro K _ _ V _ _ _ _ M x hx
  exact Bl.SecondBlockLemmaK.goal1 M hx
end Bl.general_b_fact_second''''''''
