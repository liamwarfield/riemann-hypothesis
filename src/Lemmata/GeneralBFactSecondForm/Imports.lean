module

public import Mathlib
public import Lemmata.MiscLemmasJ.Imports

@[expose] public section

namespace Bl.general_b_fact_second_form

theorem goal1 :
    ∀ {K V : Type} [inst : Field K] [NumberField K] [StarRing K] [inst_3 : AddCommGroup V]
      [inst_4 : _root_.Module K V] [inst_5 : _root_.Module (NumberField.RingOfIntegers K) V]
      [inst_6 : IsScalarTower (NumberField.RingOfIntegers K) K V]
      {Λ : Submodule (NumberField.RingOfIntegers K) V},
      Submodule.IsFullLattice K Λ → ∀ (v : V), ∃ (r : NumberField.RingOfIntegers K), r ≠ 0 ∧ r • v ∈ Λ := by
  intro K V _ _ _ _ _ _ _ Λ hΛ v
  exact Bl.SecondBlockLemmaK.goal1 Λ (by rw [hΛ.span_eq_top]; exact Submodule.mem_top)
end Bl.general_b_fact_second_form
