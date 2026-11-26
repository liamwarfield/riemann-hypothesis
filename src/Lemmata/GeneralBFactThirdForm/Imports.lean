module

public import Mathlib
public import Lemmata.MiscLemmasJ.Imports

@[expose] public section

namespace Bl.general_b_fact_third_form

theorem goal1 :
    ∀ {E V : Type} [inst : Field E] [NumberField E] [StarRing E] [inst_3 : AddCommGroup V]
      [inst_4 : _root_.Module E V] [FiniteDimensional E V]
      [inst_6 : _root_.Module (NumberField.RingOfIntegers E) V]
      [inst_7 : IsScalarTower (NumberField.RingOfIntegers E) E V]
      (Λ : Submodule (NumberField.RingOfIntegers E) V) [hΛ : Submodule.IsFullLattice E Λ] (v : V),
      ∃ (s : NumberField.RingOfIntegers E), s ≠ 0 ∧ s • v ∈ Λ := by
  intro E V _ _ _ _ _ _ _ _ Λ hΛ v
  exact Bl.SecondBlockLemmaK.goal1 Λ (by rw [hΛ.span_eq_top]; exact Submodule.mem_top)
end Bl.general_b_fact_third_form
