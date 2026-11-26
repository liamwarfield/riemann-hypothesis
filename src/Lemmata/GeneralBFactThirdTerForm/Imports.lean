module

public import Mathlib
public import Lemmata.MiscLemmasJ.Imports

@[expose] public section

namespace Bl.general_b_fact_third_ter_form

theorem goal1 :
    ∀ {K W : Type} [inst : Field K] [NumberField K] [inst_2 : AddCommGroup W]
      [inst_3 : _root_.Module K W] [inst_4 : _root_.Module (NumberField.RingOfIntegers K) W]
      [inst_5 : IsScalarTower (NumberField.RingOfIntegers K) K W]
      (Λ : Submodule (NumberField.RingOfIntegers K) W) [hΛ : Submodule.IsFullLattice K Λ] (v : W),
      ∃ (s : NumberField.RingOfIntegers K), s ≠ 0 ∧ s • v ∈ Λ := by
  intro K W _ _ _ _ _ _ Λ hΛ v
  exact Bl.SecondBlockLemmaK.goal1 Λ (by rw [hΛ.span_eq_top]; exact Submodule.mem_top)

end Bl.general_b_fact_third_ter_form
