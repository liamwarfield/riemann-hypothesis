module

public import Mathlib
public import Lemmata.MiscLemmasJ.Imports

@[expose] public section

namespace Bl.general_b_fact_third_ter

theorem goal1 :
    ∀ {E : Type} [inst : Field E] [NumberField E] [StarRing E] {W : Type} [inst_3 : AddCommGroup W]
      [inst_4 : _root_.Module E W] [inst_5 : _root_.Module (NumberField.RingOfIntegers E) W]
      [IsScalarTower (NumberField.RingOfIntegers E) E W]
      (L : Submodule (NumberField.RingOfIntegers E) W),
      Submodule.span E (SetLike.coe L) = ⊤ → ∀ (y : W), ∃ (ν : NumberField.RingOfIntegers E), ν ≠ 0 ∧ ν • y ∈ L := by
  intro E _ _ _ W _ _ _ _ L hL y
  exact Bl.SecondBlockLemmaK.goal1 L (by rw [hL]; exact Submodule.mem_top)
end Bl.general_b_fact_third_ter
