module

public import Mathlib
public import Lemmata.MiscLemmasJ.Imports

@[expose] public section

namespace Bl.general_b_fact_left''''''''

theorem goal1 :
    ∀ {K V : Type} [inst : Field K] [NumberField K] [inst_2 : AddCommGroup V]
      [inst_3 : _root_.Module K V] [inst_4 : _root_.Module (NumberField.RingOfIntegers K) V]
      [IsScalarTower (NumberField.RingOfIntegers K) K V]
      (L : Submodule (NumberField.RingOfIntegers K) V),
      ∀ v ∈ Submodule.span K (SetLike.coe L), ∃ (d : NumberField.RingOfIntegers K), d ≠ 0 ∧ d • v ∈ L := by
  intro K V _ _ _ _ _ _ L v hv
  exact Bl.SecondBlockLemmaK.goal1 L hv
end Bl.general_b_fact_left''''''''
