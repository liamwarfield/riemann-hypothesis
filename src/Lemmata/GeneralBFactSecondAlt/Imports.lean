module

public import Mathlib
public import Lemmata.MiscLemmasJ.Imports

@[expose] public section

namespace Bl.general_b_fact_second_alt

theorem goal1 :
    ∀ {K : Type} [inst : Field K] [NumberField K] {r : ℕ}
      (L : Submodule (NumberField.RingOfIntegers K) (Fin r → K)),
      ∀ v ∈ Submodule.span K (SetLike.coe L), ∃ (a : NumberField.RingOfIntegers K), a ≠ 0 ∧ a • v ∈ L := by
  intro K _ _ r L v hv
  exact Bl.SecondBlockLemmaK.goal1 L hv
end Bl.general_b_fact_second_alt
