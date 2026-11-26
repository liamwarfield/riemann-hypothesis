module

public import Mathlib
public import Lemmata.MiscLemmasJ.Imports

@[expose] public section

namespace Bl.general_b_fact_third_alt

theorem goal1 :
    ∀ {K : Type} [inst : Field K] [NumberField K] {n : ℕ}
      (R : Submodule (NumberField.RingOfIntegers K) (Fin n → K)),
      ∀ x ∈ Submodule.span K (SetLike.coe R), ∃ (d : NumberField.RingOfIntegers K), d ≠ 0 ∧ d • x ∈ R := by
  intro K _ _ n R x hx
  exact Bl.SecondBlockLemmaK.goal1 R hx
end Bl.general_b_fact_third_alt
