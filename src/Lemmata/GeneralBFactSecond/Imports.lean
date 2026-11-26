module

public import Mathlib
public import Lemmata.MiscLemmasJ.Imports

@[expose] public section

namespace Bl.general_b_fact_second

theorem goal1 :
    ∀ {K : Type} [inst : Field K] [NumberField K] {r : ℕ}
      (L : Submodule (NumberField.RingOfIntegers K) (Fin r → K)),
      Submodule.span K (SetLike.coe L) = ⊤ →
        ∀ (x : Fin r → K), ∃ (d : NumberField.RingOfIntegers K), d ≠ 0 ∧ d • x ∈ L := by
  intro K _ _ r L hL x
  exact Bl.SecondBlockLemmaK.goal1 L (by rw [hL]; exact Submodule.mem_top)
end Bl.general_b_fact_second
