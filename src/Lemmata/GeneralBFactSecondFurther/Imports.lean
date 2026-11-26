module

public import Mathlib
public import Lemmata.MiscLemmasJ.Imports

@[expose] public section

namespace Bl.general_b_fact_second''

theorem goal1 :
    ∀ {O K X : Type} [inst : CommRing O] [IsDomain O] [inst_2 : Field K] [inst_3 : Algebra O K]
      [IsFractionRing O K] [inst_5 : AddCommGroup X] [inst_6 : _root_.Module K X]
      [inst_7 : _root_.Module O X] [IsScalarTower O K X] (B : Submodule O X),
      Submodule.span K (SetLike.coe B) = ⊤ → ∀ (x : X), ∃ (d : O), d ≠ 0 ∧ d • x ∈ B := by
  intro O K X _ _ _ _ _ _ _ _ _ B hB x
  exact Bl.SecondBlockLemmaK.goal1 B (by rw [hB]; exact Submodule.mem_top)
end Bl.general_b_fact_second''
