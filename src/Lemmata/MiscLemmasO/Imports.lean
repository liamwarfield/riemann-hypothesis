module

public import Mathlib
public import Lemmata.MiscLemmasJ.Imports

@[expose] public section

namespace Bl.SecondBlockLemmaP

theorem goal1 :
    ∀ (O K V : Type) [inst : CommRing O] [IsDomain O] [inst_2 : Field K] [inst_3 : Algebra O K]
      [IsFractionRing O K] [inst_5 : AddCommGroup V] [inst_6 : _root_.Module K V]
      [inst_7 : _root_.Module O V] [IsScalarTower O K V] (M : Submodule O V),
      ∀ v ∈ Submodule.span K (SetLike.coe M), ∃ (c : O), c ≠ 0 ∧ c • v ∈ M := by
  intro O K V _ _ _ _ _ _ _ _ _ M v hv
  exact Bl.SecondBlockLemmaK.goal1 M hv
end Bl.SecondBlockLemmaP
