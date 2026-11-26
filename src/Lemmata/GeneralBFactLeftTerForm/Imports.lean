module

public import Mathlib
public import Lemmata.MiscLemmasJ.Imports

@[expose] public section

namespace Bl.general_b_fact_left_ter_form

theorem goal1 :
    ∀ {R K V : Type} [inst : CommRing R] [IsDomain R] [inst_2 : Field K] [inst_3 : Algebra R K]
      [IsFractionRing R K] [inst_5 : AddCommGroup V] [inst_6 : _root_.Module R V]
      [inst_7 : _root_.Module K V] [IsScalarTower R K V] (M : Submodule R V),
      ∀ y ∈ Submodule.span K (SetLike.coe M), ∃ (s : R), s ≠ 0 ∧ s • y ∈ M := by
  intro R K V _ _ _ _ _ _ _ _ _ M y hy
  exact Bl.SecondBlockLemmaK.goal1 M hy
end Bl.general_b_fact_left_ter_form
