module

public import Mathlib
public import Lemmata.MiscLemmasJ.Imports

@[expose] public section

namespace Bl.general_b_fact_third_bis_other

theorem goal1 :
    ∀ {R K V : Type} [inst : CommRing R] [IsDomain R] [inst_2 : Field K] [inst_3 : Algebra R K]
      [IsFractionRing R K] [inst_5 : AddCommGroup V] [inst_6 : _root_.Module K V]
      [inst_7 : _root_.Module R V] [IsScalarTower R K V] (N : Submodule R V) {v : V},
      v ∈ Submodule.span K ↑N → ∃ (c : R), c ≠ 0 ∧ c • v ∈ N := by
  intro R K V _ _ _ _ _ _ _ _ _ N v hv
  exact Bl.SecondBlockLemmaK.goal1 N hv
end Bl.general_b_fact_third_bis_other
