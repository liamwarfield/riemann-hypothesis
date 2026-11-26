module

public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.SharpRestriction.CuspSpanNormBounds.DataS
public import Formalism.SharpRestriction.GrowthBounds.DataG
public import Formalism.LocalRingCardinality.DataCD

@[expose] public section

namespace Bl.general_b_fact_left_alt

theorem goal1 :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : StarRing E]
      {S : Formalism.BasicNotions.HSpace E} (Λ : Submodule (NumberField.RingOfIntegers E) S.V),
      Submodule.IsFullLattice E Λ → ∀ (v : S.V), ∃ (c : NumberField.RingOfIntegers E), c ≠ 0 ∧ c • v ∈ Λ := by
  intro E _ _ _ S Λ hΛ v
  have hv : v ∈ Submodule.span E (Λ : Set S.V) := by
    rw [hΛ.span_eq_top]; trivial
  obtain ⟨y, hy, z, rfl⟩ :=
    (IsLocalization.mem_span_iff (R := NumberField.RingOfIntegers E)
      (M := nonZeroDivisors (NumberField.RingOfIntegers E)) (S := E)).mp hv
  rw [Submodule.span_eq] at hy
  refine ⟨z, nonZeroDivisors.coe_ne_zero z, ?_⟩
  rw [← IsScalarTower.algebraMap_smul E (z : NumberField.RingOfIntegers E), smul_smul,
    IsLocalization.mk'_spec', map_one, one_smul]
  exact hy

end Bl.general_b_fact_left_alt
