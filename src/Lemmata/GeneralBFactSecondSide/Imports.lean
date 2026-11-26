module

public import Mathlib

@[expose] public section

namespace Bl.general_b_fact_second'''''

theorem goal1 :
    ∀ {K V : Type} [inst : Field K] [NumberField K] [StarRing K] [inst_3 : AddCommGroup V]
      [inst_4 : _root_.Module K V] [inst_5 : _root_.Module (NumberField.RingOfIntegers K) V]
      [inst_6 : IsScalarTower (NumberField.RingOfIntegers K) K V]
      (M : Submodule (NumberField.RingOfIntegers K) V),
      Submodule.IsFullLattice K M → ∀ (x : V), ∃ (n : ℤ), n ≠ 0 ∧ n • x ∈ M := by
  intro K V _ _ _ _ _ _ _ M hM x
  have hx : x ∈ Submodule.span K (M : Set V) := by
    rw [hM.span_eq_top]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    have h1 : (a * b) • y = b • (a • y) := by rw [mul_comm, mul_smul]
    have h2 : (a * b) • z = a • (b • z) := by rw [mul_smul]
    rw [smul_add, h1, h2]
    exact M.add_mem (zsmul_mem hay b) (zsmul_mem hbz a)
  | smul c y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨d, hd, hint⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ K).mpr (IsAlgebraic.of_finite ℚ c)).exists_integral_multiple
    let w : NumberField.RingOfIntegers K := ⟨d • c, hint⟩
    refine ⟨d * a, mul_ne_zero hd ha, ?_⟩
    have hw : (algebraMap (NumberField.RingOfIntegers K) K w) = (d : K) * c := by
      show (d • c : K) = _
      rw [zsmul_eq_mul]
    have key : (d * a) • (c • y) = w • (a • y) := by
      rw [← algebraMap_smul K w (a • y), hw, ← Int.cast_smul_eq_zsmul K, ← Int.cast_smul_eq_zsmul K,
        smul_smul, smul_smul]
      congr 1
      push_cast
      ring
    rw [key]
    exact M.smul_mem w hay

end Bl.general_b_fact_second'''''
