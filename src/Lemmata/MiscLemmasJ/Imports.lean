module

public import Mathlib

@[expose] public section

namespace Bl.SecondBlockLemmaK

theorem goal1 :
    ∀ {R F X : Type} [inst : CommRing R] [IsDomain R] [inst_2 : Field F] [inst_3 : Algebra R F]
      [IsFractionRing R F] [inst_5 : AddCommGroup X] [inst_6 : _root_.Module F X]
      [inst_7 : _root_.Module R X] [IsScalarTower R F X] (S : Submodule R X) {x : X},
      x ∈ Submodule.span F ↑S → ∃ (d : R), d ≠ 0 ∧ d • x ∈ S := by
  intro R F X _ _ _ _ _ _ _ _ _ S x hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hy⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact S.zero_mem⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine S.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact S.smul_mem b hay
    · rw [mul_smul]
      exact S.smul_mem a hbz
  | smul c y _ hy =>
    obtain ⟨d, hd, hdy⟩ := hy
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) c
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have hbF : algebraMap R F b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    refine ⟨d * b, mul_ne_zero hd hb0, ?_⟩
    have key : (d * b) • ((algebraMap R F a / algebraMap R F b) • y) = a • (d • y) := by
      rw [← algebraMap_smul F (d * b), ← algebraMap_smul F a, ← algebraMap_smul F d, smul_smul, smul_smul]
      congr 1
      rw [map_mul]
      field_simp
    rw [key]
    exact S.smul_mem a hdy

end Bl.SecondBlockLemmaK
