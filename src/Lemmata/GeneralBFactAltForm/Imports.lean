module

public import Mathlib

@[expose] public section

universe u_1 u_2 u_3

namespace Bl.general_b_fact_alt_form

theorem goal1 :
    ∀ {R : Type u_1} {F : Type u_2} {X : Type u_3} [inst : CommRing R] [IsDomain R] [inst_2 : Field F]
      [inst_3 : Algebra R F] [IsFractionRing R F] [inst_5 : AddCommGroup X] [inst_6 : _root_.Module F X]
      [inst_7 : _root_.Module R X] [IsScalarTower R F X] (S : Submodule R X) {x : X},
      x ∈ Submodule.span F ↑S → ∃ (d : R), d ≠ 0 ∧ d • x ∈ S  := by
  intro R F X _ _ _ _ _ _ _ _ _ S x hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hy⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact S.zero_mem⟩
  | add y z _ _ hy hz =>
    obtain ⟨d1, hd1, h1⟩ := hy
    obtain ⟨d2, hd2, h2⟩ := hz
    refine ⟨d1 * d2, mul_ne_zero hd1 hd2, ?_⟩
    have e : (d1 * d2) • (y + z) = d2 • (d1 • y) + d1 • (d2 • z) := by
      rw [smul_add, ← mul_smul, ← mul_smul, mul_comm d2 d1]
    rw [e]
    exact S.add_mem (S.smul_mem d2 h1) (S.smul_mem d1 h2)
  | smul a y _ hy =>
    obtain ⟨d, hd, h⟩ := hy
    obtain ⟨⟨n, ⟨m, hm⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) a
    refine ⟨m * d, mul_ne_zero (nonZeroDivisors.ne_zero hm) hd, ?_⟩
    have e1 : m • (IsLocalization.mk' F n (⟨m, hm⟩ : nonZeroDivisors R) • y) = n • y := by
      rw [← smul_assoc, Algebra.smul_def, IsLocalization.mk'_spec' F n ⟨m, hm⟩, algebraMap_smul]
    have e : (m * d) • (IsLocalization.mk' F n (⟨m, hm⟩ : nonZeroDivisors R) • y) = n • (d • y) := by
      rw [mul_comm m d, mul_smul, e1, ← mul_smul, ← mul_smul, mul_comm d n]
    rw [e]
    exact S.smul_mem n h

end Bl.general_b_fact_alt_form
