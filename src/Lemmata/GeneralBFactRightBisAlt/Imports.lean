module

public import Mathlib

@[expose] public section

universe u_1

namespace Bl.general_b_fact_right_bis_other

theorem goal1 :
    ∀ {K : Type u_1} [inst : CommRing K] {n : ℕ} {l l' : Matrix (Fin n) (Fin n) K},
      (∀ (a b : Fin n), a < b → l a b = 0) →
        (∀ (a b : Fin n), a < b → l' a b = 0) → ∀ (a : Fin n), (l * l') a a = l a a * l' a a := by
  intro K _ n l l' hl hl' a
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single a ?_ ?_
  · intro c _ hca
    rcases lt_or_gt_of_ne hca with h | h
    · rw [hl' c a h, mul_zero]
    · rw [hl a c h, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ a) h

end Bl.general_b_fact_right_bis_other
