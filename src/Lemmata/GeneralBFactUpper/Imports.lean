module

public import Mathlib

@[expose] public section

namespace Bl.general_b_fact_upper

theorem goal1 :
    ∀ {K : Type} [inst : NormedField K] [IsUltrametricDist K] {x y : K},
      ‖x‖ ≤ 1 → ‖y‖ ≤ 1 → ∀ (n : ℕ), ‖x ^ n - y ^ n‖ ≤ ‖x - y‖ := by
  intro K _ _ x y hx hy n
  induction n with
  | zero => simp
  | succ n ih =>
    have e : x ^ (n + 1) - y ^ (n + 1) = x ^ n * (x - y) + (x ^ n - y ^ n) * y := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul, norm_pow]
      exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hx)
    · rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) hy).trans ih

end Bl.general_b_fact_upper
