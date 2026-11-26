module

public import Mathlib

@[expose] public section

namespace Bl.general_b_fact_right'''

theorem goal1 :
    ∀ {K : Type} [inst : NormedField K] [IsUltrametricDist K] {p : ℕ} {a b : K},
      ‖a‖ ≤ 1 → ‖b‖ ≤ 1 → ‖a - b‖ ≤ (↑p)⁻¹ → ∀ (k : ℕ), ‖a ^ k - b ^ k‖ ≤ (↑p)⁻¹ := by
  intro K _ _ p a b ha hb hab k
  induction k with
  | zero => simp
  | succ n ih =>
    have e : a ^ (n + 1) - b ^ (n + 1) = a ^ n * (a - b) + (a ^ n - b ^ n) * b := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul, norm_pow]
      calc ‖a‖ ^ n * ‖a - b‖ ≤ 1 * ‖a - b‖ := by
            gcongr
            exact pow_le_one₀ (norm_nonneg _) ha
        _ = ‖a - b‖ := one_mul _
        _ ≤ _ := hab
    · rw [norm_mul]
      calc ‖a ^ n - b ^ n‖ * ‖b‖ ≤ ‖a ^ n - b ^ n‖ * 1 := by gcongr
        _ = ‖a ^ n - b ^ n‖ := mul_one _
        _ ≤ _ := ih

end Bl.general_b_fact_right'''
