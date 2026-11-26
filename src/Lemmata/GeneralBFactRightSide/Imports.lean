module

public import Mathlib

@[expose] public section

namespace Bl.general_b_fact_right_side

theorem goal1 :
    ∀ (x : ℝ), Complex.exp (2 * ↑Real.pi * Complex.I * ↑x) = 1 ↔ ∃ (n : ℤ), x = ↑n := by
  intro x
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h2 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have h3 : (x : ℂ) = (n : ℂ) := by
      rw [mul_comm (n : ℂ)] at hn
      exact mul_left_cancel₀ h2 hn
    exact_mod_cast h3
  · rintro ⟨n, rfl⟩
    exact ⟨n, by push_cast; ring⟩

end Bl.general_b_fact_right_side
