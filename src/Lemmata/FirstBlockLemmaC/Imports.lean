module

public import Mathlib

@[expose] public section

namespace Bl.FirstBlockLemmaC

theorem goal1 :
    ∀ {p : ℕ} [inst : Fact (Nat.Prime p)] {m : ℕ}, m ≠ 0 → ∀ {ζ : PadicAlgCl p}, ζ ^ m = 1 → ‖ζ‖ = 1 := by
  intro p _ m hm ζ h
  have h1 : ‖ζ‖ ^ m = 1 := by rw [← norm_pow, h, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm).mp h1

end Bl.FirstBlockLemmaC
