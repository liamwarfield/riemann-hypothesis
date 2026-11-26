module

public import Mathlib

@[expose] public section

namespace Bl.FirstBlockLemmaF

theorem goal1 :
    ∀ (p : ℕ) [hp : Fact (Nat.Prime p)] {a b : ℂ_[p]} {c : ℝ}, ‖a‖ ≤ c → ‖b‖ ≤ c → ‖a - b‖ ≤ c := by
  intro p hp a b c ha hb
  rw [sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max a (-b)).trans (max_le ha ?_)
  rw [norm_neg]
  exact hb

end Bl.FirstBlockLemmaF
