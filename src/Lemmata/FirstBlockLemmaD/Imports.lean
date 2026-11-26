module

public import Mathlib

@[expose] public section

namespace Bl.FirstBlockLemmaD

theorem goal1 :
    ∀ {p : ℕ} [inst : Fact (Nat.Prime p)] (x y : PadicAlgCl p), ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  intro p inst x y
  have h := IsUltrametricDist.norm_add_le_max x (-y)
  rw [norm_neg, ← sub_eq_add_neg] at h
  exact h

end Bl.FirstBlockLemmaD
