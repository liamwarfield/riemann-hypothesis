module

public import Mathlib

@[expose] public section

namespace Bl.general_b_fact_second_last

theorem goal1 :
    ∀ (B : ℤ) {S : ℕ} (c : Fin S → ℤ),
      (∀ (m : Fin S), |c m| < B) → ∑ m : Fin S, c m * B ^ (m : ℕ) = 0 → ∀ (m : Fin S), c m = 0 := by
  intro B S
  induction S with
  | zero => intro c _ _ m; exact m.elim0
  | succ n ih =>
    intro c hc hs m
    have hB : 0 < B := lt_of_le_of_lt (abs_nonneg _) (hc 0)
    rw [Fin.sum_univ_succ] at hs
    have h2 : ∑ i : Fin n, c i.succ * B ^ (i.succ).val = B * ∑ i : Fin n, c i.succ * B ^ i.val := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Fin.val_succ, pow_succ]
      ring
    rw [h2, Fin.val_zero, pow_zero, mul_one] at hs
    have hd : B ∣ c 0 := ⟨-(∑ i : Fin n, c i.succ * B ^ i.val), by rw [mul_neg]; linarith⟩
    have h0 : c 0 = 0 := Int.eq_zero_of_abs_lt_dvd hd (hc 0)
    rw [h0, zero_add] at hs
    have hT : ∑ i : Fin n, c i.succ * B ^ i.val = 0 := by
      rcases mul_eq_zero.mp hs with h | h
      · exact absurd h hB.ne'
      · exact h
    have ih' := ih (fun i => c i.succ) (fun i => hc _) hT
    exact Fin.cases h0 (fun i => ih' i) m

end Bl.general_b_fact_second_last
