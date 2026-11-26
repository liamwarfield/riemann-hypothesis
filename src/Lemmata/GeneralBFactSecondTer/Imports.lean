module

public import Mathlib

@[expose] public section

namespace Bl.general_b_fact_second_ter

theorem goal1 :
    ∀ {n : ℕ} (Q : Fin n → Prop) [inst : DecidablePred Q],
      (∀ (q q' : Fin n), q' ≤ q → Q q → Q q') →
        ∀ (p : Fin n), Q p ↔ ↑p < (Finset.filter Q Finset.univ).card := by
  intro n Q _ hQ p
  constructor
  · intro hp
    have h : Finset.Iic p ⊆ Finset.filter Q Finset.univ := by
      intro q hq
      rw [Finset.mem_Iic] at hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hQ p q hq hp
    have hc := Finset.card_le_card h
    rw [Fin.card_Iic] at hc
    omega
  · intro hlt
    by_contra hp
    have h : Finset.filter Q Finset.univ ⊆ Finset.Iio p := by
      intro q hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
      rw [Finset.mem_Iio]
      by_contra hqp
      exact hp (hQ q p (not_lt.mp hqp) hq)
    have hc := Finset.card_le_card h
    rw [Fin.card_Iio] at hc
    omega

end Bl.general_b_fact_second_ter
