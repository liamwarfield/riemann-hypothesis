module

public import Mathlib

@[expose] public section

universe u_1 u_2

namespace Bl.general_b_fact_right_rest

private theorem aux {α : Type u_1} {β : Type u_2} (f : α → β) (t : Multiset α) :
    ∀ s : Multiset β, s ≤ t.map f → ∃ u : Multiset α, u ≤ t ∧ u.map f = s := by
  induction t using Multiset.induction_on with
  | empty =>
    intro s hs
    rw [Multiset.map_zero, Multiset.le_zero] at hs
    exact ⟨0, le_refl _, by rw [Multiset.map_zero, hs]⟩
  | cons a t ih =>
    intro s hs
    rw [Multiset.map_cons] at hs
    by_cases h : f a ∈ s
    · obtain ⟨s', rfl⟩ := Multiset.exists_cons_of_mem h
      rw [Multiset.cons_le_cons_iff] at hs
      obtain ⟨u, hu, hmap⟩ := ih s' hs
      exact ⟨a ::ₘ u, (Multiset.cons_le_cons_iff a).mpr hu, by rw [Multiset.map_cons, hmap]⟩
    · obtain ⟨u, hu, hmap⟩ := ih s ((Multiset.le_cons_of_notMem h).mp hs)
      exact ⟨u, hu.trans (Multiset.le_cons_self t a), hmap⟩

theorem goal1 :
    ∀ {α : Type u_1} {β : Type u_2} [DecidableEq β] (f : α → β) (t : Multiset α),
      ∀ s ≤ Multiset.map f t, ∃ u ≤ t, Multiset.map f u = s := by
  intro α β _ f t s h
  exact aux f t s h

end Bl.general_b_fact_right_rest
