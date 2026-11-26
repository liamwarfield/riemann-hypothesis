module

public import Mathlib

@[expose] public section

universe u_1

namespace Bl.SecondBlockLemmaF

theorem goal1 :
    ∀ {M : Type u_1} [inst : AddCommMonoid M] (r : ℕ) (S : Fin (r + 1) → Finset ℕ)
      (F : (Fin (r + 1) → ℕ) → M),
      ∑ μ ∈ Fintype.piFinset S, F μ =
        ∑ a ∈ S 0, ∑ μ' ∈ Fintype.piFinset fun (t : Fin r) ↦ S t.succ, F (Fin.cons a μ') := by
  intro M _ r S F
  rw [← Finset.sum_product' (f := fun a μ' => F (Fin.cons a μ'))]
  refine Finset.sum_nbij' (fun μ => (μ 0, Fin.tail μ)) (fun p => Fin.cons p.1 p.2) ?_ ?_ ?_ ?_ ?_
  · intro μ hμ
    simp only [Fintype.mem_piFinset, Finset.mem_product] at hμ ⊢
    exact ⟨hμ 0, fun t => hμ t.succ⟩
  · intro p hp
    simp only [Fintype.mem_piFinset, Finset.mem_product] at hp ⊢
    intro i
    refine Fin.cases ?_ (fun t => ?_) i
    · simpa only [Fin.cons_zero] using hp.1
    · simpa only [Fin.cons_succ] using hp.2 t
  · intro μ _
    exact Fin.cons_self_tail μ
  · intro p _
    simp only [Fin.cons_zero, Fin.tail_cons]
  · intro μ _
    simp only [Fin.cons_self_tail]

end Bl.SecondBlockLemmaF
