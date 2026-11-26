module

public import Mathlib

@[expose] public section

universe u_1 u_3 u_4

namespace Bl.general_b_fact_side

theorem goal1 :
    ∀ {R : Type u_1} [inst : CommRing R] [inst_1 : IsLocalRing R] [IsNoetherianRing R] {N₁ : Type u_3}
      {N₂ : Type u_4} [inst_3 : AddCommGroup N₁] [inst_4 : _root_.Module R N₁] [Module.Finite R N₁]
      [inst_6 : AddCommGroup N₂] [inst_7 : _root_.Module R N₂] [Module.Finite R N₂],
      IsLocalRing.maximalIdeal R ∉ associatedPrimes R N₁ →
        IsLocalRing.maximalIdeal R ∉ associatedPrimes R N₂ →
          ∃ z ∈ IsLocalRing.maximalIdeal R, IsSMulRegular N₁ z ∧ IsSMulRegular N₂ z := by
  intro R _ _ _ N₁ N₂ _ _ _ _ _ _ h1 h2
  have hfin : (associatedPrimes R N₁ ∪ associatedPrimes R N₂).Finite :=
    (associatedPrimes.finite R N₁).union (associatedPrimes.finite R N₂)
  have hns : ¬ ((IsLocalRing.maximalIdeal R : Set R) ⊆
      ⋃ p ∈ associatedPrimes R N₁ ∪ associatedPrimes R N₂, (p : Set R)) := by
    intro hsub
    rw [Ideal.subset_iUnion_iff_mem_of_isMaximal_of_finite hfin ⊥ ⊥
      (fun I hI _ _ => hI.elim (fun h => h.1) (fun h => h.1)) bot_ne_top bot_ne_top] at hsub
    exact hsub.elim h1 h2
  obtain ⟨z, hzm, hz⟩ := Set.not_subset.mp hns
  refine ⟨z, hzm, ?_, ?_⟩
  · have hz1 : z ∉ ⋃ p ∈ associatedPrimes R N₁, (p : Set R) := fun h => by
      obtain ⟨p, hp, hzp⟩ := Set.mem_iUnion₂.mp h
      exact hz (Set.mem_biUnion (Or.inl hp) hzp)
    rw [biUnion_associatedPrimes_eq_compl_regular R N₁] at hz1
    simpa using hz1
  · have hz2 : z ∉ ⋃ p ∈ associatedPrimes R N₂, (p : Set R) := fun h => by
      obtain ⟨p, hp, hzp⟩ := Set.mem_iUnion₂.mp h
      exact hz (Set.mem_biUnion (Or.inr hp) hzp)
    rw [biUnion_associatedPrimes_eq_compl_regular R N₂] at hz2
    simpa using hz2

end Bl.general_b_fact_side
