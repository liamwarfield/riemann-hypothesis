module

public import Mathlib

@[expose] public section

namespace Bl.general_b_fact_left'''''

private lemma aux {O A I : Type} [CommRing O] [CommRing A] [Algebra O A]
    [Fintype I] [DecidableEq I] {B : I → Type} [(i : I) → AddCommGroup (B i)]
    [(i : I) → Module O (B i)] (ε : (i : I) → B i →ₗ[O] A)
    (T : (i : I) → Set (B i)) (S : Submodule O A)
    (hS : ∀ F : (i : I) → B i, (∀ i, F i ∈ T i) → ∏ i, ε i (F i) ∈ S) :
    ∀ s : Finset I, ∀ F : (i : I) → B i, (∀ i ∈ s, F i ∈ Submodule.span O (T i)) →
      (∀ i ∉ s, F i ∈ T i) → ∏ i, ε i (F i) ∈ S := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro F _ h2
    exact hS F (fun i => h2 i (Finset.notMem_empty i))
  | insert j s hj ih =>
    intro F h1 h2
    have key : ∀ x : B j, ∏ i, ε i (Function.update F j x i)
        = ε j x * ∏ i ∈ Finset.univ \ {j}, ε i (F i) := by
      intro x
      have e : (fun i => ε i (Function.update F j x i))
          = Function.update (fun k => ε k (F k)) j (ε j x) := by
        funext i
        exact Function.apply_update (fun k => (ε k : B k → A)) F j x i
      rw [e, Finset.prod_update_of_mem (Finset.mem_univ j)]
    have hT : T j ⊆ (S.comap ((LinearMap.mulRight O (∏ i ∈ Finset.univ \ {j}, ε i (F i))).comp (ε j)) :
        Set (B j)) := by
      intro x hx
      show (LinearMap.mulRight O (∏ i ∈ Finset.univ \ {j}, ε i (F i))) (ε j x) ∈ S
      rw [LinearMap.mulRight_apply, ← key x]
      apply ih (Function.update F j x)
      · intro i hi
        have hij : i ≠ j := fun h => hj (h ▸ hi)
        rw [Function.update_of_ne hij]
        exact h1 i (Finset.mem_insert_of_mem hi)
      · intro i hi
        by_cases hij : i = j
        · subst hij
          rw [Function.update_self]
          exact hx
        · rw [Function.update_of_ne hij]
          exact h2 i (by simp [hij, hi])
    have hmem := Submodule.span_le.mpr hT (h1 j (Finset.mem_insert_self j s))
    have k := key (F j)
    rw [Function.update_eq_self] at k
    rw [k]
    exact hmem

theorem goal1 :
    ∀ {O A I : Type} [inst : CommRing O] [inst_1 : CommRing A] [inst_2 : Algebra O A]
      [inst_3 : Fintype I] [DecidableEq I] {B : I → Type} [inst_5 : (i : I) → AddCommGroup (B i)]
      [inst_6 : (i : I) → _root_.Module O (B i)] (ε : (i : I) → B i →ₗ[O] A) (T : (i : I) → Set (B i)),
      Submodule.span O
          {X : A |
            ∃ (F : (i : I) → B i),
              (∀ (i : I), F i ∈ Submodule.span O (T i)) ∧ X = ∏ i : I, (ε i) (F i)} =
        Submodule.span O
          {X : A | ∃ (F : (i : I) → B i), (∀ (i : I), F i ∈ T i) ∧ X = ∏ i : I, (ε i) (F i)} := by
  intro O A I _ _ _ _ _ B _ _ ε T
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro X ⟨F, hF, rfl⟩
    exact aux ε T _ (fun G hG => Submodule.subset_span
      (show ∃ H : (i : I) → B i, (∀ i, H i ∈ T i) ∧ ∏ i, ε i (G i) = ∏ i, ε i (H i) from
        ⟨G, hG, rfl⟩)) Finset.univ F
      (fun i _ => hF i) (fun i hi => absurd (Finset.mem_univ i) hi)
  · apply Submodule.span_mono
    rintro X ⟨F, hF, rfl⟩
    exact (show ∃ G : (i : I) → B i, (∀ i, G i ∈ Submodule.span O (T i)) ∧ _ from
      ⟨F, fun i => Submodule.subset_span (hF i), rfl⟩)

end Bl.general_b_fact_left'''''
