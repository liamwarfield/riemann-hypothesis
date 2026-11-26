module

public import Formalism.SharpRestriction.GrowthBounds.GLWeightTheory
public import Formalism.SharpRestriction.GrowthBounds.TruncatedChains.ProjectorFactorMemWeightSpace
public import Formalism.SharpRestriction.GrowthBounds.TruncatedChains.YbatStep

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.TruncatedChains.CnNODrop
section -- merged from Formalism.SharpRestriction.GrowthBounds.TruncatedChains.IdxOfAppendSecond
section -- merged from Formalism.SharpRestriction.GrowthBounds.TruncatedChains.CnNOOfNormal
section -- merged from Formalism.SharpRestriction.GrowthBounds.TruncatedChains.CnStepsTail
namespace Formalism.MainNotions.G.ExtremalProjector

open Formalism.MainNotions.G

section Pos

variable {α : Type*} [BEq α] [LawfulBEq α]

theorem cn_notMem {l1 l2 : List α} (h : (l1 ++ l2).Nodup) {x : α} (hx : x ∈ l2) : x ∉ l1 := by
  intro hx1
  first
  | exact List.disjoint_of_nodup_append h hx1 hx
  | exact (List.nodup_append.1 h).2.2 hx1 hx
  | exact (List.nodup_append.1 h).2.2 x hx1 x hx rfl
  | simp_all [List.nodup_append]

private theorem idxOf_cons_self_eq_zero (a : α) (l : List α) : (a :: l).idxOf a = 0 := by
  first
  | simp [List.idxOf_cons]
  | exact List.idxOf_cons_self l
  | simp [List.idxOf, List.findIdx_cons]

private theorem idxOf_cons_of_ne (a u : α) (h : a ≠ u) (l : List α) : (a :: l).idxOf u = l.idxOf u + 1 := by
  first
  | simp [List.idxOf_cons, h]
  | exact List.idxOf_cons_ne l h
  | simp [List.idxOf, List.findIdx_cons, h]

private theorem idxOf_append_of_not_mem_left (l1 : List α) (u : α) (hu : u ∉ l1) (l : List α) :
    (l1 ++ l).idxOf u = l1.length + l.idxOf u := by
  induction l1 with
  | nil => simp
  | cons a t ih =>
    have hau : a ≠ u := by
      rintro rfl
      simp at hu
    have ht : u ∉ t := fun h' => hu (List.mem_cons_of_mem _ h')
    rw [List.cons_append, idxOf_cons_of_ne a u hau, ih ht, List.length_cons]
    omega

private theorem idxOf_append_of_mem_left_and_lt_length (l1 : List α) (u : α) (hu : u ∈ l1) (l : List α) :
    (l1 ++ l).idxOf u = l1.idxOf u ∧ l1.idxOf u < l1.length := by
  induction l1 with
  | nil => simp at hu
  | cons a t ih =>
    by_cases hau : a = u
    · rw [hau, List.cons_append, idxOf_cons_self_eq_zero, idxOf_cons_self_eq_zero]
      simp
    · have ht : u ∈ t := by simpa [Ne.symm hau] using hu
      obtain ⟨h1, h2⟩ := ih ht
      rw [List.cons_append, idxOf_cons_of_ne a u hau, idxOf_cons_of_ne a u hau, h1, List.length_cons]
      exact ⟨rfl, by omega⟩

theorem cn_pos_swap (l1 l2 : List α) (x y : α) (hxy : x ≠ y) (hx : x ∉ l1) (hy : y ∉ l1) (u : α) :
    (u = x ∧ (l1 ++ x :: y :: l2).idxOf u = l1.length ∧ (l1 ++ y :: x :: l2).idxOf u = l1.length + 1) ∨
    (u = y ∧ (l1 ++ x :: y :: l2).idxOf u = l1.length + 1 ∧ (l1 ++ y :: x :: l2).idxOf u = l1.length) ∨
    (u ≠ x ∧ u ≠ y ∧ (l1 ++ y :: x :: l2).idxOf u = (l1 ++ x :: y :: l2).idxOf u ∧
      ((l1 ++ x :: y :: l2).idxOf u < l1.length ∨ l1.length + 2 ≤ (l1 ++ x :: y :: l2).idxOf u)) := by
  by_cases hux : u = x
  · refine Or.inl ⟨hux, ?_, ?_⟩ <;> rw [hux] <;>
      simp only [idxOf_append_of_not_mem_left l1 x hx, idxOf_cons_self_eq_zero, idxOf_cons_of_ne y x (Ne.symm hxy)] <;> omega
  · by_cases huy : u = y
    · refine Or.inr (Or.inl ⟨huy, ?_, ?_⟩) <;> rw [huy] <;>
        simp only [idxOf_append_of_not_mem_left l1 y hy, idxOf_cons_self_eq_zero, idxOf_cons_of_ne x y hxy] <;> omega
    · refine Or.inr (Or.inr ⟨hux, huy, ?_⟩)
      by_cases hu1 : u ∈ l1
      · obtain ⟨e1, e2⟩ := idxOf_append_of_mem_left_and_lt_length l1 u hu1 (x :: y :: l2)
        obtain ⟨e3, _⟩ := idxOf_append_of_mem_left_and_lt_length l1 u hu1 (y :: x :: l2)
        exact ⟨by rw [e1, e3], Or.inl (by rw [e1]; exact e2)⟩
      · refine ⟨?_, Or.inr ?_⟩ <;>
          simp only [idxOf_append_of_not_mem_left l1 u hu1, idxOf_cons_of_ne x u (Ne.symm hux), idxOf_cons_of_ne y u (Ne.symm huy)] <;> omega

theorem cn_pos_braid (l1 l2 : List α) (x y z : α) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : x ∉ l1) (hy : y ∉ l1) (hz : z ∉ l1) (u : α) :
    (u = x ∧ (l1 ++ x :: y :: z :: l2).idxOf u = l1.length ∧ (l1 ++ z :: y :: x :: l2).idxOf u = l1.length + 2) ∨
    (u = y ∧ (l1 ++ x :: y :: z :: l2).idxOf u = l1.length + 1 ∧
      (l1 ++ z :: y :: x :: l2).idxOf u = l1.length + 1) ∨
    (u = z ∧ (l1 ++ x :: y :: z :: l2).idxOf u = l1.length + 2 ∧ (l1 ++ z :: y :: x :: l2).idxOf u = l1.length) ∨
    (u ≠ x ∧ u ≠ y ∧ u ≠ z ∧ (l1 ++ z :: y :: x :: l2).idxOf u = (l1 ++ x :: y :: z :: l2).idxOf u ∧
      ((l1 ++ x :: y :: z :: l2).idxOf u < l1.length ∨ l1.length + 3 ≤ (l1 ++ x :: y :: z :: l2).idxOf u)) := by
  by_cases hux : u = x
  · refine Or.inl ⟨hux, ?_, ?_⟩ <;> rw [hux] <;>
      simp only [idxOf_append_of_not_mem_left l1 x hx, idxOf_cons_self_eq_zero, idxOf_cons_of_ne y x (Ne.symm hxy), idxOf_cons_of_ne z x (Ne.symm hxz)] <;> omega
  · by_cases huy : u = y
    · refine Or.inr (Or.inl ⟨huy, ?_, ?_⟩) <;> rw [huy] <;>
        simp only [idxOf_append_of_not_mem_left l1 y hy, idxOf_cons_self_eq_zero, idxOf_cons_of_ne x y hxy, idxOf_cons_of_ne z y (Ne.symm hyz)] <;> omega
    · by_cases huz : u = z
      · refine Or.inr (Or.inr (Or.inl ⟨huz, ?_, ?_⟩)) <;> rw [huz] <;>
          simp only [idxOf_append_of_not_mem_left l1 z hz, idxOf_cons_self_eq_zero, idxOf_cons_of_ne x z hxz, idxOf_cons_of_ne y z hyz] <;> omega
      · refine Or.inr (Or.inr (Or.inr ⟨hux, huy, huz, ?_⟩))
        by_cases hu1 : u ∈ l1
        · obtain ⟨e1, e2⟩ := idxOf_append_of_mem_left_and_lt_length l1 u hu1 (x :: y :: z :: l2)
          obtain ⟨e3, _⟩ := idxOf_append_of_mem_left_and_lt_length l1 u hu1 (z :: y :: x :: l2)
          exact ⟨by rw [e1, e3], Or.inl (by rw [e1]; exact e2)⟩
        · refine ⟨?_, Or.inr ?_⟩ <;>
            simp only [idxOf_append_of_not_mem_left l1 u hu1, idxOf_cons_of_ne x u (Ne.symm hux), idxOf_cons_of_ne y u (Ne.symm huy),
              idxOf_cons_of_ne z u (Ne.symm huz)] <;> omega

theorem cn_idx_rev {l : List α} (hnd : l.Nodup) {x : α} (hx : x ∈ l) :
    l.reverse.idxOf x + l.idxOf x + 1 = l.length := by
  induction l with
  | nil => simp at hx
  | cons a t ih =>
    rw [List.nodup_cons] at hnd
    obtain ⟨hat, hnd'⟩ := hnd
    rw [List.reverse_cons, List.length_cons]
    by_cases hax : a = x
    · have hat' : x ∉ t := hax ▸ hat
      have hr : x ∉ t.reverse := by simpa using hat'
      rw [hax]
      simp only [idxOf_append_of_not_mem_left t.reverse x hr, idxOf_cons_self_eq_zero, List.length_reverse]
      all_goals omega
    · have hxt : x ∈ t := by simpa [Ne.symm hax] using hx
      have hxr : x ∈ t.reverse := by simpa using hxt
      obtain ⟨e1, _⟩ := idxOf_append_of_mem_left_and_lt_length t.reverse x hxr [a]
      rw [e1, idxOf_cons_of_ne a x hax]
      have := ih hnd' hxt
      omega

theorem cn_decomp (F : α → Prop) (l : List α) :
    (∃ lF lG, l = lF ++ lG ∧ (∀ r ∈ lF, F r) ∧ (∀ r ∈ lG, ¬ F r)) ∨
    (∃ l1 g f lF lG, l = l1 ++ g :: f :: (lF ++ lG) ∧ ¬ F g ∧ F f ∧ (∀ r ∈ lF, F r) ∧ (∀ r ∈ lG, ¬ F r)) := by
  induction l with
  | nil => exact Or.inl ⟨[], [], by simp, by simp, by simp⟩
  | cons a t ih =>
    rcases ih with ⟨lF, lG, rfl, hF, hG⟩ | ⟨l1, g, f, lF, lG, rfl, hg, hf, hF, hG⟩
    · by_cases ha : F a
      · refine Or.inl ⟨a :: lF, lG, by simp, ?_, hG⟩
        intro r hr
        rcases List.mem_cons.1 hr with h | h
        · exact h ▸ ha
        · exact hF r h
      · cases lF with
        | nil =>
          refine Or.inl ⟨[], a :: lG, by simp, by simp, ?_⟩
          intro r hr
          rcases List.mem_cons.1 hr with h | h
          · exact h ▸ ha
          · exact hG r h
        | cons f lF' =>
          exact Or.inr ⟨[], a, f, lF', lG, by simp, ha, hF f (List.mem_cons_self ..),
            fun r hr => hF r (List.mem_cons_of_mem _ hr), hG⟩
    · exact Or.inr ⟨a :: l1, g, f, lF, lG, by simp, hg, hf, hF, hG⟩

end Pos

variable {n : ℕ}

abbrev Steps (n : ℕ) := Relation.ReflTransGen (Step n)

theorem cn_step_tail {l l' : List (Fin n × Fin n)} (h : Step n l l') (R : List (Fin n × Fin n)) :
    Step n (l ++ R) (l' ++ R) := by
  cases h <;>
    (simp only [List.append_assoc, List.cons_append]
     constructor <;> assumption)

theorem cn_steps_tail {l l' : List (Fin n × Fin n)} (h : Steps n l l') (R : List (Fin n × Fin n)) :
    Steps n (l ++ R) (l' ++ R) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact ih.tail (cn_step_tail hs R)

theorem cn_step_rev {l l' : List (Fin n × Fin n)} (h : Step n l l') : Step n l.reverse l'.reverse := by
  cases h with
  | swap l1 l2 a b c d h1 h2 h3 h4 =>
    simpa using Step.swap l2.reverse l1.reverse c d a b h1.symm h3.symm h2.symm h4.symm
  | braid l1 l2 a b c h1 h2 => simpa using Step.braid' l2.reverse l1.reverse a b c h1 h2
  | braid' l1 l2 a b c h1 h2 => simpa using Step.braid l2.reverse l1.reverse a b c h1 h2

theorem cn_steps_rev {l l' : List (Fin n × Fin n)} (h : Steps n l l') : Steps n l.reverse l'.reverse := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact ih.tail (cn_step_rev hs)

end Formalism.MainNotions.G.ExtremalProjector
end

namespace Formalism.MainNotions.G.ExtremalProjector

open Formalism.MainNotions.G

variable {n : ℕ}

def NO (n j : ℕ) (l : List (Fin n × Fin n)) : Prop :=
  l.Nodup ∧ (∀ ab ∈ l, j ≤ ab.1.val ∧ ab.1.val < ab.2.val) ∧
    (∀ a b : Fin n, j ≤ a.val → a.val < b.val → (a, b) ∈ l) ∧
    ∀ a b c : Fin n, j ≤ a.val → a.val < b.val → b.val < c.val →
      (l.idxOf (a, b) < l.idxOf (a, c) ∧ l.idxOf (a, c) < l.idxOf (b, c)) ∨
      (l.idxOf (b, c) < l.idxOf (a, c) ∧ l.idxOf (a, c) < l.idxOf (a, b))

theorem cn_NO_of_normal {ord : List (Fin n × Fin n)} (h : NormalOrder n ord) : NO n 0 ord := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  unfold NO
  exact ⟨h1, fun ab hab => ⟨Nat.zero_le _, h2 ab hab⟩, fun a b _ hab => h3 a b hab,
    fun a b c _ hab hbc => h4 a b c hab hbc⟩

theorem cn_ne {x1 x2 y1 y2 : Fin n} (h : ¬ (x1.val = y1.val ∧ x2.val = y2.val)) : (x1, x2) ≠ (y1, y2) := by
  intro heq
  rw [Prod.mk.injEq] at heq
  exact h ⟨congrArg Fin.val heq.1, congrArg Fin.val heq.2⟩

theorem cn_posR_swap (l1 l2 : List (Fin n × Fin n)) (x1 x2 y1 y2 : Fin n) (hxy : (x1, x2) ≠ (y1, y2))
    (hx : (x1, x2) ∉ l1) (hy : (y1, y2) ∉ l1) (u1 u2 : Fin n) :
    (u1.val = x1.val ∧ u2.val = x2.val ∧ (l1 ++ (x1, x2) :: (y1, y2) :: l2).idxOf (u1, u2) = l1.length ∧
      (l1 ++ (y1, y2) :: (x1, x2) :: l2).idxOf (u1, u2) = l1.length + 1) ∨
    (u1.val = y1.val ∧ u2.val = y2.val ∧ (l1 ++ (x1, x2) :: (y1, y2) :: l2).idxOf (u1, u2) = l1.length + 1 ∧
      (l1 ++ (y1, y2) :: (x1, x2) :: l2).idxOf (u1, u2) = l1.length) ∨
    (¬ (u1.val = x1.val ∧ u2.val = x2.val) ∧ ¬ (u1.val = y1.val ∧ u2.val = y2.val) ∧
      (l1 ++ (y1, y2) :: (x1, x2) :: l2).idxOf (u1, u2) = (l1 ++ (x1, x2) :: (y1, y2) :: l2).idxOf (u1, u2) ∧
      ((l1 ++ (x1, x2) :: (y1, y2) :: l2).idxOf (u1, u2) < l1.length ∨
        l1.length + 2 ≤ (l1 ++ (x1, x2) :: (y1, y2) :: l2).idxOf (u1, u2))) := by
  have hu : ∀ v1 v2 : Fin n, u1.val = v1.val ∧ u2.val = v2.val → (u1, u2) = (v1, v2) :=
    fun v1 v2 hh => Prod.ext (Fin.ext hh.1) (Fin.ext hh.2)
  rcases cn_pos_swap l1 l2 (x1, x2) (y1, y2) hxy hx hy (u1, u2) with
    ⟨e, h2, h3⟩ | ⟨e, h2, h3⟩ | ⟨e1, e2, h3, h4⟩
  · rw [Prod.mk.injEq] at e
    exact Or.inl ⟨congrArg Fin.val e.1, congrArg Fin.val e.2, h2, h3⟩
  · rw [Prod.mk.injEq] at e
    exact Or.inr (Or.inl ⟨congrArg Fin.val e.1, congrArg Fin.val e.2, h2, h3⟩)
  · exact Or.inr (Or.inr ⟨fun hh => e1 (hu _ _ hh), fun hh => e2 (hu _ _ hh), h3, h4⟩)

theorem cn_posR_braid (l1 l2 : List (Fin n × Fin n)) (x1 x2 y1 y2 z1 z2 : Fin n) (hxy : (x1, x2) ≠ (y1, y2))
    (hxz : (x1, x2) ≠ (z1, z2)) (hyz : (y1, y2) ≠ (z1, z2))
    (hx : (x1, x2) ∉ l1) (hy : (y1, y2) ∉ l1) (hz : (z1, z2) ∉ l1) (u1 u2 : Fin n) :
    (u1.val = x1.val ∧ u2.val = x2.val ∧
      (l1 ++ (x1, x2) :: (y1, y2) :: (z1, z2) :: l2).idxOf (u1, u2) = l1.length ∧
      (l1 ++ (z1, z2) :: (y1, y2) :: (x1, x2) :: l2).idxOf (u1, u2) = l1.length + 2) ∨
    (u1.val = y1.val ∧ u2.val = y2.val ∧
      (l1 ++ (x1, x2) :: (y1, y2) :: (z1, z2) :: l2).idxOf (u1, u2) = l1.length + 1 ∧
      (l1 ++ (z1, z2) :: (y1, y2) :: (x1, x2) :: l2).idxOf (u1, u2) = l1.length + 1) ∨
    (u1.val = z1.val ∧ u2.val = z2.val ∧
      (l1 ++ (x1, x2) :: (y1, y2) :: (z1, z2) :: l2).idxOf (u1, u2) = l1.length + 2 ∧
      (l1 ++ (z1, z2) :: (y1, y2) :: (x1, x2) :: l2).idxOf (u1, u2) = l1.length) ∨
    (¬ (u1.val = x1.val ∧ u2.val = x2.val) ∧ ¬ (u1.val = y1.val ∧ u2.val = y2.val) ∧
      ¬ (u1.val = z1.val ∧ u2.val = z2.val) ∧
      (l1 ++ (z1, z2) :: (y1, y2) :: (x1, x2) :: l2).idxOf (u1, u2) =
        (l1 ++ (x1, x2) :: (y1, y2) :: (z1, z2) :: l2).idxOf (u1, u2) ∧
      ((l1 ++ (x1, x2) :: (y1, y2) :: (z1, z2) :: l2).idxOf (u1, u2) < l1.length ∨
        l1.length + 3 ≤ (l1 ++ (x1, x2) :: (y1, y2) :: (z1, z2) :: l2).idxOf (u1, u2))) := by
  have hu : ∀ v1 v2 : Fin n, u1.val = v1.val ∧ u2.val = v2.val → (u1, u2) = (v1, v2) :=
    fun v1 v2 hh => Prod.ext (Fin.ext hh.1) (Fin.ext hh.2)
  rcases cn_pos_braid l1 l2 (x1, x2) (y1, y2) (z1, z2) hxy hxz hyz hx hy hz (u1, u2) with
    ⟨e, h2, h3⟩ | ⟨e, h2, h3⟩ | ⟨e, h2, h3⟩ | ⟨e1, e2, e3, h3, h4⟩
  · rw [Prod.mk.injEq] at e
    exact Or.inl ⟨congrArg Fin.val e.1, congrArg Fin.val e.2, h2, h3⟩
  · rw [Prod.mk.injEq] at e
    exact Or.inr (Or.inl ⟨congrArg Fin.val e.1, congrArg Fin.val e.2, h2, h3⟩)
  · rw [Prod.mk.injEq] at e
    exact Or.inr (Or.inr (Or.inl ⟨congrArg Fin.val e.1, congrArg Fin.val e.2, h2, h3⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨fun hh => e1 (hu _ _ hh), fun hh => e2 (hu _ _ hh),
      fun hh => e3 (hu _ _ hh), h3, h4⟩))

set_option maxHeartbeats 1600000 in
theorem cn_ar_swap {p P Q R P' Q' R' x y z a b c d : ℕ} (hxy : x < y) (hyz : y < z) (h1 : a ≠ c) (h2 : a ≠ d)
    (h3 : b ≠ c) (h4 : b ≠ d) (o : (P < Q ∧ Q < R) ∨ (R < Q ∧ Q < P))
    (p1 : (x = a ∧ y = b ∧ P = p ∧ P' = p + 1) ∨ (x = c ∧ y = d ∧ P = p + 1 ∧ P' = p) ∨
      (¬ (x = a ∧ y = b) ∧ ¬ (x = c ∧ y = d) ∧ P' = P ∧ (P < p ∨ p + 2 ≤ P)))
    (p2 : (x = a ∧ z = b ∧ Q = p ∧ Q' = p + 1) ∨ (x = c ∧ z = d ∧ Q = p + 1 ∧ Q' = p) ∨
      (¬ (x = a ∧ z = b) ∧ ¬ (x = c ∧ z = d) ∧ Q' = Q ∧ (Q < p ∨ p + 2 ≤ Q)))
    (p3 : (y = a ∧ z = b ∧ R = p ∧ R' = p + 1) ∨ (y = c ∧ z = d ∧ R = p + 1 ∧ R' = p) ∨
      (¬ (y = a ∧ z = b) ∧ ¬ (y = c ∧ z = d) ∧ R' = R ∧ (R < p ∨ p + 2 ≤ R))) :
    (P' < Q' ∧ Q' < R') ∨ (R' < Q' ∧ Q' < P') := by
  rcases p1 with h1' | h1' | h1' <;> rcases p2 with h2' | h2' | h2' <;>
    rcases p3 with h3' | h3' | h3' <;> rcases o with o | o <;> omega

set_option maxHeartbeats 3200000 in
theorem cn_ar_braid' {p P Q R P' Q' R' x y z a b c : ℕ} (hxy : x < y) (hyz : y < z) (hab : a < b) (hbc : b < c)
    (o : (P < Q ∧ Q < R) ∨ (R < Q ∧ Q < P))
    (p1 : (x = b ∧ y = c ∧ P = p ∧ P' = p + 2) ∨ (x = a ∧ y = c ∧ P = p + 1 ∧ P' = p + 1) ∨
      (x = a ∧ y = b ∧ P = p + 2 ∧ P' = p) ∨
      (¬ (x = b ∧ y = c) ∧ ¬ (x = a ∧ y = c) ∧ ¬ (x = a ∧ y = b) ∧ P' = P ∧ (P < p ∨ p + 3 ≤ P)))
    (p2 : (x = b ∧ z = c ∧ Q = p ∧ Q' = p + 2) ∨ (x = a ∧ z = c ∧ Q = p + 1 ∧ Q' = p + 1) ∨
      (x = a ∧ z = b ∧ Q = p + 2 ∧ Q' = p) ∨
      (¬ (x = b ∧ z = c) ∧ ¬ (x = a ∧ z = c) ∧ ¬ (x = a ∧ z = b) ∧ Q' = Q ∧ (Q < p ∨ p + 3 ≤ Q)))
    (p3 : (y = b ∧ z = c ∧ R = p ∧ R' = p + 2) ∨ (y = a ∧ z = c ∧ R = p + 1 ∧ R' = p + 1) ∨
      (y = a ∧ z = b ∧ R = p + 2 ∧ R' = p) ∨
      (¬ (y = b ∧ z = c) ∧ ¬ (y = a ∧ z = c) ∧ ¬ (y = a ∧ z = b) ∧ R' = R ∧ (R < p ∨ p + 3 ≤ R))) :
    (P' < Q' ∧ Q' < R') ∨ (R' < Q' ∧ Q' < P') := by
  rcases p1 with h1' | h1' | h1' | h1' <;> rcases p2 with h2' | h2' | h2' | h2' <;>
    rcases p3 with h3' | h3' | h3' | h3' <;> rcases o with o | o <;> omega

theorem cn_NO_swap {j : ℕ} (l1 l2 : List (Fin n × Fin n)) (a b c d : Fin n) (h1 : a ≠ c) (h2 : a ≠ d)
    (h3 : b ≠ c) (h4 : b ≠ d) (h : NO n j (l1 ++ (a, b) :: (c, d) :: l2)) :
    NO n j (l1 ++ (c, d) :: (a, b) :: l2) := by
  unfold NO at h ⊢
  obtain ⟨hnd, hb, hc, ht⟩ := h
  have hperm : (l1 ++ (c, d) :: (a, b) :: l2).Perm (l1 ++ (a, b) :: (c, d) :: l2) :=
    (List.Perm.swap (a, b) (c, d) l2).append_left l1
  have hne : (a, b) ≠ (c, d) := fun e => h1 (congrArg Prod.fst e)
  have hx : (a, b) ∉ l1 := cn_notMem hnd (by simp)
  have hy : (c, d) ∉ l1 := cn_notMem hnd (by simp)
  have v1 : a.val ≠ c.val := fun e => h1 (Fin.ext e)
  have v2 : a.val ≠ d.val := fun e => h2 (Fin.ext e)
  have v3 : b.val ≠ c.val := fun e => h3 (Fin.ext e)
  have v4 : b.val ≠ d.val := fun e => h4 (Fin.ext e)
  refine ⟨hperm.nodup_iff.2 hnd, fun ab hab => hb ab (hperm.mem_iff.1 hab),
    fun x y hj hxy => hperm.mem_iff.2 (hc x y hj hxy), ?_⟩
  intro x y z hj hxy hyz
  exact cn_ar_swap hxy hyz v1 v2 v3 v4 (ht x y z hj hxy hyz)
    (cn_posR_swap l1 l2 a b c d hne hx hy x y) (cn_posR_swap l1 l2 a b c d hne hx hy x z)
    (cn_posR_swap l1 l2 a b c d hne hx hy y z)

theorem cn_NO_braid' {j : ℕ} (l1 l2 : List (Fin n × Fin n)) (a b c : Fin n) (hab : a < b) (hbc : b < c)
    (h : NO n j (l1 ++ (b, c) :: (a, c) :: (a, b) :: l2)) :
    NO n j (l1 ++ (a, b) :: (a, c) :: (b, c) :: l2) := by
  unfold NO at h ⊢
  obtain ⟨hnd, hb, hc, ht⟩ := h
  have hperm : (l1 ++ (a, b) :: (a, c) :: (b, c) :: l2).Perm (l1 ++ (b, c) :: (a, c) :: (a, b) :: l2) :=
    ((((List.Perm.swap (a, c) (a, b) ((b, c) :: l2)).trans
      ((List.Perm.swap (b, c) (a, b) l2).cons (a, c))).trans
      (List.Perm.swap (b, c) (a, c) ((a, b) :: l2)))).append_left l1
  have hab' : a.val < b.val := hab
  have hbc' : b.val < c.val := hbc
  have hxy : ((b, c) : Fin n × Fin n) ≠ (a, c) := fun e => by
    have := congrArg (fun p : Fin n × Fin n => p.1.val) e; simp at this; omega
  have hxz : ((b, c) : Fin n × Fin n) ≠ (a, b) := fun e => by
    have := congrArg (fun p : Fin n × Fin n => p.1.val) e; simp at this; omega
  have hyz : ((a, c) : Fin n × Fin n) ≠ (a, b) := fun e => by
    have := congrArg (fun p : Fin n × Fin n => p.2.val) e; simp at this; omega
  have hx : (b, c) ∉ l1 := cn_notMem hnd (by simp)
  have hy : (a, c) ∉ l1 := cn_notMem hnd (by simp)
  have hz : (a, b) ∉ l1 := cn_notMem hnd (by simp)
  refine ⟨hperm.nodup_iff.2 hnd, fun ab hab => hb ab (hperm.mem_iff.1 hab),
    fun x y hj hxy => hperm.mem_iff.2 (hc x y hj hxy), ?_⟩
  intro x y z hj hxy' hyz'
  exact cn_ar_braid' hxy' hyz' hab' hbc' (ht x y z hj hxy' hyz')
    (cn_posR_braid l1 l2 b c a c a b hxy hxz hyz hx hy hz x y)
    (cn_posR_braid l1 l2 b c a c a b hxy hxz hyz hx hy hz x z)
    (cn_posR_braid l1 l2 b c a c a b hxy hxz hyz hx hy hz y z)

theorem cn_NO_rev {j : ℕ} {l : List (Fin n × Fin n)} (h : NO n j l) : NO n j l.reverse := by
  unfold NO at h ⊢
  obtain ⟨hnd, hb, hc, ht⟩ := h
  refine ⟨List.nodup_reverse.2 hnd, fun ab hab => hb ab (List.mem_reverse.1 hab),
    fun x y hj hxy => List.mem_reverse.2 (hc x y hj hxy), ?_⟩
  intro x y z hj hxy hyz
  have e1 := cn_idx_rev hnd (hc x y hj hxy)
  have e2 := cn_idx_rev hnd (hc x z hj (hxy.trans hyz))
  have e3 := cn_idx_rev hnd (hc y z (hj.trans hxy.le) hyz)
  have o := ht x y z hj hxy hyz
  omega

end Formalism.MainNotions.G.ExtremalProjector
end

namespace Formalism.MainNotions.G.ExtremalProjector

open Formalism.MainNotions.G

section Pos

variable {α : Type*} [BEq α] [LawfulBEq α]

private theorem idxOf_append_eq_length_add_of_not_mem (l1 l : List α) (x : α) (hx : x ∉ l1) :
    (l1 ++ l).idxOf x = l1.length + l.idxOf x := by
  induction l1 with
  | nil => simp
  | cons a t ih =>
    have hax : a ≠ x := by
      rintro rfl
      exact hx (by simp)
    have ht : x ∉ t := fun h => hx (by simp [h])
    simp [List.idxOf_cons, hax, ih ht] <;> omega

theorem idxOf_append_first (l1 l2 : List α) (x : α) (hx : x ∉ l1) : (l1 ++ x :: l2).idxOf x = l1.length := by
  rw [idxOf_append_eq_length_add_of_not_mem l1 _ x hx]
  simp

theorem idxOf_append_second (l1 l2 : List α) (x y : α) (hxy : x ≠ y) (hy : y ∉ l1) :
    (l1 ++ x :: y :: l2).idxOf y = l1.length + 1 := by
  rw [idxOf_append_eq_length_add_of_not_mem l1 _ y hy]
  simp [List.idxOf_cons, hxy]

theorem idxOf_append_third (l1 l2 : List α) (x y z : α) (hxz : x ≠ z) (hyz : y ≠ z) (hz : z ∉ l1) :
    (l1 ++ x :: y :: z :: l2).idxOf z = l1.length + 2 := by
  rw [idxOf_append_eq_length_add_of_not_mem l1 _ z hz]
  simp [List.idxOf_cons, hxz, hyz]

theorem cn_idx_lt (l1 l2 : List α) (u : α) (hu : u ∈ l1) : (l1 ++ l2).idxOf u < l1.length := by
  induction l1 with
  | nil => simp at hu
  | cons a t ih =>
    by_cases h : a = u
    · subst h
      simp
    · have hu' : u ∈ t := by
        rcases List.mem_cons.mp hu with h' | h'
        · exact absurd h'.symm h
        · exact h'
      have := ih hu'
      simp [List.idxOf_cons, h]
      omega

end Pos

variable {n : ℕ}

private theorem eq_of_idxOf_eq_of_mem {β : Type*} [BEq β] [LawfulBEq β] (l : List β) (u v : β) (hu : u ∈ l)
    (hv : v ∈ l) (h : l.idxOf u = l.idxOf v) : u = v := by
  induction l with
  | nil => simp at hu
  | cons a t ih =>
    by_cases hau : a = u
    · by_cases hav : a = v
      · exact hau.symm.trans hav
      · subst hau
        simp [List.idxOf_cons, hav] at h
    · by_cases hav : a = v
      · subst hav
        simp [List.idxOf_cons, hau] at h
      · simp [List.idxOf_cons, hau, hav] at h
        have hu' : u ∈ t := (List.mem_cons.mp hu).resolve_left (fun h' => hau h'.symm)
        have hv' : v ∈ t := (List.mem_cons.mp hv).resolve_left (fun h' => hav h'.symm)
        exact ih hu' hv' h

theorem cn_key {j : ℕ} (l1 l2 : List (Fin n × Fin n)) (b c j' e : Fin n)
    (h : NO n j (l1 ++ (b, c) :: (j', c) :: (j', e) :: l2)) (hj : j'.val = j) (hjb : j < b.val)
    (hbc : b.val < c.val) : e = b := by
  unfold NO at h
  obtain ⟨hnd, hall, hcomp, hord⟩ := h
  set L := l1 ++ (b, c) :: (j', c) :: (j', e) :: l2 with hL
  have hjb' : j'.val < b.val := by omega
  have hjj : j ≤ j'.val := by omega
  have hnb : j' ≠ b := fun h' => by rw [h'] at hjb'; exact lt_irrefl _ hjb'
  have hmem : ∀ u, u ∈ l1 → u ∉ (b, c) :: (j', c) :: (j', e) :: l2 := fun u hu hu' =>
    List.disjoint_of_nodup_append hnd hu hu'
  have n0 : (b, c) ∉ l1 := fun hu => hmem _ hu (by simp)
  have n1 : (j', c) ∉ l1 := fun hu => hmem _ hu (by simp)
  have n2 : (j', e) ∉ l1 := fun hu => hmem _ hu (by simp)
  have ht := List.Nodup.of_append_right hnd
  have hce : (j', c) ≠ (j', e) := by
    intro heq
    exact (List.nodup_cons.mp (List.nodup_cons.mp ht).2).1 (by simp [heq])
  have hec : e ≠ c := fun h' => hce (by rw [h'])
  have hbj : (b, c) ≠ (j', c) := fun h' => hnb (congrArg Prod.fst h').symm
  have hbje : (b, c) ≠ (j', e) := fun h' => hnb (congrArg Prod.fst h').symm
  have i0 : L.idxOf (b, c) = l1.length := idxOf_append_first l1 _ (b, c) n0
  have i1 : L.idxOf (j', c) = l1.length + 1 := idxOf_append_second l1 ((j', e) :: l2) (b, c) (j', c) hbj n1
  have i2 : L.idxOf (j', e) = l1.length + 2 := idxOf_append_third l1 l2 (b, c) (j', c) (j', e) hbje hce n2
  have inj : ∀ u v, u ∈ L → v ∈ L → L.idxOf u = L.idxOf v → u = v := by
    intro u v hu hv h'
    exact eq_of_idxOf_eq_of_mem L u v hu hv h'
  have hje : j'.val < e.val := (hall (j', e) (by simp [hL])).2
  have o1 := hord j' b c hjj hjb' hbc
  rw [i1, i0] at o1
  by_contra hne
  rcases lt_trichotomy e.val b.val with heb | heb | heb
  · have hec' : e.val < c.val := by omega
    have o2 := hord j' e c hjj hje hec'
    rw [i2, i1] at o2
    have hs : L.idxOf (e, c) ≠ l1.length := by
      rw [← i0]
      intro h'
      exact hne (congrArg Prod.fst (inj _ _ (hcomp e c (by omega) hec') (by simp [hL]) h'))
    have o3 := hord e b c (by omega) heb hbc
    rw [i0] at o3
    have o4 := hord j' e b hjj hje heb
    rw [i2] at o4
    omega
  · exact hne (Fin.ext heb)
  · have hr1 : L.idxOf (b, e) ≠ l1.length := by
      rw [← i0]
      intro h'
      exact hec (congrArg Prod.snd (inj _ _ (hcomp b e (by omega) heb) (by simp [hL]) h'))
    have hr2 : L.idxOf (b, e) ≠ l1.length + 1 := by
      rw [← i1]
      intro h'
      exact hnb (congrArg Prod.fst (inj _ _ (hcomp b e (by omega) heb) (by simp [hL]) h')).symm
    have o2 := hord j' b e hjj hjb' heb
    rw [i2] at o2
    rcases lt_or_gt_of_ne (fun h' : e.val = c.val => hec (Fin.ext h')) with hce' | hce'
    · have o3 := hord j' e c hjj hje hce'
      rw [i2, i1] at o3
      have hs : L.idxOf (e, c) ≠ l1.length := by
        rw [← i0]
        intro h'
        exact hne (congrArg Prod.fst (inj _ _ (hcomp e c (by omega) hce') (by simp [hL]) h'))
      have o4 := hord b e c (by omega) heb hce'
      rw [i0] at o4
      omega
    · have o3 := hord j' c e hjj (by omega) hce'
      rw [i1, i2] at o3
      have o4 := hord b c e (by omega) hbc hce'
      rw [i0] at o4
      omega

def meas (j : ℕ) (l : List (Fin n × Fin n)) : ℕ := ∑ r : Fin n × Fin n, if r.1.val = j then l.idxOf r else 0

theorem cn_meas_lt {j : ℕ} {l l' : List (Fin n × Fin n)}
    (h1 : ∀ r : Fin n × Fin n, r.1.val = j → l'.idxOf r ≤ l.idxOf r) (r0 : Fin n × Fin n) (h0 : r0.1.val = j)
    (h2 : l'.idxOf r0 < l.idxOf r0) : meas j l' < meas j l := by
  unfold meas
  apply Finset.sum_lt_sum
  · intro r _
    split_ifs with hr
    · exact h1 r hr
    · exact le_rfl
  · refine ⟨r0, Finset.mem_univ _, ?_⟩
    rw [if_pos h0, if_pos h0]
    exact h2

theorem cn_sort {j : ℕ} : ∀ (m : ℕ) (l : List (Fin n × Fin n)), NO n j l → meas j l < m →
    ∃ lF lG, Steps n l (lF ++ lG) ∧ NO n j (lF ++ lG) ∧ (∀ r ∈ lF, r.1.val = j) ∧ (∀ r ∈ lG, r.1.val ≠ j) := by
  intro m
  induction m with
  | zero => intro l _ h; exact absurd h (Nat.not_lt_zero _)
  | succ m ih =>
    intro l hNO hm
    rcases cn_decomp (fun r : Fin n × Fin n => r.1.val = j) l with
      ⟨lF, lG, rfl, hF, hG⟩ | ⟨l1, ⟨b, c⟩, ⟨j', d⟩, lF, lG, rfl, hg, hf, hF, hG⟩
    · exact ⟨lF, lG, .refl, hNO, hF, hG⟩
    · simp only at hg hf
      have hnd := hNO.1
      have hgm := hNO.2.1 (b, c) (by simp)
      have hfm := hNO.2.1 (j', d) (by simp)
      simp only at hgm hfm
      have hx : (b, c) ∉ l1 := cn_notMem hnd (by simp)
      have hy : (j', d) ∉ l1 := cn_notMem hnd (by simp)
      have hxy : (b, c) ≠ (j', d) := cn_ne (by omega)
      have Pg := idxOf_append_first l1 ((j', d) :: (lF ++ lG)) (b, c) hx
      have Pf := idxOf_append_second l1 (lF ++ lG) (b, c) (j', d) hxy hy
      by_cases hdb : d = b
      · exfalso
        subst hdb
        have t := hNO.2.2.2 j' d c (by omega) hfm.2 hgm.2
        rw [Pg, Pf] at t
        omega
      by_cases hdc : d = c
      · subst hdc
        have t := hNO.2.2.2 j' b d (by omega) (by omega) hgm.2
        rw [Pg, Pf] at t
        cases lF with
        | nil =>
          exfalso
          have hA := hNO.2.2.1 j' b (by omega) (by omega)
          rcases List.mem_append.1 hA with hA | hA
          · have := cn_idx_lt l1 ((b, d) :: (j', d) :: ([] ++ lG)) (j', b) hA
            omega
          · rcases List.mem_cons.1 hA with hA | hA
            · exact cn_ne (by omega) hA
            · rcases List.mem_cons.1 hA with hA | hA
              · exact cn_ne (by omega) hA
              · exact hG _ (by simpa using hA) hf
        | cons f2 lF' =>
          obtain ⟨j'', e⟩ := f2
          have hj'' : j''.val = j := hF (j'', e) List.mem_cons_self
          obtain rfl : j'' = j' := Fin.ext (by omega)
          rw [List.cons_append] at hNO hm
          obtain rfl : e = b := cn_key l1 (lF' ++ lG) b d j'' e hNO hf (by omega) hgm.2
          have hab : j'' < e := by
            have : j''.val < e.val := by omega
            exact this
          have hbc : e < d := hgm.2
          have hNO' := cn_NO_braid' l1 (lF' ++ lG) j'' e d hab hbc hNO
          have hz : (j'', e) ∉ l1 := cn_notMem hNO.1 (by simp)
          have hxz : (e, d) ≠ (j'', e) := cn_ne (by omega)
          have hyz : (j'', d) ≠ (j'', e) := cn_ne (by omega)
          have hlt : meas j (l1 ++ (j'', e) :: (j'', d) :: (e, d) :: (lF' ++ lG)) <
              meas j (l1 ++ (e, d) :: (j'', d) :: (j'', e) :: (lF' ++ lG)) := by
            refine cn_meas_lt ?_ (j'', e) hf ?_
            · rintro ⟨u1, u2⟩ hu
              simp only at hu
              rcases cn_posR_braid l1 (lF' ++ lG) e d j'' d j'' e hxy hxz hyz hx hy hz u1 u2 with
                ⟨e1, -, -, -⟩ | ⟨-, -, e3, e4⟩ | ⟨-, -, e3, e4⟩ | ⟨-, -, -, e3, -⟩
              · omega
              · rw [e3, e4]
              · rw [e3, e4]; omega
              · exact e3.le
            · rw [idxOf_append_first l1 _ _ hz, idxOf_append_third l1 _ _ _ _ hxz hyz hz]
              omega
          obtain ⟨lF2, lG2, hs, hr⟩ := ih _ hNO' (by omega)
          exact ⟨lF2, lG2, Relation.ReflTransGen.head (Step.braid' l1 (lF' ++ lG) j'' e d hab hbc) hs, hr⟩
      · have h1 : b ≠ j' := fun h' => by rw [h'] at hg; exact hg hf
        have h3 : c ≠ j' := fun h' => by rw [h'] at hgm; omega
        have hNO' := cn_NO_swap l1 (lF ++ lG) b c j' d h1 (Ne.symm hdb) h3 (Ne.symm hdc) hNO
        have hlt : meas j (l1 ++ (j', d) :: (b, c) :: (lF ++ lG)) <
            meas j (l1 ++ (b, c) :: (j', d) :: (lF ++ lG)) := by
          refine cn_meas_lt ?_ (j', d) hf ?_
          · rintro ⟨u1, u2⟩ hu
            simp only at hu
            rcases cn_posR_swap l1 (lF ++ lG) b c j' d hxy hx hy u1 u2 with
              ⟨e1, -, -, -⟩ | ⟨-, -, e3, e4⟩ | ⟨-, -, e3, -⟩
            · omega
            · rw [e3, e4]; omega
            · exact e3.le
          · rw [idxOf_append_first l1 _ _ hy, Pf]
            omega
        obtain ⟨lF2, lG2, hs, hr⟩ := ih _ hNO' (by omega)
        exact ⟨lF2, lG2, Relation.ReflTransGen.head
          (Step.swap l1 (lF ++ lG) b c j' d h1 (Ne.symm hdb) h3 (Ne.symm hdc)) hs, hr⟩

end Formalism.MainNotions.G.ExtremalProjector
end

namespace Formalism.MainNotions.G.ExtremalProjector

open Formalism.MainNotions.G

variable {n : ℕ}

theorem cn_front {j : ℕ} {l : List (Fin n × Fin n)} (h : NO n j l) (a b : Fin n) (ha : a.val = j)
    (hab : a.val + 1 = b.val) : ∃ l', Steps n l ((a, b) :: l') := by
  obtain ⟨lF, lG, hs, hNO, hF, hG⟩ := cn_sort (meas j l + 1) l h (Nat.lt_succ_self _)
  cases lF with
  | nil =>
    exfalso
    have hA := hNO.2.2.1 a b (by omega) (by omega)
    exact hG _ (by simpa using hA) ha
  | cons f lF' =>
    obtain ⟨a', d⟩ := f
    have ha' : a'.val = j := hF (a', d) List.mem_cons_self
    obtain rfl : a' = a := Fin.ext (by omega)
    have hd := (hNO.2.1 (a', d) (by simp)).2
    simp only at hd
    have hdb : d = b := by
      by_contra hne
      have hne' : d.val ≠ b.val := fun h' => hne (Fin.ext h')
      have t := hNO.2.2.2 a' b d (by omega) (by omega) (by omega)
      rw [List.cons_append, List.idxOf_cons_self] at t
      omega
    subst hdb
    exact ⟨lF' ++ lG, hs⟩

private lemma idxOf_append_of_not_mem_beq {α : Type} [BEq α] [LawfulBEq α] (l₁ l₂ : List α) (x : α) (hx : x ∉ l₁) :
    (l₁ ++ l₂).idxOf x = l₁.length + l₂.idxOf x := by
  induction l₁ with
  | nil => simp
  | cons y t ih =>
    have hxy : y ≠ x := fun h => hx (h ▸ List.mem_cons_self)
    have hxt : x ∉ t := fun h => hx (List.mem_cons_of_mem _ h)
    simp [List.idxOf_cons, ih hxt, hxy] <;> omega

theorem cn_NO_drop {j : ℕ} {lF lG : List (Fin n × Fin n)} (h : NO n j (lF ++ lG)) (hF : ∀ r ∈ lF, r.1.val = j)
    (hG : ∀ r ∈ lG, r.1.val ≠ j) : NO n (j + 1) lG := by
  obtain ⟨hnd, hrange, hall, hord⟩ := h
  have hmem : ∀ x y : Fin n, j + 1 ≤ x.val → (x, y) ∉ lF := fun x y hx hm => by
    have h1 := hF _ hm
    simp at h1
    omega
  refine ⟨List.Nodup.sublist (List.sublist_append_right lF lG) hnd, ?_, ?_, ?_⟩
  · intro ab hab
    have h1 := hrange ab (List.mem_append_right lF hab)
    have h2 := hG ab hab
    exact ⟨by omega, h1.2⟩
  · intro a b ha hab
    rcases List.mem_append.mp (hall a b (by omega) hab) with h1 | h1
    · exact absurd h1 (hmem a b ha)
    · exact h1
  · intro a b c ha hab hbc
    have ho := hord a b c (by omega) hab hbc
    rw [idxOf_append_of_not_mem_beq lF lG _ (hmem a b ha), idxOf_append_of_not_mem_beq lF lG _ (hmem a c ha),
      idxOf_append_of_not_mem_beq lF lG _ (hmem b c (by omega))] at ho
    omega

theorem cn_back {j : ℕ} {l : List (Fin n × Fin n)} (h : NO n j l) :
    ∃ l' R, Steps n l (l' ++ R) ∧ NO n (j + 1) l' := by
  obtain ⟨lF, lG, hs, hno, hF, hG⟩ :=
    cn_sort (meas j l.reverse + 1) l.reverse (cn_NO_rev h) (Nat.lt_succ_self _)
  refine ⟨lG.reverse, lF.reverse, ?_, cn_NO_rev (cn_NO_drop hno hF hG)⟩
  have h2 := cn_steps_rev hs
  rwa [List.reverse_reverse, List.reverse_append] at h2

theorem cn_iter {ord : List (Fin n × Fin n)} (h : NO n 0 ord) :
    ∀ j : ℕ, ∃ l' R, Steps n ord (l' ++ R) ∧ NO n j l' := by
  intro j
  induction j with
  | zero => exact ⟨ord, [], by simpa using (Relation.ReflTransGen.refl : Steps n ord ord), h⟩
  | succ j ih =>
    obtain ⟨l', R, hs, hno⟩ := ih
    obtain ⟨l'', R', hs', hno'⟩ := cn_back hno
    refine ⟨l'', R' ++ R, ?_, hno'⟩
    have h2 := cn_steps_tail hs' R
    rw [List.append_assoc] at h2
    exact hs.trans h2

theorem restConn : RestConn := by
  intro n ord hord a b hab
  obtain ⟨l', R, hs, hno⟩ := cn_iter (cn_NO_of_normal hord) a.val
  obtain ⟨l'', hs'⟩ := cn_front hno a b rfl hab
  exact ⟨l'' ++ R, hs.trans (cn_steps_tail hs' R)⟩

end Formalism.MainNotions.G.ExtremalProjector
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.TruncatedChains.RaisingKillOfInterface
noncomputable section

open Finset

namespace Formalism.MainNotions.G.ExtremalProjector

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.G.GLWeightTheory

section

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem pp_append (E : GLOps n K V) (mu : Fin n → ℤ) (l1 l2 : List (Fin n × Fin n)) (T : ℕ) (x : V) :
    pp E mu (l1 ++ l2) T x = pp E mu l1 T (pp E mu l2 T x) := by
  simp only [pp, List.map_append, List.prod_append, Module.End.mul_apply]

theorem pp_cons (E : GLOps n K V) (mu : Fin n → ℤ) (ab : Fin n × Fin n) (l : List (Fin n × Fin n)) (T : ℕ) (x : V) :
    pp E mu (ab :: l) T x = ppFac E mu ab.1 ab.2 T (pp E mu l T x) := by
  simp only [pp, List.map_cons, List.prod_cons, Module.End.mul_apply]

end

private theorem mem_weightSp_iff_forall_diag {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (E : GLOps n K V) (ν : Fin n → ℤ) (y : V) :
    y ∈ weightSp E ν ↔ ∀ c, E c c y = (ν c : K) • y := by
  simp only [weightSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, sub_eq_zero]
  first
  | simp only [Module.End.one_apply]
  | simp only [LinearMap.one_apply]

private theorem glRep_apply_mem_weightSp_shift {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (E : GLOps n K V) (hE : IsGLRep E) (a b : Fin n) (ν : Fin n → ℤ) (y : V)
    (hy : y ∈ weightSp E ν) :
    E a b y ∈ weightSp E (fun c => ν c + ((if c = a then 1 else 0) - (if c = b then 1 else 0))) := by
  rw [mem_weightSp_iff_forall_diag] at hy ⊢
  intro c
  have h := congrArg (fun f : Module.End K V => f y) (hE.1 c c a b)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, hy c, map_smul] at h
  rw [sub_eq_iff_eq_add] at h
  rw [h]
  by_cases hca : c = a
  · subst hca
    by_cases hcb : c = b
    · subst hcb
      simp only [eq_self_iff_true, if_true]
      push_cast
      first
      | module
      | (simp [add_smul, sub_smul])
    · have hbc : ¬ b = c := fun h => hcb h.symm
      simp only [eq_self_iff_true, if_true, if_neg hbc, if_neg hcb, LinearMap.zero_apply, sub_zero]
      push_cast
      first
      | module
      | (simp [add_smul, sub_smul]; abel)
  · by_cases hcb : c = b
    · subst hcb
      simp only [eq_self_iff_true, if_true, if_neg hca, LinearMap.zero_apply, zero_sub]
      push_cast
      first
      | module
      | (simp [add_smul, sub_smul]; abel)
    · have hbc : ¬ b = c := fun h => hcb h.symm
      simp only [if_neg hca, if_neg hbc, if_neg hcb, LinearMap.zero_apply, sub_zero, zero_add]
      push_cast
      first
      | module
      | simp

private theorem glRep_pow_apply_mem_weightSp_shift {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (E : GLOps n K V) (hE : IsGLRep E) (a b : Fin n) (k : ℕ) (ν : Fin n → ℤ) (y : V)
    (hy : y ∈ weightSp E ν) :
    (E a b ^ k) y ∈ weightSp E
      (fun c => ν c + (k : ℤ) * ((if c = a then 1 else 0) - (if c = b then 1 else 0))) := by
  induction k generalizing ν y with
  | zero => simpa using hy
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply]
    have h1 := ih _ _ (glRep_apply_mem_weightSp_shift E hE a b ν y hy)
    convert h1 using 2
    funext c
    push_cast
    ring

private theorem ppFac_apply_mem_weightSp_of_mem {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (E : GLOps n K V) (hE : IsGLRep E) (mu : Fin n → ℤ) (a b : Fin n) (T : ℕ) (ν : Fin n → ℤ)
    (y : V) (hy : y ∈ weightSp E ν) : ppFac E mu a b T y ∈ weightSp E ν := by
  unfold ppFac
  first
  | rw [LinearMap.sum_apply]
  | rw [LinearMap.coe_sum, Finset.sum_apply]
  | rw [LinearMap.coe_fn_sum, Finset.sum_apply]
  refine Submodule.sum_mem _ fun k _ => ?_
  simp only [divPowE, LinearMap.smul_apply, Module.End.mul_apply, map_smul]
  refine Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.smul_mem _ _ ?_))
  have h1 := glRep_pow_apply_mem_weightSp_shift E hE a b k ν y hy
  have h2 := glRep_pow_apply_mem_weightSp_shift E hE b a k _ _ h1
  convert h2 using 2
  funext c
  ring

private theorem pp_apply_mem_weightSp_of_mem {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (E : GLOps n K V) (hE : IsGLRep E) (mu : Fin n → ℤ) (l : List (Fin n × Fin n)) (T : ℕ)
    (ν : Fin n → ℤ) (y : V) (hy : y ∈ weightSp E ν) : pp E mu l T y ∈ weightSp E ν := by
  induction l with
  | nil => simpa [pp] using hy
  | cons ab l ih =>
    rw [pp_cons]
    exact ppFac_apply_mem_weightSp_of_mem E hE mu ab.1 ab.2 T ν _ ih

theorem pp_step (hC : RestComm) (hY : RestYB) {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {n : ℕ} (E : GLOps n K V) (hE : IsGLRep E) (mu : Fin n → ℤ)
    (hmu : ∀ a b : Fin n, a < b → 1 ≤ mu a - mu b + ((b : ℤ) - (a : ℤ))) (T : ℕ) (hT : Module.finrank K V ≤ T)
    {l l' : List (Fin n × Fin n)} (h : Step n l l') (x : V) (hx : x ∈ weightSp E mu) :
    pp E mu l T x = pp E mu l' T x := by
  cases h with
  | swap l1 l2 a b c d hac had hbc hbd =>
    simp only [pp_append, pp_cons, ppFac_eq]
    congr 1
    exact LinearMap.congr_fun (hC K V n E hE a b c d hac had hbc hbd _ _ T).eq _
  | braid l1 l2 a b c hab hbc =>
    simp only [pp_append, pp_cons, ppFac_eq]
    congr 1
    have h1 := hmu a b hab
    have h2 := hmu b c hbc
    have h3 := hmu a c (hab.trans hbc)
    have hab2 : (a : ℕ) < b := hab
    have hbc2 : (b : ℕ) < c := hbc
    have e1 : ((mu a - mu b + ((b : ℤ) - (a : ℤ))).toNat : ℤ) = mu a - mu b + ((b : ℤ) - (a : ℤ)) :=
      Int.toNat_of_nonneg (by omega)
    have e2 : ((mu b - mu c + ((c : ℤ) - (b : ℤ))).toNat : ℤ) = mu b - mu c + ((c : ℤ) - (b : ℤ)) :=
      Int.toNat_of_nonneg (by omega)
    have e3 : ((mu a - mu c + ((c : ℤ) - (a : ℤ))).toNat : ℤ) = mu a - mu c + ((c : ℤ) - (a : ℤ)) :=
      Int.toNat_of_nonneg (by omega)
    have hu : (mu a - mu c + ((c : ℤ) - (a : ℤ))).toNat =
        (mu a - mu b + ((b : ℤ) - (a : ℤ))).toNat + (mu b - mu c + ((c : ℤ) - (b : ℤ))).toNat := by
      omega
    rw [hu]
    exact hY ((b : ℕ) - a - 1) ((c : ℕ) - b - 1) K V n E hE a b c hab.ne (hab.trans hbc).ne hbc.ne
      mu _ _ (by omega) (by omega) T hT _ (pp_apply_mem_weightSp_of_mem E hE mu l2 T mu x hx)
  | braid' l1 l2 a b c hab hbc =>
    simp only [pp_append, pp_cons, ppFac_eq]
    congr 1
    have h1 := hmu a b hab
    have h2 := hmu b c hbc
    have h3 := hmu a c (hab.trans hbc)
    have hab2 : (a : ℕ) < b := hab
    have hbc2 : (b : ℕ) < c := hbc
    have e1 : ((mu a - mu b + ((b : ℤ) - (a : ℤ))).toNat : ℤ) = mu a - mu b + ((b : ℤ) - (a : ℤ)) :=
      Int.toNat_of_nonneg (by omega)
    have e2 : ((mu b - mu c + ((c : ℤ) - (b : ℤ))).toNat : ℤ) = mu b - mu c + ((c : ℤ) - (b : ℤ)) :=
      Int.toNat_of_nonneg (by omega)
    have e3 : ((mu a - mu c + ((c : ℤ) - (a : ℤ))).toNat : ℤ) = mu a - mu c + ((c : ℤ) - (a : ℤ)) :=
      Int.toNat_of_nonneg (by omega)
    have hu : (mu a - mu c + ((c : ℤ) - (a : ℤ))).toNat =
        (mu a - mu b + ((b : ℤ) - (a : ℤ))).toNat + (mu b - mu c + ((c : ℤ) - (b : ℤ))).toNat := by
      omega
    rw [hu]
    exact (hY ((b : ℕ) - a - 1) ((c : ℕ) - b - 1) K V n E hE a b c hab.ne (hab.trans hbc).ne hbc.ne
      mu _ _ (by omega) (by omega) T hT _ (pp_apply_mem_weightSp_of_mem E hE mu l2 T mu x hx)).symm

theorem raising_kill_of_interface (hN : RestConn) (hC : RestComm) (hY : RestYB) (hK : RestKill) : SimpleRaisingKillsExtremalProjector := by
  intro K V _ _ _ _ _ n E hE mu hmu ord hord T hT x hx a b hab
  obtain ⟨l, hl⟩ := hN n ord hord a b hab
  have key : ∀ l', Relation.ReflTransGen (Step n) ord l' → pp E mu ord T x = pp E mu l' T x := by
    intro l' hl'
    induction hl' with
    | refl => rfl
    | tail _ hs ih => rw [ih, pp_step hC hY E hE mu hmu T hT hs x hx]
  have hlt : a < b := by
    rw [Fin.lt_iff_val_lt_val]
    omega
  have h1 := hmu a b hlt
  have hba : ((b : ℕ) : ℤ) - ((a : ℕ) : ℤ) = 1 := by omega
  have key2 : ((mu a - mu b + ((b : ℤ) - (a : ℤ))).toNat : ℤ) = mu a - mu b + 1 := by
    rw [Int.toNat_of_nonneg (by linarith)]
    linarith
  rw [key _ hl, pp_cons, ppFac_eq]
  exact hK K V n E hE a b hlt.ne mu _ key2 T hT _ (pp_apply_mem_weightSp_of_mem E hE mu l T mu x hx)

end Formalism.MainNotions.G.ExtremalProjector
end
end

namespace Formalism.MainNotions.G.ExtremalProjector

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.G.GLWeightTheory

theorem restYB (D : Formalism.BasicNotions.D7) : RestYB :=
  restYB_of (ybat_base D restKill restPair (restPair'_of restPair)) ybat_symm

theorem raising_operators_kill_image (D : Formalism.BasicNotions.D7) : SimpleRaisingKillsExtremalProjector :=
  raising_kill_of_interface restConn restComm (restYB D) restKill

theorem extremal_projector_statement (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.CovariantDegrees.adm5 D := sizes_bound_of_log_estimates D (raising_operators_kill_image D)

end Formalism.MainNotions.G.ExtremalProjector
