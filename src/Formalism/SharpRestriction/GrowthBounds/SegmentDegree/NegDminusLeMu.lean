module

public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.ThresholdPowerBoundOfCounts

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.NegDminusLeMu
noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf.T

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

variable {n N : ℕ} {LL : Letters (Fin N)} {dd : Fin N → ℕ}

theorem step_vec (P : PPath n N LL dd) (i : Fin N) (h : LL.vec i = true) :
    HStrip (P.mu i.castSucc) (P.mu i.succ) (dd i) := by
  simpa [h] using P.step i

theorem step_cov (P : PPath n N LL dd) (i : Fin N) (h : LL.vec i = false) :
    HStrip (P.mu i.succ) (P.mu i.castSucc) (dd i) := by
  simpa [h] using P.step i

theorem mu_nonneg (P : PPath n N LL dd) :
    ∀ (s : ℕ) (hs : s < N + 1) (m : Fin n), m.val + s < n → 0 ≤ P.mu ⟨s, hs⟩ m := by
  intro s
  induction s with
  | zero =>
    intro hs m _
    have h0 : (⟨0, hs⟩ : Fin (N + 1)) = 0 := Fin.ext (by simp)
    rw [h0, P.zero]
    simp
  | succ s ih =>
    intro hs m hm
    have hsN : s < N := by omega
    cases hv : LL.vec ⟨s, hsN⟩
    · have hstr : HStrip (P.mu ⟨s + 1, hs⟩) (P.mu ⟨s, by omega⟩) (dd ⟨s, hsN⟩) := step_cov P ⟨s, hsN⟩ hv
      have hm1 : m.val + 1 < n := by omega
      calc (0 : ℤ) ≤ P.mu ⟨s, by omega⟩ ⟨m.val + 1, hm1⟩ :=
            ih (by omega) ⟨m.val + 1, hm1⟩ (show m.val + 1 + s < n by omega)
        _ ≤ P.mu ⟨s + 1, hs⟩ m := hstr.2.1 m hm1
    · have hstr : HStrip (P.mu ⟨s, by omega⟩) (P.mu ⟨s + 1, hs⟩) (dd ⟨s, hsN⟩) := step_vec P ⟨s, hsN⟩ hv
      calc (0 : ℤ) ≤ P.mu ⟨s, by omega⟩ m := ih (by omega) m (by omega)
        _ ≤ P.mu ⟨s + 1, hs⟩ m := hstr.1 m

theorem mu_nonpos (P : PPath n N LL dd) :
    ∀ (s : ℕ) (hs : s < N + 1) (m : Fin n), s ≤ m.val → P.mu ⟨s, hs⟩ m ≤ 0 := by
  intro s
  induction s with
  | zero =>
    intro hs m _
    have h0 : (⟨0, hs⟩ : Fin (N + 1)) = 0 := Fin.ext (by simp)
    rw [h0, P.zero]
    simp
  | succ s ih =>
    intro hs m hm
    have hsN : s < N := by omega
    obtain ⟨mv, hmv⟩ := m
    have hm' : s + 1 ≤ mv := hm
    cases hv : LL.vec ⟨s, hsN⟩
    · have hstr : HStrip (P.mu ⟨s + 1, hs⟩) (P.mu ⟨s, by omega⟩) (dd ⟨s, hsN⟩) := step_cov P ⟨s, hsN⟩ hv
      calc P.mu ⟨s + 1, hs⟩ ⟨mv, hmv⟩ ≤ P.mu ⟨s, by omega⟩ ⟨mv, hmv⟩ := hstr.1 _
        _ ≤ 0 := ih (by omega) ⟨mv, hmv⟩ (show s ≤ mv by omega)
    · have hstr : HStrip (P.mu ⟨s, by omega⟩) (P.mu ⟨s + 1, hs⟩) (dd ⟨s, hsN⟩) := step_vec P ⟨s, hsN⟩ hv
      obtain _ | mv := mv
      · omega
      · calc P.mu ⟨s + 1, hs⟩ ⟨mv + 1, hmv⟩ ≤ P.mu ⟨s, by omega⟩ ⟨mv, by omega⟩ := hstr.2.1 ⟨mv, by omega⟩ hmv
          _ ≤ 0 := ih (by omega) ⟨mv, by omega⟩ (show s ≤ mv by omega)

def dplus (LL : Letters (Fin N)) (dd : Fin N → ℕ) (s : ℕ) : ℕ :=
  ∑ l : Fin N, if l.val < s ∧ LL.vec l = true then dd l else 0

def dminus (LL : Letters (Fin N)) (dd : Fin N → ℕ) (s : ℕ) : ℕ :=
  ∑ l : Fin N, if l.val < s ∧ LL.vec l = false then dd l else 0

theorem dsum_succ (f : Fin N → Prop) [DecidablePred f] (dd : Fin N → ℕ) (s : ℕ) (hs : s < N) :
    (∑ l : Fin N, if l.val < s + 1 ∧ f l then dd l else 0) =
      (∑ l : Fin N, if l.val < s ∧ f l then dd l else 0) + if f ⟨s, hs⟩ then dd ⟨s, hs⟩ else 0 := by
  have key : ∀ l : Fin N, (if l.val < s + 1 ∧ f l then dd l else 0) =
      (if l.val < s ∧ f l then dd l else 0) + (if l = ⟨s, hs⟩ then (if f ⟨s, hs⟩ then dd ⟨s, hs⟩ else 0) else 0) := by
    intro l
    by_cases h1 : l = ⟨s, hs⟩
    · subst h1
      simp
    · have hne : l.val ≠ s := fun h => h1 (Fin.ext h)
      have hiff : (l.val < s + 1 ∧ f l) ↔ (l.val < s ∧ f l) :=
        ⟨fun ⟨a, b⟩ => ⟨by omega, b⟩, fun ⟨a, b⟩ => ⟨by omega, b⟩⟩
      simp only [hiff, h1, if_false, add_zero]
  rw [Finset.sum_congr rfl (fun l _ => key l), Finset.sum_add_distrib]
  simp

theorem strip_le_add {nu mu : Fin n → ℤ} {b : ℕ} (h : HStrip nu mu b) (m : Fin n) : mu m ≤ nu m + b := by
  have h1 : mu m - nu m ≤ ∑ a, (mu a - nu a) :=
    Finset.single_le_sum (f := fun a => mu a - nu a) (fun a _ => sub_nonneg.mpr (h.1 a)) (Finset.mem_univ m)
  rw [h.2.2] at h1
  linarith

theorem mu_le_dplus (P : PPath n N LL dd) :
    ∀ (s : ℕ) (hs : s < N + 1) (m : Fin n), P.mu ⟨s, hs⟩ m ≤ (dplus LL dd s : ℤ) := by
  intro s
  induction s with
  | zero =>
    intro hs m
    have h0 : (⟨0, hs⟩ : Fin (N + 1)) = 0 := Fin.ext (by simp)
    rw [h0, P.zero]
    simp
  | succ s ih =>
    intro hs m
    have hsN : s < N := by omega
    have hd : (∑ l : Fin N, if l.val < s + 1 ∧ LL.vec l = true then dd l else 0) =
        (∑ l : Fin N, if l.val < s ∧ LL.vec l = true then dd l else 0) +
          if LL.vec ⟨s, hsN⟩ = true then dd ⟨s, hsN⟩ else 0 :=
      dsum_succ (fun l : Fin N => LL.vec l = true) dd s hsN
    have h1 := ih (by omega) m
    cases hv : LL.vec ⟨s, hsN⟩
    · have hstr : HStrip (P.mu ⟨s + 1, hs⟩) (P.mu ⟨s, by omega⟩) (dd ⟨s, hsN⟩) := step_cov P ⟨s, hsN⟩ hv
      have h2 : dplus LL dd (s + 1) = dplus LL dd s := by
        unfold dplus
        rw [hd, hv]
        simp
      rw [h2]
      exact (hstr.1 m).trans h1
    · have hstr : HStrip (P.mu ⟨s, by omega⟩) (P.mu ⟨s + 1, hs⟩) (dd ⟨s, hsN⟩) := step_vec P ⟨s, hsN⟩ hv
      have h2 : dplus LL dd (s + 1) = dplus LL dd s + dd ⟨s, hsN⟩ := by
        unfold dplus
        rw [hd, hv]
        simp
      have h3 := strip_le_add hstr m
      rw [h2]
      push_cast
      linarith

theorem neg_dminus_le_mu (P : PPath n N LL dd) :
    ∀ (s : ℕ) (hs : s < N + 1) (m : Fin n), -(dminus LL dd s : ℤ) ≤ P.mu ⟨s, hs⟩ m := by
  intro s
  induction s with
  | zero =>
    intro hs m
    have h0 : (⟨0, hs⟩ : Fin (N + 1)) = 0 := Fin.ext (by simp)
    rw [h0, P.zero]
    simp
  | succ s ih =>
    intro hs m
    have hsN : s < N := by omega
    have hd : (∑ l : Fin N, if l.val < s + 1 ∧ LL.vec l = false then dd l else 0) =
        (∑ l : Fin N, if l.val < s ∧ LL.vec l = false then dd l else 0) +
          if LL.vec ⟨s, hsN⟩ = false then dd ⟨s, hsN⟩ else 0 :=
      dsum_succ (fun l : Fin N => LL.vec l = false) dd s hsN
    have h1 := ih (by omega) m
    cases hv : LL.vec ⟨s, hsN⟩
    · have hstr : HStrip (P.mu ⟨s + 1, hs⟩) (P.mu ⟨s, by omega⟩) (dd ⟨s, hsN⟩) := step_cov P ⟨s, hsN⟩ hv
      have h2 : dminus LL dd (s + 1) = dminus LL dd s + dd ⟨s, hsN⟩ := by
        unfold dminus
        rw [hd, hv]
        simp
      have h3 := strip_le_add hstr m
      rw [h2]
      push_cast
      linarith
    · have hstr : HStrip (P.mu ⟨s, by omega⟩) (P.mu ⟨s + 1, hs⟩) (dd ⟨s, hsN⟩) := step_vec P ⟨s, hsN⟩ hv
      have h2 : dminus LL dd (s + 1) = dminus LL dd s := by
        unfold dminus
        rw [hd, hv]
        simp
      rw [h2]
      exact h1.trans (hstr.1 m)

def vcount (LL : Letters (Fin N)) (t s : ℕ) : ℕ :=
  (Finset.univ.filter fun l : Fin N => t ≤ l.val ∧ l.val < s ∧ LL.vec l = true).card

theorem vcount_self (LL : Letters (Fin N)) (t : ℕ) : vcount LL t t = 0 := by
  unfold vcount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro l _ h
  obtain ⟨h1, h2, -⟩ := h
  omega

theorem vcount_succ (LL : Letters (Fin N)) (t s : ℕ) (hts : t ≤ s) (hs : s < N) :
    vcount LL t (s + 1) = vcount LL t s + if LL.vec ⟨s, hs⟩ = true then 1 else 0 := by
  unfold vcount
  by_cases hv : LL.vec ⟨s, hs⟩ = true
  · rw [if_pos hv]
    have hset : (Finset.univ.filter fun l : Fin N => t ≤ l.val ∧ l.val < s + 1 ∧ LL.vec l = true) =
        insert ⟨s, hs⟩ (Finset.univ.filter fun l : Fin N => t ≤ l.val ∧ l.val < s ∧ LL.vec l = true) := by
      ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · rintro ⟨h1, h2, h3⟩
        by_cases hl : l.val = s
        · left
          exact Fin.ext hl
        · right
          exact ⟨h1, by omega, h3⟩
      · rintro (rfl | ⟨h1, h2, h3⟩)
        · exact ⟨hts, Nat.lt_succ_self s, hv⟩
        · exact ⟨h1, by omega, h3⟩
    rw [hset, Finset.card_insert_of_notMem]
    simp
  · rw [if_neg hv, add_zero]
    congr 1
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, ?_, h3⟩
      by_contra hc
      have hl : l = ⟨s, hs⟩ := Fin.ext (show l.val = s by omega)
      subst hl
      exact hv h3
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, by omega, h3⟩

theorem row_back (P : PPath n N LL dd) (t : ℕ) :
    ∀ (s : ℕ) (_hts : t ≤ s) (hs : s < N + 1) (m m' : Fin n), m'.val = m.val + vcount LL t s →
      P.mu ⟨s, hs⟩ m' ≤ P.mu ⟨t, by omega⟩ m := by
  intro s hts
  induction s, hts using Nat.le_induction with
  | base =>
    intro hs m m' hm
    rw [vcount_self, add_zero] at hm
    have he : m' = m := Fin.ext hm
    subst he
    exact le_refl _
  | succ s hts ih =>
    intro hs m m' hm
    have hsN : s < N := by omega
    rw [vcount_succ LL t s hts hsN] at hm
    cases hv : LL.vec ⟨s, hsN⟩
    · rw [hv] at hm
      simp only [Bool.false_eq_true, if_false, add_zero] at hm
      have hstr : HStrip (P.mu ⟨s + 1, hs⟩) (P.mu ⟨s, by omega⟩) (dd ⟨s, hsN⟩) := step_cov P ⟨s, hsN⟩ hv
      exact (hstr.1 m').trans (ih (by omega) m m' hm)
    · rw [hv] at hm
      simp only [if_true] at hm
      have hstr : HStrip (P.mu ⟨s, by omega⟩) (P.mu ⟨s + 1, hs⟩) (dd ⟨s, hsN⟩) := step_vec P ⟨s, hsN⟩ hv
      have hlt := m'.isLt
      have ha : m.val + vcount LL t s < n := by omega
      have he : m' = ⟨m.val + vcount LL t s + 1, by omega⟩ := Fin.ext hm
      rw [he]
      exact (hstr.2.1 ⟨m.val + vcount LL t s, ha⟩ (by simp only; omega)).trans
        (ih (by omega) m ⟨m.val + vcount LL t s, ha⟩ rfl)

end Formalism.MainNotions.SelectionLemmas.Pf.T
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.OldestLetterInSegment
noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

section Rows

variable {n' r : ℕ} [NeZero n'] [NeZero r]


open Classical in
def evL (F : Frames n' r) (j x : ℤ) : List ℤ := ((F.letters j).filter fun z => Even z ∧ z < x).sort (· ≤ ·)

theorem row_eq (X : Dat n' r) (j x : ℤ) (i : Fin r) :
    X.row j x i = (evL X.F j x).getD ((evL X.F j x).length - r + i.val) 0 := rfl

theorem oldest_eq (F : Frames n' r) (j x : ℤ) : F.oldest j x = (evL F j x).getD ((evL F j x).length - r) 0 := rfl

theorem mem_evL (F : Frames n' r) (j x z : ℤ) : z ∈ evL F j x ↔ z ∈ F.letters j ∧ Even z ∧ z < x := by
  classical
  unfold evL
  rw [Finset.mem_sort, Finset.mem_filter]

theorem bk_fr_lt {F : Frames n' r} {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁) (j : ℤ) (i : ℕ) :
    ∀ i', i < i' → i' < r → F.fr j i < F.fr j i' := by
  intro i' hi hi'
  induction i', hi using Nat.le_induction with
  | base => exact hV.2.2.1 j i hi'
  | succ k hik ih =>
    exact lt_trans (ih (by omega)) (hV.2.2.1 j k hi')

theorem bk_fr_le {F : Frames n' r} {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁) (j : ℤ) (i i' : ℕ) (h : i ≤ i') (h' : i' < r) :
    F.fr j i ≤ F.fr j i' := by
  rcases Nat.lt_or_eq_of_le h with h1 | h1
  · exact le_of_lt (bk_fr_lt hV j i i' h1 h')
  · rw [h1]

theorem r_le_length {F : Frames n' r} {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁) (j x : ℤ) (hx : x ∈ F.letters j)
    (hW : ¬ F.IsW j x) : r ≤ (evL F j x).length := by
  have hr : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  have hW' : F.fr (j - 1) (r - 1) < x := lt_of_not_ge hW
  have h4 : F.fr (j - 1) (r - 1) < F.fr j 0 := by
    have := hV.2.2.2.1 (j - 1)
    rwa [sub_add_cancel] at this
  have hj0 : F.fr j 0 ≤ F.fr j (r - 1) := bk_fr_le hV j 0 (r - 1) (Nat.zero_le _) (by omega)
  have hsub : (Finset.range r).image (fun i => F.fr (j - 1) i) ⊆
      (F.letters j).filter (fun z => Even z ∧ z < x) := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨i, hi, rfl⟩ := hy
    rw [Finset.mem_range] at hi
    have hle : F.fr (j - 1) i ≤ F.fr (j - 1) (r - 1) := bk_fr_le hV (j - 1) i (r - 1) (by omega) (by omega)
    have hge : F.fr (j - 1) 0 ≤ F.fr (j - 1) i := bk_fr_le hV (j - 1) 0 i (Nat.zero_le _) hi
    have h5 := hV.2.2.2.2.1 (j - 1) i hi
    rw [Finset.mem_filter]
    refine ⟨?_, h5.2, lt_of_le_of_lt hle hW'⟩
    unfold Frames.letters
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hge, by linarith⟩, h5.1⟩
  have hinj : Set.InjOn (fun i => F.fr (j - 1) i) (Finset.range r : Set ℕ) := by
    intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h1 | h1
    · exact absurd hab (ne_of_lt (bk_fr_lt hV (j - 1) a b h1 hb))
    · exact absurd hab (ne_of_gt (bk_fr_lt hV (j - 1) b a h1 ha))
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj, Finset.card_range] at hc
  unfold evL
  rw [Finset.length_sort]
  exact hc

theorem evL_nodup (F : Frames n' r) (j x : ℤ) : (evL F j x).Nodup := by
  classical
  unfold evL
  exact Finset.sort_nodup _ _

theorem evL_mono (F : Frames n' r) (j x : ℤ) {a b : ℕ} (hab : a ≤ b) (hb : b < (evL F j x).length) :
    (evL F j x)[a]'(lt_of_le_of_lt hab hb) ≤ (evL F j x)[b]'hb := by
  have hp : (evL F j x).Pairwise (· ≤ ·) := Finset.pairwise_sort _ _
  rcases Nat.lt_or_eq_of_le hab with h1 | h1
  · exact List.pairwise_iff_getElem.mp hp a b _ hb h1
  · subst h1
    exact le_refl _

end Rows

theorem late_row_injective : LateIndexInjective := by
  intro p n' r K _ _ _ X hX j x hx
  unfold Dat.toLate at hx
  simp only [Finset.mem_filter] at hx
  have hlen := r_le_length hX.valid j x hx.1 hx.2
  have hidx : ∀ i : Fin r, (evL X.F j x).length - r + i.val < (evL X.F j x).length := by
    intro i
    have := i.isLt
    omega
  have hrow : ∀ i : Fin r, X.row j x i = (evL X.F j x)[(evL X.F j x).length - r + i.val]'(hidx i) := by
    intro i
    rw [row_eq, List.getD_eq_getElem]
  refine ⟨?_, ?_⟩
  · intro a b h
    rw [hrow, hrow] at h
    have := (evL_nodup X.F j x).getElem_inj_iff.mp h
    exact Fin.ext (by omega)
  · intro i
    rw [hrow]
    exact (mem_evL X.F j x _).mp (List.getElem_mem _)

theorem oldest_letter_in_segment : OldestLetterInSegment := by
  intro p n' r K _ _ _ X hX j x hx
  unfold Dat.toLate at hx
  simp only [Finset.mem_filter] at hx
  have hV := hX.valid
  have hr : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  have hlen := r_le_length hV j x hx.1 hx.2
  have hk : (evL X.F j x).length - r < (evL X.F j x).length := by omega
  have hold : X.F.oldest j x = (evL X.F j x)[(evL X.F j x).length - r]'hk := by
    rw [oldest_eq, List.getD_eq_getElem]
  have hmem := (mem_evL X.F j x _).mp (List.getElem_mem hk)
  rw [hold]
  refine ⟨hmem.1, ?_⟩
  intro hnW
  have hlet := hmem.1
  unfold Frames.letters at hlet
  rw [Finset.mem_filter, Finset.mem_Icc] at hlet
  unfold Frames.LLset
  rw [Finset.mem_filter, Finset.mem_Ioo]
  refine ⟨⟨lt_of_not_ge hnW, ?_⟩, hlet.2⟩
  by_contra hge
  push_neg at hge
  have frame : ∀ y ∈ X.F.letters j, X.F.fr j 0 ≤ y → ∃ i < r, X.F.fr j i = y := by
    intro y hy hy0
    unfold Frames.letters at hy
    rw [Finset.mem_filter, Finset.mem_Icc] at hy
    by_contra hne
    push_neg at hne
    have hall : ∀ i, i < r → X.F.fr j i < y := by
      intro i
      induction i with
      | zero => intro h0; exact lt_of_le_of_ne hy0 (hne 0 h0)
      | succ m ih =>
        intro hm
        have h1 := ih (by omega)
        by_contra h2
        push_neg at h2
        rcases lt_or_eq_of_le h2 with h3 | h3
        · exact hV.2.2.2.2.2.1 j m y hm h1 h3 hy.2
        · exact hne (m + 1) hm h3.symm
    have := hall (r - 1) (by omega)
    linarith [hy.1.2]
  set l := evL X.F j x with hl
  set k := l.length - r with hkdef
  have hdl : (l.drop k).length = r := by
    rw [List.length_drop]
    omega
  have hnd : (l.drop k).Nodup := (evL_nodup X.F j x).sublist (List.drop_sublist _ _)
  have hxn : x ∉ (l.drop k).toFinset := by
    intro h
    rw [List.mem_toFinset] at h
    have := ((mem_evL X.F j x x).mp (List.mem_of_mem_drop h)).2.2
    exact lt_irrefl _ this
  have hsub : insert x (l.drop k).toFinset ⊆ (Finset.range r).image (fun i => X.F.fr j i) := by
    intro y hy
    rw [Finset.mem_image]
    rw [Finset.mem_insert, List.mem_toFinset] at hy
    rcases hy with rfl | hy
    · obtain ⟨i, hi, he⟩ := frame y hx.1 (le_trans hge (le_of_lt hmem.2.2))
      exact ⟨i, Finset.mem_range.mpr hi, he⟩
    · have hyl := (mem_evL X.F j x y).mp (List.mem_of_mem_drop hy)
      obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.mp hy
      have hm' : k + m < l.length := by
        rw [hdl] at hm
        omega
      have hge2 : l[k]'hk ≤ (l.drop k)[m] := by
        rw [List.getElem_drop]
        exact evL_mono X.F j x (Nat.le_add_right k m) hm'
      obtain ⟨i, hi, he⟩ := frame _ hyl.1 (le_trans hge hge2)
      exact ⟨i, Finset.mem_range.mpr hi, he⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hxn, List.toFinset_card_of_nodup hnd, hdl] at hc
  have hc2 := Finset.card_image_le (s := Finset.range r) (f := fun i => X.F.fr j i)
  rw [Finset.card_range] at hc2
  omega

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.AllowedLettersOfLateRows
noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

theorem detPl_supported (R : Type) [CommRing R] [Nontrivial R] {n' r : ℕ} [NeZero n'] (X : Dat n' r) (j x : ℤ)
    (s : Set (ℤ × Fin r)) (h : ∀ a b, (X.row j x a, b) ∈ s) : X.detPl R j x ∈ supported R s := by
  unfold Dat.detPl
  rw [Matrix.det_apply]
  refine sum_mem fun σ _ => ?_
  rw [Units.smul_def]
  refine zsmul_mem (prod_mem fun i _ => ?_) _
  rw [Matrix.of_apply]
  exact (MvPolynomial.X_mem_supported).2 (h _ _)

theorem DlSeg_supported (R : Type) [CommRing R] [Nontrivial R] {n' r : ℕ} [NeZero n'] (X : Dat n' r) (p K : ℕ) (j : ℤ)
    (s : Set (ℤ × Fin r)) (h : ∀ x ∈ X.toLate j, ∀ a b, (X.row j x a, b) ∈ s) : X.DlSeg p K R j ∈ supported R s := by
  unfold Dat.DlSeg
  exact prod_mem fun x hx => pow_mem (detPl_supported R X j x s (h x hx)) _

theorem ellP_supported (R : Type) [CommRing R] [Nontrivial R] {n' r : ℕ} [NeZero n'] (X : Dat n' r) (K : ℕ) (j : ℤ)
    (e : ℤ × Fin (r + K) →₀ ℕ) (s : Set (ℤ × Fin r)) (h : ∀ x ∈ X.toLate j, ∀ b, (x, b) ∈ s) :
    X.ellP K R j e ∈ supported R s := by
  unfold Dat.ellP
  exact prod_mem fun x hx => prod_mem fun c _ => pow_mem ((MvPolynomial.X_mem_supported).2 (h x hx c)) _

theorem ellN_supported (R : Type) [CommRing R] [Nontrivial R] {n' r : ℕ} [NeZero n'] (X : Dat n' r) (K : ℕ) (j : ℤ)
    (e : ℤ × Fin (r + K) →₀ ℕ) (s : Set (ℤ × Fin K)) (h : ∀ x ∈ X.toLate j, ∀ b, (x, b) ∈ s) :
    X.ellN K R j e ∈ supported R s := by
  unfold Dat.ellN
  exact prod_mem fun x hx => prod_mem fun c _ => pow_mem ((MvPolynomial.X_mem_supported).2 (h x hx c)) _

theorem allowed_letters_of_late_rows (D : Formalism.BasicNotions.D7) (hA3 : Formalism.MainNotions.CovariantDegrees.DefiniteRankOne D) (C₀ : ℝ) (hRow : LateIndexInjective) : ProductAllowedLetters C₀ := by
  intro p n' r K _ _ _ X O _ _ _ S j b e q I' I'' hW
  classical
  have hX := hW.hX
  haveI : Fact p.Prime := ⟨hX.prime⟩
  have hlet : ∀ i : Fin (segN X.F j), segE X.F j i ∈ X.F.letters j := fun i =>
    ((X.F.letters j).orderIsoOfFin rfl i).2
  have hren : ∀ {k : ℕ} (P : MvPolynomial (Fin (segN X.F j) × Fin k) (FF O)) (s : Set (ℤ × Fin k)),
      (∀ v ∈ P.vars, (segE X.F j v.1, v.2) ∈ s) → segRen X.F j (FF O) k P ∈ supported (FF O) s := by
    intro k P s hs
    rw [MvPolynomial.mem_supported]
    intro v hv
    unfold segRen at hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 (MvPolynomial.vars_rename _ P hv)
    exact hs w hw
  obtain ⟨b', b'', ⟨P1, hP1⟩, ⟨P2, hP2⟩, hcond⟩ := hW.hq
  refine ⟨?_, ?_⟩
  · unfold Dat.Aw
    refine mul_mem (mul_mem (pow_mem (hren _ _ fun v _ => hlet v.1) _) ?_) ?_
    · exact ellP_supported (FF O) X K j e _ fun x hx c => (Finset.mem_filter.1 hx).1
    · exact DlSeg_supported (FF O) X p K j _ fun x hx a c => ((hRow p n' r K X hX j x hx).2 a).1
  · unfold Dat.Gw
    have hA := (hA3 p O S (segN X.F j) K (segLL X.F j) b'' (fun i => q.2 i.succ (lastIdx K))
      (fun i => q.2 i.succ 0)).2
    have hPol : Psi (FF O) q.2 I'' ∈ Pol (FF O) K b'' :=
      ((Set.ext_iff.1 hA _).2 (Submodule.subset_span ⟨P2, I'', by rw [hP2]; exact hW.hI'',
        fun i => by rw [hP2]; exact ⟨le_rfl, le_rfl⟩, by rw [hP2]⟩)).1
    have hseg : segRen X.F j (FF O) K (Psi (FF O) q.2 I'') ∈
        supported (FF O) {v : ℤ × Fin K | v.1 ∈ X.F.letters j ∧ ¬ X.F.IsW j v.1} := by
      refine hren _ _ fun v hv => ⟨hlet v.1, fun hWv => ?_⟩
      obtain ⟨m, hm, hvm⟩ := (MvPolynomial.mem_vars_iff_mem_support _).1 hv
      have hb0 : b'' v.1 = 0 := (hcond v.1).1 hWv
      have hsum : multideg m v.1 = b'' v.1 := ((MvPolynomial.mem_restrictSupport_iff _).1 hPol) hm v.1
      rw [hb0] at hsum
      have h0 : m (v.1, v.2) = 0 := Finset.sum_eq_zero_iff.1 hsum v.2 (Finset.mem_univ _)
      exact (Finsupp.mem_support_iff.1 hvm) h0
    refine mul_mem (pow_mem hseg _) ?_
    exact ellN_supported (FF O) X K j e _ fun x hx c =>
      ⟨(Finset.mem_filter.1 hx).1, (Finset.mem_filter.1 hx).2⟩

def DegAt {R : Type} [CommRing R] {ι : Type} {n : ℕ} (x : ι) (d : ℕ) (P : MvPolynomial (ι × Fin n) R) : Prop :=
  ∀ m ∈ P.support, multideg m x = d

section DegAt

variable {R : Type} [CommRing R] {ι : Type} {n : ℕ} {x : ι}

theorem degAt_mul {d d' : ℕ} {P Q : MvPolynomial (ι × Fin n) R} (hP : DegAt x d P) (hQ : DegAt x d' Q) :
    DegAt x (d + d') (P * Q) := by
  classical
  intro m hm
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 (MvPolynomial.support_mul P Q hm)
  simp only [multideg, Finsupp.add_apply, Finset.sum_add_distrib]
  exact congrArg₂ (· + ·) (hP a ha) (hQ b hb)

theorem degAt_one : DegAt x 0 (1 : MvPolynomial (ι × Fin n) R) := by
  classical
  intro m hm
  have h0 : m = 0 := by
    by_contra hne
    exact (MvPolynomial.mem_support_iff.1 hm) (by rw [MvPolynomial.coeff_one, if_neg (Ne.symm hne)])
  subst h0
  simp [multideg]

theorem degAt_pow {d : ℕ} {P : MvPolynomial (ι × Fin n) R} (hP : DegAt x d P) (k : ℕ) : DegAt x (k * d) (P ^ k) := by
  induction k with
  | zero => rw [pow_zero, zero_mul]; exact degAt_one
  | succ k ih => rw [pow_succ, add_mul, one_mul]; exact degAt_mul ih hP

theorem degAt_prod {κ : Type} (s : Finset κ) (f : κ → MvPolynomial (ι × Fin n) R) (d : κ → ℕ)
    (h : ∀ i ∈ s, DegAt x (d i) (f i)) : DegAt x (∑ i ∈ s, d i) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.sum_empty]; exact degAt_one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact degAt_mul (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem degAt_X [DecidableEq ι] (v : ι × Fin n) : DegAt x (if v.1 = x then 1 else 0) (X v : MvPolynomial (ι × Fin n) R) := by
  classical
  intro m hm
  have h0 : Finsupp.single v 1 = m := by
    by_contra hne
    exact (MvPolynomial.mem_support_iff.1 hm) (by rw [MvPolynomial.coeff_X', if_neg hne])
  subst h0
  obtain ⟨a, c0⟩ := v
  by_cases ha : a = x
  · subst ha
    simp [multideg, Finsupp.single_apply, Prod.ext_iff]
  · simp [multideg, Finsupp.single_apply, Prod.ext_iff, ha]

theorem degAt_of_supported {P : MvPolynomial (ι × Fin n) R} (s : Set (ι × Fin n)) (hP : P ∈ supported R s)
    (hs : ∀ v ∈ s, v.1 ≠ x) : DegAt x 0 P := by
  intro m hm
  rw [MvPolynomial.mem_supported] at hP
  show ∑ c, m (x, c) = 0
  refine Finset.sum_eq_zero fun c _ => ?_
  by_contra hne
  have hv : (x, c) ∈ P.vars := (MvPolynomial.mem_vars_iff_mem_support _).2 ⟨m, hm, Finsupp.mem_support_iff.2 hne⟩
  exact hs _ (hP hv) rfl

end DegAt

theorem degAt_segRen {R : Type} [CommRing R] {n' r : ℕ} [NeZero n'] (F : Frames n' r) (j : ℤ) {n : ℕ}
    {b : Fin (segN F j) → ℕ} {A : MvPolynomial (Fin (segN F j) × Fin n) R} (hA : A ∈ Pol R n b) (i : Fin (segN F j)) :
    DegAt (segE F j i) (b i) (segRen F j R n A) := by
  classical
  have hinj : Function.Injective (fun v : Fin (segN F j) × Fin n => (segE F j v.1, v.2)) := by
    rintro ⟨a, c⟩ ⟨a', c'⟩ h
    simp only [Prod.mk.injEq] at h
    have ha : a = a' := ((F.letters j).orderIsoOfFin rfl).injective (Subtype.ext (by exact h.1))
    rw [ha, h.2]
  intro m hm
  unfold segRen at hm
  rw [MvPolynomial.support_rename_of_injective hinj, Finset.mem_image] at hm
  obtain ⟨m0, hm0, rfl⟩ := hm
  have h0 := ((MvPolynomial.mem_restrictSupport_iff _).1 hA) hm0
  show ∑ c, (Finsupp.mapDomain _ m0) (segE F j i, c) = b i
  rw [← h0 i]
  exact Finset.sum_congr rfl fun c _ => Finsupp.mapDomain_apply_of_injective hinj m0 (i, c)

theorem ordDeg_prod {R : Type} [CommRing R] {r K : ℕ} {x : ℤ} {dA dG : ℕ} {A : MvPolynomial (ℤ × Fin r) R}
    {G : MvPolynomial (ℤ × Fin K) R} (hA : ¬ Even x → DegAt x dA A) (hG : Even x → DegAt x dG G) :
    ∀ mm ∈ (plEmb R r K A * nmEmb R r K G).support, ordDeg mm x = if Even x then dG else dA := by
  classical
  intro mm hmm
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 (MvPolynomial.support_mul _ _ hmm)
  have hi1 : Function.Injective (fun v : ℤ × Fin r => (v.1, Fin.castAdd K v.2)) := by
    rintro ⟨u1, u2⟩ ⟨w1, w2⟩ h
    simp only [Prod.mk.injEq, Fin.castAdd_inj] at h
    rw [h.1, h.2]
  have hi2 : Function.Injective (fun v : ℤ × Fin K => (v.1, Fin.natAdd r v.2)) := by
    rintro ⟨u1, u2⟩ ⟨w1, w2⟩ h
    simp only [Prod.mk.injEq, Fin.natAdd_inj] at h
    rw [h.1, h.2]
  unfold plEmb at ha
  unfold nmEmb at hb
  rw [MvPolynomial.support_rename_of_injective hi1, Finset.mem_image] at ha
  rw [MvPolynomial.support_rename_of_injective hi2, Finset.mem_image] at hb
  obtain ⟨a0, ha0, rfl⟩ := ha
  obtain ⟨b0, hb0, rfl⟩ := hb
  unfold ordDeg
  split_ifs with hx
  · have h1 : ∀ c : Fin K, (Finsupp.mapDomain (fun v : ℤ × Fin r => (v.1, Fin.castAdd K v.2)) a0)
        (x, Fin.natAdd r c) = 0 := fun c => by
      refine Finsupp.mapDomain_notin_range _ _ ?_
      rintro ⟨⟨y, d⟩, h⟩
      simp only [Prod.mk.injEq] at h
      have := congrArg Fin.val h.2
      simp only [Fin.coe_castAdd, Fin.coe_natAdd] at this
      omega
    simp only [Finsupp.add_apply, Finset.sum_add_distrib, h1, Finset.sum_const_zero, zero_add]
    rw [← hG hx b0 hb0]
    exact Finset.sum_congr rfl fun c _ => Finsupp.mapDomain_apply_of_injective hi2 b0 (x, c)
  · have h1 : ∀ c : Fin r, (Finsupp.mapDomain (fun v : ℤ × Fin K => (v.1, Fin.natAdd r v.2)) b0)
        (x, Fin.castAdd K c) = 0 := fun c => by
      refine Finsupp.mapDomain_notin_range _ _ ?_
      rintro ⟨⟨y, d⟩, h⟩
      simp only [Prod.mk.injEq] at h
      have := congrArg Fin.val h.2
      simp only [Fin.coe_castAdd, Fin.coe_natAdd] at this
      omega
    simp only [Finsupp.add_apply, Finset.sum_add_distrib, h1, Finset.sum_const_zero, add_zero]
    rw [← hA hx a0 ha0]
    exact Finset.sum_congr rfl fun c _ => Finsupp.mapDomain_apply_of_injective hi1 a0 (x, c)

end Formalism.MainNotions.SelectionLemmas.Pf
end
end
