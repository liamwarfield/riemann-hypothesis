module

public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.DplusLeBeA
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.TypicalPathOrdersSmall
public import Formalism.ThetaLogCoordinates.ResidueClassEstimates.FinalT

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.ProdIccOneEqProdRange
section -- merged from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.CountFromEqFilterLength
noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf.T

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas
open Formalism.InvariantFactorPaths

theorem filter_ge_get_eq_take : ∀ (L : List ℕ), L.Pairwise (· > ·) → ∀ (e : ℕ) (he : e < L.length),
    L.filter (fun y => decide (L[e] ≤ y)) = L.take (e + 1) := by
  intro L
  induction L with
  | nil => intro _ e he; simp at he
  | cons x xs ih =>
    intro hp e he
    rw [List.pairwise_cons] at hp
    cases e with
    | zero =>
      simp only [List.getElem_cons_zero, List.take_succ_cons, List.take_zero]
      rw [List.filter_cons_of_pos (by simp)]
      congr 1
      rw [List.filter_eq_nil_iff]
      intro y hy
      have h1 := hp.1 y hy
      simp only [decide_eq_true_eq, not_le]
      omega
    | succ e =>
      simp only [List.getElem_cons_succ, List.take_succ_cons]
      have hlt : xs[e]'(by simp at he; omega) < x := hp.1 _ (List.getElem_mem _)
      rw [List.filter_cons_of_pos (by simp only [decide_eq_true_eq]; omega),
        ih hp.2 e (by simp at he; omega)]

def latestList (P : ℕ → Bool) (M : ℕ) : List ℕ := ((List.range' 1 M).filter P).reverse

theorem mem_latest_list (P : ℕ → Bool) (M y : ℕ) : y ∈ latestList P M ↔ (1 ≤ y ∧ y ≤ M) ∧ P y = true := by
  simp only [latestList, List.mem_reverse, List.mem_filter, List.mem_range'_1]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1.1, by omega⟩, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1.1, by omega⟩, h2⟩

theorem latest_list_pairwise_gt (P : ℕ → Bool) (M : ℕ) : (latestList P M).Pairwise (· > ·) := by
  rw [latestList, List.pairwise_reverse]
  exact (List.pairwise_lt_range' (s := 1) (n := M)).filter _

theorem latest_list_nodup (P : ℕ → Bool) (M : ℕ) : (latestList P M).Nodup :=
  (latest_list_pairwise_gt P M).imp ne_of_gt

def countFrom (P : ℕ → Bool) (M x : ℕ) : ℕ := ((Finset.Icc 1 M).filter fun y => P y = true ∧ x ≤ y).card

theorem count_from_eq_filter_length (P : ℕ → Bool) (M x : ℕ) :
    countFrom P M x = ((latestList P M).filter fun y => decide (x ≤ y)).length := by
  unfold countFrom
  have hnd : ((latestList P M).filter fun y => decide (x ≤ y)).Nodup := (latest_list_nodup P M).filter _
  rw [← List.toFinset_card_of_nodup hnd]
  congr 1
  ext y
  simp only [Finset.mem_filter, Finset.mem_Icc, List.mem_toFinset, List.mem_filter, mem_latest_list,
    decide_eq_true_eq]
  tauto

theorem latest_list_get_spec (P : ℕ → Bool) (M e : ℕ) (he : e < (latestList P M).length) :
    ((1 ≤ (latestList P M)[e] ∧ (latestList P M)[e] ≤ M) ∧ P (latestList P M)[e] = true) ∧
      countFrom P M (latestList P M)[e] = e + 1 := by
  refine ⟨(mem_latest_list P M _).1 (List.getElem_mem _), ?_⟩
  rw [count_from_eq_filter_length, filter_ge_get_eq_take _ (latest_list_pairwise_gt P M) e he, List.length_take]
  omega

theorem latest_list_get_of_count (P : ℕ → Bool) (M e x : ℕ) (hx : (1 ≤ x ∧ x ≤ M) ∧ P x = true) (hc : countFrom P M x = e + 1) :
    ∃ he : e < (latestList P M).length, (latestList P M)[e] = x := by
  obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.1 ((mem_latest_list P M x).2 hx)
  have h1 := (latest_list_get_spec P M i hi).2
  rw [hix, hc] at h1
  have hie : i = e := by omega
  subst hie
  exact ⟨hi, hix⟩

theorem latest_list_succ_lt (P : ℕ → Bool) (M e : ℕ) (he : e + 1 < (latestList P M).length) :
    (latestList P M)[e + 1] < (latestList P M)[e]'(by omega) := by
  exact List.pairwise_iff_getElem.1 (latest_list_pairwise_gt P M) e (e + 1) (by omega) he (by omega)

variable {N r K : ℕ}

def toL (r K : ℕ) (LL : Letters (Fin N)) (B : Fin N → ℕ) : BranchingDimensions.Letters where
  r := r
  K := K
  Ns := N
  vec := fun i => if h : 1 ≤ i ∧ i ≤ N then LL.vec ⟨i - 1, by omega⟩ else true
  B := fun i => if h : 1 ≤ i ∧ i ≤ N then B ⟨i - 1, by omega⟩ else 0

theorem toL_vec (LL : Letters (Fin N)) (B : Fin N → ℕ) (i : ℕ) (h : 1 ≤ i ∧ i ≤ N) :
    (toL r K LL B).vec i = LL.vec ⟨i - 1, by omega⟩ := by
  simp only [toL]
  rw [dite_eq_left h]

theorem toL_B (LL : Letters (Fin N)) (B : Fin N → ℕ) (i : ℕ) (h : 1 ≤ i ∧ i ≤ N) :
    (toL r K LL B).B i = B ⟨i - 1, by omega⟩ := by
  simp only [toL]
  rw [dite_eq_left h]

section
variable {n0 : ℕ} {LL : Letters (Fin N)} {B : Fin N → ℕ} {od : Fin N → Fin N} {bb : Fin N → ℝ} {a La : ℝ} {p : ℕ}

theorem letters_n0_eq (H : HypT N n0 r K LL B od bb a La p) : (toL r K LL B).n0 = n0 := by
  show N - r = n0
  have := H.hN
  omega

theorem toL_Wf [NeZero K] (H : HypT N n0 r K LL B od bb a La p) : (toL r K LL B).Wf := by
  have hn0 := letters_n0_eq (r := r) (K := K) H
  have hN := H.hN
  have h3 := H.two_r_le_n0
  refine ⟨H.r1, Nat.one_le_iff_ne_zero.2 (NeZero.ne K), ?_, fun i h1 h2 => ?_, fun i h1 h2 => ?_⟩
  · show 3 * r ≤ N
    omega
  · simp only [toL] at h2
    rw [toL_vec LL B i ⟨h1, by omega⟩]
    exact H.vec_true_of_early _ (by simp only; omega)
  · rw [hn0] at h1
    simp only [toL] at h2
    rw [toL_vec LL B i ⟨by omega, h2⟩]
    exact H.vec_true_of_late _ (by simp only; omega)

theorem latest_thresholds_decay (H : HypT N n0 r K LL B od bb a La p) (P : ℕ → Bool) (v : Bool)
    (hP : ∀ i (h : 1 ≤ i ∧ i ≤ N), P i = true → LL.vec ⟨i - 1, by omega⟩ = v) (l : ℕ)
    (hl : l + 1 < ((latestList P n0).map (toL r K LL B).B).length) :
    13 ^ 2 * ((latestList P n0).map (toL r K LL B).B).getD (l + 1) 0 ≤
      5 * ((latestList P n0).map (toL r K LL B).B).getD l 0 := by
  have hlen : l + 1 < (latestList P n0).length := by simpa using hl
  have e1 : ((latestList P n0).map (toL r K LL B).B).getD (l + 1) 0 =
      (toL r K LL B).B ((latestList P n0)[l + 1]) := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem, hlen]
  have e2 : ((latestList P n0).map (toL r K LL B).B).getD l 0 =
      (toL r K LL B).B ((latestList P n0)[l]'(by omega)) := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem, show l < (latestList P n0).length by omega]
  rw [e1, e2]
  have hxy := latest_list_succ_lt P n0 l hlen
  have hxs := (latest_list_get_spec P n0 (l + 1) hlen).1
  have hys := (latest_list_get_spec P n0 l (by omega)).1
  generalize (latestList P n0)[l + 1] = x at hxy hxs ⊢
  generalize (latestList P n0)[l]'(by omega) = y at hxy hys ⊢
  have hN := H.hN
  rw [toL_B LL B x ⟨hxs.1.1, by omega⟩, toL_B LL B y ⟨hys.1.1, by omega⟩]
  have hv : LL.vec ⟨x - 1, by omega⟩ = LL.vec ⟨y - 1, by omega⟩ := by
    rw [hP x ⟨hxs.1.1, by omega⟩ hxs.2, hP y ⟨hys.1.1, by omega⟩ hys.2]
  have h2 := H.H2 ⟨x - 1, by omega⟩ ⟨y - 1, by omega⟩
    (by rw [Fin.lt_iff_val_lt_val]; simp only; omega) (by simp only; omega) hv
  have hp13 : (13 : ℝ) ≤ p := by exact_mod_cast H.p13
  have hB0 : (0 : ℝ) ≤ (B ⟨x - 1, by omega⟩ : ℝ) := Nat.cast_nonneg _
  have h3 : ((13 ^ 2 * B ⟨x - 1, by omega⟩ : ℕ) : ℝ) ≤ ((5 * B ⟨y - 1, by omega⟩ : ℕ) : ℝ) := by
    push_cast
    have hp2 : (169 : ℝ) ≤ (p : ℝ) ^ 2 := by nlinarith
    have h8 := mul_le_mul_of_nonneg_right hp2 hB0
    linarith
  exact_mod_cast h3

theorem toL_Hyp [NeZero K] (H : HypT N n0 r K LL B od bb a La p) : (toL r K LL B).Hyp a 13 := by
  have hn0 := letters_n0_eq (r := r) (K := K) H
  have hN := H.hN
  have h3n := H.two_r_le_n0
  have h3K := H.N_add_r_le_K
  have h4 := H.H4
  have h4a := H.N_le_a
  have eV : (toL r K LL B).latestV (toL r K LL B).n0 =
      (latestList (fun l => (toL r K LL B).vec l) n0).map (toL r K LL B).B := by
    simp only [BranchingDimensions.Letters.latestV, latestList, hn0, min_self]
  have eC : (toL r K LL B).latestC (toL r K LL B).n0 =
      (latestList (fun l => !(toL r K LL B).vec l) n0).map (toL r K LL B).B := by
    simp only [BranchingDimensions.Letters.latestC, latestList, hn0, min_self]
  refine ⟨H.a3, by norm_num, le_rfl, fun i h1 h2 => ?_, fun l hl => ?_, fun l hl => ?_,
    fun i h1 h2 => ?_, ?_, ?_, ?_, ?_⟩
  · rw [hn0] at h2
    rw [toL_B LL B i ⟨h1, by omega⟩]
    have h5 := H.H1 ⟨i - 1, by omega⟩ (by simp only; omega)
    refine ⟨?_, h5.2⟩
    show r + K ≤ B ⟨i - 1, by omega⟩
    exact_mod_cast h5.1
  · rw [eV] at hl ⊢
    exact latest_thresholds_decay H _ true (fun i hi hPi => by rw [← toL_vec LL B i hi]; exact hPi) l hl
  · rw [eC] at hl ⊢
    exact latest_thresholds_decay H _ false (fun i hi hPi => by
      rw [← toL_vec LL B i hi]
      simpa using hPi) l hl
  · rw [hn0] at h1 h2
    simp only [toL] at h1
    rw [toL_vec LL B i ⟨by omega, by omega⟩]
    exact H.vec_true_of_late _ (by simp only; omega)
  · show N + r ≤ K
    omega
  · show 2 * r ≤ N
    omega
  · show r + K ≤ 2 * (K - 2 * N)
    have hK : 2 * N ≤ K := by
      have h6 : (2 * N : ℝ) ≤ K := by
        have : (0 : ℝ) ≤ ((r + K : ℕ) : ℝ) := Nat.cast_nonneg _
        linarith
      exact_mod_cast h6
    have h7 : ((r + K : ℕ) : ℝ) ≤ ((2 * (K - 2 * N) : ℕ) : ℝ) := by
      rw [Nat.cast_mul, Nat.cast_sub hK]
      push_cast at h4 ⊢
      linarith
    exact_mod_cast h7
  · show (N : ℝ) ≤ a
    exact h4a

def toB (bb : Fin N → ℝ) (p : ℕ) : ℕ → ℝ := fun i =>
  if h : 1 ≤ i ∧ i ≤ N then 13 * bb ⟨i - 1, by omega⟩ / (p : ℝ) else 1

theorem toL_TData (H : HypT N n0 r K LL B od bb a La p) : (toL r K LL B).TData 13 La (toB bb p) := by
  have hN := H.hN
  have hp : (0 : ℝ) < p := by
    have := H.p13
    exact_mod_cast (by omega : 0 < p)
  refine ⟨H.La_pos, fun i h1 h2 => ?_⟩
  simp only [toL] at h1 h2
  have hi : 1 ≤ i ∧ i ≤ N := ⟨by omega, h2⟩
  have hb : toB bb p i = 13 * bb ⟨i - 1, by omega⟩ / (p : ℝ) := by
    simp only [toB]
    rw [dite_eq_left hi]
  refine ⟨?_, fun l hl1 hl2 hl3 => ?_⟩
  · rw [hb]
    have := H.bb_pos ⟨i - 1, by omega⟩ (by simp only; omega)
    positivity
  · rw [letters_n0_eq H] at hl3
    rw [toL_B LL B l ⟨hl1, by omega⟩, hb]
    have h5 := H.bb_le ⟨i - 1, by omega⟩ ⟨l - 1, by omega⟩ (by simp only; omega)
      (by rw [Fin.lt_iff_val_lt_val]; simp only; omega) (by simp only; omega)
    refine le_trans h5 (le_of_eq ?_)
    push_cast
    ring

end

end Formalism.MainNotions.SelectionLemmas.Pf.T
end
end

noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf.T

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas
open Formalism.InvariantFactorPaths

variable {N r K : ℕ}

theorem entry_eq_of_lt (LL : Letters (Fin N)) (B : Fin N → ℕ) (μ : Fin (N + 1) → Fin (r + K) → ℤ) (s m : ℕ)
    (hs : s < N + 1) (hm : m < r + K) :
    BranchingDimensions.Letters.ent (D := toL r K LL B) μ s m = μ ⟨s, hs⟩ ⟨m, hm⟩ :=
  dif_pos (⟨hs, hm⟩ : s < N + 1 ∧ m < r + K)

theorem entry_eq_zero_of_ge (LL : Letters (Fin N)) (B : Fin N → ℕ) (μ : Fin (N + 1) → Fin (r + K) → ℤ) (s m : ℕ)
    (hm : ¬ m < r + K) : BranchingDimensions.Letters.ent (D := toL r K LL B) μ s m = 0 :=
  dif_neg (fun h : s < N + 1 ∧ m < r + K => hm h.2)

theorem sum_Icc_one_eq_sum_range {M : Type} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ i ∈ Finset.Icc 1 n, f i = ∑ m ∈ Finset.range n, f (m + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

theorem prod_Icc_one_eq_prod_range {M : Type} [CommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∏ i ∈ Finset.Icc 1 n, f i = ∏ m ∈ Finset.range n, f (m + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.prod_Icc_succ_top (by omega), ih, Finset.prod_range_succ]

theorem prod_fin_ite_lt_eq {M : Type} [CommMonoid M] (n j : ℕ) (hj : j ≤ n) (h : ℕ → M) :
    ∏ i : Fin n, (if i.val < j then h i.val else 1) = ∏ i ∈ Finset.range j, h i := by
  rw [Fin.prod_univ_eq_prod_range (fun m => if m < j then h m else 1) n]
  rw [← Finset.prod_subset (Finset.range_subset_range.mpr hj)]
  · refine Finset.prod_congr rfl fun m hm => ?_
    rw [if_pos (Finset.mem_range.mp hm)]
  · intro m _ hm
    rw [if_neg (by simpa using hm)]

theorem sum_fin_ite_lt_eq {M : Type} [AddCommMonoid M] (n j : ℕ) (hj : j ≤ n) (h : ℕ → M) :
    ∑ i : Fin n, (if i.val < j then h i.val else 0) = ∑ i ∈ Finset.range j, h i := by
  rw [Fin.sum_univ_eq_sum_range (fun m => if m < j then h m else 0) n]
  rw [← Finset.sum_subset (Finset.range_subset_range.mpr hj)]
  · refine Finset.sum_congr rfl fun m hm => ?_
    rw [if_pos (Finset.mem_range.mp hm)]
  · intro m _ hm
    rw [if_neg (by simpa using hm)]

theorem beta_eq_sum_thresholds (LL : Letters (Fin N)) (B : Fin N → ℕ) (n0 : ℕ) (hn : n0 ≤ N) :
    ∑ i ∈ Finset.Icc 1 n0, (toL r K LL B).B i = beA n0 B := by
  unfold beA
  rw [sum_Icc_one_eq_sum_range, ← sum_fin_ite_lt_eq N n0 hn (fun m => (toL r K LL B).B (m + 1))]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : i.val < n0
  · rw [if_pos hi, if_pos hi, toL_B LL B (i.val + 1) ⟨by omega, by have := i.2; omega⟩]
    congr 1
  · rw [if_neg hi, if_neg hi]

theorem rank_eq_prod_choose (LL : Letters (Fin N)) (B : Fin N → ℕ) (n0 : ℕ) (hn : n0 ≤ N) :
    ∏ i ∈ Finset.Icc 1 n0, ((toL r K LL B).B i + (r + K) - 1).choose (r + K - 1) = rkA r K n0 B := by
  unfold rkA
  rw [prod_Icc_one_eq_prod_range, ← prod_fin_ite_lt_eq N n0 hn (fun m => ((toL r K LL B).B (m + 1) + (r + K) - 1).choose (r + K - 1))]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hi : i.val < n0
  · rw [if_pos hi, if_pos hi, toL_B LL B (i.val + 1) ⟨by omega, by have := i.2; omega⟩]
    congr 3
  · rw [if_neg hi, if_neg hi]

theorem entry_weight_eq_sum (LL : Letters (Fin N)) (B : Fin N → ℕ) (μ : Fin (N + 1) → Fin (r + K) → ℤ) (s : ℕ) (hs : s < N + 1) :
    BranchingDimensions.wsize (r + K) (BranchingDimensions.Letters.ent (D := toL r K LL B) μ s) = ∑ m : Fin (r + K), μ ⟨s, hs⟩ m := by
  unfold BranchingDimensions.wsize
  rw [Finset.sum_range]
  exact Finset.sum_congr rfl fun m _ => entry_eq_of_lt LL B μ s m.val hs m.2

section
variable {n0 : ℕ} {LL : Letters (Fin N)} {B : Fin N → ℕ} {od : Fin N → Fin N} {bb : Fin N → ℝ} {a La : ℝ} {p : ℕ}

theorem toL_IsPATH (H : HypT N n0 r K LL B od bb a La p) {dd : Fin N → ℕ} (P : PPath (r + K) N LL dd)
    (hP : IsPATHa LL n0 B P.mu dd) : (toL r K LL B).IsPATH P.mu := by
  have hN := H.hN
  have hn0 := letters_n0_eq (r := r) (K := K) H
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m
    by_cases hm : m < r + K
    · rw [entry_eq_of_lt LL B P.mu 0 m (by omega) hm]
      have h0 : (⟨0, by omega⟩ : Fin (N + 1)) = 0 := rfl
      rw [h0, P.zero]; rfl
    · exact entry_eq_zero_of_ge LL B P.mu 0 m hm
  · intro i hi m hm
    have hi' : i ≤ N := hi
    have hm' : m + 1 < r + K := hm
    rw [entry_eq_of_lt LL B P.mu i (m + 1) (by omega) hm', entry_eq_of_lt LL B P.mu i m (by omega) (by omega)]
    exact P.dom _ (by rw [Fin.le_def]; simp)
  · intro i h1 h2 hv
    obtain ⟨i0, rfl⟩ : ∃ i0, i = i0 + 1 := ⟨i - 1, by omega⟩
    have h2' : i0 + 1 ≤ N := h2
    rw [toL_vec LL B (i0 + 1) ⟨h1, h2'⟩] at hv
    have hs := step_vec P ⟨i0, by omega⟩ hv
    rw [Nat.add_sub_cancel]
    refine ⟨fun m hm => ?_, fun m hm => ?_⟩
    · have hm' : m < r + K := hm
      rw [entry_eq_of_lt LL B P.mu i0 m (by omega) hm', entry_eq_of_lt LL B P.mu (i0 + 1) m (by omega) hm']
      exact hs.1 ⟨m, hm'⟩
    · have hm' : m + 1 < r + K := hm
      rw [entry_eq_of_lt LL B P.mu i0 m (by omega) (by omega), entry_eq_of_lt LL B P.mu (i0 + 1) (m + 1) (by omega) hm']
      exact hs.2.1 ⟨m, by omega⟩ hm'
  · intro i h1 h2 hv
    obtain ⟨i0, rfl⟩ : ∃ i0, i = i0 + 1 := ⟨i - 1, by omega⟩
    have h2' : i0 + 1 ≤ N := h2
    rw [toL_vec LL B (i0 + 1) ⟨h1, h2'⟩] at hv
    have hs := step_cov P ⟨i0, by omega⟩ hv
    rw [Nat.add_sub_cancel]
    refine ⟨fun m hm => ?_, fun m hm => ?_⟩
    · have hm' : m < r + K := hm
      rw [entry_eq_of_lt LL B P.mu i0 m (by omega) hm', entry_eq_of_lt LL B P.mu (i0 + 1) m (by omega) hm']
      exact hs.1 ⟨m, hm'⟩
    · have hm' : m + 1 < r + K := hm
      rw [entry_eq_of_lt LL B P.mu (i0 + 1) m (by omega) (by omega), entry_eq_of_lt LL B P.mu i0 (m + 1) (by omega) hm']
      exact hs.2.1 ⟨m, by omega⟩ hm'
  · intro i h1 h2 hv
    obtain ⟨i0, rfl⟩ : ∃ i0, i = i0 + 1 := ⟨i - 1, by omega⟩
    rw [hn0] at h2
    rw [toL_vec LL B (i0 + 1) ⟨h1, by omega⟩] at hv
    have hs := step_vec P ⟨i0, by omega⟩ hv
    rw [Nat.add_sub_cancel, toL_B LL B (i0 + 1) ⟨h1, by omega⟩]
    show BranchingDimensions.wsize (r + K) _ - BranchingDimensions.wsize (r + K) _ = _
    rw [entry_weight_eq_sum LL B P.mu (i0 + 1) (by omega), entry_weight_eq_sum LL B P.mu i0 (by omega), ← Finset.sum_sub_distrib]
    have := hs.2.2
    rw [hP.degs ⟨i0, by omega⟩ (by simp only; omega)] at this
    exact this
  · intro i h1 h2 hv
    obtain ⟨i0, rfl⟩ : ∃ i0, i = i0 + 1 := ⟨i - 1, by omega⟩
    rw [hn0] at h2
    rw [toL_vec LL B (i0 + 1) ⟨h1, by omega⟩] at hv
    have hs := step_cov P ⟨i0, by omega⟩ hv
    rw [Nat.add_sub_cancel, toL_B LL B (i0 + 1) ⟨h1, by omega⟩]
    show BranchingDimensions.wsize (r + K) _ - BranchingDimensions.wsize (r + K) _ = _
    rw [entry_weight_eq_sum LL B P.mu (i0 + 1) (by omega), entry_weight_eq_sum LL B P.mu i0 (by omega), ← Finset.sum_sub_distrib]
    have := hs.2.2
    rw [hP.degs ⟨i0, by omega⟩ (by simp only; omega)] at this
    exact this
  · intro i' h1 h2 m hm
    have h2' : i' ≤ r := h2
    rw [hn0, entry_eq_of_lt LL B P.mu (n0 + i') m (by omega) (by omega)]
    have := hP.head ⟨n0 + i' - 1, by omega⟩ ⟨m, by omega⟩ (by simp only; omega) (by simp only; omega)
    have he : (⟨n0 + i' - 1, by omega⟩ : Fin N).succ = (⟨n0 + i', by omega⟩ : Fin (N + 1)) :=
      Fin.ext (by simp; omega)
    rw [he] at this
    rw [this]
    congr 1
    show beA n0 B = ∑ i ∈ Finset.Icc 1 (toL r K LL B).n0, (toL r K LL B).B i
    rw [hn0, beta_eq_sum_thresholds LL B n0 (by omega)]

theorem toL_wt (D : Formalism.BasicNotions.D7) (h3 : admB3 D) (μ : Fin (N + 1) → Fin (r + K) → ℤ)
    (hd : Dominant (pEnd (tanPart μ))) :
    (({I | IsSt (tanPart μ) I} : Set (ℤ → Finset (Fin K))).ncard : ℝ) = BranchingDimensions.Letters.wt (D := toL r K LL B) μ := by
  have h1 := h3 K N (tanPart μ) hd
  rw [← Nat.card_coe_set_eq]
  have h2 : ((Nat.card {I : ℤ → Finset (Fin K) // IsSt (tanPart μ) I} : ℕ) : ℝ) =
      (((Nat.card {I : ℤ → Finset (Fin K) // IsSt (tanPart μ) I} : ℕ) : ℚ) : ℝ) := by push_cast; rfl
  refine Eq.trans h2 ?_
  rw [h1]
  unfold BranchingDimensions.Letters.wt BranchingDimensions.weylDim
  push_cast
  rw [Finset.prod_comm, Finset.prod_range]
  refine Finset.prod_congr rfl fun j _ => ?_
  have hka : ∀ x : Fin K, BranchingDimensions.Letters.kaRows (D := toL r K LL B) μ N x.val = pEnd (tanPart μ) x := by
    intro x
    unfold BranchingDimensions.Letters.kaRows
    show BranchingDimensions.Letters.ent (D := toL r K LL B) μ N (r + x.val) = _
    rw [entry_eq_of_lt LL B μ N (r + x.val) (by omega) (by have := x.2; omega)]
    rfl
  refine Eq.trans ?_ (prod_fin_ite_lt_eq K j.val j.2.le (fun i =>
    (((BranchingDimensions.Letters.kaRows (D := toL r K LL B) μ N i : ℤ) : ℝ) - ((BranchingDimensions.Letters.kaRows (D := toL r K LL B) μ N j.val : ℤ) : ℝ) +
      (((j.val : ℕ) : ℝ) - (i : ℝ))) / (((j.val : ℕ) : ℝ) - (i : ℝ))))
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hij : i < j
  · have hij' : i.val < j.val := hij
    rw [if_pos hij, if_pos hij', hka i, hka j]
    push_cast
    ring
  · have hij' : ¬ i.val < j.val := hij
    rw [if_neg hij, if_neg hij']
    simp

end

end Formalism.MainNotions.SelectionLemmas.Pf.T
end
end

noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf.T

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas
open Formalism.InvariantFactorPaths

variable {N r K : ℕ}

section
variable {n0 : ℕ} {LL : Letters (Fin N)} {B : Fin N → ℕ} {od : Fin N → Fin N} {bb : Fin N → ℝ} {a La : ℝ} {p : ℕ}

theorem tail_positive_eq (H : HypT N n0 r K LL B od bb a La p) (μ : Fin (N + 1) → Fin (r + K) → ℤ) (s : ℕ) (hs : s ≤ n0) :
    BranchingDimensions.tailPos ((toL r K LL B).stLen s) (BranchingDimensions.Letters.stage (D := toL r K LL B) μ s) 0 =
      posS (μ ⟨s, by have := H.hN; omega⟩) := by
  have hN := H.hN
  have hn0 := letters_n0_eq (r := r) (K := K) H
  have h0 : s - (toL r K LL B).n0 = 0 := by rw [hn0]; omega
  unfold BranchingDimensions.tailPos BranchingDimensions.Letters.stLen BranchingDimensions.Letters.stage posS
  rw [h0, Finset.filter_true_of_mem (fun _ _ => Nat.zero_le _)]
  show ∑ m ∈ Finset.range (r + K - 0), _ = _
  rw [Nat.sub_zero, Finset.sum_range]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Nat.add_zero, entry_eq_of_lt LL B μ s m.val (by omega) m.2]

theorem tail_negative_eq (H : HypT N n0 r K LL B od bb a La p) {dd : Fin N → ℕ} (P : PPath (r + K) N LL dd)
    (hP : IsPATHa LL n0 B P.mu dd) (s : ℕ) (hs : s ≤ N) :
    BranchingDimensions.tailNeg ((toL r K LL B).stLen s) (BranchingDimensions.Letters.stage (D := toL r K LL B) P.mu s) 0 =
      negS (P.mu ⟨s, by omega⟩) := by
  have hN := H.hN
  have hn0 := letters_n0_eq (r := r) (K := K) H
  unfold BranchingDimensions.tailNeg BranchingDimensions.Letters.stLen BranchingDimensions.Letters.stage negS
  rw [hn0, Finset.filter_true_of_mem (fun _ _ => Nat.zero_le _)]
  show ∑ m ∈ Finset.range (r + K - (s - n0)),
    max (-(BranchingDimensions.Letters.ent (D := toL r K LL B) P.mu s (r + K - (s - n0) - 1 - m + (s - n0)))) 0 = _
  have hh : s - n0 ≤ r := by omega
  generalize hhd : s - n0 = h at hh
  rw [Finset.sum_range_reflect (fun x => max (-(BranchingDimensions.Letters.ent (D := toL r K LL B) P.mu s (x + h))) 0) (r + K - h)]
  have hsplit : ∑ m : Fin (r + K), max (-P.mu ⟨s, by omega⟩ m) 0 =
      ∑ m ∈ Finset.range (h + (r + K - h)), max (-(BranchingDimensions.Letters.ent (D := toL r K LL B) P.mu s m)) 0 := by
    rw [show h + (r + K - h) = r + K by omega, Finset.sum_range]
    exact Finset.sum_congr rfl fun m _ => by rw [entry_eq_of_lt LL B P.mu s m.val (by omega) m.2]
  rw [hsplit, Finset.sum_range_add]
  have hz : ∑ x ∈ Finset.range h, max (-(BranchingDimensions.Letters.ent (D := toL r K LL B) P.mu s x)) 0 = 0 := by
    refine Finset.sum_eq_zero fun m hm => ?_
    rw [Finset.mem_range] at hm
    rw [entry_eq_of_lt LL B P.mu s m (by omega) (by omega)]
    have := hP.head ⟨s - 1, by omega⟩ ⟨m, by omega⟩ (by simp only; omega) (by simp only; omega)
    have he : (⟨s - 1, by omega⟩ : Fin N).succ = (⟨s, by omega⟩ : Fin (N + 1)) := Fin.ext (by simp; omega)
    rw [he] at this
    rw [this]
    exact max_eq_right (by simp)
  rw [hz, zero_add]
  exact Finset.sum_congr rfl fun x _ => by rw [Nat.add_comm x h]

theorem count_from_eq_vcount (LL : Letters (Fin N)) (B : Fin N → ℕ) (M t : ℕ) (hM : M ≤ N) :
    countFrom (fun l => (toL r K LL B).vec l) M (t + 1) = vcount LL t M := by
  classical
  unfold countFrom vcount
  symm
  refine Finset.card_bij (fun l _ => l.val + 1) ?_ ?_ ?_
  · intro l hl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
    rw [Finset.mem_filter, Finset.mem_Icc]
    beta_reduce
    rw [toL_vec LL B (l.val + 1) ⟨by omega, by omega⟩]
    exact ⟨⟨by omega, by omega⟩, hl.2.2, by omega⟩
  · intro l _ l' _ h
    exact Fin.ext (by omega)
  · intro y hy
    rw [Finset.mem_filter, Finset.mem_Icc] at hy
    have hv : (toL r K LL B).vec y = true := hy.2.1
    rw [toL_vec LL B y ⟨hy.1.1, by omega⟩] at hv
    refine ⟨⟨y - 1, by omega⟩, ?_, by simp only; omega⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨by omega, by omega, hv⟩

theorem vcount_tau_eq_add (H : HypT N n0 r K LL B od bb a La p) (t : ℕ) (ht : t ≤ n0) :
    ∀ s, n0 ≤ s → s ≤ N → vcount LL t s = vcount LL t n0 + (s - n0) := by
  intro s hs
  induction s, hs using Nat.le_induction with
  | base => intro _; simp
  | succ s hs ih =>
    intro hsN
    rw [vcount_succ LL t s (by omega) (by omega), ih (by omega), if_pos (H.vec_true_of_late ⟨s, by omega⟩ (by simp only; omega))]
    omega

theorem oldest_threshold_eq (H : HypT N n0 r K LL B od bb a La p) (i : Fin N) (hi : r ≤ i.val) :
    (toL r K LL B).Bo (i.val + 1) = B (od i) := by
  have hN := H.hN
  have hn0 := letters_n0_eq (r := r) (K := K) H
  have hod := oldest_lt_n0 H i hi
  have hlt : (od i).val < i.val := H.od_lt i hi
  have hvc : vcount LL (od i).val i.val = r := by
    refine Eq.trans ?_ (H.od_card i hi)
    unfold vcount
    congr 1
  unfold BranchingDimensions.Letters.Bo BranchingDimensions.Letters.latestV
  rw [Nat.add_sub_cancel, hn0]
  show (List.map (toL r K LL B).B (latestList (fun l => (toL r K LL B).vec l) (min i.val n0))).getD
    (r - 1 - (i.val - n0)) 0 = _
  have hx : (1 ≤ (od i).val + 1 ∧ (od i).val + 1 ≤ min i.val n0) ∧ (toL r K LL B).vec ((od i).val + 1) = true := by
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    rw [toL_vec LL B _ ⟨by omega, by omega⟩]
    exact H.od_vec i hi
  have hc : countFrom (fun l => (toL r K LL B).vec l) (min i.val n0) ((od i).val + 1) = (r - 1 - (i.val - n0)) + 1 := by
    rw [count_from_eq_vcount LL B _ _ (by omega)]
    rcases le_total i.val n0 with h | h
    · rw [Nat.min_eq_left h, hvc]; have := H.r1; omega
    · rw [Nat.min_eq_right h]
      have := vcount_tau_eq_add H (od i).val (by omega) i.val h (by omega)
      have hi2 := i.2
      omega
  obtain ⟨he, hel⟩ := latest_list_get_of_count _ _ _ _ hx hc
  rw [List.getD_eq_getElem _ _ (by simpa using he), List.getElem_map, hel, toL_B LL B _ ⟨by omega, by omega⟩]
  congr 1

theorem threshold_letter_eq_Xi (H : HypT N n0 r K LL B od bb a La p) (i : Fin N) :
    (toL r K LL B).XT 13 La (toB bb p) (i.val + 1) = Xi r K bb La p i := by
  have hp0 : (0 : ℝ) < p := by
    have : (13 : ℝ) ≤ (p : ℝ) := by exact_mod_cast H.p13
    linarith
  have hk0 : (0 : ℝ) < ((r + K : ℕ) : ℝ) := by
    have : 0 < r + K := by have := H.r1; omega
    exact_mod_cast this
  unfold BranchingDimensions.Letters.XT toB Xi
  rw [dite_eq_left ⟨by omega, by have := i.2; omega⟩]
  show La * (13 * bb ⟨i.val + 1 - 1, _⟩ / (p : ℝ)) / (((13 : ℕ) : ℝ) * ((r + K : ℕ) : ℝ)) = _
  have he : (⟨i.val + 1 - 1, by have := i.2; omega⟩ : Fin N) = i := Fin.ext (by simp)
  rw [he]
  push_cast
  field_simp

theorem typ_of_Typical [NeZero r] (H : HypT N n0 r K LL B od bb a La p) {dd : Fin N → ℕ} (P : PPath (r + K) N LL dd)
    (hP : IsPATHa LL n0 B P.mu dd) (hT : (toL r K LL B).Typical ((toL r K LL B).XT 13 La (toB bb p)) P.mu) :
    Typ LL B od bb La p P.mu := by
  have hN := H.hN
  obtain ⟨hT1, hT2, hT3⟩ := hT
  intro i
  have hi2 := i.2
  refine ⟨fun hv => ?_, fun hv hi => ?_, fun hi => ?_⟩
  · have hin : i.val < n0 := by
      by_contra hcon
      have := H.vec_true_of_late i (by omega)
      rw [hv] at this
      exact absurd this (by simp)
    have h := hT1 (i.val + 1) (by omega) (by show i.val + 1 ≤ N; omega)
      (by rw [toL_vec LL B _ ⟨by omega, by omega⟩]; exact hv)
    rw [Nat.add_sub_cancel, tail_positive_eq H P.mu i.val (by omega), tail_positive_eq H P.mu (i.val + 1) (by omega), threshold_letter_eq_Xi H i] at h
    exact h
  · have h := hT2 (i.val + 1) (by show r < i.val + 1; omega) (by show i.val + 1 ≤ N; omega)
      (by rw [toL_vec LL B _ ⟨by omega, by omega⟩]; exact hv)
    rw [Nat.add_sub_cancel, tail_negative_eq H P hP i.val (by omega), tail_negative_eq H P hP (i.val + 1) (by omega), threshold_letter_eq_Xi H i] at h
    exact h
  · have h := hT3 (i.val + 1) (by show r < i.val + 1; omega) (by show i.val + 1 ≤ N; omega)
    rw [Nat.add_sub_cancel, oldest_threshold_eq H i hi] at h
    have he : BranchingDimensions.Letters.ent (D := toL r K LL B) P.mu i.val ((toL r K LL B).r - 1) =
        plPart P.mu i.castSucc (lastIdx r) := by
      show BranchingDimensions.Letters.ent (D := toL r K LL B) P.mu i.val (r - 1) = _
      rw [entry_eq_of_lt LL B P.mu i.val (r - 1) (by omega) (by have := H.r1; omega)]
      rfl
    rw [he] at h
    exact h

end

theorem atypical_path_small_weight (D : Formalism.BasicNotions.D7) (h3 : admB3 D) : AtypicalPathSmallWeight := by
  intro N n0 r K _ _ LL B od bb a La p H μ hμ hnT
  obtain ⟨dd, hP⟩ := hμ
  obtain ⟨P, rfl⟩ := hP.path
  have hN := H.hN
  have h2N := two_N_lt_K H
  have hn0 := letters_n0_eq (r := r) (K := K) H
  have hd : Dominant (pEnd (tanPart P.mu)) := by
    intro x y hxy
    exact P.dom (Fin.last N) (by rw [Fin.le_def] at hxy ⊢; simp; omega)
  have h := (BranchingDimensions.Top.lemma_t_one (toL r K LL B) a 13 La (toB bb p) (toL_Wf H) (toL_Hyp H) (toL_TData H) P.mu
    (toL_IsPATH H P hP)).2 (fun hT => hnT (typ_of_Typical H P hP hT))
  rw [toL_wt (LL := LL) (B := B) D h3 P.mu hd]
  have hk' : (((toL r K LL B).k' : ℕ) : ℝ) = (K : ℝ) - 2 * (N : ℝ) := by
    show ((K - 2 * N : ℕ) : ℝ) = _
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have hrk : (toL r K LL B).rankAA = rkA r K n0 B := by
    unfold BranchingDimensions.Letters.rankAA
    rw [hn0]
    exact rank_eq_prod_choose LL B n0 (by omega)
  rw [hk', hrk] at h
  exact h

end Formalism.MainNotions.SelectionLemmas.Pf.T
