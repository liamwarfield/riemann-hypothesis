module

public import Formalism.ThetaLogCoordinates.ResidueClassEstimates.VandermondeRankEstimates.N0LeNs
public import Formalism.ThetaLogCoordinates.ResidueClassEstimates.VandermondeRankEstimates.AtypicalWeightBoundOf
public import Formalism.ThetaLogCoordinates.ResidueClassEstimates.VandermondeRankEstimates.Branch
public import Formalism.ThetaLogCoordinates.ResidueClassEstimates.VandermondeRankEstimates.WeylGT

@[expose] public section

section -- merged from Formalism.ThetaLogCoordinates.ResidueClassEstimates.VandermondeRankEstimates.LogWeylDimensionEstimate
noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.BranchingDimensions

namespace TDim

def hh (z : ℝ) (d : ℕ) : ℝ := Real.log ((z + d) / d)

lemma fT_eq (k' : ℕ) (z : ℝ) : fT k' z = ∑ d ∈ Icc 1 k', hh z d := rfl

lemma hh_zero (d : ℕ) : hh 0 d = 0 := by
  unfold hh
  rw [zero_add]
  rcases eq_or_ne (d : ℝ) 0 with h | h
  · rw [h, div_zero, Real.log_zero]
  · rw [div_self h, Real.log_one]

lemma fT_zero (k' : ℕ) : fT k' 0 = 0 := by
  rw [fT_eq]
  exact Finset.sum_eq_zero fun d _ => hh_zero d

lemma hh_nonneg {z : ℝ} {d : ℕ} (hz : 0 ≤ z) (hd : 1 ≤ d) : 0 ≤ hh z d := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  unfold hh
  apply Real.log_nonneg
  rw [one_le_div hd0]
  linarith

lemma hh_le {z : ℝ} {d : ℕ} (hz : 0 ≤ z) (hd : 1 ≤ d) : hh z d ≤ Real.log (1 + z) := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  unfold hh
  apply Real.log_le_log (div_pos (by linarith) hd0)
  rw [div_le_iff₀ hd0]
  nlinarith [mul_nonneg hz (sub_nonneg.mpr hd')]

lemma sum_hh_le {z L : ℝ} (hz : 0 ≤ z) (hL : Real.log (1 + z) ≤ L) (D : Finset ℕ)
    (hD : ∀ d ∈ D, 1 ≤ d) (k' : ℕ) :
    ∑ d ∈ D, hh z d ≤ fT k' z + ((D \ Icc 1 k').card : ℝ) * L := by
  have hset : D \ (D ∩ Icc 1 k') = D \ Icc 1 k' := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hsplit : ∑ d ∈ D \ (D ∩ Icc 1 k'), hh z d + ∑ d ∈ D ∩ Icc 1 k', hh z d =
      ∑ d ∈ D, hh z d :=
    Finset.sum_sdiff (fun x hx => (Finset.mem_inter.mp hx).1)
  rw [hset] at hsplit
  have h1 : ∑ d ∈ D ∩ Icc 1 k', hh z d ≤ ∑ d ∈ Icc 1 k', hh z d :=
    Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => (Finset.mem_inter.mp hx).2)
      (fun x hx _ => hh_nonneg hz (Finset.mem_Icc.mp hx).1)
  have h2 : ∑ d ∈ D \ Icc 1 k', hh z d ≤ ∑ d ∈ D \ Icc 1 k', L :=
    Finset.sum_le_sum fun x hx => (hh_le hz (hD x (Finset.mem_sdiff.mp hx).1)).trans hL
  rw [Finset.sum_const, nsmul_eq_mul] at h2
  rw [fT_eq]
  linarith

lemma le_sum_hh {z L : ℝ} (hz : 0 ≤ z) (hL : Real.log (1 + z) ≤ L) (D : Finset ℕ)
    (hD : ∀ d ∈ D, 1 ≤ d) (k' : ℕ) :
    fT k' z - ((Icc 1 k' \ D).card : ℝ) * L ≤ ∑ d ∈ D, hh z d := by
  have hset : Icc 1 k' \ (Icc 1 k' ∩ D) = Icc 1 k' \ D := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hsplit : ∑ d ∈ Icc 1 k' \ (Icc 1 k' ∩ D), hh z d + ∑ d ∈ Icc 1 k' ∩ D, hh z d =
      ∑ d ∈ Icc 1 k', hh z d :=
    Finset.sum_sdiff (fun x hx => (Finset.mem_inter.mp hx).1)
  rw [hset] at hsplit
  have h1 : ∑ d ∈ Icc 1 k' ∩ D, hh z d ≤ ∑ d ∈ D, hh z d :=
    Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => (Finset.mem_inter.mp hx).2)
      (fun x hx _ => hh_nonneg hz (hD x hx))
  have h2 : ∑ d ∈ Icc 1 k' \ D, hh z d ≤ ∑ d ∈ Icc 1 k' \ D, L :=
    Finset.sum_le_sum fun x hx =>
      (hh_le hz (Finset.mem_Icc.mp (Finset.mem_sdiff.mp hx).1).1).trans hL
  rw [Finset.sum_const, nsmul_eq_mul] at h2
  rw [fT_eq]
  linarith

lemma dom_anti {n : ℕ} {la : ℕ → ℤ} (h : Dom n la) {i j : ℕ} (hij : i ≤ j) (hj : j < n) :
    la j ≤ la i := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  clear hij
  revert hj
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hj
    have h1 := h (i + k) (by omega)
    have h2 := ih (by omega)
    show la (i + k + 1) ≤ la i
    exact h1.trans h2

lemma pos_idx {n Ns : ℕ} {la : ℕ → ℤ} (h : Dom n la)
    (hc : ((range n).filter fun m => 0 < la m).card ≤ Ns) {i : ℕ} (hi : i < n) (hp : 0 < la i) :
    i < Ns := by
  have hsub : range (i + 1) ⊆ (range n).filter fun m => 0 < la m := by
    intro m hm
    rw [Finset.mem_range] at hm
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, lt_of_lt_of_le hp (dom_anti h (by omega) hi)⟩
  have := Finset.card_le_card hsub
  rw [Finset.card_range] at this
  omega

lemma neg_idx {n Ns : ℕ} {la : ℕ → ℤ} (h : Dom n la)
    (hc : ((range n).filter fun m => la m < 0).card ≤ Ns) {t : ℕ} (ht : t < n) (hp : la t < 0) :
    n ≤ t + Ns := by
  have hsub : Ico t n ⊆ (range n).filter fun m => la m < 0 := by
    intro m hm
    rw [Finset.mem_Ico] at hm
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨hm.2, lt_of_le_of_lt (dom_anti h hm.1 hm.2) hp⟩
  have := Finset.card_le_card hsub
  rw [Nat.card_Ico] at this
  omega

lemma pos_row {r K Ns n : ℕ} {la : ℕ → ℤ} {L : ℝ} (h2 : 2 * Ns ≤ K) (hK : K ≤ n) (hn : n ≤ r + K)
    (hd : Dom n la) (hP : ((range n).filter fun m => 0 < la m).card ≤ Ns)
    (hM : ((range n).filter fun m => la m < 0).card ≤ Ns) (hL0 : 0 ≤ L)
    {i : ℕ} (hi : i < n) (hp : 0 < la i) (hL : Real.log (1 + ((la i : ℤ) : ℝ)) ≤ L) :
    fT (K - 2 * Ns) (la i : ℝ) - (Ns : ℝ) * L ≤
        ∑ j ∈ Ico (i + 1) n, (if la j = 0 then hh (la i : ℝ) (j - i) else 0) ∧
      ∑ j ∈ Ico (i + 1) n, (if la j = 0 then hh (la i : ℝ) (j - i) else 0) ≤
        fT (K - 2 * Ns) (la i : ℝ) + ((r : ℝ) + 2 * Ns) * L := by
  have hz : (0 : ℝ) ≤ ((la i : ℤ) : ℝ) := by exact_mod_cast hp.le
  have hiN : i < Ns := pos_idx hd hP hi hp
  have hS : ∑ j ∈ Ico (i + 1) n, (if la j = 0 then Formalism.InvariantFactorPaths.BranchingDimensions.TDim.hh (la i : ℝ) (j - i) else 0) =
      ∑ d ∈ ((Ico (i + 1) n).filter (fun j => la j = 0)).image (fun j => j - i),
        Formalism.InvariantFactorPaths.BranchingDimensions.TDim.hh (la i : ℝ) d := by
    rw [Finset.sum_image, Finset.sum_filter]
    intro x hx y hy hxy
    have hxy' : x - i = y - i := hxy
    simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_Ico, Set.mem_setOf_eq,
      Finset.mem_coe] at hx hy
    omega
  rw [hS]
  generalize hDdef : ((Ico (i + 1) n).filter (fun j => la j = 0)).image (fun j => j - i) = D
  have hD : ∀ d ∈ D, 1 ≤ d := by
    intro x hx
    rw [← hDdef, Finset.mem_image] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    rw [Finset.mem_filter, Finset.mem_Ico] at hj
    omega
  have hc1 : (D \ Icc 1 (K - 2 * Ns)).card ≤ r + 2 * Ns := by
    have hsub : D \ Icc 1 (K - 2 * Ns) ⊆ Ico (K - 2 * Ns + 1) n := by
      intro x hx
      rw [Finset.mem_sdiff] at hx
      obtain ⟨hx1, hx2⟩ := hx
      rw [← hDdef, Finset.mem_image] at hx1
      obtain ⟨j, hj, rfl⟩ := hx1
      rw [Finset.mem_filter, Finset.mem_Ico] at hj
      have hgt : K - 2 * Ns < j - i := by
        by_contra hh
        exact hx2 (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      rw [Finset.mem_Ico]
      omega
    have := Finset.card_le_card hsub
    rw [Nat.card_Ico] at this
    omega
  have hc2 : (Icc 1 (K - 2 * Ns) \ D).card ≤ Ns := by
    have hsub : Icc 1 (K - 2 * Ns) \ D ⊆ Ico 1 Ns := by
      intro x hx
      rw [Finset.mem_sdiff, Finset.mem_Icc] at hx
      obtain ⟨⟨hx1, hx2⟩, hxD⟩ := hx
      rw [Finset.mem_Ico]
      refine ⟨hx1, ?_⟩
      by_contra hlt
      apply hxD
      have hjn : i + x < n := by omega
      have hz0 : la (i + x) = 0 := by
        rcases lt_trichotomy (la (i + x)) 0 with h | h | h
        · have := neg_idx hd hM hjn h
          omega
        · exact h
        · have := pos_idx hd hP hjn h
          omega
      rw [← hDdef, Finset.mem_image]
      exact ⟨i + x, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, hjn⟩, hz0⟩, by omega⟩
    have := Finset.card_le_card hsub
    rw [Nat.card_Ico] at this
    omega
  have hup := sum_hh_le hz hL D hD (K - 2 * Ns)
  have hlo := le_sum_hh hz hL D hD (K - 2 * Ns)
  have e1 : ((D \ Icc 1 (K - 2 * Ns)).card : ℝ) * L ≤ ((r : ℝ) + 2 * Ns) * L := by
    apply mul_le_mul_of_nonneg_right _ hL0
    exact_mod_cast hc1
  have e2 : ((Icc 1 (K - 2 * Ns) \ D).card : ℝ) * L ≤ (Ns : ℝ) * L := by
    apply mul_le_mul_of_nonneg_right _ hL0
    exact_mod_cast hc2
  constructor <;> linarith

lemma neg_row {r K Ns n : ℕ} {la : ℕ → ℤ} {L : ℝ} (h2 : 2 * Ns ≤ K) (hK : K ≤ n) (hn : n ≤ r + K)
    (hd : Dom n la) (hP : ((range n).filter fun m => 0 < la m).card ≤ Ns)
    (hM : ((range n).filter fun m => la m < 0).card ≤ Ns) (hL0 : 0 ≤ L)
    {j : ℕ} (hj : j < n) (hp : la j < 0) (hL : Real.log (1 + ((-la j : ℤ) : ℝ)) ≤ L) :
    fT (K - 2 * Ns) ((-la j : ℤ) : ℝ) - (Ns : ℝ) * L ≤
        ∑ i ∈ range j, (if la i = 0 then hh ((-la j : ℤ) : ℝ) (j - i) else 0) ∧
      ∑ i ∈ range j, (if la i = 0 then hh ((-la j : ℤ) : ℝ) (j - i) else 0) ≤
        fT (K - 2 * Ns) ((-la j : ℤ) : ℝ) + ((r : ℝ) + 2 * Ns) * L := by
  have h0 : (0 : ℤ) ≤ -la j := by omega
  have hz : (0 : ℝ) ≤ ((-la j : ℤ) : ℝ) := by exact_mod_cast h0
  have hjN : n ≤ j + Ns := neg_idx hd hM hj hp
  have hS : ∑ i ∈ range j, (if la i = 0 then Formalism.InvariantFactorPaths.BranchingDimensions.TDim.hh ((-la j : ℤ) : ℝ) (j - i) else 0) =
      ∑ d ∈ ((range j).filter (fun i => la i = 0)).image (fun i => j - i),
        Formalism.InvariantFactorPaths.BranchingDimensions.TDim.hh ((-la j : ℤ) : ℝ) d := by
    rw [Finset.sum_image, Finset.sum_filter]
    intro x hx y hy hxy
    have hxy' : j - x = j - y := hxy
    simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_range, Set.mem_setOf_eq,
      Finset.mem_coe] at hx hy
    omega
  rw [hS]
  generalize hDdef : ((range j).filter (fun i => la i = 0)).image (fun i => j - i) = D
  have hD : ∀ d ∈ D, 1 ≤ d := by
    intro x hx
    rw [← hDdef, Finset.mem_image] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    rw [Finset.mem_filter, Finset.mem_range] at hi
    omega
  have hc1 : (D \ Icc 1 (K - 2 * Ns)).card ≤ r + 2 * Ns := by
    have hsub : D \ Icc 1 (K - 2 * Ns) ⊆ Ico (K - 2 * Ns + 1) n := by
      intro x hx
      rw [Finset.mem_sdiff] at hx
      obtain ⟨hx1, hx2⟩ := hx
      rw [← hDdef, Finset.mem_image] at hx1
      obtain ⟨i, hi, rfl⟩ := hx1
      rw [Finset.mem_filter, Finset.mem_range] at hi
      have hgt : K - 2 * Ns < j - i := by
        by_contra hh
        exact hx2 (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      rw [Finset.mem_Ico]
      omega
    have := Finset.card_le_card hsub
    rw [Nat.card_Ico] at this
    omega
  have hc2 : (Icc 1 (K - 2 * Ns) \ D).card ≤ Ns := by
    have hsub : Icc 1 (K - 2 * Ns) \ D ⊆ Ico 1 Ns := by
      intro x hx
      rw [Finset.mem_sdiff, Finset.mem_Icc] at hx
      obtain ⟨⟨hx1, hx2⟩, hxD⟩ := hx
      rw [Finset.mem_Ico]
      refine ⟨hx1, ?_⟩
      by_contra hlt
      apply hxD
      have hxj : x ≤ j := by omega
      have hin : j - x < n := by omega
      have hz0 : la (j - x) = 0 := by
        rcases lt_trichotomy (la (j - x)) 0 with h | h | h
        · have := neg_idx hd hM hin h
          omega
        · exact h
        · have := pos_idx hd hP hin h
          omega
      rw [← hDdef, Finset.mem_image]
      exact ⟨j - x, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hz0⟩, by omega⟩
    have := Finset.card_le_card hsub
    rw [Nat.card_Ico] at this
    omega
  have hup := sum_hh_le hz hL D hD (K - 2 * Ns)
  have hlo := le_sum_hh hz hL D hD (K - 2 * Ns)
  have e1 : ((D \ Icc 1 (K - 2 * Ns)).card : ℝ) * L ≤ ((r : ℝ) + 2 * Ns) * L := by
    apply mul_le_mul_of_nonneg_right _ hL0
    exact_mod_cast hc1
  have e2 : ((Icc 1 (K - 2 * Ns) \ D).card : ℝ) * L ≤ (Ns : ℝ) * L := by
    apply mul_le_mul_of_nonneg_right _ hL0
    exact_mod_cast hc2
  constructor <;> linarith

def G (la : ℕ → ℤ) (i j : ℕ) : ℝ :=
  Real.log ((((la i - la j : ℤ) : ℝ) + ((j : ℝ) - (i : ℝ))) / ((j : ℝ) - (i : ℝ)))

lemma G_eq {la : ℕ → ℤ} {i j : ℕ} (hij : i < j) : G la i j = hh ((la i - la j : ℤ) : ℝ) (j - i) := by
  unfold G hh
  rw [Nat.cast_sub hij.le]

def pa (la : ℕ → ℤ) (i j : ℕ) : ℝ := if la i ≠ 0 ∧ la j ≠ 0 then G la i j else 0

def pb (la : ℕ → ℤ) (i j : ℕ) : ℝ := if la j = 0 then hh ((max (la i) 0 : ℤ) : ℝ) (j - i) else 0

def pc (la : ℕ → ℤ) (i j : ℕ) : ℝ := if la i = 0 then hh ((max (-(la j)) 0 : ℤ) : ℝ) (j - i) else 0

lemma G_split {n : ℕ} {la : ℕ → ℤ} (hd : Dom n la) {i j : ℕ} (hij : i < j) (hj : j < n) :
    G la i j = pa la i j + pb la i j + pc la i j := by
  have hle : la j ≤ la i := dom_anti hd hij.le hj
  unfold pa pb pc
  rw [G_eq hij]
  by_cases hi0 : la i = 0 <;> by_cases hj0 : la j = 0
  · rw [if_neg (show ¬(la i ≠ 0 ∧ la j ≠ 0) from fun h => h.1 hi0), if_pos hj0, if_pos hi0,
      hi0, hj0]
    simp [hh_zero]
  · have hm : max (-(la j)) 0 = la i - la j := by
      rw [hi0, max_eq_left (show (0 : ℤ) ≤ -la j by linarith)]
      ring
    rw [if_neg (show ¬(la i ≠ 0 ∧ la j ≠ 0) from fun h => h.1 hi0), if_neg hj0, if_pos hi0, hm]
    ring
  · have hm : max (la i) 0 = la i - la j := by
      rw [hj0, sub_zero]
      exact max_eq_left (by linarith)
    rw [if_neg (show ¬(la i ≠ 0 ∧ la j ≠ 0) from fun h => h.2 hj0), if_pos hj0, if_neg hi0, hm]
    ring
  · rw [if_pos ⟨hi0, hj0⟩, if_neg hj0, if_neg hi0]
    ring

lemma sum_ite_const_le {n Ns : ℕ} (p : ℕ → Prop) [DecidablePred p]
    (hc : ((range n).filter p).card ≤ Ns) {c : ℝ} (h0 : 0 ≤ c) :
    ∑ i ∈ range n, (if p i then c else 0) ≤ (Ns : ℝ) * c := by
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc) h0

private theorem log_one_add_le_lemma {x A : ℝ} (hx : 0 ≤ x) (h : x ≤ A) :
    Real.log (1 + x) ≤ Real.log (1 + A) :=
  Real.log_le_log (by linarith) (by linarith)

private theorem sum_rows_lemma_2 {n Ns : ℕ} (p : ℕ → Prop) [DecidablePred p]
    (hc : ((range n).filter p).card ≤ Ns) (R B : ℕ → ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hR : ∀ i ∈ range n, B i - (if p i then a else 0) ≤ R i ∧ R i ≤ B i + (if p i then b else 0)) :
    (∑ i ∈ range n, B i) - (Ns : ℝ) * a ≤ ∑ i ∈ range n, R i ∧
      ∑ i ∈ range n, R i ≤ (∑ i ∈ range n, B i) + (Ns : ℝ) * b := by
  have h1 := sum_ite_const_le (n := n) p hc ha
  have h2 := sum_ite_const_le (n := n) p hc hb
  have l1 : ∑ i ∈ range n, (B i - (if p i then a else 0)) ≤ ∑ i ∈ range n, R i :=
    Finset.sum_le_sum fun i hi => (hR i hi).1
  have l2 : ∑ i ∈ range n, R i ≤ ∑ i ∈ range n, (B i + (if p i then b else 0)) :=
    Finset.sum_le_sum fun i hi => (hR i hi).2
  rw [Finset.sum_sub_distrib] at l1
  rw [Finset.sum_add_distrib] at l2
  constructor <;> linarith

private theorem factor_pos_lemma_3 {n : ℕ} {la : ℕ → ℤ} (hd : Formalism.InvariantFactorPaths.BranchingDimensions.Dom n la) {i j : ℕ} (hij : i < j)
    (hj : j < n) :
    0 < (((la i - la j : ℤ) : ℝ) + ((j : ℝ) - (i : ℝ))) / ((j : ℝ) - (i : ℝ)) := by
  have h1 : (i : ℝ) < j := by exact_mod_cast hij
  have h0 : (0 : ℤ) ≤ la i - la j := sub_nonneg.mpr (dom_anti hd hij.le hj)
  have h2 : (0 : ℝ) ≤ ((la i - la j : ℤ) : ℝ) := by exact_mod_cast h0
  apply div_pos <;> linarith

private theorem log_weylDim_lemma_4 {n : ℕ} {la : ℕ → ℤ} (hd : Formalism.InvariantFactorPaths.BranchingDimensions.Dom n la) :
    0 < weylDim n la ∧
      Real.log (weylDim n la) = ∑ j ∈ range n, ∑ i ∈ range j, G la i j := by
  have hpos : ∀ j ∈ range n, ∀ i ∈ range j,
      0 < (((la i - la j : ℤ) : ℝ) + ((j : ℝ) - (i : ℝ))) / ((j : ℝ) - (i : ℝ)) := by
    intro j hj i hi
    rw [Finset.mem_range] at hj hi
    exact factor_pos_lemma_3 hd hi hj
  have hinner : ∀ j ∈ range n,
      0 < ∏ i ∈ range j, (((la i - la j : ℤ) : ℝ) + ((j : ℝ) - (i : ℝ))) / ((j : ℝ) - (i : ℝ)) :=
    fun j hj => Finset.prod_pos (hpos j hj)
  unfold weylDim
  refine ⟨Finset.prod_pos hinner, ?_⟩
  rw [Real.log_prod]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [Real.log_prod]
    · rfl
    · intro i hi
      exact (hpos j hj i hi).ne'
  · intro j hj
    exact (hinner j hj).ne'

lemma sum_pa_le {Ns n : ℕ} {la : ℕ → ℤ} {L : ℝ} (hL0 : 0 ≤ L)
    (hP : ((range n).filter fun m => 0 < la m).card ≤ Ns)
    (hM : ((range n).filter fun m => la m < 0).card ≤ Ns)
    (hG : ∀ i j, i < j → j < n → G la i j ≤ L) :
    ∑ j ∈ range n, ∑ i ∈ range j, pa la i j ≤ 4 * (Ns : ℝ) ^ 2 * L := by
  have hnz : ((range n).filter fun m => la m ≠ 0).card ≤ 2 * Ns := by
    have hsub : ((range n).filter fun m => la m ≠ 0) ⊆
        ((range n).filter fun m => 0 < la m) ∪ ((range n).filter fun m => la m < 0) := by
      intro m hm
      rw [Finset.mem_filter] at hm
      rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
      rcases lt_or_gt_of_ne hm.2 with h | h
      · exact Or.inr ⟨hm.1, h⟩
      · exact Or.inl ⟨hm.1, h⟩
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le ((range n).filter fun m => 0 < la m)
      ((range n).filter fun m => la m < 0)
    omega
  have hrow : ∀ j ∈ range n, ∑ i ∈ range j, pa la i j ≤
      (if la j ≠ 0 then (2 * (Ns : ℝ)) * L else 0) := by
    intro j hj
    rw [Finset.mem_range] at hj
    by_cases hj0 : la j = 0
    · rw [if_neg (show ¬(la j ≠ 0) from fun h => h hj0)]
      refine le_of_eq (Finset.sum_eq_zero fun i _ => ?_)
      unfold pa
      rw [if_neg (show ¬(la i ≠ 0 ∧ la j ≠ 0) from fun h => h.2 hj0)]
    · rw [if_pos hj0]
      have h1 : ∑ i ∈ range j, pa la i j ≤ ∑ i ∈ range j, (if la i ≠ 0 then L else 0) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [Finset.mem_range] at hi
        unfold pa
        by_cases hi0 : la i = 0
        · rw [if_neg (show ¬(la i ≠ 0 ∧ la j ≠ 0) from fun h => h.1 hi0),
            if_neg (show ¬(la i ≠ 0) from fun h => h hi0)]
          all_goals exact le_rfl
        · rw [if_pos ⟨hi0, hj0⟩, if_pos hi0]
          exact hG i j hi hj
      have h2 : ∑ i ∈ range j, (if la i ≠ 0 then L else 0) ≤
          ∑ i ∈ range n, (if la i ≠ 0 then L else 0) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
          (fun x hx => Finset.mem_range.mpr (lt_trans (Finset.mem_range.mp hx) hj))
        intro i _ _
        split_ifs
        · exact hL0
        · exact le_rfl
      have h3 : ∑ i ∈ range n, (if la i ≠ 0 then L else 0) ≤ ((2 * Ns : ℕ) : ℝ) * L :=
        sum_ite_const_le (fun m => la m ≠ 0) hnz hL0
      have h4 : ((2 * Ns : ℕ) : ℝ) = 2 * (Ns : ℝ) := by push_cast; ring
      rw [h4] at h3
      linarith
  calc ∑ j ∈ range n, ∑ i ∈ range j, pa la i j
      ≤ ∑ j ∈ range n, (if la j ≠ 0 then (2 * (Ns : ℝ)) * L else 0) := Finset.sum_le_sum hrow
    _ ≤ ((2 * Ns : ℕ) : ℝ) * ((2 * (Ns : ℝ)) * L) :=
        sum_ite_const_le (fun m => la m ≠ 0) hnz (mul_nonneg (by positivity) hL0)
    _ = 4 * (Ns : ℝ) ^ 2 * L := by push_cast; ring

end TDim


open TDim in
theorem logWeylDimensionEstimate : LogWeylDimensionEstimate := by
  unfold LogWeylDimensionEstimate
  intro r K Ns n la A0 h2 hK hn hd hP hM hA0
  have hA : ∀ x : ℤ, x ≤ max (la 0) 0 + max (-(la (n - 1))) 0 → (x : ℝ) ≤ A0 :=
    fun x hx => le_trans (Int.cast_le.mpr hx) hA0
  have hm1 := le_max_left (la 0) 0
  have hm2 := le_max_right (la 0) 0
  have hm3 := le_max_left (-(la (n - 1))) 0
  have hm4 := le_max_right (-(la (n - 1))) 0
  have htop : ∀ i, i < n → la i ≤ la 0 := fun i hi => Formalism.InvariantFactorPaths.BranchingDimensions.TDim.dom_anti hd (Nat.zero_le i) hi
  have hbot : ∀ j, j < n → la (n - 1) ≤ la j := fun j hj => Formalism.InvariantFactorPaths.BranchingDimensions.TDim.dom_anti hd (by omega) (by omega)
  have hA0nn : 0 ≤ A0 := by
    have := hA 0 (by linarith)
    rw [Int.cast_zero] at this
    exact this
  have hL0 : 0 ≤ Real.log (1 + A0) := Real.log_nonneg (by linarith)
  have hG : ∀ i j, i < j → j < n → Formalism.InvariantFactorPaths.BranchingDimensions.TDim.G la i j ≤ Real.log (1 + A0) := by
    intro i j hij hj
    rw [Formalism.InvariantFactorPaths.BranchingDimensions.TDim.G_eq hij]
    have h0 : (0 : ℤ) ≤ la i - la j := sub_nonneg.mpr (Formalism.InvariantFactorPaths.BranchingDimensions.TDim.dom_anti hd hij.le hj)
    have hnn : (0 : ℝ) ≤ ((la i - la j : ℤ) : ℝ) := by exact_mod_cast h0
    refine (Formalism.InvariantFactorPaths.BranchingDimensions.TDim.hh_le hnn (by omega)).trans (_root_.Formalism.InvariantFactorPaths.BranchingDimensions.TDim.log_one_add_le_lemma hnn (hA _ ?_))
    have := htop i (by omega)
    have := hbot j hj
    linarith
  obtain ⟨hWpos, hlogW⟩ := _root_.Formalism.InvariantFactorPaths.BranchingDimensions.TDim.log_weylDim_lemma_4 hd
  have hsplit : ∑ j ∈ range n, ∑ i ∈ range j, Formalism.InvariantFactorPaths.BranchingDimensions.TDim.G la i j =
      ∑ j ∈ range n, ∑ i ∈ range j, Formalism.InvariantFactorPaths.BranchingDimensions.TDim.pa la i j +
        ∑ j ∈ range n, ∑ i ∈ range j, Formalism.InvariantFactorPaths.BranchingDimensions.TDim.pb la i j +
        ∑ j ∈ range n, ∑ i ∈ range j, Formalism.InvariantFactorPaths.BranchingDimensions.TDim.pc la i j := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi hj
    exact Formalism.InvariantFactorPaths.BranchingDimensions.TDim.G_split hd hi hj
  have hB0 : 0 ≤ ∑ j ∈ range n, ∑ i ∈ range j, Formalism.InvariantFactorPaths.BranchingDimensions.TDim.pa la i j := by
    apply Finset.sum_nonneg
    intro j hj
    apply Finset.sum_nonneg
    intro i hi
    rw [Finset.mem_range] at hi hj
    unfold Formalism.InvariantFactorPaths.BranchingDimensions.TDim.pa
    split_ifs
    · rw [Formalism.InvariantFactorPaths.BranchingDimensions.TDim.G_eq hi]
      have h0 : (0 : ℤ) ≤ la i - la j := sub_nonneg.mpr (Formalism.InvariantFactorPaths.BranchingDimensions.TDim.dom_anti hd hi.le hj)
      have hnn : (0 : ℝ) ≤ ((la i - la j : ℤ) : ℝ) := by exact_mod_cast h0
      exact Formalism.InvariantFactorPaths.BranchingDimensions.TDim.hh_nonneg hnn (by omega)
    · exact le_rfl
  have hB1 := Formalism.InvariantFactorPaths.BranchingDimensions.TDim.sum_pa_le hL0 hP hM hG
  have hswap : ∑ j ∈ range n, ∑ i ∈ range j, Formalism.InvariantFactorPaths.BranchingDimensions.TDim.pb la i j =
      ∑ i ∈ range n, ∑ j ∈ Ico (i + 1) n, Formalism.InvariantFactorPaths.BranchingDimensions.TDim.pb la i j := by
    apply Finset.sum_comm'
    intro j i
    simp only [Finset.mem_range, Finset.mem_Ico]
    constructor <;> intro h <;> omega
  have hposR : ∀ i ∈ range n,
      fT (K - 2 * Ns) ((max (la i) 0 : ℤ) : ℝ) -
          (if 0 < la i then (Ns : ℝ) * Real.log (1 + A0) else 0) ≤
        ∑ j ∈ Ico (i + 1) n, Formalism.InvariantFactorPaths.BranchingDimensions.TDim.pb la i j ∧
      ∑ j ∈ Ico (i + 1) n, Formalism.InvariantFactorPaths.BranchingDimensions.TDim.pb la i j ≤
        fT (K - 2 * Ns) ((max (la i) 0 : ℤ) : ℝ) +
          (if 0 < la i then ((r : ℝ) + 2 * Ns) * Real.log (1 + A0) else 0) := by
    intro i hi
    rw [Finset.mem_range] at hi
    unfold Formalism.InvariantFactorPaths.BranchingDimensions.TDim.pb
    by_cases hp : 0 < la i
    · rw [if_pos hp, if_pos hp]
      have hm : max (la i) 0 = la i := max_eq_left hp.le
      rw [hm]
      have hz : (0 : ℝ) ≤ ((la i : ℤ) : ℝ) := by exact_mod_cast hp.le
      have hle : la i ≤ max (la 0) 0 + max (-(la (n - 1))) 0 := by
        have := htop i hi
        linarith
      exact pos_row h2 hK hn hd hP hM hL0 hi hp (_root_.Formalism.InvariantFactorPaths.BranchingDimensions.TDim.log_one_add_le_lemma hz (hA _ hle))
    · rw [if_neg hp, if_neg hp]
      have hm : max (la i) 0 = 0 := max_eq_right (not_lt.mp hp)
      rw [hm]
      simp [Formalism.InvariantFactorPaths.BranchingDimensions.TDim.hh_zero, Formalism.InvariantFactorPaths.BranchingDimensions.TDim.fT_zero]
  have hnegR : ∀ j ∈ range n,
      fT (K - 2 * Ns) ((max (-(la j)) 0 : ℤ) : ℝ) -
          (if la j < 0 then (Ns : ℝ) * Real.log (1 + A0) else 0) ≤
        ∑ i ∈ range j, Formalism.InvariantFactorPaths.BranchingDimensions.TDim.pc la i j ∧
      ∑ i ∈ range j, Formalism.InvariantFactorPaths.BranchingDimensions.TDim.pc la i j ≤
        fT (K - 2 * Ns) ((max (-(la j)) 0 : ℤ) : ℝ) +
          (if la j < 0 then ((r : ℝ) + 2 * Ns) * Real.log (1 + A0) else 0) := by
    intro j hj
    rw [Finset.mem_range] at hj
    unfold Formalism.InvariantFactorPaths.BranchingDimensions.TDim.pc
    by_cases hp : la j < 0
    · rw [if_pos hp, if_pos hp]
      have hm : max (-(la j)) 0 = -la j := max_eq_left (by omega)
      rw [hm]
      have h0 : (0 : ℤ) ≤ -la j := by omega
      have hz : (0 : ℝ) ≤ ((-la j : ℤ) : ℝ) := by exact_mod_cast h0
      have hle : -la j ≤ max (la 0) 0 + max (-(la (n - 1))) 0 := by
        have := hbot j hj
        linarith
      exact neg_row h2 hK hn hd hP hM hL0 hj hp (_root_.Formalism.InvariantFactorPaths.BranchingDimensions.TDim.log_one_add_le_lemma hz (hA _ hle))
    · rw [if_neg hp, if_neg hp]
      have hm : max (-(la j)) 0 = 0 := max_eq_right (by omega)
      rw [hm]
      simp [Formalism.InvariantFactorPaths.BranchingDimensions.TDim.hh_zero, Formalism.InvariantFactorPaths.BranchingDimensions.TDim.fT_zero]
  have hPos : (∑ i ∈ range n, fT (K - 2 * Ns) ((max (la i) 0 : ℤ) : ℝ)) -
        (Ns : ℝ) * ((Ns : ℝ) * Real.log (1 + A0)) ≤
        ∑ i ∈ range n, ∑ j ∈ Ico (i + 1) n, Formalism.InvariantFactorPaths.BranchingDimensions.TDim.pb la i j ∧
      ∑ i ∈ range n, ∑ j ∈ Ico (i + 1) n, Formalism.InvariantFactorPaths.BranchingDimensions.TDim.pb la i j ≤
        (∑ i ∈ range n, fT (K - 2 * Ns) ((max (la i) 0 : ℤ) : ℝ)) +
          (Ns : ℝ) * (((r : ℝ) + 2 * Ns) * Real.log (1 + A0)) :=
    _root_.Formalism.InvariantFactorPaths.BranchingDimensions.TDim.sum_rows_lemma_2 (n := n) (fun m => 0 < la m) hP (fun i => ∑ j ∈ Ico (i + 1) n, Formalism.InvariantFactorPaths.BranchingDimensions.TDim.pb la i j)
      (fun i => fT (K - 2 * Ns) ((max (la i) 0 : ℤ) : ℝ))
      (mul_nonneg (by positivity) hL0) (mul_nonneg (by positivity) hL0) hposR
  have hNeg : (∑ j ∈ range n, fT (K - 2 * Ns) ((max (-(la j)) 0 : ℤ) : ℝ)) -
        (Ns : ℝ) * ((Ns : ℝ) * Real.log (1 + A0)) ≤
        ∑ j ∈ range n, ∑ i ∈ range j, Formalism.InvariantFactorPaths.BranchingDimensions.TDim.pc la i j ∧
      ∑ j ∈ range n, ∑ i ∈ range j, Formalism.InvariantFactorPaths.BranchingDimensions.TDim.pc la i j ≤
        (∑ j ∈ range n, fT (K - 2 * Ns) ((max (-(la j)) 0 : ℤ) : ℝ)) +
          (Ns : ℝ) * (((r : ℝ) + 2 * Ns) * Real.log (1 + A0)) :=
    _root_.Formalism.InvariantFactorPaths.BranchingDimensions.TDim.sum_rows_lemma_2 (n := n) (fun m => la m < 0) hM (fun j => ∑ i ∈ range j, Formalism.InvariantFactorPaths.BranchingDimensions.TDim.pc la i j)
      (fun j => fT (K - 2 * Ns) ((max (-(la j)) 0 : ℤ) : ℝ))
      (mul_nonneg (by positivity) hL0) (mul_nonneg (by positivity) hL0) hnegR
  obtain ⟨hP1, hP2⟩ := hPos
  obtain ⟨hN1, hN2⟩ := hNeg
  refine ⟨hWpos, ?_, ?_⟩
  · rw [hlogW, hsplit, hswap]
    linarith
  · rw [hlogW, hsplit, hswap]
    linarith

end Formalism.InvariantFactorPaths.BranchingDimensions
end
end

section -- merged from Formalism.ThetaLogCoordinates.ResidueClassEstimates.VandermondeRankEstimates.LogBinomialProperties
noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.BranchingDimensions

open Letters

theorem fT_zero (k' : ℕ) : fT k' 0 = 0 := by
  unfold fT
  apply Finset.sum_eq_zero
  intro j hj
  have hj1 : (0 : ℝ) < j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
  rw [zero_add, div_self hj1.ne', Real.log_one]

theorem fT_succ (k' : ℕ) (y : ℝ) :
    fT (k' + 1) y = fT k' y + Real.log ((y + ((k' + 1 : ℕ) : ℝ)) / ((k' + 1 : ℕ) : ℝ)) := by
  unfold fT
  rw [Finset.sum_Icc_succ_top (by omega)]

theorem fT_nat (k' y : ℕ) : fT k' y = Real.log ((y + k').choose k') := by
  induction k' with
  | zero => simp [fT]
  | succ n ih =>
    have hc : (0 : ℝ) < ((y + n).choose n : ℝ) := by
      exact_mod_cast Nat.choose_pos (Nat.le_add_left n y)
    have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
    have hy : (0 : ℝ) ≤ (y : ℝ) := Nat.cast_nonneg y
    rw [fT_succ, ih, ← Real.log_mul hc.ne' (by positivity)]
    congr 1
    have h := Nat.add_one_mul_choose_eq (y + n) n
    have h' : (((y + n).succ : ℕ) : ℝ) * ((y + n).choose n : ℝ) =
        (((y + n).succ.choose n.succ : ℕ) : ℝ) * ((n.succ : ℕ) : ℝ) := by exact_mod_cast h
    have e1 : (((y + n).succ : ℕ) : ℝ) = (y : ℝ) + ((n + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [e1] at h'
    have e2 : y + (n + 1) = (y + n).succ := rfl
    rw [e2, mul_div_assoc', eq_comm, eq_div_iff hn.ne', ← h', mul_comm]

theorem fT_hasDerivAt (k' : ℕ) (y : ℝ) (hy : 0 ≤ y) : HasDerivAt (fT k') (fT' k' y) y := by
  have e : fT k' = fun y : ℝ => ∑ j ∈ Icc 1 k', Real.log ((y + j) / j) := rfl
  rw [e]
  unfold fT'
  apply HasDerivAt.fun_sum
  intro j hj
  have hj1 : (0 : ℝ) < j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
  have h1 : HasDerivAt (fun y : ℝ => (y + j) / j) (1 / j) y :=
    ((hasDerivAt_id y).add_const _).div_const _
  have h2 := h1.log (by positivity)
  have e2 : 1 / (y + (j : ℝ)) = 1 / (j : ℝ) / ((y + j) / j) :=
    (div_div_div_cancel_right₀ hj1.ne' _ _).symm
  rw [e2]
  exact h2

theorem fT'_nonneg (k' : ℕ) (y : ℝ) (hy : 0 ≤ y) : 0 ≤ fT' k' y := by
  unfold fT'
  apply Finset.sum_nonneg
  intro j _
  positivity

theorem fT'_anti (k' : ℕ) (y y' : ℝ) (hy : 0 ≤ y) (h : y ≤ y') : fT' k' y' ≤ fT' k' y := by
  unfold fT'
  apply Finset.sum_le_sum
  intro j hj
  have hj1 : (0 : ℝ) < j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
  apply one_div_le_one_div_of_le (by positivity) (by linarith)

theorem fT'_lower (k' : ℕ) (y : ℝ) (hy : 0 ≤ y) : (k' : ℝ) / (y + k') ≤ fT' k' y := by
  unfold fT'
  have : (k' : ℝ) / (y + k') = ∑ _j ∈ Icc 1 k', 1 / (y + (k' : ℝ)) := by
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]; simp [div_eq_mul_inv]
  rw [this]
  apply Finset.sum_le_sum
  intro j hj
  have hj1 : (0 : ℝ) < j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
  have hj2 : (j : ℝ) ≤ k' := by exact_mod_cast (Finset.mem_Icc.mp hj).2
  apply one_div_le_one_div_of_le (by positivity) (by linarith)

theorem fT'_upper (k' : ℕ) (y : ℝ) (hy : 0 ≤ y) : fT' k' y ≤ (k' : ℝ) / (y + 1) := by
  unfold fT'
  have : (k' : ℝ) / (y + 1) = ∑ _j ∈ Icc 1 k', 1 / (y + (1 : ℝ)) := by
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]; simp [div_eq_mul_inv]
  rw [this]
  apply Finset.sum_le_sum
  intro j hj
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
  apply one_div_le_one_div_of_le (by positivity) (by linarith)

theorem fT'_pos (k' : ℕ) (y : ℝ) (hy : 0 ≤ y) (hk : 1 ≤ k') : 0 < fT' k' y := by
  have hk' : (0 : ℝ) < k' := by exact_mod_cast hk
  exact lt_of_lt_of_le (by positivity) (fT'_lower k' y hy)

theorem fT'_lower2 (k' : ℕ) (y : ℝ) (hy : (k' : ℝ) ≤ y) (hk : 1 ≤ k') :
    (k' : ℝ) / (2 * y) ≤ fT' k' y := by
  have hk' : (0 : ℝ) < k' := by exact_mod_cast hk
  refine le_trans ?_ (fT'_lower k' y (by linarith))
  apply div_le_div_of_nonneg_left hk'.le (by linarith) (by linarith)

theorem fT'_half (k' : ℕ) (y y' : ℝ) (hy : (k' : ℝ) ≤ y) (h : 4 * y ≤ y') :
    fT' k' y' ≤ fT' k' y / 2 := by
  unfold fT'
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro j hj
  have hj1 : (0 : ℝ) < j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
  have hj2 : (j : ℝ) ≤ k' := by exact_mod_cast (Finset.mem_Icc.mp hj).2
  have hy0 : 0 ≤ y := by linarith
  rw [div_div]
  apply one_div_le_one_div_of_le (by positivity) (by linarith)

theorem fT_concave (k' : ℕ) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    fT k' x - fT k' y ≤ fT' k' y * (x - y) := by
  unfold fT fT'
  rw [← Finset.sum_sub_distrib, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j hj
  have hj1 : (0 : ℝ) < j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
  have hxj : 0 < x + j := by linarith
  have hyj : 0 < y + j := by linarith
  rw [← Real.log_div (by positivity) (by positivity)]
  have e : (x + j) / j / ((y + j) / j) = (x + j) / (y + j) := by field_simp
  rw [e]
  refine le_trans (Real.log_le_sub_one_of_pos (by positivity)) (le_of_eq ?_)
  field_simp
  ring

theorem logBinomialProperties : LogBinomialProperties := by
  intro k'
  exact ⟨fT_zero k', fT_nat k', fT_hasDerivAt k', fT'_pos k', fT'_anti k',
    fun y hy _ => ⟨fT'_lower k' y hy, fT'_upper k' y hy⟩, fT'_lower2 k', fT'_half k', fT_concave k'⟩

theorem sum_incr (g : ℕ → ℝ) (L : ℕ) :
    ∑ u ∈ range (L + 1), (g u - (if u = 0 then 0 else g (u - 1))) = g L := by
  induction L with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; simp

theorem abel_tails (g d : ℕ → ℝ) (L : ℕ) :
    ∑ l ∈ range L, g l * d l =
      ∑ u ∈ range L, (g u - (if u = 0 then 0 else g (u - 1))) * ∑ l ∈ Ico u L, d l := by
  induction L with
  | zero => simp
  | succ n ih =>
    have h1 : ∑ u ∈ range (n + 1), (g u - (if u = 0 then 0 else g (u - 1))) * ∑ l ∈ Ico u (n + 1), d l =
        ∑ u ∈ range (n + 1), ((g u - (if u = 0 then 0 else g (u - 1))) * ∑ l ∈ Ico u n, d l +
          (g u - (if u = 0 then 0 else g (u - 1))) * d n) := by
      apply Finset.sum_congr rfl
      intro u hu
      have hu' : u ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hu)
      rw [Finset.sum_Ico_succ_top hu', mul_add]
    rw [h1, Finset.sum_add_distrib, ← Finset.sum_mul, sum_incr, Finset.sum_range_succ,
      Finset.sum_range_succ, ih]
    simp

theorem logBinomialDeficit : LogBinomialDeficit := by
  intro k' L al Bs hk hal hBs h4 hDe
  have hk0 : (0 : ℝ) < k' := by exact_mod_cast hk
  have hB0 : ∀ l, l < L → 0 ≤ Bs l := fun l hl => le_trans hk0.le (hBs l hl)
  have hc : ∀ u, u < L →
      fT' k' (Bs u) / 2 ≤ fT' k' (Bs u) - (if u = 0 then 0 else fT' k' (Bs (u - 1))) := by
    intro u hu
    have hn := fT'_nonneg k' (Bs u) (hB0 u hu)
    by_cases h0 : u = 0
    · rw [if_pos h0]; linarith
    · rw [if_neg h0]
      have e : u - 1 + 1 = u := Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero h0)
      have h := h4 (u - 1) (by rw [e]; exact hu)
      rw [e] at h
      have := fT'_half k' (Bs u) (Bs (u - 1)) (hBs u hu) h
      linarith
  have hc0 : ∀ u, u < L → 0 ≤ fT' k' (Bs u) - (if u = 0 then 0 else fT' k' (Bs (u - 1))) := by
    intro u hu
    have hn := fT'_nonneg k' (Bs u) (hB0 u hu)
    linarith [hc u hu]
  have hmain : (∑ l ∈ range L, fT k' (al l)) - (∑ l ∈ range L, fT k' (Bs l)) ≤
      ∑ u ∈ range L, (fT' k' (Bs u) - (if u = 0 then 0 else fT' k' (Bs (u - 1)))) *
        ((∑ l ∈ Ico u L, al l) - (∑ l ∈ Ico u L, Bs l)) := by
    have h := abel_tails (fun l => fT' k' (Bs l)) (fun l => al l - Bs l) L
    simp only [Finset.sum_sub_distrib] at h
    rw [← h, ← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro l hl
    exact fT_concave k' (al l) (Bs l) (hal l) (hB0 l (Finset.mem_range.mp hl))
  have hterm : ∀ u ∈ range L, (fT' k' (Bs u) - (if u = 0 then 0 else fT' k' (Bs (u - 1)))) *
        ((∑ l ∈ Ico u L, al l) - (∑ l ∈ Ico u L, Bs l)) ≤ 0 := by
    intro u hu
    have hu' := Finset.mem_range.mp hu
    exact mul_nonpos_of_nonneg_of_nonpos (hc0 u hu') (hDe u hu')
  refine ⟨hc, hmain, Finset.sum_nonpos hterm, ?_⟩
  intro u₀ X hu₀ hX hdef
  constructor
  · refine le_trans hmain ?_
    have h1 := Finset.single_le_sum
      (f := fun u => -((fT' k' (Bs u) - (if u = 0 then 0 else fT' k' (Bs (u - 1)))) *
        ((∑ l ∈ Ico u L, al l) - (∑ l ∈ Ico u L, Bs l))))
      (fun u hu => neg_nonneg.mpr (hterm u hu)) (Finset.mem_range.mpr hu₀)
    rw [Finset.sum_neg_distrib] at h1
    have h2 := mul_le_mul_of_nonneg_left hdef (hc0 u₀ hu₀)
    have h3 := mul_le_mul_of_nonneg_right (hc u₀ hu₀) hX
    linarith
  · have h := fT'_lower2 k' (Bs u₀) (hBs u₀ hu₀) hk
    have hBp : 0 < Bs u₀ := lt_of_lt_of_le hk0 (hBs u₀ hu₀)
    have e : X * k' / (4 * Bs u₀) = X * ((k' : ℝ) / (2 * Bs u₀)) / 2 := by
      field_simp
      ring
    rw [e]
    have := mul_le_mul_of_nonneg_left h hX
    linarith

theorem fT_add_bounds (k' : ℕ) (y : ℝ) (hy : 0 ≤ y) (d : ℕ) :
    0 ≤ fT (k' + d) y - fT k' y ∧ fT (k' + d) y - fT k' y ≤ (d : ℝ) * Real.log (1 + y) := by
  induction d with
  | zero => simp
  | succ n ih =>
    have hN : (1 : ℝ) ≤ ((k' + n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
    have hN0 : (0 : ℝ) < ((k' + n + 1 : ℕ) : ℝ) := by linarith
    have e : fT (k' + (n + 1)) y = fT (k' + n) y +
        Real.log ((y + ((k' + n + 1 : ℕ) : ℝ)) / ((k' + n + 1 : ℕ) : ℝ)) := fT_succ (k' + n) y
    have h1 : 1 ≤ (y + ((k' + n + 1 : ℕ) : ℝ)) / ((k' + n + 1 : ℕ) : ℝ) := by
      rw [le_div_iff₀ hN0]; linarith
    have h2 : (y + ((k' + n + 1 : ℕ) : ℝ)) / ((k' + n + 1 : ℕ) : ℝ) ≤ 1 + y := by
      rw [div_le_iff₀ hN0]
      nlinarith [mul_nonneg hy (sub_nonneg.mpr hN)]
    have l1 := Real.log_nonneg h1
    have l2 := Real.log_le_log (by linarith) h2
    have ec : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [e, ec]
    constructor
    · linarith [ih.1]
    · linarith [ih.2]

theorem logRankEstimate : LogRankEstimate := by
  intro D A0 hA0 hr hrN hK hB
  obtain ⟨d, hd, hdle⟩ : ∃ d : ℕ, D.k - 1 = D.k' + d ∧ d ≤ D.r + 2 * D.Ns := by
    refine ⟨D.r + 2 * D.Ns - 1, ?_, by omega⟩
    unfold Letters.k Letters.k'
    omega
  have hk1 : 1 ≤ D.k := by unfold Letters.k; omega
  have hlog : Real.log (D.rankAA : ℝ) = ∑ i ∈ Icc 1 D.n0, fT (D.k' + d) (D.B i) := by
    unfold Letters.rankAA
    rw [Nat.cast_prod, Real.log_prod]
    · apply Finset.sum_congr rfl
      intro i _
      rw [fT_nat, ← hd]
      have : D.B i + D.k - 1 = D.B i + (D.k - 1) := by omega
      rw [this]
    · intro i _
      have : 0 < (D.B i + D.k - 1).choose (D.k - 1) := Nat.choose_pos (by omega)
      exact_mod_cast this.ne'
  rw [hlog, ← Finset.sum_sub_distrib]
  have hl0 : 0 ≤ Real.log (1 + A0) := Real.log_nonneg (by linarith)
  constructor
  · apply Finset.sum_nonneg
    intro i _
    exact (fT_add_bounds D.k' (D.B i) (Nat.cast_nonneg _) d).1
  · have h1 : ∑ i ∈ Icc 1 D.n0, (fT (D.k' + d) (D.B i) - fT D.k' (D.B i)) ≤
        ∑ _i ∈ Icc 1 D.n0, ((D.r : ℝ) + 2 * D.Ns) * Real.log (1 + A0) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' := Finset.mem_Icc.mp hi
      have hBi : (0 : ℝ) ≤ (D.B i : ℝ) := Nat.cast_nonneg _
      refine le_trans (fT_add_bounds D.k' (D.B i) hBi d).2 ?_
      have hdR : (d : ℝ) ≤ (D.r : ℝ) + 2 * D.Ns := by exact_mod_cast hdle
      have hll : Real.log (1 + (D.B i : ℝ)) ≤ Real.log (1 + A0) :=
        Real.log_le_log (by linarith) (by linarith [hB i hi'.1 hi'.2])
      exact mul_le_mul hdR hll (Real.log_nonneg (by linarith)) (by positivity)
    refine le_trans h1 ?_
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_assoc]
    have hn : ((D.n0 + 1 - 1 : ℕ) : ℝ) ≤ (D.Ns : ℝ) := by
      have : D.n0 + 1 - 1 ≤ D.Ns := by unfold Letters.n0; omega
      exact_mod_cast this
    exact mul_le_mul_of_nonneg_right hn (by positivity)

end Formalism.InvariantFactorPaths.BranchingDimensions
end
end

namespace Formalism.InvariantFactorPaths.BranchingDimensions.Top

theorem lemma_t_one : PathWeightBound :=
  pathWeightBound_of pathEntryBounds pathInterlacingCriterion logBinomialProperties logWeylDimensionEstimate logRankEstimate pathTailBounds logBinomialDeficit
theorem weylGT : ∀ (n : ℕ) (μ : Fin n → ℤ), Antitone μ → weylDim n (extW μ) = (Formalism.InvariantFactorPaths.GelfandTsetlinBases.dGT n μ : ℝ) :=
  weyl_dim_eq_gelfand_tsetlin branchingDimensionFormula

end Formalism.InvariantFactorPaths.BranchingDimensions.Top
