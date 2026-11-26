module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsFlag
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.NumStandardTableEqCardMonotone

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchSchurAtRootsOfUnity
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

theorem schurAtRoots_place_lt {r k : ℕ} (nu : Fin r → ℕ) (hanti : Antitone nu)
    (hsum : ∑ i, nu i = k) (i : Fin r) (hi : 1 ≤ nu i) : (i : ℕ) < k := by
  have h1 : (Iic i).card • 1 ≤ ∑ j ∈ Iic i, nu j :=
    Finset.card_nsmul_le_sum _ _ _ fun j hj => le_trans hi (hanti (Finset.mem_Iic.mp hj))
  have h2 : ∑ j ∈ Iic i, nu j ≤ ∑ j, nu j :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  rw [Fin.card_Iic, smul_eq_mul, mul_one] at h1
  omega

theorem SchSchurAtRootsOfUnity.proof (h1 : SchSchurRowsToK.Statement)
    (h2 : SchSchurEvalMatrix.Statement) (h3 : SchJTMatrixDetAtRoots.Statement) :
    SchSchurAtRootsOfUnity.Statement := by
  intro N r k nu hk hkN hanti hsum
  set nu' : Fin k → ℕ := fun i => if h : (i : ℕ) < r then nu ⟨i, h⟩ else 0 with hnu'
  have hplace := schurAtRoots_place_lt nu hanti hsum

  have hanti' : Antitone nu' := by
    intro i j hij
    simp only [hnu']
    by_cases hj : (j : ℕ) < r
    · have hi : (i : ℕ) < r := lt_of_le_of_lt (Fin.le_def.mp hij) hj
      rw [dif_pos hi, dif_pos hj]
      exact hanti (Fin.le_def.mpr (Fin.le_def.mp hij))
    · rw [dite_eq_right hj]; exact Nat.zero_le _

  have hsum' : ∑ i, nu' i = k := by
    set g : ℕ → ℕ := fun i => if h : i < r then nu ⟨i, h⟩ else 0 with hg
    have e1 : ∑ i, nu' i = ∑ i ∈ range k, g i := by
      rw [← Fin.sum_univ_eq_sum_range]
    have e2 : ∑ i, nu i = ∑ i ∈ range r, g i := by
      rw [← Fin.sum_univ_eq_sum_range]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hg, dif_pos i.isLt]
    have hgk : ∀ i, k ≤ i → g i = 0 := by
      intro i hi
      simp only [hg]
      split_ifs with h
      · by_contra hne
        have := hplace ⟨i, h⟩ (Nat.one_le_iff_ne_zero.mpr hne)
        simp at this; omega
      · rfl
    have hgr : ∀ i, r ≤ i → g i = 0 := by
      intro i hi; simp only [hg]; rw [dite_eq_right (by omega)]
    have e3 : ∑ i ∈ range k, g i = ∑ i ∈ range (r + k), g i :=
      Finset.sum_subset (Finset.range_mono (by omega)) fun i _ hni =>
         hgk i (not_lt.mp (fun h => hni (Finset.mem_range.mpr h)))
    have e4 : ∑ i ∈ range r, g i = ∑ i ∈ range (r + k), g i :=
      Finset.sum_subset (Finset.range_mono (by omega)) fun i _ hni =>
         hgr i (not_lt.mp (fun h => hni (Finset.mem_range.mpr h)))
    rw [e1, e3, ← e4, ← e2, hsum]
  rw [h1 (Fin N) r k nu hanti hsum, h2 N k k _ hk hkN, h3 k nu' hk hanti' hsum']

  have hcond : (∀ i : Fin k, (i : ℕ) ≠ 0 → nu' i ≤ 1) ↔ (∀ i : Fin r, (i : ℕ) ≠ 0 → nu i ≤ 1) := by
    constructor
    · intro H i hi0
      by_cases hz : nu i = 0
      · rw [hz]; exact Nat.zero_le _
      · have hik := hplace i (Nat.one_le_iff_ne_zero.mpr hz)
        have := H ⟨i, hik⟩ hi0
        simp only [hnu', dif_pos i.isLt] at this
        exact this
    · intro H i hi0
      simp only [hnu']
      split_ifs with h
      · exact H ⟨i, h⟩ hi0
      · exact Nat.zero_le _

  have hcard : (univ.filter fun i : Fin k => (i : ℕ) ≠ 0 ∧ nu' i = 1).card =
      (univ.filter fun i : Fin r => (i : ℕ) ≠ 0 ∧ nu i = 1).card := by
    refine Finset.card_bij'
      (fun i hi => ⟨i, by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hnu'] at hi
        by_contra h; rw [dite_eq_right h] at hi; omega⟩)
      (fun i hi => ⟨i, by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        exact hplace i (by omega)⟩) ?_ ?_ ?_ ?_
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hnu'] at hi ⊢
      obtain ⟨h0, h1⟩ := hi
      split_ifs at h1 with h
      exact ⟨h0, h1⟩
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hnu'] at hi ⊢
      refine ⟨hi.1, ?_⟩
      rw [dif_pos i.isLt]; exact hi.2
    · intro i hi; rfl
    · intro i hi; rfl
  simp only [hcond, hcard]

end

end GroundTheory.Heights₂.Heights.RestTerms
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PHookTableauCount
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset

theorem vandermondeOf_succ {R : Type*} [CommRing R] {n : ℕ} (v : Fin (n + 1) → R) :
    vandermondeOf v =
      (∏ j : Fin n, (v 0 - v j.succ)) * vandermondeOf (fun j : Fin n => v j.succ) := by
  have key : ∀ i : Fin (n + 1), ∏ j ∈ Finset.Ioi i, (v i - v j) =
      ∏ j : Fin (n + 1), if i < j then v i - v j else 1 := by
    intro i
    rw [← Finset.prod_filter, Finset.filter_lt_eq_Ioi]
  unfold vandermondeOf
  simp only [key]
  rw [Fin.prod_univ_succ]
  congr 1
  · rw [Fin.prod_univ_succ]
    simp [Fin.succ_pos]
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [Fin.prod_univ_succ]
    simp only [Fin.succ_lt_succ_iff, Fin.not_lt_zero, if_false, one_mul]
    rw [← Finset.prod_filter, Finset.filter_lt_eq_Ioi]

theorem numStandardTable_zero (m : ℕ) : numStandardTable (fun _ : Fin m => (0 : ℕ)) = 1 := by
  have hc : youngCells (fun _ : Fin m => (0 : ℕ)) = ∅ := by
    ext c
    simp [youngCells]
  have : IsEmpty (youngCells (fun _ : Fin m => (0 : ℕ))) :=
    ⟨fun p => by simpa [hc] using p.2⟩
  have : IsEmpty (Fin (youngCells (fun _ : Fin m => (0 : ℕ))).card) := by
    rw [hc]
    exact Fin.isEmpty'
  unfold numStandardTable
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun a b => Subtype.ext (Equiv.ext fun p => isEmptyElim p)⟩,
    ⟨⟨Equiv.equivOfIsEmpty _ _, fun p => isEmptyElim p⟩⟩⟩

theorem prod_range_sub_eq_descFactorial (n l : ℕ) :
    ∏ j ∈ Finset.range l, (n - j) = n.descFactorial l := by
  induction l with
  | zero => simp
  | succ l ih => rw [Finset.prod_range_succ, ih, Nat.descFactorial_succ, mul_comm]

theorem prod_fin_sub_eq_factorial (l : ℕ) : ∏ j : Fin l, (l - (j : ℕ)) = l.factorial := by
  rw [Fin.prod_univ_eq_prod_range (fun j => l - j) l,
    ← Finset.prod_range_reflect (fun j => l - j) l]
  have : ∀ j ∈ Finset.range l, l - (l - 1 - j) = j + 1 := by
    intro j hj
    have := Finset.mem_range.1 hj
    omega
  rw [Finset.prod_congr rfl this, Finset.prod_range_add_one_eq_factorial]

theorem vandermondeOf_add_const {R : Type*} [CommRing R] {n : ℕ} (v : Fin n → R) (c : R) :
    vandermondeOf (fun j => v j + c) = vandermondeOf v := by
  unfold vandermondeOf
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  ring

theorem numStandardTable_hookShape_succ (h : FrobeniusDimensionFormula.Statement) {k l : ℕ}
    (hlk : l < k) : numStandardTable (hookShape (l + 1) k l) = Nat.choose (k - 1) l := by
  have hanti : Antitone (hookShape (l + 1) k l) := by
    intro i j hij
    have hij' : (i : ℕ) ≤ j := hij
    unfold hookShape
    split_ifs <;> omega
  have e0 : hookShape (l + 1) k l 0 + (l + 1 - 1 - ((0 : Fin (l + 1)) : ℕ)) = k := by
    simp [hookShape]
    omega
  have es : ∀ j : Fin l, hookShape (l + 1) k l j.succ + (l + 1 - 1 - ((j.succ : Fin (l + 1)) : ℕ)) =
      (0 + (l - 1 - (j : ℕ))) + 1 := by
    intro j
    have := j.isLt
    unfold hookShape
    rw [Fin.val_succ, if_neg (by omega), if_pos (by omega)]
    omega
  have hsum : ∑ i, hookShape (l + 1) k l i = k := by
    rw [Fin.sum_univ_succ]
    have hs1 : ∀ j : Fin l, hookShape (l + 1) k l j.succ = 1 := fun j => by
      have h1 := es j
      have h2 := j.isLt
      have h3 : ((j.succ : Fin (l + 1)) : ℕ) = j + 1 := Fin.val_succ j
      omega
    simp only [hs1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
    have := e0
    have hval : ((0 : Fin (l + 1)) : ℕ) = 0 := rfl
    omega
  have hf := h (l + 1) (hookShape (l + 1) k l) hanti
  simp only [vandermondeOf_succ, Fin.prod_univ_succ] at hf
  rw [e0, hsum] at hf
  simp only [es] at hf
  have hz := h l (fun _ => 0) antitone_const
  beta_reduce at hz
  rw [numStandardTable_zero] at hz
  simp only [Finset.sum_const_zero, Nat.factorial_zero, Nat.cast_one, one_mul] at hz
  set V := vandermondeOf (fun j : Fin l => ((0 + (l - 1 - (j : ℕ)) : ℕ) : ℚ)) with hV
  set P := ∏ j : Fin l, ((0 + (l - 1 - (j : ℕ))).factorial : ℚ) with hP
  have hP0 : P ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => by positivity
  have hVP : V = P := by
    field_simp at hz
    exact hz.symm
  have hshift : vandermondeOf (fun j : Fin l => (((0 + (l - 1 - (j : ℕ))) + 1 : ℕ) : ℚ)) = V := by
    rw [hV, ← vandermondeOf_add_const (fun j : Fin l => ((0 + (l - 1 - (j : ℕ)) : ℕ) : ℚ)) 1]
    congr 1
    funext j
    push_cast
    ring
  have hnum : ∏ j : Fin l, ((k : ℚ) - (((0 + (l - 1 - (j : ℕ))) + 1 : ℕ) : ℚ)) =
      ((k - 1).descFactorial l : ℚ) := by
    rw [← prod_range_sub_eq_descFactorial, Nat.cast_prod,
      ← Finset.prod_range_reflect (fun j => ((k - 1 - j : ℕ) : ℚ)) l,
      ← Fin.prod_univ_eq_prod_range (fun j => ((k - 1 - (l - 1 - j) : ℕ) : ℚ)) l]
    refine Finset.prod_congr rfl fun j _ => ?_
    have := j.isLt
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    ring
  have hden : ∏ j : Fin l, (((0 + (l - 1 - (j : ℕ))) + 1 : ℕ).factorial : ℚ) =
      (l.factorial : ℚ) * P := by
    rw [hP, ← prod_fin_sub_eq_factorial, Nat.cast_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    have := j.isLt
    rw [Nat.factorial_succ, Nat.cast_mul]
    congr 2
    omega
  rw [hnum, hshift, hden, hVP, Nat.descFactorial_eq_factorial_mul_choose] at hf
  have hk0 : ((k.factorial : ℕ) : ℚ) ≠ 0 := by positivity
  have hl0 : ((l.factorial : ℕ) : ℚ) ≠ 0 := by positivity
  have : (numStandardTable (hookShape (l + 1) k l) : ℚ) = ((k - 1).choose l : ℚ) := by
    rw [hf]
    push_cast
    field_simp
  exact_mod_cast this

theorem HookTableauCount.proof (h : FrobeniusDimensionFormula.Statement) :
    HookTableauCount.Statement := by
  intro r k l hlk hlr
  rw [← YoungDiagramCombinatorics.numSYT_hookShape r k l hlr, YoungDiagramCombinatorics.numSYT_hookShape (l + 1) k l (by omega)]
  exact numStandardTable_hookShape_succ h hlk

end GroundTheory.Heights₂.Heights.RestTerms
end
