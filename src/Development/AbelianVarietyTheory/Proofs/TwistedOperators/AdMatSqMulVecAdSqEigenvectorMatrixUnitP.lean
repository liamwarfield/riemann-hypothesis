module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousExptPY
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SelfDualAt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdMatSqMulVecAdSqEigenvectorMatrixUnitP
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdMatSqMulVecAdSqEigenvectorMatrixUnitP
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

noncomputable section
namespace GlobalTheory.PolarU

variable {p q : ℕ}

def posMat (p q : ℕ) (f : Bool → ℕ → Bool → ℕ → ℂ) : Mat p q :=
  Matrix.of fun a b => f a.isLeft (posIx a) b.isLeft (posIx b)

theorem sum_ite_val {n : ℕ} (m : ℕ) (g : ℕ → ℂ) :
    (∑ j : Fin n, if m = (j : ℕ) then g j else 0) = if m < n then g m else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single (⟨m, h⟩ : Fin n)]
    · simp
    · intro b _ hb
      rw [if_neg]
      rintro rfl
      exact hb rfl
    · simp
  · refine Finset.sum_eq_zero fun j _ => if_neg ?_
    rintro rfl
    exact h j.2

theorem posIx_inl (i : Fin p) : posIx (Sum.inl i : Ix p q) = i := rfl

theorem posIx_inr (j : Fin q) : posIx (Sum.inr j : Ix p q) = j := rfl

theorem aOf_apply (h : ℕ → ℝ) (a b : Ix p q) :
    aOf p q h a b = if a.isLeft = b.isLeft then 0
      else if posIx a = posIx b then ((h (posIx a) : ℝ) : ℂ) else 0 := by
  rcases a with i | i <;> rcases b with j | j <;> by_cases hij : (i : ℕ) = j <;>
    simp [aOf, pOf, posIx_inl, posIx_inr, hij, eq_comm (a := (j : ℕ))]

theorem aOf_symm (h : ℕ → ℝ) (a b : Ix p q) : aOf p q h a b = aOf p q h b a := by
  rw [aOf_apply, aOf_apply]
  by_cases h1 : a.isLeft = b.isLeft
  · simp [h1]
  · by_cases h2 : posIx a = posIx b
    · simp [h1, Ne.symm h1, h2]
    · simp [h1, Ne.symm h1, h2, Ne.symm h2]

theorem sum_aOf (h : ℕ → ℝ) (a : Ix p q) (g : Bool → ℕ → ℂ) :
    ∑ c, aOf p q h a c * g c.isLeft (posIx c)
      = (cutH p q h (posIx a) : ℂ) * g (!a.isLeft) (posIx a) := by
  rw [Fintype.sum_sum_type]
  rcases a with i | i
  · have h1 : ∀ k : Fin p, aOf p q h (Sum.inl i) (Sum.inl k) = 0 := fun k => by simp [aOf_apply]
    have h2 : ∀ k : Fin q, aOf p q h (Sum.inl i) (Sum.inr k) * g false k
        = if (i : ℕ) = k then ((h i : ℝ) : ℂ) * g false k else 0 := fun k => by
      by_cases hk : (i : ℕ) = k <;> simp [aOf_apply, posIx_inl, posIx_inr, hk]
    simp only [h1, posIx_inl, posIx_inr, Sum.isLeft_inl, Sum.isLeft_inr, h2, zero_mul,
      Finset.sum_const_zero, zero_add, Bool.not_true]
    rw [sum_ite_val (n := q) i (fun m => ((h i : ℝ) : ℂ) * g false m)]
    by_cases hi : (i : ℕ) < q <;> simp [cutH, hi]
  · have h1 : ∀ k : Fin q, aOf p q h (Sum.inr i) (Sum.inr k) = 0 := fun k => by simp [aOf_apply]
    have h2 : ∀ k : Fin p, aOf p q h (Sum.inr i) (Sum.inl k) * g true k
        = if (i : ℕ) = k then ((h i : ℝ) : ℂ) * g true k else 0 := fun k => by
      by_cases hk : (i : ℕ) = k <;> simp [aOf_apply, posIx_inl, posIx_inr, hk]
    simp only [h1, posIx_inl, posIx_inr, Sum.isLeft_inl, Sum.isLeft_inr, h2, zero_mul,
      Finset.sum_const_zero, add_zero, Bool.not_false]
    rw [sum_ite_val (n := p) i (fun m => ((h i : ℝ) : ℂ) * g true m)]
    by_cases hi : (i : ℕ) < p <;> simp [cutH, hi]

theorem ad_aOf_posMat (h : ℕ → ℝ) (f : Bool → ℕ → Bool → ℕ → ℂ) :
    aOf p q h * posMat p q f - posMat p q f * aOf p q h
      = posMat p q fun s m t n =>
        (cutH p q h m : ℂ) * f (!s) m t n - (cutH p q h n : ℂ) * f s m (!t) n := by
  ext a b
  simp only [Matrix.sub_apply, Matrix.mul_apply, posMat, Matrix.of_apply]
  rw [sum_aOf h a (fun s m => f s m b.isLeft (posIx b)),
    ← sum_aOf h b (fun t n => f a.isLeft (posIx a) t n)]
  congr 1
  exact Finset.sum_congr rfl fun c _ => by rw [mul_comm, aOf_symm]

theorem eigP_eq_posMat (ab : PIx p q) :
    eigP ab.1 = vecM (posMat p q fun s m t n =>
      if s ≠ t ∧ m = posIx ab.1.1 ∧ n = posIx ab.1.2 then
        (if ab.1.1.isLeft then 1 else if s then -1 else 1) else 0) := by
  obtain ⟨⟨a, b⟩, hab⟩ := ab
  funext ⟨c, d⟩
  rcases a with i | i <;> rcases b with j | j <;> simp only [sameBlock, not_true] at hab <;>
    rcases c with k | k <;> rcases d with l | l <;>
    simp [eigP, vecM, posMat, posIx_inl, posIx_inr, sameBlock, Fin.ext_iff]
  split_ifs <;> rfl

theorem adMat_sq_mulVec_eigP (p q : ℕ) (h : ℕ → ℝ) (ab : PIx p q) :
    (adMat (aOf p q h) ^ 2) *ᵥ eigP ab.1 = (((rootP h ab.1 : ℝ) : ℂ) ^ 2) • eigP ab.1 := by
  rw [pow_two (adMat _), ← Matrix.mulVec_mulVec, eigP_eq_posMat, adMat_mulVec, ad_aOf_posMat,
    adMat_mulVec, ad_aOf_posMat]
  funext ⟨c, d⟩
  simp only [vecM, posMat, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, rootP, Bool.not_not]
  generalize c.isLeft = s
  generalize d.isLeft = t
  generalize ab.1.1.isLeft = u
  by_cases hm : posIx c = posIx ab.1.1 ∧ posIx d = posIx ab.1.2
  · rw [hm.1, hm.2]
    cases s <;> cases t <;> cases u <;> simp <;> ring
  · simp [hm]

end GlobalTheory.PolarU
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdMatSqMulVecAdSqEigenvectorMatrixUnitPStatement
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adMat_sq_mulVec_adSqEigenvectorMatrixUnitP : ∀ (p q : ℕ) (h : ℕ → ℝ) (ab : PIx p q), (adMat (aOf p q h) ^ 2) *ᵥ eigP ab.1 = (((rootP h ab.1 : ℝ) : ℂ) ^ 2) • eigP ab.1 := by
  first | exact @GlobalTheory.PolarU.adMat_sq_mulVec_eigP | exact GlobalTheory.PolarU.adMat_sq_mulVec_eigP | (intros; apply GlobalTheory.PolarU.adMat_sq_mulVec_eigP <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProdSinhcRootValueOfMatrixUnitP
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProdSinhcRootValueOfMatrixUnitP
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

namespace GlobalTheory.PolarU.RootProd

theorem shc_neg' (x : ℝ) : shc (-x) = shc x := by
  unfold shc
  by_cases hx : x = 0
  · simp [hx]
  · rw [if_neg (neg_ne_zero.mpr hx), if_neg hx, Real.sinh_neg, neg_div_neg_eq]

theorem shc_zero' : shc 0 = 1 := by
  unfold shc
  exact if_pos rfl

theorem prod_square (n : ℕ) (F : ℕ → ℕ → ℝ) :
    ∏ i ∈ Finset.range n, ∏ j ∈ Finset.range n, F i j =
      (∏ i ∈ Finset.range n, F i i) *
        ∏ i ∈ Finset.range n, ∏ j ∈ Finset.range n, if i < j then F i j * F j i else 1 := by

  have split3 : ∀ i j, F i j = (if j = i then F i i else 1) * (if i < j then F i j else 1) *
      (if j < i then F i j else 1) := by
    intro i j
    rcases lt_trichotomy i j with hij | rfl | hji
    · simp [hij, hij.ne', not_lt.mpr hij.le]
    · simp
    · simp [hji, hji.ne, not_lt.mpr hji.le]
  have row : ∀ i ∈ Finset.range n, (∏ j ∈ Finset.range n, F i j) =
      F i i * ((∏ j ∈ Finset.range n, if i < j then F i j else 1) *
        ∏ j ∈ Finset.range n, if j < i then F i j else 1) := by
    intro i hi
    have hd : (∏ j ∈ Finset.range n, if j = i then F i i else 1) = F i i := by
      rw [Finset.prod_ite_eq']
      exact if_pos hi
    rw [← Finset.prod_mul_distrib, ← hd, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun j _ => by rw [← mul_assoc]; exact split3 i j

  have below : (∏ i ∈ Finset.range n, ∏ j ∈ Finset.range n, if j < i then F i j else 1) =
      ∏ i ∈ Finset.range n, ∏ j ∈ Finset.range n, if i < j then F j i else 1 :=
    Finset.prod_comm
  rw [Finset.prod_congr rfl row, Finset.prod_mul_distrib, Finset.prod_mul_distrib, below,
    ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  split_ifs <;> simp

theorem prod_PIx (p q : ℕ) (h : ℕ → ℝ) :
    ∏ ab : PIx p q, shc (rootP h ab.1) =
      ∏ i ∈ Finset.range p, ∏ j ∈ Finset.range q,
        shc (cutH p q h i - cutH p q h j) * shc (cutH p q h i + cutH p q h j) := by

  rw [← Finset.prod_subtype (Finset.univ.filter fun ab : Ix p q × Ix p q => ¬ sameBlock ab.1 ab.2)
    (fun ab => by simp) (fun ab => shc (rootP h ab))]
  rw [Finset.prod_filter, Fintype.prod_prod_type]
  simp only [Fintype.prod_sum_type, sameBlock, not_true_eq_false, not_false_eq_true, if_false,
    if_true, Finset.prod_const_one, one_mul, mul_one, rootP, Sum.isLeft_inl, Sum.isLeft_inr,
    posIx, Sum.elim_inl, Sum.elim_inr, Bool.false_eq_true]
  simp_rw [Finset.prod_range, Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_comm]
  exact Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => by rw [add_comm]

theorem prod_rect (m d : ℕ) (h c : ℕ → ℝ) (hc : ∀ n, c n = if n < m then h n else 0) :
    ∏ i ∈ Finset.range m, ∏ j ∈ Finset.range (m + d), shc (c i - c j) * shc (c i + c j) =
      (∏ i ∈ Finset.range m, shc (2 * h i) * shc (h i) ^ (2 * d)) *
        ∏ i ∈ Finset.range m, ∏ j ∈ Finset.range m,
          if i < j then (shc (h i - h j) * shc (h i + h j)) ^ 2 else 1 := by
  have hin : ∀ i ∈ Finset.range m, c i = h i := fun i hi => by
    rw [hc, if_pos (Finset.mem_range.mp hi)]
  have hout : ∀ k, c (m + k) = 0 := fun k => by
    rw [hc, if_neg (by omega)]

  have swap : ∀ a b : ℝ, shc (b - a) * shc (b + a) = shc (a - b) * shc (a + b) := fun a b => by
    rw [show b - a = -(a - b) by ring, shc_neg', add_comm b a]

  have row : ∀ i ∈ Finset.range m,
      (∏ j ∈ Finset.range (m + d), shc (c i - c j) * shc (c i + c j)) =
        (∏ j ∈ Finset.range m, shc (h i - h j) * shc (h i + h j)) * shc (h i) ^ (2 * d) := by
    intro i hi
    rw [Finset.prod_range_add]
    congr 1
    · exact Finset.prod_congr rfl fun j hj => by rw [hin i hi, hin j hj]
    · simp only [hout, hin i hi, sub_zero, add_zero]
      rw [Finset.prod_const, Finset.card_range, ← pow_two, ← pow_mul]
  have diag : ∀ i, shc (h i - h i) * shc (h i + h i) = shc (2 * h i) := fun i => by
    rw [sub_self, shc_zero', one_mul, two_mul]
  have off : ∀ i j, (if i < j then shc (h i - h j) * shc (h i + h j) * (shc (h j - h i) * shc (h j + h i))
      else 1) = if i < j then (shc (h i - h j) * shc (h i + h j)) ^ 2 else 1 := fun i j => by
    rw [swap (h i) (h j), sq]
  rw [Finset.prod_congr rfl row, Finset.prod_mul_distrib,
    prod_square m (fun i j => shc (h i - h j) * shc (h i + h j))]
  simp only [diag]
  rw [Finset.prod_mul_distrib,
    Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => off i j]
  ring

theorem prod_shc_rootP : ∀ (p q : ℕ) (h : ℕ → ℝ), ∏ ab : PIx p q, shc (rootP h ab.1) = (∏ i ∈ Finset.range (min p q), shc (2 * h i) * shc (h i) ^ (2 * (max p q - min p q))) * ∏ i ∈ Finset.range (min p q), ∏ j ∈ Finset.range (min p q), if i < j then (shc (h i - h j) * shc (h i + h j)) ^ 2 else 1 := by
  intro p q h
  have hm : min p q + (max p q - min p q) = max p q := Nat.add_sub_cancel' min_le_max
  have swap : ∀ a b : ℝ, shc (b - a) * shc (b + a) = shc (a - b) * shc (a + b) := fun a b => by
    rw [show b - a = -(a - b) by ring, shc_neg', add_comm b a]
  rw [← prod_rect (min p q) (max p q - min p q) h (cutH p q h) (fun n => rfl), hm, prod_PIx]
  rcases le_total p q with hpq | hqp
  · rw [min_eq_left hpq, max_eq_right hpq]
  ·
    rw [min_eq_right hqp, max_eq_left hqp, Finset.prod_comm]
    exact Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => swap _ _

end GlobalTheory.PolarU.RootProd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProdSinhcRootValueOfMatrixUnitPStatement
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_sinhc_rootValueOfMatrixUnitP : ∀ (p q : ℕ) (h : ℕ → ℝ), ∏ ab : PIx p q, shc (rootP h ab.1) = (∏ i ∈ Finset.range (min p q), shc (2 * h i) * shc (h i) ^ (2 * (max p q - min p q))) * ∏ i ∈ Finset.range (min p q), ∏ j ∈ Finset.range (min p q), if i < j then (shc (h i - h j) * shc (h i + h j)) ^ 2 else 1 := by
  first | exact @GlobalTheory.PolarU.RootProd.prod_shc_rootP | exact GlobalTheory.PolarU.RootProd.prod_shc_rootP | (intros; apply GlobalTheory.PolarU.RootProd.prod_shc_rootP <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolarJacobianBlockDiagConjInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolarJacobianBlockDiagConjInvariant
noncomputable section
namespace GlobalTheory.PolarU.Conj
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory
open scoped Kronecker

theorem conj_pow_of_mul_eq_one {n : Type} [Fintype n] [DecidableEq n] (A A' S : Matrix n n ℂ)
    (h : A * A' = 1) (m : ℕ) : (A * S * A') ^ m = A * S ^ m * A' := by
  have h' : A' * A = 1 := mul_eq_one_comm.mp h
  induction m with
  | zero => simp [h]
  | succ m ih =>
    rw [pow_succ, ih, pow_succ]
    calc A * S ^ m * A' * (A * S * A') = A * S ^ m * (A' * A) * S * A' := by
          simp only [mul_assoc]
      _ = A * (S ^ m * S) * A' := by rw [h', mul_one]; simp only [mul_assoc]

theorem conj_tsum_of_mul_eq_one {n : Type} [Fintype n] [DecidableEq n] (A A' : Matrix n n ℂ)
    (h : A * A' = 1) (f : ℕ → Matrix n n ℂ) :
    A * (∑' m, f m) * A' = ∑' m, A * f m * A' := by
  have h' : A' * A = 1 := mul_eq_one_comm.mp h
  by_cases hf : Summable f
  · rw [← hf.tsum_mul_left A, ← (hf.mul_left A).tsum_mul_right A']
  · have hg : ¬ Summable (fun m => A * f m * A') := by
      intro hg
      apply hf
      have hs := (hg.mul_left A').mul_right A
      refine hs.congr (fun m => ?_)
      rw [show A' * (A * f m * A') * A = (A' * A) * f m * (A' * A) by simp only [mul_assoc],
        h', one_mul, mul_one]
    rw [tsum_eq_zero_of_not_summable hf, tsum_eq_zero_of_not_summable hg]
    simp

theorem submatrix_mul_of_left {n : Type} [Fintype n] (P : n → Prop) [DecidablePred P]
    (A S : Matrix n n ℂ) (hA : ∀ i j, P i → ¬ P j → A i j = 0) :
    (A * S).submatrix (Subtype.val : {i // P i} → n) (Subtype.val : {i // P i} → n) =
      A.submatrix Subtype.val (Subtype.val : {i // P i} → n) *
        S.submatrix Subtype.val Subtype.val := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  have key : ∀ k ∈ (Finset.univ : Finset n), A (i : n) k * S k (j : n) ≠ 0 → P k := by
    intro k _ hk
    by_contra hPk
    exact hk (by rw [hA _ _ i.2 hPk, zero_mul])
  rw [← Finset.sum_filter_of_ne key]
  exact Finset.sum_subtype _ (by simp) (fun k => A (i : n) k * S k (j : n))

theorem submatrix_mul_of_right {n : Type} [Fintype n] (P : n → Prop) [DecidablePred P]
    (S A : Matrix n n ℂ) (hA : ∀ i j, ¬ P i → P j → A i j = 0) :
    (S * A).submatrix (Subtype.val : {i // P i} → n) (Subtype.val : {i // P i} → n) =
      S.submatrix Subtype.val (Subtype.val : {i // P i} → n) *
        A.submatrix Subtype.val Subtype.val := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  have key : ∀ k ∈ (Finset.univ : Finset n), S (i : n) k * A k (j : n) ≠ 0 → P k := by
    intro k _ hk
    by_contra hPk
    exact hk (by rw [hA _ _ hPk j.2, mul_zero])
  rw [← Finset.sum_filter_of_ne key]
  exact Finset.sum_subtype _ (by simp) (fun k => S (i : n) k * A k (j : n))

variable {p q : ℕ}

theorem kron_noMix {k l : Mat p q} (hk : IsKC k) (hl : IsKC l) (i j : Ix p q × Ix p q)
    (h : ¬ (sameBlock i.1 i.2 ↔ sameBlock j.1 j.2)) : (k ⊗ₖ lᵀ) i j = 0 := by
  simp only [Matrix.kroneckerMap_apply, Matrix.transpose_apply]
  by_cases h1 : sameBlock i.1 j.1
  · have h2 : ¬ sameBlock j.2 i.2 := by
      intro h2
      apply h
      rcases i with ⟨a | a, b | b⟩ <;> rcases j with ⟨c | c, d | d⟩ <;> simp_all [sameBlock]
    rw [hl _ _ h2, mul_zero]
  · rw [hk _ _ h1, zero_mul]

theorem kron_mul_eq_one {k k' : Mat p q} (h : k * k' = 1) :
    (k ⊗ₖ k'ᵀ) * (k' ⊗ₖ kᵀ) = 1 := by
  rw [← Matrix.mul_kronecker_mul, ← Matrix.transpose_mul, h, Matrix.transpose_one,
    Matrix.one_kronecker_one]

theorem adMat_conj {k k' : Mat p q} (h : k * k' = 1) (Y : Mat p q) :
    adMat (k * Y * k') = (k ⊗ₖ k'ᵀ) * adMat Y * (k' ⊗ₖ kᵀ) := by
  have h1 : k'ᵀ * kᵀ = 1 := by rw [← Matrix.transpose_mul, h, Matrix.transpose_one]
  unfold adMat
  rw [Matrix.mul_sub, Matrix.sub_mul]
  simp only [← Matrix.mul_kronecker_mul]
  simp [h, h1, Matrix.transpose_mul, mul_assoc]

theorem sinhcAd_conj {k k' : Mat p q} (h : k * k' = 1) (Y : Mat p q) :
    sinhcAd (k * Y * k') = (k ⊗ₖ k'ᵀ) * sinhcAd Y * (k' ⊗ₖ kᵀ) := by
  unfold sinhcAd
  rw [adMat_conj h, conj_tsum_of_mul_eq_one _ _ (kron_mul_eq_one h)]
  refine tsum_congr (fun j => ?_)
  rw [conj_pow_of_mul_eq_one _ _ _ (kron_mul_eq_one h), Matrix.mul_smul, Matrix.smul_mul]

theorem polJ_conj (p q : ℕ) (k k' Y : Mat p q) (h : k * k' = 1) (hk : IsKC k) (hk' : IsKC k') :
    polJ (k * Y * k') = polJ Y := by
  unfold polJ
  rw [sinhcAd_conj h]
  have hK : ∀ i j : Ix p q × Ix p q, ¬ sameBlock i.1 i.2 → ¬ ¬ sameBlock j.1 j.2 →
      (k ⊗ₖ k'ᵀ) i j = 0 := fun i j hi hj => kron_noMix hk hk' i j (by tauto)
  have hK' : ∀ i j : Ix p q × Ix p q, ¬ ¬ sameBlock i.1 i.2 → ¬ sameBlock j.1 j.2 →
      (k' ⊗ₖ kᵀ) i j = 0 := fun i j hi hj => kron_noMix hk' hk i j (by tauto)
  have e1 : ((k ⊗ₖ k'ᵀ) * sinhcAd Y * (k' ⊗ₖ kᵀ)).submatrix (Subtype.val : PIx p q → _)
      Subtype.val = ((k ⊗ₖ k'ᵀ) * sinhcAd Y).submatrix (Subtype.val : PIx p q → _) Subtype.val *
        (k' ⊗ₖ kᵀ).submatrix Subtype.val Subtype.val :=
    submatrix_mul_of_right (fun ab : Ix p q × Ix p q => ¬ sameBlock ab.1 ab.2) _ _ hK'
  have e2 : ((k ⊗ₖ k'ᵀ) * sinhcAd Y).submatrix (Subtype.val : PIx p q → _) Subtype.val =
      (k ⊗ₖ k'ᵀ).submatrix (Subtype.val : PIx p q → _) Subtype.val *
        (sinhcAd Y).submatrix Subtype.val Subtype.val :=
    submatrix_mul_of_left (fun ab : Ix p q × Ix p q => ¬ sameBlock ab.1 ab.2) _ _ hK
  have e3 : ((k ⊗ₖ k'ᵀ) * (k' ⊗ₖ kᵀ)).submatrix (Subtype.val : PIx p q → _) Subtype.val =
      (k ⊗ₖ k'ᵀ).submatrix (Subtype.val : PIx p q → _) Subtype.val *
        (k' ⊗ₖ kᵀ).submatrix Subtype.val Subtype.val :=
    submatrix_mul_of_left (fun ab : Ix p q × Ix p q => ¬ sameBlock ab.1 ab.2) _ _ hK
  rw [kron_mul_eq_one h, Matrix.submatrix_one _ Subtype.val_injective] at e3
  have e5 := congrArg Matrix.det e3
  rw [Matrix.det_one, Matrix.det_mul] at e5
  rw [e1, e2, Matrix.det_mul, Matrix.det_mul, mul_right_comm, ← e5, one_mul]

end GlobalTheory.PolarU.Conj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolarJacobianBlockDiagConjInvariantStatement
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarJacobian_blockDiag_conj_invariant : ∀ (p q : ℕ) (k k' Y : Mat p q), k * k' = 1 → IsKC k → IsKC k' → polJ (k * Y * k') = polJ Y := by
  first | exact @GlobalTheory.PolarU.Conj.polJ_conj | exact GlobalTheory.PolarU.Conj.polJ_conj | (intros; apply GlobalTheory.PolarU.Conj.polJ_conj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetSinhcAdjointUpperRightCoordEqPolJ
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetComplexification
namespace GlobalTheory.PolarU

open Module

theorem det_complexification (E W : Type) [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    [AddCommGroup W] [Module ℂ W] (j : E →+ W) (T : E →ₗ[ℝ] E) (S : W →ₗ[ℂ] W)
    (hj : ∀ (t : ℝ) (x : E), j (t • x) = (t : ℂ) • j x)
    (hspan : ∀ w, ∃ a b, w = j a + Complex.I • j b)
    (hinj : ∀ a b, j a + Complex.I • j b = 0 → a = 0 ∧ b = 0)
    (hS : ∀ x, S (j x) = j (T x)) :
    LinearMap.det S = ((LinearMap.det T : ℝ) : ℂ) := by
  classical
  let bE := Module.finBasis ℝ E
  let v : Fin (Module.finrank ℝ E) → W := fun i => j (bE i)

  have hsum : ∀ c : Fin (Module.finrank ℝ E) → ℝ, j (∑ i, c i • bE i) = ∑ i, (c i : ℂ) • v i := by
    intro c
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl (fun i _ => hj (c i) (bE i))

  have hli : LinearIndependent ℂ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have key : j (∑ k, (g k).re • bE k) + Complex.I • j (∑ k, (g k).im • bE k) = 0 := by
      rw [hsum, hsum, Finset.smul_sum, ← Finset.sum_add_distrib]
      refine (Finset.sum_congr rfl (fun k _ => ?_)).trans hg
      rw [smul_smul, ← add_smul, mul_comm Complex.I, Complex.re_add_im]
    obtain ⟨h1, h2⟩ := hinj _ _ key
    have r1 := Fintype.linearIndependent_iff.mp bE.linearIndependent (fun k => (g k).re) h1 i
    have r2 := Fintype.linearIndependent_iff.mp bE.linearIndependent (fun k => (g k).im) h2 i
    exact Complex.ext (by simpa using r1) (by simpa using r2)

  have hsp : ⊤ ≤ Submodule.span ℂ (Set.range v) := by
    have hmem : ∀ a : E, j a ∈ Submodule.span ℂ (Set.range v) := by
      intro a
      rw [← bE.sum_repr a, hsum]
      exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
    intro w _
    obtain ⟨a, b, rfl⟩ := hspan w
    exact Submodule.add_mem _ (hmem a) (Submodule.smul_mem _ _ (hmem b))
  let bW : Basis (Fin (Module.finrank ℝ E)) ℂ W := Basis.mk hli hsp
  have hbW : ∀ i, bW i = v i := fun i => Basis.mk_apply hli hsp i

  have hmat : LinearMap.toMatrix bW bW S = (LinearMap.toMatrix bE bE T).map Complex.ofRealHom := by
    ext i k
    have e : S (bW k) = ∑ l, ((bE.repr (T (bE k)) l : ℝ) : ℂ) • bW l := by
      simp only [hbW]
      rw [← hsum (bE.repr (T (bE k))), bE.sum_repr]
      exact hS (bE k)
    rw [LinearMap.toMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply, e, bW.repr_sum_self]
    rfl
  rw [← LinearMap.det_toMatrix bW S, ← LinearMap.det_toMatrix bE T, hmat]
  exact (RingHom.map_det Complex.ofRealHom _).symm

end GlobalTheory.PolarU
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetSinhcAdjointUpperRightCoordEqPolJ
namespace GlobalTheory.PolarU
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

noncomputable def pCoord (p q : ℕ) : (Fin p → Fin q → ℂ) →+ (PIx p q → ℂ) where
  toFun C := fun ab => pY C ab.1.1 ab.1.2
  map_zero' := by
    funext ⟨⟨a, b⟩, h⟩
    cases a <;> cases b <;> simp [pY, pOf]
  map_add' B C := by funext ab; simp [pY_add]

theorem pCoord_apply {p q : ℕ} (C : Fin p → Fin q → ℂ) (ab : PIx p q) :
    pCoord p q C ab = pY C ab.1.1 ab.1.2 := rfl

private lemma pY_inl_inr {p q : ℕ} (C : Fin p → Fin q → ℂ) (i : Fin p) (j : Fin q) :
    pY C (Sum.inl i) (Sum.inr j) = C i j := by
  simp [pY, pOf]

private lemma pY_inr_inl {p q : ℕ} (C : Fin p → Fin q → ℂ) (i : Fin p) (j : Fin q) :
    pY C (Sum.inr j) (Sum.inl i) = star (C i j) := by
  simp [pY, pOf]

private lemma pY_eq_zero_of_sameBlock {p q : ℕ} (C : Fin p → Fin q → ℂ) (a b : Ix p q)
    (h : sameBlock a b) : pY C a b = 0 := by
  rcases a with a | a <;> rcases b with b | b <;> simp_all [sameBlock, pY, pOf]

private lemma not_sameBlock_inl_inr {p q : ℕ} (i : Fin p) (j : Fin q) :
    ¬ sameBlock (Sum.inl i : Ix p q) (Sum.inr j) := by
  simp [sameBlock]

private lemma not_sameBlock_inr_inl {p q : ℕ} (i : Fin p) (j : Fin q) :
    ¬ sameBlock (Sum.inr j : Ix p q) (Sum.inl i) := by
  simp [sameBlock]

theorem det_sinhc_eq_polarJacobian (p q : ℕ) (Y : Mat p q)
    (hY : ∀ C : Fin p → Fin q → ℂ, sAd Y (pY C) = pY (sP Y C)) :
    LinearMap.det (sP Y) = polJ Y := by

  set M : Matrix (PIx p q) (PIx p q) ℂ :=
    (sinhcAd Y).submatrix (Subtype.val : PIx p q → Ix p q × Ix p q) Subtype.val with hM

  have hj : ∀ (t : ℝ) (x : Fin p → Fin q → ℂ), pCoord p q (t • x) = (t : ℂ) • pCoord p q x := by
    intro t x
    funext ab
    simp only [pCoord_apply, pY_smul, Pi.smul_apply, Matrix.smul_apply, Complex.real_smul,
      smul_eq_mul]

  have hspan : ∀ w : PIx p q → ℂ, ∃ a b : Fin p → Fin q → ℂ,
      w = pCoord p q a + Complex.I • pCoord p q b := by
    intro w
    let u : Fin p → Fin q → ℂ := fun i j => w ⟨(Sum.inl i, Sum.inr j), not_sameBlock_inl_inr i j⟩
    let v : Fin p → Fin q → ℂ := fun i j => w ⟨(Sum.inr j, Sum.inl i), not_sameBlock_inr_inl i j⟩
    refine ⟨fun i j => (u i j + star (v i j)) / 2,
      fun i j => -Complex.I * (u i j - star (v i j)) / 2, ?_⟩
    funext ⟨⟨a, b⟩, h⟩
    rcases a with i | j <;> rcases b with j' | i'
    · exact absurd (by simp [sameBlock]) h
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, pCoord_apply, pY_inl_inr]
      apply Complex.ext <;> simp [u] <;> ring
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, pCoord_apply, pY_inr_inl]
      apply Complex.ext <;> simp [v] <;> ring
    · exact absurd (by simp [sameBlock]) h

  have hinj : ∀ a b : Fin p → Fin q → ℂ,
      pCoord p q a + Complex.I • pCoord p q b = 0 → a = 0 ∧ b = 0 := by
    intro a b hab
    have h1 : ∀ i j, a i j + Complex.I * b i j = 0 := fun i j => by
      have := congrFun hab ⟨(Sum.inl i, Sum.inr j), not_sameBlock_inl_inr i j⟩
      simpa [pCoord_apply, pY_inl_inr] using this
    have h2 : ∀ i j, star (a i j) + Complex.I * star (b i j) = 0 := fun i j => by
      have := congrFun hab ⟨(Sum.inr j, Sum.inl i), not_sameBlock_inr_inl i j⟩
      simpa [pCoord_apply, pY_inr_inl] using this
    have hre : ∀ i j, a i j = 0 ∧ b i j = 0 := by
      intro i j
      have e1 := congrArg Complex.re (h1 i j)
      have e2 := congrArg Complex.im (h1 i j)
      have e3 := congrArg Complex.re (h2 i j)
      have e4 := congrArg Complex.im (h2 i j)
      simp at e1 e2 e3 e4
      constructor <;> apply Complex.ext <;> simp <;> linarith
    exact ⟨funext fun i => funext fun j => (hre i j).1,
      funext fun i => funext fun j => (hre i j).2⟩

  have hS : ∀ x, Matrix.toLin' M (pCoord p q x) = pCoord p q (sP Y x) := by
    intro x
    funext ab
    rw [Matrix.toLin'_apply, pCoord_apply, ← hY x]
    simp only [sAd, Matrix.of_apply, Matrix.mulVec, dotProduct, vecM, hM,
      Matrix.submatrix_apply, pCoord_apply]
    rw [← Fintype.sum_subtype_add_sum_subtype (fun cd : Ix p q × Ix p q => ¬ sameBlock cd.1 cd.2)]
    have hz : ∑ cd : {cd : Ix p q × Ix p q // ¬ ¬ sameBlock cd.1 cd.2},
        sinhcAd Y (ab.1.1, ab.1.2) cd.1 * pY x cd.1.1 cd.1.2 = 0 := by
      apply Finset.sum_eq_zero
      intro cd _
      rw [pY_eq_zero_of_sameBlock x _ _ (not_not.mp cd.2), mul_zero]
    rw [hz, add_zero]
  have key := det_complexification (Fin p → Fin q → ℂ) (PIx p q → ℂ) (pCoord p q) (sP Y)
    (Matrix.toLin' M) hj hspan hinj hS
  rw [LinearMap.det_toLin'] at key
  unfold polJ
  rw [← hM, key, Complex.ofReal_re]

end GlobalTheory.PolarU
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetSinhcAdjointUpperRightCoordEqPolJStatement
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_sinhcAdjointUpperRightCoord_eq_polJ : ∀ (p q : ℕ) (Y : Mat p q), (∀ C : Fin p → Fin q → ℂ, sAd Y (pY C) = pY (sP Y C)) → LinearMap.det (sP Y) = polJ Y := by
  first | exact @GlobalTheory.PolarU.det_sinhc_eq_polarJacobian | exact GlobalTheory.PolarU.det_sinhc_eq_polarJacobian | (intros; apply GlobalTheory.PolarU.det_sinhc_eq_polarJacobian <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScalarCapelliTruncatedPerelomovPopov
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScalarCapelliTruncatedPerelomovPopov
open Formalism.REAL Finset Polynomial

namespace GlobalTheory.ScalarNewton

open Matrix

theorem sum_adjugate_eq {R : Type*} [CommRing R] [IsDomain R] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι R) (h : M.det ≠ 0) :
    ∑ a, ∑ b, M.adjugate a b = (M + Matrix.of fun _ _ => (1 : R)).det - M.det := by
  let K := FractionRing R
  let φ : R →+* K := algebraMap R K
  have hinj : Function.Injective φ := IsFractionRing.injective R K
  apply hinj
  have hdet : φ M.det = (M.map φ).det := RingHom.map_det φ M
  have hd0 : (M.map φ).det ≠ 0 := by
    rw [← hdet]; exact (map_ne_zero_iff φ hinj).2 h
  have hd : IsUnit (M.map φ).det := hd0.isUnit
  have hJ : (M + Matrix.of fun _ _ => (1 : R)).map φ =
      M.map φ + replicateCol Unit (fun _ : ι => (1 : K)) * replicateRow Unit (fun _ : ι => (1 : K)) := by
    ext i j; simp [replicateCol, replicateRow, Matrix.mul_apply]
  have hadj : ∀ a b, φ (M.adjugate a b) = (M.map φ).adjugate a b := by
    intro a b
    have := congrFun (congrFun (RingHom.map_adjugate φ M) a) b
    simpa using this
  have key := det_add_replicateCol_mul_replicateRow (ι := Unit) hd (fun _ => (1 : K)) (fun _ => 1)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sub, RingHom.map_det φ, RingHom.map_det φ, map_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, hadj]
  change _ = ((M + Matrix.of fun _ _ => (1 : R)).map φ).det - (M.map φ).det
  rw [hJ, key, det_unique (n := Unit), Matrix.inv_def, Ring.inverse_eq_inv']
  simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.mul_apply, replicateRow_apply, replicateCol_apply,
    Matrix.smul_apply, smul_eq_mul, one_mul, mul_one, Finset.univ_unique, Finset.sum_singleton]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  rw [mul_add, ← mul_assoc, mul_inv_cancel₀ hd0]
  ring

end GlobalTheory.ScalarNewton

namespace GlobalTheory.ScalarNewton

open Matrix

variable (m : ℕ) (χ : Fin (m + 1) → ℂ)

noncomputable def amat : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
  Formalism.REAL.Amat (fun c => χ c + (((m + 1 : ℕ) : ℂ) - 1) / 2)

theorem gelfVal_eq (k : ℕ) : GlobalTheory.Dec.gelfVal χ k = ∑ a, ∑ b, (amat m χ ^ k) a b := rfl

noncomputable def pmat : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ[X] :=
  (X : ℂ[X]) • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ).map C + (amat m χ - (m : ℂ) • 1).map C

theorem pmat_apply (a b : Fin (m + 1)) : pmat m χ a b =
    if a = b then X + C (χ a - (m : ℂ) / 2) else if a < b then -1 else 0 := by
  by_cases h1 : a = b
  · subst h1
    simp [pmat, amat, Formalism.REAL.Amat]
    rw [show ((m : ℂ[X])) = C (m : ℂ) from (map_natCast C m).symm, ← C_add, ← C_sub, ← C_sub]
    congr 1
    ring
  · by_cases h2 : a < b
    · simp [pmat, amat, Formalism.REAL.Amat, h1, h2, Matrix.one_apply]
    · simp [pmat, amat, Formalism.REAL.Amat, h1, h2, Matrix.one_apply]

theorem pmat_eq : pmat m χ = (X - C (m : ℂ)) • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ[X]) + (amat m χ).map C := by
  refine Matrix.ext fun a b => ?_
  by_cases h1 : a = b
  · subst h1
    simp [pmat]
    ring
  · simp [pmat, h1, Matrix.one_apply]

theorem det_pmat : (pmat m χ).det = ∏ s, (X + C (χ s - (m : ℂ) / 2)) := by
  rw [Matrix.det_of_upperTriangular]
  · exact Finset.prod_congr rfl fun s _ => by rw [pmat_apply]; simp
  · intro i j h
    have h' : j < i := h
    rw [pmat_apply, if_neg (ne_of_gt h'), if_neg (not_lt_of_gt h')]

theorem det_pmat_add : (pmat m χ + Matrix.of fun _ _ => (1 : ℂ[X])).det =
    ∏ s, (X + C (χ s - (m : ℂ) / 2 + 1)) := by
  rw [Matrix.det_of_lowerTriangular]
  · exact Finset.prod_congr rfl fun s _ => by rw [Matrix.add_apply, pmat_apply]; simp; ring
  · intro i j h
    have h' : i < j := h
    rw [Matrix.add_apply, pmat_apply, if_neg (ne_of_lt h'), if_pos h']
    simp

theorem det_pmat_ne_zero : (pmat m χ).det ≠ 0 := by
  rw [det_pmat]
  exact Finset.prod_ne_zero_iff.2 fun s _ => X_add_C_ne_zero _

end GlobalTheory.ScalarNewton

namespace GlobalTheory.ScalarNewton

open Matrix

theorem sumEnt_smul {n : ℕ} (c : ℂ[X]) (W : Matrix (Fin n) (Fin n) ℂ[X]) :
    ∑ a, ∑ b, (c • W) a b = c * ∑ a, ∑ b, W a b := by
  simp [Finset.mul_sum]

theorem sumEnt_sub {n : ℕ} (V W : Matrix (Fin n) (Fin n) ℂ[X]) :
    ∑ a, ∑ b, (V - W) a b = ∑ a, ∑ b, V a b - ∑ a, ∑ b, W a b := by
  simp [Finset.sum_sub_distrib]

theorem sumEnt_sum {n : ℕ} (s : Finset ℕ) (W : ℕ → Matrix (Fin n) (Fin n) ℂ[X]) :
    ∑ a, ∑ b, (∑ i ∈ s, W i : Matrix (Fin n) (Fin n) ℂ[X]) a b = ∑ i ∈ s, ∑ a, ∑ b, W i a b := by
  simp only [Matrix.sum_apply]
  calc _ = ∑ a, ∑ i ∈ s, ∑ b, W i a b := Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem poly_identity (m N : ℕ) (χ : Fin (m + 1) → ℂ) :
    (X - C (m : ℂ)) ^ (N + 1) * ((pmat m χ + Matrix.of fun _ _ => (1 : ℂ[X])).det - (pmat m χ).det) -
      (pmat m χ).det * ∑ k ∈ range (N + 1), (-1) ^ k * (X - C (m : ℂ)) ^ (N - k) * C (GlobalTheory.Dec.gelfVal χ k) =
    (-1) ^ (N + 1) * ∑ a, ∑ b, ((pmat m χ).adjugate * ((amat m χ).map C) ^ (N + 1)) a b := by
  set x : ℂ[X] := X - C (m : ℂ)
  set Bm : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ[X] := (amat m χ).map C
  set Mx := pmat m χ
  have hnp : ∀ i : ℕ, (-Bm) ^ i = ((-1 : ℂ[X]) ^ i) • Bm ^ i := by
    intro i; rw [← neg_one_smul ℂ[X] Bm, _root_.smul_pow]
  have hxp : ∀ i : ℕ, (x • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ[X])) ^ i = x ^ i • 1 := by
    intro i; rw [_root_.smul_pow, one_pow]
  have hBp : ∀ i : ℕ, ∑ a, ∑ b, (Bm ^ i) a b = C (GlobalTheory.Dec.gelfVal χ i) := by
    intro i
    set_option synthInstance.maxHeartbeats 100000 in
      rw [gelfVal_eq, map_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum]
    have : Bm ^ i = (amat m χ ^ i).map C := by
      rw [Matrix.map_pow]
    rw [this]
    simp
  have hcomm : Commute (-Bm) (x • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ[X])) :=
    (Commute.one_right _).smul_right x
  have hgeom := hcomm.mul_geom_sum₂ (N + 1)
  set P := ∑ i ∈ range (N + 1), (-Bm) ^ i * (x • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ[X])) ^ (N + 1 - 1 - i)
  have hMP : Mx * P = x ^ (N + 1) • 1 - (-1 : ℂ[X]) ^ (N + 1) • Bm ^ (N + 1) := by
    have : Mx = -(-Bm - x • 1) := by rw [show Mx = pmat m χ from rfl, pmat_eq]; abel
    rw [this, neg_mul, hgeom, hnp, hxp]
    abel
  have hSP : ∑ a, ∑ b, P a b = ∑ k ∈ range (N + 1), (-1) ^ k * x ^ (N - k) * C (GlobalTheory.Dec.gelfVal χ k) := by
    rw [sumEnt_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hnp, hxp, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, sumEnt_smul, hBp]
    simp only [Nat.add_sub_cancel]
  have hadj : Mx.adjugate * Mx = Mx.det • 1 := Matrix.adjugate_mul Mx
  have hdP : Mx.det • P = Mx.adjugate * (Mx * P) := by
    rw [← Matrix.mul_assoc, hadj, Matrix.smul_mul, Matrix.one_mul]
  have hS := congrArg (fun W => ∑ a, ∑ b, W a b) hdP
  rw [sumEnt_smul, hSP, hMP, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one, sumEnt_sub,
    sumEnt_smul, sumEnt_smul, sum_adjugate_eq Mx (det_pmat_ne_zero m χ)] at hS
  rw [hS]
  ring

end GlobalTheory.ScalarNewton

namespace GlobalTheory.ScalarNewton

open Matrix

theorem natDegree_adjugate_pmat_le (m : ℕ) (χ : Fin (m + 1) → ℂ) (i j : Fin (m + 1)) :
    ((pmat m χ).adjugate i j).natDegree ≤ m := by
  rw [adjugate_fin_succ_eq_det_submatrix]
  have h1 : ((-1 : ℂ[X]) ^ ((j : ℕ) + i)) = C ((-1) ^ ((j : ℕ) + i)) := by simp
  rw [h1]
  refine (natDegree_C_mul_le _ _).trans ?_
  have e : (pmat m χ).submatrix j.succAbove i.succAbove =
      (X : ℂ[X]) • ((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ).submatrix j.succAbove i.succAbove).map C +
      ((amat m χ - (m : ℂ) • 1).submatrix j.succAbove i.succAbove).map C := rfl
  rw [e]
  simpa using natDegree_det_X_add_C_le
    ((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ).submatrix j.succAbove i.succAbove)
    ((amat m χ - (m : ℂ) • 1).submatrix j.succAbove i.succAbove)

theorem scalar_newton : ∀ (m N : ℕ) (χ : Fin (m + 1) → ℂ), ∃ r : ℂ[X], r.natDegree ≤ m ∧ ∀ u : ℂ,
    (u - m) ^ (N + 1) * (∏ s, (u + 1 - (m : ℂ) / 2 + χ s) - ∏ s, (u - (m : ℂ) / 2 + χ s)) -
      (∏ s, (u - (m : ℂ) / 2 + χ s)) * ∑ k ∈ range (N + 1), (-1) ^ k * (u - m) ^ (N - k) * GlobalTheory.Dec.gelfVal χ k =
      r.eval u := by
  intro m N χ
  refine ⟨(-1) ^ (N + 1) * ∑ a, ∑ b, ((pmat m χ).adjugate * ((amat m χ).map C) ^ (N + 1)) a b, ?_, ?_⟩
  · have hc : ((-1 : ℂ[X]) ^ (N + 1)) = C ((-1) ^ (N + 1)) := by simp
    rw [hc]
    refine (natDegree_C_mul_le _ _).trans ?_
    refine natDegree_sum_le_of_forall_le _ _ fun a _ => natDegree_sum_le_of_forall_le _ _ fun b _ => ?_
    rw [Matrix.mul_apply]
    refine natDegree_sum_le_of_forall_le _ _ fun c _ => ?_
    rw [← Matrix.map_pow, Matrix.map_apply]
    exact (natDegree_mul_C_le _ _).trans (natDegree_adjugate_pmat_le m χ a c)
  · intro u
    rw [← poly_identity, det_pmat, det_pmat_add]
    simp only [eval_sub, eval_mul, eval_pow, eval_X, eval_C, eval_prod, eval_add, Polynomial.eval_finsetSum, eval_neg,
      eval_one]
    have e1 : ∏ s, (u + (χ s - (m : ℂ) / 2 + 1)) = ∏ s, (u + 1 - (m : ℂ) / 2 + χ s) :=
      Finset.prod_congr rfl fun _ _ => by ring
    have e0 : ∏ s, (u + (χ s - (m : ℂ) / 2)) = ∏ s, (u - (m : ℂ) / 2 + χ s) :=
      Finset.prod_congr rfl fun _ _ => by ring
    rw [e1, e0]

end GlobalTheory.ScalarNewton
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScalarCapelliTruncatedPerelomovPopovStatement
open Formalism.REAL Finset Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scalar_capelli_truncated_perelomov_popov : ∀ (m N : ℕ) (χ : Fin (m + 1) → ℂ), ∃ r : ℂ[X], r.natDegree ≤ m ∧ ∀ u : ℂ, (u - m) ^ (N + 1) * (∏ s, (u + 1 - (m : ℂ) / 2 + χ s) - ∏ s, (u - (m : ℂ) / 2 + χ s)) - (∏ s, (u - (m : ℂ) / 2 + χ s)) * ∑ k ∈ range (N + 1), (-1) ^ k * (u - m) ^ (N - k) * GlobalTheory.Dec.gelfVal χ k = r.eval u := by
  first | exact @GlobalTheory.ScalarNewton.scalar_newton | exact GlobalTheory.ScalarNewton.scalar_newton | (intros; apply GlobalTheory.ScalarNewton.scalar_newton <;> assumption)
end
end
