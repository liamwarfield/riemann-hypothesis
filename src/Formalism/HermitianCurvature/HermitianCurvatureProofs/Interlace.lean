module

public import Formalism.HermitianCurvature.Statement
public import Formalism.HermitianCurvature.StatementG

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.Interlace
namespace Formalism.FourierDecayAlt.P.Interlace

open Finset Formalism.FourierDecayAlt.I

lemma interlaces_swap {k : ℕ} {u u' ρ : ℕ → ℝ} (h : Interlaces k u u' ρ) :
    Interlaces k u' u ρ := by
  intro i hi
  obtain ⟨a, b, c, d⟩ := h i hi
  exact ⟨b, a, d, c⟩

lemma antitone_on {f : ℕ → ℝ} {k : ℕ} (h : ∀ i, 1 ≤ i → i + 1 ≤ k → f (i + 1) ≤ f i) :
    ∀ i j, 1 ≤ i → i ≤ j → j ≤ k → f j ≤ f i := by
  intro i j hi hij hjk
  induction j, hij using Nat.le_induction with
  | base => exact le_refl _
  | succ n hn ih => exact (h n (by omega) hjk).trans (ih (by omega))

lemma u_step {k : ℕ} {u u' ρ : ℕ → ℝ} (h : Interlaces k u u' ρ) :
    ∀ i, 1 ≤ i → i + 1 ≤ k → u (i + 1) ≤ u i := by
  intro i h1 h2
  obtain ⟨a, b, c, d⟩ := h i (mem_Icc.2 ⟨h1, by omega⟩)
  linarith

lemma sign_core (k : ℕ) (u u' ρ : ℕ → ℝ) (l : ℕ) (Y : ℝ) (hl1 : 1 ≤ l) (hlk : l ≤ k)
    (h : Interlaces k u u' ρ) (hA : u l + 2 ≤ -Y ∧ -Y ≤ u' l - 2) (e : ℝ)
    (he : -1 ≤ e ∧ e ≤ 1) :
    0 < (-1 : ℝ) ^ (k - l) * xpoly k ρ (Y + e) := by
  have hu := antitone_on (u_step h)
  have hu' := antitone_on (u_step (interlaces_swap h))
  have hcard : (filter (fun i => ¬ i < l) (Icc 1 (k - 1))).card = k - l := by
    have : filter (fun i => ¬ i < l) (Icc 1 (k - 1)) = Icc l (k - 1) := by
      ext i; simp only [mem_filter, mem_Icc]; omega
    rw [this, Nat.card_Icc]; omega
  have key : (-1 : ℝ) ^ (k - l) * xpoly k ρ (Y + e) =
      ∏ i ∈ Icc 1 (k - 1), ((if i < l then (1 : ℝ) else -1) * (Y + e + ρ i)) := by
    rw [prod_mul_distrib, prod_ite, prod_const_one, one_mul, prod_const, hcard]
    rfl
  rw [key]
  apply prod_pos
  intro i hi
  have hi' := mem_Icc.1 hi
  obtain ⟨a, b, c, d⟩ := h i hi
  split_ifs with hil
  · have := hu' (i + 1) l (by omega) (by omega) hlk
    rw [one_mul]; linarith
  · have := hu l i hl1 (by omega) (by omega)
    rw [neg_one_mul]; linarith

theorem interlaceSign : InterlaceSign := by
  intro k u u' ρ l Y hl1 hlk h hc e he
  have he' : -1 ≤ e ∧ e ≤ 1 := by
    simp only [mem_insert, mem_singleton] at he
    rcases he with rfl | rfl | rfl <;> norm_num
  rcases hc with hA | hB
  · exact sign_core k u u' ρ l Y hl1 hlk h hA e he'
  · exact sign_core k u' u ρ l Y hl1 hlk (interlaces_swap h) hB e he'

lemma q_core (k : ℕ) (u u' ρ : ℕ → ℝ) (l : ℕ) (Y : ℝ) (hl1 : 1 ≤ l) (hlk : l ≤ k)
    (h : Interlaces k u u' ρ) (hA : u l + 2 ≤ -Y ∧ -Y ≤ u' l - 2) :
    ∏ i ∈ Icc 1 k, ((Y + 1/2 + u i) * (Y + 1/2 + u' i)) < 0 := by
  have hu := antitone_on (u_step h)
  have hu' := antitone_on (u_step (interlaces_swap h))
  have hl : l ∈ Icc 1 k := mem_Icc.2 ⟨hl1, hlk⟩
  rw [← mul_prod_erase _ _ hl]
  apply mul_neg_of_neg_of_pos
  · apply mul_neg_of_neg_of_pos <;> linarith
  · apply prod_pos
    intro i hi
    have hne := ne_of_mem_erase hi
    have hi' := mem_Icc.1 (mem_of_mem_erase hi)
    rcases lt_or_gt_of_ne hne with hil | hil
    · obtain ⟨a, b, c, d⟩ := h i (mem_Icc.2 ⟨hi'.1, by omega⟩)
      have h1 := hu' (i + 1) l (by omega) (by omega) hlk
      have h2 := hu' i l hi'.1 (by omega) hlk
      apply mul_pos <;> linarith
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      obtain ⟨a, b, c, d⟩ := h j (mem_Icc.2 ⟨by omega, by omega⟩)
      have h1 := hu l (j + 1) hl1 (by omega) hi'.2
      have h2 := hu l j hl1 (by omega) (by omega)
      apply mul_pos_of_neg_of_neg <;> linarith

theorem qPositive : QPositive := by
  intro k u u' ρ l Y T T' hl1 hlk h hc hT hT'
  have hTT : 0 < T * T' := mul_pos hT hT'
  have hP : ∏ i ∈ Icc 1 k, ((Y + 1/2 + u i) * (Y + 1/2 + u' i)) < 0 := by
    rcases hc with hA | hB
    · exact q_core k u u' ρ l Y hl1 hlk h hA
    · have := q_core k u' u ρ l Y hl1 hlk (interlaces_swap h) hB
      rwa [prod_congr rfl (fun i _ => mul_comm (Y + 1/2 + u' i) (Y + 1/2 + u i))] at this
  unfold qpoly
  nlinarith

lemma ratio_core (k : ℕ) (u u' ρ : ℕ → ℝ) (l : ℕ) (Y : ℝ) (hl1 : 1 ≤ l) (hlk : l ≤ k)
    (h : Interlaces k u u' ρ) (hA : u l + 2 ≤ -Y ∧ -Y ≤ u' l - 2) :
    xpoly k ρ (Y + 1) ^ 2 * (|Y + 1/2 + u l| * |Y + 1/2 + u' l|) ≤
      |(∏ i ∈ Icc 1 k, (Y + 1/2 + u i)) * (∏ i ∈ Icc 1 k, (Y + 1/2 + u' i))| := by
  have hu := antitone_on (u_step h)
  have hu' := antitone_on (u_step (interlaces_swap h))
  set g : ℕ → ℝ := fun j => |Y + 1/2 + u j| * |Y + 1/2 + u' j| with hg
  have hl : l ∈ Icc 1 k := mem_Icc.2 ⟨hl1, hlk⟩
  have hR : |(∏ i ∈ Icc 1 k, (Y + 1/2 + u i)) * (∏ i ∈ Icc 1 k, (Y + 1/2 + u' i))| =
      g l * ∏ i ∈ Icc 1 (k - 1), g (if i < l then i else i + 1) := by
    rw [abs_mul, abs_prod, abs_prod, ← prod_mul_distrib, ← mul_prod_erase _ _ hl]
    congr 1
    symm
    apply prod_nbij' (fun i => if i < l then i else i + 1) (fun j => if j < l then j else j - 1)
    · intro a ha
      simp only [mem_Icc] at ha
      simp only [mem_erase, mem_Icc]
      split_ifs <;> omega
    · intro a ha
      simp only [mem_erase, mem_Icc] at ha
      simp only [mem_Icc]
      split_ifs <;> omega
    · intro a ha
      simp only [mem_Icc] at ha
      split_ifs <;> omega
    · intro a ha
      simp only [mem_erase, mem_Icc] at ha
      split_ifs <;> omega
    · intro a ha
      rfl
  rw [hR, mul_comm]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  unfold xpoly
  rw [← prod_pow]
  apply prod_le_prod₀
  · intro i _; positivity
  · intro i hi
    have hi' := mem_Icc.1 hi
    obtain ⟨a, b, c, d⟩ := h i hi
    simp only [hg]
    split_ifs with hil
    · have h1 := hu' (i + 1) l (by omega) (by omega) hlk
      rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]
      nlinarith
    · have h1 := hu l i hl1 (by omega) (by omega)
      rw [abs_of_neg (by linarith), abs_of_neg (by linarith)]
      nlinarith

theorem interlaceRatio : InterlaceRatio := by
  intro k u u' ρ l Y hl1 hlk h hc
  rcases hc with hA | hB
  · exact ratio_core k u u' ρ l Y hl1 hlk h hA
  · have := ratio_core k u' u ρ l Y hl1 hlk (interlaces_swap h) hB
    rwa [mul_comm (|Y + 1/2 + u' l|), mul_comm (∏ i ∈ Icc 1 k, (Y + 1/2 + u' i))] at this

end Formalism.FourierDecayAlt.P.Interlace

theorem Formalism.FourierDecayAlt.P.interlacing_sign : Formalism.FourierDecayAlt.I.InterlaceSign := Formalism.FourierDecayAlt.P.Interlace.interlaceSign
theorem Formalism.FourierDecayAlt.P.q_positive_interlacing : Formalism.FourierDecayAlt.I.QPositive := Formalism.FourierDecayAlt.P.Interlace.qPositive
theorem Formalism.FourierDecayAlt.P.interlacing_ratio : Formalism.FourierDecayAlt.I.InterlaceRatio := Formalism.FourierDecayAlt.P.Interlace.interlaceRatio
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.AdditiveCharacterPsi
open Matrix MeasureTheory

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace Formalism.FourierDecayAlt.P.G2

open Formalism.FourierDecayAlt.G

theorem symm_castSucc {n : ℕ} (i : Fin n) :
    finSumFinEquiv.symm (i.castSucc : Fin (n + 1)) = Sum.inl i :=
  finSumFinEquiv_symm_apply_castAdd (n := 1) i

theorem symm_last (n : ℕ) : finSumFinEquiv.symm (Fin.last n : Fin (n + 1)) = Sum.inr (0 : Fin 1) :=
  finSumFinEquiv_symm_apply_natAdd (m := n) (0 : Fin 1)

theorem blk_cc {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b a : Fin n → ℂ) (e : ℂ) (i j : Fin n) :
    blk A b a e i.castSucc j.castSucc = A i j := by
  simp [blk, symm_castSucc]

theorem blk_cl {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b a : Fin n → ℂ) (e : ℂ) (i : Fin n) :
    blk A b a e i.castSucc (Fin.last n) = b i := by
  simp [blk, symm_castSucc, symm_last]

theorem blk_lc {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b a : Fin n → ℂ) (e : ℂ) (j : Fin n) :
    blk A b a e (Fin.last n) j.castSucc = a j := by
  simp [blk, symm_castSucc, symm_last]

theorem blk_ll {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b a : Fin n → ℂ) (e : ℂ) :
    blk A b a e (Fin.last n) (Fin.last n) = e := by
  simp [blk, symm_last]

theorem blk_mul {n : ℕ} (A A' : Matrix (Fin n) (Fin n) ℂ) (b a b' a' : Fin n → ℂ) (e e' : ℂ) :
    blk A b a e * blk A' b' a' e' =
      blk (A * A' + Matrix.vecMulVec b a') (A *ᵥ b' + e' • b) (a ᵥ* A' + e • a') (a ⬝ᵥ b' + e * e') := by
  unfold blk
  rw [Matrix.reindex_apply, Matrix.reindex_apply, Matrix.reindex_apply, Matrix.submatrix_mul_equiv,
    Matrix.fromBlocks_multiply]
  congr 2
  · ext i j; simp [Matrix.mul_apply, Matrix.vecMulVec_apply]
  · ext i j; simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]
  · ext i j; simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]
  · ext i j; simp [Matrix.mul_apply, dotProduct]

theorem det_blk_col_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (a : Fin n → ℂ) (e : ℂ) :
    (blk A 0 a e).det = A.det * e := by
  unfold blk
  rw [Matrix.det_reindex_self]
  have h : (Matrix.of fun i (_ : Fin 1) => (0 : Fin n → ℂ) i) = (0 : Matrix (Fin n) (Fin 1) ℂ) := by
    ext i j; simp
  rw [h, Matrix.det_fromBlocks_zero₁₂]
  simp

theorem det_blk_row_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b : Fin n → ℂ) (e : ℂ) :
    (blk A b 0 e).det = A.det * e := by
  unfold blk
  rw [Matrix.det_reindex_self]
  have h : (Matrix.of fun (_ : Fin 1) j => (0 : Fin n → ℂ) j) = (0 : Matrix (Fin 1) (Fin n) ℂ) := by
    ext i j; simp
  rw [h, Matrix.det_fromBlocks_zero₂₁]
  simp

theorem det_upper {d : ℕ} (v : UT d → ℂ) : (upper v).det = 1 := by
  have h : (upper v).BlockTriangular id := by
    intro i j hij
    have hij' : j < i := hij
    simp [upper, strictUpper, Matrix.one_apply, hij'.ne', not_lt.2 hij'.le]
  rw [Matrix.det_of_isUpperTriangular h]
  simp [upper, strictUpper]

theorem wMat_mul_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    (wMat n * A) i j = A i.rev j := by
  simp [wMat, Matrix.mul_apply]

theorem wMat_mulVec_apply {n : ℕ} (B : Fin n → ℂ) (i : Fin n) : (wMat n *ᵥ B) i = B i.rev := by
  simp [wMat, Matrix.mulVec, dotProduct]

theorem det_wMat_succ (n : ℕ) : (wMat (n + 1)).det = (-1) ^ n * (wMat n).det := by
  rw [Matrix.det_succ_row_zero]
  rw [Finset.sum_eq_single (Fin.last n)]
  · have h : (wMat (n + 1)).submatrix Fin.succ (Fin.last n).succAbove = wMat n := by
      ext i j
      simp [wMat, Fin.rev_succ]
    rw [h]
    simp [wMat]
  · intro j _ hj
    simp [wMat, hj]
  · simp

theorem det_wMat_ne_zero (n : ℕ) : (wMat n).det ≠ 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [det_wMat_succ]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) ih

end Formalism.FourierDecayAlt.P.G2

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G2

theorem additive_character_psi : Formalism.FourierDecayAlt.G.PsiChar := by
  intro β x y
  refine ⟨?_, ?_, ?_⟩
  · simp [psi, mul_add, Complex.exp_add]
  · simp only [psi]; rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I _
  · simp [psi]

theorem det_weyl_matrix : Formalism.FourierDecayAlt.G.DetMatch :=
  fun n => ⟨det_wMat_succ n, det_wMat_ne_zero n⟩

theorem det_orbit : Formalism.FourierDecayAlt.G.DetOrbit := by
  refine ⟨fun n t c p => ?_, fun d z v => ?_⟩
  · rw [Matrix.det_mul, Matrix.det_mul, lowRow, ptBlock, det_blk_col_zero, det_blk_col_zero,
      det_blk_row_zero, det_upper, Matrix.det_smul]
    simp; ring
  · rw [Matrix.det_mul, det_upper, ptLong, Matrix.det_smul]
    simp; ring

theorem matrix_entries : Formalism.FourierDecayAlt.G.EntriesM := by
  intro n t c p
  obtain ⟨a, v, b⟩ := p
  simp only [lowRow, ptBlock, Mcoord, blk_mul, Xof, rhoOf, upper]
  congr 1
  · simp [Matrix.mul_add, Matrix.mul_smul, Matrix.smul_mul, smul_add]
  · ext i; simp [Matrix.mulVec_smul, Matrix.smul_mulVec]
  · simp [Matrix.vecMul_smul, Matrix.mul_add, Matrix.vecMul_add, smul_add, Matrix.smul_vecMul,
      ← Matrix.vecMul_vecMul]
  · simp [Matrix.mulVec_smul, Matrix.vecMul_smul, Matrix.dotProduct_mulVec, add_comm]

theorem shape_of_matrix : Formalism.FourierDecayAlt.G.ShapeM := by
  intro m t σ X B ρ hX
  refine ⟨fun i j hij => ?_, fun i j hij => ?_, fun k => ?_, ?_, ?_⟩
  · obtain ⟨i', rfl⟩ : ∃ i' : Fin (m + 1), i = i'.castSucc :=
      ⟨⟨i, by omega⟩, Fin.ext rfl⟩
    obtain ⟨j', rfl⟩ : ∃ j' : Fin (m + 1), j = j'.castSucc :=
      ⟨⟨j, by omega⟩, Fin.ext rfl⟩
    have hlt : j' < i'.rev := by
      rw [Fin.lt_def, Fin.val_rev]
      simp only [Fin.val_castSucc] at hij
      omega
    rw [Mcoord, blk_cc, wMat_mul_apply]
    simp [Matrix.one_apply, hlt.ne', hX _ _ hlt.le]
  · obtain ⟨i', rfl⟩ : ∃ i' : Fin (m + 1), i = i'.castSucc :=
      ⟨⟨i, by omega⟩, Fin.ext rfl⟩
    obtain ⟨j', rfl⟩ : ∃ j' : Fin (m + 1), j = j'.castSucc :=
      ⟨⟨j, by omega⟩, Fin.ext rfl⟩
    have heq : i'.rev = j' := by
      apply Fin.ext
      rw [Fin.val_rev]
      simp only [Fin.val_castSucc] at hij
      omega
    rw [Mcoord, blk_cc, wMat_mul_apply, heq]
    simp [hX _ _ le_rfl]
  · rw [Mcoord, xOf]
    refine Fin.lastCases ?_ (fun k' => ?_) k
    · rw [Fin.succ_last, blk_cl, blk_cl, wMat_mulVec_apply, Fin.rev_rev]
    · rw [Fin.succ_castSucc, blk_cc, blk_cc, wMat_mul_apply, Fin.rev_rev]
      have hne : k'.castSucc ≠ k'.succ := (Fin.castSucc_lt_succ).ne
      simp [Matrix.one_apply, hne]
  · have h0 : (0 : Fin (m + 1 + 1)) = (0 : Fin (m + 1)).castSucc := rfl
    rw [Mcoord, h0, blk_lc]
  · rw [Mcoord, blk_ll]

theorem phase_formula : Formalism.FourierDecayAlt.G.PhaseFormula := by
  intro m t ht p
  obtain ⟨a, v, b⟩ := p
  have h1 : subSum (lowRow a) = a (Fin.last m) := by
    rw [subSum, Fin.sum_univ_castSucc, Finset.sum_eq_zero, zero_add, Fin.succ_last, lowRow, blk_lc]
    intro i _
    have hne : i.succ ≠ i.castSucc := (Fin.castSucc_lt_succ).ne'
    rw [Fin.succ_castSucc, lowRow, blk_cc, Matrix.one_apply_ne hne]
  have h2 : rhoOf t a v 0 = t * a (Fin.last m) := by
    simp only [rhoOf, Pi.smul_apply, smul_eq_mul, Matrix.vecMul, dotProduct, wMat_mul_apply]
    congr 1
    rw [Finset.sum_eq_single (Fin.last m)]
    · simp [upper, strictUpper]
    · intro i _ hi
      have hne : i.rev ≠ 0 := by
        intro h
        apply hi
        rw [← Fin.rev_rev i, h, Fin.rev_zero]
      have hnl : ¬ i.rev < 0 := by simp
      simp [upper, strictUpper, Matrix.one_apply_ne hne]
    · simp
  have h3 : ∀ k : Fin (m + 1), xOf (Xof t v) (t • b) k = t * blk (upper v) b 0 1 k.castSucc k.succ := by
    intro k
    rw [xOf]
    refine Fin.lastCases ?_ (fun k' => ?_) k
    · rw [Fin.succ_last, blk_cl, blk_cl]; simp
    · rw [Fin.succ_castSucc, blk_cc, blk_cc]
      have hne : k'.castSucc ≠ k'.succ := (Fin.castSucc_lt_succ).ne
      simp [Xof, upper, Matrix.one_apply_ne hne]
  show subSum (lowRow a) + superSum (blk (upper v) b 0 1) =
    (rhoOf t a v 0 + ∑ k, xOf (Xof t v) (t • b) k) / t
  rw [h1, h2, superSum, Finset.sum_congr rfl (fun k _ => h3 k), ← Finset.mul_sum]
  field_simp

end Formalism.FourierDecayAlt.P
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.AffineChangeOfVariables
open Formalism.FourierDecayAlt.G Matrix MeasureTheory
open scoped FourierTransform RealInnerProductSpace

namespace Formalism.FourierDecayAlt.P.G3

theorem map_mul_vol (α : ℂ) (hα : α ≠ 0) :
    Measure.map (fun ρ : ℂ => α * ρ) (volume : Measure ℂ) = ENNReal.ofReal ((‖α‖ ^ 2)⁻¹) • volume := by
  have hdet : LinearMap.det (LinearMap.mulLeft ℝ α) = ‖α‖ ^ 2 := by
    have h1 := Algebra.norm_complex_apply α
    rw [Algebra.norm_apply] at h1
    rw [← Complex.normSq_eq_norm_sq, ← h1]
    rfl
  have h := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure ℂ)
    (f := LinearMap.mulLeft ℝ α) (by rw [hdet]; positivity)
  rw [hdet, abs_of_nonneg (by positivity)] at h
  exact h

theorem wMat_mul_self (d : ℕ) : wMat d * wMat d = 1 := by
  ext i j
  have key : ∀ k : Fin d, (if k = i.rev then (1:ℂ) else 0) * (if j = k.rev then (1:ℂ) else 0) =
      if k = i.rev then (if i = j then 1 else 0) else 0 := by
    intro k
    by_cases hk : k = i.rev
    · simp [hk, eq_comm]
    · simp [hk]
  simp only [wMat, Matrix.mul_apply, Matrix.one_apply, Matrix.of_apply, key]
  simp

instance (β : ℂ) : SigmaFinite (mu β) := by unfold mu; infer_instance

end Formalism.FourierDecayAlt.P.G3

namespace Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.G3

theorem affine_change_of_variables : Formalism.FourierDecayAlt.G.AffineChange := by
  intro β α γ hα
  have h1 : (fun ρ : ℂ => α * ρ + γ) = (fun x => x + γ) ∘ (fun ρ : ℂ => α * ρ) := rfl
  have hmul := measurable_const_mul α
  have hadd := measurable_add_const γ
  unfold mu
  rw [h1, Measure.map_smul _ (hadd.comp hmul).aemeasurable, ← Measure.map_map hadd hmul,
    map_mul_vol α hα, Measure.map_smul _ hadd.aemeasurable, map_add_right_eq_self]
  rw [smul_comm]
  congr 1

theorem scale_product_measure : Formalism.FourierDecayAlt.G.ScalePi := by
  intro β z ι _ hz
  unfold muPi
  have hA := affine_change_of_variables β z 0 hz
  simp only [add_zero] at hA
  have hfun : (fun v : ι → ℂ => z • v) = fun v i => z * v i := by
    ext v i; simp
  have hc : Real.toNNReal ((‖z‖ ^ (2 * Fintype.card ι))⁻¹) =
      (Real.toNNReal ((‖z‖ ^ 2)⁻¹)) ^ Fintype.card ι := by
    rw [← Real.toNNReal_pow (by positivity), inv_pow, pow_mul]
  have hsf : SigmaFinite (Measure.map (fun ρ : ℂ => z * ρ) (mu β)) := by
    rw [hA]; infer_instance
  rw [hfun, Measure.pi_map_pi (fun _ => (measurable_const_mul z).aemeasurable)]
  simp only [hA]
  refine Measure.pi_eq fun s hs => ?_
  rw [hc]
  simp only [Measure.smul_apply, Measure.pi_pi, ENNReal.smul_def, smul_eq_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, ENNReal.coe_pow]

end Formalism.FourierDecayAlt.P
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.StabilizerBlockPoint
open Matrix
open Formalism.FourierDecayAlt.G

namespace Formalism.FourierDecayAlt.P.G4

theorem blk_cc {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b a : Fin n → ℂ) (e : ℂ) (i j : Fin n) :
    blk A b a e i.castSucc j.castSucc = A i j := by
  have h : ∀ i : Fin n, finSumFinEquiv.symm (i.castSucc : Fin (n+1)) = Sum.inl i := fun i =>
    finSumFinEquiv_symm_apply_castAdd (n := 1) i
  simp [blk, h]

theorem blk_cl {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b a : Fin n → ℂ) (e : ℂ) (i : Fin n) :
    blk A b a e i.castSucc (Fin.last n) = b i := by
  have h : ∀ i : Fin n, finSumFinEquiv.symm (i.castSucc : Fin (n+1)) = Sum.inl i := fun i =>
    finSumFinEquiv_symm_apply_castAdd (n := 1) i
  have h2 : finSumFinEquiv.symm (Fin.last n : Fin (n+1)) = Sum.inr (0 : Fin 1) :=
    finSumFinEquiv_symm_apply_natAdd (m := n) (0 : Fin 1)
  simp [blk, h, h2]

theorem blk_lc {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b a : Fin n → ℂ) (e : ℂ) (j : Fin n) :
    blk A b a e (Fin.last n) j.castSucc = a j := by
  have h : ∀ i : Fin n, finSumFinEquiv.symm (i.castSucc : Fin (n+1)) = Sum.inl i := fun i =>
    finSumFinEquiv_symm_apply_castAdd (n := 1) i
  have h2 : finSumFinEquiv.symm (Fin.last n : Fin (n+1)) = Sum.inr (0 : Fin 1) :=
    finSumFinEquiv_symm_apply_natAdd (m := n) (0 : Fin 1)
  simp [blk, h, h2]

theorem blk_mul {n : ℕ} (A A' : Matrix (Fin n) (Fin n) ℂ) (b a b' a' : Fin n → ℂ) (e e' : ℂ) :
    blk A b a e * blk A' b' a' e' =
      blk (A * A' + Matrix.vecMulVec b a') (A *ᵥ b' + e' • b) (a ᵥ* A' + e • a') (a ⬝ᵥ b' + e * e') := by
  unfold blk
  rw [Matrix.reindex_apply, Matrix.reindex_apply, Matrix.reindex_apply, Matrix.submatrix_mul_equiv,
    Matrix.fromBlocks_multiply]
  congr 2
  · ext i j; simp [Matrix.mul_apply, Matrix.vecMulVec_apply]
  · ext i j; simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]
  · ext i j; simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]
  · ext i j; simp [Matrix.mul_apply, dotProduct]

theorem upperUni_det {d : ℕ} {u : Matrix (Fin d) (Fin d) ℂ} (hu : IsUpperUni u) : u.det = 1 := by
  have h : u.BlockTriangular id := fun i j hij => hu.2 i j hij
  rw [Matrix.det_of_isUpperTriangular h]
  simp [hu.1]

theorem superSum_blk {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (b a : Fin (m + 1) → ℂ) (e : ℂ) :
    superSum (blk A b a e) = superSum A + b (Fin.last m) := by
  unfold superSum
  rw [Fin.sum_univ_castSucc]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fin.succ_castSucc, blk_cc]
  · rw [Fin.succ_last, blk_cl]

theorem subSum_blk {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (b a : Fin (m + 1) → ℂ) (e : ℂ) :
    subSum (blk A b a e) = subSum A + a (Fin.last m) := by
  unfold subSum
  rw [Fin.sum_univ_castSucc]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fin.succ_castSucc, blk_cc]
  · rw [Fin.succ_last, blk_lc]

end Formalism.FourierDecayAlt.P.G4

namespace Formalism.FourierDecayAlt.P

open G4

end Formalism.FourierDecayAlt.P
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousInvUpper
open Matrix MeasureTheory

set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.G5

open Formalism.FourierDecayAlt.G

instance sigmaFinite_mu (β : ℂ) : SigmaFinite (mu β) := by unfold mu; infer_instance

theorem wMat_mul_self (d : ℕ) : wMat d * wMat d = 1 := by
  ext i j
  have key : ∀ k : Fin d, (if k = i.rev then (1:ℂ) else 0) * (if j = k.rev then (1:ℂ) else 0) =
      if k = i.rev then (if i = j then 1 else 0) else 0 := by
    intro k
    by_cases hk : k = i.rev
    · simp [hk, eq_comm]
    · simp [hk]
  simp only [wMat, Matrix.mul_apply, Matrix.one_apply, Matrix.of_apply, key]
  simp

theorem norm_det_wMat (d : ℕ) : ‖(wMat d).det‖ = 1 := by
  have h := congrArg (fun M => ‖Matrix.det M‖) (wMat_mul_self d)
  simp only [Matrix.det_mul, norm_mul, Matrix.det_one, norm_one] at h
  nlinarith [norm_nonneg (wMat d).det]

theorem det_upper {d : ℕ} (v : UT d → ℂ) : (upper v).det = 1 := by
  have h : (upper v).BlockTriangular id := by
    intro i j hij
    have hij' : j < i := hij
    simp [upper, strictUpper, hij'.ne', not_lt.2 hij'.le]
  rw [Matrix.det_of_isUpperTriangular h]
  simp [upper, strictUpper]

theorem continuous_upper (d : ℕ) : Continuous (upper : (UT d → ℂ) → Matrix (Fin d) (Fin d) ℂ) := by
  refine continuous_matrix fun i j => ?_
  simp only [upper, strictUpper, Matrix.add_apply, Matrix.of_apply]
  refine continuous_const.add ?_
  split_ifs with h
  · exact continuous_apply _
  · exact continuous_const

theorem card_UT (n : ℕ) : Fintype.card (UT n) = ∑ i ∈ Finset.range n, i := by
  rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type_right]
  simp_rw [← Finset.card_filter]
  have : ∀ y : Fin n, (Finset.univ.filter (fun x : Fin n => x < y)).card = (y : ℕ) := by
    intro y
    rw [show Finset.univ.filter (fun x : Fin n => x < y) = Finset.Iio y by ext; simp]
    exact Fin.card_Iio y
  simp_rw [this]
  exact Fin.sum_univ_eq_sum_range (fun i => i) n

theorem symm_castSucc {n : ℕ} (i : Fin n) :
    finSumFinEquiv.symm (i.castSucc : Fin (n + 1)) = Sum.inl i :=
  finSumFinEquiv_symm_apply_castAdd (n := 1) i

theorem symm_last (n : ℕ) : finSumFinEquiv.symm (Fin.last n : Fin (n + 1)) = Sum.inr (0 : Fin 1) :=
  finSumFinEquiv_symm_apply_natAdd (m := n) (0 : Fin 1)

theorem blk_cc {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b a : Fin n → ℂ) (e : ℂ) (i j : Fin n) :
    blk A b a e i.castSucc j.castSucc = A i j := by
  simp [blk, symm_castSucc]

theorem blk_cl {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b a : Fin n → ℂ) (e : ℂ) (i : Fin n) :
    blk A b a e i.castSucc (Fin.last n) = b i := by
  simp [blk, symm_castSucc, symm_last]

theorem blk_lc {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b a : Fin n → ℂ) (e : ℂ) (j : Fin n) :
    blk A b a e (Fin.last n) j.castSucc = a j := by
  simp [blk, symm_castSucc, symm_last]

theorem blk_ll {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b a : Fin n → ℂ) (e : ℂ) :
    blk A b a e (Fin.last n) (Fin.last n) = e := by
  simp [blk, symm_last]

theorem continuous_inv_upper (d : ℕ) : Continuous (fun v : UT d → ℂ => (upper v)⁻¹) := by
  have h : (fun v : UT d → ℂ => (upper v)⁻¹) = fun v => (upper v).adjugate := by
    funext v
    rw [Matrix.inv_def, det_upper, Ring.inverse_one, one_smul]
  rw [h]
  exact (continuous_upper d).matrix_adjugate

theorem mp_comp_equiv (β : ℂ) {ι ι' : Type} [Fintype ι] [Fintype ι'] (σ : ι ≃ ι') :
    MeasurePreserving (fun v : ι' → ℂ => v ∘ σ) (muPi β ι') (muPi β ι) := by
  have h := measurePreserving_piCongrLeft (α := fun _ : ι => ℂ) (fun _ : ι => mu β) σ.symm
  have he : (fun v : ι' → ℂ => v ∘ σ) = MeasurableEquiv.piCongrLeft (fun _ : ι => ℂ) σ.symm := by
    funext v i
    obtain ⟨j, rfl⟩ := σ.symm.surjective i
    rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
    simp
  rw [he]
  exact h

theorem wMat_mul_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    (wMat n * A) i j = A i.rev j := by
  simp [wMat, Matrix.mul_apply]

theorem mul_wMat_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    (A * wMat n) i j = A i j.rev := by
  have h : ∀ k : Fin n, (j = k.rev) = (k = j.rev) := fun k => by
    rw [eq_iff_iff]
    constructor
    · rintro rfl; simp
    · rintro rfl; simp
  simp [wMat, Matrix.mul_apply, h]

end Formalism.FourierDecayAlt.P.G5

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G5

end Formalism.FourierDecayAlt.P
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.DualIdealInclusion
namespace Formalism.FourierDecayAlt.P.Dual

open NumberField FractionalIdeal

theorem alg {E : Type} [Field E] [NumberField E] (dd : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
    (hdd : dd ≠ 0) (ν g : ℤ) (hg : g ≠ 0) :
    spanSingleton _ (g : E) * (dd⁻¹ * (dd ^ ν * spanSingleton _ ((g : E) ^ 2))⁻¹) =
      dd ^ (-(ν + 1)) * spanSingleton _ ((g : E)⁻¹) := by
  have hgE : (g : E) ≠ 0 := by exact_mod_cast hg
  rw [mul_inv (dd ^ ν), spanSingleton_inv]
  have h1 : spanSingleton (nonZeroDivisors (𝓞 E)) (g : E) * spanSingleton _ (((g : E) ^ 2)⁻¹) =
      spanSingleton _ ((g : E)⁻¹) := by
    rw [spanSingleton_mul_spanSingleton]; congr 1; field_simp
  rw [show dd ^ (-(ν + 1)) = dd⁻¹ * (dd ^ ν)⁻¹ by
    rw [neg_add, zpow_add₀ hdd, _root_.zpow_neg, zpow_neg_one, mul_comm]]
  rw [← h1]; ring

theorem dual_third_group_integral : Formalism.FourierDecayAlt.L.DualLatticeInclusion := by
  intro E _ _ dd h1 ν g hg La hLa x hx
  have hdd : dd ≠ 0 := by
    intro h0; rw [h0, _root_.inv_zero] at h1; exact dual_ne_zero ℤ ℚ (one_ne_zero (α := FractionalIdeal (nonZeroDivisors (𝓞 E)) E)) h1
  have hgE : (g : E) ≠ 0 := by exact_mod_cast hg
  have hJ : dd ^ ν * spanSingleton (nonZeroDivisors (𝓞 E)) ((g : E) ^ 2) ≠ 0 :=
    mul_ne_zero (zpow_ne_zero _ hdd) (by simp [spanSingleton_eq_zero_iff, hgE])
  have hy : x * (g : E)⁻¹ ∈ dual ℤ ℚ (dd ^ ν * spanSingleton _ ((g : E) ^ 2)) := by
    rw [mem_dual hJ]
    intro a ha
    have := hx a (hLa a ha)
    rw [Algebra.traceForm_apply]
    convert this using 2
    field_simp
  rw [dual_eq_mul_inv ℤ ℚ, h1] at hy
  rw [← alg dd hdd ν g hg]
  have := mul_mem_mul (mem_spanSingleton_self (nonZeroDivisors (𝓞 E)) (g : E)) hy
  convert this using 1
  field_simp

end Formalism.FourierDecayAlt.P.Dual

theorem Formalism.FourierDecayAlt.P.dual_third_group_holds : Formalism.FourierDecayAlt.L.DualLatticeInclusion := Formalism.FourierDecayAlt.P.Dual.dual_third_group_integral
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.RecText
namespace Formalism.FourierDecayAlt.P.RecText

open Finset Real

theorem geo (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1/2) :
    ∀ i, 1 ≤ i → ∑ t ∈ Icc 2 i, a ^ (t - 1) ≤ 2 * a - 2 * a ^ i := by
  intro i hi
  induction i, hi using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Nat.add_sub_cancel]
    have : a ^ (n + 1) = a ^ n * a := pow_succ a n
    have h0 : 0 ≤ a ^ n := pow_nonneg ha0 n
    nlinarith

theorem recT : Formalism.FourierDecayAlt.RecursionText := by
  refine ⟨Real.exp 9, ?_⟩
  intro r a ε e σ ha0 ha1 hε hεa hra he hσ hrec
  set lam := 1 + ε + 2 * a with hlam
  set Q : ℕ → ℝ := fun k => ∏ j ∈ Icc 1 k, √(1 + e j) with hQdef
  have hQsucc : ∀ k, Q (k + 1) = Q k * √(1 + e (k + 1)) := by
    intro k; simp only [hQdef]; rw [Finset.prod_Icc_succ_top (by omega)]
  have hsq1 : ∀ j, 1 ≤ √(1 + e j) := fun j => by
    rw [Real.one_le_sqrt]; linarith [he j]
  have hQ0 : Q 0 = 1 := by simp [hQdef]
  have hQ1 : ∀ k, 1 ≤ Q k := by
    intro k; induction k with
    | zero => rw [hQ0]
    | succ k ih => rw [hQsucc]; nlinarith [hsq1 (k + 1)]
  have hQmono : Monotone Q := by
    apply monotone_nat_of_le_succ; intro k; rw [hQsucc]; nlinarith [hsq1 (k + 1), hQ1 k]
  have hlam1 : 1 ≤ lam := by linarith
  have hs0 := hσ 0
  have main : ∀ i, i ≤ r + 1 → σ i ≤ lam ^ i * Q i * σ 0 := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hir
      rcases Nat.eq_zero_or_pos i with h0 | hpos
      · subst h0; simp [hQ0]
      · have hrec' := hrec i hpos hir
        obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
        have hk : k + 1 - 1 = k := by omega
        rw [hk] at hrec'
        set M := lam ^ k * Q (k + 1) * σ 0 with hM
        have hM0 : 0 ≤ M := by
          have := pow_nonneg (by linarith : (0:ℝ) ≤ lam) k
          have := hQ1 (k + 1)
          positivity
        have hk' := ih k (by omega) (by omega)
        have h1 : (1 + ε) * √(1 + e (k + 1)) * σ k ≤ (1 + ε) * M := by
          rw [hM, hQsucc]
          have : √(1 + e (k + 1)) * σ k ≤ √(1 + e (k + 1)) * (lam ^ k * Q k * σ 0) :=
            mul_le_mul_of_nonneg_left hk' (Real.sqrt_nonneg _)
          nlinarith
        have h2 : ∑ t ∈ Icc 2 (k + 1), a ^ (t - 1) * σ (k + 1 - t) ≤
            ∑ t ∈ Icc 2 (k + 1), a ^ (t - 1) * M := by
          apply Finset.sum_le_sum
          intro t ht
          rw [Finset.mem_Icc] at ht
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg ha0 _)
          have := ih (k + 1 - t) (by omega) (by omega)
          refine this.trans ?_
          rw [hM]
          have e1 : lam ^ (k + 1 - t) ≤ lam ^ k := pow_le_pow_right₀ hlam1 (by omega)
          have e2 : Q (k + 1 - t) ≤ Q (k + 1) := hQmono (by omega)
          have e3 : 0 ≤ lam ^ (k + 1 - t) := pow_nonneg (by linarith) _
          have e4 : 0 ≤ Q (k + 1 - t) := by linarith [hQ1 (k + 1 - t)]
          have e5 : 0 ≤ lam ^ k := pow_nonneg (by linarith) _
          have := mul_le_mul e1 e2 e4 e5
          exact mul_le_mul_of_nonneg_right this hs0
        have h3 : ∑ t ∈ Icc 2 (k + 1), a ^ (t - 1) * M ≤ 2 * a * M := by
          rw [← Finset.sum_mul]
          have := geo a ha0 ha1 (k + 1) (by omega)
          have : 0 ≤ a ^ (k + 1) := pow_nonneg ha0 _
          apply mul_le_mul_of_nonneg_right _ hM0
          linarith
        have : lam ^ (k + 1) * Q (k + 1) * σ 0 = lam * M := by rw [hM]; ring
        rw [this]
        calc σ (k + 1) ≤ (1 + ε) * M + 2 * a * M := by linarith
          _ = lam * M := by rw [hlam]; ring
  have hfin := main (r + 1) le_rfl
  have hQsq : Q (r + 1) ^ 2 = ∏ i ∈ Icc 1 (r + 1), (1 + e i) := by
    simp only [hQdef]; rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [Real.sq_sqrt]; linarith [he j]
  have hP : 0 ≤ ∏ i ∈ Icc 1 (r + 1), (1 + e i) := by rw [← hQsq]; positivity
  have hsr := hσ (r + 1)
  have step1 : σ (r + 1) ^ 2 ≤ (lam ^ (r + 1)) ^ 2 * (∏ i ∈ Icc 1 (r + 1), (1 + e i)) * σ 0 ^ 2 := by
    rw [← hQsq]
    have := pow_le_pow_left₀ hsr hfin 2
    calc σ (r + 1) ^ 2 ≤ (lam ^ (r + 1) * Q (r + 1) * σ 0) ^ 2 := this
      _ = _ := by ring
  set x := ((r : ℝ) + 1) * a with hxdef
  have hx0 : 0 ≤ x := by positivity
  have hx32 : x ≤ 3 / 2 := by rw [hxdef]; nlinarith
  have step2 : (lam ^ (r + 1)) ^ 2 ≤ Real.exp (6 * x) := by
    rw [← pow_mul]
    have h1 : lam ≤ Real.exp (ε + 2 * a) := by
      have := Real.add_one_le_exp (ε + 2 * a); rw [hlam]; linarith
    have h2 := pow_le_pow_left₀ (by linarith) h1 ((r + 1) * 2)
    refine h2.trans ?_
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    push_cast
    nlinarith
  have step3 : Real.exp (6 * x) ≤ 1 + Real.exp 9 * x := by
    have ht0 : 0 ≤ 2 / 3 * x := by positivity
    have hc := convexOn_exp.2 (Set.mem_univ (0:ℝ)) (Set.mem_univ (9:ℝ))
      (by linarith : (0:ℝ) ≤ 1 - 2 / 3 * x) ht0 (by ring)
    simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at hc
    have : 6 * x = 2 / 3 * x * 9 := by ring
    rw [this]
    have : 0 ≤ Real.exp 9 := (Real.exp_pos 9).le
    nlinarith
  have : (lam ^ (r + 1)) ^ 2 ≤ 1 + Real.exp 9 * ((r : ℝ) + 1) * a := by
    have := step2.trans step3; rw [hxdef] at this; linarith
  refine step1.trans ?_
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact mul_le_mul_of_nonneg_right this hP

end Formalism.FourierDecayAlt.P.RecText

theorem Formalism.FourierDecayAlt.P.coarseBound : Formalism.FourierDecayAlt.RecursionText := Formalism.FourierDecayAlt.P.RecText.recT
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.TransferProductMonic
namespace Formalism.FourierDecayAlt.P.Misc

open Formalism.FourierDecayAlt.I Finset Polynomial

theorem selfDualG_holds : SelfDualG := by
  intro F _ o q hq hq0 a
  constructor
  · intro h
    have h1 := h (1, 1) ⟨o.one_mem, o.one_mem, 0, o.zero_mem, by simp⟩
    have h2 := h (q, 0) ⟨hq, o.zero_mem, 1, o.one_mem, by simp⟩
    simp only [mul_one, mul_zero, sub_zero] at h1 h2
    have e2 : a.1 * q / q = a.1 := by field_simp
    rw [e2] at h2
    refine ⟨h2, ?_, (a.1 - a.2) / q, h1, by field_simp⟩
    have : a.2 = a.1 - q * ((a.1 - a.2) / q) := by field_simp; ring
    rw [this]; exact o.sub_mem h2 (o.mul_mem hq h1)
  · rintro ⟨ha1, ha2, s, hs, has⟩ b ⟨hb1, hb2, t, ht, hbt⟩
    have ha : a.1 = a.2 + q * s := by linear_combination has
    have hb : b.1 = b.2 + q * t := by linear_combination hbt
    have e : (a.1 * b.1 - a.2 * b.2) / q = a.2 * t + s * b.2 + q * s * t := by
      rw [ha, hb]; field_simp; ring
    rw [e]
    exact o.add_mem (o.add_mem (o.mul_mem ha2 ht) (o.mul_mem hs hb2)) (o.mul_mem (o.mul_mem hq hs) ht)

end Formalism.FourierDecayAlt.P.Misc

theorem Formalism.FourierDecayAlt.P.self_dual_gamma : Formalism.FourierDecayAlt.I.SelfDualG := Formalism.FourierDecayAlt.P.Misc.selfDualG_holds
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.UnitaryInvariantGaussian
open Formalism.FourierDecayAlt.G Matrix MeasureTheory Filter Topology

namespace Formalism.FourierDecayAlt.P.G8

theorem psi_add (β x y : ℂ) : psi β (x + y) = psi β x * psi β y := by
  simp only [psi, mul_add, Complex.add_re, Complex.ofReal_add, Complex.exp_add]

end Formalism.FourierDecayAlt.P.G8

namespace Formalism.FourierDecayAlt.P

end Formalism.FourierDecayAlt.P
end
