module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsConsecutiveRatioLeRpow
open Matrix Finset Real

namespace GlobalTheory

theorem exists_consecutive_ratio_le_rpow :
    ∀ (a q : ℕ) (τ : ℕ → ℝ), 1 ≤ a → a ≤ q → (∀ i ≤ a, 0 < τ i) → (∀ i < a, τ i < τ (i + 1)) →
      τ a = 1 / 2 → ∃ b < a, τ b / τ (b + 1) ≤ (2 * τ 0) ^ ((1 : ℝ) / q) ∧
        τ b ^ 2 ≤ (2 * τ 0) ^ ((1 : ℝ) / q) / 4 := by
  intro a q τ ha haq hpos hinc hta

  have hmono : ∀ j, j ≤ a → ∀ i, i ≤ j → τ i ≤ τ j := by
    intro j
    induction j with
    | zero => intro _ i hi; rw [Nat.le_zero.mp hi]
    | succ n ih =>
      intro hn i hi
      rcases Nat.lt_or_ge i (n + 1) with h | h
      · exact (ih (by omega) i (by omega)).trans (hinc n (by omega)).le
      · rw [le_antisymm hi h]
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  set x := 2 * τ 0 with hx
  have hx0 : 0 < x := by linarith [hpos 0 (Nat.zero_le _)]
  have hx1 : x ≤ 1 := by linarith [hmono a le_rfl 0 (Nat.zero_le _)]
  set r := x ^ ((1 : ℝ) / q) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos hx0 _
  have hr1 : r ≤ 1 := Real.rpow_le_one hx0.le hx1 (by positivity)

  have hrq : r ^ q = x := by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le, one_div_mul_cancel hqpos.ne',
      Real.rpow_one]
  have hra : x ≤ r ^ a := by rw [← hrq]; exact pow_le_pow_of_le_one hr0.le hr1 haq

  obtain ⟨b, hb, hbr⟩ : ∃ b < a, τ b / τ (b + 1) ≤ r := by
    by_contra hne
    push_neg at hne
    have hstep : ∀ b < a, r * τ (b + 1) < τ b := fun b hb => by
      have h1 := hne b hb
      have h2 := hpos (b + 1) (by omega)
      rwa [lt_div_iff₀ h2] at h1
    have hind : ∀ i, i ≤ a → r ^ i * τ i ≤ τ 0 := by
      intro i
      induction i with
      | zero => intro _; simp
      | succ n ih =>
        intro hn
        calc r ^ (n + 1) * τ (n + 1) = r ^ n * (r * τ (n + 1)) := by ring
          _ ≤ r ^ n * τ n :=
            mul_le_mul_of_nonneg_left (hstep n (by omega)).le (pow_nonneg hr0.le _)
          _ ≤ τ 0 := ih (by omega)
    obtain ⟨c, rfl⟩ : ∃ c, a = c + 1 := ⟨a - 1, by omega⟩
    have hlast : r ^ (c + 1) * τ (c + 1) < τ 0 := by
      calc r ^ (c + 1) * τ (c + 1) = r ^ c * (r * τ (c + 1)) := by ring
        _ < r ^ c * τ c := mul_lt_mul_of_pos_left (hstep c (by omega)) (pow_pos hr0 _)
        _ ≤ τ 0 := hind c (by omega)
    rw [hta] at hlast
    linarith
  refine ⟨b, hb, hbr, ?_⟩
  have hb1 : 0 < τ (b + 1) := hpos (b + 1) (by omega)
  have hb0 : 0 < τ b := hpos b (by omega)
  have hle : τ b ≤ r * τ (b + 1) := by rwa [div_le_iff₀ hb1] at hbr
  have hhalf : τ (b + 1) ≤ 1 / 2 := by rw [← hta]; exact hmono a le_rfl (b + 1) (by omega)
  have htb : τ b ≤ r / 2 := by nlinarith [mul_le_mul_of_nonneg_left hhalf hr0.le]
  nlinarith [mul_le_mul htb htb hb0.le (by linarith), mul_le_mul_of_nonneg_left hr1 hr0.le]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryStabiliserOrthogonalSummand
open Matrix

namespace GlobalTheory

theorem map_transpose_mul_rev {R : Type} [CommRing R] (s : R →+* R) {l m n : Type} [Fintype m]
    (A : Matrix l m R) (B : Matrix m n R) :
    ((A * B).map s)ᵀ = (B.map s)ᵀ * (A.map s)ᵀ := by
  rw [Matrix.map_mul, Matrix.transpose_mul]

theorem unitary_stabiliser_orthogonal_summand :
    ∀ (R : Type) [CommRing R] (s : R →+* R) (N ι κ : Type) [Fintype N] [DecidableEq N] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (J : Matrix N N R) (G : Matrix ι ι R) (G' : Matrix κ κ R) (Q : Matrix N (ι ⊕ κ) R) (Qi : Matrix (ι ⊕ κ) N R), Q * Qi = 1 → Qi * Q = 1 → (Q.map s)ᵀ * J * Q = Matrix.fromBlocks G 0 0 G' → IsUnit G'.det → (∀ y : Matrix ι ι R, (y.map s)ᵀ * G * y = G → ((Q * Matrix.fromBlocks y 0 0 (1 : Matrix κ κ R) * Qi).map s)ᵀ * J * (Q * Matrix.fromBlocks y 0 0 (1 : Matrix κ κ R) * Qi) = J) ∧ ∀ h : Matrix N N R, (h.map s)ᵀ * J * h = J → (∀ b : κ, h *ᵥ (fun i => Q i (Sum.inr b)) = fun i => Q i (Sum.inr b)) → ∃ y : Matrix ι ι R, (y.map s)ᵀ * G * y = G ∧ h = Q * Matrix.fromBlocks y 0 0 (1 : Matrix κ κ R) * Qi := by
  intro R _ s N ι κ _ _ _ _ _ _ J G G' Q Qi h1 h2 hD hG'
  have h1s : (Qi.map s)ᵀ * (Q.map s)ᵀ = 1 := by
    rw [← map_transpose_mul_rev, h1, Matrix.map_one _ (map_zero s) (map_one s), transpose_one]
  have hblk : ∀ (y : Matrix ι ι R) (c : Matrix κ ι R),
      ((Matrix.fromBlocks y 0 c (1 : Matrix κ κ R)).map s)ᵀ * Matrix.fromBlocks G 0 0 G' *
        Matrix.fromBlocks y 0 c (1 : Matrix κ κ R) =
      Matrix.fromBlocks ((y.map s)ᵀ * G * y + (c.map s)ᵀ * G' * c) ((c.map s)ᵀ * G') (G' * c) G' := by
    intro y c
    rw [Matrix.fromBlocks_map, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply, Matrix.map_one _ (map_zero s) (map_one s),
      Matrix.map_zero _ (map_zero s)]
    simp
  refine ⟨fun y hy => ?_, fun h hh hfix => ?_⟩
  · have hb := hblk y 0
    rw [hy] at hb
    simp only [Matrix.mul_zero, add_zero, Matrix.map_zero _ (map_zero s), transpose_zero,
      Matrix.zero_mul] at hb
    rw [map_transpose_mul_rev, map_transpose_mul_rev]
    calc _ = (Qi.map s)ᵀ * (((Matrix.fromBlocks y 0 0 (1 : Matrix κ κ R)).map s)ᵀ *
            ((Q.map s)ᵀ * J * Q) * Matrix.fromBlocks y 0 0 (1 : Matrix κ κ R)) * Qi := by
          simp only [Matrix.mul_assoc]
      _ = (Qi.map s)ᵀ * ((Q.map s)ᵀ * J * Q) * Qi := by rw [hD, hb]
      _ = ((Qi.map s)ᵀ * (Q.map s)ᵀ) * J * (Q * Qi) := by simp only [Matrix.mul_assoc]
      _ = J := by rw [h1s, h1, Matrix.one_mul, Matrix.mul_one]
  · set M : Matrix (ι ⊕ κ) (ι ⊕ κ) R := Qi * h * Q with hM
    have hQM : Q * M = h * Q := by
      rw [hM, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul]
    have hhM : h = Q * M * Qi := by
      rw [hQM, Matrix.mul_assoc, h1, Matrix.mul_one]
    have hcol : ∀ x b, M x (Sum.inr b) = (1 : Matrix (ι ⊕ κ) (ι ⊕ κ) R) x (Sum.inr b) := by
      intro x b
      rw [← h2, hM, Matrix.mul_assoc, Matrix.mul_apply, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      exact congrFun (hfix b) i
    have hMb : M = Matrix.fromBlocks M.toBlocks₁₁ 0 M.toBlocks₂₁ 1 := by
      ext x z
      rcases z with z | z
      · rcases x with x | x <;> rfl
      · rw [hcol]
        rcases x with x | x <;> simp [Matrix.one_apply]
    have hU : (M.map s)ᵀ * Matrix.fromBlocks G 0 0 G' * M = Matrix.fromBlocks G 0 0 G' := by
      rw [← hD]
      calc _ = ((Q * M).map s)ᵀ * J * (Q * M) := by
            rw [map_transpose_mul_rev s Q M]; simp only [Matrix.mul_assoc]
        _ = (Q.map s)ᵀ * ((h.map s)ᵀ * J * h) * Q := by
            rw [hQM, map_transpose_mul_rev]; simp only [Matrix.mul_assoc]
        _ = _ := by rw [hh]
    rw [hMb, hblk, Matrix.fromBlocks_inj] at hU
    obtain ⟨ha, -, hc, -⟩ := hU
    have hc0 : M.toBlocks₂₁ = 0 := by
      have := congrArg (G'⁻¹ * ·) hc
      simpa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hG'] using this
    rw [hc0] at ha hMb
    refine ⟨M.toBlocks₁₁, by simpa using ha, ?_⟩
    rw [← hMb]
    exact hhM

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DetUpdateRowLastSingle
namespace GlobalTheory

open Matrix

theorem det_updateRow_last_single {K : Type} [CommRing K] (r : ℕ)
    (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    (Z.updateRow (Fin.last r) (Pi.single (Fin.last r) 1)).det
      = (Z.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [← Matrix.adjugate_apply, Matrix.adjugate_fin_succ_eq_det_submatrix]
  simp [← two_mul, pow_mul]

theorem det_fromBlocks_corner {K : Type} [CommRing K] (r : ℕ)
    (Z W : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (a b : K) :
    (Matrix.fromBlocks Z (Matrix.diagonal fun i => if i = Fin.last r then a else 0)
      (Matrix.diagonal fun i => if i = Fin.last r then b else 0) W).det
      = Z.det * W.det - a * b * ((Z.submatrix Fin.castSucc Fin.castSucc).det
          * (W.submatrix Fin.castSucc Fin.castSucc).det) := by
  set l := Fin.last r with hl
  set D : K → Matrix (Fin (r + 1)) (Fin (r + 1)) K :=
    fun c => Matrix.diagonal fun i => if i = l then c else 0 with hD
  have h1 : Matrix.fromBlocks Z (D a) (D b) W
      = (Matrix.fromBlocks Z 0 (D b) W).updateRow (Sum.inl l)
          (Matrix.fromBlocks Z 0 (D b) W (Sum.inl l) + a • Pi.single (Sum.inr l) 1) := by
    ext (i | i) (j | j) <;> by_cases hi : i = l <;> by_cases hj : j = l <;>
      simp [Matrix.updateRow_apply, hD, Matrix.diagonal_apply, Pi.single_apply, hi, hj, eq_comm] <;> grind
  have h2 : (Matrix.fromBlocks Z 0 (D b) W).updateRow (Sum.inl l) (Pi.single (Sum.inr l) 1)
      = (Matrix.fromBlocks (Z.updateRow l 0) (D 1) 0 W).updateRow (Sum.inr l)
          (Matrix.fromBlocks (Z.updateRow l 0) (D 1) 0 W (Sum.inr l)
            + b • Pi.single (Sum.inl l) 1) := by
    ext (i | i) (j | j) <;> by_cases hi : i = l <;> by_cases hj : j = l <;>
      simp [Matrix.updateRow_apply, hD, Matrix.diagonal_apply, Pi.single_apply, hi, hj, eq_comm] <;> grind
  have h3 : (Matrix.fromBlocks (Z.updateRow l 0) (D 1) 0 W).updateRow (Sum.inr l)
        (Pi.single (Sum.inl l) 1)
      = (Matrix.fromBlocks (Z.updateRow l (Pi.single l 1)) 0 0
          (W.updateRow l (Pi.single l 1))).submatrix (Equiv.swap (Sum.inl l) (Sum.inr l)) id := by
    ext (i | i) (j | j) <;> by_cases hi : i = l <;> by_cases hj : j = l <;>
      simp [Matrix.updateRow_apply, hD, Matrix.diagonal_apply, Pi.single_apply, hi, hj, eq_comm,
        Equiv.swap_apply_def] <;> grind
  have h0 : (Z.updateRow l 0).det = 0 :=
    Matrix.det_eq_zero_of_row_eq_zero l (by simp)
  change (Matrix.fromBlocks Z (D a) (D b) W).det = _
  rw [h1, Matrix.det_updateRow_add, Matrix.updateRow_eq_self, Matrix.det_updateRow_smul, h2,
    Matrix.det_updateRow_add, Matrix.updateRow_eq_self, Matrix.det_updateRow_smul, h3,
    Matrix.det_permute, Equiv.Perm.sign_swap (by simp), Matrix.det_fromBlocks_zero₁₂,
    Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₂₁, h0, hl,
    det_updateRow_last_single, det_updateRow_last_single]
  simp
  ring

theorem det_gram_two_frames {K : Type} [CommRing K] (r : ℕ)
    (Z W : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (T T' : K) :
    (Matrix.fromBlocks (Matrix.diagonal fun i => if i = Fin.last r then -T else 0) Z W
      (Matrix.diagonal fun i => if i = Fin.last r then -T' else 0)).det
      = (-1) ^ (r + 1) * (Z.det * W.det - T * T' * ((Z.submatrix Fin.castSucc Fin.castSucc).det
          * (W.submatrix Fin.castSucc Fin.castSucc).det)) := by
  have hs : (Matrix.fromBlocks 0 1 1 0 :
      Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) K).det = (-1) ^ (r + 1) := by
    have h : (Matrix.fromBlocks 0 1 1 0 :
        Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) K)
        = Matrix.fromBlocks 1 (-1) 0 1 * Matrix.fromBlocks 1 1 1 0 := by
      simp [Matrix.fromBlocks_multiply]
    rw [h, Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_one₁₁]
    simp [Matrix.det_neg]
  have hm : Matrix.fromBlocks (Matrix.diagonal fun i => if i = Fin.last r then -T else 0) Z W
      (Matrix.diagonal fun i => if i = Fin.last r then -T' else 0)
      = Matrix.fromBlocks Z (Matrix.diagonal fun i => if i = Fin.last r then -T else 0)
        (Matrix.diagonal fun i => if i = Fin.last r then -T' else 0) W
        * Matrix.fromBlocks 0 1 1 0 := by
    simp [Matrix.fromBlocks_multiply]
  rw [hm, Matrix.det_mul, hs, det_fromBlocks_corner]
  ring

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitaryMulVecEqOfFormEq
open Matrix

namespace GlobalTheory

theorem conjTranspose_mul_mul_eq_of_form_eq {E : Type} [Field E] [StarRing E] {n : ℕ}
    (J γ : Matrix (Fin n) (Fin n) E)
    (h : ∀ z w : Fin n → E, star (γ *ᵥ z) ⬝ᵥ (J *ᵥ (γ *ᵥ w)) = star z ⬝ᵥ (J *ᵥ w)) :
    γᴴ * J * γ = J := by
  have key : ∀ z w : Fin n → E, star z ⬝ᵥ ((γᴴ * J * γ) *ᵥ w) = star z ⬝ᵥ (J *ᵥ w) := by
    intro z w
    rw [← h z w, star_mulVec, ← dotProduct_mulVec, ← mulVec_mulVec, ← mulVec_mulVec]
  ext i j
  simpa [single_dotProduct, mulVec_single_one] using key (star (Pi.single i 1)) (Pi.single j 1)

theorem star_form_eq_of_hermitian {E : Type} [Field E] [StarRing E] {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (hJ : Jᴴ = J) (z w : Fin n → E) :
    star (star z ⬝ᵥ (J *ᵥ w)) = star w ⬝ᵥ (J *ᵥ z) := by
  rw [star_dotProduct z (J *ᵥ w), star_star, star_mulVec, ← dotProduct_mulVec, hJ]

private lemma form_sub_smul_left {E : Type} [Field E] [StarRing E] {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (z u w : Fin n → E) (s : E) :
    star (z - s • u) ⬝ᵥ (J *ᵥ w) = star z ⬝ᵥ (J *ᵥ w) - star s * (star u ⬝ᵥ (J *ᵥ w)) := by
  rw [star_sub, star_smul, sub_dotProduct, smul_dotProduct, smul_eq_mul]

private lemma form_sub_smul_right {E : Type} [Field E] [StarRing E] {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (z u w : Fin n → E) (t : E) :
    star z ⬝ᵥ (J *ᵥ (w - t • u)) = star z ⬝ᵥ (J *ᵥ w) - t * (star z ⬝ᵥ (J *ᵥ u)) := by
  rw [mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, smul_eq_mul]

private lemma form_mulVec_eq_of_transvection {E : Type} [Field E] [StarRing E] {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (hJ : Jᴴ = J) (γ : Matrix (Fin n) (Fin n) E)
    (u : Fin n → E) (c : E)
    (hγ : ∀ v, γ *ᵥ v = v - (c * (star u ⬝ᵥ (J *ᵥ v))) • u)
    (hc : c + star c = star c * c * (star u ⬝ᵥ (J *ᵥ u))) (z w : Fin n → E) :
    star (γ *ᵥ z) ⬝ᵥ (J *ᵥ (γ *ᵥ w)) = star z ⬝ᵥ (J *ᵥ w) := by
  have hzu := star_form_eq_of_hermitian J hJ u z
  rw [hγ z, hγ w, form_sub_smul_left, form_sub_smul_right J z u w,
    form_sub_smul_right J u u w, star_mul']
  linear_combination (c * (star u ⬝ᵥ (J *ᵥ w))) * hzu +
    (-(star (star u ⬝ᵥ (J *ᵥ z))) * (star u ⬝ᵥ (J *ᵥ w))) * hc

theorem exists_quasiReflection_mulVec_eq {E : Type} [Field E] [StarRing E] {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (hJ : Jᴴ = J) (x y : Fin n → E)
    (hxy : star x ⬝ᵥ (J *ᵥ x) = star y ⬝ᵥ (J *ᵥ y))
    (h0 : star (x - y) ⬝ᵥ (J *ᵥ x) ≠ 0) :
    ∃ γ : Matrix (Fin n) (Fin n) E, γᴴ * J * γ = J ∧ γ *ᵥ x = y := by
  have hγ : ∀ v, (1 - (star (x - y) ⬝ᵥ (J *ᵥ x))⁻¹ • vecMulVec (x - y) (star (x - y) ᵥ* J)) *ᵥ v
      = v - ((star (x - y) ⬝ᵥ (J *ᵥ x))⁻¹ * (star (x - y) ⬝ᵥ (J *ᵥ v))) • (x - y) := by
    intro v
    rw [sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, ← dotProduct_mulVec]
    congr 1
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
    ring
  have hsa : star (star (x - y) ⬝ᵥ (J *ᵥ x)) = star x ⬝ᵥ (J *ᵥ (x - y)) :=
    star_form_eq_of_hermitian J hJ (x - y) x
  have hsum : star (x - y) ⬝ᵥ (J *ᵥ x) + star (star (x - y) ⬝ᵥ (J *ᵥ x))
      = star (x - y) ⬝ᵥ (J *ᵥ (x - y)) := by
    rw [hsa]
    simp only [star_sub, sub_dotProduct, mulVec_sub, dotProduct_sub]
    linear_combination hxy
  have hs0 : star (star (x - y) ⬝ᵥ (J *ᵥ x)) ≠ 0 := (star_ne_zero).mpr h0
  have hc : (star (x - y) ⬝ᵥ (J *ᵥ x))⁻¹ + star (star (x - y) ⬝ᵥ (J *ᵥ x))⁻¹
      = star (star (x - y) ⬝ᵥ (J *ᵥ x))⁻¹ * (star (x - y) ⬝ᵥ (J *ᵥ x))⁻¹
        * (star (x - y) ⬝ᵥ (J *ᵥ (x - y))) := by
    rw [star_inv₀, ← hsum]
    field_simp
    ring
  refine ⟨_, conjTranspose_mul_mul_eq_of_form_eq J _
    (form_mulVec_eq_of_transvection J hJ _ (x - y) _ hγ hc), ?_⟩
  rw [hγ, inv_mul_cancel₀ h0, one_smul, sub_sub_cancel]

theorem exists_unitary_mulVec_eq_of_form_eq :
    ∀ (E : Type) [Field E] [CharZero E] [StarRing E] (n : ℕ) (J : Matrix (Fin n) (Fin n) E),
      Jᴴ = J → J.det ≠ 0 → ∀ x y : Fin n → E,
      star x ⬝ᵥ (J *ᵥ x) = star y ⬝ᵥ (J *ᵥ y) → star x ⬝ᵥ (J *ᵥ x) ≠ 0 →
      ∃ γ : Matrix (Fin n) (Fin n) E, γᴴ * J * γ = J ∧ γ *ᵥ x = y := by
  intro E _ _ _ n J hJ _ x y hxy hx
  by_cases h0 : star (x - y) ⬝ᵥ (J *ᵥ x) = 0
  · have hneg : star (-y) ⬝ᵥ (J *ᵥ (-y)) = star y ⬝ᵥ (J *ᵥ y) := by
      rw [star_neg, mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg]
    have hyx : star y ⬝ᵥ (J *ᵥ x) = star x ⬝ᵥ (J *ᵥ x) := by
      rw [star_sub, sub_dotProduct, sub_eq_zero] at h0
      exact h0.symm
    have h1 : star (x - -y) ⬝ᵥ (J *ᵥ x) ≠ 0 := by
      rw [sub_neg_eq_add, star_add, add_dotProduct, hyx, ← two_mul]
      exact mul_ne_zero two_ne_zero hx
    obtain ⟨γ, hγ, hγx⟩ := exists_quasiReflection_mulVec_eq J hJ x (-y) (hxy.trans hneg.symm) h1
    refine ⟨-γ, ?_, ?_⟩
    · rw [conjTranspose_neg, neg_mul, mul_neg, neg_mul, neg_neg, hγ]
    · rw [neg_mulVec, hγx, neg_neg]
  · exact exists_quasiReflection_mulVec_eq J hJ x y hxy h0

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMeasurableLintegralCosetEqOneClosedSubgrou
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMeasurableLintegralCosetEqOneClosedSubgrou
open MeasureTheory

namespace GlobalTheory

open scoped ENNReal in
open scoped Pointwise in
theorem _root_.GlobalTheory.exists_measurable_lintegral_coset_eq_one
    (G H : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] (ν : Measure H)
    [ν.IsHaarMeasure] [ν.IsMulRightInvariant] (j : H →* G) (hj : Topology.IsClosedEmbedding j) :
    ∃ b : G → ENNReal, Measurable b ∧ ∀ g, ∫⁻ h, b (j h * g) ∂ν = 1 := by
  let K := CompactExhaustion.choice G
  set a : ℕ → ℝ≥0∞ := fun n => ν (j ⁻¹' (K n * (K n)⁻¹)) with ha_def
  have ha : ∀ n, a n ≠ ∞ := fun n =>
    (hj.isCompact_preimage ((K.isCompact n).mul (K.isCompact n).inv)).measure_lt_top.ne
  set c : ℕ → ℝ≥0∞ := fun n => (2⁻¹ : ℝ≥0∞) ^ n / (a n + 1) with hc_def
  have hc_pos : ∀ n, c n ≠ 0 := fun n =>
    (ENNReal.div_pos (pow_ne_zero _ (by simp)) (by simp [ha n])).ne'
  have hc_le : ∀ n, c n ≤ 2⁻¹ ^ n := fun n =>
    ENNReal.div_le_of_le_mul (le_mul_of_one_le_right' le_add_self)
  have hca : ∀ n, c n * a n ≤ 2⁻¹ ^ n := fun n => by
    calc c n * a n ≤ c n * (a n + 1) := by gcongr; exact le_self_add
      _ = 2⁻¹ ^ n := ENNReal.div_mul_cancel (by simp) (by simp [ha n])
  have hKm : ∀ n, MeasurableSet (K n) := fun n => (K.isCompact n).isClosed.measurableSet
  set f : G → ℝ≥0∞ := fun y => ∑' n, (K n).indicator (fun _ => c n) y with hf_def
  have hf : Measurable f := Measurable.tsum fun n => measurable_const.indicator (hKm n)
  have hf_pos : ∀ y, f y ≠ 0 := by
    intro y
    obtain ⟨n, hn⟩ := K.exists_mem y
    refine ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.2 (hc_pos n)) ?_)
    calc c n = (K n).indicator (fun _ => c n) y := (Set.indicator_of_mem hn (fun _ => c n)).symm
      _ ≤ f y := by
        change (K n).indicator (fun _ => c n) y ≤ ∑' i, (K i).indicator (fun _ => c i) y
        exact le_tsum (fun i => (K i).indicator (fun _ => c i) y) n
  have hjg : ∀ g, Measurable fun h => j h * g := fun g => hj.continuous.measurable.mul_const g
  have hmeas : ∀ g, Measurable fun h => f (j h * g) := fun g => hf.comp (hjg g)
  set F : G → ℝ≥0∞ := fun g => ∫⁻ h, f (j h * g) ∂ν with hF_def
  have hF : Measurable F :=
    Measurable.lintegral_prod_right' (ν := ν) (f := fun p : G × H => f (j p.2 * p.1))
      (hf.comp ((hj.continuous.measurable.comp measurable_snd).mul measurable_fst))
  have hF_inv : ∀ h' g, F (j h' * g) = F g := by
    intro h' g
    have e : ∀ h, f (j h * (j h' * g)) = (fun k => f (j k * g)) (h * h') := by
      intro h; simp only [map_mul, mul_assoc]
    calc F (j h' * g) = ∫⁻ h, (fun k => f (j k * g)) (h * h') ∂ν := lintegral_congr e
      _ = F g := lintegral_mul_right_eq_self (μ := ν) (fun k => f (j k * g)) h'
  have hF0 : ∀ g, F g ≠ 0 := by
    intro g h0
    rw [hF_def, lintegral_eq_zero_iff (hmeas g), Filter.EventuallyEq, ae_iff] at h0
    have : ν Set.univ = 0 := by simpa [hf_pos] using h0
    exact NeZero.ne ν (Measure.measure_univ_eq_zero.1 this)
  have hFtop : ∀ g, F g ≠ ∞ := by
    intro g
    obtain ⟨m, hm⟩ := K.exists_mem g
    have hterm : ∀ n, ∫⁻ h, (K n).indicator (fun _ => c n) (j h * g) ∂ν
        ≤ (1 + a m) * 2⁻¹ ^ n := by
      intro n
      have hsub : (fun h => j h * g) ⁻¹' K n ⊆ j ⁻¹' (K (max n m) * (K (max n m))⁻¹) := by
        intro h hh
        have h1 : j h * g ∈ K (max n m) := K.subset (le_max_left n m) hh
        have h2 : g ∈ K (max n m) := K.subset (le_max_right n m) hm
        have e : j h = (j h * g) * g⁻¹ := by group
        rw [Set.mem_preimage, e]
        exact Set.mul_mem_mul h1 (Set.inv_mem_inv.2 h2)
      have hle : ν ((fun h => j h * g) ⁻¹' K n) ≤ a n + a m := by
        refine (measure_mono hsub).trans ?_
        rcases le_total n m with hnm | hnm
        · rw [max_eq_right hnm]; exact le_add_self
        · rw [max_eq_left hnm]; exact le_self_add
      calc ∫⁻ h, (K n).indicator (fun _ => c n) (j h * g) ∂ν
          = ∫⁻ h, ((fun h => j h * g) ⁻¹' K n).indicator (fun _ => c n) h ∂ν := rfl
        _ = c n * ν ((fun h => j h * g) ⁻¹' K n) :=
            lintegral_indicator_const (hjg g (hKm n)) _
        _ ≤ c n * (a n + a m) := by gcongr
        _ = c n * a n + c n * a m := mul_add _ _ _
        _ ≤ 2⁻¹ ^ n + 2⁻¹ ^ n * a m := by gcongr; exacts [hca n, hc_le n]
        _ = (1 + a m) * 2⁻¹ ^ n := by ring
    have hF_eq : F g = ∑' n, ∫⁻ h, (K n).indicator (fun _ => c n) (j h * g) ∂ν :=
      lintegral_tsum fun n =>
        ((measurable_const.indicator (hKm n)).comp (hjg g)).aemeasurable
    rw [hF_eq]
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hterm)
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    exact ENNReal.mul_ne_top (by simp [ha m]) (by simp)
  refine ⟨fun g => f g * (F g)⁻¹, hf.mul hF.inv, fun g => ?_⟩
  simp only [hF_inv]
  rw [lintegral_mul_const _ (hmeas g)]
  exact ENNReal.mul_inv_cancel (hF0 g) (hFtop g)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMeasurableLintegralCosetEqOneClosedSubgrouStatement
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_measurable_lintegral_coset_eq_one_closedSubgroup : ∀ (G H : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] (ν : Measure H) [ν.IsHaarMeasure] [ν.IsMulRightInvariant] (j : H →* G), Topology.IsClosedEmbedding j → ∃ b : G → ENNReal, Measurable b ∧ ∀ g, ∫⁻ h, b (j h * g) ∂ν = 1 := by
  first | exact @GlobalTheory.exists_measurable_lintegral_coset_eq_one | exact GlobalTheory.exists_measurable_lintegral_coset_eq_one | (intros; apply GlobalTheory.exists_measurable_lintegral_coset_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsometricIntertwinerOfMatrixCoeffEq
open MeasureTheory
open scoped InnerProductSpace

namespace GlobalTheory

theorem inner_translate_translate_of_norm {G : Type} [Group G] {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : G →* (H →L[ℂ] H)) (hσ : ∀ g x, ‖σ g x‖ = ‖x‖) (w : H)
    (g h : G) : ⟪σ g w, σ h w⟫_ℂ = ⟪w, σ (g⁻¹ * h) w⟫_ℂ := by
  have hmul : σ h w = σ g (σ (g⁻¹ * h) w) := by
    show σ h w = (σ g * σ (g⁻¹ * h)) w
    rw [← map_mul, mul_inv_cancel_left]
  let T : H →ₗᵢ[ℂ] H := { toLinearMap := (σ g : H →ₗ[ℂ] H), norm_map' := hσ g }
  rw [hmul]
  exact T.inner_map_map w (σ (g⁻¹ * h) w)

theorem exists_isometric_intertwiner_of_matrixCoeff_eq :
    ∀ (G : Type) [Group G] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] (σ : G →* (H →L[ℂ] H)) (Hp : Type) [NormedAddCommGroup Hp]
      [InnerProductSpace ℂ Hp] [CompleteSpace Hp] (π : G →* (Hp →L[ℂ] Hp)),
      (∀ g x, ‖σ g x‖ = ‖x‖) → (∀ g x, ‖π g x‖ = ‖x‖) → ∀ (w : H) (v : Hp),
      (∀ y : H, (∀ g, ⟪y, σ g w⟫_ℂ = 0) → y = 0) → (∀ g, ⟪v, π g v⟫_ℂ = ⟪w, σ g w⟫_ℂ) →
      ∃ io : H →ₗᵢ[ℂ] Hp, io w = v ∧ ∀ (g : G) (u : H), io (σ g u) = π g (io u) := by
  intro G _ H _ _ _ σ Hp _ _ _ π hσ hπ w v hcyc hvw

  obtain ⟨A, hA⟩ : ∃ A : (G →₀ ℂ) →ₗ[ℂ] H, A = Finsupp.linearCombination ℂ (fun g => σ g w) :=
    ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : (G →₀ ℂ) →ₗ[ℂ] Hp, B = Finsupp.linearCombination ℂ (fun g => π g v) :=
    ⟨_, rfl⟩

  have hkey : ∀ g h : G, ⟪π g v, π h v⟫_ℂ = ⟪σ g w, σ h w⟫_ℂ := by
    intro g h
    rw [inner_translate_translate_of_norm π hπ, inner_translate_translate_of_norm σ hσ, hvw]
  have hinner : ∀ c d, ⟪B c, B d⟫_ℂ = ⟪A c, A d⟫_ℂ := by
    intro c d
    rw [hA, hB]
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum,
      inner_smul_left, inner_smul_right, hkey]
  have hnorm : ∀ c, ‖B c‖ = ‖A c‖ := by
    intro c
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ) (A c), hinner]
  have hker : LinearMap.ker A ≤ LinearMap.ker B := by
    intro c hc
    rw [LinearMap.mem_ker] at hc ⊢
    rw [← norm_eq_zero, hnorm, hc, norm_zero]

  obtain ⟨F, hF⟩ : ∃ F : LinearMap.range A →ₗ[ℂ] Hp,
      ∀ c, F ⟨A c, LinearMap.mem_range_self A c⟩ = B c :=
    ⟨(LinearMap.ker A).liftQ B hker ∘ₗ A.quotKerEquivRange.symm.toLinearMap, fun c => by simp⟩
  have hFn : ∀ y, ‖F y‖ = ‖y‖ := by
    rintro ⟨_, c, rfl⟩
    rw [hF, hnorm]
    rfl
  let F' : LinearMap.range A →ₗᵢ[ℂ] Hp := { toLinearMap := F, norm_map' := hFn }

  have hclos : (LinearMap.range A).topologicalClosure = ⊤ := by
    rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
    intro y hy
    refine hcyc y fun g => inner_eq_zero_symm.mp ((Submodule.mem_orthogonal _ _).mp hy _ ?_)
    exact ⟨Finsupp.single g 1, by simp [hA]⟩
  have hdense : DenseRange (LinearMap.range A).subtypeL :=
    denseRange_subtype_val.mpr (Submodule.dense_iff_topologicalClosure_eq_top.mpr hclos)
  have huni : IsUniformInducing (LinearMap.range A).subtypeL :=
    (LinearMap.range A).subtypeₗᵢ.isometry.isUniformInducing

  obtain ⟨X, hXdef⟩ : ∃ X : H →L[ℂ] Hp, X = F'.toContinuousLinearMap.extend (LinearMap.range A).subtypeL :=
    ⟨_, rfl⟩
  have hX : ∀ c, X (A c) = B c := fun c => by
    rw [hXdef]
    exact (ContinuousLinearMap.extend_eq F'.toContinuousLinearMap hdense huni
      ⟨A c, LinearMap.mem_range_self A c⟩).trans (hF c)
  have hXn : ∀ u, ‖X u‖ = ‖u‖ := by
    intro u
    refine hdense.induction_on (p := fun u => ‖X u‖ = ‖u‖) u
      (isClosed_eq (continuous_norm.comp X.continuous) continuous_norm) ?_
    rintro ⟨_, c, rfl⟩
    show ‖X (A c)‖ = ‖A c‖
    rw [hX, hnorm]

  have hshA : ∀ g c, σ g (A c) = A (Finsupp.mapDomain (g * ·) c) := by
    intro g c
    rw [hA, Finsupp.linearCombination_mapDomain]
    change (σ g : H →ₗ[ℂ] H) _ = _
    rw [Finsupp.apply_linearCombination]
    refine congrArg (fun f => Finsupp.linearCombination ℂ f c) ?_
    funext h
    simp [map_mul]
  have hshB : ∀ g c, π g (B c) = B (Finsupp.mapDomain (g * ·) c) := by
    intro g c
    rw [hB, Finsupp.linearCombination_mapDomain]
    change (π g : Hp →ₗ[ℂ] Hp) _ = _
    rw [Finsupp.apply_linearCombination]
    refine congrArg (fun f => Finsupp.linearCombination ℂ f c) ?_
    funext h
    simp [map_mul]
  have hXi : ∀ g u, X (σ g u) = π g (X u) := by
    intro g u
    refine hdense.induction_on (p := fun u => X (σ g u) = π g (X u)) u
      (isClosed_eq (X.continuous.comp (σ g).continuous) ((π g).continuous.comp X.continuous)) ?_
    rintro ⟨_, c, rfl⟩
    show X (σ g (A c)) = π g (X (A c))
    rw [hshA, hX, hX, hshB]
  have hw : A (Finsupp.single 1 1) = w := by simp [hA]
  have hv : B (Finsupp.single 1 1) = v := by simp [hB]
  refine ⟨{ toLinearMap := (X : H →ₗ[ℂ] Hp), norm_map' := hXn }, ?_, fun g u => hXi g u⟩
  show X w = v
  rw [← hw, hX, hv]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ZetaProdSphereVolumeBounds
open Matrix Finset Real

namespace GlobalTheory

namespace ZetaProd

theorem zeta_le (l K : ℕ) (hK : 0 < K) :
    (∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ (l + 2)) ≤
      (∑ m ∈ Finset.range K, 1 / ((m : ℝ) + 1) ^ (l + 2)) + 1 / ((K : ℝ) + 1) ^ l * (1 / K) := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have key : ∀ n : ℕ, (∑ m ∈ Finset.range (K + n), 1 / ((m : ℝ) + 1) ^ (l + 2)) ≤
      (∑ m ∈ Finset.range K, 1 / ((m : ℝ) + 1) ^ (l + 2)) +
        1 / ((K : ℝ) + 1) ^ l * (1 / K - 1 / ((K : ℝ) + n)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [← add_assoc, Finset.sum_range_succ]
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have h1 : 1 / (((K + n : ℕ) : ℝ) + 1) ^ (l + 2) ≤
          1 / ((K : ℝ) + 1) ^ l * (1 / ((K : ℝ) + n) - 1 / ((K : ℝ) + (n + 1 : ℕ))) := by
        push_cast
        have e : 1 / ((K : ℝ) + n) - 1 / ((K : ℝ) + (n + 1)) =
            1 / (((K : ℝ) + n) * ((K : ℝ) + n + 1)) := by
          field_simp
          ring
        rw [e, one_div_mul_one_div]
        apply one_div_le_one_div_of_le (by positivity)
        rw [pow_add]
        apply mul_le_mul
        · apply pow_le_pow_left₀ (by positivity)
          linarith
        · nlinarith
        · positivity
        · positivity
      nlinarith
  apply Real.tsum_le_of_sum_range_le (fun m => by positivity)
  intro n
  have h2 : (∑ m ∈ Finset.range n, 1 / ((m : ℝ) + 1) ^ (l + 2)) ≤
      ∑ m ∈ Finset.range (K + n), 1 / ((m : ℝ) + 1) ^ (l + 2) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.range_mono (by omega)
    · intro i _ _
      positivity
  have h3 : 0 ≤ 1 / ((K : ℝ) + 1) ^ l * (1 / ((K : ℝ) + n)) := by positivity
  have := key n
  nlinarith

theorem zeta_nonneg (l : ℕ) : 0 ≤ ∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ l :=
  tsum_nonneg (fun m => by positivity)

theorem zeta_two_le : (∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ 2) ≤ 1.645 := by
  have h := (hasSum_nat_add_iff' 1).2 hasSum_zeta_two
  have h2 : HasSum (fun m : ℕ => 1 / ((m : ℝ) + 1) ^ 2) (π ^ 2 / 6) := by
    simpa using h
  rw [h2.tsum_eq]
  have := Real.pi_lt_d4
  have := Real.pi_pos
  nlinarith

theorem zeta_three_le : (∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ 3) ≤ 1.2027 :=
  (zeta_le 1 30 (by norm_num)).trans (by norm_num [Finset.sum_range_succ])

theorem zeta_four_le : (∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ 4) ≤ 1.0825 :=
  (zeta_le 2 30 (by norm_num)).trans (by norm_num [Finset.sum_range_succ])

theorem zeta_five_le : (∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ 5) ≤ 1.0370 :=
  (zeta_le 3 30 (by norm_num)).trans (by norm_num [Finset.sum_range_succ])

theorem zeta_six_le : (∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ 6) ≤ 1.0174 :=
  (zeta_le 4 30 (by norm_num)).trans (by norm_num [Finset.sum_range_succ])

theorem zeta_seven_le : (∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ 7) ≤ 1.0084 :=
  (zeta_le 5 30 (by norm_num)).trans (by norm_num [Finset.sum_range_succ])

theorem zeta_eight_le : (∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ 8) ≤ 1.0041 :=
  (zeta_le 6 30 (by norm_num)).trans (by norm_num [Finset.sum_range_succ])

theorem zeta_tail_le (n : ℕ) :
    (∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ (n + 9)) ≤ 1 + 0.00235 * (1 / 2) ^ n := by
  refine (zeta_le (n + 7) 2 (by norm_num)).trans ?_
  have h : (1 / 3 : ℝ) ^ n ≤ (1 / 2) ^ n := pow_le_pow_left₀ (by norm_num) (by norm_num) n
  have e1 : 1 / ((1 : ℝ) + 1) ^ (n + 7 + 2) = (1 / 2) ^ n / 512 := by
    rw [_root_.one_div_pow, add_assoc, pow_add]; norm_num; ring
  have e2 : 1 / ((2 : ℝ) + 1) ^ (n + 7) = (1 / 3) ^ n / 2187 := by
    rw [_root_.one_div_pow, pow_add]; norm_num; ring
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.cast_zero,
    Nat.cast_one, Nat.cast_ofNat, zero_add, one_pow]
  rw [e1, e2]
  have : (0 : ℝ) ≤ (1 / 2) ^ n := by positivity
  linarith

theorem prod_three_eight (N : ℕ) (hN : N ≤ 8) :
    ∏ l ∈ Finset.Icc 3 N, (∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ l) ≤ 1.391 := by
  have hb : ∏ l ∈ Finset.Icc 3 N, (∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ l) ≤
      ∏ l ∈ Finset.Icc 3 N, (if l = 3 then (1.2027 : ℝ) else if l = 4 then 1.0825 else
        if l = 5 then 1.0370 else if l = 6 then 1.0174 else if l = 7 then 1.0084
        else 1.0041) := by
    apply Finset.prod_le_prod₀ (fun l _ => zeta_nonneg l)
    intro l hl
    rw [Finset.mem_Icc] at hl
    obtain ⟨h1, h2⟩ := hl
    have h3 : l ≤ 8 := h2.trans hN
    interval_cases l
    · simpa using zeta_three_le
    · simpa using zeta_four_le
    · simpa using zeta_five_le
    · simpa using zeta_six_le
    · simpa using zeta_seven_le
    · simpa using zeta_eight_le
  refine hb.trans ?_
  interval_cases N <;> norm_num [Finset.prod_Icc_succ_top]

theorem prod_three_tail (n : ℕ) :
    ∏ l ∈ Finset.Icc 3 (n + 8), (∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ l) ≤
      1.398 * (1 - 0.0047 * (1 / 2) ^ n) := by
  induction n with
  | zero =>
    refine (prod_three_eight 8 le_rfl).trans ?_
    norm_num
  | succ n ih =>
    rw [show n + 1 + 8 = (n + 8) + 1 by ring, Finset.prod_Icc_succ_top (by omega)]
    have h1 := zeta_tail_le n
    have hx : (0 : ℝ) ≤ (1 / 2) ^ n := by positivity
    have hx1 : ((1 : ℝ) / 2) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    refine (mul_le_mul ih h1 (zeta_nonneg _) (by nlinarith)).trans ?_
    rw [pow_succ]
    nlinarith [mul_nonneg hx hx]

theorem prod_three_le (N : ℕ) :
    ∏ l ∈ Finset.Icc 3 N, (∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ l) ≤ 1.398 := by
  rcases le_total N 8 with h | h
  · exact (prod_three_eight N h).trans (by norm_num)
  · obtain ⟨n, rfl⟩ : ∃ n, N = n + 8 := ⟨N - 8, by omega⟩
    refine (prod_three_tail n).trans ?_
    have hx : (0 : ℝ) ≤ (1 / 2) ^ n := by positivity
    nlinarith

theorem prod_two_lt (N : ℕ) :
    ∏ l ∈ Finset.Icc 2 N, (∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ l) < 2.3 := by
  rcases lt_or_ge N 2 with h | h
  · rw [Finset.Icc_eq_empty (by omega)]
    norm_num
  · have e : Finset.Icc 2 N = insert 2 (Finset.Icc 3 N) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [e, Finset.prod_insert (by simp)]
    refine (mul_le_mul zeta_two_le (prod_three_le N)
      (Finset.prod_nonneg fun l _ => zeta_nonneg l) (by norm_num)).trans_lt ?_
    norm_num

theorem sphere_le (l : ℕ) (hl : 1 ≤ l) :
    2 * Real.pi ^ l / ((l - 1).factorial : ℝ) ≤ 32.5 := by
  have h1 := Real.pi_lt_d4
  have h0 := Real.pi_pos
  have hp : ∀ k : ℕ, π ^ k ≤ (3.1416 : ℝ) ^ k := fun k => pow_le_pow_left₀ h0.le h1.le k
  have tail : ∀ n : ℕ, 2 * Real.pi ^ (n + 4) / ((n + 3).factorial : ℝ) ≤ 32.5 := by
    intro n
    induction n with
    | zero =>
      have := hp 4
      norm_num [Nat.factorial] at this ⊢
      linarith
    | succ n ih =>
      refine le_trans ?_ ih
      have hf : (0 : ℝ) < ((n + 3).factorial : ℝ) := by positivity
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      rw [show n + 1 + 3 = (n + 3) + 1 by ring, Nat.factorial_succ,
        show n + 1 + 4 = (n + 4) + 1 by ring, pow_succ]
      push_cast
      rw [div_le_div_iff₀ (by positivity) hf]
      have hq : 0 ≤ 2 * π ^ (n + 4) * ((n + 3).factorial : ℝ) := by positivity
      have : π ≤ (n : ℝ) + 3 + 1 := by linarith
      nlinarith [mul_le_mul_of_nonneg_left this hq]
  rcases le_or_gt 4 l with h | h
  · obtain ⟨n, rfl⟩ : ∃ n, l = n + 4 := ⟨l - 4, by omega⟩
    exact tail n
  · have := hp l
    interval_cases l <;> norm_num [Nat.factorial] at this ⊢ <;> linarith

end ZetaProd

theorem zetaProd_sphereVolume_bounds :
    (∀ N : ℕ, ∏ l ∈ Finset.Icc 2 N, (∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ l) < 2.3) ∧
    (∀ N : ℕ, ∏ l ∈ Finset.Icc 3 N, (∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ l) < 1.4) ∧
    ∀ l : ℕ, 1 ≤ l → 2 * Real.pi ^ l / ((l - 1).factorial : ℝ) ≤ 32.5 :=
  ⟨ZetaProd.prod_two_lt, fun N => (ZetaProd.prod_three_le N).trans_lt (by norm_num),
    ZetaProd.sphere_le⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRealSubmoduleBlockFinrankLe
open Finset

namespace GlobalTheory

theorem exists_real_submodule_block_finrank_le :
    ∀ (n : ℕ) (E E' : Submodule ℂ (EuclideanSpace ℂ (Fin n))),
    ∃ U : Submodule ℝ (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)),
      Module.finrank ℝ U ≤ 2 * Module.finrank ℂ E' * Module.finrank ℂ E ∧
      ∀ T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n),
        E'.starProjection ∘L T ∘L E.starProjection ∈ U := by
  intro n E E'
  let f : (E →L[ℂ] E') →ₗ[ℝ] (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :=
    { toFun := fun M => E'.subtypeL ∘L M ∘L E.orthogonalProjection
      map_add' := fun M N => by ext; simp
      map_smul' := fun c M => by ext; simp }
  refine ⟨LinearMap.range f, ?_, fun T => ⟨E'.orthogonalProjection ∘L T ∘L E.subtypeL, rfl⟩⟩
  refine (LinearMap.finrank_range_le f).trans (le_of_eq ?_)
  have h1 : Module.finrank ℂ (E →L[ℂ] E') = Module.finrank ℂ E * Module.finrank ℂ E' := by
    rw [← (LinearMap.toContinuousLinearMap (𝕜 := ℂ) (E := E) (F' := E')).finrank_eq,
      Module.finrank_linearMap]
  rw [← Module.finrank_mul_finrank ℝ ℂ (E →L[ℂ] E'), Complex.finrank_real_complex, h1]
  ring

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProdFirstBlocksByLayers
open Finset

namespace GlobalTheory

theorem prod_interval_mirror_split (a i : ℕ) (hi : i < a) (f : ℕ → ℝ) :
    ∏ p ∈ (Finset.range (2 * a + 1)).filter (fun p => i < p ∧ i + p ≤ 2 * a), f p
      = (∏ k ∈ Finset.Ioo i a, f k * f (2 * a - k)) * (f a * f (2 * a - i)) := by
  have hS : (Finset.range (2 * a + 1)).filter (fun p => i < p ∧ i + p ≤ 2 * a)
      = Finset.Ioo i a ∪ insert a (Finset.Ioo a (2 * a - i) ∪ {2 * a - i}) := by
    ext p
    simp only [mem_filter, mem_range, mem_union, mem_insert, mem_Ioo, mem_singleton]
    omega
  rw [hS, prod_union, prod_insert, prod_union, prod_singleton]
  · have hm : ∏ p ∈ Finset.Ioo a (2 * a - i), f p = ∏ k ∈ Finset.Ioo i a, f (2 * a - k) := by
      refine Finset.prod_nbij' (fun p => 2 * a - p) (fun k => 2 * a - k) ?_ ?_ ?_ ?_ ?_
      · intro x hx
        simp only [mem_Ioo] at hx ⊢
        omega
      · intro x hx
        simp only [mem_Ioo] at hx ⊢
        omega
      · intro x hx
        simp only [mem_Ioo] at hx
        omega
      · intro x hx
        simp only [mem_Ioo] at hx
        omega
      · intro x hx
        simp only [mem_Ioo] at hx
        congr 1
        omega
    rw [hm, prod_mul_distrib]
    ring
  all_goals first
    | (rw [Finset.disjoint_left]
       intro x hx hx'
       simp only [mem_union, mem_insert, mem_Ioo, mem_singleton] at hx hx'
       omega)
    | (simp only [mem_union, mem_Ioo, mem_singleton]
       omega)

private theorem prod_filter_gt_eq_prod_Ioo (a : ℕ) (i : Fin a) (h : ℕ → ℝ) :
    ∏ k ∈ Finset.univ.filter (fun k : Fin a => i < k), h k = ∏ k ∈ Finset.Ioo (i : ℕ) a, h k := by
  refine Finset.prod_nbij (fun k => (k : ℕ)) ?_ ?_ ?_ ?_
  · intro k hk
    simp only [mem_filter, mem_univ, true_and] at hk
    simp only [mem_Ioo]
    exact ⟨hk, k.isLt⟩
  · intro x _ y _ hxy
    exact Fin.ext hxy
  · intro k hk
    simp only [Finset.mem_coe, mem_Ioo] at hk
    exact ⟨⟨k, hk.2⟩, Finset.mem_coe.2 (mem_filter.2 ⟨mem_univ _, Fin.lt_def.2 hk.1⟩), rfl⟩
  · intro k _
    rfl

theorem prod_first_blocks_by_layers (a : ℕ) (g : ℕ → ℕ → ℝ) :
    ∏ b ∈ ((Finset.range a) ×ˢ (Finset.range (2 * a + 1))).filter
        (fun b : ℕ × ℕ => b.1 < b.2 ∧ b.1 + b.2 ≤ 2 * a), g b.1 b.2
      = (∏ i : Fin a, ∏ k ∈ Finset.univ.filter (fun k : Fin a => i < k),
          g i k * g i (2 * a - k)) * ∏ i : Fin a, g i a * g i (2 * a - i) := by
  rw [Finset.prod_filter, Finset.prod_product]
  have step : ∀ i ∈ Finset.range a,
      (∏ p ∈ Finset.range (2 * a + 1), if i < p ∧ i + p ≤ 2 * a then g i p else 1)
        = (∏ k ∈ Finset.Ioo i a, g i k * g i (2 * a - k)) * (g i a * g i (2 * a - i)) := by
    intro i hi
    rw [← Finset.prod_filter]
    exact prod_interval_mirror_split a i (mem_range.1 hi) (g i)
  refine (Finset.prod_congr rfl step).trans ?_
  rw [prod_mul_distrib]
  congr 1
  · rw [← Fin.prod_univ_eq_prod_range (fun i => ∏ k ∈ Finset.Ioo i a, g i k * g i (2 * a - k)) a]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    exact (prod_filter_gt_eq_prod_Ioo a i (fun k => g i k * g i (2 * a - k))).symm
  · exact (Fin.prod_univ_eq_prod_range (fun i => g i a * g i (2 * a - i)) a).symm

end GlobalTheory
end
