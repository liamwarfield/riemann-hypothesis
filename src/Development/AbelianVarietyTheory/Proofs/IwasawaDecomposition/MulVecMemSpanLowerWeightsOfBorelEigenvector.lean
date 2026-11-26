module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolyRep

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteShiftsVanishingLeadingMinor
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteShiftsVanishingLeadingMinor
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

namespace GlobalTheory

theorem shift_minors_vanish_finite {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) :
    Set.Finite {s : ℂ | ¬ ∀ (k : ℕ) (hk : k ≤ n),
      ((B + s • (1 : Matrix (Fin n) (Fin n) ℂ)).submatrix (Fin.castLE hk) (Fin.castLE hk)).det ≠ 0} := by
  classical
  let p : ℕ → Polynomial ℂ := fun k =>
    if hk : k ≤ n then (-(B.submatrix (Fin.castLE hk) (Fin.castLE hk))).charpoly else 1
  have key : ∀ (k : ℕ) (hk : k ≤ n) (s : ℂ),
      ((B + s • (1 : Matrix (Fin n) (Fin n) ℂ)).submatrix (Fin.castLE hk) (Fin.castLE hk)).det
        = (p k).eval s := by
    intro k hk s
    simp only [p, dif_pos hk, Matrix.eval_charpoly]
    congr 1
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply,
      Matrix.neg_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply,
      Fin.castLE_inj, smul_eq_mul, sub_neg_eq_add]
    split_ifs <;> ring
  have hp : ∀ k, p k ≠ 0 := by
    intro k
    by_cases hk : k ≤ n
    · simp only [p, dif_pos hk]; exact (Matrix.charpoly_monic _).ne_zero
    · simp [p, dif_neg hk]
  refine Set.Finite.subset
    ((Finset.range (n + 1)).finite_toSet.biUnion fun k _ =>
      Polynomial.finite_setOf_isRoot (hp k)) ?_
  intro s hs
  simp only [Set.mem_setOf_eq, not_forall, not_not] at hs
  obtain ⟨k, hk, h0⟩ := hs
  simp only [Set.mem_iUnion, Finset.coe_range, Set.mem_Iio, Set.mem_setOf_eq]
  exact ⟨k, Nat.lt_succ_of_le hk, by rw [Polynomial.IsRoot, ← key k hk s, h0]⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteShiftsVanishingLeadingMinorStatement
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_shifts_vanishing_leading_minor : ∀ {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ), Set.Finite {s : ℂ | ¬ ∀ (k : ℕ) (hk : k ≤ n), ((B + s • (1 : Matrix (Fin n) (Fin n) ℂ)).submatrix (Fin.castLE hk) (Fin.castLE hk)).det ≠ 0} := by
  first | exact @GlobalTheory.shift_minors_vanish_finite | exact GlobalTheory.shift_minors_vanish_finite | (intros; apply GlobalTheory.shift_minors_vanish_finite <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLUDecompositionOfLeadingMinorsNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLUDecompositionOfLeadingMinorsNeZero
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

namespace GlobalTheory.LUDecomp

lemma exists_row {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) (i : Fin n)
    (hdet : (B.submatrix (Fin.castLE i.is_lt.le) (Fin.castLE i.is_lt.le)).det ≠ 0) :
    ∃ x : Fin n → ℂ, (∀ j, i ≤ j → x j = 0) ∧ ∀ k, k < i → B i k + ∑ j, x j * B j k = 0 := by
  have h : (i : ℕ) ≤ n := i.is_lt.le
  set A := B.submatrix (Fin.castLE h) (Fin.castLE h) with hAdef
  have hA : IsUnit A.det := isUnit_iff_ne_zero.mpr hdet
  let c : Fin i → ℂ := fun k => B i (Fin.castLE h k)
  let y : Fin i → ℂ := -(c ᵥ* A⁻¹)
  have hy : y ᵥ* A = -c := by
    simp only [y, Matrix.neg_vecMul, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hA, Matrix.vecMul_one]
  refine ⟨fun j => if hj : (j : ℕ) < i then y ⟨j, hj⟩ else 0, ?_, ?_⟩
  · intro j hj
    have : ¬ ((j : ℕ) < i) := not_lt.mpr hj
    simp [this]
  · intro k hk
    have hsum : ∑ j : Fin n, (if hj : (j : ℕ) < i then y ⟨j, hj⟩ else 0) * B j k
        = ∑ j' : Fin i, y j' * B (Fin.castLE h j') k := by
      symm
      apply Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h)
      · intro j hj
        have : ¬ ((j : ℕ) < i) := by
          intro hlt; exact hj ⟨⟨j, hlt⟩, Fin.ext rfl⟩
        simp [this]
      · intro j'
        simp [j'.is_lt]
    have hk' := congrFun hy ⟨k, hk⟩
    have hkk : Fin.castLE h ⟨k, hk⟩ = k := Fin.ext rfl
    simp only [Matrix.vecMul, dotProduct, hAdef, Matrix.submatrix_apply, Pi.neg_apply, hkk, c] at hk'
    rw [hsum, hk']
    ring

theorem lu : ∀ {n : ℕ} (B : GL (Fin n) ℂ), (∀ (k : ℕ) (hk : k ≤ n), (B.val.submatrix (Fin.castLE hk) (Fin.castLE hk)).det ≠ 0) → ∃ L U : GL (Fin n) ℂ, L.val.BlockTriangular OrderDual.toDual ∧ U.val.BlockTriangular id ∧ B = L * U := by
  intro n B hB
  have hx : ∀ i : Fin n, ∃ x : Fin n → ℂ, (∀ j, i ≤ j → x j = 0) ∧
      ∀ k, k < i → B.val i k + ∑ j, x j * B.val j k = 0 :=
    fun i => exists_row B.val i (hB i i.is_lt.le)
  choose x hx0 hx1 using hx
  let M : Matrix (Fin n) (Fin n) ℂ := fun i j => x i j + if i = j then 1 else 0
  have hMlow : M.BlockTriangular OrderDual.toDual := by
    intro i j hij
    have hij' : i < j := hij
    simp [M, hx0 i j hij'.le, hij'.ne]
  have hMdet : M.det = 1 := by
    rw [Matrix.det_of_lowerTriangular M hMlow]
    exact Finset.prod_eq_one (fun i _ => by simp [M, hx0 i i le_rfl])
  have hMunit : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).mpr (by rw [hMdet]; exact isUnit_one)
  let Mg : GL (Fin n) ℂ := hMunit.unit
  have hMg : (Mg : Matrix (Fin n) (Fin n) ℂ) = M := rfl
  refine ⟨Mg⁻¹, Mg * B, ?_, ?_, by simp⟩
  · rw [Matrix.coe_units_inv, hMg]
    have : Invertible M := M.invertibleOfIsUnitDet ((Matrix.isUnit_iff_isUnit_det M).mp hMunit)
    exact Matrix.blockTriangular_inv_of_blockTriangular hMlow
  · intro i k hik
    have hik' : k < i := hik
    show (M * B.val) i k = 0
    rw [Matrix.mul_apply]
    have := hx1 i k hik'
    simp only [M, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [add_comm]
    exact this

end GlobalTheory.LUDecomp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLUDecompositionOfLeadingMinorsNeZeroStatement
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_LU_decomposition_of_leading_minors_ne_zero : ∀ {n : ℕ} (B : GL (Fin n) ℂ), (∀ (k : ℕ) (hk : k ≤ n), (B.val.submatrix (Fin.castLE hk) (Fin.castLE hk)).det ≠ 0) → ∃ L U : GL (Fin n) ℂ, L.val.BlockTriangular OrderDual.toDual ∧ U.val.BlockTriangular id ∧ B = L * U := by
  first | exact @GlobalTheory.LUDecomp.lu | exact GlobalTheory.LUDecomp.lu | (intros; apply GlobalTheory.LUDecomp.lu <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowerTransvectionMulVecMemSpanWeightVectorsDomin
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowerTransvectionMulVecMemSpanWeightVectorsDomin
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

noncomputable section

namespace GlobalTheory.AlgWtHW.LowerTransv

open Polynomial

def tGL {n : ℕ} (i j : Fin n) (h : i ≠ j) (s : ℂ) : GL (Fin n) ℂ :=
  ⟨transvection i j s, transvection i j (-s),
    by rw [transvection_mul_transvection_same i j h, add_neg_cancel, transvection_zero],
    by rw [transvection_mul_transvection_same i j h, neg_add_cancel, transvection_zero]⟩

theorem inv_val {n : ℕ} {i j : Fin n} (h : i ≠ j) (s : ℂ) (T : GL (Fin n) ℂ)
    (hT : T.val = transvection i j s) : (T⁻¹).val = transvection i j (-s) := by
  have e : T = tGL i j h s := Units.ext hT
  subst e
  rfl

theorem eval_evalRingHom {σ : Type} (g : σ → ℂ[X]) (Q : MvPolynomial σ ℂ) (s : ℂ) :
    (MvPolynomial.aeval g Q).eval s = MvPolynomial.eval (fun v => (g v).eval s) Q := by
  rw [MvPolynomial.aeval_def, ← Polynomial.coe_evalRingHom, MvPolynomial.eval₂_comp_left]
  have : (Polynomial.evalRingHom s).comp (algebraMap ℂ ℂ[X]) = RingHom.id ℂ := by
    ext; simp
  rw [this]
  rfl

theorem expand {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ)
    (hΦ : IsPolyRep Φ) {i j : Fin n} (h : i ≠ j) (w : ι → ℂ) :
    ∃ q : ι → ℂ[X], ∀ (s : ℂ) (T : GL (Fin n) ℂ), T.val = transvection i j s →
      Φ T *ᵥ w = fun a => (q a).eval s := by
  choose Q hQ using hΦ.poly
  let g : (Fin n × Fin n) ⊕ (Fin n × Fin n) → ℂ[X] :=
    Sum.elim (fun p => (transvection i j (X : ℂ[X])) p.1 p.2)
      (fun p => (transvection i j (-X : ℂ[X])) p.1 p.2)
  refine ⟨fun a => ∑ b, MvPolynomial.aeval g (Q a b) * C (w b), ?_⟩
  intro s T hT
  funext a
  simp only [mulVec, dotProduct, eval_finsetSum, eval_mul, eval_C, eval_evalRingHom]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [hQ a b T]
  congr 2
  congr 1
  funext v
  rcases v with ⟨p1, p2⟩ | ⟨p1, p2⟩
  · simp only [g, Sum.elim_inl, hT, transvection, Matrix.add_apply, Matrix.one_apply,
      Matrix.single_apply]
    split_ifs <;> simp
  · simp only [g, Sum.elim_inr, inv_val h s T hT, transvection, Matrix.add_apply,
      Matrix.one_apply, Matrix.single_apply]
    split_ifs <;> simp

end GlobalTheory.AlgWtHW.LowerTransv

namespace GlobalTheory.AlgWtHW.LowerTransv

open Polynomial

theorem diagonal_eq_of_isDiag {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsDiag) :
    A = diagonal (fun m => A m m) := by
  ext a b
  by_cases hab : a = b
  · subst hab; simp
  · simp [diagonal_apply_ne _ hab, hA hab]

theorem diag_ne_zero {n : ℕ} (D : GL (Fin n) ℂ) (hD : D.val.IsDiag) (m : Fin n) :
    D.val m m ≠ 0 := by
  have hdet : (D.val).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp D.isUnit).ne_zero
  rw [diagonal_eq_of_isDiag _ hD, det_diagonal] at hdet
  exact (Finset.prod_ne_zero_iff.mp hdet) m (Finset.mem_univ _)

theorem diagonal_mul_transvection {n : ℕ} {i j : Fin n} (h : i ≠ j) (d : Fin n → ℂ)
    (hdj : d j ≠ 0) (s : ℂ) :
    diagonal d * transvection i j s = transvection i j (s * (d i / d j)) * diagonal d := by
  ext a b
  simp only [transvection, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.add_apply, diagonal_mul, mul_diagonal, Matrix.single_apply]
  by_cases h2 : i = a ∧ j = b
  · obtain ⟨rfl, rfl⟩ := h2
    simp only [and_self, if_true, one_apply_ne h]
    field_simp
    ring
  · simp only [h2, if_false, mul_zero, zero_mul, add_zero]
    by_cases hab : a = b
    · subst hab; simp
    · simp [one_apply_ne hab]

theorem conj_val {n : ℕ} {i j : Fin n} (h : i ≠ j) (D : GL (Fin n) ℂ) (hD : D.val.IsDiag)
    (s : ℂ) (T : GL (Fin n) ℂ) (hT : T.val = transvection i j s) :
    (D * T * D⁻¹).val = transvection i j (s * (D.val i i / D.val j j)) := by
  have key : D.val * T.val = transvection i j (s * (D.val i i / D.val j j)) * D.val := by
    have := diagonal_mul_transvection h (fun m => D.val m m) (diag_ne_zero D hD j) s
    rw [← diagonal_eq_of_isDiag _ hD] at this
    rw [hT]
    exact this
  rw [Units.val_mul, Units.val_mul, key, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel,
    Units.val_one, Matrix.mul_one]

end GlobalTheory.AlgWtHW.LowerTransv

namespace GlobalTheory.AlgWtHW.LowerTransv

open Polynomial

def shiftWt {n : ℕ} (ν : Fin n → ℤ) (i j : Fin n) (k : ℕ) : Fin n → ℤ :=
  fun m => ν m + (k : ℤ) * (if m = i then 1 else 0) - (k : ℤ) * (if m = j then 1 else 0)

theorem prod_zpow_shiftWt {n : ℕ} (d : Fin n → ℂ) (hd : ∀ m, d m ≠ 0) (ν : Fin n → ℤ)
    (i j : Fin n) (k : ℕ) :
    ∏ m, d m ^ (shiftWt ν i j k m) = (∏ m, d m ^ ν m) * (d i / d j) ^ k := by
  have e : ∀ m, d m ^ (shiftWt ν i j k m) =
      d m ^ ν m * ((if m = i then d m ^ (k : ℤ) else 1) / (if m = j then d m ^ (k : ℤ) else 1)) := by
    intro m
    simp only [shiftWt]
    rw [zpow_sub₀ (hd m), zpow_add₀ (hd m), mul_div_assoc]
    split_ifs <;> simp
  rw [Finset.prod_congr rfl (fun m _ => e m), Finset.prod_mul_distrib, Finset.prod_div_distrib,
    Finset.prod_ite_eq', Finset.prod_ite_eq']
  simp [div_pow, zpow_natCast]

theorem domLE_shiftWt {n : ℕ} {ν lam : Fin n → ℤ} (hν : DomLE ν lam) {i j : Fin n} (hji : j < i)
    (k : ℕ) : DomLE (shiftWt ν i j k) lam := by
  obtain ⟨h1, h2⟩ := hν
  constructor
  · rw [← h1]
    simp only [shiftWt, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  · intro K
    have hK := h2 K
    simp only [shiftWt, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_ite_eq', Finset.mem_filter, Finset.mem_univ, true_and]
    have hji' : (j : ℕ) < i := hji
    by_cases hi : (i : ℕ) < K
    · have hj : (j : ℕ) < K := lt_trans hji' hi
      simp only [hi, hj, if_true]
      linarith
    · simp only [hi, if_false, mul_zero, add_zero]
      have : (0 : ℤ) ≤ (k : ℤ) * (if (j : ℕ) < K then 1 else 0) := by
        split_ifs <;> simp
      linarith

theorem isWtVec_coeff {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ) (hΦ : IsPolyRep Φ) {i j : Fin n} (h : i ≠ j)
    (ν : Fin n → ℤ) (w : ι → ℂ) (hw : IsWtVec Φ ν w) (q : ι → ℂ[X])
    (hq : ∀ (s : ℂ) (T : GL (Fin n) ℂ), T.val = transvection i j s →
      Φ T *ᵥ w = fun a => (q a).eval s) (k : ℕ) :
    IsWtVec Φ (shiftWt ν i j k) (fun a => (q a).coeff k) := by
  intro D hD
  have hd : ∀ m, D.val m m ≠ 0 := diag_ne_zero D hD
  set c : ℂ := D.val i i / D.val j j with hc
  set P : ℂ := ∏ m, D.val m m ^ ν m with hP
  have hs : ∀ s : ℂ, Φ D *ᵥ (fun a => (q a).eval s) = P • (fun a => (q a).eval (s * c)) := by
    intro s
    have hT : (tGL i j h s).val = transvection i j s := rfl
    have hc' : Φ D * Φ (tGL i j h s) = Φ (D * tGL i j h s * D⁻¹) * Φ D := by
      rw [← hΦ.mul, ← hΦ.mul, inv_mul_cancel_right]
    rw [← hq s _ hT, ← hq (s * c) _ (conj_val h D hD s _ hT), mulVec_mulVec, hc',
      ← mulVec_mulVec, hw D hD, mulVec_smul]
  have hpoly : ∀ a, ∑ b, C (Φ D a b) * q b = C P * (q a).comp (C c * X) := by
    intro a
    apply Polynomial.funext
    intro s
    have e := congrFun (hs s) a
    simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at e
    simp only [eval_finsetSum, eval_mul, eval_C, eval_comp, eval_X]
    rw [e, mul_comm c s]
  funext a
  have e := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p k) (hpoly a)
  simp only [finsetSum_coeff, coeff_C_mul, comp_C_mul_X_coeff] at e
  simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
  rw [e, prod_zpow_shiftWt _ hd]
  ring

end GlobalTheory.AlgWtHW.LowerTransv

namespace GlobalTheory.AlgWtHW

open Polynomial LowerTransv

theorem lowerTransvection_mulVec_mem_Sle : ∀ {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ), IsPolyRep Φ → ∀ (lam ν : Fin n → ℤ), DomLE ν lam →
    ∀ (w : ι → ℂ), IsWtVec Φ ν w → ∀ (i j : Fin n), j < i → ∀ (s : ℂ) (T : GL (Fin n) ℂ),
    T.val = transvection i j s → Φ T *ᵥ w ∈ Sle Φ lam := by
  intro n ι _ _ Φ hΦ lam ν hν w hw i j hji s T hT
  have h : i ≠ j := hji.ne'
  obtain ⟨q, hq⟩ := expand Φ hΦ h w
  set N : ℕ := (Finset.univ.sup fun a => (q a).natDegree) + 1 with hN
  have hsum : Φ T *ᵥ w = ∑ k ∈ Finset.range N, s ^ k • (fun a => (q a).coeff k) := by
    rw [hq s T hT]
    funext a
    rw [Finset.sum_apply]
    have hlt : (q a).natDegree < N :=
      Nat.lt_succ_of_le (Finset.le_sup (f := fun a => (q a).natDegree) (Finset.mem_univ a))
    rw [eval_eq_sum_range' hlt]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hsum]
  refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  exact ⟨shiftWt ν i j k, domLE_shiftWt hν hji k, isWtVec_coeff Φ hΦ h ν w hw q hq k⟩

end GlobalTheory.AlgWtHW
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowerTransvectionMulVecMemSpanWeightVectorsDominStatement
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowerTransvection_mulVec_mem_spanWeightVectorsDominatedBy : ∀ {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ), IsPolyRep Φ → ∀ (lam ν : Fin n → ℤ), DomLE ν lam → ∀ (w : ι → ℂ), IsWtVec Φ ν w → ∀ (i j : Fin n), j < i → ∀ (s : ℂ) (T : GL (Fin n) ℂ), T.val = transvection i j s → Φ T *ᵥ w ∈ Sle Φ lam := by
  first | exact @GlobalTheory.AlgWtHW.lowerTransvection_mulVec_mem_Sle | exact GlobalTheory.AlgWtHW.lowerTransvection_mulVec_mem_Sle | (intros; apply GlobalTheory.AlgWtHW.lowerTransvection_mulVec_mem_Sle <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowerTriangularGLComplexInduction
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowerTriangularGLComplexInduction
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

namespace GlobalTheory

noncomputable def LowerGen.offDiagSupport {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun p => p.1 ≠ p.2 ∧ M p.1 p.2 ≠ 0

theorem LowerGen.lowerTriangular_elim_step {n : ℕ} (L : Matrix (Fin n) (Fin n) ℂ)
    (hL : L.BlockTriangular OrderDual.toDual) (i j : Fin n) (hij : j < i)
    (hjj : L j j ≠ 0)
    (hmin : ∀ a b : Fin n, b < j → a ≠ b → L a b = 0) (a b : Fin n) :
    (transvection i j (-L i j / L j j) * L) a b = if a = i ∧ b = j then 0 else L a b := by
  by_cases ha : a = i
  · subst ha
    rw [transvection_mul_apply_same]
    have hrow : L j b = if b = j then L j j else 0 := by
      rcases lt_trichotomy b j with h | h | h
      · rw [if_neg h.ne]; exact hmin j b h (Ne.symm h.ne)
      · subst h; simp
      · rw [if_neg h.ne']; exact hL (by simpa using h)
    rw [hrow]
    by_cases hb : b = j
    · subst hb; simp; field_simp; ring
    · simp [hb]
  · rw [transvection_mul_apply_of_ne _ _ _ _ ha]; simp [ha]

end GlobalTheory

open GlobalTheory GlobalTheory.LowerGen in
theorem GlobalTheory.lowerTriangular_GL_induction : ∀ {n : ℕ} (P : GL (Fin n) ℂ → Prop), P 1 → (∀ A B, P A → P B → P (A * B)) →
    (∀ D : GL (Fin n) ℂ, D.val.IsDiag → P D) →
    (∀ (i j : Fin n) (s : ℂ) (T : GL (Fin n) ℂ), j < i → T.val = transvection i j s → P T) →
    ∀ L : GL (Fin n) ℂ, L.val.BlockTriangular OrderDual.toDual → P L := by
  intro n P _h1 hmul hdiag htr
  suffices H : ∀ m : ℕ, ∀ L : GL (Fin n) ℂ, L.val.BlockTriangular OrderDual.toDual →
      (LowerGen.offDiagSupport L.val).card = m → P L by
    intro L hL; exact H _ L hL rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro L hL hm

  have hdet : L.val.det ≠ 0 := by
    have h := congrArg Matrix.det L.mul_inv
    rw [Matrix.det_mul, Matrix.det_one] at h
    exact left_ne_zero_of_mul_eq_one h
  have hdiag0 : ∀ k, L.val k k ≠ 0 := by
    rw [Matrix.det_of_lowerTriangular _ hL] at hdet
    exact fun k => (Finset.prod_ne_zero_iff.mp hdet) k (Finset.mem_univ _)
  by_cases hS : (LowerGen.offDiagSupport L.val) = ∅
  · apply hdiag
    intro a b hab
    by_contra hne
    have : (a, b) ∈ LowerGen.offDiagSupport L.val := by simp [LowerGen.offDiagSupport, hab, hne]
    rw [hS] at this; simp at this
  ·
    have hne : (LowerGen.offDiagSupport L.val).Nonempty := Finset.nonempty_iff_ne_empty.mpr hS
    let cols := (LowerGen.offDiagSupport L.val).image Prod.snd
    have hcols : cols.Nonempty := hne.image _
    set j := cols.min' hcols with hjdef
    have hjmem : j ∈ cols := Finset.min'_mem _ _
    obtain ⟨⟨i, jj⟩, hp, hj'⟩ := Finset.mem_image.mp hjmem
    simp only at hj'
    subst hj'
    simp only [LowerGen.offDiagSupport, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨hij, hLij⟩ := hp
    have hlt : j < i := by
      rcases lt_or_gt_of_ne hij with h | h
      · exact absurd (hL (by simpa using h)) hLij
      · exact h
    have hmin : ∀ a b : Fin n, b < j → a ≠ b → L.val a b = 0 := by
      intro a b hb hab
      by_contra hne'
      have hbm : b ∈ cols := Finset.mem_image.mpr
        ⟨(a, b), by simp [LowerGen.offDiagSupport, hab, hne'], rfl⟩
      have := Finset.min'_le cols b hbm
      rw [← hjdef] at this
      exact absurd hb (not_lt.mpr this)
    set c : ℂ := -L.val i j / L.val j j with hc
    have hijne : i ≠ j := hij
    let U : GL (Fin n) ℂ := ⟨transvection i j c, transvection i j (-c),
      by rw [transvection_mul_transvection_same _ _ hij]; simp,
      by rw [transvection_mul_transvection_same _ _ hij]; simp⟩
    let V : GL (Fin n) ℂ := ⟨transvection i j (-c), transvection i j c,
      by rw [transvection_mul_transvection_same _ _ hij]; simp,
      by rw [transvection_mul_transvection_same _ _ hij]; simp⟩
    have hentry := LowerGen.lowerTriangular_elim_step L.val hL i j hlt (hdiag0 j) hmin
    have hUL : ∀ a b, (U * L).val a b = if a = i ∧ b = j then 0 else L.val a b := by
      intro a b; exact hentry a b
    have hlowUL : (U * L).val.BlockTriangular OrderDual.toDual := by
      intro a b hab
      rw [hUL]
      split_ifs with h
      · rfl
      · exact hL hab
    have hsupp : LowerGen.offDiagSupport (U * L).val = (LowerGen.offDiagSupport L.val).erase (i, j) := by
      ext ⟨a, b⟩
      simp only [LowerGen.offDiagSupport, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_erase, hUL, ne_eq, Prod.mk.injEq]
      by_cases h : a = i ∧ b = j
      · simp [h]
      · simp only [h, if_false]; tauto
    have hcard : (LowerGen.offDiagSupport (U * L).val).card < m := by
      rw [hsupp, ← hm]
      apply Finset.card_erase_lt_of_mem
      simp [LowerGen.offDiagSupport, hij, hLij]
    have hPUL : P (U * L) := ih _ hcard _ hlowUL rfl
    have hPV : P V := htr i j (-c) V hlt rfl
    have hVUL : V * (U * L) = L := by
      rw [← mul_assoc]
      have : V * U = 1 := by
        ext : 1
        show transvection i j (-c) * transvection i j c = 1
        rw [transvection_mul_transvection_same _ _ hij]; simp
      rw [this, one_mul]
    rw [← hVUL]
    exact hmul _ _ hPV hPUL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowerTriangularGLComplexInductionStatement
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowerTriangular_GL_complex_induction : ∀ {n : ℕ} (P : GL (Fin n) ℂ → Prop), P 1 → (∀ A B, P A → P B → P (A * B)) → (∀ D : GL (Fin n) ℂ, D.val.IsDiag → P D) → (∀ (i j : Fin n) (s : ℂ) (T : GL (Fin n) ℂ), j < i → T.val = transvection i j s → P T) → ∀ L : GL (Fin n) ℂ, L.val.BlockTriangular OrderDual.toDual → P L := by
  first | exact @GlobalTheory.lowerTriangular_GL_induction | exact GlobalTheory.lowerTriangular_GL_induction | (intros; apply GlobalTheory.lowerTriangular_GL_induction <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolyRepMulVecMemOfCofiniteScalarShift
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolyRepMulVecMemOfCofiniteScalarShift
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

namespace GlobalTheory.AlgWtHW

theorem mulVec_mem_of_cofinite_shift : ∀ {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ), IsPolyRep Φ → ∀ (S : Submodule ℂ (ι → ℂ)) (v : ι → ℂ)
    (B : GL (Fin n) ℂ) (F : Set ℂ), F.Finite →
    (∀ s ∉ F, ∀ C : GL (Fin n) ℂ, C.val = B.val + s • (1 : Matrix (Fin n) (Fin n) ℂ) → Φ C *ᵥ v ∈ S) →
    Φ B *ᵥ v ∈ S := by
  intro n ι _ _ Φ hΦ S v B F hF hS
  choose Q hQ using hΦ.poly
  let M : ℂ → Matrix (Fin n) (Fin n) ℂ := fun s => B.val + s • (1 : Matrix (Fin n) (Fin n) ℂ)
  let x : ℂ → ((Fin n × Fin n) ⊕ (Fin n × Fin n)) → ℂ :=
    fun s => Sum.elim (fun p => M s p.1 p.2) (fun p => (M s)⁻¹ p.1 p.2)
  let g : ℂ → ι → ℂ := fun s i => ∑ j, MvPolynomial.eval (x s) (Q i j) * v j
  have hMc : Continuous M := by
    fun_prop
  have hdetB : IsUnit (B.val).det := (Matrix.isUnit_iff_isUnit_det _).1 B.isUnit
  have hM0 : M 0 = B.val := by simp [M]
  have hinvc : ContinuousAt (fun s => (M s)⁻¹) 0 := by
    have h1 : ContinuousAt Inv.inv (M 0) := by
      apply continuousAt_matrix_inv
      rw [hM0]
      exact NormedRing.inverse_continuousAt hdetB.unit
    exact h1.comp hMc.continuousAt
  have hxc : ContinuousAt x 0 := by
    rw [continuousAt_pi]
    rintro (p | p)
    · exact ((continuous_apply p.2).comp ((continuous_apply p.1).comp hMc)).continuousAt
    · exact ((continuous_apply p.2).comp (continuous_apply p.1)).continuousAt.comp hinvc
  have hgc : ContinuousAt g 0 := by
    rw [continuousAt_pi]
    intro i
    apply tendsto_finsetSum
    intro j _
    exact (((MvPolynomial.continuous_eval (Q i j)).continuousAt).comp hxc).mul continuousAt_const

  have hgC : ∀ s, ∀ C : GL (Fin n) ℂ, C.val = M s → g s = Φ C *ᵥ v := by
    intro s C hC
    funext i
    simp only [g, Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hQ i j C]
    have hx : x s = Sum.elim (fun p => C.val p.1 p.2) (fun p => (C⁻¹).val p.1 p.2) := by
      funext q
      rcases q with p | p
      · simp [x, hC]
      · simp [x, Matrix.coe_units_inv, hC]
    rw [hx]
  have hg0 : g 0 = Φ B *ᵥ v := hgC 0 B hM0.symm
  have hdetev : ∀ᶠ s in nhds (0:ℂ), IsUnit (M s).det := by
    have hc : ContinuousAt (fun s => (M s).det) 0 := hMc.matrix_det.continuousAt
    have : IsOpen {z : ℂ | z ≠ 0} := isOpen_ne
    have hne : (M 0).det ≠ 0 := by rw [hM0]; exact hdetB.ne_zero
    filter_upwards [hc.eventually (this.mem_nhds hne)] with s hs
    exact isUnit_iff_ne_zero.2 hs
  have hFev : ∀ᶠ s in nhdsWithin (0:ℂ) {0}ᶜ, s ∉ F := by
    have hcl : IsClosed (F \ {0}) := (hF.diff).isClosed
    have hmem : (F \ {0})ᶜ ∈ nhds (0:ℂ) := hcl.isOpen_compl.mem_nhds (by simp)
    filter_upwards [nhdsWithin_le_nhds hmem, self_mem_nhdsWithin] with s hs1 hs2
    intro hsF
    exact hs1 ⟨hsF, hs2⟩
  have hev : ∀ᶠ s in nhdsWithin (0:ℂ) {0}ᶜ, g s ∈ S := by
    filter_upwards [hFev, nhdsWithin_le_nhds hdetev] with s hs hdet
    rw [hgC s (Matrix.nonsingInvUnit (M s) hdet) rfl]
    exact hS s hs _ rfl
  have ht : Filter.Tendsto g (nhdsWithin (0:ℂ) {0}ᶜ) (nhds (Φ B *ᵥ v)) := by
    rw [← hg0]
    exact hgc.tendsto.mono_left nhdsWithin_le_nhds
  exact (Submodule.closed_of_finiteDimensional S).mem_of_tendsto ht hev

end GlobalTheory.AlgWtHW
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolyRepMulVecMemOfCofiniteScalarShiftStatement
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polyRep_mulVec_mem_of_cofinite_scalar_shift : ∀ {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ), IsPolyRep Φ → ∀ (S : Submodule ℂ (ι → ℂ)) (v : ι → ℂ) (B : GL (Fin n) ℂ) (F : Set ℂ), F.Finite → (∀ s ∉ F, ∀ C : GL (Fin n) ℂ, C.val = B.val + s • (1 : Matrix (Fin n) (Fin n) ℂ) → Φ C *ᵥ v ∈ S) → Φ B *ᵥ v ∈ S := by
  first | exact @GlobalTheory.AlgWtHW.mulVec_mem_of_cofinite_shift | exact GlobalTheory.AlgWtHW.mulVec_mem_of_cofinite_shift | (intros; apply GlobalTheory.AlgWtHW.mulVec_mem_of_cofinite_shift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MulVecMemSpanLowerWeightsOfBorelEigenvector
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

namespace GlobalTheory.AlgWtHW

theorem mulVec_mem_sle_of_isBEig : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ), IsPolyRep Φ → ∀ (v : ι → ℂ) (lam : Fin n → ℤ), IsBEig Φ v lam → ∀ B : GL (Fin n) ℂ, Φ B *ᵥ v ∈ Sle Φ lam := by
  intro n ι _ _ Φ hΦ v lam hv B
  have hdom : DomLE lam lam := ⟨rfl, fun _ => le_rfl⟩
  have hvS : v ∈ Sle Φ lam := by
    refine Submodule.subset_span ⟨lam, hdom, fun D hD => hv.2 D ?_⟩
    intro a b hab
    exact hD (ne_of_gt hab)

  have hstab : ∀ L : GL (Fin n) ℂ, L.val.BlockTriangular OrderDual.toDual →
      ∀ w ∈ Sle Φ lam, Φ L *ᵥ w ∈ Sle Φ lam := by
    refine GlobalTheory.T.lowerTriangular_GL_complex_induction _ ?_ ?_ ?_ ?_
    · intro w hw; rw [hΦ.one, one_mulVec]; exact hw
    · intro A C hA hC w hw
      rw [hΦ.mul, ← mulVec_mulVec]
      exact hA _ (hC w hw)
    · intro D hD w hw
      refine Submodule.span_induction (p := fun w _ => Φ D *ᵥ w ∈ Sle Φ lam) ?_ ?_ ?_ ?_ hw
      · rintro u ⟨ν, hν, hu⟩
        rw [hu D hD]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨ν, hν, hu⟩)
      · simp
      · intro x y _ _ hx hy; rw [mulVec_add]; exact Submodule.add_mem _ hx hy
      · intro c x _ hx; rw [mulVec_smul]; exact Submodule.smul_mem _ _ hx
    · intro i j s T hji hT w hw
      refine Submodule.span_induction (p := fun w _ => Φ T *ᵥ w ∈ Sle Φ lam) ?_ ?_ ?_ ?_ hw
      · rintro u ⟨ν, hν, hu⟩
        exact GlobalTheory.T.lowerTransvection_mulVec_mem_spanWeightVectorsDominatedBy Φ hΦ lam ν hν u hu i j hji s T hT
      · simp
      · intro x y _ _ hx hy; rw [mulVec_add]; exact Submodule.add_mem _ hx hy
      · intro c x _ hx; rw [mulVec_smul]; exact Submodule.smul_mem _ _ hx

  have hbig : ∀ C : GL (Fin n) ℂ,
      (∀ (k : ℕ) (hk : k ≤ n), (C.val.submatrix (Fin.castLE hk) (Fin.castLE hk)).det ≠ 0) →
      Φ C *ᵥ v ∈ Sle Φ lam := by
    intro C hC
    obtain ⟨L, U, hL, hU, rfl⟩ := GlobalTheory.T.exists_LU_decomposition_of_leading_minors_ne_zero C hC
    rw [hΦ.mul, ← mulVec_mulVec, hv.2 U hU, mulVec_smul]
    exact Submodule.smul_mem _ _ (hstab L hL v hvS)

  refine GlobalTheory.T.polyRep_mulVec_mem_of_cofinite_scalar_shift Φ hΦ _ v B _ (GlobalTheory.T.finite_shifts_vanishing_leading_minor B.val) ?_
  intro s hs C hC
  apply hbig
  rw [hC]
  simpa using hs

end GlobalTheory.AlgWtHW
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MulVecMemSpanLowerWeightsOfBorelEigenvectorStatement
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mulVec_mem_span_lower_weights_of_borelEigenvector : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ), IsPolyRep Φ → ∀ (v : ι → ℂ) (lam : Fin n → ℤ), IsBEig Φ v lam → ∀ B : GL (Fin n) ℂ, Φ B *ᵥ v ∈ Sle Φ lam := by
  first | exact @GlobalTheory.AlgWtHW.mulVec_mem_sle_of_isBEig | exact GlobalTheory.AlgWtHW.mulVec_mem_sle_of_isBEig | (intros; apply GlobalTheory.AlgWtHW.mulVec_mem_sle_of_isBEig <;> assumption)
end
