module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalRepGLExistsSatakeParameters
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChainLocalDataIntegralOffLevels

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HermitianDualSubsetOfIntegralGram
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualIntegralPreimageLeSumTransposeImage
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmithNormalFormDiscreteValuationField
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmithNormalFormDiscreteValuationField
open Matrix

namespace GlobalTheory.SmithValued

variable (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))]

noncomputable def vNN : Valuation L NNReal :=
  (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).map
    { toMonoidWithZeroHom := WithZeroMulInt.toNNReal (e := 2) (by norm_num)
      monotone' := (WithZeroMulInt.toNNReal_strictMono (e := 2) (by norm_num)).monotone }

theorem vNN_le_one_iff (x : L) : vNN L x ≤ 1 ↔ x ∈ Formalism.UG.intL L := by
  have h := (WithZeroMulInt.toNNReal_strictMono (e := 2) (by norm_num)).le_iff_le
    (a := (Valued.v x : WithZero (Multiplicative ℤ))) (b := 1)
  rw [map_one] at h
  exact h

theorem vNN_integers : (vNN L).Integers ↥(Formalism.UG.intL L) := by
  refine ⟨Subtype.val_injective, ?_, ?_⟩
  · intro x
    exact (vNN_le_one_iff L _).2 x.2
  · intro r hr
    exact ⟨⟨r, (vNN_le_one_iff L _).1 hr⟩, rfl⟩

theorem exists_clear {ι : Type} (s : Finset ι) (f : ι → L) :
    ∃ c : L, c ≠ 0 ∧ c ∈ Formalism.UG.intL L ∧ ∀ i ∈ s, c * f i ∈ Formalism.UG.intL L := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, one_mem _, by simp⟩
  | insert a s _ ih =>
    obtain ⟨c, hc0, hc, hs⟩ := ih
    by_cases ha : f a ∈ Formalism.UG.intL L
    · refine ⟨c, hc0, hc, fun i hi => ?_⟩
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact mul_mem hc ha
      · exact hs i hi
    · have h0 : f a ≠ 0 := by
        intro h; exact ha (h ▸ zero_mem _)
      have hinv : (f a)⁻¹ ∈ Formalism.UG.intL L := by
        rw [← vNN_le_one_iff] at ha ⊢
        rw [map_inv₀]
        exact inv_le_one_of_one_le₀ (not_le.1 ha).le
      refine ⟨(f a)⁻¹ * c, mul_ne_zero (inv_ne_zero h0) hc0, mul_mem hinv hc, fun i hi => ?_⟩
      rcases Finset.mem_insert.1 hi with rfl | hi
      · have : (f i)⁻¹ * c * f i = c := by field_simp
        rw [this]; exact hc
      · rw [mul_assoc]; exact mul_mem hinv (hs i hi)

theorem smith_valued : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (m n : ℕ) (M : Matrix (Fin m) (Fin n) L),
    ∃ (P P' : Matrix (Fin m) (Fin m) L) (Q Q' : Matrix (Fin n) (Fin n) L) (d : Fin m → L),
      (∀ i j, P i j ∈ Formalism.UG.intL L) ∧ (∀ i j, P' i j ∈ Formalism.UG.intL L) ∧
      (∀ i j, Q i j ∈ Formalism.UG.intL L) ∧ (∀ i j, Q' i j ∈ Formalism.UG.intL L) ∧ P * P' = 1 ∧ Q * Q' = 1 ∧
      M = P * Matrix.of (fun (j : Fin m) (k : Fin n) => if (k : ℕ) = (j : ℕ) then d j else 0) * Q := by
  intro L _ _ m n M
  classical
  obtain ⟨c, hc0, -, hc⟩ := exists_clear L (Finset.univ : Finset (Fin m × Fin n))
    (fun p => M p.1 p.2)
  let A : Matrix (Fin m) (Fin n) ↥(Formalism.UG.intL L) :=
    Matrix.of fun i j => ⟨c * M i j, hc (i, j) (Finset.mem_univ _)⟩
  have diagonalize : ∀ (d n : ℕ) (X : Matrix (Fin d) (Fin n) ↥(Formalism.UG.intL L)),
      ∃ (P : Matrix (Fin d) (Fin d) ↥(Formalism.UG.intL L))
        (Q : Matrix (Fin n) (Fin n) ↥(Formalism.UG.intL L)) (a : Fin d → ↥(Formalism.UG.intL L)),
        IsUnit P.det ∧ IsUnit Q.det ∧
          ∀ j k, (P * X * Q) j k = if (k : ℕ) = (j : ℕ) then a j else 0 := by
    open ReciprocityTheory.PGsh.Up.Smith in
    intro d
    induction d with
    | zero =>
      intro n X
      exact ⟨1, 1, Fin.elim0, by simp, by simp, fun j => j.elim0⟩
    | succ d ih =>
      intro n X
      cases n with
      | zero => exact ⟨1, 1, 0, by simp, by simp, fun j k => k.elim0⟩
      | succ n =>
        let g : Fin (n + 1) → Fin (d + 1) → ↥(Formalism.UG.intL L) := fun j i => X i j
        obtain ⟨i₀, a, u, s, hu, -, hs, hz, hnz⟩ := exists_pivot (vNN_integers L) g
        by_cases ha : a = 0
        · have hX : X = 0 := by
            apply Matrix.ext
            intro i j
            exact congrFun (hz ha j) i
          exact ⟨1, 1, 0, by simp, by simp, fun j k => by simp [hX]⟩
        obtain ⟨j₀, hj₀, hs₀⟩ := hnz ha
        have hcol : ∀ i, X i j₀ = a * u i := fun i => congrFun hj₀ i
        have hrow : ∀ j, X i₀ j = a * s j := hs
        let B := (Vm i₀ u)ᵀ * X * Vm j₀ s
        have hB (i j) : B i j = if i = i₀ then (if j = j₀ then a else 0) else
            if j = j₀ then 0 else X i j - s j * (a * u i) := by
          dsimp only [B]
          rw [Matrix.mul_assoc, VmT_mul, mul_Vm, mul_Vm]
          by_cases hi : i = i₀ <;> by_cases hj : j = j₀
          · subst i
            subst j
            simp [hcol, hu]
          · subst i
            simp [hj, hrow, hs₀]
            ring
          · subst j
            simp [hi, hcol, hu]
            ring
          · simp only [hi, hj, ite_false, hcol, hrow, hu]
            ring
        let C := B.submatrix (piv i₀) (piv j₀)
        let Y := Matrix.of fun (i : Fin d) (j : Fin n) => C i.succ j.succ
        obtain ⟨P, Q, b, hP, hQ, hY⟩ := ih n Y
        let U : Matrix (Fin (d + 1)) (Fin (d + 1)) ↥(Formalism.UG.intL L) :=
          (piv i₀).toPEquiv.toMatrix
        let V : Matrix (Fin (n + 1)) (Fin (n + 1)) ↥(Formalism.UG.intL L) :=
          (piv j₀).symm.toPEquiv.toMatrix
        have hC : U * B * V = C := by
          dsimp only [U, V, C]
          rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, Equiv.symm_symm]
          rfl
        have hrow₀ (j : Fin n) : C 0 j.succ = 0 := by
          simp [C, piv_zero, piv_succ, hB, Fin.succAbove_ne]
        have hcol₀ (i : Fin d) : C i.succ 0 = 0 := by
          simp [C, piv_zero, piv_succ, hB, Fin.succAbove_ne]
        obtain ⟨h00, h0j, hi0, hij⟩ := blockOne_mul_mul_blockOne P C Q hrow₀ hcol₀
        refine ⟨bd1 P * U * (Vm i₀ u)ᵀ, Vm j₀ s * V * bd1 Q, Fin.cons a b, ?_, ?_, ?_⟩
        · rw [Matrix.det_mul, Matrix.det_mul, det_blockOne_alt, Matrix.det_transpose, det_Vm, mul_one]
          exact hP.mul (isUnit_det_perm _)
        · rw [Matrix.det_mul, Matrix.det_mul, det_blockOne_alt, det_Vm, one_mul]
          exact (isUnit_det_perm _).mul hQ
        · have hfull : bd1 P * U * (Vm i₀ u)ᵀ * X * (Vm j₀ s * V * bd1 Q) =
              bd1 P * C * bd1 Q := by
            rw [← hC]
            simp only [B, Matrix.mul_assoc]
          intro i j
          rw [hfull]
          refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
          · rw [h00]
            simp [C, piv_zero, hB]
          · rw [h0j]
            simp
          · rw [hi0]
            simp
          · rw [hij, hY]
            simp [Fin.val_succ]
  obtain ⟨P, Q, a, hP, hQ, hD⟩ := diagonalize m n A
  let φ : ↥(Formalism.UG.intL L) →+* L := (Formalism.UG.intL L).subtype
  have hP1 : P⁻¹.map φ * P.map φ = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hP, Matrix.map_one _ (map_zero φ) (map_one φ)]
  have hQ1 : Q⁻¹.map φ * Q.map φ = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hQ, Matrix.map_one _ (map_zero φ) (map_one φ)]
  have hQ2 : Q.map φ * Q⁻¹.map φ = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hQ, Matrix.map_one _ (map_zero φ) (map_one φ)]
  refine ⟨P⁻¹.map φ, P.map φ, Q⁻¹.map φ, Q.map φ, fun j => c⁻¹ * (a j : L),
    fun i j => (P⁻¹ i j).2, fun i j => (P i j).2, fun i j => (Q⁻¹ i j).2, fun i j => (Q i j).2,
    hP1, hQ1, ?_⟩
  have hA : A.map φ = c • M := by
    ext i j; simp [A, φ]
  have hD' : Matrix.of (fun (j : Fin m) (k : Fin n) =>
      if (k : ℕ) = (j : ℕ) then c⁻¹ * (a j : L) else 0) = P.map φ * M * Q.map φ := by
    have h1 : (P * A * Q).map φ = c • (P.map φ * M * Q.map φ) := by
      rw [Matrix.map_mul, Matrix.map_mul, hA, Matrix.mul_smul, Matrix.smul_mul]
    have h2 : P.map φ * M * Q.map φ = c⁻¹ • (P * A * Q).map φ := by
      rw [h1, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    rw [h2]
    ext j k
    rw [Matrix.of_apply, Matrix.smul_apply, Matrix.map_apply, hD, smul_eq_mul]
    split_ifs
    · rfl
    · simp
  rw [hD', ← Matrix.mul_assoc, ← Matrix.mul_assoc, hP1, Matrix.one_mul, Matrix.mul_assoc, hQ2,
    Matrix.mul_one]

end GlobalTheory.SmithValued
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmithNormalFormDiscreteValuationFieldStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smithNormalForm_discreteValuationField : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (m n : ℕ) (M : Matrix (Fin m) (Fin n) L),
    ∃ (P P' : Matrix (Fin m) (Fin m) L) (Q Q' : Matrix (Fin n) (Fin n) L) (d : Fin m → L),
      (∀ i j, P i j ∈ Formalism.UG.intL L) ∧ (∀ i j, P' i j ∈ Formalism.UG.intL L) ∧
      (∀ i j, Q i j ∈ Formalism.UG.intL L) ∧ (∀ i j, Q' i j ∈ Formalism.UG.intL L) ∧ P * P' = 1 ∧ Q * Q' = 1 ∧
      M = P * Matrix.of (fun (j : Fin m) (k : Fin n) => if (k : ℕ) = (j : ℕ) then d j else 0) * Q := by
  first | exact @GlobalTheory.SmithValued.smith_valued | exact GlobalTheory.SmithValued.smith_valued | (intros; apply GlobalTheory.SmithValued.smith_valued <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualIntegralPreimageLeSumTransposeImage
open Matrix

namespace GlobalTheory.LatticeDuality

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem mem_int_iff (a : L) : a ∈ Formalism.UG.intL L ↔ Valued.v a ≤ 1 := Iff.rfl

theorem mulVec_int {m n : ℕ} (A : Matrix (Fin m) (Fin n) L) (u : Fin n → L)
    (hA : ∀ i j, A i j ∈ Formalism.UG.intL L) (hu : ∀ i, u i ∈ Formalism.UG.intL L) :
    ∀ i, (A *ᵥ u) i ∈ Formalism.UG.intL L := fun i => by
  simp only [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hA i j) (hu j)

theorem one_dim (e z : L)
    (h : ∀ c : L, c ∈ Formalism.UG.intL L → e * c ∈ Formalism.UG.intL L → c * z ∈ Formalism.UG.intL L) :
    ∃ a b : L, a ∈ Formalism.UG.intL L ∧ b ∈ Formalism.UG.intL L ∧ z = a + e * b := by
  by_cases he : e ∈ Formalism.UG.intL L
  · refine ⟨z, 0, ?_, Subring.zero_mem _, by simp⟩
    simpa using h 1 (Subring.one_mem _) (by simpa using he)
  · have he0 : e ≠ 0 := by
      rintro rfl
      exact he (Subring.zero_mem _)
    have hlt : 1 < Valued.v e := not_le.mp ((mem_int_iff e).not.mp he)
    have hinv : e⁻¹ ∈ Formalism.UG.intL L := by
      rw [mem_int_iff, map_inv₀]
      exact inv_le_one_of_one_le₀ hlt.le
    refine ⟨0, e⁻¹ * z, Subring.zero_mem _, h _ hinv ?_, ?_⟩
    · rw [mul_inv_cancel₀ he0]; exact Subring.one_mem _
    · field_simp
      simp

theorem diag_case {m n : ℕ} (d : Fin m → L) (z : Fin n → L)
    (h : ∀ u : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) →
      (∀ i, ((Matrix.of (fun (j : Fin m) (k : Fin n) => if (k : ℕ) = (j : ℕ) then d j else 0)) *ᵥ u) i
        ∈ Formalism.UG.intL L) → (∑ i, u i * z i) ∈ Formalism.UG.intL L) :
    ∃ l : Fin n → L, ∃ w : Fin m → L, (∀ i, l i ∈ Formalism.UG.intL L) ∧ (∀ i, w i ∈ Formalism.UG.intL L) ∧
      z = l + (Matrix.of (fun (j : Fin m) (k : Fin n) => if (k : ℕ) = (j : ℕ) then d j else 0))ᵀ *ᵥ w := by
  have key : ∀ k : Fin n, ∃ a b : L, a ∈ Formalism.UG.intL L ∧ b ∈ Formalism.UG.intL L ∧
      z k = a + (if hk : (k : ℕ) < m then d ⟨k, hk⟩ else 0) * b := by
    intro k
    apply one_dim
    intro c hc hec
    have := h (Pi.single k c) ?_ ?_
    · simpa [Pi.single_apply] using this
    · intro i
      by_cases hi : i = k
      · subst hi; simpa using hc
      · simp [hi]
    · intro j
      rw [Matrix.mulVec_single]
      by_cases hj : (k : ℕ) = (j : ℕ)
      · have hk : (k : ℕ) < m := hj ▸ j.2
        have : (⟨k, hk⟩ : Fin m) = j := Fin.ext hj
        rw [dite_eq_left hk, this] at hec
        simpa [hj] using hec
      · simp [hj]
  choose a b ha hb hz using key
  refine ⟨a, fun j => if hj : (j : ℕ) < n then b ⟨j, hj⟩ else 0, ha, ?_, ?_⟩
  · intro j
    dsimp only
    split_ifs
    · exact hb _
    · exact Subring.zero_mem _
  · funext k
    rw [hz k, Pi.add_apply]
    congr 1
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.of_apply]
    by_cases hk : (k : ℕ) < m
    · rw [dite_eq_left hk, Finset.sum_eq_single (⟨k, hk⟩ : Fin m)]
      · simp
      · intro j _ hj
        have : (k : ℕ) ≠ (j : ℕ) := fun e => hj (Fin.ext e.symm)
        simp [this]
      · simp
    · rw [dite_eq_right hk, zero_mul]
      symm
      refine Finset.sum_eq_zero fun j _ => ?_
      have : (k : ℕ) ≠ (j : ℕ) := fun e => hk (e ▸ j.2)
      simp [this]

theorem dual_subset : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (m n : ℕ) (x : Matrix (Fin m) (Fin n) L)
    (z : Fin n → L),
    (∀ u : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) → (∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L) → (∑ i, u i * z i) ∈ Formalism.UG.intL L) →
    ∃ l : Fin n → L, ∃ w : Fin m → L, (∀ i, l i ∈ Formalism.UG.intL L) ∧ (∀ i, w i ∈ Formalism.UG.intL L) ∧ z = l + xᵀ *ᵥ w := by
  intro L _ _ m n x z h
  obtain ⟨P, P', Q, Q', d, hP, hP', hQ, hQ', hPP, hQQ, hx⟩ := GlobalTheory.T.smithNormalForm_discreteValuationField L m n x
  set D : Matrix (Fin m) (Fin n) L :=
    Matrix.of (fun (j : Fin m) (k : Fin n) => if (k : ℕ) = (j : ℕ) then d j else 0) with hD
  have hPP' : P' * P = 1 := mul_eq_one_comm.mp hPP
  have hQQ' : Q' * Q = 1 := mul_eq_one_comm.mp hQQ
  obtain ⟨l, w, hl, hw, hz⟩ := diag_case d (Q'ᵀ *ᵥ z) (by
    intro s hs hDs
    have h1 := h (Q' *ᵥ s) (mulVec_int _ _ hQ' hs) (by
      have : x *ᵥ (Q' *ᵥ s) = P *ᵥ (D *ᵥ s) := by
        rw [hx, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc (P * D), hQQ, Matrix.mul_one]
      rw [this]
      exact mulVec_int _ _ hP hDs)
    have h2 : ∑ i, s i * (Q'ᵀ *ᵥ z) i = ∑ i, (Q' *ᵥ s) i * z i := by
      change s ⬝ᵥ (Q'ᵀ *ᵥ z) = (Q' *ᵥ s) ⬝ᵥ z
      rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    rw [h2]
    exact h1)
  refine ⟨Qᵀ *ᵥ l, P'ᵀ *ᵥ w, mulVec_int _ _ (fun i j => hQ j i) hl,
    mulVec_int _ _ (fun i j => hP' j i) hw, ?_⟩
  have h3 : z = Qᵀ *ᵥ (Q'ᵀ *ᵥ z) := by
    rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, hQQ', Matrix.transpose_one, Matrix.one_mulVec]
  have h4 : xᵀ *ᵥ (P'ᵀ *ᵥ w) = Qᵀ *ᵥ (Dᵀ *ᵥ w) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.transpose_mul, ← Matrix.transpose_mul, hx,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPP', Matrix.one_mul]
  rw [h4, ← Matrix.mulVec_add, ← hz]
  exact h3

end GlobalTheory.LatticeDuality
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualIntegralPreimageLeSumTransposeImageStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_integral_preimage_le_sum_transpose_image : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (m n : ℕ) (x : Matrix (Fin m) (Fin n) L)
    (z : Fin n → L),
    (∀ u : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) → (∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L) → (∑ i, u i * z i) ∈ Formalism.UG.intL L) →
    ∃ l : Fin n → L, ∃ w : Fin m → L, (∀ i, l i ∈ Formalism.UG.intL L) ∧ (∀ i, w i ∈ Formalism.UG.intL L) ∧ z = l + xᵀ *ᵥ w := by
  first | exact @GlobalTheory.LatticeDuality.dual_subset | exact GlobalTheory.LatticeDuality.dual_subset | (intros; apply GlobalTheory.LatticeDuality.dual_subset <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HermitianDualSubsetOfIntegralGram
open Matrix

namespace GlobalTheory.Hk3.HoweG

theorem dualA_hform_eq {L : Type} [Field L] (σ : L →+* L) {n : ℕ} (J : Matrix (Fin n) (Fin n) L) (u v : Fin n → L) :
    Formalism.UG.hform σ J u v = (fun i => σ (u i)) ⬝ᵥ (J *ᵥ v) := by
  simp [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem dualA_conj_mulVec {L : Type} [Field L] (σ : L →+* L) {a b : ℕ} (y : Matrix (Fin a) (Fin b) L) (w : Fin b → L) :
    (fun i => σ ((y *ᵥ w) i)) = (y.map σ) *ᵥ (fun i => σ (w i)) := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp [dotProduct, Matrix.mulVec, map_sum]

theorem dualA_mulVec_int {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {a b : ℕ}
    {A : Matrix (Fin a) (Fin b) L} (hA : ∀ i j, A i j ∈ Formalism.UG.intL L) {w : Fin b → L}
    (hw : ∀ i, w i ∈ Formalism.UG.intL L) (i : Fin a) : (A *ᵥ w) i ∈ Formalism.UG.intL L := by
  simp only [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hA i k) (hw k)

theorem hermDual_subset_of_gram_int : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L),
    (∀ z, σ (σ z) = z) → (∀ z, Valued.v (σ z) = Valued.v z) →
    JS ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) → JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JS : Matrix (Fin n) (Fin n) L) i j) = (JS : Matrix (Fin n) (Fin n) L) j i) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ x : Matrix (Fin n') (Fin n) L, (∀ i j, (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ)) i j ∈ Formalism.UG.intL L) →
    ∀ v : Fin n → L,
      (∀ u : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) → (∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L) →
        Formalism.UG.hform σ (JS : Matrix (Fin n) (Fin n) L) u v ∈ Formalism.UG.intL L) →
      (∀ w : Fin n' → L, (∀ i, w i ∈ Formalism.UG.intL L) →
        Formalism.UG.hform σ (JS : Matrix (Fin n) (Fin n) L) (GlobalTheory.Hk3.HoweG.adj σ JS JT x *ᵥ w) v ∈ Formalism.UG.intL L) →
      ∃ u : Fin n → L, ∃ w : Fin n' → L, (∀ i, u i ∈ Formalism.UG.intL L) ∧ (∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L) ∧
        (∀ i, w i ∈ Formalism.UG.intL L) ∧ v = u + GlobalTheory.Hk3.HoweG.adj σ JS JT x *ᵥ w := by
  intro L _ _ σ n n' JS JT hσ hv hJS hJT hS0 hT0 x hx v h1 h2
  have hS : Formalism.UG.cT σ (JS : Matrix (Fin n) (Fin n) L) = JS := HoweSwap.cT_herm hS0
  have hT : Formalism.UG.cT σ (JT : Matrix (Fin n') (Fin n') L) = JT := HoweSwap.cT_herm hT0
  have hSi := HoweSwap.cT_inv_herm JS hS
  obtain ⟨hS1, hS2⟩ := HoweSwap.glint_int hJS
  obtain ⟨hT1, hT2⟩ := HoweSwap.glint_int hJT
  have hint : ∀ z, z ∈ Formalism.UG.intL L → σ z ∈ Formalism.UG.intL L := by
    intro z hz
    simp only [Formalism.UG.intL, Valuation.mem_integer_iff] at hz ⊢
    rwa [hv]
  obtain ⟨l, w, hl, hw, hz⟩ := GlobalTheory.T.dual_integral_preimage_le_sum_transpose_image L n' n (x.map σ) ((JS : Matrix (Fin n) (Fin n) L) *ᵥ v) (by
    intro u hu hxu
    have e : x *ᵥ (fun i => σ (u i)) = fun i => σ ((x.map σ *ᵥ u) i) := by
      rw [dualA_conj_mulVec]
      congr 1
      ext i j; simp [hσ]
    have := h1 (fun i => σ (u i)) (fun i => hint _ (hu i)) (fun i => by rw [e]; exact hint _ (hxu i))
    rw [dualA_hform_eq] at this
    simpa [dotProduct, hσ] using this)
  have hc : ∀ {a b : Type} (Z : Matrix a b L), (Z.map σ)ᵀ = Formalism.UG.cT σ Z := fun _ => rfl
  have hy : Formalism.UG.cT σ (adj σ JS JT x) * (JS : Matrix (Fin n) (Fin n) L) = (JT : Matrix (Fin n') (Fin n') L) * x := by
    simp only [adj, Formalism.UG.cT_mul, HoweSwap.cT_cT hσ, hT, hSi, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  have hTxv : ∀ k, (((JT : Matrix (Fin n') (Fin n') L) * x) *ᵥ v) k ∈ Formalism.UG.intL L := by
    intro k
    have := h2 (Pi.single k 1) (fun i => by
      by_cases h : i = k
      · subst h; simp
      · simp [h])
    rw [dualA_hform_eq, dualA_conj_mulVec, dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hc,
      Matrix.mulVec_mulVec, hy] at this
    have e : (fun i => σ ((Pi.single k 1 : Fin n' → L) i)) = Pi.single k 1 := by
      funext i
      by_cases h : i = k
      · subst h; simp
      · simp [h]
    rw [e] at this
    simpa using this
  have hxv : ∀ k, (x *ᵥ v) k ∈ Formalism.UG.intL L := by
    intro k
    have := dualA_mulVec_int hT2 hTxv k
    rwa [Matrix.mulVec_mulVec, HoweSwap.inv_mul_cl] at this
  have hyw : adj σ JS JT x *ᵥ (((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ w) =
      (((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (x.map σ)ᵀ) *ᵥ w := by
    rw [Matrix.mulVec_mulVec, adj, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, hc]
  have hv2 : v = ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ l +
      (((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (x.map σ)ᵀ) *ᵥ w := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_add, ← hz, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  refine ⟨((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ l,
    ((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ w, dualA_mulVec_int hS2 hl, fun i => ?_,
    dualA_mulVec_int hT2 hw, by rw [hyw]; exact hv2⟩
  have e : x *ᵥ (((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ l) = x *ᵥ v -
      (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (x.map σ)ᵀ) *ᵥ w := by
    conv_rhs => rw [hv2]
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec w, ← Matrix.mul_assoc, add_sub_cancel_right]
  rw [e, Pi.sub_apply]
  exact Subring.sub_mem _ (hxv i) (dualA_mulVec_int hx hw i)

end GlobalTheory.Hk3.HoweG
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HermitianDualSubsetOfIntegralGramStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianDual_subset_of_integral_gram : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L),
    (∀ z, σ (σ z) = z) → (∀ z, Valued.v (σ z) = Valued.v z) →
    JS ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) → JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JS : Matrix (Fin n) (Fin n) L) i j) = (JS : Matrix (Fin n) (Fin n) L) j i) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ x : Matrix (Fin n') (Fin n) L, (∀ i j, (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ)) i j ∈ Formalism.UG.intL L) →
    ∀ v : Fin n → L,
      (∀ u : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) → (∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L) →
        Formalism.UG.hform σ (JS : Matrix (Fin n) (Fin n) L) u v ∈ Formalism.UG.intL L) →
      (∀ w : Fin n' → L, (∀ i, w i ∈ Formalism.UG.intL L) →
        Formalism.UG.hform σ (JS : Matrix (Fin n) (Fin n) L) (GlobalTheory.Hk3.HoweG.adj σ JS JT x *ᵥ w) v ∈ Formalism.UG.intL L) →
      ∃ u : Fin n → L, ∃ w : Fin n' → L, (∀ i, u i ∈ Formalism.UG.intL L) ∧ (∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L) ∧
        (∀ i, w i ∈ Formalism.UG.intL L) ∧ v = u + GlobalTheory.Hk3.HoweG.adj σ JS JT x *ᵥ w := by
  first | exact @GlobalTheory.Hk3.HoweG.hermDual_subset_of_gram_int | exact GlobalTheory.Hk3.HoweG.hermDual_subset_of_gram_int | (intros; apply GlobalTheory.Hk3.HoweG.hermDual_subset_of_gram_int <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralPreimageAddImageEqLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSquareMatrixSpanColumnsIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSquareMatrixSpanColumnsIntegral
open Matrix

namespace GlobalTheory.Hk3.HoweG

theorem exists_span_fin_of_fg {L : Type} [Field L] (O : ValuationSubring L) (n : ℕ) (N : Submodule O (Fin n → L))
    (hN : N.FG) : ∃ c : Fin n → Fin n → L, N = Submodule.span O (Set.range c) := by
  classical
  have : Module.Finite O N := Module.Finite.iff_fg.mpr hN
  have : Module.Flat O N :=
    Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.2 (Submodule.isTorsionFree_iff_torsion_eq_bot.1 inferInstance)
  have : Module.Free O N := Module.free_of_flat_of_isLocalRing
  let k := Module.finrank O N
  let B : Module.Basis (Fin k) O N := Module.finBasis O N
  have hli : LinearIndependent O (fun i => (B i : Fin n → L)) :=
    B.linearIndependent.map' N.subtype (Submodule.ker_subtype N)
  have hliL : LinearIndependent L (fun i => (B i : Fin n → L)) :=
    (LinearIndependent.iff_fractionRing O L).1 hli
  have hk : k ≤ n := by simpa using hliL.fintype_card_le_finrank
  refine ⟨fun j => if h : (j : ℕ) < k then (B ⟨j, h⟩ : Fin n → L) else 0, le_antisymm ?_ ?_⟩
  · have hsp : N = Submodule.span O (Set.range fun i => (B i : Fin n → L)) := by
      have h1 := congrArg (Submodule.map N.subtype) B.span_eq
      rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at h1
      exact h1.symm
    refine hsp.le.trans (Submodule.span_mono ?_)
    rintro _ ⟨i, rfl⟩
    exact ⟨⟨i, lt_of_lt_of_le i.2 hk⟩, by simp⟩
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    by_cases h : (j : ℕ) < k
    · simp [h]
    · simp [h]

theorem mem_span_cols_iff {L : Type} [Field L] (O : ValuationSubring L) {n : ℕ} {ι : Type} [Fintype ι]
    (M : Matrix (Fin n) ι L) (v : Fin n → L) :
    v ∈ Submodule.span O (Set.range fun j i => M i j) ↔ ∃ u : ι → L, (∀ i, u i ∈ O) ∧ v = M *ᵥ u := by
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨fun j => c j, fun j => (c j).2, ?_⟩
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  · rintro ⟨u, hu, rfl⟩
    refine ⟨fun j => ⟨u j, hu j⟩, ?_⟩
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem exists_square_span_cols : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (M : Matrix (Fin n) ι L), ∃ b : Matrix (Fin n) (Fin n) L, ∀ v : Fin n → L,
      (∃ u : ι → L, (∀ i, u i ∈ Formalism.UG.intL L) ∧ v = M *ᵥ u) ↔ ∃ t : Fin n → L, (∀ i, t i ∈ Formalism.UG.intL L) ∧ v = b *ᵥ t := by
  intro L _ _ n ι _ _ M
  let O : ValuationSubring L := (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring
  obtain ⟨c, hc⟩ := exists_span_fin_of_fg O n (Submodule.span O (Set.range fun j i => M i j))
    (Submodule.fg_span (Set.finite_range _))
  refine ⟨Matrix.of fun i j => c j i, fun v => ?_⟩
  have h1 := mem_span_cols_iff O M v
  have h2 := mem_span_cols_iff O (Matrix.of fun i j => c j i) v
  rw [hc] at h1
  exact h1.symm.trans h2

end GlobalTheory.Hk3.HoweG
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSquareMatrixSpanColumnsIntegralStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_square_matrix_span_columns_integral : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (M : Matrix (Fin n) ι L), ∃ b : Matrix (Fin n) (Fin n) L, ∀ v : Fin n → L,
      (∃ u : ι → L, (∀ i, u i ∈ Formalism.UG.intL L) ∧ v = M *ᵥ u) ↔ ∃ t : Fin n → L, (∀ i, t i ∈ Formalism.UG.intL L) ∧ v = b *ᵥ t := by
  first | exact @GlobalTheory.Hk3.HoweG.exists_square_span_cols | exact GlobalTheory.Hk3.HoweG.exists_square_span_cols | (intros; apply GlobalTheory.Hk3.HoweG.exists_square_span_cols <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralPreimageAddImageEqLattice
namespace GlobalTheory.Hk3.HoweG

open Matrix

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem latA_single_mem {ι : Type} [DecidableEq ι] (j i : ι) : (Pi.single j (1 : L) : ι → L) i ∈ Formalism.UG.intL L := by
  rw [Pi.single_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem latA_dot_mem {ι : Type} [Fintype ι] {u w : ι → L} (hu : ∀ i, u i ∈ Formalism.UG.intL L)
    (hw : ∀ i, w i ∈ Formalism.UG.intL L) : u ⬝ᵥ w ∈ Formalism.UG.intL L :=
  sum_mem fun i _ => mul_mem (hu i) (hw i)

theorem latA_sum {n m : ℕ} (c : Matrix (Fin n) (Fin n) L) (hc : c.det ≠ 0) (y : Matrix (Fin n) (Fin m) L) :
    ∃ a : GL (Fin n) L, ∀ v : Fin n → L,
      (∃ u : Fin n → L, ∃ w : Fin m → L, (∀ i, u i ∈ Formalism.UG.intL L) ∧ (∀ i, w i ∈ Formalism.UG.intL L) ∧
        v = c *ᵥ u + y *ᵥ w) ↔
      ∃ t : Fin n → L, (∀ i, t i ∈ Formalism.UG.intL L) ∧ v = (a : Matrix (Fin n) (Fin n) L) *ᵥ t := by
  classical
  obtain ⟨b, hb⟩ := GlobalTheory.T.exists_square_matrix_span_columns_integral L n (Fin n ⊕ Fin m) (Matrix.fromCols c y)
  have key : ∀ v : Fin n → L,
      (∃ u : Fin n → L, ∃ w : Fin m → L, (∀ i, u i ∈ Formalism.UG.intL L) ∧ (∀ i, w i ∈ Formalism.UG.intL L) ∧
        v = c *ᵥ u + y *ᵥ w) ↔
      ∃ t : Fin n → L, (∀ i, t i ∈ Formalism.UG.intL L) ∧ v = b *ᵥ t := by
    intro v
    rw [← hb v]
    constructor
    · rintro ⟨u, w, hu, hw, rfl⟩
      refine ⟨Sum.elim u w, ?_, ?_⟩
      · rintro (i | i)
        · exact hu i
        · exact hw i
      · rw [Matrix.fromCols_mulVec_sumElim]
    · rintro ⟨u, hu, rfl⟩
      refine ⟨u ∘ Sum.inl, u ∘ Sum.inr, fun i => hu _, fun i => hu _, ?_⟩
      rw [← Matrix.fromCols_mulVec_sumElim, Sum.elim_comp_inl_inr]
  have hcol : ∀ j : Fin n, ∃ t : Fin n → L, c *ᵥ Pi.single j 1 = b *ᵥ t := by
    intro j
    obtain ⟨t, -, ht⟩ := (key (c *ᵥ Pi.single j 1)).1
      ⟨Pi.single j 1, 0, latA_single_mem j, fun _ => zero_mem _, by simp⟩
    exact ⟨t, ht⟩
  choose t ht using hcol
  have hT : b * (Matrix.of t)ᵀ = c := by
    ext i j
    have := congrFun (ht j) i
    simp only [Matrix.mulVec_single_one, Matrix.col_apply] at this
    rw [this]
    rfl
  have hdet : b.det ≠ 0 := by
    intro h
    apply hc
    rw [← hT, Matrix.det_mul, h, zero_mul]
  exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero b hdet, key⟩

theorem latA_basis (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (n n' : ℕ)
    (x : Matrix (Fin n') (Fin n) L) (y : Matrix (Fin n) (Fin n') L) :
    ∃ a : GL (Fin n) L, ∀ v : Fin n → L,
      (∃ u : Fin n → L, ∃ w : Fin n' → L, (∀ i, u i ∈ Formalism.UG.intL L) ∧ (∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L) ∧
        (∀ i, w i ∈ Formalism.UG.intL L) ∧ v = u + y *ᵥ w) ↔
      ∃ t : Fin n → L, (∀ i, t i ∈ Formalism.UG.intL L) ∧ v = (a : Matrix (Fin n) (Fin n) L) *ᵥ t := by
  classical
  obtain ⟨b, hb⟩ := latA_sum (1 : Matrix (Fin n) (Fin n) L) (by simp) xᵀ
  have hN : ∀ u : Fin n → L, ((∀ i, u i ∈ Formalism.UG.intL L) ∧ (∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L)) ↔
      ∀ j, ((b : Matrix (Fin n) (Fin n) L)ᵀ *ᵥ u) j ∈ Formalism.UG.intL L := by
    intro u
    have dual : ∀ {k : ℕ} (M : Matrix (Fin n) (Fin k) L) (t : Fin k → L), (M *ᵥ t) ⬝ᵥ u = t ⬝ᵥ (Mᵀ *ᵥ u) := by
      intro k M t
      rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    constructor
    · rintro ⟨h1, h2⟩ j
      obtain ⟨l, w, hl, hw, e⟩ := (hb ((b : Matrix (Fin n) (Fin n) L) *ᵥ Pi.single j 1)).2
        ⟨_, latA_single_mem j, rfl⟩
      have e2 := dual (b : Matrix (Fin n) (Fin n) L) (Pi.single j 1)
      rw [single_one_dotProduct, e, add_dotProduct, dual xᵀ, Matrix.one_mulVec, Matrix.transpose_transpose] at e2
      rw [← e2]
      exact add_mem (latA_dot_mem hl h1) (latA_dot_mem hw h2)
    · intro h
      refine ⟨fun i => ?_, fun k => ?_⟩
      · obtain ⟨t, ht, e⟩ := (hb (Pi.single i 1)).1
          ⟨Pi.single i 1, 0, latA_single_mem i, fun _ => zero_mem _, by
            rw [Matrix.one_mulVec, Matrix.mulVec_zero, add_zero]⟩
        have e2 := dual (b : Matrix (Fin n) (Fin n) L) t
        rw [← e, single_one_dotProduct] at e2
        rw [e2]
        exact latA_dot_mem ht h
      · obtain ⟨t, ht, e⟩ := (hb (xᵀ *ᵥ Pi.single k 1)).1
          ⟨0, Pi.single k 1, fun _ => zero_mem _, latA_single_mem k, by simp⟩
        have e2 := dual (b : Matrix (Fin n) (Fin n) L) t
        rw [← e, dual xᵀ, Matrix.transpose_transpose, single_one_dotProduct] at e2
        rw [e2]
        exact latA_dot_mem ht h
  have hmul : (b : Matrix (Fin n) (Fin n) L)ᵀ * ((b⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]
  have hmul' : ((b⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)ᵀ * (b : Matrix (Fin n) (Fin n) L)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
  have hdet : (((b⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)ᵀ).det ≠ 0 := by
    intro h
    have := congrArg Matrix.det hmul
    rw [Matrix.det_mul, h, mul_zero, Matrix.det_one] at this
    exact zero_ne_one this
  obtain ⟨a, ha⟩ := latA_sum _ hdet y
  refine ⟨a, fun v => ?_⟩
  rw [← ha v]
  constructor
  · rintro ⟨u, w, h1, h2, hw, rfl⟩
    refine ⟨(b : Matrix (Fin n) (Fin n) L)ᵀ *ᵥ u, w, (hN u).1 ⟨h1, h2⟩, hw, ?_⟩
    rw [Matrix.mulVec_mulVec, hmul', Matrix.one_mulVec]
  · rintro ⟨u, w, hu, hw, rfl⟩
    have := (hN (((b⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)ᵀ *ᵥ u)).2 (by
      rw [Matrix.mulVec_mulVec, hmul, Matrix.one_mulVec]; exact hu)
    exact ⟨_, w, this.1, this.2, hw, rfl⟩

end GlobalTheory.Hk3.HoweG
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralPreimageAddImageEqLatticeStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_preimage_add_image_eq_lattice : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (n n' : ℕ) (x : Matrix (Fin n') (Fin n) L) (y : Matrix (Fin n) (Fin n') L),
    ∃ a : GL (Fin n) L, ∀ v : Fin n → L,
      (∃ u : Fin n → L, ∃ w : Fin n' → L, (∀ i, u i ∈ Formalism.UG.intL L) ∧ (∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L) ∧ (∀ i, w i ∈ Formalism.UG.intL L) ∧ v = u + y *ᵥ w) ↔
        ∃ t : Fin n → L, (∀ i, t i ∈ Formalism.UG.intL L) ∧ v = (a : Matrix (Fin n) (Fin n) L) *ᵥ t := by
  first | exact @GlobalTheory.Hk3.HoweG.latA_basis | exact GlobalTheory.Hk3.HoweG.latA_basis | (intros; apply GlobalTheory.Hk3.HoweG.latA_basis <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HermitianFormIntegralPreimageLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HermitianFormIntegralPreimageLattice
open Matrix

namespace GlobalTheory.Hk3.HoweG.GramA

variable {L : Type} [Field L]

theorem hform_eq_dot (σ : L →+* L) {n : ℕ} (J : Matrix (Fin n) (Fin n) L) (a b : Fin n → L) :
    Formalism.UG.hform σ J a b = (fun i => σ (a i)) ⬝ᵥ (J *ᵥ b) := by
  simp [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem map_mulVec_eq (σ : L →+* L) {n m : ℕ} (A : Matrix (Fin n) (Fin m) L) (w : Fin m → L) :
    (fun i => σ ((A *ᵥ w) i)) = (fun i => σ (w i)) ᵥ* Formalism.UG.cT σ A := by
  ext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Formalism.UG.cT, dotProduct, Matrix.mulVec, Matrix.vecMul, map_sum, mul_comm]

theorem dot_mem (O : Subring L) {n : ℕ} {a b : Fin n → L} (ha : ∀ i, a i ∈ O) (hb : ∀ i, b i ∈ O) : a ⬝ᵥ b ∈ O :=
  Subring.sum_mem _ fun k _ => Subring.mul_mem _ (ha k) (hb k)

theorem mulVec_mem (O : Subring L) {n m : ℕ} {A : Matrix (Fin n) (Fin m) L} {b : Fin m → L}
    (hA : ∀ i j, A i j ∈ O) (hb : ∀ i, b i ∈ O) : ∀ i, (A *ᵥ b) i ∈ O :=
  fun i => dot_mem O (hA i) hb

theorem hform_integral : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L),
    (∀ z, σ (σ z) = z) → (∀ z, Valued.v (σ z) = Valued.v z) →
    JS ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) → JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JS : Matrix (Fin n) (Fin n) L) i j) = (JS : Matrix (Fin n) (Fin n) L) j i) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ x : Matrix (Fin n') (Fin n) L, (∀ i j, (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ)) i j ∈ Formalism.UG.intL L) →
    ∀ (u u' : Fin n → L) (w w' : Fin n' → L), (∀ i, u i ∈ Formalism.UG.intL L) → (∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L) →
      (∀ i, w i ∈ Formalism.UG.intL L) → (∀ i, u' i ∈ Formalism.UG.intL L) → (∀ i, (x *ᵥ u') i ∈ Formalism.UG.intL L) →
      (∀ i, w' i ∈ Formalism.UG.intL L) →
      Formalism.UG.hform σ (JS : Matrix (Fin n) (Fin n) L) (u + GlobalTheory.Hk3.HoweG.adj σ JS JT x *ᵥ w)
        (u' + GlobalTheory.Hk3.HoweG.adj σ JS JT x *ᵥ w') ∈ Formalism.UG.intL L := by
  intro L _ _ σ n n' JS JT hσ hv hJS hJT hS hT x hx u u' w w' hu hxu hw hu' hxu' hw'
  have hS' := HoweSwap.cT_herm hS
  have hT' := HoweSwap.cT_herm hT
  have hSi := HoweSwap.cT_inv_herm JS hS'
  have iS : ∀ i j, (JS : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L := (HoweSwap.glint_int hJS).1
  have iT : ∀ i j, (JT : Matrix (Fin n') (Fin n') L) i j ∈ Formalism.UG.intL L := (HoweSwap.glint_int hJT).1
  have hσO : ∀ z, z ∈ Formalism.UG.intL L → σ z ∈ Formalism.UG.intL L := by
    intro z hz
    simp only [Formalism.UG.intL, Valuation.mem_integer_iff] at hz ⊢
    rw [hv]; exact hz
  have e1 : (JS : Matrix (Fin n) (Fin n) L) * adj σ JS JT x = Formalism.UG.cT σ x * (JT : Matrix (Fin n') (Fin n') L) := by
    unfold adj
    rw [Matrix.mul_assoc, HoweSwap.mul_inv_cl]
  have e2 : Formalism.UG.cT σ (adj σ JS JT x) * (JS : Matrix (Fin n) (Fin n) L) = (JT : Matrix (Fin n') (Fin n') L) * x := by
    unfold adj
    rw [Formalism.UG.cT_mul, Formalism.UG.cT_mul, hT', hSi, HoweSwap.cT_cT hσ, Matrix.mul_assoc, Matrix.mul_assoc, Units.inv_mul,
      Matrix.mul_one]
  have e3 : x * adj σ JS JT x = (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ)) *
      (JT : Matrix (Fin n') (Fin n') L) := by
    unfold adj Formalism.UG.cT
    simp only [Matrix.mul_assoc]
  have h1 : ∀ b : Fin n → L, Formalism.UG.hform σ (JS : Matrix (Fin n) (Fin n) L) (u + adj σ JS JT x *ᵥ w) b =
      (fun i => σ (u i)) ⬝ᵥ ((JS : Matrix (Fin n) (Fin n) L) *ᵥ b) +
        (fun i => σ (w i)) ⬝ᵥ ((JT : Matrix (Fin n') (Fin n') L) *ᵥ (x *ᵥ b)) := by
    intro b
    have : (fun i => σ ((u + adj σ JS JT x *ᵥ w) i)) = (fun i => σ (u i)) + fun i => σ ((adj σ JS JT x *ᵥ w) i) := by
      ext i; simp
    rw [hform_eq_dot, this, add_dotProduct, map_mulVec_eq, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, e2,
      Matrix.mulVec_mulVec]
  have h2 : (fun i => σ (u i)) ⬝ᵥ ((JS : Matrix (Fin n) (Fin n) L) *ᵥ (adj σ JS JT x *ᵥ w')) =
      (fun i => σ ((x *ᵥ u) i)) ⬝ᵥ ((JT : Matrix (Fin n') (Fin n') L) *ᵥ w') := by
    rw [map_mulVec_eq, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, e1]
  have h3 : x *ᵥ (adj σ JS JT x *ᵥ w') =
      (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ)) *ᵥ
        ((JT : Matrix (Fin n') (Fin n') L) *ᵥ w') := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, e3]
  rw [h1, Matrix.mulVec_add, dotProduct_add, h2, Matrix.mulVec_add, h3]
  refine add_mem (add_mem ?_ ?_) ?_
  · exact dot_mem _ (fun i => hσO _ (hu i)) (mulVec_mem _ iS hu')
  · exact dot_mem _ (fun i => hσO _ (hxu i)) (mulVec_mem _ iT hw')
  · refine dot_mem _ (fun i => hσO _ (hw i)) (mulVec_mem _ iT fun i => ?_)
    exact add_mem (hxu' i) (mulVec_mem _ hx (mulVec_mem _ iT hw') i)

end GlobalTheory.Hk3.HoweG.GramA
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HermitianFormIntegralPreimageLatticeStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianForm_integral_preimage_lattice : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L),
    (∀ z, σ (σ z) = z) → (∀ z, Valued.v (σ z) = Valued.v z) →
    JS ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) → JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JS : Matrix (Fin n) (Fin n) L) i j) = (JS : Matrix (Fin n) (Fin n) L) j i) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ x : Matrix (Fin n') (Fin n) L, (∀ i j, (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ)) i j ∈ Formalism.UG.intL L) →
    ∀ (u u' : Fin n → L) (w w' : Fin n' → L), (∀ i, u i ∈ Formalism.UG.intL L) → (∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L) →
      (∀ i, w i ∈ Formalism.UG.intL L) → (∀ i, u' i ∈ Formalism.UG.intL L) → (∀ i, (x *ᵥ u') i ∈ Formalism.UG.intL L) →
      (∀ i, w' i ∈ Formalism.UG.intL L) →
      Formalism.UG.hform σ (JS : Matrix (Fin n) (Fin n) L) (u + GlobalTheory.Hk3.HoweG.adj σ JS JT x *ᵥ w)
        (u' + GlobalTheory.Hk3.HoweG.adj σ JS JT x *ᵥ w') ∈ Formalism.UG.intL L := by
  first | exact @GlobalTheory.Hk3.HoweG.GramA.hform_integral | exact GlobalTheory.Hk3.HoweG.GramA.hform_integral | (intros; apply GlobalTheory.Hk3.HoweG.GramA.hform_integral <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualLatticeOfIntegralGramMatrix
open Matrix

theorem GlobalTheory.Hk3.HoweG.selfDual_lattice_of_gram_int : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ)
    (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → JS ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) → JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JS : Matrix (Fin n) (Fin n) L) i j) = (JS : Matrix (Fin n) (Fin n) L) j i) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ x : Matrix (Fin n') (Fin n) L, (∀ i j, (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ)) i j ∈ Formalism.UG.intL L) →
    ∃ a : GL (Fin n) L, GlobalTheory.Hk3.HoweG.SelfDual σ JS a ∧
      (∀ y : Matrix (Fin n') (Fin n) L, GlobalTheory.Hk3.HoweG.HomA σ JS JT x y ↔
        ∀ i j, (y * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) ∧
      (∀ v : Fin n → L, (∀ i, v i ∈ Formalism.UG.intL L) →
        ((∃ u : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) ∧ v = (a : Matrix (Fin n) (Fin n) L) *ᵥ u) ↔
          ∀ i, (x *ᵥ v) i ∈ Formalism.UG.intL L)) ∧
      (∀ w : Fin n → L, (∃ u v : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) ∧ (∀ i, v i ∈ Formalism.UG.intL L) ∧
          w = (a : Matrix (Fin n) (Fin n) L) *ᵥ u + v) ↔
        ∃ v : Fin n → L, ∃ w' : Fin n' → L, (∀ i, v i ∈ Formalism.UG.intL L) ∧ (∀ i, w' i ∈ Formalism.UG.intL L) ∧
          w = v + GlobalTheory.Hk3.HoweG.adj σ JS JT x *ᵥ w') := by
  intro L _ _ ϖ σ q n n' JS JT hU _hq hJS hJT hS hT x hx
  have hσσ : ∀ z, σ (σ z) = z := hU.1
  have hσv : ∀ z, Valued.v (σ z) = Valued.v z := hU.2.1
  have hσO : ∀ z ∈ Formalism.UG.intL L, σ z ∈ Formalism.UG.intL L := by
    intro z hz
    change Valued.v (σ z) ≤ 1
    rw [hσv]; exact hz
  have iMV : ∀ {k l : ℕ} (M : Matrix (Fin k) (Fin l) L) (t : Fin l → L), (∀ i j, M i j ∈ Formalism.UG.intL L) →
      (∀ j, t j ∈ Formalism.UG.intL L) → ∀ i, (M *ᵥ t) i ∈ Formalism.UG.intL L := by
    intro k l M t hM ht i
    simp only [Matrix.mulVec, dotProduct]
    exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hM i j) (ht j)
  have iMM : ∀ {k l r : ℕ} (M : Matrix (Fin k) (Fin l) L) (M' : Matrix (Fin l) (Fin r) L), (∀ i j, M i j ∈ Formalism.UG.intL L) →
      (∀ i j, M' i j ∈ Formalism.UG.intL L) → ∀ i j, (M * M') i j ∈ Formalism.UG.intL L := by
    intro k l r M M' hM hM' i j
    simp only [Matrix.mul_apply]
    exact Subring.sum_mem _ fun m _ => Subring.mul_mem _ (hM i m) (hM' m j)
  have eJT : ∀ i j, (JT : Matrix (Fin n') (Fin n') L) i j ∈ Formalism.UG.intL L := by
    obtain ⟨g0, hg0⟩ := hJT
    intro i j; rw [← hg0]; exact ((g0 : Matrix (Fin n') (Fin n') (Formalism.UG.intL L)) i j).2
  set y := GlobalTheory.Hk3.HoweG.adj σ JS JT x with hy
  have hxy : ∀ i j, (x * y) i j ∈ Formalism.UG.intL L := by
    have : x * y = (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ)) *
        (JT : Matrix (Fin n') (Fin n') L) := by
      simp only [hy, GlobalTheory.Hk3.HoweG.adj, Formalism.UG.cT, Matrix.mul_assoc]
    rw [this]; exact iMM _ _ hx eJT
  have T4 := GlobalTheory.T.integral_preimage_add_image_eq_lattice
  have T5 := GlobalTheory.T.hermitianDual_subset_of_integral_gram
  have FreeQuotientRank := GlobalTheory.T.hermitianForm_integral_preimage_lattice
  obtain ⟨a, ha⟩ := T4 L n n' x y
  have hcol : ∀ j, ∃ u : Fin n → L, ∃ w : Fin n' → L, (∀ i, u i ∈ Formalism.UG.intL L) ∧ (∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L) ∧
      (∀ i, w i ∈ Formalism.UG.intL L) ∧ (fun k => (a : Matrix (Fin n) (Fin n) L) k j) = u + y *ᵥ w := by
    intro j
    refine (ha _).mpr ⟨Pi.single j 1, fun i => ?_, ?_⟩
    · by_cases h : i = j
      · subst h; simp [Subring.one_mem]
      · simp [h, Subring.zero_mem]
    · funext k; simp [Matrix.mulVec_single_one]
  have hN : ∀ u : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) → (∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L) →
      ∃ t : Fin n → L, (∀ i, t i ∈ Formalism.UG.intL L) ∧ u = (a : Matrix (Fin n) (Fin n) L) *ᵥ t := by
    intro u hu hxu
    exact (ha u).mp ⟨u, 0, hu, hxu, fun _ => Subring.zero_mem _, by simp⟩
  have hY : ∀ w : Fin n' → L, (∀ i, w i ∈ Formalism.UG.intL L) →
      ∃ t : Fin n → L, (∀ i, t i ∈ Formalism.UG.intL L) ∧ y *ᵥ w = (a : Matrix (Fin n) (Fin n) L) *ᵥ t := by
    intro w hw
    exact (ha _).mp ⟨0, w, fun _ => Subring.zero_mem _, by simp [Subring.zero_mem], hw, by simp⟩
  have hformM : ∀ (M : Matrix (Fin n) (Fin n) L) (t : Fin n → L) (V : Matrix (Fin n) (Fin n) L) (j : Fin n),
      Formalism.UG.hform σ (JS : Matrix (Fin n) (Fin n) L) (M *ᵥ t) (fun l => V l j) =
        ∑ k, σ (t k) * (Formalism.UG.cT σ M * (JS : Matrix (Fin n) (Fin n) L) * V) k j := by
    intro M t V j
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Formalism.UG.hform, Formalism.UG.cT, Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.map_apply, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Eq.trans (Finset.sum_congr rfl fun x1 _ => Finset.sum_comm) ?_
    symm; rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hformC : ∀ (M : Matrix (Fin n) (Fin n) L) (i j : Fin n),
      (Formalism.UG.cT σ M * (JS : Matrix (Fin n) (Fin n) L) * M) i j =
        Formalism.UG.hform σ (JS : Matrix (Fin n) (Fin n) L) (fun k => M k i) (fun k => M k j) := by
    intro M i j
    simp only [Formalism.UG.hform, Formalism.UG.cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  refine ⟨a, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro i j
    obtain ⟨u, w, hu, hxu, hw, he⟩ := hcol i
    obtain ⟨u', w', hu', hxu', hw', he'⟩ := hcol j
    rw [hformC, he, he']
    exact FreeQuotientRank L σ n n' JS JT hσσ hσv hJS hJT hS hT x hx u u' w w' hu hxu hw hu' hxu' hw'
  · intro i j
    set V : Matrix (Fin n) (Fin n) L := ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
      Formalism.UG.cT σ ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hV
    have hG : Formalism.UG.cT σ (a : Matrix (Fin n) (Fin n) L) * (JS : Matrix (Fin n) (Fin n) L) * V = 1 := by
      rw [hV, Matrix.mul_assoc, ← Matrix.mul_assoc (JS : Matrix (Fin n) (Fin n) L), Units.mul_inv, Matrix.one_mul,
        ← Formalism.UG.cT_mul, Units.inv_mul, Formalism.UG.cT_one]
    have hAm : ∀ m : Fin n → L, (∃ t : Fin n → L, (∀ i, t i ∈ Formalism.UG.intL L) ∧ m = (a : Matrix (Fin n) (Fin n) L) *ᵥ t) →
        Formalism.UG.hform σ (JS : Matrix (Fin n) (Fin n) L) m (fun l => V l j) ∈ Formalism.UG.intL L := by
      rintro m ⟨t, ht, rfl⟩
      rw [hformM, hG, Finset.sum_eq_single j]
      · simp only [Matrix.one_apply_eq, mul_one]; exact hσO _ (ht j)
      · intro k _ hk; simp [Matrix.one_apply_ne hk]
      · intro h; exact absurd (Finset.mem_univ j) h
    obtain ⟨u, w, hu, hxu, hw, he⟩ := T5 L σ n n' JS JT hσσ hσv hJS hJT hS hT x hx (fun l => V l j)
      (fun u hu hxu => hAm u (hN u hu hxu)) (fun w hw => hAm _ (hY w hw))
    obtain ⟨t, ht, het⟩ := (ha _).mp ⟨u, w, hu, hxu, hw, he⟩
    have : (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * V) i j = t i := by
      have h2 : ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ (fun l => V l j) = t := by
        rw [het, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
      rw [← h2]; simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
    rw [Matrix.mul_assoc, ← hV, this]; exact ht i
  · intro y'
    constructor
    · rintro ⟨h1, h2⟩ i j
      obtain ⟨u, w, hu, hxu, hw, he⟩ := hcol j
      have : (y' * (a : Matrix (Fin n) (Fin n) L)) i j = (y' *ᵥ (fun k => (a : Matrix (Fin n) (Fin n) L) k j)) i := by
        simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
      rw [this, he, Matrix.mulVec_add]
      exact Subring.add_mem _ (h1 u hu hxu i) (h2 w hw i)
    · intro h
      refine ⟨fun u hu hxu i => ?_, fun w hw i => ?_⟩
      · obtain ⟨t, ht, rfl⟩ := hN u hu hxu
        rw [Matrix.mulVec_mulVec]; exact iMV _ _ h ht i
      · obtain ⟨t, ht, het⟩ := hY w hw
        rw [het, Matrix.mulVec_mulVec]; exact iMV _ _ h ht i
  · intro v hv
    constructor
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨u, w, hu, hxu, hw, he⟩ := (ha _).mpr ⟨t, ht, rfl⟩
      intro i
      rw [he, Matrix.mulVec_add, Matrix.mulVec_mulVec]
      exact Subring.add_mem _ (hxu i) (iMV _ _ hxy hw i)
    · intro hxv
      exact hN v hv hxv
  · intro z
    constructor
    · rintro ⟨t, v, ht, hv, rfl⟩
      obtain ⟨u, w, hu, hxu, hw, he⟩ := (ha _).mpr ⟨t, ht, rfl⟩
      refine ⟨u + v, w, fun i => Subring.add_mem _ (hu i) (hv i), hw, ?_⟩
      rw [he]; abel
    · rintro ⟨v, w, hv, hw, rfl⟩
      obtain ⟨t, ht, het⟩ := hY w hw
      exact ⟨t, v, ht, hv, by rw [het, add_comm]⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualLatticeOfIntegralGramMatrixStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDual_lattice_of_integral_gramMatrix : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ)
    (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → JS ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) → JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JS : Matrix (Fin n) (Fin n) L) i j) = (JS : Matrix (Fin n) (Fin n) L) j i) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ x : Matrix (Fin n') (Fin n) L, (∀ i j, (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ)) i j ∈ Formalism.UG.intL L) →
    ∃ a : GL (Fin n) L, GlobalTheory.Hk3.HoweG.SelfDual σ JS a ∧
      (∀ y : Matrix (Fin n') (Fin n) L, GlobalTheory.Hk3.HoweG.HomA σ JS JT x y ↔
        ∀ i j, (y * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) ∧
      (∀ v : Fin n → L, (∀ i, v i ∈ Formalism.UG.intL L) →
        ((∃ u : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) ∧ v = (a : Matrix (Fin n) (Fin n) L) *ᵥ u) ↔
          ∀ i, (x *ᵥ v) i ∈ Formalism.UG.intL L)) ∧
      (∀ w : Fin n → L, (∃ u v : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) ∧ (∀ i, v i ∈ Formalism.UG.intL L) ∧
          w = (a : Matrix (Fin n) (Fin n) L) *ᵥ u + v) ↔
        ∃ v : Fin n → L, ∃ w' : Fin n' → L, (∀ i, v i ∈ Formalism.UG.intL L) ∧ (∀ i, w' i ∈ Formalism.UG.intL L) ∧
          w = v + GlobalTheory.Hk3.HoweG.adj σ JS JT x *ᵥ w') := by
  first | exact @GlobalTheory.Hk3.HoweG.selfDual_lattice_of_gram_int | exact GlobalTheory.Hk3.HoweG.selfDual_lattice_of_gram_int | (intros; apply GlobalTheory.Hk3.HoweG.selfDual_lattice_of_gram_int <;> assumption)
end
