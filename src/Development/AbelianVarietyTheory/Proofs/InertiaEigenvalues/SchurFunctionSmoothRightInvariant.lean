module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecompositionLocalAway

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjLowUni
noncomputable section

namespace GlobalTheory.SchurExt

section LowerUnipotent

variable {R : Type} [CommRing R] {m r : ℕ}

def lowUni (Y : Matrix (Fin (r + 1)) (Fin (m + 1)) R) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R :=
  unblk (Matrix.fromBlocks 1 0 Y 1)

def conjLowUni (Y : Matrix (Fin (r + 1)) (Fin (m + 1)) R) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) :
    Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R :=
  lowUni Y * k * lowUni (-Y)

end LowerUnipotent

end GlobalTheory.SchurExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitBlockDetOfConjLower
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LogIdealSupportFinite
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LowerUnipotentConjBlockFormulas
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StableHopfOrderSubgroupColength
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

namespace GlobalTheory.SchurExt

open Matrix

theorem schurSquareMatrixToBlocks_mul {R : Type} [CommRing R] {m r : ℕ} (M N : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) :
    blk (M * N) = blk M * blk N := by
  simp only [blk]
  exact (Matrix.submatrix_mul_equiv M N _ _ _).symm

theorem schur_mul_conjLowUni : ∀ (R : Type) [CommRing R] (m r : ℕ) (g k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R), IsUnit (Dof g).det → IsUnit (Dof (conjLowUni (Yof g) k)).det → IsUnit (Dof (g * k)).det ∧ Dof (g * k) = Dof g * Dof (conjLowUni (Yof g) k) ∧ Yof (g * k) = Yof g + Yof (conjLowUni (Yof g) k) ∧ Scof (g * k) = Scof g * Scof (conjLowUni (Yof g) k) ∧ Xof (g * k) = Xof g + Scof g * Xof (conjLowUni (Yof g) k) * (Dof g)⁻¹ := by
  intro R _ m r g k hD hD'
  have hL : ∀ Z : Matrix (Fin (r + 1)) (Fin (m + 1)) R, blk (lowUni Z) = fromBlocks 1 0 Z 1 :=
    fun Z => blk_unblk _
  have hLL : ∀ Z : Matrix (Fin (r + 1)) (Fin (m + 1)) R,
      fromBlocks (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) R) 0 (-Z) (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) R) * fromBlocks 1 0 Z 1 = 1 := by
    intro Z
    rw [fromBlocks_multiply]
    simp [fromBlocks_one]
  set Y := Yof g with hY
  set k' := conjLowUni Y k with hk'
  have hK : blk k' = fromBlocks 1 0 Y 1 * blk k * fromBlocks 1 0 (-Y) 1 := by
    rw [hk', conjLowUni, schurSquareMatrixToBlocks_mul, schurSquareMatrixToBlocks_mul, hL, hL]
  have hkk : blk k = fromBlocks 1 0 (-Y) 1 * blk k' * fromBlocks 1 0 Y 1 := by
    rw [hK]
    calc blk k = 1 * blk k * 1 := by rw [Matrix.one_mul, Matrix.mul_one]
      _ = (fromBlocks 1 0 (-Y) 1 * fromBlocks 1 0 Y 1) * blk k * (fromBlocks 1 0 (-Y) 1 * fromBlocks 1 0 Y 1) := by
          rw [hLL]
      _ = _ := by simp only [Matrix.mul_assoc]
  have hG : blk g = fromBlocks (Aof g) (Bof g) (Cof g) (Dof g) := (fromBlocks_toBlocks _).symm
  have hK' : blk k' = fromBlocks (Aof k') (Bof k') (Cof k') (Dof k') := (fromBlocks_toBlocks _).symm
  set A := Aof g
  set B := Bof g
  set C := Cof g
  set D := Dof g
  set A' := Aof k'
  set B' := Bof k'
  set C' := Cof k'
  set D' := Dof k'
  set Sc := Scof g with hSc
  have i1 : D⁻¹ * D = 1 := nonsing_inv_mul D hD
  have i2 : D * D⁻¹ = 1 := mul_nonsing_inv D hD
  have i3 : D'⁻¹ * D' = 1 := nonsing_inv_mul D' hD'
  have i4 : D' * D'⁻¹ = 1 := mul_nonsing_inv D' hD'
  have j1 : ∀ {n : Type} [Fintype n] (N : Matrix (Fin (r + 1)) n R), D⁻¹ * (D * N) = N := by
    intro n _ N; rw [← Matrix.mul_assoc, i1, Matrix.one_mul]
  have j2 : ∀ {n : Type} [Fintype n] (N : Matrix (Fin (r + 1)) n R), D * (D⁻¹ * N) = N := by
    intro n _ N; rw [← Matrix.mul_assoc, i2, Matrix.one_mul]
  have j3 : ∀ {n : Type} [Fintype n] (N : Matrix (Fin (r + 1)) n R), D'⁻¹ * (D' * N) = N := by
    intro n _ N; rw [← Matrix.mul_assoc, i3, Matrix.one_mul]
  have j4 : ∀ {n : Type} [Fintype n] (N : Matrix (Fin (r + 1)) n R), D' * (D'⁻¹ * N) = N := by
    intro n _ N; rw [← Matrix.mul_assoc, i4, Matrix.one_mul]
  have hGL : blk g * fromBlocks 1 0 (-Y) 1 = fromBlocks Sc B 0 D := by
    rw [hG, fromBlocks_multiply]
    congr 1
    · rw [hSc, Scof, hY, Yof]; simp only [Matrix.mul_one, Matrix.mul_neg, Matrix.mul_assoc]; abel
    · simp
    · have hDY : D * Y = C := j2 C
      rw [Matrix.mul_one, Matrix.mul_neg, hDY, add_neg_cancel]
    · simp
  have hprod : blk (g * k) = fromBlocks (Sc * A' + B * C' + (Sc * B' + B * D') * Y) (Sc * B' + B * D')
      (D * C' + D * D' * Y) (D * D') := by
    rw [schurSquareMatrixToBlocks_mul, hkk, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hGL, hK', fromBlocks_multiply, fromBlocks_multiply]
    simp
  have eD : Dof (g * k) = D * D' := by simp only [Dof, hprod, toBlocks_fromBlocks₂₂]
  have eC : Cof (g * k) = D * C' + D * D' * Y := by simp only [Cof, hprod, toBlocks_fromBlocks₂₁]
  have eB : Bof (g * k) = Sc * B' + B * D' := by simp only [Bof, hprod, toBlocks_fromBlocks₁₂]
  have eA : Aof (g * k) = Sc * A' + B * C' + (Sc * B' + B * D') * Y := by simp only [Aof, hprod, toBlocks_fromBlocks₁₁]
  refine ⟨?_, eD, ?_, ?_, ?_⟩
  · rw [eD, det_mul]; exact hD.mul hD'
  · rw [Yof, Yof, eD, eC, Matrix.mul_inv_rev]
    simp only [Matrix.mul_add, Matrix.mul_assoc, j1, j3]
    abel
  · rw [Scof, Scof, eA, eB, eC, eD, Matrix.mul_inv_rev]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, j1, j3, j4]
    abel
  · rw [Xof, Xof, Xof, eB, eD, Matrix.mul_inv_rev]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, j4, i4]
    abel

end GlobalTheory.SchurExt
end

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lower_unipotent_conj_block_formulas : ∀ (R : Type) [CommRing R] (m r : ℕ) (g k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R), IsUnit (Dof g).det → IsUnit (Dof (conjLowUni (Yof g) k)).det → IsUnit (Dof (g * k)).det ∧ Dof (g * k) = Dof g * Dof (conjLowUni (Yof g) k) ∧ Yof (g * k) = Yof g + Yof (conjLowUni (Yof g) k) ∧ Scof (g * k) = Scof g * Scof (conjLowUni (Yof g) k) ∧ Xof (g * k) = Xof g + Scof g * Xof (conjLowUni (Yof g) k) * (Dof g)⁻¹ := by
  first | (exact @GlobalTheory.SchurExt.schur_mul_conjLowUni) | (exact GlobalTheory.SchurExt.schur_mul_conjLowUni) | (intros; apply GlobalTheory.SchurExt.schur_mul_conjLowUni  <;> assumption)
end

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

noncomputable section

namespace GlobalTheory.SchurExt.AdBridge

section Maps

variable {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {m r : ℕ}

theorem Aof_map (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) : Aof (M.map f) = (Aof M).map f := rfl
theorem Bof_map (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) : Bof (M.map f) = (Bof M).map f := rfl
theorem Cof_map (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) : Cof (M.map f) = (Cof M).map f := rfl
theorem Dof_map (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) : Dof (M.map f) = (Dof M).map f := rfl

theorem inv_map_of_isUnit {n : ℕ} (A : Matrix (Fin n) (Fin n) R) (h : IsUnit A.det) :
    (A⁻¹).map f = (A.map f)⁻¹ := by
  symm
  apply Matrix.inv_eq_left_inv
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul A h, Matrix.map_one f (map_zero f) (map_one f)]

theorem Yof_map (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) (h : IsUnit (Dof M).det) :
    Yof (M.map f) = (Yof M).map f := by
  rw [Yof, Yof, Matrix.map_mul, Dof_map, Cof_map, inv_map_of_isUnit f _ h]

theorem Xof_map (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) (h : IsUnit (Dof M).det) :
    Xof (M.map f) = (Xof M).map f := by
  rw [Xof, Xof, Matrix.map_mul, Dof_map, Bof_map, inv_map_of_isUnit f _ h]

theorem Scof_map (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) (h : IsUnit (Dof M).det) :
    Scof (M.map f) = (Scof M).map f := by
  rw [Scof, Scof, Matrix.map_sub _ (map_sub f), Matrix.map_mul, Matrix.map_mul, Aof_map, Dof_map, Bof_map, Cof_map,
    inv_map_of_isUnit f _ h]

theorem lowUni_map (Y : Matrix (Fin (r + 1)) (Fin (m + 1)) R) :
    (lowUni Y).map f = lowUni (Y.map f) := by
  ext i j
  simp only [lowUni, unblk, Matrix.map_apply, Matrix.submatrix_apply]
  rcases (eqv m r i) with a | a <;> rcases (eqv m r j) with b | b <;>
    simp [Matrix.one_apply, apply_ite f]

theorem conjLowUni_map (Y : Matrix (Fin (r + 1)) (Fin (m + 1)) R) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) :
    (conjLowUni Y k).map f = conjLowUni (Y.map f) (k.map f) := by
  rw [conjLowUni, conjLowUni, Matrix.map_mul, Matrix.map_mul, lowUni_map, lowUni_map, Matrix.map_neg _ (map_neg f)]

end Maps

section Ones

variable {R : Type} [CommRing R] {m r : ℕ}

theorem blk_one : blk (1 : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) = 1 := by
  simp [blk]

theorem Aof_one : Aof (1 : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) = 1 := by
  rw [Aof, blk_one, ← Matrix.fromBlocks_one, Matrix.toBlocks_fromBlocks₁₁]
theorem Bof_one : Bof (1 : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) = 0 := by
  rw [Bof, blk_one, ← Matrix.fromBlocks_one, Matrix.toBlocks_fromBlocks₁₂]
theorem Cof_one : Cof (1 : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) = 0 := by
  rw [Cof, blk_one, ← Matrix.fromBlocks_one, Matrix.toBlocks_fromBlocks₂₁]
theorem Dof_one : Dof (1 : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) = 1 := by
  rw [Dof, blk_one, ← Matrix.fromBlocks_one, Matrix.toBlocks_fromBlocks₂₂]
theorem Yof_one : Yof (1 : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) = 0 := by
  rw [Yof, Cof_one, Matrix.mul_zero]
theorem Xof_one : Xof (1 : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) = 0 := by
  rw [Xof, Bof_one, Matrix.zero_mul]
theorem Scof_one : Scof (1 : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) = 1 := by
  rw [Scof, Aof_one, Bof_one, Cof_one]; simp

theorem unblk_mul (P Q : Matrix (Fin (m + 1) ⊕ Fin (r + 1)) (Fin (m + 1) ⊕ Fin (r + 1)) R) :
    unblk P * unblk Q = unblk (P * Q) := Matrix.submatrix_mul_equiv _ _ _ _ _

theorem unblk_one : unblk (1 : Matrix (Fin (m + 1) ⊕ Fin (r + 1)) (Fin (m + 1) ⊕ Fin (r + 1)) R) = 1 := by
  simp [unblk]

theorem lowUni_mul_neg (Y : Matrix (Fin (r + 1)) (Fin (m + 1)) R) : lowUni Y * lowUni (-Y) = 1 := by
  rw [lowUni, lowUni, unblk_mul, Matrix.fromBlocks_multiply]
  simp [unblk_one]

theorem conjLowUni_one (Y : Matrix (Fin (r + 1)) (Fin (m + 1)) R) : conjLowUni Y 1 = 1 := by
  rw [conjLowUni, Matrix.mul_one, lowUni_mul_neg]

theorem det_lowUni (Y : Matrix (Fin (r + 1)) (Fin (m + 1)) R) : (lowUni (m := m) Y).det = 1 := by
  rw [lowUni, unblk, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₁₂]; simp

theorem det_conjLowUni (Y : Matrix (Fin (r + 1)) (Fin (m + 1)) R) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) :
    (conjLowUni Y k).det = k.det := by
  rw [conjLowUni, Matrix.det_mul, Matrix.det_mul, det_lowUni, det_lowUni]; ring

theorem det_eq_det_Dof_mul (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) (h : IsUnit (Dof M).det) :
    M.det = (Dof M).det * (Scof M).det := by
  letI := Matrix.invertibleOfIsUnitDet _ h
  have e : Matrix.fromBlocks (Aof M) (Bof M) (Cof M) (Dof M) = blk M := Matrix.fromBlocks_toBlocks _
  have h1 : M.det = (blk M).det := by rw [blk, Matrix.det_submatrix_equiv_self]
  rw [h1, ← e, Matrix.det_fromBlocks₂₂, Matrix.invOf_eq_nonsing_inv]; rfl

theorem isUnit_det_Scof (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) (hM : IsUnit M.det)
    (h : IsUnit (Dof M).det) : IsUnit (Scof M).det := by
  rw [det_eq_det_Dof_mul M h] at hM
  exact isUnit_of_mul_isUnit_right hM

end Ones

section Adeles

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem pInf_sFin_eq_zero (b : Af E) : pInf E (sFin E b) = 0 := map_zero (infEq E).symm

omit [_root_.NumberField.IsTotallyComplex E] in
theorem pFin_sFin_eq (b : Af E) : pFin E (sFin E b) = b := rfl

theorem isUnit_of_parts {x : Ad E} (h1 : IsUnit (pInf E x)) (h2 : IsUnit (pFin E x)) : IsUnit x := by
  refine Prod.isUnit_iff.2 ⟨?_, h2⟩
  have e : (infEq E) (pInf E x) = x.1 := (infEq E).apply_symm_apply x.1
  rw [← e]; exact h1.map _

theorem map_pInf_finGL {n : ℕ} (k : GL (Fin n) (Af E)) :
    (finGL E n k : Matrix (Fin n) (Fin n) (Ad E)).map (pInf E) = 1 :=
  congrArg (fun g : GL (Fin n) (Cinf E) => (g : Matrix (Fin n) (Fin n) (Cinf E))) (pInf_finGL k)

omit [_root_.NumberField.IsTotallyComplex E] in
theorem map_pFin_finGL {n : ℕ} (k : GL (Fin n) (Af E)) :
    (finGL E n k : Matrix (Fin n) (Fin n) (Ad E)).map (pFin E) = (k : Matrix (Fin n) (Fin n) (Af E)) :=
  congrArg (fun g : GL (Fin n) (Af E) => (g : Matrix (Fin n) (Fin n) (Af E))) (pFin_finGL k)

theorem coe_finGL_mkGL {n : ℕ} (M : Matrix (Fin n) (Fin n) (Ad E)) (hi : M.map (pInf E) = 1) (hu : IsUnit M.det) :
    (finGL E n (mkGL (M.map (pFin E))) : Matrix (Fin n) (Fin n) (Ad E)) = M := by
  have hu' : IsUnit (M.map (pFin E)).det := by
    have h := hu.map (pFin E)
    rwa [RingHom.map_det] at h
  ext i j
  refine ad_ext ?_ ?_
  · exact congrFun (congrFun ((map_pInf_finGL _).trans hi.symm) i) j
  · exact congrFun (congrFun ((map_pFin_finGL _).trans (coe_mkGL hu')) i) j

end Adeles

theorem schur_data_mul_finGL : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m r : ℕ) (x : GA E (m + r + 1 + 1)) (k : GL (Fin (m + r + 1 + 1)) (Af E)), IsUnit (Dof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det → IsUnit (Dof (conjLowUni ((Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map (pFin E)) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E)))).det → IsUnit (Scof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det ∧ IsUnit (Dof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det ∧ mkGL (Dof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) = mkGL (Dof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) * finGL E (r + 1) (mkGL (Dof (conjLowUni ((Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map (pFin E)) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E))))) ∧ mkGL (Scof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) = mkGL (Scof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) * finGL E (m + 1) (mkGL (Scof (conjLowUni ((Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map (pFin E)) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E))))) ∧ (∀ i j, pInf E (Yof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) i j) = pInf E (Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) i j)) ∧ (∀ i j, pFin E (Yof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) i j) = pFin E (Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) i j) + Yof (conjLowUni ((Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map (pFin E)) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E))) i j) ∧ Xof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) (Fin.last m) 0 = Xof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) (Fin.last m) 0 + sFin E (∑ j, ∑ l, pFin E (Scof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) (Fin.last m) j) * Xof (conjLowUni ((Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map (pFin E)) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E))) j l * pFin E ((Dof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)))⁻¹ l 0)) := by
  intro E _ _ _ m r x k hD hD'
  rw [Units.val_mul]
  have hx : IsUnit (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 x.isUnit
  have hK : IsUnit (finGL E (m + r + 1 + 1) k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (finGL E (m + r + 1 + 1) k).isUnit
  have hKi := map_pInf_finGL (E := E) k
  have hKf := map_pFin_finGL (E := E) k
  generalize (finGL E (m + r + 1 + 1) k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) = K at *
  generalize (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) = g at *
  have hf : conjLowUni ((Yof g).map (pFin E)) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E)) =
      (conjLowUni (Yof g) K).map (pFin E) := by rw [conjLowUni_map, hKf]
  have hi : (conjLowUni (Yof g) K).map (pInf E) = 1 := by rw [conjLowUni_map, hKi, conjLowUni_one]
  have hdet : IsUnit (conjLowUni (Yof g) K).det := by rwa [det_conjLowUni]
  rw [hf] at hD' ⊢
  have alg := GlobalTheory.T.lower_unipotent_conj_block_formulas (Ad E) m r g K hD
  generalize conjLowUni (Yof g) K = L at *
  have hDi : (Dof L).map (pInf E) = 1 := by rw [← Dof_map, hi, Dof_one]
  have hDL : IsUnit (Dof L).det := by
    refine isUnit_of_parts ?_ ?_
    · rw [RingHom.map_det, RingHom.mapMatrix_apply, hDi, Matrix.det_one]; exact isUnit_one
    · rw [RingHom.map_det, RingHom.mapMatrix_apply, ← Dof_map]; exact hD'
  obtain ⟨a1, a2, a3, a4, a5⟩ := alg hDL
  have hS := isUnit_det_Scof g hx hD
  have hSL := isUnit_det_Scof L hdet hDL
  have hSi : (Scof L).map (pInf E) = 1 := by rw [← Scof_map _ _ hDL, hi, Scof_one]
  have hYi : (Yof L).map (pInf E) = 0 := by rw [← Yof_map _ _ hDL, hi, Yof_one]
  have hXi : (Xof L).map (pInf E) = 0 := by rw [← Xof_map _ _ hDL, hi, Xof_one]
  have hXi' : ∀ j l, pInf E (Xof L j l) = 0 := fun j l => congrFun (congrFun hXi j) l
  refine ⟨hS, a1, Units.ext ?_, Units.ext ?_, fun i j => ?_, fun i j => ?_, ?_⟩
  · rw [coe_mkGL a1, Units.val_mul, coe_mkGL hD, Dof_map, coe_finGL_mkGL _ hDi hDL, a2]
  · have hSgK : IsUnit (Scof (g * K)).det := by rw [a4, Matrix.det_mul]; exact hS.mul hSL
    rw [coe_mkGL hSgK, Units.val_mul, coe_mkGL hS, Scof_map _ _ hDL, coe_finGL_mkGL _ hSi hSL, a4]
  · have h0 : pInf E (Yof L i j) = 0 := congrFun (congrFun hYi i) j
    rw [a3, Matrix.add_apply, map_add (f := _), h0, add_zero]
  · rw [a3, Matrix.add_apply, map_add (f := _), Yof_map _ _ hDL, Matrix.map_apply]
  · rw [a5, Matrix.add_apply, Xof_map _ _ hDL]
    congr 1
    refine ad_ext ?_ ?_
    · rw [pInf_sFin_eq_zero]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Matrix.mul_apply, map_sum, map_mul, hXi', mul_zero, Finset.sum_const_zero, zero_mul]
    · rw [pFin_sFin_eq, Finset.sum_comm]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Matrix.mul_apply, map_sum, map_mul, Finset.sum_mul, Matrix.map_apply]

end GlobalTheory.SchurExt.AdBridge
end
end

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnit_block_det_of_conj_lower : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m r : ℕ) (x : GA E (m + r + 1 + 1)) (k : GL (Fin (m + r + 1 + 1)) (Af E)), IsUnit (Dof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det → IsUnit (Dof (conjLowUni ((Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map (pFin E)) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E)))).det → IsUnit (Scof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det ∧ IsUnit (Dof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det ∧ mkGL (Dof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) = mkGL (Dof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) * finGL E (r + 1) (mkGL (Dof (conjLowUni ((Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map (pFin E)) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E))))) ∧ mkGL (Scof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) = mkGL (Scof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) * finGL E (m + 1) (mkGL (Scof (conjLowUni ((Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map (pFin E)) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E))))) ∧ (∀ i j, pInf E (Yof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) i j) = pInf E (Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) i j)) ∧ (∀ i j, pFin E (Yof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) i j) = pFin E (Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) i j) + Yof (conjLowUni ((Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map (pFin E)) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E))) i j) ∧ Xof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) (Fin.last m) 0 = Xof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) (Fin.last m) 0 + sFin E (∑ j, ∑ l, pFin E (Scof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) (Fin.last m) j) * Xof (conjLowUni ((Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map (pFin E)) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E))) j l * pFin E ((Dof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)))⁻¹ l 0)) := by
  first | (exact @GlobalTheory.SchurExt.AdBridge.schur_data_mul_finGL) | (exact GlobalTheory.SchurExt.AdBridge.schur_data_mul_finGL) | (intros; apply GlobalTheory.SchurExt.AdBridge.schur_data_mul_finGL <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FirstColumnInvFiniteMemCompactOnSupport
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FirstColumnInvFiniteMemCompactOnSupport
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

namespace GlobalTheory.NmUnfCol

theorem continuous_pFin (E : Type) [Field E] [NumberField E] : Continuous (pFin E) := by
  unfold pFin; exact continuous_snd

theorem col_inv_mul {E : Type} [Field E] [NumberField E] {a : ℕ}
    (u p : GA E (a + 1)) (hu : u ∈ GlobalTheory.JSW.NA (E := E) (a := (a + 1))) (l : Fin (a + 1)) :
    ((p⁻¹ : GA E (a + 1)) : Matrix (Fin (a + 1)) (Fin (a + 1)) (Ad E)) l 0 =
      (((u⁻¹ * p)⁻¹ : GA E (a + 1)) : Matrix (Fin (a + 1)) (Fin (a + 1)) (Ad E)) l 0 := by
  have e : ((u⁻¹ * p)⁻¹ : GA E (a + 1)) = p⁻¹ * u := by group
  rw [e, Units.val_mul, Matrix.mul_apply]
  have hcol : ∀ j : Fin (a + 1), (u : Matrix (Fin (a + 1)) (Fin (a + 1)) (Ad E)) j 0 = if j = 0 then 1 else 0 := by
    intro j
    by_cases hj : j = 0
    · subst hj; simp [hu.2 0]
    · rw [if_neg hj]; exact hu.1 j 0 (Fin.pos_iff_ne_zero.2 hj)
  simp only [hcol, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem finite_first_col_inv_compact : ∀ (E : Type) [Field E] [NumberField E] (r : ℕ) (b₁ : GA E (r + 1) → ℂ), (∃ C : Set (GA E (r + 1)), IsCompact C ∧ ∀ p, b₁ p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (r + 1)), u⁻¹ * p ∈ C) → ∃ K : Set (Fin (r + 1) → Af E), IsCompact K ∧ ∀ p, b₁ p ≠ 0 → (fun l => pFin E (((p⁻¹ : GA E (r + 1)) : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E)) l 0)) ∈ K := by
  intro E _ _ r b₁ ⟨C, hC, hsupp⟩
  let f : GA E (r + 1) → (Fin (r + 1) → Af E) :=
    fun c l => pFin E (((c⁻¹ : GA E (r + 1)) : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E)) l 0)
  have hf : Continuous f := by
    refine continuous_pi fun l => (continuous_pFin E).comp ?_
    have h0 : Continuous (fun c : GA E (r + 1) => ((c⁻¹ : GA E (r + 1)) : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E))) :=
      Units.continuous_coe_inv
    exact (continuous_apply 0).comp ((continuous_apply l).comp h0)
  refine ⟨f '' C, hC.image hf, fun p hp => ?_⟩
  obtain ⟨u, hu, huC⟩ := hsupp p hp
  refine ⟨u⁻¹ * p, huC, funext fun l => ?_⟩
  simp only [f]
  rw [col_inv_mul u p hu l]

end GlobalTheory.NmUnfCol
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FirstColumnInvFiniteMemCompactOnSupportStatement
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.firstColumn_inv_finite_mem_compact_on_support : ∀ (E : Type) [Field E] [NumberField E] (r : ℕ) (b₁ : GA E (r + 1) → ℂ), (∃ C : Set (GA E (r + 1)), IsCompact C ∧ ∀ p, b₁ p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (r + 1)), u⁻¹ * p ∈ C) → ∃ K : Set (Fin (r + 1) → Af E), IsCompact K ∧ ∀ p, b₁ p ≠ 0 → (fun l => pFin E (((p⁻¹ : GA E (r + 1)) : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E)) l 0)) ∈ K := by
  first | (exact @GlobalTheory.NmUnfCol.finite_first_col_inv_compact) | (exact GlobalTheory.NmUnfCol.finite_first_col_inv_compact) | (intros; apply GlobalTheory.NmUnfCol.finite_first_col_inv_compact  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LastRowFiniteMemCompactOnSupport
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LastRowFiniteMemCompactOnSupport
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

theorem GlobalTheory.JSW.lastRow_finite_compact : ∀ (E : Type) [Field E] [NumberField E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (β : GA E (m + 1) → ℂ), (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, β h ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * h ∈ C) → ∃ K : Set (Fin (m + 1) → Af E), IsCompact K ∧ ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, β h ≠ 0 → (fun j => pFin E ((h : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) j)) ∈ K := by
  intro E _ _ m S β ⟨C, hC, hCβ⟩
  let F : GA E (m + 1) → (Fin (m + 1) → Af E) :=
    fun c j => pFin E ((c : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) j)
  have hF : Continuous F := by
    refine continuous_pi fun j => ?_
    have h0 : Continuous fun c : GA E (m + 1) => (c : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) :=
      Units.continuous_val
    have h1 : Continuous fun c : GA E (m + 1) => (c : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) j :=
      h0.matrix_elem (Fin.last m) j
    exact continuous_snd.comp h1
  refine ⟨F '' C, hC.image hF, fun h hS hβ => ?_⟩
  obtain ⟨u, hu, huC⟩ := hCβ h hS hβ
  refine ⟨u⁻¹ * h, huC, ?_⟩
  set c : GA E (m + 1) := u⁻¹ * h with hc
  have hh : h = u * c := by rw [hc]; group
  have key : ∀ j, (h : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) j =
      (c : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) j := by
    intro j
    have hm : (h : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) =
        (u : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) * (c : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) := by
      rw [hh]; rfl
    rw [hm, Matrix.mul_apply, Finset.sum_eq_single (Fin.last m)]
    · rw [hu.2, one_mul]
    · intro l _ hl
      rw [hu.1 (Fin.last m) l (lt_of_le_of_ne (Fin.le_last l) hl), zero_mul]
    · intro h'; exact absurd (Finset.mem_univ _) h'
  funext j
  simp only [F, key j]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LastRowFiniteMemCompactOnSupportStatement
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastRow_finite_mem_compact_on_support : ∀ (E : Type) [Field E] [NumberField E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (β : GA E (m + 1) → ℂ), (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, β h ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * h ∈ C) → ∃ K : Set (Fin (m + 1) → Af E), IsCompact K ∧ ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, β h ≠ 0 → (fun j => pFin E ((h : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) j)) ∈ K := by
  first
  | exact @GlobalTheory.JSW.lastRow_finite_compact
  | exact GlobalTheory.JSW.lastRow_finite_compact
  | (intros; apply GlobalTheory.JSW.lastRow_finite_compact <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurComplementMemAdelicGLSupportedAtFinitePlace
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurComplementMemAdelicGLSupportedAtFinitePlace
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

namespace GlobalTheory.SchurExt

theorem map_blocks_of_map_eq_one {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {m r : ℕ}
    (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) (h : M.map f = 1) :
    (Aof M).map f = 1 ∧ (Bof M).map f = 0 ∧ (Cof M).map f = 0 := by
  refine ⟨Matrix.ext fun i j => ?_, Matrix.ext fun i j => ?_, Matrix.ext fun i j => ?_⟩
  · have := congrFun (congrFun h ((eqv m r).symm (Sum.inl i))) ((eqv m r).symm (Sum.inl j))
    simp only [Matrix.map_apply] at this ⊢
    simp only [Aof, blk, Matrix.toBlocks₁₁, Matrix.submatrix_apply, Matrix.of_apply, this, Matrix.one_apply,
      (eqv m r).symm.injective.eq_iff, Sum.inl.injEq]
  · have := congrFun (congrFun h ((eqv m r).symm (Sum.inl i))) ((eqv m r).symm (Sum.inr j))
    simp only [Matrix.map_apply] at this ⊢
    simp only [Bof, blk, Matrix.toBlocks₁₂, Matrix.submatrix_apply, Matrix.of_apply, this, Matrix.one_apply,
      (eqv m r).symm.injective.eq_iff, reduceCtorEq, if_false, Matrix.zero_apply]
  · have := congrFun (congrFun h ((eqv m r).symm (Sum.inr i))) ((eqv m r).symm (Sum.inl j))
    simp only [Matrix.map_apply] at this ⊢
    simp only [Cof, blk, Matrix.toBlocks₂₁, Matrix.submatrix_apply, Matrix.of_apply, this, Matrix.one_apply,
      (eqv m r).symm.injective.eq_iff, reduceCtorEq, if_false, Matrix.zero_apply]

theorem map_Scof_eq_one {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {m r : ℕ}
    (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) (h : M.map f = 1) :
    (Scof M).map f = 1 := by
  obtain ⟨hA, hB, hC⟩ := map_blocks_of_map_eq_one f M h
  have hmul : ∀ {a b c : ℕ} (P : Matrix (Fin a) (Fin b) R) (Q : Matrix (Fin b) (Fin c) R),
      (P * Q).map f = P.map f * Q.map f := fun P Q => Matrix.map_mul
  rw [Scof, Matrix.map_sub _ (map_sub f), hmul, hmul, hA, hB, hC, Matrix.zero_mul, Matrix.mul_zero, sub_zero]

end GlobalTheory.SchurExt

theorem GlobalTheory.SchurExt.mkGL_Scof_mem_supS : ∀ (E : Type) [Field E] [NumberField E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (x : GA E (m + r + 1 + 1)), x ∈ GlobalTheory.JSW.supS (E := E) (a := (m + r + 1 + 1)) S → IsUnit (Dof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det → mkGL (Scof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S := by
  intro E _ _ m r S x hx _ w hw
  have h1 := hx w hw
  set f := (pLoc E w).comp (pFin E)
  have hM : (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).map f = 1 := by
    have := Units.ext_iff.mp h1
    simpa using this
  have hS := map_Scof_eq_one f _ hM
  by_cases hu : IsUnit (Scof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det
  · refine Units.ext ?_
    change ((mkGL (Scof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) :
      GL (Fin (m + 1)) (Ad E)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)).map f = 1
    rw [coe_mkGL hu]
    exact hS
  · rw [mkGL, dite_eq_right hu, map_one]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurComplementMemAdelicGLSupportedAtFinitePlaceStatement
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schurComplement_mem_adelicGLSupportedAtFinitePlaces : ∀ (E : Type) [Field E] [NumberField E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (x : GA E (m + r + 1 + 1)), x ∈ GlobalTheory.JSW.supS (E := E) (a := (m + r + 1 + 1)) S → IsUnit (Dof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det → mkGL (Scof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S := by
  first | (exact @GlobalTheory.SchurExt.mkGL_Scof_mem_supS) | (exact GlobalTheory.SchurExt.mkGL_Scof_mem_supS) | (intros; apply GlobalTheory.SchurExt.mkGL_Scof_mem_supS  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNhdsOneConjLowerUnipotentSchurBlocksSmall
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNhdsOneConjLowerUnipotentSchurBlocksSmall
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt Filter
open scoped ContDiff Topology

namespace GlobalTheory.SchurNear

variable {E : Type} [Field E] [NumberField E] {α : Type}

theorem continuous_pLoc (w : HeightOneSpectrum (𝓞 E)) : Continuous (pLoc E w) :=
  RestrictedProduct.continuous_eval w

theorem exists_inv (x : Af E) (h0 : ∀ w, pLoc E w x ≠ 0)
    (h1 : ∀ w : HeightOneSpectrum (𝓞 E), (pLoc E w x)⁻¹ ∈ w.adicCompletionIntegers E) :
    ∃ y ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E, x * y = 1 := by
  refine ⟨⟨fun w => (pLoc E w x)⁻¹, Eventually.of_forall h1⟩, h1, ?_⟩
  refine Subtype.ext (funext fun w => ?_)
  exact mul_inv_cancel₀ (h0 w)

theorem eventually_inv (S : Finset (HeightOneSpectrum (𝓞 E))) {l : Filter α} {f : α → Af E}
    (hf : Tendsto f l (𝓝 1)) (hS : ∀ᶠ a in l, ∀ w ∉ S, pLoc E w (f a) = 1) :
    ∀ᶠ a in l, ∃ y ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E, f a * y = 1 := by
  have h : ∀ w ∈ S, ∀ᶠ a in l, pLoc E w (f a) ≠ 0 ∧ (pLoc E w (f a))⁻¹ ∈ w.adicCompletionIntegers E := by
    intro w _
    have h1 : Tendsto (fun a => pLoc E w (f a)) l (𝓝 1) := by
      have := ((continuous_pLoc w).tendsto 1).comp hf
      rwa [map_one] at this
    have h2 : Tendsto (fun a => (pLoc E w (f a))⁻¹) l (𝓝 1) := by
      have := h1.inv₀ one_ne_zero
      rwa [inv_one] at this
    refine (h1.eventually_ne one_ne_zero).and ?_
    exact h2.eventually ((Valued.isOpen_valuationSubring _).mem_nhds (one_mem (w.adicCompletionIntegers E)))
  filter_upwards [(eventually_all_finset S).2 h, hS] with a ha hb
  refine exists_inv _ (fun w => ?_) (fun w => ?_)
  · by_cases hw : w ∈ S
    · exact (ha w hw).1
    · rw [hb w hw]; exact one_ne_zero
  · by_cases hw : w ∈ S
    · exact (ha w hw).2
    · rw [hb w hw, inv_one]; exact one_mem _

theorem tendsto_inverse (S : Finset (HeightOneSpectrum (𝓞 E))) {l : Filter α} {f : α → Af E}
    (hf : Tendsto f l (𝓝 1)) (hS : ∀ᶠ a in l, ∀ w ∉ S, pLoc E w (f a) = 1) :
    Tendsto (fun a => Ring.inverse (f a)) l (𝓝 1) := by
  intro W hW
  have hO := GroundTheory.Global.isCompact_integralFiniteAdeles E
  have hN : ∀ᶠ c in 𝓝 (1 : Af E), ∀ y ∈ (GroundTheory.Global.integralFiniteAdeles (𝓞 E) E : Set (Af E)),
      1 + (1 - c) * y ∈ W := by
    refine hO.eventually_forall_of_forall_eventually fun y _ => ?_
    have hc : Continuous fun z : Af E × Af E => 1 + (1 - z.1) * z.2 := by fun_prop
    have h := hc.tendsto ((1 : Af E), y)
    simp only [sub_self, zero_mul, add_zero] at h
    exact h hW
  change ∀ᶠ a in l, Ring.inverse (f a) ∈ W
  filter_upwards [hf.eventually hN, eventually_inv S hf hS] with a ha ⟨y, hy, hxy⟩
  have hu : IsUnit (f a) := IsUnit.of_mul_eq_one y hxy
  have : Ring.inverse (f a) = 1 + (1 - f a) * y := by
    have h1 := Ring.inverse_mul_cancel _ hu
    linear_combination (1 - Ring.inverse (f a)) * hxy + y * h1
  rw [this]; exact ha y hy

theorem matrix_near (S : Finset (HeightOneSpectrum (𝓞 E))) {n : ℕ} {l : Filter α}
    {g : α → Matrix (Fin n) (Fin n) (Af E)}
    (hg : Tendsto g l (𝓝 1)) (hS : ∀ᶠ a in l, ∀ w ∉ S, (g a).map (pLoc E w) = 1) :
    (∀ᶠ a in l, IsUnit (g a).det) ∧ Tendsto (fun a => (g a)⁻¹) l (𝓝 1) ∧
      Tendsto (fun a => mkGL (g a)) l (𝓝 1) := by
  have hd : Tendsto (fun a => (g a).det) l (𝓝 1) := by
    have := ((continuous_id.matrix_det (X := Matrix (Fin n) (Fin n) (Af E))).tendsto 1).comp hg
    simpa [Function.comp_def] using this
  have hdS : ∀ᶠ a in l, ∀ w ∉ S, pLoc E w (g a).det = 1 := by
    filter_upwards [hS] with a ha w hw
    rw [RingHom.map_det, RingHom.mapMatrix_apply, ha w hw, Matrix.det_one]
  have hu : ∀ᶠ a in l, IsUnit (g a).det := by
    filter_upwards [eventually_inv S hd hdS] with a ⟨y, _, hy⟩
    exact IsUnit.of_mul_eq_one y hy
  have hadj : Tendsto (fun a => (g a).adjugate) l (𝓝 1) := by
    have := ((continuous_id.matrix_adjugate (X := Matrix (Fin n) (Fin n) (Af E))).tendsto 1).comp hg
    simpa [Function.comp_def] using this
  have hi : Tendsto (fun a => (g a)⁻¹) l (𝓝 1) := by
    have := (tendsto_inverse S hd hdS).smul hadj
    simpa only [one_smul, Matrix.inv_def] using this
  refine ⟨hu, hi, ?_⟩
  rw [Units.isInducing_embedProduct.tendsto_nhds_iff]
  have h2 := (MulOpposite.continuous_op.tendsto _).comp hi
  have h3 := hg.prodMk_nhds h2
  refine Tendsto.congr' ?_ h3
  filter_upwards [hu] with a ha
  simp only [Function.comp, Units.embedProduct_apply, Matrix.coe_units_inv, coe_mkGL ha]

section Alg
variable {R T : Type} [CommRing R] [CommRing T] {m r : ℕ}

theorem blk_one : blk (1 : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) = Matrix.fromBlocks 1 0 0 1 := by
  rw [blk, Matrix.submatrix_one_equiv, Matrix.fromBlocks_one]

theorem Aof_one : Aof (1 : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) = 1 := by
  rw [Aof, blk_one, Matrix.toBlocks_fromBlocks₁₁]
theorem Bof_one : Bof (1 : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) = 0 := by
  rw [Bof, blk_one, Matrix.toBlocks_fromBlocks₁₂]
theorem Cof_one : Cof (1 : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) = 0 := by
  rw [Cof, blk_one, Matrix.toBlocks_fromBlocks₂₁]
theorem Dof_one : Dof (1 : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) = 1 := by
  rw [Dof, blk_one, Matrix.toBlocks_fromBlocks₂₂]

theorem conj_one (Y : Matrix (Fin (r + 1)) (Fin (m + 1)) R) : conjLowUni Y 1 = 1 := by
  rw [conjLowUni, mul_one, lowUni, lowUni, unblk, unblk, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp

theorem lowUni_map (p : R →+* T) (Y : Matrix (Fin (r + 1)) (Fin (m + 1)) R) :
    (lowUni Y).map p = lowUni (Y.map p) := by
  rw [lowUni, lowUni, unblk, unblk, ← Matrix.submatrix_map, Matrix.fromBlocks_map]
  simp

theorem conj_map (p : R →+* T) (Y : Matrix (Fin (r + 1)) (Fin (m + 1)) R)
    (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) (hk : k.map p = 1) :
    (conjLowUni Y k).map p = 1 := by
  rw [← conj_one (Y.map p), conjLowUni, conjLowUni, Matrix.map_mul, Matrix.map_mul, lowUni_map, lowUni_map, hk,
    Matrix.map_neg _ (map_neg p)]

theorem Dof_map (p : R →+* T) (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) (h : M.map p = 1) :
    (Dof M).map p = 1 := by
  rw [← Dof_one (m := m), ← h]; rfl

theorem Scof_map (p : R →+* T) (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) (h : M.map p = 1) :
    (Scof M).map p = 1 := by
  have hA : (Aof M).map p = 1 := by rw [← Aof_one (r := r), ← h]; rfl
  have hB : (Bof M).map p = 0 := by rw [← Bof_one (m := m) (r := r), ← h]; rfl
  rw [Scof, Matrix.map_sub _ (map_sub p), Matrix.map_mul, Matrix.map_mul, hA, hB]
  simp

variable [TopologicalSpace R] [IsTopologicalRing R]

theorem continuous_lowUni : Continuous (lowUni : Matrix (Fin (r + 1)) (Fin (m + 1)) R → _) :=
  (Continuous.matrix_fromBlocks continuous_const continuous_const continuous_id continuous_const).matrix_submatrix _ _

theorem continuous_conj {Z : Type} [TopologicalSpace Z] {f : Z → Matrix (Fin (r + 1)) (Fin (m + 1)) R}
    {g : Z → Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun z => conjLowUni (f z) (g z)) := by
  have h1 : Continuous fun z => lowUni (f z) := continuous_lowUni.comp hf
  have h2 : Continuous fun z => lowUni (-f z) := continuous_lowUni.comp hf.neg
  exact (h1.matrix_mul hg).matrix_mul h2

theorem tendsto_mul {a b c : ℕ} {l : Filter α} {f : α → Matrix (Fin a) (Fin b) R} {g : α → Matrix (Fin b) (Fin c) R}
    {x : Matrix (Fin a) (Fin b) R} {y : Matrix (Fin b) (Fin c) R} (hf : Tendsto f l (𝓝 x)) (hg : Tendsto g l (𝓝 y)) :
    Tendsto (fun t => f t * g t) l (𝓝 (x * y)) := by
  have hc : Continuous fun z : Matrix (Fin a) (Fin b) R × Matrix (Fin b) (Fin c) R => z.1 * z.2 :=
    Continuous.matrix_mul (A := fun z : Matrix (Fin a) (Fin b) R × Matrix (Fin b) (Fin c) R => z.1)
      (B := fun z => z.2) continuous_fst continuous_snd
  have h := (hc.tendsto (x, y)).comp (hf.prodMk_nhds hg)
  simpa only [Function.comp_def] using h

end Alg

theorem blocks_near (S : Finset (HeightOneSpectrum (𝓞 E))) {m r : ℕ} {l : Filter α}
    {g : α → Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E)}
    (hg : Tendsto g l (𝓝 1)) (hS : ∀ᶠ a in l, ∀ w ∉ S, (g a).map (pLoc E w) = 1) :
    (∀ᶠ a in l, IsUnit (Dof (g a)).det) ∧ Tendsto (fun a => mkGL (Dof (g a))) l (𝓝 1) ∧
      Tendsto (fun a => mkGL (Scof (g a))) l (𝓝 1) ∧ Tendsto (fun a => Yof (g a)) l (𝓝 0) ∧
      Tendsto (fun a => Xof (g a)) l (𝓝 0) := by
  have hA : Tendsto (fun a => Aof (g a)) l (𝓝 1) := by
    rw [← Aof_one (r := r)]
    exact (Continuous.tendsto (f := Aof) (continuous_matrix fun i j => continuous_id.matrix_elem _ _) _).comp hg
  have hB : Tendsto (fun a => Bof (g a)) l (𝓝 0) := by
    rw [← Bof_one]
    exact (Continuous.tendsto (f := Bof) (continuous_matrix fun i j => continuous_id.matrix_elem _ _) _).comp hg
  have hC : Tendsto (fun a => Cof (g a)) l (𝓝 0) := by
    rw [← Cof_one]
    exact (Continuous.tendsto (f := Cof) (continuous_matrix fun i j => continuous_id.matrix_elem _ _) _).comp hg
  have hD : Tendsto (fun a => Dof (g a)) l (𝓝 1) := by
    rw [← Dof_one (m := m)]
    exact (Continuous.tendsto (f := Dof) (continuous_matrix fun i j => continuous_id.matrix_elem _ _) _).comp hg
  obtain ⟨hu, hi, hm⟩ := matrix_near S hD (hS.mono fun a ha w hw => Dof_map _ _ (ha w hw))
  have hSc : Tendsto (fun a => Scof (g a)) l (𝓝 1) := by
    have := hA.sub (tendsto_mul (tendsto_mul hB hi) hC)
    simpa only [Scof, Matrix.mul_zero, sub_zero] using this
  refine ⟨hu, hm, (matrix_near S hSc (hS.mono fun a ha w hw => Scof_map _ _ (ha w hw))).2.2, ?_, ?_⟩
  · simpa only [Yof, Matrix.mul_zero] using tendsto_mul hi hC
  · simpa only [Xof, Matrix.zero_mul] using tendsto_mul hB hi

theorem conj_near (S : Finset (HeightOneSpectrum (𝓞 E))) {m r : ℕ} {Z : Type} [TopologicalSpace Z]
    (π : Z → Matrix (Fin (r + 1)) (Fin (m + 1)) (Af E)) (hπ : Continuous π) (z₀ : Z) :
    let l : Filter (GL (Fin (m + r + 1 + 1)) (Af E) × Z) :=
      𝓝 (1, z₀) ⊓ 𝓟 {z | ∀ w ∉ S, Matrix.GeneralLinearGroup.map (pLoc E w) z.1 = 1}
    Tendsto (fun z : GL (Fin (m + r + 1 + 1)) (Af E) × Z => conjLowUni (π z.2) z.1.val) l (𝓝 1) ∧
      ∀ᶠ z in l, ∀ w ∉ S, (conjLowUni (π z.2) z.1.val).map (pLoc E w) = 1 := by
  intro l
  constructor
  · have hc : Continuous fun z : GL (Fin (m + r + 1 + 1)) (Af E) × Z => conjLowUni (π z.2) z.1.val :=
      continuous_conj (f := fun z : GL (Fin (m + r + 1 + 1)) (Af E) × Z => π z.2) (g := fun z => z.1.val)
        (hπ.comp continuous_snd) (Units.continuous_val.comp continuous_fst)
    have := hc.tendsto (1, z₀)
    simp only [Units.val_one, conj_one] at this
    exact this.mono_left inf_le_left
  · refine eventually_inf_principal.2 (Eventually.of_forall fun z hz w hw => conj_map _ _ _ ?_)
    exact congrArg Units.val (hz w hw)

theorem blocks_small : ∀ (E : Type) [Field E] [NumberField E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (Uβ : Subgroup (GL (Fin (m + 1)) (Af E))) (Ub : Subgroup (GL (Fin (r + 1)) (Af E))), IsOpen (Uβ : Set (GL (Fin (m + 1)) (Af E))) → IsOpen (Ub : Set (GL (Fin (r + 1)) (Af E))) → ∀ (Krow : Set (Fin (m + 1) → Af E)) (Kcol : Set (Fin (r + 1) → Af E)), IsCompact Krow → IsCompact Kcol → ∃ W ∈ 𝓝 (1 : GL (Fin (m + r + 1 + 1)) (Af E)), ∀ k ∈ W, (∀ w ∉ S, Matrix.GeneralLinearGroup.map (pLoc E w) k = 1) → ∀ Y : Matrix (Fin (r + 1)) (Fin (m + 1)) (Af E), (∀ i j, Y i j ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E) → IsUnit (Dof (conjLowUni Y (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E)))).det ∧ mkGL (Dof (conjLowUni Y (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E)))) ∈ Ub ∧ mkGL (Scof (conjLowUni Y (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E)))) ∈ Uβ ∧ (∀ i j, Yof (conjLowUni Y (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E))) i j ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E) ∧ ∀ ρ ∈ Krow, ∀ γ ∈ Kcol, (∑ j, ∑ l, ρ j * Xof (conjLowUni Y (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E))) j l * γ l) ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E := by
  intro E _ _ m r S Uβ Ub hβ hb Krow Kcol hrow hcol
  have hO := GroundTheory.Global.isCompact_integralFiniteAdeles E
  have hOo : (GroundTheory.Global.integralFiniteAdeles (𝓞 E) E : Set (Af E)) ∈ 𝓝 (0 : Af E) :=
    GroundTheory.Global.isOpen_integralFiniteAdeles.mem_nhds (zero_mem _)
  set KY : Set (Matrix (Fin (r + 1)) (Fin (m + 1)) (Af E)) :=
    {Y | ∀ i j, Y i j ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E} with hKY
  have hK : IsCompact KY := by
    have := isCompact_pi_infinite (X := fun _ : Fin (r + 1) => Fin (m + 1) → Af E)
      (fun _ => isCompact_pi_infinite (fun _ : Fin (m + 1) => hO))
    exact this
  have h1 : ∀ᶠ k in 𝓝 (1 : GL (Fin (m + r + 1 + 1)) (Af E)), ∀ Y ∈ KY,
      (∀ w ∉ S, Matrix.GeneralLinearGroup.map (pLoc E w) k = 1) →
      IsUnit (Dof (conjLowUni Y k.val)).det ∧ mkGL (Dof (conjLowUni Y k.val)) ∈ Ub ∧
        mkGL (Scof (conjLowUni Y k.val)) ∈ Uβ ∧
        ∀ i j, Yof (conjLowUni Y k.val) i j ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E := by
    refine hK.eventually_forall_of_forall_eventually fun Y _ => ?_
    obtain ⟨a, b⟩ := conj_near S id continuous_id Y
    obtain ⟨c1, c2, c3, c4, -⟩ := blocks_near S a b
    refine eventually_inf_principal.1 (c1.and ((c2.eventually (hb.mem_nhds Ub.one_mem)).and
      ((c3.eventually (hβ.mem_nhds Uβ.one_mem)).and ?_)))
    refine eventually_all.2 fun i => eventually_all.2 fun j => ?_
    exact (((continuous_id.matrix_elem i j).tendsto 0).comp c4).eventually hOo
  have h2 : ∀ᶠ k in 𝓝 (1 : GL (Fin (m + r + 1 + 1)) (Af E)), ∀ z ∈ KY ×ˢ (Krow ×ˢ Kcol),
      (∀ w ∉ S, Matrix.GeneralLinearGroup.map (pLoc E w) k = 1) →
      (∑ j, ∑ l, z.2.1 j * Xof (conjLowUni z.1 k.val) j l * z.2.2 l) ∈
        GroundTheory.Global.integralFiniteAdeles (𝓞 E) E := by
    refine (hK.prod (hrow.prod hcol)).eventually_forall_of_forall_eventually fun z₀ _ => ?_
    obtain ⟨a, b⟩ := conj_near S Prod.fst continuous_fst z₀
    obtain ⟨-, -, -, -, c⟩ := blocks_near S a b
    have hc : Continuous fun t : Matrix (Fin (m + 1)) (Fin (r + 1)) (Af E) × (Fin (m + 1) → Af E) × (Fin (r + 1) → Af E) =>
        ∑ j, ∑ l, t.2.1 j * t.1 j l * t.2.2 l := by fun_prop
    have h3 := (hc.tendsto (0, z₀.2)).comp (c.prodMk_nhds
      (((continuous_snd.comp continuous_snd).tendsto (1, z₀)).mono_left inf_le_left))
    simp only [Matrix.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero] at h3
    exact eventually_inf_principal.1 (h3.eventually hOo)
  refine ⟨_, h1.and h2, fun k hk hS Y hY => ?_⟩
  obtain ⟨a, b, c, d⟩ := hk.1 Y hY hS
  exact ⟨a, b, c, d, fun ρ hρ γ hγ => hk.2 (Y, ρ, γ) ⟨hY, hρ, hγ⟩ hS⟩

end GlobalTheory.SchurNear
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNhdsOneConjLowerUnipotentSchurBlocksSmallStatement
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nhds_one_conjLowerUnipotent_schurBlocks_small : ∀ (E : Type) [Field E] [NumberField E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (Uβ : Subgroup (GL (Fin (m + 1)) (Af E))) (Ub : Subgroup (GL (Fin (r + 1)) (Af E))), IsOpen (Uβ : Set (GL (Fin (m + 1)) (Af E))) → IsOpen (Ub : Set (GL (Fin (r + 1)) (Af E))) → ∀ (Krow : Set (Fin (m + 1) → Af E)) (Kcol : Set (Fin (r + 1) → Af E)), IsCompact Krow → IsCompact Kcol → ∃ W ∈ 𝓝 (1 : GL (Fin (m + r + 1 + 1)) (Af E)), ∀ k ∈ W, (∀ w ∉ S, Matrix.GeneralLinearGroup.map (pLoc E w) k = 1) → ∀ Y : Matrix (Fin (r + 1)) (Fin (m + 1)) (Af E), (∀ i j, Y i j ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E) → IsUnit (Dof (conjLowUni Y (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E)))).det ∧ mkGL (Dof (conjLowUni Y (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E)))) ∈ Ub ∧ mkGL (Scof (conjLowUni Y (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E)))) ∈ Uβ ∧ (∀ i j, Yof (conjLowUni Y (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E))) i j ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E) ∧ ∀ ρ ∈ Krow, ∀ γ ∈ Kcol, (∑ j, ∑ l, ρ j * Xof (conjLowUni Y (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E))) j l * γ l) ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E := by
  first | (exact @GlobalTheory.SchurNear.blocks_small) | (exact GlobalTheory.SchurNear.blocks_small) | (intros; apply GlobalTheory.SchurNear.blocks_small <;> assumption)
end
end

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

noncomputable section

namespace GlobalTheory.SchurExt.InvParts

theorem L_bridge : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m r : ℕ) (x : GA E (m + r + 1 + 1)) (k : GL (Fin (m + r + 1 + 1)) (Af E)), IsUnit (Dof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det → IsUnit (Dof (conjLowUni ((Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map (pFin E)) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E)))).det → IsUnit (Scof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det ∧ IsUnit (Dof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det ∧ mkGL (Dof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) = mkGL (Dof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) * finGL E (r + 1) (mkGL (Dof (conjLowUni ((Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map (pFin E)) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E))))) ∧ mkGL (Scof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) = mkGL (Scof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) * finGL E (m + 1) (mkGL (Scof (conjLowUni ((Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map (pFin E)) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E))))) ∧ (∀ i j, pInf E (Yof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) i j) = pInf E (Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) i j)) ∧ (∀ i j, pFin E (Yof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) i j) = pFin E (Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) i j) + Yof (conjLowUni ((Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map (pFin E)) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E))) i j) ∧ Xof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) (Fin.last m) 0 = Xof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) (Fin.last m) 0 + sFin E (∑ j, ∑ l, pFin E (Scof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) (Fin.last m) j) * Xof (conjLowUni ((Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map (pFin E)) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E))) j l * pFin E ((Dof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)))⁻¹ l 0)) := GlobalTheory.T.isUnit_block_det_of_conj_lower

theorem L_top : ∀ (E : Type) [Field E] [NumberField E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (Uβ : Subgroup (GL (Fin (m + 1)) (Af E))) (Ub : Subgroup (GL (Fin (r + 1)) (Af E))), IsOpen (Uβ : Set (GL (Fin (m + 1)) (Af E))) → IsOpen (Ub : Set (GL (Fin (r + 1)) (Af E))) → ∀ (Krow : Set (Fin (m + 1) → Af E)) (Kcol : Set (Fin (r + 1) → Af E)), IsCompact Krow → IsCompact Kcol → ∃ W ∈ 𝓝 (1 : GL (Fin (m + r + 1 + 1)) (Af E)), ∀ k ∈ W, (∀ w ∉ S, Matrix.GeneralLinearGroup.map (pLoc E w) k = 1) → ∀ Y : Matrix (Fin (r + 1)) (Fin (m + 1)) (Af E), (∀ i j, Y i j ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E) → IsUnit (Dof (conjLowUni Y (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E)))).det ∧ mkGL (Dof (conjLowUni Y (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E)))) ∈ Ub ∧ mkGL (Scof (conjLowUni Y (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E)))) ∈ Uβ ∧ (∀ i j, Yof (conjLowUni Y (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E))) i j ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E) ∧ ∀ ρ ∈ Krow, ∀ γ ∈ Kcol, (∑ j, ∑ l, ρ j * Xof (conjLowUni Y (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E))) j l * γ l) ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E := GlobalTheory.T.exists_nhds_one_conjLowerUnipotent_schurBlocks_small

theorem L_row : ∀ (E : Type) [Field E] [NumberField E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (β : GA E (m + 1) → ℂ), (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, β h ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * h ∈ C) → ∃ K : Set (Fin (m + 1) → Af E), IsCompact K ∧ ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, β h ≠ 0 → (fun j => pFin E ((h : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) j)) ∈ K := GlobalTheory.T.lastRow_finite_mem_compact_on_support

theorem L_col : ∀ (E : Type) [Field E] [NumberField E] (r : ℕ) (b₁ : GA E (r + 1) → ℂ), (∃ C : Set (GA E (r + 1)), IsCompact C ∧ ∀ p, b₁ p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (r + 1)), u⁻¹ * p ∈ C) → ∃ K : Set (Fin (r + 1) → Af E), IsCompact K ∧ ∀ p, b₁ p ≠ 0 → (fun l => pFin E (((p⁻¹ : GA E (r + 1)) : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E)) l 0)) ∈ K := GlobalTheory.T.firstColumn_inv_finite_mem_compact_on_support

theorem L_supSc : ∀ (E : Type) [Field E] [NumberField E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (x : GA E (m + r + 1 + 1)), x ∈ GlobalTheory.JSW.supS (E := E) (a := (m + r + 1 + 1)) S → IsUnit (Dof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det → mkGL (Scof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S := GlobalTheory.T.schurComplement_mem_adelicGLSupportedAtFinitePlaces

end GlobalTheory.SchurExt.InvParts

namespace GlobalTheory.SchurExt

variable {E : Type} [Field E] [NumberField E]

theorem psi_sFin_of_mem {z : Af E} (hz : z ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E) : psi (sFin E z) = 1 := by
  have h := GroundTheory.Global.adelicChar_of_mem_invDifferentAdeles (K := E) (y := sFin E z)
    (GroundTheory.Global.mem_invDifferentAdeles.mpr (GroundTheory.Global.mem_finiteInvDifferent_of_mem_integralFiniteAdeles hz))
  have h0 : (sFin E z).1 = 0 := rfl
  rw [psi, h, h0]
  simp

theorem psi_add (a b : Ad E) : psi (a + b) = psi a * psi b := by
  simp only [psi, AddChar.map_add_eq_mul, Circle.coe_mul]

theorem supS_mul {a : ℕ} {S : Finset (HeightOneSpectrum (𝓞 E))} {x y : GA E a}
    (hx : x ∈ GlobalTheory.JSW.supS (E := E) (a := a) S) (hy : y ∈ GlobalTheory.JSW.supS (E := E) (a := a) S) : x * y ∈ GlobalTheory.JSW.supS (E := E) (a := a) S := by
  intro w hw
  rw [map_mul, hx w hw, hy w hw, mul_one]

theorem supS_inv {a : ℕ} {S : Finset (HeightOneSpectrum (𝓞 E))} {x : GA E a}
    (hx : x ∈ GlobalTheory.JSW.supS (E := E) (a := a) S) : x⁻¹ ∈ GlobalTheory.JSW.supS (E := E) (a := a) S := by
  intro w hw
  rw [map_inv, hx w hw, inv_one]

theorem finGL_mem_supS {a : ℕ} {S : Finset (HeightOneSpectrum (𝓞 E))} {k : GL (Fin a) (Af E)}
    (hk : finGL E a k ∈ GlobalTheory.JSW.supS (E := E) (a := a) S) (w : HeightOneSpectrum (𝓞 E)) (hw : w ∉ S) :
    Matrix.GeneralLinearGroup.map (pLoc E w) k = 1 := by
  have h := hk w hw
  rw [← h]
  refine Units.ext (Matrix.ext fun i j => ?_)
  change pLoc E w (k i j) = pLoc E w (pFin E ((finGL E a k : GA E a) i j))
  congr 1
  exact (congrArg (fun y : GL (Fin a) (Af E) => (y : Matrix (Fin a) (Fin a) (Af E)) i j) (pFin_finGL (E := E) k)).symm

end GlobalTheory.SchurExt


open GlobalTheory.SchurExt.InvParts in
theorem GlobalTheory.SchurExt.schurF_mul_finGL_eq : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (β : GA E (m + 1) → ℂ) (b₁ : GA E (r + 1) → ℂ) (χ : (Fin (r + 1) → Fin (m + 1) → Cinf E) → ℝ), (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, β (g * finGL E (m + 1) u) = β g) → (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, β h ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * h ∈ C) → (∃ U : Subgroup (GL (Fin (r + 1)) (Af E)), IsOpen (U : Set (GL (Fin (r + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, b₁ (g * finGL E (r + 1) u) = b₁ g) → (∃ C : Set (GA E (r + 1)), IsCompact C ∧ ∀ p, b₁ p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (r + 1)), u⁻¹ * p ∈ C) → ∃ W ∈ 𝓝 (1 : GL (Fin (m + r + 1 + 1)) (Af E)), ∀ k ∈ W, finGL E (m + r + 1 + 1) k ∈ GlobalTheory.JSW.supS (E := E) (a := (m + r + 1 + 1)) S → ∀ x ∈ GlobalTheory.JSW.supS (E := E) (a := (m + r + 1 + 1)) S, schurF β b₁ χ (x * finGL E (m + r + 1 + 1) k) = schurF β b₁ χ x := by
  intro E _ _ _ m r S β b₁ χ ⟨Uβ, hUβo, hUβ⟩ hβC ⟨Ub, hUbo, hUb⟩ hbC
  obtain ⟨Krow, hKr, hKrow⟩ := L_row E m S β hβC
  obtain ⟨Kcol, hKc, hKcol⟩ := L_col E r b₁ hbC
  obtain ⟨W₀, hW₀, hW⟩ := L_top E m r S Uβ Ub hUβo hUbo Krow Kcol hKr hKc
  have fwd : ∀ k ∈ W₀, finGL E (m + r + 1 + 1) k ∈ GlobalTheory.JSW.supS (E := E) (a := (m + r + 1 + 1)) S →
      ∀ x ∈ GlobalTheory.JSW.supS (E := E) (a := (m + r + 1 + 1)) S, schurF β b₁ χ x ≠ 0 →
        schurF β b₁ χ (x * finGL E (m + r + 1 + 1) k) = schurF β b₁ χ x := by
    intro k hk hkS x hx hF
    classical
    have hD : IsUnit (Dof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det := by
      by_contra hD
      exact hF (by rw [schurF, ite_eq_right hD])
    rw [schurF, ite_eq_left hD] at hF
    have hβ0 := left_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul hF))
    have hβ0' := right_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul hF))
    have hb0 := right_ne_zero_of_mul (left_ne_zero_of_mul hF)
    have hχ0 := right_ne_zero_of_mul hF
    have hYint : ∀ i j, pFin E (Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) i j) ∈
        GroundTheory.Global.integralFiniteAdeles (𝓞 E) E := by
      by_contra hY
      exact hχ0 (by rw [chiF, ite_eq_right hY, mul_zero])
    obtain ⟨hdu, hdU, hsU, hyI, hX⟩ := hW k hk (finGL_mem_supS hkS)
      ((Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map (pFin E)) (fun i j => hYint i j)
    obtain ⟨hSc, hD', eD, eSc, eYi, eYf, eX⟩ := L_bridge E m r x k hD hdu
    have hrow := hKrow _ (L_supSc E m r S x hx hD) hβ0'
    have hcol := hKcol _ hb0
    rw [coe_mkGL hSc] at hrow
    rw [Matrix.coe_units_inv, coe_mkGL hD] at hcol
    have hz := hX _ hrow _ hcol
    have hchi : chiF χ (Yof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) :
        Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) =
        chiF χ (Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) := by
      have h1 : (fun i j => pInf E (Yof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) :
          Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) i j)) =
          fun i j => pInf E (Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) i j) :=
        funext fun i => funext fun j => eYi i j
      have h2 : ∀ i j, pFin E (Yof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) :
          Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) i j) ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E :=
        fun i j => by rw [eYf]; exact add_mem (hYint i j) (hyI i j)
      rw [chiF, chiF, h1, ite_eq_left h2, ite_eq_left hYint]
    rw [schurF, ite_eq_left hD', eD, eSc, hUb _ hdU, hUβ _ hsU, hchi, eX, psi_add, psi_sFin_of_mem hz, mul_one, schurF, ite_eq_left hD]
  open scoped Pointwise in
  exact by
    refine ⟨W₀ ∩ W₀⁻¹, Filter.inter_mem hW₀ (inv_mem_nhds_one _ hW₀), ?_⟩
    intro k hk hkS x hx
    by_cases h0 : schurF β b₁ χ x = 0
    · by_cases h1 : schurF β b₁ χ (x * finGL E (m + r + 1 + 1) k) = 0
      · rw [h0, h1]
      · have h2 := fwd k⁻¹ hk.2 (by rw [map_inv]; exact supS_inv hkS) _ (supS_mul hx hkS) h1
        rw [mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one] at h2
        exact absurd (h2.symm.trans h0) h1
    · exact fwd k hk.1 hkS x hx h0
