module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdelicCharacterArchimedeanForm
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanOrbitalIntegralHuaBound
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InfinitesimalCharacterConjugate
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorizableSiegelWeilFiniteSet
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteTwistedDoubleCosets
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockWeilActionThetaUnfolding

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousBlkM
noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt

open MeasureTheory Matrix
open scoped ComplexConjugate

def blkM {n : ℕ} (b : Matrix (Fin n) (Fin n) ℂ) (u : Fin n → ℂ) (d : ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks b (Matrix.replicateCol (Fin 1) u) (Matrix.replicateRow (Fin 1) (star u))
      (Matrix.of fun _ _ => (d : ℂ)))

theorem blkM_mem {n : ℕ} (b : hermC n) (u : Fin n → ℂ) (d : ℝ) :
    blkM (b : Matrix (Fin n) (Fin n) ℂ) u d ∈ hermC (n + 1) := by
  have hb : (b : Matrix (Fin n) (Fin n) ℂ).IsHermitian := mem_hermC.1 b.2
  rw [mem_hermC]
  unfold blkM
  simp only [Matrix.reindex_apply]
  apply Matrix.IsHermitian.submatrix
  apply Matrix.IsHermitian.fromBlocks hb
  · ext i j
    simp [Matrix.conjTranspose_apply]
  · ext i j
    simp [Matrix.conjTranspose_apply]

def blk {n : ℕ} (b : hermC n) (u : Fin n → ℂ) (d : ℝ) : hermC (n + 1) :=
  ⟨blkM (b : Matrix (Fin n) (Fin n) ℂ) u d, blkM_mem b u d⟩

theorem continuous_blkM {n : ℕ} :
    Continuous (fun x : Matrix (Fin n) (Fin n) ℂ × (Fin n → ℂ) × ℝ => blkM x.1 x.2.1 x.2.2) := by
  refine continuous_matrix fun i j => ?_
  unfold blkM
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  rcases h1 : finSumFinEquiv.symm i with i' | i' <;> rcases h2 : finSumFinEquiv.symm j with j' | j' <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.replicateCol_apply, Matrix.replicateRow_apply, Pi.star_apply,
      Matrix.of_apply]
  all_goals fun_prop

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductHuaDeterminantIntegrable
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HuaDeterminantIntegrableOfLt
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetWEqNormSqDetOneAddI
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetWEqNormSqDetOneAddI
noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt

open MeasureTheory Matrix

theorem detW_eq_normSq_det_one_add_I_smul :
    ∀ (n : ℕ) (b : Matrix (Fin n) (Fin n) ℂ), b.IsHermitian →
      detW b = Complex.normSq (Matrix.det (1 + Complex.I • b)) := by
  intro n b hb
  unfold detW
  have h1 : (1 + b * b : Matrix (Fin n) (Fin n) ℂ) = (1 + Complex.I • b) * (1 + Complex.I • b)ᴴ := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.conjTranspose_smul, hb.eq,
      Complex.star_def, Complex.conj_I]
    simp only [add_mul, mul_add, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_neg,
      Complex.I_mul_I, one_smul, neg_smul]
    abel
  rw [h1, Matrix.det_mul, Matrix.det_conjTranspose, Complex.star_def, Complex.mul_conj, Complex.ofReal_re]

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetWEqNormSqDetOneAddIStatement
open MeasureTheory Matrix
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.detW_eq_normSq_det_one_add_I : ∀ (n : ℕ) (b : Matrix (Fin n) (Fin n) ℂ), b.IsHermitian →
    detW b = Complex.normSq (Matrix.det (1 + Complex.I • b)) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.detW_eq_normSq_det_one_add_I_smul | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.detW_eq_normSq_det_one_add_I_smul | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.detW_eq_normSq_det_one_add_I_smul <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneLeDetW
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneLeDetW
open MeasureTheory Matrix
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt

theorem det_one_add_sq_eq_prod_eigenvalues (n : ℕ) (b : Matrix (Fin n) (Fin n) ℂ) (hb : b.IsHermitian) :
    Matrix.det (1 + b * b) = ((∏ i, (1 + hb.eigenvalues i ^ 2) : ℝ) : ℂ) := by
  set U : Matrix (Fin n) (Fin n) ℂ := (hb.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  set D : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.diagonal (fun i => ((hb.eigenvalues i : ℝ) : ℂ)) with hD
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self hb.eigenvectorUnitary
  have hUU' : U * star U = 1 := Unitary.coe_mul_star_self hb.eigenvectorUnitary
  have hs : b = U * D * star U := by
    have := hb.spectral_theorem
    simpa [Unitary.conjStarAlgAut_apply, hU, hD, Function.comp_def] using this
  have h1 : 1 + b * b = U * (1 + D * D) * star U := by
    rw [hs]
    calc 1 + U * D * star U * (U * D * star U)
        = U * star U + U * D * (star U * U) * D * star U := by
          rw [hUU']; simp only [Matrix.mul_assoc]
      _ = U * (1 + D * D) * star U := by
          rw [hUU]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_assoc]
  have hdet : (star U).det * U.det = 1 := by
    rw [← Matrix.det_mul, hUU, Matrix.det_one]
  have h2 : 1 + D * D = Matrix.diagonal (fun i => (((1 + hb.eigenvalues i ^ 2 : ℝ)) : ℂ)) := by
    rw [hD, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one, Matrix.diagonal_add]
    congr 1
    ext i
    push_cast
    ring
  rw [h1, Matrix.det_mul, Matrix.det_mul, h2, Matrix.det_diagonal]
  push_cast
  calc U.det * (∏ i, (1 + ((hb.eigenvalues i : ℝ) : ℂ) ^ 2)) * (star U).det
      = ((star U).det * U.det) * ∏ i, (1 + ((hb.eigenvalues i : ℝ) : ℂ) ^ 2) := by ring
    _ = _ := by rw [hdet, one_mul]

theorem one_le_detW : ∀ (n : ℕ) (b : Matrix (Fin n) (Fin n) ℂ), b.IsHermitian → 1 ≤ detW b := by
  intro n b hb
  unfold detW
  rw [det_one_add_sq_eq_prod_eigenvalues n b hb, Complex.ofReal_re]
  have : ∀ i ∈ (Finset.univ : Finset (Fin n)), (1 : ℝ) ≤ 1 + hb.eigenvalues i ^ 2 := fun i _ => by
    nlinarith [sq_nonneg (hb.eigenvalues i)]
  calc (1 : ℝ) = ∏ _i : Fin n, (1 : ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => zero_le_one) this

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneLeDetWStatement
open MeasureTheory Matrix
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_le_detW_of_isHermitian : ∀ (n : ℕ) (b : Matrix (Fin n) (Fin n) ℂ), b.IsHermitian → 1 ≤ detW b := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.one_le_detW | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.one_le_detW | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.one_le_detW <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetWBlockMatrixFormula
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetWBlockMatrixFormula
noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt

open MeasureTheory Matrix

theorem one_add_I_blkM_eq {n : ℕ} (b : Matrix (Fin n) (Fin n) ℂ) (u : Fin n → ℂ) (d : ℝ) :
    (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) + Complex.I • blkM b u d =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (1 + Complex.I • b) (Complex.I • Matrix.replicateCol (Fin 1) u)
          (Complex.I • Matrix.replicateRow (Fin 1) (star u))
          (Matrix.of fun _ _ => 1 + Complex.I * (d : ℂ))) := by
  ext i j
  obtain ⟨i', rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j', rfl⟩ := finSumFinEquiv.surjective j
  rcases i' with i' | i' <;> rcases j' with j' | j'
  · simp [blkM, Matrix.one_apply]
  · have h : ¬Fin.castAdd 1 i' = Fin.natAdd n j' := by
      rw [Fin.ext_iff]; simp; omega
    simp [blkM, Matrix.one_apply, h]
  · have h : ¬Fin.natAdd n i' = Fin.castAdd 1 j' := by
      rw [Fin.ext_iff]; simp; omega
    simp [blkM, Matrix.one_apply, h]
  · obtain rfl := Subsingleton.elim i' j'
    simp [blkM]

theorem det_one_add_I_blkM {n : ℕ} (b : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) (d : ℝ) :
    Matrix.det (1 + Complex.I • blkM b ((1 + Complex.I • b) *ᵥ v) d) =
      Matrix.det (1 + Complex.I • b) *
        (1 + Complex.I * (d : ℂ) + star ((1 + Complex.I • b) *ᵥ v) ⬝ᵥ v) := by
  rw [one_add_I_blkM_eq, Matrix.det_reindex_self]
  set D : Matrix (Fin n) (Fin n) ℂ := 1 + Complex.I • b with hD
  set u : Fin n → ℂ := D *ᵥ v with hu
  have hcol : D * Matrix.replicateCol (Fin 1) v = Matrix.replicateCol (Fin 1) u := by
    ext i j
    simp [hu, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  have hmul :
      Matrix.fromBlocks D (Complex.I • Matrix.replicateCol (Fin 1) u)
          (Complex.I • Matrix.replicateRow (Fin 1) (star u))
          (Matrix.of fun _ _ => 1 + Complex.I * (d : ℂ)) *
        Matrix.fromBlocks 1 (-Complex.I • Matrix.replicateCol (Fin 1) v) 0
          (1 : Matrix (Fin 1) (Fin 1) ℂ) =
      Matrix.fromBlocks D 0 (Complex.I • Matrix.replicateRow (Fin 1) (star u))
        (Matrix.of fun _ _ => 1 + Complex.I * (d : ℂ) + star u ⬝ᵥ v) := by
    rw [Matrix.fromBlocks_multiply]
    congr 1
    · simp
    · simp [Matrix.mul_smul, hcol]
    · simp
    · ext i j
      have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
      simp [Matrix.mul_apply, dotProduct, Finset.mul_sum, mul_assoc, mul_left_comm]
      simp only [← mul_assoc, hI, neg_mul, one_mul, Finset.sum_neg_distrib, neg_neg]
      ring
  have hdet := congrArg Matrix.det hmul
  rw [Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₁₂] at hdet
  simpa using hdet

theorem quad_real {n : ℕ} {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian) (v : Fin n → ℂ) :
    ((star v ⬝ᵥ (b *ᵥ v)).re : ℂ) = star v ⬝ᵥ (b *ᵥ v) := by
  have h : star (star v ⬝ᵥ (b *ᵥ v)) = star v ⬝ᵥ (b *ᵥ v) := by
    rw [← Matrix.star_dotProduct, Matrix.star_mulVec, hb.eq, Matrix.dotProduct_mulVec]
  exact Complex.conj_eq_iff_re.1 h

theorem star_mulVec_dot {n : ℕ} {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian)
    (v : Fin n → ℂ) :
    star ((1 + Complex.I • b) *ᵥ v) ⬝ᵥ v =
      ((∑ i, Complex.normSq (v i) : ℝ) : ℂ) - Complex.I * ((star v ⬝ᵥ (b *ᵥ v)).re : ℂ) := by
  rw [quad_real hb, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
  have hH : (1 + Complex.I • b)ᴴ = 1 - Complex.I • b := by
    simp [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hb.eq, sub_eq_add_neg]
  rw [hH, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, dotProduct_sub,
    dotProduct_smul, smul_eq_mul]
  congr 1
  simp [dotProduct, Complex.normSq_eq_conj_mul_self]

theorem normSq_det_one_add_I_blkM (n : ℕ) (b : Matrix (Fin n) (Fin n) ℂ) (hb : b.IsHermitian)
    (_hdet : Matrix.det (1 + Complex.I • b) ≠ 0) (v : Fin n → ℂ) (d : ℝ) :
    Complex.normSq (Matrix.det (1 + Complex.I • blkM b ((1 + Complex.I • b) *ᵥ v) d)) =
      Complex.normSq (Matrix.det (1 + Complex.I • b)) *
        ((1 + ∑ i, Complex.normSq (v i)) ^ 2 + (d - (star v ⬝ᵥ (b *ᵥ v)).re) ^ 2) := by
  rw [det_one_add_I_blkM, map_mul, star_mulVec_dot hb]
  congr 1
  set r : ℝ := ∑ i, Complex.normSq (v i)
  set m : ℝ := (star v ⬝ᵥ (b *ᵥ v)).re
  have : (1 + Complex.I * (d : ℂ) + ((r : ℂ) - Complex.I * (m : ℂ))) =
      (((1 + r : ℝ) : ℂ)) + (((d - m : ℝ) : ℂ)) * Complex.I := by
    push_cast; ring
  rw [this, Complex.normSq_add_mul_I]

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetWBlockMatrixFormulaStatement
open MeasureTheory Matrix
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.detW_block_matrix_formula : ∀ (n : ℕ) (b : Matrix (Fin n) (Fin n) ℂ), b.IsHermitian →
    Matrix.det (1 + Complex.I • b) ≠ 0 → ∀ (v : Fin n → ℂ) (d : ℝ),
    Complex.normSq (Matrix.det (1 + Complex.I • blkM b ((1 + Complex.I • b) *ᵥ v) d)) =
      Complex.normSq (Matrix.det (1 + Complex.I • b)) *
        ((1 + ∑ i, Complex.normSq (v i)) ^ 2 + (d - (star v ⬝ᵥ (b *ᵥ v)).re) ^ 2) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.normSq_det_one_add_I_blkM | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.normSq_det_one_add_I_blkM | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.normSq_det_one_add_I_blkM <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianHaarBlockDecomposition
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianHaarBlockDecomposition
noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt

open MeasureTheory Matrix
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch

theorem blkM_castSucc_castSucc {n : ℕ} (b : Matrix (Fin n) (Fin n) ℂ) (u : Fin n → ℂ) (d : ℝ)
    (i j : Fin n) : blkM b u d i.castSucc j.castSucc = b i j := by
  have h : ∀ k : Fin n, finSumFinEquiv.symm k.castSucc = (Sum.inl k : Fin n ⊕ Fin 1) :=
    fun k => finSumFinEquiv_symm_apply_castAdd k
  simp [blkM, Matrix.reindex_apply, Matrix.submatrix_apply, h]

theorem blkM_castSucc_last {n : ℕ} (b : Matrix (Fin n) (Fin n) ℂ) (u : Fin n → ℂ) (d : ℝ)
    (i : Fin n) : blkM b u d i.castSucc (Fin.last n) = u i := by
  have h : ∀ k : Fin n, finSumFinEquiv.symm k.castSucc = (Sum.inl k : Fin n ⊕ Fin 1) :=
    fun k => finSumFinEquiv_symm_apply_castAdd k
  simp [blkM, Matrix.reindex_apply, Matrix.submatrix_apply, h, finSumFinEquiv_symm_last]

theorem blkM_last_last {n : ℕ} (b : Matrix (Fin n) (Fin n) ℂ) (u : Fin n → ℂ) (d : ℝ) :
    blkM b u d (Fin.last n) (Fin.last n) = d := by
  simp [blkM, Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_last]

theorem blkM_last_castSucc {n : ℕ} (b : Matrix (Fin n) (Fin n) ℂ) (u : Fin n → ℂ) (d : ℝ)
    (j : Fin n) : blkM b u d (Fin.last n) j.castSucc = star (u j) := by
  have h : ∀ k : Fin n, finSumFinEquiv.symm k.castSucc = (Sum.inl k : Fin n ⊕ Fin 1) :=
    fun k => finSumFinEquiv_symm_apply_castAdd k
  simp [blkM, Matrix.reindex_apply, Matrix.submatrix_apply, h, finSumFinEquiv_symm_last]

theorem blkM_add {n : ℕ} (b b' : Matrix (Fin n) (Fin n) ℂ) (u u' : Fin n → ℂ) (d d' : ℝ) :
    blkM (b + b') (u + u') (d + d') = blkM b u d + blkM b' u' d' := by
  ext i j
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simp [blkM_last_last]
    | cast j => simp [blkM_last_castSucc]
  | cast i =>
    induction j using Fin.lastCases with
    | last => simp [blkM_castSucc_last]
    | cast j => simp [blkM_castSucc_castSucc]

def upperLeftHermBlock {n : ℕ} (b : hermC (n + 1)) : hermC n :=
  ⟨(b : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ).submatrix Fin.castSucc Fin.castSucc,
    mem_hermC.2 ((mem_hermC.1 b.2).submatrix _)⟩

def blkEquiv (n : ℕ) : (hermC n × (Fin n → ℂ) × ℝ) ≃+ hermC (n + 1) where
  toFun x := blk x.1 x.2.1 x.2.2
  invFun b := (upperLeftHermBlock b, fun i => (b : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) i.castSucc (Fin.last n),
    ((b : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (Fin.last n) (Fin.last n)).re)
  left_inv x := by
    obtain ⟨b, u, d⟩ := x
    refine Prod.ext (Subtype.ext ?_) (Prod.ext ?_ ?_)
    · ext i j
      simp [upperLeftHermBlock, blk, blkM_castSucc_castSucc]
    · ext i
      simp [blk, blkM_castSucc_last]
    · simp [blk, blkM_last_last]
  right_inv b := by
    have hb := mem_hermC.1 b.2
    apply Subtype.ext
    ext i j
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last =>
        simp only [blk, blkM_last_last]
        have := hb.apply (Fin.last n) (Fin.last n)
        exact (Complex.conj_eq_iff_real.1 this).choose_spec ▸ by simp
      | cast j =>
        simp only [blk, blkM_last_castSucc]
        exact hb.apply _ _
    | cast i =>
      induction j using Fin.lastCases with
      | last => simp [blk, blkM_castSucc_last]
      | cast j => simp [blk, blkM_castSucc_castSucc, upperLeftHermBlock]
  map_add' x y := by
    apply Subtype.ext
    simp [blk, blkM_add]

theorem continuous_blkEquiv (n : ℕ) : Continuous (blkEquiv n) := by
  refine Continuous.subtype_mk (f := fun x : hermC n × (Fin n → ℂ) × ℝ =>
    blkM (x.1 : Matrix (Fin n) (Fin n) ℂ) x.2.1 x.2.2) ?_ _
  exact continuous_blkM.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)

theorem continuous_blkEquiv_symm (n : ℕ) : Continuous (blkEquiv n).symm := by
  have h : ∀ i j : Fin (n + 1), Continuous fun b : hermC (n + 1) =>
      (b : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) i j := fun i j =>
    (continuous_apply_apply i j).comp continuous_subtype_val
  refine Continuous.prodMk ?_ (Continuous.prodMk ?_ ?_)
  · refine Continuous.subtype_mk (continuous_matrix fun i j => ?_) _
    exact h _ _
  · exact continuous_pi fun i => h _ _
  · exact Complex.continuous_re.comp (h _ _)

theorem haar_blocks (n : ℕ) (ν : Measure (hermC (n + 1))) (ν' : Measure (hermC n))
    (hν : ν.IsAddHaarMeasure) (hν' : ν'.IsAddHaarMeasure) :
    ∃ c : ENNReal, c ≠ ⊤ ∧ ∀ F : hermC (n + 1) → ENNReal, Measurable F →
      ∫⁻ b, F b ∂ν = c * ∫⁻ b', ∫⁻ u : Fin n → ℂ, ∫⁻ d : ℝ, F (blk b' u d) ∂volume ∂volume ∂ν' := by
  haveI := hν
  haveI := hν'
  haveI : (volume : Measure (Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have hp : (ν'.prod ((volume : Measure (Fin n → ℂ)).prod (volume : Measure ℝ))).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  have hm : (Measure.map (blkEquiv n)
      (ν'.prod ((volume : Measure (Fin n → ℂ)).prod (volume : Measure ℝ)))).IsAddHaarMeasure :=
    (blkEquiv n).isAddHaarMeasure_map _ (continuous_blkEquiv n) (continuous_blkEquiv_symm n)
  have he : Measurable (blkEquiv n) := (continuous_blkEquiv n).measurable
  refine ⟨(Measure.addHaarScalarFactor ν (Measure.map (blkEquiv n)
      (ν'.prod ((volume : Measure (Fin n → ℂ)).prod (volume : Measure ℝ)))) : ENNReal),
    ENNReal.coe_ne_top, fun F hF => ?_⟩
  conv_lhs => rw [Measure.isAddLeftInvariant_eq_smul ν (Measure.map (blkEquiv n)
      (ν'.prod ((volume : Measure (Fin n → ℂ)).prod (volume : Measure ℝ))))]
  rw [lintegral_smul_measure, lintegral_map hF he, lintegral_prod (fun a => F (blkEquiv n a)) (hF.comp he).aemeasurable]
  simp only [ENNReal.smul_def, smul_eq_mul]
  congr 1
  refine lintegral_congr fun b' => ?_
  rw [lintegral_prod]
  · rfl
  · exact ((hF.comp he).comp measurable_prodMk_left).aemeasurable

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianHaarBlockDecompositionStatement
open MeasureTheory Matrix
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_haar_block_decomposition : ∀ (n : ℕ) (ν : Measure (hermC (n + 1))) (ν' : Measure (hermC n)),
    ν.IsAddHaarMeasure → ν'.IsAddHaarMeasure →
    ∃ c : ENNReal, c ≠ ⊤ ∧ ∀ F : hermC (n + 1) → ENNReal, Measurable F →
      ∫⁻ b, F b ∂ν = c * ∫⁻ b', ∫⁻ u : Fin n → ℂ, ∫⁻ d : ℝ, F (blk b' u d) ∂volume ∂volume ∂ν' := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.haar_blocks | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.haar_blocks | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.haar_blocks <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralLinearChangeVariablesComplex
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralLinearChangeVariablesComplex
open MeasureTheory Matrix
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt

theorem det_restrictScalars_toLin' {n : ℕ} (D : Matrix (Fin n) (Fin n) ℂ) :
    LinearMap.det ((Matrix.toLin' D).restrictScalars ℝ) = Complex.normSq (Matrix.det D) := by
  rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply]

theorem lintegral_eq_normSq_det_mul_lintegral_mulVec (n : ℕ) (D : Matrix (Fin n) (Fin n) ℂ)
    (hD : Matrix.det D ≠ 0) (g : (Fin n → ℂ) → ENNReal) (hg : Measurable g) :
    ∫⁻ u, g u = ENNReal.ofReal (Complex.normSq (Matrix.det D)) * ∫⁻ v, g (D *ᵥ v) := by
  set f : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ) := (Matrix.toLin' D).restrictScalars ℝ with hf
  have hdet : LinearMap.det f = Complex.normSq (Matrix.det D) := det_restrictScalars_toLin' D
  have hpos : 0 < Complex.normSq (Matrix.det D) := Complex.normSq_pos.mpr hD
  have hne : LinearMap.det f ≠ 0 := by
    rw [hdet]
    exact hpos.ne'
  have hmap := MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar
    (volume : Measure (Fin n → ℂ)) hne
  have hfm : Measurable f := f.continuous_of_finiteDimensional.measurable
  have key : ∫⁻ v, g (D *ᵥ v) = ENNReal.ofReal (Complex.normSq (Matrix.det D))⁻¹ * ∫⁻ u, g u := by
    have e : ∀ v, D *ᵥ v = f v := fun v => by simp [hf, Matrix.toLin'_apply]
    simp_rw [e]
    rw [← lintegral_map hg hfm, hmap, lintegral_smul_measure, hdet, abs_of_pos (inv_pos.mpr hpos), smul_eq_mul]
  rw [key, ← mul_assoc, ← ENNReal.ofReal_mul hpos.le, mul_inv_cancel₀ hpos.ne', ENNReal.ofReal_one,
    one_mul]

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralLinearChangeVariablesComplexStatement
open MeasureTheory Matrix
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_linear_change_variables_complex : ∀ (n : ℕ) (D : Matrix (Fin n) (Fin n) ℂ), Matrix.det D ≠ 0 →
    ∀ g : (Fin n → ℂ) → ENNReal, Measurable g →
    ∫⁻ u, g u = ENNReal.ofReal (Complex.normSq (Matrix.det D)) * ∫⁻ v, g (D *ᵥ v) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.lintegral_eq_normSq_det_mul_lintegral_mulVec | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.lintegral_eq_normSq_det_mul_lintegral_mulVec | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.lintegral_eq_normSq_det_mul_lintegral_mulVec <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralComplexPowerFinite
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralComplexPowerFinite
open MeasureTheory Matrix
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt

theorem lintegral_one_add_normSq_rpow_ne_top :
    ∀ (n : ℕ) (t : ℝ), (n : ℝ) < t →
    ∫⁻ v : Fin n → ℂ, ENNReal.ofReal ((1 + ∑ i, Complex.normSq (v i)) ^ (-t)) ≠ ⊤ := by
  intro n t ht
  have ht0 : 0 < t := lt_of_le_of_lt n.cast_nonneg ht
  have hdim : (Module.finrank ℝ (Fin n → ℂ) : ℝ) < 2 * t := by
    simp [Module.finrank_pi_fintype, Complex.finrank_real_complex]
    linarith
  have hint := integrable_rpow_neg_one_add_norm_sq (E := Fin n → ℂ) (μ := volume) hdim
  refine ne_of_lt (lt_of_le_of_lt (lintegral_mono fun v => ?_) hint.lintegral_lt_top)
  apply ENNReal.ofReal_le_ofReal

  have hS0 : 0 ≤ ∑ i, Complex.normSq (v i) := Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  have hnorm : ‖v‖ ≤ Real.sqrt (∑ i, Complex.normSq (v i)) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i => ?_
    have h1 : ‖v i‖ ^ 2 ≤ ∑ j, Complex.normSq (v j) := by
      rw [← Complex.normSq_eq_norm_sq]
      exact Finset.single_le_sum (fun j _ => Complex.normSq_nonneg (v j)) (Finset.mem_univ i)
    simpa [abs_of_nonneg (norm_nonneg _)] using Real.abs_le_sqrt h1
  have hab : 1 + ‖v‖ ^ 2 ≤ 1 + ∑ i, Complex.normSq (v i) := by
    have h2 := pow_le_pow_left₀ (norm_nonneg v) hnorm 2
    rw [Real.sq_sqrt hS0] at h2
    linarith
  have ha : 0 < 1 + ‖v‖ ^ 2 := by positivity
  rw [show -(2 * t) / 2 = -t by ring, Real.rpow_neg (by linarith), Real.rpow_neg ha.le]
  exact inv_anti₀ (Real.rpow_pos_of_pos ha t) (Real.rpow_le_rpow ha.le hab ht0.le)

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralComplexPowerFiniteStatement
open MeasureTheory Matrix
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_complex_power_finite : ∀ (n : ℕ) (t : ℝ), (n : ℝ) < t →
    ∫⁻ v : Fin n → ℂ, ENNReal.ofReal ((1 + ∑ i, Complex.normSq (v i)) ^ (-t)) ≠ ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.lintegral_one_add_normSq_rpow_ne_top | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.lintegral_one_add_normSq_rpow_ne_top | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.lintegral_one_add_normSq_rpow_ne_top <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralPowerLineScaling
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralPowerLineScaling
open MeasureTheory Matrix
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt

theorem lintegral_sq_add_sq_rpow_neg :
    ∀ s : ℝ, 1 / 2 < s → ∃ C : ENNReal, C ≠ ⊤ ∧ ∀ a : ℝ, 0 < a → ∀ m : ℝ,
    ∫⁻ d : ℝ, ENNReal.ofReal ((a ^ 2 + (d - m) ^ 2) ^ (-s)) = C * ENNReal.ofReal (a ^ (1 - 2 * s)) := by
  intro s hs
  have hint : Integrable (fun t : ℝ => (1 + t ^ 2) ^ (-s)) := by
    have h0 := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (r := 2 * s)
      (by simp; linarith)
    have e : -(2 * s) / 2 = -s := by ring
    simpa [Real.norm_eq_abs, sq_abs, e] using h0
  refine ⟨∫⁻ t, ENNReal.ofReal ((1 + t ^ 2) ^ (-s)), hint.lintegral_lt_top.ne, ?_⟩
  intro a ha m
  have hF : Measurable fun d : ℝ => ENNReal.ofReal ((a ^ 2 + d ^ 2) ^ (-s)) := by fun_prop
  rw [lintegral_sub_right_eq_self (fun d : ℝ => ENNReal.ofReal ((a ^ 2 + d ^ 2) ^ (-s))) m]
  have hpt : ∀ t : ℝ, ENNReal.ofReal ((a ^ 2 + (a * t) ^ 2) ^ (-s)) =
      ENNReal.ofReal (a ^ ((2 : ℕ) * -s : ℝ)) * ENNReal.ofReal ((1 + t ^ 2) ^ (-s)) := by
    intro t
    rw [← ENNReal.ofReal_mul (by positivity), show a ^ 2 + (a * t) ^ 2 = a ^ 2 * (1 + t ^ 2) by ring,
      Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast a 2,
      ← Real.rpow_mul ha.le]
  have hpow : a ^ (1 - 2 * s) = a * a ^ ((2 : ℕ) * -s : ℝ) := by
    rw [show (1 - 2 * s) = 1 + ((2 : ℕ) * -s : ℝ) by push_cast; ring, Real.rpow_add ha,
      Real.rpow_one]
  calc ∫⁻ d, ENNReal.ofReal ((a ^ 2 + d ^ 2) ^ (-s))
      = ∫⁻ d, ENNReal.ofReal ((a ^ 2 + d ^ 2) ^ (-s))
          ∂(ENNReal.ofReal |a| • Measure.map (a * ·) volume) := by
        rw [Real.smul_map_volume_mul_left ha.ne']
    _ = ENNReal.ofReal |a| * ∫⁻ t, ENNReal.ofReal ((a ^ 2 + (a * t) ^ 2) ^ (-s)) := by
        rw [lintegral_smul_measure, lintegral_map hF (measurable_const_mul a), smul_eq_mul]
    _ = ENNReal.ofReal a * (ENNReal.ofReal (a ^ ((2 : ℕ) * -s : ℝ)) *
          ∫⁻ t, ENNReal.ofReal ((1 + t ^ 2) ^ (-s))) := by
        rw [abs_of_pos ha]
        simp_rw [hpt]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul ha.le, ← hpow, mul_comm]

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralPowerLineScalingStatement
open MeasureTheory Matrix
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_power_line_scaling : ∀ s : ℝ, 1 / 2 < s → ∃ C : ENNReal, C ≠ ⊤ ∧ ∀ a : ℝ, 0 < a → ∀ m : ℝ,
    ∫⁻ d : ℝ, ENNReal.ofReal ((a ^ 2 + (d - m) ^ 2) ^ (-s)) = C * ENNReal.ofReal (a ^ (1 - 2 * s)) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.lintegral_sq_add_sq_rpow_neg | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.lintegral_sq_add_sq_rpow_neg | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.lintegral_sq_add_sq_rpow_neg <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HuaDeterminantIntegrableOfLt
noncomputable section
namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
open MeasureTheory Matrix
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch

theorem continuous_detW (n : ℕ) : Continuous (fun b : Matrix (Fin n) (Fin n) ℂ => detW b) := by
  unfold detW
  exact Complex.continuous_re.comp (Continuous.matrix_det (by fun_prop))

theorem measurable_term (n : ℕ) (s : ℝ) :
    Measurable (fun b : hermC n => ENNReal.ofReal (detW (b : Matrix (Fin n) (Fin n) ℂ) ^ (-s))) := by
  have h : Continuous (fun b : hermC n => detW (b : Matrix (Fin n) (Fin n) ℂ)) :=
    (continuous_detW n).comp continuous_subtype_val
  exact (h.measurable.pow_const _).ennreal_ofReal

theorem inner_eq (n : ℕ) (s : ℝ) (hs : (n : ℝ) + 1 / 2 < s) : ∃ K : ENNReal, K ≠ ⊤ ∧
    ∀ b' : hermC n, ∫⁻ u : Fin n → ℂ, ∫⁻ d : ℝ,
      ENNReal.ofReal (detW (blk b' u d : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) ^ (-s)) =
      K * ENNReal.ofReal (detW (b' : Matrix (Fin n) (Fin n) ℂ) ^ (-(s - 1))) := by
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
  obtain ⟨C, hC, hD⟩ := GlobalTheory.T.lintegral_power_line_scaling s (by linarith)
  have hL := GlobalTheory.T.lintegral_complex_power_finite n (2 * s - 1) (by linarith)
  set L := ∫⁻ v : Fin n → ℂ, ENNReal.ofReal ((1 + ∑ i, Complex.normSq (v i)) ^ (-(2 * s - 1))) with hLdef
  refine ⟨C * L, ENNReal.mul_ne_top hC hL, fun b' => ?_⟩
  have hB : (b' : Matrix (Fin n) (Fin n) ℂ).IsHermitian := mem_hermC.1 b'.2
  have hw1 := GlobalTheory.T.one_le_detW_of_isHermitian n _ hB
  have hwA := GlobalTheory.T.detW_eq_normSq_det_one_add_I n _ hB
  have hdet : Matrix.det (1 + Complex.I • (b' : Matrix (Fin n) (Fin n) ℂ)) ≠ 0 := by
    intro h0
    rw [h0] at hwA
    simp at hwA
    linarith
  have hgm : Measurable (fun u : Fin n → ℂ => ∫⁻ d : ℝ,
      ENNReal.ofReal (detW (blk b' u d : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) ^ (-s))) := by
    apply Measurable.lintegral_prod_right'
      (f := fun p : (Fin n → ℂ) × ℝ => ENNReal.ofReal (detW (blk b' p.1 p.2 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) ^ (-s)))
    have hc : Continuous (fun p : (Fin n → ℂ) × ℝ => detW (blk b' p.1 p.2 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)) :=
      (continuous_detW _).comp (continuous_blkM.comp
        (by fun_prop : Continuous fun p : (Fin n → ℂ) × ℝ => ((b' : Matrix (Fin n) (Fin n) ℂ), p.1, p.2)))
    exact (hc.measurable.pow_const _).ennreal_ofReal
  rw [GlobalTheory.T.lintegral_linear_change_variables_complex n _ hdet _ hgm, ← hwA]
  have hv : ∀ v : Fin n → ℂ, ∫⁻ d : ℝ, ENNReal.ofReal (detW (blk b' ((1 + Complex.I • (b' : Matrix (Fin n) (Fin n) ℂ)) *ᵥ v) d : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) ^ (-s))
      = ENNReal.ofReal (detW (b' : Matrix (Fin n) (Fin n) ℂ) ^ (-s)) *
        (C * ENNReal.ofReal ((1 + ∑ i, Complex.normSq (v i)) ^ (-(2 * s - 1)))) := by
    intro v
    have hr : 0 ≤ ∑ i, Complex.normSq (v i) := Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
    have hterm : ∀ d : ℝ, ENNReal.ofReal (detW (blk b' ((1 + Complex.I • (b' : Matrix (Fin n) (Fin n) ℂ)) *ᵥ v) d : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) ^ (-s))
        = ENNReal.ofReal (detW (b' : Matrix (Fin n) (Fin n) ℂ) ^ (-s)) *
          ENNReal.ofReal (((1 + ∑ i, Complex.normSq (v i)) ^ 2 +
            (d - (star v ⬝ᵥ ((b' : Matrix (Fin n) (Fin n) ℂ) *ᵥ v)).re) ^ 2) ^ (-s)) := by
      intro d
      have hh := mem_hermC.1 (blk b' ((1 + Complex.I • (b' : Matrix (Fin n) (Fin n) ℂ)) *ᵥ v) d).2
      rw [GlobalTheory.T.detW_eq_normSq_det_one_add_I _ _ hh]
      have e : ((blk b' ((1 + Complex.I • (b' : Matrix (Fin n) (Fin n) ℂ)) *ᵥ v) d : hermC (n+1)) : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
          = blkM (b' : Matrix (Fin n) (Fin n) ℂ) ((1 + Complex.I • (b' : Matrix (Fin n) (Fin n) ℂ)) *ᵥ v) d := rfl
      rw [e, GlobalTheory.T.detW_block_matrix_formula n _ hB hdet v d, ← hwA, Real.mul_rpow (by linarith) (by positivity),
        ENNReal.ofReal_mul (Real.rpow_nonneg (by linarith) _)]
    simp only [hterm]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hD (1 + ∑ i, Complex.normSq (v i)) (by linarith)]
    congr 3
    ring_nf
  simp only [hv]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ hC]
  have e2 : ENNReal.ofReal (detW (b' : Matrix (Fin n) (Fin n) ℂ) ^ (-(s - 1)))
      = ENNReal.ofReal (detW (b' : Matrix (Fin n) (Fin n) ℂ)) *
        ENNReal.ofReal (detW (b' : Matrix (Fin n) (Fin n) ℂ) ^ (-s)) := by
    rw [← ENNReal.ofReal_mul (by linarith)]
    congr 1
    rw [show -(s - 1) = 1 + -s by ring, Real.rpow_add (by linarith), Real.rpow_one]
  rw [e2]
  ring

theorem hua_integrable : ∀ (n : ℕ) (s : ℝ), (n : ℝ) - 1 / 2 < s → ∀ ν : Measure (hermC n), ν.IsAddHaarMeasure →
    Integrable (fun b : hermC n => detW (b : Matrix (Fin n) (Fin n) ℂ) ^ (-s)) ν := by
  intro n
  induction n with
  | zero =>
    intro s _ ν hν
    have : IsFiniteMeasure ν := by
      haveI : Finite (hermC 0) := by
        haveI : Subsingleton (Matrix (Fin 0) (Fin 0) ℂ) := inferInstance
        exact Finite.of_subsingleton
      haveI : CompactSpace (hermC 0) := Finite.compactSpace
      exact ⟨isCompact_univ.measure_lt_top⟩
    have h1 : ∀ b : hermC 0, detW (b : Matrix (Fin 0) (Fin 0) ℂ) ^ (-s) = 1 := by
      intro b
      simp [detW]
    simp only [h1]
    exact integrable_const _
  | succ n ih =>
    intro s hs ν hν
    have hs' : (n : ℝ) + 1 / 2 < s := by push_cast at hs; linarith
    have hpos : ∀ b : hermC (n + 1), 0 ≤ detW (b : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) ^ (-s) := fun b =>
      Real.rpow_nonneg (by linarith [GlobalTheory.T.one_le_detW_of_isHermitian _ _ (mem_hermC.1 b.2)]) _
    have hmeas := measurable_term (n + 1) s
    have hm2 : Measurable (fun b : hermC (n + 1) => detW (b : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) ^ (-s)) :=
      (((continuous_detW (n + 1)).comp continuous_subtype_val).measurable.pow_const _)
    refine ⟨hm2.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hpos)]
    obtain ⟨c, hc, hF⟩ := GlobalTheory.T.hermitian_haar_block_decomposition n ν (Measure.addHaar) hν inferInstance
    obtain ⟨K, hK, hI⟩ := inner_eq n s hs'
    rw [hF _ hmeas]
    simp only [hI]
    rw [lintegral_const_mul _ (measurable_term n (s - 1))]
    have h3 := ih (s - 1) (by linarith) Measure.addHaar inferInstance
    have hp3 : ∀ b : hermC n, 0 ≤ detW (b : Matrix (Fin n) (Fin n) ℂ) ^ (-(s - 1)) := fun b =>
      Real.rpow_nonneg (by linarith [GlobalTheory.T.one_le_detW_of_isHermitian _ _ (mem_hermC.1 b.2)]) _
    have h4 := (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hp3)).1 h3.2
    exact ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hc)
      (ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hK) h4)

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HuaDeterminantIntegrableOfLtStatement
open MeasureTheory
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hua_determinant_integrable_of_lt : ∀ (n : ℕ) (s : ℝ), (n : ℝ) - 1 / 2 < s → ∀ ν : Measure (hermC n), ν.IsAddHaarMeasure →
  Integrable (fun b : hermC n => detW (b : Matrix (Fin n) (Fin n) ℂ) ^ (-s)) ν := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.hua_integrable | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.hua_integrable | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.hua_integrable <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductHuaDeterminantIntegrable
open MeasureTheory
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch

theorem integrable_prod_detW_rpow : ∀ (W : Type) [Fintype W] (n : ℕ) (s : ℝ), (n : ℝ) - 1 / 2 < s →
    ∀ ν : Measure (W → hermC n), ν.IsAddHaarMeasure →
    Integrable (fun b : W → hermC n => ∏ w, detW (b w : Matrix (Fin n) (Fin n) ℂ) ^ (-s)) ν := by
  intro W _ n s hs ν hν
  let μ₀ : Measure (hermC n) := Measure.addHaar
  have hf : ∀ _w : W, Integrable (fun b : hermC n => detW (b : Matrix (Fin n) (Fin n) ℂ) ^ (-s)) μ₀ :=
    fun _ => GlobalTheory.T.hua_determinant_integrable_of_lt n s hs μ₀ inferInstance
  have hpi := Integrable.fintype_prod (μ := fun _ : W => μ₀)
    (f := fun _ : W => fun b : hermC n => detW (b : Matrix (Fin n) (Fin n) ℂ) ^ (-s)) hf
  rw [Measure.isAddLeftInvariant_eq_smul ν (Measure.pi fun _ : W => μ₀)]
  exact hpi.smul_measure_nnreal

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductHuaDeterminantIntegrableStatement
open MeasureTheory
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.product_hua_determinant_integrable : ∀ (W : Type) [Fintype W] (n : ℕ) (s : ℝ), (n : ℝ) - 1 / 2 < s →
  ∀ ν : Measure (W → hermC n), ν.IsAddHaarMeasure →
  Integrable (fun b : W → hermC n => ∏ w, detW (b w : Matrix (Fin n) (Fin n) ℂ) ^ (-s)) ν := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.integrable_prod_detW_rpow | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.integrable_prod_detW_rpow | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.integrable_prod_detW_rpow <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanOrbitalIntegralContinuous
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanOrbitalIntegralContinuous
open MeasureTheory
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.Cont

theorem continuous_phaseM_X {W : Type} [Fintype W] {n M : ℕ}
    (J : W → Matrix (Fin M) (Fin M) ℂ) (B : W → Matrix (Fin n) (Fin n) ℂ) :
    Continuous (phaseM J B) := by
  unfold phaseM
  refine continuous_finsetSum _ fun w _ => Complex.continuous_re.comp ?_
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, gramC]
  refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun c _ => ?_
  refine continuous_const.mul ?_
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  have h1 : Continuous fun X : W → Fin n → Fin M → ℂ => X w c i := by fun_prop
  have h2 : Continuous fun X : W → Fin n → Fin M → ℂ => X w a j := by fun_prop
  first
    | exact ((Complex.continuous_conj.comp h1).mul continuous_const).mul (by fun_prop)
    | exact ((Complex.continuous_conj.comp h2).mul continuous_const).mul (by fun_prop)

theorem continuous_phaseM_b {W : Type} [Fintype W] {n M : ℕ}
    (J : W → Matrix (Fin M) (Fin M) ℂ) (X : W → Fin n → Fin M → ℂ) :
    Continuous fun b : W → hermC n =>
      phaseM J (fun w => (b w : Matrix (Fin n) (Fin n) ℂ)) X := by
  unfold phaseM
  refine continuous_finsetSum _ fun w _ => Complex.continuous_re.comp ?_
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun c _ => ?_
  refine Continuous.mul ?_ continuous_const
  have h0 : Continuous fun b : W → hermC n => (b w : Matrix (Fin n) (Fin n) ℂ) :=
    continuous_subtype_val.comp (continuous_apply w)
  have h1 : Continuous fun m : Matrix (Fin n) (Fin n) ℂ => m a c :=
    (continuous_apply c).comp (continuous_apply a)
  exact h1.comp h0

theorem integrable_comp {E : Type} [AddCommGroup E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [MeasurableSpace E] [BorelSpace E]
    (N : ℕ) (e : E ≃+ (Fin N → ℝ)) (he : Continuous e) (hes : Continuous e.symm)
    (f : SchwartzMap (Fin N → ℝ) ℂ) (μ : Measure E) [μ.IsAddHaarMeasure] :
    Integrable (fun X => f (e X)) μ := by
  haveI : (Measure.map e μ).IsAddHaarMeasure := e.isAddHaarMeasure_map μ he hes
  have hs := Measure.isAddLeftInvariant_eq_smul (Measure.map e μ)
    (volume : Measure (Fin N → ℝ))
  have hi : Integrable f (Measure.map e μ) := by
    rw [hs]
    exact (f.integrable (μ := volume)).smul_measure_nnreal
  exact hi.comp_measurable he.measurable

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.Cont

theorem GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.continuous_coreC_schwartz
    (W : Type) [Fintype W] (n M : ℕ) (J : W → Matrix (Fin M) (Fin M) ℂ)
    (N : ℕ) (e : (W → Fin n → Fin M → ℂ) ≃+ (Fin N → ℝ)) (he : Continuous e)
    (hes : Continuous e.symm) (f : SchwartzMap (Fin N → ℝ) ℂ)
    (μ : Measure (W → Fin n → Fin M → ℂ)) (hμ : μ.IsAddHaarMeasure) :
    Continuous (coreC J μ (fun X => f (e X))) := by
  have hint := Cont.integrable_comp N e he hes f μ
  have hg : Continuous fun X => f (e X) := f.continuous.comp he
  have hnorm : ∀ t : ℝ, ‖Complex.exp (2 * Real.pi * Complex.I * (t : ℂ))‖ = 1 := by
    intro t
    have : (2 * Real.pi * Complex.I * (t : ℂ)) = ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]
  unfold coreC
  refine continuous_of_dominated (bound := fun X => ‖f (e X)‖) ?_ ?_ hint.norm ?_
  · intro b
    refine Continuous.aestronglyMeasurable (hg.mul ?_)
    have := Cont.continuous_phaseM_X J (fun w => (b w : Matrix (Fin n) (Fin n) ℂ))
    exact Complex.continuous_exp.comp
      (continuous_const.mul (Complex.continuous_ofReal.comp this))
  · intro b
    refine Filter.Eventually.of_forall fun X => ?_
    rw [norm_mul, hnorm, mul_one]
  · refine Filter.Eventually.of_forall fun X => ?_
    exact continuous_const.mul (Complex.continuous_exp.comp
      (continuous_const.mul (Complex.continuous_ofReal.comp (Cont.continuous_phaseM_b J X))))
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanOrbitalIntegralContinuousStatement
open MeasureTheory
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_orbital_integral_continuous : ∀ (W : Type) [Fintype W] (n M : ℕ) (J : W → Matrix (Fin M) (Fin M) ℂ)
  (N : ℕ) (e : (W → Fin n → Fin M → ℂ) ≃+ (Fin N → ℝ)), Continuous e → Continuous e.symm →
  ∀ (f : SchwartzMap (Fin N → ℝ) ℂ) (μ : Measure (W → Fin n → Fin M → ℂ)), μ.IsAddHaarMeasure →
  Continuous (coreC J μ (fun X => f (e X))) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.continuous_coreC_schwartz | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.continuous_coreC_schwartz | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.continuous_coreC_schwartz <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanSiegelWeilIntegralIdentity
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch NumberField

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch

theorem core_integrable {W : Type} [Fintype W] {n M : ℕ} (hnM : 2 * n < M) (J : W → Matrix (Fin M) (Fin M) ℂ)
    (hJ : ∀ w, (J w).IsHermitian) (hJd : ∀ w, (J w).det ≠ 0) {N : ℕ}
    (e : (W → Fin n → Fin M → ℂ) ≃+ (Fin N → ℝ)) (he : Continuous e) (hes : Continuous e.symm)
    (f : SchwartzMap (Fin N → ℝ) ℂ) (μ : Measure (W → Fin n → Fin M → ℂ)) (hμ : μ.IsAddHaarMeasure)
    (ν : Measure (W → hermC n)) (hν : ν.IsAddHaarMeasure) :
    Integrable (coreC J μ (fun X => f (e X))) ν := by
  obtain ⟨C, hC⟩ := GlobalTheory.T.archimedean_orbital_integral_hua_bound W n M J hJ hJd N e he hes f μ hμ
  have hcont := GlobalTheory.T.archimedean_orbital_integral_continuous W n M J N e he hes f μ hμ
  have hs : (n : ℝ) - 1 / 2 < (M : ℝ) / 2 := by
    have : (2 * n + 1 : ℝ) ≤ M := by exact_mod_cast hnM
    linarith
  have hint := (GlobalTheory.T.product_hua_determinant_integrable W n ((M : ℝ) / 2) hs ν hν).const_mul C
  refine hint.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun b => ?_)
  have := hC b
  simpa [neg_div] using this

theorem integrable_starLoc_inf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
  ∀ n : ℕ, 2 * n < M → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∀ μ : Measure (Fin n → Fin M → Ainf F ⊗[F] E), μ.IsAddHaarMeasure →
  ∀ ν : Measure (HermR (Ainf F) σ n), ν.IsAddHaarMeasure →
  ∀ P : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ, GlobalTheory.Published.SiegelOneVector.IsSchwartzArch P →
    Integrable (starLoc (Ainf F) σ J (psiInf F ψ) μ P) ν := by
  intro F E _ _ _ _ _ σ hcm M J hJ n hn ψ hψ μ hμ ν hν P hP
  obtain ⟨ρ, e, hρ, he, heρ, -, -⟩ := GlobalTheory.T.infinite_adele_haar_map_eq_scaled_volume F hcm.1
  obtain ⟨a, ha, hinf, -, -, -⟩ := GlobalTheory.T.adelic_character_archimedean_form F hcm.1 ρ e hρ he heρ ψ hψ
  obtain ⟨τ, Θ, hΘ⟩ := GlobalTheory.T.complex_coordinates_exist_at_infinity F E σ hcm ρ e hρ he heρ
  obtain ⟨Ψ, hΨ, hΨν⟩ := GlobalTheory.T.hermitian_archimedean_complex_coordinates F E σ hcm e τ Θ hΘ n
  obtain ⟨Φ, hΦ, hΦc, hΦs, hΦμ⟩ := GlobalTheory.T.tuple_archimedean_complex_coordinates F E σ hcm e τ Θ hΘ n M
  obtain ⟨N, e₀, he₀, he₀s, f, hP⟩ := hP
  obtain ⟨hνH, hνI⟩ := hΨν ν hν
  obtain ⟨hμH, hμI⟩ := hΦμ μ hμ
  let Jc : InfinitePlace F → Matrix (Fin M) (Fin M) ℂ := fun w => ((ρ w a : ℝ) : ℂ) • J.map (τ w)
  have hρa : ∀ w, ((ρ w a : ℝ) : ℂ) ≠ 0 := fun w => by
    simpa using (map_ne_zero (ρ w)).2 ha
  have hJc : ∀ w, (Jc w).IsHermitian := fun w => by
    ext i j
    have h1 := hJ.1 i j
    have h2 := hcm.2.2.2 (τ w) (J j i)
    simp only [Jc, Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, star_mul',
      Complex.star_def, Complex.conj_ofReal]
    rw [h1] at h2
    rw [h2]
    rfl
  have hJd : ∀ w, (Jc w).det ≠ 0 := fun w => by
    simp only [Jc, Matrix.det_smul]
    refine mul_ne_zero (pow_ne_zero _ (hρa w)) ?_
    have : (J.map (τ w)).det = τ w J.det := by
      simpa using (RingHom.map_det (τ w) J).symm
    rw [this]
    exact (map_ne_zero (τ w)).2 hJ.2
  let e₂ : (InfinitePlace F → Fin n → Fin M → ℂ) ≃+ (Fin N → ℝ) := Φ.symm.trans e₀
  have he₂ : Continuous e₂ := he₀.comp hΦs
  have he₂s : Continuous e₂.symm := hΦc.comp he₀s
  have hcore := core_integrable hn Jc hJc hJd e₂ he₂ he₂s f (μ.map Φ) hμH (ν.map Ψ) hνH
  have := hνI _ hcore
  refine this.congr (Filter.Eventually.of_forall fun b => ?_)
  show coreC Jc (μ.map Φ) (fun X => f (e₂ X)) (Ψ b) = starLoc (Ainf F) σ J (psiInf F ψ) μ P b
  rw [coreC, ← hμI]
  unfold starLoc
  refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
  show f (e₂ (Φ X)) * _ = P X * _
  have hph := GlobalTheory.T.archimedean_character_in_coordinates F E σ ρ e τ Θ hΘ heρ a ψ hinf M n J (b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) X
  rw [hph, hP X]
  have h1 : e₂ (Φ X) = e₀ X := by simp [e₂]
  have h2 : (fun w => ((Ψ b w : hermC n) : Matrix (Fin n) (Fin n) ℂ)) = fun w => matC Θ (b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) w := funext (hΨ b)
  rw [h1, h2, hΦ X]

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanSiegelWeilIntegralIdentityStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_siegel_weil_integral_identity : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
  ∀ n : ℕ, 2 * n < M → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∀ μ : Measure (Fin n → Fin M → Ainf F ⊗[F] E), μ.IsAddHaarMeasure →
  ∀ ν : Measure (HermR (Ainf F) σ n), ν.IsAddHaarMeasure →
  ∀ P : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ, GlobalTheory.Published.SiegelOneVector.IsSchwartzArch P →
    Integrable (starLoc (Ainf F) σ J (psiInf F ψ) μ P) ν := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.integrable_starLoc_inf | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.integrable_starLoc_inf | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.integrable_starLoc_inf <;> assumption)
end
