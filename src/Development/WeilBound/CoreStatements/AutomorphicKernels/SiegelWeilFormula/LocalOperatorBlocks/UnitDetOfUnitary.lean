module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalOperatorBlocks.IntgPowQuad
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalOperatorBlocks.ContinuousWeightFactorUnitary
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalOperatorBlocks.EqZeroOfEvalReal

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalOperatorBlocks.MobJJDiag
noncomputable section

open scoped Matrix
open MeasureTheory PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula

namespace PositivityTheory.SiegelWeilFormula.KLI

variable {m n : ℕ}

def mob (M : M2 n) (Z : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (M.toBlocks₁₁ * Z + M.toBlocks₁₂) * (M.toBlocks₂₁ * Z + M.toBlocks₂₂)⁻¹

theorem toBlocks₁₁_mul (M N : M2 n) : (M * N).toBlocks₁₁ = M.toBlocks₁₁ * N.toBlocks₁₁ + M.toBlocks₁₂ * N.toBlocks₂₁ := by
  ext i j
  simp [Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁, Matrix.mul_apply, Fintype.sum_sum_type]

theorem toBlocks₁₂_mul (M N : M2 n) : (M * N).toBlocks₁₂ = M.toBlocks₁₁ * N.toBlocks₁₂ + M.toBlocks₁₂ * N.toBlocks₂₂ := by
  ext i j
  simp [Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₂, Matrix.mul_apply, Fintype.sum_sum_type]

theorem toBlocks₂₁_mul (M N : M2 n) : (M * N).toBlocks₂₁ = M.toBlocks₂₁ * N.toBlocks₁₁ + M.toBlocks₂₂ * N.toBlocks₂₁ := by
  ext i j
  simp [Matrix.toBlocks₁₁, Matrix.toBlocks₂₂, Matrix.toBlocks₂₁, Matrix.mul_apply, Fintype.sum_sum_type]

theorem toBlocks₂₂_mul (M N : M2 n) : (M * N).toBlocks₂₂ = M.toBlocks₂₁ * N.toBlocks₁₂ + M.toBlocks₂₂ * N.toBlocks₂₂ := by
  ext i j
  simp [Matrix.toBlocks₁₂, Matrix.toBlocks₂₂, Matrix.toBlocks₂₁, Matrix.mul_apply, Fintype.sum_sum_type]

theorem mob_mul (M N : M2 n) (Z : Matrix (Fin n) (Fin n) ℂ) (hV : IsUnit (N.toBlocks₂₁ * Z + N.toBlocks₂₂).det) :
    mob (M * N) Z = mob M (mob N Z) := by
  set V := N.toBlocks₂₁ * Z + N.toBlocks₂₂ with hVdef
  set W := N.toBlocks₁₁ * Z + N.toBlocks₁₂ with hWdef
  have h1 : (M * N).toBlocks₁₁ * Z + (M * N).toBlocks₁₂ = M.toBlocks₁₁ * W + M.toBlocks₁₂ * V := by
    rw [toBlocks₁₁_mul, toBlocks₁₂_mul, hVdef, hWdef]; noncomm_ring
  have h2 : (M * N).toBlocks₂₁ * Z + (M * N).toBlocks₂₂ = M.toBlocks₂₁ * W + M.toBlocks₂₂ * V := by
    rw [toBlocks₂₁_mul, toBlocks₂₂_mul, hVdef, hWdef]; noncomm_ring
  clear_value V W
  have hVV : V * V⁻¹ = 1 := Matrix.mul_nonsing_inv V hV
  have hVV' : V⁻¹ * V = 1 := Matrix.nonsing_inv_mul V hV
  have e1 : M.toBlocks₁₁ * (W * V⁻¹) + M.toBlocks₁₂ = (M.toBlocks₁₁ * W + M.toBlocks₁₂ * V) * V⁻¹ := by
    rw [Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, hVV, Matrix.mul_one]
  have e2 : M.toBlocks₂₁ * (W * V⁻¹) + M.toBlocks₂₂ = (M.toBlocks₂₁ * W + M.toBlocks₂₂ * V) * V⁻¹ := by
    rw [Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, hVV, Matrix.mul_one]
  unfold mob
  rw [h1, h2, ← hWdef, ← hVdef, e1, e2, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv V hV, Matrix.mul_assoc,
    ← Matrix.mul_assoc V⁻¹, hVV', Matrix.one_mul]

theorem mob_nU (b Z : Matrix (Fin n) (Fin n) ℂ) : mob (nU b) Z = Z + b := by
  simp [mob, nU]

theorem mob_mLc (a Z : Matrix (Fin n) (Fin n) ℂ) (ha : IsUnit a.det) : mob (mLc a) Z = a * Z * aᴴ := by
  have h : IsUnit (aᴴ).det := by rw [Matrix.det_conjTranspose]; exact ha.star
  simp [mob, mLc, Matrix.nonsing_inv_nonsing_inv _ h]

theorem mob_JJ_diag (z : Fin n → ℂ) (hz : ∀ j, z j ≠ 0) :
    mob (JJ n) (Matrix.diagonal z) = Matrix.diagonal fun j => (-z j)⁻¹ := by
  simp only [mob, JJ, Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂, Matrix.toBlocks_fromBlocks₂₁,
    Matrix.toBlocks_fromBlocks₂₂, Matrix.zero_mul, zero_add, add_zero, Matrix.one_mul, Matrix.neg_mul]
  rw [Matrix.diagonal_neg]
  apply Matrix.inv_eq_left_inv
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases h : i = j
  · subst h; simp [hz i]
  · simp [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]

abbrev Z0 (sg : ℤˣ) : Matrix (Fin n) (Fin n) ℂ := (Complex.I * ((sg : ℤ) : ℂ)) • 1

theorem sg_sq (sg : ℤˣ) : ((sg : ℤ) : ℂ) * ((sg : ℤ) : ℂ) = 1 := by
  rcases Int.units_eq_one_or sg with h | h <;> simp [h]

theorem mob_K (sg : ℤˣ) (M : M2 n) (hM : InK M) (hV : IsUnit (M.toBlocks₂₁ * Z0 sg + M.toBlocks₂₂).det) :
    mob M (Z0 sg) = Z0 sg := by
  obtain ⟨hG, hU⟩ := hM
  have hU' : M * Mᴴ = 1 := mul_eq_one_comm.mp hU
  have hc : JJ n * M = M * JJ n := by
    calc JJ n * M = (M * Mᴴ) * JJ n * M := by rw [hU', Matrix.one_mul]
      _ = M * (Mᴴ * JJ n * M) := by simp only [Matrix.mul_assoc]
      _ = M * JJ n := by rw [hG]
  have hM' := Matrix.fromBlocks_toBlocks M
  rw [← hM'] at hc
  simp only [JJ, Matrix.fromBlocks_multiply] at hc
  simp only [Matrix.zero_mul, Matrix.one_mul, zero_add, add_zero, Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg,
    Matrix.neg_mul, neg_zero] at hc
  obtain ⟨e1, e2, -, -⟩ := Matrix.fromBlocks_inj.mp hc
  set σ : ℂ := ((sg : ℤ) : ℂ)
  have hσ := sg_sq sg
  set X := M.toBlocks₂₁ * Z0 sg + M.toBlocks₂₂ with hX
  have hnum : M.toBlocks₁₁ * Z0 sg + M.toBlocks₁₂ = (Complex.I * σ) • X := by
    rw [hX, e1, e2]
    simp only [Z0, Matrix.mul_smul, Matrix.mul_one, smul_add, Matrix.neg_mul, smul_neg, smul_smul]
    rw [show Complex.I * σ * (Complex.I * σ) = -1 by rw [mul_mul_mul_comm, Complex.I_mul_I, hσ]; ring]
    simp [neg_smul]; abel
  unfold mob
  rw [hnum, ← hX, Matrix.smul_mul, Matrix.mul_nonsing_inv X hV]

end PositivityTheory.SiegelWeilFormula.KLI

end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalOperatorBlocks.IntegrandMono
section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalOperatorBlocks.GaussianMomentRealCoords
section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalOperatorBlocks.EvalMonomial2
noncomputable section

open MeasureTheory Complex MvPolynomial

namespace PositivityTheory.SiegelWeilFormula.KLI

def toMv {σ : Type} (i : σ) (p : Polynomial ℂ) : MvPolynomial σ ℂ :=
  ∑ j ∈ Finset.range (p.natDegree + 1), C (p.coeff j) * X i ^ j

theorem eval_toMv {σ : Type} (i : σ) (p : Polynomial ℂ) (g : σ → ℂ) : eval g (toMv i p) = p.eval (g i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [toMv, Polynomial.eval_eq_sum_range, map_sum]

theorem deg_toMv {σ : Type} (i : σ) (p : Polynomial ℂ) : (toMv i p).totalDegree ≤ p.natDegree := by
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun j hj => ?_)
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_pow _ _).trans ?_
  have := Finset.mem_range.mp hj
  have h1 : (X i : MvPolynomial σ ℂ).totalDegree ≤ 1 := by rw [totalDegree_X]
  nlinarith

theorem deg_bind_le {σ τ : Type} (f : σ → MvPolynomial τ ℂ) (hf : ∀ i, (f i).totalDegree ≤ 1)
    (p : MvPolynomial σ ℂ) : (bind₁ f p).totalDegree ≤ p.totalDegree := by
  conv_lhs => rw [p.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun v hv => ?_)
  rw [bind₁_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  refine le_trans ?_ (le_totalDegree hv)
  refine Finset.sum_le_sum fun i _ => ?_
  refine (totalDegree_pow _ _).trans ?_
  have := hf i
  nlinarith

def G2 (b l μ : ℂ) (p : ℝ × ℝ) : ℂ := cexp (b * (p.1 : ℂ) ^ 2 + l * p.1) * cexp (b * (p.2 : ℂ) ^ 2 + μ * p.2)

theorem eval_monomial2 (v : Fin 2 →₀ ℕ) (c : ℂ) (x y : ℝ) :
    eval ![(x : ℂ), (y : ℂ)] (monomial v c) = c * ((x : ℂ) ^ v 0 * (y : ℂ) ^ v 1) := by
  rw [eval_monomial, Finsupp.prod_fintype _ _ (by simp)]
  simp [Fin.prod_univ_two]

theorem intg_mono2 {b : ℂ} (hb : b.re < 0) (l μ : ℂ) (v : Fin 2 →₀ ℕ) (c : ℂ) :
    Integrable (fun p : ℝ × ℝ => eval ![(p.1 : ℂ), (p.2 : ℂ)] (monomial v c) * G2 b l μ p) := by
  have := ((intg_pow_quad hb (v 0) l).mul_prod (intg_pow_quad hb (v 1) μ)).const_mul c
  refine this.congr (Filter.Eventually.of_forall fun p => ?_)
  simp only [G2, eval_monomial2]
  ring

theorem intg_poly2 {b : ℂ} (hb : b.re < 0) (l μ : ℂ) (R : MvPolynomial (Fin 2) ℂ) :
    Integrable (fun p : ℝ × ℝ => eval ![(p.1 : ℂ), (p.2 : ℂ)] R * G2 b l μ p) := by
  have e : (fun p : ℝ × ℝ => eval ![(p.1 : ℂ), (p.2 : ℂ)] R * G2 b l μ p) =
      fun p => ∑ v ∈ R.support, eval ![(p.1 : ℂ), (p.2 : ℂ)] (monomial v (AddMonoidAlgebra.coeff R v)) * G2 b l μ p := by
    funext p
    conv_lhs => rw [R.as_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_mul]
  rw [e]
  exact integrable_finsetSum _ fun v _ => intg_mono2 hb l μ v _

theorem mom2 {b : ℂ} (hb : b.re < 0) (R : MvPolynomial (Fin 2) ℂ) :
    ∃ R' : MvPolynomial (Fin 2) ℂ, R'.totalDegree ≤ R.totalDegree ∧ ∀ l μ : ℂ,
      ∫ p : ℝ × ℝ, eval ![(p.1 : ℂ), (p.2 : ℂ)] R * G2 b l μ p = eval ![l, μ] R' * (J b 0 l * J b 0 μ) := by
  refine ⟨∑ v ∈ R.support, C (AddMonoidAlgebra.coeff R v) * (toMv 0 (pk b (v 0)) * toMv 1 (pk b (v 1))), ?_, fun l μ => ?_⟩
  · refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun v hv => ?_)
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    refine (totalDegree_mul _ _).trans ?_
    refine le_trans ?_ (le_totalDegree hv)
    have h0 := (deg_toMv (0 : Fin 2) (pk b (v 0))).trans (pk_deg b (v 0))
    have h1 := (deg_toMv (1 : Fin 2) (pk b (v 1))).trans (pk_deg b (v 1))
    have hs : v.sum (fun _ e => e) = v 0 + v 1 := by
      rw [Finsupp.sum_fintype _ _ (by simp)]; simp [Fin.sum_univ_two]
    rw [hs]; omega
  · have e : (fun p : ℝ × ℝ => eval ![(p.1 : ℂ), (p.2 : ℂ)] R * G2 b l μ p) =
        fun p => ∑ v ∈ R.support, eval ![(p.1 : ℂ), (p.2 : ℂ)] (monomial v (AddMonoidAlgebra.coeff R v)) * G2 b l μ p := by
      funext p
      conv_lhs => rw [R.as_sum]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.sum_mul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e, integral_finsetSum _ fun v _ => intg_mono2 hb l μ v _, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun v _ => ?_
    have e2 : (fun p : ℝ × ℝ => eval ![(p.1 : ℂ), (p.2 : ℂ)] (monomial v (AddMonoidAlgebra.coeff R v)) * G2 b l μ p) =
        fun p => AddMonoidAlgebra.coeff R v * (((p.1 : ℂ) ^ v 0 * cexp (b * (p.1 : ℂ) ^ 2 + l * p.1)) *
          ((p.2 : ℂ) ^ v 1 * cexp (b * (p.2 : ℂ) ^ 2 + μ * p.2))) := by
      funext p; simp only [G2, eval_monomial2]; ring
    rw [e2, integral_const_mul]
    rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl,
      integral_prod_mul (fun x : ℝ => (x : ℂ) ^ v 0 * cexp (b * (x : ℂ) ^ 2 + l * x))
        (fun y : ℝ => (y : ℂ) ^ v 1 * cexp (b * (y : ℂ) ^ 2 + μ * y))]
    have h0 := J_eq hb (v 0) l
    have h1 := J_eq hb (v 1) μ
    simp only [J] at h0 h1 ⊢
    rw [h0, h1]
    simp only [eval_mul, eval_C, eval_toMv, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    ring

end PositivityTheory.SiegelWeilFormula.KLI

end
end

noncomputable section

open MeasureTheory Complex MvPolynomial

namespace PositivityTheory.SiegelWeilFormula.KLI

theorem mer_symm (p : ℝ × ℝ) : Complex.measurableEquivRealProd.symm p = p.1 + p.2 * I := by
  rw [Complex.measurableEquivRealProd_symm_apply]
  apply Complex.ext <;> simp

def phi1 (sg : ℤˣ) (t z ξ : ℂ) (α β : ℕ) (w : ℂ) : ℂ :=
  w ^ α * star w ^ β * (cexp (2 * Real.pi * I * ((sg : ℤ) : ℂ) * z * (normSq w : ℂ)) *
    cexp (2 * Real.pi * I * ((t * (star ξ * w)).re : ℂ)))

def Rab (α β : ℕ) : MvPolynomial (Fin 2) ℂ := (X 0 + C I * X 1) ^ α * (X 0 - C I * X 1) ^ β

theorem deg_Rab (α β : ℕ) : (Rab α β).totalDegree ≤ α + β := by
  have h1 : (X 0 + C I * X 1 : MvPolynomial (Fin 2) ℂ).totalDegree ≤ 1 := by
    refine (totalDegree_add _ _).trans (max_le ?_ ?_)
    · simp only [totalDegree_X, le_refl]
    · refine (totalDegree_mul _ _).trans ?_
      simp only [totalDegree_C, totalDegree_X, zero_add, le_refl]
  have h2 : (X 0 - C I * X 1 : MvPolynomial (Fin 2) ℂ).totalDegree ≤ 1 := by
    refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
    · simp only [totalDegree_X, le_refl]
    · refine (totalDegree_mul _ _).trans ?_
      simp only [totalDegree_C, totalDegree_X, zero_add, le_refl]
  unfold PositivityTheory.SiegelWeilFormula.KLI.Rab
  refine (totalDegree_mul _ _).trans (add_le_add ?_ ?_)
  · exact (totalDegree_pow _ _).trans ((Nat.mul_le_mul le_rfl h1).trans_eq (mul_one _))
  · exact (totalDegree_pow _ _).trans ((Nat.mul_le_mul le_rfl h2).trans_eq (mul_one _))

def lamF (t ξ : ℂ) : ℂ := 2 * Real.pi * I * ((t * star ξ).re : ℂ)

def muF (t ξ : ℂ) : ℂ := -(2 * Real.pi * I * ((t * star ξ).im : ℂ))

theorem gaussian_moment_real_coords (sg : ℤˣ) (t z ξ : ℂ) (α β : ℕ) (p : ℝ × ℝ) :
    phi1 sg t z ξ α β (p.1 + p.2 * I) =
      eval ![(p.1 : ℂ), (p.2 : ℂ)] (Rab α β) *
        G2 (2 * Real.pi * I * ((sg : ℤ) : ℂ) * z) (lamF t ξ) (muF t ξ) p := by
  have hs : star ((p.1 : ℂ) + p.2 * I) = p.1 - p.2 * I := by
    apply Complex.ext <;> simp
  have hn : normSq ((p.1 : ℂ) + p.2 * I) = p.1 ^ 2 + p.2 ^ 2 := Complex.normSq_add_mul_I _ _
  have hre : (t * (star ξ * ((p.1 : ℂ) + p.2 * I))).re = p.1 * (t * star ξ).re - p.2 * (t * star ξ).im := by
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have h0 : (![(p.1 : ℂ), (p.2 : ℂ)] : Fin 2 → ℂ) 0 = p.1 := rfl
  have h1 : (![(p.1 : ℂ), (p.2 : ℂ)] : Fin 2 → ℂ) 1 = p.2 := rfl
  simp only [PositivityTheory.SiegelWeilFormula.KLI.phi1, PositivityTheory.SiegelWeilFormula.KLI.Rab, PositivityTheory.SiegelWeilFormula.KLI.G2, PositivityTheory.SiegelWeilFormula.KLI.lamF,
    PositivityTheory.SiegelWeilFormula.KLI.muF, hs, hn, hre, map_mul, map_pow, map_add, map_sub, MvPolynomial.eval_C,
    MvPolynomial.eval_X, h0, h1]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  · congr 1 <;> congr 1 <;> ring
  · congr 1
    push_cast
    ring

theorem integrable_gaussian_moment (sg : ℤˣ) (t z ξ : ℂ) (hz : 0 < ((sg : ℤ) : ℝ) * z.im) (α β : ℕ) :
    Integrable (phi1 sg t z ξ α β) := by
  have hB : (2 * Real.pi * I * ((sg : ℤ) : ℂ) * z).re < 0 := by
    have hBeq : 2 * (Real.pi : ℂ) * I * ((sg : ℤ) : ℂ) * z = ((2 * Real.pi * ((sg : ℤ) : ℝ) : ℝ) : ℂ) * (I * z) := by
      push_cast
      ring
    rw [hBeq, Complex.re_ofReal_mul, Complex.I_mul_re]
    have := mul_pos Real.pi_pos hz
    nlinarith
  have h := PositivityTheory.SiegelWeilFormula.KLI.intg_poly2 hB (PositivityTheory.SiegelWeilFormula.KLI.lamF t ξ) (PositivityTheory.SiegelWeilFormula.KLI.muF t ξ)
    (PositivityTheory.SiegelWeilFormula.KLI.Rab α β)
  rw [← (MeasurePreserving.symm Complex.measurableEquivRealProd Complex.volume_preserving_equiv_real_prod).integrable_comp_emb
    Complex.measurableEquivRealProd.symm.measurableEmbedding]
  refine h.congr (ae_of_all _ fun p => ?_)
  simp only [Function.comp_apply, PositivityTheory.SiegelWeilFormula.KLI.mer_symm,
    PositivityTheory.SiegelWeilFormula.KLI.gaussian_moment_real_coords]

theorem mom1 (sg : ℤˣ) (t : ℂ) (z : ℂ) (hz : 0 < ((sg : ℤ) : ℝ) * z.im) (α β : ℕ) :
    ∃ q : MvPolynomial Bool ℂ, q.totalDegree ≤ α + β ∧ ∀ ξ : ℂ,
      ∫ w : ℂ, phi1 sg t z ξ α β w =
        eval (fun b => if b then star ξ else ξ) q *
          cexp (2 * Real.pi * I * ((sg : ℤ) : ℂ) * (-((normSq t : ℂ) / 4) * z⁻¹) * (normSq ξ : ℂ)) := by
  have hB : (2 * Real.pi * I * ((sg : ℤ) : ℂ) * z).re < 0 := by
    have hBeq : 2 * (Real.pi : ℂ) * I * ((sg : ℤ) : ℂ) * z = ((2 * Real.pi * ((sg : ℤ) : ℝ) : ℝ) : ℂ) * (I * z) := by
      push_cast
      ring
    rw [hBeq, Complex.re_ofReal_mul, Complex.I_mul_re]
    have := mul_pos Real.pi_pos hz
    nlinarith
  have hS2 : ((sg : ℤ) : ℂ) ^ 2 = 1 := by
    rcases Int.units_eq_one_or sg with h | h <;> simp [h]
  have hs0 : ((sg : ℤ) : ℂ) ≠ 0 := by
    intro h
    rw [h] at hS2
    norm_num at hS2
  have hS : ((sg : ℤ) : ℂ) * ((sg : ℤ) : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hs0
  have hP : (Real.pi : ℂ) * (Real.pi : ℂ)⁻¹ = 1 := mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hQ : I * I⁻¹ = 1 := mul_inv_cancel₀ Complex.I_ne_zero
  obtain ⟨R, hRdeg, hR⟩ := PositivityTheory.SiegelWeilFormula.KLI.mom2 hB (PositivityTheory.SiegelWeilFormula.KLI.Rab α β)
  obtain ⟨F, hF0, hF1⟩ : ∃ F : Fin 2 → MvPolynomial Bool ℂ,
      F 0 = C (2 * (Real.pi : ℂ) * I / 2) * (C t * X true + C (star t) * X false) ∧
      F 1 = C (-(2 * (Real.pi : ℂ) * I) / (2 * I)) * (C t * X true - C (star t) * X false) :=
    ⟨![C (2 * (Real.pi : ℂ) * I / 2) * (C t * X true + C (star t) * X false),
      C (-(2 * (Real.pi : ℂ) * I) / (2 * I)) * (C t * X true - C (star t) * X false)], rfl, rfl⟩
  have hF : ∀ i, (F i).totalDegree ≤ 1 := by
    refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
    · rw [hF0]
      refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_C, zero_add]
      refine (totalDegree_add _ _).trans (max_le ?_ ?_) <;>
        refine (totalDegree_mul _ _).trans ?_ <;>
        simp only [totalDegree_C, totalDegree_X, zero_add, le_refl]
    · rw [hF1]
      refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_C, zero_add]
      refine (totalDegree_sub _ _).trans (max_le ?_ ?_) <;>
        refine (totalDegree_mul _ _).trans ?_ <;>
        simp only [totalDegree_C, totalDegree_X, zero_add, le_refl]
  refine ⟨C (((Real.pi : ℂ) / -(2 * Real.pi * I * ((sg : ℤ) : ℂ) * z)) ^ (1 / 2 : ℂ) *
      ((Real.pi : ℂ) / -(2 * Real.pi * I * ((sg : ℤ) : ℂ) * z)) ^ (1 / 2 : ℂ)) * bind₁ F R, ?_, fun ξ => ?_⟩
  · refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    exact ((PositivityTheory.SiegelWeilFormula.KLI.deg_bind_le F hF R).trans hRdeg).trans
      (PositivityTheory.SiegelWeilFormula.KLI.deg_Rab α β)
  · have hfun : (fun i => eval (fun b : Bool => if b then star ξ else ξ) (F i)) =
        ![PositivityTheory.SiegelWeilFormula.KLI.lamF t ξ, PositivityTheory.SiegelWeilFormula.KLI.muF t ξ] := by
      refine funext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
      · show eval (fun b : Bool => if b then star ξ else ξ) (F 0) = PositivityTheory.SiegelWeilFormula.KLI.lamF t ξ
        rw [hF0]
        simp only [map_mul, map_add (f := _), MvPolynomial.eval_C, MvPolynomial.eval_X, PositivityTheory.SiegelWeilFormula.KLI.lamF,
          Complex.re_eq_add_conj, Complex.star_def, Complex.conj_conj, ↓reduceIte, Bool.false_eq_true]
        ring
      · show eval (fun b : Bool => if b then star ξ else ξ) (F 1) = PositivityTheory.SiegelWeilFormula.KLI.muF t ξ
        rw [hF1]
        simp only [map_mul, map_sub, MvPolynomial.eval_C, MvPolynomial.eval_X, PositivityTheory.SiegelWeilFormula.KLI.muF,
          Complex.im_eq_sub_conj, Complex.star_def, Complex.conj_conj, ↓reduceIte, Bool.false_eq_true]
        ring
    have heval : eval (fun b : Bool => if b then star ξ else ξ) (bind₁ F R) =
        eval ![PositivityTheory.SiegelWeilFormula.KLI.lamF t ξ, PositivityTheory.SiegelWeilFormula.KLI.muF t ξ] R := by
      rw [← hfun]
      exact MvPolynomial.eval₂Hom_bind₁ (RingHom.id ℂ) (fun b : Bool => if b then star ξ else ξ) F R
    have hn : (((t * star ξ).re : ℝ) : ℂ) ^ 2 + (((t * star ξ).im : ℝ) : ℂ) ^ 2 =
        (normSq t : ℂ) * (normSq ξ : ℂ) := by
      have h2 : normSq (star ξ) = normSq ξ := by rw [Complex.star_def, Complex.normSq_conj]
      have h1 : (t * star ξ).re ^ 2 + (t * star ξ).im ^ 2 = normSq t * normSq ξ := by
        rw [← h2, ← Complex.normSq_mul, Complex.normSq_apply]
        ring
      exact_mod_cast h1
    have hexp : -(PositivityTheory.SiegelWeilFormula.KLI.lamF t ξ ^ 2 / (4 * (2 * Real.pi * I * ((sg : ℤ) : ℂ) * z))) +
        -(PositivityTheory.SiegelWeilFormula.KLI.muF t ξ ^ 2 / (4 * (2 * Real.pi * I * ((sg : ℤ) : ℂ) * z))) =
        2 * Real.pi * I * ((sg : ℤ) : ℂ) * (-((normSq t : ℂ) / 4) * z⁻¹) * (normSq ξ : ℂ) := by
      unfold PositivityTheory.SiegelWeilFormula.KLI.lamF PositivityTheory.SiegelWeilFormula.KLI.muF
      linear_combination
        (-(1 / 2) * ((Real.pi : ℂ) * I * ((sg : ℤ) : ℂ)⁻¹ * z⁻¹ *
            ((((t * star ξ).re : ℝ) : ℂ) ^ 2 + (((t * star ξ).im : ℝ) : ℂ) ^ 2)) * I * I⁻¹) * hP +
        (-(1 / 2) * ((Real.pi : ℂ) * I * ((sg : ℤ) : ℂ)⁻¹ * z⁻¹ *
            ((((t * star ξ).re : ℝ) : ℂ) ^ 2 + (((t * star ξ).im : ℝ) : ℂ) ^ 2))) * hQ +
        (-(1 / 2) * (Real.pi : ℂ) * I * ((sg : ℤ) : ℂ)⁻¹ * z⁻¹) * hn +
        ((1 / 2) * (Real.pi : ℂ) * I * z⁻¹ * ((normSq t : ℂ) * (normSq ξ : ℂ)) * ((sg : ℤ) : ℂ)⁻¹) * hS2 +
        (-(1 / 2) * (Real.pi : ℂ) * I * z⁻¹ * ((normSq t : ℂ) * (normSq ξ : ℂ)) * ((sg : ℤ) : ℂ)) * hS
    have hchg : ∫ w : ℂ, PositivityTheory.SiegelWeilFormula.KLI.phi1 sg t z ξ α β w =
        ∫ p : ℝ × ℝ, PositivityTheory.SiegelWeilFormula.KLI.phi1 sg t z ξ α β (Complex.measurableEquivRealProd.symm p) :=
      ((MeasurePreserving.symm Complex.measurableEquivRealProd Complex.volume_preserving_equiv_real_prod).integral_comp
        Complex.measurableEquivRealProd.symm.measurableEmbedding _).symm
    rw [hchg]
    simp only [PositivityTheory.SiegelWeilFormula.KLI.mer_symm, PositivityTheory.SiegelWeilFormula.KLI.gaussian_moment_real_coords]
    rw [hR, PositivityTheory.SiegelWeilFormula.KLI.J_zero hB, PositivityTheory.SiegelWeilFormula.KLI.J_zero hB, map_mul,
      MvPolynomial.eval_C, heval, ← hexp, Complex.exp_add]
    ring

end PositivityTheory.SiegelWeilFormula.KLI

end
end

noncomputable section

open scoped Matrix
open MeasureTheory PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula

namespace PositivityTheory.SiegelWeilFormula.KLI

variable {m n : ℕ}

open Complex MvPolynomial

theorem evX_monomial (e : Fin m × Fin n × Bool →₀ ℕ) (c : ℂ) (v : Fin m → Fin n → ℂ) :
    evX (monomial e c) v = c * ∏ a, ∏ j, (v a j ^ e (a, j, false) * star (v a j) ^ e (a, j, true)) := by
  simp only [evX, MvPolynomial.eval_monomial]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_prod_type]
  refine congrArg _ (Finset.prod_congr rfl fun a _ => ?_)
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Fintype.prod_bool]
  simp only [if_true, Bool.false_eq_true, if_false]
  ring

theorem gZ_diag (sg : ℤˣ) (w : Fin n → ℂ) (v : Fin m → Fin n → ℂ) :
    gZ sg (Matrix.diagonal w) v =
      ∏ a, ∏ j, cexp (2 * Real.pi * I * ((sg : ℤ) : ℂ) * w j * (normSq (v a j) : ℂ)) := by
  unfold gZ
  have h : (Matrix.diagonal w * ((Matrix.of v)ᴴ * Matrix.of v)).trace =
      ∑ a, ∑ j, w j * (normSq (v a j) : ℂ) := by
    simp only [Matrix.trace, Matrix.diag]
    simp only [Matrix.diagonal_mul]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.normSq_eq_conj_mul_self]
    rfl
  rw [h, Finset.mul_sum, Complex.exp_sum]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [Finset.mul_sum, Complex.exp_sum]
  refine Finset.prod_congr rfl fun j _ => ?_
  congr 1
  ring

def ker (t : ℂ) (u v : Fin m → Fin n → ℂ) : ℂ :=
  cexp (2 * Real.pi * I * ((t * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re : ℂ))

theorem ker_prod (t : ℂ) (u v : Fin m → Fin n → ℂ) :
    ker t u v = ∏ a, ∏ j, cexp (2 * Real.pi * I * ((t * (star (u a j) * v a j)).re : ℂ)) := by
  unfold ker
  have h : t * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v) =
      ∑ a, ∑ j, t * (star (u a j) * v a j) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.of_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [h, Complex.re_sum, Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [Complex.re_sum, Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum]

theorem integrand_mono (sg : ℤˣ) (t : ℂ) (z : Fin n → ℂ) (e : Fin m × Fin n × Bool →₀ ℕ) (c : ℂ)
    (u v : Fin m → Fin n → ℂ) :
    ker t u v * (evX (monomial e c) v * gZ sg (Matrix.diagonal z) v) =
      c * ∏ a, ∏ j, phi1 sg t (z j) (u a j) (e (a, j, false)) (e (a, j, true)) (v a j) := by
  rw [ker_prod, evX_monomial, gZ_diag]
  simp only [phi1, Finset.prod_mul_distrib]
  ring

theorem intg_mono (sg : ℤˣ) (t : ℂ) (z : Fin n → ℂ) (hz : ∀ j, 0 < ((sg : ℤ) : ℝ) * (z j).im)
    (e : Fin m × Fin n × Bool →₀ ℕ) (c : ℂ) (u : Fin m → Fin n → ℂ) :
    Integrable (fun v : Fin m → Fin n → ℂ => ker t u v * (evX (monomial e c) v * gZ sg (Matrix.diagonal z) v)) := by
  have h : (fun v : Fin m → Fin n → ℂ => ker t u v * (evX (monomial e c) v * gZ sg (Matrix.diagonal z) v)) =
      fun v => c * ∏ a, ∏ j, phi1 sg t (z j) (u a j) (e (a, j, false)) (e (a, j, true)) (v a j) :=
    funext fun v => integrand_mono sg t z e c u v
  rw [h]
  refine Integrable.const_mul ?_ c
  exact Integrable.fintype_prod
    (f := fun a (w : Fin n → ℂ) => ∏ j, phi1 sg t (z j) (u a j) (e (a, j, false)) (e (a, j, true)) (w j))
    fun a => Integrable.fintype_prod
      (f := fun j w => phi1 sg t (z j) (u a j) (e (a, j, false)) (e (a, j, true)) w)
      fun j => integrable_gaussian_moment sg t (z j) (u a j) (hz j) _ _

def rn (a : Fin m) (j : Fin n) (q : MvPolynomial Bool ℂ) : PX m n := rename (fun b => (a, j, b)) q

theorem four_mono (sg : ℤˣ) (t : ℂ) (z : Fin n → ℂ) (hz : ∀ j, 0 < ((sg : ℤ) : ℝ) * (z j).im)
    (e : Fin m × Fin n × Bool →₀ ℕ) (c : ℂ) :
    ∃ Q : PX m n, Q.totalDegree ≤ e.sum (fun _ k => k) ∧ ∀ u, ∫ v : Fin m → Fin n → ℂ,
      ker t u v * (evX (monomial e c) v * gZ sg (Matrix.diagonal z) v) =
      evX Q u * gZ sg (Matrix.diagonal fun j => -((normSq t : ℂ) / 4) * (z j)⁻¹) u := by
  choose q hqd hq using fun (a : Fin m) (j : Fin n) =>
    mom1 sg t (z j) (hz j) (e (a, j, false)) (e (a, j, true))
  refine ⟨MvPolynomial.C c * ∏ a, ∏ j, rn a j (q a j), ?_, fun u => ?_⟩
  · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, zero_add]
    refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fintype.sum_prod_type]
    refine Finset.sum_le_sum fun a _ => ?_
    refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [Fintype.sum_bool]
    exact ((MvPolynomial.totalDegree_rename_le _ _).trans (hqd a j)).trans (le_of_eq (add_comm _ _))
  · have h : (fun v : Fin m → Fin n → ℂ => ker t u v * (evX (monomial e c) v * gZ sg (Matrix.diagonal z) v)) =
        fun v => c * ∏ a, ∏ j, phi1 sg t (z j) (u a j) (e (a, j, false)) (e (a, j, true)) (v a j) :=
      funext fun v => integrand_mono sg t z e c u v
    have hin : ∀ a, ∫ w : Fin n → ℂ, ∏ j, phi1 sg t (z j) (u a j) (e (a, j, false)) (e (a, j, true)) (w j) =
        ∏ j, ((MvPolynomial.eval fun b : Bool => if b = true then star (u a j) else u a j) (q a j) *
          cexp (2 * Real.pi * I * ((sg : ℤ) : ℂ) * (-((normSq t : ℂ) / 4) * (z j)⁻¹) * (normSq (u a j) : ℂ))) := by
      intro a
      rw [integral_fintype_prod_volume_eq_prod
        (fun j w => phi1 sg t (z j) (u a j) (e (a, j, false)) (e (a, j, true)) w)]
      exact Finset.prod_congr rfl fun j _ => hq a j (u a j)
    rw [h, integral_const_mul, integral_fintype_prod_volume_eq_prod
      (fun a (w : Fin n → ℂ) => ∏ j, phi1 sg t (z j) (u a j) (e (a, j, false)) (e (a, j, true)) (w j))]
    simp only [hin, gZ_diag]
    simp only [evX, map_mul, map_prod, MvPolynomial.eval_C, rn, MvPolynomial.eval_rename,
      Function.comp_def, Finset.prod_mul_distrib]
    ring

end PositivityTheory.SiegelWeilFormula.KLI

end
end

noncomputable section

open scoped Matrix
open MeasureTheory PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula

namespace PositivityTheory.SiegelWeilFormula.KLI

variable {m n : ℕ}

open Complex MvPolynomial

theorem isPG_smul {sg : ℤˣ} {d : ℕ} {Z : Matrix (Fin n) (Fin n) ℂ} {f : (Fin m → Fin n → ℂ) → ℂ} (c : ℂ)
    (h : IsPG sg d Z f) : IsPG sg d Z (fun u => c * f u) := by
  obtain ⟨Q, hQ, rfl⟩ := h
  refine ⟨MvPolynomial.C c * Q, ?_, ?_⟩
  · exact (MvPolynomial.totalDegree_mul _ _).trans (by simp [hQ])
  · funext u
    simp only [evX, map_mul, MvPolynomial.eval_C]
    ring

theorem four_diag (sg : ℤˣ) (t : ℂ) (z : Fin n → ℂ) (hz : ∀ j, 0 < ((sg : ℤ) : ℝ) * (z j).im)
    (d : ℕ) (Q : PX m n) (hQ : Q.totalDegree ≤ d) :
    IsPG sg d (Matrix.diagonal fun j => -((normSq t : ℂ) / 4) * (z j)⁻¹)
      (fun u => ∫ v : Fin m → Fin n → ℂ, ker t u v * (evX Q v * gZ sg (Matrix.diagonal z) v)) := by
  classical
  have key : ∀ e ∈ Q.support, ∃ Q' : PX m n, Q'.totalDegree ≤ d ∧ ∀ u,
      ∫ v : Fin m → Fin n → ℂ, ker t u v * (evX (MvPolynomial.monomial e (Q.coeff e)) v * gZ sg (Matrix.diagonal z) v)
        = evX Q' u * gZ sg (Matrix.diagonal fun j => -((normSq t : ℂ) / 4) * (z j)⁻¹) u := by
    intro e he
    obtain ⟨Q', hQ', h'⟩ := four_mono sg t z hz e (Q.coeff e)
    exact ⟨Q', hQ'.trans ((MvPolynomial.le_totalDegree he).trans hQ), h'⟩
  choose! F hFd hF using key
  refine ⟨∑ e ∈ Q.support, F e, ?_, ?_⟩
  · exact (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun e he => hFd e he)
  · funext u
    have hsplit : ∀ v, ker t u v * (evX Q v * gZ sg (Matrix.diagonal z) v)
        = ∑ e ∈ Q.support, ker t u v * (evX (MvPolynomial.monomial e (Q.coeff e)) v * gZ sg (Matrix.diagonal z) v) := by
      intro v
      conv_lhs => rw [Q.as_sum]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [evX, map_sum, Finset.sum_mul, Finset.mul_sum]
    simp_rw [hsplit]
    rw [integral_finsetSum _ (fun e _ => intg_mono sg t z hz e (Q.coeff e) u)]
    rw [Finset.sum_congr rfl (fun e he => hF e he u)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [evX, map_sum, Finset.sum_mul]

theorem pg_four (sg : ℤˣ) (t C0 : ℂ) (z : Fin n → ℂ) (hz : ∀ j, 0 < ((sg : ℤ) : ℝ) * (z j).im) {d : ℕ}
    {f : (Fin m → Fin n → ℂ) → ℂ} (hp : IsPG sg d (Matrix.diagonal z) f) :
    IsPG sg d (Matrix.diagonal fun j => -((normSq t : ℂ) / 4) * (z j)⁻¹)
      (fun u => C0 * ∫ v : Fin m → Fin n → ℂ, ker t u v * f v) := by
  obtain ⟨Q, hQ, rfl⟩ := hp
  exact isPG_smul C0 (four_diag sg t z hz d Q hQ)

theorem evX_mulR (Q : PX m n) (a : Matrix (Fin n) (Fin n) ℂ) :
    ∃ Q' : PX m n, Q'.totalDegree ≤ Q.totalDegree ∧ ∀ u : Fin m → Fin n → ℂ, evX Q (Matrix.of u * a) = evX Q' u := by
  classical
  let f : Fin m × Fin n × Bool → PX m n := fun k =>
    if k.2.2 = true then ∑ l, MvPolynomial.X (k.1, l, true) * MvPolynomial.C (star (a l k.2.1))
    else ∑ l, MvPolynomial.X (k.1, l, false) * MvPolynomial.C (a l k.2.1)
  refine ⟨MvPolynomial.bind₁ f Q, deg_bind_le f (fun k => ?_) Q, fun u => ?_⟩
  · dsimp only [f]
    split_ifs <;>
    · refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun l _ => ?_)
      refine (MvPolynomial.totalDegree_mul _ _).trans ?_
      simp [MvPolynomial.totalDegree_X]
  · unfold evX
    change _ = MvPolynomial.eval₂Hom (RingHom.id ℂ) _ (MvPolynomial.bind₁ f Q)
    rw [MvPolynomial.eval₂Hom_bind₁]
    change MvPolynomial.eval₂Hom (RingHom.id ℂ) _ Q = MvPolynomial.eval₂Hom (RingHom.id ℂ) _ Q
    refine congrArg (fun g => MvPolynomial.eval₂Hom (RingHom.id ℂ) g Q) ?_
    funext k
    obtain ⟨i, j, b⟩ := k
    cases b <;> simp [f, Matrix.mul_apply, star_sum, star_mul']

theorem gZ_mulR (sg : ℤˣ) (Z a : Matrix (Fin n) (Fin n) ℂ) (u : Fin m → Fin n → ℂ) :
    gZ sg Z (Matrix.of u * a) = gZ sg (a * Z * aᴴ) u := by
  unfold gZ
  have e : (Z * ((Matrix.of (Matrix.of u * a))ᴴ * Matrix.of (Matrix.of u * a))).trace
      = (a * Z * aᴴ * ((Matrix.of u)ᴴ * Matrix.of u)).trace := by
    change (Z * ((Matrix.of u * a)ᴴ * (Matrix.of u * a))).trace = _
    rw [Matrix.conjTranspose_mul]
    rw [show Z * (aᴴ * (Matrix.of u)ᴴ * (Matrix.of u * a))
        = (Z * aᴴ * ((Matrix.of u)ᴴ * Matrix.of u)) * a by simp only [Matrix.mul_assoc]]
    rw [Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [e]

variable {sg : ℤˣ} {L : LOp m n}

theorem pg_nG (h : LocHyp sg L) {b : Matrix (Fin n) (Fin n) ℂ} (hb : bᴴ = b) {d : ℕ} {Z : Matrix (Fin n) (Fin n) ℂ}
    {f : (Fin m → Fin n → ℂ) → ℂ} (hf : IsSw f) (hp : IsPG sg d Z f) :
    IsPG sg d (mob (mR (nG b)) Z) (L (nG b) f) := by
  rw [mR_nG hb, mob_nU, h.nU _ b hb (mR_nG hb) f hf]
  obtain ⟨Q, hQ, rfl⟩ := hp
  refine ⟨Q, hQ, ?_⟩
  funext u
  simp only [gZ, Matrix.add_mul, Matrix.trace_add, mul_add, Complex.exp_add]
  ring

theorem pg_mG (h : LocHyp sg L) {a : Matrix (Fin n) (Fin n) ℂ} (ha : IsUnit a.det) {d : ℕ}
    {Z : Matrix (Fin n) (Fin n) ℂ} {f : (Fin m → Fin n → ℂ) → ℂ} (hf : IsSw f) (hp : IsPG sg d Z f) :
    IsPG sg d (mob (mR (mG a)) Z) (L (mG a) f) := by
  obtain ⟨k, hk⟩ := h.mM
  rw [hk (mG a) a ha (mR_mG ha) f hf, mR_mG ha, mob_mLc _ _ ha]
  obtain ⟨Q, hQ, rfl⟩ := hp
  obtain ⟨Q', hQ', hQ'e⟩ := evX_mulR Q a
  refine ⟨MvPolynomial.C ((a.det / ↑‖a.det‖) ^ k * ↑‖a.det‖ ^ m) * Q', ?_, ?_⟩
  · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, zero_add]
    exact hQ'.trans hQ
  · funext u
    show _ * (evX Q (Matrix.of u * a) * gZ sg Z (Matrix.of u * a)) = _
    rw [hQ'e, gZ_mulR]
    simp only [evX, map_mul, MvPolynomial.eval_C]
    ring

theorem isPG_smul' {sg : ℤˣ} {d : ℕ} {Z : Matrix (Fin n) (Fin n) ℂ} {f : (Fin m → Fin n → ℂ) → ℂ} (c : ℂ)
    (h : IsPG sg d Z f) : IsPG sg d Z (c • f) := isPG_smul c h

theorem pg_lFT {sg : ℤˣ} (C s : ℂ) (hs : ‖s‖ = 2) {z : Fin n → ℂ} (hz : ∀ j, 0 < ((sg : ℤ) : ℝ) * (z j).im) {d : ℕ}
    {f : (Fin m → Fin n → ℂ) → ℂ} (hp : IsPG sg d (Matrix.diagonal z) f) :
    IsPG sg d (Matrix.diagonal fun j => -(z j)⁻¹) (lFT C s f) := by
  have e : lFT C s f = fun u => C * ∫ v : Fin m → Fin n → ℂ, ker s u v * f v := rfl
  have hn : (normSq s : ℂ) / 4 = 1 := by
    rw [Complex.normSq_eq_norm_sq, hs]
    norm_num
  have := pg_four sg s C z hz hp
  rw [e]
  simpa [hn] using this

theorem pg_chp {sg : ℤˣ} (x : Matrix (Fin n) (Fin n) ℂ) {d : ℕ} {Z : Matrix (Fin n) (Fin n) ℂ}
    {f : (Fin m → Fin n → ℂ) → ℂ} (hp : IsPG sg d Z f) : IsPG sg d (Z + x) (chp ((sg : ℤ) : ℂ) x f) := by
  obtain ⟨Q, hQ, rfl⟩ := hp
  refine ⟨Q, hQ, ?_⟩
  funext u
  simp only [chp, gZ, Matrix.add_mul, Matrix.trace_add, mul_add, Complex.exp_add]
  ring

theorem im_neg_inv {sg : ℤˣ} {w : ℂ} (hw : 0 < ((sg : ℤ) : ℝ) * w.im) : 0 < ((sg : ℤ) : ℝ) * (-w⁻¹).im := by
  have hw0 : w ≠ 0 := by
    rintro rfl
    simp at hw
  have hn : 0 < Complex.normSq w := Complex.normSq_pos.mpr hw0
  have e : (-w⁻¹).im = w.im / Complex.normSq w := by
    simp [Complex.inv_im, neg_div]
  rw [e, ← mul_div_assoc]
  exact div_pos hw hn

theorem diag_add_one (w : Fin n → ℂ) : Matrix.diagonal w + 1 = Matrix.diagonal fun j => w j + 1 := by
  rw [← Matrix.diagonal_one, Matrix.diagonal_add]

theorem inG_nbLc {c : Matrix (Fin n) (Fin n) ℂ} (hc : cᴴ = c) : InG (nbLc c) := by
  exact inG_nb hc

def nbH (c : Matrix (Fin n) (Fin n) ℂ) : GR n := if h : cᴴ = c then toGR _ (inG_nbLc h) else 1

theorem mR_nbH {c : Matrix (Fin n) (Fin n) ℂ} (hc : cᴴ = c) : mR (nbH c) = nbLc c := by
  rw [nbH, dite_eq_left hc, mR_toGR]

theorem jG_eq : jG n = nG 1 * nbH (-1) * nG 1 := by
  apply mR_injective
  have h1 : (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ = 1 := Matrix.conjTranspose_one
  have hm1 : (-1 : Matrix (Fin n) (Fin n) ℂ)ᴴ = -1 := by simp
  rw [mR_mul, mR_mul, mR_nG h1, mR_nbH hm1, mR_jG]
  simp [JJ, nU, nbLc, Matrix.fromBlocks_multiply]

theorem alg1 (x : ℂ) (hx : x ≠ 0) (hx1 : x + 1 ≠ 0) : (-x)⁻¹ = -(-(-(-(x + 1)⁻¹ + 1)⁻¹)⁻¹)⁻¹ + 1 := by
  have hy : -(x + 1)⁻¹ + 1 = x / (x + 1) := by field_simp; ring
  rw [hy]
  simp only [inv_neg, inv_inv, neg_neg, inv_div]
  field_simp
  ring

theorem pg_jG_diag (h : LocHyp sg L) {d : ℕ} {z : Fin n → ℂ} (hz : ∀ j, 0 < ((sg : ℤ) : ℝ) * (z j).im)
    {f : (Fin m → Fin n → ℂ) → ℂ} (hf : IsSw f) (hp : IsPG sg d (Matrix.diagonal z) f) :
    IsPG sg d (mob (mR (jG n)) (Matrix.diagonal z)) (L (jG n) f) := by
  have hz0 : ∀ j, z j ≠ 0 := fun j hj => by
    have := hz j
    rw [hj] at this
    simp at this
  have hz1' : ∀ j, 0 < ((sg : ℤ) : ℝ) * (z j + 1).im := fun j => by
    rw [Complex.add_im, Complex.one_im, add_zero]
    exact hz j
  have hz1 : ∀ j, z j + 1 ≠ 0 := fun j hj => by
    have := hz1' j
    rw [hj] at this
    simp at this
  obtain ⟨C, s, κ, η, -, -, hs, hη, -, hnb⟩ := h.nbar
  have h1 : (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ = 1 := Matrix.conjTranspose_one
  have hm1 : (-1 : Matrix (Fin n) (Fin n) ℂ)ᴴ = -1 := by simp
  have hf1 : IsSw (L (nG 1) f) := h.sw _ _ hf
  have hf2 : IsSw (L (nbH (-1)) (L (nG 1) f)) := h.sw _ _ hf1
  have hL : L (jG n) f = L (nG 1) (L (nbH (-1)) (L (nG 1) f)) := by
    rw [jG_eq, h.mul _ _ _ hf, h.mul _ _ _ hf1]
  rw [hL, mR_jG, mob_JJ_diag z hz0]
  have p1 : IsPG sg d (Matrix.diagonal fun j => z j + 1) (L (nG 1) f) := by
    have := pg_nG h h1 hf hp
    rwa [mR_nG h1, mob_nU, diag_add_one] at this
  have p2 : IsPG sg d (Matrix.diagonal fun j => -(z j + 1)⁻¹) (lFT C s (L (nG 1) f)) :=
    pg_lFT C s hs hz1' p1
  have e1 : Matrix.diagonal (fun j => -(z j + 1)⁻¹) + η • (-1 : Matrix (Fin n) (Fin n) ℂ)
      = Matrix.diagonal fun j => -(z j + 1)⁻¹ + 1 := by
    rw [hη, neg_smul, one_smul, neg_neg, diag_add_one]
  have p3 : IsPG sg d (Matrix.diagonal fun j => -(z j + 1)⁻¹ + 1)
      (chp ((sg : ℤ) : ℂ) (η • (-1 : Matrix (Fin n) (Fin n) ℂ)) (lFT C s (L (nG 1) f))) := by
    have := pg_chp (η • (-1 : Matrix (Fin n) (Fin n) ℂ)) p2
    rw [e1] at this
    exact this
  have hz2 : ∀ j, 0 < ((sg : ℤ) : ℝ) * (-(z j + 1)⁻¹ + 1).im := fun j => by
    rw [Complex.add_im, Complex.one_im, add_zero]
    exact im_neg_inv (hz1' j)
  have p4 := pg_lFT C s hs hz2 p3
  have hz3 : ∀ j, 0 < ((sg : ℤ) : ℝ) * (-(-(z j + 1)⁻¹ + 1)⁻¹).im := fun j => im_neg_inv (hz2 j)
  have p5 := pg_lFT C s hs hz3 p4
  have hz4 : ∀ j, 0 < ((sg : ℤ) : ℝ) * (-(-(-(z j + 1)⁻¹ + 1)⁻¹)⁻¹).im := fun j => im_neg_inv (hz3 j)
  have p6 := pg_lFT C s hs hz4 p5
  have p7 := isPG_smul' κ⁻¹ p6
  rw [← hnb (nbH (-1)) (-1) hm1 (mR_nbH hm1) _ hf1] at p7
  have p8 := pg_nG h h1 hf2 p7
  rw [mR_nG h1, mob_nU, diag_add_one] at p8
  have e : (fun j => (-z j)⁻¹) = fun j => -(-(-(-(z j + 1)⁻¹ + 1)⁻¹)⁻¹)⁻¹ + 1 :=
    funext fun j => alg1 _ (hz0 j) (hz1 j)
  rw [e]
  exact p8

theorem unit_det_of_unitary {U : Matrix (Fin n) (Fin n) ℂ} (hU : Uᴴ * U = 1) : IsUnit U.det :=
  Matrix.isUnit_det_of_left_inverse hU

theorem jG_conj {U : Matrix (Fin n) (Fin n) ℂ} (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1) :
    jG n = mG U * jG n * mG Uᴴ := by
  have h1 : IsUnit U.det := unit_det_of_unitary hU
  have h2 : IsUnit (Uᴴ).det := unit_det_of_unitary (by rw [Matrix.conjTranspose_conjTranspose]; exact hU')
  apply mR_injective
  rw [mR_mul, mR_mul, mR_mG h1, mR_mG h2, mR_jG]
  have e1 : (Uᴴ)⁻¹ = U := Matrix.inv_eq_left_inv hU'
  have e2 : (Uᴴᴴ)⁻¹ = Uᴴ := by rw [Matrix.conjTranspose_conjTranspose]; exact Matrix.inv_eq_left_inv hU
  simp only [mLc, JJ, e1, e2, Matrix.fromBlocks_multiply]
  simp [hU', hU]

theorem mob_JJ_conj {Z U : Matrix (Fin n) (Fin n) ℂ} {z : Fin n → ℂ} (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1)
    (hZ : Uᴴ * Z * U = Matrix.diagonal z) (hz0 : ∀ j, z j ≠ 0) :
    mob (JJ n) Z = U * (Matrix.diagonal fun j => (-z j)⁻¹) * Uᴴ := by
  have hZ' : Z = U * Matrix.diagonal z * Uᴴ := by
    rw [← hZ, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hU', Matrix.one_mul, Matrix.mul_assoc, hU', Matrix.mul_one]
  have hmob : mob (JJ n) Z = (-Z)⁻¹ := by
    simp [mob, JJ]
  rw [hmob]
  apply Matrix.inv_eq_right_inv
  rw [hZ']
  have e2 : U * Matrix.diagonal z * Uᴴ * (U * Matrix.diagonal (fun j => (-z j)⁻¹) * Uᴴ)
      = U * (Matrix.diagonal z * Matrix.diagonal (fun j => (-z j)⁻¹)) * Uᴴ := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᴴ U, hU, Matrix.one_mul]
  have hd : (fun j => z j * (-z j)⁻¹) = fun _ => (-1 : ℂ) := by
    funext j
    rw [inv_neg, mul_neg, mul_inv_cancel₀ (hz0 j)]
  have hd1 : Matrix.diagonal (fun _ : Fin n => (-1 : ℂ)) = -1 := by
    rw [← Matrix.diagonal_neg]
    rfl
  rw [Matrix.neg_mul, e2, Matrix.diagonal_mul_diagonal, hd, hd1]
  simp [hU']

theorem pg_jG (h : LocHyp sg L) {d : ℕ} {Z U : Matrix (Fin n) (Fin n) ℂ} {z : Fin n → ℂ} (hU : Uᴴ * U = 1)
    (hU' : U * Uᴴ = 1) (hZ : Uᴴ * Z * U = Matrix.diagonal z) (hz : ∀ j, 0 < ((sg : ℤ) : ℝ) * (z j).im)
    {f : (Fin m → Fin n → ℂ) → ℂ} (hf : IsSw f) (hp : IsPG sg d Z f) :
    IsPG sg d (mob (mR (jG n)) Z) (L (jG n) f) := by
  have hUd : IsUnit U.det := unit_det_of_unitary hU
  have hUd' : IsUnit Uᴴ.det := unit_det_of_unitary (by rw [Matrix.conjTranspose_conjTranspose]; exact hU')
  have hz0 : ∀ j, z j ≠ 0 := fun j hj => by
    have := hz j
    rw [hj] at this
    simp at this
  rw [mR_jG, mob_JJ_conj hU hU' hZ hz0]
  have hL : L (jG n) f = L (mG U) (L (jG n) (L (mG Uᴴ) f)) := by
    conv_lhs => rw [jG_conj hU hU']
    rw [h.mul _ _ _ hf, h.mul _ _ _ (h.sw _ _ hf)]
  rw [hL]
  have p1 : IsPG sg d (Matrix.diagonal z) (L (mG Uᴴ) f) := by
    have := pg_mG h hUd' hf hp
    rwa [mR_mG hUd', mob_mLc _ _ hUd', Matrix.conjTranspose_conjTranspose, hZ] at this
  have hf1 : IsSw (L (mG Uᴴ) f) := h.sw _ _ hf
  have p2 := pg_jG_diag h hz hf1 p1
  rw [mR_jG, mob_JJ_diag z hz0] at p2
  have p3 := pg_mG h hUd (h.sw _ _ hf1) p2
  rwa [mR_mG hUd, mob_mLc _ _ hUd] at p3

end PositivityTheory.SiegelWeilFormula.KLI

end
