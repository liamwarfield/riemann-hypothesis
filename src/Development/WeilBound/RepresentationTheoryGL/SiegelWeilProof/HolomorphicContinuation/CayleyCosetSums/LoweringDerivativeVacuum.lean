module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.MultiplicityOneTestOperatorsAlt
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.NormDetFirstBlockCompact
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.ContDiffOnSecondCayleyBlockEntries
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.IILeft

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.ContDiffOnInverseFirstBlock
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.InverseFirstBlockEqConjTranspose
noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.HSt.LoweringDerivative

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt

variable {n : ℕ}

theorem JJ_sq : JJ n * JJ n = -1 := by
  simp only [JJ, fromBlocks_multiply]
  rw [← fromBlocks_one, fromBlocks_neg]
  simp

theorem inv_of_inG {x : M2 n} (hx : InG x) : x⁻¹ = -(JJ n * xᴴ * JJ n) := by
  refine Matrix.inv_eq_left_inv ?_
  have h : xᴴ * JJ n * x = JJ n := hx
  calc -(JJ n * xᴴ * JJ n) * x = -(JJ n * (xᴴ * JJ n * x)) := by noncomm_ring
    _ = 1 := by rw [h, JJ_sq]; simp

theorem isUnit_of_inG {x : M2 n} (hx : InG x) : IsUnit x := by
  have h : (-(JJ n * xᴴ * JJ n)) * x = 1 := by
    have h : xᴴ * JJ n * x = JJ n := hx
    calc -(JJ n * xᴴ * JJ n) * x = -(JJ n * (xᴴ * JJ n * x)) := by noncomm_ring
      _ = 1 := by rw [h, JJ_sq]; simp
  exact (Matrix.isUnit_iff_isUnit_det x).mpr (Matrix.isUnit_det_of_left_inverse h)

theorem isUnit_det_of_inG {x : M2 n} (hx : InG x) : IsUnit x.det :=
  (Matrix.isUnit_iff_isUnit_det x).mp (isUnit_of_inG hx)

theorem inverse_first_block_eq_conjTranspose {x : M2 n} (hx : InG x) : ub1 x = (u1 x)ᴴ := by
  rw [ub1, inv_of_inG hx, u1]
  conv_lhs => rw [← fromBlocks_toBlocks x]
  simp only [JJ, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_neg, toBlocks_fromBlocks₁₁,
    toBlocks_fromBlocks₂₁]
  simp [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, sub_eq_add_neg]
  abel

theorem det_first_block_ne_zero_group {x : M2 n} (hx : InG x) : (u1 x).det ≠ 0 := by
  have := PositivityTheory.Rg.Sw.AbsSt.IwaPf.det_ne x hx Complex.I (by simp [Complex.ext_iff]; norm_num)
  simpa [u1] using this

def Nq (Q : Matrix (Fin n) (Fin n) ℂ) : M2 n := Cm n * fromBlocks 0 Q 0 0 * Cmi n

theorem cmi_mul_cm : Cmi n * Cm n = 1 := mul_eq_one_comm.mp cm_mul_cmi

theorem Nq_sq (Q : Matrix (Fin n) (Fin n) ℂ) : Nq Q * Nq Q = 0 := by
  have : fromBlocks 0 Q 0 0 * fromBlocks 0 Q 0 0 = (0 : M2 n) := by
    rw [fromBlocks_multiply]; simp [fromBlocks_zero]
  calc Nq Q * Nq Q = Cm n * fromBlocks 0 Q 0 0 * (Cmi n * Cm n) * fromBlocks 0 Q 0 0 * Cmi n := by
        simp only [Nq, Matrix.mul_assoc]
    _ = 0 := by rw [cmi_mul_cm, Matrix.mul_one, Matrix.mul_assoc (Cm n), this]; simp

theorem mX_eq (Q : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) : mX (1 : Matrix (Fin n) (Fin n) ℂ) (s • Q) 0 1 = 1 + s • Nq Q := by
  have e : (fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) (s • Q) 0 1 : M2 n) = 1 + s • (fromBlocks 0 Q 0 0 : M2 n) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.one_apply]
  rw [mX, cm_inv, e, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, cm_mul_cmi, Nq, Matrix.mul_smul, Matrix.smul_mul]

theorem lowQ_eq (Q : Matrix (Fin n) (Fin n) ℂ) : lowQ Q = Nq Q := by
  have := mX_eq Q 1
  rw [one_smul, one_smul] at this
  rw [lowQ, this]; abel

theorem Nq_blocks (Q : Matrix (Fin n) (Fin n) ℂ) :
    Nq Q = fromBlocks (-(1 / 2 : ℂ) • Q) ((Complex.I / 2) • Q) ((Complex.I / 2) • Q) ((1 / 2 : ℂ) • Q) := by
  rw [Nq, Cm, Cmi, fromBlocks_multiply, fromBlocks_multiply]
  congr 1 <;> ext i j <;> simp [Matrix.mul_apply, Matrix.one_apply, Matrix.smul_apply] <;> ring_nf <;>
    simp [Complex.I_sq] <;> ring

theorem inv_mul_lower {x : M2 n} (hx : IsUnit x) (Q : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) :
    (x * (1 + s • Nq Q))⁻¹ = (1 - s • Nq Q) * x⁻¹ := by
  refine Matrix.inv_eq_right_inv ?_
  have hN := Nq_sq Q
  have e : (1 + s • Nq Q) * (1 - s • Nq Q) = (1 : M2 n) := by
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, hN]
    simp
  have hx' : x * x⁻¹ = 1 := Matrix.mul_nonsing_inv x ((Matrix.isUnit_iff_isUnit_det x).mp hx)
  calc x * (1 + s • Nq Q) * ((1 - s • Nq Q) * x⁻¹) = x * ((1 + s • Nq Q) * (1 - s • Nq Q)) * x⁻¹ := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [e, Matrix.mul_one, hx']

theorem upper_left_block_sub (A B : M2 n) : (A - B).toBlocks₁₁ = A.toBlocks₁₁ - B.toBlocks₁₁ := by ext; simp [toBlocks₁₁]
theorem lower_left_block_sub (A B : M2 n) : (A - B).toBlocks₂₁ = A.toBlocks₂₁ - B.toBlocks₂₁ := by ext; simp [toBlocks₂₁]
theorem upper_left_block_smul (c : ℂ) (A : M2 n) : (c • A).toBlocks₁₁ = c • A.toBlocks₁₁ := by ext; simp [toBlocks₁₁]
theorem lower_left_block_smul (c : ℂ) (A : M2 n) : (c • A).toBlocks₂₁ = c • A.toBlocks₂₁ := by ext; simp [toBlocks₂₁]
theorem upper_left_block_mul_eq (A B : M2 n) : (A * B).toBlocks₁₁ = A.toBlocks₁₁ * B.toBlocks₁₁ + A.toBlocks₁₂ * B.toBlocks₂₁ := by
  conv_lhs => rw [← fromBlocks_toBlocks A, ← fromBlocks_toBlocks B, fromBlocks_multiply]
  simp

theorem inverse_first_block_lowering {x : M2 n} (hx : IsUnit x) (Q : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) :
    ub1 (x * (1 + s • Nq Q)) = ub1 x - s • (Q * ub2 x) := by
  rw [ub1, inv_mul_lower hx, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, upper_left_block_sub, lower_left_block_sub, upper_left_block_smul,
    lower_left_block_smul, upper_left_block_mul_eq, toBlocks₂₁_mul, Nq_blocks, ub1, ub2]
  simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂,
    Matrix.smul_mul, Matrix.mul_add, Matrix.mul_neg, Matrix.mul_smul, smul_add, smul_sub, smul_neg, smul_smul]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul]
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem first_block_lowering_invariant (x : M2 n) (Q : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) : u1 (x * (1 + s • Nq Q)) = u1 x := by
  have := (uAct n x 1 (s • Q) 0 1).1
  rw [mX_eq] at this
  rw [this]; simp

theorem det_lower (x : M2 n) (Q : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) : (x * (1 + s • Nq Q)).det = x.det := by
  rw [← mX_eq, det_mul, mX, cm_inv, det_mul, det_mul, det_fromBlocks_zero₂₁]
  have : (Cm n).det * (Cmi n).det = 1 := by rw [← det_mul, cm_mul_cmi, det_one]
  simp only [det_one, mul_one]
  linear_combination x.det * this

end PositivityTheory.Rg.Sw.HSt.LoweringDerivative
end
end

noncomputable section

open Matrix Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt.LoweringDerivative

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

private theorem deriv_comp_mul_exp_smul_eq_fderiv (F : M2 n → ℂ) (x W : M2 n) (hF : DifferentiableAt ℂ F x) :
    deriv (fun t : ℝ => F (x * NormedSpace.exp ((t : ℂ) • W))) 0 = fderiv ℂ F x (x * W) := by
  have hL : HasDerivAt (fun t : ℝ => x * II.cE W t) (x * W) 0 := by
    let L : M2 n →L[ℝ] M2 n := LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ x)
    exact L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (II.cE_hasDerivAt0 W)
  have h := (hF.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt_of_eq (0 : ℝ) hL (by simp [II.cE])
  have he : (fun t : ℝ => F (x * NormedSpace.exp ((t : ℂ) • W))) = fun t => F (x * II.cE W t) := by
    funext t
    simp only [II.cE, Complex.coe_smul]
  rw [he]
  exact h.deriv

theorem rC_eq (F : M2 n → ℂ) (x Z : M2 n) (hF : DifferentiableAt ℂ F x) : rC Z F x = fderiv ℂ F x (x * Z) := by
  unfold rC
  rw [deriv_comp_mul_exp_smul_eq_fderiv F x _ hF, deriv_comp_mul_exp_smul_eq_fderiv F x _ hF, ← smul_eq_mul Complex.I, ← map_smul, ← map_add (f := _),
    ← Matrix.mul_smul, ← Matrix.mul_add, smul_smul]
  have hI : Complex.I * (1 / (2 * Complex.I)) = 1 / 2 := by
    field_simp
  rw [hI, ← smul_add, add_add_sub_cancel, ← two_smul ℂ Z, smul_smul]
  norm_num

theorem contDiffOn_inverse_first_block : ∀ i j, ContDiffOn ℂ ∞ (fun x : M2 n => ub1 x i j) {x | x.det ≠ 0} := by
  intro i j
  exact LVs.contDiffOn_inverse_first_block _ (fun x hx => isUnit_iff_ne_zero.2 hx) i j

theorem isOpen_det_ne : IsOpen {x : M2 n | x.det ≠ 0} :=
  isOpen_ne_fun (continuous_id.matrix_det) continuous_const

end PositivityTheory.Rg.Sw.HSt.LoweringDerivative
end
end

noncomputable section

open Matrix Filter Topology Polynomial
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt.LoweringDerivative

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem diffAt_of_cdo {f : M2 n → ℂ} {U : Set (M2 n)} (hf : ContDiffOn ℂ ∞ f U) (hU : IsOpen U) {x : M2 n}
    (hx : x ∈ U) : DifferentiableAt ℂ f x :=
  (hf.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)

theorem D0_eq_numSeg_mul_add {x : M2 n} (hx : InG x) :
    (u1 x).det * (ub1 x).det = ((Complex.normSq (u1 x).det : ℝ) : ℂ) := by
  rw [inverse_first_block_eq_conjTranspose hx, Matrix.det_conjTranspose, Complex.star_def]
  exact Complex.mul_conj _

theorem normSq_det_first_block_pos {x : M2 n} (hx : InG x) : 0 < Complex.normSq (u1 x).det :=
  Complex.normSq_pos.mpr (det_first_block_ne_zero_group hx)

theorem det_product_mem_slitPlane {x : M2 n} (hx : InG x) : (u1 x).det * (ub1 x).det ∈ Complex.slitPlane := by
  rw [D0_eq_numSeg_mul_add hx]; exact Complex.ofReal_mem_slitPlane.mpr (normSq_det_first_block_pos hx)

theorem diff_fz {x : M2 n} (hx : InG x) (m : ℕ) (e : ℤ) (z : ℂ) : DifferentiableAt ℂ (fz m e z) x := by
  have hU : IsOpen {y : M2 n | det y ≠ 0} := isOpen_det_ne
  have hxU : x ∈ {y : M2 n | det y ≠ 0} := (isUnit_det_of_inG hx).ne_zero
  have hdet : DifferentiableAt ℂ (fun y : M2 n => det y) x :=
    diffAt_of_cdo (cdo_det (fun i j => (contDiff_apply_apply ℂ i j).contDiffOn)) hU hxU
  have hu1 : DifferentiableAt ℂ (fun y : M2 n => (u1 y).det) x :=
    diffAt_of_cdo (cdo_det (fun i j => LVs.contDiffOn_first_cayley_block_entries _ i j)) hU hxU
  have hub1 : DifferentiableAt ℂ (fun y : M2 n => (ub1 y).det) x :=
    diffAt_of_cdo (cdo_det (fun i j => PositivityTheory.Rg.Sw.HSt.LoweringDerivative.contDiffOn_inverse_first_block i j)) hU hxU
  unfold fz
  refine ((hdet.zpow (Or.inl hxU)).mul (hu1.zpow (Or.inl (det_first_block_ne_zero_group hx)))).mul ?_
  exact (hu1.mul hub1).cpow (differentiableAt_const _) (det_product_mem_slitPlane hx)

set_option backward.isDefEq.respectTransparency false in
theorem hasDerivAt_det_one_add_smul (A : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun s : ℂ => (1 + s • A).det) A.trace 0 := by
  have h : (fun s : ℂ => (1 + s • A).det) = fun s =>
      1 + A.trace * s + (det (1 + (Polynomial.X : ℂ[X]) • A.map Polynomial.C)).divX.divX.eval s * s ^ 2 := by
    funext s
    exact Matrix.det_one_add_smul s A
  rw [h]
  have h1 : HasDerivAt (fun s : ℂ => 1 + A.trace * s) A.trace 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).const_mul A.trace).const_add 1
  have h2 : HasDerivAt (fun s : ℂ =>
      (det (1 + (Polynomial.X : ℂ[X]) • A.map Polynomial.C)).divX.divX.eval s * s ^ 2) 0 0 := by
    convert (Polynomial.hasDerivAt
      (det (1 + (Polynomial.X : ℂ[X]) • A.map Polynomial.C)).divX.divX (0 : ℂ)).fun_mul
      (hasDerivAt_pow 2 (0 : ℂ)) using 1
    all_goals first
      | rfl
      | simp
  convert h1.fun_add h2 using 1
  all_goals first
    | rfl
    | simp

set_option backward.isDefEq.respectTransparency false in
theorem lt1 : LoweringDerivativeVacuum := by
  intro n m e z Q x hx
  have hxu : IsUnit x := isUnit_of_inG hx
  have hD : (u1 x).det * (ub1 x).det ≠ 0 := Complex.slitPlane_ne_zero (det_product_mem_slitPlane hx)
  have hB : (ub1 x).det ≠ 0 := right_ne_zero_of_mul hD
  rw [rC_eq _ _ _ (diff_fz hx m e z), lowQ_eq]
  have hline : ∀ s : ℂ, x + s • (x * Nq Q) = x * (1 + s • Nq Q) := by
    intro s
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]
  have hsub : ∀ s : ℂ, ub1 x - s • (Q * ub2 x) = ub1 x * (1 + s • -((ub1 x)⁻¹ * (Q * ub2 x))) := by
    intro s
    have hBu : IsUnit (ub1 x).det := isUnit_iff_ne_zero.2 hB
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, Matrix.mul_neg, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hBu, Matrix.one_mul, smul_neg, sub_eq_add_neg]
  have hcomp : ∀ s : ℂ, fz m e z (x + s • (x * Nq Q)) = det x ^ e * (u1 x).det ^ (-(m : ℤ)) *
      ((u1 x).det * ((ub1 x).det * (1 + s • -((ub1 x)⁻¹ * (Q * ub2 x))).det)) ^ (-z) := by
    intro s
    rw [hline s]
    unfold fz
    rw [det_lower, first_block_lowering_invariant, inverse_first_block_lowering hxu, hsub, Matrix.det_mul]
  have htr : (-((ub1 x)⁻¹ * (Q * ub2 x))).trace = -(Om x * Q).trace := by
    unfold Om
    rw [Matrix.trace_neg, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.trace_mul_comm Q]
  have hL : HasDerivAt (fun s : ℂ => x + s • (x * Nq Q)) (x * Nq Q) 0 := by
    convert ((hasDerivAt_id (0 : ℂ)).smul_const (x * Nq Q)).const_add x using 1
    all_goals first
      | rfl
      | simp
  have h1 : HasDerivAt (fun s : ℂ => fz m e z (x + s • (x * Nq Q)))
      (fderiv ℂ (fz m e z) x (x * Nq Q)) 0 :=
    (diff_fz hx m e z).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℂ) hL (by simp)
  have hdet := hasDerivAt_det_one_add_smul (-((ub1 x)⁻¹ * (Q * ub2 x)))
  have hg := (hdet.const_mul (ub1 x).det).const_mul (u1 x).det
  have hg0 : (u1 x).det * ((ub1 x).det * (1 + (0 : ℂ) • -((ub1 x)⁻¹ * (Q * ub2 x))).det)
      ∈ Complex.slitPlane := by
    simpa using det_product_mem_slitPlane hx
  have hp := (hg.cpow_const (c := -z) hg0).const_mul (det x ^ e * (u1 x).det ^ (-(m : ℤ)))
  have h2 := hp.congr_of_eventuallyEq (Filter.Eventually.of_forall hcomp)
  rw [h1.unique h2, htr]
  simp only [zero_smul, add_zero, Matrix.det_one, mul_one]
  rw [Complex.cpow_sub _ _ hD, Complex.cpow_one]
  have hr : (u1 x).det * ((ub1 x).det * -(Om x * Q).trace) =
      -((u1 x).det * (ub1 x).det * (Om x * Q).trace) := by ring
  rw [hr]
  unfold eQ fz
  generalize (u1 x).det * (ub1 x).det = D at hD ⊢
  field_simp

end PositivityTheory.Rg.Sw.HSt.LoweringDerivative

namespace PositivityTheory.Rg.Sw.HSt

theorem lt1 : LoweringDerivativeVacuum := LoweringDerivative.lt1

end PositivityTheory.Rg.Sw.HSt
