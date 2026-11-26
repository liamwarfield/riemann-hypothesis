module

public import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement

@[expose] public section

section -- merged from ReciprocityTheory.AnalyticForms.LeviForms.HomDensB
section -- merged from ReciprocityTheory.AnalyticForms.LeviForms.HomDensA
namespace ReciprocityTheory.AnForm.P

open Filter Topology Polynomial Matrix
open scoped ContDiff

noncomputable section

theorem leviForm_half_log_abs_of_fderiv_eq_zero {ι : Type} [Fintype ι] (f : (ι → ℂ) → ℝ) (z : ι → ℂ)
    (hf : ContDiffAt ℝ 2 f z) (hz : f z ≠ 0) (hd : fderiv ℝ f z = 0) (w : ι → ℂ) :
    levi (fun x => (1 / 2) * Real.log |f x|) z w = levi f z w / (2 * f z) := by
  have hev1 : ∀ᶠ x in 𝓝 z, f x ≠ 0 := hf.continuousAt.eventually_ne hz
  have hev2 : ∀ᶠ x in 𝓝 z, ContDiffAt ℝ 2 f x := hf.eventually (by simp)

  have hderiv : fderiv ℝ (fun x => (1 / 2) * Real.log |f x|) =ᶠ[𝓝 z]
      fun x => ((1 / 2) * (f x)⁻¹) • fderiv ℝ f x := by
    filter_upwards [hev1, hev2] with x hx1 hx2
    have hfd : HasFDerivAt f (fderiv ℝ f x) x := (hx2.differentiableAt (by norm_num)).hasFDerivAt
    have hl : HasFDerivAt (fun y => (1 / 2 : ℝ) * Real.log (f y)) ((1 / 2 : ℝ) • (f x)⁻¹ • fderiv ℝ f x) x :=
      (hfd.log hx1).const_mul (1 / 2)
    have e : (fun y => (1 / 2 : ℝ) * Real.log |f y|) = fun y => (1 / 2 : ℝ) * Real.log (f y) := by
      funext y
      rw [Real.log_abs]
    rw [e, hl.fderiv, smul_smul]
  have hL : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) z) z :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hfz : HasFDerivAt f (fderiv ℝ f z) z := (hf.differentiableAt (by norm_num)).hasFDerivAt
  have hc : HasFDerivAt (fun x => (1 / 2 : ℝ) * (f x)⁻¹) _ z :=
    ((hasDerivAt_inv hz).comp_hasFDerivAt z hfz).const_mul (1 / 2 : ℝ)
  have hprod := hc.smul hL
  unfold levi
  have hprod' : HasFDerivAt (fun x => ((1 / 2 : ℝ) * (f x)⁻¹) • fderiv ℝ f x) _ z := hprod
  rw [hderiv.fderiv_eq, hprod'.fderiv, hd]
  simp
  field_simp

theorem hasDerivAt_line {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {φ : E → ℝ}
    {v : E} {t : ℝ} (h : DifferentiableAt ℝ φ (t • v)) :
    HasDerivAt (fun s : ℝ => φ (s • v)) (fderiv ℝ φ (t • v) v) t := by
  have h1 : HasDerivAt (fun s : ℝ => s • v) v t := by simpa using (hasDerivAt_id t).smul_const v
  exact h.hasFDerivAt.comp_hasDerivAt t h1

theorem deriv2_line {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {φ : E → ℝ}
    (hφ : ContDiff ℝ 2 φ) (v : E) :
    deriv (deriv (fun s : ℝ => φ (s • v))) 0 = fderiv ℝ (fderiv ℝ φ) 0 v v := by
  have hd : ∀ x, DifferentiableAt ℝ φ x := fun x => hφ.differentiable (by norm_num) x
  have e : deriv (fun s : ℝ => φ (s • v)) = fun s => fderiv ℝ φ (s • v) v := by
    funext s
    exact (hasDerivAt_line (hd _)).deriv
  rw [e]
  have hf2 : Differentiable ℝ (fderiv ℝ φ) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have h1 : HasDerivAt (fun s : ℝ => s • v) v 0 := by simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
  have h2 := (hf2 ((0 : ℝ) • v)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  have h3 := h2.clm_apply (hasDerivAt_const (0 : ℝ) v)
  rw [zero_smul] at h3
  simpa using h3.deriv

theorem levi_eq_lines {ι : Type*} [Fintype ι] {φ : (ι → ℂ) → ℝ} (hφ : ContDiff ℝ 2 φ)
    (w : ι → ℂ) :
    levi φ 0 w = (deriv (deriv (fun s : ℝ => φ (s • w))) 0 +
      deriv (deriv (fun s : ℝ => φ (s • (Complex.I • w)))) 0) / 4 := by
  unfold levi
  rw [deriv2_line hφ w, deriv2_line hφ (Complex.I • w)]

theorem fderiv_line_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {φ : E → ℝ}
    (hφ : DifferentiableAt ℝ φ 0) (v : E) :
    fderiv ℝ φ 0 v = deriv (fun s : ℝ => φ (s • v)) 0 := by
  have h := hasDerivAt_line (v := v) (t := 0) (by rwa [zero_smul])
  rw [h.deriv, zero_smul]

theorem deriv_re_eval (D : ℂ[X]) :
    deriv (fun s : ℝ => (D.eval (s : ℂ)).re) = fun s : ℝ => (D.derivative.eval (s : ℂ)).re := by
  funext s
  exact ((Polynomial.hasDerivAt D (s : ℂ)).real_of_complex).deriv

theorem deriv_re_eval_zero (D : ℂ[X]) :
    deriv (fun s : ℝ => (D.eval (s : ℂ)).re) 0 = (D.coeff 1).re := by
  rw [deriv_re_eval]
  simp [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative]

theorem deriv2_re_eval_zero (D : ℂ[X]) :
    deriv (deriv (fun s : ℝ => (D.eval (s : ℂ)).re)) 0 = 2 * (D.coeff 2).re := by
  rw [deriv_re_eval, deriv_re_eval]
  simp [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative]
  ring

def cf {α β : Type*} (n : ℕ) (P : Matrix α β ℂ[X]) : Matrix α β ℂ := P.map fun p => p.coeff n

theorem cf_apply {α β : Type*} (n : ℕ) (P : Matrix α β ℂ[X]) (i : α) (j : β) :
    cf n P i j = (P i j).coeff n := rfl

theorem cf_mul {α β γ : Type*} [Fintype β] (n : ℕ) (P : Matrix α β ℂ[X]) (Q : Matrix β γ ℂ[X]) :
    cf n (P * Q) = ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, cf x.1 P * cf x.2 Q := by
  ext i j
  simp only [cf, Matrix.map_apply, Matrix.mul_apply, Polynomial.finsetSum_coeff, Polynomial.coeff_mul,
    Matrix.sum_apply]
  exact Finset.sum_comm

theorem cf_mapC_mul {α β γ : Type*} [Fintype β] (n : ℕ) (A : Matrix α β ℂ)
    (P : Matrix β γ ℂ[X]) : cf n (A.map C * P) = A * cf n P := by
  ext i j
  simp only [cf, Matrix.map_apply, Matrix.mul_apply, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul]

theorem coeff_X_mul_C (a : ℂ) (n : ℕ) : (X * C a).coeff n = if n = 1 then a else 0 := by
  rw [mul_comm, Polynomial.coeff_C_mul_X]

theorem eq_X_sq_mul (q : ℂ[X]) (h0 : q.coeff 0 = 0) (h1 : q.coeff 1 = 0) :
    q = X ^ 2 * q.divX.divX := by
  have e1 := Polynomial.X_mul_divX_add q
  have e2 := Polynomial.X_mul_divX_add q.divX
  rw [h0, map_zero, add_zero] at e1
  rw [Polynomial.coeff_divX, zero_add, h1, map_zero, add_zero] at e2
  calc q = X * q.divX := e1.symm
    _ = X * (X * q.divX.divX) := by rw [e2]
    _ = X ^ 2 * q.divX.divX := by ring

theorem det_map_C_add_X_sq_smul {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ)
    (M : Matrix n n ℂ[X]) :
    ∃ r : ℂ[X], (A.map C + (X ^ 2 : ℂ[X]) • M).det = C A.det + X ^ 2 * r := by
  have hmap : (A.map C + (X ^ 2 : ℂ[X]) • M).map (Ideal.Quotient.mk (Ideal.span {X ^ 2})) =
      (A.map C).map (Ideal.Quotient.mk (Ideal.span {(X : ℂ[X]) ^ 2})) := by
    ext i j
    simp [Ideal.Quotient.mk_singleton_self]
  have h := congrArg Matrix.det hmap
  have e1 : (Ideal.Quotient.mk (Ideal.span {(X : ℂ[X]) ^ 2})) (A.map C + (X ^ 2 : ℂ[X]) • M).det =
      (Ideal.Quotient.mk (Ideal.span {(X : ℂ[X]) ^ 2})) (A.map C).det := by
    rw [RingHom.map_det, RingHom.map_det]
    exact h
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at e1
  obtain ⟨r, hr⟩ := e1
  refine ⟨r, ?_⟩
  have hdet : (A.map C).det = C A.det := (RingHom.map_det C A).symm
  rw [hdet] at hr
  linear_combination hr

theorem eq_map_C_add_X_sq_smul {n : Type*} (P : Matrix n n ℂ[X]) (h1 : cf 1 P = 0) :
    P = (cf 0 P).map C + (X ^ 2 : ℂ[X]) • (P - (cf 0 P).map C).map (fun q => q.divX.divX) := by
  ext i j
  have h1' : (P i j).coeff 1 = 0 := by
    have := congrFun (congrFun h1 i) j
    simpa [cf] using this
  have hq0 : (P i j - C ((P i j).coeff 0)).coeff 0 = 0 := by simp
  have hq1 : (P i j - C ((P i j).coeff 0)).coeff 1 = 0 := by simp [h1', Polynomial.coeff_C]
  simp only [Matrix.add_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, cf]
  rw [← eq_X_sq_mul _ hq0 hq1]
  ring

theorem det_coeff_zero_one_of_coeffMatrix_one {n : Type*} [Fintype n] [DecidableEq n] (P : Matrix n n ℂ[X])
    (h1 : cf 1 P = 0) : P.det.coeff 0 = (cf 0 P).det ∧ P.det.coeff 1 = 0 := by
  obtain ⟨r, hr⟩ := det_map_C_add_X_sq_smul (cf 0 P) ((P - (cf 0 P).map C).map fun q => q.divX.divX)
  rw [← eq_map_C_add_X_sq_smul P h1] at hr
  rw [hr]
  constructor
  · simp [Polynomial.coeff_X_pow_mul']
  · simp [Polynomial.coeff_X_pow_mul', Polynomial.coeff_C]

theorem coeff2_det_of {n : Type*} [Fintype n] [DecidableEq n] (P : Matrix n n ℂ[X])
    (d : n → ℂ) (hd : ∀ a, d a ≠ 0) (h0 : cf 0 P = diagonal d) (h1 : cf 1 P = 0) :
    P.det.coeff 2 = (∏ a, d a) * ∑ a, (d a)⁻¹ * cf 2 P a a := by
  set N : Matrix n n ℂ[X] := (P - (cf 0 P).map C).map (fun q => q.divX.divX) with hN
  set K : Matrix n n ℂ[X] := diagonal (fun a => C (d a)⁻¹) * N with hK
  have hP := eq_map_C_add_X_sq_smul P h1
  rw [← hN] at hP
  have hD : (cf 0 P).map C = diagonal (fun a => C (d a)) := by
    rw [h0, Matrix.diagonal_map (map_zero C)]

  have hfac : P = diagonal (fun a => C (d a)) * (1 + ((X : ℂ[X]) ^ 2) • K) := by
    have hone : diagonal (fun a => C (d a)) * diagonal (fun a => C (d a)⁻¹) = (1 : Matrix n n ℂ[X]) := by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext a
      rw [← map_mul, mul_inv_cancel₀ (hd a), map_one]
    rw [mul_add, mul_one, Matrix.mul_smul, hK, ← mul_assoc, hone, one_mul, ← hD]
    exact hP
  have hdet : P.det = C (∏ a, d a) * (1 + ((X : ℂ[X]) ^ 2) • K).det := by
    conv_lhs => rw [hfac]
    rw [Matrix.det_mul, Matrix.det_diagonal, map_prod]
  rw [hdet, Polynomial.coeff_C_mul, Matrix.det_one_add_smul]
  have e4 : ((X : ℂ[X]) ^ 2) ^ 2 = X ^ 4 := by ring
  rw [e4, Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_mul_X_pow', Polynomial.coeff_mul_X_pow']
  simp only [show ¬ (4 ≤ 2) by norm_num, show (2 ≤ 2) by norm_num, if_false, if_true, Nat.sub_self,
    add_zero, Polynomial.coeff_one, show (2 : ℕ) ≠ 0 by norm_num, if_false, zero_add]
  congr 1
  rw [Matrix.trace, Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.diag_apply, hK, Matrix.diagonal_mul, Polynomial.coeff_C_mul, hN]
  simp [Polynomial.coeff_divX, cf]

end

end ReciprocityTheory.AnForm.P
end

namespace ReciprocityTheory.AnForm.P

open Polynomial Matrix

noncomputable section

theorem cf_mul_zero {α β γ : Type*} [Fintype β] (P : Matrix α β ℂ[X]) (Q : Matrix β γ ℂ[X]) :
    cf 0 (P * Q) = cf 0 P * cf 0 Q := by
  rw [cf_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ]

theorem cf_mul_one {α β γ : Type*} [Fintype β] (P : Matrix α β ℂ[X]) (Q : Matrix β γ ℂ[X]) :
    cf 1 (P * Q) = cf 0 P * cf 1 Q + cf 1 P * cf 0 Q := by
  rw [cf_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ]

theorem cf_mul_two {α β γ : Type*} [Fintype β] (P : Matrix α β ℂ[X]) (Q : Matrix β γ ℂ[X]) :
    cf 2 (P * Q) = cf 0 P * cf 2 Q + cf 1 P * cf 1 Q + cf 2 P * cf 0 Q := by
  rw [cf_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ]

def zMat (N : ℕ) (z : Pairs N → ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  ∑ p : Pairs N, Matrix.single p.1.2 p.1.1 (z p)

theorem cellMat_eq (N : ℕ) (z : Pairs N → ℂ) :
    cellMat N z = ∑ k ∈ Finset.range N, ((k.factorial : ℂ)⁻¹) • zMat N z ^ k := rfl

theorem zMat_apply (N : ℕ) (z : Pairs N → ℂ) (i j : Fin N) :
    zMat N z i j = if h : j < i then z ⟨(j, i), h⟩ else 0 := by
  simp only [zMat, Matrix.sum_apply, Matrix.single_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨(j, i), h⟩]
    · simp
    · intro b _ hb
      rw [if_neg]
      rintro ⟨h1, h2⟩
      exact hb (Subtype.ext (Prod.ext h2 h1))
    · simp
  · refine Finset.sum_eq_zero fun p _ => ?_
    rw [if_neg]
    rintro ⟨h1, h2⟩
    exact h (by rw [← h1, ← h2]; exact p.2)

theorem zMat_eq_zero_of_le {N : ℕ} (z : Pairs N → ℂ) {i j : Fin N} (h : i ≤ j) :
    zMat N z i j = 0 := by
  rw [zMat_apply, dite_eq_right (not_lt.2 h)]

theorem zMat_mul_swap (N : ℕ) (z : Pairs N → ℂ) (i j : Fin N) :
    zMat N z i j * zMat N z j i = 0 := by
  rcases le_total i j with h | h
  · rw [zMat_eq_zero_of_le z h, zero_mul]
  · rw [zMat_eq_zero_of_le z h, mul_zero]

theorem zMat_smul (N : ℕ) (z : Pairs N → ℂ) (c : ℂ) : zMat N (c • z) = c • zMat N z := by
  ext i j
  rw [zMat_apply, Matrix.smul_apply, zMat_apply]
  split_ifs <;> simp

theorem zMat_real_smul (N : ℕ) (z : Pairs N → ℂ) (s : ℝ) :
    zMat N (s • z) = (s : ℂ) • zMat N z := by
  rw [← zMat_smul]
  congr 1

theorem zMat_of_le_one {N : ℕ} (z : Pairs N → ℂ) (hN : N ≤ 1) : zMat N z = 0 := by
  ext i j
  rw [zMat_apply, dite_eq_right]
  · rfl
  intro h
  have := Fin.lt_iff_val_lt_val.1 h
  have := i.isLt
  omega

theorem zsq_diag (N : ℕ) (z : Pairs N → ℂ) (i : Fin N) : (zMat N z ^ 2) i i = 0 := by
  rw [pow_two, Matrix.mul_apply]
  exact Finset.sum_eq_zero fun k _ => zMat_mul_swap N z i k

theorem zhsq_diag (N : ℕ) (z : Pairs N → ℂ) (i : Fin N) : ((zMat N z)ᴴ ^ 2) i i = 0 := by
  rw [← conjTranspose_pow, conjTranspose_apply, zsq_diag, star_zero]

theorem coeff_X_pow_mul_C (a : ℂ) (k n : ℕ) : (X ^ k * C a).coeff n = if n = k then a else 0 := by
  rw [mul_comm, coeff_C_mul_X_pow]

def cpP (N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ[X] :=
  ∑ k ∈ Finset.range N, (X ^ k : ℂ[X]) • ((((k.factorial : ℂ)⁻¹) • A ^ k).map C)

theorem cf_cpP (N n : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) :
    cf n (cpP N A) = if n < N then ((n.factorial : ℂ)⁻¹) • A ^ n else 0 := by
  ext i j
  simp only [cpP, cf_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
    finsetSum_coeff, coeff_X_pow_mul_C]
  rw [Finset.sum_ite_eq]
  by_cases h : n < N <;> simp [h]

theorem coeffMatrix_zero_truncExpPoly (N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) : cf 0 (cpP N A) = 1 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact Subsingleton.elim _ _
  · rw [cf_cpP, if_pos hN]; simp

theorem coeffMatrix_one_truncExpPoly (N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (hA : N ≤ 1 → A = 0) :
    cf 1 (cpP N A) = A := by
  rw [cf_cpP]
  split_ifs with h
  · simp
  · exact (hA (by omega)).symm

theorem coeffMatrix_two_truncExpPoly (N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) : ∃ c : ℂ, cf 2 (cpP N A) = c • A ^ 2 := by
  rw [cf_cpP]
  split_ifs
  · exact ⟨_, rfl⟩
  · exact ⟨0, by simp⟩

def gP (N : ℕ) (hd : Fin N → ℝ) (v : Pairs N → ℂ) : Matrix (Fin N) (Fin N) ℂ[X] :=
  cpP N (zMat N v)ᴴ * ((diagonal fun k => (hd k : ℂ)).map C * cpP N (zMat N v))

theorem coeffMatrix_zero_gramPoly (N : ℕ) (hd : Fin N → ℝ) (v : Pairs N → ℂ) :
    cf 0 (gP N hd v) = diagonal fun k => (hd k : ℂ) := by
  rw [gP, cf_mul_zero, cf_mapC_mul, coeffMatrix_zero_truncExpPoly, coeffMatrix_zero_truncExpPoly, Matrix.one_mul, Matrix.mul_one]

theorem coeffMatrix_one_gramPoly (N : ℕ) (hd : Fin N → ℝ) (v : Pairs N → ℂ) :
    cf 1 (gP N hd v) = (diagonal fun k => (hd k : ℂ)) * zMat N v +
      (zMat N v)ᴴ * diagonal fun k => (hd k : ℂ) := by
  have h1 := coeffMatrix_one_truncExpPoly N (zMat N v) (fun h => zMat_of_le_one v h)
  have h2 := coeffMatrix_one_truncExpPoly N (zMat N v)ᴴ (fun h => by rw [zMat_of_le_one v h, conjTranspose_zero])
  rw [gP, cf_mul_one, cf_mapC_mul, cf_mapC_mul, coeffMatrix_zero_truncExpPoly, coeffMatrix_zero_truncExpPoly, h1, h2, Matrix.one_mul,
    Matrix.mul_one]

theorem coeffMatrix_two_gramPoly_diag (N : ℕ) (hd : Fin N → ℝ) (v : Pairs N → ℂ) (i : Fin N) :
    cf 2 (gP N hd v) i i = ∑ k, star (zMat N v k i) * ((hd k : ℂ) * zMat N v k i) := by
  have h1 := coeffMatrix_one_truncExpPoly N (zMat N v) (fun h => zMat_of_le_one v h)
  have h2 := coeffMatrix_one_truncExpPoly N (zMat N v)ᴴ (fun h => by rw [zMat_of_le_one v h, conjTranspose_zero])
  obtain ⟨c1, e1⟩ := coeffMatrix_two_truncExpPoly N (zMat N v)
  obtain ⟨c2, e2⟩ := coeffMatrix_two_truncExpPoly N (zMat N v)ᴴ
  rw [gP, cf_mul_two, cf_mapC_mul, cf_mapC_mul, cf_mapC_mul, coeffMatrix_zero_truncExpPoly, coeffMatrix_zero_truncExpPoly, h1, h2, e1, e2]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.add_apply, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_mul, Matrix.mul_diagonal, zsq_diag, zhsq_diag,
    mul_zero, zero_mul, zero_add, add_zero]
  rw [Matrix.mul_apply]
  simp only [Matrix.diagonal_mul, conjTranspose_apply]

def Zm (N m : ℕ) (hm : m ≤ N) (v : Pairs N → ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  (zMat N v).submatrix (Fin.castLE hm) (Fin.castLE hm)

def Gm (N : ℕ) (hd : Fin N → ℝ) (m : ℕ) (hm : m ≤ N) (v : Pairs N → ℂ) :
    Matrix (Fin m) (Fin m) ℂ[X] :=
  (gP N hd v).submatrix (Fin.castLE hm) (Fin.castLE hm)

def tL {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ[X] :=
  1 - (X : ℂ[X]) • A.map C

def Gn (N : ℕ) (hd : Fin N → ℝ) (m : ℕ) (hm : m ≤ N) (v : Pairs N → ℂ) :
    Matrix (Fin m) (Fin m) ℂ[X] :=
  tL (Zm N m hm v)ᴴ * Gm N hd m hm v * tL (Zm N m hm v)

theorem coeffMatrix_zero_unipotentLine {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) : cf 0 (tL A) = 1 := by
  ext i j
  by_cases h : i = j <;> simp [tL, cf_apply, h, Matrix.one_apply, coeff_X_mul_C, coeff_one]

theorem coeffMatrix_one_unipotentLine {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) : cf 1 (tL A) = -A := by
  ext i j
  by_cases h : i = j <;> simp [tL, cf_apply, h, Matrix.one_apply, coeff_X_mul_C, coeff_one]

theorem coeffMatrix_two_unipotentLine {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) : cf 2 (tL A) = 0 := by
  ext i j
  by_cases h : i = j <;> simp [tL, cf_apply, h, Matrix.one_apply, coeff_X_mul_C, coeff_one]

theorem castLE_le {N m : ℕ} (hm : m ≤ N) {i j : Fin m} (h : i ≤ j) :
    Fin.castLE hm i ≤ Fin.castLE hm j :=
  Fin.le_iff_val_le_val.2 (by simpa using Fin.le_iff_val_le_val.1 h)

theorem det_tL_lower (N m : ℕ) (hm : m ≤ N) (v : Pairs N → ℂ) : (tL (Zm N m hm v)).det = 1 := by
  rw [det_of_isLowerTriangular]
  · exact Finset.prod_eq_one fun i _ => by simp [tL, Zm, zMat_eq_zero_of_le v le_rfl]
  · intro i j hij
    have hij' : i < j := OrderDual.toDual_lt_toDual.1 hij
    simp [tL, Zm, Matrix.one_apply, hij'.ne, zMat_eq_zero_of_le v (castLE_le hm hij'.le)]

theorem det_tL_upper (N m : ℕ) (hm : m ≤ N) (v : Pairs N → ℂ) :
    (tL (Zm N m hm v)ᴴ).det = 1 := by
  rw [det_of_isUpperTriangular]
  · exact Finset.prod_eq_one fun i _ => by simp [tL, Zm, zMat_eq_zero_of_le v le_rfl]
  · intro i j hij
    have hij' : j < i := hij
    simp [tL, Zm, Matrix.one_apply, hij'.ne', zMat_eq_zero_of_le v (castLE_le hm hij'.le)]

theorem det_Gn (N : ℕ) (hd : Fin N → ℝ) (m : ℕ) (hm : m ≤ N) (v : Pairs N → ℂ) :
    (Gn N hd m hm v).det = (Gm N hd m hm v).det := by
  rw [Gn, det_mul, det_mul, det_tL_upper, det_tL_lower, one_mul, mul_one]

theorem coeffMatrix_zero_gramPolyMinor (N : ℕ) (hd : Fin N → ℝ) (m : ℕ) (hm : m ≤ N) (v : Pairs N → ℂ) :
    cf 0 (Gm N hd m hm v) = diagonal fun a => (hd (Fin.castLE hm a) : ℂ) := by
  show (cf 0 (gP N hd v)).submatrix _ _ = _
  rw [coeffMatrix_zero_gramPoly, submatrix_diagonal _ _ (Fin.castLE_injective hm)]
  rfl

theorem coeffMatrix_one_gramPolyMinor_apply (N : ℕ) (hd : Fin N → ℝ) (m : ℕ) (hm : m ≤ N) (v : Pairs N → ℂ)
    (a b : Fin m) : cf 1 (Gm N hd m hm v) a b =
      (hd (Fin.castLE hm a) : ℂ) * zMat N v (Fin.castLE hm a) (Fin.castLE hm b) +
        star (zMat N v (Fin.castLE hm b) (Fin.castLE hm a)) * (hd (Fin.castLE hm b) : ℂ) := by
  show cf 1 (gP N hd v) _ _ = _
  rw [coeffMatrix_one_gramPoly]
  simp [Matrix.diagonal_mul, Matrix.mul_diagonal, conjTranspose_apply]

theorem coeffMatrix_zero_reducedGramPolyMinor (N : ℕ) (hd : Fin N → ℝ) (m : ℕ) (hm : m ≤ N) (v : Pairs N → ℂ) :
    cf 0 (Gn N hd m hm v) = diagonal fun a => (hd (Fin.castLE hm a) : ℂ) := by
  rw [Gn, cf_mul_zero, cf_mul_zero, coeffMatrix_zero_unipotentLine, coeffMatrix_zero_unipotentLine, Matrix.one_mul, Matrix.mul_one, coeffMatrix_zero_gramPolyMinor]

theorem coeffMatrix_one_reducedGramPolyMinor (N : ℕ) (hd : Fin N → ℝ) (m : ℕ) (hm : m ≤ N) (v : Pairs N → ℂ) :
    cf 1 (Gn N hd m hm v) = 0 := by
  have e : cf 1 (Gn N hd m hm v) = cf 1 (Gm N hd m hm v) - (Zm N m hm v)ᴴ * cf 0 (Gm N hd m hm v) -
      cf 0 (Gm N hd m hm v) * Zm N m hm v := by
    simp only [Gn, cf_mul_zero, cf_mul_one, coeffMatrix_zero_unipotentLine, coeffMatrix_one_unipotentLine]
    noncomm_ring
  rw [e, coeffMatrix_zero_gramPolyMinor]
  ext a b
  simp only [Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, coeffMatrix_one_gramPolyMinor_apply,
    conjTranspose_apply, Zm, submatrix_apply, Matrix.zero_apply]
  ring

theorem conjTranspose_mul_coeffMatrix_one_diag (N : ℕ) (hd : Fin N → ℝ) (m : ℕ) (hm : m ≤ N) (v : Pairs N → ℂ) (a : Fin m) :
    ((Zm N m hm v)ᴴ * cf 1 (Gm N hd m hm v)) a a =
      ∑ b : Fin m, star (zMat N v (Fin.castLE hm b) (Fin.castLE hm a)) *
        ((hd (Fin.castLE hm b) : ℂ) * zMat N v (Fin.castLE hm b) (Fin.castLE hm a)) := by
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  have k := zMat_mul_swap N v (Fin.castLE hm a) (Fin.castLE hm b)
  have k' : star (zMat N v (Fin.castLE hm b) (Fin.castLE hm a)) *
      star (zMat N v (Fin.castLE hm a) (Fin.castLE hm b)) = 0 := by
    rw [← star_mul, k, star_zero]
  simp only [conjTranspose_apply, Zm, submatrix_apply, coeffMatrix_one_gramPolyMinor_apply]
  linear_combination (hd (Fin.castLE hm a) : ℂ) * k'

theorem coeffMatrix_one_mul_diag (N : ℕ) (hd : Fin N → ℝ) (m : ℕ) (hm : m ≤ N) (v : Pairs N → ℂ) (a : Fin m) :
    (cf 1 (Gm N hd m hm v) * Zm N m hm v) a a =
      ∑ b : Fin m, star (zMat N v (Fin.castLE hm b) (Fin.castLE hm a)) *
        ((hd (Fin.castLE hm b) : ℂ) * zMat N v (Fin.castLE hm b) (Fin.castLE hm a)) := by
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  have k := zMat_mul_swap N v (Fin.castLE hm a) (Fin.castLE hm b)
  simp only [Zm, submatrix_apply, coeffMatrix_one_gramPolyMinor_apply]
  linear_combination (hd (Fin.castLE hm a) : ℂ) * k

theorem conjTranspose_mul_diagonal_mul_diag (N : ℕ) (hd : Fin N → ℝ) (m : ℕ) (hm : m ≤ N) (v : Pairs N → ℂ) (a : Fin m) :
    ((Zm N m hm v)ᴴ * (diagonal fun a => (hd (Fin.castLE hm a) : ℂ)) * Zm N m hm v) a a =
      ∑ b : Fin m, star (zMat N v (Fin.castLE hm b) (Fin.castLE hm a)) *
        ((hd (Fin.castLE hm b) : ℂ) * zMat N v (Fin.castLE hm b) (Fin.castLE hm a)) := by
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [Matrix.mul_diagonal, conjTranspose_apply, Zm, submatrix_apply]
  ring

theorem coeffMatrix_two_reducedGramPolyMinor_apply (N : ℕ) (hd : Fin N → ℝ) (m : ℕ) (hm : m ≤ N) (v : Pairs N → ℂ) (a : Fin m) :
    cf 2 (Gn N hd m hm v) a a =
      ∑ k, star (zMat N v k (Fin.castLE hm a)) * ((hd k : ℂ) * zMat N v k (Fin.castLE hm a)) -
      ∑ b : Fin m, star (zMat N v (Fin.castLE hm b) (Fin.castLE hm a)) *
        ((hd (Fin.castLE hm b) : ℂ) * zMat N v (Fin.castLE hm b) (Fin.castLE hm a)) := by
  have e : cf 2 (Gn N hd m hm v) = cf 2 (Gm N hd m hm v) -
      (Zm N m hm v)ᴴ * cf 1 (Gm N hd m hm v) - cf 1 (Gm N hd m hm v) * Zm N m hm v +
      (Zm N m hm v)ᴴ * cf 0 (Gm N hd m hm v) * Zm N m hm v := by
    simp only [Gn, cf_mul_zero, cf_mul_one, cf_mul_two, coeffMatrix_zero_unipotentLine, coeffMatrix_one_unipotentLine, coeffMatrix_two_unipotentLine]
    noncomm_ring
  rw [e, coeffMatrix_zero_gramPolyMinor, Matrix.add_apply, Matrix.sub_apply, Matrix.sub_apply, conjTranspose_mul_coeffMatrix_one_diag, coeffMatrix_one_mul_diag, conjTranspose_mul_diagonal_mul_diag]
  have h2 : cf 2 (Gm N hd m hm v) a a = cf 2 (gP N hd v) (Fin.castLE hm a) (Fin.castLE hm a) :=
    rfl
  rw [h2, coeffMatrix_two_gramPoly_diag]
  ring

theorem eval_cpP (N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (t : ℂ) :
    (cpP N A).map (eval t) = ∑ k ∈ Finset.range N, (t ^ k * ((k.factorial : ℂ)⁻¹)) • A ^ k := by
  ext i j
  simp only [cpP, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← coe_evalRingHom, map_sum]
  simp [mul_assoc]

theorem det_gramPolyMinor_coeff_zero_one (N : ℕ) (hd : Fin N → ℝ) (m : ℕ) (hm : m ≤ N) (v : Pairs N → ℂ) :
    (Gm N hd m hm v).det.coeff 0 = ((∏ a : Fin m, hd (Fin.castLE hm a) : ℝ) : ℂ) ∧
      (Gm N hd m hm v).det.coeff 1 = 0 := by
  obtain ⟨h0, h1⟩ := det_coeff_zero_one_of_coeffMatrix_one (Gn N hd m hm v) (coeffMatrix_one_reducedGramPolyMinor N hd m hm v)
  rw [det_Gn] at h0 h1
  rw [h0, coeffMatrix_zero_reducedGramPolyMinor, det_diagonal, Complex.ofReal_prod]
  exact ⟨rfl, h1⟩

theorem coeff2_Gm (N : ℕ) (hd : Fin N → ℝ) (hd0 : ∀ k, hd k ≠ 0) (m : ℕ) (hm : m ≤ N)
    (v : Pairs N → ℂ) :
    (Gm N hd m hm v).det.coeff 2 = (∏ a : Fin m, (hd (Fin.castLE hm a) : ℂ)) *
      ∑ a : Fin m, ((hd (Fin.castLE hm a) : ℂ))⁻¹ *
        (∑ k, star (zMat N v k (Fin.castLE hm a)) * ((hd k : ℂ) * zMat N v k (Fin.castLE hm a)) -
        ∑ b : Fin m, star (zMat N v (Fin.castLE hm b) (Fin.castLE hm a)) *
          ((hd (Fin.castLE hm b) : ℂ) * zMat N v (Fin.castLE hm b) (Fin.castLE hm a))) := by
  rw [← det_Gn, coeff2_det_of (Gn N hd m hm v) (fun a => (hd (Fin.castLE hm a) : ℂ))
    (fun a => by exact_mod_cast hd0 _) (coeffMatrix_zero_reducedGramPolyMinor N hd m hm v) (coeffMatrix_one_reducedGramPolyMinor N hd m hm v)]
  simp only [coeffMatrix_two_reducedGramPolyMinor_apply]

end

end ReciprocityTheory.AnForm.P
end

namespace ReciprocityTheory.AnForm.P

open MeasureTheory

noncomputable section

def CellMatZeroStatement : Prop := ∀ N : ℕ, cellMat N 0 = 1

theorem cellMat_zero : CellMatZeroStatement := by
  intro N
  have hz : zMat N 0 = 0 := by
    ext i j
    rw [zMat_apply]
    split_ifs <;> rfl
  rw [cellMat_eq, hz]
  rcases N with _ | n
  · exact Subsingleton.elim _ _
  · rw [Finset.sum_range_succ']
    simp

def LeviHalfLogAbsStatement : Prop :=
  ∀ {ι : Type} [Fintype ι] (f : (ι → ℂ) → ℝ) (z : ι → ℂ), ContDiffAt ℝ 2 f z → f z ≠ 0 →
    fderiv ℝ f z = 0 → ∀ w : ι → ℂ,
      levi (fun x => (1 / 2) * Real.log |f x|) z w = levi f z w / (2 * f z)

theorem leviHalfLogAbs : LeviHalfLogAbsStatement := by
  intro ι _ f z hf hz hd w
  exact leviForm_half_log_abs_of_fderiv_eq_zero f z hf hz hd w

def detGram (N : ℕ) (hd : Fin N → ℝ) (m : ℕ) (hm : m ≤ N) (z : Pairs N → ℂ) : ℝ :=
  ((Matrix.submatrix ((cellMat N z).conjTranspose * Matrix.diagonal (fun k => (hd k : ℂ)) *
      cellMat N z) (Fin.castLE hm) (Fin.castLE hm)).det).re

section HomDensHelp

open Matrix Polynomial

theorem detGram_line (N : ℕ) (hd : Fin N → ℝ) (m : ℕ) (hm : m ≤ N) (v : Pairs N → ℂ) (s : ℝ) :
    detGram N hd m hm (s • v) = ((Gm N hd m hm v).det.eval (s : ℂ)).re := by
  have h1 : cellMat N (s • v) =
      ∑ k ∈ Finset.range N, ((s : ℂ) ^ k * ((k.factorial : ℂ)⁻¹)) • zMat N v ^ k := by
    rw [cellMat_eq, zMat_real_smul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [_root_.smul_pow, smul_smul, mul_comm]
  have h2 : (cellMat N (s • v))ᴴ =
      ∑ k ∈ Finset.range N, ((s : ℂ) ^ k * ((k.factorial : ℂ)⁻¹)) • (zMat N v)ᴴ ^ k := by
    rw [h1, conjTranspose_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [conjTranspose_smul, conjTranspose_pow]
    congr 1
    simp [Complex.conj_ofReal]
  have hG : (gP N hd v).map (eval (s : ℂ)) =
      (cellMat N (s • v))ᴴ * diagonal (fun k => (hd k : ℂ)) * cellMat N (s • v) := by
    rw [gP, ← coe_evalRingHom, Matrix.map_mul, Matrix.map_mul, coe_evalRingHom, eval_cpP,
      eval_cpP, h2, h1, Matrix.mul_assoc]
    congr 2
    ext i j
    by_cases h : i = j <;> simp [diagonal_apply, h]
  unfold detGram
  rw [← hG]
  congr 1
  rw [← coe_evalRingHom, RingHom.map_det]
  rfl

theorem contDiff_detGram (N : ℕ) (hd : Fin N → ℝ) (m : ℕ) (hm : m ≤ N) :
    ContDiff ℝ 2 (detGram N hd m hm) := by
  have hZ : ∀ a b, ContDiff ℝ 2 (fun z : Pairs N → ℂ => zMat N z a b) := by
    intro a b
    by_cases h : b < a
    · simp only [zMat_apply, dif_pos h]; exact contDiff_apply ℝ (fun _ => ℂ) _
    · simp only [zMat_apply, dif_neg h]; exact contDiff_const
  have hP : ∀ k a b, ContDiff ℝ 2 (fun z : Pairs N → ℂ => (zMat N z ^ k) a b) := by
    intro k
    induction k with
    | zero => intro a b; simp only [pow_zero]; exact contDiff_const
    | succ k ih =>
      intro a b
      simp only [pow_succ, Matrix.mul_apply]
      exact ContDiff.sum fun l _ => (ih a l).mul (hZ l b)
  have hA : ∀ a b, ContDiff ℝ 2 (fun z : Pairs N → ℂ => cellMat N z a b) := by
    intro a b
    simp only [cellMat_eq, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    exact ContDiff.sum fun k _ => contDiff_const.mul (hP k a b)
  have hS : ∀ a b, ContDiff ℝ 2 (fun z : Pairs N → ℂ => star (cellMat N z a b)) := fun a b => by
    have h := Complex.conjCLE.contDiff.comp (hA a b)
    exact h
  have hM : ∀ a b, ContDiff ℝ 2 (fun z : Pairs N → ℂ =>
      ((cellMat N z)ᴴ * Matrix.diagonal (fun k => (hd k : ℂ)) * cellMat N z) a b) := by
    intro a b
    have e : (fun z : Pairs N → ℂ =>
        ((cellMat N z)ᴴ * Matrix.diagonal (fun k => (hd k : ℂ)) * cellMat N z) a b) =
        fun z => ∑ l, star (cellMat N z l a) * (hd l : ℂ) * cellMat N z l b := by
      funext z
      rw [Matrix.mul_apply]
      simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply]
    rw [e]
    exact ContDiff.sum fun l _ => ((hS l a).mul contDiff_const).mul (hA l b)
  have hdet : ContDiff ℝ 2 (fun z : Pairs N → ℂ => (Matrix.submatrix ((cellMat N z).conjTranspose *
      Matrix.diagonal (fun k => (hd k : ℂ)) * cellMat N z) (Fin.castLE hm) (Fin.castLE hm)).det) := by
    simp only [Matrix.det_apply, Matrix.submatrix_apply, Units.smul_def, zsmul_eq_mul]
    exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => hM _ _)
  have h2 : ContDiff ℝ 2 (fun z : Pairs N → ℂ => Complex.reCLM (Matrix.submatrix
      ((cellMat N z).conjTranspose * Matrix.diagonal (fun k => (hd k : ℂ)) * cellMat N z)
      (Fin.castLE hm) (Fin.castLE hm)).det) := Complex.reCLM.contDiff.comp hdet
  unfold detGram
  simpa only [Complex.reCLM_apply] using h2

theorem sum_castLE (N m : ℕ) (hm : m ≤ N) (f : Fin N → ℝ) :
    ∑ b : Fin m, f (Fin.castLE hm b) = ∑ k : Fin N, if k.val < m then f k else 0 := by
  rw [← Finset.sum_filter]
  exact Finset.sum_bij (fun b _ => Fin.castLE hm b) (fun b _ => by simp)
    (fun b1 _ b2 _ h => Fin.castLE_injective hm h)
    (fun k hk => ⟨⟨k.val, (Finset.mem_filter.1 hk).2⟩, Finset.mem_univ _, Fin.ext rfl⟩)
    (fun b _ => rfl)

def sW (N : ℕ) (hd : Fin N → ℝ) (m : ℕ) (v : Pairs N → ℂ) : ℝ :=
  ∑ i : Fin N, ∑ k : Fin N,
    if i.val < m ∧ m ≤ k.val then hd k / hd i * ‖zMat N v k i‖ ^ 2 else 0

theorem star_mul_mul (h : ℝ) (z : ℂ) : star z * ((h : ℂ) * z) = ((h * ‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.ofReal_mul, ← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
  change (starRingEnd ℂ) z * _ = _
  ring

theorem bracket_eq (N : ℕ) (hd : Fin N → ℝ) (m : ℕ) (hm : m ≤ N) (v : Pairs N → ℂ) :
    ∑ a : Fin m, ((hd (Fin.castLE hm a) : ℂ))⁻¹ *
        (∑ k, star (zMat N v k (Fin.castLE hm a)) * ((hd k : ℂ) * zMat N v k (Fin.castLE hm a)) -
        ∑ b : Fin m, star (zMat N v (Fin.castLE hm b) (Fin.castLE hm a)) *
          ((hd (Fin.castLE hm b) : ℂ) * zMat N v (Fin.castLE hm b) (Fin.castLE hm a))) =
      (sW N hd m v : ℂ) := by
  have hin : ∀ i : Fin N, (∑ k, hd k * ‖zMat N v k i‖ ^ 2) -
      ∑ b : Fin m, hd (Fin.castLE hm b) * ‖zMat N v (Fin.castLE hm b) i‖ ^ 2 =
      ∑ k : Fin N, if m ≤ k.val then hd k * ‖zMat N v k i‖ ^ 2 else 0 := by
    intro i
    rw [sum_castLE N m hm (fun b => hd b * ‖zMat N v b i‖ ^ 2), ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases h : k.val < m
    · simp [h, not_le.2 h]
    · simp [h, not_lt.1 h]
  have hR : ∑ a : Fin m, (hd (Fin.castLE hm a))⁻¹ *
      ((∑ k, hd k * ‖zMat N v k (Fin.castLE hm a)‖ ^ 2) -
        ∑ b : Fin m, hd (Fin.castLE hm b) * ‖zMat N v (Fin.castLE hm b) (Fin.castLE hm a)‖ ^ 2) =
      sW N hd m v := by
    simp only [hin]
    rw [sum_castLE N m hm (fun i => (hd i)⁻¹ *
      ∑ k : Fin N, if m ≤ k.val then hd k * ‖zMat N v k i‖ ^ 2 else 0), sW]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : i.val < m
    · rw [if_pos hi, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hk : m ≤ k.val
      · simp only [hi, hk, and_self, if_true]; ring
      · simp [hk]
    · simp [hi]
  have hC := congrArg (fun x : ℝ => (x : ℂ)) hR
  simp only [star_mul_mul]
  push_cast at hC ⊢
  exact hC

theorem sW_I (N : ℕ) (hd : Fin N → ℝ) (m : ℕ) (w : Pairs N → ℂ) :
    sW N hd m (Complex.I • w) = sW N hd m w := by
  simp [sW, zMat_smul, norm_mul]

theorem sW_pairs (N : ℕ) (hd : Fin N → ℝ) (m : ℕ) (w : Pairs N → ℂ) :
    sW N hd m w = ∑ p : Pairs N, if p.1.1.val < m ∧ m ≤ p.1.2.val then
      hd p.1.2 / hd p.1.1 * ‖w p‖ ^ 2 else 0 := by
  let F : Fin N × Fin N → ℝ := fun q =>
    if q.1.val < m ∧ m ≤ q.2.val then hd q.2 / hd q.1 * ‖zMat N w q.2 q.1‖ ^ 2 else 0
  calc sW N hd m w = ∑ q, F q := (Fintype.sum_prod_type' (fun i k => F (i, k))).symm
    _ = ∑ q ∈ Finset.univ.filter (fun q : Fin N × Fin N => q.1 < q.2), F q := by
      refine (Finset.sum_filter_of_ne fun q _ hq => ?_).symm
      by_contra hlt
      apply hq
      simp only [F]
      rw [if_neg]
      rintro ⟨h1, h2⟩
      exact hlt (Fin.lt_iff_val_lt_val.2 (by omega))
    _ = ∑ p : Pairs N, F p.1 := Finset.sum_subtype _ (by simp) F
    _ = _ := by
      refine Finset.sum_congr rfl fun p _ => ?_
      simp only [F, zMat_apply, dif_pos p.2]

end HomDensHelp

def LogDetFlagEqStatement : Prop :=
  ∀ (N : ℕ) (hd : Fin N → ℝ) (m : ℕ) (hm : m ≤ N),
    logDetFlag N hd m hm = fun z => (1 / 2) * Real.log |detGram N hd m hm z|

theorem logDetFlag_eq : LogDetFlagEqStatement := by
  intro N hd m hm
  funext z
  have hs : star (fun k => (hd k : ℂ)) = fun k => (hd k : ℂ) :=
    funext fun k => Complex.conj_ofReal _
  have hH : (Matrix.submatrix ((cellMat N z).conjTranspose *
      Matrix.diagonal (fun k => (hd k : ℂ)) * cellMat N z) (Fin.castLE hm) (Fin.castLE hm)).conjTranspose =
      Matrix.submatrix ((cellMat N z).conjTranspose * Matrix.diagonal (fun k => (hd k : ℂ)) *
        cellMat N z) (Fin.castLE hm) (Fin.castLE hm) := by
    rw [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.diagonal_conjTranspose, hs, Matrix.mul_assoc]
  have him : (Matrix.submatrix ((cellMat N z).conjTranspose *
      Matrix.diagonal (fun k => (hd k : ℂ)) * cellMat N z) (Fin.castLE hm) (Fin.castLE hm)).det.im = 0 := by
    rw [← Complex.conj_eq_iff_im]
    change star _ = _
    rw [← Matrix.det_conjTranspose, hH]
  unfold logDetFlag detGram
  rw [(Complex.abs_re_eq_norm.2 him).symm]

def DetGramDerivStatement : Prop :=
  ∀ (N : ℕ) (hd : Fin N → ℝ) (m : ℕ) (hm : m ≤ N),
    ContDiff ℝ 2 (detGram N hd m hm) ∧
      detGram N hd m hm 0 = ∏ a : Fin m, hd (Fin.castLE hm a) ∧ fderiv ℝ (detGram N hd m hm) 0 = 0

theorem detGram_deriv : DetGramDerivStatement := by
  intro N hd m hm
  have hC := contDiff_detGram N hd m hm
  have hl : ∀ v, (fun s : ℝ => detGram N hd m hm (s • v)) =
      fun s : ℝ => ((Gm N hd m hm v).det.eval (s : ℂ)).re := fun v => funext (detGram_line N hd m hm v)
  refine ⟨hC, ?_, ?_⟩
  · have h := detGram_line N hd m hm 0 0
    rw [smul_zero] at h
    rw [h, Complex.ofReal_zero, ← Polynomial.coeff_zero_eq_eval_zero, (det_gramPolyMinor_coeff_zero_one N hd m hm 0).1,
      Complex.ofReal_re]
  · refine ContinuousLinearMap.ext fun v => ?_
    rw [fderiv_line_zero (hC.differentiable (by norm_num) 0) v, hl v, deriv_re_eval_zero,
      (det_gramPolyMinor_coeff_zero_one N hd m hm v).2]
    simp

def DetGramLeviStatement : Prop :=
  ∀ (N : ℕ) (hd : Fin N → ℝ), (∀ k, hd k ≠ 0) → ∀ (m : ℕ) (hm : m ≤ N) (w : Pairs N → ℂ),
    levi (detGram N hd m hm) 0 w = (∏ a : Fin m, hd (Fin.castLE hm a)) *
      ∑ p : Pairs N, if p.1.1.val < m ∧ m ≤ p.1.2.val then hd p.1.2 / hd p.1.1 * ‖w p‖ ^ 2 else 0

theorem detGram_levi : DetGramLeviStatement := by
  intro N hd hd0 m hm w
  have hC := contDiff_detGram N hd m hm
  have hl : ∀ v, (fun s : ℝ => detGram N hd m hm (s • v)) =
      fun s : ℝ => ((Gm N hd m hm v).det.eval (s : ℂ)).re := fun v => funext (detGram_line N hd m hm v)
  rw [levi_eq_lines hC, hl, hl, deriv2_re_eval_zero, deriv2_re_eval_zero, coeff2_Gm N hd hd0 m hm,
    coeff2_Gm N hd hd0 m hm, bracket_eq, bracket_eq, sW_I, ← sW_pairs, ← Complex.ofReal_prod,
    ← Complex.ofReal_mul, Complex.ofReal_re]
  ring

theorem homDensity : HomDensityStatement := by
  intro N hd hd0 m hm w
  have hC := contDiff_detGram N hd m hm
  obtain ⟨_, h0, h1⟩ := detGram_deriv N hd m hm
  have hP : (∏ a : Fin m, hd (Fin.castLE hm a)) ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => hd0 _
  rw [logDetFlag_eq N hd m hm, leviHalfLogAbs (detGram N hd m hm) 0 hC.contDiffAt
    (by rw [h0]; exact hP) h1 w, detGram_levi N hd hd0 m hm w, h0, Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun p _ => ?_
  split_ifs
  · rw [mul_comm (2 : ℝ), mul_div_mul_left _ _ hP]
    ring
  · simp

end

end ReciprocityTheory.AnForm.P
