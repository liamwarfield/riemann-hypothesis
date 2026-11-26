module

public import ReciprocityTheory.AnalyticForms.LeviForms.HomDens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajorantNormalForms
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.KappaStatementHolds

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.LeviVReLine
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.LogpdAnalytic
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.DiagonalCurvatureCoefficient
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.CoeffMatrixZeroCorrectedLineGramPoly
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf

open Polynomial Matrix ReciprocityTheory.AnForm.P

variable {r m : ℕ} (hm : m ≤ r) (D : Fin r → ℝ) (Y : Matrix (Fin r) (Fin r) ℂ)

def lin {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ[X] := 1 + (X : ℂ[X]) • A.map C

theorem cf_lin {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) :
    cf k (lin A) = if k = 0 then 1 else if k = 1 then A else 0 := by
  ext i j
  rcases k with _ | _ | k <;> by_cases h : i = j <;>
    simp [cf, lin, Matrix.one_apply, h, Polynomial.coeff_one, Polynomial.coeff_C]

theorem coeffMatrix_zero_linearMatrixPoly {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : cf 0 (lin A) = 1 := by
  simp [cf_lin]
theorem coeffMatrix_one_linearMatrixPoly {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : cf 1 (lin A) = A := by
  simp [cf_lin]
theorem coeffMatrix_two_linearMatrixPoly {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : cf 2 (lin A) = 0 := by
  simp [cf_lin]

theorem cf_submatrix {α β γ δ : Type*} (k : ℕ) (P : Matrix α β ℂ[X]) (f : γ → α) (g : δ → β) :
    cf k (P.submatrix f g) = (cf k P).submatrix f g := rfl

abbrev Dc : Matrix (Fin r) (Fin r) ℂ := diagonal fun k => (D k : ℂ)

abbrev Ym : Matrix (Fin m) (Fin m) ℂ := Y.submatrix (Fin.castLE hm) (Fin.castLE hm)

abbrev Dm : Matrix (Fin m) (Fin m) ℂ := diagonal fun i => (D (Fin.castLE hm i) : ℂ)

theorem Dc_sub : (Dc D).submatrix (Fin.castLE hm) (Fin.castLE hm) = Dm hm D := by
  ext i j
  by_cases h : i = j <;> simp [Dc, Dm, Matrix.diagonal_apply, h]

def GP (t : ℂ) : Matrix (Fin m) (Fin m) ℂ[X] :=
  (lin ((starRingEnd ℂ t) • Yᴴ) * ((Dc D).map C * lin (t • Y))).submatrix (Fin.castLE hm) (Fin.castLE hm)

def GnP (t : ℂ) : Matrix (Fin m) (Fin m) ℂ[X] :=
  lin (-((starRingEnd ℂ t) • (Ym hm Y)ᴴ)) * (GP hm D Y t * lin (-(t • Ym hm Y)))

theorem coeffMatrix_zero_lineGramPoly (t : ℂ) : cf 0 (GP hm D Y t) = Dm hm D := by
  rw [GP, cf_submatrix, cf_mul_zero, cf_mapC_mul, coeffMatrix_zero_linearMatrixPoly, coeffMatrix_zero_linearMatrixPoly, one_mul, mul_one, Dc_sub]

theorem coeffMatrix_one_lineGramPoly (t : ℂ) : cf 1 (GP hm D Y t) =
    (starRingEnd ℂ t) • ((Ym hm Y)ᴴ * Dm hm D) + t • (Dm hm D * Ym hm Y) := by
  rw [GP, cf_submatrix, cf_mul_one, cf_mapC_mul, cf_mapC_mul, coeffMatrix_zero_linearMatrixPoly, coeffMatrix_one_linearMatrixPoly, coeffMatrix_one_linearMatrixPoly, coeffMatrix_zero_linearMatrixPoly,
    one_mul, mul_one]
  ext i j
  simp [Dc, Dm, Ym, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.conjTranspose_apply]
  ring

theorem coeffMatrix_two_lineGramPoly (t : ℂ) : cf 2 (GP hm D Y t) =
    ((starRingEnd ℂ t) * t) • (Yᴴ * Dc D * Y).submatrix (Fin.castLE hm) (Fin.castLE hm) := by
  rw [GP, cf_submatrix, cf_mul_two, cf_mapC_mul, cf_mapC_mul, cf_mapC_mul, coeffMatrix_zero_linearMatrixPoly, coeffMatrix_one_linearMatrixPoly, coeffMatrix_one_linearMatrixPoly,
    coeffMatrix_two_linearMatrixPoly, coeffMatrix_two_linearMatrixPoly, coeffMatrix_zero_linearMatrixPoly]
  simp only [Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero, one_mul, Matrix.mul_smul,
    Matrix.smul_mul, smul_smul, Matrix.mul_assoc]
  rw [mul_comm t]
  rfl

theorem coeffMatrix_zero_correctedLineGramPoly (t : ℂ) : cf 0 (GnP hm D Y t) = Dm hm D := by
  rw [GnP, cf_mul_zero, cf_mul_zero, coeffMatrix_zero_linearMatrixPoly, coeffMatrix_zero_linearMatrixPoly, coeffMatrix_zero_lineGramPoly, one_mul, mul_one]

theorem coeffMatrix_one_correctedLineGramPoly (t : ℂ) : cf 1 (GnP hm D Y t) = 0 := by
  rw [GnP, cf_mul_one, cf_mul_one, cf_mul_zero, coeffMatrix_zero_linearMatrixPoly, coeffMatrix_one_linearMatrixPoly, coeffMatrix_zero_linearMatrixPoly, coeffMatrix_one_linearMatrixPoly, coeffMatrix_zero_lineGramPoly, coeffMatrix_one_lineGramPoly]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.add_mul]
  abel

theorem coeffMatrix_two_correctedLineGramPoly (t : ℂ) : cf 2 (GnP hm D Y t) =
    ((starRingEnd ℂ t) * t) • ((Yᴴ * Dc D * Y).submatrix (Fin.castLE hm) (Fin.castLE hm) -
      (Ym hm Y)ᴴ * Dm hm D * Ym hm Y) - t ^ 2 • (Dm hm D * Ym hm Y * Ym hm Y) -
      (starRingEnd ℂ t) ^ 2 • ((Ym hm Y)ᴴ * (Ym hm Y)ᴴ * Dm hm D) := by
  rw [GnP, cf_mul_two, cf_mul_two, cf_mul_one, cf_mul_zero, coeffMatrix_zero_linearMatrixPoly, coeffMatrix_one_linearMatrixPoly, coeffMatrix_two_linearMatrixPoly, coeffMatrix_zero_linearMatrixPoly, coeffMatrix_one_linearMatrixPoly,
    coeffMatrix_two_linearMatrixPoly, coeffMatrix_zero_lineGramPoly, coeffMatrix_one_lineGramPoly, coeffMatrix_two_lineGramPoly]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.add_mul, Matrix.mul_add,
    Matrix.mul_assoc, smul_smul]
  module

def Gz (ζ : ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  ((1 + ζ • Y)ᴴ * Dc D * (1 + ζ • Y)).submatrix (Fin.castLE hm) (Fin.castLE hm)

def Gnz (ζ : ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  (1 - ζ • Ym hm Y)ᴴ * (Gz hm D Y ζ * (1 - ζ • Ym hm Y))

end ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
end
end

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf

open Polynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.P Filter Topology

variable {r m : ℕ} (hm : m ≤ r) (D : Fin r → ℝ) (Y : Matrix (Fin r) (Fin r) ℂ)

section CD

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : WithTop ℕ∞}

theorem cd_mul {n : ℕ} (F G : E → Matrix (Fin n) (Fin n) ℂ) (hF : ∀ a b, ContDiff ℝ k fun v => F v a b)
    (hG : ∀ a b, ContDiff ℝ k fun v => G v a b) (a b : Fin n) : ContDiff ℝ k fun v => (F v * G v) a b := by
  simp only [Matrix.mul_apply]
  exact ContDiff.sum fun i _ => (hF a i).mul (hG i b)

theorem cd_conjT {n : ℕ} (F : E → Matrix (Fin n) (Fin n) ℂ) (hF : ∀ a b, ContDiff ℝ k fun v => F v a b)
    (a b : Fin n) : ContDiff ℝ k fun v => (F v)ᴴ a b := by
  simp only [Matrix.conjTranspose_apply]
  exact Complex.conjCLE.contDiff.comp (hF b a)

theorem cd_det {n : ℕ} (F : E → Matrix (Fin n) (Fin n) ℂ) (hF : ∀ a b, ContDiff ℝ k fun v => F v a b) :
    ContDiff ℝ k fun v => (F v).det := by
  simp only [Matrix.det_apply']
  refine ContDiff.sum fun σ _ => ?_
  exact contDiff_const.mul (contDiff_prod fun i _ => hF (σ i) i)

end CD

def fY (v : Fin 1 → ℂ) : ℝ := (Gz hm D Y (v 0)).det.re

def fn (v : Fin 1 → ℂ) : ℝ := (Gnz hm D Y (v 0)).det.re

def pd (v : Fin 1 → ℂ) : ℂ := (1 - (v 0) • Ym hm Y).det

theorem cd_lin {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (a b : Fin n) :
    ContDiff ℝ 2 fun v : Fin 1 → ℂ => (1 + (c * v 0) • A) a b := by
  have h0 : ContDiff ℝ 2 fun v : Fin 1 → ℂ => v 0 := contDiff_pi.mp contDiff_id 0
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  exact contDiff_const.add ((contDiff_const.mul h0).mul contDiff_const)

theorem cd_Gz (a b : Fin m) : ContDiff ℝ 2 fun v : Fin 1 → ℂ => Gz hm D Y (v 0) a b := by
  have hl : ∀ i j : Fin r, ContDiff ℝ 2 fun v : Fin 1 → ℂ => (1 + v 0 • Y) i j := by
    intro i j
    have h := cd_lin Y 1 i j
    simp only [one_mul] at h
    exact h
  show ContDiff ℝ 2 fun v : Fin 1 → ℂ =>
    ((1 + v 0 • Y)ᴴ * Dc D * (1 + v 0 • Y) : Matrix (Fin r) (Fin r) ℂ) (Fin.castLE hm a) (Fin.castLE hm b)
  exact cd_mul (fun v : Fin 1 → ℂ => (1 + v 0 • Y)ᴴ * Dc D) (fun v => 1 + v 0 • Y)
    (fun i j => cd_mul (fun v : Fin 1 → ℂ => (1 + v 0 • Y)ᴴ) (fun _ => Dc D)
      (cd_conjT (fun v : Fin 1 → ℂ => 1 + v 0 • Y) hl) (fun _ _ => contDiff_const) i j) hl _ _

theorem cd_Gnz (a b : Fin m) : ContDiff ℝ 2 fun v : Fin 1 → ℂ => Gnz hm D Y (v 0) a b := by
  have hl : ∀ i j : Fin m, ContDiff ℝ 2 fun v : Fin 1 → ℂ => (1 - v 0 • Ym hm Y) i j := by
    intro i j
    have h := cd_lin (Ym hm Y) (-1) i j
    have e : ∀ v : Fin 1 → ℂ, (1 + (-1 * v 0) • Ym hm Y) = 1 - v 0 • Ym hm Y := by
      intro v
      rw [neg_one_mul, neg_smul, ← sub_eq_add_neg]
    simp only [e] at h
    exact h
  show ContDiff ℝ 2 fun v : Fin 1 → ℂ =>
    ((1 - v 0 • Ym hm Y)ᴴ * (Gz hm D Y (v 0) * (1 - v 0 • Ym hm Y)) : Matrix (Fin m) (Fin m) ℂ) a b
  exact cd_mul (fun v : Fin 1 → ℂ => (1 - v 0 • Ym hm Y)ᴴ)
    (fun v => Gz hm D Y (v 0) * (1 - v 0 • Ym hm Y))
    (cd_conjT (fun v : Fin 1 → ℂ => 1 - v 0 • Ym hm Y) hl)
    (fun i j => cd_mul (fun v : Fin 1 → ℂ => Gz hm D Y (v 0)) (fun v => 1 - v 0 • Ym hm Y)
      (fun i j => cd_Gz hm D Y i j) hl i j) a b

theorem contDiff_fn : ContDiff ℝ 2 (fn hm D Y) := by
  have h := cd_det (fun v : Fin 1 → ℂ => Gnz hm D Y (v 0)) (fun a b => cd_Gnz hm D Y a b)
  exact Complex.reCLM.contDiff.comp h

theorem contDiff_fY : ContDiff ℝ 2 (fY hm D Y) := by
  have h := cd_det (fun v : Fin 1 → ℂ => Gz hm D Y (v 0)) (fun a b => cd_Gz hm D Y a b)
  exact Complex.reCLM.contDiff.comp h

theorem fn_line (t : ℂ) (s : ℝ) :
    fn hm D Y (s • fun _ => t) = ((GnP hm D Y t).det.eval (s : ℂ)).re := by

  have hlin : ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ),
      (Polynomial.evalRingHom (s : ℂ)).mapMatrix (lin A) = 1 + (s : ℂ) • A := by
    intro n A
    unfold lin
    rw [map_add (f := _), map_one]
    congr 1
    ext i j
    simp
    exact mul_comm _ _
  have hC : (Polynomial.evalRingHom (s : ℂ)).mapMatrix ((Dc D).map Polynomial.C) = Dc D := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.diagonal_apply, h]
  have hsub : ∀ M : Matrix (Fin r) (Fin r) ℂ[X],
      (Polynomial.evalRingHom (s : ℂ)).mapMatrix (M.submatrix (Fin.castLE hm) (Fin.castLE hm)) =
        ((Polynomial.evalRingHom (s : ℂ)).mapMatrix M).submatrix (Fin.castLE hm) (Fin.castLE hm) :=
    fun M => rfl
  have hst : star ((s : ℂ) * t) = (s : ℂ) * (starRingEnd ℂ) t := by
    rw [star_mul', Complex.star_def, Complex.conj_ofReal]
  have key : (GnP hm D Y t).map (Polynomial.eval (s : ℂ)) = Gnz hm D Y ((s : ℂ) * t) := by
    change (Polynomial.evalRingHom (s : ℂ)).mapMatrix (GnP hm D Y t) = _
    unfold GnP GP Gnz Gz
    rw [map_mul, map_mul, hsub, map_mul, map_mul, hlin, hlin, hlin, hlin, hC]
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_add, Matrix.conjTranspose_one,
      Matrix.conjTranspose_smul, hst, smul_smul, smul_neg, ← sub_eq_add_neg, Matrix.mul_assoc]
  have hs : (s • fun _ : Fin 1 => t) 0 = (s : ℂ) * t := by
    simp [Complex.real_smul]
  unfold fn
  rw [hs, ← key]
  congr 1
  have h := RingHom.map_det (Polynomial.evalRingHom (s : ℂ)) (GnP hm D Y t)
  simpa using h.symm

theorem Gz_zero : Gz hm D Y 0 = Dm hm D := by
  ext i j
  simp [Gz, Matrix.diagonal_apply, Fin.castLE_inj]

theorem fn_zero : fn hm D Y (0 : Fin 1 → ℂ) = ∏ a : Fin m, D (Fin.castLE hm a) := by
  have e : Gnz hm D Y 0 = Dm hm D := by
    unfold Gnz
    rw [Gz_zero]
    simp
  unfold fn
  simp only [Pi.zero_apply]
  rw [e]
  simp [Matrix.det_diagonal, ← Complex.ofReal_prod]

theorem fY_zero : fY hm D Y (0 : Fin 1 → ℂ) = ∏ a : Fin m, D (Fin.castLE hm a) := by
  unfold fY
  simp only [Pi.zero_apply]
  rw [Gz_zero]
  simp [Matrix.det_diagonal, ← Complex.ofReal_prod]

theorem fderiv_fn_zero : fderiv ℝ (fn hm D Y) 0 = 0 := by
  refine ContinuousLinearMap.ext fun w => ?_
  set t := w 0 with ht
  have hw : w = fun _ => t := funext fun i => by fin_cases i; rfl
  rw [fderiv_line_zero (((contDiff_fn hm D Y).differentiable (by norm_num)) 0), hw]
  have e : (fun s : ℝ => fn hm D Y (s • fun _ => t)) = fun s : ℝ => ((GnP hm D Y t).det.eval (s : ℂ)).re :=
    funext (fn_line hm D Y t)
  rw [e, deriv_re_eval_zero, (det_coeff_zero_one_of_coeffMatrix_one _ (coeffMatrix_one_correctedLineGramPoly hm D Y t)).2]
  simp

theorem sum_castLE' {M : Type} [AddCommMonoid M] (g : Fin r → M) :
    ∑ j : Fin m, g (Fin.castLE hm j) = ∑ k : Fin r, if (k : ℕ) < m then g k else 0 := by
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun j _ => Fin.castLE hm j) ?_ ?_ ?_ ?_
  · intro j _
    simp
  · intro a _ b _ h
    exact Fin.ext (by simpa using congrArg Fin.val h)
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    exact ⟨⟨k, hk⟩, Finset.mem_univ _, Fin.ext (by simp)⟩
  · intro j _
    rfl

def Sa (a : Fin m) : ℝ := ∑ k : Fin r, if m ≤ (k : ℕ) then D k * ‖Y k (Fin.castLE hm a)‖ ^ 2 else 0

theorem diagonal_curvature_coefficient (a : Fin m) :
    (cf 2 (GnP hm D Y 1) + cf 2 (GnP hm D Y Complex.I)) a a = 2 * (Sa hm D Y a : ℂ) := by
  rw [coeffMatrix_two_correctedLineGramPoly, coeffMatrix_two_correctedLineGramPoly]
  have hc1 : (starRingEnd ℂ) (1 : ℂ) = 1 := map_one _
  have hcI : (starRingEnd ℂ) Complex.I = -Complex.I := Complex.conj_I
  simp only [hc1, hcI, one_mul, one_pow, one_smul, neg_mul, Complex.I_mul_I, neg_neg, Complex.I_sq,
    neg_sq, neg_smul, one_smul, sub_neg_eq_add]
  have e : ∀ (A P Q : Matrix (Fin m) (Fin m) ℂ), (A - P - Q) + (A + P + Q) = (2 : ℂ) • A := by
    intro A P Q; rw [two_smul]; abel
  rw [e, Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply]
  congr 1
  simp only [Matrix.submatrix_apply]
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp only [Dc, Dm, Ym, Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.submatrix_apply]
  rw [sum_castLE' hm (fun k => star (Y k (Fin.castLE hm a)) * (D k : ℂ) * Y k (Fin.castLE hm a)),
    ← Finset.sum_sub_distrib, Sa]
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : (k : ℕ) < m
  · rw [if_pos hk, if_neg (by omega), sub_self]
    simp
  · rw [if_neg hk, if_pos (by omega), sub_zero, Complex.ofReal_mul, Complex.ofReal_pow,
      ← Complex.conj_mul', Complex.star_def]
    ring

theorem levi_fn (hD : ∀ k, D k ≠ 0) :
    levi (fn hm D Y) 0 (fun _ => 1) =
      (∏ a : Fin m, D (Fin.castLE hm a)) * ∑ a : Fin m, (D (Fin.castLE hm a))⁻¹ * Sa hm D Y a := by
  rw [levi_eq_lines (contDiff_fn hm D Y)]
  have hI : (Complex.I • fun _ : Fin 1 => (1 : ℂ)) = fun _ => Complex.I := by funext i; simp
  have e1 : (fun s : ℝ => fn hm D Y (s • fun _ => (1 : ℂ))) =
      fun s : ℝ => ((GnP hm D Y 1).det.eval (s : ℂ)).re := funext (fn_line hm D Y 1)
  have e2 : (fun s : ℝ => fn hm D Y (s • (Complex.I • fun _ : Fin 1 => (1 : ℂ)))) =
      fun s : ℝ => ((GnP hm D Y Complex.I).det.eval (s : ℂ)).re := by
    rw [hI]; exact funext (fn_line hm D Y Complex.I)
  rw [e1, e2, deriv2_re_eval_zero, deriv2_re_eval_zero]
  set d : Fin m → ℂ := fun a => (D (Fin.castLE hm a) : ℂ) with hdd
  have hd : ∀ a, d a ≠ 0 := fun a => Complex.ofReal_ne_zero.2 (hD _)
  rw [coeff2_det_of _ d hd (coeffMatrix_zero_correctedLineGramPoly hm D Y 1) (coeffMatrix_one_correctedLineGramPoly hm D Y 1),
    coeff2_det_of _ d hd (coeffMatrix_zero_correctedLineGramPoly hm D Y Complex.I) (coeffMatrix_one_correctedLineGramPoly hm D Y _)]
  have hterm : ∀ a, (d a)⁻¹ * cf 2 (GnP hm D Y 1) a a + (d a)⁻¹ * cf 2 (GnP hm D Y Complex.I) a a =
      (d a)⁻¹ * (2 * (Sa hm D Y a : ℂ)) := fun a => by
    rw [← mul_add, ← Matrix.add_apply, diagonal_curvature_coefficient]
  have key : (∏ a, d a) * ∑ a, (d a)⁻¹ * cf 2 (GnP hm D Y 1) a a +
      (∏ a, d a) * ∑ a, (d a)⁻¹ * cf 2 (GnP hm D Y Complex.I) a a =
      (((∏ a : Fin m, D (Fin.castLE hm a)) * ∑ a, (D (Fin.castLE hm a))⁻¹ * (2 * Sa hm D Y a) : ℝ) : ℂ) := by
    rw [← mul_add, ← Finset.sum_add_distrib]
    simp_rw [hterm]
    push_cast
    rfl
  have hre := congrArg Complex.re key
  rw [Complex.add_re, Complex.ofReal_re] at hre
  calc (2 * ((∏ a, d a) * ∑ a, (d a)⁻¹ * cf 2 (GnP hm D Y 1) a a).re +
        2 * ((∏ a, d a) * ∑ a, (d a)⁻¹ * cf 2 (GnP hm D Y Complex.I) a a).re) / 4
      = (((∏ a : Fin m, D (Fin.castLE hm a)) * ∑ a, (D (Fin.castLE hm a))⁻¹ * (2 * Sa hm D Y a))) / 2 := by
        rw [← hre]; ring
    _ = _ := by rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_div]; congr 1; funext a; ring

end ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
end
end

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf

open Polynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.P Filter Topology

variable {r m : ℕ} (hm : m ≤ r) (D : Fin r → ℝ) (Y : Matrix (Fin r) (Fin r) ℂ)

theorem fn_zero_ne (hD : ∀ k, D k ≠ 0) : fn hm D Y 0 ≠ 0 := by
  unfold fn
  simp only [Pi.zero_apply]
  have h : Gnz hm D Y 0 = Matrix.diagonal fun a : Fin m => ((D (Fin.castLE hm a) : ℝ) : ℂ) := by
    simp only [Gnz, Gz, zero_smul, sub_zero, add_zero, Matrix.conjTranspose_one, Matrix.one_mul,
      Matrix.mul_one]
    first
    | exact Matrix.submatrix_diagonal _ _ (Fin.castLE_injective hm)
    | simp [Matrix.submatrix_diagonal _ _ (Fin.castLE_injective hm)]
    | (ext i j
       simp [Matrix.diagonal_apply, (Fin.castLE_injective hm).eq_iff])
  rw [h, Matrix.det_diagonal, ← Complex.ofReal_prod, Complex.ofReal_re]
  exact Finset.prod_ne_zero_iff.2 fun a _ => hD _

theorem levi_logfn (hD : ∀ k, D k ≠ 0) :
    levi (fun v => Real.log |fn hm D Y v|) 0 (fun _ => 1) =
      levi (fn hm D Y) 0 (fun _ => 1) / fn hm D Y 0 := by
  have hc : ContDiffAt ℝ 2 (fn hm D Y) 0 := (contDiff_fn hm D Y).contDiffAt
  have h0 := fn_zero_ne hm D Y hD
  have h := leviHalfLogAbs (ι := Fin 1) (fn hm D Y) 0 hc h0 (fderiv_fn_zero hm D Y) (fun _ => 1)
  have hL : ContDiffAt ℝ 2 (fun x => (1 / 2 : ℝ) * Real.log |fn hm D Y x|) 0 := by
    have e : (fun x => (1 / 2 : ℝ) * Real.log |fn hm D Y x|) = fun x => (1 / 2 : ℝ) * Real.log (fn hm D Y x) := by
      funext x; rw [Real.log_abs]
    rw [e]
    exact contDiffAt_const.mul (hc.log h0)
  have e : (fun v => Real.log |fn hm D Y v|) =
      fun v => (1 / 2 * Real.log |fn hm D Y v|) + 1 * (1 / 2 * Real.log |fn hm D Y v|) := by
    funext v; ring
  rw [e, levi_add_smul 1 hL hL, h]
  field_simp
  ring

theorem Gz_herm (ζ : ℂ) : (Gz hm D Y ζ)ᴴ = Gz hm D Y ζ := by
  have hD : (Matrix.diagonal fun k => (D k : ℂ))ᴴ = Matrix.diagonal fun k => (D k : ℂ) := by
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext k
    simp
  first
  | simp only [Gz, Matrix.conjTranspose_submatrix, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hD, Matrix.mul_assoc]
  | (unfold Gz
     rw [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
       Matrix.conjTranspose_conjTranspose]
     erw [hD]
     simp only [Matrix.mul_assoc])

theorem fn_eq (v : Fin 1 → ℂ) : fn hm D Y v = ‖pd hm Y v‖ ^ 2 * fY hm D Y v := by
  have key : ∀ (p G : ℂ), (star p * (G * p)).re = ‖p‖ ^ 2 * G.re := by
    intro p G
    have h1 : star p * (G * p) = ((Complex.normSq p : ℝ) : ℂ) * G := by
      rw [Complex.star_def, ← Complex.mul_conj]
      ring
    rw [h1, Complex.re_ofReal_mul]
    first
    | rw [Complex.normSq_eq_norm_sq]
    | rw [← Complex.sq_norm]
    | simp [Complex.normSq_eq_norm_sq]
  simp only [fn, fY, Gnz, pd, Matrix.det_mul, Matrix.det_conjTranspose]
  exact key _ _

theorem pd_eval (v : Fin 1 → ℂ) : pd hm Y v = (lin (-(Ym hm Y))).det.eval (v 0) := by
  unfold pd lin
  rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  by_cases h : i = j
  · subst h
    simp [Matrix.one_apply, sub_eq_add_neg] <;> ring
  · simp [Matrix.one_apply, h, sub_eq_add_neg] <;> ring

theorem pd_analytic : AnalyticAt ℂ (pd hm Y) 0 := by
  have e : pd hm Y = (fun z => (lin (-(Ym hm Y))).det.eval z) ∘ (fun v : Fin 1 → ℂ => v 0) :=
    funext fun v => pd_eval hm Y v
  rw [e]
  exact ((lin (-(Ym hm Y))).det.differentiable.analyticAt _).comp
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).analyticAt _)

theorem pd_zero : pd hm Y 0 = 1 := by
  simp [pd]

theorem logpd_analytic : AnalyticAt ℂ (fun v => 2 * Complex.log (pd hm Y v)) 0 := by
  have h0 : pd hm Y 0 ∈ Complex.slitPlane := by
    rw [pd_zero]
    exact Complex.one_mem_slitPlane
  exact analyticAt_const.mul ((pd_analytic hm Y).clog h0)

theorem logpd_eq (v : Fin 1 → ℂ) : Real.log (‖pd hm Y v‖ ^ 2) = (2 * Complex.log (pd hm Y v)).re := by
  have h : (2 * Complex.log (pd hm Y v)).re = 2 * (Complex.log (pd hm Y v)).re := by
    simp [Complex.mul_re]
  rw [h, Complex.log_re, Real.log_pow]
  push_cast
  ring

theorem levi_logpd (w : Fin 1 → ℂ) : levi (fun v => Real.log (‖pd hm Y v‖ ^ 2)) 0 w = 0 := by
  have e : (fun v => Real.log (‖pd hm Y v‖ ^ 2)) = fun v => (2 * Complex.log (pd hm Y v)).re :=
    funext fun v => logpd_eq hm Y v
  rw [e]
  exact levi_re_analytic (logpd_analytic hm Y) w

theorem core_levi (hD : ∀ k, D k ≠ 0) :
    levi (fun v => Real.log |fY hm D Y v|) 0 (fun _ => 1) =
      ∑ a : Fin m, (D (Fin.castLE hm a))⁻¹ * Sa hm D Y a := by
  have hP : (∏ a : Fin m, D (Fin.castLE hm a)) ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => hD _
  have hfY0 : fY hm D Y 0 ≠ 0 := by rw [fY_zero]; exact hP
  have h0 := fn_zero_ne hm D Y hD
  have hcont : ContinuousAt (fY hm D Y) 0 := (contDiff_fY hm D Y).continuous.continuousAt
  have hpdc : ContinuousAt (pd hm Y) 0 := (pd_analytic hm Y).continuousAt
  have hev : (fun v => Real.log |fY hm D Y v|) =ᶠ[𝓝 0]
      fun v => Real.log |fn hm D Y v| + (-1) * Real.log (‖pd hm Y v‖ ^ 2) := by
    filter_upwards [hcont.eventually_ne hfY0, hpdc.eventually_ne (by rw [pd_zero]; exact one_ne_zero)]
      with v h1 h2
    have hp : ‖pd hm Y v‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 h2)
    rw [Real.log_abs, Real.log_abs, fn_eq, Real.log_mul hp h1]
    ring
  have hL1 : ContDiffAt ℝ 2 (fun v => Real.log |fn hm D Y v|) 0 := by
    have e : (fun v => Real.log |fn hm D Y v|) = fun v => Real.log (fn hm D Y v) := by
      funext v; rw [Real.log_abs]
    rw [e]
    exact (contDiff_fn hm D Y).contDiffAt.log h0
  have hL2 : ContDiffAt ℝ 2 (fun v => Real.log (‖pd hm Y v‖ ^ 2)) 0 := by
    rw [funext (logpd_eq hm Y)]
    exact Complex.reCLM.contDiff.contDiffAt.comp _
      ((logpd_analytic hm Y).contDiffAt.restrict_scalars ℝ)
  rw [levi_congr hev, levi_add_smul (-1) hL1 hL2, levi_logpd, levi_logfn hm D Y hD, levi_fn hm D Y hD,
    fn_zero, mul_zero, add_zero, mul_div_cancel_left₀ _ hP]

end ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
end
end

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf

open ReciprocityTheory.AnForm ReciprocityTheory.L2DbarEstimates Filter Topology

theorem snd_affine {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (h : F → ℝ) (c : F) (L : E →L[ℝ] F) (x : E) (hh : ContDiffAt ℝ 2 h (c + L x))
    (w : E) :
    fderiv ℝ (fderiv ℝ (fun y => h (c + L y))) x w w = fderiv ℝ (fderiv ℝ h) (c + L x) (L w) (L w) := by
  have hd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ h (c + L y) := by
    have h1 : ∀ᶠ z in 𝓝 (c + L x), DifferentiableAt ℝ h z :=
      (hh.eventually (by simp)).mono fun z hz => hz.differentiableAt (by norm_num)
    have hg : ContinuousAt (fun y => c + L y) x := (continuous_const.add L.continuous).continuousAt
    exact hg.eventually h1
  have heq : fderiv ℝ (fun y => h (c + L y)) =ᶠ[𝓝 x] fun y => (fderiv ℝ h (c + L y)).comp L := by
    filter_upwards [hd] with y hy
    have hgd : HasFDerivAt (fun y => c + L y) L y := (L.hasFDerivAt).const_add c
    exact (hy.hasFDerivAt.comp y hgd).fderiv
  rw [heq.fderiv_eq]
  have hd2 : DifferentiableAt ℝ (fderiv ℝ h) (c + L x) :=
    (hh.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hF : HasFDerivAt (fun y => fderiv ℝ h (c + L y)) ((fderiv ℝ (fderiv ℝ h) (c + L x)).comp L) x :=
    hd2.hasFDerivAt.comp x ((L.hasFDerivAt).const_add c)
  have hG : HasFDerivAt (fun y => (fderiv ℝ h (c + L y)).comp L)
      (((ContinuousLinearMap.compL ℝ E F ℝ).flip L).comp ((fderiv ℝ (fderiv ℝ h) (c + L x)).comp L)) x :=
    ((ContinuousLinearMap.compL ℝ E F ℝ).flip L).hasFDerivAt.comp x hF
  rw [hG.fderiv]
  rfl

def lineL {n : ℕ} (u : V n) : (Fin 1 → ℂ) →L[ℝ] V n :=
  ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).smulRight u).restrictScalars ℝ

theorem lineL_apply {n : ℕ} (u : V n) (v : Fin 1 → ℂ) : lineL u v = v 0 • u := rfl

theorem sum_bas_re {n : ℕ} (ξ : Fin n → ℂ) :
    (∑ k, ((ξ k).re • bas n k + (ξ k).im • (Complex.I • bas n k))) = WithLp.toLp 2 ξ := by
  have h : ∀ k, ((ξ k).re • bas n k + (ξ k).im • (Complex.I • bas n k)) = ξ k • bas n k := fun k => by
    rw [← Complex.coe_smul, ← Complex.coe_smul, smul_smul, ← add_smul]
    congr 1
    exact Complex.re_add_im (ξ k)
  have hsum : ∑ k, ξ k • bas n k = WithLp.toLp 2 ξ := by
    ext j
    simp [bas, PiLp.single_apply, Pi.single_apply, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq']
  simp_rw [h]
  exact hsum

theorem sum_bas_im {n : ℕ} (ξ : Fin n → ℂ) :
    (∑ k, ((ξ k).re • (Complex.I • bas n k) - (ξ k).im • bas n k)) = Complex.I • WithLp.toLp 2 ξ := by
  have h : ∀ k, ((ξ k).re • (Complex.I • bas n k) - (ξ k).im • bas n k) = Complex.I • (ξ k • bas n k) :=
      fun k => by
    rw [← Complex.coe_smul, ← Complex.coe_smul, smul_smul, smul_smul, ← sub_smul]
    congr 1
    apply Complex.ext <;> simp
  have hsum : ∑ k, ξ k • bas n k = WithLp.toLp 2 ξ := by
    ext j
    simp [bas, PiLp.single_apply, Pi.single_apply, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq']
  simp_rw [h, ← Finset.smul_sum, hsum]

theorem leviV_re_line {n : ℕ} (h : V n → ℝ) (z : V n) (hh : ContDiffAt ℝ 2 h z) (ξ : Fin n → ℂ) :
    (leviV n (fun y => (h y : ℂ)) z ξ).re =
      levi (fun v : Fin 1 → ℂ => h (z + lineL (WithLp.toLp 2 ξ) v)) 0 (fun _ => 1) := by
  have e := Y.LocalMaximumSecondDerivative.leviV_re_eq hh ξ
  rw [sum_bas_re, sum_bas_im] at e
  have L0 : z + lineL (WithLp.toLp 2 ξ) 0 = z := by simp [lineL_apply]
  have L1 : lineL (WithLp.toLp 2 ξ) (fun _ => 1) = WithLp.toLp 2 ξ := by simp [lineL_apply]
  have L2 : lineL (WithLp.toLp 2 ξ) (Complex.I • fun _ => 1) = Complex.I • WithLp.toLp 2 ξ := by
    simp [lineL_apply]
  have h0 : ContDiffAt ℝ 2 h (z + lineL (WithLp.toLp 2 ξ) 0) := by rw [L0]; exact hh
  have s1 := snd_affine h z (lineL (WithLp.toLp 2 ξ)) 0 h0 (fun _ => 1)
  have s2 := snd_affine h z (lineL (WithLp.toLp 2 ξ)) 0 h0 (Complex.I • fun _ => 1)
  rw [L0, L1] at s1
  rw [L0, L2] at s2
  unfold levi
  rw [s1, s2]
  linarith

end ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
end
end

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf

open Matrix ReciprocityTheory.ChartRestriction.G.FD

variable {r : ℕ}

theorem sum_eq_castLE {m : ℕ} (hm : m ≤ r) {M : Type} [AddCommMonoid M] (g : Fin r → M)
    (hg : ∀ k : Fin r, m ≤ (k : ℕ) → g k = 0) :
    ∑ k, g k = ∑ j : Fin m, g (Fin.castLE hm j) := by
  symm
  refine Fintype.sum_of_injective (Fin.castLE hm) (Fin.castLE_injective hm) _ g
    (fun k hk => hg k ?_) (fun j => rfl)
  by_contra h
  push_neg at h
  exact hk ⟨⟨k, h⟩, Fin.ext rfl⟩

theorem sub_LMU {m : ℕ} (hm : m ≤ r) (L M U : Matrix (Fin r) (Fin r) ℂ)
    (hL : ∀ a c : Fin r, c < a → L a c = 0) (hU : ∀ a c : Fin r, c < a → U a c = 0) :
    (Lᵀ * M * U).submatrix (Fin.castLE hm) (Fin.castLE hm) =
      (L.submatrix (Fin.castLE hm) (Fin.castLE hm))ᵀ * M.submatrix (Fin.castLE hm) (Fin.castLE hm) *
        U.submatrix (Fin.castLE hm) (Fin.castLE hm) := by
  ext i j
  simp only [submatrix_apply, Matrix.mul_apply, transpose_apply]
  rw [sum_eq_castLE hm (fun b => (∑ a, L a (Fin.castLE hm i) * M a b) * U b (Fin.castLE hm j))]
  · refine Finset.sum_congr rfl fun b _ => ?_
    congr 1
    rw [sum_eq_castLE hm (fun a => L a (Fin.castLE hm i) * M a (Fin.castLE hm b))]
    intro k hk
    have := i.isLt
    rw [hL k _ (by simp only [Fin.lt_def, Fin.coe_castLE]; omega), zero_mul]
  · intro k hk
    have := j.isLt
    rw [hU k _ (by simp only [Fin.lt_def, Fin.coe_castLE]; omega), mul_zero]

theorem lminor_LMU (L M U : Matrix (Fin r) (Fin r) ℂ)
    (hL : ∀ a c : Fin r, c < a → L a c = 0) (hU : ∀ a c : Fin r, c < a → U a c = 0) (k : Fin (r + 1)) :
    lminor (Lᵀ * M * U) k =
      (L.submatrix (Fin.castLE (Nat.le_of_lt_succ k.isLt)) (Fin.castLE (Nat.le_of_lt_succ k.isLt))).det *
        lminor M k *
        (U.submatrix (Fin.castLE (Nat.le_of_lt_succ k.isLt)) (Fin.castLE (Nat.le_of_lt_succ k.isLt))).det := by
  unfold lminor
  rw [sub_LMU _ L M U hL hU, det_mul, det_mul, det_transpose]

theorem lminor_map_conj (M : Matrix (Fin r) (Fin r) ℂ) (k : Fin (r + 1)) :
    lminor (M.map (starRingEnd ℂ)) k = starRingEnd ℂ (lminor M k) := by
  unfold lminor
  rw [RingHom.map_det]
  rfl

theorem tr_D_conj (A : Matrix (Fin r) (Fin r) ℂ) (D : Fin r → ℝ) :
    Aᵀ * (diagonal fun k => (D k : ℂ)) * A.map (starRingEnd ℂ) =
      (Aᴴ * (diagonal fun k => (D k : ℂ)) * A).map (starRingEnd ℂ) := by
  rw [Matrix.map_mul, Matrix.map_mul]
  congr 2
  · ext i j
    simp [Matrix.conjTranspose_apply]
  · ext i j
    by_cases h : i = j <;> simp [Matrix.diagonal_apply, h]

end ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
