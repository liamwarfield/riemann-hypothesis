module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.EigLocal

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.SymZeroCommFrameMatrix
section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.InvCancelRight
section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.FrameZeroApply
noncomputable section

open Matrix
open scoped Kronecker ContDiff ComplexConjugate

namespace PositivityTheory.RgBcC

open PositivityTheory.RgTw (Mat hb)

variable {n : ℕ} {lam : Fin n → ℤ}

theorem cjL_apply (A : Matrix (Ix n lam) (Ix n lam) ℂ) : cjL lam A = sqQ lam * clm lam A * Ring.inverse (sqQ lam) := by
  simp [cjL, mul_assoc]
  rfl

theorem clm_mul' (A B : Matrix (Ix n lam) (Ix n lam) ℂ) : clm lam (A * B) = clm lam A * clm lam B := map_mul _ A B

theorem clm_one' : clm lam (1 : Matrix (Ix n lam) (Ix n lam) ℂ) = 1 := map_one _

theorem cj_mul (hu : IsUnit (sqQ lam)) (A B : Matrix (Ix n lam) (Ix n lam) ℂ) :
    cjL lam A * cjL lam B = cjL lam (A * B) := by
  rw [cjL_apply, cjL_apply, cjL_apply, clm_mul']
  have h : Ring.inverse (sqQ lam) * sqQ lam = 1 := Ring.inverse_mul_cancel _ hu
  calc sqQ lam * clm lam A * Ring.inverse (sqQ lam) * (sqQ lam * clm lam B * Ring.inverse (sqQ lam))
      = sqQ lam * clm lam A * (Ring.inverse (sqQ lam) * sqQ lam) * clm lam B * Ring.inverse (sqQ lam) := by
        simp only [mul_assoc]
    _ = sqQ lam * (clm lam A * clm lam B) * Ring.inverse (sqQ lam) := by rw [h, mul_one]; simp only [mul_assoc]

theorem cj_one (hu : IsUnit (sqQ lam)) : cjL lam 1 = 1 := by
  rw [cjL_apply, clm_one', mul_one]
  exact Ring.mul_inverse_cancel _ hu

theorem lefε_apply (H : Mat n) : lefε n lam H = cjL lam (creL n (cf n H) ⊗ₖ (1 : Matrix (Jd n lam × Jd n lam) (Jd n lam × Jd n lam) ℂ)) := rfl

theorem lefι_apply (H : Mat n) : lefι n lam H = cjL lam (annL n (cf n H) ⊗ₖ (1 : Matrix (Jd n lam × Jd n lam) (Jd n lam × Jd n lam) ℂ)) := rfl

theorem lefFr_apply (x : Mat n) : lefFr n lam x = cjL lam (fr0 lam x) := rfl

theorem frame_zero_apply (x : Mat n) : fr0 lam x = gamM (Mt x⁻¹)ᵀ ⊗ₖ rhoW lam x := rfl

end PositivityTheory.RgBcC
end
end

noncomputable section

open Matrix
open scoped Kronecker ContDiff ComplexConjugate

namespace PositivityTheory.RgBcC

open PositivityTheory.RgTw (Mat hb)

variable {n : ℕ} {lam : Fin n → ℤ}

theorem cj_smul_one (hu : IsUnit (sqQ lam)) (c : ℂ) : cjL lam (c • (1 : Matrix (Ix n lam) (Ix n lam) ℂ)) = c • 1 := by
  rw [map_smul, cj_one hu]

theorem herm_conj {x H : Mat n} (hH : H.IsHermitian) : (x * H * xᴴ).IsHermitian := by
  exact Matrix.isHermitian_mul_mul_conjTranspose x hH

theorem herm_conj' {x H : Mat n} (hH : H.IsHermitian) : (xᴴ * H * x).IsHermitian := by
  exact Matrix.isHermitian_conjTranspose_mul_mul x hH

theorem car_f (hu : IsUnit (sqQ lam)) (hB : Car) (hP : CfPair) (H H' : Mat n) (hH : H.IsHermitian)
    (hH' : H'.IsHermitian) : lefε n lam H * lefι n lam H' + lefι n lam H' * lefε n lam H = (H * H').trace • 1 := by
  rw [lefε_apply, lefι_apply, cj_mul hu, cj_mul hu, ← map_add (f := _), ← mul_kronecker_mul, ← mul_kronecker_mul, mul_one,
    ← add_kronecker, add_comm (creL n (cf n H) * annL n (cf n H')), hB n (cf n H) (cf n H')]
  have e : cf n H' ⬝ᵥ cf n H = (H * H').trace := by
    rw [← hP n H H' hH hH', dotProduct]
    exact Finset.sum_congr rfl fun m _ => mul_comm _ _
  rw [e, smul_kronecker, one_kronecker_one, cj_smul_one hu]

theorem inv_cancel_left' {x : Mat n} (hx : x ∈ GLs n) : x⁻¹ * x = 1 :=
  Matrix.nonsing_inv_mul x (isUnit_iff_ne_zero.mpr hx)

theorem inv_cancel_right' {x : Mat n} (hx : x ∈ GLs n) : x * x⁻¹ = 1 :=
  Matrix.mul_nonsing_inv x (isUnit_iff_ne_zero.mpr hx)

theorem frι_f (hu : IsUnit (sqQ lam)) (hC : GamCre) (hM : MtLaws) (x : Mat n) (hx : x ∈ GLs n) (H : Mat n)
    (hH : H.IsHermitian) : lefFr n lam x * lefι n lam H = lefι n lam (x * H * xᴴ) * lefFr n lam x := by
  rw [lefFr_apply, lefι_apply, lefι_apply, cj_mul hu, cj_mul hu, frame_zero_apply, ← mul_kronecker_mul, ← mul_kronecker_mul,
    mul_one, one_mul]
  congr 2
  rw [(hC n _ 0 (cf n (x * H * xᴴ))).2, transpose_transpose, (hM n).2.2.1 x⁻¹ _ (herm_conj hH)]
  have h1 := inv_cancel_left' hx
  have h2 : xᴴ * x⁻¹ᴴ = 1 := by rw [← conjTranspose_mul, h1, conjTranspose_one]
  have key : x⁻¹ * (x * H * xᴴ) * x⁻¹ᴴ = H := by
    calc x⁻¹ * (x * H * xᴴ) * x⁻¹ᴴ = (x⁻¹ * x) * H * (xᴴ * x⁻¹ᴴ) := by simp only [mul_assoc]
      _ = H := by rw [h1, h2, one_mul, mul_one]
  rw [key]

theorem frε_f (hu : IsUnit (sqQ lam)) (hC : GamCre) (hM : MtLaws) (x : Mat n) (hx : x ∈ GLs n) (H : Mat n)
    (hH : H.IsHermitian) : lefε n lam H * lefFr n lam x = lefFr n lam x * lefε n lam (xᴴ * H * x) := by
  rw [lefFr_apply, lefε_apply, lefε_apply, cj_mul hu, cj_mul hu, frame_zero_apply, ← mul_kronecker_mul, ← mul_kronecker_mul,
    mul_one, one_mul]
  congr 2
  rw [(hC n _ (cf n (xᴴ * H * x)) 0).1, (hM n).2.2.2 x⁻¹ _ (herm_conj' hH)]
  have h1 := inv_cancel_right' hx
  have h2 : x⁻¹ᴴ * xᴴ = 1 := by rw [← conjTranspose_mul, h1, conjTranspose_one]
  have key : x⁻¹ᴴ * (xᴴ * H * x) * x⁻¹ = H := by
    calc x⁻¹ᴴ * (xᴴ * H * x) * x⁻¹ = (x⁻¹ᴴ * xᴴ) * H * (x * x⁻¹) := by simp only [mul_assoc]
      _ = H := by rw [h1, h2, one_mul, mul_one]
  rw [key]

end PositivityTheory.RgBcC
end
end

noncomputable section

open Matrix
open scoped Kronecker ContDiff ComplexConjugate

namespace PositivityTheory.RgBcC

open PositivityTheory.RgTw (Mat hb)

variable {n : ℕ} {lam : Fin n → ℤ}

theorem lefΓ_apply : lefΓ n lam = cjL lam (gamM (-1 : Matrix (Md n) (Md n) ℂ) ⊗ₖ (1 : Matrix (Jd n lam × Jd n lam) (Jd n lam × Jd n lam) ℂ)) := rfl

theorem lefS_apply (s : ℝ) : lefS n lam s =
    cjL lam (gamM ((s : ℂ) • (1 : Matrix (Md n) (Md n) ℂ)) ⊗ₖ (1 : Matrix (Jd n lam × Jd n lam) (Jd n lam × Jd n lam) ℂ)) := rfl

theorem lefT_apply : lefT n lam = cjL lam ((1 : Matrix (Finset (Md n)) (Finset (Md n)) ℂ) ⊗ₖ swapJ lam) := rfl

theorem lefS_zero : lefS n lam 0 =
    cjL lam (gamM (0 : Matrix (Md n) (Md n) ℂ) ⊗ₖ (1 : Matrix (Jd n lam × Jd n lam) (Jd n lam × Jd n lam) ℂ)) := by
  rw [lefS_apply, Complex.ofReal_zero, zero_smul]

theorem neg_kron' {ι₁ ι₂ : Type*} (A : Matrix ι₁ ι₁ ℂ) (B : Matrix ι₂ ι₂ ℂ) : (-A) ⊗ₖ B = -(A ⊗ₖ B) := by
  ext i j; simp [kroneckerMap_apply, neg_mul]

theorem smul_one_mulVec' {ι₁ : Type*} [Fintype ι₁] [DecidableEq ι₁] (s : ℂ) (v : ι₁ → ℂ) :
    (s • (1 : Matrix ι₁ ι₁ ℂ)) *ᵥ v = s • v := by
  rw [Matrix.smul_mulVec, one_mulVec]

section

variable (hu : IsUnit (sqQ lam)) (hG : GamMul) (hC : GamCre)
include hu hG

theorem gam_mul' (g h : Matrix (Md n) (Md n) ℂ) : gamM g * gamM h = gamM (g * h) := ((hG n).2 g h).symm

theorem Γsq_f : lefΓ n lam * lefΓ n lam = 1 := by
  rw [lefΓ_apply, cj_mul hu, ← mul_kronecker_mul, gam_mul' hu hG, neg_one_mul, neg_neg, (hG n).1, mul_one,
    one_kronecker_one, cj_one hu]

include hC in
theorem Γε_f (H : Mat n) : lefΓ n lam * lefε n lam H = -(lefε n lam H * lefΓ n lam) := by
  have hk : gamM (-1 : Matrix (Md n) (Md n) ℂ) * creL n (cf n H) = -(creL n (cf n H) * gamM (-1 : Matrix (Md n) (Md n) ℂ)) := by
    rw [(hC n (-1) (cf n H) 0).1, Matrix.neg_mulVec, Matrix.one_mulVec, map_neg, neg_mul]
  rw [lefΓ_apply, lefε_apply, cj_mul hu, cj_mul hu, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, hk,
    neg_kron', map_neg]

include hC in
theorem Γι_f (H : Mat n) : lefΓ n lam * lefι n lam H = -(lefι n lam H * lefΓ n lam) := by
  have hk : gamM (-1 : Matrix (Md n) (Md n) ℂ) * annL n (cf n H) = -(annL n (cf n H) * gamM (-1 : Matrix (Md n) (Md n) ℂ)) := by
    rw [(hC n (-1) 0 (cf n H)).2, Matrix.transpose_neg, Matrix.transpose_one, Matrix.neg_mulVec, Matrix.one_mulVec,
      map_neg, mul_neg, neg_neg]
  rw [lefΓ_apply, lefι_apply, cj_mul hu, cj_mul hu, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, hk,
    neg_kron', map_neg]

theorem ΓFr_f (x : Mat n) : lefΓ n lam * lefFr n lam x = lefFr n lam x * lefΓ n lam := by
  rw [lefΓ_apply, lefFr_apply, cj_mul hu, cj_mul hu, frame_zero_apply, ← mul_kronecker_mul, ← mul_kronecker_mul,
    gam_mul' hu hG, gam_mul' hu hG, neg_one_mul, mul_neg_one, one_mul, mul_one]

theorem ΓT_f : lefΓ n lam * lefT n lam = lefT n lam * lefΓ n lam := by
  rw [lefΓ_apply, lefT_apply, cj_mul hu, cj_mul hu, ← mul_kronecker_mul, ← mul_kronecker_mul, one_mul, mul_one,
    one_mul, mul_one]

theorem sym_one_eq_one : lefS n lam 1 = 1 := by
  rw [lefS_apply, Complex.ofReal_one, one_smul, (hG n).1, one_kronecker_one, cj_one hu]

include hC in
theorem Sε_f (s : ℝ) (H : Mat n) : lefS n lam s * lefε n lam H = (s : ℂ) • (lefε n lam H * lefS n lam s) := by
  rw [lefS_apply, lefε_apply, cj_mul hu, cj_mul hu, ← mul_kronecker_mul, ← mul_kronecker_mul, (hC n _ _ 0).1,
    smul_one_mulVec', map_smul, smul_mul_assoc, smul_kronecker, map_smul]

theorem SΓ_f (s : ℝ) : lefΓ n lam * lefS n lam s = lefS n lam s * lefΓ n lam := by
  rw [lefS_apply, lefΓ_apply, cj_mul hu, cj_mul hu, ← mul_kronecker_mul, ← mul_kronecker_mul, gam_mul' hu hG,
    gam_mul' hu hG, mul_neg_one, neg_one_mul]

theorem S0sq_f : lefS n lam 0 * lefS n lam 0 = lefS n lam 0 := by
  rw [lefS_zero, cj_mul hu, ← mul_kronecker_mul, gam_mul' hu hG, mul_zero, mul_one]

theorem S0Γ_f : lefΓ n lam * lefS n lam 0 = lefS n lam 0 := by
  rw [lefS_zero, lefΓ_apply, cj_mul hu, ← mul_kronecker_mul, gam_mul' hu hG, mul_zero, mul_one]

theorem sym_zero_comm_frame_matrix (x : Mat n) : lefS n lam 0 * lefFr n lam x = lefFr n lam x * lefS n lam 0 := by
  rw [lefS_zero, lefFr_apply, cj_mul hu, cj_mul hu, frame_zero_apply, ← mul_kronecker_mul, ← mul_kronecker_mul,
    gam_mul' hu hG, gam_mul' hu hG, zero_mul, mul_zero, one_mul, mul_one]

theorem time_comm_sym_zero_matrix : lefT n lam * lefS n lam 0 = lefS n lam 0 * lefT n lam := by
  rw [lefS_zero, lefT_apply, cj_mul hu, cj_mul hu, ← mul_kronecker_mul, ← mul_kronecker_mul, one_mul, mul_one,
    one_mul, mul_one]

end

section

variable (hu : IsUnit (sqQ lam)) (hS : SwapLaws)
include hu hS

theorem Tsq_f : lefT n lam * lefT n lam = 1 := by
  rw [lefT_apply, cj_mul hu, ← mul_kronecker_mul, mul_one, (hS n lam).1, one_kronecker_one, cj_one hu]

theorem Tε_f (H : Mat n) : lefT n lam * lefε n lam H = lefε n lam H * lefT n lam := by
  rw [lefT_apply, lefε_apply, cj_mul hu, cj_mul hu, ← mul_kronecker_mul, ← mul_kronecker_mul, one_mul, mul_one,
    one_mul, mul_one]

theorem Tι_f (H : Mat n) : lefT n lam * lefι n lam H = lefι n lam H * lefT n lam := by
  rw [lefT_apply, lefι_apply, cj_mul hu, cj_mul hu, ← mul_kronecker_mul, ← mul_kronecker_mul, one_mul, mul_one,
    one_mul, mul_one]

theorem unit_inv_conj (k : Matrix.unitaryGroup (Fin n) ℂ) : (k.1ᴴ)⁻¹ = k.1 := by
  apply Matrix.inv_eq_right_inv
  have h := Unitary.star_mul_self_of_mem k.2
  rwa [Matrix.star_eq_conjTranspose] at h

theorem isUnit_det_unitary (k : Matrix.unitaryGroup (Fin n) ℂ) : IsUnit (k.1).det := by
  apply Matrix.isUnit_det_of_right_inverse (B := (k.1)ᴴ)
  have h := Unitary.mul_star_self_of_mem k.2
  rwa [Matrix.star_eq_conjTranspose] at h

theorem swap_rhoW_k (k : Matrix.unitaryGroup (Fin n) ℂ) : swapJ lam * rhoW lam k.1 = rhoW lam k.1 * swapJ lam := by
  have := (hS n lam).2.2.1 k.1 (isUnit_det_unitary hu hS k)
  rwa [unit_inv_conj hu hS k] at this

theorem TK_f (k : Matrix.unitaryGroup (Fin n) ℂ) : lefT n lam * lefFr n lam k.1 = lefFr n lam k.1 * lefT n lam := by
  rw [lefT_apply, lefFr_apply, frame_zero_apply, cj_mul hu, cj_mul hu, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    swap_rhoW_k hu hS k, one_mul, mul_one]

theorem S0θ_f (hG : GamMul) (x : Mat n) (hx : x ∈ GLs n) :
    lefT n lam * lefFr n lam (xᴴ⁻¹) * lefS n lam 0 = lefFr n lam x * lefT n lam * lefS n lam 0 := by
  have hd : IsUnit x.det := isUnit_iff_ne_zero.mpr hx
  rw [lefT_apply, lefFr_apply, lefFr_apply, frame_zero_apply, frame_zero_apply, lefS_zero, cj_mul hu, cj_mul hu, cj_mul hu, cj_mul hu]
  simp only [← Matrix.mul_kronecker_mul, ← (hG n).2, mul_zero, one_mul, mul_one]
  rw [(hS n lam).2.2.1 x hd]

end

end PositivityTheory.RgBcC
end
end

noncomputable section

open Matrix
open scoped Kronecker ContDiff ComplexConjugate

namespace PositivityTheory.RgBcC

open PositivityTheory.RgTw (Mat hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def TDOf : Prop := Avg → HbOrtho → SwapLaws → MatrixFrechetDerivativeAtZero → WedgeDer → ∀ (n : ℕ) (lam : Fin n → ℤ),
  lefT n lam * (∑ p, lefε n lam (hb p) * fderiv ℝ (lefFr n lam) 1 (hb p)) =
    -((∑ p, lefε n lam (hb p) * fderiv ℝ (lefFr n lam) 1 (hb p)) * lefT n lam)

def EigOf : Prop := Avg → GamMul → RmLaws → RmHol → RmAnti → EigProd → EigLocal → ∀ (n : ℕ) (lam : Fin n → ℤ),
  Antitone lam → ∀ w : EV n lam, IsEig (infOf lam) fun x => lefFr n lam x⁻¹ (lefS n lam 0 w)

end PositivityTheory.RgBcC
