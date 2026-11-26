module

public import GroundTheory.AutomorphicForms.GL2Classical.Adelic
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.HasModerateGrowthZero

@[expose] public section

section -- merged from GroundTheory.AutomorphicForms.GL2Classical.Iwasawa
open Matrix UpperHalfPlane

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2Classical

theorem det_fin_two_kmat (w : ℂ) : (!![w.re, -w.im; w.im, w.re] : Matrix (Fin 2) (Fin 2) ℝ).det =
    Complex.normSq w := by
  rw [Matrix.det_fin_two_of, Complex.normSq_apply]
  ring

def kGL (w : ℂ) (hw : w ≠ 0) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![w.re, -w.im; w.im, w.re] (by
    rw [det_fin_two_kmat]
    exact (Complex.normSq_pos.2 hw).ne')

@[simp]
theorem coe_kGL (w : ℂ) (hw : w ≠ 0) :
    (kGL w hw : Matrix (Fin 2) (Fin 2) ℝ) = !![w.re, -w.im; w.im, w.re] :=
  rfl

theorem det_kGL (w : ℂ) (hw : w ≠ 0) : (kGL w hw).det.val = Complex.normSq w := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, coe_kGL, det_fin_two_kmat]

theorem det_kGL_pos (w : ℂ) (hw : w ≠ 0) : 0 < (kGL w hw).det.val := by
  rw [det_kGL]
  exact Complex.normSq_pos.2 hw

theorem denom_kGL (w : ℂ) (hw : w ≠ 0) : denom (kGL w hw) (I : ℂ) = w := by
  rw [denom]
  apply Complex.ext <;> simp

theorem kGL_smul_I (w : ℂ) (hw : w ≠ 0) : kGL w hw • I = I := by
  apply UpperHalfPlane.ext
  rw [coe_smul_of_det_pos (det_kGL_pos w hw), denom_kGL, div_eq_iff hw]
  rw [num]
  apply Complex.ext <;> simp

def borelGL (z : ℍ) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![z.im, z.re; 0, 1] (by
    rw [Matrix.det_fin_two_of]
    simpa using z.im_pos.ne')

@[simp]
theorem coe_borelGL (z : ℍ) :
    (borelGL z : Matrix (Fin 2) (Fin 2) ℝ) = !![z.im, z.re; 0, 1] :=
  rfl

theorem det_borelGL (z : ℍ) : (borelGL z).det.val = z.im := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, coe_borelGL, Matrix.det_fin_two_of]
  ring

theorem det_borelGL_pos (z : ℍ) : 0 < (borelGL z).det.val := by
  rw [det_borelGL]
  exact z.im_pos

theorem denom_borelGL (z : ℍ) (w : ℂ) : denom (borelGL z) w = 1 := by
  simp [denom]

theorem borelGL_smul_I (z : ℍ) : borelGL z • I = z := by
  apply UpperHalfPlane.ext
  rw [coe_smul_of_det_pos (det_borelGL_pos z), denom_borelGL, div_one, num]
  apply Complex.ext <;> simp

theorem im_smul_I {h : GL (Fin 2) ℝ} (hpos : 0 < h.det.val) :
    (h • I).im = h.det.val / Complex.normSq (denom h (I : ℂ)) := by
  rw [im_smul_eq_div_normSq, abs_of_pos hpos, I_im, mul_one]

end GL2Classical

end

end GroundTheory.Automorphic
end

open NumberField Matrix CongruenceSubgroup UpperHalfPlane ModularForm
open scoped MatrixGroups ModularForm

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2Classical

open AdelicGLn AutomorphicForm

set_option linter.unusedSectionVars false

variable {N : ℕ} (k : ℤ)

theorem σ_of_det_pos {h : GL (Fin 2) ℝ} (hpos : 0 < h.det.val) (z : ℂ) : σ h z = z := by
  rw [σ, if_pos hpos]
  rfl

theorem denom_mul_of_det_pos (g : GL (Fin 2) ℝ) {h : GL (Fin 2) ℝ} (hpos : 0 < h.det.val) (z : ℍ) :
    denom (g * h) z = denom g ((h • z : ℍ) : ℂ) * denom h z := by
  rw [denom_cocycle_σ, σ_of_det_pos hpos]

theorem sqrt_div_normSq {a : ℝ} (w : ℂ) :
    Real.sqrt (a / Complex.normSq w) = Real.sqrt a / ‖w‖ := by
  rw [Real.sqrt_div' _ (Complex.normSq_nonneg w), Complex.normSq_eq_norm_sq,
    Real.sqrt_sq (norm_nonneg w)]

theorem div_norm_zpow_neg (w : ℂ) : (w / (‖w‖ : ℂ)) ^ (-k) = w ^ (-k) * (‖w‖ : ℂ) ^ k := by
  rw [div_eq_mul_inv, mul_zpow, _root_.inv_zpow', neg_neg]

def archLift (f : ℍ → ℂ) (h : GL (Fin 2) ℝ) : ℂ :=
  (Real.sqrt h.det.val : ℂ) ^ k * f (h • I) * denom h (I : ℂ) ^ (-k)

theorem archLift_mul_kGL (f : ℍ → ℂ) {h : GL (Fin 2) ℝ} (hpos : 0 < h.det.val) (w : ℂ)
    (hw : w ≠ 0) :
    archLift k f (h * kGL w hw) = (w / (‖w‖ : ℂ)) ^ (-k) * archLift k f h := by
  have hdet : (h * kGL w hw).det.val = h.det.val * Complex.normSq w := by
    rw [map_mul, Units.val_mul, det_kGL]
  have hsq : Real.sqrt (h.det.val * Complex.normSq w) = Real.sqrt h.det.val * ‖w‖ := by
    rw [Real.sqrt_mul hpos.le, Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg w)]
  rw [archLift, archLift, hdet, hsq, mul_smul, kGL_smul_I, denom_mul_of_det_pos _ (det_kGL_pos w hw),
    kGL_smul_I, denom_kGL, div_norm_zpow_neg, Complex.ofReal_mul, mul_zpow, mul_zpow]
  ring

theorem archLift_borelGL (f : ℍ → ℂ) (z : ℍ) :
    archLift k f (borelGL z) = (Real.sqrt z.im : ℂ) ^ k * f z := by
  rw [archLift, det_borelGL, borelGL_smul_I, denom_borelGL, _root_.one_zpow, mul_one]

variable (N) [NeZero N]

def decompGL (g : AdelicGL ℚ 2) : GL (Fin 2) ℝ :=
  Classical.choose (Classical.choose_spec (exists_decomposition N g))

theorem decompGL_spec (g : AdelicGL ℚ 2) :
    0 < (decompGL N g).det.val ∧ ∃ γ : GL (Fin 2) ℚ, ∃ u ∈ Gamma0Level N,
      g = diagonal ℚ 2 γ * realEmb (decompGL N g) * finEmb ℚ 2 u :=
  ⟨(Classical.choose_spec (Classical.choose_spec (exists_decomposition N g))).1,
    Classical.choose (exists_decomposition N g),
    (Classical.choose_spec (Classical.choose_spec (exists_decomposition N g))).2⟩

variable {N k}

variable (N k)

variable {N k}

variable (k)

variable {k}

variable (N k)

variable {N k}

end GL2Classical

end

end GroundTheory.Automorphic
