module

public import Formalism.SharpRestriction.CuspSpanNormBounds.OnePlaceEstimates

@[expose] public section

section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.TrD
section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.DMiMulVecApply
section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.ContinuousCjIT
open MeasureTheory Matrix Finset

noncomputable section

namespace Formalism.MainNotions.FrameBoundFromBesselTorus

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates

def tF (r : ℕ) (κ τ : ℝ) (a : ℕ) : ℝ := τ * κ ^ (r - a)

def tV (k r : ℕ) (κ τ : ℝ) (i : Fin (2 * r + k + 1)) : ℝ :=
  if i.val < r then tF r κ τ i.val
  else if i.val ≤ r + k then 1 else (tF r κ τ (2 * r + k - i.val))⁻¹

def dM (k r : ℕ) (κ τ : ℝ) : Mx k r := Matrix.diagonal fun i => ((tV k r κ τ i : ℝ) : ℂ)

def dMi (k r : ℕ) (κ τ : ℝ) : Mx k r := Matrix.diagonal fun i => (((tV k r κ τ i)⁻¹ : ℝ) : ℂ)

def cj (k r : ℕ) (κ τ : ℝ) (x : Mx k r) : Mx k r := dMi k r κ τ * x * dM k r κ τ

def cjI (k r : ℕ) (κ τ : ℝ) (x : Mx k r) : Mx k r := dM k r κ τ * x * dMi k r κ τ

def cjT (k r : ℕ) (κ τ : ℝ) (x : Mt k r) : Mt k r := fun i j => cj k r κ τ (Matrix.of x) i j

def cjIT (k r : ℕ) (κ τ : ℝ) (x : Mt k r) : Mt k r := fun i j => cjI k r κ τ (Matrix.of x) i j

section Alg

variable {k r : ℕ} {κ τ : ℝ}

theorem tF_pos (hκ : 0 < κ) (hτ : 0 < τ) (a : ℕ) : 0 < tF r κ τ a := mul_pos hτ (pow_pos hκ _)

theorem tV_pos (hκ : 0 < κ) (hτ : 0 < τ) (i : Fin (2 * r + k + 1)) : 0 < tV k r κ τ i := by
  unfold tV; split_ifs
  · exact tF_pos hκ hτ _
  · exact one_pos
  · exact inv_pos.mpr (tF_pos hκ hτ _)

theorem dMi_mul_dM (hκ : 0 < κ) (hτ : 0 < τ) : dMi k r κ τ * dM k r κ τ = 1 := by
  rw [dMi, dM, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext i
  rw [← Complex.ofReal_mul, inv_mul_cancel₀ (tV_pos hκ hτ i).ne', Complex.ofReal_one]

theorem dM_mul_dMi (hκ : 0 < κ) (hτ : 0 < τ) : dM k r κ τ * dMi k r κ τ = 1 := by
  rw [dMi, dM, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext i
  rw [← Complex.ofReal_mul, mul_inv_cancel₀ (tV_pos hκ hτ i).ne', Complex.ofReal_one]

theorem cj_apply (x : Mx k r) (i j : Fin (2 * r + k + 1)) :
    cj k r κ τ x i j = ((((tV k r κ τ i)⁻¹ * tV k r κ τ j : ℝ)) : ℂ) * x i j := by
  simp only [cj, dMi, dM, Matrix.mul_diagonal, Matrix.diagonal_mul]
  push_cast; ring

theorem cjI_apply (x : Mx k r) (i j : Fin (2 * r + k + 1)) :
    cjI k r κ τ x i j = (((tV k r κ τ i * (tV k r κ τ j)⁻¹ : ℝ)) : ℂ) * x i j := by
  simp only [cjI, dMi, dM, Matrix.mul_diagonal, Matrix.diagonal_mul]
  push_cast; ring

theorem cj_cjI (hκ : 0 < κ) (hτ : 0 < τ) (x : Mx k r) : cj k r κ τ (cjI k r κ τ x) = x := by
  simp only [cj, cjI, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (dMi k r κ τ) (dM k r κ τ), dMi_mul_dM hκ hτ, Matrix.one_mul, Matrix.mul_one]

theorem cjI_cj (hκ : 0 < κ) (hτ : 0 < τ) (x : Mx k r) : cjI k r κ τ (cj k r κ τ x) = x := by
  simp only [cj, cjI, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (dM k r κ τ) (dMi k r κ τ), dM_mul_dMi hκ hτ, Matrix.one_mul, Matrix.mul_one]

theorem cj_mul (hκ : 0 < κ) (hτ : 0 < τ) (x y : Mx k r) :
    cj k r κ τ (x * y) = cj k r κ τ x * cj k r κ τ y := by
  simp only [cj, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (dM k r κ τ) (dMi k r κ τ), dM_mul_dMi hκ hτ, Matrix.one_mul]

theorem dM_inv (hκ : 0 < κ) (hτ : 0 < τ) : (dM k r κ τ)⁻¹ = dMi k r κ τ :=
  Matrix.inv_eq_left_inv (dMi_mul_dM hκ hτ)

theorem dMi_inv (hκ : 0 < κ) (hτ : 0 < τ) : (dMi k r κ τ)⁻¹ = dM k r κ τ :=
  Matrix.inv_eq_left_inv (dM_mul_dMi hκ hτ)

theorem cj_inv (hκ : 0 < κ) (hτ : 0 < τ) (x : Mx k r) : cj k r κ τ x⁻¹ = (cj k r κ τ x)⁻¹ := by
  rw [cj, cj, Matrix.mul_inv_rev, Matrix.mul_inv_rev, dM_inv hκ hτ, dMi_inv hκ hτ, Matrix.mul_assoc]

theorem of_cjT (x : Mt k r) : Matrix.of (cjT k r κ τ x) = cj k r κ τ (Matrix.of x) := by
  ext i j; rfl

theorem of_cjIT (x : Mt k r) : Matrix.of (cjIT k r κ τ x) = cjI k r κ τ (Matrix.of x) := by
  ext i j; rfl

theorem cjT_cjIT (hκ : 0 < κ) (hτ : 0 < τ) (x : Mt k r) : cjT k r κ τ (cjIT k r κ τ x) = x := by
  funext i j; simp only [cjT, of_cjIT, cj_cjI hκ hτ]; rfl

theorem cjIT_cjT (hκ : 0 < κ) (hτ : 0 < τ) (x : Mt k r) : cjIT k r κ τ (cjT k r κ τ x) = x := by
  funext i j; simp only [cjIT, of_cjT, cjI_cj hκ hτ]; rfl

theorem continuous_cjT : Continuous (cjT k r κ τ) := by
  have : cjT k r κ τ = fun x i j => ((((tV k r κ τ i)⁻¹ * tV k r κ τ j : ℝ)) : ℂ) * x i j := by
    funext x i j; exact cj_apply (Matrix.of x) i j
  rw [this]; fun_prop

theorem continuous_cjIT : Continuous (cjIT k r κ τ) := by
  have : cjIT k r κ τ = fun x i j => (((tV k r κ τ i * (tV k r κ τ j)⁻¹ : ℝ)) : ℂ) * x i j := by
    funext x i j; exact cjI_apply (Matrix.of x) i j
  rw [this]; fun_prop

def cjE (hκ : 0 < κ) (hτ : 0 < τ) : Mt k r ≃ᵐ Mt k r where
  toFun := cjT k r κ τ
  invFun := cjIT k r κ τ
  left_inv := cjIT_cjT hκ hτ
  right_inv := cjT_cjIT hκ hτ
  measurable_toFun := continuous_cjT.measurable
  measurable_invFun := continuous_cjIT.measurable

theorem tV_mul_of_Hpk (hκ : 0 < κ) (hτ : 0 < τ) (i j : Fin (2 * r + k + 1)) (h : Hpk k r i j ≠ 0) :
    tV k r κ τ i * tV k r κ τ j = 1 := by
  have hti := tF_pos (r := r) hκ hτ i.val
  have htj := tF_pos (r := r) hκ hτ j.val
  unfold tV
  by_cases h1 : i.val < r ∧ i.val + j.val = 2 * r + k
  · have e : 2 * r + k - j.val = i.val := by omega
    rw [if_pos h1.1, if_neg (by omega), if_neg (by omega), e, mul_inv_cancel₀ hti.ne']
  by_cases h2 : j.val < r ∧ i.val + j.val = 2 * r + k
  · have e : 2 * r + k - i.val = j.val := by omega
    rw [if_neg (by omega), if_neg (by omega), if_pos h2.1, e, inv_mul_cancel₀ htj.ne']
  by_cases h3 : r ≤ i.val ∧ i.val ≤ r + k ∧ i = j
  · rw [h3.2.2]; rw [if_neg (by omega), if_pos (by omega), mul_one]
  · exfalso; apply h; unfold Hpk; rw [if_neg h1, if_neg h2, if_neg h3]

theorem diag_mem_UH (s : Fin (2 * r + k + 1) → ℝ)
    (hs : ∀ i j, Hpk k r i j ≠ 0 → s i * s j = 1) :
    Matrix.diagonal (fun i => ((s i : ℝ) : ℂ)) ∈ UH (Hpk k r) := by
  show (Matrix.diagonal fun i => ((s i : ℝ) : ℂ))ᴴ * Hpk k r * Matrix.diagonal (fun i => ((s i : ℝ) : ℂ)) = Hpk k r
  rw [Matrix.diagonal_conjTranspose]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h : Hpk k r i j = 0
  · rw [h]; simp
  · have := hs i j h
    simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
    calc (s i : ℂ) * Hpk k r i j * (s j : ℂ) = ((s i * s j : ℝ) : ℂ) * Hpk k r i j := by push_cast; ring
      _ = Hpk k r i j := by rw [this]; simp

theorem dM_mem_UH (hκ : 0 < κ) (hτ : 0 < τ) : dM k r κ τ ∈ UH (Hpk k r) :=
  diag_mem_UH _ (tV_mul_of_Hpk hκ hτ)

theorem dMi_mem_UH (hκ : 0 < κ) (hτ : 0 < τ) : dMi k r κ τ ∈ UH (Hpk k r) := by
  refine diag_mem_UH _ fun i j h => ?_
  rw [← mul_inv, tV_mul_of_Hpk hκ hτ i j h, inv_one]

theorem UH_mul {a b : Mx k r} (ha : a ∈ UH (Hpk k r)) (hb : b ∈ UH (Hpk k r)) : a * b ∈ UH (Hpk k r) := by
  show (a * b)ᴴ * Hpk k r * (a * b) = Hpk k r
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have hb' : bᴴ * Hpk k r * b = Hpk k r := hb
  rw [Matrix.conjTranspose_mul]
  calc bᴴ * aᴴ * Hpk k r * (a * b) = bᴴ * (aᴴ * Hpk k r * a) * b := by simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [ha', hb']

theorem cj_mem_UH_iff (hκ : 0 < κ) (hτ : 0 < τ) (g : Mx k r) :
    cj k r κ τ g ∈ UH (Hpk k r) ↔ g ∈ UH (Hpk k r) := by
  constructor
  · intro h
    have := UH_mul (UH_mul (dM_mem_UH hκ hτ) h) (dMi_mem_UH hκ hτ)
    rwa [← cjI, cjI_cj hκ hτ] at this
  · intro h; exact UH_mul (UH_mul (dMi_mem_UH hκ hτ) h) (dM_mem_UH hκ hτ)

end Alg

end Formalism.MainNotions.FrameBoundFromBesselTorus
end
end

open MeasureTheory Matrix Finset

noncomputable section

namespace Formalism.MainNotions.FrameBoundFromBesselTorus

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates

section Alg2

variable {k r : ℕ} {κ τ : ℝ}

theorem tV_eI (a : Fin r) : tV k r κ τ (eI k r a) = tF r κ τ a.val := by
  unfold tV eI; rw [if_pos a.isLt]

theorem tV_esI (a : Fin r) : tV k r κ τ (esI k r a) = (tF r κ τ a.val)⁻¹ := by
  unfold tV esI
  have h := a.isLt
  rw [if_neg (by simp only; omega), if_neg (by simp only; omega)]
  congr 2; simp only; omega

theorem tV_wb (i : Fin (2 * r + k + 1)) (h1 : r ≤ i.val) (h2 : i.val ≤ r + k) : tV k r κ τ i = 1 := by
  unfold tV; rw [if_neg (by omega), if_pos h2]

theorem dM_mulVec_apply (v : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    (dM k r κ τ *ᵥ v) i = ((tV k r κ τ i : ℝ) : ℂ) * v i := by
  rw [dM, Matrix.mulVec_diagonal]

theorem dMi_mulVec_apply (v : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    (dMi k r κ τ *ᵥ v) i = (((tV k r κ τ i)⁻¹ : ℝ) : ℂ) * v i := by
  rw [dMi, Matrix.mulVec_diagonal]

theorem dM_mulVec_wb {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) : dM k r κ τ *ᵥ z = z := by
  funext i; rw [dM_mulVec_apply]
  by_cases h : i.val < r ∨ r + k < i.val
  · rw [hz i h, mul_zero]
  · rw [tV_wb i (by omega) (by omega)]; simp

theorem dMi_mulVec_wb {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) : dMi k r κ τ *ᵥ z = z := by
  funext i; rw [dMi_mulVec_apply]
  by_cases h : i.val < r ∨ r + k < i.val
  · rw [hz i h, mul_zero]
  · rw [tV_wb i (by omega) (by omega)]; simp

theorem dM_mulVec_bvec (i : Fin (2 * r + k + 1)) :
    dM k r κ τ *ᵥ bvec i = ((tV k r κ τ i : ℝ) : ℂ) • bvec i := by
  funext j; rw [dM_mulVec_apply, Pi.smul_apply, smul_eq_mul]
  by_cases h : j = i
  · subst h; rfl
  · simp [bvec, h]

theorem dMi_mulVec_bvec (i : Fin (2 * r + k + 1)) :
    dMi k r κ τ *ᵥ bvec i = (((tV k r κ τ i)⁻¹ : ℝ) : ℂ) • bvec i := by
  funext j; rw [dMi_mulVec_apply, Pi.smul_apply, smul_eq_mul]
  by_cases h : j = i
  · subst h; rfl
  · simp [bvec, h]

theorem inWb_smul {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (a : ℂ) : inWb k r (a • z) := by
  intro i hi; rw [Pi.smul_apply, hz i hi, smul_zero]

theorem cj_mulVec (x : Mx k r) (v : Fin (2 * r + k + 1) → ℂ) :
    cj k r κ τ x *ᵥ v = dMi k r κ τ *ᵥ (x *ᵥ (dM k r κ τ *ᵥ v)) := by
  rw [cj, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

theorem dM_mulVec_fvec {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (a : Fin (r + 1)) :
    dM k r κ τ *ᵥ fvec k r ((τ : ℂ) • z) a = ((tF r κ τ a.val : ℝ) : ℂ) • fvec k r z a := by
  unfold fvec
  by_cases h : a.val < r
  · rw [dite_eq_left h, dite_eq_left h, dM_mulVec_bvec, tV_eI]
  · rw [dite_eq_right h, dite_eq_right h, dM_mulVec_wb (inWb_smul hz _)]
    have : a.val = r := by omega
    simp [tF, this]

theorem ell_cj (hκ : 0 < κ) (hτ : 0 < τ) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (x : Mx k r) :
    ell k r ((τ : ℂ) • z) (cj k r κ τ x) = (κ : ℂ)⁻¹ * ell k r z x := by
  unfold ell
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : a.val + 1 < r
  · rw [dite_eq_left h, dite_eq_left h, cj_apply, tV_eI, tV_eI]
    have e : r - a.val = (r - (a.val + 1)) + 1 := by omega
    have hk := pow_pos hκ (r - (a.val + 1))
    have hκc : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
    have hτc : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ.ne'
    have hkc : (κ : ℂ) ^ (r - (a.val + 1)) ≠ 0 := pow_ne_zero _ hκc
    simp only [tF]
    rw [e, pow_succ]
    push_cast
    field_simp
  · rw [dite_eq_right h, dite_eq_right h, cj_mulVec, dM_mulVec_wb (inWb_smul hz _), Matrix.mulVec_smul,
      dMi_mulVec_apply, tV_eI, Pi.smul_apply, smul_eq_mul]
    have e : r - a.val = 1 := by omega
    have hκc : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
    have hτc : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ.ne'
    simp only [tF, e, pow_one]
    push_cast
    field_simp

theorem psi_cj (hκ : 0 < κ) (hτ : 0 < τ) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (c : ℂ) (x : Mx k r) :
    psi k r ((τ : ℂ) • z) ((κ : ℂ) * c) (cj k r κ τ x) = psi k r z c x := by
  unfold psi
  rw [ell_cj hκ hτ hz]
  have hκc : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
  have : (κ : ℂ) * c * ((κ : ℂ)⁻¹ * ell k r z x) = c * ell k r z x := by
    field_simp
  rw [this]

theorem delta_iff {s y : ℂ} {i j : Fin (2 * r + k + 1)} (hs : s ≠ 0) (h1 : i = j → s = 1) :
    (s * y = if i = j then 1 else 0) ↔ (y = if i = j then 1 else 0) := by
  by_cases h : i = j
  · rw [h1 h, one_mul]
  · simp only [h, if_false, mul_eq_zero, hs, false_or]

theorem cj_fac_ne (hκ : 0 < κ) (hτ : 0 < τ) (i j : Fin (2 * r + k + 1)) :
    ((((tV k r κ τ i)⁻¹ * tV k r κ τ j : ℝ)) : ℂ) ≠ 0 := by
  have := tV_pos (k := k) (r := r) hκ hτ i
  have := tV_pos (k := k) (r := r) hκ hτ j
  exact_mod_cast (mul_pos (inv_pos.mpr ‹0 < tV k r κ τ i›) this).ne'

theorem cj_fac_diag (hκ : 0 < κ) (hτ : 0 < τ) (i j : Fin (2 * r + k + 1)) (h : i = j) :
    ((((tV k r κ τ i)⁻¹ * tV k r κ τ j : ℝ)) : ℂ) = 1 := by
  subst h; rw [inv_mul_cancel₀ (tV_pos hκ hτ i).ne']; simp

theorem cj_mem_Nset_iff (hκ : 0 < κ) (hτ : 0 < τ) (x : Mx k r) :
    cj k r κ τ x ∈ Nset k r ↔ x ∈ Nset k r := by
  simp only [Nset, Set.mem_ofPred_eq, cj_mem_UH_iff hκ hτ, cj_apply]
  refine and_congr Iff.rfl (and_congr ?_ ?_)
  · refine forall_congr' fun a => forall_congr' fun i => imp_congr_right fun _ => ?_
    exact delta_iff (cj_fac_ne hκ hτ _ _) (cj_fac_diag hκ hτ _ _)
  · refine forall_congr' fun i => forall_congr' fun j => imp_congr_right fun _ =>
      imp_congr_right fun _ => imp_congr_right fun _ => ?_
    exact delta_iff (cj_fac_ne hκ hτ _ _) (cj_fac_diag hκ hτ _ _)

theorem UWset_smul {z : Fin (2 * r + k + 1) → ℂ} (hτ : 0 < τ) : UWset k r ((τ : ℂ) • z) = UWset k r z := by
  ext g
  simp only [UWset, Set.mem_ofPred_eq, Matrix.mulVec_smul]
  have hτ' : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ.ne'
  refine and_congr Iff.rfl (and_congr Iff.rfl ⟨fun h => ?_, fun h => by rw [h]⟩)
  exact smul_right_injective _ hτ' h

theorem cj_fix_iff (hκ : 0 < κ) (hτ : 0 < τ) (g : Mx k r) (v : Fin (2 * r + k + 1) → ℂ) (s : ℂ) (hs : s ≠ 0)
    (h1 : dM k r κ τ *ᵥ v = s • v) (h2 : dMi k r κ τ *ᵥ v = s⁻¹ • v) :
    cj k r κ τ g *ᵥ v = v ↔ g *ᵥ v = v := by
  rw [cj_mulVec, h1, Matrix.mulVec_smul, Matrix.mulVec_smul]
  constructor
  · intro h
    have h3 : dM k r κ τ *ᵥ (s • (dMi k r κ τ *ᵥ (g *ᵥ v))) = dM k r κ τ *ᵥ v := by rw [h]
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, dM_mul_dMi hκ hτ, Matrix.one_mulVec, h1] at h3
    exact smul_right_injective _ hs h3
  · intro h; rw [h, h2, smul_smul, mul_inv_cancel₀ hs, one_smul]

theorem cj_fix_bvec_iff (hκ : 0 < κ) (hτ : 0 < τ) (g : Mx k r) (i : Fin (2 * r + k + 1)) :
    cj k r κ τ g *ᵥ bvec i = bvec i ↔ g *ᵥ bvec i = bvec i := by
  refine cj_fix_iff hκ hτ g _ ((tV k r κ τ i : ℝ) : ℂ) (by exact_mod_cast (tV_pos hκ hτ i).ne')
    (dM_mulVec_bvec i) ?_
  rw [dMi_mulVec_bvec, Complex.ofReal_inv]

theorem cj_mem_UWset_iff (hκ : 0 < κ) (hτ : 0 < τ) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (g : Mx k r) :
    cj k r κ τ g ∈ UWset k r z ↔ g ∈ UWset k r z := by
  simp only [UWset, Set.mem_ofPred_eq, cj_mem_UH_iff hκ hτ]
  refine and_congr Iff.rfl (and_congr (forall_congr' fun a =>
    and_congr (cj_fix_bvec_iff hκ hτ g _) (cj_fix_bvec_iff hκ hτ g _)) ?_)
  exact cj_fix_iff hκ hτ g z 1 one_ne_zero (by rw [one_smul, dM_mulVec_wb hz])
    (by rw [inv_one, one_smul, dMi_mulVec_wb hz])

theorem cj_mem_RStab_iff (hκ : 0 < κ) (hτ : 0 < τ) (g a : Mx k r) :
    cj k r κ τ a ∈ RStab k r (cj k r κ τ g) ↔ a ∈ RStab k r g := by
  simp only [RStab, Set.mem_ofPred_eq]
  rw [← cj_inv hκ hτ, ← cj_mul hκ hτ, ← cj_mul hκ hτ, cj_mem_Nset_iff hκ hτ, cj_mem_Nset_iff hκ hτ]

end Alg2

end Formalism.MainNotions.FrameBoundFromBesselTorus
end
end

open MeasureTheory Matrix Finset

noncomputable section

namespace Formalism.MainNotions.FrameBoundFromBesselTorus

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates

variable {k r : ℕ}

def trD (L : LocBessel k r) (κ τ : ℝ) (κN₁ : ENNReal)
    (hz : inWb k r ((τ : ℂ) • L.z) ∧ 0 < Tz k r ((τ : ℂ) • L.z))
    (hz' : inWb k r ((τ : ℂ) • L.z') ∧ 0 < Tz k r ((τ : ℂ) • L.z'))
    (hπ : IsHCTypeW k r ((τ : ℂ) • L.z) L.u (fun x => L.π (cjI k r κ τ x)))
    (hπ' : IsHCTypeW k r ((τ : ℂ) • L.z') L.u' (fun x => L.π' (cjI k r κ τ x)))
    (hμW : IsHaarOn (UWset k r ((τ : ℂ) • L.z)) (L.μW.map (cjT k r κ τ)) ∧ L.μW.map (cjT k r κ τ) Set.univ = 1)
    (hμW' : IsHaarOn (UWset k r ((τ : ℂ) • L.z')) (L.μW'.map (cjT k r κ τ)) ∧
      L.μW'.map (cjT k r κ τ) Set.univ = 1) : LocBessel k r where
  ε := L.ε
  lam := L.lam
  hlam := L.hlam
  z := (τ : ℂ) • L.z
  z' := (τ : ℂ) • L.z'
  hz := hz
  hz' := hz'
  u := L.u
  u' := L.u'
  Hs := L.Hs
  σ := L.σ
  hσ := L.hσ
  Wp := L.Wp
  π := fun x => L.π (cjI k r κ τ x)
  hπ := hπ
  Wq := L.Wq
  π' := fun x => L.π' (cjI k r κ τ x)
  hπ' := hπ'
  c := (κ : ℂ) * L.c
  μW := L.μW.map (cjT k r κ τ)
  μW' := L.μW'.map (cjT k r κ τ)
  hμW := hμW
  hμW' := hμW'
  κN := κN₁

end Formalism.MainNotions.FrameBoundFromBesselTorus
end
end

open MeasureTheory Matrix Finset

noncomputable section

set_option linter.unusedVariables false

namespace Formalism.MainNotions.FrameBoundFromBesselTorus

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates

def alphaPt {r : ℕ} (κ τ : ℝ) (γ : Point ℂ (r + 1)) : ℝ :=
  κ ^ (rootPat γ).card * ∏ p ∈ rootPat γ, (tF r κ τ p.2.val / tF r κ τ p.1.val) ^ 2

section Alg3

variable {k r : ℕ} {κ τ : ℝ}

theorem Hpk_mul_dMi (hκ : 0 < κ) (hτ : 0 < τ) : Hpk k r * dMi k r κ τ = dM k r κ τ * Hpk k r := by
  ext i j
  rw [dMi, dM, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h : Hpk k r i j = 0
  · rw [h]; simp
  · have e := tV_mul_of_Hpk hκ hτ i j h
    have : (tV k r κ τ j)⁻¹ = tV k r κ τ i := (eq_inv_of_mul_eq_one_left e).symm
    rw [this]; ring

theorem star_vecMul_dM (v : Fin (2 * r + k + 1) → ℂ) : star v ᵥ* dM k r κ τ = star (dM k r κ τ *ᵥ v) := by
  funext j
  rw [dM, Matrix.vecMul_diagonal, Pi.star_apply, Pi.star_apply, Matrix.mulVec_diagonal, star_mul',
    Complex.star_def, Complex.conj_ofReal, mul_comm]

theorem Zhat_cj (hκ : 0 < κ) (hτ : 0 < τ) {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z)
    (hz' : inWb k r z') (g : Mx k r) (a b : Fin (r + 1)) :
    Zhat k r ((τ : ℂ) • z) ((τ : ℂ) • z') (cj k r κ τ g) a b =
      ((tF r κ τ a.val * tF r κ τ b.val : ℝ) : ℂ) * Zhat k r z z' g a b := by
  unfold QuantumDeterminants.Zhat herm
  rw [cj_mulVec, dM_mulVec_fvec hz' b, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul,
    Matrix.mulVec_mulVec (M := Hpk k r) (N := dMi k r κ τ), Hpk_mul_dMi hκ hτ, ← Matrix.mulVec_mulVec,
    dotProduct_smul, Matrix.dotProduct_mulVec, star_vecMul_dM, dM_mulVec_fvec hz a, star_smul,
    smul_dotProduct]
  simp only [Complex.star_def, Complex.conj_ofReal, smul_eq_mul]
  push_cast; ring

theorem bigCell_cj (hκ : 0 < κ) (hτ : 0 < τ) (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    cj k r κ τ (bigCell k r c μ) = bigCell k r (fun a => ((tF r κ τ a.val ^ 2 : ℝ) : ℂ) * c a) μ := by
  ext i j
  rw [cj_apply]
  unfold bigCell
  by_cases hj : j.val < r
  · rw [dite_eq_left hj, dite_eq_left hj]
    by_cases hi : i = esI k r ⟨j.val, hj⟩
    · rw [if_pos hi, if_pos hi, hi, tV_esI]
      have : tV k r κ τ j = tF r κ τ j.val := by unfold tV; rw [if_pos hj]
      rw [this, inv_inv]; push_cast; ring
    · rw [if_neg hi, if_neg hi, mul_zero]
  · rw [dite_eq_right hj, dite_eq_right hj]
    by_cases hj2 : j.val ≤ r + k
    · rw [dite_eq_left hj2, dite_eq_left hj2]
      by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
      · rw [dite_eq_left hi, tV_wb i hi.1 hi.2, tV_wb j (by omega) hj2]; simp
      · rw [dite_eq_right hi, mul_zero]
    · rw [dite_eq_right hj2, dite_eq_right hj2]
      by_cases hi : i.val = 2 * r + k - j.val
      · rw [if_pos hi, if_pos hi]
        have hti : tV k r κ τ i = tF r κ τ (2 * r + k - j.val) := by
          unfold tV; rw [if_pos (by omega), hi]
        have htj : tV k r κ τ j = (tF r κ τ (2 * r + k - j.val))⁻¹ := by
          unfold tV; rw [if_neg hj, if_neg hj2]
        have hp := tF_pos (r := r) hκ hτ (2 * r + k - j.val)
        rw [hti, htj]
        simp only [star_mul', Complex.star_def, Complex.conj_ofReal]
        have hpc : ((tF r κ τ (2 * r + k - j.val) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
        push_cast
        rw [mul_inv]
        field_simp
      · rw [if_neg hi, if_neg hi, mul_zero]

theorem flagMat_cj (hκ : 0 < κ) (hτ : 0 < τ) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (x : Mx k r)
    (i j : Fin (r + 1)) (hi : i.val < r) :
    flagMat k r ((τ : ℂ) • z) (cj k r κ τ x) i j =
      ((tF r κ τ j.val / tF r κ τ i.val : ℝ) : ℂ) * flagMat k r z x i j := by
  unfold flagMat
  rw [dite_eq_left hi, dite_eq_left hi, cj_mulVec, dM_mulVec_fvec hz j, Matrix.mulVec_smul, dMi_mulVec_apply, tV_eI,
    Pi.smul_apply, smul_eq_mul]
  push_cast; ring

theorem rootCoords_cjT (hκ : 0 < κ) (hτ : 0 < τ) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z)
    (γ : Point ℂ (r + 1)) (x : Mt k r) (p : rootPat γ) :
    rootCoords k r ((τ : ℂ) • z) γ (cjT k r κ τ x) p =
      ((tF r κ τ p.1.2.val / tF r κ τ p.1.1.val : ℝ) : ℂ) * rootCoords k r z γ x p := by
  have hp := (Finset.mem_filter.mp p.2).2.1
  have hi : p.1.1.val < r := by
    have h1 : p.1.1.val < p.1.2.val := hp
    have h2 := p.1.2.isLt
    omega
  unfold rootCoords
  rw [of_cjT]
  exact flagMat_cj hκ hτ hz (Matrix.of x) p.1.1 p.1.2 hi

theorem Tz_smul (z : Fin (2 * r + k + 1) → ℂ) (t : ℝ) : Tz k r ((t : ℂ) • z) = t ^ 2 * Tz k r z := by
  unfold Tz herm
  rw [Matrix.mulVec_smul, dotProduct_smul, star_smul, smul_dotProduct]
  simp only [Complex.star_def, Complex.conj_ofReal, smul_eq_mul]
  rw [← mul_assoc, ← Complex.ofReal_mul, Complex.re_ofReal_mul]
  ring

theorem inWb_bvec_wI (j : Fin (k + 1)) : inWb k r (bvec (wI k r j)) := by
  intro i hi
  have : i ≠ wI k r j := by
    intro e; rw [e] at hi; unfold wI at hi; simp only at hi; omega
  simp [bvec, this]

theorem cj_blockW (hκ : 0 < κ) (hτ : 0 < τ) (h : Matrix (Fin k) (Fin k) ℂ) :
    cj k r κ τ (blockW k r h) = blockW k r h := by
  ext i j
  rw [cj_apply]
  unfold blockW
  by_cases hi : r ≤ i.val ∧ i.val < r + k
  · rw [dite_eq_left hi]
    by_cases hj : r ≤ j.val ∧ j.val < r + k
    · rw [dite_eq_left hj, tV_wb i hi.1 (by omega), tV_wb j hj.1 (by omega)]; simp
    · rw [dite_eq_right hj, mul_zero]
  · rw [dite_eq_right hi]
    by_cases e : i = j
    · rw [if_pos e, cj_fac_diag hκ hτ i j e, one_mul]
    · rw [if_neg e, mul_zero]

theorem isHCTypeW_cjI (hκ : 0 < κ) (hτ : 0 < τ) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z)
    {u : Fin k → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {π : Mx k r → (H →L[ℂ] H)} (h : IsHCTypeW k r z u π) :
    IsHCTypeW k r ((τ : ℂ) • z) u (fun x => π (cjI k r κ τ x)) := by
  obtain ⟨g, ⟨hg1, hg2, hg3⟩, hU⟩ := h
  refine ⟨cj k r κ τ g, ⟨(cj_mem_UH_iff hκ hτ g).mpr hg1, fun a =>
    ⟨(cj_fix_bvec_iff hκ hτ g _).mpr (hg2 a).1, (cj_fix_bvec_iff hκ hτ g _).mpr (hg2 a).2⟩, ?_⟩, ?_⟩
  · rw [Tz_smul, Real.sqrt_mul (sq_nonneg τ), Real.sqrt_sq hτ.le, cj_mulVec, Matrix.mulVec_smul,
      dM_mulVec_wb (inWb_bvec_wI _), Complex.ofReal_mul, ← smul_smul, Matrix.mulVec_smul, hg3,
      Matrix.mulVec_smul, dMi_mulVec_wb hz]
  · have e : (fun h => π (cjI k r κ τ (cj k r κ τ g * blockW k r h * (cj k r κ τ g)⁻¹))) =
        fun h => π (g * blockW k r h * g⁻¹) := by
      funext h
      rw [← cj_inv hκ hτ, ← cj_blockW hκ hτ h, ← cj_mul hκ hτ, ← cj_mul hκ hτ, cjI_cj hκ hτ, cj_blockW hκ hτ]
    simp only at e ⊢
    rw [e]; exact hU

theorem isRelStab_iff (hκ : 0 < κ) (hτ : 0 < τ) (L L₁ : LocBessel k r) (hz : inWb k r L.z) (hz' : inWb k r L.z')
    (e1 : L₁.z = (τ : ℂ) • L.z) (e2 : L₁.z' = (τ : ℂ) • L.z') (e3 : L₁.c = (κ : ℂ) * L.c) (g : Mx k r) :
    IsRelStab L₁ (cj k r κ τ g) ↔ IsRelStab L g := by
  unfold IsRelStab
  rw [e1, e2, e3]
  constructor
  · intro h a ha
    have := h (cj k r κ τ a) ((cj_mem_RStab_iff hκ hτ g a).mpr ha)
    rwa [← cj_inv hκ hτ, ← cj_mul hκ hτ, ← cj_mul hκ hτ, psi_cj hκ hτ hz, psi_cj hκ hτ hz'] at this
  · intro h a₁ ha₁
    have ha : cjI k r κ τ a₁ ∈ RStab k r g := by
      rw [← cj_mem_RStab_iff hκ hτ g, cj_cjI hκ hτ]; exact ha₁
    have := h _ ha
    rw [← cj_cjI hκ hτ a₁, ← cj_inv hκ hτ, ← cj_mul hκ hτ, ← cj_mul hκ hτ, psi_cj hκ hτ hz, psi_cj hκ hτ hz']
    exact this

end Alg3

end Formalism.MainNotions.FrameBoundFromBesselTorus
