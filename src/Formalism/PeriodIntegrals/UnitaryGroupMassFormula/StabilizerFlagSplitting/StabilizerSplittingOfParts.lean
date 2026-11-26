module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerFlagSplitting.SubFlag

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerFlagSplitting.MulVecColOfMul
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerFlagSplitting.UnitR
namespace PI.StabSplit.Alg

variable {R : Type*} [Ring R]

theorem decomp (h P : R) (hPP : P * P = P) (hU : P * h * (1 - P) = 0) :
    (h * P + (1 - P)) * (h * (1 - P) + P) = h := by
  have r : P * P - P = 0 := sub_eq_zero.mpr hPP
  have e : (h * P + (1 - P)) * (h * (1 - P) + P) - h =
      h * (P * h * (1 - P)) + h * (P * P - P) - P * h * (1 - P) - (P * P - P) := by
    noncomm_ring
  have z : h * (P * h * (1 - P)) + h * (P * P - P) - P * h * (1 - P) - (P * P - P) = 0 := by
    simp only [hU, r, mul_zero, add_zero, sub_zero]
  exact sub_eq_zero.mp (e.trans z)

theorem uniq (h P ρ κ : R) (hρκ : ρ * κ = h) (hρ : ρ * (1 - P) = 1 - P) (hκ : κ * P = P)
    (hκU : P * κ * (1 - P) = 0) :
    ρ = h * P + (1 - P) ∧ κ = h * (1 - P) + P := by
  have a : ρ * κ - h = 0 := sub_eq_zero.mpr hρκ
  have b : ρ * (1 - P) - (1 - P) = 0 := sub_eq_zero.mpr hρ
  have c : κ * P - P = 0 := sub_eq_zero.mpr hκ
  constructor
  · have e : ρ - (h * P + (1 - P)) = (ρ * κ - h) * P - ρ * (κ * P - P) + (ρ * (1 - P) - (1 - P)) := by
      noncomm_ring
    have z : (ρ * κ - h) * P - ρ * (κ * P - P) + (ρ * (1 - P) - (1 - P)) = 0 := by
      simp only [a, b, c, mul_zero, zero_mul, add_zero, sub_zero]
    exact sub_eq_zero.mp (e.trans z)
  · have e : κ - (h * (1 - P) + P) = (κ * P - P) + P * κ * (1 - P) + (ρ * κ - h) * (1 - P)
        - ρ * (P * κ * (1 - P)) - (ρ * (1 - P) - (1 - P)) * κ * (1 - P) := by
      noncomm_ring
    have z : (κ * P - P) + P * κ * (1 - P) + (ρ * κ - h) * (1 - P)
        - ρ * (P * κ * (1 - P)) - (ρ * (1 - P) - (1 - P)) * κ * (1 - P) = 0 := by
      simp only [a, b, c, hκU, mul_zero, zero_mul, add_zero, sub_zero]
    exact sub_eq_zero.mp (e.trans z)

theorem comm (P ρ κ : R) (hρ : ρ * (1 - P) = 1 - P) (hκ : κ * P = P)
    (hρM : (1 - P) * ρ * P = 0) (hκU : P * κ * (1 - P) = 0) : ρ * κ = κ * ρ := by
  have b : ρ * (1 - P) - (1 - P) = 0 := sub_eq_zero.mpr hρ
  have c : κ * P - P = 0 := sub_eq_zero.mpr hκ
  have e : ρ * κ - κ * ρ = ρ * (κ * P - P) + ρ * (P * κ * (1 - P)) - P * κ * (1 - P)
      + (ρ * (1 - P) - (1 - P)) * κ * (1 - P) + (1 - P) * ρ * P - (κ * P - P) * ρ * P
      - κ * ((1 - P) * ρ * P) - κ * (ρ * (1 - P) - (1 - P)) := by
    noncomm_ring
  have z : ρ * (κ * P - P) + ρ * (P * κ * (1 - P)) - P * κ * (1 - P)
      + (ρ * (1 - P) - (1 - P)) * κ * (1 - P) + (1 - P) * ρ * P - (κ * P - P) * ρ * P
      - κ * ((1 - P) * ρ * P) - κ * (ρ * (1 - P) - (1 - P)) = 0 := by
    simp only [b, c, hρM, hκU, mul_zero, zero_mul, add_zero, sub_zero]
  exact sub_eq_zero.mp (e.trans z)

theorem nilp (P g : R) (m : ℕ) (hPP : P * P = P) (hgQ : (g - 1) * (1 - P) = 0)
    (hgM : (1 - P) * g * P = 0) (hm : (g - 1) ^ m * P = 0) : (g - 1) ^ (m + 1) = 0 := by
  have r : P * P - P = 0 := sub_eq_zero.mpr hPP
  have h1 : (g - 1) * P = P * ((g - 1) * P) := by
    have e : (g - 1) * P - P * ((g - 1) * P) = (1 - P) * g * P + (P * P - P) := by noncomm_ring
    rw [hgM, r, add_zero] at e
    exact sub_eq_zero.mp e
  have h2 : g - 1 = (g - 1) * P := by
    have e : (g - 1) - (g - 1) * P = (g - 1) * (1 - P) := by noncomm_ring
    rw [hgQ] at e
    exact sub_eq_zero.mp e
  calc (g - 1) ^ (m + 1) = (g - 1) ^ m * (g - 1) := pow_succ _ _
    _ = (g - 1) ^ m * ((g - 1) * P) := by rw [← h2]
    _ = (g - 1) ^ m * (P * ((g - 1) * P)) := by rw [← h1]
    _ = ((g - 1) ^ m * P) * ((g - 1) * P) := (mul_assoc _ _ _).symm
    _ = 0 := by rw [hm, zero_mul]

variable [StarRing R]

theorem unitK (H P h : R) (hH : star H = H) (hPH : star P * H = H * P) (hPP : P * P = P)
    (hh : star h * H * h = H) (hU : P * h * (1 - P) = 0) :
    star (h * (1 - P) + P) * H * (h * (1 - P) + P) = H := by
  have r1 : star P * H - H * P = 0 := sub_eq_zero.mpr hPH
  have r2 : P * P - P = 0 := sub_eq_zero.mpr hPP
  have r3 : star h * H * h - H = 0 := sub_eq_zero.mpr hh
  have r5 : (1 - star P) * (star h * star P) = 0 := by
    simpa only [star_mul, star_sub, star_one, star_zero] using congrArg star hU
  have e : star (h * (1 - P) + P) * H * (h * (1 - P) + P) - H =
      H * (P * P - P) + H * (P * P - P) - (star P * H - H * P) * (1 - P)
      + (1 - star P) * (star h * H * h - H) * (1 - P) + (1 - star P) * (star h * star P) * H
      - (1 - star P) * star h * (star P * H - H * P) + H * (P * h * (1 - P))
      + (star P * H - H * P) * h * (1 - P) + (star P * H - H * P) * P := by
    simp only [star_add, star_mul, star_sub, star_one]
    noncomm_ring
  have z : H * (P * P - P) + H * (P * P - P) - (star P * H - H * P) * (1 - P)
      + (1 - star P) * (star h * H * h - H) * (1 - P) + (1 - star P) * (star h * star P) * H
      - (1 - star P) * star h * (star P * H - H * P) + H * (P * h * (1 - P))
      + (star P * H - H * P) * h * (1 - P) + (star P * H - H * P) * P = 0 := by
    simp only [r1, r2, r3, r5, hU, mul_zero, zero_mul, add_zero, sub_zero]
  exact sub_eq_zero.mp (e.trans z)

end PI.StabSplit.Alg
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerFlagSplitting.PrjMulVecOfL
open Matrix

noncomputable section

namespace PI.StabSplit.Proj

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

def prj (H : Matrix n n ℂ) (Y : Matrix n ι ℂ) : Matrix n n ℂ := Y * (Yᴴ * H * Y)⁻¹ * (Yᴴ * H)

variable (H : Matrix n n ℂ) (Y : Matrix n ι ℂ)

lemma prj_Y (hG : IsUnit (Yᴴ * H * Y).det) : prj H Y * Y = Y := by
  calc prj H Y * Y = Y * ((Yᴴ * H * Y)⁻¹ * (Yᴴ * H * Y)) := by simp only [prj, Matrix.mul_assoc]
    _ = Y := by rw [nonsing_inv_mul _ hG, Matrix.mul_one]

lemma L_prj (hG : IsUnit (Yᴴ * H * Y).det) : (Yᴴ * H) * prj H Y = Yᴴ * H := by
  calc (Yᴴ * H) * prj H Y = ((Yᴴ * H * Y) * (Yᴴ * H * Y)⁻¹) * (Yᴴ * H) := by
        simp only [prj, Matrix.mul_assoc]
    _ = Yᴴ * H := by rw [mul_nonsing_inv _ hG, Matrix.one_mul]

lemma prj_sq (hG : IsUnit (Yᴴ * H * Y).det) : prj H Y * prj H Y = prj H Y := by
  calc prj H Y * prj H Y = (prj H Y * Y) * (Yᴴ * H * Y)⁻¹ * (Yᴴ * H) := by
        simp only [prj, Matrix.mul_assoc]
    _ = prj H Y := by rw [prj_Y H Y hG]; rfl

lemma prj_star (hH : Hᴴ = H) : (prj H Y)ᴴ * H = H * prj H Y := by
  simp only [prj, conjTranspose_mul, conjTranspose_nonsing_inv, hH, conjTranspose_conjTranspose,
    Matrix.mul_assoc]

lemma L_one_sub (hG : IsUnit (Yᴴ * H * Y).det) : (Yᴴ * H) * (1 - prj H Y) = 0 := by
  rw [Matrix.mul_sub, L_prj H Y hG, Matrix.mul_one, sub_self]

lemma prj_mulVec_of_L {v : n → ℂ} (hv : (Yᴴ * H) *ᵥ v = 0) : prj H Y *ᵥ v = 0 := by
  rw [prj, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]

lemma prj_mul_of_L {m : Type*} [Fintype m] (A : Matrix n m ℂ) (hA : (Yᴴ * H) * A = 0) :
    prj H Y * A = 0 := by
  rw [prj, Matrix.mul_assoc, hA, Matrix.mul_zero]

lemma presM (hG : IsUnit (Yᴴ * H * Y).det) (g : Matrix n n ℂ) (C : Matrix ι ι ℂ) (hC : g * Y = Y * C) :
    (1 - prj H Y) * g * prj H Y = 0 := by
  have : g * prj H Y = Y * C * ((Yᴴ * H * Y)⁻¹ * (Yᴴ * H)) := by
    rw [prj, Matrix.mul_assoc Y, ← Matrix.mul_assoc g, hC]
  rw [Matrix.mul_assoc, this, Matrix.sub_mul, Matrix.one_mul, ← Matrix.mul_assoc (prj H Y),
    ← Matrix.mul_assoc (prj H Y), prj_Y H Y hG, sub_self]

lemma presU (hG : IsUnit (Yᴴ * H * Y).det) (g : Matrix n n ℂ) (hg : gᴴ * H * g = H)
    (hdet : IsUnit g.det) (C : Matrix ι ι ℂ) (hC : g⁻¹ * Y = Y * C) :
    prj H Y * g * (1 - prj H Y) = 0 := by
  have hgs : IsUnit gᴴ.det := by rw [det_conjTranspose]; exact hdet.star
  have hHg : H * g = (g⁻¹)ᴴ * H := by
    rw [conjTranspose_nonsing_inv]
    calc H * g = (gᴴ)⁻¹ * (gᴴ * H * g) := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, nonsing_inv_mul _ hgs, Matrix.one_mul]
      _ = (gᴴ)⁻¹ * H := by rw [hg]
  have hL : (Yᴴ * H) * g = Cᴴ * (Yᴴ * H) := by
    rw [Matrix.mul_assoc, hHg, ← Matrix.mul_assoc, ← conjTranspose_mul, hC, conjTranspose_mul,
      Matrix.mul_assoc]
  have : (Yᴴ * H) * (g * (1 - prj H Y)) = 0 := by
    rw [← Matrix.mul_assoc, hL, Matrix.mul_assoc, L_one_sub H Y hG, Matrix.mul_zero]
  rw [Matrix.mul_assoc, prj_mul_of_L H Y _ this]

lemma exists_C (A : Matrix n ι ℂ)
    (hA : ∀ j, (fun i => A i j) ∈ Submodule.span ℂ (Set.range fun l => fun i => Y i l)) :
    ∃ C : Matrix ι ι ℂ, A = Y * C := by
  choose c hc using fun j => (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hA j)
  refine ⟨Matrix.of fun l j => c j l, ?_⟩
  ext i j
  have h := congrFun (hc j) i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
  rw [Matrix.mul_apply, ← h]
  simp [mul_comm]

lemma Y_inj (hG : IsUnit (Yᴴ * H * Y).det) (c : ι → ℂ) (hc : Y *ᵥ c = 0) : c = 0 := by
  have h1 : (Yᴴ * H * Y) *ᵥ c = 0 := by rw [← Matrix.mulVec_mulVec, hc, Matrix.mulVec_zero]
  have h2 := congrArg (fun v => (Yᴴ * H * Y)⁻¹ *ᵥ v) h1
  simpa [Matrix.mulVec_mulVec, nonsing_inv_mul _ hG] using h2

end PI.StabSplit.Proj
end
end

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2

noncomputable section

namespace PI.StabSplit

def Ym (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) :
    Matrix (Fin (2 * r + k + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) ℂ :=
  Matrix.of fun i j => gramVec k r z z' γ j i

def Pm (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) : B.Mat k r :=
  Proj.prj (Hpk k r) (Ym k r z z' γ)

lemma Ym_mulVec (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) (c) :
    Ym k r z z' γ *ᵥ c = ∑ j, c j • gramVec k r z z' γ j := by
  ext i
  simp [Ym, mulVec, dotProduct, Finset.sum_apply, mul_comm]

lemma L_mulVec (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) (v) (j) :
    (((Ym k r z z' γ)ᴴ * Hpk k r) *ᵥ v) j = herm (Hpk k r) v (gramVec k r z z' γ j) := by
  simp only [herm, mulVec, dotProduct, Matrix.mul_apply, conjTranspose_apply, Ym, of_apply, Finset.sum_mul,
    Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

lemma gram_eq (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) :
    gramM k r z z' γ = (Ym k r z z' γ)ᴴ * Hpk k r * Ym k r z z' γ := by
  ext i j
  rw [gramM, ← L_mulVec]
  simp only [mulVec, dotProduct, Matrix.mul_apply, Ym, of_apply]

lemma mem_U_iff (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) (v) :
    v ∈ Uperp k r z z' γ ↔ ((Ym k r z z' γ)ᴴ * Hpk k r) *ᵥ v = 0 := by
  have : (Matrix.of fun i j => star (gramVec k r z z' γ i j)) = (Ym k r z z' γ)ᴴ := by
    ext i j; simp [Ym, conjTranspose_apply]
  rw [Uperp, LinearMap.mem_ker, Matrix.mulVecLin_apply, this]

lemma hpk_unit (k r : ℕ) : IsUnit (Hpk k r).det := by
  have h := congrArg Matrix.det (GBasic.Hpk_sq k r)
  rw [det_mul, det_one] at h
  exact isUnit_iff_ne_zero.2 (by intro h0; rw [h0, zero_mul] at h; exact zero_ne_one h)

lemma GV_one (k r : ℕ) : (1 : B.Mat k r) ∈ B.GV k r := (uHGroup _ _ (hpk_unit k r)).1

lemma GV_mul (k r : ℕ) {g h : B.Mat k r} (hg : g ∈ B.GV k r) (hh : h ∈ B.GV k r) :
    g * h ∈ B.GV k r := (uHGroup _ _ (hpk_unit k r)).2.1 g hg h hh

lemma GV_unit (k r : ℕ) {g : B.Mat k r} (hg : g ∈ B.GV k r) : IsUnit g.det :=
  ((uHGroup _ _ (hpk_unit k r)).2.2 g hg).1

lemma GV_inv (k r : ℕ) {g : B.Mat k r} (hg : g ∈ B.GV k r) : g⁻¹ ∈ B.GV k r :=
  ((uHGroup _ _ (hpk_unit k r)).2.2 g hg).2

lemma GV_eq (k r : ℕ) {g : B.Mat k r} (hg : g ∈ B.GV k r) : gᴴ * Hpk k r * g = Hpk k r := hg

lemma gram_unit (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) (hs : Std k r z z')
    (hp : PosPt k r z z' γ) : IsUnit ((Ym k r z z' γ)ᴴ * Hpk k r * Ym k r z z' γ).det := by
  rw [← gram_eq]
  have h := gGram k r z z' hs.2.1.1 hs.2.2.1 γ hp.1
  have hne : (gramM k r z z' γ).det ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h
    have := hp.2
    have h1 : (Gf k r z z' γ : ℝ) = 0 := by exact_mod_cast h
    linarith
  exact isUnit_iff_ne_zero.2 hne

lemma herm_unit (k r : ℕ) {g : B.Mat k r} (hg : g ∈ B.GV k r) (x y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (g *ᵥ x) (g *ᵥ y) = herm (Hpk k r) x y := by
  unfold herm
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]
  rw [GV_eq k r hg]

lemma mul_eq_of_cols {m : Type*} [Fintype m] (k r : ℕ) (A : B.Mat k r)
    (C : Matrix (Fin (2 * r + k + 1)) m ℂ) (h : ∀ j, A *ᵥ (fun i => C i j) = fun i => C i j) :
    A * C = C := by
  ext i j
  have := congrFun (h j) i
  simpa [mulVec, dotProduct, Matrix.mul_apply] using this

lemma mulVec_col_of_mul {m : Type*} [Fintype m] (k r : ℕ) (A : B.Mat k r)
    (C : Matrix (Fin (2 * r + k + 1)) m ℂ) (h : A * C = C) (j : m) :
    A *ᵥ (fun i => C i j) = fun i => C i j := by
  ext i
  have := congrFun (congrFun h i) j
  simpa [mulVec, dotProduct, Matrix.mul_apply] using this

lemma flag_nilp {m N : ℕ} (g : Matrix (Fin N) (Fin N) ℂ) (v : Fin m → Fin N → ℂ)
    (hv : ∀ a, g *ᵥ v a - v a ∈ Submodule.span ℂ (Set.range fun b : {b : Fin m // b < a} => v b.1)) :
    ∀ a : Fin m, ((g - 1) ^ (a.val + 1)) *ᵥ v a = 0 := by
  intro a
  induction' ht : a.val using Nat.strong_induction_on with t ih generalizing a
  have hsp : Submodule.span ℂ (Set.range fun b : {b : Fin m // b < a} => v b.1) ≤
      LinearMap.ker (Matrix.mulVecLin ((g - 1) ^ t)) := by
    rw [Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    have hb : b.1.val < t := by rw [← ht]; exact b.2
    have := ih b.1.val hb b.1 rfl
    simp only [SetLike.mem_coe, LinearMap.mem_ker, Matrix.mulVecLin_apply]
    have e : t = (t - (b.1.val + 1)) + (b.1.val + 1) := by omega
    rw [e, pow_add, ← mulVec_mulVec, this, mulVec_zero]
  have h1 := hsp (hv a)
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at h1
  rw [pow_succ, ← mulVec_mulVec, sub_mulVec, one_mulVec]
  exact h1

lemma flag_nilp_all {m N : ℕ} (g : Matrix (Fin N) (Fin N) ℂ) (v : Fin m → Fin N → ℂ)
    (hv : ∀ a, g *ᵥ v a - v a ∈ Submodule.span ℂ (Set.range fun b : {b : Fin m // b < a} => v b.1)) :
    ∀ a : Fin m, ((g - 1) ^ m) *ᵥ v a = 0 := by
  intro a
  have e : m = (m - (a.val + 1)) + (a.val + 1) := by omega
  rw [e, pow_add, ← mulVec_mulVec, flag_nilp g v hv a, mulVec_zero]

lemma conj_pow {N : ℕ} (A G Gi : Matrix (Fin N) (Fin N) ℂ) (h1 : Gi * G = 1) (h2 : G * Gi = 1) :
    ∀ p : ℕ, (Gi * A * G) ^ p = Gi * A ^ p * G := by
  intro p
  induction p with
  | zero => simp [h1]
  | succ p ih =>
    rw [pow_succ, ih, pow_succ]
    calc
      Gi * A ^ p * G * (Gi * A * G) = Gi * A ^ p * (G * Gi) * A * G := by
        simp only [Matrix.mul_assoc]
      _ = Gi * (A ^ p * A) * G := by
        rw [h2]
        simp only [Matrix.mul_one, Matrix.mul_assoc]

lemma fvec_lt (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    fvec k r z ⟨a.val, by omega⟩ = bvec (eI k r a) := by
  unfold fvec; rw [dite_eq_left a.isLt]

end PI.StabSplit
end
end

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2

noncomputable section

namespace PI.StabSplit

theorem stabilizer_splitting_of_parts (hFS : FixSub) (hSF : SubFlag) (hUN : UnipN) (hNP : NPerp) : C1ii := by
  intro k r z z' γ hs hp
  have hz : inWb k r z := hs.2.1.1
  have hz' : inWb k r z' := hs.2.2.1
  have hγ : γ ∈ B.GV k r := hp.1
  have hγu : IsUnit γ.det := GV_unit k r hγ
  have hγ1 : γ⁻¹ * γ = 1 := nonsing_inv_mul γ hγu
  have hγ2 : γ * γ⁻¹ = 1 := mul_nonsing_inv γ hγu
  have hG : IsUnit ((Ym k r z z' γ)ᴴ * Hpk k r * Ym k r z z' γ).det := gram_unit k r z z' γ hs hp
  have hPY : Pm k r z z' γ * Ym k r z z' γ = Ym k r z z' γ := Proj.prj_Y _ _ hG
  have hPP : Pm k r z z' γ * Pm k r z z' γ = Pm k r z z' γ := Proj.prj_sq _ _ hG
  have hHh : (Hpk k r)ᴴ = Hpk k r := GBasic.Hpk_herm k r
  have hPH : (Pm k r z z' γ)ᴴ * Hpk k r = Hpk k r * Pm k r z z' γ := Proj.prj_star _ _ hHh
  have hLQ : ((Ym k r z z' γ)ᴴ * Hpk k r) * (1 - Pm k r z z' γ) = 0 := Proj.L_one_sub _ _ hG
  set Y := Ym k r z z' γ with hY
  set P := Pm k r z z' γ with hP

  have UW1 : ∀ w, (1 : B.Mat k r) ∈ UWset k r w := fun w => ⟨GV_one k r, fun a => by simp, by simp⟩
  have NS : ∀ w, ∀ g ∈ Nset k r, g ∈ Sset k r w := fun w g hg => ⟨1, UW1 w, g, hg, by simp⟩
  have Hmul : ∀ g ∈ Hst k r z z' γ, ∀ h ∈ Hst k r z z' γ, g * h ∈ Hst k r z z' γ := by
    rintro g ⟨hgS, s, hs1, rfl⟩ h ⟨hhS, t, ht1, rfl⟩
    refine ⟨(sGroup k r z hz).2.1 _ hgS _ hhS, s * t, (sGroup k r z' hz').2.1 _ hs1 _ ht1, ?_⟩
    calc γ * s * γ⁻¹ * (γ * t * γ⁻¹) = γ * s * (γ⁻¹ * γ) * t * γ⁻¹ := by noncomm_ring
      _ = γ * (s * t) * γ⁻¹ := by rw [hγ1]; noncomm_ring
  have Hinv : ∀ g ∈ Hst k r z z' γ, g⁻¹ ∈ Hst k r z z' γ := by
    rintro g ⟨hgS, s, hs1, rfl⟩
    refine ⟨(sGroup k r z hz).2.2 _ hgS, s⁻¹, (sGroup k r z' hz').2.2 _ hs1, ?_⟩
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, nonsing_inv_nonsing_inv γ hγu, Matrix.mul_assoc]
  have H_GV : ∀ g ∈ Hst k r z z' γ, g ∈ B.GV k r := fun g hg => (hSF k r z hz hg.1).1

  have spanF : ∀ a, flagSpan k r z a ≤ Submodule.span ℂ (Set.range (gramVec k r z z' γ)) := by
    intro a; rw [flagSpan, Submodule.span_le]; rintro _ ⟨b, rfl⟩
    exact Submodule.subset_span ⟨Sum.inl b.1, rfl⟩
  have spanF' : ∀ b, flagSpan k r z' b ≤
      (Submodule.span ℂ (Set.range (gramVec k r z z' γ))).comap (Matrix.mulVecLin γ) := by
    intro b; rw [flagSpan, Submodule.span_le]; rintro _ ⟨c, rfl⟩
    exact Submodule.mem_comap.2 (Submodule.subset_span ⟨Sum.inr c.1, rfl⟩)
  have Hcol : ∀ g ∈ Hst k r z z' γ, ∀ j,
      g *ᵥ gramVec k r z z' γ j ∈ Submodule.span ℂ (Set.range (gramVec k r z z' γ)) := by
    rintro g ⟨hgS, s, hs1, hgs⟩ j
    have hF := hSF k r z hz hgS
    have hF' := hSF k r z' hz' hs1
    rcases j with a | b
    · have h1 := spanF a (hF.2 a)
      have h2 : fvec k r z a ∈ Submodule.span ℂ (Set.range (gramVec k r z z' γ)) :=
        Submodule.subset_span ⟨Sum.inl a, rfl⟩
      have e : g *ᵥ gramVec k r z z' γ (Sum.inl a) = (g *ᵥ fvec k r z a - fvec k r z a) + fvec k r z a := by
        rw [sub_add_cancel]; rfl
      rw [e]; exact Submodule.add_mem _ h1 h2
    · have h1 : Matrix.mulVecLin γ (s *ᵥ fvec k r z' b - fvec k r z' b) ∈
          Submodule.span ℂ (Set.range (gramVec k r z z' γ)) := spanF' b (hF'.2 b)
      have h2 : γ *ᵥ fvec k r z' b ∈ Submodule.span ℂ (Set.range (gramVec k r z z' γ)) :=
        Submodule.subset_span ⟨Sum.inr b, rfl⟩
      rw [Matrix.mulVecLin_apply] at h1
      have e : g *ᵥ gramVec k r z z' γ (Sum.inr b) =
          γ *ᵥ (s *ᵥ fvec k r z' b - fvec k r z' b) + γ *ᵥ fvec k r z' b := by
        rw [← mulVec_add, sub_add_cancel, hgs]
        show (γ * s * γ⁻¹) *ᵥ (γ *ᵥ fvec k r z' b) = γ *ᵥ (s *ᵥ fvec k r z' b)
        rw [mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc, hγ1, Matrix.mul_one]
      rw [e]; exact Submodule.add_mem _ h1 h2
  have HC : ∀ g ∈ Hst k r z z' γ, ∃ C, g * Y = Y * C := by
    intro g hg
    refine Proj.exists_C Y (g * Y) (fun j => ?_)
    have e : (fun i => (g * Y) i j) = g *ᵥ gramVec k r z z' γ j := by
      ext i; simp [hY, Ym, Matrix.mul_apply, mulVec, dotProduct]
    rw [e]; exact Hcol g hg j
  have HM : ∀ g ∈ Hst k r z z' γ, (1 - P) * g * P = 0 := fun g hg => by
    obtain ⟨C, hC⟩ := HC g hg; exact Proj.presM _ Y hG g C hC
  have HU : ∀ g ∈ Hst k r z z' γ, P * g * (1 - P) = 0 := fun g hg => by
    obtain ⟨C, hC⟩ := HC g⁻¹ (Hinv g hg)
    exact Proj.presU _ Y hG g (H_GV g hg) (GV_unit k r (H_GV g hg)) C hC

  have U_P : ∀ v ∈ Uperp k r z z' γ, P *ᵥ v = 0 := fun v hv =>
    Proj.prj_mulVec_of_L _ Y ((mem_U_iff k r z z' γ v).1 hv)
  have Q_U : ∀ j, (fun i => (1 - P) i j) ∈ Uperp k r z z' γ := by
    intro j; rw [mem_U_iff]; ext l
    have := congrFun (congrFun hLQ l) j
    simpa [mulVec, dotProduct, Matrix.mul_apply] using this
  have fixU : ∀ g : B.Mat k r, (∀ v ∈ Uperp k r z z' γ, g *ᵥ v = v) → g * (1 - P) = 1 - P :=
    fun g hg => mul_eq_of_cols k r g (1 - P) (fun j => hg _ (Q_U j))
  have fixM : ∀ g : B.Mat k r, g * Y = Y → g * P = P := by
    intro g hg
    simp only [hP, Pm, Proj.prj, ← Matrix.mul_assoc]
    rw [hg]

  have hKH : KU k r z z' γ ⊆ Hst k r z z' γ := by
    rintro κ ⟨hκG, hκf⟩
    refine ⟨hFS k r z hz ⟨hκG, fun a => hκf (Sum.inl a)⟩, γ⁻¹ * κ * γ,
      hFS k r z' hz' ⟨GV_mul k r (GV_mul k r (GV_inv k r hγ) hκG) hγ, fun b => ?_⟩, ?_⟩
    · have h1 : κ *ᵥ (γ *ᵥ fvec k r z' b) = γ *ᵥ fvec k r z' b := hκf (Sum.inr b)
      rw [← mulVec_mulVec, ← mulVec_mulVec, h1, mulVec_mulVec, hγ1, one_mulVec]
    · calc κ = (γ * γ⁻¹) * κ * (γ * γ⁻¹) := by rw [hγ2]; simp
        _ = γ * (γ⁻¹ * κ * γ) * γ⁻¹ := by noncomm_ring

  have Rnil : ∀ g ∈ Rst k r z z' γ, (g - 1) ^ (r + 2) = 0 := by
    rintro g ⟨hgH, hgU⟩
    obtain ⟨hgS, s, hs1, hgs⟩ := hgH
    have hF := hSF k r z hz hgS
    have hF' := hSF k r z' hz' hs1
    have n1 : ∀ a, ((g - 1) ^ (r + 1)) *ᵥ fvec k r z a = 0 := flag_nilp_all g (fvec k r z) hF.2
    have n2 : ∀ b, ((g - 1) ^ (r + 1)) *ᵥ (γ *ᵥ fvec k r z' b) = 0 := by
      refine flag_nilp_all g (fun b => γ *ᵥ fvec k r z' b) (fun b => ?_)
      have e : g *ᵥ (γ *ᵥ fvec k r z' b) - γ *ᵥ fvec k r z' b =
          Matrix.mulVecLin γ (s *ᵥ fvec k r z' b - fvec k r z' b) := by
        rw [Matrix.mulVecLin_apply, mulVec_sub, hgs, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc,
          hγ1, Matrix.mul_one]
      rw [e]
      have hle : flagSpan k r z' b ≤ (Submodule.span ℂ (Set.range fun c : {c : Fin (r + 1) // c < b} =>
          γ *ᵥ fvec k r z' c.1)).comap (Matrix.mulVecLin γ) := by
        rw [flagSpan, Submodule.span_le]; rintro _ ⟨c, rfl⟩
        exact Submodule.mem_comap.2 (Submodule.subset_span ⟨c, rfl⟩)
      exact hle (hF'.2 b)
    have hY0 : (g - 1) ^ (r + 1) * Y = 0 := by
      ext i j
      rcases j with a | b
      · have := congrFun (n1 a) i
        simpa [hY, Ym, Matrix.mul_apply, mulVec, dotProduct, gramVec] using this
      · have := congrFun (n2 b) i
        simpa [hY, Ym, Matrix.mul_apply, mulVec, dotProduct, gramVec] using this
    have hP0 : (g - 1) ^ (r + 1) * P = 0 := by
      simp only [hP, Pm, Proj.prj, ← Matrix.mul_assoc]
      rw [← hY, hY0]; simp
    have hQ : (g - 1) * (1 - P) = 0 := by
      rw [Matrix.sub_mul, fixU g hgU, Matrix.one_mul, sub_self]
    exact Alg.nilp P g (r + 1) hPP hQ (HM g ⟨hgS, s, hs1, hgs⟩) hP0

  have hli : LinearIndependent ℂ (gramVec k r z z' γ) := by
    rw [Fintype.linearIndependent_iff]; intro c hc
    have h0 : c = 0 := Proj.Y_inj _ Y hG c (by rw [hY, Ym_mulVec]; exact hc)
    intro i; rw [h0]; rfl
  have hdis := hli.disjoint_span_image Set.isCompl_range_inl_range_inr.disjoint
  have hXl : Xsp k r ≤ Submodule.span ℂ (gramVec k r z z' γ '' Set.range Sum.inl) := by
    rw [Xsp, Submodule.span_le]; rintro _ ⟨a, rfl⟩
    exact Submodule.subset_span ⟨Sum.inl ⟨a.val, by omega⟩, ⟨_, rfl⟩, fvec_lt k r z a⟩
  have hXr : Xsp k r ≤ (Submodule.span ℂ (gramVec k r z z' γ '' Set.range Sum.inr)).comap
      (Matrix.mulVecLin γ) := by
    rw [Xsp, Submodule.span_le]; rintro _ ⟨a, rfl⟩
    refine Submodule.mem_comap.2 (Submodule.subset_span ⟨Sum.inr ⟨a.val, by omega⟩, ⟨_, rfl⟩, ?_⟩)
    show γ *ᵥ fvec k r z' ⟨a.val, _⟩ = _
    rw [fvec_lt k r z' a]; rfl
  have hR : Rst k r z z' γ = {g | g ∈ Nset k r ∧ ∃ n ∈ Nset k r, g = γ * n * γ⁻¹} := by
    ext g; constructor
    · intro hg
      have hn := Rnil g hg
      obtain ⟨⟨hgS, s, hs1, hgs⟩, -⟩ := hg
      refine ⟨hUN k r z hs.2.1 g hgS (r + 2) hn, s, hUN k r z' hs.2.2 s hs1 (r + 2) ?_, hgs⟩
      have hsg : s = γ⁻¹ * g * γ := by
        rw [hgs]
        calc s = (γ⁻¹ * γ) * s * (γ⁻¹ * γ) := by rw [hγ1]; simp
          _ = γ⁻¹ * (γ * s * γ⁻¹) * γ := by noncomm_ring
      have e : s - 1 = γ⁻¹ * (g - 1) * γ := by
        calc s - 1 = γ⁻¹ * g * γ - γ⁻¹ * γ := by rw [hγ1, ← hsg]
          _ = γ⁻¹ * (g - 1) * γ := by noncomm_ring
      rw [e]
      have hp : ∀ n : ℕ, (γ⁻¹ * (g - 1) * γ) ^ n = γ⁻¹ * (g - 1) ^ n * γ := by
        intro n
        induction n with
        | zero => simp [hγ1]
        | succ n ih =>
          rw [pow_succ, ih, pow_succ]
          calc
            γ⁻¹ * (g - 1) ^ n * γ * (γ⁻¹ * (g - 1) * γ) =
                γ⁻¹ * ((g - 1) ^ n * (γ * γ⁻¹)) * (g - 1) * γ := by noncomm_ring
            _ = γ⁻¹ * ((g - 1) ^ n * (g - 1)) * γ := by rw [hγ2]; noncomm_ring
            _ = γ⁻¹ * (g - 1) ^ (n + 1) * γ := by rw [pow_succ]
      rw [hp (r + 2), hn]
      simp
    · rintro ⟨hgN, n, hnN, hgn⟩
      refine ⟨⟨NS z g hgN, n, NS z' n hnN, hgn⟩, fun v hv => ?_⟩
      have hL : ∀ j, herm (Hpk k r) v (gramVec k r z z' γ j) = 0 := fun j => by
        rw [← L_mulVec, (mem_U_iff k r z z' γ v).1 hv]; rfl
      have h1 : (g - 1) *ᵥ v ∈ Xsp k r := hNP k r g hgN v (fun a => by
        have := hL (Sum.inl ⟨a.val, by omega⟩)
        rw [← fvec_lt k r z a]; exact this)
      have h2 : (n - 1) *ᵥ (γ⁻¹ *ᵥ v) ∈ Xsp k r := hNP k r n hnN _ (fun a => by
        have := hL (Sum.inr ⟨a.val, by omega⟩)
        rw [← herm_unit k r hγ, mulVec_mulVec, hγ2, one_mulVec, ← fvec_lt k r z' a]
        exact this)
      have e : (g - 1) *ᵥ v = Matrix.mulVecLin γ ((n - 1) *ᵥ (γ⁻¹ *ᵥ v)) := by
        rw [Matrix.mulVecLin_apply, mulVec_mulVec, mulVec_mulVec, hgn]
        congr 1
        calc γ * n * γ⁻¹ - 1 = γ * n * γ⁻¹ - γ * γ⁻¹ := by rw [hγ2]
          _ = γ * (n - 1) * γ⁻¹ := by noncomm_ring
      have m1 := hXl h1
      have m2 : (g - 1) *ᵥ v ∈ Submodule.span ℂ (gramVec k r z z' γ '' Set.range Sum.inr) := by
        rw [e]; exact hXr h2
      have h0 := Submodule.disjoint_def.1 hdis _ m1 m2
      have : g *ᵥ v - v = 0 := by rw [← h0, sub_mulVec, one_mulVec]
      exact sub_eq_zero.1 this

  have hc : ∀ h ∈ Hst k r z z' γ, ∃! p : B.Mat k r × B.Mat k r,
      p.1 ∈ Rst k r z z' γ ∧ p.2 ∈ KU k r z z' γ ∧ h = p.1 * p.2 := by
    intro h hh
    have hhG := H_GV h hh
    have hU := HU h hh
    have hκG : h * (1 - P) + P ∈ B.GV k r := Alg.unitK (Hpk k r) P h hHh hPH hPP hhG hU
    have hκY : (h * (1 - P) + P) * Y = Y := by
      rw [Matrix.add_mul, Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, hPY, sub_self,
        Matrix.mul_zero, zero_add]
    have hκK : h * (1 - P) + P ∈ KU k r z z' γ := ⟨hκG, fun i => mulVec_col_of_mul k r _ Y hκY i⟩
    have hdec : (h * P + (1 - P)) * (h * (1 - P) + P) = h := Alg.decomp h P hPP hU
    have hκu : IsUnit (h * (1 - P) + P).det := GV_unit k r hκG
    have hρeq : h * P + (1 - P) = h * (h * (1 - P) + P)⁻¹ := by
      calc h * P + (1 - P) = (h * P + (1 - P)) * ((h * (1 - P) + P) * (h * (1 - P) + P)⁻¹) := by
            rw [mul_nonsing_inv _ hκu, Matrix.mul_one]
        _ = h * (h * (1 - P) + P)⁻¹ := by rw [← Matrix.mul_assoc, hdec]
    have hρH : h * P + (1 - P) ∈ Hst k r z z' γ := by
      rw [hρeq]; exact Hmul h hh _ (Hinv _ (hKH hκK))
    have hρR : h * P + (1 - P) ∈ Rst k r z z' γ := ⟨hρH, fun v hv => by
      rw [add_mulVec, ← mulVec_mulVec, U_P v hv, mulVec_zero, zero_add, sub_mulVec, one_mulVec,
        U_P v hv, sub_zero]⟩
    refine ⟨(h * P + (1 - P), h * (1 - P) + P), ⟨hρR, hκK, hdec.symm⟩, ?_⟩
    rintro ⟨ρ₁, κ₁⟩ ⟨hρ₁, hκ₁, h₁⟩
    have u := Alg.uniq h P ρ₁ κ₁ h₁.symm (fixU ρ₁ hρ₁.2)
      (fixM κ₁ (mul_eq_of_cols k r κ₁ Y hκ₁.2)) (HU κ₁ (hKH hκ₁))
    exact Prod.ext u.1 u.2

  have hd : ∀ ρ ∈ Rst k r z z' γ, ∀ κ ∈ KU k r z z' γ, ρ * κ = κ * ρ := fun ρ hρ κ hκ =>
    Alg.comm P ρ κ (fixU ρ hρ.2) (fixM κ (mul_eq_of_cols k r κ Y hκ.2)) (HM ρ hρ.1) (HU κ (hKH hκ))

  have he : ∀ ρ ∈ Rst k r z z' γ, (ρ - 1) ^ (2 * r + k + 1) = 0 := fun ρ hρ => by
    have e : r + 2 ≤ 2 * r + k + 1 := by have := hs.1; omega
    exact pow_eq_zero_of_le e (Rnil ρ hρ)
  exact ⟨hKH, hR, hc, hd, he⟩

end PI.StabSplit
