module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSPointwise

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJfSSymDefs
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JfS.Sym

noncomputable section

def Xuv (k r : ℕ) (u v : Fin (2 * r + k + 1) → ℂ) : B.Mat k r :=
  vecMulVec u (star (Hpk k r *ᵥ v)) - vecMulVec v (star (Hpk k r *ᵥ u))

end

end Formalism.FourierDecayAlt.P.CutMP.JfS.Sym
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJfSSymbolW
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.HermSelfNeZero
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.HermZeroOfTrace
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.HermZeroRight
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JfS.Sym

noncomputable section

variable {k r : ℕ}

theorem hpk_mulVec (x : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ x) i = if i.val < r ∨ r + k < i.val then x ⟨2 * r + k - i.val, by omega⟩
      else if i.val = r + k then -x i else x i := by
  rw [mulVec, dotProduct]
  by_cases h : i.val < r ∨ r + k < i.val
  · rw [if_pos h, Finset.sum_eq_single ⟨2 * r + k - i.val, by omega⟩]
    · have : Hpk k r i ⟨2 * r + k - i.val, by omega⟩ = 1 := by
        unfold Hpk
        rcases h with h | h
        · rw [if_pos ⟨h, by simp; omega⟩]
        · rw [if_neg (by simp; omega), if_pos ⟨by simp; omega, by simp; omega⟩]
      rw [this, one_mul]
    · intro j _ hj
      have : Hpk k r i j = 0 := by
        unfold Hpk
        have hj' : j.val ≠ 2 * r + k - i.val := fun e => hj (Fin.ext (by simpa using e))
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      rw [this, zero_mul]
    · intro h'; exact absurd (Finset.mem_univ _) h'
  · rw [if_neg h, Finset.sum_eq_single i]
    · unfold Hpk
      rw [if_neg (by omega), if_neg (by omega), if_pos ⟨by omega, by omega, rfl⟩]
      split_ifs <;> ring
    · intro j _ hj
      have : Hpk k r i j = 0 := by
        unfold Hpk
        rw [if_neg (by omega), if_neg (by omega), if_neg (fun e => hj e.2.2.symm)]
      rw [this, zero_mul]
    · intro h'; exact absurd (Finset.mem_univ _) h'

theorem hpk_symm' : (Hpk k r)ᵀ = Hpk k r := by
  ext i j
  simp only [transpose_apply, Hpk]
  by_cases h1 : j.val < r ∧ j.val + i.val = 2 * r + k
  · rw [if_pos h1]
    by_cases h2 : i.val < r ∧ i.val + j.val = 2 * r + k
    · rw [if_pos h2]
    · rw [if_neg h2, if_pos ⟨h1.1, by omega⟩]
  · rw [if_neg h1]
    by_cases h2 : i.val < r ∧ j.val + i.val = 2 * r + k
    · rw [if_pos h2, if_pos ⟨h2.1, by omega⟩]
    · rw [if_neg h2]
      by_cases h3 : i.val < r ∧ i.val + j.val = 2 * r + k
      · exact absurd ⟨h3.1, by omega⟩ h2
      · by_cases h4 : j.val < r ∧ i.val + j.val = 2 * r + k
        · exact absurd ⟨h4.1, by omega⟩ h1
        · rw [if_neg h3, if_neg h4]
          by_cases h5 : i = j
          · subst h5; rfl
          · rw [if_neg (fun e => h5 e.2.2.symm), if_neg (fun e => h5 e.2.2)]

theorem hpk_conjT : (Hpk k r)ᴴ = Hpk k r := by
  ext i j
  rw [conjTranspose_apply, ← transpose_apply (Hpk k r) j i, hpk_symm']
  unfold Hpk
  split_ifs <;> simp

theorem herm_eq (x y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) x y = ∑ i, star (y i) * (Hpk k r *ᵥ x) i := rfl

theorem herm_add_left (x x' y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (x + x') y = herm (Hpk k r) x y + herm (Hpk k r) x' y := by
  simp only [herm, mulVec_add, dotProduct_add]

theorem herm_smul_left (c : ℂ) (x y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (c • x) y = c * herm (Hpk k r) x y := by
  simp only [herm, mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem herm_sub_left (x x' y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (x - x') y = herm (Hpk k r) x y - herm (Hpk k r) x' y := by
  simp only [herm, mulVec_sub, dotProduct_sub]

theorem herm_add_right (x y y' : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) x (y + y') = herm (Hpk k r) x y + herm (Hpk k r) x y' := by
  simp only [herm, star_add, add_dotProduct]

theorem herm_smul_right (c : ℂ) (x y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) x (c • y) = star c * herm (Hpk k r) x y := by
  simp only [herm, star_smul, smul_dotProduct, smul_eq_mul]

theorem herm_zero_left (y : Fin (2 * r + k + 1) → ℂ) : herm (Hpk k r) 0 y = 0 := by
  simp [herm]

theorem herm_zero_right (x : Fin (2 * r + k + 1) → ℂ) : herm (Hpk k r) x 0 = 0 := by
  simp [herm]

theorem herm_swap (x y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) x y = star (herm (Hpk k r) y x) := by
  simp only [herm]
  rw [star_dotProduct, star_mulVec, hpk_conjT, dotProduct_mulVec]

theorem herm_skew {ξ : B.Mat k r} (hξ : B.inLie k r ξ) (x y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (ξ *ᵥ x) y = -herm (Hpk k r) x (ξ *ᵥ y) := by
  have h : ξᴴ * Hpk k r = -(Hpk k r * ξ) := eq_neg_of_add_eq_zero_left hξ
  simp only [herm]
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, h, neg_mulVec, dotProduct_neg, neg_neg]

theorem trace_xuv (ξ : B.Mat k r) (u v : Fin (2 * r + k + 1) → ℂ) :
    Matrix.trace (ξ * Xuv k r u v) = herm (Hpk k r) (ξ *ᵥ u) v - herm (Hpk k r) (ξ *ᵥ v) u := by
  have key : ∀ a b : Fin (2 * r + k + 1) → ℂ,
      Matrix.trace (ξ * vecMulVec a (star (Hpk k r *ᵥ b))) = herm (Hpk k r) (ξ *ᵥ a) b := by
    intro a b
    have hb : star (Hpk k r *ᵥ b) = star b ᵥ* Hpk k r := by
      rw [star_mulVec, hpk_conjT]
    rw [hb, herm, dotProduct_mulVec]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, vecMulVec_apply, dotProduct, mulVec]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  rw [Xuv, Matrix.mul_sub, Matrix.trace_sub, key, key]

end

end Formalism.FourierDecayAlt.P.CutMP.JfS.Sym
end

open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JfS.Sym

noncomputable section

variable {k r : ℕ}

theorem herm_zero_of_trace {ζ : B.Mat k r} (hζ : B.inLie k r ζ) (u v : Fin (2 * r + k + 1) → ℂ)
    (h1 : (Matrix.trace (ζ * Xuv k r u v)).re = 0)
    (h2 : (Matrix.trace (ζ * Xuv k r u (Complex.I • v))).re = 0) :
    herm (Hpk k r) (ζ *ᵥ u) v = 0 := by
  rw [trace_xuv] at h1 h2
  have hs : ∀ w, herm (Hpk k r) (ζ *ᵥ w) u = -star (herm (Hpk k r) (ζ *ᵥ u) w) := by
    intro w
    rw [herm_skew hζ, herm_swap w]
  rw [hs] at h1 h2
  rw [herm_smul_right] at h2
  set A := herm (Hpk k r) (ζ *ᵥ u) v
  simp [Complex.ext_iff, Complex.mul_re, Complex.mul_im] at h1 h2 ⊢
  constructor <;> linarith

theorem herm_bvec (x : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    herm (Hpk k r) x (bvec i) = (Hpk k r *ᵥ x) i := by
  rw [herm_eq, Finset.sum_eq_single i]
  · simp [bvec]
  · intro j _ hj; simp [bvec, hj]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem herm_e (x : Fin (2 * r + k + 1) → ℂ) (b : Fin r) :
    herm (Hpk k r) x (bvec (eI k r b)) = x (esI k r b) := by
  rw [herm_bvec, hpk_mulVec, if_pos (Or.inl (by simp [eI]))]
  rfl

theorem herm_es (x : Fin (2 * r + k + 1) → ℂ) (b : Fin r) :
    herm (Hpk k r) x (bvec (esI k r b)) = x (eI k r b) := by
  rw [herm_bvec, hpk_mulVec, if_pos (Or.inr (by simp [esI]; omega))]
  congr 1
  apply Fin.ext
  simp [eI, esI]
  omega

theorem herm_w (x : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) (h1 : r ≤ i.val) (h2 : i.val ≤ r + k) :
    herm (Hpk k r) x (bvec i) = if i.val = r + k then -x i else x i := by
  rw [herm_bvec, hpk_mulVec, if_neg (by omega)]

theorem inWb_sub {u v : Fin (2 * r + k + 1) → ℂ} (hu : inWb k r u) (hv : inWb k r v) : inWb k r (u - v) := by
  intro i hi; simp [hu i hi, hv i hi]

theorem inWb_smul (c : ℂ) {u : Fin (2 * r + k + 1) → ℂ} (hu : inWb k r u) : inWb k r (c • u) := by
  intro i hi; simp [hu i hi]

def sg (i : Fin (2 * r + k + 1)) : ℂ := if i.val = r + k then -1 else 1

theorem hpk_mulVec_wb {u : Fin (2 * r + k + 1) → ℂ} (hu : inWb k r u) (i : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ u) i = sg (k := k) (r := r) i * u i := by
  rw [hpk_mulVec, sg]
  by_cases h : i.val < r ∨ r + k < i.val
  · rw [if_pos h, hu i h, hu ⟨2 * r + k - i.val, by omega⟩ (by simp; omega), mul_zero]
  · rw [if_neg h]
    split_ifs <;> ring

def KI (k r : ℕ) : Fin (2 * r + k + 1) := ⟨r + k, by omega⟩

theorem herm_wb {u : Fin (2 * r + k + 1) → ℂ} (hu : inWb k r u) (y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) u y = ∑ i ∈ Finset.univ.erase (KI k r), star (y i) * u i - star (y (KI k r)) * u (KI k r) := by
  rw [herm_eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ (KI k r))]
  have hK : sg (k := k) (r := r) (KI k r) = -1 := by simp [sg, KI]
  rw [hpk_mulVec_wb hu, hK]
  have : ∀ i ∈ Finset.univ.erase (KI k r), star (y i) * (Hpk k r *ᵥ u) i = star (y i) * u i := by
    intro i hi
    rw [hpk_mulVec_wb hu]
    have : i.val ≠ r + k := fun e => (Finset.mem_erase.1 hi).1 (Fin.ext (by simp [KI, e]))
    simp [sg, this]
  rw [Finset.sum_congr rfl this]
  ring

theorem re_star_mul_self (a : ℂ) : (star a * a).re = ‖a‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [Complex.mul_re]

theorem wb_definite {z w : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z)
    (hw : inWb k r w) (hwz : herm (Hpk k r) w z = 0) (hww : (herm (Hpk k r) w w).re ≤ 0) : w = 0 := by
  set S := Finset.univ.erase (KI k r)
  set K := KI k r
  have e2 : (herm (Hpk k r) w w).re = ∑ i ∈ S, ‖w i‖ ^ 2 - ‖w K‖ ^ 2 := by
    rw [herm_wb hw, Complex.sub_re, Complex.re_sum, re_star_mul_self]
    simp only [re_star_mul_self]
    rfl
  have eT : Tz k r z = ‖z K‖ ^ 2 - ∑ i ∈ S, ‖z i‖ ^ 2 := by
    rw [Tz, herm_wb hz, Complex.sub_re, Complex.re_sum, re_star_mul_self]
    simp only [re_star_mul_self]
    ring
  rw [herm_wb hw, sub_eq_zero] at hwz
  have hn : ‖z K‖ * ‖w K‖ ≤ ∑ i ∈ S, ‖z i‖ * ‖w i‖ := by
    calc ‖z K‖ * ‖w K‖ = ‖star (z K) * w K‖ := by rw [norm_mul, norm_star]
      _ = ‖∑ i ∈ S, star (z i) * w i‖ := by rw [hwz]
      _ ≤ ∑ i ∈ S, ‖star (z i) * w i‖ := norm_sum_le _ _
      _ = ∑ i ∈ S, ‖z i‖ * ‖w i‖ := by simp only [norm_mul, norm_star]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S (fun i => ‖z i‖) (fun i => ‖w i‖)
  set P := ∑ i ∈ S, ‖w i‖ ^ 2
  set Q := ∑ i ∈ S, ‖z i‖ ^ 2
  set m := ∑ i ∈ S, ‖z i‖ * ‖w i‖
  have hP : 0 ≤ P := Finset.sum_nonneg (fun i _ => by positivity)
  have hQ : 0 ≤ Q := Finset.sum_nonneg (fun i _ => by positivity)
  have ha : 0 ≤ ‖w K‖ := norm_nonneg _
  have hc : 0 ≤ ‖z K‖ := norm_nonneg _
  have h1 : P ≤ ‖w K‖ ^ 2 := by linarith
  have h2 : Q < ‖z K‖ ^ 2 := by linarith
  have h3 : (‖z K‖ * ‖w K‖) ^ 2 ≤ m ^ 2 := by
    have : 0 ≤ ‖z K‖ * ‖w K‖ := by positivity
    exact pow_le_pow_left₀ this hn 2
  have h4 : (‖z K‖ * ‖w K‖) ^ 2 ≤ Q * ‖w K‖ ^ 2 := by
    calc (‖z K‖ * ‖w K‖) ^ 2 ≤ m ^ 2 := h3
      _ ≤ Q * P := hcs
      _ ≤ Q * ‖w K‖ ^ 2 := mul_le_mul_of_nonneg_left h1 hQ
  have h5 : ‖w K‖ ^ 2 * (‖z K‖ ^ 2 - Q) ≤ 0 := by nlinarith
  have h6 : ‖w K‖ ^ 2 ≤ 0 := by
    by_contra hcon
    push Not at hcon
    have : 0 < ‖w K‖ ^ 2 * (‖z K‖ ^ 2 - Q) := mul_pos hcon (by linarith)
    linarith
  have hwK : w K = 0 := by
    have : ‖w K‖ = 0 := by nlinarith
    exact norm_eq_zero.1 this
  have hP0 : P = 0 := le_antisymm (by nlinarith) hP
  have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)).1 hP0
  funext i
  by_cases hi : i = K
  · rw [hi, hwK]; rfl
  · have := hall i (Finset.mem_erase.2 ⟨hi, Finset.mem_univ _⟩)
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, norm_eq_zero] at this
    rw [this]; rfl

end

end Formalism.FourierDecayAlt.P.CutMP.JfS.Sym
end

open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JfS.Sym

noncomputable section

variable {k r : ℕ}

theorem herm_self_ne_zero {z : Fin (2 * r + k + 1) → ℂ} (hT : 0 < Tz k r z) : herm (Hpk k r) z z ≠ 0 := by
  intro h
  rw [Tz, h] at hT
  simp at hT

theorem herm_proj_zero (x z : Fin (2 * r + k + 1) → ℂ) (hc : herm (Hpk k r) z z ≠ 0) :
    herm (Hpk k r) (x - (herm (Hpk k r) x z / herm (Hpk k r) z z) • z) z = 0 := by
  rw [herm_sub_left, herm_smul_left]
  field_simp
  ring

theorem coreW {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z) (ξ : B.Mat k r)
    (h1 : ∀ u, inWb k r u → inWb k r (ξ *ᵥ u))
    (h2 : ∀ u v, inWb k r u → inWb k r v → herm (Hpk k r) (ξ *ᵥ u) v = -herm (Hpk k r) u (ξ *ᵥ v))
    (h3 : ∀ u v, inWb k r u → inWb k r v → herm (Hpk k r) u z = 0 → herm (Hpk k r) v z = 0 →
      herm (Hpk k r) (ξ *ᵥ u) v = 0)
    (N : ℕ) (h4 : ∀ u, inWb k r u → (ξ ^ N) *ᵥ u = 0) :
    ∀ u, inWb k r u → ξ *ᵥ u = 0 := by
  set c := herm (Hpk k r) z z with hcdef
  have hc0 : c ≠ 0 := herm_self_ne_zero hT

  have stepA : ∀ w, inWb k r w → herm (Hpk k r) w z = 0 →
      ξ *ᵥ w = (herm (Hpk k r) (ξ *ᵥ w) z / c) • z := by
    intro w hw hwz
    set y := ξ *ᵥ w - (herm (Hpk k r) (ξ *ᵥ w) z / c) • z with hydef
    have hy : inWb k r y := inWb_sub (h1 w hw) (inWb_smul _ hz)
    have hyz : herm (Hpk k r) y z = 0 := herm_proj_zero _ _ hc0
    have hyy : herm (Hpk k r) y y = 0 := by
      have e1 : herm (Hpk k r) (ξ *ᵥ w) y = 0 := h3 w y hw hy hwz hyz
      have e2 : herm (Hpk k r) z y = 0 := by rw [herm_swap, hyz, star_zero]
      calc herm (Hpk k r) y y
          = herm (Hpk k r) (ξ *ᵥ w) y - (herm (Hpk k r) (ξ *ᵥ w) z / c) * herm (Hpk k r) z y := by
            conv_lhs => rw [hydef]
            rw [herm_sub_left, herm_smul_left]
        _ = 0 := by rw [e1, e2]; ring
    have : y = 0 := wb_definite hz hT hy hyz (by rw [hyy]; simp)
    exact sub_eq_zero.1 this
  set μ := herm (Hpk k r) (ξ *ᵥ z) z / c with hμ
  set b := ξ *ᵥ z - μ • z with hbdef
  have hb : inWb k r b := inWb_sub (h1 z hz) (inWb_smul _ hz)
  have hbz : herm (Hpk k r) b z = 0 := herm_proj_zero _ _ hc0
  have hξz : ξ *ᵥ z = μ • z + b := by rw [hbdef]; abel

  have stepB : ∀ w, inWb k r w → herm (Hpk k r) w z = 0 →
      ξ *ᵥ w = (-(herm (Hpk k r) w b) / c) • z := by
    intro w hw hwz
    rw [stepA w hw hwz, h2 w z hw hz, hξz, herm_add_right, herm_smul_right, hwz]
    congr 1
    ring
  have hξb : ξ *ᵥ b = (-(herm (Hpk k r) b b) / c) • z := stepB b hb hbz
  have hNz := h4 z hz

  have hb0 : b = 0 := by
    by_contra hb0
    have hbb : herm (Hpk k r) b b ≠ 0 := by
      intro h
      exact hb0 (wb_definite hz hT hb hbz (by rw [h]; simp))
    set l := -(herm (Hpk k r) b b) / c with hl
    have hl0 : l ≠ 0 := div_ne_zero (neg_ne_zero.2 hbb) hc0
    let f : ℕ → ℂ × ℂ := fun m => Nat.rec (motive := fun _ => ℂ × ℂ) (1, 0)
      (fun _ pq => (μ * pq.1 + l * pq.2, pq.1)) m
    have hf0 : f 0 = (1, 0) := rfl
    have hfs : ∀ m, f (m + 1) = (μ * (f m).1 + l * (f m).2, (f m).1) := fun m => rfl
    have hpow : ∀ m, (ξ ^ m) *ᵥ z = (f m).1 • z + (f m).2 • b := by
      intro m
      induction m with
      | zero => rw [hf0, pow_zero, one_mulVec]; simp
      | succ m ih =>
        rw [pow_succ', ← mulVec_mulVec, ih, mulVec_add, mulVec_smul, mulVec_smul, hξz, hξb, hfs]
        module
    rw [hpow] at hNz
    have hp : (f N).1 = 0 := by
      have := congrArg (fun x => herm (Hpk k r) x z) hNz
      simp only [herm_add_left, herm_smul_left, hbz, herm_zero_left, mul_zero, add_zero] at this
      exact (mul_eq_zero.1 this).resolve_right hc0
    have hq : (f N).2 = 0 := by
      rw [hp, zero_smul, zero_add] at hNz
      exact (smul_eq_zero.1 hNz).resolve_right hb0
    have hnz : ∀ m, (f m).1 ≠ 0 ∨ (f m).2 ≠ 0 := by
      intro m
      induction m with
      | zero => left; rw [hf0]; exact one_ne_zero
      | succ m ih =>
        by_contra hcon
        push Not at hcon
        rw [hfs] at hcon
        obtain ⟨e1, e2⟩ := hcon
        simp only at e1 e2
        rw [e2, mul_zero, zero_add] at e1
        have : (f m).2 = 0 := (mul_eq_zero.1 e1).resolve_left hl0
        rcases ih with h | h
        · exact h e2
        · exact h this
    rcases hnz N with h | h
    · exact h hp
    · exact h hq

  have hξz' : ξ *ᵥ z = μ • z := by rw [hξz, hb0, add_zero]
  have hpow2 : ∀ m, (ξ ^ m) *ᵥ z = μ ^ m • z := by
    intro m
    induction m with
    | zero => rw [pow_zero, one_mulVec, pow_zero, one_smul]
    | succ m ih => rw [pow_succ', ← mulVec_mulVec, ih, mulVec_smul, hξz', smul_smul, pow_succ]
  rw [hpow2] at hNz
  have hμ0 : μ = 0 := by
    have := congrArg (fun x => herm (Hpk k r) x z) hNz
    simp only [herm_smul_left, herm_zero_left] at this
    exact pow_eq_zero_iff'.1 ((mul_eq_zero.1 this).resolve_right hc0) |>.1
  have hξz0 : ξ *ᵥ z = 0 := by rw [hξz', hμ0, zero_smul]
  intro u hu
  set α := herm (Hpk k r) u z / c
  have hu' : inWb k r (u - α • z) := inWb_sub hu (inWb_smul _ hz)
  have hu'z : herm (Hpk k r) (u - α • z) z = 0 := herm_proj_zero _ _ hc0
  have e : u = α • z + (u - α • z) := by abel
  rw [e, mulVec_add, mulVec_smul, hξz0, stepB _ hu' hu'z, hb0, herm_zero_right]
  simp

end

end Formalism.FourierDecayAlt.P.CutMP.JfS.Sym
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJfSSymExp
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JfS.Sym

noncomputable section

lemma expS_summable {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    Summable (fun m : ℕ => ((m.factorial : ℂ))⁻¹ • X ^ m) := by
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  exact NormedSpace.expSeries_summable' X

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def mvL {n : ℕ} (y : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ →L[ℂ] (Fin n → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M *ᵥ y
      map_add' := fun M N => Matrix.add_mulVec M N y
      map_smul' := fun c M => Matrix.smul_mulVec c M y }

lemma mvL_apply {n : ℕ} (y : Fin n → ℂ) (M : Matrix (Fin n) (Fin n) ℂ) : mvL y M = M *ᵥ y := rfl

lemma exp_mulVec_sq {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (y : Fin n → ℂ) (h : X *ᵥ (X *ᵥ y) = 0) :
    NormedSpace.exp X *ᵥ y = y + X *ᵥ y := by
  have hs := expS_summable X
  rw [NormedSpace.exp_eq_tsum (𝕂 := ℂ)]
  show (∑' m : ℕ, ((m.factorial : ℂ))⁻¹ • X ^ m) *ᵥ y = y + X *ᵥ y
  rw [← mvL_apply y, ContinuousLinearMap.map_tsum (mvL y) hs]
  rw [tsum_eq_sum (s := Finset.range 2) ?_]
  · simp [Finset.sum_range_succ, mvL_apply, Matrix.smul_mulVec]
  · intro m hm
    simp only [Finset.mem_range, not_lt] at hm
    rw [mvL_apply, Matrix.smul_mulVec]
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
    rw [pow_add, ← Matrix.mulVec_mulVec, pow_two, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero, smul_zero]

lemma exp_smul_mulVec_sq {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (y : Fin n → ℂ) (h : X *ᵥ (X *ᵥ y) = 0)
    (c : ℂ) : NormedSpace.exp (c • X) *ᵥ y = y + c • (X *ᵥ y) := by
  have h' : (c • X) *ᵥ ((c • X) *ᵥ y) = 0 := by
    rw [Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.mulVec_smul, h, smul_zero, smul_zero]
  rw [exp_mulVec_sq (c • X) y h', Matrix.smul_mulVec]

lemma exp_smul_mulVec_fix {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (y : Fin n → ℂ) (h : X *ᵥ y = 0)
    (c : ℂ) : NormedSpace.exp (c • X) *ᵥ y = y := by
  have h2 : X *ᵥ (X *ᵥ y) = 0 := by rw [h, Matrix.mulVec_zero]
  rw [exp_smul_mulVec_sq X y h2 c, h, smul_zero, add_zero]

variable {k r : ℕ}

lemma hpk_star (i j : Fin (2 * r + k + 1)) : star (Hpk k r i j) = Hpk k r i j := by
  unfold Hpk
  split_ifs <;> simp

lemma hpk_symm (i j : Fin (2 * r + k + 1)) : Hpk k r i j = Hpk k r j i := by
  by_cases hij : i = j
  · subst hij
    rfl
  · have hji : ¬ j = i := fun h => hij h.symm
    unfold Hpk
    simp only [hij, hji, and_false, if_false]
    split_ifs <;> first | rfl | (exfalso; omega)

lemma herm_conj (y w : Fin (2 * r + k + 1) → ℂ) : herm (Hpk k r) y w = star (herm (Hpk k r) w y) := by
  simp only [herm, dotProduct, mulVec, star_sum, star_mul', star_star, Pi.star_apply, hpk_star,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hpk_symm j i]
  ring

lemma vmv_mulVec {n : ℕ} (u w y : Fin n → ℂ) : vecMulVec u w *ᵥ y = (w ⬝ᵥ y) • u := by
  ext i
  simp only [vecMulVec, mulVec, dotProduct, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

lemma star_hpk_dot (v y : Fin (2 * r + k + 1) → ℂ) : star (Hpk k r *ᵥ v) ⬝ᵥ y = herm (Hpk k r) y v := by
  simp only [herm, dotProduct, mulVec, star_sum, star_mul', Pi.star_apply, hpk_star, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hpk_symm j i]
  ring

theorem xuv_mulVec (u v y : Fin (2 * r + k + 1) → ℂ) :
    Xuv k r u v *ᵥ y = herm (Hpk k r) y v • u - herm (Hpk k r) y u • v := by
  unfold Xuv
  rw [Matrix.sub_mulVec, vmv_mulVec, vmv_mulVec, star_hpk_dot, star_hpk_dot]

theorem xuv_inLie (u v : Fin (2 * r + k + 1) → ℂ) : B.inLie k r (Xuv k r u v) := by
  have hH : (Hpk k r)ᴴ = Hpk k r := (hpkFacts k r).1
  have e1 : star (Hpk k r *ᵥ u) = star u ᵥ* Hpk k r := by rw [Matrix.star_mulVec, hH]
  have e2 : star (Hpk k r *ᵥ v) = star v ᵥ* Hpk k r := by rw [Matrix.star_mulVec, hH]
  unfold B.inLie Xuv
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_vecMulVec, Matrix.conjTranspose_vecMulVec,
    star_star, star_star, Matrix.sub_mul, Matrix.mul_sub, Matrix.vecMulVec_mul, Matrix.vecMulVec_mul,
    Matrix.mul_vecMulVec, Matrix.mul_vecMulVec, e1, e2]
  abel

lemma mat_eq_mulVec_bvec {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) : M i j = (M *ᵥ bvec j) i := by
  simp [bvec, Matrix.mulVec_single]

lemma herm_bvec_left (p : Fin (2 * r + k + 1)) (w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (bvec p) w = ∑ i, star (w i) * Hpk k r i p := by
  simp [herm, bvec, dotProduct, Matrix.mulVec_single]

lemma herm_bvec_bvec (p q : Fin (2 * r + k + 1)) : herm (Hpk k r) (bvec p) (bvec q) = Hpk k r q p := by
  rw [herm_bvec_left]
  simp [bvec, Pi.single_apply]

lemma hpk_col_eI (c : Fin r) (i : Fin (2 * r + k + 1)) :
    Hpk k r i (eI k r c) = if i = esI k r c then 1 else 0 := by
  have hc := c.isLt
  have hi := i.isLt
  unfold Hpk
  simp only [eI, esI, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

lemma hpk_col_esI (c : Fin r) (i : Fin (2 * r + k + 1)) :
    Hpk k r i (esI k r c) = if i = eI k r c then 1 else 0 := by
  have hc := c.isLt
  have hi := i.isLt
  unfold Hpk
  simp only [eI, esI, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

lemma herm_eI_left (c : Fin r) (w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (bvec (eI k r c)) w = star (w (esI k r c)) := by
  rw [herm_bvec_left]
  simp [hpk_col_eI]

lemma herm_esI_left (c : Fin r) (w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (bvec (esI k r c)) w = star (w (eI k r c)) := by
  rw [herm_bvec_left]
  simp [hpk_col_esI]

lemma hpk_eI_row_block (a : Fin r) (j : Fin (2 * r + k + 1)) (hj : r ≤ j.val) (hj' : j.val ≤ r + k) :
    Hpk k r (eI k r a) j = 0 := by
  have ha := a.isLt
  unfold Hpk
  simp only [eI, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

lemma hpk_eI_eI (a c : Fin r) : Hpk k r (eI k r a) (eI k r c) = 0 := by
  have ha := a.isLt
  have hc := c.isLt
  unfold Hpk
  simp only [eI, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

lemma one_mem_UWset (z : Fin (2 * r + k + 1) → ℂ) : (1 : B.Mat k r) ∈ UWset k r z := by
  refine ⟨?_, fun a => ⟨Matrix.one_mulVec _, Matrix.one_mulVec _⟩, Matrix.one_mulVec _⟩
  show (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ᴴ * Hpk k r * 1 = Hpk k r
  simp

theorem xuv_lieN (z : Fin (2 * r + k + 1) → ℂ) (a : Fin r) (v : Fin (2 * r + k + 1) → ℂ)
    (hv : ∀ b : Fin r, b.val ≤ a.val → v (esI k r b) = 0) :
    Xuv k r (bvec (eI k r a)) v ∈ lieOf (Sset k r z) := by
  intro t
  set X := Xuv k r (bvec (eI k r a)) v with hX
  have hXa : X *ᵥ bvec (eI k r a) = 0 := by
    rw [hX, xuv_mulVec, herm_eI_left, hv a le_rfl, herm_bvec_bvec, hpk_eI_eI]
    simp
  have hXc : ∀ c : Fin r, X *ᵥ bvec (eI k r c) = star (v (esI k r c)) • bvec (eI k r a) := by
    intro c
    rw [hX, xuv_mulVec, herm_eI_left, herm_bvec_bvec, hpk_eI_eI]
    simp
  have hXj : ∀ j : Fin (2 * r + k + 1), r ≤ j.val → j.val ≤ r + k →
      X *ᵥ bvec j = herm (Hpk k r) (bvec j) v • bvec (eI k r a) := by
    intro j hj hj'
    rw [hX, xuv_mulVec, herm_bvec_bvec, hpk_eI_row_block a j hj hj']
    simp
  refine ⟨1, one_mem_UWset z, NormedSpace.exp ((t : ℂ) • X), ⟨Formalism.FourierDecayAlt.P.B5.exp_mem (xuv_inLie _ _) t, ?_, ?_⟩,
    (Matrix.one_mul _).symm⟩
  · intro c i hci
    have e := exp_smul_mulVec_sq X (bvec (eI k r c)) (by rw [hXc, Matrix.mulVec_smul, hXa, smul_zero]) (t : ℂ)
    rw [show NormedSpace.exp ((t : ℂ) • X) i (eI k r c) = (NormedSpace.exp ((t : ℂ) • X) *ᵥ bvec (eI k r c)) i
      from mat_eq_mulVec_bvec _ _ _, e, hXc]
    have hz : star (v (esI k r c)) * bvec (eI k r a) i = 0 := by
      by_cases hca : c.val ≤ a.val
      · rw [hv c hca]; simp
      · have : i ≠ eI k r a := by
          intro h; rw [h] at hci; simp only [eI] at hci; omega
        simp [bvec, Pi.single_apply, this]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hz, mul_zero, add_zero]
    simp [bvec, Pi.single_apply]
  · intro i j hj hj' hi
    have e := exp_smul_mulVec_sq X (bvec j) (by rw [hXj j hj hj', Matrix.mulVec_smul, hXa, smul_zero]) (t : ℂ)
    rw [show NormedSpace.exp ((t : ℂ) • X) i j = (NormedSpace.exp ((t : ℂ) • X) *ᵥ bvec j) i
      from mat_eq_mulVec_bvec _ _ _, e, hXj j hj hj']
    have : i ≠ eI k r a := by
      intro h; rw [h] at hi; simp only [eI] at hi; omega
    simp [bvec, Pi.single_apply, this]

theorem xuv_lieW (z u v : Fin (2 * r + k + 1) → ℂ) (hu : inWb k r u) (hv : inWb k r v)
    (huz : herm (Hpk k r) u z = 0) (hvz : herm (Hpk k r) v z = 0) :
    Xuv k r u v ∈ lieOf (UWset k r z) := by
  intro t
  set X := Xuv k r u v with hX
  have hes : ∀ (w : Fin (2 * r + k + 1) → ℂ), inWb k r w → ∀ c : Fin r, w (esI k r c) = 0 := by
    intro w hw c; exact hw _ (Or.inr (by simp only [esI]; omega))
  have hei : ∀ (w : Fin (2 * r + k + 1) → ℂ), inWb k r w → ∀ c : Fin r, w (eI k r c) = 0 := by
    intro w hw c; exact hw _ (Or.inl (by simp only [eI]; omega))
  refine ⟨Formalism.FourierDecayAlt.P.B5.exp_mem (xuv_inLie _ _) t, fun c => ⟨?_, ?_⟩, ?_⟩
  · refine exp_smul_mulVec_fix X _ ?_ _
    rw [hX, xuv_mulVec, herm_eI_left, herm_eI_left, hes v hv, hes u hu]; simp
  · refine exp_smul_mulVec_fix X _ ?_ _
    rw [hX, xuv_mulVec, herm_esI_left, herm_esI_left, hei v hv, hei u hu]; simp
  · refine exp_smul_mulVec_fix X _ ?_ _
    rw [hX, xuv_mulVec, herm_conj z v, herm_conj z u, hvz, huz]; simp

end

end Formalism.FourierDecayAlt.P.CutMP.JfS.Sym
end

open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JfS.Sym

noncomputable section

variable {k r : ℕ}

theorem herm_zero_of_lieW {ζ : B.Mat k r} (hζ : B.inLie k r ζ) (z : Fin (2 * r + k + 1) → ℂ)
    (hW : ∀ X ∈ lieOf (UWset k r z), (Matrix.trace (ζ * X)).re = 0)
    (u v : Fin (2 * r + k + 1) → ℂ) (hu : inWb k r u) (hv : inWb k r v)
    (huz : herm (Hpk k r) u z = 0) (hvz : herm (Hpk k r) v z = 0) :
    herm (Hpk k r) (ζ *ᵥ u) v = 0 := by
  refine herm_zero_of_trace hζ u v (hW _ (xuv_lieW z u v hu hv huz hvz)) (hW _ ?_)
  refine xuv_lieW z u _ hu (inWb_smul _ hv) huz ?_
  rw [herm_smul_left, hvz, mul_zero]

end

end Formalism.FourierDecayAlt.P.CutMP.JfS.Sym

namespace Formalism.FourierDecayAlt.P.CutMP.JfS

end Formalism.FourierDecayAlt.P.CutMP.JfS
end

open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JfS.Sym

noncomputable section

variable {k r : ℕ}

def Flt (a : ℕ) (x : Fin (2 * r + k + 1) → ℂ) : Prop := ∀ i : Fin (2 * r + k + 1), a ≤ i.val → x i = 0

def hermL (y : Fin (2 * r + k + 1) → ℂ) : (Fin (2 * r + k + 1) → ℂ) →ₗ[ℂ] ℂ where
  toFun x := herm (Hpk k r) x y
  map_add' x x' := herm_add_left x x' y
  map_smul' c x := by simp [herm_smul_left]

theorem herm_sum_left {ι : Type*} (s : Finset ι) (f : ι → Fin (2 * r + k + 1) → ℂ) (y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (∑ j ∈ s, f j) y = ∑ j ∈ s, herm (Hpk k r) (f j) y :=
  map_sum (hermL y) f s

theorem herm_sum_right {ι : Type*} (s : Finset ι) (f : ι → Fin (2 * r + k + 1) → ℂ) (x : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) x (∑ j ∈ s, f j) = ∑ j ∈ s, herm (Hpk k r) x (f j) := by
  rw [herm_swap, herm_sum_left, star_sum]
  exact Finset.sum_congr rfl (fun j _ => by rw [← herm_swap])

theorem mulVec_sum' {ι : Type*} (s : Finset ι) (g : B.Mat k r) (f : ι → Fin (2 * r + k + 1) → ℂ) :
    g *ᵥ (∑ j ∈ s, f j) = ∑ j ∈ s, g *ᵥ f j :=
  map_sum (Matrix.mulVecLin g) f s

theorem flt_decomp (a : ℕ) (ha : a ≤ r) (y : Fin (2 * r + k + 1) → ℂ) (hy : Flt a y) :
    y = ∑ j : Fin a, y (eI k r ⟨j.val, by omega⟩) • bvec (eI k r ⟨j.val, by omega⟩) := by
  funext i
  rw [Finset.sum_apply]
  by_cases hi : i.val < a
  · rw [Finset.sum_eq_single ⟨i.val, hi⟩]
    · have : eI k r ⟨i.val, by omega⟩ = i := Fin.ext rfl
      simp [this, bvec]
    · intro j _ hj
      have : eI k r ⟨j.val, by omega⟩ ≠ i := by
        intro e; apply hj; apply Fin.ext; have := congrArg Fin.val e; simpa [eI] using this
      simp [bvec, Ne.symm this]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [hy i (by omega)]
    symm
    refine Finset.sum_eq_zero (fun j _ => ?_)
    have : eI k r ⟨j.val, by omega⟩ ≠ i := by
      intro e; have := congrArg Fin.val e; simp [eI] at this; omega
    simp [bvec, Ne.symm this]

def Mblk (g : B.Mat k r) (a : ℕ) (ha : a ≤ r) : Matrix (Fin a) (Fin a) ℂ := fun i j =>
  herm (Hpk k r) (g *ᵥ bvec (eI k r ⟨j.val, by omega⟩)) (bvec (eI k r ⟨i.val, by omega⟩))

theorem dmin_eq (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) (a : ℕ) (ha : a ≤ r) :
    Dmin k r z z' g ⟨a, by omega⟩ = (Mblk g a ha).det := by
  unfold Dmin
  congr 1
  ext i j
  simp only [Matrix.submatrix_apply, Zhat, fvec, Fin.val_castLE, Mblk]
  have hi : (i : ℕ) < a := i.isLt
  have hj : (j : ℕ) < a := j.isLt
  rw [dite_eq_left (show i.val < r by omega), dite_eq_left (show j.val < r by omega)]

theorem dlem_i (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) (a : ℕ) (ha : a ≤ r)
    (hD : Dmin k r z z' g ⟨a, by omega⟩ ≠ 0) (y : Fin (2 * r + k + 1) → ℂ) (hy : Flt a y)
    (h : ∀ c : Fin r, c.val < a → herm (Hpk k r) (g *ᵥ y) (bvec (eI k r c)) = 0) : y = 0 := by
  rw [dmin_eq z z' g a ha] at hD
  set y' : Fin a → ℂ := fun j => y (eI k r ⟨j.val, by omega⟩)
  have hMy : Mblk g a ha *ᵥ y' = 0 := by
    funext c
    have hc := h ⟨c.val, by omega⟩ c.isLt
    rw [flt_decomp a ha y hy, mulVec_sum', herm_sum_left] at hc
    simp only [mulVec_smul, herm_smul_left] at hc
    rw [Pi.zero_apply, ← hc]
    simp only [mulVec, dotProduct, Mblk, y']
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hy' : y' = 0 := Matrix.eq_zero_of_mulVec_eq_zero hD hMy
  rw [flt_decomp a ha y hy]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  have : y (eI k r ⟨j.val, by omega⟩) = 0 := congrFun hy' j
  rw [this, zero_smul]

theorem dlem_ii (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) (a : ℕ) (ha : a ≤ r)
    (hD : Dmin k r z z' g ⟨a, by omega⟩ ≠ 0) (y : Fin (2 * r + k + 1) → ℂ) (hy : Flt a y)
    (h : ∀ c : Fin r, c.val < a → herm (Hpk k r) y (g *ᵥ bvec (eI k r c)) = 0) : y = 0 := by
  rw [dmin_eq z z' g a ha] at hD
  set y' : Fin a → ℂ := fun j => y (eI k r ⟨j.val, by omega⟩)
  have hMy : star y' ᵥ* Mblk g a ha = 0 := by
    funext c
    have hc := h ⟨c.val, by omega⟩ c.isLt
    rw [herm_swap, star_eq_zero, flt_decomp a ha y hy, herm_sum_right] at hc
    simp only [herm_smul_right] at hc
    rw [Pi.zero_apply, ← hc]
    simp only [vecMul, dotProduct, Mblk, y', Pi.star_apply]
  have hy' : star y' = 0 := Matrix.eq_zero_of_vecMul_eq_zero hD hMy
  rw [flt_decomp a ha y hy]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  have : y (eI k r ⟨j.val, by omega⟩) = 0 := by
    have := congrFun hy' j
    simpa [y'] using this
  rw [this, zero_smul]

end

end Formalism.FourierDecayAlt.P.CutMP.JfS.Sym
