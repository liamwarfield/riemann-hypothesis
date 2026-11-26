module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.EnergyAbsMain
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.HaarDisintegrationRealHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.ConvGG

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.SecWGlob
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.SecWSec
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.SecWLoc
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.SecWFrame
noncomputable section

open Matrix
open scoped ComplexConjugate

namespace Formalism.L2.S.Pv.SecW

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj.InfCut Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.NH

variable {n r k : ℕ} (ε : Fin n → Bool)

def fr2L (e p : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (w : Fin k → Fin n → ℂ)
    (e' p' : Fin r → Fin n → ℂ) (z' : Fin n → ℂ) (w' : Fin k → Fin n → ℂ) (T : ℝ) :
    (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) where
  toFun v := syn e' p' z' w' T (fun a => hJ ε (p a) v) (fun a => hJ ε (e a) v) (hJ ε z v) (fun j => hJ ε (w j) v)
  map_add' v v' := by
    simp only [syn, UnitaryIsometries.hJ_add_right, add_smul, Finset.sum_add_distrib, neg_add, add_div]
    abel
  map_smul' c v := by
    simp only [syn, UnitaryIsometries.hJ_smul_right, RingHom.id_apply, smul_add, Finset.smul_sum, smul_smul]
    rw [show -(c * hJ ε z v) / (T : ℂ) = c * (-hJ ε z v / T) by ring]

def fr2M (e p : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (w : Fin k → Fin n → ℂ)
    (e' p' : Fin r → Fin n → ℂ) (z' : Fin n → ℂ) (w' : Fin k → Fin n → ℂ) (T : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toMatrix' (fr2L ε e p z w e' p' z' w' T)

variable {ε} {e p : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {w : Fin k → Fin n → ℂ}
  {e' p' : Fin r → Fin n → ℂ} {z' : Fin n → ℂ} {w' : Fin k → Fin n → ℂ} {T : ℝ}

theorem frameChangeMatrix_mulVec (v : Fin n → ℂ) :
    fr2M ε e p z w e' p' z' w' T *ᵥ v =
      syn e' p' z' w' T (fun a => hJ ε (p a) v) (fun a => hJ ε (e a) v) (hJ ε z v) (fun j => hJ ε (w j) v) := by
  unfold fr2M
  rw [LinearMap.toMatrix'_mulVec]
  rfl

theorem frameChangeMatrix_entry (i j : Fin n) :
    fr2M ε e p z w e' p' z' w' T i j =
      syn e' p' z' w' T (fun a => hJ ε (p a) (Pi.single j 1)) (fun a => hJ ε (e a) (Pi.single j 1))
        (hJ ε z (Pi.single j 1)) (fun l => hJ ε (w l) (Pi.single j 1)) i := by
  have h : fr2M ε e p z w e' p' z' w' T *ᵥ Pi.single j 1 = _ := frameChangeMatrix_mulVec _
  rw [Matrix.mulVec_single_one] at h
  exact congrFun h i

theorem frameChangeMatrix_isometry (F : Frm ε e p z w T) (F' : Frm ε e' p' z' w' T) (hdim : n = 2 * r + 1 + k) :
    UnitaryIsometries.IsIsom ε (fr2M ε e p z w e' p' z' w' T) := by
  intro x y
  rw [frameChangeMatrix_mulVec, frameChangeMatrix_mulVec, hJ_syn_syn F']
  conv_rhs => rw [recon F hdim x, recon F hdim y, hJ_syn_syn F]

theorem frameChangeMatrix_isotropic (F : Frm ε e p z w T) (b : Fin r) : fr2M ε e p z w e' p' z' w' T *ᵥ e b = e' b := by
  rw [frameChangeMatrix_mulVec]
  have h1 : (fun a => hJ ε (p a) (e b)) = fun a => if a = b then (1 : ℂ) else 0 := by
    funext a
    rw [UnitaryIsometries.hJ_conj, F.ep b a]
    by_cases hab : a = b
    · subst hab
      simp
    · simp [hab, Ne.symm hab]
  have h2 : (fun a => hJ ε (e a) (e b)) = fun _ => (0 : ℂ) := by
    funext a
    exact F.ee a b
  have h3 : hJ ε z (e b) = 0 := by rw [UnitaryIsometries.hJ_conj, F.ez b, map_zero]
  have h4 : (fun j => hJ ε (w j) (e b)) = fun _ => (0 : ℂ) := by
    funext j
    rw [UnitaryIsometries.hJ_conj, F.ew b j, map_zero]
  rw [h1, h2, h3, h4]
  simp [syn]

theorem fr2M_mulVec_z (F : Frm ε e p z w T) : fr2M ε e p z w e' p' z' w' T *ᵥ z = z' := by
  rw [frameChangeMatrix_mulVec]
  have h1 : (fun a => hJ ε (p a) z) = fun _ => (0 : ℂ) := by
    funext a
    exact F.pz a
  have h2 : (fun a => hJ ε (e a) z) = fun _ => (0 : ℂ) := by
    funext a
    exact F.ez a
  have h4 : (fun j => hJ ε (w j) z) = fun _ => (0 : ℂ) := by
    funext j
    rw [UnitaryIsometries.hJ_conj, F.zw j, map_zero]
  rw [h1, h2, F.zz, h4]
  have hT : (T : ℂ) ≠ 0 := by exact_mod_cast F.T_ne
  simp [syn, hT]

end Formalism.L2.S.Pv.SecW
end
end

noncomputable section

open Matrix
open scoped ComplexConjugate

namespace Formalism.L2.S.Pv.SecW

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj.InfCut Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.NH

variable {n r k : ℕ}

def sfv (sc : ℝ) (b : Fin r) : ℂ := ((sc : ℂ) ^ (r - b.1))⁻¹

def lamv (sc : ℝ) (c : Fin (r + 1) → ℂ) (b : Fin r) : ℂ := c (Fin.castSucc b) / (sfv sc b * sfv sc b)

def alv (T : ℝ) (c : Fin (r + 1) → ℂ) : ℂ := -c (Fin.last r) / (T : ℂ)

def bev (T T' : ℝ) (c : Fin (r + 1) → ℂ) : ℂ := ((Real.sqrt (‖c (Fin.last r)‖ ^ 2 / T - T') : ℝ) : ℂ)

def svv (T T' : ℝ) : ℂ := (((Real.sqrt (T * T'))⁻¹ : ℝ) : ℂ)

def e2 (sc : ℝ) (c : Fin (r + 1) → ℂ) (f : Fin r → Fin n → ℂ) : Fin r → Fin n → ℂ :=
  fun b => lamv sc c b • f b

def p2 (sc : ℝ) (c : Fin (r + 1) → ℂ) (e : Fin r → Fin n → ℂ) : Fin r → Fin n → ℂ :=
  fun b => (conj (lamv sc c b))⁻¹ • e b

def z2 (T T' : ℝ) (c : Fin (r + 1) → ℂ) (z : Fin n → ℂ) (w : Fin k → Fin n → ℂ) (i0 : Fin k) : Fin n → ℂ :=
  alv T c • z + bev T T' c • w i0

def w2 (T T' : ℝ) (c : Fin (r + 1) → ℂ) (z : Fin n → ℂ) (w : Fin k → Fin n → ℂ) (i0 : Fin k) :
    Fin k → Fin n → ℂ :=
  fun j => if j = i0 then svv T T' • (bev T T' c • z + (conj (alv T c) * (T : ℂ)) • w i0) else w j

section Facts

variable {sc T T' : ℝ} {c : Fin (r + 1) → ℂ}

theorem conj_sfv (sc : ℝ) (b : Fin r) : conj (sfv sc b) = sfv sc b := by
  simp only [sfv, map_inv₀, map_pow, Complex.conj_ofReal]

theorem sfv_ne (hsc : 0 < sc) (b : Fin r) : sfv sc b ≠ 0 :=
  inv_ne_zero (pow_ne_zero _ (by exact_mod_cast hsc.ne'))

theorem lamv_ne (hsc : 0 < sc) (hc : ∀ l, c l ≠ 0) (b : Fin r) : lamv sc c b ≠ 0 :=
  div_ne_zero (hc _) (mul_ne_zero (sfv_ne hsc b) (sfv_ne hsc b))

theorem conj_bev (T T' : ℝ) (c : Fin (r + 1) → ℂ) : conj (bev T T' c) = bev T T' c := Complex.conj_ofReal _

theorem bev_sq (hT : 0 < T) (hg : 0 < ‖c (Fin.last r)‖ ^ 2 - T * T') :
    conj (bev T T' c) * bev T T' c = ((‖c (Fin.last r)‖ ^ 2 / T - T' : ℝ) : ℂ) := by
  have hq0 : 0 ≤ ‖c (Fin.last r)‖ ^ 2 / T - T' := by
    rw [div_sub' hT.ne']
    exact div_nonneg (by nlinarith) hT.le
  rw [conj_bev, bev, ← Complex.ofReal_mul, Real.mul_self_sqrt hq0]

theorem alv_sq (T : ℝ) (c : Fin (r + 1) → ℂ) :
    conj (alv T c) * alv T c = ((‖c (Fin.last r)‖ ^ 2 / T ^ 2 : ℝ) : ℂ) := by
  rw [mul_comm, alv, map_div₀, map_neg, Complex.conj_ofReal, neg_div, neg_div, neg_mul_neg, div_mul_div_comm,
    Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

theorem svv_sq (hT : 0 < T) (hT' : 0 < T') : conj (svv T T') * svv T T' = ((1 / (T * T') : ℝ) : ℂ) := by
  rw [svv, Complex.conj_ofReal, ← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by positivity), one_div]

end Facts

section Frame

variable {ε : Fin n → Bool} {e f : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {w : Fin k → Fin n → ℂ}
  {sc T T' : ℝ} {c : Fin (r + 1) → ℂ}

theorem frm2 (F0 : Frm ε e f z w T) (hT : 0 < T) (hT' : 0 < T') (hsc : 0 < sc) (hc : ∀ l, c l ≠ 0)
    (hg : 0 < ‖c (Fin.last r)‖ ^ 2 - T * T') (i0 : Fin k) :
    Frm ε (e2 sc c f) (p2 sc c e) (z2 T T' c z w i0) (w2 T T' c z w i0) T' := by
  have hfe : ∀ a b, hJ ε (f a) (e b) = if a = b then 1 else 0 := by
    intro a b
    rw [hJ_swapδ F0.ep b a]
    by_cases h : a = b
    · subst h; simp
    · simp [h, Ne.symm h]
  have hwz : ∀ j, hJ ε (w j) z = 0 := fun j => hJ_swap0 (F0.zw j)
  have hTc : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  have hT'c : (T' : ℂ) ≠ 0 := by exact_mod_cast hT'.ne'
  have hlam := lamv_ne hsc hc
  have hcb := conj_bev T T' c
  have hβ := bev_sq (T' := T') hT hg
  rw [hcb] at hβ
  have hα := alv_sq T c
  have hs := svv_sq hT hT'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hT'.ne'⟩
  · intro a b
    simp only [e2, UnitaryIsometries.hJ_smul_left, UnitaryIsometries.hJ_smul_right, F0.pp, mul_zero]
  · intro a b
    simp only [e2, p2, UnitaryIsometries.hJ_smul_left, UnitaryIsometries.hJ_smul_right, hfe]
    split_ifs with h
    · subst h
      rw [mul_one, inv_mul_cancel₀ ((map_ne_zero _).2 (hlam a))]
    · simp
  · intro a b
    simp only [p2, UnitaryIsometries.hJ_smul_left, UnitaryIsometries.hJ_smul_right, F0.ee, mul_zero]
  · intro a
    simp only [e2, z2, UnitaryIsometries.hJ_smul_left, UnitaryIsometries.hJ_add_right, UnitaryIsometries.hJ_smul_right, F0.pz, F0.pw, mul_zero,
      add_zero]
  · intro a
    simp only [p2, z2, UnitaryIsometries.hJ_smul_left, UnitaryIsometries.hJ_add_right, UnitaryIsometries.hJ_smul_right, F0.ez, F0.ew, mul_zero,
      add_zero]
  · simp only [z2, UnitaryIsometries.hJ_add_left, UnitaryIsometries.hJ_add_right, UnitaryIsometries.hJ_smul_left, UnitaryIsometries.hJ_smul_right, F0.zz,
      F0.zw, hwz, F0.ww, if_true, mul_zero, add_zero, zero_add, mul_one, hcb]
    linear_combination (norm := skip) (-(T : ℂ)) * hα + hβ
    push_cast
    field_simp
    ring
  · intro a j
    by_cases hj : j = i0
    · simp only [e2, w2, if_pos hj, UnitaryIsometries.hJ_smul_left, UnitaryIsometries.hJ_smul_right, UnitaryIsometries.hJ_add_right, F0.pz, F0.pw,
        mul_zero, add_zero]
    · simp only [e2, w2, if_neg hj, UnitaryIsometries.hJ_smul_left, F0.pw, mul_zero]
  · intro a j
    by_cases hj : j = i0
    · simp only [p2, w2, if_pos hj, UnitaryIsometries.hJ_smul_left, UnitaryIsometries.hJ_smul_right, UnitaryIsometries.hJ_add_right, F0.ez, F0.ew,
        mul_zero, add_zero]
    · simp only [p2, w2, if_neg hj, UnitaryIsometries.hJ_smul_left, F0.ew, mul_zero]
  · intro j
    by_cases hj : j = i0
    · simp only [z2, w2, if_pos hj, UnitaryIsometries.hJ_smul_right, UnitaryIsometries.hJ_add_left, UnitaryIsometries.hJ_add_right,
        UnitaryIsometries.hJ_smul_left, F0.zz, F0.zw, hwz, F0.ww, if_true, mul_zero, add_zero, zero_add, mul_one, hcb]
      ring
    · have hne : i0 ≠ j := fun h => hj h.symm
      simp only [z2, w2, if_neg hj, UnitaryIsometries.hJ_add_left, UnitaryIsometries.hJ_smul_left, F0.zw, F0.ww, if_neg hne, mul_zero,
        add_zero]
  · intro i j
    by_cases hi : i = i0 <;> by_cases hj : j = i0
    · subst hi; subst hj
      simp only [w2, if_true, UnitaryIsometries.hJ_smul_right, UnitaryIsometries.hJ_add_left, UnitaryIsometries.hJ_add_right, UnitaryIsometries.hJ_smul_left,
        F0.zz, F0.zw, hwz, F0.ww, mul_zero, add_zero, zero_add, mul_one, hcb, map_mul, Complex.conj_conj,
        Complex.conj_ofReal]
      linear_combination (norm := skip) ((T : ℂ) ^ 2 * (conj (alv T c) * alv T c) - (T : ℂ) * (bev T T' c * bev T T' c)) * hs +
        (((1 / (T * T') : ℝ) : ℂ) * (T : ℂ) ^ 2) * hα - (((1 / (T * T') : ℝ) : ℂ) * (T : ℂ)) * hβ
      push_cast
      field_simp
      ring
    · subst hi
      have hne : i ≠ j := fun h => hj h.symm
      simp only [w2, if_true, if_neg hj, UnitaryIsometries.hJ_smul_left, UnitaryIsometries.hJ_add_left, F0.zw, F0.ww, if_neg hne,
        mul_zero, add_zero]
    · subst hj
      have hne : i ≠ j := hi
      simp only [w2, if_true, if_neg hi, UnitaryIsometries.hJ_smul_right, UnitaryIsometries.hJ_add_right, hwz, F0.ww, if_neg hne,
        mul_zero, add_zero]
    · simp only [w2, if_neg hi, if_neg hj]
      exact F0.ww i j

end Frame

end Formalism.L2.S.Pv.SecW
end
end

noncomputable section

open MeasureTheory Matrix
open scoped ComplexConjugate

namespace Formalism.L2.S.Pv.SecW

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.NH

variable {n r k : ℕ} {ε : Fin n → Bool} {e f : Fin r → Fin n → ℂ} {z z' : Fin n → ℂ}
  {w w' : Fin k → Fin n → ℂ} {sc T T' : ℝ}

def Mv (ε : Fin n → Bool) (e f : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ) (w w' : Fin k → Fin n → ℂ)
    (sc T T' : ℝ) (i0 : Fin k) (c : Fin (r + 1) → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fr2M ε e f z' w' (e2 sc c f) (p2 sc c e) (z2 T T' c z w i0) (w2 T T' c z w i0) T'

theorem famSc_castSucc (sc : ℝ) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (b : Fin r) :
    famSc sc e z (Fin.castSucc b) = sfv sc b • e b := by
  simp only [famSc, fam, Fin.snoc_castSucc, Fin.coe_castSucc, sfv]

theorem famSc_last (sc : ℝ) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) : famSc sc e z (Fin.last r) = z := by
  simp only [famSc, fam, Fin.snoc_last, Fin.val_last, Nat.sub_self, pow_zero, inv_one, one_smul]

theorem zhat_Mv (F0 : Frm ε e f z w T) (F1 : Frm ε e f z' w' T') (hsc : 0 < sc) {c : Fin (r + 1) → ℂ} (i0 : Fin k) :
    Zhat ε (famSc sc e z) (famSc sc e z') (Mv ε e f z z' w w' sc T T' i0 c) = Matrix.diagonal c := by
  have hMe : ∀ b, Mv ε e f z z' w w' sc T T' i0 c *ᵥ e b = e2 sc c f b := fun b => frameChangeMatrix_isotropic F1 b
  have hMz : Mv ε e f z z' w w' sc T T' i0 c *ᵥ z' = z2 T T' c z w i0 := fr2M_mulVec_z F1
  have hTc : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 F0.T_ne
  have hfe : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0 := F0.ep
  ext a b
  simp only [Zhat]
  induction a using Fin.lastCases with
  | last =>
    induction b using Fin.lastCases with
    | last =>
      rw [famSc_last, famSc_last, hMz]
      simp only [z2, UnitaryIsometries.hJ_add_right, UnitaryIsometries.hJ_smul_right, F0.zz, F0.zw, mul_zero, add_zero, diagonal_apply_eq,
        alv]
      field_simp
    | cast b =>
      rw [famSc_last, famSc_castSucc, mulVec_smul, hMe]
      simp only [e2, UnitaryIsometries.hJ_smul_right, hJ_swap0 (F0.pz b), mul_zero]
      rw [diagonal_apply_ne]
      exact fun h => (Fin.castSucc_lt_last b).ne h.symm
  | cast a =>
    induction b using Fin.lastCases with
    | last =>
      rw [famSc_castSucc, famSc_last, hMz]
      simp only [z2, UnitaryIsometries.hJ_smul_left, UnitaryIsometries.hJ_add_right, UnitaryIsometries.hJ_smul_right, F0.ez, F0.ew, mul_zero,
        add_zero]
      rw [diagonal_apply_ne]
      exact (Fin.castSucc_lt_last a).ne
    | cast b =>
      rw [famSc_castSucc, famSc_castSucc, mulVec_smul, hMe]
      simp only [e2, UnitaryIsometries.hJ_smul_left, UnitaryIsometries.hJ_smul_right, hfe, conj_sfv]
      by_cases h : a = b
      · subst h
        rw [diagonal_apply_eq, if_pos rfl, lamv]
        have hs : sfv sc a ≠ 0 := sfv_ne hsc a
        field_simp
      · rw [if_neg h, diagonal_apply_ne _ (fun h' => h (Fin.castSucc_injective _ h'))]
        ring

theorem measurable_Mv (i0 : Fin k) :
    Measurable (fun c : Fin (r + 1) → ℂ => Mv ε e f z z' w w' sc T T' i0 c) := by
  have hlam : ∀ a, Measurable (fun c : Fin (r + 1) → ℂ => lamv sc c a) := fun a =>
    (measurable_pi_apply _).div_const _
  have hinv : ∀ a, Measurable (fun c : Fin (r + 1) → ℂ => (conj (lamv sc c a))⁻¹) := fun a =>
    (Complex.continuous_conj.measurable.comp (hlam a)).inv
  have hal : Measurable (fun c : Fin (r + 1) → ℂ => alv T c) := (measurable_pi_apply _).neg.div_const _
  have hbe : Measurable (fun c : Fin (r + 1) → ℂ => bev T T' c) := by
    unfold bev
    exact Complex.measurable_ofReal.comp (Real.continuous_sqrt.measurable.comp
      ((((measurable_pi_apply _).norm.pow_const 2).div_const _).sub_const _))
  have hcal : Measurable (fun c : Fin (r + 1) → ℂ => conj (alv T c)) := Complex.continuous_conj.measurable.comp hal
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  simp only [Mv, frameChangeMatrix_entry, syn, Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  refine ((Finset.measurable_sum _ fun a _ => ?_).add (Finset.measurable_sum _ fun a _ => ?_)).add ?_ |>.add
    (Finset.measurable_sum _ fun l _ => ?_)
  · simp only [e2, Pi.smul_apply, smul_eq_mul]
    exact measurable_const.mul ((hlam a).mul measurable_const)
  · simp only [p2, Pi.smul_apply, smul_eq_mul]
    exact measurable_const.mul ((hinv a).mul measurable_const)
  · simp only [z2, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact measurable_const.mul ((hal.mul measurable_const).add (hbe.mul measurable_const))
  · simp only [w2]
    by_cases hl : l = i0
    · simp only [if_pos hl, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
      exact measurable_const.mul (measurable_const.mul ((hbe.mul measurable_const).add
        ((hcal.mul measurable_const).mul measurable_const)))
    · simp only [if_neg hl]
      exact measurable_const

instance matrix_borel (m : ℕ) : BorelSpace (Matrix (Fin m) (Fin m) ℂ) :=
  inferInstanceAs (BorelSpace (Fin m → Fin m → ℂ))

theorem measurableEmbedding_uMat (ε : Fin n → Bool) :
    MeasurableEmbedding (fun g : Formalism.REAL.UJ ε => Formalism.MainNotions.S.uMat g) :=
  (Formalism.REAL.isClosedEmbeddingMatrix n ε).1.measurableEmbedding

def secV (F0 : Frm ε e f z w T) (F1 : Frm ε e f z' w' T') (hdim : n = 2 * r + 1 + k) (hT : 0 < T) (hT' : 0 < T')
    (hsc : 0 < sc) (i0 : Fin k) (c : Fin (r + 1) → ℂ) : Formalism.REAL.UJ ε :=
  if h : (∀ l, c l ≠ 0) ∧ 0 < ‖c (Fin.last r)‖ ^ 2 - T * T' then
    UnitaryIsometries.toUJ ε (frameChangeMatrix_isometry F1 (frm2 (sc := sc) F0 hT hT' hsc h.1 h.2 i0) hdim)
  else 1

theorem uMat_secV (F0 : Frm ε e f z w T) (F1 : Frm ε e f z' w' T') (hdim : n = 2 * r + 1 + k) (hT : 0 < T)
    (hT' : 0 < T') (hsc : 0 < sc) (i0 : Fin k) (c : Fin (r + 1) → ℂ) :
    Formalism.MainNotions.S.uMat (secV F0 F1 hdim hT hT' hsc i0 c) =
      if (∀ l, c l ≠ 0) ∧ 0 < ‖c (Fin.last r)‖ ^ 2 - T * T' then Mv ε e f z z' w w' sc T T' i0 c else 1 := by
  unfold secV
  split_ifs with h
  · rfl
  · simp [Formalism.MainNotions.S.uMat]

theorem measurable_secV (F0 : Frm ε e f z w T) (F1 : Frm ε e f z' w' T') (hdim : n = 2 * r + 1 + k)
    (hT : 0 < T) (hT' : 0 < T') (hsc : 0 < sc) (i0 : Fin k) :
    Measurable (secV F0 F1 hdim hT hT' hsc i0) := by
  rw [← (measurableEmbedding_uMat ε).measurable_comp_iff]
  have he : (fun g : Formalism.REAL.UJ ε => Formalism.MainNotions.S.uMat g) ∘ secV F0 F1 hdim hT hT' hsc i0 =
      fun c => if (∀ l, c l ≠ 0) ∧ 0 < ‖c (Fin.last r)‖ ^ 2 - T * T' then Mv ε e f z z' w w' sc T T' i0 c
        else 1 := by
    funext c
    exact uMat_secV F0 F1 hdim hT hT' hsc i0 c
  rw [he]
  have hm1 : MeasurableSet {c : Fin (r + 1) → ℂ | ∀ l, c l ≠ 0} := by
    rw [Set.setOf_forall]
    exact MeasurableSet.iInter fun l => (measurableSet_singleton 0).compl.preimage (measurable_pi_apply l)
  have hm2 : MeasurableSet {c : Fin (r + 1) → ℂ | 0 < ‖c (Fin.last r)‖ ^ 2 - T * T'} :=
    measurableSet_lt measurable_const ((((measurable_pi_apply _).norm.pow_const 2)).sub_const _)
  have hm : MeasurableSet {c : Fin (r + 1) → ℂ | (∀ l, c l ≠ 0) ∧ 0 < ‖c (Fin.last r)‖ ^ 2 - T * T'} :=
    hm1.inter hm2
  exact Measurable.ite hm (measurable_Mv i0) measurable_const

theorem zhat_secV (F0 : Frm ε e f z w T) (F1 : Frm ε e f z' w' T') (hdim : n = 2 * r + 1 + k) (hT : 0 < T)
    (hT' : 0 < T') (hsc : 0 < sc) (i0 : Fin k) {c : Fin (r + 1) → ℂ} (hc : ∀ l, c l ≠ 0)
    (hg : 0 < ‖c (Fin.last r)‖ ^ 2 - T * T') :
    Zhat ε (famSc sc e z) (famSc sc e z') (Formalism.MainNotions.S.uMat (secV F0 F1 hdim hT hT' hsc i0 c)) =
      Matrix.diagonal c := by
  rw [uMat_secV, if_pos ⟨hc, hg⟩]
  exact zhat_Mv F0 F1 hsc i0

end Formalism.L2.S.Pv.SecW
end
end

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.S.Pv.SecW

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem stepSection_holds : Formalism.L2.SG.RealObj.EnergyInst.StepSection := by
  intro D X u u' sc hsc
  have hk : 0 < D.R.k := by have := D.R.m_add_three_le_k; omega
  let i0 : Fin D.R.k := ⟨0, hk⟩
  choose w Fw using fun v => Formalism.L2.S.Pv.HaarSubS.frm_at X u v
  choose w' Fw' using fun v => Formalism.L2.S.Pv.HaarSubS.frm_at X u' v
  have hdim : ∀ v, X.B.I.n = 2 * D.R.rS + 1 + D.R.k := fun v => (ProductExactness.frameLoc_X X u u v).dim
  have hT : 0 < Tw (D := D) u := ProductExactness.Tw_pos u
  have hT' : 0 < Tw (D := D) u' := ProductExactness.Tw_pos u'
  refine ⟨fun c v => secV (Fw v) (Fw' v) (hdim v) hT hT' hsc i0 (c v), ?_, ?_⟩
  · exact Measurable.of_eval fun v => (measurable_secV (Fw v) (Fw' v) (hdim v) hT hT' hsc i0).comp
      (measurable_pi_apply v)
  · intro c hc v
    have hcv := hc v
    have hg := ProductExactness.normSq_last_sub_pos_of_Gv_diagonal_pos (Tw (D := D) u) (Tw (D := D) u') (c v) hcv.2
    exact zhat_secV (Fw v) (Fw' v) (hdim v) hT hT' hsc i0 hcv.1 hg

end Formalism.L2.S.Pv.SecW
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyAt
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace Formalism.L2.SG.RealObj.EnergyInst

open Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.EnergyAbs

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def StepIntAt (D : D7) : Prop :=
  ∀ (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (sc : ℝ), 0 < sc →
    ∀ c ∈ Good X u u', ∀ γ, HasDiag X u u' sc c γ →
      TermOp.OOInt (Formalism.L2.SG.ProjRows.muInf X.B.I) Set.univ (X.Wu u) (X.Wu u') γ

def StepConvAt (D : D7) : Prop :=
  ∀ (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (sc : ℝ), 0 < sc →
    (∀ c ∈ Good X u u', ∀ γ, HasDiag X u u' sc c γ →
      ∫⁻ z, ∫⁻ z', ∫⁻ s, ∫⁻ s', ‖⟪X.B.σs z (X.B.tens X.B.w),
          X.B.σs (s * γ * s'⁻¹) (X.B.σs z' (X.B.tens X.B.w))⟫_ℂ‖ₑ * ‖X.Wu u z‖ₑ * ‖X.Wu u' z'‖ₑ
        ∂(muS X u') ∂(muS X u) ∂(X.nuQ u') ∂(X.nuQ u) < ⊤) ∧
    ∀ w : D.what₂.Word,
      ∫⁻ z, ∫⁻ z', ∫⁻ s, ‖⟪X.B.σs z (X.B.tens X.B.w), X.B.σs s (X.B.σs z' (X.B.tens X.B.w))⟫_ℂ‖ₑ *
        ‖X.Wu w z‖ₑ * ‖X.Wu w z'‖ₑ ∂(muS X w) ∂(X.nuQ w) ∂(X.nuQ w) < ⊤

def StepEnergyAt (D : D7) : Prop :=
  ∀ (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (sc : ℝ), 0 < sc →
    DisintegrationConstantPositive X u u' sc → CoordOK X u u' sc → intOOe X u u' sc ≤ ENNReal.ofReal (1 / degX X)

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem stepEnergyAt_of_inst (D : D7) (hE : EnergyAbs) (hS : StepSchurG) (hG : StepSubG) (hSec : StepSection)
    (hC : StepConvAt D) (hI : StepIntAt D) : StepEnergyAt D := by
  classical
  intro X u u' sc hsc h27 _
  obtain ⟨hUR, hSch, hw, -⟩ := hS D X
  obtain ⟨hHu, hFu, -, -, hSFu⟩ := hG D X u
  obtain ⟨hHu', hFu', -, -, hSFu'⟩ := hG D X u'
  obtain ⟨hh, hhm, hhd⟩ := hSec D X u u' sc hsc
  have hGood : MeasurableSet (Good X u u') := by
    rw [Formalism.L2.SG.RealObj.EnergyCut.good_eq_pi X u u']
    exact MeasurableSet.univ_pi fun _ => Formalism.L2.SG.RealObj.EnergyCut.goodV_meas u u'
  by_cases hne : (Good X u u').Nonempty
  swap
  · have h0 : Good X u u' = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    simp [intOOe, nuM, h0]
  obtain ⟨c₀, hc₀⟩ := hne
  let g : Cinf X → X.B.I.Ginf := (Good X u u').piecewise hh (fun _ => hh c₀)
  have hgm : Measurable g := Measurable.piecewise hGood hhm measurable_const
  have hgG : ∀ c ∈ Good X u u', g c = hh c := fun c hc => Set.piecewise_eq_of_mem _ _ _ hc
  have hgd : ∀ c, ∃ c' ∈ Good X u u', HasDiag X u u' sc c' (g c) := by
    intro c
    by_cases hc : c ∈ Good X u u'
    · exact ⟨c, hc, by rw [hgG c hc]; exact hhd c hc⟩
    · refine ⟨c₀, hc₀, ?_⟩
      have : g c = hh c₀ := Set.piecewise_eq_of_notMem _ _ _ hc
      rw [this]; exact hhd c₀ hc₀
  have hgD : ∀ c ∈ Good X u u', HasDiag X u u' sc c (g c) := fun c hc => by
    rw [hgG c hc]; exact hhd c hc
  have hOfD : ∀ c ∈ Good X u u', HasDiag X u u' sc c (hOf X u u' sc c) := by
    intro c hc
    have hex : ∃ γ, HasDiag X u u' sc c γ := ⟨hh c, hhd c hc⟩
    have e : hOf X u u' sc c = hex.choose := dif_pos hex
    rw [e]
    exact hex.choose_spec
  have hD : Disint X u u' sc (DisintegrationConstant X u u' sc) := by
    have e : DisintegrationConstant X u u' sc = h27.choose := dif_pos h27
    rw [e]
    exact h27.choose_spec.2
  have hm : Measurable fun c => ENNReal.ofReal (DisintegrationConstant X u u' sc * wt X u u' c) :=
    ENNReal.measurable_ofReal.comp ((Formalism.L2.SG.RealObj.InfCut.wt_cont X u u').measurable.const_mul _)
  have hDis : Formalism.L2.SG.Pf.EnergyAbs.IsDisint (Formalism.L2.SG.ProjRows.muInf X.B.I) (muS X u) (muS X u')
      (nuM X u u' sc) g := by
    intro φ hφ
    rw [hD φ hφ, nuM, lintegral_withDensity_eq_lintegral_mul_non_measurable _ hm
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine lintegral_congr_ae (ae_restrict_of_forall_mem hGood fun c hc => ?_)
    simp only [Pi.mul_apply]
    congr 1
    obtain ⟨a, ha, b, hb, hab⟩ :=
      InfCut.UnitaryIsometries.StepDiagDC_holds D X u u' sc c hc _ _ (hOfD c hc) (hgD c hc)
    exact (inner_transfer X hG u u' φ hφ _ _ a ha b hb hab).symm
  have key := hE X.B.I.Ginf (Formalism.L2.SG.ProjRows.muInf X.B.I) _ X.B.σs (degX X) (X.B.tens X.B.w)
    (X.Vpi u) (X.Vpi u') (X.SinfU u) (X.SinfU u') (muS X u) (muS X u') (X.nuQ u) (X.nuQ u')
    (tauU X u) (tauU X u') (X.Wu u) (X.Wu u') (Cinf X) inferInstance (nuM X u u' sc) g
    hUR hSch hw hHu hHu' hFu hFu' hSFu hSFu' (fun f hf => X.nuQ_weil u f hf)
    (fun f hf => X.nuQ_weil u' f hf) (isWAbs_of X hS hG u) (isWAbs_of X hS hG u') hDis hgm
    (fun c => by
      obtain ⟨c', hc', hd⟩ := hgd c
      exact integrableOn_univ.mp (hI X u u' sc hsc c' hc' (g c) hd))
    (fun c => by
      obtain ⟨c', hc', hd⟩ := hgd c
      exact (hC X u u' sc hsc).1 c' hc' (g c) hd)
    ((hC X u u' sc hsc).2 u) ((hC X u u' sc hsc).2 u')
  refine le_trans (le_of_eq ?_) key
  have hae : ∀ᵐ c ∂(nuM X u u' sc), c ∈ Good X u u' := by
    rw [nuM]
    exact withDensity_absolutelyContinuous _ _ (ae_restrict_mem hGood)
  have hIndep : OOIndep X u u' sc := InfCut.ooIndep_of_step X InfCut.UnitaryIsometries.StepDiagDC_holds u u' sc
  unfold intOOe
  refine lintegral_congr_ae ?_
  filter_upwards [hae] with c hc
  rw [hilbertSchmidtSqGram, hIndep c hc _ _ (hOfD c hc) (hgD c hc)]
  simp only [OOinf, TermOp.OO, Measure.restrict_univ]
  rfl

theorem inInfinityXAt (hI : StepIntAt D) (hC : StepConvAt D) (u u' : D.what₂.Word) (sc : ℝ) (hsc : 0 < sc) :
    InInfinityX X u u' sc := by
  have h27 : DisintegrationConstantPositive X u u' sc := InfCut.ProductExactness.haar_disintegration_real_holds D X u u' sc hsc
  have hR := InfCut.ProductExactness.StepReal_holds D X u u' sc hsc
  have hco : CoordOK X u u' sc := by
    refine ⟨hR, fun c hc => ?_⟩
    have hex := hR c hc
    refine hI X u u' sc hsc c hc _ ?_
    have e : hOf X u u' sc c = hex.choose := dif_pos hex
    rw [e]
    exact hex.choose_spec
  exact ⟨h27, hco, stepEnergyAt_of_inst D S.Pv.EnergyAbs.energyAbs_holds S.Pv.SchurTens.stepSchurG_holds
    S.Pv.HaarSubS.stepSubG_holds S.Pv.SecW.stepSection_holds hC hI X u u' sc hsc h27 hco⟩

end Formalism.L2.SG.RealObj.EnergyInst
end
end

open Formalism.BasicNotions Formalism.L2.SG.RealObj

namespace Formalism.L2.SG.Pf

theorem realObj_inInfinityX_ofG (hI : Formalism.L2.SG.RealObj.EnergyInt.StepIntG) (hC : Formalism.L2.S.Pv.ConvG.StepConvG)
    {D : D7}
    (hg : Formalism.L2.SG.ConcreteSettingExists.GapHyp D) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (sc : ℝ)
    (hsc : 0 < sc) : InInfinityX X u u' sc := Formalism.L2.SG.RealObj.EnergyInst.inInfinityXAt (X := X) (hI D hg) (hC D hg) u u' sc hsc

end Formalism.L2.SG.Pf
