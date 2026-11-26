module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GenFin
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DHol
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ActsAwayNbar
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.WopTop
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussClosed
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.AwayFactPf
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilThetaConvergence.WeilThetaConvergenceOfSiegelSet

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchwartzBilinear.PowMulExpLeHalfExp
namespace UpperTheory.Reformulated.B.P6.r23b

theorem pow_mul_exp_le_half_exp (N : ℕ) (a : ℝ) (ha : 0 < a) :
    ∃ (C : ℝ), 0 ≤ C ∧ ∀ (x : ℝ), 0 ≤ x →
      (1 + x) ^ N * Real.exp (-(a * x)) ≤ C * Real.exp (-(a / 2 * x)) := by
  refine ⟨(2 / a) ^ N * (N.factorial : ℝ) * Real.exp (a / 2), by positivity, ?_⟩
  intro x hx
  have hy : 0 ≤ a / 2 * (1 + x) := by positivity
  have h1 : (a / 2 * (1 + x)) ^ N / (N.factorial : ℝ) ≤ Real.exp (a / 2 * (1 + x)) := Real.pow_div_factorial_le_exp (x := a / 2 * (1 + x)) (n := N) hy
  have hf : (0 : ℝ) < (N.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos N
  have h1' : (a / 2 * (1 + x)) ^ N ≤ Real.exp (a / 2 * (1 + x)) * (N.factorial : ℝ) :=
    (div_le_iff₀ hf).mp h1
  have h2 : (1 + x) ^ N = (2 / a) ^ N * (a / 2 * (1 + x)) ^ N := by
    rw [← mul_pow]
    congr 1
    field_simp
  have hp : (0 : ℝ) ≤ (2 / a) ^ N := by positivity
  have h3 : (1 + x) ^ N ≤ (2 / a) ^ N * (N.factorial : ℝ) * Real.exp (a / 2 * (1 + x)) := by
    rw [h2]
    have := mul_le_mul_of_nonneg_left h1' hp
    linarith [this]
  have h4 : Real.exp (a / 2 * (1 + x)) * Real.exp (-(a * x)) =
      Real.exp (a / 2) * Real.exp (-(a / 2 * x)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc (1 + x) ^ N * Real.exp (-(a * x))
      ≤ ((2 / a) ^ N * (N.factorial : ℝ) * Real.exp (a / 2 * (1 + x))) * Real.exp (-(a * x)) :=
        mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
    _ = (2 / a) ^ N * (N.factorial : ℝ) * (Real.exp (a / 2 * (1 + x)) * Real.exp (-(a * x))) := by ring
    _ = (2 / a) ^ N * (N.factorial : ℝ) * Real.exp (a / 2) * Real.exp (-(a / 2 * x)) := by
        rw [h4]; ring

theorem PositivityTheory.Rg.Sw.Glob.DCalcDH.poly_exp :
    ∀ (N : ℕ) (a : ℝ), OfNat.ofNat (nat_lit 0) < a → ∃ (C : ℝ), OfNat.ofNat (nat_lit 0) ≤ C ∧ ∀ (x : ℝ), OfNat.ofNat (nat_lit 0) ≤ x → (OfNat.ofNat (nat_lit 1) + x) ^ N * Real.exp (-(a * x)) ≤ C * Real.exp (-(a / OfNat.ofNat (nat_lit 2) * x)) := by
  intro N a ha
  exact pow_mul_exp_le_half_exp N a ha

end UpperTheory.Reformulated.B.P6.r23b
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.IteratedDerivMulConst
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DCalc
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.HasDeriv
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DCalcE
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DCalcD
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DCalcC
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DCalcB
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DCalcA
noncomputable section

open Matrix MvPolynomial

namespace PositivityTheory.Rg.Sw.Glob

namespace DCalcH

variable {m n : ℕ}

def vS (u : Fin m → Fin n → ℂ) (X : Fin n → ℝ) (s : ℝ) : Fin m → Fin n → ℂ :=
  fun a j => u a j * (Real.exp (s * X j) : ℂ)

def crd (v : Fin m → Fin n → ℂ) (k : Fin m × Fin n × Bool) : ℂ := if k.2.2 then star (v k.1 k.2.1) else v k.1 k.2.1

theorem evX_eq (P : PX m n) (v : Fin m → Fin n → ℂ) : evX P v = MvPolynomial.eval (crd v) P := rfl

theorem crd_vS (u : Fin m → Fin n → ℂ) (X : Fin n → ℝ) (k : Fin m × Fin n × Bool) (s : ℝ) :
    crd (vS u X s) k = crd u k * ((Real.exp (s * X k.2.1) : ℝ) : ℂ) := by
  unfold crd vS
  split_ifs
  · rw [star_mul', Complex.star_def, Complex.conj_ofReal]
  · rfl

theorem hasDerivAt_expX (x s : ℝ) :
    HasDerivAt (fun s : ℝ => ((Real.exp (s * x) : ℝ) : ℂ)) ((x : ℂ) * ((Real.exp (s * x) : ℝ) : ℂ)) s := by
  have h := ((hasDerivAt_id s).mul_const x).exp
  simp only [id, one_mul] at h
  have h2 := h.ofReal_comp
  have e : ((x : ℂ) * ((Real.exp (s * x) : ℝ) : ℂ)) = ((Real.exp (s * x) * x : ℝ) : ℂ) := by push_cast; ring
  rw [e]
  exact h2

theorem crd_hasDeriv (u : Fin m → Fin n → ℂ) (X : Fin n → ℝ) (k : Fin m × Fin n × Bool) (s : ℝ) :
    HasDerivAt (fun s : ℝ => crd (vS u X s) k) ((X k.2.1 : ℂ) * crd (vS u X s) k) s := by
  have h := (hasDerivAt_expX (X k.2.1) s).const_mul (crd u k)
  have e1 : (fun s : ℝ => crd (vS u X s) k) = fun s => crd u k * ((Real.exp (s * X k.2.1) : ℝ) : ℂ) :=
    funext fun s => crd_vS u X k s
  rw [e1, crd_vS]
  exact h.congr_deriv (by ring)

theorem pderiv_mul_X (p : PX m n) (k i : Fin m × Fin n × Bool) :
    pderiv i (p * MvPolynomial.X k) = pderiv i p * MvPolynomial.X k + if i = k then p else 0 := by
  rw [Derivation.leibniz, pderiv_X, smul_eq_mul, smul_eq_mul]
  by_cases h : i = k
  · subst h; simp [add_comm, mul_comm]
  · simp [h, Ne.symm h, mul_comm]

theorem eval_hasDeriv (P : PX m n) (u : Fin m → Fin n → ℂ) (X : Fin n → ℝ) (s : ℝ) :
    HasDerivAt (fun s : ℝ => evX P (vS u X s))
      (∑ k, evX (pderiv k P) (vS u X s) * ((X k.2.1 : ℂ) * crd (vS u X s) k)) s := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    simp only [evX_eq, eval_C, pderiv_C, map_zero, zero_mul, Finset.sum_const_zero]
    exact hasDerivAt_const _ _
  | add p q hp hq =>
    simp only [evX_eq, map_add (f := _), add_mul, Finset.sum_add_distrib] at *
    exact hp.add hq
  | mul_X p k hp =>
    have h := hp.mul (crd_hasDeriv u X k s)
    simp only [evX_eq] at *
    have efun : (fun s : ℝ => eval (crd (vS u X s)) (p * MvPolynomial.X k)) =
        fun s => eval (crd (vS u X s)) p * crd (vS u X s) k := by
      funext s'; simp [eval_mul, eval_X]
    rw [efun]
    refine h.congr_deriv ?_
    symm
    set D : Fin m × Fin n × Bool → ℂ := fun i => (X i.2.1 : ℂ) * crd (vS u X s) i with hD
    calc (∑ i, eval (crd (vS u X s)) (pderiv i (p * MvPolynomial.X k)) * D i)
        = ∑ i, (eval (crd (vS u X s)) (pderiv i p) * D i * crd (vS u X s) k +
            (if i = k then eval (crd (vS u X s)) p * D i else 0)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [pderiv_mul_X]
          split_ifs with hik
          · simp [eval_mul, eval_X]; ring
          · simp [eval_mul, eval_X]; ring
      _ = (∑ i, eval (crd (vS u X s)) (pderiv i p) * D i) * crd (vS u X s) k + eval (crd (vS u X s)) p * D k := by
          rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_ite_eq']
          simp

theorem crd_false (v : Fin m → Fin n → ℂ) (a : Fin m) (j : Fin n) : crd v (a, j, false) = v a j := rfl

theorem crd_true (v : Fin m → Fin n → ℂ) (a : Fin m) (j : Fin n) : crd v (a, j, true) = star (v a j) := rfl

theorem evX_dil (c : ℝ) (X : Fin n → ℝ) (P : PX m n) (v : Fin m → Fin n → ℂ) :
    evX (dil c X P) v = ((m : ℂ) * ∑ j, (X j : ℂ)) * evX P v +
      ∑ k, evX (pderiv k P) v * ((X k.2.1 : ℂ) * crd v k) -
      (2 * c : ℂ) * (∑ a, ∑ j, (X j : ℂ) * ((‖v a j‖ ^ 2 : ℝ) : ℂ)) * evX P v := by
  have hnorm : ∀ a j, ((‖v a j‖ ^ 2 : ℝ) : ℂ) = v a j * star (v a j) := by
    intro a j
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dil, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.add_apply,
    LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.id_apply,
    Derivation.coeFn_coe, evX_eq, map_sum, map_add, map_sub, map_mul, MvPolynomial.smul_eval, eval_X, smul_eq_mul]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, crd_false, crd_true, hnorm]
  set E := (eval (crd v)) P with hE
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin m))) (t := (Finset.univ : Finset (Fin n)))
      (f := fun a j => (eval (crd v)) ((pderiv (a, j, true)) P) * ((X j : ℂ) * star (v a j)) +
        (eval (crd v)) ((pderiv (a, j, false)) P) * ((X j : ℂ) * v a j)),
    Finset.sum_comm (s := (Finset.univ : Finset (Fin m))) (t := (Finset.univ : Finset (Fin n)))
      (f := fun a j => (X j : ℂ) * (v a j * star (v a j)))]
  rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_add, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, add_sub_assoc, ← Finset.sum_sub_distrib]
  congr 1
  · ring
  · refine Finset.sum_congr rfl fun a _ => ?_
    ring

end DCalcH

end PositivityTheory.Rg.Sw.Glob
end
end

noncomputable section

open Matrix MvPolynomial

namespace PositivityTheory.Rg.Sw.Glob

namespace DCalcBH

open DCalcH

variable {m n : ℕ}

theorem norm_vS (u : Fin m → Fin n → ℂ) (X : Fin n → ℝ) (s : ℝ) (a : Fin m) (j : Fin n) :
    ‖vS u X s a j‖ ^ 2 = ‖u a j‖ ^ 2 * Real.exp (s * X j) ^ 2 := by
  simp only [DCalcH.vS, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

def nS (u : Fin m → Fin n → ℂ) (X : Fin n → ℝ) (s : ℝ) : ℝ := ∑ a, ∑ j, ‖u a j‖ ^ 2 * Real.exp (s * X j) ^ 2

theorem gs_vS (c : ℝ) (u : Fin m → Fin n → ℂ) (X : Fin n → ℝ) (s : ℝ) :
    gs c (vS u X s) = Complex.exp (((-(c * nS u X s)) : ℝ) : ℂ) := by
  simp only [gs, nS, norm_vS, Complex.ofReal_neg]

theorem nS_hasDeriv (u : Fin m → Fin n → ℂ) (X : Fin n → ℝ) (s : ℝ) :
    HasDerivAt (nS u X) (∑ a, ∑ j, 2 * X j * ‖vS u X s a j‖ ^ 2) s := by
  have h : ∀ a j, HasDerivAt (fun s => ‖u a j‖ ^ 2 * Real.exp (s * X j) ^ 2)
      (2 * X j * ‖vS u X s a j‖ ^ 2) s := by
    intro a j
    rw [norm_vS]
    have h1 : HasDerivAt (fun s : ℝ => s * X j) (X j) s := by
      simpa using (hasDerivAt_id s).mul_const (X j)
    refine (((h1.exp).pow 2).const_mul (‖u a j‖ ^ 2)).congr_deriv ?_
    rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    push_cast
    ring
  have h3 := HasDerivAt.sum (u := Finset.univ) fun a _ => HasDerivAt.sum (u := Finset.univ) fun j _ => h a j
  have e : nS u X = ∑ a, ∑ j, fun s : ℝ => ‖u a j‖ ^ 2 * Real.exp (s * X j) ^ 2 := by
    ext y
    simp [nS, Finset.sum_apply]
  rw [e]
  exact h3

theorem gs_hasDeriv (c : ℝ) (u : Fin m → Fin n → ℂ) (X : Fin n → ℝ) (s : ℝ) :
    HasDerivAt (fun s : ℝ => gs c (vS u X s))
      (gs c (vS u X s) * (-(2 * c : ℂ) * ∑ a, ∑ j, (X j : ℂ) * ((‖vS u X s a j‖ ^ 2 : ℝ) : ℂ))) s := by
  simp_rw [gs_vS]
  have h := ((nS_hasDeriv u X s).const_mul c).neg.ofReal_comp.cexp
  refine h.congr_deriv ?_
  congr 1
  push_cast
  rw [neg_mul]
  congr 1
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

def fF (c : ℝ) (X : Fin n → ℝ) (P : PX m n) (u : Fin m → Fin n → ℂ) (s : ℝ) : ℂ :=
  ((Real.exp (s * (m : ℝ) * ∑ j, X j) : ℝ) : ℂ) * fP c P (vS u X s)

theorem fF_hasDeriv (c : ℝ) (X : Fin n → ℝ) (P : PX m n) (u : Fin m → Fin n → ℂ) (s : ℝ) :
    HasDerivAt (fF c X P u) (fF c X (dil c X P) u s) s := by
  have he : HasDerivAt (fun s : ℝ => ((Real.exp (s * (m : ℝ) * ∑ j, X j) : ℝ) : ℂ))
      ((((m : ℝ) * ∑ j, X j : ℝ) : ℂ) * ((Real.exp (s * (m : ℝ) * ∑ j, X j) : ℝ) : ℂ)) s := by
    have := hasDerivAt_expX ((m : ℝ) * ∑ j, X j) s
    simp only [mul_assoc] at this ⊢
    exact this
  have h := he.mul ((eval_hasDeriv P u X s).mul (gs_hasDeriv c u X s))
  unfold fF fP
  have efun : (fun s : ℝ => ((Real.exp (s * (m : ℝ) * ∑ j, X j) : ℝ) : ℂ) * (evX P (vS u X s) * gs c (vS u X s))) =
      fun s => ((Real.exp (s * (m : ℝ) * ∑ j, X j) : ℝ) : ℂ) * (evX P (vS u X s) * gs c (vS u X s)) := rfl
  refine h.congr_deriv ?_
  simp only [Pi.mul_apply]
  rw [evX_dil]
  push_cast
  ring

theorem fF_iter (c : ℝ) (X : Fin n → ℝ) (u : Fin m → Fin n → ℂ) (r : ℕ) :
    iteratedDeriv r (fF c X 1 u) = fF c X ((dil c X ^ r) 1) u := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [iteratedDeriv_succ, ih]
    funext s
    rw [(fF_hasDeriv c X ((dil c X ^ r) 1) u s).deriv, pow_succ', Module.End.mul_apply]

end DCalcBH

end PositivityTheory.Rg.Sw.Glob
end
end

noncomputable section

open Matrix MvPolynomial

namespace PositivityTheory.Rg.Sw.Glob

namespace DCalcCH

open DCalcH DCalcBH

variable {m n : ℕ}

theorem mR_one : mR (1 : GR n) = 1 := rfl

theorem cnt_add (ε : Fin m → Bool) : cnt ε true + cnt ε false = m := by
  unfold cnt
  rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
  have h : ∀ a : Fin m, ((if ε a = true then 1 else 0) + (if ε a = false then 1 else 0) : ℕ) = 1 := by
    intro a; cases ε a <;> simp
  simp [h]

theorem det_diag_exp (X : Fin n → ℝ) (z : ℂ) :
    (diagonal fun j => Complex.exp (-(z * X j))).det = Complex.exp (-(z * ∑ j, (X j : ℂ))) := by
  rw [det_diagonal, ← Complex.exp_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]

theorem det_aC (X : Fin n → ℝ) (z : ℂ) : (aC X z).det = 1 := by
  unfold aC
  rw [det_fromBlocks_zero₂₁, det_diagonal, det_diagonal, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun j _ => ?_
  rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]

theorem zpow_exp_neg (w : ℂ) (p : ℕ) : Complex.exp (-w) ^ (-(p : ℤ)) = Complex.exp ((p : ℂ) * w) := by
  rw [← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

theorem jC_one (e : ℤ) (p q : ℕ) (X : Fin n → ℝ) (z : ℂ) :
    jC e p q 1 X z = Complex.exp (((p : ℂ) + q) * (z * ∑ j, (X j : ℂ))) := by
  unfold jC
  simp only [mR_one, Matrix.one_mul]
  rw [det_aC]
  unfold aC
  simp only [toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, Matrix.zero_mul, zero_add, _root_.one_zpow, one_mul]
  rw [det_diag_exp, zpow_exp_neg, zpow_exp_neg, ← Complex.exp_add]
  congr 1
  ring

theorem inv_diag_exp (X : Fin n → ℝ) (z : ℂ) :
    (diagonal fun j => Complex.exp (-(z * X j)))⁻¹ = diagonal fun j => Complex.exp (z * X j) := by
  refine Matrix.inv_eq_left_inv ?_
  rw [diagonal_mul_diagonal]
  conv_rhs => rw [← diagonal_one]
  congr 1
  funext j
  rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]

theorem ptZ_one (X : Fin n → ℝ) (z s₀ : ℂ) :
    ptZ 1 X z s₀ = s₀ • diagonal fun j => Complex.exp (2 * z * X j) := by
  unfold ptZ
  simp only [mR_one, Matrix.one_mul]
  unfold aC
  simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂,
    Matrix.zero_mul, zero_add, add_zero]
  rw [inv_diag_exp, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, diagonal_mul_diagonal]
  congr 2
  funext j
  rw [← Complex.exp_add]
  congr 1
  ring

theorem gramB_diag (ε : Fin m → Bool) (b : Bool) (u : Fin m → Fin n → ℂ) (j : Fin n) :
    gramB ε b u j j = ∑ a ∈ Finset.univ.filter (fun a => ε a = b), star (u a j) * u a j := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [gramB, Qb, evX, map_sum, eval_X]

theorem trace_sdiag (s₀ : ℂ) (w : Fin n → ℂ) (G : Matrix (Fin n) (Fin n) ℂ) :
    ((s₀ • diagonal w) * G).trace = s₀ * ∑ j, w j * G j j := by
  rw [Matrix.smul_mul, trace_smul, smul_eq_mul]
  congr 1
  simp [trace, diagonal_mul]

theorem famC_one (ε : Fin m → Bool) (t c : ℝ) (e : ℤ) (X : Fin n → ℝ) (u : Fin m → Fin n → ℂ) (s : ℝ) :
    famC ε t c e 1 X (s : ℂ) u = fF c X 1 u s := by
  unfold famC fF fP
  rw [jC_one, ptZ_one, ptZ_one, gs_vS]
  unfold gC
  rw [trace_sdiag, trace_sdiag]
  simp only [gramB_diag, evX_eq, map_one, one_mul]
  have hpq : ((cnt (epsT t ε) true : ℂ) + (cnt (epsT t ε) false : ℂ)) = (m : ℂ) := by
    rw [← Nat.cast_add, cnt_add]
  rw [hpq, ← Complex.exp_add, Complex.ofReal_exp]
  have hsum : ∀ j, (∑ a ∈ Finset.univ.filter (fun a => epsT t ε a = true), star (u a j) * u a j) +
      (∑ a ∈ Finset.univ.filter (fun a => epsT t ε a = false), star (u a j) * u a j) =
      ∑ a, ((‖u a j‖ ^ 2 : ℝ) : ℂ) := by
    intro j
    have := Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (Fin m)))
      (p := fun a => epsT t ε a = true) (f := fun a => star (u a j) * u a j)
    simp only [Bool.not_eq_true] at this
    rw [this]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Complex.star_def, Complex.conj_mul']
    push_cast; ring
  have e2 : ∀ j, Complex.exp (2 * (s : ℂ) * (X j : ℂ)) = ((Real.exp (s * X j) ^ 2 : ℝ) : ℂ) := by
    intro j
    push_cast
    rw [← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  unfold nS
  push_cast
  simp only [e2]
  have key : Complex.I * (c : ℂ) * (Complex.I * ∑ j, ((Real.exp (s * X j) ^ 2 : ℝ) : ℂ) *
        ∑ a ∈ Finset.univ.filter (fun a => epsT t ε a = true), star (u a j) * u a j) -
      Complex.I * (c : ℂ) * (-Complex.I * ∑ j, ((Real.exp (s * X j) ^ 2 : ℝ) : ℂ) *
        ∑ a ∈ Finset.univ.filter (fun a => epsT t ε a = false), star (u a j) * u a j) =
      -((c : ℂ) * ∑ j, ((Real.exp (s * X j) ^ 2 : ℝ) : ℂ) * ∑ a, ((‖u a j‖ ^ 2 : ℝ) : ℂ)) := by
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    simp only [← hsum, mul_add, Finset.sum_add_distrib]
    linear_combination ((c : ℂ) * ∑ j, ((Real.exp (s * X j) ^ 2 : ℝ) : ℂ) *
        ∑ a ∈ Finset.univ.filter (fun a => epsT t ε a = true), star (u a j) * u a j +
      (c : ℂ) * ∑ j, ((Real.exp (s * X j) ^ 2 : ℝ) : ℂ) *
        ∑ a ∈ Finset.univ.filter (fun a => epsT t ε a = false), star (u a j) * u a j) * hI
  rw [key, ← Complex.exp_add]
  have hswap : ∀ (E : Fin n → ℂ) (N : Fin m → Fin n → ℂ), (∑ j, E j * ∑ a, N a j) = ∑ a, ∑ j, N a j * E j := by
    intro E N
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => mul_comm _ _
  congr 1
  push_cast
  rw [hswap]
  ring

end DCalcCH

end PositivityTheory.Rg.Sw.Glob
end
end

noncomputable section

open MeasureTheory Filter Topology MvPolynomial

namespace PositivityTheory.Rg.Sw.Glob

namespace DCalcDH

open DCalcH DCalcBH

variable {m n : ℕ}

def sqN (v : Fin m → Fin n → ℂ) : ℝ := ∑ a, ∑ j, ‖v a j‖ ^ 2

theorem sqN_nonneg (v : Fin m → Fin n → ℂ) : 0 ≤ sqN v := by
  unfold sqN; positivity

theorem norm_le_one_add_sq (v : Fin m → Fin n → ℂ) (a : Fin m) (j : Fin n) : ‖v a j‖ ≤ 1 + sqN v := by
  have h1 : ‖v a j‖ ^ 2 ≤ sqN v := by
    unfold sqN
    have ha : ‖v a j‖ ^ 2 ≤ ∑ j', ‖v a j'‖ ^ 2 :=
      Finset.single_le_sum (f := fun j' => ‖v a j'‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j)
    exact ha.trans (Finset.single_le_sum (f := fun a' => ∑ j', ‖v a' j'‖ ^ 2) (fun _ _ => by positivity)
      (Finset.mem_univ a))
  nlinarith [norm_nonneg (v a j), sq_nonneg (‖v a j‖ - 1)]

theorem norm_crd (v : Fin m → Fin n → ℂ) (k : Fin m × Fin n × Bool) : ‖crd v k‖ = ‖v k.1 k.2.1‖ := by
  unfold crd; split_ifs <;> simp

theorem evX_growth (Q : PX m n) : ∃ C N, 0 ≤ C ∧ ∀ v, ‖evX Q v‖ ≤ C * (1 + sqN v) ^ N := by
  induction Q using MvPolynomial.induction_on with
  | C a => exact ⟨‖a‖, 0, norm_nonneg _, fun v => by simp [evX_eq]⟩
  | add p q hp hq =>
    obtain ⟨C1, N1, hC1, h1⟩ := hp
    obtain ⟨C2, N2, hC2, h2⟩ := hq
    refine ⟨C1 + C2, max N1 N2, by positivity, fun v => ?_⟩
    have hs : 1 ≤ 1 + sqN v := by linarith [sqN_nonneg v]
    have e1 := pow_le_pow_right₀ hs (le_max_left N1 N2)
    have e2 := pow_le_pow_right₀ hs (le_max_right N1 N2)
    calc ‖evX (p + q) v‖ ≤ ‖evX p v‖ + ‖evX q v‖ := by rw [evX_eq, map_add (f := _)]; exact norm_add_le _ _
      _ ≤ C1 * (1 + sqN v) ^ N1 + C2 * (1 + sqN v) ^ N2 := add_le_add (h1 v) (h2 v)
      _ ≤ C1 * (1 + sqN v) ^ max N1 N2 + C2 * (1 + sqN v) ^ max N1 N2 :=
          add_le_add (mul_le_mul_of_nonneg_left e1 hC1) (mul_le_mul_of_nonneg_left e2 hC2)
      _ = (C1 + C2) * (1 + sqN v) ^ max N1 N2 := by ring
  | mul_X p k hp =>
    obtain ⟨C, N, hC, h⟩ := hp
    refine ⟨C, N + 1, hC, fun v => ?_⟩
    have hk : ‖crd v k‖ ≤ 1 + sqN v := by rw [norm_crd]; exact norm_le_one_add_sq v _ _
    calc ‖evX (p * X k) v‖ = ‖evX p v‖ * ‖crd v k‖ := by rw [evX_eq, map_mul, eval_X, norm_mul]; rfl
      _ ≤ C * (1 + sqN v) ^ N * (1 + sqN v) :=
          mul_le_mul (h v) hk (norm_nonneg _) (mul_nonneg hC (pow_nonneg (by linarith [sqN_nonneg v]) _))
      _ = C * (1 + sqN v) ^ (N + 1) := by ring

theorem poly_exp (N : ℕ) (a : ℝ) (ha : 0 < a) :
    ∃ C, 0 ≤ C ∧ ∀ x : ℝ, 0 ≤ x → (1 + x) ^ N * Real.exp (-(a * x)) ≤ C * Real.exp (-(a / 2 * x)) :=
  _root_.UpperTheory.Reformulated.B.P6.r23b.PositivityTheory.Rg.Sw.Glob.DCalcDH.poly_exp N a ha

theorem integrable_gauss_C (a : ℝ) (ha : 0 < a) : Integrable (fun z : ℂ => Real.exp (-(a * ‖z‖ ^ 2))) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) (b := (a : ℂ)) (by simpa using ha) 0 0
  refine h.norm.congr (Eventually.of_forall fun z => ?_)
  simp only [zero_mul, add_zero, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, ← Complex.ofReal_pow]

theorem integrable_gauss (a : ℝ) (ha : 0 < a) : Integrable (fun u : Fin m → Fin n → ℂ => Real.exp (-(a * sqN u))) := by
  have hinner : Integrable (fun w : Fin n → ℂ => ∏ j, Real.exp (-(a * ‖w j‖ ^ 2))) :=
    Integrable.fintype_prod (ι := Fin n) (E := ℂ) (μ := fun _ => (volume : Measure ℂ))
      (f := fun _ z => Real.exp (-(a * ‖z‖ ^ 2))) fun _ => integrable_gauss_C a ha
  have houter : Integrable (fun u : Fin m → Fin n → ℂ => ∏ i, ∏ j, Real.exp (-(a * ‖u i j‖ ^ 2))) :=
    Integrable.fintype_prod (ι := Fin m) (E := Fin n → ℂ) (μ := fun _ => (volume : Measure (Fin n → ℂ)))
      (f := fun _ w => ∏ j, Real.exp (-(a * ‖w j‖ ^ 2))) fun _ => hinner
  refine houter.congr (Eventually.of_forall fun u => ?_)
  simp only [sqN]
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib, Real.exp_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib, Real.exp_sum]

end DCalcDH

end PositivityTheory.Rg.Sw.Glob
end
end

noncomputable section

open MeasureTheory Filter Topology MvPolynomial

namespace PositivityTheory.Rg.Sw.Glob

namespace DCalcEH

open DCalcH DCalcBH DCalcDH

variable {m n : ℕ}

theorem crd_cont (X : Fin n → ℝ) (s : ℝ) : Continuous fun u : Fin m → Fin n → ℂ => crd (vS u X s) := by
  refine continuous_pi fun k => ?_
  unfold crd vS
  split_ifs <;> fun_prop

theorem fF_cont (c : ℝ) (X : Fin n → ℝ) (Q : PX m n) (s : ℝ) : Continuous fun u : Fin m → Fin n → ℂ => fF c X Q u s := by
  unfold fF fP
  refine continuous_const.mul (Continuous.mul ?_ ?_)
  · simp only [evX_eq]
    exact (MvPolynomial.continuous_eval Q).comp (crd_cont X s)
  · simp only [gs, vS]
    fun_prop

theorem norm_gs (c : ℝ) (v : Fin m → Fin n → ℂ) : ‖gs c v‖ = Real.exp (-(c * sqN v)) := by
  simp only [gs, sqN]
  rw [← Complex.ofReal_neg, Complex.norm_exp_ofReal]

theorem sq_vS_le (u : Fin m → Fin n → ℂ) (X : Fin n → ℝ) (s R : ℝ) (hs : |s| ≤ R) :
    Real.exp (-(2 * R * ∑ j, |X j|)) * sqN u ≤ sqN (vS u X s) ∧ sqN (vS u X s) ≤ Real.exp (2 * R * ∑ j, |X j|) * sqN u := by
  have hR : 0 ≤ R := (abs_nonneg s).trans hs
  have hX : ∀ j, |2 * s * X j| ≤ 2 * R * ∑ j, |X j| := by
    intro j
    have h1 : |X j| ≤ ∑ j, |X j| := Finset.single_le_sum (f := fun j => |X j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    rw [abs_mul, abs_mul, abs_two]
    have := mul_le_mul hs h1 (abs_nonneg _) hR
    nlinarith
  have hterm : ∀ a j, ‖vS u X s a j‖ ^ 2 = ‖u a j‖ ^ 2 * Real.exp (2 * s * X j) := by
    intro a j
    rw [norm_vS, ← Real.exp_nat_mul]; push_cast; ring_nf
  unfold sqN
  simp only [hterm]
  constructor
  · rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [mul_comm]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
    linarith [neg_abs_le (2 * s * X j), hX j]
  · rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity) |>.trans_eq (mul_comm _ _)
    linarith [le_abs_self (2 * s * X j), hX j]

theorem fF_bound (c : ℝ) (hc : 0 < c) (X : Fin n → ℝ) (Q : PX m n) (s : ℝ) :
    ∃ K a, 0 ≤ K ∧ 0 < a ∧ ∀ u, ∀ s' ∈ Set.Icc (s - 1) (s + 1), ‖fF c X Q u s'‖ ≤ K * Real.exp (-(a * sqN u)) := by
  set R := |s| + 1
  set M := ∑ j, |X j|
  set κ := Real.exp (-(2 * R * M))
  set κ' := Real.exp (2 * R * M)
  have hκ : 0 < κ := Real.exp_pos _
  have hκ' : 1 ≤ κ' := Real.one_le_exp (by positivity)
  obtain ⟨C, N, hC, hev⟩ := evX_growth Q
  obtain ⟨C2, hC2, hpe⟩ := poly_exp N (c * κ) (by positivity)
  refine ⟨Real.exp (R * m * M) * (C * (κ' ^ N * C2)), c * κ / 2, by positivity, by positivity, fun u s' hs' => ?_⟩
  have hs'R : |s'| ≤ R := by
    rw [abs_le]; constructor <;> linarith [hs'.1, hs'.2, neg_abs_le s, le_abs_self s]
  obtain ⟨hlo, hhi⟩ := sq_vS_le u X s' R hs'R
  have hS := sqN_nonneg u
  have h1 : ‖((Real.exp (s' * (m : ℝ) * ∑ j, X j) : ℝ) : ℂ)‖ ≤ Real.exp (R * m * M) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.2 ?_
    have : |∑ j, X j| ≤ M := Finset.abs_sum_le_sum_abs _ _
    have h2 : s' * (m : ℝ) * ∑ j, X j ≤ |s'| * m * |∑ j, X j| := by
      calc s' * (m : ℝ) * ∑ j, X j ≤ |s' * (m : ℝ) * ∑ j, X j| := le_abs_self _
        _ = |s'| * m * |∑ j, X j| := by rw [abs_mul, abs_mul, Nat.abs_cast]
    have h3 : |s'| * m * |∑ j, X j| ≤ R * m * M :=
      mul_le_mul (mul_le_mul_of_nonneg_right hs'R (by positivity)) this (abs_nonneg _) (by positivity)
    linarith
  have h2 : ‖evX Q (vS u X s')‖ ≤ C * (κ' ^ N * (1 + sqN u) ^ N) := by
    refine (hev _).trans (mul_le_mul_of_nonneg_left ?_ hC)
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by linarith [sqN_nonneg (vS u X s')]) ?_ N
    nlinarith
  have h3 : ‖gs c (vS u X s')‖ ≤ Real.exp (-(c * κ * sqN u)) := by
    rw [norm_gs]; refine Real.exp_le_exp.2 ?_
    have := mul_le_mul_of_nonneg_left hlo hc.le
    linarith
  unfold fF fP
  rw [norm_mul, norm_mul]
  calc ‖((Real.exp (s' * (m : ℝ) * ∑ j, X j) : ℝ) : ℂ)‖ * (‖evX Q (vS u X s')‖ * ‖gs c (vS u X s')‖)
      ≤ Real.exp (R * m * M) * (C * (κ' ^ N * (1 + sqN u) ^ N) * Real.exp (-(c * κ * sqN u))) :=
        mul_le_mul h1 (mul_le_mul h2 h3 (norm_nonneg _)
          (mul_nonneg hC (mul_nonneg (pow_nonneg (by linarith) _) (pow_nonneg (by linarith) _))))
          (by positivity) (by positivity)
    _ = Real.exp (R * m * M) * (C * (κ' ^ N * ((1 + sqN u) ^ N * Real.exp (-(c * κ * sqN u))))) := by ring
    _ ≤ Real.exp (R * m * M) * (C * (κ' ^ N * (C2 * Real.exp (-(c * κ / 2 * sqN u))))) := by
        have := hpe (sqN u) hS
        gcongr
    _ = Real.exp (R * m * M) * (C * (κ' ^ N * C2)) * Real.exp (-(c * κ / 2 * sqN u)) := by ring

end DCalcEH

end PositivityTheory.Rg.Sw.Glob
end
end

noncomputable section

open MeasureTheory Filter Topology MvPolynomial

namespace PositivityTheory.Rg.Sw.Glob

namespace DCalc2H

open DCalcH DCalcBH DCalcDH DCalcEH

variable {m n : ℕ}

theorem hasDeriv (c : ℝ) (X : Fin n → ℝ) (P : PX m n) (u : Fin m → Fin n → ℂ) (t : ℝ) :
    HasDerivAt (fun t => fF c X P u t) (fF c X (dil c X P) u t) t :=
  fF_hasDeriv c X P u t

theorem quot_le (c : ℝ) (X : Fin n → ℝ) (P : PX m n) (u : Fin m → Fin n → ℂ) (s B : ℝ)
    (hB : ∀ t ∈ Set.Icc (s - 1) (s + 1), ‖fF c X (dil c X P) u t‖ ≤ B) (h : ℝ) (hh : |h| ≤ 1) :
    ‖fF c X P u (s + h) - fF c X P u s‖ ≤ B * |h| := by
  have hcv : Convex ℝ (Set.Icc (s - 1) (s + 1)) := convex_Icc _ _
  have hs : s ∈ Set.Icc (s - 1) (s + 1) := ⟨by linarith, by linarith⟩
  have hsh : s + h ∈ Set.Icc (s - 1) (s + 1) := by
    rw [abs_le] at hh; exact ⟨by linarith [hh.1], by linarith [hh.2]⟩
  have := hcv.norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun t => fF c X P u t)
    (fun t _ => (hasDeriv c X P u t).hasDerivWithinAt) hB hs hsh
  simpa [Real.norm_eq_abs] using this

theorem l2conv (c : ℝ) (hc : 0 < c) (X : Fin n → ℝ) (P : PX m n) (s : ℝ) :
    Tendsto (fun h : ℝ => ∫ u, ‖(fF c X P u (s + h) - fF c X P u s) / (h : ℂ) - fF c X (dil c X P) u s‖ ^ 2)
      (𝓝[≠] 0) (𝓝 0) := by
  obtain ⟨K, a, hK, ha, hb⟩ := fF_bound c hc X (dil c X P) s
  suffices key : Tendsto (fun h : ℝ => ∫ u, ‖(fF c X P u (s + h) - fF c X P u s) / (h : ℂ) - fF c X (dil c X P) u s‖ ^ 2)
      (𝓝[≠] 0) (𝓝 (∫ _u : Fin m → Fin n → ℂ, (0 : ℝ))) by simpa using key
  refine tendsto_integral_filter_of_dominated_convergence
    (fun u => (2 * K) ^ 2 * Real.exp (-(2 * a * sqN u))) ?_ ?_ ?_ ?_
  · refine Eventually.of_forall fun h => ?_
    refine Continuous.aestronglyMeasurable ?_
    have h1 := fF_cont c X P (s + h)
    have h2 := fF_cont c X P s
    have h3 := fF_cont c X (dil c X P) s
    fun_prop
  · have hev : ∀ᶠ h in 𝓝[≠] (0 : ℝ), |h| ≤ 1 ∧ h ≠ 0 := by
      refine (eventually_nhdsWithin_of_eventually_nhds ?_).and self_mem_nhdsWithin
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with h hh
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hh
      exact hh.le
    filter_upwards [hev] with h ⟨hh, h0⟩
    refine Eventually.of_forall fun u => ?_
    have hB : ∀ t ∈ Set.Icc (s - 1) (s + 1), ‖fF c X (dil c X P) u t‖ ≤ K * Real.exp (-(a * sqN u)) := fun t ht => hb u t ht
    have hq := quot_le c X P u s _ hB h hh
    have hhpos : 0 < |h| := abs_pos.2 h0
    have e1 : ‖(fF c X P u (s + h) - fF c X P u s) / (h : ℂ)‖ ≤ K * Real.exp (-(a * sqN u)) := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, div_le_iff₀ hhpos]
      exact hq
    have e2 : ‖fF c X (dil c X P) u s‖ ≤ K * Real.exp (-(a * sqN u)) := hb u s ⟨by linarith, by linarith⟩
    have e3 : ‖(fF c X P u (s + h) - fF c X P u s) / (h : ℂ) - fF c X (dil c X P) u s‖ ≤ 2 * K * Real.exp (-(a * sqN u)) := by
      calc _ ≤ ‖(fF c X P u (s + h) - fF c X P u s) / (h : ℂ)‖ + ‖fF c X (dil c X P) u s‖ := norm_sub_le _ _
        _ ≤ _ := by linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc ‖(fF c X P u (s + h) - fF c X P u s) / (h : ℂ) - fF c X (dil c X P) u s‖ ^ 2
        ≤ (2 * K * Real.exp (-(a * sqN u))) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) e3 2
      _ = (2 * K) ^ 2 * Real.exp (-(2 * a * sqN u)) := by
        rw [mul_pow, ← Real.exp_nat_mul]; push_cast; ring_nf
  · exact (integrable_gauss (2 * a) (by positivity)).const_mul _
  · refine Eventually.of_forall fun u => ?_
    have : Tendsto (fun h : ℝ => (fF c X P u (s + h) - fF c X P u s) / (h : ℂ) - fF c X (dil c X P) u s) (𝓝[≠] 0) (𝓝 0) := by
      have h2 := (hasDeriv c X P u s).tendsto_slope_zero
      have h3 := h2.sub_const (fF c X (dil c X P) u s)
      rw [sub_self] at h3
      refine h3.congr' (Eventually.of_forall fun h => ?_)
      show h⁻¹ • (fF c X P u (s + h) - fF c X P u s) - fF c X (dil c X P) u s =
        (fF c X P u (s + h) - fF c X P u s) / (h : ℂ) - fF c X (dil c X P) u s
      rw [Complex.real_smul, Complex.ofReal_inv, div_eq_inv_mul]
    have := (this.norm).pow 2
    simpa using this

end DCalc2H

end PositivityTheory.Rg.Sw.Glob

end
end

noncomputable section

open MeasureTheory Filter Topology

namespace PositivityTheory.Rg.Sw.Glob

open DCalcBH DCalcCH in
theorem dCalc : DCalc := by
  intro m n ε t c e X hc _
  have hfun : ∀ u : Fin m → Fin n → ℂ, (fun s' : ℝ => famC ε t c e 1 X (↑s') u) = fF c X 1 u :=
    fun u => funext fun s => famC_one ε t c e X u s
  refine ⟨fun s r u => ?_, fun r s => ?_⟩
  · rw [hfun, fF_iter]
    rfl
  · simp only [hfun, fF_iter]
    rw [pow_succ']
    exact DCalc2H.l2conv c hc X ((dil c X ^ r) 1) s

end PositivityTheory.Rg.Sw.Glob
end
end

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.DilH

instance fcGR (n : ℕ) : FirstCountableTopology (GR n) := by
  have h1 : FirstCountableTopology (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) :=
    inferInstanceAs (FirstCountableTopology ((Fin n ⊕ Fin n) → (Fin n ⊕ Fin n) → ℂ))
  have h2 : FirstCountableTopology (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph.symm.isInducing).firstCountableTopology
  exact (Units.isInducing_embedProduct.comp Topology.IsInducing.subtypeVal).firstCountableTopology

theorem iteratedDeriv_mul_const (f : ℂ → ℂ) (k : ℂ) (r : ℕ) :
    iteratedDeriv r (fun w => f w * k) = fun w => iteratedDeriv r f w * k := by
  induction r with
  | zero => simp
  | succ r ih => rw [iteratedDeriv_succ, ih, iteratedDeriv_succ]; exact deriv_mul_const_field' k

theorem isSiegel_Ir {n : ℕ} {r : ℝ} (hr : 0 < r) :
    IsSiegel ((Complex.I * r) • (1 : Matrix (Fin n) (Fin n) ℂ)) ∧
      IsSiegel (((-(Complex.I * r)) • (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ) := by
  have hc : ((-(Complex.I * r)) • (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ = (Complex.I * r) • 1 := by
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, star_neg, star_mul', Complex.star_def, Complex.conj_I,
      Complex.conj_ofReal]
    ring_nf
  rw [hc]
  have : IsSiegel ((Complex.I * r) • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
    unfold IsSiegel
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, ← sub_smul, smul_smul]
    have e : -(Complex.I / 2) * (Complex.I * r - star (Complex.I * r)) = (r : ℂ) := by
      rw [star_mul', Complex.star_def, Complex.conj_I, Complex.conj_ofReal]
      ring_nf; rw [Complex.I_sq]; ring
    rw [e]
    exact Matrix.PosDef.one.smul (by exact_mod_cast hr)
  exact ⟨this, this⟩

end PositivityTheory.Rg.Sw.Glob.DilH

namespace PositivityTheory.Rg.Sw.Glob

attribute [local irreducible] famC

set_option maxHeartbeats 1000000 in
open DilAH DilCH DilEH DilH in
theorem gIdil_of' (hWTC : GlobalTheory.Published.WeilThetaConvergence) (hDecA : DecompAway) (hAway : AwayAct) (hLF : LocFact)
    (hGL : GaussLaw) (hAI : AwayIn) (hLL2 : LocalL2Isometry) (hSF : SchFP) (hLNe : LNe) (hDC : DCalc) : GIdil := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx Ψ hΨA g X a ha
  have hl0 : ∀ τ', l τ' ≠ 0 := hLNe D ψ θ l hcx.hψ hcx.hθ hcx.hl
  have hc : 0 < cLoc l τ := cLoc_pos (hl0 τ)
  have htc : |tLoc l τ| = cLoc l τ := abs_tLoc l τ
  have hfr : IsUnit fr.det := hcx.hfr.1
  have hΨ : AwayCls θ τ fr Ψ := hAI D n V θ l s τ ε fr hcx.hθ hcx.hs hcx.hfr hl0 Ψ hΨA
  obtain ⟨L, hL⟩ := hLF D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx
  obtain ⟨e, hG⟩ := hGL D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx L hL
  obtain ⟨x, y₀, hxt, hg, -⟩ := hDecA D n θ τ ι hcx.hθ hcx.hι g
  obtain ⟨A, hA⟩ := hAway D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx x hxt
  obtain ⟨hAΨ, hAact⟩ := hA Ψ hΨ
  have hsch1 : ∀ P : PX V.rank n, IsSch (fP (cLoc l τ) P) := fun P => hSF _ _ _ hc P
  obtain ⟨hB1, hB2, hB3⟩ := dBound V.rank n ε (tLoc l τ) (cLoc l τ) e X hc htc
  have hfam : ∀ (y : GR n) (z : ℂ), z ∈ stripS X → IsSch (famC ε (tLoc l τ) (cLoc l τ) e y X z) := by
    intro y z hz
    obtain ⟨h1, h2, -, -⟩ := dSieg n y X z hz
    unfold famC
    exact SchwartzDifferenceQuotient.isSch_smul _ (gCSch V.rank n ε _ _ hc htc _ _ h1 h2)
  have hphi : ∀ P : PX V.rank n, phiS θ τ fr (cLoc l τ) Ψ P = ⟨tens θ τ fr (fP (cLoc l τ) P) Ψ, hΨ.2 _ (hsch1 P)⟩ := by
    intro P; unfold phiS; rw [dite_eq_left (hΨ.2 _ (hsch1 P))]
  have hω : ∀ (y : GR n) (P : PX V.rank n), (ω (g * ι y) (phiS θ τ fr (cLoc l τ) Ψ P)).1 =
      tens θ τ fr (L (y₀ * y) (fP (cLoc l τ) P)) (A Ψ) := by
    intro y P
    have h1 : ω (ι (y₀ * y)) ⟨tens θ τ fr (fP (cLoc l τ) P) Ψ, hΨ.2 _ (hsch1 P)⟩ =
        ⟨tens θ τ fr (L (y₀ * y) (fP (cLoc l τ) P)) Ψ, hΨ.2 _ (hL.1 _ _ (hsch1 P))⟩ :=
      Subtype.ext (hL.2 _ Ψ hΨ _ (hsch1 P))
    rw [hg, mul_assoc, ← map_mul ι, map_mul ω, Module.End.mul_apply, hphi, h1]
    exact hAact _ (hL.1 _ _ (hsch1 P))
  have hbase : ∀ (y : GR n) (s' : ℝ), L (y * a s') (fP (cLoc l τ) 1) = famC ε (tLoc l τ) (cLoc l τ) e y X s' := by
    intro y s'
    rw [fP_one ε (tLoc l τ) _ hc, hG _ _ isSiegel_I, dReal _ _ ε _ _ e y X a ha s']
  have hR : ∀ s' : ℝ, (s' : ℂ) ∈ stripS X := fun s' j => by simp [div_pos Real.pi_pos]
  have hAc : Continuous (A Ψ) := FTH.cont_of_away hcx.hθ hAΨ
  set φ : GR n → ℂ → Mx D V.rank n → ℂ := fun y z xx => tens θ τ fr (famC ε (tLoc l τ) (cLoc l τ) e (y₀ * y) X z) (A Ψ) xx
    with hφ
  have hs1 : ∀ y z, z ∈ stripS X → φ y z ∈ schwartzA θ V.rank n := fun y z hz => hAΨ.2 _ (hfam _ z hz)
  have hs2 : ∀ y xx, DifferentiableOn ℂ (fun z => φ y z xx) (stripS X) := fun y xx =>
    (hB1 (y₀ * y) _).mul_const _
  have hcu : Continuous fun xx : Mx D V.rank n => fr⁻¹ * compAt θ τ xx :=
    continuous_const.matrix_mul (GlobalTheory.RealWeil.continuous_compAt hcx.hθ τ V.rank n)
  have hs3 : ∀ xx, ContinuousOn (fun p : GR n × ℂ => φ p.1 p.2 xx) (Set.univ ×ˢ stripS X) := by
    intro xx
    have hm : Continuous fun p : GR n × ℂ => (y₀ * p.1, p.2, fr⁻¹ * compAt θ τ xx) := by fun_prop
    refine ContinuousOn.mul (hB2.comp hm.continuousOn fun p hp => ⟨Set.mem_univ _, hp.2, Set.mem_univ _⟩) continuousOn_const
  have hs4 : ∀ y, ContinuousOn (fun zx : ℂ × Mx D V.rank n => φ y zx.1 zx.2) (stripS X ×ˢ Set.univ) := by
    intro y
    have hm : Continuous fun zx : ℂ × Mx D V.rank n => (y₀ * y, zx.1, fr⁻¹ * compAt θ τ zx.2) :=
      continuous_const.prodMk (continuous_fst.prodMk (hcu.comp continuous_snd))
    refine ContinuousOn.mul (hB2.comp hm.continuousOn fun p hp => ⟨Set.mem_univ _, hp.1, Set.mem_univ _⟩)
      (hAc.comp continuous_snd).continuousOn
  have hs5 : ∀ (p₀ : GR n) (z₀ : ℂ), z₀ ∈ stripS X → ∃ (N : Set (GR n × ℂ)) (M : Mx D V.rank n → ℂ), N ∈ 𝓝 (p₀, z₀) ∧
      M ∈ schwartzA θ V.rank n ∧ ∀ pz ∈ N, pz.2 ∈ stripS X → ∀ xx, ‖φ pz.1 pz.2 xx‖ ≤ ‖M xx‖ := by
    intro p₀ z₀ hz₀
    obtain ⟨N', δ, C, hN', hδ, hbd⟩ := hB3 (y₀ * p₀) z₀ hz₀
    have hm : Continuous fun p : GR n × ℂ => (y₀ * p.1, p.2) := by fun_prop
    have hdc : 0 < δ / cLoc l τ := div_pos hδ hc
    obtain ⟨hS1, hS2⟩ := isSiegel_Ir (n := n) hdc
    have hgs := gCSch V.rank n ε _ _ hc htc _ _ hS1 hS2
    refine ⟨(fun p : GR n × ℂ => (y₀ * p.1, p.2)) ⁻¹' N', tens θ τ fr (fun u => ((max C 0 : ℝ) : ℂ) *
      gC ε (tLoc l τ) (cLoc l τ) ((Complex.I * ((δ / cLoc l τ : ℝ) : ℂ)) • 1) ((-(Complex.I * ((δ / cLoc l τ : ℝ) : ℂ))) • 1) u) (A Ψ),
      hm.continuousAt.preimage_mem_nhds hN', hAΨ.2 _ (SchwartzDifferenceQuotient.isSch_smul _ hgs), fun pz hpz hz xx => ?_⟩
    have hb := hbd _ hpz hz (fr⁻¹ * compAt θ τ xx)
    simp only [hφ, tens, norm_mul]
    have hgg := gC_gauss ε (tLoc l τ) (cLoc l τ) hc δ (fr⁻¹ * compAt θ τ xx)
    rw [hgg]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_max_right C 0)]
    have he : ∀ r : ℝ, ‖Complex.exp (-(r : ℂ))‖ = Real.exp (-r) := fun r => by
      rw [← Complex.ofReal_neg, Complex.norm_exp_ofReal]
    rw [he]
    exact mul_le_mul_of_nonneg_right (hb.trans (mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.exp_pos _).le))
      (norm_nonneg _)
  obtain ⟨hcont, hdiff, hiter⟩ := dHol hWTC D n V hcx.hn hcx.hr.2.2 θ hcx.hθ ν hcx.hν (GR n) (stripS X)
    (DBoundBH.isOpen_stripS X) φ hs1 hs2 hs3 hs4 hs5
  refine ⟨stripS X, fun y z => ⨍ q, descend (GQ V) (fun h => ∑' ξ, φ y z (GlobalTheory.SiegelFormula.invPt V h ξ)) q ∂autMeasure V ν,
    DBoundBH.isOpen_stripS X, hR, hcont, fun y => ⟨hdiff y, fun t' => ?_, fun r => ?_⟩⟩
  ·
    have hfun : (ω (g * ι (y * a t')) (phiS θ τ fr (cLoc l τ) Ψ 1)).1 = φ y t' := by
      rw [hω, ← mul_assoc, hbase]
    have key : (fun h => ∑' ξ, φ y t' (GlobalTheory.SiegelFormula.invPt V h ξ)) =
        theta ω (phiS θ τ fr (cLoc l τ) Ψ 1) (g * ι (y * a t')) := by
      funext h; unfold theta; rw [hfun]; rfl
    show (⨍ q, descend (GQ V) (fun h => ∑' ξ, φ y t' (GlobalTheory.SiegelFormula.invPt V h ξ)) q ∂autMeasure V ν) = _
    rw [key]; rfl
  ·
    rw [hiter y r 0 (hR 0)]
    have hpt : ∀ xx : Mx D V.rank n, iteratedDeriv r (fun w => φ y w xx) 0 =
        tens θ τ fr (L (y₀ * y) (fP (cLoc l τ) ((dil (cLoc l τ) X ^ r) 1))) (A Ψ) xx := by
      intro xx
      simp only [hφ, tens]
      rw [iteratedDeriv_mul_const]
      beta_reduce
      by_cases hz : ∃ x₀, Ψ x₀ ≠ 0
      · obtain ⟨x₀, hx₀⟩ := hz
        obtain ⟨κ, hκ, hκL⟩ := hLL2 D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx L hL (y₀ * y)
        have hofR := congrFun (iteratedDeriv_ofReal (DBoundBH.isOpen_stripS X)
          (hB1 (y₀ * y) (fr⁻¹ * compAt θ τ xx)) hR r) 0
        simp only [Complex.ofReal_zero] at hofR
        rw [← hofR, exch dReal dBound hDC dL2 contDeriv schScale hSF hL hcx.hθ hfr hΨ hx₀ hc htc hG ha (y₀ * y) hκ hκL r]
      · push_neg at hz
        have hΨ0 : Ψ = 0 := funext hz
        have h0 : tens θ τ fr (fP (cLoc l τ) 1) (A Ψ) = 0 := by
          rw [← hAact _ (hsch1 1)]
          have : (⟨tens θ τ fr (fP (cLoc l τ) 1) Ψ, hΨ.2 _ (hsch1 1)⟩ : schwartzA θ V.rank n) = 0 :=
            Subtype.ext (by funext x'; simp [tens, hΨ0])
          rw [this, map_zero]; rfl
        have hAx : A Ψ xx = 0 := by
          have := congrFun h0 xx
          simp only [tens, Pi.zero_apply] at this
          refine (mul_eq_zero.1 this).resolve_left ?_
          simp [fP, evX, gs, Complex.exp_ne_zero]
        rw [hAx, mul_zero, mul_zero]
    have key : (fun h => ∑' ξ, iteratedDeriv r (fun w => φ y w (GlobalTheory.SiegelFormula.invPt V h ξ)) 0) =
        theta ω (phiS θ τ fr (cLoc l τ) Ψ ((dil (cLoc l τ) X ^ r) 1)) (g * ι y) := by
      funext h; unfold theta; rw [hω]
      congr 1; funext ξ; exact hpt _
    show (⨍ q, descend (GQ V) (fun h => ∑' ξ, iteratedDeriv r (fun w => φ y w (GlobalTheory.SiegelFormula.invPt V h ξ)) 0) q
      ∂autMeasure V ν) = _
    rw [key]; rfl

theorem gIdil_of (hWTC : GlobalTheory.Published.WeilThetaConvergence) (_hGZ : GZSch) (hDecA : DecompAway) (hAway : AwayAct)
    (hLF : LocFact) (hGL : GaussLaw) (hAI : AwayIn) (hLL2 : LocalL2Isometry) : GIdil :=
  gIdil_of' hWTC hDecA hAway hLF hGL hAI hLL2 schFP lNe dCalc

end PositivityTheory.Rg.Sw.Glob
end
end

namespace PositivityTheory.Rg.Sw.Glob

theorem awayAct_gen (hG : GenA) : AwayAct := awayAct_of hG fTfact decompAway

theorem locFact : LocFact := locFact_of decomp (opGen_of fTfact)

theorem localRepresentationL2 : LocalL2Isometry := local_L2_isometry fTfact

theorem gIdil_gen (h : GlobalTheory.Published.WeilThetaConvergence) (hG : GenA) : GIdil :=
  gIdil_of h gZSch decompAway (awayAct_gen hG) locFact gaussLaw awayIn localRepresentationL2

end PositivityTheory.Rg.Sw.Glob
