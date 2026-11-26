module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DifferenceQuotientIsometryExchangeAlt

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DetNeOfInG
noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.Glob.VacB

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.Glob

variable {n : ℕ}

theorem JJ_mul_JJ : JJ n * JJ n = -1 := by
  rw [JJ, fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.one_mul, Matrix.mul_zero, Matrix.mul_one, zero_add, add_zero,
    Matrix.neg_mul, Matrix.mul_neg]
  rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_neg, neg_zero]

theorem det_JJ_ne : (JJ n).det ≠ 0 := by
  intro h
  have := congrArg Matrix.det (JJ_mul_JJ (n := n))
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_neg] at this
  simp at this

theorem det_ne_of_inG {g : M2 n} (h : InG g) : g.det ≠ 0 := by
  intro h0
  have := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at this
  exact det_JJ_ne this.symm

def mkG (g : M2 n) (h : InG g) : GR n := ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero g (det_ne_of_inG h), h⟩

@[simp] theorem mR_mkG (g : M2 n) (h : InG g) : mR (mkG g h) = g := rfl

theorem inG_nU (b : Matrix (Fin n) (Fin n) ℂ) (hb : bᴴ = b) : InG (nU b) := by
  simp [InG, nU, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hb]

theorem inG_nbar (c : Matrix (Fin n) (Fin n) ℂ) (hc : cᴴ = c) : InG (nbar c) := by
  simp [InG, nbar, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hc]

theorem inG_mM (a : Matrix (Fin n) (Fin n) ℂ) (ha : IsUnit a.det) : InG (mM a) := by
  have hu : IsUnit aᴴ.det := by
    rw [Matrix.det_conjTranspose]
    exact ha.star
  simp [InG, mM, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    Matrix.conjTranspose_nonsing_inv, Matrix.mul_nonsing_inv _ hu, Matrix.nonsing_inv_mul _ ha]

def kth (θ : Fin n → ℝ) : M2 n :=
  fromBlocks (diagonal fun j => (Real.cos (θ j) : ℂ)) (diagonal fun j => (Real.sin (θ j) : ℂ))
    (-diagonal fun j => (Real.sin (θ j) : ℂ)) (diagonal fun j => (Real.cos (θ j) : ℂ))

theorem inK_kth (θ : Fin n → ℝ) : InK (kth θ) := by
  have hcs : ∀ j : Fin n, (Real.cos (θ j) : ℂ) * Real.cos (θ j) + (Real.sin (θ j) : ℂ) * Real.sin (θ j) = 1 := by
    intro j
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_add]
    rw [← sq, ← sq, Real.cos_sq_add_sin_sq, Complex.ofReal_one]
  have hsc : ∀ j : Fin n, (Real.sin (θ j) : ℂ) * Real.sin (θ j) + (Real.cos (θ j) : ℂ) * Real.cos (θ j) = 1 := by
    intro j
    rw [add_comm]
    exact hcs j
  refine ⟨?_, ?_⟩
  · simp [InG, kth, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
      Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, -Complex.ofReal_cos,
      -Complex.ofReal_sin, Complex.conj_ofReal, hcs, hsc]
    refine ⟨?_, ?_, ?_⟩
    · funext i
      rw [Pi.zero_apply]
      ring
    · ext i j
      rw [Matrix.diagonal_apply, Matrix.neg_apply, Matrix.one_apply]
      split_ifs
      · linear_combination -(hcs i)
      · simp
    · funext i
      rw [Pi.zero_apply]
      ring
  · simp [kth, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
      Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, -Complex.ofReal_cos,
      -Complex.ofReal_sin, Complex.conj_ofReal, hcs, hsc]
    have h0 : (Matrix.diagonal fun i : Fin n => (Real.cos (θ i) : ℂ) * Real.sin (θ i) +
        -((Real.sin (θ i) : ℂ) * Real.cos (θ i))) = 0 := by
      rw [← Matrix.diagonal_zero]
      congr 1
      funext i
      ring
    have h1 : (Matrix.diagonal fun i : Fin n => (Real.sin (θ i) : ℂ) * Real.cos (θ i) +
        -((Real.cos (θ i) : ℂ) * Real.sin (θ i))) = 0 := by
      rw [← Matrix.diagonal_zero]
      congr 1
      funext i
      ring
    rw [h0, h1, Matrix.fromBlocks_one]

end PositivityTheory.Rg.Sw.Glob.VacB
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussScalar
noncomputable section

open Complex MeasureTheory

namespace PositivityTheory.Rg.Sw.Glob.VacS

theorem gauss_scalar (b : ℂ) (hb : 0 < b.re) (s : ℝ) (w : ℂ) :
    ∫ y : ℂ, cexp (-b * ((‖y‖ ^ 2 : ℝ) : ℂ)) * cexp (I * ((2 * s : ℝ) : ℂ) * (((starRingEnd ℂ w) * y).re : ℂ)) =
      ((Real.pi : ℂ) / b) * cexp (-((s : ℂ) ^ 2) * ((‖w‖ ^ 2 : ℝ) : ℂ) / b) := by
  have h := GaussianFourier.integral_cexp_neg_mul_sq_norm_add (V := ℂ) hb (I * ((2 * s : ℝ) : ℂ)) w
  have hf : (Module.finrank ℝ ℂ : ℂ) / 2 = 1 := by
    rw [Complex.finrank_real_complex]; norm_num
  rw [hf, cpow_one] at h
  have e1 : ∀ y : ℂ, cexp (-b * ((‖y‖ ^ 2 : ℝ) : ℂ)) * cexp (I * ((2 * s : ℝ) : ℂ) * (((starRingEnd ℂ w) * y).re : ℂ)) =
      cexp (-b * (‖y‖ : ℂ) ^ 2 + I * ((2 * s : ℝ) : ℂ) * ((inner ℝ w y : ℝ) : ℂ)) := by
    intro y
    rw [← Complex.exp_add, Complex.inner, mul_comm (starRingEnd ℂ w) y]
    push_cast
    ring_nf
  simp_rw [e1]
  rw [h]
  congr 1
  congr 1
  push_cast
  have hb0 : b ≠ 0 := by
    intro h0; rw [h0] at hb; simp at hb
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

def DG {m n : ℕ} (K : ℂ) (γ : Fin m → Fin n → ℂ) (v : Fin m → Fin n → ℂ) : ℂ :=
  K * ∏ a, ∏ j, cexp (-γ a j * ((‖v a j‖ ^ 2 : ℝ) : ℂ))

def ftG {m n : ℕ} (σ : Fin m → ℝ) (s : ℝ) (f : (Fin m → Fin n → ℂ) → ℂ) (u : Fin m → Fin n → ℂ) : ℂ :=
  ∫ y : Fin m → Fin n → ℂ, f y *
    cexp (I * ((2 * s : ℝ) : ℂ) * ((∑ a, ∑ j, σ a * ((starRingEnd ℂ (u a j)) * y a j).re : ℝ) : ℂ))

theorem ftG_DG {m n : ℕ} (σ : Fin m → ℝ) (s : ℝ) (K : ℂ) (γ : Fin m → Fin n → ℂ) (hγ : ∀ a j, 0 < (γ a j).re)
    (u : Fin m → Fin n → ℂ) :
    ftG σ s (DG K γ) u = DG (K * ∏ a, ∏ j, ((Real.pi : ℂ) / γ a j))
      (fun a j => (s : ℂ) ^ 2 * ((σ a : ℂ) ^ 2) / γ a j) u := by
  have hk : ∀ y : Fin m → Fin n → ℂ, DG K γ y *
      cexp (I * ((2 * s : ℝ) : ℂ) * ((∑ a, ∑ j, σ a * ((starRingEnd ℂ (u a j)) * y a j).re : ℝ) : ℂ)) =
      K * ∏ a, ∏ j, (cexp (-γ a j * ((‖y a j‖ ^ 2 : ℝ) : ℂ)) *
        cexp (I * ((2 * s : ℝ) : ℂ) * (((starRingEnd ℂ ((σ a : ℂ) * u a j)) * y a j).re : ℂ))) := by
    intro y
    unfold DG
    have e : cexp (I * ((2 * s : ℝ) : ℂ) * ((∑ a, ∑ j, σ a * ((starRingEnd ℂ (u a j)) * y a j).re : ℝ) : ℂ)) =
        ∏ a, ∏ j, cexp (I * ((2 * s : ℝ) : ℂ) * (((starRingEnd ℂ ((σ a : ℂ) * u a j)) * y a j).re : ℂ)) := by
      rw [Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum]
      refine Finset.prod_congr rfl fun a _ => ?_
      rw [Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum]
      refine Finset.prod_congr rfl fun j _ => ?_
      congr 2
      rw [map_mul, Complex.conj_ofReal, mul_assoc, Complex.re_ofReal_mul]
      all_goals (push_cast; try ring)
    rw [e, mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [← Finset.prod_mul_distrib]
  unfold ftG
  simp_rw [hk]
  rw [integral_const_mul]
  have hI : ∫ y : Fin m → Fin n → ℂ, ∏ a, ∏ j, (cexp (-γ a j * ((‖y a j‖ ^ 2 : ℝ) : ℂ)) *
        cexp (I * ((2 * s : ℝ) : ℂ) * (((starRingEnd ℂ ((σ a : ℂ) * u a j)) * y a j).re : ℂ))) =
      ∏ a, ∏ j, (((Real.pi : ℂ) / γ a j) * cexp (-((s : ℂ) ^ 2) * ((‖(σ a : ℂ) * u a j‖ ^ 2 : ℝ) : ℂ) / γ a j)) := by
    rw [integral_fintype_prod_volume_eq_prod (f := fun a (x : Fin n → ℂ) => ∏ j, (cexp (-γ a j * ((‖x j‖ ^ 2 : ℝ) : ℂ)) *
        cexp (I * ((2 * s : ℝ) : ℂ) * (((starRingEnd ℂ ((σ a : ℂ) * u a j)) * x j).re : ℂ))))]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [integral_fintype_prod_volume_eq_prod (f := fun j (z : ℂ) => (cexp (-γ a j * ((‖z‖ ^ 2 : ℝ) : ℂ)) *
        cexp (I * ((2 * s : ℝ) : ℂ) * (((starRingEnd ℂ ((σ a : ℂ) * u a j)) * z).re : ℂ))))]
    refine Finset.prod_congr rfl fun j _ => ?_
    exact gauss_scalar _ (hγ a j) s _
  rw [hI]
  unfold DG
  rw [mul_assoc]
  congr 1
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  congr 1
  congr 1
  rw [norm_mul, Complex.norm_real]
  push_cast
  have hg : γ a j ≠ 0 := by
    intro h0; have := hγ a j; rw [h0] at this; simp at this
  field_simp
  rw [Real.norm_eq_abs]
  have hs : ((|σ a| : ℝ) : ℂ) ^ 2 = ((σ a : ℝ) : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, sq_abs]
  push_cast
  rw [hs]
  ring

end PositivityTheory.Rg.Sw.Glob.VacS
end
end

noncomputable section

open Matrix Complex

namespace PositivityTheory.Rg.Sw.Glob.VacC

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.Glob PositivityTheory.Rg.Sw.Glob.VacS

variable {m n : ℕ}

def sigR (ε : Fin m → Bool) (a : Fin m) : ℝ := if ε a then 1 else -1

theorem sgn_eq (ε : Fin m → Bool) (a : Fin m) : sgn ε a = ((sigR ε a : ℝ) : ℂ) := by
  unfold sgn sigR
  by_cases h : ε a <;> simp [h]

theorem ftLoc_eq (ε : Fin m → Bool) (s : ℝ) (f : (Fin m → Fin n → ℂ) → ℂ) (u : Fin m → Fin n → ℂ) :
    ftLoc ε s f u = ftG (sigR ε) s f u := by
  simp only [ftLoc, ftG]
  congr 1
  funext y
  have key : ((of u)ᴴ * diagonal (sgn ε) * of y).trace.re =
      ∑ a, ∑ j, sigR ε a * ((starRingEnd ℂ) (u a j) * y a j).re := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.of_apply, Complex.re_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    rw [sgn_eq, mul_comm (star (u a j)) _, mul_assoc, Complex.re_ofReal_mul]
    rfl
  rw [key]

theorem gramX_diag (ε : Fin m → Bool) (u : Fin m → Fin n → ℂ) (j : Fin n) :
    gramX ε u j j = ∑ a, ((sigR ε a : ℝ) : ℂ) * ((‖u a j‖ ^ 2 : ℝ) : ℂ) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gramX, Qp, Qb, evX, map_sub, map_sum, map_mul, MvPolynomial.eval_X, if_true,
    Bool.false_eq_true, if_false, Finset.sum_filter]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : ε a <;> simp [h, sigR, Complex.conj_mul']

theorem chN_DG (ε : Fin m → Bool) (t : ℝ) (β : Fin n → ℝ) (K : ℂ) (γ : Fin m → Fin n → ℂ) (u : Fin m → Fin n → ℂ) :
    chN ε t (diagonal fun j => (β j : ℂ)) u * DG K γ u =
      DG K (fun a j => γ a j - I * t * (sigR ε a : ℂ) * (β j : ℂ)) u := by
  simp only [chN, DG]
  simp only [← Complex.exp_sum]
  rw [mul_left_comm, ← Complex.exp_add]
  congr 2
  have htr : (diagonal (fun j => (β j : ℂ)) * gramX ε u).trace = ∑ j, (β j : ℂ) * gramX ε u j j := by
    simp [Matrix.trace, Matrix.diagonal_mul]
  rw [htr]
  simp_rw [gramX_diag, Finset.mul_sum]
  conv_lhs => arg 1; rw [Finset.sum_comm]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem dg_const (K γ0 : ℂ) (v : Fin m → Fin n → ℂ) :
    DG K (fun _ _ => γ0) v = K * cexp (-γ0 * ∑ a, ∑ j, ((‖v a j‖ ^ 2 : ℝ) : ℂ)) := by
  simp only [DG]
  congr 1
  rw [Finset.mul_sum, Complex.exp_sum]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [Finset.mul_sum, Complex.exp_sum]

theorem vac_eq (ε : Fin m → Bool) (t c : ℝ) : vac (n := n) ε t c = DG 1 (fun _ _ => (c : ℂ)) := by
  funext y
  rw [dg_const, one_mul]
  simp only [vac, gZf]
  congr 1
  have hsum : (gramB (epsT t ε) true y).trace + (gramB (epsT t ε) false y).trace =
      ∑ a, ∑ j, ((‖y a j‖ ^ 2 : ℝ) : ℂ) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.trace, Matrix.diag, gramB, Qb, evX, map_sum, Finset.sum_filter]
    rw [← Finset.sum_add_distrib, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases h : epsT t ε a <;> simp [h, Complex.conj_mul']
  rw [smul_mul_assoc, one_mul, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
    smul_mul_assoc, one_mul, Matrix.trace_smul, Matrix.trace_smul]
  simp only [smul_eq_mul, Complex.star_def, Complex.conj_I]
  linear_combination ((c : ℂ) * ((gramB (epsT t ε) true y).trace + (gramB (epsT t ε) false y).trace)) *
    Complex.I_sq + (-(c : ℂ)) * hsum

theorem levF_diag (e : ℤ) (δ : Fin n → ℝ) (hδ : ∀ j, 0 < δ j) (K : ℂ) (γ : Fin m → Fin n → ℂ) :
    levF e (diagonal fun j => (δ j : ℂ)) (DG K γ) =
      DG (K * (∏ j, (δ j : ℂ)) ^ m) (fun a j => γ a j * ((δ j : ℂ) ^ 2)) := by
  funext u
  simp only [levF, DG, Matrix.det_diagonal]
  have hD : (∏ j, (δ j : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => by exact_mod_cast (hδ j).ne'
  have hs : star (∏ j, (δ j : ℂ)) = ∏ j, (δ j : ℂ) := by
    rw [← Complex.ofReal_prod]
    exact Complex.conj_ofReal _
  rw [hs, ← zpow_add₀ hD, add_sub_cancel, zpow_natCast]
  rw [← mul_assoc, mul_comm (_ ^ m) K]
  congr 1
  refine Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun j _ => ?_
  congr 1
  simp only [Matrix.mul_diagonal, Matrix.of_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    mul_pow, sq_abs]
  push_cast
  ring

end PositivityTheory.Rg.Sw.Glob.VacC
