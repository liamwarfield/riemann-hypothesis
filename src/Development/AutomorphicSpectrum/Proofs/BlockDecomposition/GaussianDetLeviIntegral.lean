module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwKerIffAverage
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeLogBound

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussianDetSquareIntegral
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussianDetSquareIntegral
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate

noncomputable section

namespace GlobalTheory.CompanionTheory.FSCrofton.GaussDet

theorem integral_exp_sq : ∫ z : ℂ, Real.exp (-‖z‖ ^ 2) = Real.pi := by
  have h := Complex.integral_exp_neg_rpow (p := 2) (by norm_num)
  simp only [Real.rpow_two] at h
  rw [h]
  norm_num

theorem integral_sq_exp_sq : ∫ z : ℂ, ‖z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) = Real.pi := by
  have h := Complex.integral_rpow_mul_exp_neg_rpow (p := 2) (q := 2) (by norm_num) (by norm_num)
  simp only [Real.rpow_two] at h
  rw [h]
  norm_num

theorem integrable_exp_sq : Integrable (fun z : ℂ => Real.exp (-‖z‖ ^ 2)) :=
  Integrable.of_integral_ne_zero (by rw [integral_exp_sq]; exact Real.pi_ne_zero)

theorem integrable_sq_exp_sq : Integrable (fun z : ℂ => ‖z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)) :=
  Integrable.of_integral_ne_zero (by rw [integral_sq_exp_sq]; exact Real.pi_ne_zero)

def hf (p q : Prop) [Decidable p] [Decidable q] (z : ℂ) : ℂ :=
  (if p then z else 1) * (if q then conj z else 1) * (Real.exp (-‖z‖ ^ 2) : ℂ)

theorem continuous_hf (p q : Prop) [Decidable p] [Decidable q] : Continuous (hf p q) := by
  unfold hf
  by_cases hp : p <;> by_cases hq : q <;> simp only [hp, hq, if_true, if_false] <;> fun_prop

theorem integrable_hf (p q : Prop) [Decidable p] [Decidable q] : Integrable (hf p q) := by
  refine Integrable.mono' (integrable_exp_sq.add integrable_sq_exp_sq)
    (continuous_hf p q).aestronglyMeasurable (ae_of_all _ fun z => ?_)
  have he : 0 < Real.exp (-‖z‖ ^ 2) := Real.exp_pos _
  have hz : 0 ≤ ‖z‖ := norm_nonneg z
  have hn : ‖((Real.exp (-‖z‖ ^ 2) : ℝ) : ℂ)‖ = Real.exp (-‖z‖ ^ 2) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos he]
  have hb : ‖z‖ ≤ 1 + ‖z‖ ^ 2 := by nlinarith [sq_nonneg (‖z‖ - 1)]
  simp only [hf, norm_mul, hn, Pi.add_apply]
  by_cases hp : p <;> by_cases hq : q <;> simp only [hp, hq, if_true, if_false, norm_one, Complex.norm_conj] <;>
    nlinarith [mul_le_mul_of_nonneg_right hb he.le, mul_pos he he, mul_nonneg (sq_nonneg ‖z‖) he.le]

theorem hf_neg_of_ne (p q : Prop) [Decidable p] [Decidable q] (h : ¬ (p ↔ q)) (z : ℂ) :
    hf p q (-z) = - hf p q z := by
  unfold hf
  by_cases hp : p <;> by_cases hq : q <;> simp_all

theorem integral_hf (p q : Prop) [Decidable p] [Decidable q] :
    ∫ z, hf p q z = if p ↔ q then (Real.pi : ℂ) else 0 := by
  by_cases h : p ↔ q
  · rw [if_pos h]
    by_cases hp : p
    · have hq : q := h.1 hp
      have : hf p q = fun z : ℂ => ((‖z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) : ℝ) : ℂ) := by
        funext z
        simp only [hf, hp, hq, if_true, Complex.mul_conj, Complex.normSq_eq_norm_sq]
        push_cast
        ring
      simp_rw [this]
      rw [integral_complex_ofReal, integral_sq_exp_sq]
    · have hq : ¬ q := fun hq => hp (h.2 hq)
      have : hf p q = fun z : ℂ => ((Real.exp (-‖z‖ ^ 2) : ℝ) : ℂ) := by
        funext z
        simp only [hf, hp, hq, if_false, one_mul]
      simp_rw [this]
      rw [integral_complex_ofReal, integral_exp_sq]
  · rw [if_neg h]
    have h1 : ∫ z, hf p q (-z) = ∫ z, hf p q z := integral_neg_eq_self _ _
    simp only [hf_neg_of_ne p q h, integral_neg] at h1
    have h2 : (2 : ℂ) * ∫ z, hf p q z = 0 := by linear_combination -h1
    simpa using h2

variable {β : Type} [Fintype β] [DecidableEq β]

def eR (r : β → ℂ) : ℂ := (Real.exp (-∑ k, ‖r k‖ ^ 2) : ℂ)

theorem row_prod (i j : β) (r : β → ℂ) :
    r i * conj (r j) * eR r = ∏ k, hf (k = i) (k = j) (r k) := by
  simp only [hf, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, if_true, eR]
  rw [← Finset.sum_neg_distrib, Real.exp_sum]
  push_cast
  rfl

theorem integrable_row (i j : β) :
    Integrable (fun r : β → ℂ => r i * conj (r j) * eR r) := by
  simp_rw [row_prod, volume_pi]
  exact Integrable.fintype_prod (f := fun k : β => hf (k = i) (k = j)) (μ := fun _ => volume)
    fun k => integrable_hf _ _

theorem integral_row (i j : β) :
    ∫ r : β → ℂ, r i * conj (r j) * eR r =
      if i = j then (Real.pi : ℂ) ^ Fintype.card β else 0 := by
  simp_rw [row_prod]
  rw [integral_fintype_prod_volume_eq_prod (fun k : β => hf (k = i) (k = j))]
  simp_rw [integral_hf]
  by_cases h : i = j
  · subst h
    simp
  · rw [if_neg h]
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    simp [h]

variable {d : ℕ}

def rowF (G : Matrix β (Fin d) ℂ) (a c : Fin d) (r : β → ℂ) : ℂ :=
  (∑ i, r i * G i a) * conj (∑ j, r j * G j c) * eR r

theorem rowF_eq (G : Matrix β (Fin d) ℂ) (a c : Fin d) (r : β → ℂ) :
    rowF G a c r = ∑ i, ∑ j, (G i a * conj (G j c)) * (r i * conj (r j) * eR r) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [rowF, map_sum, Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul]
  ring

theorem integrable_rowF (G : Matrix β (Fin d) ℂ) (a c : Fin d) : Integrable (rowF G a c) := by
  have : rowF G a c = fun r => ∑ i, ∑ j, (G i a * conj (G j c)) * (r i * conj (r j) * eR r) :=
    funext (rowF_eq G a c)
  rw [this]
  exact MeasureTheory.integrable_finsetSum _ fun i _ => MeasureTheory.integrable_finsetSum _ fun j _ =>
    (integrable_row i j).const_mul _

theorem integral_rowF (G : Matrix β (Fin d) ℂ) (a c : Fin d) :
    ∫ r, rowF G a c r = (Real.pi : ℂ) ^ Fintype.card β * (G.conjTranspose * G) c a := by
  simp_rw [rowF_eq]
  rw [MeasureTheory.integral_finsetSum _ fun i _ => MeasureTheory.integrable_finsetSum _ fun j _ =>
    (integrable_row i j).const_mul _]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [MeasureTheory.integral_finsetSum _ fun j _ => (integrable_row i j).const_mul _]
  simp only [integral_const_mul, integral_row, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]
  simp only [Complex.star_def]
  ring

theorem det_expand (G : Matrix β (Fin d) ℂ) (C : Fin d → β → ℂ) :
    ((Real.exp (-∑ k, ∑ j, ‖C k j‖ ^ 2) * ‖(Matrix.of C * G).det‖ ^ 2 : ℝ) : ℂ) =
      ∑ σ : Equiv.Perm (Fin d), ∑ τ : Equiv.Perm (Fin d),
        (((Equiv.Perm.sign σ : ℤ) : ℂ) * ((Equiv.Perm.sign τ : ℤ) : ℂ)) *
          ∏ k, rowF G (σ k) (τ k) (C k) := by
  set M := Matrix.of C * G with hMdef
  have hM : ∀ k a, M k a = ∑ i, C k i * G i a := fun k a => by
    simp [hMdef, Matrix.mul_apply]
  have hd : M.det = ∑ σ : Equiv.Perm (Fin d), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k, M k (σ k) := by
    rw [← Matrix.det_transpose, Matrix.det_apply']
    simp [Matrix.transpose_apply]
  have hc : conj M.det =
      ∑ τ : Equiv.Perm (Fin d), ((Equiv.Perm.sign τ : ℤ) : ℂ) * ∏ k, conj (M k (τ k)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hd, map_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [map_mul, map_prod]
    simp
  have hn : ((‖M.det‖ ^ 2 : ℝ) : ℂ) = M.det * conj M.det := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hE : ((Real.exp (-∑ k, ∑ j, ‖C k j‖ ^ 2) : ℝ) : ℂ) = ∏ k, eR (C k) := by
    simp only [eR]
    rw [← Finset.sum_neg_distrib, Real.exp_sum]
    push_cast
    rfl
  have hp : ∀ σ τ : Equiv.Perm (Fin d), ∏ k, rowF G (σ k) (τ k) (C k) =
      (∏ k, M k (σ k)) * (∏ k, conj (M k (τ k))) * ∏ k, eR (C k) := fun σ τ => by
    simp only [rowF, Finset.prod_mul_distrib, hM]
  rw [Complex.ofReal_mul, hn, hE]
  conv_lhs => rw [hc]; rw [hd]
  simp only [hp]
  rw [Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  ring

theorem perm_sum (p : ℂ) (A : Matrix (Fin d) (Fin d) ℂ) :
    ∑ σ : Equiv.Perm (Fin d), ∑ τ : Equiv.Perm (Fin d),
        (((Equiv.Perm.sign σ : ℤ) : ℂ) * ((Equiv.Perm.sign τ : ℤ) : ℂ)) *
          ∏ k, (p * A (τ k) (σ k)) = p ^ d * (d.factorial : ℂ) * A.det := by
  have h1 : ∀ σ : Equiv.Perm (Fin d), ∑ τ : Equiv.Perm (Fin d),
      (((Equiv.Perm.sign σ : ℤ) : ℂ) * ((Equiv.Perm.sign τ : ℤ) : ℂ)) *
        ∏ k, (p * A (τ k) (σ k)) = p ^ d * A.det := fun σ => by
    have h2 := Matrix.det_permute' σ A
    rw [Matrix.det_apply'] at h2
    simp only [Matrix.submatrix_apply, id] at h2
    have hs : ((Equiv.Perm.sign σ : ℤ) : ℂ) * ((Equiv.Perm.sign σ : ℤ) : ℂ) = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
    calc _ = ((Equiv.Perm.sign σ : ℤ) : ℂ) * p ^ d *
          ∑ τ : Equiv.Perm (Fin d), ((Equiv.Perm.sign τ : ℤ) : ℂ) * ∏ k, A (τ k) (σ k) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun τ _ => ?_
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          ring
      _ = p ^ d * A.det := by
          rw [h2]
          linear_combination (p ^ d * A.det) * hs
  simp only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem integrable_prod_rowF (G : Matrix β (Fin d) ℂ) (σ τ : Equiv.Perm (Fin d)) :
    Integrable (fun C : Fin d → β → ℂ => ∏ k, rowF G (σ k) (τ k) (C k)) := by
  rw [volume_pi]
  exact Integrable.fintype_prod (f := fun k : Fin d => rowF G (σ k) (τ k)) (μ := fun _ => volume)
    fun k => integrable_rowF G _ _

theorem integral_prod_rowF (G : Matrix β (Fin d) ℂ) (σ τ : Equiv.Perm (Fin d)) :
    ∫ C : Fin d → β → ℂ, ∏ k, rowF G (σ k) (τ k) (C k) =
      ∏ k, ((Real.pi : ℂ) ^ Fintype.card β * (G.conjTranspose * G) (τ k) (σ k)) := by
  rw [integral_fintype_prod_volume_eq_prod (fun k : Fin d => rowF G (σ k) (τ k))]
  simp_rw [integral_rowF]

def fR (G : Matrix β (Fin d) ℂ) (C : Fin d → β → ℂ) : ℝ :=
  Real.exp (-∑ k, ∑ j, ‖C k j‖ ^ 2) * ‖(Matrix.of C * G).det‖ ^ 2

theorem integrable_fR_complex (G : Matrix β (Fin d) ℂ) :
    Integrable (fun C => ((fR G C : ℝ) : ℂ)) := by
  simp_rw [fR, det_expand]
  exact MeasureTheory.integrable_finsetSum _ fun σ _ => MeasureTheory.integrable_finsetSum _ fun τ _ =>
    (integrable_prod_rowF G σ τ).const_mul _

theorem integral_fR_complex (G : Matrix β (Fin d) ℂ) :
    ∫ C, ((fR G C : ℝ) : ℂ) = ((Real.pi : ℂ) ^ Fintype.card β) ^ d * (d.factorial : ℂ) *
      (G.conjTranspose * G).det := by
  simp_rw [fR, det_expand]
  rw [MeasureTheory.integral_finsetSum _ fun σ _ => MeasureTheory.integrable_finsetSum _ fun τ _ =>
    (integrable_prod_rowF G σ τ).const_mul _]
  rw [← perm_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [MeasureTheory.integral_finsetSum _ fun τ _ => (integrable_prod_rowF G σ τ).const_mul _]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [integral_const_mul, integral_prod_rowF]

end GlobalTheory.CompanionTheory.FSCrofton.GaussDet


open GlobalTheory.CompanionTheory.FSCrofton.GaussDet in
theorem GlobalTheory.CompanionTheory.FSCrofton.lintegral_gW_norm_det_sq (d : ℕ) (β : Type) [Fintype β] [DecidableEq β]
    (G : Matrix β (Fin d) ℂ) :
    ∫⁻ C : Fin d → β → ℂ, gW d β C * ENNReal.ofReal (‖(Matrix.of C * G).det‖ ^ 2) =
      ENNReal.ofReal (Real.pi ^ (d * Fintype.card β) * (d.factorial : ℝ) *
        (G.conjTranspose * G).det.re) := by
  have hint : Integrable (fR G) := by
    have := (integrable_fR_complex G).re
    simpa using this
  have hnn : 0 ≤ᵐ[volume] fR G := ae_of_all _ fun C => by
    simp only [fR, Pi.zero_apply]
    positivity
  have hval : ∫ C, fR G C = Real.pi ^ (d * Fintype.card β) * (d.factorial : ℝ) *
      (G.conjTranspose * G).det.re := by
    have h := integral_fR_complex G
    rw [integral_complex_ofReal] at h
    have h2 := congrArg Complex.re h
    rw [Complex.ofReal_re] at h2
    rw [h2, pow_mul' ]
    have : ((Real.pi : ℂ) ^ Fintype.card β) ^ d * (d.factorial : ℂ) =
        (((Real.pi ^ Fintype.card β) ^ d * (d.factorial : ℝ) : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [this, Complex.re_ofReal_mul]
  rw [← hval, ofReal_integral_eq_lintegral_ofReal hint hnn]
  refine lintegral_congr fun C => ?_
  rw [gW, fR, ENNReal.ofReal_mul (Real.exp_pos _).le]
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussianDetSquareIntegralStatement
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussian_det_square_integral : ∀ (d : ℕ) (β : Type) [Fintype β] [DecidableEq β] (G : Matrix β (Fin d) ℂ), ∫⁻ C : Fin d → β → ℂ, gW d β C * ENNReal.ofReal (‖(Matrix.of C * G).det‖ ^ 2) = ENNReal.ofReal (Real.pi ^ (d * Fintype.card β) * (d.factorial : ℝ) * (G.conjTranspose * G).det.re) := by
  first | exact @GlobalTheory.CompanionTheory.FSCrofton.lintegral_gW_norm_det_sq | exact GlobalTheory.CompanionTheory.FSCrofton.lintegral_gW_norm_det_sq | (intros; apply GlobalTheory.CompanionTheory.FSCrofton.lintegral_gW_norm_det_sq <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussianDetLeviIntegral
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate

noncomputable section

namespace GlobalTheory.CompanionTheory.FSCrofton.GaussLevi

open Matrix

variable {β : Type} [Fintype β] [DecidableEq β]

def rk (f : β → ℂ) : Matrix β β ℂ := vecMulVec f (star f)

def nS (f : β → ℂ) : ℝ := 1 + ∑ j, ‖f j‖ ^ 2

theorem nS_pos (f : β → ℂ) : 0 < nS f := by
  unfold nS; positivity

theorem star_dot (f : β → ℂ) : star f ⬝ᵥ f = ((nS f - 1 : ℝ) : ℂ) := by
  simp [nS, dotProduct, Complex.conj_mul']

theorem rk_mul_rk (f : β → ℂ) : rk f * rk f = ((nS f - 1 : ℝ) : ℂ) • rk f := by
  unfold rk
  rw [vecMulVec_mul_vecMulVec, star_dot, vecMulVec_smul]

theorem rk_conjTranspose (f : β → ℂ) : (rk f)ᴴ = rk f := by
  unfold rk
  rw [conjTranspose_vecMulVec, star_star]

theorem one_add_mul_one_sub (A : Matrix β β ℂ) (c t u : ℂ) (h : A * A = c • A) :
    (1 + t • A) * (1 - u • A) = 1 + (t - u - t * u * c) • A := by
  simp only [mul_sub, add_mul, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, h, smul_smul]
  module

theorem one_sub_mul_one_sub (A : Matrix β β ℂ) (c u : ℂ) (h : A * A = c • A) :
    (1 - u • A) * (1 - u • A) = 1 + (-(2 * u) + u * u * c) • A := by
  simp only [mul_sub, sub_mul, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, h, smul_smul]
  module

def pM (f : β → ℂ) : Matrix β β ℂ := 1 + ((1 / (1 + √(nS f)) : ℝ) : ℂ) • rk f

def rM (f : β → ℂ) : Matrix β β ℂ := 1 - ((1 / (√(nS f) * (1 + √(nS f))) : ℝ) : ℂ) • rk f

theorem sqrt_facts (f : β → ℂ) : 0 < √(nS f) ∧ √(nS f) * √(nS f) = nS f :=
  ⟨Real.sqrt_pos.2 (nS_pos f), Real.mul_self_sqrt (nS_pos f).le⟩

theorem pM_mul_rM (f : β → ℂ) : pM f * rM f = 1 := by
  obtain ⟨h0, h1⟩ := sqrt_facts f
  unfold pM rM
  rw [one_add_mul_one_sub _ _ _ _ (rk_mul_rk f)]
  have : ((1 / (1 + √(nS f)) : ℝ) : ℂ) - ((1 / (√(nS f) * (1 + √(nS f))) : ℝ) : ℂ) -
      ((1 / (1 + √(nS f)) : ℝ) : ℂ) * ((1 / (√(nS f) * (1 + √(nS f))) : ℝ) : ℂ) *
        ((nS f - 1 : ℝ) : ℂ) = 0 := by
    norm_cast
    generalize √(nS f) = s at h0 h1 ⊢
    rw [← h1]
    field_simp
    ring
  rw [this, zero_smul, add_zero]

theorem rM_conjTranspose (f : β → ℂ) : (rM f)ᴴ = rM f := by
  unfold rM
  rw [conjTranspose_sub, conjTranspose_one, conjTranspose_smul, rk_conjTranspose]
  simp

theorem rM_mul_rM (f : β → ℂ) : rM f * rM f = 1 - ((1 / nS f : ℝ) : ℂ) • rk f := by
  obtain ⟨h0, h1⟩ := sqrt_facts f
  unfold rM
  rw [one_sub_mul_one_sub _ _ _ (rk_mul_rk f), sub_eq_add_neg 1, ← neg_smul]
  congr 2
  norm_cast
  generalize √(nS f) = s at h0 h1 ⊢
  rw [← h1]
  field_simp
  ring

theorem det_pM (f : β → ℂ) : (pM f).det = ((√(nS f) : ℝ) : ℂ) := by
  obtain ⟨h0, h1⟩ := sqrt_facts f
  have e : pM f = 1 + replicateCol Unit (((1 / (1 + √(nS f)) : ℝ) : ℂ) • f) *
      replicateRow Unit (star f) := by
    unfold pM rk
    congr 1
    ext i j
    simp [vecMulVec_apply, Matrix.mul_apply, mul_assoc]
  rw [e, det_one_add_replicateCol_mul_replicateRow, dotProduct_smul, star_dot]
  simp only [smul_eq_mul]
  norm_cast
  generalize √(nS f) = s at h0 h1 ⊢
  rw [← h1]
  field_simp
  ring

theorem vecMul_pM_apply (f r : β → ℂ) (j : β) :
    (r ᵥ* pM f) j = r j + ((1 / (1 + √(nS f)) : ℝ) : ℂ) * (∑ i, r i * f i) * conj (f j) := by
  unfold pM rk
  rw [vecMul_add, vecMul_one, vecMul_smul, vecMul_vecMulVec]
  simp [dotProduct, mul_assoc]

theorem sum_norm_sq_vecMul_pM (f r : β → ℂ) :
    ∑ j, ‖(r ᵥ* pM f) j‖ ^ 2 = ‖∑ i, r i * f i‖ ^ 2 + ∑ j, ‖r j‖ ^ 2 := by
  obtain ⟨h0, h1⟩ := sqrt_facts f
  have ht1 : (1 / (1 + √(nS f))) ^ 2 * (nS f - 1) + 2 * (1 / (1 + √(nS f))) = 1 := by
    generalize √(nS f) = s at h0 h1 ⊢
    rw [← h1]
    field_simp
    ring
  generalize ha : ∑ i, r i * f i = a
  generalize htt : 1 / (1 + √(nS f)) = t at ht1
  have hterm : ∀ j, ‖(r ᵥ* pM f) j‖ ^ 2 =
      ‖r j‖ ^ 2 + t ^ 2 * ‖a‖ ^ 2 * ‖f j‖ ^ 2 + 2 * t * (r j * f j * conj a).re := by
    intro j
    rw [vecMul_pM_apply, ha, htt, Complex.sq_norm, Complex.normSq_add, ← Complex.sq_norm (r j)]
    have e1 : Complex.normSq ((t : ℂ) * a * conj (f j)) = t ^ 2 * ‖a‖ ^ 2 * ‖f j‖ ^ 2 := by
      simp [Complex.normSq_eq_norm_sq, mul_pow]
    have e2 : r j * conj ((t : ℂ) * a * conj (f j)) = (t : ℂ) * (r j * f j * conj a) := by
      simp only [map_mul, Complex.conj_ofReal, Complex.conj_conj]
      ring
    rw [e1, e2, Complex.re_ofReal_mul]
    ring
  have hs : ∑ j, (r j * f j * conj a).re = ‖a‖ ^ 2 := by
    rw [← Complex.re_sum, ← Finset.sum_mul, ha, Complex.mul_conj, Complex.ofReal_re,
      Complex.normSq_eq_norm_sq]
  have hf : ∑ j, ‖f j‖ ^ 2 = nS f - 1 := by simp [nS]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hs, hf]
  linear_combination ‖a‖ ^ 2 * ht1

theorem lintegral_rows (d : ℕ) (P : Matrix β β ℂ) (hP : P.det ≠ 0)
    (H : (Fin d → β → ℂ) → ℝ≥0∞) (hH : Measurable H) :
    ∫⁻ C : Fin d → β → ℂ, H (fun k => C k ᵥ* P) =
      ENNReal.ofReal |((Complex.normSq P.det) ^ d)⁻¹| * ∫⁻ D, H D := by
  let T : (β → ℂ) →ₗ[ℝ] (β → ℂ) := (Matrix.toLin' Pᵀ).restrictScalars ℝ
  let L : (Fin d → β → ℂ) →ₗ[ℝ] (Fin d → β → ℂ) := LinearMap.pi fun k => T ∘ₗ LinearMap.proj k
  have hdT : LinearMap.det T = Complex.normSq P.det := by
    simp only [T]
    rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Matrix.det_transpose,
      Algebra.norm_complex_apply]
  have hdL : LinearMap.det L = (Complex.normSq P.det) ^ d := by
    simp only [L]
    rw [LinearMap.det_pi, Finset.prod_const, hdT]
    simp
  have hne : LinearMap.det L ≠ 0 := by
    rw [hdL]
    exact pow_ne_zero _ (Complex.normSq_pos.2 hP).ne'
  have hL : (fun C : Fin d → β → ℂ => fun k => C k ᵥ* P) = L := by
    funext C k
    simp [L, T, toLin'_apply, mulVec_transpose]
  have hLm : Measurable L := L.continuous_of_finiteDimensional.measurable
  haveI : (volume : Measure (β → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure (Fin d → β → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have e : ∫⁻ C : Fin d → β → ℂ, H (fun k => C k ᵥ* P) = ∫⁻ C, H (L C) := by
    rw [← hL]
  rw [e, ← lintegral_map hH hLm, Measure.map_linearMap_addHaar_eq_smul_addHaar _ hne,
    lintegral_smul_measure, hdL]
  rfl

theorem gram_eq {d : ℕ} (f : β → ℂ) (F : Matrix β (Fin d) ℂ) :
    (rM f * F)ᴴ * (rM f * F) =
      Fᴴ * F - ((1 / nS f : ℝ) : ℂ) • vecMulVec (Fᴴ *ᵥ f) (star f ᵥ* F) := by
  rw [conjTranspose_mul, rM_conjTranspose, Matrix.mul_assoc, ← Matrix.mul_assoc (rM f), rM_mul_rM,
    Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul]
  congr 2
  unfold rk
  rw [vecMulVec_mul, mul_vecMulVec]

theorem fsLevi_eq {d : ℕ} (f : β → ℂ) (F : Matrix β (Fin d) ℂ) :
    fsLevi f F = ((1 / nS f : ℝ) : ℂ) • ((rM f * F)ᴴ * (rM f * F))ᵀ := by
  have hS : ((nS f : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (nS_pos f).ne'
  rw [gram_eq]
  ext a c
  have hX : ∑ j, F j a * conj (F j c) = (Fᴴ * F) c a := by
    simp [Matrix.mul_apply, mul_comm]
  have hY : ∑ j, F j a * conj (f j) = (star f ᵥ* F) a := by
    simp [vecMul, dotProduct, mul_comm]
  have hZ : ∑ j, f j * conj (F j c) = (Fᴴ *ᵥ f) c := by
    simp [mulVec, dotProduct, mul_comm]
  have h1 : ((1 + ∑ j, ‖f j‖ ^ 2 : ℝ) : ℂ) = ((nS f : ℝ) : ℂ) := rfl
  simp only [fsLevi, of_apply, hX, hY, hZ, h1, Matrix.smul_apply, transpose_apply, Matrix.sub_apply,
    vecMulVec_apply, smul_eq_mul]
  push_cast
  field_simp

theorem lintegral_gauss_levi : ∀ (d : ℕ) (β : Type) [Fintype β] [DecidableEq β] (f : β → ℂ)
    (F : Matrix β (Fin d) ℂ),
    ∫⁻ C : Fin d → β → ℂ, gW d β C *
        ENNReal.ofReal (Real.exp (-∑ k, ‖∑ j, C k j * f j‖ ^ 2) * ‖(Matrix.of C * F).det‖ ^ 2) =
      ENNReal.ofReal (Real.pi ^ (d * Fintype.card β) * (d.factorial : ℝ) * (fsLevi f F).det.re) := by
  intro d β _ _ f F
  obtain ⟨h0, h1⟩ := sqrt_facts f
  have hSp := nS_pos f
  let G : Matrix β (Fin d) ℂ := rM f * F
  let H : (Fin d → β → ℂ) → ℝ≥0∞ := fun D =>
    gW d β D * ENNReal.ofReal (‖(Matrix.of D * G).det‖ ^ 2)
  have hH : Measurable H := by
    have c1 : Continuous fun D : Fin d → β → ℂ => Real.exp (-∑ k, ∑ j, ‖D k j‖ ^ 2) := by
      fun_prop
    have c2 : Continuous fun D : Fin d → β → ℂ => (Matrix.of D * G).det :=
      Continuous.matrix_det (Continuous.matrix_mul continuous_id continuous_const)
    exact (ENNReal.measurable_ofReal.comp c1.measurable).mul
      (ENNReal.measurable_ofReal.comp (c2.norm.pow 2).measurable)
  have hpt : ∀ C : Fin d → β → ℂ, gW d β C *
      ENNReal.ofReal (Real.exp (-∑ k, ‖∑ j, C k j * f j‖ ^ 2) * ‖(Matrix.of C * F).det‖ ^ 2) =
      H (fun k => C k ᵥ* pM f) := by
    intro C
    have hrow : Matrix.of (fun k => C k ᵥ* pM f) = Matrix.of C * pM f := by
      ext k j
      simp [vecMul, Matrix.mul_apply, dotProduct]
    have hdet : Matrix.of (fun k => C k ᵥ* pM f) * G = Matrix.of C * F := by
      rw [hrow, Matrix.mul_assoc]
      simp only [G]
      rw [← Matrix.mul_assoc (pM f), pM_mul_rM, Matrix.one_mul]
    simp only [H, gW]
    rw [hdet]
    simp_rw [sum_norm_sq_vecMul_pM]
    rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ← mul_assoc,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, Finset.sum_add_distrib]
    congr 3
    ring
  have hPd : (pM f).det ≠ 0 := by
    rw [det_pM]
    exact_mod_cast h0.ne'
  simp_rw [hpt]
  rw [lintegral_rows d (pM f) hPd H hH]
  have hI : ∫⁻ D, H D = ENNReal.ofReal (Real.pi ^ (d * Fintype.card β) * (d.factorial : ℝ) *
      (G.conjTranspose * G).det.re) := GlobalTheory.T.gaussian_det_square_integral d β G
  rw [hI, ← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1
  have hn : Complex.normSq (pM f).det = nS f := by
    rw [det_pM, Complex.normSq_ofReal, h1]
  have hL : (fsLevi f F).det.re = (1 / nS f) ^ d * (G.conjTranspose * G).det.re := by
    rw [fsLevi_eq, Matrix.det_smul, Matrix.det_transpose, Fintype.card_fin]
    simp only [G]
    rw [← Complex.ofReal_pow, Complex.re_ofReal_mul]
  rw [hn, hL, abs_of_pos (inv_pos.2 (pow_pos hSp d)), one_div, inv_pow]
  ring

end GlobalTheory.CompanionTheory.FSCrofton.GaussLevi
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussianDetLeviIntegralStatement
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussian_det_levi_integral : ∀ (d : ℕ) (β : Type) [Fintype β] [DecidableEq β] (f : β → ℂ) (F : Matrix β (Fin d) ℂ), ∫⁻ C : Fin d → β → ℂ, gW d β C * ENNReal.ofReal (Real.exp (-∑ k, ‖∑ j, C k j * f j‖ ^ 2) * ‖(Matrix.of C * F).det‖ ^ 2) = ENNReal.ofReal (Real.pi ^ (d * Fintype.card β) * (d.factorial : ℝ) * (fsLevi f F).det.re) := by
  first | exact @GlobalTheory.CompanionTheory.FSCrofton.GaussLevi.lintegral_gauss_levi | exact GlobalTheory.CompanionTheory.FSCrofton.GaussLevi.lintegral_gauss_levi | (intros; apply GlobalTheory.CompanionTheory.FSCrofton.GaussLevi.lintegral_gauss_levi <;> assumption)
end
