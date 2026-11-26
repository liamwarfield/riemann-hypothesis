module

public import Mathlib

@[expose] public section

/-!
# Fréchet Derivative of Multivariate Polynomial Evaluation

Proves that evaluation `x ↦ MvPolynomial.eval x g` of a complex multivariate polynomial
`g ∈ ℂ[X_i]_{i ∈ σ}` on a finite index type `σ` has Fréchet derivative
`∑ i, (eval z (pderiv i g)) • proj i` at every point `z : σ → ℂ`.
-/

open MvPolynomial in
theorem UpperTheory.Reformulated.B.FrechetDerivEvaluation.hasFDerivAt_eval.{u_1}
    {σ : Type u_1} [Fintype σ] (g : MvPolynomial σ ℂ) (z : σ → ℂ) :
    HasFDerivAt (fun x : σ → ℂ => eval x g)
      (∑ i : σ, eval z (pderiv i g) • (ContinuousLinearMap.proj i : (σ → ℂ) →L[ℂ] ℂ)) z := by
  classical
  induction g using MvPolynomial.induction_on with
  | C a =>
    simp only [eval_C]
    refine (hasFDerivAt_const (𝕜 := ℂ) a z).congr_fderiv ?_
    ext v
    simp
  | add p q hp hq =>
    have h := hp.add hq
    simp only [map_add (f := _)]
    refine h.congr_fderiv ?_
    ext v
    simp [add_mul, Finset.sum_add_distrib]
  | mul_X p n hp =>
    have h := hp.mul (hasFDerivAt_apply (𝕜 := ℂ) n z)
    simp only [map_mul, eval_X]
    refine HasFDerivAt.congr_fderiv h ?_
    ext v
    simp [Derivation.leibniz, pderiv_X, Pi.single_apply, Finset.mul_sum, mul_add,
      Finset.sum_add_distrib, apply_ite (eval z), mul_comm, mul_left_comm]
