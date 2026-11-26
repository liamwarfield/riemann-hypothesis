module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.IntegralityNearIdentity.EqOneOfNear

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.WeightedSumBis
open scoped ContDiff

namespace UpperTheory.Reformulated.B.weightedSumBis

theorem exists_eq_exp (f : ℝ → ℂ) (hc : Continuous f) (h0 : f 0 = 1) (hm : ∀ x y, f (x + y) = f x * f y) :
    ∃ c : ℂ, ∀ x : ℝ, f x = Complex.exp (c * x) := by
  set F : ℝ → ℂ := fun u => ∫ t in (0 : ℝ)..u, f t with hF
  have hFd : ∀ u, HasDerivAt F (f u) u := fun u =>
    (hc.integral_hasStrictDerivAt 0 u).hasDerivAt
  obtain ⟨a, ha⟩ : ∃ a, F a ≠ 0 := by
    by_contra h
    push Not at h
    have h1 : F = fun _ => 0 := funext h
    have h2 := hFd 0
    rw [h1, h0] at h2
    exact one_ne_zero (h2.unique (hasDerivAt_const _ _))
  have key : ∀ x, f x = (F (x + a) - F x) / F a := by
    intro x
    rw [eq_div_iff ha]
    have h1 : F (x + a) - F x = ∫ t in x..(x + a), f t :=
      intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _)
        (hc.intervalIntegrable _ _)
    have h2 : ∫ t in (0 : ℝ)..a, f (x + t) = ∫ t in x..(x + a), f t := by
      simp
    rw [h1, ← h2]
    simp only [hm, hF]
    rw [intervalIntegral.integral_const_mul]
  set c : ℂ := (f a - 1) / F a with hcdef
  have hfd : ∀ x, HasDerivAt f (c * f x) x := by
    intro x
    have h1 : HasDerivAt (fun y => (F (y + a) - F y) / F a) ((f (x + a) - f x) / F a) x :=
      (((hFd (x + a)).comp_add_const x a).sub (hFd x)).div_const _
    rw [← funext key] at h1
    convert h1 using 1
    rw [hm, hcdef]
    ring
  have hg : ∀ x : ℝ, HasDerivAt (fun y : ℝ => f y * Complex.exp (-c * y)) 0 x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => Complex.exp (-c * y)) (Complex.exp (-c * x) * (-c * 1)) x :=
      ((Complex.ofRealCLM.hasDerivAt (x := x)).const_mul (-c)).cexp
    have h2 := (hfd x).mul h1
    have h3 : c * f x * Complex.exp (-c * x) + f x * (Complex.exp (-c * x) * (-c * 1)) = 0 := by
      ring
    rw [h3] at h2
    exact h2
  refine ⟨c, fun x => ?_⟩
  have h := is_const_of_deriv_eq_zero (fun y => (hg y).differentiableAt)
    (fun y => (hg y).deriv) x 0
  simp only [h0, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at h
  rw [neg_mul, Complex.exp_neg] at h
  exact (mul_inv_eq_one₀ (Complex.exp_ne_zero _)).mp h

end UpperTheory.Reformulated.B.weightedSumBis
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ConjugateOfRoots
open scoped ContDiff

namespace UpperTheory.Reformulated.B.ConjugateOfRoots

theorem conj_of_roots {K : Type} [Field K] {n : ℕ} (d : Fin n → K) (hd : Function.Injective d) (N D : GL (Fin n) K)
    (hD : (D : Matrix (Fin n) (Fin n) K) = Matrix.diagonal d)
    (hN : ∀ i, (N : Matrix (Fin n) (Fin n) K).charpoly.IsRoot (d i)) : ∃ g : GL (Fin n) K, N = g * D * g⁻¹ := by
  have hv : ∀ i, ∃ v : Fin n → K, v ≠ 0 ∧
      (N : Matrix (Fin n) (Fin n) K).mulVec v = d i • v := by
    intro i
    have h := hN i
    rw [Polynomial.IsRoot.def, Matrix.eval_charpoly] at h
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
    refine ⟨v, hv0, ?_⟩
    rw [Matrix.sub_mulVec, sub_eq_zero] at hv
    rw [← hv]
    ext j
    simp [Matrix.mulVec_diagonal]
  choose v hv0 hv using hv
  have hli : LinearIndependent K v := by
    refine Module.End.eigenvectors_linearIndependent'
      (Matrix.toLin' (N : Matrix (Fin n) (Fin n) K)) d hd v fun i => ⟨?_, hv0 i⟩
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, hv i]
  have hP : IsUnit (Matrix.of v).transpose := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit]
    exact hli
  obtain ⟨g, hg⟩ := hP
  refine ⟨g, ?_⟩
  rw [eq_mul_inv_iff_mul_eq]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hg, hD]
  ext i j
  have h := congrFun (hv j) i
  rw [Matrix.mul_diagonal, Matrix.mul_apply]
  simpa [Matrix.mulVec, dotProduct, mul_comm] using h

end UpperTheory.Reformulated.B.ConjugateOfRoots
end

open scoped ContDiff

namespace UpperTheory.V.Lib.Small

theorem conj_of_roots {K : Type} [Field K] {n : ℕ} (d : Fin n → K) (hd : Function.Injective d) (N D : GL (Fin n) K)
    (hD : (D : Matrix (Fin n) (Fin n) K) = Matrix.diagonal d)
    (hN : ∀ i, (N : Matrix (Fin n) (Fin n) K).charpoly.IsRoot (d i)) : ∃ g : GL (Fin n) K, N = g * D * g⁻¹ :=
  _root_.UpperTheory.Reformulated.B.ConjugateOfRoots.conj_of_roots d hd N D hD hN

theorem exists_eq_exp (f : ℝ → ℂ) (hc : Continuous f) (h0 : f 0 = 1) (hm : ∀ x y, f (x + y) = f x * f y) :
    ∃ c : ℂ, ∀ x : ℝ, f x = Complex.exp (c * x) :=
  _root_.UpperTheory.Reformulated.B.weightedSumBis.exists_eq_exp f hc h0 hm

end UpperTheory.V.Lib.Small
