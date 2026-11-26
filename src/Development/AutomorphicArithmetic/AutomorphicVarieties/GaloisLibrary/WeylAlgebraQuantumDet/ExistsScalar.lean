module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CapCommuteRtInfGL
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.QdetRect

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.CoefDiff
open Matrix UpperTheory.V.Weyl

private theorem UpperTheory.V.Weyl.differentiable_eval_polynomial_entries (n : ℕ) (p : MvPolynomial (Fin n × Fin n) ℂ) :
    Differentiable ℂ (fun x : Fin n → Fin n → ℂ => MvPolynomial.eval (fun ab => x ab.1 ab.2) p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp only [MvPolynomial.eval_C]; fun_prop
  | add p q hp hq => simp only [map_add (f := _)]; exact hp.add hq
  | mul_X p ab hp =>
    simp only [map_mul, MvPolynomial.eval_X]
    exact hp.mul (by fun_prop)

theorem UpperTheory.V.Weyl.coefDiff :
    ∀ (n : ℕ) (Ξ : Pre n) (i j : Fin Ξ.d), Differentiable ℂ (Ξ.coef i j) := by
  intro n Ξ i j
  obtain ⟨p, hp⟩ := Ξ.poly i j
  have h : Ξ.coef i j = fun x : Fin n → Fin n → ℂ => MvPolynomial.eval (fun ab => x ab.1 ab.2) p := by
    funext x
    exact hp (Matrix.of x)
  rw [h]
  exact UpperTheory.V.Weyl.differentiable_eval_polynomial_entries n p
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.Curve
open Matrix UpperTheory.V.Weyl

theorem UpperTheory.V.Weyl.curve :
    ∀ (n : ℕ) (Ξ : Pre n) (c : ℂ → Matrix (Fin n) (Fin n) ℂ) (X : Matrix (Fin n) (Fin n) ℂ), c 0 = 1 →
      (∀ a b, HasDerivAt (fun t => c t a b) (X a b) 0) → ∀ i j, HasDerivAt (fun t => Ξ.mat (c t) i j) (Ξ.D X i j) 0 := by
  intro n Ξ c X h0 hd i j
  have hγ : HasDerivAt (fun t => (of.symm (c t) : Fin n → Fin n → ℂ)) (of.symm X) 0 := by
    rw [hasDerivAt_pi]
    intro a
    rw [hasDerivAt_pi]
    intro b
    exact hd a b
  have hγ0 : (of.symm (c 0) : Fin n → Fin n → ℂ) = oneM n := by
    rw [h0]
  have hf : HasFDerivAt (Ξ.coef i j) (fderiv ℂ (Ξ.coef i j) (oneM n))
      ((fun t => (of.symm (c t) : Fin n → Fin n → ℂ)) 0) := by
    show HasFDerivAt (Ξ.coef i j) (fderiv ℂ (Ξ.coef i j) (oneM n)) (of.symm (c 0))
    rw [hγ0]
    exact ((coefDiff n Ξ i j) (oneM n)).hasFDerivAt
  exact hf.comp_hasDerivAt (0 : ℂ) hγ
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.LineDeriv
open Matrix UpperTheory.V.Weyl

private theorem pre_coef_differentiableAt {n : ℕ} (Ξ : Pre n) (i j : Fin Ξ.d) (x : Fin n → Fin n → ℂ) :
    DifferentiableAt ℂ (Ξ.coef i j) x := by
  obtain ⟨p, hp⟩ := Ξ.poly i j
  have h : Ξ.coef i j = fun y => MvPolynomial.aeval (fun ab : Fin n × Fin n => y ab.1 ab.2) p := by
    funext y
    simp [Pre.coef, hp, MvPolynomial.coe_aeval_eq_eval]
  rw [h]
  exact (AnalyticAt.aeval_mvPolynomial (fun ab : Fin n × Fin n =>
    (((ContinuousLinearMap.proj ab.2 : (Fin n → ℂ) →L[ℂ] ℂ).comp
      (ContinuousLinearMap.proj ab.1 : (Fin n → Fin n → ℂ) →L[ℂ] (Fin n → ℂ))).analyticAt x)) p).differentiableAt

private theorem hasDerivAt_pre_mat_one_add_smul {n : ℕ} (Ξ : Pre n) (X : Matrix (Fin n) (Fin n) ℂ) (k j : Fin Ξ.d) :
    HasDerivAt (fun t : ℂ => Ξ.mat (of (oneM n + t • of.symm X)) k j) (Ξ.D X k j) 0 := by
  have hc : HasDerivAt (fun t : ℂ => oneM n + t • of.symm X) (of.symm X) 0 := by
    simpa using ((hasDerivAt_id (0:ℂ)).smul_const (of.symm X)).const_add (oneM n)
  have hf := (pre_coef_differentiableAt Ξ k j (oneM n + (0:ℂ) • of.symm X)).hasFDerivAt.comp_hasDerivAt (0:ℂ) hc
  simp only [zero_smul, add_zero] at hf
  exact hf

theorem UpperTheory.V.Weyl.adEq :
    ∀ (n : ℕ) (Ξ : Pre n) (P Z W : Matrix (Fin n) (Fin n) ℂ), P * Z = W * P → Ξ.mat P * Ξ.D Z = Ξ.D W * Ξ.mat P := by
  intro n Ξ P Z W h
  have key : ∀ t : ℂ, P * of (oneM n + t • of.symm Z) = of (oneM n + t • of.symm W) * P := by
    intro t
    change P * (1 + t • Z) = (1 + t • W) * P
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, h, mul_one, one_mul]
  ext i j
  have hZ : HasDerivAt (fun t : ℂ => (Ξ.mat P * Ξ.mat (of (oneM n + t • of.symm Z))) i j)
      ((Ξ.mat P * Ξ.D Z) i j) 0 := by
    simp only [Matrix.mul_apply]
    exact HasDerivAt.fun_sum fun k _ => (hasDerivAt_pre_mat_one_add_smul Ξ Z k j).const_mul _
  have hW : HasDerivAt (fun t : ℂ => (Ξ.mat (of (oneM n + t • of.symm W)) * Ξ.mat P) i j)
      ((Ξ.D W * Ξ.mat P) i j) 0 := by
    simp only [Matrix.mul_apply]
    exact HasDerivAt.fun_sum fun k _ => (hasDerivAt_pre_mat_one_add_smul Ξ W i k).mul_const _
  have hfun : (fun t : ℂ => (Ξ.mat P * Ξ.mat (of (oneM n + t • of.symm Z))) i j) =
      fun t : ℂ => (Ξ.mat (of (oneM n + t • of.symm W)) * Ξ.mat P) i j := by
    funext t
    rw [← map_mul, ← map_mul, key]
  rw [hfun] at hZ
  exact hZ.unique hW
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.GlRel
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.Bracket
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.InvCurve
open Matrix UpperTheory.V.Weyl

theorem UpperTheory.V.Weyl.invCurve :
    ∀ (n : ℕ) (a b : Fin n), ∃ P Q : ℂ → Matrix (Fin n) (Fin n) ℂ, P 0 = 1 ∧ Q 0 = 1 ∧ (∀ t, Q t * P t = 1) ∧
      ∀ i j, HasDerivAt (fun t => P t i j) (Matrix.single a b (1 : ℂ) i j) 0 ∧ HasDerivAt (fun t => Q t i j) (-Matrix.single a b (1 : ℂ) i j) 0 := by
  intro n a b
  by_cases hab : a = b
  · subst hab
    set E : Matrix (Fin n) (Fin n) ℂ := Matrix.single a a 1 with hEdef
    have hE : E * E = E := by
      rw [hEdef, Matrix.single_mul_single_same, one_mul]
    refine ⟨fun t => 1 + (Complex.exp t - 1) • E, fun t => 1 + (Complex.exp (-t) - 1) • E,
      by simp, by simp, ?_, ?_⟩
    · intro t
      have key : (Complex.exp (-t) - 1) + ((Complex.exp t - 1)
          + (Complex.exp (-t) - 1) * (Complex.exp t - 1)) = 0 := by
        have h1 : Complex.exp (-t) * Complex.exp t = 1 := by
          rw [← Complex.exp_add]; simp
        linear_combination h1
      simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_smul_comm, hE]
      rw [add_assoc, ← add_smul, ← add_smul, key, zero_smul, add_zero]
    · intro i j
      constructor
      · have h := (((Complex.hasDerivAt_exp 0).sub_const 1).mul_const (E i j)).const_add ((1 : Matrix (Fin n) (Fin n) ℂ) i j)
        simpa [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] using h
      · have h0 : HasDerivAt (fun t : ℂ => Complex.exp (-t)) (-1) 0 := by
          simpa using (hasDerivAt_neg (0 : ℂ)).cexp
        have h := ((h0.sub_const 1).mul_const (E i j)).const_add ((1 : Matrix (Fin n) (Fin n) ℂ) i j)
        simpa [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] using h
  · set E : Matrix (Fin n) (Fin n) ℂ := Matrix.single a b 1 with hEdef
    have hE : E * E = 0 := by
      rw [hEdef]
      simp [Ne.symm hab]
    refine ⟨fun t => 1 + t • E, fun t => 1 - t • E, by simp, by simp, ?_, ?_⟩
    · intro t
      simp only [sub_mul, mul_add, one_mul, mul_one, smul_mul_smul_comm, hE, smul_zero]
      abel
    · intro i j
      constructor
      · have h := ((hasDerivAt_id (0 : ℂ)).mul_const (E i j)).const_add ((1 : Matrix (Fin n) (Fin n) ℂ) i j)
        simpa [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] using h
      · have h := ((hasDerivAt_id (0 : ℂ)).mul_const (E i j)).const_sub ((1 : Matrix (Fin n) (Fin n) ℂ) i j)
        simpa [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] using h
end

open Matrix UpperTheory.V.Weyl

private theorem hasDerivAt_mul_mul_entry {n : ℕ} (P Q : ℂ → Matrix (Fin n) (Fin n) ℂ)
    (P' Q' Y : Matrix (Fin n) (Fin n) ℂ)
    (hP : ∀ i j, HasDerivAt (fun t => P t i j) (P' i j) 0)
    (hQ : ∀ i j, HasDerivAt (fun t => Q t i j) (Q' i j) 0) (p q : Fin n) :
    HasDerivAt (fun t => (P t * Y * Q t) p q) ((P' * Y * Q 0 + P 0 * Y * Q') p q) 0 := by
  have h : HasDerivAt (fun t => ∑ m, (∑ l, P t p l * Y l m) * Q t m q)
      (∑ m, ((∑ l, P' p l * Y l m) * Q 0 m q + (∑ l, P 0 p l * Y l m) * Q' m q)) 0 :=
    HasDerivAt.fun_sum fun m _ =>
      (HasDerivAt.fun_sum fun l _ => (hP p l).mul_const (Y l m)).mul (hQ m q)
  have e : (P' * Y * Q 0 + P 0 * Y * Q') p q =
      ∑ m, ((∑ l, P' p l * Y l m) * Q 0 m q + (∑ l, P 0 p l * Y l m) * Q' m q) := by
    rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply, ← Finset.sum_add_distrib]
    simp only [Matrix.mul_apply]
  have ef : (fun t => (P t * Y * Q t) p q) = fun t => ∑ m, (∑ l, P t p l * Y l m) * Q t m q := by
    funext t
    simp only [Matrix.mul_apply]
  rw [e, ef]
  exact h

private theorem pre_D_eq_sum_single {n : ℕ} (Ξ : Pre n) (M : Matrix (Fin n) (Fin n) ℂ) (i k : Fin Ξ.d) :
    Ξ.D M i k = ∑ p, ∑ q, M p q * Ξ.D (Matrix.single p q 1) i k := by
  have hM : M = ∑ p, ∑ q, M p q • Matrix.single p q (1 : ℂ) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single M]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  conv_lhs => rw [hM]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

theorem UpperTheory.V.Weyl.bracket :
    ∀ (n : ℕ) (Ξ : Pre n) (a b : Fin n) (Y : Matrix (Fin n) (Fin n) ℂ),
      Ξ.E a b * Ξ.D Y - Ξ.D Y * Ξ.E a b = Ξ.D (Matrix.single a b 1 * Y - Y * Matrix.single a b 1) := by
  intro n Ξ a b Y
  obtain ⟨P, Q, hP0, hQ0, hQP, hd⟩ := invCurve n a b
  set s : Matrix (Fin n) (Fin n) ℂ := Matrix.single a b 1 with hs
  set c : Matrix (Fin n) (Fin n) ℂ := s * Y - Y * s with hc
  have hE : ∀ t, Ξ.mat (P t) * Ξ.D Y = Ξ.D (P t * Y * Q t) * Ξ.mat (P t) := fun t =>
    adEq n Ξ (P t) Y (P t * Y * Q t) (by rw [Matrix.mul_assoc (P t * Y), hQP t, Matrix.mul_one])
  have hmat := curve n Ξ P s hP0 (fun i j => (hd i j).1)
  have hM : ∀ p q, HasDerivAt (fun t => (P t * Y * Q t) p q) (c p q) 0 := by
    intro p q
    have h := hasDerivAt_mul_mul_entry P Q s (-s) Y
      (fun i j => (hd i j).1) (fun i j => by simpa using (hd i j).2) p q
    simpa [hP0, hQ0, hc, sub_eq_add_neg, Matrix.mul_neg] using h
  have hdD : ∀ i k, HasDerivAt (fun t => Ξ.D (P t * Y * Q t) i k) (Ξ.D c i k) 0 := by
    intro i k
    have h : HasDerivAt (fun t => ∑ p, ∑ q, (P t * Y * Q t) p q * Ξ.D (Matrix.single p q 1) i k)
        (∑ p, ∑ q, c p q * Ξ.D (Matrix.single p q 1) i k) 0 :=
      HasDerivAt.fun_sum fun p _ => HasDerivAt.fun_sum fun q _ => (hM p q).mul_const _
    rw [pre_D_eq_sum_single Ξ c i k]
    convert h using 1
    funext t
    exact pre_D_eq_sum_single Ξ _ i k
  ext i j
  have hL : HasDerivAt (fun t => (Ξ.mat (P t) * Ξ.D Y) i j)
      (∑ k, Ξ.D s i k * Ξ.D Y k j) 0 := by
    simp only [Matrix.mul_apply]
    exact HasDerivAt.fun_sum fun k _ => (hmat i k).mul_const _
  have hR : HasDerivAt (fun t => (Ξ.D (P t * Y * Q t) * Ξ.mat (P t)) i j)
      (∑ k, (Ξ.D c i k * Ξ.mat (P 0) k j + Ξ.D (P 0 * Y * Q 0) i k * Ξ.D s k j)) 0 := by
    simp only [Matrix.mul_apply]
    exact HasDerivAt.fun_sum fun k _ => (hdD i k).mul (hmat k j)
  have hfun : (fun t => (Ξ.mat (P t) * Ξ.D Y) i j) =
      fun t => (Ξ.D (P t * Y * Q t) * Ξ.mat (P t)) i j :=
    funext fun t => by rw [hE t]
  rw [hfun] at hL
  have hu := hL.unique hR
  simp only [hP0, hQ0, Matrix.mul_one, Matrix.one_mul, map_one, Finset.sum_add_distrib] at hu
  simp only [Matrix.sub_apply, Pre.E, Matrix.mul_apply]
  rw [hu]
  simp [Matrix.one_apply, s]
end

open Matrix UpperTheory.V.Weyl

theorem UpperTheory.V.Weyl.glRel :
    ∀ (n : ℕ) (Ξ : Pre n), Formalism.REAL.GlRel Ξ.E := by
  intro n Ξ a b c d
  have h := UpperTheory.V.Weyl.bracket n Ξ a b (Matrix.single c d 1)
  have h1 : Ξ.D (Matrix.single a b (1:ℂ) * Matrix.single c d 1) = if b = c then Ξ.E a d else 0 := by
    split_ifs with hbc
    · subst hbc; rw [Matrix.single_mul_single_same, mul_one]; rfl
    · rw [Matrix.single_mul_single_of_ne _ _ _ _ hbc, map_zero]
  have h2 : Ξ.D (Matrix.single c d (1:ℂ) * Matrix.single a b 1) = if d = a then Ξ.E c b else 0 := by
    split_ifs with hbc
    · subst hbc; rw [Matrix.single_mul_single_same, mul_one]; rfl
    · rw [Matrix.single_mul_single_of_ne _ _ _ _ hbc, map_zero]
  rw [map_sub, h1, h2] at h
  exact h
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.Scalar
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.QdetComm
open Matrix UpperTheory.V.Weyl

theorem UpperTheory.V.Weyl.qdetComm :
    ∀ (n : ℕ) (Ξ : Pre n) (u : ℂ) (y : Matrix (Fin n) (Fin n) ℂ), IsUnit y →
      Ξ.mat y * Formalism.REAL.qdet Ξ.E u = Formalism.REAL.qdet Ξ.E u * Ξ.mat y := by
  intro n Ξ u y hy
  obtain ⟨Q, hQ⟩ := hy.exists_left_inv
  have hW : ∀ a b : Fin n, y * Matrix.single a b (1 : ℂ) * Q =
      ∑ c, ∑ d, (y c a * Q b d) • Matrix.single c d (1 : ℂ) := by
    intro a b
    rw [Matrix.matrix_eq_sum_single (y * Matrix.single a b (1 : ℂ) * Q)]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [Matrix.smul_single]
    congr 1
    simp [Matrix.mul_apply, Matrix.single_apply, ite_and]
  have h : ∀ a b : Fin n, Ξ.mat y * Ξ.E a b =
      (∑ c, ∑ d, (y c a * Q b d) • Ξ.E c d) * Ξ.mat y := by
    intro a b
    have h1 := UpperTheory.V.Weyl.adEq n Ξ y (Matrix.single a b 1) (y * Matrix.single a b (1 : ℂ) * Q)
      (by rw [mul_assoc, hQ, mul_one])
    rw [hW] at h1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul] at h1
    exact h1
  rw [GlobalTheory.CapAdInv.qdet_semiconj _ _ _ h u,
    GlobalTheory.CapAdInv.qdet_ad _ (UpperTheory.V.Weyl.glRel n Ξ) y Q hQ u]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.PreSub
open Matrix UpperTheory.V.Weyl

theorem UpperTheory.V.Weyl.preSub :
    ∀ (n : ℕ) (Ξ : Pre n) (S : Submodule ℂ (Fin Ξ.d → ℂ)), (∀ y, ∀ v ∈ S, Ξ.mat y *ᵥ v ∈ S) →
      ∃ (Ξ' : Pre n) (A : Matrix (Fin Ξ.d) (Fin Ξ'.d) ℂ) (B : Matrix (Fin Ξ'.d) (Fin Ξ.d) ℂ),
        Ξ'.d = Module.finrank ℂ S ∧ B * A = 1 ∧ (∀ w, A *ᵥ w ∈ S) ∧ ∀ X, Ξ.D X * A = A * Ξ'.D X := by
  intro n Ξ S hS
  obtain ⟨d', A, B, ρ', hd, hBA, hA, hρ, hcomm⟩ :=
    UpperTheory.V.Weyl.subMat (Matrix (Fin n) (Fin n) ℂ) Ξ.d Ξ.mat S hS
  have hpoly : ∀ i j, ∃ p : MvPolynomial (Fin n × Fin n) ℂ, ∀ g,
      ρ' g i j = MvPolynomial.eval (fun ab => g ab.1 ab.2) p := by
    choose p hp using Ξ.poly
    intro i j
    refine ⟨∑ l, (∑ k, MvPolynomial.C (B i k) * p k l) * MvPolynomial.C (A l j), fun g => ?_⟩
    rw [hρ]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mul_apply, map_sum, map_mul, MvPolynomial.eval_C, hp]
  let Ξ' : Pre n := ⟨d', ρ', hpoly⟩
  refine ⟨Ξ', A, B, hd, hBA, hA, fun X => ?_⟩
  have h0 : (fun t : ℂ => (1 : Matrix (Fin n) (Fin n) ℂ) + t • X) 0 = 1 := by simp
  have hc : ∀ a b, HasDerivAt (fun t : ℂ => ((1 : Matrix (Fin n) (Fin n) ℂ) + t • X) a b) (X a b) 0 := by
    intro a b
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const (X a b)).const_add ((1 : Matrix (Fin n) (Fin n) ℂ) a b)
  have h1 := UpperTheory.V.Weyl.curve n Ξ _ X h0 hc
  have h2 := UpperTheory.V.Weyl.curve n Ξ' _ X h0 hc
  ext i j
  have e1 : HasDerivAt (fun t : ℂ => (Ξ.mat (1 + t • X) * A) i j) ((Ξ.D X * A) i j) 0 := by
    simp only [Matrix.mul_apply]
    exact HasDerivAt.fun_sum fun k _ => (h1 i k).mul_const (A k j)
  have e2 : HasDerivAt (fun t : ℂ => (A * ρ' (1 + t • X)) i j) ((A * Ξ'.D X) i j) 0 := by
    simp only [Matrix.mul_apply]
    exact HasDerivAt.fun_sum fun k _ => (h2 k j).const_mul (A i k)
  simp only [hcomm] at e1
  exact e1.unique e2
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.TopLie
open Matrix UpperTheory.V.Weyl

private theorem UpperTheory.V.Weyl.top_weight_lie_action (n : ℕ) (Ξ : Pre n) (ν : Fin n → ℕ) (v : Fin Ξ.d → ℂ)
    (h : Ξ.IsTop ν v) (a b : Fin n) (hab : a ≤ b) (f : ℂ → ℂ) (f' : ℂ) (hf : HasDerivAt f f' 0)
    (hfe : ∀ t : ℂ, ∏ k, ((1 : Matrix (Fin n) (Fin n) ℂ) + t • single a b (1 : ℂ)) k k ^ ν k = f t) :
    Ξ.E a b *ᵥ v = f' • v := by
  have hc := UpperTheory.V.Weyl.curve n Ξ (fun t => 1 + t • single a b (1 : ℂ)) (single a b 1) (by simp) (by
    intro i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const (single a b (1 : ℂ) i j)).const_add
      ((1 : Matrix (Fin n) (Fin n) ℂ) i j))
  funext i
  have h1 : HasDerivAt (fun t : ℂ => (Ξ.mat (1 + t • single a b (1 : ℂ)) *ᵥ v) i) ((Ξ.E a b *ᵥ v) i) 0 := by
    simp only [Matrix.mulVec, dotProduct]
    exact HasDerivAt.fun_sum fun j _ => (hc i j).mul_const (v j)
  have h2 : (fun t : ℂ => (Ξ.mat (1 + t • single a b (1 : ℂ)) *ᵥ v) i) = fun t => f t * v i := by
    funext t
    rw [h _ ?_, hfe]
    · rfl
    · intro p q hpq
      have : ¬ (a = p ∧ b = q) := by
        rintro ⟨rfl, rfl⟩
        exact absurd hab (not_le.mpr hpq)
      simp [Matrix.one_apply_ne hpq.ne', Matrix.single_apply, this]
  rw [h2] at h1
  exact h1.unique (hf.mul_const (v i))

theorem UpperTheory.V.Weyl.topLie :
    ∀ (n : ℕ) (Ξ : Pre n) (ν : Fin n → ℕ) (v : Fin Ξ.d → ℂ), Ξ.IsTop ν v →
      (∀ a, Ξ.E a a *ᵥ v = (ν a : ℂ) • v) ∧ ∀ a b, a < b → Ξ.E a b *ᵥ v = 0 := by
  intro n Ξ ν v h
  refine ⟨fun a => ?_, fun a b hab => ?_⟩
  · refine UpperTheory.V.Weyl.top_weight_lie_action n Ξ ν v h a a le_rfl (fun t => (1 + t) ^ ν a) _ ?_ ?_
    · simpa using ((hasDerivAt_id (0 : ℂ)).const_add 1).fun_pow (ν a)
    · intro t
      rw [Finset.prod_eq_single a]
      · simp
      · intro k _ hk
        simp [Matrix.single_apply, hk.symm]
      · simp
  · have := UpperTheory.V.Weyl.top_weight_lie_action n Ξ ν v h a b hab.le (fun _ => 1) 0 (hasDerivAt_const _ _) (by
      intro t
      refine Finset.prod_eq_one fun k _ => ?_
      have : ¬ (a = k ∧ b = k) := by
        rintro ⟨rfl, rfl⟩
        exact lt_irrefl _ hab
      simp [Matrix.single_apply, this])
    simpa using this
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.QdetHW
open Matrix UpperTheory.V.Weyl

open Formalism.REAL in
private theorem UpperTheory.V.Weyl.map_quantum_determinant {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (φ : A →ₐ[ℂ] B) {n : ℕ}
    (X : Fin n → Fin n → A) (u : ℂ) : φ (qdet X u) = qdet (fun a b => φ (X a b)) u := by
  have hT : ∀ v a b, φ (Tm X v a b) = Tm (fun a b => φ (X a b)) v a b := fun v a b => by
    unfold Tm
    split_ifs <;> simp
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [qdet, qminor, map_sum, map_mul, map_intCast, map_list_prod, List.map_ofFn, Function.comp_def, hT]

theorem UpperTheory.V.Weyl.qdetHW :
    ∀ (n d : ℕ) (E : Fin n → Fin n → Matrix (Fin d) (Fin d) ℂ) (ν : Fin n → ℂ) (v : Fin d → ℂ), Formalism.REAL.GlRel E →
      (∀ a, E a a *ᵥ v = ν a • v) → (∀ a b, a < b → E a b *ᵥ v = 0) →
      ∀ u : ℂ, Formalism.REAL.qdet E u *ᵥ v = (∏ k : Fin n, (u - (k : ℂ) + ν k)) • v := by
  intro n d E ν v hgl h1 h2 u
  let φ : Matrix (Fin d) (Fin d) ℂ →ₐ[ℂ] Module.End ℂ (Fin d → ℂ) :=
    (Matrix.toLinAlgEquiv' : Matrix (Fin d) (Fin d) ℂ ≃ₐ[ℂ] _).toAlgHom
  have hφ : ∀ M w, φ M w = M *ᵥ w := fun M w => Matrix.toLinAlgEquiv'_apply M w
  have hgl' : Formalism.REAL.GlRel (fun a b => φ (E a b)) := by
    intro a b c e
    have := congrArg φ (hgl a b c e)
    simpa only [map_sub, map_mul, apply_ite φ, map_zero] using this
  have hw : Formalism.REAL.IsHW (fun a b => φ (E a b)) ν v :=
    ⟨fun a => (hφ _ _).trans (h1 a), fun a b hab => (hφ _ _).trans (h2 a b hab)⟩
  rw [← hφ, UpperTheory.V.Weyl.map_quantum_determinant]
  exact Formalism.REAL.qDetHW _ n _ ν v hgl' hw u
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.CommAll
open Matrix UpperTheory.V.Weyl

theorem UpperTheory.V.Weyl.commAll :
    ∀ (n : ℕ) (Ξ : Pre n) (Z : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ), (∀ y, IsUnit y → Ξ.mat y * Z = Z * Ξ.mat y) →
      ∀ y, Ξ.mat y * Z = Z * Ξ.mat y := by
  intro n Ξ Z hZ y
  choose P hP using Ξ.poly
  let Q : Fin Ξ.d → Fin Ξ.d → MvPolynomial (Fin n × Fin n) ℂ := fun i j =>
    ∑ l, P i l * MvPolynomial.C (Z l j) - ∑ l, MvPolynomial.C (Z i l) * P l j
  have hent : ∀ (g : Matrix (Fin n) (Fin n) ℂ) i j,
      (Ξ.mat g * Z - Z * Ξ.mat g) i j = MvPolynomial.eval (fun ab => g ab.1 ab.2) (Q i j) := by
    intro g i j
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Q, Matrix.mul_apply, hP, map_sum, mul_comm]
  rw [← sub_eq_zero]
  ext i j
  rw [hent, Matrix.zero_apply]
  have hQ : Q i j = 0 := MvPolynomial.eq_of_eval_eq_on_gl (fun g => by
    rw [← hent, hZ (g : Matrix (Fin n) (Fin n) ℂ) g.isUnit, sub_self, Matrix.zero_apply, map_zero])
  rw [hQ, map_zero]
end

open Matrix UpperTheory.V.Weyl

theorem UpperTheory.V.Weyl.scalar :
    ∀ (n : ℕ) (Ξ : Pre n) (ν : Fin n → ℕ) (v : Fin Ξ.d → ℂ), v ≠ 0 → Ξ.IsTop ν v →
      ∃ Ξ' : Pre n, 0 < Ξ'.d ∧ Ξ'.d ≤ Ξ.d ∧ Ξ'.HasWt fun k => (ν k : ℂ) := by
  intro n Ξ ν v hv htop
  let S : Submodule ℂ (Fin Ξ.d → ℂ) :=
    Submodule.span ℂ (Set.range fun y : Matrix (Fin n) (Fin n) ℂ => Ξ.mat y *ᵥ v)
  have hS : ∀ y, ∀ w ∈ S, Ξ.mat y *ᵥ w ∈ S := by
    intro y w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, rfl⟩ := hx
      rw [Matrix.mulVec_mulVec, ← map_mul]
      exact Submodule.subset_span ⟨y * z, rfl⟩
    | zero => simp
    | add x z _ _ hx hz =>
      rw [Matrix.mulVec_add]
      exact S.add_mem hx hz
    | smul a x _ hx =>
      rw [Matrix.mulVec_smul]
      exact S.smul_mem a hx
  have hvS : v ∈ S := by
    have h : Ξ.mat 1 *ᵥ v ∈ S := Submodule.subset_span ⟨1, rfl⟩
    simpa using h
  obtain ⟨Ξ', A, B, hd, hBA, hA, hD⟩ := preSub n Ξ S hS
  obtain ⟨hdiag, hup⟩ := topLie n Ξ ν v htop
  refine ⟨Ξ', ?_, ?_, fun u => ?_⟩
  · rw [hd]
    exact Module.finrank_pos_iff_exists_ne_zero.mpr
      ⟨⟨v, hvS⟩, fun h => hv (congrArg Subtype.val h)⟩
  · rw [hd]
    simpa using Submodule.finrank_le S
  · set c : ℂ := ∏ k : Fin n, (u - ((k : ℕ) : ℂ) + (ν k : ℂ)) with hc
    have hQv : Formalism.REAL.qdet Ξ.E u *ᵥ v = c • v :=
      qdetHW n Ξ.d Ξ.E (fun k => (ν k : ℂ)) v (glRel n Ξ) hdiag hup u
    have hcomm : ∀ y, Ξ.mat y * Formalism.REAL.qdet Ξ.E u = Formalism.REAL.qdet Ξ.E u * Ξ.mat y :=
      commAll n Ξ _ (fun y hy => qdetComm n Ξ u y hy)
    have hQS : ∀ w ∈ S, Formalism.REAL.qdet Ξ.E u *ᵥ w = c • w := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨y, rfl⟩ := hx
        rw [Matrix.mulVec_mulVec, ← hcomm y, ← Matrix.mulVec_mulVec, hQv, Matrix.mulVec_smul]
      | zero => simp
      | add x z _ _ hx hz => rw [Matrix.mulVec_add, hx, hz, smul_add]
      | smul a x _ hx => rw [Matrix.mulVec_smul, hx, smul_comm]
    have hR := qdetRect n Ξ.d Ξ'.d Ξ.E Ξ'.E A (fun a b => hD _) u
    have hcA : Formalism.REAL.qdet Ξ.E u * A = c • A := by
      refine Matrix.toLin'.injective (LinearMap.ext fun w => ?_)
      simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, hQS _ (hA w), Matrix.smul_mulVec]
    show Formalism.REAL.qdet Ξ'.E u = c • 1
    calc Formalism.REAL.qdet Ξ'.E u = (B * A) * Formalism.REAL.qdet Ξ'.E u := by rw [hBA, Matrix.one_mul]
      _ = B * (Formalism.REAL.qdet Ξ.E u * A) := by rw [Matrix.mul_assoc, hR]
      _ = c • 1 := by rw [hcA, Matrix.mul_smul, hBA]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.TopPol
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.MinorRtr
open Matrix UpperTheory.V.Weyl

private theorem prod_fin_castLE_eq_prod_le {M : Type*} [CommMonoid M] {n : ℕ} (k : Fin n) (f : Fin n → M) :
    ∏ l : Fin ((k : ℕ) + 1), f (Fin.castLE k.isLt l) = ∏ i : Fin n with i ≤ k, f i := by
  apply Finset.prod_bij (fun l _ => Fin.castLE k.isLt l)
  · intro l _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_iff_val_le_val, Fin.coe_castLE]
    omega
  · intro a _ b _ h
    exact Fin.castLE_injective _ h
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_iff_val_le_val] at hi
    exact ⟨⟨i.val, by omega⟩, Finset.mem_univ _, Fin.ext (by simp)⟩
  · intro _ _
    rfl

private theorem sum_fin_castLE_eq_sum_le {M : Type*} [AddCommMonoid M] {n : ℕ} (k : Fin n) (f : Fin n → M) :
    ∑ l : Fin ((k : ℕ) + 1), f (Fin.castLE k.isLt l) = ∑ i : Fin n with i ≤ k, f i := by
  apply Finset.sum_bij (fun l _ => Fin.castLE k.isLt l)
  · intro l _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_iff_val_le_val, Fin.coe_castLE]
    omega
  · intro a _ b _ h
    exact Fin.castLE_injective _ h
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_iff_val_le_val] at hi
    exact ⟨⟨i.val, by omega⟩, Finset.mem_univ _, Fin.ext (by simp)⟩
  · intro _ _
    rfl

theorem UpperTheory.V.Weyl.minorRtr :
    ∀ (n : ℕ) (k : Fin n) (b : Matrix (Fin n) (Fin n) ℂ), (∀ i j, j < i → b i j = 0) →
      rtr b (minor k) = (∏ i : Fin n with i ≤ k, b i i) • minor k := by
  intro n k b hb
  have hmat : (rtr b).mapMatrix (Matrix.of fun i j : Fin ((k : ℕ) + 1) =>
        (MvPolynomial.X (Fin.castLE k.isLt i, Fin.castLE k.isLt j) : Pol n)) =
      (Matrix.of fun i j : Fin ((k : ℕ) + 1) =>
        (MvPolynomial.X (Fin.castLE k.isLt i, Fin.castLE k.isLt j) : Pol n)) *
      (Matrix.of fun i j : Fin ((k : ℕ) + 1) => b (Fin.castLE k.isLt i) (Fin.castLE k.isLt j)).map
        (MvPolynomial.C : ℂ →+* Pol n) := by
    refine Matrix.ext fun i j => ?_
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.mul_apply, rtr,
      MvPolynomial.aeval_X]
    rw [sum_fin_castLE_eq_sum_le k (fun m => MvPolynomial.X (Fin.castLE k.isLt i, m) *
      MvPolynomial.C (b m (Fin.castLE k.isLt j)))]
    symm
    apply Finset.sum_filter_of_ne
    intro m _ hm
    by_contra hmk
    apply hm
    rw [hb m (Fin.castLE k.isLt j) ?_, map_zero, mul_zero]
    simp only [not_le] at hmk
    rw [Fin.lt_iff_val_lt_val] at hmk ⊢
    simp only [Fin.coe_castLE]
    omega
  have hup : (Matrix.of fun i j : Fin ((k : ℕ) + 1) =>
      b (Fin.castLE k.isLt i) (Fin.castLE k.isLt j)).det =
      ∏ i : Fin n with i ≤ k, b i i := by
    rw [Matrix.det_of_upperTriangular, ← prod_fin_castLE_eq_prod_le k (fun i => b i i)]
    · rfl
    · intro i j hij
      simp only [Matrix.of_apply]
      apply hb
      rw [Fin.lt_iff_val_lt_val] at hij ⊢
      simpa using hij
  have hC : ((Matrix.of fun i j : Fin ((k : ℕ) + 1) =>
      b (Fin.castLE k.isLt i) (Fin.castLE k.isLt j)).map (MvPolynomial.C : ℂ →+* Pol n)).det =
      MvPolynomial.C (∏ i : Fin n with i ≤ k, b i i) := by
    rw [← hup, RingHom.map_det]
    rfl
  unfold minor
  rw [AlgHom.map_det, hmat, Matrix.det_mul, hC, MvPolynomial.smul_eq_C_mul, mul_comm]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.MinorDeg
open Matrix UpperTheory.V.Weyl

theorem UpperTheory.V.Weyl.minorDeg :
    ∀ (n : ℕ) (k : Fin n), minor k ≠ 0 ∧ (minor k).totalDegree ≤ (k : ℕ) + 1 := by
  intro n k
  constructor
  · intro h
    have h0 := congrArg
      (MvPolynomial.eval (fun ab : Fin n × Fin n => if ab.1 = ab.2 then (1 : ℂ) else 0)) h
    rw [minor, RingHom.map_det, map_zero] at h0
    rw [show (RingHom.mapMatrix _) _ = (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) from ?_] at h0
    · simp at h0
    · ext i j
      simp [Matrix.one_apply, Fin.castLE_inj]
  · rw [minor, Matrix.det_apply]
    refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun σ _ => ?_)
    rw [Units.smul_def, ← Int.cast_smul_eq_zsmul ℂ]
    refine (MvPolynomial.totalDegree_smul_le _ _).trans ?_
    refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
    simp [MvPolynomial.totalDegree_X]
end

open Matrix UpperTheory.V.Weyl

theorem UpperTheory.V.Weyl.topPol :
    ∀ (n : ℕ) (ν : Fin n → ℕ), Antitone ν → ∀ H : ℕ, (∀ k, ν k ≤ H) → ∃ f : Pol n, f ≠ 0 ∧ f.totalDegree ≤ n * H ∧
      ∀ b : Matrix (Fin n) (Fin n) ℂ, (∀ i j, j < i → b i j = 0) → rtr b f = (∏ k, b k k ^ ν k) • f := by
  intro n ν hν H hH
  classical
  have hmem : ∀ (h : ℕ) (hs : (Finset.univ.filter (fun i : Fin n => h < ν i)).Nonempty) (i : Fin n),
      i ∈ Finset.univ.filter (fun i : Fin n => h < ν i) ↔ i ≤ (Finset.univ.filter (fun i : Fin n => h < ν i)).max' hs := by
    intro h hs i
    constructor
    · intro hi
      exact Finset.le_max' _ _ hi
    · intro hi
      have hm := Finset.max'_mem _ hs
      rw [Finset.mem_filter] at hm ⊢
      exact ⟨Finset.mem_univ _, lt_of_lt_of_le hm.2 (hν hi)⟩
  obtain ⟨g, hg1, hg2, hg3⟩ : ∃ g : ℕ → Pol n, (∀ h, g h ≠ 0) ∧ (∀ h, (g h).totalDegree ≤ n) ∧
      ∀ b : Matrix (Fin n) (Fin n) ℂ, (∀ i j, j < i → b i j = 0) → ∀ h,
        rtr b (g h) = (∏ i ∈ Finset.univ.filter (fun i : Fin n => h < ν i), b i i) • g h := by
    refine ⟨fun h => if hs : (Finset.univ.filter (fun i : Fin n => h < ν i)).Nonempty then
      minor ((Finset.univ.filter (fun i : Fin n => h < ν i)).max' hs) else 1, ?_, ?_, ?_⟩
    · intro h
      by_cases hs : (Finset.univ.filter (fun i : Fin n => h < ν i)).Nonempty
      · simp only [dite_eq_left hs]
        exact (minorDeg n _).1
      · simp only [dite_eq_right hs]
        exact one_ne_zero
    · intro h
      by_cases hs : (Finset.univ.filter (fun i : Fin n => h < ν i)).Nonempty
      · simp only [dite_eq_left hs]
        have h1 := (minorDeg n ((Finset.univ.filter (fun i : Fin n => h < ν i)).max' hs)).2
        have h2 := ((Finset.univ.filter (fun i : Fin n => h < ν i)).max' hs).isLt
        omega
      · simp only [dite_eq_right hs, MvPolynomial.totalDegree_one]
        exact Nat.zero_le _
    · intro b hb h
      by_cases hs : (Finset.univ.filter (fun i : Fin n => h < ν i)).Nonempty
      · simp only [dite_eq_left hs]
        rw [minorRtr n _ b hb]
        congr 1
        apply Finset.prod_congr _ (fun _ _ => rfl)
        ext i
        rw [hmem h hs i, Finset.mem_filter]
        simp
      · simp only [dite_eq_right hs]
        rw [Finset.not_nonempty_iff_eq_empty.mp hs]
        simp
  refine ⟨∏ h ∈ Finset.range H, g h, ?_, ?_, ?_⟩
  · exact Finset.prod_ne_zero_iff.mpr (fun h _ => hg1 h)
  · calc (∏ h ∈ Finset.range H, g h).totalDegree ≤ ∑ h ∈ Finset.range H, (g h).totalDegree :=
          MvPolynomial.totalDegree_finsetProd _ _
      _ ≤ ∑ h ∈ Finset.range H, n := Finset.sum_le_sum (fun h _ => hg2 h)
      _ = n * H := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_comm]
  · intro b hb
    have key : ∏ h ∈ Finset.range H, ∏ i ∈ Finset.univ.filter (fun i : Fin n => h < ν i), b i i =
        ∏ k, b k k ^ ν k := by
      calc ∏ h ∈ Finset.range H, ∏ i ∈ Finset.univ.filter (fun i : Fin n => h < ν i), b i i
          = ∏ h ∈ Finset.range H, ∏ i, (if h < ν i then b i i else 1) := by
            refine Finset.prod_congr rfl (fun h _ => ?_)
            rw [Finset.prod_filter]
        _ = ∏ i, ∏ h ∈ Finset.range H, (if h < ν i then b i i else 1) := Finset.prod_comm
        _ = ∏ k, b k k ^ ν k := by
            refine Finset.prod_congr rfl (fun i _ => ?_)
            rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
            congr 1
            have hf : (Finset.range H).filter (fun h => h < ν i) = Finset.range (ν i) := by
              ext h
              simp only [Finset.mem_filter, Finset.mem_range]
              have := hH i
              omega
            rw [hf, Finset.card_range]
    rw [map_prod, Finset.prod_congr rfl (fun h _ => hg3 b hb h), ← key]
    simp only [Algebra.smul_def, map_prod, Finset.prod_mul_distrib]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.PolPre
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.RtrPoly
open Matrix UpperTheory.V.Weyl

theorem UpperTheory.V.Weyl.rtrPoly :
    ∀ (n : ℕ) (f : Pol n) (φ : Pol n →ₗ[ℂ] ℂ), ∃ p : Pol n, ∀ g : Matrix (Fin n) (Fin n) ℂ,
      φ (rtr g f) = MvPolynomial.eval (fun ab => g ab.1 ab.2) p := by
  intro n f
  induction f using MvPolynomial.induction_on with
  | C a =>
    intro φ
    refine ⟨MvPolynomial.C (φ (MvPolynomial.C a)), fun g => ?_⟩
    have hc := (rtr g).commutes a
    rw [MvPolynomial.algebraMap_eq] at hc
    rw [hc, MvPolynomial.eval_C]
  | add p q hp hq =>
    intro φ
    obtain ⟨p1, h1⟩ := hp φ
    obtain ⟨p2, h2⟩ := hq φ
    exact ⟨p1 + p2, fun g => by rw [map_add (f := _), map_add (f := _), h1, h2, map_add (f := _)]⟩
  | mul_X p ij hp =>
    intro φ
    choose P hP using fun k : Fin n =>
      hp (φ.comp (LinearMap.mulRight ℂ (MvPolynomial.X (ij.1, k) : Pol n)))
    refine ⟨∑ k, MvPolynomial.X (k, ij.2) * P k, fun g => ?_⟩
    have hX : rtr g (MvPolynomial.X ij : Pol n)
        = ∑ k, (MvPolynomial.X (ij.1, k) : Pol n) * MvPolynomial.C (g k ij.2) := by
      simp [rtr, MvPolynomial.aeval_X]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_mul, hX, Finset.mul_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hk := hP k g
    simp only [LinearMap.comp_apply, LinearMap.mulRight_apply] at hk
    rw [show rtr g p * ((MvPolynomial.X (ij.1, k) : Pol n) * MvPolynomial.C (g k ij.2))
        = MvPolynomial.C (g k ij.2) * (rtr g p * MvPolynomial.X (ij.1, k)) by ring,
      MvPolynomial.C_mul', map_smul, smul_eq_mul, hk, MvPolynomial.eval_mul,
      MvPolynomial.eval_X]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.RtrMul
open Matrix UpperTheory.V.Weyl

theorem UpperTheory.V.Weyl.rtrMul :
    ∀ (n : ℕ), (∀ f : Pol n, rtr 1 f = f) ∧ ∀ (g h : Matrix (Fin n) (Fin n) ℂ) (f : Pol n), rtr (g * h) f = rtr g (rtr h f) := by
  intro n
  constructor
  · intro f
    have e : (rtr (1 : Matrix (Fin n) (Fin n) ℂ) : Pol n →ₐ[ℂ] Pol n) = AlgHom.id ℂ (Pol n) := by
      apply MvPolynomial.algHom_ext
      rintro ⟨i, j⟩
      simp [rtr, Matrix.one_apply, mul_ite, Finset.sum_ite_eq']
    rw [e]
    rfl
  · intro g h f
    have e : (rtr (g * h) : Pol n →ₐ[ℂ] Pol n) = (rtr g).comp (rtr h) := by
      apply MvPolynomial.algHom_ext
      rintro ⟨i, j⟩
      rw [AlgHom.comp_apply]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [rtr, MvPolynomial.aeval_X, map_sum]
      have hx : ∀ x, (MvPolynomial.aeval (fun ij : Fin n × Fin n => ∑ k, MvPolynomial.X (ij.1, k) *
          MvPolynomial.C (g k ij.2)) : MvPolynomial (Fin n × Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n × Fin n) ℂ)
          (MvPolynomial.X (i, x) * MvPolynomial.C (h x j)) =
          ∑ k, MvPolynomial.X (i, k) * MvPolynomial.C (g k x * h x j) := by
        intro x
        rw [map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, Finset.sum_mul]
        simp only [mul_assoc, ← map_mul]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hx, Matrix.mul_apply, map_sum, Finset.mul_sum]
      rw [Finset.sum_comm]
    rw [e]
    rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.RtrDeg
open Matrix UpperTheory.V.Weyl

theorem UpperTheory.V.Weyl.rtrDeg :
    ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) ℂ) (f : Pol n), (rtr g f).totalDegree ≤ f.totalDegree := by
  intro n g f
  have hY : ∀ ij : Fin n × Fin n,
      (∑ k, MvPolynomial.X (ij.1, k) * MvPolynomial.C (g k ij.2) : MvPolynomial (Fin n × Fin n) ℂ).totalDegree ≤ 1 := by
    intro ij
    refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun k _ => ?_)
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_C]
  conv_lhs => rw [MvPolynomial.as_sum f]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [rtr, map_sum, MvPolynomial.aeval_monomial]
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun s hs => ?_)
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.algebraMap_eq, MvPolynomial.totalDegree_C, zero_add]
  refine le_trans ?_ (MvPolynomial.le_totalDegree hs)
  unfold Finsupp.prod Finsupp.sum
  refine (MvPolynomial.totalDegree_finsetProd _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  refine (MvPolynomial.totalDegree_pow _ _).trans ?_
  calc s i * _ ≤ s i * 1 := Nat.mul_le_mul_left _ (hY i)
    _ = s i := mul_one _
end

open Matrix UpperTheory.V.Weyl

theorem UpperTheory.V.Weyl.polPre :
    ∀ (n N : ℕ), ∃ (Ξ : Pre n) (e : MvPolynomial.restrictTotalDegree (Fin n × Fin n) ℂ N ≃ₗ[ℂ] (Fin Ξ.d → ℂ)),
      ∀ (g : Matrix (Fin n) (Fin n) ℂ) (f f' : MvPolynomial.restrictTotalDegree (Fin n × Fin n) ℂ N),
        (f' : Pol n) = rtr g f → Ξ.mat g *ᵥ e f = e f' := by
  intro n N
  let V := MvPolynomial.restrictTotalDegree (Fin n × Fin n) ℂ N
  have mem : ∀ (g : Matrix (Fin n) (Fin n) ℂ) (f : V), rtr g (f : Pol n) ∈ V := by
    intro g f
    rw [MvPolynomial.mem_restrictTotalDegree]
    exact (rtrDeg n g f).trans ((MvPolynomial.mem_restrictTotalDegree _ _ _).1 f.2)
  let R : Matrix (Fin n) (Fin n) ℂ → V →ₗ[ℂ] V := fun g =>
    LinearMap.codRestrict V ((rtr g).toLinearMap.comp V.subtype) (mem g)
  have hR : ∀ g (f : V), ((R g f : V) : Pol n) = rtr g (f : Pol n) := fun g f => rfl
  let b := Module.finBasis ℂ V
  let M : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin (Module.finrank ℂ V)) (Fin (Module.finrank ℂ V)) ℂ :=
    fun g => LinearMap.toMatrix b b (R g)
  have hR1 : R 1 = LinearMap.id := by
    ext f
    rw [hR, (rtrMul n).1]
    rfl
  have hRm : ∀ g h, R (g * h) = R g ∘ₗ R h := by
    intro g h
    ext f
    rw [hR, (rtrMul n).2]
    rfl
  let mat : Matrix (Fin n) (Fin n) ℂ →* Matrix (Fin (Module.finrank ℂ V)) (Fin (Module.finrank ℂ V)) ℂ :=
    { toFun := M
      map_one' := by
        show LinearMap.toMatrix b b (R 1) = 1
        rw [hR1, LinearMap.toMatrix_id]
      map_mul' := by
        intro g h
        show LinearMap.toMatrix b b (R (g * h)) = LinearMap.toMatrix b b (R g) * LinearMap.toMatrix b b (R h)
        rw [hRm]
        exact LinearMap.toMatrix_comp b b b (R g) (R h) }
  have poly : ∀ i j : Fin (Module.finrank ℂ V), ∃ p : Pol n, ∀ g : Matrix (Fin n) (Fin n) ℂ,
      mat g i j = MvPolynomial.eval (fun ab => g ab.1 ab.2) p := by
    intro i j
    obtain ⟨φ, hφ⟩ := LinearMap.exists_extend (b.coord i)
    obtain ⟨p, hp⟩ := rtrPoly n ((b j : V) : Pol n) φ
    refine ⟨p, fun g => ?_⟩
    rw [← hp]
    show LinearMap.toMatrix b b (R g) i j = _
    rw [LinearMap.toMatrix_apply, ← hR, ← b.coord_apply, ← hφ]
    rfl
  refine ⟨⟨Module.finrank ℂ V, mat, poly⟩, b.equivFun, ?_⟩
  intro g f f' hf
  show LinearMap.toMatrix b b (R g) *ᵥ b.repr f = b.repr f'
  rw [LinearMap.toMatrix_mulVec_repr]
  congr 2
  apply Subtype.ext
  rw [hR, hf]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.DegRank
open Matrix UpperTheory.V.Weyl

theorem UpperTheory.V.Weyl.degRank :
    ∀ (n N : ℕ), Module.finrank ℂ (MvPolynomial.restrictTotalDegree (Fin n × Fin n) ℂ N) ≤ (N + 1) ^ (n * n) := by
  intro n N
  change Module.finrank ℂ (MvPolynomial.restrictSupport ℂ
    {m : Fin n × Fin n →₀ ℕ | (m.sum fun _ e => e) ≤ N}) ≤ _
  rw [Module.finrank_eq_nat_card_basis (MvPolynomial.basisRestrictSupport ℂ _)]
  have key : ∀ m : {m : Fin n × Fin n →₀ ℕ | (m.sum fun _ e => e) ≤ N},
      ∀ i, (m : Fin n × Fin n →₀ ℕ) i < N + 1 := by
    intro m i
    have h1 := Finsupp.le_degree i (m : Fin n × Fin n →₀ ℕ)
    have h2 : Finsupp.degree (m : Fin n × Fin n →₀ ℕ)
        = (m : Fin n × Fin n →₀ ℕ).sum fun _ e => e := rfl
    have h3 := m.2
    simp only [Set.mem_setOf_eq] at h3
    omega
  calc Nat.card {m : Fin n × Fin n →₀ ℕ | (m.sum fun _ e => e) ≤ N}
      ≤ Nat.card (Fin n × Fin n → Fin (N + 1)) :=
        Nat.card_le_card_of_injective (fun m i => ⟨(m : Fin n × Fin n →₀ ℕ) i, key m i⟩)
          (by
            intro a b h
            apply Subtype.ext
            ext i
            have := congrArg Fin.val (congrFun h i)
            simpa using this)
    _ = (N + 1) ^ (n * n) := by
      simp [Nat.card_eq_fintype_card, Fintype.card_fun]
end

open Matrix UpperTheory.V.Weyl

theorem UpperTheory.V.Weyl.existsScalar :
    ∀ (n : ℕ) (ν : Fin n → ℕ), Antitone ν → ∀ H : ℕ, (∀ k, ν k ≤ H) →
      ∃ Ξ : Pre n, 0 < Ξ.d ∧ Ξ.d ≤ (n * H + 1) ^ (n * n) ∧ Ξ.HasWt fun k => (ν k : ℂ) := by
  intro n ν hν H hH
  obtain ⟨f, hf0, hdeg, hf⟩ := topPol n ν hν H hH
  obtain ⟨Ξ, e, he⟩ := polPre n (n * H)
  let F : MvPolynomial.restrictTotalDegree (Fin n × Fin n) ℂ (n * H) :=
    ⟨f, (MvPolynomial.mem_restrictTotalDegree _ _ _).2 hdeg⟩
  have hF : F ≠ 0 := fun h => hf0 (congrArg Subtype.val h)
  have hv : e F ≠ 0 := fun h => hF (e.injective (h.trans e.map_zero.symm))
  have htop : Ξ.IsTop ν (e F) := by
    intro b hb
    rw [he b F ((∏ k, b k k ^ ν k) • F) (hf b hb).symm, map_smul]
  obtain ⟨Ξ', h0, hle, hw⟩ := scalar n Ξ ν (e F) hv htop
  refine ⟨Ξ', h0, hle.trans ?_, hw⟩
  have h1 := e.finrank_eq
  have h2 := degRank n (n * H)
  rw [h1] at h2
  simpa using h2
