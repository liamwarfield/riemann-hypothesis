module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.CayDivOf
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.ClsGainA

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.BridgeH
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.BridgeSt
noncomputable section

open Matrix Filter Topology

namespace PositivityTheory.Rg.Sw.SP

open PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Z

variable {n : ℕ}

def Ym (s : ℂ) (B : MC n) : Matrix (Fin n) (Fin n) ℂ := (1 - (Complex.I * s) • Matrix.of B)⁻¹

def Yp (s : ℂ) (B : MC n) : Matrix (Fin n) (Fin n) ℂ := (1 + (Complex.I * s) • Matrix.of B)⁻¹

def vals (s : ℂ) (B : MC n) : Bool × Fin n × Fin n → ℂ := fun k => if k.1 then Yp s B k.2.1 k.2.2 else Ym s B k.2.1 k.2.2

def evQ (s z : ℂ) (Q : Fm n) (B : MC n) : ℂ :=
  MvPolynomial.eval (vals s B) (MvPolynomial.map (Polynomial.evalRingHom z) Q)

def fQ (s z : ℂ) (m : ℕ) (Q : Fm n) (B : MC n) : ℂ := clsC s z m 0 1 B * evQ s z Q B

def HYm : Prop :=
  ∀ (n : ℕ) (s : ℂ) (x v : MC n), (1 - (Complex.I * s) • Matrix.of x).det ≠ 0 → ∀ a d : Fin n,
    HasDerivAt (fun t : ℂ => Ym s (x + t • v) a d) (((Complex.I * s) • (Ym s x * Matrix.of v * Ym s x)) a d) 0

def HYp : Prop :=
  ∀ (n : ℕ) (s : ℂ) (x v : MC n), (1 + (Complex.I * s) • Matrix.of x).det ≠ 0 → ∀ a d : Fin n,
    HasDerivAt (fun t : ℂ => Yp s (x + t • v) a d) ((-(Complex.I * s) • (Yp s x * Matrix.of v * Yp s x)) a d) 0

def HCls : Prop :=
  ∀ (n : ℕ) (s : ℂ), (s = 1 ∨ s = -1) → ∀ (z : ℂ) (m : ℕ) (x v : MC n), x ∈ OmS s →
    HasDerivAt (fun t : ℂ => clsC s z m 0 1 (x + t • v))
      (clsC s z m 0 1 x * (Complex.I * s * ((m : ℂ) + z) * (Ym s x * Matrix.of v).trace -
        Complex.I * s * z * (Yp s x * Matrix.of v).trace)) 0

end PositivityTheory.Rg.Sw.SP
end
end

noncomputable section

open Matrix Filter Topology

namespace PositivityTheory.Rg.Sw.SP

open PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Z

variable {n : ℕ}

theorem hasDerivAt_line (x v : MC n) : HasDerivAt (fun t : ℂ => x + t • v) v 0 := by
  simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add x

theorem det_affine_eventually (M0 A : Matrix (Fin n) (Fin n) ℂ) (h : M0.det ≠ 0) :
    ∀ᶠ t : ℂ in 𝓝 0, (M0 + t • A).det ≠ 0 := by
  have hc : Continuous fun t : ℂ => (M0 + t • A).det :=
    (continuous_const.add (continuous_id.smul continuous_const)).matrix_det
  have : (fun t : ℂ => (M0 + t • A).det) 0 ≠ 0 := by simpa using h
  exact hc.continuousAt.eventually_ne this

theorem inv_line (M0 A : Matrix (Fin n) (Fin n) ℂ) (h : M0.det ≠ 0)
    (hdiff : ∀ a d, DifferentiableAt ℂ (fun t : ℂ => (M0 + t • A)⁻¹ a d) 0) (a d : Fin n) :
    HasDerivAt (fun t : ℂ => (M0 + t • A)⁻¹ a d) ((-(M0⁻¹ * A * M0⁻¹)) a d) 0 := by
  set D : Matrix (Fin n) (Fin n) ℂ := fun a d => deriv (fun t : ℂ => (M0 + t • A)⁻¹ a d) 0 with hD
  have hY : ∀ a d, HasDerivAt (fun t : ℂ => (M0 + t • A)⁻¹ a d) (D a d) 0 := fun a d => (hdiff a d).hasDerivAt

  have hid : ∀ i j, HasDerivAt (fun t : ℂ => ((M0 + t • A) * (M0 + t • A)⁻¹) i j) ((A * M0⁻¹ + M0 * D) i j) 0 := by
    intro i j
    have e : (fun t : ℂ => ((M0 + t • A) * (M0 + t • A)⁻¹) i j) =
        fun t : ℂ => ∑ k, (M0 i k + t * A i k) * (M0 + t • A)⁻¹ k j := by
      funext t; simp [Matrix.mul_apply]
    rw [e]
    have hs : HasDerivAt (fun t : ℂ => ∑ k, (M0 i k + t * A i k) * (M0 + t • A)⁻¹ k j)
        (∑ k, (A i k * M0⁻¹ k j + M0 i k * D k j)) 0 := by
      apply HasDerivAt.fun_sum
      intro k _
      have h1 : HasDerivAt (fun t : ℂ => M0 i k + t * A i k) (A i k) 0 := by
        simpa using ((hasDerivAt_id (0 : ℂ)).mul_const (A i k)).const_add (M0 i k)
      simpa using h1.fun_mul (hY k j)
    convert hs using 1
    simp [Matrix.add_apply, Matrix.mul_apply, Finset.sum_add_distrib]
  have hconst : ∀ i j, HasDerivAt (fun t : ℂ => ((M0 + t • A) * (M0 + t • A)⁻¹) i j) 0 0 := by
    intro i j
    have hev : (fun t : ℂ => ((M0 + t • A) * (M0 + t • A)⁻¹) i j) =ᶠ[𝓝 0] fun _ => (1 : Matrix (Fin n) (Fin n) ℂ) i j := by
      filter_upwards [det_affine_eventually M0 A h] with t ht
      rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr ht)]
    exact (hasDerivAt_const (0 : ℂ) ((1 : Matrix (Fin n) (Fin n) ℂ) i j)).congr_of_eventuallyEq hev
  have hzero : A * M0⁻¹ + M0 * D = 0 := by
    ext i j
    exact (hid i j).unique (hconst i j)
  have hDv : D = -(M0⁻¹ * A * M0⁻¹) := by
    have h1 : M0⁻¹ * M0 = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr h)
    have h2 : M0 * D = -(A * M0⁻¹) := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact hzero
    calc D = M0⁻¹ * M0 * D := by rw [h1, Matrix.one_mul]
      _ = M0⁻¹ * (M0 * D) := by rw [Matrix.mul_assoc]
      _ = -(M0⁻¹ * A * M0⁻¹) := by rw [h2, Matrix.mul_neg, Matrix.mul_assoc]
  rw [← hDv]
  exact hY a d

theorem mX (s : ℂ) (x v : MC n) (t : ℂ) :
    1 - (Complex.I * s) • Matrix.of (x + t • v) = (1 - (Complex.I * s) • Matrix.of x) + t • (-(Complex.I * s) • Matrix.of v) := by
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem mY (s : ℂ) (x v : MC n) (t : ℂ) :
    1 + (Complex.I * s) • Matrix.of (x + t • v) = (1 + (Complex.I * s) • Matrix.of x) + t • ((Complex.I * s) • Matrix.of v) := by
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem diff_inv_X (s : ℂ) (x v : MC n) (h : (1 - (Complex.I * s) • Matrix.of x).det ≠ 0) (a d : Fin n) :
    DifferentiableAt ℂ (fun t : ℂ => ((1 - (Complex.I * s) • Matrix.of x) + t • (-(Complex.I * s) • Matrix.of v))⁻¹ a d) 0 := by
  have hA := entAn_inv (entAn_X (Complex.I * s) x) h a d
  have e : (fun t : ℂ => ((1 - (Complex.I * s) • Matrix.of x) + t • (-(Complex.I * s) • Matrix.of v))⁻¹ a d) =
      (fun B : MC n => (1 - (Complex.I * s) • Matrix.of B)⁻¹ a d) ∘ (fun t : ℂ => x + t • v) := by
    funext t
    simp only [Function.comp]
    rw [mX s x v t]
  rw [e]
  have hA' : DifferentiableAt ℂ (fun B : MC n => (1 - (Complex.I * s) • Matrix.of B)⁻¹ a d) ((fun t : ℂ => x + t • v) 0) := by
    simpa using hA.differentiableAt
  exact hA'.comp (0 : ℂ) (hasDerivAt_line x v).differentiableAt

theorem diff_inv_Y (s : ℂ) (x v : MC n) (h : (1 + (Complex.I * s) • Matrix.of x).det ≠ 0) (a d : Fin n) :
    DifferentiableAt ℂ (fun t : ℂ => ((1 + (Complex.I * s) • Matrix.of x) + t • ((Complex.I * s) • Matrix.of v))⁻¹ a d) 0 := by
  have hA := entAn_inv (entAn_Y (Complex.I * s) x) h a d
  have e : (fun t : ℂ => ((1 + (Complex.I * s) • Matrix.of x) + t • ((Complex.I * s) • Matrix.of v))⁻¹ a d) =
      (fun B : MC n => (1 + (Complex.I * s) • Matrix.of B)⁻¹ a d) ∘ (fun t : ℂ => x + t • v) := by
    funext t
    simp only [Function.comp]
    rw [mY s x v t]
  rw [e]
  have hA' : DifferentiableAt ℂ (fun B : MC n => (1 + (Complex.I * s) • Matrix.of B)⁻¹ a d) ((fun t : ℂ => x + t • v) 0) := by
    simpa using hA.differentiableAt
  exact hA'.comp (0 : ℂ) (hasDerivAt_line x v).differentiableAt

theorem hYm : HYm := by
  intro n s x v h a d
  have e : (fun t : ℂ => Ym s (x + t • v) a d) =
      fun t : ℂ => ((1 - (Complex.I * s) • Matrix.of x) + t • (-(Complex.I * s) • Matrix.of v))⁻¹ a d := by
    funext t
    simp only [Ym]
    rw [mX s x v t]
  rw [e]
  have := inv_line _ _ h (diff_inv_X s x v h) a d
  convert this using 1
  simp only [Ym, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_smul, Matrix.smul_mul]
  ring

theorem hYp : HYp := by
  intro n s x v h a d
  have e : (fun t : ℂ => Yp s (x + t • v) a d) =
      fun t : ℂ => ((1 + (Complex.I * s) • Matrix.of x) + t • ((Complex.I * s) • Matrix.of v))⁻¹ a d := by
    funext t
    simp only [Yp]
    rw [mY s x v t]
  rw [e]
  have := inv_line _ _ h (diff_inv_Y s x v h) a d
  convert this using 1
  simp only [Yp, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_smul, Matrix.smul_mul]
  ring

end PositivityTheory.Rg.Sw.SP
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.BridgeC
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.BridgeB
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.BridgeA
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.DetSqSplit
noncomputable section

open Matrix Filter Topology

namespace PositivityTheory.Rg.Sw.SP

open PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Z

variable {n : ℕ}

theorem det_line (M0 A : Matrix (Fin n) (Fin n) ℂ) (h : M0.det ≠ 0) :
    HasDerivAt (fun t : ℂ => (M0 + t • A).det) (M0.det * (M0⁻¹ * A).trace) 0 := by
  have hM : M0 * M0⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr h)
  set N := M0⁻¹ * A with hN
  set P : Polynomial ℂ := (det (1 + (Polynomial.X : Polynomial ℂ) • N.map Polynomial.C)).divX.divX with hP
  have e : (fun t : ℂ => (M0 + t • A).det) = fun t : ℂ => M0.det * (1 + N.trace * t + P.eval t * t ^ 2) := by
    funext t
    have : M0 + t • A = M0 * (1 + t • N) := by
      rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, hN, ← Matrix.mul_assoc, hM, Matrix.one_mul]
    rw [this, Matrix.det_mul, Matrix.det_one_add_smul]
  rw [e]
  have h1 : HasDerivAt (fun t : ℂ => 1 + N.trace * t + P.eval t * t ^ 2) N.trace 0 := by
    have ha : HasDerivAt (fun t : ℂ => N.trace * t) N.trace 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).const_mul N.trace
    have hb : HasDerivAt (fun t : ℂ => P.eval t * t ^ 2) 0 0 := by
      have := (P.hasDerivAt (0 : ℂ)).fun_mul (hasDerivAt_pow 2 (0 : ℂ))
      simpa using this
    simpa using (ha.const_add 1).fun_add hb
  exact h1.const_mul M0.det

theorem c_sq (s : ℂ) (hs : s = 1 ∨ s = -1) : (Complex.I * s) * (Complex.I * s) = -1 := by
  rcases hs with rfl | rfl <;> simp [Complex.I_mul_I]

theorem det_sq_split (s : ℂ) (hs : s = 1 ∨ s = -1) (B : MC n) :
    (1 + Matrix.of B * Matrix.of B).det =
      (1 - (Complex.I * s) • Matrix.of B).det * (1 + (Complex.I * s) • Matrix.of B).det := by
  rw [← Matrix.det_mul]
  congr 1
  have hc := c_sq s hs
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hc]
  simp only [neg_smul, one_smul]
  abel

theorem hCls : HCls := by
  intro n s hs z m x v hx
  obtain ⟨h1, h2, h3⟩ := hx
  set c : ℂ := Complex.I * s with hc
  set M0 : Matrix (Fin n) (Fin n) ℂ := 1 - c • Matrix.of x
  set M0' : Matrix (Fin n) (Fin n) ℂ := 1 + c • Matrix.of x
  set V : Matrix (Fin n) (Fin n) ℂ := Matrix.of v
  have hdM := det_line M0 (-c • V) h1
  have hdM' := det_line M0' (c • V) h2

  have e : (fun t : ℂ => clsC s z m 0 1 (x + t • v)) = fun t : ℂ =>
      Complex.exp (-z * Complex.log ((M0 + t • (-c • V)).det * (M0' + t • (c • V)).det)) * (((M0 + t • (-c • V)).det)⁻¹) ^ m := by
    funext t
    simp only [clsC, pow_zero, mul_one, map_one]
    rw [det_sq_split s hs, mX, mY, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  rw [e]
  have hW0 : (M0 + (0 : ℂ) • (-c • V)).det * (M0' + (0 : ℂ) • (c • V)).det ∈ Complex.slitPlane := by
    have e0 : (M0 + (0 : ℂ) • (-c • V)).det * (M0' + (0 : ℂ) • (c • V)).det = (1 + Matrix.of x * Matrix.of x).det := by
      simp only [zero_smul, add_zero]
      exact (det_sq_split s hs x).symm
    rw [e0]
    exact h3
  have hW := hdM.fun_mul hdM'
  have hL := hW.clog (by simpa using hW0)
  have hE := (hL.const_mul (-z)).cexp
  have hD := (hdM.inv (by simpa using h1)).pow m
  have hT := hE.fun_mul hD
  refine hT.congr_deriv ?_
  simp only [zero_smul, add_zero]
  have hM0 : M0.det ≠ 0 := h1
  have hM0' : M0'.det ≠ 0 := h2
  have tr1 : (M0⁻¹ * (-c • V)).trace = -c * (Ym s x * V).trace := by
    rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    rfl
  have tr2 : (M0'⁻¹ * (c • V)).trace = c * (Yp s x * V).trace := by
    rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    rfl
  have ecls : clsC s z m 0 1 x = Complex.exp (-z * Complex.log (M0.det * M0'.det)) * (M0.det⁻¹) ^ m := by
    simp only [clsC, pow_zero, mul_one, map_one]
    rw [det_sq_split s hs, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  rw [ecls, tr1, tr2]
  simp only [Pi.inv_apply, Pi.pow_apply, zero_smul, add_zero]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
    field_simp
    ring
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    field_simp
    have hinv : M0.det * M0.det⁻¹ = 1 := mul_inv_cancel₀ hM0
    linear_combination (-(c * (Ym s x * V).trace * M0.det⁻¹ ^ k) * (1 + (k : ℂ))) * hinv

end PositivityTheory.Rg.Sw.SP
end
end

noncomputable section

open Matrix Filter Topology

namespace PositivityTheory.Rg.Sw.SP

open PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Z

variable {n : ℕ}

theorem hasDerivAt_eval {ι : Type} [Fintype ι] [DecidableEq ι] (g : ℂ → ι → ℂ) (g' : ι → ℂ)
    (hg : ∀ k, HasDerivAt (fun t => g t k) (g' k) 0) (P : MvPolynomial ι ℂ) :
    HasDerivAt (fun t => MvPolynomial.eval (g t) P)
      (∑ k, MvPolynomial.eval (g 0) (MvPolynomial.pderiv k P) * g' k) 0 := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using hasDerivAt_const (0 : ℂ) a
  | add p q hp hq =>
    have e1 : (fun t => MvPolynomial.eval (g t) (p + q)) =
        fun t => MvPolynomial.eval (g t) p + MvPolynomial.eval (g t) q := by
      funext t; rw [map_add (f := _)]
    rw [e1]
    refine (hp.add hq).congr_deriv ?_
    simp only [map_add (f := _), add_mul, Finset.sum_add_distrib]
  | mul_X p k0 hp =>
    have h := hp.mul (hg k0)
    have e1 : (fun t => MvPolynomial.eval (g t) (p * MvPolynomial.X k0)) =
        fun t => MvPolynomial.eval (g t) p * g t k0 := by
      funext t; rw [map_mul, MvPolynomial.eval_X]
    rw [e1]
    refine h.congr_deriv ?_
    symm
    simp only [Derivation.leibniz, MvPolynomial.pderiv_X, smul_eq_mul, map_add (f := _), map_mul, MvPolynomial.eval_X,
      add_mul, Finset.sum_add_distrib]
    have e : ∑ k, MvPolynomial.eval (g 0) p * MvPolynomial.eval (g 0) ((Pi.single k (1 : MvPolynomial ι ℂ) : ι → MvPolynomial ι ℂ) k0) * g' k =
        MvPolynomial.eval (g 0) p * g' k0 := by
      rw [Finset.sum_eq_single k0]
      · simp
      · intro b _ hb
        simp [Pi.single_apply, Ne.symm hb]
      · simp
    rw [e, Finset.sum_mul]
    have e2 : ∑ k, g 0 k0 * MvPolynomial.eval (g 0) (MvPolynomial.pderiv k p) * g' k =
        ∑ k, MvPolynomial.eval (g 0) (MvPolynomial.pderiv k p) * g' k * g 0 k0 :=
      Finset.sum_congr rfl fun k _ => by ring
    rw [e2]
    ring

def cB (s : ℂ) (b : Bool) : ℂ := if b then Complex.I * s else -(Complex.I * s)

def alB (m : ℕ) (b : Bool) : Polynomial ℂ := if b then Polynomial.X else Polynomial.C (m : ℂ) + Polynomial.X

theorem smulC (a : ℂ) (P : Fm n) : a • P = MvPolynomial.C (Polynomial.C a) * P := by
  rw [Algebra.smul_def, MvPolynomial.algebraMap_apply, Polynomial.algebraMap_apply]
  rfl

def multPart (s : ℂ) (m : ℕ) (b : Bool) (k l : Fin n) : Fm n →ₗ[ℂ] Fm n :=
  (-(cB s b)) • (LinearMap.mulLeft ℂ (MvPolynomial.C (alB m b) * yv b l k)).restrictScalars ℂ

def derPart (s : ℂ) (b : Bool) (k l : Fin n) : Fm n →ₗ[ℂ] Fm n :=
  ∑ a : Fin n, ∑ d : Fin n, (-(cB s b)) •
    (LinearMap.mulLeft ℂ (yv b a k * yv b l d) ∘ₗ (MvPolynomial.pderiv (b, a, d)).toLinearMap.restrictScalars ℂ)

theorem opH_eq (s : ℂ) (m : ℕ) (b : Bool) (k l : Fin n) : opH s m b k l = multPart s m b k l + derPart s b k l := by
  cases b <;> rfl

theorem multPart_apply (s : ℂ) (m : ℕ) (b : Bool) (k l : Fin n) (Q : Fm n) :
    multPart s m b k l Q = MvPolynomial.C (Polynomial.C (-(cB s b))) * (MvPolynomial.C (alB m b) * yv b l k * Q) := by
  rw [multPart, LinearMap.smul_apply, smulC]
  rfl

theorem derPart_apply (s : ℂ) (b : Bool) (k l : Fin n) (Q : Fm n) :
    derPart s b k l Q = ∑ a : Fin n, ∑ d : Fin n, MvPolynomial.C (Polynomial.C (-(cB s b))) *
      (yv b a k * yv b l d * MvPolynomial.pderiv (b, a, d) Q) := by
  rw [derPart, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [LinearMap.smul_apply, smulC]
  rfl

end PositivityTheory.Rg.Sw.SP
end
end

noncomputable section

open Matrix Filter Topology

namespace PositivityTheory.Rg.Sw.SP

open PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Z

variable {n : ℕ}

theorem evQ_mul (s z : ℂ) (P Q : Fm n) (B : MC n) : evQ s z (P * Q) B = evQ s z P B * evQ s z Q B := by
  simp [evQ]

theorem evQ_add (s z : ℂ) (P Q : Fm n) (B : MC n) : evQ s z (P + Q) B = evQ s z P B + evQ s z Q B := by
  simp [evQ]

theorem evQ_sum (s z : ℂ) {ι : Type} (t : Finset ι) (P : ι → Fm n) (B : MC n) :
    evQ s z (∑ i ∈ t, P i) B = ∑ i ∈ t, evQ s z (P i) B := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [evQ, map_sum]

theorem evQ_CC (s z a : ℂ) (B : MC n) : evQ s z (MvPolynomial.C (Polynomial.C a)) B = a := by
  simp [evQ]

theorem evQ_C (s z : ℂ) (p : Polynomial ℂ) (B : MC n) : evQ s z (MvPolynomial.C p) B = p.eval z := by
  simp [evQ]

theorem evQ_yv (s z : ℂ) (b : Bool) (i j : Fin n) (B : MC n) : evQ s z (yv b i j) B = vals s B (b, i, j) := by
  simp [evQ, yv]

theorem evQ_multPart (s z : ℂ) (m : ℕ) (b : Bool) (k l : Fin n) (Q : Fm n) (B : MC n) :
    evQ s z (multPart s m b k l Q) B = -(cB s b) * ((alB m b).eval z * vals s B (b, l, k) * evQ s z Q B) := by
  rw [multPart_apply, evQ_mul, evQ_CC, evQ_mul, evQ_mul, evQ_C, evQ_yv]

theorem evQ_derPart (s z : ℂ) (b : Bool) (k l : Fin n) (Q : Fm n) (B : MC n) :
    evQ s z (derPart s b k l Q) B = ∑ a : Fin n, ∑ d : Fin n,
      -(cB s b) * (vals s B (b, a, k) * vals s B (b, l, d) * evQ s z (MvPolynomial.pderiv (b, a, d) Q) B) := by
  rw [derPart_apply, evQ_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [evQ_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [evQ_mul, evQ_CC, evQ_mul, evQ_mul, evQ_yv, evQ_yv]

theorem trace_eU (Y : Matrix (Fin n) (Fin n) ℂ) (k l : Fin n) : (Y * Matrix.of (eU k l)).trace = Y l k := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply, eU]
  rw [Finset.sum_eq_single l]
  · rw [Finset.sum_eq_single k]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  · intro b _ hb
    refine Finset.sum_eq_zero fun j _ => ?_
    simp [hb]
  · simp

theorem sandwich_eU (Y : Matrix (Fin n) (Fin n) ℂ) (k l a d : Fin n) :
    (Y * Matrix.of (eU k l) * Y) a d = Y a k * Y l d := by
  simp only [Matrix.mul_apply, Matrix.of_apply, eU]
  rw [Finset.sum_eq_single l]
  · rw [Finset.sum_eq_single k]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  · intro b _ hb
    rw [Finset.sum_eq_zero]
    · simp
    intro j _
    simp [hb]
  · simp

end PositivityTheory.Rg.Sw.SP
end
end

noncomputable section

open Matrix Filter Topology

namespace PositivityTheory.Rg.Sw.SP

open PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Z

variable {n : ℕ}

def gD (s : ℂ) (x : MC n) (k l : Fin n) (kk : Bool × Fin n × Fin n) : ℂ :=
  if kk.1 then (-(Complex.I * s) • (Yp s x * Matrix.of (eU k l) * Yp s x)) kk.2.1 kk.2.2
  else ((Complex.I * s) • (Ym s x * Matrix.of (eU k l) * Ym s x)) kk.2.1 kk.2.2

theorem hasDerivAt_vals (s : ℂ) (x : MC n) (hx : x ∈ OmS s) (k l : Fin n) (kk : Bool × Fin n × Fin n) :
    HasDerivAt (fun t : ℂ => vals s (x + t • eU k l) kk) (gD s x k l kk) 0 := by
  obtain ⟨b, a, d⟩ := kk
  cases b
  · simpa [vals, gD] using hYm n s x (eU k l) hx.1 a d
  · simpa [vals, gD] using hYp n s x (eU k l) hx.2.1 a d

theorem hasDerivAt_evQ (s z : ℂ) (x : MC n) (hx : x ∈ OmS s) (k l : Fin n) (Q : Fm n) :
    HasDerivAt (fun t : ℂ => evQ s z Q (x + t • eU k l))
      (∑ kk, evQ s z (MvPolynomial.pderiv kk Q) x * gD s x k l kk) 0 := by
  have h := hasDerivAt_eval (fun t : ℂ => vals s (x + t • eU k l)) (gD s x k l) (hasDerivAt_vals s x hx k l)
    (MvPolynomial.map (Polynomial.evalRingHom z) Q)
  simp only [zero_smul, add_zero] at h
  refine h.congr_deriv ?_
  refine Finset.sum_congr rfl fun kk _ => ?_
  rw [MvPolynomial.pderiv_map]
  rfl

theorem sum_bool_fin (F : Bool × Fin n × Fin n → ℂ) :
    ∑ kk, F kk = ∑ a : Fin n, ∑ d : Fin n, F (false, a, d) + ∑ a : Fin n, ∑ d : Fin n, F (true, a, d) := by
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [Fintype.sum_prod_type]
  ring

theorem line_fQ (s : ℂ) (hs : s = 1 ∨ s = -1) (z : ℂ) (m : ℕ) (Q : Fm n) (x : MC n) (hx : x ∈ OmS s) (k l : Fin n) :
    HasDerivAt (fun t : ℂ => fQ s z m Q (x + t • eU k l)) (fQ s z m (opD s m k l Q) x) 0 := by
  have h1 := hCls n s hs z m x (eU k l) hx
  have h2 := hasDerivAt_evQ s z x hx k l Q
  have h3 := h1.mul h2
  refine h3.congr_deriv ?_
  simp only [fQ, opD, LinearMap.add_apply, opH_eq, evQ_add, evQ_multPart, evQ_derPart, trace_eU, sum_bool_fin, gD,
    Bool.false_eq_true, if_false, if_true, Matrix.smul_apply, sandwich_eU, smul_eq_mul, cB, alB, vals,
    Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X, zero_smul, add_zero]
  simp only [Finset.mul_sum, Finset.sum_add_distrib, mul_add]
  ring_nf
  congr 1
  · congr 1
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun d _ => ?_
    ring
  · refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun d _ => ?_
    ring

end PositivityTheory.Rg.Sw.SP
end
end

noncomputable section

open Matrix Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.SP

open PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Z

variable {n : ℕ}

theorem an_fQ (s z : ℂ) (m : ℕ) (Q : Fm n) (B₀ : MC n) (hB : B₀ ∈ OmS s) : AnalyticAt ℂ (fQ s z m Q) B₀ := by
  obtain ⟨h1, h2, h3⟩ := hB
  have hu := entAn_inv (entAn_X (Complex.I * s) B₀) h1
  have hv := entAn_inv (entAn_Y (Complex.I * s) B₀) h2
  have hf : ∀ k : Bool × Fin n × Fin n, AnalyticAt ℂ (fun B => vals s B k) B₀ := by
    rintro ⟨_ | _, a, b⟩
    · exact hu a b
    · exact hv a b
  exact (an_clsC s z m 0 1 B₀ ⟨h1, h2, h3⟩).mul (an_eval (fun k B => vals s B k) B₀ hf _)

theorem anN_fQ (s z : ℂ) (m : ℕ) (Q : Fm n) : AnalyticOnNhd ℂ (fQ s z m Q) (OmS s) := fun x hx => an_fQ s z m Q x hx

theorem fderiv_fQ (s : ℂ) (hs : s = 1 ∨ s = -1) (z : ℂ) (m : ℕ) (Q : Fm n) (x : MC n) (hx : x ∈ OmS s) (k l : Fin n) :
    fderiv ℂ (fQ s z m Q) x (eU k l) = fQ s z m (opD s m k l Q) x := by
  have hd := (an_fQ s z m Q x hx).differentiableAt.hasFDerivAt
  have hl : HasDerivAt (fun t : ℂ => x + t • eU k l) (eU k l) 0 := hasDerivAt_line x (eU k l)
  have h1 : HasDerivAt (fun t : ℂ => fQ s z m Q (x + t • eU k l)) (fderiv ℂ (fQ s z m Q) x (eU k l)) 0 :=
    hd.comp_hasDerivAt_of_eq (0 : ℂ) hl (by simp)
  exact h1.unique (line_fQ s hs z m Q x hx k l)

def opsSeq (s : ℂ) (m : ℕ) : (k : ℕ) → (Fin k → Fin n × Fin n) → Fm n → Fm n
  | 0, _, Q => Q
  | k + 1, dirs, Q => opD s m (dirs 0).1 (dirs 0).2 (opsSeq s m k (Fin.tail dirs) Q)

theorem iter_fQ (s : ℂ) (hs : s = 1 ∨ s = -1) (z : ℂ) (m : ℕ) :
    ∀ (k : ℕ) (dirs : Fin k → Fin n × Fin n) (Q : Fm n) (x : MC n), x ∈ OmS s →
      iteratedFDeriv ℂ k (fQ s z m Q) x (fun i => eU (dirs i).1 (dirs i).2) = fQ s z m (opsSeq s m k dirs Q) x
  | 0, dirs, Q, x, hx => by simp [opsSeq]
  | k + 1, dirs, Q, x, hx => by
    have hdiff : DifferentiableAt ℂ (iteratedFDeriv ℂ k (fQ s z m Q)) x :=
      ((anN_fQ s z m Q).iteratedFDeriv k x hx).differentiableAt
    rw [hdiff.iteratedFDeriv_succ_apply_left']
    have heq : (fun y => iteratedFDeriv ℂ k (fQ s z m Q) y (Fin.tail fun i => eU (dirs i).1 (dirs i).2)) =ᶠ[𝓝 x]
        fQ s z m (opsSeq s m k (Fin.tail dirs) Q) := by
      filter_upwards [(isOpen_OmS s).mem_nhds hx] with y hy
      exact iter_fQ s hs z m k (Fin.tail dirs) Q y hy
    rw [heq.fderiv_eq]
    exact fderiv_fQ s hs z m _ x hx (dirs 0).1 (dirs 0).2

theorem opsSeq_eq (s : ℂ) (m : ℕ) : ∀ (k : ℕ) (dirs : Fin k → Fin n × Fin n) (Q : Fm n),
    opsSeq s m k dirs Q = (List.finRange k).foldr (fun i g => opD s m (dirs i).1 (dirs i).2 ∘ₗ g) LinearMap.id Q
  | 0, dirs, Q => by simp [opsSeq]
  | k + 1, dirs, Q => by
    rw [opsSeq, opsSeq_eq s m k (Fin.tail dirs) Q, List.finRange_succ, List.foldr_cons, List.foldr_map]
    rfl

theorem evQ_smul (s z a : ℂ) (P : Fm n) (B : MC n) : evQ s z (a • P) B = a * evQ s z P B := by
  rw [smulC, evQ_mul, evQ_CC]

theorem fQ_linear (s z : ℂ) (m : ℕ) {ι : Type} (t : Finset ι) (a : ι → ℂ) (P : ι → Fm n) (B : MC n) :
    fQ s z m (∑ i ∈ t, a i • P i) B = ∑ i ∈ t, a i * fQ s z m (P i) B := by
  simp only [fQ, evQ_sum, evQ_smul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem cay_fQ (s : ℂ) (hs : s = 1 ∨ s = -1) (z : ℂ) (m : ℕ) (Q : Fm n) (x : MC n) (hx : x ∈ OmS s) :
    cay (fQ s z m Q) x = fQ s z m (cayF s m Q) x := by
  have hc : ContDiffAt ℂ ω (fQ s z m Q) x := (an_fQ s z m Q x hx).contDiffAt
  have hperm : ∀ σ : Equiv.Perm (Fin n), iteratedFDeriv ℂ n (fQ s z m Q) x (fun k => eU (σ k) k) =
      iteratedFDeriv ℂ n (fQ s z m Q) x (fun k => eU k (σ⁻¹ k)) := by
    intro σ
    have := hc.iteratedFDeriv_comp_perm (fun k => eU k (σ⁻¹ k)) σ
    rw [← this]
    congr 1
    funext k
    change eU (σ k) k = eU (σ k) (σ.symm (σ k))
    rw [Equiv.symm_apply_apply]
  simp only [cay, hperm]
  rw [← Equiv.sum_comp (Equiv.inv (Equiv.Perm (Fin n)))]
  simp only [Equiv.inv_apply, inv_inv, Equiv.Perm.sign_inv]
  have hI : ∀ σ : Equiv.Perm (Fin n), iteratedFDeriv ℂ n (fQ s z m Q) x (fun k => eU k (σ k)) =
      fQ s z m (opsSeq s m n (fun k => (k, σ k)) Q) x := fun σ => iter_fQ s hs z m n (fun k => (k, σ k)) Q x hx
  simp only [hI, opsSeq_eq]
  rw [cayF, LinearMap.sum_apply]
  simp only [LinearMap.smul_apply]
  rw [fQ_linear]

theorem fQ_one (s z : ℂ) (m : ℕ) (B : MC n) : fQ s z m 1 B = clsC s z m 0 1 B := by
  simp [fQ, evQ]

theorem bridge : Bridge := by
  intro n s hs m N z B hB
  have key : ∀ N : ℕ, ∀ B : MC n, B ∈ OmS s → (cay^[N] (clsC s z m 0 1)) B = fQ s z m ((cayF s m)^[N] 1) B := by
    intro N
    induction N with
    | zero =>
      intro B _
      simp [fQ_one]
    | succ N ih =>
      intro B hB
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      have heq : (cay^[N] (clsC s z m 0 1)) =ᶠ[𝓝 B] fQ s z m ((cayF s m)^[N] 1) := by
        filter_upwards [(isOpen_OmS s).mem_nhds hB] with y hy
        exact ih y hy
      have e : cay (cay^[N] (clsC s z m 0 1)) B = cay (fQ s z m ((cayF s m)^[N] 1)) B := by
        simp only [cay]
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [(heq.iteratedFDeriv ℂ n).eq_of_nhds]
      rw [e, cay_fQ s hs z m _ B hB]
  rw [key N B hB]
  rfl

end PositivityTheory.Rg.Sw.SP
