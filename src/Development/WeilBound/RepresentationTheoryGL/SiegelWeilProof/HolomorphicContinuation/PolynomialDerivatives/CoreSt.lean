module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.NullStableAlt

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.CoreSt
noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

def inF1 (ε : Fin m → Bool) (k : Fin m × Fin n × Bool) : Prop := k.2.2 = !ε k.1

instance (ε : Fin m → Bool) : DecidablePred (inF1 (n := n) ε) := fun k => by unfold inF1; infer_instance

def F1 (ε : Fin m → Bool) : Submodule ℂ (PX m n) := Subalgebra.toSubmodule (MvPolynomial.supported ℂ {k | inF1 ε k})

def F2 (ε : Fin m → Bool) : Submodule ℂ (PX m n) := Subalgebra.toSubmodule (MvPolynomial.supported ℂ {k | ¬ inF1 ε k})

def rdeg (ε : Fin m → Bool) (s : Fin m × Fin n × Bool →₀ ℕ) (a : Fin m) : ℕ := ∑ i, s (a, i, !ε a)

def box (ε : Fin m → Bool) (R : Set (Fin m → ℕ)) : Submodule ℂ (PX m n) :=
  Submodule.span ℂ {p | ∃ s : Fin m × Fin n × Bool →₀ ℕ, (∀ k ∈ s.support, inF1 ε k) ∧ rdeg ε s ∈ R ∧ p = monomial s 1}

def wt (c : ℝ) (s : Fin m × Fin n × Bool →₀ ℕ) : ℝ := ∏ k ∈ s.support, ((s k).factorial : ℝ) * (2 * c) ^ (s k)

def fform (c : ℝ) (p q : PX m n) : ℂ := ∑ s ∈ p.support ∪ q.support, star (p.coeff s) * q.coeff s * (wt c s : ℂ)

def D1 (ε : Fin m → Bool) (c : ℝ) (a b : Fin m) (p : PX m n) : PX m n :=
  if ε a = ε b then
    (if ε a then -∑ i, X (a, i, false) * pderiv (b, i, false) p else ∑ i, X (b, i, true) * pderiv (a, i, true) p)
  else
    (if ε a then -(1 / (2 * c) : ℂ) • ∑ i, X (a, i, false) * X (b, i, true) * p
     else (2 * c : ℂ) • ∑ i, pderiv (b, i, false) (pderiv (a, i, true) p))

def D2 (ε : Fin m → Bool) (c : ℝ) (a b : Fin m) (p : PX m n) : PX m n :=
  if ε a = ε b then
    (if ε a then ∑ i, X (b, i, true) * pderiv (a, i, true) p else -∑ i, X (a, i, false) * pderiv (b, i, false) p)
  else
    (if ε a then (2 * c : ℂ) • ∑ i, pderiv (b, i, false) (pderiv (a, i, true) p)
     else -(1 / (2 * c) : ℂ) • ∑ i, X (a, i, false) * X (b, i, true) * p)

def firstFamilyOperatorEnd (ε : Fin m → Bool) (c : ℝ) (a b : Fin m) : Module.End ℂ (PX m n) where
  toFun := D1 ε c a b
  map_add' p q := by unfold D1; split_ifs <;> simp [mul_add, Finset.sum_add_distrib, smul_add] <;> abel
  map_smul' r p := by unfold D1; split_ifs <;> simp [Finset.mul_sum, Finset.smul_sum, smul_comm r, mul_smul_comm]

abbrev Sym (m n : ℕ) := MvPolynomial ((Fin m × Fin n × Bool) ⊕ (Fin m × Fin n × Bool)) ℂ

def opMono (t : (Fin m × Fin n × Bool) ⊕ (Fin m × Fin n × Bool) →₀ ℕ) (f : PX m n) : PX m n :=
  monomial (t.comapDomain Sum.inl Sum.inl_injective.injOn) 1 *
    (((Finset.univ : Finset (Fin m × Fin n × Bool)).toList.map fun k => (pderiv (R := ℂ) k).toLinearMap ^ (t (Sum.inr k))).prod) f

def op (s : Sym m n) (f : PX m n) : PX m n := ∑ t ∈ s.support, s.coeff t • opMono t f

def SymbolInFirstFamily (ε : Fin m → Bool) (s : Sym m n) : Prop := ∀ t ∈ s.support, ∀ k, (t (Sum.inl k) ≠ 0 ∨ t (Sum.inr k) ≠ 0) → inF1 ε k

def symK (ε : Fin m → Bool) (i j : Fin n) : Derivation ℂ (Sym m n) (Sym m n) :=
  MvPolynomial.mkDerivation ℂ (Sum.elim
    (fun k => if ε k.1 then (if k.2.2 = false ∧ k.2.1 = j then X (Sum.inl (k.1, i, false)) else 0)
      else (if k.2.2 = true ∧ k.2.1 = i then -X (Sum.inl (k.1, j, true)) else 0))
    (fun k => if ε k.1 then (if k.2.2 = false ∧ k.2.1 = i then -X (Sum.inr (k.1, j, false)) else 0)
      else (if k.2.2 = true ∧ k.2.1 = j then X (Sum.inr (k.1, i, true)) else 0)))

def SemiFam : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (φ : V → V → ℂ),
    (∀ v, ∀ w₁ w₂, φ v (w₁ + w₂) = φ v w₁ + φ v w₂) → (∀ v w (r : ℂ), φ v (r • w) = r * φ v w) →
    (∀ v w, φ w v = star (φ v w)) → (∀ v, v ≠ 0 → 0 < (φ v v).re) →
    ∀ (ι : Type) (T : ι → Module.End ℂ V), (∀ i, ∃ j, ∀ v w, φ (T i v) w = φ v (T j w)) →
      (∀ v, ∃ v₀ w, v = v₀ + w ∧ (∀ i, T i v₀ = 0) ∧ w ∈ ⨆ i, LinearMap.range (T i)) ∧
      ∀ v, (∀ i, T i v = 0) → v ∈ (⨆ i, LinearMap.range (T i)) → v = 0

def Bicomm : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (φ : V → V → ℂ),
    (∀ v, ∀ w₁ w₂, φ v (w₁ + w₂) = φ v w₁ + φ v w₂) → (∀ v w (r : ℂ), φ v (r • w) = r * φ v w) →
    (∀ v w, φ w v = star (φ v w)) → (∀ v, v ≠ 0 → 0 < (φ v v).re) →
    ∀ (ι : Type) (T : ι → Module.End ℂ V), (∀ i, ∃ j, ∀ v w, φ (T i v) w = φ v (T j w)) →
      ∀ x : Module.End ℂ V, (∀ t : Module.End ℂ V, (∀ i, t * T i = T i * t) → x * t = t * x) →
        x ∈ Algebra.adjoin ℂ (Set.range T)

def Dens : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (R : Finset (Fin m → ℕ)) (T : PX m n →ₗ[ℂ] PX m n), (∀ f ∈ box ε (R : Set _), T f ∈ F1 ε) →
    ∃ s : Sym m n, SymbolInFirstFamily ε s ∧ ∀ f ∈ box ε (R : Set _), op s f = T f

def SymKComm : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (i j : Fin n) (s : Sym m n), SymbolInFirstFamily ε s → ∀ f ∈ F1 ε,
    op (symK ε i j s) f = KopL ε i j (op s f) - op s (KopL ε i j f)

def InvOp : Prop :=
  PositivityTheory.Rg.Sw.FFT → ∀ (m n : ℕ) (ε : Fin m → Bool) (c : ℝ), 0 < c → ∀ s : Sym m n, SymbolInFirstFamily ε s → (∀ i j, symK ε i j s = 0) →
    ∃ w ∈ Algebra.adjoin ℂ (Set.range fun ab : Fin m × Fin m => firstFamilyOperatorEnd (n := n) ε c ab.1 ab.2), ∀ f ∈ F1 ε, op s f = w f

def RepB : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c : ℝ), 0 < c → ∀ Λ : PX m n →ₗ[ℂ] ℂ, (∀ a b p, Λ (Dop ε c a b p) = 0) →
    ∃ B : Module.End ℂ (PX m n), (∀ R : Set (Fin m → ℕ), ∀ f ∈ box ε R, B f ∈ box ε R) ∧
      (∀ f ∈ F1 ε, ∀ g ∈ F2 ε, Λ (f * g) = contr c (B f * g)) ∧
      ∀ a b, ∀ f ∈ F1 ε, B (D1 ε c a b f) = D1 ε c a b (B f)

def FormFacts : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c : ℝ), 0 < c →
    (∀ p q : PX m n, fform c q p = star (fform c p q)) ∧ (∀ p : PX m n, p ≠ 0 → 0 < (fform c p p).re) ∧
    (∀ (i j : Fin n) (p q : PX m n), fform c (KopL ε i j p) q = fform c p (KopL ε j i q)) ∧
    (∀ (i j : Fin n) (R : Set (Fin m → ℕ)), ∀ f ∈ box ε R, KopL ε i j f ∈ box ε R) ∧
    (∀ (i j : Fin n) (s t : Sym m n), fform (m := m) (n := n) (1 / 2) 0 0 = 0 ∧
      (∑ u ∈ (symK ε i j s).support ∪ t.support, star ((symK ε i j s).coeff u) * t.coeff u *
          ((∏ k ∈ u.support, ((u k).factorial : ℂ))) =
        ∑ u ∈ s.support ∪ (symK ε j i t).support, star (s.coeff u) * (symK ε j i t).coeff u *
          ((∏ k ∈ u.support, ((u k).factorial : ℂ)))))

end PositivityTheory.Rg.Sw.LC
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.PolyExpBound
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SquareNormBound
theorem UpperTheory.Reformulated.B.SquareNormBound.sq_norm_le :
    ∀ {m n : ℕ} (x : Fin m → Fin n → ℂ),
    ‖x‖ ^ (2 : ℕ) ≤ ∑ a : Fin m, ∑ i : Fin n, ‖x a i‖ ^ (2 : ℕ) := by
  intro m n x
  have hS0 : 0 ≤ ∑ a : Fin m, ∑ i : Fin n, ‖x a i‖ ^ (2 : ℕ) :=
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun i _ => by positivity
  have h : ‖x‖ ≤ Real.sqrt (∑ a : Fin m, ∑ i : Fin n, ‖x a i‖ ^ (2 : ℕ)) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun a =>
      (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
    apply Real.le_sqrt_of_sq_le
    calc ‖x a i‖ ^ (2 : ℕ) ≤ ∑ j : Fin n, ‖x a j‖ ^ (2 : ℕ) :=
          Finset.single_le_sum (f := fun j => ‖x a j‖ ^ (2 : ℕ))
            (fun _ _ => by positivity) (Finset.mem_univ i)
      _ ≤ ∑ b : Fin m, ∑ j : Fin n, ‖x b j‖ ^ (2 : ℕ) :=
          Finset.single_le_sum (f := fun b => ∑ j : Fin n, ‖x b j‖ ^ (2 : ℕ))
            (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ a)
  calc ‖x‖ ^ (2 : ℕ)
      ≤ (Real.sqrt (∑ a : Fin m, ∑ i : Fin n, ‖x a i‖ ^ (2 : ℕ))) ^ (2 : ℕ) := by gcongr
    _ = ∑ a : Fin m, ∑ i : Fin n, ‖x a i‖ ^ (2 : ℕ) := Real.sq_sqrt hS0
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.HasFDerivAtEvX
noncomputable section

open MvPolynomial MeasureTheory

namespace PositivityTheory.Rg.Sw.LC.NullS

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC

variable {m n : ℕ}

def crd (k : Fin m × Fin n × Bool) : (Fin m → Fin n → ℂ) →L[ℝ] ℂ :=
  if k.2.2 then (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) k.2.1).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin n → ℂ) k.1))
  else (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) k.2.1).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin n → ℂ) k.1)

theorem crd_apply (k : Fin m × Fin n × Bool) (x : Fin m → Fin n → ℂ) :
    crd k x = if k.2.2 then star (x k.1 k.2.1) else x k.1 k.2.1 := by
  unfold crd; split_ifs <;> simp [Complex.conjCLE_apply, Complex.star_def]

theorem evX_eq (P : PX m n) (x : Fin m → Fin n → ℂ) : evX P x = MvPolynomial.eval (fun k => crd k x) P := by
  simp only [evX, crd_apply]

theorem norm_crd_le (k : Fin m × Fin n × Bool) (x : Fin m → Fin n → ℂ) : ‖crd k x‖ ≤ ‖x‖ := by
  rw [crd_apply]
  have h : ‖x k.1 k.2.1‖ ≤ ‖x‖ := (norm_le_pi_norm (x k.1) k.2.1).trans (norm_le_pi_norm x k.1)
  split_ifs <;> simpa using h

def dP (P : PX m n) (x : Fin m → Fin n → ℂ) : (Fin m → Fin n → ℂ) →L[ℝ] ℂ := ∑ k, evX (pderiv k P) x • crd k

theorem hasFDerivAt_evX (P : PX m n) (x : Fin m → Fin n → ℂ) : HasFDerivAt (fun y => evX P y) (dP P x) x := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    have : dP (C a : PX m n) x = 0 := by simp [dP, evX_eq]
    have e : (fun y => evX (C a : PX m n) y) = fun _ => a := by funext y; simp [evX_eq]
    rw [this, e]; exact hasFDerivAt_const a x
  | add p q hp hq =>
    have : dP (p + q) x = dP p x + dP q x := by simp [dP, evX_eq, Finset.sum_add_distrib, add_smul]
    have e : (fun y => evX (p + q) y) = fun y => evX p y + evX q y := by funext y; simp [evX_eq]
    rw [this, e]; exact hp.add hq
  | mul_X p k hp =>
    have h1 : HasFDerivAt (fun y => evX p y * crd k y) (evX p x • crd k + crd k x • dP p x) x :=
      hp.mul (crd k).hasFDerivAt
    have e1 : (fun y => evX (p * X k) y) = fun y => evX p y * crd k y := by
      funext y; simp [evX_eq]
    have e2 : dP (p * X k) x = evX p x • crd k + crd k x • dP p x := by
      ext v
      have hb : ∀ b, evX (pderiv b (p * X k)) x * crd b v =
          crd k x * (evX (pderiv b p) x * crd b v) + (if k = b then evX p x * crd k v else 0) := by
        intro b
        rw [Derivation.leibniz, pderiv_X]
        by_cases h : k = b
        · subst h; simp [evX_eq]; ring
        · simp [evX_eq, Pi.single_apply, Ne.symm h, h]; ring
      simp only [dP, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_sum',
        Finset.sum_apply, smul_eq_mul]
      rw [Finset.sum_congr rfl fun b _ => hb b, Finset.sum_add_distrib, Finset.sum_ite_eq, if_pos (Finset.mem_univ _),
        ← Finset.mul_sum]
      ring
    rw [e1, e2]; exact h1

end PositivityTheory.Rg.Sw.LC.NullS
end
end

noncomputable section

open MvPolynomial MeasureTheory

namespace PositivityTheory.Rg.Sw.LC.NullS

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC

variable {m n : ℕ}

def Sg (c : ℝ) : PX m n := C (-(c : ℂ)) * ∑ a, ∑ i, X (a, i, true) * X (a, i, false)

theorem gs_eq (c : ℝ) (x : Fin m → Fin n → ℂ) : gs c x = Complex.exp (evX (Sg c) x) := by
  unfold gs
  congr 1
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Sg, evX_eq, map_mul, map_sum, eval_C, eval_X, crd_apply, if_true, Bool.false_eq_true, if_false,
    Complex.star_def, Complex.conj_mul']
  push_cast
  ring

theorem continuous_evX (P : PX m n) : Continuous fun x : Fin m → Fin n → ℂ => evX P x :=
  continuous_iff_continuousAt.2 fun x => (hasFDerivAt_evX P x).continuousAt

theorem evX_bound (P : PX m n) : ∃ K : ℝ, ∃ d : ℕ, 0 ≤ K ∧ ∀ x, ‖evX P x‖ ≤ K * (1 + ‖x‖) ^ d := by
  induction P using MvPolynomial.induction_on with
  | C a => exact ⟨‖a‖, 0, norm_nonneg _, fun x => by simp [evX_eq]⟩
  | add p q hp hq =>
    obtain ⟨K1, d1, h1, b1⟩ := hp
    obtain ⟨K2, d2, h2, b2⟩ := hq
    refine ⟨K1 + K2, max d1 d2, by positivity, fun x => ?_⟩
    have hx : 1 ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
    have e1 : (1 + ‖x‖) ^ d1 ≤ (1 + ‖x‖) ^ max d1 d2 := pow_le_pow_right₀ hx (le_max_left _ _)
    have e2 : (1 + ‖x‖) ^ d2 ≤ (1 + ‖x‖) ^ max d1 d2 := pow_le_pow_right₀ hx (le_max_right _ _)
    calc ‖evX (p + q) x‖ ≤ ‖evX p x‖ + ‖evX q x‖ := by simpa [evX_eq] using norm_add_le _ _
      _ ≤ K1 * (1 + ‖x‖) ^ d1 + K2 * (1 + ‖x‖) ^ d2 := add_le_add (b1 x) (b2 x)
      _ ≤ K1 * (1 + ‖x‖) ^ max d1 d2 + K2 * (1 + ‖x‖) ^ max d1 d2 :=
        add_le_add (mul_le_mul_of_nonneg_left e1 h1) (mul_le_mul_of_nonneg_left e2 h2)
      _ = (K1 + K2) * (1 + ‖x‖) ^ max d1 d2 := by ring
  | mul_X p k hp =>
    obtain ⟨K, d, hK, b⟩ := hp
    refine ⟨K, d + 1, hK, fun x => ?_⟩
    have hc : ‖crd k x‖ ≤ 1 + ‖x‖ := (norm_crd_le k x).trans (by linarith)
    calc ‖evX (p * X k) x‖ = ‖evX p x‖ * ‖crd k x‖ := by simp [evX_eq]
      _ ≤ (K * (1 + ‖x‖) ^ d) * (1 + ‖x‖) := mul_le_mul (b x) hc (norm_nonneg _) (by positivity)
      _ = K * (1 + ‖x‖) ^ (d + 1) := by ring

theorem sq_norm_le (x : Fin m → Fin n → ℂ) : ‖x‖ ^ 2 ≤ ∑ a, ∑ i, ‖x a i‖ ^ 2 :=
  _root_.UpperTheory.Reformulated.B.SquareNormBound.sq_norm_le x

theorem norm_gs_le (c : ℝ) (hc : 0 < c) (x : Fin m → Fin n → ℂ) : ‖gs c x‖ ≤ Real.exp (-(c * ‖x‖ ^ 2)) := by
  unfold gs
  rw [show (-(↑(c * ∑ a, ∑ i, ‖x a i‖ ^ 2) : ℂ)) = ↑(-(c * ∑ a, ∑ i, ‖x a i‖ ^ 2)) by push_cast; ring,
    Complex.norm_exp_ofReal]
  apply Real.exp_le_exp.2
  have := sq_norm_le x
  nlinarith

theorem poly_exp_bound (c : ℝ) (hc : 0 < c) (N : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (1 + t) ^ N * Real.exp (-(c * t ^ 2)) ≤ Real.exp (3 * c) * ((N.factorial : ℝ) / (2 * c) ^ N) := by
  set y := 2 * c * (1 + t) with hy
  have hy0 : 0 ≤ y := by positivity
  have h1 : Real.exp (-(c * t ^ 2)) ≤ Real.exp (3 * c) * Real.exp (-y) := by
    rw [← Real.exp_add]; apply Real.exp_le_exp.2; nlinarith [sq_nonneg (t - 1)]
  have h2 : (1 + t) ^ N * Real.exp (-y) ≤ (N.factorial : ℝ) / (2 * c) ^ N := by
    have := Real.pow_div_factorial_le_exp y hy0 N
    rw [div_le_iff₀ (by positivity)] at this
    rw [le_div_iff₀ (by positivity)]
    have hyN : y ^ N = (2 * c) ^ N * (1 + t) ^ N := by rw [hy, mul_pow]
    calc (1 + t) ^ N * Real.exp (-y) * (2 * c) ^ N = y ^ N * Real.exp (-y) := by rw [hyN]; ring
      _ ≤ (Real.exp y * N.factorial) * Real.exp (-y) := mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
      _ = N.factorial := by rw [mul_comm (Real.exp y), mul_assoc, ← Real.exp_add]; simp
  calc (1 + t) ^ N * Real.exp (-(c * t ^ 2)) ≤ (1 + t) ^ N * (Real.exp (3 * c) * Real.exp (-y)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = Real.exp (3 * c) * ((1 + t) ^ N * Real.exp (-y)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le

instance instHaarX : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure :=
  MeasureTheory.Measure.pi.isAddHaarMeasure _

theorem continuous_gs (c : ℝ) : Continuous fun x : Fin m → Fin n → ℂ => gs c x := by
  simp_rw [gs_eq]; exact Complex.continuous_exp.comp (continuous_evX _)

theorem integrable_pg (c : ℝ) (hc : 0 < c) (P : PX m n) :
    Integrable (fun x : Fin m → Fin n → ℂ => evX P x * gs c x) := by
  obtain ⟨K, d, hK, hb⟩ := evX_bound P
  set R : ℕ := Module.finrank ℝ (Fin m → Fin n → ℂ) + 1 with hR
  set M := Real.exp (3 * c) * (((d + R).factorial : ℝ) / (2 * c) ^ (d + R)) with hM
  have hcont : Continuous (fun x : Fin m → Fin n → ℂ => evX P x * gs c x) := (continuous_evX P).mul (continuous_gs c)
  refine ((integrable_one_add_norm (E := Fin m → Fin n → ℂ) (μ := volume) (r := (R : ℝ)) (by simp [hR])).const_mul
    (K * M)).mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  have ht : 0 ≤ ‖x‖ := norm_nonneg x
  have hpos : 0 < (1 + ‖x‖) ^ R := by positivity
  have key := poly_exp_bound c hc (d + R) ‖x‖ ht
  rw [norm_mul, Real.rpow_neg (by positivity), Real.rpow_natCast]
  calc ‖evX P x‖ * ‖gs c x‖ ≤ (K * (1 + ‖x‖) ^ d) * Real.exp (-(c * ‖x‖ ^ 2)) :=
        mul_le_mul (hb x) (norm_gs_le c hc x) (norm_nonneg _) (by positivity)
    _ = K * ((1 + ‖x‖) ^ (d + R) * Real.exp (-(c * ‖x‖ ^ 2))) / (1 + ‖x‖) ^ R := by
        rw [pow_add]; field_simp
    _ ≤ K * M / (1 + ‖x‖) ^ R := by
        apply div_le_div_of_nonneg_right _ hpos.le
        exact mul_le_mul_of_nonneg_left key hK
    _ = K * M * ((1 + ‖x‖) ^ R)⁻¹ := by rw [div_eq_mul_inv]

end PositivityTheory.Rg.Sw.LC.NullS
end
end
