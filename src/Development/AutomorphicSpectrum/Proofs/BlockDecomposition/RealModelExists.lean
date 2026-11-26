module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsBlockMatrixTwoByTwoFinEq
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralRightDerivativeEqZeroStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedFunctionDerivativeAtOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedFunctionKHighestWeight
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedFunctionKFinite
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CtGrowth
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviAdjointOnChains
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HighestWeightMemCone

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieGeneratorsGlRelations
noncomputable section

open Matrix
open PositivityTheory.RgTw (Mat)

namespace GlobalTheory.CompanionTheory.GLK.Pair

section Ring

variable {A : Type*} [Ring A] [Algebra ℂ A]

theorem brk_ee (p q r s P Q : A) (h1 : p * r - r * p = P) (h2 : q * r - r * q = Q) (h3 : p * s - s * p = Q)
    (h4 : q * s - s * q = -P) :
    ((1 / 2 : ℂ) • (p - Complex.I • q)) * ((1 / 2 : ℂ) • (r - Complex.I • s))
      - ((1 / 2 : ℂ) • (r - Complex.I • s)) * ((1 / 2 : ℂ) • (p - Complex.I • q))
      = (1 / 2 : ℂ) • (P - Complex.I • Q) := by
  subst h1 h2
  simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_sub, smul_smul]
  linear_combination (norm := skip) (-(Complex.I / 4)) • h3 + (-(1 / 4) : ℂ) • h4
  match_scalars <;> (ring_nf; try simp [Complex.I_sq]; try ring)

theorem brk_ff (p q r s P Q : A) (h1 : p * r - r * p = P) (h2 : q * r - r * q = Q) (h3 : p * s - s * p = Q)
    (h4 : q * s - s * q = -P) :
    ((1 / 2 : ℂ) • (p + Complex.I • q)) * ((1 / 2 : ℂ) • (r + Complex.I • s))
      - ((1 / 2 : ℂ) • (r + Complex.I • s)) * ((1 / 2 : ℂ) • (p + Complex.I • q))
      = (1 / 2 : ℂ) • (P + Complex.I • Q) := by
  subst h1 h2
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul]
  linear_combination (norm := skip) (Complex.I / 4) • h3 + (-(1 / 4) : ℂ) • h4
  match_scalars <;> (ring_nf; try simp [Complex.I_sq]; try ring)

theorem brk_ef (p q r s P Q : A) (h1 : p * r - r * p = P) (h2 : q * r - r * q = Q) (h3 : p * s - s * p = Q)
    (h4 : q * s - s * q = -P) :
    ((1 / 2 : ℂ) • (p - Complex.I • q)) * ((1 / 2 : ℂ) • (r + Complex.I • s))
      = ((1 / 2 : ℂ) • (r + Complex.I • s)) * ((1 / 2 : ℂ) • (p - Complex.I • q)) := by
  subst h1 h2
  simp only [sub_mul, mul_sub, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_sub, smul_add, smul_smul]
  linear_combination (norm := skip) (Complex.I / 4) • h3 + (1 / 4 : ℂ) • h4
  match_scalars <;> (ring_nf; try simp [Complex.I_sq]; try ring)

end Ring

section Main

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

def eP (D : Mat n → Module.End ℂ V) (Z : Mat n) : Module.End ℂ V :=
  (1 / 2 : ℂ) • (D Z - Complex.I • D (Complex.I • Z))

def fP (D : Mat n → Module.End ℂ V) (Z : Mat n) : Module.End ℂ V :=
  (1 / 2 : ℂ) • (D Z + Complex.I • D (Complex.I • Z))

theorem first_generator_eq_single (D : Mat n → Module.End ℂ V) (a b : Fin n) : e1 D a b = eP D (Matrix.single a b 1) := by
  simp [e1, eP, Matrix.smul_single]

theorem second_generator_eq_single (D : Mat n → Module.End ℂ V) (a b : Fin n) : f1 D a b = fP D (Matrix.single a b 1) := by
  simp [f1, fP, Matrix.smul_single]

variable {D : Mat n → Module.End ℂ V}

theorem D_neg (hs : ∀ (r : ℝ) X, D ((r : ℂ) • X) = (r : ℂ) • D X) (X : Mat n) : D (-X) = -D X := by
  simpa using hs (-1) X

theorem D_zero (hs : ∀ (r : ℝ) X, D ((r : ℂ) • X) = (r : ℂ) • D X) : D (0 : Mat n) = 0 := by
  simpa using hs 0 0

theorem D_sub (ha : ∀ X Y, D (X + Y) = D X + D Y) (hs : ∀ (r : ℝ) X, D ((r : ℂ) • X) = (r : ℂ) • D X)
    (X Y : Mat n) : D (X - Y) = D X - D Y := by
  rw [sub_eq_add_neg, ha, D_neg hs, sub_eq_add_neg]

theorem eP_zero (hs : ∀ (r : ℝ) X, D ((r : ℂ) • X) = (r : ℂ) • D X) : eP D (0 : Mat n) = 0 := by
  simp [eP, D_zero hs]

theorem fP_zero (hs : ∀ (r : ℝ) X, D ((r : ℂ) • X) = (r : ℂ) • D X) : fP D (0 : Mat n) = 0 := by
  simp [fP, D_zero hs]

theorem eP_sub (ha : ∀ X Y, D (X + Y) = D X + D Y) (hs : ∀ (r : ℝ) X, D ((r : ℂ) • X) = (r : ℂ) • D X)
    (X Y : Mat n) : eP D (X - Y) = eP D X - eP D Y := by
  simp only [eP, smul_sub, D_sub ha hs]
  abel

theorem fP_sub (ha : ∀ X Y, D (X + Y) = D X + D Y) (hs : ∀ (r : ℝ) X, D ((r : ℂ) • X) = (r : ℂ) • D X)
    (X Y : Mat n) : fP D (X - Y) = fP D X - fP D Y := by
  simp only [fP, smul_sub, smul_add, D_sub ha hs]
  abel

theorem brk_four (hs : ∀ (r : ℝ) X, D ((r : ℂ) • X) = (r : ℂ) • D X)
    (hb : ∀ X Y, D (X * Y - Y * X) = D X * D Y - D Y * D X) (Z W : Mat n) :
    D Z * D W - D W * D Z = D (Z * W - W * Z) ∧
    D (Complex.I • Z) * D W - D W * D (Complex.I • Z) = D (Complex.I • (Z * W - W * Z)) ∧
    D Z * D (Complex.I • W) - D (Complex.I • W) * D Z = D (Complex.I • (Z * W - W * Z)) ∧
    D (Complex.I • Z) * D (Complex.I • W) - D (Complex.I • W) * D (Complex.I • Z) = -D (Z * W - W * Z) := by
  refine ⟨(hb Z W).symm, ?_, ?_, ?_⟩
  · rw [← hb]
    congr 1
    simp [smul_sub]
  · rw [← hb]
    congr 1
    simp [smul_sub]
  · rw [← hb, ← D_neg hs]
    congr 1
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Complex.I_mul_I, neg_smul, one_smul]
    abel

theorem eP_brk (hs : ∀ (r : ℝ) X, D ((r : ℂ) • X) = (r : ℂ) • D X)
    (hb : ∀ X Y, D (X * Y - Y * X) = D X * D Y - D Y * D X) (Z W : Mat n) :
    eP D Z * eP D W - eP D W * eP D Z = eP D (Z * W - W * Z) := by
  obtain ⟨h1, h2, h3, h4⟩ := brk_four hs hb Z W
  exact brk_ee _ _ _ _ _ _ h1 h2 h3 h4

theorem fP_brk (hs : ∀ (r : ℝ) X, D ((r : ℂ) • X) = (r : ℂ) • D X)
    (hb : ∀ X Y, D (X * Y - Y * X) = D X * D Y - D Y * D X) (Z W : Mat n) :
    fP D Z * fP D W - fP D W * fP D Z = fP D (Z * W - W * Z) := by
  obtain ⟨h1, h2, h3, h4⟩ := brk_four hs hb Z W
  exact brk_ff _ _ _ _ _ _ h1 h2 h3 h4

theorem eP_fP_comm (hs : ∀ (r : ℝ) X, D ((r : ℂ) • X) = (r : ℂ) • D X)
    (hb : ∀ X Y, D (X * Y - Y * X) = D X * D Y - D Y * D X) (Z W : Mat n) :
    eP D Z * fP D W = fP D W * eP D Z := by
  obtain ⟨h1, h2, h3, h4⟩ := brk_four hs hb Z W
  exact brk_ef _ _ _ _ _ _ h1 h2 h3 h4

theorem single_brk (a b c d : Fin n) :
    (Matrix.single a b (1 : ℂ)) * Matrix.single c d 1 - Matrix.single c d (1 : ℂ) * Matrix.single a b 1 =
      (if b = c then Matrix.single a d 1 else 0) - (if d = a then Matrix.single c b 1 else 0) := by
  have h : ∀ a b c d : Fin n, (Matrix.single a b (1 : ℂ)) * Matrix.single c d 1 =
      if b = c then Matrix.single a d 1 else 0 := by
    intro a b c d
    split_ifs with h
    · subst h; simp
    · exact Matrix.single_mul_single_of_ne a b c h 1 (c := (1 : ℂ))
  rw [h, h]

theorem eP_units (ha : ∀ X Y, D (X + Y) = D X + D Y) (hs : ∀ (r : ℝ) X, D ((r : ℂ) • X) = (r : ℂ) • D X)
    (hb : ∀ X Y, D (X * Y - Y * X) = D X * D Y - D Y * D X) (a b c d : Fin n) :
    e1 D a b * e1 D c d - e1 D c d * e1 D a b =
      (if b = c then e1 D a d else 0) - (if d = a then e1 D c b else 0) := by
  simp only [first_generator_eq_single]
  rw [eP_brk hs hb, single_brk, eP_sub ha hs]
  split_ifs <;> simp [eP_zero hs]

theorem fP_units (ha : ∀ X Y, D (X + Y) = D X + D Y) (hs : ∀ (r : ℝ) X, D ((r : ℂ) • X) = (r : ℂ) • D X)
    (hb : ∀ X Y, D (X * Y - Y * X) = D X * D Y - D Y * D X) (a b c d : Fin n) :
    f1 D a b * f1 D c d - f1 D c d * f1 D a b =
      (if b = c then f1 D a d else 0) - (if d = a then f1 D c b else 0) := by
  simp only [second_generator_eq_single]
  rw [fP_brk hs hb, single_brk, fP_sub ha hs]
  split_ifs <;> simp [fP_zero hs]

end Main

theorem gl_pair : ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (D : Mat n → Module.End ℂ V),
    (∀ X Y, D (X + Y) = D X + D Y) → (∀ (r : ℝ) X, D ((r : ℂ) • X) = (r : ℂ) • D X) →
    (∀ X Y, D (X * Y - Y * X) = D X * D Y - D Y * D X) →
    Formalism.REAL.GlRel (e1 D) ∧ Formalism.REAL.GlRel (e2 D) ∧ ∀ a b c d, e1 D a b * e2 D c d = e2 D c d * e1 D a b := by
  intro n V _ _ D ha hs hb
  refine ⟨fun a b c d => eP_units ha hs hb a b c d, fun a b c d => ?_, fun a b c d => ?_⟩
  · have h := fP_units ha hs hb b a d c
    simp only [e2, neg_mul_neg]
    rw [h]
    simp only [eq_comm (a := b) (b := c), eq_comm (a := d) (b := a)]
    split_ifs <;> simp <;> abel
  · simp only [e2, mul_neg, neg_mul, first_generator_eq_single, second_generator_eq_single]
    rw [eP_fP_comm hs hb]

end GlobalTheory.CompanionTheory.GLK.Pair

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandInvariantEvalLowest
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandInvariantEvalLowest
open Finset
open PositivityTheory.RgBcC.RealD (epow gelA)

noncomputable section

namespace GlobalTheory.CompanionTheory.EvGel

section Dual

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

def dualFam (E : Fin n → Fin n → Module.End ℂ V) : Fin n → Fin n → Module.End ℂ (Module.Dual ℂ V) :=
  fun a b => (E b a).dualMap

theorem dualFam_apply (E : Fin n → Fin n → Module.End ℂ V) (a b : Fin n) (φ : Module.Dual ℂ V) (v : V) :
    dualFam E a b φ v = φ (E b a v) := rfl

theorem glRel_dualFam {E : Fin n → Fin n → Module.End ℂ V} (hE : Formalism.REAL.GlRel E) :
    Formalism.REAL.GlRel (dualFam E) := by
  intro a b c d
  refine LinearMap.ext fun φ => LinearMap.ext fun v => ?_
  have h2 := congrArg (fun T : Module.End ℂ V => φ (T v)) (hE d c b a)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, map_sub] at h2
  simp only [LinearMap.sub_apply, Module.End.mul_apply, dualFam_apply]
  by_cases h1 : b = c <;> by_cases h3 : d = a
  · subst h1; subst h3; simpa [dualFam_apply] using h2
  · subst h1; simpa [dualFam_apply, h3, Ne.symm h3] using h2
  · subst h3; simpa [dualFam_apply, h1, Ne.symm h1] using h2
  · simpa [dualFam_apply, h1, h3, Ne.symm h1, Ne.symm h3] using h2

theorem pow_dualFam (E : Fin n → Fin n → Module.End ℂ V) (m : ℕ) (a b : Fin n) (φ : Module.Dual ℂ V) (v : V) :
    ((Matrix.of (dualFam E) : Matrix (Fin n) (Fin n) (Module.End ℂ (Module.Dual ℂ V))) ^ m) a b φ v =
      φ (((Matrix.of E : Matrix (Fin n) (Fin n) (Module.End ℂ V)) ^ m) b a v) := by
  induction m generalizing a b φ v with
  | zero =>
    by_cases h : a = b
    · subst h; simp
    · simp [Matrix.one_apply, h, Ne.symm h]
  | succ m ih =>
    set_option synthInstance.maxHeartbeats 100000 in
      rw [pow_succ', pow_succ, Matrix.mul_apply, Matrix.mul_apply, LinearMap.sum_apply, LinearMap.sum_apply,
      LinearMap.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [Module.End.mul_apply, Matrix.of_apply, dualFam_apply, ih]

end Dual

theorem epow_eq_pow {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (m : ℕ) (a b : Fin n) :
    epow E m a b = ((Matrix.of E : Matrix (Fin n) (Fin n) (Module.End ℂ V)) ^ m) a b := by
  induction m generalizing a b with
  | zero => simp [epow, Matrix.one_apply]
  | succ m ih => simp only [epow, pow_succ', Matrix.mul_apply, Matrix.of_apply, ih]

theorem ev_gelA : ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V), Formalism.REAL.GlRel E → ∀ (ev : V →ₗ[ℂ] ℂ) (x : Fin n → ℂ),
    (∀ a b, b < a → ∀ v, ev (E a b v) = 0) → (∀ a v, ev (E a a v) = x a * ev v) →
    ∀ (m : ℕ) (v : V), ev (gelA E m v) =
      GlobalTheory.Dec.gelfVal (fun a => x a + ((n : ℂ) - 1) / 2 - ((a : ℕ) : ℂ)) m * ev v := by
  intro n V _ _ E hE ev x hlow hdiag m v
  have hHW : Formalism.REAL.IsHW (dualFam E) x ev :=
    ⟨fun a => LinearMap.ext fun w => by simp [dualFam_apply, hdiag],
      fun a b hab => LinearMap.ext fun w => by simpa [dualFam_apply] using hlow b a hab w⟩
  have h1 := GlobalTheory.PhiEigenfun.trace_pow_hw (dualFam E) x ev (glRel_dualFam hE) hHW m
  have h2 := congrArg (fun φ : Module.Dual ℂ V => φ v) h1
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, pow_dualFam, smul_eq_mul] at h2
  have hval : GlobalTheory.Dec.gelfVal (fun a : Fin n => x a + ((n : ℂ) - 1) / 2 - ((a : ℕ) : ℂ)) m =
      ∑ a, ∑ b, (Formalism.REAL.Amat (Formalism.REAL.lsh x) ^ m) a b := by
    have : (fun c : Fin n => x c + ((n : ℂ) - 1) / 2 - ((c : ℕ) : ℂ) + ((n : ℂ) - 1) / 2) = Formalism.REAL.lsh x := by
      funext c
      simp only [Formalism.REAL.lsh]
      ring
    rw [GlobalTheory.Dec.gelfVal, this]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hval, ← h2, gelA, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun a _ => by rw [epow_eq_pow]

end GlobalTheory.CompanionTheory.EvGel
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandInvariantEvalLowestStatement
open PositivityTheory.RgBcC.RealD (gelA)

theorem GlobalTheory.T.gelfand_invariant_eval_lowest :
    ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
      (E : Fin n → Fin n → Module.End ℂ V),
      Formalism.REAL.GlRel E → ∀ (ev : V →ₗ[ℂ] ℂ) (x : Fin n → ℂ),
        (∀ a b, b < a → ∀ v, ev (E a b v) = 0) →
        (∀ a v, ev (E a a v) = x a * ev v) →
        ∀ (m : ℕ) (v : V), ev (gelA E m v) =
          GlobalTheory.Dec.gelfVal (fun a => x a + ((n : ℂ) - 1) / 2 - ((a : ℕ) : ℂ)) m * ev v :=
  GlobalTheory.CompanionTheory.EvGel.ev_gelA
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandInvariantCommuteOfCommute
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandInvariantCommuteOfCommute
open scoped BigOperators
open PositivityTheory.RgBcC.RealD (epow gelA)

namespace GlobalTheory.CompanionTheory.ModelS

theorem commute_epow_of_units {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (T : Module.End ℂ V)
    (hT : ∀ a b, T * E a b = E a b * T) (m : ℕ) (a b : Fin n) :
    Commute T (epow E m a b) := by
  induction m generalizing a b with
  | zero =>
    change Commute T (if a = b then 1 else 0)
    split_ifs
    · exact Commute.one_right T
    · exact Commute.zero_right T
  | succ m ih =>
    change Commute T (∑ c, E a c * epow E m c b)
    exact Commute.sum_right _ _ _ fun c _ => Commute.mul_right (hT a c) (ih c b)

theorem gelA_commute_of_units : ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (T : Module.End ℂ V),
    (∀ a b, T * E a b = E a b * T) → ∀ m : ℕ, gelA E m * T = T * gelA E m := by
  intro n V _ _ E T hT m
  have h : Commute T (gelA E m) :=
    Commute.sum_right _ _ _ fun a _ => commute_epow_of_units E T hT m a a
  exact h.eq.symm

end GlobalTheory.CompanionTheory.ModelS
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandInvariantCommuteOfCommuteStatement
open PositivityTheory.RgBcC.RealD (gelA)

theorem _root_.GlobalTheory.T.gelfand_invariant_commute_of_commute :
    ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
      (E : Fin n → Fin n → Module.End ℂ V) (T : Module.End ℂ V),
      (∀ a b, T * E a b = E a b * T) → ∀ m : ℕ, gelA E m * T = T * gelA E m :=
  GlobalTheory.CompanionTheory.ModelS.gelA_commute_of_units
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CenterActsByScalarOnCyclic
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CenterActsByScalarOnCyclic
open PositivityTheory.RgBcC.RealD (kF)

namespace GlobalTheory.CompanionTheory.ModelS

theorem eq_smul_of_commute_of_ev : ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (F1 F2 : Fin n → Fin n → Module.End ℂ V), (∀ x : V, ∃ S : Submodule ℂ V, FiniteDimensional ℂ S ∧ x ∈ S ∧ ∀ a b, ∀ w ∈ S, kF F1 F2 a b w ∈ S) → ∀ (z : Module.End ℂ V), (∀ a b, z * F1 a b = F1 a b * z ∧ z * F2 a b = F2 a b * z) → ∀ (ev : V →ₗ[ℂ] ℂ) (c : ℂ), (∀ v, ev (z v) = c * ev v) → (∀ S : Submodule ℂ V, FiniteDimensional ℂ S → (∀ a b, ∀ w ∈ S, kF F1 F2 a b w ∈ S) → (∀ w ∈ S, ev w = 0) → ∀ w ∈ S, w = 0) → ∀ x : V, z x = c • x := by
  intro n V _ _ F1 F2 hfin z hz ev c hev hS x
  set A := Algebra.adjoin ℂ {T : Module.End ℂ V | ∃ a b, T = kF F1 F2 a b} with hA
  set y : V := z x - c • x with hy
  obtain ⟨S₁, hfd, hyS₁, hst⟩ := hfin y
  have hpres : ∀ T ∈ A, ∀ w ∈ S₁, T w ∈ S₁ := by
    intro T hT
    induction hT using Algebra.adjoin_induction with
    | mem T hT =>
      obtain ⟨a, b, rfl⟩ := hT
      exact hst a b
    | algebraMap r =>
      intro w hw
      simpa [Module.algebraMap_end_apply] using S₁.smul_mem r hw
    | add S T _ _ hS' hT' =>
      intro w hw
      exact S₁.add_mem (hS' w hw) (hT' w hw)
    | mul S T _ _ hS' hT' =>
      intro w hw
      exact hS' _ (hT' w hw)
  have hcomm : ∀ T ∈ A, z * T = T * z := by
    intro T hT
    induction hT using Algebra.adjoin_induction with
    | mem T hT =>
      obtain ⟨a, b, rfl⟩ := hT
      have h1 := (hz a b).1
      have h2 := (hz a b).2
      show z * (F1 a b + F2 a b) = (F1 a b + F2 a b) * z
      rw [mul_add, add_mul, h1, h2]
    | algebraMap r => exact (Algebra.commutes r z).symm
    | add S T _ _ hS' hT' => rw [mul_add, add_mul, hS', hT']
    | mul S T _ _ hS' hT' => rw [← mul_assoc, hS', mul_assoc, hT', mul_assoc]
  let S : Submodule ℂ V := (Subalgebra.toSubmodule A).map (LinearMap.applyₗ y)
  have hmem : ∀ w, w ∈ S ↔ ∃ T ∈ A, T y = w := by
    intro w
    simp [S, Submodule.mem_map]
  have hle : S ≤ S₁ := by
    intro w hw
    obtain ⟨T, hT, rfl⟩ := (hmem w).1 hw
    exact hpres T hT y hyS₁
  have hSfd : FiniteDimensional ℂ S := Submodule.finiteDimensional_of_le hle
  have hSst : ∀ a b, ∀ w ∈ S, kF F1 F2 a b w ∈ S := by
    intro a b w hw
    obtain ⟨T, hT, rfl⟩ := (hmem w).1 hw
    refine (hmem _).2 ⟨kF F1 F2 a b * T, A.mul_mem (Algebra.subset_adjoin ⟨a, b, rfl⟩) hT, rfl⟩
  have hSev : ∀ w ∈ S, ev w = 0 := by
    intro w hw
    obtain ⟨T, hT, rfl⟩ := (hmem w).1 hw
    have hzT : T (z x) = z (T x) := (LinearMap.congr_fun (hcomm T hT) x).symm
    rw [hy, map_sub, map_smul, hzT, map_sub, map_smul, hev, smul_eq_mul, sub_self]
  have hyS : y ∈ S := (hmem y).2 ⟨1, A.one_mem, rfl⟩
  exact sub_eq_zero.1 (hS S hSfd hSst hSev y hyS)

end GlobalTheory.CompanionTheory.ModelS
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CenterActsByScalarOnCyclicStatement
open PositivityTheory.RgBcC.RealD (kF)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.center_acts_by_scalar_on_cyclic : ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (F1 F2 : Fin n → Fin n → Module.End ℂ V), (∀ x : V, ∃ S : Submodule ℂ V, FiniteDimensional ℂ S ∧ x ∈ S ∧ ∀ a b, ∀ w ∈ S, kF F1 F2 a b w ∈ S) → ∀ (z : Module.End ℂ V), (∀ a b, z * F1 a b = F1 a b * z ∧ z * F2 a b = F2 a b * z) → ∀ (ev : V →ₗ[ℂ] ℂ) (c : ℂ), (∀ v, ev (z v) = c * ev v) → (∀ S : Submodule ℂ V, FiniteDimensional ℂ S → (∀ a b, ∀ w ∈ S, kF F1 F2 a b w ∈ S) → (∀ w ∈ S, ev w = 0) → ∀ w ∈ S, w = 0) → ∀ x : V, z x = c • x := by
  first | exact @GlobalTheory.CompanionTheory.ModelS.eq_smul_of_commute_of_ev | exact GlobalTheory.CompanionTheory.ModelS.eq_smul_of_commute_of_ev | (intros; apply GlobalTheory.CompanionTheory.ModelS.eq_smul_of_commute_of_ev <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsKFiniteSubmoduleContaining
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsKFiniteSubmoduleContaining
noncomputable section

open PositivityTheory.RgBcC.RealD (alg kF)

namespace GlobalTheory.CompanionTheory.ModelS.LocFin

section Abstract

variable {V : Type} [AddCommGroup V] [Module ℂ V] {ι κ : Type}

def stp (L : ι → Module.End ℂ V) (S : Submodule ℂ V) : Submodule ℂ V := S ⊔ ⨆ i, S.map (L i)

def fil (L : ι → Module.End ℂ V) (S₀ : Submodule ℂ V) (k : ℕ) : Submodule ℂ V := (stp L)^[k] S₀

theorem fil_succ (L : ι → Module.End ℂ V) (S₀ : Submodule ℂ V) (k : ℕ) :
    fil L S₀ (k + 1) = stp L (fil L S₀ k) :=
  Function.iterate_succ_apply' _ _ _

theorem le_stp (L : ι → Module.End ℂ V) (S : Submodule ℂ V) : S ≤ stp L S := le_sup_left

theorem letter_mem_stp (L : ι → Module.End ℂ V) {S : Submodule ℂ V} {u : V} (hu : u ∈ S) (i : ι) :
    L i u ∈ stp L S :=
  Submodule.mem_sup_right (Submodule.mem_iSup_of_mem i (Submodule.mem_map_of_mem hu))

theorem span_mem_stp (L : ι → Module.End ℂ V) {S : Submodule ℂ V} {u : V} (hu : u ∈ S)
    {C : Module.End ℂ V} (hC : C ∈ Submodule.span ℂ (Set.range L)) : C u ∈ stp L S := by
  induction hC using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact letter_mem_stp L hu i
  | zero => simp
  | add x y _ _ hx hy => simpa using add_mem hx hy
  | smul c x _ hx => simpa using Submodule.smul_mem _ c hx

theorem fil_mono (L : ι → Module.End ℂ V) (S₀ : Submodule ℂ V) : Monotone (fil L S₀) :=
  monotone_nat_of_le_succ fun k => by
    rw [fil_succ]
    exact le_stp L _

theorem fil_finite [Finite ι] (L : ι → Module.End ℂ V) (S₀ : Submodule ℂ V) [h₀ : FiniteDimensional ℂ S₀] (k : ℕ) :
    FiniteDimensional ℂ (fil L S₀ k) := by
  induction k with
  | zero => exact h₀
  | succ k ih =>
    rw [fil_succ]
    have : ∀ i, FiniteDimensional ℂ ((fil L S₀ k).map (L i)) := fun i => inferInstance
    have : FiniteDimensional ℂ ↥(⨆ i, (fil L S₀ k).map (L i) : Submodule ℂ V) := Submodule.finiteDimensional_iSup _
    exact Submodule.finiteDimensional_sup _ _

theorem stp_stable (L : ι → Module.End ℂ V) (K : Module.End ℂ V)
    (hK : ∀ i, K * L i - L i * K ∈ Submodule.span ℂ (Set.range L)) {S : Submodule ℂ V}
    (hS : ∀ w ∈ S, K w ∈ S) : ∀ w ∈ stp L S, K w ∈ stp L S := by
  have key : stp L S ≤ (stp L S).comap K := by
    refine sup_le (fun w hw => le_stp L S (hS w hw)) (iSup_le fun i => ?_)
    rintro _ ⟨u, hu, rfl⟩
    have h1 : L i (K u) ∈ stp L S := letter_mem_stp L (hS u hu) i
    have h2 : (K * L i - L i * K) u ∈ stp L S := span_mem_stp L hu (hK i)
    have h3 : K (L i u) = (K * L i - L i * K) u + L i (K u) := by simp
    change K (L i u) ∈ stp L S
    rw [h3]
    exact add_mem h2 h1
  exact fun w hw => key hw

theorem fil_stable (L : ι → Module.End ℂ V) (K : Module.End ℂ V)
    (hK : ∀ i, K * L i - L i * K ∈ Submodule.span ℂ (Set.range L)) {S₀ : Submodule ℂ V}
    (h₀ : ∀ w ∈ S₀, K w ∈ S₀) (k : ℕ) : ∀ w ∈ fil L S₀ k, K w ∈ fil L S₀ k := by
  induction k with
  | zero => exact h₀
  | succ k ih =>
    rw [fil_succ]
    exact stp_stable L K hK ih

theorem mem_fil_of_adjoin (L : ι → Module.End ℂ V) (S₀ : Submodule ℂ V) {T : Module.End ℂ V}
    (hT : T ∈ Algebra.adjoin ℂ (Set.range L)) {f : V} (hf : f ∈ S₀) : ∃ k, T f ∈ fil L S₀ k := by
  have key : ∀ w, (∃ k, w ∈ fil L S₀ k) → ∃ k, T w ∈ fil L S₀ k := by
    induction hT using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rintro w ⟨k, hk⟩
      exact ⟨k + 1, by rw [fil_succ]; exact letter_mem_stp L hk i⟩
    | algebraMap r =>
      rintro w ⟨k, hk⟩
      refine ⟨k, ?_⟩
      simpa [Module.algebraMap_end_apply] using Submodule.smul_mem _ r hk
    | add x y _ _ hx hy =>
      intro w hw
      obtain ⟨k, hk⟩ := hx w hw
      obtain ⟨m, hm⟩ := hy w hw
      refine ⟨max k m, ?_⟩
      simpa using add_mem (fil_mono L S₀ (le_max_left k m) hk) (fil_mono L S₀ (le_max_right k m) hm)
    | mul x y _ _ hx hy =>
      intro w hw
      simpa using hx (y w) (hy w hw)
  exact key f ⟨0, hf⟩

end Abstract

section Pair

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

def letters (F1 F2 : Fin n → Fin n → Module.End ℂ V) : Bool × Fin n × Fin n → Module.End ℂ V
  | (true, a, b) => F1 a b
  | (false, a, b) => F2 a b

theorem range_letters (F1 F2 : Fin n → Fin n → Module.End ℂ V) :
    Set.range (letters F1 F2) = {x | ∃ a b, x = F1 a b ∨ x = F2 a b} := by
  ext x
  constructor
  · rintro ⟨⟨_ | _, a, b⟩, rfl⟩
    · exact ⟨a, b, Or.inr rfl⟩
    · exact ⟨a, b, Or.inl rfl⟩
  · rintro ⟨a, b, rfl | rfl⟩
    · exact ⟨(true, a, b), rfl⟩
    · exact ⟨(false, a, b), rfl⟩

theorem gl_span (F1 F2 : Fin n → Fin n → Module.End ℂ V) (e : Bool) (E : Fin n → Fin n → Module.End ℂ V)
    (hE : ∀ a b, E a b = letters F1 F2 (e, a, b)) (a b c d : Fin n) :
    (if b = c then E a d else 0) - (if d = a then E c b else 0) ∈
      Submodule.span ℂ (Set.range (letters F1 F2)) := by
  have hm : ∀ a b, E a b ∈ Submodule.span ℂ (Set.range (letters F1 F2)) := fun a b =>
    Submodule.subset_span ⟨(e, a, b), (hE a b).symm⟩
  refine sub_mem ?_ ?_
  · split_ifs
    · exact hm _ _
    · exact zero_mem _
  · split_ifs
    · exact hm _ _
    · exact zero_mem _

theorem comm_letters {F1 F2 : Fin n → Fin n → Module.End ℂ V} (h1 : Formalism.REAL.GlRel F1) (h2 : Formalism.REAL.GlRel F2)
    (hc : ∀ a b c d, F1 a b * F2 c d = F2 c d * F1 a b) (a b : Fin n) (i : Bool × Fin n × Fin n) :
    kF F1 F2 a b * letters F1 F2 i - letters F1 F2 i * kF F1 F2 a b ∈
      Submodule.span ℂ (Set.range (letters F1 F2)) := by
  obtain ⟨_ | _, c, d⟩ := i
  · have h : kF F1 F2 a b * F2 c d - F2 c d * kF F1 F2 a b =
        (if b = c then F2 a d else 0) - (if d = a then F2 c b else 0) := by
      rw [← h2 a b c d]
      delta kF
      simp only [add_mul, mul_add, hc a b c d]
      abel
    change kF F1 F2 a b * F2 c d - F2 c d * kF F1 F2 a b ∈ _
    rw [h]
    exact gl_span F1 F2 false F2 (fun _ _ => rfl) a b c d
  · have h : kF F1 F2 a b * F1 c d - F1 c d * kF F1 F2 a b =
        (if b = c then F1 a d else 0) - (if d = a then F1 c b else 0) := by
      rw [← h1 a b c d]
      delta kF
      simp only [add_mul, mul_add, hc c d a b]
      abel
    change kF F1 F2 a b * F1 c d - F1 c d * kF F1 F2 a b ∈ _
    rw [h]
    exact gl_span F1 F2 true F1 (fun _ _ => rfl) a b c d

end Pair

theorem cyclic_locFin : ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (F1 F2 : Fin n → Fin n → Module.End ℂ V), Formalism.REAL.GlRel F1 → Formalism.REAL.GlRel F2 →
    (∀ a b c d, F1 a b * F2 c d = F2 c d * F1 a b) → ∀ f : V, (∀ x : V, ∃ T ∈ alg F1 F2, T f = x) →
    ∀ S₀ : Submodule ℂ V, FiniteDimensional ℂ S₀ → f ∈ S₀ → (∀ a b, ∀ w ∈ S₀, kF F1 F2 a b w ∈ S₀) →
    ∀ x : V, ∃ S : Submodule ℂ V, FiniteDimensional ℂ S ∧ x ∈ S ∧ ∀ a b, ∀ w ∈ S, kF F1 F2 a b w ∈ S := by
  intro n V _ _ F1 F2 h1 h2 hc f hgen S₀ hfin hf hst x
  obtain ⟨T, hT, rfl⟩ := hgen x
  have hT' : T ∈ Algebra.adjoin ℂ (Set.range (letters F1 F2)) := by
    rw [range_letters]
    exact hT
  obtain ⟨k, hk⟩ := mem_fil_of_adjoin (letters F1 F2) S₀ hT' hf
  exact ⟨fil (letters F1 F2) S₀ k, fil_finite _ _ k, hk, fun a b =>
    fil_stable _ _ (comm_letters h1 h2 hc a b) (hst a b) k⟩

end GlobalTheory.CompanionTheory.ModelS.LocFin
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsKFiniteSubmoduleContainingStatement
open PositivityTheory.RgBcC.RealD (alg kF)

theorem GlobalTheory.T.exists_k_finite_submodule_containing :
    ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
      (F1 F2 : Fin n → Fin n → Module.End ℂ V), Formalism.REAL.GlRel F1 → Formalism.REAL.GlRel F2 →
      (∀ a b c d, F1 a b * F2 c d = F2 c d * F1 a b) → ∀ f : V,
      (∀ x : V, ∃ T ∈ alg F1 F2, T f = x) → ∀ S₀ : Submodule ℂ V,
      FiniteDimensional ℂ S₀ → f ∈ S₀ → (∀ a b, ∀ w ∈ S₀, kF F1 F2 a b w ∈ S₀) →
      ∀ x : V, ∃ S : Submodule ℂ V, FiniteDimensional ℂ S ∧ x ∈ S ∧
        ∀ a b, ∀ w ∈ S, kF F1 F2 a b w ∈ S :=
  @GlobalTheory.CompanionTheory.ModelS.LocFin.cyclic_locFin
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealModelExists
noncomputable section

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ModelS

variable {n : ℕ}

theorem kF_gl {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {F1 F2 : Fin n → Fin n → Module.End ℂ V}
    (g1 : Formalism.REAL.GlRel F1) (g2 : Formalism.REAL.GlRel F2) (cm : ∀ a b c d, F1 a b * F2 c d = F2 c d * F1 a b) :
    Formalism.REAL.GlRel (kF F1 F2) := by
  intro a b c d
  have e : kF F1 F2 a b * kF F1 F2 c d - kF F1 F2 c d * kF F1 F2 a b =
      (F1 a b * F1 c d - F1 c d * F1 a b) + (F2 a b * F2 c d - F2 c d * F2 a b) +
        (F1 a b * F2 c d - F2 c d * F1 a b) - (F1 c d * F2 a b - F2 a b * F1 c d) := by
    simp only [kF]
    noncomm_ring
  rw [e, g1 a b c d, g2 a b c d, cm a b c d, cm c d a b]
  simp only [kF, sub_self, add_zero, sub_zero]
  split_ifs <;> first | abel | (simp; done) | (simp; abel)

theorem barF_gl {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {F2 : Fin n → Fin n → Module.End ℂ V}
    (g2 : Formalism.REAL.GlRel F2) : Formalism.REAL.GlRel (barF F2) := by
  intro a b c d
  have h := g2 b a d c
  simp only [barF, neg_mul_neg]
  rw [h]
  simp only [eq_comm (a := b) (b := c), eq_comm (a := d) (b := a)]
  split_ifs <;> first | abel | (simp; done) | (simp; abel)

theorem muZ_cast (lam : Fin n → ℤ) (lev : Fin n → ℕ) (a : Fin n) : ((muZ lam lev a : ℤ) : ℝ) = muQ lam lev a := by
  simp only [muZ, muQ, rhoU]
  push_cast
  ring

theorem model_of_ops (lam : Fin n → ℤ) (lev : Fin n → ℕ) (hlev : IsLev lam lev)
    {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (F1 F2 : Fin n → Fin n → Module.End ℂ V) (f : V)
    (ev : V →ₗ[ℂ] ℂ) (gl1 : Formalism.REAL.GlRel F1) (gl2 : Formalism.REAL.GlRel F2)
    (cm : ∀ a b c d, F1 a b * F2 c d = F2 c d * F1 a b)
    (unitK : ∀ a b (x y : V), ⟪kF F1 F2 a b x, y⟫_ℂ = ⟪x, kF F1 F2 b a y⟫_ℂ)
    (gen : ∀ x : V, ∃ T ∈ alg F1 F2, T f = x) (S₀ : Submodule ℂ V) (fd : FiniteDimensional ℂ S₀) (hf : f ∈ S₀)
    (st : ∀ a b, ∀ w ∈ S₀, kF F1 F2 a b w ∈ S₀) (hw : f ∈ hwSp F1 F2 (muQ lam lev)) (hev : ev f ≠ 0)
    (e1l : ∀ a b v, lev b ≤ lev a → a ≠ b → ev (F1 a b v) = 0) (e1d : ∀ a v, ev (F1 a a v) = (lam a : ℂ) * ev v)
    (e2l : ∀ a b v, lev b ≤ lev a → a ≠ b → ev (barF F2 a b v) = 0)
    (e2d : ∀ a v, ev (barF F2 a a v) = (yZ lam lev a : ℂ) * ev v)
    (sep : ∀ S : Submodule ℂ V, FiniteDimensional ℂ S → (∀ a b, ∀ w ∈ S, kF F1 F2 a b w ∈ S) → (∀ w ∈ S, ev w = 0) →
      ∀ w ∈ S, w = 0) : Nonempty (Model lam lev) := by
  have gK := kF_gl gl1 gl2 cm
  have gB := barF_gl gl2
  have lf := GlobalTheory.T.exists_k_finite_submodule_containing n V F1 F2 gl1 gl2 cm f gen S₀ fd hf st
  have hlow : ∀ a b : Fin n, b < a → lev b ≤ lev a ∧ a ≠ b := fun a b h => ⟨hlev.1 h.le, h.ne'⟩
  refine ⟨{ W := V, F1 := F1, F2 := F2, f := f, gl1 := gl1, gl2 := gl2, comm := cm, unitK := unitK, locFin := lf,
            hw := hw, ne := fun h => hev (by rw [h, map_zero]), ch1 := ?_, ch2 := ?_, cone := ?_ }⟩
  · intro m x
    refine GlobalTheory.T.center_acts_by_scalar_on_cyclic n V F1 F2 lf (gelA F1 m) (fun a b => ⟨GlobalTheory.T.gelfand_invariant_commute_generator n V F1 gl1 m a b, GlobalTheory.T.gelfand_invariant_commute_of_commute n V F1 (F2 a b)
      (fun c d => (cm c d a b).symm) m⟩) ev _ (fun v => ?_) sep x
    have h := GlobalTheory.T.gelfand_invariant_eval_lowest n V F1 gl1 ev (fun a => (lam a : ℂ)) (fun a b hba v => e1l a b v (hlow a b hba).1 (hlow a b hba).2)
      e1d m v
    rw [h]
    congr 2
    funext a
    simp [infOf]
  · intro m x
    refine GlobalTheory.T.center_acts_by_scalar_on_cyclic n V F1 F2 lf (gelA (barF F2) m) (fun a b => ⟨?_, ?_⟩) ev _ (fun v => ?_) sep x
    · refine GlobalTheory.T.gelfand_invariant_commute_of_commute n V (barF F2) (F1 a b) (fun c d => ?_) m
      simp only [barF, mul_neg, neg_mul, cm a b d c]
    · have h := GlobalTheory.T.gelfand_invariant_commute_generator n V (barF F2) gB m b a
      simp only [barF, mul_neg, neg_mul, neg_inj] at h
      simpa [barF] using h
    · have h := GlobalTheory.T.gelfand_invariant_eval_lowest n V (barF F2) gB ev (fun a => (yZ lam lev a : ℂ))
        (fun a b hba v => e2l a b v (hlow a b hba).1 (hlow a b hba).2) e2d m v
      rw [h]
      obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_perm_shifted_weight_eq_inf_char n lam lev hlev
      have : (fun a : Fin n => (yZ lam lev a : ℂ) + ((n : ℂ) - 1) / 2 - ((a : ℕ) : ℂ)) =
          fun a => infOf lam false (σ a) := funext hσ
      rw [this, GlobalTheory.T.gelfand_value_perm_invariant n (infOf lam false) σ m]
  · intro ν x hx hx0
    set A := Algebra.adjoin ℂ {T : Module.End ℂ V | ∃ a b, T = kF F1 F2 a b} with hA
    refine GlobalTheory.T.highest_weight_mem_cone n V (kF F1 F2) gK lev hlev.1 ev (muQ lam lev) ν x hx (fun a b v hl hne => ?_) (fun a v => ?_) ?_
    · have h1 := e1l a b v hl.ge hne
      have h2 := e2l b a v hl.le hne.symm
      simp only [barF, LinearMap.neg_apply, map_neg, neg_eq_zero] at h2
      simp [kF, h1, h2]
    · have h1 := e1d a v
      have h2 := e2d a v
      simp only [barF, LinearMap.neg_apply, map_neg] at h2
      have hm : (muQ lam lev a : ℂ) = (lam a : ℂ) - (yZ lam lev a : ℂ) := by
        rw [← muZ_cast]
        simp [yZ]
      simp only [kF, LinearMap.add_apply, map_add (f := _), h1, hm]
      linear_combination -h2
    · by_contra hcon
      push_neg at hcon
      obtain ⟨S₁, fd₁, hx₁, st₁⟩ := lf x
      have hstab : ∀ T ∈ A, ∀ w ∈ S₁, T w ∈ S₁ := by
        intro T hT
        induction hT using Algebra.adjoin_induction with
        | mem T hT => obtain ⟨a, b, rfl⟩ := hT; exact st₁ a b
        | algebraMap r => intro w hw; simpa [Module.algebraMap_end_apply] using S₁.smul_mem r hw
        | add T T' _ _ h h' => intro w hw; exact S₁.add_mem (h w hw) (h' w hw)
        | mul T T' _ _ h h' => intro w hw; exact h _ (h' w hw)
      let S : Submodule ℂ V := A.toSubmodule.map (LinearMap.applyₗ x)
      have hS : ∀ w, w ∈ S ↔ ∃ T ∈ A, T x = w := by
        intro w
        simp [S, Submodule.mem_map]
      have hle : S ≤ S₁ := by
        intro w hw
        obtain ⟨T, hT, rfl⟩ := (hS w).1 hw
        exact hstab T hT x hx₁
      haveI : FiniteDimensional ℂ S := Submodule.finiteDimensional_of_le hle
      have h0 := sep S inferInstance (fun a b w hw => ?_) (fun w hw => ?_) x ((hS x).2 ⟨1, A.one_mem, rfl⟩)
      · exact hx0 h0
      · obtain ⟨T, hT, rfl⟩ := (hS w).1 hw
        exact (hS _).2 ⟨kF F1 F2 a b * T, A.mul_mem (Algebra.subset_adjoin ⟨a, b, rfl⟩) hT, rfl⟩
      · obtain ⟨T, hT, rfl⟩ := (hS w).1 hw
        exact hcon T hT

theorem res_gl {M : Type} [AddCommGroup M] [Module ℂ M] (V : Submodule ℂ M) (E : Fin n → Fin n → Module.End ℂ M)
    (hE : ∀ a b, ∀ v ∈ V, E a b v ∈ V) (h : Formalism.REAL.GlRel E) :
    Formalism.REAL.GlRel (fun a b => (E a b).restrict (hE a b)) := by
  intro a b c d
  ext v
  have := congrArg (fun F => F (v : M)) (h a b c d)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at this
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub, LinearMap.restrict_apply]
  rw [this]
  split_ifs <;> simp

theorem first_raising_mem_equivariant (lev : Fin n → ℕ) (φ : Mat n → ℂ) (a b : Fin n) {h : SmF n} (hh : h ∈ Eqv lev φ) :
    e1 DR a b h ∈ Eqv lev φ := by
  simp only [e1, LinearMap.smul_apply, LinearMap.sub_apply]
  exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (GlobalTheory.T.right_derivative_preserves_equivariant n lev φ _ h hh)
    (Submodule.smul_mem _ _ (GlobalTheory.T.right_derivative_preserves_equivariant n lev φ _ h hh)))

theorem first_lowering_mem_equivariant (lev : Fin n → ℕ) (φ : Mat n → ℂ) (a b : Fin n) {h : SmF n} (hh : h ∈ Eqv lev φ) :
    f1 DR a b h ∈ Eqv lev φ := by
  simp only [f1, LinearMap.smul_apply, LinearMap.add_apply]
  exact Submodule.smul_mem _ _ (Submodule.add_mem _ (GlobalTheory.T.right_derivative_preserves_equivariant n lev φ _ h hh)
    (Submodule.smul_mem _ _ (GlobalTheory.T.right_derivative_preserves_equivariant n lev φ _ h hh)))

theorem evaluation_raising_lowering (lev : Fin n → ℕ) (f h : SmF n) (hf : f ∈ Eqv lev f.1) (h1 : f.1 1 = 1) (hh : h ∈ Eqv lev f.1)
    (a b : Fin n) (hab : lev b ≤ lev a) :
    (e1 DR a b h).1 1 = (e1 DR a b f).1 1 * h.1 1 ∧ (f1 DR a b h).1 1 = (f1 DR a b f).1 1 * h.1 1 := by
  have hX : ∀ c : ℂ, ∀ a' b', lev a' < lev b' → (Matrix.single a b c : Mat n) a' b' = 0 := by
    intro c a' b' hlt
    rw [Matrix.single_apply_of_ne]
    rintro ⟨rfl, rfl⟩
    exact absurd hlt (not_lt.2 hab)
  have d1 := GlobalTheory.T.right_derivative_lower_block_at_one n lev f h hf h1 hh _ (hX 1)
  have d2 := GlobalTheory.T.right_derivative_lower_block_at_one n lev f h hf h1 hh _ (hX Complex.I)
  constructor
  · simp only [e1, LinearMap.smul_apply, LinearMap.sub_apply, Submodule.coe_smul, Submodule.coe_sub, Pi.smul_apply,
      Pi.sub_apply, d1, d2, smul_eq_mul]
    ring
  · simp only [f1, LinearMap.smul_apply, LinearMap.add_apply, Submodule.coe_smul, Submodule.coe_add, Pi.smul_apply,
      Pi.add_apply, d1, d2, smul_eq_mul]
    ring

theorem modelEx_main : ModelEx := by
  intro n lam hlam lev hlev
  classical
  letI : MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ) := borel _
  haveI : BorelSpace (Matrix.unitaryGroup (Fin n) ℂ) := ⟨rfl⟩
  obtain ⟨κ, hκ1, hκ2, hκ3⟩ := GlobalTheory.T.exists_haar_unitary_group n
  have hmem := GlobalTheory.T.inducedFunction_smooth n lam hlam lev hlev
  let F : SmF n := ⟨fRaw lam lev, hmem⟩
  have hF : F.1 = fRaw lam lev := rfl
  have hFe : F ∈ Eqv lev F.1 := fun p hp g hg => GlobalTheory.T.inducedFunction_parabolic_equivariant n lam hlam lev hlev p hp g hg
  have hF1 : F.1 1 = 1 := GlobalTheory.T.inducedFunction_at_one n lam lev
  let A := Algebra.adjoin ℂ {T : Module.End ℂ (SmF n) | ∃ a b, T = e1 DR a b ∨ T = e2 DR a b}
  have hcyc : ∀ w, w ∈ cyc F ↔ ∃ T ∈ A, T F = w := by
    intro w
    simp [cyc, A, Submodule.mem_map]
  have hEq : ∀ T ∈ A, ∀ h ∈ Eqv lev F.1, T h ∈ Eqv lev F.1 := by
    intro T hT
    induction hT using Algebra.adjoin_induction with
    | mem T hT =>
      obtain ⟨a, b, rfl | rfl⟩ := hT
      · exact fun h hh => first_raising_mem_equivariant lev _ a b hh
      · intro h hh
        simp only [e2, LinearMap.neg_apply]
        exact Submodule.neg_mem _ (first_lowering_mem_equivariant lev _ b a hh)
    | algebraMap r => intro w hw; simpa [Module.algebraMap_end_apply] using Submodule.smul_mem _ r hw
    | add T T' _ _ h h' => intro w hw; exact Submodule.add_mem _ (h w hw) (h' w hw)
    | mul T T' _ _ h h' => intro w hw; exact h _ (h' w hw)
  have hWE : ∀ w ∈ cyc F, w ∈ Eqv lev F.1 := by
    intro w hw
    obtain ⟨T, hT, rfl⟩ := (hcyc w).1 hw
    exact hEq T hT F hFe
  have st1 : ∀ a b, ∀ w ∈ cyc F, e1 DR a b w ∈ cyc F := by
    intro a b w hw
    obtain ⟨T, hT, rfl⟩ := (hcyc w).1 hw
    exact (hcyc _).2 ⟨e1 DR a b * T, A.mul_mem (Algebra.subset_adjoin ⟨a, b, Or.inl rfl⟩) hT, rfl⟩
  have st2 : ∀ a b, ∀ w ∈ cyc F, e2 DR a b w ∈ cyc F := by
    intro a b w hw
    obtain ⟨T, hT, rfl⟩ := (hcyc w).1 hw
    exact (hcyc _).2 ⟨e2 DR a b * T, A.mul_mem (Algebra.subset_adjoin ⟨a, b, Or.inr rfl⟩) hT, rfl⟩
  obtain ⟨hsym, hnn, hadd, hsm, hdef⟩ := GlobalTheory.T.l2_inner_product_hermitian_form n κ
  have hzero : ∀ w ∈ cyc F, (∀ k : Matrix.unitaryGroup (Fin n) ℂ, w.1 k.1 = 0) → w = 0 := by
    intro w hw hk
    apply Subtype.ext
    funext g
    by_cases hg : g ∈ GLs n
    · obtain ⟨p, hp, k, rfl⟩ := GlobalTheory.T.iwasawa_parabolic_unitary n lev hlev.1 g hg
      have := hWE w hw p hp k.1 (GlobalTheory.CompanionTheory.ModelS.unit_mem k)
      simp [this, hk k]
    · exact w.2.2 g hg
  let core : InnerProductSpace.Core ℂ (cyc F) :=
    { inner := fun x y => ipK κ x.1 y.1
      conj_inner_symm := fun x y => hsym x.1 y.1
      re_inner_nonneg := fun x => hnn x.1
      add_left := fun x y z => hadd x.1 y.1 z.1
      smul_left := fun x y c => hsm c x.1 y.1
      definite := fun x hx => Subtype.ext (hzero x.1 x.2 (hdef x.1 hx)) }
  letI : NormedAddCommGroup (cyc F) := @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ core
  letI : InnerProductSpace ℂ (cyc F) := InnerProductSpace.ofCore core.toCore
  obtain ⟨g1, g2, cm⟩ := GlobalTheory.CompanionTheory.GLK.Pair.gl_pair n (SmF n) DR (GlobalTheory.T.right_derivative_real_lie_hom n).1 (GlobalTheory.T.right_derivative_real_lie_hom n).2.1 (GlobalTheory.T.right_derivative_real_lie_hom n).2.2
  let F1 : Fin n → Fin n → Module.End ℂ (cyc F) := fun a b => (e1 DR a b).restrict (st1 a b)
  let F2 : Fin n → Fin n → Module.End ℂ (cyc F) := fun a b => (e2 DR a b).restrict (st2 a b)
  have hKc : ∀ a b (x : cyc F), ((kF F1 F2 a b x : cyc F) : SmF n) = Kf a b x.1 := fun _ _ _ => rfl
  let f : cyc F := ⟨F, (hcyc F).2 ⟨1, A.one_mem, rfl⟩⟩
  let ev : cyc F →ₗ[ℂ] ℂ := ev1.comp (cyc F).subtype
  obtain ⟨S₁, fd₁, hf₁, st₁⟩ := GlobalTheory.T.inducedFunction_k_finite n lam hlam lev hlev F hF
  obtain ⟨hh1, hh2⟩ := GlobalTheory.T.inducedFunction_k_highest_weight n lam hlam lev hlev F hF
  have hder := GlobalTheory.T.inducedFunction_derivative_at_one n lam hlam lev hlev F hF
  refine model_of_ops lam lev hlev F1 F2 f ev (res_gl _ _ st1 g1) (res_gl _ _ st2 g2) ?_ ?_ ?_
    (S₁.comap (cyc F).subtype) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro a b c d
    refine LinearMap.ext fun w => Subtype.ext ?_
    exact congrArg (fun T => T w.1) (cm a b c d)
  · intro a b x y
    exact GlobalTheory.T.k_action_skew_adjoint_l2 n κ (GlobalTheory.T.integral_right_derivative_eq_zero n κ) a b x.1 y.1
  · intro x
    have key : ∀ T ∈ A, ∃ T' ∈ alg F1 F2, ∀ w : cyc F, ((T' w : cyc F) : SmF n) = T w.1 := by
      intro T hT
      induction hT using Algebra.adjoin_induction with
      | mem T hT =>
        obtain ⟨a, b, rfl | rfl⟩ := hT
        · exact ⟨F1 a b, Algebra.subset_adjoin ⟨a, b, Or.inl rfl⟩, fun _ => rfl⟩
        · exact ⟨F2 a b, Algebra.subset_adjoin ⟨a, b, Or.inr rfl⟩, fun _ => rfl⟩
      | algebraMap r =>
        exact ⟨algebraMap ℂ _ r, Subalgebra.algebraMap_mem _ r, fun w => by simp [Module.algebraMap_end_apply]⟩
      | add T T' _ _ h h' =>
        obtain ⟨P, hP, hP'⟩ := h
        obtain ⟨Q, hQ, hQ'⟩ := h'
        exact ⟨P + Q, Subalgebra.add_mem _ hP hQ, fun w => by simp [hP', hQ']⟩
      | mul T T' _ _ h h' =>
        obtain ⟨P, hP, hP'⟩ := h
        obtain ⟨Q, hQ, hQ'⟩ := h'
        exact ⟨P * Q, Subalgebra.mul_mem _ hP hQ, fun w => by simp [hP', hQ']⟩
    obtain ⟨T, hT, hTx⟩ := (hcyc x.1).1 x.2
    obtain ⟨T', hT', hc⟩ := key T hT
    exact ⟨T', hT', Subtype.ext (by rw [hc f]; exact hTx)⟩
  · let φ : ↥(S₁.comap (cyc F).subtype) →ₗ[ℂ] S₁ :=
      ((cyc F).subtype ∘ₗ (S₁.comap (cyc F).subtype).subtype).codRestrict S₁ (fun x => x.2)
    exact Module.Finite.of_injective φ (fun x y h => Subtype.ext (Subtype.ext (congrArg (fun t : ↥S₁ => (t : SmF n)) h)))
  · exact hf₁
  · intro a b w hw
    exact st₁ a b w.1 hw
  · refine ⟨fun a => ?_, fun a b hab _ => ?_⟩
    · apply Subtype.ext
      rw [hKc]
      have := hh2 a
      rw [← muZ_cast]
      simpa [f] using this
    · apply Subtype.ext
      rw [hKc]
      exact hh1 a b hab
  · show F.1 1 ≠ 0
    rw [hF1]
    exact one_ne_zero
  · intro a b v hl hne
    have := (evaluation_raising_lowering lev F v.1 hFe hF1 (hWE _ v.2) a b hl).1
    have h0 := (hder a b hl).1
    show (e1 DR a b v.1).1 1 = 0
    rw [this, h0, if_neg hne, zero_mul]
  · intro a v
    have := (evaluation_raising_lowering lev F v.1 hFe hF1 (hWE _ v.2) a a le_rfl).1
    have h0 := (hder a a le_rfl).1
    show (e1 DR a a v.1).1 1 = _ * v.1.1 1
    rw [this, h0, if_pos rfl]
  · intro a b v hl hne
    have := (evaluation_raising_lowering lev F v.1 hFe hF1 (hWE _ v.2) a b hl).2
    have h0 := (hder a b hl).2
    show (-(e2 DR b a v.1)).1 1 = 0
    simp only [e2, neg_neg, LinearMap.neg_apply]
    rw [this, h0, if_neg hne, zero_mul]
  · intro a v
    have := (evaluation_raising_lowering lev F v.1 hFe hF1 (hWE _ v.2) a a le_rfl).2
    have h0 := (hder a a le_rfl).2
    show (-(e2 DR a a v.1)).1 1 = _ * v.1.1 1
    simp only [e2, neg_neg, LinearMap.neg_apply]
    rw [this, h0, if_pos rfl]
  · intro S fdS stS ev0 w hw
    haveI := fdS
    have hS := GlobalTheory.T.eq_zero_on_unitary_of_vanish_at_one n (S.map (cyc F).subtype) inferInstance (by
        intro a b u hu
        obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.1 hu
        exact Submodule.mem_map.2 ⟨kF F1 F2 a b v, stS a b v hv, rfl⟩) (by
        intro u hu
        obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.1 hu
        exact ev0 v hv) w.1 (Submodule.mem_map.2 ⟨w, hw, rfl⟩)
    exact Subtype.ext (hzero w.1 w.2 hS)

end GlobalTheory.CompanionTheory.ModelS
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealModelExistsStatement
theorem _root_.GlobalTheory.T.real_model_exists : PositivityTheory.RgBcC.RealD.ModelEx :=
  GlobalTheory.CompanionTheory.ModelS.modelEx_main
end
