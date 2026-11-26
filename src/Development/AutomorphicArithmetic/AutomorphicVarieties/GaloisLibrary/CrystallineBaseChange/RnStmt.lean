module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.HfStmt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CuspCritAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.HasPairingOfHerm

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.RnStmt
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual Polynomial MeasureTheory
open GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Nf UpperTheory.V.Sd CongruenceSubgroup
open UpperHalfPlane hiding I
open scoped Matrix MatrixGroups ModularForm Manifold

namespace UpperTheory.V.Br

structure IsLow (k : ℕ) (φ : TR.Sm ℚ 2) : Prop where
  wt : ∀ v, TR.Eop v 0 1 φ - TR.Eop v 1 0 φ = (Complex.I * k) • φ
  low : ∀ v, TR.Eop v 0 0 φ - TR.Eop v 1 1 φ = Complex.I • (TR.Eop v 0 1 φ + TR.Eop v 1 0 φ)
  one : ∀ v, TR.Eop v 0 0 φ + TR.Eop v 1 1 φ = 0

def CapTwo : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (π : TR.CuspSub F 2) (v : InfinitePlace F) (a b : ℂ), π.HasInfChar v {a, b} →
    ∀ φ ∈ π.V, TR.Eop v 0 0 φ + TR.Eop v 1 1 φ = (a + b) • φ ∧
      TR.Eop v 0 0 (TR.Eop v 0 0 φ) + TR.Eop v 0 1 (TR.Eop v 1 0 φ) + TR.Eop v 1 0 (TR.Eop v 0 1 φ) + TR.Eop v 1 1 (TR.Eop v 1 1 φ) =
        (a ^ 2 + b ^ 2 - 1 / 2) • φ

def WtVec : Prop :=
  ∀ π : TR.CuspSub ℚ 2, ∃ φ ∈ π.V, φ ≠ 0 ∧ ∃ n : ℤ, ∀ v, TR.Eop v 0 1 φ - TR.Eop v 1 0 φ = (Complex.I * n) • φ

def Sl2Low : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (W R L : Module.End ℂ V) (H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (k : ℕ), 3 ≤ k →
    W * R - R * W = (2 : ℂ) • R → W * L - L * W = (-2 : ℂ) • L → (4 : ℂ) • (R * L) = ((k : ℂ) * (k - 2)) • 1 - (W * W - (2 : ℂ) • W) →
    (4 : ℂ) • (L * R) = ((k : ℂ) * (k - 2)) • 1 - (W * W + (2 : ℂ) • W) →
    (∀ x, H x x = 0 → x = 0) → (∀ x y, H (W x) y = H x (W y)) → (∀ x y, H (R x) y = -H x (L y)) → (∀ x y, H (L x) y = -H x (R y)) →
    (∃ x, x ≠ 0 ∧ ∃ n : ℤ, W x = (n : ℂ) • x) →
    ∃ x, x ≠ 0 ∧ ((W x = (k : ℂ) • x ∧ L x = 0) ∨ (W x = (-(k : ℂ)) • x ∧ R x = 0))

def HolVec : Prop :=
  ∀ (k : ℕ), 3 ≤ k → ∀ π : TR.CuspSub ℚ 2, (∀ v, π.HasInfChar v {((k : ℂ) - 1) / 2, -(((k : ℂ) - 1) / 2)}) →
    ∀ H, Gk.IsHerm π H → ∃ φ ∈ π.V, φ ≠ 0 ∧ IsLow k φ

def LevelVec : Prop :=
  ∀ (k : ℕ) (π : TR.CuspSub ℚ 2), (∃ φ ∈ π.V, φ ≠ 0 ∧ IsLow k φ) →
    ∃ (N : ℕ) (ψ : DirichletCharacter ℂ N) (ν : HChar ℚ), 1 ≤ N ∧ IsDirOf ψ ν ∧
      ∃ φ ∈ (π.twist ν).V, φ ≠ 0 ∧ IsLow k φ ∧ ∀ u ∈ K1G N, TR.finRep ℚ 2 u φ = φ

def CharOf : Prop :=
  ∀ (N : ℕ), 1 ≤ N → ∀ (ω : HChar ℚ) (φ : TR.Sm ℚ 2), φ ≠ 0 → (∀ v, TR.Eop v 0 0 φ + TR.Eop v 1 1 φ = 0) →
    (∀ u ∈ K1G N, TR.finRep ℚ 2 u φ = φ) →
    (∀ (z : Ideles ℚ) (g : GA ℚ 2), φ.1 (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω.1 z : ℂˣ) : ℂ) * φ.1 g) →
    ∃ χ : DirichletCharacter ℂ N, IsDirOf χ ω

def down (k : ℕ) (φ : GA ℚ 2 → ℂ) (z : ℍ) : ℂ :=
  ((z.im ^ (-((k : ℝ) / 2)) : ℝ) : ℂ) * φ (upR (aff (Units.mk0 z.im z.im_pos.ne') z.re))

def DownLift : Prop :=
  ∀ (k N : ℕ), 1 ≤ N → ∀ φ : TR.Sm ℚ 2, (∀ γ g, φ.1 (ratGL ℚ 2 γ * g) = φ.1 g) → IsLow k φ → (∀ u ∈ K1G N, TR.finRep ℚ 2 u φ = φ) →
    Nf.IsLift k N (down k φ.1) φ.1

def DownHol : Prop := ∀ (k : ℕ) (φ : TR.Sm ℚ 2), IsLow k φ → MDiff (down k φ.1)

def DownChar : Prop :=
  ∀ (k N : ℕ), 1 ≤ N → ∀ (χ : DirichletCharacter ℂ N) (ω : HChar ℚ), IsDirOf χ ω → ∀ (f : ℍ → ℂ) (φ : GA ℚ 2 → ℂ), Nf.IsLift k N f φ →
    (∀ (z : Ideles ℚ) (g : GA ℚ 2), φ (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω.1 z : ℂˣ) : ℂ) * φ g) → HasChar k χ f

def PerZero : Prop :=
  ∀ (f : ℍ → ℂ) (N : ℕ), 0 < N → MDiff f → (∀ z : ℍ, f ((N : ℝ) +ᵥ z) = f z) →
    (∃ (C : ℝ) (m : ℕ), ∀ z : ℍ, 1 ≤ z.im → |z.re| ≤ N → ‖f z‖ ≤ C * z.im ^ m) →
    (∀ z : ℍ, ∫ t in (0 : ℝ)..N, f (t +ᵥ z) = 0) → IsZeroAtImInfty f

def CuspMean : Prop :=
  ∀ φ : TR.Sm ℚ 2, TR.IsCuspForm φ → ∀ g, ∃ N : ℕ, 0 < N ∧ ∀ y : GL (Fin 2) ℝ,
    Function.Periodic (fun t : ℝ => φ.1 (upR (aff 1 t) * (g * upR y))) N ∧ ∫ t in (0 : ℝ)..N, φ.1 (upR (aff 1 t) * (g * upR y)) = 0

def DownZero : Prop := ∀ (k : ℕ) (φ : TR.Sm ℚ 2), TR.IsCuspForm φ → IsLow k φ → IsZeroAtImInfty (down k φ.1)

def Deadel : Prop :=
  ∀ (k N : ℕ), 1 ≤ N → ∀ (χ : DirichletCharacter ℂ N) (ω : HChar ℚ), IsDirOf χ ω → ∀ φ : TR.Sm ℚ 2, TR.IsCuspForm φ → IsLow k φ →
    (∀ u ∈ K1G N, TR.finRep ℚ 2 u φ = φ) →
    (∀ (z : Ideles ℚ) (g : GA ℚ 2), φ.1 (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω.1 z : ℂˣ) : ℂ) * φ.1 g) →
    ∃ f : CuspForm (Gamma1 N) (k : ℤ), HasChar k χ f ∧ Nf.IsLift k N f φ.1

def UOfSat : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (w : Pl F) (V : Type) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin 2) (w.adicCompletion F)) V) (x : V) (α β : ℂˣ), GlobalTheory.LFun.IsSatVecGL w ρ x {α, β} →
    Uop w ρ 0 x = ((((normV w : ℝ) ^ ((1 : ℝ) / 2) : ℝ) : ℂ) * ((α : ℂ) + β)) • x ∧
    ρ (Matrix.GeneralLinearGroup.scalar (Fin 2) (atFin w (unif w))) x = ((α * β : ℂˣ) : ℂ) • x

def EigOf : Prop :=
  ∀ (k N : ℕ), 1 ≤ k → 1 ≤ N → ∀ (χ : DirichletCharacter ℂ N) (ω : HChar ℚ), IsDirOf χ ω → ∀ (f : CuspForm (Gamma1 N) (k : ℤ))
    (φ : TR.Sm ℚ 2), Nf.IsLift k N f φ.1 → IsHol k (lev N) ω φ → ∀ (w : Pl ℚ) (α β : ℂˣ), ¬ normV w ∣ N →
    GlobalTheory.LFun.IsSatVecGL w (locSm ℚ w) φ {α, β} →
    IsEigAt k χ f (normV w) ((((normV w : ℝ) ^ (((k : ℝ) - 1) / 2) : ℝ) : ℂ) * ((α : ℂ) + β)) ∧ ((α * β : ℂˣ) : ℂ) = χ (normV w : ZMod N)

def EigEx : Prop :=
  ∀ (N k : ℕ) [NeZero N], 1 ≤ k → ∀ (χ : DirichletCharacter ℂ N) (f : CuspForm (Gamma1 N) (k : ℤ)), HasChar k χ f → f ≠ 0 → ∀ a : ℕ → ℂ,
    ∃ g : Eigenform k N χ, ∀ p : ℕ, p.Prime → IsEigAt k χ f p (a p) → g.a p = a p

def ClTwist : Prop :=
  ∀ (N k : ℕ) [NeZero N] (χ ψ : DirichletCharacter ℂ N) (f : CuspForm (Gamma1 N) (k : ℤ)), HasChar k χ f →
    ∃ g : CuspForm (Gamma1 (N * N)) (k : ℤ), HasChar k (DirichletCharacter.changeLevel (dvd_mul_right N N) (χ * ψ ^ 2)) g ∧
      ∀ n : ℕ, coef g n = ψ (n : ZMod N) * coef f n

def MinNew : Prop :=
  ∀ (N k : ℕ) [NeZero N], 1 ≤ k → ∀ (χ : DirichletCharacter ℂ N) (g : Eigenform k N χ),
    ∃ (f : Newform k) (_ : NeZero f.M) (h : Eigenform k f.M f.χ), h.f = f.f ∧ ∀ᶠ p : ℕ in Filter.cofinite, p.Prime → h.a p = g.a p

def CharEq : Prop :=
  ∀ (k N M : ℕ) [NeZero N] [NeZero M], 2 ≤ k → ∀ (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M) (g : Eigenform k N χ)
    (h : Eigenform k M ψ), (∀ᶠ p : ℕ in Filter.cofinite, p.Prime → h.a p = g.a p) →
    ∀ᶠ p : ℕ in Filter.cofinite, p.Prime → χ (p : ZMod N) = ψ (p : ZMod M)

def RepEig : Prop :=
  ∀ (k : ℕ), 3 ≤ k → ∀ π : TR.CuspSub ℚ 2, (∀ v, π.HasInfChar v {((k : ℂ) - 1) / 2, -(((k : ℂ) - 1) / 2)}) →
    ∃ (N : ℕ) (_ : NeZero N) (χ : DirichletCharacter ℂ N) (g : Eigenform k N χ), ∀ᶠ w : Pl ℚ in Filter.cofinite, ∃ α β : ℂˣ,
      π.HasSat w {α, β} ∧ g.a (normV w) = (((normV w : ℝ) ^ (((k : ℝ) - 1) / 2) : ℝ) : ℂ) * ((α : ℂ) + β) ∧
        ((α * β : ℂˣ) : ℂ) = χ (normV w : ZMod N)

def RepNewAE : Prop :=
  ∀ (k : ℕ), 3 ≤ k → ∀ (j : ℤ) (π : TR.CuspSub ℚ 2), (∀ v, π.HasInfChar v {1 / 2 + (j : ℂ), 3 / 2 - (k : ℂ) + (j : ℂ)}) →
    ∃ f : Newform k, ∀ᶠ w : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, ∃ B, π.HasSat w B ∧
      ((algSat 2 (normV w) B).map fun b => X - C ((normV w : ℂ) ^ j * b)).prod = f.heckePoly (normV w)

end UpperTheory.V.Br
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.RotEig
open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix UpperTheory.V

namespace UpperTheory.V.Br.RotationEigenvalues

variable {F : Type} [Field F] [NumberField F]

private noncomputable def rot (θ : TR.Rinf F) : TR.Kinf F 2 :=
  ⟨!![fun v => Real.cos (θ v), fun v => Real.sin (θ v); fun v => -Real.sin (θ v), fun v => Real.cos (θ v)], by
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j v
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_apply] <;>
      nlinarith [Real.sin_sq_add_cos_sq (θ v)]⟩

omit [NumberField F] in
private theorem rot_add (θ η : TR.Rinf F) : rot (θ + η) = rot θ * rot η := by
  ext i j v
  fin_cases i <;> fin_cases j <;> simp [rot, Matrix.mul_apply, Fin.sum_univ_succ, Real.cos_add, Real.sin_add] <;> ring

omit [NumberField F] in
private theorem rot_zero : rot (0 : TR.Rinf F) = 1 := by
  ext i j v
  fin_cases i <;> fin_cases j <;> simp [rot]

variable [IsTotallyReal F]

private theorem rot_eig (φ : TR.Sm F 2) (z : ℂ) (h : ∀ v, TR.Eop v 0 1 φ - TR.Eop v 1 0 φ = z • φ) (g : GA F 2) (θ : TR.Rinf F) :
    φ.1 (g * TR.infGL F 2 (Unitary.toUnits (rot θ))) = Complex.exp (z * ∑ v, (θ v : ℂ)) * φ.1 g := by
  classical
  set μ : ℂ := z * ∑ v, (θ v : ℂ) with hμ
  let X : TR.Lie F 2 := TR.toL !![0, θ; -θ, 0]
  have hX : X = ∑ v, θ v • (TR.toL (Matrix.single 0 1 (Pi.single v 1)) - TR.toL (Matrix.single 1 0 (Pi.single v 1))) := by
    ext i j u
    fin_cases i <;> fin_cases j <;> simp [X, Finset.sum_apply, Pi.single_apply]
  have hL : TR.lie F 2 X φ = μ • φ := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hX, map_sum, LinearMap.sum_apply, hμ, Finset.mul_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [map_smul, map_sub, LinearMap.smul_apply, LinearMap.sub_apply, mul_comm, mul_smul, Complex.coe_smul, ← h v]
    simp only [TR.Eop]
  have hc : HasDerivAt (fun t : ℝ => TR.toL (Unitary.toUnits (rot (t • θ))).val) X 0 := by
    refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun v => ?_
    have h1 : HasDerivAt (fun t : ℝ => t * θ v) (θ v) 0 := by simpa using (hasDerivAt_id (0 : ℝ)).mul_const (θ v)
    fin_cases i <;> fin_cases j
    · simpa [X, rot] using h1.cos
    · simpa [X, rot] using h1.sin
    · simpa [X, rot] using h1.sin.fun_neg
    · simpa [X, rot] using h1.cos
  let f : ℝ → ℂ := fun t => φ.1 (g * TR.infGL F 2 (Unitary.toUnits (rot (t • θ))))
  have hf : ∀ t, HasDerivAt f (μ * f t) t := fun t => by
    have h1 := TR.hasDerivAt_curve φ (g * TR.infGL F 2 (Unitary.toUnits (rot (t • θ)))) (fun s => Unitary.toUnits (rot (s • θ))) X
      (by rw [zero_smul, rot_zero, map_one]) hc
    rw [← TR.lie_apply, hL] at h1
    have h2 : HasDerivAt (fun s => f (t + s)) (μ * f t) 0 := by
      simpa only [f, add_smul, rot_add, map_mul, mul_assoc] using! h1
    have h3 := HasDerivAt.comp_sub_const t t (f := fun s => f (t + s)) (by rw [sub_self]; exact h2)
    simpa using h3
  have hg : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Complex.exp (-μ * s) * f s) 0 t := fun t => by
    have h1 : HasDerivAt (fun s : ℝ => -μ * (s : ℂ)) (-μ) t := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (-μ)
    exact (h1.cexp.fun_mul (hf t)).congr_deriv (by ring)
  have h4 := is_const_of_deriv_eq_zero (fun t => (hg t).differentiableAt) (fun t => (hg t).deriv) 1 0
  simp only [f, one_smul, zero_smul, rot_zero, map_one, mul_one, Complex.ofReal_one, Complex.ofReal_zero, mul_zero,
    Complex.exp_zero, one_mul] at h4
  rw [← h4, ← mul_assoc, ← Complex.exp_add]
  simp

end UpperTheory.V.Br.RotationEigenvalues

open UpperTheory.V.Br.RotationEigenvalues in
theorem UpperTheory.V.Br.rotEig :
    UpperTheory.V.Br.RotEig := by
  intro F _ _ _ φ z hφ θ h hh g
  have e : h = Unitary.toUnits (rot θ) := Units.ext hh
  rw [e]
  exact rot_eig φ z hφ g θ
end
