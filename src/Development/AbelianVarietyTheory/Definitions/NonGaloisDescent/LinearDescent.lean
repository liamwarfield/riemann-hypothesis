module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FiniteCocycles

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
noncomputable section

namespace GlobalTheory.UnitLemma

open Polynomial Filter Topology

namespace InvAlg

variable {K : UQ} (B : InvAlg K)

def UU (x w : B.A) : ℕ := Nat.card {L : B.X x // w ∈ (L : Submodule K.O B.A)}

def Lin : Set (Submodule K.O B.A) :=
  {M | IsLat K.O K.E M ∧ (∀ y ∈ M, B.g * y ∈ M) ∧ ∀ y ∈ M, B.σ y ∈ M}

def sgnLat (M : Submodule K.O B.A) : ℚ :=
  let m : Fin (Module.finrank K.E B.A) → B.A :=
    Classical.epsilon fun m => Submodule.span K.O (Set.range m) = M
  K.eta (Matrix.of fun k l : Fin (Module.finrank K.E B.A) =>
    Algebra.trace K.E B.A (B.g ^ (k : ℕ) * m l)).det

def GG (u : B.A) : ℚ :=
  ∑ᶠ M ∈ {M ∈ B.Lin | u ∈ M ∧ ∀ z ∈ M, Algebra.trace K.E B.A z ∈ (algebraMap K.O K.E).range}, B.sgnLat M

def rho (w : B.A) : ℕ :=
  Nat.card {k : B.T ⧸ (intUnits K.O B.A).subgroupOf B.T //
    IsIntegral K.O ((((Quotient.out k : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * w : B.A)}

def LieReg : Prop := B.σ B.g = B.g ∧ B.P.Separable

def Plus (x : B.A) : Prop := IsUnit x ∧ B.σ x = x

def LinLim (a : K.O) (x : B.A) (ℓ : ℝ) : Prop :=
  Tendsto (fun k : ℕ => (B.GG (x * algebraMap K.O B.A a ^ (2 * k)) : ℝ) / (B.rho (algebraMap K.O B.A a ^ k) : ℝ))
    atTop (𝓝 ℓ)

end InvAlg

def UQ.Small (K : UQ) (a : K.O) : Prop :=
  a ≠ 0 ∧ a ∈ IsLocalRing.maximalIdeal K.O ∧ K.c (algebraMap K.O K.E a) = algebraMap K.O K.E a

def CountIdentity : Prop :=
  ∀ (K : UQ) (B : InvAlg K), B.LieReg → ∀ x w : B.A, B.Plus x → IsUnit w →
    B.GG (x * (w * B.σ w)) = (B.UU x w : ℚ)

def UnitaryLimit : Prop :=
  ∀ (K : UQ) (B : InvAlg K), B.LieReg → ∀ a : K.O, K.Small a → ∀ x : B.A, B.Plus x →
    Tendsto (fun k : ℕ => (B.UU x (algebraMap K.O B.A a ^ k) : ℝ) / (B.rho (algebraMap K.O B.A a ^ k) : ℝ))
      atTop (𝓝 (B.N x : ℝ))

def LinearDescent : Prop :=
  ∀ (K : UQ) (B₁ B₂ : InvAlg K), B₁.σ B₁.g = B₁.g → B₂.σ B₂.g = B₂.g → (B₁.P * B₂.P).Separable →
    ∀ a : K.O, K.Small a → ∀ (ℓ : (B₁.prod B₂).A → ℝ) (ℓ₁ : B₁.A → ℝ) (ℓ₂ : B₂.A → ℝ),
    (∀ x, (B₁.prod B₂).Plus x → (B₁.prod B₂).LinLim a x (ℓ x)) →
    (∀ x, B₁.Plus x → B₁.LinLim a x (ℓ₁ x)) → (∀ x, B₂.Plus x → B₂.LinLim a x (ℓ₂ x)) →
    ∑ᶠ k : (B₁.prod B₂).Cl, (K.eta (Algebra.norm K.E (InvAlg.Cl.rep k).1) : ℝ) * ℓ k.rep =
      (-(K.q : ℝ)) ^ (val K.O (resultant B₁.P B₂.P)) *
        ((∑ᶠ k : B₁.Cl, (K.eta (Algebra.norm K.E k.rep) : ℝ) * ℓ₁ k.rep) * ∑ᶠ k : B₂.Cl, ℓ₂ k.rep)

end GlobalTheory.UnitLemma
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR

def fourB {V : Type} [MeasurableSpace V] (μ : Measure V) (B : V → V → ℂ) (f : V → ℂ) (y : V) : ℂ :=
  ∫ x, f x * B x y ∂μ

def SelfDual {V : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] (μ : Measure V)
    (B : V → V → ℂ) : Prop :=
  μ.IsAddHaarMeasure ∧ ∀ f : V → ℂ, IsTest f → ∀ y, fourB μ B (fourB μ B f) y = f (-y)

def IsTestRep {G X : Type} [Group G] [TopologicalSpace X] (W : G → (X → ℂ) → X → ℂ) : Prop :=
  (∀ g f, IsTest f → IsTest (W g f)) ∧ (∀ f, IsTest f → W 1 f = f) ∧
    (∀ g h f, IsTest f → W (g * h) f = W g (W h f)) ∧
    ∀ g (c : ℂ) f f', IsTest f → IsTest f' → W g (c • f + f') = c • W g f + W g f'

def nS {k : Type} [CommRing k] (z : k) : SpecialLinearGroup (Fin 2) k := ⟨!![1, z; 0, 1], by simp [Matrix.det_fin_two]⟩

def mS {k : Type} [CommRing k] (s : kˣ) : SpecialLinearGroup (Fin 2) k :=
  ⟨!![(s : k), 0; 0, ((s⁻¹ : kˣ) : k)], by simp [Matrix.det_fin_two]⟩

def wS (k : Type) [CommRing k] : SpecialLinearGroup (Fin 2) k := ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩

structure Et (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] where
  K : Type
  L : Type
  [crK : CommRing K]
  [algK : Algebra F K]
  [finK : Module.Finite F K]
  [redK : IsReduced K]
  [topK : TopologicalSpace K]
  [mtK : IsModuleTopology F K]
  [trK : IsTopologicalRing K]
  [lcK : LocallyCompactSpace K]
  [mK : MeasurableSpace K]
  [bK : BorelSpace K]
  [crL : CommRing L]
  [stL : StarRing L]
  [algFL : Algebra F L]
  [algKL : Algebra K L]
  [algEL : Algebra E L]
  [twK : IsScalarTower F K L]
  [twE : IsScalarTower F E L]
  [topL : TopologicalSpace L]
  [mtL : IsModuleTopology F L]
  [mL : MeasurableSpace L]
  [bL : BorelSpace L]
  push : Algebra.IsPushout F E K L
  star_K : ∀ x : K, star (algebraMap K L x) = algebraMap K L x
  star_E : ∀ y : E, star (algebraMap E L y) = algebraMap E L (star y)

attribute [instance] Et.crK Et.algK Et.finK Et.redK Et.topK Et.mtK Et.trK Et.lcK Et.mK Et.bK Et.crL Et.stL Et.algFL
  Et.algKL Et.algEL Et.twK Et.twE Et.topL Et.mtL Et.mL Et.bL

namespace Et
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  (A : Et F E)

def absK (t : A.K) : ℝ := by
  classical exact if h : IsUnit t then (distribHaarChar A.K h.unit : ℝ) else 0

def etaK (t : A.K) : ℂ := eta (Algebra.norm F t)

def psiK (ψ : AddChar F ℂ) (t : A.K) : ℂ := ψ (Algebra.trace F A.K t)

def NL (y : A.L) : A.K := Algebra.norm A.K y

def kerK (ψ : AddChar F ℂ) (y y' : A.K) : ℂ := A.psiK ψ (y * y')

def kerL (ψ : AddChar F ℂ) (x : A.K) (y' y : A.L) : ℂ := A.psiK ψ (x * Algebra.trace A.K A.L (star y' * y))

def orbK (μK : Measure A.K) (φ' : A.K × A.K → ℂ) (a : A.K) : ℂ :=
  ∫ t in {t : A.K | IsUnit t}, φ' (a * Ring.inverse t, t) * A.etaK t * ((A.absK t : ℂ))⁻¹ ∂μK

def fourK (μK : Measure A.K) (ψ : AddChar F ℂ) (φ' : A.K × A.K → ℂ) (p : A.K × A.K) : ℂ :=
  ∫ b', ∫ c', φ' (b', c') * A.psiK ψ (p.1 * c' + b' * p.2) ∂μK ∂μK

def orbL (ν : Measure (unitary A.L)) (φ : A.L → ℂ) (y₀ : A.L) : ℂ := ∫ t : unitary A.L, φ (t.1 * y₀) ∂ν

def IsNat (μK : Measure A.K) (μL : Measure A.L) (ν : Measure (unitary A.L)) : Prop :=
  ν.IsHaarMeasure ∧ ∀ (s : A.K → A.L), (∀ y : A.L, IsUnit y → A.NL (s (A.NL y)) = A.NL y) →
    ∀ h : A.L → ℂ, IsTest h → tsupport h ⊆ {y | IsUnit y} →
      ∫ y, h y * ((A.absK (A.NL y) : ℂ))⁻¹ ∂μL =
        ∫ a in {a : A.K | ∃ y : A.L, IsUnit y ∧ A.NL y = a}, A.orbL ν h (s a) * ((A.absK a : ℂ))⁻¹ ∂μK

structure Meas (ψ : AddChar F ℂ) where
  μK : Measure A.K
  μL : A.Kˣ → Measure A.L
  ν : Measure (unitary A.L)
  sdK : SelfDual μK (A.kerK ψ)
  sdL : ∀ x : A.Kˣ, SelfDual (μL x) (A.kerL ψ x)
  nat : A.IsNat μK (μL 1) ν

def IsWeil (ψ : AddChar F ℂ) (x : A.K) (ω : A.K → ℂ) (μ : Measure A.L) (γ : ℂ)
    (W : SpecialLinearGroup (Fin 2) A.K → (A.L → ℂ) → A.L → ℂ) : Prop :=
  IsTestRep W ∧ ∀ φ, IsTest φ →
    (∀ z y, W (nS z) φ y = A.psiK ψ (z * x * A.NL y) * φ y) ∧
    (∀ (s : A.Kˣ) y, W (mS s) φ y = ω s * (A.absK s : ℂ) * φ ((s : A.K) • y)) ∧
    ∀ y, W (wS A.K) φ y = γ * fourB μ (A.kerL ψ x) φ y

def OK : Set A.K := {z | ∀ i, ‖(LinearMap.charpoly (Algebra.lmul F A.K z)).coeff i‖ ≤ 1}

def InI (Φ : SpecialLinearGroup (Fin 2) A.K → ℂ) : Prop :=
  (∃ U ∈ 𝓝 (0 : A.K), ∀ g k : SpecialLinearGroup (Fin 2) A.K,
      (∀ i j, ((k : Matrix (Fin 2) (Fin 2) A.K) - 1) i j ∈ U) → Φ (g * k) = Φ g) ∧
    ∀ z (s : A.Kˣ) g, Φ (nS z * mS s * g) = A.etaK s * (A.absK s : ℂ) * Φ g

def abelian₂ (μK : Measure A.K) (ψ : AddChar F ℂ) (a : A.K) (Φ : SpecialLinearGroup (Fin 2) A.K → ℂ) (c : F) : ℂ :=
  ∫ z in {z : A.K | c • z ∈ A.OK}, Φ (wS A.K * nS z) * A.psiK ψ (-(a * z)) ∂μK

def tilde (μK : Measure A.K) (ψ : AddChar F ℂ) (φ' : A.K × A.K → ℂ) (c u : A.K) : ℂ :=
  ∫ b, φ' (b, c) * A.psiK ψ (u * b) ∂μK

def jHyp (μK : Measure A.K) (ψ : AddChar F ℂ) (φ' : A.K × A.K → ℂ) (g : SpecialLinearGroup (Fin 2) A.K) : ℂ :=
  ∫ t, A.tilde μK ψ φ' (t * g 1 0) (t * g 1 1) * A.etaK t ∂μK

def IsIsom {r : ℕ} (x : A.K) (j : A.L ≃ₗ[E] (Fin r → E)) : Prop :=
  ∀ y y', star (j y) ⬝ᵥ j y' = Algebra.trace E A.L (algebraMap A.K A.L x * star y * y')

def IsReps (S : Set A.Kˣ) : Prop := ∀ a : A.Kˣ, ∃! x : A.Kˣ, x ∈ S ∧ ∃ y : A.L, IsUnit y ∧ (a : A.K) = x * A.NL y

def IsGen {r : ℕ} (τ : A.K) (p : Fin r → F) : Prop :=
  LinearIndependent F (fun i : Fin r => τ ^ (i : ℕ)) ∧ Module.finrank F A.K = r ∧
    τ ^ r + ∑ i, p i • τ ^ (i : ℕ) = 0

def invK {r : ℕ} (τ : A.K) (p : Fin r → F) (lam : F) (a : A.K) : Inv r F :=
  (p, fun i => Algebra.trace F A.K (τ ^ (i : ℕ) * a), lam)

end Et

def WeilField : Prop :=
  ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E]
    (A : Et F E), IsField A.K → IsField A.L → ∀ (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (x : A.Kˣ) (μ : Measure A.L),
    SelfDual μ (A.kerL ψ x) → ∀ ω : A.K → ℂ,
    (∀ s : A.Kˣ, ((∃ y, A.NL y = s) → ω s = 1) ∧ ((¬ ∃ y, A.NL y = s) → ω s = -1)) →
    ∃ γ W, A.IsWeil ψ x ω μ γ W

def WeilEt : Prop :=
  ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E]
    (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (x : A.Kˣ) (μ : Measure A.L),
    SelfDual μ (A.kerL ψ x) → ∃ γ W, A.IsWeil ψ x A.etaK μ γ W

def RankOne : Prop :=
  ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E]
    (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (m : A.Meas ψ) (S : Set A.Kˣ), A.IsReps S →
    ∀ (γ : A.Kˣ → ℂ) (W : A.Kˣ → SpecialLinearGroup (Fin 2) A.K → (A.L → ℂ) → A.L → ℂ),
    (∀ x ∈ S, A.IsWeil ψ x A.etaK (m.μL x) (γ x) (W x)) →
    ∀ (φ' : A.K × A.K → ℂ) (φ : A.Kˣ → A.L → ℂ) (κ : ℂ), IsTest φ' → (∀ x ∈ S, IsTest (φ x)) →
    (∀ x ∈ S, ∀ y : A.L, IsUnit y → κ * A.orbK m.μK φ' (x * A.NL y) = A.orbL m.ν (φ x) y) →
    ∀ x ∈ S, ∀ y : A.L, IsUnit y →
      κ * A.orbK m.μK (A.fourK m.μK ψ φ') (x * A.NL y) =
        γ x * A.orbL m.ν (fourB (m.μL x) (A.kerL ψ x) (φ x)) y

def GammaOne : Prop :=
  ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E]
    (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (x : A.Kˣ) (μ : Measure A.L), SelfDual μ (A.kerL ψ x) →
    ∀ (ω : A.K → ℂ) (γ : ℂ) W, A.IsWeil ψ x ω μ γ W → ∀ (r : ℕ) (j : A.L ≃ₗ[E] (Fin r → E)), A.IsIsom x j → γ = 1

end GlobalTheory.JR
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemCentIffTwConj
open Matrix

noncomputable section

namespace GlobalTheory.Tw.Model

variable {n : ℕ} {R : Type} [CommRing R] [StarRing R]

omit [StarRing R] in
theorem Phi_apply' (i j : Fin n) : Phi n R i j = if j = i.rev then (-1) ^ (i : ℕ) else 0 := by
  simp only [Phi, Matrix.of_apply]
  congr 1
  apply propext
  rw [Fin.ext_iff, Fin.val_rev]
  have := i.2
  have := j.2
  omega

omit [StarRing R] in
theorem Phi_mul_transpose : Phi n R * (Phi n R)ᵀ = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Phi_apply', ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Fin.rev_inj, Matrix.one_apply]
  split_ifs with h
  · subst h
    rw [← pow_add, ← two_mul, pow_mul]; simp
  · simp

omit [StarRing R] in
theorem transpose_mul_Phi : (Phi n R)ᵀ * Phi n R = 1 := mul_eq_one_comm.mp Phi_mul_transpose

theorem Phi_conjTranspose : (Phi n R)ᴴ = (Phi n R)ᵀ := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply, Phi_apply']
  split_ifs <;> simp

omit [StarRing R] in
theorem Phi_transpose : (Phi n R)ᵀ = ((-1 : R) ^ (n - 1)) • Phi n R := by
  ext i j
  simp only [Matrix.transpose_apply, Matrix.smul_apply, Phi, Matrix.of_apply, smul_eq_mul]
  by_cases h : (i : ℕ) + (j : ℕ) + 1 = n
  · rw [if_pos h, if_pos (by omega)]
    have : n - 1 = i + j := by omega
    rw [this, ← pow_add, show (i : ℕ) + j + i = 2 * i + j by ring, pow_add, pow_mul]; simp
  · rw [if_neg h, if_neg (by omega)]; simp

theorem theta_one : theta (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  simp [theta, Phi_mul_transpose]

theorem theta_mul (g h : Matrix (Fin n) (Fin n) R) : theta (g * h) = theta g * theta h := by
  simp only [theta, Matrix.mul_inv_rev, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Phi n R)ᵀ (Phi n R), transpose_mul_Phi, Matrix.one_mul]

theorem theta_mul_theta_inv {g : Matrix (Fin n) (Fin n) R} (hg : IsUnit g) :
    theta g * theta g⁻¹ = 1 := by
  rw [← theta_mul, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det g).mp hg), theta_one]

theorem theta_inv_eq {g : Matrix (Fin n) (Fin n) R} (hg : IsUnit g) :
    (theta g)⁻¹ = Phi n R * gᴴ * (Phi n R)ᵀ := by
  rw [Matrix.inv_eq_right_inv (theta_mul_theta_inv hg), theta,
    Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det g).mp hg)]

theorem theta_theta {g : Matrix (Fin n) (Fin n) R} (hg : IsUnit g) : theta (theta g) = g := by
  rw [theta, theta_inv_eq hg]
  have h2 : ((Phi n R)ᵀ)ᴴ = Phi n R := by rw [← Phi_conjTranspose, conjTranspose_conjTranspose]
  simp only [Matrix.conjTranspose_mul, conjTranspose_conjTranspose, h2, Phi_conjTranspose]
  have hs : ((-1 : R) ^ (n - 1)) * ((-1 : R) ^ (n - 1)) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; simp
  have hP : Phi n R = ((-1 : R) ^ (n - 1)) • (Phi n R)ᵀ := by
    rw [Phi_transpose, smul_smul, hs, one_smul]
  have h3 : Phi n R * Phi n R = ((-1 : R) ^ (n - 1)) • (1 : Matrix (Fin n) (Fin n) R) := by
    conv_lhs => rw [hP]
    nth_rewrite 2 [Phi_transpose]
    rw [smul_smul, hs, one_smul, Matrix.smul_mul, transpose_mul_Phi]
  have h4 : (Phi n R)ᵀ * (Phi n R)ᵀ = ((-1 : R) ^ (n - 1)) • (1 : Matrix (Fin n) (Fin n) R) := by
    rw [← Matrix.transpose_mul, h3]; simp
  calc Phi n R * (Phi n R * (g * (Phi n R)ᵀ)) * (Phi n R)ᵀ
      = (Phi n R * Phi n R) * g * ((Phi n R)ᵀ * (Phi n R)ᵀ) := by simp only [Matrix.mul_assoc]
    _ = g := by rw [h3, h4]; simp [smul_smul, hs]

theorem adj_eq {δ g : Matrix (Fin n) (Fin n) R} (hδ : IsUnit δ) (hg : IsUnit g) :
    adj δ g = (δ * theta g * δ⁻¹)⁻¹ := by
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, theta_inv_eq hg,
    Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det δ).mp hδ), adj]
  simp only [Matrix.mul_assoc]

end GlobalTheory.Tw.Model
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MatMapTmul
noncomputable section

open TensorProduct Polynomial IsLocalRing

namespace GlobalTheory.Pat

namespace Det

variable {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E)

end Det

def lagIdem {R E ι : Type} [CommRing R] [Ring E] [Algebra R E] [Fintype ι] [DecidableEq ι]
    (M : E) (a : ι → R) (i : ι) : E :=
  Ring.inverse (∏ j ∈ Finset.univ.erase i, (a i - a j)) •
    Polynomial.aeval M (∏ j ∈ Finset.univ.erase i, (X - C (a j)))

end GlobalTheory.Pat
end
end
