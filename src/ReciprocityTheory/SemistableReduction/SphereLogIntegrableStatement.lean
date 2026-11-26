module

public import Mathlib

@[expose] public section

section -- merged from ReciprocityTheory.SemistableReduction.SphereLogIntegrableStatement
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory Metric NumberField

abbrev UnitSphereC (n : ℕ) : Type := sphere (0 : EuclideanSpace ℂ (Fin n)) 1

def sphereProb (n : ℕ) : Measure (UnitSphereC n) :=
  ProbabilityTheory.cond (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere Set.univ

instance (n : ℕ) : IsZeroOrProbabilityMeasure (sphereProb n) := by
  unfold sphereProb; infer_instance

def spherePoint {n : ℕ} (z : UnitSphereC n) : Fin n → ℂ :=
  WithLp.ofLp (z : EuclideanSpace ℂ (Fin n))

abbrev BlockSphere (B n : ℕ) : Type := Fin B → UnitSphereC n

def blockSphereProb (B n : ℕ) : Measure (BlockSphere B n) :=
  Measure.pi fun _ => sphereProb n

def blockPoint {B n : ℕ} (z : BlockSphere B n) : Fin B × Fin n → ℂ :=
  fun p => spherePoint (z p.1) p.2

def blockSphereMean (B n : ℕ) (f : MvPolynomial (Fin B × Fin n) ℂ) : ℝ :=
  ∫ z, Real.log ‖MvPolynomial.eval (blockPoint z) f‖ ∂(blockSphereProb B n)

def IsMultiHomogeneous {R : Type*} [CommSemiring R] {B n : ℕ} (a : Fin B → ℕ)
    (f : MvPolynomial (Fin B × Fin n) R) : Prop :=
  ∀ s ∈ f.support, ∀ b : Fin B, ∑ j : Fin n, s (b, j) = a b

def gaussAbs {K : Type*} [Field K] [NumberField K] {ι : Type*} (w : FinitePlace K)
    (f : MvPolynomial ι K) : ℝ :=
  ((f.support.sup fun s => (w (f.coeff s)).toNNReal : NNReal) : ℝ)

def h0 {K : Type*} [Field K] [NumberField K] {B n : ℕ} (f : MvPolynomial (Fin B × Fin n) K) : ℝ :=
  ((∑ᶠ w : FinitePlace K, Real.log (gaussAbs w f)) +
      ∑ σ : K →+* ℂ, blockSphereMean B n (MvPolynomial.map σ f)) / (Module.finrank ℚ K : ℝ)

def SphereLinLogStatement : Prop :=
  ∀ (n : ℕ) (c : EuclideanSpace ℂ (Fin n)), c ≠ 0 →
    Integrable (fun z : UnitSphereC n => Real.log ‖∑ i, WithLp.ofLp c i * spherePoint z i‖)
        (sphereProb n) ∧
      ∫ z, Real.log ‖∑ i, WithLp.ofLp c i * spherePoint z i‖ ∂(sphereProb n) =
        Real.log ‖c‖ - (harmonic (n - 1) : ℝ) / 2

def SJStatement : Prop :=
  ∀ (n a : ℕ) (f : MvPolynomial (Fin n) ℂ) (u : EuclideanSpace ℂ (Fin n)),
    f.IsHomogeneous a → ‖u‖ = 1 → MvPolynomial.eval (WithLp.ofLp u) f ≠ 0 →
    Integrable (fun z : UnitSphereC n => Real.log ‖MvPolynomial.eval (spherePoint z) f‖)
        (sphereProb n) ∧
      Real.log ‖MvPolynomial.eval (WithLp.ofLp u) f‖ - (a : ℝ) / 2 * (harmonic (n - 1) : ℝ) ≤
        ∫ z, Real.log ‖MvPolynomial.eval (spherePoint z) f‖ ∂(sphereProb n)

def SphereLogIntegrableStatement : Prop :=
  ∀ (B n : ℕ) (a : Fin B → ℕ) (f : MvPolynomial (Fin B × Fin n) ℂ),
    f ≠ 0 → IsMultiHomogeneous a f →
    Integrable (fun z => Real.log ‖MvPolynomial.eval (blockPoint z) f‖) (blockSphereProb B n)

def HeightAdditiveStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (B n : ℕ) (a a' : Fin B → ℕ)
    (f g : MvPolynomial (Fin B × Fin n) K),
    0 < n → f ≠ 0 → g ≠ 0 → IsMultiHomogeneous a f → IsMultiHomogeneous a' g →
    h0 (f * g) = h0 f + h0 g ∧ ∀ c : K, c ≠ 0 → h0 (MvPolynomial.C c * f) = h0 f

def HeightLowerBoundStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (B n : ℕ) (a : Fin B → ℕ)
    (f : MvPolynomial (Fin B × Fin n) K),
    0 < n → f ≠ 0 → IsMultiHomogeneous a f →
    -(∑ b, (a b : ℝ) * (Real.log n + 1 / 2)) ≤ h0 f

def torusProb (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi fun _ => volume.restrict (Set.Ioc (0 : ℝ) 1)

def torusPoint {ι : Type*} (θ : ι → ℝ) : ι → ℂ :=
  fun i => Complex.exp (2 * Real.pi * Complex.I * (θ i : ℂ))

def torusMean {ι : Type*} [Fintype ι] (f : MvPolynomial ι ℂ) : ℝ :=
  ∫ θ, Real.log ‖MvPolynomial.eval (torusPoint θ) f‖ ∂(torusProb ι)

def coeffIn {R : Type*} [CommSemiring R] {ι : Type*} (i : ι) (k : ℕ) (f : MvPolynomial ι R) :
    MvPolynomial ι R :=
  ∑ s ∈ f.support.filter (fun s => s i = k), MvPolynomial.monomial (s.erase i) (f.coeff s)

def polyL2 {ι : Type*} (f : MvPolynomial ι ℂ) : ℝ :=
  Real.sqrt (∑ s ∈ f.support, ‖f.coeff s‖ ^ 2)

def polyInner {ι : Type*} (P Q : MvPolynomial ι ℂ) : ℂ :=
  ∑ s ∈ P.support, P.coeff s * star (Q.coeff s)

def TorusMeanBasicStatement : Prop :=
  ∀ (ι : Type) [Fintype ι],
    (∀ f : MvPolynomial ι ℂ, f ≠ 0 →
      Integrable (fun θ => Real.log ‖MvPolynomial.eval (torusPoint θ) f‖) (torusProb ι)) ∧
    (∀ f g : MvPolynomial ι ℂ, f ≠ 0 → g ≠ 0 → torusMean (f * g) = torusMean f + torusMean g) ∧
    (∀ (s : ι →₀ ℕ) (c : ℂ), torusMean (MvPolynomial.monomial s c) = Real.log ‖c‖)

def TorusCoeffStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] (f : MvPolynomial ι ℂ) (i : ι) (k : ℕ), coeffIn i k f ≠ 0 →
    ((∀ k', k < k' → coeffIn i k' f = 0) ∨ (∀ k', k' < k → coeffIn i k' f = 0)) →
    torusMean (coeffIn i k f) ≤ torusMean f

def TorusLexStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] [LinearOrder ι] (f : MvPolynomial ι ℂ) (s : ι →₀ ℕ), s ∈ f.support →
    (∀ t ∈ f.support, t ≠ s → ∃ i, (∀ j < i, s j = t j) ∧ s i < t i) →
    Real.log ‖f.coeff s‖ ≤ torusMean f

def TorusL2Cauchy : Prop :=
  ∀ (ι : Type) [Fintype ι] (f : MvPolynomial ι ℂ),
    (f ≠ 0 → torusMean f ≤ Real.log (polyL2 f)) ∧
    ∀ s : ι →₀ ℕ, ∃ θ : ι → ℝ, ‖f.coeff s‖ ≤ ‖MvPolynomial.eval (torusPoint θ) f‖

def GramStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (F : MvPolynomial ι ℂ) (S : Finset (ι →₀ ℕ)), F ≠ 0 →
    Real.exp (2 * S.card * torusMean F) ≤
      (Matrix.det (Matrix.of fun m m' : S =>
        polyInner (F * MvPolynomial.monomial (m : ι →₀ ℕ) 1)
          (F * MvPolynomial.monomial (m' : ι →₀ ℕ) 1))).re

def SphereLeTorusStatement : Prop :=
  ∀ (B n : ℕ) (a : Fin B → ℕ) (f : MvPolynomial (Fin B × Fin n) ℂ),
    0 < n → f ≠ 0 → IsMultiHomogeneous a f → blockSphereMean B n f ≤ torusMean f

end ReciprocityTheory.MultiplicativeHeights
end
end

section -- merged from ReciprocityTheory.SemistableReduction.TorsionNonvanishStatement
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

def triChar {p : ℕ} (a : Fin p → ℕ) (b : Matrix (Fin p) (Fin p) ℂ) : ℂ :=
  ∏ i, b i i ^ a i

def IsTriEquivariant {p : ℕ} (a : Fin p → ℕ) (P : Matrix (Fin p) (Fin p) ℂ → ℂ) : Prop :=
  ∀ x b : Matrix (Fin p) (Fin p) ℂ, x.det ≠ 0 → b.det ≠ 0 → b.BlockTriangular id →
    P (x * b) = triChar a b * P x

def colNormSq {p : ℕ} (x : Matrix (Fin p) (Fin p) ℂ) (j : Fin p) : ℝ :=
  ∑ i, ‖x i j‖ ^ 2

def LemmaHStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (p : ι → ℕ) (a : ∀ s, Fin (p s) → ℕ)
    (P : (∀ s, Matrix (Fin (p s)) (Fin (p s)) ℂ) → ℂ) (C R : ℝ),
    (∀ (x : ∀ s, Matrix (Fin (p s)) (Fin (p s)) ℂ) (s : ι) (b : Matrix (Fin (p s)) (Fin (p s)) ℂ),
      (∀ t, (x t).det ≠ 0) → b.det ≠ 0 → b.BlockTriangular id →
      P (Function.update x s (x s * b)) = triChar (a s) b * P x) →
    (∀ k : ∀ s, Matrix (Fin (p s)) (Fin (p s)) ℂ,
      (∀ s, k s ∈ Matrix.unitaryGroup (Fin (p s)) ℂ) → ‖P k‖ ≤ C) → 0 ≤ R →
    ∀ x : ∀ s, Matrix (Fin (p s)) (Fin (p s)) ℂ, (∀ s, (x s).det ≠ 0) →
      (∀ s j, colNormSq (x s) j ≤ R ^ 2) → ‖P x‖ ≤ C * R ^ (∑ s, ∑ i, a s i)

def TorsionNonvanishStatement : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (θ : V → ℂ) (Λ : AddSubgroup V) (ρ : ℝ) (n : ℕ),
    Differentiable ℂ θ → (∃ z, θ z ≠ 0) →
    (∀ l ∈ Λ, ∀ z, ‖θ (z + l)‖ * Real.exp (-(Real.pi / 2) * ‖z + l‖ ^ 2) =
      ‖θ z‖ * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2)) →
    (∀ v : V, ∃ l ∈ Λ, ‖v - l‖ ≤ ρ) → 5 * ρ < n →
    ∃ l ∈ Λ, θ ((n : ℂ)⁻¹ • l) ≠ 0

def sgn (p : ℕ) {r : ℕ} (k : Fin r) : ℂ := if (k : ℕ) < p then 1 else -1

def jForm (p : ℕ) {r : ℕ} (x y : Fin r → ℂ) : ℂ :=
  ∑ k, sgn p k * (conj (x k) * y k)

def normSq {r : ℕ} (u : Fin r → ℂ) : ℝ := ∑ k, ‖u k‖ ^ 2

def posSq (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : ℝ :=
  ∑ k : Fin r, if (k : ℕ) < p then ‖u k‖ ^ 2 else 0

def negSq (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : ℝ :=
  ∑ k : Fin r, if (k : ℕ) < p then 0 else ‖u k‖ ^ 2

def approxR (r : ℕ) (μ ρ : ℝ) : ℝ := 4 * Real.sqrt r * μ / ρ

def ApproxGraphStatement : Prop :=
  ∀ (r p : ℕ) (μ ρ : ℝ) (X : Fin r → Fin r → ℂ), p ≤ r → 0 < μ → 0 < ρ → ρ ≤ 1 →
    (∀ j : Fin r, (j : ℕ) < p →
      normSq (X j - (approxR r μ ρ : ℂ) • (Pi.single j 1 : Fin r → ℂ)) ≤ μ ^ 2) →
    (∀ w : Fin r → ℂ, (∀ j : Fin r, p ≤ (j : ℕ) → w j = 0) →
      negSq p (∑ j, w j • X j) ≤ (ρ / 3) ^ 2 * posSq p (∑ j, w j • X j) ∧
      (w ≠ 0 → 0 < posSq p (∑ j, w j • X j))) ∧
    (∀ y : Fin r → ℂ, (∀ j : Fin r, (j : ℕ) < p → jForm p (X j) y = 0) → y ≠ 0 →
      (jForm p y y).re < 0) ∧
    (∀ v y : Fin r → ℂ, (∀ j : Fin r, (j : ℕ) < p → jForm p (X j) y = 0) →
      v - y ∈ Submodule.span ℂ (X '' {j | (j : ℕ) < p}) →
      ‖jForm p y y‖ ≤ 2 * normSq v)

structure HermForm (K : Type) [Field K] [NumberField K] (r : ℕ) where

  c : K →+* K
  c_invol : ∀ x, c (c x) = x
  c_emb : ∀ (σ : K →+* ℂ) (x : K), σ (c x) = conj (σ x)

  G : Matrix (Fin r) (Fin r) K
  G_herm : ∀ a b, c (G a b) = G b a

def HermForm.h {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) (x y : Fin r → K) : K :=
  ∑ a, ∑ b, S.c (x a) * S.G a b * y b

def embVec {K : Type} [Field K] [NumberField K] {r : ℕ} (σ : K →+* ℂ) (x : Fin r → K) : Fin r → ℂ := fun a => σ (x a)

def IsIntegralElt {K : Type} [Field K] [NumberField K] (x : K) : Prop := ∃ z : 𝓞 K, (z : K) = x

def IsLattice {K : Type} [Field K] [NumberField K] {r : ℕ} (L : Submodule (𝓞 K) (Fin r → K)) : Prop :=
  L.FG ∧ Submodule.span K (L : Set (Fin r → K)) = ⊤

def IsIntegralOn {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) (L : Submodule (𝓞 K) (Fin r → K)) : Prop :=
  ∀ x ∈ L, ∀ y ∈ L, IsIntegralElt (S.h x y)

def IsSelfDual {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) (L : Submodule (𝓞 K) (Fin r → K)) : Prop :=
  IsIntegralOn S L ∧ ∀ x, (∀ y ∈ L, IsIntegralElt (S.h x y)) → x ∈ L

def majSq {K : Type} [Field K] [NumberField K] {r : ℕ} {ι : Type} [Fintype ι] (σ : ι → K →+* ℂ) (Q : ι → Matrix (Fin r) (Fin r) ℂ)
    (v : Fin r → K) : ℝ :=
  ∑ i, normSq (Q i *ᵥ embVec (σ i) v)

def ApproxStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] [Nonempty ι] (r p : ℕ)
    (S : HermForm K r) (σ : ι → K →+* ℂ) (Q : ι → Matrix (Fin r) (Fin r) ℂ)
    (L : Submodule (𝓞 K) (Fin r → K)) (v : Fin r → Fin r → K) (μ ρ : ℝ),
    p ≤ r → 0 < μ → 0 < ρ → ρ ≤ 1 → (∀ i, (Q i).det ≠ 0) →
    (∀ i x y, σ i (S.h x y) = jForm p (Q i *ᵥ embVec (σ i) x) (Q i *ᵥ embVec (σ i) y)) →
    IsIntegralOn S L →
    (∀ w : ι → Fin r → ℂ, ∃ l ∈ L, ∑ i, normSq (Q i *ᵥ embVec (σ i) l - w i) ≤ μ ^ 2) →
    (∀ j, v j ∈ L) → LinearIndependent K v → (∀ j, majSq σ Q (v j) ≤ μ ^ 2) →
    ∃ la : Fin r → Fin r → K, (∀ j, la j ∈ L) ∧ LinearIndependent K la ∧
      (∀ j k : Fin r, (j : ℕ) < p → p ≤ (k : ℕ) → S.h (la j) (la k) = 0) ∧
      (∀ i (w : Fin r → ℂ), (∀ j : Fin r, p ≤ (j : ℕ) → w j = 0) →
        negSq p (Q i *ᵥ ∑ j, w j • embVec (σ i) (la j)) ≤
          (ρ / 3) ^ 2 * posSq p (Q i *ᵥ ∑ j, w j • embVec (σ i) (la j)) ∧
        (w ≠ 0 → 0 < (jForm p (Q i *ᵥ ∑ j, w j • embVec (σ i) (la j))
          (Q i *ᵥ ∑ j, w j • embVec (σ i) (la j))).re)) ∧
      (∀ i (w : Fin r → ℂ), (∀ j : Fin r, (j : ℕ) < p → w j = 0) → w ≠ 0 →
        (jForm p (Q i *ᵥ ∑ j, w j • embVec (σ i) (la j))
          (Q i *ᵥ ∑ j, w j • embVec (σ i) (la j))).re < 0) ∧
      (∀ i (j : Fin r), (j : ℕ) < p → ‖σ i (S.h (la j) (la j))‖ ≤ (2 * approxR r μ ρ) ^ 2) ∧
      (∀ i (j : Fin r), p ≤ (j : ℕ) →
        ‖σ i (S.h (la j) (la j))‖ ≤ (2 * approxR r μ ρ) ^ (4 * p) * (2 * μ ^ 2))

def OnePolyGrowthStatement : Prop :=
  ∀ (f : ℂ → ℂ) (B : Set ℂ) (A : ℝ) (k : ℕ), B.Finite → DifferentiableOn ℂ f Bᶜ →
    (∀ t ∉ B, ‖f t‖ ≤ A * (1 + ‖t‖) ^ k) →
    ∃ P : Polynomial ℂ, P.natDegree ≤ k ∧ ∀ t ∉ B, f t = P.eval t

def IsHoloGL {p : ℕ} (P : Matrix (Fin p) (Fin p) ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ (fun y : Fin p → Fin p → ℂ => P (Matrix.of y)) {y | (Matrix.of y).det ≠ 0}

def leadMinor {p : ℕ} (x : Matrix (Fin p) (Fin p) ℂ) (i : Fin p) : ℂ :=
  (Matrix.of fun a b : Fin (i + 1) => x (Fin.castLE i.isLt a) (Fin.castLE i.isLt b)).det

def BWPolyStatement : Prop :=
  ∀ (p : ℕ) (a : Fin p → ℕ) (P : Matrix (Fin p) (Fin p) ℂ → ℂ), IsHoloGL P →
    IsTriEquivariant a P →
    ∃ F : MvPolynomial (Fin p × Fin p) ℂ, F.IsHomogeneous (∑ i, a i) ∧
      ∀ x : Matrix (Fin p) (Fin p) ℂ, x.det ≠ 0 → P x = MvPolynomial.eval (fun ij => x ij.1 ij.2) F

end ReciprocityTheory.MultiplicativeHeights
end
end

section -- merged from ReciprocityTheory.SemistableReduction.ComapInclusionIsLocalHom
namespace ReciprocityTheory.MultiplicativeHeights

open scoped TensorProduct

def RankStatement : Prop :=
  ∀ (K L V : Type) [Field K] [Field L] [Algebra K L] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (W : Submodule K V) (ι : Type) (v : ι → V),
    (∀ i, v i ∈ W) →
    Submodule.span L (Set.range fun i => (1 : L) ⊗ₜ[K] v i) = ⊤ →
    W = ⊤ ∧ Submodule.span K (Set.range v) = ⊤

noncomputable def torusSum {K : Type*} [NormedField K] {n : ℕ} (c : (Fin n → ℤ) → K)
    (τ : Fin n → K) : K :=
  ∑' χ, c χ * ∏ i, τ i ^ χ i

def ResidueFieldInfiniteOn {K : Type*} [NormedField K] (S : Set K) : Prop :=
  ∀ s : Finset K, ∃ x ∈ S, ‖x‖ ≤ 1 ∧ ∀ y ∈ s, 1 ≤ ‖x - y‖

def CauchyTorusStatement : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (K₀ : Subfield K),
    ResidueFieldInfiniteOn (K₀ : Set K) →
    ∀ (n : ℕ) (c : (Fin n → ℤ) → K),
      Filter.Tendsto (fun χ => ‖c χ‖) Filter.cofinite (nhds 0) →
      (∀ τ : Fin n → K, (∀ i, τ i ∈ K₀ ∧ ‖τ i‖ = 1) → ‖torusSum c τ‖ ≤ 1) →
      ∀ χ, ‖c χ‖ ≤ 1

def NormLengthStatement : Prop :=
  ∀ (O B : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing B] [IsDomain B]
    [Algebra O B] [Module.Finite O B] [NoZeroSMulDivisors O B] (g : B),
    g ≠ 0 →
      IsDiscreteValuationRing.addVal O (Algebra.norm O g) =
        Module.length O (B ⧸ Ideal.span {g})

def NormOrdStatement : Prop :=
  ∀ (O B : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing B] [IsDomain B]
    [IsDedekindDomain B] [Algebra O B] [Module.Finite O B] [NoZeroSMulDivisors O B] (g : B),
    g ≠ 0 →
      IsDiscreteValuationRing.addVal O (Algebra.norm O g) =
        ((∑ᶠ Q : {Q : Ideal B // Q.IsMaximal},
          Q.1.inertiaDeg O *
            Multiset.count Q.1 (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {g})) :
          ℕ) : ℕ∞)

def comapInclusion {F₁ F₂ : Type*} [Field F₁] [Field F₂] (V : ValuationSubring F₂)
    (f : F₁ →+* F₂) : V.comap f →+* V :=
  f.restrict (V.comap f) V fun _ hx => hx

instance comapInclusion_isLocalHom {F₁ F₂ : Type*} [Field F₁] [Field F₂]
    (V : ValuationSubring F₂) (f : F₁ →+* F₂) : IsLocalHom (comapInclusion V f) := by
  constructor
  intro x hx
  obtain ⟨u, hu⟩ := isUnit_iff_exists_inv.mp hx
  have hu' : f (x : F₁) * (u : F₂) = 1 := congrArg Subtype.val hu
  have hx0 : (x : F₁) ≠ 0 := fun h => zero_ne_one (by rw [h, map_zero, zero_mul] at hu'; exact hu')
  have hinv : f ((x : F₁)⁻¹) = (u : F₂) := by rw [map_inv₀]; exact inv_eq_of_mul_eq_one_right hu'
  have hmem : (x : F₁)⁻¹ ∈ V.comap f := by rw [ValuationSubring.mem_comap, hinv]; exact u.2
  exact isUnit_iff_exists_inv.mpr ⟨⟨_, hmem⟩, Subtype.ext (mul_inv_cancel₀ hx0)⟩

noncomputable abbrev residueAlgebra {F₁ F₂ : Type*} [Field F₁] [Field F₂]
    (V : ValuationSubring F₂) (f : F₁ →+* F₂) :
    Algebra (IsLocalRing.ResidueField (V.comap f)) (IsLocalRing.ResidueField V) :=
  (IsLocalRing.ResidueField.map (comapInclusion V f)).toAlgebra

def TRStatement : Prop :=
  ∀ (F₁ F₂ : Type) [Field F₁] [Field F₂] [Algebra F₁ F₂] (V : ValuationSubring F₂),
    letI := residueAlgebra V (algebraMap F₁ F₂)
    Algebra.trdeg (IsLocalRing.ResidueField (V.comap (algebraMap F₁ F₂)))
        (IsLocalRing.ResidueField V) ≤ Algebra.trdeg F₁ F₂

def DedekindRankStatement : Prop :=
  ∀ (O F L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field F] [Algebra O F]
    [IsFractionRing O F] [Field L] [Algebra F L] [FiniteDimensional F L] [Algebra.IsSeparable F L]
    [Algebra O L] [IsScalarTower O F L],
    IsDedekindDomain (integralClosure O L) ∧ Module.Finite O (integralClosure O L) ∧
      Module.Free O (integralClosure O L) ∧
      Module.finrank O (integralClosure O L) = Module.finrank F L ∧
      {Q : Ideal (integralClosure O L) | Q.IsMaximal}.Finite ∧
      ∑ᶠ Q : {Q : Ideal (integralClosure O L) // Q.IsMaximal},
          Q.1.ramificationIdx O * Q.1.inertiaDeg O = Module.finrank F L

abbrev SVars (D m : ℕ) : Type := Unit ⊕ (Fin (D + 1) × Fin m)

abbrev SField (Ω : Type) [Field Ω] (D m : ℕ) : Type :=
  FractionRing (MvPolynomial (SVars D m) Ω)

noncomputable def sImage {Ω : Type} [Field Ω] {D m : ℕ} (x : Fin m → Ω) :
    Fin (D + 1) × Fin (m + 1) → SField Ω D m :=
  fun p => algebraMap (MvPolynomial (SVars D m) Ω) (SField Ω D m)
    (Fin.cases (motive := fun _ => MvPolynomial (SVars D m) Ω)
      (if p.1 = 0 then MvPolynomial.X (Sum.inl ())
        else -∑ k, MvPolynomial.X (Sum.inr (p.1, k)) * MvPolynomial.C (x k))
      (fun j => MvPolynomial.X (Sum.inr (p.1, j))) p.2)

def FieldOfSStatement : Prop :=
  ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω] (D m : ℕ) (x : Fin m → Ω),
    (⊤ : IntermediateField K Ω).FG → Algebra.trdeg K Ω = D →
    (∃ J : Fin D → Fin m,
      LinearIndependent Ω fun a => KaehlerDifferential.D K Ω (x (J a))) →
    AlgebraicIndependent K (sImage (D := D) x) ∧
      FiniteDimensional (IntermediateField.adjoin K (Set.range (sImage (D := D) x)))
        (SField Ω D m)

def ResidueTrdegStatement : Prop :=
  ∀ (K Ω U : Type) [Field K] [Field Ω] [Field U] [Algebra K Ω] [Algebra Ω U] (D : ℕ),
    Algebra.trdeg K Ω = D →
    ∀ (σ : Type) [Fintype σ] (t : σ → U) (V : ValuationSubring U) (ht : ∀ s, t s ∈ V)
      (τ : Type) [Fintype τ] (u : τ → V) (p : τ → MvPolynomial σ Ω)
      (hp : ∀ j α, (p j).coeff α ∈ V.comap (algebraMap Ω U)),
      Fintype.card τ = Fintype.card σ + D → (∀ j, MvPolynomial.aeval t (p j) = (u j : U)) →
      letI _iW := residueAlgebra V (algebraMap Ω U)
      letI _io := residueAlgebra (V.comap (algebraMap Ω U)) (algebraMap K Ω)
      letI : Algebra (IsLocalRing.ResidueField
          ((V.comap (algebraMap Ω U)).comap (algebraMap K Ω))) (IsLocalRing.ResidueField V) :=
        ((algebraMap _ (IsLocalRing.ResidueField V)).comp
          (algebraMap _ (IsLocalRing.ResidueField (V.comap (algebraMap Ω U))))).toAlgebra
      AlgebraicIndependent
          (IsLocalRing.ResidueField ((V.comap (algebraMap Ω U)).comap (algebraMap K Ω)))
          (fun j => IsLocalRing.residue V (u j)) →
      (∀ k₁ : IntermediateField
          (IsLocalRing.ResidueField ((V.comap (algebraMap Ω U)).comap (algebraMap K Ω)))
          (IsLocalRing.ResidueField (V.comap (algebraMap Ω U))),
        (∀ j α, IsLocalRing.residue _ ⟨(p j).coeff α, hp j α⟩ ∈ k₁) →
        Algebra.trdeg
          (IsLocalRing.ResidueField ((V.comap (algebraMap Ω U)).comap (algebraMap K Ω))) k₁ = D) ∧
      Algebra.trdeg
          (IsLocalRing.ResidueField ((V.comap (algebraMap Ω U)).comap (algebraMap K Ω)))
          (IsLocalRing.ResidueField (V.comap (algebraMap Ω U))) = D ∧
        AlgebraicIndependent (IsLocalRing.ResidueField (V.comap (algebraMap Ω U)))
          (fun s => IsLocalRing.residue V ⟨t s, ht s⟩)

end ReciprocityTheory.MultiplicativeHeights
end

section -- merged from ReciprocityTheory.SemistableReduction.SemiDegCA
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.SemiDegIdx

open NumberField
open scoped nonZeroDivisors

theorem relIndex_eq_map_mul_ker {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (f : G →+ H) {A B : AddSubgroup G} (hAB : A ≤ B) :
    A.relIndex B = (A.map f).relIndex (B.map f) * (A ⊓ f.ker).relIndex (B ⊓ f.ker) := by
  have hN : A ⊓ (B ⊓ f.ker) = A ⊓ f.ker := by
    rw [← inf_assoc, inf_eq_left.mpr hAB]
  have hC : (A ⊔ f.ker) ⊓ B = A ⊔ (B ⊓ f.ker) := by
    ext x
    simp only [AddSubgroup.mem_inf, AddSubgroup.mem_sup]
    constructor
    · rintro ⟨⟨y, hy, z, hz, rfl⟩, hx⟩
      refine ⟨y, hy, z, ⟨?_, hz⟩, rfl⟩
      have := B.sub_mem hx (hAB hy)
      simpa using this
    · rintro ⟨y, hy, z, ⟨hzB, hz⟩, rfl⟩
      exact ⟨⟨y, hy, z, hz, rfl⟩, B.add_mem (hAB hy) hzB⟩
  have h1 : (A.map f).relIndex (B.map f) = (A ⊔ (B ⊓ f.ker)).relIndex B := by
    rw [← AddSubgroup.relIndex_comap, AddSubgroup.comap_map_eq,
      ← AddSubgroup.inf_relIndex_right, hC]
  have h2 : (A ⊓ f.ker).relIndex (B ⊓ f.ker) = A.relIndex (A ⊔ (B ⊓ f.ker)) := by
    rw [sup_comm A, AddSubgroup.relIndex_sup_right, ← AddSubgroup.inf_relIndex_right A (B ⊓ f.ker),
      hN]
  rw [h1, h2, mul_comm]
  exact (AddSubgroup.relIndex_mul_relIndex _ _ _ le_sup_left (sup_le hAB inf_le_left)).symm

def intVec (K : Type) [Field K] [NumberField K] (k : ℕ) : Submodule (𝓞 K) (Fin k → K) :=
  Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 K) K)

theorem mem_intVec {K : Type} [Field K] [NumberField K] {k : ℕ} {x : Fin k → K} :
    x ∈ intVec K k ↔ ∀ i, x i ∈ (1 : Submodule (𝓞 K) K) := by
  simp [intVec, Submodule.mem_pi]

theorem exists_section_of_image {K : Type} [Field K] [NumberField K] {V : Type*}
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (X : Submodule (𝓞 K) V) (f : V →ₗ[K] K) (hfg : (X.map (f.restrictScalars (𝓞 K))).FG)
    (h1 : (1 : Submodule (𝓞 K) K) ≤ X.map (f.restrictScalars (𝓞 K))) :
    ∃ v : V, f v = 1 ∧ ∀ t ∈ X.map (f.restrictScalars (𝓞 K)), t • v ∈ X := by
  classical
  let I : FractionalIdeal (𝓞 K)⁰ K :=
    ⟨X.map (f.restrictScalars (𝓞 K)), FractionalIdeal.isFractional_of_fg hfg⟩
  have hone : (1 : K) ∈ (1 : Submodule (𝓞 K) K) := Submodule.mem_one.mpr ⟨1, map_one _⟩
  have hI0 : I ≠ 0 := by
    intro h
    have h1I : (1 : K) ∈ (I : Submodule (𝓞 K) K) := h1 hone
    rw [h, FractionalIdeal.coe_zero, Submodule.mem_bot] at h1I
    exact one_ne_zero h1I
  have hII : (I : Submodule (𝓞 K) K) * ((I⁻¹ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) =
      1 := by
    rw [← FractionalIdeal.coe_mul, mul_inv_cancel₀ hI0, FractionalIdeal.coe_one]
  have key : ∀ w ∈ (I : Submodule (𝓞 K) K) * ((I⁻¹ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K),
      ∃ u : V, f u = w ∧ ∀ t ∈ X.map (f.restrictScalars (𝓞 K)), t • u ∈ X := by
    intro w hw
    refine Submodule.mul_induction_on hw (fun c hc d hd => ?_) (fun a b ha hb => ?_)
    · obtain ⟨x, hx, hfx⟩ := Submodule.mem_map.mp hc
      rw [LinearMap.restrictScalars_apply] at hfx
      refine ⟨d • x, ?_, fun t ht => ?_⟩
      · rw [map_smul, smul_eq_mul, hfx, mul_comm]
      · have htd : t * d ∈ (1 : Submodule (𝓞 K) K) := by
          rw [← hII]
          exact Submodule.mul_mem_mul (show t ∈ (I : Submodule (𝓞 K) K) from ht) hd
        obtain ⟨r, hr⟩ := Submodule.mem_one.mp htd
        rw [smul_smul, ← hr, algebraMap_smul]
        exact X.smul_mem r hx
    · obtain ⟨u1, e1, h1'⟩ := ha
      obtain ⟨u2, e2, h2'⟩ := hb
      exact ⟨u1 + u2, by rw [map_add (f := _), e1, e2], fun t ht => by
        rw [smul_add]; exact X.add_mem (h1' t ht) (h2' t ht)⟩
  exact key 1 (by rw [hII]; exact hone)

theorem absNorm_mul_relIndex_one {K : Type} [Field K] [NumberField K] (C : Submodule (𝓞 K) K)
    (hC : C.FG) (h1 : 1 ≤ C) :
    FractionalIdeal.absNorm
        (⟨C, FractionalIdeal.isFractional_of_fg hC⟩ : FractionalIdeal (𝓞 K)⁰ K) *
      ((1 : Submodule (𝓞 K) K).toAddSubgroup.relIndex C.toAddSubgroup : ℚ) = 1 := by
  classical
  set I : FractionalIdeal (𝓞 K)⁰ K := ⟨C, FractionalIdeal.isFractional_of_fg hC⟩ with hIdef
  have hden := FractionalIdeal.den_mul_self_eq_num I
  set d : 𝓞 K := (I.den : 𝓞 K) with hd
  set J : Ideal (𝓞 K) := I.num with hJ
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero I.den.2
  have hdK : algebraMap (𝓞 K) K d ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors I.den.2
  let ι : 𝓞 K →+ K := (algebraMap (𝓞 K) K).toAddMonoidHom
  have hι : Function.Injective ι := IsFractionRing.injective (𝓞 K) K
  let μ : K →+ K := AddMonoidHom.mulLeft (algebraMap (𝓞 K) K d)
  have hμ : Function.Injective μ := mul_right_injective₀ hdK
  have hsm : ∀ y : K, (I.den : 𝓞 K) • y = μ y := fun y => by
    rw [Algebra.smul_def]
    rfl
  have hone : AddSubgroup.map μ (1 : Submodule (𝓞 K) K).toAddSubgroup =
      AddSubgroup.map ι (Ideal.span {d}).toAddSubgroup := by
    ext x
    simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, Submodule.mem_one,
      Ideal.mem_span_singleton']
    constructor
    · rintro ⟨y, ⟨r, rfl⟩, rfl⟩
      exact ⟨r * d, ⟨r, rfl⟩, by simp [μ, ι, mul_comm]⟩
    · rintro ⟨y, ⟨r, rfl⟩, rfl⟩
      exact ⟨algebraMap (𝓞 K) K r, ⟨r, rfl⟩, by simp [μ, ι, mul_comm]⟩
  have hCm : AddSubgroup.map μ C.toAddSubgroup = AddSubgroup.map ι J.toAddSubgroup := by
    ext x
    open Pointwise in
    have hx : x ∈ ((I.den : 𝓞 K) • (I : Submodule (𝓞 K) K)) ↔
        x ∈ Submodule.map (Algebra.linearMap (𝓞 K) K) I.num := by
      rw [← hden]
      exact Iff.rfl
    rw [Submodule.mem_map, Submodule.mem_smul_pointwise_iff_exists] at hx
    simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup]
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨z, hz, hzx⟩ := hx.mp ⟨y, hy, hsm y⟩
      exact ⟨z, hz, hzx⟩
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨y, hy, hyx⟩ := hx.mpr ⟨z, hz, rfl⟩
      exact ⟨y, hy, by rw [← hsm]; exact hyx⟩
  have hidx : (1 : Submodule (𝓞 K) K).toAddSubgroup.relIndex C.toAddSubgroup =
      (Ideal.span {d}).toAddSubgroup.relIndex J.toAddSubgroup := by
    rw [← AddSubgroup.relIndex_map_map_of_injective _ _ hμ, hone, hCm,
      AddSubgroup.relIndex_map_map_of_injective _ _ hι]
  have hle : Ideal.span {d} ≤ J := by
    rw [Ideal.span_singleton_le_iff_mem]
    have h1C : (1 : K) ∈ C := h1 (Submodule.mem_one.mpr ⟨1, map_one _⟩)
    have hm : algebraMap (𝓞 K) K d ∈ Submodule.map (Algebra.linearMap (𝓞 K) K) I.num := by
      rw [← hden]
      open Pointwise in
      show _ ∈ ((I.den : 𝓞 K) • (I : Submodule (𝓞 K) K))
      exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
        ⟨1, h1C, by rw [hsm]; simp [μ]⟩
    obtain ⟨z, hz, hzd⟩ := Submodule.mem_map.mp hm
    have hzd' := hι hzd
    rw [hd, ← hzd']
    exact hz
  have htower := AddSubgroup.relIndex_mul_relIndex (Ideal.span {d}).toAddSubgroup
    J.toAddSubgroup ⊤ hle le_top
  rw [AddSubgroup.relIndex_top_right, AddSubgroup.relIndex_top_right] at htower
  have hiJ : J.toAddSubgroup.index = Ideal.absNorm J := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, AddSubgroup.index_eq_card]
    rfl
  have hid : (Ideal.span {d}).toAddSubgroup.index = (Algebra.norm ℤ d).natAbs := by
    rw [← Ideal.absNorm_span_singleton, Ideal.absNorm_apply, Submodule.cardQuot_apply,
      AddSubgroup.index_eq_card]
    rfl
  rw [hiJ, hid] at htower
  have hb : (Algebra.norm ℤ d).natAbs ≠ 0 := by
    rw [← Ideal.absNorm_span_singleton]
    intro h
    rw [Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot] at h
    exact hd0 h
  have hbq : ((Algebra.norm ℤ d).natAbs : ℚ) ≠ 0 := by exact_mod_cast hb
  have hcast : ((|Algebra.norm ℤ d| : ℤ) : ℚ) = ((Algebra.norm ℤ d).natAbs : ℚ) := by
    simp [Nat.cast_natAbs, Int.cast_abs]
  rw [hidx, FractionalIdeal.absNorm_eq, hcast, div_mul_eq_mul_div, div_eq_one_iff_eq hbq]
  rw [mul_comm] at htower
  exact_mod_cast htower

end ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
end
end

section -- merged from ReciprocityTheory.SemistableReduction.GaussIndepOfLeTrdeg
namespace ReciprocityTheory.MultiplicativeHeights

open MvPolynomial

private theorem exists_transcendenceBasis_subset_adjoin_range {E C : Type} [Field E] [Field C] [Algebra E C] {σ : Type}
    (tb : σ → C) : ∃ t ⊆ ((↑) ⁻¹' Set.range tb : Set (Algebra.adjoin E (Set.range tb))),
      IsTranscendenceBasis E (Subtype.val : t → Algebra.adjoin E (Set.range tb)) := by
  have htop : Algebra.adjoin E ((↑) ⁻¹' Set.range tb : Set (Algebra.adjoin E (Set.range tb))) = ⊤ :=
    Algebra.adjoin_adjoin_coe_preimage
  haveI : FaithfulSMul E (Algebra.adjoin E (Set.range tb)) :=
    (faithfulSMul_iff_algebraMap_injective E _).mpr (algebraMap E _).injective
  haveI : Algebra.IsAlgebraic
      (Algebra.adjoin E ((↑) ⁻¹' Set.range tb : Set (Algebra.adjoin E (Set.range tb))))
      (Algebra.adjoin E (Set.range tb)) := ⟨fun a => by
    have ha : a ∈ Algebra.adjoin E ((↑) ⁻¹' Set.range tb : Set (Algebra.adjoin E (Set.range tb))) := by
      rw [htop]; exact Algebra.mem_top
    exact isAlgebraic_algebraMap (⟨a, ha⟩ : Algebra.adjoin E _)⟩
  exact exists_isTranscendenceBasis_subset (R := E) _

theorem gauss_trdeg_adjoin_le {E C : Type} [Field E] [Field C] [Algebra E C] {σ : Type}
    (tb : σ → C) : Algebra.trdeg E (Algebra.adjoin E (Set.range tb)) ≤ Cardinal.mk σ := by
  obtain ⟨t, hts, hb⟩ := exists_transcendenceBasis_subset_adjoin_range (E := E) tb
  rw [← hb.cardinalMk_eq_trdeg]
  calc Cardinal.mk t ≤ Cardinal.mk ((↑) ⁻¹' Set.range tb : Set (Algebra.adjoin E (Set.range tb))) :=
        Cardinal.mk_le_mk_of_subset hts
    _ ≤ Cardinal.mk (Set.range tb) := Cardinal.mk_preimage_of_injective _ _ Subtype.val_injective
    _ ≤ Cardinal.mk σ := Cardinal.mk_range_le

theorem gauss_card_le_trdeg_add {F E C : Type} [Field F] [Field E] [Field C] [Algebra F E] [Algebra E C]
    [Algebra F C] [IsScalarTower F E C] {σ τ : Type} (tb : σ → C) (ub : τ → C)
    (hu : AlgebraicIndependent F ub) (hmem : ∀ j, ub j ∈ Algebra.adjoin E (Set.range tb)) :
    Cardinal.mk τ ≤ Algebra.trdeg F E + Algebra.trdeg E (Algebra.adjoin E (Set.range tb)) := by
  haveI : FaithfulSMul F E :=
    (faithfulSMul_iff_algebraMap_injective F E).mpr (algebraMap F E).injective
  haveI : FaithfulSMul E (Algebra.adjoin E (Set.range tb)) :=
    (faithfulSMul_iff_algebraMap_injective E _).mpr (algebraMap E _).injective
  rw [trdeg_add_eq F E (A := Algebra.adjoin E (Set.range tb))]
  have hu' : AlgebraicIndependent F (fun j => (⟨ub j, hmem j⟩ : Algebra.adjoin E (Set.range tb))) :=
    AlgebraicIndependent.of_comp ((Algebra.adjoin E (Set.range tb)).val.restrictScalars F) hu
  exact hu'.cardinalMk_le_trdeg

theorem gauss_indep_of_le_trdeg {E C : Type} [Field E] [Field C] [Algebra E C] {σ : Type}
    [Finite σ] (tb : σ → C)
    (h : Cardinal.mk σ ≤ Algebra.trdeg E (Algebra.adjoin E (Set.range tb))) :
    AlgebraicIndependent E tb := by
  classical
  obtain ⟨t, hts, hb⟩ := exists_transcendenceBasis_subset_adjoin_range (E := E) tb
  have ht := hb.cardinalMk_eq_trdeg
  have h1 : Cardinal.mk t ≤ Cardinal.mk ((↑) ⁻¹' Set.range tb : Set (Algebra.adjoin E (Set.range tb))) :=
    Cardinal.mk_le_mk_of_subset hts
  have h2 : Cardinal.mk ((↑) ⁻¹' Set.range tb : Set (Algebra.adjoin E (Set.range tb))) ≤
      Cardinal.mk (Set.range tb) := Cardinal.mk_preimage_of_injective _ _ Subtype.val_injective
  have h3 : Cardinal.mk (Set.range tb) ≤ Cardinal.mk σ := Cardinal.mk_range_le
  have hσt : Cardinal.mk σ ≤ Cardinal.mk t := ht ▸ h

  have hinj : Function.Injective tb := by
    obtain ⟨e⟩ := Cardinal.eq.1 (le_antisymm h3 (hσt.trans (h1.trans h2)))
    have hr : Function.Injective (Set.rangeFactorization tb) :=
      (Finite.injective_iff_surjective_of_equiv e.symm).2 Set.rangeFactorization_surjective
    exact fun a b hab => hr (Subtype.ext hab)

  have hsf : ((↑) ⁻¹' Set.range tb : Set (Algebra.adjoin E (Set.range tb))).Finite :=
    (Set.finite_range tb).preimage Subtype.val_injective.injOn
  have hle : ((↑) ⁻¹' Set.range tb : Set (Algebra.adjoin E (Set.range tb))).ncard ≤ t.ncard := by
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    exact Cardinal.toNat_le_toNat ((h2.trans h3).trans hσt) (hsf.subset hts).lt_aleph0
  rw [Set.eq_of_subset_of_ncard_le hts hle hsf] at hb
  let g : σ → Algebra.adjoin E (Set.range tb) := fun i => ⟨tb i, Algebra.subset_adjoin ⟨i, rfl⟩⟩
  have hginj : Function.Injective g := fun a b hab => hinj (congrArg Subtype.val hab)
  have hrange : Set.range g = ((↑) ⁻¹' Set.range tb : Set (Algebra.adjoin E (Set.range tb))) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, hi⟩
      exact ⟨i, Subtype.ext hi⟩
  have hg : AlgebraicIndependent E g := by
    rw [← algebraicIndependent_subtype_range hginj, hrange]
    exact hb.1
  exact hg.map' (f := (Algebra.adjoin E (Set.range tb)).val) Subtype.val_injective

theorem gauss_card_arith {a b : Cardinal} {s d : ℕ} (h : ((s + d : ℕ) : Cardinal) ≤ a + b)
    (ha : a ≤ d) (hb : b ≤ s) : a = d ∧ b = s := by
  obtain ⟨a', rfl⟩ := Cardinal.lt_aleph0.1 (ha.trans_lt Cardinal.natCast_lt_aleph0)
  obtain ⟨b', rfl⟩ := Cardinal.lt_aleph0.1 (hb.trans_lt Cardinal.natCast_lt_aleph0)
  have h' : s + d ≤ a' + b' := by exact_mod_cast h
  have ha' : a' ≤ d := by exact_mod_cast ha
  have hb' : b' ≤ s := by exact_mod_cast hb
  constructor
  · exact_mod_cast (by omega : a' = d)
  · exact_mod_cast (by omega : b' = s)

theorem gauss_aeval_mem {B C : Type} [CommRing B] [CommRing C] [Algebra B C] {σ : Type}
    (g : σ → C) (P : MvPolynomial σ B) (R : Subring C)
    (hc : ∀ α, algebraMap B C (P.coeff α) ∈ R) (hg : ∀ s, g s ∈ R) : aeval g P ∈ R := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  exact R.sum_mem fun α _ => R.mul_mem (hc α) (R.prod_mem fun i _ => R.pow_mem (hg i) _)

end ReciprocityTheory.MultiplicativeHeights
end

section -- merged from ReciprocityTheory.SemistableReduction.AlgebraicIndependentOfDerivations
namespace ReciprocityTheory.MultiplicativeHeights

namespace DerivationAlgebraicIndependence

open MvPolynomial

theorem derivation_aeval_eq {K R ι : Type*} [CommRing K] [CommRing R] [Algebra K R] [Fintype ι]
    (d : Derivation K R R) (z : ι → R) (P : MvPolynomial ι K) :
    d (aeval z P) = ∑ i, aeval z (pderiv i P) * d (z i) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [map_add (f := _), hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p j hp =>
    simp only [map_mul, aeval_X, Derivation.leibniz, hp, smul_eq_mul, pderiv_X, Pi.single_apply,
      add_mul, Finset.sum_add_distrib, Finset.mul_sum]
    simp only [map_add (f := _), map_mul, aeval_X, apply_ite (aeval z), map_zero, map_one, add_mul, mul_ite,
      mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_add_distrib, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    ring

theorem totalDegree_pderiv_lt {K ι : Type*} [CommRing K] (P : MvPolynomial ι K) (i : ι)
    (hP : 0 < P.totalDegree) : (pderiv i P).totalDegree < P.totalDegree := by
  classical
  have hsum : pderiv i P = ∑ m ∈ P.support, pderiv i (monomial m (AddMonoidAlgebra.coeff P m)) := by
    conv_lhs => rw [P.as_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
  rw [hsum]
  refine lt_of_le_of_lt (MvPolynomial.totalDegree_finsetSum _ _) ?_
  rw [Finset.sup_lt_iff hP]
  intro m hm
  rw [pderiv_monomial]
  by_cases hmi : m i = 0
  · simp [hmi, hP]
  · have hm1 : m = (m - Finsupp.single i 1) + Finsupp.single i 1 := by
      ext k
      by_cases hk : k = i
      · subst hk; simp; omega
      · simp [Finsupp.single_apply, Ne.symm hk]
    have key : ((m - Finsupp.single i 1).sum fun _ e => e) + 1 = m.sum fun _ e => e := by
      conv_rhs => rw [hm1]
      rw [Finsupp.sum_add_index' (by simp) (by intros; rfl), Finsupp.sum_single_index rfl]
    have hle : (m.sum fun _ e => e) ≤ P.totalDegree := le_totalDegree hm
    refine lt_of_le_of_lt (totalDegree_monomial_le _ _) ?_
    show ((m - Finsupp.single i 1).sum fun _ e => e) < _
    omega

theorem eq_C_of_pderiv_eq_zero {K ι : Type*} [Field K] [CharZero K] (P : MvPolynomial ι K)
    (h : ∀ i, pderiv i P = 0) : P.totalDegree = 0 := by
  classical
  by_contra hne
  obtain ⟨m, hm, hmd⟩ := Finset.exists_mem_eq_sup P.support
    (Finset.nonempty_of_ne_empty (by rintro hs; apply hne; simp [totalDegree, hs]))
    (fun s => s.sum fun _ e => e)
  have hm0 : m ≠ 0 := by
    rintro rfl
    apply hne
    simpa [totalDegree] using hmd
  obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hm0 (Finsupp.ext hc)
  have hc := congrArg (AddMonoidAlgebra.coeff · (m - Finsupp.single i 1)) (h i)
  rw [coeff_pderiv, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at hc
  have hm' : m - Finsupp.single i 1 + Finsupp.single i 1 = m := by
    ext k
    by_cases hk : k = i
    · subst hk; simp; omega
    · simp [Finsupp.single_apply, Ne.symm hk]
  rw [hm'] at hc
  rcases mul_eq_zero.mp hc with h1 | h1
  · exact (mem_support_iff.mp hm) h1
  · exact Nat.cast_add_one_ne_zero _ h1

theorem algebraicIndependent_of_derivations {K R ι J : Type*} [Field K] [CharZero K] [CommRing R]
    [Nontrivial R] [Algebra K R] [Fintype ι] (z : ι → R) (δ : J → Derivation K R R)
    (h : ∀ c : ι → R, (∀ j, ∑ i, c i * δ j (z i) = 0) → ∀ i, c i = 0) :
    AlgebraicIndependent K z := by
  classical
  rw [algebraicIndependent_iff]
  suffices H : ∀ n (P : MvPolynomial ι K), P.totalDegree = n → aeval z P = 0 → P = 0 from
    fun P => H _ P rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro P hn hP
  have hd : ∀ i, pderiv i P = 0 := by
    have hv : ∀ i, aeval z (pderiv i P) = 0 :=
      h (fun i => aeval z (pderiv i P)) (fun j => by rw [← derivation_aeval_eq, hP, map_zero])
    intro i
    by_cases h0 : P.totalDegree = 0
    · rw [totalDegree_eq_zero_iff_eq_C] at h0
      rw [h0]
      simp
    · exact ih _ (hn ▸ totalDegree_pderiv_lt P i (Nat.pos_of_ne_zero h0)) _ rfl (hv i)
  have h0 := eq_C_of_pderiv_eq_zero P hd
  rw [totalDegree_eq_zero_iff_eq_C] at h0
  rw [h0, aeval_C] at hP
  have hc : AddMonoidAlgebra.coeff P 0 = 0 := (algebraMap K R).injective (hP.trans (map_zero _).symm)
  rw [h0, hc, map_zero]

end DerivationAlgebraicIndependence

end ReciprocityTheory.MultiplicativeHeights
end

section -- merged from ReciprocityTheory.SemistableReduction.SemiContractA
namespace ReciprocityTheory.MultiplicativeHeights

open Matrix
open scoped ComplexOrder

theorem sc_schur_posDef {k m : Type*} [Fintype k] [Fintype m] [DecidableEq k]
    {A : Matrix k k ℂ} (B : Matrix k m ℂ) (D : Matrix m m ℂ) (hA : A.PosDef)
    (h : (fromBlocks A B Bᴴ D).PosDef) : (D - Bᴴ * A⁻¹ * B).PosDef := by
  classical
  have hAu : IsUnit A.det := isUnit_iff_ne_zero.mpr hA.det_pos.ne'
  obtain ⟨N, hN⟩ : ∃ N : Matrix (k ⊕ m) m ℂ, N = fromRows (-(A⁻¹ * B)) 1 := ⟨_, rfl⟩
  have hinj : Function.Injective N.mulVec := by
    intro v w hvw
    funext i
    have h1 := congrFun hvw (Sum.inr i)
    simpa [hN, fromRows_mulVec] using h1
  have hAA : A * A⁻¹ = 1 := mul_nonsing_inv A hAu
  have h1 : A * (-(A⁻¹ * B)) + B * (1 : Matrix m m ℂ) = 0 := by
    rw [Matrix.mul_neg, ← Matrix.mul_assoc, hAA, Matrix.one_mul, Matrix.mul_one, neg_add_cancel]
  have h2 : Bᴴ * (-(A⁻¹ * B)) + D * (1 : Matrix m m ℂ) = D - Bᴴ * A⁻¹ * B := by
    rw [Matrix.mul_neg, Matrix.mul_one, ← Matrix.mul_assoc]
    abel
  have key : Nᴴ * fromBlocks A B Bᴴ D * N = D - Bᴴ * A⁻¹ * B := by
    rw [hN, conjTranspose_fromRows_eq_fromCols_conjTranspose, ← fromRows_fromCols_eq_fromBlocks,
      fromCols_mul_fromRows, Matrix.add_mul]
    simp only [Matrix.mul_assoc]
    rw [fromCols_mul_fromRows, fromCols_mul_fromRows, h1, h2, Matrix.mul_zero, zero_add,
      conjTranspose_one, Matrix.one_mul, Matrix.mul_assoc]
  have hpd := h.conjTranspose_mul_mul_same hinj
  rwa [key] at hpd

end ReciprocityTheory.MultiplicativeHeights
end
