module

public import Mathlib

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial Pointwise

noncomputable section

variable {n d : ℕ}

def zeroSet (J : Ideal (MvPolynomial (Fin n) ℂ)) : Set (Fin n → ℂ) :=
  {x | ∀ q ∈ J, eval x q = 0}

def linPoly (A : Matrix (Fin d) (Fin n) ℂ) (i : Fin d) : MvPolynomial (Fin n) ℂ :=
  ∑ j, C (A i j) * X j

def pullback (A : Matrix (Fin d) (Fin n) ℂ) : MvPolynomial (Fin d) ℂ →ₐ[ℂ] MvPolynomial (Fin n) ℂ :=
  aeval (linPoly A)

def projHom (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) :
    MvPolynomial (Fin d) ℂ →ₐ[ℂ] MvPolynomial (Fin n) ℂ ⧸ J :=
  (Ideal.Quotient.mkₐ ℂ J).comp (pullback A)

structure IsFiniteProjection (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) :
    Prop where

  injective : Function.Injective (projHom J A)

  finite : (projHom J A).toRingHom.Finite

def projDegree (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) : ℕ :=
  letI : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
    (projHom J A).toRingHom.toAlgebra
  letI : Module (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) := Algebra.toModule
  Module.finrank (FractionRing (MvPolynomial (Fin d) ℂ))
    (TensorProduct (MvPolynomial (Fin d) ℂ) (FractionRing (MvPolynomial (Fin d) ℂ))
      (MvPolynomial (Fin n) ℂ ⧸ J))

def fibre (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) (y : Fin d → ℂ) :
    Set (Fin n → ℂ) :=
  {x | x ∈ zeroSet J ∧ A.mulVec x = y}

def IsZariskiOpen (U : Set (Matrix (Fin d) (Fin n) ℂ)) : Prop :=
  ∃ S : Set (MvPolynomial (Fin d × Fin n) ℂ),
    U = {A | ∃ p ∈ S, eval (fun ij : Fin d × Fin n => A ij.1 ij.2) p ≠ 0}

def orthoRows (d n : ℕ) : Set (Matrix (Fin d) (Fin n) ℂ) :=
  {A | A * A.conjTranspose = 1}

def GenericProjectionFinite.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d →
      (∃ U : Set (Matrix (Fin d) (Fin n) ℂ), IsZariskiOpen U ∧ U.Nonempty ∧
        ∀ A ∈ U, IsFiniteProjection J A) ∧
      {A : Matrix (Fin d) (Fin n) ℂ | IsFiniteProjection J A}.Nonempty ∧
      (∀ D : Set (Matrix (Fin d) (Fin n) ℂ), D ⊆ orthoRows d n → orthoRows d n ⊆ closure D →
        ∃ A ∈ D, IsFiniteProjection J A) ∧
      (∀ (m : ℕ) (F : Fin m → Matrix.unitaryGroup (Fin n) ℂ),
        ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ (k : Fin m) (s : Fin d ↪ Fin n),
          IsFiniteProjection J (((F k : Matrix (Fin n) (Fin n) ℂ) * U).submatrix s id))

def FibreBound.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → IsFiniteProjection J A →
      ∀ y : Fin d → ℂ, (fibre J A y).Nonempty ∧ (fibre J A y).Finite ∧
        (fibre J A y).ncard ≤ projDegree J A

def DiscriminantCover.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → IsFiniteProjection J A →
      ∃ P : MvPolynomial (Fin d) ℂ, P ≠ 0 ∧ ∀ y : Fin d → ℂ, eval y P ≠ 0 →
        (fibre J A y).Finite ∧ (fibre J A y).ncard = projDegree J A ∧
        ∀ x ∈ fibre J A y, ∃ (U : Set (Fin d → ℂ)) (V : Set (Fin n → ℂ))
          (g : (Fin d → ℂ) → (Fin n → ℂ)), IsOpen U ∧ y ∈ U ∧ IsOpen V ∧ x ∈ V ∧
            DifferentiableOn ℂ g U ∧ g y = x ∧ (∀ w ∈ U, A.mulVec (g w) = w) ∧
            zeroSet J ∩ V = g '' U

def BadSetSmaller.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → IsFiniteProjection J A →
      ∀ P : MvPolynomial (Fin d) ℂ, P ≠ 0 →
        zeroSet (J ⊔ Ideal.span {pullback A P}) = zeroSet J ∩ {x | eval (A.mulVec x) P = 0} ∧
        ∀ Q ∈ (J ⊔ Ideal.span {pullback A P}).minimalPrimes,
          ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ Q) < d


section Inhabitants



end Inhabitants

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalModel
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial

noncomputable section

def zeroSetIn {σ : Type*} (I : Ideal (MvPolynomial σ ℂ)) : Set (σ → ℂ) :=
  {z | ∀ q ∈ I, eval z q = 0}

def firstCoords {n m : ℕ} (w : Fin n ⊕ Fin m → ℂ) : Fin n → ℂ :=
  fun i => w (Sum.inl i)

structure NormalModel {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) where

  m : ℕ

  ideal : Ideal (MvPolynomial (Fin n ⊕ Fin m) ℂ)
  isPrime : ideal.IsPrime
  isIntegrallyClosed : IsIntegrallyClosed (MvPolynomial (Fin n ⊕ Fin m) ℂ ⧸ ideal)
  comap_eq : ideal.comap
    (rename Sum.inl : MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n ⊕ Fin m) ℂ) = J
  integral : ∀ i : Fin m, ∃ P : Polynomial (MvPolynomial (Fin n) ℂ), P.Monic ∧
    P.eval₂ (rename Sum.inl : MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n ⊕ Fin m) ℂ).toRingHom
      (X (Sum.inr i)) ∈ ideal
  birational : ∀ i : Fin m, ∃ a b : MvPolynomial (Fin n) ℂ, b ∉ J ∧
    rename Sum.inl b * X (Sum.inr i) - rename Sum.inl a ∈ ideal

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.AnalyticGerm
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

def IsAnalyticNear {σ : Type} [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) : Prop :=
  ∃ (N : Set (σ → ℂ)) (k : ℕ) (f : Fin k → (σ → ℂ) → ℂ), IsOpen N ∧ w ∈ N ∧
    (∀ i, AnalyticOnNhd ℂ (f i) N) ∧ X ∩ N = {z | z ∈ N ∧ ∀ i, f i z = 0}

def GermIrreducibleAt {σ : Type} [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) : Prop :=
  w ∈ X ∧ ∀ f g : (σ → ℂ) → ℂ, AnalyticAt ℂ f w → AnalyticAt ℂ g w →
    (∀ᶠ z in 𝓝 w, z ∈ X → f z * g z = 0) →
      (∀ᶠ z in 𝓝 w, z ∈ X → f z = 0) ∨ (∀ᶠ z in 𝓝 w, z ∈ X → g z = 0)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StAreaMultiplicity
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Module

open scoped ENNReal

noncomputable section

def areaJacobian {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] (L : E →ₗ[ℝ] F) : ℝ :=
  √(LinearMap.det (LinearMap.adjoint L ∘ₗ L))

def AreaMultiplicity.Statement : Prop :=
  ∀ (E F : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] (k : ℕ),
    finrank ℝ E = k → finrank ℝ F = k →
    ∀ (A : Set E) (f : E → F) (f' : E → E →L[ℝ] F), MeasurableSet A →
      (∀ x ∈ A, HasFDerivWithinAt f (f' x) A x) →
      ∫⁻ x in A, ENNReal.ofReal (areaJacobian (f' x : E →ₗ[ℝ] F)) ∂(μH[(k : ℝ)]) =
        ∫⁻ y, (({x ∈ A | f x = y}.encard : ℕ∞) : ℝ≥0∞) ∂(μH[(k : ℝ)])

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StHolomorphicOnSubset
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def HolomorphicOnSubset {σ : Type*} [Fintype σ] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : (σ → ℂ) → E) (S : Set (σ → ℂ)) : Prop :=
  ∀ z ∈ S, ∃ U : Set (σ → ℂ), IsOpen U ∧ z ∈ U ∧ ∃ F : (σ → ℂ) → E,
    DifferentiableOn ℂ F U ∧ Set.EqOn f F (S ∩ U)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFlatNormalFibres
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

abbrev primeFibreLocalRing (R : Type*) {S : Type*} [CommRing R] [CommRing S] [Algebra R S] (P : Ideal S)
    [P.IsPrime] : Type _ :=
  Localization.AtPrime P ⧸
    Ideal.map (algebraMap S (Localization.AtPrime P)) (Ideal.map (algebraMap R S) (Ideal.comap (algebraMap R S) P))

def FlatNormalFibres.Statement : Prop :=
  ∀ (R S : Type) [CommRing R] [CommRing S] [Algebra R S],
    IsNoetherianRing R → IsNoetherianRing S → IsLocalRing S → Module.Flat R S →
      IsDomain R → IsIntegrallyClosed R →
      (∀ (P : Ideal S) [P.IsPrime],
        IsDomain (primeFibreLocalRing R P) ∧ IsIntegrallyClosed (primeFibreLocalRing R P)) →
        IsDomain S ∧ IsIntegrallyClosed S

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGenericPrimitive
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

noncomputable section

def GenericPrimitive.Statement : Prop :=
  ∀ (k K L : Type) [Field k] [Field K] [Field L] [Algebra k K] [Algebra K L] [Algebra k L]
    [IsScalarTower k K L] [FiniteDimensional K L] [Algebra.IsSeparable K L] (n : ℕ) (x : Fin n → L),
    IntermediateField.adjoin K (Set.range x) = ⊤ →
      ∃ D : MvPolynomial (Fin n) k, D ≠ 0 ∧ ∀ c : Fin n → k, MvPolynomial.eval c D ≠ 0 →
        IntermediateField.adjoin K {∑ j, c j • x j} = ⊤

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StUnbranchedProperCountConstant
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def UnbranchedProperCountConstant.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (Y : Set (σ → ℂ)) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ))
    (D : Set (Fin d → ℂ)) (δ : (Fin d → ℂ) → ℂ),
    IsOpen D → IsPreconnected D → Set.MapsTo A Y D →
    (∀ K ⊆ D, IsCompact K → IsCompact {x | x ∈ Y ∧ A x ∈ K}) →
    AnalyticOnNhd ℂ δ D →
    (∀ x ∈ Y, δ (A x) ≠ 0 → ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (g : (Fin d → ℂ) → σ → ℂ),
      IsOpen O ∧ IsOpen V ∧ x ∈ V ∧ ContinuousOn g O ∧ (∀ y ∈ O, A (g y) = y) ∧ Y ∩ V = g '' O) →
    ∃ N : ℕ, ∀ y ∈ D, δ y ≠ 0 → {x | x ∈ Y ∧ A x = y}.encard = N

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRiemannExtensionAnalytic
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

noncomputable section

def RiemannExtensionAnalytic.Statement : Prop :=
  ∀ (k : ℕ) (U : Set (Fin k → ℂ)) (g f : (Fin k → ℂ) → ℂ),
    IsOpen U → DifferentiableOn ℂ g U →
    (∀ V : Set (Fin k → ℂ), IsOpen V → V ⊆ U → V.Nonempty → ∃ t ∈ V, g t ≠ 0) →
    DifferentiableOn ℂ f (U ∩ {t | g t ≠ 0}) →
    (∀ τ ∈ U, ∃ N ∈ 𝓝 τ, Bornology.IsBounded (f '' (N ∩ U ∩ {t | g t ≠ 0}))) →
    ∃ F : (Fin k → ℂ) → ℂ, DifferentiableOn ℂ F U ∧ Set.EqOn F f (U ∩ {t | g t ≠ 0})

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGraphJacContinuous
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open scoped ENNReal NNReal

noncomputable section

def graphJac {k m : ℕ} (B : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) : ℝ :=
  √(LinearMap.det ((1 : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)) +
    LinearMap.adjoint B ∘ₗ B))

def GraphJacContinuous.Statement : Prop :=
  ∀ (k m : ℕ) (A : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m)) (ε : ℝ), 0 < ε →
    ∃ r : ℝ, 0 < r ∧ ∀ B : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m), ‖B - A‖ ≤ r →
      graphJac (B : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) ≤
          (1 + ε) * graphJac (A : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) ∧
        graphJac (A : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) ≤
          (1 + ε) * graphJac (B : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StInjectiveHolomorphicOpen
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def InjectiveHolomorphicOpen.Statement : Prop :=
  ∀ (k : ℕ) (U : Set (Fin k → ℂ)) (f : (Fin k → ℂ) → Fin k → ℂ),
    IsOpen U → DifferentiableOn ℂ f U → Set.InjOn f U → IsOpen (f '' U)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFlatDimFormula
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing

def FlatDimFormula.Statement : Prop :=
  ∀ (A B : Type) [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] [Algebra A B],
    IsNoetherianRing A → IsNoetherianRing B → IsLocalHom (algebraMap A B) → Module.Flat A B →
      ringKrullDim B = ringKrullDim A + ringKrullDim (B ⧸ (maximalIdeal A).map (algebraMap A B))

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCompactHolomorphicFibreFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Metric

def CompactHolomorphicFibreFinite.Statement : Prop :=
  ∀ (k m : ℕ) (U : Set (Fin k → ℂ)) (f : (Fin k → ℂ) → Fin m → ℂ) (y : Fin m → ℂ),
    IsOpen U → DifferentiableOn ℂ f U → IsCompact {v | v ∈ U ∧ f v = y} →
      {v | v ∈ U ∧ f v = y}.Finite

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StHolomorphicFibreInfinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

noncomputable section

def HolomorphicFibreInfinite.Statement : Prop :=
  ∀ (k d : ℕ) (U : Set (Fin k → ℂ)) (f : (Fin k → ℂ) → Fin d → ℂ),
    d < k → IsOpen U → U.Nonempty → DifferentiableOn ℂ f U →
      ∃ y : Fin d → ℂ, {t | t ∈ U ∧ f t = y}.Infinite

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCriticalImageNull
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MeasureTheory

noncomputable section

def CriticalImageNull.Statement : Prop :=
  ∀ (d n : ℕ) (U : Set (Fin d → ℂ)) (f : (Fin d → ℂ) → Fin n → ℂ), IsOpen U →
    DifferentiableOn ℂ f U →
      μH[((2 * d : ℕ) : ℝ)] (f '' {s | s ∈ U ∧ ¬ Function.Injective (fderiv ℂ f s)}) = 0

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StParametricCircleIntegralAnalytic
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Metric

noncomputable section

def ParametricCircleIntegralAnalytic.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] (Φ : (ι → ℂ) × ℂ → ℂ) (O : Set ((ι → ℂ) × ℂ)) (U : Set (ι → ℂ)) (c : ℂ) (r : ℝ),
    0 ≤ r → IsOpen O → IsOpen U → DifferentiableOn ℂ Φ O →
    (∀ x ∈ U, ∀ s ∈ sphere c r, (x, s) ∈ O) →
    AnalyticOnNhd ℂ (fun x => ∮ s in C(c, r), Φ (x, s)) U

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSimpleRootBranch
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

def SimpleRootBranch.Statement : Prop :=
  ∀ (d : ℕ) (p : Polynomial (MvPolynomial (Fin d) ℂ)) (y : Fin d → ℂ) (τ : ℂ),
    (p.map (MvPolynomial.eval y)).IsRoot τ →
      (p.map (MvPolynomial.eval y)).derivative.eval τ ≠ 0 →
        ∃ (U : Set (Fin d → ℂ)) (B : Set ℂ) (ψ : (Fin d → ℂ) → ℂ),
          IsOpen U ∧ y ∈ U ∧ IsOpen B ∧ τ ∈ B ∧ DifferentiableOn ℂ ψ U ∧ ψ y = τ ∧
            ∀ w ∈ U, ψ w ∈ B ∧
              ∀ s ∈ B, ((p.map (MvPolynomial.eval w)).IsRoot s ↔ s = ψ w)

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.HeightCoheightQuotient
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem ringKrullDim_quotient_eq_coheight {B : Type*} [CommRing B] (P : Ideal B) [hP : P.IsPrime] :
    ringKrullDim (B ⧸ P) = Order.coheight (⟨P, hP⟩ : PrimeSpectrum B) := by
  rw [ringKrullDim_quotient, Order.coheight_eq_krullDim_Ici]
  have h : PrimeSpectrum.zeroLocus (P : Set B) = Set.Ici (⟨P, hP⟩ : PrimeSpectrum B) := by
    ext q
    rw [PrimeSpectrum.mem_zeroLocus, Set.mem_Ici, ← PrimeSpectrum.asIdeal_le_asIdeal]
    exact SetLike.coe_subset_coe
  rw [h]

theorem height_add_ringKrullDim_quotient_le {B : Type*} [CommRing B] (P : Ideal B) [hP : P.IsPrime] :
    (P.height : WithBot ℕ∞) + ringKrullDim (B ⧸ P) ≤ ringKrullDim B := by
  have : Nonempty (PrimeSpectrum B) := ⟨⟨P, hP⟩⟩
  rw [ringKrullDim_quotient_eq_coheight, PrimeSpectrum.height_eq_orderHeight ⟨P, hP⟩, ringKrullDim,
    Order.krullDim_eq_iSup_height_add_coheight_of_nonempty, ← WithBot.coe_add, WithBot.coe_le_coe]
  exact le_iSup (fun a : PrimeSpectrum B => Order.height a + Order.coheight a) ⟨P, hP⟩

theorem height_map_add_one_le_of_mem_nonZeroDivisors {B : Type*} [CommRing B] [IsNoetherianRing B] {y : B}
    (hy : y ∈ nonZeroDivisors B) (P : Ideal B) [hP : P.IsPrime] (hyP : y ∈ P) :
    (P.map (Ideal.Quotient.mk (Ideal.span {y}))).height + 1 ≤ P.height := by
  set I := Ideal.span {y} with hI
  have hIP : I ≤ P := (Ideal.span_singleton_le_iff_mem P).mpr hyP
  have hP' : (P.map (Ideal.Quotient.mk I)).IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hIP
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (P.map (Ideal.Quotient.mk I)).height = n :=
    ENat.ne_top_iff_exists.mp (Ideal.height_ne_top hP'.ne_top) |>.imp fun _ h => h.symm
  rw [hn]
  obtain ⟨l, hlast, hlen⟩ := Order.exists_series_of_height_eq_coe (⟨_, hP'⟩ : PrimeSpectrum (B ⧸ I))
    (by rw [← PrimeSpectrum.height_eq_orderHeight]; exact hn)
  let f : PrimeSpectrum (B ⧸ I) → PrimeSpectrum B := PrimeSpectrum.comap (Ideal.Quotient.mk I)
  have hf : StrictMono f := by
    refine Monotone.strictMono_of_injective (fun a b hab => ?_) (fun a b hab => ?_)
    · rw [← PrimeSpectrum.asIdeal_le_asIdeal] at hab ⊢
      exact Ideal.comap_mono hab
    · ext1
      have := congrArg PrimeSpectrum.asIdeal hab
      exact Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective this
  let L := l.map f hf
  have hyhead : y ∈ L.head.asIdeal := by
    change y ∈ (l.head.asIdeal).comap (Ideal.Quotient.mk I)
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self y)]
    exact Ideal.zero_mem _
  obtain ⟨p, hp, hple⟩ := Ideal.exists_minimalPrimes_le (J := L.head.asIdeal) bot_le
  let p0 : PrimeSpectrum B := ⟨p, hp.1.1⟩
  have hlt : p0 < L.head := by
    refine lt_of_le_of_ne ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mp hple) fun h => ?_
    have hyp : y ∈ p := by
      have : p = L.head.asIdeal := congrArg PrimeSpectrum.asIdeal h
      rw [this]
      exact hyhead
    exact Set.disjoint_iff.mp (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hp) ⟨hyp, hy⟩
  let L' := L.cons p0 hlt
  have hLlast : L'.last = ⟨P, hP⟩ := by
    simp only [L', L, RelSeries.last_cons, LTSeries.last_map, hlast]
    ext1
    exact Ideal.comap_map_mk hIP
  have hlen' : L'.length = n + 1 := by
    simp [L', L, hlen]
  have := Order.length_le_height_last (p := L')
  rw [hLlast, hlen', ← PrimeSpectrum.height_eq_orderHeight] at this
  exact_mod_cast this

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StInjectiveHolomorphicDerivNeZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

def InjectiveHolomorphicDerivNeZero.Statement : Prop :=
  ∀ (D : Set ℂ) (f : ℂ → ℂ), IsOpen D → DifferentiableOn ℂ f D → Set.InjOn f D → ∀ a ∈ D, deriv f a ≠ 0

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StHolomorphicIsolatedFibreOpen
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def HolomorphicIsolatedFibreOpen.Statement : Prop :=
  ∀ (k : ℕ) (U : Set (Fin k → ℂ)) (g : (Fin k → ℂ) → Fin k → ℂ) (u : Fin k → ℂ),
    IsOpen U → u ∈ U → DifferentiableOn ℂ g U →
    (∃ W ∈ 𝓝 u, ∀ v ∈ W, v ∈ U → g v = g u → v = u) →
    ∀ V ∈ 𝓝 u, g '' V ∈ 𝓝 (g u)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRankDeficientFibreInfinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Metric

def RankDeficientFibreInfinite.Statement : Prop :=
  ∀ (k m : ℕ) (U : Set (Fin k → ℂ)) (f : (Fin k → ℂ) → Fin m → ℂ),
    IsOpen U → U.Nonempty → DifferentiableOn ℂ f U →
    (∀ v ∈ U, ¬ Function.Injective (fderiv ℂ f v)) →
      ∃ y : Fin m → ℂ, {t | t ∈ U ∧ f t = y}.Infinite

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRueckertNullstellensatz
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

def RueckertNullstellensatz.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (w : σ → ℂ) (k : ℕ) (f : Fin k → (σ → ℂ) → ℂ) (g : (σ → ℂ) → ℂ),
    (∀ i, AnalyticAt ℂ (f i) w) → AnalyticAt ℂ g w →
    (∀ᶠ z in 𝓝 w, (∀ i, f i z = 0) → g z = 0) →
    ∃ (m : ℕ) (h : Fin k → (σ → ℂ) → ℂ), 0 < m ∧ (∀ i, AnalyticAt ℂ (h i) w) ∧
      ∀ᶠ z in 𝓝 w, g z ^ m = ∑ i, h i z * f i z

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGeneralProjection
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Matrix

noncomputable section

def GeneralProjection.Statement : Prop :=
  ∀ (n d m : ℕ) (L : Fin m → (Fin d → ℂ) →ₗ[ℂ] (Fin n → ℂ)), (∀ b, Function.Injective (L b)) →
    ∃ π : Matrix (Fin d) (Fin n) ℂ, ∀ b, Function.Injective fun v => π *ᵥ L b v

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StUnitaryZariskiDense
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

def UnitaryZariskiDense.Statement : Prop :=
  ∀ (n : ℕ) (p : MvPolynomial (Fin n × Fin n) ℂ), p ≠ 0 →
    ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ, eval (fun ij : Fin n × Fin n => U ij.1 ij.2) p ≠ 0

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSeparateWeierstrassDivision
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

def SeparateWeierstrassDivision.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (d : ℕ) (y₀ : Fin d → ℂ) (u₀ : σ → ℂ) (n : σ → ℕ)
    (b : (m : σ) → Fin (n m) → (Fin d → ℂ) → ℂ) (f : (Fin d → ℂ) × (σ → ℂ) → ℂ),
    (∀ m j, AnalyticAt ℂ (b m j) y₀) →
    (∀ m (T : ℂ), T ^ n m + ∑ j, b m j y₀ * T ^ (j : ℕ) = (T - u₀ m) ^ n m) →
    AnalyticAt ℂ f (y₀, u₀) →
    ∃ (v : σ → (Fin d → ℂ) × (σ → ℂ) → ℂ) (r : ((m : σ) → Fin (n m)) → (Fin d → ℂ) → ℂ),
      (∀ m, AnalyticAt ℂ (v m) (y₀, u₀)) ∧ (∀ α, AnalyticAt ℂ (r α) y₀) ∧
      ∀ᶠ x in 𝓝 (y₀, u₀),
        f x = ∑ m, v m x * (x.2 m ^ n m + ∑ j, b m j x.1 * x.2 m ^ (j : ℕ)) +
          ∑ α, r α x.1 * ∏ m, x.2 m ^ (α m : ℕ)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceMatricesOpen
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

def SliceMatricesOpen.Statement : Prop :=
  ∀ (n k m : ℕ) (γ : Fin m → (Fin (k + 1) → ℂ) → Fin n → ℂ) (s : Fin m → Fin (k + 1) → ℂ),
    (∀ b, DifferentiableAt ℂ (γ b) (s b)) →
    (∀ b (v : Fin (k + 1) → ℂ), v 0 = 0 → fderiv ℂ (γ b) (s b) v = 0 → v = 0) →
      IsOpen {L : Matrix (Fin k) (Fin n) ℂ |
          ∀ b, Function.Bijective (fderiv ℂ (fun t => vecCons (t 0) (L *ᵥ γ b t)) (s b))} ∧
        {L : Matrix (Fin k) (Fin n) ℂ |
          ∀ b, Function.Bijective (fderiv ℂ (fun t => vecCons (t 0) (L *ᵥ γ b t)) (s b))}.Nonempty

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCentredDiscCoverCurve
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Metric

def IsCentredDiscCover {σ : Type} [Fintype σ] (Y : Set (σ → ℂ)) (w : σ → ℂ) (p : (σ → ℂ) →L[ℂ] ℂ)
    (ρ : ℝ) (N : ℕ) : Prop :=
  w ∈ Y ∧ 0 < N ∧ Set.MapsTo p Y (ball (p w) ρ) ∧ (∀ x ∈ Y, p x = p w → x = w) ∧
    (∀ t ∈ ball (p w) ρ, t ≠ p w → {x | x ∈ Y ∧ p x = t}.encard = N) ∧
    (∀ K ⊆ ball (p w) ρ, IsCompact K → IsCompact {x | x ∈ Y ∧ p x ∈ K}) ∧
    (∀ x ∈ Y, p x ≠ p w → ∃ (O : Set ℂ) (V : Set (σ → ℂ)) (g : ℂ → σ → ℂ), IsOpen O ∧ IsOpen V ∧ x ∈ V ∧
      DifferentiableOn ℂ g O ∧ (∀ t ∈ O, p (g t) = t) ∧ Y ∩ V = g '' O)

def CentredDiscCoverCurve.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (Y : Set (σ → ℂ)) (w : σ → ℂ) (p : (σ → ℂ) →L[ℂ] ℂ) (ρ : ℝ) (N : ℕ),
    IsCentredDiscCover Y w p ρ N →
      ∃ r : ℝ, 0 < r ∧ ∃ γ : ℂ → σ → ℂ,
        DifferentiableOn ℂ γ (ball 0 r) ∧ Set.InjOn γ (ball 0 r) ∧ γ 0 = w ∧ Set.MapsTo γ (ball 0 r) Y

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StImplicitCurve
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Topology

noncomputable section

def ImplicitCurve.Statement : Prop :=
  ∀ (n k : ℕ) (γ : (Fin (k + 1) → ℂ) → Fin n → ℂ) (R : ℝ) (L : Matrix (Fin k) (Fin n) ℂ)
    (s : Fin (k + 1) → ℂ),
    DifferentiableOn ℂ γ (Metric.ball 0 R) → s ∈ Metric.ball 0 R →
    Function.Bijective (fderiv ℂ (fun t => vecCons (t 0) (L *ᵥ γ t)) s) →
      ∃ r > 0, ∃ φ : (Fin 1 → ℂ) → Fin (k + 1) → ℂ,
        DifferentiableOn ℂ φ (Metric.ball 0 r) ∧ φ 0 = s ∧
        (∀ τ ∈ Metric.ball 0 r,
          φ τ ∈ Metric.ball 0 R ∧ φ τ 0 = s 0 + τ 0 ∧ L *ᵥ γ (φ τ) = L *ᵥ γ s) ∧
        ∃ P ∈ 𝓝 s, ∀ t ∈ P, L *ᵥ γ t = L *ᵥ γ s → ∃ τ ∈ Metric.ball 0 r, φ τ = t

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StAreaGraphPartition
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open scoped ENNReal NNReal

noncomputable section

def AreaGraphPartition.Statement : Prop :=
  ∀ (k m : ℕ) (U : Set (EuclideanSpace ℝ (Fin k)))
    (F : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin m)),
    IsOpen U → ContDiffOn ℝ 1 F U →
      ∀ r : (EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m)) → ℝ≥0, (∀ A, r A ≠ 0) →
        ∃ (t : ℕ → Set (EuclideanSpace ℝ (Fin k)))
          (A : ℕ → EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m)),
          Pairwise (Function.onFun Disjoint t) ∧ (∀ n, MeasurableSet (t n)) ∧ (∀ n, t n ⊆ U) ∧
            U ⊆ ⋃ n, t n ∧ (∀ n, ApproximatesLinearOn F (A n) (t n) (r (A n))) ∧
              ∀ n, ∀ x ∈ t n, ‖fderiv ℝ F x - A n‖₊ ≤ r (A n)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGenericFibreTor
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem ker_fibreMap {σ ι : Type*} (t : σ → ℂ) :
    RingHom.ker (MvPolynomial.map (eval t) : MvPolynomial ι (MvPolynomial σ ℂ) →+* MvPolynomial ι ℂ) =
      (RingHom.ker (eval t : MvPolynomial σ ℂ →+* ℂ)).map (C : MvPolynomial σ ℂ →+* MvPolynomial ι (MvPolynomial σ ℂ)) :=
  MvPolynomial.ker_map _

def GenericFibreTor.Statement : Prop :=
  ∀ (σ : Type) [Finite σ] (ι : Type) [Finite ι] (L : Ideal (MvPolynomial ι (MvPolynomial σ ℂ))),
    ∃ F : MvPolynomial σ ℂ, F ≠ 0 ∧ ∀ t : σ → ℂ, eval t F ≠ 0 →
      L ⊓ RingHom.ker (MvPolynomial.map (eval t) : MvPolynomial ι (MvPolynomial σ ℂ) →+* MvPolynomial ι ℂ) ≤
        RingHom.ker (MvPolynomial.map (eval t) : MvPolynomial ι (MvPolynomial σ ℂ) →+* MvPolynomial ι ℂ) * L

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteModuloIntegral
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

def IsFiniteModuloOver {σ τ : Type} [Fintype σ] [Fintype τ] (x : σ → ℂ) {k : ℕ}
    (f : Fin k → (σ → ℂ) → ℂ) (L : (σ → ℂ) →L[ℂ] (τ → ℂ)) : Prop :=
  ∃ (n : ℕ) (e : Fin n → (σ → ℂ) → ℂ), (∀ m, AnalyticAt ℂ (e m) x) ∧
    ∀ g : (σ → ℂ) → ℂ, AnalyticAt ℂ g x →
      ∃ (b : Fin n → (τ → ℂ) → ℂ) (h : Fin k → (σ → ℂ) → ℂ),
        (∀ m, AnalyticAt ℂ (b m) (L x)) ∧ (∀ i, AnalyticAt ℂ (h i) x) ∧
        ∀ᶠ z in 𝓝 x, g z = ∑ m, b m (L z) * e m z + ∑ i, h i z * f i z

def FiniteModuloIntegral.Statement : Prop :=
  ∀ (σ τ : Type) [Fintype σ] [Fintype τ] (x : σ → ℂ) (k : ℕ) (f : Fin k → (σ → ℂ) → ℂ)
    (L : (σ → ℂ) →L[ℂ] (τ → ℂ)),
    (∀ i, AnalyticAt ℂ (f i) x) → IsFiniteModuloOver x f L →
    ∀ g : (σ → ℂ) → ℂ, AnalyticAt ℂ g x →
      ∃ (N : ℕ) (a : Fin N → (τ → ℂ) → ℂ) (h : Fin k → (σ → ℂ) → ℂ),
        (∀ j, AnalyticAt ℂ (a j) (L x)) ∧ (∀ i, AnalyticAt ℂ (h i) x) ∧
        ∀ᶠ z in 𝓝 x, g z ^ N + ∑ j, a j (L z) * g z ^ (j : ℕ) = ∑ i, h i z * f i z

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPerfectFieldExtensionFormallySmooth
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def PerfectFieldExtensionFormallySmooth.Statement : Prop :=
  ∀ (F K : Type) [Field F] [Field K] [Algebra F K] [PerfectField F], Algebra.FormallySmooth F K

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPolyKaehlerFree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def PolyKaehlerFree.Statement : Prop :=
  ∀ (R k : Type) [Field R] [Field k] [Algebra R k] (n : ℕ),
    Module.Free (MvPolynomial (Fin n) k) Ω[MvPolynomial (Fin n) k⁄R]

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StInvarianceOfDomain
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def InvarianceOfDomain.Statement : Prop :=
  ∀ (n : ℕ) (U : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → Fin n → ℝ),
    IsOpen U → ContinuousOn f U → Set.InjOn f U → IsOpen (f '' U)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBrouwerFixedPoint
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def BrouwerFixedPoint.Statement : Prop :=
  ∀ (n : ℕ) (f : (Fin n → ℝ) → Fin n → ℝ),
    ContinuousOn f (Metric.closedBall 0 1) →
      Set.MapsTo f (Metric.closedBall 0 1) (Metric.closedBall 0 1) →
        ∃ x ∈ Metric.closedBall (0 : Fin n → ℝ) 1, f x = x

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end
