module

public import Mathlib

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsZeroLocusDimH
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def ZeroLocusDimH.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)),
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) ≤ d →
      dimH {x : Fin n → ℂ | ∀ q ∈ J, eval x q = 0} ≤ 2 * (d : ENNReal)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsLocalSectionLengthSum
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

def LocalSectionLengthSum.Statement : Prop :=
  ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [IsLocalRing B] (J : Ideal B) (f : B),
    J.IsRadical →
    (∀ P ∈ J.minimalPrimes, f ∉ P) →
    (∀ Q : Ideal B, Q.IsPrime → J ≤ Q → Q ∈ J.minimalPrimes ∨ Q = IsLocalRing.maximalIdeal B) →
      Module.length B (B ⧸ (J ⊔ Ideal.span {f})) =
        ∑ P ∈ (J.finite_minimalPrimes_of_isNoetherianRing B).toFinset,
          Module.length B (B ⧸ (P ⊔ Ideal.span {f}))

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsKernelProjMeasurable
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

noncomputable section

def KernelProjMeasurable.Statement : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] (n k : ℕ)
    (L : X → Matrix (Fin k) (Fin n) ℂ), Continuous L →
      Measurable fun x => (LinearMap.ker (Matrix.toEuclideanLin (L x))).starProjection

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsPiQuotCokerFiniteLength
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

def quotToPiMinimalPrimes {B : Type*} [CommRing B] (J : Ideal B) :
    (B ⧸ J) →ₗ[B] ((P : J.minimalPrimes) → B ⧸ (P : Ideal B)) :=
  LinearMap.pi fun P => Submodule.factor P.2.1.2

def PiQuotCokerFiniteLength.Statement : Prop :=
  ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [IsLocalRing B] (J : Ideal B),
    J.IsRadical →
    (∀ Q : Ideal B, Q.IsPrime → J ≤ Q → Q ∈ J.minimalPrimes ∨ Q = IsLocalRing.maximalIdeal B) →
      Function.Injective (quotToPiMinimalPrimes J) ∧
        IsFiniteLength B
          (((P : J.minimalPrimes) → B ⧸ (P : Ideal B)) ⧸ LinearMap.range (quotToPiMinimalPrimes J))

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsTrdegBaseAlgebraic
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

def TrdegBaseAlgebraic.Statement : Prop :=
  ∀ (F K Ω : Type) [Field F] [Field K] [Field Ω] [Algebra F K] [Algebra K Ω] [Algebra F Ω]
    [IsScalarTower F K Ω], Algebra.IsAlgebraic F K → ∀ (ι : Type) (z : ι → Ω),
      Algebra.trdeg K (Algebra.adjoin K (Set.range z)) ≤ Algebra.trdeg F (Algebra.adjoin F (Set.range z))

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsTrdegAdjoinLe
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

def TrdegAdjoinLe.Statement : Prop :=
  ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (s : Set Ω) (ι : Type) [Fintype ι] (t : ι → Ω)
    (ι' : Type) (w : ι' → Ω), (∀ i, IsAlgebraic (Algebra.adjoin K (s ∪ Set.range t)) (w i)) →
      Algebra.trdeg K (Algebra.adjoin K (Set.range w)) ≤
        Algebra.trdeg K (Algebra.adjoin K s) + Fintype.card ι

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsAreaMultiplicityWeight
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

open scoped ENNReal

noncomputable section

def AreaMultiplicityWeight.Statement : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (A : Set E) (f : E → E)
    (f' : E → E →L[ℝ] E), MeasurableSet A → (∀ x ∈ A, HasFDerivWithinAt f (f' x) A x) →
      AEMeasurable (fun y => (({x ∈ A | f x = y}.encard : ℕ∞) : ℝ≥0∞)) μ ∧
        ∀ g : E → ℝ≥0∞, Measurable g →
          ∫⁻ x in A, g (f x) * ENNReal.ofReal |(f' x).det| ∂μ =
            ∫⁻ y, (({x ∈ A | f x = y}.encard : ℕ∞) : ℝ≥0∞) * g y ∂μ

end

end GroundTheory.Heights₂.Heights
end
