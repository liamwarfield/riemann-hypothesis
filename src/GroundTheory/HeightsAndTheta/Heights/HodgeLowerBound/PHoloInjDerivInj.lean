module

public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsHoloInjDerivInj
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceImmersiveGeneral
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.SpecFirstDetFormNeZero

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHoloInjDerivInj
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

theorem HoloInjDerivInj.proof : HoloInjDerivInj.Statement := by
  intro m f U hU hf hinj u hu
  have hdet : LinearMap.det (fderiv ℂ f u : (Fin m → ℂ) →ₗ[ℂ] Fin m → ℂ) ≠ 0 :=
    IndefiniteRowSideFullHecke.ComplexSets.InjectiveHolomorphicJacobianNeZero.proof IndefiniteRowSideFullHecke.ComplexSets.HolomorphicKernelFibre.proof
      IndefiniteRowSideFullHecke.ComplexSets.CriticalFlatNotInjective.proof m U f hU hf.differentiableOn hinj u hu
  have hunit : IsUnit (fderiv ℂ f u : (Fin m → ℂ) →ₗ[ℂ] Fin m → ℂ) :=
    (LinearMap.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet)
  exact ((Module.End.isUnit_iff _).1 hunit).injective

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsDimX
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar PBlk)

abbrev DimX.genericCone {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) : Type :=
  Localization (Algebra.algebraMapSubmonoid (MRing ι ⧸ P) (nonZeroDivisors ℤ))

def DimX.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ),
    IsArithVar P (n + 1) →
      ringKrullDim (DimX.genericCone P) = ((n + Fintype.card K : ℕ) : WithBot ℕ∞)

end GroundTheory.Heights₂.Heights
end
end
