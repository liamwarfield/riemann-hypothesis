module

public import GroundTheory.HeightsAndTheta.Heights.FlagBundles.Statements

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.FlagBundles.StatementsSphereLongitude
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open MeasureTheory

noncomputable section

def SphereLongitudeCoordinates.Statement : Prop :=
  sphereMeasure.map (fun n : Sphere2 => (n : E3)) =
    (ENNReal.ofReal (4 * Real.pi))⁻¹ •
      (volume.restrict (Set.Icc (-1 : ℝ) 1 ×ˢ Set.Ioc 0 (2 * Real.pi))).map
        (fun p : ℝ × ℝ => spherePoint p.1 p.2)

end

end GroundTheory.Heights₂.Heights.FlagBundles
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FlagBundles.StatementsZonalReduction
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

def ZonalHeightReduction.Statement : Prop :=
  ∀ F H : Polynomial ℝ,
    Integrable (fun p : Sphere2 × Sphere2 =>
      kernelL ⟪(p.1 : E3), (p.2 : E3)⟫_ℝ * F.eval (height p.1) * H.eval (height p.2)) pairMeasure ∧
    ∫ p, kernelL ⟪(p.1 : E3), (p.2 : E3)⟫_ℝ * F.eval (height p.1) * H.eval (height p.2)
        ∂pairMeasure =
      (1 / 4) * ∫ c₁ in (-1 : ℝ)..1, ∫ c₂ in (-1 : ℝ)..1, zonalKernel c₁ c₂ * F.eval c₁ * H.eval c₂

end

end GroundTheory.Heights₂.Heights.FlagBundles
end
