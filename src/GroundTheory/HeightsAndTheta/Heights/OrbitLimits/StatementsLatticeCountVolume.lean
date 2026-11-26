module

public import Mathlib

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsLatticeCountVolume
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MeasureTheory
open scoped ENNReal

def LatticeCountVolume.Statement : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (La : Submodule ℤ E) [DiscreteTopology La]
    [IsZLattice ℝ La] (S T : Set E), MeasurableSet S → (∀ x ∈ S, ∀ y ∈ S, x - y ∈ T) →
      μ S ≤ (({x : E | x ∈ La ∧ x ∈ T}.encard : ℕ∞) : ℝ≥0∞) * ENNReal.ofReal (ZLattice.covolume La μ)

end GroundTheory.Heights₂.Heights.Targets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StCriticalFibreInfinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

def CriticalFibreInfinite.Statement : Prop :=
  ∀ (k d : ℕ) (U : Set (Fin k → ℂ)) (f : (Fin k → ℂ) → Fin d → ℂ),
    IsOpen U → U.Nonempty → DifferentiableOn ℂ f U →
      (∀ t ∈ U, ¬ Function.Injective (fderiv ℂ f t)) →
        ∃ y : Fin d → ℂ, {t | t ∈ U ∧ f t = y}.Infinite

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsMixedBoxCount
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding


open scoped Classical in
def MixedBoxCount.Statement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (La : Submodule ℤ (mixedSpace F)) [DiscreteTopology La]
    [IsZLattice ℝ (E := mixedSpace F) La] (f : InfinitePlace F → ℝ), (∀ w, 0 < f w) →
      {y : mixedSpace F | y ∈ La ∧ ∀ w, normAtPlace w y ≤ f w}.Finite ∧
        Real.log (convexBodyLTFactor F : ℝ) + ∑ w, (mult w : ℝ) * Real.log (f w) -
            Module.finrank ℚ F * Real.log 2 - Real.log (ZLattice.covolume La) ≤
          Real.log ({y : mixedSpace F | y ∈ La ∧ ∀ w, normAtPlace w y ≤ f w}.ncard : ℝ)

end GroundTheory.Heights₂.Heights.Targets
end
