module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothCutoffSlopeThreeQuarters
public import ReciprocityTheory.L2DbarEstimates.NormFibrations.Hormander
public import ReciprocityTheory.L2DbarEstimates.NormFibrations.ImportsAlt
public import ReciprocityTheory.L2DbarEstimates.NormFibrations.LseSmoothRIffReal
public import ReciprocityTheory.L2DbarEstimates.NormFibrations.MvBlowup
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup

@[expose] public section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smoothCutoff_slope_three_quarters : ∀ T : ℝ, ∃ θ : ℝ → ℝ, IsCut T θ := by
  first | exact @GlobalTheory.exists_isCut₂ | exact GlobalTheory.exists_isCut₂ | (intros; apply GlobalTheory.exists_isCut₂ <;> assumption)
