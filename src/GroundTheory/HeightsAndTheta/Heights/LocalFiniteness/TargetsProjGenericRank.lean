module

public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.TargetsCurveVertPointLength
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveSectionQuotFinite
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsPosPartLocal

@[expose] public section

set_option maxSynthPendingDepth 1

theorem GroundTheory.Heights₂.Heights.AutoClose.DefectAverage : GroundTheory.Heights₂.Heights.DefectAverage.Statement :=
  @GroundTheory.Heights₂.Heights.DefectAverage.proof GroundTheory.Heights₂.Heights.AutoClose.MahlerAverageSplit GroundTheory.Heights₂.Heights.AutoClose.CycleAverage
