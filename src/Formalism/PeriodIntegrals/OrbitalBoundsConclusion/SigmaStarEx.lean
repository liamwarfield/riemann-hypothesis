module

public import Mathlib
public import Formalism.PeriodIntegrals.QuotInv
public import Formalism.PeriodIntegrals.SigmaStarEx
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ThetaSeriesExistence.SigmaStarEx

@[expose] public section

theorem sigma_star_exists : PI.SigmaStarEx := PI.SSE.sigmaStarEx
