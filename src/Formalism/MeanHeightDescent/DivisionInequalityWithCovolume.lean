module

public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.TheoremDivIneq
public import Formalism.MeanHeightDescent.AverageDegreeBounds.TwistLower
public import Formalism.MeanHeightDescent.AverageDegreeBounds.GoodBadCut
public import Formalism.MeanHeightDescent.AverageDegreeBounds.SumComponents

@[expose] public section

namespace Formalism.ExtensionFiltration

theorem lcvMu : LcvMu := log_covolume_slope_mu
theorem descentSlope : DescentSlope := descent_slope
theorem spanMuMin : SpanMuMin := span_min_slope
theorem goodBadCut : GoodBadCut := good_bad_split
theorem twistLower : TwistLower := twist_lower_bound
theorem muMaxMinkowski : MuMaxMinkowski := max_slope_minkowski
theorem mean_height_sum_bound : CombinedAverageDegreeBound := mean_height_sum_bound_holds

end Formalism.ExtensionFiltration
