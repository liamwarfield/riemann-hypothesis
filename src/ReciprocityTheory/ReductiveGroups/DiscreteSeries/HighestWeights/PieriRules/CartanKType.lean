module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousRepresentations.URepCompRed
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.StdExpEntryHasDerivAt
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Unique

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.DS.HW

theorem pieriStd : PieriStdStatement := pieriStd_of compRed kRepRel

theorem pieriDual : PieriDualStatement := pieriDual_of compRed kRepRel

end ReciprocityTheory.ChartRestriction.DS.HW
