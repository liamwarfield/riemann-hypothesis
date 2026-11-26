module

public import ReciprocityTheory.AnalyticForms.PotentialTheory.IsCompatChartRestrOpen

@[expose] public section

namespace ReciprocityTheory.AnForm.M

open MeasureTheory FinHolAtlas
open scoped ContDiff

noncomputable section

theorem poincareLelong : PoincareLelongStatement := PLAux.pl_global

end

end ReciprocityTheory.AnForm.M
