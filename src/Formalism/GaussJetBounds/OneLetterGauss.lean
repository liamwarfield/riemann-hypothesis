module

public import Formalism.GaussJetBounds.GaussJetProofs.OneGauss
public import Formalism.GaussJetBounds.ThmAGauss

@[expose] public section

section -- merged from Formalism.GaussJetBounds.GaussJetProofs.CoefficientBoundMembership
noncomputable section
open scoped BigOperators

namespace Formalism.DworkPowerSeriesWeights

open MvPolynomial Formalism.IncomingBounds

end Formalism.DworkPowerSeriesWeights
end
end

namespace Formalism.DworkPowerSeriesWeights

theorem oneLetterGauss : OneLetterGauss := one_letter_gauss_sum

end Formalism.DworkPowerSeriesWeights
