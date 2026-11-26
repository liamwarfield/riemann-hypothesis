module

public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ReductionLemmaSecond
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ReductionSecondStep
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.SecondComplementParameterBounds
public import Formalism.LogFactorialIndices.SignedSubspaceIndex.IdxBase

@[expose] public section

namespace Formalism.DivisionValues

theorem reduction_lemma_zero : GramDeterminantQuotientMetric := gram_determinant_quotient_metric
theorem lemmaRb : LemmaRb := reduction_lemma_second
theorem specDet : SpecDet := spectral_determinant_formula
theorem stepA : StepA := reduction_first_step

theorem interlace : Formalism.LatticeIndexTer.Interlace := Formalism.LatticeIndexTer.sumInterlacedBound

end Formalism.DivisionValues
