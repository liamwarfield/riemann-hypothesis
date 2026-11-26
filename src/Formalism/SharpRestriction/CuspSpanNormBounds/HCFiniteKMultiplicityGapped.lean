module

public import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLitG
public import CompanionTheory.AutomorphicTheory.BesselWaveGrids.TiedNum

@[expose] public section

section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.HCFiniteKMultiplicityGapped
noncomputable section

namespace Formalism.MainNotions.BridgeDS3

open Formalism.MainNotions Formalism.MainNotions.S

theorem discrete_series_exists_gapped [Fact Formalism.MainNotions.DiscreteSeriesWeylDimension.DiscreteSeriesExistsG] : DiscreteSeriesWeylDimension.DiscreteSeriesExistsG := Fact.out


end Formalism.MainNotions.BridgeDS3

end
end

section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.NearParameterGap
noncomputable section

namespace Formalism.MainNotions.NearParameterGap

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.OnePlaceEstimates

theorem consts (k r : ℕ) (hk : 1 ≤ k) :
    Formalism.FourierDecayAlt.ThreeDimData.Mexp r ≤ (2 * (r : ℝ) + 2) ^ 2 / 2 ∧ 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.Mexp r ∧
    Formalism.FourierDecayAlt.ThreeDimData.AS k r ≤ 2 * (2 * (r : ℝ) + k + 1) ^ 3 ∧ 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.AS k r ∧
    Formalism.FourierDecayAlt.ThreeDimData.AG k r ≤ 4 * (2 * (r : ℝ) + k + 1) ^ 3 ∧ 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.AG k r := _root_.CompanionTheory.WaveGrid.GapSizes.consts k r hk

end Formalism.MainNotions.NearParameterGap
end
end
