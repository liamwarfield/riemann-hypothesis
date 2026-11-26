module

public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.IdealLattice
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FoldUnfold
public import Mathlib
public import Formalism.PeriodIntegrals.QuotInv
public import Formalism.PeriodIntegrals.KFinSmooth
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SigmaStarUniq
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DiscrNe
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SigmaStarEx

@[expose] public section

namespace Formalism.MainNotions.Ext

theorem discrNe_holds : DiscrNe := discrNe'

theorem sigmaStarEx_holds : SigmaStarEx := sigma_star_exists

end Formalism.MainNotions.Ext
