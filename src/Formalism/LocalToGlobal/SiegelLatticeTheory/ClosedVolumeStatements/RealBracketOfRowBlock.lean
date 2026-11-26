module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.RealBracketHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RootPatterns
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXKL
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NOfibFibC
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.CovolBRc

@[expose] public section

namespace Formalism.L2.SG.Closed





open Formalism.L2.SG.Pf.NcReal.JX in
theorem CovolRef_outright : CovolRef :=
  covolRef_of_steps (coordCovol_of kapLaw_holds NOf.nofib_holds Formalism.L2.SG.Pf.NcReal.JX.CovB.blockCovol_holds)
    (refNBox_of Formalism.L2.SG.Pf.NcReal.JX.FR.frameRow_holds)


end Formalism.L2.SG.Closed
