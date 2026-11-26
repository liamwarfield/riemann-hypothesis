module

public import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.CuspPairIrr
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.ComapTwKer
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.DerFin
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftInvSubtypeSum
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeJacquetHolds

@[expose] public section

namespace PositivityTheory.RgGu.NR.JmTh
export CompanionTheory.RgGu.NR.JmTh (
  thetaL_surjective mem_unipRad_iff' thetaL_eq_one thetaW_mem_unipRad_iff
  twKer_theta leviProj_thetaW_leviEmb jacTheta jm_congr jacquet_module_theta_twist
)
end PositivityTheory.RgGu.NR.JmTh

namespace PositivityTheory.RgGu.NR
export CompanionTheory.RgGu.NR (
  jmTheta nuPair_of nuPair cuspPairIrr cuspPairIrr_of
)
end PositivityTheory.RgGu.NR

namespace PositivityTheory.RgGu.NR.NuP
export CompanionTheory.RgGu.NR.NuP (
  nontrivial_of_irr nontrivial_of_isIrreducible continuous_inv_addChar dualCl_fst
)
end PositivityTheory.RgGu.NR.NuP

namespace PositivityTheory.RgGu.NR.CuspPair
export CompanionTheory.RgGu.NR.CuspPair (key)
end PositivityTheory.RgGu.NR.CuspPair
