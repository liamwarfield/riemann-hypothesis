module

public import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.CuspPairIrr
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.Complementary
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedJacquetPhiMinusEquiv

@[expose] public section

namespace PositivityTheory.RgGu.NR.DerEq
export CompanionTheory.RgGu.NR.DerEq (
  comap_twKer Q Q_surj ker_Q E Q_equiv E_val_zero E_val_succ E_val emb_val
  stdSum_inj one_std E_eq InU inU_of_mem mem_of_inU Q' Q'_surj Q'_equiv
  derChar_val ker_Q'
)
end PositivityTheory.RgGu.NR.DerEq

namespace PositivityTheory.RgGu.NR
export CompanionTheory.RgGu.NR (derEquiv)
end PositivityTheory.RgGu.NR
