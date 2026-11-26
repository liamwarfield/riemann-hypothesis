module

public import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.CuspPairIrr
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.Complementary
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviIrreducibleTensorDecomposition
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleFiniteLength
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAutFunOfMemCusp
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.WhittakerCuspidal.WhitCuspOfSegCuspGeneric

@[expose] public section

namespace PositivityTheory.RgGu.NR.DerFin
export CompanionTheory.RgGu.NR.DerFin (
  dMap dMap_mk dMap_surjective twKer_le_map d_exact subsingleton_tw topBot
  topBot_surjective phi lift2 phi_lift2 phi_surjective phi_continuous base finLen
)
end PositivityTheory.RgGu.NR.DerFin

namespace PositivityTheory.RgGu.NR
export CompanionTheory.RgGu.NR (derFin_of)
end PositivityTheory.RgGu.NR
