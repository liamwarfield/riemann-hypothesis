module

public import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.Complementary
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.SegmentDerivatives.DerivJac
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.RightWhit

@[expose] public section

namespace PositivityTheory.RgGu.NR
export CompanionTheory.RgGu.NR (
  DerEquiv DerFin HasSesq ConjEquiv IsFamily Signature Complementary chi sum_two
  blk2 Compact Bound ConjProd ConjDual Herm ProdModel CuspUnit SomeRed RedCl
)
end PositivityTheory.RgGu.NR

namespace PositivityTheory.RgGu.NR.IsFamily
export CompanionTheory.RgGu.NR.IsFamily (mk const expo)
end PositivityTheory.RgGu.NR.IsFamily
