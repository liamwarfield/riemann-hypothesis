module

public import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.JacquetModuleThetaTwist
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.Complementary
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleFiniteLength

@[expose] public section

namespace PositivityTheory.RgGu.NR.SomeRed
export CompanionTheory.RgGu.NR.SomeRed (
  intw intw' intw_symm smooth_of_equiv admissible_of_equiv sesq_of_equiv
  unit_of_equiv irr_of_equiv unit_twist
)
end PositivityTheory.RgGu.NR.SomeRed

namespace PositivityTheory.RgGu.NR
export CompanionTheory.RgGu.NR (chi_apply norm_chi someRed_of)
end PositivityTheory.RgGu.NR
