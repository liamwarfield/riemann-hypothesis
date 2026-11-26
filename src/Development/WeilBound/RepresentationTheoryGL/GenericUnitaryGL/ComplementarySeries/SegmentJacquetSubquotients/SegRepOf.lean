module

public import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.SegmentSubquotients.SegRepOf
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.HasFiniteLengthJacSub
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftInvSubtypeSum
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WordOccursProductInterleave

@[expose] public section

namespace PositivityTheory.Pf1.SegRepC.Lift
export CompanionTheory.Pf1.SegRepC.Lift (
  isSmooth_multiProd_segTerm isSubquotient_jac_multiProd_of_sub
  perm_eq_one_of_lt_succ
)
end PositivityTheory.Pf1.SegRepC.Lift

namespace PositivityTheory.RgGu.SRC.SrRev
export CompanionTheory.RgGu.SRC.SrRev (transfer jmc)
end PositivityTheory.RgGu.SRC.SrRev

namespace PositivityTheory.RgGu.SRC
export CompanionTheory.RgGu.SRC (
  jhMult_rev_jac_sub jhMult_jac_multiProd exists_perm_of_isSubquotient_jac
  constituents_jac_sub exists_irred_le isIrreducible_segTensor
  hasFiniteLength_jac_sub StageP segTwo_of segRep_of
)
end PositivityTheory.RgGu.SRC

namespace PositivityTheory.Pf1.SegRepC.Twist
export CompanionTheory.Pf1.SegRepC.Twist (exists_ne_zero_irr exists_nabs_ne_one not_equiv_segTerm)
end PositivityTheory.Pf1.SegRepC.Twist

namespace PositivityTheory.RgGu.SRC.SrMult
export CompanionTheory.RgGu.SRC.SrMult (
  irrAdm isSmooth_segTerm' isIrreducible_segTerm' cl cl_injective cl_cusp
  jacEquivOf cl'
)
end PositivityTheory.RgGu.SRC.SrMult

namespace PositivityTheory.Pf1.SegRepC.MultOne
export CompanionTheory.Pf1.SegRepC.MultOne (
  isSmooth_segTerm isIrreducible_segTerm hasFiniteLength_segTerm
)
end PositivityTheory.Pf1.SegRepC.MultOne

namespace PositivityTheory.Pf1.SegRepC.Perm
export CompanionTheory.Pf1.SegRepC.Perm (entries_zero_or_d)
end PositivityTheory.Pf1.SegRepC.Perm

namespace PositivityTheory.RgGu.SRC.SrPerm
export CompanionTheory.RgGu.SRC.SrPerm (
  sq_right sq_left equiv_parInd_jac row_class col_class segIrr exists_perm_of_cell
)
end PositivityTheory.RgGu.SRC.SrPerm

namespace PositivityTheory.RgGu.SRC.SrEasy
export CompanionTheory.RgGu.SRC.SrEasy (isSmooth_prod hasFiniteLength_prod isSmooth_sub)
end PositivityTheory.RgGu.SRC.SrEasy

namespace PositivityTheory.Pf1.SegRepC.Uniq
export CompanionTheory.Pf1.SegRepC.Uniq (exists_unique_irred_sub)
end PositivityTheory.Pf1.SegRepC.Uniq

namespace PositivityTheory.Pf1.SegRepC.PiLocalization₂
export CompanionTheory.Pf1.SegRepC.PiLocalization₂ (isSubquotient_jac_of_le)
end PositivityTheory.Pf1.SegRepC.PiLocalization₂
