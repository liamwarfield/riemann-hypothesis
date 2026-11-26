module

public import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.SegmentSubquotients.SegmentRepresentation
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.SegRepOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeCuspidalPairLength
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.CuspPairIrr
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.ComplementaryOf
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.Compact
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.BoundB
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.ConjDual
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.ThetaContra
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SomeRed
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GeometricSplitting.Imports

@[expose] public section

namespace PositivityTheory.RgGu.NR.Sig
export CompanionTheory.RgGu.NR.Sig (
  qf cont_qf qf_smul qf_single Sq ef gram mk mk_apply expand mk_gram gram_mk
  gram_smul Inv Herm Pos ker_bot inv_sub uniq real_of pos_of pos_mk_iff pos_open
  mk_smul herm_smul inv_smul normalize lim_form
)
end PositivityTheory.RgGu.NR.Sig

namespace PositivityTheory.RgGu.NR
export CompanionTheory.RgGu.NR (
  signature redCl_ofC rhoNuRho_ofC redClC rhoNuRhoReducibleC
)
end PositivityTheory.RgGu.NR

namespace PositivityTheory.RgGu.SRC.StageC
export CompanionTheory.RgGu.SRC.StageC (
  cls segTerm_smooth segTerm_irr tcl tcl_eq blocks_eq consec_equiv
  prod₂_map_injective_right inj_comp inj_equiv sum_const_fin Emb sum_app embR embL
  emb_right emb_left comb classMain exists_alt_ter exists_unit_one_add_generator
  one_le_jm
)
end PositivityTheory.RgGu.SRC.StageC

namespace PositivityTheory.RgGu.SRC.StageC.Emb
export CompanionTheory.RgGu.SRC.StageC.Emb (
  trans of of' sub range
)
end PositivityTheory.RgGu.SRC.StageC.Emb

namespace PositivityTheory.RgGu.SRC
export CompanionTheory.RgGu.SRC (stageP)
end PositivityTheory.RgGu.SRC

namespace PositivityTheory.RgGu.NR.RedC
export CompanionTheory.RgGu.NR.RedC (irr_congr irr_tw)
end PositivityTheory.RgGu.NR.RedC

namespace PositivityTheory.RgGu
export CompanionTheory.RgGu (segmentRepresentation)
end PositivityTheory.RgGu
