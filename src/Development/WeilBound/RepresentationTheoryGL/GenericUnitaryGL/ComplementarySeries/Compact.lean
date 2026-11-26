module

public import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.Compact
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.Complementary

@[expose] public section

namespace PositivityTheory.RgGu.NR.Compact
export CompanionTheory.RgGu.NR.Compact (
  isOpen_fix rc rc_pos rc_mul chi_val rc_of_KO exists_pw hh hh_spec hh_pos
  hh_mul_left hh_mul_right mulFun mulFun_mem mulFun_smooth mulMap rel_symm
  mulEquiv relChi E F F_apply cc cc_left K1 isOpen_compact_open_subgroup cc_right
  cc_finite ind_val_sum piece expo
)
end PositivityTheory.RgGu.NR.Compact

namespace PositivityTheory.RgGu.NR
export CompanionTheory.RgGu.NR (compact)
end PositivityTheory.RgGu.NR
