module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightsTopGrid
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow

@[expose] public section

namespace GlobalTheory.WtInterlaceC
export GlobalTheory.WtInterlace (
  cnt IsUp Good good_pair good_single good_congr block_succ_top block_succ_bot
  block_le block_ge good_blocks good_empty good_family cnt_decide isUp_le isUp_lt
  strictInterlace_of_good good_CB good_MB good_U
  one_pow_not_mem_height_one_asIdeal lb_U ub_U chiGrid_row_entries_lower_bound
  chiGrid_row_entries_upper_bound good_top_grid interlace_wtOf descEnum_last
  sameShift_wtOf low_mem_weightX min_weightX half_mem_parD min_parD
  weights_top_grid
)
end GlobalTheory.WtInterlaceC

namespace GlobalTheory.WtInterlaceC.Good
export GlobalTheory.WtInterlace.Good (union)
end GlobalTheory.WtInterlaceC.Good
