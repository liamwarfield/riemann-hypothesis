module

public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.SquareIntegrableSegments.SegmentReordering.CsOrderfree
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleFiniteLength
public import Lean.LibrarySuggestions.Basic
public import Lean.Elab.Command

@[expose] public section

namespace PositivityTheory.PfEss.Zc2
export CompanionTheory.PfEss.Zc2 (
  ntrans prodIrr_equiv_of_eq cut_e cutC_lt cutA cutC sum_append sum_split2 stage2
  head_swap split_alt_alt split_swap swap_adj Reach reach_step strictMono_of_adj
  swap_lt_swap invSet symm_mul_swap_apply reach_of_inv cs_reorderord
)
end PositivityTheory.PfEss.Zc2
