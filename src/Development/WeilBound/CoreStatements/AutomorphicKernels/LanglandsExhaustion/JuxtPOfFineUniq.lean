module

public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.JuxtPOfFineUniq
public import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.CuspEmbP
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientProductIrreducible

@[expose] public section

namespace PositivityTheory.Exh
export CompanionTheory.Exh (
  nxt ShlP DecLP interleave_nil_left interleave_nil_right interleave_single
  shuffle_two_single decW_single words_of_subq decW_up nxt_not_mem
  eq_decW_of_append eq_of_isLSeg nu_nu_nat not_linked_single mem_tail_decW
  move_past emb_move_end FineUniqP exists_emb_of_cast decW_get_eq decLP juxtP
  juxtP_of_fineUniq
)
end PositivityTheory.Exh
