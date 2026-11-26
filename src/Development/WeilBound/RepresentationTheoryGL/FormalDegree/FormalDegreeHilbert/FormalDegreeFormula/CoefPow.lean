module

public import CompanionTheory.RealGroups.FormalDegrees.ArchimedeanFormalDegrees.FormalDegreeFormula.CoefPow
public import Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.FormalDegreeFormula.ModelFunctionsMultiply

@[expose] public section

namespace PositivityTheory.RgFd
export CompanionTheory.RgFd (
  twChi twChi_one twChi_mul twChi_ne norm_twChi kop_one kop_mul twTau twTau_apply
  twTau_cont twD twTau_irred twTau_hasDeriv twD_wt twD_hw twistKType cK_twistKType
  ckTwist mexp_add model_functions_multiply coefPow
)
end PositivityTheory.RgFd

namespace PositivityTheory.RgFd.CkM
export CompanionTheory.RgFd.CkM (
  blkMinor_diag_mul model_function_diag_mul vsp_diag ev ev_apply cpart1_Eaa
  cpart2_Eaa exp_Eaa ev_dTau_Eaa model_op model_dτ model_w uEv inner_uEv uEv_wt
  not_cone_neg_root uEv_hw evaluation_longest_weyl_one uEv_eq ckModel
)
end PositivityTheory.RgFd.CkM
