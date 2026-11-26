module

public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.GrothOfCls
public import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.ClassGlEqClass
public import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.ClassProductIrreducibleLeft
public import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.MulClassBasisRight
public import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.ClassProductIrreducibleFold
public import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.ClassProductIrreducibleCast
public import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.TriCoeFlattenDecW

@[expose] public section

namespace PositivityTheory.Groth.JClsPf
export CompanionTheory.Groth.JClsPf (piTensor_irr jm_ne_top jm_congr jm_eq_sum)
end PositivityTheory.Groth.JClsPf

namespace PositivityTheory.Groth
export CompanionTheory.Groth (
  jacquet_functional_class jCls triAut uniTri altSum groth_of_cls
)
end PositivityTheory.Groth

namespace PositivityTheory.Groth.ChartWirtingerDerivatives
export CompanionTheory.Groth.ChartWirtingerDerivatives (
  toZAlg tri_supported_le tri_surj tri_bij uni_inj uni_exists uni_bij
)
end PositivityTheory.Groth.ChartWirtingerDerivatives

namespace PositivityTheory.Groth.AltC
export CompanionTheory.Groth.AltC (
  filter_mem_eq_of_sublist mem_sub mem_sub_self sub_sublist shuffleCount_eq
  cond_map wN mem_wN nodup_wN sublist_of_lt run_sublist Cond cond_iff altSumN
)
end PositivityTheory.Groth.AltC

namespace PositivityTheory.Groth.AltS
export CompanionTheory.Groth.AltS (
  tN tN_injective tN_zero vWord_eq decWord_eq first_mem_decWord
)
end PositivityTheory.Groth.AltS
