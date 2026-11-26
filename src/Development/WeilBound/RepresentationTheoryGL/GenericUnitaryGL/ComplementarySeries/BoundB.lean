module

public import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.BoundB
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.Complementary
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIrreducibleSecondFactorOfIrreducibleProduct
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicGLIwasawaDecompositionStandardParabolic

@[expose] public section

namespace PositivityTheory.RgGu.NR.BoundB
export CompanionTheory.RgGu.NR.BoundB (
  val_le_one zd Zt Zt_val Zt_inv_val Zt_mem leviProj_Zt conj_mem conj_mem' avL
  avL_apply avL_fixed hfixH ineq fixval law act zval modulus_scalar_block
  bound_main
)
end PositivityTheory.RgGu.NR.BoundB

namespace PositivityTheory.RgGu.NR
export CompanionTheory.RgGu.NR (boundB)
end PositivityTheory.RgGu.NR
