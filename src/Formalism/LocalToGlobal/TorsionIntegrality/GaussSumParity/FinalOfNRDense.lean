module

public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.HomotheticLatticeIntegralOf
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.SqrtInUnramifiedCompletion

@[expose] public section

namespace Formalism.L2.Th1.D

theorem sqrtKur : SqrtKur := sqrt_in_unramified_completion
theorem denseOK : DenseOK := dense_criterion
theorem homothetic_lattice_integral_s2 : HomotheticLatticeIntegralS2 := homothetic_lattice_integral_of

end Formalism.L2.Th1.D
