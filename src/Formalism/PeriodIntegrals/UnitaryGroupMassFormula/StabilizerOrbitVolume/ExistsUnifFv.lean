module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.ExistsUnifFv
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.MeasureEqOfCos
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensVNA

@[expose] public section

namespace PI.VolStabSW
export PI.VolStabS (
  smulSub mem_smulSub coe_smulSub isOpen_smulSub isCompact_smulSub
  eventually_smul_sub reach_of_approx filt_abstract sigR_algebraMap hR_smul_left
  hR_smul_right hermSMul coe_hermSMul hermModule exists_unif_Fv
)
end PI.VolStabSW
