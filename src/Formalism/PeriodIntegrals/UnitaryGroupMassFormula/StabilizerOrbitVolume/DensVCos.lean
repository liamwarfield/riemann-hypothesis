module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensVCos
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF

@[expose] public section

namespace PI.VolStabSW
export PI.VolStabS (
  IsLCcOn HasCOSub HasDens nonneg_of_setIntegral isOpen_inf_iInf exists_sub_osc
  cosApx cosApx_sub_mem cosApx_eq cosApx_lc densApprox_lc hasDens_zero hasDens_sum
  DensCosB IsCOBasis isCompact_cos integrable_cos densLC_of_cosB
)
end PI.VolStabSW

namespace PI.VolStabSW.HasDens
export PI.VolStabS.HasDens (sub const_mul le add)
end PI.VolStabSW.HasDens
