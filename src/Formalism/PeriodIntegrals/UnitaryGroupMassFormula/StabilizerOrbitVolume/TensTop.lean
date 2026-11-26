module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.PosNear
public import Formalism.PeriodIntegrals.VolFromSW
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import ReciprocityTheory.GeneralLinearIntegers.AlgebraMapIntMemOint

@[expose] public section

namespace PI.VolStabSW
export PI.VolStabS (
  secondCountable_tens borelSpace_tens borelSpace_herm continuous_norm_tens
  isUnit_iff_norm_tens isOpen_units_tens isOpen_isUnit_det hLin
  linIndep_of_isUnit_det continuous_hR continuous_gramR_apply continuous_gramR
  isClosed_HermR locallyCompact_herm sigma_invol sigR_invol gramR_mem
  secondCountable_completion secondCountable_Ainf isOpen_units_Ainf gramH
  continuous_gramH isOpen_unitHerm DensAll FibOfDens TensFacts fib_of_tens
  um_countable_HFinIn
)
end PI.VolStabSW

namespace PI.VolStabSW.PositiveNearLattice
export PI.VolStabS.PositiveNearLattice (
  crd crd_map crd_incl eq_sum_crd continuous_crd continuous_map_tens isClosed_int
  isClopen_latV isCompact_latV
)
end PI.VolStabSW.PositiveNearLattice

namespace PI.VolStabSW.DensGen
export PI.VolStabS.DensGen (ae_fib fib_set_nonneg fib_set eq_zero_of_setIntegral)
end PI.VolStabSW.DensGen
