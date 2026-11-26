module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensInfCo
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.FibFour
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TensTop

@[expose] public section

namespace PI.VolStabSW.TopoAF
export PI.VolStabS.TopoAF (
  countable_field countable_ringOfIntegers countable_ideal countable_spectrum
  separable_adicCompletion secondCountable_adicCompletion isOpen_integers
  secondCountable_finiteAdeleRing secondCountable_adeleRing secondCountable_tensAF
  secondCountable_HA_of secondCountable_HA
)
end PI.VolStabSW.TopoAF

namespace PI.VolStabSW
export PI.VolStabS (
  countable_numberField separableSpace_Fv secondCountable_Fv locallyCompact_Fv
  isOpen_units_Fv gramB hR_add_left hR_add_right hR_herm gramB_mem
  continuous_gramB_apply continuous_gramB DensOn IsCcOn densAll_iff DensApprox
)
end PI.VolStabSW
