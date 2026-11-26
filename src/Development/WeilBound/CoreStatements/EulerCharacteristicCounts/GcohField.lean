module

public import CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.GcohCmp
public import CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.GcohField
public import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.GcohDefs
public import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.MainCount

@[expose] public section

namespace PositivityTheory.LocalTateOrthogonality.Gcoh
export CompanionTheory.LocalTateOrthogonality.Gcoh (
  coc_inj exists_coc pi_succ_eq_zero_iff pi_zero_eq_zero_iff core_hom core_quot
  neg_one_pow_smul' dn_app d_comp dn_zero dn_one dn_two integer_padic_eq
  card_quotient_padic isSepClosure_padic gcField bij_transport nsmul_zmod bij_flip
  exists_dualEquiv
)
end PositivityTheory.LocalTateOrthogonality.Gcoh
