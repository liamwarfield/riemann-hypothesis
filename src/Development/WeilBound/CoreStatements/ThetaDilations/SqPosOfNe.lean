module

public import CompanionTheory.AutomorphicTheory.ThetaDilations.SqPosOfNe
public import Development.WeilBound.CoreStatements.ThetaDilations.IsOpenCoset

@[expose] public section

namespace PositivityTheory.PlacePermOperatorBicommutantSpan

export CompanionTheory.PlacePermOperatorBicommutantSpan (
  CO ind ind_of_mem ind_of_not ind_congr ind_add
  isOpen_coset lc_of_inv sb_ind sb_add sb_mul sb_smul
  sb_zero sb_sum sb_homeo sb_span co_cpt sb_level
  chi_sym chi_norm chi_add chi_cont chi_ne chi_add'
  chi_zero chi_neg perpG co_perp perp_perp meas_perp
  chi_lc sb_int sb_chi fou_add fou_smul map_sum_sb
  fou_ind fou_sb planch schur bsym sb_heis sb_opU
  sb_opD impl_mul impl_U impl_D impl_fou_chiB
  sq_pos_of_ne impl_uniq weil_id orbit_bd
)

namespace CO
export CompanionTheory.PlacePermOperatorBicommutantSpan.CO (sup inf)
end CO

end PositivityTheory.PlacePermOperatorBicommutantSpan
