module

public import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.KleimanNef
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.KleimanGenericPointSectionInput
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GramDetNeZeroLocalBasisCofinite

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.KleimanNefCriteriaHold
open MvPolynomial ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem kleimanNef_field_and_fibre : KleimanNefIntersectionNonneg ∧ KleimanNefFStatement := by
  have hF : KleimanNefFStatement :=
    GroundTheory.Heights₂.Heights.ForSecondHalf.KleimanNefF.kleimanNef_field_of_alt (GlobalTheory.T.kleiman_input_nef_ample_section_count GlobalTheory.T.kleiman_genericPointSectionInput).1
  exact ⟨GroundTheory.Heights₂.Heights.ForSecondHalf.KleimanNef.proof hF, hF⟩

end GlobalTheory.CompanionTheory.Ar.Giv
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.KleimanNefCriteriaHoldStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kleiman_nef_criteria_hold : KleimanNefIntersectionNonneg ∧ KleimanNefFStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.kleimanNef_field_and_fibre | exact GlobalTheory.CompanionTheory.Ar.Giv.kleimanNef_field_and_fibre | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.kleimanNef_field_and_fibre <;> assumption)
end
