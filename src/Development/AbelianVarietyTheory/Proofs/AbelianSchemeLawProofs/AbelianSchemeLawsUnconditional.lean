module

public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsOfH0EqOneClosedFields
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FinrankSectionsPrincipalPolarisationEqOne
public import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
section -- merged from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.abelianSchemeLaws_all : _root_.ReciprocityTheory.ChartRestriction.G.Out.Laws ∧ _root_.ReciprocityTheory.ChartRestriction.G.Out.Laws2 :=
  _root_.GlobalTheory.AbLaw.AllLaws.laws_of_h0_eq_one _root_.GlobalTheory.AbLaw.finrank_sections_principal_polarisation_eq_one

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditionalStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_laws_unconditional : Laws ∧ Laws2 := by
  first | exact @GlobalTheory.abelianSchemeLaws_all | exact GlobalTheory.abelianSchemeLaws_all | (intros; apply GlobalTheory.abelianSchemeLaws_all <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PrincipalPolarisationUniqueSection
namespace GlobalTheory.AbLaw

theorem principalPolarisation_unique_section : GlobalTheory.Published.principalPolarisationOneSection :=
  finrank_sections_principal_polarisation_eq_one

end GlobalTheory.AbLaw
end
