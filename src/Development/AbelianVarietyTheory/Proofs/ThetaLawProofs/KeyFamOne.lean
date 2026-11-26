module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExactKeyFormulaProof

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyFamOfKeyFormula
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KeyCl

namespace GlobalTheory.KeyFamOfExact

theorem keyFam_of_keyFormula : KeyFormula → KeyFam fun _ => 1 := fun h => by
  obtain ⟨κ, h1, h2, h3, h4, h5⟩ := keyFormula_iff.1 h
  exact ⟨κ, h1, h2, h3, h4, h5, GlobalTheory.KeyFamUnit.famUnit κ h2 h3,
    GlobalTheory.KeyFamHomog.famHomog_of_homog _ κ h1, GlobalTheory.T.thetaKeyRule_valuationUnit_of_functorial κ h2 h3⟩

end GlobalTheory.KeyFamOfExact
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KeyCl

namespace GlobalTheory.KeyFamClosing

theorem keyFam_one : KeyFam fun _ => 1 :=
  GlobalTheory.KeyFamOfExact.keyFam_of_keyFormula GlobalTheory.T.exactKeyFormula_proof

end GlobalTheory.KeyFamClosing
