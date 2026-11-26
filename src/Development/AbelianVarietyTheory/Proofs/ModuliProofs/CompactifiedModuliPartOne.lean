module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PartOneOfSemistableReductionPadicPolarized

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CompactifiedModuliPartOne
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CompactifiedModuliPartOne
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem _root_.GlobalTheory.partI_closed : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.PartI :=
  _root_.GlobalTheory.partI_of_semistableReduction _root_.GlobalTheory.SS.semistableReductionSt

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CompactifiedModuliPartOneStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactifiedModuli_partOne : PartI := by
  first | exact @GlobalTheory.partI_closed | exact GlobalTheory.partI_closed | (intros; apply GlobalTheory.partI_closed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CompactifiedModuliExistenceAndModuliScheme
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.Moduli

theorem _root_.GlobalTheory.Moduli.jointExistence_and_moduliScheme : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.PartI ∧ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.N1ab :=
  ⟨_root_.GlobalTheory.partI_of_semistableReduction _root_.GlobalTheory.SS.semistableReductionSt,
    _root_.GlobalTheory.Moduli.moduli_scheme_exists⟩

end GlobalTheory.Moduli
end
