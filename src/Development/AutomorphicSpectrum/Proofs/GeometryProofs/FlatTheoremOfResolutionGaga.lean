module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TowerWeightOfZero
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatFirstFromResolutionAndGaga
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatTheoremOfParts
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginGenericFrameBound
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginFrameDegreeBound

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatTheoremOfResolutionGaga
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteConstantHolds
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteConstantHolds
namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem finConst_of_all_hosts : FinConst :=
  FinConstAll.finConst GlobalTheory.T.finite_constant_all_holds

end GlobalTheory.CompanionTheory.Ar.Flat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteConstantHoldsStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_constant_holds : GlobalTheory.CompanionTheory.Ar.Flat.FinConst := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.finConst_of_all_hosts | exact GlobalTheory.CompanionTheory.Ar.Flat.finConst_of_all_hosts | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.finConst_of_all_hosts <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatTheoremOfResolutionGaga
open CategoryTheory AlgebraicGeometry NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT GlobalTheory.CompanionTheory.Ar.Flat ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem thmFlatA_of_resK_gaga_partI :
    Geo.ResK.ResKStatement → GagaSections → PartI → ThmFlatA :=
  fun hR hG hP =>
    GlobalTheory.T.flat_theorem_of_parts hP (GlobalTheory.T.flat_zero_from_resolution_and_gaga hR hG) (GlobalTheory.T.flat_first_from_resolution_and_gaga hR hG) GlobalTheory.T.finite_constant_holds

end GlobalTheory.CompanionTheory.Ar.Flat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatTheoremOfResolutionGagaStatement
open CategoryTheory AlgebraicGeometry NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT GlobalTheory.CompanionTheory.Ar.Flat ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_theorem_of_resolution_gaga : Geo.ResK.ResKStatement → GagaSections → PartI → ThmFlatA := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.thmFlatA_of_resK_gaga_partI | exact GlobalTheory.CompanionTheory.Ar.Flat.thmFlatA_of_resK_gaga_partI | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.thmFlatA_of_resK_gaga_partI <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformLawsRootModelBound
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Rec

theorem latExp_eq (E : Type) [Field E] [NumberField E] (SS : Finset ℕ) (p : ℕ) :
    Small.latExp E SS p = if p ∈ SS then 1 / ((p : ℝ) - 1) + (if p = 2 then 1 else 0) +
      (padicValInt p (discr E) : ℝ) / Module.finrank ℚ E else 0 := by
  unfold Small.latExp Small.htExp
  by_cases h : p ∈ SS
  · by_cases h2 : p = 2
    · subst h2
      norm_num
    · simp [h, h2]
  · simp [h]

end GlobalTheory.CompanionTheory.Ar.Rec
end
end
