module

public import Development.WeilBound.CoreStatements.FlagImmersions.ArithmeticIntersectionDivisorSupport

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ArithIntersectionDivisorSupport
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem kleiman_generic_fibre_integral : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.KleimanNefFStatement → (∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], ReciprocityTheory.ChartRestriction.G.AI.I1.ExistsUniqueStatement ℚ ι) → ReciprocityTheory.ChartRestriction.G.Geo.DivSuppArithStatement → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (W : Ideal (MRing ι)) (e : ℕ) (L : Fin e → HermLine ι), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar W (e + 1) → (∀ j, IsSmoothHerm (L j)) → (∀ j W', ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar W' 2 → W ≤ W' → 0 ≤ geomDeg W' (L j) 1) → 0 ≤ ptsIntegral W (fun j z => Real.log ((L j).h z)) (fun _ => 1) :=
  RootFieldNumerics.arithmetic_intersection_divisor_support

end GlobalTheory.CompanionTheory.Ar.Top
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ArithIntersectionDivisorSupportStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ptsIntegral_log_nonneg : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.KleimanNefFStatement → (∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], ReciprocityTheory.ChartRestriction.G.AI.I1.ExistsUniqueStatement ℚ ι) → ReciprocityTheory.ChartRestriction.G.Geo.DivSuppArithStatement → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (W : Ideal (MRing ι)) (e : ℕ) (L : Fin e → HermLine ι), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar W (e + 1) → (∀ j, IsSmoothHerm (L j)) → (∀ j W', ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar W' 2 → W ≤ W' → 0 ≤ geomDeg W' (L j) 1) → 0 ≤ ptsIntegral W (fun j z => Real.log ((L j).h z)) (fun _ => 1) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.kleiman_generic_fibre_integral | exact GlobalTheory.CompanionTheory.Ar.Top.kleiman_generic_fibre_integral | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.kleiman_generic_fibre_integral <;> assumption)
end
