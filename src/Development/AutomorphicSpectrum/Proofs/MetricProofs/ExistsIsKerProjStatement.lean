module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsEigenComponentPolynomial
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodLimit
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsIsChart
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.CxSimple
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannLatticeEigenProjection

@[expose] public section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isKerProj' : ∀ (g : ℕ) (S : Matrix (Fin g) (Fin g) ℤ), ∃ Pr : Matrix (Fin g) (Fin g) ℝ, IsKerProj S Pr := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.exists_isKerProj | exact GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.exists_isKerProj | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.exists_isKerProj <;> assumption)
