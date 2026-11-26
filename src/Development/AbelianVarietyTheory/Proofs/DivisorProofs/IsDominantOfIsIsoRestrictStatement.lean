module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleRigidFiniteOrder
public import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDominant_of_isIso_restrict' : ∀ (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (s : Y ⟶ X) (U : X.Opens), (U : Set X).Nonempty → IsIso (s ∣_ U) → IsDominant s := by
  first | exact @GlobalTheory.Discrepancy.isDominant_of_isIso_restrict | exact GlobalTheory.Discrepancy.isDominant_of_isIso_restrict | (intros; apply GlobalTheory.Discrepancy.isDominant_of_isIso_restrict <;> assumption)
