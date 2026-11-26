module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitCenterMemIff
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.CurveComplexPoint
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsKleimanScheme

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResVolume
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory

noncomputable section

def ResVolume.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (e : ℕ)
    (R : AnRes P J e) [MeasurableSpace R.X] [BorelSpace R.X],
    IsArithVar P (e + 1) → ∃ dV : Measure R.X, IsSmoothVolume R.A dV

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPullFSExtension
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory

noncomputable section

def PullFSExtension.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω) (e : Fin (D + 1) → Ix κ),
    IsProjFrame x e →
    ∃ m₀ : ConeMetric ℂ (Ix κ), IsSmoothMetric m₀ ∧ IsConjInvariant m₀ ∧
      IsSemipositiveRel ⊥ (coordIdeal ℤ x) (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofCone m₀) ∧ IsPullFS x e m₀

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSupBoundBlock
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def SupBoundBlock.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (d : HSMBlockDatum D K ι Ω),
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ f : MRing ι, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f (blockDeg d.k₀ n) →
      ∀ z ∈ mcPts (mCoordIdeal d.y),
        ‖eval z (map (Int.castRingHom ℂ) f)‖ / d.A.h z ^ n ≤ C * (n : ℝ) ^ ((D : ℝ) / 2) * blockL2Norm d n f

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSupBoundCount
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory

noncomputable section

def SupBoundCount.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (d : HSMBlockDatum D K ι Ω) (n : ℕ) (c : ℝ), 0 < c →
    (∀ f : MRing ι, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f (blockDeg d.k₀ n) → ∀ z ∈ mcPts (mCoordIdeal d.y),
      ‖eval z (map (Int.castRingHom ℂ) f)‖ / d.A.h z ^ n ≤ c * blockL2Norm d n f) →
    (Module.finrank ℤ (secM d.y (blockDeg d.k₀ n)) : ℝ) ≤ 2 * c ^ 2 ∧
      blockChi d n - (Module.finrank ℤ (secM d.y (blockDeg d.k₀ n)) : ℝ) *
          Real.log (c * Real.sqrt (Module.finrank ℤ (secM d.y (blockDeg d.k₀ n)))) ≤
        smallSectionCount (IsSmallH (mCoordIdeal d.y) d.y d.A) (fun τ => secM d.y (blockDeg d.k₀ τ)) n

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsConstantShift
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory

noncomputable section

section Def

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def HermLine.constShift (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (η : ℝ) : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι :=
  A.tensor (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofWeight (fun _ => η) (fun _ _ _ => rfl))

end Def

def ConstantShift.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) → ℝ) (P : Ideal (MRing ι)) (D : ℕ)
    (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (η : ℝ),
    IsIntersectionFamily I → IsArithVar P (D + 1) → IsSmoothHerm A →
    I P (D + 1) (fun _ => HilbertSamuel.HermLine.constShift A η) =
      I P (D + 1) (fun _ => A) - ((D : ℝ) + 1) * η * geomDeg P A D

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFSGeomDegPos
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo

def FSGeomDegPos.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ),
    IsArithVar P (e + 1) → 0 < ptsIntegral P (pot fun _ : Fin e => fsH ι) (fun _ => 1)

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsCurvePointsFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo

def CurvePointsFinite.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (W : Ideal (MRing ι)),
    IsArithVar W 1 → Finite (GroundTheory.Heights₂.Heights.projPts W)

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsIntegralAgainstPositive
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo

def IntegralAgainstPositive.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P P0 : Ideal (MRing ι)) (e : ℕ)
    (L : Fin e → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (g : ((Σ k, ι k) → ℂ) → ℝ),
    P0 ≤ P → (∀ j, IsSemipositiveRel P0 P (L j)) → (∀ z ∈ mcPts P, g z ≤ 0) →
    ptsIntegral P (pot L) g ≤ 0

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArithKleiman
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo

def ArithKleiman.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P P0 : Ideal (MRing ι)) (D : ℕ)
    (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (II : IntersectionSystem),
    IsIntersectionSystem II → IsArithVar P (D + 1) → P0 ≤ P → IsSemipositiveRel P0 P A →
    NefOnFibres P A.a → IsConjInvariantH A →
    (∀ W, IsArithVar W 1 → P ≤ W → 0 ≤ II K ι W 1 ![A]) →
    0 ≤ II K ι P (D + 1) (fun _ => A)

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsMixedKleiman
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo

def MixedKleiman.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P P0 : Ideal (MRing ι)) (d : ℕ)
    (M A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (a : K → ℕ) (II : IntersectionSystem),
    IsIntersectionSystem II → 1 ≤ d → IsArithVar P d → P0 ≤ P →
    IsSemipositiveRel P0 P M → NefOnFibres P M.a → IsConjInvariantH M →
    (∀ W, IsArithVar W 1 → P ≤ W → 0 ≤ II K ι W 1 ![M]) →
    (A.a = fun k => (a k : ℤ)) → IsSemipositiveRel P0 P A → MonomialsBounded P A a → IsConjInvariantH A →
    ∀ j ≤ d, 0 ≤ II K ι P d (fun i : Fin d => if (i : ℕ) < j then M else A)

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGenDegAmple
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def GenDegAmple.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (d : K → ℤ),
    IsArithVar (mCoordIdeal y) (D + 1) → (∀ k, 1 ≤ d k) → 0 < genDeg (mCoordIdeal y) D d

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNmSectionsFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

def NmSectionsFinite.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (a : K → ℕ),
    (∀ k, 1 ≤ a k) → (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → Birational y → ∀ τ₂ : ℕ,
    ∃ (J : Type) (_ : Fintype J) (d : J → ℕ) (e : J → Ω) (τ₁ : ℕ),
      (∀ j, τ₂ ≤ d j ∧ d j ≤ τ₁ ∧ e j ∈ chartLatNm y (fun k => (a k : ℤ)) (d j)) ∧
      ∀ τ : ℕ, τ₁ ≤ τ → ∀ s ∈ chartLatNm y (fun k => (a k : ℤ)) τ,
        ∃ r : J → Ω, (∀ j, r j ∈ secM y (fun k => (τ - d j) * a k)) ∧ s = ∑ j, r j * e j

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionsRank
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def SectionsRank.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω) (n : ℕ),
    GroundTheory.Heights₂.Heights.NumbersDVR.hilbFn (ι := GlobalTheory κ)
        ((coordIdeal ℤ x).map (MvPolynomial.map (Int.castRingHom ℚ))) (fun _ => (n : ℤ)) =
      (Module.finrank ℤ (sec ℤ x n) : ℤ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsShiftDegreePolynomial
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory

noncomputable section

def ShiftDegreePolynomial.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (D : ℕ) (a b : K → ℤ),
    IsArithVar P (D + 1) →
    ∃ r : Polynomial ℝ, r.natDegree ≤ D ∧ r.coeff D = (genDeg P D a : ℝ) ∧
      ∀ q : ℕ, (genDeg P D ((q : ℤ) • a + b) : ℝ) = r.eval (q : ℝ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGenericFibre
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def GenericFibre.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω) (D : ℕ),
    IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1) →
    GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiProjPrime (ι := GlobalTheory κ)
        ((coordIdeal ℤ x).map (MvPolynomial.map (Int.castRingHom ℚ))) ∧
      ringKrullDim (MvPolynomial (Ix κ) ℚ ⧸
          (coordIdeal ℤ x).map (MvPolynomial.map (Int.castRingHom ℚ))) = ((D + 1 : ℕ) : WithBot ℕ∞)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsZCombExpand
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo

def ZCombExpand.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) → ℝ), IsIntersectionFamily I →
    ∀ (P : Ideal (MRing ι)) (d : ℕ) (M H : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (q p : ℕ),
      IsArithVar P d → IsSmoothHerm M → IsSmoothHerm H →
      I P d (fun _ => HermLine.zcomb M H (q : ℤ) (p : ℤ)) =
          ∑ i ∈ Finset.range (d + 1), (d.choose i : ℝ) * (q : ℝ) ^ (d - i) * (p : ℝ) ^ i *
            I P d (fun j : Fin d => if (j : ℕ) < d - i then M else H) ∧
        (1 ≤ d → I P d (fun j : Fin d => if (j : ℕ) = 0 then M else HermLine.zcomb M H (q : ℤ) (p : ℤ)) =
          ∑ i ∈ Finset.range d, ((d - 1).choose i : ℝ) * (q : ℝ) ^ (d - 1 - i) * (p : ℝ) ^ i *
            I P d (fun j : Fin d => if (j : ℕ) < d - i then M else H))

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBergmanDensChartSum
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M

noncomputable section

def BergmanDensChartSum.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] (A : FinHolAtlas D X) (L : HolLineBundle A) (W : Weight L) (dV : SmoothVolume A)
    (P : ChartPartition A) (g : X → ℝ), Continuous g →
      ∫ x, g x * bergmanDens W dV x ∂dV.μ =
        (∑ j, ∫ y in (A.chart j).target,
          P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * chernTopDens W j y) / (D.factorial : ℝ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsConstantsRegular
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry NumberField

def ConstantsRegular.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (F : Type) [Field F] [NumberField F] [Algebra F Ω] (y : (Σ k, ι k) → Ω),
    (∀ z ∈ mcPts (mCoordIdeal y), ∃! sg : F →+* ℂ, LiesOver y sg z) →
    ∃ N : ℕ, 1 ≤ N ∧ ∀ (θ : 𝓞 F) (c : ∀ k, ι k), (∀ k, y ⟨k, c k⟩ ≠ 0) →
      (N : Ω) * algebraMap F Ω (θ : F) ∈ chartRingZ y c

section Inhabitants

open ProjLine

end Inhabitants

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionSupBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def SectionSupBound.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (τ : ℕ) (e : Ω),
    ContinuousOn A.h {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} → e ∈ chartLat y A.a τ →
    ∃ C : ℝ, 0 ≤ C ∧ IsBoundedH (mCoordIdeal y) y A τ (Real.exp C) e

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNefAmpleFibre
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def NefAmpleFibre.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (α : K → ℤ) (b a ℓ : ℕ),
    IsArithVar (mCoordIdeal y) (D + 1) → NefOnFibres (mCoordIdeal y) α → 1 ≤ b → 1 ≤ a → ℓ.Prime →
    KH.AmpleV (ZMod ℓ) (fibreIdeal ℓ y) ((b : ℤ) • α + fun _ => (a : ℤ))

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNefAmpleGeneric
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def NefAmpleGeneric.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (M : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (P0 : Ideal (MRing ι))
    (b a : ℕ),
    IsArithVar (mCoordIdeal y) (D + 1) → P0 ≤ mCoordIdeal y → IsSemipositiveRel P0 (mCoordIdeal y) M →
    1 ≤ b → 1 ≤ a → KH.AmpleV ℚ (KH.genIdeal y) ((b : ℤ) • M.a + fun _ => (a : ℤ))

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsLocalRep
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory

noncomputable section

def LocalRep.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (a : K → ℤ) (n : ℕ) (s : Ω) (z : (Σ k, ι k) → ℂ),
    s ∈ chartLat y a n → z ∈ mcPts (mCoordIdeal y) →
    ∃ (dg dh : K → ℕ) (g h : MRing ι), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g dg ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog h dh ∧
      (∀ k, (dg k : ℤ) = dh k + n * a k) ∧ aeval y g = s * aeval y h ∧
      eval z (map (Int.castRingHom ℂ) h) ≠ 0

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsHSMTransport
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def matSubst {J : Type} [Fintype J] (B : Matrix J J ℚ) (b : MvPolynomial J ℚ) : MvPolynomial J ℚ :=
  aeval (fun i => ∑ j, C (B i j) * X j) b

theorem matAct_one {Ω : Type} [Field Ω] [CharZero Ω] {J : Type} [Fintype J] [DecidableEq J] (x : J → Ω) :
    matAct (1 : Matrix J J ℚ) x = x := by
  funext i
  simp only [matAct, Matrix.one_apply]
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [Ne.symm hj]) (by simp)]
  simp

def HSMTransport.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (d : HSMDatum D Ω κ)
    (B : Matrix (Ix κ) (Ix κ) ℚ), IsInvMat B →
    ∃ d' : HSMDatum D Ω κ, d'.x = matAct B d.x ∧ (∀ z, d'.m.ρ (matActC B z) = d.m.ρ z) ∧
      ∀ (n r : ℕ) (b : Fin r → MvPolynomial (Ix κ) ℚ),
        resGram d' n b = resGram d n fun k => matSubst B (b k)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockDefectMetricChange
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

variable {D : ℕ} {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {Ω : Type} [Field Ω] [CharZero Ω]

def HSMBlockDatum.withMetric (d : HSMBlockDatum D K ι Ω) (A' : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (P0' : Ideal (MRing ι))
    (hdeg : A'.a = unitDeg d.k₀) (hc : IsConjInvariantH A') (hle : P0' ≤ mCoordIdeal d.y)
    (hp : IsSemipositiveRel P0' (mCoordIdeal d.y) A') : HSMBlockDatum D K ι Ω :=
  { d with A := A', P0 := P0', deg := hdeg, conjInv := hc, normalForm_baseLattice_le_dualSpan_sup_line := hle, semipos := hp }

def BlockDefectMetricChange.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (I : AllFam) (d : HSMBlockDatum D K ι Ω) (A' : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (P0' : Ideal (MRing ι))
    (hdeg : A'.a = unitDeg d.k₀) (hc : IsConjInvariantH A') (hle : P0' ≤ mCoordIdeal d.y)
    (hp : IsSemipositiveRel P0' (mCoordIdeal d.y) A'),
    I.IsFamily →
    (fun n => hsDefect D (blockChi (d.withMetric A' P0' hdeg hc hle hp))
          (I K ι (mCoordIdeal d.y) (D + 1) fun _ => A') n -
        hsDefect D (blockChi d) (I K ι (mCoordIdeal d.y) (D + 1) fun _ => d.A) n) =o[atTop] pw D

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNmSectionsRational
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

namespace NmSectionsRationalProof

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem aeval_mul_prod_zpow (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) {d : K → ℕ} {g : MRing ι}
    (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g d) :
    aeval y g * ∏ k, y ⟨k, c k⟩ ^ (-(d k : ℤ)) = aeval (fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩) g := by
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [aeval_monomial, aeval_monomial, Finsupp.prod, Finsupp.prod]
  have hsub : ∀ f : (Σ k, ι k) → Ω, ∏ p ∈ m.support, f p ^ m p = ∏ p, f p ^ m p := fun f =>
    Finset.prod_subset (Finset.subset_univ _) (fun p _ hp => by simp [Finsupp.notMem_support_iff.mp hp])
  have hden : ∏ p, y ⟨p.1, c p.1⟩ ^ m p = ∏ k, y ⟨k, c k⟩ ^ d k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, y ⟨k, c k⟩ ^ m ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hg m hm k]
  simp only [hsub, div_pow, Finset.prod_div_distrib, hden, zpow_neg, zpow_natCast, Finset.prod_inv_distrib]
  ring


end NmSectionsRationalProof


end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFibreNormMax
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

def FibreNormMax.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (a : K → ℤ) (e : K → ℕ) (L : Fin (D + 1) → MRing ι),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    (∀ k, 1 ≤ e k) → (∀ j, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (L j) e) →
    (∀ z ∈ mcPts (mCoordIdeal y), ∃ j, eval z (map (Int.castRingHom ℂ) (L j)) ≠ 0) →
    ∃ (n c : ℕ) (B : ℝ), 1 ≤ n ∧ 1 ≤ B ∧
      ∀ τ : ℕ, ∀ u ∈ chartLatNm y a τ, u ≠ 0 →
        ∃ F : MvPolynomial (Fin (D + 1)) ℤ, F ≠ 0 ∧ (∀ i, F.degreeOf i ≤ c * (τ + 1)) ∧
          ∀ ζ : Fin (D + 1) → ℂ, (∀ i, ‖ζ i‖ = 1) →
          ∀ S : Finset ((Σ k, ι k) → ℂ),
            (∀ z ∈ mcPts (mCoordIdeal y),
              (∃ t : ℂ, ∀ j, eval z (map (Int.castRingHom ℂ) (L j)) = t * ζ j) →
              ∃ z' ∈ S, ∃ r : K → ℂ, (∀ k, r k ≠ 0) ∧ z = fun p => r p.1 * z' p) →
          ∀ M : ℝ, 0 ≤ M →
            (∀ z ∈ S, ∃ (dg dh : K → ℕ) (g h : MRing ι), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g dg ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog h dh ∧
              (∀ k, (dg k : ℤ) = dh k + τ * a k) ∧ aeval y g = u * aeval y h ∧
              eval z (map (Int.castRingHom ℂ) h) ≠ 0 ∧
              ‖eval z (map (Int.castRingHom ℂ) g)‖ ≤
                M * (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofMetrics (fun k => maxMetric (C := ℂ) (ι := ι k)) a).h z ^ τ *
                  ‖eval z (map (Int.castRingHom ℂ) h)‖) →
            ‖eval ζ (map (Int.castRingHom ℂ) F)‖ ≤ B ^ (τ + 1) * M ^ n



end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.CharacterNondegenerate
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter

noncomputable section

namespace NormCountBounded

section Coords

variable {Ω : Type} [Field Ω] {κ : Type} [Fintype κ]

theorem aeval_mul_zpow_mem (x : Ix κ → Ω) (c : κ) {τ : ℕ} {g : MRing (GlobalTheory κ)}
    (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g (fun _ => τ)) :
    aeval x g * x ⟨(), c⟩ ^ (-(τ : ℤ)) ∈ chartRingZ (ι := GlobalTheory κ) x (fun _ => c) := by
  have hsum : ∀ m ∈ g.support, ∑ p ∈ m.support, m p = τ := by
    intro m hm
    rw [Finset.sum_subset (Finset.subset_univ m.support) (fun p _ hp => by simpa using hp),
      Fintype.sum_sigma]
    simpa using hg m hm ()
  have key : aeval x g * x ⟨(), c⟩ ^ (-(τ : ℤ)) =
      aeval (fun p : Ix κ => x p / x ⟨(), c⟩) g := by
    conv_lhs => rw [g.as_sum]
    conv_rhs => rw [g.as_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [aeval_monomial, aeval_monomial, Finsupp.prod, Finsupp.prod]
    simp only [div_eq_mul_inv, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hsum m hm,
      zpow_neg, zpow_natCast]
    ring
  rw [key, chartRingZ, Algebra.adjoin_range_eq_range_aeval]
  exact ⟨g, rfl⟩

theorem secM_le_chartLat (x : Ix κ → Ω) (τ : ℕ) :
    secM (ι := GlobalTheory κ) x (fun _ => τ) ≤ chartLat (ι := GlobalTheory κ) x 1 τ := by
  intro s hs
  have hle : Submodule.span ℤ {s | ∃ g : MRing (GlobalTheory κ), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g (fun _ => τ) ∧ aeval x g = s} ≤
      (chartLat (ι := GlobalTheory κ) x 1 τ).toIntSubmodule := by
    rw [Submodule.span_le]
    rintro _ ⟨g, hg, rfl⟩ c _
    have hc : c = fun _ => c () := rfl
    rw [hc]
    simpa using aeval_mul_zpow_mem x (c ()) hg
  exact hle hs

end Coords

section Counts

variable {Ω : Type} [Field Ω]

theorem norm_count_bounded {h : ℕ → ℝ} {C : ℝ} (D : ℕ) (hC : ∀ τ, h τ ≤ C * ((τ : ℝ) + 1) ^ (D + 1)) :
    ∃ B, ∀ᶠ τ in atTop, h τ / ((τ : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) ≤ B := by
  refine ⟨|C| * 2 ^ (D + 1) * ((D + 1).factorial : ℝ), eventually_atTop.2 ⟨1, fun τ hτ => ?_⟩⟩
  have hτ' : (1 : ℝ) ≤ τ := by exact_mod_cast hτ
  have hfac : (0 : ℝ) < (D + 1).factorial := by exact_mod_cast Nat.factorial_pos _
  have hden : 0 < (τ : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ) := by positivity
  rw [div_le_iff₀ hden]
  have h1 : ((τ : ℝ) + 1) ^ (D + 1) ≤ 2 ^ (D + 1) * (τ : ℝ) ^ (D + 1) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) _
  calc h τ ≤ C * ((τ : ℝ) + 1) ^ (D + 1) := hC τ
    _ ≤ |C| * ((τ : ℝ) + 1) ^ (D + 1) := mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    _ ≤ |C| * (2 ^ (D + 1) * (τ : ℝ) ^ (D + 1)) := mul_le_mul_of_nonneg_left h1 (abs_nonneg C)
    _ = |C| * 2 ^ (D + 1) * ((D + 1).factorial : ℝ) * ((τ : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) := by
      field_simp

end Counts

end NormCountBounded

namespace NormCountBounded

end NormCountBounded


end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSecEq
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

def SecEq.Statement : Prop := KH.SecEqStatement

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPointHeightFS
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory

noncomputable section

def PointHeightFS.Statement : Prop :=
  ∀ I : AllFam, I.IsFamily → hhOf I 0 = 0

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsKrullDimMatAct
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def KrullDimMatAct.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] (J : Type) [Fintype J] (x : J → Ω) (B : Matrix J J ℚ), IsInvMat B →
    ringKrullDim (MvPolynomial J ℤ ⧸ coordIdeal ℤ (matAct B x)) = ringKrullDim (MvPolynomial J ℤ ⧸ coordIdeal ℤ x)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsProjDegGenDeg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

def ProjDegGenDeg.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω) (e : Fin (D + 1) → Ix κ),
    IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1) → IsProjFrame x e →
    genDeg (ι := GlobalTheory κ) (coordIdeal ℤ x) D 1 = (projDeg x e : ℤ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsMetricMaxComparison
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

def MetricMaxComparison.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι), IsSmoothHerm A →
    ∃ C : ℝ, 1 ≤ C ∧ ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) →
      A.h z ≤ C * (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofMetrics (fun k => maxMetric (C := ℂ) (ι := ι k)) A.a).h z

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGenDegMatAct
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

def GenDegMatAct.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω)
    (B : Matrix (Ix κ) (Ix κ) ℚ),
    IsInvMat B → genDeg (ι := GlobalTheory κ) (coordIdeal ℤ (matAct B x)) D 1 = genDeg (ι := GlobalTheory κ) (coordIdeal ℤ x) D 1

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
