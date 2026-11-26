module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsKodairaGeneric
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRatNoetherFrame
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResVolume

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionsDimZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def SectionsDimZero.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (a : K → ℤ) (n : ℕ),
    IsArithVar (mCoordIdeal y) 1 →
      (Module.finrank ℚ (chartLatQ y a n) : ℤ) = genDeg (mCoordIdeal y) 0 a

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ImportsLast
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def KleimanVarietyH1Generation.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (I : IFamily F ι) (Q : Ideal (MRingOver F ι))
    (α : K → ℤ) (b a : ℕ),
    IsFieldIntersection I → IsMultiProjPrime Q → KH.NefOnF I Q α → 1 ≤ b → 1 ≤ a →
    H1GenAmple F Q (b • α + fun _ => (a : ℤ))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockResolutionImageSup
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory

noncomputable section

def BlockResolutionImageSup.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (d : HSMBlockDatum D K ι Ω),
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ f : MRingOver ℂ ι, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f (blockDeg d.k₀ n) →
      ∀ x : d.R.X,
        ‖eval (blockPt d x) f‖ / d.A.h (blockPt d x) ^ n ≤ C * (n : ℝ) ^ ((D : ℝ) / 2) * blockL2NormComplex d n f

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsShiftIntersectionPolynomial
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory

noncomputable section

def ShiftIntersectionPolynomial.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (II : IntersectionSystem) (P : Ideal (MRing ι))
    (n : ℕ) (A B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι),
    IsIntersectionSystem II → IsArithVar P n → IsSmoothHerm A → IsSmoothHerm B →
    ∃ p : Polynomial ℝ, p.natDegree ≤ n ∧ p.coeff n = II K ι P n (fun _ => A) ∧
      ∀ q : ℕ, II K ι P n (fun _ => HermLine.zcomb A B (q : ℤ) 1) = p.eval (q : ℝ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockResolutionMixedIntegral
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def BlockResolutionMixedIntegral.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (d : HSMBlockDatum D K ι Ω) (A' : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι), A'.a = unitDeg d.k₀ → IsSmoothHerm A' →
    ∑ i ∈ Finset.range (D + 1),
        ptsIntegral (mCoordIdeal d.y) (blockMixPot d.A A' D i) (fun z => Real.log (A'.h z / d.A.h z)) =
      ((D : ℝ) + 1) * blockMetricInt d A'

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsShiftNefBig
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter

noncomputable section

def ShiftNefBig.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (P0 : Ideal (MRing ι)),
    1 ≤ D → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    P0 ≤ mCoordIdeal y → IsSemipositiveRel P0 (mCoordIdeal y) A → NefOnFibres (mCoordIdeal y) A.a →
    IsConjInvariantH A →
    ∀ q : ℕ, 1 ≤ q → IsNefBigDatum P0 y D (HermLine.zcomb A (fsH ι) (q : ℤ) 1)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockResolutionMixedBridge
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M

noncomputable section

def BlockResolutionMixedBridge.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (d : HSMBlockDatum D K ι Ω) (L : Fin D → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (A₁ : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι),
    (∀ j, IsSmoothHerm (L j)) → A₁.a = unitDeg d.k₀ → IsSmoothHerm A₁ →
    ptsIntegral (mCoordIdeal d.y) (fun j z => Real.log ((L j).h z)) (fun z => Real.log (A₁.h z / d.A.h z)) =
      mInt d.R.A (fun j => AnResBridge.potOf d.R (L j))
        (fun x => Real.log (A₁.h (blockPt d x) / d.A.h (blockPt d x)))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockResolutionDegreeIntegral
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M

noncomputable section

def BlockResolutionDegreeIntegral.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (d : HSMBlockDatum D K ι Ω) (A₀ A₁ : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι),
    A₀.a = unitDeg d.k₀ → A₁.a = unitDeg d.k₀ → IsSmoothHerm A₀ → IsSmoothHerm A₁ →
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      mInt d.R.A (fun _ => blockInterpPot d A₀ A₁ t) (fun _ => 1) =
        (genDeg (mCoordIdeal d.y) D (unitDeg d.k₀) : ℝ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockComplexGramMetricChange
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

def BlockComplexGramMetricChange.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (d : HSMBlockDatum D K ι Ω) (A' : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (P0' : Ideal (MRing ι))
    (hdeg : A'.a = unitDeg d.k₀) (hc : IsConjInvariantH A') (hle : P0' ≤ mCoordIdeal d.y)
    (hp : IsSemipositiveRel P0' (mCoordIdeal d.y) A'),
    (fun n => blockCChi (d.withMetric A' P0' hdeg hc hle hp) n - blockCChi d n -
        (n : ℝ) ^ (D + 1) / (D.factorial : ℝ) * blockMetricInt d A') =o[atTop] pw D

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsDiagonalSectionDifference
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter

noncomputable section

def DiagonalSectionDifference.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ),
    1 ≤ D → IsArithVar (mCoordIdeal y) (D + 1) →
    ∃ C : ℝ, ∀ᶠ j : ℕ in atTop,
      (Module.finrank ℚ (chartLatQ y ((j : ℤ) • (1 : K → ℤ)) 1) : ℝ) ≤
        (Module.finrank ℚ (chartLatQ y ((j : ℤ) • (1 : K → ℤ) - 1) 1) : ℝ) + C * (j : ℝ) ^ (D - 1)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGramChiDerivative
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.CP

noncomputable section

def GramChiDerivative.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] (A : FinHolAtlas D X) (L : HolLineBundle A) (W₀ W₁ : Weight L)
    (dV : SmoothVolume A) (n : ℕ) (V : Submodule ℂ (Fin A.n → X → ℂ)) [FiniteDimensional ℂ V],
    V ≤ L.sections n → ∀ (e : Module.Basis (Fin (Module.finrank ℂ V)) ℂ V) (t : ℝ),
      HasDerivAt (fun s : ℝ ↦ chiGram (W₀.lerp W₁ s) dV n (fun a ↦ (e a : Fin A.n → X → ℂ)))
        ((n : ℝ) / 2 * ∫ x, Weight.diff W₁ W₀ x * bergman (W₀.lerp W₁ t) dV V n x ∂dV.μ) t

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockResolutionDegree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M

noncomputable section

def BlockResolutionDegree.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (d : HSMBlockDatum D K ι Ω) (A₀ A₁ : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι),
    A₀.a = unitDeg d.k₀ → A₁.a = unitDeg d.k₀ → IsSmoothHerm A₀ → IsSmoothHerm A₁ →
    ∀ t ∈ Set.Icc (0 : ℝ) 1, ∃ C : ℝ, ∀ n : ℕ,
      |(Module.finrank ℤ (secM d.y (blockDeg d.k₀ n)) : ℝ) -
          mInt d.R.A (fun _ => blockInterpPot d A₀ A₁ t) (fun _ => 1) * (n : ℝ) ^ D / (D.factorial : ℝ)| ≤
        C * ((n : ℝ) + 1) ^ (D - 1)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockResolutionInterpIntegral
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M

noncomputable section

def BlockResolutionInterpIntegral.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (d : HSMBlockDatum D K ι Ω) (A' : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι), A'.a = unitDeg d.k₀ → IsSmoothHerm A' →
    ((D : ℝ) + 1) * blockMetricInt d A' =
      ∑ i ∈ Finset.range (D + 1),
        mInt d.R.A
          (fun j : Fin D => if j.val < i then AnResBridge.potOf d.R A' else AnResBridge.potOf d.R d.A)
          (fun x => Real.log (A'.h (blockPt d x) / d.A.h (blockPt d x)))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockImageHilb
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def BlockImageHilb.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (κ : Type) [Fintype κ] (y : (Σ k, ι k) → Ω) (k₀ : K) (M : Matrix (Ix κ) (ι k₀) ℤ)
    (N : Matrix (ι k₀) (Ix κ) ℤ) (x : Ix κ → Ω),
    IsBlockImage y k₀ M N x → ∀ n : ℕ,
      GroundTheory.Heights₂.Heights.NumbersDVR.hilbFn (ι := GlobalTheory κ)
          ((coordIdeal ℤ x).map (MvPolynomial.map (Int.castRingHom ℚ))) (fun _ => (n : ℤ)) =
        GroundTheory.Heights₂.Heights.NumbersDVR.hilbFn ((mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ)))
          (fun k => if k = k₀ then (n : ℤ) else 0)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockImageTop
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

def BlockImageTop.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (κ : Type) [Fintype κ] (I : AllFam) (y : (Σ k, ι k) → Ω) (k₀ : K) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι)
    (M : Matrix (Ix κ) (ι k₀) ℤ) (N : Matrix (ι k₀) (Ix κ) ℤ) (x : Ix κ → Ω)
    (m : ConeMetric (C := ℂ) (ι := Ix κ)),
    I.IsFamily → IsArithVar (mCoordIdeal y) (D + 1) → BlockBirational y k₀ →
    IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1) → IsBlockImage y k₀ M N x → A.a = unitDeg k₀ →
    IsSmoothHerm A → IsSmoothMetric m → (∀ z ∈ mcPts (mCoordIdeal y), A.h z = m.ρ (blockMapC k₀ M z)) →
    I K ι (mCoordIdeal y) (D + 1) (fun _ => A) = top I x m D

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionOrderAtPoint
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def SectionOrderAtPoint.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (a : K → ℤ) (τ : ℕ) (s : Ω) (W : Ideal (MRing ι)) (G H : MRing ι)
    (dg dh : K → ℕ),
    IsArithVar W 1 → mCoordIdeal y ≤ W → s ∈ chartLatNm y a τ →
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog G dg → ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog H dh → (∀ k, (dg k : ℤ) = dh k + τ * a k) →
    aeval y G = s * aeval y H → G ∉ W → H ∉ W →
    ∀ V ∈ divSupp W H, V ∈ divSupp W G ∧
      multAt (W ⊔ Ideal.span {H}) V ≤ multAt (W ⊔ Ideal.span {G}) V

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsChartCover
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.CP

noncomputable section

def ChartTaylorCover.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] (A : FinHolAtlas D X) (L : HolLineBundle A) (W₀ W₁ : Weight L)
    (dV : SmoothVolume A),
    ∃ r : ℝ, 0 < r ∧ ∃ M c : ℝ, 0 < c ∧ ∀ x : X, ∃ j : Fin A.n, x ∈ (A.chart j).source ∧
      Metric.closedBall (A.chart j x) r ⊆ (A.chart j).target ∧
      (∀ y ∈ Metric.closedBall (A.chart j x) r, c ≤ dV.dens j y) ∧
      ∀ W ∈ [W₀, W₁], ∃ ℓ : (Fin D → ℂ) →L[ℝ] ℝ, ∀ z : Fin D → ℂ, ‖z‖ ≤ r →
        W.φ j ((A.chart j).symm (A.chart j x + z)) ≤ W.φ j x + ℓ z + M * ∑ i, ‖z i‖ ^ 2

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResolutionPullback
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M

noncomputable section

def ResolutionPullback.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (d : HSMBlockDatum D K ι Ω),
    ∃ (A : FinHolAtlas D d.R.X) (L : HolLineBundle A) (W : Weight L) (dV : SmoothVolume A),
      A.Compatible d.R.A ∧ W.IsSemipositive ∧ dV.μ = d.dV ∧
      ∀ (n : ℕ) (f : MRing ι), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f (blockDeg d.k₀ n) →
        ∃ s ∈ L.sections n, ∀ x : d.R.X,
          ptNormSq W n s x =
            (‖eval (blockPt d x) (map (Int.castRingHom ℂ) f)‖ / d.A.h (blockPt d x) ^ n) ^ 2

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ImportsTail
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def H1VanishingDevissage.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (V : Ideal (MRingOver S ι)) (N : K → ℤ),
    IsNoetherianRing S →
    (∀ P : Ideal (MRingOver S ι), IsMultiProjPrime P → V ≤ P → ∀ e : K → ℤ, ∃ c₁ : ℕ, ∀ c : ℕ, c₁ ≤ c →
      Subsingleton (KH.cechHc ι (KH.quotPart S P) (e + c • N) 1)) →
    ∀ (M : Type) [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
      (𝓜 : (K → ℤ) → Submodule S M),
      Module.Finite (MRingOver S ι) M → KH.IsMGraded S ι 𝓜 → V ≤ Module.annihilator (MRingOver S ι) M →
      ∀ e : K → ℤ, ∃ c₁ : ℕ, ∀ c : ℕ, c₁ ≤ c → Subsingleton (KH.cechHc ι 𝓜 (e + c • N) 1)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IntConst
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory

noncomputable section

def L2GramLattice.Statement : Prop :=
  ∀ (E : Type) [AddCommGroup E] [Module.Free ℤ E] [Module.Finite ℤ E] (X : Type) [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (w : E →+ (X → ℂ)),
    (∀ s, AEStronglyMeasurable (w s) μ) → (∀ s, ∃ C : ℝ, ∀ᵐ z ∂μ, ‖w s z‖ ≤ C) →
    (∀ (r : ℕ) (x : Fin r → E), LinearIndependent ℤ x → ∀ c : Fin r → ℝ,
      (∀ᵐ z ∂μ, ∑ i, (c i : ℂ) * w (x i) z = 0) → c = 0) →
    ∃ φ : E →+ EuclideanSpace ℝ (Fin (Module.finrank ℤ E)),
      Function.Injective φ ∧ DiscreteTopology (imageLattice φ) ∧
      (∀ [DiscreteTopology (imageLattice φ)], IsZLattice ℝ (imageLattice φ)) ∧
      ∀ s, ‖φ s‖ = Real.sqrt (∫ z, ‖w s z‖ ^ 2 ∂μ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsShiftVolumeBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter

noncomputable section

def ShiftVolumeBound.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (P0 : Ideal (MRing ι)),
    1 ≤ D → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    P0 ≤ mCoordIdeal y → IsSemipositiveRel P0 (mCoordIdeal y) A → NefOnFibres (mCoordIdeal y) A.a →
    IsConjInvariantH A →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : ℕ, 1 ≤ q →
      arVolP (IsSmallH (mCoordIdeal y) y (HermLine.zcomb A (fsH ι) (q : ℤ) 1))
          (chartLat y (HermLine.zcomb A (fsH ι) (q : ℤ) 1).a) 1 D ≤
        C * ((q : ℝ) + 1) * (genDeg (mCoordIdeal y) D (HermLine.zcomb A (fsH ι) (q : ℤ) 1).a : ℝ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsAnResNullForm
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory

noncomputable section

def AnResNullForm.Statement : Prop :=
  ∀ (e : ℕ) (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι))
    (R : AnRes P J e) (G : MRing ι) (dG : K → ℕ),
    IsArithVar P (e + 1) → ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog G dG → G ∉ P →
      ∀ j, volume ((R.A.chart j).target ∩
        (R.A.chart j).symm ⁻¹' {a | eval (R.lift a a) (map (Int.castRingHom ℂ) G) = 0}) = 0

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionSpanStep
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def SectionSpanStep.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (a : K → ℤ) (q : ℕ) (w : Fin q → Ω),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → (∀ j, w j ∈ chartLat y a 1) → KH.GeneratesOn y a w →
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      chartLat y a (n + 1) ≤ AddSubgroup.closure {t | ∃ s ∈ chartLat y a n, ∃ j, t = s * w j}

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSpanStepHomog
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def SpanStepHomog.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (a : K → ℤ) (q : ℕ) (w : Fin q → Ω),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → (∀ j, w j ∈ chartLat y a 1) → KH.GeneratesOn y a w →
    ∃ (m r : ℕ) (t : Fin r → Ω), (∀ l, t l ∈ chartLat y a m) ∧
      ∀ (n : ℕ), ∀ s ∈ chartLat y a n, ∀ j, w j ≠ 0 →
        ∃ D : ℕ, s * w j ^ D ∈ gradedSpan w (fun _ => m) t (n + D)

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSpanStepLocal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def SpanStepLocal.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (a : K → ℤ) (q : ℕ) (w : Fin q → Ω),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → (∀ j, w j ∈ chartLat y a 1) → KH.GeneratesOn y a w →
    ∀ j, w j ≠ 0 → ∃ (r : ℕ) (b : Fin r → Ω), (∀ l, ∃ n : ℕ, b l * w j ^ n ∈ chartLat y a n) ∧
      ∀ (g : Ω) (n : ℕ), g * w j ^ n ∈ chartLat y a n →
        ∃ c : Fin r → Ω, (∀ l, c l ∈ Algebra.adjoin ℤ (Set.range fun i => w i / w j)) ∧ g = ∑ l, c l * b l

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSmallSectionsSeparated
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

def SmallSectionsSeparated.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y → IsSmoothHerm A →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℕ, ∃ (Z : Finset ((Σ k, ι k) → ℂ)) (ev : chartLatNm y A.a τ →+ (Z → ℂ)),
      (∀ z ∈ Z, z ∈ mcPts (mCoordIdeal y)) ∧
      (∀ (s : chartLatNm y A.a τ) (z : Z), ∃ (dg dh : K → ℕ) (g h : MRing ι),
        ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g dg ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog h dh ∧ (∀ k, (dg k : ℤ) = dh k + τ * A.a k) ∧
        aeval y g = (s : Ω) * aeval y h ∧ eval (z : (Σ k, ι k) → ℂ) (map (Int.castRingHom ℂ) h) ≠ 0 ∧
        ev s z * eval (z : (Σ k, ι k) → ℂ) (map (Int.castRingHom ℂ) h) =
          eval (z : (Σ k, ι k) → ℂ) (map (Int.castRingHom ℂ) g)) ∧
      ∀ s t : chartLatNm y A.a τ, IsSmallH (mCoordIdeal y) y A τ (s : Ω) →
        IsSmallH (mCoordIdeal y) y A τ (t : Ω) → s ≠ t →
        ∃ z : Z, Real.exp (-(C * ((τ : ℝ) + 1))) * A.h z ^ τ ≤ ‖ev s z - ev t z‖

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockGraphImage
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I4

section Objects

variable {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)]

def blockForms {κ : Type} (k₀ : K) (M : Matrix (Ix κ) (ι k₀) ℤ) : (Σ k, GlobalTheory κ k) → MRing ι :=
  fun q => ∑ i, C (M q i) * X ⟨k₀, i⟩

end Objects

def BlockGraphImage.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (κ : Type) [Fintype κ] (y : (Σ k, ι k) → Ω) (k₀ : K) (M : Matrix (Ix κ) (ι k₀) ℤ)
    (N : Matrix (ι k₀) (Ix κ) ℤ) (x : Ix κ → Ω),
    IsBlockImage y k₀ M N x →
    imageZ (inrV (ι := ι) (ι₂ := GlobalTheory κ)) (graphIdeal (mCoordIdeal y) (blockForms k₀ M)) = coordIdeal ℤ x

end GroundTheory.Heights₂.Heights.HilbertSamuel

end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockImageChi
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory

noncomputable section

def BlockImageChi.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (d₀ : HSMBlockDatum D K ι Ω) (r : ℕ) (M : Matrix (Ix (Fin r)) (ι d₀.k₀) ℤ)
    (N : Matrix (ι d₀.k₀) (Ix (Fin r)) ℤ) (d' : HSMDatum D Ω (Fin r)),
    IsBlockImage d₀.y d₀.k₀ M N d'.x →
    (∀ z ∈ mcPts (mCoordIdeal d₀.y), d₀.A.h z = d'.m.ρ (blockMapC d₀.k₀ M z)) →
    (∀ g : (Ix (Fin r) → ℂ) → ℂ, ContinuousOn g {0}ᶜ → (∀ (c : ℂ) z, c ≠ 0 → g (c • z) = g z) →
      ∫ a, g (resPt d' a) ∂d'.dV = ∫ a, g (blockMapC d₀.k₀ M (blockPt d₀ a)) ∂d₀.dV) →
    ∀ n, blockChi d₀ n = resChi d' n

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsChartConstantsDetermined
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry NumberField

def intsIn (F Ω : Type*) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] : Subalgebra ℤ Ω :=
  ((algebraMap F Ω).comp (algebraMap (𝓞 F) F)).toIntAlgHom.range

def ChartConstantsDetermined.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (F : Type) [Field F] [NumberField F] [Algebra F Ω] (y : (Σ k, ι k) → Ω),
    (∀ z ∈ mcPts (mCoordIdeal y), ∃! sg : F →+* ℂ, LiesOver y sg z) →
    ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) →
    ∀ w w' : ↥(chartRingZ y c ⊔ intsIn F Ω) →+* ℂ,
      w.comp (Subalgebra.inclusion (le_sup_left : chartRingZ y c ≤ chartRingZ y c ⊔ intsIn F Ω)).toRingHom =
          w'.comp (Subalgebra.inclusion (le_sup_left : chartRingZ y c ≤ chartRingZ y c ⊔ intsIn F Ω)).toRingHom →
        w.comp (Subalgebra.inclusion (le_sup_right : intsIn F Ω ≤ chartRingZ y c ⊔ intsIn F Ω)).toRingHom =
          w'.comp (Subalgebra.inclusion (le_sup_right : intsIn F Ω ≤ chartRingZ y c ⊔ intsIn F Ω)).toRingHom

section Inhabitants

open ProjLine

end Inhabitants

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSublatticeDegree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

def SublatticeDegree.Statement : Prop :=
  ∀ (E E' : Type) [AddCommGroup E] [AddCommGroup E'] (R R' : ℕ) (φ : E →+ EuclideanSpace ℝ (Fin R))
    (φ' : E' →+ EuclideanSpace ℝ (Fin R')) [DiscreteTopology (imageLattice φ)] [IsZLattice ℝ (imageLattice φ)]
    [DiscreteTopology (imageLattice φ')] [IsZLattice ℝ (imageLattice φ')] (ψ : E' →+ E) (S : Set E) (C : ℝ),
    Function.Injective φ → Function.Injective φ' → Function.Injective ψ → (∀ x, ‖φ (ψ x)‖ ≤ ‖φ' x‖) →
    AddSubgroup.closure S = ⊤ → (∀ s ∈ S, ‖φ s‖ ≤ C) → 1 ≤ C →
    -Real.log (ZLattice.covolume (imageLattice φ')) ≤
      -Real.log (ZLattice.covolume (imageLattice φ)) + R * Real.log C

namespace SublatticeDegree

abbrev b1 : Module.Basis (Fin 1) ℝ (EuclideanSpace ℝ (Fin 1)) := (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis

abbrev lat1 : Submodule ℤ (EuclideanSpace ℝ (Fin 1)) := Submodule.span ℤ (Set.range b1)

abbrev φ1 : lat1 →+ EuclideanSpace ℝ (Fin 1) := lat1.subtype.toAddMonoidHom

end SublatticeDegree

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockResolutionMetricPair
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M MeasureTheory

noncomputable section

def BlockResolutionMetricPair.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (d : HSMBlockDatum D K ι Ω) (A' : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (P0' : Ideal (MRing ι)),
    A'.a = unitDeg d.k₀ → P0' ≤ mCoordIdeal d.y → IsSemipositiveRel P0' (mCoordIdeal d.y) A' →
    ∃ (A : FinHolAtlas D d.R.X) (L : HolLineBundle A) (W₀ W₁ : Weight L) (dV : SmoothVolume A)
      (σ : ℕ → MvPolynomial (Σ k, ι k) ℚ → Fin A.n → d.R.X → ℂ),
      A.Compatible d.R.A ∧ W₀.IsSemipositive ∧ W₁.IsSemipositive ∧ dV.μ = d.dV ∧
      (∀ (n : ℕ) (b : MvPolynomial (Σ k, ι k) ℚ), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog b (blockDeg d.k₀ n) → σ n b ∈ L.sections n) ∧
      (∀ y : d.R.X, ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧
        (∀ (n : ℕ) (b : MvPolynomial (Σ k, ι k) ℚ), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog b (blockDeg d.k₀ n) →
          σ n b (chartIdx A y) y = eval (fun p => c p.1 * blockPt d y p) (map (algebraMap ℚ ℂ) b)) ∧
        W₀.φ (chartIdx A y) y = 2 * Real.log (d.A.h (fun p => c p.1 * blockPt d y p)) ∧
        W₁.φ (chartIdx A y) y = 2 * Real.log (A'.h (fun p => c p.1 * blockPt d y p))) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ g : d.R.X → ℝ, Continuous g →
        ∫ y, g y * bergmanDens (W₀.lerp W₁ t) dV y ∂dV.μ =
          mInt d.R.A (fun _ => blockInterpPot d d.A A' t) g / (D.factorial : ℝ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTwistIntersectionAnyDegree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology

noncomputable section

def TwistIntersectionAnyDegree.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (F : Type) [Field F] [NumberField F] [Algebra F Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (II : IntersectionSystem)
    (Λ : (F →+* ℂ) → ℝ),
    1 ≤ D → IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    IsSmoothHerm A → B.a = 0 → IsSmoothHerm B → (∀ sg, 0 < Λ sg) →
    (∀ z ∈ mcPts (mCoordIdeal y), ∃! sg : F →+* ℂ, LiesOver y sg z) →
    (∀ z ∈ mcPts (mCoordIdeal y), ∀ sg : F →+* ℂ, LiesOver y sg z → B.h =ᶠ[𝓝 z] fun _ => Λ sg) →
    II K ι (mCoordIdeal y) (D + 1) (fun _ => A.tensor B) =
      II K ι (mCoordIdeal y) (D + 1) (fun _ => A) +
        ((D + 1 : ℕ) : ℝ) * genDeg (mCoordIdeal y) D A.a *
          ((∑ sg, Real.log (Λ sg)) / Fintype.card (F →+* ℂ))

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
