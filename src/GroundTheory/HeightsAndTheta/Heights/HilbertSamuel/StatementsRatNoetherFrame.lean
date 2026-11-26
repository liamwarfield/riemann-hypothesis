module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.IsSaturatedFirstCoordinateLine

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRatNoetherFrame
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def RatNoetherFrame.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω),
    IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1) →
    ∃ (B : Matrix (Ix κ) (Ix κ) ℚ) (e : Fin (D + 1) → Ix κ), IsInvMat B ∧ IsRatProjFrame (matAct B x) e

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGenFibreHomog
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def GenFibreHomog.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω),
    GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomogIdeal
      ((mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ)))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockMeasureChange
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

def BlockMeasureChange.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (d d' : HSMBlockDatum D K ι Ω),
    d'.y = d.y → d'.k₀ = d.k₀ → d'.A = d.A →
    (fun n => blockChi d' n - blockChi d n) =o[atTop] pw D

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTopPullFS
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

def TopPullFS.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (I : AllFam) (x : Ix κ → Ω)
    (m : ConeMetric ℂ (Ix κ)) (e : Fin (D + 1) → Ix κ),
    I.IsFamily → IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1) → IsSmoothMetric m → IsProjFrame x e →
    IsPullFS x e m → top I x m D = (projDeg x e : ℝ) * hhOf I D

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSmallSectionsNonzero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def SmallSectionsNonzero.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : HermLine ι) (P0 : Ideal (MRing ι)),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y → IsSmallGeneratedDatum P0 y D A →
    ∀ j : ℕ, ∃ t ∈ chartLat y A.a j, t ≠ 0 ∧ IsSmallH (mCoordIdeal y) y A j t

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTopConstantTwist
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

def TopConstantTwist.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (D : ℕ)
    (A : HermLine ι) (c : ℝ) (II : IntersectionSystem),
    IsIntersectionSystem II → IsArithVar P (D + 1) → IsSmoothHerm A →
    II K ι P (D + 1) (fun _ => A.tensor (constLine c)) =
      II K ι P (D + 1) (fun _ => A) - ((D + 1 : ℕ) : ℝ) * c * geomDeg P A D

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsProjFSMass
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def ProjFSMass.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω) (e : Fin (D + 1) → Ix κ)
    (m : ConeMetric ℂ (Ix κ)), IsProjFrame x e → IsPullFS x e m →
    ∃ Ψ : (((k : Unit) → GlobalTheory κ k) → ℂ) →ₗ[ℂ] (Fin (D + 1) → ℂ),
      IsGoodProj (ι := GlobalTheory κ) (coordIdeal ℤ x) Ψ ∧
        ptsIntegralAt (ι := GlobalTheory κ) (coordIdeal ℤ x) Ψ (purePot m D) (fun _ => 1) = (projDeg x e : ℝ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSecondVeronese
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory

noncomputable section

def SecondVeronese.Statement : Prop :=
  ∀ D : ℕ, 1 ≤ D →
    ∃ (Ω : Type) (_ : Field Ω) (_ : CharZero Ω) (κ : Type) (_ : Fintype κ) (d : HSMDatum D Ω κ),
      (∀ n : ℕ, resChi d n = chiP D (2 * n)) ∧
      (∀ I : AllFam, I.IsFamily → top I d.x d.m D = 2 ^ (D + 1) * hhOf I D) ∧
      genDeg (ι := GlobalTheory κ) (coordIdeal ℤ d.x) D 1 = 2 ^ D

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSecMRankBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def SecMRankBound.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (b : K → ℕ),
    IsArithVar (mCoordIdeal y) (D + 1) → (∀ k, 1 ≤ b k) →
    (∀ m : ℕ, Module.Finite ℤ (secM y (fun k => m * b k))) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, (Module.finrank ℤ (secM y (fun k => m * b k)) : ℝ) ≤ C * ((m : ℝ) + 1) ^ D

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSmallSectionMixed
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

def SmallSectionMixed.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P P0 : Ideal (MRing ι)) (d : ℕ)
    (M H : HermLine ι) (p q : ℕ) (II : IntersectionSystem),
    IsIntersectionSystem II → 1 ≤ d → IsArithVar P d → P0 ≤ P →
    IsSemipositiveRel P0 P M → NefOnFibres P M.a → IsConjInvariantH M →
    (H.a = fun _ => (1 : ℤ)) → IsSemipositiveRel P0 P H → MonomialsBounded P H (fun _ => 1) → IsConjInvariantH H →
    1 ≤ p → 0 < II K ι P d (fun _ => HermLine.zcomb M H q p) →
    ∃ (n : ℕ) (f g : MRing ι), 1 ≤ n ∧ IsRatSectionOn P (HermLine.zcomb M H ((n * q : ℕ) : ℤ) ((n * p : ℕ) : ℤ)) f g ∧
      divCycle P g ≤ divCycle P f ∧
      ∀ z ∈ mcPts P, ‖eval z (map (Int.castRingHom ℂ) f)‖ ≤
        ‖eval z (map (Int.castRingHom ℂ) g)‖ * (HermLine.zcomb M H ((n * q : ℕ) : ℤ) ((n * p : ℕ) : ℤ)).h z

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResChiBounds
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory

noncomputable section

def ResChiBounds.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (d : HSMDatum D Ω κ)
    (e : Fin (D + 1) → Ix κ),
    IsProjFrame d.x e → IsPullFS d.x e d.m →
    ∃ (k : ℕ) (C : ℝ), ∀ n : ℕ, k + 1 ≤ n →
      (projDeg d.x e : ℝ) * chiP D (n - k) - C * (n : ℝ) ^ D * Real.log (n + 1) ≤ resChi d n ∧
      resChi d n ≤ (projDeg d.x e : ℝ) * chiP D (n + k) + C * (n : ℝ) ^ D * Real.log (n + 1)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPerturbMonomial
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter

noncomputable section

def PerturbMonomial.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (a : K → ℕ) (A : HermLine ι) (P0 : Ideal (MRing ι)) (q : ℕ),
    1 ≤ D → IsArithVar (mCoordIdeal y) (D + 1) → Birational y → (A.a = fun k => (a k : ℤ)) →
    P0 ≤ mCoordIdeal y → IsSemipositiveRel P0 (mCoordIdeal y) A → MonomialsBounded (mCoordIdeal y) A a →
    1 ≤ q →
    IsSmallGeneratedDatum P0 y D (HermLine.zcomb A (fsH ι) q 1)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsAvoidFormFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

noncomputable section

def AvoidFormFinite.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (S : Set (MRingOver ℂ ι)) (G : MRingOver ℂ ι) (e : K → ℕ),
    (∀ k, 1 ≤ e k) → IsMultiHomog G e → (∀ s ∈ S, ∃ a, IsMultiHomog s a) →
    (∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → (∀ s ∈ S, eval z s = 0) → eval z G ≠ 0) →
    ∃ T : Finset ((Σ k, ι k) → ℂ), ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) →
      (∀ s ∈ S, eval z s = 0) → ∃ t ∈ T, ∃ r : K → ℂ, (∀ k, r k ≠ 0) ∧ z = fun p => r p.1 * t p

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockSectionsRank
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M

noncomputable section

def BlockSectionsRank.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (y : (Σ k, ι k) → Ω) (k₀ : K),
    1 ≤ D → IsArithVar (mCoordIdeal y) (D + 1) → BlockBirational y k₀ →
    ∃ C : ℝ, ∀ n : ℕ,
      |(Module.finrank ℤ (secM y (blockDeg k₀ n)) : ℝ) -
          (genDeg (mCoordIdeal y) D (unitDeg k₀) : ℝ) * (n : ℝ) ^ D / (D.factorial : ℝ)| ≤
        C * ((n : ℝ) + 1) ^ (D - 1)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsUpperNormalisation
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter

noncomputable section

def UpperNormalisation.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (B : HermLine ι) (P0 : Ideal (MRing ι)) (II : IntersectionSystem),
    1 ≤ D → IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    IsSmallGeneratedDatum P0 y D B → IsConjInvariantH B → (∀ k, 1 ≤ B.a k) →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      smallSectionCount (IsSmallH (mCoordIdeal y) y B) (chartLatNm y B.a) n ≤
        (II K ι (mCoordIdeal y) (D + 1) (fun _ => B) + ε) * ((n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsShiftSectionSeparation
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory

noncomputable section

def ShiftSectionSeparation.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : HermLine ι),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y → IsSmoothHerm A →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : ℕ, 1 ≤ q → ∀ (n : ℕ) (s : Ω),
      s ∈ chartLat y (HermLine.zcomb A (fsH ι) (q : ℤ) 1).a n → s ≠ 0 →
      ∀ c : ℝ, c < Real.exp (-(C * n * ((q : ℝ) + 1))) →
        ¬ IsBoundedH (mCoordIdeal y) y (HermLine.zcomb A (fsH ι) (q : ℤ) 1) n c s

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSegreArith
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def segreCoords {K : Type} [Fintype K] {ι : K → Type} {Ω : Type} [CommRing Ω] (y : (Σ k, ι k) → Ω) :
    Ix ((k : K) → ι k) → Ω :=
  fun p => ∏ k, y ⟨k, p.2 k⟩

def SegreArith.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ),
    IsArithVar (mCoordIdeal y) (D + 1) →
    IsArithVar (ι := GlobalTheory ((k : K) → ι k)) (coordIdeal ℤ (segreCoords y)) (D + 1)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsMonomialShift
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter

noncomputable section

def MonomialShift.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (a : K → ℕ) (A : HermLine ι) (P0 : Ideal (MRing ι)) (q τ n : ℕ),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y → (A.a = fun k => (a k : ℤ)) →
    P0 ≤ mCoordIdeal y → IsSemipositiveRel P0 (mCoordIdeal y) A → MonomialsBounded (mCoordIdeal y) A a →
    1 ≤ q → τ ≤ q * n →
    smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLatNm y A.a) τ ≤
      smallSectionCount (IsSmallH (mCoordIdeal y) y (HermLine.zcomb A (fsH ι) q 1))
        (chartLatNm y (HermLine.zcomb A (fsH ι) q 1).a) n

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPerturbSemipos
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def PerturbSemipos.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P0 P : Ideal (MRing ι)) (M : HermLine ι)
    (b a : ℤ),
    IsSemipositiveRel P0 P M → 0 ≤ b → 0 ≤ a → IsSemipositiveRel P0 P (HermLine.zcomb M (fsH ι) b a)

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNormalLocusRep
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

def NormalLocusRep.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    ∃ (df : K → ℕ) (f : MRing ι), IsMultiHomog f df ∧ f ∉ mCoordIdeal y ∧
      ∀ (a : K → ℤ) (τ : ℕ), ∀ s ∈ chartLatNm y a τ, ∀ z ∈ mcPts (mCoordIdeal y),
        eval z (map (Int.castRingHom ℂ) f) ≠ 0 →
        ∃ (dg dh : K → ℕ) (g h : MRing ι), IsMultiHomog g dg ∧ IsMultiHomog h dh ∧
          (∀ k, (dg k : ℤ) = dh k + τ * a k) ∧ aeval y g = s * aeval y h ∧
          eval z (map (Int.castRingHom ℂ) h) ≠ 0

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTwistMetric
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory NumberField

def TwistMetric.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (F : Type) [Field F] [NumberField F] [Algebra F Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : HermLine ι) (P0 : Ideal (MRing ι))
    (II : IntersectionSystem) (u : (F →+* ℂ) → ℝ),
    1 ≤ D → IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    P0 ≤ mCoordIdeal y → IsSemipositiveRel P0 (mCoordIdeal y) A → IsConjInvariantH A →
    (∀ z ∈ mcPts (mCoordIdeal y), ∃! sg : F →+* ℂ, LiesOver y sg z) →
    (∀ sg, u (ComplexEmbedding.conjugate sg) = u sg) → ∑ sg, u sg = 0 →
    ∃ c : ℝ, ∀ δ : ℝ, 0 < δ → ∃ A' : HermLine ι, A'.a = A.a ∧
      IsSemipositiveRel P0 (mCoordIdeal y) A' ∧ IsConjInvariantH A' ∧
      (∀ z ∈ mcPts (mCoordIdeal y), ∀ sg : F →+* ℂ, LiesOver y sg z →
        A'.h z = Real.exp (u sg + δ) * A.h z) ∧
      II K ι (mCoordIdeal y) (D + 1) (fun _ => A') ≤ II K ι (mCoordIdeal y) (D + 1) (fun _ => A) + c * δ

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsProjAvoidingForm
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

def ProjAvoidingForm.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (df : K → ℕ) (f : MRing ι),
    IsArithVar (mCoordIdeal y) (D + 1) → IsMultiHomog f df → f ∉ mCoordIdeal y →
    ∃ (e : K → ℕ) (L : Fin (D + 1) → MRing ι) (G : MvPolynomial (Fin (D + 1)) ℤ),
      (∀ k, 1 ≤ e k) ∧ (∀ j, IsMultiHomog (L j) e) ∧
      (∀ z ∈ mcPts (mCoordIdeal y), ∃ j, eval z (map (Int.castRingHom ℂ) (L j)) ≠ 0) ∧ G ≠ 0 ∧
      ∀ ζ : Fin (D + 1) → ℂ, eval ζ (map (Int.castRingHom ℂ) G) ≠ 0 →
        ∀ z ∈ mcPts (mCoordIdeal y),
          (∃ t : ℂ, ∀ j, eval z (map (Int.castRingHom ℂ) (L j)) = t * ζ j) →
          eval z (map (Int.castRingHom ℂ) f) ≠ 0

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFibreRepresentatives
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

def FibreRepresentatives.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (e : K → ℕ) (L : Fin (D + 1) → MRing ι),
    (∀ k, 1 ≤ e k) → (∀ j, IsMultiHomog (L j) e) →
    (∀ z ∈ mcPts (mCoordIdeal y), ∃ j, eval z (map (Int.castRingHom ℂ) (L j)) ≠ 0) →
    ∀ ζ : Fin (D + 1) → ℂ, ∃ S : Finset ((Σ k, ι k) → ℂ),
      (∀ z ∈ S, z ∈ mcPts (mCoordIdeal y) ∧
        ∃ t : ℂ, ∀ j, eval z (map (Int.castRingHom ℂ) (L j)) = t * ζ j) ∧
      ∀ z ∈ mcPts (mCoordIdeal y),
        (∃ t : ℂ, ∀ j, eval z (map (Int.castRingHom ℂ) (L j)) = t * ζ j) →
        ∃ z' ∈ S, ∃ r : K → ℂ, (∀ k, r k ≠ 0) ∧ z = fun p => r p.1 * z' p

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsScaledFSTopPos
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable def scaledFSH {K : Type} [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] : HermLine ι :=
  (fsH ι).tensor (constLine (-1))

def ScaledFSTopPos.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ)
    (II : IntersectionSystem),
    IsIntersectionSystem II → 1 ≤ d → IsArithVar P d → 0 < II K ι P d (fun _ => scaledFSH ι)

theorem scaledFSH_a {K : Type} [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] :
    (scaledFSH ι).a = fun _ => 1 := by
  funext k
  simp [scaledFSH, HermLine.tensor, fsH, HermLine.ofMetrics, constLine, HermLine.ofWeight]

theorem scaledFSH_h {K : Type} [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (z : (Σ k, ι k) → ℂ) :
    (scaledFSH ι).h z = (∏ k, (fsMetric (ι := ι k)).ρ (fun i => z ⟨k, i⟩)) * Real.exp 1 := by
  simp [scaledFSH, HermLine.tensor, fsH, HermLine.ofMetrics, constLine, HermLine.ofWeight]

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsKodairaSection
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def KodairaSection.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (M : HermLine ι) (P0 : Ideal (MRing ι)),
    1 ≤ D → IsArithVar (mCoordIdeal y) (D + 1) → Birational y → IsNefBigDatum P0 y D M →
    ∃ (k : ℕ) (e : Ω) (C : ℝ), 1 ≤ k ∧ 0 ≤ C ∧ e ≠ 0 ∧ e ∈ chartLat y ((k : ℤ) • M.a - 1) 1 ∧
      IsBoundedH (mCoordIdeal y) y (HermLine.zcomb M (fsH ι) k (-1)) 1 (Real.exp C) e

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsHeightsirationalHilb
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def BlockBirationalHilbert.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (y : (Σ k, ι k) → Ω) (k₀ : K),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → BlockBirational y k₀ → ∀ m : K → ℕ, ∃ c : ℕ, ∀ n : ℕ,
      GroundTheory.Heights₂.Heights.NumbersDVR.hilbFn ((mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ)))
          (fun k => if k = k₀ then (n : ℤ) else 0) ≤
        GroundTheory.Heights₂.Heights.NumbersDVR.hilbFn ((mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ)))
          (fun k => if k = k₀ then (n : ℤ) else m k) ∧
      GroundTheory.Heights₂.Heights.NumbersDVR.hilbFn ((mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ)))
          (fun k => if k = k₀ then (n : ℤ) else m k) ≤
        GroundTheory.Heights₂.Heights.NumbersDVR.hilbFn ((mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ)))
          (fun k => if k = k₀ then ((n + c : ℕ) : ℤ) else 0)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockResolutionSup
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory

noncomputable section

variable {D : ℕ} {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {Ω : Type} [Field Ω] [CharZero Ω]

def blockL2NormComplex (d : HSMBlockDatum D K ι Ω) (n : ℕ) (f : MRingOver ℂ ι) : ℝ :=
  Real.sqrt (∫ x, (‖eval (blockPt d x) f‖ / d.A.h (blockPt d x) ^ n) ^ 2 ∂d.dV)

def BlockResolutionSupBound.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (d : HSMBlockDatum D K ι Ω),
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ f : MRingOver ℂ ι, IsMultiHomog f (blockDeg d.k₀ n) →
      ∀ z ∈ mcPts (mCoordIdeal d.y),
        ‖eval z f‖ / d.A.h z ^ n ≤ C * (n : ℝ) ^ ((D : ℝ) / 2) * blockL2NormComplex d n f

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGridSeparation
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

def GridSeparation.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : HermLine ι),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y → IsSmoothHerm A →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℕ, ∃ Z : Finset ((Σ k, ι k) → ℂ),
      (∀ z ∈ Z, z ∈ mcPts (mCoordIdeal y)) ∧
      (∀ s ∈ chartLatNm y A.a τ, ∀ z ∈ Z, ∃ (dg dh : K → ℕ) (g h : MRing ι),
        IsMultiHomog g dg ∧ IsMultiHomog h dh ∧ (∀ k, (dg k : ℤ) = dh k + τ * A.a k) ∧
        aeval y g = s * aeval y h ∧ eval z (map (Int.castRingHom ℂ) h) ≠ 0) ∧
      ∀ u ∈ chartLatNm y A.a τ, u ≠ 0 → ∃ z ∈ Z, ∃ (dg dh : K → ℕ) (g h : MRing ι),
        IsMultiHomog g dg ∧ IsMultiHomog h dh ∧ (∀ k, (dg k : ℤ) = dh k + τ * A.a k) ∧
        aeval y g = u * aeval y h ∧ eval z (map (Int.castRingHom ℂ) h) ≠ 0 ∧
        Real.exp (-(C * ((τ : ℝ) + 1))) * A.h z ^ τ * ‖eval z (map (Int.castRingHom ℂ) h)‖ ≤
          ‖eval z (map (Int.castRingHom ℂ) g)‖

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSeparatedSmallCount
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory

noncomputable section

def SeparatedSmallCount.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : HermLine ι) (τ : ℕ) (b : ℝ),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y → 0 ≤ b →
    (∀ s : Ω, s ∈ chartLat y A.a τ → s ≠ 0 → ∀ c : ℝ, c < Real.exp (-b) →
      ¬ IsBoundedH (mCoordIdeal y) y A τ c s) →
    smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) τ ≤
      (Module.finrank ℤ (chartLat y A.a τ) : ℝ) * (b + Real.log 3)

section Inhabitant

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet

end Inhabitant

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsHilbFnValueSpan
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

section ValueSpan

variable {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]

def valueSpan (y : (Σ k, ι k) → Ω) (a : K → ℕ) : Submodule ℚ Ω :=
  Submodule.span ℚ {s | ∃ g : MRing ι, IsMultiHomog g a ∧ aeval y g = s}

end ValueSpan

def HilbFnValueSpan.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (y : (Σ k, ι k) → Ω) (a : K → ℕ),
    GroundTheory.Heights₂.Heights.NumbersDVR.hilbFn ((mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ)))
        (fun k => (a k : ℤ)) =
      (Module.finrank ℚ (valueSpan y a) : ℤ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsDefectMetricChange
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

variable {D : ℕ} {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ]

def HSMDatum.withMetric (d : HSMDatum D Ω κ) (m : ConeMetric ℂ (Ix κ)) (P0 : Ideal (MRing (GlobalTheory κ)))
    (hs : IsSmoothMetric m) (hc : IsConjInvariant m) (hle : P0 ≤ coordIdeal ℤ d.x)
    (hp : IsSemipositiveRel P0 (coordIdeal ℤ d.x) (HermLine.ofCone m)) : HSMDatum D Ω κ :=
  { d with m := m, P0 := P0, smooth := hs, conjInv := hc, normalForm_baseLattice_le_dualSpan_sup_line := hle, semipos := hp }

def DefectMetricChange.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (I : AllFam) (d : HSMDatum D Ω κ)
    (m₁ : ConeMetric ℂ (Ix κ)) (P0₁ : Ideal (MRing (GlobalTheory κ))) (hs : IsSmoothMetric m₁)
    (hc : IsConjInvariant m₁) (hle : P0₁ ≤ coordIdeal ℤ d.x)
    (hp : IsSemipositiveRel P0₁ (coordIdeal ℤ d.x) (HermLine.ofCone m₁)) (e : Fin (D + 1) → Ix κ),
    I.IsFamily → IsProjFrame d.x e →
    (fun n => hsDefect D (resChi (d.withMetric m₁ P0₁ hs hc hle hp)) (top I d.x m₁ D) n -
        hsDefect D (resChi d) (top I d.x d.m D) n) =o[atTop] pw D

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsZCombLimit
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def ZCombLimit.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A B : HermLine ι) (II : IntersectionSystem) (k : ℕ),
    IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → IsSmoothHerm A → IsSmoothHerm B →
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ p q : ℕ, 0 < p → 0 < q → (p : ℝ) / q < δ →
      |II K ι (mCoordIdeal y) (D + 1) (fun _ => HermLine.zcomb A B ((q : ℤ) - k * p) p) /
          (q : ℝ) ^ (D + 1) - II K ι (mCoordIdeal y) (D + 1) (fun _ => A)| < ε ∧
      |(genDeg (mCoordIdeal y) D (HermLine.zcomb A B ((q : ℤ) - k * p) p).a : ℝ) / (q : ℝ) ^ D -
          genDeg (mCoordIdeal y) D A.a| < ε

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionProduct
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def SectionProduct.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (A B C : HermLine ι) (n j τ : ℕ) (s t : Ω),
    (τ : ℤ) • C.a = (n : ℤ) • A.a + (j : ℤ) • B.a →
    (∀ z ∈ mcPts (mCoordIdeal y), C.h z ^ τ = A.h z ^ n * B.h z ^ j) →
    s ∈ chartLat y A.a n → t ∈ chartLat y B.a 1 →
    s * t ^ j ∈ chartLat y C.a τ ∧
      ∀ c c' : ℝ, IsBoundedH (mCoordIdeal y) y A n c s → IsBoundedH (mCoordIdeal y) y B 1 c' t →
        IsBoundedH (mCoordIdeal y) y C τ (c * c' ^ j) (s * t ^ j)

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
