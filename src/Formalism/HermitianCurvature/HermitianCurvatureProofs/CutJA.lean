module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedA
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LeftTypeAction
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LduDecompositionExists
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapAdInv
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsAdmissibleSplittingCharPairMulTwist

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJA
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA

open NumberField Formalism.FourierDecayAlt.P.CutMP

noncomputable section

section defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]

abbrev GFn (S : C.HidaSetting E Wp Wq) (v : Fin S.f) : Type := B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))

def smoothFormsPositiveCone (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) : Set (GFn S v) :=
  Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v)

def GfP (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (g : B.Mat S.G.k S.G.r) : ℝ :=
  Formalism.QuantumDeterminants.Gf S.G.k S.G.r (T v).base.z (T v).base.z' g

def mulG (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (ψ : ℝ → ℝ) (J : GFn S v) : GFn S v :=
  fun g => ((ψ (GfP S T v g) : ℝ) : ℂ) • J g

def CCg (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (A Bg : ℝ) (F : GFn S v) : Prop :=
  ∀ m : ℕ, B.InCC (A - Bg * m) m F

def CutCoef (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (Θ : (B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))) (d Bg : ℝ) : Prop :=
  ∀ Tm ∈ Θ, ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, ∃ Cb : ℝ, ∀ u w : List (B.Mat S.G.k S.G.r),
    (∀ X ∈ u, B.unitLie S.G.k S.G.r X) → (∀ X ∈ w, B.unitLie S.G.k S.G.r X) → u.length + w.length ≤ m →
    ∀ g ∈ B.GV S.G.k S.G.r, ε ≤ GfP S T v g →
      ‖B.dLR u w Tm.coef g‖ ≤ Cb * B.gN g ^ (d + Bg * m) ∧ ‖B.dLR u w Tm.coefAdj g‖ ≤ Cb * B.gN g ^ (d + Bg * m)

def IsAAOp (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (Θ : (B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))) : Prop :=
  B.SmoothCoef (B.GPos (T v).base) Θ ∧ B.Commutes (T v).base (B.GPos (T v).base) Θ

def LocCC (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (A Bg : ℝ) (J : GFn S v) : Prop :=
  J ∈ smoothFormsPositiveCone S T v ∧ ∀ δ : ℝ, 0 < δ → ∃ F : GFn S v, B.CkOn ⊤ (B.GV S.G.k S.G.r) F ∧ CCg S v A Bg F ∧
    ∀ x ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT, δ ≤ GfP S T v (B.gq (T v).base x) →
      J (B.gq (T v).base x) = B.JF (T v).base F (B.gq (T v).base x)

def applyL (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (Θs : List (B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))) (J : GFn S v) : GFn S v :=
  Θs.foldr (fun Θ J' => B.opApply Θ J') J

def adjL (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (Θs : List (B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))) (J : GFn S v) : GFn S v :=
  Θs.foldl (fun J' Θ => B.opAdj Θ J') J

end defs

def JABddStar : Prop :=
  ∀ (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r), 0 < P.TT → MA.IsModelLevel P (MA.DQ P) L →
    ∀ b ∈ Submonoid.closure (MA.bddSet P L), star b ∈ Submonoid.closure (MA.bddSet P L) ∧
      ∀ (ε : ℝ) (U V : M.Ty P → MA.SmQ P.r P.TT), 0 < ε →
        (∀ π q, MA.Gq P q < ε → MA.evQ P (U π) q = 0) →
        (∀ π, MeasureTheory.IntegrableOn (fun q => ‖MA.evQ P (U π) q‖ ^ 2) {q | ε ≤ MA.Gq P q} (MA.mu0 P.r P.TT)) →
        (∀ π, MeasureTheory.IntegrableOn (fun q => ‖MA.evQ P (V π) q‖ ^ 2) {q | ε ≤ MA.Gq P q} (MA.mu0 P.r P.TT)) →
        MA.ipA P U (MA.actA P b V) = MA.ipA P (MA.actA P (star b) U) V

def JAIsAdj : Prop :=
  ∀ (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r), 0 < P.TT → MA.IsModelLevel P (MA.DQ P) L →
    ∀ a ∈ Submonoid.closure (MA.hatSet P L ∪ MA.bddSet P L), MA.IsAdjA P a

def JAPhiOp : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))), IsFrame S T v e → ∀ φ : ℝ → ℝ, LE.SmoothLog φ →
      ∀ J ∈ smoothFormsPositiveCone S T v, mulG S T v φ J ∈ smoothFormsPositiveCone S T v ∧
        trJ S T v e (mulG S T v φ J) =
          fun π => MA.toSm (D.parOf S v) (fun q => (φ (MA.Gq (D.parOf S v) q) : ℂ)) * trJ S T v e J π

def JAStarOp : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (L : R.LevelData (MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) (D.parOf S v).r),
      IsFrame S T v e → IsGauge S T v e → MA.IsModelLevel (D.parOf S v) (MA.DQ (D.parOf S v)) L →
      ∀ a ∈ Submonoid.closure (MA.hatSet (D.parOf S v) L ∪ MA.bddSet (D.parOf S v) L), ∀ ts : List (ℂ × List (B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))), (∀ t ∈ ts, ∀ Θ ∈ t.2, IsAAOp S T v Θ) →
        (∀ J ∈ smoothFormsPositiveCone S T v, (∀ t ∈ ts, applyL S v t.2 J ∈ smoothFormsPositiveCone S T v ∧ adjL S v t.2 J ∈ smoothFormsPositiveCone S T v) ∧
          MA.actA (D.parOf S v) a (trJ S T v e J) = (ts.map fun t => t.1 • trJ S T v e (applyL S v t.2 J)).sum) →
        ∀ J ∈ smoothFormsPositiveCone S T v,
          MA.actA (D.parOf S v) (star a) (trJ S T v e J) = (ts.map fun t => (starRingEnd ℂ t.1) • trJ S T v e (adjL S v t.2 J)).sum

def JAGroupAdj : Prop :=
  ∃ Cc Cg : ℝ, 0 ≤ Cg ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))), IsFrame S T v e →
      ∀ (Θ : (B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))) (d Bg : ℝ), 0 ≤ d → Cg * ((S.G.r : ℝ) + 1) ≤ Bg → IsAAOp S T v Θ → CutCoef S T v Θ d Bg →
      ∀ ε : ℝ, 0 < ε → ∀ J₁ J₂ : GFn S v,
        LocCC S T v (B.AB S.G.k S.G.r + Cc * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r ^ 2 +
          6 * (S.G.r : ℝ) * ((B.opOrder Θ : ℝ) + 5) + d + 2 * Bg * ((B.opOrder Θ : ℝ) + 5)) Bg J₁ →
        LocCC S T v (B.AB S.G.k S.G.r + Cc * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r ^ 2 +
          6 * (S.G.r : ℝ) * ((B.opOrder Θ : ℝ) + 5) + d + 2 * Bg * ((B.opOrder Θ : ℝ) + 5)) Bg J₂ →
        (∀ x ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT, GfP S T v (B.gq (T v).base x) < ε → J₁ (B.gq (T v).base x) = 0) →
        B.opApply Θ J₁ ∈ smoothFormsPositiveCone S T v → B.opAdj Θ J₂ ∈ smoothFormsPositiveCone S T v →
        MA.ipA (D.parOf S v) (trJ S T v e (B.opApply Θ J₁)) (trJ S T v e J₂) =
          MA.ipA (D.parOf S v) (trJ S T v e J₁) (trJ S T v e (B.opAdj Θ J₂))

def JALocCC : Prop :=
  ∃ Cc Cg : ℝ, 0 ≤ Cg ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v,
      (∀ (F : GFn S v) (A Bg : ℝ), B.CkOn ⊤ (B.GV S.G.k S.G.r) F → (∀ m : ℕ, B.InCC A m F) →
        B.JF (T v).base F ∈ smoothFormsPositiveCone S T v → 0 ≤ Bg → LocCC S T v A Bg (B.JF (T v).base F)) ∧
      (∀ (Θ : (B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))) (d Bg A : ℝ) (J : GFn S v), 0 ≤ d → Cg * ((S.G.r : ℝ) + 1) ≤ Bg → IsAAOp S T v Θ →
        CutCoef S T v Θ d Bg →
        Cc * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r ^ 2 + 6 * (S.G.r : ℝ) * (B.opOrder Θ : ℝ) + d +
          2 * Bg * ((B.opOrder Θ : ℝ) + 1) ≤ A →
        LocCC S T v A Bg J → B.opApply Θ J ∈ smoothFormsPositiveCone S T v →
          LocCC S T v (A - d - 2 * Bg * (B.opOrder Θ : ℝ)) Bg (B.opApply Θ J)) ∧
      (∀ (Θ : (B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))) (d Bg A : ℝ) (J : GFn S v), 0 ≤ d → Cg * ((S.G.r : ℝ) + 1) ≤ Bg → IsAAOp S T v Θ →
        CutCoef S T v Θ d Bg →
        Cc * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r ^ 2 + 6 * (S.G.r : ℝ) * (B.opOrder Θ : ℝ) + d +
          2 * Bg * ((B.opOrder Θ : ℝ) + 1) ≤ A →
        LocCC S T v A Bg J → B.opAdj Θ J ∈ smoothFormsPositiveCone S T v →
          LocCC S T v (A - d - 2 * Bg * (B.opOrder Θ : ℝ)) Bg (B.opAdj Θ J)) ∧
      (∀ (φ : ℝ → ℝ) (Bg A : ℝ) (J : GFn S v), LE.SmoothLog φ → (∀ p, ∃ C, ∀ x, 0 < x → |LE.ld p φ x| ≤ C) →
        Cg * ((S.G.r : ℝ) + 1) ≤ Bg → LocCC S T v A Bg J → mulG S T v φ J ∈ smoothFormsPositiveCone S T v →
          LocCC S T v A Bg (mulG S T v φ J)) ∧
      (∀ (Bg A : ℝ) (J J' : GFn S v), 0 ≤ Bg → Cc * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r ^ 2 ≤ A →
        LocCC S T v A Bg J → LocCC S T v A Bg J' → LocCC S T v A Bg (J + J')) ∧
      (∀ (Bg A : ℝ) (c : ℂ) (J : GFn S v), LocCC S T v A Bg J → LocCC S T v A Bg (c • J)) ∧
      (∀ (Bg A A' : ℝ) (J : GFn S v), A' ≤ A → LocCC S T v A Bg J → LocCC S T v A' Bg J) ∧
      (∀ (Bg A ε : ℝ) (J : GFn S v) (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))), IsFrame S T v e → 0 ≤ Bg → 0 < ε →
        Cc * ((S.G.r : ℝ) + 1) ^ 2 * nDim S.G.k S.G.r + 5 * Bg ≤ A → LocCC S T v A Bg J →
        ∀ π, MeasureTheory.IntegrableOn (fun q => ‖MA.evQ (D.parOf S v) (trJ S T v e J π) q‖ ^ 2)
          {q | ε ≤ MA.Gq (D.parOf S v) q} (MA.mu0 (D.parOf S v).r (D.parOf S v).TT))

def JAFFStable : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (Θ : (B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))), IsAAOp S T v Θ → ∀ J ∈ smoothFormsPositiveCone S T v, B.opApply Θ J ∈ smoothFormsPositiveCone S T v ∧ B.opAdj Θ J ∈ smoothFormsPositiveCone S T v

end

end Formalism.FourierDecayAlt.P.CutMP.JA
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreCut
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

def CSec (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μ0 : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : Prop :=
  IsSection k r z z' μ0 ∧ ∀ ζ ζ' : ℂ, Tz k r z * Tz k r z' < Complex.normSq ζ → Tz k r z * Tz k r z' < Complex.normSq ζ' →
    NF.Stab k r z z' μ0 ζ = NF.Stab k r z z' μ0 ζ'

def GCoreSec : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → CSec P.k P.r Bs.z Bs.z' Bs.μsec →
    ∃ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e ∧
      ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)), FamR P Bs Dc Φ →
        ∀ (Y : ℝ) (a b : Fin 2) (ρ : M.Ty P),
          MA.toSm P (rawR P Bs.μsec e (Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (Y : ℂ) a b Φ) ρ) =
            MA.actA P (MA.QQr P (MA.DQ P) (Y : ℂ) a b) (fun ρ' => MA.toSm P (rawR P Bs.μsec e Φ ρ')) ρ

def SecExists : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → ∃ μ0, CSec P.k P.r Bs.z Bs.z' μ0

def SecMove : Prop := SecExists → GCoreSec → GCore

def trR {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : M.Ty P → MA.SmQ P.r P.TT :=
  fun ρ => MA.toSm P (rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ)

def FamLocal : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k →
    ∀ (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r))
      (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)), FamR P Bs Dc Φ →
    ∀ q : MA.Qp P.r P.TT, ∃ Φt : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π', ∃ V ∈ nhds q.1.2,
      ∀ ζ' ∈ V, (Φt : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1 (NF.muZ P.k P.r Bs.μsec ζ') = Φ q.1.1 (NF.muZ P.k P.r Bs.μsec ζ') ∧
        ∀ (Y : ℂ) (a b : Fin 2), (X.t Y a b Φt : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1 (NF.muZ P.k P.r Bs.μsec ζ') =
          Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) Y a b Φ q.1.1 (NF.muZ P.k P.r Bs.μsec ζ')

def GenTransfer : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → CSec P.k P.r Bs.z Bs.z' Bs.μsec →
    ∀ (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
      Q.IsActualLevel X d.L → Fr.IsStarLevel d.L → d.Rel → (∀ Y : ℂ, X.QQ Y = d.QQ Y) →
      ∃ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e ∧
        ∀ Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π',
          trR P Bs e (d.L.ζ.1 Φ) = MA.actA P (MA.zA P (MA.DQ P)) (trR P Bs e Φ) ∧
          trR P Bs e (d.L.ζi.1 Φ) = MA.actA P (MA.ziA P (MA.DQ P)) (trR P Bs e Φ) ∧
          trR P Bs e (d.L.ζb.1 Φ) = MA.actA P (MA.zbA P (MA.DQ P)) (trR P Bs e Φ) ∧
          trR P Bs e (d.L.ζbi.1 Φ) = MA.actA P (MA.zbiA P (MA.DQ P)) (trR P Bs e Φ) ∧
          trR P Bs e (d.L.GG.1 Φ) = MA.actA P (MA.ggA P (MA.DQ P)) (trR P Bs e Φ) ∧
          trR P Bs e (d.L.GGi.1 Φ) = MA.actA P (MA.ggiA P (MA.DQ P)) (trR P Bs e Φ) ∧
          trR P Bs e (d.L.nab.1 Φ) = MA.actA P (MA.nabA P (MA.DQ P)) (trR P Bs e Φ) ∧
          trR P Bs e (d.L.nabs.1 Φ) = MA.actA P (MA.nabsA P (MA.DQ P)) (trR P Bs e Φ) ∧
          (∀ f : M.Ty P → ℂ, trR P Bs e ((d.κ f).1 Φ) = MA.actA P (MA.kap P (MA.DQ P) f) (trR P Bs e Φ)) ∧
          (∀ l ∈ Finset.Icc 1 (P.k - 1),
            trR P Bs e ((d.SS l).1 Φ) = MA.actA P (MA.SS P (MA.DQ P) l) (trR P Bs e Φ)) ∧
          ∀ l ∈ Finset.Icc 1 (P.k - 1),
            trR P Bs e ((star (d.SS l)).1 Φ) = MA.actA P (star (MA.SS P (MA.DQ P) l)) (trR P Bs e Φ)

def GenTransferQQ : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → CSec P.k P.r Bs.z Bs.z' Bs.μsec →
    ∀ X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π',
      ∃ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e ∧
        ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (Y : ℂ) (a b : Fin 2),
          trR P Bs e (X.t Y a b Φ) = MA.actA P (MA.QQr P (MA.DQ P) Y a b) (trR P Bs e Φ)

def ModelLocal : Prop :=
  ∀ (P : M.Par) (f g : M.Ty P → MA.SmQ P.r P.TT) (c : Fin P.r → ℂ) (V : Set ℂ), IsOpen V →
    (∀ ρ (q : MA.Qp P.r P.TT), q.1.1 = c → q.1.2 ∈ V → (f ρ : MA.Qp P.r P.TT → ℂ) q = (g ρ : MA.Qp P.r P.TT → ℂ) q) →
    ∀ (Y : ℂ) (a b : Fin 2) ρ (q : MA.Qp P.r P.TT), q.1.1 = c → q.1.2 ∈ V →
      (MA.actA P (MA.QQr P (MA.DQ P) Y a b) f ρ : MA.Qp P.r P.TT → ℂ) q =
        (MA.actA P (MA.QQr P (MA.DQ P) Y a b) g ρ : MA.Qp P.r P.TT → ℂ) q

def RadSpSmooth : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k →
    ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e →
    ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') ρ,
      rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ ∈ MA.smSub P.r P.TT

def GenToQQ : Prop := RadSpSmooth → GenTransfer → GenTransferQQ

def AsmSec : Prop := FamLocal → GenTransferQQ → ModelLocal → RadSpSmooth → GRawSmooth → GQLFam → GCoreSec

def GCoreOfCut : Prop :=
  SecExists → SecMove → FamLocal → GenTransfer → GenToQQ → ModelLocal → RadSpSmooth → GRawSmooth → GQLFam → AsmSec → GCore

theorem gauge_construction_of_truncation : GCoreOfCut := fun hSE hSM hFL hGT hGQ hML hRS hRaw hQL hA =>
  hSM hSE (hA hFL (hGQ hRS hGT) hML hRS hRaw hQL)

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellDiagonalMap
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

set_option linter.unusedSimpArgs false

noncomputable section

namespace Formalism.FourierDecayAlt.P.BigCellDiagonalMap

variable {k j ρ : ℕ}

theorem leviElement_mul_mMap (W Z : Matrix (Fin j) (Fin j) ℂ) (γ : B.Mat k ρ) (hW : IsUnit W.det) :
    muP k j ρ W * mMap k j ρ Z γ = mMap k j ρ (Wᴴ⁻¹ * Z) γ := by
  unfold mMap muP
  rw [Ux3.block3_mul]
  have h13 : W * (Zᴴ⁻¹ * G.wMat j) = (Wᴴ⁻¹ * Z)ᴴ⁻¹ * G.wMat j := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hW, Matrix.mul_assoc]
  have h31 : G.wMat j * Wᴴ⁻¹ * G.wMat j * (G.wMat j * Z) = G.wMat j * (Wᴴ⁻¹ * Z) := by
    rw [Matrix.mul_assoc, Ux4.w_w_mul, Matrix.mul_assoc]
  congr 1 <;> simp [h13, h31]

theorem leviElement_nset (p : Matrix (Fin j) (Fin j) ℂ) (hp : Formalism.DoubleCosetMeasures.IsUpUni p) : muP k j ρ p ∈ Nset k (j + ρ) := by
  have hdet : p.det ≠ 0 := by rw [Formalism.DoubleCosetMeasures.isUpUni_det ℂ hp]; exact one_ne_zero
  refine ⟨(Formalism.FourierDecayAlt.P.slice_membership k j ρ).2.1 p hdet, ?_, ?_⟩
  · intro a i hai
    obtain ⟨x, rfl⟩ := (eB k j ρ).surjective i
    obtain ⟨y, hy⟩ := (eB k j ρ).surjective (eI k (j + ρ) a)
    unfold muP
    rw [← hy, Ux3.block3_apply]
    simp only [(eB k j ρ).apply_eq_iff_eq]
    have hv := congrArg Fin.val hy
    have ha := a.isLt
    simp only [eI] at hv
    rw [← hv] at hai
    rcases x with ((x | x) | x) <;> rcases y with ((y | y) | y) <;>
      simp only [Ux3.block_index_first_val, Ux3.block_index_middle_val, Ux3.block_index_last_val] at hv hai
    all_goals first
      | (exfalso; have := x.isLt; have := y.isLt; omega)
      | (simp [Matrix.one_apply, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl,
          Matrix.fromCols_apply_inr]; done)
      | skip

    simp only [Matrix.fromBlocks_apply₁₁, Sum.inl.injEq]
    rcases eq_or_lt_of_le hai with h | h
    · have : x = y := Fin.ext h.symm
      subst this; simp [hp.2]
    · have hne : x ≠ y := fun e => by subst e; omega
      rw [if_neg hne]
      exact hp.1 (show y < x from h)
  · intro i c hc1 hc2 hi
    obtain ⟨x, rfl⟩ := (eB k j ρ).surjective i
    obtain ⟨y, rfl⟩ := (eB k j ρ).surjective c
    unfold muP
    rw [Ux3.block3_apply]
    simp only [(eB k j ρ).apply_eq_iff_eq]
    rcases x with ((x | x) | x) <;> rcases y with ((y | y) | y) <;>
      simp only [Ux3.block_index_first_val, Ux3.block_index_middle_val, Ux3.block_index_last_val] at hc1 hc2 hi <;>
      first
      | (simp [Matrix.one_apply, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl,
          Matrix.fromCols_apply_inr]; done)
      | (exfalso; have := x.isLt; have := y.isLt; omega)

def eW (k : ℕ) : Fin (2 * 0 + k + 1) ≃ Fin (k + 1) := finCongr (by omega)

def muOf (γ : B.Mat k 0) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ := Matrix.reindex (eW k) (eW k) γ

theorem hb_eq (k : ℕ) : Hb k = Matrix.reindex (eW k) (eW k) (Hpk k 0) := by
  ext i j
  simp only [Hb, Hpk, eW, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.diagonal_apply, finCongr_symm,
    finCongr_apply, Fin.coe_cast, Fin.ext_iff, Fin.val_last]
  split_ifs <;> first | rfl | omega

theorem muOf_mem (γ : B.Mat k 0) (hγ : γ ∈ B.GV k 0) : (muOf γ)ᴴ * Hb k * muOf γ = Hb k := by
  have h : γᴴ * Hpk k 0 * γ = Hpk k 0 := hγ
  rw [hb_eq]
  simp only [muOf, Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, h]

theorem inv_diag {r : ℕ} (v : Fin r → ℂ) (hv : ∀ a, v a ≠ 0) :
    (Matrix.diagonal v)⁻¹ = Matrix.diagonal (fun a => (v a)⁻¹) := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  exact inv_mul_cancel₀ (hv a)

theorem mMap_diag (r : ℕ) (d : Fin r → ℂ) (hd : ∀ a, d a ≠ 0) (γ : B.Mat k 0) :
    (mMap k r 0 (Matrix.diagonal d) γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) =
      bigCell k r d (muOf γ) := by
  ext i l
  obtain ⟨x, rfl⟩ := (eB k r 0).surjective i
  obtain ⟨y, rfl⟩ := (eB k r 0).surjective l
  unfold mMap
  rw [Matrix.diagonal_conjTranspose, inv_diag (star d) (fun a => by simpa [Pi.star_apply] using hd a), Ux3.block3_apply]
  have v1 := @Ux3.block_index_first_val k r 0
  have v2 := @Ux3.block_index_middle_val k r 0
  have v3 := @Ux3.block_index_last_val k r 0
  rcases x with ((x | x) | x) <;> rcases y with ((y | y) | y) <;>
    simp only [bigCell, v1, v2, v3, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl,
      Matrix.fromCols_apply_inr, Matrix.zero_apply]
  all_goals
    have hx := x.isLt
    have hy := y.isLt
    simp only [Fin.ext_iff, v1, v2, v3, esI, G.wMat, Matrix.of_apply, Matrix.diagonal_mul,
      Matrix.mul_diagonal, Ring.inverse_eq_inv', Pi.star_apply, Fin.val_rev, Pi.inv_apply, Complex.star_def, mul_one,
      one_mul, mul_zero, zero_mul]
    split_ifs <;> first
      | rfl
      | (exfalso; omega)
      | (congr 1; ext; simp only [Fin.val_mk]; omega)
      | (congr 2; ext; simp only [Fin.val_mk]; omega)
      | (intro h; exfalso; omega)
      | (simp; done)
      | (simp only [mul_one]; congr 3; ext; simp only [Fin.val_mk]; omega)
      | (simp only [muOf, eW, Matrix.reindex_apply, Matrix.submatrix_apply]; congr 1 <;> (ext; simp))
      | skip

theorem dmin_lead {k r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (l : ℕ) (hl : l ≤ r) : Dmin k r z z' g ⟨l, by omega⟩ = Formalism.FourierDecayAlt.S3.lead (Zh k r 0 g) l hl := by
  unfold Dmin Formalism.FourierDecayAlt.S3.lead
  congr 1
  ext a b
  simp only [Matrix.submatrix_apply]
  rw [Ux3.zhat_apply_low]
  · rfl
  · simp; omega
  · simp; omega

theorem cellDecomp : BigCellDecomposition.CellDecomp := by
  intro k r z z' g hg hD
  have hDl : ∀ (l : ℕ) (hl : l ≤ r), Formalism.FourierDecayAlt.S3.lead (Zh k r 0 g) l hl ≠ 0 := fun l hl => by
    rw [← dmin_lead z z' g l hl]; exact hD ⟨l, by omega⟩ hl
  have hDj : DjU k r 0 g ≠ 0 := by
    have h := Formalism.FourierDecayAlt.P.hat_z_minimum_degree k r 0 z z' g
    rw [← h]; exact hD ⟨r, by omega⟩ le_rfl
  obtain ⟨x, x', Z, γ, _hZ, hγ, hgeq⟩ := Ux3.bigCell_exists (k := k) (j := r) (ρ := 0) g hg hDj
  have hZh : Zh k r 0 g = Z := by rw [hgeq]; exact Formalism.FourierDecayAlt.P.hat_z_on_slice k r 0 x x' Z γ
  have hDZ : ∀ (l : ℕ) (hl : l ≤ r), Formalism.FourierDecayAlt.S3.lead Z l hl ≠ 0 := by rw [← hZh]; exact hDl
  obtain ⟨L, U, d, hL, hU, hLDU, hlead⟩ :=
    Formalism.FourierDecayAlt.P.ldu_decomposition_exists ℂ r Z (fun l hl => (hDZ l hl.le).isUnit)
  have hd : ∀ a, d a ≠ 0 := fun a h0 => by
    have h1 := hlead a.val a.isLt
    rw [h0, zero_mul] at h1
    exact hDZ (a.val + 1) a.isLt h1
  have hLh : Formalism.DoubleCosetMeasures.IsUpUni Lᴴ := by
    refine ⟨fun i j hij => ?_, fun a => ?_⟩
    · rw [Matrix.conjTranspose_apply, hL.1 hij, star_zero]
    · rw [Matrix.conjTranspose_apply, hL.2 a, star_one]
  have hLu : IsUnit L.det := by rw [Formalism.DoubleCosetMeasures.isLowUni_det ℂ hL]; exact isUnit_one
  have hLhu : IsUnit Lᴴ.det := by rw [Formalism.DoubleCosetMeasures.isUpUni_det ℂ hLh]; exact isUnit_one
  have hP : muP k r 0 Lᴴ ∈ Nset k (r + 0) := leviElement_nset _ hLh
  have hPu : IsUnit (muP k r 0 Lᴴ).det := Ux3.gv_det hP.1
  have h1 : muP k r 0 Lᴴ * mMap k r 0 Z γ = mMap k r 0 (Matrix.diagonal d) γ * muP k r 0 U := by
    rw [leviElement_mul_mMap _ _ _ hLhu, Ux4.mMap_mul_muP, hLDU, Matrix.conjTranspose_conjTranspose, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hLu, Matrix.one_mul]
  have key : mMap k r 0 Z γ = (muP k r 0 Lᴴ)⁻¹ * (mMap k r 0 (Matrix.diagonal d) γ * muP k r 0 U) := by
    rw [← h1, Matrix.nonsing_inv_mul_cancel_left _ _ hPu]
  refine ⟨muP k r 0 Lᴴ * Rn k r 0 x, WeylGroupFacts.mem_n_mul hP (Ux3.rn_nset x),
    muP k r 0 U * Rn k r 0 x', WeylGroupFacts.mem_n_mul (leviElement_nset _ hU) (Ux3.rn_nset x'), d, hd, muOf γ, muOf_mem γ hγ, ?_⟩
  rw [hgeq, key, ← mMap_diag r d hd γ, Matrix.mul_inv_rev]
  simp only [Matrix.mul_assoc]

end Formalism.FourierDecayAlt.P.BigCellDiagonalMap

namespace Formalism.FourierDecayAlt.P

theorem big_cell_decomposition : BigCellDecomposition.CellDecomp := by
  exact BigCellDiagonalMap.cellDecomp

theorem psiOnto_true : Formalism.FourierDecayAlt.JF.PsiOnto := jf_psiOnto_of_cellDecomp BigCellDiagonalMap.cellDecomp

end Formalism.FourierDecayAlt.P
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHat
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField

noncomputable section

section model

variable (P : M.Par)

def RhM (L : R.LevelData (MA.A P (MA.DQ P)) P.r) (y : ℂ) : MA.A P (MA.DQ P) :=
  L.Drb * (MA.t21 P (MA.DQ P) y * L.Ar y + MA.t22 P (MA.DQ P) y * L.Br y)

def RhvM (L : R.LevelData (MA.A P (MA.DQ P)) P.r) (y : ℂ) : MA.A P (MA.DQ P) :=
  L.Dr * (MA.t12 P (MA.DQ P) y * L.Avr y + MA.t22 P (MA.DQ P) y * L.Bvr y)

def xInvM (y : ℂ) : MA.A P (MA.DQ P) := MA.kap P (MA.DQ P) fun π => (M.xC P π y)⁻¹

def SSn (L : R.LevelData (MA.A P (MA.DQ P)) P.r) (l : ℕ) : MA.A P (MA.DQ P) :=
  L.Drb * L.Dri * MA.SS P (MA.DQ P) l

def RegY (y : ℂ) : Prop := ∀ π : M.Ty P, M.xC P π y ≠ 0

end model

def lagC {m : ℕ} (ν : Fin m → ℝ) (j : Fin m) (y : ℂ) : ℂ :=
  ∏ i ∈ Finset.univ.erase j, (y - (ν i : ℂ)) / ((ν j : ℂ) - (ν i : ℂ))

section defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]

def HatOK (Cc : ℝ) (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (Θ : B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))) : Prop :=
  B.SmoothCoef (B.GPos (T v).base) Θ ∧ B.Commutes (T v).base (B.GPos (T v).base) Θ ∧
    GlobCoef Θ (Cc * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r) ∧ (B.opOrder Θ : ℝ) ≤ Cc * nDim S.G.k S.G.r

def IsGaugeQQ (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) : Prop :=
  ∀ (Dc : (Fin (D.parOf S v).r → ℂ) → Set (Q.Mx (D.parOf S v).k (D.parOf S v).r))
    (Φ : Q.Fn (D.parOf S v).k (D.parOf S v).r (Wq (S.pl v) →L[ℂ] Wp (S.pl v))),
    Gauge.FamR (D.parOf S v) (T v).base Dc Φ →
    ∀ (Y : ℝ) (a b : Fin 2) (ρ : M.Ty (D.parOf S v)),
      MA.toSm (D.parOf S v) (Gauge.rawR (D.parOf S v) (T v).base.μsec e
          (Q.QL (D.parOf S v).k (D.parOf S v).r (T v).base.z (T v).base.z' (Fin.last (D.parOf S v).r) (Y : ℂ) a b Φ) ρ) =
        MA.actA (D.parOf S v) (MA.QQr (D.parOf S v) (MA.DQ (D.parOf S v)) (Y : ℂ) a b)
          (fun ρ' => MA.toSm (D.parOf S v) (Gauge.rawR (D.parOf S v) (T v).base.μsec e Φ ρ')) ρ

end defs

def ResidueSplittingModelAlgebra : Prop :=
  ∀ (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r), MA.IsModelLevel P (MA.DQ P) L → ∀ y : ℂ, RegY P y →
    L.R0 y = xInvM P y * RhM P L y -
      ∑ l ∈ Finset.Icc 1 (P.k - 1),
        xInvM P y * SSn P L l * MA.kap P (MA.DQ P) (fun π => M.xEx P {l} π y) * L.Ahat y

def MirrorResidueSplittingModelAlgebra : Prop :=
  ∀ (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r), MA.IsModelLevel P (MA.DQ P) L → ∀ y : ℂ, RegY P y →
    L.R0v y = xInvM P y * RhvM P L y -
      ∑ l ∈ Finset.Icc 1 (P.k - 1),
        xInvM P y * MA.kap P (MA.DQ P) (fun π => M.xEx P {l} π y) * star (SSn P L l) * L.Ahatv y

def JDHatLagrange : Prop :=
  ∀ (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r) (ν : Fin (P.r + 2) → ℝ), Function.Injective ν → ∀ y : ℂ,
    L.R0 y = ∑ j, lagC ν j y • L.R0 (ν j) ∧ L.R0v y = ∑ j, lagC ν j y • L.R0v (ν j)

def JDHatNodes : Prop :=
  ∀ P : M.Par, ∃ ν : Fin (P.r + 2) → ℝ, Function.Injective ν ∧ ∀ j, RegY P (ν j)

def JDOpA : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ Cc : ℝ, K ≤ Cc → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
      (L : R.LevelData (MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) (D.parOf S v).r),
      IsFrame S T v e → MA.IsModelLevel (D.parOf S v) (MA.DQ (D.parOf S v)) L → ∀ y : ℂ,
      ∃ Θ Θv : B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)), HatOK Cc S T v Θ ∧ HatOK Cc S T v Θv ∧
        ∀ J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v),
          trJ S T v e (B.opApply Θ J) = MA.actA (D.parOf S v) (L.Ahat y) (trJ S T v e J) ∧
          trJ S T v e (B.opApply Θv J) = MA.actA (D.parOf S v) (L.Ahatv y) (trJ S T v e J)

def JDOpR : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ Cc : ℝ, K ≤ Cc → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
      (L : R.LevelData (MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) (D.parOf S v).r),
      IsFrame S T v e → IsGaugeQQ S T v e → MA.IsModelLevel (D.parOf S v) (MA.DQ (D.parOf S v)) L → ∀ y : ℝ,
      ∃ Θ Θv : B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)), HatOK Cc S T v Θ ∧ HatOK Cc S T v Θv ∧
        ∀ J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v),
          trJ S T v e (B.opApply Θ J) = MA.actA (D.parOf S v) (RhM (D.parOf S v) L y) (trJ S T v e J) ∧
          trJ S T v e (B.opApply Θv J) = MA.actA (D.parOf S v) (RhvM (D.parOf S v) L y) (trJ S T v e J)

section gen

variable (P : M.Par)

theorem jdh_actA_one (f : M.Ty P → MA.SmQ P.r P.TT) : MA.actA P 1 f = f := by
  funext π
  show ∑ π', ((1 : MA.A P (MA.DQ P)) π π').1 (f π') = f π
  rw [Finset.sum_eq_single π (fun π' _ h => by rw [Matrix.one_apply_ne (Ne.symm h)]; rfl)
    (fun h => absurd (Finset.mem_univ π) h), Matrix.one_apply_eq]
  rfl

theorem jdh_actA_zeroR (a : MA.A P (MA.DQ P)) : MA.actA P a 0 = 0 := by
  funext π
  show ∑ π', (a π π').1 0 = 0
  exact Finset.sum_eq_zero fun π' _ => map_zero _

theorem jdh_actA_addR (a : MA.A P (MA.DQ P)) (x y : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P a (x + y) = MA.actA P a x + MA.actA P a y := by
  funext π
  show ∑ π', (a π π').1 (x π' + y π') = ∑ π', (a π π').1 (x π') + ∑ π', (a π π').1 (y π')
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => map_add _ _ _

theorem jdh_actA_listsum {ι : Type} (a : MA.A P (MA.DQ P)) (l : List ι) (g : ι → M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P a (l.map g).sum = (l.map fun i => MA.actA P a (g i)).sum := by
  induction l with
  | nil => simp only [List.map_nil, List.sum_nil]; exact jdh_actA_zeroR P a
  | cons i l ih => simp only [List.map_cons, List.sum_cons]; rw [jdh_actA_addR, ih]

theorem jdh_kap_mem (L : R.LevelData (MA.A P (MA.DQ P)) P.r) (g : M.Ty P → ℂ) :
    MA.kap P (MA.DQ P) g ∈ Submonoid.closure (MA.bddSet P L) :=
  Submonoid.subset_closure (Or.inl (Or.inl (Or.inr ⟨g, rfl⟩)))

theorem jdh_SSn_mem (L : R.LevelData (MA.A P (MA.DQ P)) P.r) (l : ℕ) (hl : l ∈ Finset.Icc 1 (P.k - 1)) :
    SSn P L l ∈ Submonoid.closure (MA.bddSet P L) :=
  Submonoid.subset_closure (Or.inl (Or.inr ⟨l, Finset.mem_Icc.1 hl, rfl⟩))

theorem jdh_SSns_mem (L : R.LevelData (MA.A P (MA.DQ P)) P.r) (l : ℕ) (hl : l ∈ Finset.Icc 1 (P.k - 1)) :
    star (SSn P L l) ∈ Submonoid.closure (MA.bddSet P L) :=
  Submonoid.subset_closure (Or.inr ⟨l, Finset.mem_Icc.1 hl, rfl⟩)

theorem jdh_smul_eq (c : ℂ) (a : MA.A P (MA.DQ P)) : c • a = MA.kap P (MA.DQ P) (fun _ => c) * a := by
  rw [Algebra.smul_def, ← (MA.kap P (MA.DQ P)).commutes c]
  rfl

end gen

section realise

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]
  {Cc : ℝ} {S : C.HidaSetting E Wp Wq} {T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))}
  {v : Fin S.f} {e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))}
  {L : R.LevelData (MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) (D.parOf S v).r}


variable (Cc S T v e L) in
def HReal (X : MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) : Prop :=
  ∃ ts : List (MA.A (D.parOf S v) (MA.DQ (D.parOf S v)) × B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))),
    (∀ t ∈ ts, t.1 ∈ Submonoid.closure (MA.bddSet (D.parOf S v) L) ∧ HatOK Cc S T v t.2) ∧
    ∀ J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v),
      MA.actA (D.parOf S v) X (trJ S T v e J) =
        (ts.map fun t => MA.actA (D.parOf S v) t.1 (trJ S T v e (B.opApply t.2 J))).sum

theorem hReal_op {X : MA.A (D.parOf S v) (MA.DQ (D.parOf S v))} (Θ : B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (hΘ : HatOK Cc S T v Θ)
    (h : ∀ J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v),
      trJ S T v e (B.opApply Θ J) = MA.actA (D.parOf S v) X (trJ S T v e J)) :
    HReal Cc S T v e L X := by
  refine ⟨[(1, Θ)], fun t ht => ?_, fun J hJ => ?_⟩
  · rw [List.mem_singleton] at ht
    subst ht
    exact ⟨Submonoid.one_mem _, hΘ⟩
  · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [jdh_actA_one, h J hJ]

theorem hReal_zero : HReal Cc S T v e L 0 :=
  ⟨[], fun t ht => absurd ht List.not_mem_nil, fun J _ => by
    simp only [List.map_nil, List.sum_nil]; exact Gauge.actA_zero _ _⟩

theorem hReal_add {X Y : MA.A (D.parOf S v) (MA.DQ (D.parOf S v))} (hX : HReal Cc S T v e L X)
    (hY : HReal Cc S T v e L Y) : HReal Cc S T v e L (X + Y) := by
  obtain ⟨ts, hts, hJ⟩ := hX
  obtain ⟨ts', hts', hJ'⟩ := hY
  refine ⟨ts ++ ts', fun t ht => ?_, fun J hJJ => ?_⟩
  · rcases List.mem_append.1 ht with h | h
    · exact hts t h
    · exact hts' t h
  · rw [Gauge.actA_add, hJ J hJJ, hJ' J hJJ, List.map_append, List.sum_append]

theorem hReal_mul {b X : MA.A (D.parOf S v) (MA.DQ (D.parOf S v))}
    (hb : b ∈ Submonoid.closure (MA.bddSet (D.parOf S v) L)) (hX : HReal Cc S T v e L X) :
    HReal Cc S T v e L (b * X) := by
  obtain ⟨ts, hts, hJ⟩ := hX
  refine ⟨ts.map fun t => (b * t.1, t.2), fun t ht => ?_, fun J hJJ => ?_⟩
  · obtain ⟨t', ht', rfl⟩ := List.mem_map.1 ht
    exact ⟨Submonoid.mul_mem _ hb (hts t' ht').1, (hts t' ht').2⟩
  · rw [Gauge.actA_mul, hJ J hJJ, jdh_actA_listsum, List.map_map]
    congr 1
    apply List.map_congr_left
    intro t _
    simp only [Function.comp_apply]
    rw [Gauge.actA_mul]

theorem hReal_sum {ι : Type} (s : Finset ι) (X : ι → MA.A (D.parOf S v) (MA.DQ (D.parOf S v)))
    (h : ∀ i ∈ s, HReal Cc S T v e L (X i)) : HReal Cc S T v e L (∑ i ∈ s, X i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact hReal_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact hReal_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem hReal_smul (c : ℂ) {X : MA.A (D.parOf S v) (MA.DQ (D.parOf S v))} (hX : HReal Cc S T v e L X) :
    HReal Cc S T v e L (c • X) := by
  rw [jdh_smul_eq]
  exact hReal_mul (jdh_kap_mem _ L _) hX

theorem hReal_sub {X Y : MA.A (D.parOf S v) (MA.DQ (D.parOf S v))} (hX : HReal Cc S T v e L X)
    (hY : HReal Cc S T v e L Y) : HReal Cc S T v e L (X - Y) := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ Y]
  exact hReal_add hX (hReal_smul _ hY)

end realise

end

end Formalism.FourierDecayAlt.P.CutMP
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDCCLower
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

theorem class_lower_decay_holds : JDCCLower := by
  intro k r Wp Wq _ _ _ _ _ _ Θ d A hd hG F hF hFA
  have hO : IsOpen (∅ : Set (B.Mat k r)) := isOpen_empty
  have hcov : ∀ g ∈ B.GV k r, g ∈ (∅ : Set (B.Mat k r)) ∨ g ∈ B.GV k r := fun g hg => Or.inr hg
  have hΦck : ∀ T ∈ Θ, B.CkOn ⊤ (B.GV k r) (B.Rw T.word F) := by
    intro T hT
    rw [← Dw_wR]
    apply CkOn_Dw (fun x hx => lie_LR (u := []) (by simp) T.word_lie x (by simpa [wL] using hx))
    simpa using hF
  have hop : B.opApply Θ F = fun g => (Θ.map fun T => ap T.coef (B.Rw T.word F) g).sum := rfl
  refine ⟨?_, fun m => ?_⟩
  · rw [hop]
    clear hop
    induction Θ with
    | nil => simpa using (CkOn_zero : B.CkOn ⊤ (B.GV k r) (fun _ => (0 : Wq →L[ℂ] Wp)))
    | cons T Θ ih =>
      have h1 : B.CkOn ⊤ (B.GV k r) (ap T.coef (B.Rw T.word F)) :=
        Pr.ck hO hcov ⟨(hG T (by simp)).1, hΦck T (by simp), fun g _ hg => by simp at hg⟩
      have h2 := ih (fun S hS => hG S (by simp [hS])) (fun S hS => hΦck S (by simp [hS]))
      simpa using CkOn_add h1 h2
  · rw [hop]
    refine InCC_opsum Θ (fun T => ap T.coef (B.Rw T.word F)) ?_
    intro T hT
    obtain ⟨hc1, -, hcb⟩ := hG T hT
    obtain ⟨C, hC⟩ := hcb m
    obtain ⟨c, hc⟩ : B.InCC (A - d + d) m (B.Rw T.word F) := by
      rw [sub_add_cancel]; exact InCC_Rw T.word_lie (hFA _)
    exact ⟨_, prodBound hO hcov (sCkOn_mono le_top hc1)
      (fun u v hu hv hl g hg _ => (hC u v hu hv hl g hg).1) hc (fun g _ hg => by simp at hg)⟩

end

end Formalism.FourierDecayAlt.P.CutMP
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGaugeGQLFam
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge

theorem quadratic_local_family_holds : GQLFam := by
  intro Wp Wq _ _ _ _ _ _ P Bs _ _ Dc Φ hF Y a b
  obtain ⟨hO, hD, hM, hS, hFF⟩ := hF
  refine ⟨hO, hD, hM, ?_, ?_⟩
  · exact Formalism.FourierDecayAlt.P.transfer_joint_smooth _ _ _ _ _ _ _ Φ (Y : ℂ) a b hO hS
  · intro c hc
    exact Formalism.FourierDecayAlt.P.operator_preserves_fusion_forms _ _ _ _ _ _ _ _ _ _ (Y : ℂ) a b Bs.z_mem Bs.z'_mem (hD c hc) _ (hFF c hc)

end Formalism.FourierDecayAlt.P.CutMP.Gauge
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnCVLocal
open Formalism.FourierDecayAlt
open Formalism.REAL Formalism.QuantumDeterminants

namespace Formalism.FourierDecayAlt.P.CutMP.En

theorem rw_congr {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {U : Set (B.Mat k r)}
    (hU : IsOpen U) {f₁ f₂ : B.Mat k r → E} (he : ∀ x ∈ U, x ∈ B.GV k r → f₁ x = f₂ x) :
    ∀ w : List (B.Mat k r), (∀ X ∈ w, B.inLie k r X) → ∀ x ∈ U, x ∈ B.GV k r → B.Rw w f₁ x = B.Rw w f₂ x
  | [], _, x, hx, hxG => he x hx hxG
  | X :: w, hw, x, hx, hxG => by
    show RdV X (B.Rw w f₁) x = RdV X (B.Rw w f₂) x
    exact Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.rdV_congr hU hx hxG (hw X (by simp))
      (rw_congr hU he w (fun Y hY => hw Y (by simp [hY])))

theorem coefficient_vector_locality : CVLocal := by
  intro k r E _ _ U f₁ f₂ Y hU h₁ h₂ he g hg
  obtain ⟨L, hL, hCV⟩ := Formalism.FourierDecayAlt.P.capelli_word_sum k r Y
  rw [hCV E (U ∩ B.GV k r) f₁ h₁ g hg hg.2, hCV E (U ∩ B.GV k r) f₂ h₂ g hg hg.2]
  congr 1
  refine List.map_congr_left fun cw hcw => ?_
  rw [rw_congr hU (fun x hx hxG => he x ⟨hx, hxG⟩) cw.2 (fun X hX => ((hL cw hcw).1 X hX).1) g hg.1 hg.2]

end Formalism.FourierDecayAlt.P.CutMP.En
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliDetAdInvariant
theorem Formalism.FourierDecayAlt.P.capelli_rho_commute : Formalism.FourierDecayAlt.JF.CVRho := by
  exact Formalism.FourierDecayAlt.P.JFxE.cVRho
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatBdd
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

noncomputable section

theorem hat_bounded_decay_holds : JDHatBdd := by
  intro P L hTT hL X hX b hb
  have hLaw : (MA.DQ P).Laws P.TT := Formalism.FourierDecayAlt.P.analytic_laws P.r P.TT hTT
  have hS := Formalism.FourierDecayAlt.P.MAx3.H.hyp_model hL hLaw
  have hV := Formalism.FourierDecayAlt.P.MAx3.K.hypV_model hL hLaw
  have gen : ∀ b' ∈ Submonoid.closure (MA.bddSet P L), ∀ X' ∈ MA.hatSet P L,
      b' * X' ∈ Submodule.span ℂ (bddHat P L) := fun b' hb' X' hX' =>
    Submodule.subset_span ⟨b', hb', X', hX', rfl⟩
  have mA : ∀ y, L.Ahat y ∈ MA.hatSet P L := fun y => Or.inl (Or.inl (Or.inl ⟨y, rfl⟩))
  have mR : ∀ y, L.R0 y ∈ MA.hatSet P L := fun y => Or.inl (Or.inl (Or.inr ⟨y, rfl⟩))
  have mAv : ∀ y, L.Ahatv y ∈ MA.hatSet P L := fun y => Or.inl (Or.inr ⟨y, rfl⟩)
  have mRv : ∀ y, L.R0v y ∈ MA.hatSet P L := fun y => Or.inr ⟨y, rfl⟩
  have sumA : ∀ ts : List (ℂ × MA.A P (MA.DQ P) × ℂ), (∀ x ∈ ts, x.2.1 ∈ Submonoid.closure (MA.bddSet P L)) →
      (ts.map fun x => x.1 • (x.2.1 * L.Ahat x.2.2)).sum ∈ Submodule.span ℂ (bddHat P L) := by
    intro ts hts
    refine list_sum_mem fun u hu => ?_
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hu
    exact Submodule.smul_mem _ _ (gen _ (hts x hx) _ (mA _))
  have sumAv : ∀ ts : List (ℂ × MA.A P (MA.DQ P) × ℂ), (∀ x ∈ ts, x.2.1 ∈ Submonoid.closure (MA.bddSet P L)) →
      (ts.map fun x => x.1 • (x.2.1 * L.Ahatv x.2.2)).sum ∈ Submodule.span ℂ (bddHat P L) := by
    intro ts hts
    refine list_sum_mem fun u hu => ?_
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hu
    exact Submodule.smul_mem _ _ (gen _ (hts x hx) _ (mAv _))
  rcases hX with (((⟨y, rfl⟩ | ⟨y, rfl⟩) | ⟨y, rfl⟩) | ⟨y, rfl⟩)
  · obtain ⟨t, ht⟩ := hS.ahat b hb
    rw [ht y]; exact gen _ hb _ (mA _)
  · obtain ⟨t, ts, hts, he⟩ := hS.r0 b hb y
    rw [he]; exact Submodule.add_mem _ (gen _ hb _ (mR _)) (sumA ts hts)
  · obtain ⟨t, ht⟩ := hV.ahatv b hb
    rw [ht y]; exact gen _ hb _ (mAv _)
  · obtain ⟨t, ts, hts, he⟩ := hV.r0v b hb y
    rw [he]; exact Submodule.add_mem _ (gen _ hb _ (mRv _)) (sumAv ts hts)

end

end Formalism.FourierDecayAlt.P.CutMP
end
