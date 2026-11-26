module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UhMeasurableSet
public import Formalism.HermitianCurvature.CapelliDeterminantAndBranching
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OneParameterDifferentiable
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.StabPairs

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellZetaMinors
open Matrix MeasureTheory Filter

noncomputable section

namespace Formalism.FourierDecayAlt.P.BigCellZetaMinors

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

variable {k r : ℕ}

theorem one_uw (z : Fin (2 * r + k + 1) → ℂ) : (1 : Mat k r) ∈ UWset k r z := by
  refine ⟨?_, fun a => by simp, by simp⟩
  simp [UH]

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem dmin_sgs (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) (g : Mat k r) (l : Fin (r + 2)) :
    Dmin k r D.z D.z' (sgs p g) l = Dmin k r D.z D.z' g l := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  have hs : (Matrix.of p.1.2 * Matrix.of p.1.1 : Mat k r)⁻¹ ∈ Sset k r D.z := by
    rw [Matrix.mul_inv_rev]
    exact ⟨_, BigCellInversePair.uw_inv h1, _, WeylGroupFacts.mem_n_inv h2, rfl⟩
  have hs' : (Matrix.of p.2.2 * Matrix.of p.2.1 : Mat k r) ∈ Sset k r D.z' :=
    (sGroup k r D.z' D.z'_mem).2.1 _ ⟨1, one_uw _, _, h4, (Matrix.one_mul _).symm⟩ _
      ⟨_, h3, 1, WeylGroupFacts.mem_n_one, (Matrix.mul_one _).symm⟩
  rw [B5.sgs_eq]
  exact dInv k r D.z D.z' D.z_mem D.z'_mem _ hs _ hs' g l

theorem cmin_gq (D : RealPlaceData k r Wp Wq) {q : (Fin r → ℂ) × ℂ} (hq : q ∈ QDom k r D.z D.z') (a : Fin r) :
    cmin k r D.z D.z' (gq D q) a = q.1 a :=
  (bigCellMinors k r D.z D.z' q.1 (D.μsec q.2) D.z_mem D.z'_mem).2.1 hq.1 a

theorem zeta_gq (D : RealPlaceData k r Wp Wq) {q : (Fin r → ℂ) × ℂ} (hq : q ∈ QDom k r D.z D.z') :
    zeta k r D.z D.z' (gq D q) = q.2 := by
  have hz := (bigCellMinors k r D.z D.z' q.1 (D.μsec q.2) D.z_mem D.z'_mem).2.2 hq.1
  rw [BigCellHermitian.herm_bigCell _ _ D.z_mem D.z'_mem, (D.sec.2 q.2 hq.2).2] at hz
  exact hz

end Formalism.FourierDecayAlt.P.BigCellZetaMinors

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

end Formalism.FourierDecayAlt.P
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutMP2
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField

noncomputable section

section defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]

def BuiltOW (Cc : ℝ) (S : C.HidaSetting E Wp Wq)
    (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ) : Prop :=
  JCT.IsBuiltPlace Cc S T f χ ν' m₀ top A₀ ∧ (∀ v, (S.G.place (S.pl v)).Ok) ∧
    Sz.IsWord S.G.k S.de ∧ Sz.IsWord S.G.k S.de'

def lamCfg (S : C.HidaSetting E Wp Wq) (v : Fin S.f) : Fin ((D.parOf S v).k + 2 * (D.parOf S v).r + 1) → ℝ :=
  fun s => (S.G.place (S.pl v)).lam ((s : ℕ) + 1)

def OmP (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) : Set (B.Mat S.G.k S.G.r) :=
  {g | 0 < Formalism.QuantumDeterminants.Gf S.G.k S.G.r (T v).base.z (T v).base.z' g ∧
    ∀ a : Fin S.G.r, Formalism.QuantumDeterminants.Dmin S.G.k S.G.r (T v).base.z (T v).base.z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0}

def trJ (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (J : B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) :
    M.Ty (D.parOf S v) → MA.SmQ (D.parOf S v).r (D.parOf S v).TT :=
  fun ρ => MA.toSm (D.parOf S v) fun q =>
    ((Real.sqrt (MA.wq S.G.k q.1 (D.parOf S v).TT) : ℝ) : ℂ) *
      inner ℂ (B.hsVec (e ρ q.1.2)) (B.hsVec (J (B.gq (T v).base q.1)))

def IsFrame (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) : Prop :=
  (∀ ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (e ρ) {ζ : ℂ | (D.parOf S v).TT < Complex.normSq ζ}) ∧
  ∀ ζ : ℂ, (D.parOf S v).TT < Complex.normSq ζ →
    (∀ ρ, e ρ ζ ∈ NF.Fib S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec (T v).base.π (T v).base.π' ζ) ∧
    (∀ ρ ρ', inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec (e ρ' ζ)) = if ρ = ρ' then (1 : ℂ) else 0) ∧
    ∀ X ∈ NF.Fib S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec (T v).base.π (T v).base.π' ζ,
      X = ∑ ρ, inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec X) • e ρ ζ

def IsGauge (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) : Prop :=
  ∀ J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v), ∀ Y : ℝ,
    trJ S T v e (Q.CV S.G.k S.G.r (Y : ℂ) J) =
      MA.actA (D.parOf S v) (Wd.C0 (MA.QQr (D.parOf S v) (MA.DQ (D.parOf S v))) (MA.sites (D.parOf S v) (MA.DQ (D.parOf S v))) (Y : ℂ))
        (trJ S T v e J)

end defs

def LamCfgInterlaces : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq),
    2 ≤ S.G.k → (∀ v, (S.G.place (S.pl v)).Ok) → Sz.IsWord S.G.k S.de → Sz.IsWord S.G.k S.de' → ∀ v,
      C7.LamInterlaces S.G.k S.G.r (D.parOf S v).u (lamCfg S v) ∧
        C7.LamInterlaces S.G.k S.G.r (D.parOf S v).u' (lamCfg S v)

def AdmInCut : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq),
    C.GridsOK S → ∀ v (a : List C.Letter), D.AdmAt S v a → ∀ x ∈ a, x.2 ∈ Set.Icc (S.cutLo v) (S.cutHi v)

def CVPresFF : Prop :=
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
    ∀ v, ∀ J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v), ∀ (Y : ℝ) (s : ℂ), s • Q.CV S.G.k S.G.r (Y : ℂ) J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v)

def BesselEigen : Prop :=
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
    ∀ v, ∀ Y : ℝ, ∀ x ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT,
      Q.CV S.G.k S.G.r (Y : ℂ) (B.JF (T v).base (f v)) (B.gq (T v).base x) =
        ((S.P v Y : ℝ) : ℂ) • B.JF (T v).base (f v) (B.gq (T v).base x)

def EnergyTr : Prop :=
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
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))), IsFrame S T v e →
      (∀ J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v), ∀ (Y : ℝ) (s : ℂ), s • Q.CV S.G.k S.G.r (Y : ℂ) J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v)) →
      ∀ ε : ℝ, 0 < ε → B.JF (T v).base (D.cutF (T v).base χ (f v) ε) ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v) → ∀ a : List C.Letter, D.AdmAt S v a →
        C7.principalHermitianLattice (T v).base (M.sgn (D.parOf S v) (S.l + 1)) a (D.cutF (T v).base χ (f v) ε) =
          MA.ipA (D.parOf S v)
            (trJ S T v e (a.reverse.foldr (fun x J => (M.sgn (D.parOf S v) (S.l + 1)) • Q.CV S.G.k S.G.r (x.2 : ℂ) J)
              (B.JF (T v).base (D.cutF (T v).base χ (f v) ε))))
            (trJ S T v e (B.JF (T v).base (D.cutF (T v).base χ (f v) ε)))

def CutTr : Prop :=
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
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))), IsFrame S T v e →
      B.JF (T v).base (f v) ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v) → ∀ c : LE.Cut, c.χ = χ → ∀ ε : ℝ, 0 < ε →
        trJ S T v e (B.JF (T v).base (D.cutF (T v).base χ (f v) ε)) =
          MA.chiJ (D.parOf S v) (trJ S T v e (B.JF (T v).base (f v))) c ε

def EnergyReal : Prop :=
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
    ∀ v, ∀ ε : ℝ, 0 < ε → ∀ a : List C.Letter, D.AdmAt S v a →
      (C7.principalHermitianLattice (T v).base (M.sgn (D.parOf S v) (S.l + 1)) a (D.cutF (T v).base χ (f v) ε)).im = 0

end

end Formalism.FourierDecayAlt.P.CutMP
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.RightTypeAction
open Matrix Finset Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace QrD

section Geometry

variable {k r : ℕ}

def InLieW (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (X : Mx k r) : Prop :=
  inLieLev k r (Fin.last r) X ∧ X *ᵥ z = 0

theorem exp_uw {z : Fin (2 * r + k + 1) → ℂ} {X : Mx k r} (hX : InLieW k r z X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ UWset k r z := by
  have h := Qx8.exp_lev hX.1 t
  exact ⟨h.1, fun a => h.2 a (by simp), Qx8.exp_fix hX.2 t⟩

theorem unitB_conj_mulVec {n m : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (Bs : Fin m → Fin n → ℂ) (a b : Fin m)
    (v : Fin n → ℂ) (h : herm H v (Bs a) = 0) : (unitB H Bs a b)ᴴ *ᵥ (H *ᵥ v) = 0 := by
  ext q
  have h' : ∑ p, star (Bs a p) * (H *ᵥ v) p = 0 := h
  show ∑ p, star (Bs a p * (star (Bs b) ⬝ᵥ H *ᵥ bvec q)) * (H *ᵥ v) p = 0
  simp_rw [star_mul']
  rw [show ∑ p, star (Bs a p) * star (star (Bs b) ⬝ᵥ H *ᵥ bvec q) * (H *ᵥ v) p
      = star (star (Bs b) ⬝ᵥ H *ᵥ bvec q) * ∑ p, star (Bs a p) * (H *ᵥ v) p from by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun p _ => by ring, h', mul_zero]

theorem frame_lie {m : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {Bs : Fin m → Fin (2 * r + k + 1) → ℂ}
    (hB : IsFrameOf k r [z] Bs) (a b : Fin m) :
    InLieW k r z (hpart1 (Hpk k r) (unitB (Hpk k r) Bs a b)) ∧
      InLieW k r z (hpart2 (Hpk k r) (unitB (Hpk k r) Bs a b)) := by
  have hl := Qx8.unitB_lie Bs hB.1 (Fin.last r) a b
  have h0 : ∀ c, herm (Hpk k r) z (Bs c) = 0 := by
    intro c
    rw [← Qx2.herm_star, hB.2.2 c z (by simp), star_zero]
  have z1 : unitB (Hpk k r) Bs a b *ᵥ z = 0 := by
    rw [Qx8.unitB_mulVec, h0, zero_smul]
  have z2 : ((Hpk k r)⁻¹ * (unitB (Hpk k r) Bs a b)ᴴ * Hpk k r) *ᵥ z = 0 := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, unitB_conj_mulVec _ _ _ _ _ (h0 a), Matrix.mulVec_zero]
  refine ⟨⟨hl.1, ?_⟩, ⟨hl.2, ?_⟩⟩
  · unfold hpart1; rw [Matrix.smul_mulVec, Matrix.sub_mulVec, z1, z2]; simp
  · unfold hpart2; rw [Matrix.smul_mulVec, Matrix.add_mulVec, z1, z2]; simp

end Geometry

section Rep

variable {k r : ℕ} {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]

def dOp (π : Mx k r → (W →L[ℂ] W)) (X : Mx k r) : W →L[ℂ] W :=
  deriv (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • X))) 0

def ecOp (π : Mx k r → (W →L[ℂ] W)) (Z : Mx k r) : W →L[ℂ] W :=
  dOp π (hpart1 (Hpk k r) Z) + Complex.I • dOp π (hpart2 (Hpk k r) Z)

variable [FiniteDimensional ℂ W] {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (W →L[ℂ] W)}

theorem dOp_hasDeriv (hπ : IsCRepOn (UWset k r z) π) (hc : ContinuousOn π (UWset k r z)) {X : Mx k r}
    (hX : InLieW k r z X) : HasDerivAt (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • X))) (dOp π X) 0 := by
  have hcont : Continuous fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • X)) := by
    have h1 := Qx8.lcurve_cont X (1 : Mx k r)
    simp only [Matrix.mul_one] at h1
    exact hc.comp_continuous h1 (exp_uw hX)
  obtain ⟨A, hA⟩ := one_parameter_differentiable W (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • X)))
    (by simp [NormedSpace.exp_zero, hπ.1])
    (fun s t => by
      show π (NormedSpace.exp (((s + t : ℝ) : ℂ) • X)) = _
      rw [B5.exp_add', hπ.2 _ (exp_uw hX s) _ (exp_uw hX t)]) hcont
  exact (hA 0).differentiableAt.hasDerivAt

theorem dRep_eq (hπ : IsCRepOn (UWset k r z) π) (hc : ContinuousOn π (UWset k r z)) {X : Mx k r}
    (hX : InLieW k r z X) (v : W) : dRep π X v = dOp π X v := by
  have h := dOp_hasDeriv hπ hc hX
  have h2 : HasDerivAt (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • X)) v) (dOp π X v) 0 := by
    have := ((ContinuousLinearMap.apply ℂ W v).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
    simpa [Function.comp_def] using this
  unfold dRep
  exact h2.deriv

theorem ecRep_eq (hπ : IsCRepOn (UWset k r z) π) (hc : ContinuousOn π (UWset k r z)) {Z : Mx k r}
    (h1 : InLieW k r z (hpart1 (Hpk k r) Z)) (h2 : InLieW k r z (hpart2 (Hpk k r) Z)) (v : W) :
    EcRep (Hpk k r) π Z v = ecOp π Z v := by
  unfold EcRep ecOp
  rw [dRep_eq hπ hc h1, dRep_eq hπ hc h2]
  rfl

end Rep

section Right

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq]
  [NormedSpace ℂ Wq] [FiniteDimensional ℂ Wq] {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
  {π' : Mx k r → (Wq →L[ℂ] Wq)} {D : Set (Mx k r)} {J : Mx k r → (Wq →L[ℂ] Wp)}

theorem mem_right (hD : IsDom k r z z' (Fin.last r) D) {g h : Mx k r} (hg : g ∈ Glev k r (Fin.last r) ∩ D)
    (hh : h ∈ UWset k r z') : g * h ∈ Glev k r (Fin.last r) ∩ D := by
  obtain ⟨hgG, hgD⟩ := hg
  refine ⟨?_, ?_⟩
  · simp only [Glev, UH, UWset, Set.mem_setOf_eq] at hgG hh ⊢
    refine ⟨?_, fun a ha => ?_⟩
    · rw [conjTranspose_mul]
      calc hᴴ * gᴴ * Hpk k r * (g * h) = hᴴ * (gᴴ * Hpk k r * g) * h := by simp only [Matrix.mul_assoc]
        _ = Hpk k r := by rw [hgG.1, hh.1]
    · rw [← mulVec_mulVec, ← mulVec_mulVec, (hh.2.1 a).1, (hh.2.1 a).2]
      exact hgG.2 a ha
  · have h1z : (1 : Mx k r) ∈ UWset k r z := by simp [UWset, UH]
    have h1N : (1 : Mx k r) ∈ Nlev k r (Fin.last r) := by simp [Nlev, QuantumDeterminants.Nset, Glev, UH, Matrix.one_apply]
    have hS := hD.2 g ⟨hgG, hgD⟩ 1 ⟨1, h1z, 1, h1N, by simp⟩ h ⟨h, hh, 1, h1N, by simp⟩
    simpa using hS

theorem J_right (hπ' : IsCRepOn (UWset k r z') π') (hJ : J ∈ FFl k r z z' π π' (Fin.last r) D) {g h : Mx k r}
    (hg : g ∈ Glev k r (Fin.last r) ∩ D) (hh : h ∈ UWset k r z') : J (g * h) = (J g).comp (π' h) := by
  have h1z : (1 : Mx k r) ∈ UWset k r z := by simp [UWset, UH]
  have h1z' : (1 : Mx k r) ∈ UWset k r z' := by simp [UWset, UH]
  simp only [FFl, Set.mem_setOf_eq] at hJ
  have e1 := hJ.2.2.2 g hg 1 h1z 1 h1z'
  have e2 := hJ.2.2.2 g hg 1 h1z h hh
  rw [one_mul, mul_one, hπ'.1] at e1
  have e1' : π 1 ∘SL J g = J g := by
    ext x
    exact (congrArg (fun T => T x) e1).symm
  rw [one_mul] at e2
  rw [e2, ← ContinuousLinearMap.comp_assoc, e1']

theorem rd_right (hD : IsDom k r z z' (Fin.last r) D) (hπ' : IsCRepOn (UWset k r z') π')
    (hc : ContinuousOn π' (UWset k r z')) (hJ : J ∈ FFl k r z z' π π' (Fin.last r) D)
    {F : Mx k r → (Wq →L[ℂ] Wp)} {B : Wq →L[ℂ] Wq}
    (hF : ∀ g ∈ Glev k r (Fin.last r) ∩ D, F g = (J g).comp B) {X : Mx k r} (hX : InLieW k r z' X)
    {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r) ∩ D) : RdV X F g = (J g).comp ((dOp π' X).comp B) := by
  have hfun : (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • X))) =
      fun t : ℝ => (J g).comp ((π' (NormedSpace.exp ((t : ℂ) • X))).comp B) := by
    funext t
    have hu := exp_uw hX t
    rw [hF _ (mem_right hD hg hu), J_right hπ' hJ hg hu, ContinuousLinearMap.comp_assoc]
  unfold RdV
  rw [hfun]
  have hd := dOp_hasDeriv hπ' hc hX
  let L : (Wq →L[ℂ] Wq) →L[ℝ] (Wq →L[ℂ] Wp) :=
    (((ContinuousLinearMap.compL ℂ Wq Wq Wp) (J g)).comp
      ((ContinuousLinearMap.compL ℂ Wq Wq Wq).flip B)).restrictScalars ℝ
  have key : HasDerivAt (fun t : ℝ => (J g).comp ((π' (NormedSpace.exp ((t : ℂ) • X))).comp B))
      ((J g).comp ((dOp π' X).comp B)) 0 := by
    have h2 := L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
    convert h2 using 1
    all_goals first | rfl | (ext; rfl)
  exact key.deriv

theorem rz_right (hD : IsDom k r z z' (Fin.last r) D) (hπ' : IsCRepOn (UWset k r z') π')
    (hc : ContinuousOn π' (UWset k r z')) (hJ : J ∈ FFl k r z z' π π' (Fin.last r) D)
    {F : Mx k r → (Wq →L[ℂ] Wp)} {B : Wq →L[ℂ] Wq}
    (hF : ∀ g ∈ Glev k r (Fin.last r) ∩ D, F g = (J g).comp B) {Z : Mx k r}
    (h1 : InLieW k r z' (hpart1 (Hpk k r) Z)) (h2 : InLieW k r z' (hpart2 (Hpk k r) Z))
    {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r) ∩ D) :
    RZ (Hpk k r) Z F g = (J g).comp ((ecOp π' Z).comp B) := by
  unfold RZ
  rw [rd_right hD hπ' hc hJ hF h1 hg, rd_right hD hπ' hc hJ hF h2 hg]
  ext v
  simp [ecOp]

theorem fold_right (hD : IsDom k r z z' (Fin.last r) D) (hπ' : IsCRepOn (UWset k r z') π')
    (hc : ContinuousOn π' (UWset k r z')) (hJ : J ∈ FFl k r z z' π π' (Fin.last r) D)
    (L : List (ℂ × Mx k r))
    (hL : ∀ p ∈ L, InLieW k r z' (hpart1 (Hpk k r) p.2) ∧ InLieW k r z' (hpart2 (Hpk k r) p.2)) :
    ∃ B : Wq →L[ℂ] Wq,
      (∀ g ∈ Glev k r (Fin.last r) ∩ D,
        (L.map fun p => fun y : Mx k r → (Wq →L[ℂ] Wp) => p.1 • y + RZ (Hpk k r) p.2 y).foldr (fun T h => T h) J g =
          (J g).comp B) ∧
      ∀ v, B v = (L.map fun p => fun y : Wq => p.1 • y + EcRep (Hpk k r) π' p.2 y).foldr (fun T h => T h) v := by
  induction L with
  | nil => exact ⟨ContinuousLinearMap.id ℂ Wq, fun g _ => by simp, fun v => rfl⟩
  | cons p L ih =>
    obtain ⟨B', hB1, hB2⟩ := ih (fun q hq => hL q (by simp [hq]))
    obtain ⟨h1, h2⟩ := hL p (by simp)
    refine ⟨p.1 • B' + (ecOp π' p.2).comp B', fun g hg => ?_, fun v => ?_⟩
    · simp only [List.map_cons, List.foldr_cons, Pi.add_apply, Pi.smul_apply]
      rw [rz_right hD hπ' hc hJ hB1 h1 h2 hg, hB1 g hg]
      ext v
      simp
    · simp only [List.map_cons, List.foldr_cons, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply]
      rw [hB2 v, ecRep_eq hπ' hc h1 h2]

end Right

end QrD

theorem right_type_action : Formalism.FourierDecayAlt.Q.RightTypeAction := by
  intro Wp Wq _ _ _ _ _ k r m z z' π π' D hz hz' hD hπ' hc J hJ g hg Bs hB w v
  unfold capR capRep qmF
  have key : ∀ σ : Equiv.Perm (Fin m), ∃ Bσ : Wq →L[ℂ] Wq,
      (∀ g ∈ Glev k r (Fin.last r) ∩ D,
        ((List.ofFn fun j => ((if σ j = j then w - ((j : ℕ) : ℂ) else 0), unitB (Hpk k r) Bs (σ j) j)).map
          fun p => fun y : Mx k r → (Wq →L[ℂ] Wp) => p.1 • y + RZ (Hpk k r) p.2 y).foldr (fun T h => T h) J g =
            (J g).comp Bσ) ∧
      ∀ v, Bσ v = ((List.ofFn fun j => ((if σ j = j then w - ((j : ℕ) : ℂ) else 0), unitB (Hpk k r) Bs (σ j) j)).map
          fun p => fun y : Wq => p.1 • y + EcRep (Hpk k r) π' p.2 y).foldr (fun T h => T h) v :=
    fun σ => QrD.fold_right hD hπ' hc hJ _ (by
      intro p hp
      simp only [List.mem_ofFn] at hp
      obtain ⟨j, rfl⟩ := hp
      exact QrD.frame_lie hB (σ j) j)
  simp only [List.map_ofFn, Function.comp_def, ite_smul, zero_smul] at key
  choose Bf hBf1 hBf2 using key
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [id, Finset.sum_apply, Pi.smul_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, map_sum, map_zsmul, map_smul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [hBf1 σ g hg, ContinuousLinearMap.comp_apply, hBf2 σ v]

end Formalism.FourierDecayAlt.P
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.L2NormScaling
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

noncomputable section

set_option maxHeartbeats 1600000

namespace Formalism.FourierDecayAlt.P.DDSmoothness

open Formalism.FourierDecayAlt.ThreeDimData

section Alg

variable {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]

theorem inner_self_cast (a : Wp) : ⟪a, a⟫_ℂ = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
  apply Complex.ext
  · rw [Complex.ofReal_re]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) a
  · rw [Complex.ofReal_im]
    exact inner_self_im (𝕜 := ℂ) a

theorem l2_norm_scaling {νq : Measure (Formalism.QuantumDeterminants.Mt k r)} (T F : Mx k r → Wp) (a : Wp) (U D : ℝ) (hU : 0 ≤ U)
    (hN : PI.BesselPeriodGGP.l2SG (k := k) (r := r) νq T =
      ENNReal.ofReal (U * (⟪a, ⟪a, a⟫_ℂ • a⟫_ℂ).re / D))
    (hae : ∀ᵐ x ∂νq, T (Matrix.of x) = ⟪a, a⟫_ℂ • F (Matrix.of x)) :
    ENNReal.ofReal (‖a‖ ^ 2) * PI.BesselPeriodGGP.l2SG (k := k) (r := r) νq F =
      ENNReal.ofReal (U * ‖a‖ ^ 2 / D) := by
  have hinner : ⟪a, a⟫_ℂ = ((‖a‖ ^ 2 : ℝ) : ℂ) := inner_self_cast a
  have hnq : ‖⟪a, a⟫_ℂ‖ = ‖a‖ ^ 2 := by
    rw [hinner, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hc : (‖⟪a, a⟫_ℂ‖₊ : ENNReal) = ENNReal.ofReal (‖a‖ ^ 2) := by
    rw [← hnq]
    exact (ENNReal.ofReal_eq_coe_nnreal (norm_nonneg _)).symm
  have hT : PI.BesselPeriodGGP.l2SG (k := k) (r := r) νq T =
      ENNReal.ofReal (‖a‖ ^ 2) ^ 2 * PI.BesselPeriodGGP.l2SG (k := k) (r := r) νq F := by
    unfold PI.BesselPeriodGGP.l2SG
    rw [← lintegral_const_mul' (ENNReal.ofReal (‖a‖ ^ 2) ^ 2) _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)]
    refine lintegral_congr_ae (hae.mono fun x hx => ?_)
    dsimp only
    rw [hx, nnnorm_smul, ENNReal.coe_mul, mul_pow, hc]
  have hre : (⟪a, ⟪a, a⟫_ℂ • a⟫_ℂ).re = ‖a‖ ^ 4 := by
    rw [inner_smul_right, hinner, ← Complex.ofReal_mul, Complex.ofReal_re]
    ring
  rw [hT, hre] at hN
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  have hp : 0 < ‖a‖ ^ 2 := pow_pos (norm_pos_iff.mpr ha) 2
  have key : ENNReal.ofReal (‖a‖ ^ 2) * (ENNReal.ofReal (‖a‖ ^ 2) * PI.BesselPeriodGGP.l2SG (k := k) (r := r) νq F) =
      ENNReal.ofReal (‖a‖ ^ 2) * ENNReal.ofReal (U * ‖a‖ ^ 2 / D) := by
    rw [← mul_assoc, ← pow_two, hN, ← ENNReal.ofReal_mul hp.le]
    congr 1
    ring
  exact (ENNReal.mul_right_inj (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top).mp key

end Alg

theorem shape_of (hPsi : PsiConst) (hSch : SchurH) (hBC : BeConv) (hNI : NormIdSm) (hBB : BeBessel) : Shape := by
  intro hIn k r ε lam h H _ _ _ σ w0 Wp _ _ _ _ z c u π μW μN μG νq hS hnz
  have hS' := hS
  obtain ⟨hlam, hσ, -, -, hw0, hz, hT, hc, hπ, -, -, -, -⟩ := hS'
  have hsm := DD_smooth hIn.2.2.1 hlam hσ hw0
  obtain ⟨-, -, -, hBC4⟩ := hBC hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS
  obtain ⟨x0, hx0, y0, hy0, hne⟩ := hnz
  obtain ⟨ξ0, hξ0⟩ : ∃ ξ, be z c π σ μW μN x0 y0 ξ ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hne (ContinuousLinearMap.ext hcon)
  have hB0 := hBB hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS y0 (Or.inl hy0) ξ0
  set B0 : H → Wp := fun x => be z c π σ μW μN x y0 ξ0 with hB0def
  have hB0x : B0 x0 ≠ 0 := hξ0
  have hcoef : ∀ v ∈ DDsp σ w0, ∀ ξ : Wp, ∃ κ : ℂ, ∀ x ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ,
      be z c π σ μW μN x v ξ = κ • B0 x := fun v hv ξ =>
    jsz_line hIn.2.2.2 hPsi hlam hσ hz hT hc hπ hB0
      (hBB hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS v (Or.inl hv) ξ) (hsm x0 hx0) hB0x
  choose! cf hcf using hcoef
  have herm : ∀ x ∈ DDsp σ w0, ∀ v ∈ DDsp σ w0, ∀ η ξ : Wp,
      cf v ξ * ⟪η, B0 x⟫_ℂ = conj (cf x η) * ⟪B0 v, ξ⟫_ℂ := by
    intro x hx v hv η ξ
    have hadj := (hBC4 x hx v (Or.inl hv)).2
    have e := ContinuousLinearMap.adjoint_inner_left (be z c π σ μW μN x v) ξ η
    rw [hadj, hcf v hv ξ x (hsm x hx), hcf x hx η v (hsm v hv), inner_smul_left, inner_smul_right] at e
    exact e.symm
  have hη : ⟪B0 x0, B0 x0⟫_ℂ ≠ 0 := inner_self_ne_zero.mpr hB0x
  set κ : ℂ := conj (cf x0 (B0 x0)) / ⟪B0 x0, B0 x0⟫_ℂ with hκdef
  have hcf' : ∀ v ∈ DDsp σ w0, ∀ ξ, cf v ξ = κ * ⟪B0 v, ξ⟫_ℂ := by
    intro v hv ξ
    have e := herm x0 hx0 v hv (B0 x0) ξ
    rw [hκdef, div_mul_eq_mul_div, eq_div_iff hη]
    linear_combination e
  have hform : ∀ x ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, ∀ v ∈ DDsp σ w0, ∀ ξ,
      be z c π σ μW μN x v ξ = (κ * ⟪B0 v, ξ⟫_ℂ) • B0 x := fun x hx v hv ξ => by
    rw [hcf v hv ξ x hx, hcf' v hv ξ]
  have hκ0 : κ ≠ 0 := by
    intro h0
    apply hξ0
    show be z c π σ μW μN x0 y0 ξ0 = 0
    rw [hform x0 (hsm x0 hx0) y0 hy0 ξ0, h0, zero_mul, zero_smul]
  have hpos := (hNI hIn hSch k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS x0 (hsm x0 hx0) x0 (Or.inl hx0)
    (B0 x0)).2
  rw [hform x0 (hsm x0 hx0) x0 hx0, inner_smul_right, inner_self_cast] at hpos
  set N2 : ℝ := ‖B0 x0‖ ^ 2 with hN2
  have hN2pos : 0 < N2 := by rw [hN2]; have := norm_pos_iff.mpr hB0x; positivity
  have hexp : κ * (N2 : ℂ) * (N2 : ℂ) = κ * ((N2 * N2 : ℝ) : ℂ) := by push_cast; ring
  rw [hexp, Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im] at hpos
  simp only [mul_zero, zero_add, sub_zero] at hpos
  have hNN : 0 < N2 * N2 := mul_pos hN2pos hN2pos
  have him : κ.im = 0 := by
    rcases mul_eq_zero.mp hpos.1 with h1 | h1
    · exact h1
    · exact absurd h1 hNN.ne'
  have hre0 : 0 ≤ κ.re := by
    by_contra hneg; push_neg at hneg
    have : κ.re * (N2 * N2) < 0 := mul_neg_of_neg_of_pos hneg hNN
    linarith [hpos.2]
  have hre : 0 < κ.re := by
    rcases hre0.lt_or_eq with h1 | h1
    · exact h1
    · exact absurd (Complex.ext (by simp [← h1]) (by simp [him])) hκ0
  set s : ℝ := Real.sqrt κ.re with hs
  have hss : (s : ℂ) * (s : ℂ) = κ := by
    rw [← Complex.ofReal_mul, hs, Real.mul_self_sqrt hre.le]
    exact Complex.ext (by simp) (by simp [him])
  have hspos : 0 < s := Real.sqrt_pos.mpr hre
  refine ⟨fun x => (s : ℂ) • B0 x, bessel_smul hB0 _, ⟨x0, hx0, ?_⟩, ?_⟩
  · exact smul_ne_zero (by exact_mod_cast hspos.ne') hB0x
  · intro x hx v hv
    ext ξ
    simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
    rw [hform x hx v hv ξ, inner_smul_left, Complex.conj_ofReal, smul_smul]
    congr 1
    rw [← hss]; ring

theorem kFinForm_of (hPsi : PsiConst) (hBC : BeConv) (hBB : BeBessel) : KFinForm := by
  intro hIn k r ε lam h H _ _ _ σ w0 Wp _ _ _ _ z c u π μW μN μG νq hS l hl hx1e hid v hv x hx
  obtain ⟨x1, hx1, hlx1⟩ := hx1e
  have hS' := hS
  obtain ⟨hlam, hσ, -, -, hw0, hz, hT, hc, hπ, -, -, -, -⟩ := hS'
  have hsm := DD_smooth hIn.2.2.1 hlam hσ hw0
  have hvs : v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ := hIn.2.2.1 k r ε lam H σ hlam hσ v hv
  obtain ⟨-, -, -, hBC4⟩ := hBC hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS
  ext ξ
  obtain ⟨κ, hκ⟩ := jsz_line hIn.2.2.2 hPsi hlam hσ hz hT hc hπ hl
    (hBB hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS v (Or.inr hv) ξ) (hsm x1 hx1) hlx1
  have hadj := (hBC4 x1 hx1 v (Or.inr hv)).2
  have e := ContinuousLinearMap.adjoint_inner_left (be z c π σ μW μN x1 v) ξ (l x1)
  rw [hadj, hκ x1 (hsm x1 hx1), hid v hvs x1 hx1] at e
  simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, inner_smul_left, inner_smul_right,
    inner_conj_symm] at e
  have hn : ⟪l x1, l x1⟫_ℂ ≠ 0 := inner_self_ne_zero.mpr hlx1
  have hκv : κ = ⟪l v, ξ⟫_ℂ := by
    apply mul_left_cancel₀ hn
    linear_combination -e
  rw [hκ x hx, hκv]
  simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]

theorem discrete_form_one_side : DDFormOneOfSteps := by
  intro hPsi hSch _ _ _ _ hBC hNI hBB hSh hIn k r ε lam h H _ _ _ σ w0 Wp _ _ _ _ z c u π μW μN μG νq hS
  have hS' := hS
  obtain ⟨hlam, hσ, -, -, hw0, -, -, -, -, hW, hN, hG, hq⟩ := hS'
  have hsm := DD_smooth hIn.2.2.1 hlam hσ hw0
  obtain ⟨hBC1, -, -, -⟩ := hBC hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS
  obtain ⟨d, hd, hSd⟩ := hSch k r ε lam H σ μG hlam hσ hG
  have hw0n : w0 ≠ 0 := by
    obtain ⟨P, -, hn1, -⟩ := hw0
    intro h0; rw [h0, norm_zero] at hn1; exact zero_ne_one hn1
  have hdeg : ∀ x : H, x ≠ 0 → PI.BesselPeriodGGP.fdegH μG σ x = d := fun x hx => fdeg_eq hd hSd hx
  have hmu := muSof_facts hW hN
  have hae := ae_UH_of_quot hG.2.2.1 hmu.1 hmu.2 hq
  by_cases hnz : ∃ x ∈ DDsp σ w0, ∃ y ∈ DDsp σ w0, be z c π σ μW μN x y ≠ 0
  · obtain ⟨l, hl, -, hid⟩ := hSh hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS hnz
    refine ⟨l, hl, fun x hx v hv => ⟨hBC1 x (hsm x hx) v (Or.inl hv), hid x (hsm x hx) v hv⟩, ?_⟩
    intro x hx hx0 v hv
    have hNv := (hNI hIn hSch k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS x (hsm x hx) v (Or.inl hv) (l v)).1
    rw [hid v (hsm v hv) v hv] at hNv
    simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply] at hNv
    rw [hdeg w0 hw0n] at hNv
    rw [hdeg x hx0]
    refine l2_norm_scaling _ _ (l v) _ _ (by positivity) hNv (hae.mono fun g hg => ?_)
    rw [hid _ (PI.UnitaryGroupMassFormula.CapelliEig.smooth_right_action k r ε lam H σ hσ x (hsm x hx) _ hg) v hv]
    simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
  · push_neg at hnz
    refine ⟨fun _ => 0, bessel_zero, fun x hx v hv => ⟨hBC1 x (hsm x hx) v (Or.inl hv), ?_⟩,
      fun x _ _ v _ => by simp⟩
    show be z c π σ μW μN x v = _
    rw [hnz x hx v hv]
    ext ξ; simp

end Formalism.FourierDecayAlt.P.DDSmoothness
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellOrbitSet
open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.JFxA3

open Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

theorem _root_.Formalism.FourierDecayAlt.P.big_cell_orbit_set : GqOm := by
  intro k r Wp Wq _ _ _ _ D
  have hnull : (volume : Measure ((Fin r → ℂ) × ℂ))
      (Set.univ ×ˢ {w : ℂ | Complex.normSq w = Formalism.QuantumDeterminants.Tz k r D.z * Formalism.QuantumDeterminants.Tz k r D.z'}) = 0 := by
    rw [Measure.volume_eq_prod, Measure.prod_prod]
    have h0 : (volume : Measure ℂ)
        {w : ℂ | Complex.normSq w = Formalism.QuantumDeterminants.Tz k r D.z * Formalism.QuantumDeterminants.Tz k r D.z'} = 0 := by
      apply measure_mono_null (t := Metric.sphere (0 : ℂ)
        (Real.sqrt (Formalism.QuantumDeterminants.Tz k r D.z * Formalism.QuantumDeterminants.Tz k r D.z')))
      · intro w hw
        simp only [Set.mem_setOf_eq] at hw
        simp only [Metric.mem_sphere, dist_zero_right]
        rw [← hw, Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
      · exact Measure.addHaar_sphere _ _ _
    rw [h0, mul_zero]
  rw [ae_restrict_iff' (Formalism.FourierDecayAlt.P.B7.measurableSet_Qset D)]
  filter_upwards [compl_mem_ae_iff.mpr hnull] with q hq hqQ
  apply Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom D
  simp only [B.Qset, Set.mem_setOf_eq] at hqQ
  unfold Formalism.QuantumDeterminants.bcWeight at hqQ
  split_ifs at hqQ with hle
  · refine ⟨?_, ?_⟩
    · intro a ha
      have hp : (∏ b : Fin r, ‖q.1 b‖ ^ (2 * (Formalism.QuantumDeterminants.Mdim k r b - 2))) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ a)
        rw [ha, norm_zero]
        apply zero_pow
        have := a.isLt
        unfold Formalism.QuantumDeterminants.Mdim
        omega
      rw [hp, zero_mul] at hqQ
      exact lt_irrefl _ hqQ
    · refine lt_of_le_of_ne hle ?_
      intro heq
      exact hq ⟨Set.mem_univ _, heq.symm⟩
  · exact absurd hqQ (lt_irrefl _)

end Formalism.FourierDecayAlt.P.JFxA3
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.MeasurableOfContinuousOnZero
open MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem measurable_of_continuousOn_zero {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {s : Set X} (hs : MeasurableSet s) {f : X → ℂ} (hf : ContinuousOn f s) (h0 : ∀ x ∉ s, f x = 0) : Measurable f := by
  classical
  have e : f = s.piecewise f (fun _ => 0) := by
    funext x
    by_cases hx : x ∈ s <;> simp [Set.piecewise, hx, h0]
  rw [e]
  exact hf.measurable_piecewise continuousOn_const hs

section Meas

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem radSp_continuousOn (Φ : RadSp k r z z' π π') :
    ContinuousOn (fun x : (Fin r → ℂ) × Mx k r => (Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2) (DomR k r z z') := by
  obtain ⟨-, hs, -⟩ := Φ.2
  intro x₀ hx₀
  obtain ⟨U, F, hU, hxU, hF, hΦ⟩ := hs x₀ hx₀
  have hFc : ContinuousAt F x₀ := hF.continuousOn.continuousAt (hU.mem_nhds hxU)
  refine hFc.continuousWithinAt.congr_of_eventuallyEq ?_ (hΦ x₀ hxU hx₀.2.1)
  filter_upwards [inter_mem_nhdsWithin (DomR k r z z') (hU.mem_nhds hxU)] with x hx
  exact hΦ x hx.2 hx.1.2.1

theorem radSp_zero_off (Φ : RadSp k r z z' π π') {x : (Fin r → ℂ) × Mx k r} (hx : x ∉ DomR k r z z') :
    (Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = 0 :=
  Φ.2.1 x hx

def glueMap (c : Fin r → ℂ) (q : Cf r 0 × Mt k r) : (Fin r → ℂ) × Mx k r := (glue 0 c q.1, Matrix.of q.2)

theorem glueMap_continuous (c : Fin r → ℂ) : Continuous (glueMap (k := k) c) := by
  refine Continuous.prodMk ?_ ?_
  · refine continuous_pi fun l => ?_
    have : (fun q : Cf r 0 × Mt k r => glue 0 c q.1 l) = fun q => q.1 ⟨l, Nat.zero_le _⟩ := by
      funext q
      simp [glue]
    rw [this]
    exact (continuous_apply _).comp continuous_fst
  · exact continuous_snd

theorem DomR_eq : DomR k r z z' = P.Qx5.OpR k r z z' ∩ (Prod.snd ⁻¹' Glev k r (Fin.last r)) := by
  ext x
  simp only [DomR, P.Qx5.OpR, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage]
  tauto

theorem measurableSet_glueMap_DomR (c : Fin r → ℂ) :
    MeasurableSet (glueMap (k := k) c ⁻¹' DomR k r z z') := by
  rw [DomR_eq, Set.preimage_inter]
  exact ((P.Qx5.isOpen_OpR k r z z').preimage (glueMap_continuous c)).measurableSet.inter
    (((P.Qx5.Glev_closed (Fin.last r)).preimage continuous_snd).preimage (glueMap_continuous c)).measurableSet

theorem pair_measurable (c : Fin r → ℂ) (Φ Ψ : RadSp k r z z' π π') :
    Measurable (fun q : Cf r 0 × Mt k r => B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) (glue 0 c q.1) (Matrix.of q.2))
      ((Ψ : Fn k r (Wq →L[ℂ] Wp)) (glue 0 c q.1) (Matrix.of q.2))) := by
  have hmaps : Set.MapsTo (glueMap (k := k) c) (glueMap (k := k) c ⁻¹' DomR k r z z') (DomR k r z z') :=
    fun q hq => hq
  have hΦc := (radSp_continuousOn Φ).comp (glueMap_continuous c).continuousOn hmaps
  have hΨc := (radSp_continuousOn Ψ).comp (glueMap_continuous c).continuousOn hmaps
  refine measurable_of_continuousOn_zero (measurableSet_glueMap_DomR c)
    ((P.B6.hsInner_continuous (Wp := Wp) (Wq := Wq)).comp_continuousOn (hΦc.prodMk hΨc)) ?_
  intro q hq
  have h0 : (Φ : Fn k r (Wq →L[ℂ] Wp)) (glue 0 c q.1) (Matrix.of q.2) = 0 := radSp_zero_off Φ hq
  show B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) (glue 0 c q.1) (Matrix.of q.2)) _ = 0
  rw [h0, P.B6.hilbert_schmidt_inner_basis_sum]
  simp

end Meas

theorem topDensMeasAll : TopDensMeasAll := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' μ L st K w u v _ _ c
  refine Measurable.stronglyMeasurable ?_
  unfold topDens
  exact Finset.measurable_sum _ fun e _ => pair_measurable c _ _

end Formalism.FourierDecayAlt.P5
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.StabilizerPairs
theorem Formalism.FourierDecayAlt.P.stabilizer_pairs : Formalism.FourierDecayAlt.C2.CurvatureConditionOneClauseThree :=
  stabPairs
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRTWNeAlgSt
open Matrix Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.TW

open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

def TWNeAlg : Prop :=
  ∀ (V V' : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [AddCommGroup V'] [Module ℂ V']
    [FiniteDimensional ℂ V'] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V)
    (E' : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V') (β β' : ℂ) (L L' : Fin (n + 1) → ℤ) (M M' : Fin n → ℤ) (i : Fin n),
    Hyp E β L → Hyp E' β' L' → Box L M → Box L' M' → Box L (Function.update M i (M i + 1)) →
    Box L' (Function.update M' i (M' i + 1)) → shf β M = shf β' M' →
    ∀ J : V' →ₗ[ℂ] V, J ≠ 0 → (∀ a b v, J (subA E' a b v) = subA E a b (J v)) →
    (∀ v, J v ∈ CapSp (subA E) (shf β M)) →
    ∃ v' : V', (∑ c, etaK E c (J (yK E' c v'))) ≠ 0 ∧
      (∑ c, etaK E c (J (yK E' c v'))) ∈ CapSp (subA E) (shf β (Function.update M i (M i + 1)))

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.TW
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.ExponentWordRecursion
open Matrix Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.ListSumInequalities

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.Ux10 Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma list_sum_flatMap {α β M : Type*} [AddCommMonoid M] (L : List α) (f : α → List β) (h : β → M) :
    ((L.flatMap f).map h).sum = (L.map fun a => ((f a).map h).sum).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [List.flatMap_cons, List.map_append, List.sum_append, ih]

lemma norm_list_sum_le {α : Type*} (L : List α) (f : α → E) :
    ‖(L.map f).sum‖ ≤ (L.map fun a => ‖f a‖).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons]
    exact (norm_add_le _ _).trans (add_le_add le_rfl ih)

lemma list_sum_le {α : Type*} (L : List α) (f f' : α → ℝ) (h : ∀ a ∈ L, f a ≤ f' a) :
    (L.map f).sum ≤ (L.map f').sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons]
    exact add_le_add (h a (by simp)) (ih (fun b hb => h b (by simp [hb])))

lemma list_sum_nonneg {α : Type*} (L : List α) (f : α → ℝ) (h : ∀ a ∈ L, 0 ≤ f a) : 0 ≤ (L.map f).sum := by
  exact List.sum_nonneg (fun x hx => by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
    exact h a ha)

end Formalism.FourierDecayAlt.P.ListSumInequalities

namespace Formalism.FourierDecayAlt.P

end Formalism.FourierDecayAlt.P
end
end
