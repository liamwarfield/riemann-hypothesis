module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJA
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FixedPointsGramVector
public import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ZinvBound
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.InverseSplitting
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ZhatSectionExists
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.StabilizerSplit

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStable2
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.FFS

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

def GermOps : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (Θ : B.DiffOp k r Wp Wq),
    (∀ (U : Set (B.Mat k r)) (f f' : B.Mat k r → (Wq →L[ℂ] Wp)), IsOpen U →
      (∀ x ∈ U, x ∈ B.GV k r → f x = f' x) → ∀ g ∈ U, g ∈ B.GV k r →
        B.opApply Θ f g = B.opApply Θ f' g ∧ B.opAdj Θ f g = B.opAdj Θ f' g) ∧
    (∀ (c : ℂ) (f : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r),
      B.opApply Θ (c • f) g = c • B.opApply Θ f g ∧ B.opAdj Θ (c • f) g = c • B.opAdj Θ f g)

def ExtLoc : Prop :=
  ∀ (k r : ℕ) (E' : Type) [NormedAddCommGroup E'] [NormedSpace ℂ E'] (O : Set (B.Mat k r)) (J : B.Mat k r → E'),
    IsOpen O → Q.SmoothLev k r 0 O J → ∀ g₀ ∈ B.GV k r, g₀ ∈ O →
      ∃ (f : B.Mat k r → E') (U : Set (B.Mat k r)), B.CkOn ⊤ (B.GV k r) f ∧ HasCompactSupport f ∧ tsupport f ⊆ O ∧
        IsOpen U ∧ g₀ ∈ U ∧ ∀ x ∈ U, x ∈ B.GV k r → f x = J x

def SmoothOps : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (Θ : B.DiffOp k r Wp Wq) (O : Set (B.Mat k r)), IsOpen O → (∀ g ∈ O, g ∈ B.GV k r → g ∈ B.GPos D) →
    B.SmoothCoef (B.GPos D) Θ → ∀ f : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) f → tsupport f ⊆ O →
      Q.SmoothLev k r 0 O (B.opApply Θ f) ∧ Q.SmoothLev k r 0 O (B.opAdj Θ f)

def AdjComm : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (Θ : B.DiffOp k r Wp Wq), B.SmoothCoef (B.GPos D) Θ → B.Commutes D (B.GPos D) Θ →
    ∀ f : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) f → HasCompactSupport f → B.SuppIn (B.GPos D) f →
      ∀ p, D.inSS p → ∀ g ∈ B.GPos D, B.opAdj Θ (B.rho D p f) g = B.rho D p (B.opAdj Θ f) g

def EquivOps : Prop :=
  ExtLoc →
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (O : Set (B.Mat k r)) (P : (B.Mat k r → (Wq →L[ℂ] Wp)) → B.Mat k r → (Wq →L[ℂ] Wp)),
    Q.IsDom k r D.z D.z' 0 O →
    (∀ (U : Set (B.Mat k r)) (f f' : B.Mat k r → (Wq →L[ℂ] Wp)), IsOpen U →
      (∀ x ∈ U, x ∈ B.GV k r → f x = f' x) → ∀ g ∈ U, g ∈ B.GV k r → P f g = P f' g) →
    (∀ (c : ℂ) (f : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r), g ∈ B.GV k r → P (c • f) g = c • P f g) →
    (∀ f : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) f → tsupport f ⊆ O → Q.SmoothLev k r 0 O (P f)) →
    (∀ f : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) f → HasCompactSupport f → tsupport f ⊆ O →
      ∀ p, D.inSS p → ∀ g ∈ O, g ∈ B.GV k r → P (B.rho D p f) g = B.rho D p (P f) g) →
    ∀ J ∈ Q.FFl k r D.z D.z' D.π D.π' 0 O, P J ∈ Q.FFl k r D.z D.z' D.π D.π' 0 O

def OmPDom : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))) (v : Fin S.f),
    Q.IsDom S.G.k S.G.r (T v).base.z (T v).base.z' 0 (OmP S T v) ∧
      ∀ g ∈ OmP S T v, g ∈ B.GV S.G.k S.G.r → g ∈ B.GPos (T v).base

end

end Formalism.FourierDecayAlt.P.CutMP.JA.FFS
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentUpperFacts
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P

namespace UnipotentUpperFacts

open C2x5 C2x6 C2x7 HermitianProjections FixedPointsGramVector

section gen

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

end gen

variable {k r : ℕ}

lemma N_upper {g : B.Mat k r} (hg : g ∈ Nset k r) (i j : Fin (2 * r + k + 1)) (hji : j ≤ i) :
    g i j = if i = j then 1 else 0 := by
  have hc := ((WeylGroupFacts.nset_iff g).mp hg).2
  by_cases hj : j.val ≤ r + k
  · exact hc i j hj (Or.inl hji)
  · push Not at hj
    have hU : gᴴ * Hpk k r * g = Hpk k r := hg.1
    have hinv : g⁻¹ = Hpk k r * gᴴ * Hpk k r := by
      apply Matrix.inv_eq_left_inv
      calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hU, WeylGroupFacts.hpk_sq]
    have hci := ((WeylGroupFacts.nset_iff _).mp (WeylGroupFacts.mem_n_inv hg)).2
    rw [hinv] at hci
    have hle : j.val ≤ i.val := hji
    have hsj := GBasic.sig_val k r j
    have hsi := GBasic.sig_val k r i
    rw [if_pos (Or.inr hj)] at hsj
    rw [if_pos (Or.inr (by omega))] at hsi
    have h := hci (GBasic.sig k r j) (GBasic.sig k r i) (by omega) (Or.inl (by omega))
    rw [Matrix.mul_assoc, Hpk_mul_apply, mul_Hpk_apply, Matrix.conjTranspose_apply, GBasic.sig_sig,
      GBasic.sig_sig] at h
    have hs1 : GBasic.sgn k r (GBasic.sig k r j) = 1 := by unfold GBasic.sgn; rw [if_neg (by omega)]
    have hs2 : GBasic.sgn k r (GBasic.sig k r i) = 1 := by unfold GBasic.sgn; rw [if_neg (by omega)]
    rw [hs1, hs2, one_mul, mul_one] at h
    have hiff : (GBasic.sig k r j = GBasic.sig k r i) ↔ (i = j) := by
      constructor
      · intro e; have := congrArg (GBasic.sig k r) e; rw [GBasic.sig_sig, GBasic.sig_sig] at this; exact this.symm
      · intro e; rw [e]
    have h2 := congrArg star h
    rw [star_star] at h2
    rw [h2]
    by_cases e : i = j
    · rw [if_pos (hiff.mpr e), if_pos e, star_one]
    · rw [if_neg (fun e' => e (hiff.mp e')), if_neg e, star_zero]

lemma N_unip {g : B.Mat k r} (hg : g ∈ Nset k r) : (g - 1) ^ (2 * r + k + 1) = 0 := by
  apply strict_pow_eq_zero
  intro i j hji
  rw [Matrix.sub_apply, N_upper hg i j hji, Matrix.one_apply, sub_self]

end UnipotentUpperFacts

end Formalism.FourierDecayAlt.P
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatOpA
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField

noncomputable section

def PolyOp {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (o κ : ℕ) (Θ : B.DiffOp k r Wp Wq) : Prop :=
  ∀ Tm ∈ Θ, Tm.word.length ≤ o ∧ ∃ P : B.Mat k r → ℂ, U.IsPolyDeg κ P ∧
    (∀ g, Tm.coef g = P g • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) ∧
    ∀ g, Tm.coefAdj g = star (P g) • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)

def JDPolyOK : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (o κ : ℕ) (Θ : B.DiffOp k r Wp Wq),
    PolyOp o κ Θ → (∀ UU : Set (B.Mat k r), B.SmoothCoef UU Θ) ∧ (∀ d : ℝ, (κ : ℝ) ≤ d → GlobCoef Θ d) ∧
      B.opOrder Θ ≤ o

def JDCapA : Prop :=
  ∀ (Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
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
      ∃ Θ Θv : B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)),
        PolyOp (2 * S.G.r + S.G.k + 1) ((S.G.r + 1) * (2 * S.G.r + S.G.k + 1)) Θ ∧
        PolyOp (2 * S.G.r + S.G.k + 1) ((S.G.r + 1) * (2 * S.G.r + S.G.k + 1)) Θv ∧
        B.Commutes (T v).base (B.GPos (T v).base) Θ ∧ B.Commutes (T v).base (B.GPos (T v).base) Θv ∧
        ∀ J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v),
          trJ S T v e (B.opApply Θ J) = MA.actA (D.parOf S v) (L.Ahat y) (trJ S T v e J) ∧
          trJ S T v e (B.opApply Θv J) = MA.actA (D.parOf S v) (L.Ahatv y) (trJ S T v e J)

def JDCapR : Prop :=
  ∀ (Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
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
      ∃ Θ Θv : B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)),
        PolyOp (2 * S.G.r + S.G.k + 1) ((S.G.r + 1) * (2 * S.G.r + S.G.k + 1)) Θ ∧
        PolyOp (2 * S.G.r + S.G.k + 1) ((S.G.r + 1) * (2 * S.G.r + S.G.k + 1)) Θv ∧
        B.Commutes (T v).base (B.GPos (T v).base) Θ ∧ B.Commutes (T v).base (B.GPos (T v).base) Θv ∧
        ∀ J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v),
          trJ S T v e (B.opApply Θ J) = MA.actA (D.parOf S v) (RhM (D.parOf S v) L y) (trJ S T v e J) ∧
          trJ S T v e (B.opApply Θv J) = MA.actA (D.parOf S v) (RhvM (D.parOf S v) L y) (trJ S T v e J)

theorem hatOK_of_poly (hP : JDPolyOK) {E : Type} [Field E] [NumberField E] [IsCMField E]
    {Wp Wq : InfinitePlace E → Type}
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    {Cc : ℝ} (hCc : 1 ≤ Cc) {S : C.HidaSetting E Wp Wq}
    {T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))} {v : Fin S.f}
    {Θ : B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))}
    (hΘ : PolyOp (2 * S.G.r + S.G.k + 1) ((S.G.r + 1) * (2 * S.G.r + S.G.k + 1)) Θ)
    (hc : B.Commutes (T v).base (B.GPos (T v).base) Θ) : HatOK Cc S T v Θ := by
  obtain ⟨hs, hg, ho⟩ := hP S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) _ _ Θ hΘ
  have hn : (0 : ℝ) ≤ nDim S.G.k S.G.r := by unfold nDim; positivity
  have hr : (0 : ℝ) ≤ (S.G.r : ℝ) + 1 := by positivity
  refine ⟨hs _, hc, hg _ ?_, ?_⟩
  · have e1 : (((S.G.r + 1) * (2 * S.G.r + S.G.k + 1) : ℕ) : ℝ) = ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r := by
      unfold nDim; push_cast; ring
    rw [e1, mul_assoc]
    exact le_mul_of_one_le_left (mul_nonneg hr hn) hCc
  · have e2 : ((B.opOrder Θ : ℕ) : ℝ) ≤ nDim S.G.k S.G.r := by
      unfold nDim; exact_mod_cast ho
    exact e2.trans (le_mul_of_one_le_left hn hCc)

theorem jDOpA_of_parts (hP : JDPolyOK) (hC : JDCapA) : JDOpA := by
  refine ⟨1, zero_le_one, ?_⟩
  intro Cc hCc E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e L hFr hL y
  obtain ⟨Θ, Θv, hΘ, hΘv, hc, hcv, h⟩ := hC Cc E Wp Wq S T f χ ν' m₀ top A₀ hB v e L hFr hL y
  exact ⟨Θ, Θv, hatOK_of_poly hP hCc hΘ hc, hatOK_of_poly hP hCc hΘv hcv, h⟩

theorem jDOpR_of_parts (hP : JDPolyOK) (hC : JDCapR) : JDOpR := by
  refine ⟨1, zero_le_one, ?_⟩
  intro Cc hCc E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e L hFr hQQ hL y
  obtain ⟨Θ, Θv, hΘ, hΘv, hc, hcv, h⟩ := hC Cc E Wp Wq S T f χ ν' m₀ top A₀ hB v e L hFr hQQ hL y
  exact ⟨Θ, Θv, hatOK_of_poly hP hCc hΘ hc, hatOK_of_poly hP hCc hΘv hcv, h⟩

end

end Formalism.FourierDecayAlt.P.CutMP
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.PBCutInside
namespace Formalism.FourierDecayAlt.P.PBCut

open Formalism.FourierDecayAlt NumberField

theorem cutInside_of_built {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
    [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
    {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}
    (h : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) : KB.CutInside S := by
  obtain ⟨-, -, -, -, -, hw1, hw2, hl1, hl2, hde, -⟩ := h
  intro v Y hY
  obtain ⟨hY1, hY2⟩ := hY
  unfold C.HidaSetting.cutLo at hY1
  unfold C.HidaSetting.cutHi at hY2
  have hne1 : S.l + 1 ≠ 1 := by omega
  have hne2 : S.l + 1 ≠ (S.G.place (S.pl v)).k := by simp only [Sz.Glob.place]; omega
  have hu : ∀ de : ℕ → ℝ, (S.G.place (S.pl v)).u de (S.l + 1) =
      (S.G.place (S.pl v)).v S.l - 1 / 2 - de S.l * (S.G.place (S.pl v)).Del := by
    intro de
    unfold Sz.Cfg.u
    rw [if_neg hne1, if_neg hne2, Nat.add_sub_cancel]
  simp only [D.parOf]
  unfold I.OnCut
  rw [hu S.de, hu S.de']
  rcases hw1.1 S.l with h | h <;> rcases hw2.1 S.l with h' | h'
  · exact absurd (h.trans h'.symm) hde
  · right
    rw [h, h']
    constructor <;> linarith
  · left
    rw [h, h']
    constructor <;> linarith
  · exact absurd (h.trans h'.symm) hde

end Formalism.FourierDecayAlt.P.PBCut
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.PointStep
open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

def mc {k ρ m : ℕ} (e : ρ + 1 = m) (c : ℂ) (γ : B.Mat k ρ) : B.Mat k m :=
  D.castM e (D.castM (Nat.add_comm 1 ρ) (U.mMap k 1 ρ (Matrix.of fun _ _ => c) γ))

def rn1 {k ρ m : ℕ} (e : ρ + 1 = m) (x : U.RC k 1 ρ) : B.Mat k m :=
  D.castM e (D.castM (Nat.add_comm 1 ρ) (U.Rn k 1 ρ x))

def lev1 {k ρ m : ℕ} (e : ρ + 1 = m) (y : B.Mat k ρ) : B.Mat k m :=
  D.castM e (D.castM (Nat.add_comm 1 ρ) (ιLev k 1 ρ y))

def JFStep : Prop :=
  ∀ (k ρ m : ℕ) (e : ρ + 1 = m) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (B1 : B.RealPlaceData k m Wp Wq) (B0 : B.RealPlaceData k ρ Wp Wq),
    B1.z = D.castV e (D.castV (Nat.add_comm 1 ρ) (liftVec k 1 ρ B0.z)) →
    B1.z' = D.castV e (D.castV (Nat.add_comm 1 ρ) (liftVec k 1 ρ B0.z')) →
    (∀ y : B.Mat k ρ, B0.π y = B1.π (lev1 e y)) → (∀ y : B.Mat k ρ, B0.π' y = B1.π' (lev1 e y)) →
    B1.μW Set.univ = 1 → B1.μW' Set.univ = 1 → B0.μW Set.univ = 1 → B0.μW' Set.univ = 1 →
    B1.μN = D.muN k m → B0.μN = D.muN k ρ →
    ∀ (f1 : B.Mat k m → (Wq →L[ℂ] Wp)) (f0 : B.Mat k ρ → (Wq →L[ℂ] Wp)) (c : ℂ), c ≠ 0 → KB.CptCoef B1 f1 →
    (∀ γ ∈ B.GV k ρ, f0 γ = ∫ xx : U.RC k 1 ρ × U.RC k 1 ρ,
        (psi k m B1.z cStd (rn1 e xx.1) * star (psi k m B1.z' cStd (rn1 e xx.2))) •
          f1 ((rn1 e xx.1)⁻¹ * mc e c γ * rn1 e xx.2) ∂((U.muRC k 1 ρ).prod (U.muRC k 1 ρ))) →
    ∀ γ ∈ B.GV k ρ, γ ∈ Q.OmPlus k ρ B0.z B0.z' →
      B.JF B0 f0 γ = B.JF B1 f1 (mc e c γ)

end Formalism.FourierDecayAlt.P.PBH

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

def PointStep : Prop :=
  ∀ (k j ρ : ℕ) (σ : Equiv.Perm (Fin j)) (d : Fin j → ℂ), (∀ i, d i ≠ 0) → ∀ (c : ℂ), c ≠ 0 →
    ∀ (zA zA' : Fin (2 * (j + 1 + ρ) + k + 1) → ℂ), inWb k (j + 1 + ρ) zA → inWb k (j + 1 + ρ) zA' →
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (F : B.Mat k (j + 1 + ρ) → E)
      (γ : B.Mat k ρ),
      Integrable (fun ξ : U.Xi k j 1 ρ σ =>
          U.psiStar k ρ σ zA zA' ξ • F (U.gaXi k ρ σ d ξ (fun _ _ => c) γ)) (U.muXi k j 1 ρ σ) →
      U.PhiFun k ρ σ d zA zA' F (fun _ _ => c) γ =
        ∫ yy : U.RC k 1 ρ × U.RC k 1 ρ,
          (psi k (1 + ρ) (U.lowV k j (1 + ρ) (D.castV (by omega : j + 1 + ρ = j + (1 + ρ)) zA)) cStd
              (U.Rn k 1 ρ yy.1) *
            star (psi k (1 + ρ) (U.lowV k j (1 + ρ) (D.castV (by omega : j + 1 + ρ = j + (1 + ρ)) zA')) cStd
              (U.Rn k 1 ρ yy.2))) •
          U.PhiFun (p := j) (s := 0) k (1 + ρ) σ d (D.castV (by omega : j + 1 + ρ = j + (1 + ρ)) zA)
            (D.castV (by omega : j + 1 + ρ = j + (1 + ρ)) zA') (D.castF (by omega : j + (1 + ρ) = j + 1 + ρ) F)
            (fun a => a.elim0)
            ((U.Rn k 1 ρ yy.1)⁻¹ * U.mMap k 1 ρ (Matrix.of fun _ _ => c) γ * U.Rn k 1 ρ yy.2)
          ∂((U.muRC k 1 ρ).prod (U.muRC k 1 ρ))

end Formalism.FourierDecayAlt.P.PBH
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGenTransferCut
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

section preds

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def GTHyp (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π')
    (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))) : Prop :=
  Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' ∧ 2 ≤ P.k ∧ CSec P.k P.r Bs.z Bs.z' Bs.μsec ∧
    Q.IsActualLevel X d.L ∧ Fr.IsStarLevel d.L ∧ d.Rel ∧ ∀ Y : ℂ, X.QQ Y = d.QQ Y

def FnF (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')))
    (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) : Prop :=
  ∀ Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π',
    trR P Bs e (d.L.ζ.1 Φ) = MA.actA P (MA.zA P (MA.DQ P)) (trR P Bs e Φ) ∧
    trR P Bs e (d.L.ζi.1 Φ) = MA.actA P (MA.ziA P (MA.DQ P)) (trR P Bs e Φ) ∧
    trR P Bs e (d.L.ζb.1 Φ) = MA.actA P (MA.zbA P (MA.DQ P)) (trR P Bs e Φ) ∧
    trR P Bs e (d.L.ζbi.1 Φ) = MA.actA P (MA.zbiA P (MA.DQ P)) (trR P Bs e Φ) ∧
    trR P Bs e (d.L.GG.1 Φ) = MA.actA P (MA.ggA P (MA.DQ P)) (trR P Bs e Φ) ∧
    trR P Bs e (d.L.GGi.1 Φ) = MA.actA P (MA.ggiA P (MA.DQ P)) (trR P Bs e Φ)

def KapF (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')))
    (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) : Prop :=
  ∀ (f : M.Ty P → ℂ) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'),
    trR P Bs e ((d.κ f).1 Φ) = MA.actA P (MA.kap P (MA.DQ P) f) (trR P Bs e Φ)

def NabF (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')))
    (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) : Prop :=
  ∀ Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π',
    trR P Bs e (d.L.nab.1 Φ) = MA.actA P (MA.nabA P (MA.DQ P)) (trR P Bs e Φ) ∧
    trR P Bs e (d.L.nabs.1 Φ) = MA.actA P (MA.nabsA P (MA.DQ P)) (trR P Bs e Φ)

def SSF (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')))
    (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) : Prop :=
  ∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π',
    trR P Bs e ((d.SS l).1 Φ) = MA.actA P (MA.SS P (MA.DQ P) l) (trR P Bs e Φ) ∧
    trR P Bs e ((star (d.SS l)).1 Φ) = MA.actA P (star (MA.SS P (MA.DQ P) l)) (trR P Bs e Φ)

end preds

def GTFn : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), FnF P Bs d e

def GTKap : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∃ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e ∧ KapF P Bs d e

def GTConn : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e → KapF P Bs d e →
      ∃ e' : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e' ∧ KapF P Bs d e' ∧ NabF P Bs d e'

def GTSS : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e → KapF P Bs d e → NabF P Bs d e →
      ∃ e' : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e' ∧ KapF P Bs d e' ∧ NabF P Bs d e' ∧ SSF P Bs d e'

def GenTransferOfCut : Prop := GTFn → GTKap → GTConn → GTSS → GenTransfer

theorem genTransfer_of_cut : GenTransferOfCut := by
  intro hFn hKap hConn hSS Wp Wq _ _ _ _ _ _ P Bs hpl hk hcs X d hL hS hR hQ
  have hyp : GTHyp P Bs X d := by
    unfold GTHyp
    exact ⟨hpl, hk, hcs, hL, hS, hR, hQ⟩
  obtain ⟨e₀, hf₀, hk₀⟩ := hKap Wp Wq P Bs X d hyp
  obtain ⟨e₁, hf₁, hk₁, hn₁⟩ := hConn Wp Wq P Bs X d hyp e₀ hf₀ hk₀
  obtain ⟨e, hf, hke, hne, hse⟩ := hSS Wp Wq P Bs X d hyp e₁ hf₁ hk₁ hn₁
  refine ⟨e, hf, fun Φ => ?_⟩
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆⟩ := hFn Wp Wq P Bs X d hyp e Φ
  obtain ⟨b₁, b₂⟩ := hne Φ
  exact ⟨a₁, a₂, a₃, a₄, a₅, a₆, b₁, b₂, fun f => hke f Φ, fun l hl => (hse l hl Φ).1,
    fun l hl => (hse l hl Φ).2⟩

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddOp
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA

open NumberField Formalism.FourierDecayAlt.P.CutMP

noncomputable section

section defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]

def BddReal (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (Cb : ℝ)
    (b : MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) : Prop :=
  ∃ Θ : (B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))), B.opOrder Θ = 0 ∧ IsAAOp S T v Θ ∧
    CutCoef S T v Θ 0 (Cb * ((S.G.r : ℝ) + 1)) ∧
    ∀ J ∈ smoothFormsPositiveCone S T v, B.opApply Θ J ∈ smoothFormsPositiveCone S T v ∧ B.opAdj Θ J ∈ smoothFormsPositiveCone S T v ∧
      MA.actA (D.parOf S v) b (trJ S T v e J) = trJ S T v e (B.opApply Θ J)

end defs

def scalSet (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r) : Set (MA.A P (MA.DQ P)) :=
  {L.ζi, L.ζbi, L.D * L.Dbi, L.Db * L.Di}

def ssnSet (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r) : Set (MA.A P (MA.DQ P)) :=
  (fun i => L.Drb * L.Dri * MA.SS P (MA.DQ P) i) '' Set.Icc 1 (P.k - 1)

def ssnStarSet (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r) : Set (MA.A P (MA.DQ P)) :=
  (fun i => star (L.Drb * L.Dri * MA.SS P (MA.DQ P) i)) '' Set.Icc 1 (P.k - 1)

def BddClassOp (cls : ∀ P : M.Par, R.LevelData (MA.A P (MA.DQ P)) P.r → Set (MA.A P (MA.DQ P))) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ Cc Cb : ℝ, K ≤ Cc → K ≤ Cb → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
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
      ∀ b ∈ cls (D.parOf S v) L, BddReal S T v e Cb b

def JABddScal : Prop := BddClassOp scalSet

theorem bddSet_cases (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r) (b : MA.A P (MA.DQ P))
    (hb : b ∈ MA.bddSet P L) :
    b ∈ scalSet P L ∨ b ∈ Set.range (MA.kap P (MA.DQ P)) ∨ b ∈ ssnSet P L ∨ b ∈ ssnStarSet P L := by
  unfold MA.bddSet at hb
  rcases hb with ((h | h) | h) | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

def JABddOpQQ : Prop :=
  ∃ Cc Cb : ℝ, 0 ≤ Cb ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
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
      IsFrame S T v e → IsGauge S T v e → IsGaugeQQ S T v e → MA.IsModelLevel (D.parOf S v) (MA.DQ (D.parOf S v)) L →
      ∀ b ∈ MA.bddSet (D.parOf S v) L, ∃ Θ : (B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))), B.opOrder Θ = 0 ∧ IsAAOp S T v Θ ∧
        CutCoef S T v Θ 0 (Cb * ((S.G.r : ℝ) + 1)) ∧
        ∀ J ∈ smoothFormsPositiveCone S T v, B.opApply Θ J ∈ smoothFormsPositiveCone S T v ∧ B.opAdj Θ J ∈ smoothFormsPositiveCone S T v ∧
          MA.actA (D.parOf S v) b (trJ S T v e J) = trJ S T v e (B.opApply Θ J)

def BddClassOpQQ (cls : ∀ P : M.Par, R.LevelData (MA.A P (MA.DQ P)) P.r → Set (MA.A P (MA.DQ P))) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ Cc Cb : ℝ, K ≤ Cc → K ≤ Cb → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
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
      IsFrame S T v e → IsGauge S T v e → IsGaugeQQ S T v e → MA.IsModelLevel (D.parOf S v) (MA.DQ (D.parOf S v)) L →
      ∀ b ∈ cls (D.parOf S v) L, BddReal S T v e Cb b

theorem bddClassOpQQ_of (cls : ∀ P : M.Par, R.LevelData (MA.A P (MA.DQ P)) P.r → Set (MA.A P (MA.DQ P)))
    (h : BddClassOp cls) : BddClassOpQQ cls := by
  obtain ⟨K, hK, h⟩ := h
  exact ⟨K, hK, fun Cc Cb h1 h2 E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e L hFr hGa _ hL =>
    h Cc Cb h1 h2 E Wp Wq S T f χ ν' m₀ top A₀ hB v e L hFr hGa hL⟩

def JABddKapQQ : Prop := BddClassOpQQ fun P _ => Set.range (MA.kap P (MA.DQ P))

def JABddSSnQQ : Prop := BddClassOpQQ ssnSet

def JABddSSnStarQQ : Prop := BddClassOpQQ ssnStarSet

theorem jABddOpQQ_of_bddLeaves (h1 : JABddScal) (h2 : JABddKapQQ) (h3 : JABddSSnQQ) (h4 : JABddSSnStarQQ) :
    JABddOpQQ := by
  obtain ⟨K1, hK1, h1⟩ := bddClassOpQQ_of scalSet h1
  obtain ⟨K2, hK2, h2⟩ := h2
  obtain ⟨K3, hK3, h3⟩ := h3
  obtain ⟨K4, hK4, h4⟩ := h4
  set K := max (max K1 K2) (max K3 K4) with hK
  have e1 : K1 ≤ K := le_trans (le_max_left _ _) (le_max_left _ _)
  have e2 : K2 ≤ K := le_trans (le_max_right _ _) (le_max_left _ _)
  have e3 : K3 ≤ K := le_trans (le_max_left _ _) (le_max_right _ _)
  have e4 : K4 ≤ K := le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨K, K, le_trans hK1 e1, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e L hFr hGa hQQ hL b hb
  rcases bddSet_cases _ L b hb with h | h | h | h
  · exact h1 K K e1 e1 E Wp Wq S T f χ ν' m₀ top A₀ hB v e L hFr hGa hQQ hL b h
  · exact h2 K K e2 e2 E Wp Wq S T f χ ν' m₀ top A₀ hB v e L hFr hGa hQQ hL b h
  · exact h3 K K e3 e3 E Wp Wq S T f χ ν' m₀ top A₀ hB v e L hFr hGa hQQ hL b h
  · exact h4 K K e4 e4 E Wp Wq S T f χ ν' m₀ top A₀ hB v e L hFr hGa hQQ hL b h

end

end Formalism.FourierDecayAlt.P.CutMP.JA
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutoffIteratedFDerivBounded
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.DminStarPd
open Matrix Set
open scoped ComplexConjugate ContDiff Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.AdmissibleLieWords

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

lemma gf_pd (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) :
    U.IsPolyDeg (2 * r + 2) (fun g : Mat k r => ((Gf k r z z' g : ℝ) : ℂ)) := by
  exact gram_function_polynomial k r z z'

section fac

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

lemma ubl_monoM (D : RealPlaceData k r Wp Wq) (L : Finset (Fin (r + 2))) (a b : Fin (r + 2) → ℕ) (c : ℕ)
    (hab : ∀ l, l ∉ L → l ≠ Fin.last (r + 1) → a l = 0 ∧ b l = 0) {S : Set (Mat k r)} (hSG : S ⊆ GV k r)
    {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hSD : ∀ g ∈ S, ∀ l, (l ∈ L ∨ l = Fin.last (r + 1)) → c₀ ≤ Complex.normSq (Dmin k r D.z D.z' g l))
    (hSGf : ∀ g ∈ S, c₀ ≤ Complex.normSq ((Gf k r D.z D.z' g : ℝ) : ℂ)) (n : ℕ) :
    UBL (C6.monoM D a b c) S n 0 (2 * r + 2) := by
  have hfac : ∀ l ∈ (Finset.univ : Finset (Fin (r + 2))),
      UBL (fun g => (Dmin k r D.z D.z' g l)⁻¹ ^ a l * (star (Dmin k r D.z D.z' g l))⁻¹ ^ b l)
        S n 0 (2 * r + 2) := by
    intro l _
    by_cases hl : l ∈ L ∨ l = Fin.last (r + 1)
    · have hl' : l.val ≤ 2 * r + 2 := by have := l.isLt; omega
      have h1 : UBL (fun g => (Dmin k r D.z D.z' g l)⁻¹ ^ a l) S n 0 (2 * r + 2) :=
        ubl_mono hSG (ubl_invpow (minor_polynomial_property k r D.z D.z' l) hSG hc₀
          (fun g hg => hSD g hg l hl) (a l) n) le_rfl hl'
      have h2 : UBL (fun g => (star (Dmin k r D.z D.z' g l))⁻¹ ^ b l) S n 0 (2 * r + 2) :=
        ubl_mono hSG (ubl_invpow (dmin_star_pd k r D.z D.z' l) hSG hc₀
          (fun g hg => by rw [Complex.star_def, Complex.normSq_conj]; exact hSD g hg l hl) (b l) n)
          le_rfl hl'
      exact ubl_mul hSG h1 h2
    · push_neg at hl
      obtain ⟨ha, hb⟩ := hab l hl.1 hl.2
      have e : (fun g => (Dmin k r D.z D.z' g l)⁻¹ ^ a l * (star (Dmin k r D.z D.z' g l))⁻¹ ^ b l) =
          fun _ => (1 : ℂ) := by
        funext g
        simp [ha, hb]
      rw [e]
      exact ubl_const 1 hSG n _
  have hP := ubl_prod hSG Finset.univ
    (fun l g => (Dmin k r D.z D.z' g l)⁻¹ ^ a l * (star (Dmin k r D.z D.z' g l))⁻¹ ^ b l) hfac
  have hG := ubl_invpow (gram_function_polynomial k r D.z D.z') hSG hc₀ hSGf c n
  exact ubl_mul hSG hP hG

private lemma rw_congr_on_open_of_eq_on_GV {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] {V : Set (Mat k r)}
    (hV : IsOpen V) {f f' : Mat k r → F} (he : ∀ g ∈ GV k r, g ∈ V → f g = f' g) :
    ∀ (w : List (Mat k r)), (∀ X ∈ w, inLie k r X) → ∀ g ∈ GV k r, g ∈ V → Rw w f g = Rw w f' g := by
  intro w
  induction w with
  | nil => intro _ g hg hgV; exact he g hg hgV
  | cons X w ih =>
    intro hw g hg hgV
    have ih' := ih (fun Y hY => hw Y (List.mem_cons_of_mem _ hY))
    show Dx (false, X) (Rw w f) g = Dx (false, X) (Rw w f') g
    rw [Dx_eq, Dx_eq]
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [crv_ev (x := (false, X)) hV hgV] with t ht
    exact ih' _ (crv_mem (x := (false, X)) (hw X (by simp)) hg t) ht

private lemma dw_const_smul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] (c : ℂ) (f : Mat k r → F) :
    ∀ w : List (Bool × Mat k r), Dw w (fun g => c • f g) = fun g => c • Dw w f g := by
  intro w
  induction w with
  | nil => rfl
  | cons x w ih =>
    funext g
    show Dx x (Dw w (fun g => c • f g)) g = c • Dx x (Dw w f) g
    rw [ih, Dx_eq, Dx_eq]
    first
    | exact deriv_const_smul_field c (f := fun t => Dw w f (crv x g t))
    | exact deriv_const_smul' (f := fun t => Dw w f (crv x g t)) c
    | simp [deriv_const_smul']

lemma ubl_fib (D : RealPlaceData k r Wp Wq) (E : Mat k r → C6.EndH Wp Wq) (hE : C6.FibBound D E) {ε : ℝ} (hε : 0 < ε)
    {S : Set (Mat k r)} (hS : ∀ g ∈ S, g ∈ GV k r ∧ ε ≤ Gf k r D.z D.z' g) (v : List (Mat k r))
    (hv : ∀ X ∈ v, inLie k r X) (n : ℕ) :
    UBL (Rw v E) S n (3 * (r + 1) * v.length) (3 * (r + 1)) := by
  obtain ⟨hE1, hE2⟩ := hE
  have hSsub : S ⊆ GPos D := fun g hg => ⟨(hS g hg).1, lt_of_lt_of_le hε (hS g hg).2⟩
  choose Cf hCf using fun i => hE2 ε hε i
  refine ⟨⟨|(v.map nz).prod| * ∑ j ∈ Finset.range (n + v.length + 1), |Cf j|, by positivity, ?_⟩, ?_⟩
  · intro w hw g hg
    obtain ⟨u, v', hu, hv', hlen, rfl⟩ := hw
    have hgGV := (hS g hg).1
    have hgε := (hS g hg).2
    have hX : 0 ≤ gN g := by
      first
      | positivity
      | (unfold gN; positivity)
      | (simp only [gN]; positivity)
    rw [Rw_scale v E, dw_const_smul, norm_smul]
    have hsplit : Dw (wL u ++ wR v') (Rw (v.map nrm) E) g = dLR u (v' ++ v.map nrm) E g := by
      rw [dLR_eq, Dw_append, Dw_append, Dw_wR, Dw_wR]
      rw [show Rw (v' ++ v.map nrm) E = Rw v' (Rw (v.map nrm) E) by simp only [Rw, List.foldr_append]]
    rw [hsplit]
    have hU : C6.UnitWords k r u (v' ++ v.map nrm) (u.length + (v' ++ v.map nrm).length) := by
      refine ⟨hu, fun X hX => ?_, rfl⟩
      rcases List.mem_append.1 hX with h | h
      · exact hv' X h
      · obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 h
        exact nrm_unit (hv Y hY)
    have hb := hCf (u.length + (v' ++ v.map nrm).length) u (v' ++ v.map nrm) hU g hgGV hgε
    have hlenw : (wL u ++ wR v').length = u.length + v'.length := by simp [wL, wR]
    have hexp : 3 * (r + 1) * (u.length + (v' ++ v.map nrm).length) =
        3 * (r + 1) * v.length + 3 * (r + 1) * (wL u ++ wR v').length := by
      rw [hlenw, List.length_append, List.length_map]; ring
    rw [hexp] at hb
    have hX' : 0 ≤ gN g ^ (3 * (r + 1) * v.length + 3 * (r + 1) * (wL u ++ wR v').length) :=
      pow_nonneg hX _
    have hi : u.length + (v' ++ v.map nrm).length < n + v.length + 1 := by
      rw [List.length_append, List.length_map]; omega
    have hCi : Cf (u.length + (v' ++ v.map nrm).length) ≤
        ∑ j ∈ Finset.range (n + v.length + 1), |Cf j| :=
      (le_abs_self _).trans (Finset.single_le_sum (f := fun j => |Cf j|)
        (fun j _ => abs_nonneg _) (Finset.mem_range.2 hi))
    have hnorm : ‖(((v.map nz).prod : ℝ) : ℂ)‖ = |(v.map nz).prod| := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    rw [hnorm]
    calc |(v.map nz).prod| * ‖dLR u (v' ++ v.map nrm) E g‖
        ≤ |(v.map nz).prod| * (Cf (u.length + (v' ++ v.map nrm).length) *
            gN g ^ (3 * (r + 1) * v.length + 3 * (r + 1) * (wL u ++ wR v').length)) :=
          mul_le_mul_of_nonneg_left hb (abs_nonneg _)
      _ ≤ |(v.map nz).prod| * ((∑ j ∈ Finset.range (n + v.length + 1), |Cf j|) *
            gN g ^ (3 * (r + 1) * v.length + 3 * (r + 1) * (wL u ++ wR v').length)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hCi hX') (abs_nonneg _)
      _ = _ := by ring
  · intro g₀ hg₀
    obtain ⟨f', hf', V, hV, hgV, he⟩ := lss_of_ckOn hE1 hSsub g₀ hg₀
    refine ⟨Rw v f', ?_, V, hV, hgV, fun g' hg' hg'V => rw_congr_on_open_of_eq_on_GV hV he v hv g' hg' hg'V⟩
    rw [← Dw_wR]
    exact cdw _ hf'

end fac

end Formalism.FourierDecayAlt.P.AdmissibleLieWords
end
end

open Matrix Set
open scoped ComplexConjugate ContDiff Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.AdmissibleLieWords

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

section fac

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

lemma ubl_epart (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (hfib : ∀ j, C6.FibBound D (fib j)) {ε : ℝ} (hε : 0 < ε) {S : Set (Mat k r)}
    (hS : ∀ g ∈ S, g ∈ GV k r ∧ ε ≤ Gf k r D.z D.z' g) (n : ℕ) :
    ∀ es : List (Fin nf × List (Mat k r)), (∀ e ∈ es, ∀ X ∈ e.2, inLie k r X) →
      UBL (C6.Epart fib es) S n (3 * (r + 1) * (es.map fun e => e.2.length).sum) (3 * (r + 1)) := by
  have hSG : S ⊆ GV k r := fun g hg => (hS g hg).1
  intro es
  induction es with
  | nil =>
    intro _
    have e0 : C6.Epart fib ([] : List (Fin nf × List (Mat k r))) = fun _ => 1 := by
      funext g
      simp [C6.Epart]
    rw [e0]
    simpa using ubl_const (1 : C6.EndH Wp Wq) hSG n (3 * (r + 1))
  | cons e es ih =>
    intro hes
    have hA := ubl_fib D (fib e.1) (hfib e.1) hε hS e.2 (hes e (by simp)) n
    have hB := ih (fun e' he' => hes e' (List.mem_cons_of_mem _ he'))
    have hL := ubl_clm ((ContinuousLinearMap.mul ℂ (C6.EndH Wp Wq)).restrictScalars ℝ) hSG hA
    have hAB := ubl_app hSG hL hB
    have e1 : C6.Epart fib (e :: es) =
        fun g => ((ContinuousLinearMap.mul ℂ (C6.EndH Wp Wq)).restrictScalars ℝ
          (Rw e.2 (fib e.1) g)) (C6.Epart fib es g) := by
      funext g
      simp [C6.Epart]
    rw [e1]
    convert hAB using 2
    simp only [List.map_cons, List.sum_cons]
    ring

lemma ubl_coefP (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (hfib : ∀ j, C6.FibBound D (fib j)) (L : Finset (Fin (r + 2))) {κ : ℕ} (P : Mat k r → ℂ)
    (a b : Fin (r + 2) → ℕ) (c : ℕ) (es : List (Fin nf × List (Mat k r))) (hP : U.IsPolyDeg κ P)
    (hab : ∀ l, l ∉ L → l ≠ Fin.last (r + 1) → a l = 0 ∧ b l = 0) (hes : ∀ e ∈ es, ∀ X ∈ e.2, inLie k r X)
    {ε : ℝ} (hε : 0 < ε) {S : Set (Mat k r)} (hS : ∀ g ∈ S, g ∈ GV k r ∧ ε ≤ Gf k r D.z D.z' g)
    {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hSD : ∀ g ∈ S, ∀ l, (l ∈ L ∨ l = Fin.last (r + 1)) → c₀ ≤ Complex.normSq (Dmin k r D.z D.z' g l))
    (hSGf : ∀ g ∈ S, c₀ ≤ Complex.normSq ((Gf k r D.z D.z' g : ℝ) : ℂ)) (n : ℕ) :
    UBL (fun g => (P g * C6.monoM D a b c g) • C6.Epart fib es g) S n
      (κ + 3 * (r + 1) * (es.map fun e => e.2.length).sum) (3 * (r + 1)) := by
  have hSG : S ⊆ GV k r := fun g hg => (hS g hg).1
  have hP' := ubl_poly hP S hSG n (3 * (r + 1))
  have hM := ubl_mono hSG (ubl_monoM D L a b c hab hSG hc₀ hSD hSGf n) le_rfl
    (show 2 * r + 2 ≤ 3 * (r + 1) by omega)
  have hPM := ubl_mul hSG hP' hM
  have hE := ubl_epart D fib hfib hε hS n es hes
  let Lm : ℂ →L[ℝ] (C6.EndH Wp Wq →L[ℂ] C6.EndH Wp Wq) :=
    (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℂ ℂ)
      (ContinuousLinearMap.id ℂ (C6.EndH Wp Wq))).restrictScalars ℝ
  have hA := ubl_clm Lm hSG hPM
  have hAE := ubl_app hSG hA hE
  have e1 : (fun g => (P g * C6.monoM D a b c g) • C6.Epart fib es g) =
      fun g => Lm (P g * C6.monoM D a b c g) (C6.Epart fib es g) := by
    funext g
    simp [Lm]
  rw [e1]
  simpa using hAE

end fac

section cut

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

end cut

end Formalism.FourierDecayAlt.P.AdmissibleLieWords
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.SectionDecomposition
namespace Formalism.FourierDecayAlt.P

theorem c2_section_decomp : Formalism.FourierDecayAlt.C2.SectionDecomp :=
  c2_section_decomp_of_pieces stabilizer_split stabilizer_pairs unipotent_radical_image upper_splitting standard_flag_property
    unipotent_map_frame zhat_equivalence c2_tau_mem

end Formalism.FourierDecayAlt.P
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.PBFCstmt
namespace Formalism.FourierDecayAlt.KB

open Finset Filter Topology NumberField MeasureTheory Matrix Formalism.QuantumDeterminants

noncomputable section

def SizeStdCpt : Prop :=
  P5.ThmPActualCpt → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : Pl P Wp Wq) (j : ℕ)
    (hj : j ≤ P.r) (w : List C.Letter) (ys : List ℝ),
    CutWord P p.l0 (plusW ys w) → CutWord P p.l0 (minusW ys w) → ys.Pairwise (fun y y' => 2 < |y - y'|) →
    (∀ y ∈ ys, 0 < (Wd.qw (M.qC P) (D.positionted w) y).re) ∧
    ∀ x x', (∀ e, CptCoef (p.T.bs j) (x e)) → (∀ e, CptCoef (p.T.bs j) (x' e)) →
      ‖pairJ (p.form j hj w) ys x x'‖ ^ 2 * (ys.map fun y : ℝ => (Wd.qw (M.qC P) (D.positionted w) y).re).prod ≤
        (p.form j hj (plusW ys w) x x).re * (p.form j hj (minusW ys w) x' x').re

def VIsoCpt : Prop :=
  P5.ThmPActualCpt → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : Pl P Wp Wq) (j : ℕ)
    (hj : j ≤ P.r) (w : List C.Letter), CutWord P p.l0 w →
    ∀ (s : ℂ) x x', (∀ e, CptCoef (p.T.bs j) (x e)) → (∀ e, CptCoef (p.T.bs j) (x' e)) →
      (∀ e, CptCoef (p.T.bs j) (waveG (p.T.bs j) s w x e)) ∧
      p.form j hj w (waveG (p.T.bs j) s w x) (waveG (p.T.bs j) s w x') = p.form j hj w x x'

end

end Formalism.FourierDecayAlt.KB
end
