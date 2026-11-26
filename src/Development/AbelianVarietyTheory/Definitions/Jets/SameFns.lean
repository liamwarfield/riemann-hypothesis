module

public import Formalism.HermitianCurvature.StatementTL
public import Formalism.HermitianCurvature.StatementTBB
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.Jets.SameFns
namespace GlobalTheory.HatNF

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory

noncomputable section

section alg

variable {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]

def hats {r : ℕ} (L : LevelData A r) : Set A :=
  Set.range L.Ahat ∪ Set.range L.R0 ∪ Set.range L.Ahatv ∪ Set.range L.R0v

def SameFns {r : ℕ} (L L' : LevelData A r) : Prop :=
  L.p = L'.p ∧ L.pb = L'.pb ∧ L.c = L'.c ∧ L.ci = L'.ci ∧ L.cb = L'.cb ∧ L.cbi = L'.cbi ∧ L.ζ = L'.ζ ∧ L.ζi = L'.ζi ∧
    L.ζb = L'.ζb ∧ L.ζbi = L'.ζbi ∧ L.GG = L'.GG ∧ L.GGi = L'.GGi ∧ L.TT = L'.TT

def MulRel {r : ℕ} (L : LevelData A r) (m : ℕ → A) : Prop :=
  ∀ q, (∀ f ∈ L.fns, Commute f (m q)) ∧ (∀ l, L.p l * m q = m q * L.p l + m (q + 1)) ∧
    (∀ l, L.pb l * m q = m q * L.pb l + m (q + 1)) ∧
    L.nab * m q = m q * L.nab + L.ζb * L.GGi * m (q + 1) ∧
    L.nabs * m q = m q * L.nabs - L.ζ * L.GGi * m (q + 1)

variable {P : M.Par}

def ssn (d : Q.NFData P A) (l : ℕ) : A := d.L.Drb * d.L.Dri * d.SS l

def bset (d : Q.NFData P A) : Set A :=
  {d.L.ζi, d.L.ζbi, d.L.D * d.L.Dbi, d.L.Db * d.L.Di} ∪ Set.range d.κ ∪
    ssn d '' Set.Icc 1 (P.k - 1) ∪ (fun l => star (ssn d l)) '' Set.Icc 1 (P.k - 1)

def bmon (d : Q.NFData P A) : Submonoid A := Submonoid.closure (bset d)

def HatHyp (d : Q.NFData P A) : Prop :=
  P.OK ∧ IsStarLevel d.L ∧ d.Rel ∧ (∀ l, star (d.L.p l) = -d.L.pb l) ∧ (∀ l, star (d.L.c l) = d.L.cb l) ∧
    (∀ l, star (d.L.ci l) = d.L.cbi l) ∧ ∀ f : M.Ty P → ℂ, ∀ g ∈ TL.siteOps d.L, Commute (d.κ f) g

def Comparison₂ (d : Q.NFData P A) (L : LevelData A P.r) (st : Start A) (s : ℂ) : Prop :=
  TL.AHyp L st ∧ SameFns L d.L ∧ (s = 1 ∨ s = -1) ∧ (∀ Y, st.QQ Y = s • d.QQ Y) ∧
    st.inv = {Y | ∀ ρ : M.Ty P, M.xC P ρ Y ≠ 0}

def nfSpan (d : Q.NFData P A) (T : Set A) (i j n : ℕ) : Submodule ℂ A :=
  Submodule.span ℂ {x | ∃ b ∈ bmon d, ∃ H : List A, H.length = n ∧ (∀ h ∈ H, h ∈ T) ∧
    x = b * d.L.Di ^ i * TL.gI d.L ^ j * H.prod}

def rh (d : Q.NFData P A) (y : ℂ) : A := d.L.Drb * (d.QQ y 1 0 * d.L.Ar y + d.QQ y 1 1 * d.L.Br y)

def rhv (d : Q.NFData P A) (y : ℂ) : A := d.L.Dr * (d.QQ y 0 1 * d.L.Avr y + d.QQ y 1 1 * d.L.Bvr y)

def basics (d : Q.NFData P A) : Set A :=
  {x | ∃ y : ℝ, (∀ ρ : M.Ty P, M.xC P ρ (y : ℂ) ≠ 0 ∧ M.xC P ρ ((y : ℂ) - 1) ≠ 0 ∧ M.xC P ρ ((y : ℂ) + 1) ≠ 0) ∧
    (x = d.L.Ahat y ∨ x = d.L.Ahatv y ∨ x = rh d y ∨ x = rhv d y)}

end alg

section actual

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

abbrev RA (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) : Type := Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')

def nv {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq} (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')
    (x : (Fin P.r → ℂ) × Q.Mx P.k P.r) : ℝ :=
  ‖B.hsVec ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2)‖

def IsNF {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq} (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π')
    (d : Q.NFData P (RA P Bs)) : Prop :=
  Q.IsActualLevel X d.L ∧ IsStarLevel d.L ∧ d.Rel ∧ ∀ Y : ℂ, X.QQ Y = d.QQ Y

def PtB (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (b : RA P Bs) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π', ∀ x ∈ Q.DomR P.k P.r Bs.z Bs.z',
    nv (b.1 Φ) x ≤ C * nv Φ x

def PtAdj (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (b : RA P Bs) : Prop :=
  ∀ Φ Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π', ∀ x ∈ Q.DomR P.k P.r Bs.z Bs.z',
    B.hsInner ((b.1 Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2) ((Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2) =
      B.hsInner ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2) (((star b).1 Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2)

def gR (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (c : Fin P.r → ℂ) (g : Q.Mx P.k P.r) : ℝ :=
  Complex.normSq (∏ a, c a) * Q.GGl P.k P.r Bs.z Bs.z' g

def dR (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (c : Fin P.r → ℂ) (g : Q.Mx P.k P.r) : ℝ :=
  ‖(∏ a, c a) * P5.zeta P.k P.r Bs.z Bs.z' g‖

def IsMulG (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (φ : ℝ → ℝ)
    (W : ℕ → Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) : Prop :=
  ∀ q, P5.multiplicationOperator (W q) fun c g => ((LE.ld q φ (gR P Bs c g) : ℝ) : ℂ)

end actual

end

end GlobalTheory.HatNF
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Jets.ImportsAlt
namespace GlobalTheory.TopVec

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

noncomputable section

def tv {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (c : Fin (P.r + 1) → ℂ) :
    PiLp 2 (fun _ : Wd.Ix (Fin w.length) × M.Ty P => PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp)) :=
  WithLp.toLp 2 fun x =>
    ((Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c)) *
        Top.dH P p.l0 (TBB.TTp p) w (TBB.bigPt P.r c) x.1 x.2 : ℝ) : ℂ) •
      B.hsVec ((p.TP.E x.2).comp (p.V (p.Θ.Θ w x.1 H) (TBB.bigPt P.r c)))

end

end GlobalTheory.TopVec
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Jets.SupWOfSup
open Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace BpJoin

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData BranchingSupport

def Pst {n : ℕ} (lam : Fin n → ℝ) (c : ℝ) (y : ℝ) : ℝ := ∏ s, (|y + lam s| + c)

def GridNum (C b c : ℝ) (P : M.Par) (l : ℕ) (lam : Fin (2 * P.r + P.k + 1) → ℝ) : Prop :=
  1 ≤ c ∧ c + 2 ≤ b ∧ (P.k : ℝ) ≤ b ∧ |P.u l| ≤ b ∧ |P.u' l| ≤ b ∧ (∀ s, |lam s| ≤ b) ∧
  (∀ s t, s < t → lam t + 2 * c ≤ lam s) ∧
  (∀ s : Fin (2 * P.r + P.k + 1), s.val + 2 ≤ P.k →
    (s.val + 1 ≠ l → lam s + 1 / 2 ≤ P.u (s.val + 1)) ∧ (s.val + 2 ≠ l → P.u (s.val + 2) + 1 / 2 ≤ lam s)) ∧
  (∀ s : Fin (2 * P.r + P.k + 1), s.val + 2 ≤ P.k →
    (s.val + 1 ≠ l → lam s + 1 / 2 ≤ P.u' (s.val + 1)) ∧ (s.val + 2 ≠ l → P.u' (s.val + 2) + 1 / 2 ≤ lam s)) ∧
  b ^ (-(C * ((2 * P.r + 2 : ℕ) : ℝ))) ≤ P.T ∧ b ^ (-(C * ((2 * P.r + 2 : ℕ) : ℝ))) ≤ P.T'

def StdNum (C b c : ℝ) (P : M.Par) (lam : Fin (2 * P.r + P.k + 1) → ℝ) : Prop :=
  (∀ l ∈ Icc 1 P.k, GridNum C b c P l lam) ∧
  (∀ s : Fin (2 * P.r + P.k + 1), s.val + 2 ≤ P.k →
    lam s + 1 / 2 ≤ P.u (s.val + 1) ∧ P.u (s.val + 2) + 1 / 2 ≤ lam s ∧
    lam s + 1 / 2 ≤ P.u' (s.val + 1) ∧ P.u' (s.val + 2) + 1 / 2 ≤ lam s)

def Cases (P : M.Par) (n₀ : ℕ) : Prop :=
  (n₀ = 0 ∧ ∃ l ∈ Icc 1 P.k, ((30 * (P.r + 1) ^ 2 + 6 : ℕ) : ℝ) ≤ |P.u l - P.u' l|) ∨
  (n₀ = 30 * (P.r + 1) ^ 2 + 6 ∧ (∀ i ∈ Icc 1 P.k, P.u i = P.u' i) ∧
    ∃ l, 1 ≤ l ∧ l < P.k ∧ 2 * (n₀ : ℝ) + 1 ≤ P.u' l - P.u' (l + 1))

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def EigDec {k r : ℕ} (f : B.Mat k r → (Wq →L[ℂ] Wp)) (A : ℝ) (mu : Fin (2 * r + k + 1) → ℝ) : Prop :=
  B.CkOn ⊤ (B.GV k r) f ∧ (∀ m : ℕ, B.InCC A m f) ∧
    ∀ y : ℝ, ∀ g ∈ B.GV k r, Q.CV k r (y : ℂ) f g = ((∏ s, (y + mu s) : ℝ) : ℂ) • f g

end BpJoin
end
end
