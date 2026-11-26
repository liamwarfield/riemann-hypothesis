module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSTr
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsCompactZetaLe

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSH2
open MeasureTheory
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSH

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P.PBH

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section defs

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}

def cc (j : ℕ) (hj : j + 1 ≤ P.r) (t : ℂ) (c : Fin (P.r - (j + 1)) → ℂ) : Fin (P.r - j) → ℂ :=
  fun l => consC t c (Fin.cast (by omega) l)

def gi (j : ℕ) (hj : j + 1 ≤ P.r) (g : Mx P.k (P.r - (j + 1))) : Mx P.k (P.r - j) :=
  D.castM (by omega) (ιLev P.k 1 (P.r - (j + 1)) g)

def GoodFam (T : D.LevTower P.k P.r Wp Wq) (j : ℕ) (G : ℂ → B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp)) : Prop :=
  (∀ t₀ : ℂ, t₀ ≠ 0 → ∀ γ₀ ∈ B.GV P.k (P.r - (j + 1)), ∃ (U : Set (ℂ × B.Mat P.k (P.r - (j + 1))))
      (f : ℂ × B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp)), IsOpen U ∧ (t₀, γ₀) ∈ U ∧ ContDiffOn ℝ ∞ f U ∧
      ∀ p ∈ U, p.2 ∈ B.GV P.k (P.r - (j + 1)) → G p.1 p.2 = f p) ∧
  ∀ K : Set ℂ, IsCompact K → (∀ t ∈ K, t ≠ 0) → ∃ C : Set (B.Mat P.k (P.r - (j + 1))), IsCompact C ∧
    ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ K, ∀ γ, G t γ ≠ 0 → γ ∈ C ∧
      (γ ∈ B.GV P.k (P.r - (j + 1)) → ε ≤ Gf P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' γ)

def famP (j : ℕ) (G : ℂ → B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp)) (v : ℂ) :
    ℂ → B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp) :=
  fun t => (B.GV P.k (P.r - (j + 1))).indicator fun γ => fderiv ℝ (fun u : ℂ => G u γ) t v

def Rep (T : D.LevTower P.k P.r Wp Wq) (j : ℕ) (hj : j + 1 ≤ P.r)
    (Ψ : RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')
    (G : ℂ → B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp)) : Prop :=
  ∀ t : ℂ, t ≠ 0 → ∀ x ∈ DomR P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z',
    (Ψ : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) (cc j hj t x.1) (gi j hj x.2) =
      resG P.k (P.r - (j + 1)) (Fin.last _) (B.JF (T.bs (j + 1)) (G t)) x.1 x.2

def InC (T : D.LevTower P.k P.r Wp Wq) (j : ℕ) (hj : j + 1 ≤ P.r)
    (Ψ : RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π') : Prop :=
  ∃ G, GoodFam T j G ∧ Rep T j hj Ψ G

def sliceFam (T : D.LevTower P.k P.r Wp Wq) (j : ℕ) (hj : j + 1 ≤ P.r) (F : B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) :
    ℂ → B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp) :=
  fun t => (B.GV P.k (P.r - (j + 1))).indicator fun γ =>
    ((‖t‖ ^ (2 * (P.r - j) + P.k) : ℝ) : ℂ) • ∫ xx : U.RC P.k 1 (P.r - (j + 1)) × U.RC P.k 1 (P.r - (j + 1)),
      (psi P.k (P.r - j) (T.bs j).z cStd (rn1 (by omega : P.r - (j + 1) + 1 = P.r - j) xx.1) *
          star (psi P.k (P.r - j) (T.bs j).z' cStd (rn1 (by omega : P.r - (j + 1) + 1 = P.r - j) xx.2))) •
        F ((rn1 (by omega : P.r - (j + 1) + 1 = P.r - j) xx.1)⁻¹ * mc (by omega : P.r - (j + 1) + 1 = P.r - j) t γ *
          rn1 (by omega : P.r - (j + 1) + 1 = P.r - j) xx.2)
      ∂((U.muRC P.k 1 (P.r - (j + 1))).prod (U.muRC P.k 1 (P.r - (j + 1))))

end defs

def FamJFOK : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (T : D.LevTower P.k P.r Wp Wq) (j : ℕ) (G : ℂ → B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp)),
    GoodFam T j G → ∀ t : ℂ, t ≠ 0 → JFOKCpt (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (G t)

def FamAlg : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (T : D.LevTower P.k P.r Wp Wq) (j : ℕ) (G G' : ℂ → B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp)),
    GoodFam T j G → GoodFam T j G' → ∀ m : ℂ → ℂ, ContDiffOn ℝ ∞ m {t | t ≠ 0} →
      GoodFam T j (fun t γ => G t γ + G' t γ) ∧ GoodFam T j (fun t γ => m t • G t γ)

def FamDeriv : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (T : D.LevTower P.k P.r Wp Wq) (j : ℕ) (G : ℂ → B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp)),
    GoodFam T j G → ∀ v : ℂ, GoodFam T j (famP j G v)

def RepLin : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (T : D.LevTower P.k P.r Wp Wq), IsPlace P T.base.z T.base.z' T.base.π T.base.π' → D.TowerNormalised T →
    ∀ (j : ℕ), j + 1 ≤ P.r →
    IsPlace (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π' →
    ∀ (G G' : ℂ → B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp)), GoodFam T j G → GoodFam T j G' →
    ∀ t : ℂ, t ≠ 0 → ∀ (a : ℂ), ∀ x ∈ DomR P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z',
      resG P.k (P.r - (j + 1)) (Fin.last _) (B.JF (T.bs (j + 1)) (fun γ => G t γ + G' t γ)) x.1 x.2 =
          resG P.k (P.r - (j + 1)) (Fin.last _) (B.JF (T.bs (j + 1)) (G t)) x.1 x.2 +
            resG P.k (P.r - (j + 1)) (Fin.last _) (B.JF (T.bs (j + 1)) (G' t)) x.1 x.2 ∧
        resG P.k (P.r - (j + 1)) (Fin.last _) (B.JF (T.bs (j + 1)) (fun γ => a • G t γ)) x.1 x.2 =
          a • resG P.k (P.r - (j + 1)) (Fin.last _) (B.JF (T.bs (j + 1)) (G t)) x.1 x.2

def FamJFDeriv : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (T : D.LevTower P.k P.r Wp Wq), IsPlace P T.base.z T.base.z' T.base.π T.base.π' → D.TowerNormalised T →
    ∀ (j : ℕ), j + 1 ≤ P.r →
    IsPlace (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π' →
    ∀ (G : ℂ → B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp)), GoodFam T j G →
    ∀ t : ℂ, t ≠ 0 → ∀ x ∈ DomR P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z', ∀ v : ℂ,
      HasDerivAt (fun s : ℝ =>
          resG P.k (P.r - (j + 1)) (Fin.last _) (B.JF (T.bs (j + 1)) (G (t + (s : ℂ) * v))) x.1 x.2)
        (resG P.k (P.r - (j + 1)) (Fin.last _) (B.JF (T.bs (j + 1)) (famP j G v t)) x.1 x.2) 0

def CellTie : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (T : D.LevTower P.k P.r Wp Wq), IsPlace P T.base.z T.base.z' T.base.π T.base.π' → D.TowerNormalised T →
    ∀ (j : ℕ) (hj : j + 1 ≤ P.r),
    IsPlace (JC.parLev P j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' →
    IsPlace (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π' →
    ∀ t : ℂ, t ≠ 0 → ∀ x ∈ DomR P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z',
      (cc j hj t x.1, gi j hj x.2) ∈ DomR P.k (P.r - j) (T.bs j).z (T.bs j).z' ∧
        wCell P.k (P.r - (j + 1)) (Fin.last _) x.1 * x.2 ∈ B.GV P.k (P.r - (j + 1)) ∧
        wCell P.k (P.r - (j + 1)) (Fin.last _) x.1 * x.2 ∈ OmPlus P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z'

def SliceFamGood : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (T : D.LevTower P.k P.r Wp Wq), IsPlace P T.base.z T.base.z' T.base.π T.base.π' → D.TowerNormalised T →
    ∀ (j : ℕ) (hj : j + 1 ≤ P.r),
    IsPlace (JC.parLev P j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' →
    IsPlace (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π' →
    ∀ F : B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp), JFOKCpt (JC.parLev P j) (T.bs j).z (T.bs j).z' F →
      GoodFam T j (sliceFam T j hj F)

def SliceFamJF : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (T : D.LevTower P.k P.r Wp Wq), IsPlace P T.base.z T.base.z' T.base.π T.base.π' → D.TowerNormalised T →
    ∀ (j : ℕ) (hj : j + 1 ≤ P.r),
    IsPlace (JC.parLev P j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' →
    IsPlace (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π' →
    ∀ F : B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp), JFOKCpt (JC.parLev P j) (T.bs j).z (T.bs j).z' F →
    ∀ t : ℂ, t ≠ 0 → ∀ γ ∈ B.GV P.k (P.r - (j + 1)),
      γ ∈ OmPlus P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' →
      B.JF (T.bs (j + 1)) (sliceFam T j hj F t) γ =
        ((‖t‖ ^ (2 * (P.r - j) + P.k) : ℝ) : ℂ) • B.JF (T.bs j) F (mc (by omega : P.r - (j + 1) + 1 = P.r - j) t γ)

def OpClosed : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (T : D.LevTower P.k P.r Wp Wq), IsPlace P T.base.z T.base.z' T.base.π T.base.π' → D.TowerNormalised T →
    ∀ (j : ℕ) (hj : j + 1 ≤ P.r),
    IsPlace (JC.parLev P j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' →
    IsPlace (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π' →
    ∀ (X : ActualOps P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π') (i : Fin 6)
      (Ψ : RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'),
      InC T j hj Ψ → InC T j hj (X.op ⟨0, by omega⟩ i Ψ)

def BTlAdjoin : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (k r : ℕ)
    (z z' : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (π' : Mx k r → (Wq →L[ℂ] Wq))
    (X : ActualOps k r z z' π π') (L : R.LevelData (Pr (RadSp k r z z' π π')) r), IsActualLevel X L →
    ∀ (S : Type) [Fintype S] [DecidableEq S] (l : Fin r) (w : List (Wd.Letter ℂ S)) (a b : Wd.Ix S),
      (bTl L l w a b).1 ∈ Algebra.adjoin ℂ (Set.range (X.op l))

def UUiwScalar : Prop :=
  ∀ (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] (S : Type) [Fintype S] [DecidableEq S] (s : ℂ)
    (w : List (Wd.Letter ℂ S)) (a b : Wd.Ix S), Wd.UUiw (A := A) s w a b ∈ (⊥ : Subalgebra ℂ A)

end Formalism.FourierDecayAlt.P.CutSH
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapR
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField

noncomputable section

section defs

variable {k r : ℕ} {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

def dMul (d : (Fin r → ℂ) → ℂ) (Φ : Q.Fn k r X) : Q.Fn k r X := fun c g => d c • Φ c g

def drF (r : ℕ) : (Fin r → ℂ) → ℂ := fun c => ∏ a, c a

def drbF (r : ℕ) : (Fin r → ℂ) → ℂ := fun c => starRingEnd ℂ (∏ a, c a)

variable (k r)

def rhGrp (z z' : Fin (2 * r + k + 1) → ℂ) (y : ℂ) (Φ : Q.Fn k r X) : Q.Fn k r X :=
  dMul (drbF r) (Q.QL k r z z' (Fin.last r) y 1 0 (Q.crd (Q.cmp (Q.vAB r y r) 0) Φ) +
    Q.QL k r z z' (Fin.last r) y 1 1 (Q.crd (Q.cmp (Q.vAB r y r) 1) Φ))

def rhvGrp (z z' : Fin (2 * r + k + 1) → ℂ) (y : ℂ) (Φ : Q.Fn k r X) : Q.Fn k r X :=
  dMul (drF r) (Q.QL k r z z' (Fin.last r) y 0 1 (Q.crd (Q.cmp (Q.vABs r y r) 0) Φ) +
    Q.QL k r z z' (Fin.last r) y 1 1 (Q.crd (Q.cmp (Q.vABs r y r) 1) Φ))

end defs

def JDRGrp : Prop :=
  ∀ (Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ → ∀ v (y : ℝ),
      ∃ Θ Θv : B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)),
        PolyOp (2 * S.G.r + S.G.k + 1) ((S.G.r + 1) * (2 * S.G.r + S.G.k + 1)) Θ ∧
        PolyOp (2 * S.G.r + S.G.k + 1) ((S.G.r + 1) * (2 * S.G.r + S.G.k + 1)) Θv ∧
        B.Commutes (T v).base (B.GPos (T v).base) Θ ∧ B.Commutes (T v).base (B.GPos (T v).base) Θv ∧
        ∀ J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v),
          ∀ c ∈ OmX S.G.r, ∀ g ∈ Q.Glev S.G.k S.G.r (Fin.last S.G.r),
            Q.wCell S.G.k S.G.r (Fin.last S.G.r) c * g ∈ OmP S T v →
            Q.resG S.G.k S.G.r (Fin.last S.G.r) (B.opApply Θ J) c g =
                rhGrp S.G.k S.G.r (T v).base.z (T v).base.z' (y : ℂ) (Q.resG S.G.k S.G.r (Fin.last S.G.r) J) c g ∧
              Q.resG S.G.k S.G.r (Fin.last S.G.r) (B.opApply Θv J) c g =
                rhvGrp S.G.k S.G.r (T v).base.z (T v).base.z' (y : ℂ) (Q.resG S.G.k S.G.r (Fin.last S.G.r) J) c g

def JDRDrTr : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k →
    ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), Gauge.IsFrameB P Bs e →
    ∀ L : R.LevelData (MA.A P (MA.DQ P)) P.r, MA.IsModelLevel P (MA.DQ P) L →
    ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)), Gauge.FamR P Bs Dc Φ →
      (∀ ρ, MA.toSm P (Gauge.rawR P Bs.μsec e (dMul (drbF P.r) Φ) ρ) =
        MA.actA P L.Drb (fun ρ' => MA.toSm P (Gauge.rawR P Bs.μsec e Φ ρ')) ρ) ∧
      ∀ ρ, MA.toSm P (Gauge.rawR P Bs.μsec e (dMul (drF P.r) Φ) ρ) =
        MA.actA P L.Dr (fun ρ' => MA.toSm P (Gauge.rawR P Bs.μsec e Φ ρ')) ρ

def JDRModelV : Prop :=
  ∀ (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r), MA.IsModelLevel P (MA.DQ P) L → ∀ y : ℝ,
    (∀ b : Fin 2, Wd.v0 (MA.sites P (MA.DQ P)) (y : ℂ) b = L.Tprod (y : ℂ) b 0) ∧
    ∀ a : Fin 2, star (Wd.v0 (MA.sites P (MA.DQ P)) (y : ℂ) a) = L.Tvprod (y : ℂ) a 0

def JDRGrpP : Prop :=
  ∀ (Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ → ∀ v (y : ℝ),
      ∃ Θ : B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)),
        PolyOp (2 * S.G.r + S.G.k + 1) ((S.G.r + 1) * (2 * S.G.r + S.G.k + 1)) Θ ∧
        B.Commutes (T v).base (B.GPos (T v).base) Θ ∧
        ∀ J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v),
          ∀ c ∈ OmX S.G.r, ∀ g ∈ Q.Glev S.G.k S.G.r (Fin.last S.G.r),
            Q.wCell S.G.k S.G.r (Fin.last S.G.r) c * g ∈ OmP S T v →
            Q.resG S.G.k S.G.r (Fin.last S.G.r) (B.opApply Θ J) c g =
                rhGrp S.G.k S.G.r (T v).base.z (T v).base.z' (y : ℂ) (Q.resG S.G.k S.G.r (Fin.last S.G.r) J) c g

def JDRGrpM : Prop :=
  ∀ (Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ → ∀ v (y : ℝ),
      ∃ Θv : B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)),
        PolyOp (2 * S.G.r + S.G.k + 1) ((S.G.r + 1) * (2 * S.G.r + S.G.k + 1)) Θv ∧
        B.Commutes (T v).base (B.GPos (T v).base) Θv ∧
        ∀ J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v),
          ∀ c ∈ OmX S.G.r, ∀ g ∈ Q.Glev S.G.k S.G.r (Fin.last S.G.r),
            Q.wCell S.G.k S.G.r (Fin.last S.G.r) c * g ∈ OmP S T v →
            Q.resG S.G.k S.G.r (Fin.last S.G.r) (B.opApply Θv J) c g =
                rhvGrp S.G.k S.G.r (T v).base.z (T v).base.z' (y : ℂ) (Q.resG S.G.k S.G.r (Fin.last S.G.r) J) c g

theorem jDRGrp_of_halves (hP : JDRGrpP) (hM : JDRGrpM) : JDRGrp := by
  intro Cc E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v y
  obtain ⟨Θ, h1, h3, hR⟩ := hP Cc E Wp Wq S T f χ ν' m₀ top A₀ hB v y
  obtain ⟨Θv, h2, h4, hRv⟩ := hM Cc E Wp Wq S T f χ ν' m₀ top A₀ hB v y
  exact ⟨Θ, Θv, h1, h2, h3, h4, fun J hJ c hc g hg hcg => ⟨hR J hJ c hc g hg hcg, hRv J hJ c hc g hg hcg⟩⟩

section assembly

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem jdr_tr_at (hD : JDRDrTr) (hM : JDRModelV) (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (hk : 2 ≤ P.k) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (he : Gauge.IsFrameB P Bs e)
    (hQQ : ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)), Gauge.FamR P Bs Dc Φ →
      ∀ (Y : ℝ) (a b : Fin 2) (ρ : M.Ty P),
        MA.toSm P (Gauge.rawR P Bs.μsec e (Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (Y : ℂ) a b Φ) ρ) =
          MA.actA P (MA.QQr P (MA.DQ P) (Y : ℂ) a b) (fun ρ' => MA.toSm P (Gauge.rawR P Bs.μsec e Φ ρ')) ρ)
    (L : R.LevelData (MA.A P (MA.DQ P)) P.r) (hL : MA.IsModelLevel P (MA.DQ P) L)
    (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (hΦ : Gauge.FamR P Bs Dc Φ)
    (y : ℝ) :
    Gauge.VLem.trR P Bs.μsec e (rhGrp P.k P.r Bs.z Bs.z' (y : ℂ) Φ) =
        MA.actA P (RhM P L y) (Gauge.VLem.trR P Bs.μsec e Φ) ∧
      Gauge.VLem.trR P Bs.μsec e (rhvGrp P.k P.r Bs.z Bs.z' (y : ℂ) Φ) =
        MA.actA P (RhvM P L y) (Gauge.VLem.trR P Bs.μsec e Φ) := by
  have hV : Gauge.GVTr := by
    intro Wp Wq _ _ _ _ _ _ P Bs hpl hk e he Dc Φ hΦ Y b
    have h := Gauge.VLem.vab_ind hpl hk he Y P.r le_rfl Dc Φ hΦ
    rw [Gauge.VLem.sitesCommonSpace_v0_eq_Vp]
    fin_cases b
    · exact ⟨h.1.1, fun ρ => congrFun h.1.2 ρ⟩
    · exact ⟨h.2.1, fun ρ => congrFun h.2.2 ρ⟩
  have hV := fun b => hV Wp Wq P Bs hpl hk e he Dc Φ hΦ y b
  have hVs : Gauge.GVsTr := by
    intro Wp Wq _ _ _ _ _ _ P Bs hpl hk e he Dc Φ hΦ Y a
    have h := Gauge.VLem.vabs_ind hpl hk he Y P.r le_rfl Dc Φ hΦ
    rw [Gauge.VLem.sitesCommonSpace_v0_eq_Vp]
    fin_cases a
    · exact ⟨h.1.1, fun ρ => congrFun h.1.2 ρ⟩
    · exact ⟨h.2.1, fun ρ => congrFun h.2.2 ρ⟩
  have hVs := fun a => hVs Wp Wq P Bs hpl hk e he Dc Φ hΦ y a
  have hsm := fun (Dc' : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp))
    (hΨ : Gauge.FamR P Bs Dc' Ψ) => Gauge.raw_gauge_smoothness_holds Wp Wq P Bs hpl hk e he Dc' Ψ hΨ
  have hql := fun (Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (hΨ : Gauge.FamR P Bs Dc Ψ) (a b : Fin 2) =>
    Gauge.quadratic_local_family_holds Wp Wq P Bs hpl hk Dc Ψ hΨ y a b
  obtain ⟨hMv, hMs⟩ := hM P L hL y
  have hsum : ∀ (Ψ₀ Ψ₁ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)), Gauge.FamR P Bs Dc Ψ₀ → Gauge.FamR P Bs Dc Ψ₁ →
      Gauge.FamR P Bs Dc (Ψ₀ + Ψ₁) := fun _ _ h₀ h₁ => Gauge.VLem.famR_add h₀ h₁
  constructor
  · have hF0 := hql _ (hV 0).1 1 0
    have hF1 := hql _ (hV 1).1 1 1
    funext ρ
    show MA.toSm P (Gauge.rawR P Bs.μsec e (dMul (drbF P.r) _) ρ) = _
    rw [(hD Wp Wq P Bs hpl hk e he L hL Dc _ (hsum _ _ hF0 hF1)).1 ρ]
    have e1 : (fun ρ' => MA.toSm P (Gauge.rawR P Bs.μsec e
        (Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (y : ℂ) 1 0 (Q.crd (Q.cmp (Q.vAB P.r (y : ℂ) P.r) 0) Φ) +
          Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (y : ℂ) 1 1 (Q.crd (Q.cmp (Q.vAB P.r (y : ℂ) P.r) 1) Φ)) ρ')) =
        MA.actA P (MA.QQr P (MA.DQ P) (y : ℂ) 1 0 * L.Ar (y : ℂ) + MA.QQr P (MA.DQ P) (y : ℂ) 1 1 * L.Br (y : ℂ))
          (Gauge.VLem.trR P Bs.μsec e Φ) := by
      have := Gauge.VLem.trR_add Bs.μsec e _ _ (hsm _ _ hF0) (hsm _ _ hF1)
      unfold Gauge.VLem.trR at this
      rw [this, Gauge.actA_add, Gauge.actA_mul, Gauge.actA_mul, R.LevelData.Ar, R.LevelData.Br, ← hMv 0, ← hMv 1]
      congr 1
      · funext ρ'; rw [hQQ _ _ (hV 0).1 y 1 0 ρ']; congr 1; funext ρ''; exact (hV 0).2 ρ''
      · funext ρ'; rw [hQQ _ _ (hV 1).1 y 1 1 ρ']; congr 1; funext ρ''; exact (hV 1).2 ρ''
    rw [e1, ← Gauge.actA_mul]
    rfl
  · have hF0 := hql _ (hVs 0).1 0 1
    have hF1 := hql _ (hVs 1).1 1 1
    funext ρ
    show MA.toSm P (Gauge.rawR P Bs.μsec e (dMul (drF P.r) _) ρ) = _
    rw [(hD Wp Wq P Bs hpl hk e he L hL Dc _ (hsum _ _ hF0 hF1)).2 ρ]
    have e1 : (fun ρ' => MA.toSm P (Gauge.rawR P Bs.μsec e
        (Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (y : ℂ) 0 1 (Q.crd (Q.cmp (Q.vABs P.r (y : ℂ) P.r) 0) Φ) +
          Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (y : ℂ) 1 1 (Q.crd (Q.cmp (Q.vABs P.r (y : ℂ) P.r) 1) Φ)) ρ')) =
        MA.actA P (MA.QQr P (MA.DQ P) (y : ℂ) 0 1 * L.Avr (y : ℂ) + MA.QQr P (MA.DQ P) (y : ℂ) 1 1 * L.Bvr (y : ℂ))
          (Gauge.VLem.trR P Bs.μsec e Φ) := by
      have := Gauge.VLem.trR_add Bs.μsec e _ _ (hsm _ _ hF0) (hsm _ _ hF1)
      unfold Gauge.VLem.trR at this
      rw [this, Gauge.actA_add, Gauge.actA_mul, Gauge.actA_mul, R.LevelData.Avr, R.LevelData.Bvr, ← hMs 0, ← hMs 1]
      congr 1
      · funext ρ'; rw [hQQ _ _ (hVs 0).1 y 0 1 ρ']; congr 1; funext ρ''; exact (hVs 0).2 ρ''
      · funext ρ'; rw [hQQ _ _ (hVs 1).1 y 1 1 ρ']; congr 1; funext ρ''; exact (hVs 1).2 ρ''
    rw [e1, ← Gauge.actA_mul]
    rfl

end assembly

theorem jDCapR_of_parts (hG : JDRGrp) (hD : JDRDrTr) (hM : JDRModelV) : JDCapR := by
  intro Cc E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e L hFr hQQ hL y
  obtain ⟨Θ, Θv, h1, h2, h3, h4, hR⟩ := hG Cc E Wp Wq S T f χ ν' m₀ top A₀ hB v y
  refine ⟨Θ, Θv, h1, h2, h3, h4, fun J hJ => ?_⟩
  obtain ⟨hIB, -, -, -⟩ := hB
  obtain ⟨-, -, -, hIsB, -, -, -, -, -, -, hk, -⟩ := hIB
  have hpl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hIsB.2 v).2.2.2.1
  have hF := Gauge.tc_famR (D.parOf S v) (T v).base hpl J hJ
  obtain ⟨tR, tRv⟩ := jdr_tr_at hD hM (D.parOf S v) (T v).base hpl hk e hFr
    (fun Dc Φ hΦ Y a b ρ => hQQ Dc Φ hΦ Y a b ρ) L hL _ _ hF y
  have hJR : trJ S T v e J = Gauge.VLem.trR (D.parOf S v) (T v).base.μsec e
      (Q.resG S.G.k S.G.r (Fin.last S.G.r) J) := by
    funext ρ
    show MA.toSm _ (Gauge.rawJ (D.parOf S v) (T v).base e J ρ) = _
    rw [Gauge.tc_rawJ]
    rfl
  have hpt : ∀ (Θ' : B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))) (F : Q.Fn S.G.k S.G.r (Wq (S.pl v) →L[ℂ] Wp (S.pl v))),
      (∀ c ∈ OmX S.G.r, ∀ g ∈ Q.Glev S.G.k S.G.r (Fin.last S.G.r),
        Q.wCell S.G.k S.G.r (Fin.last S.G.r) c * g ∈ OmP S T v →
        Q.resG S.G.k S.G.r (Fin.last S.G.r) (B.opApply Θ' J) c g = F c g) →
      trJ S T v e (B.opApply Θ' J) = Gauge.VLem.trR (D.parOf S v) (T v).base.μsec e F := by
    intro Θ' F hF'
    funext ρ
    show MA.toSm _ (Gauge.rawJ (D.parOf S v) (T v).base e (B.opApply Θ' J) ρ) = _
    rw [Gauge.tc_rawJ]
    show MA.toSm _ _ = MA.toSm _ _
    congr 1
    funext q
    have hmu := Gauge.tc_mu (D.parOf S v) (T v).base hpl q
    simp only [Gauge.rawR]
    rw [hF' q.1.1 q.2.1 _ hmu.1 hmu.2]
  constructor
  · rw [hpt Θ _ (fun c hc g hg hcg => (hR J hJ c hc g hg hcg).1), hJR]
    exact tR
  · rw [hpt Θv _ (fun c hc g hg hcg => (hR J hJ c hc g hg hcg).2), hJR]
    exact tRv

end

end Formalism.FourierDecayAlt.P.CutMP
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.SfiniteOfHaar
open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.PTieJ

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

theorem haar_prop {k r : ℕ} {U : Set (B.Mat k r)} (hU : B2.IsClosedSubgroup U) {μ ν : Measure (Mt k r)}
    (hμ : B.IsHaarOn U μ) (hν : B.IsHaarOn U ν) : ∃ c : ℝ≥0∞, ν = c • μ := by
  obtain ⟨c, hc⟩ := Formalism.FourierDecayAlt.P.haar_measure_unique_up_to_scalar k r U μ ν hU hμ hν.conc hν.left hν.finite_compact
  exact ⟨c, by rw [hc, ENNReal.smul_def]⟩

theorem sfinite_of_haar {k r : ℕ} {U : Set (B.Mat k r)} {μ : Measure (Mt k r)} (h : B.IsHaarOn U μ) : SFinite μ := by
  have : IsFiniteMeasureOnCompacts μ := ⟨h.finite_compact⟩
  infer_instance

theorem jfScale : Formalism.FourierDecayAlt.P.PTie.JFScale := by
  intro k r Wp Wq _ _ _ _ Bs Bs' hz hz' hπ hπ'
  have hW := Bs.haarW
  have hW' := Bs.haarW'
  rw [hz] at hW
  rw [hz'] at hW'
  obtain ⟨a, ha⟩ := haar_prop (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r Bs'.z) Bs'.haarW hW
  obtain ⟨a', ha'⟩ := haar_prop (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r Bs'.z') Bs'.haarW' hW'
  obtain ⟨b, hb⟩ := haar_prop (Formalism.FourierDecayAlt.P.unipotent_radical_closed k r) Bs'.haarN Bs.haarN
  have := sfinite_of_haar Bs'.haarW
  have := sfinite_of_haar Bs'.haarW'
  have := sfinite_of_haar Bs'.haarN
  refine ⟨(((a * b) * (a' * b)).toReal : ℂ), fun F => ?_⟩
  funext g
  simp only [B.JF, Pi.smul_apply]
  rw [hz, hz', hπ, hπ', ha, ha', hb]
  unfold besselJ
  simp only [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
  rw [integral_smul_measure, Complex.coe_smul]
  congr 2
  ring

end Formalism.FourierDecayAlt.P.PTieJ

namespace Formalism.FourierDecayAlt.P

theorem jacquet_scaling : Formalism.FourierDecayAlt.P.PTie.JFScale := PTieJ.jfScale

end Formalism.FourierDecayAlt.P
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.TendstoIntUv
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate InnerProductSpace ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerB

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section HS

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem hs_add_left (A A' C : Wq →L[ℂ] Wp) : B.hsInner (A + A') C = B.hsInner A C + B.hsInner A' C := by
  have h : B.hsVec (A + A') = B.hsVec A + B.hsVec A' := by
    unfold B.hsVec; ext i; simp
  unfold B.hsInner
  rw [h, inner_add_right]

theorem hs_add_right (A C C' : Wq →L[ℂ] Wp) : B.hsInner A (C + C') = B.hsInner A C + B.hsInner A C' := by
  have h : B.hsVec (C + C') = B.hsVec C + B.hsVec C' := by
    unfold B.hsVec; ext i; simp
  unfold B.hsInner
  rw [h, inner_add_left]

theorem hs_smul_left (a : ℂ) (A C : Wq →L[ℂ] Wp) : B.hsInner (a • A) C = a * B.hsInner A C := by
  have h : B.hsVec (a • A) = a • B.hsVec A := by
    unfold B.hsVec; ext i; simp
  unfold B.hsInner
  rw [h, inner_smul_right]

theorem hs_smul_right (a : ℂ) (A C : Wq →L[ℂ] Wp) : B.hsInner A (a • C) = conj a * B.hsInner A C := by
  have h : B.hsVec (a • C) = a • B.hsVec C := by
    unfold B.hsVec; ext i; simp
  unfold B.hsInner
  rw [h, inner_smul_left]

end HS

section Lim

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

end Lim

end Formalism.FourierDecayAlt.P5.HerB
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCHolPhaseRel
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def qOne (P : M.Par) (ζ : ℂ) (hζ : ζ ∈ Ann P) : MA.Qp P.r P.TT :=
  ⟨(fun _ => (1 : ℂ), ζ), ⟨fun _ => one_ne_zero, hζ⟩⟩

theorem kap_orth (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π')
    (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))) (hyp : GTHyp P Bs X d)
    (e e0 : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (he : IsFrameB P Bs e) (hk : KapF P Bs d e)
    (he0 : IsFrameB P Bs e0) (hk0 : KapF P Bs d e0) (ρ σ : M.Ty P) (hσ : σ ≠ ρ) (ζ : ℂ) (hζ : ζ ∈ Ann P) :
    inner ℂ (B.hsVec (e σ ζ)) (B.hsVec (e0 ρ ζ)) = 0 := by
  have hpl := hyp.1
  have hk2 := hyp.2.1
  let F : M.Ty P → MA.SmQ P.r P.TT := fun τ => if τ = ρ then fnZ P (fun _ => (1 : ℂ)) else 0
  obtain ⟨Φ, hΦ, hΦv⟩ := SSTr.exists_tr P Bs hpl hk2 e0 he0 F
  let f : M.Ty P → ℂ := fun τ => if τ = ρ then 1 else 0
  have hfix : (d.κ f).1 Φ = Φ := by
    apply SSTr.trR_inj P Bs hpl hk2 e0 he0
    rw [hk0 f Φ, hΦ]
    funext τ
    rw [actA_kap]
    by_cases h : τ = ρ
    · simp [f, h]
    · simp [f, F, h]
  have hz : trR P Bs e Φ σ = 0 := by
    have h := congrFun (hk f Φ) σ
    rw [hfix, actA_kap] at h
    rw [h]
    simp [f, hσ]
  have hq := congrArg (fun g : MA.SmQ P.r P.TT => (g : MA.Qp P.r P.TT → ℂ) (qOne P ζ hζ)) hz
  simp only [ZeroMemClass.coe_zero, Pi.zero_apply] at hq
  rw [SSTr.trR_apply P Bs hpl hk2 e he Φ σ, rawR, hΦv] at hq
  have h1 : ((F ρ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) (qOne P ζ hζ) = 1 := by
    simp only [F, if_pos rfl, fnZ_eq_mk P (contDiffOn_const (c := (1 : ℂ)))]
  have hsum : inner ℂ (B.hsVec (e σ ζ)) (B.hsVec (∑ τ, ((((wR P.k P.TT ζ)⁻¹ : ℝ) : ℂ) *
      ((F τ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) (qOne P ζ hζ)) • e0 τ ζ)) =
      (((wR P.k P.TT ζ)⁻¹ : ℝ) : ℂ) * inner ℂ (B.hsVec (e σ ζ)) (B.hsVec (e0 ρ ζ)) := by
    rw [SSTr.hsVec_sum, inner_sum, Finset.sum_eq_single ρ]
    · rw [hsVec_smul, inner_smul_right, h1, mul_one]
    · intro τ _ hτ
      simp only [F, if_neg hτ, ZeroMemClass.coe_zero, Pi.zero_apply, mul_zero, zero_smul]
      rw [← zero_smul ℂ (0 : Wq →L[ℂ] Wp), hsVec_smul, zero_smul, inner_zero_right]
    · intro h; exact absurd (Finset.mem_univ ρ) h
  have hw := SSTr.wR_pos P (ζ := ζ) hζ
  change ((wR P.k P.TT ζ : ℝ) : ℂ) * inner ℂ (B.hsVec (e σ ζ)) (B.hsVec (∑ τ, ((((wR P.k P.TT ζ)⁻¹ : ℝ) : ℂ) *
      ((F τ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) (qOne P ζ hζ)) • e0 τ ζ)) = 0 at hq
  rw [hsum, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hw.ne', Complex.ofReal_one, one_mul] at hq
  exact hq

def hsCLM : (Wq →L[ℂ] Wp) →L[ℝ] PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp) :=
  (LinearMap.toContinuousLinearMap (SSTr.hsL (Wp := Wp) (Wq := Wq))).restrictScalars ℝ

theorem hsCLM_apply (A : Wq →L[ℂ] Wp) : hsCLM A = B.hsVec A := rfl

theorem e0_eq (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π')
    (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))) (hyp : GTHyp P Bs X d)
    (e e0 : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (he : IsFrameB P Bs e) (hk : KapF P Bs d e)
    (he0 : IsFrameB P Bs e0) (hk0 : KapF P Bs d e0) (ρ : M.Ty P) (ζ : ℂ) (hζ : ζ ∈ Ann P) :
    e0 ρ ζ = inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec (e0 ρ ζ)) • e ρ ζ := by
  obtain ⟨hfib0, -, -⟩ := (he0.2 ζ hζ)
  obtain ⟨-, -, hexp⟩ := he.2 ζ hζ
  conv_lhs => rw [hexp (e0 ρ ζ) (hfib0 ρ)]
  rw [Finset.sum_eq_single ρ]
  · intro σ _ hσ
    rw [kap_orth P Bs X d hyp e e0 he hk he0 hk0 ρ σ hσ ζ hζ, zero_smul]
  · intro h; exact absurd (Finset.mem_univ ρ) h

end

theorem phase_relation_holds : GTCPhaseRel := by
  intro Wp Wq _ _ _ _ _ _ P Bs X d hyp e e0 he hk he0 hk0
  refine ⟨fun ρ ζ => inner ℂ (B.hsVec (e0 ρ ζ)) (B.hsVec (e ρ ζ)), fun ρ => ⟨?_, ?_⟩, ?_⟩
  · have h1 := (hsCLM (Wp := Wp) (Wq := Wq)).contDiff.comp_contDiffOn (he0.1 ρ)
    have h2 := (hsCLM (Wp := Wp) (Wq := Wq)).contDiff.comp_contDiffOn (he.1 ρ)
    have h3 := h1.inner ℂ h2
    simp only [Function.comp_def, hsCLM_apply] at h3
    exact h3
  · intro ζ hζ
    have hrel := e0_eq P Bs X d hyp e0 e he0 hk0 he hk ρ ζ hζ
    have hn := ((he.2 ζ hζ).2.1 ρ ρ)
    rw [if_pos rfl] at hn
    set c := inner ℂ (B.hsVec (e0 ρ ζ)) (B.hsVec (e ρ ζ)) with hc
    have hn0 := ((he0.2 ζ hζ).2.1 ρ ρ)
    rw [if_pos rfl] at hn0
    rw [hrel, hsVec_smul, inner_smul_left, inner_smul_right, hn0, mul_one] at hn
    have h2 : ((‖c‖ ^ 2 : ℝ) : ℂ) = 1 := by
      rw [← hn, Complex.ofReal_pow, ← Complex.mul_conj', mul_comm]
    have h3 : ‖c‖ ^ 2 = 1 := by exact_mod_cast h2
    have h4 : 0 ≤ ‖c‖ := norm_nonneg c
    nlinarith [h3, h4]
  · intro ρ ζ hζ
    exact e0_eq P Bs X d hyp e0 e he0 hk0 he hk ρ ζ hζ

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSAdjH
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt MeasureTheory

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.SSAdjH

open Formalism.FourierDecayAlt.P.CutMP.Gauge.GC Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.NFx4

noncomputable section

section pt

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem hsVec_zero' : B.hsVec (0 : Wq →L[ℂ] Wp) = 0 := by
  unfold B.hsVec
  ext i
  simp

theorem rawR_smul (P : M.Par) (μsec : ℂ → Matrix (Fin (P.k + 1)) (Fin (P.k + 1)) ℂ) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (a : ℂ) (Z : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (ρ : M.Ty P) (q : MA.Qp P.r P.TT) :
    rawR P μsec e (a • Z) ρ q = a * rawR P μsec e Z ρ q := by
  have hs : ∀ A : Wq →L[ℂ] Wp, B.hsVec (a • A) = a • B.hsVec A := by
    intro A
    unfold B.hsVec
    ext i
    simp
  simp only [rawR, Pi.smul_apply, hs, inner_smul_right]
  ring

theorem rawR_zero (P : M.Par) (μsec : ℂ → Matrix (Fin (P.k + 1)) (Fin (P.k + 1)) ℂ) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (ρ : M.Ty P) (q : MA.Qp P.r P.TT) :
    rawR P μsec e (0 : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ q = 0 := by
  simp only [rawR, Pi.zero_apply, hsVec_zero', inner_zero_right, mul_zero]

theorem smQ_sum_apply (P : M.Par) (x : M.Ty P → MA.SmQ P.r P.TT) (q : MA.Qp P.r P.TT) :
    ((∑ σ, x σ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q = ∑ σ, ((x σ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q := by
  simp only [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]

variable (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (hk2 : 2 ≤ P.k)
  (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (he : IsFrameB P Bs e)

include hpl hk2 he

theorem kap_pt (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))) (hk : KapF P Bs d e)
    (f : M.Ty P → ℂ) (Z : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (σ : M.Ty P) (q : MA.Qp P.r P.TT) :
    rawR P Bs.μsec e (((d.κ f).1 Z : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) σ q =
      f σ * rawR P Bs.μsec e (Z : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) σ q := by
  have h := congrArg (fun x : M.Ty P → MA.SmQ P.r P.TT => ((x σ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q) (hk f Z)
  simp only [actA_kap] at h
  rw [← SSTr.trR_apply P Bs hpl hk2 e he, h, ← SSTr.trR_apply P Bs hpl hk2 e he]
  rfl

theorem ss_pt (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))) (s t : ℕ → M.Ty P → M.Ty P → ℂ → ℂ)
    (hst : SmST P s t) (hL : SSLoc P Bs d e s t) {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1))
    (Z : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (ρ' : M.Ty P) (q : MA.Qp P.r P.TT) :
    rawR P Bs.μsec e (((d.SS l).1 Z : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ' q =
        ∑ σ, s l ρ' σ q.1.2 * rawR P Bs.μsec e (Z : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) σ q ∧
      rawR P Bs.μsec e (((star (d.SS l)).1 Z : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ' q =
        ∑ σ, t l ρ' σ q.1.2 * rawR P Bs.μsec e (Z : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) σ q := by
  obtain ⟨h1, h2⟩ := hL l hl Z ρ'
  constructor
  · rw [← SSTr.trR_apply P Bs hpl hk2 e he, h1, smQ_sum_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Subalgebra.coe_mul, Pi.mul_apply, fnZ_val P (hst l ρ' σ).1, SSTr.trR_apply P Bs hpl hk2 e he]
  · rw [← SSTr.trR_apply P Bs hpl hk2 e he, h2, smQ_sum_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Subalgebra.coe_mul, Pi.mul_apply, fnZ_val P (hst l ρ' σ).2, SSTr.trR_apply P Bs hpl hk2 e he]

theorem sec_expand (Z : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (q : MA.Qp P.r P.TT) :
    (Z : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1 (NF.muZ P.k P.r Bs.μsec q.1.2) =
      ∑ σ, ((((wR P.k P.TT q.1.2)⁻¹ : ℝ) : ℂ) * rawR P Bs.μsec e (Z : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) σ q) •
        e σ q.1.2 := by
  have hq : (q.1 : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' := (SSTr.qr_iff P Bs hpl _).2 q.2
  have hmem := Formalism.FourierDecayAlt.P.radical_reduction_mem Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' (SSTr.radBase P Bs hpl)
    (Z : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) Z.2
  have hF := hmem.2.1 _ hq
  simp only [NF.radR, Set.indicator_of_mem hq] at hF
  have hζ : P.TT < Complex.normSq q.1.2 := q.2.2
  obtain ⟨-, -, hexp⟩ := he.2 q.1.2 hζ
  conv_lhs => rw [hexp _ hF]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  have hw := SSTr.wR_pos P hζ
  simp only [rawR]
  rw [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hw.ne', Complex.ofReal_one, one_mul]

theorem hs_pair (Z W : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (q : MA.Qp P.r P.TT) :
    (((wR P.k P.TT q.1.2 ^ 2 : ℝ)) : ℂ) *
        inner ℂ (B.hsVec ((Z : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1 (NF.muZ P.k P.r Bs.μsec q.1.2)))
          (B.hsVec ((W : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1 (NF.muZ P.k P.r Bs.μsec q.1.2))) =
      ∑ σ, star (rawR P Bs.μsec e (Z : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) σ q) *
        rawR P Bs.μsec e (W : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) σ q := by
  rw [sec_expand P Bs hpl hk2 e he W q, SSTr.hsVec_sum, inner_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hw := (SSTr.wR_pos P (q.2.2 : P.TT < Complex.normSq q.1.2)).ne'
  rw [hsVec_smul, inner_smul_right]
  have hc : star (rawR P Bs.μsec e (Z : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) σ q) =
      ((wR P.k P.TT q.1.2 : ℝ) : ℂ) *
        inner ℂ (B.hsVec ((Z : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1 (NF.muZ P.k P.r Bs.μsec q.1.2))) (B.hsVec (e σ q.1.2)) := by
    simp only [rawR]
    rw [star_mul', Complex.star_def, Complex.conj_ofReal, inner_conj_symm]
  rw [hc]
  have hw' : ((wR P.k P.TT q.1.2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hw
  push_cast
  field_simp

theorem exists_proj (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))) (hk : KapF P Bs d e)
    (f : ℂ → ℂ) (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Ann P)) (ρ : M.Ty P) :
    ∃ Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π',
      (∀ σ (q : MA.Qp P.r P.TT), rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) σ q =
        (if σ = ρ then 1 else 0) * f q.1.2) ∧ (NO.Pj d ρ).1 Φ = Φ := by
  obtain ⟨Φ0, hΦ0, -⟩ := SSTr.exists_tr P Bs hpl hk2 e he (fun _ => fnZ P f)
  refine ⟨(NO.Pj d ρ).1 Φ0, fun σ q => ?_, ?_⟩
  · show rawR P Bs.μsec e
        (((d.κ (fun ρ' => if ρ' = ρ then (1 : ℂ) else 0)).1 Φ0 : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :
          Q.Fn P.k P.r (Wq →L[ℂ] Wp)) σ q = _
    rw [kap_pt P Bs hpl hk2 e he d hk, ← SSTr.trR_apply P Bs hpl hk2 e he, hΦ0, fnZ_val P hf]
  · show ((NO.Pj d ρ) * (NO.Pj d ρ)).1 Φ0 = _
    rw [NO.Pj_idem]

end pt

theorem pt_of_tests {U : Set ℂ} (hU : IsOpen U) {H : ℂ → ℂ} (hH : ContinuousOn H U)
    (h : ∀ φ : ℂ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
      ∫ ζ, φ ζ • H ζ = 0) :
    ∀ ζ0 ∈ U, H ζ0 = 0 := by
  have hae := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume) (hH.locallyIntegrableOn hU.measurableSet) h
  intro ζ0 hζ0
  by_contra hne
  have hc : ContinuousAt H ζ0 := hH.continuousAt (hU.mem_nhds hζ0)
  have hev : ∀ᶠ x in nhds ζ0, H x ≠ 0 ∧ x ∈ U := (hc.eventually_ne hne).and (hU.mem_nhds hζ0)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  have hpos := Metric.measure_ball_pos (volume : Measure ℂ) ζ0 hδ
  rw [ae_iff] at hae
  apply hpos.ne'
  apply measure_mono_null _ hae
  intro x hx
  have := hball x hx
  simp only [Set.mem_setOf_eq, not_forall, exists_prop]
  exact ⟨this.2, this.1⟩

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.SSAdjH
end
