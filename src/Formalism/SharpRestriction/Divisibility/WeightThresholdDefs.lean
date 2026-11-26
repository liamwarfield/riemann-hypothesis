module

public import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
public import Formalism.SharpRestriction.CuspSpanNormBounds.PlaceDegreeData

@[expose] public section

section -- merged from Formalism.SharpRestriction.Divisibility.WeightThresholdDefs
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.WeightThresholdDefs

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.DegreeFormula

open Classical

def dE (D : D7) : ℕ := (NumberField.discr D.host.E).natAbs

section Derived
variable {D : D7} (Y : ShimX D.what₂.Tau)

abbrev dimY : ℕ := dimFl D.what₂.Tau Y.N

def gap (lam : D.what₂.Tau → Fin Y.N → ℝ) (τ : D.what₂.Tau) : ℝ :=
  lam τ ⟨Y.j - 1, by have := Y.j_lt; omega⟩ - lam τ ⟨Y.j, Y.j_lt⟩

def supAbs (lam : D.what₂.Tau → Fin Y.N → ℝ) : ℝ := ⨆ x : Rt D.what₂.Tau Y.N, |lam x.1 x.2|

def bigB0 (u : D.what₂.Tau → Fin Y.N → ℝ) (g : ℝ) : ℝ :=
  4 * (D.R.f : ℝ) * (Y.N : ℝ) ^ 2 * (1 + supAbs Y u / g)

end Derived

def cP (p : ℕ) : ℝ := 1 / ((p : ℝ) - 1)

variable {D : D7} (V : DivX D) (P : DIV.Align.PrinLev V)

def TrivialFlagIntersectionCond : Prop := ∀ S κ, HidaSetting D V S κ → DIV.Align.LevB P κ → ∀ (Sx : Finset ℕ) (R : ℝ) (p : ℕ), p.Prime →
  ∀ (τ : D.what₂.Tau) (k : ℕ), 1 ≤ k → ∀ Q : MvPolynomial (Rt D.what₂.Tau (V.shv S κ).N) ℝ,
    (V.shv S κ).arMix Sx R p (tagHT D.what₂.Tau _ (pk D _ τ k) *
      (tagDR D.what₂.Tau _ Q - tagHT D.what₂.Tau _ Q)) = 0

structure Loc4 where

  dRho : V.Surf → ℕ
  dRho_pos : ∀ t, 0 < dRho t

  CHr : V.Surf → Type
  instCHr : ∀ t, AddCommGroup (CHr t)

  ch2 : ∀ t, CHr t

  ch2o : ∀ t, CHr t

  arithFirstChernHom : ∀ t, ℝ →+ CHr t

  degA : ∀ t, CHr t →+ ℝ

attribute [instance] Loc4.instCHr

section Fam
variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (PL : DIV.Align.PrinLevF Fm)

end Fam

end Formalism.MainNotions.WeightThresholdDefs

end
end

section -- merged from Formalism.SharpRestriction.Divisibility.InnerProductFormulaField
noncomputable section

namespace Formalism.MainNotions.InnerProductFormulaField

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Finset MeasureTheory
open Formalism.MainNotions.ZetaProductPairs (qE zetaProd idxPar Lpair)
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

abbrev Pl (D : D7) : Type := HeightOneSpectrum (𝓞 D.host.F)

structure Loc (D : D7) where

  Sg : Finset (Pl D)
  mem_Sg : ∀ v, v ∈ Sg ↔ ∃ i, ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal

  ZgCh : D.what₂.Tup → ℕ → D.what₂.FT → Pl D → ℂ
  ZgSb : D.what₂.Tup → ℕ → D.what₂.FT → Pl D → ℂ

  idxgCh : D.what₂.Tup → ℕ → Pl D → ℕ
  idxgSb : D.what₂.Tup → ℕ → Pl D → ℕ

  cCh : ℕ → ℝ
  cSb : ℕ → ℝ

  ZChR : ℕ → ℝ

  ZSbR : ℕ → ℝ

  nT : ℕ → ℝ

  massCh : ℕ → ℝ
  massSb : ℕ → ℝ
  mass_pos : ∀ j, 0 < massCh j ∧ 0 < massSb j

  LsS : D.what₂.Tup → ℕ → D.what₂.FT → ℂ

  LChS : D.what₂.Tup → ℕ → D.what₂.FT → ℂ

  Lfin : ℕ → ℕ → ℂ

  dFin : ℕ → ℂ

namespace Loc

variable {D : D7} (X : Loc D) (Z : DivX D)

end Loc

variable (D : D7) (Z : DivX D) (T : ThetaX D) (A : TH.ProvA) (X : Loc D)

section RealConstant

variable {D} {T}

structure LocC (Y : Formalism.MainNotions.ZetaProductPairs.Loc D T) where

  Vc : D.what₂.Word → Type
  [acVc : ∀ u, AddCommGroup (Vc u)]
  [moVc : ∀ u, Module ℂ (Vc u)]

  VD : D.what₂.Word → Type
  [acVD : ∀ u, AddCommGroup (VD u)]
  [moVD : ∀ u, Module ℂ (VD u)]

  ell : ∀ u, Vc u →ₗ[ℂ] VD u →ₗ[ℂ] ℂ

  vOf : ∀ u, Y.ArchDat u → Vc u

  TOf : ∀ u, Y.ArchDat u → VD u

  ellT_eq : ∀ u da, Y.ellT u da = ell u (vOf u da) (TOf u da)

  v_free : ∀ u (v : Vc u) (da : Y.ArchDat u), ∃ da', vOf u da' = v ∧ TOf u da' = TOf u da

attribute [instance] LocC.acVc LocC.moVc LocC.acVD LocC.moVD

end RealConstant

structure LevObj {D : D7} (T : ThetaX D) {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE]
    [FiniteDimensional ℂ EE] (S : RowSide D EE) where

  mY : D.what₂.Tup → ℕ → ℝ
  mY_pos : ∀ μ j, 0 < mY μ j

  rowAF : ∀ (μ : D.what₂.Tup) (j : ℕ), S.Mult μ j →ₗ[ℂ] T.cusp (D.sp.Y j)

  PhiYup : ∀ (_μ : D.what₂.Tup) (j : ℕ), T.Sch (D.sp.Y j) (D.sp.Y (j + 1))

  ZgCh : D.what₂.Tup → ℕ → D.what₂.FT → Pl D → ℂ

  idxgCh : D.what₂.Tup → ℕ → Pl D → ℕ

section Level

variable {D} {T} {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]

variable (S : RowSide D EE) {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ EE) (ty : Fin n → D.what₂.FT) (V : LevObj T S)

end Level

structure LevDat {D : D7} (T : ThetaX D) where
  EE : Type
  [nacg : NormedAddCommGroup EE]
  [ips : InnerProductSpace ℂ EE]
  [fd : FiniteDimensional ℂ EE]
  S : RowSide D EE
  n : ℕ
  b : OrthonormalBasis (Fin n) ℂ EE
  ty : Fin n → D.what₂.FT
  V : LevObj T S

attribute [instance] LevDat.nacg LevDat.ips LevDat.fd

section Fam

variable {eps : ℝ}

end Fam

end Formalism.MainNotions.InnerProductFormulaField

end
end
