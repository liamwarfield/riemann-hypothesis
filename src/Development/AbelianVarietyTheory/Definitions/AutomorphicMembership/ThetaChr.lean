module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OverIx
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HasPartAnd

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaChr
noncomputable section

namespace GlobalTheory.Mem.Top.Bl

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab _root_.Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.GroupRetwisting NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

abbrev SExt : Type 2 := ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl)
  (p0 : BaseLevelRowSide (w.D Z)) (r : RowsT K w Z Wt p0) (col : ColT w Z), SX K B f T w Z Wt p0 r col → Type 1

def SExt.none : SExt := fun _ _ _ _ _ _ _ _ _ _ _ => PUnit

def SXE (E : SExt) : SPosition := fun K B f T w Z Wt p0 r col => Σ a : SX K B f T w Z Wt p0 r col, E K B f T w Z Wt p0 r col a

structure Prm (hL : GlobalTheory.Published.LocalLanglandsGL) : Type 2 where
  R : RPosition
  N : NExt hL
  S : SExt
  Γ : GeoP

variable {hL : GlobalTheory.Published.LocalLanglandsGL}

structure KPin {𝒮 : Slots} {K : Ctx} (q : WPt 𝒮 K) (t : Formalism.L2.Ker.KerEntTied q.O.ex) : Prop where
  std : TC.StdKer q.w.I q.w.l q.Z t
  O : t.O = q.x.ker.O
  ent : HEq t.ent q.x.ker.E
  adapted : t.Adapted
  top : t.TopPinned

def ZeU (𝒮 : Slots) : Prop := ∀ (K : Ctx) (q : WPt 𝒮 K), Formalism.L2.Rows.ZetaCompatible (q.w.D q.Z)

variable {B : Base} {f : Fr B.toPre} {T : TwDat B}

def EntC {w : ColW B f T} {Z : w.Lt} {t : ColT w Z} {Y : DivX (w.D Z)} {Gy : G.LatInst (w.D Z)}
    {ker : KerFam (w.D Z) t.Gt t.cmp (w.tw Z) Gy} (k : KerT t Y Gy ker) : Prop :=
  ∃ (Pl : Examples₂.EntPl (w.D Z)) (Bs : Formalism.L2.Ker.PlaceMatrixFamily (w.D Z)) (h : Formalism.L2.Ker.KerEntHyp Pl k.O Bs Y (w.tw Z)),
    k.E = Formalism.L2.Ker.kerEntC Pl k.O Bs h

def BuiltE (𝒮 : Slots) : CP := fun K _ _ _ w Z c => ∃ b : Built 𝒮 K w Z c, EntC b.ker

def GoodE (𝒮 : Slots) : CP := fun K B f T w Z c => BuiltE 𝒮 K B f T w Z c ∧ GoodO (w.D Z) c.O.nch c.O.xd

def IsBuiltE (𝒮 : Slots) : V4.Slot := positionOf (BuiltE 𝒮)

def IsGoodE (𝒮 : Slots) : V4.Slot := positionOf (GoodE 𝒮)

theorem IsBuiltE.isBuilt {𝒮 : Slots} (K X f T c) (h : IsBuiltE 𝒮 K X f T c) : IsBuilt 𝒮 K X f T c :=
  positionOf_mono (fun _ _ _ _ _ _ _ ⟨b, _⟩ => ⟨b⟩) K X f T c h

theorem IsGoodE.isBuiltE {𝒮 : Slots} (K X f T c) (h : IsGoodE 𝒮 K X f T c) : IsBuiltE 𝒮 K X f T c :=
  positionOf_mono (fun _ _ _ _ _ _ _ h => h.1) K X f T c h

def MemberE (𝒮 : Slots) : Prop :=
  BaseCond KPx ∧ FirstG KPx (IsBuiltE 𝒮) ∧ ExportF KPx (IsBuiltE 𝒮) ∧ SecondG KPx (IsBuiltE 𝒮) (IsGoodE 𝒮)

def WitExE (𝒮 : Slots) : Prop :=
  ∀ (K : Ctx) (β : GlobalTheory.Fc.BPt K), β.Is (IsGoodE 𝒮) → ∃ q : WPt 𝒮 K, q.Is β.D β.O ∧ EntC q.x.ker

end GlobalTheory.Mem.Top.Bl

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotGeoClFalse
noncomputable section

namespace GlobalTheory.Mem.Top.Bl

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField

def coreS {D : D7} (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ) (J : Formalism.L2.Pj.Core D) :
    Formalism.L2.Pj.Core (setDiv D N h) where
  Q := ⟨J.Q.H, J.Q.l, J.Q.c, J.Q.Dw, J.Q.Xo, J.Q.eO⟩
  U := J.U
  V := J.V
  dict := J.dict
  mu := J.mu
  Kf := J.Kf
  pb := J.pb

inductive GeoCl (Γ : GeoP) : ∀ D : D7, Formalism.L2.Pj.Core D → DivX D → Prop
  | base {D : D7} {J : Formalism.L2.Pj.Core D} {X : DivX D} : Γ D J X → GeoCl Γ D J X
  | step {D : D7} (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ)
      {J : Formalism.L2.Pj.Core D} {X : DivX D} : GeoCl Γ D J X → GeoCl Γ (setDiv D N h) (coreS N h J) (divTr N h X)

def geoCl (Γ : GeoP) : GeoP := GeoCl Γ

theorem geoCl_of {Γ : GeoP} {D : D7} {J : Formalism.L2.Pj.Core D} {X : DivX D} (h : Γ D J X) : geoCl Γ D J X := GeoCl.base h

end GlobalTheory.Mem.Top.Bl

end
end
