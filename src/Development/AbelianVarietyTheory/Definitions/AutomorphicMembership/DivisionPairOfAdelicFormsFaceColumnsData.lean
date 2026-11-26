module

public import Formalism.LocalToGlobal.IndefiniteReal.NonzeroIndexPlaceIndepConstants
public import Lean
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WeakCharInertPartRealAdelicDataTransport

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DivisionPairOfAdelicFormsFaceColumnsData
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev

namespace GlobalTheory.Mem.R3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {K : Formalism.MainNotions.G.Consts} {Yd : DivX D}
  {cX : ExtraC}


set_option genInjectivity false in
set_option genSizeOfSpec false in
set_option maxHeartbeats 2000000 in
structure TwIn (ex : Extra D L hT Gi Gl K Yd cX) : Type 1 where
  G : Type
  [grp : Group G]
  [fin : Fintype G]
  Pl0 : Type
  I0 : Type
  T : Type
  A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m
  core : Formalism.L2.Pj.CoreJ D
  [alg : Algebra core.Q.c.F D.what₂.LL]
  R : RealDat3 D A3 core.Q.c.F
  F : Face3 D A3
  cG : G0 R.Pg D.R.r ≃* G0g D.nd
  geo : GlobalTheory.RealGeo.GeoHalf core R.toRealDat fun _ => 1
  pins : Pins R F cG
  err : ErrEq R F
  Y : Read (A3 := A3) R.toRealDat F.lv2 ex.p0
  Z : ReadL R F ex.p0 Y
  C : ReadC R F ex.p0 Y
  sEE : (R.toCx3 F).EE →ₗ⋆[ℂ] (F.fc (R.toCx3 F).zs).Sp.HH
  div : DivDef3 D A3 F.P0 F.ψ0 F.P1 F.ψ1 (zsOf R F) (s0Of R F) (s1Of R F) ex.p0 (colOf R F sEE) C.NuC (idsOf cG Z C)
  JA : AmbIds D A3.A ex.p0.s ex.amb0 F.P0 F.ψ0 Y.tup
  amb0 : AmbTie D A3.A ex.p0.s ex.amb0 F.P0 F.ψ0 Y.tup Y.jA0 JA
  JM : MjHIds D A3.A Yd (A3.indefDown (s0Of R F))
  mjH : MjHTie D A3.A Yd (A3.indefDown (s0Of R F)) Z.jW JM

attribute [instance] TwIn.grp TwIn.fin TwIn.alg

variable {ex : Extra D L hT Gi Gl K Yd cX}


set_option maxHeartbeats 2000000 in
@[reducible] def divisionPairOfAdelicFormsFaceColumnsData (x : TwIn ex) : RowSideFamily ex where
  Gp := x.G
  Pl0 := x.Pl0
  I0 := x.I0
  T := x.T
  A3 := x.A3
  P0 := x.F.P0
  ψ0 := x.F.ψ0
  Ps := x.F.P1
  ψs := x.F.ψ1
  Zs := zsOf x.R x.F
  S0 := s0Of x.R x.F
  S1 := s1Of x.R x.F
  Dc := x.F.Dc (zsOf x.R x.F)
  Sp := x.F.Sp (zsOf x.R x.F)
  C := colOf x.R x.F x.sEE
  NuC := x.C.NuC
  I := idsOf x.cG x.Z x.C
  JA := x.JA
  JM := x.JM
  tied := ⟨x.div, x.amb0, x.mjH, x.Y.cen0 x.cG x.pins.keep⟩

def TwIn.wd (x : TwIn ex) : (x.F.Dc (zsOf x.R x.F)).Mem → D.what₂.Word := (Equiv.ofBijective _ x.C.bij).symm

theorem TwIn.wd_wU (x : TwIn ex) (u : D.what₂.Word) : x.wd (x.C.wU u) = u := (Equiv.ofBijective _ x.C.bij).symm_apply_apply u

theorem TwIn.wU_wd (x : TwIn ex) (m : (x.F.Dc (zsOf x.R x.F)).Mem) : x.C.wU (x.wd m) = m :=
  (Equiv.ofBijective _ x.C.bij).apply_symm_apply m

def TwIn.bR (x : TwIn ex) (m : (x.F.Dc (zsOf x.R x.F)).Mem) (i : Fin ((x.F.Dc (zsOf x.R x.F)).a m)) : (D.mem (x.wd m)).A.Mram :=
  D.eMu (x.wd m) (D.jN (x.wd m) (x.C.eNu (x.wd m)
    (Pi.single (Fin.cast (congrArg (x.F.Dc (zsOf x.R x.F)).a (x.wU_wd m)).symm i) 1)))


set_option genInjectivity false in
set_option genSizeOfSpec false in
set_option maxHeartbeats 4000000 in
structure RealIn (x : TwIn ex) (Rc : Formalism.L2.RecT ex) (S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc) : Type 1 where
  psiPin : x.R.ψ = Rc.T.theta.W.ψ
  hin : ∀ u, Formalism.L2.SG.PoincareInHH.PoincareSetting.InHH S.X u S.Y.hK
  spPin : HEq (x.F.Sp (zsOf x.R x.F)) (Formalism.IndefR.Cx.spOf (X := S.X) (twAt D.what₂.embLL x.A3.A.v0) (x.F.Dc (zsOf x.R x.F)) S.Y.hK S.G
    x.wd (fun m => pwOf S hin (x.wd m)) x.bR)
  Sx : Formalism.IndefR.NX.RatDat D.ntw
  nexp : Formalism.IndefR.NX.NExpRealS x.R x.cG Sx
  stdV : ∀ i, (∀ a b, (Vc D i).hT ((Vc D i).frame a) ((Vc D i).frame b) = if a = b then 1 else 0) ∧
    (Vc D i).L0 = Submodule.span (𝓞 D.host.E) (Set.range (Vc D i).frame)
  stdX : (∀ a b, D.sp.X'.hT (D.sp.X'.frame a) (D.sp.X'.frame b) = if a = b then 1 else 0) ∧
    D.sp.X'.L0 = Submodule.span (𝓞 D.host.E) (Set.range D.sp.X'.frame)
  tS : Formalism.L2.Theta.GA D (Yc D 0)
  cS : ℝ
  κS : ℝ
  ιS : Formalism.L2.Theta.GA D (Yc D 0) ≃* S.X.B.I.GA
  instEq : S.X.B.I = Formalism.IndefR.RationalEmbedding.inst D
  ιS_eq : HEq ιS (Formalism.IndefR.RationalEmbedding.iota D).toMulEquiv
  sEEc : Tw (twAt D.what₂.embLL x.A3.A.v0) x.R.HE.H →ₗ⋆[ℂ] Tw (twAt D.what₂.embLL x.A3.A.v0) (Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX S.X)
  sEEj : HEq x.sEE sEEc
  seeLev : (∃ t' : Formalism.L2.Theta.GA D (Yc D 0), Formalism.IndefR.AutomorphicEvaluation.ConjLevel t'⁻¹ (levS _ (x.R.βY 0) (x.R.dat0 (x.R.toRealDat.levR x.F.lv2 true))) (Formalism.IndefR.Lev.levChi _ (x.R.βY 0) (x.R.dat0 (x.R.toRealDat.levR x.F.lv2 true))) (ιS ⁻¹' seeKS S.X) (fun k => seeChiS S.X (ιS k))) →
    Formalism.IndefR.AutomorphicEvaluation.ConjLevel tS⁻¹ (levS _ (x.R.βY 0) (x.R.dat0 (x.R.toRealDat.levR x.F.lv2 true))) (Formalism.IndefR.Lev.levChi _ (x.R.βY 0) (x.R.dat0 (x.R.toRealDat.levR x.F.lv2 true))) (ιS ⁻¹' seeKS S.X) (fun k => seeChiS S.X (ιS k))
  seeEval : (∃ c' : ℝ, Formalism.IndefR.AutomorphicEvaluation.EvalTieT (x.R.MY 0) x.R.ν0 x.R.fd0 (x.R.toRealDat.EEat (x.R.toRealDat.levR x.F.lv2 true)) S.X S.G ιS tS c') →
    Formalism.IndefR.AutomorphicEvaluation.EvalTieT (x.R.MY 0) x.R.ν0 x.R.fd0 (x.R.toRealDat.EEat (x.R.toRealDat.levR x.F.lv2 true)) S.X S.G ιS tS cS
  uS : ℂ
  uS_norm : ‖uS‖ = 1
  seeDef : ∀ (v : Tw (twAt D.what₂.embLL x.A3.A.v0) x.R.HE.H) (hx : x.R.HE.e (Tw.out v) ∈ (x.R.toRealDat.EEat (x.R.toRealDat.levR x.F.lv2 true))),
    sEEc v = Tw.mk (twAt D.what₂.embLL x.A3.A.v0) ((uS * (κS : ℂ)) • (Formalism.IndefR.AutomorphicEvaluation.sEEofTT (x.R.MY 0) x.R.ν0 x.R.fd0 (x.R.toRealDat.EEat (x.R.toRealDat.levR x.F.lv2 true)) S.X S.G ιS tS cS) ⟨x.R.HE.e (Tw.out v), hx⟩)
  seeK : 0 < κS ∧ ((∃ κ' : ℝ, 0 < κ' ∧ ∀ (v : Tw (twAt D.what₂.embLL x.A3.A.v0) x.R.HE.H) (hx : x.R.HE.e (Tw.out v) ∈ (x.R.toRealDat.EEat (x.R.toRealDat.levR x.F.lv2 true))),
      ‖(κ' : ℂ) • (Formalism.IndefR.AutomorphicEvaluation.sEEofTT (x.R.MY 0) x.R.ν0 x.R.fd0 (x.R.toRealDat.EEat (x.R.toRealDat.levR x.F.lv2 true)) S.X S.G ιS tS cS) ⟨x.R.HE.e (Tw.out v), hx⟩‖ = ‖v‖) →
    ∀ (v : Tw (twAt D.what₂.embLL x.A3.A.v0) x.R.HE.H), x.R.HE.e (Tw.out v) ∈ (x.R.toRealDat.EEat (x.R.toRealDat.levR x.F.lv2 true)) →
      RealDat.nP x.F.lv2 true * ‖sEEc v‖ ^ 2 = ‖v‖ ^ 2)
  host : HostHyp D
  vpos : ∀ i, (Vc D i).IsPosDef

variable {x : TwIn ex} {Rc : Formalism.L2.RecT ex} {S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc}


theorem phEff_one (x : TwIn ex) : phEff x.R = fun _ => 1 := by
  funext i
  unfold phEff
  rw [x.pins.phs i]
  simp




end GlobalTheory.Mem.R3

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
noncomputable section

namespace GlobalTheory.Mem.Top.Bl

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.GroupRetwisting NumberField IsDedekindDomain

def PrePin (P : Pre) : Prop :=
  letI := P.host.cmStar; ∀ (a : Fin P.sp.X'.rank) (b : Fin (P.sp.X P.R.m).rank), (a : ℕ) = b →
    P.sp.iX' (P.sp.X'.frame a) = (P.sp.X P.R.m).frame b

def KPx : BaseP := fun B f => (∃ δ : Fld.FieldDat B.toPre, B.KsExact δ f) ∧ PrePin B.toPre

structure ColW (B : Base) (f : Fr B.toPre) (T : TwDat B) : Type 1 where
  px : PreX B.toPre
  I : ColIn B px
  ok : I.Ok
  C_eq : I.C = f
  S_eq : I.S = {p | p ∈ offSet B.toPre ∧ p ≠ B.host.pde ∧ p ≠ B.host.pde'}
  xi_range : Set.range I.xi = T.set f
  pins : TC.Pins B px
  l : TC.Laws I
  l0 : TC.Law0 I l
  δ : Fld.FieldDat B.toPre
  exact : B.KsExact δ f
  fld : GlobalTheory.Mem.Per.FieldOK B.host B.embLL B.embE
  val : ∀ C W V S N G, ValLL0 (assemble B C W V S N G) (Fr.at ⟨B, C, W, V, S, N, G⟩ f)

namespace ColW

variable {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T)

abbrev C : Cols B := TC.cols w.I w.l

abbrev Lt : Type _ := TC.Later B w.C

abbrev st (Z : w.Lt) : Stages := ⟨B, w.C, Z.W, Z.V, Z.S, Z.N, Z.G⟩

abbrev D (Z : w.Lt) : D7 := TC.rec7 w.I w.l Z

abbrev tw (Z : w.Lt) : TwForms (w.D Z) := TC.tw w.I w.l w.l0 Z

end ColW

abbrev WP : Type 1 := ∀ (_ : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B), ColW B f T → Prop

abbrev ZP : Type 1 := ∀ (_ : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), w.Lt → Prop

abbrev CP : Type 1 :=
  ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt), V4.Core K (w.st Z) f T → Prop

def positionOf (P : CP) : V4.Slot := fun K X f T c =>
  ∃ (w : ColW X.B f T) (Z : w.Lt) (c' : V4.Core K (w.st Z) f T), P K X.B f T w Z c' ∧
    (⟨X.C, ⟨X.W, X.V, X.S, X.N, X.G⟩, c⟩ : Σ (C : Cols X.B) (Y : TC.Later X.B C), V4.Core K ⟨X.B, C, Y.W, Y.V, Y.S, Y.N, Y.G⟩ f T) =
      ⟨w.C, Z, c'⟩

def HasZ (P : ZP) : WP := fun K B f T w => ∃ Z : w.Lt, P K B f T w Z

def HasC (P : CP) : WP := fun K B f T w => ∃ (Z : w.Lt) (c : V4.Core K (w.st Z) f T), P K B f T w Z c

def StepW (p q : WP) : Prop :=
  Step KPx (fun _ _ _ _ => True) fun K B f T => ∀ w : ColW B f T, p K B f T w → q K B f T w

structure ColT {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) (Z : w.Lt) : Type 1 where
  C : Formalism.L2.Forms.ColsTiedSym (w.D Z)
  std : TC.StdC w.I w.l Z C
  stdLv : ∀ u, TC.StdLvC w.I w.l Z u (C.forms u)
  full : Formalism.L2.Forms.ColsFullS C
  stdDt : TC.StdDt w.I w.l Z full.1.base.dt
  Gt : GatTies (w.D Z)
  cmp : LatCmp (w.D Z)
  g : Formalism.L2.G.GroupCompatibilityAll (w.D Z) Gt cmp
  herm_eq : g.herm = full.1.to0
  forms_eq : g.forms = fun u => (C.forms u).to0
  gpl : Formalism.L2.Herm.SymmetricGroupCompatibleAtPlaces (w.D Z) full.1.base.toHermColsCh full.1.g Gt

theorem positionOf_intro {P : CP} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt}
    {c : V4.Core K (w.st Z) f T} (h : P K B f T w Z c) : positionOf P K (w.st Z) f T c := ⟨w, Z, c, h, rfl⟩

theorem positionOf_ind {P : CP} {R : V4.Slot}
    (h : ∀ K B f T (w : ColW B f T) (Z : w.Lt) (c : V4.Core K (w.st Z) f T), P K B f T w Z c → R K (w.st Z) f T c)
    {K : Ctx} {X : Stages} {f : Fr X.B.toPre} {T : TwDat X.B} {c : V4.Core K X f T} (hc : positionOf P K X f T c) : R K X f T c := by
  obtain ⟨B, C, W, V, S, N, G⟩ := X
  dsimp only at f T
  obtain ⟨w, Z, c', hp, e⟩ := hc
  exact Eq.mpr (congrArg (fun y : Σ (C : Cols B) (Y : TC.Later B C), V4.Core K ⟨B, C, Y.W, Y.V, Y.S, Y.N, Y.G⟩ f T =>
    R K ⟨B, y.1, y.2.1.W, y.2.1.V, y.2.1.S, y.2.1.N, y.2.1.G⟩ f T y.2.2) e) (h K B f T w Z c' hp)

theorem positionOf_mono {P P' : CP} (h : ∀ K B f T w Z c, P K B f T w Z c → P' K B f T w Z c) (K : Ctx) (X : Stages) (f : Fr X.B.toPre)
    (T : TwDat X.B) (c : V4.Core K X f T) (hc : positionOf P K X f T c) : positionOf P' K X f T c :=
  let ⟨w, Z, c', hp, e⟩ := hc; ⟨w, Z, c', h _ _ _ _ _ _ _ hp, e⟩

theorem StepW.of_all {p q : WP} (h : ∀ K B f T w, K.Over B.toPre → Forced K B T → p K B f T w → q K B f T w) : StepW p q :=
  Step.of_all fun K B f T a _ b _ w => h K B f T w a b

theorem StepW.trans {p q r : WP} (h : StepW p q) (h' : StepW q r) : StepW p r :=
  (Step.and h h').trans (Step.of_all fun _ _ _ _ _ _ _ H w a => H.2 w (H.1 w a))

theorem StepW.and {p q r : WP} (h : StepW p q) (h' : StepW p r) : StepW p fun K B f T w => q K B f T w ∧ r K B f T w :=
  (Step.and h h').trans (Step.of_all fun _ _ _ _ _ _ _ H w a => ⟨H.1 w a, H.2 w a⟩)

theorem step_hasCore {admitted : AtP} {p : WP} {P : CP} (h0 : Step KPx admitted fun K B f T => ∃ w : ColW B f T, p K B f T w)
    (h1 : StepW p (HasC P)) : Step KPx admitted (HasCore (positionOf P)) :=
  (h0.and ((Step.of_all fun _ _ _ _ _ _ _ _ => trivial).trans h1)).trans (Step.of_all fun _ _ _ _ _ _ _ H =>
    let ⟨w, a⟩ := H.1
    let ⟨Z, c, hc⟩ := H.2 w a
    ⟨w.C, Z.W, Z.V, Z.S, Z.N, Z.G, c, positionOf_intro hc⟩)

end GlobalTheory.Mem.Top.Bl

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BaseLevelRowSideTransport
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.L2.Pj Formalism.L2.Host
open Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.RealGeo
open scoped TensorProduct

namespace GlobalTheory.Mem.R3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B : Base} {C : Cols B}

structure Refill (a : Late B C) where

  S : SStage B C a.W

  G : GJStage B C

  L : ∀ u, Submodule (𝓞 B.LL) (a.V.div.Nu u).V

  h : B.Word → ℝ

  HH : ℝ

  HH_ge : sFrame (fun u => { a.V.div.Nu u with L := L u }) h + a.V.div.RR.muMax ≤ HH

  etaF : ℝ

abbrev Refill.to {a : Late B C} (c : Refill a) : Late B C :=
  ⟨a.W, { a.V with
      div := { a.V.div with Nu := fun u => { a.V.div.Nu u with L := c.L u }, h := c.h, HH := c.HH, HH_ge := c.HH_ge, etaF := c.etaF } },
    c.S, a.N, c.G⟩

abbrev Refill.ofSG (a : Late B C) (S : SStage B C a.W) (G : GJStage B C) : Refill a :=
  ⟨S, G, fun u => (a.V.div.Nu u).L, a.V.div.h, a.V.div.HH, a.V.div.HH_ge, a.V.div.etaF⟩

abbrev Refill.ofDiv (a : Late B C) (L : ∀ u, Submodule (𝓞 B.LL) (a.V.div.Nu u).V) (h : B.Word → ℝ) : Refill a :=
  ⟨a.S, a.G, L, h, max 1 (sFrame (fun u => { a.V.div.Nu u with L := L u }) h + a.V.div.RR.muMax), le_max_right _ _, a.V.div.etaF⟩

def Refill.same {a : Late B C} (c : Refill a) : SameGrp a c.to := SameGrp.ofN a.N a.V c.to.V a.S c.S a.G c.G

def Refill.same' {a : Late B C} (c : Refill a) : SameGrp c.to a := SameGrp.ofN a.N c.to.V a.V c.S a.S c.G a.G

namespace Tr

variable {a : Late B C} (c : Refill a) {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
variable {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL]

def rowSide {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] (X : RowSide a.D EE) :
    RowSide c.to.D EE where
  Amb := (X.Amb)
  instAmb := (X.instAmb)
  instAmbi := (X.instAmbi)
  instAmbf := (X.instAmbf)
  Mult := (X.Mult)
  instMult := (X.instMult)
  instMulti := (X.instMulti)
  instMultf := (X.instMultf)
  multZero := (X.multZero)
  multTop := (X.multTop)
  io := (X.io)
  Mtilde := (X.Mtilde)
  cen := (X.cen)
  eOp := (X.eOp)
  eOp_idem := (X.eOp_idem)
  eOp_sa := (X.eOp_sa)
  eOp_tie := (X.eOp_tie)
  RR := (X.RR)
  RR_frames := (X.RR_frames)
  jEE := (X.jEE)
  jEE_basis := (X.jEE_basis)
  jEE_norm := (X.jEE_norm)

def baseLevelRowSideTransport (X : BaseLevelRowSide a.D) : BaseLevelRowSide c.to.D := ⟨(@rowSide B C a c (@Rows.Data.EE0 (@Late.D B C a).R (@Late.D B C a).what₂) (@Rows.Data.instEE0 (@Late.D B C a).R (@Late.D B C a).what₂) (@Rows.Data.instEE0i (@Late.D B C a).R (@Late.D B C a).what₂) (@Rows.Data.instEE0f (@Late.D B C a).R (@Late.D B C a).what₂) (@BaseLevelRowSide.s (@Late.D B C a) X))⟩

def colReal (K : ColReal a.D) : ColReal c.to.D := ⟨(K.xi)⟩

section Chain

variable {A : FamIn a.D.what₂.LL G Pl0 T a.D.R.m} {R : RealDat a.D A Ks} {F : Face a.D A} {tupT : a.D.what₂.Tup → T}
  {hm : 0 < a.D.R.m} {hTop : TopMultH R}


variable (F tupT hm hTop) in
def spEEc : type_of% (toChainReal R F tupT hm hTop).EEc := ((chainB c.to F tupT hm hTop).EEc)


variable (F tupT hm hTop) in
theorem spEEc_eq : (toChainReal R F tupT hm hTop).EEc = spEEc c F tupT hm hTop := (chain_EEc c.to F tupT hm hTop)


variable (F tupT hm hTop) in
def spCC : type_of% (toChainReal R F tupT hm hTop).CC := ((chainB c.to F tupT hm hTop).CC)


variable (F tupT hm hTop) in
theorem spCC_eq : (toChainReal R F tupT hm hTop).CC = spCC c F tupT hm hTop := (chain_CC c.to F tupT hm hTop)


variable (F tupT hm hTop) in
def spCCP : type_of% (toChainReal R F tupT hm hTop).CCP := ((chainB c.to F tupT hm hTop).CCP)


variable (F tupT hm hTop) in
theorem spCCP_eq : (toChainReal R F tupT hm hTop).CCP = spCCP c F tupT hm hTop := (chain_CCP c.to F tupT hm hTop)


variable (F tupT hm hTop) in
def spCCX : type_of% (toChainReal R F tupT hm hTop).CCX := ((chainB c.to F tupT hm hTop).CCX)


variable (F tupT hm hTop) in
theorem spCCX_eq : (toChainReal R F tupT hm hTop).CCX = spCCX c F tupT hm hTop := (chain_CCX c.to F tupT hm hTop)


variable (F tupT hm hTop) in
def spCCXP : type_of% (toChainReal R F tupT hm hTop).CCXP := ((chainB c.to F tupT hm hTop).CCXP)


variable (F tupT hm hTop) in
theorem spCCXP_eq : (toChainReal R F tupT hm hTop).CCXP = spCCXP c F tupT hm hTop := (chain_CCXP c.to F tupT hm hTop)


variable (F tupT hm hTop) in
def okB (l : Bool) (μ : a.D.what₂.Tup) : Prop := (chainB c.to F tupT hm hTop).IoOK l ((μ))

theorem okB_imp {l : Bool} {μ : a.D.what₂.Tup} (h : okB c F tupT hm hTop l μ) : (toChainReal R F tupT hm hTop).IoOK l μ :=
  chain_ioOK c.to F tupT hm hTop ((h))

def ioCB (l : Bool) (μ : a.D.what₂.Tup) (k : ℕ) (v : (toChainReal R F tupT hm hTop).CC l μ (k + 1)) : (toChainReal R F tupT hm hTop).Amb k :=
  (by with_unfolding_all exact (((chainB c.to F tupT hm hTop).ioC l ((by with_unfolding_all exact (μ :))) k
    ((by with_unfolding_all exact ((LinearEquiv.ofEq _ _ (congrFun (congrFun (congrFun (spCC_eq c F tupT hm hTop) l) μ) (k + 1)) v) :)))).1 :))

theorem ioCB_eq (l : Bool) (μ : a.D.what₂.Tup) (k : ℕ) (v : (toChainReal R F tupT hm hTop).CC l μ (k + 1)) :
    ioCB c l μ k v = ((toChainReal R F tupT hm hTop).ioC l μ k v).1 :=
  (by with_unfolding_all exact ((chain_ioC c.to (R := R) (tupT μ) k ((v.1))
    (((LinearEquiv.ofEq _ _ (congrFun (congrFun (congrFun (spCC_eq c F tupT hm hTop) l) μ) (k + 1)) v).2)) ((v.2))) : _))

def ioXB' (l : Bool) (μ : a.D.what₂.Tup) (v : (toChainReal R F tupT hm hTop).CCX l μ) : (toChainReal R F tupT hm hTop).Amb (a.D.R.m - 1) :=
  (by with_unfolding_all exact (((chainB c.to F tupT hm hTop).ioX l ((by with_unfolding_all exact (μ :))) ((by with_unfolding_all exact ((LinearEquiv.ofEq _ _ (congrFun (congrFun (spCCX_eq c F tupT hm hTop) l) μ) v) :)))).1 :))

theorem ioXB'_eq (l : Bool) (μ : a.D.what₂.Tup) (v : (toChainReal R F tupT hm hTop).CCX l μ) :
    ioXB' c l μ v = ((toChainReal R F tupT hm hTop).ioX l μ v).1 :=
  (by with_unfolding_all exact ((chain_ioX c.to (R := R) hm hTop (tupT μ) ((by with_unfolding_all exact (v.1 :))) ((by with_unfolding_all exact ((topMult_tr c.to hTop) :)))
    ((by with_unfolding_all exact ((LinearEquiv.ofEq _ _ (congrFun (congrFun (spCCX_eq c F tupT hm hTop) l) μ) v).2 :))) ((by with_unfolding_all exact (v.2 :)))) :))

end Chain

end Tr

end GlobalTheory.Mem.R3

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NontrivialReferenceForms
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.RowsRestModel

namespace GlobalTheory.Mem.Df.Model

attribute [local instance] GlobalTheory.Mem.Col2.starE

section Gen

variable {K : Type} [Field K] [NumberField K] [StarRing K] (H : HLat K) (σ : K →+* ℂ) {M : Type} [AddCommGroup M] [Module ℂ M]
  (j : H.V →ₛₗ[σ] M) (c : Module.Basis H.ι ℂ M) (hc : ∀ i, c i = j (H.b i))




end Gen

section Pack

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (hX : X.Ok)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (P : LevFam X.E X.K R.r Pr.vGs) (σ : X.K →+* ℂ)





end Pack

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : TC.Laws I) (hX : B.fields.Ok)



theorem exists_ka (B : Base) : ∃ (kb : ∀ j, Tau B.R → Fin (B.R.sigW j).1 → ℤ) (ks : ∀ j, Tau B.R → Fin (B.R.sigW j).2 → ℤ),
    ∀ (C : Cols B) (W : RowsRest B C), W.kaBig = kb → W.kaSmall = ks → ∀ V S N G, DV.KapDef (assemble B C W V S N G) := by
  by_cases h : ∃ (C : Cols B) (W : RowsRest B C) (_ : DivStage B C W) (_ : SStage B C W) (_ : NStage B C W), Nonempty (GJStage B C)
  · obtain ⟨C, W, V, S, N, ⟨G⟩⟩ := h
    obtain ⟨kb, ks, hk⟩ := DV.exists_blocks (assemble B C W V S N G)
    refine ⟨kb, ks, fun C' W' h1 h2 V' S' N' G' j _ _ τ => ⟨fun i => ?_, fun c => ?_⟩⟩
    · show ((W'.kaBig j τ i : ℤ) : ℚ) = _
      rw [h1]
      exact (hk j τ).1 i
    · show ((W'.kaSmall j τ c : ℤ) : ℚ) = _
      rw [h2]
      exact (hk j τ).2 c
  · exact ⟨0, 0, fun C W _ _ V S N G => absurd ⟨C, W, V, S, N, ⟨G⟩⟩ h⟩

section Build

variable {C : Cols B} {d₀ : C.Tup → ℕ} (hf : Fits C d₀) (d : C.Tup → ℕ)
  (L : ∀ a, Rows.OLat B.O (B.embLL.comp B.OtoLL) (Eu (d a)))
  (e0 : ∀ u, (C.mem u).P.Mt ≃ₗ[ℂ] Eu (d C.mu0)) (eT : ∀ u a, (C.PTw u a).Mt ≃ₗ[ℂ] Eu (d a))
  (kb : ∀ j, Tau B.R → Fin (B.R.sigW j).1 → ℤ) (ks : ∀ j, Tau B.R → Fin (B.R.sigW j).2 → ℤ)

end Build





end GlobalTheory.Mem.Df.Model

end
end
