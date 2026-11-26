module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LowerTieTwAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsBIffCoreB
noncomputable section

namespace GlobalTheory.Mem.Db

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl
  GlobalTheory.Mem.Df NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure NStd {B : Base} {C : Cols B} {W : RowsRest B C} (N : NStage B C W) : Prop where
  loc : IsEmpty N.nd.Loc
  cover : N.ntw.TwCover
  chiT : ∀ (k : Fin 2) (v : N.nd.PlG k), ∃ w : (ZMod (B.host.g k))ˣ, orderOf w = B.host.g k - 1 ∧
    ∀ j : Fin B.R.m, N.nd.chiT k v j = w ^ (2 * (j.1 + 1))

structure SStd (K : Ctx) {B : Base} {C : Cols B} {W : RowsRest B C} (S : SStage B C W) (cd : CDHaar) : Prop where
  del : S.s.Del = (Delv K.s K.cD : ℚ)
  scale : S.s.cdScale = Vol.trueScale cd
  dsig : ∀ τ, S.dsig τ = Vol.trueDsig B.R (B.hc τ)

variable {B : Base} {f : Fr B.toPre} {T : TwDat B}

def GCols (K : Ctx) (w : ColW B f T) (G : GJStage B w.C) : Prop :=
  ∀ W V S N, GatNum K.s (w.D ⟨W, V, S, N, G⟩) ∧ Nonempty (ColumnDataSplitPrimes K w ⟨W, V, S, N, G⟩)

structure ZDef (K : Ctx) (w : ColW B f T) (Z : w.Lt) : Type 1 where
  hX : B.fields.Ok
  e : ∀ a : w.C.Tup, MtCx w.I a ≃ₗ[ℂ] Z.W.Amb a
  tru : DefTrue w.I w.l hX Z.W e
  std : StandIn Z.W
  etaF : Z.V.div.etaF = 6 * K.s.x ^ (-K.C.P.CF)
  s : SStd K Z.S Z.G.cd
  n : NStd Z.N
  g : GCols K w Z.G

structure Side (w : ColW B f T) (Z : w.Lt) : Type 1 where
  th : ThetaX (w.D Z)
  th_io : th.TieIo
  nch : NChoice (w.D Z)
  n : NchT w Z ∅ nch
  xd : ThData (w.D Z)
  X : DivX (w.D Z)
  qp : TC.QpIs w.I X.Qp
  p0 : BaseLevelRowSide (w.D Z)
  amb0 : AmbForm (w.D Z) p0.s
  row : V4.RowLay (w.D Z) p0 X
  gauge : GlobalTheoryTheory.GenusMassVolumes.GaugeFam (w.D Z).host.F (w.D Z).host.E (w.D Z).sp.cm.sig
  gauge_def : gauge.IsGauge

structure CoreB (K : Ctx) (w : ColW B f T) (Z : w.Lt) : Type 1 where
  isOver : K.Over B.toPre
  untw : T = TwDat.untw B T.pl
  forced : Forced K B T
  pin : ColPin w
  z : ZDef K w Z
  mu : V4.MuIsW (w.st Z) f T ∅ w.I.xi
  sd : Side w Z
  t : ColumnDataSplitPrimes K w Z
  Gy : G.LatInst (w.D Z)
  ker : KerFam (w.D Z) t.Gt t.cmp (w.tw Z) Gy
  gy : GyLay K (w.D Z) t.Gt t.cmp Gy
  kt : KerT t.toColT sd.X Gy ker
  entC : ∃ (Pl : Examples₂.EntPl (w.D Z)) (Bs : Formalism.L2.Ker.PlaceMatrixFamily (w.D Z)) (h : Formalism.L2.Ker.KerEntHyp Pl kt.O Bs sd.X (w.tw Z)),
    kt.E = Formalism.L2.Ker.kerEntC Pl kt.O Bs h
  col : ColLay (w.D Z) t.full.1.base.lev0 (Formalism.L2.Herm.toErrXS t.full.1)
  amb : AmbForm (w.D Z) (RowSide.sharp (w.D Z))
  ambTrue : AmbTrue w.I w.l z.hX Z z.e amb
  mtStable : DQ.MtStableAt (w.D Z)
  cd : cdScaleTie (w.D Z)
  dsT : dsigTie (w.D Z)
  ds : ∀ τ, Formalism.L2.Theta.IsDsig (w.D Z) τ ((w.D Z).dsig τ)

def CoreB.obj {K : Ctx} {w : ColW B f T} {Z : w.Lt} (b : CoreB K w Z) : Obj2 (w.D Z) where
  gatT := b.t.Gt
  th := b.sd.th
  cmp := b.t.cmp
  tw := w.tw Z
  Gy := b.Gy
  errX := Formalism.L2.Herm.toErrXS b.t.full.1
  nch := b.sd.nch
  xd := b.sd.xd
  lev := b.t.full.1.base.lev0
  X := b.sd.X
  p0 := b.sd.p0
  ker := b.ker
  amb := b.amb
  amb0 := b.sd.amb0
  gauge := b.sd.gauge

def setDivZ {C : Cols B} (Z : TC.Later B C) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) : TC.Later B C :=
  { Z with V := { Z.V with div := (setDiv (assemble B C Z.W Z.V Z.S Z.N Z.G) N h).div } }

theorem D_setDivZ (w : ColW B f T) (Z : w.Lt) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) :
    w.D (setDivZ Z N h) = setDiv (w.D Z) N h := rfl

def IsB (K : Ctx) (D : D7) (O : Obj2 D) : Prop :=
  ∃ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (b : CoreB K w Z),
    (⟨D, O⟩ : Σ D : D7, Obj2 D) = ⟨w.D Z, b.obj⟩

def ForVol (w : ColW B f T) (P : w.Lt → Prop) : Prop :=
  ∀ (vol : HSpace B.host.E → ℝ) (cd : CDHaar), (∀ W, 0 < vol W) →
    (∀ Z : w.Lt, Z.G.vol = vol → Z.G.cd = cd → Formalism.L2.Herm.VolumeCompatible (w.D Z)) → ∃ Z : w.Lt, Z.G.vol = vol ∧ Z.G.cd = cd ∧ P Z

theorem IsB.ind {K : Ctx} {R : ∀ D : D7, Obj2 D → Prop}
    (h : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (b : CoreB K w Z), R (w.D Z) b.obj)
    {D : D7} {O : Obj2 D} (hD : IsB K D O) : R D O := by
  obtain ⟨B, f, T, w, Z, b, e⟩ := hD
  cases e
  exact h B f T w Z b

section Layers

variable {K : Ctx} {w : ColW B f T} {Z : w.Lt}

end Layers

end GlobalTheory.Mem.Db

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimes
noncomputable section

namespace GlobalTheory.Mem.Top.Bl

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.GroupRetwisting NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar


open Classical in
def FK (s : Scale) (D : D7) (j p : ℕ) : ℝ :=
  if ∃ i, p = D.host.g i then FTypeG D j
  else if D.host.cls p = PrimeClass.ramD then FRamD D j
  else if (G.IsResidueClassZero D p ∨ G.IsSg D p) ∧ (p : ℝ) ≤ s.X'' D.R.n then FInert D j p
  else 0

def F0K (s : Scale) (D : D7) (y : HeightOneSpectrum (𝓞 D.what₂.LL)) (j : Fin D.R.m) : ℝ :=
  FK s D (j.1 + 1) (D.what₂.places.resChar (D.plEq.symm y))

section Reading

open Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}
  {Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0}

def MjAre (Z : R3.ReadL R F X0 Y) (Xd : DivX D) : Prop :=
  ∃ J : MjHIds D A3.A Xd (A3.indefDown (R3.s0Of R F)), MjHTie D A3.A Xd (A3.indefDown (R3.s0Of R F)) Z.jW J

def AmbAre (_Z : R3.ReadL R F X0 Y) (a : AmbForm D (RowSide.sharp D)) (a0 : AmbForm D X0.s) : Prop :=
  (∃ J, AmbTie D A3.A (RowSide.sharp D) a F.P1 F.ψ1 Y.tup Y.jA J) ∧ ∃ J, AmbTie D A3.A X0.s a0 F.P0 F.ψ0 Y.tup Y.jA0 J

end Reading

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B}

structure RowsT (K : Ctx) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (p0 : BaseLevelRowSide (w.D Z)) : Type 1 where
  hX : B.fields.Ok
  r : R3.RowsAre (w.st Z) w.I hX T Wt (Equiv.refl _) p0
  exAt : r.z.R.toRealDat.ExAt
  inGeo : GlobalTheory.RealGeo.InGeo r.z.geo
  grpAt : R3.GrpAt (w.st Z) w.I
  grp : GrpTrue Z.N f
  mu : V4.MuIsW (w.st Z) f T Wt w.I.xi
  exact : Wt = r.z.W1 (F0K K.s (w.D Z))
  untw : ∀ v, v ∉ Wt → ∀ j, 1 ≤ j → j ≤ B.R.m → (w.D Z).what₂.Ij (w.D Z).what₂.mu0 j v = 0 ∧ (w.D Z).what₂.jw (w.D Z).what₂.mu0 j v = 0
  emt0 : ∀ u F G, inner ℂ ((w.D Z).eMt u F) ((w.D Z).eMt u G) = TC.ipMt w.I w.l u w.I.mu0 F G
  emt : ∀ u (a : (w.D Z).what₂.Tup), a ≠ (w.D Z).what₂.mu0 → ∀ F G,
    inner ℂ ((w.D Z).eMtTw u a F) ((w.D Z).eMtTw u a G) = TC.ipMt w.I w.l u a F G
  etaF : Z.V.div.etaF = 6 * K.s.x ^ (-K.C.P.CF)
  rowInt : GlobalTheory.PerQ.RowInt w.I w.l Z
  idx : ∀ Y : DivX (w.st Z).toD7, MjAre r.Z Y → IdxDefs (w.D Z) Y

structure ObjT {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl} (O : Obj2 (w.D Z)) (t : RowsT K w Z Wt O.p0) : Prop where
  amb : AmbAre t.r.Z O.amb O.amb0
  mjH : MjAre t.r.Z O.X
  kapR : ∀ σ, O.X.kapR σ = kapSharp (w.D Z)

def DatGood : WP := fun K B f T w =>
  ∃ (Z : w.Lt) (hX : B.fields.Ok) (z : R3.Dat (w.st Z) w.I hX T {v | B.places.resChar v ∈ T.pl}),
    GIs2 K w Z.G ∧ GrpTrue Z.N f ∧ R3.GrpAt (w.st Z) w.I ∧ DV.KapDef (w.D Z) ∧ z.R.toRealDat.ExAt ∧ GlobalTheory.RealGeo.InGeo z.geo ∧
    (Formalism.L2.Pj.LawsCore z.core.toCore ∧ z.core.Q.Canon ∧ (∀ j, 1 ≤ (z.core.Q.Dw j).p + (z.core.Q.Dw j).q) ∧ z.core.pb = f.P.pb) ∧
    z.Std ∧ (∀ v ∈ z.W1 (F0K K.s (w.D Z)), B.places.resChar v ∈ T.pl) ∧ ∀ v, v ∉ z.W1 (F0K K.s (w.D Z)) → T.psi v = 1

def Supp : WP := fun K B f T w => T = TwDat.untw B T.pl ∨ DatGood K B f T w

structure Coh (B : Base) (T : TwDat B) : Prop where
  same : ∀ v v', (∀ x ∈ B.LL0, 0 ≤ B.places.val v x ↔ 0 ≤ B.places.val v' x) → T.Q v = T.Q v' ∧ T.k v = T.k v' ∧ T.psi v = T.psi v'
  roots : ∀ v, ∃ z : B.LL, IsPrimitiveRoot z (B.places.resChar v ^ T.k v)

def Start : WP := fun K B f T w => Pinned K B f T w ∧ Supp K B f T w ∧ Coh B T

def Below (D D' : D7) (v : D.what₂.places.Pl) (v' : D'.what₂.places.Pl) : Prop :=
  ∀ (x : 𝓞 D.what₂.LL) (x' : 𝓞 D'.what₂.LL), D.what₂.embLL (x : D.what₂.LL) = D'.what₂.embLL (x' : D'.what₂.LL) →
    (x ∈ (D.plEq v).asIdeal ↔ x' ∈ (D'.plEq v').asIdeal)

abbrev NCondition : Type 2 := ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl)
  (p0 : BaseLevelRowSide (w.D Z)) (_ : RowsT K w Z Wt p0) (nch : NChoice (w.D Z)) (_ : NchT w Z Wt nch) (_ : ThData (w.D Z)), Type 1

abbrev SPosition : Type 2 := ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl)
  (p0 : BaseLevelRowSide (w.D Z)) (_ : RowsT K w Z Wt p0) (_ : ColT w Z), Type 1

abbrev OComponent₂ : Type 2 := ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl)
  (O : Obj2 (w.D Z)) (_ : RowsT K w Z Wt O.p0), Type 1

abbrev RPosition : Type 2 := ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl)
  (p0 : BaseLevelRowSide (w.D Z)) (_ : RowsT K w Z Wt p0), Type 1

structure Slots : Type 2 where
  Rx : RPosition
  Nx : NCondition
  Sx : SPosition
  Ox : OComponent₂

structure Lv2 (𝒮 : Slots) (K : Ctx) (w : ColW B f T) (Z : w.Lt) : Type 1 where
  g : GIs2 K w Z.G
  coh : Coh B T
  Wt : Set B.places.Pl
  p0 : BaseLevelRowSide (w.D Z)
  what₂ : RowsT K w Z Wt p0
  rx : 𝒮.Rx K B f T w Z Wt p0 what₂

structure Lv3 (𝒮 : Slots) (K : Ctx) (w : ColW B f T) (Z : w.Lt) : Type 1 extends Lv2 𝒮 K w Z where
  nch : NChoice (w.D Z)
  n : NchT w Z Wt nch
  xd : ThData (w.D Z)
  chiT : ∀ (k : Fin 2) (v : Z.N.nd.PlG k), ∃ x : (ZMod (B.host.g k))ˣ, orderOf x = B.host.g k - 1 ∧
    ∀ j : Fin B.R.m, Z.N.nd.chiT k v j = x ^ (2 * (j.1 + 1))
  nx : 𝒮.Nx K B f T w Z Wt p0 what₂ nch n xd

structure Lv4 (𝒮 : Slots) (K : Ctx) (w : ColW B f T) (Z : w.Lt) : Type 1 extends Lv3 𝒮 K w Z where
  col : ColumnDataSplitPrimes K w Z
  real : Formalism.L2.Theta.RealTied (w.D Z)
  dsig_eq : ∀ τ, Z.S.dsig τ = Vol.trueDsig B.R (B.hc τ)
  del : Z.S.s.Del = (Delv K.s K.cD : ℚ)
  sx : 𝒮.Sx K B f T w Z Wt p0 what₂ col.toColT

structure Built (𝒮 : Slots) (K : Ctx) (w : ColW B f T) (Z : w.Lt) (c : V4.Core K (w.st Z) f T) : Type 1 where
  pin : ColPin w
  coh : Coh B T
  g : GIs2 K w Z.G
  col : ColumnDataSplitPrimes K w Z
  what₂ : RowsT K w Z c.Wt c.O.p0
  rx : 𝒮.Rx K B f T w Z c.Wt c.O.p0 what₂
  xi : c.xi = w.I.xi
  lev : c.O.lev = col.full.1.base.lev0
  errX : c.O.errX = Formalism.L2.Herm.toErrXS col.full.1
  n : NchT w Z c.Wt c.O.nch
  nx : 𝒮.Nx K B f T w Z c.Wt c.O.p0 what₂ c.O.nch n c.O.xd
  sx : 𝒮.Sx K B f T w Z c.Wt c.O.p0 what₂ col.toColT
  ker0 : KerFam (w.D Z) col.Gt col.cmp (w.tw Z) c.O.Gy
  ker_eq : (⟨c.O.gatT, c.O.cmp, c.O.tw, c.O.ker⟩ : Σ (Gt : GatTies (w.D Z)) (cmp : LatCmp (w.D Z)) (tw : TwForms (w.D Z)),
    KerFam (w.D Z) Gt cmp tw c.O.Gy) = ⟨col.Gt, col.cmp, w.tw Z, ker0⟩
  ker : KerT col.toColT c.O.X c.O.Gy ker0
  div : DivT n c.O.X
  th : ThT n c.O.th
  obj : ObjT c.O what₂
  ox : 𝒮.Ox K B f T w Z c.Wt c.O what₂

def BuiltC (𝒮 : Slots) : CP := fun K _ _ _ w Z c => Nonempty (Built 𝒮 K w Z c)

def IsBuilt (𝒮 : Slots) : V4.Slot := positionOf (BuiltC 𝒮)

def Has3 (𝒮 : Slots) : WP := HasZ fun K _ _ _ w Z => Nonempty (Lv3 𝒮 K w Z)

def Has4 (𝒮 : Slots) : WP := HasZ fun K _ _ _ w Z => Nonempty (Lv4 𝒮 K w Z)

def pinAnd (p : WP) : WP := fun K B f T w => Pinned K B f T w ∧ p K B f T w

def AmbEx (𝒮 : Slots) : Prop := StepW Pinned fun K _ _ _ w => ∀ (Z : w.Lt) (l : Lv4 𝒮 K w Z), ∃ a a0, AmbAre l.what₂.r.Z a a0

def DivEx (𝒮 : Slots) : Prop := StepW Pinned fun K B f T w => ∀ (Z : w.Lt) (l : Lv4 𝒮 K w Z), ∃ Y : DivX (w.D Z),
  Nonempty (DivT l.n Y) ∧ MjAre l.what₂.r.Z Y ∧ (∀ σ, Y.kapR σ = kapSharp (w.D Z)) ∧
    ∀ (O : Obj2 (w.D Z)) (t : RowsT K w Z l.Wt O.p0), O.X = Y → O.p0 = l.p0 → HEq t l.what₂ → Nonempty (𝒮.Ox K B f T w Z l.Wt O t)

def ThEx (𝒮 : Slots) : Prop := StepW Pinned fun K _ _ _ w => ∀ (Z : w.Lt) (l : Lv4 𝒮 K w Z), ∃ th : ThetaX (w.D Z), Nonempty (ThT l.n th)

theorem supp_of_untw (w : ColW B f T) (h : T = TwDat.untw B T.pl) : Supp K B f T w := Or.inl h

theorem coh_of_untw (h : T = TwDat.untw B T.pl) : Coh B T := by
  rw [h]
  exact ⟨fun _ _ _ => ⟨rfl, rfl, rfl⟩, fun v => ⟨1, by change IsPrimitiveRoot _ (_ ^ 0); rw [pow_zero]; exact IsPrimitiveRoot.one⟩⟩

end GlobalTheory.Mem.Top.Bl

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldTies
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.L2.Pj GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.FieldSize

namespace GlobalTheory.AtMember

variable {D : D7}

structure CorePin (J : Core D) (pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K)) : Prop where
  laws : LawsCore J
  canon : J.Q.Canon
  rank : ∀ j, 1 ≤ (J.Q.Dw j).p + (J.Q.Dw j).q
  pb : J.pb = pb

theorem CorePin.reCore {J : CoreJ D} {pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K)} (h : CorePin J.toCore pb) {dict mu chiW x₀ cE}
    (hM : LawsM (GlobalTheory.RealGeo.reCore J dict mu chiW x₀ cE).toCore) : CorePin (GlobalTheory.RealGeo.reCore J dict mu chiW x₀ cE).toCore pb :=
  ⟨⟨hM, h.laws.cuspMul, h.laws.latZ, h.laws.cuNe, h.laws.expo⟩, h.canon, h.rank, h.pb⟩

structure FieldTies (D : D7) (C : Formalism.L2.Host.CharFrame D) : Prop where
  one : FieldOK0 D D.host.pde
  two : FieldOK0 D D.host.pde'
  del : ∀ x, ((C.del.1 x : ℂˣ) : ℂ) ∈ FO D
  del' : ∀ x, ((C.del'.1 x : ℂˣ) : ℂ) ∈ FO D
  small : ∀ L : ℝ, HostSz D.host L → Sz (FO D) (poR D.R L) (poR D.R L)

def HalfAt (EX : ErrX D) (C : Formalism.L2.Host.CharFrame D) : Prop :=
  ∀ k, barE D (EX.piG k) ∈ (C.P.pb k).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))

def NumAtL (L : SizeData₂ D) (x : ℝ) : Prop :=
  DV.KapDef D ∧ (∃ (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm), GlobalTheory.BigOn.PageNum Tp x) ∧ FieldSmall D L

end GlobalTheory.AtMember
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsetTwistExceptionalPlaces
noncomputable section

namespace GlobalTheory.HeightCounting

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice _root_.Formalism.L2 _root_.Formalism.L2.Host _root_.Formalism.L2.Theta _root_.Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
  Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000

def TauTrue {D : D7} (X : NExpTied D) : Prop :=
  ∃ τ : ℕ → ∀ kv : (Σ k : Fin 2, D.nd.PlG k), (ZMod (D.host.g kv.1))ˣ →* (↥D.LL0)ˣ, ∀ i j b kv x, 1 ≤ j → j ≤ D.R.m →
    ((X.tauG i j b kv x : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) =
      GlobalTheory.SeriesTie.sideEmb D.ntw i b ((τ j kv x : (↥D.LL0)ˣ) : ↥D.LL0)

def lowAll (D : D7) : Finset ℕ := lowPr D ∪ {D.host.g 0, D.host.g 1, D.host.pde, D.host.pde'}

def OverSet (D : D7) (S : Finset (PlE D.host)) (s : Finset ℕ) : Prop := ∀ P ∈ S, ∃ p ∈ s, P ∈ placesOver D.host.E p

theorem OverSet.subset {D : D7} {S S' : Finset (PlE D.host)} {s : Finset ℕ} (h : OverSet D S s)
    (hs : ∀ p ∈ s, placesOver D.host.E p ⊆ ↑S') : S ⊆ S' :=
  fun P hP => (h P hP).elim fun p hp => hs p hp.1 hp.2

theorem OverSet.subset_twistExceptionalPlaces {D : D7} {S : Finset (PlE D.host)} {s low : Finset ℕ} (h : OverSet D S s) (hs : s ⊆ low)
    {F : TwFrameC D} (T : TwistFrameLowIndexCompatibility D F low) (i : D.ntw.Tw) : S ⊆ D.ntw.S0 i :=
  h.subset fun p hp P hP => by
    rw [T.ringSpec_excludedPlaces_eq i]
    exact Or.inr (T.concreteTwistFrame_extraExcluded_over_smallPrimes i p (hs hp) hP)

structure Elem (D : D7) : Prop where
  star : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0
  int : ∀ j g, ∃ z : ℤ, eExp D j g = z
  split : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v

section Rows

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}


set_option genInjectivity false in
set_option genSizeOfSpec false in
structure MtAd (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (M : MtFam D) where
  PV : ∀ i : Fin D.R.m, principalLevelFrame.RowPsi (Vc D i) D.R.nV
  std : ∀ i, R3.StdFrame Y.hF (PV i)
  eW : ∀ μ, Used0 D μ → ∀ i : Fin D.R.m, (M μ (i.1 + 1) (by omega) (by omega)).wt.W ≃ₗ[ℂ] (R.cV i).W
  read : ∀ μ (h : Used0 D μ) (i : Fin D.R.m) (x : D.what₂.Mt μ (i.1 + 1)) (g : GAf D.host.E D.R.nV),
    eW μ h i ((M μ (i.1 + 1) (by omega) (by omega)).real x g) = (Y.IL.jMt μ h i x).1 ((PV i).ψ g)
  rat : ∀ (i : Fin D.R.m) (g : GAf D.host.E D.R.nV), g ∈ ReciprocityTheory.Aut.GQ D.host.E D.R.nV ↔
    ∃ γ ∈ Formalism.L2.Theta.GQ (Vc D i), finHom (Vc D i) γ = finHom (Vc D i) ((PV i).ψ g)
  wt : ∀ μ (h : Used0 D μ) (i : Fin D.R.m) (g : ReciprocityTheory.Aut.GQ D.host.E D.R.nV), ∀ γ ∈ Formalism.L2.Theta.GQ (Vc D i),
    finHom (Vc D i) γ = finHom (Vc D i) ((PV i).ψ g) → ∀ v,
      eW μ h i ((M μ (i.1 + 1) (by omega) (by omega)).wt.ρ g v) = (R.cV i).ρ γ (eW μ h i v)
  id : ∀ i : Fin D.R.m, ∃ hn : (Vc D i).rank = D.R.nV, ∀ κ a b, finMat D.sp.cm.sig (Vc D i).gram ((PV i).ψ κ) a b =
    (GlobalTheory.Mem.R3.swapCast Y.hF).symm ((κ.1 : Matrix (Fin D.R.nV) (Fin D.R.nV) (ReciprocityTheory.Aut.AL D.host.E)) (Fin.cast hn a) (Fin.cast hn b))


variable (R) in
def hkNorm (i : Fin D.R.m) (k : ℕ) (P : PlE D.host) : ℂ :=
  (((R.C.mu0 i).val P : ℂˣ) : ℂ)⁻¹ ^ k * (((Nat.card (kP P) : ℕ) : ℂ) ^ (k * (D.R.nV / 2)))⁻¹


variable (R) in
structure HkDat (Sb : Finset (PlE D.host)) (i : Fin D.R.m) (k : ℕ) (P : PlE D.host) (α : GA D (Wc D i))
    (Rr : Finset (GA D (Wc D i))) : Prop where
  split : IsSplitPl D.host P
  offS : P ∉ Sb
  odd : ((2 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal
  le : k ≤ D.R.r
  elt : IsHeckeAt (Wc D i) P k α
  reps : Bridge.IsDC (levG (Wc D i) (R.βW i) (R.datWp i R.triv)) α Rr

def EigAd (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (Sb : Finset (PlE D.host))
    (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) : Prop :=
  ∀ (i : Fin D.R.m) σ k P α Rr, HkDat R Sb i k P α Rr → D.nd.goodRow σ → ∀ x ∈ D.what₂.isot (i.1 + 1) σ,
    hkNorm R i k P • heckeOn (R.MW i (sg0 D A3.A)) Rr ((R.HW i (sg0 D A3.A)).e (Y.mj.eW i x)) =
      D.what₂.embLL ((eig (i.1 + 1) σ k P : ↥D.LL0) : D.what₂.LL) • (R.HW i (sg0 D A3.A)).e (Y.mj.eW i x)

structure RatAd (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (kKs : Ks →+* ↥D.LL0)
    (hk : ∀ x : Ks, ((kKs x : ↥D.LL0) : D.what₂.LL) = algebraMap Ks D.what₂.LL x) (In : RatIn D (ratDatR R cG kKs hk)) : Prop where
  hecke : ∀ j k P α Rr, 1 ≤ j → j ≤ D.R.m → HkDat R In.Sb (idxOf D j) k P α Rr → ∀ x : Fin (R.nW (idxOf D j)) → D.what₂.LL,
    (R.HW (idxOf D j) (sg0 D A3.A)).e ((R.FW (idxOf D j)).j (sg0 D A3.A) (In.hL j k P x)) =
      hkNorm R (idxOf D j) k P • heckeOn (R.MW (idxOf D j) (sg0 D A3.A)) Rr
        ((R.HW (idxOf D j) (sg0 D A3.A)).e ((R.FW (idxOf D j)).j (sg0 D A3.A) x))
  eig : EigAd Y In.Sb In.eig
  Sb_le : OverSet D In.Sb (lowAll D)
  lvl : ∀ g : G, g ∈ F.P0 ↔ (R.eG.trans cG) g ∈ Formalism.IndefR.NX.U D.nd
  psi : ∀ (u : F.P0) (hu : (R.eG.trans cG) u ∈ Formalism.IndefR.NX.U D.nd),
    (((psiUOf D.nd (NX.xiRed D) In.θ ⟨_, hu⟩ : (↥D.LL0)ˣ) : ↥D.LL0) : D.what₂.LL) = (((F.ψ0 u)⁻¹ : D.what₂.LLˣ) : D.what₂.LL)

variable {cG : G0 R.Pg D.R.r ≃* G0g D.nd} {S : RatDat D.ntw}


set_option genInjectivity false in
set_option genSizeOfSpec false in
set_option maxHeartbeats 1000000 in
structure SerAt (YS : NExpRealS R cG S) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW j σ).Vec) (X : NExpTied D)
    (PV : ∀ i : Fin D.R.m, principalLevelFrame.RowPsi (Vc D i) D.R.nV) (cf : CharFrame D)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) : Type 1 where
  ex : GlobalTheory.SeriesTie.ExportTie YS v₀
  bad : ∀ i, ex.ρ.bad i = GlobalTheory.SeriesTie.normProd (D.ntw.S0 i)
  ch : ∀ i P, IsSplitPl D.host P → (P ∈ ex.ρ.ch i ↔ P ∈ Set.range Pq)
  join : ∀ i (j : Fin D.R.m) b k Q ψ (hA : NX.AdmTw D i k Q ψ), IntegralHeckeForms.TwOK i k Q ψ →
    ∃ ω : (X.mtV i (j.1 + 1) b k Q ψ (by omega) (by omega) hA).W →ₛₗ[ex.ρ.ek i b k] PolF D (Wc D j).rank (Vc D j).rank,
      Function.Injective ω ∧ ∀ f g, (ex.tie i j b).rdV k Q ψ f ((finHom _).rangeRestrict ((PV j).ψ g)) =
        ω (((X.mtV i (j.1 + 1) b k Q ψ (by omega) (by omega) hA).real f).1 g)
  sup : ∀ i j b (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (x : D.nexp.Fm i j b), x ∈ D.nexp.Bsup i j b ↔ YS.eF i j b h1 h2 x ∈ Bsup S i j b
  off : ∀ i j b, ¬ (1 ≤ j ∧ j ≤ D.R.m) → Subsingleton (D.nexp.Fm i j b)
  lam : GlobalTheory.LamTie.LamDat D
  lam_ok : lam.Ok
  lam_teich : lam.Teich
  lam_C : lam.C = cf
  lam_q : lam.q0 = AbsolutelyIrreducibleSpan.q0 D
  lam_tie : GlobalTheory.LamTie.IsLamTieFull D.ntw lam

def EMtTheta (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (YS : NExpRealS R cG S) (c : NChoice D) : Prop :=
  ∀ (w : D.what₂.places.Pl) (i : Fin D.R.m), D.what₂.muAt w ≠ D.what₂.mu0 →
    ∀ x ∈ Idx.TjV D (D.what₂.muTw w) (i.1 + 1), ∀ (n : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → FmK S (i.1 + 1)),
      (R.FW i).j (sg0 D A3.A) ((YS.fi i).e (∑ k, a k • (show ↥(S.A (i.1 + 1)).WK from f k).1)) =
        Y.mj.eW i (D.what₂.thetaP (D.what₂.muTw w) (i.1 + 1) (D.what₂.jMt (D.what₂.muTw w) (i.1 + 1) x)) →
      NChoice.thPe D c w (i.1 + 1) (c.eMt w (i.1 + 1) x) =
        ∑ k, c.embW w (a k) ⊗ₜ[D.ntw.O (c.twI w)]
          (YS.eF (c.twI w) (i.1 + 1) (c.sd w) (by omega) (by omega)).symm ((1 : KB S (c.twI w) (c.sd w)) ⊗ₜ[S.Ks] f k)

end Rows

def XdAll {D : D7} (xd : ThData D) : Prop := ∀ i j b, 1 ≤ j → j ≤ D.R.m → xd.xd0 i j b = Set.univ

end GlobalTheory.HeightCounting

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsTiedOfIsRecG
noncomputable section

namespace GlobalTheory.Mem.Top.Bl.LayerTwoModel

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.GroupRetwisting NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.BasicNotions.factResChar

open Formalism.MainNotions.G Formalism.UG Formalism.L2.Forms Formalism.L2.G

theorem isRecG_retie {sc D Gt c H F} (h : IsRecG sc D Gt c H F) (g') : IsRecG sc D Gt c ⟨H.lev0, g'⟩ F := by
  obtain ⟨D0, Lc, I, ψ, hd, H0, hL, T, B, hBs, hB, iK, lam, hK, hPos, CH, heq⟩ := h
  cases heq
  exact ⟨D0, Lc, I, ψ, hd, ⟨_, g'⟩, hL, _, B, hBs, hB, iK, lam, hK, hPos, CH, rfl⟩

theorem gatNum_of_isRecG {sc D Gt c H F} (h : IsRecG sc D Gt c H F) : GatNum sc D := by
  obtain ⟨D0, Lc, I, ψ, hd, H0, hL, T, B, hBs, hB, iK, lam, hK, hPos, CH, heq⟩ := h
  cases heq
  intro u w hg
  exact ⟨rfl, rfl⟩

section Stages
variable {B : Base} {C : Cols B} (W W' : RowsRest B C) (V : DivStage B C W) (V' : DivStage B C W') (S : SStage B C W)
  (S' : SStage B C W') (N : NStage B C W) (N' : NStage B C W') (G G' : GJStage B C)

end Stages

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B}

theorem gIs2_iff (w : ColW B f T) (G : GJStage B w.C) : GIs2 K w G ↔
    ∀ W V S N, Formalism.L2.Theta.VolTieG (w.D ⟨W, V, S, N, G⟩) ∧ Nonempty (ColumnDataSplitPrimes K w ⟨W, V, S, N, G⟩) :=
  by
    constructor
    · intro h W V S N
      exact ⟨(h W V S N).1, (h W V S N).2.2⟩
    · intro h W V S N
      obtain ⟨a, ⟨t⟩⟩ := h W V S N
      exact ⟨a, gatNum_of_isRecG t.isRec, ⟨t⟩⟩

end GlobalTheory.Mem.Top.Bl.LayerTwoModel

end
end
