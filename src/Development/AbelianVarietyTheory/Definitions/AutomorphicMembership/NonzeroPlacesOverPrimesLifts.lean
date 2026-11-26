module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame
public import Lean.LibrarySuggestions.Basic
public import Lean.Elab.Command
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RelabelledWeight
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrbitThickSt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.Rw

attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI

variable {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z₀ : w.Lt} {hX : B.fields.Ok} {Wt : Set B.places.Pl}
  {z₀ : Dat (w.st Z₀) w.I hX T Wt} {q : RowPk w z₀} {o : q.Over}

structure Moved.Copy (m : Moved o) : Prop where
  core : HEq m.z.core (coreJ (a := ⟨Z₀.W, Z₀.V, Z₀.S, Z₀.N, Z₀.G⟩) ⟨q.W o.η o.hη, o.V, o.S, o.N, o.G⟩ z₀.core)
  R : HEq m.z.R (real3 (a := ⟨Z₀.W, Z₀.V, Z₀.S, Z₀.N, Z₀.G⟩) ⟨q.W o.η o.hη, o.V, o.S, o.N, o.G⟩ (iK := z₀.alg) z₀.R)

structure Moved.Coh (m : Moved o) : Prop where
  tupT : HEq m.y.tupT q.y.tupT
  PY : HEq m.y.PY.ψ q.y.PY.ψ
  PW : HEq (fun i => (m.y.PW i).ψ) fun i => (q.y.PW i).ψ
  rep : HEq m.t.rep q.t.rep
  jE : ∀ b, HEq (m.t.ch b).jE (q.t.ch b).jE
  jM : ∀ b, HEq (m.t.ch b).jM (q.t.ch b).jM
  jX : ∀ b, HEq (m.t.ch b).jX (q.t.ch b).jX
  eW : HEq m.t.lf.eW q.t.lf.eW
  jMt : HEq m.t.lf.jMt q.t.lf.jMt

structure ReadPk.Pin {m : Moved o} {s : Side0 o} (r : ReadPk m s) : Prop where
  rep : ∀ π, (principalLevelFrame.rowRepR m.z.R.θ (r.Y.eFT π)).Iso (m.t.rep π)
  jE : ∀ x, HEq (r.Y.Ish.jE x).1 ((m.t.ch true).jE x)
  heq_eigen_embedding_zero : ∀ x, HEq (r.Y.Iz.jE x).1 ((m.t.ch false).jE x)
  eW : ∀ i x, HEq (r.Y.mj.eW i x) (m.t.lf.eW i x)
  jMt : ∀ μ h i x, HEq (r.Y.IL.jMt μ h i x).1 (m.t.lf.jMt μ i x)


set_option genInjectivity false in
set_option genSizeOfSpec false in
structure Pre2 (K : Ctx) (w : ColW B f T) : Type 1 where
  Z₀ : w.Lt
  hX : B.fields.Ok
  Wt : Set B.places.Pl
  z : Dat (w.st Z₀) w.I hX T Wt
  q : RowPk w z
  g : GIs2 K w Z₀.G
  coh : Coh B T
  grp : GrpTrue Z₀.N f
  grpAt : GrpAt (w.st Z₀) w.I
  kap : DV.KapDef (w.D Z₀)
  intersectionNumber_baseChange : Holds z.R z.F
  exAt : z.R.toRealDat.ExAt
  inGeo : GlobalTheory.RealGeo.InGeo z.geo
  core : CoreP z
  exact : Wt = z.W1 (F0K K.s (w.D Z₀))
  sub : ∀ v ∈ Wt, B.places.resChar v ∈ T.pl
  supp : ∀ v, v ∉ Wt → T.psi v = 1
  std : z.Std

def HasPk : WP := fun K _ _ _ w => Nonempty (Pre2 K w)

structure HoldsL {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) : Prop where
  heckeR : ∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint
  heckeL : ∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint
  hecke : R.PHecke F
  gUnit : R.PGUnit F
  gEquiv : R.PGEquiv F
  block : (R.toCx3 F).zs.InBlock
  liftTest : Formalism.IndefR.Rat.LiftTest (R.toCx3 F)
  liftTestB : Formalism.IndefR.Rat.LiftTestB (R.toCx3 F) false
  liftOnto : ∀ hW, HeckeIntertwiningLifts A3 (R.toCx3 F) hW → U2.OntoC A3 (R.toCx3 F) F.P0 F.ψ0 F.P1 F.ψ1 hW
  unif : R.toRealDat.LUnif
  mLat : (R.toCx3 F).MLat false
  levW : R.PLevW F
  thmA : R.PThmA
  sumW : (R.toCx3 F).PartsW false
  aux : UnusedChoiceStatements R F
  ok : A3.fam3.Ok3 1
  sep : A3.fam3.TypesSep3

theorem HoldsL.of_holds {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} (h : Holds R F) :
    HoldsL R F :=
  ⟨h.prim.heckeR, h.prim.heckeL, h.prim.hecke, h.prim.gUnit, h.prim.gEquiv, h.prim.block, h.prim.liftTest, h.prim.liftTestB,
    h.prim.liftOnto, h.prim.unif, h.prim.mLat, h.prim.levW, h.prim.thmA, h.prim.sumW, h.aux, h.ok, h.sep⟩

def LowerUnitaryCaseCondition : Prop := GroupRetwisting.Step KPx (fun _ _ _ _ => True) fun K B f T => ∀ w : ColW B f T, Pinned K B f T w →
  ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I →
    z.R.toRealDat.ExAt → GlobalTheory.RealGeo.InGeo z.geo → HoldsL z.R z.F

def WeightCaseCondition : Prop := StepW Start fun K B f T w => ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
  (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → DV.KapDef (w.D Z) → z.R.toRealDat.ExAt →
    GlobalTheory.RealGeo.InGeo z.geo → CoreP z → GIs2 K w Z.G → Wt = z.W1 (F0K K.s (w.D Z)) → (∀ v ∈ Wt, B.places.resChar v ∈ T.pl) →
    Holds z.R z.F

def BkLaw (D : D7) : Prop := WeightDegreeSizes.RationalMapValues D → D.BuRational

structure St {K : Ctx} (P : Pre2 K w) : Type 1 where
  o : P.q.Over
  fits : o.Fits
  G_eq : o.G = P.Z₀.G
  etaF : o.V.div.etaF = 6 * K.s.x ^ (-K.C.P.CF)
  bk : BkLaw (w.D o.Z)
  m : Moved o
  copy : m.Copy
  coh : m.Coh
  s : Side0 o
  r : ReadPk m s
  pin : r.Pin

def HasBare : WP := fun K _ _ _ w => ∃ (P : Pre2 K w) (x : St P), IsEmpty x.o.N.nd.Loc ∧ ∀ j v, x.o.η j v = 0

structure RowsSame {K : Ctx} {Z Z' : w.Lt} {p0 : BaseLevelRowSide (w.D Z)} {p0' : BaseLevelRowSide (w.D Z')} (t : RowsT K w Z Wt p0)
    (t' : RowsT K w Z' Wt p0') : Prop where
  Xg : t'.r.z.Xg = t.r.z.Xg
  tr : t'.r.z.tr = t.r.z.tr
  core : HEq t'.r.z.core (coreJ (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) ⟨Z'.W, Z'.V, Z'.S, Z'.N, Z'.G⟩ t.r.z.core)
  R : HEq t'.r.z.R (real3 (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) ⟨Z'.W, Z'.V, Z'.S, Z'.N, Z'.G⟩ (iK := t.r.z.alg) t.r.z.R)
  cG : HEq t'.r.z.cG t.r.z.cG
  tup : HEq t'.r.Y.tup t.r.Y.tup
  tupT : HEq t'.r.Y.tupT t.r.Y.tupT
  PY : HEq t'.r.Y.PY.ψ t.r.Y.PY.ψ
  PW : HEq (fun i => (t'.r.Y.PW i).ψ) fun i => (t.r.Y.PW i).ψ
  rep : HEq (fun π => principalLevelFrame.rowRepR t'.r.z.R.θ (t'.r.Y.eFT π)) fun π => principalLevelFrame.rowRepR t.r.z.R.θ (t.r.Y.eFT π)
  jE : HEq (fun x => (t'.r.Y.Ish.jE x).1) fun x => (t.r.Y.Ish.jE x).1
  heq_eigen_embedding_zero : HEq (fun x => (t'.r.Y.Iz.jE x).1) fun x => (t.r.Y.Iz.jE x).1
  eE : HEq t'.r.Y.eE t.r.Y.eE
  jA : HEq t'.r.Y.jA t.r.Y.jA
  jA0 : HEq t'.r.Y.jA0 t.r.Y.jA0
  eMt : HEq t'.r.Y.eMt t.r.Y.eMt
  eW : HEq t'.r.Y.mj.eW t.r.Y.mj.eW
  jW : HEq t'.r.Z.jW t.r.Z.jW
  eRR : HEq t'.r.Z.eRR t.r.Z.eRR
  eRR0 : HEq t'.r.Z.eRR0 t.r.Z.eRR0

end GlobalTheory.Mem.R3.Rw

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.UpLReStage
noncomputable section

namespace GlobalTheory.Mem.SRe

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.L2.DIV
  Formalism.MainNotions Formalism.L2.Forms NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.R3.Tr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl

attribute [local instance] Formalism.BasicNotions.Host.cmStar


set_option genInjectivity false in
set_option genSizeOfSpec false in
structure RowPk (D : D7) : Type 1 where
  G' : Type
  [grp : Group G']
  [fin : Fintype G']
  Pl0 : Type
  T : Type
  A : FamIn D.what₂.LL G' Pl0 T D.R.m
  Ks : Type
  [fld : Field Ks]
  [nf : NumberField Ks]
  [iK : Algebra Ks D.what₂.LL]
  R : RealDat D A Ks
  F : Face D A
  eE : D.what₂.EE →ₗ[ℂ] R.HE.H

attribute [instance] RowPk.grp RowPk.fin RowPk.fld RowPk.nf RowPk.iK

def RowPk.SAt {D : D7} (p : RowPk D) (F₀ : ∀ u, Forms0 D u) : Type 1 := Top.Bl.SAt p.R p.F p.eE F₀

def upL {B : Base} {C : Cols B} (a : Late B C) (S' : SStage B C a.W) (N : ∀ u, Submodule (𝓞 B.LL) (a.V.div.Nu u).V)
    (h : B.Word → ℝ) : Late B C := ⟨a.W, (Db.setDivZ a N h).V, S', a.N, a.G⟩


set_option maxHeartbeats 4000000 in
def RowPk.up {B : Base} {C : Cols B} (a : Late B C) (S' : SStage B C a.W) (N : ∀ u, Submodule (𝓞 B.LL) (a.V.div.Nu u).V)
    (h : B.Word → ℝ) (p : RowPk a.D) : RowPk (upL a S' N h).D :=
  @RowPk.mk (upL a S' N h).D p.G' p.grp p.fin p.Pl0 p.T (famM (upL a S' N h) p.A) p.Ks p.fld p.nf (alg (upL a S' N h) p.iK)
    (real (upL a S' N h) p.R) (face (upL a S' N h) p.F) ((p.eE))

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B}


set_option maxHeartbeats 4000000 in
def pkOf {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)} (r : RowsT K w Z Wt p0) : RowPk (Late.D Z) where
  G' := _
  Pl0 := _
  T := _
  Ks := _
  A := _
  R := r.r.z.R.toRealDat
  F := r.r.z.F.lv2
  eE := r.r.Y.eE


set_option maxHeartbeats 4000000 in
theorem sx_eq {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)} (r : RowsT K w Z Wt p0) (col : ColT w Z) :
    SX K B f T w Z Wt p0 r col = (pkOf r).SAt fun u => (col.C.forms u).to0 := (Eq.refl (SX K B f T w Z Wt p0 r col))


set_option maxHeartbeats 4000000 in
def LevelThreeCondition (𝒮 : Slots) : Prop :=
  ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (l : Lv3 𝒮 K w Z) (S' : SStage B w.C Z.W)
    (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ),
    ∃ l' : Lv3 𝒮 K w (upL Z S' N h), pkOf l'.what₂ = (pkOf l.what₂).up Z S' N h


set_option maxHeartbeats 4000000 in
def SxMv : Prop :=
  ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (p0 : BaseLevelRowSide (w.D Z))
    (r : RowsT K w Z Wt p0) (col : ColT w Z) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ)
    (p0' : BaseLevelRowSide (w.D (Db.setDivZ Z N h))) (t : RowsT K w (Db.setDivZ Z N h) Wt p0') (col' : ColT w (Db.setDivZ Z N h)),
    HEq (pkOf t) ((pkOf r).up Z Z.S N h) → Nonempty (SX K B f T w Z Wt p0 r col) →
      Nonempty (SX K B f T w (Db.setDivZ Z N h) Wt p0' t col')


set_option maxHeartbeats 4000000 in
def SameCar {D : D7} (F F' : ∀ u, Forms0 D u) : Prop :=
  ∀ u : D.what₂.Word, (F' u).cls0.lev.Lb = (F u).cls0.lev.Lb ∧ (F' u).cls0.lev.U = (F u).cls0.lev.U ∧
    HEq (F' u).cls0.lev.chi (F u).cls0.lev.chi ∧ (F' u).cls0.y = (F u).cls0.y ∧ (F' u).val0.eY = (F u).val0.eY


set_option maxHeartbeats 4000000 in
def SameStd : Prop :=
  ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Zn : New (Late.D Z)) (col : ColT w Z)
    (col' : ColT w (reL Z Zn)) (F₁ : ∀ u, Forms0 (reL Z Zn).D u), SameL Z Zn (fun u => (col.C.forms u).to0) F₁ →
      SameCar F₁ fun u => (col'.C.forms u).to0

end GlobalTheory.Mem.SRe

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LineModel
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.LocM

namespace GlobalTheory.ShFam.Pad

structure FinLB (X : Scheme.{0}) : Type where
  n : ℕ
  U : Fin n → X.Opens
  g : ∀ i k, Γ(X, U i ⊓ U k)ˣ
  isLB : LB.IsLB ⟨Fin n, U, g⟩

abbrev FinLB.lb {X : Scheme.{0}} (L : FinLB X) : LB X := ⟨Fin L.n, L.U, L.g⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

structure LineModel (Z : Mdl Y i₀) (b : Bool) (st : ((E →+* ℂ) × ℕ) ⊕ ℕ) (x : Letter Dw) : Type where
  L : FinLB Z.X
  r : ∀ (a : Fin Z.m) (i : Fin L.n), Γ(Z.X, (Z.U a).1 ⊓ L.U i)ˣ
  trans : ∀ (k : Type) [Field k] (w : Sp k ⟶ Z.X) a i i', ⊤ ≤ w ⁻¹ᵁ ((Z.U a).1 ⊓ (L.U i ⊓ L.U i')) →
    valF w _ (r a i').val = valF w _ (L.g i i').val * valF w _ (r a i).val
  chart : ∀ (k : Type) [Field k] a a' i (φ : Γ(Z.X, (Z.U a).1) →+* k) (φ' : Γ(Z.X, (Z.U a').1) →+* k)
    (cf : Fin (Dw.mult x.1) → k), spMap φ ≫ Z.chart a = spMap φ' ≫ Z.chart a' →
    ⊤ ≤ (spMap φ ≫ Z.chart a) ⁻¹ᵁ L.U i → (∀ m, x.2 < m → cf m = 0) →
    IsCombAtG (Y Z.i).t (spMap φ ≫ Z.chart a ≫ Z.π) ((Z.fr a).bc φ x.1) cf ((Z.fr a').bc φ' x.1 x.2) →
    valF (spMap φ ≫ Z.chart a) _ (r a i).val = valF (spMap φ ≫ Z.chart a) _ (r a' i).val * cf x.2
  norm : ∀ (y : Z.Pt) a i (φ : Γ(Z.X, (Z.U a).1) →+* ↥y.C.S), spMap φ ≫ Z.chart a = y.gen → ⊤ ≤ y.z ⁻¹ᵁ L.U i →
    Real.log ‖valF y.gen _ (r a i).val‖ + lnStep (Y Z.i).t (y.gen ≫ Z.π) ((Z.fr a).bc φ) p b st = 0

structure admitted (Y : LocalSystem Xo p W) (i₀ : Idx H p) : Type where
  Z : Mdl Y i₀
  full : ∀ τ k, k ≤ Dw.mult τ → k ∈ Z.ty τ
  n : ℕ
  lvl : Z.i.l.M = i₀.l.M ∧ Z.i.l.Mb = i₀.l.Mb ∧ Z.i.l.A = i₀.l.A * p ^ n
  line : ∀ (b : Bool) (st : ((E →+* ℂ) × ℕ) ⊕ ℕ) (x : Letter Dw), letterOf Dw st = some x → LineModel Z b st x

variable {D : D7}


open Classical in
def placeW (D : D7) (p : ℕ) [Fact p.Prime] (la : PlL D p) (jc : DV.KW p →+* ℂ) : ValuationSubring ℂ :=
  Classical.epsilon fun W => (∀ x : D.what₂.LL, D.what₂.embLL x ∈ W ↔ la.1.valuation D.what₂.LL x ≤ 1) ∧
    ∀ a : DV.KW p, jc a ∈ W ↔ a ∈ (algebraMap (WittVector p (AlgebraicClosure (ZMod p))) (DV.KW p)).range

abbrev AdmAt {A : Amb D} {N j : ℕ} (S : Sig A N j) (κ : Lv A) {p : ℕ} (hp : p.Prime) {W : ValuationSubring ℂ}
    (hW : (p : ℂ) ∈ W.nonunits) : Type :=
  admitted (S.sys.Y p W hp hW) ⟨κ.l, κ.c, κ.good p hp⟩

def AdmEx {A : Amb D} {N j : ℕ} (S : Sig A N j) (κ : Lv A) : Prop :=
  ∀ (p : ℕ) (hp : p.Prime) (W : ValuationSubring ℂ) (hW : (p : ℂ) ∈ W.nonunits) (n : ℕ),
    1 + 1 / ((p : ℝ) - 1) < n → ∃ z : AdmAt S κ hp hW, z.n = n

end GlobalTheory.ShFam.Pad
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLinearHomPull
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht GlobalTheory.TorusModel GlobalTheory.TorusExt GlobalTheory.Serre

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RayEv

section Ray

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O D.X]

structure Ray (oa : D.OAct O) : Type 1 where

  H : Over (Sp R)
  [grp : GrpObj H]
  [comm : IsCommMonObj H]

  Φ : ∀ T, (T ⟶ H) ≃ GtPt D T
  isGt : (splitExt D).IsGt H
  rep : Represents Φ

  ρ : RingAct H O
  smul : ∀ (a : O) T (x : T ⟶ H), FormalPoint.IsSmulPt oa a (Φ T x) (Φ T (x ≫ ρ.act a))

attribute [instance] Ray.grp Ray.comm

instance (oa : D.OAct O) : Nonempty (Ray oa) := by
  have hL := GlobalTheory.allSixLaws.1.globalFns
  obtain ⟨H, _, _, hH⟩ := exists_isGt hL (splitExt D)
  obtain ⟨Φ, hΦ⟩ := exists_points hL hH
  obtain ⟨ρ, hρ⟩ := exists_ringAct hL oa (Φ := Φ) hΦ
  exact ⟨{ H := H, Φ := Φ, isGt := hH, rep := hΦ, ρ := ρ, smul := hρ }⟩

def Chr (D : DegPre R) : Type := D.X

instance : AddCommGroup (Chr D) := inferInstanceAs (AddCommGroup D.X)

instance : Module O (Chr D) := Module.compHom D.X (starRingEnd O)


variable (D O) in
def torAct : OAct O (splitTorus (Sp R) (Chr D)) := Diag.diagAct (Sp R) O (Chr D)

theorem exists_torPt {T : Over (Sp R)} (x : T ⟶ splitTorus (Sp R) (Chr D)) : ∃ g : GtPt D T, g.b = 1 ∧
    ∀ (χ : D.X) (Z : Scheme.{0}) (r : Z ⟶ T.left) y J, Good D.P.L y J →
      (val (g.s χ) r y J).val = gs r y ⊤ ((coord x).hom (AddMonoidAlgebra.single χ 1)) := by
  let u : Multiplicative D.X →* Γ(T.left, ⊤) :=
    { toFun := fun χ => (coord x).hom (AddMonoidAlgebra.single χ.toAdd 1)
      map_one' := Diag.coord_single_zero x
      map_mul' := fun a b => Diag.coord_single_add x _ _ }
  let v : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (Y := T.left) (K := PEmpty.{1}) PEmpty.elim PEmpty.elim) := fun χ =>
    ⟨fun _ => res le_top (u.toHomUnits (Multiplicative.ofAdd χ))⟩
  have hv : ∀ χ (Z : Scheme.{0}) (r : Z ⟶ T.left) y J, Good D.P.L y J →
      val (v χ) r y J = gm r y ⊤ (u.toHomUnits (Multiplicative.ofAdd χ)) := fun χ Z r y J hJ =>
    gm_res r y _ (hJ.mem PEmpty.elim r) _
  obtain ⟨g, hb, hg⟩ := exists_pt (1 : T ⟶ D.P.A) v (fun χ i j => by
      obtain rfl : i = j := funext fun k => k.elim
      have e : (LB.LinComb D.P.L (Y := T.left) (K := PEmpty.{1}) PEmpty.elim PEmpty.elim).g i i = 1 := by
        dsimp only [LB.LinComb]
        erw [Fintype.prod_empty]
        rfl
      rw [e, _root_.one_mul])
    (fun χ U _ h => by
      rw [prod_pt, _root_.mul_one, Fintype.prod_empty, inv_mul_cancel, _root_.one_mul, mul_inv_cancel])
    (fun y J hJ => by rw [hv _ _ _ _ _ hJ, ofAdd_zero, map_one, map_one])
    (fun χ χ' y J hJ => by
      have C : IsCub (th D (T := T) y J) := isCub_cubV D.cub hJ
      rw [C.face₃, _root_.mul_one, hv _ _ _ _ _ hJ, hv _ _ _ _ _ hJ, hv _ _ _ _ _ hJ, ofAdd_add, map_mul, map_mul])
  exact ⟨g, hb, fun χ Z r y J hJ => by
    rw [hg _ _ _ _ _ hJ, hv _ _ _ _ _ hJ]; exact (gs_unit r y ⊤ trivial _).symm⟩

namespace Ray

variable {oa : D.OAct O} (Y : Ray oa)

def act : OAct O Y.H := ofRingAct Y.ρ


variable (oa) in
def actB : OAct O D.P.A := ofRingAct oa.onB.toRingAct

def q : Y.H ⟶ D.P.A := (Y.Φ Y.H (𝟙 _)).b

theorem Φ_b {T : Over (Sp R)} (x : T ⟶ Y.H) : (Y.Φ T x).b = x ≫ Y.q := by
  have h := ((isPull_iff _ _ _).1 (Y.rep.1 T Y.H x (𝟙 _))).1
  rwa [Category.comp_id] at h

theorem q_linear : IsLinearHom Y.act (actB oa) Y.q :=
  ⟨isMonHom_of_mul _ fun T x x' => by
      rw [← Φ_b, ← Φ_b, ← Φ_b]; exact ((TorusModel.isAdd_iff _ _ _).1 (Y.rep.2 T x x')).1,
    fun a => by
      have h := (Y.smul a _ (𝟙 _)).1
      rw [Φ_b, Category.id_comp] at h
      exact h⟩

def i : splitTorus (Sp R) (Chr D) ⟶ Y.H := (Y.Φ _).symm (exists_torPt (𝟙 _)).choose

theorem Φ_i {T : Over (Sp R)} (x : T ⟶ splitTorus (Sp R) (Chr D)) : (Y.Φ T (x ≫ Y.i)).b = 1 ∧
    ∀ (χ : D.X) y J, Good D.P.L y J →
      (cv (Y.Φ T (x ≫ Y.i)) χ y J).val = gs (𝟙 _) y ⊤ ((coord x).hom (AddMonoidAlgebra.single χ 1)) := by
  obtain ⟨h₁, h₂⟩ := (isPull_iff _ _ _).1 (Y.rep.1 T _ x Y.i)
  obtain ⟨e₁, e₂⟩ := (exists_torPt (D := D) (𝟙 _)).choose_spec
  have e : Y.Φ _ Y.i = (exists_torPt (D := D) (𝟙 _)).choose := Equiv.apply_symm_apply _ _
  rw [e] at h₁ h₂
  refine ⟨by rw [h₁, e₁, MonObj.comp_one], fun χ y J hJ => ?_⟩
  rw [h₂ χ y J hJ, e₂ χ _ _ y J hJ]
  conv_rhs => rw [← Category.comp_id x, coord_comp]
  exact (gs_eq x.left y ⊤ trivial _).trans (gs_eq (𝟙 _) y ⊤ trivial _).symm

theorem i_q : Y.i ≫ Y.q = 1 := by
  have h := (Y.Φ_i (𝟙 _)).1
  rwa [Φ_b, Category.id_comp] at h

theorem i_linear : IsLinearHom (torAct D O) Y.act Y.i := by
  have hL := GlobalTheory.allSixLaws.1.globalFns
  refine ⟨isMonHom_of_mul _ fun T x x' => (Y.Φ T).injective ?_, fun a => (Y.Φ _).injective ?_⟩
  · refine isAdd_unique ((TorusModel.isAdd_iff _ _ _).2 ⟨?_, fun χ y J hJ => Units.ext ?_⟩) (Y.rep.2 T _ _)
    · rw [(Y.Φ_i _).1, (Y.Φ_i _).1, (Y.Φ_i _).1, _root_.mul_one]
    · have C : IsCub (th D (T := T) y J) := isCub_cubV D.cub hJ
      rw [(Y.Φ_i x').1, C.face₃, _root_.mul_one, Units.val_mul, (Y.Φ_i _).2 χ y J hJ, (Y.Φ_i _).2 χ y J hJ,
        (Y.Φ_i _).2 χ y J hJ]
      exact (congrArg (gs _ y ⊤) (Diag.coord_mul x x' χ)).trans (gs_mul (𝟙 _) y ⊤ trivial _ _)
  · obtain ⟨h₁, h₂⟩ := (isSmulPt_iff hL oa a _ _).1 (Y.smul a _ (𝟙 _ ≫ Y.i))
    have := oa.onB.hom a
    have := oa.onB.hom (star a)
    rw [Category.id_comp] at h₁ h₂
    have k := Y.Φ_i (𝟙 _)
    rw [Category.id_comp] at k
    refine pt_ext ?_ fun χ y J hJ => Units.ext ?_
    · exact (Y.Φ_i _).1.trans (h₁.trans (by rw [k.1, MonObj.one_comp])).symm
    · have C : IsCub (th D (T := splitTorus (Sp R) (Chr D)) y J) := isCub_cubV D.cub hJ
      have e := (rosGen_add hL oa a hJ 1 1 (cP D _ χ)).2
      rw [_root_.mul_one, MonObj.one_comp, C.face₃, C.face₃, _root_.mul_one, _root_.one_mul] at e
      refine ((Y.Φ_i _).2 χ y J hJ).trans (Eq.trans ?_ (congrArg Units.val (h₂ χ y J hJ)).symm)
      rw [k.1, mul_eq_left.1 e.symm, _root_.mul_one, k.2 _ y J hJ]
      refine congrArg (gs _ y ⊤) ?_
      have := Diag.coord_comp_diagMap_single (𝟙 (splitTorus (Sp R) (Chr D)))
        (DistribSMul.toAddMonoidHom (Chr D) a) χ
      rw [Category.id_comp] at this
      exact this

theorem isKernel : IsPullback Y.i (toUnit _) Y.q η[D.P.A] := by
  have ex : ∀ {T : Over (Sp R)} y, ∃ J, Good D.P.L (Z := T.left) y J := fun y => by
    choose I hI using fun χ => exists_chart D.P.isLB ((χ : _ ⟶ D.P.A.left) y)
    exact ⟨I, hI⟩
  refine Diag.isPullback_toUnit_of_lift _ Y.i_q (fun {T} a b h => Diag.hom_ext fun χ => fn_ext fun y _ => ?_)
    fun {T} x hx => ?_
  · obtain ⟨J, hJ⟩ := ex y
    exact ((Y.Φ_i a).2 χ y J hJ).symm.trans (h ▸ (Y.Φ_i b).2 χ y J hJ)
  · have hb : (Y.Φ T x).b = 1 := (Y.Φ_b x).trans hx
    have hF : ∀ χ, FormEq (DegPre.gtφT D T (Y.Φ T x).b χ) DegPre.gtε (K' := PEmpty.{1}) PEmpty.elim PEmpty.elim :=
      fun χ U _ h => by
        rw [prod_pt, hb, _root_.mul_one, Fintype.prod_empty, inv_mul_cancel, _root_.one_mul, mul_inv_cancel]
    choose s _ vs using fun χ => exists_gen D.P.isLB (hF χ) _ ((Y.Φ T x).isGen χ)
    have le : (⊤ : T.left.Opens) ≤ LB.wchart D.P.L (K := PEmpty.{1}) PEmpty.elim PEmpty.elim :=
      fun _ _ => Set.mem_iInter.2 fun k => k.elim
    let u : D.X → Γ(T.left, ⊤)ˣ := fun χ => res le ((s χ).s PEmpty.elim)
    have hu : ∀ χ y J, Good D.P.L y J → gs (𝟙 _) y ⊤ (u χ).val = (cv (Y.Φ T x) χ y J).val := fun χ y J hJ =>
      (gs_unit _ y ⊤ trivial _).trans (congrArg Units.val ((gm_res _ y le trivial _).trans
        ((val_of (s χ) _ y J PEmpty.elim fun k => k.elim).symm.trans (vs χ _ _ y J hJ))))
    let g : Multiplicative (Chr D) →* Γ(T.left, ⊤) :=
      { toFun := fun χ => (u χ.toAdd).val
        map_one' := fn_ext fun y _ => by
          obtain ⟨J, hJ⟩ := ex y
          refine (hu 0 y J hJ).trans ?_
          rw [cv_zero _ hJ, gs_eq _ y ⊤ trivial, map_one, map_one, Units.val_one]
        map_mul' := fun a b => fn_ext fun y _ => by
          obtain ⟨J, hJ⟩ := ex y
          have C : IsCub (th D (T := T) y J) := isCub_cubV D.cub hJ
          have e := cv_add (Y.Φ T x) hJ a.toAdd b.toAdd
          rw [hb, C.face₃, _root_.mul_one] at e
          refine (hu _ y J hJ).trans (Eq.trans ?_ (gs_mul _ y ⊤ trivial _ _).symm)
          exact (congrArg Units.val e).trans (congrArg₂ (· * ·) (hu _ y J hJ) (hu _ y J hJ)).symm }
    refine ⟨Diag.ofChar T g, (Y.Φ T).injective (pt_ext ((Y.Φ_i _).1.trans hb.symm) fun χ y J hJ => Units.ext ?_)⟩
    exact ((Y.Φ_i _).2 χ y J hJ).trans ((congrArg (gs _ y ⊤) (Diag.coord_ofChar T g χ)).trans (hu χ y J hJ))

end Ray

end Ray

section Eig

variable {R S O : Type} [CommRing R] [CommRing S] [CommRing O] (f : R →+* S)
  {G G' : Over (Sp R)} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']

abbrev LieAt (a : OAct O G) : Type := Lie (a.pullback (spMap f))

def lieMap {a : OAct O G} {a' : OAct O G'} {φ : G ⟶ G'} (h : IsLinearHom a a' φ) : LieAt f a →ₗ[S] LieAt f a' :=
  haveI := h.isMonHom
  Lie.map _ _ ((Over.pullback (spMap f)).map φ)

def tanPt {a : OAct O G} (v : LieAt f a) : Over.mk ((epsR S).hom ≫ spMap f) ⟶ G :=
  HTLat.pushEquiv (isGrpPullback_pullback G (spMap f)) _ v.hom

end Eig

end GlobalTheory.RayEv
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousAndSmul
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Matrix MeasureTheory Set Complex
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.L2DbarEstimates GlobalTheory.CxPts GlobalTheory.ShFam
open scoped ContDiff

namespace GlobalTheory.ChernReg

section Flat

variable {d : ℕ}

def polMat (q : (Fin d → ℂ) → ℝ) : Matrix (Fin d) (Fin d) ℂ := fun k l =>
  (q (Pi.single k 1 + Pi.single l 1) - q (Pi.single k 1 - Pi.single l 1) +
    I * q (Pi.single k 1 + I • Pi.single l 1) - I * q (Pi.single k 1 - I • Pi.single l 1)) / 4

def christoffel (b : V d → Matrix (Fin d) (Fin d) ℂ) (z ξ : V d) : V d :=
  WithLp.toLp 2 ((ξ.ofLp ᵥ* Matrix.of fun k l => del (fun v => b v k l) z ξ) ᵥ* (b z)⁻¹)

def jet (b : V d → Matrix (Fin d) (Fin d) ℂ) (n : ℕ) : V d × V d → V d :=
  n.rec Prod.fst fun _ f q => del f q (q.2, -christoffel b q.1 q.2)

variable (b : V d → Matrix (Fin d) (Fin d) ℂ)

def cutoff (t : ℝ) : ℝ := if t < 1 then ((1 - t) ^ 2)⁻¹ * Real.exp (t - 1)⁻¹ else 0

def mean (q f : (Fin d → ℂ) → ℝ) : ℝ := (∫ ξ, f ξ * cutoff (q ξ)) / ∫ ξ, cutoff (q ξ)

section Mass

variable {q : (Fin d → ℂ) → ℝ} (hc : Continuous q) (hh : ∀ (t : ℝ) ξ, q (t • ξ) = t ^ 2 * q ξ)
  (hp : ∀ ξ, ξ ≠ 0 → 0 < q ξ)
include hc hh hp

end Mass

end Flat

section Manifold

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ σ' : k →+* ℂ} {d : ℕ}

abbrev ChartMap (p : Y ⟶ Sp k) (σ : k →+* ℂ) (d : ℕ) : Type := AlgChart p σ d → CxPts p σ → (Fin d → ℂ) → CxPts p σ

def matIn (a : ChartForm p σ d) (c : AlgChart p σ d) (v : V d) : Matrix (Fin d) (Fin d) ℂ := polMat (a c (c.e.symm v))

structure IsExph (a : ChartForm p σ d) (E : ChartMap p σ d) : Prop where

  trans : ∀ (c c' : AlgChart p σ d), ∀ y ∈ c.e.source, y ∈ c'.e.source → ∀ ξ, E c y ξ = E c' y (c.dtrans c' y ξ)

  cont : ∀ c : AlgChart p σ d, ContinuousOn (fun q : V d × V d => E c (c.e.symm q.1) q.2.ofLp) (c.e.target ×ˢ univ)

  smooth : ∀ c c' : AlgChart p σ d, ContDiffOn ℝ ∞ (fun q : V d × V d => c'.e (E c (c.e.symm q.1) q.2.ofLp))
    {q | q.1 ∈ c.e.target ∧ E c (c.e.symm q.1) q.2.ofLp ∈ c'.e.source}

  zero : ∀ c : AlgChart p σ d, ∀ y ∈ c.e.source, E c y 0 = y

  jets : ∀ c : AlgChart p σ d, ∀ y ∈ c.e.source, ∀ (ξ : V d) (n : ℕ),
    iteratedDeriv n (fun t : ℝ => c.e (E c y (t • ξ.ofLp))) 0 = jet (matIn a c) n (c.e y, ξ)

def ConjComm (j : CxPts p σ' → CxPts p σ) (E : ChartMap p σ d) (E' : ChartMap p σ' d) : Prop :=
  ∀ (c : AlgChart p σ d) (c' : AlgChart p σ' d),
    (∀ w ∈ c'.e.source, j w ∈ c.e.source → ∀ i, c'.e w i = starRingEnd ℂ (c.e (j w) i)) →
    ∀ z ∈ c'.e.source, j z ∈ c.e.source → ∀ ξ, j (E' c' z ξ) = E c (j z) (star ξ)

def rhoIn (a : ChartForm p σ d) (E : ChartMap p σ d) (ψ : CxPts p σ → ℝ) (c : AlgChart p σ d) (y : CxPts p σ) (t : ℝ) : ℝ :=
  mean (a c y) fun ξ => ψ (E c y (t • ξ))

structure IsRegConst (a θ : ChartForm p σ d) (Ψ : CxPts p σ → ℝ → ℝ) (A K δ : ℝ) : Prop where
  A_nonneg : 0 ≤ A
  K_nonneg : 0 ≤ K
  δ_pos : 0 < δ
  smooth : ∀ c : AlgChart p σ d, ContDiffOn ℝ ∞ (fun q : V d × ℂ => Ψ (c.e.symm q.1) ‖q.2‖)
    (c.e.target ×ˢ {w | 0 < ‖w‖ ∧ ‖w‖ < δ})
  mono : ∀ y, MonotoneOn (fun t => Ψ y t + K * t ^ 2) (Ioo 0 δ)
  hess : ∀ c : AlgChart p σ d, ∀ y ∈ c.e.source, ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ < δ → ∀ (ξ : V d) (η : ℂ),
    -(A * (‖w‖ * deriv (fun t => Ψ y t + K * t ^ 2) ‖w‖) * a c y ξ.ofLp) -
        K * (‖w‖ ^ 2 * a c y ξ.ofLp + √(a c y ξ.ofLp) * ‖η‖ + ‖η‖ ^ 2) ≤
      θ c y ξ.ofLp + (leviForm (fun q : V d × ℂ => Ψ (c.e.symm q.1) ‖q.2‖) (c.e y, w) (ξ, η) (ξ, η)).re / Real.pi

variable {a : ChartForm p σ d} {E : ChartMap p σ d} {R : AnRead p σ d}

variable [SmoothOfRelativeDimension d p]

def rho (a : ChartForm p σ d) (E : ChartMap p σ d) (ψ : CxPts p σ → ℝ) (y : CxPts p σ) (t : ℝ) : ℝ :=
  rhoIn a E ψ (AlgChart.exists_mem_source (D := d) y).choose y t



end Manifold

end GlobalTheory.ChernReg
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalCompactificationData
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet
open scoped ComplexOrder

namespace GlobalTheory.ShFam

attribute [local instance] Over.cartesianMonoidalCategory

section Domain

open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up Formalism.DegreeFormula Formalism.MJ GlobalTheory.HodgeDomain GlobalTheory.TrueCx

section Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {j : ℕ} (hj : j ≤ r)

def coW (f : Frame X.Ψ r) (τ : X.Ψ) : Matrix (Fin j) (Fin j) ℂ :=
  (frameCo X hj f τ).toBlocks₁₁ - moeb (frameCo X hj f τ) 0 * (frameCo X hj f τ).toBlocks₂₁

def coOm (f : Frame X.Ψ r) (τ : X.Ψ) : Matrix (Fin (r - j)) (Fin (r - j)) ℂ := (frameCo X hj f τ).toBlocks₂₂

theorem frameCo_eq (hp : X.p0 = r - j) {f : Frame X.Ψ r} (hf : f ∈ X.dom) (τ : X.Ψ) :
    frameCo X hj f τ = fromBlocks 1 (moeb (frameCo X hj f τ) 0) 0 1 *
      fromBlocks (coW X hj f τ) 0 (frameCo X hj f τ).toBlocks₂₁ (coOm X hj f τ) := by
  rw [fromBlocks_multiply, coW, coOm]
  conv_lhs => rw [← fromBlocks_toBlocks (frameCo X hj f τ)]
  simp [moeb_zero, nonsing_inv_mul_cancel_right _ _ (frameCo_isUnit₂₂ X hj hp hf τ)]

theorem isUnit_coOm (hp : X.p0 = r - j) {f : Frame X.Ψ r} (hf : f ∈ X.dom) (τ : X.Ψ) : IsUnit (coOm X hj f τ).det :=
  frameCo_isUnit₂₂ X hj hp hf τ

theorem isUnit_coW (hp : X.p0 = r - j) {f : Frame X.Ψ r} (hf : f ∈ X.dom) (τ : X.Ψ) : IsUnit (coW X hj f τ).det := by
  have h : IsUnit (frameCo X hj f τ).det := by
    rw [frameCo, det_reindex_self, det_mul]
    exact (isUnit_nonsing_inv_det _ (det_x0F X τ).isUnit).mul (hf τ).1.isUnit
  rw [frameCo_eq X hj hp hf, det_mul, det_fromBlocks_zero₁₂] at h
  exact isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_right h)

theorem hodge_co (hp : X.p0 = r - j) {f : Frame X.Ψ r} (hf : IsOrth X f) (τ : X.Ψ) :
    (coW X hj f τ)ᴴ * (hP (moeb (frameCo X hj f τ) 0))⁻¹ * coW X hj f τ = 1 ∧
      (coOm X hj f τ)ᴴ * hQ (moeb (frameCo X hj f τ) 0) * coOm X hj f τ = 1 := by
  obtain ⟨g, hg, e⟩ := exists_upq_of_orth X hj hp hf τ
  have h1 := hP_inv_moeb hg (zero_mem_hcDom _ _)
  have h2 := hQ_moeb hg (zero_mem_hcDom _ _)
  rw [jW, e] at h1
  rw [kapQ, e, Matrix.mul_zero, zero_add] at h2
  exact ⟨h1.trans (by simp [hP]), h2.trans (by simp [hQ])⟩

end Frames

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A}

instance FinalTheorems.smooth (s : FinalTheorems S κ) : SmoothOfRelativeDimension S.Dw.dim (genStr s.T.Z) := s.T.smooth

abbrev ToroidalCompactificationData (s : FinalTheorems S κ) : Type := OddPrimesWithRootsOfUnity s.T.Z

theorem Sig.mult_psi (S : Sig A N j) (L : CmList A) (t : D.what₂.Tau) : S.Dw.mult (L.ψ t).1 = j :=
  (if_pos (L.ψ t).2).trans S.p_eq

theorem Sig.mult_conj (S : Sig A N j) (L : CmList A) (t : D.what₂.Tau) : S.Dw.mult (conjEmb (L.ψ t).1) = N - j :=
  (if_neg (GlobalTheory.AllWt.conj_not_mem (L.ψ t))).trans (by have := S.p_eq; have := S.rank_eq; omega)

namespace FinalTheorems

variable (s : FinalTheorems S κ) (L : CmList A) (k : s.Comp)

abbrev fd : Data D.host.E N := (s.U κ.σ₀).X k


include s in
theorem j_le : j ≤ N := le_of_isUnf _ s.isUnf S.p_eq

abbrev lab : D.what₂.Tau ≃ (s.fd k).Ψ := cmEquiv _ s.isUnf L.ψ k

abbrev zOf (f : (s.fd k).dom) : Pt D.what₂.Tau j (N - j) := domPt (s.fd k) s.j_le (s.lab L k) f.1

def framePt (f : (s.fd k).dom) : CxPts (genStr s.T.Z) κ.σ₀ := cxPt s.T.Z ((s.U κ.σ₀).un k f)

def lieFrame (f : (s.fd k).dom) : EigFrame s.T.Z κ.σ₀ ((s.framePt k f).1 ≫ genι s.T.Z) :=
  cxFrame s.T.Z ((s.U κ.σ₀).un k f)


open Classical in
def frameOver (z : Pt D.what₂.Tau j (N - j)) : (s.fd k).dom :=
  if h : ∃ f, s.zOf L k f = z then h.choose else ⟨x0F _, IW.orth_mem_dom _ _ (isOrth_x0F _)⟩

def toCpt (z : Pt D.what₂.Tau j (N - j)) : CxPts (genStr s.T.Z) κ.σ₀ := s.framePt k (s.frameOver L k z)

end FinalTheorems

variable {s : FinalTheorems S κ} (x : ToroidalCompactificationData s) (L : CmList A)

def ToroidalCompactificationData.gramW (k : s.Comp) (f : (s.fd k).dom) (t : D.what₂.Tau) : Matrix (Fin j) (Fin j) ℂ :=
  (x.gram (s.framePt k f) (s.lieFrame k f) (L.ψ t).1).submatrix
    (Fin.cast (S.mult_psi L t).symm) (Fin.cast (S.mult_psi L t).symm)

def ToroidalCompactificationData.gramOm (k : s.Comp) (f : (s.fd k).dom) (t : D.what₂.Tau) : Matrix (Fin (N - j)) (Fin (N - j)) ℂ :=
  ((hodgeC (s.fd k) (s.lab L k) t : ℂ) ^ 2) •
    (dualGram (x.gram (s.framePt k f) (s.lieFrame k f) (conjEmb (L.ψ t).1))).submatrix
      (fun a => Fin.cast (S.mult_conj L t).symm a.rev) (fun a => Fin.cast (S.mult_conj L t).symm a.rev)

def ToroidalCompactificationData.metW (k : s.Comp) (z : Pt D.what₂.Tau j (N - j)) (t : D.what₂.Tau) : Matrix (Fin j) (Fin j) ℂ :=
  ((coW (s.fd k) s.j_le (s.frameOver L k z).1 (s.lab L k t))⁻¹)ᴴ * x.gramW L k (s.frameOver L k z) t *
    (coW (s.fd k) s.j_le (s.frameOver L k z).1 (s.lab L k t))⁻¹

def ToroidalCompactificationData.metOm (k : s.Comp) (z : Pt D.what₂.Tau j (N - j)) (t : D.what₂.Tau) : Matrix (Fin (N - j)) (Fin (N - j)) ℂ :=
  ((coOm (s.fd k) s.j_le (s.frameOver L k z).1 (s.lab L k t))⁻¹)ᴴ * x.gramOm L k (s.frameOver L k z) t *
    (coOm (s.fd k) s.j_le (s.frameOver L k z).1 (s.lab L k t))⁻¹

structure IsBdOf (B : s.Bd L) : Prop where
  m_eq : ∀ k, (B k).m = x.m
  nrm : ∀ k i, ∀ z ∈ DomI D.what₂.Tau j (N - j), (B k).nrm i z = x.nrm κ.σ₀ (Fin.cast (m_eq k) i) (s.toCpt L k z)
  kae : ∀ k W φ, IsPotential (manifold s.T.Z κ.σ₀) (x.kae κ.σ₀) W φ → ∀ z ∈ DomI D.what₂.Tau j (N - j),
    s.toCpt L k z ∈ W → ∀ ξ, ((B k).kae z ξ ξ).re = ddc (φ ∘ s.toCpt L k) z ξ
  cst : ∀ k, (B k).cst = x.cst
  metW : ∀ k f t, (coW (s.fd k) s.j_le f.1 (s.lab L k t))ᴴ * (B k).metW (s.zOf L k f) t *
    coW (s.fd k) s.j_le f.1 (s.lab L k t) = x.gramW L k f t
  metOm : ∀ k f t, (coOm (s.fd k) s.j_le f.1 (s.lab L k t))ᴴ * (B k).metOm (s.zOf L k f) t *
    coOm (s.fd k) s.j_le f.1 (s.lab L k t) = x.gramOm L k f t

namespace IsBdOf

variable {x L} {B B' : s.Bd L} (h : IsBdOf x L B) (k : s.Comp) {z : Pt D.what₂.Tau j (N - j)}
include h

end IsBdOf

end Domain

end GlobalTheory.ShFam
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoordAtConstMulIff
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.Cartier
open GlobalTheory.ShFam.Descent GlobalTheory.FlatLine

namespace GlobalTheory.ShFam.Pad

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

section Frame

variable (Z : Model Xo c β) {R : Type} [CommRing R] [Algebra c.F R] (P : FrPt Xo c R)

def frameOf : EigFrame Z (algebraMap c.F R) (GlobalTheory.AllWt.ptF P ≫ Z.j) := (exists_tie_frame P rfl).choose

variable {Z P}

end Frame

variable {Z : Model Xo c β} {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e)

def CoordAt {k : Type} [Field k] [Algebra c.F k] (P : FrPt Xo c k) (n : Letter Dw → ℤ) (σ : Y.Y.Fn) (a : k) : Prop :=
  ∃ p : Sp k ⟶ Y.Y.X, p ≫ Y.π = GlobalTheory.AllWt.ptF P ≫ Z.jQ ∧ IsCoord Y p (frameOf Z P) n σ a

def CoordAtC {ι : c.F →+* ℂ} (P : FrPt Xo c (CAt ι)) (n : Letter Dw → ℤ) (σ : Y.Y.Fn) (a : ℂ) : Prop :=
  letI := ι.toAlgebra; CoordAt (k := ℂ) Y P n σ a

variable {Y}

variable {r : ℕ}

end Free

end GlobalTheory.ShFam.Pad
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ImaginaryRootNeZero
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.TrueGeo GlobalTheory.Cartier

namespace GlobalTheory.ShFam.Pad.LineTest

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)


variable {Dw} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e)

variable {D : D7} {A : Amb D}

end GlobalTheory.ShFam.Pad.LineTest
end
end
