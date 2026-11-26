module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RealDatumPrerequisitesUpdateModels
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsAtAndSeedFacts
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MaxSimplicialCellMultiplicityLtTopOfIsPolyFan
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverSplit

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DofOTw
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

noncomputable section

namespace GlobalTheory.HeightCounting.Up

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def nTw {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (N : TwNew (Dof x)) :
    NStage B w.C (P.q.W x.o.η x.o.hη) :=
  { x.o.N with ntw := N.tw, nexp := N.ex, nStage_trivialCharacter_coeff_eq := N.h0, nth := N.th, ntwbr := N.br, ntwbr_ind := N.hbr }

def oTw {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (N : TwNew (Dof x)) : P.q.Over := ⟨x.o.η, x.o.hη, x.o.V, x.o.S, nTw x N, x.o.G⟩

theorem dof_oTw {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (N : TwNew (Dof x)) : (w.st (oTw x N).Z).toD7 = N.toD7 := rfl

end GlobalTheory.HeightCounting.Up

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GridStaircaseLatticeFirstColumnTransportStages
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open GlobalTheory.Mem.R3.Tr Formalism.BasicNotions.TH

set_option maxHeartbeats 4000000
noncomputable section
namespace GlobalTheory.Mem.GridMove
open GlobalTheory.ChiGrid
variable {B : Base} {C : Cols B} {a : Late B C} (b : Late B C) {T : Type}

def plC {L : Formalism.IndefR.Links.LevCh a.D T} (P : Places L) : Places (levCh b L) where
  v0 := (by with_unfolding_all exact (P.v0 :))
  basePlace_over_qZero := (by with_unfolding_all exact (P.basePlace_over_qZero :))
  w := (by with_unfolding_all exact (P.w :))
  w_over := (by with_unfolding_all exact (P.w_over :))
  w_split := (by with_unfolding_all exact (P.w_split :))
  w_g := (by with_unfolding_all exact (P.w_g :))
  w_de := (by with_unfolding_all exact (P.w_de :))
  w_Q := (by with_unfolding_all exact (P.w_Q :))
  levelPlace_ne_basePlace := (by with_unfolding_all exact (P.levelPlace_ne_basePlace :))

def chC {L : Formalism.IndefR.Links.LevCh a.D T} {P : Places L} {c : ℝ} (X : Chars P c) : Chars (plC b P) c where
  chiH := (by with_unfolding_all exact (X.chiH :))
  chi := (by with_unfolding_all exact (X.chi :))
  chi_eq := (by with_unfolding_all exact (X.chi_eq :))
  triv := (by with_unfolding_all exact (X.triv :))
  inf := (by with_unfolding_all exact (X.inf :))
  unr := (by with_unfolding_all exact (X.unr :))
  lev1 := (by with_unfolding_all exact (X.lev1 :))
  wild := (by with_unfolding_all exact (X.wild :))
  lev0 := (by with_unfolding_all exact (X.lev0 :))

def lsC (X : LSp a.D) : LSp b.D := ⟨(by with_unfolding_all exact (X.sp :)), (by with_unfolding_all exact (X.lat :))⟩

theorem isVC {X : LSp a.D} {ν q : ℕ} (h : X.IsV ν q) : (lsC b X).IsV ν q :=
  ⟨(by with_unfolding_all exact (h.rank :)), (by with_unfolding_all exact (h.sigOK :)), (by with_unfolding_all exact (h.sig :)), (by with_unfolding_all exact (h.sd :))⟩

def adC {A B' : HSp a.D} {c : ℕ} {ε : a.D.host.E} (d : HermitianOrthogonalExtensionData A B' c ε) :
    @HermitianOrthogonalExtensionData b.D ((A)) ((B')) c ((ε)) where
  ι := (by with_unfolding_all exact (d.ι :))
  isom := (by with_unfolding_all exact (d.isom :))
  a := (by with_unfolding_all exact (d.a :))
  gram := (by with_unfolding_all exact (d.gram :))
  perp := (by with_unfolding_all exact (d.perp :))
  rank := (by with_unfolding_all exact (d.rank :))

section V
open scoped nonZeroDivisors
variable {L : Formalism.IndefR.Links.LevCh a.D T} (Vs : ℕ → ℕ → LSp a.D) (Xs : ℕ → LSp a.D)

def gridColumnVertexDecompTransport (P : ℕ → LSp a.D) : ∀ (i : ℕ) (_ : 1 ≤ i) (_ : HermitianOrthogonalExtensionData (P i).sp (vtxOf L Vs i 0).sp (i - 1) (-1)),
    HermitianOrthogonalExtensionData (lsC b (P i)).sp (vtxOf (levCh b L) (fun i j => lsC b (Vs i j)) i 0).sp (i - 1) (-1)
  | 0, h, _ => absurd h (by omega)
  | _ + 1, _, d => (adC b d :)

theorem gridStaircaseLattice_firstColumn_transportStages (P : ℕ → LSp a.D) : ∀ (i : ℕ) (h : 1 ≤ i) (d : HermitianOrthogonalExtensionData (P i).sp (vtxOf L Vs i 0).sp (i - 1) (-1))
    (𝔟 : Fin (i - 1) → FractionalIdeal (𝓞 a.D.host.E)⁰ a.D.host.E),
    (vtxOf L Vs i 0).lat = d.lat (P i).lat 𝔟 →
    (vtxOf (levCh b L) (fun i j => lsC b (Vs i j)) i 0).lat = (gridColumnVertexDecompTransport b Vs P i h d).lat (lsC b (P i)).lat ((𝔟))
  | 0, h, _, _, _ => absurd h (by omega)
  | _ + 1, _, _, _, e => (e)

def gridInteriorVertexDecompTransport (j : ℕ) : ∀ (n : ℕ) (_ : j + 1 < n) (_ : HermitianOrthogonalExtensionData (Xs (j + 1)).sp (vtxOf L Vs n (j + 1)).sp (n - 1 - (j + 1)) (-1)),
    HermitianOrthogonalExtensionData (lsC b (Xs (j + 1))).sp (vtxOf (levCh b L) (fun i j => lsC b (Vs i j)) n (j + 1)).sp (n - 1 - (j + 1)) (-1)
  | 0, h, _ => absurd h (by omega)
  | _ + 1, _, d => (adC b d :)

theorem gridLastRowVertexLattice_transportStages (j : ℕ) : ∀ (n : ℕ) (h : j + 1 < n) (d : HermitianOrthogonalExtensionData (Xs (j + 1)).sp (vtxOf L Vs n (j + 1)).sp (n - 1 - (j + 1)) (-1))
    (𝔟 : Fin (n - 1 - (j + 1)) → FractionalIdeal (𝓞 a.D.host.E)⁰ a.D.host.E),
    (vtxOf L Vs n (j + 1)).lat = d.lat (Xs (j + 1)).lat 𝔟 →
    (vtxOf (levCh b L) (fun i j => lsC b (Vs i j)) n (j + 1)).lat = (gridInteriorVertexDecompTransport b Vs Xs j n h d).lat (lsC b (Xs (j + 1))).lat ((𝔟))
  | 0, h, _, _, _ => absurd h (by omega)
  | _ + 1, _, _, _, e => (e)

def gridDiagonalVertexDecompTransport (X0 : LSp a.D) : ∀ (n : ℕ) (_ : 1 ≤ n) (_ : HermitianOrthogonalExtensionData (vtxOf L Vs n n).sp (xOf X0 Xs n).sp 1 1),
    HermitianOrthogonalExtensionData (vtxOf (levCh b L) (fun i j => lsC b (Vs i j)) n n).sp (xOf (lsC b X0) (fun j => lsC b (Xs j)) n).sp 1 1
  | 0, h, _ => absurd h (by omega)
  | _ + 1, _, d => (adC b d :)

theorem gridTopVertexLattice_transportStages (X0 : LSp a.D) : ∀ (n : ℕ) (h : 1 ≤ n) (d : HermitianOrthogonalExtensionData (vtxOf L Vs n n).sp (xOf X0 Xs n).sp 1 1),
    (xOf X0 Xs n).lat = d.lat (vtxOf L Vs n n).lat (fun _ => 1) →
    (xOf (lsC b X0) (fun j => lsC b (Xs j)) n).lat = (gridDiagonalVertexDecompTransport b Vs Xs X0 n h d).lat (vtxOf (levCh b L) (fun i j => lsC b (Vs i j)) n n).lat (fun _ => 1)
  | 0, h, _, _ => absurd h (by omega)
  | _ + 1, _, _, e => (e)

end V

section W
open scoped nonZeroDivisors
variable {L : Formalism.IndefR.Links.LevCh a.D T}

def vtC {𝔞 𝔞' : FractionalIdeal (𝓞 a.D.host.E)⁰ a.D.host.E} (V : Vertices L 𝔞 𝔞') :
    Vertices (levCh b L) ((𝔞)) ((𝔞')) where
  Vs i j := lsC b (V.Vs i j)
  P i := lsC b (V.P i)
  Xs j := lsC b (V.Xs j)
  V_is i j h1 h2 h3 := (by with_unfolding_all exact ((isVC b (V.V_is i j h1 h2 h3)) :))
  P_is i h := (by with_unfolding_all exact ((isVC b (V.P_is i h)) :))
  X_is j h1 h2 := (by with_unfolding_all exact ((isVC b (V.X_is j h1 h2)) :))
  dec0 := (by with_unfolding_all exact ((adC b V.dec0) :))
  lat0 := (by with_unfolding_all exact (V.lat0 :))
  colDec i h h' := gridColumnVertexDecompTransport b V.Vs V.P i h (V.colDec i h h')
  colLat i h h' := (by with_unfolding_all exact ((gridStaircaseLattice_firstColumn_transportStages b V.Vs V.P i h (V.colDec i h h') _ (V.colLat i h h')) :))
  rowDecS j h := (by with_unfolding_all exact ((gridInteriorVertexDecompTransport b V.Vs V.Xs j a.D.R.m h (V.rowDecS j h)) :))
  rowLat j h := (by with_unfolding_all exact ((gridLastRowVertexLattice_transportStages b V.Vs V.Xs j a.D.R.m h (V.rowDecS j h) _ (V.rowLat j h)) :))
  topDec := (by with_unfolding_all exact ((gridDiagonalVertexDecompTransport b V.Vs V.Xs (V.P a.D.R.m) a.D.R.m (by have := a.D.R.two_le_m; omega) V.topDec) :))
  topLat := (by with_unfolding_all exact ((gridTopVertexLattice_transportStages b V.Vs V.Xs (V.P a.D.R.m) a.D.R.m (by have := a.D.R.two_le_m; omega) V.topDec V.topLat) :))

def gdC {sc : Consts} (G : GridData L sc) : GridData (levCh b L) sc where
  pl := plC b G.pl
  ch := chC b G.ch
  sp := (by with_unfolding_all exact ((vtC b G.sp) :))

end W

section Y
variable {L : Formalism.IndefR.Links.LevCh a.D T}

theorem listPin_upL (S' : SStage B C a.W) (Nn : ∀ u, Submodule (𝓞 B.LL) (a.V.div.Nu u).V) (hh : B.Word → ℝ) (c bb : ℝ)
    (h : ListPin a.D L c bb) : ListPin (upL a S' Nn hh).D (levCh (upL a S' Nn hh) L) c bb := by
  obtain ⟨G, h1, h2⟩ := h
  exact ⟨gdC _ G, ⟨(by with_unfolding_all exact (h1.values :)), (by with_unfolding_all exact (h1.roots :))⟩, (by with_unfolding_all exact (h2 :))⟩
end Y


set_option maxHeartbeats 4000000 in
theorem listPin_rowsSame : ∀ (cDep b : ℝ) (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) (p0 : BaseLevelRowSide (w.D Z)) (t : RowsT K w Z Wt p0) (p0' : BaseLevelRowSide (w.D (upL Z S' N h))) (t' : RowsT K w (upL Z S' N h) Wt p0'), RowsSame t t' → ListPin (w.st Z).toD7 t.r.z.R.toRealDat.toLevCh cDep b → ListPin (w.st (upL Z S' N h)).toD7 t'.r.z.R.toRealDat.toLevCh cDep b := by
  intro cDep b K B f T w Z Wt S' N h p0 t p0' t' hs hp
  cases t' with | mk hX' r' => ?_
  cases r' with | mk z' => ?_
  cases z' with | @mk Xg' tr' core' alg' alg_eq' R' => ?_
  have hXg := hs.Xg
  have htr := hs.tr
  have hcore := hs.core
  have hR := hs.R
  clear hs
  change Xg' = t.r.z.Xg at hXg
  change tr' = t.r.z.tr at htr
  subst hXg htr
  change HEq core' _ at hcore
  have hc := eq_of_heq hcore
  subst hc
  have ha : alg' = GlobalTheory.Mem.R3.Tr.alg (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩)
      ⟨(upL Z S' N h).W, (upL Z S' N h).V, (upL Z S' N h).S, (upL Z S' N h).N, (upL Z S' N h).G⟩ t.r.z.alg := by
    apply Algebra.algebra_ext
    intro r
    apply (w.st (upL Z S' N h)).B.embLL.injective
    exact (by with_unfolding_all exact (((alg_eq' r).trans (t.r.z.alg_eq r).symm) :))
  subst ha
  change HEq R' _ at hR
  have hR2 := eq_of_heq hR
  subst hR2
  exact (by with_unfolding_all exact ((listPin_upL (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) S' N h cDep b hp) :))

end GlobalTheory.Mem.GridMove

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqCjOneSmul
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open GlobalTheory.Mem.KeepRef

namespace GlobalTheory.Mem.R3.Rw.WeilExt

section Defs

variable {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL]
  {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}

def LevSame (z : Dat (w.st Z) w.I hX T Wt) (Wt' : Set B'.places.Pl)
    (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks) : Prop :=
  (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
    HEq (R'.toLevCh.mu (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))) ((i' : ℕ) + 1)) (z.R.toLevCh.mu (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))) ((i : ℕ) + 1)) ∧
    ∀ PP' PP, HEq PP' PP → PP ∈ z.R.Pg → HEq (R'.chi ((i' : ℕ) + 1) PP') (z.R.chi ((i : ℕ) + 1) PP)) ∧
  HEq R'.eta z.R.eta ∧ R'.Q (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))) = ∅ ∧ z.R.Q (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))) = ∅

def IdemSame (z : Dat (w.st Z) w.I hX T Wt) (Xg : Finset (Gc B' w'.px → B'.LL)) : Prop :=
  ∀ (g' : Gc B' w'.px) (g : Gc B w.px), HEq g' g → B'.embLL ((idemOf Xg).coeff g') = B.embLL ((idemOf z.Xg).coeff g)


set_option maxHeartbeats 1000000 in
def JSpan (z : Dat (w.st Z) w.I hX T Wt) (Wt' : Set B'.places.Pl)
    (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks) : Prop :=
  ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
    ∀ x' : (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr).A.fam.amb.FL i' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))),
      ∃ (n : ℕ) (a : Fin n → (w'.st Z').toD7.what₂.LL)
        (x : Fin n → (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.fam.amb.FL i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))),
        HEq (R'.B.jL i' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))) x') (∑ k, (w'.st Z').toD7.what₂.embLL (a k) • z.R.B.jL i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))) (x k))

end Defs

theorem ratAt_of_geo {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {C : Formalism.L2.Pj.CoreJ D} [Algebra C.Q.c.F D.what₂.LL] (R : RealDat3 D A3 C.Q.c.F)
    (F : Face3 D A3) (hch : R.WeakCharacterisation F) (hEx : R.toRealDat.ExAt) (hn : 8 * D.R.f * D.R.r + 4 ≤ D.R.nV)
    (geo : GlobalTheory.RealGeo.GeoHalf C R.toRealDat fun _ => 1) (hI : GlobalTheory.RealGeo.InGeo geo) (hU : R.toRealDat.LUnif) :
    RatAt R.toRealDat A3.A.μ0 := by
  intro i x v hv
  have hio := GlobalTheory.IoExtremal.ioExt D G Pl0 T0 A3.A _ R.toRealDat hch.base.lev hch.base.fam hch.base.models
    (RealDat.thP_of_weak hch.base.thP hEx)
  have hM := GlobalTheory.OneMapRow3.oneFormMapRow_threeLevel_of_characterisation _ _ _ _ _ _ C R F geo.κ geo.v₀ geo.O (fun _ => 1) hn hch hEx ⟨geo.fw⟩ hio i
    (geo.pins i) (geo.phase i hU)
  have e : v = R.jV i A3.A.μ0 x := (hch.base.models.HV i _).1 (hv.trans (hch.base.models.jV i _ x).symm)
  subst e
  obtain ⟨y, hy⟩ := (Formalism.IndefR.FWT.phase_of_oneMap geo.fw hU
    (hI.evInj i _ (Formalism.IndefR.FWT.base_embedding_good C R.toRealDat geo.fw.alg_eq geo.fw.laws.pins.2.2.1)) (geo.O i) (geo.phase i hU hM.1)).2 x
  exact ⟨y, hy.trans (one_smul ℂ _)⟩

theorem eq_cj_one_smul {H : Type} [AddCommGroup H] [Module ℂ H] (s : Bool) (v : H) : v = Formalism.IndefR.Links.cj s (1 : ℂ) • v := by
  rw [map_one, one_smul]


set_option maxHeartbeats 8000000 in
theorem charW_keep (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι)
    (Xg : Finset (Gc X.B px → X.B.LL)) (tr₀ : TrI X.B px) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks X.toD7.what₂.LL]
    (R₀ : RealDat3 X.toD7 (famR X I hX U Xg tr₀) Ks) (cG : G0 R₀.Pg X.toD7.R.r ≃* G0g X.toD7.nd) (hI : Inputs X.toD7)
    (hXi : IdemClass (D := X.toD7) (famR X I hX U Xg tr₀).A)
    (hEx : ∀ R : RealDat X.toD7 (famR X I hX U Xg tr₀).A Ks, R.Pre1 (face0 X I hX U Xg tr₀).lv2 → R.IsChainW → R.IsThPW → R.ExAt)
    (S : RealDat X.toD7 (famR X I hX U Xg tr₀).A Ks → Prop)
    (hSM : ∀ R HX HV HE gE jX jV νY fdY ν0 fd0 νX fdX νV fdV ωP vP thF thG, S R →
      S (updM R HX HV HE gE jX jV νY fdY ν0 fd0 νX fdX νV fdV ωP vP thF thG))
    (hS3 : ∀ R ωY ωX vac vacX vY vX ItY ItX ioY ioX Th, S R → S (R.upd3 ωY ωX vac vacX vY vX ItY ItX ioY ioX Th))
    (hS6 : ∀ R kap lam, S R → S (R.upd6 kap lam)) (s0 : S R₀.toRealDat)
    (p0 : R₀.toRealDat.Pre0 (face0 X I hX U Xg tr₀).lv2) (i0 : R₀.IsInert) (t0 : R₀.IsTup) (a0 : R₀.AllPlaces)
    (k0 : Keep R₀.toRealDat (face0 X I hX U Xg tr₀).lv2 cG) (b0 : BrgStd X I hX U Xg tr₀ R₀.toRealDat) (x0 : R₀.toRealDat.grp_chiW)
    (hW : ModW R₀.toRealDat) (hω : WeilAt R₀.toRealDat (famR X I hX U Xg tr₀).A.μ0) (hV : ModVAt R₀.toRealDat (famR X I hX U Xg tr₀).A.μ0)
    (hl : LiftAt R₀.toRealDat (famR X I hX U Xg tr₀).A.μ0) (hr : RatAt R₀.toRealDat (famR X I hX U Xg tr₀).A.μ0) :
    ∃ (tr : TrI X.B px) (R : RealDat3 X.toD7 (famR X I hX U Xg tr) Ks) (cG' : G0 R.Pg X.toD7.R.r ≃* G0g X.toD7.nd),
      Pins R (face0 X I hX U Xg tr) cG' ∧ R.toRealDat.ExAt ∧ R.toRealDat.toLevCh = R₀.toRealDat.toLevCh ∧ HEq R.eG R₀.eG ∧ HEq cG' cG ∧
      R.mu = R₀.mu ∧ R.twPl = R₀.twPl ∧ BrgStd X I hX U Xg tr R.toRealDat ∧ S R.toRealDat ∧
      SameAt (A := (famR X I hX U Xg tr₀).A) R₀.toRealDat R.toRealDat (famR X I hX U Xg tr₀).A.μ0 := by
  classical
  obtain ⟨hL, hF⟩ := GlobalTheory.HeckeCharacterRestriction.liftsAt_and_seedFacts X.toD7 _ _ _ (famR X I hX U Xg tr₀).A Ks (face0 X I hX U Xg tr₀).lv2
  obtain ⟨R1, p1, c1, t1, f1, g1, ⟨q1, s1⟩, m1, hrat⟩ := exists_weak_keep hI hXi hL hF
    (fun R => (RealDat3.IsInert (⟨R, R₀.plI, R₀.SF, R₀.phs, R₀.lam3⟩ : RealDat3 X.toD7 (famR X I hX U Xg tr₀) Ks) ∧
      RealDat3.IsTup (⟨R, R₀.plI, R₀.SF, R₀.phs, R₀.lam3⟩ : RealDat3 X.toD7 (famR X I hX U Xg tr₀) Ks) ∧
      RealDat3.AllPlaces (⟨R, R₀.plI, R₀.SF, R₀.phs, R₀.lam3⟩ : RealDat3 X.toD7 (famR X I hX U Xg tr₀) Ks) ∧
      R.toLevCh = R₀.toLevCh ∧ HEq R.eG R₀.eG ∧ R.mu = R₀.mu ∧ R.twPl = R₀.twPl ∧
      BrgStd X I hX U Xg tr₀ R ∧ R.grp_chiW ∧
      ∀ c : G0 R.Pg X.toD7.R.r ≃* G0g X.toD7.nd, HEq c cG → Keep (A3 := (famR X I hX U Xg tr₀)) R (face0 X I hX U Xg tr₀).lv2 c) ∧ S R)
    (fun R a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 ⟨h, s⟩ => ⟨by
      obtain ⟨hi, ht, ha, hl, he, hm, hw, hb, hg, hk⟩ := h
      exact ⟨⟨hi.tie, hi.onto, hi.hR, hi.hL, hi.SF⟩, ⟨ht.mu_off, ht.mu_used, ht.mu_ne, ht.mu_conj, ht.mu_on⟩, ha, hl, he, hm, hw, hb, hg, fun c hc => by
        have k := hk c hc
        exact ⟨k.std, k.signs, k.frames, k.beta, k.prX, k.grp, k.psi, k.guard, k.valKs, k.frameKs, k.levKs⟩⟩, hSM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s⟩)
    (fun R a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 ⟨h, s⟩ => ⟨by
      obtain ⟨hi, ht, ha, hl, he, hm, hw, hb, hg, hk⟩ := h
      exact ⟨⟨hi.tie, hi.onto, hi.hR, hi.hL, hi.SF⟩, ⟨ht.mu_off, ht.mu_used, ht.mu_ne, ht.mu_conj, ht.mu_on⟩, ha, hl, he, hm, hw, hb, hg, fun c hc => by
        have k := hk c hc
        exact ⟨k.std, k.signs, k.frames, k.beta, k.prX, k.grp, k.psi, k.guard, k.valKs, k.frameKs, k.levKs⟩⟩, hS3 _ _ _ _ _ _ _ _ _ _ _ _ s⟩)
    R₀.toRealDat p0 ⟨⟨⟨i0.tie, i0.onto, i0.hR, i0.hL, i0.SF⟩, ⟨t0.mu_off, t0.mu_used, t0.mu_ne, t0.mu_conj, t0.mu_on⟩, a0, rfl, HEq.rfl,
      rfl, rfl, b0, x0, fun c hc => by cases eq_of_heq hc; exact k0⟩, s0⟩ hW hω hV hl hr
  obtain ⟨i1, u1, a1, l1, e1, mu1, w1, b1, x1, k1⟩ := q1
  have hc : ∃ c : G0 R1.Pg X.toD7.R.r ≃* G0g X.toD7.nd, HEq c cG := by
    rw [show R1.Pg = R₀.Pg from congrArg (fun L => L.Pg) l1]
    exact ⟨cG, HEq.rfl⟩
  obtain ⟨cutoffDeriv, hcG1⟩ := hc
  let R2₀ : RealDat3 X.toD7 (famR X I hX U Xg tr₀) Ks := ⟨R1, R₀.plI, R₀.SF, fun _ => 1, R₀.lam3⟩
  have htr : ∃ tr : TrI X.B px, (∃ t', R2₀.TrISem (face0 X I hX U Xg tr₀) t' ∧ SepWith (famR X I hX U Xg tr₀) t') →
      R2₀.TrISem (face0 X I hX U Xg tr₀) tr ∧ SepWith (famR X I hX U Xg tr₀) tr := by
    by_cases h : ∃ t', R2₀.TrISem (face0 X I hX U Xg tr₀) t' ∧ SepWith (famR X I hX U Xg tr₀) t'
    · obtain ⟨t', h'⟩ := h
      exact ⟨t', fun _ => h'⟩
    · exact ⟨tr₀, fun h' => absurd h' h⟩
  obtain ⟨tr, htr⟩ := htr
  let R2 : RealDat3 X.toD7 (famR X I hX U Xg tr) Ks := ⟨R1, R₀.plI, R₀.SF, fun _ => 1, R₀.lam3⟩
  obtain ⟨kap, lam, hs⟩ := scalars_exist (F := face0 X I hX U Xg tr) R2
  have p6 := RealDat.preliminary_of_scalar_update p1 kap R2.lam
  have f6 := RealDat.full_Y_of_scalar_update f1 kap R2.lam
  have c6 := RealDat.weak_chain_of_scalar_update c1 kap R2.lam
  have t6 := RealDat.weak_theta_props_of_scalar_update t1 kap R2.lam
  have g6 := RealDat.full_P_of_scalar_update g1 kap R2.lam
  have hphs : (R2.updS kap lam).phase := by
    intro i
    refine ⟨show ‖(1 : ℂ)‖ = 1 from norm_one, fun _ x => ?_⟩
    obtain ⟨y, hy⟩ := hrat i x
    refine ⟨y, ?_⟩
    exact (by with_unfolding_all exact (hy.trans (eq_cj_one_smul (twAt X.toD7.what₂.embLL (famR X I hX U Xg tr₀).A.v0) _) :))
  have kv := k1 cutoffDeriv hcG1
  exact ⟨tr, R2.updS kap lam, cutoffDeriv, ⟨⟨⟨p6.1.lev, ⟨p6.1.red_R, p6.1.red_L, p6.1.levels, p6.1.record, x1⟩,
      p6.1.fam, p6.2, c6, t6⟩, ⟨⟨i1.tie.plI_inj, i1.tie.okI⟩, i1.onto, i1.hR, i1.hL, i1.SF⟩, f6.1, f6.2, g6, hs,
      ⟨u1.mu_off, u1.mu_used, u1.mu_ne, u1.mu_conj, u1.mu_on⟩, hphs, a1⟩,
    ⟨kv.std, kv.signs, kv.frames, kv.beta, kv.prX, kv.grp, kv.psi, kv.guard, kv.valKs, kv.frameKs, kv.levKs⟩,
    fun _ => rfl, fun h => htr h⟩, hEx _ p6 c6 t6, l1, e1, hcG1, mu1, w1, b1, hS6 _ kap R2.lam s1, m1⟩

end GlobalTheory.Mem.R3.Rw.WeilExt

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFormLevelPrimesIsSplitSet
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFormLevelPrimesIsSplitSet
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.Mem.R3.LiftBrg

theorem mem_sgL_iff (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (U : Set I.ι)
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (hL : LevOf X I U L) (t : TupU I U) (PP : Pl X.toD7.host.E) :
    PP ∈ sgL X I U t ↔ PP ∈ L.Pg ∨ PP ∈ L.Q t := by
  rw [hL.Pg, hL.Q t, Col2.ColIn.Q, tup_ixOf I t]
  classical
  exact Finset.mem_union

theorem isSplitSet_sgL : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι)
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)), I.Ok → LevOf X I U L →
    ∀ t : TupU I U, Formalism.L2.DIV.IsSplitSet (LiftBrg.sgL X I U t) := by
  intro X px I U L _ hL t PP h PP' h' hc
  have hc' : Formalism.IndefR.Lev.IsConjPl (D := X.toD7) PP PP' := fun c hm =>
    ⟨Formalism.DivisionValues.cO X.toD7.host.E c, (hc c (Formalism.DivisionValues.cO X.toD7.host.E c) rfl).1 hm, rfl⟩
  exact GlobalTheory.HeckeCharacterRestriction.not_isConjPl_union hL.is t ((mem_sgL_iff X I U L hL t PP).1 h)
    ((mem_sgL_iff X I U L hL t PP').1 h') hc'

end GlobalTheory.Mem.R3.LiftBrg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFormLevelPrimesIsSplitSetStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowFormLevelPrimes_isSplitSet : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι)
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)), I.Ok → LevOf X I U L →
    ∀ t : TupU I U, Formalism.L2.DIV.IsSplitSet (LiftBrg.sgL X I U t) := by
  first | exact @GlobalTheory.Mem.R3.LiftBrg.isSplitSet_sgL | exact GlobalTheory.Mem.R3.LiftBrg.isSplitSet_sgL | (intros; apply GlobalTheory.Mem.R3.LiftBrg.isSplitSet_sgL <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInvariantSmoothRefinementPolyFan
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInvariantSmoothRefinementPolyFan
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.PolFan

theorem resolution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (φ lab : InvFun (𝓞 E)), (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) → IsPolyFan H.bar q φ → IsTwInv H φ → IsTwInv H lab → SimpLab H.bar q φ lab → ∃ φ' : InvFun (𝓞 E), IsPolFan H.bar q φ' ∧ NoSelfInt H.bar q φ' ∧ IsTwInv H φ' ∧ Subordinate H.bar q φ' φ := by
  intro E _ _ _ H q φ lab hD hP hT hL hS
  suffices key : ∀ n : ℕ, ∀ φ lab : InvFun (𝓞 E), maxMult H.bar q φ = n → IsPolyFan H.bar q φ → IsTwInv H φ →
      IsTwInv H lab → SimpLab H.bar q φ lab → ∃ φ' : InvFun (𝓞 E), IsPolFan H.bar q φ' ∧ NoSelfInt H.bar q φ' ∧
        IsTwInv H φ' ∧ Subordinate H.bar q φ' φ by
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (GlobalTheory.T.maxSimplicialCellMultiplicity_lt_top_of_isPolyFan E H q φ hP).ne
    exact key n φ lab hn.symm hP hT hL hS
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro φ lab hn hP hT hL hS
    by_cases h2 : 2 ≤ maxMult H.bar q φ
    · obtain ⟨φ', lab', hP', hT', hL', hS', hsub, hlt⟩ :=
        GlobalTheory.T.exists_starSubdivision_lowers_maxCellMultiplicity E H q φ lab hD hP hT hL hS (hn ▸ ENat.coe_lt_top n) h2
      obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 (hlt.trans_le le_top).ne
      have hkn : k < n := by
        rw [← hk, hn] at hlt; exact_mod_cast hlt
      obtain ⟨φ'', h1, h2, h3, h4⟩ := ih k hkn φ' lab' hk.symm hP' hT' hL' hS'
      exact ⟨φ'', h1, h2, h3, h4.trans hsub⟩
    · have hle : maxMult H.bar q φ ≤ 1 := by
        rw [hn] at h2 ⊢
        have : ¬ 2 ≤ n := fun h => h2 (by exact_mod_cast h)
        exact_mod_cast (show n ≤ 1 by omega)
      obtain ⟨h1, h2⟩ := GlobalTheory.T.isSmoothAdmissibleFan_of_cellMult_one_CMField E H q φ lab hD hP hS hle
      exact ⟨φ, h1, h2, hT, Subordinate.refl φ⟩

end GlobalTheory.PolFan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInvariantSmoothRefinementPolyFanStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_invariant_smooth_refinement_polyFan : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (φ lab : InvFun (𝓞 E)), (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) → IsPolyFan H.bar q φ → IsTwInv H φ → IsTwInv H lab → SimpLab H.bar q φ lab → ∃ φ' : InvFun (𝓞 E), IsPolFan H.bar q φ' ∧ NoSelfInt H.bar q φ' ∧ IsTwInv H φ' ∧ Subordinate H.bar q φ' φ := by
  first | exact @GlobalTheory.PolFan.resolution | exact GlobalTheory.PolFan.resolution | (intros; apply GlobalTheory.PolFan.resolution <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CentralFrameSplitNontrivialAt
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev

noncomputable section

namespace GlobalTheory.FrameTypes

open ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.CenFrame


def IsBlockUpperUnipotentMatrix {k : Type} [CommRing k] {n : ℕ} (r : ℕ) (x : GL (Fin n) k) : Prop :=
  ∀ i j : Fin n, (r ≤ i.val → j.val < r → x.val i j = 0) ∧ (i.val < r → j.val < i.val → x.val i j = 0) ∧
    (i.val < r → i = j → x.val i j = 1)

theorem blkUni_one {k : Type} [CommRing k] {n : ℕ} (r : ℕ) : IsBlockUpperUnipotentMatrix r (1 : GL (Fin n) k) := by
  intro i j
  refine ⟨fun h1 h2 => ?_, fun _ h2 => ?_, fun _ h2 => ?_⟩
  · rw [Units.val_one, Matrix.one_apply_ne]; rintro rfl; omega
  · rw [Units.val_one, Matrix.one_apply_ne]; rintro rfl; omega
  · rw [Units.val_one, h2, Matrix.one_apply_eq]

theorem IsBlockUpperUnipotentMatrix.blk2 {k : Type} [CommRing k] {n r : ℕ} {x : GL (Fin n) k} (h : IsBlockUpperUnipotentMatrix r x) : x ∈ blockTri (blk2 r) := by
  refine mem_blockTri.2 fun i j hij => ?_
  unfold Formalism.L2.DIV.blk2 at hij
  refine (h i j).1 ?_ ?_ <;> split_ifs at hij <;> omega

theorem IsBlockUpperUnipotentMatrix.blkOf {k : Type} [CommRing k] {n r t : ℕ} (hn : n ≤ r + t) {x : GL (Fin n) k} (h : IsBlockUpperUnipotentMatrix r x) :
    x ∈ blockTri (blkOf r t) := by
  refine mem_blockTri.2 fun i j hij => ?_
  unfold Formalism.L2.DIV.blkOf at hij
  have hi := i.2
  by_cases h1 : i.val < r
  · rw [if_pos h1] at hij; omega
  · rw [if_neg h1, Nat.div_eq_of_lt (show i.val - r < t by omega)] at hij
    refine (h i j).1 (by omega) ?_
    by_contra h2
    rw [if_neg h2] at hij
    exact absurd hij (not_lt.2 (Nat.succ_le_succ (Nat.zero_le _)))

theorem IsBlockUpperUnipotentMatrix.unip {k : Type} [CommRing k] {n r : ℕ} (hr : r ≤ n) {x : GL (Fin n) k} (h : IsBlockUpperUnipotentMatrix r x) :
    upperLeftBlock hr x ∈ unip k r := by
  refine ⟨mem_blockTri.2 fun i j hij => ?_, fun i => ?_⟩
  · rw [upper_block_val_submatrix hr h.blk2]
    exact (h _ _).2.1 i.2 hij
  · rw [upper_block_val_submatrix hr h.blk2]
    exact (h _ _).2.2 i.2 rfl

variable {D : D7}

theorem isConjPl_of_under (s : SplitPlace D.host.E) {PP : PlE D.host} (hne : PP ≠ s.w)
    (h : HeightOneSpectrum.under (𝓞 (maximalRealSubfield D.host.E)) PP = s.v) : Formalism.IndefR.Lev.IsConjPl (D := D) PP s.w := by
  rcases Formalism.L2.eq_or_eq_conjPlE s.w PP ((congrArg HeightOneSpectrum.asIdeal h).trans s.w_under.symm) with e | e
  · exact absurd e hne
  · intro c hc
    rw [e, Formalism.L2.mem_conjPlE] at hc
    refine ⟨_, hc, ?_⟩
    rw [IsCMField.coe_ringOfIntegersComplexConj, GlobalTheory.TypePlaces.star_eq_conj, GlobalTheory.SplitPlaceOver.host_conj_eq']

theorem mem_level {V : TH.HSp D} {n : ℕ} (hn : V.rank = n) {hF : D.host.F = maximalRealSubfield D.host.E}
    {P : Formalism.IndefR.principalLevelFrame.RowPsi V n} (hP : StdFrame hF P) {β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hB : Formalism.IndefR.Lev.IsBaseFrame V β Λ 1)
    (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) (hrt : V.rank ≤ L.r + L.t)
    (hH : ∀ g : G0 L.Pg L.r, (∀ PP, g PP ∈ unip (kP PP.1) L.r) → g ∈ L.P.H)
    (s : SplitPlace D.host.E) (hsep : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → ¬ Formalism.IndefR.Lev.IsConjPl (D := D) PP s.w)
    {φ : Os s →+* kP s.w} {b : GL (Fin n) (kP s.w)} (hfr : FrameRed hn P β s φ b)
    {κ : GAf D.host.E n} (hU : κ ∈ Umax D.host.E n) (hT : TrivOutside {s.v} κ) {y : GL (Fin n) (Os s)} (hy : IsCompOf s κ y) :
    (IsBlockUpperUnipotentMatrix L.r (b * Matrix.GeneralLinearGroup.map φ y * b⁻¹) → P.ψ κ ∈ Formalism.IndefR.Links.levS V β L) ∧
    (Matrix.GeneralLinearGroup.map φ y = 1 →
      P.ψ κ ∈ Formalism.IndefR.Links.levS V β L ∧ Formalism.IndefR.Lev.levChi V β L (P.ψ κ) = 1) := by
  have hS := (GlobalTheory.FinZeta.LevelOff.finE_mem_St_iff hB (P.into κ)).2 ((hP.2 κ).1 hU)
  have hred : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ s.w → redFn β PP (Formalism.IndefR.Lev.finE V (P.ψ κ)) = 1 := by
    intro PP hPP hne
    refine GlobalTheory.FinZeta.LevelOff.redFn_eq_one_of_proj β {(_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)} hS (fun u hu => ?_) (Finset.mem_singleton_self _)
    rw [Finset.mem_singleton.1 hu]
    exact GlobalTheory.NonSplitLevel.projV_eq_one hP κ PP (hT _ fun e => hsep PP hPP (isConjPl_of_under s hne e))
  have hent : ∀ i j : Fin V.rank, (redFn β s.w (Formalism.IndefR.Lev.finE V (P.ψ κ))).val i j =
      (b * Matrix.GeneralLinearGroup.map φ y * b⁻¹).val (Fin.cast hn i) (Fin.cast hn j) :=
    fun i j => hfr κ hU y hy (Fin.cast hn i) (Fin.cast hn j)
  refine ⟨fun hb => ?_, fun h1 => ?_⟩
  · have hall : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → IsBlockUpperUnipotentMatrix L.r (redFn β PP (Formalism.IndefR.Lev.finE V (P.ψ κ))) := by
      intro PP hPP
      by_cases e : PP = s.w
      · subst e
        intro i j
        rw [hent]
        have hb' := hb (Fin.cast hn i) (Fin.cast hn j)
        exact ⟨hb'.1, hb'.2.1, fun h1 h2 => hb'.2.2 h1 (congrArg _ h2)⟩
      · rw [hred PP hPP e]; exact blkUni_one _
    exact ⟨P.into κ, mem_lev.2 ⟨mem_parLev.2 ⟨GlobalTheory.LevSplit.finE_mem_UA V _, hS, fun PP h => (hall PP (Or.inl h)).blkOf hrt,
      fun PP h => (hall PP (Or.inr h)).blk2⟩, hH _ fun PP => (hall PP.1 (Or.inl PP.2)).unip L.hr⟩⟩
  · have hall : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → redFn β PP (Formalism.IndefR.Lev.finE V (P.ψ κ)) = 1 := by
      intro PP hPP
      by_cases e : PP = s.w
      · subst e
        refine Units.ext (Matrix.ext fun i j => ?_)
        rw [hent, h1, mul_one, mul_inv_cancel, Units.val_one, Units.val_one, Matrix.one_apply, Matrix.one_apply]
        exact if_congr (Fin.cast_injective hn).eq_iff rfl rfl
      · exact hred PP hPP e
    refine ⟨⟨P.into κ, GlobalTheory.LevSplit.mem_lev_of_red _ _ β L _ (GlobalTheory.LevSplit.finE_mem_UA V _) hS hall⟩, ?_⟩
    unfold Formalism.IndefR.Lev.levChi
    rw [GlobalTheory.LevSplit.levFn_eq_one β L _ hall, Units.val_one]

section Read
variable {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : Formalism.IndefR.Links.RealDat3 D A3 Ks}
  {F : Formalism.IndefR.Links.Face3 D A3} {X0 : BaseLevelRowSide D} {Y : Read R.toRealDat F.lv2 X0} {M : MtFam D}


set_option maxHeartbeats 1000000 in
theorem exists_fn (ad : MtAd Y M) (μ : D.what₂.Tup) (hμ : Formalism.IndefR.RecTie.Used0 D μ) (k : Fin D.R.m)
    (hnt : Nontrivial (D.what₂.Mt μ ((k : ℕ) + 1))) :
    ∃ f : GAf D.host.E D.R.nV → ℂ, f ≠ 0 ∧
      (∀ κ (h : κ ∈ (M μ (k.1 + 1) (by omega) (by omega)).J) g,
        f (g * κ) = (((M μ (k.1 + 1) (by omega) (by omega)).χ ⟨κ, h⟩ : ℂˣ) : ℂ) * f g) ∧
      ∀ κ, (ad.PV k).ψ κ ∈ levS _ (R.toRealDat.βV k)
          (Formalism.IndefR.RecTie.datVP R.toRealDat k (Y.tupT μ) (R.toRealDat.levR F.lv2 false)) →
        ∀ g, f (g * κ) = levChi _ (R.toRealDat.βV k)
          (Formalism.IndefR.RecTie.datVP R.toRealDat k (Y.tupT μ) (R.toRealDat.levR F.lv2 false)) ((ad.PV k).ψ κ) * f g := by
  obtain ⟨x, hx⟩ := exists_ne (0 : D.what₂.Mt μ ((k : ℕ) + 1))
  have hr : (M μ (k.1 + 1) (by omega) (by omega)).real x ≠ 0 := fun e =>
    hx ((M μ (k.1 + 1) _ _).real_inj (e.trans (map_zero _).symm))
  obtain ⟨g₀, hg₀⟩ := Function.ne_iff.1 hr
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_ne_zero ℂ hg₀
  have hm : (M μ (k.1 + 1) (Nat.le_add_left _ _) k.2).real x ∈ NG.TypeSp (M μ (k.1 + 1) (Nat.le_add_left _ _) k.2).wt.ρ
      (M μ (k.1 + 1) (Nat.le_add_left _ _) k.2).J (M μ (k.1 + 1) (Nat.le_add_left _ _) k.2).χ :=
    (M μ (k.1 + 1) (Nat.le_add_left _ _) k.2).real_range ▸ LinearMap.mem_range_self _ x
  refine ⟨fun g => l ((M μ (k.1 + 1) (Nat.le_add_left _ _) k.2).real x g), fun e => hl (congrFun e g₀), fun κ h g => ?_, fun κ hJ g => ?_⟩
  · have e := congrFun (hm.2 ⟨κ, h⟩) g
    exact (congrArg l e).trans (map_smul l _ _)
  · have e1 := ad.read _ hμ k x (g * κ)
    have e2 := ad.read _ hμ k x g
    have e3 := (Y.IL.jMt _ hμ k x).2.2 _ hJ ((ad.PV k).ψ g)
    rw [← map_mul] at e3
    have e4 := e1.trans (e3.trans (congrArg _ e2.symm))
    rw [← map_smul] at e4
    exact (congrArg l ((ad.eW _ hμ k).injective e4)).trans (map_smul l _ _)


set_option maxHeartbeats 1000000 in
theorem types_of (ad : MtAd Y M) {tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E} {Q : D.what₂.places.Pl → Finset (PlE D.host)}
    (hin : MtInput D M tup Q) {μ0 : T} (hlev : R.toRealDat.toLevCh.Is μ0) (hgl : R.toRealDat.grp_levels F.lv2)
    (i : D.nd.Loc) (μ : D.what₂.Tup) (k : Fin D.R.m) (hμ : μ = D.nd.mu i) (hnt : Nontrivial (D.what₂.Mt μ ((k : ℕ) + 1)))
    (s : SplitPlace D.host.E) (φ : Os s →+* kP s.w) (b : GL (Fin D.R.nV) (kP s.w)) (hs : s.w ∈ R.Pg)
    (hw : ∃ kk v, s.w = D.naut.plGw kk v) (hfr : FrameRed (GlobalTheory.FrameBlockDiagonal.rankV D k) (ad.PV k) (R.βV k) s φ b) :
    ∃ (f : GAf D.host.E D.R.nV → ℂ) (J : Subgroup (GAf D.host.E D.R.nV)) (χ : J →* ℂˣ)
      (ψ₀ : AddChar (s.v.adicCompletion (maximalRealSubfield D.host.E)) ℂ)
      (ξ : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ),
      f ≠ 0 ∧ NG.IsPsi0 s ψ₀ ∧ NG.LevelUni J χ s D.R.r ψ₀ ξ ∧ (∀ κ (h : κ ∈ J) g, f (g * κ) = ((χ ⟨κ, h⟩ : ℂˣ) : ℂ) * f g) ∧
      ∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {s.v} κ → ∀ y : GL (Fin D.R.nV) (Os s), IsCompOf s κ y →
        (IsBlockUpperUnipotentMatrix D.R.r (b * Matrix.GeneralLinearGroup.map φ y * b⁻¹) → ∃ c : ℂ, ∀ g, f (g * κ) = c * f g) ∧
        (Matrix.GeneralLinearGroup.map φ y = 1 → ∀ g, f (g * κ) = f g) := by
  have hu : Formalism.IndefR.RecTie.Used0 D μ := hμ ▸ Model.used_loc i
  rw [D.nd.mu_w i] at hμ
  subst hμ
  obtain ⟨kk, v, hv⟩ := hw
  obtain ⟨ψ₀, ξ, h1, -, h2⟩ := hin.uni (D.nd.w i) k kk v s hv
  obtain ⟨f, hf, hJ, hL⟩ := exists_fn ad _ hu k hnt
  obtain ⟨c, hc⟩ := hlev.βV k
  rw [one_pow] at hc
  obtain ⟨ψ0, -, hP0, -⟩ := hgl
  refine ⟨f, _, _, ψ₀, ξ, hf, h1, h2, hJ, fun κ hU hT y hy => ?_⟩
  have key := mem_level (GlobalTheory.FrameBlockDiagonal.rankV D k) (ad.std k) hc
    (Formalism.IndefR.RecTie.datVP R.toRealDat k (Y.tupT (D.what₂.muTw (D.nd.w i))) (R.toRealDat.levR F.lv2 false))
    (le_of_eq (GlobalTheory.FrameBlockDiagonal.rankV D k))
    (fun g hg => by
      show g ∈ (R.toRealDat.levR F.lv2 false).H
      rw [hP0]
      exact fun PP _ => hg PP)
    s (fun PP hPP => GlobalTheory.HeckeCharacterRestriction.not_isConjPl_union hlev _ hPP (Or.inl hs)) hfr hU hT hy
  refine ⟨fun hb => ⟨_, hL κ (key.1 hb)⟩, fun h1 g => ?_⟩
  rw [hL κ (key.2 h1).1 g, (key.2 h1).2, one_mul]

end Read


end GlobalTheory.FrameTypes

end
end
