module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
public import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair
public import Formalism.LocalToGlobal.ClassOfRecordOfChoice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WtBigRun

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
set_option synthInstance.maxHeartbeats 200000

section
set_option genSizeOfSpec false
set_option genInjectivity false
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam
section Gen
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word)
set_option maxHeartbeats 1000000 in
structure GeometricFamily where
  g : Geo D
  j : SmT (_root_.GlobalTheory.Fam.pk_z W).MX →ₗ[ℂ] (Formalism.L2.Forms.FrP D → ℂ)
  k : Type
  [fld : Field k]
  [val : ValuativeRel k]
  [top : TopologicalSpace k]
  [loc : IsNonarchimedeanLocalField k]
  ι : Type
  v : VCom (commOf (_root_.GlobalTheory.Fam.pk_z W) u g)
  o : TDat (commOf (_root_.GlobalTheory.Fam.pk_z W) u g) k ι
  n : ℕ
  G : Fin n → GLoc v
  pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg
  Q : ∀ PP, _root_.GlobalTheory.Fam.QAllAlt W PP → GlobalTheory.QTw.QGeo v (baseOf (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u g) PP
  d : _root_.GlobalTheory.MiTop.BottomData W u
  c₀ : ℕ → ℂ
attribute [instance] _root_.GlobalTheory.Fam.GeometricFamily.fld _root_.GlobalTheory.Fam.GeometricFamily.val _root_.GlobalTheory.Fam.GeometricFamily.top _root_.GlobalTheory.Fam.GeometricFamily.loc
variable {W u} (a : _root_.GlobalTheory.Fam.GeometricFamily W u)
abbrev GeometricFamily.fam (row : ∀ t, RowCh (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u a.g t) (col : ∀ t : W.P.T, ColCh u (D.chTw u (W.P.I.tup t))) : _root_.GlobalTheory.Fam.FamilyCharacter W u :=
  ⟨a.g, a.j, row, col⟩
structure GeometricFamily.Is : Prop where
  meas : GeoMeas (_root_.GlobalTheory.Fam.pk_z W) a.g
  last : (commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g).VolLast
  x : ∀ j, j ≤ D.R.m → (a.g.x j).Is
  vis : a.v.Is
  shape : ShapeOff a.v a.o
  gpin : GPin a.G
  tie : ∀ row col, _root_.GlobalTheory.Fam.CommutingVectorTie (a.fam row col) a.v ∧ _root_.GlobalTheory.Fam.LocalGroupReading (a.fam row col) a.G a.pl
  top : _root_.GlobalTheory.Fam.LeadingReadAt W u a.j a.g.bT
  norm : star a.o.ζ₀ ⬝ᵥ a.g.Lz.gram *ᵥ a.o.ζ₀ = (((D.mem u).A.T : ℕ) : D.host.E) ∧
    ∀ j h, a.v.τ j h *ᵥ a.o.ζ₀ = (-D.host.xi0 ^ (D.R.m / 2)) • (a.g.bes j 0 h).ζ
  stdG : ∀ i, (∀ j hj, IsStdFr GlobalTheory.SymBridge.xPos ((a.G i).FX j hj)) ∧ IsStdFr GlobalTheory.SymBridge.zPos (a.G i).FT ∧
    (a.G i).z₀ = fun r => (ofSplit (a.G i).q).pr (a.o.ζ₀ r)
  stdQ : ∀ PP h, (∀ j hj, IsStdFr GlobalTheory.SymBridge.xPos ((a.Q PP h).FX j hj)) ∧ IsStdFr GlobalTheory.SymBridge.zPos (a.Q PP h).FT ∧
    (a.Q PP h).z₀ = fun r => (ofSplit (a.Q PP h).q).pr (a.o.ζ₀ r)
  bot : (∀ h0, a.d.B.lev = (commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g).B 0 D.R.rS h0) ∧ a.d.b = a.g.b 0 ∧ a.d.B.Adapted (W.S.tr u).wt ∧
    ∀ r, (a.d.B.d.i₀ *ᵥ vecB a.d.B.o a.d.B.ζ) r = W.S.X.ιE (W.S.X.zR u (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) r))
end Gen
section True
open GlobalTheory.Mem GlobalTheory.Mem.Col2
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : B.Word}
structure GeometricFamily.True (a : _root_.GlobalTheory.Fam.GeometricFamily W u) : Prop where
  pinX : GlobalTheory.AdForm.PinX I l Z (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ a.g.x a.g.vac a.c₀
  std : @GlobalTheory.AdForm.StdT B X I l Z u a.k a.fld a.val a.top a.loc a.ι (@TDat.p _ _ _ a.fld a.val a.top a.loc _ a.o)
    (@TDat.β _ _ _ a.fld a.val a.top a.loc _ a.o) (@TDat.Q _ _ _ a.fld a.val a.top a.loc _ a.o) fun j => (a.g.x j).L
  emb : GlobalTheory.AdForm.IsEmbTop (D := I.rec7 l Z) (TC.z0 X u) ((a.g.oT B.R.m rfl).emb.comp (MonoidHom.inl _ _))
  z0 : ∀ r, vecB (a.g.oT B.R.m rfl) (@TDat.ζ₀ _ _ _ a.fld a.val a.top a.loc _ a.o) r =
    (show Fin (B.R.N B.R.m) → (I.rec7 l Z).host.E from TC.z0 X u) (Fin.cast (Formalism.L2.Forms.rankN (I.rec7 l Z) _ le_rfl) r)
structure GeometricFamilyConditions (W : _root_.GlobalTheory.MiS.RealPackAlt ex) : Prop where
  xi : ∀ t, ChrEq ((_root_.GlobalTheory.Fam.pk_z W).xi t) (I.xi (W.P.I.tup t))
  Q : ∀ t PP, PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t ↔ PP ∈ Formalism.L2.Col.QE I.sel (I.tup (W.P.I.tup t) : Formalism.L2.DIV.Chr B.fields.F B.fields.E B.fields.K)
  top1 : ∀ u, ∃ j, _root_.GlobalTheory.Fam.LeadingReadAt W u j 1
end True
end GlobalTheory.Fam
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColumnChoiceWithTies
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem.Top
namespace GlobalTheory.Cp
abbrev BaseLevelTiedChoiceAlt (𝒜 : FamClass) (sel : _root_.Formalism.L2.TwistSelection 𝒜) :=
  ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
    {P : Formalism.L2.Rows.RowSideFamily (Fm.ex x hx i) // _root_.Formalism.L2.Rows.RowSideDeterminedAlt ((sel Fm hc).2 x hx h i).T P}
abbrev SelectionDefiniteHeightCondition (𝒜 : FamClass) (sel : _root_.Formalism.L2.TwistSelection 𝒜) :=
  ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
    {p : ℕ × ℕ // (Fm.D x i).s.Del = (p.1 : ℚ) ∧ (Fm.L x i).etaSz = ((Fm.D x i).R.m : ℝ) * (p.2 : ℝ)}
abbrev ColumnChoiceCompatibleSelection (𝒜 : FamClass) (sel : _root_.Formalism.L2.TwistSelection 𝒜) (selP : _root_.GlobalTheory.Cp.BaseLevelTiedChoiceAlt 𝒜 sel) :=
  ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
    _root_.GlobalTheory.Cp.SquareIntegrableColumns ((sel Fm hc).2 x hx h i).T (selP Fm hc x hx h i).1
abbrev SelectionSpectralCondition (𝒜 : FamClass) (sel : _root_.Formalism.L2.TwistSelection 𝒜) :=
  ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
    _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt ((sel Fm hc).2 x hx h i)
def IndefiniteScaleAtPoint {𝒜 : FamClass} (sel : _root_.Formalism.L2.TwistSelection 𝒜) (selP : _root_.GlobalTheory.Cp.BaseLevelTiedChoiceAlt 𝒜 sel) (selDH : _root_.GlobalTheory.Cp.SelectionDefiniteHeightCondition 𝒜 sel) {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm)
    (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x) :
    Formalism.L2.Indef.DefSub (selP Fm hc x hx h i).1.A3.fam3.amb3 → Formalism.L2.Indef.IndefScale (selP Fm hc x hx h i).1.A3.fam3.base3 :=
  fun Zs =>
    let z := Formalism.L2.DIV.ZscOfNum3 (selP Fm hc x hx h i).1.A3 (selP Fm hc x hx h i).1.P0 (selP Fm hc x hx h i).1.ψ0
      (Formalism.L2.DIV.ofRecord (Fm.D x i) (Fm.L x i) (selDH Fm hc x hx h i).1.1 (selDH Fm hc x hx h i).1.2) (Equiv.refl _) (Fm.L x i).Nc Zs
    { z with l6m := fun j => z.l6m j - Fm.Csz * z.l6u, l6u := 0 }
abbrev SelectionBundle (𝒜 : FamClass) (sel : _root_.Formalism.L2.TwistSelection 𝒜) (selS : _root_.GlobalTheory.Cp.SelectionSpectralCondition 𝒜 sel) (selP : _root_.GlobalTheory.Cp.BaseLevelTiedChoiceAlt 𝒜 sel) (selDH : _root_.GlobalTheory.Cp.SelectionDefiniteHeightCondition 𝒜 sel) (selC : _root_.GlobalTheory.Cp.ColumnChoiceCompatibleSelection 𝒜 sel selP) :=
  ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
    _root_.Formalism.IndefR.RealTBAlt ((sel Fm hc).2 x hx h i) (selP Fm hc x hx h i).1 (selC Fm hc x hx h i).c.face (selC Fm hc x hx h i).Sp
      (_root_.GlobalTheory.Cp.IndefiniteScaleAtPoint sel selP selDH Fm hc x hx h i) (selS Fm hc x hx h i)
def EventuallyAlongSelection {𝒜 : FamClass} (sel : _root_.Formalism.L2.TwistSelection 𝒜) {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm)
    (Q : ∀ (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x), Prop) : Prop :=
  ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x), x0 ≤ x → ∀ i : Fm.Ix x, Q x hx h i
end GlobalTheory.Cp
namespace GlobalTheory.Fc
open GlobalTheory.Cp
set_option genInjectivity false in
set_option genSizeOfSpec false in
structure BundleCondition (D : D7) (O : Obj D) (c : ℝ) : Type 1 where
  R : _root_.Formalism.L2.RecTAlt O.ex
  S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R
  P : Formalism.L2.Rows.RowSideFamily O.ex
  pin : _root_.Formalism.L2.Rows.RowSideDeterminedAlt R.T P
  DH : {p : ℕ × ℕ // D.s.Del = (p.1 : ℚ) ∧ O.L.etaSz = (D.R.m : ℝ) * (p.2 : ℝ)}
  C : _root_.GlobalTheory.Cp.SquareIntegrableColumns R.T P
  B : _root_.Formalism.IndefR.RealTBAlt R P C.c.face C.Sp (zsc P DH.1.1 DH.1.2 c) S
variable {𝒜 : FamClass} (σ : RawSel _root_.GlobalTheory.Fc.BundleCondition 𝒜)
def familySelection : _root_.Formalism.L2.TwistSelection 𝒜 := fun Fm hc => ⟨Fm.x1, fun x hx _ i => (σ Fm hc x hx i).R⟩
def spectralConditionOfRawSelection : _root_.GlobalTheory.Cp.SelectionSpectralCondition 𝒜 (_root_.GlobalTheory.Fc.familySelection σ) := fun Fm hc x hx _ i => (σ Fm hc x hx i).S
def baseLevelChoiceOfRawSelection : _root_.GlobalTheory.Cp.BaseLevelTiedChoiceAlt 𝒜 (_root_.GlobalTheory.Fc.familySelection σ) := fun Fm hc x hx _ i => ⟨(σ Fm hc x hx i).P, (σ Fm hc x hx i).pin⟩
def definiteHeightOfRawSelection : _root_.GlobalTheory.Cp.SelectionDefiniteHeightCondition 𝒜 (_root_.GlobalTheory.Fc.familySelection σ) := fun Fm hc x hx _ i => (σ Fm hc x hx i).DH
def columnChoiceOfRawSelection : _root_.GlobalTheory.Cp.ColumnChoiceCompatibleSelection 𝒜 (_root_.GlobalTheory.Fc.familySelection σ) (_root_.GlobalTheory.Fc.baseLevelChoiceOfRawSelection σ) := fun Fm hc x hx _ i => (σ Fm hc x hx i).C
def selectionBundleOfRawSelection : _root_.GlobalTheory.Cp.SelectionBundle 𝒜 (_root_.GlobalTheory.Fc.familySelection σ) (_root_.GlobalTheory.Fc.spectralConditionOfRawSelection σ) (_root_.GlobalTheory.Fc.baseLevelChoiceOfRawSelection σ) (_root_.GlobalTheory.Fc.definiteHeightOfRawSelection σ) (_root_.GlobalTheory.Fc.columnChoiceOfRawSelection σ) := fun Fm hc x hx _ i => (σ Fm hc x hx i).B
end GlobalTheory.Fc
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowAtOfRatStep
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
namespace GlobalTheory.BigOn.Exp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Sets
variable {D : D7} {ρ : Setup D.ntw} (hρ : ρ.Good) {i : D.ntw.Tw} {j : Fin D.R.m} {b : Bool} (rd : Rd ρ D.nexp i j b)
end Sets
section Hyp
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m}
end Hyp
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (w : D.what₂.places.Pl) (j : Fin D.R.m)
variable {p w j}
namespace Fit
variable {ρ : Setup D.ntw} {hρ : ρ.Good} {ν : ℂ} (h : Fit p w j hρ ν)
include h
end Fit
end Point
def TwistConditions (Q : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), Pt Fm x hx i →
    (Fm.D x i).what₂.places.Pl → Fin (Fm.D x i).R.m → Prop) : Prop :=
  _root_.GlobalTheory.BigOn.AtPtsAlt fun Fm x hx i p => ∀ w, (Fm.D x i).plEq w ∈ p.R.twPl → ∀ j, Q Fm x hx i p w j
section AtTw
variable {Q Q' : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), Pt Fm x hx i →
  (Fm.D x i).what₂.places.Pl → Fin (Fm.D x i).R.m → Prop}
theorem TwistConditions.and (h : _root_.GlobalTheory.BigOn.Exp.TwistConditions Q) (h' : _root_.GlobalTheory.BigOn.Exp.TwistConditions Q') : _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => Q Fm x hx i p w j ∧ Q' Fm x hx i p w j :=
  Closed.imp (Closed.and h h') fun _ _ _ H =>
    let ⟨x0, K⟩ := _root_.GlobalTheory.BigTop.EventuallyAtPoints.and H.1 H.2
    ⟨x0, fun x hx h0 i p r m w hw j => ⟨(K x hx h0 i p r).1 m w hw j, (K x hx h0 i p r).2 m w hw j⟩⟩
theorem TwistConditions.imp (h : _root_.GlobalTheory.BigOn.Exp.TwistConditions Q) (f : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (p : Pt Fm x hx i), p.PointConditions' →
    More p → ∀ w, (Fm.D x i).plEq w ∈ p.R.twPl → ∀ j, Q Fm x hx i p w j → Q' Fm x hx i p w j) : _root_.GlobalTheory.BigOn.Exp.TwistConditions Q' :=
  Closed.imp h fun Fm _ _ ⟨x0, K⟩ => ⟨x0, fun x hx h0 i p r m w hw j => f Fm x hx i p r m w hw j (K x hx h0 i p r m w hw j)⟩
theorem TwistConditions.of_forall (f : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (p : Pt Fm x hx i), p.PointConditions' →
    More p → ∀ w, (Fm.D x i).plEq w ∈ p.R.twPl → ∀ j, Q Fm x hx i p w j) : _root_.GlobalTheory.BigOn.Exp.TwistConditions Q :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ => ⟨0, fun x hx _ i p => f Fm x hx i p⟩⟩⟩
end AtTw
def CanonicalExists : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∃ rd : Can p w j, IsCan p rd ∧
  ∃ (n : ℕ) (β : Module.Basis (Fin n) (Fm.D x i).what₂.LL (Fin ((R2 p).nW j) → (Fm.D x i).what₂.LL)),
    LinearIndependent (FractionRing ((Fm.ex x hx i).nch.Oe w)) fun a => rd (β a)
def CanonicalProjection₂ : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x _ i p w j => ∀ rd : Can p w j, IsCan p rd → ∀ y,
  rd ((((R2 p).FW j).eOp fun g => (idemOf p.P.A3.A.X).coeff g) y) = eExt (Fm.D x i).nexp _ _ _ _ (rd y)
def TwAdmAlt : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i _ w _ =>
  IntegralHeckeForms.TwOK ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.k' w) ((Fm.ex x hx i).nch.Q w)
                     (GlobalTheory.TwistIndex.chosenChar (Fm.ex x hx i).nch w) ∧
    IntegralHeckeForms.ClsQ (D := Fm.D x i) ((Fm.ex x hx i).nch.Q w) ∧ (Fm.D x i).ntw.NonzeroIndexPlace ((Fm.ex x hx i).nch.twI w)
def LowerBoundAtPlace : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i _ w _ => ∀ P : Pl (Fm.D x i).host.E,
  (((Fm.D x i).host.QS * (Fm.D x i).host.q * Ideal.absNorm (Fm.D x i).host.ccK * ((Fm.D x i).host.g 0 * (Fm.D x i).host.g 1 * (Fm.D x i).host.pde *
    (Fm.D x i).host.pde') : ℕ) : 𝓞 (Fm.D x i).host.E) ∈ P.asIdeal → P ∈ (Fm.D x i).ntw.S0 ((Fm.ex x hx i).nch.twI w)
def ConditionAtPlace : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ (ρ : Setup (Fm.D x i).ntw) (hρ : ρ.Good), RealPin p.R p.cG ρ →
  ρ.LevelOf (Fm.D x i).nexp → RatRow p.nexp p.v₀ hρ ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)
def RationalityHypothesis : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j =>
  ∃ (T' : CoreJ (Fm.D x i)) (_ : Algebra T'.Q.c.F (Fm.D x i).what₂.LL) (Rl' : RealDat3 (Fm.D x i) p.P.A3 T'.Q.c.F)
    (cG' : G0 Rl'.Pg (Fm.D x i).R.r ≃* G0g (Fm.D x i).nd) (S' : NX.RatDat (Fm.D x i).ntw) (YS' : NX.NExpRealS Rl' cG' S')
    (F' : Face (Fm.D x i) p.P.A3.A) (κ' : ∀ j : Fin (Fm.D x i).R.m, WeightFamilies.Wt (Fm.D x i) ((j : ℕ) + 1))
    (v₀' : ∀ (j : Fin (Fm.D x i).R.m) (σ : (Fm.D x i).what₂.LL →+* ℂ), (Rl'.MW j σ).Vec)
    (O' : ∀ j, OMDat T'.toCore Rl'.toRealDat j Unit (fun _ => p.P.A3.A.μ0)) (hV' : T'.V ((j : ℕ) + 1) T'.σ₀ = Wc (Fm.D x i) j),
    RatHyp T' Rl' F' κ' v₀' O' ((Fm.ex x hx i).nch.twI w) j hV' ∧
      (∀ ρ : Setup (Fm.D x i).ntw, RealPin p.R p.cG ρ → RealPin Rl' cG' ρ) ∧
      ∀ (ρ : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (b : Bool), RatRow YS' v₀' hρ ((Fm.ex x hx i).nch.twI w) j b →
        RatRow p.nexp p.v₀ hρ ((Fm.ex x hx i).nch.twI w) j b
theorem twist_at_statement_of_ratHypAt (h : _root_.GlobalTheory.BigOn.Exp.RationalityHypothesis) (hR : RatStep) : _root_.GlobalTheory.BigOn.Exp.ConditionAtPlace :=
  _root_.GlobalTheory.BigOn.Exp.TwistConditions.imp h fun Fm x hx i _ _ _ _ _ j ⟨T', _, Rl', cG', S', YS', F', κ', v₀', O', hV', h1, h2, h3⟩ ρ hρ hp hL =>
    h3 ρ hρ _ (hR _ _ _ _ _ _ T' Rl' cG' S' YS' F' κ' v₀' O' ρ hρ _ j _ hV' (h2 ρ hp) hL
      ⟨(Fm.params x hx i).level_split _ (Fm.D x i).host.pde_level.1, (Fm.params x hx i).level_split _ (Fm.D x i).host.pde_level.2⟩ h1)
def CompatibilityRational : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ Z : ExportTie p.nexp p.v₀,
  IsNorm p.R p.v₀ (Z.ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) (Z.ν ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ∧ RatAt p w j Z.good (Z.ν ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w))
def RecursiveSide : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ Z : ExportTie p.nexp p.v₀, RatAt p w j Z.good (Z.ν ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) →
  Submodule.span ((Fm.ex x hx i).nch.Oe w) ((fun a => (1 : FractionRing ((Fm.ex x hx i).nch.Oe w)) ⊗ₜ (Fm.D x i).nexp.th _ _ _ a) ''
      IntegralHeckeForms.SgJ (Fm.D x i).nexp (twE Fm x hx i) ((Fm.ex x hx i).nch.twI w) ((j : ℕ) + 1) ((Fm.ex x hx i).nch.sd w)) = baseLat p w j Z.good (Z.ν ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ∧
  Submodule.span ((Fm.ex x hx i).nch.Oe w) (incl (Fm.D x i).nexp _ _ _ ((Fm.ex x hx i).nch.Oe w) ((Fm.ex x hx i).nch.k' w) ''
      ⋃ a ∈ IntegralHeckeForms.SgJ (Fm.D x i).nexp (twE Fm x hx i) ((Fm.ex x hx i).nch.twI w) ((j : ℕ) + 1) ((Fm.ex x hx i).nch.sd w),
        (Fm.D x i).nexp.thPsi _ _ _ ((Fm.ex x hx i).nch.k' w) ((Fm.ex x hx i).nch.Q w)
          (GlobalTheory.TwistIndex.chosenChar (Fm.ex x hx i).nch w) a) = twLat p w j Z.good (Z.ν ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w))
def AdaptedExistence₂ : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x _ i p w _ => ∀ ρ : Setup (Fm.D x i).ntw, ρ.Good → RealPin p.R p.cG ρ →
  ∃ ρ' : Setup (Fm.D x i).ntw, ρ'.Good ∧ SameBut ρ ρ' ∧ Adapted p w ρ'
def ConjugateBase : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ (ρ ρ' : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (hρ' : ρ'.Good) (ν ν' : ℂ),
  RealPin p.R p.cG ρ → SameBut ρ ρ' → IsNorm p.R p.v₀ (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν →
    RatAt p w j hρ ν → Fit p w j hρ' ν' → baseLat p w j hρ ν = baseLat p w j hρ' ν'
def ConjugateTwist : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ (ρ ρ' : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (hρ' : ρ'.Good) (ν ν' : ℂ),
  RealPin p.R p.cG ρ → SameBut ρ ρ' → IsNorm p.R p.v₀ (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν →
    RatAt p w j hρ ν → Fit p w j hρ' ν' → twLat p w j hρ ν = twLat p w j hρ' ν'
def TwistCharacter : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ ρ : Setup (Fm.D x i).ntw, ρ.Good → Adapted p w ρ →
  ChrEq (ρ.tw ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w) ((Fm.ex x hx i).nch.k' w) ((Fm.ex x hx i).nch.Q w)
      (GlobalTheory.TwistIndex.chosenChar (Fm.ex x hx i).nch w)).chi (p.Tp.psi w) ∧
    p.R.xi (p.R.mu ((Fm.D x i).plEq w)) = (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)).de.chi *
      (ρ.tw ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w) ((Fm.ex x hx i).nch.k' w) ((Fm.ex x hx i).nch.Q w)
        (GlobalTheory.TwistIndex.chosenChar (Fm.ex x hx i).nch w)).chi
def CanonicalFits (Q : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (p : Pt Fm x hx i) (w : (Fm.D x i).what₂.places.Pl)
    (j : Fin (Fm.D x i).R.m) (ρ : Setup (Fm.D x i).ntw), ρ.Good → ℂ → Can p w j → Prop) : Prop :=
  _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ (ρ : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (ν : ℂ) (rd : Can p w j), Fit p w j hρ ν → IsCan p rd →
    Q Fm x hx i p w j ρ hρ ν rd
def BaseUpperBound₂ : Prop := _root_.GlobalTheory.BigOn.Exp.CanonicalFits fun _ _ _ _ p w j _ hρ ν rd => realBase p rd ≤ baseLat p w j hρ ν
def BaseLowerBound₂ : Prop := _root_.GlobalTheory.BigOn.Exp.CanonicalFits fun _ _ _ _ p w j _ hρ ν rd => baseLat p w j hρ ν ≤ realBase p rd
def TwistUpperBound₂ : Prop := _root_.GlobalTheory.BigOn.Exp.CanonicalFits fun _ _ _ _ p w j _ hρ ν rd => realTw p rd ≤ twLat p w j hρ ν
def TwistLowerBound : Prop := _root_.GlobalTheory.BigOn.Exp.CanonicalFits fun _ _ _ _ p w j _ hρ ν rd => twLat p w j hρ ν ≤ realTw p rd
def InductionConditions : Prop := _root_.GlobalTheory.BigOn.Exp.CanonicalExists ∧ _root_.GlobalTheory.BigOn.Exp.CanonicalProjection₂ ∧ _root_.GlobalTheory.BigOn.Exp.TwAdmAlt ∧ _root_.GlobalTheory.BigOn.Exp.ConditionAtPlace ∧ _root_.GlobalTheory.BigOn.Exp.CompatibilityRational ∧ _root_.GlobalTheory.BigOn.Exp.RecursiveSide ∧ _root_.GlobalTheory.BigOn.Exp.AdaptedExistence₂ ∧ _root_.GlobalTheory.BigOn.Exp.ConjugateBase ∧ _root_.GlobalTheory.BigOn.Exp.ConjugateTwist ∧ _root_.GlobalTheory.BigOn.Exp.BaseUpperBound₂ ∧ _root_.GlobalTheory.BigOn.Exp.BaseLowerBound₂ ∧ _root_.GlobalTheory.BigOn.Exp.TwistUpperBound₂ ∧ _root_.GlobalTheory.BigOn.Exp.TwistLowerBound
theorem exists_exportTie_fit_at_tw (h1 : _root_.GlobalTheory.BigOn.Exp.TwAdmAlt) (h2 : _root_.GlobalTheory.BigOn.Exp.ConditionAtPlace) (h3 : _root_.GlobalTheory.BigOn.Exp.AdaptedExistence₂) : _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x _ i p w j => Nonempty (ExportTie p.nexp p.v₀) ∧
    ∀ Z : ExportTie p.nexp p.v₀, ∃ (ρ : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (ν : ℂ), SameBut Z.ρ ρ ∧ Fit p w j hρ ν :=
  _root_.GlobalTheory.BigOn.Exp.TwistConditions.imp (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and h1 (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and h2 h3)) fun _ _ _ _ _ _ hm _ _ _ ⟨a1, a2, a3⟩ => ⟨hm.2.2.series, fun Z =>
    let ⟨ρ, hρ, hs, ha⟩ := a3 Z.ρ Z.good Z.pin
    have hL := levelOf_of_sameBut hm.2.2 Z.good hρ Z.pin ha.1 hs (levelOf_exportTie Z)
    let ⟨ν, hn, hr⟩ := a2 ρ hρ ha.1 hL
    ⟨ρ, hρ, ν, hs, ha, hn, ⟨hr.1, hr.2.1 _ _ _ a1.1 a1.2.1⟩, hL⟩⟩
theorem InductionConditions.exportSt (h : _root_.GlobalTheory.BigOn.Exp.InductionConditions) : _root_.GlobalTheory.BigOn.ExportedStatement := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  refine Closed.imp (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and (_root_.GlobalTheory.BigOn.Exp.exists_exportTie_fit_at_tw h3 h4 h7) (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and h1 (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and h2 (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and h5 (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and h6 (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and h8 (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and h9
    (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and h10 (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and h11 (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and h12 h13)))))))))) fun Fm _ _ ⟨x0, K⟩ => ⟨x0, fun x hx h0 i p r m v hv j => ?_⟩
  obtain ⟨⟨⟨Z⟩, a0⟩, ⟨rd, hc, hβ⟩, a2, a5, a6, a8, a9, a10, a11, a12, a13⟩ :=
    K x hx h0 i p r m ((Fm.D x i).plEq.symm v) (by rwa [Equiv.apply_symm_apply]) j
  obtain ⟨ρ, hρ, ν, hs, hf⟩ := a0 Z
  obtain ⟨hN, hR⟩ := a5 Z
  obtain ⟨r1, r2⟩ := a6 Z hR
  have b1 := le_antisymm (a10 ρ hρ ν rd hf hc) (a11 ρ hρ ν rd hf hc)
  have b2 := le_antisymm (a12 ρ hρ ν rd hf hc) (a13 ρ hρ ν rd hf hc)
  simp only [realBase, realTw, Equiv.apply_symm_apply] at b1 b2
  exact ⟨rd, hβ, a2 rd hc, (b1.trans (a8 Z.ρ ρ Z.good hρ _ ν Z.pin hs hN hR hf).symm).trans r1.symm,
    (b2.trans (a9 Z.ρ ρ Z.good hρ _ ν Z.pin hs hN hR hf).symm).trans r2.symm⟩
end GlobalTheory.BigOn.Exp
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftWeightNumerator
set_option synthInstance.maxHeartbeats 200000

section
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop
namespace GlobalTheory.CovTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
def HostNAlt (M : ℝ) : Prop := _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι _ _ PP A => HostNum (Fm.D x ι) (Fm.L x ι) PP A M
def LiftWeightNumerator : Prop := _root_.GlobalTheory.CovTop.LiftsCondition fun _ _ _ _ p i PP _ => WtNum p i PP
end GlobalTheory.CovTop
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ChartZero
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeSaw GlobalTheory.Fam Matrix ValuativeRel IsLocalRing GlobalTheory.LocMod
namespace GlobalTheory.MiTop
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : D.what₂.Word} (f : _root_.GlobalTheory.Fam.FamilyCharacter W u)
  (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0))
def LevTraceAlt : Prop :=
  ∀ κ ∈ GfC (D.sp.X 0), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _))
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F),
    GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) κ = y.1.1 →
    ((y : GL _ _) ∈ (_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.U ↔
      (show GA D (D.sp.Y 0) from f.g.b 0)⁻¹ * embA B.d B.o κ * (show GA D (D.sp.Y 0) from f.g.b 0) ∈ _root_.GlobalTheory.MiTop.rJ_z W) ∧
    ∀ hy : (y : GL _ _) ∈ (_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.U, (((_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.chi ⟨_, hy⟩ : ℂˣ) : ℂ) *
      _root_.GlobalTheory.MiTop.realCharacter W ((show GA D (D.sp.Y 0) from f.g.b 0)⁻¹ * embA B.d B.o κ * (show GA D (D.sp.Y 0) from f.g.b 0)) = 1
structure LocalBottomCompatibility {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
    (v : VCom f.c) (o : TDat f.c k ι) {n : ℕ} (G : Fin n → GLoc v) : Prop where
  lev : ∀ h₀ : 0 + 2 * D.R.rS + 2 = D.R.m, B.lev = f.c.B 0 D.R.rS h₀
  adapted : B.Adapted (W.S.tr u).wt
  norm : ∃ μ lam : D.host.E, μ * lam = -D.host.xi0 ^ (D.R.m / 2) ∧
    (∀ r, (B.d.i₀ *ᵥ vecB B.o B.ζ) r = μ * W.S.X.ιE (W.S.X.zR u (Fin.cast (rank_eq W.S.X W.Q.instEq) r))) ∧
    ∀ j h, v.τ j h *ᵥ o.ζ₀ = lam • (f.c.bes j 0 h).ζ
  last : ∀ i, (G i).z₀ = fun r => (ofSplit (G i).q).pr (o.ζ₀ r)
  lat : ∀ p, p ∉ v.tP → GlobalTheory.FinPl.latV (D.sp.X 0) (f.g.x 0).L (· = p) = GlobalTheory.FinPl.latV (D.sp.X 0)
    ((_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.Lb.map ((LinearEquiv.funCongrLeft D.host.E D.host.E
      (finCongr (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)))).toLinearMap.restrictScalars (𝓞 D.host.E))) (· = p)
  trace : _root_.GlobalTheory.MiTop.LevTraceAlt f B
def ChartAtZeroCondition : Prop :=
  ∀ t, ∃ α₀ : (f.t t).Ch 0, (∀ α, α = α₀) ∧ (f.t t).e 0 α₀ = Finsupp.single (f.g.b 0) 1 ∧
    (∀ φ, _root_.GlobalTheory.MiTop.col0_alt f t φ ∈ (f.t t).Ram 0 ∧ ∀ y, (f.t t).rd 0 α₀ (_root_.GlobalTheory.MiTop.col0_alt f t φ) y = (chart0 (_root_.GlobalTheory.MiTop.formsAtZero W u)).rd W.Q.Rl.θ (D.eMu u φ).1 y) ∧
    ∀ ψ ∈ (f.t t).Ram 0, ∃ φ, ψ = _root_.GlobalTheory.MiTop.col0_alt f t φ
end GlobalTheory.MiTop
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LeafInfinitePlaceBound
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
namespace GlobalTheory.BigTop.Fun
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}
section Fit
open GlobalTheory.ChiGrid _root_.Formalism.L2.Host
variable {T : Type} {Lc : LevCh D T} {sc : Consts}
end Fit
def LeafConditions (Comparison₂ : TieT) (Q : PropT) : Prop := ∃ CF0 : ℝ, ∀ CF, CF0 ≤ CF → Closed FamHyp fun Fm CH => DIVinN Fm →
  ∃ C0 : ℝ, ∀ C, C0 ≤ C → _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun _ _ _ p => ∀ d : FunIn p CF, Comparison₂ p CF d → Q p CF d C CH
def ExistsFunctionIn (Fld : FldT) (Comparison₂ : TieT) : Prop := ∃ CF0 : ℝ, ∀ CF, CF0 ≤ CF → Closed FamHyp fun Fm _ => DIVinN Fm →
  _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun _ _ _ p => ∀ (G : Grid p CF) (W : G.Weil), W.Over p.R.toRealDat → GridFit p G → Fld p CF G W →
    ∃ d : FunIn p CF, d.G = G ∧ Comparison₂ p CF d
def LeafMinimalMass (Comparison₂ : TieT) : Prop := _root_.GlobalTheory.BigTop.Fun.LeafConditions (Fitted Comparison₂) fun _ _ d C _ => LeafMM d.O C
def LeafUniqueMap (Comparison₂ : TieT) : Prop := _root_.GlobalTheory.BigTop.Fun.LeafConditions (Fitted Comparison₂) fun p _ d _ _ =>
  ∃ ze : Tup p → _, ze p.P.A3.fam3.base3.μ0 = 1 ∧ (∀ t, ∃ n : ℕ, 0 < n ∧ ze t ^ n = 1) ∧
    LeafC (p.S false) (d.data ze ∅ fun _ => 0)
def LeafKernel (Comparison₂ : TieT) : Prop := _root_.GlobalTheory.BigTop.Fun.LeafConditions (Fitted Comparison₂) fun _ _ d _ _ => LeafKer d.O
def LeafFixedPoint (Comparison₂ : TieT) : Prop := _root_.GlobalTheory.BigTop.Fun.LeafConditions (Fitted Comparison₂) fun p _ d C _ => ∃ Tf dF, LeafFP (d.data (fun _ => 1) Tf dF) (p.S false).μ C p.Z.b
def LeafHeightMapBound (Comparison₂ : TieT) : Prop := _root_.GlobalTheory.BigTop.Fun.LeafConditions (Fitted Comparison₂) fun p _ d C _ =>
  ∀ vb : Matrix (Fin d.n) (Fin ((Df p).dQ p.P.A3.fam3.base3.μ0)) _,
    vb * (Df p).Pq p.P.A3.fam3.base3.μ0 = d.V p.P.A3.fam3.base3.μ0 →
      Formalism.HN.htMap (Pi.basisFun _ (Fin ((Df p).dQ p.P.A3.fam3.base3.μ0))) ((Df p).XQ p.P.A3.fam3.base3.μ0)
        (Pi.basisFun _ (Fin d.n)) d.X' (Matrix.mulVecLin vb) ≤ d.O.bIPa C p.Z.b
def LeafInfinitePlaceBound : Prop := _root_.GlobalTheory.BigTop.Fun.LeafConditions trivialTieCondition fun p _ d C _ =>
  ∃ g : InfinitePlace _ → ℝ, (∀ v q, (Df p).Qp p.P.A3.fam3.base3.μ0 q ≠ ⊥ →
      g v ≤ ∑ j, Real.log ((p.S false).lam j p.P.A3.fam3.base3.μ0 q v)) ∧
    -(3 * C * d.O.f * d.O.m * (d.O.N : ℝ) ^ 2 * Real.log p.Z.b) ≤ Formalism.PairingDivisionLocalBalance.meanInf _ g
def LeafUniqueSquareRoot (Comparison₂ : TieT) : Prop := _root_.GlobalTheory.BigTop.Fun.LeafConditions (Fitted Comparison₂) fun p _ d C _ => LeafOneSquare d.O (p.S false).μ C p.Z.b
def LeafDensity (Comparison₂ : TieT) : Prop := _root_.GlobalTheory.BigTop.Fun.LeafConditions (Fitted Comparison₂) fun p _ d C _ => PrimeCountingSumBound d.O C p.Z.x p.Z.b
def LeafIntegrality (Comparison₂ : TieT) : Prop := _root_.GlobalTheory.BigTop.Fun.LeafConditions (Fitted Comparison₂) fun p _ d C _ => LeafINT d.O C p.Z.b
def ArchimedeanCondition (Comparison₂ : TieT) : Prop := _root_.GlobalTheory.BigTop.Fun.LeafConditions (Fitted Comparison₂) fun p _ d C _ => LeafARCH d.O C p.Z.b
def LeafThetaBound (Comparison₂ : TieT) : Prop := _root_.GlobalTheory.BigTop.Fun.LeafConditions (Fitted Comparison₂) fun p _ d C _ => LeafTHB d.O C p.Z.x p.Z.b
def LeafWeightBound (Comparison₂ : TieT) : Prop := _root_.GlobalTheory.BigTop.Fun.LeafConditions (Fitted Comparison₂) fun p _ d C _ => LeafWt d.O C p.Z.b
def DescentHeightCondition : Prop := _root_.GlobalTheory.BigTop.Fun.LeafConditions trivialTieCondition fun p _ d _ _ => leafHypothesesConst d.O ∧ LatticeConstantBound d.O p.Z.b
def RankGapBound' : Prop := _root_.GlobalTheory.BigTop.Fun.LeafConditions trivialTieCondition fun p _ d C _ => DegreeAndSizeBounds d.O C p.Z.b
def RamifiedSumBound' : Prop := _root_.GlobalTheory.BigTop.Fun.LeafConditions trivialTieCondition fun p _ d C _ => PrimePowerModuliSumBound d.O C p.Z.b ∧ LeafCS d.O p.Z.b
def DescentPolynomialCondition : Prop := _root_.GlobalTheory.BigTop.Fun.LeafConditions trivialTieCondition fun p _ d C CH => LeafPol d.O C p.Z.x CH p.Z.b
def ScaleCondition : Prop := Closed FamHyp fun Fm _ => _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun _ _ _ p =>
  1 ≤ p.Z.x ∧ 1 ≤ Real.log p.Z.b ∧ Real.log p.Z.b + Real.log p.Z.x ≤ 3 * Real.log p.Z.b
def BundleCondition : Prop := ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), p.PointConditions' →
  (Df p).WF ∧ ∃ R0 : IndefRows (Df p), R0.toIndefData = p.S false
def ConstantFunctionFits (Fld : FldT) : Prop := ∃ CF0 : ℝ, ∀ CF, CF0 ≤ CF → Closed FamHyp fun Fm CH => DIVinN Fm →
  _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun _ _ _ p => HasGrid Fld p CF → ∀ C, (p.S false).FUN (p.N C CH)
theorem evPt_and' {eps : ℝ} {Fm : FamP eps} {P Q : ∀ (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), Pt Fm x hx i → Prop}
    (hP : _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm P) (hQ : _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm Q) : _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun x hx i p => P x hx i p ∧ Q x hx i p :=
  let ⟨a, ha⟩ := hP
  let ⟨b, hb⟩ := hQ
  ⟨max a b, fun x hx h i p hp => ⟨ha x hx (le_of_max_le_left h) i p hp, hb x hx (le_of_max_le_right h) i p hp⟩⟩
theorem evPt_mono {eps : ℝ} {Fm : FamP eps} {P Q : ∀ (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), Pt Fm x hx i → Prop}
    (hP : _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm P) (h : ∀ x hx i p, p.PointConditions' → P x hx i p → Q x hx i p) : _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm Q :=
  let ⟨a, ha⟩ := hP
  ⟨a, fun x hx h' i p hp => h x hx i p hp (ha x hx h' i p hp)⟩
theorem LeafConditions.mono {Comparison₂ Tie' : TieT} {Q Q' : PropT} (h : _root_.GlobalTheory.BigTop.Fun.LeafConditions Comparison₂ Q)
    (h' : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (CF : ℝ) (d : FunIn p CF) (C CH : ℝ), p.PointConditions' → Tie' p CF d →
      Comparison₂ p CF d ∧ (Q p CF d C CH → Q' p CF d C CH)) : _root_.GlobalTheory.BigTop.Fun.LeafConditions Tie' Q' := by
  obtain ⟨CF0, h⟩ := h
  refine ⟨CF0, fun CF hCF => (h CF hCF).imp fun Fm CH _ a hN => ?_⟩
  obtain ⟨C0, a⟩ := a hN
  exact ⟨C0, fun C hC => _root_.GlobalTheory.BigTop.Fun.evPt_mono (a C hC) fun _ _ _ p hp b d hd =>
    (h' p CF d C CH hp hd).2 (b d (h' p CF d C CH hp hd).1)⟩
theorem LeafConditions.and {Comparison₂ : TieT} {Q Q' : PropT} (h : _root_.GlobalTheory.BigTop.Fun.LeafConditions Comparison₂ Q) (h' : _root_.GlobalTheory.BigTop.Fun.LeafConditions Comparison₂ Q') :
    _root_.GlobalTheory.BigTop.Fun.LeafConditions Comparison₂ fun p CF d C CH => Q p CF d C CH ∧ Q' p CF d C CH := by
  obtain ⟨a, h⟩ := h
  obtain ⟨b, h'⟩ := h'
  refine ⟨max a b, fun CF hCF => ((h CF (le_of_max_le_left hCF)).and (h' CF (le_of_max_le_right hCF))).imp
    fun Fm CH _ c hN => ?_⟩
  obtain ⟨C0, c1⟩ := c.1 hN
  obtain ⟨C1, c2⟩ := c.2 hN
  exact ⟨max C0 C1, fun C hC => _root_.GlobalTheory.BigTop.Fun.evPt_mono (_root_.GlobalTheory.BigTop.Fun.evPt_and' (c1 C (le_of_max_le_left hC)) (c2 C (le_of_max_le_right hC)))
    fun _ _ _ _ _ e d hd => ⟨e.1 d hd, e.2 d hd⟩⟩
theorem LeafConditions.of_noTie {Q : PropT} (h : _root_.GlobalTheory.BigTop.Fun.LeafConditions trivialTieCondition Q) (Comparison₂ : TieT) : _root_.GlobalTheory.BigTop.Fun.LeafConditions Comparison₂ Q :=
  h.mono fun _ _ _ _ _ _ _ => ⟨trivial, id⟩
theorem fun0Fit_of_leaves_alt (Fld : FldT) (Comparison₂ : TieT) (hB : _root_.GlobalTheory.BigTop.Fun.BundleCondition) (hS : _root_.GlobalTheory.BigTop.Fun.ScaleCondition) (hE : _root_.GlobalTheory.BigTop.Fun.ExistsFunctionIn Fld Comparison₂) (h1 : _root_.GlobalTheory.BigTop.Fun.LeafMinimalMass Comparison₂) (h2 : _root_.GlobalTheory.BigTop.Fun.LeafUniqueMap Comparison₂)
    (h3 : _root_.GlobalTheory.BigTop.Fun.LeafKernel Comparison₂) (h4 : _root_.GlobalTheory.BigTop.Fun.LeafFixedPoint Comparison₂) (h5 : _root_.GlobalTheory.BigTop.Fun.LeafHeightMapBound Comparison₂) (h6 : _root_.GlobalTheory.BigTop.Fun.LeafInfinitePlaceBound) (h7 : _root_.GlobalTheory.BigTop.Fun.LeafUniqueSquareRoot Comparison₂) (h8 : _root_.GlobalTheory.BigTop.Fun.LeafDensity Comparison₂) (h9 : _root_.GlobalTheory.BigTop.Fun.LeafIntegrality Comparison₂) (h10 : _root_.GlobalTheory.BigTop.Fun.ArchimedeanCondition Comparison₂)
    (h11 : _root_.GlobalTheory.BigTop.Fun.LeafThetaBound Comparison₂) (h12 : _root_.GlobalTheory.BigTop.Fun.LeafWeightBound Comparison₂) (h13 : _root_.GlobalTheory.BigTop.Fun.DescentHeightCondition) (h14 : _root_.GlobalTheory.BigTop.Fun.RankGapBound') (h15 : _root_.GlobalTheory.BigTop.Fun.RamifiedSumBound') (h16 : _root_.GlobalTheory.BigTop.Fun.DescentPolynomialCondition) : _root_.GlobalTheory.BigTop.Fun.ConstantFunctionFits Fld := by
  obtain ⟨a, hA⟩ := _root_.GlobalTheory.BigTop.Fun.LeafConditions.and h1 <| _root_.GlobalTheory.BigTop.Fun.LeafConditions.and h2 <| _root_.GlobalTheory.BigTop.Fun.LeafConditions.and h3 <| _root_.GlobalTheory.BigTop.Fun.LeafConditions.and h4 <| _root_.GlobalTheory.BigTop.Fun.LeafConditions.and h5 <| _root_.GlobalTheory.BigTop.Fun.LeafConditions.and (_root_.GlobalTheory.BigTop.Fun.LeafConditions.of_noTie h6 _) <| _root_.GlobalTheory.BigTop.Fun.LeafConditions.and h7 <|
    _root_.GlobalTheory.BigTop.Fun.LeafConditions.and h8 <| _root_.GlobalTheory.BigTop.Fun.LeafConditions.and h9 <| _root_.GlobalTheory.BigTop.Fun.LeafConditions.and h10 <| _root_.GlobalTheory.BigTop.Fun.LeafConditions.and h11 <| _root_.GlobalTheory.BigTop.Fun.LeafConditions.and h12 <| _root_.GlobalTheory.BigTop.Fun.LeafConditions.and (_root_.GlobalTheory.BigTop.Fun.LeafConditions.of_noTie h13 _) <|
    _root_.GlobalTheory.BigTop.Fun.LeafConditions.and (_root_.GlobalTheory.BigTop.Fun.LeafConditions.of_noTie h14 _) <| _root_.GlobalTheory.BigTop.Fun.LeafConditions.and (_root_.GlobalTheory.BigTop.Fun.LeafConditions.of_noTie h15 _) (_root_.GlobalTheory.BigTop.Fun.LeafConditions.of_noTie h16 _)
  obtain ⟨b, hE⟩ := hE
  refine ⟨max a b, fun CF hCF => (((hA CF (le_of_max_le_left hCF)).and (hE CF (le_of_max_le_right hCF))).and hS).imp
    fun Fm CH _ c hN => ?_⟩
  obtain ⟨C0, c1⟩ := c.1.1 hN
  refine _root_.GlobalTheory.BigTop.Fun.evPt_mono (_root_.GlobalTheory.BigTop.Fun.evPt_and' (_root_.GlobalTheory.BigTop.Fun.evPt_and' (c1 (max C0 1) (le_max_left _ _)) (c.1.2 hN)) c.2) fun x hx i p hp e hG C => ?_
  obtain ⟨⟨e1, e2⟩, s1, s2, s3⟩ := e
  obtain ⟨G, W, g1, g2, g3⟩ := hG
  obtain ⟨d, rfl, hd⟩ := e2 G W g1 g2 g3
  obtain ⟨l1, ⟨ze, z1, z2, l2⟩, l3, ⟨Tf, dF, l4⟩, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15, l16⟩ := e1 d ⟨g2, hd⟩
  obtain ⟨wf, R0, hR⟩ := hB p hp
  have v0 : (d.data ze Tf dF).vmu p.P.A3.fam3.base3.μ0 = d.V p.P.A3.fam3.base3.μ0 := by
    show (ze _)⁻¹ • _ = _
    rw [z1, inv_one]
    exact one_smul _ _
  have v1 : ∀ Tf dF t, (d.data (fun _ => 1) Tf dF).vmu t = d.V t := fun _ _ _ => by
    show (1 : _)⁻¹ • _ = _
    rw [inv_one]
    exact one_smul _ _
  have hRR := R0.RR_spec Formalism.DivisionValues.lattice_gluing wf
  refine functional_lower_bound_of_conditions_numeric wf (p.S false) p.Z C CH (d.data ze Tf dF) (max C0 1) (hR ▸ R0.D_pos) (hR ▸ R0.h0) (hR ▸ R0.l1a)
    (hR ▸ R0.l1c) (hR ▸ R0.frames.1) (hR ▸ hRR.1) (hR ▸ hRR.2) (le_max_right _ _) s1 s2 s3 l1 l2 ?_ ?_ ⟨?_, l6⟩ l7 l8 l9 l10
    l11 l13.1 l13.2 l14 l15.1 l15.2 l12 l16
  · have : LinearMap.ker (d.O.vmu _).mulVecLin = _ := l3
    rw [v1] at this
    show LinearMap.ker ((d.data ze Tf dF).vmu _).mulVecLin = _
    rw [v0]
    exact this
  · have := GlobalTheory.finitePlaceBound_inv_rootOfUnity_smul _ ze _ _ _ z2 l4
    simp only [v1] at this
    exact this
  · intro vb hvb
    exact l5 vb (hvb.trans v0)
end GlobalTheory.BigTop.Fun
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ClassOfRecordOfChoice
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT
namespace Formalism.L2.Top3
theorem tied_families_of_choice_alt {eps : ℝ} {Fm : FamP eps} (s : _root_.Formalism.L2.TwistSelectionFunctions Fm) : _root_.Formalism.L2.SecondChernLinkedClass Fm :=
  ⟨s.1, fun x hx h i => ⟨(s.2 x hx h i).T.toTiedDataS⟩⟩
theorem linkedFamiliesAligned_of_duty {eps : ℝ} {Fm : FamP eps} (s : _root_.Formalism.L2.TwistSelectionFunctions Fm) (h : Duty Fm) : _root_.Formalism.L2.LinkedFamiliesAligned' Fm :=
  ⟨⟨_root_.Formalism.L2.Top3.tied_families_of_choice_alt s, h.1⟩, h.2.2.1, h.2.2.2.1⟩
theorem layerTwoFamilyClass_of_linked_aligned {eps : ℝ} {Fm : FamP eps} (s : _root_.Formalism.L2.TwistSelectionFunctions Fm) (h : _root_.Formalism.L2.LinkedFamiliesAligned' Fm) : _root_.Formalism.L2.SecondLayerFamilyClass Fm :=
  ⟨s.tiedRec, h⟩
abbrev SelectionDefiniteHeightCondition (𝒜 : FamClass) (sel : _root_.Formalism.L2.TwistSelection 𝒜) :=
  ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
    {p : ℕ × ℕ // (Fm.D x i).s.Del = (p.1 : ℚ) ∧ (Fm.L x i).etaSz = ((Fm.D x i).R.m : ℝ) * (p.2 : ℝ)}
section ColChoice
end ColChoice
end Formalism.L2.Top3
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WtBigRun
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
  GlobalTheory.CompHS GlobalTheory.HSApp
namespace GlobalTheory.HSApp
theorem wtBig_run_alt : _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i PP _ => (i : ℕ) + 1 < (Fm.D x ι).R.m →
    WtBig (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)) := by
  obtain ⟨ε1, hε1, H⟩ := GlobalTheory.T.runSizes_quotientGaps_large
  refine ⟨ε1, hε1, fun eps he hle => ?_⟩
  obtain ⟨K, hK⟩ := H eps he hle
  refine ⟨K, fun Fm CH hc hL => ?_⟩
  obtain ⟨x0, hx0⟩ := hK Fm CH hc hL
  refine ⟨0, le_rfl, x0, fun x hx hxx ι p _ i hi => ?_⟩
  obtain ⟨hD1, hDT, hG⟩ := hx0 x hx hxx ι
  obtain ⟨hr, hdim, hgap⟩ := GlobalTheory.T.anchoredWeight_indefiniteLift_gaps p (Fm.params x hx ι) i hi
  have hlen : lenT p i (Fm.parT x hx ι).PP = ⌈(Fm.parT x hx ι).PP ^ 2 *
      (((Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 : ℕ) : ℝ) ^ 2 * ((Fm.D x ι).R.k : ℝ) / ((Fm.D x ι).R.m : ℝ)⌉₊ := by
    rw [lenT, GlobalTheory.CompHS.dimFlag_eq, hdim]
  obtain ⟨hG1, hG2⟩ := hG _ _ rfl hlen
  have hc0 : ((cZero (Fm.D x ι) ((i : ℕ) + 1) : ℤ) : ℝ) ≤ 22 * ((Fm.D x ι).R.f : ℝ) ^ 2 * ((Fm.D x ι).R.r : ℝ) ^ 4 := by
    exact_mod_cast (cZero_spec (Fm.D x ι) ((i : ℕ) + 1)).2.2
  clear H hK hx0 hG
  refine ⟨fun τ k hk => ?_, ?_, ?_⟩
  · rw [WtPar.gap_u₁ _ τ hk, WtPar.gap_uMinus_sub_kap _ τ hk]
    simp only [WtPar.T₁]
    rw [hdim]
    have hGeq : ((Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 3) *
        (((Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 1).choose 2 + 4 * ((dat p i).p + (dat p i).q) +
          (Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 3) =
        ((Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 3) *
        (((Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 1).choose 2 + 4 * (Fm.D x ι).R.r +
          (Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 3) := by rw [hr]
    rw [hGeq]
    have hr2 : (((dat p i).p + (dat p i).q : ℕ) : ℤ) = (Fm.D x ι).R.r := by exact_mod_cast hr
    generalize ((Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 3) *
        (((Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 1).choose 2 + 4 * (Fm.D x ι).R.r +
          (Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 3) = G at hG1 hG2 ⊢
    generalize lenT p i (Fm.parT x hx ι).PP = T at hG1 hG2 ⊢
    generalize (Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 = Dd at hG1 hG2 ⊢
    have hT : (0 : ℤ) < (T : ℤ) + (Dd : ℤ) + 1 := by positivity
    refine Int.le_ediv_of_mul_le hT ?_
    obtain ⟨g1, g2⟩ := hgap τ k hk
    by_cases hb : k + 1 = (dat p i).p
    · rw [if_pos hb, hr2]
      have e := g2 hb
      have : (((G : ℤ) * ((T : ℤ) + (Dd : ℤ) + 1) : ℤ) : ℝ) ≤
          ((gap (uW p i τ) k + (-(cZero (Fm.D x ι) ((i : ℕ) + 1)) - (2 * ((Fm.D x ι).R.r : ℤ) - 2)) : ℤ) : ℝ) := by
        push_cast at hG2 e ⊢
        linarith
      exact_mod_cast this
    · rw [if_neg hb]
      have e := g1 hb
      have : (((G : ℤ) * ((T : ℤ) + (Dd : ℤ) + 1) : ℤ) : ℝ) ≤ ((gap (uW p i τ) k + 2 : ℤ) : ℝ) := by
        push_cast at hG1 e ⊢
        linarith
      exact_mod_cast this
  · show GlobalTheory.FlagTan.dimFlag (dat p i) + 1 ≤ lenT p i (Fm.parT x hx ι).PP
    rw [hdim, hlen]; exact hDT
  · show 1 ≤ GlobalTheory.FlagTan.dimFlag (dat p i)
    rw [hdim]; exact hD1
end GlobalTheory.HSApp
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SmallnessCondition
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ExpFrame
open Formalism.CohomologicalDescent.DepthNonnegative
section Tests
variable (O : Type) [CommRing O] (N : ℕ) {ι : Type} [DecidableEq ι] (lam : ι → ℕ → ℕ) (ϖ : O)
end Tests
end GlobalTheory.ExpFrame
end
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts HidaSetting WInputsLink h0)
open GlobalTheory.ExpFrame
namespace GlobalTheory.ExpTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)
def InRangeAlt (Q : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (_ : Pt Fm x hx i) (_ : Fin (Fm.D x i).R.m) (_ : Par)
    (_ : Wts (Fm.D x i).what₂.Tau), HeightOneSpectrum (𝓞 (Fm.D x i).what₂.LL) → Prop) : Prop :=
  _root_.GlobalTheory.BigOn.AtPtsAlt fun Fm x hx i p => ∀ j (P : Par) (W : Wts (Fm.D x i).what₂.Tau), Dict (Fm.L x i) j P W → NumOk P W →
    ∀ w ∈ p.R.twPl, W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → Q Fm x hx i p j P W w
def FrameStatement' : Prop := _root_.GlobalTheory.ExpTie.InRangeAlt fun _ _ _ _ p j P W w => FrameAt p j P W w
def GaloisStatement : Prop := _root_.GlobalTheory.ExpTie.InRangeAlt fun _ _ _ _ p j P W w => GalAt p j P W w
def SmallnessCondition : Prop := _root_.GlobalTheory.ExpTie.InRangeAlt fun _ _ _ _ p j P _ w => SmallAt p j P w
end GlobalTheory.ExpTie
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ShareWSt
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
namespace GlobalTheory.ShareOn
section Model
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {U C : Type} [Group U] [MulAction U C]
end Model
section Point
open Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
end Point
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigOn
def ModelStatement : Prop := _root_.GlobalTheory.BigOn.ForallTwoRuns fun Fm x hx ι p _ _ => ∀ i, ModelAt p i (Fm.parT x hx ι).TO
def SharedWeightStatement : Prop := _root_.GlobalTheory.BigOn.ForallTwoRuns fun Fm x _ ι p _ _ => ∀ i,
  ShareW p i (1 / (4 * (((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.k) ^ 3))
def BadWeightStatement : Prop := _root_.GlobalTheory.BigOn.ForallTwoRuns fun Fm x _ ι p _ _ => ∀ i,
  BadW p i (Real.exp (-((Fm.L x ι).sc.x ^ ((Fm.L x ι).sc.ez / 7))))
end GlobalTheory.ShareOn
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamAllQ
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeSaw GlobalTheory.Fam
namespace GlobalTheory.MiTop
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
def qPrime_alt (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (t : W.P.T) (p : ℕ) : Prop := ∃ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t, ((p : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal
def FamilyRatioCondition {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : D.what₂.Word} (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) : Prop :=
  ∀ n, 2 * n = D.R.m → ∀ t, (f.t t).cTop n ≠ 0 ∧ UnitRatio (_root_.GlobalTheory.MiTop.qPrime_alt W t) ((f.t t).cTop n / (f.t t).cBot)
    ((f.t W.P.A3.A.μ0).cTop n / (f.t W.P.A3.A.μ0).cBot)
def FamilyServedCondition (W : _root_.GlobalTheory.MiS.RealPackAlt ex) : Prop :=
  ∀ w (p : ℕ), p.Prime → _root_.GlobalTheory.MiTop.qPrime_alt W (W.Q.Rl.mu w) p → (p : 𝓞 D.what₂.LL) ∉ w.asIdeal
def FamilyAllConditions (W : _root_.GlobalTheory.MiS.RealPackAlt ex) : Prop :=
  ∃ z ∈ GfC (D.sp.Y 0), z ∈ Subgroup.center (GA D (D.sp.Y 0)) ∧ ∀ u, ∃ (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (d : _root_.GlobalTheory.MiTop.BottomData W u),
    d.Pin z ∧ LawsX f.t ∧ _root_.GlobalTheory.MiTop.LinkVanishes f d ∧ _root_.GlobalTheory.MiTop.LinkTailCondition f ∧ _root_.GlobalTheory.MiTop.LinkDescends f ∧ _root_.GlobalTheory.MiTop.LinkSurjective f ∧ _root_.GlobalTheory.MiTop.LinkCommutes f ∧ _root_.GlobalTheory.MiTop.FamilyRatioCondition f
end GlobalTheory.MiTop
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ModelStatement
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts HidaSetting WInputsLink h0)
namespace GlobalTheory.ExpTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7}
section Point
variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)
end Point
def NumStAlt : Prop := _root_.GlobalTheory.BigOn.AtPtsAlt fun Fm x _ i _ => ∀ j, ∃ (P : Par) (W : Wts (Fm.D x i).what₂.Tau), Dict (Fm.L x i) j P W ∧ NumOk P W
open Classical in
def ExponentSumStatement : Prop := _root_.GlobalTheory.BigOn.AtPtsAlt fun Fm x _ i p => ∀ j (P : Par) (W : Wts (Fm.D x i).what₂.Tau), Dict (Fm.L x i) j P W → NumOk P W →
  ∀ t w, LIncl (blk p j t) (lvlL p) (subZ p j t) w (W.JA P (Formalism.EigenvalueLevelCeiling.plc w))
def ModelStatement : Prop := _root_.GlobalTheory.BigOn.AtPtsAlt fun Fm x _ i p => ∀ j (P : Par) (W : Wts (Fm.D x i).what₂.Tau), Dict (Fm.L x i) j P W → NumOk P W →
  ∀ w ∈ p.R.twPl, W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → ModelAt p j P W w
end GlobalTheory.ExpTie
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GVec
set_option synthInstance.maxHeartbeats 200000

section
set_option genSizeOfSpec false
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : D.what₂.Word} (f : _root_.GlobalTheory.Fam.FamilyCharacter W u)
structure QLevAlt {v : VCom f.c} {t : W.P.T} (F : GlobalTheory.QPl.QFam v (f.t t)) : Prop where
  places : ∃ pl : Fin F.r ≃ (_root_.GlobalTheory.Fam.pk_z W).Q t, ∀ i, Formalism.L2.NTheta.IsIdemAt (F.Q i).q.e (pl i).1 ∧ (F.Q i).q.v = (pl i).1.under (𝓞 D.host.F)
  mid : ∀ i j d hd, j < D.R.m → ∀ x ∈ KO (F.Q i).k _,
    ((f.g.b j)⁻¹ * (F.Q i).gl j d hd x * f.g.b j ∈ levS _ ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)) ↔ x ∈ ((F.Q i).T.lev j d hd).J) ∧
    ∀ hx : x ∈ ((F.Q i).T.lev j d hd).J, levChi _ ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W))
      ((f.g.b j)⁻¹ * (F.Q i).gl j d hd x * f.g.b j) = (((F.Q i).T.lev j d hd).lam ⟨x, hx⟩ : ℂ)
  top : ∀ i, ∀ x ∈ KO (F.Q i).k _, ∀ g, (ofSplit (F.Q i).q).IsLoc (F.Q i).FT g x →
    (f.g.bT⁻¹ * g * f.g.bT ∈ levS _ (_root_.GlobalTheory.Fam.pk_z W).βX (datXP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) t) ↔ x ∈ (F.Q i).T.levTop.J)
def VectorFunctionCondition (v : VCom f.c) {t : W.P.T} (w : VTup (f.t t)) (sc : ℕ → ℂ) : Prop :=
  (∀ j, j + 1 < D.R.m → ∀ P, ∀ a ∈ GinfC _, ∀ a' ∈ GinfC _, (f.t t).om j (a * v.b j, a' * v.b (j + 1)) ((f.t t).pt j P) =
    sc j • comb f.c.ψ _ _ (v.eG j) (comb f.c.ψ _ _ (w.eQ j) (v.Ψ j P a a'))) ∧
  ∀ j h P, (f.t t).omT j h (v.b (j + 1), v.bT) ((f.t t).ptT j h P) =
    sc (j + 1) • comb f.c.ψ _ _ (v.eGT j h) (comb f.c.ψ _ _ (w.eQT j h) (v.ΨT j h P))
def GVectorCondition (v : VCom f.c) (s : ℕ → ℂ) : Prop :=
  (∀ j, j + 1 < D.R.m → ∀ d, _root_.GlobalTheory.Fam.IsDivisorGlobal W j ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j) d → ∀ P, ∀ a ∈ GinfC _,
    ∀ a' ∈ GinfC _, (_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (a * f.g.b j, a' * f.g.b (j + 1)) (comb f.c.ψ _ _ d (pureTensorO f.c.ψ f.c.θ (Yc D j)
      (Yc D (j + 1)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) ((_root_.GlobalTheory.Fam.pk_z W).vac j) P)) =
      s j • comb f.c.ψ _ _ (v.eG j) (v.Ψ j P a a')) ∧
  ∀ j h d, _root_.GlobalTheory.Fam.IsDivisorGlobal W (j + 1) (_root_.GlobalTheory.Fam.pk_z W).MX (_root_.GlobalTheory.Fam.pk_z W).ΛX (_root_.GlobalTheory.Fam.pk_z W).βX (vacT (_root_.GlobalTheory.Fam.pk_z W) j h) d → ∀ P,
    omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (comb f.c.ψ _ _ d (pureTensorO f.c.ψ f.c.θ (Yc D (j + 1)) D.sp.X'
      (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (cart (_root_.GlobalTheory.Fam.pk_z W).MX) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb (_root_.GlobalTheory.Fam.pk_z W).MX) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h) P)) =
      s (j + 1) • comb f.c.ψ _ _ (v.eGT j h) (v.ΨT j h P)
end GlobalTheory.Fam
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EvWCOnPtOfGuarded
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EvWCOnPtOfGuarded
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Fc GlobalTheory.Fc.Ind GlobalTheory.BigTop
namespace GlobalTheory.Fc.Ind
theorem evWC_onPt_of_guarded_alt (prem : ∀ {eps : ℝ}, FamP eps → Prop) (G : PtP) (T : ℝ → ℝ → PtP)
    (h : Closed FamHyp fun Fm CH => prem Fm → ∃ C0 : ℝ, 0 ≤ C0 ∧ _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun x hx i p =>
      G _ (objAt Fm x hx i) _ p → ∀ C, C0 ≤ C → T C CH _ (objAt Fm x hx i) _ p)
    (𝒜 : FamClass) (σ : RawSel _root_.GlobalTheory.Fc.Ind.PointSummands 𝒜) (hd : ∀ (eps : ℝ) (Fm : FamP eps), 𝒜 Fm → GlobalTheory.EX.DQ.Duty7 Fm)
    (hR : EvW _root_.GlobalTheory.Fc.Ind.RowPointSummands 𝒜 σ) (hG : EvW (_root_.GlobalTheory.Fc.Ind.conditionOnPoint G) 𝒜 σ) : EvWC prem (fun C CH => _root_.GlobalTheory.Fc.Ind.conditionOnPoint (T C CH)) 𝒜 σ := by
  have h' : Closed (W3 𝒜) fun Fm CH => prem Fm → ∃ C0 : ℝ, 0 ≤ C0 ∧ _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun x hx i p =>
      G _ (objAt Fm x hx i) _ p → ∀ C, C0 ≤ C → T C CH _ (objAt Fm x hx i) _ p := by
    obtain ⟨a, ha, h⟩ := h
    refine ⟨a, ha, fun e he hle => ?_⟩
    obtain ⟨K, hK⟩ := h e he hle
    exact ⟨K, fun Fm CH hc hL => hK Fm CH (GlobalTheory.T.familyHypotheses_of_workingClass_sevenDuties 𝒜 _ Fm hc (hd _ Fm (w3_a hc))) hL⟩
  refine Closed.imp (Closed.and h' (Closed.and hR hG)) ?_
  rintro eps Fm CH - ⟨h1, h2, h3⟩ hc hp
  obtain ⟨C0, hC0, a, ha⟩ := h1 hp
  obtain ⟨b, hb⟩ := h2 hc
  obtain ⟨c, hc'⟩ := h3 hc
  refine ⟨C0, hC0, fun C hC => ⟨max a (max b c), fun x hx hle i => ?_⟩⟩
  have e1 : a ≤ x := (le_max_left _ _).trans hle
  have e2 : b ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hle
  have e3 : c ≤ x := ((le_max_right _ _).trans (le_max_right _ _)).trans hle
  exact ha x hx e1 i (σ Fm (w3_a hc) x hx i).pt (hb x hx e2 i) (hc' x hx e3 i) C hC
end GlobalTheory.Fc.Ind
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EvWCOnPtOfGuardedStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Fc GlobalTheory.Fc.Ind GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_onPt_of_pDiv_ties_and_onPt : ∀ (prem : ∀ {eps : ℝ}, FamP eps → Prop) (G : PtP) (T : ℝ → ℝ → PtP), (Closed FamHyp fun Fm CH => prem Fm → ∃ C0 : ℝ, 0 ≤ C0 ∧ _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun x hx i p => G _ (objAt Fm x hx i) _ p → ∀ C, C0 ≤ C → T C CH _ (objAt Fm x hx i) _ p) → ∀ (𝒜 : FamClass) (σ : RawSel _root_.GlobalTheory.Fc.Ind.PointSummands 𝒜), (∀ (eps : ℝ) (Fm : FamP eps), 𝒜 Fm → GlobalTheory.EX.DQ.Duty7 Fm) → EvW _root_.GlobalTheory.Fc.Ind.RowPointSummands 𝒜 σ → EvW (_root_.GlobalTheory.Fc.Ind.conditionOnPoint G) 𝒜 σ → EvWC prem (fun C CH => _root_.GlobalTheory.Fc.Ind.conditionOnPoint (T C CH)) 𝒜 σ := by
  first | exact @_root_.GlobalTheory.Fc.Ind.evWC_onPt_of_guarded_alt | exact _root_.GlobalTheory.Fc.Ind.evWC_onPt_of_guarded_alt | (intros; apply _root_.GlobalTheory.Fc.Ind.evWC_onPt_of_guarded_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RatHyp0AtPoint
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RatHyp0AtPoint
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.BigOn GlobalTheory.BigOn.Exp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn.Exp
theorem ratHyp0_at_point_alt : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (p : Pt Fm x hx i), p.PointConditions' → More p →
  ∀ t : (Fm.D x i).ntw.Tw, (Fm.D x i).ntw.NonzeroIndexPlace t →
  (∀ P : Pl (Fm.D x i).host.E, (((Fm.D x i).host.QS * (Fm.D x i).host.q * Ideal.absNorm (Fm.D x i).host.ccK * ((Fm.D x i).host.g 0 * (Fm.D x i).host.g 1 *
    (Fm.D x i).host.pde * (Fm.D x i).host.pde') : ℕ) : 𝓞 (Fm.D x i).host.E) ∈ P.asIdeal → P ∈ (Fm.D x i).ntw.S0 t) →
  ∀ j : Fin (Fm.D x i).R.m, RatHyp0 p.T p.R (F2 p) p.κ p.v₀ p.O t j := by
  intro eps Fm x hx i p hp hM t ht hlow j
  obtain ⟨hc, -, hu, -⟩ := _root_.GlobalTheory.T.links2_of_single_index_twisted _ _ _ _ _ _ _ _ _ _ p hp hM.1
  have hTie : TieIn p.T p.R.toRealDat p.κ p.v₀ :=
    ⟨p.fw.laws, p.fw.alg_eq, p.fw.kap, p.fw.hv₀, p.fw.chiR, p.fw.x0⟩
  exact
    { size := (Fm.parT x hx i).nV_ge
      host := p.host
      std := GlobalTheory.StdFrame.vStd_of_orthonormal_span _ j (p.stdV j)
      laws := p.fw.laws
      core :=
        { lev := hc.lev
          grp := ⟨hc.grp.red_R, hc.grp.red_L, hc.grp.levels, hc.grp.record, hc.grp.chiW⟩
          fam := ⟨hc.fam.tie, hc.fam.Sb, hc.fam.roots, hc.fam.pl_onto, hc.fam.degR, hc.fam.degL, hc.fam.muVal, hc.fam.etaVal⟩
          models := ⟨hc.models.inf, hc.models.vpos, hc.models.cX, hc.models.cV, hc.models.prX, hc.models.HX, hc.models.HV,
            hc.models.HE, hc.models.HW, hc.models.gE, hc.models.gW, hc.models.jX, hc.models.jV, hc.models.νY, hc.models.νY',
            hc.models.ν0, hc.models.νX, hc.models.νV, hc.models.νW, hc.models.BV, hc.models.order⟩
          chain := ⟨hc.chain.ωY, hc.chain.ωX, hc.chain.vY, hc.chain.vX, hc.chain.ptY, hc.chain.ptX, hc.chain.ItY, hc.chain.ItX,
            hc.chain.ioY, hc.chain.ioX, hc.chain.Th⟩
          thP := ⟨hc.thP.ωP, hc.thP.vP, hc.thP.pt_theta, hc.thP.ioP, hc.thP.thF_mem, hc.thP.thF, hc.thP.thG⟩ }
      unif := hu
      fw := ⟨p.fw⟩
      tieIn := hTie
      io := hp.ioExt
      guard := p.qGuard
      fin := GlobalTheory.BigOn.Check.finite_tuples_of_indefiniteSidePoint p
      pins := p.pins j
      phase := p.phase j hu
      galois := (Fm.ties x i).baseField_isGalois
      small := hM.2.2.small
      inUse := ht
      low := hlow }
end GlobalTheory.BigOn.Exp
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RatHyp0AtPointStatement
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.BigOn GlobalTheory.BigOn.Exp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ratHyp0_of_bad_prime_mem_S0 : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (p : Pt Fm x hx i), p.PointConditions' → More p →
  ∀ t : (Fm.D x i).ntw.Tw, (Fm.D x i).ntw.NonzeroIndexPlace t →
  (∀ P : Pl (Fm.D x i).host.E, (((Fm.D x i).host.QS * (Fm.D x i).host.q * Ideal.absNorm (Fm.D x i).host.ccK * ((Fm.D x i).host.g 0 * (Fm.D x i).host.g 1 *
    (Fm.D x i).host.pde * (Fm.D x i).host.pde') : ℕ) : 𝓞 (Fm.D x i).host.E) ∈ P.asIdeal → P ∈ (Fm.D x i).ntw.S0 t) →
  ∀ j : Fin (Fm.D x i).R.m, RatHyp0 p.T p.R (F2 p) p.κ p.v₀ p.O t j := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.ratHyp0_at_point_alt | exact _root_.GlobalTheory.BigOn.Exp.ratHyp0_at_point_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.ratHyp0_at_point_alt <;> assumption)
end
end
end
