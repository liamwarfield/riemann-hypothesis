module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColJoinSOfSTiesR
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsMoreExtra
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTied
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualFramesNormalAtLevelPlacesOfCharFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SizeParametersNonempty
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationEveryEmbeddingThirdKind
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRowPlacementFiniteElementMatchesLevels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarCoeffEisensteinSeriesReversePoly

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped InnerProductSpace
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx
  Formalism.IndefR.Links Formalism.L2.SG.PackageTie2 Formalism.L2.SG.KerJoinS Formalism.IndefR.CxPass
namespace GlobalTheory.MiS
open _root_.Formalism _root_.Formalism.IndefR _root_.Formalism.IndefR.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC}
structure RealPackAlt (ex : Extra D L hT Gi Gl Kc Yd cX) where
  R : _root_.Formalism.L2.RecTAlt ex
  S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R
  P : RowSideFamily ex
  Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)
  Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)
  Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3
  Ks : Type
  [fKs : Field Ks]
  [nKs : NumberField Ks]
  [aKs : Algebra Ks D.what₂.LL]
  Q : _root_.Formalism.IndefR.IndefiniteRealisation R P Dcf Spf Zscf S Ks
attribute [instance] _root_.GlobalTheory.MiS.RealPackAlt.fKs _root_.GlobalTheory.MiS.RealPackAlt.nKs _root_.GlobalTheory.MiS.RealPackAlt.aKs
variable {ex : Extra D L hT Gi Gl Kc Yd cX}
def HypothesisAtPackage (W : _root_.GlobalTheory.MiS.RealPackAlt ex) : Prop :=
  Nonempty (_root_.Formalism.L2.SG.JoinSI.IndefiniteRealisationJoin W.R W.S W.Q) ∧
    (∀ u, Formalism.L2.SG.ColDict.LevelMatch W.S.X (W.S.tr u) W.S.Y.hK) ∧ DcPtG W.P ∧ W.Q.Rl.Char3 W.Q.F ∧ FramesOKg2 W.Q.Rl
abbrev packageCoefficientSpace (W : _root_.GlobalTheory.MiS.RealPackAlt ex) := W.Q.Rl.toCx3 W.Q.F
def LevelHypothesis (W : _root_.GlobalTheory.MiS.RealPackAlt ex) : Prop :=
  (∃ s, W.P.A3.fam3.Ok3 s) ∧ (_root_.GlobalTheory.MiS.packageCoefficientSpace W).RatZ ∧
    ∃ gE : Representation ℂ W.P.Gp (_root_.GlobalTheory.MiS.packageCoefficientSpace W).EE, GUnit3 (_root_.GlobalTheory.MiS.packageCoefficientSpace W) gE ∧ GEquiv3 W.P.A3 (_root_.GlobalTheory.MiS.packageCoefficientSpace W) gE ∧
      PrincipalLevelBijectivity W.P.A3 (_root_.GlobalTheory.MiS.packageCoefficientSpace W) (P1 := W.P.Ps) (ψ1 := W.P.ψs) (Dc := W.Dcf) (Sp := W.Spf) (Zsc := W.Zscf) ∧
      LevType3 W.P.A3 (_root_.GlobalTheory.MiS.packageCoefficientSpace W) (P1 := W.P.Ps) (ψ1 := W.P.ψs) (Dc := W.Dcf) (Sp := W.Spf) (Zsc := W.Zscf) gE false W.P.P0 W.P.ψ0 ∧
      LevType3 W.P.A3 (_root_.GlobalTheory.MiS.packageCoefficientSpace W) (P1 := W.P.Ps) (ψ1 := W.P.ψs) (Dc := W.Dcf) (Sp := W.Spf) (Zsc := W.Zscf) gE true W.P.Ps W.P.ψs
end GlobalTheory.MiS
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealRecOf
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
namespace GlobalTheory.Mem.R3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {K : Formalism.MainNotions.G.Consts} {Yd : DivX D}
  {cX : ExtraC}
variable {ex : Extra D L hT Gi Gl K Yd cX}
set_option genInjectivity false in
set_option genSizeOfSpec false in
set_option maxHeartbeats 4000000 in
structure RealInAlt (x : TwIn ex) (Rc : _root_.Formalism.L2.RecTAlt ex) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) : Type 1 where
  psiPin : x.R.ψ = Rc.T.theta.W.ψ
  hin : ∀ u, Formalism.L2.SG.PoincareInHH.PoincareSetting.InHH S.X u S.Y.hK
  spPin : HEq (x.F.Sp (zsOf x.R x.F)) (Formalism.IndefR.Cx.spOf (X := S.X) (twAt D.what₂.embLL x.A3.A.v0) (x.F.Dc (zsOf x.R x.F)) S.Y.hK S.G
    x.wd (fun m => _root_.Formalism.IndefR.pwOf_alt S hin (x.wd m)) x.bR)
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
variable {x : TwIn ex} {Rc : _root_.Formalism.L2.RecTAlt ex} {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc}
set_option maxHeartbeats 4000000 in
def realisationOfInput (y : _root_.GlobalTheory.Mem.R3.RealInAlt x Rc S) : _root_.Formalism.IndefR.IndefiniteRealisation Rc (divisionPairOfAdelicFormsFaceColumnsData x) x.F.Dc x.F.Sp x.F.Zsc S x.core.Q.c.F where
  Rl := x.R
  sEE := x.sEE
  charW := (x.pins.char)
  zs := rfl
  s0 := (HEq.refl (s0Of x.R x.F))
  s1 := (HEq.refl (s1Of x.R x.F))
  dc := rfl
  sp := HEq.rfl
  col := (HEq.refl (colOf x.R x.F x.sEE))
  allPlaces := x.pins.char.allPl
  trSem := (x.pins.trSem)
  stdChar := x.pins.keep.std
  psiPin := y.psiPin
  signs := (x.pins.keep.signs)
  wdD := x.wd
  wdD_wU := x.wd_wU
  wU_wdD := x.wU_wd
  hin := y.hin
  bR := x.bR
  spPin := (y.spPin)
  frames := fun h => (Formalism.IndefR.Seed.Frm.framesOKg2_iff x.R).2 (x.pins.keep.frames h)
  cG := x.cG
  Sx := y.Sx
  nexp := y.nexp
  stdV := y.stdV
  stdX := y.stdX
  tS := y.tS
  cS := y.cS
  κS := y.κS
  ιS := y.ιS
  instEq := y.instEq
  ιS_eq := y.ιS_eq
  sEEc := y.sEEc
  sEEj := y.sEEj
  seeLev := (y.seeLev)
  seeEval := (y.seeEval)
  uS := y.uS
  uS_norm := y.uS_norm
  seeDef := (y.seeDef)
  seeK := (y.seeK)
  host := y.host
  err_eq := (x.err)
  vpos := y.vpos
set_option maxHeartbeats 4000000 in
def boundedRealisationOfInput (y : _root_.GlobalTheory.Mem.R3.RealInAlt x Rc S) : _root_.Formalism.IndefR.RealTBAlt Rc (divisionPairOfAdelicFormsFaceColumnsData x) x.F.Dc x.F.Sp x.F.Zsc S where
  T := x.core
  Q := _root_.GlobalTheory.Mem.R3.realisationOfInput y
  κ := x.geo.κ
  v₀ := (x.geo.v₀)
  fw := (x.geo.fw)
  bar := (x.geo.bar)
  O := (x.geo.O)
  pins := (x.geo.pins)
  rhoGeo := (x.geo.rhoGeo)
  equivAll := (x.geo.equivAll)
  cTie := (x.geo.cTie)
  phase := by
    have h : ∀ i, x.R.toRealDat.LUnif →
        Formalism.IndefR.FWT.PhaseTie x.core x.R.toRealDat x.geo.κ x.geo.v₀ x.geo.O (phEff x.R) i := by
      rw [phEff_one x]
      exact x.geo.phase
    exact (h)
set_option genInjectivity false in
set_option genSizeOfSpec false in
set_option maxHeartbeats 4000000 in
structure RecursiveInput (y : _root_.GlobalTheory.Mem.R3.RealInAlt x Rc S) : Type 1 where
  E : EigIdx D Yd
  labPi : E.Pi → x.A3.A.fam.base.Ix
  piOf : E.Pi → HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ
  Tp : Formalism.L2.Host.TupTied D x.R.C ex.nch
  tpEq : HEq Tp Rc.T.n.tp
  tupXi : ∀ μ, Formalism.IndefR.RecTie.Used0 D μ → x.R.toLevCh.xiH (x.Y.tupT μ) = Tp.xi μ
  mtRead : Formalism.IndefR.RecTie.MtRead x.R.toRealDat x.F.lv2 x.Y.tupT x.Y.hm x.Y.hTop x.Y.hinj x.Y.IL
    (twPOf (divisionPairOfAdelicFormsFaceColumnsData x) x.Y.tupT x.Y.tupTie)
  mjRead : Formalism.IndefR.RecTie.MjRead x.R.toRealDat x.F.lv2 x.Y.tupT x.Y.hm x.Y.hTop x.Y.hinj x.Y.IL
    (fun i => (x.A3.indefDown (s0Of x.R x.F)).dW i) (fun i v => x.Z.jW i v) ((indefiniteDownJoin (realisationOfInput y)))
set_option maxHeartbeats 4000000 in
def realisationRecursionOfInput {y : _root_.GlobalTheory.Mem.R3.RealInAlt x Rc S} (r : _root_.GlobalTheory.Mem.R3.RecursiveInput y) : _root_.Formalism.IndefR.IndefiniteRealisationRecursion (_root_.GlobalTheory.Mem.R3.realisationOfInput y) where
  tupT := x.Y.tupT
  hm := x.Y.hm
  hTop := x.Y.hTop
  hinj := x.Y.hinj
  Ish := (x.Y.Ish)
  I0 := (x.Y.Iz)
  IL := (x.Y.IL)
  Kc := x.Y.Kc
  E := r.E
  labPi := r.labPi
  PY := x.Y.PY
  PW := x.Y.PW
  eFT := (x.Y.eFT)
  piOf := r.piOf
  ιW := x.Y.ιW
  Tp := (r.Tp)
  recR := by
    have h : Formalism.IndefR.RecTie.RecReal x.R.toRealDat x.F.lv2 x.Y.tupT x.Y.hm x.Y.hTop x.Y.hinj ex.p0 x.Y.Ish x.Y.Iz x.Y.IL x.Y.Kc r.E
        r.labPi x.Y.PY x.Y.PW x.Y.eFT r.piOf x.Y.ιW ex.nch r.Tp :=
      ⟨x.pins.char.base, x.Y.tied, x.Y.prtE, x.Y.prtE0, x.Y.prtWE, x.Y.xi, r.tupXi,
        fun w => by rw [x.Y.muAt w, x.Y.tupT_tup], x.Y.isomFin, x.Y.frameMatch⟩
    exact (h)
  tpEq := (r.tpEq)
  tupTie := x.Y.tupTie
  tupT_tup := x.Y.tupT_tup
  muEq := (Eq.refl x.R.mu)
  mtRead := (r.mtRead)
  mjRead := (r.mjRead)
end GlobalTheory.Mem.R3
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SelSideRT
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
namespace Formalism.L2
section
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}
open Classical in
structure SelectedSideOfRealRecord (R : _root_.Formalism.L2.RecTAlt ex) (P : Rows.RowSideFamily ex)
    {Dcf : ∀ Zs : Indef.DefSub P.A3.fam3.amb3, Indef.DefCols (P.A3.side3 P.Ps P.ψs Zs)}
    {Spf : ∀ Zs : Indef.DefSub P.A3.fam3.amb3, Indef.SPer (Dcf Zs)}
    {Zscf : Indef.DefSub P.A3.fam3.amb3 → Indef.IndefScale P.A3.fam3.base3}
    {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (RT : _root_.Formalism.IndefR.IndefiniteRealisation R P Dcf Spf Zscf S Ks) (Qr : _root_.Formalism.IndefR.IndefiniteRealisationRecursion RT) (hd : _root_.Formalism.L2.HostDatumWithTies R.T.toTiedDataS)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → HeightOneSpectrum (𝓞 D.host.E)) : Prop where
  sel : _root_.Formalism.L2.SelectedSideOfPrimeAbove R Pq
  twQ : ∀ μ : D.what₂.Tup, (μ = D.what₂.mu0 ∨ ∃ w, μ = D.what₂.muAt w) →
    (Col.QE R.T.ker.sel (R.T.ker.tup μ : DIV.Chr R.T.ker.X.F R.T.ker.X.E R.T.ker.X.K)).image
      (Host.CT.plMap R.T.ker.seam.iE) = RT.Rl.Q (Qr.tupT μ)
  de : ∀ v, ((D.host.pde : ℕ) : 𝓞 D.host.E) ∈ (Pq v).asIdeal → (Pq v).under (𝓞 D.host.K) = hd.d3b.pK
  de' : ∀ v, ((D.host.pde' : ℕ) : 𝓞 D.host.E) ∈ (Pq v).asIdeal → (Pq v).under (𝓞 D.host.K) = hd.d3b.pK'
end
end Formalism.L2
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtMemberImp
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.HeightCounting.Up.Model
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N _root_.Formalism.L2 _root_.Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting
  GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists}
theorem AtMem.at_member_imp {p q : _root_.GlobalTheory.HeightCounting.Up.LayPAlt hL} (h : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL p)
    (hpq : ∀ K B f T w Z Wt p0 t nch n c, p K B f T w Z Wt p0 t nch n c → q K B f T w Z Wt p0 t nch n c) : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL q :=
  EvG.imp h fun _ _ _ _ _ hK => large₂.imp hK fun B f T _ H kp w Z Wt p0 t nch n xd c a b d =>
    hpq _ B f T w Z Wt p0 t nch n c (H kp w Z Wt p0 t nch n xd c a b d)
theorem AtMem.and_z {p q : _root_.GlobalTheory.HeightCounting.Up.LayPAlt hL} (h : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL p) (h' : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL q) :
    _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun K B f T w Z Wt p0 t nch n c => p K B f T w Z Wt p0 t nch n c ∧ q K B f T w Z Wt p0 t nch n c :=
  EvG.imp (EvG.inter h h') fun _ _ _ _ _ hK => large₂.imp (large₂.inter hK.1 hK.2) fun _ _ _ _ H kp w Z Wt p0 t nch n xd c a b d =>
    ⟨H.1 kp w Z Wt p0 t nch n xd c a b d, H.2 kp w Z Wt p0 t nch n xd c a b d⟩
end GlobalTheory.HeightCounting.Up.Model
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealRecPins
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR.Links Formalism.IndefR.Cx
namespace Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}
variable {Rc : _root_.Formalism.L2.RecTAlt ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
  {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
structure IndefiniteRealisationCompatible {Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks} (Qp : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation Q) (Qr : _root_.Formalism.IndefR.IndefiniteRealisationRecursion Q) : Prop where
  stdPsi : Formalism.IndefR.principalLevelFrame.StdPsi Qp.hF Qr.PY ∧ ∀ i, Formalism.IndefR.principalLevelFrame.StdPsi Qp.hF (Qr.PW i)
  rowLoc : _root_.Formalism.IndefR.principalLevelFrame.RowLocPinAlt Rc.T.n.gal.lp Q.Rl.θ Qr.PY (Q.Rl.MY 0)
    (fun b => levS _ (Q.Rl.βY 0) (Q.Rl.dat0 (Q.Rl.toRealDat.levR Q.F.lv2 b)))
    (fun b => Formalism.IndefR.Lev.levChi _ (Q.Rl.βY 0) (Q.Rl.dat0 (Q.Rl.toRealDat.levR Q.F.lv2 b))) (fun _ => Q.Rl.e0) Qr.eFT
end Formalism.IndefR
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.JumpsCardOfBuilt
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
noncomputable section
namespace GlobalTheory.HeightCounting.JumpsAt
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem jumpsCard_of_built_alt (hH : HtCard) {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D' : D7} (b : _root_.GlobalTheory.HeightCounting.NormChoiceConstructed hL D')
    (fr : OmFrame b.D) (hp : PhtOn b.A.wd fr fun _ _ _ _ => True) : JumpsCard D'.nd D'.naut := by
  obtain ⟨D, cf, jE, A, cg, au, rep, row, low, Pq, S, hL', eig, θ, Bs, M, C, tp, ch, mt, big, L, Sp, Au, ss, rfl⟩ := b
  intro i a r w τ hw hτ hdR
  have hdA := ((Au.wdOf i a r w).2.2.2.1).mp hdR
  have e1 := (Au.wdOf i a r w).2.2.2.2 τ
  haveI : Fact (L.X.nd.l i).Prime := L.X.nd.lPrime i
  have e2 := hp.card _ (L.Y.naut.iotaQC i) a r τ w trivial (fun x => (hτ x).symm) hdA
  show Multiset.card (L.Y.jumpsW i r τ) = a
  rw [e1, e2]
theorem jumpsCard_at_members_of_htCard : HtCard → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists,
    _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ _ _ _ _ => JumpsCard (w.D Z).nd (w.D Z).naut := by
  intro hH hL
  refine evLgG_of_forall fun K B f T _ w Z Wt p0 t nch n xd c hE _ _ => ?_
  obtain ⟨e⟩ := hE
  obtain ⟨fr, -, hp⟩ := (e : _root_.GlobalTheory.HeightCounting.RealExpansionExtraData (D := (w.st Z).toD7) c.row t.r.z.geo xd).pht
  exact _root_.GlobalTheory.HeightCounting.JumpsAt.jumpsCard_of_built_alt hH c.a.nt.toNBuilt fr hp
end GlobalTheory.HeightCounting.JumpsAt
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.JoinPin
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.Indef Formalism.L2.DIV Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links Formalism.IndefR.Mult
  Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.Lev Formalism.L2.Theta NumberField MeasureTheory Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.RowDict Formalism.L2.SG.ColDict
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Mem.JTop
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
  {R : _root_.Formalism.L2.RecTAlt ex} {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R} {P : RowSideFamily ex}
  {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)} {Spf : ∀ Zs, SPer (Dcf Zs)}
  {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
def JoinPinAlt (Q : _root_.Formalism.IndefR.IndefiniteRealisation R P Dcf Spf Zscf S Ks) : Prop :=
  ∃ eE : D.what₂.EE →ₗ[ℂ] Q.Rl.HE.H,
    (∀ y y', HEq y y' → eE (D.jEE (P.I.eRR y)) =
      Tw.out (s := Formalism.L2.SG.JoinSI.twQ P) (E := Q.Rl.HE.H)
        ((_root_.Formalism.L2.SG.JoinSI.complexRealisationJoinData Q).iC Q.F.cr true P.A3.A.μ0 (cpt P.A3.A.v0.embedding y'))) ∧
    ∀ hF : Formalism.L2.SG.PackageTie2.FinX S.Y, GlobalTheory.Mem.SRe.RowJ Q.Rl.toRealDat eE S.X S.inst S.G Q.tS (_root_.Formalism.L2.SG.JoinSI.spectralRowIsometry S hF)
theorem bR_heq_eMu_single (Q : _root_.Formalism.IndefR.IndefiniteRealisation R P Dcf Spf Zscf S Ks) (hPin : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation Q) (u : D.what₂.Word) (i : Fin (P.Dc.a (P.I.wU u))) :
    HEq (Q.bR (P.I.wU u) i) (D.eMu u (D.jN u (P.I.eNu u (Pi.single i 1)))) := by
  refine HEq.trans (heq_of_eq (hPin.bR_read (P.I.wU u) i)) ?_
  have key : ∀ (w : D.what₂.Word) (hw : w = u) (hc : P.Dc.a (P.I.wU u) = P.Dc.a (P.I.wU w)),
      HEq (D.eMu w (D.jN w (P.I.eNu w (Pi.single (Fin.cast hc i) 1))))
        (D.eMu u (D.jN u (P.I.eNu u (Pi.single i 1)))) := by
    intro w hw hc
    subst hw
    rfl
  exact key _ (Q.wdD_wU u) _
end GlobalTheory.Mem.JTop
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SetPointGood
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsFurtherAlt
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
namespace GlobalTheory.SetPtOff
theorem main_alt_alt : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂ → ∀ i, D.nd.l i ∉ TwistedPlaces.gset D → ∀ π ∈ D.nd.Zgood i, SetPt i (X.r i) (X.ρ i) π := by
  intro hP D L P nch HW F Cm X C₂ hS i hi π hπ
  have fa := hS.facts
  have hHub := _root_.GlobalTheory.T.split_bound_of_params_alt hP.font hP.fin GlobalTheory.Published.cheb_holds D L HW F (rowC C₂) nch X 120 0 hS.canon P
    (by linarith [hS.big]) le_rfl (by exact_mod_cast (Real.exp_pos _).le) (fa.admJ L hS.par) hS.par67 fa.admA
    fa.Conclusion1.1 fa.Conclusion1.2.2 fa.Conclusion2.1 fa.Conclusion2.2.2 fa.rhoBar fa.large.2.1 fa.large.2.2 fa.nct fa.trip fa.same fa.block
    fa.muUnr fa.depthG
  have hR : RestPt i (X.r i) (X.ρ i) π := hHub.2.2.2.2.2.2.2.1 i hi π hπ
  have hHG : HG D.nd D.naut i := ⟨π, (D.Zgood_tie i π).1 hπ⟩
  have hZ : π ∈ D.nd.Z i := (D.Z_tie i π).2 ((D.Zgood_tie i π).1 hπ).1
  have hJ := _root_.GlobalTheory.JumpStatement.holds_all_alt D L (fa.admJ L hS.par)
  have hdec : TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i (X.r i) (X.ρ i) π :=
    semisimple_decomposition_of D i (X.r i) (X.ρ i) π fa.admA.2.2.2.2.2.2 hR.good hR.rho hR.ss
  exact ⟨_root_.Formalism.MainNotions.N.galois_condition_one_of_alt D i (X.r i) fa.Conclusion1.1 hR.good,
    _root_.GlobalTheory.GTwoTheta.main_alt_alt hP.font D L fa.g2.1 hJ.1 hJ.2.2.1 i (X.r i) (X.ρ i) π hR.good hR.ng0 hR.ng1 hZ hdec,
    _root_.Formalism.MainNotions.N.galois_condition_three_of_alt_alt D i (X.r i) (X.ρ i) π fa.Conclusion1.1 hR.good hdec hR.cont hHG fa.rhoBar (litBurnside_all D) hR.g3,
    _root_.Formalism.MainNotions.N.admG4_of_goodR D i (X.r i) fa.Conclusion1.1 hR.good,
    galois_condition_five_of D i (X.r i) fa.Conclusion2.1 hHG hR.good,
    (GlobalTheory.TameDesign.main D i).2,
    galois_condition_six_of D i (X.r i) fa.Conclusion2.2.1 hHG hR.good,
    GlobalTheory.T.blochKato_localCondition_all_localizations hP.bk hP.tate hP.euler D i,
    continuous_family_of D i (X.r i) hR.good,
    semisimple_family_of D i (X.r i) hR.good,
    hdec, hR.eps, GlobalTheory.T.completion_comparison_admissible_every_place_over D i, hR.shape, GlobalTheory.FontaineAdm.fontaineProperties_all_places D i,
    GlobalTheory.T.integral_tate_H2_top hP.tate D i, GlobalTheory.T.unramifiedClassFieldBound_of_artin hP.artin D i⟩
end GlobalTheory.SetPtOff
end
end

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.set_pt_of_setup_not_twisted : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂ → ∀ i, D.nd.l i ∉ TwistedPlaces.gset D → ∀ π ∈ D.nd.Zgood i, SetPt i (X.r i) (X.ρ i) π := by
  first | exact @_root_.GlobalTheory.SetPtOff.main_alt_alt | exact _root_.GlobalTheory.SetPtOff.main_alt_alt | (intros; apply _root_.GlobalTheory.SetPtOff.main_alt_alt <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SXdAll
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 2000000 in
theorem sXd_all_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.ThetaDataExists hL := by
  intro hL
  refine StepW.of_all fun K B f T w _ _ _ P x l => ?_
  have hU : x.m.z.R.toRealDat.LUnif := x.m.intersectionNumber_baseChange.prim.unif
  have hW : x.m.z.R.toRealDat.models_HW := x.m.z.pins.char.base.models.HW
  have H := (GlobalTheory.ExportType.type_of_exportTie l.b.ser.ex hU hW).2.2.2
  exact ⟨⟨fun _ j _ => {_d | j ∈ Finset.Icc 1 (Dof x).R.m}, fun i j b a ha u =>
    sub_eq_zero.1 (LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 (H i j ha b a) u))⟩,
    fun i j b h1 h2 => Set.eq_univ_of_forall fun _ => Finset.mem_Icc.2 ⟨h1, h2⟩⟩
end GlobalTheory.HeightCounting.Up
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtMemImpAltAlt
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
namespace GlobalTheory.GalLoc
theorem atMem_and' {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p q : _root_.GlobalTheory.HeightCounting.Up.LayPAlt hL} (hp : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL p) (hq : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL q) :
    _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun K B f T w Z Wt p0 t nch n c => p K B f T w Z Wt p0 t nch n c ∧ q K B f T w Z Wt p0 t nch n c := by
  refine (hp.inter hq).imp fun K _ _ _ _ H => ?_
  refine (H.1.inter H.2).imp fun B f T _ H => ?_
  intro hK w Z Wt p0 t nch n xd c hE hX hC
  exact ⟨H.1 hK w Z Wt p0 t nch n xd c hE hX hC, H.2 hK w Z Wt p0 t nch n xd c hE hX hC⟩
theorem atMem_mono {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p q : _root_.GlobalTheory.HeightCounting.Up.LayPAlt hL} (hp : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL p)
    (h : ∀ K B f T w Z Wt p0 t nch n xd c, Nonempty (_root_.GlobalTheory.HeightCounting.defaultExtension hL K B f T w Z Wt p0 t nch n xd c) →
      p K B f T w Z Wt p0 t nch n c → q K B f T w Z Wt p0 t nch n c) : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL q := by
  refine hp.imp fun K _ _ _ _ H => ?_
  refine H.imp fun B f T _ H => ?_
  intro hK w Z Wt p0 t nch n xd c hE hX hC
  exact h K B f T w Z Wt p0 t nch n xd c hE (H hK w Z Wt p0 t nch n xd c hE hX hC)
end GlobalTheory.GalLoc
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsTied
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section
namespace GlobalTheory.HeightCounting.Up.RealOfReading
open _root_.Formalism.L2.Theta _root_.Formalism.L2.DIV _root_.Formalism.L2.Indef _root_.Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie
theorem exists_linked_data_of_agreement {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) {cf : CharFrame D} {nch : NChoice D}
    {tp : TupTied D cf nch} (X : GlobalTheory.NJoin.RealAt D cf nch tp) (hcf : P.cf = cf) (hC : P.C = nch) (htp : HEq P.tp tp)
    {M : MtFam D} {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r} (hM : P.M = M) (hrep : HEq P.rep rep)
    (ag : GlobalTheory.NJoin.Agree X M rep) (e0 : GlobalTheory.NRows.GoodIdempotentReadsAsGoodTypeProjector X) :
    ∃ T : _root_.GlobalTheory.NRows.LinkedData hL D, T.P = P ∧ HEq T.X.R X.R := by
  subst hcf
  subst hC
  cases eq_of_heq htp
  subst hM
  cases eq_of_heq hrep
  exact ⟨⟨P, X, ag, e0⟩, rfl, HEq.rfl⟩
end GlobalTheory.HeightCounting.Up.RealOfReading
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FramesExOfRealisation
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FramesExOfRealisation
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.FramesAtReal
theorem framesEx_of_realisation_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks), _root_.Formalism.IndefR.IndefiniteRealisationNormalisation Q → Q.FramesEx := by
  intro D L hT Gi Gl K Y cX ex Rc P Dcf Spf Zscf S Ks _ _ _ Q _
  exact GlobalTheory.FramesExistLev.selfDual_frames_normal_at_level_places_of_charFrame D Q.Rl.C Q.Rl.Pg Q.charW.base.lev.Pg
end GlobalTheory.FramesAtReal
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FramesExOfRealisationStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.framesEx_of_realPins_indefinite_scale : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks), _root_.Formalism.IndefR.IndefiniteRealisationNormalisation Q → Q.FramesEx := by
  first | exact @_root_.GlobalTheory.FramesAtReal.framesEx_of_realisation_alt | exact _root_.GlobalTheory.FramesAtReal.framesEx_of_realisation_alt | (intros; apply _root_.GlobalTheory.FramesAtReal.framesEx_of_realisation_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsParamsAtMem
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsParamsAtMem
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Col2
open Formalism.MainNotions.Inhab Formalism.BasicNotions.TH Formalism.L2.GlobalTheoryTheory IsDedekindDomain NumberField GlobalTheory.EX GlobalTheory.EX.OB
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.HeightCounting.Up.SizePar
theorem exists_params_atMem_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) :
    _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ _ _ _ _ => ∃ L : SizeData₂ (w.D Z), Nonempty (ParameterChoice' (w.D Z) L) := by
  refine (evG_of_ev GlobalTheory.PrimIn.AtData.ev_params).imp fun K _ _ _ _ hK => ?_
  refine ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, by simp, by simp,
    fun B f T hO _ _ _ _ w Z Wt p0 t nch n xd c _ _ _ => ?_⟩
  obtain ⟨L, -, -, hp, -⟩ := hK (w.st Z) hO t.etaF fun v hv j h1 h2 => by
    have key : ∀ v', (w.D Z).what₂.muAt v' = (w.D Z).what₂.mu0 → v' ∉ Wt := by
      intro v' he hw
      have he' : (w.st Z).W.muAt v' = (w.st Z).C.mu0 := he
      rw [t.mu.on v' hw] at he'
      have h1 := t.mu.tw v'
      rw [he', t.mu.mu0] at h1
      exact (TwFin.tw_fin B f T).2.1 v' h1.symm
    change (w.D Z).what₂.Aj j v = 0
    replace hv : (w.D Z).what₂.muAt v = (w.D Z).what₂.mu0 := hv
    have a := t.untw v (key v hv) j h1 h2
    have b := t.untw _ (key _ (((w.D Z).what₂.muAt_conj v).trans hv)) j h1 h2
    unfold Formalism.BasicNotions.Rows.Data.Aj
    rw [hv, a.1, a.2, b.1]
    rfl
  exact ⟨L, hp⟩
end GlobalTheory.HeightCounting.Up.SizePar
namespace GlobalTheory.HeightCounting.Up.SizePar
end GlobalTheory.HeightCounting.Up.SizePar
namespace GlobalTheory.HeightCounting.Up.SizePar
theorem exists_params_alt :
    (∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ _ _ _ _ => ∃ L : SizeData₂ (w.D Z), Nonempty (ParameterChoice' (w.D Z) L)) ∧
      AllSt fun _ _ _ _ _ _ x => (∃ L : SizeData₂ (Dof x), Nonempty (ParameterChoice' (Dof x) L)) ∧
        ∀ Lc : LocAll (lay0 (Dof x)), ∃ L : SizeData₂ (withLoc Lc), Nonempty (ParameterChoice' (withLoc Lc) L) :=
  ⟨_root_.GlobalTheory.HeightCounting.Up.SizePar.exists_params_atMem_alt, exists_params_allSt⟩
end GlobalTheory.HeightCounting.Up.SizePar
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsParamsAtMemStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_parameters_parameterChoice_nonempty : (∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ _ _ _ _ => ∃ L : SizeData₂ (w.D Z), Nonempty (ParameterChoice' (w.D Z) L)) ∧ AllSt fun _ _ _ _ _ _ x => (∃ L : SizeData₂ (Dof x), Nonempty (ParameterChoice' (Dof x) L)) ∧ ∀ Lc : LocAll (lay0 (Dof x)), ∃ L : SizeData₂ (withLoc Lc), Nonempty (ParameterChoice' (withLoc Lc) L) := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.SizePar.exists_params_alt | exact _root_.GlobalTheory.HeightCounting.Up.SizePar.exists_params_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.SizePar.exists_params_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowsBOfDecay
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LUnifRealTB
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LUnifRealTB
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.LocalUniformizerReal
theorem lUnif_of_nV_ge_of_bundle : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (B : _root_.Formalism.IndefR.RealTBAlt Rc P Dcf Spf Zscf S), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → B.Q.Rl.toRealDat.LUnif := by
  intro h1 D L hT Gi Gl K Y cX ex Rc P Dcf Spf Zscf S B hn
  exact GlobalTheory.TiedUnif.uniformisation_every_embedding_thirdKind h1 GlobalTheory.Mem.VolFin.finVol B.T B.Q.Rl _ B.κ B.v₀ B.fw B.O B.Q.charW B.bar B.pins B.rhoGeo B.equivAll hn
end GlobalTheory.LocalUniformizerReal
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LUnifRealTBStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lUnif_of_nV_ge : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (B : _root_.Formalism.IndefR.RealTBAlt Rc P Dcf Spf Zscf S), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → B.Q.Rl.toRealDat.LUnif := by
  first | exact @_root_.GlobalTheory.LocalUniformizerReal.lUnif_of_nV_ge_of_bundle | exact _root_.GlobalTheory.LocalUniformizerReal.lUnif_of_nV_ge_of_bundle | (intros; apply _root_.GlobalTheory.LocalUniformizerReal.lUnif_of_nV_ge_of_bundle <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowsBOfClauses
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj Formalism.L2 Formalism.L2.Rows Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.RowsAtRealTB
set_option maxHeartbeats 1000000 in
theorem rowsB_of_clauses_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (B : _root_.Formalism.IndefR.RealTBAlt Rc P Dcf Spf Zscf S), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → B.Q.Rl.toRealDat.ExAt → B.Q.Rl.toRealDat.LUnif → IoExt B.Q.Rl.toRealDat → _root_.Formalism.IndefR.IndefiniteRealisationBoundedRows B := by
  intro D L hT Gi Gl K Y cX ex Rc P Dcf Spf Zscf S B hn hEx hUnif hIo
  exact ⟨hIo, fun i => GlobalTheory.T.oneMapRowR_of_weakCharacterisation D _ _ _ _ P.A3 B.T B.Q.Rl (faceT P Dcf Spf Zscf) B.κ B.v₀ B.O (phEff B.Q.Rl)
    hn B.Q.charW hEx ⟨B.fw⟩ hIo i (B.pins i) (B.phase i hUnif)⟩
end GlobalTheory.RowsAtRealTB
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowsBOfDecay
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.RowsAtRealTBClose
theorem rowsB_of_decay_alt : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (B : _root_.Formalism.IndefR.RealTBAlt Rc P Dcf Spf Zscf S), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → B.Q.Rl.toRealDat.ExAt → _root_.Formalism.IndefR.IndefiniteRealisationBoundedRows B := by
  intro hDec D L hT Gi Gl K Y cX ex Rc P Dcf Spf Zscf S B hn hEx
  have hUnif := _root_.GlobalTheory.T.lUnif_of_nV_ge hDec D L hT Gi Gl K Y cX ex Rc P Dcf Spf Zscf S B hn
  have hIo := GlobalTheory.T.ioExt_of_weakCharacterisation_of_orthonormal_frames D _ _ _ _ P.A3 _ B.Q.Rl (faceT P Dcf Spf Zscf) B.Q.charW hEx B.Q.stdV
  exact _root_.GlobalTheory.RowsAtRealTB.rowsB_of_clauses_alt D L hT Gi Gl K Y cX ex Rc P Dcf Spf Zscf S B hn hEx hUnif hIo
end GlobalTheory.RowsAtRealTBClose
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowsBOfDecayStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.indefinite_scale_theta_bound_right_alt : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (B : _root_.Formalism.IndefR.RealTBAlt Rc P Dcf Spf Zscf S), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → B.Q.Rl.toRealDat.ExAt → _root_.Formalism.IndefR.IndefiniteRealisationBoundedRows B := by
  first | exact @_root_.GlobalTheory.RowsAtRealTBClose.rowsB_of_decay_alt | exact _root_.GlobalTheory.RowsAtRealTBClose.rowsB_of_decay_alt | (intros; apply _root_.GlobalTheory.RowsAtRealTBClose.rowsB_of_decay_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RestPtOf
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RestPtOf
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
noncomputable section
namespace GlobalTheory.NLinkTameShape
theorem restPt_of_alt (hP : Hypotheses₂) (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc)
    (F : FonOf D.loc D.locA HW) (X : KillingConditions.HubData D) (C₂ : ℝ) (hS : _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂) (i : D.nd.Loc)
    (hi : D.nd.l i ∉ TwistedPlaces.gset D) (π : D.nd.X i) (hπ : π ∈ D.nd.Zgood i) : RestPt i (X.r i) (X.ρ i) π := by
  have hb : ((0 : ℕ) : ℝ) ≤ L.sc.b := by
    simp only [Nat.cast_zero]; unfold Scale.b; exact (Real.exp_pos _).le
  have hL : 1 ≤ L.sc.L := by unfold Scale.L; exact Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le
  have fa := hS.facts
  exact (_root_.GlobalTheory.T.split_bound_of_params_alt hP.font hP.fin GlobalTheory.Published.cheb_holds D L HW F (rowC C₂) nch X 120 0 hS.canon P hL le_rfl hb
    (fa.admJ L hS.par) hS.par67 fa.toCore.admA fa.Conclusion1.1 fa.Conclusion1.2.2 fa.Conclusion2.1 fa.Conclusion2.2.2 fa.rhoBar fa.large.2.1
    fa.large.2.2 fa.nct fa.trip fa.same fa.block fa.muUnr fa.depthG).2.2.2.2.2.2.2.1 i hi π hπ
theorem main_alt_alt : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂ → ∀ i, D.nd.l i ∉ TwistedPlaces.gset D → ∀ π ∈ D.nd.Zgood i, EmbeddingTypes.admG5 i (X.r i) (X.ρ i) π := by
  intro hP D L P nch HW F Cm X C₂ hS i hi π hπ _ S hG
  have R := _root_.GlobalTheory.NLinkTameShape.restPt_of_alt hP D L P nch HW F X C₂ hS i hi π hπ
  have hHG : HG D.nd D.naut i := ⟨π, (D.Zgood_tie i π).1 hπ⟩
  have h32 := hS.facts.Conclusion2.1 i hHG (X.r i) R.good
  have hx := (GlobalTheory.TameDesign.main D i).2
  have hrb := isRhoBar_of_isRhoOf D i π (X.ρ i π) R.rho
  intro v hv
  have hl := D.nd.SQ_l i v hv
  obtain ⟨ha, hb, hc⟩ := h32 v hv hl
  refine ⟨(hx v hv).1, fun hq x => ?_, fun hk => ?_, fun hvS => ⟨?_, fun a => ?_⟩⟩
  · obtain ⟨hprod, Pm, hPm⟩ := ha hq x
    refine ⟨fun γ hγ => by simpa [rO, chi1] using hprod γ hγ, ?_⟩
    let ψ : (Fin D.R.nV → KK D.nd i) ≃ₗ[KK D.nd i] (Fin D.R.nV → KK D.nd i) :=
      LinearEquiv.ofLinear (Matrix.toLin' ((Pm⁻¹ : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)))
        (Matrix.toLin' ((Pm : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)))
        (by rw [← Matrix.toLin'_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.toLin'_one])
        (by rw [← Matrix.toLin'_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.toLin'_one])
    refine ⟨ψ.trans (Formalism.MainNotions.N.K.SplitLatticeDiagonal.splitL D.R.r D.R.t D.R.nV rfl), fun γ hγ u => ?_⟩
    have hM := hPm γ hγ
    have h1 : ((Pm⁻¹ : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) *
        mapM (toK D.nd i) (rO D.nd i (X.r i) x) γ =
        Matrix.diagonal (fun k : Fin D.R.nV => if (k : ℕ) < D.R.r then 1 else
          algebraMap (D.nd.O i) (KK D.nd i) (chi1 D.nd i γ)) *
          ((Pm⁻¹ : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) := by
      rw [← hM]
      have e : Pm⁻¹ * mapRep (algebraMap (D.nd.O i) (Kf D.nd i)) (X.r i x) γ =
          (Pm⁻¹ * mapRep (algebraMap (D.nd.O i) (Kf D.nd i)) (X.r i x) γ * Pm) * Pm⁻¹ := by group
      have e2 := congrArg (fun g : GL (Fin D.R.nV) (Kf D.nd i) => (g : Matrix (Fin D.R.nV) (Fin D.R.nV) (Kf D.nd i))) e
      simp only [Units.val_mul] at e2
      exact e2
    show Formalism.MainNotions.N.K.SplitLatticeDiagonal.splitL D.R.r D.R.t D.R.nV rfl
        (((Pm⁻¹ : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)).mulVec
          ((mapM (toK D.nd i) (rO D.nd i (X.r i) x) γ).mulVec u)) = _
    rw [Matrix.mulVec_mulVec, h1, ← Matrix.mulVec_mulVec]
    exact splitL_diagonal D.R.r D.R.t D.R.nV rfl _ _
  · obtain ⟨k, hk⟩ := hk
    have hvS : v ∈ D.nd.S i := by
      refine (D.nd.S_def i v).2 ⟨?_, hl⟩
      fin_cases k
      · exact Or.inl hk
      · exact Or.inr (Or.inl hk)
    obtain ⟨Pp, hU, hPp⟩ := hb ⟨k, hk⟩ hvS
    exact ⟨Pp, fun x γ hγ => hPp x γ hγ, hU⟩
  · exact (hc hvS).1 (X.ρ i) π S (Formalism.MainNotions.SumRepresentations.At.inertia_props_of_idempotent_choice D.nd hG)
  · have H := (hc hvS).2 _ hrb a
    obtain ⟨H0z, H1z, H2z⟩ := H
    rw [rhoBarTw_eq]
    letI : TopologicalSpace (IsLocalRing.ResidueField (D.nd.O i)) := ⊥
    haveI : DiscreteTopology (IsLocalRing.ResidueField (D.nd.O i)) := ⟨rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · have e : H0 ((twistRep (glRep (redRep D.nd i (X.ρ i π))) (Formalism.MainNotions.SumRepresentations.At.chiEpsBar D.nd i a)).comp (decS D.nd v)) = ⊥ := H0z
      rw [e]
      infer_instance
    · convert H1z using 2
    · convert H2z using 2
end GlobalTheory.NLinkTameShape
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RestPtOfStatement
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admG5_of_setup : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂ → ∀ i, D.nd.l i ∉ TwistedPlaces.gset D → ∀ π ∈ D.nd.Zgood i, EmbeddingTypes.admG5 i (X.r i) (X.ρ i) π := by
  first | exact @_root_.GlobalTheory.NLinkTameShape.main_alt_alt | exact _root_.GlobalTheory.NLinkTameShape.main_alt_alt | (intros; apply _root_.GlobalTheory.NLinkTameShape.main_alt_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PlacementOfRealisation
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PlacementOfRealisation
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.RowPlacementReal
theorem placement_of_realisation_alt : GlobalTheory.Published.DiscreteSeriesClassification → ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks), _root_.Formalism.IndefR.IndefiniteRealisationNormalisation Q → (∀ x : S.X.B.I.E, HEq (S.X.ιE x) x) → _root_.Formalism.IndefR.IndefiniteRealisationExtends Q := by
  intro hDS D L hT Gi Gl K Y cX ex Rc P Dcf Spf Zscf S Ks _ _ _ Q hP hE
  have hE0 : Formalism.L2.SG.RowDict.IdempotentRealFixed D := by
    have key : ∀ {g : ℕ} [Fact g.Prime] {C : Formalism.IrreducibleCountingLemmas.TYPES.LabelConv (ZMod g)} (O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod g) C), Formalism.IrreducibleCountingLemmas.TYPES.LabelMapEquivariant O → ∀ (r : ℕ) (f : Polynomial (ZMod g)), f.Monic → f.coeff 0 ≠ 0 → ∀ x, star ((Formalism.L2.NT.eSerO O r f).coeff x) = (Formalism.L2.NT.eSerO O r (Polynomial.C (f.coeff 0)⁻¹ * f.reverse)).coeff x := GlobalTheory.T.star_coeff_eisenstein_series_reverse_poly
    exact GlobalTheory.GoodIdemReal.star_coeff_of_reverse D (fun k f hm h0 x => by
      haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      rw [Rc.T.n.types.eSer_def, Rc.T.n.types.eSer_def]
      exact key _ (Rc.T.n.types.O_equiv k) D.R.r f hm h0 x)
  exact GlobalTheory.T.exists_rowPlacement_finiteElement_matches_levels hDS Q.Rl.toRealDat (faceT P Dcf Spf Zscf).lv2 S.X S.G Q.instEq Q.ιS Q.tS Q.cG
    Q.charW.base.lev Q.charW.base.grp Q.charW.base.models Q.host hE0 Q.ιS_eq hE hP.grpRecPin hP.tSfin hP.tSpin
end GlobalTheory.RowPlacementReal
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PlacementOfRealisationStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.indefinite_scale_theta_nonvanishing_alt : GlobalTheory.Published.DiscreteSeriesClassification → ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks), _root_.Formalism.IndefR.IndefiniteRealisationNormalisation Q → (∀ x : S.X.B.I.E, HEq (S.X.ιE x) x) → _root_.Formalism.IndefR.IndefiniteRealisationExtends Q := by
  first | exact @_root_.GlobalTheory.RowPlacementReal.placement_of_realisation_alt | exact _root_.GlobalTheory.RowPlacementReal.placement_of_realisation_alt | (intros; apply _root_.GlobalTheory.RowPlacementReal.placement_of_realisation_alt <;> assumption)
end
end
end
