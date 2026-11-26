module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.STiesR
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AtSame
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AmbientH1fOfLocalFiniteness
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AdmissibleJOfRestricted
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PointInputAwayFromTypePrimes

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR.Links Formalism.IndefR.Cx
namespace Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}
def pwOf_alt {Rc : _root_.Formalism.L2.RecTAlt ex} (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc)
    (hin : ∀ u, Formalism.L2.SG.PoincareInHH.PoincareSetting.InHH S.X u S.Y.hK) (u : D.what₂.Word) : Formalism.IndefR.Cx.PerW S.X S.Y.hK u where
  Dt := S.Y.Dt u
  hD := S.Y.reps u
  hin := hin u
  hlin := Formalism.L2.SG.Closed.PuLinearC_holds D S.X S.Y u
  F := (Rc.T.cols.forms u).to0
  Tr := S.tr u
  hI := S.into u
  hB := S.bij u
set_option genInjectivity false in
set_option genSizeOfSpec false in
structure IndefiniteRealisation (Rc : _root_.Formalism.L2.RecTAlt ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs))
    (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3)
    (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] : Type 1 where
  Rl : RealDat3 D P.A3 Ks
  sEE : (Rl.toCx3 (faceT P Dcf Spf Zscf)).EE →ₗ⋆[ℂ] ((faceT P Dcf Spf Zscf).fc (Rl.toCx3 (faceT P Dcf Spf Zscf)).zs).Sp.HH
  charW : Rl.WeakCharacterisation (faceT P Dcf Spf Zscf)
  zs : (Rl.toCx3 (faceT P Dcf Spf Zscf)).zs = P.Zs
  s0 : HEq ((Rl.toCx3 (faceT P Dcf Spf Zscf)).data (faceT P Dcf Spf Zscf).cr false) P.S0
  s1 : HEq ((Rl.toCx3 (faceT P Dcf Spf Zscf)).data (faceT P Dcf Spf Zscf).cr true) P.S1
  dc : Dcf P.Zs = P.Dc
  sp : HEq (Spf P.Zs) P.Sp
  col : HEq ((Rl.toCx3 (faceT P Dcf Spf Zscf)).colOf (faceT P Dcf Spf Zscf).cr
      ((Rl.toCx3 (faceT P Dcf Spf Zscf)).colDef
        (fun u t => (zetaEps (Rl.toCx3 (faceT P Dcf Spf Zscf)) (faceT P Dcf Spf Zscf).cr sEE u t)⁻¹) sEE)) P.C
  allPlaces : Rl.AllPlaces
  trSem : (∃ tr, Rl.TrISem (faceT P Dcf Spf Zscf) tr ∧ TrISepWith P.A3 tr) →
    Rl.TrISem (faceT P Dcf Spf Zscf) P.A3.trI ∧ P.A3.fam3.TrISep
  stdChar : Formalism.L2.Theta.IsStdChar D Rl.ψ (-1)
  psiPin : Rl.ψ = Rc.T.theta.W.ψ
  signs : Formalism.IndefR.Mi.SignsAtG Rl.toRealDat (faceT P Dcf Spf Zscf).lv2
  wdD : P.Dc.Mem → D.what₂.Word
  wdD_wU : ∀ u, wdD (P.I.wU u) = u
  wU_wdD : ∀ x, P.I.wU (wdD x) = x
  hin : ∀ u, Formalism.L2.SG.PoincareInHH.PoincareSetting.InHH S.X u S.Y.hK
  bR : ∀ x, Fin (P.Dc.a x) → (D.mem (wdD x)).A.Mram
  spPin : HEq P.Sp (Formalism.IndefR.Cx.spOf (X := S.X) (twAt D.what₂.embLL P.A3.A.v0) P.Dc S.Y.hK S.G wdD (fun x => _root_.Formalism.IndefR.pwOf_alt S hin (wdD x)) bR)
  frames : Formalism.IndefR.Seed.Frm.FramesExistDiagonal D Rl.Pg → Formalism.IndefR.Mi.FramesOKg2 Rl
  cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd
  Sx : Formalism.IndefR.NX.RatDat D.ntw
  nexp : Formalism.IndefR.NX.NExpRealS Rl cG Sx
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
  sEEc : Tw (twAt D.what₂.embLL P.A3.A.v0) Rl.HE.H →ₗ⋆[ℂ] Tw (twAt D.what₂.embLL P.A3.A.v0) (Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX S.X)
  sEEj : HEq sEE sEEc
  seeLev : (∃ t' : Formalism.L2.Theta.GA D (Yc D 0), Formalism.IndefR.AutomorphicEvaluation.ConjLevel t'⁻¹ (levS _ (Rl.βY 0) (Rl.dat0 (Rl.toRealDat.levR (faceT P Dcf Spf Zscf).lv2 true))) (Formalism.IndefR.Lev.levChi _ (Rl.βY 0) (Rl.dat0 (Rl.toRealDat.levR (faceT P Dcf Spf Zscf).lv2 true))) (ιS ⁻¹' seeKS S.X) (fun k => seeChiS S.X (ιS k))) →
    Formalism.IndefR.AutomorphicEvaluation.ConjLevel tS⁻¹ (levS _ (Rl.βY 0) (Rl.dat0 (Rl.toRealDat.levR (faceT P Dcf Spf Zscf).lv2 true))) (Formalism.IndefR.Lev.levChi _ (Rl.βY 0) (Rl.dat0 (Rl.toRealDat.levR (faceT P Dcf Spf Zscf).lv2 true))) (ιS ⁻¹' seeKS S.X) (fun k => seeChiS S.X (ιS k))
  seeEval : (∃ c' : ℝ, Formalism.IndefR.AutomorphicEvaluation.EvalTieT (Rl.MY 0) Rl.ν0 Rl.fd0 (Rl.toRealDat.EEat (Rl.toRealDat.levR (faceT P Dcf Spf Zscf).lv2 true)) S.X S.G ιS tS c') →
    Formalism.IndefR.AutomorphicEvaluation.EvalTieT (Rl.MY 0) Rl.ν0 Rl.fd0 (Rl.toRealDat.EEat (Rl.toRealDat.levR (faceT P Dcf Spf Zscf).lv2 true)) S.X S.G ιS tS cS
  uS : ℂ
  uS_norm : ‖uS‖ = 1
  seeDef : ∀ (x : Tw (twAt D.what₂.embLL P.A3.A.v0) Rl.HE.H) (hx : Rl.HE.e (Tw.out x) ∈ (Rl.toRealDat.EEat (Rl.toRealDat.levR (faceT P Dcf Spf Zscf).lv2 true))),
    sEEc x = Tw.mk (twAt D.what₂.embLL P.A3.A.v0) ((uS * (κS : ℂ)) • (Formalism.IndefR.AutomorphicEvaluation.sEEofTT (Rl.MY 0) Rl.ν0 Rl.fd0 (Rl.toRealDat.EEat (Rl.toRealDat.levR (faceT P Dcf Spf Zscf).lv2 true)) S.X S.G ιS tS cS) ⟨Rl.HE.e (Tw.out x), hx⟩)
  seeK : 0 < κS ∧ ((∃ κ' : ℝ, 0 < κ' ∧ ∀ (x : Tw (twAt D.what₂.embLL P.A3.A.v0) Rl.HE.H) (hx : Rl.HE.e (Tw.out x) ∈ (Rl.toRealDat.EEat (Rl.toRealDat.levR (faceT P Dcf Spf Zscf).lv2 true))),
      ‖(κ' : ℂ) • (Formalism.IndefR.AutomorphicEvaluation.sEEofTT (Rl.MY 0) Rl.ν0 Rl.fd0 (Rl.toRealDat.EEat (Rl.toRealDat.levR (faceT P Dcf Spf Zscf).lv2 true)) S.X S.G ιS tS cS) ⟨Rl.HE.e (Tw.out x), hx⟩‖ = ‖x‖) →
    ∀ (x : Tw (twAt D.what₂.embLL P.A3.A.v0) Rl.HE.H), Rl.HE.e (Tw.out x) ∈ (Rl.toRealDat.EEat (Rl.toRealDat.levR (faceT P Dcf Spf Zscf).lv2 true)) →
      RealDat.nP (faceT P Dcf Spf Zscf).lv2 true * ‖sEEc x‖ ^ 2 = ‖x‖ ^ 2)
  host : HostHyp D
  err_eq : ∀ w j, ((Rl.toCx3 (faceT P Dcf Spf Zscf)).data (faceT P Dcf Spf Zscf).cr false).err0 w j =
    errCan ((Rl.toCx3 (faceT P Dcf Spf Zscf)).data (faceT P Dcf Spf Zscf).cr false)
      ((faceT P Dcf Spf Zscf).fc (Rl.toCx3 (faceT P Dcf Spf Zscf)).zs).Z.F0 w
  vpos : ∀ i, (Vc D i).IsPosDef
namespace RealT
variable {Rc : _root_.Formalism.L2.RecTAlt ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
  {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  (R : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks)
abbrev _root_.Formalism.IndefR.IndefiniteRealisation.F (_R : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) : Face3 D P.A3 := faceT P Dcf Spf Zscf
def _root_.Formalism.IndefR.IndefiniteRealisation.FramesEx : Prop := Formalism.IndefR.Seed.Frm.FramesExistDiagonal D R.Rl.Pg
end RealT
end Formalism.IndefR
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.HeightCounting.Up
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N _root_.Formalism.L2 _root_.Formalism.L2.Host Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting
  GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option genInjectivity false
set_option genSizeOfSpec false
set_option maxHeartbeats 2000000
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
structure SameGaloisLevel (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (x : St P) : Type 1 where
  a : _root_.GlobalTheory.HeightCounting.HeightCountingBaseData hL (Dof x) (cfOf x) (repOf x.r.Y)
  Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield (Dof x).host.E)) → PlE (Dof x).host
  Pq_over : ∀ v, NG.OverPl (Pq v) v
  sel : Set.range Pq = Set.range w.I.sel
structure IntermediateLevel (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (x : St P) : Type 1 extends toLA : _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x where
  mt : InMt x.r.Y (cfOf x) w.I.xi (QOf P)
  rat : InRat x.r.Y x.m.z.cG
  cusp : RowCusp (Dof x) a.A.row
structure FirstIntermediateLevel (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (x : St P) : Type 1 extends toLI : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x where
  b : _root_.GlobalTheory.HeightCounting.SettingsFormsData a rat Pq
structure SecondIntermediateLevel (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (x : St P) : Type 1 extends toLI : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x where
  b : _root_.GlobalTheory.HeightCounting.SeriesData x.m.z.geo a rat mt.ad.PV Pq
structure ThirdIntermediateLevel (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (x : St P) : Type 1 extends toLI : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x where
  b : _root_.GlobalTheory.HeightCounting.ModuliPointsData x.m.z.geo a rat mt.ad.PV Pq
structure StrictHenselianAcyclicLevel (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (x : St P) : Type 1 extends toStrictHenselianAcyclic : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x where
  c : _root_.GlobalTheory.HeightCounting.HeightCountingCharacterData mt b T.k T.psi
variable (hL)
def extensionWithLaw : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL := fun K B f T w Z Wt p0 t nch n xd c => _root_.GlobalTheory.HeightCounting.defaultExtension hL K B f T w Z Wt p0 t nch n xd c × PLift (BkLaw (w.D Z))
def SameGaloisLevelExists : Prop := AllSt fun _ _ _ _ _ P x => IsEmpty x.o.N.nd.Loc →
  ∃ x' : St P, Nonempty (_root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x') ∧ GlobalTheory.TwistChoice.SameGalois (Dof x).nd (Dof x').nd
def RationalityStatementThirdPlaceSeries : Prop := AllSt fun _ _ _ _ _ _ x => _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x → Nonempty (InRat x.r.Y x.m.z.cG)
def CuspStatement' : Prop := AllSt fun _ _ _ _ _ _ x => ∀ l : _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x, RowCusp (Dof x) l.a.A.row
def FirstIntermediateLevelExists : Prop := AllSt fun _ _ _ _ _ P x => _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x → ∃ x' : St P, Nonempty (_root_.GlobalTheory.HeightCounting.Up.FirstIntermediateLevel hL x')
def SecondIntermediateLevelExists : Prop := AllSt fun _ _ _ _ _ P x => _root_.GlobalTheory.HeightCounting.Up.FirstIntermediateLevel hL x → ∃ x' : St P, Nonempty (_root_.GlobalTheory.HeightCounting.Up.SecondIntermediateLevel hL x')
def ThirdIntermediateLevelExists : Prop := AllSt fun _ _ _ _ _ P x => _root_.GlobalTheory.HeightCounting.Up.SecondIntermediateLevel hL x → ∃ x' : St P, Nonempty (_root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x')
def StrictHenselianAcyclicLevelNonempty : Prop := AllSt fun _ _ _ T _ _ x => ∀ l : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x, Nonempty (_root_.GlobalTheory.HeightCounting.HeightCountingCharacterData l.mt l.b T.k T.psi)
def EtaStatement' : Prop := AllSt fun _ _ _ _ _ P x => ∀ l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x,
  _root_.GlobalTheory.CoefDuty.AutomorphicSideExists l.a.A l.mt.M l.c.ch l.c.tp.tup → _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' =>
    GlobalTheory.CoefDuty.Large D' ∧ ∀ j v, 1 ≤ j → j ≤ (Dof x).R.m → ∀ v' : D'.what₂.places.Pl, HEq v' v → D'.what₂.etaJ j v' = P.q.eta j v
def FinitenessStatement : Prop := AllSt fun K _ _ _ w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) (S : SExt) (Γ : GeoP),
  ∃ (Z : w.Lt) (v : Lv3 (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL) S Γ).s K w Z), v.Wt = P.Wt ∧ Kept l.c.ch v.nch
end GlobalTheory.HeightCounting.Up
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ToSTiesR
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.Mem.SRe
open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S _root_.Formalism.L2.SG.HidaSetting _root_.Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.SG.RowDict Formalism.L2.Forms
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl K Yd cX}
def SRest.toRealSpectralMatching (Rc : _root_.Formalism.L2.RecTAlt ex) {P : SPack D fun u => (Rc.T.cols.forms u).to0} (S : SRest P) :
    _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc where
  toSTies := S.toSTies
  tr := P.tr
  into := P.into
  bij := P.bij
  lev := P.lev
  colPin := fun _ => S.colPin
  inst := P.inst
  G := P.G
  rowTie := fun _ => S.rowTie
  locTied := S.locTied
section
end
end GlobalTheory.Mem.SRe
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Inner
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open GlobalTheory.HeightCounting GlobalTheory.Mem.R3.Tr
noncomputable section
namespace GlobalTheory.LayerMove
set_option maxHeartbeats 4000000
variable {D : D7} (m : Mv D) {hL : _root_.UpperTheory.Zero.LLC.RecTExists}
def InnerAlt {cf : CharFrame D} {C : NChoice D} {tp : TupTied D cf C} (n : _root_.GlobalTheory.HeightCounting.NormChoiceRealisation hL D cf C tp) : Prop :=
  LabConj n.D n.A.wdT ∧
    (∀ k, haveI : Fact (n.D.host.g k).Prime := ⟨n.D.host.g_prime k⟩
      n.A.grp.ζ k = (GlobalTheory.Mem.TypePl.labDat (n.D.host.g k)).gen) ∧
    ∃ fr : Formalism.L2.OmFrame n.D, fr.jE = n.jE ∧ PhtOn n.A.wd fr fun _ _ _ _ => True
section
end
end GlobalTheory.LayerMove
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ClosingFamilyX
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
namespace GlobalTheory
theorem closingFamilyX_alt_alt : GlobalTheory.Published.FontaineBcris → Formalism.GaloisCohomology.LocalFinitenessK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (large₂ : SizeData₂ D) (X : KillingConditions.HubData D), @_root_.Formalism.MainNotions.AdmissibleParameterJ.JumpClosed D → _root_.Formalism.MainNotions.AdmissibleParameterJ.AdmJAlt large₂ → EmbeddingTypeJumps.ParametersPolynomiallyBounded large₂ → _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → GlobalTheory.SplitCoef.OSplit D → GlobalTheory.PtCore.PtFam D X.r X.ρ → (∀ i, GlobalTheory.HubLoc.cBnum (D.nd.l i) ⌊2 * large₂.sc.b⌋₊ D.R.t (4 * D.R.n * D.R.nV) ≤ X.cB i) → (∀ i, AbsIrreducibleDistinct D i (X.r i)) ∧ (∀ i, KillingConditions.RangeAD large₂ X.exc (D.nd.l i) → ∀ π, ∃ M0 h0 : ℕ, JointConditionTameBound D HW F i (X.r i) π M0 h0 (X.cB i)) ∧ (∀ i, D.nd.l i ∉ TwistedPlaces.gset D → ∀ π ∈ D.nd.Zgood i, EmbeddingTypes.ambDual (D := D) i (X.ρ i) π (X.dc i)) ∧ (∀ i π, EmbeddingTypes.H1fFiniteRankTorsion (D := D) i (X.ρ i) π (X.dc i))
:= by
  intro hF hK D HW F large₂ X hJ hA hP h41 hO hX hcB
  refine ⟨fun i => UpperTheory.GalS.jc_of_u (hX.good i) hO (_root_.UpperTheory.GalS.g3a_of_restricted_general_alt h41 hA.2.2.1 i _ (hX.good i)), fun i hR π => ?_,
    fun i hl π hπ => ?_, fun i π => GlobalTheory.Pass.ambient_h1f_of_local_finiteness hK D i _ π _ (hX.cont i π)⟩
  · exact GlobalTheory.BlockWindow.jointCond_TB_at_range D HW F large₂ (hJ large₂ hA) hP i _ π _ (fun h => hR.1 (Or.inl h))
      (fun h => hR.2.1 (Or.inl h)) (fun h => hR.2.1 (Or.inr h)) (hX.good i) (hcB i)
  · have hp := _root_.GlobalTheory.T.ptIn_of_ptFam_deRham_away hF D X hX hA.1 i hl π hπ
    intro _ w hw _ C τ a
    have hd : ∃ e, GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsDecomp (t := D.R.t) (X.r i π) (X.ρ i π) (D.nd.chi i) e := by
      obtain ⟨e, he⟩ := hp.dec
      exact ⟨e, fun g u => he g u⟩
    have := D.nd.lPrime i
    have := C.LL.2
    have hdr := (GlobalTheory.Per.CrisDR.isDR_of_isCrys _ _ _ (D.locT (D.nd.l i)) _ C.LL _ _ (hp.crys w hw C π)).1
    exact (((GlobalTheory.SummandJumps.main D i w hw (D.locT _) C.LL C.le (X.r i) (X.ρ i) π hd).2 hdr).2.2 τ a).2
end GlobalTheory
end
end
