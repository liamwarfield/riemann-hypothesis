module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
public import Formalism.LocalToGlobal.PtKOfReal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JumpsCardOfBuilt

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColJoinSOfSTiesR
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped InnerProductSpace
open MeasureTheory Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.RowDict Formalism.L2.SG.ColDict Formalism.L2.SG.KerJoinS Formalism.L2.SG.KerSideCut Formalism.IndefR.Cx Formalism.L2.Indef
namespace Formalism.L2.SG.JoinSI
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Twist
variable {D : D7} (X : HidaSetting D) (G : GoodOp X) (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC X G)
  {Fm : ∀ u, Formalism.L2.Forms.Forms0 D u} (Tr : ∀ u, Transport X u (Fm u)) (hK : X.LevelSubgroupCharacter)
  (Dt : D.what₂.Word → Set X.B.I.GA)
  {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs}
  (P : CxData A) {fc : DefSub A → DefFace Bs}
  (eV : ∀ t, (Fin ((fc P.zs).Df1.nV t) → K) →ₗ[K] A.FR t) (sEE : P.EE →ₗ⋆[ℂ] (fc P.zs).Sp.HH)
  (s : Bool) (σ : K →+* ℂ)
  (m : D.what₂.Word → (fc P.zs).Dc.Mem)
  (cφ : ∀ u, D.what₂.Mu u ≃ₗ[ℂ] (Fin ((fc P.zs).Dc.a (m u)) → ℂ))
  (cF : (Fin ((fc P.zs).Df1.nV Bs.μ0) → ℂ) →ₗ[ℂ] D.what₂.Amb D.what₂.mu0)
  (eR : D.what₂.EE →ₛₗ[Formalism.IndefR.Links.cj s] P.EE)
end Twist
section SpOf
end SpOf
section At
variable {D : D7}
variable {X : HidaSetting D} {G : GoodOp X} {Y : Formalism.L2.SG.Full.Full X} {j : FinX Y → (D.what₂.EE ≃ₗᵢ[ℂ] EEC X G)}
  {Fm : ∀ u, Formalism.L2.Forms.Forms0 D u} {Tr : ∀ u, Transport X u (Fm u)}
  {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs}
  {P : CxData A} {fc : DefSub A → DefFace Bs}
  {eV : ∀ t, (Fin ((fc P.zs).Df1.nV t) → K) →ₗ[K] A.FR t} {sEE : P.EE →ₗ⋆[ℂ] (fc P.zs).Sp.HH}
  {s : Bool} {σ : K →+* ℂ}
end At
section Ties
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {R : _root_.Formalism.L2.RecTAlt ex}
def spectralRowIsometry (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R) (hF : FinX S.Y) : D.what₂.EE ≃ₗᵢ[ℂ] EEC S.X S.G :=
  Classical.choose (S.rowTie hF)
theorem eHH_sEE_eq_conjHH_isometryOfJoin (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R) (hF : FinX S.Y) (F : D.what₂.EE) :
    (S.hI hF).eHH (D.sEE F) = conjHH S.X S.G (_root_.Formalism.L2.SG.JoinSI.spectralRowIsometry S hF F) :=
  Classical.choose_spec (S.rowTie hF) F
theorem isometryOfJoin_eq_of_conj_compat (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R) (hF : FinX S.Y) (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC S.X S.G)
    (hj : ∀ F, (S.hI hF).eHH (D.sEE F) = conjHH S.X S.G (j F)) : _root_.Formalism.L2.SG.JoinSI.spectralRowIsometry S hF = j := by
  ext1 F
  apply (conjHH S.X S.G).injective
  rw [← _root_.Formalism.L2.SG.JoinSI.eHH_sEE_eq_conjHH_isometryOfJoin S hF F, hj F]
theorem colJoinS_of_spectral_ties_real (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R) (hF : FinX S.Y) : ColJoinS hF (S.hI hF) S.tr :=
  colJoinS_of_pin hF (S.hI hF) S.tr S.into S.bij fun u x =>
    (LinearEquiv.eq_symm_apply (colDict S.X (S.tr u) S.Y.hK (S.into u) (S.bij u))).2 (S.colPin hF u x)
end Ties
section Real
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
abbrev complexRealisationJoinData {R : _root_.Formalism.L2.RecTAlt ex} {P : Formalism.L2.Rows.RowSideFamily ex}
    {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)} {Spf : ∀ Zs, SPer (Dcf Zs)}
    {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3} {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Q : _root_.Formalism.IndefR.IndefiniteRealisation R P Dcf Spf Zscf S Ks) :=
  Q.Rl.toCx3 Q.F
structure IndefiniteRealisationJoin (R : _root_.Formalism.L2.RecTAlt ex) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R) {P : Formalism.L2.Rows.RowSideFamily ex}
    {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)} {Spf : ∀ Zs, SPer (Dcf Zs)}
    {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (Q : _root_.Formalism.IndefR.IndefiniteRealisation R P Dcf Spf Zscf S Ks) where
  m : D.what₂.Word → (Q.F.fc (_root_.Formalism.L2.SG.JoinSI.complexRealisationJoinData Q).zs).Dc.Mem
  mPin : HEq m P.I.wU
  cφ : ∀ u, D.what₂.Mu u ≃ₗ[ℂ] (Fin ((Q.F.fc (_root_.Formalism.L2.SG.JoinSI.complexRealisationJoinData Q).zs).Dc.a (m u)) → ℂ)
  cF : (Fin ((Q.F.fc (_root_.Formalism.L2.SG.JoinSI.complexRealisationJoinData Q).zs).Df1.nV P.A3.fam3.base3.μ0) → ℂ) →ₗ[ℂ] D.what₂.Amb D.what₂.mu0
  eR : D.what₂.EE →ₛₗ[Formalism.IndefR.Links.cj (twQ P)] (_root_.Formalism.L2.SG.JoinSI.complexRealisationJoinData Q).EE
  chainTie : ChainTieT (P := _root_.Formalism.L2.SG.JoinSI.complexRealisationJoinData Q) (fc := Q.F.fc) (σ := D.what₂.embLL) (m := m) (cφ := cφ) (cF := cF)
  v0Surjective : GoodPartHasComplexCoordinates (P := _root_.Formalism.L2.SG.JoinSI.complexRealisationJoinData Q) (fc := Q.F.fc) (cF := cF)
  rowTie : RowTieT (P := _root_.Formalism.L2.SG.JoinSI.complexRealisationJoinData Q) (fc := Q.F.fc) (eV := Q.F.eV (_root_.Formalism.L2.SG.JoinSI.complexRealisationJoinData Q).zs) (s := twQ P) (σ := D.what₂.embLL) (cF := cF) (eR := eR)
  colNorm : ColNormT (P := _root_.Formalism.L2.SG.JoinSI.complexRealisationJoinData Q) (fc := Q.F.fc) (s := twQ P) (m := m) (cφ := cφ)
  pairTie : ∀ hF : FinX S.Y, PairTieT (X := S.X) (G := S.G) (j := _root_.Formalism.L2.SG.JoinSI.spectralRowIsometry S hF) (Tr := S.tr) (hK := S.Y.hK) (Dt := S.Y.Dt)
    (P := _root_.Formalism.L2.SG.JoinSI.complexRealisationJoinData Q) (fc := Q.F.fc) (sEE := Q.sEE) (s := twQ P) (m := m) (cφ := cφ) (eR := eR)
variable {R : _root_.Formalism.L2.RecTAlt ex} {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R} {P : Formalism.L2.Rows.RowSideFamily ex}
  {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)} {Spf : ∀ Zs, SPer (Dcf Zs)}
  {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {Q : _root_.Formalism.IndefR.IndefiniteRealisation R P Dcf Spf Zscf S Ks}
theorem embedding_eq_cj_twQ_embLL (Q : _root_.Formalism.IndefR.IndefiniteRealisation R P Dcf Spf Zscf S Ks) (a : D.what₂.LL) :
    P.A3.fam3.base3.v0.embedding a = Formalism.IndefR.Links.cj (twQ P) (D.what₂.embLL a) :=
  twist_of_mk D.what₂.embLL P.A3.A.v0 Q.Rl.hv0 a
def IndefiniteRealisationJoin.toJoinAt (J : _root_.Formalism.L2.SG.JoinSI.IndefiniteRealisationJoin R S Q) :
    JoinAt S.X S.G S.Y (_root_.Formalism.L2.SG.JoinSI.spectralRowIsometry S) S.tr (_root_.Formalism.L2.SG.JoinSI.complexRealisationJoinData Q) Q.F.fc (Q.F.eV (_root_.Formalism.L2.SG.JoinSI.complexRealisationJoinData Q).zs) Q.sEE (twQ P) D.what₂.embLL where
  m := J.m
  cφ := J.cφ
  cF := J.cF
  eR := J.eR
  twist := _root_.Formalism.L2.SG.JoinSI.embedding_eq_cj_twQ_embLL Q
  chainTie := J.chainTie
  v0Surjective := J.v0Surjective
  rowTie := J.rowTie
  colNorm := J.colNorm
  pairTie := J.pairTie
end Real
end Formalism.L2.SG.JoinSI
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealTB
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
namespace Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}
set_option genInjectivity false in
set_option genSizeOfSpec false in
structure RealTBAlt (Rc : _root_.Formalism.L2.RecTAlt ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs))
    (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3)
    (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) : Type 1 where
  T : CoreJ D
  [alg : Algebra T.Q.c.F D.what₂.LL]
  Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S T.Q.c.F
  κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)
  v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Q.Rl.toRealDat.MW i σ).Vec
  fw : FWTie T Q.Rl.toRealDat κ v₀
  bar : BarTie fw
  O : ∀ i, OMDat T.toCore Q.Rl.toRealDat i Unit (fun _ => P.A3.A.μ0)
  pins : ∀ i, OMPins T Q.Rl.toRealDat κ v₀ O i
  rhoGeo : RhoGeo fw O
  equivAll : EquivAll T Q.Rl.toRealDat κ O
  cTie : ∀ i, CTie T Q.Rl.toRealDat κ v₀ O i
  phase : ∀ i, Q.Rl.toRealDat.LUnif → PhaseTie T Q.Rl.toRealDat κ v₀ O (phEff Q.Rl) i
attribute [instance] _root_.Formalism.IndefR.RealTBAlt.alg
variable {Rc : _root_.Formalism.L2.RecTAlt ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
  {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc}
structure IndefiniteRealisationBoundedRows (B : _root_.Formalism.IndefR.RealTBAlt Rc P Dcf Spf Zscf S) : Prop where
  ioExt : IoExt B.Q.Rl.toRealDat
  oneMap : ∀ i, OneMapRowR B.T B.Q.Rl.toRealDat B.κ B.v₀ B.O (phEff B.Q.Rl) i
end Formalism.IndefR
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaDataExists
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.HeightCounting.Up
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N _root_.Formalism.L2 _root_.Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting
  GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting
attribute [local instance] Formalism.BasicNotions.Host.cmStar
abbrev LayPAlt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) : Type 1 :=
  ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl)
    (p0 : BaseLevelRowSide (w.D Z)) (t : RowsT K w Z Wt p0) (nch : NChoice (w.D Z)) (n : NchT w Z Wt nch), _root_.GlobalTheory.Mem.Top.Bl.NormChoiceCore hL t n → Prop
def MemberAtLayerPoint (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.HeightCounting.Up.LayPAlt hL) : Prop :=
  EvLgG fun K B f T => KPx B f → ∀ w Z Wt p0 t nch n xd c, Nonempty (_root_.GlobalTheory.HeightCounting.defaultExtension hL K B f T w Z Wt p0 t nch n xd c) → Nonempty (RXs t) →
    ColPin w → p K B f T w Z Wt p0 t nch n c
structure PinnedAtCharacterChoice {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch}
    (a : _root_.GlobalTheory.Mem.Top.Bl.NAtData hL D cf nch tp) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) : Prop where
  cf_eq : P.cf = cf
  C_eq : P.C = nch
  tp_eq : HEq P.tp tp
  rep_eq : HEq P.rep a.nt.rep
  M_eq : P.M = a.all.gal.mt
  lab : GlobalTheory.PendOf.LabAll D P.T
  green : GlobalTheory.PendOf.GreenLab P.ty.grp
  chiT : ChiTOk D P.cf
def ParameterStatement (hL : _root_.UpperTheory.Zero.LLC.RecTExists) : Prop :=
  AllSt fun _ _ _ _ _ _ x => ∀ l : _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x, GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.GoodRowCuspParam (Dof x) l.a.A.row
def ThetaDataExists (hL : _root_.UpperTheory.Zero.LLC.RecTExists) : Prop :=
  AllSt fun _ _ _ _ _ _ x => _root_.GlobalTheory.HeightCounting.Up.SecondIntermediateLevel hL x → ∃ xd : ThData (Dof x), XdAll xd
def PointStatement (hL : _root_.UpperTheory.Zero.LLC.RecTExists) : Prop :=
  AllSt fun _ _ _ _ _ _ x => ∀ l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x, _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' =>
    (SumRepresentations.hypO D' → _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D' ∧ AutomorphicSideWildInertia.ResidualIrreducibleGood D' ∧ SumRepresentations.Conclusion42 D' ∧ SumRepresentations.ConclusionZ D') ∧ D'.nd.EigSpan ∧ Rows.IsotInternal D'.what₂
end GlobalTheory.HeightCounting.Up
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealPins
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR.Links Formalism.IndefR.Cx
namespace Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}
open Classical in
structure IndefiniteRealisationNormalisation {Rc : _root_.Formalism.L2.RecTAlt ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
    {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
    {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) : Prop where
  cfEq : Q.Rl.C = Rc.T.n.cf
  qGuard : Formalism.IndefR.FWT.QGuard Q.Rl.toRealDat
  hF : D.host.F = maximalRealSubfield D.host.E
  phsOne : ∀ i, Q.Rl.phs i = 1
  prXunit : Formalism.IndefR.Seed.PrIso Q.Rl.MX Q.Rl.cX Q.Rl.prX
  grpRecPin : ∃ (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ Q.Rl.toRealDat.Pg)
      (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1),
    (∀ kv, ((plg kv : Q.Rl.toRealDat.Pg) : Pl D.host.E) = D.naut.plGw kv.1 kv.2) ∧
    (∀ g, D.what₂.embLL ((idemOf P.A3.A.X).coeff g) = D.ntypes.e0.coeff ((Q.Rl.eG.trans Q.cG) g)) ∧
    (∀ kv, Q.Rl.toRealDat.C.P.Div kv.1 (plg kv).1) ∧
    ∀ g kv, Q.Rl.toRealDat.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) ((Q.Rl.eG.trans Q.cG) g kv)
  fdiag : ∀ i, IsFDiag (Wc D i) ∧ IsFDiag (Vc D i)
  pgEq : Q.Rl.Pg = Rc.T.ker.Pr.vGs.image (Formalism.L2.Host.CT.plMap Rc.T.ker.seam.iE)
  tSfin : Q.tS ∈ Formalism.L2.Theta.GfC (Yc D 0)
  tSpin : (∃ t ∈ Formalism.L2.Theta.GfC (Yc D 0), Formalism.IndefR.AutomorphicEvaluation.ConjLevel t⁻¹ (levS _ (Q.Rl.βY 0) (Q.Rl.dat0 (Q.Rl.toRealDat.levR (faceT P Dcf Spf Zscf).lv2 true))) (Formalism.IndefR.Lev.levChi _ (Q.Rl.βY 0) (Q.Rl.dat0 (Q.Rl.toRealDat.levR (faceT P Dcf Spf Zscf).lv2 true))) (Q.ιS ⁻¹' seeKS S.X) (fun k => seeChiS S.X (Q.ιS k)) ∧
      Formalism.L2.SG.RowLevelMatch.RowLevelMatchAt Q.Rl.toRealDat (faceT P Dcf Spf Zscf).lv2 S.X Q.instEq t) →
    Formalism.IndefR.AutomorphicEvaluation.ConjLevel Q.tS⁻¹ (levS _ (Q.Rl.βY 0) (Q.Rl.dat0 (Q.Rl.toRealDat.levR (faceT P Dcf Spf Zscf).lv2 true))) (Formalism.IndefR.Lev.levChi _ (Q.Rl.βY 0) (Q.Rl.dat0 (Q.Rl.toRealDat.levR (faceT P Dcf Spf Zscf).lv2 true))) (Q.ιS ⁻¹' seeKS S.X) (fun k => seeChiS S.X (Q.ιS k)) ∧
      Formalism.L2.SG.RowLevelMatch.RowLevelMatchAt Q.Rl.toRealDat (faceT P Dcf Spf Zscf).lv2 S.X Q.instEq Q.tS
  eGtie : P.I.eG = Q.Rl.eG.trans Q.cG
  betaStd : (∀ i, Q.Rl.βV i = 1) ∧ Q.Rl.βX = 1
  bR_read : ∀ x i, Q.bR x i = D.eMu (Q.wdD x) (D.jN (Q.wdD x) (P.I.eNu (Q.wdD x)
    (Pi.single (Fin.cast (congrArg P.Dc.a (Q.wU_wdD x)).symm i) 1)))
variable {Rc : _root_.Formalism.L2.RecTAlt ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
  {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
def IndefiniteRealisationExtends (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) : Prop :=
  (∃ t ∈ Formalism.L2.Theta.GfC (Yc D 0), Formalism.IndefR.AutomorphicEvaluation.ConjLevel t⁻¹ (levS _ (Q.Rl.βY 0) (Q.Rl.dat0 (Q.Rl.toRealDat.levR (faceT P Dcf Spf Zscf).lv2 true))) (Formalism.IndefR.Lev.levChi _ (Q.Rl.βY 0) (Q.Rl.dat0 (Q.Rl.toRealDat.levR (faceT P Dcf Spf Zscf).lv2 true))) (Q.ιS ⁻¹' seeKS S.X) (fun k => seeChiS S.X (Q.ιS k)) ∧
      Formalism.L2.SG.RowLevelMatch.RowLevelMatchAt Q.Rl.toRealDat (faceT P Dcf Spf Zscf).lv2 S.X Q.instEq t) ∧
    ∃ c' : ℝ, Formalism.IndefR.AutomorphicEvaluation.EvalTieT (Q.Rl.MY 0) Q.Rl.ν0 Q.Rl.fd0 (Q.Rl.toRealDat.EEat (Q.Rl.toRealDat.levR (faceT P Dcf Spf Zscf).lv2 true)) S.X S.G Q.ιS Q.tS c'
end Formalism.IndefR
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealRec
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
theorem finrank_WL_eq_dW (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) (i : Fin D.R.m) :
    Module.finrank D.what₂.LL (Q.Rl.toRealDat.WL Q.F.lv2 false i) = (P.A3.indefDown P.S0).dW i :=
  congrFun (dW_of_heq (congrArg (fun Z => P.A3.side3 P.P0 P.ψ0 Z) Q.zs) Q.s0) i
def indefiniteDownJoin (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) (i : Fin D.R.m) (y : Fin ((P.A3.indefDown P.S0).dW i) → D.what₂.LL) :
    Fin (Q.Rl.nW i) → D.what₂.LL :=
  Formalism.IndefR.NX.jDL Q.Rl Q.F.lv2 i (y ∘ Fin.cast (_root_.Formalism.IndefR.finrank_WL_eq_dW Q i))
set_option genInjectivity false in
set_option genSizeOfSpec false in
structure IndefiniteRealisationRecursion (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) : Type 1 where
  tupT : D.what₂.Tup → P.T
  hm : 0 < D.R.m
  hTop : Formalism.IndefR.RecTie.TopMultH Q.Rl.toRealDat
  hinj : ∀ i t, Function.Injective (Q.Rl.toRealDat.extV i t)
  Ish : Formalism.IndefR.RecTie.RowIds (Formalism.BasicNotions.RowSide.sharp D) (Formalism.IndefR.RecTie.toChainReal Q.Rl.toRealDat (faceT P Dcf Spf Zscf).lv2 tupT hm hTop) true
  I0 : Formalism.IndefR.RecTie.RowIds ex.p0.s (Formalism.IndefR.RecTie.toChainReal Q.Rl.toRealDat (faceT P Dcf Spf Zscf).lv2 tupT hm hTop) false
  IL : Formalism.IndefR.RecTie.LiftIds (Formalism.IndefR.RecTie.toLiftReal Q.Rl.toRealDat (faceT P Dcf Spf Zscf).lv2 tupT hm hTop hinj)
  Kc : Formalism.IndefR.RecTie.ColReal D
  E : EigIdx D Y
  labPi : E.Pi → P.A3.A.fam.base.Ix
  PY : Formalism.IndefR.principalLevelFrame.RowPsi (Yc D 0) D.R.r
  PW : ∀ i, Formalism.IndefR.principalLevelFrame.RowPsi (Wc D i) D.R.r
  eFT : D.what₂.FT ≃ Formalism.IndefR.principalLevelFrame.FTR Q.Rl.θ PY (Q.Rl.MY 0)
    (fun b => levS _ (Q.Rl.βY 0) (Q.Rl.dat0 (Q.Rl.levR (faceT P Dcf Spf Zscf).lv2 b)))
    (fun b => Formalism.IndefR.Lev.levChi _ (Q.Rl.βY 0) (Q.Rl.dat0 (Q.Rl.levR (faceT P Dcf Spf Zscf).lv2 b))) (fun _ => Q.Rl.e0)
  piOf : E.Pi → HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ
  ιW : ∀ i, ↥(Formalism.L2.Theta.GfC (Yc D 0)) →* ↥(Formalism.L2.Theta.GfC (Wc D i))
  Tp : Formalism.L2.Host.TupTied D Q.Rl.C ex.nch
  recR : Formalism.IndefR.RecTie.RecReal Q.Rl.toRealDat (faceT P Dcf Spf Zscf).lv2 tupT hm hTop hinj ex.p0 Ish I0 IL Kc E labPi PY PW eFT piOf ιW ex.nch Tp
  tpEq : HEq Tp Rc.T.n.tp
  tupTie : ∀ μ, Formalism.IndefR.RecTie.Used0 D μ → P.I.tup (tupT μ) = μ
  tupT_tup : ∀ t, tupT (P.I.tup t) = t
  muEq : Q.Rl.mu = P.S0.μ
  mtRead : Formalism.IndefR.RecTie.MtRead Q.Rl.toRealDat Q.F.lv2 tupT hm hTop hinj IL (twPOf P tupT tupTie)
  mjRead : Formalism.IndefR.RecTie.MjRead Q.Rl.toRealDat Q.F.lv2 tupT hm hTop hinj IL (fun i => (P.A3.indefDown P.S0).dW i)
    (fun i y => P.I.jW i y) (_root_.Formalism.IndefR.indefiniteDownJoin Q)
namespace RealRec
variable {Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks} (Qr : _root_.Formalism.IndefR.IndefiniteRealisationRecursion Q)
theorem _root_.Formalism.IndefR.IndefiniteRealisationRecursion.tupT_inj_used {μ μ' : D.what₂.Tup} (hμ : Formalism.IndefR.RecTie.Used0 D μ) (hμ' : Formalism.IndefR.RecTie.Used0 D μ')
    (h : Qr.tupT μ = Qr.tupT μ') : μ = μ' := by
  apply Qr.Tp.xi_inj
  rw [← Qr.recR.tupXi μ hμ, ← Qr.recR.tupXi μ' hμ', h]
theorem _root_.Formalism.IndefR.IndefiniteRealisationRecursion.tupleRead_baseTuple_eq_family : Qr.tupT D.what₂.mu0 = P.A3.A.μ0 :=
  Q.charW.base.lev.xi_inj (by rw [Qr.recR.tupXi D.what₂.mu0 (Or.inl rfl), Qr.Tp.trueColumnChoices_heckeChar_reference_eq_one, Q.charW.base.lev.xi_base])
theorem _root_.Formalism.IndefR.IndefiniteRealisationRecursion.tw_iff (Qr : _root_.Formalism.IndefR.IndefiniteRealisationRecursion Q) (w : D.what₂.places.Pl) : D.plEq w ∈ Q.Rl.twPl ↔ D.what₂.muAt w ≠ D.what₂.mu0 := by
  have h0 := Qr.tupleRead_baseTuple_eq_family
  constructor
  · intro hw he
    apply Q.charW.tup.mu_ne (D.plEq w) hw
    rw [← Qr.recR.tupAt w, he, h0]
  · intro hne
    by_contra hw
    apply hne
    apply Qr.tupT_inj_used (Or.inr ⟨w, rfl⟩) (Or.inl rfl)
    rw [Qr.recR.tupAt w, Q.charW.tup.mu_off (D.plEq w) hw, h0]
end RealRec
namespace RealRec
variable {Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks}
def _root_.Formalism.IndefR.IndefiniteRealisationRecursion.PartsRow (Qr : _root_.Formalism.IndefR.IndefiniteRealisationRecursion Q) : Prop :=
  Formalism.IndefR.RecTie.PartsRec Q.Rl.toRealDat Q.F.lv2 Qr.tupT Qr.hm Qr.PY Qr.PW Qr.eFT Qr.E Qr.labPi Qr.piOf Qr.Ish.prt Qr.IL.prtW
end RealRec
end Formalism.IndefR
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ParLaws
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.HeightCounting.Up
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N _root_.Formalism.L2 _root_.Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting
  GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting
attribute [local instance] Formalism.BasicNotions.Host.cmStar
structure ParityConditions (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (cf : CharFrame D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r)
    (Rw : RowSide D) : Type 1 where
  T : GlobalTheory.RowTie.WDTie D.nd D.naut
  lab : LabTrue D T
  chr : CharSide D cf
  cg : _root_.GlobalTheory.HeightCounting.CGTrueT hL D T
  A : _root_.GlobalTheory.HeightCounting.AUSideAlt D
  au : _root_.GlobalTheory.HeightCounting.AutomorphicSideRealised hL D T A
  row : _root_.GlobalTheory.HeightCounting.RepresentationParametersHold hL D rep (fun σ w => T.e w (Rw.locR σ w)) Rw.satR
def ParityConditions.ofSt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} {cf : CharFrame D} {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r}
    (a : _root_.GlobalTheory.HeightCounting.HeightCountingBaseData hL D cf rep) : _root_.GlobalTheory.HeightCounting.Up.ParityConditions hL D cf rep a.A.row := ⟨a.A.wdT, a.A.lab, a.A.chr, a.cg, a.A.au, a.au, a.row⟩
structure ParityLaws (D : D7) : Prop where
  tie0 : SumRepresentations.tie0 D
  an : SumRepresentations.adm5 D
  temp : _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D
  lab : SumRepresentations.tieLab D
  one : GlobalTheory.RowCopy.HeckeSplitOne D
  cancel : ∀ w (a b c : D.naut.LP w), D.naut.lpSum a c = D.naut.lpSum b c → a = b
  gsp : ∀ (k : Fin 2) (v : D.nd.PlG k), IsSplitPl D.host (D.naut.plGw k v)
end GlobalTheory.HeightCounting.Up
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PtKOfReal
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Module NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2 Formalism.L2.Indef Formalism.L2.DIV Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
namespace Formalism.L2.RowDataTransport
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}
abbrev packageOfPrimitiveLinks [_root_.NumberField.IsTotallyComplex D.what₂.LL] {Rc : _root_.Formalism.L2.RecTAlt ex} {P : RowSideFamily ex}
    {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)} {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)}
    {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3} {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) {s : ℕ} (hOk : P.A3.fam3.Ok3 s) (hsep : P.A3.fam3.TypesSep3) (Cl CHl : ℝ)
    (hP : CovolumeOntoIsometryConditions Q.Rl (faceT P Dcf Spf Zscf) Q.sEE (hkCan P.A3) Cl CHl) (hI : PassIn3 Q.Rl (faceT P Dcf Spf Zscf) Cl CHl) :=
  primitivePackageFullHecke hOk hsep Q.Rl (faceT P Dcf Spf Zscf) Q.sEE (hkCan P.A3) Cl CHl Q.charW hP hI
def InpAtAlt [_root_.NumberField.IsTotallyComplex D.what₂.LL] {Rc : _root_.Formalism.L2.RecTAlt ex} {P : RowSideFamily ex} {X : Formalism.L2.Col.Fields}
    {e : X.Tau → (X.E →+* D.what₂.LL)} (c : ColRec3 (fieldsLL D X e) P.A3 P.Ps P.ψs)
    {Sp : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (c.face Zs)} {Zsc : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
    {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P c.face Sp Zsc S Ks) {s : ℕ} (hOk : P.A3.fam3.Ok3 s) (hsep : P.A3.fam3.TypesSep3) (Cl CHl : ℝ)
    (hP : CovolumeOntoIsometryConditions Q.Rl (faceT P c.face Sp Zsc) Q.sEE (hkCan P.A3) Cl CHl) (hI : PassIn3 Q.Rl (faceT P c.face Sp Zsc) Cl CHl)
    (Del h0 : ℕ) (lam0 C0 ce Ch Sw C1 : ℝ) (eJ : P.A3.fam3.base3.J ≃ Fin D.R.m)
    (H : ∀ u, (ofRecord D L Del h0).NumFacts (letterOf D L Del h0 u) L.Nc lam0 C0 ce Ch Sw C1) : Prop :=
  ∀ (NuC : ∀ w, Submodule (𝓞 D.what₂.LL) (Fin ((c.face (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).Zs).a w) → D.what₂.LL))
      (I : DivisionCompatibilityDataThreeSided D P.A3 P.P0 P.ψ0 P.Ps P.ψs (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).Zs
        (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).core.base.toIndefData (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).core.cols.toIndefData ex.p0
        (c.face (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).Zs)),
      DivTied3 D P.A3 P.P0 P.ψ0 P.Ps P.ψs (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).Zs
        (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).core.base.toIndefData (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).core.cols.toIndefData ex.p0
        (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).core.cols.col NuC I →
      HEq I P.I →
      ∃ inp : ∀ u, DivInputs0R (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).core
          (RecNums.ofNum (ofRecord D L Del h0) eJ (letterOf D L Del h0 u) ((D.mem u).A.T) L.Nc lam0 C0 ce Ch Sw C1 (H u))
          (I.wU u) (Cons.nuOf L u (I.eNu u)) (sgRec L u),
        ∃ hQ : ∀ u, ChainTie (inp u).ch (c.memQ (I.wU u)), ∀ u, FirstCols c.hE (hQ u)
theorem ptK_of_real_alt [_root_.NumberField.IsTotallyComplex D.what₂.LL] (Rc : _root_.Formalism.L2.RecTAlt ex) (R : _root_.Formalism.L2.DIV.DivisionKernelData ex) (hT : R.T = Rc.T)
    (hpin : _root_.Formalism.L2.Rows.RowSideDeterminedAlt Rc.T R.P) (hkap : RowsHoldKap3 R.P) (hPt : RowsHoldDcPt3 R.P)
    (hR : DivRows3 D R.P.A3 R.P.P0 R.P.ψ0 R.P.Ps R.P.ψs R.P.Zs R.P.S0 R.P.S1 ex.p0 R.P.C R.P.NuC R.P.I) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc R.P R.c.face R.Sp R.Zsc S Ks) (hsep : R.P.A3.fam3.TypesSep3) (Cl CHl : ℝ)
    (hP : CovolumeOntoIsometryConditions Q.Rl (faceT R.P R.c.face R.Sp R.Zsc) Q.sEE (hkCan R.P.A3) Cl CHl)
    (hI : PassIn3 Q.Rl (faceT R.P R.c.face R.Sp R.Zsc) Cl CHl)
    (C Cabs : ℝ) (Del h0 : ℕ) (hDel : D.s.Del = (Del : ℚ)) (hh0 : L.etaSz = (D.R.m : ℝ) * (h0 : ℝ))
    (lam0 C0 ce Ch Sw C1 : ℝ) (eJ : R.P.A3.fam3.base3.J ≃ Fin D.R.m)
    (H : ∀ u, (ofRecord D L Del h0).NumFacts (letterOf D L Del h0 u) L.Nc lam0 C0 ce Ch Sw C1)
    (hInp : _root_.Formalism.L2.RowDataTransport.InpAtAlt R.c Q R.ok1 hsep Cl CHl hP hI Del h0 lam0 C0 ce Ch Sw C1 eJ H)
    (hN : NprimeDef D L) (hh : ∀ u, D.div.h u = hExpl6 D L Y Ch u)
    (hF : FTie L ((Formalism.IndefR.Cx.faceOf3 R.P.A3 R.P.P0 R.P.ψ0 R.P.Ps R.P.ψs R.c.face R.Sp R.Zsc
      (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q R.ok1 hsep Cl CHl hP hI).Zs).Z.num Cl CHl) eJ)
    (hC0 : 0 ≤ C) (hC1 : 50 * C0 + 10 ≤ C) (hC2 : 60 * ce ≤ C) (hCabs : 1 ≤ Cabs) (hLa : 0 ≤ L.La) :
    Nonempty (_root_.Formalism.L2.DIV.DivisionPackageKernel' R C Cabs) := by
  have hZs : (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q R.ok1 hsep Cl CHl hP hI).Zs = R.P.Zs := Q.zs
  have hS0 : HEq (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q R.ok1 hsep Cl CHl hP hI).core.base.toIndefData R.P.S0 := Q.s0
  have hS1 : HEq (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q R.ok1 hsep Cl CHl hP hI).core.cols.toIndefData R.P.S1 := Q.s1
  have hRows : HEq (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q R.ok1 hsep Cl CHl hP hI).core.base.toIndefRows (Classical.choose R.hr.rows0) :=
    rows_heq hZs _ _ (hS0.trans (heq_of_eq (Classical.choose_spec R.hr.rows0).symm))
  have hDc : HEq (R.c.face (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q R.ok1 hsep Cl CHl hP hI).Zs) R.P.Dc :=
    (congr_arg_heq R.c.face hZs).trans (heq_of_eq R.colTie.1)
  exact _root_.Formalism.L2.DIV.pkg_of_rowsK_alt R hR C Cabs Cl CHl _ (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q R.ok1 hsep Cl CHl hP hI) hZs hRows hS1 Q.col
    Del h0 lam0 C0 ce Ch Sw C1 eJ H
    (fun NuC I hT' hI' => ⟨Formalism.L2.G.ServJointF.brTied_of hT' ⟨1, R.ok1.ok2⟩ (dcPt_move hPt hZs hDc hS0 hS1 hI'),
      hInp NuC I hT' hI'⟩)
    hN Y (fun σ => (hkap σ).trans (congrFun (kap_heq hZs hS1) _).symm) (fun u => ⟨rfl, HEq.rfl, rfl, hDel, hh0⟩) hh hF
    hC0 hC1 hC2 hCabs hLa
end Formalism.L2.RowDataTransport
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPins3Iff
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR.Links Formalism.IndefR.Cx
namespace Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}
structure IndefiniteRealisationNormalisationDegreeThree {Rc : _root_.Formalism.L2.RecTAlt ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
    {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
    {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) : Prop where
  muDef : ∀ C CH : ℝ, (Q.Rl.toCx3 Q.F).MuDef Q.F.cr (Q.Rl.num Q.F C CH) Q.Rl.mu
namespace Pins3
variable {Rc : _root_.Formalism.L2.RecTAlt ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
  {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
theorem muDef_iff_alt (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) (C CH : ℝ) :
    (Q.Rl.toCx3 Q.F).MuDef Q.F.cr (Q.Rl.num Q.F C CH) Q.Rl.mu ↔
      ∀ w, w ∈ Q.Rl.twPl ↔ (Q.Rl.toCx3 Q.F).W1 Q.F.cr (Q.Rl.num Q.F C CH) w := by
  have ht := Q.charW.tup
  constructor
  · rintro ⟨_, _, _, h4⟩
    exact h4
  · intro h
    refine ⟨fun w hw => ht.mu_ne w ((h w).2 hw), fun w _ => ht.mu_conj w, fun w => ?_, h⟩
    show Q.Rl.mu w = _
    split_ifs with hw
    · rfl
    · exact ht.mu_off w fun hm => hw ((h w).1 hm)
theorem realPins3_iff_twPl_iff_W1 (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) :
    _root_.Formalism.IndefR.IndefiniteRealisationNormalisationDegreeThree Q ↔ ∀ w, w ∈ Q.Rl.twPl ↔ (Q.Rl.toCx3 Q.F).W1 Q.F.cr (Q.Rl.num Q.F 0 0) w :=
  ⟨fun h => (_root_.Formalism.IndefR.Pins3.muDef_iff_alt Q 0 0).1 (h.muDef 0 0), fun h => ⟨fun C CH => (_root_.Formalism.IndefR.Pins3.muDef_iff_alt Q C CH).2 h⟩⟩
end Pins3
namespace RealPins3
variable {Rc : _root_.Formalism.L2.RecTAlt ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
  {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks}
theorem _root_.Formalism.IndefR.IndefiniteRealisationNormalisationDegreeThree.w1 (h : _root_.Formalism.IndefR.IndefiniteRealisationNormalisationDegreeThree Q) (C CH : ℝ) :
    ∀ w, (Q.Rl.toCx3 Q.F).W1 Q.F.cr (Q.Rl.num Q.F C CH) w → w ∈ Q.Rl.twPl :=
  fun w hw => (h.muDef C CH).2.2.2 w |>.2 hw
end RealPins3
end Formalism.IndefR
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BaseRankEqOfRealisation
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Module
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR.Links Formalism.IndefR.Cx
namespace Formalism.IndefR.LevelRealisationRankEquality
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}
variable {Rc : _root_.Formalism.L2.RecTAlt ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
  {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
theorem indefinite_realisation_base_rank_eq (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) :
    D.what₂.D0 = (P.A3.A.fam.R P.A3.A.fam.μ0).dZ (P.A3.A.fam.lvl P.P0 P.ψ0) (P.Zs.Z P.A3.A.fam.μ0) := by
  have hD := D_of_heq (congrArg (fun Z => P.A3.side3 P.P0 P.ψ0 Z) Q.zs) Q.s0
  have hz : (P.A3.side3 P.P0 P.ψ0 (Q.Rl.toCx3 (faceT P Dcf Spf Zscf)).zs).dQ P.A3.fam3.base3.μ0 =
      (P.A3.side3 P.P0 P.ψ0 P.Zs).dQ P.A3.fam3.base3.μ0 := by rw [Q.zs]
  rw [base_rank_eq_of_tied_level P, ← hD]
  exact hz
theorem indefinite_realisation_mu_eq (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) : Q.Rl.mu = P.S0.μ :=
  mu_of_heq (congrArg (fun Z => P.A3.side3 P.P0 P.ψ0 Z) Q.zs) Q.s0
theorem tup_all_used_of_realisation (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) : TupAllUsed P := by
  apply tupAllUsed_of_cover
  intro t
  rcases Q.charW.tup.mu_used t with h | ⟨w, h⟩
  · exact Or.inl h
  · refine Or.inr ⟨D.plEq.symm w, ?_⟩
    show t = P.S0.μ (D.plEq (D.plEq.symm w))
    rw [← _root_.Formalism.IndefR.LevelRealisationRankEquality.indefinite_realisation_mu_eq Q, Equiv.apply_symm_apply]
    exact h.symm
end Formalism.IndefR.LevelRealisationRankEquality
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NXNMjT
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR.Links Formalism.IndefR.Cx
namespace Formalism.IndefR.NX
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}
  {Rc : _root_.Formalism.L2.RecTAlt ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
  {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
set_option synthInstance.maxHeartbeats 400000 in
def RealExpansionMajorant (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) (cG : Formalism.L2.DIV.G0 Q.Rl.Pg D.R.r ≃* G0g D.nd) (Sd : RatDat D.ntw)
    (Yr : NExpRealS Q.Rl cG Sd) (c : NChoice D) :
    Prop :=
  ∃ jD : ∀ j, (Y.MjH j).V →ₗ[D.what₂.LL] Sd.WL j,
    (∀ (i : Fin D.R.m) (x : (Y.MjH ((i : ℕ) + 1)).V)
      (y : Fin (Module.finrank D.what₂.LL (Q.Rl.toRealDat.WL Q.F.lv2 false i)) → D.what₂.LL),
      HEq ((P.JM.eW i).symm x) y → (Yr.fi i).e (jD ((i : ℕ) + 1) x) = jDL Q.Rl Q.F.lv2 i y) ∧
    Nonempty (NMjRR Q.Rl cG Sd Yr Y c jD)
end Formalism.IndefR.NX
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsTheta
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
namespace GlobalTheory.HeightCounting.ThetaSt
section Gen
variable {D : D7}
theorem res_xiBar_alt (kv : Σ k : Fin 2, D.nd.PlG k) {PP : Pl D.host.E} (e : PP = D.naut.plGw kv.1 kv.2)
    (res : kP PP ≃+* ZMod (D.host.g kv.1)) : res (xiBar D PP) = NX.xiRed D kv := by
  subst e
  obtain ⟨a, c, hc, hac, hmem⟩ := Formalism.IndefR.NX.xiRed_isXiRes D kv
  have h1 := Formalism.L2.Col.reduction_spec (D.naut.plGw kv.1 kv.2) (a := D.host.xi0) (r := a) (s := c) hc (by
    change (c : D.host.E) * D.host.xi0 = (a : D.host.E)
    rw [hac, mul_comm])
  have h2 : Ideal.Quotient.mk (D.naut.plGw kv.1 kv.2).asIdeal (((NX.xiRed D kv).val : ℕ) : 𝓞 D.host.E) *
      Ideal.Quotient.mk (D.naut.plGw kv.1 kv.2).asIdeal c = Ideal.Quotient.mk (D.naut.plGw kv.1 kv.2).asIdeal a := by
    rw [← map_mul, Ideal.Quotient.eq]
    exact hmem
  have hc0 : Ideal.Quotient.mk (D.naut.plGw kv.1 kv.2).asIdeal c ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have h3 : Formalism.L2.Col.redP (D.naut.plGw kv.1 kv.2) D.host.xi0 =
      Ideal.Quotient.mk (D.naut.plGw kv.1 kv.2).asIdeal (((NX.xiRed D kv).val : ℕ) : 𝓞 D.host.E) := by
    apply mul_left_cancel₀ hc0
    rw [h1, ← h2, mul_comm]
  show res (Formalism.L2.Col.redP _ D.host.xi0) = _
  rw [h3, map_natCast, map_natCast, ZMod.natCast_zmod_val]
theorem exists_theta_ne_one_psiU_eq_psi0_inv {G : Type} [Group G] {P0 : Subgroup G} {ψ0 : P0 →* D.what₂.LLˣ} {Ps : Subgroup G} {ψs : Ps →* D.what₂.LLˣ}
    {eG : G ≃* G0g D.nd} (h : PsiPPTie D P0 ψ0 Ps ψs eG) (ζ : Fin 2 → ↥D.LL0)
    (hζ : ∀ k, D.what₂.embLL (ζ k : D.what₂.LL) = Complex.exp (2 * Real.pi * Complex.I / (D.host.g k : ℂ))) :
    ∃ θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ, (∀ kk, θ kk ≠ 1) ∧
      (∀ g : G, g ∈ P0 ↔ eG g ∈ Formalism.IndefR.NX.U D.nd) ∧
      ∀ (u : P0) (hu : eG u ∈ Formalism.IndefR.NX.U D.nd),
        (((psiUOf D.nd (NX.xiRed D) θ ⟨_, hu⟩ : (↥D.LL0)ˣ) : ↥D.LL0) : D.what₂.LL) =
          (((ψ0 u)⁻¹ : D.what₂.LLˣ) : D.what₂.LL) := by
  have hp := pow_of_emb ζ hζ
  obtain ⟨Pg, pl, res, ψ, eC, hT, hW⟩ := h
  refine ⟨thOf ζ hp, fun k hk => ?_, fun g => ?_, fun u hu => ?_⟩
  ·
    have hg1 : 1 < D.host.g k := (D.host.g_prime k).one_lt
    have : Fact (1 < D.host.g k) := ⟨hg1⟩
    have e := congrArg (fun f : Multiplicative (ZMod (D.host.g k)) →* (↥D.LL0)ˣ =>
      (((f (Multiplicative.ofAdd 1) : (↥D.LL0)ˣ) : ↥D.LL0) : D.what₂.LL)) hk
    simp only [thOf_val, ZMod.val_one, pow_one, MonoidHom.one_apply, Units.val_one] at e
    have e' : (ζ k : D.what₂.LL) = 1 := by
      have := congrArg (·⁻¹) e
      simpa using this
    have e2 := congrArg D.what₂.embLL e'
    rw [hζ, map_one] at e2
    exact ((Complex.isPrimitiveRoot_exp (D.host.g k) (D.host.g_prime k).ne_zero).ne_one hg1) e2
  ·
    rw [hT.p0, mem_U]
    change (∀ PP ∈ Set.univ, eC g PP ∈ unip _ _) ↔ _
    simp only [Set.mem_univ, forall_true_left]
    rw [pl.surjective.forall]
    refine forall_congr' fun kv => ?_
    rw [hT.comp g kv]
    have e : ∀ a b : Fin D.R.r, (Matrix.GeneralLinearGroup.map (res kv).toRingHom (eC g (pl kv))).val a b =
        res kv ((eC g (pl kv)).val a b) := fun _ _ => rfl
    simp only [e, EmbeddingLike.map_eq_zero_iff, EmbeddingLike.map_eq_one_iff]
    exact ⟨fun h => ⟨fun a b hab => h.1 hab, h.2⟩, fun h => ⟨fun a b hab => h.1 a b hab, h.2⟩⟩
  ·
    have hu0 : eC u ∈ (Formalism.L2.DIV.P0 Pg D.R.r ψ).H := (hT.p0 u).1 u.2
    rw [hT.chi0 u hu0, Units.val_inv_eq_inv_val, baseLevelCharacter_eq_prod_superdiagonalSum]
    have hfac : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ψ (pl kv).1 (edgeSum supEdge (eC u (pl kv))) =
        (ζ kv.1 : D.what₂.LL) ^ (NX.xiRed D kv * Formalism.L2.NX.supSum D.R.r
          (((eG u : G0g D.nd) kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))).val := by
      intro kv
      have hres : res kv (xiBar D (pl kv).1 * edgeSum supEdge (eC u (pl kv))) = NX.xiRed D kv * Formalism.L2.NX.supSum D.R.r
          (((eG u : G0g D.nd) kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) := by
        rw [map_mul, _root_.GlobalTheory.HeightCounting.ThetaSt.res_xiBar_alt kv (hT.place kv), hT.comp u kv, supSum_map]
        rfl
      rw [← hres]
      have hb : xiBar D (pl kv).1 * edgeSum supEdge (eC u (pl kv)) =
          (((res kv (xiBar D (pl kv).1 * edgeSum supEdge (eC u (pl kv)))).val : ℤ) : kP (pl kv).1) := by
        apply (res kv).injective
        rw [map_intCast, Int.cast_natCast, ZMod.natCast_zmod_val]
      apply D.what₂.embLL.injective
      rw [hW kv _ _ hb, map_pow, hζ, ← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    have lhs : (((psiUOf D.nd (NX.xiRed D) (thOf ζ hp) ⟨_, hu⟩ : (↥D.LL0)ˣ) : ↥D.LL0) : D.what₂.LL) =
        ∏ kv : (Σ k : Fin 2, D.nd.PlG k), ((ζ kv.1 : D.what₂.LL) ^ (NX.xiRed D kv * Formalism.L2.NX.supSum D.R.r
          (((eG u : G0g D.nd) kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))).val)⁻¹ := by
      rw [psiUOf_apply, Units.coe_prod, IntermediateField.coe_prod]
      exact Finset.prod_congr rfl fun kv _ => thOf_val ζ hp kv.1 _
    rw [lhs, ← Fintype.prod_equiv pl (fun kv => ψ (pl kv).1 (edgeSum supEdge (eC u (pl kv)))) _ (fun _ => rfl),
      Finset.prod_inv_distrib]
    exact congrArg _ (Finset.prod_congr rfl fun kv _ => (hfac kv).symm)
end Gen
section State
variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
end State
theorem main_alt_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P), _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x → ∃ θ : ∀ kk : Fin 2, Multiplicative (ZMod ((Dof x).host.g kk)) →* (↥(Dof x).LL0)ˣ, (∀ kk, θ kk ≠ 1) ∧ LvlPsi x.m.z.R x.m.z.F x.m.z.cG θ := by
  intro hL
  refine StepW.of_all fun K B f T w _ _ _ P x _ => ?_
  have hζ := fun k => roots_g x k
  choose ζ hζ using hζ
  obtain ⟨θ, hne, hlvl, hpsi⟩ := _root_.GlobalTheory.HeightCounting.ThetaSt.exists_theta_ne_one_psiU_eq_psi0_inv x.m.z.pins.keep.psi ζ hζ
  exact ⟨θ, hne, hlvl, hpsi⟩
section Gen
end Gen
end GlobalTheory.HeightCounting.ThetaSt
end
end
end
