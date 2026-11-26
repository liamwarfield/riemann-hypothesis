module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaChr
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmG2TwistSetup

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.STiesR
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.PoincareInHH.PoincareSetting
namespace Formalism.L2.SG.SpectralTiesReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl K Yd cX}
structure STiesRAlt (R : _root_.Formalism.L2.RecTAlt ex) extends STies D where
  tr : ∀ u, Formalism.L2.SG.ColDict.Transport X u ((R.T.cols.forms u).to0)
  into : ∀ u, Formalism.L2.SG.ColDict.ColDictInto X (tr u) Y.hK
  bij : ∀ u, Formalism.L2.SG.ColDict.ColDictBij X (tr u) Y.hK
  lev : ∀ u, Formalism.L2.SG.ColDict.LevelMatch X (tr u) Y.hK
  colPin : ∀ (hF : FinX Y) (u : D.what₂.Word) (x : D.s.Cu u),
    Formalism.L2.SG.ColDict.colDict X (tr u) Y.hK (into u) (bij u) ((hI hF).eCu u x) = D.s_Cu u x
  inst : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D
  G : Formalism.L2.SG.RowDict.GoodOp X
  rowTie : ∀ hF : FinX Y, Formalism.L2.SG.RowDict.RowDictTie X G (hI hF).eHH
  locTied : Formalism.L2.SG.Pf.LocCP.LocTied D
end Formalism.L2.SG.SpectralTiesReal
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreAltAltBis
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.Mem.Top.Bl
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab _root_.Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.GroupRetwisting NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
structure Parameters (hL : _root_.UpperTheory.Zero.LLC.RecTExists) : Type 2 where
  R : RPosition
  N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL
  S : SExt
  Γ : GeoP
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists}
@[reducible] def Parameters.s (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) : Slots := ⟨p.R, _root_.GlobalTheory.Mem.Top.Bl.normChoiceOfExtension hL p.N, SXE p.S, OX p.Γ⟩
def WPt.core_data_of_point {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : WPt p.s K) : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceCore hL q.x.what₂ q.x.n := q.x.nx.1
structure SpectralDataCompatible {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : WPt p.s K) (S : _root_.Formalism.L2.TiedDataSAlt q.O.ex) : Prop where
  host : S.host = q.core_data_of_point.a.host
  cols : S.cols = q.x.col.C
  full : HEq S.full q.x.col.full
  g : HEq S.g q.x.col.g
  theta : (⟨S.provA, S.theta⟩ : Σ a, Formalism.L2.Theta.AllTied (q.w.D q.Z) q.O.ex.th a) = ⟨q.x.th.provA, q.x.th.all⟩
  twE : S.twIn.E = twEOf q.O.ex.xd
  twGood : DQ.GoodAllAt (q.w.D q.Z) q.O.ex.nch S.twIn
  chr : (⟨S.n.cf, S.n.tp⟩ : Σ c : CharFrame (q.w.D q.Z), TupTied (q.w.D q.Z) c q.O.ex.nch) = ⟨TC.cf q.w.I q.w.l q.Z, q.x.n.tp⟩
  gal : S.n.gal = q.core_data_of_point.a.all.gal
  nn : S.n.n = q.core_data_of_point.a.all.n
  exp : S.n.exp = q.core_data_of_point.a.all.exp
  chiD : S.n.chiD = q.core_data_of_point.a.all.chiD
  twF : S.n.twF = q.core_data_of_point.a.all.twF
  types : HEq S.n.types q.core_data_of_point.a.all.types
  cover : HEq S.n.cover q.core_data_of_point.a.all.cover
  plB : S.n.plB = q.core_data_of_point.a.all.plB
  thetaChr : HEq S.thetaChr q.x.th.chr
  dt : ∀ a, S.chrDt.eDt a = (QuotientGroup.mk a : GlobalTheory.Mem.Col2.DtQ q.B.host q.w.I.SQ)
  pieces : S.what₂.O.pieces.rcf = GlobalTheory.Mem.HD.qb S.host.fr.ι q.w.δ.ray ∧ S.what₂.O.pieces.MDel = GlobalTheory.Mem.HD.qb S.host.fr.ι q.w.δ.M'
  inK : S.inK = q.x.div.inK
  geo : HEq S.geo q.x.div.geo
  tw : ∃ he : q.O.ex.tw = q.w.tw q.Z, TC.StdTw q.w.I q.w.l q.Z q.w.l0 (he ▸ S.tw)
abbrev BoundaryReciprocity : GlobalTheory.Fc.BdT := fun _ O _ => _root_.Formalism.L2.RecTAlt O.ex
structure RecordCompatible {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : WPt p.s K) (R : _root_.Formalism.L2.RecTAlt q.O.ex) : Prop where
  s : _root_.GlobalTheory.Mem.Top.Bl.SpectralDataCompatible q R.T.toTiedDataS
  k : KPin q R.T.ker
  crd : ∀ u i hi, R.T.crd u i hi = 1
variable {B : Base} {f : Fr B.toPre} {T : TwDat B}
structure RecordCompatibleExtended {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : WPt p.s K) (R : _root_.Formalism.L2.RecTAlt q.O.ex) : Prop extends toRecPin : _root_.GlobalTheory.Mem.Top.Bl.RecordCompatible q R where
  entC : EntC q.x.ker
  std : GlobalTheory.Svd.StdAt q.w.I q.w.l q.w.l0 q.Z q.O R.T.ker
  rd : GlobalTheory.Pdv.StdRd q.w.I q.w.l q.Z R.T.ker
def ReciprocityLinkage (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) : GlobalTheory.Fc.LkT _root_.GlobalTheory.Mem.Top.Bl.BoundaryReciprocity := linkOf (𝒮 := p.s) (Bd := _root_.GlobalTheory.Mem.Top.Bl.BoundaryReciprocity) fun _ q _ R => _root_.GlobalTheory.Mem.Top.Bl.RecordCompatibleExtended (p := p) q R
@[reducible] def parametersOfExtension (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP) : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL := ⟨RX, N, S, Γ⟩
end GlobalTheory.Mem.Top.Bl
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SelSidePq
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open scoped TensorProduct
namespace Formalism.L2
namespace SelJ
variable {D : D7} {X : Col.Fields}
end SelJ
section
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}
def SelInAlt (R : _root_.Formalism.L2.RecTAlt ex) (Side : Set (HeightOneSpectrum (𝓞 D.host.E))) : Prop :=
  ∀ μ, ∀ P ∈ Col.QE R.T.ker.sel (R.T.ker.tup μ : DIV.Chr R.T.ker.X.F R.T.ker.X.E R.T.ker.X.K),
    ∀ P', SelJ.Carried R.T.ker.seam P P' → P' ∈ Side
def SelectedSideOfPrimeAbove (R : _root_.Formalism.L2.RecTAlt ex)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → HeightOneSpectrum (𝓞 D.host.E)) : Prop :=
  (∀ v, NG.OverPl (Pq v) v) ∧ _root_.Formalism.L2.SelInAlt R (Set.range Pq)
end
end Formalism.L2
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsFurtherTer
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsFurtherTer
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
namespace GlobalTheory.JumpShapeAt
open Classical
theorem main_alt_alt : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂ → ∀ ep, AdmissibleParameterJ.hodgeTateJumpsAtModulesForSign D ep → ∀ i, EmbeddingTypes.admG2 i (X.r i) ep := by
  intro hPr D L P nch HW F Cm X C₂ S ep hJ i h0 h1 w hw C
  have hR : GoodR D.nd i (X.r i) := S.canon.fam.good i
  have hA := S.facts.toCore.admA
  have hg : D.nd.l i ∉ TwistedPlaces.gset D := by
    simp only [TwistedPlaces.gset, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨h0, h1⟩
  have hChi := _root_.GlobalTheory.ChiOneNoPt.main_alt_alt_alt hPr.font D hA.1 hA.2.2.2.1 hA.2.2.2.2.2.2 S.facts.block S.facts.muUnr i hg
  have hG2 := S.facts.g2.1 i (X.r i) hR
  have hcr : ∀ x, IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rO D.nd i (X.r i) x))) :=
    fun x => GlobalTheory.DualTwistCrys.crys_coef D i (X.r i) w hw C x
      (_root_.GlobalTheory.DualTwistCrys.crys_bridge_alt_alt D i (X.r i) hR hG2 h0 h1 w hw x)
  refine ⟨hcr, fun x => GlobalTheory.DualTwistCrys.tw_crys D i (X.r i) w hw C x
    (GlobalTheory.DualTwistCrys.crys_chi D i hChi w hw C) (hcr x), fun τ => ?_⟩
  obtain ⟨g, ρ, hRd, hx, -⟩ := hJ i (X.r i) hR w hw C τ
  have hAJ := S.facts.admJ L S.par
  have hJall : AdmissibleParameterJ.JumpConditions L := _root_.GlobalTheory.JumpStatement.holds_all_alt D L hAJ
  have hj := D.nd.j_range i
  have hint := jj_int D L S.par hAJ.2.2.2.1 i _ g ρ hRd (decide (AdmissibleParameterJ.TypeU D ep g))
  obtain ⟨Cl, Lo, hS⟩ := shape D L S.par hJall.2.1 hJall.2.2.1 _ hj.1 hj.2 ρ _ hint
  refine ⟨Cl, Lo, fun x => ?_⟩
  have hsg : (if EmbeddingTypes.EmbU C ep τ then (1 : ℤ) else -1) = (if decide (AdmissibleParameterJ.TypeU D ep g) then 1 else -1) := by
    by_cases hT : AdmissibleParameterJ.TypeU D ep g
    · rw [if_pos ((embU_iff D i w hw C τ ep g ρ hRd).2 hT), decide_eq_true hT]; rfl
    · rw [if_neg (mt (embU_iff D i w hw C τ ep g ρ hRd).1 hT), decide_eq_false hT]; rfl
  rw [hsg]
  convert hS using 1
  funext a
  rw [(hx x a).2.1]
end GlobalTheory.JumpShapeAt
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsFurtherTerStatement
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admG2_of_setup_jumps : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂ → ∀ ep, AdmissibleParameterJ.hodgeTateJumpsAtModulesForSign D ep → ∀ i, EmbeddingTypes.admG2 i (X.r i) ep := by
  first | exact @_root_.GlobalTheory.JumpShapeAt.main_alt_alt | exact _root_.GlobalTheory.JumpShapeAt.main_alt_alt | (intros; apply _root_.GlobalTheory.JumpShapeAt.main_alt_alt <;> assumption)
end
end
end
