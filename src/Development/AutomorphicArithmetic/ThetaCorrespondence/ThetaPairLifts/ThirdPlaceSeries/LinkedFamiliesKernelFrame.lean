module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesFixedValues
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ResidualIrreducibilityFormsEquivalent
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.ConstituentConditionAtDistinguishedPrime
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalGlobalCompatibility
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPlaceGood
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsHeckeGaloisQOfIsHeckeGaloisStatement

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesKernelFrame
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Matrix Formalism.UG
namespace Formalism.L2
section
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC}
structure TiedDataSKAlt (ex : Extra D L hT Gi Gl K Y cX) extends toTiedDataS : _root_.Formalism.L2.TiedDataSAlt ex where
  ker : Ker.KerEntTied ex
  crd : ∀ (u : D.what₂.Word) i, i ≤ D.R.m → GL (Fin (D.R.N i)) D.host.E
  crd_gram : ∀ u i (hi : i ≤ D.R.m),
    cT (Forms.sigD D : D.host.E →+* D.host.E) (crd u i hi).1 * (crd u i hi).1 = Forms.gramN D i hi
  crd_lat : ∀ u i (hi : i ≤ D.R.m) (x : Fin (D.R.N i) → D.host.E),
    x ∈ Forms.selfDualLatticeCoords D i hi ↔ ∀ a, ((crd u i hi).1 *ᵥ x) a ∈ (algebraMap (𝓞 D.host.E) D.host.E).range
  ker_sharp : ∀ μ, (ker.cst μ).sharp = true
  ker_frm : ∀ u μ i (hi : i ≤ D.R.m) (y : (D.chTw u μ).Y i) (τ : D.what₂.Tau),
    (ker.O u μ).frm i y τ = Forms.atInf (Forms.embT D) (crd u i hi).1 τ * (Forms.twYS tw.ch cols.forms u μ i hi y).1 τ
def ExtraDataSelfDualKernel (ex : Extra D L hT Gi Gl K Y cX) : Prop := Nonempty (_root_.Formalism.L2.TiedDataSKAlt ex)
end
def LinkedFamiliesKernelFrame' : FamClass := fun {_} Fm =>
  ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, _root_.Formalism.L2.ExtraDataSelfDualKernel (Fm.ex x hx i)
theorem LinkedFamiliesKernelFrame'.c2s {eps : ℝ} {Fm : FamP eps} (h : _root_.Formalism.L2.LinkedFamiliesKernelFrame' Fm) : _root_.Formalism.L2.SecondChernLinkedClass Fm := by
  obtain ⟨x0, h⟩ := h
  exact ⟨x0, fun x hx hx0 i => let ⟨T⟩ := h x hx hx0 i; ⟨T.toTiedDataS⟩⟩
end Formalism.L2
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.HeightCounting
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice _root_.Formalism.L2 _root_.Formalism.L2.Host _root_.Formalism.L2.Theta _root_.Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
  Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option genInjectivity false
set_option genSizeOfSpec false
set_option maxHeartbeats 1000000
structure HeightCountingBaseData (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (cf : CharFrame D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) : Type 1 where
  host : HostTied D
  jE : D.host.E →+* Qb
  frame : ∀ x, jE x = host.fr.j x
  A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE
  cg : _root_.GlobalTheory.HeightCounting.CGTrueT hL D A.wdT
  au : _root_.GlobalTheory.HeightCounting.AutomorphicSideRealised hL D A.wdT A.au
  row : _root_.GlobalTheory.HeightCounting.RepresentationParametersHold hL D rep (fun σ w => A.wdT.e w (A.row.locR σ w)) A.row.satR
  fr : OmFrame D
  fr_jE : fr.jE = jE
  pht : PhtOn A.wd fr fun _ _ _ _ => True
  depth : RowDepth D rep
  elem : Elem D
  val : ValLL0 D cf
  labc : LabConj D A.wdT
  zeta : ∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; A.grp.ζ k = (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen
  omax : Function.Injective D.what₂.OtoLL ∧ ∃ F : Subfield D.what₂.LL, ∀ x, x ∈ D.what₂.OtoLL.range ↔ x ∈ F ∧ IsIntegral ℤ x
section Rows
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {C : Formalism.L2.Pj.CoreJ D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat3 D A3 C.Q.c.F}
  {F : Face3 D A3} {X0 : BaseLevelRowSide D} (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) {cf : CharFrame D}
variable {Y cG}
structure SettingsFormsData (a : _root_.GlobalTheory.HeightCounting.HeightCountingBaseData hL D cf (repOf Y)) (n : InRat Y cG)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) : Type 1 where
  Bs : SideB D cf a.A.row (lowAll D) Pq n.S n.In.hL n.In.eig n.In.θ
  Sb_le : ∀ i, n.In.Sb ⊆ D.ntw.S0 i
  rootsOfUnityRing_le_wittIntegers : ∀ i, OverSet D (D.ntw.S0 i) (insert (D.ntw.l i) (lowAll D))
  lam : ∃ Z : GlobalTheory.LamTie.LamDat D, Z.Ok ∧ Z.Teich ∧ Z.C = cf ∧ Z.q0 = AbsolutelyIrreducibleSpan.q0 D ∧ GlobalTheory.LamTie.IsLamTieFull D.ntw Z
variable (g : GlobalTheory.RealGeo.GeoHalf C R.toRealDat fun _ => 1)
structure SeriesData (a : _root_.GlobalTheory.HeightCounting.HeightCountingBaseData hL D cf (repOf Y)) (n : InRat Y cG) (PV : ∀ i : Fin D.R.m, principalLevelFrame.RowPsi (Vc D i) D.R.nV)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) : Type 1 extends toSettingsFormsState : _root_.GlobalTheory.HeightCounting.SettingsFormsData a n Pq where
  YS : NExpRealS R cG n.S
  eF : YS.eF = Bs.eF
  fi : ∀ i x, HEq ((YS.fi i).e x) x
  ser : SerAt YS g.v₀ Bs.exp PV cf Pq
  tau : TauTrue Bs.exp
structure ModuliPointsData (a : _root_.GlobalTheory.HeightCounting.HeightCountingBaseData hL D cf (repOf Y)) (n : InRat Y cG) (PV : ∀ i : Fin D.R.m, principalLevelFrame.RowPsi (Vc D i) D.R.nV)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) : Type 1 extends toSeriesState : _root_.GlobalTheory.HeightCounting.SeriesData g a n PV Pq where
  geo : Nonempty (GlobalTheory.GeoTie.ThetaTie YS g.fw D.nth)
variable {g}
structure HeightCountingCharacterData {a : _root_.GlobalTheory.HeightCounting.HeightCountingBaseData hL D cf (repOf Y)} {n : InRat Y cG} {xi : D.what₂.Tup → HChar D.host.E}
    {Q : D.what₂.places.Pl → Finset (PlE D.host)} (m : InMt Y cf xi Q)
    {Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host} (b : _root_.GlobalTheory.HeightCounting.ModuliPointsData g a n m.ad.PV Pq)
    (k : D.what₂.places.Pl → ℕ) (psi : D.what₂.places.Pl → HChar D.host.E) : Type 1 where
  ch : NChoice D
  tp : TupTied D cf ch
  xi_eq : tp.xi = xi
  psi_eq : tp.psi = psi
  Q_eq : ch.Q = Q
  k_eq : ∀ w, TwistedAt D w → ch.k' w = k w
  side : ChoiceSide D cf m.M b.Bs.exp ch tp
  ok : ∀ w, TwistedAt D w → IntegralHeckeForms.TwOK (ch.twI w) (ch.k' w) (ch.Q w) ((ch.psi' w).comp (D.ntw.art (ch.twI w) (ch.Q w)))
  th : EMtTheta Y b.YS ch
structure RealExpansionExtraData {nch : NChoice D} {tp : TupTied D cf nch} {a : _root_.GlobalTheory.Mem.Top.Bl.NAtData hL D cf nch tp} (r : _root_.GlobalTheory.Mem.Top.Bl.NormRealisationData a R F cG Y)
    (g : GlobalTheory.RealGeo.GeoHalf C R.toRealDat fun _ => 1) (xd : ThData D) : Type 1 where
  ad : MtAd Y a.all.gal.mt
  fi : ∀ i x, HEq ((r.nexp.fi i).e x) x
  hecke : NExpHeckeRowX R cG _ r.nexp r.hecke fun _ => LinearMap.id
  cHk : ∀ i b P, ∃ u : (D.ntw.O i)ˣ, r.hecke.cHk i b 1 P = algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) u
  eig : ∃ Sb e, (∀ i, Sb ⊆ D.ntw.S0 i) ∧ HEq a.nt.eig e ∧ EigAd Y Sb e
  ser : SerAt r.nexp g.v₀ a.all.exp ad.PV cf a.Pq
  tau : TauTrue a.all.exp
  geo : Nonempty (GlobalTheory.GeoTie.ThetaTie r.nexp g.fw D.nth)
  ok : ∀ w, TwistedAt D w → IntegralHeckeForms.TwOK (nch.twI w) (nch.k' w) (nch.Q w) ((nch.psi' w).comp (D.ntw.art (nch.twI w) (nch.Q w)))
  th : EMtTheta Y r.nexp nch
  xd : XdAll xd
  large : GlobalTheory.CoefDuty.Large D
  labc : LabConj a.nt.D a.nt.A.wdT
  zeta : ∀ k, haveI : Fact (a.nt.D.host.g k).Prime := ⟨a.nt.D.host.g_prime k⟩
    a.nt.A.grp.ζ k = (GlobalTheory.Mem.TypePl.labDat (a.nt.D.host.g k)).gen
  pht : ∃ fr : OmFrame a.nt.D, fr.jE = a.nt.jE ∧ PhtOn a.nt.A.wd fr fun _ _ _ _ => True
end Rows
open GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl in
def defaultExtension (hL : _root_.UpperTheory.Zero.LLC.RecTExists) : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL := fun _ _ _ _ w Z _ _ t _ _ xd c =>
  _root_.GlobalTheory.HeightCounting.RealExpansionExtraData (D := (w.st Z).toD7) c.row t.r.z.geo xd
end GlobalTheory.HeightCounting
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HostDatumS
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions
namespace Formalism.L2
namespace Host
end Host
section
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC}
structure HostDatumWithTies {ex : Extra D L hT Gi Gl K Y cX} (T : _root_.Formalism.L2.TiedDataSAlt ex) where
  d3b : Host.PlacesOverCommonPrime D.host
  Tu_g : ∀ u i, (D.mem u).A.T ≠ D.host.g i
  Qw_Tu : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → ∀ v ∈ ex.nch.Q w, ∀ u, ¬ Host.OverP D.host (D.mem u).A.T v
  clsK : Host.ClsRepK D.host
  clsK_Tu : ∀ c u, IsCoprime (clsK.rep c : Ideal (𝓞 D.host.K)) (Host.idK (H := D.host) (D.mem u).A.T)
  clsK_Qw : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → ∀ v ∈ ex.nch.Q w, ∀ c,
    Host.PrimeToPl (H := D.host) (clsK.rep c : Ideal (𝓞 D.host.K)) v
  LLgal : IsGalois ℚ T.host.LLQ
  HE : Fld
  HE_fd : FiniteDimensional ℚ HE
  HE_hilb : Host.IsHilbertCFE (hL := HE_fd) D.host HE
  HE_le : HE ≤ Rows.KsQ D T.host T.n.cf T.what₂.O.pieces
def HostDatumSelfDual {ex : Extra D L hT Gi Gl K Y cX} (T : _root_.Formalism.L2.TiedDataSAlt ex) : Prop := Nonempty (_root_.Formalism.L2.HostDatumWithTies T)
end
end Formalism.L2
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceFacts
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.NFacts
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
structure CoreNormFacts (D : D7) : Prop where
  what₂ : _root_.GlobalTheory.NRows.PointConditions' D
  adm : _root_.Formalism.MainNotions.SumRepresentations.AdmissibleDatum D
  Conclusion1 : _root_.Formalism.MainNotions.SumRepresentations.provisionFirst D
  Conclusion2 : SumRepresentations.Conclusion2 D
  rhoBar : ResidualIrreducibleRankR D
  g3p : _root_.UpperTheory.GalS.AdmissibleResidualTameEigenvalues D
  weight : GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.WeightParam D
  block : GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.BlockCharParam D
  g2 : _root_.Formalism.MainNotions.AdmissibleParameterJ.DeRhamFamilyAwayAlt D ∧ _root_.UpperTheory.GalS.DeRhamJumpsDistinctCondition D
  admJ : ∀ L : SizeData₂ D, AdmissibleParameterJ.AdmPar L → _root_.Formalism.MainNotions.AdmissibleParameterJ.AdmJAlt L
  muUnr : GlobalTheory.HubX.MuUnr D
  depthG : GlobalTheory.HubX.DepthZeroG D
  bc : SphericalInertData.Conclusion1 D
  lam : GlobalTheory.NRows.LamUsed D
structure NormChoiceFacts (D : D7) (C : NChoice D) : Prop extends toCore : _root_.GlobalTheory.NFacts.CoreNormFacts D where
  c2 : KillingConditions.LocalisationUniqueness D
  large : GlobalTheory.CoefDuty.Large D
  duties : GlobalTheory.CoefDuty.Duties D
  nct : NChTie D C
  trip : GlobalTheory.PtCore.TriplesGood D
  same : GlobalTheory.PtCore.SameTwist D C
  good : GoodFTAll D
theorem CoreNormFacts.admA {D : D7} (h : _root_.GlobalTheory.NFacts.CoreNormFacts D) : _root_.Formalism.MainNotions.SumRepresentations.AdmAAlt D := h.adm.1.1
theorem CoreNormFacts.a3 {D : D7} (h : _root_.GlobalTheory.NFacts.CoreNormFacts D) (L : SizeData₂ D) : TwistedPlaces.adm3 L := h.what₂.rank L
theorem CoreNormFacts.isot {D : D7} (h : _root_.GlobalTheory.NFacts.CoreNormFacts D) : Rows.IsotInternal D.what₂ := h.adm.2.2
end GlobalTheory.NFacts
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OPin
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.CoefDuty
open Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2 _root_.Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.HeightCounting
structure OPinAlt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch}
    (a : _root_.GlobalTheory.Mem.Top.Bl.NAtData hL D cf nch tp) : Prop where
  large : Large D
  inner : ∀ i : D.nd.Loc, ClassSum (a.all.gal.mt.loc i)
  lab : GlobalTheory.SerSys.LabTie a.nt.D fun k => @GlobalTheory.Mem.TypePl.labDat (a.nt.D.host.g k) ⟨a.nt.D.host.g_prime k⟩
  gen : ∀ k, a.nt.A.grp.ζ k = @GlobalTheory.GLq.LabelDatum.gen _ ⟨a.nt.D.host.g_prime k⟩
    (@GlobalTheory.Mem.TypePl.labDat (a.nt.D.host.g k) ⟨a.nt.D.host.g_prime k⟩)
end GlobalTheory.CoefDuty
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SParts
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Conclusion42OfParts
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MuBlockMemStatement
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MuBlockMemAlt
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SplitStepOAlt
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
noncomputable section
namespace GlobalTheory.MuBlock
theorem split_step_o_alt (D : D7) (hT : SumRepresentations.tie0 D) (h3 : SumRepresentations.adm3 D) (h7 : _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D)
    (hRS : GlobalTheory.RowCopy.RowSize D) (i : D.nd.Loc) (σ : D.what₂.FT) (P : D.naut.AV i)
    (Pa : List (Part D.naut.CG)) (hσ : D.what₂.isot (D.nd.j i) σ ≠ ⊥) (hth : thetaOf D.nd D.naut i σ P)
    (hB : IsBCV D.nd D.naut i P Pa) (w : PlE D.host) (hs : IsSplitPl D.host w)
    (hPa : ∀ p ∈ Pa, D.naut.unr (D.naut.locG p.π w)) (hμ : D.naut.unr (D.naut.locG (D.naut.muC i) w)) :
    (∃ p ∈ Pa, D.R.t ≤ p.d) ∧ ∀ p ∈ Pa, D.R.t ≤ p.d → p.d = D.R.t ∧
      D.naut.frobEig (D.naut.locG p.π w) = D.naut.frobEig (D.naut.locG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) w) := by
  have hLP := hT.1
  have hAut := hT.2.1
  have heu := D.naut.etaT_unr w
  have hed : D.naut.lpDim (D.naut.locG D.naut.etaT w) = 1 := D.naut.locG_dim _ _
  obtain ⟨e, he⟩ := frobEig_eq_single D.nd D.naut _ heu hed
  have hen : ‖e‖ = 1 := (D.naut.tempered_unr _ heu).1 (hAut.2.2.1 w) e (by rw [he]; exact Multiset.mem_singleton_self e)
  have he0 : e ≠ 0 := by intro h; rw [h] at hen; simp at hen
  obtain ⟨hbu, hbe⟩ := D.naut.etaTinv_def w
  have hbd : D.naut.lpDim (D.naut.locG D.naut.etaTinv w) = 1 := D.naut.locG_dim _ _
  have hb : D.naut.frobEig (D.naut.locG D.naut.etaTinv w) = {e⁻¹} := by rw [hbe, he]; simp
  have hbn : ‖e⁻¹‖ = 1 := by rw [norm_inv, hen, inv_one]
  obtain ⟨m, hm⟩ := frobEig_eq_single D.nd D.naut _ hμ (D.naut.locG_dim _ _)
  have hmn : ‖m‖ = 1 := (D.naut.tempered_unr _ hμ).1 (hAut.2.2.2 i w) m (by rw [hm]; exact Multiset.mem_singleton_self m)
  have htw : D.naut.frobEig (D.naut.locG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) w) = {m * e⁻¹} := by
    rw [D.naut.locG_tw, D.naut.frobEig_char _ _ (e⁻¹) hμ hbu hbd hb, hm]; simp
  have hV := h3 i σ P hth w hs
  have hiso := frobEig_isoLoc D.nd D.naut Pa w hPa
  have hVu : D.naut.unr (D.naut.locV i P w) := by rw [← hB.2.2.2.1 w hs]; exact hiso.1
  have hinv : D.naut.lpChar (D.naut.locG D.naut.etaTinv w) (D.naut.locG D.naut.etaT w) = D.naut.lpUnr w {1} := by
    have hu := D.naut.unr_char _ _ hed hbu heu
    rw [D.naut.unr_eq_lpUnr _ hu, D.naut.frobEig_char _ _ e hbu heu hed he, hb]; simp [he0]
  have hX : D.naut.lpChar (D.naut.locV i P w) (D.naut.locG D.naut.etaT w) =
      D.naut.lpSum (D.naut.locW i σ w) (spehLoc D.nd D.naut (muPart D.nd D.naut i) w) := by
    rw [hV, (hLP w (D.naut.lpSum (D.naut.locW i σ w) (spehLoc D.nd D.naut (muPart D.nd D.naut i) w))
      (D.naut.locW i σ w) (D.naut.locG D.naut.etaTinv w) (D.naut.locG D.naut.etaT w) 0 hbd hed).2.2.2.1, hinv]
    exact (hLP w _ (D.naut.locW i σ w) (D.naut.locG D.naut.etaT w) (D.naut.locG D.naut.etaT w) 0 hed hed).2.2.2.2.1
  have hXu : D.naut.unr (D.naut.lpSum (D.naut.locW i σ w) (spehLoc D.nd D.naut (muPart D.nd D.naut i) w)) := by
    rw [← hX]; exact D.naut.unr_char _ _ hed hVu heu
  obtain ⟨hWu, hSu⟩ := (D.naut.unr_sum _ _).1 hXu
  have hmu := frobEig_spehLoc D.nd D.naut (muPart D.nd D.naut i) w hμ
  dsimp only [muPart] at hmu
  have hVe : D.naut.frobEig (D.naut.locV i P w) =
      (D.naut.frobEig (D.naut.locW i σ w)).map (· * e⁻¹) +
      ((List.range D.R.t).map fun k => ({(m * e⁻¹) * ((normV w : ℕ) : ℂ) ^
        (((((D.R.t : ℝ) - 1) / 2 - (k : ℝ) : ℝ)) : ℂ)} : Multiset ℂ)).sum := by
    rw [hV, D.naut.frobEig_char _ _ _ hXu hbu hbd hb, D.naut.frobEig_sum _ _ hWu hSu, Multiset.map_add (f := _)]
    dsimp only [muPart]
    rw [hmu.2, hm]
    congr 1
    rw [← Multiset.coe_mapAddMonoidHom, map_list_sum, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k _
    simp only [Function.comp_apply, Multiset.coe_mapAddMonoidHom, Multiset.map_singleton]
    ring_nf
  have key := UpperTheory.GalN.string_count (normV w) D.R.t (Pa.map fun p => (p.d, D.naut.frobEig (D.naut.locG p.π w)))
    ((D.naut.frobEig (D.naut.locW i σ w)).map (· * e⁻¹)) (m * e⁻¹)
    (by exact_mod_cast GlobalTheory.LocalInv.one_lt_normV w) D.R.t_odd.pos
    (by rw [norm_mul, hmn, hbn, one_mul])
    (by
      intro x hx
      obtain ⟨α, hα, rfl⟩ := Multiset.mem_map.1 hx
      rw [norm_mul, hbn, mul_one]
      have := hRS i σ hσ w hs hWu α hα
      rwa [absNorm_eq_normV] at this)
    (by
      intro x hx
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
      have k := _root_.GlobalTheory.PartUnitary.frobEig_openB_and_norm_one_of_isBCV D hT h7 i P Pa hB p hp w (hPa p hp)
      refine ⟨(hB.1 p hp).2.1, ?_, fun α hα => (k α hα).1, fun ht α hα =>
        (k α hα).2 (UpperTheory.GalN.rank_one_of_long hB.2.2.1 hp (hB.1 p hp).1 ht)⟩
      intro h0
      change D.naut.frobEig (D.naut.locG p.π w) = 0 at h0
      have h1 := D.naut.frobEig_card _ (hPa p hp)
      rw [h0, D.naut.locG_dim] at h1
      have := (hB.1 p hp).1
      simp at h1
      omega)
    (by
      have hiso2 := hiso.2
      simp only [GlobalTheory.LocalInv.list_coe, List.map_map] at hiso2
      rw [List.map_map]
      exact hiso2.symm.trans ((congrArg D.naut.frobEig (hB.2.2.2.1 w hs)).trans hVe))
  refine ⟨?_, fun p hp hpt => ?_⟩
  · obtain ⟨x, hx, hxt⟩ := key.1
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
    exact ⟨p, hp, hxt⟩
  · obtain ⟨h1, h2⟩ := key.2 _ (List.mem_map_of_mem (f := fun p : Part D.naut.CG => (p.d, D.naut.frobEig (D.naut.locG p.π w))) hp) hpt
    exact ⟨h1, h2.trans htw.symm⟩
end GlobalTheory.MuBlock
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
noncomputable section
namespace GlobalTheory.MuBlock
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
end GlobalTheory.MuBlock
namespace GlobalTheory.MuBlock
end GlobalTheory.MuBlock
namespace GlobalTheory.MuBlock
theorem mu_block_mem_alt : ∀ D : D7, SumRepresentations.tie0 D → SumRepresentations.adm3 D → SumRepresentations.adm5 D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D →
    GlobalTheory.RowCopy.RowSize D → GlobalTheory.RowCopy.HeckeSplitOne D →
    ∀ (i : D.nd.Loc) (σ : D.what₂.FT) (P : D.naut.AV i) (Pa : List (Part D.naut.CG)),
    D.what₂.isot (D.nd.j i) σ ≠ ⊥ → thetaOf D.nd D.naut i σ P → IsBCV D.nd D.naut i P Pa →
    (⟨1, D.naut.tw (D.naut.muC i) D.naut.etaTinv, D.R.t⟩ : Part D.naut.CG) ∈ Pa := by
  intro D hT h3 h5 h7 hRS hH i σ P Pa hσ hth hB
  have hgood : ∀ᶠ w in Filter.cofinite, (∀ p ∈ Pa, D.naut.unr (D.naut.locG p.π w)) ∧
      D.naut.unr (D.naut.locG (D.naut.muC i) w) := by
    refine Filter.Eventually.and ?_ (D.naut.locG_unr_ae _)
    exact (Filter.eventually_all_finite (List.finite_toSet Pa)).2 fun p _ => D.naut.locG_unr_ae p.π
  obtain ⟨w0, hw0, hs0⟩ := exists_split_not_mem D.nd h5.2.2.1 _ (Filter.eventually_cofinite.1 hgood)
  have hg0 : (∀ p ∈ Pa, D.naut.unr (D.naut.locG p.π w0)) ∧ D.naut.unr (D.naut.locG (D.naut.muC i) w0) := by
    simpa using hw0
  obtain ⟨⟨p0, hp0, hpt⟩, -⟩ := _root_.GlobalTheory.MuBlock.split_step_o_alt D hT h3 h7 hRS i σ P Pa hσ hth hB w0 hs0 hg0.1 hg0.2
  have hall : ∀ w, ((∀ p ∈ Pa, D.naut.unr (D.naut.locG p.π w)) ∧ D.naut.unr (D.naut.locG (D.naut.muC i) w)) →
      IsSplitPl D.host w → p0.d = D.R.t ∧ D.naut.frobEig (D.naut.locG p0.π w) =
        D.naut.frobEig (D.naut.locG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) w) :=
    fun w hw hs => (_root_.GlobalTheory.MuBlock.split_step_o_alt D hT h3 h7 hRS i σ P Pa hσ hth hB w hs hw.1 hw.2).2 p0 hp0 hpt
  have htu : ∀ w, D.naut.unr (D.naut.locG (D.naut.muC i) w) →
      D.naut.unr (D.naut.locG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) w) := fun w h => by
    rw [D.naut.locG_tw]
    exact D.naut.unr_char _ _ (D.naut.locG_dim _ _) h (D.naut.etaTinv_def w).1
  obtain ⟨hd0, hf0⟩ := hall w0 hg0 hs0
  have ha0 : p0.a = 1 := by
    have h1 := D.naut.frobEig_card _ (hg0.1 p0 hp0)
    rw [hf0, D.naut.frobEig_card _ (htu w0 hg0.2), D.naut.locG_dim, D.naut.locG_dim] at h1
    exact h1.symm
  obtain ⟨a, π, d⟩ := p0
  dsimp only at ha0 hd0 hall hp0
  subst ha0 hd0
  have hν : π = D.naut.tw (D.naut.muC i) D.naut.etaTinv := by
    refine hH π _ ?_
    filter_upwards [hgood] with w hw hs
    rw [D.naut.unr_eq_lpUnr _ (hw.1 _ hp0), (hall w hw hs).2, ← D.naut.unr_eq_lpUnr _ (htu w hw.2)]
  subst hν
  exact hp0
end GlobalTheory.MuBlock
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_mu_piece_mem_base_change : ∀ D : D7, SumRepresentations.tie0 D → SumRepresentations.adm3 D → SumRepresentations.adm5 D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D → GlobalTheory.RowCopy.RowSize D → GlobalTheory.RowCopy.HeckeSplitOne D → ∀ (i : D.nd.Loc) (σ : D.what₂.FT) (P : D.naut.AV i) (Pa : List (Part D.naut.CG)), D.what₂.isot (D.nd.j i) σ ≠ ⊥ → thetaOf D.nd D.naut i σ P → IsBCV D.nd D.naut i P Pa → (⟨1, D.naut.tw (D.naut.muC i) D.naut.etaTinv, D.R.t⟩ : Part D.naut.CG) ∈ Pa := by
  first | exact @_root_.GlobalTheory.MuBlock.mu_block_mem_alt | exact _root_.GlobalTheory.MuBlock.mu_block_mem_alt | (intros; apply _root_.GlobalTheory.MuBlock.mu_block_mem_alt <;> assumption)
end
end

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
namespace GlobalTheory.NRows.Parts
theorem conclusion42_of_parts (D : D7) (a : _root_.Formalism.MainNotions.SumRepresentations.AdmAtAlt D) (s : GlobalTheory.RowCopy.RowSize D) (hk : GlobalTheory.RowCopy.HeckeSplitOne D)
    (l : ∀ i : D.nd.Loc, GlobalTheory.RowCopy.LamPos D (D.nd.mu i) (D.nd.j i)) (th : GlobalTheory.RowCopy.ThetaOne D) : SumRepresentations.ReducedParameterProposition D := by
  obtain ⟨⟨t0, hO, a1, a2, a3, a4, a5⟩, a7⟩ := a
  intro i σ hσ
  obtain ⟨P, hP⟩ := th i σ hσ
  obtain ⟨Pa, hPa⟩ := a1 i P
  obtain ⟨Sig, h1, h2⟩ := GlobalTheory.T.row_param_of_thetaLift_baseChange D t0 a3 a4 a5 i σ P Pa hP hPa (_root_.GlobalTheory.T.twisted_mu_piece_mem_base_change D t0 a3 a5 a7 s hk i σ P Pa hσ hP hPa)
  refine ⟨⟨⟨_, (l i σ).2 hσ, (l i σ).1⟩, P, hP⟩, Sig, h1, fun P' hP' => ?_⟩
  obtain rfl : P = P' := by
    by_contra hne
    exact hP.1 (le_bot_iff.1 ((le_inf hP.2 hP'.2).trans ((D.naut.typeV_indep i).pairwiseDisjoint hne).le_bot))
  exact h2
end GlobalTheory.NRows.Parts
end
end

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
namespace UpperTheory.GalS.Parts
open UpperTheory.GalS GlobalTheory.NRows GlobalTheory.AbsIrrConstituents Pointwise
theorem p41'_alt (D : D7) (t0 : SumRepresentations.tie0 D) (hO : SumRepresentations.hypO D) (a1 : SumRepresentations.adm1 D) (a2 : AutomorphicGaloisAdmissible D.nd D.naut) (a5 : SumRepresentations.adm5 D)
    (_ : _root_.Formalism.MainNotions.SumRepresentations.AdmAtAlt D) : HeckeGaloisFamilyProperties D := heckeGaloisFamilyProperties_of_admissible D t0 hO a1 a2 a5
theorem main_alt_alt : ∀ D : D7, _root_.GlobalTheory.NRows.SummandsSuffice D := fun D a t s hk l th g =>
  ⟨_root_.UpperTheory.GalS.Parts.p41'_alt D a.1.1 a.1.2.1 a.1.2.2.1 a.1.2.2.2.1 a.1.2.2.2.2.2.2 a, g, (SumRepresentations.proposition_parameters_iff_reduced D t).2 (_root_.GlobalTheory.NRows.Parts.conclusion42_of_parts D a s hk l th)⟩
end UpperTheory.GalS.Parts
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.JointsTiedS
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.UG
open scoped TensorProduct
namespace Formalism.L2
open Formalism.L2.Joints
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC}
structure JointsSAlt {ex : Extra D L hT Gi Gl K Y cX} (T : _root_.Formalism.L2.TiedDataSAlt ex) : Prop where
  dt : ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (e : Formalism.L2.Theta.AE D), Formalism.L2.JoinChr.IsPlIdem D e P →
    ∀ (k : D.host.Eˣ) (y : Formalism.L2.Theta.AE D), IsRatioAt D e (k : D.host.E) y →
    ∀ x : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm,
      ((Matrix.GeneralLinearGroup.det (x : GL (Fin 1) (D.host.E ⊗[D.host.F] Formalism.L2.Herm.Af D.host.F)) :
        (D.host.E ⊗[D.host.F] Formalism.L2.Herm.Af D.host.F)ˣ) : D.host.E ⊗[D.host.F] Formalism.L2.Herm.Af D.host.F) = finE D y →
      T.full.1.base.dt x = T.chrDt.eDt (localIdele D.host.E P (Formalism.L2.Host.atFin P k))
  piBar : ∀ k : Fin 2, InPrimeK D (Formalism.L2.Forms.sigD D ((T.cols.forms D.u₀).gl.piG k : D.host.E)) (T.n.cf.P.pb k)
  om : ∀ (k : Fin 2) (v : HeightOneSpectrum (𝓞 D.host.F)) (h : (D.host.g k : 𝓞 D.host.F) ∈ v.asIdeal) (a n : ℕ)
    (hn : n.Coprime (D.host.g k)), a < D.R.m →
    (T.cols.forms D.u₀).gl.chiB k v h a (n : Formalism.L2.Forms.kv D.host.F v) =
      ((T.n.cf.W.om k (ZMod.unitOfCoprime n hn) ^ (2 * (a + 1)) : ℂˣ) : ℂ)
  psiG : ∀ (k : Fin 2) (v : HeightOneSpectrum (𝓞 D.host.F)) (h : (D.host.g k : 𝓞 D.host.F) ∈ v.asIdeal)
    (ε : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F), Formalism.L2.Theta.IsPlaceIdem D v ε → ∀ c y : 𝓞 D.host.F,
    Valued.v (algebraMap D.host.F (v.adicCompletion D.host.F) (c : D.host.F) -
        (T.cols.forms D.u₀).gl.phi k v h (inclE (F := D.host.F) (v.adicCompletion D.host.F) D.host.xi0)) < 1 →
    (T.cols.forms D.u₀).gl.psi0 k v h (redV D.host.F v (algebraMap D.host.F (v.adicCompletion D.host.F) (y : D.host.F))) =
      T.theta.W.ψ (ε * algebraMap D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ((c : D.host.F) * (y : D.host.F) / (D.host.g k : D.host.F)))
  div : Nonempty (Formalism.L2.Host.DivisorCharacterCompatibility D T.n.cf ex.nch T.n.tp Y)
namespace JointsS
variable {ex : Extra D L hT Gi Gl K Y cX} {T : _root_.Formalism.L2.TiedDataSAlt ex}
end JointsS
section
end
end Formalism.L2
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GTiedFOfC2S
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions
namespace Formalism.L2
theorem gTiedF_of_C2S_alt {eps : ℝ} (Fm : FamP eps) (h : _root_.Formalism.L2.SecondChernLinkedClass Fm) : G.GroupCompatibilityFamily Fm := by
  obtain ⟨x0, hx0⟩ := h
  refine ⟨max x0 (Fm.x1 + 1), fun x hx i hx1 => ?_⟩
  obtain ⟨T⟩ := hx0 x hx1 ((le_max_left _ _).trans hx) i
  exact ⟨T.g⟩
end Formalism.L2
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GoodOffGp
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GoodOffGp
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.OffBad
theorem good_off_gp_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp)
    (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hG : GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) w) :
    (∀ k : Fin 2, w ∉ placesOver D.host.E (D.host.g k)) ∧
      w ∉ placesOver D.host.E (if D.nd.l i = D.host.pde then D.host.pde' else D.host.pde) := by
  have hlev := X.recR.base.lev
  have hmu : D.nd.mu i = D.what₂.muAt (D.nd.w i) := by
    rcases D.what₂.muAt_or (D.nd.w i) with h | h
    · exact absurd h (D.nd.w_tw i)
    · rw [h, D.nd.mu_w i]
  have hxi := X.recR.tupXi (D.nd.mu i) (Or.inr ⟨D.nd.w i, hmu⟩)
  have hunr : (X.R.xiH (X.tupT (D.nd.mu i))).UnrAt w := by
    by_contra hn
    rcases (hlev.Q_ram _ w).1 hn with h | ⟨PP, hPP, hc⟩
    · exact (hG w (Or.inr h)).1 rfl
    · exact (hG PP (Or.inr hPP)).2 hc
  rw [hxi, D.nd.mu_w i, X.Tp.xi_tw, D.nd.w_l i] at hunr
  have hψ := X.Tp.psi_is (D.nd.w i) (D.nd.w_tw i)
  rw [D.nd.w_l i] at hψ
  set δ := X.R.C.delAt (D.nd.l i) with hδdef
  set ψ := X.Tp.psi (D.nd.w i) with hψdef
  set p := if D.nd.l i = D.host.pde then D.host.pde' else D.host.pde with hpdef
  have hd : IsDelta (H := D.host) p δ := by
    rw [hδdef, hpdef, CharFrame.delAt]
    split_ifs
    exacts [X.R.C.isDel', X.R.C.isDel]
  have hmul : ∀ x, (δ * ψ).loc w x = δ.loc w x * ψ.loc w x := fun _ => rfl
  have hnp : ¬ OverP D.host p w := by
    intro hw
    obtain ⟨a, ha⟩ := hψ.ord
    have h15 : 15 ∣ D.nd.l i ^ a := by
      refine (hd.ine w hw (D.nd.l i ^ a)).1 fun x hx => ?_
      have h1 : δ.loc w x * ψ.loc w x = 1 := (hmul x).symm.trans (hunr x hx)
      have h2 : ψ.loc w x ^ (D.nd.l i ^ a) = 1 := by
        have := congrArg (fun ξ : HChar D.host.E => ξ.loc w x) ha
        simpa [HChar.loc] using this
      have h3 : (δ.loc w x * ψ.loc w x) ^ (D.nd.l i ^ a) = 1 := by rw [h1, one_pow]
      rwa [mul_pow, h2, mul_one] at h3
    have hl : (D.nd.l i).Prime := (D.nd.lPrime i).out
    have h3 : 3 = D.nd.l i := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hl).1
      (Nat.prime_three.dvd_of_dvd_pow (dvd_trans (by norm_num) h15))
    have h5 : 5 = D.nd.l i := (Nat.prime_dvd_prime_iff_eq (by norm_num) hl).1
      ((show (5 : ℕ).Prime by norm_num).dvd_of_dvd_pow (dvd_trans (by norm_num) h15))
    omega
  have hng : ∀ k : Fin 2, w ∉ placesOver D.host.E (D.host.g k) := by
    intro k hw
    have hs : GlobalTheory.Mem.Chr.SplitsC D.host.E (D.host.g k) := D.nd.g_split k
    rcases (GlobalTheory.BigOn.Inhab.overP_iff (D.host.g_prime k) hs (X.R.C.P.pb_over k) w).1 hw with h | ⟨w', h, hc⟩
    · exact (hG w (Or.inl ((hlev.Pg w).2 ⟨k, GlobalTheory.BigOn.Inhab.mem_aboveK.1 h⟩))).1 rfl
    · exact (hG w' (Or.inl ((hlev.Pg w').2 ⟨k, GlobalTheory.BigOn.Inhab.mem_aboveK.1 h⟩))).2 hc
  exact ⟨hng, hnp⟩
end GlobalTheory.OffBad
namespace GlobalTheory.OffBad
theorem offbad_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)), GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) w → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (w.under (𝓞 D.host.F)) → ∃ sp : SplitPlace D.host.E, sp.w = w ∧ (∀ κ : GAf D.host.E D.R.nV, TrivOutside {sp.v} κ → (κ ∈ (P.M.loc i).J ↔ κ ∈ Umax D.host.E D.R.nV) ∧ ∀ hκ : κ ∈ (P.M.loc i).J, (P.M.loc i).χ ⟨κ, hκ⟩ = 1) := by
  intro _ hL D P X hA h41 _ htl i w hG hsplit
  obtain ⟨sp, hsp⟩ := splitPlace_of_isSplitPl D w (isSplitPl_of_isSplit D w hsplit)
  obtain ⟨hng, hnp⟩ := _root_.GlobalTheory.OffBad.good_off_gp_alt hL D P X i w hG
  have hQ := (_root_.GlobalTheory.OffSQ.good_off_SQ_alt hL D P X hA h41 htl i w hG).2
  have HT := P.H.hecke
  have hbad : sp.v ∉ badPl D i := by
    rintro ⟨w', hover, hw'⟩
    have hp : ∀ p : ℕ, w' ∈ placesOver D.host.E p → w ∈ placesOver D.host.E p := by
      intro p hp
      have h1 : algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) (p : 𝓞 (maximalRealSubfield D.host.E)) ∈
          w'.asIdeal := by rw [map_natCast]; exact hp
      have h2 : (p : 𝓞 (maximalRealSubfield D.host.E)) ∈ sp.v.asIdeal := by
        rw [← hover]; exact h1
      have h3 : algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) (p : 𝓞 (maximalRealSubfield D.host.E)) ∈
          sp.w.asIdeal := by
        rw [← Ideal.mem_comap, sp.w_under]; exact h2
      rw [map_natCast, hsp] at h3
      exact h3
    rcases hw' with hQ' | ⟨kk, hg⟩ | hpd
    · rcases GlobalTheory.SplitConjPlace.eq_or_eq_conjPlE sp.w w' (hover.trans sp.w_under.symm) with e | e
      · rw [e, hsp] at hQ'
        exact hQ hQ'
      · apply hQ
        rw [← hsp]
        refine HT.Q_conj i w' sp.w ?_ hQ'
        rw [e]
        intro x y hxy
        rw [GlobalTheory.SplitConjPlace.mem_conjPlE]
        have hy : IsCMField.ringOfIntegersComplexConj D.host.E x = y := by
          apply RingOfIntegers.ext
          rw [IsCMField.coe_ringOfIntegersComplexConj, hxy, GlobalTheory.HeckeScalarAll.host_conj_eq']
        rw [← hy]
    · exact hng kk (hp _ hg)
    · exact hnp (hp _ hpd)
  refine ⟨sp, hsp, fun κ hκ => HT.J_hyp i κ (fun v hv => hκ v ?_)⟩
  rintro rfl
  exact hv hbad
end GlobalTheory.OffBad
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GoodOffGpStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSplit_of_hk3_good : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)), GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) w → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (w.under (𝓞 D.host.F)) → ∃ sp : SplitPlace D.host.E, sp.w = w ∧ (∀ κ : GAf D.host.E D.R.nV, TrivOutside {sp.v} κ → (κ ∈ (P.M.loc i).J ↔ κ ∈ Umax D.host.E D.R.nV) ∧ ∀ hκ : κ ∈ (P.M.loc i).J, (P.M.loc i).χ ⟨κ, hκ⟩ = 1) := by
  exact _root_.GlobalTheory.OffBad.offbad_alt
end
end
end
