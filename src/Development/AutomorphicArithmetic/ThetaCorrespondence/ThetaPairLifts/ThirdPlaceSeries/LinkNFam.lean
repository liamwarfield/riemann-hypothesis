module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.LinkNOfGd
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleConstituentsCharpolyProduct
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValuationRingModel
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ResidueCountOfSsRank
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InfinityTypeEtaTildeAtCmTypeEmbeddingsEqHalf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AllTriplesLocal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosingAtRecord
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallinePeriodBoundAllConstantGeForty
public import Formalism.SharpRestriction.LevelLetterCocycles.CongruenceAnnihilatesCharacterPart
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaPolynomialKillsPotentiallyCrystallineModu
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinkNAlongFamilyOfLocalBounds
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerUp
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PendingLayerConditionAtMember
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsFurtherTail
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisRepUniqueBaseChange
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameDescentConditionsEveryLocalisationStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReducedFormOfLocalInputs
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsIrreducibleConstituentRanksUniqueOfCharpolyStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousIotaOQOfDataStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigencharacterOfSummandCharZeroStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleConstituentsCharpolyProductStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsHeckeGaloisQOfIsHeckeGaloisStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StringRankOneLengthAndMultisetSumSingletonStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValuationRingModelStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CongruenceAtTypePrimes

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalTypeDeterminedAtAllPrimes
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.InePolEqWdAt
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.InePolEqWdAt
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
namespace GlobalTheory.TieInePolyPin
theorem inePol_eq_wdAt_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (m : ℕ) (r : GE D.nd →* GL (Fin m) (D.nd.O i)), Continuous (fun g => ((r g : GL _ _) : Matrix (Fin m) (Fin m) (D.nd.O i))) → GlobalTheory.Pst.IsPstAt (D.loc (D.nd.l i)) (D.nbr i w hw) (GlobalTheory.Pst.resDec D.nd.plOm.1 (mapRep (iotaOQ D.nd D.naut i) r) w) → ∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w), D.naut.inePol (D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) r) w) σ = (GlobalTheory.Pst.wdAt (D.loc (D.nd.l i)) (D.naut.iotaQC i) (D.nbr i w hw) (D.nd.plOm.2 w) (D.nbr_ind i w hw) (GlobalTheory.Pst.resDec D.nd.plOm.1 (mapRep (iotaOQ D.nd D.naut i) r) w)).inePol σ := by
  intro hL D P i w hw m r hc hpst σ hσ
  have hc' : Continuous (fun g => ((GlobalTheory.Pst.resDec D.nd.plOm.1 (mapRep (iotaOQ D.nd D.naut i) r) w g : GL _ _) : Matrix (Fin m) (Fin m) (Om (D.nd.l i)))) :=
    ((hc.matrix_map (GlobalTheory.T.continuous_iotaOQ' D.nd D.naut i)).comp continuous_subtype_val)
  rw [(P.wdOf i m (mapRep (iotaOQ D.nd D.naut i) r) w).1, P.T.inePol w _ σ hσ]
  obtain ⟨LL, Bw, hj, e2⟩ := P.wd.above (D.nd.l i) (D.naut.iotaQC i) (mapRep (iotaOQ D.nd D.naut i) r) w hw
  rw [e2]
  refine congrArg (fun x => GlobalTheory.WeilDeligne.WD.inePol x σ) ?_
  exact GlobalTheory.Pst.BridgeParam.wdAt_indep_bridge (D.nd.l i) (D.loc (D.nd.l i)) (D.locA (D.nd.l i)) ⟨D.locT (D.nd.l i)⟩
    (D.naut.iotaQC i) D.host.E D.nd.Om (D.nd.plOm.1 w) w _ _ Bw (D.nbr i w hw) (D.nd.plOm.2 w) hj (D.nbr_ind i w hw) m _ hc'
    (GlobalTheory.T.isPotSemistable_independent_of_inducingEmbedding (D.nd.l i) (D.loc (D.nd.l i)) (D.locA (D.nd.l i)) ⟨D.locT (D.nd.l i)⟩ D.host.E D.nd.Om (D.nd.plOm.1 w) _ _
      (D.nbr i w hw) Bw (D.nbr_ind i w hw) hj m _ hc' hpst) hpst
theorem main_alt_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), GlobalTheory.Pass.TieInePoly D := by
  intro hL D P i w hw K' h hN hF hS m r hc hpot σ hσ p hp d hd
  exact GlobalTheory.T.inertiaPolynomial_kills_potentiallyCrystalline_module D i w hw K' h hN hF hS m r hc hpot σ hσ p
    (hp.trans (_root_.GlobalTheory.TieInePolyPin.inePol_eq_wdAt_alt hL D P i w hw m r hc (GlobalTheory.T.potSemistable_of_potCrystalline_decompositionGroup D i w hw K' h hN hF hS m r hc hpot) σ hσ)) d hd
end GlobalTheory.TieInePolyPin
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.InePolEqWdAtStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem _root_.GlobalTheory.T.tieInePoly_of_characterChoice
    (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7)
    (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) : GlobalTheory.Pass.TieInePoly D :=
  _root_.GlobalTheory.TieInePolyPin.main_alt_alt hL D P
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
namespace GlobalTheory.TypePrimesFinished
theorem locComp_of_isRc_classMapD_cenLoc : GlobalTheory.HeightCounting.HtCard → _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → GlobalTheory.Published.DepthZeroSupport → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ _ _ _ _ => (PairedCharacterCondition.tieChi (D := w.D Z) ∧ (∃ Q : PairedCharacterCondition.Pend (w.D Z), PairedCharacterCondition.admDZ Q ∧ GlobalTheory.Pass.EigSpan Q) ∧ GlobalTheory.Pass.TieInePoly (w.D Z) ∧ GlobalTheory.TypeLeaf.SerLoc (w.D Z)) := by
  intro hC hP hS hL
  refine _root_.GlobalTheory.HeightCounting.Up.Model.AtMem.at_member_imp
    (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.T.tieChi_at_mem_of_depth_zero_inputs hC hP hS hL)
      (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.T.exists_character_choice_pin_at_of_third_layer hP hL) (_root_.GlobalTheory.T.serLoc_at_member_of_published_inputs hP hL))) ?_
  intro K B f T w Z Wt p0 t nch n c h
  obtain ⟨⟨h1, h2⟩, ⟨P, _⟩, h4⟩ := h
  exact ⟨h1, h2, _root_.GlobalTheory.T.tieInePoly_of_characterChoice hL (w.D Z) P, h4⟩
end GlobalTheory.TypePrimesFinished
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tieChi_at_members_of_depthZero : GlobalTheory.HeightCounting.HtCard → _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → GlobalTheory.Published.DepthZeroSupport → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ _ _ _ _ => (PairedCharacterCondition.tieChi (D := w.D Z) ∧ (∃ Q : PairedCharacterCondition.Pend (w.D Z), PairedCharacterCondition.admDZ Q ∧ GlobalTheory.Pass.EigSpan Q) ∧ GlobalTheory.Pass.TieInePoly (w.D Z) ∧ GlobalTheory.TypeLeaf.SerLoc (w.D Z)) := by
  first | exact @_root_.GlobalTheory.TypePrimesFinished.locComp_of_isRc_classMapD_cenLoc | exact _root_.GlobalTheory.TypePrimesFinished.locComp_of_isRc_classMapD_cenLoc | (intros; apply _root_.GlobalTheory.TypePrimesFinished.locComp_of_isRc_classMapD_cenLoc <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SlotMvPin
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.NLink.Final
section Slot
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab _root_.Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
set_option maxHeartbeats 4000000 in
theorem slot_mv_extension_with_list_geo_cl (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (cDep : ℝ) (Γ : GeoP) :
    PositionMv (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithList hL cDep) SExt.none (geoCl Γ)).s := by
  intro K B f T w Z O x N h O' hO' col n
  have hrows := _root_.GlobalTheory.T.rows_pass_to_moved_divisionLatticesHeights
    K B f T w Z x.Wt O x.what₂ N h O' hO'
  obtain ⟨t', hs, hgeo, hpk, hobj, hrx⟩ := hrows
  obtain ⟨nch', xd', -, hnx, -, -, hmv⟩ := _root_.GlobalTheory.T.exists_kept_choice_upper_lattice_alt hL K B f T w Z x.Wt Z.S N h O.nch O.xd
  obtain ⟨hn1, hn2⟩ := hnx rfl
  subst hO'
  have e1 : nch' = (O.tr N h).nch := eq_of_heq hn1
  have e2 : xd' = (O.tr N h).xd := eq_of_heq hn2
  subst e1 e2
  have hlp := GlobalTheory.Mem.GridMove.listPin_rowsSame cDep K.s.b K B f T w Z x.Wt Z.S N h O.p0 x.what₂ (O.tr N h).p0 t' hs x.nx.2.2.down
  obtain ⟨c⟩ := hmv O.p0 x.what₂ x.n (O.tr N h).p0 t' n hs hgeo ⟨x.nx.1, x.nx.2.1⟩
  obtain ⟨s⟩ := GlobalTheory.T.spectralStageData_transfer_lattices_heights K B f T w Z x.Wt O.p0 x.what₂ x.col.toColT N h (O.tr N h).p0 t' col.toColT hpk ⟨x.sx.1⟩
  obtain ⟨o⟩ := GlobalTheory.T.divisionGeometryScalars_transfer_setDivision Γ K B f T w Z x.Wt N h O (O.tr N h) rfl x.what₂ t' hs x.ox
  exact ⟨t', hobj x.obj, hrx ⟨x.rx⟩, ⟨⟨c.1, c.2, ⟨hlp⟩⟩⟩, ⟨⟨s, PUnit.unit⟩⟩, ⟨o⟩⟩
end Slot
end GlobalTheory.NLink.Final
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OverNEOfNEb
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Lg1EntryOfMembership
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.NRows.AtPt
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.Inhab _root_.Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl
  GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.Fc NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists}
def OverNEAlt (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) : Prop :=
  ∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.defaultExtension hL K B f T w Z Wt p0 t nch n xd c)
def membershipLocation (P : _root_.GlobalTheory.HeightCounting.Up.LayPAlt hL) : V4.Slot := fun K X f T _ =>
  ∀ w Z Wt p0 t nch n xd c, Nonempty (_root_.GlobalTheory.HeightCounting.defaultExtension hL K X.B f T w Z Wt p0 t nch n xd c) → Nonempty (RXs t) → ColPin w →
    P K X.B f T w Z Wt p0 t nch n c
abbrev WitnessAtPoint (P : _root_.GlobalTheory.HeightCounting.Up.LayPAlt hL) {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : WPt p.s K) : Prop :=
  P K q.B q.f q.T q.w q.Z q.x.Wt _ q.x.what₂ _ q.x.n q.core_data_of_point
theorem lgSlotG_memSlot' {P : _root_.GlobalTheory.HeightCounting.Up.LayPAlt hL} (h : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL P) (Q : V4.Slot) : LargeBaseConditionG KPx Q (_root_.GlobalTheory.NRows.AtPt.membershipLocation P) :=
  EvG.imp h fun _ _ _ _ _ hK => large₂.imp hK fun _ _ _ _ H kp _ _ _ _ _ _ _ _ => H kp
section
variable {N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL} {S : SExt} {Γ : GeoP} {P : _root_.GlobalTheory.HeightCounting.Up.LayPAlt hL}
theorem exists_wPt_entC_atWit_of_heq (hN : _root_.GlobalTheory.NRows.AtPt.OverNEAlt N) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {D : D7}
    (hP : ∀ w Z Wt p0 t nch n xd c, Nonempty (_root_.GlobalTheory.HeightCounting.defaultExtension hL K B f T w Z Wt p0 t nch n xd c) → Nonempty (RXs t) → ColPin w →
      P K B f T w Z Wt p0 t nch n c)
    (e : w.D Z = D) (O : Obj D) {O' : Obj2 (w.D Z)} (hO : HEq (ofObj O) O') (x : Wit (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s K w Z O') (hx : EntC x.ker) :
    ∃ q : WPt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s K, q.Is D O ∧ EntC q.x.ker ∧ _root_.GlobalTheory.NRows.AtPt.WitnessAtPoint (p := _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) P q := by
  subst e
  obtain rfl := eq_of_heq hO
  exact ⟨⟨B, f, T, w, Z, O, x⟩, rfl, hx, hP w Z _ _ _ _ _ _ x.nx.1 (hN _ _ _ _ _ _ _ _ _ _ _ _ _ x.nx.2) ⟨x.rx⟩ x.pin⟩
set_option maxHeartbeats 2000000 in
theorem exists_wit_pt_alt (hN : _root_.GlobalTheory.NRows.AtPt.OverNEAlt N) (H : WitMv (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}
    {Z : w.Lt}
    (hP : ∀ w Z Wt p0 t nch n xd c, Nonempty (_root_.GlobalTheory.HeightCounting.defaultExtension hL K B f T w Z Wt p0 t nch n xd c) → Nonempty (RXs t) → ColPin w →
      P K B f T w Z Wt p0 t nch n c)
    {O : Obj2 (w.D Z)} (x : Wit (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s K w Z O) (hx : EntC x.ker) (Y : Lay (w.D Z)) (hY : layObj Y = O) (p : LedPart K.C Y) :
    ∃ q : WPt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s K, q.Is p.pt.D (Obj.ofPt p.pt) ∧ EntC q.x.ker ∧ _root_.GlobalTheory.NRows.AtPt.WitnessAtPoint (p := _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) P q := by
  obtain ⟨y, hy⟩ := H K B f T w Z O x (nPrime p.L) p.ht hx
  exact _root_.GlobalTheory.NRows.AtPt.exists_wPt_entC_atWit_of_heq hN hP (Db.D_setDivZ w Z (nPrime p.L) p.ht) (Obj.ofPt p.pt)
    (hY ▸ heq_of_eq (pointObj_pt p)) y hy
set_option maxHeartbeats 2000000 in
theorem exists_wPt_entC_atWit (hN : _root_.GlobalTheory.NRows.AtPt.OverNEAlt N) (H : WitMv (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s) {K : Ctx} (β : BPt K)
    (hβ : β.Is (sAnd (IsGoodE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s) (_root_.GlobalTheory.NRows.AtPt.membershipLocation P))) :
    ∃ q : WPt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s K, q.Is β.D β.O ∧ EntC q.x.ker ∧ _root_.GlobalTheory.NRows.AtPt.WitnessAtPoint (p := _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) P q :=
  positionOf_ind (P := GoodE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s) (R := fun K X f T c => _root_.GlobalTheory.NRows.AtPt.membershipLocation P K X f T c →
      ∀ (Y : Lay X.toD7) (_ : layObj Y = c.O) (p : LedPart K.C Y),
      ∃ q : WPt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s K, q.Is p.pt.D (Obj.ofPt p.pt) ∧ EntC q.x.ker ∧ _root_.GlobalTheory.NRows.AtPt.WitnessAtPoint (p := _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) P q)
    (fun _ _ _ _ _ _ _ g hP => g.1.elim fun b hb => _root_.GlobalTheory.NRows.AtPt.exists_wit_pt_alt hN H hP (b.wit g.2) hb)
    hβ.1 hβ.2 β.Y β.hY β.p
theorem memSlot_entry_of_atWit (hN : _root_.GlobalTheory.NRows.AtPt.OverNEAlt N) (H : WitMv (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s) {r : ∀ D : D7, Obj D → Prop}
    (hr : ∀ K (q : WPt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s K), EntC q.x.ker → _root_.GlobalTheory.NRows.AtPt.WitnessAtPoint (p := _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) P q → r (q.w.D q.Z) q.O) {Bd : BdT} (Lk : LkT Bd) :
    RowE (sAnd (IsGoodE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s) (_root_.GlobalTheory.NRows.AtPt.membershipLocation P)) Lk fun _ D O _ _ => r D O :=
  RowE.of_all fun _ K β _ _ _ hβ _ => let ⟨q, a, b, c⟩ := _root_.GlobalTheory.NRows.AtPt.exists_wPt_entC_atWit hN H β hβ; of_is a (hr K q b c)
end
theorem lg1_entry_of_atWit {N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL} {S : SExt} {Γ : GeoP} {P : _root_.GlobalTheory.HeightCounting.Up.LayPAlt hL} (h : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL P) (hN : _root_.GlobalTheory.NRows.AtPt.OverNEAlt N)
    (H : WitMv (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s) {r : ∀ D : D7, Obj D → Prop}
    (hr : ∀ K (q : WPt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s K), EntC q.x.ker → _root_.GlobalTheory.NRows.AtPt.WitnessAtPoint (p := _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) P q → r (q.w.D q.Z) q.O) {Bd : BdT} (Lk : LkT Bd) :
    Lg1 KPx (IsBuiltE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s) (IsGoodE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s) fun U => RowE U Lk fun _ D O _ _ => r D O :=
  linkedBundleProperty_after_largeBaseCoreProperty (_root_.GlobalTheory.NRows.AtPt.lgSlotG_memSlot' h _) (_root_.GlobalTheory.NRows.AtPt.memSlot_entry_of_atWit hN H hr Lk)
end GlobalTheory.NRows.AtPt
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
namespace GlobalTheory.Mem.AtPtTransport
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists}
theorem overNE_of_NEb_alt {N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL}
    (hN : ∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) :
    _root_.GlobalTheory.NRows.AtPt.OverNEAlt N :=
  fun K B f T w Z Wt p0 t nch n xd c h => (hN K B f T w Z Wt p0 t nch n xd c h).elim fun x => ⟨x.1⟩
theorem atMem_at_wit_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), WitMv (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s →
    (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) →
    (∀ p : _root_.GlobalTheory.HeightCounting.Up.LayPAlt hL, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL p → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) fun Q L => RowE Q L fun κ D O _ _ => ∃ K : Ctx, κ.Of K ∧ O.L.sc = K.s ∧
      Val K.C K.cD K.ch O.L ∧ ∃ q : WPt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s K, q.Is D O ∧
        p K q.B q.f q.T q.w q.Z q.x.Wt _ q.x.what₂ _ q.x.n (_root_.GlobalTheory.Mem.Top.Bl.WPt.core_data_of_point (p := _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) q)) ∧
    ∀ P : ∀ D : D7, NChoice D → Prop, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL (fun _ _ _ _ w Z _ _ _ nch _ _ => P (w.D Z) nch) →
      _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) fun Q L => RowE Q L fun _ D O _ _ => P D O.ex.nch := by
  intro hL N S Γ H hN
  have hN' := _root_.GlobalTheory.Mem.AtPtTransport.overNE_of_NEb_alt hN
  refine ⟨fun p hp => ?_, fun P hP => ?_⟩
  · refine GlobalTheory.NRows.AtPt.linkedBundleProperty_after_largeBaseCoreProperty (_root_.GlobalTheory.NRows.AtPt.lgSlotG_memSlot' hp _) ?_
    refine RowE.of_all fun κ K β c b hk hβ _ => ?_
    obtain ⟨q, hq, _, hw⟩ := _root_.GlobalTheory.NRows.AtPt.exists_wPt_entC_atWit hN' H β hβ
    exact ⟨K, hk, β.sc, β.p.pt_val β.val, q, hq, hw⟩
  · exact _root_.GlobalTheory.NRows.AtPt.lg1_entry_of_atWit hP hN' H (r := fun D O => P D O.ex.nch) (fun K q _ t => t) _
end GlobalTheory.Mem.AtPtTransport
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExtraBoundOfTwistingEigenFacts
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsExtraAlt
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsFurtherLast
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AdmG14OfAux
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ConclusionOfAdmissibles
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BcAll
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BcPerm
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MainTyzAlt
set_option synthInstance.maxHeartbeats 200000

section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
noncomputable section
namespace GlobalTheory.BCPerm
abbrev _root_.GlobalTheory.BCPerm.mainTheorem : Prop :=  ∀ D : D7, SumRepresentations.tie0 D → _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D → SumRepresentations.adm5 D → ∀ (i : D.nd.Loc) (x : D.nd.X i)
    (P0 PI : D.naut.AV i) (Pa0 Pa : List (Part D.naut.CG)), D.naut.ptV i P0 = some x →
    D.naut.ptV i PI = some x → IsBCV D.nd D.naut i P0 Pa0 → IsBCV D.nd D.naut i PI Pa → Pa0.Perm Pa
end GlobalTheory.BCPerm
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
open GlobalTheory.BCPerm
noncomputable section
namespace UpperTheory.GalS
theorem bcPerm_alt : _root_.GlobalTheory.BCPerm.mainTheorem := by
  intro D ht h2 h5 i x P0 PI Pa0 Pa hx hx' hB0 hB
  have hG : GalIsoN D.nd D.naut i := by
    intro P Pb hPb
    obtain ⟨ρ, hc, hss, hw, -⟩ := isoRep D ht (_root_.UpperTheory.GalS.weak' h2) i P Pb hPb
    exact ⟨ρ, hc, hss, hw⟩
  have hC : GlobalTheory.RowTie.ChebSplit D.nd := by
    intro S
    rw [dense_iff_closure_eq]
    exact h5.2.2.1 (S : Set (PlE D.host)) S.finite_toSet
  have hAN : GlobalTheory.RowCopy.IsobaricDiscreteSelfDualStrongMultiplicityOne D.nd D.naut := h5.2.1
  have hS := splitBC_of_galIso D.R D.host D.what₂ D.nd D.naut i hG hC hAN
  have hd0 : (if D.nd.l i = D.host.pde then D.host.pde' else D.host.pde) ≠ 0 := by
    split_ifs
    exacts [D.host.pde'_prime.ne_zero, D.host.pde_prime.ne_zero]
  have hfin : (placesOver D.host.E (D.nd.l i) ∪ (D.nd.S i : Set (PlE D.host)) ∪ (D.nd.Q i : Set (PlE D.host)) ∪
      placesOver D.host.E (D.host.g 0) ∪ placesOver D.host.E (D.host.g 1) ∪
      placesOver D.host.E (if D.nd.l i = D.host.pde then D.host.pde' else D.host.pde)).Finite := by
    refine (((((GlobalTheory.RowTie.placesOver_finite_of_ne_zero _ _ (D.nd.lPrime i).out.ne_zero).union
      (D.nd.S i).finite_toSet).union (D.nd.Q i).finite_toSet).union
      (GlobalTheory.RowTie.placesOver_finite_of_ne_zero _ _ (D.host.g_prime 0).ne_zero)).union
      (GlobalTheory.RowTie.placesOver_finite_of_ne_zero _ _ (D.host.g_prime 1).ne_zero)).union
      (GlobalTheory.RowTie.placesOver_finite_of_ne_zero _ _ hd0)
  have hev : ∀ᶠ v in Filter.cofinite, IsSplitPl D.host v → D.naut.locV i P0 v = D.naut.locV i PI v := by
    rw [Filter.eventually_cofinite]
    refine hfin.subset fun v hv => ?_
    by_contra hn
    simp only [Set.mem_union, Finset.mem_coe, not_or] at hn
    obtain ⟨⟨⟨⟨⟨hl, hSv⟩, hQv⟩, hg0⟩, hg1⟩, hdv⟩ := hn
    refine hv fun hsp => GlobalTheory.RowTie.locV_eq_of_pt D.nd D.naut i hx hx' ⟨hsp, hl, hSv, hQv⟩ ?_ hdv
    intro k
    fin_cases k
    exacts [hg0, hg1]
  exact hS P0 PI hev Pa0 Pa hB0 hB
end UpperTheory.GalS
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BcAll
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules
open Polynomial
namespace GlobalTheory.CutAtGood
section AtPlace
attribute [local instance] Formalism.BasicNotions.Examples₂.NZ.neZero_g Formalism.BasicNotions.Examples₂.NZ.fact_g Classical.propDecidable
variable (D : D7)
end AtPlace
section OnMt
variable (D : D7) (μ : D.what₂.Tup) (j : ℕ)
end OnMt
section Record
variable {D : D7}
theorem isBCV_of_isBCV_of_same_ptV (hT0 : SumRepresentations.tie0 D) (hG : _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D) (h5 : SumRepresentations.adm5 D) (hBC : SumRepresentations.adm1 D) {i : D.nd.Loc}
    {x : D.nd.X i} {P0 PI : D.naut.AV i} (h0 : D.naut.ptV i P0 = some x) (hx : D.naut.ptV i PI = some x)
    {Pa0 : List (Part D.naut.CG)} (hB0 : IsBCV D.nd D.naut i P0 Pa0) : IsBCV D.nd D.naut i PI Pa0 := by
  obtain ⟨Pa, hPa⟩ := hBC i PI
  have hp := _root_.UpperTheory.GalS.bcPerm_alt D hT0 hG h5 i x P0 PI Pa0 Pa h0 hx hB0 hPa
  exact isBCV_perm hPa hp.symm
end Record
section Series
variable {D : D7}
end Series
section Main
end Main
theorem main_alt_alt : ∀ (D : D7) (P : Pend D), GlobalTheory.TypeLeaf.SerLoc D → admBC (D := D) → _root_.Formalism.MainNotions.PairedCharacterCondition.LocalGlobalCompatibility' (D := D) → SumRepresentations.tie0 D → SumRepresentations.adm5 D → EigSpan P → CentralElt D → ∀ (i : D.nd.Loc) (k : Fin 2), D.nd.l i = D.host.g k → ∀ π ∈ D.nd.Zgood i, ∃ (Xs : Set (D.nd.X i)) (β : Module.End (D.nd.O i) (D.nd.Mt i)) (b : D.nd.O i), CutAt i k π Xs β b ∧ TypeLocus P i k Xs := by
  intro D P hSer hBC hLGC hT0 h5 hEig hCE i k hl π hπ
  classical
  obtain ⟨hπZN, Sig, hSig, hgood⟩ := (D.Zgood_tie i π).1 hπ
  obtain ⟨σ', hσ'⟩ := P.Par_surj i π Sig hSig
  obtain ⟨P0, hP0, hB0⟩ := hSig
  let s : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), (ZMod (D.host.g kv.1))[X] := fun kv => D.ntypes.labPar kv.1 σ' kv.2
  obtain ⟨z, L, hLnd, hLall, hz⟩ := hCE i s
  have onMt_coe (μ : D.what₂.Tup) (j : ℕ) (c : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)))) :
      D.ntypes.onMt μ j (c : MonoidAlgebra ℂ (G0g D.nd)) = D.ntypes.cenMt μ j c := by
    unfold NTypes.onMt
    rw [dite_eq_left c.2]
  have onMt_sum (μ : D.what₂.Tup) (j : ℕ) {ι : Type} (S : Finset ι)
      (a : ι → MonoidAlgebra ℂ (G0g D.nd))
      (ha : ∀ i ∈ S, a i ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))) :
      D.ntypes.onMt μ j (∑ i ∈ S, a i) = ∑ i ∈ S, D.ntypes.onMt μ j (a i) := by
    induction S using Finset.induction_on with
    | empty =>
      unfold NTypes.onMt
      rw [Finset.sum_empty, Finset.sum_empty, dite_eq_left (Subalgebra.zero_mem _)]
      exact map_zero (D.ntypes.cenMt μ j)
    | insert i S hi ih =>
      have h₁ := ha i (Finset.mem_insert_self i S)
      have h₂ := Subalgebra.sum_mem (Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))) (fun x hx => ha x (Finset.mem_insert_of_mem hx))
      rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih (fun x hx => ha x (Finset.mem_insert_of_mem hx))]
      unfold NTypes.onMt
      rw [dite_eq_left (Subalgebra.add_mem _ h₁ h₂), dite_eq_left h₁, dite_eq_left h₂]
      exact map_add (D.ntypes.cenMt μ j) ⟨a i, h₁⟩ ⟨∑ x ∈ S, a x, h₂⟩
  let ef (s : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), (ZMod (D.host.g kv.1))[X]) (kv : Σ k : Fin 2, D.nd.PlG k) : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))) :=
    ⟨Formalism.MainNotions.ArithmeticCylinders.atPlace D kv.1 kv.2 (D.ntypes.eSer kv.1 (s kv)), atPlace_mem_center D kv.1 kv.2 _ (D.ntypes.eSer_central kv.1 (s kv))⟩
  have list_prod_eq (s : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), (ZMod (D.host.g kv.1))[X])
      (L : List (Σ k : Fin 2, D.nd.PlG k)) (hnd : L.Nodup) (hall : ∀ kv, kv ∈ L) :
      (L.map fun kv => Formalism.MainNotions.ArithmeticCylinders.atPlace D kv.1 kv.2 (D.ntypes.eSer kv.1 (s kv))).prod =
        ((∏ kv, ef s kv : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)))) : MonoidAlgebra ℂ (G0g D.nd)) := by
    have h1 : (L.map fun kv => Formalism.MainNotions.ArithmeticCylinders.atPlace D kv.1 kv.2 (D.ntypes.eSer kv.1 (s kv))) =
        (L.map (ef s)).map (Subalgebra.val _) := by rw [List.map_map]; rfl
    have h2 : L.toFinset = Finset.univ := Finset.eq_univ_of_forall fun kv => List.mem_toFinset.2 (hall kv)
    rw [h1, ← map_list_prod (Subalgebra.val _), ← List.prod_toFinset (ef s) hnd, h2]
    rfl
  have cen_prod_fix {M : Type} [AddCommGroup M] [Module ℂ M]
      (cen : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))) →ₐ[ℂ] Module.End ℂ M)
      {ι : Type} (e : ι → ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)))) (S : Finset ι) (F : M) (h : ∀ a ∈ S, cen (e a) F = F) :
      cen (∏ a ∈ S, e a) F = F := by
    induction S using Finset.induction_on with
    | empty => rw [Finset.prod_empty, map_one]; rfl
    | insert a S ha ih =>
      rw [Finset.prod_insert ha, map_mul, Module.End.mul_apply, ih (fun b hb => h b (Finset.mem_insert_of_mem hb)), h a (Finset.mem_insert_self a S)]
  have cen_prod_ne {M : Type} [AddCommGroup M] [Module ℂ M]
      (cen : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))) →ₐ[ℂ] Module.End ℂ M)
      {ι : Type} [DecidableEq ι] (e : ι → ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)))) (S : Finset ι) (F : M) (hne : cen (∏ a ∈ S, e a) F ≠ 0)
      (a : ι) (ha : a ∈ S) : cen (e a) F ≠ 0 := by
    intro h0
    apply hne
    rw [← Finset.prod_erase_mul S e ha, map_mul, Module.End.mul_apply, h0, map_zero]
  have hz' : ∀ F, D.ntypes.onMt (D.nd.mu i) (D.nd.j i)
      (PairedCharacterCondition.mapCoef (iotaO D.nd D.naut i) (z : MonoidAlgebra (D.nd.O i) (G0g D.nd))) F =
      (D.what₂.restRowsFiniteGroupCard : ℂ) • D.ntypes.cenMt (D.nd.mu i) (D.nd.j i) (∏ kv, ef s kv) F := by
    intro F
    rw [hz, list_prod_eq s L hLnd hLall]
    rw [show (D.what₂.restRowsFiniteGroupCard : ℂ) • ((∏ kv, ef s kv : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)))) :
        MonoidAlgebra ℂ (G0g D.nd)) = (((D.what₂.restRowsFiniteGroupCard : ℂ) • ∏ kv, ef s kv :
          ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)))) : MonoidAlgebra ℂ (G0g D.nd)) from rfl,
      onMt_coe, map_smul]
    rfl
  have hfixπ : ∀ PI : D.naut.AV i, D.naut.ptV i PI = some π → ∀ F ∈ D.naut.typeV i PI,
      D.ntypes.cenMt (D.nd.mu i) (D.nd.j i) (∏ kv, ef s kv) F = F := by
    intro PI hPI F hF
    have hB := _root_.GlobalTheory.CutAtGood.isBCV_of_isBCV_of_same_ptV hT0 hLGC h5 hBC hP0 hPI hB0
    have hF' := typeV_le_mtPar hσ' hB hF
    refine cen_prod_fix _ _ _ F fun kv _ => ?_
    rw [← onMt_coe]
    exact series_fix hSer i σ' F hF' kv.1 kv.2
  have hιb : iotaO D.nd D.naut i (D.what₂.restRowsFiniteGroupCard : D.nd.O i) = (D.what₂.restRowsFiniteGroupCard : ℂ) := map_natCast _ _
  have hscal : ∀ u ∈ heckeEig (D.nd.T i) (D.nd.act i) π,
      (P.zO i z).baseChange (FractionRing (D.nd.O i)) u = (D.what₂.restRowsFiniteGroupCard : D.nd.O i) • u :=
    hEig i z π _ fun PI hPI F hF => by rw [hz', hfixπ PI hPI F hF, hιb]
  let Xs : Set (D.nd.X i) :=
    {x | ∃ u ∈ heckeEig (D.nd.T i) (D.nd.act i) x, (P.zO i z).baseChange (FractionRing (D.nd.O i)) u ≠ 0}
  have hwit : ∀ x ∈ Xs, ∃ PI : D.naut.AV i, D.naut.ptV i PI = some x ∧ ∃ F ∈ D.naut.typeV i PI,
      ∀ kv, D.ntypes.cenMt (D.nd.mu i) (D.nd.j i) (ef s kv) F ≠ 0 := by
    rintro x ⟨u, hu, hne⟩
    by_contra hcon
    push Not at hcon
    apply hne
    have h0 := hEig i z x 0 (fun PI hPI F hF => ?_) u hu
    · rw [h0, zero_smul]
    · obtain ⟨kv, hkv⟩ := hcon PI hPI F hF
      rw [hz', map_zero, zero_smul]
      by_contra hc
      have hc' : D.ntypes.cenMt (D.nd.mu i) (D.nd.j i) (∏ kv, ef s kv) F ≠ 0 := fun h => hc (by rw [h, smul_zero])
      exact cen_prod_ne _ _ _ F hc' kv (Finset.mem_univ kv) hkv
  have hcard : D.what₂.restRowsFiniteGroupCard ≠ 0 := by
    rw [D.nd.restN_card_levelGroup_eq]
    refine Finset.prod_ne_zero_iff.2 fun k' _ => ?_
    have : NeZero (D.host.g k') := ⟨(D.host.g_prime k').ne_zero⟩
    exact pow_ne_zero _ Nat.card_pos.ne'
  have hb0 : (D.what₂.restRowsFiniteGroupCard : D.nd.O i) ≠ 0 := by
    intro h
    have := congrArg (iotaO D.nd D.naut i) h
    rw [hιb, map_zero] at this
    exact (Nat.cast_ne_zero.2 hcard) this
  have hπX : π ∈ Xs := by
    have hpos : 0 < Module.finrank ℂ ↥(⨆ P ∈ {P | D.naut.ptV i P = some π}, D.naut.typeV i P) := by
      obtain ⟨P2, hP2⟩ := D.naut.pt_surj i π
      refine Nat.pos_of_ne_zero fun h0 => D.naut.typeV_ne i P2 ?_
      have hbot := Submodule.finrank_eq_zero.1 h0
      exact le_bot_iff.1 (hbot ▸ le_iSup₂_of_le (f := fun P _ => D.naut.typeV i P) P2 hP2 le_rfl)
    rw [← D.naut.eig_dim i π] at hpos
    have hne : heckeEig (D.nd.T i) (D.nd.act i) π ≠ ⊥ := by
      intro h
      have e : D.nd.mult i π = Module.finrank (FractionRing (D.nd.O i))
          ↥(heckeEig (D.nd.T i) (D.nd.act i) π) := rfl
      rw [e, h, finrank_bot] at hpos
      exact lt_irrefl 0 hpos
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    refine ⟨u, hu, ?_⟩
    rw [hscal u hu, ← algebraMap_smul (FractionRing (D.nd.O i))]
    refine smul_ne_zero ?_ hu0
    rw [Ne, ← map_zero (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))]
    exact (IsFractionRing.injective (D.nd.O i) (FractionRing (D.nd.O i))).ne hb0
  refine ⟨Xs, P.zO i z, (D.what₂.restRowsFiniteGroupCard : D.nd.O i), ⟨hπX, (D.Z_tie i π).2 hπZN, ?_, fun f => P.zO_comm i z f,
    hb0, hscal, fun x hx u hu => ?_, ?_⟩, ?_⟩
  · intro x hx hxZ
    obtain ⟨PI, hPI, F, hF, hne⟩ := hwit x hx
    obtain ⟨Sig1, hS1⟩ := hasParamX_of_Z hT0 h5 hxZ
    obtain ⟨σ1, hσ1⟩ := P.Par_surj i x Sig1 hS1
    obtain ⟨P1, hP1, hB1⟩ := hS1
    have hF1 := typeV_le_mtPar hσ1 (_root_.GlobalTheory.CutAtGood.isBCV_of_isBCV_of_same_ptV hT0 hLGC h5 hBC hP1 hPI hB1) hF
    have hlab : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), s kv = D.ntypes.labPar kv.1 σ1 kv.2 := fun kv =>
      hSer i σ1 kv.1 kv.2 (s kv) F hF1
        (by rw [show Formalism.MainNotions.ArithmeticCylinders.atPlace D kv.1 kv.2 (D.ntypes.eSer kv.1 (s kv)) = ((ef s kv : ↥(Subalgebra.center ℂ
          (MonoidAlgebra ℂ (G0g D.nd)))) : MonoidAlgebra ℂ (G0g D.nd)) from rfl, onMt_coe]; exact hne kv)
    have hg1 : goodSig D.nd D.naut Sig1 := goodSig_of_labels (fun k' v => by
      rw [← labPar_eq hσ' k' v, ← labPar_eq hσ1 k' v]; exact hlab ⟨k', v⟩) hgood
    exact (D.Zgood_tie i x).2 ⟨(D.Z_tie i x).1 hxZ, Sig1, ⟨P1, hP1, hB1⟩, hg1⟩
  · by_contra h
    exact hx ⟨u, hu, h⟩
  · rw [← hl]
    exact lenUnit_natCast_le i _ hcard
  · refine ⟨fun v => s ⟨k, v⟩, fun v => ?_, fun x hx => ?_⟩
    · show Squarefree (D.ntypes.labPar k σ' v) ∧ ∀ u : (ZMod (D.host.g k))ˣ,
          u = PairedCharacterCondition.chiJ D i k v ∨ u = (PairedCharacterCondition.chiJ D i k v)⁻¹ → ¬ (D.ntypes.labPar k σ' v).IsRoot (u : ZMod (D.host.g k))
      rw [labPar_eq hσ' k v]
      exact good_labels hgood i k v
    · obtain ⟨PI, hPI, F, hF, hne⟩ := hwit x hx
      refine ⟨PI, hPI, fun v => ?_⟩
      have h1 := hne ⟨k, v⟩
      rw [← onMt_coe] at h1
      change D.ntypes.onMt (D.nd.mu i) (D.nd.j i)
        (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v (D.ntypes.eSer k (s ⟨k, v⟩))) F ≠ 0 at h1
      have hc : ∀ τ ∈ (Finset.univ : Finset ((P.lz k).Irr D.R.r)),
          Formalism.MainNotions.ArithmeticCylinders.atPlace D k v (if (P.lz k).lab τ = s ⟨k, v⟩ then (P.lz k).idem τ else 0) ∈
            Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)) := by
        intro τ _
        split_ifs
        · exact atPlace_mem_center D k v _ fun b => (P.lz k).idem_central τ b
        · rw [atPlace_zero]
          exact Subalgebra.zero_mem _
      rw [P.eSer_eq k, atPlace_sum, onMt_sum _ _ _ _ hc, LinearMap.sum_apply] at h1
      obtain ⟨τ, -, hτ⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
      by_cases hlab : (P.lz k).lab τ = s ⟨k, v⟩
      · rw [if_pos hlab] at hτ
        exact ⟨τ, (P.kty_spec i PI k v τ).2 ⟨F, hF, hτ⟩, hlab⟩
      · exfalso
        apply hτ
        rw [if_neg hlab, atPlace_zero]
        unfold NTypes.onMt
        rw [dite_eq_left (Subalgebra.zero_mem _)]
        have e0 : (⟨0, Subalgebra.zero_mem _⟩ : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)))) = 0 := rfl
        rw [e0, map_zero]
        rfl
end GlobalTheory.CutAtGood
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BcAllStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admBC_of_serLoc : ∀ (D : D7) (P : Pend D), GlobalTheory.TypeLeaf.SerLoc D → admBC (D := D) → _root_.Formalism.MainNotions.PairedCharacterCondition.LocalGlobalCompatibility' (D := D) → SumRepresentations.tie0 D → SumRepresentations.adm5 D → EigSpan P → CentralElt D → ∀ (i : D.nd.Loc) (k : Fin 2), D.nd.l i = D.host.g k → ∀ π ∈ D.nd.Zgood i, ∃ (Xs : Set (D.nd.X i)) (β : Module.End (D.nd.O i) (D.nd.Mt i)) (b : D.nd.O i), CutAt i k π Xs β b ∧ TypeLocus P i k Xs := by
  first | exact @_root_.GlobalTheory.CutAtGood.main_alt_alt | exact _root_.GlobalTheory.CutAtGood.main_alt_alt | (intros; apply _root_.GlobalTheory.CutAtGood.main_alt_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CutBoundOfSteps
set_option synthInstance.maxHeartbeats 200000

section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules
noncomputable section
namespace GlobalTheory.Pass
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem cutBound_of_steps_alt : _root_.GlobalTheory.Pass.NoCutStatement → ∀ (D : D7) (P : Pend D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (CT : ℕ), SumRepresentations.adm5 D → ElementDenominator.adm12 D → TieInePoly D → admT (D := D) CT → LocalPushoutProposition (D := D) → ResidualAbsIrreducible (D := D) → TypePrimeChoiceLemmas (D := D) → admDZ P → _root_.Formalism.MainNotions.PairedCharacterCondition.GaloisFamilyConditions' (D := D) → admG5 (D := D) → admG6 (D := D) → admTB (D := D) HW F → admBK (D := D) → admBC (D := D) → _root_.Formalism.MainNotions.PairedCharacterCondition.LocalGlobalCompatibility' (D := D) → FontaineAtPlacesOverL (D := D) → SumRepresentations.tie0 D → tieChi (D := D) → _root_.Formalism.MainNotions.PairedCharacterCondition.CongruenceModules.CongruenceAtTypePrimes' (D := D) CT fun i k ρ eta => ∀ π ∈ D.nd.Zgood i, ∀ Xs : Set (D.nd.X i), π ∈ Xs → TypeLocus P i k Xs → LocalCongruenceBound CT eta i ρ π (vccCut i Xs π) := by
  rintro ⟨_hCI, _hCen, hDeg, hType, hPotD, hPotDu, hJD, hJDu, hLift, hSub, hCont, hLocD, hLocDu, hHf, hRes, hGlob⟩
  intro D P HW F CT h5 h12 hIne hT hLOC hRbar hN5g hDZ hG14 hG5 hG6 hTB hBK hBC hLGC hFont htie0 hChi
  obtain ⟨hDJ, hPDR, hPT, hBr, hIE⟩ := GlobalTheory.Closing.closing_at_record D
  intro i k k' _hkk' hlk r ρ hr hdec eta s S sg U hs _hlog hCT _hsg hHost hsFin hSha π hπ Xs hπXs hTL
  have hπZ : π ∈ D.nd.Z i := (D.Z_tie i π).2 ((D.Zgood_tie i π).1 hπ).1
  have hHG : HG D.nd D.naut i := GlobalTheory.EigenProjector.HG_of_mem_Zgood D i π hπ
  have hdecπ := hdec π hπZ
  have hTLGC : TypeLGC P := hType D P hDZ htie0 hBC hLGC h5
  have hPH : PairedCharacterCondition.tiePH (D := D) := D.loc_tie
  have hl2 : D.nd.l i ≠ 2 := hlk ▸ Formalism.L2.Pj.g_ne_two D k
  have hloc : ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)), HfChar i w hw ∧
      LocBoundP i w hw r Xs (WpO D.nd i ρ π) (2 * D.R.r * eMax D CT eta) ∧
      ∀ c ∈ Finset.Icc 1 D.R.t, LocBoundP i w hw r Xs (chiRatO D.nd i c) (2 * 1 * eMax D CT eta) := by
    intro w hw
    have hdeg1 := (hDeg D hBr i k hlk).2 w hw
    have hPot : PotFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) (D.R.nV + 1) :=
      hPotD D P hTLGC hFont htie0 hBr hPH hChi hIE h12 hPT hIne i k hlk r ρ hr π hπZ hdecπ Xs hπXs hTL w hw
    have hCT' : CT * ((s + S) * (D.R.nV + 1) ^ 2 + (D.R.nV + 1) ^ 3) < D.nd.l i := hlk ▸ hCT
    have hH : eta + D.R.t + 1 < s + S := by omega
    have hsub := hSub D i r ρ hr π hdecπ Xs hπXs
    have key : ∀ (kk : ℕ) (M : GE D.nd →* Matrix (Fin kk) (Fin kk) (D.nd.O i)), SubTw i r Xs M →
        LocBoundP i w hw r Xs M (2 * kk * eMax D CT eta) := by
      intro kk M hM
      cases hsw : sg w
      · have hPotDu' := hPotDu D hPT i r hr Xs w hw _ hPot
        have hJ := hJDu D hDJ hPDR i r hr eta s S sg U hs hHost Xs w hw _ hsw hPot
        have hL := hLift D CT hT hFont i w hw hdeg1 (↥Xs) (fun x => rDuO D.nd i r x)
          (fun x => (hCont D i r hr x).2) eta (s + S) hH hCT' hPotDu' hJ
        exact hLocDu D hLOC hBK hFont hPDR i r hr Xs w hw hdeg1 _ _ hPot hL kk M hM
      · have hJ := hJD D i r eta s S sg U hs hHost Xs w hw hsw
        have hL := hLift D CT hT hFont i w hw hdeg1 (↥Xs) (fun x => rTwO D.nd i r x)
          (fun x => (hCont D i r hr x).1) eta (s + S) hH hCT' hPot hJ
        exact hLocD D hLOC hBK hFont hPDR i r hr Xs w hw hdeg1 _ _ hPot hL kk M hM
    exact ⟨hHf D P HW F hTB hIE i k hlk hl2 w hw hdeg1, key _ _ hsub.1, fun c hc => key _ _ (hsub.2 c hc)⟩
  have hG1 : TruncatedSeriesCountingIdentities.admG1 (D := D) i r := by
    intro g kk
    obtain ⟨f, hf⟩ := (hG14 i r hr).1 g kk
    have e : (fun x : D.nd.X i => ((rO D.nd i r x g).charpolyRev).coeff kk) = (f : D.nd.X i → D.nd.O i) :=
      funext fun x => (hf x).symm
    rw [e]
    exact f.2
  have hG4 : TruncatedSeriesCountingIdentities.admG4 (D := D) i r := by
    intro x v hl hS hQ g hg
    exact (hG14 i r hr).2.2.2 x v hl hS hQ (D.nd.plOm.1 v) (D.nd.plOm.2 v) g hg
  obtain ⟨S0, hS0, -⟩ := ((hN5g i k hlk hHG r ρ hr).2 π hπZ hdecπ).1 hπZ
  have hG := hGlob D i r ρ π Xs (2 * D.R.r * eMax D CT eta) (2 * 1 * eMax D CT eta) hr hG1
    (hRes D hRbar hG14 i r ρ hr π hπ hdecπ) hG4 (galois_condition_five_of D i r hG5 hHG hr)
    (GlobalTheory.TameDesign.main D i).2 (galois_condition_six_of D i r hG6 hHG hr) hdecπ (coefficient_compatibility_of D i (hBr i))
    ⟨S0, hS0⟩ hπZ hπXs hloc (hsFin π hπ) hSha
  have hcard : (placesOver D.host.E (D.nd.l i)).ncard = 2 * D.R.f := (hDeg D hBr i k hlk).1
  have hnat : (placesOver D.host.E (D.nd.l i)).ncard * (2 * D.R.r * eMax D CT eta + D.R.t * (2 * 1 * eMax D CT eta)) =
      D.R.f * (2 * ((2 * D.R.r + D.R.t * 2) * (CT * ((D.R.nV + 1) * ((D.R.nV + 1) ^ 2 / 4) +
        (eta + D.R.t + 1) * ((D.R.nV + 1) + (D.R.nV + 1) ^ 2 / 4))))) := by
    rw [hcard]; unfold eMax; ring
  rw [hnat] at hG
  have hrn : D.R.r ≤ D.R.nV := by unfold Ranks.nV; omega
  have hr2 : 2 ≤ D.R.r := hRbar.1
  refine ⟨D.R.nV + 1, (D.R.nV + 1) ^ 2 / 4, by omega, le_refl _, ?_, Nat.mul_div_le _ _, ?_⟩
  · have h9 : 9 ≤ (D.R.nV + 1) ^ 2 := by nlinarith
    omega
  · have hG' := (Rat.cast_le (K := ℝ)).2 hG
    push_cast at hG' ⊢
    linarith
end GlobalTheory.Pass
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TypePrimeBoundOfEtaBound
set_option synthInstance.maxHeartbeats 200000

section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules
namespace GlobalTheory.TypePrimeEta
end GlobalTheory.TypePrimeEta
namespace GlobalTheory
theorem typePrimeBound_of_etaBound_alt : ∀ (D : D7) (C : ℝ) (CT : ℕ), 8 * (CT : ℝ) ≤ C →
    _root_.Formalism.MainNotions.PairedCharacterCondition.CongruenceModules.CongruenceAtTypePrimes' (D := D) CT (EtaBound CT) → _root_.Formalism.MainNotions.PairedCharacterCondition.PairedCharacterConditionAlt (D := D) C CT := by
  intro D C CT hC hQ i k k' hkk hl r ρ hr hadm eta s S sg U h1 h2 h3 h4 h5 h7 h8
  obtain ⟨c, hη, hL⟩ := hQ i k k' hkk hl r ρ hr hadm eta s S sg U h1 h2 h3 h4 h5 h7 h8
  have hv : (padicValNat (D.host.g k) D.what₂.restRowsFiniteGroupCard : ℝ) ≤ 2 * D.R.f * (D.R.r : ℝ) ^ 2 := by
    exact_mod_cast TypePrimeEta.val_cardG0g_le D k k' hkk h2
  have key : ∀ π ∈ D.nd.Zgood i,
      (c π : ℝ) + (padicValNat (D.host.g k) D.what₂.restRowsFiniteGroupCard : ℝ) ≤ rhs C eta i ρ π := by
    intro π hπ
    obtain ⟨N, r', hN2, hN, hr1, hr4, hc⟩ := hL π hπ
    have hA := TypePrimeEta.first_le D.R.f D.R.r D.R.t CT N r' eta D.R.nV C hC hN2 hN hr4 rfl
    unfold rhs eT
    linarith
  have hη' : (D.nd.etaLoc i : ℝ) ≤ ∑ π ∈ D.nd.Zgood i,
      (D.nd.mult i π : ℝ) * ((c π : ℝ) + (padicValNat (D.host.g k) D.what₂.restRowsFiniteGroupCard : ℝ)) := by
    exact_mod_cast hη
  exact hη'.trans (Finset.sum_le_sum fun π hπ => mul_le_mul_of_nonneg_left (key π hπ) (Nat.cast_nonneg _))
end GlobalTheory
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ConclusionOfAdmissibles
set_option synthInstance.maxHeartbeats 200000

section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules
namespace GlobalTheory
theorem conclusion_of_typeLocus_alt {D : D7} (P : Pend D) (CT : ℕ)
    (hcut : ∀ (i : D.nd.Loc) (k : Fin 2), D.nd.l i = D.host.g k → ∀ π ∈ D.nd.Zgood i,
      ∃ (Xs : Set (D.nd.X i)) (β : Module.End (D.nd.O i) (D.nd.Mt i)) (b : D.nd.O i),
        CutAt i k π Xs β b ∧ TypeLocus P i k Xs)
    (hl5 : _root_.Formalism.MainNotions.PairedCharacterCondition.CongruenceModules.CongruenceAtTypePrimes' (D := D) CT fun i k ρ eta => ∀ π ∈ D.nd.Zgood i, ∀ Xs : Set (D.nd.X i), π ∈ Xs →
      TypeLocus P i k Xs → LocalCongruenceBound CT eta i ρ π (vccCut i Xs π)) :
    _root_.Formalism.MainNotions.PairedCharacterCondition.CongruenceModules.CongruenceAtTypePrimes' (D := D) CT (CongruenceLocalDecomposition CT) := by
  intro i k k' hkk' hl r ρ hr hdec eta s S sg U h1 h2 h3 h4 h5 h7 h8
  have hQ := hl5 i k k' hkk' hl r ρ hr hdec eta s S sg U h1 h2 h3 h4 h5 h7 h8
  have hc := hcut i k hl
  choose! Xs β b hcb using hc
  refine ⟨Xs, β, b, fun π hπ => ⟨(hcb π hπ).1, ?_⟩⟩
  exact hQ π hπ (Xs π) (hcb π hπ).1.1 (hcb π hπ).2
theorem admT_of_adm5_eigSpan_tieInePoly : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (P : Pend D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C : ℝ) (CT : ℕ), 8 * (CT : ℝ) ≤ C → SumRepresentations.adm5 D → EigSpan P → TieInePoly D → admT (D := D) CT → LocalPushoutProposition (D := D) → ResidualAbsIrreducible (D := D) → TypePrimeChoiceLemmas (D := D) → admDZ P → _root_.Formalism.MainNotions.PairedCharacterCondition.GaloisFamilyConditions' (D := D) → admG5 (D := D) → admG6 (D := D) → GlobalTheory.TypeLeaf.SerLoc D → admTB (D := D) HW F → admBK (D := D) → admBC (D := D) → _root_.Formalism.MainNotions.PairedCharacterCondition.LocalGlobalCompatibility' (D := D) → SumRepresentations.tie0 D → tieChi (D := D) → _root_.Formalism.MainNotions.PairedCharacterCondition.PairedCharacterConditionAlt (D := D) C CT := by
  intro hGAR D P HW F C CT hC hadm5 hEig hTie hT hLOC hRbar hN5g hDZ hG14 hG5 hG6 hSer hTB hBK hBC hLGC htie0 htieChi
  have hSteps : _root_.GlobalTheory.Pass.NoCutStatement := _root_.GlobalTheory.Pass.stepsNoCut_of_artin_alt hGAR
  have hCent : CentralElt D := hSteps.2.1 hSteps.1 D P
  have hl5 := _root_.GlobalTheory.Pass.cutBound_of_steps_alt hSteps D P HW F CT hadm5 (GlobalTheory.Per.ResFinite.adm12_elementDenominator D) hTie hT hLOC hRbar hN5g hDZ hG14 hG5 hG6 hTB
    hBK hBC hLGC (GlobalTheory.FontaineAdmissible.fontaineProperties_all_places D) htie0 htieChi
  have hcut := _root_.GlobalTheory.T.admBC_of_serLoc D P hSer hBC hLGC htie0 hadm5 hEig hCent
  have h3 : _root_.Formalism.MainNotions.PairedCharacterCondition.CongruenceModules.CongruenceAtTypePrimes' (D := D) CT (CongruenceLocalDecomposition CT) := _root_.GlobalTheory.conclusion_of_typeLocus_alt P CT hcut hl5
  have h4 : _root_.Formalism.MainNotions.PairedCharacterCondition.CongruenceModules.CongruenceAtTypePrimes' (D := D) CT (EtaBound CT) := by
    intro i k k' hkk' hl r ρ hr hdec eta s S sg U h1 h2 h3' h4 h5 h7 h8
    exact GlobalTheory.EtaFromCut.etaBound_of_cut D CT i k ρ eta
      (h3 i k k' hkk' hl r ρ hr hdec eta s S sg U h1 h2 h3' h4 h5 h7 h8)
  exact _root_.GlobalTheory.typePrimeBound_of_etaBound_alt D C CT hC h4
end GlobalTheory
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ConclusionOfAdmissiblesStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admT_of_artin_reciprocity_and_local_conditions : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (P : Pend D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C : ℝ) (CT : ℕ), 8 * (CT : ℝ) ≤ C → SumRepresentations.adm5 D → EigSpan P → TieInePoly D → admT (D := D) CT → LocalPushoutProposition (D := D) → ResidualAbsIrreducible (D := D) → TypePrimeChoiceLemmas (D := D) → admDZ P → _root_.Formalism.MainNotions.PairedCharacterCondition.GaloisFamilyConditions' (D := D) → admG5 (D := D) → admG6 (D := D) → GlobalTheory.TypeLeaf.SerLoc D → admTB (D := D) HW F → admBK (D := D) → admBC (D := D) → _root_.Formalism.MainNotions.PairedCharacterCondition.LocalGlobalCompatibility' (D := D) → SumRepresentations.tie0 D → tieChi (D := D) → _root_.Formalism.MainNotions.PairedCharacterCondition.PairedCharacterConditionAlt (D := D) C CT := by
  first | exact @_root_.GlobalTheory.admT_of_adm5_eigSpan_tieInePoly | exact _root_.GlobalTheory.admT_of_adm5_eigSpan_tieInePoly | (intros; apply _root_.GlobalTheory.admT_of_adm5_eigSpan_tieInePoly <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LemmaOpenOfIntegrality
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TypePrimeLemmasTheorem
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace Formalism.MainNotions.TypePrimeCongruences
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
def TypePrimeHypothesesAlt (D : D7) : Prop := SumRepresentations.adm5 D ∧ _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D ∧ AutomorphicSideWildInertia.ResidualIrreducibleGood D ∧ TypePrimeWildIdempotentChoice D
def TypePrimeLemmasStatement (D : D7) : Prop := _root_.Formalism.MainNotions.TypePrimeCongruences.TypePrimeHypothesesAlt D → TypePrimeChoiceConclusions D
end Formalism.MainNotions.TypePrimeCongruences
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations
namespace GlobalTheory
theorem lemma_open_of_integrality_alt (D : D7) (h41 : _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D) : TypePrimeCongruences.CongruenceModules.SupplierRemainingLemmas D :=
  fun i _ _ _ r ρ hr =>
    ⟨LargeLevelLemmas.span_lemma_clause i r (_root_.Formalism.MainNotions.N.galois_condition_one_of_alt D i r h41 hr),
      fun π _ _ => ⟨LargeLevelLemmas.eigenspace_lemma_clause i r ρ π, LargeLevelLemmas.relation_lemma_clause i r ρ π⟩⟩
theorem typePrimeCongruences_forall : ∀ D : D7, _root_.Formalism.MainNotions.TypePrimeCongruences.TypePrimeLemmasStatement D :=
  fun D hA => TypePrimeCongruences.CongruenceModules.supplier_of_choice_and_lemmas D hA.2.2.2 (_root_.GlobalTheory.lemma_open_of_integrality_alt D hA.2.1)
end GlobalTheory
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AdmG14OfAux
set_option synthInstance.maxHeartbeats 200000

section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules
namespace GlobalTheory.ClosingLocalInputs
theorem galoisFamilyConditions_of_sumRepresentations_alt (D : D7) (h41 : _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D) : _root_.Formalism.MainNotions.PairedCharacterCondition.GaloisFamilyConditions' (D := D) :=
  fun i r hr => (h41 i).2.2 r hr
theorem main_alt_alt : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.BhattScholzeIntegral → GlobalTheory.Published.FontaineBcris →
    GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK →
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
    ∀ (C : ℝ) (CT : ℕ), 40 ≤ CT → 8 * (CT : ℝ) ≤ C → (∃ P : Pend D, admDZ P ∧ EigSpan P) →
    SumRepresentations.tie0 D → SumRepresentations.adm1 D → _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D → SumRepresentations.adm5 D → _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → SumRepresentations.ConclusionG5 D → SumRepresentations.ConclusionG6 D →
    ResidualIrreducibleRankR D → GlobalTheory.TypeLeaf.SerLoc D → TypePrimeCongruences.TypePrimeWildIdempotentChoice D → TieInePoly D → tieChi (D := D) →
    _root_.Formalism.MainNotions.PairedCharacterCondition.PairedCharacterConditionAlt (D := D) C CT := by
  intro hGAR hBS hFB hBKL hLTD hLEC D HW F Cm C CT hCT hC hP htie0 hadm1 hadm2 hadm5 h41 hG5 hG6 hN9 hSer hO
    hIne hChi
  obtain ⟨P, hDZ, hEig⟩ := hP
  have hT : admT (D := D) CT := GlobalTheory.T.crystallinePeriodBound_all_constant_ge_forty hBS hFB hBKL hLTD hLEC D HW F Cm CT hCT
  have hLOC : LocalPushoutProposition (D := D) := GlobalTheory.T.local_absorption_length_bound_of_blochKato hBKL hLTD hLEC D HW F Cm
  have hRbar : ResidualAbsIrreducible (D := D) := GlobalTheory.Pass.residualRep_spans_matrixAlgebra_of_goodPoint D hN9
  have hN5g : TypePrimeChoiceLemmas (D := D) := _root_.GlobalTheory.typePrimeCongruences_forall D ⟨hadm5, h41, hN9, hO⟩
  have hTB : admTB (D := D) HW F := GlobalTheory.T.theorem_tb_of_local_blochKato_duality_euler hBKL hLTD hLEC D HW F Cm
  have hBK : admBK (D := D) := GlobalTheory.T.blochKatoLocal_all_of_tateDuality_eulerChar hBKL hLTD hLEC D
  exact _root_.GlobalTheory.T.admT_of_artin_reciprocity_and_local_conditions hGAR D P HW F C CT hC hadm5 hEig hIne hT hLOC hRbar hN5g hDZ
    (_root_.GlobalTheory.ClosingLocalInputs.galoisFamilyConditions_of_sumRepresentations_alt D h41) hG5 hG6 hSer hTB hBK hadm1 hadm2 htie0 hChi
end GlobalTheory.ClosingLocalInputs
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AdmG14OfAuxStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conclusion41_of_pAdicHodge_alt : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.BhattScholzeIntegral → GlobalTheory.Published.FontaineBcris → GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), ∀ (C : ℝ) (CT : ℕ), 40 ≤ CT → 8 * (CT : ℝ) ≤ C → (∃ P : Pend D, admDZ P ∧ EigSpan P) → SumRepresentations.tie0 D → SumRepresentations.adm1 D → _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D → SumRepresentations.adm5 D → _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → SumRepresentations.ConclusionG5 D → SumRepresentations.ConclusionG6 D → ResidualIrreducibleRankR D → GlobalTheory.TypeLeaf.SerLoc D → TypePrimeCongruences.TypePrimeWildIdempotentChoice D → TieInePoly D → tieChi (D := D) → _root_.Formalism.MainNotions.PairedCharacterCondition.PairedCharacterConditionAlt (D := D) C CT := by
  first | exact @_root_.GlobalTheory.ClosingLocalInputs.main_alt_alt | exact _root_.GlobalTheory.ClosingLocalInputs.main_alt_alt | (intros; apply _root_.GlobalTheory.ClosingLocalInputs.main_alt_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsFurtherLast
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
namespace GlobalTheory.NormFromFacts
theorem main_alt_alt : Hypotheses₂ → ∃ CT : ℕ, ∀ (D : D7) (nch : NChoice D), _root_.GlobalTheory.NFacts.NormChoiceFacts D nch → (PairedCharacterCondition.tieChi (D := D) ∧ (∃ Q : PairedCharacterCondition.Pend (D), PairedCharacterCondition.admDZ Q ∧ GlobalTheory.Pass.EigSpan Q) ∧ GlobalTheory.Pass.TieInePoly (D) ∧ GlobalTheory.TypeLeaf.SerLoc (D)) → _root_.Formalism.MainNotions.PairedCharacterCondition.PairedCharacterConditionAlt (D := D) (8 * (CT : ℝ)) CT := by
  intro hP
  refine ⟨40, ?_⟩
  intro D nch hf h
  obtain ⟨hchi, hQ, hine, hser⟩ := h
  obtain ⟨HW, F, ⟨Cm⟩⟩ := GlobalTheory.T.exists_wachFunctor_comparison_of_bhattScholze hP.bs D
  have hA := hf.adm.1.1
  exact _root_.GlobalTheory.T.conclusion41_of_pAdicHodge_alt hP.artin hP.bs hP.font hP.bk hP.tate hP.euler D HW F Cm _ 40 le_rfl le_rfl hQ hA.1 hA.2.2.1
    hA.2.2.2.1 hA.2.2.2.2.2.2 hf.Conclusion1.1 hf.Conclusion2.1 hf.Conclusion2.2.1 hf.rhoBar hser hf.duties.2.2.2 hine hchi
end GlobalTheory.NormFromFacts
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsFurtherLastStatement
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bound_tieChi_of_prints : Hypotheses₂ → ∃ CT : ℕ, ∀ (D : D7) (nch : NChoice D), _root_.GlobalTheory.NFacts.NormChoiceFacts D nch → (PairedCharacterCondition.tieChi (D := D) ∧ (∃ Q : PairedCharacterCondition.Pend (D), PairedCharacterCondition.admDZ Q ∧ GlobalTheory.Pass.EigSpan Q) ∧ GlobalTheory.Pass.TieInePoly (D) ∧ GlobalTheory.TypeLeaf.SerLoc (D)) → _root_.Formalism.MainNotions.PairedCharacterCondition.PairedCharacterConditionAlt (D := D) (8 * (CT : ℝ)) CT := by
  first | exact @_root_.GlobalTheory.NormFromFacts.main_alt_alt | exact _root_.GlobalTheory.NormFromFacts.main_alt_alt | (intros; apply _root_.GlobalTheory.NormFromFacts.main_alt_alt <;> assumption)
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
namespace GlobalTheory.ExtraFromFacts
theorem main_alt_alt : Hypotheses₂ → ∃ (C : ℝ) (CT : ℕ), 0 ≤ C ∧ ∀ (D : D7) (nch : NChoice D), _root_.GlobalTheory.NFacts.NormChoiceFacts D nch → (PairedCharacterCondition.tieChi (D := D) ∧ (∃ Q : PairedCharacterCondition.Pend (D), PairedCharacterCondition.admDZ Q ∧ GlobalTheory.Pass.EigSpan Q) ∧ GlobalTheory.Pass.TieInePoly (D) ∧ GlobalTheory.TypeLeaf.SerLoc (D)) → _root_.GlobalTheory.NLink.ExtraAlt D C CT := by
  intro hP
  obtain ⟨CT, hCT⟩ := _root_.GlobalTheory.T.exists_bound_tieChi_of_prints hP
  refine ⟨8 * (CT : ℝ), CT, by positivity, ?_⟩
  intro D nch hf h
  refine ⟨?_, hCT D nch hf h⟩
  obtain ⟨hchi, ⟨Q, hDZ, hE⟩, hine, hser⟩ := h
  have hS := _root_.GlobalTheory.T.no_cut_passes_of_artin_reciprocity hP.artin
  exact _root_.GlobalTheory.T.commutingEndomorphismCondition_of_serLoc D Q hE (hS.2.1 hS.1 D Q) hser hf.Conclusion1.1 hf.what₂.a.tieLab
    hf.adm.1.1.1 hf.adm.1.1.2.2.1 hf.adm.1.1.2.2.2.2.2.2
end GlobalTheory.ExtraFromFacts
end
end

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_const_tieChi_bound_of_facts : Hypotheses₂ → ∃ (C : ℝ) (CT : ℕ), 0 ≤ C ∧ ∀ (D : D7) (nch : NChoice D), _root_.GlobalTheory.NFacts.NormChoiceFacts D nch → (PairedCharacterCondition.tieChi (D := D) ∧ (∃ Q : PairedCharacterCondition.Pend (D), PairedCharacterCondition.admDZ Q ∧ GlobalTheory.Pass.EigSpan Q) ∧ GlobalTheory.Pass.TieInePoly (D) ∧ GlobalTheory.TypeLeaf.SerLoc (D)) → _root_.GlobalTheory.NLink.ExtraAlt D C CT := by
  first | exact @_root_.GlobalTheory.ExtraFromFacts.main_alt_alt | exact _root_.GlobalTheory.ExtraFromFacts.main_alt_alt | (intros; apply _root_.GlobalTheory.ExtraFromFacts.main_alt_alt <;> assumption)
end
end

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace UpperTheory.GalC
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.NLink
def CutGivesAlt : Prop := ∀ (D : D7) (nch : NChoice D), _root_.UpperTheory.GalC.GaloisPreconditions D nch → Tie4 D →
  ∃ c : CutD D, c.Good ∧ _root_.GlobalTheory.NFacts.NormChoiceFacts (cut D c) (nchTr c nch) ∧ Tie4 (cut D c)
theorem linkN_of_twGood_galoisPreconditions (hP : Hypotheses₂) (hG : _root_.UpperTheory.GalC.CutGivesAlt) {eps : ℝ} (Fm : FamP eps) (hTw : TwGood Fm)
    (hF : ∀ (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), _root_.UpperTheory.GalC.GaloisPreconditions (Fm.D x i) (Fm.ex x hx i).nch ∧ Tie4 (Fm.D x i)) : LinkN Fm := by
  classical
  obtain ⟨C, CT, hC, hEx⟩ := _root_.GlobalTheory.T.exists_const_tieChi_bound_of_facts hP
  have key : ∀ x (i : Fm.Ix x), ∃ c : CutD (Fm.D x i), ∀ hx : Fm.x1 < x, c.Good ∧
      _root_.GlobalTheory.NFacts.NormChoiceFacts (cut (Fm.D x i) c) (nchTr c (Fm.ex x hx i).nch) ∧ Tie4 (cut (Fm.D x i) c) := fun x i => by
    by_cases hx : Fm.x1 < x
    · obtain ⟨c, h⟩ := hG _ _ (hF x hx i).1 (hF x hx i).2
      exact ⟨c, fun _ => h⟩
    · exact ⟨CutD.all _, fun h => absurd h hx⟩
  choose c hc using key
  have hFF : _root_.GlobalTheory.NLink.FactsFAlt (gd Fm c) C CT := fun x hx i =>
    ⟨(hc x i hx).2.1, hEx _ _ (hc x i hx).2.1 (hc x i hx).2.2⟩
  refine linkN_of_gd Fm c (fun x hx i => ⟨(hc x i hx).1, ?_, (hF x hx i).1.what₂.rank _⟩)
    (GlobalTheory.T.linkN_along_family_of_localBounds _ (_root_.GlobalTheory.T.conclF_of_family_facts_and_bound_at_two_three hP _ C CT hC (twGood_gd Fm c hTw) hFF (_root_.UpperTheory.N.at23_family_alt hP _)))
  have p := (hF x hx i).1
  exact GlobalTheory.T.goodPointMultiplicityLeRank_proof _ _ p.Conclusion1.2.2 p.z p.adm.2.2 p.c2
theorem linkN_of_boundAtTwoThree_slot (hP : Hypotheses₂) (hG : _root_.UpperTheory.GalC.CutGivesAlt) (Q : GlobalTheory.Mem.Top.V4.Slot) (Lk : GlobalTheory.Fc.LkT _root_.GlobalTheory.Fc.BundleCondition)
    (hE : GlobalTheory.Fc.RowE Q Lk (fun _ D O _ _ => _root_.UpperTheory.GalC.GaloisPreconditions D O.ex.nch ∧ Tie4 D))
    (h23 : _root_.GlobalTheory.Fc.R1.SlotNormCondition Q Lk (fun 𝒞 => Closed 𝒞 fun Fm _ => _root_.GlobalTheory.NLink.BoundAtTwoThreeFamilyFonAlt Fm)) :
    _root_.GlobalTheory.Fc.R1.SlotNormCondition Q Lk (fun 𝒞 => Closed 𝒞 fun Fm _ => Formalism.MainNotions.LinkN Fm) := by
  refine ((GlobalTheory.Fc.RowE.row hE).and h23).imp fun 𝒜 σ _ hh => ?_
  obtain ⟨hA, ε1, hε, hcl⟩ := hh
  refine ⟨ε1, hε, fun e he hle => ?_⟩
  obtain ⟨K, hK⟩ := hcl e he hle
  refine ⟨K, fun Fm CH hc hL => ?_⟩
  exact _root_.UpperTheory.GalC.linkN_of_twGood_galoisPreconditions hP hG Fm hc.1.2 fun x hx i => hA Fm (GlobalTheory.Cp.d3_a hc) x hx i
theorem linkedAt_linkN_of_boundAtTwoThree (hP : Hypotheses₂) (hG : _root_.UpperTheory.GalC.CutGivesAlt) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL)
    (h1 : _root_.GlobalTheory.Fc.RL.LinkedAt p (fun S L => GlobalTheory.Fc.RowE S L fun _ D O _ _ => _root_.UpperTheory.GalC.GaloisPreconditions D O.ex.nch ∧ Tie4 D))
    (h3 : _root_.GlobalTheory.Fc.RL.LinkedAt p (fun S L => _root_.GlobalTheory.Fc.R1.SlotNormCondition S L fun 𝒞 => Closed 𝒞 fun Fm _ => _root_.GlobalTheory.NLink.BoundAtTwoThreeFamilyFonAlt Fm)) :
    _root_.GlobalTheory.Fc.RL.LinkedAt p (fun S L => _root_.GlobalTheory.Fc.R1.SlotNormCondition S L fun 𝒞 => Closed 𝒞 fun Fm _ => Formalism.MainNotions.LinkN Fm) := by
  obtain ⟨R1, r1, e1⟩ := h1
  obtain ⟨R3, r3, e3⟩ := h3
  refine ⟨_, r1.and r3, ?_⟩
  refine _root_.UpperTheory.GalC.linkN_of_boundAtTwoThree_slot hP hG _ _ ?_ ?_
  · exact GlobalTheory.Fc.EvP.mono (fun _ _ _ H β q => H β ⟨q.1, q.2.1⟩) e1
  · exact GlobalTheory.Fc.Row.strengthen (fun _ _ _ _ _ t => ⟨t.1, t.2.2⟩) e3
open Formalism.L2 Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.Fc in
theorem final_of_alt (hP : Hypotheses₂) (hG : _root_.UpperTheory.GalC.CutGivesAlt) (prN : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt) (hX : _root_.GlobalTheory.NRows.GeometricGaloisRepCompatibility)
    (dzs : GlobalTheory.Published.DepthZeroSupport) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (cDep : ℝ)
    (hF : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ _ nch _ _ => _root_.UpperTheory.GalC.GaloisPreconditions (w.D Z) nch)
    (hAt : _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfDependence hL cDep) (fun Q L => _root_.GlobalTheory.Fc.R1.SlotNormCondition Q L fun 𝒞 => Formalism.MainNotions.Closed 𝒞 fun Fm _ => _root_.GlobalTheory.NLink.BoundAtTwoThreeFamilyFonAlt Fm)) :
    _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfDependence hL cDep) (fun Q L => _root_.GlobalTheory.Fc.R1.SlotNormCondition Q L fun 𝒞 => Formalism.MainNotions.Closed 𝒞 fun Fm _ => Formalism.MainNotions.LinkN Fm) := by
  have hW : WitMv (_root_.GlobalTheory.Mem.Top.Bl.parametersOfDependence hL cDep).s :=
    GlobalTheory.T.witnesses_pass_along_set_division _ (_root_.GlobalTheory.NLink.Final.slot_mv_extension_with_list_geo_cl hL cDep anyGeometry)
  have hTf := _root_.GlobalTheory.T.tieChi_at_members_of_depthZero hX.ht prN dzs hL
  have hTr := (_root_.GlobalTheory.Mem.AtPtTransport.atMem_at_wit_alt hL (_root_.GlobalTheory.HeightCounting.Up.extensionWithList hL cDep) SExt.none (geoCl anyGeometry) hW
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ e => ⟨e.1⟩)).2
  exact _root_.UpperTheory.GalC.linkedAt_linkN_of_boundAtTwoThree hP hG hL (_root_.GlobalTheory.Mem.Top.Bl.parametersOfDependence hL cDep)
    (hTr (fun D nch => _root_.UpperTheory.GalC.GaloisPreconditions D nch ∧ Tie4 D) (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z hF hTf)) hAt
end UpperTheory.GalC
end
end
