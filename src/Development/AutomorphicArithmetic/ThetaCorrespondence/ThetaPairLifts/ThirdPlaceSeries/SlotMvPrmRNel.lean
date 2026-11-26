module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerUp
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FirstTermConditionHoldsAllStages

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SlotMvPrmRNel
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SlotMvPrmRNel
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
noncomputable section
namespace GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 4000000
theorem movable_prmR_nel_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (cDep : ℝ) (Γ : GeoP), PositionMv (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) SExt.none (geoCl Γ)).s := by
  intro hL cDep Γ
  intro K B f T w Z O x N h O' hO' col n
  have hrows := _root_.GlobalTheory.T.rows_pass_to_moved_divisionLatticesHeights
    K B f T w Z x.Wt O x.what₂ N h O' hO'
  obtain ⟨t', hs, hgeo, hpk, hobj, hrx⟩ := hrows
  obtain ⟨nch', xd', hkept, hnx, -, -, hmv⟩ := _root_.GlobalTheory.T.exists_kept_choice_upper_lattice_alt hL K B f T w Z x.Wt Z.S N h O.nch O.xd
  obtain ⟨hn1, hn2⟩ := hnx rfl
  subst hO'
  have e1 : nch' = (O.tr N h).nch := eq_of_heq hn1
  have e2 : xd' = (O.tr N h).xd := eq_of_heq hn2
  subst e1 e2
  have hlp := _root_.GlobalTheory.Mem.GridMove.listPin_rowsSame cDep K.s.b K B f T w Z x.Wt Z.S N h O.p0 x.what₂ (O.tr N h).p0 t' hs x.nx.2.1.2.down
  obtain ⟨P, y, l, hls, hW, hk⟩ := x.nx.2.2.down
  obtain ⟨c⟩ := hmv O.p0 x.what₂ x.n (O.tr N h).p0 t' n hs hgeo ⟨x.nx.1, x.nx.2.1.1⟩
  obtain ⟨s⟩ := _root_.GlobalTheory.T.spectralStageData_transfer_lattices_heights K B f T w Z x.Wt O.p0 x.what₂ x.col.toColT N h (O.tr N h).p0 t' col.toColT hpk ⟨x.sx.1⟩
  obtain ⟨o⟩ := _root_.GlobalTheory.T.divisionGeometryScalars_transfer_setDivision Γ K B f T w Z x.Wt N h O (O.tr N h) rfl x.what₂ t' hs x.ox
  exact ⟨t', hobj x.obj, hrx ⟨x.rx⟩, ⟨⟨c.1, ⟨c.2, ⟨hlp⟩⟩, ⟨⟨P, y, l, hls, hW, kept_trans hk hkept⟩⟩⟩⟩, ⟨⟨s, PUnit.unit⟩⟩, ⟨o⟩⟩
end GlobalTheory.HeightCounting.Up
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SlotMvPrmRNelStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.slot_mv_extension_with_origin_geo_cl : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (cDep : ℝ) (Γ : GeoP), PositionMv (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) SExt.none (geoCl Γ)).s := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.movable_prmR_nel_alt | exact _root_.GlobalTheory.HeightCounting.Up.movable_prmR_nel_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.movable_prmR_nel_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OrgOfKept
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OrgOfKept
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
namespace GlobalTheory.HeightCounting.Up
theorem org_of_kept_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {cDep : ℝ} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B}
    {w : ColW B f T} {D D' : D7} {Wt : Set B.places.Pl} {nch : NChoice D} {nch' : NChoice D'}
    (h : _root_.GlobalTheory.HeightCounting.Up.OriginData hL cDep K w Wt nch) (hk : Kept nch nch') : _root_.GlobalTheory.HeightCounting.Up.OriginData hL cDep K w Wt nch' := by
  obtain ⟨P, x, l, h1, h2, h3⟩ := h
  exact ⟨P, x, l, h1, h2, kept_trans_layer h3 hk⟩
set_option maxHeartbeats 4000000 in
theorem lv3Mv_extensionWithOrigin_and_nEog : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (cDep : ℝ) (S : SExt) (Γ : GeoP), LevelThreeCondition (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) S Γ).s ∧ LevelThreeCondition (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.GeometricNormExtension hL cDep) S Γ).s := by
  intro hL cDep S Γ
  constructor
  · intro K B f T w Z l S' N h
    have htransport := _root_.GlobalTheory.T.adelicRowsDivision_transport_spectralStage_lattices K B f T w Z l.Wt l.p0 l.what₂ S' N h
    obtain ⟨p0', t', hs, hgeo, hpk, hrx⟩ := htransport
    have hchoice := _root_.GlobalTheory.T.exists_kept_choice_upper_lattice_alt hL K B f T w Z l.Wt S' N h l.nch l.xd
    obtain ⟨nch', xd', hk, -, hn, -, hnx⟩ := hchoice
    have hnnew := hn l.n
    obtain ⟨n'⟩ := hnnew
    have hrxnew := hrx ⟨l.rx⟩
    obtain ⟨rx'⟩ := hrxnew
    have hdata := l.nx
    obtain ⟨c, ⟨e, ⟨pin⟩⟩, ⟨org⟩⟩ := hdata
    have hnxnew := hnx l.p0 l.what₂ l.n p0' t' n' hs hgeo ⟨c, e⟩
    obtain ⟨⟨c', e'⟩⟩ := hnxnew
    have pin' := GlobalTheory.Mem.GridMove.listPin_rowsSame cDep K.s.b K B f T w Z l.Wt S' N h l.p0 l.what₂ p0' t' hs pin
    exact ⟨Lv3.mk ⟨l.g, l.coh, l.Wt, p0', t', rx'⟩ nch' n' xd'
      l.chiT ⟨c', ⟨e', ⟨pin'⟩⟩, ⟨_root_.GlobalTheory.HeightCounting.Up.org_of_kept_alt org hk⟩⟩, hpk⟩
  · intro K B f T w Z l S' N h
    have htransport := _root_.GlobalTheory.T.adelicRowsDivision_transport_spectralStage_lattices K B f T w Z l.Wt l.p0 l.what₂ S' N h
    obtain ⟨p0', t', hs, hgeo, hpk, hrx⟩ := htransport
    have hchoice := _root_.GlobalTheory.T.exists_kept_choice_upper_lattice_alt hL K B f T w Z l.Wt S' N h l.nch l.xd
    obtain ⟨nch', xd', hk, -, hn, hg, hnx⟩ := hchoice
    have hnnew := hn l.n
    obtain ⟨n'⟩ := hnnew
    have hrxnew := hrx ⟨l.rx⟩
    obtain ⟨rx'⟩ := hrxnew
    have hdata := l.nx
    obtain ⟨c, ⟨⟨e, ⟨pin⟩⟩, ⟨org⟩⟩, ⟨good⟩⟩ := hdata
    have hnxnew := hnx l.p0 l.what₂ l.n p0' t' n' hs hgeo ⟨c, e⟩
    obtain ⟨⟨c', e'⟩⟩ := hnxnew
    have pin' := GlobalTheory.Mem.GridMove.listPin_rowsSame cDep K.s.b K B f T w Z l.Wt S' N h l.p0 l.what₂ p0' t' hs pin
    exact ⟨Lv3.mk ⟨l.g, l.coh, l.Wt, p0', t', rx'⟩ nch' n' xd'
      l.chiT ⟨c', ⟨⟨e', ⟨pin'⟩⟩, ⟨_root_.GlobalTheory.HeightCounting.Up.org_of_kept_alt org hk⟩⟩, ⟨hg good⟩⟩, hpk⟩
end GlobalTheory.HeightCounting.Up
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OrgOfKeptStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lv3Mv_extensionWithOrigin_and_NEog : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (cDep : ℝ) (S : SExt) (Γ : GeoP), LevelThreeCondition (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) S Γ).s ∧ LevelThreeCondition (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.GeometricNormExtension hL cDep) S Γ).s := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.lv3Mv_extensionWithOrigin_and_nEog | exact _root_.GlobalTheory.HeightCounting.Up.lv3Mv_extensionWithOrigin_and_nEog | (intros; apply _root_.GlobalTheory.HeightCounting.Up.lv3Mv_extensionWithOrigin_and_nEog <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NonGaloisEtaJMem
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EtaJLocalCompatibility
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 4000000 in
theorem GlobalTheory.etaJ_with_local_data_eq_alt : ∀ (hPr : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}, KPx B f → Forced K B T → Start K B f T w → ∀ (x : St P) (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) (big : (Dof x).what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 (Dof x))), _root_.GlobalTheory.CoefDuty.BuiltAlt l.a.A l.mt.M l.c.ch l.c.tp.tup big L → SumRepresentations.hypO (withLoc L) → ∀ (M : MtFam (withLoc L)) (Tn : NormalizedLocalCompatibility (withLoc L) M) (Q : (withLoc L).what₂.places.Pl → Finset (PlE (withLoc L).host)), HeckeStdTw Tn.B → (∀ i, (withLoc L).nd.Q i = Q ((withLoc L).nd.w i)) → (∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ (withLoc L).R.m) (w' : (withLoc L).what₂.places.Pl), (withLoc L).what₂.muAt w' ≠ (withLoc L).what₂.mu0 → GlobalTheory.CoefDuty.LatInt (withLoc L) M (Q w') j h1 h2 w') → HeckeTied (withLoc L) M → HeckeRational (withLoc L) M → AVTied (withLoc L) M → (∀ i, GlobalTheory.CoefDuty.ClassSum (M.loc i)) → (withLoc L).nd.EigSpan → Rows.IsotInternal (withLoc L).what₂ → SumRepresentations.Conclusion42 (withLoc L) → SumRepresentations.ConclusionZ (withLoc L) → GoodFTAll (withLoc L) → ∀ (j : ℕ) (v : B.places.Pl), 1 ≤ j → j ≤ (Dof x).R.m → ∀ v' : (withLoc L).what₂.places.Pl, HEq v' v → (withLoc L).what₂.etaJ j v' = P.q.eta j v := by
  intro hPr hL K B f T w P hK hF hS x l big L hB hO M Tn Q hstd hQ hlat hT hR hAV hCS hE hI h42 hZ hG j v h1 h2 v' hv
  obtain rfl : v' = v := eq_of_heq hv
  have hTup : Formalism.L2.DIV.TupTie (withLoc L) (famR (w.st x.o.Z) w.I P.hX (usedOf w.I T P.Wt) x.m.z.Xg x.m.z.tr).A
      ((famR (w.st x.o.Z) w.I P.hX (usedOf w.I T P.Wt) x.m.z.Xg x.m.z.tr).indefDown (s0Of x.m.z.R x.m.z.F)) x.r.Y.tup :=
    ⟨x.r.Y.tup0, x.r.Y.muAt, x.m.z.R.hv0, fun a b h => by rw [← x.r.Y.tupT_tup a, h, x.r.Y.tupT_tup]⟩
  have hTw : ∀ y, y ∈ ((famR (w.st x.o.Z) w.I P.hX (usedOf w.I T P.Wt) x.m.z.Xg x.m.z.tr).indefDown (s0Of x.m.z.R x.m.z.F)).Tw ↔
      ((famR (w.st x.o.Z) w.I P.hX (usedOf w.I T P.Wt) x.m.z.Xg x.m.z.tr).indefDown (s0Of x.m.z.R x.m.z.F)).μ y ≠
        (famR (w.st x.o.Z) w.I P.hX (usedOf w.I T P.Wt) x.m.z.Xg x.m.z.tr).A.μ0 :=
    fun y => ⟨x.m.z.pins.char.tup.mu_ne y, fun h => by_contra fun hw => h (x.m.z.pins.char.tup.mu_off y hw)⟩
  have hθ := GlobalTheory.Mem.ThRead.theta_of_noEta GlobalTheory.Mem.ThetaRead3.thetaP_read_noEta GlobalTheory.Mem.ThOrth.thG_eq_zero_of_orth_noEta
    _ _ _ _ _ _ _ x.m.z.R x.m.z.F x.m.z.cG x.s.p0 x.r.Y x.r.Z x.m.z.pins x.m.intersectionNumber_baseChange
  have hZ0 := GlobalTheory.Mem.R3.DivisionRationalLift.rationalReadingNoCongruence_thetaComplement_spanned _ _ _ _ _ _ _ x.m.z.R x.m.z.F x.m.z.cG x.s.p0 x.r.Y x.r.Z x.m.z.pins x.m.intersectionNumber_baseChange
  have key := GlobalTheory.T.congruenceLength_twistedPlaces_of_heckeIntegrality (withLoc L) _ _ _ _ (famR (w.st x.o.Z) w.I P.hX (usedOf w.I T P.Wt) x.m.z.Xg x.m.z.tr).A
    x.m.z.F.P0 x.m.z.F.ψ0 ((famR (w.st x.o.Z) w.I P.hX (usedOf w.I T P.Wt) x.m.z.Xg x.m.z.tr).fam3.toSub2 (zsOf x.m.z.R x.m.z.F))
    x.r.Y.tup x.r.Y.eMt 1 x.m.intersectionNumber_baseChange.ok.ok2 le_rfl
    ((famR (w.st x.o.Z) w.I P.hX (usedOf w.I T P.Wt) x.m.z.Xg x.m.z.tr).indefDown (s0Of x.m.z.R x.m.z.F)) M Tn
    hTup hTw (fun i y _ => ⟨x.r.Y.formsL i _, x.r.Y.latL i _, hZ0 i _⟩) hstd Q hQ hlat hT hR hAV hCS x.r.Z.jW rfl
    (fun i y _ x' => hθ i _ x') hE hI h42 hZ hG
  obtain ⟨i, rfl⟩ : ∃ i : Fin (Dof x).R.m, j = (i : ℕ) + 1 := ⟨⟨j - 1, by omega⟩, by simp only; omega⟩
  refine (key i v').trans (Eq.trans ?_ (x.m.eta _ v'))
  unfold Rw.etaOf
  rw [dite_eq_left ⟨by omega, i.2⟩]
  split_ifs with ha hb hb
  · simp only [Nat.add_sub_cancel, Fin.eta]
    rfl
  · exact (hb ha).elim
  · exact (ha hb).elim
  · rfl
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaJ_local_compatibility_alt : ∀ (hPr : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}, KPx B f → Forced K B T → Start K B f T w → ∀ (x : St P) (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) (big : (Dof x).what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 (Dof x))), _root_.GlobalTheory.CoefDuty.BuiltAlt l.a.A l.mt.M l.c.ch l.c.tp.tup big L → SumRepresentations.hypO (withLoc L) → ∀ (M : MtFam (withLoc L)) (Tn : NormalizedLocalCompatibility (withLoc L) M) (Q : (withLoc L).what₂.places.Pl → Finset (PlE (withLoc L).host)), HeckeStdTw Tn.B → (∀ i, (withLoc L).nd.Q i = Q ((withLoc L).nd.w i)) → (∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ (withLoc L).R.m) (w' : (withLoc L).what₂.places.Pl), (withLoc L).what₂.muAt w' ≠ (withLoc L).what₂.mu0 → GlobalTheory.CoefDuty.LatInt (withLoc L) M (Q w') j h1 h2 w') → HeckeTied (withLoc L) M → HeckeRational (withLoc L) M → AVTied (withLoc L) M → (∀ i, GlobalTheory.CoefDuty.ClassSum (M.loc i)) → (withLoc L).nd.EigSpan → Rows.IsotInternal (withLoc L).what₂ → SumRepresentations.Conclusion42 (withLoc L) → SumRepresentations.ConclusionZ (withLoc L) → GoodFTAll (withLoc L) → ∀ (j : ℕ) (v : B.places.Pl), 1 ≤ j → j ≤ (Dof x).R.m → ∀ v' : (withLoc L).what₂.places.Pl, HEq v' v → (withLoc L).what₂.etaJ j v' = P.q.eta j v := by
  first | exact @_root_.GlobalTheory.etaJ_with_local_data_eq_alt | exact _root_.GlobalTheory.etaJ_with_local_data_eq_alt | (intros; apply _root_.GlobalTheory.etaJ_with_local_data_eq_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LatIntMember
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty
namespace GlobalTheory.CoefDuty
theorem latInt_member_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (M : MtFam D) (C : NChoice D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E), MtInput D M tup C.Q → ∀ big L, _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tup big L → (∀ i, (withLoc L).nd.Q i = C.Q ((withLoc L).nd.w i)) ∧ ∀ j h1 h2 w, (withLoc L).what₂.muAt w ≠ (withLoc L).what₂.mu0 → LatInt (withLoc L) (mtL L M) (C.Q w) j h1 h2 w := by
  intro D cf jE A M C tup hM big L hB
  obtain ⟨Sp, -, -⟩ := hB
  refine ⟨fun i => ?_, fun j h1 h2 w hw => ?_⟩
  · have h : i ∈ L.X.nd.locs (L.X.nd.j i) (L.X.nd.w i) := (L.X.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩
    exact (Sp.Q_eq _ _ i h).trans (Sp.Qc_eq _ _)
  · obtain ⟨j, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    have h2' : j < D.R.m := h2
    exact ⟨(hM.full w ⟨j, h2'⟩ hw).1, fun v k s ϖ hg hc hu => hM.int w ⟨j, h2'⟩ v k s ϖ hw hg hc hu⟩
end GlobalTheory.CoefDuty
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section
namespace GlobalTheory.EtaMem
open GlobalTheory.CoefDuty GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem exists_etaJ_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.PointStatement hL → AllSt fun _ _ _ _ _ P x => ∀ l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x, _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' => SumRepresentations.hypO D' → ∀ j v, 1 ≤ j → j ≤ (Dof x).R.m → ∀ v' : D'.what₂.places.Pl, HEq v' v → D'.what₂.etaJ j v' = P.q.eta j v := by
  intro hPr hL hPt
  have hG := _root_.GlobalTheory.T.allSt_goodFTAll_of_levelA hPr hL
  have hI := GlobalTheory.T.twistedPlace_innerProduct_classSum_rows
  have hcheb := GlobalTheory.ChebSplitDense.chebSplit_nd hPr.what₂.cheb
  unfold _root_.GlobalTheory.HeightCounting.Up.PointStatement at hPt
  unfold AllSt at hPt hG ⊢
  unfold OverRows at hI
  unfold StepW GroupRetwisting.Step EvLgG at hPt hG ⊢
  refine EvG.imp (EvG.inter (EvG.inter hPt hG) hI) fun K _ _ _ _ h => ?_
  refine large₂.imp (large₂.inter (large₂.inter h.1.1 h.1.2) h.2) fun B f T _ g => ?_
  intro hKP hF _ w hS P x l
  have hpin : ColPin w := hS.1.some
  obtain ⟨big, hbig⟩ := g.1.1 hKP hF trivial w hS P x l
  refine ⟨big, fun L hB hO => ?_⟩
  have hB0 := hB
  obtain ⟨hconds, hEig, hIso⟩ := hbig L hB
  obtain ⟨-, -, h42, hZ⟩ := hconds hO
  have hgood : GoodFTAll (withLoc L) := g.1.2 hKP hF trivial w hS P x l.toLA
  have hmt : MtInput (Dof x) l.mt.M l.c.tp.tup l.c.ch.Q := by
    have h0 := l.mt.mt
    have e1 := l.c.xi_eq
    have e2 := l.c.Q_eq
    unfold TupTied.tup
    rw [e1, e2]
    exact h0
  have hlat := _root_.GlobalTheory.CoefDuty.latInt_member_alt (Dof x) (cfOf x) l.a.jE l.a.A l.mt.M l.c.ch l.c.tp.tup hmt big L hB
  have hsum : SumTw (Dof x) l.mt.M := g.2 hKP w hpin x.o.Z P.Wt P.hX x.m.z x.s.p0 x.r.Y x.m.intersectionNumber_baseChange x.m.exAt x.m.inGeo
    x.fits.grp x.fits.grpAt l.mt.M l.c.tp.tup l.c.ch.Q l.mt.ad hmt
  obtain ⟨Sp, ⟨Au⟩, hss⟩ := hB
  obtain ⟨Hk, -⟩ := _root_.GlobalTheory.FitHecke.heckeOpen_withLoc_alt (Dof x) (cfOf x) l.a.jE l.a.A (lowAll (Dof x)) l.Pq l.rat.S l.rat.In.hL
    l.rat.In.eig l.rat.In.θ l.b.Bs l.mt.M l.c.ch l.c.tp l.c.side hmt l.a.elem.star l.a.elem.int l.a.elem.split
    (hcheb (Dof x)) big L Sp Au
  let cover : NormalizedLocalCompatibility (withLoc L) (mtL L l.mt.M) :=
    { B := { Sp.B with }
      Q_eq := Sp.Q_eq
      mx := Sp.mx
      mx_max := Sp.mx_max
      mx_inj := Sp.mx_inj
      mx_all := Sp.mx_all
      phO := Sp.phO
      phK := Sp.phK
      phK_alg := Sp.phK_alg
      phK_emb := Sp.phK_emb
      Psi := Sp.Psi
      Psi_inj := Sp.Psi_inj
      Psi_range := Sp.Psi_range
      Psi_pr := Sp.Psi_pr
      ptX := Sp.ptX
      ptX_hT := Sp.ptX_hT
      iotaC := Sp.iotaC
      iotaC_coh := fun j w i h z => by
        have e1 : (withLoc L).naut.iotaQ i = Sp.iq i := Au.iotaQ i
        have e2 : (withLoc L).naut.iotaQC i = qCast ((withLoc L).nd.w_l i) (l.a.A.pl.ι ((withLoc L).nd.w i)) := Au.iotaQC i
        unfold iotaOC
        rw [RingHom.comp_apply, RingHom.comp_apply, e1, e2]
        exact Sp.iotaC_coh j w i h z }
  have hstd : HeckeStdTw cover.B := heckeStdTw_of_std Sp.std
  have hcls : ∀ i, CoefDuty.ClassSum ((mtL L l.mt.M).loc i) := by
    intro i
    have hj := L.X.j_range i
    have h0 := hsum (L.X.w i) (L.X.w_tw i) (L.X.j i) hj.1 hj.2
    exact GlobalTheory.FitHecke.mt_transport l.mt.M (fun μ j m => CoefDuty.ClassSum m) (L.X.mu_w i).symm rfl hj.1 hj.2 hj.1 hj.2 h0
  exact _root_.GlobalTheory.T.etaJ_local_compatibility_alt hPr hL hKP hF hS x l big L hB0 hO (mtL L l.mt.M) cover l.c.ch.Q hstd hlat.1 hlat.2 Hk.hecke Hk.rational Hk.av hcls hEig hIso h42 hZ hgood
end GlobalTheory.EtaMem
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_etaJ_eq_eta_of_levelC : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.PointStatement hL → AllSt fun _ _ _ _ _ P x => ∀ l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x, _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' => SumRepresentations.hypO D' → ∀ j v, 1 ≤ j → j ≤ (Dof x).R.m → ∀ v' : D'.what₂.places.Pl, HEq v' v → D'.what₂.etaJ j v' = P.q.eta j v := by
  first | exact @_root_.GlobalTheory.EtaMem.exists_etaJ_alt | exact _root_.GlobalTheory.EtaMem.exists_etaJ_alt | (intros; apply _root_.GlobalTheory.EtaMem.exists_etaJ_alt <;> assumption)
end
end
end
