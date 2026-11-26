module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLocalModelsOfSplitUnramifiedJoints
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueColumnJointsHoldAllTuples
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalModelBoundPlaceOverSecondEmbedding
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowAtOfStdTie

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TuplesHaveLocalModelsAtConstructedPointOverTrueC
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TuplesHaveLocalModelsOfStandardColumnObjects
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JointsAtAllStd
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelRelationTrueColumnsJointsAllTuples
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StdKerStdRdMark
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.Pdv.stdKer_stdRd_mark : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), I.StdKer l Z t → ∃ t' : KerEntTied ex, I.StdKer l Z t' ∧ GlobalTheory.Pdv.StdRd I l Z t' ∧ t'.TopPinned ∧ (∀ (u : B.Word) (a : I.ι) (i : ℕ) (c : ((I.rec7 l Z).chTw u a).cls i), (t'.rd u a).pin i c ↔ (i + 1 ≤ B.R.m ∨ ∃ d, OverRow (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u d ((I.stp u a i).rep c).1.1)) := by
  intro B X I hOk hP l Z L hT Gi Gl K Y cX ex t hS
  rcases t with ⟨cc, cc_rec, cc_ok, δ, δ_ok, Bb, χ, χ_ok, idl, idl_ok, χ_rec, cD, Xf, seam, seam_ok, Pr, pr_ok, g_rec, Ch, sel, S, word, T_rec, tup, Q_rec, cst, idx, m2, glob, glob_σ, glob_xi, idx_ok, O, rd, rd_chain, O_dgen, O_S, O_lat, O_Th, unf, ent, ent_lam, kf, kf_un, served⟩
  obtain ⟨hX, hseam, hPr, hCh, hsel, hSS, hword, htup, hcst, hidx, hm2, hglob, hamb, hδ, hO⟩ := hS
  dsimp only at hX hseam hPr hCh hsel hSS hword htup hcst hidx hm2 hglob hamb hδ hO
  subst hX
  cases hseam
  cases hPr
  cases hCh
  cases hsel
  subst hSS
  cases htup
  cases hcst
  cases hidx
  subst hm2
  cases hglob
  cases hword
  have hA : ambOf (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) Bb χ cD = I.J.amb B χ := eq_of_heq hamb
  have hm := hOk.hm
  have hpi : ∀ (u : B.Word) (a : I.ι) (w : rowSG (B.primes X) I.sel (I.tup a)), (B.primes X).piT u ∉ w.1.asIdeal := fun u a =>
    (TopStep.tilOk_of_avoid l.pr hOk.sel_ok u ⟨hOk.T_mem u, hOk.g_mem⟩).2.1
  refine ⟨⟨cc, cc_rec, cc_ok, δ, δ_ok, Bb, χ, χ_ok, idl, idl_ok, χ_rec, cD, _, _, seam_ok, _, pr_ok, g_rec, _, _, _, _, T_rec, _, Q_rec, _, _, _, _, glob_σ, glob_xi, idx_ok, O, I.kerRd l Z, fun u a => topChain _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (FieldsLaws.fields_ok B) l.pr (hOk.idx_ok a).cst_ok hm (hpi u a) (I.kerRd_top l Z hm u a), O_dgen, O_S, ?_, ?_, unf, ent, ent_lam, kf, kf_un, served⟩, ?_, ?_, ?_, ?_⟩
  · exact fun u a i c => (hO.lat u a i c).trans (seamOf_lat B (I.cols l) Z.W Z.V Z.S Z.N Z.G _).symm
  · intro u a i c c'
    rw [hA, AmbIn.amb_eq_ambOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G I.J χ, χ_rec]
    exact (hO.Th u a i c c').trans (I.kerRd_Th l Z hOk idl_ok hO u a i c c').symm
  · exact ⟨rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, rfl, HEq.rfl, heq_of_eq hA, hδ, hO⟩
  · exact fun u a => ⟨I.kerRd l Z u a, HEq.rfl, fun _ _ => rfl, fun _ _ _ _ _ => rfl⟩
  · exact fun u a => I.kerRd_top l Z hm u a
  · exact fun u a i c => Iff.rfl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelRelationTrueColumnsJointsAllTuples
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.TwV
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Pdv.oneTie_jointsAt_all : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (l0 : I.Law0 l) (Z : TC.Later B (I.cols l)) (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex) (C : ColsTiedSym (I.rec7 l Z)) (full : ColsFullS C) (g : Formalism.L2.G.GroupCompatibilityAll (I.rec7 l Z) hT ex.cmp) (nch : NChoice (I.rec7 l Z)) (tp : Formalism.L2.Host.TupTied (I.rec7 l Z) (I.cf l Z) nch), tp.xi = I.xi → I.IsTw → ColIn.JetsIn I → ex.tw = I.tw l l0 Z → ex.errX.piT = X.piT → I.StdKer l Z t → I.StdC l Z C → (∀ u, I.StdLvC l Z u (C.forms u)) → I.StdDt l Z full.1.base.dt → g.herm = full.1.to0 → (g.forms = fun u => (C.forms u).to0) → (∀ z : (I.rec7 l Z).Dt, ∃ r : (I.rec7 l Z).what₂.LL, (I.rec7 l Z).what₂.embLL r = (((I.rec7 l Z).chiD z : ℂˣ) : ℂ)) → G.LatTied hT Gi Gl → (∃ t' : KerEntTied ex, ∀ μ, JointsAt t' μ) ∧ ∀ u, ex.tw.e0 u (I.rec7 l Z).what₂.mu0 = ex.tw.eMu0 u 0 (Nat.zero_le _) := by
  intro B X I hOk hP l l0 Z L hT Gi Gl K Y cX ex t C full g nch tp _htp hTw hJ htw hpi hS hC _hLv hDt hg hgf hD hLat
  obtain ⟨t', hS', hR', _, hM'⟩ := GlobalTheory.Pdv.stdKer_stdRd_mark I hOk hP l Z L hT Gi Gl K Y cX ex t hS
  obtain ⟨h1, h2⟩ := GlobalTheory.T.trueColumn_joints_hold_all_tuples I hOk hP l Z l0 L hT Gi Gl K Y cX ex t' C full g hTw hJ htw hpi hS' hR' hM' hC hDt hg hgf hD hLat
  exact ⟨⟨t', h1⟩, h2⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelRelationTrueColumnsJointsAllTuplesStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.TwV
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_relation_true_columns_joints_all_tuples : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (l0 : I.Law0 l) (Z : TC.Later B (I.cols l)) (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex) (C : ColsTiedSym (I.rec7 l Z)) (full : ColsFullS C) (g : Formalism.L2.G.GroupCompatibilityAll (I.rec7 l Z) hT ex.cmp) (nch : NChoice (I.rec7 l Z)) (tp : Formalism.L2.Host.TupTied (I.rec7 l Z) (I.cf l Z) nch), tp.xi = I.xi → I.IsTw → ColIn.JetsIn I → ex.tw = I.tw l l0 Z → ex.errX.piT = X.piT → I.StdKer l Z t → I.StdC l Z C → (∀ u, I.StdLvC l Z u (C.forms u)) → I.StdDt l Z full.1.base.dt → g.herm = full.1.to0 → (g.forms = fun u => (C.forms u).to0) → (∀ z : (I.rec7 l Z).Dt, ∃ r : (I.rec7 l Z).what₂.LL, (I.rec7 l Z).what₂.embLL r = (((I.rec7 l Z).chiD z : ℂˣ) : ℂ)) → G.LatTied hT Gi Gl → (∃ t' : KerEntTied ex, ∀ μ, JointsAt t' μ) ∧ ∀ u, ex.tw.e0 u (I.rec7 l Z).what₂.mu0 = ex.tw.eMu0 u 0 (Nat.zero_le _) := by
  first | exact @GlobalTheory.Pdv.oneTie_jointsAt_all | exact GlobalTheory.Pdv.oneTie_jointsAt_all | (intros; apply GlobalTheory.Pdv.oneTie_jointsAt_all <;> assumption)
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain

set_option maxHeartbeats 1000000

theorem GlobalTheory.Svd.jointsAt_all_std : ∀ (B : GlobalTheory.Mem.Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (O : Obj (w.D Z)), Part w Z (ofObj O) → G.LatTied O.gatT O.Gx O.Gy → (∃ t : KerEntTied O.ex, ∀ μ, GlobalTheory.TwV.JointsAt t μ) ∧ ∀ u, O.ex.tw.e0 u (w.D Z).what₂.mu0 = O.ex.tw.eMu0 u 0 (Nat.zero_le _) := by
  intro B f T w Z O P hL
  obtain ⟨htw, -, hpiT, -, t, hstd, -, -⟩ := GlobalTheory.Svd.Part.kerTie B f T w Z O P
  have hchi := (GlobalTheory.Mem.ChiDVal.chiD_values_and_cc_top B f T w Z).1
  obtain ⟨L, gatT, Gx, Gy, K, X, cX, ex⟩ := O
  obtain ⟨pin, col, errX, tp, xi, qp, ker0, ker_eq, ker⟩ := P
  simp only [ofObj, extraObj] at ker_eq
  have h1 := congrArg Sigma.fst ker_eq
  simp only at h1
  subst h1
  have h2 := eq_of_heq (Sigma.mk.inj ker_eq).2
  have h3 := congrArg Sigma.fst h2
  simp only at h3
  obtain ⟨lev, th, th_io, cmp, lat, tw, exker⟩ := ex
  simp only at h3
  subst h3
  exact GlobalTheory.T.kernel_relation_true_columns_joints_all_tuples w.I w.ok w.pins w.l w.l0 Z L col.Gt Gx Gy K X cX _ t col.C col.full col.g _ tp xi
    pin.isTw pin.jets htw hpiT hstd col.std col.stdLv col.stdDt col.herm_eq col.forms_eq hchi hL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TuplesHaveLocalModelsOfStandardColumnObjects
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain

namespace GlobalTheory.Svd

theorem modelsAt_of_part : GlobalTheory.TwV.Lt.AdmAtEnt2 → GlobalTheory.TwV.Lt.CurveEx → ∀ (B : GlobalTheory.Mem.Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (O : Obj (w.D Z)), Part w Z (ofObj O) → ModelsAt (w.D Z) O := by
  intro hA hC B f T w Z O hP hL hk
  obtain ⟨⟨t, hJ⟩, he⟩ := GlobalTheory.Svd.jointsAt_all_std B f T w Z O hP hL
  have hS : OrbitPlaces.Stab0 (w.D Z) := GlobalTheory.Pdv.stepZero_trivial_stabilisers_trueColumns w.I w.ok w.pins w.l Z O.ex.lev
  exact GlobalTheory.T.thetaLocalModels_of_splitUnramified_joints hA hC t (fun μ _ => hJ μ) he hS hk

end GlobalTheory.Svd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TuplesHaveLocalModelsOfStandardColumnObjectsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tuplesHaveLocalModels_of_standardColumnObjects : GlobalTheory.TwV.Lt.AdmAtEnt2 → GlobalTheory.TwV.Lt.CurveEx → ∀ (B : GlobalTheory.Mem.Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (O : Obj (w.D Z)), GlobalTheory.Svd.Part w Z (ofObj O) → ModelsAt (w.D Z) O := by
  first | exact @GlobalTheory.Svd.modelsAt_of_part | exact GlobalTheory.Svd.modelsAt_of_part | (intros; apply GlobalTheory.Svd.modelsAt_of_part <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TuplesLocalModelsOfOtherDivisionLatticesHeights
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeChainComparisonIndepDivisionLattices
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeChainComparisonIndepDivisionLattices
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain

namespace GlobalTheory.Svd


set_option maxHeartbeats 1000000 in
theorem cmpLite_setDiv : ∀ (D : D7) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ) (c : LatCmp D) (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (Fl : G.Fills (D.gat u w hg)) (Lv : G.Levels Fl) (Ch : G.Chain Lv), GlobalTheory.TwU.CmpLite D c Tw u μ w hg Ch → GlobalTheory.TwU.CmpLite (setDiv D N h) (cmpTr N h c) (twTr N h Tw) u μ w hg Ch := by
  intro D N h c Tw u μ w hg Fl Lv Ch H
  exact H

end GlobalTheory.Svd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeChainComparisonIndepDivisionLatticesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeChainComparison_indep_divisionLattices : ∀ (D : D7) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ) (c : LatCmp D) (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (Fl : G.Fills (D.gat u w hg)) (Lv : G.Levels Fl) (Ch : G.Chain Lv), GlobalTheory.TwU.CmpLite D c Tw u μ w hg Ch → GlobalTheory.TwU.CmpLite (setDiv D N h) (cmpTr N h c) (twTr N h Tw) u μ w hg Ch := by
  first | exact @GlobalTheory.Svd.cmpLite_setDiv | exact GlobalTheory.Svd.cmpLite_setDiv | (intros; apply GlobalTheory.Svd.cmpLite_setDiv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteAdmissibleIndepDivisionLattices
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteAdmissibleIndepDivisionLattices
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain

theorem GlobalTheory.TwU.siteAdm_setDiv : ∀ (D : D7) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (Fl : G.Fills (D.gat u w hg)) (Lv : G.Levels Fl) (Ch : G.Chain Lv), GlobalTheory.TwU.SiteAdm D u w hg Fl Lv Ch → GlobalTheory.TwU.SiteAdm (setDiv D N h) u w hg Fl Lv Ch := by
  intro D N h u w hg Fl Lv Ch H
  exact H
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteAdmissibleIndepDivisionLatticesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siteAdmissible_indep_divisionLattices : ∀ (D : D7) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (Fl : G.Fills (D.gat u w hg)) (Lv : G.Levels Fl) (Ch : G.Chain Lv), GlobalTheory.TwU.SiteAdm D u w hg Fl Lv Ch → GlobalTheory.TwU.SiteAdm (setDiv D N h) u w hg Fl Lv Ch := by
  first | exact @GlobalTheory.TwU.siteAdm_setDiv | exact GlobalTheory.TwU.siteAdm_setDiv | (intros; apply GlobalTheory.TwU.siteAdm_setDiv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TuplesLocalModelsOfOtherDivisionLatticesHeights
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain

namespace GlobalTheory.Svd


set_option maxHeartbeats 800000 in
theorem modelsAt_tr : ∀ (D : D7) (O : Obj D) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ),
    ModelsAt D O → ModelsAt (setDiv D N h) (O.tr N h) := by
  intro D O N h H hT hk
  obtain ⟨h0, LC, hLC⟩ := H hT hk
  refine ⟨h0, LC, fun μ hμ u w hg hq => ?_⟩
  obtain ⟨c1, c2⟩ := hLC μ hμ u w hg hq
  exact ⟨GlobalTheory.T.latticeChainComparison_indep_divisionLattices D N h _ _ u μ w hg _ _ _ c1, GlobalTheory.T.siteAdmissible_indep_divisionLattices D N h u w hg _ _ _ c2⟩

end GlobalTheory.Svd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TuplesLocalModelsOfOtherDivisionLatticesHeightsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tuplesLocalModels_of_otherDivisionLatticesHeights : ∀ (D : D7) (O : Obj D) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ), ModelsAt D O → ModelsAt (setDiv D N h) (O.tr N h) := by
  first | exact @GlobalTheory.Svd.modelsAt_tr | exact GlobalTheory.Svd.modelsAt_tr | (intros; apply GlobalTheory.Svd.modelsAt_tr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TuplesHaveLocalModelsAtConstructedPointOverTrueC
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain

namespace GlobalTheory.Svd

theorem modelsAt_bpt : GlobalTheory.TwV.Lt.AdmAtEnt2 → GlobalTheory.TwV.Lt.CurveEx → ∀ (K : Ctx) (β : BPt K), β.Is (positionOf HasPart) → ModelsAt β.D β.O := by
  intro h1 h2 K β hβ
  have key : ∀ O : Obj β.X.toD7, ofObj O = β.c.O → ModelsAt β.X.toD7 O := by
    refine positionOf_ind (P := HasPart) (R := fun K X f T c => ∀ O : Obj X.toD7, ofObj O = c.O → ModelsAt X.toD7 O) ?_ hβ
    intro K B f T w Z c hc O hO
    obtain ⟨b⟩ := hc
    have b' : Part w Z (ofObj O) := hO ▸ b
    exact GlobalTheory.T.tuplesHaveLocalModels_of_standardColumnObjects h1 h2 B f T w Z O b'
  have hm := key (β.Y.obj β.p) (by rw [ofObj_obj]; exact β.hY)
  exact GlobalTheory.T.tuplesLocalModels_of_otherDivisionLatticesHeights β.X.toD7 (β.Y.obj β.p) (nPrime β.p.L) β.p.ht hm

end GlobalTheory.Svd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TuplesHaveLocalModelsAtConstructedPointOverTrueCStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tuplesHaveLocalModels_at_constructedPoint_over_trueColumns : GlobalTheory.TwV.Lt.AdmAtEnt2 → GlobalTheory.TwV.Lt.CurveEx → ∀ (K : Ctx) (β : BPt K), β.Is (positionOf HasPart) → ModelsAt β.D β.O := by
  first | exact @GlobalTheory.Svd.modelsAt_bpt | exact GlobalTheory.Svd.modelsAt_bpt | (intros; apply GlobalTheory.Svd.modelsAt_bpt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowTwUHolds
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryWeightModels
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalSystemsLowerBoundsSecondRealPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LowTermLeSecondRealPlaceBounds
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LowTermLeSecondRealPlaceBounds
noncomputable section

namespace GlobalTheory.TwU.LowTerm

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

variable {D : D7} {L : SizeData₂ D}

theorem sum_betaI (X : Inst D L) (K : Consts) (ce : ErrC) (j p : ℕ) (hs : ¬ IsSg D p) :
    ∑ r ∈ OrbitPlaces.repsPl X p, OrbitPlaces.betaI X K ce j p r =
      (∑ t ∈ reps X p, max (g0 X K (aL L) (bL L) p j t) 0) +
        ∑ t ∈ reps X p, (FOrb D j p (true, t) - OrbitPlaces.errF L K ce j p (true, t)) := by
  have hd : Disjoint ((reps X p).image (fun t => ((false, t) : OrbitPlaces.Pl D)))
      ((reps X p).image (fun t => ((true, t) : OrbitPlaces.Pl D))) := by
    rw [Finset.disjoint_left]
    intro r h1 h2
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 h1
    obtain ⟨t', -, h⟩ := Finset.mem_image.1 h2
    simp at h
  unfold OrbitPlaces.repsPl
  rw [if_neg hs, Finset.sum_union hd, Finset.sum_image (fun a _ b _ h => by simpa using h),
    Finset.sum_image (fun a _ b _ h => by simpa using h)]
  congr 1
  · refine Finset.sum_congr rfl fun t _ => ?_
    simp [OrbitPlaces.betaI, OrbitPlaces.g0Pl, kindA, hs]
  · refine Finset.sum_congr rfl fun t _ => ?_
    simp [OrbitPlaces.betaI, OrbitPlaces.g0Pl, kindA]

theorem FInert_sub_EatI (X : Inst D L) (K : Consts) (ce : ErrC) {p j : ℕ} (hp : p.Prime) (hc : IsResidueClassZero D p)
    (hh : HEv D p) (hs : ¬ IsSg D p) (hj : j ∈ SizeData₂.lifts D) :
    FInert D j p - EatI L K ce j p ≤
      ∑ t ∈ reps X p, (FOrb D j p (true, t) - OrbitPlaces.errF L K ce j p (true, t)) := by
  have h := OrbitPlaces.sumI X K ce p hp (Or.inl ⟨hc, hh⟩) j hj
  rw [sum_betaI X K ce j p hs] at h
  linarith

theorem sum_dG_le {m n : ℕ} (hm : 1 ≤ m) {d : ℕ → ℕ} (h0 : d 0 = 0) (hj : ∀ j, d j ≤ n) :
    ∑ j ∈ Finset.range m, (d j : ℝ) ≤ ((m : ℝ) - 1) * n := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [Finset.sum_range_succ', h0]
  have : ∑ j ∈ Finset.range k, (d (j + 1) : ℝ) ≤ ∑ _j ∈ Finset.range k, (n : ℝ) :=
    Finset.sum_le_sum fun j _ => by exact_mod_cast hj _
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
  push_cast
  linarith

theorem lowS_le : ∀ (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (L : SizeData₂ D) (X : Inst D L) (K : Consts) (ce : ErrC)
    (Xe : ErrX D) (dG : ℕ → ℕ), L.FDef → dG 0 = 0 →
    (∀ j, dG j ≤ padicValNat (D.what₂.places.resChar w) (D.mem u).C.DGam) →
    WeilJacquetShalikaLaw.lowS L Xe K ce 1 u w ≤ (∑ j ∈ Finset.Icc 1 D.R.m, ∑ t ∈ reps X (D.what₂.places.resChar w),
      if ((D.what₂.places.resChar w) : ℝ) ≤ L.sc.X'' D.R.n then
        FOrb D j (D.what₂.places.resChar w) (true, t) - OrbitPlaces.errF L K ce j (D.what₂.places.resChar w) (true, t) else 0) -
      ∑ j ∈ Finset.range D.R.m, (dG j : ℝ) := by
  intro D u w hg L X K ce Xe dG hF h0 hd
  have hm : 1 ≤ D.R.m := le_trans one_le_two D.R.two_le_m
  have hloss := sum_dG_le hm h0 hd
  have hc : IsResidueClassZero D (D.what₂.places.resChar w) := hg.2.2.1
  have hs : ¬ IsSg D (D.what₂.places.resChar w) := by
    intro h
    have h' : D.host.cls (D.what₂.places.resChar w) = _ := h
    rw [hg.2.2.1] at h'
    exact absurd h' (by decide)
  have hev : HEv D (D.what₂.places.resChar w) := hEv_of_hNeZero hg.1 hg.2.2.2.1
  have hh := hev.ne_zero
  have hne : ∀ i : Fin 2, D.what₂.places.resChar w ≠ D.host.g i := fun i h => hg.2.2.2.2.1 (h ▸ D.host.g_level i)
  have h2 : D.host.cls (D.what₂.places.resChar w) ≠ PrimeClass.ramD := by rw [hg.2.2.1]; decide
  have h4 : D.what₂.places.resChar w ∉ L.gTypes := by simp [SizeData₂.gTypes, hne]
  have hcard : ((SizeData₂.lifts D).card : ℝ) = D.R.m := by simp [SizeData₂.lifts]
  have hterm : ∀ j ∈ SizeData₂.lifts D, L.F j w - WeilJacquetShalikaLaw.ES L Xe K ce u j w =
      (if (D.what₂.places.resChar w : ℝ) ≤ L.sc.X'' D.R.n then
        FInert D j (D.what₂.places.resChar w) - EatI L K ce j (D.what₂.places.resChar w) else 0) - WeilJacquetShalikaLaw.vDG D u w := by
    intro j hj
    rw [hF j hj w]
    unfold Fval FvalP WeilJacquetShalikaLaw.ES Eval WeilJacquetShalikaLaw.vDG
    simp only [if_neg (hne 0), if_neg (hne 1), if_neg (WeilJacquetShalikaLaw.residue_char_ne_level hg), if_neg h2, if_neg h4]
    by_cases hX : (D.what₂.places.resChar w : ℝ) ≤ L.sc.X'' D.R.n
    · have hA : (IsResidueClassZero D (D.what₂.places.resChar w) ∨ IsSg D (D.what₂.places.resChar w)) ∧
          (D.what₂.places.resChar w : ℝ) ≤ L.sc.X'' D.R.n := ⟨Or.inl hc, hX⟩
      have hB : ¬ (IsResidueClassZero D (D.what₂.places.resChar w) ∧ hP D (D.what₂.places.resChar w) = 0) := fun h => hh h.2
      simp only [if_pos hA, if_neg hB, if_pos hX]
      unfold FInert
      rw [if_neg hB]
      ring
    · have hA : ¬ ((IsResidueClassZero D (D.what₂.places.resChar w) ∨ IsSg D (D.what₂.places.resChar w)) ∧
          (D.what₂.places.resChar w : ℝ) ≤ L.sc.X'' D.R.n) := fun h => hX h.2
      simp only [if_neg hA, if_neg hX]
      ring
  have hsum : WeilJacquetShalikaLaw.lowS L Xe K ce 1 u w = (∑ j ∈ Finset.Icc 1 D.R.m,
      if (D.what₂.places.resChar w : ℝ) ≤ L.sc.X'' D.R.n then
        FInert D j (D.what₂.places.resChar w) - EatI L K ce j (D.what₂.places.resChar w) else 0) -
      ((D.R.m : ℝ) - 1) * WeilJacquetShalikaLaw.vDG D u w := by
    unfold WeilJacquetShalikaLaw.lowS
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hcard]
    have hl : SizeData₂.lifts D = Finset.Icc 1 D.R.m := rfl
    rw [hl]
    ring
  have hle : (∑ j ∈ Finset.Icc 1 D.R.m,
      if (D.what₂.places.resChar w : ℝ) ≤ L.sc.X'' D.R.n then
        FInert D j (D.what₂.places.resChar w) - EatI L K ce j (D.what₂.places.resChar w) else 0) ≤
      ∑ j ∈ Finset.Icc 1 D.R.m, ∑ t ∈ reps X (D.what₂.places.resChar w),
        if (D.what₂.places.resChar w : ℝ) ≤ L.sc.X'' D.R.n then
          FOrb D j (D.what₂.places.resChar w) (true, t) - OrbitPlaces.errF L K ce j (D.what₂.places.resChar w) (true, t) else 0 := by
    refine Finset.sum_le_sum fun j hj => ?_
    by_cases hX : (D.what₂.places.resChar w : ℝ) ≤ L.sc.X'' D.R.n
    · simp only [if_pos hX]
      exact FInert_sub_EatI X K ce hg.1 hc hev hs hj
    · simp [hX]
  have hv : ((D.R.m : ℝ) - 1) * (padicValNat (D.what₂.places.resChar w) (D.mem u).C.DGam : ℝ) =
      ((D.R.m : ℝ) - 1) * WeilJacquetShalikaLaw.vDG D u w := rfl
  rw [hsum]
  linarith

end GlobalTheory.TwU.LowTerm

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LowTermLeSecondRealPlaceBoundsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.low_term_le_second_real_place_bounds : ∀ (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (L : SizeData₂ D) (X : Inst D L) (K : Consts) (ce : ErrC) (Xe : ErrX D) (dG : ℕ → ℕ), L.FDef → dG 0 = 0 → (∀ j, dG j ≤ padicValNat (D.what₂.places.resChar w) (D.mem u).C.DGam) → WeilJacquetShalikaLaw.lowS L Xe K ce 1 u w ≤ (∑ j ∈ Finset.Icc 1 D.R.m, ∑ t ∈ reps X (D.what₂.places.resChar w), if ((D.what₂.places.resChar w) : ℝ) ≤ L.sc.X'' D.R.n then FOrb D j (D.what₂.places.resChar w) (true, t) - OrbitPlaces.errF L K ce j (D.what₂.places.resChar w) (true, t) else 0) - ∑ j ∈ Finset.range D.R.m, (dG j : ℝ) := by
  first | exact @GlobalTheory.TwU.LowTerm.lowS_le | exact GlobalTheory.TwU.LowTerm.lowS_le | (intros; apply GlobalTheory.TwU.LowTerm.lowS_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlacesOffFirstOrbits
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

namespace GlobalTheory.SecondOrbits

section Abstract

variable {V H : Type} [AddCommGroup H] [Finite H] {h : H} {bs : H → H}

omit [Finite H] in
theorem inv_nsmul {Z : Type} {f : H → Z} (hf : ∀ t, f (t + h) = f t) (t : H) (i : ℕ) : f (t + i • h) = f t := by
  induction i with
  | zero => simp
  | succ i ih => rw [succ_nsmul, ← add_assoc, hf, ih]

theorem exists_back (a : H) (i : ℕ) : ∃ k, k < addOrderOf h ∧ a + i • h + k • h = a := by
  have hpos : 0 < addOrderOf h := addOrderOf_pos h
  refine ⟨(i * (addOrderOf h - 1)) % addOrderOf h, Nat.mod_lt _ hpos, ?_⟩
  rw [mod_addOrderOf_nsmul, add_assoc, ← add_nsmul]
  have : i + i * (addOrderOf h - 1) = i * addOrderOf h := by
    obtain ⟨m, hm⟩ : ∃ m, addOrderOf h = m + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
    rw [hm, Nat.add_sub_cancel]; ring
  rw [this, mul_comm, mul_nsmul, addOrderOf_nsmul_eq_zero, nsmul_zero, add_zero]

theorem second_orbits [Fintype V] [Fintype H] [DecidableEq V] [DecidableEq H] (n' : V → ℕ) (hn : ∀ v, n' v = addOrderOf h)
    (π : (Σ v, Fin (n' v)) ≃ Bool × H) (β : V → Bool) (r : V → H)
    (hπ : ∀ v s, π ⟨v, s⟩ = (β v, r v + s.val • h))
    (horb : ∀ t, ∃ i : ℕ, bs t + i • h = t) (hstep : ∀ t, bs (t + h) = bs t) (vOf : H → V)
    (hv : ∀ t0 ∈ Finset.univ.image bs, ∀ s, π ⟨vOf t0, s⟩ = (false, t0 + s.val • h)) :
    (∀ v, v ∉ (Finset.univ.image bs).image vOf → β v = true) ∧
      ∀ f : H → ℝ, (∀ t, f (t + h) = f t) →
        ∑ v ∈ Finset.univ \ (Finset.univ.image bs).image vOf, f (r v) = ∑ t ∈ Finset.univ.image bs, f t := by
  have hpos : 0 < addOrderOf h := addOrderOf_pos h
  have reach : ∀ v, ∃ s, π ⟨v, s⟩ = (β v, bs (r v)) := fun v => by
    obtain ⟨i, hi⟩ := horb (r v)
    obtain ⟨k, hk, hk'⟩ := exists_back (h := h) (bs (r v)) i
    refine ⟨⟨k, by rw [hn]; exact hk⟩, ?_⟩
    rw [hπ]
    rw [hi] at hk'
    simp only [hk']
  have h1 : ∀ v, v ∉ (Finset.univ.image bs).image vOf → β v = true := fun v hvn => by
    by_contra hb
    have hb' : β v = false := by simpa using hb
    obtain ⟨s, hs⟩ := reach v
    have hm : bs (r v) ∈ Finset.univ.image bs := Finset.mem_image_of_mem _ (Finset.mem_univ _)
    have h0 := hv _ hm ⟨0, by rw [hn]; exact hpos⟩
    simp only [zero_smul, add_zero] at h0
    rw [hb', ← h0] at hs
    have := congrArg Sigma.fst (π.injective hs)
    exact hvn (Finset.mem_image.2 ⟨_, hm, this.symm⟩)
  refine ⟨h1, fun f hf => ?_⟩
  refine Finset.sum_bij (fun v _ => bs (r v)) (fun v _ => Finset.mem_image_of_mem _ (Finset.mem_univ _)) ?_ ?_ ?_
  · intro v hv1 v' hv2 he
    obtain ⟨s, hs⟩ := reach v
    obtain ⟨s', hs'⟩ := reach v'
    rw [h1 v (Finset.mem_sdiff.1 hv1).2] at hs
    rw [h1 v' (Finset.mem_sdiff.1 hv2).2] at hs'
    have he' : bs (r v) = bs (r v') := he
    rw [he', ← hs'] at hs
    exact congrArg Sigma.fst (π.injective hs)
  · intro t0 ht0
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 ht0
    obtain ⟨⟨v, s⟩, hvs⟩ := π.surjective (true, bs t)
    refine ⟨v, Finset.mem_sdiff.2 ⟨Finset.mem_univ _, fun hm => ?_⟩, ?_⟩
    · obtain ⟨t1, ht1, rfl⟩ := Finset.mem_image.1 hm
      rw [hv t1 ht1] at hvs
      cases congrArg Prod.fst hvs
    · rw [hπ] at hvs
      have e1 : r v + s.val • h = bs t := congrArg Prod.snd hvs
      obtain ⟨i, hi⟩ := horb t
      show bs (r v) = bs t
      rw [← inv_nsmul hstep (r v) s.val, e1, ← inv_nsmul hstep (bs t) i, hi]
  · intro v _
    obtain ⟨i, hi⟩ := horb (r v)
    rw [← inv_nsmul hf (bs (r v)) i, hi]

end Abstract

open NumberField GlobalTheory.InertCompare

theorem orderOf_iotaH (φ : Formalism.HC.Frame) (t : φ.A) : orderOf (φ.iota t) = addOrderOf t :=
  orderOf_ofAdd_eq_addOrderOf t

theorem eTau_tauPl (D : D7) (z : Bool × HH D) : ((D.eTau (tauPl D z) : D.R.Psi) : D.R.GG) = plGG D z := by
  unfold tauPl
  rw [Equiv.apply_symm_apply]

theorem eq_tauPl (D : D7) {τ : D.what₂.Tau} {z : Bool × HH D} (h : ((D.eTau τ : D.R.Psi) : D.R.GG) = plGG D z) :
    τ = tauPl D z :=
  D.eTau.injective (Subtype.ext (h.trans (eTau_tauPl D z).symm))

theorem orbit_positions (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (hT : GatTies D) (v : Fin (D.gat u w hg).P.nV) :
    (D.gat u w hg).P.n' v = addOrderOf (hP D (D.what₂.places.resChar w)) ∧
      ∃ z : Bool × HH D, ∀ s : Fin ((D.gat u w hg).P.n' v),
        hT.gat_pos u w hg ⟨v, s⟩ = tauPl D (posPl D (D.what₂.places.resChar w) z s.val) := by
  have : Fact (D.what₂.places.resChar w).Prime := ⟨hg.1⟩
  have hc : IsResidueClassZero D (D.what₂.places.resChar w) ∨ IsSg D (D.what₂.places.resChar w) := Or.inl hg.2.2.1
  have : (Ideal.span {((D.what₂.places.resChar w : ℕ) : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hg.1.ne_zero)).2 (Nat.prime_iff_prime_int.1 hg.1)
  obtain ⟨⟨P, hP1, hP2⟩⟩ := (Ideal.span {((D.what₂.places.resChar w : ℕ) : ℤ)}).nonempty_primesOver (S := 𝓞 D.host.E)
  obtain ⟨φ, hφ, hstep⟩ := exists_frob_step D _ hc P
  obtain ⟨h2, hq, hd⟩ := ne_of_inert D _ hc
  have hn : (D.gat u w hg).P.n' v = addOrderOf (hP D (D.what₂.places.resChar w)) := by
    rw [hT.gat_n u w hg v P φ hφ, galE_frob_snd D _ h2 hq hd P φ hφ, orderOf_iotaH]
  have hpos : 0 < (D.gat u w hg).P.n' v := by rw [hn]; exact addOrderOf_pos _
  obtain ⟨z, hz⟩ := (tauPl_bijective D).2 (hT.gat_pos u w hg ⟨v, ⟨0, hpos⟩⟩)
  refine ⟨hn, z, ?_⟩
  rintro ⟨s, hs⟩
  induction s with
  | zero => rw [posPl_zero, hz]
  | succ s ih =>
    have hs' : s < (D.gat u w hg).P.n' v := Nat.lt_of_succ_lt hs
    have e1 : (⟨s + 1, hs⟩ : Fin ((D.gat u w hg).P.n' v)) = posAdd ⟨s, hs'⟩ 1 := Fin.ext (Nat.mod_eq_of_lt hs).symm
    refine eq_tauPl D ?_
    show _ = plGG D (posPl D _ z (s + 1))
    rw [e1, hT.gat_step u w hg v ⟨s, hs'⟩ P φ hφ, ih hs', eTau_tauPl, ← posPl_add, hstep]

theorem places_off_first_orbits : ∀ (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (L : SizeData₂ D) (hT : GatTies D) (X : Inst D L) (Y : LatInst D), LatTied hT X Y → ∃ r : Fin (D.gat u w hg).P.nV → HH D, (∀ v, v ∉ (reps X (D.what₂.places.resChar w)).image (Y.vOf u w hg) → (D.gat u w hg).P.n' v = nP D (D.what₂.places.resChar w) ∧ (Y.Fl u w hg).TT v = ∅ ∧ ∀ s : Fin ((D.gat u w hg).P.n' v), hT.gat_pos u w hg ⟨v, s⟩ = tauPl D (posPl D (D.what₂.places.resChar w) (true, r v) s.val)) ∧ ∀ f : HH D → ℝ, (∀ t, f (t + hP D (D.what₂.places.resChar w)) = f t) → ∑ v ∈ Finset.univ \ (reps X (D.what₂.places.resChar w)).image (Y.vOf u w hg), f (r v) = ∑ t ∈ reps X (D.what₂.places.resChar w), f t := by
  intro D u w hg L hT X Y hL
  have hs : ¬ IsSg D (D.what₂.places.resChar w) := fun hs => by
    have := hg.2.2.1.symm.trans hs
    cases this
  have hstepP : stepP D (D.what₂.places.resChar w) = hP D (D.what₂.places.resChar w) := if_neg hs
  have hnP : nP D (D.what₂.places.resChar w) = addOrderOf (hP D (D.what₂.places.resChar w)) := if_neg hs
  have hpos : ∀ (z : Bool × HH D) (e : ℕ), posPl D (D.what₂.places.resChar w) z e =
      (z.1, z.2 + e • hP D (D.what₂.places.resChar w)) := fun z e => by
    simp [posPl, partner, hs]
  have hn := fun v => (orbit_positions D u w hg hT v).1
  choose z hz using fun v => (orbit_positions D u w hg hT v).2
  obtain ⟨-, -, -, -, -, hT2, hT1⟩ := hL u w hg
  have hreps : reps X (D.what₂.places.resChar w) = Finset.univ.image (X.bs (hP D (D.what₂.places.resChar w))) := by
    unfold reps
    rw [hstepP]
  have key := second_orbits (h := hP D (D.what₂.places.resChar w)) (bs := X.bs (hP D (D.what₂.places.resChar w)))
    (D.gat u w hg).P.n' hn ((hT.gat_pos u w hg).trans (plEquiv D).symm) (fun v => (z v).1) (fun v => (z v).2)
    (fun v s => by
      rw [Equiv.trans_apply, Equiv.symm_apply_eq, hz, hpos]
      rfl)
    (X.bs_orb _) (X.bs_step _) (Y.vOf u w hg)
    (fun t0 ht0 s => by
      rw [Equiv.trans_apply, Equiv.symm_apply_eq]
      exact eq_tauPl D ((hT1 t0 (hreps ▸ ht0)).2 s).1)
  rw [hreps]
  refine ⟨fun v => (z v).2, fun v hv => ?_, key.2⟩
  have hb : z v = (true, (z v).2) := Prod.ext (key.1 v hv) rfl
  refine ⟨(hn v).trans hnP.symm, ?_, fun s => by rw [hz, ← hb]⟩
  refine Finset.eq_empty_of_forall_notMem fun s => (hT2 v s ((z v).2 + s.val • hP D (D.what₂.places.resChar w)) ?_).1
  rw [hz, eTau_tauPl, hpos, hb]
  rfl

end GlobalTheory.SecondOrbits
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalSystemsLowerBoundsSecondRealPlace
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

namespace GlobalTheory.TwU.SiteSys

variable {D : D7}

theorem orbMap_posPl (p : ℕ) (r : OrbitPlaces.Pl D) (e : ℕ) (s : ZMod (nP D p)) :
    OrbitPlaces.orbMap D p (posPl D p r e) s = OrbitPlaces.orbMap D p r (s + (e : ZMod (nP D p))) := by
  unfold OrbitPlaces.orbMap
  rw [posPl_add, ZMod.val_add, ZMod.val_natCast, posPl_mod, ← posPl_add D p r s.val, posPl_mod, posPl_add, add_comm]

theorem topsOrb_posPl (p : ℕ) (r : OrbitPlaces.Pl D) (e : ℕ) :
    OrbitPlaces.topsOrb D p (posPl D p r e) = OrbitPlaces.topsOrb D p r := by
  unfold OrbitPlaces.topsOrb
  refine Finset.card_equiv (Equiv.addRight (e : ZMod (nP D p))) fun s => ?_
  simp [orbMap_posPl]

theorem errF_posPl {L : SizeData₂ D} (K : Consts) (ce : ErrC) (j p : ℕ) (r : OrbitPlaces.Pl D) (e : ℕ) :
    OrbitPlaces.errF L K ce j p (posPl D p r e) = OrbitPlaces.errF L K ce j p r := by
  have h : ∑ s : ZMod (nP D p), wPl D j (OrbitPlaces.orbMap D p (posPl D p r e) s) =
      ∑ s : ZMod (nP D p), wPl D j (OrbitPlaces.orbMap D p r s) := by
    simp only [orbMap_posPl]
    exact Equiv.sum_comp (Equiv.addRight (e : ZMod (nP D p))) (fun s => wPl D j (OrbitPlaces.orbMap D p r s))
  unfold OrbitPlaces.errF
  rw [h, topsOrb_posPl]

theorem posPl_true_one {p : ℕ} (hs : ¬ IsSg D p) (t : HH D) : posPl D p (true, t) 1 = (true, t + hP D p) := by
  simp [posPl, partner, hs]

theorem notSg {T p : ℕ} (hg : GIdx D.host T p) : ¬ IsSg D p := by
  intro h
  have h1 : D.host.cls p = PrimeClass.inertClass := hg.2.2.1
  unfold IsSg at h
  rw [h1] at h
  exact absurd h (by decide)

theorem sysTw_sites : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (X : Inst D L) (Y : LatInst D) (K : Consts) (Dx : DivX D) (lev : LevelData D) (Xe : ErrX D) (ce : ErrC) (E : OrbitPlaces.Ent D) (LC : D.what₂.Tup → ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)), Σ Lv : Levels (Y.Fl u w hg), Chain Lv), LatTied hT X Y → FillsAll hT Y → L.FDef → OrbitPlaces.OrbitLetterBoundsAll 11 1 → OrbitPlaces.Shape D L X E → OrbitPlaces.CLarge 11 1 K ce → (∀ μ, DV.Used D μ → ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)), D.what₂.places.resChar w ∉ Dx.Qp μ → SiteAdm D u w hg (Y.Fl u w hg) (LC μ u w hg).1 (LC μ u w hg).2) → SysTw D L X K Dx (reW Y LC) lev Xe ce 1 := by
  intro D L hT X Y K Dx lev Xe ce E LC hty hfa hF hadm hSh hCL hS hE μ hμ hT' hty' u w hg hQ
  obtain ⟨i, std, vp, unif, eO, eO_spec, dG, dG_spec, om, Y5, hA, h0, hj⟩ := hS μ hμ u w hg hQ
  obtain ⟨r, hr1, hr2⟩ := GlobalTheory.SecondOrbits.places_off_first_orbits D u w hg L hT X Y hty
  refine ⟨i, std, vp, unif, eO, eO_spec, dG, dG_spec, om, Y5, hA,
    fun v j => if ((D.what₂.places.resChar w : ℕ) : ℝ) ≤ L.sc.X'' D.R.n then
      FOrb D j (D.what₂.places.resChar w) (true, r v) - OrbitPlaces.errF L K ce j (D.what₂.places.resChar w) (true, r v) else 0,
    ?_, ?_⟩
  · intro v hv j hjm
    obtain ⟨-, -, -, a2c, -, -, -, -, -, -, -, -, a11⟩ := hA
    by_cases hp : ((D.what₂.places.resChar w : ℕ) : ℝ) ≤ L.sc.X'' D.R.n
    · simp only [if_pos hp]
      exact GlobalTheory.T.local_model_bound_place_over_second_embedding D u w hg L hT X Y K ce E hty hfa hadm hSh hCL hp _ _ std vp unif eO eO_spec dG dG_spec om Y5 a2c v (r v)
        (hr1 v hv).1 (hr1 v hv).2.2 j hjm
    · simp only [if_neg hp]
      exact a11 v j (lt_of_lt_of_eq hjm (hty u w hg).1.symm)
  · refine (GlobalTheory.T.low_term_le_second_real_place_bounds D u w hg L X K ce Xe dG hF h0 hj).trans (sub_le_sub_right (le_of_eq ?_) _)
    refine Finset.sum_congr rfl fun j _ => ?_
    refine (hr2 (fun t => if ((D.what₂.places.resChar w : ℕ) : ℝ) ≤ L.sc.X'' D.R.n then
      FOrb D j (D.what₂.places.resChar w) (true, t) - OrbitPlaces.errF L K ce j (D.what₂.places.resChar w) (true, t) else 0) ?_).symm
    intro t
    have h1 := posPl_true_one (notSg hg) t
    have h2 := FOrb_step D j (D.what₂.places.resChar w) (true, t) 1
    have h3 := errF_posPl (L := L) K ce j (D.what₂.places.resChar w) (true, t) 1
    rw [h1] at h2 h3
    simp only [h2, h3]

end GlobalTheory.TwU.SiteSys
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalSystemsLowerBoundsSecondRealPlaceStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_systems_lower_bounds_second_real_place : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (X : Inst D L) (Y : LatInst D) (K : Consts) (Dx : DivX D) (lev : LevelData D) (Xe : ErrX D) (ce : ErrC) (E : OrbitPlaces.Ent D) (LC : D.what₂.Tup → ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)), Σ Lv : Levels (Y.Fl u w hg), Chain Lv), LatTied hT X Y → FillsAll hT Y → L.FDef → OrbitPlaces.OrbitLetterBoundsAll 11 1 → OrbitPlaces.Shape D L X E → OrbitPlaces.CLarge 11 1 K ce → (∀ μ, DV.Used D μ → ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)), D.what₂.places.resChar w ∉ Dx.Qp μ → SiteAdm D u w hg (Y.Fl u w hg) (LC μ u w hg).1 (LC μ u w hg).2) → SysTw D L X K Dx (reW Y LC) lev Xe ce 1 := by
  first | exact @GlobalTheory.TwU.SiteSys.sysTw_sites | exact GlobalTheory.TwU.SiteSys.sysTw_sites | (intros; apply GlobalTheory.TwU.SiteSys.sysTw_sites <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColumnWeightComparison
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeValuationBound
noncomputable section

open scoped BigOperators
open NumberField IsDedekindDomain Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.G Formalism.MainNotions.WeilJacquetShalikaLaw

namespace GlobalTheory.Proof.LatticeValuationBound

section Chain

variable {R : Ranks} {LL : Type} [Field LL] [NumberField LL] [StarRing LL] {embLL : LL →+* ℂ}
  {Pl : Rows.Places LL} {Tau : Type} [Fintype Tau] {hc : Tau → HCParam R}
  {C : ColumnChain R Tau hc} {A : ColumnsAtT R C} {P : PeriodMap R C}

theorem exists_chain (M : MemberForms LL embLL Pl Tau hc C A P) {p : ℕ} {G : GAtP p} {Fl : Fills G} {Lv : Levels Fl}
    (Ch : Chain Lv) (σ : LL →+* G.Kf) (cmp : ∀ j, (M.lat j).V →ₛₗ[σ] Lv.Fm j)
    (hK : ∀ j, j < R.m → ∀ (x : (M.lat j).V) (y : (M.lat (j + 1)).V),
      M.emb (j + 1) y = C.K j (M.emb j x) → cmp (j + 1) y = Ch.Kz j (cmp j x))
    (hrat : ∀ j, j < R.m → M.KRat j) (x : (M.lat 0).V) (j : ℕ) (hj : j ≤ R.m) :
    ∃ y : (M.lat j).V, M.emb j y = Formalism.ThetaLiftIndependence.chainOpM C.wt C.Kmap j (M.emb 0 x) ∧ cmp j y = Ch.chainK j (cmp 0 x) := by
  induction j with
  | zero => exact ⟨x, rfl, rfl⟩
  | succ j ih =>
    obtain ⟨y, hy, hy'⟩ := ih (by omega)
    obtain ⟨z, hz⟩ := hrat j (by omega) y
    refine ⟨z, ?_, ?_⟩
    · rw [hz, hy]; rfl
    · rw [hK j (by omega) y z hz, hy']; rfl

end Chain

variable {D : D7}

theorem col_heq {R : Ranks} {Tau : Type} [Fintype Tau] {hc : Tau → HCParam R} {C C' : ColumnChain R Tau hc}
    (h : C = C') {φ : C.cls 0 → C.Y 0 → ℂ} {φ' : C'.cls 0 → C'.Y 0 → ℂ} (hφ : HEq φ φ') :
    HEq (C.col φ) (C'.col φ') := by
  subst h
  rw [eq_of_heq hφ]

theorem VGe_symm {w : D.what₂.places.Pl} (A B : HLat D.what₂.LL) (e : A.V ≃ₗ[D.what₂.LL] B.V)
    (he : ∀ x, x ∈ A.L ↔ e x ∈ B.L) {y : B.V} {s : ℝ} (h : VGe D w B.L y s) : VGe D w A.L (e.symm y) s := by
  obtain ⟨a, z, hz, rfl, ha⟩ := h
  refine ⟨a, e.symm z, ?_, map_smul _ _ _, ha⟩
  obtain ⟨t, ht, hz⟩ := (D.mem_locW_iff w _ _).1 hz
  refine (D.mem_locW_iff w _ _).2 ⟨t, ht, (he _).2 ?_⟩
  rw [← algebraMap_smul D.what₂.LL t, map_smul, LinearEquiv.apply_symm_apply, algebraMap_smul]
  exact hz

end GlobalTheory.Proof.LatticeValuationBound

end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

namespace GlobalTheory.Proof.ColumnWeightComparison

theorem colGeTw_of_cmpLite {D : D7} (c : LatCmp D) (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    {Fl : Fills (D.gat u w hg)} {Lv : Levels Fl} (Ch : Chain Lv) (h : CmpLite D c Tw u μ w hg Ch)
    (x : ((D.fm u).lat 0).V) (s : ℝ)
    (hx : vGeLat (D.gat u w hg) (Lv.Int D.R.m) (Ch.chainK D.R.m (c.cmp u w hg x)) s) :
    WeilJacquetShalikaLaw.ColGeTw Tw u μ w x s := by
  obtain ⟨cmp, h0, hK, hrat, hval⟩ := h
  obtain ⟨y, hy, hy'⟩ := GlobalTheory.Proof.LatticeValuationBound.exists_chain (Tw.fm u μ) Ch (c.embW u w hg) cmp hK hrat
    (Tw.e0 u μ x) D.R.m le_rfl
  refine ⟨y, ?_, hval y s (by rw [hy', h0]; exact hx)⟩
  rw [hy, Tw.embed_mul_block_embedding]
  rfl

theorem colGe0_of_colGeTw {D : D7} (Tw : TwForms D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (x : ((D.fm u).lat 0).V) (s : ℝ) (h0 : Tw.e0 u D.what₂.mu0 = Tw.eMu0 u 0 (Nat.zero_le _))
    (h : WeilJacquetShalikaLaw.ColGeTw Tw u D.what₂.mu0 w x s) : WeilJacquetShalikaLaw.ColGe0 D u w x s := by
  obtain ⟨y, hy, hv⟩ := h
  refine ⟨(Tw.eMu0 u D.R.m le_rfl).symm y, ?_,
    GlobalTheory.Proof.LatticeValuationBound.VGe_symm _ _ _ (Tw.eMu0_lat u D.R.m le_rfl) hv⟩
  have h1 := Tw.eMu0_emb u D.R.m le_rfl ((Tw.eMu0 u D.R.m le_rfl).symm y)
  rw [LinearEquiv.apply_symm_apply, hy] at h1
  have h2 := Tw.eMu0_emb u 0 (Nat.zero_le _) x
  rw [← h0, Tw.embed_mul_block_embedding] at h2
  exact eq_of_heq (h1.symm.trans (GlobalTheory.Proof.LatticeValuationBound.col_heq (D.memberColumns_twistedChain_base u) h2))

theorem cmpV_of_cmpLite (D : D7) (Y : LatInst D) (c : LatCmp D) (Dx : DivX D) (Tw : TwForms D)
    (LC : D.what₂.Tup → ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
      Σ Lv : Levels (Y.Fl u w hg), Chain Lv)
    (h0 : ∀ u, Tw.e0 u D.what₂.mu0 = Tw.eMu0 u 0 (Nat.zero_le _))
    (h : ∀ μ, DV.Used D μ → ∀ u (w : D.what₂.places.Pl)
      (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)), D.what₂.places.resChar w ∉ Dx.Qp μ →
      CmpLite D c Tw u μ w hg (LC μ u w hg).2) :
    WeilJacquetShalikaLaw.CmpV c Dx Tw (reW Y LC) := by
  intro u w hg μ hU hQ x s hx
  have key : WeilJacquetShalikaLaw.ColGeTw Tw u μ w x s :=
    colGeTw_of_cmpLite c Tw u μ w hg (LC μ u w hg).2 (h μ hU u w hg hQ) x s hx
  refine ⟨?_, fun _ => key⟩
  rintro rfl
  exact colGe0_of_colGeTw Tw u w x s (h0 u) key

end GlobalTheory.Proof.ColumnWeightComparison
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

namespace GlobalTheory.Proof.UnitaryWeightModels

theorem rowTwU_of_models : OrbitPlaces.OrbitLetterBoundsAll 11 1 → ∀ {eps : ℝ} (Fm : FamP eps),
    (∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, ∃ E : OrbitPlaces.Ent (Fm.D x i),
      OrbitPlaces.Shape (Fm.D x i) (Fm.L x i) (Fm.Gx x i) E) →
    (∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
      ModelsOK (Fm.D x i) (Fm.Gy x i) (Fm.ex x hx i).cmp (Fm.X x i) (Fm.ex x hx i).tw) →
    RowTwU Fm := by
  rintro h01 eps Fm ⟨xa, ha⟩ ⟨xb, hb⟩
  have hCL : OrbitPlaces.CLarge 11 1 Fm.GK Fm.cX.err :=
    OrbitPlaces.cLarge_of_fixed Fm.fixed.2.2.2.2.1 Fm.fixed.2.2.2.2.2.1 Fm.fixed.2.1
      (by rw [Fm.fixed.2.2.1]; norm_num)
  refine ⟨max xa xb, fun x hx h1 i => ?_⟩
  obtain ⟨E, hS⟩ := ha x (le_trans (le_max_left _ _) hx) h1 i
  obtain ⟨h0, LC, hLC⟩ := hb x (le_trans (le_max_right _ _) hx) h1 i
  exact ⟨LC,
    GlobalTheory.Proof.ColumnWeightComparison.cmpV_of_cmpLite _ _ _ _ _ LC h0 fun μ hU u w hg hQ => (hLC μ hU u w hg hQ).1,
    GlobalTheory.T.local_systems_lower_bounds_second_real_place _ _ (Fm.gatT x i) _ _ _ _ _ _ _ E LC (Fm.latTied x h1 i) (Fm.ex x h1 i).fills_all
      (Fm.ex x h1 i).fdef h01 hS hCL fun μ hU u w hg hQ => (hLC μ hU u w hg hQ).2⟩

end GlobalTheory.Proof.UnitaryWeightModels
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwoRGLeKOfSize
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

noncomputable section

namespace GlobalTheory.TwU

theorem two_rG_le_k_of_size {D : Formalism.BasicNotions.D7} {L : SizeData₂ D} (hS : Formalism.MainNotions.SizesAt L)
    (h : 70 < L.sc.x * L.sc.eps) : 2 * Formalism.MainNotions.G.rG L.sc ≤ D.R.k := by
  by_contra hk
  have hk : D.R.k < 2 * Formalism.MainNotions.G.rG L.sc := not_le.1 hk
  have hx := L.sc.one_lt_alt
  have he := L.sc.eps_pos
  have he2 := L.sc.eps_lt
  have hK := hS.2.2.1.1
  have h1 : L.sc.x ≤ L.sc.x ^ (9 / 2 + 10 * L.sc.eps - Formalism.MainNotions.szTh L) :=
    Real.self_le_rpow_of_one_le hx.le (by unfold Formalism.MainNotions.szTh; linarith)
  have h2 : (D.R.k : ℝ) ≤ 2 * (Formalism.MainNotions.G.rG L.sc : ℝ) := by exact_mod_cast hk.le
  have h3 : (Formalism.MainNotions.G.rG L.sc : ℝ) ≤ 8 * (Formalism.MainNotions.G.hG L.sc + 2) / L.sc.eps + 2 := by
    unfold Formalism.MainNotions.G.rG Formalism.MainNotions.G.KG
    have := Nat.ceil_lt_add_one (a := 8 * (Formalism.MainNotions.G.hG L.sc + 2) / L.sc.eps)
      (div_nonneg (by unfold Formalism.MainNotions.G.hG; linarith) he.le)
    push_cast
    linarith
  have h5 : L.sc.x ≤ 2 * (8 * (Formalism.MainNotions.G.hG L.sc + 2) / L.sc.eps + 2) := by linarith
  have h6 := mul_le_mul_of_nonneg_right h5 he.le
  have h7 : 2 * (8 * (Formalism.MainNotions.G.hG L.sc + 2) / L.sc.eps + 2) * L.sc.eps =
      2 * (8 * (Formalism.MainNotions.G.hG L.sc + 2) + 2 * L.sc.eps) := by
    field_simp
  rw [h7] at h6
  unfold Formalism.MainNotions.G.hG at h6
  linarith

theorem two_rG_le_k_large {eps : ℝ} (Fm : FamP eps) :
    ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, 2 * rG (Fm.L x i).sc ≤ (Fm.D x i).R.k := by
  refine ⟨71 / eps, fun x hx hx1 i => two_rG_le_k_of_size (Fm.sizes x hx1 i) ?_⟩
  have hs : (Fm.L x i).sc.x = x := Fm.L_x x i hx1
  have he : (Fm.L x i).sc.eps = eps := Fm.L_eps x i
  have hp : 0 < eps := he ▸ (Fm.L x i).sc.eps_pos
  rw [hs, he]
  have : 71 ≤ x * eps := (div_le_iff₀ hp).1 hx
  linarith

end GlobalTheory.TwU
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain

namespace GlobalTheory.Svd

noncomputable def entStd (D : D7) : Formalism.MainNotions.OrbitPlaces.Ent D := ⟨nuD D, nuRowOK D, nuD_rows D, 0, 0, 0, 0⟩

theorem rowTwU : ∀ {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd), RowE Q Lk (fun _ D O _ _ => ModelsAt D O) →
    Row Q Lk fun 𝒜 _ => Closed 𝒜 fun Fm _ => GlobalTheory.TwU.RowTwU Fm := by
  intro Bd Q Lk hE
  refine ⟨fun _ D O _ _ => ModelsAt D O, hE, fun 𝒜 σ s => ?_⟩
  refine ⟨1, one_pos, fun eps _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ hc _ => ?_⟩⟩
  obtain ⟨_, _, _, t⟩ := s Fm hc
  have h01 : Formalism.MainNotions.OrbitPlaces.OrbitLetterBoundsAll 11 1 := Formalism.MainNotions.DIV.Bridge.DworkPowerSeriesWeights.split_bound_eleven_one
  obtain ⟨xa, ha⟩ := GlobalTheory.ShapeRows.shape Fm
  obtain ⟨xb, hb⟩ := GlobalTheory.TwU.two_rG_le_k_large Fm
  refine GlobalTheory.Proof.UnitaryWeightModels.rowTwU_of_models h01 Fm ⟨xa, fun x hx h1 i => ⟨entStd _, ha x hx h1 i _⟩⟩
    ⟨xb, fun x hx h1 i => (t x h1 i).2 (Fm.latTied x h1 i) (hb x hx h1 i)⟩

end GlobalTheory.Svd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BundleBothPartsOfStandardKernelAndSixHypotheses
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain

namespace GlobalTheory.Svd

theorem servH_row (hA : Formalism.L2.KerInert.AlgTAll) (hG : Formalism.L2.KerInert.GenusOneModelExistsLattice) (hC : Formalism.L2.KerInert.Rep.CurveDict)
    (hI : Formalism.L2.KerInert.IntInert) (hE : GlobalTheory.TwV.Lt.AdmAtEnt2) (hX : GlobalTheory.TwV.Lt.CurveEx) :
    ∀ {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd) (ker : ∀ (D : D7) (O : Obj D) (c : ℝ), Bd D O c → KerEntTied O.ex),
      (∀ K X f T c, Q K X f T c → positionOf HasPart K X f T c) →
      RowE Q Lk (fun _ D O c b => StdTie D O (ker D O c b)) → Row Q Lk (ServH ker) := by
  intro Bd Q Lk ker hQ hT
  have hM : RowE Q Lk (fun _ D O _ _ => ModelsAt D O) :=
    RowE.of_all fun _ K β _ _ _ hq _ => GlobalTheory.T.tuplesHaveLocalModels_at_constructedPoint_over_trueColumns hE hX K β (hQ _ _ _ _ _ hq)
  exact Row.and (GlobalTheory.Svd.rowTwU Q Lk hM) (GlobalTheory.Pdv.rowAt_of_stdTie hA hG hC hI Q Lk ker hT)

end GlobalTheory.Svd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BundleBothPartsOfStandardKernelAndSixHypothesesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bundle_bothParts_of_standardKernel_and_six_hypotheses : Formalism.L2.KerInert.AlgTAll → Formalism.L2.KerInert.GenusOneModelExistsLattice → Formalism.L2.KerInert.Rep.CurveDict → Formalism.L2.KerInert.IntInert → GlobalTheory.TwV.Lt.AdmAtEnt2 → GlobalTheory.TwV.Lt.CurveEx → ∀ {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd) (ker : ∀ (D : D7) (O : Obj D) (c : ℝ), Bd D O c → KerEntTied O.ex), (∀ K X f T c, Q K X f T c → positionOf HasPart K X f T c) → RowE Q Lk (fun _ D O c b => StdTie D O (ker D O c b)) → Row Q Lk (ServH ker) := by
  first | exact @GlobalTheory.Svd.servH_row | exact GlobalTheory.Svd.servH_row | (intros; apply GlobalTheory.Svd.servH_row <;> assumption)
end
