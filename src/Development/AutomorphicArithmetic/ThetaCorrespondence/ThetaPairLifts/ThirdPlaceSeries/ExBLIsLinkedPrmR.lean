module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WitnessesPassAlongSetDivision
public import Lean
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BwitExists

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsLinkedOfEq
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsRecPinE
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TiedDataSAssemble
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NTiedAllAtWit
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Mem.Top.Bl
theorem exists_core_parameters_agree : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) (K : Ctx) (q : WPt p.s K), ∃ (I : TwIn (q.w.D q.Z)) (n : _root_.Formalism.L2.NTiedAllAlt (q.w.D q.Z) q.O.ex.nch I), I.E = twEOf q.O.ex.xd ∧ DQ.GoodAllAt (q.w.D q.Z) q.O.ex.nch I ∧ (⟨n.cf, n.tp⟩ : Σ c : CharFrame (q.w.D q.Z), TupTied (q.w.D q.Z) c q.O.ex.nch) = ⟨TC.cf q.w.I q.w.l q.Z, q.x.n.tp⟩ ∧ n.gal = q.core_data_of_point.a.all.gal ∧ n.n = q.core_data_of_point.a.all.n ∧ n.exp = q.core_data_of_point.a.all.exp ∧ n.chiD = q.core_data_of_point.a.all.chiD ∧ n.twF = q.core_data_of_point.a.all.twF ∧ HEq n.types q.core_data_of_point.a.all.types ∧ HEq n.cover q.core_data_of_point.a.all.cover ∧ n.plB = q.core_data_of_point.a.all.plB := by
  intro hL p K q
  obtain ⟨I, hE, hG, hC⟩ := q.x.good.tw
  have hch := q.core_data_of_point.a.chr_eq
  have hc : Formalism.L2.NChoiceTied (q.w.D q.Z) q.O.ex.nch I (Formalism.L2.avDesign (q.w.D q.Z)) := by
    have c := q.core_data_of_point.a.all.choice
    first
    | exact { twI_conj := c.twI_conj, sd_place := c.sd_place, emb_side := c.emb_side, sd_conj := c.sd_conj, one := c.one,
              good := fun w hw h => hC w hw h, conj := c.conj }
    | exact { twI_conj := c.twI_conj, sd_place := c.sd_place, emb_side := c.emb_side, sd_conj := c.sd_conj, one := c.one,
              conj := c.conj }
  refine ⟨I, { q.core_data_of_point.a.all with choice := hc }, hE, hG, hch, rfl, rfl, rfl, rfl, rfl, HEq.rfl, HEq.rfl, rfl⟩
end GlobalTheory.Mem.Top.Bl
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TiedDataSAssemble
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Mem.Top.Bl
open _root_.Formalism.L2 in
set_option maxHeartbeats 1000000 in
theorem tiedDataS_assemble_alt {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {K : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} (ex : Extra D L hT Gi Gl K Y cX)
    (host : Formalism.L2.Host.HostTied D) (level : Formalism.L2.Host.LevelTied D) (cols : Formalism.L2.Forms.ColsTiedSym D) (full : Formalism.L2.Forms.ColsFullS cols)
    (extra : Formalism.L2.Forms.ColsExtraTiedS full ex) (provA : Formalism.BasicNotions.TH.ProvA) (theta : Formalism.L2.Theta.AllTied D ex.th provA) (twIn : Formalism.MainNotions.TwIn D)
    (n : _root_.Formalism.L2.NTiedAllAlt D ex.nch twIn) (frameN : ∀ x, n.gal.fr.jE x = host.fr.j x)
    (cf : Formalism.L2.Host.CharFrame D) (tp : Formalism.L2.Host.TupTied D cf ex.nch)
    (h : (⟨n.cf, n.tp⟩ : Σ c : Formalism.L2.Host.CharFrame D, Formalism.L2.Host.TupTied D c ex.nch) = ⟨cf, tp⟩)
    (thetaChr : Formalism.L2.Host.ThetaChrTied D cf ex.nch tp ex.th) (chrVal : Formalism.L2.Host.ValLL0 D cf) (chrDt : Formalism.L2.Host.DtTied D cf)
    (chrN : Formalism.L2.Host.NCharTied D cf ex.nch tp) (chrGal : Formalism.L2.Host.NGalChrTied D cf ex.nch tp)
    (chrPsi : Formalism.L2.Host.PsiChoiceCompatible D cf ex.nch tp) (sameChr : Formalism.L2.JoinChr.SameChr theta.T thetaChr)
    (what₂ : Formalism.L2.Rows.RowsCompatible D host cf tp) (inK : Y.Lev → ℕ → Prop) (geo : Formalism.L2.Geo.GeoTiedP Y inK)
    (tw0 : TwForms D) (he : ex.tw = tw0) (tw : Formalism.L2.Forms.SymmetricTwistedColumnsAtPrimes tp cols tw0) (emt : Formalism.L2.Rows.EMtTied D cols tw)
    (g : Formalism.L2.G.GroupCompatibilityAll D hT ex.cmp) (herm_eq : g.herm = full.1.to0) (forms_eq : g.forms = fun u => (cols.forms u).to0)
    (P : ∀ (c : Formalism.L2.Host.CharFrame D) (t : Formalism.L2.Host.TupTied D c ex.nch) (C : Formalism.L2.Forms.ColsTiedSym D), Formalism.L2.Forms.SymmetricTwistedColumnsAtPrimes t C tw0 → Prop)
    (hP : P cf tp cols tw) :
    ∃ S : _root_.Formalism.L2.TiedDataSAlt ex, S.host = host ∧ S.cols = cols ∧ HEq S.full full ∧ S.g = g ∧
      (⟨S.provA, S.theta⟩ : Σ a, Formalism.L2.Theta.AllTied D ex.th a) = ⟨provA, theta⟩ ∧
      (⟨S.twIn, S.n⟩ : Σ I, _root_.Formalism.L2.NTiedAllAlt D ex.nch I) = ⟨twIn, n⟩ ∧ HEq S.thetaChr thetaChr ∧
      (∀ a, S.chrDt.eDt a = chrDt.eDt a) ∧
      (S.what₂.O.pieces.rcf = what₂.O.pieces.rcf ∧ S.what₂.O.pieces.MDel = what₂.O.pieces.MDel) ∧
      S.inK = inK ∧ HEq S.geo geo ∧ P _ _ _ (he ▸ S.tw) := by
  cases h
  subst he
  first
  | exact ⟨{ host := host, level := level, cols := cols, full := full, extra := extra, provA := provA, theta := theta,
               twIn := twIn, n := n, frameN := frameN, thetaChr := thetaChr, chrVal := chrVal, chrDt := chrDt, chrN := chrN,
               chrGal := chrGal, chrPsi := chrPsi, sameChr := sameChr, what₂ := what₂, inK := inK, geo := geo, tw := tw, emt := emt,
               g := g, herm_eq := herm_eq, forms_eq := forms_eq },
        rfl, rfl, HEq.rfl, rfl, rfl, rfl, HEq.rfl, fun _ => rfl, ⟨rfl, rfl⟩, rfl, HEq.rfl, hP⟩
  | exact ⟨{ host := host, level := level, cols := cols, full := full, extra := extra, provA := provA, theta := theta,
               twIn := twIn, n := n, thetaChr := thetaChr, chrVal := chrVal, chrDt := chrDt, chrN := chrN,
               chrGal := chrGal, chrPsi := chrPsi, sameChr := sameChr, what₂ := what₂, inK := inK, geo := geo, tw := tw, emt := emt,
               g := g, herm_eq := herm_eq, forms_eq := forms_eq },
        rfl, rfl, HEq.rfl, rfl, rfl, rfl, HEq.rfl, fun _ => rfl, ⟨rfl, rfl⟩, rfl, HEq.rfl, hP⟩
set_option maxHeartbeats 2000000 in
theorem WPt.exists_pinned_spectral_data_compatible : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.WeberRayFieldSt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) (K : Ctx) (q : WPt p.s K), Formalism.L2.Host.LevelTied (q.w.D q.Z) → Formalism.L2.Rows.ZetaCompatible (q.w.D q.Z) → ∃ S : _root_.Formalism.L2.TiedDataSAlt q.O.ex, _root_.GlobalTheory.Mem.Top.Bl.SpectralDataCompatible q S := by
  intro hA hW hL p K q hlev hze
  obtain ⟨extra, g, hg, hherm, hforms⟩ := WPt.extraTied_col p.s K q
  obtain ⟨I, n, hE, hgood, hchr, h1, h2, h3, h4, h5, h6, h7, h8⟩ := _root_.GlobalTheory.Mem.Top.Bl.exists_core_parameters_agree hL p K q
  obtain ⟨he, tw, hstd, emt⟩ := GlobalTheory.Mem.Top.Bl.WPt.colsTwTied p.s K q
  obtain ⟨dt, hdt⟩ := TC.dtTied_true q.w.I q.w.ok q.w.pins q.w.l q.Z
  have hO : ∃ O : Formalism.L2.Rows.OTied (q.w.D q.Z) q.core_data_of_point.a.host (TC.cf q.w.I q.w.l q.Z),
      O.pieces.rcf = GlobalTheory.Mem.HD.qb q.core_data_of_point.a.host.fr.ι q.w.δ.ray ∧ O.pieces.MDel = GlobalTheory.Mem.HD.qb q.core_data_of_point.a.host.fr.ι q.w.δ.M' := by
    generalize q.core_data_of_point.a.host = H
    rw [← ColW.cf_eq]
    exact GlobalTheory.Mem.CyclotomicFieldContainment.oTied_of_ksExact hA hW (q.w.st q.Z) q.f q.w.δ q.w.exact H
  obtain ⟨O, hO1, hO2⟩ := hO
  have hval : Formalism.L2.Host.ValLL0 (q.w.D q.Z) (TC.cf q.w.I q.w.l q.Z) := by
    rw [← ColW.cf_eq]
    exact q.w.val _ _ _ _ _ _
  have hfr : ∀ x, n.gal.fr.jE x = q.core_data_of_point.a.host.fr.j x := by
    rw [h1]
    exact q.core_data_of_point.a.frameN
  obtain ⟨S, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12⟩ :=
    _root_.GlobalTheory.Mem.Top.Bl.tiedDataS_assemble_alt q.O.ex q.core_data_of_point.a.host hlev q.x.col.C q.x.col.full extra q.x.th.provA q.x.th.all I n hfr
      (TC.cf q.w.I q.w.l q.Z) q.x.n.tp hchr q.x.th.chr hval dt q.core_data_of_point.a.chrN q.core_data_of_point.a.chrGal q.x.n.chrPsi q.x.th.same
      ⟨O, q.O.ex.kap_def, hze⟩ q.x.div.inK q.x.div.geo (q.w.tw q.Z) he tw emt g hherm hforms
      (fun _ _ _ t => TC.StdTw q.w.I q.w.l q.Z q.w.l0 t) hstd
  have key : ∀ Q : (Σ I, _root_.Formalism.L2.NTiedAllAlt (q.w.D q.Z) q.O.ex.nch I) → Prop, Q ⟨I, n⟩ → Q ⟨S.twIn, S.n⟩ :=
    fun Q hQ => s6 ▸ hQ
  refine ⟨S, s1, s2, s3, s4 ▸ hg, s5, key (fun z => z.1.E = _) hE, key (fun z => DQ.GoodAllAt _ _ z.1) hgood,
    key (fun z => (⟨z.2.cf, z.2.tp⟩ : Σ c : CharFrame (q.w.D q.Z), TupTied (q.w.D q.Z) c q.O.ex.nch) = _) hchr,
    key (fun z => z.2.gal = _) h1, key (fun z => z.2.n = _) h2, key (fun z => z.2.exp = _) h3,
    key (fun z => z.2.chiD = _) h4, key (fun z => z.2.twF = _) h5, key (fun z => HEq z.2.types _) h6,
    key (fun z => HEq z.2.cover _) h7, key (fun z => z.2.plB = _) h8, s7, fun a => (s8 a).trans (hdt a), ?_, s10, s11, he, s12⟩
  rw [s9.1, s9.2, s1]
  exact ⟨hO1, hO2⟩
end GlobalTheory.Mem.Top.Bl
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TiedDataSAssembleStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_spectral_data_compatible : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.WeberRayFieldSt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) (K : Ctx) (q : WPt p.s K), Formalism.L2.Host.LevelTied (q.w.D q.Z) → Formalism.L2.Rows.ZetaCompatible (q.w.D q.Z) → ∃ S : _root_.Formalism.L2.TiedDataSAlt q.O.ex, _root_.GlobalTheory.Mem.Top.Bl.SpectralDataCompatible q S := by
  first | exact @_root_.GlobalTheory.Mem.Top.Bl.WPt.exists_pinned_spectral_data_compatible | exact _root_.GlobalTheory.Mem.Top.Bl.WPt.exists_pinned_spectral_data_compatible | (intros; apply _root_.GlobalTheory.Mem.Top.Bl.WPt.exists_pinned_spectral_data_compatible <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TiedSKAtWitnesses
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.JointsSTrue
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct
noncomputable section
namespace GlobalTheory.Mem.JointsTrue
open _root_.Formalism.L2 _root_.Formalism.L2.Host ReciprocityTheory.Neutral.Bridge.HCFR
set_option maxHeartbeats 1000000 in
theorem joints_of_standard_character : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (T : _root_.Formalism.L2.TiedDataSAlt ex), I.StdC l Z T.cols → I.StdDt l Z T.full.1.base.dt → T.n.cf = I.cf l Z → (∀ a, T.chrDt.eDt a = (QuotientGroup.mk a : DtQ B.host I.SQ)) → Nonempty (Formalism.L2.Host.DivisorCharacterCompatibility (I.rec7 l Z) T.n.cf ex.nch T.n.tp Y) → Formalism.L2.Theta.IsStdChar (I.rec7 l Z) T.theta.W.ψ (-1) → _root_.Formalism.L2.JointsSAlt T := by
  intro B X I hOk hP l Z L hT Gi Gl K Y cX ex T hC hD hcf he hdiv hψ
  refine ⟨fun P e hi k y hy x hx => ?_, fun k => ?_, fun k v h a n hn ha => ?_, fun k v h ε hε c y hc => ?_, hdiv⟩
  · exact (hD x _ (isDetLift_local (I.rec7 l Z) P e hi k y hy x hx)).trans (he _).symm
  · rw [hcf, show (T.cols.forms (I.rec7 l Z).u₀).gl.piG = X.piG from (hC _).gl.piG]
    exact GlobalTheory.Core.Cls.JointsStd.piBar_std I hOk k
  · rw [hcf]
    exact GlobalTheory.Core.Cls.JointsStd.om_std I hOk l Z _ (hC _).gl k v h a n hn ha
  · have hy : algebraMap (I.rec7 l Z).host.F (v.adicCompletion (I.rec7 l Z).host.F) (y : (I.rec7 l Z).host.F) ∈
        v.adicCompletionIntegers (I.rec7 l Z).host.F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, valued_algebraMap]
      exact HeightOneSpectrum.valuation_le_one v y
    have e1 := GlobalTheory.Mem.TypePrimes.psiG_true I hOk hP l Z _ (hC (I.rec7 l Z).u₀).gl _ hψ k v h ε hε c y hc ⟨_, hy⟩ rfl
    unfold Joints.redV
    rw [dite_eq_left hy]
    exact e1
end GlobalTheory.Mem.JointsTrue
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.Mem.Col2.starE
namespace GlobalTheory.Mem.Top.Bl.WitSK
end GlobalTheory.Mem.Top.Bl.WitSK
open Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2.TC Matrix in
set_option maxHeartbeats 1600000 in
theorem GlobalTheory.Mem.Top.Bl.exists_kernel_spectral_data_at_witnesses : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) (K : Ctx) (q : WPt p.s K), ∀ (S : _root_.Formalism.L2.TiedDataSAlt q.O.ex) (t : Formalism.L2.Ker.KerEntTied q.O.ex), _root_.GlobalTheory.Mem.Top.Bl.SpectralDataCompatible q S → KPin q t → ∃ T : _root_.Formalism.L2.TiedDataSKAlt q.O.ex, T.toTiedDataS = S ∧ T.ker = t ∧ (∀ u i hi, T.crd u i hi = 1) ∧ _root_.Formalism.L2.Rows.RowPinMinAlt T ∧ _root_.Formalism.L2.JointsSAlt S ∧ Nonempty (PLift (Formalism.L2.Theta.WeilCompatibleEquivariance S.theta.W)) := by
  intro hL p K q S t hS hKp
  obtain ⟨he, hTw⟩ := hS.tw
  have hK := hKp.std
  have hC : TC.StdC q.w.I q.w.l q.Z S.cols := hS.cols ▸ q.x.col.std
  have hsp := GlobalTheory.Mem.Col2.TC.spaces_in_coordinates q.w.I q.w.ok q.w.pins q.w.l q.Z
  have hD : TC.StdDt q.w.I q.w.l q.Z S.full.1.base.dt := by
    have key : ∀ (C : ColsTiedSym (q.w.D q.Z)) (F : ColsFullS C), C = q.x.col.C → HEq F q.x.col.full →
        TC.StdDt q.w.I q.w.l q.Z F.1.base.dt := by
      intro C F hC' hF
      subst hC'
      cases hF
      exact q.x.col.stdDt
    exact key _ _ hS.cols hS.full
  have hcf : S.n.cf = TC.cf q.w.I q.w.l q.Z := congrArg Sigma.fst hS.chr
  have hdiv : Nonempty (Formalism.L2.Host.DivisorCharacterCompatibility (q.w.D q.Z) S.n.cf q.O.ex.nch S.n.tp q.O.X) :=
    ⟨WitSK.of_sigma_eq hS.chr (fun c tp => Formalism.L2.Host.DivisorCharacterCompatibility (q.w.D q.Z) c q.O.ex.nch tp q.O.X) q.x.div.chr⟩
  have hψ : Formalism.L2.Theta.IsStdChar (q.w.D q.Z) S.theta.W.ψ (-1) :=
    WitSK.of_sigma_eq hS.theta (fun _ A => Formalism.L2.Theta.IsStdChar (q.w.D q.Z) A.W.ψ (-1)) q.x.th.std
  have hweq : Formalism.L2.Theta.WeilCompatibleEquivariance S.theta.W :=
    WitSK.of_sigma_eq hS.theta (fun _ A => Formalism.L2.Theta.WeilCompatibleEquivariance A.W) q.x.th.weq
  refine ⟨{ S with ker := t, crd := fun u i hi => 1, crd_gram := ?_, crd_lat := ?_, ker_sharp := ?_, ker_frm := ?_ }, rfl, rfl,
    fun _ _ _ => rfl, ⟨fun u => ?_, fun u μ hμ _ h1 => ?_, q.x.what₂.r.Y.bu⟩,
    _root_.GlobalTheory.Mem.JointsTrue.joints_of_standard_character q.w.I q.w.ok q.w.pins q.w.l q.Z _ _ _ _ _ _ _ q.O.ex S hC hD hcf hS.dt hdiv hψ, ⟨⟨hweq⟩⟩⟩
  · intro u i hi
    rw [(hsp.2.2.2 i hi).1, Units.val_one, mul_one]
    ext a b
    simp [cT, Matrix.one_apply]
    exact if_congr eq_comm rfl rfl
  · intro u i hi x
    rw [(hsp.2.2.2 i hi).2.1 x, Units.val_one, Matrix.one_mulVec]
    rfl
  · intro μ
    rw [GlobalTheory.Mem.Col2.TC.KerSK.sharp_heq hK.X_eq (GlobalTheory.Mem.Col2.TC.KerSK.rowSG_heq hK.X_eq hK.Pr hK.sel hK.S hK.tup) hK.cst μ]
    exact q.w.ok.sharp μ
  · intro u μ i hi y τ
    rw [hK.O.frm u μ i y]
    have h1 : Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT (q.w.D q.Z)) (Units.val (1 : GL (Fin ((q.w.D q.Z).R.N i)) (q.w.D q.Z).host.E)) τ = 1 := by
      simp [Formalism.L2.Forms.atInf]
    rw [h1, one_mul]
    have hY := hTw.1.eY u μ i hi
    rw [GlobalTheory.Mem.Col2.TC.KerSK.ch_cast he] at hY
    simp only [twYS, Equiv.trans_apply, hY, Equiv.refl_symm, Equiv.refl_apply, eYS]
    split_ifs with h
    · exact congrFun ((hC u).eY i hi h y).symm τ
    · exact congrFun ((hC u).eYC i _ _ y).symm τ
  · exact GlobalTheory.Mem.Col2.LowerTie.lowerMap_tie q.w.I q.w.ok q.w.pins q.w.l q.Z u _ _ _ (hC u)
  · exact _root_.GlobalTheory.Mem.Col2.LowerTie.lowerMap_tieTw_alt q.w.I q.w.ok q.w.pins q.w.l q.Z q.w.l0 _ _ _ _ _ _ _ q.O.ex _ he hC hTw u μ hμ h1
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsRecPinE
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Mem.Top.Bl
theorem WPt.exists_recPinE_alt : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.WeberRayFieldSt → GlobalTheory.NT.RayField →
    ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) (K : Ctx) (q : WPt p.s K), Formalism.L2.Host.LevelTied (q.w.D q.Z) →
      Formalism.L2.Rows.ZetaCompatible (q.w.D q.Z) → EntC q.x.ker → ∃ R : _root_.Formalism.L2.RecTAlt q.O.ex, _root_.GlobalTheory.Mem.Top.Bl.RecordCompatibleExtended q R := by
  intro hA hW hR hL p K q hLT hZe hE
  obtain ⟨S, hS⟩ := _root_.GlobalTheory.T.exists_spectral_data_compatible hA hW hL p K q hLT hZe
  obtain ⟨t, hK, hstd, hrd⟩ := GlobalTheory.Mem.Top.Bl.WPt.exists_kerTie p.s K q hE
  obtain ⟨T, hTS, hTk, hcrd, hpin, hj, ⟨⟨hw⟩⟩⟩ := _root_.GlobalTheory.Mem.Top.Bl.exists_kernel_spectral_data_at_witnesses hL p K q S t hS hK
  have hp := GlobalTheory.Mem.Top.Bl.hostPins_wpt hR p.s K q
  subst hTS hTk
  obtain ⟨hd, -⟩ := _root_.GlobalTheory.HostDatumExists.exists_hostDatum_alt hA _ _ _ _ _ _ _ _ q.O.ex T.toTiedDataS hp q.x.pin.d3b
  exact ⟨⟨T, hpin, hj, ⟨hd⟩, hw⟩, ⟨⟨hS, hK, hcrd⟩, hE, hstd, hrd⟩⟩
end GlobalTheory.Mem.Top.Bl
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsRecPinEStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_reciprocity_record_compatible : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.WeberRayFieldSt → GlobalTheory.NT.RayField → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) (K : Ctx) (q : WPt p.s K), Formalism.L2.Host.LevelTied (q.w.D q.Z) → Formalism.L2.Rows.ZetaCompatible (q.w.D q.Z) → EntC q.x.ker → ∃ R : _root_.Formalism.L2.RecTAlt q.O.ex, _root_.GlobalTheory.Mem.Top.Bl.RecordCompatibleExtended q R := by
  first | exact @_root_.GlobalTheory.Mem.Top.Bl.WPt.exists_recPinE_alt | exact _root_.GlobalTheory.Mem.Top.Bl.WPt.exists_recPinE_alt | (intros; apply _root_.GlobalTheory.Mem.Top.Bl.WPt.exists_recPinE_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsBdRecOfEq
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Mem.Top.Bl
theorem exists_bdRec_of_eq_alt {D D' : D7} {O : Obj D} {O' : Obj D'} (h : (⟨D, O⟩ : Σ D : D7, Obj D) = ⟨D', O'⟩)
    (R : _root_.Formalism.L2.RecTAlt O'.ex) (c : ℝ) :
    ∃ b : _root_.GlobalTheory.Mem.Top.Bl.BoundaryReciprocity D O c, (⟨D, O, b⟩ : Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Mem.Top.Bl.BoundaryReciprocity D O c) = ⟨D', O', R⟩ := by
  cases h
  exact ⟨R, rfl⟩
end GlobalTheory.Mem.Top.Bl
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsLinkedOfEq
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
namespace GlobalTheory.Mem.Top.Bl
theorem exists_linked_of_eq_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx}
    (hB : ∀ (q : WPt p.s K) (R : _root_.Formalism.L2.RecTAlt q.O.ex), _root_.GlobalTheory.Mem.Top.Bl.RecordCompatibleExtended q R → ∀ (c : ℝ)
      (_ : {n : ℕ × ℕ // (q.w.D q.Z).s.Del = (n.1 : ℚ) ∧ q.O.L.etaSz = ((q.w.D q.Z).R.m : ℝ) * (n.2 : ℝ)}),
      q.O.L.sc = K.s → Val K.C K.cD K.ch q.O.L → ∃ b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c, b.R = R ∧ Nonempty (_root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b))
    (q : WPt p.s K) (R' : _root_.Formalism.L2.RecTAlt q.O.ex) (hR' : _root_.GlobalTheory.Mem.Top.Bl.RecordCompatibleExtended q R') (c : ℝ) {D : D7} {O : Obj D} (R : _root_.GlobalTheory.Mem.Top.Bl.BoundaryReciprocity D O c)
    (he : (⟨D, O, R⟩ : Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Mem.Top.Bl.BoundaryReciprocity D O c) = ⟨q.w.D q.Z, q.O, R'⟩) (hsc : O.L.sc = K.s)
    (hv : Val K.C K.cD K.ch O.L) (n : {n : ℕ × ℕ // D.s.Del = (n.1 : ℚ) ∧ O.L.etaSz = (D.R.m : ℝ) * (n.2 : ℝ)}) :
    ∃ b : _root_.GlobalTheory.Fc.BundleCondition D O c, ∃ (q' : WPt p.s K) (b' : _root_.GlobalTheory.Fc.BundleCondition (q'.w.D q'.Z) q'.O c), Nonempty (_root_.GlobalTheory.Mem.Top.Bl.BundleWitness q' b') ∧
      (⟨D, O, b⟩ : Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Fc.BundleCondition D O c) = ⟨q'.w.D q'.Z, q'.O, b'⟩ := by
  obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.mp he
  obtain ⟨rfl, -⟩ := Sigma.mk.inj_iff.mp (eq_of_heq h2)
  obtain ⟨b, -, hW⟩ := hB q R' hR' c n hsc hv
  exact ⟨b, q, b, hW, rfl⟩
theorem exBL_isLinked_alt : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.WeberRayFieldSt → GlobalTheory.NT.RayField → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), WitExE p.s → (GlobalTheory.Fc.EvP fun _ K => ∀ q : WPt p.s K, Formalism.L2.Rows.ZetaCompatible (q.w.D q.Z)) → (GlobalTheory.Fc.EvP fun _ K => ∀ (q : WPt p.s K) (R : _root_.Formalism.L2.RecTAlt q.O.ex), _root_.GlobalTheory.Mem.Top.Bl.RecordCompatibleExtended q R → ∀ (c : ℝ) (_ : {n : ℕ × ℕ // (q.w.D q.Z).s.Del = (n.1 : ℚ) ∧ q.O.L.etaSz = ((q.w.D q.Z).R.m : ℝ) * (n.2 : ℝ)}), q.O.L.sc = K.s → Val K.C K.cD K.ch q.O.L → ∃ b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c, b.R = R ∧ Nonempty (_root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b)) → GlobalTheory.Fc.ExBL KPx (IsBuiltE p.s) (IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) := by
  intro hA hW hRay hL p hWit hZe hB
  refine ⟨fun _ _ _ _ _ => True, GlobalTheory.Fc.largeBaseProperty_true, ?_⟩
  unfold GlobalTheory.Fc.ExB
  refine GlobalTheory.Fc.EvP.mono (fun κ K _ H => ?_) (GlobalTheory.Fc.EvP.and hZe hB)
  intro β hβ c
  obtain ⟨q, hq, hE⟩ := hWit K β hβ.1
  obtain ⟨C5, c6, Cb, hG⟩ := β.good
  have hO : Over β.X.toD7 K.P K.Lv := by
    obtain ⟨sp, hT, hY, hA', hV, hz, e, -⟩ := β.c.isOver
    exact ⟨sp, hT, hY, hA', hV, hz, β.X, e, rfl⟩
  have hP : K.P.H.levelPrimes = {K.P.H.g 0, K.P.H.g 1, K.P.H.pde, K.P.H.pde', DC.q0H K.P.H} :=
    hG.host.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hLT : Formalism.L2.Host.LevelTied β.D :=
    GlobalTheory.Mem.HD.levelTied_of_levEx _ ((GlobalTheory.Mem.HD.levEx_of_over _ _ _ hO hP).2 _ _)
  have hD : β.D = q.w.D q.Z := congrArg Sigma.fst hq
  have hLT' : Formalism.L2.Host.LevelTied (q.w.D q.Z) := hD ▸ hLT
  obtain ⟨R', hR'⟩ := _root_.GlobalTheory.T.exists_reciprocity_record_compatible hA hW hRay hL p K q hLT' (H.1 q) hE
  obtain ⟨R, he⟩ := _root_.GlobalTheory.Mem.Top.Bl.exists_bdRec_of_eq_alt hq R' c
  have hv : Val K.C K.cD K.ch β.O.L := β.p.pt_val β.val
  exact _root_.GlobalTheory.Mem.Top.Bl.exists_linked_of_eq_alt H.2 q R' hR' c R he β.sc hv ⟨(_, _), hv.Del_eq, hv.eta_eq⟩
end GlobalTheory.Mem.Top.Bl
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsLinkedOfEqStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eta_size_recursion_alt : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.WeberRayFieldSt → GlobalTheory.NT.RayField → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), WitExE p.s → (GlobalTheory.Fc.EvP fun _ K => ∀ q : WPt p.s K, Formalism.L2.Rows.ZetaCompatible (q.w.D q.Z)) → (GlobalTheory.Fc.EvP fun _ K => ∀ (q : WPt p.s K) (R : _root_.Formalism.L2.RecTAlt q.O.ex), _root_.GlobalTheory.Mem.Top.Bl.RecordCompatibleExtended q R → ∀ (c : ℝ) (_ : {n : ℕ × ℕ // (q.w.D q.Z).s.Del = (n.1 : ℚ) ∧ q.O.L.etaSz = ((q.w.D q.Z).R.m : ℝ) * (n.2 : ℝ)}), q.O.L.sc = K.s → Val K.C K.cD K.ch q.O.L → ∃ b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c, b.R = R ∧ Nonempty (_root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b)) → GlobalTheory.Fc.ExBL KPx (IsBuiltE p.s) (IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) := by
  first | exact @_root_.GlobalTheory.Mem.Top.Bl.exBL_isLinked_alt | exact _root_.GlobalTheory.Mem.Top.Bl.exBL_isLinked_alt | (intros; apply _root_.GlobalTheory.Mem.Top.Bl.exBL_isLinked_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ZeUPrmRNEb
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ZeUPrmRNEb
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev GlobalTheory.Mem.R3 in
set_option maxHeartbeats 4000000 in
theorem GlobalTheory.Mem.Top.Bl.ze_u_prm_of_extension_with_law : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) → ZeU (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s := by
  intro hPr hL N S Γ hN K q
  have hK : ∃ t : Formalism.L2.Ker.KerEntTied q.O.ex, KPin q t := by
    obtain ⟨B, f, T, w, Z, O, x⟩ := q
    obtain ⟨L, gatT, Gx, Gy, Kc, X, cX, ex⟩ := O
    obtain ⟨lev, th, th_io, cmp, lat, tw, ker, ep_def, ep_tie, kapI_def, fills_all, nu_unserved, idx, kap_def, lam_def, kapR_def, errX, err, nch, nch_tie, xd, p0, rationalRoots_def, amb, amb0, fdef, duStar_def, Dstar_def, gauge, gauge_def⟩ := ex
    obtain ⟨isOver, forced, Wt, pin, coh, vol, col, what₂, rx, hlev, herrX, n, nx, sx, ker0, ker_eq, kT, div, thT, obj, ox, real, dsig_eq, gaugeG, good⟩ := x
    simp only [ofObj, extraObj] at ker_eq
    cases ker_eq
    obtain ⟨t1, s1, o1, e1, a1, p1⟩ := TC.kerEntTied_true_ent w.I w.ok w.pins w.l Z L col.Gt Gx Gy Kc X cX
      ⟨lev, th, th_io, col.cmp, lat, w.tw Z, ker, ep_def, ep_tie, kapI_def, fills_all, nu_unserved, idx, kap_def, lam_def, kapR_def, errX, err, nch,
        nch_tie, xd, p0, rationalRoots_def, amb, amb0, fdef, duStar_def, Dstar_def, gauge, gauge_def⟩ kT.O kT.E div.Qp kT.std
      kT.unf kT.ok kT.served
    exact ⟨t1, (StdModel.stdKer_iff w.I w.l Z t1).2 s1, o1, heq_of_eq e1, a1, p1⟩
  obtain ⟨t, ht⟩ := hK
  let _ : Algebra q.x.what₂.r.z.core.Q.c.F (q.w.D q.Z).what₂.LL := q.x.what₂.r.z.alg
  obtain ⟨Dc, Sp₀, Zsc₀, C₀, -⟩ := _root_.GlobalTheory.Mem.R3.SelC.square_integrable_columns_of_witnesses _ K q t ht ⟨q.x.rx⟩
  obtain ⟨kap, lam, err, hP, hH, -, -, -, Y', Z', htup, -, hjA, -⟩ := GlobalTheory.Mem.R3.reFace_scalars_errors_readings _ _ _ _ _ _ _
    q.x.what₂.r.z.R q.x.what₂.r.z.F q.x.what₂.r.z.cG q.O.ex.p0 q.x.what₂.r.Y q.x.what₂.r.Z Dc Sp₀ q.x.what₂.r.z.F.Zsc (fun _ => Or.inl rfl)
    q.x.what₂.r.z.pins q.x.what₂.r.intersectionNumber_baseChange
  obtain ⟨C'⟩ := GlobalTheory.Mem.R3.readC_reFace_updS q.x.what₂.r.z.R q.x.what₂.r.z.F q.O.ex.p0
    Dc Sp₀ Sp₀ Zsc₀ q.x.what₂.r.z.F.Zsc kap lam err C₀ Y' htup hjA
  obtain ⟨nb⟩ := hN _ _ _ _ _ _ _ _ _ _ _ _ _ q.x.nx.2
  have hBk : BkLaw (q.w.D q.Z) := nb.2.down
  have hRat := GlobalTheory.Mem.R3.divisionPairing_rational_on_rationalPoints hPr (q.w.st q.Z).toD7 _ _ _ _ _ _ _ _ _ _ Y' Z' C' hP hH
  exact GlobalTheory.Mem.R3.zeTied_of_read hPr (q.w.st q.Z).toD7 _ _ _ _ _ _ _ _ _ _ Y' Z' C' hP hH (hBk hRat)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ZeUPrmRNEbStatement
alias GlobalTheory.T.zeta_uniform_of_extension' :=
  GlobalTheory.Mem.Top.Bl.ze_u_prm_of_extension_with_law
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExBLIsLinkedPrmR
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
noncomputable section
namespace GlobalTheory.Mem.Top.Bl
theorem exBL_isLinked_prmR_alt : GlobalTheory.Published.GreenCuspidal → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.WeberRayFieldSt → GlobalTheory.NT.RayField → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (Γ : GeoP) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), p = _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none Γ → (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) → PositionMv p.s → (GlobalTheory.Fc.EvP fun _ K => ∀ q : WPt p.s K, GlobalTheory.CuspMult.MultEq q.x.what₂.r.z.R.toRealDat) → GlobalTheory.Fc.ExBL KPx (IsBuiltE p.s) (IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) := by
  intro hG hCov hHM hCW hW hD hH hC hA hWb hRF hL N Γ p hp hN hS hM
  have hz := _root_.GlobalTheory.T.zeta_uniform_of_extension' ⟨hCov, hHM, hCW, hH, hC⟩ hL N SExt.none Γ hN
  subst hp
  refine _root_.GlobalTheory.T.eta_size_recursion_alt hA hWb hRF hL _ ?_ ?_ ?_
  · exact witExE_of_witMv _ (GlobalTheory.T.witnesses_pass_along_set_division _ hS)
  · exact GlobalTheory.Fc.EvP.of_all fun _ K _ q => hz K q
  · exact _root_.GlobalTheory.T.local_langlands_prm_reduction_alt hG hCov hHM hCW hW hD hH hC hA hRF hL N Γ _ rfl hN hM
end GlobalTheory.Mem.Top.Bl
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExBLIsLinkedPrmRStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometric_parameter_uniform_alt : GlobalTheory.Published.GreenCuspidal → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.WeberRayFieldSt → GlobalTheory.NT.RayField → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (Γ : GeoP) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), p = _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none Γ → (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) → PositionMv p.s → (GlobalTheory.Fc.EvP fun _ K => ∀ q : WPt p.s K, GlobalTheory.CuspMult.MultEq q.x.what₂.r.z.R.toRealDat) → GlobalTheory.Fc.ExBL KPx (IsBuiltE p.s) (IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) := by
  first | exact @_root_.GlobalTheory.Mem.Top.Bl.exBL_isLinked_prmR_alt | exact _root_.GlobalTheory.Mem.Top.Bl.exBL_isLinked_prmR_alt | (intros; apply _root_.GlobalTheory.Mem.Top.Bl.exBL_isLinked_prmR_alt <;> assumption)
end
end
