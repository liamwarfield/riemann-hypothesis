module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReferenceTupleFamilyPeriodEqPeriod
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TypeDataUnitShiftRelation
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLatticeFramePinsFiniteIntegralLaws
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.QuadraticFamilyLevelIdentity
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KernelPartLawsOfColumnPins
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLastPeriodClassDataOfLastStep
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRowFormReadingLevelFormLastSpace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainIdealIndexProduct
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Imports
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsBis
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyChars

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ClsPinDOfFamCol
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ClsPinDOfFamCol
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.MiS GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.AdForm
set_option maxHeartbeats 2000000 in
theorem clsPinD_of_famCol_of_trueW : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : (I.rec7 l Z).what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.ValidRealPackage W → _root_.GlobalTheory.AdForm.TwStdAlt W → _root_.GlobalTheory.Fam.LeadingReadAt W u f.j f.g.bT → f.RowOK → _root_.GlobalTheory.AdForm.FamilyColumnCondition f → ClsPinD f.t := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W u f hTW hStd hTop hRow hCol
  obtain ⟨c₀, hX, hcol⟩ := hCol
  have hOk := hTW.ok
  have hPins := hTW.pins.some
  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_nonzero_jetScale_trueColumns I hOk hPins l Z (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ hX.std hX.inf
  obtain ⟨J, hJ⟩ := GlobalTheory.T.exists_translates_of_values_frames I hOk hPins l Z (_root_.GlobalTheory.Fam.pk_z W) hX.inf f.j
  have hemb : IsEmbTop (D := I.rec7 l Z) (TC.z0 X u) ((f.g.oT B.R.m rfl).emb.comp (MonoidHom.inl _ _)) := by
    obtain ⟨UT, ε, hP⟩ := (hcol W.P.A3.A.μ0).2
    exact hP.emb
  refine ⟨realOf u (_root_.GlobalTheory.Fam.pk_z W) f.g s J, GlobalTheory.T.trueColumns_realData_spec I hOk hPins l Z u (_root_.GlobalTheory.Fam.pk_z W) f.g c₀ s J hX f.j hTop.1 hJ hemb, fun t => ⟨?_, ?_⟩⟩
  · obtain ⟨⟨Ch₀, A, ι, w, hA⟩, -⟩ := hcol t
    exact ⟨_, GlobalTheory.T.kernelPart_laws_of_columnPins I hOk hPins l Z u (_root_.GlobalTheory.Fam.pk_z W) f.g c₀ s J hX hs hRow.x (_root_.GlobalTheory.Fam.complexLevelStructure W) t (f.row t) (W.P.I.tup t) (f.col t) _ Ch₀ A ι w hA⟩
  · obtain ⟨⟨Ch₀, A, ι, w, hA⟩, UT, ε, hTL⟩ := hcol t
    have hstdC := hTW.std.some
    have key : ∀ a : (I.rec7 l Z).what₂.Tup, _root_.GlobalTheory.Fam.LevelCondition W u a f.g.bT (levS _ (_root_.GlobalTheory.Fam.pk_z W).βX (datXP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) t)) (levChi _ (_root_.GlobalTheory.Fam.pk_z W).βX (datXP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) t)) →
        ∃ (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (D := I.rec7 l Z) (u := u) (I.fm l u a) bad)
          (eW : (I.per l u a).Wrow ≃ₗ[ℂ] ((I.fm l u a).clsP → FrP (I.rec7 l Z) → ℂ)),
          I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) ∧
          (∀ z c (y : FrP (I.rec7 l Z)) y', y'.1 = y.1 → eW z c y = z c y') ∧
          LevG K f.g.bT (levS _ (_root_.GlobalTheory.Fam.pk_z W).βX (datXP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) t)) (levChi _ (_root_.GlobalTheory.Fam.pk_z W).βX (datXP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) t)) ∧
          ∀ (ψ : ColT I l u a B.R.m) (F : CXP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) t), ∃ G', ReadsG K eW f.j f.g.bT G' F.1 ∧
            _root_.GlobalTheory.Fam.tailCoefficient W u f.j f.g.bT a ψ F.1 = (I.per l u a).Ptil ψ G' := by
      intro a hL
      by_cases h0 : a = I.mu0
      · subst h0
        have hon := GlobalTheory.T.exists_rowForm_reading_levelForm_lastSpace I hOk hPins l Z u (_root_.GlobalTheory.Fam.pk_z W) f.g c₀ hX f.j hTop.1 (_root_.GlobalTheory.Fam.complexLevelStructure W) t I.mu0 _ (W.R.T.cols.forms u).clsP.toG
          (W.R.T.cols.forms u).valP.eW (hstdC u).what₂ (hstdC u).eW hTop.2.1 (hL.1 rfl)
        refine ⟨_, (W.R.T.cols.forms u).clsP.toG, (W.R.T.cols.forms u).valP.eW, (hstdC u).what₂, (hstdC u).eW, hL.1 rfl, ?_⟩
        intro ψ F
        have hex : ∃ G, _root_.GlobalTheory.Fam.ReadsCoefficients W u f.j f.g.bT I.mu0 G F.1 := by
          obtain ⟨G', hG'⟩ := hon F
          refine ⟨(I.rec7 l Z).eMt u G', fun h => ?_, fun h => absurd rfl h⟩
          have e : ((I.rec7 l Z).eMt u).symm (h ▸ ((I.rec7 l Z).eMt u) G') = G' := ((I.rec7 l Z).eMt u).symm_apply_apply G'
          first
            | (rw [e]; exact hG')
            | exact e ▸ hG'
            | exact (congrArg (fun G => ReadsG (W.R.T.cols.forms u).clsP.toG (W.R.T.cols.forms u).valP.eW f.j f.g.bT G F.1) e).mpr hG'
        refine ⟨_, hex.choose_spec.1 rfl, ?_⟩
        unfold _root_.GlobalTheory.Fam.tailCoefficient
        rw [dite_eq_left hex]
        split
        · rfl
        · next h => exact absurd rfl h
      · obtain ⟨l0, t', e, hh, hst⟩ := hStd
        obtain ⟨-, -, hP⟩ := hst
        cases ex
        dsimp only at e
        subst e
        have hh' := eq_of_heq hh
        subst hh'
        have hon := GlobalTheory.T.exists_rowForm_reading_levelForm_lastSpace I hOk hPins l Z u (_root_.GlobalTheory.Fam.pk_z W) f.g c₀ hX f.j hTop.1 (_root_.GlobalTheory.Fam.complexLevelStructure W) t a _ (W.R.T.tw.pt.cls u a h0)
          (W.R.T.tw.pt.val u a h0).eW (hP.what₂ u a h0) (hP.eW u a h0) hTop.2.1 (hL.2 h0)
        refine ⟨_, W.R.T.tw.pt.cls u a h0, (W.R.T.tw.pt.val u a h0).eW, hP.what₂ u a h0, hP.eW u a h0, hL.2 h0, ?_⟩
        intro ψ F
        have hex : ∃ G, _root_.GlobalTheory.Fam.ReadsCoefficients W u f.j f.g.bT a G F.1 := by
          obtain ⟨G', hG'⟩ := hon F
          refine ⟨(I.rec7 l Z).eMtTw u a G', fun h => absurd h h0, fun h => ?_⟩
          have e := ((I.rec7 l Z).eMtTw u a).symm_apply_apply G'
          first
            | (rw [e]; exact hG')
            | exact e ▸ hG'
            | exact (congrArg (fun G => ReadsG (W.R.T.tw.pt.cls u a h0) (W.R.T.tw.pt.val u a h0).eW f.j f.g.bT G F.1) e).mpr hG'
        refine ⟨_, hex.choose_spec.2 h0, ?_⟩
        unfold _root_.GlobalTheory.Fam.tailCoefficient
        rw [dite_eq_left hex]
        split
        · next h => exact absurd h h0
        · rfl
    obtain ⟨bad, K, eW, h1, h2, h3, h4⟩ := key _ (hTop.2.2 t).1
    exact GlobalTheory.T.exists_lastPeriod_classData_of_lastStep I hOk hPins l Z u (_root_.GlobalTheory.Fam.pk_z W) f.g c₀ s J hX f.j hTop.1 hJ (_root_.GlobalTheory.Fam.complexLevelStructure W) t (f.row t) (W.P.I.tup t) (f.col t) _ Ch₀ A ι w hA UT ε hTL bad K eW h1 h2 hTop.2.1 h3 h4
end GlobalTheory.AdForm
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ClsPinDOfFamColStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms
open NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.MiS GlobalTheory.AdForm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cls_pin_d_of_true_family : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : (I.rec7 l Z).what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.ValidRealPackage W → _root_.GlobalTheory.AdForm.TwStdAlt W → _root_.GlobalTheory.Fam.LeadingReadAt W u f.j f.g.bT → f.RowOK → _root_.GlobalTheory.AdForm.FamilyColumnCondition f → ClsPinD f.t := by
  first | exact @_root_.GlobalTheory.AdForm.clsPinD_of_famCol_of_trueW | exact _root_.GlobalTheory.AdForm.clsPinD_of_famCol_of_trueW | (intros; apply _root_.GlobalTheory.AdForm.clsPinD_of_famCol_of_trueW <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OffLev
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OffLev
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
namespace GlobalTheory.RowLevel
theorem off_lev_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ v : VCom f.c, v.Is → _root_.GlobalTheory.Fam.CommutingVectorTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), GPin G → _root_.GlobalTheory.Fam.LocalGroupReading f G pl → ∀ t (w : VTup (f.t t)) (F : GlobalTheory.QPl.QFam v (f.t t)), (f.t t).Is → F.Pins w → _root_.GlobalTheory.Fam.QLevAlt f F → (∀ i, (G i).Chars (f.t t)) → ∀ j, j < D.R.m → ∀ κ, GlobalTheory.FinPl.InK _ (v.N j) (offP v w) κ → (f.g.b j)⁻¹ * κ * f.g.b j ∈ levS _ ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)) ∧ levChi _ ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)) ((f.g.b j)⁻¹ * κ * f.g.b j) = 1 := by
  intro D L hT Gi Gl Kc Yd cX ex W u f hP hR v hv hV n G pl hGP hGR t w F ht hFP hQL hch j hj κ hκ
  have hlev := W.Q.charW.base.lev
  refine conj_mem_off (hlev.βY j hj) (hv.sd j hj) _ ?_ (hV.b j ▸ hv.b j)
    (fun p hp => hV.moves j hj _ fun q hq => hq ▸ hp.1) hκ
  rintro PP (h | h) ho
  · exact ho.1 ((hV.gP _).2 ⟨PP, h, rfl⟩)
  · obtain ⟨e, he⟩ := hQL.places
    obtain ⟨i, hi⟩ := e.surjective ⟨PP, h⟩
    refine ho.2 ((hFP.places _).2 ⟨i, ?_⟩)
    rw [(he i).2, hi]
theorem top_lev_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ v : VCom f.c, v.Is → _root_.GlobalTheory.Fam.CommutingVectorTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), GPin G → _root_.GlobalTheory.Fam.LocalGroupReading f G pl → ∀ t (w : VTup (f.t t)) (F : GlobalTheory.QPl.QFam v (f.t t)), (f.t t).Is → F.Pins w → _root_.GlobalTheory.Fam.QLevAlt f F → (∀ i, (G i).Chars (f.t t)) → ∀ κ, GlobalTheory.FinPl.InK f.c.T v.NT (· ∈ v.tP) κ → f.g.bT⁻¹ * κ * f.g.bT ∈ levS _ (_root_.GlobalTheory.Fam.pk_z W).βX (datXP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) t) ∧ levChi _ (_root_.GlobalTheory.Fam.pk_z W).βX (datXP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) t) (f.g.bT⁻¹ * κ * f.g.bT) = 1 := by
  intro D L hT Gi Gl Kc Yd cX ex W u f hP hR v hv hV n G pl hGP hGR t w F ht hFP hQL hch κ hκ
  have hlev := W.Q.charW.base.lev
  refine conj_mem_off hlev.βX hv.sdT _ ?_ (hV.bT.1 ▸ hv.bT) (fun p _ => hV.bT.2 ▸ hV.movesT _) hκ
  rintro PP (h | h) ho
  · exact Finset.disjoint_left.1 hv.disj ((hV.gP _).2 ⟨PP, h, rfl⟩) ho
  · have h1 := (hV.tP _).1 ho
    refine (hlev.Q_off t PP h).2 u ?_
    have h2 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ PP.asIdeal := h1
    rwa [map_natCast] at h2
section Loc
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end Loc
set_option maxHeartbeats 1000000 in
theorem g_lev_alt {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : D.what₂.Word} {f : _root_.GlobalTheory.Fam.FamilyCharacter W u}
    {v : VCom f.c} (hv : v.Is) (hV : _root_.GlobalTheory.Fam.CommutingVectorTie f v) {n : ℕ} {G : Fin n → GLoc v} {pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg} (hGP : GPin G)
    (hGR : _root_.GlobalTheory.Fam.LocalGroupReading f G pl) (t : W.P.T) (j : ℕ) (hj : j < D.R.m) (k : GA D (Yc D j)) (hk : k ∈ v.JG j) (a : ℂ) (ha : GLam G j k a) :
    (f.g.b j)⁻¹ * k * f.g.b j ∈ levS _ ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)) ∧
      levChi _ ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)) ((f.g.b j)⁻¹ * k * f.g.b j) = a := by
  have hlev := W.Q.charW.base.lev
  have hΛ := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hlev.βY j hj)
  obtain ⟨c0, hfr, -⟩ := hlev.βY j hj
  obtain ⟨hkg, hkJ⟩ := (hGP.lev j hj k).1 hk
  obtain ⟨hkf, hkS⟩ := (GlobalTheory.FinPl.KOpen.mem_grpAt_iff _ _ k).1 hkg
  obtain ⟨c, hc, x, hxM, rfl⟩ := ha
  have hb : f.g.b j ∈ GfC (Yc D j) := hV.b j ▸ hv.b j
  choose e he hmv using fun i => hGR.frame i j (c i) (hc i)
  choose π h1 h2 h3 h4 using fun i => GlobalTheory.LocMod.LevBack.exists_chart (G i).q (hGR.idem i).1
  have hSt : Lev.finE (Yc D j) ((f.g.b j)⁻¹ * k * f.g.b j) ∈ St ((_root_.GlobalTheory.Fam.pk_z W).βY j) := by
    obtain ⟨h, hloc, hprod⟩ := GlobalTheory.LevelCut.prod_local_parts D f.c v n G hGP j k hkg
    rw [hprod, conj_list_prod, map_list_prod]
    refine Subgroup.list_prod_mem _ fun y hy => ?_
    simp only [List.mem_map] at hy
    obtain ⟨_, ⟨i, -, rfl⟩, rfl⟩ := hy
    obtain ⟨xk, hM, hL⟩ := hloc i (c i) (hc i)
    have hJ := hkJ i _ _ _ hM
    have hγ := mat_frame (G i).q (π i) (h1 i) ((G i).FY j (c i) (hc i))
      (typeFrame (G i).S.ϖ (stdOrd (Fin D.R.k) (Fin D.R.t) j (c i) (hc i))) (e i) (hmv i) xk hL.2
    obtain ⟨hyK, -⟩ := (GlobalTheory.SymChain.pattern_iter _ _ _ (G i).S (Fin D.R.t) j
      ((typeFrame (G i).S.ϖ (stdOrd (Fin D.R.k) (Fin D.R.t) j (c i) (hc i))).conj.symm xk)).1 hJ
    obtain ⟨Y, hY, -⟩ := GlobalTheory.LocMod.LevBack.exists_int (G i).q (π i) (h2 i) (Yc D j) hΛ hfr (t := f.g.b j) hL.1 (by
      erw [hγ]
      rw [mem_KO, ← map_inv]
      rw [mem_KO] at hyK
      exact ⟨fun _ _ => hyK.1 _ _, fun _ _ => hyK.2 _ _⟩)
    exact ⟨Y, hY⟩
  have hQ : ∀ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t, redFn ((_root_.GlobalTheory.Fam.pk_z W).βY j) PP (Lev.finE (Yc D j) ((f.g.b j)⁻¹ * k * f.g.b j)) = 1 := fun PP hPP => by
    refine GlobalTheory.ChainOnto.RedOne.redFn_eq_one D _ _ _ PP hSt ?_
    have hn : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∉ v.gP := fun hm => by
      obtain ⟨PP', hP', e'⟩ := (hV.gP _).1 hm
      obtain ⟨i, hi⟩ := (hlev.Pg PP').1 hP'
      obtain ⟨⟨q, hq, hcard, -, hqg⟩, -⟩ := hlev.Q_pl t PP hPP
      have g1 := Formalism.IndefR.Fin.g_mem_of_div _ hi
      have g2 : ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP')).asIdeal := by
        change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ PP'.asIdeal
        rwa [map_natCast]
      rw [← e'] at g2
      have g3 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ PP.asIdeal := g2
      rw [map_natCast] at g3
      exact Formalism.IndefR.Fin.not_two_primes PP.isPrime.ne_top (D.host.g_prime i) hq (fun h => hqg i h.symm) g3
        (Formalism.IndefR.Fin.char_mem hq hcard)
    rw [map_mul, map_mul, hkS _ hn, mul_one, ← map_mul, inv_mul_cancel, map_one]
  obtain ⟨Y, hY⟩ := id hSt
  have hYv : Formalism.UG.bc (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype Y =
      ((_root_.GlobalTheory.Fam.pk_z W).βY j)⁻¹ * Lev.finE (Yc D j) ((f.g.b j)⁻¹ * k * f.g.b j) * (_root_.GlobalTheory.Fam.pk_z W).βY j := by
    rw [← hY]
    change _ = ((_root_.GlobalTheory.Fam.pk_z W).βY j)⁻¹ * ((_root_.GlobalTheory.Fam.pk_z W).βY j * Formalism.UG.bc (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype Y * ((_root_.GlobalTheory.Fam.pk_z W).βY j)⁻¹) * (_root_.GlobalTheory.Fam.pk_z W).βY j
    group
  have hall := fun i => by
    haveI : Nontrivial (kP (pl i).1) := Ideal.Quotient.nontrivial_iff.2 (pl i).1.isPrime.ne_top
    have hs := (G i).hs
    have hγ := mat_frame (G i).q (π i) (h1 i) ((G i).FY j (c i) (hc i))
      (typeFrame (G i).S.ϖ (stdOrd (Fin D.R.k) (Fin D.R.t) j (c i) (hc i))) (e i) (hmv i) (x i).1 (hxM i)
    exact red_lam (G i).S (r := D.R.r) (by unfold Ranks.r; omega) (r_le_Y j) (he i) (resS D.host.F (pl i).1)
      ((π i).comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (h3 i) (h4 i) (fun c => (_root_.GlobalTheory.Fam.pk_z W).chi c (pl i).1)
      (fun c hc z y x' hy hx => chi_eq_mu (_root_.GlobalTheory.Fam.pk_z W).toLevCh hlev (G i).q (pl i).2 (hGR.idem i).1 (π i) (h1 i) (h3 i) (h4 i) c
        (by omega) _ (hGR.mu i (c + 1) (by omega) (by omega)) ((G i).S.tame _) z y x' hy hx) Y
      ⟨(typeFrame (G i).S.ϖ (stdOrd (Fin D.R.k) (Fin D.R.t) j (c i) (hc i))).conj.symm (x i).1, (x i).2⟩ (fun a b => by
        have e1 := congrArg (fun g : GL _ _ => g.val (e i a) (e i b)) hγ
        simp only [reGL_val, submatrix_apply, Equiv.symm_apply_apply] at e1
        refine Eq.trans ?_ e1
        exact congrArg (π i) (congrArg (fun g : GL _ _ => g.val (e i a) (e i b)) hYv))
  choose hbt x₀ hred hlam using hall
  have hr : ∀ PP, redFn ((_root_.GlobalTheory.Fam.pk_z W).βY j) PP (Lev.finE (Yc D j) ((f.g.b j)⁻¹ * k * f.g.b j)) = Formalism.UG.bc (resS D.host.F PP) Y :=
    fun PP => by rw [← hY, redFn_frGL]
  obtain ⟨g, hg⟩ : ∃ g : ∀ PP : (_root_.GlobalTheory.Fam.pk_z W).Pg, GL (Fin D.R.r) (kP PP.1),
    ∀ PP, g PP = upperLeftBlock (r_le_Y j) (Formalism.UG.bc (resS D.host.F PP.1) Y) := ⟨_, fun _ => rfl⟩
  have hrT : rTup ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)) (Lev.finE (Yc D j) ((f.g.b j)⁻¹ * k * f.g.b j)) = g := by
    funext PP
    exact (congrArg (upperLeftBlock (r_le_Y j)) (hr PP.1)).trans (hg PP).symm
  have hR : ∀ i (a b : Fin D.R.k ⊕ Fin ((G i).s + 1)) (a' b' : Fin D.R.r),
      a'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ a → b'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ b → ∀ z : 𝓞 D.host.E,
        Ideal.Quotient.mk (pl i).1.asIdeal z = (g (pl i)).val a' b' →
        valuation (G i).k ((x₀ i : GL (Fin D.R.k ⊕ Fin ((G i).s + 1)) (G i).k).val a b - (ofSplit (G i).q).pr (z : D.host.E)) < 1 := by
    intro i a b a' b' ha hb z hz
    rw [hg] at hz
    have := hred i a b a' b' ha hb (oToS D.host.F D.host.E z) ((resS_oToS (pl i).1 z).trans hz)
    rwa [show ((π i).comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (oToS D.host.F D.host.E z) =
      (ofSplit (G i).q).pr (z : D.host.E) from h1 i (incA D (z : D.host.E))] at this
  have hgH : g ∈ (_root_.GlobalTheory.Fam.complexLevelStructure W).H := (hGR.lev g).1.2 fun i => ⟨x₀ i, hR i⟩
  have hchi := (hGR.lev g).2 hgH x₀ hR
  refine ⟨⟨(GfC _).mul_mem ((GfC _).mul_mem ((GfC _).inv_mem hb) hkf) hb, ?_⟩, ?_⟩
  · change Lev.finE (Yc D j) _ ∈ Formalism.L2.DIV.lev _ _ _ _
    refine ⟨mem_parLev.2 ⟨GlobalTheory.LevSplit.finE_mem_UA _ _, hSt, fun PP hPP => ?_, fun PP hPP => ?_⟩, ?_⟩
    · obtain ⟨i, hi⟩ := pl.surjective ⟨PP, hPP⟩
      obtain rfl : (pl i).1 = PP := congrArg Subtype.val hi
      rw [hr]
      exact hbt i
    · rw [hQ PP hPP]; exact one_mem _
    · rw [hrT]; exact hgH
  · unfold Lev.levChi levFn
    rw [hrT]
    have e1 : ext1 ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)).P.H ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)).P.chi g = ∏ i, (G i).S.P.lam (x₀ i) :=
      (extendOne_of_mem (P := (_root_.GlobalTheory.Fam.complexLevelStructure W).H) (_root_.GlobalTheory.Fam.complexLevelStructure W).chi hgH).trans hchi
    have e2 : ∏ PP ∈ ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)).Q, ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)).xq PP (dBlk (blk2 ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)).r) 1
        (redFn ((_root_.GlobalTheory.Fam.pk_z W).βY j) PP (Lev.finE (Yc D j) ((f.g.b j)⁻¹ * k * f.g.b j)))) = 1 :=
      Finset.prod_eq_one fun PP hPP => by rw [hQ PP hPP, dBlk, blockDiagonalExtendByOnePrimeField_one, map_one]
    have e3 : ∏ PP ∈ ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)).Pg, ∏ c ∈ Finset.range ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)).s,
        ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)).cg (c + 1) PP (dBlk (blkOf ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)).r ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)).t) (c + 1)
          (redFn ((_root_.GlobalTheory.Fam.pk_z W).βY j) PP (Lev.finE (Yc D j) ((f.g.b j)⁻¹ * k * f.g.b j)))) =
        ∏ i, ∏ c ∈ Finset.range j, (_root_.GlobalTheory.Fam.pk_z W).chi (c + 1) (pl i).1
          (dBlk (blkOf D.R.r D.R.t) (c + 1) (Formalism.UG.bc (resS D.host.F (pl i).1) Y)) := by
      simp only [hr]
      rw [← Finset.prod_coe_sort]
      exact (Fintype.prod_equiv pl _ _ fun i => rfl).symm
    rw [e1, e2, e3, mul_one, ← Finset.prod_mul_distrib, Units.coe_prod]
    exact Finset.prod_congr rfl fun i _ => congrArg Units.val (hlam i).symm
theorem main_alt_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ v : VCom f.c, v.Is → _root_.GlobalTheory.Fam.CommutingVectorTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), GPin G → _root_.GlobalTheory.Fam.LocalGroupReading f G pl → ∀ t (w : VTup (f.t t)) (F : GlobalTheory.QPl.QFam v (f.t t)), (f.t t).Is → F.Pins w → _root_.GlobalTheory.Fam.QLevAlt f F → (∀ i, (G i).Chars (f.t t)) → (∀ j, j < D.R.m → ∀ (X : (f.t t).CC j) x, ∀ a ∈ GinfC _, (∀ i, (F.Q i).Typed j (rTrans (a * v.b j) (X.1 x))) ∧ ∀ κ, GlobalTheory.FinPl.InK _ (v.N j) (offP v w) κ → rTrans κ (rTrans (a * v.b j) (X.1 x)) = rTrans (a * v.b j) (X.1 x)) ∧ (∀ j, j + 1 < D.R.m → ∀ k ∈ v.JG (j + 1), ∃ a : ℂ, a ≠ 0 ∧ (∀ g, GlobalTheory.FinPl.Vac f.c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ v.gP) g → (f.t t).om j (1, k) (comb f.c.ψ _ _ (v.eG j) g) = a⁻¹ • comb f.c.ψ _ _ (v.eG j) g) ∧ (j + 1 + 1 < D.R.m → ∀ g, GlobalTheory.FinPl.Vac f.c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (· ∈ v.gP) g → (f.t t).om (j + 1) (k, 1) (comb f.c.ψ _ _ (v.eG (j + 1)) g) = a • comb f.c.ψ _ _ (v.eG (j + 1)) g) ∧ ∀ (X : (f.t t).CC (j + 1)) x, rTrans k (rTrans (v.b (j + 1)) (X.1 x)) = a • rTrans (v.b (j + 1)) (X.1 x)) ∧ TopSph (t := f.t t) v := by
  intro D L hT Gi Gl Kc Yd cX ex W u f hP hR v hv hV n G pl hGP hGR t w F ht hFP hQL hch
  have hθ : IsInfFam f.c.θ := W.Q.charW.base.models.inf
  have hc : IsStdChar D f.c.ψ (-1) := W.Q.stdChar
  have hGLv := fun j (hj : j + 1 < D.R.m) k hk a ha => _root_.GlobalTheory.RowLevel.g_lev_alt hv hV hGP hGR t (j + 1) hj k hk a ha
  refine ⟨fun j hj X x a ha => ⟨fun i => ?_, fun κ hκ => ?_⟩, fun j hj k hk => ?_, fun X x κ hκ => ?_⟩
  · intro d h y
    have hKO := (F.Q i).le j d h y.2
    have hm := (hQL.mid i j d h hj y.1 hKO)
    have hgf : (F.Q i).gl j d h y.1 ∈ GfC _ :=
      GlobalTheory.WeilProduct.mem_GfC_of_suppAt (F.Q i).q.split ((F.Q i).gl_loc j d h y.1).1
    rw [hV.b j, rTrans_lev hθ _ _ _ _ X.2 x ha hgf ((hm.1).2 y.2), hm.2 y.2]
  · have hκf : κ ∈ GfC _ := GlobalTheory.LevelCut.mem_GfC_of_grpAt _ _ κ hκ.1
    have ho := _root_.GlobalTheory.RowLevel.off_lev_alt D L hT Gi Gl Kc Yd cX ex W u f hP hR v hv hV n G pl hGP hGR t w F ht hFP hQL hch j hj κ hκ
    rw [hV.b j, rTrans_lev hθ _ _ _ _ X.2 x ha hκf ho.1, ho.2, one_smul]
  · obtain ⟨r, hr⟩ := D.R.m_even
    have third : ∀ (X : (f.t t).CC (j + 1)) x (a : ℂ), GLam G (j + 1) k a →
        rTrans k (rTrans (v.b (j + 1)) (X.1 x)) = a • rTrans (v.b (j + 1)) (X.1 x) := by
      intro X x a hga
      have hkf : k ∈ GfC _ := GlobalTheory.LevelCut.mem_GfC_of_grpAt _ _ k ((hv.JG (j + 1) hj).1 hk)
      have ho := hGLv j hj k hk a hga
      rw [hV.b (j + 1), rightTranslate_level_conj_acts_by_character_finite hθ _ _ _ _ X.2 x hkf ho.1, ho.2]
    have uniq : ∀ a a', GLam G (j + 1) k a → GLam G (j + 1) k a' → a = a' := fun a a' h h' =>
      (hGLv j hj k hk a h).2.symm.trans (hGLv j hj k hk a' h').2
    rcases Nat.even_or_odd j with ⟨q, hq⟩ | ⟨q, hq⟩
    · obtain ⟨σ, hσ⟩ : ∃ σ, j + 2 * σ + 2 = D.R.m := ⟨(D.R.m - j - 2) / 2, by omega⟩
      have LL := GlobalTheory.RowLevel.Std.lift_laws D f.c v n G hc hv hGP (f.t t) ht hch j σ hσ
      obtain ⟨a, ha0, hga, hlaw⟩ := LL.1 k hk
      refine ⟨a, ha0, hlaw, fun hj2 => ?_, fun X x => third X x a hga⟩
      obtain ⟨a', -, hga', hlaw'⟩ := (LL.2.2 (by omega)).2 k hk
      rw [uniq a a' hga hga']
      exact hlaw'
    · obtain ⟨j₀, rfl⟩ : ∃ j₀, j = j₀ + 1 := ⟨2 * q, by omega⟩
      obtain ⟨σ, hσ⟩ : ∃ σ, j₀ + 2 * (σ + 1) + 2 = D.R.m := ⟨(D.R.m - j₀ - 4) / 2, by omega⟩
      have LL := GlobalTheory.RowLevel.Std.lift_laws D f.c v n G hc hv hGP (f.t t) ht hch j₀ (σ + 1) hσ
      obtain ⟨a, ha0, hga, hlaw⟩ := (LL.2.2 (by omega)).1 k hk
      refine ⟨a, ha0, hlaw, fun hj2 => ?_, fun X x => third X x a hga⟩
      have LL' := GlobalTheory.RowLevel.Std.lift_laws D f.c v n G hc hv hGP (f.t t) ht hch (j₀ + 1 + 1) σ (by omega)
      obtain ⟨a', -, hga', hlaw'⟩ := LL'.2.1 k hk
      rw [uniq a a' hga hga']
      exact hlaw'
  · have hκf : κ ∈ GfC _ := GlobalTheory.LevelCut.mem_GfC_of_grpAt _ _ κ hκ.1
    have ho := _root_.GlobalTheory.RowLevel.top_lev_alt D L hT Gi Gl Kc Yd cX ex W u f hP hR v hv hV n G pl hGP hGR t w F ht hFP hQL hch κ hκ
    rw [hV.bT.1, rightTranslate_level_conj_acts_by_character_finite hθ _ _ _ _ X.2 x hκf ho.1, ho.2, one_smul]
end GlobalTheory.RowLevel
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OffLevStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quadratic_family_level_identity_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ v : VCom f.c, v.Is → _root_.GlobalTheory.Fam.CommutingVectorTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), GPin G → _root_.GlobalTheory.Fam.LocalGroupReading f G pl → ∀ t (w : VTup (f.t t)) (F : GlobalTheory.QPl.QFam v (f.t t)), (f.t t).Is → F.Pins w → _root_.GlobalTheory.Fam.QLevAlt f F → (∀ i, (G i).Chars (f.t t)) → (∀ j, j < D.R.m → ∀ (X : (f.t t).CC j) x, ∀ a ∈ GinfC _, (∀ i, (F.Q i).Typed j (rTrans (a * v.b j) (X.1 x))) ∧ ∀ κ, GlobalTheory.FinPl.InK _ (v.N j) (offP v w) κ → rTrans κ (rTrans (a * v.b j) (X.1 x)) = rTrans (a * v.b j) (X.1 x)) ∧ (∀ j, j + 1 < D.R.m → ∀ k ∈ v.JG (j + 1), ∃ a : ℂ, a ≠ 0 ∧ (∀ g, GlobalTheory.FinPl.Vac f.c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ v.gP) g → (f.t t).om j (1, k) (comb f.c.ψ _ _ (v.eG j) g) = a⁻¹ • comb f.c.ψ _ _ (v.eG j) g) ∧ (j + 1 + 1 < D.R.m → ∀ g, GlobalTheory.FinPl.Vac f.c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (· ∈ v.gP) g → (f.t t).om (j + 1) (k, 1) (comb f.c.ψ _ _ (v.eG (j + 1)) g) = a • comb f.c.ψ _ _ (v.eG (j + 1)) g) ∧ ∀ (X : (f.t t).CC (j + 1)) x, rTrans k (rTrans (v.b (j + 1)) (X.1 x)) = a • rTrans (v.b (j + 1)) (X.1 x)) ∧ TopSph (t := f.t t) v := by
  first | exact @_root_.GlobalTheory.RowLevel.main_alt_alt | exact _root_.GlobalTheory.RowLevel.main_alt_alt | (intros; apply _root_.GlobalTheory.RowLevel.main_alt_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CIMulIdx
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CIMulIdx
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
set_option maxHeartbeats 1000000
noncomputable section
namespace GlobalTheory.StepConst
variable {D : D7}
theorem cI_mul_idx_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ v : VCom f.c, v.Is → _root_.GlobalTheory.Fam.CommutingVectorTie f v → ∀ t (w : VTup (f.t t)) (F : GlobalTheory.QPl.QFam v (f.t t)), F.Pins w → _root_.GlobalTheory.Fam.QLevAlt f F → ∀ j, j < D.R.m → (f.t t).cI j * ∏ i, ((F.Q i).idx (j + 1) : ℂ) = (f.t W.P.A3.A.μ0).cI j := by
  intro D L hT Gi Gl Kc Yd cX ex W u f _ hRow v hv hVT t w F hPins hQL j hj
  have hL : (_root_.GlobalTheory.Fam.pk_z W).toLevCh.Is W.P.A3.A.μ0 := W.Q.charW.base.lev
  have hQ0 := base_empty hL
  obtain ⟨pl, hpl⟩ := hQL.places
  have hq : ∀ i, ∀ PP' ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') = (F.Q i).q.v → PP' = (pl i).1 := fun i PP' h e => by
    have e1 := (hpl (pl.symm ⟨PP', h⟩)).2
    rw [Equiv.apply_symm_apply] at e1
    have e2 : pl.symm ⟨PP', h⟩ = i := hPins.inj (e1.trans e)
    rw [← e2, Equiv.apply_symm_apply]
  have hg : ∀ i, ∀ PP' ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') ≠ (F.Q i).q.v := fun i PP' h => by
    rw [(hpl i).2]
    exact under_ne hL t (pl i).2 h
  have hgP : ∀ i, (F.Q i).q.v ∉ v.gP := fun i h => by
    obtain ⟨PP, h1, h2⟩ := (hVT.gP _).1 h
    exact hg i PP h1 h2.symm
  have hP : ∀ PP : Pl D.host.E, PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg ∨ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q W.P.A3.A.μ0 → ¬ (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∈ w.Q := by
    rintro PP (h | h) h'
    · obtain ⟨i, hi⟩ := (hPins.places _).1 h'
      exact hg i PP h hi.symm
    · rw [hQ0] at h
      exact absurd h (Finset.notMem_empty _)
  have key : GlobalTheory.Fam.volLev (_root_.GlobalTheory.Fam.pk_z W) f.g t j * ∏ i, ((F.Q i).idx (j + 1) : ℝ) = GlobalTheory.Fam.volLev (_root_.GlobalTheory.Fam.pk_z W) f.g W.P.A3.A.μ0 j := by
    unfold GlobalTheory.Fam.volLev
    split_ifs with h1
    · generalize j + 1 = J at h1
      have hb : f.g.b J ∈ GfC (Yc D J) := by rw [← hVT.b J]; exact hv.b J
      have hΛ : ((_root_.GlobalTheory.Fam.pk_z W).ΛY J).FG := (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.βY J h1)).1.fg
      have hβ : IsFrame ((_root_.GlobalTheory.Fam.pk_z W).βY J) ((_root_.GlobalTheory.Fam.pk_z W).ΛY J) := (hL.βY J h1).choose_spec.1
      obtain ⟨a1, a2, a3, a4, a5⟩ := moved_level (V := Yc D J) (N := v.N J) (P := (· ∈ w.Q)) hβ hΛ ((_root_.GlobalTheory.Fam.pk_z W).datYt W.P.A3.A.μ0 J (_root_.GlobalTheory.Fam.pk_z W).triv) hP hb
        (hVT.moves J h1 _ fun p hp => by
          obtain ⟨i, rfl⟩ := (hPins.places _).1 hp
          exact hgP i)
      have loc : ∀ i d hd (g : GA D (Yc D J)), finE (Yc D J) ((f.g.b J)⁻¹ * g * f.g.b J) ∈ St ((_root_.GlobalTheory.Fam.pk_z W).βY J) → ∀ x,
          (mt _ g).map (F.Q i).q.pr = ((F.Q i).FY J d hd).β * x.val * ((F.Q i).FY J d hd).γ →
          (redFn ((_root_.GlobalTheory.Fam.pk_z W).βY J) (pl i).1 (finE (Yc D J) ((f.g.b J)⁻¹ * g * f.g.b J)) ∈ blockTri (blk2 D.R.r) ↔
            x ∈ ((F.Q i).T.lev J d hd).J) := fun i d hd g hS x hx => by
        refine red_iff_local (N := v.N J) (F.Q i).q ((F.Q i).FY J d hd) _ hβ hΛ ((_root_.GlobalTheory.Fam.pk_z W).datYt t J (_root_.GlobalTheory.Fam.complexLevelStructure W)) (pl i).2 (hpl i).2
          (hg i) (hq i) hb (hVT.moves J h1 _ fun p hp => hp ▸ hgP i) ((F.Q i).latY J d hd) (fun y hy c hc => ?_) hS hx
        obtain ⟨gl, -, -, hu⟩ := GlobalTheory.LocEmb.exists_gl D _ (F.Q i).q (Yc D J) _ ((F.Q i).FY J d hd)
        have e : c = (F.Q i).gl J d hd y :=
          (hu c y hc.1 hc.2).trans (hu _ y ((F.Q i).gl_loc J d hd y).1 ((F.Q i).gl_loc J d hd y).2).symm
        rw [e]
        exact (hQL.mid i J d hd h1 y hy).1
      have hA := (GlobalTheory.T.volume_seeSaw_tuple_level_eq_spherical_div_index D f.c v (f.t t) w F hPins).1 J h1 (hv.sd J h1) (f.g.μf J) (hRow.meas.μf J) _
        (moved (f.g.b J) (levG (Yc D J) ((_root_.GlobalTheory.Fam.pk_z W).βY J) ((_root_.GlobalTheory.Fam.pk_z W).datYt t J (_root_.GlobalTheory.Fam.pk_z W).triv))) (f.g.b J) hb a1 a2 a3 a4 a5 fun g => by
          refine (mem_moved _ _ g).trans ((mem_levG_iff_base _ _ _ _ _ _ _ _ ((_root_.GlobalTheory.Fam.pk_z W).xiR W.P.A3.A.μ0) hQ0 _).trans
            ((and_congr_right fun h0 => ?_).trans (and_congr_left' (mem_moved _ _ g).symm)))
          have hS := parLev_St (lev_le_parLev h0.2)
          refine ⟨fun H i d hd x hx => (loc i d hd g hS x hx).1 (H _ (pl i).2), fun H PP hPP => ?_⟩
          obtain ⟨i, hi⟩ := pl.surjective ⟨PP, hPP⟩
          have hs := (F.Q i).hs
          have hd : J + ((F.Q i).s + 1 - J) = (F.Q i).s + 1 := by omega
          obtain ⟨x, hx⟩ := exists_mat (F.Q i).q ((F.Q i).FY J _ hd) g
          have := (loc i _ hd g hS x hx).2 (H i _ hd x hx)
          rw [hi] at this
          exact this
      have e1 := moved_set (f.g.b J) (levG (Yc D J) ((_root_.GlobalTheory.Fam.pk_z W).βY J) ((_root_.GlobalTheory.Fam.pk_z W).datYt t J (_root_.GlobalTheory.Fam.pk_z W).triv))
      have e2 := moved_set (f.g.b J) (levG (Yc D J) ((_root_.GlobalTheory.Fam.pk_z W).βY J) ((_root_.GlobalTheory.Fam.pk_z W).datYt W.P.A3.A.μ0 J (_root_.GlobalTheory.Fam.pk_z W).triv))
      rw [e1, e2] at hA
      exact hA
    · have hjm : j + 1 = D.R.m := by omega
      rw [hjm]
      have hb : f.g.bT ∈ GfC D.sp.X' := by rw [← hVT.bT.1]; exact hv.bT
      have hΛ : (_root_.GlobalTheory.Fam.pk_z W).ΛX.FG := (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ hL.βX).1.fg
      have hβ : IsFrame (_root_.GlobalTheory.Fam.pk_z W).βX (_root_.GlobalTheory.Fam.pk_z W).ΛX := hL.βX.choose_spec.1
      have hm : ∀ P, GlobalTheory.FinPl.Moves D.sp.X' f.g.bT (_root_.GlobalTheory.Fam.pk_z W).ΛX v.NT P := fun P => by
        rw [hVT.bT.2]
        exact hVT.movesT P
      obtain ⟨a1, a2, a3, a4, a5⟩ := moved_level (V := D.sp.X') (N := v.NT) (P := (· ∈ w.Q)) hβ hΛ ((_root_.GlobalTheory.Fam.pk_z W).datXt W.P.A3.A.μ0) hP hb (hm _)
      have loc : ∀ i (g : GA D D.sp.X'), finE D.sp.X' (f.g.bT⁻¹ * g * f.g.bT) ∈ St (_root_.GlobalTheory.Fam.pk_z W).βX → ∀ x : GL (F.Q i).Z (F.Q i).k,
          (mt _ g).map (F.Q i).q.pr = (F.Q i).FT.β * x.val * (F.Q i).FT.γ →
          (redFn (_root_.GlobalTheory.Fam.pk_z W).βX (pl i).1 (finE D.sp.X' (f.g.bT⁻¹ * g * f.g.bT)) ∈ blockTri (blk2 D.R.r) ↔
            x ∈ (F.Q i).T.levTop.J) := fun i g hS x hx =>
        red_iff_local (N := v.NT) (F.Q i).q (F.Q i).FT _ hβ hΛ (datXP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) t) (pl i).2 (hpl i).2
          (hg i) (hq i) hb (hm _) (F.Q i).latT (hQL.top i) hS hx
      have hA := (GlobalTheory.T.volume_seeSaw_tuple_level_eq_spherical_div_index D f.c v (f.t t) w F hPins).2 hv.sdT (fun i => (F.Q i).openT) f.g.μT hRow.meas.μT _
        (moved f.g.bT (levG D.sp.X' (_root_.GlobalTheory.Fam.pk_z W).βX ((_root_.GlobalTheory.Fam.pk_z W).datXt t))) f.g.bT hb a1 a2 a3 a4 a5 fun g => by
          refine (mem_moved _ _ g).trans ((mem_levG_iff_base _ _ _ _ _ _ _ _ ((_root_.GlobalTheory.Fam.pk_z W).xiR W.P.A3.A.μ0) hQ0 _).trans
            ((and_congr_right fun h0 => ?_).trans (and_congr_left' (mem_moved _ _ g).symm)))
          have hS := parLev_St (lev_le_parLev h0.2)
          refine ⟨fun H i x hx => (loc i g hS x hx).1 (H _ (pl i).2), fun H PP hPP => ?_⟩
          obtain ⟨i, hi⟩ := pl.surjective ⟨PP, hPP⟩
          obtain ⟨x, hx⟩ := exists_mat (F.Q i).q (F.Q i).FT g
          have := (loc i g hS x hx).2 (H i x hx)
          rw [hi] at this
          exact this
      have e1 := moved_set f.g.bT (levG D.sp.X' (_root_.GlobalTheory.Fam.pk_z W).βX ((_root_.GlobalTheory.Fam.pk_z W).datXt t))
      have e2 := moved_set f.g.bT (levG D.sp.X' (_root_.GlobalTheory.Fam.pk_z W).βX ((_root_.GlobalTheory.Fam.pk_z W).datXt W.P.A3.A.μ0))
      rw [e1, e2] at hA
      exact hA
  show cIOf (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) f.g t j * _ = cIOf (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) f.g W.P.A3.A.μ0 j
  unfold cIOf
  rw [← key]
  push_cast
  ring
end GlobalTheory.StepConst
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CIMulIdxStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cI_mul_prod_idx_eq_cI_mu0 : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ v : VCom f.c, v.Is → _root_.GlobalTheory.Fam.CommutingVectorTie f v → ∀ t (w : VTup (f.t t)) (F : GlobalTheory.QPl.QFam v (f.t t)), F.Pins w → _root_.GlobalTheory.Fam.QLevAlt f F → ∀ j, j < D.R.m → (f.t t).cI j * ∏ i, ((F.Q i).idx (j + 1) : ℂ) = (f.t W.P.A3.A.μ0).cI j := by
  first | exact @_root_.GlobalTheory.StepConst.cI_mul_idx_alt | exact _root_.GlobalTheory.StepConst.cI_mul_idx_alt | (intros; apply _root_.GlobalTheory.StepConst.cI_mul_idx_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkTailOfTopReadAt
set_option synthInstance.maxHeartbeats 200000

section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
noncomputable section
namespace GlobalTheory.MiTop.TailColumnRecursion
open Classical
open _root_.Formalism.L2.Forms GlobalTheory.Core.Rk.Top
variable {D : D7}
variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : D.what₂.Word}
theorem tcol_alt (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (t : W.P.T) (i : ℕ) (ψ : (f.t t).Col 0) :
    (f.t t).col i ψ = Formalism.ThetaLiftIndependence.chainOpM (D.chTw u (W.P.I.tup t)).wt (D.chTw u (W.P.I.tup t)).Kmap i ψ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    show (f.t t).K i ((f.t t).col i ψ) = _
    rw [ih]; rfl
end GlobalTheory.MiTop.TailColumnRecursion
namespace GlobalTheory.MiTop.TailColumnRecursion
open Classical
open _root_.Formalism.L2.Forms GlobalTheory.Core.Rk.Top Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev
variable {D : D7}
end GlobalTheory.MiTop.TailColumnRecursion
namespace GlobalTheory.MiTop.TailColumnRecursion
open Classical
open _root_.Formalism.L2.Forms GlobalTheory.Core.Rk.Top Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev
variable {D : D7}
end GlobalTheory.MiTop.TailColumnRecursion
namespace GlobalTheory.MiTop.TailColumnRecursion
open Classical
open _root_.Formalism.L2.Forms GlobalTheory.Core.Rk.Top Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev
variable {D : D7}
section G
variable {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {Pm : PeriodMap D.R C}
    {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A Pm}
    {bad : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F))} {K : ClassesAtPrimes M bad} {okW : D.what₂.places.Pl → Prop}
end G
end GlobalTheory.MiTop.TailColumnRecursion
namespace GlobalTheory.MiTop.TailColumnRecursion
open Classical
open _root_.Formalism.L2.Forms GlobalTheory.Core.Rk.Top Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev
variable {D : D7}
end GlobalTheory.MiTop.TailColumnRecursion
namespace GlobalTheory.MiTop
open Classical
open GlobalTheory.MiTop.TailColumnRecursion _root_.Formalism.L2.Forms
theorem linkTail_of_topReadAt_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), ∀ u (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.LeadingReadAt W u f.j f.g.bT → (∀ t, W.P.I.tup t = D.what₂.mu0 → ∀ φ : D.what₂.Mu u, HEq (_root_.GlobalTheory.MiTop.col0_alt f t φ) (D.eMu u φ).1) → _root_.GlobalTheory.MiTop.LinkTailCondition f := by
  intro D L hT Gi Gl Kc Yd cX ex W u f hTR h0 n h t φ F F' hFF G hG
  obtain ⟨hJ, -, hall⟩ := hTR
  have hR := (hall t).2 F F' hFF
  have hex : ∃ G0, _root_.GlobalTheory.Fam.ReadsCoefficients W u f.j f.g.bT (W.P.I.tup t) G0 (_root_.GlobalTheory.Fam.leadingLinearMap W t F') := ⟨_, hR⟩
  have hspec := hex.choose_spec
  show _root_.GlobalTheory.Fam.tailCoefficient W u f.j f.g.bT (W.P.I.tup t)
    (Eq.rec (motive := fun n _ => (D.chTw u (W.P.I.tup t)).cls n → (D.chTw u (W.P.I.tup t)).Y n → ℂ)
      ((f.t t).col (2 * n) (_root_.GlobalTheory.MiTop.col0_alt f t φ)) h) G.1 = _
  rw [hG, _root_.GlobalTheory.MiTop.TailColumnRecursion.tcol_alt, rec_chain]
  unfold _root_.GlobalTheory.Fam.tailCoefficient
  rw [dite_eq_left hex]
  by_cases hμ : W.P.I.tup t = D.what₂.mu0
  · rw [dite_eq_left hμ]
    refine referenceTuple_familyPeriod_eq_period u _ hμ _ φ (h0 t hμ φ) _ _ ?_
    have hv : ∀ z ∈ (D.fm u).ptC, ∀ c, (W.R.T.cols.forms u).valP.eW z c ∈ LinearMap.range f.j := by
      intro z hz c
      rw [hJ.range]
      exact fic_val _ _ _ _ (((W.R.T.cols.forms u).valP.ptC z).1 hz) c
    exact reads_uniq _ _ _ _ (W.R.T.cols.forms u).jM hv (W.R.T.cols.forms u).per.2.1 (W.R.T.cols.forms u).per.2.2
      (pos_0 (W.R.T.cols.forms u)) (hspec.1 hμ) (hR.1 hμ)
  · rw [dite_eq_right hμ, D.perCol_tie u _ hμ, PeriodMap.PtilCol, PeriodMap.Ptil, PeriodMap.Ptil]
    have hv : ∀ z ∈ (ex.tw.fm u (W.P.I.tup t)).ptC, ∀ c, (W.R.T.tw.pt.val u _ hμ).eW z c ∈ LinearMap.range f.j := by
      intro z hz c
      rw [hJ.range, ← sg_eq (W.R.T.tw.pt.val u _ hμ) (W.R.T.cols.forms u).valP]
      exact fic_val _ _ _ _ (((W.R.T.tw.pt.val u _ hμ).ptC z).1 hz) c
    rw [reads_uniq _ _ _ _ (W.R.T.tw.ptE.jM u _) hv (W.R.T.tw.ptE.per u _ hμ).2.1 (W.R.T.tw.ptE.per u _ hμ).2.2
      (pos_G (W.R.T.tw.pt.val u _ hμ)) (hspec.2 hμ) (hR.2 hμ)]
    rfl
end GlobalTheory.MiTop
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkCommOfLaws
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkCommOfLaws
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.AdForm GlobalTheory.AdForm.RdVal
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.MiTop.LComm
variable {D : D7}
end GlobalTheory.MiTop.LComm
end
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem GlobalTheory.MiTop.linkComm_of_laws_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), ∀ u (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat f.c k ι) (ε : ℕ → ι → 𝓀[k]ˣ) (S₀ : ∀ t, (ι → 𝓀[k]ˣ) → (f.t t).Col 0 → (f.t t).Col 0), RamUnitary D → f.c.Is → (∀ t, (f.t t).Is ∧ (f.t t).KBack ∧ (f.t t).TailRd ∧ LiftS o (f.t t) ∧ ReadS o (f.t t) ε (S₀ t)) → o.I.Nodup → (∀ i, i ∈ o.I) → (Function.Injective fun i => (o.p i).v) → (∀ t, Nonempty ((f.t t).Ch 0)) → (∀ t φ, _root_.GlobalTheory.MiTop.col0_alt f t φ ∈ (f.t t).Ram 0 ∧ ∀ α y, (f.t t).rd 0 α (_root_.GlobalTheory.MiTop.col0_alt f t φ) y = (chart0 (_root_.GlobalTheory.MiTop.formsAtZero W u)).rd W.Q.Rl.θ (D.eMu u φ).1 y) → (∀ t, ∀ ψ ∈ (f.t t).Ram 0, ∃ φ, ψ = _root_.GlobalTheory.MiTop.col0_alt f t φ) → _root_.GlobalTheory.MiTop.LinkCommutes f := by
  intro D L hT Gi Gl Kc Yd cX ex W u f k _ _ _ _ ι o ε S₀ hU hc ht hnd _ hinj hne h0 hsur n h
  have hall : ∀ η : ι → 𝓀[k]ˣ, ∃ (S : D.what₂.Mu u ≃ₗ[ℂ] D.what₂.Mu u) (r : ℝ), 0 < r ∧ (∀ φ, ‖S φ‖ = r * ‖φ‖) ∧
      ∀ φ y, (chart0 (_root_.GlobalTheory.MiTop.formsAtZero W u)).rd W.Q.Rl.θ (D.eMu u (S φ)).1 y =
        o.S (fun _ => η) 0 ((chart0 (_root_.GlobalTheory.MiTop.formsAtZero W u)).rd W.Q.Rl.θ (D.eMu u φ).1 y) := by
    intro η
    obtain ⟨α⟩ := hne W.P.A3.A.μ0
    have hR := (ht W.P.A3.A.μ0).2.2.2.2
    refine GlobalTheory.T.levelPrime_operators_stepZero_scale_norms D u (_root_.GlobalTheory.MiTop.formsAtZero W u) W.Q.Rl.θ hc.inf hU (hc.x 0 (Nat.zero_le _)).cpt k ι o.p o.I o.q o.χ o.hχ (o.β 0) (o.Q 0)
      hnd hinj (fun φ y i => ?_) η (fun φ => ?_)
    · have := (hR.ram 0 (Nat.zero_le _) _ (h0 _ φ).1 α y).2 i
      rw [(h0 _ φ).2 α y] at this
      exact this
    · obtain ⟨h1, h2⟩ := hR.S₀ η _ (h0 _ φ).1
      obtain ⟨φ', e⟩ := hsur _ _ h1
      refine ⟨φ', fun y => ?_⟩
      have := h2 α y
      rw [e, (h0 _ φ').2 α y, (h0 _ φ).2 α y] at this
      exact this
  choose S r hr hS hrd using hall
  have hS0 : ∀ t η φ, S₀ t η (_root_.GlobalTheory.MiTop.col0_alt f t φ) = _root_.GlobalTheory.MiTop.col0_alt f t (S η φ) := by
    intro t η φ
    obtain ⟨α⟩ := hne t
    obtain ⟨h1, h2⟩ := (ht t).2.2.2.2.S₀ η _ (h0 t φ).1
    obtain ⟨φ', e⟩ := hsur _ _ h1
    rw [e]
    congr 1
    apply (D.eMu u).injective
    apply Subtype.ext
    refine LComm.chart0_inj (_root_.GlobalTheory.MiTop.formsAtZero W u) W.Q.Rl.θ _ _ (fun y => ?_)
    have := h2 α y
    rw [e, (h0 _ φ').2 α y, (h0 _ φ).2 α y] at this
    rw [this, hrd]
  obtain ⟨A, a, ha, hA, hA'⟩ := LComm.iter_equiv S r hr hS ε n
  refine ⟨A, a, o.cS n, ha, hA, ?_, fun t φ F => ?_⟩
  · refine Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j _ => pow_ne_zero _ ?_
    refine Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos ?_ _).ne'
    exact Nat.cast_pos.2 Nat.card_pos
  · obtain ⟨t1, t2, t3, t4, t5⟩ := ht t
    rw [GlobalTheory.T.seeSawKernelChain_levelPrimeOperator_to_step_zero D f.c k ι o (f.t t) ε (S₀ t) t1 t2 t3 t4 t5 n h _ (h0 t φ).1 F,
      LComm.iterS_comm (fun η φ => S η φ) (S₀ t) (_root_.GlobalTheory.MiTop.col0_alt f t) (hS0 t) ε n φ, hA']
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkCommOfLawsStatement
set_option synthInstance.maxHeartbeats 200000

section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.type_data_unit_shift_relation_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), ∀ u (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat f.c k ι) (ε : ℕ → ι → 𝓀[k]ˣ) (S₀ : ∀ t, (ι → 𝓀[k]ˣ) → (f.t t).Col 0 → (f.t t).Col 0), RamUnitary D → f.c.Is → (∀ t, (f.t t).Is ∧ (f.t t).KBack ∧ (f.t t).TailRd ∧ LiftS o (f.t t) ∧ ReadS o (f.t t) ε (S₀ t)) → o.I.Nodup → (∀ i, i ∈ o.I) → (Function.Injective fun i => (o.p i).v) → (∀ t, Nonempty ((f.t t).Ch 0)) → (∀ t φ, _root_.GlobalTheory.MiTop.col0_alt f t φ ∈ (f.t t).Ram 0 ∧ ∀ α y, (f.t t).rd 0 α (_root_.GlobalTheory.MiTop.col0_alt f t φ) y = (chart0 (_root_.GlobalTheory.MiTop.formsAtZero W u)).rd W.Q.Rl.θ (D.eMu u φ).1 y) → (∀ t, ∀ ψ ∈ (f.t t).Ram 0, ∃ φ, ψ = _root_.GlobalTheory.MiTop.col0_alt f t φ) → _root_.GlobalTheory.MiTop.LinkCommutes f := by
  first | exact @_root_.GlobalTheory.MiTop.linkComm_of_laws_alt | exact _root_.GlobalTheory.MiTop.linkComm_of_laws_alt | (intros; apply _root_.GlobalTheory.MiTop.linkComm_of_laws_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealEqOfColOK
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealEqOfColOK
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam
theorem realEq_of_colOK_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ f : _root_.GlobalTheory.Fam.FamilyCharacter W u, f.ColOK → RealEq f.t := by
  intro D L hT Gi Gl Kc Yd cX ex W u _ f hf j hj s s' a ha b hb φ hφ
  obtain ⟨θ, hθ⟩ := GlobalTheory.DualPairCompare.exists_infFam D
  have hL := W.Q.charW.base.lev
  let k : Fin D.R.m := ⟨j, hj⟩
  have hexp : ∀ τ, ∃ e : ℚ, HasInfExp D ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu s (j + 1)) τ e ∧
      HasInfExp D ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu s' (j + 1)) τ e := by
    intro τ
    obtain ⟨n, hn, ho⟩ := hL.xi_fin s
    obtain ⟨n', hn', ho'⟩ := hL.xi_fin s'
    have h0 := GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ (hL.mu0 k)
      (GlobalTheory.Chain.StepVac.hasInfQ_tau ((_root_.GlobalTheory.Fam.pk_z W).C.isMu0 k).inf) τ
    exact ⟨_, GlobalTheory.Chain.StepVac.hasInfExp_mul h0 (GlobalTheory.Chain.StepVac.hasInfExp_of_order hθ (hL.xi s) hn ho τ),
      GlobalTheory.Chain.StepVac.hasInfExp_mul h0 (GlobalTheory.Chain.StepVac.hasInfExp_of_order hθ (hL.xi s') hn' ho' τ)⟩
  exact GlobalTheory.RealEqWeil.weilDatum_realEq D _ _ _ _ _ _ _ _ _ (hf.kom s j hj) (hf.kom s' j hj) hexp hexp a ha b hb φ hφ
end GlobalTheory.Fam
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealEqOfColOKStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realEq_of_colOK' : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ f : _root_.GlobalTheory.Fam.FamilyCharacter W u, f.ColOK → RealEq f.t := by
  first | exact @_root_.GlobalTheory.Fam.realEq_of_colOK_alt | exact _root_.GlobalTheory.Fam.realEq_of_colOK_alt | (intros; apply _root_.GlobalTheory.Fam.realEq_of_colOK_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.KomWeilUnram
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.KomWeilUnram
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam.UnrWeil
end GlobalTheory.Fam.UnrWeil
open GlobalTheory.Fam.UnrWeil in
theorem GlobalTheory.Fam.kom_weil_unram_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (v : VCom f.c) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat f.c k ι), f.RowOK → f.ColOK → v.Is → _root_.GlobalTheory.Fam.CommutingVectorTie f v → ShapeOff v o → ∀ t j, j < D.R.m → ∃ μ, IsWeilDatumO f.c.ψ _ _ μ μ ((f.t t).kom j) ∧ ∀ i, GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D μ (o.p i).v := by
  intro D L hT Gi Gl Kc Yd cX ex W u hW f v k _ _ _ _ ι o _ hC _ hV hS t j hj
  refine ⟨(_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t (j + 1), hC.kom t j hj, fun i => ?_⟩
  have lev : (_root_.GlobalTheory.Fam.pk_z W).toLevCh.Is W.P.A3.A.μ0 := hW.bot.hyp.2.2.2.1.lev
  have hp : (o.p i).v ∈ v.tP := (hS.pre.tP _).2 ⟨i, rfl⟩
  have hTF : (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ (o.p i).v.asIdeal := (hV.tP _).1 hp
  have hTw : ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = (o.p i).v →
      (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal := by
    intro w hw
    rw [← hw] at hTF
    have := Ideal.mem_comap.1 hTF
    simpa using this
  show GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (Formalism.IndefR.Lift.tup (_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu0 ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.xi t) (j + 1)) (o.p i).v
  refine GlobalTheory.SeeSaw.WeilLines.charUnram_mul ?_ ?_
  · refine GlobalTheory.SeeSaw.LevelTest.charUnramAt_of fun w hw => ?_
    refine (GlobalTheory.LFun.unrAt_iff_of_chrEq (lev.mu0 ⟨j, hj⟩) w).2 ?_
    refine ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.C.isMu0 ⟨j, hj⟩).unr w fun kk hk => ?_
    exact not_both_mem (D.mem u).A.T_prime (D.host.g_prime kk) (D.T_ne_g u kk) w (hTw w hw) hk
  · refine GlobalTheory.SeeSaw.LevelTest.charUnramAt_of fun w hw => ?_
    refine (GlobalTheory.LFun.unrAt_iff_of_chrEq (lev.xi t) w).2 ?_
    by_contra hr
    rcases (lev.Q_ram t w).1 hr with hq | ⟨PP', hq, hc⟩
    · exact (lev.Q_off t w hq).2 u (hTw w hw)
    · exact (lev.Q_off t PP' hq).2 u (natCast_mem_of_isConjPl _ hc (hTw w hw))
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.KomWeilUnramStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.type_data_local_relation_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (v : VCom f.c) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat f.c k ι), f.RowOK → f.ColOK → v.Is → _root_.GlobalTheory.Fam.CommutingVectorTie f v → ShapeOff v o → ∀ t j, j < D.R.m → ∃ μ, IsWeilDatumO f.c.ψ _ _ μ μ ((f.t t).kom j) ∧ ∀ i, GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D μ (o.p i).v := by
  first | exact @_root_.GlobalTheory.Fam.kom_weil_unram_alt | exact _root_.GlobalTheory.Fam.kom_weil_unram_alt | (intros; apply _root_.GlobalTheory.Fam.kom_weil_unram_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LawsLinksOfGeoRowsCols
set_option synthInstance.maxHeartbeats 200000

section
set_option maxHeartbeats 4000000
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem GlobalTheory.Fam.lawsLinks_of_geo_rows_cols_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.StrongApproxSU → ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ row, (∀ t, (row t).Is) → (∀ t t', (row t).Same (row t')) → (∀ k : _root_.GlobalTheory.Fam.FamilyConstants a, ∃ col w₀ w F, _root_.GlobalTheory.AdForm.FamilyColumnCondition (a.fam row col) ∧ _root_.GlobalTheory.Fam.ColumnOutputCondition (row := row) (col := col) k w₀ w F) → ∃ col, (a.fam row col).RowOK ∧ LawsX (a.fam row col).t ∧ _root_.GlobalTheory.MiTop.ChartAtZeroCondition (a.fam row col) ∧ _root_.GlobalTheory.MiTop.LinkTailCondition (a.fam row col) ∧ _root_.GlobalTheory.MiTop.LinkCommutes (a.fam row col) ∧ _root_.GlobalTheory.MiTop.FamilyRatioCondition (a.fam row col) := by
  intro hDS hHC hSA B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha haT row hrow hsame hcol
  letI := a.fld; letI := a.val; letI := a.top; haveI := a.loc
  have hRow : ∀ col, (a.fam row col).RowOK := fun col => ⟨ha.meas, ha.last, ha.x, hrow, hsame⟩
  obtain ⟨col₀, -, -, -, -, -⟩ := hcol ⟨fun _ _ => 1, fun _ => ⟨0, Fin.elim0, Fin.elim0⟩, 0, 0, 0, 0⟩
  have hcIs : (commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g).Is := (_root_.GlobalTheory.T.famCh_is_and_tuples_is_of_colOK hDS hHC W u hW.pk (a.fam row col₀) (hRow col₀)).1
  obtain ⟨ε, op, r, e, cG, hr, hcG, hkap, hvIs, hall⟩ :=
    GlobalTheory.T.seeSaw_latticeFramePins_finiteIntegralLaws _ _ a.v a.k a.ι a.o a.n a.G hcIs ha.last ha.vis ha.shape ha.gpin
  obtain ⟨s, hs, hζ⟩ := _root_.GlobalTheory.T.nonzero_scalars_roots_of_unity_alt _ _ _ _ _ _ _ _ _ W u (a.fam row col₀) hW.pk (hRow col₀) a.v ha.vis
    (ha.tie row col₀).1 a.n a.G a.pl ha.gpin (ha.tie row col₀).2
  choose ζ hζu hζv using hζ
  let k : _root_.GlobalTheory.Fam.FamilyConstants a := ⟨ε, op, r, e, cG, fun t j => s j * ζ t j⟩
  obtain ⟨col, w₀, w, F, hFC, hCO⟩ := hcol k
  have hQ : ∀ t p, p ∈ (w t).Q ↔ ∃ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t, p = PP.under (𝓞 (I.rec7 l Z).host.F) := by
    intro t p
    rw [(hCO.same t).1, (hCO.pins t).places p]
    obtain ⟨pl, hpl⟩ := (hCO.lev t).places
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨(pl i).1, (pl i).2, (hpl i).2⟩
    · rintro ⟨PP, hPP, rfl⟩
      exact ⟨pl.symm ⟨PP, hPP⟩, by rw [(hpl _).2, Equiv.apply_symm_apply]⟩
  have hVf : ∀ t, _root_.GlobalTheory.Fam.VectorFunctionCondition (a.fam row col) a.v (w t) (k.sc t) := by
    intro t
    let w' : VTup ((a.fam row col₀).t t) := ⟨(w₀ t).Q, 0, (w₀ t).eQ, (w₀ t).eQT, fun _ _ _ => 0, fun _ _ => 0, fun _ _ _ => 0, fun _ _ => ∅,
      fun _ => ∅, ∅, 0, 0⟩
    have h1 := hζv t w' (fun p => by rw [← (hCO.same t).1]; exact hQ t p)
      (fun j => ⟨(hCO.atQ t j).1, (hCO.atQ t j).2.1⟩) (hCO.vec t)
    obtain ⟨-, he, heT, -⟩ := hCO.same t
    refine ⟨fun j hj P b hb b' hb' => ?_, fun j h P => ?_⟩
    · rw [he]; exact h1.1 j hj P b hb b' hb'
    · rw [heT]; exact h1.2 j h P
  have hIs := _root_.GlobalTheory.T.famCh_is_and_tuples_is_of_colOK hDS hHC W u hW.pk (a.fam row col) (hRow col)
  have htIs : ∀ t, ((a.fam row col).t t).Is := hIs.2 hCO.ok
  have hweil := fun t => _root_.GlobalTheory.T.weilOK_of_rank_one_gram' W u hW.pk (a.fam row col) a.v (hRow col) hCO.ok (ha.tie row col).1
    (fun j h => ⟨ha.shape.pre.line.1, ha.shape.pre.tau j h⟩) t (w t) (hQ t)
  have hchars : ∀ t i, (a.G i).Chars ((a.fam row col).t t) := fun t => (hweil t).2.2.2.2.2.2 a.n a.G a.pl (ha.tie row col).2
  have hrowt := fun t => _root_.GlobalTheory.T.quadratic_family_level_identity_alt _ _ _ _ _ _ _ _ _ W u (a.fam row col) hW.pk (hRow col) a.v ha.vis (ha.tie row col).1 a.n a.G a.pl
    ha.gpin (ha.tie row col).2 t (w₀ t) (F t) (htIs t) (hCO.pins t) (hCO.lev t) (hchars t)
  have hVF : ∀ t, VForm k.v (w t) := by
    intro t
    obtain ⟨hsQ, he, heT, -, hFY, hFT⟩ := hCO.same t
    have hw := hweil t
    have hrw := hrowt t
    have htie := (ha.tie row col).1
    obtain ⟨S₀, hS⟩ := hCO.read t
    refine ⟨hw.2.2.2.2.1, hw.2.2.2.2.2.1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hrw.2.1⟩
    · intro j hj P b hb b' hb'
      rw [hCO.sc t]; exact (hVf t).1 j hj P b hb b' hb'
    · intro j h P
      rw [hCO.sc t]; exact (hVf t).2 j h P
    · intro j
      have := hCO.atQ t j
      rw [← hsQ, ← he, ← heT] at this
      exact this
    · intro j α
      obtain ⟨h1, h2⟩ := hCO.e t j α
      have hb : k.v.b j = a.g.b j := htie.b j
      refine ⟨by rw [hb]; exact h1, fun g hg => ?_⟩
      rw [hsQ]; exact h2 g hg
    · intro n h β
      obtain ⟨h1, h2⟩ := hCO.eT t n h β
      have hb : k.v.bT = a.g.bT := htie.bT.1
      refine ⟨by rw [hb]; exact h1, fun g hg => ?_⟩
      rw [hsQ]; exact h2 g hg
    · exact hCO.dd t
    · intro j hj ψ hψ α y
      refine ⟨?_, hCO.FX t j hj ψ hψ α y, hS.S j hj ψ hψ α y⟩
      show _ ∈ a.v.RamAd j
      rw [ha.shape.ram j]; exact hS.ram j (by omega) ψ hψ α y
    · intro j hj G x b hb
      obtain ⟨h1, h2⟩ := hrw.1 j hj G x b hb
      refine ⟨?_, fun κ hκ => h2 κ ?_⟩
      · rw [hFY]; exact ((hCO.FY t j _).2 h1)
      · have hoff : offP k.v (w t) = offP a.v (w₀ t) := by
          funext p
          show (p ∉ a.v.gP ∧ p ∉ (w t).Q) = (p ∉ a.v.gP ∧ p ∉ (w₀ t).Q)
          rw [hsQ]
        rw [hoff] at hκ; exact hκ
    · intro G x
      rw [hFT]; exact hCO.FT t _
  obtain ⟨hloc, hval, hlast⟩ := hall W.P.T (a.fam row col).t w fun t => ⟨htIs t, hVF t, (hweil t).1, (hrowt t).2.2, (hweil t).2.1,
    (hweil t).2.2.2.1, hchars t, (hCO.laws t).1, (hCO.laws t).2.1, (hCO.laws t).2.2, hCO.cT t, hCO.cv t⟩
  have hcls : ClsPinD (a.fam row col).t := _root_.GlobalTheory.T.cls_pin_d_of_true_family W u (a.fam row col) hW.tr hW.tw ha.top (hRow col) hFC
  have hlaws : LawsX (a.fam row col).t := ⟨hIs.1, htIs, hloc, _root_.GlobalTheory.T.realEq_of_colOK' W u hW.pk (a.fam row col) hCO.ok, hval, hlast,
    GlobalTheory.T.seeSawKernelLiftCombination_of_definiteClassData _ _ _ _ hIs.1 htIs hcls, GlobalTheory.T.seeSawLastPeriodFactorization_of_classData _ _ _ _ hIs.1 htIs hcls, GlobalTheory.T.seeSaw_scalarForms_continuous_automorphic_central _ _ _ _ hIs.1 htIs hcls⟩
  have hheq : ∀ t, W.P.I.tup t = (I.rec7 l Z).what₂.mu0 → ∀ φ, HEq (_root_.GlobalTheory.MiTop.col0_alt (a.fam row col) t φ) ((I.rec7 l Z).eMu u φ).1 := by
    intro t ht φ
    show HEq ((I.rec7 l Z).e0Tw u (W.P.I.tup t) _) _
    rw [ht]
    exact heq_of_eq (GlobalTheory.Mem.Col2.TC.stepZeroTwist_reference_tuple_eq_id l u _)
  refine ⟨col, hRow col, hlaws, hCO.zero, _root_.GlobalTheory.MiTop.linkTail_of_topReadAt_alt W u (a.fam row col) ha.top hheq, ?_, ?_⟩
  · obtain ⟨ρ, hρ, hA⟩ := hcls
    choose S₀ hS₀ using hCO.read
    have hsh : ShapeOff k.v a.o := by
      have hs := ha.shape
      have hp := hs.pre
      exact ⟨⟨hp.nodup, hp.all, hp.inj, hp.tP, hp.char, hp.latT, hp.line, hp.tau, hp.lam, hp.normT, hp.topT⟩,
        fun x => ⟨(hs.good x).bf, (hs.good x).fb⟩, fun x hx => ⟨(hs.split x hx).core, (hs.split x hx).top⟩, hs.glued, hs.rep,
        hs.ram⟩
    have hne : ∀ {S : ℕ → Prop} {x y : ℂ}, UnitRatio S x y → x ≠ 0 := fun h => ((GlobalTheory.Fam.unitRatio_laws _).2.1 _ _ _ _ h h).2.2
    refine _root_.GlobalTheory.T.type_data_unit_shift_relation_alt W u (a.fam row col) a.k a.ι a.o ε S₀ (GlobalTheory.FinPl.RamUnit.ramUnitary_holds _) hIs.1
      (fun t => ⟨htIs t, ?_, ?_, ?_, hS₀ t⟩) ha.shape.pre.nodup ha.shape.pre.all ha.shape.pre.inj ?_ ?_ ?_
    · obtain ⟨⟨A, hAI⟩, -⟩ := hA t
      exact GlobalTheory.T.seeSawTuple_kernelBack_of_classKernelData _ _ _ ρ A hIs.1 (htIs t) hρ hAI fun j hj => hne (hCO.cK t j hj)
    · obtain ⟨-, A, hAI⟩ := hA t
      exact GlobalTheory.T.lastPeriodClasses_give_tailReading _ _ _ ρ A hAI (hne (hCO.cP t))
    · exact GlobalTheory.T.definiteLift_comm_levelPrimeOperators _ _ a.k a.ι k.v a.o _ (w t) (GlobalTheory.T.splitLiftExactConstant_proof _) hIs.1 (htIs t) hvIs (hVF t) hsh
        (_root_.GlobalTheory.T.type_data_local_relation_alt W u hW.pk (a.fam row col) a.v a.k a.ι a.o (hRow col) hCO.ok ha.vis (ha.tie row col).1 ha.shape t)
    · intro t
      obtain ⟨α₀, -⟩ := hCO.zero t
      exact ⟨α₀⟩
    · intro t φ
      obtain ⟨α₀, hα, -, h3, -⟩ := hCO.zero t
      exact ⟨(h3 φ).1, fun α y => by rw [hα α]; exact (h3 φ).2 y⟩
    · intro t
      obtain ⟨α₀, -, -, -, h4⟩ := hCO.zero t
      exact h4
  · intro n hn t
    have hsc : ∀ tt j, j < (I.rec7 l Z).R.m → UnitRatio (_root_.GlobalTheory.MiTop.qPrime_alt W tt) ((w tt).sc j) ((w W.P.A3.A.μ0).sc j) ∧
        UnitRatio (_root_.GlobalTheory.MiTop.qPrime_alt W tt) (((a.fam row col).t tt).cK j) (((a.fam row col).t W.P.A3.A.μ0).cK j) := by
      intro tt j hj
      refine ⟨?_, hCO.cK tt j hj⟩
      rw [hCO.sc tt, hCO.sc W.P.A3.A.μ0]
      obtain ⟨n₁, hn₁, e₁⟩ := hζu tt j
      obtain ⟨n₂, hn₂, e₂⟩ := hζu W.P.A3.A.μ0 j
      have hz : ζ W.P.A3.A.μ0 j ≠ 0 := fun h0 => by rw [h0, zero_pow hn₂.ne'] at e₂; exact zero_ne_one e₂
      refine (GlobalTheory.Fam.unitRatio_laws _).2.2.1 _ _ (n₁ * n₂) (mul_ne_zero (hs j) hz) (Nat.mul_pos hn₁ hn₂) ?_
      show (s j * ζ tt j) ^ (n₁ * n₂) = (s j * ζ W.P.A3.A.μ0 j) ^ (n₁ * n₂)
      rw [mul_pow, mul_pow, pow_mul (ζ tt j), e₁, mul_comm n₁ n₂, pow_mul (ζ W.P.A3.A.μ0 j), e₂, one_pow, one_pow]
    have hcI : ∀ tt j, j < (I.rec7 l Z).R.m → ((a.fam row col).t tt).cI j ≠ 0 := fun tt j hj =>
      GlobalTheory.Fam.GeoMeas.cIOf_ne_zero (_root_.GlobalTheory.Fam.complexLevelStructure W) ha.meas tt j hj
    have hci := fun tt => _root_.GlobalTheory.T.cI_mul_prod_idx_eq_cI_mu0 _ _ _ _ _ _ _ _ _ W u (a.fam row col) hW.pk (hRow col) a.v ha.vis (ha.tie row col).1 tt
      (w₀ tt) (F tt) (hCO.pins tt) (hCO.lev tt)
    have hq : ∀ tt j ρ, j + 2 * ρ + 2 = (I.rec7 l Z).R.m → (w tt).cQ j / (((a.fam row col).t tt).cI j * ((a.fam row col).t tt).cI (j + 1)) =
        (((a.fam row col).t W.P.A3.A.μ0).cI j * ((a.fam row col).t W.P.A3.A.μ0).cI (j + 1))⁻¹ := by
      intro tt j ρ h
      rw [(hCO.same tt).2.2.2.1, (hCO.pins tt).cQ j (by omega), ← hci tt j (by omega), ← hci tt (j + 1) (by omega),
        Finset.prod_inv_distrib, Finset.prod_mul_distrib, div_eq_mul_inv, ← mul_inv]
      congr 1
      ring
    have hct : ∀ tt j ρ, j + 2 * ρ + 2 = (I.rec7 l Z).R.m → UnitRatio (_root_.GlobalTheory.MiTop.qPrime_alt W tt) ((w tt).cT j) ((w W.P.A3.A.μ0).cT j) ∧
        UnitRatio (_root_.GlobalTheory.MiTop.qPrime_alt W tt) ((w tt).cQ j / (((a.fam row col).t tt).cI j * ((a.fam row col).t tt).cI (j + 1)))
          ((w W.P.A3.A.μ0).cQ j / (((a.fam row col).t W.P.A3.A.μ0).cI j * ((a.fam row col).t W.P.A3.A.μ0).cI (j + 1))) := by
      intro tt j ρ h
      refine ⟨?_, ?_⟩
      · rw [hCO.cT tt j ρ h, hCO.cT W.P.A3.A.μ0 j ρ h, ((hrow tt).sBF j ρ h).2.2.2, ((hrow W.P.A3.A.μ0).sBF j ρ h).2.2.2]
        exact GlobalTheory.SeeSaw.mono_unitRatio _ _ a.k a.ι a.o (r j) (e j) _ _ _ (hr j)
          ((_root_.GlobalTheory.T.root_of_unity_theta_twist_alt _ _ _ _ _ _ _ _ _ W u (a.fam row col) hW.pk (hRow col) tt).choose_spec.2.2.2 (j + 1))
      · rw [hq tt j ρ h, hq W.P.A3.A.μ0 j ρ h]
        exact (GlobalTheory.Fam.unitRatio_laws _).1 _ (inv_ne_zero (mul_ne_zero (hcI _ j (by omega)) (hcI _ (j + 1) (by omega))))
    obtain ⟨h1, -, h3⟩ := GlobalTheory.T.seeSaw_totalConstant_ratio_of_factor_ratios _ _ k.v W.P.T (a.fam row col).t w (_root_.GlobalTheory.MiTop.qPrime_alt W) W.P.A3.A.μ0 htIs hCO.cv hkap hcG hsc hct
      hCO.cP n hn t
    exact ⟨h1, h3⟩
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LawsLinksOfGeoRowsColsStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_family_column_data_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.StrongApproxSU → ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ row, (∀ t, (row t).Is) → (∀ t t', (row t).Same (row t')) → (∀ k : _root_.GlobalTheory.Fam.FamilyConstants a, ∃ col w₀ w F, _root_.GlobalTheory.AdForm.FamilyColumnCondition (a.fam row col) ∧ _root_.GlobalTheory.Fam.ColumnOutputCondition (row := row) (col := col) k w₀ w F) → ∃ col, (a.fam row col).RowOK ∧ LawsX (a.fam row col).t ∧ _root_.GlobalTheory.MiTop.ChartAtZeroCondition (a.fam row col) ∧ _root_.GlobalTheory.MiTop.LinkTailCondition (a.fam row col) ∧ _root_.GlobalTheory.MiTop.LinkCommutes (a.fam row col) ∧ _root_.GlobalTheory.MiTop.FamilyRatioCondition (a.fam row col) := by
  first | exact @_root_.GlobalTheory.Fam.lawsLinks_of_geo_rows_cols_alt | exact _root_.GlobalTheory.Fam.lawsLinks_of_geo_rows_cols_alt | (intros; apply _root_.GlobalTheory.Fam.lawsLinks_of_geo_rows_cols_alt <;> assumption)
end
end
