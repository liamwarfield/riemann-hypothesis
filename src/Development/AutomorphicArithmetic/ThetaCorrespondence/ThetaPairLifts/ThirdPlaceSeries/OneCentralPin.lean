module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaLocalInputs
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FinECentralRatioMemSt

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsIsAt
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowCharacterEqExtension
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowCharacterEqExtension
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.LevZeroChr
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
set_option maxHeartbeats 1000000 in
theorem rowChi_conj_of_mem_alt (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (hW : _root_.GlobalTheory.Fam.PackageHypotheses W) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u)
    (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) (hPl : _root_.GlobalTheory.MiTop.PlacedAlt f B) (a₀ : GA D (D.sp.X 0)) (hH0 : IsTransportAdelicCorrection (W.S.tr u) a₀)
    (a : GA D (D.sp.X 0)) (hac : a ∈ Subgroup.center (GA D (D.sp.X 0)))
    (t s : GA D (D.sp.Y 0)) (ht : t = f.g.b 0)
    (hs : s = ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))⁻¹ * embA B.d B.o (a₀ * a) * t)
    (β : GL (Fin (D.sp.Y 0).rank) (Lev.EAf D)) (hβ : β = (_root_.GlobalTheory.Fam.pk_z W).βY 0)
    (Lz : Formalism.L2.DIV.LevDat D.host.E ℂ (D.sp.Y 0).rank) (hLz : Lz = _root_.GlobalTheory.LevZero.datZero_alt W)
    (hSt : ∀ κ : GA D (D.sp.Y 0), (κ ∈ GfC (D.sp.Y 0) ∧ finE (D.sp.Y 0) κ ∈ St (finE (D.sp.Y 0) s * β)) ↔
      ((iotaX W.S.X W.Q.instEq κ).1 = 1 ∧ (iotaX W.S.X W.Q.instEq κ).2 ∈ W.S.X.B.I.Kset))
    (hmem : ∀ k ∈ levS (D.sp.Y 0) β Lz, s * k * s⁻¹ ∈ rowJ W.S.X W.Q.instEq) :
    ∀ k ∈ levS (D.sp.Y 0) β Lz, rowChi W.S.X W.Q.instEq (s * k * s⁻¹) = levChi (D.sp.Y 0) β Lz k := by
  obtain ⟨kk, i1, i2, i3, i4, ι, v, o, n, G, pl, hcis, hvis, htie, hshape, hpin, hread, hbot⟩ := hPl
  have hBot := _root_.GlobalTheory.T.bessel_local_type_data_alt W hW u f B kk ι v o n G pl ⟨hcis, hvis, htie, hshape, hpin, hread, hbot⟩
  have h0 : 0 + 2 * D.R.rS + 2 = D.R.m := by
    obtain ⟨b, hb⟩ := D.R.m_even
    have := D.R.two_le_m
    unfold Formalism.BasicNotions.Ranks.rS
    omega
  have hBl := hbot.lev h0
  have hE : GlobalTheory.Core.Mi.IdE W.S.X := hW.bot.idE
  have hTP : GlobalTheory.Core.Mi.IsTypePlaces (_root_.GlobalTheory.BaseChain.com_z W).Pg := hBot.typ
  have hemb : ∀ b, embA B.d B.o b = (embA (f.c.bes 0 D.R.rS h0).d (f.c.bes 0 D.R.rS h0).o b : GA D (f.c.V 0)) := fun b =>
    by
      have h1 := congr_arg_heq (fun L : BesLev D D.R.rS => (embA L.d L.o : GA D L.A →* GA D L.V)) hBl
      have h2 : embA B.d B.o = (embA (f.c.bes 0 D.R.rS h0).d (f.c.bes 0 D.R.rS h0).o : GA D (D.sp.X 0) →* GA D (f.c.V 0)) :=
        eq_of_heq h1
      exact DFunLike.congr_fun h2 b
  have hfl : flagN B.d = (flagN (f.c.bes 0 D.R.rS h0).d : Subgroup (GA D (f.c.V 0))) :=
    eq_of_heq (congr_arg_heq (fun L : BesLev D D.R.rS => flagN L.d) hBl)
  have hps : psiBes W.Q.Rl.ψ B.d 1 (vecB B.o B.ζ) =
      (psiBes f.c.ψ (f.c.bes 0 D.R.rS h0).d 1 (vecB (f.c.bes 0 D.R.rS h0).o (f.c.bes 0 D.R.rS h0).ζ) : GA D (f.c.V 0) → ℂ) :=
    eq_of_heq (congr_arg_heq (fun L : BesLev D D.R.rS => psiBes W.Q.Rl.ψ L.d 1 (vecB L.o L.ζ)) hBl)
  have hred : ∀ (PP : Formalism.L2.DIV.Pl D.host.E) (k : GA D (D.sp.Y 0)),
      redFn (finE (D.sp.Y 0) s * β) PP (finE (D.sp.Y 0) (s * k * s⁻¹)) = redFn β PP (finE (D.sp.Y 0) k) := fun PP k => by
    rw [map_mul, map_mul, map_inv, GlobalTheory.FrameConj.redFn_conj]
  subst hβ hLz
  refine GlobalTheory.T.indexZeroLevel_generated_by_local_unipotents (c := f.c) (_root_.GlobalTheory.BaseChain.com_z W) (_root_.GlobalTheory.LevZero.levelZeroState W) (f.g.b 0) (fun PP => G (pl.symm PP)) h0 hBot
    (fun k : GA D (D.sp.Y 0) => rowChi W.S.X W.Q.instEq (s * k * s⁻¹) =
      levChi (D.sp.Y 0) ((_root_.GlobalTheory.Fam.pk_z W).βY 0) (_root_.GlobalTheory.LevZero.datZero_alt W) k) ?_ ?_ ?_ ?_
  · intro (k : GA D (D.sp.Y 0)) hk (k' : GA D (D.sp.Y 0)) hk' q q'
    show rowChi W.S.X W.Q.instEq (s * (k * k') * s⁻¹) = levChi (D.sp.Y 0) ((_root_.GlobalTheory.Fam.pk_z W).βY 0) (_root_.GlobalTheory.LevZero.datZero_alt W) (k * k')
    have e : s * (k * k') * s⁻¹ = (s * k * s⁻¹) * (s * k' * s⁻¹) := by group
    have q₁ : rowChi W.S.X W.Q.instEq (s * k * s⁻¹) = levChi (D.sp.Y 0) ((_root_.GlobalTheory.Fam.pk_z W).βY 0) (_root_.GlobalTheory.LevZero.datZero_alt W) k := q
    have q₂ : rowChi W.S.X W.Q.instEq (s * k' * s⁻¹) = levChi (D.sp.Y 0) ((_root_.GlobalTheory.Fam.pk_z W).βY 0) (_root_.GlobalTheory.LevZero.datZero_alt W) k' := q'
    rw [GlobalTheory.ChrMatch.levChi_mul (D.sp.Y 0) ((_root_.GlobalTheory.Fam.pk_z W).βY 0) (_root_.GlobalTheory.LevZero.datZero_alt W) hk hk', ← q₁, ← q₂, e, rowChi, rowChi, rowChi,
      map_mul, Prod.snd_mul, W.S.Y.hK.2.2.2.1 _ (hmem k hk).2 _ (hmem k' hk').2, star_mul']
  · intro PP (n : GA D (D.sp.Y 0)) q hn hq hl hk
    have h2 := GlobalTheory.T.indexZeroLevelCharacter_eq_besselCharacter (c := f.c) (_root_.GlobalTheory.BaseChain.com_z W) (_root_.GlobalTheory.LevZero.levelZeroState W) (f.g.b 0) (fun PP => G (pl.symm PP)) h0 hBot
      PP n q hq hl hk
    have hn' : n ∈ flagN B.d := by rw [hfl]; exact hn
    have e : s * (t⁻¹ * n * t) * s⁻¹ = ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))⁻¹ *
        (embA B.d B.o (a₀ * a) * n * (embA B.d B.o (a₀ * a))⁻¹) * (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) := by
      rw [hs]; group
    have hj := hmem (t⁻¹ * n * t) (by rw [ht]; exact hk)
    rw [e] at hj
    have h1 := GlobalTheory.RowBesChar.rowChi_conj_eq_psiBes D W.S.X W.Q.instEq u W.Q.Rl.ψ _ B hE PP.1 (G (pl.symm PP)).q.e
      (G (pl.symm PP)).q.split (hBot.loc PP).idem (hTP.1 PP.1 PP.2) _
      (GlobalTheory.CharLaws.embA_conj_mem B.d B.o (a₀ * a) hn') (GlobalTheory.ChrMatch.suppAt_conj _ _ _ _ hl.1) hj
    subst ht
    show rowChi W.S.X W.Q.instEq
      (s * ((show GA D (D.sp.Y 0) from f.g.b 0)⁻¹ * n * (show GA D (D.sp.Y 0) from f.g.b 0)) * s⁻¹) = _
    refine (congrArg _ e).trans (h1.trans (Eq.trans ?_ h2.symm))
    rw [GlobalTheory.CharLaws.psiBes_conj]
    exact congrFun hps n
  · intro (b : GA D (D.sp.X 0)) hb hk
    have hk' : (show GA D (D.sp.Y 0) from f.g.b 0)⁻¹ * embA B.d B.o b * (show GA D (D.sp.Y 0) from f.g.b 0) ∈ _root_.GlobalTheory.MiTop.rJ_z W := by
      rw [hemb b]; exact hk
    have h1 := (_root_.GlobalTheory.T.level_trace_adapted_translate_alt W hW u f B hbot.trace hbot.adapted a₀ hH0 b hb).2 hk'
    have hab : a * b * a⁻¹ = b := by rw [← Subgroup.mem_center_iff.1 hac b]; group
    have e : s * (t⁻¹ * embA B.d B.o b * t) * s⁻¹ = ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))⁻¹ *
        embA B.d B.o (a₀ * b * a₀⁻¹) * (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) := by
      have : a₀ * b * a₀⁻¹ = (a₀ * a) * b * (a₀ * a)⁻¹ := by
        conv_lhs => rw [← hab]
        group
      rw [this, map_mul _ _ (a₀ * a)⁻¹, map_mul _ (a₀ * a) b, map_inv, hs]; group
    subst ht
    have h3 := (congrArg (rowChi W.S.X W.Q.instEq) e).trans h1
    rw [hemb b] at h3
    exact h3
  · intro (k : GA D (D.sp.Y 0)) hk hr1
    show rowChi W.S.X W.Q.instEq (s * k * s⁻¹) = levChi (D.sp.Y 0) ((_root_.GlobalTheory.Fam.pk_z W).βY 0) (_root_.GlobalTheory.LevZero.datZero_alt W) k
    rw [GlobalTheory.PrinFrame.rowChi_eq_one D W.S.X W.Q.instEq hE (_root_.GlobalTheory.BaseChain.com_z W).Pg hTP hBot.com.split _ hSt _ (hmem k hk)
      (fun PP hPP => (hred PP k).trans (hr1 PP hPP))]
    exact (GlobalTheory.ChrMatch.levChi_of_red_one _ _ _ rfl rfl hr1).symm
set_option maxHeartbeats 1000000 in
theorem row_character_eq_extension_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedAlt f B → ∀ a₀ : GA D (D.sp.X 0), IsTransportAdelicCorrection (W.S.tr u) a₀ → ∀ a ∈ GfC (D.sp.X 0), a ∈ Subgroup.center (GA D (D.sp.X 0)) → _root_.GlobalTheory.LevZero.StabiliserCondition f B a₀ a → ∀ κ : GA D (D.sp.Y 0), κ ∈ GfC (D.sp.Y 0) → finE (D.sp.Y 0) κ ∈ Formalism.L2.DIV.St (F := D.host.F) (E := D.host.E) (_root_.GlobalTheory.LevZero.frameAtTranslate f B a₀ a) → Formalism.L2.DIV.rTup (F := D.host.F) (E := D.host.E) (_root_.GlobalTheory.LevZero.frameAtTranslate f B a₀ a) (_root_.GlobalTheory.LevZero.datZero_alt W) (finE (D.sp.Y 0) κ) ∈ (_root_.GlobalTheory.LevZero.datZero_alt W).P.H → κ ∈ rowJ W.S.X W.Q.instEq → rowChi W.S.X W.Q.instEq κ = ((Formalism.L2.DIV.ext1 (_root_.GlobalTheory.LevZero.datZero_alt W).P.H (_root_.GlobalTheory.LevZero.datZero_alt W).P.chi (Formalism.L2.DIV.rTup (F := D.host.F) (E := D.host.E) (_root_.GlobalTheory.LevZero.frameAtTranslate f B a₀ a) (_root_.GlobalTheory.LevZero.datZero_alt W) (finE (D.sp.Y 0) κ)) : ℂˣ) : ℂ) := by
  intro D L hT Gi Gl Kc Yd cX ex W hW u f B hPl a₀ hH0 a ha hac hSt κ hκ hκS hP _
  have hn : (D.sp.Y 0).rank ≤ D.R.r := by
    have := GlobalTheory.Chain.StepVac.rank_Yc (D := D) (j := 0) (Nat.zero_le _)
    exact le_of_eq (this.trans (by simp))
  have hM := _root_.GlobalTheory.T.central_adapted_element_property_alt W hW u f B hPl a₀ hH0 a ha hac hSt
  obtain ⟨β, hβ⟩ : ∃ β : GL (Fin (D.sp.Y 0).rank) (Lev.EAf D), β = (_root_.GlobalTheory.Fam.pk_z W).βY 0 := ⟨_, rfl⟩
  obtain ⟨Lz, hLz⟩ : ∃ Lz : Formalism.L2.DIV.LevDat D.host.E ℂ (D.sp.Y 0).rank, Lz = _root_.GlobalTheory.LevZero.datZero_alt W := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, s = _root_.GlobalTheory.MiTop.translationElement f B a₀ a := ⟨_, rfl⟩
  have hfr : _root_.GlobalTheory.LevZero.frameAtTranslate f B a₀ a = finE (D.sp.Y 0) s * β := by rw [hs, hβ]; rfl
  have hSt' : ∀ κ : GA D (D.sp.Y 0), (κ ∈ GfC (D.sp.Y 0) ∧ finE (D.sp.Y 0) κ ∈ St (finE (D.sp.Y 0) s * β)) ↔
      ((iotaX W.S.X W.Q.instEq κ).1 = 1 ∧ (iotaX W.S.X W.Q.instEq κ).2 ∈ W.S.X.B.I.Kset) := by
    rw [← hfr]; exact hSt
  have key := _root_.GlobalTheory.LevZeroChr.rowChi_conj_of_mem_alt W hW u f B hPl a₀ hH0 a hac _ s rfl hs β hβ Lz hLz hSt'
  have hM' : ∀ κ : GA D (D.sp.Y 0), κ ∈ GfC (D.sp.Y 0) → finE (D.sp.Y 0) κ ∈ St (finE (D.sp.Y 0) s * β) →
      rTup (finE (D.sp.Y 0) s * β) Lz (finE (D.sp.Y 0) κ) ∈ Lz.P.H → κ ∈ rowJ W.S.X W.Q.instEq := by
    rw [← hfr, hLz]; exact fun κ h1 h2 h3 => (hM κ h1 h2).2 h3
  have hκS' : finE (D.sp.Y 0) κ ∈ St (finE (D.sp.Y 0) s * β) := by rw [← hfr]; exact hκS
  have hP' : rTup (finE (D.sp.Y 0) s * β) Lz (finE (D.sp.Y 0) κ) ∈ Lz.P.H := by rw [← hfr, hLz]; exact hP
  suffices hgoal : rowChi W.S.X W.Q.instEq κ =
      ((ext1 Lz.P.H Lz.P.chi (rTup (finE (D.sp.Y 0) s * β) Lz (finE (D.sp.Y 0) κ)) : ℂˣ) : ℂ) by
    rw [← hfr, hLz] at hgoal; exact hgoal
  have e1 : Lz.s = 0 := by rw [hLz]; rfl
  have e2 : Lz.Q = ∅ := by rw [hLz]; rfl
  have e3 : (D.sp.Y 0).rank ≤ Lz.r := by rw [hLz]; exact hn
  clear hκS hP hM hSt hfr hs hβ hLz
  have hfin : ∀ s k : GA D (D.sp.Y 0), k ∈ GfC (D.sp.Y 0) → s * k * s⁻¹ ∈ GfC (D.sp.Y 0) := fun s k hk => by
    rw [← GlobalTheory.SeeConjRead.iotaX_fst_eq_one_iff W.S.X W.Q.instEq] at hk ⊢
    rw [map_mul, map_mul, map_inv, Prod.fst_mul, Prod.fst_mul, hk, mul_one, Prod.fst_inv, mul_inv_cancel]
  have hfe : ∀ k : GA D (D.sp.Y 0), finE (D.sp.Y 0) (s * k * s⁻¹) =
      finE (D.sp.Y 0) s * finE (D.sp.Y 0) k * (finE (D.sp.Y 0) s)⁻¹ := fun k => by rw [map_mul, map_mul, map_inv]
  have hmem : ∀ k ∈ levS (D.sp.Y 0) β Lz, s * k * s⁻¹ ∈ rowJ W.S.X W.Q.instEq := by
    intro k hk
    obtain ⟨hf, hl⟩ := hk
    change finE (D.sp.Y 0) k ∈ lev _ _ _ _ at hl
    rw [mem_lev, mem_parLev] at hl
    have hs' : finE (D.sp.Y 0) (s * k * s⁻¹) ∈ St (finE (D.sp.Y 0) s * β) := by
      rw [hfe, GlobalTheory.FrameConj.conj_mem_St_iff]; exact hl.1.2.1
    refine hM' _ (hfin s k hf) hs' ?_
    rw [hfe, GlobalTheory.FrameConj.rTup_conj]
    exact hl.2
  obtain ⟨k₀, rfl⟩ : ∃ k₀, κ = s * k₀ * s⁻¹ := ⟨s⁻¹ * κ * s, by group⟩
  rw [hfe, GlobalTheory.FrameConj.rTup_conj] at hP' ⊢
  have hk₀ : k₀ ∈ levS (D.sp.Y 0) β Lz := by
    refine ⟨?_, ?_⟩
    · have := hfin s⁻¹ _ hκ
      rwa [show s⁻¹ * (s * k₀ * s⁻¹) * s⁻¹⁻¹ = k₀ by group] at this
    · show finE (D.sp.Y 0) k₀ ∈ lev _ _ _ _
      rw [mem_lev, mem_parLev]
      rw [hfe, GlobalTheory.FrameConj.conj_mem_St_iff] at hκS'
      exact ⟨⟨GlobalTheory.LevSplit.finE_mem_UA _ _, hκS', fun PP _ => GlobalTheory.SeeConjRead.blockTri_blkOf_top _ e3 _,
        fun PP hPP => absurd (e2 ▸ hPP) (Finset.notMem_empty _)⟩, hP'⟩
  refine (key hmem k₀ hk₀).trans ?_
  unfold levChi levFn
  simp only [e1, e2, Finset.range_zero, Finset.prod_empty, Finset.prod_const_one, mul_one]
end GlobalTheory.LevZeroChr
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowCharacterEqExtensionStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.central_adapted_element_value_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedAlt f B → ∀ a₀ : GA D (D.sp.X 0), IsTransportAdelicCorrection (W.S.tr u) a₀ → ∀ a ∈ GfC (D.sp.X 0), a ∈ Subgroup.center (GA D (D.sp.X 0)) → _root_.GlobalTheory.LevZero.StabiliserCondition f B a₀ a → ∀ κ : GA D (D.sp.Y 0), κ ∈ GfC (D.sp.Y 0) → finE (D.sp.Y 0) κ ∈ Formalism.L2.DIV.St (F := D.host.F) (E := D.host.E) (_root_.GlobalTheory.LevZero.frameAtTranslate f B a₀ a) → Formalism.L2.DIV.rTup (F := D.host.F) (E := D.host.E) (_root_.GlobalTheory.LevZero.frameAtTranslate f B a₀ a) (_root_.GlobalTheory.LevZero.datZero_alt W) (finE (D.sp.Y 0) κ) ∈ (_root_.GlobalTheory.LevZero.datZero_alt W).P.H → κ ∈ rowJ W.S.X W.Q.instEq → rowChi W.S.X W.Q.instEq κ = ((Formalism.L2.DIV.ext1 (_root_.GlobalTheory.LevZero.datZero_alt W).P.H (_root_.GlobalTheory.LevZero.datZero_alt W).P.chi (Formalism.L2.DIV.rTup (F := D.host.F) (E := D.host.E) (_root_.GlobalTheory.LevZero.frameAtTranslate f B a₀ a) (_root_.GlobalTheory.LevZero.datZero_alt W) (finE (D.sp.Y 0) κ)) : ℂˣ) : ℂ) := by
  first | exact @_root_.GlobalTheory.LevZeroChr.row_character_eq_extension_alt | exact _root_.GlobalTheory.LevZeroChr.row_character_eq_extension_alt | (intros; apply _root_.GlobalTheory.LevZeroChr.row_character_eq_extension_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.StabMatch
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.StabMatch
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.Core.Mi.LatMatch
noncomputable section
namespace GlobalTheory.LevZero.StabMatch
variable {D : D7}
set_option maxHeartbeats 2000000 in
theorem exists_center_stab_at_of_transport_correction : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedAlt f B → Framed B → ∀ a₀ : GA D (D.sp.X 0), IsTransportAdelicCorrection (W.S.tr u) a₀ → ∃ a ∈ GfC (D.sp.X 0), a ∈ Subgroup.center (GA D (D.sp.X 0)) ∧ _root_.GlobalTheory.LevZero.StabiliserCondition f B a₀ a := by
  intro D L hT Gi Gl Kc Yd cX ex W hW u f B hPl hFr a₀ ha₀
  obtain ⟨k, _, _, _, _, ι, v, o, n, G, pl, hc, hv, hVT, hSh, hGP, hGR, hBT⟩ := hPl
  have hbot := _root_.GlobalTheory.LevZero.bot_of_placedBy_alt W hW u f B k ι v o n G pl ⟨hc, hv, hVT, hSh, hGP, hGR, hBT⟩
  obtain ⟨μ, lam, hμ, hl, hz', he, he'⟩ := hFr
  have hF : B.FrameAt μ lam :=
    ⟨hμ, hl, funext fun r => funext fun a => he r a, funext fun r => funext fun a => he' r a, funext fun r => hz' r⟩
  have h0 : 0 + 2 * D.R.rS + 2 = D.R.m := by have := D.R.rS_two; omega
  have hm : 0 < D.R.m := by omega
  have hE : GlobalTheory.Core.Mi.IdE W.S.X := hW.bot.idE
  have hLM := hW.bot.hyp.2.1 u
  have hBa := hBT.adapted
  have hψ : IsStdChar D W.Q.Rl.ψ (-1) := hc.std
  have hb : @Eq (BesAt (f.c.V 0) (f.c.X 0) D.R.rS) (f.c.bes 0 D.R.rS h0) (toBes B) := eq_toBes B _ _ (hBT.lev h0)
  have hΛ : IsSelfDualC (Yc D 0) ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) := hbot.mem.selfDual
  have hfr : Formalism.L2.DIV.IsFrame ((_root_.GlobalTheory.Fam.pk_z W).βY 0) ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) := hbot.mem.frame
  obtain ⟨Lm, hLm, hmv⟩ := GlobalTheory.FinPl.GlobImage.image_moves (Yc D 0) ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) hΛ (f.g.b 0)
  have hloc : ∀ i, LocAt (G i) (pl i).1 (f.g.b 0) ((_root_.GlobalTheory.Fam.pk_z W).βY 0) := fun i => by
    have := hbot.loc (pl i)
    rwa [Equiv.symm_apply_apply] at this
  have hC := facts o G h0 hc hSh (fun i => (pl i).1) (f.g.b 0) ((_root_.GlobalTheory.Fam.pk_z W).βY 0) hloc ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) Lm hfr hmv
  rw [hb] at hC
  obtain ⟨M, c1, c2, c3, c4⟩ := hC
  obtain ⟨s1, s2, s3, -, -, s6⟩ := rows_shape hE hF
  obtain ⟨-, z2, -⟩ := GlobalTheory.T.besselLevelLineVector_primitive_rowLattice_norm D W.S.X W.Q.instEq u W.Q.Rl.ψ _ B μ lam hE hF
  have loc : ∀ p : GlobalTheory.FinPl.Pl D, ∃ (a : GA D (D.sp.X 0)) (c : AE D), CenAt (D.sp.X 0) p a ∧ NormOneAt p c ∧
      SMoves (D.sp.Y 0) c (embA B.d B.o (a₀ * a)) Lm (latS D) p := by
    intro p
    by_cases hpg : p ∈ v.gP
    · obtain ⟨i, rfl⟩ := (hGP.places p).1 hpg
      have hpT : (G i).q.v ∉ v.tP := Finset.disjoint_left.1 hv.disj hpg
      obtain ⟨q⟩ : Nonempty (GlobalTheory.LatPair.Unif (G i).k) := inferInstance
      have hϖ := (GlobalTheory.SeeSaw.LevelTest.val_eq_unif (G i).q (hloc i).idem q (hbot.typ.1 (pl i).1 (pl i).2)
        (GlobalTheory.SeeSaw.LevelTest.g_notMem_sq (pl i).1)).trans (GlobalTheory.SeeSaw.LevelTest.unif_val q (G i).S.unif)
      exact loc_level hE hF hLM hBa ha₀ (G i).q (G i).unit _ (by simpa using hϖ) (fun h => hpT ((hVT.tP _).2 h))
        (c4 i).1 hLm (hBT.lat _ hpT) (c4 i).2
    · have hg : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ∉ p.asIdeal := by
        intro h
        obtain ⟨PP, ⟨h1, h2⟩, -⟩ := hbot.typ.2 p h
        exact hpg ((hVT.gP p).2 ⟨PP, h1, h2.symm⟩)
      have hpS : p ∉ (_root_.GlobalTheory.BaseChain.com_z W).S := by
        intro h
        obtain ⟨PP, h1, h2⟩ := Finset.mem_image.1 h
        exact hpg ((hVT.gP p).2 ⟨PP, h1, h2.symm⟩)
      have hN : Moves (Yc D 0) (f.g.b 0) ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) (v.N 0) (· = p) := hVT.moves 0 hm _ fun p' hp' => hp' ▸ hpg
      obtain ⟨d1, d2, d3, d4⟩ := c1 p
      suffices H : ∃ (a : GA D (D.sp.X 0)) (c : AE D), CenAt (D.sp.X 0) p a ∧ NormOneAt p c ∧
          SMoves (D.sp.Y 0) c (embA B.d B.o (a₀ * a)) (v.N 0) (latS D) p by
        obtain ⟨a, c, h1, h2, h3⟩ := H
        exact ⟨a, c, h1, h2, sMoves_of_moves (S := D.sp.Y 0) hN (hmv _) h3⟩
      refine loc_of_core hψ hE hF hg (hv.sd 0 hm) d1 d2 d3 d4 ?_
      by_cases hpT : p ∈ v.tP
      · have hTv := (hVT.tP p).1 hpT
        obtain ⟨i, rfl⟩ := (hSh.pre.tP p).1 hpT
        obtain ⟨β₀, e1, e2⟩ := c3 i
        have hr : 3 ≤ Fintype.card (Fin (D.sp.X 0).rank) := by
          have h1 := D.R.m_add_three_le_k
          rw [Fintype.card_fin, D.sp.X_rank 0 (Nat.zero_le _), Ranks.N]
          omega
        refine GlobalTheory.T.exists_central_element_homothetic_gluedCores D k (o.p i) _ _ _ B.o B.ζ _ (o.β 0 i) β₀ M _ μ _ o.q (o.Q 0 i) a₀ hr e1 d1 s2 e2 hF.ne (s6 _) z2
          (GlobalTheory.SeeSaw.LevelTest.unifT_of _ _ hTv) fun a ha => ?_
        obtain ⟨y, hy, hU⟩ := GlobalTheory.T.columnLevel_iff_rowLattice_kept_at_place D W.S.X W.Q.instEq u W.Q.Rl.ψ (_root_.GlobalTheory.MiTop.formsAtZero W u) (W.S.tr u) W.S.Y.hK B a₀ hE hLM hBa ha₀ _ hg a ha
        have c5 : (y : GL _ _) ∈ (_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.U ↔ Moves (D.sp.Y 0) (embA B.d B.o a) (v.N 0) (v.N 0) (· = (o.p i).v) :=
          (hBT.trace a (mem_GfC_of_grpAt ha) y hy).1.trans
            ((GlobalTheory.T.mem_chainLevel_iff_carriesLattice_offLevel D (_root_.GlobalTheory.BaseChain.com_z W) 0 (_root_.GlobalTheory.LevZero.levelZeroState W).st hbot.mem _ hpS _
              (conj_mem_grpAt (S := D.sp.Y 0) (embA_mem_grpAt _ _ ha) _)).trans (moves_conj (S := D.sp.Y 0) hN _))
        exact ((GlobalTheory.T.wittCoreEmbedding_stabilises_iff_core_stabilises D _ _ _ B.d _ _ _ _ d2).symm.trans (c5.symm.trans hU)).trans
          (GlobalTheory.T.wittCoreEmbedding_stabilises_iff_core_stabilises D _ _ _ B.d _ _ _ _ (s3 _))
      · obtain ⟨LL, e1, e2⟩ := c2 p hpT
        have hTv : (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∉ p.asIdeal := fun h => hpT ((hVT.tP p).2 h)
        exact GlobalTheory.T.orthogonalSumCores_homothetic_off_level D _ _ _ B.o B.ζ M _ (f.g.x 0).L LL μ _ p a₀ B.line e1 e2
          (rows_trace hE hF hLM hBa ha₀ p (hBT.lat p hpT))
          (GlobalTheory.T.selfDualLattice_splitsOff_unitNormLine_at_place D _ _ _ B.o B.ζ _ μ _ p B.line s2 hF.ne (s6 p) z2 hTv) hF.ne (s6 p) z2 hTv
  obtain ⟨a, haf, hac, z, hz, hmvz⟩ := GlobalTheory.T.exists_central_glue_localHomotheties D (D.sp.Y 0) (D.sp.X 0) (embA B.d B.o) (embA B.d B.o a₀) Lm
    (latS D) hLm s1 (fun v a ha => embA_mem_grpAt _ _ ha) (fun v => by simpa only [map_mul] using loc v)
  rw [← map_mul] at hmvz
  exact ⟨a, haf, hac, stab_of_frame W.S.X W.Q.instEq u ((_root_.GlobalTheory.Fam.pk_z W).βY 0) _ _ z hz
    (GlobalTheory.T.isFrame_finitePart_mul_of_carries_lattice D (D.sp.Y 0) _ ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) (latS D) ((_root_.GlobalTheory.Fam.pk_z W).βY 0) (moves_trans (hmv _) hmvz) hfr)⟩
end GlobalTheory.LevZero.StabMatch
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.StabMatchStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_central_stab_of_transport_correction : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedAlt f B → Framed B → ∀ a₀ : GA D (D.sp.X 0), IsTransportAdelicCorrection (W.S.tr u) a₀ → ∃ a ∈ GfC (D.sp.X 0), a ∈ Subgroup.center (GA D (D.sp.X 0)) ∧ _root_.GlobalTheory.LevZero.StabiliserCondition f B a₀ a := by
  first | exact @_root_.GlobalTheory.LevZero.StabMatch.exists_center_stab_at_of_transport_correction | exact _root_.GlobalTheory.LevZero.StabMatch.exists_center_stab_at_of_transport_correction | (intros; apply _root_.GlobalTheory.LevZero.StabMatch.exists_center_stab_at_of_transport_correction <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsIsAt
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
namespace GlobalTheory.MiTop
set_option maxHeartbeats 1000000 in
theorem exists_isAt_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ u (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedAlt f B → GlobalTheory.MiTop.Framed B → ∃ a₀ a, _root_.GlobalTheory.MiTop.IsTranslate' f B a₀ a := by
  intro D L hT Gi Gl Kc Yd cX ex W hW u f B hP hF
  obtain ⟨a₀, ha₀⟩ := GlobalTheory.Core.Mi.PinModel.exists_transport_adelic_correction (W.S.tr u)
  obtain ⟨a, haf, hac, hSt⟩ := _root_.GlobalTheory.T.exists_central_stab_of_transport_correction W hW u f B hP hF a₀ ha₀
  have hM := _root_.GlobalTheory.T.central_adapted_element_property_alt W hW u f B hP a₀ ha₀ a haf hac hSt
  have hC := _root_.GlobalTheory.T.central_adapted_element_value_alt W hW u f B hP a₀ ha₀ a haf hac hSt
  have hb : (show GA D (D.sp.Y 0) from f.g.b 0) ∈ GfC (D.sp.Y 0) := by
    obtain ⟨k, _, _, _, _, ι, v, o, n, G, pl, -, hv, ht, -⟩ := hP
    have h1 := hv.b 0
    rw [ht.b 0] at h1
    exact h1
  have hx : (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) ∈ GfC (D.sp.Y 0) :=
    (GlobalTheory.SeeConjRead.iotaX_fst_eq_one_iff W.S.X W.Q.instEq _).1 (by simp)
  have htf : _root_.GlobalTheory.MiTop.translationElement f B a₀ a ∈ GfC (D.sp.Y 0) :=
    mul_mem (mul_mem (inv_mem hx) (GlobalTheory.Core.Mi.CenAct.embA_mem_GfC B.d B.o (mul_mem ha₀.1 haf))) hb
  have hn : (D.sp.Y 0).rank ≤ D.R.r := by
    rw [rank_eq W.S.X W.Q.instEq, W.S.X.n_eq]
  refine ⟨a₀, a, ha₀, haf, hac, htf, fun κ => ?_⟩
  rw [inv_inv]
  have h1 := GlobalTheory.FrameConj.levS_conj_frame (D.sp.Y 0) (show GL (Fin (D.sp.Y 0).rank) (Lev.EAf D) from (_root_.GlobalTheory.Fam.pk_z W).βY 0)
    (show LevDat D.host.E ℂ (D.sp.Y 0).rank from _root_.GlobalTheory.LevZero.datZero_alt W) (_root_.GlobalTheory.MiTop.translationElement f B a₀ a) htf κ
  generalize _root_.GlobalTheory.MiTop.translationElement f B a₀ a * κ * (_root_.GlobalTheory.MiTop.translationElement f B a₀ a)⁻¹ = y at h1 ⊢
  obtain ⟨h2, h3⟩ := oneBlock_lev (D.sp.Y 0) (_root_.GlobalTheory.LevZero.frameAtTranslate f B a₀ a)
    (show LevDat D.host.E ℂ (D.sp.Y 0).rank from _root_.GlobalTheory.LevZero.datZero_alt W) hn rfl rfl y
  have h4 : κ ∈ _root_.GlobalTheory.MiTop.rJ_z W ↔ y ∈ levS (D.sp.Y 0) (_root_.GlobalTheory.LevZero.frameAtTranslate f B a₀ a)
    (show LevDat D.host.E ℂ (D.sp.Y 0).rank from _root_.GlobalTheory.LevZero.datZero_alt W) := h1.1
  have h5 : Lev.levChi (D.sp.Y 0) (_root_.GlobalTheory.LevZero.frameAtTranslate f B a₀ a)
    (show LevDat D.host.E ℂ (D.sp.Y 0).rank from _root_.GlobalTheory.LevZero.datZero_alt W) y = _root_.GlobalTheory.MiTop.realCharacter W κ := h1.2
  rw [h2] at h4
  refine ⟨h4.trans ⟨fun h => (hM y h.1 h.2.1).2 h.2.2, fun h => ?_⟩, fun hk => ?_⟩
  · obtain ⟨hf, hs⟩ := (hSt y).2 ⟨h.1, h.2.1⟩
    exact ⟨hf, hs, (hM y hf hs).1 h⟩
  · obtain ⟨hf, hs, hp⟩ := h4.1 hk
    exact (hC y hf hs hp ((hM y hf hs).2 hp)).trans (h3.symm.trans h5)
end GlobalTheory.MiTop
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsIsAtStatement
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
theorem _root_.GlobalTheory.T.exists_isAt_of_placed_framed : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ u (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedAlt f B → GlobalTheory.MiTop.Framed B → ∃ a₀ a, _root_.GlobalTheory.MiTop.IsTranslate' f B a₀ a := by
  first | exact @_root_.GlobalTheory.MiTop.exists_isAt_alt | exact _root_.GlobalTheory.MiTop.exists_isAt_alt | (intros; apply _root_.GlobalTheory.MiTop.exists_isAt_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MatchingCoset
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CentralRatioRedEqOne
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AdelicEmbeddingInverseVector
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AdelicEmbeddingInverseVector
set_option synthInstance.maxHeartbeats 200000

section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.LocMod Matrix
noncomputable section
namespace GlobalTheory.MiTop.MoveZ
section Two
variable {D : D7} {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']
end Two
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
theorem addChar_uniformizer_eq_chi_of_gRead (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (PP : (_root_.GlobalTheory.Fam.pk_z W).Pg) : ∃ χ : 𝓞 D.host.E → ℂ, ∀ u (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (v : VCom f.c) (n : ℕ)
    (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), _root_.GlobalTheory.Fam.LocalGroupReading f G pl → ∀ i, pl i = PP → ∀ z : 𝓞 D.host.E,
      ((G i).S.ψ ((((G i).S.ϖ⁻¹ : (G i).kˣ) : (G i).k) * (ofSplit (G i).q).pr (z : D.host.E)) : ℂ) = χ z := by
  classical
  have hr : 2 ≤ D.R.r := by have := D.R.two_le_m; have := D.R.m_add_three_le_k; unfold Ranks.r; omega
  have hk : 2 ≤ D.R.k := by have := D.R.two_le_m; have := D.R.m_add_three_le_k; omega
  let a : Fin D.R.r := ⟨0, by omega⟩
  let b : Fin D.R.r := ⟨1, by omega⟩
  have hab : a ≠ b := fun e => by have := congrArg Fin.val e; simp [a, b] at this
  let g : 𝓞 D.host.E → ∀ P : (_root_.GlobalTheory.Fam.pk_z W).Pg, GL (Fin D.R.r) (kP P.1) := fun z P =>
    elem a b hab (Ideal.Quotient.mk P.1.asIdeal (if P = PP then z else 0))
  refine ⟨fun z => if h : g z ∈ (_root_.GlobalTheory.Fam.complexLevelStructure W).H then (((_root_.GlobalTheory.Fam.complexLevelStructure W).chi ⟨g z, h⟩ : ℂˣ) : ℂ) else 0, ?_⟩
  intro u f v n G pl hG i hi z
  have hex : ∀ j, ∃ x, GlobalTheory.LevZero.Red (G j) (pl j).1 x (g z (pl j)) := fun j =>
    (GlobalTheory.LevZero.exists_red_iff_isPat (G j) (pl j).1 (hG.idem j).1 _).2
      (isPat_elem a b hab (Or.inl ⟨by simp only [a]; omega, by simp only [b]; omega, by simp [a, b]⟩) _)
  have hmem : g z ∈ (_root_.GlobalTheory.Fam.complexLevelStructure W).H := (hG.lev (g z)).1.2 hex
  choose x hx using hex
  have hchi := (hG.lev (g z)).2 hmem x hx
  have hlam : ∀ j, (((G j).S.P.lam (x j) : ℂˣ) : ℂ) = (G j).S.ψ ((((G j).S.ϖ⁻¹ : (G j).kˣ) : (G j).k) *
      (ofSplit (G j).q).pr ((if pl j = PP then z else 0 : 𝓞 D.host.E) : D.host.E)) := fun j =>
    GlobalTheory.LevZero.lam_eq_of_red (G j) (pl j).1 (hG.idem j).1 (x j) _ (hx j) _
      (edgeSum_elem a b hab ⟨rfl, by simp only [a]; omega⟩ _).symm
  simp only [dif_pos hmem]
  rw [hchi, Units.coe_prod, Finset.prod_eq_single i (fun j _ hj => ?_) (by simp), hlam, if_pos hi]
  rw [hlam, if_neg (fun e => hj (pl.injective (e.trans hi.symm)))]
  simp [Place.pr]
set_option maxHeartbeats 1000000 in
theorem base_inv_alt_alt (W : _root_.GlobalTheory.MiS.RealPackAlt ex) {u : D.what₂.Word} (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0))
    {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
    (v : VCom f.c) (o : TDat f.c k ι) {n : ℕ} (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg) (hG : _root_.GlobalTheory.Fam.LocalGroupReading f G pl)
    (hB : _root_.GlobalTheory.MiTop.LocalBottomCompatibility f B v o G) (i : Fin n) : ∃ j₀ : Fin (Yc D 0).rank, j₀.val = D.R.k + D.R.rS ∧ ∀ r,
      toEAf D (G i).q.e * (((Formalism.IndefR.Lev.finE (Yc D 0) (f.g.b 0))⁻¹).val *ᵥ
        (fun r => algebraMap D.host.E (Formalism.IndefR.Lev.EAf D)
          (W.S.X.ιE (W.S.X.zR u (Fin.cast (rank_eq W.S.X W.Q.instEq) r))))) r =
      toEAf D ((G i).q.sec (((((G i).S.ϖ⁻¹ : (G i).kˣ) : (G i).k)) ^ (D.R.rS + 1))) * ((_root_.GlobalTheory.Fam.pk_z W).βY 0).val r j₀ := by
  have hs := (G i).hs
  have hodd := (G i).S.odd
  have hρ : D.R.rS = (G i).S.ρ := by unfold Ranks.rS; omega
  have h₀ : 0 + 2 * D.R.rS + 2 = D.R.m := by omega
  have he := (hG.idem i).1
  obtain ⟨μ, lam, hμ, hv, hτ⟩ := hB.norm
  have hsc := sc_mul_mu (G i) μ lam hμ o.ζ₀ hτ (hB.last i)
  obtain ⟨e, hord, hM⟩ := hG.frame i 0 ((G i).s + 1) (Nat.zero_add _)
  let p : Fin ((G i).s + 1) := ⟨D.R.rS, by omega⟩
  refine ⟨e (.inl (.inr p)), hord _, fun r => ?_⟩
  refine e_mul_of_prF (G i).q he _ _ _ ?_
  refine map_inv_mulVec ((G i).q.prF he) _ _ (fun r => ((_root_.GlobalTheory.Fam.pk_z W).βY 0).val r (e (.inl (.inr p)))) _ (fun r => ?_) r
  choose lf hlf using fun x : Formalism.IndefR.Datum.EAf D => GlobalTheory.ResLoc.toEAf_surj x
  have h1 := congrFun (congrFun (hM (((_root_.GlobalTheory.Fam.pk_z W).βY 0).val.map lf) (Matrix.ext fun a b => hlf _)) r) (e (.inl (.inr p)))
  have h2 : (G i).q.prF he (((Formalism.IndefR.Lev.finE (Yc D 0) (f.g.b 0)).val *ᵥ
      fun r => ((_root_.GlobalTheory.Fam.pk_z W).βY 0).val r (e (.inl (.inr p)))) r) =
      (ofSplit (G i).q).π ((Formalism.L2.Theta.mt (Yc D 0) (f.g.b 0) * ((_root_.GlobalTheory.Fam.pk_z W).βY 0).val.map lf) r (e (.inl (.inr p)))) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Matrix.mul_apply, map_sum, mulVec, dotProduct, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← hlf (((_root_.GlobalTheory.Fam.pk_z W).βY 0).val a _)]
    exact (congrArg ((G i).q.prF he) ((toEAf D).map_mul _ _).symm).trans ((G i).q.prF_toEAf he _)
  have h3 : (ofSplit (G i).q).π ((Formalism.L2.Theta.mt (Yc D 0) (f.g.b 0) * ((_root_.GlobalTheory.Fam.pk_z W).βY 0).val.map lf) r (e (.inl (.inr p)))) =
      ((G i).FY 0 ((G i).s + 1) (Nat.zero_add _)).β r (.inr p) * ((G i).S.ϖ : (G i).k) ^ (D.R.rS + 1) := by
    refine h1.trans ?_
    rw [submatrix_apply, Equiv.symm_apply_apply, GlobalTheory.LevZeroUp.bas_val, mul_diagonal]
    rw [GlobalTheory.StepData.standardOrderExtendedBasis_apply_low_block (Fin D.R.k) (Fin D.R.t) (l := (G i).s + 1) 0 ((G i).s + 1) (Nat.zero_add _) p]
    rfl
  have h4 := ((G i).bes 0 D.R.rS h₀ ((G i).s + 1) (Nat.zero_add _)).2.2.2.1 p rfl r
  have h5 : B.d.i₀ *ᵥ vecB B.o B.ζ = (f.c.B 0 D.R.rS h₀).d.i₀ *ᵥ vecB (f.c.B 0 D.R.rS h₀).o (f.c.B 0 D.R.rS h₀).ζ :=
    eq_of_heq (congr_arg_heq (fun B' : BesLev D D.R.rS => B'.d.i₀ *ᵥ vecB B'.o B'.ζ) (hB.lev h₀))
  rw [← h5, hv r] at h4
  have h6 : (G i).q.prF he (algebraMap D.host.E (Formalism.IndefR.Lev.EAf D)
      (W.S.X.ιE (W.S.X.zR u (Fin.cast (rank_eq W.S.X W.Q.instEq) r)))) =
      (ofSplit (G i).q).pr (W.S.X.ιE (W.S.X.zR u (Fin.cast (rank_eq W.S.X W.Q.instEq) r))) :=
    (G i).q.prF_toEAf he (incA D _)
  have h7 : ∀ x y, (ofSplit (G i).q).pr (x * y) = (ofSplit (G i).q).pr x * (ofSplit (G i).q).pr y := fun x y =>
    ((G i).q.pr.comp (incA D)).map_mul x y
  rw [h7, ← mul_assoc, hsc, one_mul] at h4
  rw [h6, h2, h3, h4, mul_comm, mul_assoc, ← mul_pow, Units.mul_inv, one_pow, mul_one]
theorem inv_mulVec_adelic_embedding_eq_self (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (hW : _root_.GlobalTheory.Fam.PackageHypotheses W) {u : D.what₂.Word} (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0))
    (g : GA D (D.sp.X 0)) :
    ((Formalism.IndefR.Lev.finE (D.sp.Y 0) (embA B.d B.o g))⁻¹).val *ᵥ (fun r => algebraMap D.host.E (Formalism.IndefR.Lev.EAf D)
      (W.S.X.ιE (W.S.X.zR u (Fin.cast (rank_eq W.S.X W.Q.instEq) r)))) =
      fun r => algebraMap D.host.E (Formalism.IndefR.Lev.EAf D) (W.S.X.ιE (W.S.X.zR u (Fin.cast (rank_eq W.S.X W.Q.instEq) r))) := by
  have h := GlobalTheory.MiTop.fixAux W.S.X W.Q.instEq hW.bot.idE (Formalism.L2.SG.PoincareInHH.PoincareSetting.fixSet W.S.X u) (W.S.X.zR u)
    (Or.inr rfl) (embA B.d B.o g)⁻¹ ((B.tieH _).1 ((embA B.d B.o).range.inv_mem ⟨g, rfl⟩))
  funext r
  rw [← map_inv]
  exact ((toEAf D).map_mulVec _ _ r).symm.trans (congrArg (toEAf D) (congrFun h r))
end GlobalTheory.MiTop.MoveZ
open GlobalTheory.MiTop.MoveZ in
set_option maxHeartbeats 1000000 in
theorem GlobalTheory.MiTop.base_moves_vector_z_alt_bis : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → 1 ≤ D.R.rS → ∀ PP ∈ (W.Q.Rl.dat0 (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true)).Pg, ∃ Γ : Fin (Yc D 0).rank → Formalism.IndefR.Lev.EAf D, ∀ u (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedAlt f B → ∀ a₀ a, _root_.GlobalTheory.MiTop.IsTranslate' f B a₀ a → ∃ (θ : Formalism.IndefR.Lev.EAf D) (hθ : θ ∈ Formalism.L2.Herm.intAf D.host.F D.host.E), Formalism.L2.DIV.resS D.host.F PP ⟨θ, hθ⟩ = 1 ∧ ∀ ei : AE D, Formalism.L2.NTheta.IsIdemAt ei PP → toEAf D ei • Matrix.mulVec (((Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from embA B.d B.o (a₀ * a) * (show GA D (D.sp.Y 0) from f.g.b 0))))⁻¹ : GL (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D)).val (fun r => algebraMap D.host.E (Formalism.IndefR.Lev.EAf D) (W.S.X.ιE (W.S.X.zR u (Fin.cast (rank_eq W.S.X W.Q.instEq) r)))) = toEAf D ei • (θ • Γ) := by
  intro D L hT Gi Gl Kc Yd cX ex W hW hr PP hPP
  obtain ⟨χ, hχ⟩ := _root_.GlobalTheory.MiTop.MoveZ.addChar_uniformizer_eq_chi_of_gRead W ⟨PP, hPP⟩
  by_cases hex : ∃ u, ∃ (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedAlt f B
  swap
  · exact ⟨0, fun u f B h => absurd ⟨u, f, B, h⟩ hex⟩
  obtain ⟨u₀, f₀, B₀, k₀, _, _, _, _, ι₀, v₀, o₀, n₀, G₀, pl₀, -, -, -, -, -, hG₀, hB₀⟩ := hex
  obtain ⟨i₀, hi₀⟩ := pl₀.surjective ⟨PP, hPP⟩
  have he₀ : Formalism.L2.NTheta.IsIdemAt (G₀ i₀).q.e PP := by have := (hG₀.idem i₀).1; rwa [hi₀] at this
  obtain ⟨j₀, hj₀, -⟩ := _root_.GlobalTheory.MiTop.MoveZ.base_inv_alt_alt W f₀ B₀ v₀ o₀ G₀ pl₀ hG₀ hB₀ i₀
  refine ⟨fun r => toEAf D ((G₀ i₀).q.sec (((((G₀ i₀).S.ϖ⁻¹ : (G₀ i₀).kˣ) : (G₀ i₀).k)) ^ (D.R.rS + 1))) *
    ((_root_.GlobalTheory.Fam.pk_z W).βY 0).val r j₀, ?_⟩
  rintro u f B ⟨k, _, _, _, _, ι, v, o, n, G, pl, -, -, -, -, -, hG, hB⟩ a₀ a -
  obtain ⟨i, hi⟩ := pl.surjective ⟨PP, hPP⟩
  have he : Formalism.L2.NTheta.IsIdemAt (G i).q.e PP := by have := (hG.idem i).1; rwa [hi] at this
  have hee : (G₀ i₀).q.e = (G i).q.e := GlobalTheory.LocMod.PinInhab.idem_unique he₀ he
  obtain ⟨j, hj, hz⟩ := _root_.GlobalTheory.MiTop.MoveZ.base_inv_alt_alt W f B v o G pl hG hB i
  obtain rfl : j = j₀ := Fin.ext (hj.trans hj₀.symm)
  have hrat := unif_ratio (G₀ i₀).q (G i).q he₀ hee (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (G₀ i₀).char (G i).char (G₀ i₀).S.cond _ _
    (G₀ i₀).S.unif (G i).S.unif fun z => (hχ u₀ f₀ v₀ n₀ G₀ pl₀ hG₀ i₀ hi₀ z).trans (hχ u f v n G pl hG i hi z).symm
  obtain ⟨θ, hθ, h1, h2⟩ := exists_theta (G₀ i₀).q he₀ _ (pow_sub_one_lt hrat (D.R.rS + 1))
  refine ⟨θ, hθ, h1, fun ei hei => ?_⟩
  obtain rfl : ei = (G i).q.e := GlobalTheory.LocMod.PinInhab.idem_unique hei he
  have h3 : toEAf D ((G i).q.sec (((((G i).S.ϖ⁻¹ : (G i).kˣ) : (G i).k)) ^ (D.R.rS + 1))) = toEAf D (G i).q.e * θ *
      toEAf D ((G₀ i₀).q.sec (((((G₀ i₀).S.ϖ⁻¹ : (G₀ i₀).kˣ) : (G₀ i₀).k)) ^ (D.R.rS + 1))) := by
    rw [← hee, h2, ← RingHom.map_mul, ← GlobalTheory.MiTop.MoveZ.sec_mul_sec, ← mul_pow, mul_right_comm, Units.mul_inv, one_mul, ← map_pow, sec_chg]
  have h4 : (((Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from embA B.d B.o (a₀ * a) *
      (show GA D (D.sp.Y 0) from f.g.b 0))))⁻¹ : GL (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D)).val =
      ((Formalism.IndefR.Lev.finE (Yc D 0) (f.g.b 0))⁻¹).val *
        ((Formalism.IndefR.Lev.finE (Yc D 0) (embA B.d B.o (a₀ * a)))⁻¹).val := by
    have := (Formalism.IndefR.Lev.finE (D.sp.Y 0)).map_mul (embA B.d B.o (a₀ * a)) (f.g.b 0)
    exact congrArg Units.val ((congrArg Inv.inv this).trans (_root_.mul_inv_rev _ _))
  funext r
  rw [h4, ← mulVec_mulVec]
  have h5 := _root_.GlobalTheory.MiTop.MoveZ.inv_mulVec_adelic_embedding_eq_self W hW B (a₀ * a)
  refine Eq.trans ?_ ((hz r).trans ?_)
  · exact congrArg (fun w => toEAf D (G i).q.e * (((Formalism.IndefR.Lev.finE (Yc D 0) (f.g.b 0))⁻¹).val *ᵥ w) r) h5
  · rw [h3, mul_assoc, mul_assoc]
    rfl
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AdelicEmbeddingInverseVectorStatement
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
theorem _root_.GlobalTheory.T.base_moves_vector_z_alt_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → 1 ≤ D.R.rS → ∀ PP ∈ (W.Q.Rl.dat0 (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true)).Pg, ∃ Γ : Fin (Yc D 0).rank → Formalism.IndefR.Lev.EAf D, ∀ u (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedAlt f B → ∀ a₀ a, _root_.GlobalTheory.MiTop.IsTranslate' f B a₀ a → ∃ (θ : Formalism.IndefR.Lev.EAf D) (hθ : θ ∈ Formalism.L2.Herm.intAf D.host.F D.host.E), Formalism.L2.DIV.resS D.host.F PP ⟨θ, hθ⟩ = 1 ∧ ∀ ei : AE D, Formalism.L2.NTheta.IsIdemAt ei PP → toEAf D ei • Matrix.mulVec (((Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from embA B.d B.o (a₀ * a) * (show GA D (D.sp.Y 0) from f.g.b 0))))⁻¹ : GL (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D)).val (fun r => algebraMap D.host.E (Formalism.IndefR.Lev.EAf D) (W.S.X.ιE (W.S.X.zR u (Fin.cast (rank_eq W.S.X W.Q.instEq) r)))) = toEAf D ei • (θ • Γ) := by
  first | exact @_root_.GlobalTheory.MiTop.base_moves_vector_z_alt_bis | exact _root_.GlobalTheory.MiTop.base_moves_vector_z_alt_bis | (intros; apply _root_.GlobalTheory.MiTop.base_moves_vector_z_alt_bis <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ResSEqOfFlag
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ResSEqOfFlag
set_option synthInstance.maxHeartbeats 200000

section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
namespace GlobalTheory.CongFlag
open Formalism.MainNotions.S _root_.Formalism.L2.SG.HidaSetting _root_.Formalism.L2.SG.Pf.unitaryCongruence
open scoped Matrix
end GlobalTheory.CongFlag
namespace GlobalTheory.CongFlag
open Formalism.MainNotions.S _root_.Formalism.L2.SG.HidaSetting
end GlobalTheory.CongFlag
namespace GlobalTheory.CongFlag
open Formalism.MainNotions.S _root_.Formalism.L2.SG.HidaSetting
open scoped Matrix
end GlobalTheory.CongFlag
namespace GlobalTheory.CongFlag
theorem resS_eq_of_flag_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → 1 ≤ D.R.rS → ∀ (u u' : D.what₂.Word) (κ : GA D (D.sp.Y 0)), κ ∈ rowJ W.S.X W.Q.instEq → ∀ (c c₂ : Formalism.IndefR.Lev.EAf D) (hc : c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (hc₂ : c₂ ∈ Formalism.L2.Herm.intAf D.host.F D.host.E), ∀ PP ∈ (W.Q.Rl.dat0 (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true)).Pg, (∀ ei : AE D, Formalism.L2.NTheta.IsIdemAt ei PP → toEAf D ei • (c • Matrix.mulVec (Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from κ)).val (Matrix.mulVec (((Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u'))))⁻¹ : GL (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D)).val (fun r => algebraMap D.host.E (Formalism.IndefR.Lev.EAf D) (W.S.X.ιE (W.S.X.zR u' (Fin.cast (rank_eq W.S.X W.Q.instEq) r)))))) = toEAf D ei • (c₂ • (Matrix.mulVec (((Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))))⁻¹ : GL (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D)).val (fun r => algebraMap D.host.E (Formalism.IndefR.Lev.EAf D) (W.S.X.ιE (W.S.X.zR u (Fin.cast (rank_eq W.S.X W.Q.instEq) r))))))) → Formalism.L2.DIV.resS D.host.F PP ⟨c, hc⟩ = Formalism.L2.DIV.resS D.host.F PP ⟨c₂, hc₂⟩ := by
  intro D L hT Gi Gl Kc Yd cX ex W hP _ u u' κ hκ c c₂ hc hc₂ PP hPP hEq
  have lev : (_root_.GlobalTheory.Fam.pk_z W).toLevCh.Is W.P.A3.A.μ0 := hP.bot.hyp.2.2.2.1.lev
  have hPP' : PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg := hPP
  have hg := (GlobalTheory.SeeConjRead.places_over_g (_root_.GlobalTheory.Fam.pk_z W) lev).1 PP hPP'
  obtain ⟨ei, hei⟩ := GlobalTheory.ParahoricLift.exists_isIdemAt (GlobalTheory.TypePlaces.not_isConjPl _ _ lev.Pg PP hPP' PP hPP')
  obtain ⟨hε, hε1⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D ei PP hei
  exact finiteRing_sq_sub_mul_sq_eq_of_card W.S.X W.Q.instEq hP.bot.idE u u' κ hκ c c₂ hc hc₂ PP hg (toEAf D ei) hε hε1 (hEq ei hei)
end GlobalTheory.CongFlag
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ResSEqOfFlagStatement
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
theorem _root_.GlobalTheory.T.row_level_integral_twist_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → 1 ≤ D.R.rS → ∀ (u u' : D.what₂.Word) (κ : GA D (D.sp.Y 0)), κ ∈ rowJ W.S.X W.Q.instEq → ∀ (c c₂ : Formalism.IndefR.Lev.EAf D) (hc : c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (hc₂ : c₂ ∈ Formalism.L2.Herm.intAf D.host.F D.host.E), ∀ PP ∈ (W.Q.Rl.dat0 (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true)).Pg, (∀ ei : AE D, Formalism.L2.NTheta.IsIdemAt ei PP → toEAf D ei • (c • Matrix.mulVec (Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from κ)).val (Matrix.mulVec (((Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u'))))⁻¹ : GL (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D)).val (fun r => algebraMap D.host.E (Formalism.IndefR.Lev.EAf D) (W.S.X.ιE (W.S.X.zR u' (Fin.cast (rank_eq W.S.X W.Q.instEq) r)))))) = toEAf D ei • (c₂ • (Matrix.mulVec (((Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))))⁻¹ : GL (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D)).val (fun r => algebraMap D.host.E (Formalism.IndefR.Lev.EAf D) (W.S.X.ιE (W.S.X.zR u (Fin.cast (rank_eq W.S.X W.Q.instEq) r))))))) → Formalism.L2.DIV.resS D.host.F PP ⟨c, hc⟩ = Formalism.L2.DIV.resS D.host.F PP ⟨c₂, hc₂⟩ := by
  first | exact @_root_.GlobalTheory.CongFlag.resS_eq_of_flag_alt | exact _root_.GlobalTheory.CongFlag.resS_eq_of_flag_alt | (intros; apply _root_.GlobalTheory.CongFlag.resS_eq_of_flag_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CentralRatioRedEqOne
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
namespace GlobalTheory.MiTop
set_option maxHeartbeats 2000000 in
theorem centralRatio_red_eq_one_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → 1 ≤ D.R.rS → ∀ u u' (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (f' : _root_.GlobalTheory.Fam.FamilyCharacter W u') (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) (B' : SBes W.S.X W.Q.instEq u' W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedConditions f B → _root_.GlobalTheory.MiTop.PlacedConditions f' B' → ∀ a₀ a a₀' a', _root_.GlobalTheory.MiTop.IsTranslate' f B a₀ a → _root_.GlobalTheory.MiTop.IsTranslate' f' B' a₀' a' → ∀ z ∈ GfC (D.sp.Y 0), z ∈ Subgroup.center (GA D (D.sp.Y 0)) → ∀ k ∈ _root_.GlobalTheory.MiTop.rJ_z W, _root_.GlobalTheory.MiTop.translationElement f B a₀ a = z * _root_.GlobalTheory.MiTop.translationElement f' B' a₀' a' * k → ∀ PP ∈ (W.Q.Rl.dat0 (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true)).Pg, Formalism.L2.DIV.redFn (W.Q.Rl.βY 0) PP (Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from z)) = 1 := by
  intro D L hT Gi Gl Kc Yd cX ex W hP hr u u' f f' B B' hPl hPl' a₀ a a₀' a' hA hA' z hzf hzc k hk heq PP hPP
  classical
  by_cases hS : Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from z) ∈ Formalism.L2.DIV.St (W.Q.Rl.βY 0)
  swap
  · unfold Formalism.L2.DIV.redFn Formalism.L2.DIV.ext1
    rw [dite_eq_right hS]
  rcases Nat.eq_zero_or_pos (Yc D 0).rank with h0 | hpos
  · apply Units.ext; ext i; exact absurd i.2 (by omega)
  obtain ⟨c, hc⟩ := GlobalTheory.T.center_adelicUnitaryGroup_finitePart_scalar (Yc D 0) (show GA D (Yc D 0) from z) hzc hzf
  obtain ⟨hci, hfin⟩ := redFn_scalar_eq_one (W.Q.Rl.βY 0) PP _ c hS hc ⟨0, hpos⟩
  apply hfin
  obtain ⟨-, hconj⟩ := hA'.2.2.2
  have hκ : _root_.GlobalTheory.MiTop.translationElement f' B' a₀' a' * k * (_root_.GlobalTheory.MiTop.translationElement f' B' a₀' a')⁻¹ ∈ rowJ W.S.X W.Q.instEq := by
    have := ((hconj k).1).1 hk
    simpa using this
  obtain ⟨Γ, hΓ⟩ := _root_.GlobalTheory.T.base_moves_vector_z_alt_alt W hP hr PP hPP
  obtain ⟨θ, hθ, hθ1, hm⟩ := hΓ u f B (by first | exact hPl | exact _root_.GlobalTheory.MiTop.PlacedConditions.placed f B hPl) a₀ a hA
  obtain ⟨θ', hθ', hθ1', hm'⟩ := hΓ u' f' B' (by first | exact hPl' | exact _root_.GlobalTheory.MiTop.PlacedConditions.placed f' B' hPl') a₀' a' hA'
  have hmul : ∀ x y : GA D (D.sp.Y 0), Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from (x * y : GA D (D.sp.Y 0))) =
      Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from x) * Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from y) :=
    fun x y => map_mul (Formalism.IndefR.Lev.finE (Yc D 0)) x y
  have hinv : ∀ x : GA D (D.sp.Y 0), Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from (x⁻¹ : GA D (D.sp.Y 0))) =
      (Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from x))⁻¹ :=
    fun x => map_inv (Formalism.IndefR.Lev.finE (Yc D 0)) x
  have ht : ∀ (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) a₀ a,
      Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from _root_.GlobalTheory.MiTop.translationElement f B a₀ a) =
        (Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u)))⁻¹ *
          Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from embA B.d B.o (a₀ * a) * (show GA D (D.sp.Y 0) from f.g.b 0)) := by
    intro u f B a₀ a
    unfold _root_.GlobalTheory.MiTop.translationElement
    rw [mul_assoc, hmul, hinv]
  have hT := congrArg (fun g : GA D (D.sp.Y 0) => Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from g)) heq
  simp only [hmul, ht] at hT
  have hcong := _root_.GlobalTheory.T.row_level_integral_twist_alt W hP hr u u' _ hκ (θ * c) θ' (Subring.mul_mem _ hθ hci) hθ' PP hPP (fun ei hei => by
    have key := lattice_ratio_vector_of_scalar_factorisation (toEAf D ei) c θ θ' _ _ _ _ _ _ hc hT _ _ Γ (hm ei hei) (hm' ei hei)
    have hκE : Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from (_root_.GlobalTheory.MiTop.translationElement f' B' a₀' a' * k * (_root_.GlobalTheory.MiTop.translationElement f' B' a₀' a')⁻¹ : GA D (D.sp.Y 0))) =
        Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from _root_.GlobalTheory.MiTop.translationElement f' B' a₀' a') * Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from k) *
          (Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from _root_.GlobalTheory.MiTop.translationElement f' B' a₀' a'))⁻¹ :=
      ((map_mul (Formalism.IndefR.Lev.finE (Yc D 0)) _ _).trans (congrArg₂ (· * ·) (map_mul (Formalism.IndefR.Lev.finE (Yc D 0)) _ _)
        (map_inv (Formalism.IndefR.Lev.finE (Yc D 0)) _)))
    rw [ht u' f' B' a₀' a'] at hκE
    rw [← hκE] at key
    exact key)
  have e1 : (⟨θ * c, Subring.mul_mem _ hθ hci⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = ⟨θ, hθ⟩ * ⟨c, hci⟩ := rfl
  rw [e1, map_mul, hθ1, hθ1', one_mul] at hcong
  exact hcong
end GlobalTheory.MiTop
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CentralRatioRedEqOneStatement
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
theorem _root_.GlobalTheory.T.placed_bessel_pair_identity_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → 1 ≤ D.R.rS → ∀ u u' (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (f' : _root_.GlobalTheory.Fam.FamilyCharacter W u') (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) (B' : SBes W.S.X W.Q.instEq u' W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedConditions f B → _root_.GlobalTheory.MiTop.PlacedConditions f' B' → ∀ a₀ a a₀' a', _root_.GlobalTheory.MiTop.IsTranslate' f B a₀ a → _root_.GlobalTheory.MiTop.IsTranslate' f' B' a₀' a' → ∀ z ∈ GfC (D.sp.Y 0), z ∈ Subgroup.center (GA D (D.sp.Y 0)) → ∀ k ∈ _root_.GlobalTheory.MiTop.rJ_z W, _root_.GlobalTheory.MiTop.translationElement f B a₀ a = z * _root_.GlobalTheory.MiTop.translationElement f' B' a₀' a' * k → ∀ PP ∈ (W.Q.Rl.dat0 (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true)).Pg, Formalism.L2.DIV.redFn (W.Q.Rl.βY 0) PP (Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from z)) = 1 := by
  first | exact @_root_.GlobalTheory.MiTop.centralRatio_red_eq_one_alt | exact _root_.GlobalTheory.MiTop.centralRatio_red_eq_one_alt | (intros; apply _root_.GlobalTheory.MiTop.centralRatio_red_eq_one_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MatchingCoset
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
namespace GlobalTheory.MiTop
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
theorem mem_rJ_of_red_alt (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (z : GA D (D.sp.Y 0)) (hz : z ∈ GfC (D.sp.Y 0))
    (hS : Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from z) ∈ Formalism.L2.DIV.St (W.Q.Rl.βY 0))
    (hR : ∀ PP ∈ (W.Q.Rl.dat0 (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true)).Pg,
      Formalism.L2.DIV.redFn (W.Q.Rl.βY 0) PP (Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from z)) = 1) :
    z ∈ _root_.GlobalTheory.MiTop.rJ_z W := by
  refine ⟨hz, ?_⟩
  refine GlobalTheory.LevSplit.mem_lev_of_red _ _ _ _ _ (GlobalTheory.LevSplit.finE_mem_UA _ _) hS ?_
  rintro PP (hP | hP)
  · exact hR PP hP
  · exact absurd hP (Finset.notMem_empty _)
theorem reduced_character_conj_eq_of_mem_level_group (W : _root_.GlobalTheory.MiS.RealPackAlt ex) {k κ : GA D (D.sp.Y 0)} (hk : k ∈ _root_.GlobalTheory.MiTop.rJ_z W) (hκ : κ ∈ _root_.GlobalTheory.MiTop.rJ_z W) :
    _root_.GlobalTheory.MiTop.realCharacter W (k * κ * k⁻¹) = _root_.GlobalTheory.MiTop.realCharacter W κ := by
  have h1 : Formalism.IndefR.Lev.finE (Yc D 0) k ∈ Formalism.L2.DIV.lev D.sp.cm (Yc D 0).gram (W.Q.Rl.βY 0) (W.Q.Rl.dat0 (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true)) := hk.2
  have h2 : Formalism.IndefR.Lev.finE (Yc D 0) κ ∈ Formalism.L2.DIV.lev D.sp.cm (Yc D 0).gram (W.Q.Rl.βY 0) (W.Q.Rl.dat0 (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true)) := hκ.2
  have e := levFn_conj D.sp.cm (Yc D 0).gram (W.Q.Rl.βY 0) (W.Q.Rl.dat0 (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true)) h1 h2
  unfold _root_.GlobalTheory.MiTop.realCharacter Formalism.IndefR.Lev.levChi
  erw [map_mul, map_mul, map_inv, e]
theorem mem_rJ_iff_conj_mem (W : _root_.GlobalTheory.MiS.RealPackAlt ex) {k κ : GA D (D.sp.Y 0)} (hk : k ∈ _root_.GlobalTheory.MiTop.rJ_z W) : κ ∈ _root_.GlobalTheory.MiTop.rJ_z W ↔ k * κ * k⁻¹ ∈ _root_.GlobalTheory.MiTop.rJ_z W := by
  have := (Subgroup.mul_mem_cancel_right (Formalism.IndefR.Lev.levG (Yc D 0) (W.Q.Rl.βY 0) (W.Q.Rl.dat0 (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true))) (y := k * κ) (Subgroup.inv_mem _ hk)).trans
    (Subgroup.mul_mem_cancel_left (Formalism.IndefR.Lev.levG (Yc D 0) (W.Q.Rl.βY 0) (W.Q.Rl.dat0 (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true))) (y := κ) hk)
  exact this.symm
theorem matches_mul_of_mem_rJ (W : _root_.GlobalTheory.MiS.RealPackAlt ex) {z t k : GA D (D.sp.Y 0)} (hzf : z ∈ GfC (D.sp.Y 0))
    (hzc : z ∈ Subgroup.center (GA D (D.sp.Y 0))) (hk : k ∈ _root_.GlobalTheory.MiTop.rJ_z W) (ht : Matches W.S.X W.Q.instEq (_root_.GlobalTheory.MiTop.rJ_z W) (_root_.GlobalTheory.MiTop.realCharacter W) t) :
    Matches W.S.X W.Q.instEq (_root_.GlobalTheory.MiTop.rJ_z W) (_root_.GlobalTheory.MiTop.realCharacter W) (z * t * k) := by
  have hkf : k ∈ GfC (D.sp.Y 0) := hk.1
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hzf ht.1) hkf, fun κ => ?_⟩
  have hz := Subgroup.mem_center_iff.mp hzc
  have hc : (z * t * k)⁻¹⁻¹ * κ * (z * t * k)⁻¹ = t⁻¹⁻¹ * (k * κ * k⁻¹) * t⁻¹ := by
    have e : (z * t * k)⁻¹⁻¹ * κ * (z * t * k)⁻¹ = z * (t⁻¹⁻¹ * (k * κ * k⁻¹) * t⁻¹) * z⁻¹ := by group
    rw [e, ← hz, mul_inv_cancel_right]
  obtain ⟨h1, h2⟩ := ht.2 (k * κ * k⁻¹)
  rw [hc]
  refine ⟨(_root_.GlobalTheory.MiTop.mem_rJ_iff_conj_mem W hk).trans h1, fun hκ => ?_⟩
  rw [h2 ((_root_.GlobalTheory.MiTop.mem_rJ_iff_conj_mem W hk).1 hκ), _root_.GlobalTheory.MiTop.reduced_character_conj_eq_of_mem_level_group W hk hκ]
theorem matching_coset_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → 1 ≤ D.R.rS → ∀ u u' (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (f' : _root_.GlobalTheory.Fam.FamilyCharacter W u') (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) (B' : SBes W.S.X W.Q.instEq u' W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedConditions f B → _root_.GlobalTheory.MiTop.PlacedConditions f' B' → GlobalTheory.MiTop.Framed B → GlobalTheory.MiTop.Framed B' → ∀ a₀ a a₀' a', _root_.GlobalTheory.MiTop.IsTranslate' f B a₀ a → _root_.GlobalTheory.MiTop.IsTranslate' f' B' a₀' a' → ∃ a₁, _root_.GlobalTheory.MiTop.IsTranslate' f B a₀ a₁ ∧ ∃ k ∈ _root_.GlobalTheory.MiTop.rJ_z W, _root_.GlobalTheory.MiTop.translationElement f B a₀ a₁ = _root_.GlobalTheory.MiTop.translationElement f' B' a₀' a' * k := by
  intro D L hT Gi Gl Kc Yd cX ex W hW hr u u' f f' B B' hP hP' hF hF' a₀ a a₀' a' hA hA'
  obtain ⟨z, hzf, hzc, c, hcf, hcc, k, hk, he⟩ :=
    _root_.GlobalTheory.T.matching_translates_bottom_alt W hW.bot hr u B (_root_.GlobalTheory.MiTop.translationElement f B a₀ a) hA.2.2.2.1 (_root_.GlobalTheory.MiTop.translationElement f' B' a₀' a') hA'.2.2.2.1 hA.2.2.2 hA'.2.2.2
  have hcc' := Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hcc)
  have hX : _root_.GlobalTheory.MiTop.translationElement f B a₀ (a * c⁻¹) = ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))⁻¹ * embA B.d B.o c⁻¹ *
      (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) * _root_.GlobalTheory.MiTop.translationElement f B a₀ a := by
    unfold _root_.GlobalTheory.MiTop.translationElement
    rw [show a₀ * (a * c⁻¹) = c⁻¹ * (a₀ * a) by rw [← hcc' (a₀ * a), mul_assoc], map_mul]
    have key : ∀ {G : Type} [Group G] (x e y b : G), x⁻¹ * (e * y) * b = x⁻¹ * e * x * (x⁻¹ * y * b) := by
      intros; group
    exact key (G := GA D (D.sp.Y 0)) _ _ _ _
  have e1 : _root_.GlobalTheory.MiTop.translationElement f B a₀ (a * c⁻¹) = z * _root_.GlobalTheory.MiTop.translationElement f' B' a₀' a' * k := by
    rw [hX, he, map_inv]
    simp only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left]
  have hA₁ : _root_.GlobalTheory.MiTop.IsTranslate' f B a₀ (a * c⁻¹) := by
    refine ⟨hA.1, Subgroup.mul_mem _ hA.2.1 (Subgroup.inv_mem _ hcf),
      Subgroup.mul_mem _ hA.2.2.1 (Subgroup.inv_mem _ hcc), ?_⟩
    rw [e1]
    exact _root_.GlobalTheory.MiTop.matches_mul_of_mem_rJ W hzf hzc hk hA'.2.2.2
  have hz : z ∈ _root_.GlobalTheory.MiTop.rJ_z W := _root_.GlobalTheory.MiTop.mem_rJ_of_red_alt W z hzf
    (by first
      | exact _root_.GlobalTheory.T.placed_bessel_pair_relation_alt W hW hr u u' f f' B B' hP hP' hF hF' a₀ (a * c⁻¹) a₀' a' hA₁ hA' z hzf hzc k hk e1
      | exact _root_.GlobalTheory.T.placed_bessel_pair_relation_alt W hW hr u u' f f' B B' hP hP' a₀ (a * c⁻¹) a₀' a' hA₁ hA' z hzf hzc k hk e1)
    (by first
      | exact _root_.GlobalTheory.T.placed_bessel_pair_identity_alt W hW hr u u' f f' B B' hP hP' hF hF' a₀ (a * c⁻¹) a₀' a' hA₁ hA' z hzf hzc k hk e1
      | exact _root_.GlobalTheory.T.placed_bessel_pair_identity_alt W hW hr u u' f f' B B' hP hP' a₀ (a * c⁻¹) a₀' a' hA₁ hA' z hzf hzc k hk e1)
  refine ⟨a * c⁻¹, hA₁, z * k, Subgroup.mul_mem _ hz hk, ?_⟩
  rw [e1, ← (Subgroup.mem_center_iff.mp hzc (_root_.GlobalTheory.MiTop.translationElement f' B' a₀' a')), mul_assoc]
end GlobalTheory.MiTop
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MatchingCosetStatement
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
theorem _root_.GlobalTheory.T.placed_bessel_compatibility_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → 1 ≤ D.R.rS → ∀ u u' (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (f' : _root_.GlobalTheory.Fam.FamilyCharacter W u') (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) (B' : SBes W.S.X W.Q.instEq u' W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedConditions f B → _root_.GlobalTheory.MiTop.PlacedConditions f' B' → GlobalTheory.MiTop.Framed B → GlobalTheory.MiTop.Framed B' → ∀ a₀ a a₀' a', _root_.GlobalTheory.MiTop.IsTranslate' f B a₀ a → _root_.GlobalTheory.MiTop.IsTranslate' f' B' a₀' a' → ∃ a₁, _root_.GlobalTheory.MiTop.IsTranslate' f B a₀ a₁ ∧ ∃ k ∈ _root_.GlobalTheory.MiTop.rJ_z W, _root_.GlobalTheory.MiTop.translationElement f B a₀ a₁ = _root_.GlobalTheory.MiTop.translationElement f' B' a₀' a' * k := by
  first | exact @_root_.GlobalTheory.MiTop.matching_coset_alt | exact _root_.GlobalTheory.MiTop.matching_coset_alt | (intros; apply _root_.GlobalTheory.MiTop.matching_coset_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OneCentralPin
set_option synthInstance.maxHeartbeats 200000

section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
theorem GlobalTheory.MiTop.matches_mul_of_mem_rJ' {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex)
    {t k : GA D (D.sp.Y 0)} (ht : Matches W.S.X W.Q.instEq (_root_.GlobalTheory.MiTop.rJ_z W) (_root_.GlobalTheory.MiTop.realCharacter W) t) (hk : k ∈ _root_.GlobalTheory.MiTop.rJ_z W) :
    Matches W.S.X W.Q.instEq (_root_.GlobalTheory.MiTop.rJ_z W) (_root_.GlobalTheory.MiTop.realCharacter W) (t * k) := by
  refine ⟨mul_mem ht.1 hk.1, fun j => ?_⟩
  have hc := GlobalTheory.MiTop.conj_in_level (G := GA D (D.sp.Y 0))
    (Lev.levG (Yc D 0) (W.Q.Rl.βY 0) (W.Q.Rl.dat0 (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true))) (_root_.GlobalTheory.MiTop.realCharacter W)
    (fun a ha b hb => GlobalTheory.MiTop.levChi_mul_lev _ _ _ ha hb) (fun a => Lev.levChi_ne_zero _ _) hk j
  have h2 := ht.2 (k * j * k⁻¹)
  have e : (t⁻¹)⁻¹ * (k * j * k⁻¹) * t⁻¹ = ((t * k)⁻¹)⁻¹ * j * (t * k)⁻¹ := by group
  rw [e] at h2
  exact ⟨hc.1.trans h2.1, fun hj => (h2.2 (hc.1.1 hj)).trans (hc.2 hj)⟩
theorem GlobalTheory.MiTop.exists_botDat_pin_of_placed_of_framed : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → 1 ≤ D.R.rS → ∃ z ∈ GfC (D.sp.Y 0), z ∈ Subgroup.center (GA D (D.sp.Y 0)) ∧ ∀ u (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedConditions f B → GlobalTheory.MiTop.Framed B → ∃ d : _root_.GlobalTheory.MiTop.BottomData W u, d.B = B ∧ d.b = (show GA D (D.sp.Y 0) from f.g.b 0) ∧ d.Pin z := by
  intro D L hT Gi Gl Kc Yd cX ex W hP hr
  classical
  by_cases hex : ∃ (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedConditions f B ∧ Framed B
  · obtain ⟨u₀, f₀, B₀, hpl₀, hF₀⟩ := hex
    obtain ⟨a₀, a, hAt⟩ := _root_.GlobalTheory.T.exists_isAt_of_placed_framed W hP u₀ f₀ B₀ (by first | exact _root_.GlobalTheory.MiTop.PlacedConditions.placed _ _ hpl₀ | exact hpl₀) hF₀
    have hm := _root_.GlobalTheory.MiTop.botHyp_match_alt W hP.bot
    have hS : Matches W.S.X W.Q.instEq (_root_.GlobalTheory.MiTop.rJ_z W) (_root_.GlobalTheory.MiTop.realCharacter W) (show GA D (D.sp.Y 0) from W.Q.tS) := by
      have h1 := hm.2.2.2.1 1 (one_mem _) (one_mem _)
      rwa [one_mul] at h1
    obtain ⟨z, hzf, hzc, c, hcf, hcc, k₀, hk₀, ht⟩ :=
      _root_.GlobalTheory.T.matching_translates_bottom_alt W hP.bot hr u₀ B₀ _ hAt.2.2.2.1 _ hS.1 hAt.2.2.2 hS
    have ht₀ : _root_.GlobalTheory.MiTop.translationElement f₀ B₀ a₀ (c⁻¹ * a) = z * (show GA D (D.sp.Y 0) from W.Q.tS) * k₀ := by
      have hc : a₀ * (c⁻¹ * a) = c⁻¹ * (a₀ * a) := by
        rw [← mul_assoc, Subgroup.mem_center_iff.1 (inv_mem hcc) a₀, mul_assoc]
      unfold _root_.GlobalTheory.MiTop.translationElement at ht ⊢
      rw [hc, map_mul, map_inv]
      generalize (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u₀) = x at ht ⊢
      generalize embA B₀.d B₀.o (a₀ * a) = p at ht ⊢
      generalize embA B₀.d B₀.o c = q at ht ⊢
      generalize (show GA D (D.sp.Y 0) from f₀.g.b 0) = b at ht ⊢
      generalize (show GA D (D.sp.Y 0) from W.Q.tS) = s at ht ⊢
      calc x⁻¹ * (q⁻¹ * p) * b = x⁻¹ * q⁻¹ * x * (x⁻¹ * p * b) := by group
        _ = z * s * k₀ := by rw [ht]; group
    have hAt₀ : _root_.GlobalTheory.MiTop.IsTranslate' f₀ B₀ a₀ (c⁻¹ * a) := by
      refine ⟨hAt.1, mul_mem (inv_mem hcf) hAt.2.1, mul_mem (inv_mem hcc) hAt.2.2.1, ?_⟩
      rw [ht₀]
      exact _root_.GlobalTheory.MiTop.matches_mul_of_mem_rJ' W (hm.2.2.2.1 z hzf hzc) hk₀
    refine ⟨z, hzf, hzc, fun u f B hpl hF => ?_⟩
    obtain ⟨b₀, b, hAt'⟩ := _root_.GlobalTheory.T.exists_isAt_of_placed_framed W hP u f B (by first | exact _root_.GlobalTheory.MiTop.PlacedConditions.placed _ _ hpl | exact hpl) hF
    obtain ⟨a₁, hAt1, k, hk, hkt⟩ := _root_.GlobalTheory.T.placed_bessel_compatibility_alt W hP hr u u₀ f f₀ B B₀ hpl hpl₀ hF hF₀ b₀ b a₀ _ hAt' hAt₀
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hBT, _⟩ := hpl
    refine ⟨⟨B, (show GA D (D.sp.Y 0) from f.g.b 0), b₀, a₁, k₀ * k⟩, rfl, rfl,
      ⟨hBT.adapted, hAt1.1, hAt1.2.1, hAt1.2.2.1, ?_, ?_⟩⟩
    · exact (Formalism.IndefR.Lev.levG _ _ _).mul_mem hk₀ hk
    · have e := hkt
      rw [ht₀] at e
      unfold _root_.GlobalTheory.MiTop.translationElement at e
      show embA B.d B.o (b₀ * a₁) * (show GA D (D.sp.Y 0) from f.g.b 0) =
        (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) * (z * (show GA D (D.sp.Y 0) from W.Q.tS) * (k₀ * k))
      have e' : ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))⁻¹ *
          (embA B.d B.o (b₀ * a₁) * (show GA D (D.sp.Y 0) from f.g.b 0)) =
          z * (show GA D (D.sp.Y 0) from W.Q.tS) * k₀ * k := by
        rw [← mul_assoc]; exact e
      rw [← mul_assoc (z * _) k₀ k, ← e', mul_inv_cancel_left]
  · exact ⟨1, one_mem _, one_mem _, fun u f B hpl hF => (hex ⟨u, f, B, hpl, hF⟩).elim⟩
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OneCentralPinStatement
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
theorem _root_.GlobalTheory.T.exists_botDat_of_placedP_framed : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → 1 ≤ D.R.rS → ∃ z ∈ GfC (D.sp.Y 0), z ∈ Subgroup.center (GA D (D.sp.Y 0)) ∧ ∀ u (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedConditions f B → GlobalTheory.MiTop.Framed B → ∃ d : _root_.GlobalTheory.MiTop.BottomData W u, d.B = B ∧ d.b = (show GA D (D.sp.Y 0) from f.g.b 0) ∧ d.Pin z := by
  first | exact @_root_.GlobalTheory.MiTop.exists_botDat_pin_of_placed_of_framed | exact _root_.GlobalTheory.MiTop.exists_botDat_pin_of_placed_of_framed | (intros; apply _root_.GlobalTheory.MiTop.exists_botDat_pin_of_placed_of_framed <;> assumption)
end
end
