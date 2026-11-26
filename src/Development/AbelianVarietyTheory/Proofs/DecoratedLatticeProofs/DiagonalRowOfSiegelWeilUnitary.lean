module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsFinCombOfIsThetaAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowAmplitudeBoundsUniformSingletonWidth
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalBesselJFactorAllWordsOfGap
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabiliserCovolumeRelevantTermLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsPosTypeP
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmallOnUnivUnconditional
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CollSOn
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneLeSizeZ
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EquivIntegral
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CntClLeEncardMul
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeanPrimitiveCorankOneSublatticesBound
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowPositivityOfSiegelWeil
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OneOnSingletonOfSiegelWeil

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KernelExpansionAbsoluteConvergenceEqualWords
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KernelExpansionAbsoluteConvergenceEqualWords
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 GlobalTheory.Core.Diag GlobalTheory.Core.Deg

namespace GlobalTheory.Core.Diag

theorem kExp_absConv_tied : Formalism.L2.SG.ThmSOwn.KExpTied ∧ AbsConvTied :=
  ⟨Formalism.L2.SG.ThmSOwn.kExpTied_of_full Formalism.L2.SG.Closed.FoldOKC_outright Formalism.L2.SG.Closed.InHHC_holds
            Formalism.L2.SG.Closed.FundExistsC_holds Formalism.L2.SG.Closed.OOIntAllC_outright Formalism.L2.SG.Closed.OOFundIndepC_holds
            Formalism.L2.SG.Closed.AmpWellDefC_holds Formalism.L2.SG.Closed.AbsConvC_outright Formalism.L2.SG.Closed.KExpansionC_holds,
    Formalism.L2.SG.RowsConc.absConvTied_of_full Formalism.L2.SG.Closed.FoldOKC_outright Formalism.L2.SG.Closed.FundExistsC_holds
      Formalism.L2.SG.Closed.OOIntAllC_outright Formalism.L2.SG.Closed.AbsConvC_outright⟩

end GlobalTheory.Core.Diag
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KernelExpansionAbsoluteConvergenceEqualWordsStatement
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 GlobalTheory.Core.Diag GlobalTheory.Core.Deg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_expansion_absolute_convergence_equal_words : Formalism.L2.SG.ThmSOwn.KExpTied ∧ AbsConvTied := by
  first | exact @GlobalTheory.Core.Diag.kExp_absConv_tied | exact GlobalTheory.Core.Diag.kExp_absConv_tied | (intros; apply GlobalTheory.Core.Diag.kExp_absConv_tied <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CorankOnePairsFamilyBoundsOfSiegelWeil
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CorankOnePairsFamilyBoundsOfSiegelWeil
namespace GlobalTheory.Core.Diag

theorem oneOn_singleton_of_siegelWeil :
    HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent →
      ∀ c : ℝ, GlobalTheory.Core.Diag.OneOn {c} true ∧ GlobalTheory.Core.Diag.OneOn {c} false :=
  fun h => oneOn_singleton_of_siegelWeil_of_stepChoice h
    (GlobalTheory.St.stepChoiceDataC_of_siegelWeil_inInfinity h (fun _ X u u' hg =>
      Formalism.L2.SG.RealObj.EnergyConvJ.BM.realObj_inInfinityX_jsz
        CompanionTheory.Lime.BM.uniqGap_holds hg X u u' 1 one_pos))
    Formalism.MainStatements.RowRest.bDat_theoremB_global (GlobalTheory.rowNGP_of_siegelWeil h)

end GlobalTheory.Core.Diag
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CorankOnePairsFamilyBoundsOfSiegelWeilStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.corankOnePairsFamilyBounds_of_siegelWeil : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → ∀ c : ℝ, GlobalTheory.Core.Diag.OneOn {c} true ∧ GlobalTheory.Core.Diag.OneOn {c} false := by
  first | exact @GlobalTheory.Core.Diag.oneOn_singleton_of_siegelWeil | exact GlobalTheory.Core.Diag.oneOn_singleton_of_siegelWeil | (intros; apply GlobalTheory.Core.Diag.oneOn_singleton_of_siegelWeil <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DegenerateTermsAndCollisionBoundsUniformWidths
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTermLoopOfStandingHypotheses
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Core.Deg.exists_termLoop_of_standingHypotheses : ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (sOf hF)) (u : D.what₂.Word) (C' Cl Cg cb Cu cT CT : ℝ), 29 ≤ C' → 72 ≤ Cl → Ties D → StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT → ConcTie X Y → ∃ (W : WittDat X) (H : TieHyp W hI) (Am : AmpDat X) (hV : PvalForm W hI Am) (Z : LoopTie D large₂ (termTieOf W hI H Am hV) u u 1), TieAt hF hI large₂ u (termTieOf W hI H Am hV) Z ∧ ∀ t, Z.volR t = Formalism.L2.SG.LoopTerm.volRC hI t := by
  intro D large₂ X Y hF hI u C' Cl Cg cb Cu cT CT hC' hCl hT hS hCT
  haveI : Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow := ⟨GlobalTheory.DecTransport.decLow_holds⟩
  haveI : Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc := ⟨GlobalTheory.Sloc.CoefWeighted.coefWeightedLoc_uncond⟩
  have hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D := Formalism.L2.SG.ThmSOwn.gap_hypothesis_of_hypotheses hS (by linarith) hC'
  have hWD : Formalism.L2.SG.WuDecay.WuDecay X := hCT.2.2.2.2.1
  haveI : Nonempty D.what₂.Word := ⟨u⟩
  obtain ⟨C⟩ := Formalism.L2.SG.Pf.choiceExists X 1 one_pos
  have hB : Formalism.L2.SG.LocWSOf.WuBessel C := Formalism.L2.SG.Pf.wuBesselOfLoc_all C hG GlobalTheory.uniqGap_and_besselOfW.2
    (Formalism.L2.SG.Pf.LocF.locFactor_holds hG C) (fun τ => Formalism.L2.SG.Pf.dsTr C τ) (fun τ => Formalism.L2.SG.Pf.haarTr C τ)
    (fun w τ => Formalism.L2.SG.Pf.colsTypeTr C w τ)
  have hW : ∀ τ, GoodW D τ u u 1 (Formalism.L2.SG.LocWSOf.locW C u u τ) := fun τ =>
    Formalism.L2.SG.LocWSOf.goodW_of C u u τ (Formalism.L2.SG.Pf.colsTypeTr C u τ) (Formalism.L2.SG.Pf.colsTypeTr C u τ)
      (Formalism.L2.SG.Pf.zTr C u τ) (Formalism.L2.SG.Pf.zTr C u τ) (Formalism.L2.SG.Pf.haarTr C τ)
  have hSS : ∀ τ, GoodS D (lamD D τ) (Formalism.L2.SG.LocWSOf.locS hB u u τ) := fun τ =>
    Formalism.L2.SG.LocWSOf.goodS_of hB u u τ (Formalism.L2.SG.Pf.goodSRest_all hG hT.dsig_tie hB u u τ)
  have hwin : normWin D large₂ 1 1 := Formalism.L2.SG.Pf.LoopBTheta.normWin_one large₂ zero_le_one
  have hCF : Formalism.L2.SG.Pf.LoopBCovN.CovNFormula := GlobalTheory.T.covolume_unipotentIntegral_normalisedHaar
  have hup : Formalism.L2.SG.Pf.LoopBCovN.eN D * Real.log (2 * D.host.v) ≤
      1 * (D.R.m : ℝ) ^ 2 * Real.log large₂.sc.b := by
    have h2v : 2 * D.host.v = D.host.rdE := by unfold Formalism.BasicNotions.Host.v; ring
    have hrd : Real.log D.host.rdE ≤ large₂.sc.L / Cl := hS.2.2.2.2.2.2.2.2.2.2.1
    have hv0 : 0 ≤ Real.log (2 * D.host.v) := Real.log_nonneg (Formalism.L2.SG.Pf.LoopBCovN.rdE_ge_one D)
    have he := Formalism.L2.SG.Pf.LoopBCovN.eN_le D
    have he0 : 0 ≤ Formalism.L2.SG.Pf.LoopBCovN.eN D := by unfold Formalism.L2.SG.Pf.LoopBCovN.eN; positivity
    rw [Formalism.MainNotions.S.log_scb large₂, h2v]
    rw [h2v] at hv0
    have hCl0 : (0 : ℝ) < Cl := by linarith
    have hL0 : 0 ≤ large₂.sc.L := by
      by_contra hneg
      push_neg at hneg
      have : large₂.sc.L / Cl < 0 := div_neg_of_neg_of_pos hneg hCl0
      linarith
    have h72 : large₂.sc.L / Cl ≤ large₂.sc.L / 72 := div_le_div_of_nonneg_left hL0 (by norm_num) hCl
    have hm0 : 0 ≤ (D.R.m : ℝ) ^ 2 := sq_nonneg _
    calc Formalism.L2.SG.Pf.LoopBCovN.eN D * Real.log D.host.rdE ≤ ((D.R.m : ℝ) ^ 2 / 2) * (large₂.sc.L / 72) :=
          mul_le_mul he (hrd.trans h72) hv0 (by positivity)
      _ ≤ 1 * (D.R.m : ℝ) ^ 2 * large₂.sc.L := by nlinarith
  have hFE := Formalism.L2.SG.LoopsFinal.frameEqvInj_of (Formalism.L2.SG.LoopsTies.wOf X) hI (Formalism.L2.SG.LoopsTies.hOf X Y hF hI)
    (Formalism.L2.SG.LoopsTies.aOfW X Y hF hI hWD) (Formalism.L2.SG.LoopsTies.hvOfW X Y hF hI hWD)
    (Formalism.L2.SG.Pf.LoopBFrame.frameChangeC_holds _ _ _ hF hI _) u u
  have hti := Formalism.L2.SG.LoopsTies.tiesAt X Y hF hI hWD u u
  refine ⟨Formalism.L2.SG.LoopsTies.wOf X, Formalism.L2.SG.LoopsTies.hOf X Y hF hI, Formalism.L2.SG.LoopsTies.aOfW X Y hF hI hWD,
    Formalism.L2.SG.LoopsTies.hvOfW X Y hF hI hWD,
    Formalism.L2.SG.LoopTieOf.loopTieOfParts
      (Formalism.L2.SG.LoopTieOf.loopRowsOf (Formalism.L2.SG.LoopsTies.wOf X) hI (Formalism.L2.SG.LoopsTies.hOf X Y hF hI)
        (Formalism.L2.SG.LoopsTies.aOfW X Y hF hI hWD) (Formalism.L2.SG.LoopsTies.hvOfW X Y hF hI hWD)
        (Formalism.L2.SG.Pf.WittFlags.RowRepsIso_holds D) u u hFE)
      (Formalism.L2.SG.LoopTerm.locB large₂ 1 C hB u u hwin hW hSS)
      (Formalism.L2.SG.LoopTerm.loopTermOfN (Formalism.L2.SG.LoopsTies.wOf X) hI (Formalism.L2.SG.LoopsTies.hOf X Y hF hI)
        (Formalism.L2.SG.LoopsTies.aOfW X Y hF hI hWD) (Formalism.L2.SG.LoopsTies.hvOfW X Y hF hI hWD) large₂ 1 C hB u u hwin hW hSS
        (GlobalTheory.RMeasAll.rMeasEx_all D X Y hF hI C u u hW)
        (Formalism.L2.SG.Pf.LoopBPin.pinAll_holds u u) (Formalism.L2.SG.Pf.LoopBPin.covolPos_holds u u)
        (GlobalTheory.T.localBesselJFactor_all_words_of_gap D X Y hF hI C hB u u hG)
        (Formalism.L2.SG.Pf.LoopBCovN.covN_pos hCF one_pos C u u)
        (Formalism.L2.SG.Pf.LoopBCovN.covWinN_of hCF C large₂ zero_le_one hup u u) hwin), ?_, fun t => rfl⟩
  exact ⟨Formalism.L2.SG.LoopsFinal.jtPin_of _ hI _ _ _ (Formalism.L2.SG.Pf.FibreCounting.AmpFibreConst_holds Y),
    Formalism.L2.SG.Pf.WittFlags.WRowPin_holds hF hI _ _ _ _,
    Formalism.L2.SG.Pf.FibreCounting.FibreCount_holds Y,
    Formalism.MainNotions.BridgeLemma₂.rows_TermPtsTie_of _ (Formalism.MainNotions.BridgeLemma₂.rows_rdE_pos D) hti.1,
    hti.2.1, hti.2.2, fun t t' hL hE => hFE t t' hL hE⟩

namespace GlobalTheory.Core.Deg

theorem tieOn_singleton_uncond : ∀ c : ℝ, TieOn {c} := by
  intro c Cg cb Cu cT CT
  obtain ⟨C, hCv⟩ := GlobalTheory.T.stabiliserCovolume_relevantTerm_le_heightPow Cg cb Cu cT CT c 1
  refine ⟨C, 72, ?_⟩
  intro C0 hC0 C' Cl hC' hCl D large₂ X Y hF hI u hT hH hCT
  have hC0' : C0 = c := hC0
  subst hC0'
  obtain ⟨W, H, Am, hV, Z, hTie, hvol⟩ :=
    exists_termLoop_of_standingHypotheses D large₂ X Y hF hI u C' Cl Cg cb Cu cT CT (by linarith) hCl hT hH.1 hCT
  refine ⟨_, Z, hTie, ?_⟩
  intro hHyp t hG hr
  rw [hvol t]
  exact hCv D X Y hF hI W H Am hV large₂ u u C' Cl (by linarith) hHyp t hG hr

end GlobalTheory.Core.Deg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CntOnSingleton
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma GlobalTheory.Core.Deg

namespace GlobalTheory.Core.Deg

theorem cntOn_singleton : Formalism.HermitianLatticesTheory.SiegelMassRatio → ∀ c : ℝ, CntOn {c} := by
  intro hM c Cg cb Cu cT CT
  obtain ⟨C1a, hC1⟩ := GlobalTheory.Mass.PrimMeanRow.main 1 one_pos
  obtain ⟨c3, hC3⟩ := GlobalTheory.LoopC.PairMean.main Cg cb Cu cT CT c 1 3 (max C1a 0) (le_max_right _ _)
  obtain ⟨cH, -, hHH⟩ := GlobalTheory.GramHeight.height_bounds Cg cb Cu cT CT c 1
  obtain ⟨cS, hSW⟩ := GlobalTheory.LoopC.GenericMean.main Cg cb Cu cT CT c 1
  obtain ⟨c4, hC4⟩ := GlobalTheory.LoopC.Partner.partners_le Cg cb Cu cT CT c 1
  refine ⟨c3, cH, cS, c4, 1, fun C0 hC0 C' Cl _ hl D large₂ u => ?_⟩
  rw [Set.mem_singleton_iff] at hC0
  subst hC0
  refine ⟨fun C hC => ?_, ?_, ?_, ?_⟩
  · exact hC3 C hC _ _ u u _ _ hl (GlobalTheory.Mass.RowsRawMass.main _ u)
      (hC1 _ (le_max_left _ _) _ _ u u _ _ Cg cb Cu cT CT C0 1 hl)
  · exact hHH _ _ u u _ _ hl
  · exact hSW _ _ u u _ _ hl
      (GlobalTheory.Mass.PrimMeanCorankOne.main _ _ u u _ _ Cg cb Cu cT CT C0 1 (Formalism.MainNotions.BridgeLemma.mass_ratio_of_siegel_cm_unramified hM _))
  · exact hC4 _ _ u u _ _ hl

end GlobalTheory.Core.Deg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CorankTwoCountBoundsOfRowCountBoundsUniform
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Core.Deg

theorem corankTwoCountBounds_of_rowCountBoundsUniform : ∀ S : Set ℝ, CntOn S → CountBoundOn S := by
  intro S h Cg cb Cu cT CT
  obtain ⟨c3, cH, cS, c4, thr, hthr⟩ := h Cg cb Cu cT CT
  exact ⟨c3, cH, thr, fun C0 hC0 C' Cl h1 h2 D large₂ u =>
    ⟨(hthr C0 hC0 C' Cl h1 h2 D large₂ u).1, (hthr C0 hC0 C' Cl h1 h2 D large₂ u).2.1⟩⟩

end GlobalTheory.Core.Deg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.VanishingGramBoundUniformWindowAndParams
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Core.Deg

theorem vanishingGramBound_uniformWindow_and_weightData : (VanishingGramTermsBoundWindow → ∀ c : ℝ, On {c} VanishingGramTermsBound) ∧ (VanishingGramTermsBoundParams → Led1 VanishingGramTermsBound) := by
  refine ⟨fun h c => ?_, fun h => ?_⟩
  · intro Cg cb Cu cT CT h1 h2
    obtain ⟨a, b, H⟩ := h Cg cb Cu cT CT c h1 h2
    refine ⟨max a b, fun C0 hC0 C' Cl hC' hCl D large₂ X Y hF hI u _ t r s d e => ?_⟩
    rw [Set.mem_singleton_iff] at hC0
    subst hC0
    exact H C' Cl (le_trans (le_max_left _ _) hC') (le_trans (le_max_right _ _) hCl) D large₂ X Y hF hI u t r s d e
  · intro Cg cb Cu cT CT h1 h2
    obtain ⟨a, b, H⟩ := h Cg cb Cu cT CT h1 h2
    exact ⟨max a b, fun C' Cl hC' hCl D large₂ X Y hF hI u _ t r s n d e =>
      H C' Cl (le_trans (le_max_left _ _) hC') (le_trans (le_max_right _ _) hCl) D large₂ X Y hF hI u t r s n d e⟩

end GlobalTheory.Core.Deg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.VanishingGramBoundWindowOfTermPairTypeBound
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TermSumBoundOfPairsAmplitude
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TermSumBoundOfPairsAmplitude
noncomputable section
open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc
namespace GlobalTheory.Core.Deg

theorem termSumBound_of_pairsAmplitude : TermSumBoundOfPairsAmplitude := by
  intro C' Cl Cg cb Cw cT CT C0 D large₂ X Y u hH hT ha hA
  have hN : NormExpDegC :=
    Formalism.L2.SG.Pf.normExpDegC_of_leaves Formalism.L2.SG.Closed.FinLeviC_holds Formalism.L2.SG.Closed.OOLintSumC_holds
  have hG0 : 0 ≤ (Y.tO u u).Gam1 := ha.2.2.le
  have hPg : 0 ≤ PgC Y := Finset.prod_nonneg fun v _ => by positivity
  have hGB : (Y.tO u u).GGBound (PgC Y) :=
    Formalism.L2.SG.TermOp.ggBound Y.TR (Y.cs u) (Y.cs u) (Y.FN u) (Y.FN u) Formalism.L2.SG.Closed.TermsGGBound_holds Y.psi_ne
      (fun v => card_ge_three hH.2 Y.TR v)
  refine ⟨ha.1.indicator _, ?_⟩
  exact Formalism.L2.SG.RowsOther.kppDiag_of_pairs (Y.tO u u) Formalism.FourierDecayAlt.P.price_of_index
    Formalism.FourierDecayAlt.P.equal_index Formalism.FourierDecayAlt.P.pair_split_alt Formalism.FourierDecayAlt.P.subfamilyAlt
    (PgC Y) (duC X Y u) D.R.k D.R.f hPg ha
    (Formalism.L2.SG.TermOp.rowOrth Y.TR (Y.cs u) (Y.cs u) (Y.FN u) (Y.FN u))
    (Formalism.L2.SG.KappaOffDiagonal.corankPosC_holds D X Y u u hT) (hN D X Y u hT) hGB
    (Formalism.L2.SG.RowsOther.pairsDeg_of_amp _ hG0 _ _ _ _ hPg hA)

end GlobalTheory.Core.Deg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TermSumBoundOfPairsAmplitudeStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deg_termSumBoundOfPairsAmplitude : GlobalTheory.Core.Deg.TermSumBoundOfPairsAmplitude := by
  first | exact @GlobalTheory.Core.Deg.termSumBound_of_pairsAmplitude | exact GlobalTheory.Core.Deg.termSumBound_of_pairsAmplitude | (intros; apply GlobalTheory.Core.Deg.termSumBound_of_pairsAmplitude <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PairsAmplitudeBoundOfTypeBound
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PgCLeTwoAtRecord
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Cnt Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.KappaOffDiagonal Formalism.L2.SG.RowsConc

noncomputable section

namespace GlobalTheory.Core.Deg

theorem pgC_le_two_at_record : ∀ (C' Cl Cg cb Cw cT CT C0 : ℝ) (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X),
    Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 → PgC Y ≤ 2 := by
  intro C' Cl Cg cb Cw cT CT C0 D large₂ X Y hH
  have hPg := Formalism.L2.SG.Pf.SatGram.tt_eq' Formalism.L2.SG.Pf.splitPrimeLoc_holds
    Formalism.L2.SG.Pf.SatGramLoc.reduction_structure_holds Y.TR
  unfold Formalism.L2.SG.RowsConc.PgC
  rw [hPg, Formalism.L2.SG.KappaOffDiagonal.PgLe.finrank_F X]
  obtain ⟨⟨hS0, -, -⟩, hP⟩ := hH
  obtain ⟨-, -, -, hfk, -⟩ := hS0
  have hg := hP.2.1
  have hb := Formalism.MainNotions.KappaEndpoints.two_le_scale_b D large₂
  have hk : (1 : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k; exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hf : (D.R.f : ℝ) ≤ D.R.k := by exact_mod_cast hfk
  have h0 := Formalism.L2.SG.KappaOffDiagonal.PgLe.one_factor (D.R.k : ℝ) large₂.sc.b (D.host.g 0 : ℝ) D.R.f hk hb (hg 0).1 hf
  have h1 := Formalism.L2.SG.KappaOffDiagonal.PgLe.one_factor (D.R.k : ℝ) large₂.sc.b (D.host.g 1 : ℝ) D.R.f hk hb (hg 1).1 hf
  calc (1 + 3 / (D.host.g 0 : ℝ)) ^ D.R.f * (1 + 3 / (D.host.g 1 : ℝ)) ^ D.R.f
      ≤ Real.exp (1 / 4) * Real.exp (1 / 4) :=
        mul_le_mul h0 h1 (by positivity) (Real.exp_pos _).le
    _ ≤ 2 := Formalism.L2.SG.KappaOffDiagonal.PgLe.exp_quarter_mul_exp_quarter_le_two

end GlobalTheory.Core.Deg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SumLabelsOneRecord
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Cnt Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.KappaOffDiagonal Formalism.L2.SG.RowsConc

noncomputable section
open scoped Classical
open Formalism.MainNotions Formalism.MainNotions.KTwoCosetCount Formalism.MainNotions.MinorIntegralityTorus
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Deg

theorem sum_labels_one_record : ∀ (CH C' Cl Cg cb Cw cT CT C0 : ℝ) (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), 1 ≤ Cl → Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 → ∀ j ∈ Finset.Icc 1 D.R.rS, ∀ T : Finset (ℕ → D.host.E), (∀ δ ∈ T, ∃ t ∈ relSet Y u, jT t = j ∧ labT t = δ) → ∑ δ ∈ T, k2S D (H1C large₂ CH) j δ ^ (-(3 * (D.R.rS : ℝ))) ≤ Hb large₂.sc.b (21 + 4 * |CH|) D.R.m D.R.f ^ ((21 + 4 * |CH|) * (D.R.rS : ℝ)) := by
  intro CH C' Cl Cg cb Cw cT CT C0 D large₂ X Y u hCl1 hH j hj T hTm
  have hfact : ∀ δ ∈ T, (∀ l, IsIntegral ℤ (δ l)) ∧ (∀ l, j < l → δ l = 0) ∧ δ 0 = 1 := by
    intro δ hδ
    obtain ⟨t, -, rfl, rfl⟩ := hTm δ hδ
    exact labFacts_conc t
  have h := kloostermanCosetSum_le Formalism.MainNotions.MinorIntegralityTorus.NormLB_holds Formalism.MainNotions.LatticeSumConvergence.LatSum_holds large₂ hH CH j hj T hfact
  unfold H1C
  refine h.trans ?_
  have hb : 1 ≤ large₂.sc.b := by linarith [KappaEndpoints.two_le_scale_b D large₂]
  have hCl0 : 0 < Cl := by linarith
  have hc0 : 0 ≤ ccOf CH Cl := by unfold ccOf; positivity
  have hcle : ccOf CH Cl ≤ 21 + 4 * |CH| := by
    unfold ccOf
    have : 4 / Cl ≤ 4 := by rw [div_le_iff₀ hCl0]; linarith
    linarith
  unfold Hb
  rw [← Real.rpow_mul (by linarith), ← Real.rpow_mul (by linarith)]
  apply Real.rpow_le_rpow_of_exponent_le hb
  have hx : 0 ≤ (D.R.m : ℝ) ^ 2 * D.R.f * D.R.rS := by positivity
  have e1 : ccOf CH Cl * (D.R.m : ℝ) ^ 2 * D.R.f * (ccOf CH Cl * D.R.rS) =
      ccOf CH Cl * ccOf CH Cl * ((D.R.m : ℝ) ^ 2 * D.R.f * D.R.rS) := by ring
  have e2 : (21 + 4 * |CH|) * (D.R.m : ℝ) ^ 2 * D.R.f * ((21 + 4 * |CH|) * D.R.rS) =
      (21 + 4 * |CH|) * (21 + 4 * |CH|) * ((D.R.m : ℝ) ^ 2 * D.R.f * D.R.rS) := by ring
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_right (mul_le_mul hcle hcle hc0 (by positivity)) hx

end GlobalTheory.Core.Deg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PairsAmplitudeBoundOfTypeBound
noncomputable section
open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.MainNotions.S.Cnt Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.KappaOffDiagonal Formalism.L2.SG.RowsConc
namespace GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem pairsDegOfType_holds : PairsDegOfType := by
  intro CH Ch Cp C hCH hCh hCp hC
  set Cc : ℝ := 21 + 4 * |CH| with hCcdef
  have hCc : 0 ≤ Cc := by positivity
  have hC0 : 0 ≤ C := by linarith
  refine ⟨max 1 (k2C0 (k2Cf C Ch Cc)), fun C' Cl Cg cb Cw cT CT C0 D large₂ X Y u h2 hH hTie tAt => ?_⟩
  have b1 : (1 : ℝ) ≤ Cl := le_trans (le_max_left _ _) h2
  have b5 : k2C0 (k2Cf C Ch Cc) ≤ Cl := le_trans (le_max_right _ _) h2
  have dAt : ∀ t ∈ relSet Y u, 0 < k2Del D (jT t) (labT t) ∧
      k2Del D (jT t) (labT t) ≤ Hb large₂.sc.b C D.R.m D.R.f * k2S D (H1C large₂ CH) (jT t) (labT t) ^ 2 :=
    fun t ht => delta_pos_le_height_sq (PFHost_of_data D hH.1.2.1) large₂ hCH hC t ht
  have cAt := GlobalTheory.Core.Deg.sum_labels_one_record CH C' Cl Cg cb Cw cT CT C0 D large₂ X Y u b1 hH
  have pg := GlobalTheory.Core.Deg.pgC_le_two_at_record C' Cl Cg cb Cw cT CT C0 D large₂ X Y hH
  obtain ⟨hΓ, hdim⟩ := kappa_off_diagonal_dim_form_C D X Y u hTie
  have hJ := JPosC_holds Cg cb Cw cT CT C0 C' Cl D large₂ X Y u hH hTie
  obtain ⟨hL, -, -, -, hWd, -⟩ := hTie
  have hF := Formalism.L2.SG.Pf.fundExistsC_holds D X Y u u
  have hI := Formalism.L2.SG.Closed.OOIntAllC_outright D X Y u u (Formalism.L2.SG.Closed.FoldOKC_outright D X Y u hL hWd)
    (Formalism.L2.SG.Closed.FoldOKC_outright D X Y u hL hWd) hF
  have hIrr := IrrVecC_holds D X Y u hF hI
  have hdpi : 0 ≤ dpiC X u := Nat.cast_nonneg _
  have hmass : 0 ≤ massC Y u := Finset.sum_nonneg fun Λ _ => by unfold wRow; positivity
  have hK : 0 ≤ dpiC X u * massC Y u := mul_nonneg hdpi hmass
  set B := dpiC X u * massC Y u * (∑ j ∈ Finset.Icc 1 D.R.rS, k2A1 large₂ C Ch Cc j) ^ 2 with hB
  set g : GTu Y u × GTu Y u → ℝ := ((Y.tO u u).allPairs (Y.tO u u).degSet).indicator
    (fun p => ‖(Y.tO u u).vec p.1‖ * ‖(Y.tO u u).vec p.2‖) with hg
  have hg0 : ∀ p, 0 ≤ g p := fun p => Set.indicator_nonneg (fun p _ => by positivity) p
  have hfin : ∀ s : Finset (GTu Y u × GTu Y u), ∑ p ∈ s, g p ≤ B := by
    intro s
    have : ∑ p ∈ s, g p = ∑ p ∈ s.filter (fun p => p ∈ (Y.tO u u).allPairs (Y.tO u u).degSet),
        ‖(Y.tO u u).vec p.1‖ * ‖(Y.tO u u).vec p.2‖ := by
      rw [Finset.sum_filter]
      rfl
    rw [this]
    exact fin_bound hC0 hCh (le_refl _) hK hIrr hJ tAt dAt cAt _ (fun p hp => (Finset.mem_filter.1 hp).2)
  have hsum : Summable g := summable_of_sum_le hg0 hfin
  have htsum : Formalism.L2.SG.RowsOther.ampSum (Y.tO u u) ((Y.tO u u).allPairs (Y.tO u u).degSet) ≤ B :=
    tsum_le_of_sum_le' (mul_nonneg hK (sq_nonneg _)) hfin
  refine ⟨hsum, ?_⟩
  have hPg0 : 0 ≤ PgC Y := Finset.prod_nonneg fun v _ => by positivity
  have hdu : 0 ≤ duC X Y u := Nat.cast_nonneg _
  have hCf : 1 ≤ k2Cf C Ch Cc := by unfold k2Cf; nlinarith [sq_nonneg C, sq_nonneg Ch, sq_nonneg Cc]
  have hk : k2C0 (k2Cf C Ch Cc) * (D.R.m : ℝ) ^ 6 * large₂.sc.L ≤ (D.R.k : ℝ) * Real.log D.R.k := by
    have hL0 : 0 ≤ large₂.sc.L := by
      rw [← log_scale_eq_L]; exact Real.log_nonneg (by linarith [two_le_scale_b large₂ (D := D)])
    have hm6 : 0 ≤ (D.R.m : ℝ) ^ 6 * large₂.sc.L := mul_nonneg (by positivity) hL0
    have := hH.2.1
    calc k2C0 (k2Cf C Ch Cc) * (D.R.m : ℝ) ^ 6 * large₂.sc.L = k2C0 (k2Cf C Ch Cc) * ((D.R.m : ℝ) ^ 6 * large₂.sc.L) := by ring
      _ ≤ Cl * ((D.R.m : ℝ) ^ 6 * large₂.sc.L) := mul_le_mul_of_nonneg_right b5 hm6
      _ = Cl * (D.R.m : ℝ) ^ 6 * large₂.sc.L := by ring
      _ ≤ _ := this
  have hA : (∑ j ∈ Finset.Icc 1 D.R.rS, k2A1 large₂ C Ch Cc j) ^ 2 ≤ k2B D large₂ (k2Cf C Ch Cc) := by
    unfold k2B
    exact pow_le_pow_left₀ (Finset.sum_nonneg fun j _ => kloostermanTermA_nonneg large₂ hC0 hCh hCc j)
      (Finset.sum_le_sum fun j hj => rank_contribution_le large₂ hC0 j hj) 2
  have hclose := final_bound_closes D large₂ (k2Cf C Ch Cc) hCf _ hdu hk
  have hGB : (Y.tO u u).Gam1 * B ≤ duC X Y u * (∑ j ∈ Finset.Icc 1 D.R.rS, k2A1 large₂ C Ch Cc j) ^ 2 := by
    have e : (Y.tO u u).Gam1 * B =
        ((Y.tO u u).Gam1 * massC Y u * dpiC X u) * (∑ j ∈ Finset.Icc 1 D.R.rS, k2A1 large₂ C Ch Cc j) ^ 2 := by
      rw [hB]; ring
    rw [e]
    exact mul_le_mul_of_nonneg_right hdim (sq_nonneg _)
  calc PgC Y * ((Y.tO u u).Gam1 *
        Formalism.L2.SG.RowsOther.ampSum (Y.tO u u) ((Y.tO u u).allPairs (Y.tO u u).degSet))
      ≤ PgC Y * ((Y.tO u u).Gam1 * B) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htsum hΓ) hPg0
    _ ≤ PgC Y * (duC X Y u * (∑ j ∈ Finset.Icc 1 D.R.rS, k2A1 large₂ C Ch Cc j) ^ 2) :=
        mul_le_mul_of_nonneg_left hGB hPg0
    _ ≤ 2 * (duC X Y u * k2B D large₂ (k2Cf C Ch Cc)) :=
        mul_le_mul pg (mul_le_mul_of_nonneg_left hA hdu) (mul_nonneg hdu (sq_nonneg _)) (by norm_num)
    _ = 2 * duC X Y u * k2B D large₂ (k2Cf C Ch Cc) := by ring
    _ ≤ _ := hclose

end GlobalTheory.Core.Deg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PairsAmplitudeBoundOfTypeBoundStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairsAmplitudeBound_of_typeBound : GlobalTheory.Core.Deg.PairsDegOfType := by
  first | exact @GlobalTheory.Core.Deg.pairsDegOfType_holds | exact GlobalTheory.Core.Deg.pairsDegOfType_holds | (intros; apply GlobalTheory.Core.Deg.pairsDegOfType_holds <;> assumption)
end
end

namespace GlobalTheory.Core.Deg

theorem vanishingGramBoundWindow_of_termPairTypeBound (hT : GlobalTheory.TypeAsm.TypeP) : VanishingGramTermsBoundWindow := by
  intro Cg cb Cu cT CT C0 hcb hcT
  obtain ⟨CH, Ch, Cp, hCH, hCh, hCp, H⟩ := hT Cg cb Cu cT CT C0 hcb hcT
  obtain ⟨C₀, H2⟩ := H (Cp + 4) le_rfl
  obtain ⟨C'₀, Cl₀, H3⟩ := H2 (max C₀ (2 * (CH + 1))) (le_max_left _ _)
  obtain ⟨Cl₁, H4⟩ := GlobalTheory.T.pairsAmplitudeBound_of_typeBound CH Ch Cp (max C₀ (2 * (CH + 1))) hCH hCh hCp (le_max_right _ _)
  refine ⟨max C'₀ 1, max Cl₀ Cl₁, fun C' Cl hC' hCl D large₂ X Y _ _ u hTies _ h0 hC hAbs => ?_⟩
  have hK2 : Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cu cT CT C0 :=
    Formalism.MainNotions.NonGenericAndKTwoTheorems.Hyp_of D large₂ C' Cl Cg cb Cu cT CT C0 h0.2.1 h0.1 h0.2.2 ((le_max_right _ _).trans hC')
  have hType := H3 C' Cl ((le_max_left _ _).trans hC') ((le_max_left _ _).trans hCl) D large₂ X Y u hTies hK2 hC
  have hPairs := H4 C' Cl Cg cb Cu cT CT C0 D large₂ X Y u ((le_max_right _ _).trans hCl) hK2 hC hType
  exact GlobalTheory.T.deg_termSumBoundOfPairsAmplitude C' Cl Cg cb Cu cT CT C0 D large₂ X Y u hK2 hC hAbs hPairs

end GlobalTheory.Core.Deg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DegenerateTermsAndCollisionBoundsUniformWidths
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Deg

theorem degenerate_and_collisions_uncond : (∀ c : ℝ, On {c} VanishingGramTermsBound) ∧ ∀ c : ℝ, On {c} CollS := by
  have hSM : Formalism.HermitianLatticesTheory.SiegelMassRatio := GlobalTheory.Mass.siegelMassRatio_holds
  have hS : ∀ c : ℝ, SmallOn {c} := fun c =>
    (inputs_of_subset_widths {c} Set.univ (Set.subset_univ _)).2.1 smallOn_univ_unconditional
  have hP : GlobalTheory.TypeAsm.TypeP := GlobalTheory.rowsPos_typeP
  refine ⟨vanishingGramBound_uniformWindow_and_weightData.1 (vanishingGramBoundWindow_of_termPairTypeBound hP), fun c => ?_⟩
  exact collS_on hSM {c} (GlobalTheory.T.rowAmplitudeBoundsUniform_singleton_width c) (corankTwoCountBounds_of_rowCountBoundsUniform {c} (cntOn_singleton hSM c)) (hS c)
    (tieOn_singleton_uncond c)

end GlobalTheory.Core.Deg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DegenerateTermsAndCollisionBoundsUniformWidthsStatement
open GlobalTheory.Core.Deg

theorem GlobalTheory.T.degenerateTerms_and_collisionBounds_uniform_widths :
    (∀ c : ℝ, On {c} VanishingGramTermsBound) ∧ ∀ c : ℝ, On {c} CollS :=
  degenerate_and_collisions_uncond
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DiagonalRowBoundFromWindowWidthThree
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DiagonalTheoremOfFourPointBounds
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqualIdentificationPairPriceLeSixFifths
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqualIdentificationPairPriceLeSixFifths
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 GlobalTheory.Core.Diag GlobalTheory.Core.Deg

noncomputable section
namespace GlobalTheory.Core.Deg

theorem exp_le_inv_one_sub_pg (x : ℝ) (hx1 : x < 1) : Real.exp x * (1 - x) ≤ 1 := by
  have h := Real.add_one_le_exp (-x)
  have hp := Real.exp_pos x
  have : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
  nlinarith

theorem one_factor_sharp (k b g : ℝ) (f : ℕ) (hk : 1 ≤ k) (hb : 2 ≤ b) (hg : (k * b) ^ 8 ≤ g) (hf : (f : ℝ) ≤ k) :
    (1 + 3 / g) ^ f ≤ Real.exp (3 / 256) := by
  have hb8 : (256 : ℝ) ≤ b ^ 8 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hb 8
    norm_num at this ⊢; linarith
  have hk8 : k ≤ k ^ 8 := le_self_pow₀ hk (by norm_num)
  have hkb : 256 * k ≤ (k * b) ^ 8 := by
    rw [mul_pow]
    have : 256 * k ≤ k ^ 8 * 256 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hb8 (by positivity : (0 : ℝ) ≤ k ^ 8)]
  have hg0 : 0 < g := by nlinarith
  have hx : (f : ℝ) * (3 / g) ≤ 3 / 256 := by
    rw [mul_div_assoc', div_le_div_iff₀ hg0 (by norm_num)]
    nlinarith
  calc (1 + 3 / g) ^ f ≤ Real.exp (3 / g) ^ f := by
        apply pow_le_pow_left₀ (by positivity)
        have := Real.add_one_le_exp (3 / g)
        linarith
    _ = Real.exp (f * (3 / g)) := by rw [← Real.exp_nat_mul]
    _ ≤ Real.exp (3 / 256) := Real.exp_le_exp.2 hx

theorem exp_pair_le_six_fifths : Real.exp (3 / 256) * Real.exp (3 / 256) ≤ 6 / 5 := by
  rw [← Real.exp_add]
  have h := exp_le_inv_one_sub_pg (3 / 256 + 3 / 256) (by norm_num)
  have hp := Real.exp_pos (3 / 256 + 3 / 256 : ℝ)
  norm_num at h ⊢
  nlinarith

theorem pgC_le_six_fifths : ∀ (C' Cl Cg cb Cw cT CT C0 : ℝ) (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X),
    Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 → PgC Y ≤ 6 / 5 := by
  intro C' Cl Cg cb Cw cT CT C0 D large₂ X Y hH
  have hPg := Formalism.L2.SG.Pf.SatGram.tt_eq' Formalism.L2.SG.Pf.splitPrimeLoc_holds
    Formalism.L2.SG.Pf.SatGramLoc.reduction_structure_holds Y.TR
  unfold Formalism.L2.SG.RowsConc.PgC
  rw [hPg, Formalism.L2.SG.KappaOffDiagonal.PgLe.finrank_F X]
  obtain ⟨⟨hS0, -, -⟩, hP⟩ := hH
  obtain ⟨-, -, -, hfk, -⟩ := hS0
  have hg := hP.2.1
  have hb := Formalism.MainNotions.KappaEndpoints.two_le_scale_b D large₂
  have hk : (1 : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k; exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hf : (D.R.f : ℝ) ≤ D.R.k := by exact_mod_cast hfk
  have h0 := one_factor_sharp (D.R.k : ℝ) large₂.sc.b (D.host.g 0 : ℝ) D.R.f hk hb (hg 0).1 hf
  have h1 := one_factor_sharp (D.R.k : ℝ) large₂.sc.b (D.host.g 1 : ℝ) D.R.f hk hb (hg 1).1 hf
  calc (1 + 3 / (D.host.g 0 : ℝ)) ^ D.R.f * (1 + 3 / (D.host.g 1 : ℝ)) ^ D.R.f
      ≤ Real.exp (3 / 256) * Real.exp (3 / 256) :=
        mul_le_mul h0 h1 (by positivity) (Real.exp_pos _).le
    _ ≤ 6 / 5 := exp_pair_le_six_fifths

end GlobalTheory.Core.Deg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqualIdentificationPairPriceLeSixFifthsStatement
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 GlobalTheory.Core.Diag GlobalTheory.Core.Deg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.equalIdentificationPairPrice_le_six_fifths : ∀ (C' Cl Cg cb Cw cT CT C0 : ℝ) (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X), Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 → PgC Y ≤ 6 / 5 := by
  first | exact @GlobalTheory.Core.Deg.pgC_le_six_fifths | exact GlobalTheory.Core.Deg.pgC_le_six_fifths | (intros; apply GlobalTheory.Core.Deg.pgC_le_six_fifths <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AbstractDiagonalBoundCollisionsCountedOnce
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AbstractDiagonalBoundCollisionsCountedOnce
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 GlobalTheory.Core.Diag GlobalTheory.Core.Deg

noncomputable section

namespace GlobalTheory

theorem diag_abstract_collisions_once :
    ∀ (τ Rw I H H₁ : Type) [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁] (X : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (one : H) (Pg B A₁ A₂ : ℝ), 0 ≤ Pg → X.AbsConv → X.NormExpansionOn X.genSet → X.NormExpansionOn X.ngSet → X.GGBound Pg → X.RowOrth → X.CorankPos → Formalism.L2.SG.RowsOther.IdOne X one → X.pairAbs (X.big X.nzSet) ≤ B → X.pairSum (X.one X.genSet) ≤ A₁ → X.pairSum (X.one X.ngSet) ≤ A₂ → ‖X.K0 - one‖ ^ 2 ≤ 2 * Pg * (B + A₁ + A₂) := by
  intro τ Rw I H H₁ _ _ _ _ _ _ X one Pg B A₁ A₂ hPg hA hNg hNn hG hO hC hI hB h1 h2
  have hE := Formalism.FourierDecayAlt.P.equal_index
  have hF := Formalism.FourierDecayAlt.P.subfamilyAlt τ Rw I H H₁ X hA
  obtain ⟨_, _, hng⟩ := Formalism.FourierDecayAlt.P.pair_split_alt τ Rw I H H₁ X hA hO hC

  have hgen : X.PhiEq X.genSet = X.pairSum (X.big X.genSet) + X.pairSum (X.one X.genSet) := by
    let Y : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁ := { X with scal := fun _ _ => True }
    obtain ⟨_, hg, _⟩ := Formalism.FourierDecayAlt.P.pair_split_alt τ Rw I H H₁ Y hA hO hC
    have e1 : Y.nsc Y.genSet = ∅ := by
      ext p; simp [Y, Formalism.FourierDecayAlt.PB.Terms.nsc]
    have e2 : Y.sc Y.genSet = X.one X.genSet := by
      ext p; simp [Y, Formalism.FourierDecayAlt.PB.Terms.sc, Formalism.FourierDecayAlt.PB.Terms.one, Formalism.FourierDecayAlt.PB.Terms.allPairs,
        Formalism.FourierDecayAlt.PB.Terms.genSet]
    have e0 : Y.pairSum ∅ = 0 := by simp [Formalism.FourierDecayAlt.PB.Terms.pairSum]
    rw [e1, e2, e0, add_zero] at hg
    exact hg

  have hS : Summable (fun p : τ × τ => ‖inner ℂ (X.vec p.1) (X.vec p.2)‖) := by
    have hv := hA.2.1
    have hm : Summable (fun p : τ × τ => ‖X.vec p.1‖ * ‖X.vec p.2‖) :=
      hv.mul_of_nonneg hv (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => norm_inner_le_norm _ _) hm
  have hdisj : Disjoint (X.big X.genSet) (X.big X.ngSet) := by
    rw [Set.disjoint_left]
    intro p hp hq
    exact hq.1.1.2 hp.1.1.2
  have hunion : X.pairAbs (X.big X.genSet) + X.pairAbs (X.big X.ngSet) =
      X.pairAbs (X.big X.genSet ∪ X.big X.ngSet) := by
    unfold Formalism.FourierDecayAlt.PB.Terms.pairAbs
    rw [Set.indicator_union_of_disjoint hdisj]
    beta_reduce
    rw [Summable.tsum_add (hS.indicator _) (hS.indicator _), mul_add]
  have hsub : X.big X.genSet ∪ X.big X.ngSet ⊆ X.big X.nzSet := by
    rintro p (hp | hp)
    · exact ⟨⟨hp.1.1.1, hp.1.2.1.1, hp.1.2.2⟩, hp.2⟩
    · exact ⟨⟨hp.1.1.1, hp.1.2.1.1, hp.1.2.2⟩, hp.2⟩
  have hsum : X.pairAbs (X.big X.genSet) + X.pairAbs (X.big X.ngSet) ≤ B := by
    rw [hunion]; exact (hF _ _ hsub).1.trans hB
  have bg : X.pairSum (X.big X.genSet) ≤ X.pairAbs (X.big X.genSet) :=
    (le_abs_self _).trans (hF _ _ le_rfl).2
  have bn : X.pairSum (X.big X.ngSet) ≤ X.pairAbs (X.big X.ngSet) :=
    (le_abs_self _).trans (hF _ _ le_rfl).2
  have g1 : ‖X.part X.genSet‖ ^ 2 ≤ Pg * (X.pairAbs (X.big X.genSet) + A₁) := by
    have := Formalism.FourierDecayAlt.P.price_of_index hE τ Rw I H H₁ X Pg X.genSet hNg hG
    refine this.trans (mul_le_mul_of_nonneg_left ?_ hPg)
    rw [hgen]; linarith
  have g2 : ‖X.part X.ngSet‖ ^ 2 ≤ Pg * (X.pairAbs (X.big X.ngSet) + A₂) := by
    have := Formalism.FourierDecayAlt.P.price_of_index hE τ Rw I H H₁ X Pg X.ngSet hNn hG
    refine this.trans (mul_le_mul_of_nonneg_left ?_ hPg)
    rw [hng]; linarith
  have hK : X.K0 - one = X.part X.genSet + X.part X.ngSet := by
    unfold Formalism.FourierDecayAlt.PB.Terms.K0
    rw [← hI]
    abel
  rw [hK]
  have hpar : ‖X.part X.genSet + X.part X.ngSet‖ ^ 2 ≤
      2 * ‖X.part X.genSet‖ ^ 2 + 2 * ‖X.part X.ngSet‖ ^ 2 := by
    have := norm_add_le (X.part X.genSet) (X.part X.ngSet)
    have h0 := norm_nonneg (X.part X.genSet + X.part X.ngSet)
    nlinarith [sq_nonneg (‖X.part X.genSet‖ - ‖X.part X.ngSet‖), norm_nonneg (X.part X.genSet),
      norm_nonneg (X.part X.ngSet)]
  have hfin : Pg * (X.pairAbs (X.big X.genSet) + A₁) + Pg * (X.pairAbs (X.big X.ngSet) + A₂) ≤
      Pg * (B + A₁ + A₂) := by
    rw [← mul_add]; apply mul_le_mul_of_nonneg_left _ hPg; linarith
  linarith

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AbstractDiagonalBoundCollisionsCountedOnceStatement
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 GlobalTheory.Core.Diag GlobalTheory.Core.Deg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abstractDiagonalBound_collisions_counted_once : ∀ (τ Rw I H H₁ : Type) [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁] (X : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (one : H) (Pg B A₁ A₂ : ℝ), 0 ≤ Pg → X.AbsConv → X.NormExpansionOn X.genSet → X.NormExpansionOn X.ngSet → X.GGBound Pg → X.RowOrth → X.CorankPos → Formalism.L2.SG.RowsOther.IdOne X one → X.pairAbs (X.big X.nzSet) ≤ B → X.pairSum (X.one X.genSet) ≤ A₁ → X.pairSum (X.one X.ngSet) ≤ A₂ → ‖X.K0 - one‖ ^ 2 ≤ 2 * Pg * (B + A₁ + A₂) := by
  first | exact @GlobalTheory.diag_abstract_collisions_once | exact GlobalTheory.diag_abstract_collisions_once | (intros; apply GlobalTheory.diag_abstract_collisions_once <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GramPoincareHilbertSchmidtDeviationLeSplit
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GramPoincareHilbertSchmidtDeviationLeSplit
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 GlobalTheory.Core.Diag GlobalTheory.Core.Deg

namespace GlobalTheory.Core.Rk

theorem hsNormSq_add_le_three_halves {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (A B : Wq →L[ℂ] Wp) :
    hsNormSq (A + B) ≤ 3 / 2 * hsNormSq A + 3 * hsNormSq B := by
  rw [hsNormSq_eq, hsNormSq_eq, hsNormSq_eq, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have h := norm_add_le (A (stdOrthonormalBasis ℂ Wq i)) (B (stdOrthonormalBasis ℂ Wq i))
  have h0 := norm_nonneg (A (stdOrthonormalBasis ℂ Wq i) + B (stdOrthonormalBasis ℂ Wq i))
  rw [ContinuousLinearMap.add_apply]
  nlinarith [sq_nonneg (‖A (stdOrthonormalBasis ℂ Wq i)‖ - 2 * ‖B (stdOrthonormalBasis ℂ Wq i)‖)]

theorem hsDev_le_split_three_halves : ∀ (D : D7) (u : D.what₂.Word), GlobalTheory.Core.Rk.hsDev D u ≤
    3 / 2 * hsNormSq (Kmat D.s u u - AdmissibleBoundsFromSource.Kpp D u u - ContinuousLinearMap.id ℂ (D.s.Cu u)) + 3 * hsNormSq (AdmissibleBoundsFromSource.Kpp D u u) := by
  intro D u
  have e : Kmat D.s u u - ContinuousLinearMap.id ℂ (D.s.Cu u) =
      (Kmat D.s u u - AdmissibleBoundsFromSource.Kpp D u u - ContinuousLinearMap.id ℂ (D.s.Cu u)) + AdmissibleBoundsFromSource.Kpp D u u := by abel
  unfold GlobalTheory.Core.Rk.hsDev
  rw [e]
  exact hsNormSq_add_le_three_halves _ _

end GlobalTheory.Core.Rk
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GramPoincareHilbertSchmidtDeviationLeSplitStatement
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 GlobalTheory.Core.Diag GlobalTheory.Core.Deg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gramPoincareHilbertSchmidtDeviation_le_split : ∀ (D : D7) (u : D.what₂.Word), GlobalTheory.Core.Rk.hsDev D u ≤ 3 / 2 * hsNormSq (Kmat D.s u u - AdmissibleBoundsFromSource.Kpp D u u - ContinuousLinearMap.id ℂ (D.s.Cu u)) + 3 * hsNormSq (AdmissibleBoundsFromSource.Kpp D u u) := by
  first | exact @GlobalTheory.Core.Rk.hsDev_le_split_three_halves | exact GlobalTheory.Core.Rk.hsDev_le_split_three_halves | (intros; apply GlobalTheory.Core.Rk.hsDev_le_split_three_halves <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DiagonalTheoremOfFourPointBounds
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 GlobalTheory.Core.Diag GlobalTheory.Core.Deg

noncomputable section
namespace GlobalTheory.Core.Diag
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exp_neg_le_two_fifths {x : ℝ} (hx : 2 ≤ x) : Real.exp (-x) ≤ 2 / 5 * Real.exp (-x / 2) := by
  have h2 : Real.exp (-x / 2) ≤ Real.exp (-1) := Real.exp_le_exp.2 (by linarith)
  have h1 : Real.exp (-1) < 2 / 5 := by
    rw [Real.exp_neg]
    have := Real.exp_one_gt_d9
    rw [inv_lt_comm₀ (Real.exp_pos 1) (by norm_num)]
    linarith
  have e : Real.exp (-x) = Real.exp (-x / 2) * Real.exp (-x / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [e]
  exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le

theorem diag_arith {H N₁ N₂ P s dd d E₂ E Γ₁ Γ₂ Γ : ℝ} (hH : H ≤ 3 / 2 * N₁ + 3 * N₂)
    (h₁ : N₁ ≤ 2 * P * (s * dd + E₂ * d + Γ₁ * dd + Γ₂ * dd)) (h₂ : N₂ ≤ d * E) (hP : P ≤ 6 / 5)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hdd : 0 ≤ dd) (hd : 0 ≤ d) (hE₂ : 0 ≤ E₂) (hE : E ≤ 2 / 5 * E₂)
    (hΓ₁ : 0 ≤ Γ₁) (hΓ₂ : 0 ≤ Γ₂) (hΓ : Γ₁ + Γ₂ ≤ Γ) :
    H ≤ 4 * ((Γ + 1) * dd + d * E₂) + 2 * d * E := by
  have hS : 0 ≤ s * dd + E₂ * d + Γ₁ * dd + Γ₂ * dd := by positivity
  have p1 : 2 * P * (s * dd + E₂ * d + Γ₁ * dd + Γ₂ * dd) ≤ 2 * (6 / 5) * (s * dd + E₂ * d + Γ₁ * dd + Γ₂ * dd) :=
    mul_le_mul_of_nonneg_right (by linarith) hS
  have p2 : s * dd ≤ dd := mul_le_of_le_one_left hdd hs1
  have p3 : (Γ₁ + Γ₂) * dd ≤ Γ * dd := mul_le_mul_of_nonneg_right hΓ hdd
  have p4 : d * E ≤ d * (2 / 5 * E₂) := mul_le_mul_of_nonneg_left hE hd
  nlinarith

theorem sDiagAt_of_points : ∀ (D : D7) (c : Formalism.L2.SG.ThmSOwn.ConcK D) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Γ₁ Γ₂ Γ : ℝ)
    (u : D.what₂.Word), 29 ≤ C' → 29 ≤ Cl → Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → 0 ≤ Γ₁ → 0 ≤ Γ₂ → Γ₁ + Γ₂ ≤ Γ →
    VanishingGramTermsBound c.Y u → CollS c.Y u →
    (c.Y.tO u u).pairSum ((c.Y.tO u u).one (c.Y.tO u u).genSet) ≤ Γ₁ * ddC c.X c.Y u u →
    (c.Y.tO u u).pairSum ((c.Y.tO u u).one (c.Y.tO u u).ngSet) ≤ Γ₂ * ddC c.X c.Y u u → SDiagAt D u Γ (1 / 2) := by
  intro D c large₂ C' Cl Cg cb Cu cT CT C0 Γ₁ Γ₂ Γ u hC' hCl h0 hg1 hg2 hg hG0 hColl hgen hng
  obtain ⟨hExp, hAbs⟩ := GlobalTheory.T.kernel_expansion_absolute_convergence_equal_words
  have hT := c.tie
  have hA : (c.Y.tO u u).AbsConv := hAbs D c.X c.Y u u hT
  have hK2 := Formalism.MainNotions.NonGenericAndKTwoTheorems.Hyp_of D large₂ C' Cl Cg cb Cu cT CT C0 h0.2.1 h0.1 h0.2.2 (by linarith)
  have hPg : PgC c.Y ≤ 6 / 5 := GlobalTheory.T.equalIdentificationPairPrice_le_six_fifths C' Cl Cg cb Cu cT CT C0 D large₂ c.X c.Y hK2
  have hPg0 : 0 ≤ PgC c.Y := Finset.prod_nonneg fun v _ => by positivity
  have hGB : (c.Y.tO u u).GGBound (PgC c.Y) :=
    Formalism.L2.SG.TermOp.ggBound c.Y.TR (c.Y.cs u) (c.Y.cs u) (c.Y.FN u) (c.Y.FN u) Formalism.L2.SG.Closed.TermsGGBound_holds
      c.Y.psi_ne (fun v => card_ge_three hK2.2 c.Y.TR v)
  have hNE := normExpSatTied_holds D c.X c.Y u u hT
  have hK0 := GlobalTheory.T.abstractDiagonalBound_collisions_counted_once _ _ _ _ _ (c.Y.tO u u) (oneC c.X c.Y u) (PgC c.Y) _ _ _ hPg0 hA hNE.1 hNE.2 hGB
    (Formalism.L2.SG.TermOp.rowOrth c.Y.TR (c.Y.cs u) (c.Y.cs u) (c.Y.FN u) (c.Y.FN u))
    (Formalism.L2.SG.KappaOffDiagonal.corankPosC_holds D c.X c.Y u u hT) (idOneC_holds D c.X c.Y u hT) hColl hgen hng
  have hsplit := GlobalTheory.T.gramPoincareHilbertSchmidtDeviation_le_split D u
  rw [Formalism.L2.SG.ThmSOwn.hsNormSq_diag c.hI (hExp D c.X c.Y u u hT) hA (Formalism.L2.SG.Pf.SatGram.idDegenerate_tO c.Y u u),
    Formalism.L2.SG.ThmSOwn.hsNormSq_Kpp c.hI hA] at hsplit
  have hdd : 0 ≤ ddC c.X c.Y u u := dd_nonneg hT u u
  have hdu : duC c.X c.Y u = (D.duS u : ℝ) := hT.2.2.1 u
  have hddE : ddC c.X c.Y u u = (D.duS u : ℝ) ^ 2 / D.what₂.Dstar := by
    unfold ddC; rw [hdu, hT.2.2.2.1]; ring
  have hd0 : (0 : ℝ) ≤ duC c.X c.Y u := Nat.cast_nonneg _

  have hk5 : 5 ≤ D.R.k := by have := D.R.two_le_m; have := D.R.m_add_three_le_k; omega
  have hf1 : 1 ≤ D.R.f := by
    have h4 : D.R.m ^ 4 ≤ D.R.f := h0.1.2.2.1
    have : 1 ≤ D.R.m ^ 4 := Nat.one_le_pow _ _ (by have := D.R.two_le_m; omega)
    omega
  have hkR : (5 : ℝ) ≤ D.R.k := by exact_mod_cast hk5
  have hfR : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf1
  have hlog : 1 ≤ Real.log D.R.k := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hx2 : 2 ≤ (D.R.k : ℝ) * D.R.f * Real.log D.R.k := by
    have : (5 : ℝ) * 1 * 1 ≤ (D.R.k : ℝ) * D.R.f * Real.log D.R.k := by gcongr
    linarith
  have hE := exp_neg_le_two_fifths hx2

  have g0 : (1 : ℝ) ≤ (D.host.g 0 : ℝ) := by exact_mod_cast (D.host.g_prime 0).one_lt.le
  have g1 : (1 : ℝ) ≤ (D.host.g 1 : ℝ) := by exact_mod_cast (D.host.g_prime 1).one_lt.le
  have hq : 1 ≤ Real.sqrt ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) := Real.one_le_sqrt.2 (one_le_mul_of_one_le_of_one_le g0 g1)
  have hi0 : 0 ≤ (Real.sqrt ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)))⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
  have key := diag_arith hsplit hK0 hG0.2 hPg (pow_nonneg hi0 _) (pow_le_one₀ hi0 (inv_le_one_of_one_le₀ hq)) hdd hd0
    (Real.exp_pos _).le hE hg1 hg2 hg
  have e1 : Real.exp (-((D.R.k : ℝ) * D.R.f * Real.log D.R.k) / 2) =
      Real.exp (-((1 / 2 : ℝ) * D.R.k * D.R.f * Real.log D.R.k)) := by
    congr 1; ring
  unfold SDiagAt
  unfold epsK at key
  rw [hddE, hdu, e1] at key
  calc _ ≤ _ := key
    _ = _ := by ring

end GlobalTheory.Core.Diag
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DiagonalTheoremOfFourPointBoundsStatement
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 GlobalTheory.Core.Diag GlobalTheory.Core.Deg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagonalTheorem_of_fourPointBounds : ∀ (D : D7) (c : Formalism.L2.SG.ThmSOwn.ConcK D) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Γ₁ Γ₂ Γ : ℝ) (u : D.what₂.Word), 29 ≤ C' → 29 ≤ Cl → Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → 0 ≤ Γ₁ → 0 ≤ Γ₂ → Γ₁ + Γ₂ ≤ Γ → VanishingGramTermsBound c.Y u → CollS c.Y u → (c.Y.tO u u).pairSum ((c.Y.tO u u).one (c.Y.tO u u).genSet) ≤ Γ₁ * ddC c.X c.Y u u → (c.Y.tO u u).pairSum ((c.Y.tO u u).one (c.Y.tO u u).ngSet) ≤ Γ₂ * ddC c.X c.Y u u → SDiagAt D u Γ (1 / 2) := by
  first | exact @GlobalTheory.Core.Diag.sDiagAt_of_points | exact GlobalTheory.Core.Diag.sDiagAt_of_points | (intros; apply GlobalTheory.Core.Diag.sDiagAt_of_points <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NonemptyConcreteRowDataOfFinitenessBundle
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NonemptyConcreteRowDataOfFinitenessBundle
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 GlobalTheory.Core.Diag GlobalTheory.Core.Deg

namespace GlobalTheory.Core.Diag

theorem concK_of_finX : Formalism.L2.SG.Pf.WuDecayOfGap → ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT : ℝ) (S : Formalism.L2.SG.SpectralTiesReal.STies D), 29 ≤ C' → 29 ≤ Cl → FinX S.Y → Formalism.L2.SG.Pf.LocCP.LocTied D → TFrameAt D → StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT → Nonempty (Formalism.L2.SG.ThmSOwn.ConcK D) := by
  intro hWu D large₂ C' Cl Cg cb Cu cT CT S hC' hCl hFX hL hTF hH
  have hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D := Formalism.L2.SG.ThmSOwn.gap_hypothesis_of_hypotheses hH (by linarith) hC'
  have hK := Formalism.L2.SG.Closed.level_subgroup_properties S.X
  exact ⟨Formalism.L2.SG.ThmSOwn.concKOf S ⟨hFX, hK, fun u => Formalism.L2.SG.Pf.RegroupPf.neatKu_K2Level D S.X S.Y u hK,
    (hWu D hG S.X).1, (hWu D hG S.X).2, hL, hTF⟩⟩

end GlobalTheory.Core.Diag
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NonemptyConcreteRowDataOfFinitenessBundleStatement
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 GlobalTheory.Core.Diag GlobalTheory.Core.Deg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_concreteRowData_of_finitenessBundle : Formalism.L2.SG.Pf.WuDecayOfGap → ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT : ℝ) (S : Formalism.L2.SG.SpectralTiesReal.STies D), 29 ≤ C' → 29 ≤ Cl → FinX S.Y → Formalism.L2.SG.Pf.LocCP.LocTied D → TFrameAt D → StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT → Nonempty (Formalism.L2.SG.ThmSOwn.ConcK D) := by
  first | exact @GlobalTheory.Core.Diag.concK_of_finX | exact GlobalTheory.Core.Diag.concK_of_finX | (intros; apply GlobalTheory.Core.Diag.concK_of_finX <;> assumption)
end
end

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 GlobalTheory.Core.Diag GlobalTheory.Core.Deg

namespace GlobalTheory.Core.Rk

theorem exp_add_exp_le_exp_max_succ {C₁ C₂ y : ℝ} (hy : 1 ≤ y) :
    Real.exp (C₁ * y) + Real.exp (C₂ * y) ≤ Real.exp ((max C₁ C₂ + 1) * y) := by
  have hy0 : 0 ≤ y := by linarith
  have a1 : Real.exp (C₁ * y) ≤ Real.exp (max C₁ C₂ * y) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (le_max_left _ _) hy0)
  have a2 : Real.exp (C₂ * y) ≤ Real.exp (max C₁ C₂ * y) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (le_max_right _ _) hy0)
  have a3 : (2 : ℝ) ≤ Real.exp y := by
    have := Real.add_one_le_exp y
    linarith
  have e : Real.exp ((max C₁ C₂ + 1) * y) = Real.exp (max C₁ C₂ * y) * Real.exp y := by
    rw [← Real.exp_add]; ring_nf
  rw [e]
  have hp := Real.exp_pos (max C₁ C₂ * y)
  nlinarith

theorem diagonalRow_bound_from_windowWidthThree : Formalism.L2.SG.Pf.WuDecayOfGap → On {3} VanishingGramTermsBound → On {3} CollS → OneOn {3} true →
    OneOn {3} false →
    GlobalTheory.Core.Rk.RowDiag (fun D L C' => GlobalTheory.Core.Rk.IsScaleWithBoundedGamma D L C' ∧ ∀ u, GlobalTheory.Core.Rk.RankMu D u) := by
  intro hW hG hCo h1 h2 Cg cb Cu cT CT hcb hcT
  obtain ⟨C₁, hC₁, t₁, H₁⟩ := h1 Cg cb Cu cT CT hcb hcT
  obtain ⟨C₂, _, t₂, H₂⟩ := h2 Cg cb Cu cT CT hcb hcT
  obtain ⟨tG, HG⟩ := hG Cg cb Cu cT CT hcb hcT
  obtain ⟨tC, HC⟩ := hCo Cg cb Cu cT CT hcb hcT
  refine ⟨max C₁ C₂ + 1, max (max (max t₁ t₂) (max tG tC)) 29, max (max (max t₁ t₂) (max tG tC)) 29,
    by linarith [le_max_left C₁ C₂], ?_⟩
  intro C' Cl hC' hCl D L u hT hE hD
  obtain ⟨⟨large₂, hL, h8, h1G⟩, hR⟩ := hE
  obtain ⟨hTies, hAdm, hHL, hNW, hTF⟩ := hD
  subst hL
  have hS0 : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT := ⟨h8, hHL.2⟩
  have hD0 : StandingNumericalData D 3 := GlobalTheory.T.columnDimension_window_three_of_columnCount D hNW hR
  have hH0 : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT 3 := ⟨hS0, hD0, by norm_num⟩
  obtain ⟨S, hF, hLT⟩ := hT.trueD.sTies
  have m1 : ∀ {a b c d e : ℝ}, max (max (max a b) (max c d)) 29 ≤ e →
      a ≤ e ∧ b ≤ e ∧ c ≤ e ∧ d ≤ e ∧ 29 ≤ e := by
    intro a b c d e h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> refine le_trans ?_ h <;> simp
  obtain ⟨a1, a2, a3, a4, a5⟩ := m1 hC'
  obtain ⟨b1, b2, b3, b4, b5⟩ := m1 hCl
  obtain ⟨c⟩ := GlobalTheory.T.nonempty_concreteRowData_of_finitenessBundle hW D large₂ C' Cl Cg cb Cu cT CT S a5 b5 hF hLT hTF hS0
  have hAC : (c.Y.tO u u).AbsConv := kExp_absConv_tied.2 D c.X c.Y u u c.tie
  have g0 := HG 3 rfl C' Cl a3 b3 D large₂ c.X c.Y c.hF c.hI u h1G hTies hAdm hH0 c.tie hAC
  have gc := HC 3 rfl C' Cl a4 b4 D large₂ c.X c.Y c.hF c.hI u h1G hTies hAdm hH0 c.tie hAC
  have o1 := H₁ 3 rfl C' Cl a1 b1 D large₂ c.X c.Y u hTies hH0 c.tie hAC
  have o2 := H₂ 3 rfl C' Cl a2 b2 D large₂ c.X c.Y u hTies hH0 c.tie hAC
  simp only [if_true, Bool.false_eq_true, if_false] at o1 o2
  have hf : (1 : ℝ) ≤ D.R.f := by
    have h4 : D.R.m ^ 4 ≤ D.R.f := hHL.2.2.1
    have : 1 ≤ D.R.m ^ 4 := Nat.one_le_pow _ _ (by have := D.R.two_le_m; omega)
    exact_mod_cast le_trans this h4
  have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by have := D.R.two_le_m; omega : 1 ≤ D.R.m)
  have hL1 : 1 < large₂.sc.L := hHL.1
  have hy : 1 ≤ (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L := by
    have : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 5 := one_le_pow₀ hm
    have h2' : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 5 * D.R.f := one_le_mul_of_one_le_of_one_le this hf
    exact one_le_mul_of_one_le_of_one_le h2' hL1.le
  have hg : ∀ C, gamL D large₂.sc.L C = Real.exp (C * ((D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L)) := by
    intro C; unfold gamL; congr 1; ring
  have hsum : gamL D large₂.sc.L C₁ + gamL D large₂.sc.L C₂ ≤ gamL D large₂.sc.L (max C₁ C₂ + 1) := by
    rw [hg, hg, hg]; exact exp_add_exp_le_exp_max_succ hy
  have key := GlobalTheory.T.diagonalTheorem_of_fourPointBounds D c large₂ C' Cl Cg cb Cu cT CT 3 (gamL D large₂.sc.L C₁) (gamL D large₂.sc.L C₂)
    (gamL D large₂.sc.L (max C₁ C₂ + 1)) u a5 b5 hH0 (Real.exp_pos _).le (Real.exp_pos _).le hsum g0 gc o1 o2
  unfold SDiagAt at key
  show TwoTerm D u _ _
  unfold TwoTerm
  rw [d0_eq]
  have e1 : gamL D large₂.sc.L (max C₁ C₂ + 1) = Real.exp ((max C₁ C₂ + 1) * mfL D large₂.sc.L) := by
    rw [hg]; rfl
  have e2 : Real.exp (-((1 / 2 : ℝ) * D.R.k * D.R.f * Real.log D.R.k)) = Real.exp (-(kfk D / 2)) := by
    unfold kfk; congr 1; ring
  have e3 : Real.exp (-((D.R.k : ℝ) * D.R.f * Real.log D.R.k)) = Real.exp (-kfk D) := by
    unfold kfk; rfl
  rw [e1, e2, e3] at key
  refine le_trans key (le_of_eq ?_)
  ring

end GlobalTheory.Core.Rk
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DiagonalRowOfSiegelWeilUnitary
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Rk

theorem rowDiag_of_siegelWeilUnitary
    (hSW : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent) :
    GlobalTheory.Core.Rk.RowDiag (fun D L C' => GlobalTheory.Core.Rk.IsScaleWithBoundedGamma D L C' ∧ ∀ u, GlobalTheory.Core.Rk.RankMu D u) := by
  have hDeg := GlobalTheory.T.degenerateTerms_and_collisionBounds_uniform_widths
  have hOne := GlobalTheory.T.corankOnePairsFamilyBounds_of_siegelWeil hSW 3
  exact GlobalTheory.Core.Rk.diagonalRow_bound_from_windowWidthThree GlobalTheory.wuDecayOfGap (hDeg.1 3) (hDeg.2 3) hOne.1 hOne.2

end GlobalTheory.Core.Rk
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DiagonalRowOfSiegelWeilUnitaryStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem _root_.GlobalTheory.T.diagonalRow_of_siegelWeil_unitary :
    HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent →
      GlobalTheory.Core.Rk.RowDiag (fun D L C' =>
        GlobalTheory.Core.Rk.IsScaleWithBoundedGamma D L C' ∧ ∀ u, GlobalTheory.Core.Rk.RankMu D u) :=
  GlobalTheory.Core.Rk.rowDiag_of_siegelWeilUnitary
end
