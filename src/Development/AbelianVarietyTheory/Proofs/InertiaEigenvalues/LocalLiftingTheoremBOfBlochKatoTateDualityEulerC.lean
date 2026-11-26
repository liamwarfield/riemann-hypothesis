module

public import Formalism.SharpRestriction.LevelLetterCocycles.FrobeniusStatementOfFontaine
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFullFaithfulExactPsi
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineDcris
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalConstantsFromAdmittedLocalGaloisStatements
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsMirabolicWhittakerStageOfIsCuspForm
public import Formalism.SharpRestriction.LevelLetterCocycles.ArcCoordinatesFinal
public import Formalism.SharpRestriction.LevelLetterCocycles.UniversalGeneralStatementHolds
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivProdIrrZero
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLiftingTheoremBOfBlochKatoTateDualityEulerC
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLiftingTheoremBHypothesesAdmitted
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachRelayLemmaArcCoordinateHypotheses
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachRelayLemmaArcCoordinateHypotheses
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.NQ

theorem relay_and_arc_inputs : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK →
    Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F), UnusedSlot80.RelayArcLifting D HW F ∧ UnusedSlot80.AdmArcA D HW F Cm := by
  intro hBK hTD hEC D HW F Cm
  obtain ⟨_, _, p3, p4, p5, _, _, _, p9, _⟩ := GlobalTheory.T.wachLattice_laterClauses_hold D HW F Cm
  obtain ⟨_, _, hW1, _, _, hH, hTr, _⟩ := GlobalTheory.T.localConstants_from_admitted_local_Galois_statements hBK hTD hEC D HW F Cm
  obtain ⟨hSat, _, _, _, _, _, _, hF1, _, hF2, _⟩ := GlobalTheory.T.arcTheorem_tools_of_wachModuleConclusions D HW F Cm
  exact ⟨UnusedSlot80.relay_general_statement D HW F ⟨p5, p9, hH, hTr, hSat, hF1, hF2⟩,
    ⟨p3, p4, p5, p9, hH, hTr, hW1, hSat⟩⟩

end GlobalTheory.NQ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachRelayLemmaArcCoordinateHypothesesStatement
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachRelayLemma_arcCoordinateHypotheses : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), UnusedSlot80.RelayArcLifting D HW F ∧ UnusedSlot80.AdmArcA D HW F Cm := by
  first | exact @GlobalTheory.NQ.relay_and_arc_inputs | exact GlobalTheory.NQ.relay_and_arc_inputs | (intros; apply GlobalTheory.NQ.relay_and_arc_inputs <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassSplittingAlongArcsOfAdmissible
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassSplittingAlongArcsOfAdmissible
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem classSplitAlongArcs : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), UnusedSlot80.AdmSplitA D HW F Cm → UnusedSlot80.AdmArcA D HW F Cm → DeltaInvariantLattices.WachLatticeFreeGlobal D HW F → DeltaInvariantLattices.P6 D HW F → LiftingTheory.WachKillsQuotients D HW F → InvariantsGenerators.LitFont D HW F → LiftingTheory.adm23 D HW F → TruncatedSeriesCountingBounds.adm9 D → RamifiedCoefficientChains.adm11 D → UnusedSlot80.SplittingArcLifting D HW F Cm :=
  UnusedSlot80.split_case_A_final

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassSplittingAlongArcsOfAdmissibleStatement
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classSplitting_along_arcs_of_admissible : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), UnusedSlot80.AdmSplitA D HW F Cm → UnusedSlot80.AdmArcA D HW F Cm → DeltaInvariantLattices.WachLatticeFreeGlobal D HW F → DeltaInvariantLattices.P6 D HW F → LiftingTheory.WachKillsQuotients D HW F → InvariantsGenerators.LitFont D HW F → LiftingTheory.adm23 D HW F → TruncatedSeriesCountingBounds.adm9 D → RamifiedCoefficientChains.adm11 D → UnusedSlot80.SplittingArcLifting D HW F Cm := by
  first | exact @GlobalTheory.classSplitAlongArcs | exact GlobalTheory.classSplitAlongArcs | (intros; apply GlobalTheory.classSplitAlongArcs <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleArcDatumGivesArcProperty
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleArcDatumGivesArcProperty
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem admissibleArcDatum_gives_arcProperty : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
    UnusedSlot80.AdmArcA D HW F Cm → DeltaInvariantLattices.WachLatticeFreeGlobal D HW F → RamifiedCoefficientChains.adm11 D → UnusedSlot80.ArcLiftingCoordinates D HW F Cm :=
  fun D HW F Cm hA h1f h11 => UnusedSlot80.arc_coordinates_final D HW F Cm hA h1f h11

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleArcDatumGivesArcPropertyStatement
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arcCoordinatesCaseA_of_admArcA_of_P1free_of_adm11 : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), UnusedSlot80.AdmArcA D HW F Cm → DeltaInvariantLattices.WachLatticeFreeGlobal D HW F → RamifiedCoefficientChains.adm11 D → UnusedSlot80.ArcLiftingCoordinates D HW F Cm := by
  first | exact @GlobalTheory.admissibleArcDatum_gives_arcProperty | exact GlobalTheory.admissibleArcDatum_gives_arcProperty | (intros; apply GlobalTheory.admissibleArcDatum_gives_arcProperty <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineUniversalPartCaseA
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineUniversalPartCaseA
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem universalPart_caseA :
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
      UnusedSlot80.AdmUnivA D HW F Cm → DeltaInvariantLattices.P9 D HW F → LiftingTheory.ConclusionH D HW F → TruncatedSeriesCountingBounds.adm15 D →
      UnusedSlot80.UniversalComponentCaseA D HW F Cm :=
  fun D HW F Cm hAdm h9 hH h15 => Formalism.MainNotions.UnusedSlot80.universal_general_statement_holds D HW F Cm hAdm h9 hH h15

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineUniversalPartCaseAStatement
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystallineUniversalPart_caseA : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), UnusedSlot80.AdmUnivA D HW F Cm → DeltaInvariantLattices.P9 D HW F → LiftingTheory.ConclusionH D HW F → TruncatedSeriesCountingBounds.adm15 D → UnusedSlot80.UniversalComponentCaseA D HW F Cm := by
  first | exact @GlobalTheory.universalPart_caseA | exact GlobalTheory.universalPart_caseA | (intros; apply GlobalTheory.universalPart_caseA <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DcrisExactStrictElementwiseCrystalline
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DcrisExactStrictElementwiseCrystalline
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem dcris_exact_strict_elementwise : ∀ D : D7, Formalism.MainNotions.TruncatedSeriesCountingBounds.adm9 D := by
  intro D l _ K LL
  have hA := (GlobalTheory.T.ramifiedCoefficientChains_adm11 D l K LL).1
  intro hbij V₀ V₁ V₂ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ρ₀ ρ₁ ρ₂ ι π _ _ _ _ _ _ _ _ _ hιe hπe hinj hsurj
    hker c₀ c₁ c₂
  obtain ⟨h1, h2, h3, h4⟩ :=
    hA hbij V₀ ρ₀ V₁ ρ₁ V₂ ρ₂ ι π hιe hπe hinj hsurj hker.symm c₀ c₁ c₂
  refine ⟨h1, ?_, h3, fun a => (h4 a).1, ?_⟩
  · intro x hx hπx
    exact Submodule.mem_map.mp (h2.ge ⟨hx, hπx⟩)
  · intro a y hy hyF
    exact (h4 a).2.ge ⟨hy, hyF⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DcrisExactStrictElementwiseCrystallineStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dcris_exact_strict_elementwise_crystalline : ∀ D : D7, Formalism.MainNotions.TruncatedSeriesCountingBounds.adm9 D := by
  first | exact @GlobalTheory.dcris_exact_strict_elementwise | exact GlobalTheory.dcris_exact_strict_elementwise | (intros; apply GlobalTheory.dcris_exact_strict_elementwise <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DDeRhamEqDCrisOfUnramified
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DDeRhamEqDCrisOfUnramified
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.FontaineAdmissibility

theorem intersectionNumber_baseChange : ∀ D : D7, Formalism.MainNotions.TruncatedSeriesCountingBounds.adm15 D :=
  fun D l _ K LL hb V _ _ _ _ _ ρ _ _ _ hc =>
    GlobalTheory.Per.DdREqDcris.map_Dcris_eq_DdR l (D.loc l) (D.locA l) (D.locT l) K LL hb V ρ hc

end GlobalTheory.FontaineAdmissibility
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DDeRhamEqDCrisOfUnramifiedStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dDeRham_eq_dCris_of_unramified : ∀ D : D7, Formalism.MainNotions.TruncatedSeriesCountingBounds.adm15 D := by
  first | exact @GlobalTheory.FontaineAdmissibility.intersectionNumber_baseChange | exact GlobalTheory.FontaineAdmissibility.intersectionNumber_baseChange | (intros; apply GlobalTheory.FontaineAdmissibility.intersectionNumber_baseChange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLiftingTheoremBHypothesesAdmitted
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.TheoremBAdm

theorem admissible_ranks_of_CMDatum : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK →
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
      ArcLiftingSetup.admitted D HW F Cm 10 23 32 32 8 := by
  intro hBK hTD hEC D HW F Cm
  have hN1 := GlobalTheory.T.wachLattice_laterClauses_hold D HW F Cm
  obtain ⟨hP1, -, -, -, -, hP6, -, hP8, hP9, -⟩ := hN1
  have h54 := GlobalTheory.T.localConstants_from_admitted_local_Galois_statements hBK hTD hEC D HW F Cm
  obtain ⟨-, ⟨hWX, -⟩, hW1, -, -, hH, -, -⟩ := h54
  have hB := GlobalTheory.T.arcTheorem_tools_of_wachModuleConclusions D HW F Cm
  obtain ⟨hSat, -, hSatP, hPi0, hKL, hKill, -, hF1, -⟩ := hB
  obtain ⟨hRelay, hArcAdm⟩ := GlobalTheory.T.wachRelayLemma_arcCoordinateHypotheses hBK hTD hEC D HW F Cm
  have hA11 := GlobalTheory.T.ramifiedCoefficientChains_adm11 D
  have hArc := GlobalTheory.T.arcCoordinatesCaseA_of_admArcA_of_P1free_of_adm11 D HW F Cm hArcAdm hP1 hA11
  have hJ := (GlobalTheory.jumps_exact_adm D HW F).2
  have hExt := GlobalTheory.HerrExtClass.herr_extension_class_formula D HW F
  have hAdm9 := GlobalTheory.T.dcris_exact_strict_elementwise_crystalline D
  have hSplit := GlobalTheory.T.classSplitting_along_arcs_of_admissible D HW F Cm ⟨hP8, hP9, hW1, hJ, hExt, hF1, hRelay, hArc⟩ hArcAdm hP1 hP6 hWX
    (GlobalTheory.T.fontaine_fullFaithful_exact_psi D HW F) hJ hAdm9 hA11
  have hUniv := GlobalTheory.T.crystallineUniversalPart_caseA D HW F Cm ⟨hSat, hKL, hPi0, hArc⟩ hP9 hH (GlobalTheory.T.dDeRham_eq_dCris_of_unramified D)
  exact ⟨(GlobalTheory.T.wachModuleLocalConclusions_usedForms D HW F Cm).1, GlobalTheory.T.localConstants_from_admitted_local_Galois_statements hBK hTD hEC D HW F Cm, hSat, hSatP, hKill,
    ArcLiftingSetup.content_divisibility_clause D, GlobalTheory.T.h1fGeneratorBoundAll_loc D, hRelay, hArc, hSplit, hUniv, hAdm9, GlobalTheory.T.blochKato_crystalline_extension_criterion D⟩

end GlobalTheory.TheoremBAdm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLiftingTheoremBHypothesesAdmittedStatement
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localLifting_theoremB_hypotheses_admitted : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), ArcLiftingSetup.admitted D HW F Cm 10 23 32 32 8 := by
  first | exact @GlobalTheory.TheoremBAdm.admissible_ranks_of_CMDatum | exact GlobalTheory.TheoremBAdm.admissible_ranks_of_CMDatum | (intros; apply GlobalTheory.TheoremBAdm.admissible_ranks_of_CMDatum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TheoremBOfLocalFilteredHypotheses
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TheoremBOfLocalFilteredHypotheses
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem theoremB_of_admitted_inputs :
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
    ∀ (C CR CA CB CK Ckap : ℝ), (320 : ℝ) ≤ C → CrystallineLiftingBounds.adm22 D HW F → CrystallineLiftingBounds.adm23 D HW F →
      Formalism.MainNotions.N.LetterConditionGlobal D HW F → ArcLiftingSetup.Stmt D HW F Cm C CR CA CB CK Ckap :=
  fun D HW F Cm C CR CA CB CK Ckap hC a22 a23 c4 =>
    Formalism.MainNotions.N.Ln17.frobenius_statement_of_fontaine D HW F Cm C CR CA CB CK Ckap hC a22 a23 c4

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TheoremBOfLocalFilteredHypothesesStatement
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theoremB_of_localFilteredHypotheses : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), ∀ (C CR CA CB CK Ckap : ℝ), (320 : ℝ) ≤ C → CrystallineLiftingBounds.adm22 D HW F → CrystallineLiftingBounds.adm23 D HW F → Formalism.MainNotions.N.LetterConditionGlobal D HW F → ArcLiftingSetup.Stmt D HW F Cm C CR CA CB CK Ckap := by
  first | exact @GlobalTheory.theoremB_of_admitted_inputs | exact GlobalTheory.theoremB_of_admitted_inputs | (intros; apply GlobalTheory.theoremB_of_admitted_inputs <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLiftingTheoremBOfBlochKatoTateDualityEulerC
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem theoremB_closing : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK →
    Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F), ∀ C : ℝ, (320 : ℝ) ≤ C → ArcLiftingSetup.aux₃ D HW F C := by
  intro hBK hTD hEC D HW F Cm C hC
  have h22 : CrystallineLiftingBounds.adm22 D HW F := GlobalTheory.FontaineIneq.one_place_admissible_of_gap_constant_le D HW F
  have h23 : CrystallineLiftingBounds.adm23 D HW F := (GlobalTheory.jumps_exact_adm D HW F).1
  have hN1 : Formalism.MainNotions.DeltaInvariantLattices.DeltaInvariantNormBound D HW F Cm := GlobalTheory.T.wachLattice_laterClauses_hold D HW F Cm
  have hC4 : Formalism.MainNotions.N.LetterConditionGlobal D HW F := GlobalTheory.T.letterConditionGlobal_of_N1used D HW F Cm hN1
  exact GlobalTheory.T.theoremB_of_localFilteredHypotheses D HW F Cm C 10 23 32 32 8 hC h22 h23 hC4 (GlobalTheory.T.localLifting_theoremB_hypotheses_admitted hBK hTD hEC D HW F Cm)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLiftingTheoremBOfBlochKatoTateDualityEulerCStatement
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localLiftingTheoremB_of_blochKato_tateDuality_eulerChar : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), ∀ C : ℝ, (320 : ℝ) ≤ C → ArcLiftingSetup.aux₃ D HW F C := by
  first | exact @GlobalTheory.theoremB_closing | exact GlobalTheory.theoremB_closing | (intros; apply GlobalTheory.theoremB_closing <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSmoothCharCompNorm
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LBC
open scoped Topology

namespace GlobalTheory.LBC.Inh
open ValuativeRel Filter

section Cont
variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [Algebra k k']

theorem isOpen_lt_one (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] :
    IsOpen {x : F | valuation F x < 1} := by
  refine isOpen_iff_mem_nhds.2 fun x hx => (IsValuativeTopology.mem_nhds_iff').2 ⟨1, fun z hz => ?_⟩
  have e : z = (z - x) + x := by ring
  show valuation F z < 1
  rw [e]
  have hz' : valuation F (z - x) < 1 := by simpa using hz
  exact (valuation F).map_add_lt hz' hx

theorem lt_one_of_lt_one (hc : Continuous (algebraMap k k')) {z : k} (h : valuation k z < 1) :
    valuation k' (algebraMap k k' z) < 1 := by
  have h1 := (GroundTheory.LocalField.tendsto_pow_atTop_nhds_zero_iff z).2 h
  have h2 := (hc.tendsto 0).comp h1
  rw [map_zero] at h2
  apply (GroundTheory.LocalField.tendsto_pow_atTop_nhds_zero_iff (algebraMap k k' z)).1
  refine h2.congr fun n => ?_
  simp [Function.comp_apply, map_pow]

theorem lt_one_iff (hc : Continuous (algebraMap k k')) (z : k) :
    valuation k' (algebraMap k k' z) < 1 ↔ valuation k z < 1 := by
  refine ⟨fun h => ?_, lt_one_of_lt_one hc⟩
  by_contra hz
  push_neg at hz
  have hz0 : z ≠ 0 := by
    rintro rfl; simp at hz
  rcases hz.lt_or_eq with hlt | heq
  · have h2 : valuation k z⁻¹ < 1 := by rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hlt
    have h3 := lt_one_of_lt_one (k' := k') hc h2
    have h4 : valuation k' (algebraMap k k' z) * valuation k' (algebraMap k k' z⁻¹) = 1 := by
      rw [← map_mul, ← map_mul, mul_inv_cancel₀ hz0, map_one, map_one]
    have := lt_of_le_of_lt (mul_le_of_le_one_left' h.le) h3
    rw [h4] at this
    exact lt_irrefl _ this
  · set S : Set k := {x | valuation k x ≤ 1} ∩ {x | valuation k x < 1}ᶜ with hS
    have hSc : IsCompact S :=
      (IsNonarchimedeanLocalField.isCompact_closedBall k 1).inter_right (isOpen_lt_one k).isClosed_compl
    haveI : T2Space k' := GroundTheory.LocalField.t2Space_of_isNonarchimedeanLocalField k'
    have hI : IsClosed (algebraMap k k' '' S) := (hSc.image hc).isClosed
    have h0 : (0 : k') ∉ algebraMap k k' '' S := by
      rintro ⟨x, hx, hx0⟩
      rw [map_eq_zero_iff _ (algebraMap k k').injective] at hx0
      subst hx0
      simp [hS] at hx
    have ht := (GroundTheory.LocalField.tendsto_pow_atTop_nhds_zero_iff (algebraMap k k' z)).2 h
    obtain ⟨n, hn⟩ := (ht.eventually (hI.isOpen_compl.mem_nhds h0)).exists
    apply hn
    refine ⟨z ^ n, ?_, by rw [map_pow]⟩
    simp [hS, map_pow, ← heq]

theorem valuativeExtension (hc : Continuous (algebraMap k k')) : ValuativeExtension k k' :=
  ⟨fun {a b} => GroundTheory.LocalField.vle_map_iff_of_valuation_lt_one_iff
    (algebraMap k k') (lt_one_iff hc) a b⟩

theorem continuous_algNorm [FiniteDimensional k k'] (hc : Continuous (algebraMap k k')) :
    Continuous (Algebra.norm k : k' → k) := by
  classical
  haveI := valuativeExtension hc
  haveI := GroundTheory.LocalField.isModuleTopology k k'
  let b := Module.finBasis k k'
  have h : (Algebra.norm k : k' → k) = fun t => (Algebra.leftMulMatrix b t).det := by
    funext t; exact Algebra.norm_eq_matrix_det b t
  rw [h]
  refine Continuous.matrix_det ?_
  refine continuous_pi fun i => continuous_pi fun j => ?_
  have : (fun t : k' => Algebra.leftMulMatrix b t i j) =
      fun t => (b.coord i) (LinearMap.mulRight k (b j) t) := by
    funext t; simp [Algebra.leftMulMatrix_eq_repr_mul]
  rw [this]
  exact IsModuleTopology.continuous_of_linearMap ((b.coord i).comp (LinearMap.mulRight k (b j)))

theorem isSmoothChar_comp_norm [FiniteDimensional k k'] (hc : Continuous (algebraMap k k')) {χ : kˣ →* ℂˣ}
    (hχ : IsSmoothChar χ) : IsSmoothChar (χ.comp (Units.map (Algebra.norm k : k' →* k))) :=
  hχ.comp _ (Continuous.units_map _ (continuous_algNorm hc))

end Cont

end GlobalTheory.LBC.Inh
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TrivialLevelCosetRepresentativeMemLevel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RawLift.Eu

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]


open Classical in
def fid (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) : AE D :=
  if h : ∃ f, IsFinIdem D v f then h.choose else 0

def locSet (R : RealDat D A Ks) (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.host.F)) : Set (GA D (Wc D i)) :=
  {g | g ∈ GfC (Wc D i) ∧ SuppF (Wc D i) (fid D v) g}

def LX (R : RealDat D A Ks) (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.host.F)) : Type :=
  Quotient ((QuotientGroup.leftRel (levW R i)).comap (Subtype.val : locSet R i v → GA D (Wc D i)))

theorem one_mem_locSet (R : RealDat D A Ks) (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    (1 : GA D (Wc D i)) ∈ locSet R i v := by
  refine ⟨(GfC (Wc D i)).one_mem, ?_⟩
  have : Formalism.L2.Theta.mt (Wc D i) 1 = 1 := rfl
  intro a b
  simp [this]

def lx0 (R : RealDat D A Ks) (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.host.F)) : LX R i v :=
  Quotient.mk _ ⟨1, one_mem_locSet R i v⟩

def rep {R : RealDat D A Ks} {i : Fin D.R.m} {v : HeightOneSpectrum (𝓞 D.host.F)} (x : LX R i v) : GA D (Wc D i) :=
  (Quotient.out x).1


open Classical in
def Bop (R : RealDat D A Ks) (i : Fin D.R.m) (γ : GA D (Wc D i)) :
    (R.HW i (sg0 D A)).H →L[ℂ] (R.HW i (sg0 D A)).H :=
  if h : ∃ B : (R.HW i (sg0 D A)).H →L[ℂ] (R.HW i (sg0 D A)).H, ‖B‖ ≤ 1 ∧ ∀ x y, trPair R i γ x y = ⟪x, B y⟫_ℂ then
    h.choose else 0


open Classical in
def famProd (R : RealDat D A Ks) (i : Fin D.R.m) (F : ∀ v, LX R i v) : GA D (Wc D i) :=
  if h : {w | F w ≠ lx0 R i w}.Finite then (h.toFinset.toList.map fun w => rep (F w)).prod else 1

def Bfam (R : RealDat D A Ks) (i : Fin D.R.m) (F : ∀ v, LX R i v) :
    (R.HW i (sg0 D A)).H →L[ℂ] (R.HW i (sg0 D A)).H :=
  Bop R i (famProd R i F)

def acoef (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (μ : Measure (WO (Vc D i) (Wc D i)))
    (𝓕 : Set (WO (Vc D i) (Wc D i))) (v : HeightOneSpectrum (𝓞 D.host.F)) (x : LX R i v) : ℂ :=
  coef R i t μ 𝓕 (rep x)

def Zop (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (μ : Measure (WO (Vc D i) (Wc D i)))
    (𝓕 : Set (WO (Vc D i) (Wc D i))) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    (R.HW i (sg0 D A)).H →L[ℂ] (R.HW i (sg0 D A)).H :=
  ∑' x : LX R i v, acoef R i t μ 𝓕 v x • Bop R i (rep x)

section Helpers
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem bop_one {R : RealDat D A Ks} {i : Fin D.R.m} (hTL : TransLaws R i) : Eu.Bop R i 1 = 1 := by
  have h6 : ∀ x y, trPair R i 1 x y = ⟪x, y⟫_ℂ := hTL.2.2.2.2.2
  have hex : ∃ B : (R.HW i (sg0 D A)).H →L[ℂ] (R.HW i (sg0 D A)).H, ‖B‖ ≤ 1 ∧
      ∀ x y, trPair R i 1 x y = ⟪x, B y⟫_ℂ :=
    ⟨1, ContinuousLinearMap.norm_id_le, fun x y => by rw [h6]; rfl⟩
  unfold Eu.Bop
  rw [dite_eq_left hex]
  apply ContinuousLinearMap.ext
  intro y
  apply ext_inner_left ℂ
  intro x
  rw [← hex.choose_spec.2 x y, h6]
  rfl

theorem bop_norm (R : RealDat D A Ks) (i : Fin D.R.m) (γ : GA D (Wc D i)) : ‖Eu.Bop R i γ‖ ≤ 1 := by
  unfold Eu.Bop
  split_ifs with h
  · exact h.choose_spec.1
  · simp

theorem trivial_level_coset_representative_mem_level (R : RealDat D A Ks) (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    Eu.rep (Eu.lx0 R i v) ∈ levW R i := by
  have h := Quotient.mk_out (s := (QuotientGroup.leftRel (levW R i)).comap
    (Subtype.val : Eu.locSet R i v → GA D (Wc D i))) ⟨1, Eu.one_mem_locSet R i v⟩
  rw [Setoid.comap_rel, QuotientGroup.leftRel_apply] at h
  have h2 := h
  have h3 := (levW R i).inv_mem h2
  simpa [Eu.rep, Eu.lx0] using h3

theorem local_coefficient_trivial_level_coset {R : RealDat D A Ks} {i : Fin D.R.m} {t : T} (hLF : LevFix R i t) (hVN : VecNe R i t) {μ 𝓕}
    (hμ : IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    Eu.acoef R i t μ 𝓕 v (Eu.lx0 R i v) = 1 := by
  unfold Eu.acoef
  have := Model.coef_mul_lev R i t hLF μ 𝓕 1 _ (trivial_level_coset_representative_mem_level R i v)
  rw [one_mul] at this
  rw [this, Model.coef_one R i t hVN μ 𝓕 hμ]

theorem localCosetFamilyRepresentativeProd_trivial_eq_one (R : RealDat D A Ks) (i : Fin D.R.m) : Eu.famProd R i (Eu.lx0 R i) = 1 := by
  unfold Eu.famProd
  have hf : {w | Eu.lx0 R i w ≠ Eu.lx0 R i w}.Finite := by simp
  rw [dite_eq_left hf]
  have : hf.toFinset = ∅ := by simp
  rw [this]
  simp

end Helpers

end GlobalTheory.RawLift.Eu

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSmoothDualNeZeroAtVector
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSmoothDualNeZeroAtVector
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Topology

namespace GlobalTheory.SmoothForm

theorem exists_smooth_form_ne_zero : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V), (∀ U ∈ 𝓝 (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U) → IsSmooth ρ → ∀ v : V, v ≠ 0 → ∃ l : Module.Dual ℂ V, l ∈ smoothPart ρ.dual ∧ l v ≠ 0 := by
  intro G V _ _ _ _ _ ρ hK hρ v hv
  obtain ⟨K, hKo, hKc, hKU⟩ := hK {g | ρ g v = v} ((hρ v).mem_nhds (by simp))
  have hfix : v ∈ fixed ρ K := GlobalTheory.IwahoriInj.mem_fixed.2 fun h hh => hKU hh
  have hnot : v ∉ twKer ρ K 1 := fun h => hv (GlobalTheory.IwahoriInj.eq_zero_of_fixed hρ hKc hfix h)
  have hq : (twKer ρ K 1).mkQ v ≠ 0 := by
    rwa [Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual ℂ (V ⧸ twKer ρ K 1), f ((twKer ρ K 1).mkQ v) ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hq ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 hc)
  refine ⟨f ∘ₗ (twKer ρ K 1).mkQ, ?_, hf⟩
  have hinv : ∀ g ∈ K, ρ.dual g (f ∘ₗ (twKer ρ K 1).mkQ) = f ∘ₗ (twKer ρ K 1).mkQ := by
    intro g hg
    refine LinearMap.ext fun x => ?_
    rw [Representation.dual_apply]
    show f ((twKer ρ K 1).mkQ (ρ g⁻¹ x)) = f ((twKer ρ K 1).mkQ x)
    congr 1
    exact (Submodule.Quotient.eq _).2 (GlobalTheory.IwahoriInj.sub_mem_twKer (inv_mem hg) x)
  exact GlobalTheory.SmGL.mem_smoothPart_of_nhds
    (Filter.mem_of_superset (hKo.mem_nhds K.one_mem) fun g hg => hinv g hg)

end GlobalTheory.SmoothForm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSmoothDualNeZeroAtVectorStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smoothDual_ne_zero_at_vector : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V), (∀ U ∈ 𝓝 (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U) → IsSmooth ρ → ∀ v : V, v ≠ 0 → ∃ l : Module.Dual ℂ V, l ∈ smoothPart ρ.dual ∧ l v ≠ 0 := by
  first | exact @GlobalTheory.SmoothForm.exists_smooth_form_ne_zero | exact GlobalTheory.SmoothForm.exists_smooth_form_ne_zero | (intros; apply GlobalTheory.SmoothForm.exists_smooth_form_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CountableDoubledHermitianLagrangians
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CountableDoubledHermitianLagrangians
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

namespace GlobalTheory.RawLift

theorem countable_numberField_type (K : Type) [Field K] [NumberField K] : Countable K := by
  let b := Module.finBasis ℚ K
  exact (b.equivFun.toEquiv.injective).countable

theorem lag_countable : ∀ (D : D7) (W : HSp D), Countable (Lag W) := by
  intro D W
  haveI : Countable D.host.E := countable_numberField_type D.host.E
  let M := (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)
  haveI : Countable (Submodule D.host.E M) := by
    have hs : Function.Surjective (fun s : Finset M => Submodule.span D.host.E (s : Set M)) := by
      intro N
      obtain ⟨s, hs⟩ := (IsNoetherian.noetherian N : N.FG)
      exact ⟨s, hs⟩
    exact hs.countable
  unfold Lag
  infer_instance

end GlobalTheory.RawLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CountableDoubledHermitianLagrangiansStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.countable_doubled_hermitian_lagrangians : ∀ (D : D7) (W : HSp D), Countable (Lag W) := by
  first | exact @GlobalTheory.RawLift.lag_countable | exact GlobalTheory.RawLift.lag_countable | (intros; apply GlobalTheory.RawLift.lag_countable <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SiegelWeilLagrangianTermStronglyMeasurable
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SiegelWeilLagrangianTermStronglyMeasurable
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

open scoped GlobalTheory.GaugeEx

namespace GlobalTheory.RallisMeas

variable {D : D7}

theorem borelSpace_WO (V W : HSp D) : BorelSpace (WO V W) := ⟨rfl⟩

theorem secondCountable_WO (V W : HSp D) : SecondCountableTopology (WO V W) :=
  inferInstanceAs (SecondCountableTopology (Fin W.rank → Fin V.rank → AE D))

theorem measurable_om_uncurry {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} {χV χW : (AE D)ˣ →* Circle}
    {om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} (hw : IsWeilDatumO ψ V W χV χW om)
    {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) :
    Measurable (fun q : GA D W × WO V W => om (1, q.1) f q.2) := by
  have := borelSpace_WO V W
  have := secondCountable_WO V W
  have h := measurable_uncurry_of_continuous_of_measurable (ι := GA D W) (α := WO V W) (β := ℂ)
    (u := fun g w => om (1, g) f w)
    (fun w => (hw.om_cont f hf w).comp (Continuous.prodMk continuous_const continuous_id))
    (fun g => (hw.om_pres (1, g) f hf).cont.measurable)
  exact h

theorem lagTerm_stronglyMeasurable : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), IsWeilDatumO ψ V W χV χW om → IsCovolOne (ratL W V) μ 𝓕 → ∀ (f₁ f₂ : WO V W → ℂ), IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → ∀ C : Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E, StronglyMeasurable (fun p : GA D W × GA D W => lagTerm μ 𝓕 C (om (1, p.1) f₁) (om (1, p.2) f₂)) := by
  intro D ψ V W χV χW om μ 𝓕 hw hμ f₁ f₂ hf₁ hf₂ C
  have := borelSpace_WO V W
  have := secondCountable_WO V W
  have hfin : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.2 (by rw [hμ.2.2]; simp)
  have hsf : SFinite (μ.restrict 𝓕) := @instSFiniteOfSigmaFinite _ _ _ (@IsFiniteMeasure.toSigmaFinite _ _ _ hfin)
  have c1 : Continuous (fun u : WO V W => ratMul C.1 u) := by unfold ratMul; fun_prop
  have c2 : Continuous (fun u : WO V W => ratMul C.2 u) := by unfold ratMul; fun_prop
  have m1 : Measurable (fun x : (GA D W × GA D W) × WO V W => om (1, x.1.1) f₁ (ratMul C.1 x.2)) :=
    (measurable_om_uncurry hw hf₁).comp (measurable_fst.fst.prodMk (c1.measurable.comp measurable_snd))
  have m2 : Measurable (fun x : (GA D W × GA D W) × WO V W => om (1, x.1.2) f₂ (ratMul C.2 x.2)) :=
    (measurable_om_uncurry hw hf₂).comp (measurable_fst.snd.prodMk (c2.measurable.comp measurable_snd))
  have hG : Measurable (fun x : (GA D W × GA D W) × WO V W =>
      om (1, x.1.1) f₁ (ratMul C.1 x.2) * star (om (1, x.1.2) f₂ (ratMul C.2 x.2))) :=
    m1.mul (continuous_star.measurable.comp m2)
  exact hG.stronglyMeasurable.integral_prod_right' (ν := μ.restrict 𝓕)

end GlobalTheory.RallisMeas

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SiegelWeilLagrangianTermStronglyMeasurableStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelWeil_lagrangian_term_stronglyMeasurable : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), IsWeilDatumO ψ V W χV χW om → IsCovolOne (ratL W V) μ 𝓕 → ∀ (f₁ f₂ : WO V W → ℂ), IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → ∀ C : Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E, StronglyMeasurable (fun p : GA D W × GA D W => lagTerm μ 𝓕 C (om (1, p.1) f₁) (om (1, p.2) f₂)) := by
  first | exact @GlobalTheory.RallisMeas.lagTerm_stronglyMeasurable | exact GlobalTheory.RallisMeas.lagTerm_stronglyMeasurable | (intros; apply GlobalTheory.RallisMeas.lagTerm_stronglyMeasurable <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DoubledLagrangianTermFrameIndependent
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DoubledLagrangianTermFrameIndependent
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open GlobalTheory.RawLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RawLift

variable {D : D7}

theorem ratMul_ratMul {m : ℕ} {a c : ℕ} (c₁ : Matrix (Fin a) (Fin m) D.host.E) (c₂ : Matrix (Fin m) (Fin m) D.host.E)
    (u : Mx D m c) : ratMul c₁ (ratMul c₂ u) = ratMul (c₁ * c₂) u := by
  unfold ratMul
  rw [Matrix.map_mul, Matrix.mul_assoc]

theorem covolOne_integral_ratMul {m n : ℕ} {μ : Measure (Mx D m n)} {𝓕 : Set (Mx D m n)}
    (hμ : IsCovolOne (GlobalTheory.MixModel.ratMx D m n) μ 𝓕) (c c' : Matrix (Fin m) (Fin m) D.host.E) (h1 : c' * c = 1)
    (h2 : c * c' = 1) (φ : Mx D m n → ℂ) (hφ : ∀ γ ∈ GlobalTheory.MixModel.ratMx D m n, ∀ a, φ (γ + a) = φ a) :
    ∫ a in 𝓕, φ (ratMul c a) ∂μ = ∫ a in 𝓕, φ a ∂μ := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.MixModel.lattice_Mx D m n
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  have hl : ∀ a : Mx D m n, ratMul c' (ratMul c a) = a := fun a => by
    rw [ratMul_ratMul, h1, ratMul_one]
  have hr : ∀ a : Mx D m n, ratMul c (ratMul c' a) = a := fun a => by
    rw [ratMul_ratMul, h2, ratMul_one]
  have mem : ∀ (d : Matrix (Fin m) (Fin m) D.host.E) (g : GlobalTheory.MixModel.ratMx D m n),
      ratMul d (g : Mx D m n) ∈ GlobalTheory.MixModel.ratMx D m n := fun d g =>
    GlobalTheory.MixModel.ratMx_mul (GlobalTheory.MixModel.rat_mem d) g.2
  let A : Mx D m n ≃+ Mx D m n :=
    { toFun := fun a => ratMul c a
      invFun := fun a => ratMul c' a
      left_inv := hl
      right_inv := hr
      map_add' := fun a b => Matrix.mul_add _ _ _ }
  let L : Mx D m n ≃ₜ+ Mx D m n :=
    { A with
      continuous_toFun := continuous_const.matrix_mul continuous_id
      continuous_invFun := continuous_const.matrix_mul continuous_id }
  let e : Mx D m n ≃ᵐ Mx D m n := L.toHomeomorph.toMeasurableEquiv
  haveI := hμ.1
  have hH : (μ.map e).IsAddHaarMeasure := L.isAddHaarMeasure_map μ
  have hmp : MeasurePreserving e μ (μ.map e) := e.measurable.measurePreserving μ
  let r : GlobalTheory.MixModel.ratMx D m n ≃ GlobalTheory.MixModel.ratMx D m n :=
    { toFun := fun g => ⟨ratMul c' (g : Mx D m n), mem c' g⟩
      invFun := fun g => ⟨ratMul c (g : Mx D m n), mem c g⟩
      left_inv := fun g => Subtype.ext (hr _)
      right_inv := fun g => Subtype.ext (hl _) }
  have hcov : IsCovolOne (GlobalTheory.MixModel.ratMx D m n) (μ.map e) (e '' 𝓕) := by
    refine ⟨hH, ?_, ?_⟩
    · refine hμ.2.1.image_of_equiv e.toEquiv (hmp.symm e).quasiMeasurePreserving r fun g a => ?_
      show ratMul c (ratMul c' (g : Mx D m n) + a) = (g : Mx D m n) + ratMul c a
      unfold ratMul
      rw [Matrix.mul_add]
      congr 1
      exact hr _
    · rw [e.map_apply, e.preimage_image]; exact hμ.2.2
  have h := GlobalTheory.MixModel.covolOne_integral_eq hμ hcov φ hφ
  rw [setIntegral_map_equiv, e.preimage_image] at h
  exact h

theorem exists_frame_change {W : HSp D} {Y : Lag W}
    {C C' : Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E}
    (hC : IsLagFrame W Y C) (hC' : IsLagFrame W Y C') :
    ∃ c c' : Matrix (Fin W.rank) (Fin W.rank) D.host.E,
      C'.1 = C.1 * c ∧ C'.2 = C.2 * c ∧ c * c' = 1 ∧ c' * c = 1 := by
  have mem : ∀ {C : Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E},
      IsLagFrame W Y C → ∀ j, ((fun a => C.1 a j), (fun a => C.2 a j)) ∈ Y.1 :=
    fun h j => h ▸ Submodule.subset_span ⟨j, rfl⟩
  let v : ∀ C, IsLagFrame W Y C → Fin W.rank → Y.1 := fun C h j => ⟨_, mem h j⟩
  have sp : ∀ C (h : IsLagFrame W Y C), ⊤ ≤ Submodule.span D.host.E (Set.range (v C h)) := by
    intro C h
    refine le_of_eq (Submodule.map_injective_of_injective Y.1.injective_subtype ?_).symm
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp]
    exact h
  have li : ∀ C (h : IsLagFrame W Y C), LinearIndependent D.host.E (v C h) := fun C h =>
    linearIndependent_of_top_le_span_of_card_eq_finrank (sp C h) (by rw [Fintype.card_fin, Y.2.1])
  let b := Module.Basis.mk (li C hC) (sp C hC)
  let b' := Module.Basis.mk (li C' hC') (sp C' hC')
  have hb : ∀ j, (b j : (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)) = ((fun a => C.1 a j), (fun a => C.2 a j)) :=
    fun j => by simp [b, v]
  have hb' : ∀ j, (b' j : (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)) = ((fun a => C'.1 a j), (fun a => C'.2 a j)) :=
    fun j => by simp [b', v]
  have key : ∀ j, (b' j : (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)) =
      ∑ i, b.toMatrix b' i j • (b i : (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)) := fun j => by
    have := congrArg Subtype.val (b.sum_repr (b' j))
    simp only [Submodule.coe_sum, Submodule.coe_smul] at this
    simp only [Module.Basis.toMatrix_apply]
    exact this.symm
  refine ⟨b.toMatrix b', b'.toMatrix b, ?_, ?_, Module.Basis.toMatrix_mul_toMatrix_flip b b', Module.Basis.toMatrix_mul_toMatrix_flip b' b⟩
  · refine Matrix.ext fun a j => ?_
    have := congrArg (fun y : (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E) => y.1 a) (key j)
    simp only [hb, hb', Prod.fst_sum, Prod.smul_fst, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [this, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  · refine Matrix.ext fun a j => ?_
    have := congrArg (fun y : (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E) => y.2 a) (key j)
    simp only [hb, hb', Prod.snd_sum, Prod.smul_snd, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [this, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem lagTerm_frame_indep : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), IsCovolOne (ratL W V) μ 𝓕 → IsStdChar D ψ (-1) → ∀ f₁ f₂, IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → ∀ (Y : Lag W) C C', IsLagFrame W Y C → IsLagFrame W Y C' → lagTerm μ 𝓕 C f₁ f₂ = lagTerm μ 𝓕 C' f₁ f₂ := by
  intro D ψ V W μ 𝓕 hμ hψ f₁ f₂ h₁ h₂ Y C C' hC hC'
  obtain ⟨c, c', e1, e2, hcc, hc'c⟩ := exists_frame_change hC hC'
  have hψ' : ∀ x, ‖ψ x‖ = 1 := hψ.1.2.1
  unfold lagTerm
  rw [e1, e2]
  simp only [← ratMul_ratMul]
  refine (covolOne_integral_ratMul (m := W.rank) (n := V.rank) hμ c c' hc'c hcc
    (fun u => f₁ (ratMul C.1 u) * star (f₂ (ratMul C.2 u))) ?_).symm
  rintro _ ⟨γ, rfl⟩ a
  exact GlobalTheory.RawLift.Model.integrand_periodic hψ' hC h₁ h₂ γ a

end GlobalTheory.RawLift

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DoubledLagrangianTermFrameIndependentStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open GlobalTheory.RawLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubled_lagrangian_term_frame_independent : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), IsCovolOne (ratL W V) μ 𝓕 → IsStdChar D ψ (-1) → ∀ f₁ f₂, IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → ∀ (Y : Lag W) C C', IsLagFrame W Y C → IsLagFrame W Y C' → lagTerm μ 𝓕 C f₁ f₂ = lagTerm μ 𝓕 C' f₁ f₂ := by
  first | exact @GlobalTheory.RawLift.lagTerm_frame_indep | exact GlobalTheory.RawLift.lagTerm_frame_indep | (intros; apply GlobalTheory.RawLift.lagTerm_frame_indep <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwoMulRankWLt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RawLift

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def realLev (R : RealDat D A Ks) (i : Fin D.R.m) : Set (GA D (Wc D i)) :=
  {h | ∃ u ∈ GinfC (Wc D i), ∃ k ∈ levW R i, h = u * k}

def lowCoefSq (R : RealDat D A Ks) (i : Fin D.R.m) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (h : GA D (Wc D i)) : ℝ :=
  ‖∏ ρ, ⟪((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ),
    (R.MW i (sg0 D A)).rep ρ (infMat D.sp.cm.sig (Wc D i).gram (R.θ ρ) h)
      ((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ)⟫_ℂ‖ ^ 2


variable (A) in
def dimProd (i : Fin D.R.m) : ℂ :=
  ∏ ρ, ((dimK _ _ (kapAt (Wc D i) (sg0 D A) ρ) : ℚ) : ℂ)

def rallisF (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (μ : Measure (WO (Vc D i) (Wc D i)))
    (𝓕 : Set (WO (Vc D i) (Wc D i))) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (f : WO (Vc D i) (Wc D i) → ℂ)
    (x y : (R.HW i (sg0 D A)).H) (g : GA D (Wc D i)) : ℂ :=
  thetaIP μ 𝓕 (R.ωP i t (1, g) f) f *
    ∫ z in R.fdW i, star (val R i v x z) * val R i v y (z * g) ∂(R.νW i)

theorem two_mul_rank_W_lt (D : D7) (i : Fin D.R.m) : 2 * (Wc D i).rank < (Vc D i).rank := by
  have h1 := i.2
  rw [D.sp.W_rank _ (by omega) (by omega), D.sp.V_rank _ (by omega) (by omega)]
  have := (D.R.rank_add_five_le : D.R.r + 5 ≤ D.R.t)
  unfold Ranks.nV
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  omega

end GlobalTheory.RawLift

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpehLanglandsQuotient
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpehLanglandsQuotient
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

noncomputable section

namespace GlobalTheory.LocGL

theorem IsLSeg.nu_rep {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {δ : IrrGL (k := k)} {Δ : Segment k} (h : IsLSeg Δ δ.rep) (c : ℂ) : IsLSeg (Δ.nu c) (δ.nu c).rep :=
  (h.tw (absPow k c) (isSmoothChar_absPow c)).of_equiv (δ.twEquiv _ _)

theorem IsSpeh.nu_rep {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {δ x : IrrGL (k := k)} {m : ℕ} (h : IsSpeh δ m x.rep) (s : ℂ) : IsSpeh (δ.nu s) m (x.nu s).rep := by
  obtain ⟨hd, h'⟩ := h.tw (absPow k s) (isSmoothChar_absPow s)
  exact ⟨hd, h'.of_equiv (x.twEquiv _ _) (.refl _)⟩

theorem isL_speh_nu (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hP : ∀ (δ δ' : IrrGL (k := k)) (Δ Δ' : Segment k), IsLSeg Δ δ.rep → IsUnitarisable δ.rep → IsLSeg Δ' δ'.rep →
      IsUnitarisable δ'.rep → ∀ x y : ℝ, (Δ.nu x).Precedes (Δ'.nu y) → x + 1 ≤ y) :
    ∀ (δ x : IrrGL (k := k)) (Δ : Segment k) (m : ℕ), IsLSeg Δ δ.rep → IsUnitarisable δ.rep → IsSpeh δ m x.rep →
      ∀ s : ℝ, IsL ↑(List.ofFn fun i : Fin m => Δ.nu ((s + ((m : ℝ) - 1) / 2 - (i : ℕ) : ℝ) : ℂ)) (x.nu (s : ℂ)).rep := by
  intro δ x Δ m hL hU hS s
  obtain ⟨hd, hc⟩ := hS.nu_rep (s : ℂ)
  set c : Fin m → ℝ := fun i => s + ((m : ℝ) - 1) / 2 - (i : ℕ) with hcdef
  have hy : ∀ i, spehFactor (δ.nu s) m i = δ.nu (c i : ℂ) := fun i => by
    simp only [spehFactor, IrrGL.nu_nu, hcdef]
    congr 1
    push_cast
    ring
  refine ⟨m, spehFactor (δ.nu s) m, hd, ⟨fun i => Δ.nu (c i : ℂ), ⟨?_, ?_⟩, ?_⟩, hc⟩
  · rw [Fin.univ_val_map]
  · intro i j hij hp
    have h1 := hP δ δ Δ Δ hL hU hL hU (c i) (c j) hp
    have h2 : ((i : ℕ) : ℝ) < (j : ℕ) := by exact_mod_cast hij
    simp only [hcdef] at h1
    linarith
  · intro i
    rw [hy i]
    exact hL.nu_rep _

end GlobalTheory.LocGL
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpehLanglandsQuotientStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.speh_langlands_quotient : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], (∀ (δ δ' : IrrGL (k := k)) (Δ Δ' : Segment k), IsLSeg Δ δ.rep → IsUnitarisable δ.rep → IsLSeg Δ' δ'.rep →
      IsUnitarisable δ'.rep → ∀ x y : ℝ, (Δ.nu x).Precedes (Δ'.nu y) → x + 1 ≤ y) →
    ∀ (δ x : IrrGL (k := k)) (Δ : Segment k) (m : ℕ), IsLSeg Δ δ.rep → IsUnitarisable δ.rep → IsSpeh δ m x.rep →
      ∀ s : ℝ, IsL ↑(List.ofFn fun i : Fin m => Δ.nu ((s + ((m : ℝ) - 1) / 2 - (i : ℕ) : ℝ) : ℂ)) (x.nu (s : ℂ)).rep := by
  first | exact @GlobalTheory.LocGL.isL_speh_nu | exact GlobalTheory.LocGL.isL_speh_nu | (intros; apply GlobalTheory.LocGL.isL_speh_nu <;> assumption)
end
end
