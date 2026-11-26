module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmJumpSetup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetPointGood
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TheoremBOfAdmittedHypotheses
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.MainFinal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TheoremTbOfLocalBlochKatoDualityEuler
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisRepUniqueBaseChange
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameDescentConditionsEveryLocalisationStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedPlaceSelmerLengthBoundOfLocalDuality
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLiftingTheoremAOfBlochKatoTateDualityEulerC
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLiftingTheoremAHypothesesAdmitted
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ElementDenominatorAdm7
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ElementDenominatorAdm7
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem elementDenominator_adm7 : ∀ D : D7, Formalism.MainNotions.ElementDenominator.adm7 D := by
  intro D l _ _ K LL _ T _
  haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  exact @GlobalTheory.T.h1f_generated_lattice l _ (D.loc l) (D.locA l) (D.locT l) K LL (Fintype.ofFinite _) T _

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ElementDenominatorAdm7Statement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adm7_elementDenominator : ∀ D : D7, Formalism.MainNotions.ElementDenominator.adm7 D := by
  first | exact @GlobalTheory.elementDenominator_adm7 | exact GlobalTheory.elementDenominator_adm7 | (intros; apply GlobalTheory.elementDenominator_adm7 <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLiftingTheoremAHypothesesAdmitted
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.AdmittedPartOne

theorem all_admitted : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK →
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
      ElementDenominator.Adm1 D HW F Cm 23 32 32 := by
  intro hBK hTD hEC D HW F Cm
  have hU := (GlobalTheory.T.wachModuleLocalConclusions_usedForms D HW F Cm).1
  have h54 := GlobalTheory.T.localConstants_from_admitted_local_Galois_statements hBK hTD hEC D HW F Cm
  have hA := (GlobalTheory.T.liftingTheorem_wachModuleLemma_hypotheses_admitted D HW F Cm).1
  refine ⟨hU.1, hU.2.2.1, GlobalTheory.T.restriction_corestriction_H1f D HW F, hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    GlobalTheory.AdmHerrLocal.main D HW F, hU.2.2.2, archimedean_signature_matching_of_liftingTheory D HW F 23 32 32 10 h54,
    lifting_input_five_of_lifting D HW F 10 23 32 32 h54, lifting_input_six_of_lifting D HW F 10 23 32 32 h54,
    GlobalTheory.T.adm7_elementDenominator D, GlobalTheory.Per.FontaineAdm.fontaine_bounds D, GlobalTheory.Per.StrictAdm.strict_adm D, GlobalTheory.T.crystalline_restrict_finite_extension_jumps D⟩

end GlobalTheory.AdmittedPartOne
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLiftingTheoremAHypothesesAdmittedStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localLifting_theoremA_hypotheses_admitted : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), ElementDenominator.Adm1 D HW F Cm 23 32 32 := by
  first | exact @GlobalTheory.AdmittedPartOne.all_admitted | exact GlobalTheory.AdmittedPartOne.all_admitted | (intros; apply GlobalTheory.AdmittedPartOne.all_admitted <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLiftingOfEtaleExactDeRhamCrystallineConst
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankIotaLetter
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.NL.IotaLetterRank

theorem finrank_iota_letter : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hG : Good K 1 LL) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsCrys ((D.loc l).PD K) T.ρ → ∀ c : ZMod (finrank ℚ_[l] ↥(K0 K)), finrank ↥LL.1 ↥(Formalism.MainNotions.DeltaInvariantLattices.ιDi ((HW l).W K 1 LL hG) T c) = finrank ↥LL.1 T.V := by
  intro D HW F Cm l _ K LL hG T hV c
  unfold Formalism.MainNotions.DeltaInvariantLattices.ιDi
  rw [← (Submodule.equivMapOfInjective _ (GlobalTheory.NL.PhiD.iota_injective _) _).finrank_eq]
  exact (GlobalTheory.Per.Components.components_finrank l (D.loc l) (D.locA l) (D.locT l) K LL T.V T.ρ).2 _ hV

end GlobalTheory.NL.IotaLetterRank
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankDdREOfIsCrys
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.CrysDdR

set_option synthInstance.maxHeartbeats 200000 in
theorem finrank_DdRE_of_isCrys : ∀ D : D7, ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l), (∃ s, Good K s LL) → ∀ T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL), IsCrys ((D.loc l).PD K) T.ρ → ∀ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, finrank ↥LL.1 ↥(DdRE ((D.loc l).PD K) T.ρ τ) = finrank ↥LL.1 T.V := by
  intro D l _ K LL _ T hc τ
  have hdr := (GlobalTheory.Per.CrisDR.isDR_of_isCrys l (D.loc l) (D.locA l) (D.locT l) K LL T.V T.ρ hc).1
  exact ((GlobalTheory.Per.Components.components_finrank l (D.loc l) (D.locA l) (D.locT l) K LL T.V T.ρ).1 τ).2.2 hdr

end GlobalTheory.CrysDdR
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLiftingOfEtaleExactDeRhamCrystallineConst
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.TheoremAFinal

theorem integralityFromMetric_of_le : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), ∀ CA CB CK C : ℝ, 160 ≤ C → ElementDenominator.IntegralityFromMetric D HW F Cm CA CB CK C := by
  intro D HW F Cm CA CB CK C hC
  exact Formalism.MainNotions.N.Ln34.integrality_from_metric_of_large_constant D HW F Cm CA CB CK C hC
    (fun l _ K s LL hG T₀ T₁ T₂ ι π h => GlobalTheory.LatExact.W_exact D HW F l K s LL hG T₀ T₁ T₂ ι π h)
    (GlobalTheory.CrysDdR.finrank_DdRE_of_isCrys D) (GlobalTheory.NL.IotaLetterRank.finrank_iota_letter D HW F Cm)

end GlobalTheory.TheoremAFinal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLiftingOfEtaleExactDeRhamCrystallineConstStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralityFromMetric_of_160_le : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), ∀ CA CB CK C : ℝ, 160 ≤ C → ElementDenominator.IntegralityFromMetric D HW F Cm CA CB CK C := by
  first | exact @GlobalTheory.TheoremAFinal.integralityFromMetric_of_le | exact GlobalTheory.TheoremAFinal.integralityFromMetric_of_le | (intros; apply GlobalTheory.TheoremAFinal.integralityFromMetric_of_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLiftingTheoremAOfBlochKatoTateDualityEulerC
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory

theorem theoremA_closing : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), ∀ C : ℝ, 160 ≤ C → ElementDenominator.Conclusion1 D C := by
  intro hBK hTD hEC D HW F Cm C hC
  exact GlobalTheory.T.integralityFromMetric_of_160_le D HW F Cm 23 32 32 C hC (GlobalTheory.T.localLifting_theoremA_hypotheses_admitted hBK hTD hEC D HW F Cm)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLiftingTheoremAOfBlochKatoTateDualityEulerCStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localLifting_of_blochKato_tateDuality_eulerChar : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), ∀ C : ℝ, 160 ≤ C → ElementDenominator.Conclusion1 D C := by
  first | exact @GlobalTheory.theoremA_closing | exact GlobalTheory.theoremA_closing | (intros; apply GlobalTheory.theoremA_closing <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoDimAtAuxiliaryPrimePlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoDimAtAuxiliaryPrimePlaces
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.InertiaEigenvalues.DimAtQD

theorem main : Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (i : D.nd.Loc),
    EmbeddingTypeJumps.AtQD i → ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw), Formalism.WeaklyAdmissibleFiltrations.BlochKatoDim (Br.PD D.loc D.nbr i w hw) ↥C.LL.1 :=
  fun _ _ D i _ w hw C =>
    by
      classical
      haveI := (D.nbr i w hw).Kw.2
      haveI := C.LL.2
      exact @GlobalTheory.BlochKatoTied.blochKatoDim_of_tied (D.nd.l i) _ (D.loc (D.nd.l i)) (D.locA (D.nd.l i)) (D.locT (D.nd.l i)) (D.nbr i w hw).Kw C.LL _

end GlobalTheory.InertiaEigenvalues.DimAtQD
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoDimAtAuxiliaryPrimePlacesStatement
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blochKatoDim_at_auxiliary_prime_places : Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (i : D.nd.Loc), EmbeddingTypeJumps.AtQD i → ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw), Formalism.WeaklyAdmissibleFiltrations.BlochKatoDim (Br.PD D.loc D.nbr i w hw) ↥C.LL.1 := by
  first | exact @GlobalTheory.InertiaEigenvalues.DimAtQD.main | exact GlobalTheory.InertiaEigenvalues.DimAtQD.main | (intros; apply GlobalTheory.InertiaEigenvalues.DimAtQD.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedPlaceSelmerLengthBoundOfLocalDuality
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.TwistedPlaceBound

theorem closing : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), ∀ (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (large₂ : SizeData₂ D) (ep : Bool) (C : ℝ) (Qp : MvPolynomial (Fin 3) ℕ), 2080 ≤ C → (∀ f r t : ℕ, 260 * f ^ 2 * t ^ 2 * (r + t) ≤ EmbeddingTypeJumps.polyVal Qp f r t) → EmbeddingTypeJumps.GlobalIndexAwayFromTypes r ρ → EmbeddingTypeJumps.admG1 r → EmbeddingTypeJumps.admG2 r ρ → EmbeddingTypeJumps.admG3 r ρ → EmbeddingTypeJumps.admG4 r → EmbeddingTypeJumps.admG5 r → EmbeddingTypeJumps.admG6 r → EmbeddingTypeJumps.iwahoriAdmissibleSet r ρ → EmbeddingTypeJumps.KillingTwistedPlaces ρ → EmbeddingTypeJumps.HodgeJumpWindowsAtDistinguishedPrimes r ep large₂ → EmbeddingTypeJumps.FontaineSubOfSumsAtDistinguishedPrimes r ρ → (∀ i : D.nd.Loc, EmbeddingTypeJumps.AtQD i → TruncatedSeriesCountingIdentities.TameGeneratorConditions i) → EmbeddingTypeJumps.ParametersPolynomiallyBounded large₂ → EmbeddingTypeJumps.Conclusion0 D ∧ EmbeddingTypeJumps.Conclusion1 D ∧ EmbeddingTypeJumps.Conclusion2 ρ large₂ C Qp := by
  intro hGAR hBKL hLTD hLEC D HW F Cm r ρ large₂ ep C Qp hC hQ hN5 hG1 hG2 hG3 hG4 hG5 hG6 hSet hKill hJump hFon hG5x hPar
  have hUsed := GlobalTheory.T.wachModuleLocalConclusions_usedForms D HW F Cm
  have hW : EmbeddingTypeJumps.admW (D := D) HW F := by
    intro i _ w hw Cf h
    exact GlobalTheory.T.wachHypothesis_crystallineLattices D HW F Cm hUsed.1 hUsed.2 (GlobalTheory.crysOnCond_all D HW F) (D.nd.l i) _ 1 Cf.LL h
  have hA : EmbeddingTypeJumps.admA (D := D) 160 := GlobalTheory.T.localLifting_of_blochKato_tateDuality_eulerChar hBKL hLTD hLEC D HW F Cm 160 le_rfl
  have hTB : EmbeddingTypeJumps.admTB (D := D) HW F := GlobalTheory.T.theorem_tb_of_local_blochKato_duality_euler hBKL hLTD hLEC D HW F Cm
  have hBK : EmbeddingTypeJumps.admBK (D := D) := GlobalTheory.T.blochKatoLocal_all_of_tateDuality_eulerChar hBKL hLTD hLEC D
  have hLit : EmbeddingTypeJumps.LiteratureHypotheses (D := D) := by
    intro i hi
    refine ⟨hG5x i hi, fun w hw Cf => ⟨?_, GlobalTheory.T.blochKatoDim_at_auxiliary_prime_places hLTD hLEC D i hi w hw Cf⟩,
      GlobalTheory.BridgeTie.localCoefficientCompatibility D i, GlobalTheory.FontaineAdm.fontaineProperties_all_places D i, GlobalTheory.T.integral_tate_H2_top hLTD D i,
      GlobalTheory.T.unramifiedClassFieldBound_of_artin hGAR D i⟩
    exact Formalism.MainNotions.TruncatedSeriesCountingIdentities.tate_duality_h2_of_all_coefficients _ _ _
      (GlobalTheory.TateTop.tateH2_of_duality_loc hLTD (D.nd.l i) (D.loc (D.nd.l i)) (D.nbr i w hw).Kw)
      (GlobalTheory.HTW.Rec.goodO_finExt_integers (D.nd.l i) Cf.LL)
  have h01 := GlobalTheory.T.local_fields_at_auxiliary_primes D
  refine ⟨h01.1, h01.2, ?_⟩
  exact GlobalTheory.T.theoremB_of_admittedHypotheses D HW F r ρ large₂ ep 160 C Qp (by rw [max_eq_left (by norm_num)]; linarith) hQ hW hA
    hN5 hG1 hG2 hG3 hG4 hG5 hG6 hSet hTB hBK hKill hJump hFon hLit hPar

end GlobalTheory.TwistedPlaceBound
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedPlaceSelmerLengthBoundOfLocalDualityStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedPlace_selmerLengthBound_of_localDuality : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), ∀ (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (large₂ : SizeData₂ D) (ep : Bool) (C : ℝ) (Qp : MvPolynomial (Fin 3) ℕ), 2080 ≤ C → (∀ f r t : ℕ, 260 * f ^ 2 * t ^ 2 * (r + t) ≤ EmbeddingTypeJumps.polyVal Qp f r t) → EmbeddingTypeJumps.GlobalIndexAwayFromTypes r ρ → EmbeddingTypeJumps.admG1 r → EmbeddingTypeJumps.admG2 r ρ → EmbeddingTypeJumps.admG3 r ρ → EmbeddingTypeJumps.admG4 r → EmbeddingTypeJumps.admG5 r → EmbeddingTypeJumps.admG6 r → EmbeddingTypeJumps.iwahoriAdmissibleSet r ρ → EmbeddingTypeJumps.KillingTwistedPlaces ρ → EmbeddingTypeJumps.HodgeJumpWindowsAtDistinguishedPrimes r ep large₂ → EmbeddingTypeJumps.FontaineSubOfSumsAtDistinguishedPrimes r ρ → (∀ i : D.nd.Loc, EmbeddingTypeJumps.AtQD i → TruncatedSeriesCountingIdentities.TameGeneratorConditions i) → EmbeddingTypeJumps.ParametersPolynomiallyBounded large₂ → EmbeddingTypeJumps.Conclusion0 D ∧ EmbeddingTypeJumps.Conclusion1 D ∧ EmbeddingTypeJumps.Conclusion2 ρ large₂ C Qp := by
  first | exact @GlobalTheory.TwistedPlaceBound.closing | exact GlobalTheory.TwistedPlaceBound.closing | (intros; apply GlobalTheory.TwistedPlaceBound.closing <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthBoundOfRowConditionsAndDualityTheorems
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthBoundOfRowConditionsAndDualityTheorems
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.InertiaEigenvalues.LengthBoundClosing

theorem stmt_closed : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ D : D7, Formalism.MainNotions.N.K.Rows.AllDesignConditions D → TruncatedSeriesCountingIdentities.Stmt D := by
  intro hA hB hT hE D h51
  exact ⟨GlobalTheory.T.integralityFromMetric_of_designConditionAll hA hB hT hE D h51, Formalism.MainNotions.TruncatedSeriesCountingIdentities.second_statement D⟩

end GlobalTheory.InertiaEigenvalues.LengthBoundClosing
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthBoundOfRowConditionsAndDualityTheoremsStatement
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lengthBound_of_rowConditions_and_dualityTheorems : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ D : D7, Formalism.MainNotions.N.K.Rows.AllDesignConditions D → TruncatedSeriesCountingIdentities.Stmt D := by
  first | exact @GlobalTheory.InertiaEigenvalues.LengthBoundClosing.stmt_closed | exact GlobalTheory.InertiaEigenvalues.LengthBoundClosing.stmt_closed | (intros; apply GlobalTheory.InertiaEigenvalues.LengthBoundClosing.stmt_closed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsBisLast
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.DesignUnconditional

theorem main : ∀ D : D7, GlobalTheory.CoefDuty.TakenAll D → Formalism.MainNotions.N.K.Rows.AllDesignConditions D :=
  GlobalTheory.T.designConditionAll_of_cheb_of_takenAll (GlobalTheory.Published.chebotarevDegreeOne_iff_cheb.mp GlobalTheory.Published.chebotarevDegreeOne')

end GlobalTheory.DesignUnconditional
end

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

noncomputable section

namespace GlobalTheory.TheoremBQD

open MvPolynomial

def polyB : MvPolynomial (Fin 3) ℕ := 260 * X 0 ^ 2 * X 2 ^ 2 * (X 1 + X 2)

theorem polyB_val (f r t : ℕ) : 260 * f ^ 2 * t ^ 2 * (r + t) ≤ EmbeddingTypeJumps.polyVal polyB f r t := by
  simp [EmbeddingTypeJumps.polyVal, polyB]

theorem exists_good {D : D7} {i : D.nd.Loc} (hi : EmbeddingTypeJumps.AtQD i) : ∃ π, π ∈ D.nd.Zgood i := by
  obtain ⟨π, hπ⟩ := hi.2
  exact ⟨π, (D.Zgood_tie i π).2 hπ⟩

end GlobalTheory.TheoremBQD

end
