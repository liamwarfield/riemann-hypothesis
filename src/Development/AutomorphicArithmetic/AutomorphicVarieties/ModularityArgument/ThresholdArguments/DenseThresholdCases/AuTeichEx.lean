module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutQN
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.CuspUnique
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.HeckeOperatorPreservesPart
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.DefQuatExists
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.NewformRepOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.AlgIso
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.NormCongruenceUnits.SeedII
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.NormCongruenceUnits.SeedIII
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.Imports
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.LinkEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.PfConst
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.AcClosed
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.CondDRoots
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.TraceOfCp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.H5
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.PsiInj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.RegOfTan
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.CocycleVanishesOnInertiaOfPointPseudodeformation
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidueFlagPoints.PowMemOpen
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AutomorphicCharacters.PsiCont
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CentralResidueGroups.CcEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AutomorphicDetection.PfromAut
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.CoefIsCoef
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.AutNew
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.CocycleCoefficients.PetAdj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HermitianTwists.EvPl
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.SymmetricAdjointFrobenius.AdAutQ
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.SymmetricAdjointFrobenius.QuadOf
public import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.HilbertEisensteinWeightOneHolds
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.InertiaPartMaps.CountE
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SafeUP

@[expose] public section

attribute [-instance] Formalism.LFunctionChainParameters.LChain6.FamC.indexKFirst Formalism.LFunctionChainParameters.LChain6.FamC.indexKSecond Formalism.LFunctionChainParameters.LChain6.FamC.indexKThird Formalism.LFunctionChainParameters.LChain6.FamC.indexKFourth Formalism.BasicNotions.NTypes.instMray Formalism.BasicNotions.NTypes.nfMray Formalism.BasicNotions.NTypes.algKM UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.isLocalHom UpperTheory.V.Pr.IsCD.fin

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AuTeichEx
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
private theorem au_teich_ex (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] [CharP (ResidueField O) l] :
    ∃ τ : ResidueField O →* O, ∀ x, residue O (τ x) = x := by
  haveI : CharP (O ⧸ maximalIdeal O) l := inferInstanceAs (CharP (ResidueField O) l)
  haveI : PerfectRing (ResidueField O) l := inferInstance
  let j : ResidueField O →+* Perfection (O ⧸ maximalIdeal O) l :=
    Perfection.lift l (ResidueField O) (O ⧸ maximalIdeal O) (RingHom.id (ResidueField O))
  have hj : ∀ x, Perfection.coeff (O ⧸ maximalIdeal O) l 0 (j x) = x := fun x => by
    have := (Perfection.lift l (ResidueField O) (O ⧸ maximalIdeal O)).symm_apply_apply (RingHom.id (ResidueField O))
    exact RingHom.congr_fun this x
  refine ⟨(Perfection.teichmuller l (maximalIdeal O)).comp j, fun x => ?_⟩
  exact (Perfection.mk_teichmuller (j x)).trans (hj x)
private theorem au_isTeich {l : ℕ} [hl : Fact l.Prime] {F : W.GFrame l} (c : Coef l) {n : ℕ} (r : Resid F c.O n) :
    ∃ t, r.IsTeich t := by
  obtain ⟨hc, hfin, hlm, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
  haveI : Finite (ResidueField c.O) := hfin
  haveI : CharP (ResidueField c.O) l := by
    refine (CharP.charP_iff_prime_eq_zero hl.out).2 ?_
    rw [← map_natCast (residue c.O), residue_eq_zero_iff]
    exact hlm
  obtain ⟨τ, hτ⟩ := au_teich_ex l c.O
  refine ⟨fun i => (Units.map τ).comp (r.chib i), fun i g => ⟨hτ _, ?_⟩⟩
  rw [MonoidHom.comp_apply, ← map_pow, ← Nat.card_units, pow_card_eq_one', map_one]
private theorem au_open {G O : Type} [Group G] [TopologicalSpace G] [CommRing O] {m : ℕ} (f : O →+* ℂ) (hf : Function.Injective f)
    (τ : G →* GL (Fin m) O) (h : IsOpen (((Matrix.GeneralLinearGroup.map f).comp τ).ker : Set G)) : IsOpen (τ.ker : Set G) := by
  have : ((Matrix.GeneralLinearGroup.map f).comp τ).ker = τ.ker := by
    refine MonoidHom.ker_comp_of_injective _ _ fun a b hab => ?_
    ext i j
    exact hf (congrArg (fun x : GL (Fin m) ℂ => (x : Matrix (Fin m) (Fin m) ℂ) i j) hab)
  rwa [this] at h
theorem UpperTheory.V.Hi.automorphicHeckeSet_unitaryPointProperties_of_typeFor :
    _root_.UpperTheory.V.Af.HypothesesH' → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ), ∀ (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O), _root_.UpperTheory.V.Hi.CaseU.TypeForAlt r ι τ₀ →
    (hset Q τ₀).AutomorphicHeckeSet ι (_root_.UpperTheory.V.Hi.CaseU.UnitaryPointProperties r ι) := by
  intro hP l _ L Ω _ _ _ _ _ _ s n hn V Q c r ι m τ₀ hτ lam _ d ξ hξ F hF hK hI
  obtain ⟨e, he⟩ := hξ
  obtain ⟨t, ht⟩ := au_isTeich c r
  have hop : IsOpen (τ₀.ker : Set (KT n (wt s))) :=
    au_open _ (ι.injective.comp Subtype.val_injective) τ₀ (hτ t ht).1
  have h1 := decompU l L Ω s n hn V Q c m τ₀ ι hop lam d e ξ he F hF hK hI
  refine SetLike.le_def.1 (iSup_le fun σ => ?_) h1
  by_cases h0 : YOf Q ι τ₀ e ξ σ.1 = ⊥
  · rw [h0]; exact bot_le
  · obtain ⟨Y, hY, hPU, -⟩ := _root_.UpperTheory.V.Z.Desc.P.partU_alt hP l L Ω s n hn V Q c r ι m τ₀ hτ lam d e ξ he σ.1 σ.2 h0
    rw [← hY]
    exact le_iSup (fun Y : {Y : (hset Q τ₀).PartAltAlt ι lam ξ // _root_.UpperTheory.V.Hi.CaseU.UnitaryPointProperties r ι lam Y.r} => Y.1.Y) ⟨Y, hPU⟩
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.CuspUnique
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SVRSol
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.FrobOfProps
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
open UpperTheory.Zero.LLC UpperTheory.V.Z.Win
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Af.ExLib
namespace UpperTheory.Gal.SV
theorem frob_of_props_alt (P : _root_.UpperTheory.V.Af.Hypotheses') {K Ω : Type} [Field K] [NumberField K] [IsCMField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    {l : ℕ} [Fact l.Prime] {n : ℕ} (hn : 1 ≤ n) {ι : Qbar l ≃+* ℂ} {R : G K Ω →* GL (Fin n) (Qbar l)} {π : CuspSub K n}
    {wt : ℤ} {HT : (K →+* Qbar l) → Multiset ℤ} (H : UpperTheory.GalStar.PropsB (fun h rc => IsRecT h rc) π ι R wt HT) (w : HeightOneSpectrum (𝓞 K))
    (hw : ((l : ℕ) : 𝓞 K) ∉ w.asIdeal) (B : Multiset ℂˣ) (hB : (CG.mk π).HasSat w B) : FrobEig ι R w (algSat n (normV w) B) := by
  obtain ⟨⟨σ, hσ⟩, hi⟩ := _root_.UpperTheory.V.Af.local_comp_complex_of_printed_results P K n π w
  have hS := ((_root_.UpperTheory.V.Af.satake_local_of_printed_results P K n w σ).2 _ π.finPart (hi σ hσ) B).1 hB
  refine frob_of hw σ hS fun A h rc hrc => ?_
  have g := gdOf K Ω A w h rc hrc n σ ((plainOf K n hn π w).2 ⟨_, hB⟩ σ hσ)
  rw [← (H.away w hw A h rc hrc σ hσ).tor g.1 g.2]
  exact isWDOf_wdOf (h := h) hw ι (Units.continuous_val.comp H.cont)
theorem exCS_of_prints :
    _root_.UpperTheory.V.Af.Hypotheses' → ExCS := by
  intro P K Ω _ _ _ _ _ _ l _ ι n hn π χ hreg hsign hd
  have hsign_pow : ∃ m : ℕ, ∀ v, χ.locInf v (-1) = (-1) ^ m := by
    obtain ⟨v₀⟩ : Nonempty (InfinitePlace (maximalRealSubfield K)) := inferInstance
    have hsq : ((χ.locInf v₀ (-1) : ℂˣ) : ℂ) ^ 2 = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← map_pow, neg_one_sq, map_one, Units.val_one]
    rcases sq_eq_one_iff.1 hsq with e | e
    · exact ⟨0, fun v => (hsign v v₀).trans (Units.ext (by simpa using e))⟩
    · exact ⟨1, fun v => (hsign v v₀).trans (Units.ext (by simpa using e))⟩
  obtain ⟨m, hm⟩ := hsign_pow
  have hN : compNorm K (χ * quadChar K ^ (m + n)) = compNorm K χ := by
    rw [map_mul, map_pow, compNorm_quadChar, one_pow, mul_one]
  have hpol : GlobalTheory.ContraPair.PolarizedPair π (χ * quadChar K ^ (m + n)) :=
    ⟨fun v => by
      change χ.locInf v (-1) * (quadChar K ^ (m + n)).locInf v (-1) = (-1) ^ n
      rw [locInf_pow, hm, quadChar_locInf, ← pow_add, ← add_assoc, pow_add, ← two_mul, pow_mul]
      simp, hN ▸ hd⟩
  obtain ⟨R, wt, HT, H⟩ := rowB (_root_.UpperTheory.Gal.SV.rowOf' P.litN.aut.gal) K Ω l ι n hn π _ hreg hpol
  have hsat : ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite, ∃ B, (CG.mk π).HasSat w B :=
    ExLib.eventually_sat (_root_.UpperTheory.V.Af.satake_local_of_printed_results P) π.finPart π.isSmooth_finPart fun w =>
      let ⟨⟨σ, hσ⟩, hi⟩ := _root_.UpperTheory.V.Af.local_comp_complex_of_printed_results P K n π w
      ⟨σ, hi σ hσ⟩
  refine ⟨_, R, wt, HT, hN, H, ⟨H.ss, (hsat.and (eventually_not_mem K l)).mono ?_⟩, fun r hr ha => ?_⟩
  · rintro w ⟨⟨B, hB⟩, hw⟩
    exact ⟨B, hB, _root_.UpperTheory.Gal.SV.frob_of_props_alt P hn H w hw B hB⟩
  · refine propsB_iso H ha.1
      (_root_.UpperTheory.V.Af.iso_of_frobenius_of_printed_results P K Ω l ι n R r H.cont hr H.ss ha.1 ((ha.2.and (eventually_not_mem K l)).mono ?_))
    rintro w ⟨⟨B, h1, h2⟩, hw⟩
    exact ⟨_, _root_.UpperTheory.Gal.SV.frob_of_props_alt P hn H w hw B h1, h2⟩
end UpperTheory.Gal.SV
end
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.NormCharacterOfFrobeniusCompatibility
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol
private theorem normV_under {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    (w : HeightOneSpectrum (𝓞 K')) : normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  simp only [normV, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 K') w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]
private theorem tendsto_under' {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K'] :
    Filter.Tendsto (fun w : HeightOneSpectrum (𝓞 K') => w.under (𝓞 K)) Filter.cofinite Filter.cofinite := by
  refine Filter.Tendsto.cofinite_of_finite_preimage_singleton fun v => ?_
  have h0 : Ideal.map (algebraMap (𝓞 K) (𝓞 K')) v.asIdeal ≠ 0 :=
    fun h => v.ne_bot ((Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)).1 h)
  refine (Ideal.finite_factors h0).subset fun w hw => ?_
  have e : w.under (𝓞 K) = v := hw
  show w.asIdeal ∣ _
  rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap, ← e]
  exact le_rfl
theorem UpperTheory.norm_character_of_printed_char_frobenius :
    _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Af.Sol.CharFrob → UpperTheory.V.Af.Sol.NormChar := by
  intro P hC K M Ω _ _ _ _ _ _ _ _ _ _ _ l _ ι η hη
  rcases hη with rfl | hN
  · exact ⟨1, rfl, Filter.Eventually.of_forall fun v => charEig_one ι v⟩
  obtain ⟨art, ha⟩ := P.litN.aut.art K Ω
  have hm : 0 < Module.finrank K M := Module.finrank_pos
  have hA : IsAlgPos η 0 := isAlgPos_zero_of_orderDvd (χ := η) hm hN.2.1
  obtain ⟨δ, hδc, hL⟩ := ha.exists_isLAdicOf ι hA
  have hE := hC K Ω l ι η δ ⟨hδc, art, 0, ha, hA, hL⟩
  refine ⟨δ, ?_, hE.mono fun v hv => hv.2⟩
  have hw : ∀ᶠ w : HeightOneSpectrum (𝓞 M) in Filter.cofinite, CharEig ι (δ.comp (res K Ω M)) w 1 := by
    filter_upwards [hN.2.2, (tendsto_under' (K := K) (K' := M)).eventually hE] with w h1 h2
    have hf := normV_under (K := K) w
    have h3 := (UpperTheory.frobenius_power_compatibility K M Ω l ι w _ hf).2 δ _ h2.2
    rwa [← Units.val_pow_eq_pow_val, h1 _ hf, Units.val_one] at h3
  have key := GlobalTheory.Published.ChebotarevDegreeOne.eq_of_frob (F := M) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne'
    (Filter.eventually_cofinite.1 hw) (f := fun s => δ (res K Ω M s)) (f' := fun _ => 1)
    (hδc.comp (continuous_restrictScalarsHom K M Ω)) continuous_const fun v hv _ A hA σ hσ => by
      have h := ((not_not.1 hv : CharEig _ _ _ _) A hA).2 σ hσ
      rw [map_eq_one_iff _ ι.injective, map_inv, Units.val_eq_one, inv_eq_one] at h
      exact h
  exact MonoidHom.ext fun s => congrFun key s
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc UpperTheory.V.Af.Sol
namespace UpperTheory.V.Z.Bc
theorem exDownC_sv_alt (H : _root_.UpperTheory.V.Af.HypothesesH') (cyc : CycC) : ExDownC := by
  have hA0 := _root_.UpperTheory.V.Af.algOfCyc_s H
  have hTo := UpperTheory.cyclotomicCharacter_plusPart hA0 UpperTheory.cyclotomic_char_conj_invariant
  have hDual := UpperTheory.dualBaseChange_of_frobeniusDuality_of_conjUnder UpperTheory.frobeniusDuality_complexConj UpperTheory.complexConj_place_under_eq
  have hNorm := _root_.UpperTheory.norm_character_of_printed_char_frobenius H.toClassicalTheorems UpperTheory.galois_character_frobenius_compatibility
  have hFin := UpperTheory.finiteCharacter_of_algebraic_cyclotomic hA0
  have hExt := UpperTheory.character_extends_to_galois_group
  have hEig := UpperTheory.hecke_eigenvalue_basic_properties
  have hSign := UpperTheory.sign_at_infinity_of_parallel_weight UpperTheory.adelicSolution_parallel
  intro K M Ω _ _ _ _ _ _ _ _ _ _ _ _ _ _ hp l _ ι n hn r π sat' inf' hpol hreg hc' hbc hatt
  haveI : IsAlgClosure (maximalRealSubfield K) Ω :=
    ⟨IsAlgClosure.isAlgClosed K, Algebra.IsAlgebraic.trans (maximalRealSubfield K) K Ω⟩
  obtain ⟨μ, χ, c, P, hμ, hs, hc, hP⟩ := hTo K Ω l ι n r hpol
  have huniq : ∀ w B B', sat' w B → sat' w B' → B = B' := by
    rcases hc' with ⟨_, Q, rfl, -⟩ | ⟨_, Q, rfl, -⟩
    · exact fun _ _ _ h h' => h.unique h'
    · exact fun _ _ _ h h' => TR.CuspSub.HasSat.unique h h'
  have hbc' := hDual K M Ω l ι n r π sat' huniq hbc hatt μ χ c P hμ hc hP
  obtain ⟨η, hη, hev⟩ := (cyc K M hp inferInstance n hn).2.2 _ _ sat' inf'
    (Or.inl ⟨inferInstance, π, rfl, rfl⟩) hc' hbc _ _ (Or.inl ⟨inferInstance, _, rfl, rfl⟩) hbc'
  obtain ⟨δ, hδ, hδe⟩ := hNorm K M Ω l ι η hη
  obtain ⟨δ', hδ', hδc, hδo⟩ := hExt K M Ω l δ hδ
  have hA := (_root_.UpperTheory.V.Af.algOfCyc_s H (maximalRealSubfield K) Ω l ι).2.1
  have h1 : IsAlgChar ι μ := ⟨χ, hμ⟩
  have h2 := hFin.1 _ Ω l ι δ' hδo
  obtain ⟨χ', hχ'⟩ := (hA _ _ h1 (hA _ _ h2 h2).2).1
  have hs' : SameSign (μ * δ'⁻¹) := fun a b ha hb => by
    rw [MonoidHom.mul_apply, MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.inv_apply, hδc a ha, hδc b hb, hs a b ha hb]
  have hd : GlobalTheory.ContraPair.DualIsConjBy π (compNorm K χ') := by
    refine UpperTheory.polOfSat_of_thetaSat UpperTheory.theta_satake_parameters_inverse H.litN.aut.js.1 H.litN.aut.gk K n hn π _ ?_
    have h3 := (conjSrc_injective (IsCMField.complexConj K).toRingEquiv).tendsto_cofinite.eventually hev
    filter_upwards [Bc.normGal K Ω l ι χ μ hμ, Bc.normGal K Ω l ι χ' _ hχ', hev, h3, hδe] with w ⟨hu, he⟩ ⟨hu', he'⟩
      ⟨_, B, hB, hB₁⟩ ⟨_, B', hB', _⟩ hw
    refine ⟨hu', B, B', hB, hB', ?_⟩
    have e1 : (μ * δ'⁻¹).comp (res (maximalRealSubfield K) Ω K) = μ.comp (res (maximalRealSubfield K) Ω K) * δ⁻¹ := by
      rw [← hδ']
      rfl
    rw [e1] at he'
    have e2 := (hEig K Ω l ι w).2.1 _ _ _ he' ((hEig K Ω l ι w).1 _ _ _ _ he hw)
    have e3 := hB₁.unique (GlobalTheory.SphGal.hasSatGL_twist K n _ (compNorm K χ) w _ hu (UpperTheory.theta_satake_parameters_inverse K n π w B' hB'))
    have e4 := congrArg (Multiset.map (· * ((compNorm K χ).val w)⁻¹)) e3
    simp only [Multiset.map_map, Function.comp_def, mul_inv_cancel_right] at e4
    rw [← e4, e2]
    refine Multiset.map_congr rfl fun a _ => ?_
    rw [mul_inv_rev, inv_inv, mul_assoc]
  obtain ⟨_, R, _, _, _, hR, hatt', -⟩ := _root_.UpperTheory.Gal.SV.exCS_of_prints H.toClassicalTheorems K Ω l ι n hn π χ' hreg (hSign _ Ω l ι χ' _ hχ' hs') hd
  exact ⟨R, hR.cont, hatt'⟩
end UpperTheory.V.Z.Bc
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc UpperTheory.V.Af.Sol
namespace UpperTheory.V.Z.Bc
private theorem cusp_unique {F : Type} [Field F] [NumberField F] {n : ℕ} {sat : HeightOneSpectrum (𝓞 F) → Multiset ℂˣ → Prop}
    {inf : (F →+* ℂ) → Multiset ℂ → Prop} (h : IsCusp n sat inf) : ∀ v B B', sat v B → sat v B' → B = B' := by
  rcases h with ⟨_, π, rfl, -⟩ | ⟨_, π, rfl, -⟩
  · exact fun _ _ _ h h' => h.unique h'
  · exact fun _ _ _ h h' => h.unique h'
private theorem not_both (F : Type) [Field F] [NumberField F] (h : IsTotallyReal F) (h' : IsTotallyComplex F) : False := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
  exact (InfinitePlace.not_isReal_iff_isComplex.2 (h'.isComplex v)) (h.isReal v)
theorem stepC_alt (H : _root_.UpperTheory.V.Af.HypothesesH') (cyc : CycC) : StepC := by
  intro K M Ω _ _ _ _ _ _ _ _ _ _ _ _ hp hK hM l _ ι n hn r hr hirr hpol
  obtain ⟨hup, hdown, -⟩ := cyc K M hp inferInstance n hn
  have hss : IsSSRep (r.comp (resG K M Ω)) := (Bc.irrBasic.1 _ Unit _ n _).2.1 hirr
  have hirr' : IsIrr r := (Bc.irrBasic.1 _ _ _ n r).1 _ hirr
  have hcont := continuous_restrictScalarsHom K M Ω
  constructor
  · rintro ⟨sat, inf, hc, hreg, hatt⟩
    rcases hup sat inf hc hreg with ⟨η, hη, ht⟩ | ⟨sat', inf', hc', hbc, hinf⟩
    · obtain ⟨δ, h1, -, h2, h3⟩ := _root_.UpperTheory.V.Sd.self_twist_galois_of_printed_results H.toClassicalTheorems K Ω l ι n r sat (cusp_unique hc) hr hatt η _ hp.pos hη.2.1 hη.1 ht
      exact (h1 (UpperTheory.schur_twist_holds _ _ _ n r (resG K M Ω) δ hirr (h3 M hη) h2)).elim
    · refine ⟨sat', inf', hc', fun τ => ?_, UpperTheory.satake_base_change_attached K M Ω l ι n r sat sat' (cusp_unique hc) hbc hatt hss⟩
      obtain ⟨m, hm, h⟩ := hreg (τ.comp (algebraMap K M))
      exact ⟨m, hinf τ m hm, h⟩
  · rintro ⟨sat', inf', hc', hreg', hatt'⟩
    obtain ⟨sat, inf, hc, hbc, hinf⟩ := hdown sat' inf' hc' hreg' (UpperTheory.satake_invariant_of_frobConj_of_eigenvalue_basic UpperTheory.frobenius_conj_of_galois_conjugate_places UpperTheory.hecke_eigenvalue_basic_properties K M Ω l ι n r sat' hatt')
    have hreg : RegInf n inf := fun τ => by
      obtain ⟨m, hm, h⟩ := hreg' (ComplexEmbedding.lift M τ)
      have := hinf _ m hm
      rw [ComplexEmbedding.lift_comp_algebraMap] at this
      exact ⟨m, this, h⟩
    obtain ⟨r₁, hr₁, hatt₁⟩ := (show ∃ r₁ : G K Ω →* GL (Fin n) (Qbar l), Continuous r₁ ∧ AttachedSys ι r₁ sat by
      rcases hc with ⟨hC, π, rfl, rfl⟩ | ⟨hR, -⟩
      · refine _root_.UpperTheory.V.Z.Bc.exDownC_sv_alt H cyc K M Ω hp l ι n hn r π sat' inf' hpol ((GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => ?_) hc' hbc hatt'
        obtain ⟨m, hm, h⟩ := hreg τ
        rw [CG.HasInfChar.infChar_eq (π := CG.mk π) hm]
        exact h
      · exact (not_both K hR inferInstance).elim)
    have hN := (UpperTheory.galois_representation_image_spec K M Ω).1
    have hss₁ := UpperTheory.semisimpleModule_restriction_to_normal_subgroup _ _ _ n r₁ (resG K M Ω) hN hatt₁.1
    have hatt₁' := UpperTheory.satake_base_change_attached K M Ω l ι n r₁ sat sat' (cusp_unique hc) hbc hatt₁ hss₁
    have hiso : RepIso (r₁.comp (resG K M Ω)) (r.comp (resG K M Ω)) := by
      refine _root_.UpperTheory.V.Af.iso_of_frobenius_of_printed_results H.toClassicalTheorems M Ω l ι n _ _ (hr₁.comp hcont) (hr.comp hcont) hss₁ hss ?_
      filter_upwards [hatt₁'.2, hatt'.2] with w ⟨B, hB, h⟩ ⟨B', hB', h'⟩
      obtain rfl := cusp_unique hc' w B B' hB hB'
      exact ⟨_, h, h'⟩
    obtain ⟨δ, hδ, hiso'⟩ := UpperTheory.schur_extension _ _ _ n r r₁ (resG K M Ω) hN hirr hiso
    have hF := UpperTheory.finiteCharacter_of_algebraic_cyclotomic (_root_.UpperTheory.V.Af.algOfCyc_s H)
    obtain ⟨sat₂, inf₂, hc₂, hreg₂, hatt₂⟩ := _root_.UpperTheory.V.Af.twist_invariance_automorphic H K Ω l ι n r₁ δ ⟨sat, inf, hc, hreg, hatt₁⟩
      (hF.1 K Ω l ι δ (hF.2 K M Ω l δ hδ))
    exact ⟨sat₂, inf₂, hc₂, hreg₂, (Bc.irrBasic.1 _ Unit _ n _).2.1 hirr',
      hatt₂.2.mono fun w ⟨B, hB, h⟩ => ⟨B, hB, h.of_iso hiso'⟩⟩
theorem solC_alt (H : _root_.UpperTheory.V.Af.HypothesesH') (cyc : CycC) : SolE := solC_of_stepC (_root_.UpperTheory.V.Z.Bc.stepC_alt H cyc)
end UpperTheory.V.Z.Bc
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LevelAdmissibleRestrictionHolds
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Aut UpperTheory.V.Pr
open UpperTheory.GalN.V
theorem UpperTheory.V.Z.Win.A4.admissible_restriction_level_n_of_printed_results : _root_.UpperTheory.V.Af.Hypotheses' → _root_.UpperTheory.GalN.V.AdmResNAlt := by
  intro hP K _ _ _ hK n hn m wt hm M hM l _ hl Ω _ _ _ _ _ _ ι r hr hirr
  have hC := Lev.LevelF.of_level hr.level
  have hF := Lev.levelFRes ℚ K Ω l n M m r hC
  obtain ⟨⟨P, hreg, hA⟩, hW⟩ := hr.aut hC.cont K hK hirr
  obtain ⟨θ, hθ, hd⟩ := hr.dual
  obtain ⟨χ, μ, hpol, -, -⟩ := _root_.UpperTheory.V.Z.Bc.polarization_k_of_printed_results hP K hK n (by omega) l Ω ι r wt θ P hθ hd hA
  exact ⟨hirr, ⟨P, hreg, ⟨χ, hpol⟩, hA⟩, hW, hF, _root_.UpperTheory.V.Z.Win.A4.safeRes' K (_root_.UpperTheory.V.Z.Win.A4.safeUP'_alt hP hr.irr hr.level hr.aut hr.safe)⟩
end
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TCoreSep
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
private theorem coreSep_coord {A M N κ : Type} [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module ℂ N]
    (Y : Submodule A M) (φ : A →+* ℂ) (sp : M → N) (hadd : ∀ f ∈ Y, ∀ f' ∈ Y, sp (f + f') = sp f + sp f')
    (hsmul : ∀ f ∈ Y, ∀ b : A, sp (b • f) = φ b • sp f) (b : Module.Basis κ A Y)
    (hind : LinearIndependent ℂ fun i => sp (b i)) (g : Y) (hg : sp g = 0) (i : κ) : φ (b.repr g i) = 0 := by
  classical
  let s : Y →ₛₗ[φ] N :=
    { toFun := fun f => sp f
      map_add' := fun f f' => hadd _ f.2 _ f'.2
      map_smul' := fun r f => hsmul _ f.2 r }
  have h1 : s g = ∑ j ∈ (b.repr g).support, φ (b.repr g j) • sp (b j) := by
    set_option synthInstance.maxHeartbeats 100000 in
      conv_lhs => rw [← b.linearCombination_repr g, Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
    exact Finset.sum_congr rfl fun j _ => s.map_smulₛₗ _ _
  by_cases hi : i ∈ (b.repr g).support
  · exact linearIndependent_iff'.1 hind _ (fun j => φ (b.repr g j)) (h1.symm.trans hg) i hi
  · rw [Finsupp.notMem_support_iff.1 hi, map_zero]
private theorem coreSep_kill {N J : Type*} [AddCommGroup N] [Module ℂ N] (E : Submodule ℂ N) (Y : J → Submodule ℂ N)
    (hE : E = ⨆ j, Y j ⊓ E) (T : Module.End ℂ E) (h : ∀ j, ∀ F : E, (F : N) ∈ Y j → T F = 0) (F : E) : T F = 0 := by
  have hle : E ≤ (LinearMap.ker T).map E.subtype := by
    conv_lhs => rw [hE]
    exact iSup_le fun j G hG => ⟨⟨G, hG.2⟩, h j ⟨G, hG.2⟩ hG.1, rfl⟩
  obtain ⟨G, hG, hGF⟩ := hle F.2
  have : G = F := Subtype.ext hGF
  exact this ▸ hG
theorem UpperTheory.V.Hi.eq_zero_of_vanish_at_good_points_dense_weight :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c), H.Ax →
    ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (ι : Qbar l ≃+* ℂ) (P : Wt L l n → (H.Gq →* GL (Fin n) (Qbar l)) → Prop), H.AutomorphicHeckeSet ι P →
    ∀ (a : H.Op → c.O) (K : H.Lev) [Fact (CommOn (H.MK θ a K) (H.op A))], ∀ lam ∈ H.admitted, H.DenseWt θ lam → ∀ t : H.TK θ a K, (∀ x : H.TK θ a K →ₐ[c.O] Qbar l, H.Good θ (x.toRingHom.comp (algebraMap A _)) lam → x t = 0) → t = 0 := by
  intro hLit L Ω _ _ _ _ _ l _ n c H hAx A _ _ _ θ hθ ι P hP a K _ lam hlam hD t ht
  obtain ⟨-, -, hfree, -⟩ := hiComm L Ω l n c H hAx A θ hθ K
  let b := Module.Free.chooseBasis A (H.X.Ord (H.τA A) θ (H.lev K))
  refine Subtype.ext (LinearMap.ext fun f => ?_)
  let g : H.X.Ord (H.τA A) θ (H.lev K) :=
    ⟨((t : Module.End A (H.MK θ a K)) f : H.MK θ a K), ((t : Module.End A (H.MK θ a K)) f).2.1⟩
  have hg : g = 0 := by
    refine b.repr.injective (Finsupp.ext fun i => ?_)
    rw [map_zero, Finsupp.zero_apply]
    refine hD _ fun x hx => ?_
    obtain ⟨d, ξ, c0, sp, hsp⟩ := spec L Ω l n c H hAx A θ hθ ι x lam hx.2.1
    obtain ⟨h1, act, h2, -, -, -, h3⟩ := _root_.UpperTheory.V.Hi.partAct0_alt hLit L Ω l n c H hAx A θ hθ ι P hP x lam d ξ c0 sp hsp hlam a K _ rfl
    have hE := h1.resolve_right (not_not.2 hx)
    have h0 := coreSep_kill _ _ hE (act t) (fun Y F hF => by
      by_cases hb : Y.1.Y ⊓ Submodule.span ℂ (sp '' H.MK θ a K) = ⊥
      · have : F = 0 := Subtype.ext ((Submodule.eq_bot_iff _).1 hb _ ⟨hF, F.2⟩)
        rw [this, map_zero]
      · obtain ⟨y, hy, hact⟩ := h3 hx Y.1 hb
        rw [hact t F hF, ht y (hy ▸ hx), map_zero, zero_smul])
      ⟨sp f, Submodule.subset_span ⟨f, f.2, rfl⟩⟩
    have h4 := h2 t f ⟨sp f, Submodule.subset_span ⟨f, f.2, rfl⟩⟩ rfl
    rw [h0] at h4
    have h5 := coreSep_coord _ (ι.toRingHom.comp x.toRingHom) sp (hsp.add K) (hsp.smul K) b (hsp.indep K _ b) g h4.symm i
    exact ι.injective (h5.trans (map_zero ι).symm)
  exact Subtype.ext (congrArg (fun z : H.X.Ord (H.τA A) θ (H.lev K) => (z : H.X.Fn A H.m)) hg)
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ClassicalFixedByIwahori
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws
private theorem UpperTheory.V.Ws.ch_num {x y : WithBot ℕ∞} {a b c N : ℕ} (h1 : x ≤ y + (a : ℕ)) (h2 : y + (b : ℕ) ≤ (c : ℕ))
    (h : c + a < N + b) : x < N := by
  refine h1.trans_lt ?_
  induction y using WithBot.recBotCoe with
  | bot => simp
  | coe y =>
    induction y using ENat.recTopCoe with
    | top => exact absurd h2 (by norm_cast)
    | coe y =>
      have h3 : y + b ≤ c := by exact_mod_cast h2
      exact_mod_cast (by omega : y + a < N)
private theorem UpperTheory.V.Ws.ch_core {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ] {Φ : Fr O Γ} {l : ℕ} [Fact l.Prime] {Λ : Type} [CommRing Λ] [IsDomain Λ]
    [IsDiscreteValuationRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] [Finite (ResidueField Λ)] {a : O →+* Λ} (hS : Φ.Std l a)
    (X : Space Φ a) (J : Ideal X.B) (U : Φ.ι → Set Γ) (hU : ∀ v, ∀ s ∈ U v, s ∈ Φ.Gv v) {d C dv N : ℕ}
    (hB : Φ.Bounds ((residue Λ).comp a) d C) (hN1 : d + 20 * C + 1 < N)
    (hN2 : 2 * d + 1 + (2 + 4 * Nat.card Φ.ι) < N + dv)
    (hnn : ∀ v i j, i ≠ j → ∀ q : Ideal X.B, q.IsPrime → J ≤ q → (maximalIdeal Λ).map (algebraMap Λ X.B) ≤ q →
      (∀ s ∈ U v, X.ψ v i s - X.ψ v j s ∈ q) → ringKrullDim (X.B ⧸ q) + dv ≤ (2 * d + 1 : ℕ))
    (hp1 : ∀ (k : Type) [Field k] [Finite k] [Algebra Λ k] (y : X.A →ₐ[Λ] PowerSeries k),
      (∀ b ∈ maximalIdeal X.B, PowerSeries.constantCoeff (y (algebraMap X.B X.A b)) = 0) →
      (∀ b ∈ J, y (algebraMap X.B X.A b) = 0) →
      (∀ v i j, i ≠ j → ∃ s ∈ U v, y (X.P.ψ v i s) ≠ y (X.P.ψ v j s)) →
      Irr (mapRep ((algebraMap (PowerSeries k) (FractionRing (PowerSeries k))).comp (y : X.A →+* PowerSeries k)) X.P.r) →
      X.LocZero J (y : X.A →+* PowerSeries k))
    {c : PD Φ.ι Γ (ResidueField Λ)} (hc : Φ.IsRes ((residue Λ).comp a) c) (hg : Φ.Good ((residue Λ).comp a) c)
    {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] (f : X.A →ₐ[Λ] R) (hdef : Φ.IsDef a c (X.P.map (f : X.A →+* R)))
    {P Q : Ideal R} (hPQ : Ch.Adj R (N + 1) P Q) (hP : J ≤ P.comap ((f : X.A →+* R).comp (algebraMap X.B X.A))) :
    J ≤ Q.comap ((f : X.A →+* R).comp (algebraMap X.B X.A)) := by
  classical
  haveI := hS.char
  let φ : X.B →+* R := (f : X.A →+* R).comp (algebraMap X.B X.A)
  have hφ : ∀ t : Λ, φ (algebraMap Λ X.B t) = algebraMap Λ R t := fun t => by
    show f (algebraMap X.B X.A _) = _
    rw [← IsScalarTower.algebraMap_apply, AlgHom.commutes]
  obtain ⟨ϖ, hϖ⟩ := (IsPrincipalIdealRing.principal (maximalIdeal Λ)).1
  have hm : ∀ q : Ideal R, algebraMap Λ R ϖ ∈ q → ∀ t ∈ maximalIdeal Λ, algebraMap Λ R t ∈ q := fun q hq t ht => by
    rw [hϖ] at ht
    obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.1 ht
    rw [map_mul]
    exact q.mul_mem_left _ hq
  have hϖm : algebraMap Λ R ϖ ∈ maximalIdeal R :=
    map_nonunit _ _ (show ϖ ∈ maximalIdeal Λ by rw [hϖ]; exact Ideal.mem_span_singleton_self ϖ)
  let A : {S // S ∈ redTypes} → Ideal R := fun S => redIdeal S.1 (X.P.map (f : X.A →+* R)).r
  let B : {t : Φ.ι × Fin 4 × Fin 4 // t.2.1 ≠ t.2.2} → Ideal R := fun t =>
    J.map φ ⊔ Ideal.span {algebraMap Λ R ϖ} ⊔ Ideal.span ((fun s => φ (X.ψ t.1.1 t.1.2.1 s - X.ψ t.1.1 t.1.2.2 s)) '' U t.1.1)
  haveI : Finite {S // S ∈ redTypes} := (List.finite_toSet redTypes).to_subtype
  obtain ⟨p, hp, hIp, hdim, hϖp, hA, hBp⟩ := Ch.nice _ hϖm N (by omega) A B
    (fun S => (red Φ l a hS d C hB c hc hg R _ hdef S.1 S.2).trans_lt (by exact_mod_cast hN1))
    (fun t q hq hle hr => ch_num
      (fib Φ l a hS X c hc R f hdef q (Ch.irr hS.ok hc hdef.1
        ((algebraMap (R ⧸ q) (FractionRing (R ⧸ q))).comp (Ideal.Quotient.mk q)) q
        (fun x hx => Ideal.Quotient.eq_zero_iff_mem.1 ((map_eq_zero_iff _ (IsFractionRing.injective _ _)).1 hx))
        fun S hS => hr ⟨S, hS⟩))
      (hnn t.1.1 _ _ t.2 (q.comap φ) (Ideal.comap_isPrime _ _)
        (Ideal.map_le_iff_le_comap.1 (le_sup_left.trans (le_sup_left.trans hle)))
        (Ideal.map_le_iff_le_comap.2 fun u hu => by
          show φ (algebraMap Λ X.B u) ∈ q
          rw [hφ]
          exact hm q (hle (Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))) u hu)
        fun s hs => hle (Ideal.mem_sup_right (Ideal.subset_span ⟨s, hs, rfl⟩))) hN2) _ hPQ.2.2
  obtain ⟨K, _, _, _, j, hj, hj0⟩ := Ch.curve l Λ R p hp hdim (hm p hϖp)
  have hJp : ∀ b ∈ J, φ b ∈ p := fun b hb => hIp (Ideal.mem_sup_left (hP hb))
  haveI : Q.IsPrime := hPQ.2.1.1.1
  refine hp1 K (j.comp f) (fun b hb => hj0 _ ?_) (fun b hb => (hj _).2 (hJp b hb)) (fun v i i' hi => ?_)
    (Ch.irr hS.ok hc hdef.1 ((algebraMap (PowerSeries K) (FractionRing (PowerSeries K))).comp (j : R →+* PowerSeries K)) p
      (fun x hx => (hj x).1 ((map_eq_zero_iff _ (IsFractionRing.injective _ _)).1 hx)) fun S hS => hA ⟨S, hS⟩)
    _ (Ideal.comap_isPrime _ _) fun s hs => (hj _).2 (hIp (Ideal.mem_sup_right hs))
  · show (f.comp (IsScalarTower.toAlgHom Λ X.B X.A)) b ∈ maximalIdeal R
    rw [← res_eq_zero_iff Λ, res_map, res_eq_zero_iff]
    exact hb
  · by_contra hn
    push Not at hn
    refine hBp ⟨(v, i, i'), hi⟩ (sup_le (sup_le (Ideal.map_le_iff_le_comap.2 hJp)
      ((Ideal.span_singleton_le_iff_mem _).2 hϖp)) (Ideal.span_le.2 ?_))
    rintro _ ⟨s, hs, rfl⟩
    refine (hj _).1 ?_
    show (j.comp f) (algebraMap X.B X.A (X.ψ v i s - X.ψ v i' s)) = 0
    rw [map_sub, map_sub, X.ψ_map v i s (hU v s hs), X.ψ_map v i' s (hU v s hs), hn s hs, sub_self]
theorem UpperTheory.V.Ws.residual_charpoly_rank_four :
    CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → T.Deep → ∀ (ι : PadicAlgCl l ≃+* ℂ) (c' : Coef l) (h : c.O ≤ c'.O) (X : Space (T.fr ∅) (inc h)) (J : Ideal X.B), T.PotentialModularityTower ι X J → ∀ C : ℕ, (T.fr ∅).Bounds ((residue c'.O).comp (inc h)) T.d C → 30 * (C + 1) * (C + 1) ≤ T.d →
      ∀ x : X.A →ₐ[c'.O] ResidueField c'.O, (T.fr ∅).IsRes ((residue c'.O).comp (inc h)) (X.P.map (x : X.A →+* _)) → (T.fr ∅).Good ((residue c'.O).comp (inc h)) (X.P.map (x : X.A →+* _)) →
      X.SomeIn J (RingHom.ker x) → X.AllIn J (RingHom.ker x) := by
  intro hC Ω _ _ _ l _ c D T hF hD ι c' h X J hPM C hB hd x hx hg ⟨q₀, hq₀, hq₀x, hq₀J⟩ q hq hqx
  haveI : Finite (ResidueField c'.O) := (UpperTheory.V.abelian₂.dvr_finite l c'.O).2.1
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : IsAlgClosure T.F Ω := ⟨inferInstance, inferInstance⟩
  haveI : IsGalois T.F Ω := {}
  haveI : CompactSpace (G T.F Ω) := inferInstanceAs (CompactSpace (Ω ≃ₐ[T.F] Ω))
  haveI : TotallyDisconnectedSpace (G T.F Ω) := inferInstanceAs (TotallyDisconnectedSpace (Ω ≃ₐ[T.F] Ω))
  have hS := (std hC D T hF ∅ c' h).1 (Finset.notMem_empty 0)
  obtain ⟨R, _, _, _, f, hdef, hfl, hres⟩ := cmplEx (T.fr ∅) l (inc h) hS X x hx
  obtain ⟨a, b, π, e, hπ, hk, hab⟩ := x1 hC D T hF hD c' h _ hx R _ hdef
  obtain ⟨dv, hdv⟩ := chDv D T
  have hg' : Nat.card T.ι ≤ C := hB.card
  have hdv' : 30 * (C + 1) ≤ dv := by
    by_contra hn
    have h1 : dv * Nat.card T.ι ≤ 30 * (C + 1) * C := Nat.mul_le_mul (by omega) hg'
    nlinarith
  have hd' : 30 * (C + 1) ≤ T.d := le_trans (Nat.le_mul_of_pos_right _ (by omega)) hd
  obtain ⟨N, hN⟩ : ∃ N, N + 2 * Nat.card T.ι = 2 * T.d + 1 := ⟨2 * T.d + 1 - 2 * Nat.card T.ι, by omega⟩
  have hker : RingHom.ker x = (maximalIdeal R).comap (f : X.A →+* R) := by
    ext z
    rw [RingHom.mem_ker, ← hres]
    exact res_eq_zero_iff c'.O R (f z)
  obtain ⟨P, hP, rfl⟩ := Ch.flat_min _ hfl hq₀ (hker ▸ hq₀x)
  obtain ⟨Q, hQ, rfl⟩ := Ch.flat_min _ hfl hq (hker ▸ hqx)
  rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap] at hq₀J ⊢
  have hch := Ch.chain c'.O (D := N + 1) π e hπ hk (by omega) hP hQ
  clear hq hqx hQ
  induction hch with
  | refl => exact hq₀J
  | tail _ hPQ ih =>
    exact ch_core hS X J T.U1 (fun v s hs => Ine_le_Dec _ hs.1) (dv := dv) hB (by omega)
      (by show _ + (2 + 4 * Nat.card T.ι) < _; omega)
      (fun v i j hij q h1 h2 h3 h4 => _root_.UpperTheory.V.Ws.off_diagonal_nilpotent_rank_four hC D T hF hD ι c' h X J hPM v i j hij q h1 h2 h3 h4 dv hdv) hPM.p1 hx hg f hdef hPQ ih
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.CohInp
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphyU3OfEndoscopy
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LevelZeroEqMaximalCompactAlt
noncomputable abbrev UpperTheory.V.Z.Win.WitAQ.weak_admissible_iso := @UpperTheory.GalN.V.WitQ.weak_admissible_iso
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.GalN.V hiding autCsd_iso
open NumberField IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Aut UpperTheory.V.Pr UpperTheory.V
theorem UpperTheory.GalN.V.modOfEnd'_alt {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
    {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) {g₁ : G ℚ Ω}
    {B : ValuationSubring Ω} {ι : Qbar l ≃+* ℂ} (h : _root_.UpperTheory.V.Z.Win.Dn.AutEnd2A c D.η D.Ψ D.cc g₁ B e ι)
    (A : Subalgebra c.O (PadicAlgCl l)) [IsDiscreteValuationRing A] [Module.Finite c.O A] (r : G ℚ Ω →* GG (m := 3) (R := A))
    (h1 : OrdPt l D.η D.Ψ D.cc g₁ B r) (h2 : TypeII D.η (UnitaryThreeInertia.push A.val r)) (h3 : ∀ g ∈ D.η.ker, (r g).mat 1 1 = 1)
    (W' : G ℚ Ω →* GL (Fin 2) (PadicAlgCl l)) (h4 : ∀ g ∈ D.η.ker, (W' g).val = corner (UnitaryThreeInertia.push A.val r g).mat)
    (h5 : (W' D.cc).val.trace = 0) (W : G ℚ Ω →* GL (Fin 2) (PadicAlgCl l)) (hi : Af.RepIso W' W) : _root_.UpperTheory.V.Z.Win.Dn.IsModularA D ι W := by
  obtain ⟨⟨f, hf⟩, hw⟩ := h A r h1 h2 h3 W' h4 h5
  refine ⟨⟨f, ?_⟩, hw.weak_admissible_iso hi⟩
  obtain ⟨g, hg⟩ := hi
  let χ := cycBar ℚ Ω l ^ (-(e : ℤ))
  have htw : ∀ s, Af.tw W χ s = g * Af.tw W' χ s * g⁻¹ := by
    intro s
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Af.tw_val, Af.tw_val, hg, Units.val_mul, Units.val_mul,
      Matrix.mul_smul, Matrix.smul_mul]
  change f.Att ι (Af.tw W χ)
  refine ⟨?_, hf.2.mono fun w hw A' hA' => ⟨fun s hs => ?_, fun σ hσ => ?_⟩⟩
  · let E : (Fin 2 → Qbar l) ≃ₗ[Qbar l] (Fin 2 → Qbar l) :=
      Matrix.toLin'OfInv (Units.mul_inv g) (Units.inv_mul g)
    have hE (v : Fin 2 → Qbar l) : E v = (↑g⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).mulVec v := rfl
    have hintertwine (s : G ℚ Ω) (v : Fin 2 → Qbar l) :
        E ((Af.tw W χ s).val.mulVec v) = (Af.tw W' χ s).val.mulVec (E v) := by
      rw [hE, hE, htw, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul]
      congr 2
      group
    intro V hV
    obtain ⟨V', hV', hcompl⟩ := hf.1 (V.map E.toLinearMap) (by
      rintro s _ ⟨v, hv, rfl⟩
      exact ⟨_, hV s v hv, hintertwine s v⟩)
    refine ⟨V'.comap E.toLinearMap, fun s v hv => ?_, ?_⟩
    · show E _ ∈ V'
      rw [hintertwine]
      exact hV' s _ hv
    · have hcompl' : IsCompl ((V.map E.toLinearMap).comap E.toLinearMap) (V'.comap E.toLinearMap) :=
        (Submodule.orderIsoMapComap E).symm.isCompl hcompl
      rwa [Submodule.comap_map_eq_of_injective E.injective] at hcompl'
  · rw [htw, (hw A' hA').1 s hs, mul_one, mul_inv_cancel]
  · rw [← (hw A' hA').2 σ hσ, htw, Units.val_mul, Units.val_mul, Matrix.coe_units_inv,
      Matrix.charpoly_units_conj]
theorem UpperTheory.V.Pr.automorphyUnramified_of_locPrints_kisin_gdEnd :
    Loc.LocalPublishedTheorems → _root_.UpperTheory.V.Pr.GdEndAlt → _root_.UpperTheory.V.Aut.AutomorphyUnramifiedCoefficientsAlt := by
  intro hL H Ω _ _ _ K _ _ _ _ l _ c N _ e ψ D _ ι
  obtain ⟨B, hB, -, -, -, hmem, -⟩ := dat_loc D
  obtain ⟨g₁, hM, hfin, h3, h2⟩ := H Ω K l c N e ψ D ι B hB
  have hA : FinA D g₁ := finA_of_end hL D g₁ hM B hmem hfin
  refine ⟨g₁, hM, hA, fun U S ξ r hr hp hI => ?_, fun U S ξ r hp hII h11 W hW => ?_⟩
  · obtain ⟨A, _, _, t, r', ho, ht⟩ := exists_ordPt_of_point hL D g₁ hM U S hA B hmem ξ r hp
    have hl : ∀ s ∈ D.η.ker, (UnitaryThreeInertia.push A.val r' s).left = tor _ t * (r s).left * (tor _ t)⁻¹ := fun s hs => by
      have hright : (r s).right = 1 := (hr s).trans hs
      have hconj : conjBy (tor _ t) r s = GG.ofGL (tor _ t) * r s * GG.ofGL (tor _ t)⁻¹ := by
        rw [map_inv]
        rfl
      rw [ht, hconj, SemidirectProduct.mul_left, SemidirectProduct.mul_left, SemidirectProduct.left_inl,
        SemidirectProduct.left_inl, SemidirectProduct.right_inl, sgnAct_one, SemidirectProduct.mul_right,
        SemidirectProduct.right_inl, hright, mul_one, sgnAct_one]
    have hI' : TypeI D.η (UnitaryThreeInertia.push A.val r') :=
      _root_.UpperTheory.Reformulated.B.Qf5.matIrr_conj (tor _ t) (fun s hs => by
        rw [mats, mats, GG.mat, GG.mat, hl s hs, ← Units.val_mul, ← Units.val_mul]
        congr 1
        group) hI
    have hm : HasMult D.η (UnitaryThreeInertia.push A.val r') := ho.red.mult
    have hiso : Af.RepIso (D.rhoK r hr) (D.rhoK _ hm) :=
      ⟨tor _ t, fun s => hl _ (D.η_ker.ge (Base.galEmb_mem ℚ K Ω s))⟩
    have key := h3 A r' ho (matIrr_open_gd D g₁ hM B hB A r' ho hI') (D.rhoK _ hm) fun s => rfl
    refine _root_.UpperTheory.GalN.V.autCsd_iso_alt ?_ key
    obtain ⟨g, hg⟩ := hiso.symm'
    refine ⟨g, fun s => Units.ext ?_⟩
    rw [Units.val_mul, Units.val_mul, Af.tw_val, Af.tw_val, hg, Units.val_mul, Units.val_mul,
      Matrix.mul_smul, Matrix.smul_mul]
  · obtain ⟨A, _, _, t, r', ho, ht⟩ := exists_ordPt_of_point hL D g₁ hM U S hA B hmem ξ r hp
    let d : Fin 2 → (PadicAlgCl l)ˣ := ![t, t⁻¹]
    let T : GL (Fin 2) (PadicAlgCl l) :=
      Units.map (Matrix.diagonalRingHom (n := Fin 2) (α := PadicAlgCl l)).toMonoidHom
        (MulEquiv.piUnits.symm d)
    have hcorner (g : G ℚ Ω) :
        corner (conjBy (tor _ t) r g).mat = T.val * corner (r g).mat * (↑T⁻¹ : Matrix _ _ _) := by
      ext a b
      show _ = (Matrix.diagonal (fun i => (d i : PadicAlgCl l)) * corner (r g).mat *
        Matrix.diagonal (fun i => (↑(d i)⁻¹ : PadicAlgCl l))) a b
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul, corner, corner, Matrix.submatrix_apply, Matrix.submatrix_apply,
        (conjBy_tor r t).1, wt, zpow_sub, Units.val_mul, mul_right_comm]
      congr 1
      · congr 1
        fin_cases a <;> simp [d, wt1]
      · fin_cases b <;> simp [d, wt1]
    let W' : G ℚ Ω →* GL (Fin 2) (PadicAlgCl l) := (MulAut.conj T).toMonoidHom.comp W
    have hW' : ∀ s, W' s = T * W s * T⁻¹ := fun s => rfl
    have hII' : TypeII D.η (UnitaryThreeInertia.push A.val r') := by
      rw [ht]
      refine ⟨fun g hg a b hab => ?_, _root_.UpperTheory.Reformulated.B.Qf5.matIrr_conj T (fun s _ => ?_) hII.2⟩
      · rw [(conjBy_tor r t).1, hII.1 g hg a b hab, mul_zero]
      · rw [hcorner]
        simp only [← Matrix.mul_assoc]
        rw [Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
    exact _root_.UpperTheory.GalN.V.modOfEnd'_alt D h2 A r' ho hII' (fun g hg => by
      apply Subtype.ext
      show (UnitaryThreeInertia.push A.val r' g).mat 1 1 = 1
      rw [ht, (conjBy_tor r t).1, h11 g hg]
      simp [wt]) W' (fun g hg => by
      rw [ht, hcorner, hW', Units.val_mul, Units.val_mul, hW.1 g hg]) (by
      rw [hW', Units.val_mul, Units.val_mul, Matrix.trace_units_conj, hW.2]) W (Af.RepIso.symm' ⟨T, hW'⟩)
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.GaloisCohomology UpperTheory.Top GlobalTheory.Mem.LiteralAutomorphy
namespace UpperTheory.V.HV.Core0
open UpperTheory.V.Lit
theorem cohInp_alt (hN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) (hK : ∃ CK : ℝ, LemmaK CK) : U3.CohInp :=
  ⟨_root_.UpperTheory.V.HV.U.locPrints_of_litN hN, hN.coh.pt, hN.coh.gf, hN.coh.ge, hK⟩
theorem automorphyUnramified_of_litN_of_gdEnd (hN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) (hG : _root_.UpperTheory.V.Pr.GdEndAlt) : _root_.UpperTheory.V.Aut.AutomorphyUnramifiedCoefficientsAlt := _root_.UpperTheory.V.Pr.automorphyUnramified_of_locPrints_kisin_gdEnd (_root_.UpperTheory.V.HV.U.locPrints_of_litN hN) hG
end UpperTheory.V.HV.Core0
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TCountE
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing Filter GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj)
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Z.Mult (Cp At IsDec CompOf Mult)
open UpperTheory.V.Z.J.D
open UpperTheory.V.Z.Desc.V0
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
private theorem ce_teich_ex (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] [CharP (ResidueField O) l] :
    ∃ τ : ResidueField O →* O, ∀ x, residue O (τ x) = x := by
  haveI : CharP (O ⧸ maximalIdeal O) l := inferInstanceAs (CharP (ResidueField O) l)
  haveI : PerfectRing (ResidueField O) l := inferInstance
  let j : ResidueField O →+* Perfection (O ⧸ maximalIdeal O) l :=
    Perfection.lift l (ResidueField O) (O ⧸ maximalIdeal O) (RingHom.id (ResidueField O))
  have hj : ∀ x, Perfection.coeff (O ⧸ maximalIdeal O) l 0 (j x) = x := fun x => by
    have := (Perfection.lift l (ResidueField O) (O ⧸ maximalIdeal O)).symm_apply_apply (RingHom.id (ResidueField O))
    exact RingHom.congr_fun this x
  refine ⟨(Perfection.teichmuller l (maximalIdeal O)).comp j, fun x => ?_⟩
  exact (Perfection.mk_teichmuller (j x)).trans (hj x)
private theorem ce_isTeich {l : ℕ} [hl : Fact l.Prime] {F : W.GFrame l} (c : Coef l) {n : ℕ} (r : Resid F c.O n) :
    ∃ t, r.IsTeich t := by
  obtain ⟨hc, hfin, hlm, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
  haveI : Finite (ResidueField c.O) := hfin
  haveI : CharP (ResidueField c.O) l := by
    refine (CharP.charP_iff_prime_eq_zero hl.out).2 ?_
    rw [← map_natCast (residue c.O), residue_eq_zero_iff]
    exact hlm
  obtain ⟨τ, hτ⟩ := ce_teich_ex l c.O
  refine ⟨fun i => (Units.map τ).comp (r.chib i), fun i g => ⟨hτ _, ?_⟩⟩
  rw [MonoidHom.comp_apply, ← map_pow, ← Nat.card_units, pow_card_eq_one', map_one]
private theorem ce_open {G O : Type} [Group G] [TopologicalSpace G] [CommRing O] {m : ℕ} (f : O →+* ℂ) (hf : Function.Injective f)
    (τ : G →* GL (Fin m) O) (h : IsOpen (((Matrix.GeneralLinearGroup.map f).comp τ).ker : Set G)) : IsOpen (τ.ker : Set G) := by
  have : ((Matrix.GeneralLinearGroup.map f).comp τ).ker = τ.ker := by
    refine MonoidHom.ker_comp_of_injective _ _ fun a b hab => ?_
    ext i j
    exact hf (congrArg (fun x : GL (Fin m) ℂ => (x : Matrix (Fin m) (Fin m) ℂ) i j) hab)
  rwa [this] at h
private theorem ce_ex {M J : Type} [AddCommGroup M] [Module ℂ M] [Fintype J] (Y : J → Submodule ℂ M) (Z : Submodule ℂ M)
    (hf : FiniteDimensional ℂ Z) (hZ : Z ≠ ⊥) (hsum : Module.finrank ℂ Z = ∑ i, Module.finrank ℂ ↥(Y i ⊓ Z)) :
    ∃ i, Y i ⊓ Z ≠ ⊥ := by
  by_contra h
  push Not at h
  apply hZ
  rw [← Submodule.finrank_eq_zero, hsum]
  exact Finset.sum_eq_zero fun i _ => by rw [h i, finrank_bot]
private def ce_mk {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    {n : ℕ} {s : HidaSetting l L Ω} (V : s.Lev) (hS : ∀ v ∈ s.S, IsSplitAt (s.w v)) (τ : ∀ w : Plc L, SmIrr (GLw n w))
    (σ : Submodule ℂ (UA L n → ℂ)) (h : ∀ w, IsSplitAt w → Cp σ w (τ w)) : Comps V σ where
  l v := τ (s.w v.1)
  u v := τ (s.w v)
  o := τ (s.w s.v0)
  hl v := h _ (hS _ (Or.inl v.2))
  hu v := h _ (hS _ (Or.inr (Or.inl v.2)))
  ho := h _ (hS _ (Or.inr (Or.inr rfl)))
private theorem ce_ne {M : Type} [AddCommGroup M] [Module ℂ M] {Y Z : Submodule ℂ M} (h : Y ⊓ Z ≠ ⊥) : Y ≠ ⊥ :=
  fun h' => h (by rw [h', bot_inf_eq])
section Set
variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {n : ℕ} {c : Coef l}
  {H : HSet L Ω l n c} {A : Type} [CommRing A] [Algebra c.O A] [IsLocalRing A] {θ : H.X.I.T →* Aˣ} {ι : Qbar l ≃+* ℂ}
  {x : A →+* Qbar l} {lam : Wt L l n} {d : ℕ} {ξ : GV n H.Sl →* GL (Fin d) ℂ} {c0 : ℕ}
  {sp : H.X.Fn A H.m → Fin H.m → H.X.Fn ℂ d}
private theorem ce_fin (hsp : H.IsSpec θ ι x lam ξ c0 sp) (K : H.Lev) (ev : H.Op → ℂ) :
    FiniteDimensional ℂ (zPart H θ ι x lam ξ K c0 ev) :=
  haveI := hsp.fin K c0 le_rfl
  Submodule.finiteDimensional_of_le (S₂ := H.ClAt θ ι x lam ξ K c0) (inf_le_left.trans (iSup_le fun _ => inf_le_left))
private theorem ce_one (hSl : Slope) (hO1 : _root_.UpperTheory.V.Z.J.D.Ord1Alt) (hEP : EigPi) (N : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) (hAx : H.Ax)
    (hsp : H.IsSpec θ ι x lam ξ c0 sp) (ev : H.Op → ℂ) (hev : ∀ v j, ‖ι.symm (ev (.inr (v, j)))‖ = 1)
    (τ : ∀ v, SmIrr (GLw n (H.Sl v))) :
    Module.rank ℂ (eigL H.Sl (piRep fun v => (τ v).ρ) c0 (fun v i y => (ι (H.finPart θ x lam v i y))⁻¹)
      fun v j => H.lowVal ι lam v (j + 1) * ev (.inr (v, j))) ≤ 1 := by
  refine hEP L n H.V H.Sl τ c0 _ _ fun v => ?_
  refine hO1 N _ n _ _ (τ _).smooth (τ _).irred c0 _ _ (fun i y hy => ?_)
    (hSl L Ω l n c H hAx ι lam v (fun j => ev (.inr (v, j))) (hev v))
  rw [hsp.triv v i y hy, map_one, inv_one]
end Set
section Stg
variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  (s : HidaSetting l L Ω)
private theorem ce_w (v : Plc (Lp L)) : (s.w v).under (𝓞 (Lp L)) = v := by
  ext x
  exact (s.hw v (algebraMap (𝓞 (Lp L)) (𝓞 L) x)).symm.trans (s.hA v x)
private theorem ce_split (w : Plc L) (h : w.under (𝓞 (Lp L)) ∈ s.S) : IsSplitAt w :=
  UpperTheory.isSplitAt_of_decomposition_le_restriction_range L Ω (s.A _) _ (s.hA _) (s.split _ h) w rfl
private theorem ce_S (v : Plc (Lp L)) (h : v ∈ s.S) : IsSplitAt (s.w v) := ce_split s _ ((ce_w s v).symm ▸ h)
private theorem ce_irr (V : s.Lev) {n : ℕ} (ρ : V.frame.G₀ →* GL (Fin n) (Qbar l)) (hi : Af.IsIrr ρ) : Af.IsIrr (ρ.comp V.pr) := by
  have hpr : Function.Surjective V.pr := fun g => by
    obtain ⟨τ, hτ⟩ : ∃ τ, ReciprocityTheory.Gal.toGS Ω V.S' τ = g.1 := QuotientGroup.mk_surjective g.1
    obtain ⟨t, rfl⟩ := (V.hη τ).1 (by rw [hτ]; exact g.2)
    exact ⟨t, Subtype.ext hτ⟩
  refine ⟨hi.1, fun _ _ _ => Submodule.mem_top, fun M hM hI => hi.2.2 M hM fun g => ?_⟩
  obtain ⟨g, rfl⟩ := hpr g
  exact hI g
end Stg
private theorem eigenpart_zero_eq_top {G R W : Type} [Group G] [CommRing R] [AddCommGroup W] [Module R W] (ρ : Representation R G W) :
    ePart ρ (0 : G →₀ ℤ) 0 = ⊤ := by
  simp [ePart, opE]
private theorem ce_top {M J : Type} [AddCommGroup M] [Module ℂ M] [Fintype J] (Y : J → Submodule ℂ M) (Z E : Submodule ℂ M) (hE : E = ⊤)
    (hsum : Module.finrank ℂ ↥(Z ⊓ E) = ∑ i, Module.finrank ℂ ↥(Y i ⊓ Z ⊓ E)) :
    Module.finrank ℂ Z = ∑ i, Module.finrank ℂ ↥(Y i ⊓ Z) := by
  subst hE
  have h : ∀ S : Submodule ℂ M, Module.finrank ℂ ↥(S ⊓ ⊤) = Module.finrank ℂ S := fun S => by rw [inf_top_eq]
  simpa only [h] using hsum
private theorem cardinal_factor_eq_one {M : Type} [AddCommGroup M] [Module ℂ M] (Y Z ZL E : Submodule ℂ M) (hE : E = ⊤) (h0 : Y ⊓ Z ≠ ⊥) (h2 : Y ⊓ Z = Y ⊓ ZL)
    (a b : Cardinal) (ha : a ≤ 1) (h3 : Module.rank ℂ ↥(Y ⊓ ZL ⊓ E) = a * b) : a = 1 := by
  subst hE
  rcases Cardinal.le_one_iff.1 ha with h | h
  · rw [h, zero_mul, Submodule.rank_eq_zero, inf_top_eq, ← h2] at h3
    exact absurd h3 h0
  · exact h
private theorem ce_cnt {M J : Type} [AddCommGroup M] [Module ℂ M] [Fintype J] (Y : J → Submodule ℂ M) (Z ZL E : Submodule ℂ M)
    (hf : FiniteDimensional ℂ Z) (hsum : Module.finrank ℂ ↥(Z ⊓ E) = ∑ i, Module.finrank ℂ ↥(Y i ⊓ Z ⊓ E)) (P : J → Prop)
    (a b : Cardinal) (k : ℕ) (h1 : ∀ i, Y i ⊓ Z ≠ ⊥ → P i) (h2 : ∀ i, P i → Y i ⊓ Z = Y i ⊓ ZL) (ha1 : a = 1)
    (h3 : ∀ i, P i → Module.rank ℂ ↥(Y i ⊓ ZL ⊓ E) = a * b) (hk : Nat.card {i // P i} = k) :
    (Module.finrank ℂ ↥(Z ⊓ E) : Cardinal) = k * b := by
  classical
  have h6 : ∀ i, (Module.finrank ℂ ↥(Y i ⊓ Z ⊓ E) : Cardinal) = if P i then b else 0 := fun i => by
    haveI : FiniteDimensional ℂ ↥(Y i ⊓ Z ⊓ E) := Submodule.finiteDimensional_of_le (inf_le_left.trans inf_le_right)
    rw [Module.finrank_eq_rank]
    split_ifs with h
    · rw [h2 i h, h3 i h, ha1, one_mul]
    · rw [Submodule.rank_eq_zero]
      by_contra h'
      refine h (h1 i fun h'' => h' ?_)
      rw [h'', bot_inf_eq]
  rw [hsum, Nat.cast_sum, Finset.sum_congr rfl fun i _ => h6 i, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, ← hk,
    Nat.card_eq_fintype_card, Fintype.card_subtype]
set_option maxHeartbeats 800000 in
theorem UpperTheory.V.Z.Desc.V0.count_e_of_sph_same_at_same_bc_dims :
    UpperTheory.V.Z.J.D.WtEx → UpperTheory.V.Z.J.D.Decomp → ZDecE → UpperTheory.V.Z.J.D.ZEq → _root_.UpperTheory.V.Z.J.D.SphSameAlt → _root_.UpperTheory.V.Z.J.D.AtSameAlt → _root_.UpperTheory.V.Z.J.D.BcOfAlt → YDimE → UpperTheory.V.Z.J.D.CompsEx → UpperTheory.V.Z.J.D.Slope → _root_.UpperTheory.V.Z.J.D.Ord1Alt → UpperTheory.V.Z.J.D.EigPi → _root_.UpperTheory.V.Z.Desc.V0.CountEAlt := by
  intro hWt hDec hZD _ hSph hAt hBc hYD _ hSl hO1 hEP PH hM hCO l _ L Ω _ _ _ _ _ _ s n hn V hV h4 ι lam
  have N := PH.toClassicalTheorems.litN
  have hU : GlobalTheory.BCT.Unr L := UpperTheory.isUnramifiedAt_totallyReal_of_inertia_le_restriction_range L Ω s.unr
  obtain ⟨lam', hl'⟩ := hWt l L Ω s n hn V hV ι lam
  obtain ⟨a₀, -, ha⟩ := hM L hU n hn h4 lam'
  refine ⟨a₀, ?_⟩
  intro Q c r m τ₀ hτ d e ξ he A _ _ _ θ x c0 sp hθ hsp K ev hev hZ hP
  have hAx := _root_.UpperTheory.V.Hi.axU_s N l L Ω s n hn V Q c m τ₀
  have hS := ce_S s
  obtain ⟨t, ht⟩ := ce_isTeich c r
  have hop : IsOpen (τ₀.ker : Set (KT n (wt s))) :=
    ce_open _ (ι.injective.comp Subtype.val_injective) τ₀ (hτ t ht).1
  obtain ⟨S, K', J, _, σ, hSec, hLev, hKL, hID, hInd, hUn, hFix, hLe⟩ :=
    hDec l L Ω s n hn V hV Q c ι m τ₀ lam d e ξ he hop lam' hl' c0
  have hA : ∀ i, IsAutRepU (σ i) := fun i => (hID.1 i).1
  have hsumE := fun (a : GLw n (s.w s.v0) →₀ ℤ) (N : ℕ) (h : ∀ g ∈ a.support, g ∈ KO _ (Fin n)) =>
    hZD l L Ω s n hn V hV Q c ι m τ₀ lam d e ξ he A θ x c0 sp hθ hsp K ev hev J σ hA hInd hLe a N h
  have he0 : eC Q τ₀ d (0 : GLw n (s.w s.v0) →₀ ℤ) 0 = ⊤ := eigenpart_zero_eq_top _
  have hsum := ce_top (fun i => YOf Q ι τ₀ e ξ (σ i)) _ _ he0 (hsumE 0 0 (by simp))
  have hfin := ce_fin hsp K ev
  obtain ⟨i0, h0⟩ := ce_ex (fun i => YOf Q ι τ₀ e ξ (σ i)) _ hfin hZ hsum
  have hY0 : YOf Q ι τ₀ e ξ (σ i0) ≠ ⊥ := ce_ne h0
  obtain ⟨Y, hY, -, -, hLG⟩ := _root_.UpperTheory.V.Z.Desc.P.partU_alt PH l L Ω s n hn V Q c r ι m τ₀ hτ lam d e ξ he (σ i0) (hA i0) hY0
  have hi := hP Y (by rw [hY]; exact h0)
  have hc : Continuous (Y.r.comp V.pr) := Y.cont.comp (V.pr_cont W.continuous_resP)
  obtain ⟨π, hreg, hcsd, hat, hinf, hsat⟩ := hBc PH L Ω hU l s.odd ι n hn (σ i0) (hA i0) (Y.r.comp V.pr) hc (ce_irr s V Y.r hi)
    (Eventually.of_forall hLG)
  have hns : ∀ w : Plc L, ¬ IsSplitAt w → w.under (𝓞 (Lp L)) ∉ s.S := fun w h h' => h (ce_split s w h')
  choose τ hτπ using fun w => (_root_.UpperTheory.V.Af.local_comp_complex_of_printed_results PH.toClassicalTheorems L n π w).1
  have hCp : ∀ i, At π (σ i) → ∀ w, IsSplitAt w → Cp (σ i) w (τ w) := fun i h w hw =>
    hCO L hU n hn h4 π hreg hcsd (σ i) (hA i) (fun w hw => hUn i w (hns w hw)) h w hw _ (hτπ w)
  have hcard := ha π hreg hcsd (fun v => hinf _ _ ((hID.1 i0).2.1 v)) (fun w hw => hsat w (hUn i0 w (hns w hw))) S hSec K' hLev
    (fun w hw => hKL w (hns w hw)) (fun w hwS hw => ⟨τ w, hτπ w, hFix i0 w hwS hw _ (hCp i0 hat w hw)⟩) J σ hID
  have h1 := fun i h => hAt N l L Ω s n hn V hV Q c ι m τ₀ lam d e ξ he A θ x c0 sp hθ hsp K ev _ _ (hA i0) (hA i) h0 h π hat
  have h2 := fun i (h : At π (σ i)) => hSph N l L Ω s n hn V hV Q c ι m τ₀ lam d e ξ he A θ x c0 sp hθ hsp K ev hev _ _ (hA i0) (hA i)
      (fun w hw => ⟨τ w, hCp i0 hat w hw, hCp i h w hw⟩) h0
  have h3 := fun (a : GLw n (s.w s.v0) →₀ ℤ) (N : ℕ) i (h : At π (σ i)) =>
    hYD l L Ω s n hn V hV Q c ι m τ₀ lam d e ξ he (σ i) (hA i) (hUn i) ((hl' _ (hA i)).2 (hID.1 i).2.1)
      (ce_mk V hS τ (σ i) (hCp i h)) c0 (fun v i y => (ι ((hset Q τ₀).finPart θ x.toRingHom lam v i y))⁻¹)
      (fun v j => (hset Q τ₀).lowVal ι lam v (j + 1) * ev (.inr (v, j))) a N
  have h5 := ce_one hSl hO1 hEP N hAx hsp ev hev fun v => τ (s.w v.1)
  have ha1 := cardinal_factor_eq_one _ _ _ _ he0 h0 (h2 i0 hat) _ _ h5 (h3 0 0 i0 hat)
  refine ⟨π, σ i0, ce_mk V hS τ (σ i0) (hCp i0 hat), fun u => hτπ _, hτπ _, hY0, hA i0, fun a N' hs => ?_⟩
  exact ce_cnt (fun i => YOf Q ι τ₀ e ξ (σ i)) _ _ _ hfin (hsumE a N' hs) (fun i => At π (σ i)) _ _ a₀ h1 h2 ha1 (h3 a N') hcard
end
end
