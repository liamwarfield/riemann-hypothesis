module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.PAdicSplitting.LocalGlobalCompatAtIwahoriFixedPlaces
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CharpolyFromTrace.GoodLiftAlt
public import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.WeilGroupRestriction.NotRealComplex
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IneInclOntoUnits
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RestrictsWdPst
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.Closed
public import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LiftInvariantsFinrankEq
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalArtinCompNormCompat
public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.EventuallyHasSatakeParameters
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLevelAwayAdapted
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BlockCharacterApproximation.NeatOfPlace
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSphericalTwistOfUnr
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.UnrField
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.SphericalOperatorsExist
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MultiplicityOneRigidity.GelfandKazhdanDualOfRigidity
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.CuspRapidDecayGL.CuspRapidDecaySiegelGL
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.RecTExists
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PlainTorsionPairs.EndoscopyRank2Ordinary

@[expose] public section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
  UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.isLocalHom UpperTheory.V.Pr.IsCD.fin
  UpperTheory.V.Alg.IsCO.toIsLocalRing UpperTheory.V.Alg.IsCO.complete
  UpperTheory.V.Alg.IsCO.isLocalHom UpperTheory.V.Alg.IsCO.self

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InePolLpTwOfMemIne
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RoadU.DepthZeroRec

theorem inePol_lpTw_of_mem_Ine {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    (y : WD h) (s : ℝ) {σ : G E Ω} (hσ : σ ∈ Ine (F := E) A) :
    (y.lpTw s).inePol σ = y.inePol σ := by
  rw [WD.inePol_of_mem_Ine _ hσ, WD.inePol_of_mem_Ine _ hσ]
  obtain ⟨m, b, rfl⟩ := y.exists_rep
  rw [WD.lpTw, WD.lpTwist_mk, WD.charPol_mk, WD.charPol_mk]
  congr 1
  show ((unrChar h (qPow w s) (ineIncl h ⟨σ, hσ⟩) : ℂˣ) : ℂ) • b.ρ (ineIncl h ⟨σ, hσ⟩) = _
  rw [WeilDeligne.unrChar_apply, deg_ineIncl, zpow_zero, Units.val_one, one_smul]

end GlobalTheory.RoadU.DepthZeroRec
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CharpolyFromTrace.GoodLiftCHolds
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CharpolyFromTrace.NumberField
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel UpperTheory.Gal.TypesAndIwahori GlobalTheory.Cong

namespace UpperTheory.Gal.NearKilling

structure CmExt (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] where
  K : Type
  [field : Field K]
  [numberField : NumberField K]
  [isCM : IsCMField K]
  [algE : Algebra E K]
  [algΩ : Algebra K Ω]
  [tower : IsScalarTower E K Ω]
  [closure : IsAlgClosure K Ω]

attribute [instance] CmExt.field CmExt.numberField CmExt.isCM CmExt.algE CmExt.algΩ CmExt.tower CmExt.closure

instance (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] : Inhabited (CmExt E Ω) :=
  ⟨{ K := E }⟩

def GoodLiftC : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l a : ℕ) [Fact l.Prime],
    1 ≤ a → ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)), InScope .all l π χ → ∀ w : HeightOneSpectrum (𝓞 E),
    ∃ (X : CmExt E Ω) (P : CuspSub X.K a) (χ' : HChar (maximalRealSubfield X.K)),
      InertialTypesAlt.Lifts (InertialTypesAlt.Pt.base Ω π) ({ K := X.K, π := P } : InertialTypesAlt.Pt E Ω a) ∧ InScope .good l P χ' ∧
      (∀ A : ValuationSubring Ω, IsPlaceOver A w → (∀ g ∈ Dec (F := E) A, UnramifiedFromSplittingCriterion.Fixes (F := E) X.K g) ∧
        ∀ w' : HeightOneSpectrum (𝓞 X.K), IsPlaceOver A w' → IsSplitAt w') ∧
      ∀ (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l)), Weak π ι r → Weak P ι (r.comp (UpperTheory.V.Af.Bc.res E Ω X.K))

def PolBC : Prop :=
  ∀ (K M : Type) [Field K] [NumberField K] [IsCMField K] [Field M] [NumberField M] [IsCMField M] [Algebra K M] (a : ℕ), 1 ≤ a →
    ∀ (π : CuspSub K a) (P : CuspSub M a) (χ : HChar (maximalRealSubfield K)), GlobalTheory.ContraPair.PolarizedPair π χ →
    UpperTheory.V.Published.WeakBC (CG.mk π).HasSat (CG.mk P).HasSat →
    (∃ χ' : HChar (maximalRealSubfield M), GlobalTheory.ContraPair.PolarizedPair P χ') ∧
      (χ = quadChar K ^ a → GlobalTheory.ContraPair.PolarizedPair P (quadChar M ^ a))

def WeakRes : Prop :=
  ∀ (K M Ω : Type) [Field K] [NumberField K] [IsCMField K] [Field M] [NumberField M] [IsCMField M] [Algebra K M] [Field Ω]
    [Algebra K Ω] [Algebra M Ω] [IsScalarTower K M Ω] [IsAlgClosure K Ω] [IsAlgClosure M Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (a : ℕ) (π : CuspSub K a) (P : CuspSub M a), UpperTheory.V.Published.WeakBC (CG.mk π).HasSat (CG.mk P).HasSat →
    ∀ r : G K Ω →* GL (Fin a) (Qbar l), Weak π ι r → Weak P ι (r.comp (UpperTheory.V.Af.Bc.res K Ω M))

def StepLift : Prop :=
  ∀ (K M Ω : Type) [Field K] [NumberField K] [IsCMField K] [Field M] [NumberField M] [IsCMField M] [Algebra K M] [Field Ω]
    [Algebra K Ω] [Algebra M Ω] [IsScalarTower K M Ω] [IsAlgClosure K Ω] [IsAlgClosure M Ω] [IsGalois K M],
    (Module.finrank K M).Prime → ∀ (l a : ℕ) [Fact l.Prime], 1 ≤ a →
    ∀ (π : CuspSub K a) (χ : HChar (maximalRealSubfield K)), InScope .all l π χ →
    ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)), IsPlaceOver A v →
      (∃ τ ∈ Ine (F := K) A, ¬ UnramifiedFromSplittingCriterion.Fixes (F := K) M τ) → (∃ B, (CG.mk π).HasSat v B) →
    ∃ (P : CuspSub M a) (χ' : HChar (maximalRealSubfield M)),
      UpperTheory.V.Published.WeakBC (UpperTheory.CBC.Cusp.cx π).sat (UpperTheory.CBC.Cusp.cx P).sat ∧
      UpperTheory.CBC.SplitLift (UpperTheory.CBC.Cusp.cx π) (UpperTheory.CBC.Cusp.cx P) ∧ InScope .all l P χ' ∧
      (χ = quadChar K ^ a → GlobalTheory.ContraPair.PolarizedPair P (quadChar M ^ a)) ∧
      ∀ (ι : Qbar l ≃+* ℂ) (r : G K Ω →* GL (Fin a) (Qbar l)), Weak π ι r → Weak P ι (r.comp (UpperTheory.V.Af.Bc.res K Ω M))

end UpperTheory.Gal.NearKilling
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CharpolyFromTrace.StepLift
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel UpperTheory.Gal.TypesAndIwahori GlobalTheory.Cong UpperTheory.Gal.NearKilling

theorem UpperTheory.Gal.NearKilling.stepLift :
    UpperTheory.V.Z.Bc.CBCc → UpperTheory.Gal.UnramifiedFromSplittingCriterion.NoSelfTwist → PolBC → WeakRes → StepLift := by
  intro hC hN hP hW K M Ω _ _ _ _ _ _ _ _ _ _ _ _ _ _ hp l a _ ha π χ hs A v hv hτ hsat
  obtain ⟨hreg, hpol, -⟩ := hs
  have hK : IsTotallyComplex K := inferInstance
  have hM : IsTotallyComplex M := inferInstance
  rcases (hC K M hp hK a ha).1 (.cx π) with ⟨η, hη, hi⟩ | ⟨Q, hw, hinf, hsplit⟩
  · exfalso
    obtain ⟨B, hB⟩ := hsat
    refine hN K M Ω hp A v hv hτ a ha (CG.mk π) B hB η hη ?_
    rw [CG.twist_mk]
    exact Quotient.sound hi
  · cases Q with
    | re Q => exact (PositivityTheory.Pf1.CLGD.K.LKW.not_real_complex M inferInstance hM).elim
    | cx P =>
      have hw' : UpperTheory.V.Published.WeakBC (CG.mk π).HasSat (CG.mk P).HasSat := hw
      obtain ⟨⟨χ', hχ'⟩, hq⟩ := hP K M a ha π P χ hpol hw'
      refine ⟨P, χ', hw, hsplit, ⟨?_, hχ', trivial⟩, hq, fun ι r hr => hW K M Ω l ι a π P hw' r hr⟩
      refine (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => ?_
      have h1 := GlobalTheory.CuspRep.ParLaws.hasInfChar_infChar (CG.mk π) (τ.comp (algebraMap K M))
      have h2 : P.HasInfChar τ ((CG.mk π).infChar (τ.comp (algebraMap K M))) := hinf τ _ h1
      have h3 : (CG.mk P).infChar τ = (CG.mk π).infChar (τ.comp (algebraMap K M)) :=
        CG.HasInfChar.infChar_eq h2
      rw [h3]
      exact hreg _
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CharpolyFromTrace.WeakRes
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel UpperTheory.Gal.TypesAndIwahori GlobalTheory.Cong UpperTheory.Gal.NearKilling

open GlobalTheory.WeakBaseChange in
theorem UpperTheory.Gal.NearKilling.weakRes :
    WeakRes := by
  intro E M Ω _ _ _ _ _ _ _ _ _ _ _ _ _ l _ ι a π P hL r hr
  obtain ⟨hc, hss, hatt⟩ := hr
  refine ⟨hc.comp (UpperTheory.V.Af.continuous_restrictScalarsHom E M Ω), ?_, ?_⟩
  · haveI := finiteIndex_range_res E M Ω
    set H := (UpperTheory.V.Af.Bc.res E Ω M).range with hH
    haveI : (H.normalCore.comap (UpperTheory.V.Af.Bc.res E Ω M)).FiniteIndex := finiteIndex_comap _ _
    refine isSSRep_of_finiteIndex _ (H.normalCore.comap (UpperTheory.V.Af.Bc.res E Ω M)) ?_
    have hrange : ((UpperTheory.V.Af.Bc.res E Ω M).comp (H.normalCore.comap (UpperTheory.V.Af.Bc.res E Ω M)).subtype).range = H.normalCore := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact y.2
      · intro hx
        obtain ⟨y, hy⟩ := (Subgroup.normalCore_le H hx : x ∈ (UpperTheory.V.Af.Bc.res E Ω M).range)
        exact ⟨⟨y, by rw [Subgroup.mem_comap, hy]; exact hx⟩, hy⟩
    have := UpperTheory.semisimple_restriction_to_normal_subgroup _ _ _ a r ((UpperTheory.V.Af.Bc.res E Ω M).comp (H.normalCore.comap (UpperTheory.V.Af.Bc.res E Ω M)).subtype)
      (by rw [hrange]; exact Subgroup.normalCore_normal H) hss
    rwa [MonoidHom.comp_assoc]
  · unfold UpperTheory.V.Published.WeakBC at hL
    filter_upwards [(GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under E M).eventually hatt, hL] with w h hW
    obtain ⟨B, hB, hF⟩ := h
    have h2 := GlobalTheory.AttResTower.normV_under_pow (K := E) w
    set f := w.asIdeal.inertiaDeg (𝓞 E)
    obtain ⟨B', hB', hP⟩ := hW f h2
    have hBB : B' = B := GlobalTheory.T.cuspRep_satakeParameters_unique E a (CG.mk π) (w.under (𝓞 E)) B' B hB' hB
    subst hBB
    refine ⟨B'.map (· ^ f), hP, ?_⟩
    have h3 := (UpperTheory.frobenius_power_compatibility E M Ω l ι w f h2).1 a r _ hF
    rw [h2, algSat_pow]
    exact h3
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CharpolyFromTrace.PolNorm
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel UpperTheory.Gal.TypesAndIwahori GlobalTheory.Cong UpperTheory.Gal.NearKilling

private theorem pol_norm (hjs : GlobalTheory.Published.JacquetShalikaRigidity) (hgk : GlobalTheory.Published.GelfandKazhdanDual)
    (K M : Type) [Field K] [NumberField K] [IsCMField K] [Field M] [NumberField M]
    [IsCMField M] [Algebra K M] (a : ℕ) (ha : 1 ≤ a) (π : CuspSub K a) (π' : CuspSub M a) (χ : HChar (maximalRealSubfield K))
    (hpol : GlobalTheory.ContraPair.PolarizedPair π χ) (hbc : UpperTheory.V.Published.WeakBC (CG.mk π).HasSat (CG.mk π').HasSat) :
    ∃ χ' : HChar (maximalRealSubfield M), GlobalTheory.ContraPair.PolarizedPair π' χ' ∧
      ∀ x : Ideles M, (compNorm M χ').1 x = (compNorm K χ).1 (GroundTheory.Global.ideleNorm K M x) := by
  obtain ⟨χ', hs, hN⟩ := GlobalTheory.T.hecke_char_norm_descent K M a χ hpol.sign
  refine ⟨χ', ⟨hs, ?_⟩, hN⟩
  apply UpperTheory.polOfSat_of_thetaSat UpperTheory.theta_satake_parameters_inverse hjs hgk M a ha π' (compNorm M χ')

  have hT := GlobalTheory.PolarizedSat.hasSat_conjPlace GlobalTheory.automorphicFormsFiniteGL K a π χ hpol
  have hU : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, (compNorm K χ).UnrAt v :=
    Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified _)
  have hT' := GlobalTheory.T.eventually_cofinite_under_of_eventually_cofinite_places K M _ (hT.and hU)
  have hbc' := (conjSrc_injective (IsCMField.complexConj M).toRingEquiv).tendsto_cofinite.eventually hbc
  filter_upwards [hT', hbc, hbc'] with w ⟨hTw, hUw⟩ hw hcw
  obtain ⟨f, hf⟩ := GlobalTheory.T.exists_normV_eq_normV_under_pow K M w
  obtain ⟨hu', hval⟩ := GlobalTheory.T.unramifiedAt_value_heckeChar_comp_ideleNorm K M (compNorm K χ) (compNorm M χ') hN w f hf hUw
  refine ⟨hu', ?_⟩
  obtain ⟨B, hB1, hB2⟩ := hw f hf
  have hcu := GlobalTheory.T.under_conjugatePlace_eq_conjugatePlace_under K M w
  have hnc : normV (UpperTheory.V.Af.Bc.cPl w) = normV ((UpperTheory.V.Af.Bc.cPl w).under (𝓞 K)) ^ f := by
    rw [hcu]
    have e1 : normV (UpperTheory.V.Af.Bc.cPl w) = normV w := by
      simpa only [normV, ← Ideal.absNorm_eq_natCard, UpperTheory.V.Af.Bc.cPl] using GlobalTheory.UnrEuler.ConjFac.absNorm_conjSrc (IsCMField.complexConj M).toRingEquiv w
    have e2 : normV (UpperTheory.V.Af.Bc.cPl (w.under (𝓞 K))) = normV (w.under (𝓞 K)) :=
      by simpa only [normV, ← Ideal.absNorm_eq_natCard, UpperTheory.V.Af.Bc.cPl] using GlobalTheory.UnrEuler.ConjFac.absNorm_conjSrc (IsCMField.complexConj K).toRingEquiv (w.under (𝓞 K))
    rw [e1, e2, hf]
  obtain ⟨C, hC1, hC2⟩ := hcw f hnc
  rw [hcu] at hC1
  have e := GlobalTheory.T.cuspRep_satakeParameters_unique K a (CG.mk π) _ _ _ hC1 (hTw B hB1)
  refine ⟨_, _, hB2, hC2, ?_⟩
  rw [e, hval]
  simp only [Multiset.map_map]
  refine Multiset.map_congr rfl fun α _ => ?_
  simp only [Function.comp_apply, mul_pow, inv_pow, mul_inv, inv_inv]

theorem UpperTheory.Gal.NearKilling.polBC :
    GlobalTheory.Published.JacquetShalikaRigidity → GlobalTheory.Published.GelfandKazhdanDual → PolBC := by
  intro hjs hgk K M _ _ _ _ _ _ _ a ha π P χ hpol hbc
  obtain ⟨χ', hχ', hN⟩ := pol_norm hjs hgk K M a ha π P χ hpol hbc
  refine ⟨⟨χ', hχ'⟩, fun hq => ?_⟩
  have h1 : compNorm M χ' = 1 := by
    refine Subtype.ext (MonoidHom.ext fun x => ?_)
    rw [hN x, hq, map_pow, compNorm_quadChar, one_pow]
    rfl
  refine ⟨fun v => ?_, ?_⟩
  · have e : (quadChar M ^ a).locInf v (-1) = (quadChar M).locInf v (-1) ^ a := rfl
    rw [e, quadChar_locInf]
  · rw [map_pow, compNorm_quadChar, one_pow]
    have h := hχ'.dual
    rwa [h1] at h
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CharpolyFromTrace.AllLift
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel UpperTheory.Gal.TypesAndIwahori GlobalTheory.Cong UpperTheory.Gal.NearKilling

private theorem dec_restrict {F K Ω : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω] [Algebra F K]
    [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω] {A : ValuationSubring Ω} {g : G K Ω} (hg : g ∈ Dec (F := K) A) :
    AlgEquiv.restrictScalars F g ∈ Dec (F := F) A :=
  GlobalTheory.FunExt.ConjLift.mem_Dec_of_iff fun x => apply_mem_iff_of_mem_Dec hg x

private def Carry {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l a : ℕ)
    [Fact l.Prime] (π : CuspSub E a) (S : Set (HeightOneSpectrum (𝓞 E))) (X : UpperTheory.Gal.UnramifiedFromSplittingCriterion.Fld E Ω) : Prop :=
  ∃ (P : CuspSub X.K a) (χ' : HChar (maximalRealSubfield X.K)),
    UpperTheory.Gal.InertialTypesAlt.Lifts (UpperTheory.Gal.InertialTypesAlt.Pt.base Ω π) ({ K := X.K, π := P } : UpperTheory.Gal.InertialTypesAlt.Pt E Ω a) ∧ InScope .all l P χ' ∧
    (∀ (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l)), Weak π ι r → Weak P ι (r.comp (UpperTheory.V.Af.Bc.res E Ω X.K))) ∧
    ∀ u ∉ S, ∀ A : ValuationSubring Ω, IsPlaceOver A u → (∀ g ∈ Dec (F := E) A, UpperTheory.Gal.UnramifiedFromSplittingCriterion.Fixes (F := E) X.K g) →
      ∀ w' : HeightOneSpectrum (𝓞 X.K), IsPlaceOver A w' → ∃ B, (CG.mk P).HasSat w' B

theorem UpperTheory.Gal.NearKilling.allLift :
    StepLift → UpperTheory.Gal.UnramifiedFromSplittingCriterion.SatSplit → AllLift := by
  intro hStep hSat E Ω _ _ _ _ _ _ l a _ ha π χ hχ S hS X hX
  suffices H : Carry l a π S X by
    obtain ⟨P, χ', h1, h2, h3, -⟩ := H
    exact ⟨P, χ', h1, h2, h3⟩
  refine UpperTheory.Gal.UnramifiedFromSplittingCriterion.Tower.induction (S := S) (P := Carry l a π S) ?_ ?_ hX
  · refine ⟨π, χ, Relation.ReflTransGen.refl, hχ, fun ι r h => ?_, fun u hu A hA _ w' hw' => ?_⟩
    · exact h
    · have e : w' = u := HeightOneSpectrum.ext (Ideal.ext fun x => (hw' x).symm.trans (hA x))
      rw [e]
      exact hS u hu
  · rintro X Y - ⟨alg, t1, t2, hG, hp, u, hu, hsp, A, hA, τ, hτ, hτn⟩ ⟨P, χ', h1, h2, h3, h4⟩
    obtain ⟨v, hv, -⟩ := GlobalTheory.AboveL.exists_isPlaceOver_of_tower E X.K Ω A u hA
    have hfix : ∀ g ∈ Dec (F := E) A, UpperTheory.Gal.UnramifiedFromSplittingCriterion.Fixes (F := E) X.K g := fun g hg =>
      (hsp A hA (AlgEquiv.restrictScalars _ g) (dec_restrict hg)).2
    obtain ⟨P', χ'', hbc, hsl, hsc, -, hweak⟩ :=
      hStep X.K Y.K Ω hp l a ha P χ' h2 A v hv ⟨τ, hτ, hτn⟩ (h4 u hu A hA hfix v hv)
    refine ⟨P', χ'', Relation.ReflTransGen.tail h1 ⟨alg, t2, hG, hp, hbc⟩, hsc, fun ι r h => ?_, ?_⟩
    · exact hweak ι (r.comp (UpperTheory.V.Af.Bc.res E Ω X.K)) (h3 ι r h)
    · intro u' hu' A' hA' hfix' w' hw'
      have hv' : IsPlaceOver A' (w'.under (𝓞 X.K)) := fun x => by
        rw [IsScalarTower.algebraMap_apply X.K Y.K Ω]
        exact hw' (algebraMap (𝓞 X.K) (𝓞 Y.K) x)
      have hfixX : ∀ g ∈ Dec (F := E) A', UpperTheory.Gal.UnramifiedFromSplittingCriterion.Fixes (F := E) X.K g := fun g hg x => by
        have := hfix' g hg (algebraMap X.K Y.K x)
        rwa [← IsScalarTower.algebraMap_apply] at this
      obtain ⟨B, hB⟩ := h4 u' hu' A' hA' hfixX _ hv'
      exact ⟨B, hSat X.K Y.K Ω A' _ w' hv' hw' (fun g hg => hfix' _ (dec_restrict hg)) a P P' hsl B hB⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CharpolyFromTrace.IneNorm
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open scoped Pointwise
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel UpperTheory.Gal.TypesAndIwahori GlobalTheory.Cong UpperTheory.Gal.NearKilling

section
variable {E M Ω : Type} [Field E] [NumberField E] [Field M] [NumberField M] [Field Ω] [Algebra E M] [Algebra E Ω] [Algebra M Ω] [IsScalarTower E M Ω]

private theorem res_mem_Ine_iff (A : ValuationSubring Ω) (σ : G M Ω) :
    (AlgEquiv.restrictScalarsHom E σ : G E Ω) ∈ Ine (F := E) A ↔ σ ∈ Ine (F := M) A := (Iff.rfl)

end

theorem UpperTheory.Gal.NearKilling.ineNorm :
    IneNorm := by
  intro E M Ω _ _ _ _ _ _ _ _ _ _ _ A v w _ h h' hfix art art' ha ha'
  have hl : ∀ s : Ine (F := E) A, ∃ t : G M Ω, AlgEquiv.restrictScalarsHom E t = (s : G E Ω) := by
    intro s
    exact ⟨{ (s : G E Ω) with commutes' := fun x => hfix s s.2 x }, by ext x; rfl⟩
  have hr : ∀ t : Ine (F := M) A, (AlgEquiv.restrictScalarsHom E (t : G M Ω) : G E Ω) ∈ Ine (F := E) A :=
    fun t => (res_mem_Ine_iff (E := E) (M := M) A (t : G M Ω)).2 t.2
  obtain ⟨r, hrv⟩ : ∃ r : Ine (F := M) A →* Ine (F := E) A,
      ∀ t, (r t : G E Ω) = AlgEquiv.restrictScalarsHom E (t : G M Ω) :=
    ⟨MonoidHom.codRestrict ((AlgEquiv.restrictScalarsHom E).comp (Ine (F := M) A).subtype)
      (Ine (F := E) A) hr, fun t => rfl⟩
  have hbij : Function.Bijective r := by
    constructor
    · intro a b hab
      apply Subtype.ext
      ext x
      have hab' := congrArg Subtype.val hab
      rw [hrv, hrv] at hab'
      exact DFunLike.congr_fun hab' x
    · intro s
      obtain ⟨t, ht⟩ := hl s
      have htm : t ∈ Ine (F := M) A := (res_mem_Ine_iff (E := E) (M := M) A t).1 (ht ▸ s.2)
      exact ⟨⟨t, htm⟩, Subtype.ext ((hrv _).trans ht)⟩
  obtain ⟨e, he⟩ : ∃ e : Ine (F := E) A ≃* Ine (F := M) A, ∀ s, r (e s) = s :=
    ⟨(MulEquiv.ofBijective r hbij).symm, fun s => (MulEquiv.ofBijective r hbij).apply_symm_apply s⟩
  have key : ∀ s, (AlgEquiv.restrictScalarsHom E ((e s : Ine (F := M) A) : G M Ω) : G E Ω) = s := by
    intro s
    rw [← hrv, he]
  refine ⟨e, key, fun s => ?_⟩
  exact GlobalTheory.ArtinNormU.localArtin_normU E M Ω A v w h h' art art' ha ha' _ _
    (fun z => (DFunLike.congr_fun (key s) z).symm)
end

noncomputable section

open GlobalTheory.GalCut GlobalTheory.Cong UpperTheory.Gal.UnramifiedFromSplittingCriterion

namespace UpperTheory.Gal.NearKilling

theorem stepLift_holds : StepLift :=
  stepLift UpperTheory.ConvolutionTheory.cbcc noSelfTwist_holds
    (polBC PositivityTheory.AdelicQuotientData.jacquetShalikaRigidity
      (PositivityTheory.JMult1.gelfandKazhdanDual_of_rigidity PositivityTheory.AdelicQuotientData.jacquetShalikaRigidity PositivityTheory.S2.CuspBdd.cuspFormsBoundedGL)) weakRes

theorem allLift_holds : AllLift := allLift stepLift_holds satSplit_holds

end UpperTheory.Gal.NearKilling
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteOrderTwists
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RoadU.FinTwist

open GlobalTheory.ContraPair GlobalTheory.HeightCounting.Blocks

end GlobalTheory.RoadU.FinTwist

namespace GlobalTheory.RoadU.FinTwist

open GlobalTheory.ContraPair GlobalTheory.HeightCounting.Blocks

theorem isAlg_zero {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] {κ : HChar K} {m : ℕ} (hm : 0 < m)
    (h : κ ^ m = 1) : κ.IsAlg 0 := fun k => isAlgPos_zero_of_orderDvd hm h k fun φ => by
  have h := IsTotallyComplex.complexEmbedding_not_isReal (Complex.ofRealHom.comp φ)
  refine absurd ?_ h
  rw [ComplexEmbedding.isReal_iff]
  ext x
  simp

theorem infChar_twist {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] {n : ℕ} (P : CuspSub K n) {κ : HChar K}
    (hκ : κ.IsAlg 0) (τ : K →+* ℂ) : (CG.mk (P.twist κ)).infChar τ = (CG.mk P).infChar τ := by
  have e := ((ParLaws.hasInfChar_infChar (CG.mk P) τ).twist κ).infChar_eq
  rw [CG.twist_mk] at e
  rw [e, (InfType.expo_of_infType K κ).1 0 hκ τ]
  simp

end GlobalTheory.RoadU.FinTwist
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlainTorOfMono0
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.PlainMono

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem linked_single {ρ ρ' : IrrGL (k := k)} (hρ : ρ.IsCusp) (hρ' : ρ'.IsCusp) (hne : ρ ≠ ρ.nu 1) (e : ρ' = ρ.nu 1) :
    (Segment.single ρ hρ).Linked (Segment.single ρ' hρ') := _root_.UpperTheory.Gal.projectedFormsSystemPart.Pm.linked_single (ρ := ρ) (ρ' := ρ') hρ hρ' hne e

theorem eq_single_of_len {Δ : Segment k} (h : Δ.len = 1) : Δ = Segment.single Δ.first Δ.isCusp_first :=
  Segment.ext_first (by simp [Segment.single]) (by simp [Segment.single, h])

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem ne_nu_one {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a}
    {rc : IrrGL (k := w.adicCompletion E) → WD h} (L : UpperTheory.Zero.LLC.LawsT a ha rc) {ρ : IrrGL (k := w.adicCompletion E)}
    (hρ : ρ.IsCusp) : ρ ≠ ρ.nu 1 := by
  intro e0
  refine WD.lpTw_one_ne (rc ρ) (by rw [L.dim]; exact hρ.1) ?_
  calc (rc ρ).lpTw 1 = rc (ρ.nu ((1 : ℝ) : ℂ)) := (L.nu ρ 1).symm
    _ = rc ρ := by rw [Complex.ofReal_one, ← e0]

end GlobalTheory.PlainMono
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.PAdicSplitting.InfLifts
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL GlobalTheory.DeRhamOfPlainTorus ValuativeRel
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.ToralGalois.R2

def MixedOf : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (n : ℕ) (π : CuspSub E n)
    (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin n) (w.adicCompletion E))), π.IsLocComp w σ →
    fixed σ.ρ (KOne (w.adicCompletion E) (Fin n)) ≠ ⊥ → Apart (algNorm σ) →
    ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (rc : IrrGL (k := w.adicCompletion E) → WD h), UpperTheory.Zero.LLC.IsRecT h rc →
      (rc (algNorm σ)).mono0 → UpperTheory.Gal.InertialTypesAlt.Mixed (IrrGL.of σ.ρ σ.smooth σ.irred)

def InfStep : Prop :=
  ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M] [_root_.NumberField.IsTotallyComplex K]
    [_root_.NumberField.IsTotallyComplex M], (Module.finrank K M).Prime → ∀ n : ℕ, 0 < n → ∀ (π : CuspSub K n) (P : CuspSub M n),
    UpperTheory.V.Published.WeakBC (UpperTheory.CBC.Cusp.cx π).sat (UpperTheory.CBC.Cusp.cx P).sat →
    ∀ τ : M →+* ℂ, (CG.mk P).infChar τ = (CG.mk π).infChar (τ.comp (algebraMap K M))

def InfLifts : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (n : ℕ), 0 < n →
    ∀ (π : CuspSub E n) (Y : UpperTheory.Gal.InertialTypesAlt.Pt E Ω n), UpperTheory.Gal.InertialTypesAlt.Lifts (UpperTheory.Gal.InertialTypesAlt.Pt.base Ω π) Y →
    ∀ τ : Y.K →+* ℂ, (CG.mk Y.π).infChar τ = (CG.mk π).infChar (τ.comp (algebraMap E Y.K))

def RecChars : Prop :=
  ∀ (M Ω : Type) [Field M] [NumberField M] [Field Ω] [Algebra M Ω] [IsAlgClosure M Ω] (A : ValuationSubring Ω)
    (u : HeightOneSpectrum (𝓞 M)) (h : IsPlaceOver A u) (n : ℕ) (T : SmIrr (GL (Fin n) (u.adicCompletion M)))
    (ξ : Fin n → ((u.adicCompletion M)ˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)), HasSupport T.ρ (chars ξ hξ) →
    (GlobalTheory.RoadU.Unlinked (chars ξ hξ) → PlainTor (algNorm T)) ∧
    ∀ rc : IrrGL (k := u.adicCompletion M) → WD h, UpperTheory.Zero.LLC.IsRecT h rc → ∀ a, IsLocalArtin h a → ∀ t : Ine (F := M) A,
      (rc (algNorm T)).charPol (ineIncl h t) = ∏ j, (X - C ((ξ j (a (ineIncl h t)) : ℂˣ) : ℂ))

def ToTor : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ (π : CuspSub E n) (χ : HChar (maximalRealSubfield E)),
    InScope .all l π χ → ∀ r : G E Ω →* GL (Fin n) (Qbar l), Weak π ι r →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin n) (w.adicCompletion E))), π.IsLocComp w σ → IsQg w →
      UpperTheory.Gal.InertialTypesAlt.Mixed (IrrGL.of σ.ρ σ.smooth σ.irred) →
    ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (rc : IrrGL (k := w.adicCompletion E) → WD h), UpperTheory.Zero.LLC.IsRecT h rc →
    ∃ (X : UpperTheory.Gal.UnramifiedFromSplittingCriterion.Fld E Ω) (P : CuspSub X.K n) (χ' : HChar (maximalRealSubfield X.K)) (u : HeightOneSpectrum (𝓞 X.K))
      (h' : IsPlaceOver A u) (T : SmIrr (GL (Fin n) (u.adicCompletion X.K))) (rc' : IrrGL (k := u.adicCompletion X.K) → WD h'),
      InScope .all l P χ' ∧ Weak P ι (resTo X.K r) ∧
      (∀ τ : X.K →+* ℂ, (CG.mk P).infChar τ = (CG.mk π).infChar (τ.comp (algebraMap E X.K))) ∧
      P.IsLocComp u T ∧ PlainTor (algNorm T) ∧ UpperTheory.Zero.LLC.IsRecT h' rc' ∧
      ∀ t : Ine (F := E) A, ∃ t' : Ine (F := X.K) A, (∀ z : Ω, (t : G E Ω) z = (t' : G X.K Ω) z) ∧
        (rc' (algNorm T)).charPol (ineIncl h' t') = (rc (algNorm σ)).charPol (ineIncl h t)

def DRDesc : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ) (π : CuspSub E n) (r : G E Ω →* GL (Fin n) (Qbar l)), Continuous r →
    ∀ w : HeightOneSpectrum (𝓞 E), (∀ A : ValuationSubring Ω, IsPlaceOver A w →
      ∃ (X : UpperTheory.Gal.UnramifiedFromSplittingCriterion.Fld E Ω) (P : CuspSub X.K n) (u : HeightOneSpectrum (𝓞 X.K)), IsPlaceOver A u ∧
        (∀ τ : X.K →+* ℂ, (CG.mk P).infChar τ = (CG.mk π).infChar (τ.comp (algebraMap E X.K))) ∧
        ClauseAt .dR P ι (resTo X.K r) u) → ClauseAt .dR π ι r w

end UpperTheory.Gal.ToralGalois.R2
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.PAdicSplitting.PInfStep
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL GlobalTheory.DeRhamOfPlainTorus ValuativeRel
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.ToralGalois.R2

theorem UpperTheory.Gal.ToralGalois.R2.infStep :
    UpperTheory.Gal.InertialTypesAlt.StableOf → InfStep := by
  intro hS K M _ _ _ _ _ _ _ _ hp n hn π P hw τ
  obtain ⟨hconj, -⟩ := hS K M hp n hn π P hw
  have hK : IsTotallyComplex K := inferInstance
  obtain ⟨-, hD, hF⟩ := UpperTheory.ConvolutionTheory.cbcc K M hp hK n hn
  obtain ⟨Q, hQw, hQinf, -⟩ := hD (.cx P) hconj
  cases Q with
  | re Q => exact (PositivityTheory.Pf1.CLGD.K.LKW.not_real_complex K inferInstance hK).elim
  | cx π₁ =>
    obtain ⟨η, hη, hi⟩ := (hF (.cx π) (.cx P) hconj hw).2 (.cx π₁) hQw
    have hP := GlobalTheory.CuspRep.ParLaws.hasInfChar_infChar (CG.mk P) τ
    have h2 : π₁.HasInfChar (τ.comp (algebraMap K M)) ((CG.mk P).infChar τ) := hQinf τ _ hP
    have h3 : (CG.mk π₁).infChar (τ.comp (algebraMap K M)) = (CG.mk P).infChar τ :=
      CG.HasInfChar.infChar_eq h2
    have h4 : CG.mk (π.twist η) = CG.mk π₁ := Quotient.sound hi
    have h5 : (CG.mk (π.twist η)).infChar (τ.comp (algebraMap K M)) =
        (CG.mk π).infChar (τ.comp (algebraMap K M)) := by
      rcases hη with rfl | hη
      · exact GlobalTheory.RoadU.FinTwist.infChar_twist π
          (GlobalTheory.RoadU.FinTwist.isAlg_zero (m := 1) one_pos (pow_one _)) _
      · exact GlobalTheory.RoadU.FinTwist.infChar_twist π
          (GlobalTheory.RoadU.FinTwist.isAlg_zero hp.pos hη.2.1) _
    rw [← h3, ← h4, h5]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.PAdicSplitting.PMixedOf
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL GlobalTheory.DeRhamOfPlainTorus ValuativeRel
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.ToralGalois.R2

namespace UpperTheory.Gal.ToralGalois.R2

private theorem fixed_ne_bot {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (φ : ρ.Equiv σ) {H : Subgroup G} (h : fixed ρ H ≠ ⊥) : fixed σ H ≠ ⊥ := by
  obtain ⟨v, hv, h0⟩ := (Submodule.ne_bot_iff _).1 h
  refine (Submodule.ne_bot_iff _).2 ⟨φ.toIntertwiningMap v, GlobalTheory.Parabolic.mem_fixed.2 fun g hg => ?_, fun e => h0 ?_⟩
  · rw [← φ.toIntertwiningMap.isIntertwining, GlobalTheory.Parabolic.mem_fixed.1 hv g hg]
  · exact φ.toLinearEquiv.injective (e.trans (map_zero φ.toLinearEquiv).symm)

private theorem pairwise_of_map {α β : Type*} (f : α → β) {r : β → β → Prop} (hr : Symmetric r) (t : Multiset α)
    (h : (t.map f).Pairwise r) : t.Pairwise fun a b => r (f a) (f b) := by
  induction t using Quot.inductionOn with
  | h l =>
    have h' : Multiset.Pairwise r ((l.map f : List β) : Multiset β) := h
    haveI : Std.Symm r := ⟨fun _ _ e => hr e⟩
    rw [Multiset.pairwise_coe_iff_pairwise, List.pairwise_map] at h'
    exact ⟨l, rfl, h'⟩

private theorem apart_of_nu {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {s : Multiset (IrrGL (k := k))} (c : ℂ)
    (h : ((s.map fun y => y.nu c).filter fun y => 2 ≤ y.1).Pairwise fun y z => ¬ y.Inert z) :
    (s.filter fun y => 2 ≤ y.1).Pairwise fun y z => ¬ y.Inert z := by
  rw [Multiset.filter_map] at h
  have hsym : Symmetric fun y z : IrrGL (k := k) => ¬ y.Inert z :=
    fun y z hyz e => hyz (IrrGL.inert_equivalence.symm e)
  obtain ⟨l, hl, hp⟩ := pairwise_of_map (t := s.filter fun y => 2 ≤ y.1) (fun y => y.nu c) hsym (by convert h using 3; exact Iff.rfl)
  refine ⟨l, hl, hp.imp fun {y z} hyz e => hyz ?_⟩
  exact IrrGL.inert_equivalence.trans (IrrGL.inert_equivalence.symm (IrrGL.inert_nu y c))
      (IrrGL.inert_equivalence.trans e (IrrGL.inert_nu z c))

end UpperTheory.Gal.ToralGalois.R2

open GlobalTheory.PlainMono in
theorem UpperTheory.Gal.ToralGalois.R2.mixedOf :
    MixedOf := by
  intro E Ω _ _ _ _ _ _ n π w σ hσ hfix hap A h rc hrc hm
  obtain ⟨a, ha, L⟩ := hrc
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  have hg : IsGeneric σ.ρ := GlobalTheory.CuspRep.Generic.isGeneric_of_isLocComp E n π w σ hσ
  have hnu : ∀ (z : IrrGL (k := w.adicCompletion E)) (s : ℂ), IsGeneric z.rep → IsGeneric (z.nu s).rep :=
    fun z s hz => (isGeneric_congr (IrrGL.twEquiv z _ _)).1 ((isGeneric_twist_iff _).2 hz)
  have hgτ : IsGeneric (algNorm σ).rep :=
    hnu _ _ ((isGeneric_congr (IrrGL.equivOf σ.ρ σ.smooth σ.irred)).1 hg)
  obtain ⟨c, Δ, y, hd, hun, hL, ⟨e⟩⟩ := GlobalTheory.genericUnlinkedGL_outright (w.adicCompletion E) (algNorm σ).1 _
    (algNorm σ).rep (algNorm σ).2.rep.smooth (algNorm σ).2.rep.irr hgτ
  have hIsL : IsL ((List.ofFn Δ : List (Segment (w.adicCompletion E))) : Multiset (Segment (w.adicCompletion E)))
      (algNorm σ).rep :=
    ⟨c, y, hd, ⟨Δ, ⟨Fin.univ_val_map Δ, fun i j hij hp => hun i j hij.ne hp.1⟩, hL⟩,
      (isCosocle_self (algNorm σ).2.rep.irr).of_equiv (.refl _) e⟩
  have hm' := hm
  rw [L.langlands (List.ofFn Δ) (algNorm σ) hIsL, segSum] at hm'
  have hlen : ∀ i, (Δ i).len = 1 := by
    intro i
    have hmi := GlobalTheory.UnlinkedMono.noMonodromy_of_mem_weilDeligneListSum _ hm' _
      (List.mem_map.2 ⟨Δ i, List.mem_ofFn.2 ⟨i, rfl⟩, rfl⟩)
    by_contra hne
    have hirr : IsIrrWD ((rc (Δ i).first).lpTw ((((Δ i).len : ℝ) - 1) / 2)) := by
      rw [← L.nu]; exact L.cusp _ ((Δ i).isCusp_first.nu _)
    exact GlobalTheory.SegLen.not_mono0_lpChar_lpSp hirr (by have := (Δ i).len_pos; omega) hmi
  obtain ⟨𝔪, h𝔪⟩ := UpperTheory.Zero.LLC.Pr.exh (w.adicCompletion E) (IrrGL.of σ.ρ σ.smooth σ.irred)
  obtain ⟨s, hs⟩ : ∃ s, HasSupport (IrrGL.of σ.ρ σ.smooth σ.irred).rep s :=
    ⟨_, GlobalTheory.LocGL.hasSupport_msupp_of_isL UpperTheory.Zero.LLC.Pr.zel _ 𝔪 _ h𝔪⟩
  have hs' := GlobalTheory.LocGL.SupportRing.hasSupport_nu hs (((1 - (n : ℝ)) / 2 : ℝ) : ℂ)
  have hms := GlobalTheory.LocGL.ZelevinskyExpansion.msupp_eq_of_isL (algNorm σ).2.rep.irr hIsL hs'
  have mem : ∀ u ∈ s, ∃ i, (Δ i).first = u.nu (((1 - (n : ℝ)) / 2 : ℝ) : ℂ) := by
    intro u hu
    have hu' : u.nu (((1 - (n : ℝ)) / 2 : ℝ) : ℂ) ∈ msupp ((List.ofFn Δ : List (Segment (w.adicCompletion E))) :
        Multiset (Segment (w.adicCompletion E))) := by
      rw [hms]; exact Multiset.mem_map_of_mem _ hu
    rw [msupp, Multiset.mem_bind] at hu'
    obtain ⟨D, hD, hu''⟩ := hu'
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 (Multiset.mem_coe.1 hD)
    rw [Segment.mem_ms, Segment.mem_carrier] at hu''
    obtain ⟨m, hm1, e'⟩ := hu''
    have : m = 0 := by have := hlen i; omega
    subst this
    exact ⟨i, by simpa using e'⟩
  refine ⟨fixed_ne_bot (IrrGL.equivOf σ.ρ σ.smooth σ.irred) hfix, s, hs, ?_, apart_of_nu _ (hap _ hs')⟩
  intro y1 hy1 z1 hz1 hyz
  obtain ⟨i, hi⟩ := mem y1 hy1
  obtain ⟨j, hj⟩ := mem z1 hz1
  have key : (Δ i).first = (Δ j).first.nu 1 := by
    rw [hi, hj, hyz, IrrGL.nu_nu, IrrGL.nu_nu, add_comm]
  have hne := ne_nu_one L (Δ j).isCusp_first
  by_cases hij : i = j
  · subst hij; exact hne key
  · refine hun j i (Ne.symm hij) ?_
    rw [eq_single_of_len (hlen j), eq_single_of_len (hlen i)]
    exact linked_single _ _ hne key
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.PAdicSplitting.R2g
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL GlobalTheory.DeRhamOfPlainTorus ValuativeRel
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.ToralGalois.R2

theorem UpperTheory.Gal.ToralGalois.R2.r2g :
    MixedOf → ToTor → DRDesc → UpperTheory.Zero.LLC.RecTExists → GlobalTheory.DeRhamOfPlainTorus.R1 → LocalGlobalCompatAtIwahoriFixedPlaces := by
  intro hMix hTor hDR hRec hR1 E Ω _ _ _ _ _ _ l _ ι n hn π χ hπ r hr w σ hσ hfix hcase A h rc hrc hm0
  rcases hcase with hpt | ⟨hQ, hap⟩
  · obtain ⟨haway, habove⟩ := hR1 E Ω l ι n hn π χ hπ r hr w σ hσ hpt
    refine ⟨fun hl => ?_, fun hl => ?_⟩
    · obtain ⟨hm, he⟩ := haway hl A h
      exact ⟨hm, fun t => by rw [he rc hrc]⟩
    · obtain ⟨hd, hb⟩ := habove hl
      refine ⟨hd, fun Q AI hT O _ _ _ Bw hj => ?_⟩
      obtain ⟨h1, h2, h3⟩ := hb Q AI hT A h O Bw hj
      exact ⟨h1, h2, fun t => h3 rc hrc _⟩
  · have hmix := hMix E Ω n π w σ hσ hfix hap A h rc hrc hm0
    obtain ⟨X, P, χ', u, h', T, rc', hP, hW, hinf, hTc, hPT, hrc', hine⟩ :=
      hTor E Ω l ι n hn π χ hπ r hr w σ hσ hQ hmix A h rc hrc
    obtain ⟨haway, habove⟩ := hR1 X.K Ω l ι n hn P χ' hP (resTo X.K r) hW u T hTc hPT
    refine ⟨fun hl => ?_, fun hl => ?_⟩
    · have hl' : ((l : ℕ) : 𝓞 X.K) ∉ u.asIdeal := by
        intro hm
        apply hl
        rw [← h]
        rw [← h'] at hm
        simpa using hm
      obtain ⟨hm', he⟩ := haway hl' A h'
      have hres := GlobalTheory.AboveL.wdOf_restricts E X.K Ω A w u h h' l ι n r hl hl' hr.1
      obtain ⟨-, hmono, hcp⟩ := GlobalTheory.AboveL.restricts_lpDim_mono0_charPol E X.K Ω A w u h h' _ _ hres
      refine ⟨hmono.mp hm', fun t => ?_⟩
      obtain ⟨t', hz, hc⟩ := hine t
      rw [← hcp (ineIncl h t) (ineIncl h' t') (fun z => by simpa [coe_ineIncl] using hz z), he rc' hrc', hc]
    · have hl' : ((l : ℕ) : 𝓞 X.K) ∈ u.asIdeal := by
        rw [← h] at hl
        rw [← h']
        simpa using hl
      obtain ⟨-, hb⟩ := habove hl'
      refine ⟨?_, fun Q AI hT O _ _ _ Bw hj => ?_⟩
      · refine hDR E Ω l ι n π r hr.1 w fun A' hA' => ?_
        obtain ⟨rc₁, hrc₁⟩ := hRec E Ω A' w hA'
        obtain ⟨X₁, P₁, χ₁, u₁, h₁, T₁, rc₁', hP₁, hW₁, hinf₁, hTc₁, hPT₁, -, -⟩ :=
          hTor E Ω l ι n hn π χ hπ r hr w σ hσ hQ hmix A' hA' rc₁ hrc₁
        have hl₁ : ((l : ℕ) : 𝓞 X₁.K) ∈ u₁.asIdeal := by
          rw [← hA'] at hl
          rw [← h₁]
          simpa using hl
        exact ⟨X₁, P₁, u₁, h₁, hinf₁,
          ((hR1 X₁.K Ω l ι n hn P₁ χ₁ hP₁ (resTo X₁.K r) hW₁ u₁ T₁ hTc₁ hPT₁).2 hl₁).1⟩
      · obtain ⟨LL₀, Bw₀, hjj₀, -, -⟩ := GlobalTheory.AboveLRes.exists_bridge (L := X.K) Bw hj Bw.LL
        have hj₀ : GlobalTheory.Pst.Induces Bw₀ := fun x => by rw [hjj₀]; exact hj x
        have hp₀ := (hb Q AI hT A h' _ Bw₀ hj₀).1
        have hpst : IsPstAt Q Bw (r.comp (Dec (F := E) A).subtype) :=
          GlobalTheory.AboveLRes.isPstAt_of_resTo E X.K Ω A l Q AI hT n r hr.1 O _ Bw Bw₀ hj hj₀ hp₀
        obtain ⟨O', _, _, _, Bw', hj', -, hres⟩ :=
          GlobalTheory.AboveLRes.wdAt_resTo E X.K Ω A w u h h' l ι Q AI hT n r O Bw hj hpst
        obtain ⟨-, hmono, hcp⟩ := GlobalTheory.AboveL.restricts_lpDim_mono0_charPol E X.K Ω A w u h h' _ _ hres
        obtain ⟨-, hm', hc'⟩ := hb Q AI hT A h' O' Bw' hj'
        refine ⟨hpst, hmono.mp hm', fun t => ?_⟩
        obtain ⟨t', hz, hc⟩ := hine t
        rw [← hcp (ineIncl h t) (ineIncl h' t') (fun z => by simpa [coe_ineIncl] using hz z), hc' rc' hrc', hc]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.PAdicSplitting.PToTor
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL GlobalTheory.DeRhamOfPlainTorus ValuativeRel
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.ToralGalois.R2 GlobalTheory.UnitaryBC UpperTheory.Gal.TypesAndIwahori GlobalTheory.Cong UpperTheory.Gal.NearKilling

private theorem split_of_padic {E : Type} [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E))
    (g : ℕ) [Fact g.Prime] (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i) : normV w = g ∧ IsSplitAt w := by
  have hq : normV w = g := DiscreteGroups.sglob.DzType.normV_eq_of_padic w g i hi
  refine ⟨hq, GlobalTheory.DenseInvFrob.isSplitAt_of_inertiaDeg_eq_one w ?_ ?_⟩
  · have hp : (Ideal.absNorm w.asIdeal).Prime := by
      have : Ideal.absNorm w.asIdeal = g := by
        simpa only [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using hq
      rw [this]
      exact Fact.out
    exact ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified E).1 w).1 hp
  · have hmem : ((g : ℕ) : 𝓞 E) ∈ w.asIdeal := by
      apply DiscreteGroups.sglob.DzType.mem_of_val_lt_one w
      have := DiscreteGroups.sglob.DzType.val_lt_one_of_norm_lt_one w g i hi (g : ℚ_[g]) Padic.norm_p_lt_one
      rw [map_natCast] at this
      rw [DiscreteGroups.sglob.DzType.alg_natCast]
      exact this
    have hsq := DiscreteGroups.sglob.DzType.g_not_mem_sq w g i hi
    have hl : g.Prime := Fact.out
    have hp : Prime (g : ℤ) := Nat.prime_iff_prime_int.mp hl
    have hmax : (Ideal.span {(g : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
    have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(g : ℤ)}) = Ideal.span {((g : ℕ) : 𝓞 E)} := by
      rw [Ideal.map_span]; simp
    have hle : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(g : ℤ)}) ≤ w.asIdeal := by
      rw [hmap, Ideal.span_le]; simpa using hmem
    have := w.isPrime
    have : w.asIdeal.LiesOver (Ideal.span {(g : ℤ)}) :=
      ⟨hmax.eq_of_le (Ideal.comap_ne_top _ w.isPrime.ne_top) (Ideal.map_le_iff_le_comap.mp hle)⟩
    have hb : Ideal.span {(g : ℤ)} ≠ ⊥ := by simpa using hl.ne_zero
    rw [← Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(g : ℤ)}) w.asIdeal hb]
    by_contra hne
    rw [← ne_eq, Ideal.ramificationIdx'_ne_one_iff hle, hmap, Ideal.span_le] at hne
    exact hsq (by simpa using hne)

private theorem dvd_of_support {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin N) k) V) (s : Multiset (IrrGL (k := k)))
    (hs : HasSupport ρ s) (y : IrrGL (k := k)) (hy : y ∈ s) : y.1 ∣ N.factorial := by
  have h1 : 0 < y.1 := (hs.isCusp hy).1
  have h2 := hs.sum_fst
  have h3 : y.1 ≤ (s.map Sigma.fst).sum := Multiset.single_le_sum (by simp) _ (Multiset.mem_map_of_mem _ hy)
  rw [h2, Fintype.card_fin] at h3
  exact Nat.dvd_factorial h1 h3

theorem UpperTheory.Gal.ToralGalois.R2.toTor :
    UpperTheory.Gal.InertialTypesAlt.SuppBC → UpperTheory.Gal.NearKilling.UnrField → UpperTheory.Gal.NearKilling.AllLift → UpperTheory.Gal.NearKilling.IneNorm → InfLifts → RecChars → UpperTheory.Zero.LLC.RecTExists → ToTor := by
  intro hSupp hUnr hLift hIne hInf hChars hRec E Ω _ _ _ _ _ _ l _ ι n hn π χ hs r hr w σ hσ hQ hM A h rc hrc
  obtain ⟨p, hp, i, hi⟩ := hQ
  haveI := hp
  obtain ⟨hq, hsp⟩ := split_of_padic w p i hi
  have hf : 0 < n.factorial := Nat.factorial_pos n
  have hSfin : {u : HeightOneSpectrum (𝓞 E) | ¬ ∃ B, (CG.mk π).HasSat u B}.Finite := by
    have h := Filter.eventually_cofinite.1
      (GlobalTheory.CuspRep.UnrSat.eventually_hasSatGL_locRep GlobalTheory.automorphicFormsFiniteGL E n π)
    simpa only [CG.hasSat_mk] using h
  obtain ⟨Xf, hXT, hXw, -⟩ := hUnr E Ω w hsp _ hf _ hSfin
  obtain ⟨P, χ', hPL, hPs, hPr⟩ := hLift E Ω l n hn π χ hs _ (fun u hu => not_not.1 hu) Xf hXT
  obtain ⟨w', h', -⟩ := GlobalTheory.AboveL.exists_isPlaceOver_of_tower E Xf.K Ω A w h
  haveI : w'.asIdeal.LiesOver w.asIdeal := ⟨(GlobalTheory.AboveL.comap_eq_of_placeOver h h').symm⟩
  have hXfix := (hXw A h).1
  have hnorm := (hXw A h).2 w' h'
  obtain ⟨σ', hσ', -⟩ := LocEx.exists_isLocComp GlobalTheory.automorphicFormsFiniteGL Xf.K n P w'
  obtain ⟨art, hart⟩ := GlobalTheory.localArtinExists_holds E Ω A w h
  obtain ⟨art', hart'⟩ := GlobalTheory.localArtinExists_holds Xf.K Ω A w' h'
  obtain ⟨g, hg1, -⟩ := hIne E Xf.K Ω A w w' h h' hXfix art art' hart hart'
  obtain ⟨ξ, hξ, hT, hU⟩ := hSupp E Ω n hn π { K := Xf.K, π := P } hPL A w w' h h' p i hi hXfix σ σ' hσ hσ' hM.1 n.factorial
    (by rw [hnorm, hq]) (fun s hs y hy => dvd_of_support _ s hs y hy)
  obtain ⟨-, hTS, hTP⟩ := id hT
  obtain ⟨rc', hrc'⟩ := hRec Xf.K Ω A w' h'
  have hCh := hChars Xf.K Ω A w' h' n σ' ξ hξ hTS
  have hB : ∀ s : ↥(Ine (F := E) A), (rc (IrrGL.of σ.ρ σ.smooth σ.irred)).inePol (s : G E Ω) =
      ∏ j, (X - C ((ξ j (art' (ineIncl h' (g s))) : ℂˣ) : ℂ)) := fun s => by
    have := hTP rc hrc art' hart' (g s)
    rwa [show AlgEquiv.restrictScalars E ((g s : ↥(Ine (F := Xf.K) A)) : G Xf.K Ω) = (s : G E Ω) from hg1 s] at this
  refine ⟨Xf, P, χ', w', h', σ', rc', hPs, hPr ι r hr, hInf E Ω n hn π { K := Xf.K, π := P } hPL, hσ', hCh.1 (hU hM), hrc',
    fun t => ⟨g t, fun z => ?_, ?_⟩⟩
  · exact (DFunLike.congr_fun (hg1 t) z).symm
  · rw [hCh.2 rc' hrc' art' hart' (g t)]
    obtain ⟨a₀, ha₀, L⟩ := hrc
    have e1 : (rc (algNorm σ)).charPol (ineIncl h t) = (rc (algNorm σ)).inePol (t : G E Ω) :=
      (WD.inePol_of_mem_Ine _ t.2).symm
    have e2 : algNorm σ = (IrrGL.of σ.ρ σ.smooth σ.irred).nu (((1 - ((n : ℕ) : ℝ)) / 2 : ℝ) : ℂ) := rfl
    rw [e1, e2, L.nu, GlobalTheory.RoadU.DepthZeroRec.inePol_lpTw_of_mem_Ine _ _ t.2, hB t]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.PAdicSplitting.PRecChars
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL GlobalTheory.DeRhamOfPlainTorus ValuativeRel
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.ToralGalois.R2

theorem UpperTheory.Gal.ToralGalois.R2.recChars :
    UpperTheory.Gal.InertialTypesAlt.SuppIne → RecChars := by
  intro hSI M Ω _ _ _ _ _ A u h n T ξ hξ hsup
  haveI : CharZero (u.adicCompletion M) := charZero_of_injective_algebraMap (algebraMap M _).injective
  have hsupx : HasSupport (IrrGL.of T.ρ T.smooth T.irred).rep (chars ξ hξ) :=
    hsup.of_equiv (IrrGL.equivOf T.ρ T.smooth T.irred)
  have hnu := GlobalTheory.RoadU.TwistSupp.supp_nu_chars (u.adicCompletion M) (IrrGL.of T.ρ T.smooth T.irred) n ξ
    (fun j => ξ j * absPow _ (((1 - (n : ℝ)) / 2 : ℝ) : ℂ))
    hξ (fun j => (hξ j).mul (GlobalTheory.LocGL.isSmoothChar_absPow _)) (((1 - (n : ℝ)) / 2 : ℝ) : ℂ) (fun _ => rfl)
  refine ⟨fun hun => ⟨_, hnu.1.1 hsupx, fun y hy => ?_, hnu.2.1 hun⟩, fun rc hrc a ha t => ?_⟩
  · obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 hy
    rfl
  · have hSI' := hSI M Ω A u h rc hrc _ _ hsupx t
    obtain ⟨a₀, ha₀, L⟩ := hrc
    obtain rfl : a₀ = a := (UpperTheory.Zero.LLC.artEx M Ω A u h).unique ha₀ ha
    have e : algNorm T = (IrrGL.of T.ρ T.smooth T.irred).nu (((1 - (n : ℝ)) / 2 : ℝ) : ℂ) := rfl
    have h1 : ∀ j, (rc (IrrGL.ofChar (ξ j) (hξ j))).inePol (t : G M Ω) = X - C ((ξ j (a₀ (ineIncl h t)) : ℂˣ) : ℂ) := by
      intro j
      rw [WD.inePol_of_mem_Ine _ t.2, L.one, WD.lpOfChar, WD.charPol_mk, WDRep.ofChars_ρ, charpoly_diagEnd]
      simp
    rw [← WD.inePol_of_mem_Ine _ t.2, e, L.nu, GlobalTheory.RoadU.DepthZeroRec.inePol_lpTw_of_mem_Ine _ _ t.2, hSI', chars,
      Multiset.map_map]
    exact congrArg Multiset.prod (Multiset.map_congr rfl fun j _ => h1 j)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.PAdicSplitting.PInfLifts
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL GlobalTheory.DeRhamOfPlainTorus ValuativeRel
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.ToralGalois.R2

theorem UpperTheory.Gal.ToralGalois.R2.infLifts :
    InfStep → InfLifts := by
  intro hS E Ω _ _ _ _ _ _ n hn π Y hY
  induction hY with
  | refl =>
    intro τ
    exact congrArg (CG.mk π).infChar (RingHom.comp_id τ).symm
  | @tail Y Z _ hs ih =>
    intro τ
    obtain ⟨alg, tow, hG, hP, hW⟩ := hs
    have hcomp : (algebraMap Y.K Z.K).comp (algebraMap E Y.K) = algebraMap E Z.K := by
      ext x
      apply (algebraMap Z.K Ω).injective
      rw [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply Y.K Z.K Ω,
        ← IsScalarTower.algebraMap_apply E Y.K Ω, ← IsScalarTower.algebraMap_apply E Z.K Ω]
    rw [hS Y.K Z.K hP n hn Y.π Z.π hW τ, ih (τ.comp (algebraMap Y.K Z.K)), RingHom.comp_assoc, hcomp]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.PAdicSplitting.PDrDesc
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL GlobalTheory.DeRhamOfPlainTorus ValuativeRel
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.ToralGalois.R2

theorem UpperTheory.Gal.ToralGalois.R2.drDesc :
    DRDesc := by
  intro E Ω _ _ _ _ _ _ l _ ι n π r hr w hall P AI hT A hA O _ _ _ Bw hj
  obtain ⟨X, PM, u, h', hinf, hcl⟩ := hall A hA
  obtain ⟨O', _, _, _, Bw', hj', hjj, hdesc⟩ :=
    GlobalTheory.DRDescent.deRham_descends E X.K Ω A w u hA h' l P AI hT n r hr O Bw hj
  obtain ⟨hdR, hjump⟩ := hcl P AI hT A h' O' Bw' hj'
  refine ⟨hdesc hdR, ?_⟩
  intro τ LL' τ' hind J hJ
  obtain ⟨φ, hφ⟩ := IntermediateField.exists_algHom_of_splits
    (fun s : Om l => ⟨Algebra.IsIntegral.isIntegral s, IsAlgClosed.splits _⟩)
    ((IntermediateField.val LL'.1).comp τ')
  have hφx : ∀ x : E, φ (Bw.j (algebraMap E Ω x)) = τ x := by
    intro x
    have := congrArg (fun f => f ⟨Bw.j (algebraMap E Ω x), Bw.j_E x⟩) hφ
    simp only [AlgHom.comp_apply, IntermediateField.val_mk] at this
    rw [this, hind x]
    rfl
  let LL'' : FinExt l := ⟨Bw'.Kw.1.map φ, inferInstance⟩
  let τ'' : ↥Bw'.Kw.1 →ₐ[ℚ_[l]] ↥LL''.1 := (IntermediateField.equivMap Bw'.Kw.1 φ).toAlgHom
  let τL : X.K →+* Om l := φ.toRingHom.comp (Bw'.j.comp (algebraMap X.K Ω))
  have hτL : τL.comp (algebraMap E X.K) = τ := by
    ext x
    show φ (Bw'.j (algebraMap X.K Ω (algebraMap E X.K x))) = τ x
    rw [← IsScalarTower.algebraMap_apply E X.K Ω, hjj, hφx]
  have hind' : IsInduced Bw' τL τ'' := fun x => rfl
  have hJ' : J.map (fun n : ℤ => (n : ℂ)) =
      ((CG.mk PM).infChar (ι.toRingHom.comp τL)).map (fun z => ((n : ℂ) - 1) / 2 - z) := by
    rw [hinf, RingHom.comp_assoc, hτL, hJ]
  exact GlobalTheory.JumpsDescend.jumps_descend E X.K Ω A w u hA h' l P AI hT n r hr O Bw O' Bw' hj hj' hjj τ τL hτL J
    (hjump τL LL'' τ'' hind' J hJ')
end

namespace UpperTheory.Gal.ToralGalois.R2

theorem toTor_holds : ToTor :=
  toTor UpperTheory.Gal.InertialTypesAlt.suppBC_outright UpperTheory.Gal.UnramifiedFromSplittingCriterion.unrField_holds UpperTheory.Gal.NearKilling.allLift_holds UpperTheory.Gal.NearKilling.ineNorm
    (infLifts (infStep UpperTheory.Gal.InertialTypesAlt.stableOf)) (recChars UpperTheory.Gal.InertialTypesAlt.suppIne) UpperTheory.Zero.LLC.recTExists

theorem localGlobalCompatAtIwahoriFixed_of_unlinked : GlobalTheory.DeRhamOfPlainTorus.R1 → LocalGlobalCompatAtIwahoriFixedPlaces := r2g mixedOf toTor_holds drDesc UpperTheory.Zero.LLC.recTExists

end UpperTheory.Gal.ToralGalois.R2
