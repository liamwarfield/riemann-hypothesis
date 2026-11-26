module

public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModuliConsequenceOfAbelianSchemeLaws
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ThetaPointDeterminesPolarisedLevel
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsProperOfThetaUnitInEveryCoset
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEndomorphismsToCompleteDvr
public import Development.AbelianVarietyTheory.Counterexamples.UniformisationSurvey.MapPowLeOfIsPullUnif
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.UniformTorsionIsomorphism
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NotWeilIsGrpPullbackNoncomm
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDescOfPoints
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsEllipticCurveTwoAdic
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGenericIsoOfUniformisationsIsoData

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem _root_.GlobalTheory.lawsAndExpansions :
    _root_.GlobalTheory.UT.LL ∧ _root_.ReciprocityTheory.ChartRestriction.G.DVR.TwistBCSpanStatement ∧ _root_.ReciprocityTheory.ChartRestriction.G.DVR.TWM.VRatioGtStatement ∧ _root_.ReciprocityTheory.ChartRestriction.G.DVR.TWStatement ∧ _root_.ReciprocityTheory.ChartRestriction.G.DVR.UUStatement := by
  have hLaws := _root_.GlobalTheory.allSixLaws
  have hU : _root_.ReciprocityTheory.ChartRestriction.G.Out.GlobalFnsSt := _root_.GlobalTheory.laws_without_cohomology.1
  have hS : _root_.ReciprocityTheory.ChartRestriction.G.DVR.TwistBaseChangeStatement := _root_.GlobalTheory.twistBaseChange
  have hR : _root_.ReciprocityTheory.ChartRestriction.G.DVR.TwistBCSpanStatement := _root_.ReciprocityTheory.ChartRestriction.G.DVR.twistBCSpan_of hS
  have hA : _root_.ReciprocityTheory.ChartRestriction.G.DVR.TWM.VRatioGtStatement := _root_.GlobalTheory.RatioVal.main
  refine ⟨?_, hR, hA, _root_.ReciprocityTheory.ChartRestriction.G.DVR.TWM.tw_of hU hR hA, _root_.GlobalTheory.UnitBallFree.main hU hS⟩
  unfold _root_.GlobalTheory.UT.LL
  exact ⟨hLaws.1, hLaws.2.1, hLaws.2.2.1, hLaws.2.2.2.1, hLaws.2.2.2.2.1⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatementsStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformization_laws_and_expansion_statements : GlobalTheory.UT.LL ∧ DVR.TwistBCSpanStatement ∧ DVR.TWM.VRatioGtStatement ∧ DVR.TWStatement ∧ DVR.UUStatement := by
  first | exact @GlobalTheory.lawsAndExpansions | exact GlobalTheory.lawsAndExpansions | (intros; apply GlobalTheory.lawsAndExpansions <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaUniformisationComplexAbelianVarieties
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaUniformisationComplexAbelianVarieties
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem _root_.GlobalTheory.thetaUnifAV_closed : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ThetaUnifAV := by
  have hLaws := _root_.GlobalTheory.allSixLaws.1
  exact _root_.GlobalTheory.thetaUnifAV_of_laws hLaws.cube hLaws.mulN hLaws.weil
    hLaws.weilNondeg hLaws.globalSectionsRank

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaUniformisationComplexAbelianVarietiesStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_uniformisation_complex_abelian_varieties : ThetaUnifAV := by
  first | exact @GlobalTheory.thetaUnifAV_closed | exact GlobalTheory.thetaUnifAV_closed | (intros; apply GlobalTheory.thetaUnifAV_closed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSemiAbelianTripleMapExtendingModelMap
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabMapExtendingOfIso
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.Models

theorem Cpt.arith_and_proOpen {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {U : Scheme.{0}}
    {F O : Type} [Field F] [CommRing O] {c : U ⟶ Sp F} {t : SAB H U} {β : O →+* F} (C : Cpt c t β)
    (hβ : IsDedFrac β) (hO : Algebra.FiniteType ℤ O) :
    (∃ z : C.X ⟶ Sp ℤ, LocallyOfFiniteType z ∧ Flat z) ∧ IsPreimmersion C.j ∧ Flat C.j ∧ IsDominant C.j ∧
      QuasiCompact C.j := by
  obtain ⟨⟨hdom, hded⟩, hchar, hfr⟩ := hβ
  let _ : Algebra O F := β.toAlgebra
  have h := GlobalTheory.genericPart_dense_proOpen O F C.X U C.s C.jQ C.flat C.proj C.jQ_open C.jQ_dense
  refine ⟨⟨C.s ≫ spMap (algebraMap ℤ O), ?_, ?_⟩, h.2.2.2⟩
  · have hprop : IsProper C.s := by
      obtain ⟨N, i, hi, e⟩ := C.proj
      have := isProper_str O N
      rw [← e]; infer_instance
    have : LocallyOfFiniteType (spMap (algebraMap ℤ O)) := by
      rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
      exact RingHom.finiteType_algebraMap.mpr hO
    infer_instance
  · have := C.flat
    have : Flat (spMap (algebraMap ℤ O)) := by
      rw [Flat.SpecMap_iff]
      exact RingHom.flat_algebraMap_iff.mpr inferInstance
    infer_instance

theorem exists_sabMap_extending_of_iso : ((∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X U : Scheme.{0}) (j : U ⟶ X), (Geo.Tor.IsNormalScheme X ∧ ∃ z : X ⟶ Sp ℤ, LocallyOfFiniteType z ∧ Flat z) → IsPreimmersion j → Flat j → IsDominant j → QuasiCompact j → ∀ (t₀ : SAB H U) (t t' : SAB H X) (a : SABMap t₀ t j) (a' : SABMap t₀ t' j), IsProper t₀.G.hom → ∃ b : SABMap t t' (𝟙 X), a.φ ≫ b.φ = a'.φ) → (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (U : Scheme.{0}) (F O : Type) [Field F] [CommRing O] (c : U ⟶ Sp F) (t : SAB H U) (β : O →+* F) (U' : Scheme.{0}) (F' O' : Type) [Field F'] [CommRing O'] (c' : U' ⟶ Sp F') (t' : SAB H U') (β' : O' →+* F') (C : Cpt c t β) (C' : Cpt c' t' β') (r : U' ⟶ U) (ν : SABMap t' t r) (f : C'.X ⟶ C.X), IsDedFrac β' → Algebra.FiniteType ℤ O' → IsProper t'.G.hom → C'.j ≫ f = r ≫ C.j → ∃ mu : SABMap C'.t C.t f, C'.m.φ ≫ mu.φ = ν.φ ≫ C.m.φ := by
  intro hS hT E _ _ _ H U F O _ _ c t β U' F' O' _ _ c' t' β' C C' r ν f hβ hO hp hj
  obtain ⟨hz, h1, h2, h3, h4⟩ := C'.arith_and_proOpen hβ hO
  obtain ⟨PP', cub, sym, adj, prim, p, -⟩ := sabPull Out.CubePf.cubePull f C.t
  obtain ⟨n, hn⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ C.m ν
  obtain ⟨n', hn'⟩ := GlobalTheory.exists_sabMap_of_base_eq n (g := C'.j ≫ f) hj.symm
  obtain ⟨a', ha'⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ p n'
  obtain ⟨b, hb⟩ := hS hT E H C'.X U' C'.j ⟨C'.normal, hz⟩ h1 h2 h3 h4 t' C'.t _ C'.m a' hp
  obtain ⟨m, hm⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ p b
  obtain ⟨mu, hmu⟩ := GlobalTheory.exists_sabMap_of_base_eq m (Category.id_comp f)
  refine ⟨mu, ?_⟩
  exact (congrArg (C'.m.φ ≫ ·) (hmu.trans hm)).trans ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ p.φ) hb).trans (ha'.symm.trans (hn'.trans hn))))

end GlobalTheory.Models
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSemiAbelianTripleMapExtendingModelMap
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.Models

theorem exists_sabMap_extending : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (U : Scheme.{0}) (F O : Type) [Field F] [CommRing O] (c : U ⟶ Sp F) (t : SAB H U) (β : O →+* F) (U' : Scheme.{0}) (F' O' : Type) [Field F'] [CommRing O'] (c' : U' ⟶ Sp F') (t' : SAB H U') (β' : O' →+* F') (C : Cpt c t β) (C' : Cpt c' t' β') (r : U' ⟶ U) (ν : SABMap t' t r) (f : C'.X ⟶ C.X), IsDedFrac β' → Algebra.FiniteType ℤ O' → IsProper t'.G.hom → C'.j ≫ f = r ≫ C.j → ∃ mu : SABMap C'.t C.t f, C'.m.φ ≫ mu.φ = ν.φ ≫ C.m.φ :=
  exists_sabMap_extending_of_iso GlobalTheory.exists_sabMap_id_of_common_generic

end GlobalTheory.Models
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSemiAbelianTripleMapExtendingModelMapStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_semiAbelianTripleMap_extending_modelMap : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (U : Scheme.{0}) (F O : Type) [Field F] [CommRing O] (c : U ⟶ Sp F) (t : SAB H U) (β : O →+* F) (U' : Scheme.{0}) (F' O' : Type) [Field F'] [CommRing O'] (c' : U' ⟶ Sp F') (t' : SAB H U') (β' : O' →+* F') (C : Cpt c t β) (C' : Cpt c' t' β') (r : U' ⟶ U) (ν : SABMap t' t r) (f : C'.X ⟶ C.X), IsDedFrac β' → Algebra.FiniteType ℤ O' → IsProper t'.G.hom → C'.j ≫ f = r ≫ C.j → ∃ mu : SABMap C'.t C.t f, C'.m.φ ≫ mu.φ = ν.φ ≫ C.m.φ := by
  first | exact @GlobalTheory.Models.exists_sabMap_extending | exact GlobalTheory.Models.exists_sabMap_extending | (intros; apply GlobalTheory.Models.exists_sabMap_extending <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaPointDeterminesAndEndDeterminedTorsion
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaPointDeterminesAndEndDeterminedTorsion
namespace GlobalTheory

theorem _root_.GlobalTheory.thetaPtDetermines_and_endDeterminedOnTorsion :
    _root_.GlobalTheory.ThetaPtDeterminesSt ∧ _root_.GlobalTheory.EndDeterminedOnTorsionSt := by
  have hL := _root_.GlobalTheory.allSixLaws
  refine ⟨_root_.GlobalTheory.thetaPt_determines hL.1,
    _root_.GlobalTheory.endDeterminedOnTorsion hL.1 ?_⟩
  exact _root_.GlobalTheory.card_zeros_on_torsion_coset_le hL.1.mulN
    (fun K _ X _ p L hL => _root_.GlobalTheory.SectionRing.exists_sectionRing K X p L hL)
    (_root_.GlobalTheory.PowSec.exists_basis_sections hL.1.globalSectionsRank)
    (_root_.GlobalTheory.veryAmple_lbPow hL.1.ample)
    (_root_.GlobalTheory.exists_mulPull_sec hL.1.mulPull)
    (fun K _ X p g hp U hU hne => _root_.GlobalTheory.SmoothDim.ringKrullDim_affineOpen K X p g hp U hU hne)
    _root_.GlobalTheory.polAV_isIntegral_of_isAlgClosed
    (fun K T _ _ _ _ 𝒜 _ m x hx hne d s hs hpow => _root_.GlobalTheory.isIntegral_adjoin_of_mul_pow_mem K T 𝒜 m x hx hne d s hs hpow)
    _root_.GlobalTheory.graded_bezout_bound

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaPointDeterminesAndEndDeterminedTorsionStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaPoint_determines_and_end_determined_torsion : GlobalTheory.ThetaPtDeterminesSt ∧ GlobalTheory.EndDeterminedOnTorsionSt := by
  first | exact @GlobalTheory.thetaPtDetermines_and_endDeterminedOnTorsion | exact GlobalTheory.thetaPtDetermines_and_endDeterminedOnTorsion | (intros; apply GlobalTheory.thetaPtDetermines_and_endDeterminedOnTorsion <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsBirationalModelSemiAbelianAmpleFrames
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsBirationalModelSemiAbelianAmpleFrames
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
open Classical

namespace GlobalTheory.ModelOfOutput

theorem exists_openImmersion_section {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] {U : Scheme.{0}} [IsIntegral U] (g : U ⟶ Sp R) [IsSeparated g] [LocallyOfFiniteType g]
    (x : Sp K ⟶ U) [IsDominant x] (hx : x ≫ g = spMap (algebraMap R K)) :
    ∃ (W : (Sp R).Opens) (j : W.toScheme ⟶ U), Dense (W : Set (Sp R)) ∧ IsOpenImmersion j ∧ IsDominant j ∧
      j ≫ g = W.ι := by
  obtain ⟨e, he⟩ := IsGenericPointHom.fractionField R K
  obtain ⟨W, hW, j, h₁, h₂⟩ := spread_out_of_isGermInjective' (𝟙 (Sp R)) g (x := genericPoint (Sp R)) (e.inv ≫ x)
    (by rw [Category.assoc, hx, Category.comp_id, Iso.inv_comp_eq]; exact he.symm)
  rw [Category.comp_id] at h₂
  have hd : IsDominant j := by
    have : IsDominant (W.fromSpecStalkOfMem _ hW ≫ j) := h₁ ▸ inferInstance
    exact IsDominant.of_comp (W.fromSpecStalkOfMem _ hW) j
  have hr : Set.range j ⊆ Set.range (g ⁻¹ᵁ W).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    show g (j w) ∈ W
    rw [← Scheme.Hom.comp_apply, h₂]
    exact w.2
  have e₁ := IsOpenImmersion.lift_fac (g ⁻¹ᵁ W).ι j hr
  set j' := IsOpenImmersion.lift (g ⁻¹ᵁ W).ι j hr
  have : IsDominant (j' ≫ (g ⁻¹ᵁ W).ι) := e₁.symm ▸ hd
  have : IsDominant j' := IsDominant.of_comp_of_isOpenImmersion _ (g ⁻¹ᵁ W).ι
  have e₂ : j' ≫ g ∣_ W = 𝟙 _ := by
    rw [← cancel_mono W.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, e₁, h₂, Category.id_comp]
  have e₃ : g ∣_ W ≫ j = (g ⁻¹ᵁ W).ι :=
    ext_of_isDominant_of_isSeparated g (by rw [Category.assoc, h₂, morphismRestrict_ι]) j'
      (by rw [← Category.assoc, e₂, Category.id_comp, e₁])
  have : IsIso j' := ⟨g ∣_ W, e₂, by
    rw [← cancel_mono (g ⁻¹ᵁ W).ι, Category.assoc, e₁, e₃, Category.id_comp]⟩
  refine ⟨W, j, W.isOpen.dense ⟨_, hW⟩, ?_, hd, h₂⟩
  rw [← e₁]
  infer_instance

theorem flat_ratModel {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [h : GlobalTheory.ZH.ArithBase o Ω]
    (M : GlobalTheory.ZH.RatModel o Ω) : Flat M.s := by
  have := h.ded
  have := M.sep
  have : IsSchemeTheoreticallyDominant M.pt := .of_isDominant _
  have : QuasiCompact M.pt := ⟨fun U _ _ => (Set.toFinite _).isCompact⟩
  have : Flat (M.pt ≫ M.s) := by
    rw [M.pt_s]
    refine Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 ?_)
    have : FaithfulSMul o Ω := (faithfulSMul_iff_algebraMap_injective o Ω).2 h.inj
    infer_instance
  exact flat_of_schemeDominant_of_isDedekindDomain (O := CommRingCat.of o) M.pt M.s

theorem exists_zOn : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [GlobalTheory.ZH.ArithBase o Ω] (R : Subalgebra o Ω) (t₀ : SAB H (Sp R)) (S : GlobalTheory.ZH.ThetaSys o Ω) (ρ : S.Real) (h : R ≤ S.R) (φ : ρ.P.A.left ⟶ t₀.G.left) (act : OAct (𝓞 E) ρ.P.A) (M : GlobalTheory.ZH.RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Z : GlobalTheory.ZH.ZHOut ρ M U₀ EE) (m : ℕ) (r₀ : ℤ), R.FG → (∀ x : Ω, ∃ a ∈ R, ∃ c ∈ R, x = a / c) → S.Over₀ M U₀ → IsOpen (abLocus Z.G) → IsGrpPullback ρ.P.A t₀.G (spMap (Subalgebra.inclusion h).toRingHom) φ → LBIso ρ.P.L (t₀.PP.L.pull φ) → (∀ a, (act.act a).left ≫ φ = φ ≫ (t₀.act.act a).left) → (letI := ρ.P.isAb.comm; ∀ a, LBIso (cubeLB ρ.P.A ![fst _ _ ≫ act.act a, snd _ _] ρ.P.L) (cubeLB ρ.P.A ![fst _ _, snd _ _ ≫ act.act (H.bar a)] ρ.P.L)) → (letI := ρ.P.isAb.comm; LBIso ρ.P.L (cubeLB ρ.P.A ![𝟙 _, act.act H.w0] ρ.P.L)) → (∀ r : ℤ, r₀ ≤ r → ∃ A : GlobalTheory.LN.AmpFrames Z.G Z.L.L (m ^ 2), A.r = r ∧ A.s = 1) → ∃ C : ZOn (spMap (algebraMap o R)) t₀ m, IsIntegral C.Z ∧ C.amp.s = 1 ∧ ∀ r : ℤ, C.amp.r ≤ r → ∃ A : GlobalTheory.LN.AmpFrames C.t.G C.t.PP.L (m ^ 2), A.r = r ∧ A.s = 1 := by
  intro _ _ E _ _ _ H o Ω _ _ _ hb R t₀ S ρ h φ act M U₀ EE Z m r₀ _ hfr hO hop hφ hL hact hadj hprim hamp
  obtain ⟨act', h₂, h₃, hact', hgood⟩ := GlobalTheory.TripleOut.exists_triple GlobalTheory.homExtension_semiAbelian_dvr o Ω S ρ M U₀ EE Z
    E H act hO hadj hprim
  let t : SAB H M.Z := SAB.mk (H := H) Z.G Z.semi act' Z.L Z.cub Z.sym h₂ h₃
  have : IsFractionRing R Ω := IsFractionRing.of_field R Ω fun y => by
    obtain ⟨a, ha, b, hb, rfl⟩ := hfr y
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, rfl⟩
  have hr : Set.range M.pt ⊆ Set.range U₀.ι := by
    rw [Scheme.Opens.range_ι]
    exact (GlobalTheory.ZH.top_le_preimage_iff _ _).1 (M.top_le_preimage_pt hO.ne)
  have ex := IsOpenImmersion.lift_fac U₀.ι M.pt hr
  set x := IsOpenImmersion.lift U₀.ι M.pt hr
  have : IsDominant (x ≫ U₀.ι) := ex.symm ▸ inferInstance
  have : IsDominant x := IsDominant.of_comp_of_isOpenImmersion _ U₀.ι
  have : Nonempty U₀.toScheme := ⟨⟨_, hO.ne.some_mem⟩⟩
  have : IsIntegral U₀.toScheme := isIntegral_of_isOpenImmersion U₀.ι
  let g : U₀.toScheme ⟶ Sp R := Z.u₀ ≫ spMap (Subalgebra.inclusion h).toRingHom
  have hx : x ≫ g = spMap (algebraMap R Ω) := by
    rw [← Category.assoc, Z.u₀_gen x ex, ← Spec.map_comp]
    rfl
  have hg : g ≫ spMap (algebraMap o R) = U₀.ι ≫ M.s := by
    refine ext_of_isDominant x ?_
    rw [← Category.assoc, hx, ← Category.assoc, ex, M.pt_s, ← Spec.map_comp]
    rfl
  have := M.sep
  have := M.lft
  have : IsSeparated (g ≫ spMap (algebraMap o R)) := hg ▸ inferInstance
  have : IsSeparated g := IsSeparated.of_comp g (spMap (algebraMap o R))
  have : LocallyOfFiniteType (g ≫ spMap (algebraMap o R)) := hg ▸ inferInstance
  have : LocallyOfFiniteType g := locallyOfFiniteType_of_comp g (spMap (algebraMap o R))
  obtain ⟨W, j, hW, hj₁, hj₂, hj⟩ := exists_openImmersion_section g x hx
  obtain ⟨PP', cub, sym, adj, prim, m₁, -⟩ := sabPull GlobalTheory.laws3.cubePull W.ι t₀
  set tW : SAB H W.toScheme := ⟨(Over.pullback W.ι).obj t₀.G, IsSemiAbelian.pullback W.ι t₀.G t₀.semi,
    OAct.pullback W.ι t₀.G t₀.act, PP', cub, sym, adj, prim⟩
  clear_value tW
  have hP := (isGrpPullback_pullback ρ.P.A Z.u₀).comp hφ
  let ψ : tW.G.left ⟶ pullback ρ.P.A.hom Z.u₀ :=
    hP.1.lift m₁.φ (tW.G.hom ≫ j) (by rw [m₁.cart.1.w, Category.assoc, hj])
  have ψ₁ : ψ ≫ pullback.fst ρ.P.A.hom Z.u₀ ≫ φ = m₁.φ := hP.1.lift_fst _ _ _
  have ψ₂ : ψ ≫ pullback.snd ρ.P.A.hom Z.u₀ = tW.G.hom ≫ j := hP.1.lift_snd _ _ _
  have hψ : IsGrpPullback tW.G ((Over.pullback Z.u₀).obj ρ.P.A) j ψ :=
    hP.cancel (m₁.cart.congr hj.symm ψ₁.symm) ψ₂
  have hA : IsProper ρ.P.A.hom := GlobalTheory.ZH.isProper_hom_of_relAmple ρ.P.ample
  have hA' : IsProper tW.G.hom :=
    MorphismProperty.of_isPullback (P := @IsProper) hψ.1 (inferInstanceAs (IsProper (pullback.snd ρ.P.A.hom Z.u₀)))
  have hψa : ∀ a, (tW.act.act a).left ≫ ψ = ψ ≫ ((Over.pullback Z.u₀).map (act.act a)).left := fun a => by
    have A : ((Over.pullback Z.u₀).map (act.act a)).left ≫ pullback.fst ρ.P.A.hom Z.u₀ =
      pullback.fst ρ.P.A.hom Z.u₀ ≫ (act.act a).left := pullback.lift_fst _ _ _
    have B : ((Over.pullback Z.u₀).map (act.act a)).left ≫ pullback.snd ρ.P.A.hom Z.u₀ =
      pullback.snd ρ.P.A.hom Z.u₀ := Over.w ((Over.pullback Z.u₀).map (act.act a))
    apply hP.1.hom_ext
    · calc ((tW.act.act a).left ≫ ψ) ≫ pullback.fst ρ.P.A.hom Z.u₀ ≫ φ
          = m₁.φ ≫ (t₀.act.act a).left := by rw [Category.assoc, ψ₁]; exact m₁.act a
        _ = ψ ≫ (pullback.fst ρ.P.A.hom Z.u₀ ≫ (act.act a).left) ≫ φ := by
          rw [← ψ₁]; simp only [Category.assoc, hact]
        _ = _ := by rw [← A]; simp only [Category.assoc]
    · calc ((tW.act.act a).left ≫ ψ) ≫ pullback.snd ρ.P.A.hom Z.u₀
          = tW.G.hom ≫ j := by rw [Category.assoc, ψ₂, ← Category.assoc, Over.w]
        _ = ψ ≫ ((Over.pullback Z.u₀).map (act.act a)).left ≫ pullback.snd ρ.P.A.hom Z.u₀ := by rw [B, ψ₂]
        _ = _ := (Category.assoc _ _ _).symm
  have hLW : LBIso tW.PP.L (t.PP.L.pull (ψ ≫ Z.φ)) := by
    have a₁ : LBIso tW.PP.L (t₀.PP.L.pull m₁.φ) := by
      obtain ⟨w, hw, -⟩ := m₁.lin
      exact ⟨w, hw⟩
    have a₂ : LBIso (ρ.P.L.pull (ψ ≫ pullback.fst ρ.P.A.hom Z.u₀)) (t₀.PP.L.pull m₁.φ) :=
      GenSpread.lbIso_pull_of_lbIso hL _ (by rw [Category.assoc, ψ₁])
    have a₃ : LBIso (Z.L.L.pull (ψ ≫ Z.φ)) (ρ.P.L.pull (ψ ≫ pullback.fst ρ.P.A.hom Z.u₀)) :=
      GenSpread.lbIso_pull_comp ψ rfl rfl ⟨Z.w, Z.w_gen⟩
    exact LBIso.trans tW.PP.isLB (pull_isLB t₀.PP.isLB _) (pull_isLB Z.L.isLB _) a₁
      (LBIso.trans (pull_isLB Z.L.isLB _) (pull_isLB ρ.P.isLB _) (pull_isLB t₀.PP.isLB _) a₃ a₂).symm
  obtain ⟨m₂, -⟩ := GlobalTheory.exists_sabMap_of_lbIso E H M.Z W.toScheme t tW (j ≫ U₀.ι) (ψ ≫ Z.φ)
    ⟨inferInstance, fun y _ K _ _ p _ => inferInstance⟩ (hψ.comp Z.cart)
    (fun a => by
      rw [← Category.assoc, hψa, Category.assoc, Category.assoc]
      exact congrArg (ψ ≫ ·) (hact' a)) hLW
  obtain ⟨A, hA₁, hA₂⟩ := hamp r₀ le_rfl
  have : IsDominant U₀.ι := ⟨by
    rw [DenseRange, Scheme.Opens.range_ι]
    exact U₀.isOpen.dense hO.ne⟩
  exact ⟨⟨M.Z, M.s, GlobalTheory.IsNormalScheme.of_pred hO.normal, hO.proj, flat_ratModel M, t, Z.qproj,
    hgood (GlobalTheory.ZH.abOpen_of_isOpen_abLocus o Ω S ρ M U₀ EE Z hO hop), W, hW, j ≫ U₀.ι, inferInstance, inferInstance,
    by rw [Category.assoc, ← hg, ← Category.assoc, hj], tW, m₁, m₂, A⟩, M.integral, hA₂,
    fun r hr => hamp r (hA₁ ▸ hr)⟩

end GlobalTheory.ModelOfOutput
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsBirationalModelSemiAbelianAmpleFramesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_birationalModel_semiAbelian_ampleFrames : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [GlobalTheory.ZH.ArithBase o Ω] (R : Subalgebra o Ω) (t₀ : SAB H (Sp R)) (S : GlobalTheory.ZH.ThetaSys o Ω) (ρ : S.Real) (h : R ≤ S.R) (φ : ρ.P.A.left ⟶ t₀.G.left) (act : OAct (𝓞 E) ρ.P.A) (M : GlobalTheory.ZH.RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Z : GlobalTheory.ZH.ZHOut ρ M U₀ EE) (m : ℕ) (r₀ : ℤ), R.FG → (∀ x : Ω, ∃ a ∈ R, ∃ c ∈ R, x = a / c) → S.Over₀ M U₀ → IsOpen (abLocus Z.G) → IsGrpPullback ρ.P.A t₀.G (spMap (Subalgebra.inclusion h).toRingHom) φ → LBIso ρ.P.L (t₀.PP.L.pull φ) → (∀ a, (act.act a).left ≫ φ = φ ≫ (t₀.act.act a).left) → (letI := ρ.P.isAb.comm; ∀ a, LBIso (cubeLB ρ.P.A ![fst _ _ ≫ act.act a, snd _ _] ρ.P.L) (cubeLB ρ.P.A ![fst _ _, snd _ _ ≫ act.act (H.bar a)] ρ.P.L)) → (letI := ρ.P.isAb.comm; LBIso ρ.P.L (cubeLB ρ.P.A ![𝟙 _, act.act H.w0] ρ.P.L)) → (∀ r : ℤ, r₀ ≤ r → ∃ A : GlobalTheory.LN.AmpFrames Z.G Z.L.L (m ^ 2), A.r = r ∧ A.s = 1) → ∃ C : ZOn (spMap (algebraMap o R)) t₀ m, IsIntegral C.Z ∧ C.amp.s = 1 ∧ ∀ r : ℤ, C.amp.r ≤ r → ∃ A : GlobalTheory.LN.AmpFrames C.t.G C.t.PP.L (m ^ 2), A.r = r ∧ A.s = 1 := by
  first | exact @GlobalTheory.ModelOfOutput.exists_zOn | exact GlobalTheory.ModelOfOutput.exists_zOn | (intros; apply GlobalTheory.ModelOfOutput.exists_zOn <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSemiAbelianTripleGlueCommonGenericPart
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSemiAbelianTripleGlueCommonGenericPart
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.TripleGlue

def DensePart {X X₀ : Scheme.{0}} (j : X₀ ⟶ X) : Prop :=
  (Geo.Tor.IsNormalScheme X ∧ ∃ z : X ⟶ Sp ℤ, LocallyOfFiniteType z ∧ Flat z) ∧ IsPreimmersion j ∧ Flat j ∧
    IsDominant j ∧ QuasiCompact j

theorem DensePart.restrict {X X₀ Y : Scheme.{0}} {j : X₀ ⟶ X} (h : DensePart j) (i : Y ⟶ X) [IsOpenImmersion i]
    {k : X₀ ⟶ Y} (hk : k ≫ i = j) : DensePart k := by
  obtain ⟨⟨hn, z, hz₁, hz₂⟩, h₁, h₂, h₃, h₄⟩ := h
  have sq : IsPullback (𝟙 X₀) k j i := IsPullback.of_horiz_isIso_mono ⟨by rw [hk, Category.id_comp]⟩
  refine ⟨⟨fun y => ?_, i ≫ z, inferInstance, inferInstance⟩, MorphismProperty.of_isPullback sq h₁,
    MorphismProperty.of_isPullback sq h₂, ⟨?_⟩, MorphismProperty.of_isPullback sq h₄⟩
  · obtain ⟨_, _⟩ := hn (i y)
    have e := (asIso (i.stalkMap y)).commRingCatIsoToRingEquiv
    exact ⟨e.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e⟩
  · have e : Set.range k = i ⁻¹' Set.range j := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨x, by rw [← hk, Scheme.Hom.comp_apply]⟩
      · rintro ⟨x, hx⟩
        exact ⟨x, i.isOpenEmbedding.injective (by rw [← hx, ← hk, Scheme.Hom.comp_apply])⟩
    rw [DenseRange, e]
    exact j.denseRange.preimage i.isOpenEmbedding.isOpenMap

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_cast {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f g : S' ⟶ S} (m : SABMap t' t f) (h : f = g) :
    ∃ n : SABMap t' t g, n.φ = m.φ := by
  subst h
  exact ⟨m, rfl⟩

theorem exists_fac {X X₀ Y : Scheme.{0}} {j : X₀ ⟶ X} {t₀ : SAB H X₀} {t : SAB H X} (a : SABMap t₀ t j) (i : Y ⟶ X)
    {k : X₀ ⟶ Y} (hk : k ≫ i = j) :
    ∃ (s : SAB H Y) (b : SABMap t₀ s k) (m : SABMap s t i), b.φ ≫ m.φ = a.φ := by
  obtain ⟨_, _, _, _, _, m, -⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.sabPull Out.CubePf.cubePull i t
  obtain ⟨a', ha'⟩ := exists_cast a hk.symm
  obtain ⟨b, hb⟩ := ObjMaps.exists_sab_cancel m a'
  exact ⟨_, b, m, hb.symm.trans ha'⟩

theorem DensePart.generic {X X₀ : Scheme.{0}} {j : X₀ ⟶ X} (h : DensePart j) {t₀ : SAB H X₀} {t : SAB H X}
    (a : SABMap t₀ t j) (hp : IsProper t₀.G.hom) : IsReduced X ∧ genericPoints X ⊆ abLocus t.G := by
  obtain ⟨hX, h₁, h₂, h₃, h₄⟩ := h
  have : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
    have := (hX.1 x).1
    infer_instance
  exact ⟨isReduced_of_isReduced_stalk X,
    (densePart_basic X X₀ j h₁ h₂ h₃ h₄).1.trans (range_subset_abLocus_of_isProper t.semi a.cart.1)⟩

section

variable (hdvr : ∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f)
include hdvr

theorem DensePart.exists_map {X X₀ Y : Scheme.{0}} {j : X₀ ⟶ X} {k : X₀ ⟶ Y} (h : DensePart k) {i : Y ⟶ X}
    (hk : k ≫ i = j) {t₀ : SAB H X₀} {t : SAB H X} {s : SAB H Y} (a : SABMap t₀ t j) (b : SABMap t₀ s k)
    (hp : IsProper t₀.G.hom) : ∃ n : SABMap s t i, b.φ ≫ n.φ = a.φ := by
  obtain ⟨s', b', m, hm⟩ := exists_fac a i hk
  obtain ⟨c, hc⟩ := exists_sabMap_id_of_common_generic hdvr E H Y X₀ k h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2
    t₀ s s' b b' hp
  obtain ⟨n, hn⟩ := ObjMaps.exists_sab_comp m c
  obtain ⟨n', hn'⟩ := exists_cast n (Category.id_comp i)
  exact ⟨n', by rw [hn', hn, ← Category.assoc, hc, hm]⟩

theorem DensePart.glue_top {X X₀ : Scheme.{0}} {j : X₀ ⟶ X} (h : DensePart j) {U V : X.Opens} (hUV : U ⊔ V = ⊤)
    {jU : X₀ ⟶ U.toScheme} {jV : X₀ ⟶ V.toScheme} (hU : jU ≫ U.ι = j) (hV : jV ≫ V.ι = j) {t₀ : SAB H X₀}
    {t₁ : SAB H U.toScheme} {t₂ : SAB H V.toScheme} (a₁ : SABMap t₀ t₁ jU) (a₂ : SABMap t₀ t₂ jV)
    (hp : IsProper t₀.G.hom) : ∃ t : SAB H X, Nonempty (SABMap t₀ t j) := by
  have hr : Set.range j ⊆ Set.range (U ⊓ V).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact ⟨by rw [← hU]; exact (jU x).2, by rw [← hV]; exact (jV x).2⟩
  obtain ⟨k, hk⟩ : ∃ k : X₀ ⟶ (U ⊓ V).toScheme, k ≫ (U ⊓ V).ι = j := ⟨_, IsOpenImmersion.lift_fac _ j hr⟩
  have hkU : k ≫ X.homOfLE inf_le_left = jU := by
    rw [← cancel_mono U.ι, Category.assoc, Scheme.homOfLE_ι, hk, hU]
  have hkV : k ≫ X.homOfLE inf_le_right = jV := by
    rw [← cancel_mono V.ι, Category.assoc, Scheme.homOfLE_ι, hk, hV]
  obtain ⟨s, b, m₁, -⟩ := exists_fac a₁ _ hkU
  obtain ⟨m₂, -⟩ := (h.restrict _ hk).exists_map hdvr hkV a₂ b hp
  obtain ⟨t, n₁, -, -⟩ := GlobalTheory.T.exists_triple_glue_two_opens E H X U V t₁ t₂ s m₁ m₂ hUV ((h.restrict _ hU).generic a₁ hp)
    ((h.restrict _ hV).generic a₂ hp)
  obtain ⟨n, -⟩ := ObjMaps.exists_sab_comp n₁ a₁
  obtain ⟨n', -⟩ := exists_cast n hU
  exact ⟨t, ⟨n'⟩⟩

omit hdvr in
theorem exists_trace {X X₀ Y : Scheme.{0}} {j : X₀ ⟶ X} (i : Y ⟶ X) {k : X₀ ⟶ Y} (hk : k ≫ i = j) {U : X.Opens}
    {jU : X₀ ⟶ U.toScheme} (hU : jU ≫ U.ι = j) {t₀ : SAB H X₀} {t : SAB H U.toScheme} (a : SABMap t₀ t jU) :
    ∃ (k' : X₀ ⟶ (i ⁻¹ᵁ U).toScheme) (s : SAB H (i ⁻¹ᵁ U).toScheme),
      k' ≫ (i ⁻¹ᵁ U).ι = k ∧ Nonempty (SABMap t₀ s k') := by
  have hr : Set.range k ⊆ Set.range (i ⁻¹ᵁ U).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    show i (k x) ∈ U
    rw [← Scheme.Hom.comp_apply, hk, ← hU]
    exact (jU x).2
  obtain ⟨k', hk'⟩ : ∃ k' : X₀ ⟶ (i ⁻¹ᵁ U).toScheme, k' ≫ (i ⁻¹ᵁ U).ι = k := ⟨_, IsOpenImmersion.lift_fac _ k hr⟩
  have e : k' ≫ (i ∣_ U) = jU := by
    rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hk', hk, hU]
  obtain ⟨s, b, -, -⟩ := exists_fac a _ e
  exact ⟨k', s, hk', ⟨b⟩⟩

theorem DensePart.glue_sup {X X₀ : Scheme.{0}} {j : X₀ ⟶ X} (h : DensePart j) {t₀ : SAB H X₀} (hp : IsProper t₀.G.hom)
    {U V : X.Opens}
    (hU : ∃ (k : X₀ ⟶ U.toScheme) (s : SAB H U.toScheme), k ≫ U.ι = j ∧ Nonempty (SABMap t₀ s k))
    (hV : ∃ (k : X₀ ⟶ V.toScheme) (s : SAB H V.toScheme), k ≫ V.ι = j ∧ Nonempty (SABMap t₀ s k)) :
    ∃ (k : X₀ ⟶ (U ⊔ V).toScheme) (s : SAB H (U ⊔ V).toScheme), k ≫ (U ⊔ V).ι = j ∧ Nonempty (SABMap t₀ s k) := by
  obtain ⟨jU, t₁, hU, ⟨a₁⟩⟩ := hU
  obtain ⟨jV, t₂, hV, ⟨a₂⟩⟩ := hV
  have hk : (jU ≫ X.homOfLE le_sup_left) ≫ (U ⊔ V).ι = j := by rw [Category.assoc, Scheme.homOfLE_ι, hU]
  obtain ⟨k₁, s₁, hk₁, ⟨b₁⟩⟩ := exists_trace _ hk hU a₁
  obtain ⟨k₂, s₂, hk₂, ⟨b₂⟩⟩ := exists_trace _ hk hV a₂
  have hc : (U ⊔ V).ι ⁻¹ᵁ U ⊔ (U ⊔ V).ι ⁻¹ᵁ V = ⊤ := by
    rw [← Scheme.Hom.preimage_sup, Scheme.Opens.ι_preimage_self]
  obtain ⟨t, ha⟩ := (h.restrict _ hk).glue_top hdvr hc hk₁ hk₂ b₁ b₂ hp
  exact ⟨_, t, hk, ha⟩

end

end GlobalTheory.TripleGlue

theorem GlobalTheory.exists_sab_glue_of_common_generic : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X₀ : Scheme.{0}) (j : X₀ ⟶ X) (t₀ : SAB H X₀) (I : Type) [Finite I] (U : I → X.Opens) (jU : ∀ i, X₀ ⟶ (U i).toScheme) (t : ∀ i, SAB H (U i).toScheme) (a : ∀ i, SABMap t₀ (t i) (jU i)), Nonempty I → (Geo.Tor.IsNormalScheme X ∧ ∃ z : X ⟶ Sp ℤ, LocallyOfFiniteType z ∧ Flat z) → IsPreimmersion j → Flat j → IsDominant j → QuasiCompact j → IsProper t₀.G.hom → ⨆ i, U i = ⊤ → (∀ i, jU i ≫ (U i).ι = j) → ∃ (t' : SAB H X) (a' : SABMap t₀ t' j) (n : ∀ i, SABMap (t i) t' (U i).ι), ∀ i, (a i).φ ≫ (n i).φ = a'.φ := by
  intro hdvr E _ _ _ H X X₀ j t₀ I _ U jU t a hI hX h₁ h₂ h₃ h₄ hp hcov hj
  have h : TripleGlue.DensePart j := ⟨hX, h₁, h₂, h₃, h₄⟩
  have := Fintype.ofFinite I
  have key : ∃ (k : X₀ ⟶ (Finset.univ.sup' Finset.univ_nonempty U).toScheme) (s : SAB H _),
      k ≫ (Finset.univ.sup' Finset.univ_nonempty U).ι = j ∧ Nonempty (SABMap t₀ s k) :=
    Finset.sup'_induction (p := fun W : X.Opens => ∃ (k : X₀ ⟶ W.toScheme) (s : SAB H W.toScheme),
      k ≫ W.ι = j ∧ Nonempty (SABMap t₀ s k)) _ _ (fun _ hU _ hV => h.glue_sup hdvr hp hU hV)
      (fun i _ => ⟨jU i, t i, hj i, ⟨a i⟩⟩)
  rw [Finset.sup'_univ_eq_ciSup, hcov] at key
  obtain ⟨k, s, hk, ⟨b⟩⟩ := key
  have e : j ≫ X.topIso.inv = k := by
    rw [← hk, Category.assoc]
    exact (congrArg (k ≫ ·) X.topIso.hom_inv_id).trans (Category.comp_id _)
  obtain ⟨t', a', -, -⟩ := TripleGlue.exists_fac b _ e
  choose n hn using fun i => (h.restrict _ (hj i)).exists_map hdvr (hj i) a' (a i) hp
  exact ⟨t', a', n, hn⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSemiAbelianTripleGlueCommonGenericPartStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_semiAbelianTriple_glue_common_genericPart : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X₀ : Scheme.{0}) (j : X₀ ⟶ X) (t₀ : SAB H X₀) (I : Type) [Finite I] (U : I → X.Opens) (jU : ∀ i, X₀ ⟶ (U i).toScheme) (t : ∀ i, SAB H (U i).toScheme) (a : ∀ i, SABMap t₀ (t i) (jU i)), Nonempty I → (Geo.Tor.IsNormalScheme X ∧ ∃ z : X ⟶ Sp ℤ, LocallyOfFiniteType z ∧ Flat z) → IsPreimmersion j → Flat j → IsDominant j → QuasiCompact j → IsProper t₀.G.hom → ⨆ i, U i = ⊤ → (∀ i, jU i ≫ (U i).ι = j) → ∃ (t' : SAB H X) (a' : SABMap t₀ t' j) (n : ∀ i, SABMap (t i) t' (U i).ι), ∀ i, (a i).φ ≫ (n i).φ = a'.φ := by
  first | exact @GlobalTheory.exists_sab_glue_of_common_generic | exact GlobalTheory.exists_sab_glue_of_common_generic | (intros; apply GlobalTheory.exists_sab_glue_of_common_generic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegDataFiniteUnramified
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.SiegClause

theorem lbIso_pull_pull {X X' X'' : Scheme.{0}} {L : LB X} {L' : LB X'} {φ : X' ⟶ X} (h : LBIso L' (L.pull φ))
    (ψ : X'' ⟶ X') : LBIso (L'.pull ψ) (L.pull (ψ ≫ φ)) :=
  LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull L' ψ ψ rfl) (chartPullSame L _ _ _ ψ fun _ => rfl) h

theorem lbIso_lam_pull {S : Scheme.{0}} {A B : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
    (e : A ⟶ B) [IsMonHom e] {L : LB A.left} {M : LB B.left} (hL : L.IsLB) (hM : M.IsLB)
    (h : LBIso L (M.pull e.left)) : LBIso (abelian₂ A L) ((abelian₂ B M).pull (e ⊗ₘ e).left) := by
  have pa : ∀ I : Finset (Fin 2), psum A (x2 A) I ≫ e = (e ⊗ₘ e) ≫ psum B (x2 B) I := by
    intro I
    refine (psum_hom (MonoidHom.mk' (fun z : G2 A ⟶ A => z ≫ e) fun a b => MonObj.mul_comp a b _) _ I).trans
      (Eq.trans (congrArg (fun z => psum B z I) (funext fun k => ?_)) (psum_hom (preHom (e ⊗ₘ e)) _ I).symm)
    fin_cases k
    · exact (tensorHom_fst e e).symm
    · exact (tensorHom_snd e e).symm
  have hB : (abelian₂ B M).IsLB := DVR.linComb_isLB M hM _ _
  have r : LBIso (abelian₂ B M) (abelian₂ B M) := GlobalTheory.PolBaseChange.lbIso_refl hB
  have h₁ : LBIso (abelian₂ A L) (abelian₂ A (M.pull e.left)) := GlobalTheory.PowPrimitive.lbIso_linComb h _ _
  have h₂ : LBIso (abelian₂ A (M.pull e.left)) ((abelian₂ B M).pull (e ⊗ₘ e).left) :=
    LBIso.chartPull (chartPullLinComb M e.left (K := ULift.{0} (Finset (Fin 2)))
      (fun I => (psum A (x2 A) I.down).left) (fun I => (psum B (x2 B) I.down).left)
      (fun I => (-1) ^ (2 - I.down.card)) (e ⊗ₘ e).left (fun I => congrArg (fun z => z.left) (pa I.down)))
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (abelian₂ B M) _ _ rfl) r
  exact LBIso.trans (DVR.linComb_isLB L hL _ _) (DVR.linComb_isLB _ (pull_isLB hM _) _ _) (pull_isLB hB _) h₁ h₂

end GlobalTheory.ZM.SiegClause
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ImportsTer
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UnifMove

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT GlobalTheory.ArcPull GlobalTheory.PullLinear in
theorem exists_pull {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {I : Ideal R}
    {I' : Ideal R'} (hR : AdmBase R I) (hR' : AdmBase R' I') (g : R →+* R') (hg : Function.Injective g)
    (hI : I.map g ≤ I') (gK : FractionRing R →+* FractionRing R') (sq : spMap gK ≫ jK R = jK R' ≫ spMap g)
    {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))}
    [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (U : Unif I D A G) :
    ∃ (D' : DegData R' I') (hD : IsPullDeg g D.toPre D'.toPre) (A' : PolAV (Spec (CommRingCat.of (FractionRing R'))))
      (gA : A'.A.left ⟶ A.A.left) (U' : Unif I' D' A' ((Over.pullback (specOf g)).obj G)),
      IsPullUnif g hD (Iso.refl _) U U' ∧ IsGrpPullback A'.A A.A (spMap gK) gA ∧ LBIso A'.L (A.L.pull gA) ∧
      U'.gen.hom.left ≫ gA ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) =
        pullback.fst ((Over.pullback (specOf g)).obj G).hom (jK R') ≫ pullback.fst G.hom (spMap g) := by
  have hP : PolBaseChangeSt := GlobalTheory.abelianSchemeLaws_all.1.polBaseChange
  have hU : UnifBaseChangeSt := GlobalTheory.UnifPullGuards.unifBaseChange_holds
  have hψ : PsiOnExistsSt := psiOnExists
  obtain ⟨A', gA, pA, dA, mA, tA⟩ := hP _ _ (spMap gK) A
  have gpA : IsGrpPullback A'.A A.A (spMap gK) gA := ⟨pA, fun T x y x₀ y₀ hx hy => by
    have e₁ : x₀ = Out.toBase pA.w x := Over.OverMorphism.ext hx
    have e₂ : y₀ = Out.toBase pA.w y := Over.OverMorphism.ext hy
    rw [e₁, e₂, ← mA]; rfl⟩
  have gpG := ThetaBaseChange.grp_generic U.toUnifPre
  have gp' : IsGrpPullback ((Over.pullback (jK R')).obj ((Over.pullback (specOf g)).obj G)) G (spMap gK ≫ jK R)
      (pullback.fst ((Over.pullback (specOf g)).obj G).hom (jK R') ≫ pullback.fst G.hom (spMap g)) :=
    ((isGrpPullback_pullback ((Over.pullback (specOf g)).obj G) (jK R')).comp (isGrpPullback_pullback G (spMap g))).congr sq.symm rfl
  obtain ⟨eA, mE, heA⟩ := grpPullback_iso gp' (gpA.comp gpG)
  have hgi : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have hbc : (Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g) = pullback.fst G.hom (spMap g) :=
    Category.id_comp _
  have wA : LBIso (A'.L.pull eA.hom.left) (U.LG.L.pull (pullback.fst ((Over.pullback (specOf g)).obj G).hom (jK R') ≫
      (Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g))) := by
    refine LBIso.trans (pull_isLB A'.isLB _) (pull_isLB (pull_isLB A.isLB gA) eA.hom.left)
      (pull_isLB U.LG.isLB _)
      ((LBIso.symm tA).chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull A'.L _ _ rfl) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (A.L.pull gA) _ _ rfl)) ?_
    refine LBIso.chartPull (h := eA.hom.left ≫ gA ≫ U.gen.inv.left)
      (chartPullLinComb A.L gA (fun _ => eA.hom.left) (fun _ => U.gen.hom.left) _ _ fun _ => ?_)
      (chartPullSame U.LG.L _ (fun _ => pullback.fst G.hom (jK R)) _ _ fun _ => ?_) U.ext
    · rw [Category.assoc, Category.assoc, hgi, Category.comp_id]
    · rw [hbc, ← heA]; simp only [Category.assoc]
  have he : eSec ((Over.pullback (specOf g)).obj G) ≫ (Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g) = specOf g ≫ eSec G := by
    rw [hbc]; exact (cubeMapOf (isGrpPullback_pullback G (spMap g))).e_comm
  have hr : (rigPullOf (G := G) (G' := (Over.pullback (specOf g)).obj G) _ (specOf g) he U.LG.L U.LG.rig).IsGen :=
    LBxP.isGen_pullAlong U.LG.L _ (specOf g) (fun _ : PUnit => eSec G) (fun _ => 1) (fun _ => eSec ((Over.pullback (specOf g)).obj G))
      (fun _ => he) U.LG.rig U.LG.rigGen
  let L' : RigLB ((Over.pullback (specOf g)).obj G) := ⟨U.LG.L.pull ((Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g)),
    rigPullOf (G := G) (G' := (Over.pullback (specOf g)).obj G) _ (specOf g) he U.LG.L U.LG.rig, pull_isLB U.LG.isLB _, hr⟩
  obtain ⟨Wo, hWo, hψ⟩ := hψ R I hR D
  have hgen : (specOf g).base (genericPoint (Spec (CommRingCat.of R'))) ∈ Wo := by
    have : (specOf g).base (genericPoint (Spec (CommRingCat.of R'))) = genericPoint (Spec (CommRingCat.of R)) := by
      rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
      exact PrimeSpectrum.ext (Ideal.comap_bot_of_injective g hg)
    rw [this]; exact hWo
  have mR : IsMonHom (Iso.refl ((Over.pullback (specOf g)).obj G)).hom := by show IsMonHom (𝟙 _); infer_instance
  obtain ⟨D', hD, U', -, hgenU, hPU⟩ := hU R R' I I' hR hR' g hI D A G hG U Wo hψ hgen ((Over.pullback (specOf g)).obj G)
    (Iso.refl _) mR A' dA eA mE wA L' (idIso _) he (idIso_isGen L'.isLB) (fun p => hr p.1 p.2)
  exact ⟨D', hD, A', gA, U', hPU, gpA, LBIso.symm tA, by rw [hgenU]; exact heA⟩

end GlobalTheory.UnifMove

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ArcClauseOfNotFrac
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj NumberField

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ArcClauseCompare

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.TorusExt GlobalTheory.ArcInputCompare GlobalTheory.ArcDataDescent GlobalTheory.LN
open scoped CategoryTheory.Obj

section Bundles

variable {X X' T : Scheme.{0}} {K : Type} [Fintype K] {L' : LB X'} {L : LB X} {φ : X' ⟶ X}
  {w : LB.Iso L' (L.pull φ)} {a : K → (T ⟶ X')} {b : K → (T ⟶ X)} {ε : K → ℤ}
  {t' : LB.Gen (LB.LinComb L' a ε)} {t : LB.Gen (LB.LinComb L b ε)} {z : Γ(T, ⊤)ˣ}

end Bundles

theorem qkToAkU_of_equiv {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    [IsCommMonObj G] (U : UnifPre I D A G) {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ} (hk : 1 ≤ k)
    {p q : QkPt D.toPre F k} (e : QkPt.Equiv D.toPre F p q) {x : TFK (R := R) F ⟶ A.A} (h : QkToAkU U F k p x) :
    QkToAkU U F k q x := by
  obtain ⟨z, hy, g, hι, hadd⟩ := e
  refine fun w₀ hw₀ => ⟨(h w₀ hw₀).1, fun θ hθ => ?_⟩
  obtain ⟨w, hw, H⟩ := (h w₀ hw₀).2 θ hθ
  obtain ⟨w₂, hw₂, H₂⟩ := QkShift.qk_shift globalFns_holds R D.toPre D.tau_bimult F k hk p q z g hy hι hadd w hw
  exact ⟨w₂, hw₂, fun t t' s s' a b c => H₂ s s' (H t t' s s' a b c)⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {c : Coeff l}
  {O : Type} [CommRing O] {β : O →+* c.F} {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'}
  {R : Type} [CommRing R] [IsDomain R] {f : O' →+* R} {u : R}

section Transport

open ArcTransport

variable {a : ArcIn D l β O' b} {P : DegPre R} [Module (𝓞 E) P.X] {φ : P.P.A.left ⟶ a.D₀.P.A.left}
  {w : LB.Iso P.P.L (a.D₀.P.L.pull φ)} {e : a.D₀.X ≃ₗ[𝓞 E] P.X}
  {F F' : Type} [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing O') F]
  [Field F'] [Algebra (FractionRing R) F'] [Algebra (FractionRing O') F'] (σ : F →+* F')
  (h₁ : σ.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F')
  (h₂ : σ.comp (algebraMap (FractionRing O') F) = algebraMap (FractionRing O') F')

variable {oP : letI := H.starRing; P.OAct (𝓞 E)} {he : eSec P.P.A ≫ φ = spMap f ≫ eSec a.D₀.P.A}
  (hW : Match a f u P oP φ he w e)
  (hF : ∀ x, algebraMap (FractionRing O') F (algebraMap O' _ x) = algebraMap (FractionRing R) F (algebraMap R _ (f x)))

end Transport

section Twist

variable (x : TateUniformizationInput.ArcInput D c β O' b) (hf : Function.Injective f) (hu : u ≠ 0) {I : Ideal R}
  (Δ : UniformTorsionIsomorphism.OData H I) (φ : Δ.D.toPre.P.A.left ⟶ x.P.P.A.left) (w : LB.Iso Δ.D.toPre.P.L (x.P.P.L.pull φ))
  (e : x.P.X ≃ₗ[𝓞 E] Δ.D.toPre.X)

end Twist

variable {Xo : Moduli D l} (Y : Model Xo c β)

section Level

variable {I : Ideal R} {χ : Sp R ⟶ Y.X} {t : SAB H (Sp R)} (m : SABMap t Y.t χ) (P : PELUnif I t)

variable {Y m P}

end Level

end GlobalTheory.ArcClauseCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.AdmBaseOfCompleteDvr
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UnifDvrCompare
open GlobalTheory.UU GlobalTheory.LN

theorem exists_point_of_fixed {F F' : Type} [Field F] [Field F'] [Algebra F F'] [IsGalois F F'] {X : Scheme.{0}}
    (x' : Sp F' ⟶ X) (h : ∀ σ : Gal(F'/F), spMap (σ : F' →+* F') ≫ x' = x') :
    ∃ x : Sp F ⟶ X, spMap (algebraMap F F') ≫ x = x' := by
  obtain ⟨⟨y, f⟩, rfl⟩ := (Scheme.SpecToEquivOfField F' X).symm.surjective x'
  have e : (Scheme.SpecToEquivOfField F' X).symm ⟨y, f⟩ = Spec.map f ≫ X.fromSpecResidueField y := rfl
  rw [e] at h ⊢
  have hf : ∀ a, f.hom a ∈ (algebraMap F F').range := fun a => by
    refine IntermediateField.mem_bot.1 ((InfiniteGalois.mem_bot_iff_fixed _).2 fun σ => ?_)
    have := h σ
    rw [← Category.assoc, cancel_mono, ← Spec.map_comp] at this
    exact congrArg (fun q => q.hom a) (Spec.map_injective this)
  choose g hg using hf
  have inj := (algebraMap F F').injective
  let g' : X.residueField y →+* F :=
    { toFun := g
      map_one' := inj (by rw [hg, map_one, map_one])
      map_mul' := fun a b => inj (by rw [hg, map_mul, map_mul, hg, hg])
      map_zero' := inj (by rw [hg, map_zero, map_zero])
      map_add' := fun a b => inj (by rw [hg, map_add (f := _), map_add (f := _), hg, hg]) }
  refine ⟨Spec.map (CommRingCat.ofHom g') ≫ X.fromSpecResidueField y, ?_⟩
  rw [← Category.assoc, ← Spec.map_comp]
  congr 2
  exact CommRingCat.hom_ext (RingHom.ext hg)

section Totality

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D D' : DegData R I}
  {A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  [IsCommMonObj G]

end Totality

section HidaSetting

variable {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {A : PolAV (Spec (CommRingCat.of (FractionRing V)))}
  {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G]

end HidaSetting

section Triples

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

end Triples

end GlobalTheory.UnifDvrCompare
end
end
