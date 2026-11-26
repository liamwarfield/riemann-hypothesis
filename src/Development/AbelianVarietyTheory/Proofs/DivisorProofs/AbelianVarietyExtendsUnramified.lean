module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuliLawsCoefficientFieldChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClsLocEqOfIsLocComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlmostNormClassCount
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyExtendsUnramified
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyExtendsUnramified
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UnramifiedClosure

theorem injective_of_map_maximalIdeal {R W : Type} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Algebra R W]
    (h : (maximalIdeal R).map (algebraMap R W) = maximalIdeal W) :
    Function.Injective (algebraMap R W) := by
  rw [RingHom.injective_iff_ker_eq_bot]
  by_contra hne
  have hp : (RingHom.ker (algebraMap R W)).IsPrime := RingHom.ker_isPrime _
  have hm : RingHom.ker (algebraMap R W) = maximalIdeal R := IsLocalRing.eq_maximalIdeal (hp.isMaximal hne)
  apply IsDiscreteValuationRing.not_a_field W
  rw [← h, ← hm]
  exact (Ideal.map_eq_bot_iff_le_ker _).2 le_rfl

variable (R K W K' : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
  [Algebra R K] [IsFractionRing R K] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
  [Field K'] [Algebra W K'] [IsFractionRing W K'] [Algebra R W] [Algebra K K'] [Algebra R K']
  [IsScalarTower R W K'] [IsScalarTower R K K']

theorem isLocalization (h : (maximalIdeal R).map (algebraMap R W) = maximalIdeal W) :
    IsLocalization (Algebra.algebraMapSubmonoid W (nonZeroDivisors R)) K' := by
  have hinj := injective_of_map_maximalIdeal h
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hϖW : Irreducible (algebraMap R W ϖ) := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer, ← h,
      (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.map_span,
      Set.image_singleton]
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, r, hr, rfl⟩
    refine IsUnit.mk0 _ ?_
    rw [ne_eq, IsFractionRing.to_map_eq_zero_iff]
    exact fun h0 => nonZeroDivisors.ne_zero hr (hinj (by rw [map_zero]; exact h0))
  · intro z
    obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := W) z
    have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy0 hϖW
    refine ⟨⟨x * ↑u⁻¹, ⟨algebraMap R W (ϖ ^ n), ϖ ^ n,
      mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ hϖ.ne_zero), rfl⟩⟩, ?_⟩
    have hu : algebraMap W K' ↑u * algebraMap W K' ↑u⁻¹ = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have hp : algebraMap W K' (algebraMap R W ϖ) ≠ 0 := by
      rw [ne_eq, IsFractionRing.to_map_eq_zero_iff]; exact hϖW.ne_zero
    have hu0 : algebraMap W K' ↑u ≠ 0 := by
      rw [ne_eq, IsFractionRing.to_map_eq_zero_iff]; exact u.ne_zero
    simp only [map_pow, map_mul]
    field_simp
    linear_combination (-(algebraMap W K' x)) * hu
  · intro x y hxy
    exact ⟨1, by simpa using IsFractionRing.injective W K' hxy⟩

theorem isPushout (h : (maximalIdeal R).map (algebraMap R W) = maximalIdeal W) :
    Algebra.IsPushout R K W K' := by
  haveI := isLocalization R W K' h
  constructor
  exact (isLocalizedModule_iff_isBaseChange (nonZeroDivisors R) K _).1
    (isLocalizedModule_iff_isLocalization.2 this)

theorem isPullback_spec (h : (maximalIdeal R).map (algebraMap R W) = maximalIdeal W) :
    IsPullback (spMap (algebraMap K K')) (spMap (algebraMap W K')) (spMap (algebraMap R K))
      (spMap (algebraMap R W)) := by
  haveI := isPushout R K W K' h
  exact isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_of_isPushout R K W K')

theorem flat_spec (h : (maximalIdeal R).map (algebraMap R W) = maximalIdeal W) :
    Flat (spMap (algebraMap R W)) := by
  have hinj := injective_of_map_maximalIdeal h
  rw [HasRingHomProperty.Spec_iff (P := @Flat)]
  refine GlobalTheory.ringHom_flat_of_injective_of_isUnit (algebraMap R W) (algebraMap W (FractionRing W))
    (IsFractionRing.injective W (FractionRing W)) fun t ht => IsUnit.mk0 _ ?_
  rw [ne_eq, IsFractionRing.to_map_eq_zero_iff]
  exact fun h0 => ht (hinj (by rw [h0, map_zero]))

end GlobalTheory.UnramifiedClosure

namespace GlobalTheory.UnramifiedClosure

theorem schDom_spMap {A B : Type} [CommRing A] [CommRing B] [IsReduced A] (φ : A →+* B)
    (hφ : Function.Injective φ) : IsSchemeTheoreticallyDominant (spMap φ) := by
  haveI : IsDominant (spMap φ) := by
    rw [isDominant_iff]
    show DenseRange (PrimeSpectrum.comap φ)
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot φ).1 hφ]
    exact bot_le
  exact IsSchemeTheoreticallyDominant.of_isDominant _

end GlobalTheory.UnramifiedClosure

open GlobalTheory.UnramifiedClosure in
theorem GlobalTheory.UnramifiedClosure.closure_baseChange : ∀ (R K W K' : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] [Algebra R W] [Algebra K K'] [Algebra R K'] [IsScalarTower R W K'] [IsScalarTower R K K'], (maximalIdeal R).map (algebraMap R W) = maximalIdeal W → ∀ (P : Over (Sp R)), QuasiSeparated P.hom → ∀ (A : Over (Sp K)), QuasiCompact A.hom → ∀ (G : Over (Sp W)), QuasiCompact G.hom → Flat G.hom → ∀ (e : (Over.pullback (spMap (algebraMap W K'))).obj G ≅ (Over.pullback (spMap (algebraMap K K'))).obj A) (iA : A.left ⟶ P.left) (hA : iA ≫ P.hom = A.hom ≫ spMap (algebraMap R K)), IsClosedImmersion (pullback.lift iA A.hom hA) → ∀ (iG : G.left ⟶ P.left) (hG : iG ≫ P.hom = G.hom ≫ spMap (algebraMap R W)), IsClosedImmersion (pullback.lift iG G.hom hG) → e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K')) ≫ iA = pullback.fst G.hom (spMap (algebraMap W K')) ≫ iG → ∃ (X : Over (Sp R)) (a : A.left ⟶ X.left) (g : G.left ⟶ X.left), IsPullback a A.hom X.hom (spMap (algebraMap R K)) ∧ IsPullback g G.hom X.hom (spMap (algebraMap R W)) ∧ e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K')) ≫ a = pullback.fst G.hom (spMap (algebraMap W K')) ≫ g := by
  intro R K W K' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hm P hP A hAq G hGq hGf e iA hA hcA iG hG hcG hcomp

  have hjp : IsPreimmersion (spMap (algebraMap R K)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have hjf : Flat (spMap (algebraMap R K)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat K (nonZeroDivisors R))
  have hjW : Flat (spMap (algebraMap R W)) := flat_spec R W hm
  have hsq := isPullback_spec R K W K' hm
  have hqc : QuasiCompact iA := by
    have : QuasiCompact (iA ≫ P.hom) := by rw [hA]; infer_instance
    exact QuasiCompact.of_comp iA P.hom
  have hdom : IsSchemeTheoreticallyDominant iA.toImage := GlobalTheory.isSchemeTheoreticallyDominant_toImage iA
  let X : Over (Sp R) := Over.mk (iA.imageι ≫ P.hom)
  have hXh : X.hom = iA.imageι ≫ P.hom := rfl
  have hXa : iA.toImage ≫ X.hom = A.hom ≫ spMap (algebraMap R K) := by
    rw [hXh, Scheme.Hom.toImage_imageι_assoc, hA]
  have : MorphismProperty.IsStableUnderComposition @IsClosedImmersion.{0} :=
    ⟨fun f g hf hg ↦ @IsClosedImmersion.comp _ _ _ f g hf hg⟩

  let t : A.left ⟶ pullback X.hom (spMap (algebraMap R K)) := pullback.lift iA.toImage A.hom hXa
  let mK : pullback X.hom (spMap (algebraMap R K)) ⟶ pullback P.hom (spMap (algebraMap R K)) :=
    pullback.map _ _ _ _ iA.imageι (𝟙 _) (𝟙 _) (Category.comp_id _) (by simp)
  have hmK : IsClosedImmersion mK :=
    MorphismProperty.pullbackMap (P := @IsClosedImmersion.{0}) inferInstance inferInstance rfl (by simp)
  have htm : t ≫ mK = pullback.lift iA A.hom hA := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_fst,
        Scheme.Hom.toImage_imageι]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, pullback.lift_snd,
        Category.comp_id]
  have : IsClosedImmersion (t ≫ mK) := htm ▸ hcA
  have ht : IsClosedImmersion t := IsClosedImmersion.of_comp_isClosedImmersion t mK
  have hpb : IsPullback (𝟙 A.left) t iA.toImage (pullback.fst X.hom (spMap (algebraMap R K))) :=
    IsPullback.of_horiz_isIso_mono ⟨by rw [Category.id_comp, pullback.lift_fst]⟩
  have htd : IsSchemeTheoreticallyDominant t := .of_isPullback hpb
  have : IsIso t := IsClosedImmersion.isIso_iff_ker_eq_bot.mpr t.ker_eq_bot
  have hIa : IsPullback iA.toImage A.hom X.hom (spMap (algebraMap R K)) :=
    IsPullback.of_iso_pullback ⟨hXa⟩ (asIso t) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

  have hAK : IsPullback (pullback.fst A.hom (spMap (algebraMap K K')))
      (pullback.snd A.hom (spMap (algebraMap K K')) ≫ spMap (algebraMap W K'))
      (A.hom ≫ spMap (algebraMap R K)) (spMap (algebraMap R W)) :=
    (IsPullback.of_hasPullback A.hom (spMap (algebraMap K K'))).paste_vert hsq
  let mW : pullback X.hom (spMap (algebraMap R W)) ⟶ pullback P.hom (spMap (algebraMap R W)) :=
    pullback.map _ _ _ _ iA.imageι (𝟙 _) (𝟙 _) (Category.comp_id _) (by simp)
  have hmW : IsClosedImmersion mW :=
    MorphismProperty.pullbackMap (P := @IsClosedImmersion.{0}) inferInstance inferInstance rfl (by simp)
  let n : pullback (A.hom ≫ spMap (algebraMap R K)) (spMap (algebraMap R W)) ⟶
      pullback X.hom (spMap (algebraMap R W)) :=
    pullback.map _ _ _ _ iA.toImage (𝟙 _) (𝟙 _) (by rw [Category.comp_id, hXa]) (by simp)
  have hL : IsPullback (pullback.fst (A.hom ≫ spMap (algebraMap R K)) (spMap (algebraMap R W))) n
      iA.toImage (pullback.fst X.hom (spMap (algebraMap R W))) := by
    refine IsPullback.of_bot ?_ (pullback.lift_fst _ _ _).symm
      (IsPullback.of_hasPullback X.hom (spMap (algebraMap R W)))
    have h1 : n ≫ pullback.snd X.hom (spMap (algebraMap R W)) =
        pullback.snd (A.hom ≫ spMap (algebraMap R K)) (spMap (algebraMap R W)) := by
      rw [pullback.lift_snd, Category.comp_id]
    rw [h1, hXa]
    exact IsPullback.of_hasPullback _ _
  have hn : IsSchemeTheoreticallyDominant n := .of_isPullback hL
  have hsd : IsSchemeTheoreticallyDominant (spMap (algebraMap W K')) :=
    schDom_spMap _ (IsFractionRing.injective W K')
  have hu : IsSchemeTheoreticallyDominant (pullback.fst G.hom (spMap (algebraMap W K'))) :=
    inferInstance
  have he : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  let v : pullback G.hom (spMap (algebraMap W K')) ⟶ pullback X.hom (spMap (algebraMap R W)) :=
    e.hom.left ≫ hAK.isoPullback.hom ≫ n
  have hv : IsSchemeTheoreticallyDominant v := inferInstance
  let cG : G.left ⟶ pullback P.hom (spMap (algebraMap R W)) := pullback.lift iG G.hom hG
  have hes : e.hom.left ≫ pullback.snd A.hom (spMap (algebraMap K K')) =
      pullback.snd G.hom (spMap (algebraMap W K')) := Over.w e.hom
  have hcomm : pullback.fst G.hom (spMap (algebraMap W K')) ≫ cG = v ≫ mW := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← hcomp]
      simp only [v, mW, n, pullback.map, Category.assoc]
      simp only [pullback.lift_fst, pullback.lift_fst_assoc, Category.assoc,
        IsPullback.isoPullback_hom_fst_assoc, Scheme.Hom.toImage_imageι]
    · rw [Category.assoc, pullback.lift_snd]
      simp only [v, mW, n, Category.assoc]
      rw [pullback.lift_snd, Category.comp_id (pullback.snd X.hom (spMap (algebraMap R W))),
        pullback.lift_snd,
        Category.comp_id (pullback.snd (A.hom ≫ spMap (algebraMap R K)) (spMap (algebraMap R W))),
        IsPullback.isoPullback_hom_snd, reassoc_of% hes]
      exact pullback.condition
  have hker : mW.ker = cG.ker := by
    have h1 : (pullback.fst G.hom (spMap (algebraMap W K')) ≫ cG).ker = cG.ker := by
      rw [Scheme.Hom.ker_comp, Scheme.Hom.ker_eq_bot, Scheme.IdealSheafData.map_bot]
    have h2 : (v ≫ mW).ker = mW.ker := by
      rw [Scheme.Hom.ker_comp, Scheme.Hom.ker_eq_bot, Scheme.IdealSheafData.map_bot]
    rw [← h1, ← h2, hcomm]
  let ψ : G.left ⟶ pullback X.hom (spMap (algebraMap R W)) := IsClosedImmersion.lift mW cG hker.le
  have hψ : ψ ≫ mW = cG := IsClosedImmersion.lift_fac _ _ _
  have : IsIso ψ := IsClosedImmersion.isIso_lift mW cG hker
  have hψs : ψ ≫ pullback.snd X.hom (spMap (algebraMap R W)) = G.hom := by
    have h := congrArg (· ≫ pullback.snd P.hom (spMap (algebraMap R W))) hψ
    simp only [Category.assoc] at h
    rwa [pullback.lift_snd, Category.comp_id, pullback.lift_snd] at h
  have hIg : IsPullback (ψ ≫ pullback.fst X.hom (spMap (algebraMap R W))) G.hom X.hom
      (spMap (algebraMap R W)) :=
    IsPullback.of_iso_pullback ⟨by rw [Category.assoc, pullback.condition, reassoc_of% hψs]⟩
      (asIso ψ) rfl hψs
  refine ⟨X, iA.toImage, ψ ≫ pullback.fst X.hom (spMap (algebraMap R W)), hIa, hIg, ?_⟩
  rw [← cancel_mono iA.imageι]
  have h3 : pullback.fst X.hom (spMap (algebraMap R W)) ≫ iA.imageι =
      mW ≫ pullback.fst P.hom (spMap (algebraMap R W)) := (pullback.lift_fst _ _ _).symm
  simp only [Category.assoc]
  simp only [h3, ← Category.assoc, hψ, Scheme.Hom.toImage_imageι]
  simpa only [Category.assoc, cG, pullback.lift_fst] using hcomp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyExtendsUnramifiedStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_variety_extends_unramified : ∀ (R K W K' : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] [Algebra R W] [Algebra K K'] [Algebra R K'] [IsScalarTower R W K'] [IsScalarTower R K K'], (maximalIdeal R).map (algebraMap R W) = maximalIdeal W → ∀ (P : Over (Sp R)), QuasiSeparated P.hom → ∀ (A : Over (Sp K)), QuasiCompact A.hom → ∀ (G : Over (Sp W)), QuasiCompact G.hom → Flat G.hom → ∀ (e : (Over.pullback (spMap (algebraMap W K'))).obj G ≅ (Over.pullback (spMap (algebraMap K K'))).obj A) (iA : A.left ⟶ P.left) (hA : iA ≫ P.hom = A.hom ≫ spMap (algebraMap R K)), IsClosedImmersion (pullback.lift iA A.hom hA) → ∀ (iG : G.left ⟶ P.left) (hG : iG ≫ P.hom = G.hom ≫ spMap (algebraMap R W)), IsClosedImmersion (pullback.lift iG G.hom hG) → e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K')) ≫ iA = pullback.fst G.hom (spMap (algebraMap W K')) ≫ iG → ∃ (X : Over (Sp R)) (a : A.left ⟶ X.left) (g : G.left ⟶ X.left), IsPullback a A.hom X.hom (spMap (algebraMap R K)) ∧ IsPullback g G.hom X.hom (spMap (algebraMap R W)) ∧ e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K')) ≫ a = pullback.fst G.hom (spMap (algebraMap W K')) ≫ g := by
  first | exact @GlobalTheory.UnramifiedClosure.closure_baseChange | exact GlobalTheory.UnramifiedClosure.closure_baseChange | (intros; apply GlobalTheory.UnramifiedClosure.closure_baseChange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormOrdKaehlerWedgeUniformiserResidueIndependent
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormOrdKaehlerWedgeUniformiserResidueIndependent
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

namespace GlobalTheory

theorem formOrd_dForm_cons_of_ord_eq_one : ∀ {K : Type} [Field K] (cK : ℂ →+* K) (F : Place cK) (m : ℕ) (π : K) (y : Fin m → K),
  F.ord π = 1 → (∀ i, y i ∈ F.ring) →
  (∀ P : MvPolynomial (Fin m) ℂ, P ≠ 0 → MvPolynomial.eval₂ cK y P ≠ 0 ∧ (MvPolynomial.eval₂ cK y P)⁻¹ ∈ F.ring) →
  TrBasis cK (Fin.cons π y : Fin (m + 1) → K) →
  (fun ω => @dite ℤ (∃ a, F.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (dForm cK (Fin.cons π y : Fin (m + 1) → K)) = 0 := by
  intro K _ cK F m π y hπ hy hP hB
  have hπ0 : π ≠ 0 := by
    rintro rfl
    simp [Place.ord] at hπ
  have hπm : π ∈ F.ring := (F.ord_nonneg_iff hπ0).1 (by rw [hπ]; norm_num)
  have hirr : Irreducible (⟨π, hπm⟩ : F.ring) := by
    obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible F.ring
    have hne : (⟨π, hπm⟩ : F.ring) ≠ 0 := fun h => hπ0 (congrArg Subtype.val h)
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne ht
    have e : π = ((u : F.ring) : K) * (t : K) ^ n := by
      simpa using congrArg Subtype.val hu
    have hu0 : ((u : F.ring) : K) ≠ 0 := (u.isUnit.map F.ring.subtype).ne_zero
    have ht0 : (t : K) ≠ 0 := fun h => ht.ne_zero (Subtype.ext h)
    have h1 : F.ord π = n := by
      rw [e, F.ord_mul hu0 (pow_ne_zero _ ht0), F.ord_eq_zero u.isUnit, F.ord_pow,
        F.ord_irreducible ht]
      simp
    obtain rfl : n = 1 := by
      rw [hπ] at h1
      exact_mod_cast h1.symm
    rw [hu, pow_one]
    exact (irreducible_units_mul u).2 ht
  refine formOrd_dForm_uniformiser_cons cK m F ⟨π, hπm⟩ (fun i => ⟨y i, hy i⟩) hirr ?_ ⟨_, hB⟩
  intro P hP0
  obtain ⟨h0, hi⟩ := hP P hP0
  have e : ((MvPolynomial.eval₂ F.const (fun i => (⟨y i, hy i⟩ : F.ring)) P : F.ring) : K) =
      MvPolynomial.eval₂ cK y P :=
    MvPolynomial.eval₂_comp_left F.ring.subtype F.const (fun i => (⟨y i, hy i⟩ : F.ring)) P
  refine IsUnit.of_mul_eq_one (⟨_, hi⟩ : F.ring) (Subtype.ext ?_)
  change ((MvPolynomial.eval₂ F.const (fun i => (⟨y i, hy i⟩ : F.ring)) P : F.ring) : K) * _ = 1
  rw [e]
  exact mul_inv_cancel₀ h0

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormOrdKaehlerWedgeUniformiserResidueIndependentStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formOrd_kaehlerWedge_uniformiser_residueIndependent_eq_zero : ∀ {K : Type} [Field K] (cK : ℂ →+* K) (F : Place cK) (m : ℕ) (π : K) (y : Fin m → K),
  F.ord π = 1 → (∀ i, y i ∈ F.ring) →
  (∀ P : MvPolynomial (Fin m) ℂ, P ≠ 0 → MvPolynomial.eval₂ cK y P ≠ 0 ∧ (MvPolynomial.eval₂ cK y P)⁻¹ ∈ F.ring) →
  TrBasis cK (Fin.cons π y : Fin (m + 1) → K) →
  (fun ω => @dite ℤ (∃ a, F.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (dForm cK (Fin.cons π y : Fin (m + 1) → K)) = 0 := by
  first | exact @GlobalTheory.formOrd_dForm_cons_of_ord_eq_one | exact GlobalTheory.formOrd_dForm_cons_of_ord_eq_one | (intros; apply GlobalTheory.formOrd_dForm_cons_of_ord_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnCutoffTopChernFormPoincareGrowth
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnCutoffTopChernFormPoincareGrowth
set_option autoImplicit false

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
set_option autoImplicit false in
private lemma mem_offHyp_iff {n : ℕ} {S : Finset (Fin n)}
    {U : Set (_root_.ReciprocityTheory.L2DbarEstimates.V n)} {v : _root_.ReciprocityTheory.L2DbarEstimates.V n} :
    v ∈ _root_.GlobalTheory.GoodTop.offHyp S U ↔ v ∈ U ∧ ∀ a ∈ S, v.ofLp a ≠ 0 := by
  unfold _root_.GlobalTheory.GoodTop.offHyp
  exact Iff.rfl

open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
set_option autoImplicit false in
private lemma continuousAt_cutoff_mul_mix_curvAt {n : ℕ} {r : Type} [Fintype r]
    [DecidableEq r] {G : _root_.ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ} {ρ : _root_.ReciprocityTheory.L2DbarEstimates.V n → ℝ} {v : _root_.ReciprocityTheory.L2DbarEstimates.V n}
    (hG : _root_.GlobalTheory.HermFrame.MContDiffAt ∞ G v) (hdet : IsUnit (G v).det) (hρ : ContinuousAt ρ v) :
    ContinuousAt (fun x => (ρ x : ℂ) * _root_.GlobalTheory.GoodTop.mixTop fun _ => _root_.GlobalTheory.GoodTop.curvAt G x)
      v := by
  refine ContinuousAt.mul (Complex.continuous_ofReal.continuousAt.comp (f := ρ) hρ) ?_
  refine _root_.GlobalTheory.GoodTop.continuousAt_mixTop (K := fun x _ => _root_.GlobalTheory.GoodTop.curvAt G x)
    fun i a b p q => ?_
  have h := hG.curv (j := 0) hdet
    (by rw [zero_add]; first | exact le_top | exact_mod_cast (le_top : ((2 : ℕ∞) ≤ ⊤)) | exact WithTop.coe_le_coe.2 le_top)
    (_root_.GlobalTheory.GoodMetric.coordVec a) (_root_.GlobalTheory.GoodMetric.coordVec b) p q
  exact h.continuousAt


open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
set_option autoImplicit false in
theorem _root_.GlobalTheory.GoodTop.integrableOn_cut_mixTop_curvAt :
    ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (S : Finset (Fin n)) (U K : Set (_root_.ReciprocityTheory.L2DbarEstimates.V n)) (G₀ G₁ : _root_.ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ) (ρ : _root_.ReciprocityTheory.L2DbarEstimates.V n → ℝ) (c : ℝ), IsOpen U → IsCompact K → K ⊆ U → (∀ v ∈ U, ∀ a ∈ S, ‖v a‖ ≤ 1 / 2) → (∀ v ∈ U, _root_.GlobalTheory.HermFrame.MContDiffAt ∞ G₀ v ∧ IsUnit (G₀ v).det) → (∀ v ∈ _root_.GlobalTheory.GoodTop.offHyp S U, _root_.GlobalTheory.HermFrame.MContDiffAt ∞ G₁ v ∧ IsUnit (G₁ v).det) → (∀ v ∈ _root_.GlobalTheory.GoodTop.offHyp S U, ∀ a i j, ‖_root_.GlobalTheory.HermFrame.conn G₁ v (_root_.GlobalTheory.GoodMetric.coordVec a) i j‖ * _root_.GlobalTheory.GoodMetric.poinWt S v a ≤ c) → (∀ v ∈ _root_.GlobalTheory.GoodTop.offHyp S U, ∀ a b i j, ‖_root_.GlobalTheory.HermFrame.curv G₁ v (_root_.GlobalTheory.GoodMetric.coordVec a) (_root_.GlobalTheory.GoodMetric.coordVec b) i j‖ * (_root_.GlobalTheory.GoodMetric.poinWt S v a * _root_.GlobalTheory.GoodMetric.poinWt S v b) ≤ c) → ContDiffOn ℝ ∞ ρ U → (∀ v ∈ U, v ∉ K → ρ v = 0) → IntegrableOn (fun v => (ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop fun _ => _root_.GlobalTheory.GoodTop.curvAt G₁ v) (_root_.GlobalTheory.GoodTop.offHyp S U) := by
  intro n r _ _ S U K G₀ G₁ ρ c hU hK hKU hS hG₀ hG₁ hconn hcurv hρ hρK
  obtain ⟨C₀, hC₀⟩ := hK.exists_bound_of_continuousOn (hρ.continuousOn.mono hKU)
  refine _root_.GlobalTheory.T.integrableOn_offCoordinateHyperplanes_of_poincareBound S U K _
    (C₀ * ((Fintype.card r : ℝ) ^ n * (n.factorial : ℝ) ^ 2 * |c| ^ n)) hU hK hKU hS ?_ ?_ ?_
  · intro v hv
    have hvU := (mem_offHyp_iff.1 hv).1
    exact (continuousAt_cutoff_mul_mix_curvAt (hG₁ v hv).1 (hG₁ v hv).2
      (hρ.contDiffAt (hU.mem_nhds hvU)).continuousAt).continuousWithinAt
  · intro v hv hvK
    rw [hρK v (mem_offHyp_iff.1 hv).1 hvK, Complex.ofReal_zero, zero_mul]
  · intro v hv hvK
    have hpos := (_root_.GlobalTheory.GoodTop.poinWt_mem_Icc_and_pos S v
      (hS v (mem_offHyp_iff.1 hv).1)).2 (mem_offHyp_iff.1 hv).2
    have hP := _root_.GlobalTheory.GoodTop.norm_mixTop_le_of_weighted
      (fun _ => _root_.GlobalTheory.GoodTop.curvAt G₁ v) (_root_.GlobalTheory.GoodMetric.poinWt S v) c hpos
      (fun _ a b p q => hcurv v hv a b p q)
    rw [norm_mul, Complex.norm_real]
    exact (mul_le_mul (hC₀ v hvK) hP (norm_nonneg _) ((norm_nonneg _).trans (hC₀ v hvK))).trans_eq
      (by ring)

end GlobalTheory.GoodTop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnCutoffTopChernFormPoincareGrowthStatement
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrableOn_cutoff_topChernForm_poincareGrowth : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (S : Finset (Fin n)) (U K : Set (V n)) (G₀ G₁ : V n → Matrix r r ℂ) (ρ : V n → ℝ) (c : ℝ), IsOpen U → IsCompact K → K ⊆ U → (∀ v ∈ U, ∀ a ∈ S, ‖v a‖ ≤ 1 / 2) → (∀ v ∈ U, MContDiffAt ∞ G₀ v ∧ IsUnit (G₀ v).det) → (∀ v ∈ offHyp S U, MContDiffAt ∞ G₁ v ∧ IsUnit (G₁ v).det) → (∀ v ∈ offHyp S U, ∀ a i j, ‖conn G₁ v (coordVec a) i j‖ * poinWt S v a ≤ c) → (∀ v ∈ offHyp S U, ∀ a b i j, ‖curv G₁ v (coordVec a) (coordVec b) i j‖ * (poinWt S v a * poinWt S v b) ≤ c) → ContDiffOn ℝ ∞ ρ U → (∀ v ∈ U, v ∉ K → ρ v = 0) → IntegrableOn (fun v => (ρ v : ℂ) * mixTop fun _ => curvAt G₁ v) (offHyp S U) := by
  first | exact @GlobalTheory.GoodTop.integrableOn_cut_mixTop_curvAt | exact GlobalTheory.GoodTop.integrableOn_cut_mixTop_curvAt | (intros; apply GlobalTheory.GoodTop.integrableOn_cut_mixTop_curvAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomEqOfCompEqId
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (RingAct)
open scoped CategoryTheory.Obj NumberField
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.IwLevel

namespace GlobalTheory.TangentStalk

theorem ker_eq_maximalIdeal {k R : Type} [Field k] [CommRing R] [IsLocalRing R] (j : k →+* R)
    (g : R →+* k) (hg : g.comp j = RingHom.id k) : RingHom.ker g = IsLocalRing.maximalIdeal R :=
  IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective g
    (fun c => ⟨j c, RingHom.congr_fun hg c⟩))

theorem ringHom_eq_of_comp_eq_id {k R : Type} [Field k] [CommRing R] [IsLocalRing R] (j : k →+* R)
    (g₁ g₂ : R →+* k) (h₁ : g₁.comp j = RingHom.id k) (h₂ : g₂.comp j = RingHom.id k) : g₁ = g₂ := by
  ext a
  have hm : a - j (g₁ a) ∈ RingHom.ker g₂ := by
    rw [ker_eq_maximalIdeal j g₂ h₂, ← ker_eq_maximalIdeal j g₁ h₁, RingHom.mem_ker, map_sub,
      show g₁ (j (g₁ a)) = g₁ a from RingHom.congr_fun h₁ (g₁ a), sub_self]
  rw [RingHom.mem_ker, map_sub, sub_eq_zero] at hm
  rw [hm]
  exact (RingHom.congr_fun h₂ (g₁ a)).symm

theorem tangent_eq_stalk_dual : ∀ (k : Type) [Field k] (A : Over (Sp k)) [GrpObj A] (x₀ : A.left), x₀ ∈ Set.range (η[A]).left.base →
    ∃ jk : k →+* A.left.presheaf.stalk x₀,
      (∀ a : A.left.presheaf.stalk x₀, ∃ c : k, a - jk c ∈ IsLocalRing.maximalIdeal (A.left.presheaf.stalk x₀)) ∧
      (∀ ψ : A.left.presheaf.stalk x₀ →+* DualNumber k, ψ.comp jk = algebraMap k (DualNumber k) →
        ∃ v : epsR k ⟶ A, IsTangent v ∧ v.left = Spec.map (CommRingCat.ofHom ψ) ≫ A.left.fromSpecStalk x₀) ∧
      (∀ ψ₁ ψ₂ : A.left.presheaf.stalk x₀ →+* DualNumber k, ψ₁.comp jk = algebraMap k (DualNumber k) →
        ψ₂.comp jk = algebraMap k (DualNumber k) →
        Spec.map (CommRingCat.ofHom ψ₁) ≫ A.left.fromSpecStalk x₀ = Spec.map (CommRingCat.ofHom ψ₂) ≫ A.left.fromSpecStalk x₀ →
        ψ₁ = ψ₂) := by
  intro k _ A _ x₀ hx
  obtain ⟨pt, rfl⟩ := hx
  have hpt : pt = IsLocalRing.closedPoint k := Subsingleton.elim (α := PrimeSpectrum k) _ _
  subst hpt
  let s : Sp k ⟶ A.left := (η[A]).left
  have hsA : s ≫ A.hom = 𝟙 _ := (η[A]).w.trans rfl
  have hr : Spec.map (Scheme.stalkClosedPointTo s) ≫ A.left.fromSpecStalk _ = s :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk s
  have hJ := Spec.map_preimage (A.left.fromSpecStalk (s.base (IsLocalRing.closedPoint k)) ≫ A.hom)

  set r := Scheme.stalkClosedPointTo s with hrdef
  set J := Spec.preimage (A.left.fromSpecStalk (s.base (IsLocalRing.closedPoint k)) ≫ A.hom) with hJdef
  have hrJ : J ≫ r = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hJ, ← Category.assoc, hr, hsA, Spec.map_id]
  have hcomp : r.hom.comp J.hom = RingHom.id k := congrArg CommRingCat.Hom.hom hrJ
  have hfst : ∀ ψ : A.left.presheaf.stalk (s.base (IsLocalRing.closedPoint k)) →+* DualNumber k,
      ψ.comp J.hom = algebraMap k (DualNumber k) →
      ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ψ).comp J.hom = RingHom.id k := by
    intro ψ hψ
    rw [RingHom.comp_assoc, hψ]
    ext c
    simp
  refine ⟨J.hom, fun a => ⟨r.hom a, ?_⟩, fun ψ hψ => ?_, fun ψ₁ ψ₂ h₁ h₂ h => ?_⟩
  · rw [← ker_eq_maximalIdeal J.hom r.hom hcomp, RingHom.mem_ker, map_sub,
      show r.hom (J.hom (r.hom a)) = r.hom a from RingHom.congr_fun hcomp _, sub_self]
  · refine ⟨Over.homMk (Spec.map (CommRingCat.ofHom ψ) ≫ A.left.fromSpecStalk _) ?_, ?_, rfl⟩
    · show Spec.map (CommRingCat.ofHom ψ) ≫ A.left.fromSpecStalk _ ≫ A.hom =
        Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))
      rw [← hJ, ← Spec.map_comp, ← hψ]
      rfl
    · show Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫
        Spec.map (CommRingCat.ofHom ψ) ≫ A.left.fromSpecStalk _ = s
      rw [← Category.assoc, ← Spec.map_comp, ← hr]
      congr 2
      ext1
      exact ringHom_eq_of_comp_eq_id J.hom _ _ (hfst ψ hψ) hcomp
  · have hloc : ∀ ψ : A.left.presheaf.stalk (s.base (IsLocalRing.closedPoint k)) →+* DualNumber k,
        ψ.comp J.hom = algebraMap k (DualNumber k) → IsLocalHom ψ := by
      intro ψ hψ
      refine ⟨fun a ha => ?_⟩
      by_contra hna
      have hm : a ∈ IsLocalRing.maximalIdeal _ := (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 hna)
      rw [← ker_eq_maximalIdeal J.hom _ (hfst ψ hψ), RingHom.mem_ker] at hm
      have hu := TrivSqZeroExt.isUnit_iff_isUnit_fst.1 ha
      simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        TrivSqZeroExt.fstHom_apply] at hm
      rw [hm] at hu
      exact not_isUnit_zero hu
    have e1 := hloc ψ₁ h₁
    have e2 := hloc ψ₂ h₂
    have hinj := (SpecToEquivOfLocalRing A.left (CommRingCat.of (DualNumber k))).symm.injective
      (a₁ := ⟨_, CommRingCat.ofHom ψ₁, e1⟩) (a₂ := ⟨_, CommRingCat.ofHom ψ₂, e2⟩) h
    have := eq_of_heq (Sigma.mk.inj_iff.mp hinj).2
    exact congrArg (fun f => f.1.hom) this
end GlobalTheory.TangentStalk
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactDiscreteSeriesOwnType
noncomputable section

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.TRGap

namespace GlobalTheory.PsCo.PcEF

open GlobalTheory.PsCo.PcEG

variable {n : ℕ}

theorem cpt_const {ε : Fin n → Bool} (h : pOf ε = 0 ∨ qOf ε = 0) (a b : Fin n) : ε a = ε b := by
  rcases h with hp | hq
  · have h1 : ∀ c, ε c = false := fun c => by
      have := Finset.filter_eq_empty_iff.1 (Finset.card_eq_zero.1 hp) (Finset.mem_univ c)
      simpa using this
    rw [h1 a, h1 b]
  · have h1 : ∀ c, ε c = true := fun c => by
      have := Finset.filter_eq_empty_iff.1 (Finset.card_eq_zero.1 hq) (Finset.mem_univ c)
      simpa using this
    rw [h1 a, h1 b]

theorem cpt_Jm_comm {ε : Fin n → Bool} (hc : ∀ a b, ε a = ε b) (M : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.Jm ε * M = M * Formalism.REAL.Jm ε := by
  ext i j
  delta Formalism.REAL.Jm
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, hc i j]
  ring

theorem cpt_Kset_eq {ε : Fin n → Bool} (hc : ∀ a b, ε a = ε b) :
    Formalism.REAL.Kset ε = Formalism.MainNotions.S.UJset ε := by
  ext g
  delta Formalism.REAL.Kset Formalism.MainNotions.S.UJset Formalism.REAL.inUJ
  simp only [Set.mem_ofPred_eq, Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  constructor
  · rintro ⟨hu, -⟩
    rw [Matrix.mul_assoc, cpt_Jm_comm hc g, ← Matrix.mul_assoc, hu, Matrix.one_mul]
  · intro h
    refine ⟨?_, (cpt_Jm_comm hc g).symm⟩
    have h2 : g.conjTranspose * g * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε := by
      rw [Matrix.mul_assoc, ← cpt_Jm_comm hc g, ← Matrix.mul_assoc]
      exact h
    have h3 := congrArg (· * Formalism.REAL.Jm ε) h2
    simp only [Matrix.mul_assoc, Formalism.REAL.Jm_mul_self, Matrix.mul_one] at h3
    exact h3

theorem compactDiscreteSeries_ownType : CptCase := by
  intro n ε lam h
  have hc := cpt_const h
  refine ⟨fun k => ?_, ?_, ?_⟩
  · have : IsEmpty {x : Fin n × Fin n // IsPhys ε x} :=
      ⟨fun x => by
        have h1 := x.2.1
        have h2 := x.2.2
        rw [hc x.1.1 x.1.2] at h1
        rw [h1] at h2
        exact Bool.noConfusion h2⟩
    unfold physDet
    exact Matrix.det_isEmpty
  · unfold sDeg sModes
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro x - ⟨h1, h2, -⟩
    rw [hc x.1 x.2] at h1
    rw [h1] at h2
    exact Bool.noConfusion h2
  · intro X _ _ D hD
    obtain ⟨hcs, hnt, hU, hirr, -, ⟨S, hS⟩, -⟩ := hD
    have := hcs
    have hKU := cpt_Kset_eq hc
    have : FiniteDimensional ℂ S := hS.1
    have hclosed : IsClosed (S : Set X) := S.isClosed_of_finiteDimensional
    have hstab : ∀ g ∈ Formalism.MainNotions.S.UJset ε, ∀ v ∈ S, D g v ∈ S := fun g hg v hv =>
      hS.2.1 g (hKU ▸ hg) v hv
    have htop : S = ⊤ := by
      rcases hirr S hclosed hstab with h0 | h0
      · exfalso
        obtain ⟨v, hv, hv0, -⟩ := hS.2.2.2.1
        rw [h0] at hv
        exact hv0 ((Submodule.mem_bot ℂ).1 hv)
      · exact h0
    subst htop
    have hga : gaW ε lam = Formalism.QuantumDeterminants.lowK ε lam := by
      funext a
      have hN : Formalism.REAL.rhoN ε a = 0 := by
        unfold Formalism.REAL.rhoN
        have e1 : (Finset.univ.filter fun b => a < b ∧ ε b ≠ ε a) = ∅ :=
          Finset.filter_eq_empty_iff.2 fun b _ hb => hb.2 (hc b a)
        have e2 : (Finset.univ.filter fun b => b < a ∧ ε b ≠ ε a) = ∅ :=
          Finset.filter_eq_empty_iff.2 fun b _ hb => hb.2 (hc b a)
        rw [e1, e2]
        simp
      have hH : rhoHol ε a = 0 := by
        unfold rhoHol
        rcases h with hp | hq
        · have ha : ε a = false := by
            have := Finset.filter_eq_empty_iff.1 (Finset.card_eq_zero.1 hp) (Finset.mem_univ a)
            simpa using this
          simp [ha, hp]
        · have ha : ε a = true := by
            have := Finset.filter_eq_empty_iff.1 (Finset.card_eq_zero.1 hq) (Finset.mem_univ a)
            simpa using this
          simp [ha, hq]
      delta gaW Formalism.QuantumDeterminants.lowK
      simp only [Pi.add_apply, Pi.sub_apply, hN, hH, add_zero]
      rfl
    refine ⟨LinearEquiv.finiteDimensional Submodule.topEquiv, hnt, hKU ▸ hU, ?_⟩
    rw [hga]
    exact hS

end GlobalTheory.PsCo.PcEF
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraWeightIntegralDominant
section
open GlobalTheory.PsCo.PcEG

noncomputable section

open Finset ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.TRGap

namespace GlobalTheory.PsCo.PcEF.HarishChandraWeightIntegral

variable {n : ℕ}

theorem card_split (ε : Fin n → Bool) (a : Fin n) :
    (univ.filter fun b => a < b ∧ ε b = ε a).card + (univ.filter fun b => b < a ∧ ε b = ε a).card + 1 =
      (univ.filter fun b => ε b = ε a).card := by
  have h : (univ.filter fun b => ε b = ε a) =
      ((univ.filter fun b => a < b ∧ ε b = ε a) ∪ (univ.filter fun b => b < a ∧ ε b = ε a)) ∪ {a} := by
    ext b
    simp only [mem_filter, mem_univ, true_and, mem_union, mem_singleton]
    constructor
    · intro h
      rcases lt_trichotomy a b with h1 | h1 | h1
      · exact Or.inl (Or.inl ⟨h1, h⟩)
      · exact Or.inr h1.symm
      · exact Or.inl (Or.inr ⟨h1, h⟩)
    · rintro ((⟨_, h⟩ | ⟨_, h⟩) | rfl)
      · exact h
      · exact h
      · rfl
  have d1 : Disjoint (univ.filter fun b => a < b ∧ ε b = ε a) (univ.filter fun b => b < a ∧ ε b = ε a) := by
    rw [disjoint_filter]
    intro x _ h1 h2
    exact lt_asymm h1.1 h2.1
  have d2 : Disjoint ((univ.filter fun b => a < b ∧ ε b = ε a) ∪ (univ.filter fun b => b < a ∧ ε b = ε a))
      {a} := by
    rw [disjoint_singleton_right]
    simp
  rw [h, card_union_of_disjoint d2, card_union_of_disjoint d1, card_singleton]

theorem p_add_q (ε : Fin n → Bool) : pOf ε + qOf ε = n := by
  delta pOf qOf
  have := card_filter_add_card_filter_not (s := (univ : Finset (Fin n))) (fun a => ε a = true)
  simpa using this

theorem gaW_eq (ε : Fin n → Bool) (lam : Fin n → ℝ) (m : Fin n → ℤ)
    (hm : ∀ a, lam a + ((n : ℝ) - 1) / 2 = m a) (a : Fin n) :
    gaW ε lam a = ((m a - (if ε a then 0 else (pOf ε : ℤ)) - ReciprocityTheory.ChartRestriction.TR.Weyl.rhoK ε a : ℤ) : ℝ) := by
  have hcR : ((univ.filter fun b => a < b ∧ ε b = ε a).card : ℝ) +
      ((univ.filter fun b => b < a ∧ ε b = ε a).card : ℝ) + 1 =
      ((univ.filter fun b => ε b = ε a).card : ℝ) := by exact_mod_cast card_split ε a
  have hpqR : (pOf ε : ℝ) + qOf ε = n := by exact_mod_cast p_add_q ε
  have hma := hm a
  delta gaW rhoC rhoHol ReciprocityTheory.ChartRestriction.TR.Weyl.rhoK
  simp only [Pi.add_apply, Pi.sub_apply]
  by_cases h : ε a = true
  · have hs : ((univ.filter fun b => ε b = ε a).card : ℝ) = pOf ε := by
      delta pOf
      rw [h]
    simp only [ite_eq_left h]
    push_cast
    linarith
  · have hs : ((univ.filter fun b => ε b = ε a).card : ℝ) = qOf ε := by
      delta qOf
      rw [Bool.eq_false_of_not_eq_true h]
    simp only [ite_eq_right h]
    push_cast
    linarith

end GlobalTheory.PsCo.PcEF.HarishChandraWeightIntegral

namespace GlobalTheory.PsCo.PcEF

theorem harishChandraWeight_integral_dominant : GaInt := by
  intro n ε lam hlam
  obtain ⟨hanti, hz⟩ := hlam
  choose z hz using hz
  let m : Fin n → ℤ := fun a => z a + ((n : ℤ) - 1)
  have hm : ∀ a, lam a + ((n : ℝ) - 1) / 2 = m a := by
    intro a
    have := hz a
    simp only [m]
    push_cast
    linarith
  let Λ : Fin n → ℤ := fun a =>
    m a - (if ε a then 0 else (pOf ε : ℤ)) - ReciprocityTheory.ChartRestriction.TR.Weyl.rhoK ε a
  have hg : gaW ε lam = fun a => (Λ a : ℝ) := funext fun a => HarishChandraWeightIntegral.gaW_eq ε lam m hm a
  refine ⟨Λ, m, hg, ?_, hm, ?_⟩
  · intro a b hab he
    have hBA : BlockAnti ε lam := by
      intro a b hab _
      have h1 := hanti hab
      have h2 : (m b : ℝ) < m a := by linarith [hm a, hm b]
      have h3 : m b < m a := by exact_mod_cast h2
      have h4 : ((m b : ℤ) : ℝ) + 1 ≤ m a := by exact_mod_cast Int.add_one_le_of_lt h3
      linarith [hm a, hm b]
    have h := lf_dom_block hBA a b hab he
    have e : lowK ε lam + (rhoHol ε - rhoN ε) = gaW ε lam := by
      funext x
      delta lowK gaW
      simp only [Pi.add_apply, Pi.sub_apply]
      ring
    rw [e, hg] at h
    have h' : (Λ b : ℝ) ≤ Λ a := h
    exact_mod_cast h'
  · intro a
    simp only [Λ, Pi.add_apply]
    ring

end GlobalTheory.PsCo.PcEF

end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisRepresentationTateModuleBaseChangeEqOneIff
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseChangePointsEquivGalois
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Published.AbVarRed

variable (K L Ω : Type) [Field K] [Field L] [Field Ω] [Algebra K L] [Algebra L Ω] [Algebra K Ω]
  [IsScalarTower K L Ω]

theorem spMap_algebraMap_tower :
    spMap (algebraMap K Ω) = spMap (algebraMap L Ω) ≫ spMap (algebraMap K L) := by
  rw [IsScalarTower.algebraMap_eq K L Ω]
  show Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  rfl

variable {K L Ω} (A : Over (Sp K))

def baseChangePt (x : ptOver L Ω ⟶ (Over.pullback (spMap (algebraMap K L))).obj A) : ptOver K Ω ⟶ A :=
  Over.homMk (x.left ≫ pullback.fst A.hom (spMap (algebraMap K L))) (by
    show (x.left ≫ pullback.fst A.hom (spMap (algebraMap K L))) ≫ A.hom = spMap (algebraMap K Ω)
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    have hx : x.left ≫ pullback.snd A.hom (spMap (algebraMap K L)) = spMap (algebraMap L Ω) := Over.w x
    rw [hx, spMap_algebraMap_tower K L Ω])

def baseChangePtInv (y : ptOver K Ω ⟶ A) : ptOver L Ω ⟶ (Over.pullback (spMap (algebraMap K L))).obj A :=
  Over.homMk (pullback.lift y.left (spMap (algebraMap L Ω)) (by
    have hy : y.left ≫ A.hom = spMap (algebraMap K Ω) := Over.w y
    rw [hy, spMap_algebraMap_tower K L Ω])) (pullback.lift_snd _ _ _)

def baseChangePtEquiv [GrpObj A] :
    (ptOver L Ω ⟶ (Over.pullback (spMap (algebraMap K L))).obj A) ≃* (ptOver K Ω ⟶ A) where
  toFun := baseChangePt A
  invFun := baseChangePtInv A
  left_inv x := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · exact (pullback.lift_snd _ _ _).trans (Over.w x).symm
  right_inv y := Over.OverMorphism.ext (pullback.lift_fst _ _ _)
  map_mul' x y := by
    have h := isGrpPullback_pullback A (spMap (algebraMap K L))
    apply Over.OverMorphism.ext
    refine Eq.symm <| (mul_left_congr (spMap_algebraMap_tower K L Ω) (baseChangePt A x) (baseChangePt A y)
      (pushPt h.1.w x) (pushPt h.1.w y) rfl rfl).trans ?_
    exact (h.2 _ x y (pushPt h.1.w x) (pushPt h.1.w y) rfl rfl).trans rfl

end GlobalTheory.Published.AbVarRed
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisRepresentationTateModuleBaseChangeEqOneIff
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TateBaseChange

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise in
open IsLocalRing in
attribute [local instance] Over.cartesianMonoidalCategory in
private lemma baseChangePtEquiv_galPts (K L Ω : Type) [Field K] [Field L] [Field Ω]
    [Algebra K L] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω]
    (A : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K)) [GrpObj A] (σ : Ω ≃ₐ[L] Ω)
    (x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ptOver L Ω ⟶ (Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K L))).obj A) :
    _root_.GlobalTheory.Published.AbVarRed.baseChangePtEquiv A (_root_.GlobalTheory.Published.AbVarRed.galPts _ σ x) =
      _root_.GlobalTheory.Published.AbVarRed.galPts A (σ.restrictScalars K) (_root_.GlobalTheory.Published.AbVarRed.baseChangePtEquiv A x) := by
  apply Over.OverMorphism.ext
  show (_root_.GlobalTheory.Published.AbVarRed.galPts _ σ x).left ≫ _ = (_root_.GlobalTheory.Published.AbVarRed.galPts A (σ.restrictScalars K) _).left
  rw [_root_.GlobalTheory.Published.AbVarRed.galPts_left, _root_.GlobalTheory.Published.AbVarRed.galPts_left, Category.assoc]
  rfl


open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise in
open IsLocalRing in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.TateBaseChange.galTate_baseChange_eq_one_iff : ∀ (K L Ω : Type) [Field K] [Field L] [Field Ω] [Algebra K L] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω] (A : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K)) [GrpObj A] [IsCommMonObj A] [IsCommMonObj ((Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K L))).obj A)] (l : ℕ) [Fact l.Prime] (σ : Ω ≃ₐ[L] Ω), _root_.GlobalTheory.Published.AbVarRed.galTate ((Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K L))).obj A) l σ = 1 ↔ _root_.GlobalTheory.Published.AbVarRed.galTate A l (σ.restrictScalars K) = 1 := by
  intro K L Ω _ _ _ _ _ _ _ A _ _ _ l _ σ
  set e := _root_.GlobalTheory.Published.AbVarRed.baseChangePtEquiv (K := K) (L := L) (Ω := Ω) A
  have he := baseChangePtEquiv_galPts K L Ω A σ
  constructor
  · intro h
    refine LinearMap.ext fun s => _root_.GlobalTheory.HTLat.Tate.ext fun n => ?_
    rw [_root_.GlobalTheory.Published.AbVarRed.lev_galTate, Module.End.one_apply]
    have ht := congrArg (fun ρ : Module.End ℤ_[l] _ =>
      (ρ (_root_.GlobalTheory.HTLat.Tate.map l e.symm.toMonoidHom s)).lev n) h
    simp only [_root_.GlobalTheory.Published.AbVarRed.lev_galTate, Module.End.one_apply,
      _root_.GlobalTheory.HTLat.Tate.lev_map] at ht
    have := congrArg e ht
    rw [he] at this
    simpa [e] using this
  · intro h
    refine LinearMap.ext fun t => _root_.GlobalTheory.HTLat.Tate.ext fun n => ?_
    rw [_root_.GlobalTheory.Published.AbVarRed.lev_galTate, Module.End.one_apply]
    have hs := congrArg (fun ρ : Module.End ℤ_[l] _ =>
      (ρ (_root_.GlobalTheory.HTLat.Tate.map l e.toMonoidHom t)).lev n) h
    simp only [_root_.GlobalTheory.Published.AbVarRed.lev_galTate, Module.End.one_apply,
      _root_.GlobalTheory.HTLat.Tate.lev_map] at hs
    apply e.injective
    rw [he]
    exact hs

end GlobalTheory.TateBaseChange
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisRepresentationTateModuleBaseChangeEqOneIffStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisRepresentationTateModule_baseChange_eq_one_iff : ∀ (K L Ω : Type) [Field K] [Field L] [Field Ω] [Algebra K L] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] [IsCommMonObj ((Over.pullback (spMap (algebraMap K L))).obj A)] (l : ℕ) [Fact l.Prime] (σ : Ω ≃ₐ[L] Ω), galTate ((Over.pullback (spMap (algebraMap K L))).obj A) l σ = 1 ↔ galTate A l (σ.restrictScalars K) = 1 := by
  first | exact @GlobalTheory.TateBaseChange.galTate_baseChange_eq_one_iff | exact GlobalTheory.TateBaseChange.galTate_baseChange_eq_one_iff | (intros; apply GlobalTheory.TateBaseChange.galTate_baseChange_eq_one_iff <;> assumption)
end
end
