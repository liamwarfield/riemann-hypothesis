module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecMapFromSpecOfRangeSubset
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory


open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.extension_descends_of_isIntegral : ∀ (R R₂ : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CommRing R₂] [IsDomain R₂] [IsLocalRing R₂] (g : R →+* R₂) (gam : FractionRing R →+* FractionRing R₂), (∀ r, gam (algebraMap R _ r) = algebraMap R₂ _ (g r)) → g.IsIntegral → ∀ (X : Scheme.{0}) (y : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (FractionRing R) ⟶ X) (χ₂ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R₂ ⟶ X), _root_.ReciprocityTheory.ChartRestriction.G.Out.jK R₂ ≫ χ₂ = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap gam ≫ y → ∃ χ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R ⟶ X, _root_.ReciprocityTheory.ChartRestriction.G.Out.jK R ≫ χ = y ∧ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap g ≫ χ = χ₂ := by
  intro R R₂ _ _ _ _ _ _ g gam hgam hint X y χ₂ hcomm
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap _root_.ReciprocityTheory.ChartRestriction.G.Out.jK at *
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X)
    (x := χ₂ (IsLocalRing.closedPoint R₂)) (U := ⊤) trivial
  have hmem : ∀ p, χ₂ p ∈ U := fun p =>
    ((IsLocalRing.specializes_closedPoint (R := R₂) p).map χ₂.continuous).mem_open U.2 hxU
  have h₂ : Set.range χ₂ ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨p, rfl⟩
    exact hmem p
  have hy : Set.range y ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨p, rfl⟩
    let q : ↥(Spec (CommRingCat.of (FractionRing R₂))) :=
      (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum _)
    have hp : (Spec.map (CommRingCat.ofHom gam)) q = p := Subsingleton.elim _ _
    have e := Scheme.Hom.comp_apply
      (Spec.map (CommRingCat.ofHom (algebraMap R₂ (FractionRing R₂)))) χ₂ q
    rw [hcomm, Scheme.Hom.comp_apply, hp] at e
    rw [e]
    exact hmem _
  set χ₂' := IsOpenImmersion.lift U.ι χ₂ h₂ with hχ₂'
  set y' := IsOpenImmersion.lift U.ι y hy with hy'
  have hc' : Spec.map (CommRingCat.ofHom (algebraMap R₂ (FractionRing R₂))) ≫ χ₂' =
      Spec.map (CommRingCat.ofHom gam) ≫ y' := by
    rw [← cancel_mono U.ι, Category.assoc, Category.assoc, hχ₂', hy', IsOpenImmersion.lift_fac,
      IsOpenImmersion.lift_fac, hcomm]
  set a₂ := Spec.preimage (χ₂' ≫ hU.isoSpec.hom) with ha₂
  set b := Spec.preimage (y' ≫ hU.isoSpec.hom) with hb
  have hab : a₂ ≫ CommRingCat.ofHom (algebraMap R₂ (FractionRing R₂)) =
      b ≫ CommRingCat.ofHom gam := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, ha₂, hb, Spec.map_preimage, Spec.map_preimage,
      ← Category.assoc, ← Category.assoc, hc']
  have e1 : ∀ a, gam (b.hom a) = algebraMap R₂ _ (a₂.hom a) := fun a =>
    (congrArg (fun f => f.hom a) hab).symm
  have hcomp : gam.comp (algebraMap R (FractionRing R)) =
      (algebraMap R₂ (FractionRing R₂)).comp g :=
    RingHom.ext hgam
  have hpt : ∀ a, b.hom a ∈ (algebraMap R (FractionRing R)).range := by
    intro a
    obtain ⟨p, hpm, hp⟩ := hint (a₂.hom a)
    rw [RingHom.mem_range]
    apply IsIntegrallyClosed.algebraMap_eq_of_integral
    refine ⟨p, hpm, gam.injective ?_⟩
    rw [Polynomial.hom_eval₂, map_zero, e1, hcomp, ← Polynomial.hom_eval₂, hp, map_zero]
  let e := RingEquiv.ofBijective (algebraMap R (FractionRing R)).rangeRestrict
    ⟨fun u v h => IsFractionRing.injective R (FractionRing R) (congrArg Subtype.val h),
      RingHom.rangeRestrict_surjective _⟩
  let φ : Γ(X, U) →+* R := e.symm.toRingHom.comp (b.hom.codRestrict _ hpt)
  have hφ : ∀ a, algebraMap R (FractionRing R) (φ a) = b.hom a := fun a =>
    congrArg Subtype.val (e.apply_symm_apply ⟨b.hom a, hpt a⟩)
  refine ⟨Spec.map (CommRingCat.ofHom φ) ≫ hU.isoSpec.inv ≫ U.ι, ?_, ?_⟩
  · have hφb : CommRingCat.ofHom φ ≫ CommRingCat.ofHom (algebraMap R (FractionRing R)) = b := by
      ext a
      exact hφ a
    rw [← Category.assoc, ← Spec.map_comp, hφb, hb, Spec.map_preimage, Category.assoc,
      Iso.hom_inv_id_assoc, hy', IsOpenImmersion.lift_fac]
  · have hφa : CommRingCat.ofHom φ ≫ CommRingCat.ofHom g = a₂ := by
      ext a
      apply IsFractionRing.injective R₂ (FractionRing R₂)
      change algebraMap R₂ _ (g (φ a)) = algebraMap R₂ _ (a₂.hom a)
      rw [← hgam, hφ, e1]
    rw [← Category.assoc, ← Spec.map_comp, hφa, ha₂, Spec.map_preimage, Category.assoc,
      Iso.hom_inv_id_assoc, hχ₂', IsOpenImmersion.lift_fac]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecOnPullSurjectiveOfSurjective
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbLaw

theorem secOn_pull_surjective_of_surjective :
    ∀ (A A' : Type) [CommRing A] [CommRing A'] (g : A →+* A'), Function.Surjective g → ∀ (X X' : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of A)) (f' : X' ⟶ Spec (CommRingCat.of A')) (β : X' ⟶ X), IsPullback β f' f (Spec.map (CommRingCat.ofHom g)) → ∀ H : LB X, H.IsLB → ∀ D : X.Opens, IsAffineOpen D → Function.Surjective (SecOn.pull H β D) := by
  intro A A' _ _ g hg X X' f f' β hβ H hH D hD y
  letI := g.toAlgebra
  obtain ⟨z, hz⟩ := (SecOnR.baseChangeHom_bijective (R := A) (R' := A') hH hβ hD rfl).2 y
  obtain ⟨x, rfl⟩ := TensorProduct.mk_surjective A (SecOnR f H D) A' hg z
  refine ⟨x, ?_⟩
  have h := (SecOnR.baseChangeHom_tmul (R := A) (R' := A') hβ.w le_rfl 1 x).symm.trans hz
  rw [one_smul] at h
  exact (SecOn.pullLE_self β x).symm.trans h

end GlobalTheory.AbLaw
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PotModelTrans
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
namespace GlobalTheory.SS


open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
theorem _root_.GlobalTheory.SS.potModel_trans : ∀ (V K V₁ K₁ : Type) [CommRing V] [Field K] [Algebra V K] [CommRing V₁] [Field K₁] [Algebra V₁ K₁] [Algebra V V₁] [Algebra K K₁], (algebraMap V₁ K₁).comp (algebraMap V V₁) = (algebraMap K K₁).comp (algebraMap V K) → Module.Finite V V₁ → IsLocalHom (algebraMap V V₁) → ∀ (A : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K)) [GrpObj A] (A₁ : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K₁)) [GrpObj A₁] (φ : A₁.left ⟶ A.left), _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback A₁ A (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K K₁)) φ → ∀ Q, _root_.GlobalTheory.SS.PotModel V₁ K₁ A₁ Q → _root_.GlobalTheory.SS.PotModel V K A Q := by
  intro V K V₁ K₁ _ _ _ _ _ _ _ _ hcomm hfin hloc A _ A₁ _ φ hφ Q hP
  obtain ⟨W, L, _, _, _, _, _, _, _, _, h1, h2, h3, h4, G, _, ⟨e, he⟩, hQ⟩ := hP
  letI : Algebra V W := ((algebraMap V₁ W).comp (algebraMap V V₁)).toAlgebra
  letI : Algebra K L := ((algebraMap K₁ L).comp (algebraMap K K₁)).toAlgebra
  have hA : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback ((Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K₁ L))).obj A₁) A (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K L)) (pullback.fst A₁.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K₁ L)) ≫ φ) := by
    refine (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback.comp (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_pullback A₁ _) hφ).congr ?_ rfl
    rw [← _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp]
  obtain ⟨e', he', -⟩ := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.grpPullback_iso hA (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_pullback A _)
  refine ⟨W, L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_, ?_, h4, G, inferInstance, ⟨e ≪≫ e', ?_⟩, hQ⟩
  · show (algebraMap W L).comp ((algebraMap V₁ W).comp (algebraMap V V₁)) = ((algebraMap K₁ L).comp (algebraMap K K₁)).comp (algebraMap V K)
    rw [← RingHom.comp_assoc, h1, RingHom.comp_assoc, hcomm, RingHom.comp_assoc]
  · exact (RingHom.finite_algebraMap.mpr h2).comp (RingHom.finite_algebraMap.mpr hfin)
  · show IsLocalHom ((algebraMap V₁ W).comp (algebraMap V V₁))
    infer_instance
  · rw [Iso.trans_hom]
    infer_instance

end GlobalTheory.SS
end
