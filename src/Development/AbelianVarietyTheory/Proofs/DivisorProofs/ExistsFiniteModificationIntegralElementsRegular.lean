module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGenerationIntegralFamilySections

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteNormalizationIntegralSections
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelObjIsoHomSubtype
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.AffineZariskiSite

noncomputable section

namespace GlobalTheory.RelativeSpectrum

structure QCohSub {X Y : Scheme.{0}} (f : X ⟶ Y) (F : ∀ V : Y.Opens, Subring Γ(X, f ⁻¹ᵁ V)) : Prop where
  app_mem : ∀ V : Y.Opens, IsAffineOpen V → ∀ a : Γ(Y, V), (f.app V).hom a ∈ F V
  res_mem : ∀ (V V' : Y.Opens) (hle : V' ≤ V), IsAffineOpen V → IsAffineOpen V' → ∀ x ∈ F V,
    (X.presheaf.map (homOfLE (f.preimage_mono hle)).op).hom x ∈ F V'
  loc : ∀ V : Y.Opens, IsAffineOpen V → ∀ (r : Γ(Y, V)) (x : Γ(X, f ⁻¹ᵁ Y.basicOpen r)),
    x ∈ F (Y.basicOpen r) →
    ∃ (k : ℕ) (y : Γ(X, f ⁻¹ᵁ V)), y ∈ F V ∧
      (X.presheaf.map (homOfLE (f.preimage_mono (Y.basicOpen_le r))).op).hom y =
        (X.presheaf.map (homOfLE (f.preimage_mono (Y.basicOpen_le r))).op).hom ((f.app V).hom r) ^ k * x

variable {X Y : Scheme.{0}} {f : X ⟶ Y} {F : ∀ V : Y.Opens, Subring Γ(X, f ⁻¹ᵁ V)}


set_option backward.isDefEq.respectTransparency false in
def diagram (H : QCohSub f F) : Y.AffineZariskiSiteᵒᵖ ⥤ CommRingCat where
  obj U := .of (F U.unop.1)
  map {V U} i :=
    CommRingCat.ofHom ((X.presheaf.map (homOfLE (f.preimage_mono (toOpens_mono i.unop.le))).op).hom.restrict
      _ _ fun x hx ↦ H.res_mem _ _ (toOpens_mono i.unop.le) V.unop.2 U.unop.2 x hx)
  map_id U := by
    ext x
    change ((X.presheaf.map (𝟙 _)).hom x.1) = x.1
    simp
  map_comp i j := by
    simp only [← CommRingCat.ofHom_comp]
    rw [← homOfLE_comp (f.preimage_mono (toOpens_mono j.unop.le))
      (f.preimage_mono (toOpens_mono i.unop.le)), op_comp]
    simp_rw [X.presheaf.map_comp]
    rfl

def diagramMap (H : QCohSub f F) : (toOpensFunctor Y).op ⋙ Y.presheaf ⟶ diagram H where
  app U := CommRingCat.ofHom ((f.app U.unop.1).hom.codRestrict (F U.unop.1) (H.app_mem _ U.unop.2))
  naturality {U V} i := by
    ext x
    exact Subtype.ext congr($(f.naturality ((toOpensFunctor Y).op.map i)) x)

variable [QuasiCompact f] [QuasiSeparated f]

set_option backward.isDefEq.respectTransparency false in
lemma coequifibered (H : QCohSub f F) : (diagramMap H).Coequifibered := by
  refine coequifibered_iff_forall_isLocalizationAway.mpr fun U r ↦ ?_
  let inst : Algebra Γ(X, f ⁻¹ᵁ U.1) Γ(X, f ⁻¹ᵁ Y.basicOpen r) :=
    (X.presheaf.map (homOfLE (f.preimage_mono (Y.basicOpen_le r))).op).hom.toAlgebra
  have hl : IsLocalization.Away ((f.app U.1).hom r) Γ(X, f ⁻¹ᵁ Y.basicOpen r) := by
    let : Algebra Γ(X, f ⁻¹ᵁ U.1) Γ(X, X.basicOpen (f.app _ r)) :=
      (X.presheaf.map (homOfLE (X.basicOpen_le _)).op).hom.toAlgebra
    dsimp +instances [inst]
    rw! (castMode := .all) [f.preimage_basicOpen r]
    exact isLocalization_basicOpen_of_qcqs (f.isCompact_preimage U.2.isCompact)
        (f.isQuasiSeparated_preimage U.2.isQuasiSeparated) (f.app _ r)
  letI := ((diagram H).map (homOfLE (U.basicOpen_le r)).op).hom.toAlgebra
  refine IsLocalization.Away.mk _ ?_ ?_ ?_
  · have h1 : IsUnit ((Y.presheaf.map (homOfLE (Y.basicOpen_le r)).op).hom r) :=
      Y.toRingedSpace.isUnit_res_basicOpen r
    have h2 := h1.map ((diagramMap H).app (.op (U.basicOpen r))).hom
    convert h2 using 1
    exact congr($((diagramMap H).naturality (homOfLE (U.basicOpen_le r)).op) r).symm
  · intro s
    obtain ⟨k, y, hy, e⟩ := H.loc U.1 U.2 r s.1 s.2
    refine ⟨k, ⟨y, hy⟩, Subtype.ext ?_⟩
    rw [mul_comm] at e
    exact e.symm
  · intro a b hab
    have hab' : algebraMap Γ(X, f ⁻¹ᵁ U.1) Γ(X, f ⁻¹ᵁ Y.basicOpen r) a.1 =
        algebraMap Γ(X, f ⁻¹ᵁ U.1) Γ(X, f ⁻¹ᵁ Y.basicOpen r) b.1 := congrArg Subtype.val hab
    obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq ((f.app U.1).hom r) hab'
    exact ⟨n, Subtype.ext hn⟩

def glueData (H : QCohSub f F) := relativeGluingData (coequifibered H)

instance (H : QCohSub f F) : ((glueData H).functor ⋙ Scheme.forget).IsLocallyDirected :=
  Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..

def relSpec (H : QCohSub f F) : Scheme := (glueData H).glued

def relCover (H : QCohSub f F) : (relSpec H).OpenCover := (glueData H).cover


set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
def toRel (H : QCohSub f F) : X ⟶ relSpec H :=
  Scheme.OpenCover.glueMorphismsOfLocallyDirected
    ((directedCover Y).pullback₁ f)
    (fun U ↦
      (pullbackRestrictIsoRestrict f _).hom ≫
      (f ⁻¹ᵁ U.1).toSpecΓ ≫ Spec.map (CommRingCat.ofHom (F U.1).subtype) ≫ (relCover H).f U)
    fun {U V : Y.AffineZariskiSite} i ↦ by
  have : (pullbackRestrictIsoRestrict f U.1).inv ≫
      Cover.trans ((directedCover Y).pullback₁ f) i ≫
      (pullbackRestrictIsoRestrict f V.1).hom = X.homOfLE
        (f.preimage_mono (toOpens_mono i.1.1)) := by
    rw [← cancel_mono (Scheme.Opens.ι _)]
    simp +instances [Cover.trans, Cover.locallyDirectedPullbackCover]
  rw [← Iso.inv_comp_eq, reassoc_of% this, ← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc,
    ← Spec.map_comp_assoc]
  dsimp [relCover]
  rw [← colimit.w (glueData H).functor i]
  dsimp [glueData, relativeGluingData]
  rw [← Spec.map_comp_assoc]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc]
lemma ι_toRel (H : QCohSub f F) (U : Y.affineOpens) :
    (f ⁻¹ᵁ U.1).ι ≫ toRel H = (f ⁻¹ᵁ U.1).toSpecΓ ≫
      Spec.map (CommRingCat.ofHom (F U.1).subtype) ≫ (relCover H).f U := by
  rw [← cancel_epi (pullbackRestrictIsoRestrict f U.1).hom, ← Category.assoc]
  trans ((directedCover Y).pullback₁ f).f U ≫ toRel H
  · congr 1; simp
  delta toRel
  generalize_proofs _ _ _ _ H'
  exact Scheme.OpenCover.map_glueMorphismsOfLocallyDirected _ _ H' _

def fromRel (H : QCohSub f F) : relSpec H ⟶ Y := (glueData H).toBase

lemma ι_fromRel (H : QCohSub f F) (U : Y.affineOpens) :
    (relCover H).f U ≫ fromRel H =
      Spec.map ((diagramMap H).app (.op U)) ≫ U.2.fromSpec :=
  colimit.ι_desc _ _

set_option backward.isDefEq.respectTransparency.types false in
lemma fromRel_preimage (H : QCohSub f F) (U : Y.affineOpens) :
    fromRel H ⁻¹ᵁ U = ((relCover H).f U).opensRange := by
  simpa using! (glueData H).toBase_preimage_eq_opensRange_ι U

set_option backward.isDefEq.respectTransparency false in
lemma toRel_fromRel (H : QCohSub f F) : toRel H ≫ fromRel H = f := by
  refine Scheme.Cover.hom_ext (X.openCoverOfIsOpenCover _
    (.comap (iSup_affineOpens_eq_top Y) f.base.1)) _ _ fun U ↦ ?_
  refine (ι_toRel_assoc H _ _).trans ?_
  rw [ι_fromRel, ← Spec.map_comp_assoc]
  change (f ⁻¹ᵁ U.1).toSpecΓ ≫ Spec.map (f.app _) ≫ U.2.fromSpec = (f ⁻¹ᵁ U.1).ι ≫ _
  simp

set_option backward.isDefEq.respectTransparency false in
lemma isFinite_fromRel (H : QCohSub f F)
    (hfin : ∀ U : Y.affineOpens, ((diagramMap H).app (.op U)).hom.Finite) : IsFinite (fromRel H) := by
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsFinite) _
    (iSup_affineOpens_eq_top _)]
  intro U
  let e := IsOpenImmersion.isoOfRangeEq (fromRel H ⁻¹ᵁ U).ι ((relCover H).f U)
      (by simpa using congr($(fromRel_preimage H U).1))
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsFinite e.inv,
    ← MorphismProperty.cancel_right_of_respectsIso @IsFinite _ U.2.isoSpec.hom]
  convert! (IsFinite.SpecMap_iff _).mpr (hfin U)
  rw [← cancel_mono U.2.fromSpec]
  simp [IsAffineOpen.isoSpec_hom, e, ι_fromRel]


set_option backward.isDefEq.respectTransparency.types false in
def relObjIso (H : QCohSub f F) {U : Y.Opens} (hU : IsAffineOpen U) :
    Γ(relSpec H, fromRel H ⁻¹ᵁ U) ≅ .of (F U) :=
  (relSpec H).presheaf.mapIso (eqToIso
    (by simpa using! (fromRel_preimage H ⟨U, hU⟩).symm)).op ≪≫
  ((relCover H).f ⟨U, hU⟩).appIso ⊤ ≪≫ Scheme.ΓSpecIso _

set_option backward.isDefEq.respectTransparency false in
lemma toRel_app_preimage (H : QCohSub f F) (U : Y.affineOpens) :
    (toRel H).app (fromRel H ⁻¹ᵁ ↑U) =
      (relObjIso H U.2).hom ≫
      CommRingCat.ofHom (F U.1).subtype ≫
      X.presheaf.map (eqToHom (by
        rw [← Scheme.Hom.comp_preimage (toRel H) (fromRel H), toRel_fromRel])).op := by
  dsimp [relObjIso]
  change _ = (relSpec H).presheaf.map (eqToHom (by simp [fromRel_preimage])).op ≫
      (((relCover H).f U).appIso _).hom ≫
      (Scheme.ΓSpecIso _).hom ≫
      CommRingCat.ofHom (F U.1).subtype ≫
      X.presheaf.map (eqToHom (by
        rw [← Scheme.Hom.comp_preimage (toRel H) (fromRel H), toRel_fromRel])).op
  have H' : toRel H ⁻¹ᵁ fromRel H ⁻¹ᵁ U =
      (f ⁻¹ᵁ U).ι ''ᵁ (((f ⁻¹ᵁ U).ι ≫ toRel H) ⁻¹ᵁ fromRel H ⁻¹ᵁ U) := by
    rw [Scheme.Hom.comp_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Opens.opensRange_ι, ← Scheme.Hom.comp_preimage (toRel H) (fromRel H),
      toRel_fromRel, inf_idem]
  convert! congr($(Scheme.Hom.congr_app (ι_toRel H U) (fromRel H ⁻¹ᵁ U)) ≫
    X.presheaf.map (eqToHom H').op) using 1
  · simp [Hom.app_eq_appLE]
  dsimp
  simp only [eqToHom_op, Hom.appIso_hom, Category.assoc, Scheme.Hom.naturality_assoc, eqToHom_unop,
    ← Functor.map_comp_assoc, eqToHom_map (TopologicalSpace.Opens.map _), eqToHom_trans]
  congr 1
  rw [← IsIso.eq_inv_comp, ← Functor.map_inv, inv_eqToHom]
  simp [← Functor.map_comp, Scheme.Opens.toSpecΓ_appTop,
    ΓSpecIso_naturality_assoc (CommRingCat.ofHom _)]
  rfl

lemma relObjIso_hom_subtype (H : QCohSub f F) {U : Y.Opens} (hU : IsAffineOpen U) :
    (relObjIso H hU).hom ≫ CommRingCat.ofHom (F U).subtype =
    (toRel H).appLE _ _ (by
      rw [← Scheme.Hom.comp_preimage (toRel H) (fromRel H), toRel_fromRel]) := by
  rw [Hom.appLE, toRel_app_preimage H ⟨U, hU⟩, Category.assoc]
  simp [← Functor.map_comp]
  rfl

lemma isDominant_toRel (H : QCohSub f F) (hfin : IsFinite (fromRel H)) : IsDominant (toRel H) := by
  have hqc : QuasiCompact (toRel H) := by
    apply MorphismProperty.of_postcomp (W := @QuasiCompact)
      (W' := @QuasiSeparated) _ (fromRel H)
    · infer_instance
    · rw [toRel_fromRel]
      infer_instance
  have hker : (toRel H).ker = ⊥ := by
    refine Scheme.IdealSheafData.ext_of_iSup_eq_top
      (fun U : Y.affineOpens ↦ ⟨fromRel H ⁻¹ᵁ U.1, U.2.preimage _⟩)
      (TopologicalSpace.IsOpenCover.comap (iSup_affineOpens_eq_top _) _) fun U ↦ ?_
    simp only [Hom.ker_apply, IdealSheafData.ideal_bot, Pi.bot_apply]
    rw [← RingHom.injective_iff_ker_eq_bot,
      ← ConcreteCategory.mono_iff_injective_of_preservesPullback, ← MorphismProperty.monomorphisms]
    simp only [toRel_app_preimage,
      eqToHom_op, MorphismProperty.cancel_left_of_respectsIso,
      MorphismProperty.cancel_right_of_respectsIso]
    rw [MorphismProperty.monomorphisms, @ConcreteCategory.mono_iff_injective_of_preservesPullback]
    exact Subtype.val_injective
  have := congr(($(hker).support : Set (relSpec H)))
  rw [IdealSheafData.support_bot, Scheme.Hom.support_ker, TopologicalSpace.Closeds.coe_top] at this
  exact ⟨dense_iff_closure_eq.mpr this⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
lemma isReduced_relSpec (H : QCohSub f F) [AlgebraicGeometry.IsReduced X] :
    AlgebraicGeometry.IsReduced (relSpec H) :=
  have (i : _) : AlgebraicGeometry.IsReduced ((relCover H).X i) := by
    have : _root_.IsReduced ((diagram H).obj (.op i)) :=
      isReduced_of_injective (F i.1).subtype Subtype.val_injective
    dsimp [relCover, glueData, relativeGluingData]
    infer_instance
  .of_openCover _ (relCover H)

lemma isIntegral_relSpec (H : QCohSub f F) [AlgebraicGeometry.IsIntegral X] [IsDominant (toRel H)] :
    AlgebraicGeometry.IsIntegral (relSpec H) :=
  have := isReduced_relSpec H
  have : IrreducibleSpace (relSpec H) := by
    rw [irreducibleSpace_def]
    convert!
      ((IrreducibleSpace.isIrreducible_univ X).image _
          (toRel H).continuous.continuousOn).closure
    simpa using (toRel H).denseRange.closure_range.symm
  isIntegral_of_irreducibleSpace_of_isReduced _


open ReciprocityTheory.ChartRestriction.G.Geo.Tor in
theorem exists_finite_cover {S : Scheme.{0}} {K : Type} [Field K] (gp : Sp K ⟶ S) [AlgebraicGeometry.IsIntegral S]
    [IsDominant gp] (F : ∀ V : S.Opens, Subring Γ(Sp K, gp ⁻¹ᵁ V)) (hF : GlobalTheory.Mum.IsFinSub gp F) :
    ∃ (S' : Scheme) (h : S' ⟶ S) (gp' : Sp K ⟶ S') (hgp : gp' ≫ h = gp),
      IsFinite h ∧ AlgebraicGeometry.IsIntegral S' ∧ IsDominant gp' ∧
      ∀ V : S.Opens, IsAffineOpen V → ∀ x ∈ F V, ∃ c : Γ(S', h ⁻¹ᵁ V),
        (gp'.appLE (h ⁻¹ᵁ V) (gp ⁻¹ᵁ V) (GlobalTheory.Mum.le_preimage_of_comp_eq gp gp' h hgp V)).hom c = x := by
  obtain ⟨h1, h2, h3, h4⟩ := hF
  have H : QCohSub gp F := ⟨h1, h2, h3⟩
  haveI : AlgebraicGeometry.IsIntegral (Sp K) := inferInstanceAs (AlgebraicGeometry.IsIntegral (Spec (.of K)))
  haveI : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  haveI : TopologicalSpace.NoetherianSpace (Sp K) := inferInstance
  haveI : QuasiCompact gp := inferInstance
  haveI : QuasiSeparated gp := inferInstance
  have hfin : IsFinite (fromRel H) := by
    refine isFinite_fromRel H fun U ↦ ?_
    obtain ⟨t, ht, hx⟩ := h4 U.1 U.2
    letI : Algebra Γ(S, U.1) (F U.1) :=
      ((gp.app U.1).hom.codRestrict (F U.1) (h1 _ U.2)).toAlgebra
    change Module.Finite Γ(S, U.1) (F U.1)
    refine Module.Finite.of_fg_top ?_
    rw [Submodule.fg_def]
    refine ⟨Set.range (fun y : t ↦ (⟨y.1, ht y.1 y.2⟩ : F U.1)), Set.finite_range _, ?_⟩
    rw [eq_top_iff]
    rintro x -
    obtain ⟨c, hc⟩ := hx x.1 x.2
    have : x = ∑ y : t, c y.1 • (⟨y.1, ht y.1 y.2⟩ : F U.1) := by
      apply Subtype.ext
      rw [hc, AddSubmonoidClass.coe_finsetSum, ← Finset.sum_coe_sort]
      rfl
    rw [this]
    exact Submodule.sum_mem _ fun y _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, rfl⟩)
  haveI := isDominant_toRel H hfin
  refine ⟨relSpec H, fromRel H, toRel H, toRel_fromRel H, hfin, isIntegral_relSpec H, this, ?_⟩
  intro V hV x hx
  refine ⟨(relObjIso H hV).inv.hom ⟨x, hx⟩, ?_⟩
  rw [← relObjIso_hom_subtype H hV, ← CommRingCat.comp_apply, Iso.inv_hom_id_assoc]
  rfl

end GlobalTheory.RelativeSpectrum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteNormalizationIntegralSections
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum
open Scheme.AffineZariskiSite

noncomputable section

theorem exists_finite_of_isFinSub : ∀ {S : Scheme.{0}} {K : Type} [Field K] (gp : Sp K ⟶ S) [IsIntegral S] [IsDominant gp]
    (F : ∀ V : S.Opens, Subring Γ(Sp K, gp ⁻¹ᵁ V)), IsFinSub gp F →
    ∃ (S' : Scheme.{0}) (h : S' ⟶ S) (gp' : Sp K ⟶ S') (hgp : gp' ≫ h = gp),
      IsFinite h ∧ IsIntegral S' ∧ IsDominant gp' ∧
      ∀ V : S.Opens, IsAffineOpen V → ∀ x ∈ F V, ∃ c : Γ(S', h ⁻¹ᵁ V),
        (gp'.appLE (h ⁻¹ᵁ V) (gp ⁻¹ᵁ V) (le_preimage_of_comp_eq gp gp' h hgp V)).hom c = x := by
  first
  | exact @_root_.GlobalTheory.RelativeSpectrum.exists_finite_cover
  | exact _root_.GlobalTheory.RelativeSpectrum.exists_finite_cover
  | (apply _root_.GlobalTheory.RelativeSpectrum.exists_finite_cover <;> assumption)
  | (intros; apply _root_.GlobalTheory.RelativeSpectrum.exists_finite_cover <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RelativeSpectrum.exists_finite_cover <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RelativeSpectrum.exists_finite_cover ..)

end

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteNormalizationIntegralSectionsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_normalization_integral_sections : ∀ {S : Scheme.{0}} {K : Type} [Field K] (gp : Sp K ⟶ S) [IsIntegral S] [IsDominant gp]
    (F : ∀ V : S.Opens, Subring Γ(Sp K, gp ⁻¹ᵁ V)), IsFinSub gp F →
    ∃ (S' : Scheme.{0}) (h : S' ⟶ S) (gp' : Sp K ⟶ S') (hgp : gp' ≫ h = gp),
      IsFinite h ∧ IsIntegral S' ∧ IsDominant gp' ∧
      ∀ V : S.Opens, IsAffineOpen V → ∀ x ∈ F V, ∃ c : Γ(S', h ⁻¹ᵁ V),
        (gp'.appLE (h ⁻¹ᵁ V) (gp ⁻¹ᵁ V) (le_preimage_of_comp_eq gp gp' h hgp V)).hom c = x := by
  first | exact @GlobalTheory.Mum.exists_finite_of_isFinSub | exact GlobalTheory.Mum.exists_finite_of_isFinSub | (intros; apply GlobalTheory.Mum.exists_finite_of_isFinSub <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSubringClosureOfIsIntegralElemAffineOpenLe
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSubringClosureOfIsIntegralElemAffineOpenLe
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem resK_bijective {S : Scheme.{0}} {K : Type} [Field K] (gp : Sp K ⟶ S) {V W : S.Opens} (h : W ≤ V)
    (e : gp ⁻¹ᵁ V ≤ gp ⁻¹ᵁ W) : Function.Bijective (resK gp h) := by
  have e' : gp ⁻¹ᵁ W = gp ⁻¹ᵁ V := le_antisymm (gp.preimage_mono h) e
  have hh : homOfLE (gp.preimage_mono h) = eqToHom e' := Subsingleton.elim _ _
  show Function.Bijective ((Sp K).presheaf.map (homOfLE (gp.preimage_mono h)).op).hom
  rw [hh]
  exact ConcreteCategory.bijective_of_isIso ((Sp K).presheaf.map (eqToHom e').op)

theorem isIntegralElem_of_comp_injective {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    (f : R →+* A) (g : A →+* B) (hg : Function.Injective g) {y : A}
    (h : (g.comp f).IsIntegralElem (g y)) : f.IsIntegralElem y := by
  obtain ⟨p, hp, hy⟩ := h
  refine ⟨p, hp, hg ?_⟩
  rw [Polynomial.hom_eval₂, hy, map_zero]

end GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem eq_bot_or_eq_top_of_sp (K : Type) [Field K] (O : (Sp K).Opens) : O = ⊥ ∨ O = ⊤ := by
  by_cases h : O = ⊥
  · exact Or.inl h
  · right
    obtain ⟨x, hx⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty O).mp h
    refine top_unique fun z _ => ?_
    have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
    rwa [Subsingleton.elim z x]
end GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem mem_closure_of_isIntegralElem_affine_le : ∀ {S : Scheme.{0}} {K : Type} [Field K] (gp : Sp K ⟶ S) (V W : S.Opens) (hWV : W ≤ V),
    IsAffineOpen V → IsAffineOpen W → ∀ b : Γ(Sp K, gp ⁻¹ᵁ W), (gp.app W).hom.IsIntegralElem b →
    ∃ s : Finset Γ(Sp K, gp ⁻¹ᵁ V), (∀ y ∈ s, (gp.app V).hom.IsIntegralElem y) ∧
      b ∈ Subring.closure (Set.range (gp.app W).hom ∪ resK gp hWV '' (s : Set _)) := by
  intro S K _ gp V W hWV hV hW b hb
  classical
  let C : Finset Γ(Sp K, gp ⁻¹ᵁ V) → Subring Γ(Sp K, gp ⁻¹ᵁ W) := fun s =>
    Subring.closure (Set.range (gp.app W).hom ∪ resK gp hWV '' (s : Set _))
  have Cmono : ∀ s t : Finset Γ(Sp K, gp ⁻¹ᵁ V), s ⊆ t → C s ≤ C t := by
    intro s t hst
    refine Subring.closure_mono (Set.union_subset_union_right _ (Set.image_mono ?_))
    exact_mod_cast hst
  let J : Ideal Γ(S, W) :=
    { carrier := {c | ∃ s : Finset Γ(Sp K, gp ⁻¹ᵁ V), (∀ y ∈ s, (gp.app V).hom.IsIntegralElem y) ∧
        (gp.app W).hom c * b ∈ C s}
      zero_mem' := ⟨∅, by simp, by rw [map_zero, zero_mul]; exact zero_mem _⟩
      add_mem' := by
        rintro c d ⟨s, hs, hc⟩ ⟨t, ht, hd⟩
        refine ⟨s ∪ t, fun y hy => (Finset.mem_union.mp hy).elim (hs y) (ht y), ?_⟩
        rw [map_add (f := _), add_mul]
        exact add_mem (Cmono _ _ Finset.subset_union_left hc) (Cmono _ _ Finset.subset_union_right hd)
      smul_mem' := by
        rintro c d ⟨s, hs, hd⟩
        refine ⟨s, hs, ?_⟩
        rw [smul_eq_mul, map_mul, _root_.mul_assoc]
        exact mul_mem (Subring.subset_closure (Or.inl ⟨c, rfl⟩)) hd }
  let T : Set Γ(S, W) := {c | ∃ g : Γ(S, V), S.basicOpen g ≤ W ∧ (S.presheaf.map (homOfLE hWV).op).hom g = c}
  have hspan : Ideal.span T = ⊤ := by
    refine hW.self_le_iSup_basicOpen_iff.mp ?_
    intro x hx
    obtain ⟨g, hg, hxg⟩ := hV.exists_basicOpen_le (V := W) ⟨x, hx⟩ (hWV hx)
    rw [TopologicalSpace.Opens.mem_iSup]
    refine ⟨⟨_, g, hg, rfl⟩, ?_⟩
    show x ∈ S.basicOpen ((S.presheaf.map (homOfLE hWV).op).hom g)
    rw [Scheme.basicOpen_res]
    exact ⟨hx, hxg⟩
  have hT : T ⊆ J.radical := by
    rintro _ ⟨g, hg, rfl⟩
    set D := S.basicOpen g with hD
    rcases eq_bot_or_eq_top_of_sp K (gp ⁻¹ᵁ D) with h0 | h1
    ·
      have hz : (gp.app V).hom g = 0 := by
        rw [← AlgebraicGeometry.basicOpen_eq_bot_iff, ← Scheme.preimage_basicOpen]
        exact h0
      refine ⟨1, ∅, by simp, ?_⟩
      rw [pow_one, ← resK_app, hz, map_zero, zero_mul]
      exact zero_mem _
    ·
      have hDW : D ≤ W := hg
      have hDV : D ≤ V := hDW.trans hWV
      have := hV.isLocalization_basicOpen g
      letI : Algebra Γ(S, D) Γ(Sp K, gp ⁻¹ᵁ D) := (gp.app D).hom.toAlgebra
      letI : Algebra Γ(S, V) Γ(Sp K, gp ⁻¹ᵁ D) := ((gp.app D).hom.comp (algebraMap Γ(S, V) Γ(S, D))).toAlgebra
      haveI : IsScalarTower Γ(S, V) Γ(S, D) Γ(Sp K, gp ⁻¹ᵁ D) := IsScalarTower.of_algebraMap_eq fun _ => rfl
      have sq : (resK gp hDW).comp (gp.app W).hom =
          (gp.app D).hom.comp (S.presheaf.map (homOfLE hDW).op).hom := by
        ext a; exact resK_app gp hDW a
      have hb' : IsIntegral Γ(S, D) (resK gp hDW b) := by
        have := hb.map (resK gp hDW)
        rw [sq] at this
        exact RingHom.isIntegralElem.of_comp _ _ this
      obtain ⟨⟨_, N, rfl⟩, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization (Submonoid.powers g)
        (Rₘ := Γ(S, D)) _ hb'
      have top : ∀ U : S.Opens, gp ⁻¹ᵁ U ≤ gp ⁻¹ᵁ D := fun _ => h1 ▸ le_top
      obtain ⟨y, hy⟩ := (resK_bijective gp hDV (top V)).2 ((g ^ N) • resK gp hDW b)
      have alg : ∀ a : Γ(S, V), algebraMap Γ(S, V) Γ(Sp K, gp ⁻¹ᵁ D) a = resK gp hDV ((gp.app V).hom a) := by
        intro a; rw [resK_app]; rfl
      have hyi : (gp.app V).hom.IsIntegralElem y := by
        refine isIntegralElem_of_comp_injective _ (resK gp hDV) (resK_bijective gp hDV (top V)).1 ?_
        have e : (resK gp hDV).comp (gp.app V).hom = algebraMap Γ(S, V) Γ(Sp K, gp ⁻¹ᵁ D) := by
          ext a; exact (alg a).symm
        rw [e, hy]
        exact hm
      refine ⟨N, {y}, by simpa using hyi, ?_⟩
      have key : resK gp hWV y = (gp.app W).hom ((S.presheaf.map (homOfLE hWV).op).hom g ^ N) * b := by
        apply (resK_bijective gp hDW (top W)).1
        rw [resK_resK, hy, Algebra.smul_def, alg, map_mul]
        simp only [map_pow]
        rw [← resK_app gp hWV g, resK_resK]
      rw [← key]
      exact Subring.subset_closure (Or.inr ⟨y, by simp, rfl⟩)
  have hJ : J = ⊤ := Ideal.radical_eq_top.mp (top_unique (hspan ▸ Ideal.span_le.mpr hT))
  obtain ⟨s, hs, h⟩ : (1 : Γ(S, W)) ∈ J := hJ ▸ Submodule.mem_top
  refine ⟨s, hs, ?_⟩
  simpa using h

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSubringClosureOfIsIntegralElemAffineOpenLeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_subringClosure_of_isIntegralElem_affineOpen_le : ∀ {S : Scheme.{0}} {K : Type} [Field K] (gp : Sp K ⟶ S) (V W : S.Opens) (hWV : W ≤ V),
    IsAffineOpen V → IsAffineOpen W → ∀ b : Γ(Sp K, gp ⁻¹ᵁ W), (gp.app W).hom.IsIntegralElem b →
    ∃ s : Finset Γ(Sp K, gp ⁻¹ᵁ V), (∀ y ∈ s, (gp.app V).hom.IsIntegralElem y) ∧
      b ∈ Subring.closure (Set.range (gp.app W).hom ∪ resK gp hWV '' (s : Set _)) := by
  first | exact @GlobalTheory.Mum.mem_closure_of_isIntegralElem_affine_le | exact GlobalTheory.Mum.mem_closure_of_isIntegralElem_affine_le | (intros; apply GlobalTheory.Mum.mem_closure_of_isIntegralElem_affine_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGeneratedSubringLocalisedBasicOpen
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGeneratedSubringLocalisedBasicOpen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem closure_pow_lift {L L' : Type*} [CommRing L] [CommRing L'] (ρ : L →+* L') (C : Subring L) (u : L)
    (hu : u ∈ C) (G : Set L') (hG : ∀ g ∈ G, ∃ k : ℕ, ∃ w ∈ C, ρ w = ρ u ^ k * g) :
    ∀ z ∈ Subring.closure G, ∃ k : ℕ, ∃ w ∈ C, ρ w = ρ u ^ k * z := by
  intro z hz
  induction hz using Subring.closure_induction with
  | mem g hg => exact hG g hg
  | zero => exact ⟨0, 0, C.zero_mem, by simp⟩
  | one => exact ⟨0, 1, C.one_mem, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨k, w, hw, e⟩ := ha
    obtain ⟨l, v, hv, e'⟩ := hb
    refine ⟨k + l, u ^ l * w + u ^ k * v,
      C.add_mem (C.mul_mem (C.pow_mem hu _) hw) (C.mul_mem (C.pow_mem hu _) hv), ?_⟩
    rw [map_add (f := _), map_mul, map_mul, map_pow, map_pow, e, e']
    ring
  | neg a _ ha =>
    obtain ⟨k, w, hw, e⟩ := ha
    exact ⟨k, -w, C.neg_mem hw, by rw [map_neg, e]; ring⟩
  | mul a b _ _ ha hb =>
    obtain ⟨k, w, hw, e⟩ := ha
    obtain ⟨l, v, hv, e'⟩ := hb
    refine ⟨k + l, w * v, C.mul_mem hw hv, ?_⟩
    rw [map_mul, e, e']
    ring

theorem exists_pow_mul_res {S : Scheme.{0}} {U : S.Opens} (hc : IsCompact (U : Set S))
    (hq : IsQuasiSeparated (U : Set S)) (g : Γ(S, U)) (U' : S.Opens) (hle : U' ≤ U) (hU' : U' = S.basicOpen g)
    (a : Γ(S, U')) : ∃ (k : ℕ) (b : Γ(S, U)), (S.presheaf.map (homOfLE hle).op).hom b =
      (S.presheaf.map (homOfLE hle).op).hom g ^ k * a := by
  subst hU'
  letI := (S.presheaf.map (homOfLE (S.basicOpen_le g)).op).hom.toAlgebra
  have := isLocalization_basicOpen_of_qcqs hc hq g
  obtain ⟨⟨y, ⟨_, k, rfl⟩⟩, hy⟩ := IsLocalization.surj (Submonoid.powers g) a
  refine ⟨k, y, ?_⟩
  rw [← map_pow, mul_comm]
  simpa [RingHom.algebraMap_toAlgebra] using hy.symm

theorem presheaf_map_bijective_of_eq {X : Scheme.{0}} {A B : X.Opens} (h : B ≤ A) (e : A = B) :
    Function.Bijective (X.presheaf.map (homOfLE h).op).hom := by
  subst e
  have : homOfLE h = 𝟙 A := Subsingleton.elim _ _
  simpa [this] using Function.bijective_id

end GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem finFam_basicOpen_loc : ∀ {S : Scheme.{0}} {K : Type} [Field K] (gp : Sp K ⟶ S) [IsLocallyNoetherian S] {r : ℕ} (V : Fin r → S.Opens)
    (t : ∀ i, Finset Γ(Sp K, gp ⁻¹ᵁ V i)) (W : S.Opens), IsAffineOpen W → ∀ (f : Γ(S, W))
    (x : Γ(Sp K, gp ⁻¹ᵁ S.basicOpen f)), x ∈ finFam gp V t (S.basicOpen f) →
    ∃ (k : ℕ) (y : Γ(Sp K, gp ⁻¹ᵁ W)), y ∈ finFam gp V t W ∧
      resK gp (S.basicOpen_le f) y = resK gp (S.basicOpen_le f) ((gp.app W).hom f) ^ k * x := by
  intro S K _ gp _ r V t W hW f x hx
  haveI : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  let p : Sp K := (IsLocalRing.closedPoint K : PrimeSpectrum K)
  have pre : ∀ U U' : S.Opens, (gp.base p ∈ U ↔ gp.base p ∈ U') → gp ⁻¹ᵁ U = gp ⁻¹ᵁ U' := by
    intro U U' h
    ext q
    rw [Subsingleton.elim q p]
    exact h
  have bij : ∀ {U U' : S.Opens} (h : U' ≤ U), (gp.base p ∈ U ↔ gp.base p ∈ U') →
      Function.Bijective (resK gp h) := fun h e => presheaf_map_bijective_of_eq _ (pre _ _ e)
  by_cases hs : gp.base p ∈ S.basicOpen f
  swap
  · have e : gp ⁻¹ᵁ S.basicOpen f = ⊥ := by
      ext q
      rw [Subsingleton.elim q p]
      exact ⟨fun h => (hs h).elim, fun h => by simp at h⟩
    haveI : Subsingleton Γ(Sp K, gp ⁻¹ᵁ S.basicOpen f) := by rw [e]; infer_instance
    exact ⟨0, 0, Subring.zero_mem _, Subsingleton.elim _ _⟩
  have hsW : gp.base p ∈ W := S.basicOpen_le f hs
  haveI : IsNoetherianRing Γ(S, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  have hNW : TopologicalSpace.NoetherianSpace (W : Set S) := noetherianSpace_of_isAffineOpen W hW
  have hcpt : ∀ T ⊆ (W : Set S), IsCompact T := (TopologicalSpace.noetherianSpace_set_iff _).mp hNW
  have hle : ∀ i, S.basicOpen f ⊓ V i ≤ W ⊓ V i := fun i => inf_le_inf_right _ (S.basicOpen_le f)
  rw [mem_finFam] at hx
  have step : ∀ i, ∃ k : ℕ, ∃ w ∈ Subring.closure (Set.range (gp.app (W ⊓ V i)).hom ∪
      resK gp (inf_le_right : W ⊓ V i ≤ V i) '' (t i : Set _)),
      resK gp (hle i) w = resK gp (hle i) (resK gp (inf_le_left : W ⊓ V i ≤ W) ((gp.app W).hom f)) ^ k *
        resK gp (inf_le_left : S.basicOpen f ⊓ V i ≤ S.basicOpen f) x := by
    intro i
    refine closure_pow_lift _ _ _ ?_ _ ?_ _ (hx i)
    · rw [resK_app]
      exact Subring.subset_closure (Or.inl ⟨_, rfl⟩)
    rintro _ (⟨a, rfl⟩ | ⟨c, hc, rfl⟩)
    · have hU' : S.basicOpen f ⊓ V i =
          S.basicOpen ((S.presheaf.map (homOfLE (inf_le_left : W ⊓ V i ≤ W)).op).hom f) := by
        rw [Scheme.basicOpen_res]
        exact le_antisymm (le_inf (le_inf (inf_le_left.trans (S.basicOpen_le f)) inf_le_right) inf_le_left)
          (le_inf inf_le_right (inf_le_left.trans inf_le_right))
      have hWi : (↑(W ⊓ V i) : Set S) ⊆ W := fun z hz => hz.1
      obtain ⟨k, b, e⟩ := exists_pow_mul_res (hcpt _ hWi)
        (fun A B hA _ _ hB _ _ => hcpt _ ((Set.inter_subset_left.trans hA).trans hWi)) _ _ (hle i) hU' a
      refine ⟨k, (gp.app (W ⊓ V i)).hom b, Subring.subset_closure (Or.inl ⟨_, rfl⟩), ?_⟩
      rw [resK_app, resK_app, resK_app, e, map_mul, map_pow, ← CommRingCat.comp_apply]
    · refine ⟨0, resK gp (inf_le_right : W ⊓ V i ≤ V i) c, Subring.subset_closure (Or.inr ⟨c, hc, rfl⟩), ?_⟩
      rw [pow_zero, _root_.one_mul, resK_resK]
  choose k w hw e using step
  let N := Finset.univ.sup k
  obtain ⟨y, hy⟩ := (bij (S.basicOpen_le f) ⟨fun _ => hs, fun _ => hsW⟩).2
    (resK gp (S.basicOpen_le f) ((gp.app W).hom f) ^ N * x)
  refine ⟨N, y, ?_, hy⟩
  rw [mem_finFam]
  intro i
  have hki : k i ≤ N := Finset.le_sup (Finset.mem_univ i)
  have hmem : resK gp (inf_le_left : W ⊓ V i ≤ W) ((gp.app W).hom f) ^ (N - k i) * w i ∈
      Subring.closure (Set.range (gp.app (W ⊓ V i)).hom ∪
        resK gp (inf_le_right : W ⊓ V i ≤ V i) '' (t i : Set _)) := by
    refine Subring.mul_mem _ (Subring.pow_mem _ ?_ _) (hw i)
    rw [resK_app]
    exact Subring.subset_closure (Or.inl ⟨_, rfl⟩)
  have inj := (bij (hle i) (by simp [hs, hsW])).1
  convert hmem using 1
  apply inj
  rw [map_mul, map_pow, e i, ← _root_.mul_assoc, ← pow_add, Nat.sub_add_cancel hki, resK_resK, resK_resK,
    ← resK_resK gp (S.basicOpen_le f) (inf_le_left : S.basicOpen f ⊓ V i ≤ S.basicOpen f), hy, map_mul, map_pow,
    resK_resK]

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGeneratedSubringLocalisedBasicOpenStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteGeneratedSubring_localised_basicOpen : ∀ {S : Scheme.{0}} {K : Type} [Field K] (gp : Sp K ⟶ S) [IsLocallyNoetherian S] {r : ℕ} (V : Fin r → S.Opens)
    (t : ∀ i, Finset Γ(Sp K, gp ⁻¹ᵁ V i)) (W : S.Opens), IsAffineOpen W → ∀ (f : Γ(S, W))
    (x : Γ(Sp K, gp ⁻¹ᵁ S.basicOpen f)), x ∈ finFam gp V t (S.basicOpen f) →
    ∃ (k : ℕ) (y : Γ(Sp K, gp ⁻¹ᵁ W)), y ∈ finFam gp V t W ∧
      resK gp (S.basicOpen_le f) y = resK gp (S.basicOpen_le f) ((gp.app W).hom f) ^ k * x := by
  first | exact @GlobalTheory.Mum.finFam_basicOpen_loc | exact GlobalTheory.Mum.finFam_basicOpen_loc | (intros; apply GlobalTheory.Mum.finFam_basicOpen_loc <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteModificationIntegralElementsRegular
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem exists_finSub_of_isIntegralElem : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (M : Modif R) (n : ℕ) (U : Fin n → M.S.Opens)
    (b : ∀ m, Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U m)), (∀ m, IsAffineOpen (U m)) →
    (∀ m, (M.gp.app (U m)).hom.IsIntegralElem (b m)) →
    ∃ F : ∀ V : M.S.Opens, Subring Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ V), IsFinSub M.gp F ∧ ∀ m, b m ∈ F (U m) := by
  classical
  intro R _ _ _ M n U b hU hb
  haveI := M.proper
  haveI : IsLocallyNoetherian M.S := LocallyOfFiniteType.isLocallyNoetherian M.π
  haveI : CompactSpace M.S := QuasiCompact.compactSpace_of_compactSpace M.π
  haveI : M.S.IsSeparated := ⟨by rw [← terminal.comp_from M.π]; infer_instance⟩

  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun V : M.S.affineOpens => (V.1 : Set M.S))
    (fun V => V.1.isOpen) (by
      intro x _
      obtain ⟨_, ⟨V, hV, rfl⟩, hx, -⟩ := M.S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
      exact Set.mem_iUnion.2 ⟨⟨V, hV⟩, hx⟩)
  let r := s.card
  let Vc : Fin r → M.S.Opens := fun i => (s.equivFin.symm i).1.1
  have hVa : ∀ i, IsAffineOpen (Vc i) := fun i => (s.equivFin.symm i).1.2
  have hcov : (⨆ i, Vc i) = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨V, hV, hx⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ x))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨s.equivFin ⟨V, hV⟩, by simpa [Vc] using hx⟩
  have hloc : ∀ (i : Fin r) (m : Fin n), ∃ t : Finset Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ Vc i),
      (∀ y ∈ t, (M.gp.app (Vc i)).hom.IsIntegralElem y) ∧
      resK M.gp (inf_le_left : U m ⊓ Vc i ≤ U m) (b m) ∈ Subring.closure (Set.range (M.gp.app (U m ⊓ Vc i)).hom ∪
        resK M.gp (inf_le_right : U m ⊓ Vc i ≤ Vc i) '' (t : Set _)) := by
    intro i m
    refine GlobalTheory.T.mem_subringClosure_of_isIntegralElem_affineOpen_le M.gp (Vc i) (U m ⊓ Vc i) inf_le_right (hVa i) ((hU m).inf (hVa i)) _ ?_
    obtain ⟨p, hp, hpe⟩ := hb m
    refine ⟨p.map (M.S.presheaf.map (homOfLE (inf_le_left : U m ⊓ Vc i ≤ U m)).op).hom, hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have hc : (M.gp.app (U m ⊓ Vc i)).hom.comp (M.S.presheaf.map (homOfLE (inf_le_left : U m ⊓ Vc i ≤ U m)).op).hom =
        (resK M.gp (inf_le_left : U m ⊓ Vc i ≤ U m)).comp (M.gp.app (U m)).hom := by
      ext a; exact (resK_app M.gp _ a).symm
    rw [hc, ← Polynomial.hom_eval₂, hpe, map_zero]
  choose t ht hbt using hloc
  let T : ∀ i, Finset Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ Vc i) := fun i => Finset.univ.biUnion (t i)
  refine ⟨finFam M.gp Vc T, ⟨fun V _ a => finFam_range _ _ _ _ a, fun V V' hle _ _ x hx => finFam_res _ _ _ V V' hle x hx,
    fun V hV f x hx => GlobalTheory.T.finiteGeneratedSubring_localised_basicOpen M.gp Vc T V hV f x hx, fun V hV => GlobalTheory.T.finite_generation_integral_family_sections M.gp Vc T hcov ?_ V hV⟩, ?_⟩
  · intro i y hy
    obtain ⟨m, -, hm⟩ := Finset.mem_biUnion.1 (show y ∈ Finset.univ.biUnion (t i) from hy)
    exact ht i m y hm
  · intro m
    rw [mem_finFam]
    intro i
    refine Subring.closure_mono ?_ (hbt i m)
    rintro _ (h | ⟨z, hz, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨z, show z ∈ Finset.univ.biUnion (t i) from Finset.mem_biUnion.2 ⟨m, Finset.mem_univ _, hz⟩, rfl⟩

theorem finiteModif_regular : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (M : Modif R) (n : ℕ) (U : Fin n → M.S.Opens) (b : ∀ m, Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U m)), (∀ m, IsAffineOpen (U m)) → (∀ m, (M.gp.app (U m)).hom.IsIntegralElem (b m)) → ∃ (M' : Modif R) (h : M'.S ⟶ M.S) (hgp : M'.gp ≫ h = M.gp), IsFinite h ∧ h ≫ M.π = M'.π ∧ ∀ m, ∃ c : Γ(M'.S, h ⁻¹ᵁ U m), (M'.gp.appLE (h ⁻¹ᵁ U m) (M.gp ⁻¹ᵁ U m) (le_preimage_of_comp_eq M.gp M'.gp h hgp (U m))).hom c = b m := by
  intro R _ _ _ M n U b hU hb
  obtain ⟨F, hF, hbF⟩ := exists_finSub_of_isIntegralElem R M n U b hU hb
  haveI : IsIntegral M.S := M.integral
  haveI : IsDominant M.gp := M.dominant
  obtain ⟨S', h, gp', hgp, hfin, hint, hdom, hsec⟩ := GlobalTheory.T.exists_finite_normalization_integral_sections M.gp F hF
  haveI := M.proper
  let M' : Modif R :=
    { S := S', π := h ≫ M.π, proper := inferInstance, integral := hint, gp := gp',
      gp_π := by rw [← Category.assoc, hgp, M.gp_π], dominant := hdom }
  exact ⟨M', h, hgp, hfin, rfl, fun m => hsec (U m) (hU m) (b m) (hbF m)⟩

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteModificationIntegralElementsRegularStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteModification_integral_elements_regular : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (M : Modif R) (n : ℕ) (U : Fin n → M.S.Opens) (b : ∀ m, Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U m)), (∀ m, IsAffineOpen (U m)) → (∀ m, (M.gp.app (U m)).hom.IsIntegralElem (b m)) → ∃ (M' : Modif R) (h : M'.S ⟶ M.S) (hgp : M'.gp ≫ h = M.gp), IsFinite h ∧ h ≫ M.π = M'.π ∧ ∀ m, ∃ c : Γ(M'.S, h ⁻¹ᵁ U m), (M'.gp.appLE (h ⁻¹ᵁ U m) (M.gp ⁻¹ᵁ U m) (le_preimage_of_comp_eq M.gp M'.gp h hgp (U m))).hom c = b m := by
  first | exact @GlobalTheory.Mum.finiteModif_regular | exact GlobalTheory.Mum.finiteModif_regular | (intros; apply GlobalTheory.Mum.finiteModif_regular <;> assumption)
end
