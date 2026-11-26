module

public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineResolutionRuleCompatibility
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.GluedBlowupSequenceExistence
public import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.StandardSmoothCharts
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.LocalResolutionData

@[expose] public section

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.LocalResolutionDense
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace LocalResolutionData

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}
  [LocallyOfFiniteType f] {s : SequenceOfBlowups X}

theorem dense_preimage_smoothLocus (d : LocalResolutionData k f s) :
    Dense ((s.lastStructMap ⁻¹ᵁ f.smoothLocus : TopologicalSpace.Opens ↥(s.lastObj)) : Set ↥(s.lastObj)) := by
  rw [dense_iff_inter_open]
  intro V hV hVne
  obtain ⟨x, hxV⟩ := hVne
  obtain ⟨i, y, hy⟩ := d.exists_chartToLastObj_eq x
  have hres := (d.isResolution i).2.2.2.1
  have hW : IsOpen (((d.chartToLastObj i) ⁻¹ᵁ (⟨V, hV⟩ : TopologicalSpace.Opens ↥(s.lastObj)) :
      TopologicalSpace.Opens ↥((d.seq i).lastObj)) : Set ↥((d.seq i).lastObj)) :=
    ((d.chartToLastObj i) ⁻¹ᵁ (⟨V, hV⟩ : TopologicalSpace.Opens ↥(s.lastObj))).2
  have hyW : y ∈ (((d.chartToLastObj i) ⁻¹ᵁ (⟨V, hV⟩ : TopologicalSpace.Opens ↥(s.lastObj)) :
      TopologicalSpace.Opens ↥((d.seq i).lastObj)) : Set ↥((d.seq i).lastObj)) := by
    show (d.chartToLastObj i).base y ∈ V
    rw [hy]
    exact hxV
  obtain ⟨z, hz1, hz2⟩ := dense_iff_inter_open.mp hres _ hW ⟨y, hyW⟩
  refine ⟨(d.chartToLastObj i).base z, hz1, ?_⟩
  have hmem : ((d.seq i).lastStructMap).base z ∈ (d.cover.f i) ⁻¹ᵁ f.smoothLocus := by
    rw [d.preimage_smoothLocus_cover_map i]
    exact hz2
  have hbase : (s.lastStructMap).base ((d.chartToLastObj i).base z)
      = (d.cover.f i).base (((d.seq i).lastStructMap).base z) := by
    have h := congrArg (fun m : (d.seq i).lastObj ⟶ X => m.base z) (d.chartToLastObj_comp_lastStructMap i)
    simpa using h
  show (s.lastStructMap).base ((d.chartToLastObj i).base z) ∈ f.smoothLocus
  rw [hbase]
  exact hmem

end LocalResolutionData

end FunctorialResolution.EmbeddedResolution

end
end

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.LocalResolutionSmooth
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace LocalResolutionData

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}
  [LocallyOfFiniteType f] {s : SequenceOfBlowups X}

theorem chartToLastObj_comp_lastStructMap_assoc (d : LocalResolutionData k f s) (j : d.cover.I₀) :
    d.chartToLastObj j ≫ (s.lastStructMap ≫ f) = (d.seq j).lastStructMap ≫ (d.cover.f j ≫ f) := by
  rw [← Category.assoc, d.chartToLastObj_comp_lastStructMap j, Category.assoc]

private theorem ringHom_smooth_appTop_of_smooth {A B : Scheme.{u}} [AlgebraicGeometry.IsAffine B]
    (g : A ⟶ B) (𝒲 : Scheme.OpenCover.{u, u} A)
    [∀ i, AlgebraicGeometry.IsAffine (𝒲.X i)]
    (hg : AlgebraicGeometry.Smooth g) (i : 𝒲.I₀) :
    RingHom.Smooth ((𝒲.f i ≫ g).appTop.hom) :=
  (AlgebraicGeometry.HasRingHomProperty.iff_of_source_openCover 𝒲).mp hg i

private theorem smooth_of_ringHom_smooth_appTop {A B : Scheme.{u}} [AlgebraicGeometry.IsAffine B]
    (g : A ⟶ B) (𝒲 : Scheme.OpenCover.{u, u} A)
    [∀ i, AlgebraicGeometry.IsAffine (𝒲.X i)]
    (h : ∀ i : 𝒲.I₀, RingHom.Smooth ((𝒲.f i ≫ g).appTop.hom)) :
    AlgebraicGeometry.Smooth g :=
  (AlgebraicGeometry.HasRingHomProperty.iff_of_source_openCover 𝒲).mpr h

private theorem smooth_chartToLastObj_comp (d : LocalResolutionData k f s) (j : d.cover.I₀) :
    AlgebraicGeometry.Smooth (d.chartToLastObj j ≫ (s.lastStructMap ≫ f)) := by
  rw [d.chartToLastObj_comp_lastStructMap_assoc j]
  exact (d.isResolution j).1

private theorem smooth_appTop_affineCover_chartToLastObj (d : LocalResolutionData k f s) (j : d.cover.I₀)
    (a : ((d.seq j).lastObj.affineCover).I₀) :
    RingHom.Smooth (((((d.seq j).lastObj.affineCover).f a ≫ d.chartToLastObj j)
      ≫ (s.lastStructMap ≫ f)).appTop.hom) := by
  have h := ringHom_smooth_appTop_of_smooth (d.chartToLastObj j ≫ (s.lastStructMap ≫ f))
    ((d.seq j).lastObj.affineCover) (smooth_chartToLastObj_comp d j) a
  rw [Category.assoc]
  exact h

theorem smooth_lastStructMap_comp (d : LocalResolutionData k f s) :
    AlgebraicGeometry.Smooth (s.lastStructMap ≫ f) := by
  have haffine : ∀ i : (d.lastObjCover.bind fun j => (d.lastObjCover.X j).affineCover).I₀,
      AlgebraicGeometry.IsAffine
        ((d.lastObjCover.bind fun j => (d.lastObjCover.X j).affineCover).X i) := by
    rintro ⟨j, a⟩
    exact inferInstanceAs (AlgebraicGeometry.IsAffine (((d.lastObjCover.X j).affineCover).X a))
  refine smooth_of_ringHom_smooth_appTop (s.lastStructMap ≫ f)
    (d.lastObjCover.bind fun j => (d.lastObjCover.X j).affineCover) ?_
  rintro ⟨j, a⟩
  exact smooth_appTop_affineCover_chartToLastObj d j a

end LocalResolutionData

end FunctorialResolution.EmbeddedResolution

end
end

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.LocalResolutionProper
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace LocalResolutionData

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}
  [LocallyOfFiniteType f] {s : SequenceOfBlowups X}

def pullbackIsoLastObj (d : LocalResolutionData k f s) (i : d.cover.I₀) :
    ((pullback s.lastStructMap (d.cover.f i) : Scheme.{u}) ≅ (d.seq i).lastObj) :=
  (pullbackSymmetry s.lastStructMap (d.cover.f i)).trans (d.lastObjIsoPullback i).symm

theorem pullbackIsoLastObj_hom_lastStructMap (d : LocalResolutionData k f s) (i : d.cover.I₀) :
    (d.pullbackIsoLastObj i).hom ≫ (d.seq i).lastStructMap = pullback.snd s.lastStructMap (d.cover.f i) := by
  rw [pullbackIsoLastObj]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [← d.lastObjIsoPullback_hom_fst i, Iso.inv_hom_id_assoc]
  exact pullbackSymmetry_hom_comp_fst _ _

theorem isProper_lastStructMap (d : LocalResolutionData k f s) : IsProper s.lastStructMap := by
  have key : ∀ i : d.cover.I₀, IsProper (d.seq i).lastStructMap := by
    intro i
    obtain ⟨-, h, -⟩ := d.isResolution i
    exact h
  obtain ⟨-, h2⟩ := (inferInstance :
    MorphismProperty.IsLocalAtTarget (@IsProper) Scheme.zariskiPrecoverage)
  refine h2 (R := d.cover.presieve₀) d.cover.mem₀ ?_
  intro U g _inst hg
  obtain ⟨i⟩ := hg
  rw [← d.pullbackIsoLastObj_hom_lastStructMap i]
  have := key i
  infer_instance

end LocalResolutionData

end FunctorialResolution.EmbeddedResolution

end
end

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.LocalResolutionStrictNormalCrossings
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

namespace LocalResolutionData

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}
  [LocallyOfFiniteType f] {s : SequenceOfBlowups X}

private theorem support_vanishingIdeal_eq {Y : Scheme.{u}} (Z : Closeds ↥Y) :
    (Scheme.IdealSheafData.vanishingIdeal Z).support = Z := rfl

private theorem comap_vanishingIdeal_of_isOpenImmersion {Y T : Scheme.{u}} (g : T ⟶ Y)
    [IsOpenImmersion g] (Z : Closeds ↥Y) (W : Closeds ↥T)
    (hW : (W : Set ↥T) = g.base ⁻¹' (Z : Set ↥Y)) :
    (Scheme.IdealSheafData.vanishingIdeal Z).comap g
      = Scheme.IdealSheafData.vanishingIdeal W := by
  have hrad : ((Scheme.IdealSheafData.vanishingIdeal Z).comap g).radical
      = (Scheme.IdealSheafData.vanishingIdeal Z).comap g := by
    refine Scheme.IdealSheafData.ext (funext fun U => ?_)
    rw [Scheme.IdealSheafData.radical_ideal,
      Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
      Scheme.IdealSheafData.vanishingIdeal_ideal]
    exact ((PrimeSpectrum.isRadical_vanishingIdeal _).comap _).radical
  have hsupp : ((Scheme.IdealSheafData.vanishingIdeal Z).comap g).support = W := by
    rw [Scheme.IdealSheafData.support_comap, support_vanishingIdeal_eq]
    exact TopologicalSpace.Closeds.ext hW.symm
  rw [← hsupp, Scheme.IdealSheafData.vanishingIdeal_support, hrad]

private theorem isRegularParameterSystem_map_ringEquiv {R S : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) (n : ℕ) (x : Fin n → R)
    (h : IsRegularParameterSystem R n x) :
    IsRegularParameterSystem S n (fun i => e (x i)) := by
  unfold IsRegularParameterSystem at h ⊢
  obtain ⟨h1, h2⟩ := h
  constructor
  · have hmax : Ideal.comap (e : R →+* S) (IsLocalRing.maximalIdeal S)
        = IsLocalRing.maximalIdeal R :=
      IsLocalRing.eq_maximalIdeal
        (Ideal.comap_isMaximal_of_surjective (e : R →+* S) e.surjective)
    have hm : Ideal.map (e : R →+* S) (IsLocalRing.maximalIdeal R)
        = IsLocalRing.maximalIdeal S := by
      rw [← hmax]
      exact Ideal.map_comap_of_surjective (e : R →+* S) e.surjective _
    have himg : Ideal.span (Set.range fun i => e (x i))
        = Ideal.map (e : R →+* S) (Ideal.span (Set.range x)) := by
      rw [Ideal.map_span]
      congr 1
      ext b
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨x i, ⟨i, rfl⟩, rfl⟩
      · rintro ⟨a, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
    rw [himg, h1, hm]
  · rw [h2]
    exact ringKrullDim_eq_of_ringEquiv e

private theorem isRegularParameterSystem_of_ringEquiv_apply_eq {R S : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) (n : ℕ) (x : Fin n → R) (y : Fin n → S)
    (hxy : ∀ i, e (x i) = y i) (h : IsRegularParameterSystem R n x) :
    IsRegularParameterSystem S n y := by
  have hy : y = fun i => e (x i) := (funext fun i => hxy i).symm
  subst hy
  exact isRegularParameterSystem_map_ringEquiv e n x h

private theorem surjective_iso_inv {A B : CommRingCat.{u}} (e : A ≅ B) :
    Function.Surjective (CommRingCat.Hom.hom e.inv) := by
  intro a
  refine ⟨(CommRingCat.Hom.hom e.hom) a, ?_⟩
  simp

private theorem map_eqToHom_germ {T : Scheme.{u}} {U V : T.Opens}
    (h : Opposite.op U = Opposite.op V) (z : ↥T) (hz : z ∈ U) (hz' : z ∈ V) :
    T.presheaf.map (eqToHom h) ≫ T.presheaf.germ V z hz' = T.presheaf.germ U z hz := by
  have h' : U = V := congrArg Opposite.unop h
  subst h'
  simp

private theorem appIso_inv_germ_stalkMap {Y T : Scheme.{u}} (g : T ⟶ Y) [IsOpenImmersion g]
    (U : T.Opens) (z : ↥T) (hz : z ∈ U) (hgz : g.base z ∈ (g ''ᵁ U : Y.Opens)) :
    (Scheme.Hom.appIso g U).inv ≫ Y.presheaf.germ (g ''ᵁ U) (g.base z) hgz ≫
        Scheme.Hom.stalkMap g z = T.presheaf.germ U z hz := by
  have h1 : Y.presheaf.germ (g ''ᵁ U) (g.base z) hgz ≫ Scheme.Hom.stalkMap g z
      = Scheme.Hom.app g (g ''ᵁ U) ≫ T.presheaf.germ (g ⁻¹ᵁ (g ''ᵁ U)) z hgz :=
    Scheme.Hom.germ_stalkMap g (g ''ᵁ U) z hgz
  rw [h1, ← Category.assoc]
  simp
  exact map_eqToHom_germ _ z hz hgz

private theorem appIso_inv_germ_stalkMap_apply {Y T : Scheme.{u}} (g : T ⟶ Y) [IsOpenImmersion g]
    (U : T.Opens) (z : ↥T) (hz : z ∈ U) (hgz : g.base z ∈ (g ''ᵁ U : Y.Opens))
    (a : Γ(T, U)) :
    (ConcreteCategory.hom (Scheme.Hom.stalkMap g z))
        ((ConcreteCategory.hom (Y.presheaf.germ (g ''ᵁ U) (g.base z) hgz))
          ((ConcreteCategory.hom (Scheme.Hom.appIso g U).inv) a))
      = (ConcreteCategory.hom (T.presheaf.germ U z hz)) a := by
  have h := congrArg (fun m : Γ(T, U) ⟶ T.presheaf.stalk z => (ConcreteCategory.hom m) a)
    (appIso_inv_germ_stalkMap g U z hz hgz)
  simpa only [CommRingCat.comp_apply] using h

theorem chartToLastObj_preimage_smoothLocusComplement (d : LocalResolutionData k f s) (i : d.cover.I₀)
    [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation (d.cover.f i ≫ f)] :
    (d.chartToLastObj i).base ⁻¹'
        (s.lastStructMap.base ⁻¹' ((smoothLocusComplement f : Closeds ↥X) : Set ↥X))
      = (d.seq i).lastStructMap.base ⁻¹'
        ((smoothLocusComplement (d.cover.f i ≫ f) : Closeds ↥(d.cover.X i)) : Set ↥(d.cover.X i)) := by
  have hcomp := d.chartToLastObj_comp_lastStructMap i
  have hsl := d.preimage_smoothLocusComplement_cover_map i
  ext x
  simp only [Set.mem_preimage]
  have hx : s.lastStructMap.base ((d.chartToLastObj i).base x)
      = (d.cover.f i).base ((d.seq i).lastStructMap.base x) := by
    have h := congrArg (fun g : (d.seq i).lastObj ⟶ X => g.base x) hcomp
    simpa using h
  rw [hx, ← Set.mem_preimage, hsl]

theorem comap_reducedInverseImage_chartToLastObj (d : LocalResolutionData k f s) (i : d.cover.I₀)
    [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation (d.cover.f i ≫ f)] :
    (reducedInverseImage s.lastStructMap (smoothLocusComplement f)).comap (d.chartToLastObj i)
      = reducedInverseImage (d.seq i).lastStructMap (smoothLocusComplement (d.cover.f i ≫ f)) := by
  have h1 := d.chartToLastObj_preimage_smoothLocusComplement i
  unfold reducedInverseImage
  exact comap_vanishingIdeal_of_isOpenImmersion (d.chartToLastObj i) _ _ h1.symm

private theorem isStrictNormalCrossingsDivisor_of_openCover {Y : Scheme.{u}} (I : Y.IdealSheafData)
    (H : ∀ y : ↥Y, ∃ (T : Scheme.{u}) (g : T ⟶ Y) (_ : IsOpenImmersion g) (z : ↥T),
      g.base z = y ∧ IsStrictNormalCrossingsDivisor (I.comap g)) : IsStrictNormalCrossingsDivisor I := by
  intro y
  obtain ⟨T, g, hg, z, hzy, hSNC⟩ := H y
  subst hzy
  have := hg
  obtain ⟨hreg, U, hzU, n, F, J, hpar, hid⟩ := hSNC z
  have : IsRegularLocalRing ↑(T.presheaf.stalk z) := hreg
  obtain ⟨E, hE⟩ : ∃ E : (↑(Y.presheaf.stalk (g.base z)) : Type u) ≃+* ↑(T.presheaf.stalk z),
      ∀ x, E x = (ConcreteCategory.hom (Scheme.Hom.stalkMap g z)) x :=
    ⟨(asIso (Scheme.Hom.stalkMap g z)).commRingCatIsoToRingEquiv, fun _ => rfl⟩
  have hgz : g.base z ∈ (g ''ᵁ (U : T.Opens) : Y.Opens) := ⟨z, hzU, rfl⟩
  have hVaff : IsAffineOpen (g ''ᵁ (U : T.Opens)) :=
    (U.2 : IsAffineOpen (U : T.Opens)).image_of_isOpenImmersion g
  have hsurj : Function.Surjective
      (CommRingCat.Hom.hom (Scheme.Hom.appIso g (U : T.Opens)).inv) :=
    surjective_iso_inv (Scheme.Hom.appIso g (U : T.Opens))
  refine ⟨IsRegularLocalRing.of_ringEquiv E.symm,
    ⟨g ''ᵁ (U : T.Opens), hVaff⟩, hgz, n,
    fun i => (ConcreteCategory.hom (Scheme.Hom.appIso g (U : T.Opens)).inv) (F i), J, ?_, ?_⟩
  · refine isRegularParameterSystem_of_ringEquiv_apply_eq E.symm n _ _ ?_ hpar
    intro i
    have hgerm := appIso_inv_germ_stalkMap_apply g (U : T.Opens) z hzU hgz (F i)
    rw [← hE] at hgerm
    rw [← hgerm, E.symm_apply_apply]
  · have h1 := Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion I g U
    rw [hid] at h1
    have h2 : Ideal.map (CommRingCat.Hom.hom (Scheme.Hom.appIso g (U : T.Opens)).inv)
        (Ideal.span {∏ i ∈ J, F i})
        = Ideal.span {∏ i ∈ J,
            (CommRingCat.Hom.hom (Scheme.Hom.appIso g (U : T.Opens)).inv) (F i)} := by
      rw [Ideal.map_span, Set.image_singleton, map_prod]
    have h3 : Ideal.map (CommRingCat.Hom.hom (Scheme.Hom.appIso g (U : T.Opens)).inv)
        (Ideal.comap (CommRingCat.Hom.hom (Scheme.Hom.appIso g (U : T.Opens)).inv)
          (I.ideal ⟨g ''ᵁ (U : T.Opens), hVaff⟩))
        = I.ideal ⟨g ''ᵁ (U : T.Opens), hVaff⟩ :=
      Ideal.map_comap_of_surjective _ hsurj _
    exact (h3.symm.trans
      (congrArg (Ideal.map (CommRingCat.Hom.hom (Scheme.Hom.appIso g (U : T.Opens)).inv))
        h1.symm)).trans h2

theorem isStrictNormalCrossingsDivisor_reducedInverseImage (d : LocalResolutionData k f s) [LocallyOfFinitePresentation f] :
    IsStrictNormalCrossingsDivisor (reducedInverseImage s.lastStructMap (smoothLocusComplement f)) := by
  refine isStrictNormalCrossingsDivisor_of_openCover _ ?_
  intro y
  obtain ⟨i, z, hz⟩ := d.exists_chartToLastObj_eq y
  refine ⟨(d.seq i).lastObj, d.chartToLastObj i, inferInstance, z, hz, ?_⟩
  rw [d.comap_reducedInverseImage_chartToLastObj i]
  exact (d.isResolution i).2.2.2.2.2

end LocalResolutionData

end FunctorialResolution.EmbeddedResolution
end

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.LocalResolutionCenters
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

namespace LocalResolutionData

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}
  [LocallyOfFiniteType f] {s : SequenceOfBlowups X}

private theorem comp_base_apply {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) (z : ↥A) :
    (a ≫ b).base z = b.base (a.base z) := by
  simp

private theorem hom_base_inv_base_apply {A B : Scheme.{u}} (e : A ≅ B) (z : ↥B) :
    e.hom.base (e.inv.base z) = z := by
  rw [← comp_base_apply, e.inv_hom_id]
  simp

private theorem mem_support_comap_of_mem_support {Z W : Scheme.{u}} (g : Z ⟶ W) (I : W.IdealSheafData)
    (z : ↥Z) (hz : g.base z ∈ I.support) : z ∈ (I.comap g).support := by
  rw [Scheme.IdealSheafData.support_comap]
  exact hz

theorem centersLieOver_smoothLocusComplement (d : LocalResolutionData k f s) :
    s.CentersLieOver ((smoothLocusComplement f : TopologicalSpace.Closeds ↥X) : Set ↥X) := by
  intro i hi x hx
  obtain ⟨i₀, u, hu⟩ : ∃ (i₀ : d.cover.I₀) (u : ↥(d.cover.X i₀)),
      (d.cover.f i₀).base u = (s.projectionToBase i).base x := by
    obtain ⟨u, hu⟩ := d.cover.covers ((s.projectionToBase i).base x)
    exact ⟨d.cover.idx ((s.projectionToBase i).base x), u, hu⟩
  obtain ⟨w, hw1, hw2⟩ := Scheme.Pullback.exists_preimage_pullback u x hu
  have hw1' : (pullback.fst (d.cover.f i₀) (s.projectionToBase i)).base w = u := hw1
  have hw2' : (pullback.snd (d.cover.f i₀) (s.projectionToBase i)).base w = x := hw2
  have hws : w ∈ ((s.center i).comap (pullback.snd (d.cover.f i₀) (s.projectionToBase i))).support := by
    refine mem_support_comap_of_mem_support _ _ _ ?_
    rw [hw2']
    exact hx
  obtain ⟨l, hl, hr⟩ := (d.exists_reindex_eq_iff_exists_mem_support i₀ i hi).2 ⟨w, hws⟩
  subst hr
  have ht : ((d.schemeAtIsoPullback i₀ l hl.le).inv.base w) ∈ ((d.seq i₀).center l).support := by
    rw [d.localSequence_center_eq_comap i₀ l hl]
    refine mem_support_comap_of_mem_support _ _ _ ?_
    rw [comp_base_apply, hom_base_inv_base_apply, hw2']
    exact hx
  have key : ((d.seq i₀).projectionToBase l).base ((d.schemeAtIsoPullback i₀ l hl.le).inv.base w)
      = (pullback.fst (d.cover.f i₀) (s.projectionToBase (d.reindex i₀ l))).base w := by
    rw [← d.schemeAtIsoPullback_hom_fst i₀ l hl.le, comp_base_apply, hom_base_inv_base_apply]
  have hres := d.isResolution i₀
  unfold FunctorialResolution.EmbeddedResolution.IsStrongResolution at hres
  obtain ⟨-, -, -, -, hC, -⟩ := hres
  have hCt : ((d.seq i₀).projectionToBase l).base ((d.schemeAtIsoPullback i₀ l hl.le).inv.base w) ∈
      ((smoothLocusComplement (d.cover.f i₀ ≫ f) : TopologicalSpace.Closeds ↥(d.cover.X i₀)) :
        Set ↥(d.cover.X i₀)) := hC l hl _ ht
  rw [← d.preimage_smoothLocusComplement_cover_map i₀] at hCt
  have hfin : (d.cover.f i₀).base
      (((d.seq i₀).projectionToBase l).base ((d.schemeAtIsoPullback i₀ l hl.le).inv.base w)) ∈
      ((smoothLocusComplement f : TopologicalSpace.Closeds ↥X) : Set ↥X) := hCt
  show (s.projectionToBase (d.reindex i₀ l)).base x ∈
    ((smoothLocusComplement f : TopologicalSpace.Closeds ↥X) : Set ↥X)
  rw [← hu, ← hw1', ← key]
  exact hfin

end LocalResolutionData

end FunctorialResolution.EmbeddedResolution
end

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.SmoothLocusIsomorphism
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace LocalResolutionData

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}
  [LocallyOfFiniteType f] {s : SequenceOfBlowups X}

theorem isPullback_chartToLastObj (d : LocalResolutionData k f s) (i : d.cover.I₀) :
    IsPullback (d.chartToLastObj i) ((d.seq i).lastStructMap) s.lastStructMap (d.cover.f i) := by
  have hsq : CommSq ((d.seq i).lastStructMap) (d.chartToLastObj i) (d.cover.f i) s.lastStructMap :=
    ⟨(d.chartToLastObj_comp_lastStructMap i).symm⟩
  have h : IsPullback ((d.seq i).lastStructMap) (d.chartToLastObj i) (d.cover.f i) s.lastStructMap :=
    IsPullback.of_iso_pullback hsq (d.lastObjIsoPullback i) (d.lastObjIsoPullback_hom_fst i)
      (d.chartToLastObj_eq i).symm
  exact h.flip

private theorem isIso_pullback_snd_restrict_smoothLocus (d : LocalResolutionData k f s) (i : d.cover.I₀) :
    IsIso (pullback.snd (s.lastStructMap ∣_ f.smoothLocus) (d.cover.f i ∣_ f.smoothLocus)) := by
  have hp := isPullback_morphismRestrict s.lastStructMap f.smoothLocus
  have hc := isPullback_morphismRestrict (d.cover.f i) f.smoothLocus
  have ht := isPullback_morphismRestrict ((d.seq i).lastStructMap) (d.cover.f i ⁻¹ᵁ f.smoothLocus)
  have hbig := ht.paste_vert (d.isPullback_chartToLastObj i).flip
  have hw : (((d.seq i).lastStructMap ∣_ (d.cover.f i ⁻¹ᵁ f.smoothLocus)) ≫
        (d.cover.f i ∣_ f.smoothLocus)) ≫ f.smoothLocus.ι
      = ((((d.seq i).lastStructMap ⁻¹ᵁ (d.cover.f i ⁻¹ᵁ f.smoothLocus)).ι) ≫ d.chartToLastObj i)
        ≫ s.lastStructMap := by
    rw [Category.assoc, hc.w]
    exact hbig.w
  have hsq : IsPullback ((d.seq i).lastStructMap ∣_ (d.cover.f i ⁻¹ᵁ f.smoothLocus))
      (hp.lift _ _ hw) (d.cover.f i ∣_ f.smoothLocus) (s.lastStructMap ∣_ f.smoothLocus) := by
    refine IsPullback.of_bot ?_ ?_ hp
    · rw [hp.lift_snd, hc.w]
      exact hbig
    · rw [hp.lift_fst]
  have hiso : IsIso ((d.seq i).lastStructMap ∣_ (d.cover.f i ⁻¹ᵁ f.smoothLocus)) := by
    rw [d.preimage_smoothLocus_cover_map i]
    exact (d.isResolution i).2.2.1
  have hcomp : IsIso (hsq.flip.isoPullback.hom ≫
      pullback.snd (s.lastStructMap ∣_ f.smoothLocus) (d.cover.f i ∣_ f.smoothLocus)) := by
    rw [hsq.flip.isoPullback_hom_snd]
    exact hiso
  exact IsIso.of_isIso_comp_left hsq.flip.isoPullback.hom
    (pullback.snd (s.lastStructMap ∣_ f.smoothLocus) (d.cover.f i ∣_ f.smoothLocus))

private theorem exists_restrict_smoothLocus_apply_eq (d : LocalResolutionData k f s) :
    ∀ x : ↥(f.smoothLocus.toScheme), ∃ (i : d.cover.I₀)
      (y : ↥((d.cover.f i ⁻¹ᵁ f.smoothLocus).toScheme)),
        (d.cover.f i ∣_ f.smoothLocus) y = x := by
  intro x
  have hsup : (⨆ i, (d.cover.f i).opensRange) = ⊤ := d.cover.iSup_opensRange
  have hx : (x.1 : ↥X) ∈ (⨆ i, (d.cover.f i).opensRange : X.Opens) := by
    rw [hsup]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  have hi' : (x.1 : ↥X) ∈ Set.range (d.cover.f i).base := hi
  obtain ⟨y₀, hy₀⟩ := hi'
  have hmem : y₀ ∈ (d.cover.f i ⁻¹ᵁ f.smoothLocus) := by
    show (d.cover.f i).base y₀ ∈ f.smoothLocus
    rw [hy₀]
    exact x.2
  refine ⟨i, ⟨y₀, hmem⟩, ?_⟩
  have h2 := congrFun (morphismRestrict_base (d.cover.f i) f.smoothLocus) ⟨y₀, hmem⟩
  refine h2.trans (Subtype.ext ?_)
  exact hy₀

private def smoothLocusOpenCover (d : LocalResolutionData k f s) :
    Scheme.OpenCover.{u, u} (f.smoothLocus.toScheme) :=
  Scheme.Cover.mkOfCovers d.cover.I₀
    (fun i => (d.cover.f i ⁻¹ᵁ f.smoothLocus).toScheme)
    (fun i => d.cover.f i ∣_ f.smoothLocus)
    (exists_restrict_smoothLocus_apply_eq d)
    (fun i => show IsOpenImmersion (d.cover.f i ∣_ f.smoothLocus) from inferInstance)

theorem isIso_lastStructMap_restrict_smoothLocus (d : LocalResolutionData k f s) :
    IsIso (s.lastStructMap ∣_ f.smoothLocus) := by
  have hh : ∀ i : d.cover.I₀, MorphismProperty.isomorphisms Scheme.{u}
      (Scheme.Cover.pullbackHom (smoothLocusOpenCover d) (s.lastStructMap ∣_ f.smoothLocus) i) := by
    intro i
    exact isIso_pullback_snd_restrict_smoothLocus d i
  have key : MorphismProperty.isomorphisms Scheme.{u} (s.lastStructMap ∣_ f.smoothLocus) :=
    IsZariskiLocalAtTarget.of_openCover (smoothLocusOpenCover d) hh
  exact key

end LocalResolutionData

end FunctorialResolution.EmbeddedResolution

end
end

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

def IsCompatibleWithSmoothOfRelativeDimension (B : AffineResolutionRule.{u}) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (Y V : Scheme.{u})
    (pY : Y ⟶ Spec (CommRingCat.of k)) (pV : V ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.IsAffine Y] [AlgebraicGeometry.IsAffine V]
    [AlgebraicGeometry.IsReduced Y] [AlgebraicGeometry.IsReduced V]
    [AlgebraicGeometry.LocallyOfFiniteType pY] [AlgebraicGeometry.QuasiCompact pY]
    [AlgebraicGeometry.LocallyOfFiniteType pV] [AlgebraicGeometry.QuasiCompact pV]
    (u : V ⟶ Y) (r : ℕ) [AlgebraicGeometry.SmoothOfRelativeDimension r u],
    u ≫ pY = pV → IsPullbackBlowupSequence u (B k V pV) (B k Y pY)

theorem isCompatibleWithSmoothOfRelativeDimension_affineResolutionRule (A : PrincipalizationAlgorithm.{u})
    (hAlg : IsFunctorialPrincipalization A) (hw : TransitionsAreBlowupsForEmbeddings A)
    (hemb : AffineEmbedsIntoAffineSpace.{u}) (hsncE : NilIsStrictNormalCrossingsOnAffineSpace.{u})
    (hsm : AffineSpaceIsSmooth.{u}) (hex : EmbeddedPrincipalizationYieldsBlowups A hemb hsncE hsm)
    (hcmp : ClosedEmbeddingsRelatedByAutomorphism.{u}) :
    IsCompatibleWithSmoothOfRelativeDimension (affineResolutionRuleOfPrincipalization A hemb hsncE hsm hex) := by
  intro k _ _ Y V pY pV _ _ _ _ _ _ _ _ u r _ hu
  exact isPullbackBlowupSequence_affineResolutionRuleOfPrincipalization_of_smooth A hAlg hw hemb hsncE hsm hex hcmp
    k Y V pY pV u r hu

private theorem smoothOfRelativeDimension_comp_zero {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (r : ℕ) [AlgebraicGeometry.SmoothOfRelativeDimension r f]
    [AlgebraicGeometry.SmoothOfRelativeDimension 0 g] :
    AlgebraicGeometry.SmoothOfRelativeDimension r (f ≫ g) := by
  have h : AlgebraicGeometry.SmoothOfRelativeDimension (r + 0) (f ≫ g) := inferInstance
  simpa using h

private theorem smoothOfRelativeDimension_zero_comp {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (r : ℕ) [AlgebraicGeometry.SmoothOfRelativeDimension 0 f]
    [AlgebraicGeometry.SmoothOfRelativeDimension r g] :
    AlgebraicGeometry.SmoothOfRelativeDimension r (f ≫ g) := by
  have h : AlgebraicGeometry.SmoothOfRelativeDimension (0 + r) (f ≫ g) := inferInstance
  simpa using h

private theorem opensImage_le_preimage {X Y : Scheme.{u}} (f : X ⟶ Y) (Z : X.Opens) (U₀ : Y.Opens)
    (W : Z.toScheme.Opens) (e : W ≤ (Z.ι ≫ f) ⁻¹ᵁ U₀) : Z.ι ''ᵁ W ≤ f ⁻¹ᵁ U₀ := by
  rintro x ⟨w, hw, rfl⟩
  simpa using e hw

private theorem respectsIso_smoothOfRelativeDimension (r : ℕ) :
    MorphismProperty.RespectsIso
      (@AlgebraicGeometry.SmoothOfRelativeDimension r : MorphismProperty Scheme.{u}) := by
  have hL : MorphismProperty.RespectsLeft
      (@AlgebraicGeometry.SmoothOfRelativeDimension r : MorphismProperty Scheme.{u})
      (MorphismProperty.isomorphisms Scheme.{u}) := by
    constructor
    intro X Y Z i hi f hf
    have : CategoryTheory.IsIso i := hi
    have : AlgebraicGeometry.IsOpenImmersion i := inferInstance
    have : AlgebraicGeometry.SmoothOfRelativeDimension 0 i := inferInstance
    have := hf
    exact smoothOfRelativeDimension_zero_comp i f r
  have hR : MorphismProperty.RespectsRight
      (@AlgebraicGeometry.SmoothOfRelativeDimension r : MorphismProperty Scheme.{u})
      (MorphismProperty.isomorphisms Scheme.{u}) := by
    constructor
    intro X Y Z i hi f hf
    have : CategoryTheory.IsIso i := hi
    have : AlgebraicGeometry.IsOpenImmersion i := inferInstance
    have : AlgebraicGeometry.SmoothOfRelativeDimension 0 i := inferInstance
    have := hf
    exact smoothOfRelativeDimension_comp_zero f i r
  exact ⟨⟩

private theorem smoothOfRelativeDimension_of_iSup_eq_top (r : ℕ) {X Y : Scheme.{u}} (f : X ⟶ Y)
    {ι : Type u} (U : ι → X.Opens) (hU : iSup U = ⊤)
    (H : ∀ i, AlgebraicGeometry.SmoothOfRelativeDimension r ((U i).ι ≫ f)) :
    AlgebraicGeometry.SmoothOfRelativeDimension r f := by
  refine ⟨fun x => ?_⟩
  have htop : x ∈ (⊤ : X.Opens) := trivial
  rw [← hU] at htop
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp htop
  obtain ⟨H'⟩ := H i
  obtain ⟨U₀, hU₀, W, hW, hxW, e, hsm⟩ := H' ⟨x, hi⟩
  have e' : (U i).ι ''ᵁ W ≤ f ⁻¹ᵁ U₀ := opensImage_le_preimage f (U i) U₀ W e
  have hle : W ≤ (U i).ι ⁻¹ᵁ ((U i).ι ''ᵁ W) := by
    intro w hw
    exact ⟨w, hw, rfl⟩
  refine ⟨U₀, hU₀, (U i).ι ''ᵁ W, hW.image_of_isOpenImmersion (U i).ι,
    ⟨⟨x, hi⟩, hxW, rfl⟩, e', ?_⟩
  have h1 := Scheme.Hom.appLE_comp_appLE (U i).ι f U₀ ((U i).ι ''ᵁ W) W e' hle
  have h2 := Scheme.Opens.ι_appLE (U i) ((U i).ι ''ᵁ W) W hle
  have h3 : X.presheaf.map (homOfLE (le_refl ((U i).ι ''ᵁ W))).op
      = 𝟙 (X.presheaf.obj (Opposite.op ((U i).ι ''ᵁ W))) := by
    simp
  have h23 := h2.trans h3
  have key : ((U i).ι ≫ f).appLE U₀ W e = f.appLE U₀ ((U i).ι ''ᵁ W) e' :=
    h1.symm.trans ((congrArg (fun m => f.appLE U₀ ((U i).ι ''ᵁ W) e' ≫ m) h23).trans
      (Category.comp_id _))
  exact Eq.mp (congrArg (fun m =>
    RingHom.IsStandardSmoothOfRelativeDimension r (CommRingCat.Hom.hom m)) key) hsm

private theorem isZariskiLocalAtSource_smoothOfRelativeDimension (r : ℕ) :
    AlgebraicGeometry.IsZariskiLocalAtSource
      (@AlgebraicGeometry.SmoothOfRelativeDimension r : MorphismProperty Scheme.{u}) := by
  have := respectsIso_smoothOfRelativeDimension r
  refine AlgebraicGeometry.IsZariskiLocalAtSource.mk' ?_ ?_
  · intro X Y f U hf
    have := hf
    have : AlgebraicGeometry.SmoothOfRelativeDimension 0 U.ι := inferInstance
    exact smoothOfRelativeDimension_zero_comp U.ι f r
  · intro X Y f ι U hU H
    exact smoothOfRelativeDimension_of_iSup_eq_top r f U hU H

theorem smoothOfRelativeDimension_opensCoprodMapOfRefinement {X' X : Scheme.{u}} (φ : X' ⟶ X) (r : ℕ)
    [AlgebraicGeometry.SmoothOfRelativeDimension r φ] {ι κ : Type u}
    (U : ι → X.Opens) (V : κ → X'.Opens) (β : κ → ι)
    (hβ : ∀ a, V a ≤ φ ⁻¹ᵁ (U (β a))) :
    AlgebraicGeometry.SmoothOfRelativeDimension r (opensCoprodMapOfRefinement φ U V β hβ) := by
  have := isZariskiLocalAtSource_smoothOfRelativeDimension r
  have h : ∀ a : κ, AlgebraicGeometry.SmoothOfRelativeDimension r
      (φ.resLE (U (β a)) (V a) (hβ a) ≫ Sigma.ι (fun i => (U i).toScheme) (β a)) := by
    intro a
    have : AlgebraicGeometry.SmoothOfRelativeDimension 0
        (Sigma.ι (fun i => (U i).toScheme) (β a)) := inferInstance
    exact smoothOfRelativeDimension_comp_zero _ _ r
  exact AlgebraicGeometry.IsZariskiLocalAtSource.sigmaDesc h

theorem exists_affine_etale_cover_of_smoothOfRelativeDimension {k : Type u} [Field k]
    {X X' : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (f' : X' ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.LocallyOfFiniteType f] [AlgebraicGeometry.QuasiCompact f]
    [AlgebraicGeometry.IsReduced X]
    [AlgebraicGeometry.LocallyOfFiniteType f'] [AlgebraicGeometry.QuasiCompact f']
    [AlgebraicGeometry.IsReduced X']
    (φ : X' ⟶ X) (r : ℕ) [AlgebraicGeometry.SmoothOfRelativeDimension r φ]
    (hφ : φ ≫ f = f') :
    ∃ (W : Scheme.{u}) (q : W ⟶ Spec (CommRingCat.of k)) (c : W ⟶ X)
      (W' : Scheme.{u}) (q' : W' ⟶ Spec (CommRingCat.of k)) (c' : W' ⟶ X') (ψ : W' ⟶ W),
      AlgebraicGeometry.IsAffine W ∧ AlgebraicGeometry.IsReduced W ∧
        AlgebraicGeometry.LocallyOfFiniteType q ∧ AlgebraicGeometry.QuasiCompact q ∧
        AlgebraicGeometry.Etale c ∧ AlgebraicGeometry.Surjective c ∧ c ≫ f = q ∧
      AlgebraicGeometry.IsAffine W' ∧ AlgebraicGeometry.IsReduced W' ∧
        AlgebraicGeometry.LocallyOfFiniteType q' ∧ AlgebraicGeometry.QuasiCompact q' ∧
        AlgebraicGeometry.Etale c' ∧ AlgebraicGeometry.Surjective c' ∧ c' ≫ f' = q' ∧
      AlgebraicGeometry.SmoothOfRelativeDimension r ψ ∧ ψ ≫ c = c' ≫ φ ∧ ψ ≫ q = q' := by
  have hcX : CompactSpace ↥X := QuasiCompact.compactSpace_of_compactSpace f
  have hcX' : CompactSpace ↥X' := QuasiCompact.compactSpace_of_compactSpace f'
  obtain ⟨ι, hι, U, hUaff, hUtop⟩ := exists_finite_affine_cover X
  have : Finite ι := hι
  obtain ⟨κ, hκ, V, β, hVaff, hβ, hVtop⟩ := exists_finite_affine_cover_subordinate φ U hUtop
  have : Finite κ := hκ
  have hWaff : AlgebraicGeometry.IsAffine (sigmaOpens X U) := isAffine_sigmaOpens X U hUaff
  have hW'aff : AlgebraicGeometry.IsAffine (sigmaOpens X' V) := isAffine_sigmaOpens X' V hVaff
  have hcW : CompactSpace ↥(sigmaOpens X U) := inferInstance
  have hcW' : CompactSpace ↥(sigmaOpens X' V) := inferInstance
  exact ⟨sigmaOpens X U, sigmaOpensDesc X U ≫ f, sigmaOpensDesc X U,
    sigmaOpens X' V, sigmaOpensDesc X' V ≫ f', sigmaOpensDesc X' V,
    opensCoprodMapOfRefinement φ U V β hβ,
    hWaff, inferInstance, inferInstance,
    quasiCompact_of_compactSpace_of_subsingleton (sigmaOpensDesc X U ≫ f), inferInstance,
    surjective_sigmaOpensDesc X U hUtop, rfl,
    hW'aff, inferInstance, inferInstance,
    quasiCompact_of_compactSpace_of_subsingleton (sigmaOpensDesc X' V ≫ f'), inferInstance,
    surjective_sigmaOpensDesc X' V hVtop, rfl,
    smoothOfRelativeDimension_opensCoprodMapOfRefinement φ r U V β hβ,
    opensCoprodMapOfRefinement_comp_sigmaOpensDesc φ U V β hβ,
    (by rw [← Category.assoc, opensCoprodMapOfRefinement_comp_sigmaOpensDesc, Category.assoc, hφ])⟩

theorem isCompatibleWithSmoothMorphisms_of_isInducedByAffineRule (B : AffineResolutionRule.{u})
    (hB : IsCompatibleWithSmoothOfRelativeDimension B) (R : ResolutionRule.{u})
    (hR : ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
      (p : Y ⟶ Spec (CommRingCat.of k))
      [AlgebraicGeometry.LocallyOfFiniteType p] [AlgebraicGeometry.QuasiCompact p]
      [AlgebraicGeometry.IsReduced Y], IsInducedByAffineRule B k Y p (R k Y p)) :
    IsCompatibleWithSmoothMorphisms R := by
  intro k _ _ X X' f f' _ _ _ _ _ _ φ r _ hφ
  obtain ⟨W, q, c, W', q', c', ψ, hWaff, hWred, hqlft, hqqc, hcet, hcsurj, hcq,
    hW'aff, hW'red, hq'lft, hq'qc, hc'et, hc'surj, hc'q', hψsm, hψc, hψq⟩ :=
    exists_affine_etale_cover_of_smoothOfRelativeDimension f f' φ r hφ
  have := hWaff
  have := hWred
  have := hqlft
  have := hqqc
  have := hcet
  have := hcsurj
  have := hW'aff
  have := hW'red
  have := hq'lft
  have := hq'qc
  have := hc'et
  have := hc'surj
  have := hψsm
  have hsmφ : AlgebraicGeometry.Smooth φ :=
    AlgebraicGeometry.SmoothOfRelativeDimension.smooth r φ
  have hsmψ : AlgebraicGeometry.Smooth ψ :=
    AlgebraicGeometry.SmoothOfRelativeDimension.smooth r ψ
  have hflatφ : AlgebraicGeometry.Flat φ := inferInstance
  have hflatψ : AlgebraicGeometry.Flat ψ := inferInstance
  have hflatc' : AlgebraicGeometry.Flat c' := inferInstance
  have hcs : ∀ y : ↥X, ∃ w, c w = y := fun y => hcsurj.surj y
  have hc's : ∀ y : ↥X', ∃ w, c' w = y := fun y => hc'surj.surj y
  have hA : IsStrictPullbackBlowupSeq c (B k W q) (R k X f) := hR k X f W q c hcq hcs
  have hA' : IsStrictPullbackBlowupSeq c' (B k W' q') (R k X' f') := hR k X' f' W' q' c' hc'q' hc's
  have hC : IsPullbackBlowupSequence ψ (B k W' q') (B k W q) := hB k W W' q q' ψ r hψq
  have h1 : IsStrictPullbackBlowupSeq φ ((R k X f).baseChange φ) (R k X f) :=
    isStrictPullbackSequenceOfBlowups_baseChange (R k X f) φ
  have h2 : IsStrictPullbackBlowupSeq c' (((R k X f).baseChange φ).baseChange c')
      ((R k X f).baseChange φ) :=
    isStrictPullbackSequenceOfBlowups_baseChange ((R k X f).baseChange φ) c'
  have h3 : IsStrictPullbackBlowupSeq (c' ≫ φ) (((R k X f).baseChange φ).baseChange c')
      (R k X f) := h2.comp h1
  have h4 : IsStrictPullbackBlowupSeq ψ ((B k W q).baseChange ψ) (B k W q) :=
    isStrictPullbackSequenceOfBlowups_baseChange (B k W q) ψ
  have h5 : IsStrictPullbackBlowupSeq (c' ≫ φ) ((B k W q).baseChange ψ) (R k X f) := by
    have h5' : IsStrictPullbackBlowupSeq (ψ ≫ c) ((B k W q).baseChange ψ) (R k X f) := h4.comp hA
    rwa [hψc] at h5'
  have h6 := h3.isomorphic h5
  have h7 := h6.withoutIsoBlowups
  have h8 : IsPullbackBlowupSequence ψ ((B k W q).baseChange ψ).withoutIsoBlowups (B k W q) := h4.isPullbackSequenceOfBlowups_withoutIsoBlowups
  have h9 := hC.isomorphic h8
  have h10 := h9.trans h7.symm
  have h11 := h2.withoutIsoBlowups
  have h12 := hA'.isomorphic_of_isomorphic h11 h10
  have h13 : IsPullbackBlowupSequence φ ((R k X f).baseChange φ).withoutIsoBlowups (R k X f) :=
    h1.isPullbackSequenceOfBlowups_withoutIsoBlowups
  exact h13.of_isomorphic h12.symm

private theorem isStrongResolution_of_isInducedByAffineRule_of_isAffine (B : AffineResolutionRule.{u})
    (hres : ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
      (p : Y ⟶ Spec (CommRingCat.of k))
      [AlgebraicGeometry.IsAffine Y] [AlgebraicGeometry.IsReduced Y]
      [AlgebraicGeometry.LocallyOfFiniteType p] [AlgebraicGeometry.QuasiCompact p],
      IsStrongResolution k Y p (B k Y p))
    (hetale : IsCompatibleWithEtaleCovers B)
    (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u}) (p : Y ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.IsAffine Y] [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.LocallyOfFiniteType p] [AlgebraicGeometry.QuasiCompact p]
    (s : SequenceOfBlowups Y) (hc : IsInducedByAffineRule B k Y p s) :
    IsStrongResolution k Y p s := by
  obtain ⟨W, q, g, hWaff, hWred, hqlft, hqqc, hget, hgsurj, hgq⟩ :=
    exists_affine_etale_cover_of_isReduced Y p
  have := hWaff
  have := hWred
  have := hqlft
  have := hqqc
  have := hget
  have := hgsurj
  have : AlgebraicGeometry.Flat g := inferInstance
  have hsurj : ∀ y : ↥Y, ∃ w, g w = y := fun y => hgsurj.surj y
  have h1 : IsStrictPullbackBlowupSeq g (B k W q) s := hc W q g hgq hsurj
  have h2 : IsStrictPullbackBlowupSeq g (B k W q) (B k Y p) := hetale k Y W p q g hgq hsurj
  exact IsStrongResolution.of_isomorphic k Y p (h2.isomorphic_of_isomorphic h1 (SequenceOfBlowups.isomorphic_refl _)) (hres k Y p)

private theorem isStrongResolution_of_isInducedByAffineRule (B : AffineResolutionRule.{u})
    (hres : ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
      (p : Y ⟶ Spec (CommRingCat.of k))
      [AlgebraicGeometry.IsAffine Y] [AlgebraicGeometry.IsReduced Y]
      [AlgebraicGeometry.LocallyOfFiniteType p] [AlgebraicGeometry.QuasiCompact p],
      IsStrongResolution k Y p (B k Y p))
    (hetale : IsCompatibleWithEtaleCovers B) (R : ResolutionRule.{u})
    (hcomes : ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
      (p : Y ⟶ Spec (CommRingCat.of k))
      [AlgebraicGeometry.LocallyOfFiniteType p] [AlgebraicGeometry.QuasiCompact p]
      [AlgebraicGeometry.IsReduced Y], IsInducedByAffineRule B k Y p (R k Y p))
    (hsmF : IsCompatibleWithSmoothMorphisms R)
    (k : Type u) [Field k] [CharZero k] (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.LocallyOfFiniteType f] [AlgebraicGeometry.QuasiCompact f]
    [AlgebraicGeometry.IsReduced X] :
    IsStrongResolution k X f (R k X f) := by
  have hOI : ∀ i : X.affineCover.I₀,
      AlgebraicGeometry.IsOpenImmersion (X.affineCover.f i) := fun _ => inferInstance
  have hA : ∀ i : X.affineCover.I₀,
      AlgebraicGeometry.IsAffine (X.affineCover.X i) := fun _ => inferInstance
  have hRed : ∀ i : X.affineCover.I₀,
      AlgebraicGeometry.IsReduced (X.affineCover.X i) := by
    intro i
    have := hOI i
    exact inferInstance
  have hLFT : ∀ i : X.affineCover.I₀,
      AlgebraicGeometry.LocallyOfFiniteType (X.affineCover.f i ≫ f) := by
    intro i
    have := hOI i
    exact inferInstance
  have hqc : ∀ i : X.affineCover.I₀,
      AlgebraicGeometry.QuasiCompact (X.affineCover.f i ≫ f) := by
    intro i
    have := hA i
    have : CompactSpace ↥(X.affineCover.X i) := inferInstance
    exact quasiCompact_of_compactSpace_of_subsingleton (X.affineCover.f i ≫ f)
  have hCharts : ∀ i : X.affineCover.I₀,
      AlgebraicGeometry.SmoothOfRelativeDimension 0 (X.affineCover.f i) := by
    intro i
    have := hOI i
    exact inferInstance
  have d : LocalResolutionData k f (R k X f) := by
    refine
      { cover := X.affineCover
        seq := fun i =>
          haveI := hLFT i
          haveI := hqc i
          haveI := hRed i
          R k (X.affineCover.X i) (X.affineCover.f i ≫ f)
        isPullback := ?_
        finiteType := hLFT
        isResolution := ?_ }
    · intro i
      have := hLFT i
      have := hqc i
      have := hRed i
      have := hCharts i
      exact hsmF k X (X.affineCover.X i) f (X.affineCover.f i ≫ f)
        (X.affineCover.f i) 0 rfl
    · intro i
      have := hA i
      have := hLFT i
      have := hqc i
      have := hRed i
      exact isStrongResolution_of_isInducedByAffineRule_of_isAffine B hres hetale k (X.affineCover.X i)
        (X.affineCover.f i ≫ f)
        (R k (X.affineCover.X i) (X.affineCover.f i ≫ f))
        (hcomes k (X.affineCover.X i) (X.affineCover.f i ≫ f))
  refine ⟨d.smooth_lastStructMap_comp, d.isProper_lastStructMap, d.isIso_lastStructMap_restrict_smoothLocus, ?_,
    d.centersLieOver_smoothLocusComplement, d.isStrictNormalCrossingsDivisor_reducedInverseImage⟩
  exact d.dense_preimage_smoothLocus

theorem strongResolutionOfSingularitiesCharZero_of_affineResolutionRule (B : AffineResolutionRule.{u})
    (hres : ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
      (p : Y ⟶ Spec (CommRingCat.of k))
      [AlgebraicGeometry.IsAffine Y] [AlgebraicGeometry.IsReduced Y]
      [AlgebraicGeometry.LocallyOfFiniteType p] [AlgebraicGeometry.QuasiCompact p],
      IsStrongResolution k Y p (B k Y p))
    (hetale : IsCompatibleWithEtaleCovers B) (hopen : IsCompatibleWithOpenImmersions B)
    (hfield : IsCompatibleWithFieldBaseChange B) (hsmooth : IsCompatibleWithSmoothOfRelativeDimension B) :
    StrongResolutionOfSingularitiesCharZero.{u} := by
  have hcen : ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
      (p : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType p]
      [AlgebraicGeometry.QuasiCompact p] [AlgebraicGeometry.IsReduced Y]
      [AlgebraicGeometry.IsAffine Y] (i : ℕ),
      i < (B k Y p).length → (B k Y p).center i ≠ ⊤ := by
    intro k _ _ Y p _ _ _ _ i hi
    exact AffineResolutionRule.center_ne_top B hopen k Y p i hi
  have H := existsGluedBlowupSequence_of_center_ne_top B hcen hetale
  obtain ⟨R, hcomes⟩ : ∃ R : ResolutionRule.{u},
      ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
        (p : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType p]
        [AlgebraicGeometry.QuasiCompact p] [AlgebraicGeometry.IsReduced Y],
        IsInducedByAffineRule B k Y p (R k Y p) :=
    ⟨fun k _ _ Y p _ _ _ => (H k Y p).choose,
      fun k _ _ Y p _ _ _ => (H k Y p).choose_spec.2⟩
  have hsmF : IsCompatibleWithSmoothMorphisms R :=
    isCompatibleWithSmoothMorphisms_of_isInducedByAffineRule B hsmooth R hcomes
  refine ⟨R, ?_, hsmF, inducedRuleCompatibleWithFieldExtension B hopen hfield R hcomes⟩
  refine (isStrongResolutionRule_iff R).mpr ?_
  intro k _ _ X f _ _ _
  exact isStrongResolution_of_isInducedByAffineRule B hres hetale R hcomes hsmF k X f

theorem strongResolutionOfSingularitiesCharZero_of_principalizationAlgorithm (A : PrincipalizationAlgorithm.{u})
    (hemb : AffineEmbedsIntoAffineSpace.{u}) (hsncE : NilIsStrictNormalCrossingsOnAffineSpace.{u})
    (hsm : AffineSpaceIsSmooth.{u}) (hAlg : IsFunctorialPrincipalization A) (hw : TransitionsAreBlowupsForEmbeddings A)
    (hex : EmbeddedPrincipalizationYieldsBlowups A hemb hsncE hsm) (hcmp : ClosedEmbeddingsRelatedByAutomorphism.{u})
    (haff : ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
      (p : Y ⟶ Spec (CommRingCat.of k))
      [AlgebraicGeometry.IsAffine Y] [AlgebraicGeometry.IsReduced Y]
      [AlgebraicGeometry.LocallyOfFiniteType p] [AlgebraicGeometry.QuasiCompact p],
      IsStrongResolution k Y p (affineResolutionRuleOfPrincipalization A hemb hsncE hsm hex k Y p)) :
    StrongResolutionOfSingularitiesCharZero.{u} :=
  strongResolutionOfSingularitiesCharZero_of_affineResolutionRule
    (affineResolutionRuleOfPrincipalization A hemb hsncE hsm hex) haff
    (isCompatibleWithEtaleCovers_affineResolutionRuleOfPrincipalization A hAlg hw hemb hsncE hsm hex hcmp)
    (isCompatibleWithOpenImmersions_affineResolutionRuleOfPrincipalization A hAlg hw hemb hsncE hsm hex hcmp)
    (isCompatibleWithFieldBaseChange_affineResolutionRuleOfPrincipalization A hAlg hw hemb hsncE hsm hex hcmp)
    (isCompatibleWithSmoothOfRelativeDimension_affineResolutionRule A hAlg hw hemb hsncE hsm hex hcmp)

end FunctorialResolution.EmbeddedResolution

end
