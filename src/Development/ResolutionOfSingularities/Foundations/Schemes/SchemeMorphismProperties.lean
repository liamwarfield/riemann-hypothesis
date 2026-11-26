module

public import Mathlib

@[expose] public section

section -- merged from Development.ResolutionOfSingularities.Foundations.Schemes.SchemeMorphismProperties
universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace FunctorialResolution.Blowup

theorem noetherianSpace_toScheme (X : Scheme.{u}) [NoetherianSpace ↥X] (U : X.Opens) :
    NoetherianSpace ↥(U.toScheme) := by
  have h : Topology.IsInducing (fun x : { y : ↥X // y ∈ U } => (x : ↥X)) := ⟨rfl⟩
  exact h.noetherianSpace

instance instNoetherianSpaceToScheme (X : Scheme.{u}) [NoetherianSpace ↥X] (U : X.Opens) :
    NoetherianSpace ↥(U.toScheme) :=
  noetherianSpace_toScheme X U

private theorem isAffineHom_specMap {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    AlgebraicGeometry.IsAffineHom (Spec.map φ) :=
  inferInstance

private theorem isAffineHom_pullback_fst {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [AlgebraicGeometry.IsAffineHom g] :
    AlgebraicGeometry.IsAffineHom (pullback.fst f g) :=
  MorphismProperty.of_isPullback (P := @AlgebraicGeometry.IsAffineHom)
    (IsPullback.of_hasPullback f g).flip ‹AlgebraicGeometry.IsAffineHom g›

theorem isAffineHom_pullback_fst_specMap_of_field {k K : Type u} [Field k] [Field K] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (φ : CommRingCat.of k ⟶ CommRingCat.of K) :
    AlgebraicGeometry.IsAffineHom (pullback.fst p (Spec.map φ)) :=
  @isAffineHom_pullback_fst X _ _ p (Spec.map φ) (isAffineHom_specMap φ)

instance instIsAffineHomSpecMapPullbackFst {k K : Type u} [Field k] [Field K] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (φ : CommRingCat.of k ⟶ CommRingCat.of K) :
    AlgebraicGeometry.IsAffineHom (pullback.fst p (Spec.map φ)) :=
  isAffineHom_pullback_fst_specMap_of_field p φ

private theorem le_comap_map_of_isClosedImmersion {S X : Scheme.{u}} (ι : S ⟶ X)
    [IsClosedImmersion ι] (Z : S.IdealSheafData) : Z ≤ (Z.map ι).comap ι := by
  have hmapdef : Z.map ι = Scheme.Hom.ker (Z.subschemeι ≫ ι) := rfl
  have hcomapdef : (Z.map ι).comap ι
      = Scheme.Hom.ker (pullback.fst ι (Z.map ι).subschemeι) := rfl
  have hle : Scheme.Hom.ker (Z.subschemeι ≫ ι)
      ≤ Scheme.Hom.ker (Z.map ι).subschemeι := by
    rw [Scheme.IdealSheafData.ker_subschemeι, ← hmapdef]
  have hu : IsClosedImmersion.lift (Z.subschemeι ≫ ι) (Z.map ι).subschemeι hle
      ≫ (Z.subschemeι ≫ ι) = (Z.map ι).subschemeι :=
    IsClosedImmersion.lift_fac _ _ hle
  set u := IsClosedImmersion.lift (Z.subschemeι ≫ ι) (Z.map ι).subschemeι hle with hudef
  have hk : (pullback.snd ι (Z.map ι).subschemeι ≫ u) ≫ Z.subschemeι
      = pullback.fst ι (Z.map ι).subschemeι := by
    have h2 : ((pullback.snd ι (Z.map ι).subschemeι ≫ u) ≫ Z.subschemeι) ≫ ι
        = pullback.fst ι (Z.map ι).subschemeι ≫ ι := by
      rw [Category.assoc, Category.assoc, hu]
      exact pullback.condition.symm
    exact (cancel_mono ι).mp h2
  rw [hcomapdef, ← hk, Scheme.Hom.ker_comp]
  calc Z = (⊥ : Z.subscheme.IdealSheafData).map Z.subschemeι := by
        rw [Scheme.IdealSheafData.map_bot, Scheme.IdealSheafData.ker_subschemeι]
    _ ≤ _ := Scheme.IdealSheafData.map_mono Z.subschemeι bot_le

theorem comap_map_of_isClosedImmersion {S X : Scheme.{u}} (ι : S ⟶ X)
    [IsClosedImmersion ι] (Z : S.IdealSheafData) :
    (Z.map ι).comap ι = Z :=
  le_antisymm (Scheme.IdealSheafData.comap_map_le Z ι) (le_comap_map_of_isClosedImmersion ι Z)

theorem isOpen_connectedComponent_of_noetherianSpace (T : Type v) [TopologicalSpace T]
    [TopologicalSpace.NoetherianSpace T] (x : T) : IsOpen (connectedComponent x) := by
  classical
  have hfin : {Z : Set T | Z ∈ irreducibleComponents T ∧ ¬ Z ⊆ connectedComponent x}.Finite := by
    refine Set.Finite.subset
      (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents) ?_
    rintro Z ⟨hZ, -⟩
    exact hZ
  have heq : (connectedComponent x)ᶜ
      = ⋃ Z ∈ {Z : Set T | Z ∈ irreducibleComponents T ∧ ¬ Z ⊆ connectedComponent x}, Z := by
    apply Set.Subset.antisymm
    · intro y hy
      exact Set.mem_biUnion
        (⟨irreducibleComponent_mem_irreducibleComponents y,
          fun h => hy (h mem_irreducibleComponent)⟩ :
          irreducibleComponent y ∈
            {Z : Set T | Z ∈ irreducibleComponents T ∧ ¬ Z ⊆ connectedComponent x})
        mem_irreducibleComponent
    · intro z hz
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop] at hz
      obtain ⟨Z, ⟨hZ, hZ'⟩, hzZ⟩ := hz
      intro hzc
      have h1 : Z ⊆ connectedComponent z :=
        hZ.1.2.isPreconnected.subset_connectedComponent hzZ
      rw [← connectedComponent_eq hzc] at h1
      exact hZ' h1
  rw [← isClosed_compl_iff, heq]
  exact hfin.isClosed_biUnion (fun Z hZ => isClosed_of_mem_irreducibleComponents _ hZ.1)

end FunctorialResolution.Blowup

namespace TopologicalSpace.NoetherianSpace

theorem finite_range_connectedComponent (Y : Type*) [TopologicalSpace Y] [NoetherianSpace Y] :
    (Set.range fun x : Y => connectedComponent x).Finite := by
  classical
  have hfin : (irreducibleComponents Y).Finite :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  refine Set.Finite.subset (hfin.image fun Z => ⋃ z ∈ Z, connectedComponent z) ?_
  rintro _ ⟨x, rfl⟩
  refine ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x, ?_⟩
  have hsub : irreducibleComponent x ⊆ connectedComponent x :=
    (irreducibleComponent_mem_irreducibleComponents x).1.2.isPreconnected.subset_connectedComponent
      mem_irreducibleComponent
  show (⋃ z ∈ irreducibleComponent x, connectedComponent z) = connectedComponent x
  apply Set.Subset.antisymm
  · intro y hy
    obtain ⟨z, hz, hyz⟩ := Set.mem_iUnion₂.mp hy
    rwa [← connectedComponent_eq (hsub hz)] at hyz
  · intro y hy
    exact Set.mem_biUnion mem_irreducibleComponent hy

theorem isClosed_setOf_connectedComponent_subset (Y : Type*) [TopologicalSpace Y]
    [NoetherianSpace Y] (A : Set Y) : IsClosed {x : Y | connectedComponent x ⊆ A} := by
  classical
  have hfin :
      {C : Set Y | C ∈ Set.range (fun x : Y => connectedComponent x) ∧ C ⊆ A}.Finite := by
    refine (finite_range_connectedComponent Y).subset ?_
    rintro C ⟨hC, -⟩
    exact hC
  have heq : {x : Y | connectedComponent x ⊆ A}
      = ⋃ C ∈ {C : Set Y | C ∈ Set.range (fun x : Y => connectedComponent x) ∧ C ⊆ A}, C := by
    apply Set.Subset.antisymm
    · intro x hx
      have hmem : connectedComponent x ∈
          {C : Set Y | C ∈ Set.range (fun x : Y => connectedComponent x) ∧ C ⊆ A} :=
        ⟨⟨x, rfl⟩, hx⟩
      exact Set.mem_biUnion hmem mem_connectedComponent
    · intro x hx
      obtain ⟨C, hC, hxC⟩ := Set.mem_iUnion₂.mp hx
      obtain ⟨⟨y, hy⟩, hCA⟩ := hC
      have hy' : connectedComponent y = C := hy
      rw [← hy'] at hxC hCA
      show connectedComponent x ⊆ A
      rw [← connectedComponent_eq hxC]
      exact hCA
  rw [heq]
  refine hfin.isClosed_biUnion ?_
  rintro C ⟨⟨x, hx⟩, -⟩
  have hC : C = connectedComponent x := hx.symm
  rw [hC]
  exact isClosed_connectedComponent

end TopologicalSpace.NoetherianSpace

namespace AlgebraicGeometry

namespace Scheme

theorem presheaf_map_eq_of_parallel (X₁ : Scheme.{u}) {A B : (X₁.Opens)ᵒᵖ} (g₁ g₂ : A ⟶ B) :
    X₁.presheaf.map g₁ = X₁.presheaf.map g₂ :=
  congrArg X₁.presheaf.map (Quiver.Hom.unop_inj (Subsingleton.elim _ _))

namespace Hom

theorem appLE_congr_hom {A B : Scheme.{u}} {f g : A ⟶ B} (hfg : f = g) (O : B.Opens)
    (S : A.Opens) (h1 : S ≤ f ⁻¹ᵁ O) (h2 : S ≤ g ⁻¹ᵁ O) :
    Scheme.Hom.appLE f O S h1 = Scheme.Hom.appLE g O S h2 := by
  subst hfg
  rfl

theorem range_comp_base {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    Set.range (f ≫ g).base = g.base '' Set.range f.base := by
  have hcomp : ∀ x : A, (f ≫ g).base x = g.base (f.base x) := fun _ => rfl
  apply Set.Subset.antisymm
  · rintro z ⟨x, rfl⟩
    exact ⟨f.base x, ⟨x, rfl⟩, (hcomp x).symm⟩
  · rintro z ⟨y, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, hcomp x⟩

end Hom

end Scheme

theorem quasiCompact_of_compactSpace_of_subsingleton {W S : Scheme.{u}} (f : W ⟶ S)
    [CompactSpace ↥W] [Subsingleton ↥S] : QuasiCompact f := by
  constructor
  intro U _ _
  rcases Set.eq_empty_or_nonempty (f.base ⁻¹' U) with h | ⟨w, hw⟩
  · rw [h]
    exact isCompact_empty
  · have h2 : f.base ⁻¹' U = Set.univ := by
      refine Set.eq_univ_of_forall fun w' => ?_
      have hww : f.base w' = f.base w := Subsingleton.elim _ _
      show f.base w' ∈ U
      rw [hww]
      exact hw
    rw [h2]
    exact isCompact_univ

end AlgebraicGeometry
end

section -- merged from Development.ResolutionOfSingularities.Foundations.Schemes.AffineOpens
universe u

namespace AlgebraicGeometry.Scheme

theorem exists_isAffineOpen_mem {X : Scheme.{u}} (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ IsAffineOpen U := by
  obtain ⟨U, hU, hxU, -⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens X)
      (show x ∈ (⊤ : X.Opens) from trivial)
  exact ⟨U, hxU, hU⟩

theorem exists_affineOpens_mem {X : Scheme.{u}} (x : X) : ∃ U : X.affineOpens, x ∈ U.1 := by
  have hx : x ∈ (⨆ U : X.affineOpens, (U : X.Opens)) := by
    rw [AlgebraicGeometry.iSup_affineOpens_eq_top X]
    trivial
  obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact ⟨U, hU⟩

theorem exists_affineOpens_mem_le {X : Scheme.{u}} {x : X} {U : X.Opens} (hx : x ∈ U) :
    ∃ V : X.affineOpens, x ∈ V.1 ∧ V.1 ≤ U := by
  obtain ⟨V, hV, hxV, hsub⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx U.isOpen
  obtain ⟨W, hW, rfl⟩ := hV
  exact ⟨⟨W, hW⟩, hxV, hsub⟩

end AlgebraicGeometry.Scheme
end

section -- merged from Development.ResolutionOfSingularities.Foundations.Schemes.SchemeCoproduct
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FunctorialResolution.Blowup

theorem range_coprod_inr_eq_compl (X Y : Scheme.{u}) :
    Set.range ⇑(coprod.inr : Y ⟶ X ⨿ Y).base
      = (Set.range ⇑(coprod.inl : X ⟶ X ⨿ Y).base)ᶜ := by
  have h : IsCompl (Set.range ⇑(coprod.inl : X ⟶ X ⨿ Y).base)
      (Set.range ⇑(coprod.inr : Y ⟶ X ⨿ Y).base) := isCompl_range_inl_inr ..
  exact h.compl_eq.symm

theorem isClosed_range_coprod_inl (X Y : Scheme.{u}) :
    IsClosed (Set.range ⇑(coprod.inl : X ⟶ X ⨿ Y).base) := by
  have h : IsCompl (Set.range ⇑(coprod.inl : X ⟶ X ⨿ Y).base)
      (Set.range ⇑(coprod.inr : Y ⟶ X ⨿ Y).base) := isCompl_range_inl_inr X Y
  have hopen : IsOpen (Set.range ⇑(coprod.inr : Y ⟶ X ⨿ Y).base) :=
    (coprod.inr : Y ⟶ X ⨿ Y).isOpenEmbedding.isOpen_range
  rw [← isOpen_compl_iff, h.compl_eq]
  exact hopen

instance instIsClosedImmersionCoprodInl (X Y : Scheme.{u}) :
    IsClosedImmersion (coprod.inl : X ⟶ X ⨿ Y) := by
  constructor
  exact ⟨(coprod.inl : X ⟶ X ⨿ Y).isOpenEmbedding.toIsEmbedding,
    isClosed_range_coprod_inl X Y⟩

private theorem isClosedEmbedding_coprod_inl_base (X Y : Scheme.{u}) :
    Topology.IsClosedEmbedding ⇑(coprod.inl : X ⟶ X ⨿ Y).base :=
  ⟨(coprod.inl : X ⟶ X ⨿ Y).isOpenEmbedding.toIsEmbedding, isClosed_range_coprod_inl X Y⟩

instance instQuasiCompactCoprodInl (X Y : Scheme.{u}) :
    QuasiCompact (coprod.inl : X ⟶ X ⨿ Y) := by
  constructor
  intro U _ hU
  exact (isClosedEmbedding_coprod_inl_base X Y).isCompact_preimage hU

section

variable {ι : Type u} (X : ι → Scheme.{u}) [HasCoproduct X]

theorem sigmaι_base_ne {i j : ι} (hij : i ≠ j) (x : ↥(X i)) (y : ↥(X j)) :
    (Sigma.ι X i).base x ≠ (Sigma.ι X j).base y := by
  intro h
  exact hij (congrArg Sigma.fst ((sigmaι_eq_iff X i j x y).mp h))

private noncomputable def iSupOpensRangeSigmaι {κ : Type u} (Y : κ → Scheme.{u}) [HasCoproduct Y] : (∐ Y).Opens :=
  ⟨⋃ i, Set.range ⇑(Sigma.ι Y i).base,
    isOpen_iUnion fun i => (Sigma.ι Y i).isOpenEmbedding.isOpen_range⟩

private theorem range_sigmaι_subset_iUnion {κ : Type u} (Y : κ → Scheme.{u}) [HasCoproduct Y]
    (i : κ) : Set.range ⇑(Sigma.ι Y i).base ⊆ Set.range ⇑(iSupOpensRangeSigmaι Y).ι.base := by
  rw [Scheme.Opens.range_ι]
  intro z hz
  show z ∈ ⋃ i, Set.range ⇑(Sigma.ι Y i).base
  exact Set.mem_iUnion.mpr ⟨i, hz⟩

private theorem surjective_base_of_comp_eq_id {A B : Scheme.{u}} (g : A ⟶ B) (h : B ⟶ A)
    (hgh : g ≫ h = 𝟙 A) : Function.Surjective ⇑h.base := by
  intro x
  refine ⟨g.base x, ?_⟩
  have h1 := congrArg (fun m : A ⟶ A => m.base x) hgh
  simpa using h1

private theorem exists_sigmaι_base_eq {κ : Type u} (Y : κ → Scheme.{u}) [HasCoproduct Y]
    (x : ↥(∐ Y)) : ∃ (i : κ) (y : ↥(Y i)), (Sigma.ι Y i).base y = x := by
  have hid : (Sigma.desc fun i =>
      IsOpenImmersion.lift (iSupOpensRangeSigmaι Y).ι (Sigma.ι Y i) (range_sigmaι_subset_iUnion Y i)) ≫
        (iSupOpensRangeSigmaι Y).ι = 𝟙 (∐ Y) := by
    apply Sigma.hom_ext
    intro i
    have hfac := IsOpenImmersion.lift_fac (iSupOpensRangeSigmaι Y).ι (Sigma.ι Y i)
      (range_sigmaι_subset_iUnion Y i)
    simp [hfac]
  obtain ⟨w, hw⟩ := surjective_base_of_comp_eq_id _ _ hid x
  have hmem : x ∈ Set.range ⇑(iSupOpensRangeSigmaι Y).ι.base := ⟨w, hw⟩
  rw [Scheme.Opens.range_ι] at hmem
  have hmem2 : x ∈ ⋃ i, Set.range ⇑(Sigma.ι Y i).base := hmem
  obtain ⟨i, y, hy⟩ := Set.mem_iUnion.mp hmem2
  exact ⟨i, y, hy⟩

theorem isClosed_range_sigmaι (j : ι) : IsClosed (Set.range ⇑(Sigma.ι X j).base) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  rw [Set.mem_compl_iff] at hx
  obtain ⟨i, y, rfl⟩ := exists_sigmaι_base_eq X x
  have hij : i ≠ j := by
    intro h
    subst h
    exact hx ⟨y, rfl⟩
  refine ⟨Set.range ⇑(Sigma.ι X i).base, ?_,
    (Sigma.ι X i).isOpenEmbedding.isOpen_range, Set.mem_range_self y⟩
  intro u hu
  obtain ⟨z, rfl⟩ := hu
  rw [Set.mem_compl_iff]
  intro hmem
  obtain ⟨w, hw⟩ := hmem
  exact sigmaι_base_ne X hij z w hw.symm

private theorem isClosedEmbedding_sigmaι_base {κ : Type u} (Y : κ → Scheme.{u})
    [HasCoproduct Y] (j : κ) (hc : IsClosed (Set.range ⇑(Sigma.ι Y j).base)) :
    Topology.IsClosedEmbedding ⇑(Sigma.ι Y j).base :=
  ⟨(Sigma.ι Y j).isOpenEmbedding.toIsEmbedding, hc⟩

theorem quasiCompact_sigmaι (j : ι) : QuasiCompact (Sigma.ι X j) := by
  constructor
  intro U _ hU
  exact (isClosedEmbedding_sigmaι_base X j (isClosed_range_sigmaι X j)).isCompact_preimage hU

instance instQuasiCompactSigmaι (j : ι) : QuasiCompact (Sigma.ι X j) :=
  quasiCompact_sigmaι X j

end

end FunctorialResolution.Blowup
end
