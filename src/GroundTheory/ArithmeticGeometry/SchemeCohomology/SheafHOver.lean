module

public import GroundTheory.ArithmeticGeometry.SchemeCohomology.RegularLocalDomain

@[expose] public section

section -- merged from GroundTheory.ArithmeticGeometry.SchemeCohomology.OverShriek
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open CategoryTheory Limits Opposite DirectSum

universe v u

attribute [local instance] Classical.decEq

variable {C : Type u} [Category.{v} C] {U : C}

section Presheaf

variable (P : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{v})

abbrev shriekSummand (X : C) (s : X ⟶ U) : Type v := P.obj (op (Over.mk s))

noncomputable def shriekMap {X Y : C} (g : Y ⟶ X) :
    (⨁ s : X ⟶ U, shriekSummand P X s) →+ ⨁ t : Y ⟶ U, shriekSummand P Y t :=
  DirectSum.toAddMonoid fun s =>
    (DirectSum.of (shriekSummand P Y) (g ≫ s)).comp
      (P.map (Over.homMk g rfl : Over.mk (g ≫ s) ⟶ Over.mk s).op).hom

lemma shriekMap_of {X Y : C} (g : Y ⟶ X) (s : X ⟶ U) (x : shriekSummand P X s) :
    shriekMap P g (DirectSum.of _ s x) =
      DirectSum.of (shriekSummand P Y) (g ≫ s)
        (P.map (Over.homMk g rfl : Over.mk (g ≫ s) ⟶ Over.mk s).op x) :=
  DirectSum.toAddMonoid_of _ _ _

lemma shriek_of_eq_of {Y : C} {V : Over U} {t t' : Y ⟶ U} (h : t = t') (a : Over.mk t ⟶ V)
    (a' : Over.mk t' ⟶ V) (ha : a.left = a'.left) (x : P.obj (op V)) :
    DirectSum.of (shriekSummand P Y) t (P.map a.op x) =
      DirectSum.of (shriekSummand P Y) t' (P.map a'.op x) := by
  subst h
  rw [Over.OverMorphism.ext ha]

noncomputable def shriekPresheaf : Cᵒᵖ ⥤ AddCommGrpCat.{v} where
  obj X := AddCommGrpCat.of (⨁ s : X.unop ⟶ U, shriekSummand P X.unop s)
  map g := AddCommGrpCat.ofHom (shriekMap P g.unop)
  map_id X := by
    apply AddCommGrpCat.hom_ext
    apply DirectSum.addHom_ext
    intro s x
    simp only [AddCommGrpCat.hom_ofHom, unop_id, AddCommGrpCat.hom_id, AddMonoidHom.id_apply]
    rw [shriekMap_of]
    rw [shriek_of_eq_of P (Category.id_comp s) _ (𝟙 _) (by simp)]
    simp
  map_comp f g := by
    apply AddCommGrpCat.hom_ext
    apply DirectSum.addHom_ext
    intro s x
    simp only [AddCommGrpCat.hom_ofHom, unop_comp, AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp,
      Function.comp_apply]
    rw [shriekMap_of, shriekMap_of, shriekMap_of, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
      ← op_comp]
    exact shriek_of_eq_of P (by simp) _ _ (by simp) x


variable {P} in
noncomputable def shriekPresheafMap {P Q : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{v}} (φ : P ⟶ Q) :
    shriekPresheaf P ⟶ shriekPresheaf Q where
  app X := AddCommGrpCat.ofHom (DirectSum.toAddMonoid fun s =>
    (DirectSum.of (shriekSummand Q X.unop) s).comp (φ.app (op (Over.mk s))).hom)
  naturality X Y g := by
    apply AddCommGrpCat.hom_ext
    apply DirectSum.addHom_ext
    intro s x
    change (DirectSum.toAddMonoid fun s => (DirectSum.of (shriekSummand Q Y.unop) s).comp
        (φ.app (op (Over.mk s))).hom) (shriekMap P g.unop (DirectSum.of _ s x)) =
      shriekMap Q g.unop ((DirectSum.toAddMonoid fun s => (DirectSum.of (shriekSummand Q X.unop) s).comp
        (φ.app (op (Over.mk s))).hom) (DirectSum.of _ s x))
    rw [shriekMap_of, DirectSum.toAddMonoid_of, DirectSum.toAddMonoid_of,
      AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, shriekMap_of]
    congr 1
    exact NatTrans.naturality_apply φ _ x

lemma shriekPresheafMap_app_of {P Q : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{v}} (φ : P ⟶ Q) (X : Cᵒᵖ)
    (s : X.unop ⟶ U) (x : shriekSummand P X.unop s) :
    (shriekPresheafMap φ).app X (DirectSum.of (shriekSummand P X.unop) s x) =
      DirectSum.of (shriekSummand Q X.unop) s (φ.app (op (Over.mk s)) x) :=
  DirectSum.toAddMonoid_of
    (fun t => (DirectSum.of (shriekSummand Q X.unop) t).comp (φ.app (op (Over.mk t))).hom) s x

end Presheaf


variable (U) in
noncomputable def shriekFunctor (U : C) :
    ((Over U)ᵒᵖ ⥤ AddCommGrpCat.{v}) ⥤ (Cᵒᵖ ⥤ AddCommGrpCat.{v}) where
  obj P := shriekPresheaf P
  map φ := shriekPresheafMap φ
  map_id P := by
    ext X : 2
    apply AddCommGrpCat.hom_ext
    apply DirectSum.addHom_ext
    intro s x
    change DirectSum.toAddMonoid _ (DirectSum.of _ s x) = DirectSum.of _ s x
    rw [DirectSum.toAddMonoid_of]
    rfl
  map_comp {P₁ P₂ P₃} φ ψ := by
    ext X : 2
    apply AddCommGrpCat.hom_ext
    apply DirectSum.addHom_ext
    intro s x
    change (DirectSum.toAddMonoid fun s => (DirectSum.of (shriekSummand P₃ X.unop) s).comp
        ((ψ.app (op (Over.mk s))).hom.comp (φ.app (op (Over.mk s))).hom))
          (DirectSum.of (shriekSummand P₁ X.unop) s x) =
      (DirectSum.toAddMonoid fun s => (DirectSum.of (shriekSummand P₃ X.unop) s).comp
        (ψ.app (op (Over.mk s))).hom) ((DirectSum.toAddMonoid fun s =>
          (DirectSum.of (shriekSummand P₂ X.unop) s).comp (φ.app (op (Over.mk s))).hom)
            (DirectSum.of (shriekSummand P₁ X.unop) s x))
    simp only [DirectSum.toAddMonoid_of, AddMonoidHom.comp_apply]

section Adjunction

variable {P : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{v}} {Q : Cᵒᵖ ⥤ AddCommGrpCat.{v}}

noncomputable def shriekHomToRestrict (α : shriekPresheaf P ⟶ Q) :
    P ⟶ (Over.forget U).op ⋙ Q where
  app V := AddCommGrpCat.ofHom ((α.app (op V.unop.left)).hom.comp
    (DirectSum.of (shriekSummand P V.unop.left) V.unop.hom))
  naturality V W f := by
    ext x
    change (α.app (op W.unop.left)) (DirectSum.of (shriekSummand P W.unop.left) W.unop.hom
        (P.map f x)) =
      Q.map f.unop.left.op ((α.app (op V.unop.left)) (DirectSum.of (shriekSummand P V.unop.left)
        V.unop.hom x))
    refine (congrArg (α.app (op W.unop.left)) ?_).trans
      (NatTrans.naturality_apply α f.unop.left.op _)
    exact (shriek_of_eq_of P (Over.w f.unop).symm f.unop _ rfl x).trans
      (shriekMap_of P f.unop.left V.unop.hom x).symm

noncomputable abbrev shriekHomOfRestrictApp (β : P ⟶ (Over.forget U).op ⋙ Q) (X : Cᵒᵖ) :
    (⨁ s : X.unop ⟶ U, shriekSummand P X.unop s) →+ Q.obj X :=
  DirectSum.toAddMonoid fun s => (β.app (op (Over.mk s))).hom

lemma shriekHomOfRestrictApp_of (β : P ⟶ (Over.forget U).op ⋙ Q) (X : Cᵒᵖ) (s : X.unop ⟶ U)
    (x : shriekSummand P X.unop s) :
    shriekHomOfRestrictApp β X (DirectSum.of (shriekSummand P X.unop) s x) =
      β.app (op (Over.mk s)) x :=
  DirectSum.toAddMonoid_of _ _ _

noncomputable def shriekHomOfRestrict (β : P ⟶ (Over.forget U).op ⋙ Q) :
    shriekPresheaf P ⟶ Q where
  app X := AddCommGrpCat.ofHom (shriekHomOfRestrictApp β X)
  naturality X Y g := by
    apply AddCommGrpCat.hom_ext
    apply DirectSum.addHom_ext
    intro s x
    refine (congrArg ((shriekHomOfRestrictApp β Y)) (shriekMap_of P g.unop s x)).trans ?_
    refine (shriekHomOfRestrictApp_of β Y _ _).trans ?_
    refine Eq.trans ?_ (congrArg (Q.map g) (shriekHomOfRestrictApp_of β X s x).symm)
    exact NatTrans.naturality_apply β _ x


variable (U) in
noncomputable def shriekAdjunction (U : C) :
    shriekFunctor U ⊣ (Functor.whiskeringLeft _ _ AddCommGrpCat.{v}).obj (Over.forget U).op :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun P Q =>
        { toFun := shriekHomToRestrict
          invFun := shriekHomOfRestrict
          left_inv := fun α => by
            ext X : 2
            apply AddCommGrpCat.hom_ext
            apply DirectSum.addHom_ext
            intro s x
            exact (shriekHomOfRestrictApp_of (shriekHomToRestrict α) X s x).trans rfl
          right_inv := fun β => by
            ext V x
            exact shriekHomOfRestrictApp_of β (op V.unop.left) V.unop.hom x }
      homEquiv_naturality_left_symm := fun {P P' Q} f g => by
        ext X : 2
        apply AddCommGrpCat.hom_ext
        apply DirectSum.addHom_ext
        intro s x
        refine (shriekHomOfRestrictApp_of (f ≫ g) X s x).trans ?_
        refine Eq.trans ?_ (congrArg (shriekHomOfRestrictApp g X)
          (shriekPresheafMap_app_of f X s x).symm)
        exact (shriekHomOfRestrictApp_of g X s _).symm
      homEquiv_naturality_right := fun {P Q Q'} f g => rfl }

end Adjunction

instance : (shriekFunctor U).PreservesMonomorphisms where
  preserves {P Q} φ _ := by
    have hφ : ∀ V, Function.Injective (φ.app V) := fun V =>
      (AddCommGrpCat.mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app φ).1 inferInstance V)
    rw [NatTrans.mono_iff_mono_app]
    intro X
    rw [AddCommGrpCat.mono_iff_injective]
    have key : (DirectSum.toAddMonoid fun s => (DirectSum.of (shriekSummand Q X.unop) s).comp
        (φ.app (op (Over.mk s))).hom) =
        DFinsupp.mapRange.addMonoidHom (fun s => (φ.app (op (Over.mk s))).hom) := by
      apply DirectSum.addHom_ext
      intro s x
      rw [DirectSum.toAddMonoid_of, AddMonoidHom.comp_apply, DFinsupp.mapRange.addMonoidHom_apply]
      exact (DFinsupp.mapRange_single (f := fun s => ⇑(φ.app (op (Over.mk s))).hom)
        (hf := fun s => map_zero _)).symm
    change Function.Injective (DirectSum.toAddMonoid fun s =>
      (DirectSum.of (shriekSummand Q X.unop) s).comp (φ.app (op (Over.mk s))).hom)
    rw [key]
    intro a b hab
    exact (DFinsupp.mapRange_injective _ (fun s => map_zero _)).2 (fun s => hφ _) hab

section Sheaf

variable (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{v}]

noncomputable def sheafShriek (U : C) : Sheaf (J.over U) AddCommGrpCat.{v} ⥤ Sheaf J AddCommGrpCat.{v} :=
  sheafToPresheaf _ _ ⋙ shriekFunctor U ⋙ presheafToSheaf J _

noncomputable def sheafShriekAdjunction (U : C) :
    sheafShriek J U ⊣ J.overPullback AddCommGrpCat.{v} U :=
  ((shriekAdjunction U).comp (sheafificationAdjunction J AddCommGrpCat.{v})).restrictFullyFaithful
    (iC := sheafToPresheaf (J.over U) AddCommGrpCat.{v}) (iD := 𝟭 _)
    (fullyFaithfulSheafToPresheaf _ _) (Functor.FullyFaithful.id _)
    (Functor.rightUnitor _).symm
    (Functor.leftUnitor _ ≪≫ ((Over.forget U).sheafPushforwardContinuousCompSheafToPresheafIso
      AddCommGrpCat.{v} (J.over U) J).symm)

instance (U : C) : (sheafShriek J U).PreservesMonomorphisms := by
  unfold sheafShriek
  infer_instance

instance (U : C) : (J.overPullback AddCommGrpCat.{v} U).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (sheafShriekAdjunction J U)

end Sheaf

end GroundTheory.Arith.SchemeCoh
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open CategoryTheory Limits Opposite Abelian

universe w' v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{v}] (U : C)

section Exact

instance overPullback_additive : (J.overPullback AddCommGrpCat.{v} U).Additive where
  map_add := rfl

attribute [local instance] Classical.decEq in
instance overPullback_isRightAdjoint : (J.overPullback AddCommGrpCat.{v} U).IsRightAdjoint :=
  ⟨_, ⟨((Adjunction.mkOfHomEquiv
    { homEquiv := fun P Q =>
        { toFun := shriekHomToRestrict
          invFun := shriekHomOfRestrict
          left_inv := fun α => by
            ext X : 2
            apply AddCommGrpCat.hom_ext
            apply DirectSum.addHom_ext
            intro s x
            exact (shriekHomOfRestrictApp_of (shriekHomToRestrict α) X s x).trans rfl
          right_inv := fun β => by
            ext V x
            exact shriekHomOfRestrictApp_of β (op V.unop.left) V.unop.hom x }
      homEquiv_naturality_left_symm := fun {P P' Q} f g => by
        ext X : 2
        apply AddCommGrpCat.hom_ext
        apply DirectSum.addHom_ext
        intro s x
        refine (shriekHomOfRestrictApp_of (f ≫ g) X s x).trans ?_
        refine Eq.trans ?_ (congrArg (shriekHomOfRestrictApp g X)
          (shriekPresheafMap_app_of f X s x).symm)
        exact (shriekHomOfRestrictApp_of g X s _).symm
      homEquiv_naturality_right := fun {P Q Q'} f g => rfl } :
        shriekFunctor U ⊣
          (Functor.whiskeringLeft _ _ AddCommGrpCat.{v}).obj (Over.forget U).op).comp
    (sheafificationAdjunction J AddCommGrpCat.{v})).restrictFullyFaithful
    (iC := sheafToPresheaf (J.over U) AddCommGrpCat.{v}) (iD := 𝟭 _)
    (fullyFaithfulSheafToPresheaf _ _) (Functor.FullyFaithful.id _)
    (Functor.rightUnitor _).symm
    (Functor.leftUnitor _ ≪≫ ((Over.forget U).sheafPushforwardContinuousCompSheafToPresheafIso
      AddCommGrpCat.{v} (J.over U) J).symm)⟩⟩

instance overPullback_preservesFiniteLimits :
    PreservesFiniteLimits (J.overPullback AddCommGrpCat.{v} U) := inferInstance

variable [HasSheafify (J.over U) AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{v}]
  [J.HasSheafCompose (forget AddCommGrpCat.{v})] [(J.over U).HasSheafCompose (forget AddCommGrpCat.{v})]

instance overPullback_preservesEpimorphisms :
    (J.overPullback AddCommGrpCat.{v} U).PreservesEpimorphisms where
  preserves {F G} φ _ := by
    have : Sheaf.IsLocallySurjective φ := (Sheaf.isLocallySurjective_iff_epi' (A := AddCommGrpCat.{v}) φ).2 inferInstance
    have : Sheaf.IsLocallySurjective ((J.overPullback AddCommGrpCat.{v} U).map φ) :=
      Presheaf.isLocallySurjective_whisker (J.over U) J (Over.forget U) φ.hom
    exact (Sheaf.isLocallySurjective_iff_epi' (A := AddCommGrpCat.{v}) _).1 this

instance overPullback_preservesFiniteColimits :
    PreservesFiniteColimits (J.overPullback AddCommGrpCat.{v} U) := by
  have h := (Functor.preservesFiniteLimits_tfae (J.overPullback AddCommGrpCat.{v} U)).out 4 1
  refine ((Functor.preservesFiniteColimits_tfae (J.overPullback AddCommGrpCat.{v} U)).out 1 4).1 ?_
  intro S hS
  have := hS.epi_g
  exact ⟨(h.1 inferInstance S hS).1, (J.overPullback AddCommGrpCat.{v} U).map_epi S.g⟩

end Exact

section Const

variable [HasSheafify (J.over U) AddCommGrpCat.{v}]


omit [HasSheafify J AddCommGrpCat.{v}] in
noncomputable def overConstHomAddEquiv (G : Sheaf (J.over U) AddCommGrpCat.{v}) :
    ((constantSheaf (J.over U) AddCommGrpCat.{v}).obj (AddCommGrpCat.of (ULift.{v} ℤ)) ⟶ G) ≃+
      G.obj.obj (op (Over.mk (𝟙 U))) :=
  ((constantSheafAdj (J.over U) AddCommGrpCat.{v} (Over.mkIdTerminal (X := U))).homAddEquiv _ G).trans
    (AddCommGrpCat.uliftZMultiplesAddEquiv _)

omit [HasSheafify J AddCommGrpCat.{v}] in
lemma overConstHomAddEquiv_naturality {G G' : Sheaf (J.over U) AddCommGrpCat.{v}}
    (a : (constantSheaf (J.over U) AddCommGrpCat.{v}).obj (AddCommGrpCat.of (ULift.{v} ℤ)) ⟶ G)
    (φ : G ⟶ G') :
    overConstHomAddEquiv J U G' (a ≫ φ) = φ.hom.app _ (overConstHomAddEquiv J U G a) := by
  simp only [overConstHomAddEquiv, AddEquiv.trans_apply, Adjunction.homAddEquiv_apply,
    Adjunction.homEquiv_naturality_right]
  rfl

noncomputable def overUnitMap :
    (constantSheaf (J.over U) AddCommGrpCat.{v}).obj (AddCommGrpCat.of (ULift.{v} ℤ)) ⟶
      (freeSheaf J U).over U :=
  (overConstHomAddEquiv J U _).symm (freeSheafHomAddEquiv U (freeSheaf J U) (𝟙 _))

end Const

section Main

variable [HasSheafify (J.over U) AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{v}]
  [J.HasSheafCompose (forget AddCommGrpCat.{v})] [(J.over U).HasSheafCompose (forget AddCommGrpCat.{v})]
  [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})] [HasExt.{w'} (Sheaf (J.over U) AddCommGrpCat.{v})]

noncomputable def overCohomologyMap (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ) :
    Ext (freeSheaf J U) F n →+ Sheaf.H (F.over U) n :=
  ((Ext.mk₀ (overUnitMap J U)).precomp _ (zero_add n)).comp
    ((J.overPullback AddCommGrpCat.{v} U).mapExtAddHom (freeSheaf J U) F n)

lemma overCohomologyMap_apply (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ)
    (x : Ext (freeSheaf J U) F n) :
    overCohomologyMap J U F n x = (Ext.mk₀ (overUnitMap J U)).comp
      (x.mapExactFunctor (J.overPullback AddCommGrpCat.{v} U)) (zero_add n) := rfl

lemma overCohomologyMap_comp_mk₀ {F G : Sheaf J AddCommGrpCat.{v}} (f : F ⟶ G) (n : ℕ)
    (x : Ext (freeSheaf J U) F n) :
    overCohomologyMap J U G n (x.comp (Ext.mk₀ f) (add_zero n)) =
      (overCohomologyMap J U F n x).comp (Ext.mk₀ ((J.overPullback AddCommGrpCat.{v} U).map f))
        (add_zero n) := by
  rw [overCohomologyMap_apply, overCohomologyMap_apply, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_mk₀, Ext.comp_assoc_of_third_deg_zero]

lemma overCohomologyMap_comp_extClass {S : ShortComplex (Sheaf J AddCommGrpCat.{v})}
    (hS : S.ShortExact) (n : ℕ) (x : Ext (freeSheaf J U) S.X₃ n) :
    overCohomologyMap J U S.X₁ (n + 1) (x.comp hS.extClass rfl) =
      (overCohomologyMap J U S.X₃ n x).comp
        (hS.map_of_exact (J.overPullback AddCommGrpCat.{v} U)).extClass rfl := by
  rw [overCohomologyMap_apply, overCohomologyMap_apply, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_extClass]
  exact (Ext.comp_assoc _ _ _ (zero_add n) rfl (by omega)).symm

lemma overCohomologyMap_zero_bijective (F : Sheaf J AddCommGrpCat.{v}) :
    Function.Bijective (overCohomologyMap J U F 0) := by
  let Θ : (freeSheaf J U ⟶ F) → _ := fun g =>
    overUnitMap J U ≫ (J.overPullback AddCommGrpCat.{v} U).map g
  have key : ∀ g, overConstHomAddEquiv J U (F.over U) (Θ g) = freeSheafHomAddEquiv U F g := by
    intro g
    simp only [Θ]
    rw [overConstHomAddEquiv_naturality, overUnitMap]
    refine (congrArg (((J.overPullback AddCommGrpCat.{v} U).map g).hom.app (op (Over.mk (𝟙 U))))
      (AddEquiv.apply_symm_apply _ _)).trans ?_
    have := freeSheafHomAddEquiv_naturality U (𝟙 (freeSheaf J U)) g
    rw [Category.id_comp] at this
    exact this.symm
  have hΘ : Function.Bijective Θ := by
    have : Θ = (overConstHomAddEquiv J U (F.over U)).symm ∘ freeSheafHomAddEquiv U F :=
      funext fun g => ((AddEquiv.symm_apply_eq _).2 (key g).symm).symm
    rw [this]
    exact (AddEquiv.bijective _).comp (AddEquiv.bijective _)
  have : ⇑(overCohomologyMap J U F 0) = Ext.addEquiv₀.symm ∘ Θ ∘ Ext.addEquiv₀ := by
    funext x
    obtain ⟨g, rfl⟩ := Ext.addEquiv₀.symm.surjective x
    simp only [Function.comp_apply, AddEquiv.apply_symm_apply, Θ]
    rw [Ext.addEquiv₀_symm_apply, Ext.addEquiv₀_symm_apply, overCohomologyMap_apply, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀]
  rw [this]
  exact (AddEquiv.bijective _).comp (hΘ.comp (AddEquiv.bijective _))


attribute [local instance] Ext.subsingleton_of_injective in
theorem overCohomologyMap_bijective [EnoughInjectives (Sheaf J AddCommGrpCat.{v})] (n : ℕ) :
    ∀ F : Sheaf J AddCommGrpCat.{v}, Function.Bijective (overCohomologyMap J U F n) := by
  induction n with
  | zero => exact overCohomologyMap_zero_bijective J U
  | succ n hn =>
    intro F
    let I : InjectivePresentation F := Classical.arbitrary _
    let S := ShortComplex.mk _ _ (cokernel.condition I.f)
    letI : Injective S.X₂ := I.injective
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
    have hS' := hS.map_of_exact (J.overPullback AddCommGrpCat.{v} U)
    letI : Injective (S.map (J.overPullback AddCommGrpCat.{v} U)).X₂ :=
      (J.overPullback AddCommGrpCat.{v} U).injective_obj_of_injective I.injective
    exact AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact _ _ _ _
      (overCohomologyMap J U S.X₂ n) (overCohomologyMap J U S.X₃ n)
      (overCohomologyMap J U S.X₁ (n + 1))
      (by ext x; exact (overCohomologyMap_comp_mk₀ J U S.g n x).symm)
      (by ext x; exact (overCohomologyMap_comp_extClass J U hS n x).symm)
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' (freeSheaf J U) hS n (n + 1) rfl))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' _ hS' n (n + 1) rfl))
      (hn _).surjective (hn _)
      (fun x₁ ↦ Ext.covariant_sequence_exact₁ _ hS x₁
        (Ext.eq_zero_of_injective (x₁.comp (Ext.mk₀ S.f) (add_zero (n + 1)))) rfl)
      (fun y₁ ↦ Ext.covariant_sequence_exact₁ _ hS' y₁
        (Ext.eq_zero_of_injective (y₁.comp (Ext.mk₀ ((J.overPullback AddCommGrpCat.{v} U).map S.f))
          (add_zero (n + 1)))) rfl)

noncomputable def cohomologyPresheafOverAddEquiv [EnoughInjectives (Sheaf J AddCommGrpCat.{v})]
    (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ) :
    (F.cohomologyPresheaf n).obj (op U) ≃+ Sheaf.H (F.over U) n :=
  AddEquiv.ofBijective (overCohomologyMap J U F n) (overCohomologyMap_bijective J U n F)

end Main

section Small

variable {C : Type v} [SmallCategory C] (J : GrothendieckTopology C) (U : C)
  [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})] [HasExt.{w'} (Sheaf (J.over U) AddCommGrpCat.{v})]

noncomputable def cohomologyPresheafOverAddEquivOfSmall (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ) :
    (F.cohomologyPresheaf n).obj (op U) ≃+ Sheaf.H (F.over U) n :=
  cohomologyPresheafOverAddEquiv J U F n

end Small

end GroundTheory.Arith.SchemeCoh
