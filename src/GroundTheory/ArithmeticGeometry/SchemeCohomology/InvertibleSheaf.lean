module

public import Mathlib

@[expose] public section

section -- merged from GroundTheory.ArithmeticGeometry.SchemeCohomology.ModulesTensor
set_option maxSynthPendingDepth 1

open CategoryTheory MonoidalCategory Opposite TensorProduct

universe u v₁ u₁
variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C) {R : Cᵒᵖ ⥤ CommRingCat.{u}}

namespace GroundTheory.Arith.SchemeCoh
namespace ModulesTensor

def zeroSieve {M : PresheafOfModules.{u} (R ⋙ forget₂ _ _)} {U : Cᵒᵖ} (x : M.obj U) :
    Sieve U.unop where
  arrows _ g := M.map g.op x = 0
  downward_closed {_ _} g hg h := by
    rw [op_comp, PresheafOfModules.map_comp_apply]
    erw [hg]; exact map_zero _

def imSieve {M N : PresheafOfModules.{u} (R ⋙ forget₂ _ _)} (φ : M ⟶ N) {U : Cᵒᵖ}
    (y : N.obj U) : Sieve U.unop where
  arrows V g := ∃ x : M.obj (op V), φ.app (op V) x = N.map g.op y
  downward_closed {_ _} g := by
    rintro ⟨x, hx⟩ h
    refine ⟨M.map h.op x, ?_⟩
    rw [PresheafOfModules.naturality_apply, hx]
    change _ = N.map (h ≫ g).op y
    rw [op_comp, PresheafOfModules.map_comp_apply]

variable {J}
variable {M N : PresheafOfModules.{u} (R ⋙ forget₂ _ _)}

lemma zeroSieve_pullback {U : Cᵒᵖ} (x : M.obj U) {V : C} (g : V ⟶ U.unop) :
    (zeroSieve x).pullback g = zeroSieve (M.map g.op x) := by
  ext W h
  change M.map (h ≫ g).op x = 0 ↔ M.map h.op (M.map g.op x) = 0
  rw [op_comp, PresheafOfModules.map_comp_apply]
  exact Iff.rfl

lemma zeroSieve_zero {U : Cᵒᵖ} : zeroSieve (0 : M.obj U) = ⊤ := by
  ext W h
  simp only [Sieve.top_apply, iff_true]
  exact map_zero _

lemma zeroSieve_add {U : Cᵒᵖ} (x y : M.obj U) :
    zeroSieve x ⊓ zeroSieve y ≤ zeroSieve (x + y) := by
  rintro W h ⟨hx, hy⟩
  change M.map h.op (x + y) = 0
  rw [map_add (f := _)]
  erw [hx, hy]
  exact add_zero _

lemma imSieve_add (φ : M ⟶ N) {U : Cᵒᵖ} (x y : N.obj U) :
    imSieve φ x ⊓ imSieve φ y ≤ imSieve φ (x + y) := by
  rintro W h ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  refine ⟨a + b, ?_⟩
  rw [map_add (f := _), ha, hb, map_add (f := _)]
  rfl

section
variable (P : PresheafOfModules.{u} (R ⋙ forget₂ _ _))

lemma whiskerRight_imSieve_mem (φ : M ⟶ N) (hφ : ∀ (U : Cᵒᵖ) (y : N.obj U), imSieve φ y ∈ J U.unop)
    (U : Cᵒᵖ) (y : (N ⊗ P).obj U) : imSieve (φ ▷ P) y ∈ J U.unop := by
  induction y using TensorProduct.induction_on with
  | zero =>
    refine J.superset_covering ?_ (J.top_mem _)
    rintro W h -
    exact ⟨0, by erw [map_zero]⟩
  | tmul n p =>
    refine J.superset_covering ?_ (hφ U n)
    rintro W h ⟨m, hm⟩
    refine ⟨m ⊗ₜ P.map h.op p, ?_⟩
    change φ.app _ m ⊗ₜ _ = N.map h.op n ⊗ₜ P.map h.op p
    rw [hm]
    rfl
  | add a b ha hb =>
    exact J.superset_covering (imSieve_add (M := M ⊗ P) (N := N ⊗ P) (φ ▷ P) a b)
      (J.intersection_covering ha hb)

lemma tmul_zeroSieve_le {U : Cᵒᵖ} (m : M.obj U) (p : P.obj U) :
    zeroSieve m ≤ zeroSieve (M := M ⊗ P) (m ⊗ₜ p : (M ⊗ P).obj U) := by
  intro W h hm
  change M.map h.op m ⊗ₜ P.map h.op p = 0
  erw [hm]
  exact TensorProduct.zero_tmul _ _

lemma zeroSieve_mem_of_rTensor_rangeRestrict (φ : M ⟶ N)
    (hφ : ∀ (U : Cᵒᵖ) (x : M.obj U), φ.app U x = 0 → zeroSieve x ∈ J U.unop)
    (V : Cᵒᵖ) (z : (M ⊗ P).obj V)
    (hz : ((φ.app V).hom.rangeRestrict.rTensor (P.obj V)) z = 0) :
    zeroSieve z ∈ J V.unop := by
  letI : CommRing ((R ⋙ forget₂ CommRingCat RingCat).obj V) := inferInstanceAs (CommRing (R.obj V))
  have hex : Function.Exact (LinearMap.ker (φ.app V).hom.rangeRestrict).subtype
      (φ.app V).hom.rangeRestrict := by
    rw [LinearMap.exact_iff, Submodule.range_subtype]
  have hex' := rTensor_exact (P.obj V) hex (φ.app V).hom.surjective_rangeRestrict
  obtain ⟨w, rfl⟩ := (hex' z).1 hz
  clear hz hex hex'
  induction w using TensorProduct.induction_on with
  | zero =>
    rw [map_zero]
    exact J.superset_covering (zeroSieve_zero (M := M ⊗ P) (U := V)).ge (J.top_mem _)
  | tmul k p =>
    refine J.superset_covering (tmul_zeroSieve_le P (k : M.obj V) p) (hφ V _ ?_)
    have := k.2
    rw [LinearMap.mem_ker] at this
    exact congrArg Subtype.val this
  | add a b ha hb =>
    rw [map_add (f := _)]
    exact J.superset_covering (zeroSieve_add (M := M ⊗ P) _ _) (J.intersection_covering ha hb)

end

section
variable (P : PresheafOfModules.{u} (R ⋙ forget₂ _ _))

lemma finset_inf_mem {X : C} {ι : Type*} (T : Finset ι) (S : ι → Sieve X)
    (h : ∀ t ∈ T, S t ∈ J X) : T.inf S ∈ J X :=
  Finset.inf_induction (p := (· ∈ J X)) (J.top_mem X)
    (fun _ h₁ _ h₂ => J.intersection_covering h₁ h₂) h

lemma whiskerRight_zeroSieve_mem (φ : M ⟶ N)
    (hinj : ∀ (U : Cᵒᵖ) (x : M.obj U), φ.app U x = 0 → zeroSieve x ∈ J U.unop)
    (hsurj : ∀ (U : Cᵒᵖ) (y : N.obj U), imSieve φ y ∈ J U.unop)
    (U : Cᵒᵖ) (x : (M ⊗ P).obj U) (hx : (φ ▷ P).app U x = 0) : zeroSieve x ∈ J U.unop := by
  letI : CommRing ((R ⋙ forget₂ CommRingCat RingCat).obj U) := inferInstanceAs (CommRing (R.obj U))
  have hx' : (φ.app U).hom.rTensor (P.obj U) x = 0 := hx
  obtain ⟨A, hA, y, rfl⟩ := Submodule.exists_fg_le_eq_rTensor_subtype (x : (M.obj U) ⊗[_] (P.obj U))
  set f := (φ.app U).hom with hf
  let fA : A →ₗ[_] A.map f := f.submoduleMap A
  have h1 : (A.map f).subtype ∘ₗ fA = f ∘ₗ A.subtype := LinearMap.ext fun _ => rfl
  have h2 : (A.map f).subtype.rTensor (P.obj U) (fA.rTensor (P.obj U) y) =
      (A.map f).subtype.rTensor (P.obj U) 0 := by
    rw [← LinearMap.rTensor_comp_apply, h1, LinearMap.rTensor_comp_apply, map_zero]
    exact hx'
  obtain ⟨B, hB, hle, hB0⟩ := (hA.map f).exists_rTensor_fg_inclusion_eq h2
  rw [map_zero] at hB0
  obtain ⟨T, hT⟩ := hB
  refine J.transitive (finset_inf_mem T _ (fun t _ => hsurj U t)) _ (fun W g hg => ?_)
  erw [zeroSieve_pullback (M := M ⊗ P)]
  apply zeroSieve_mem_of_rTensor_rangeRestrict P φ hinj
  have hT' : ∀ t ∈ T, ∃ m, φ.app (op W) m = N.map g.op t :=
    fun t ht => (Finset.inf_le ht : _ ≤ imSieve φ t) g hg
  have hρ : ∀ b ∈ B, N.map g.op b ∈ LinearMap.range (φ.app (op W)).hom := by
    intro b hb
    rw [← hT] at hb
    induction hb using Submodule.span_induction with
    | mem t ht => obtain ⟨m, hm⟩ := hT' t ht; exact ⟨m, hm⟩
    | zero => erw [map_zero]; exact zero_mem _
    | add a b _ _ ha hb => erw [map_add]; exact add_mem ha hb
    | smul r a _ ha => erw [PresheafOfModules.map_smul]; exact Submodule.smul_mem _ _ ha
  let ρ : B →+ LinearMap.range (φ.app (op W)).hom :=
    { toFun := fun b => ⟨N.map g.op b, hρ b b.2⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun a b => Subtype.ext (map_add _ _ _) }
  let RW := (R ⋙ forget₂ CommRingCat RingCat).obj (op W)
  letI : CommRing RW := inferInstanceAs (CommRing (R.obj (op W)))
  let pW : P.obj U →+ P.obj (op W) :=
    { toFun := fun p => (P.map g.op p : P.obj (op W))
      map_zero' := map_zero (P.map g.op).hom
      map_add' := map_add (P.map g.op).hom }
  have pW_smul : ∀ (r : (R ⋙ forget₂ CommRingCat RingCat).obj U) (p : P.obj U),
      pW (r • p) = ((R ⋙ forget₂ CommRingCat RingCat).map g.op).hom r • pW p :=
    fun r p => PresheafOfModules.map_smul _ _ _ _
  have ρ_smul : ∀ (r : (R ⋙ forget₂ CommRingCat RingCat).obj U) (b : B),
      ρ (r • b) = ((R ⋙ forget₂ CommRingCat RingCat).map g.op).hom r • ρ b :=
    fun r b => Subtype.ext (PresheafOfModules.map_smul _ _ _ _)
  let F : B ⊗[(R ⋙ forget₂ CommRingCat RingCat).obj U] P.obj U →+
      (LinearMap.range (φ.app (op W)).hom) ⊗[RW] P.obj (op W) :=
    TensorProduct.liftAddHom (R := (R ⋙ forget₂ CommRingCat RingCat).obj U)
      { toFun := fun b => AddMonoidHom.mk' (fun p => ρ b ⊗ₜ[RW] pW p)
          (fun p q => by rw [map_add (f := _), tmul_add])
        map_zero' := by ext p; simp
        map_add' := fun a b => by ext p; simp [add_tmul] }
      (fun r b p => by
        change ρ (r • b) ⊗ₜ[RW] pW p = ρ b ⊗ₜ[RW] pW (r • p)
        rw [ρ_smul, pW_smul, smul_tmul])
  have key : ∀ z : A ⊗[_] P.obj U,
      (φ.app (op W)).hom.rangeRestrict.rTensor (P.obj (op W))
        ((M ⊗ P).map g.op (A.subtype.rTensor (P.obj U) z)) =
      F ((A.map f).inclusion hle |>.rTensor (P.obj U) (fA.rTensor (P.obj U) z)) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]; erw [map_zero]
    | tmul a p =>
      change (φ.app (op W)).hom.rangeRestrict (M.map g.op a) ⊗ₜ[RW] pW p = ρ _ ⊗ₜ[RW] pW p
      congr 1
      exact Subtype.ext (PresheafOfModules.naturality_apply φ g.op (a : M.obj U))
    | add a b ha hb =>
      simp only [map_add (f := _)] at ha hb ⊢
      exact (congrArg _ (map_add ((M ⊗ P).map g.op).hom _ _)).trans
        ((map_add _ _ _).trans (congrArg₂ (· + ·) ha hb))
  erw [key, hB0, map_zero]

end

section
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

lemma W_toPresheaf_iff (φ : M ⟶ N) :
    J.W ((PresheafOfModules.toPresheaf _).map φ) ↔
      (∀ (U : Cᵒᵖ) (x : M.obj U), φ.app U x = 0 → zeroSieve x ∈ J U.unop) ∧
      (∀ (U : Cᵒᵖ) (y : N.obj U), imSieve φ y ∈ J U.unop) := by
  rw [J.W_iff_isLocallyBijective]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun U x hx => ?_, fun U y => h2.imageSieve_mem y⟩
    have := h1.equalizerSieve_mem (X := U) x 0 (by
      erw [hx, map_zero]; rfl)
    refine J.superset_covering ?_ this
    intro W g hg
    change M.map g.op x = 0
    have hg' : M.map g.op x = M.map g.op 0 := hg
    rw [hg']
    exact map_zero _
  · rintro ⟨h1, h2⟩
    refine ⟨⟨fun {U} x y hxy => ?_⟩, ⟨fun {U} y => h2 _ y⟩⟩
    let x' : M.obj U := x
    let y' : M.obj U := y
    have hxy' : φ.app U x' = φ.app U y' := hxy
    have h := h1 U (x' - y') (by rw [map_sub, hxy', sub_self])
    refine J.superset_covering ?_ h
    intro W g hg
    have hg' : M.map g.op (x' - y') = 0 := hg
    rw [map_sub, sub_eq_zero] at hg'
    exact hg'

end


variable (J R) in
abbrev W (J : GrothendieckTopology C) (R : Cᵒᵖ ⥤ CommRingCat.{u}) :
    MorphismProperty (PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)) :=
  J.W.inverseImage (PresheafOfModules.toPresheaf _)

variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

lemma W_whiskerRight {φ : M ⟶ N} (hφ : W J R φ) (P : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) :
    W J R (φ ▷ P) := by
  rw [W, MorphismProperty.inverseImage_iff, W_toPresheaf_iff] at hφ ⊢
  exact ⟨whiskerRight_zeroSieve_mem P φ hφ.1 hφ.2, whiskerRight_imSieve_mem P φ hφ.2⟩

instance isMonoidal_W : (W J R).IsMonoidal where
  whiskerLeft P _ _ φ hφ :=
    ((W J R).arrow_mk_iso_iff (Arrow.isoMk (β_ P _) (β_ P _) (by simp))).2 (W_whiskerRight hφ P)
  whiskerRight φ hφ P := W_whiskerRight hφ P

end ModulesTensor

section
variable {C' : Type u} [Category.{u} C'] (K : GrothendieckTopology C') (S : Sheaf K CommRingCat.{u})

abbrev ringSheaf : Sheaf K RingCat.{u} := (sheafCompose K (forget₂ CommRingCat RingCat)).obj S

abbrev ringSheafId : S.obj ⋙ forget₂ CommRingCat RingCat ⟶ (ringSheaf K S).obj := 𝟙 _

instance : IsIso (ringSheafId K S) := inferInstanceAs (IsIso (𝟙 (S.obj ⋙ forget₂ CommRingCat RingCat)))

variable [HasWeakSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]

noncomputable abbrev modulesSheafification :
    PresheafOfModules.{u} (S.obj ⋙ forget₂ CommRingCat RingCat) ⥤ SheafOfModules.{u} (ringSheaf K S) :=
  PresheafOfModules.sheafification (J := K) (R₀ := S.obj ⋙ forget₂ CommRingCat RingCat)
    (R := ringSheaf K S) (ringSheafId K S)

instance : (modulesSheafification K S).IsLocalization (ModulesTensor.W K S.obj) :=
  inferInstanceAs ((PresheafOfModules.sheafification (J := K) (R₀ := S.obj ⋙ forget₂ CommRingCat RingCat)
    (R := ringSheaf K S) (ringSheafId K S)).IsLocalization
      (K.W.inverseImage (PresheafOfModules.toPresheaf (S.obj ⋙ forget₂ CommRingCat RingCat))))

instance : IsIso (PresheafOfModules.sheafificationAdjunction (J := K)
    (R₀ := S.obj ⋙ forget₂ CommRingCat RingCat) (R := ringSheaf K S) (ringSheafId K S)).counit :=
  inferInstanceAs (IsIso (PresheafOfModules.sheafificationAdjunction (J := K)
    (R := ringSheaf K S) (𝟙 (ringSheaf K S).obj)).counit)

noncomputable def sheafificationUnitIso :
    (modulesSheafification K S).obj (𝟙_ _) ≅ SheafOfModules.unit (ringSheaf K S) :=
  @asIso _ _ _ _ _ (NatIso.isIso_app_of_isIso (PresheafOfModules.sheafificationAdjunction (J := K)
    (R₀ := S.obj ⋙ forget₂ CommRingCat RingCat) (R := ringSheaf K S) (ringSheafId K S)).counit
      (SheafOfModules.unit (ringSheaf K S)))

end

section
variable {C' : Type u} [Category.{u} C'] (K : GrothendieckTopology C') (S : Sheaf K CommRingCat.{u})
variable [HasWeakSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]

@[instance_reducible]
noncomputable def sheafModulesMonoidal : MonoidalCategory (SheafOfModules.{u} (ringSheaf K S)) :=
  inferInstanceAs (MonoidalCategory (LocalizedMonoidal (L := modulesSheafification K S)
    (W := ModulesTensor.W K S.obj) (sheafificationUnitIso K S)))

attribute [local instance] sheafModulesMonoidal

@[instance_reducible]
noncomputable def sheafModulesSymmetric : SymmetricCategory (SheafOfModules.{u} (ringSheaf K S)) :=
  inferInstanceAs (SymmetricCategory (LocalizedMonoidal (L := modulesSheafification K S)
    (W := ModulesTensor.W K S.obj) (sheafificationUnitIso K S)))

@[instance_reducible]
noncomputable def modulesSheafificationMonoidal : (modulesSheafification K S).Monoidal :=
  inferInstanceAs (Localization.Monoidal.toMonoidalCategory (L := modulesSheafification K S)
    (W := ModulesTensor.W K S.obj) (sheafificationUnitIso K S)).Monoidal

attribute [local instance] modulesSheafificationMonoidal

end

end GroundTheory.Arith.SchemeCoh
end

set_option maxSynthPendingDepth 1

open CategoryTheory MonoidalCategory Opposite TensorProduct AlgebraicGeometry TopologicalSpace

universe u

namespace GroundTheory.Arith.SchemeCoh
variable {X : Scheme.{u}}

variable (X) in
abbrev PMod (X : Scheme.{u}) := PresheafOfModulesOfCommRing.{u} X.sheaf.obj

private theorem schemeModules_W_whiskerRight {M N : PMod X} {φ : M ⟶ N}
    (hφ : ModulesTensor.W (J := Opens.grothendieckTopology X) (R := X.sheaf.obj) φ)
    (P : PMod X) :
    ModulesTensor.W (J := Opens.grothendieckTopology X) (R := X.sheaf.obj) (φ ▷ P) := by
  rw [ModulesTensor.W, MorphismProperty.inverseImage_iff, ModulesTensor.W_toPresheaf_iff] at hφ ⊢
  exact ⟨ModulesTensor.whiskerRight_zeroSieve_mem P φ hφ.1 hφ.2,
    ModulesTensor.whiskerRight_imSieve_mem P φ hφ.2⟩

local instance :
    (ModulesTensor.W (J := Opens.grothendieckTopology X) (R := X.sheaf.obj)).IsMonoidal where
  whiskerLeft P _ _ φ hφ :=
    ((ModulesTensor.W (J := Opens.grothendieckTopology X) (R := X.sheaf.obj)).arrow_mk_iso_iff
      (Arrow.isoMk (β_ P _) (β_ P _) (by simp))).2 (schemeModules_W_whiskerRight hφ P)
  whiskerRight φ hφ P := schemeModules_W_whiskerRight hφ P

noncomputable instance : MonoidalCategory X.Modules :=
  inferInstanceAs (MonoidalCategory (LocalizedMonoidal
    (modulesSheafification (Opens.grothendieckTopology X) X.sheaf)
    (ModulesTensor.W (J := Opens.grothendieckTopology X) (R := X.sheaf.obj))
    (sheafificationUnitIso (Opens.grothendieckTopology X) X.sheaf)))

noncomputable instance : SymmetricCategory X.Modules :=
  inferInstanceAs (SymmetricCategory (LocalizedMonoidal
    (modulesSheafification (Opens.grothendieckTopology X) X.sheaf)
    (ModulesTensor.W (J := Opens.grothendieckTopology X) (R := X.sheaf.obj))
    (sheafificationUnitIso (Opens.grothendieckTopology X) X.sheaf)))

instance isIso_ringSheafId_scheme : IsIso (ringSheafId (Opens.grothendieckTopology X) X.sheaf) :=
  inferInstanceAs (IsIso (𝟙 (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)))


variable (X) in
noncomputable abbrev sheafifyMod (X : Scheme.{u}) : PMod X ⥤ X.Modules :=
  modulesSheafification (Opens.grothendieckTopology X) X.sheaf


variable (X) in
noncomputable abbrev preMod (X : Scheme.{u}) : X.Modules ⥤ PMod X :=
  SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars (ringSheafId _ X.sheaf)


variable (X) in
noncomputable abbrev sheafifyModAdj (X : Scheme.{u}) : sheafifyMod X ⊣ preMod X :=
  PresheafOfModules.sheafificationAdjunction (J := Opens.grothendieckTopology X)
    (R₀ := X.sheaf.obj ⋙ forget₂ CommRingCat RingCat) (R := X.ringCatSheaf) (ringSheafId _ X.sheaf)

instance isIso_sheafifyModAdj_counit : IsIso (sheafifyModAdj X).counit :=
  inferInstanceAs (IsIso (PresheafOfModules.sheafificationAdjunction (J := Opens.grothendieckTopology X)
    (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).counit)

noncomputable instance : (sheafifyMod X).Monoidal :=
  inferInstanceAs (Localization.Monoidal.toMonoidalCategory
    (modulesSheafification (Opens.grothendieckTopology X) X.sheaf)
    (ModulesTensor.W (J := Opens.grothendieckTopology X) (R := X.sheaf.obj))
    (sheafificationUnitIso (Opens.grothendieckTopology X) X.sheaf)).Monoidal

noncomputable def tensorIso (M N : X.Modules) :
    (sheafifyMod X).obj ((preMod X).obj M ⊗ (preMod X).obj N) ≅ M ⊗ N :=
  (Functor.Monoidal.μIso (sheafifyMod X) _ _).symm ≪≫
    (asIso ((sheafifyModAdj X).counit.app M) ⊗ᵢ asIso ((sheafifyModAdj X).counit.app N))

noncomputable def tensorToSheaf (M N : X.Modules) :
    (preMod X).obj M ⊗ (preMod X).obj N ⟶ (preMod X).obj (M ⊗ N) :=
  (sheafifyModAdj X).unit.app _ ≫ (preMod X).map (tensorIso M N).hom

noncomputable def tensorLift {M N G : X.Modules}
    (e : (preMod X).obj M ⊗ (preMod X).obj N ⟶ (preMod X).obj G) : M ⊗ N ⟶ G :=
  (tensorIso M N).inv ≫ ((sheafifyModAdj X).homEquiv _ _).symm e

lemma tensorToSheaf_tensorLift {M N G : X.Modules}
    (e : (preMod X).obj M ⊗ (preMod X).obj N ⟶ (preMod X).obj G) :
    tensorToSheaf M N ≫ (preMod X).map (tensorLift e) = e := by
  rw [tensorToSheaf, tensorLift, Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_assoc,
    ← Adjunction.homEquiv_unit, Equiv.apply_symm_apply]

lemma W_tensorToSheaf (M N : X.Modules) :
    ModulesTensor.W (J := Opens.grothendieckTopology X) (R := X.sheaf.obj) (tensorToSheaf M N) := by
  refine MorphismProperty.comp_mem _ _ _ ?_ (MorphismProperty.of_isIso _ _)
  change (Opens.grothendieckTopology X).W ((PresheafOfModules.toPresheaf _).map _)
  rw [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
  exact GrothendieckTopology.W_toSheafify _ _

lemma sheaf_eq_of_locally {C : Type*} [Category.{u} C] {FC : C → C → Type*} {CC : C → Type u}
    [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{u} C FC]
    [Limits.HasLimitsOfSize.{u, u} C] [(forget C).ReflectsIsomorphisms]
    [Limits.PreservesLimitsOfSize.{u, u} (forget C)]
    {T : TopCat.{u}} (F : TopCat.Sheaf C T) {V : Opens T} (s t : ToType (F.1.obj (op V)))
    (h : ∀ x ∈ V, ∃ (W : Opens T) (i : W ≤ V), x ∈ W ∧
      F.1.map (homOfLE i).op s = F.1.map (homOfLE i).op t) : s = t := by
  choose W i hx h using h
  refine F.eq_of_locally_eq' (U := fun x : V => W x.1 x.2) V (fun x => homOfLE (i _ _)) ?_ s t
    (fun x => h _ _)
  intro x hxV
  exact Opens.mem_iSup.2 ⟨⟨x, hxV⟩, hx _ _⟩

lemma sheaf_exists_glue {C : Type*} [Category.{u} C] {FC : C → C → Type*} {CC : C → Type u}
    [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{u} C FC]
    [Limits.HasLimitsOfSize.{u, u} C] [(forget C).ReflectsIsomorphisms]
    [Limits.PreservesLimitsOfSize.{u, u} (forget C)]
    {T : TopCat.{u}} (F : TopCat.Sheaf C T) {V : Opens T} {ι : Type u} (W : ι → Opens T)
    (i : ∀ a, W a ≤ V) (hcov : ∀ x ∈ V, ∃ a, x ∈ W a) (sf : ∀ a, ToType (F.1.obj (op (W a))))
    (hsf : ∀ a b, F.1.map (homOfLE (inf_le_left : W a ⊓ W b ≤ W a)).op (sf a) =
      F.1.map (homOfLE (inf_le_right : W a ⊓ W b ≤ W b)).op (sf b)) :
    ∃ s : ToType (F.1.obj (op V)), ∀ a, F.1.map (homOfLE (i a)).op s = sf a := by
  obtain ⟨s, hs, -⟩ := F.existsUnique_gluing' W V (fun a => homOfLE (i a))
    (fun x hxV => Opens.mem_iSup.2 (hcov x hxV)) sf hsf
  exact ⟨s, hs⟩

noncomputable def resM (P : PMod X) {U V : X.Opens} (h : V ≤ U) (x : P.obj (op U)) : P.obj (op V) :=
  P.map (homOfLE h).op x

abbrev ringOn (X : Scheme.{u}) (V : X.Opens) := (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op V)

noncomputable def resR {U V : X.Opens} (h : V ≤ U) : ringOn X U →+* ringOn X V :=
  ((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).map (homOfLE h).op).hom

lemma resM_resM (P : PMod X) {U V W : X.Opens} (h : V ≤ U) (i : W ≤ V) (x : P.obj (op U)) :
    resM P i (resM P h x) = resM P (i.trans h) x := by
  rw [resM, resM, resM, ← PresheafOfModules.map_comp_apply]
  rfl

lemma resM_smul (P : PMod X) {U V : X.Opens} (h : V ≤ U) (r : ringOn X U) (x : P.obj (op U)) :
    resM P h (r • x) = resR h r • resM P h x :=
  PresheafOfModules.map_smul _ _ _ _

lemma resM_add (P : PMod X) {U V : X.Opens} (h : V ≤ U) (x y : P.obj (op U)) :
    resM P h (x + y) = resM P h x + resM P h y :=
  map_add _ _ _

lemma resM_smul_res (P : PMod X) {U V W : X.Opens} (h : V ≤ U) (i : W ≤ V) (r : ringOn X V)
    (x : P.obj (op U)) : resM P i (r • resM P h x) = resR i r • resM P (i.trans h) x := by
  rw [resM_smul, resM_resM]

lemma app_resM {P Q : PMod X} (φ : P ⟶ Q) {U V : X.Opens} (h : V ≤ U) (x : P.obj (op U)) :
    φ.app (op V) (resM P h x) = resM Q h (φ.app (op U) x) :=
  PresheafOfModules.naturality_apply φ _ x

lemma app_smul {P Q : PMod X} (φ : P ⟶ Q) {U : X.Opens} (r : ringOn X U) (x : P.obj (op U)) :
    φ.app (op U) (r • x) = r • φ.app (op U) x :=
  (φ.app (op U)).hom.map_smul r x

lemma resR_resR {U V W : X.Opens} (h : V ≤ U) (i : W ≤ V) (r : ringOn X U) :
    resR i (resR h r) = resR (i.trans h) r := by
  rw [resR, resR, resR, ← RingHom.comp_apply, ← RingCat.hom_comp, ← Functor.map_comp]
  rfl

def IsBasisOn (P : PMod X) (U : X.Opens) (s : P.obj (op U)) : Prop :=
  ∀ (V : X.Opens) (h : V ≤ U), Function.Bijective
    (fun r : (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op V) => r • resM P h s)

theorem IsBasisOn.map_of_alt {P : PMod X} {F : X.Modules} (φ : P ⟶ (preMod X).obj F)
    (hφ : ModulesTensor.W (J := Opens.grothendieckTopology X) (R := X.sheaf.obj) φ)
    {U : X.Opens} {s : P.obj (op U)} (hs : IsBasisOn P U s) :
    IsBasisOn ((preMod X).obj F) U (φ.app _ s) := by
  obtain ⟨hinj, hsurj⟩ := (ModulesTensor.W_toPresheaf_iff φ).1 hφ
  have hres : ∀ (V : X.Opens) (h : V ≤ U), resM ((preMod X).obj F) h (φ.app _ s) =
      φ.app _ (resM P h s) :=
    fun V h => (PresheafOfModules.naturality_apply φ _ s).symm
  have hsm : ∀ (V : X.Opens) (r : ringOn X V) (x : P.obj (op V)),
      φ.app (op V) (r • x) = r • φ.app (op V) x := fun V r x => (φ.app (op V)).hom.map_smul r x
  have hPsm : ∀ (V W : X.Opens) (i : W ≤ V) (h : V ≤ U) (r : ringOn X V),
      resM P i (r • resM P h s) =
        (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).map (homOfLE i).op r • resM P (i.trans h) s := by
    intro V W i h r
    rw [resM, PresheafOfModules.map_smul, resM, ← PresheafOfModules.map_comp_apply]
    rfl
  have inj : ∀ (V : X.Opens) (h : V ≤ U) (r : ringOn X V),
      r • resM ((preMod X).obj F) h (φ.app _ s) = 0 → r = 0 := by
    intro V h r hr
    rw [hres, ← hsm] at hr
    have hz := hinj (op V) _ hr
    apply sheaf_eq_of_locally X.sheaf (V := V) r 0
    intro x hx
    obtain ⟨W, f, hf, hxW⟩ := hz x hx
    refine ⟨W, f.le, hxW, ?_⟩
    have hf' : resM P f.le (r • resM P h s) = 0 := hf
    rw [hPsm] at hf'
    have := (hs W (f.le.trans h)).1 (a₁ := (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).map
      (homOfLE f.le).op r) (a₂ := 0) (by simp only [zero_smul]; exact hf')
    change ((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).map (homOfLE f.le).op) r = _
    rw [this]
    exact (map_zero _).symm
  intro V h
  constructor
  · intro r₁ r₂ e
    have := inj V h (r₁ - r₂) (by rw [sub_smul]; exact sub_eq_zero.mpr e)
    exact sub_eq_zero.mp this
  · intro σ
    have hσ := hsurj (op V) σ
    choose W f hf hxW using hσ
    choose p hp using hf
    have hWU : ∀ x hx, W x hx ≤ U := fun x hx => (f x hx).le.trans h
    choose rr hrr using fun x hx => (hs (W x hx) (hWU x hx)).2 (p x hx)
    have key : ∀ x hx, rr x hx • resM ((preMod X).obj F) (hWU x hx) (φ.app _ s) =
        resM ((preMod X).obj F) (f x hx).le σ := by
      intro x hx
      have e := hrr x hx
      simp only at e
      rw [← app_resM, ← app_smul, e]
      exact hp x hx
    obtain ⟨r, hr⟩ := sheaf_exists_glue X.sheaf (V := V) (ι := V) (fun a => W a.1 a.2)
      (fun a => (f a.1 a.2).le) (fun x hx => ⟨⟨x, hx⟩, hxW x hx⟩) (fun a => rr a.1 a.2) (by
        intro a b
        have hab : W a.1 a.2 ⊓ W b.1 b.2 ≤ U := inf_le_left.trans (hWU _ _)
        have := inj _ hab (resR inf_le_left (rr a.1 a.2) - resR inf_le_right (rr b.1 b.2)) (by
          rw [sub_smul, sub_eq_zero, ← resM_smul_res _ (hWU a.1 a.2) inf_le_left,
            ← resM_smul_res _ (hWU b.1 b.2) inf_le_right, key, key, resM_resM, resM_resM])
        exact sub_eq_zero.mp this)
    refine ⟨r, ?_⟩
    apply sheaf_eq_of_locally ⟨F.presheaf, F.isSheaf⟩ (V := V)
    intro x hx
    refine ⟨W x hx, (f x hx).le, hxW x hx, ?_⟩
    change resM ((preMod X).obj F) (f x hx).le (r • resM ((preMod X).obj F) h (φ.app _ s)) =
      resM ((preMod X).obj F) (f x hx).le σ
    rw [resM_smul, resM_resM, ← key x hx]
    congr 1
    exact hr ⟨x, hx⟩

lemma IsBasisOn.restrict {P : PMod X} {U : X.Opens} {s : P.obj (op U)} (hs : IsBasisOn P U s)
    {V : X.Opens} (h : V ≤ U) : IsBasisOn P V (resM P h s) := by
  intro W i
  have := hs W (i.trans h)
  simp only [resM_resM]
  exact this

lemma isBasisOn_one (U : X.Opens) :
    IsBasisOn ((preMod X).obj (𝟙_ X.Modules)) U (1 : ringOn X U) := by
  intro V h
  have e : resM ((preMod X).obj (𝟙_ X.Modules)) h (1 : ringOn X U) = (1 : ringOn X V) :=
    map_one (resR h)
  simp only [e]
  change Function.Bijective (fun r : ringOn X V => r * 1)
  simp only [mul_one]
  exact Function.bijective_id

lemma IsBasisOn.tmul {P Q : PMod X} {U : X.Opens} {s : P.obj (op U)} {t : Q.obj (op U)}
    (hs : IsBasisOn P U s) (ht : IsBasisOn Q U t) :
    IsBasisOn (P ⊗ Q) U (s ⊗ₜ t : (P ⊗ Q).obj (op U)) := by
  intro V h
  have e : resM (P ⊗ Q) h (s ⊗ₜ t : (P ⊗ Q).obj (op U)) =
      (resM P h s ⊗ₜ resM Q h t : (P ⊗ Q).obj (op V)) := rfl
  rw [e]
  let R := X.sheaf.obj.obj (op V)
  let eP := LinearEquiv.ofBijective (LinearMap.toSpanSingleton R _ (resM P h s)) (hs V h)
  let eQ := LinearEquiv.ofBijective (LinearMap.toSpanSingleton R _ (resM Q h t)) (ht V h)
  let E := (TensorProduct.lid R R).symm ≪≫ₗ TensorProduct.congr eP eQ
  have hE : ∀ r : R, E r = r • (resM P h s ⊗ₜ[R] resM Q h t) := by
    intro r
    change eP 1 ⊗ₜ[R] eQ r = _
    change ((1 : R) • resM P h s) ⊗ₜ[R] (r • resM Q h t) = _
    rw [one_smul, TensorProduct.tmul_smul]
  have : (fun r : R => r • (resM P h s ⊗ₜ[R] resM Q h t)) = E := by
    funext r
    exact (hE r).symm
  have hb := E.bijective
  rw [← this] at hb
  exact hb

lemma IsBasisOn.map_iso {M N : X.Modules} (e : M ≅ N) {U : X.Opens}
    {s : ((preMod X).obj M).obj (op U)} (hs : IsBasisOn ((preMod X).obj M) U s) :
    IsBasisOn ((preMod X).obj N) U (((preMod X).map e.hom).app _ s) :=
  hs.map_of_alt _ (MorphismProperty.of_isIso _ _)

def IsInvertibleSheaf (M : X.Modules) : Prop :=
  ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U) (s : ((preMod X).obj M).obj (op U)),
    IsBasisOn ((preMod X).obj M) U s

lemma isIso_of_locally_bijective {M N : X.Modules} (f : M ⟶ N)
    (hf : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∀ V ≤ U, Function.Bijective (f.app V)) : IsIso f := by
  choose U hxU hU using hf
  have nat : ∀ {V W : X.Opens} (i : W ≤ V) (σ : Γ(M, V)),
      f.app W (M.presheaf.map (homOfLE i).op σ) = N.presheaf.map (homOfLE i).op (f.app V σ) :=
    fun i σ => NatTrans.naturality_apply f.mapPresheaf (homOfLE i).op σ
  have inj : ∀ V : X.Opens, Function.Injective (f.app V) := by
    intro V σ τ hστ
    apply sheaf_eq_of_locally ⟨M.presheaf, M.isSheaf⟩ (V := V)
    intro x hx
    refine ⟨V ⊓ U x, inf_le_left, ⟨hx, hxU x⟩, ?_⟩
    apply (hU x (V ⊓ U x) inf_le_right).1
    change f.app _ (M.presheaf.map _ σ) = f.app _ (M.presheaf.map _ τ)
    rw [nat, nat, hστ]
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro V
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨inj V, fun τ => ?_⟩
  have loc : ∀ x : {x : X // x ∈ V}, ∃ σ : Γ(M, V ⊓ U x.1),
      f.app _ σ = N.presheaf.map (homOfLE (inf_le_left : V ⊓ U x.1 ≤ V)).op τ :=
    fun x => (hU x.1 _ inf_le_right).2 _
  choose σ hσ using loc
  obtain ⟨g, hg⟩ := sheaf_exists_glue ⟨M.presheaf, M.isSheaf⟩ (V := V) (ι := {x : X // x ∈ V})
    (fun a => V ⊓ U a.1) (fun _ => inf_le_left) (fun x hx => ⟨⟨x, hx⟩, hx, hxU x⟩) σ (by
      intro a b
      apply inj
      change f.app _ (M.presheaf.map _ (σ a)) = f.app _ (M.presheaf.map _ (σ b))
      rw [nat, nat, hσ, hσ]
      change ((N.presheaf.map _ ≫ N.presheaf.map _) τ) = ((N.presheaf.map _ ≫ N.presheaf.map _) τ)
      rw [← N.presheaf.map_comp, ← N.presheaf.map_comp]
      rfl)
  refine ⟨g, ?_⟩
  apply sheaf_eq_of_locally ⟨N.presheaf, N.isSheaf⟩ (V := V)
  intro x hx
  refine ⟨V ⊓ U x, inf_le_left, ⟨hx, hxU x⟩, ?_⟩
  change N.presheaf.map _ (f.app V g) = _
  rw [← nat]
  have := hg ⟨x, hx⟩
  simp only at this
  rw [this]
  exact hσ ⟨x, hx⟩

lemma bijective_app_of_isBasisOn {M N : X.Modules} (f : M ⟶ N) {U : X.Opens}
    {s : ((preMod X).obj M).obj (op U)} (hs : IsBasisOn ((preMod X).obj M) U s)
    (hfs : IsBasisOn ((preMod X).obj N) U (((preMod X).map f).app _ s)) (V : X.Opens) (h : V ≤ U) :
    Function.Bijective (f.app V) := by
  have e : (fun r : ringOn X V => r • resM ((preMod X).obj N) h (((preMod X).map f).app _ s)) =
      f.app V ∘ (fun r : ringOn X V => r • resM ((preMod X).obj M) h s) := by
    funext r
    change _ = ((preMod X).map f).app (op V) (r • resM ((preMod X).obj M) h s)
    rw [app_smul, app_resM]
  have h1 := hfs V h
  rw [e] at h1
  exact (Function.Bijective.of_comp_iff _ (hs V h)).1 h1

lemma isIso_of_isBasisOn {M N : X.Modules} (f : M ⟶ N)
    (hf : ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U) (s : ((preMod X).obj M).obj (op U)),
      IsBasisOn ((preMod X).obj M) U s ∧ IsBasisOn ((preMod X).obj N) U (((preMod X).map f).app _ s)) :
    IsIso f := by
  apply isIso_of_locally_bijective
  intro x
  obtain ⟨U, hx, s, hs, hfs⟩ := hf x
  exact ⟨U, hx, fun V h => bijective_app_of_isBasisOn f hs hfs V h⟩

end GroundTheory.Arith.SchemeCoh
