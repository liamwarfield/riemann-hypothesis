module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.SubsingletonOfSubsingletonFreeSheaf
open CategoryTheory Opposite Limits Abelian

universe w v u

noncomputable section

namespace GlobalTheory.SiteCoh

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{v}]

abbrev freeSheaf : C ⥤ Sheaf J AddCommGrpCat.{v} :=
  yoneda ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙ presheafToSheaf _ _

variable {J}

def freeSheafHomEquiv (U : C) (F : Sheaf J AddCommGrpCat.{v}) :
    ((freeSheaf J).obj U ⟶ F) ≃+ F.obj.obj (op U) where
  toEquiv := ((sheafificationAdjunction J AddCommGrpCat.{v}).homEquiv _ F).trans
    (((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv (yoneda.obj U) F.obj).trans yonedaEquiv)
  map_add' _ _ := rfl

lemma freeSheafHomEquiv_comp (U : C) {F G : Sheaf J AddCommGrpCat.{v}}
    (φ : (freeSheaf J).obj U ⟶ F) (f : F ⟶ G) :
    freeSheafHomEquiv U G (φ ≫ f) = f.hom.app (op U) (freeSheafHomEquiv U F φ) := rfl

def freePresheafIsoConst {T : C} (hT : IsTerminal T) :
    yoneda.obj T ⋙ AddCommGrpCat.free.{v} ≅
      (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{v} ℤ)) :=
  NatIso.ofComponents
    (fun V ↦
      letI : Unique (V.unop ⟶ T) := ⟨⟨hT.from _⟩, fun _ ↦ hT.hom_ext _ _⟩
      ((FreeAbelianGroup.uniqueEquiv (V.unop ⟶ T)).trans AddEquiv.ulift.symm).toAddCommGrpIso)
    (fun {V W} f ↦ by
      apply AddCommGrpCat.hom_ext
      apply FreeAbelianGroup.lift_ext
      intro x
      rfl)

def freeSheafIsoConst {T : C} (hT : IsTerminal T) :
    (freeSheaf J).obj T ≅ (constantSheaf J AddCommGrpCat.{v}).obj (AddCommGrpCat.of (ULift ℤ)) :=
  (presheafToSheaf J _).mapIso (freePresheafIsoConst hT)

variable [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]

def extEquiv (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ) (U : C) :
    F.H' n U ≃+ Ext.{w} ((freeSheaf J).obj U) F n :=
  AddEquiv.refl _

abbrev map {F G : Sheaf J AddCommGrpCat.{v}} (f : F ⟶ G) (n : ℕ) (U : C) :
    F.H' n U ⟶ G.H' n U :=
  ((Sheaf.cohomologyPresheafFunctor J n).map f).app (op U)

abbrev res (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ) {U V : C} (i : V ⟶ U) :
    F.H' n U ⟶ F.H' n V :=
  (F.cohomologyPresheaf n).map i.op

lemma extEquiv_map {F G : Sheaf J AddCommGrpCat.{v}} (f : F ⟶ G) (n : ℕ) (U : C)
    (x : F.H' n U) :
    extEquiv G n U (map f n U x) = (extEquiv F n U x).comp (Ext.mk₀ f) (add_zero n) := rfl

instance cohomologyPresheafFunctor_additive (n : ℕ) :
    (Sheaf.cohomologyPresheafFunctor.{w} J n).Additive where
  map_add {F G f g} := by
    ext U x
    apply (extEquiv G n U.unop).injective
    change (extEquiv F n U.unop x).comp (Ext.mk₀ (f + g)) (add_zero n) =
      (extEquiv F n U.unop x).comp (Ext.mk₀ f) (add_zero n) +
        (extEquiv F n U.unop x).comp (Ext.mk₀ g) (add_zero n)
    rw [Ext.mk₀_add, Ext.comp_add]

def zeroEquiv (F : Sheaf J AddCommGrpCat.{v}) (U : C) : F.H' 0 U ≃+ F.obj.obj (op U) :=
  (extEquiv F 0 U).trans (Ext.addEquiv₀.trans (freeSheafHomEquiv U F))

lemma zeroEquiv_mk₀ (F : Sheaf J AddCommGrpCat.{v}) (U : C) (φ : (freeSheaf J).obj U ⟶ F) :
    zeroEquiv F U ((extEquiv F 0 U).symm (Ext.mk₀ φ)) = freeSheafHomEquiv U F φ := by
  simp only [zeroEquiv, AddEquiv.trans_apply, AddEquiv.apply_symm_apply]
  congr 1
  exact Ext.addEquiv₀.apply_symm_apply φ

lemma zeroEquiv_map {F G : Sheaf J AddCommGrpCat.{v}} (f : F ⟶ G) (U : C) (x : F.H' 0 U) :
    zeroEquiv G U (map f 0 U x) = f.hom.app (op U) (zeroEquiv F U x) := by
  obtain ⟨y, rfl⟩ := (extEquiv F 0 U).symm.surjective x
  obtain ⟨φ, rfl⟩ := (Ext.mk₀_bijective _ _).surjective y
  rw [zeroEquiv_mk₀, ← freeSheafHomEquiv_comp, ← zeroEquiv_mk₀]
  congr 1
  apply (extEquiv G 0 U).injective
  rw [extEquiv_map, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, Ext.mk₀_comp_mk₀]

def terminalEquiv (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ) {T : C} (hT : IsTerminal T) :
    F.H' n T ≃+ F.H n :=
  (extEquiv F n T).trans
    (((extFunctor n).mapIso (freeSheafIsoConst (J := J) hT).symm.op).app F).addCommGroupIsoToAddEquiv

lemma terminalEquiv_apply (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ) {T : C} (hT : IsTerminal T)
    (x : F.H' n T) :
    terminalEquiv F n hT x =
      (Ext.mk₀ (freeSheafIsoConst hT).inv).comp (extEquiv F n T x) (zero_add n) := rfl

lemma terminalEquiv_map {F G : Sheaf J AddCommGrpCat.{v}} (f : F ⟶ G) (n : ℕ) {T : C}
    (hT : IsTerminal T) (x : F.H' n T) :
    terminalEquiv G n hT (map f n T x) = Sheaf.H.map f n (terminalEquiv F n hT x) := by
  rw [terminalEquiv_apply, terminalEquiv_apply, extEquiv_map, Sheaf.H.map_apply]
  symm
  apply Ext.comp_assoc
  all_goals omega

lemma equiv₀_terminalEquiv (F : Sheaf J AddCommGrpCat.{v}) {T : C} (hT : IsTerminal T)
    (x : F.H' 0 T) :
    Sheaf.H.equiv₀ F hT (terminalEquiv F 0 hT x) = zeroEquiv F T x := by
  obtain ⟨y, rfl⟩ := (extEquiv F 0 T).symm.surjective x
  obtain ⟨φ, rfl⟩ := (Ext.mk₀_bijective _ _).surjective y
  rw [zeroEquiv_mk₀, terminalEquiv_apply, AddEquiv.apply_symm_apply, Ext.mk₀_comp_mk₀]
  obtain ⟨ψ, rfl⟩ : ∃ ψ, (freeSheafIsoConst hT).hom ≫ ψ = φ :=
    ⟨(freeSheafIsoConst hT).inv ≫ φ, by simp⟩
  rw [Iso.inv_hom_id_assoc, freeSheafHomEquiv_comp]
  have h : (Ext.addEquiv₀ (Ext.mk₀.{w} ψ)) = ψ := Ext.addEquiv₀.apply_symm_apply ψ
  simp only [Sheaf.H.equiv₀, AddEquiv.trans_apply, h]
  have h₁ := ConcreteCategory.congr_hom (NatTrans.congr_app
    (toSheafify_naturality J (freePresheafIsoConst hT).hom) (op T))
    (FreeAbelianGroup.of (𝟙 T))
  exact congrArg (ψ.hom.app (op T)) h₁

end GlobalTheory.SiteCoh
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits

universe w v u

noncomputable section

namespace GlobalTheory

variable {X : Scheme.{u}}


variable (X) in
def toAbSheaf : X.Modules ⥤ Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf X.ringCatSheaf

instance toAbSheaf_additive : (toAbSheaf (X := X)).Additive :=
  inferInstanceAs (SheafOfModules.toSheaf X.ringCatSheaf).Additive

instance toAbSheaf_preservesFiniteLimits : PreservesFiniteLimits (toAbSheaf (X := X)) :=
  inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf X.ringCatSheaf))

abbrev restrictGlobal (X : Scheme.{u}) (U : X.Opens) : Γ(X, ⊤) →+* Γ(X, U) :=
  (X.presheaf.map (homOfLE le_top : U ⟶ ⊤).op).hom

lemma restrictGlobal_top (r : Γ(X, ⊤)) : restrictGlobal X ⊤ r = r := by
  have : (homOfLE le_top : (⊤ : X.Opens) ⟶ ⊤) = 𝟙 _ := rfl
  rw [restrictGlobal, this, op_id, X.presheaf.map_id]
  rfl

lemma map_restrictGlobal {U V : X.Opens} (i : V ⟶ U) (r : Γ(X, ⊤)) :
    X.presheaf.map i.op (restrictGlobal X U r) = restrictGlobal X V r := by
  rw [restrictGlobal, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

def smulHom (F : X.Modules) (r : Γ(X, ⊤)) : F ⟶ F :=
  SheafOfModules.Hom.mk <| PresheafOfModules.homMk
    { app := fun U ↦ (F.smul (restrictGlobal X U.unop r)).asHom
      naturality := fun U V i ↦ by
        have := F.map_comp_smul i.unop (restrictGlobal X U.unop r)
        rw [map_restrictGlobal] at this
        exact this.symm }
    (fun U a m ↦ smul_comm (restrictGlobal X U.unop r) (show Γ(X, U.unop) from a) (show Γ(F, U.unop) from m))

@[simp] lemma smulHom_app_apply (F : X.Modules) (r : Γ(X, ⊤)) (U : X.Opens) (x : Γ(F, U)) :
    (smulHom F r).app U x = restrictGlobal X U r • x := rfl

@[simp] lemma smulHom_one (F : X.Modules) : smulHom F 1 = 𝟙 F := by
  ext U x; rw [smulHom_app_apply, map_one, one_smul]; rfl

@[simp] lemma smulHom_zero (F : X.Modules) : smulHom F 0 = 0 := by
  ext U x; rw [smulHom_app_apply, map_zero, zero_smul]; rfl

lemma smulHom_add (F : X.Modules) (r s : Γ(X, ⊤)) :
    smulHom F (r + s) = smulHom F r + smulHom F s := by
  ext U x; rw [smulHom_app_apply, map_add (f := _), add_smul]; rfl

lemma smulHom_mul (F : X.Modules) (r s : Γ(X, ⊤)) :
    smulHom F (r * s) = smulHom F s ≫ smulHom F r := by
  ext U x; rw [smulHom_app_apply, map_mul, mul_smul]; rfl

lemma smulHom_comp {F G : X.Modules} (r : Γ(X, ⊤)) (φ : F ⟶ G) :
    smulHom F r ≫ φ = φ ≫ smulHom G r := by
  ext U x
  exact φ.app_smul (restrictGlobal X U r) x

def smulEnd (F : X.Modules) : Γ(X, ⊤) →+* End F where
  toFun r := ⟨smulHom F r⟩
  map_one' := by apply End.ext; simp
  map_mul' r s := by apply End.ext; simpa using smulHom_mul F r s
  map_zero' := by apply End.ext; simp
  map_add' r s := by apply End.ext; simpa using smulHom_add F r s

instance linearModules : Linear Γ(X, ⊤) X.Modules where
  homModule F G :=
    { smul r φ := φ ≫ smulHom G r
      one_smul φ := by change φ ≫ _ = _; rw [smulHom_one, Category.comp_id]
      mul_smul r s φ := by change φ ≫ _ = (φ ≫ _) ≫ _; rw [smulHom_mul, Category.assoc]
      smul_zero r := zero_comp
      smul_add r φ ψ := Preadditive.add_comp _ _ _ _ _ _
      add_smul r s φ := by
        change φ ≫ _ = φ ≫ _ + φ ≫ _; rw [smulHom_add, Preadditive.comp_add]
      zero_smul φ := by change φ ≫ _ = _; rw [smulHom_zero, comp_zero] }
  smul_comp F G H r φ ψ := by
    change (φ ≫ _) ≫ ψ = (φ ≫ ψ) ≫ _
    rw [Category.assoc, Category.assoc, smulHom_comp]
  comp_smul F G H φ r ψ := (Category.assoc _ _ _).symm

lemma smul_hom_def {F G : X.Modules} (r : Γ(X, ⊤)) (φ : F ⟶ G) : r • φ = φ ≫ smulHom G r := rfl

lemma smulHom_eq_smul_id (F : X.Modules) (r : Γ(X, ⊤)) : smulHom F r = r • 𝟙 F :=
  (Category.id_comp _).symm

@[reducible] def addCommGroupOfAction {A M : Type*} [CommRing A] (inst : AddCommGroup M)
    (ρ : A →+* AddMonoid.End M) : AddCommGroup M :=
  { inst with
    zsmul := fun n x ↦ ρ (algebraMap ℤ A n) x
    zsmul_zero' := fun x ↦ by
      change ρ (algebraMap ℤ A 0) x = 0
      rw [map_zero, map_zero]; rfl
    zsmul_succ' := fun n x ↦ by
      change ρ (algebraMap ℤ A (n + 1 : ℕ)) x = ρ (algebraMap ℤ A n) x + x
      rw [Nat.cast_succ, map_add (f := _), map_add (f := _), map_one, map_one]; rfl
    zsmul_neg' := fun n x ↦ by
      change ρ (algebraMap ℤ A (Int.negSucc n)) x = -ρ (algebraMap ℤ A (n + 1 : ℕ)) x
      rw [show Int.negSucc n = -((n + 1 : ℕ) : ℤ) from rfl, map_neg, map_neg]; rfl }

def WithAction {A M : Type*} [CommRing A] [AddCommGroup M] (_ρ : A →+* AddMonoid.End M) := M

namespace WithAction

variable {A M N : Type*} [CommRing A] [AddCommGroup M] [AddCommGroup N]
  (ρ : A →+* AddMonoid.End M) (σ : A →+* AddMonoid.End N)

instance instAddCommGroup : AddCommGroup (WithAction ρ) := addCommGroupOfAction (M := M) ‹_› ρ

def toBase : WithAction ρ ≃+ M where
  toEquiv := Equiv.refl _
  map_add' _ _ := rfl

variable (R : Type*) [CommRing R] [Algebra R A]

instance instModule : Module R (WithAction ρ) where
  smul r x := ρ (algebraMap R A r) x
  one_smul x := by
    change ρ (algebraMap R A 1) x = x
    rw [map_one, map_one]; rfl
  mul_smul r s x := by
    change ρ (algebraMap R A (r * s)) x = _
    rw [map_mul, map_mul]; rfl
  smul_zero r := map_zero (ρ (algebraMap R A r))
  smul_add r := map_add (ρ (algebraMap R A r))
  add_smul r s x := by
    change ρ (algebraMap R A (r + s)) x = _
    rw [map_add (f := _), map_add (f := _)]; rfl
  zero_smul x := by
    change ρ (algebraMap R A 0) x = _
    rw [map_zero, map_zero]; rfl


variable {R} in
lemma toBase_smul (r : R) (x : WithAction ρ) :
    toBase ρ (r • x) = ρ (algebraMap R A r) (toBase ρ x) := rfl

instance instIsScalarTower (S : Type*) [CommRing S] [Algebra S A] [Algebra R S]
    [IsScalarTower R S A] : IsScalarTower R S (WithAction ρ) :=
  .of_algebraMap_smul fun r x ↦ by
    apply (toBase ρ).injective
    rw [toBase_smul, toBase_smul, ← IsScalarTower.algebraMap_apply]

def linearMap (f : M →+ N) (h : ∀ a x, f (ρ a x) = σ a (f x)) :
    WithAction ρ →ₗ[R] WithAction σ where
  toFun := f
  map_add' := f.map_add
  map_smul' _ x := h _ x

lemma toBase_linearMap (f : M →+ N) (h : ∀ a x, f (ρ a x) = σ a (f x)) (x : WithAction ρ) :
    toBase σ (linearMap ρ σ R f h x) = f (toBase ρ x) := rfl

def linearEquiv (f : M ≃+ N) (h : ∀ a x, f (ρ a x) = σ a (f x)) :
    WithAction ρ ≃ₗ[R] WithAction σ where
  toFun := f
  invFun := f.symm
  left_inv := f.left_inv
  right_inv := f.right_inv
  map_add' := f.map_add
  map_smul' _ x := h _ x

end WithAction

def functorEndRingHom {C : Type u} {D : Type v} [Category C] [Category D]
    [Preadditive C] [Preadditive D] (G : C ⥤ D) [G.Additive] (Y : C) :
    End Y →+* End (G.obj Y) where
  toFun f := ⟨G.map f.asHom⟩
  map_one' := by
    apply End.ext
    exact G.map_id Y
  map_mul' f g := by
    apply End.ext
    exact G.map_comp g.asHom f.asHom
  map_zero' := by
    apply End.ext
    exact G.map_zero Y Y
  map_add' f g := by
    apply End.ext
    exact G.map_add

namespace SiteCoh

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{v}] [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]
  {F G H : Sheaf J AddCommGrpCat.{v}} {n : ℕ} {U V W : C}

lemma map_id_apply (x : F.H' n U) : map (𝟙 F) n U x = x := by
  simp only [map, CategoryTheory.Functor.map_id]; rfl

lemma map_comp_apply (f : F ⟶ G) (g : G ⟶ H) (x : F.H' n U) :
    map (f ≫ g) n U x = map g n U (map f n U x) := by
  simp only [map, Functor.map_comp]; rfl

lemma map_add_apply (f g : F ⟶ G) (x : F.H' n U) :
    map (f + g) n U x = map f n U x + map g n U x := by
  change ((Abelian.Ext.mk₀ (f + g)).postcomp _ (add_zero n)) x =
    ((Abelian.Ext.mk₀ f).postcomp _ (add_zero n)) x +
      ((Abelian.Ext.mk₀ g).postcomp _ (add_zero n)) x
  simp [Abelian.Ext.mk₀_add, Abelian.Ext.postcomp]
  rfl

lemma map_zero_apply (x : F.H' n U) : map (0 : F ⟶ G) n U x = 0 := by
  simp only [map, Functor.map_zero]; rfl

lemma res_id_apply (x : F.H' n U) : res F n (𝟙 U) x = x := by
  simp only [res, op_id, CategoryTheory.Functor.map_id]; rfl

lemma res_comp_apply (i : V ⟶ U) (j : W ⟶ V) (x : F.H' n U) :
    res F n (j ≫ i) x = res F n j (res F n i x) := by
  simp only [res, op_comp, Functor.map_comp]; rfl

lemma res_map_apply (f : F ⟶ G) (i : V ⟶ U) (x : F.H' n U) :
    res G n i (map f n U x) = map f n V (res F n i x) :=
  (ConcreteCategory.congr_hom
    (((Sheaf.cohomologyPresheafFunctor J n).map f).naturality i.op) x).symm


variable (F n U) in
def endAction : End F →+* AddMonoid.End (F.H' n U) where
  toFun f := (map f.asHom n U).hom
  map_one' := AddMonoidHom.ext (fun x => map_id_apply x)
  map_mul' f g := AddMonoidHom.ext (fun x => map_comp_apply g.asHom f.asHom x)
  map_zero' := AddMonoidHom.ext (fun x => map_zero_apply x)
  map_add' f g := AddMonoidHom.ext (fun x => map_add_apply f.asHom g.asHom x)

lemma endAction_apply (f : End F) (x : F.H' n U) :
    endAction (F := F) (n := n) (U := U) f x = map f.asHom n U x := rfl

end SiteCoh

end GlobalTheory
