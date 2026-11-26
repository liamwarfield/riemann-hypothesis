module

public import Mathlib

@[expose] public section

section -- merged from GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.HasExtInstances
set_option maxSynthPendingDepth 1

open AlgebraicGeometry CategoryTheory Abelian TopologicalSpace

universe u

namespace GroundTheory.Arith.SchemeCoh

noncomputable instance hasExt_zariski (X : Scheme.{u}) :
    HasExt.{u} (Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u}) :=
  hasExt_of_enoughInjectives.{u} _

noncomputable instance hasExt_zariski_over (X : Scheme.{u}) (V : X.Opens) :
    HasExt.{u} (Sheaf ((Opens.grothendieckTopology X.toTopCat).over V) AddCommGrpCat.{u}) :=
  hasExt_of_enoughInjectives.{u} _

end GroundTheory.Arith.SchemeCoh
end

section -- merged from GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.PullbackGamma
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Limits Opposite

universe u

noncomputable section

variable {P X Y Z : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}

theorem isPushout_app_of_isPullback (H : IsPullback fst snd f g) [IsAffine Y] [IsAffine Z]
    {V : X.Opens} (hV : IsAffineOpen V) :
    IsPushout (f.appLE ⊤ V le_top) g.appTop (fst.app V) (snd.appLE ⊤ (fst ⁻¹ᵁ V) le_top) := by
  have : IsAffine V.toScheme := hV
  have hP := (isPullback_morphismRestrict fst V).paste_vert H
  have hA := isPushout_appTop_of_isPullback hP
  refine hA.of_iso (Iso.refl _) (Scheme.Opens.topIso V) (Iso.refl _)
    (Scheme.Opens.topIso (fst ⁻¹ᵁ V)) ?_ ?_ ?_ ?_
  · simp only [Iso.refl_hom, Category.id_comp, Scheme.Hom.comp_appTop, Scheme.Opens.topIso_hom,
      Scheme.Opens.ι_appTop, Scheme.Hom.appLE]
    erw [Category.assoc, ← Functor.map_comp]
    rfl
  · simp
  · simp only [Scheme.Opens.topIso_hom, morphismRestrict_appTop]
    erw [Category.assoc, ← Functor.map_comp, ← Scheme.Hom.naturality]
    rfl
  · simp only [Iso.refl_hom, Category.id_comp, Scheme.Hom.comp_appTop, Scheme.Opens.topIso_hom,
      Scheme.Opens.ι_appTop, Scheme.Hom.appLE]
    erw [Category.assoc, ← Functor.map_comp]
    rfl

end

end GroundTheory.Arith.SchemeCoh
end

section -- merged from GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.SchemeImage
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Limits

universe u

noncomputable section

namespace SchemeImage

variable {Y Z : Scheme.{u}} (f : Y ⟶ Z) [QuasiCompact f] (W : Z.Opens)

theorem ker_morphismRestrict : (f ∣_ W).ker = f.ker.comap W.ι := by
  ext V : 2
  rw [Scheme.ker_ideal_of_isPullback_of_isOpenImmersion f (f ∣_ W) (f ⁻¹ᵁ W).ι W.ι
    (isPullback_morphismRestrict f W) V,
    Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]

theorem exists_lift_imageι_morphismRestrict {C : Scheme.{u}} (c : C ⟶ W.toScheme)
    [IsClosedImmersion c] (g : (f ⁻¹ᵁ W).toScheme ⟶ C) (hg : g ≫ c = f ∣_ W) :
    ∃ k : (f.imageι ⁻¹ᵁ W).toScheme ⟶ C, k ≫ c = f.imageι ∣_ W := by
  have H : c.ker ≤ (f.imageι ∣_ W).ker := by
    rw [ker_morphismRestrict, Scheme.IdealSheafData.ker_subschemeι, ← ker_morphismRestrict, ← hg]
    exact Scheme.Hom.le_ker_comp g c
  exact ⟨IsClosedImmersion.lift c _ H, IsClosedImmersion.lift_fac _ _ _⟩

def imageRestrictLift [IsClosedImmersion (f ∣_ W)] :
    (f.imageι ⁻¹ᵁ W).toScheme ⟶ (f ⁻¹ᵁ W).toScheme :=
  IsClosedImmersion.lift (f ∣_ W) (f.imageι ∣_ W) (by
    rw [ker_morphismRestrict, ker_morphismRestrict, Scheme.IdealSheafData.ker_subschemeι])

@[reassoc (attr := simp)]
lemma imageRestrictLift_fac [IsClosedImmersion (f ∣_ W)] :
    imageRestrictLift f W ≫ (f ∣_ W) = f.imageι ∣_ W :=
  IsClosedImmersion.lift_fac _ _ _

instance isIso_imageRestrictLift [IsClosedImmersion (f ∣_ W)] :
    IsIso (imageRestrictLift f W) :=
  IsClosedImmersion.isIso_lift _ _ (by
    rw [ker_morphismRestrict, ker_morphismRestrict, Scheme.IdealSheafData.ker_subschemeι])



end SchemeImage

section EqLocus

variable {T S B : Scheme.{u}} (p : S ⟶ B) [IsSeparated p] (g h : T ⟶ S) (hgh : g ≫ p = h ≫ p)

abbrev eqLocus : Scheme.{u} :=
  pullback (pullback.diagonal p) (pullback.lift g h hgh)

abbrev eqLocusι : eqLocus p g h hgh ⟶ T := pullback.snd _ _

instance : IsClosedImmersion (eqLocusι p g h hgh) := by
  dsimp only [eqLocusι, eqLocus]
  infer_instance


omit [IsSeparated p] in
lemma eqLocusι_comp_eq : eqLocusι p g h hgh ≫ g = eqLocusι p g h hgh ≫ h := by
  have h₁ := congrArg (· ≫ pullback.fst p p) (pullback.condition (f := pullback.diagonal p)
    (g := pullback.lift g h hgh))
  have h₂ := congrArg (· ≫ pullback.snd p p) (pullback.condition (f := pullback.diagonal p)
    (g := pullback.lift g h hgh))
  simp only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id,
    pullback.lift_fst, pullback.lift_snd] at h₁ h₂
  rw [← h₁, h₂]

def eqLocusLift {V : Scheme.{u}} (t : V ⟶ T) (ht : t ≫ g = t ≫ h) : V ⟶ eqLocus p g h hgh :=
  pullback.lift (t ≫ g) t (by
    apply pullback.hom_ext <;>
      simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.diagonal_fst,
        pullback.diagonal_snd, Category.comp_id, ht])

omit [IsSeparated p] in
@[reassoc (attr := simp)]
lemma eqLocusLift_ι {V : Scheme.{u}} (t : V ⟶ T) (ht : t ≫ g = t ≫ h) :
    eqLocusLift p g h hgh t ht ≫ eqLocusι p g h hgh = t :=
  pullback.lift_snd _ _ _

end EqLocus

end

end GroundTheory.Arith.SchemeCoh
end

section -- merged from GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.RestrictIso
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory TopologicalSpace Limits

universe u

noncomputable section

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

lemma isIso_morphismRestrict_of_le {U U' : Y.Opens} (h : U' ≤ U) [IsIso (f ∣_ U)] :
    IsIso (f ∣_ U') := by
  have h1 : IsPullback (f ∣_ U') (f ⁻¹ᵁ U').ι U'.ι f := isPullback_morphismRestrict f U'
  have h2 : IsPullback (f ∣_ U) (f ⁻¹ᵁ U).ι U.ι f := isPullback_morphismRestrict f U
  have hU : Y.homOfLE h ≫ U.ι = U'.ι := Y.homOfLE_ι h
  have hX : X.homOfLE (f.preimage_mono h) ≫ (f ⁻¹ᵁ U).ι = (f ⁻¹ᵁ U').ι := X.homOfLE_ι _
  have hsq : X.homOfLE (f.preimage_mono h) ≫ f ∣_ U = f ∣_ U' ≫ Y.homOfLE h := by
    rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, Category.assoc, hU,
      morphismRestrict_ι, ← Category.assoc, hX]
  have h3 : IsPullback (X.homOfLE (f.preimage_mono h)) (f ∣_ U') (f ∣_ U) (Y.homOfLE h) := by
    refine IsPullback.of_right ?_ hsq h2.flip
    rw [hX, hU]
    exact h1.flip
  exact h3.isIso_snd_of_isIso

lemma bijective_app_of_isIso_morphismRestrict {U : Y.Opens} [IsIso (f ∣_ U)] {V : Y.Opens}
    (hV : V ≤ U) : Function.Bijective (f.app V) := by
  have := isIso_morphismRestrict_of_le f hV
  have h0 : IsIso ((f ∣_ V).app ⊤) := inferInstance
  have h1 : IsIso (f.app (V.ι ''ᵁ ⊤) ≫
      X.presheaf.map (eqToHom (image_morphismRestrict_preimage f V ⊤)).op) := by
    rw [← morphismRestrict_app]
    exact h0
  have h2 : IsIso (f.app (V.ι ''ᵁ ⊤)) := IsIso.of_isIso_comp_right _
    (X.presheaf.map (eqToHom (image_morphismRestrict_preimage f V ⊤)).op)
  have e : V.ι ''ᵁ ⊤ = V := V.ι_image_top
  rw [e] at h2
  exact ConcreteCategory.bijective_of_isIso _

lemma injOn_of_isIso_morphismRestrict {U : Y.Opens} [IsIso (f ∣_ U)] :
    Set.InjOn f.base (f ⁻¹ᵁ U : Set X) := by
  intro a ha b hb hab
  have hinj : Function.Injective (f ∣_ U).base :=
    (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso (asIso (f ∣_ U)))).injective
  have := @hinj ⟨a, ha⟩ ⟨b, hb⟩ (Subtype.ext
    ((morphismRestrict_base_coe f U ⟨a, ha⟩).trans (hab.trans
      (morphismRestrict_base_coe f U ⟨b, hb⟩).symm)))
  exact congrArg Subtype.val this

lemma exists_preimage_of_isIso_morphismRestrict {U : Y.Opens} [IsIso (f ∣_ U)] {y : Y}
    (hy : y ∈ U) : ∃ x : X, x ∈ f ⁻¹ᵁ U ∧ f.base x = y := by
  have hsurj : Function.Surjective (f ∣_ U).base :=
    (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso (asIso (f ∣_ U)))).surjective
  obtain ⟨⟨x, hx⟩, hxy⟩ := hsurj ⟨y, hy⟩
  refine ⟨x, hx, ?_⟩
  exact (morphismRestrict_base_coe f U ⟨x, hx⟩).symm.trans (congrArg Subtype.val hxy)

end

end GroundTheory.Arith.SchemeCoh
end

section -- merged from GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.FormalLimit
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

universe u

noncomputable section

section Tower

variable {A : Type u} [CommRing A] {E : ℕ → Type u} [∀ n, AddCommGroup (E n)]
  [∀ n, Module A (E n)] (τ : ∀ n, E (n + 1) →ₗ[A] E n)

def towerLimit : Submodule A (∀ n, E n) where
  carrier := {x | ∀ n, τ n (x (n + 1)) = x n}
  add_mem' {x y} hx hy n := by
    change τ n (x (n + 1) + y (n + 1)) = x n + y n
    rw [map_add (f := _), hx n, hy n]
  zero_mem' n := by
    change τ n 0 = 0
    exact map_zero _
  smul_mem' a x hx n := by
    change τ n (a • x (n + 1)) = a • x n
    rw [map_smul, hx n]

def towerComp (n : ℕ) : (k : ℕ) → E (n + k) →ₗ[A] E n
  | 0 => LinearMap.id
  | k + 1 => (towerComp n k).comp (τ (n + k))

lemma towerComp_apply_of_mem {x : ∀ n, E n} (hx : x ∈ towerLimit τ) (n k : ℕ) :
    towerComp τ n k (x (n + k)) = x n := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change towerComp τ n k (τ (n + k) (x (n + k + 1))) = x n
    rw [hx (n + k)]
    exact ih

theorem towerLimit_eq_bot {c : ℕ} (hc : ∀ n, towerComp τ n c = 0) : towerLimit τ = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Submodule.mem_bot]
  funext n
  rw [← towerComp_apply_of_mem τ hx n c, hc n, LinearMap.zero_apply]
  rfl

end Tower

section Exact

variable {A : Type u} [CommRing A]
  {P E Q : ℕ → Type u} [∀ n, AddCommGroup (P n)] [∀ n, Module A (P n)]
  [∀ n, AddCommGroup (E n)] [∀ n, Module A (E n)] [∀ n, AddCommGroup (Q n)]
  [∀ n, Module A (Q n)]
  (τP : ∀ n, P (n + 1) →ₗ[A] P n) (τE : ∀ n, E (n + 1) →ₗ[A] E n) (τQ : ∀ n, Q (n + 1) →ₗ[A] Q n)
  (ι : ∀ n, P n →ₗ[A] E n) (π : ∀ n, E n →ₗ[A] Q n)
  (hι : ∀ n, (τE n).comp (ι (n + 1)) = (ι n).comp (τP n))
  (hπ : ∀ n, (τQ n).comp (π (n + 1)) = (π n).comp (τE n))



variable (hinj : ∀ n, Function.Injective (ι n))
  (hex : ∀ n, LinearMap.range (ι n) = LinearMap.ker (π n))

def towerLimitMap : towerLimit τP →ₗ[A] towerLimit τE where
  toFun x := ⟨fun n => ι n (x.1 n), fun n => by
    have := congrArg (fun f => f (x.1 (n + 1))) (hι n)
    simp only [LinearMap.comp_apply] at this
    rw [this, x.2 n]⟩
  map_add' x y := by
    ext n
    exact map_add (ι n) _ _
  map_smul' a x := by
    ext n
    exact map_smul (ι n) _ _


include hι hπ hinj hex in
theorem bijective_towerLimitMap (hinj : ∀ n, Function.Injective (ι n))
    (hex : ∀ n, LinearMap.range (ι n) = LinearMap.ker (π n))
    (hπ : ∀ n, (τQ n).comp (π (n + 1)) = (π n).comp (τE n))
    {c : ℕ} (hc : ∀ n, towerComp τQ n c = 0) :
    Function.Bijective (towerLimitMap τP τE ι hι) := by
  constructor
  · intro x y hxy
    ext n
    exact hinj n (congrArg (fun z : towerLimit τE => z.1 n) hxy)
  · intro e
    have hQ : ∀ n, π n (e.1 n) = 0 := by
      have hmem : (fun n => π n (e.1 n)) ∈ towerLimit τQ := fun n => by
        have := congrArg (fun f => f (e.1 (n + 1))) (hπ n)
        simp only [LinearMap.comp_apply] at this
        rw [this, e.2 n]
      rw [towerLimit_eq_bot τQ hc] at hmem
      intro n
      exact congrFun ((Submodule.mem_bot A).1 hmem) n
    have hp : ∀ n, ∃ p, ι n p = e.1 n := fun n => by
      have : e.1 n ∈ LinearMap.range (ι n) := by
        rw [hex n]
        exact hQ n
      exact this
    choose p hp using hp
    refine ⟨⟨p, fun n => hinj n ?_⟩, ?_⟩
    · have := congrArg (fun f => f (p (n + 1))) (hι n)
      simp only [LinearMap.comp_apply] at this
      rw [← this, hp, hp, e.2 n]
    · ext n
      exact hp n

end Exact

section Adic

variable {A : Type u} [CommRing A] (I : Ideal A) {H : Type u} [AddCommGroup H] [Module A H]
  (K : ℕ → Submodule A H) (hK : Antitone K)

def quotTower : ∀ n, (H ⧸ K (n + 1)) →ₗ[A] (H ⧸ K n) :=
  fun n => Submodule.factor (hK (Nat.le_succ n))

variable {I K}

end Adic

end

end GroundTheory.Arith.SchemeCoh
end
