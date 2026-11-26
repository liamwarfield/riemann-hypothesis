module

public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.GlobalGen
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.PSpaceFinite
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.ImmersionPullback
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.ImmersionCech

@[expose] public section

section -- merged from GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.SerreP
section -- merged from GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.SerrePAux
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe c236Ext c236Scheme

end

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits MonoidalCategory
  MvPolynomial

universe w' u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

section Additive

variable {X : Scheme.{u}}

lemma modulesAbMap_add {F G : X.Modules} (φ ψ : F ⟶ G) :
    modulesAbMap (φ + ψ) = modulesAbMap φ + modulesAbMap ψ := by
  ext U x
  rfl

variable [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u})]
  (A : Type*) [CommRing A] [Algebra A Γ(X, ⊤)]

lemma H.linearMap_add {F G : X.Modules} (φ ψ : F ⟶ G) (p : ℕ) :
    H.linearMap.{w'} A (φ + ψ) p = H.linearMap A φ p + H.linearMap A ψ p := by
  ext x
  simp only [H.linearMap_apply, LinearMap.add_apply, modulesAbMap_add, Sheaf.H.map_add_apply]

lemma H.linearMap_comp {F G K : X.Modules} (φ : F ⟶ G) (ψ : G ⟶ K) (p : ℕ) :
    H.linearMap.{w'} A (φ ≫ ψ) p = (H.linearMap A ψ p).comp (H.linearMap A φ p) := by
  ext x
  simp only [H.linearMap_apply, LinearMap.comp_apply, modulesAbMap_comp, Sheaf.H.map_comp_apply]

lemma H.linearMap_id (F : X.Modules) (p : ℕ) :
    H.linearMap.{w'} A (𝟙 F) p = LinearMap.id := by
  ext x
  simp only [H.linearMap_apply, LinearMap.id_apply, modulesAbMap_id, Sheaf.H.map_id_apply]

lemma H.linearMap_zero (F G : X.Modules) (p : ℕ) :
    H.linearMap.{w'} A (0 : F ⟶ G) p = 0 := by
  have h := H.linearMap_add.{w'} A (0 : F ⟶ G) 0 p
  rw [add_zero] at h
  exact left_eq_add.mp h

lemma H.linearMap_sum {F G : X.Modules} {ι : Type*} (s : Finset ι) (φ : ι → (F ⟶ G)) (p : ℕ) :
    H.linearMap.{w'} A (∑ i ∈ s, φ i) p = ∑ i ∈ s, H.linearMap A (φ i) p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [H.linearMap_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, H.linearMap_add, ih]

def H.linearEquivOfIso {F G : X.Modules} (e : F ≅ G) (p : ℕ) :
    Sheaf.H.{w'} (modulesAb F) p ≃ₗ[A] Sheaf.H.{w'} (modulesAb G) p :=
  ((H.moduleFunctor.{w'} A p).mapIso e).toLinearEquiv

end Additive

section Delta

variable {X : Scheme.{u}}

def abSC (S : ShortComplex X.Modules) :
    ShortComplex (Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u}) :=
  ShortComplex.mk (modulesAbMap S.f) (modulesAbMap S.g) (by
    rw [← modulesAbMap_comp, S.zero]
    exact (SheafOfModules.toSheaf X.ringCatSheaf).map_zero _ _)

lemma shortExact_abSC {S : ShortComplex X.Modules} (hS : S.ShortExact) : (abSC S).ShortExact :=
  shortExact_abShortComplex hS

variable [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u})]
  (A : Type*) [CommRing A] [Algebra A Γ(X, ⊤)]
  {S : ShortComplex X.Modules} (hS : (abSC S).ShortExact)

def abSmulEnd (S : ShortComplex X.Modules) (r : Γ(X, ⊤)) : abSC S ⟶ abSC S where
  τ₁ := modulesAbMap (smulHom S.X₁ r)
  τ₂ := modulesAbMap (smulHom S.X₂ r)
  τ₃ := modulesAbMap (smulHom S.X₃ r)
  comm₁₂ := smulAbRingHom_comp S.f r
  comm₂₃ := smulAbRingHom_comp S.g r

def H.δLinear (p : ℕ) :
    Sheaf.H.{w'} (modulesAb S.X₃) p →ₗ[A] Sheaf.H.{w'} (modulesAb S.X₁) (p + 1) where
  toFun := H.δ hS p (p + 1) rfl
  map_add' := map_add _
  map_smul' a x :=
    H.δ_naturality hS hS (abSmulEnd S (algebraMap A Γ(X, ⊤) a)) p (p + 1) rfl x

lemma H.δLinear_apply (p : ℕ) (x : Sheaf.H.{w'} (modulesAb S.X₃) p) :
    H.δLinear A hS p x = H.δ hS p (p + 1) rfl x := rfl

end Delta

section Finite

theorem finite_of_exact_noetherian {R M₁ M₂ M₃ : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃] [Module R M₁] [Module R M₂] [Module R M₃]
    [Module.Finite R M₁] [Module.Finite R M₃] (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃)
    (hfg : ∀ y, g y = 0 → ∃ x, f x = y) : Module.Finite R M₂ := by
  have hker : LinearMap.ker g ≤ LinearMap.range f := fun y hy => hfg y hy
  have hN3 : IsNoetherian R M₃ := isNoetherian_of_isNoetherianRing_of_finite R M₃
  have hrg : (LinearMap.range g).FG := IsNoetherian.noetherian _
  have hrf : (LinearMap.range f).FG := by
    rw [LinearMap.range_eq_map]; exact Module.Finite.fg_top.map f
  have hN : IsNoetherian R (LinearMap.range f) := isNoetherian_of_fg_of_noetherian _ hrf
  have hkf : (LinearMap.ker g).FG := by
    have h0 : ((LinearMap.ker g).comap (LinearMap.range f).subtype).FG := IsNoetherian.noetherian _
    have h := h0.map (LinearMap.range f).subtype
    rwa [Submodule.map_comap_eq, Submodule.range_subtype, inf_eq_right.mpr hker] at h
  refine ⟨Submodule.fg_of_fg_map_of_fg_inf_ker g ?_ ?_⟩
  · rw [Submodule.map_top]; exact hrg
  · rw [top_inf_eq]; exact hkf

end Finite

section Sandwich

variable {X : Scheme.{u}}
  [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u})]
  (A : Type*) [CommRing A] [Algebra A Γ(X, ⊤)]
  {S : ShortComplex X.Modules} (hS : S.ShortExact)

include hS in
theorem finite_H_X₃ [IsNoetherianRing A] (p : ℕ)
    [Module.Finite A (Sheaf.H.{w'} (modulesAb S.X₂) p)]
    [Module.Finite A (Sheaf.H.{w'} (modulesAb S.X₁) (p + 1))] :
    Module.Finite A (Sheaf.H.{w'} (modulesAb S.X₃) p) :=
  finite_of_exact_noetherian (H.linearMap A S.g p) (H.δLinear A (shortExact_abSC hS) p)
    fun y hy => H.exact₃ (shortExact_abSC hS) rfl y hy

include hS in
theorem subsingleton_H_X₃ (p : ℕ) [Subsingleton (Sheaf.H.{w'} (modulesAb S.X₂) p)]
    [Subsingleton (Sheaf.H.{w'} (modulesAb S.X₁) (p + 1))] :
    Subsingleton (Sheaf.H.{w'} (modulesAb S.X₃) p) := by
  have key : ∀ y : Sheaf.H.{w'} (modulesAb S.X₃) p, y = 0 := fun y => by
    have : Subsingleton (Sheaf.H.{w'} (abSC S).X₁ (p + 1)) :=
      ‹Subsingleton (Sheaf.H.{w'} (modulesAb S.X₁) (p + 1))›
    obtain ⟨x, hx⟩ := H.exact₃ (shortExact_abSC hS) rfl y (Subsingleton.elim _ _)
    have : Subsingleton (Sheaf.H.{w'} (abSC S).X₂ p) := ‹Subsingleton (Sheaf.H.{w'} (modulesAb S.X₂) p)›
    rw [← hx, Subsingleton.elim x 0, map_zero]
    rfl
  exact ⟨fun y z => (key y).trans (key z).symm⟩

end Sandwich

namespace ProjSpace

variable {A : Type u} [CommRing A] {n : ℕ}

abbrev twistEquiv (k : ℤ) : (projectiveSpace A n).Modules ≌ (projectiveSpace A n).Modules :=
  tensorEquivOfInvertible (isInvertibleSheaf_twistingSheaf (A := A) (n := n) k)

lemma twistEquiv_obj (k : ℤ) (M : (projectiveSpace A n).Modules) :
    (twistEquiv k).functor.obj M = twist M k := by
  rw [twistEquiv, tensorEquivOfInvertible_functor]
  rfl

lemma twistEquiv_additive (k : ℤ) : (twistEquiv (A := A) (n := n) k).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

variable (A n) in
abbrev freeP (I : Type u) : (projectiveSpace A n).Modules :=
  SheafOfModules.free (R := (projectiveSpace A n).ringCatSheaf) I

def ιP {I : Type u} (i : I) : 𝟙_ (projectiveSpace A n).Modules ⟶ freeP A n I :=
  SheafOfModules.ιFree i

def πP {I : Type u} [DecidableEq I] (i : I) : freeP A n I ⟶ 𝟙_ (projectiveSpace A n).Modules :=
  Cofan.IsColimit.desc (A := SheafOfModules.unit (projectiveSpace A n).ringCatSheaf)
    (SheafOfModules.isColimitFreeCofan I) fun j => if j = i then 𝟙 _ else 0

lemma freeSheaf_hom_ext {I : Type u} {M : (projectiveSpace A n).Modules} (f g : freeP A n I ⟶ M)
    (h : ∀ j, ιP j ≫ f = ιP j ≫ g) : f = g :=
  Cofan.IsColimit.hom_ext (SheafOfModules.isColimitFreeCofan I) f g fun j => by
    rw [SheafOfModules.freeCofan_inj]
    exact h j

lemma ιP_πP {I : Type u} [DecidableEq I] (i j : I) :
    ιP (A := A) (n := n) j ≫ πP i = if j = i then 𝟙 _ else 0 := by
  have := Cofan.IsColimit.fac (SheafOfModules.isColimitFreeCofan
    (R := (projectiveSpace A n).ringCatSheaf) I) (fun j => if j = i then 𝟙 _ else 0) j
  rw [SheafOfModules.freeCofan_inj] at this
  exact this

lemma free_total {I : Type u} [Fintype I] [DecidableEq I] :
    ∑ i, πP (A := A) (n := n) i ≫ ιP i = 𝟙 (freeP A n I) := by
  refine freeSheaf_hom_ext _ _ fun j => ?_
  rw [Preadditive.comp_sum, Category.comp_id, Finset.sum_eq_single j]
  · rw [← Category.assoc, ιP_πP, ite_eq_left rfl, Category.id_comp]
  · intro b _ hb
    rw [← Category.assoc, ιP_πP, ite_eq_right (Ne.symm hb), zero_comp]
  · intro h
    exact absurd (Finset.mem_univ j) h

lemma finite_sections_unit (U : (projectiveSpace A n).Opens) :
    Module.Finite Γ(projectiveSpace A n, U) Γ(𝟙_ (projectiveSpace A n).Modules, U) := by
  let one : Γ(𝟙_ (projectiveSpace A n).Modules, U) := (show Γ(projectiveSpace A n, U) from 1)
  refine ⟨⟨{one}, ?_⟩⟩
  rw [eq_top_iff]
  intro x _
  rw [Finset.coe_singleton, Submodule.mem_span_singleton]
  exact ⟨(show Γ(projectiveSpace A n, U) from x), mul_one (show Γ(projectiveSpace A n, U) from x)⟩

lemma twist_total (k : ℤ) {I : Type u} [Fintype I] [DecidableEq I] :
    ∑ i, (twistEquiv (A := A) (n := n) k).functor.map (πP i) ≫
      (twistEquiv k).functor.map (ιP i) = 𝟙 ((twistEquiv k).functor.obj (freeP A n I)) := by
  have : (twistEquiv (A := A) (n := n) k).functor.Additive := twistEquiv_additive k
  set F := (twistEquiv (A := A) (n := n) k).functor
  calc ∑ i, F.map (πP i) ≫ F.map (ιP i)
      = ∑ i, F.map (πP (A := A) (n := n) i ≫ ιP i) := by
        simp only [Functor.map_comp]
    _ = F.map (∑ i, πP (A := A) (n := n) i ≫ ιP i) := (F.map_sum _ _).symm
    _ = F.map (𝟙 _) := congrArg F.map free_total
    _ = 𝟙 _ := F.map_id _

lemma sum_app_apply {M N : (projectiveSpace A n).Modules} {ι : Type*} (s : Finset ι)
    (φ : ι → (M ⟶ N)) (U : (projectiveSpace A n).Opens) (x : Γ(M, U)) :
    (∑ i ∈ s, φ i).app U x = ∑ i ∈ s, (φ i).app U x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih]

theorem isCoherent_freeP (I : Type u) [Finite I] : IsCoherent (freeP A n I) := by
  classical
  have := Fintype.ofFinite I
  refine ⟨inferInstanceAs (SheafOfModules.free I).IsQuasicoherent, fun U _ => ?_⟩
  have := finite_sections_unit (A := A) (n := n) U
  let ιL : I → Γ(𝟙_ (projectiveSpace A n).Modules, U)
      →ₗ[Γ(projectiveSpace A n, U)] Γ(freeP A n I, U) := fun i =>
    { toFun := (ιP i).app U
      map_add' := map_add _
      map_smul' := fun r x => Scheme.Modules.Hom.app_smul _ r x }
  let Φ : (I → Γ(𝟙_ (projectiveSpace A n).Modules, U))
      →ₗ[Γ(projectiveSpace A n, U)] Γ(freeP A n I, U) := ∑ i, (ιL i).comp (LinearMap.proj i)
  refine Module.Finite.of_surjective Φ fun x => ⟨fun i => (πP i).app U x, ?_⟩
  have h := congrArg (fun φ => Scheme.Modules.Hom.app φ U x)
    (free_total (A := A) (n := n) (I := I))
  simp only [sum_app_apply, Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app,
    ConcreteCategory.comp_apply, ConcreteCategory.id_apply] at h
  simp only [Φ, ιL, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    LinearMap.coe_mk, AddHom.coe_mk]
  exact h

variable [HasExt.{w'} (Sheaf (Opens.grothendieckTopology (projectiveSpace A n).toTopCat) AddCommGrpCat.{u})]

attribute [local instance] algebraOfOver

lemma H_twist_free_eq {I : Type u} [Fintype I] [DecidableEq I] (k : ℤ) (p : ℕ)
    (x : Sheaf.H.{w'} (modulesAb ((twistEquiv (A := A) (n := n) k).functor.obj (freeP A n I))) p) :
    x = ∑ i, H.linearMap A ((twistEquiv k).functor.map (ιP i)) p
      (H.linearMap A ((twistEquiv k).functor.map (πP i)) p x) := by
  conv_lhs => rw [← LinearMap.id_apply (R := A) x, ← H.linearMap_id, ← twist_total k]
  rw [H.linearMap_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [H.linearMap_comp, LinearMap.comp_apply]

def H_twistUnitEquiv (k : ℤ) (p : ℕ) :
    Sheaf.H.{w'} (modulesAb ((twistEquiv (A := A) (n := n) k).functor.obj
      (𝟙_ (projectiveSpace A n).Modules))) p ≃ₗ[A]
      Sheaf.H.{w'} (modulesAb (twistingSheaf (grading A n) k)) p :=
  H.linearEquivOfIso A (eqToIso (twistEquiv_obj k _) ≪≫ λ_ _) p

lemma finite_H_twist_free (I : Type u) [Finite I] (k : ℤ) (p : ℕ) :
    Module.Finite A (Sheaf.H.{w'}
      (modulesAb ((twistEquiv (A := A) (n := n) k).functor.obj (freeP A n I))) p) := by
  classical
  have := Fintype.ofFinite I
  have h1 : Module.Finite A (Sheaf.H.{w'} (modulesAb ((twistEquiv (A := A) (n := n) k).functor.obj
      (𝟙_ (projectiveSpace A n).Modules))) p) :=
    have := finite_H_twistingSheaf.{w'} (A := A) (n := n) k p
    Module.Finite.equiv (H_twistUnitEquiv (A := A) (n := n) k p).symm
  let Φ : (I → Sheaf.H.{w'} (modulesAb ((twistEquiv (A := A) (n := n) k).functor.obj
      (𝟙_ (projectiveSpace A n).Modules))) p) →ₗ[A]
      Sheaf.H.{w'} (modulesAb ((twistEquiv (A := A) (n := n) k).functor.obj (freeP A n I))) p :=
    ∑ i, (H.linearMap A ((twistEquiv k).functor.map (ιP i)) p).comp (LinearMap.proj i)
  refine Module.Finite.of_surjective Φ fun x => ⟨fun i =>
    H.linearMap A ((twistEquiv k).functor.map (πP i)) p x, ?_⟩
  conv_rhs => rw [H_twist_free_eq k p x]
  simp [Φ, LinearMap.sum_apply]

lemma subsingleton_H_twist_free (I : Type u) [Finite I] {k : ℤ} (hk : 0 ≤ k) {p : ℕ}
    (hp : 0 < p) : Subsingleton (Sheaf.H.{w'}
      (modulesAb ((twistEquiv (A := A) (n := n) k).functor.obj (freeP A n I))) p) := by
  classical
  have := Fintype.ofFinite I
  have h1 : Subsingleton (Sheaf.H.{w'} (modulesAb ((twistEquiv (A := A) (n := n) k).functor.obj
      (𝟙_ (projectiveSpace A n).Modules))) p) :=
    have := subsingleton_H_twistingSheaf.{w'} (A := A) (n := n) hk hp
    (H_twistUnitEquiv (A := A) (n := n) k p).toEquiv.subsingleton
  refine ⟨fun x y => ?_⟩
  rw [H_twist_free_eq k p x, H_twist_free_eq k p y]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Subsingleton.elim
    (H.linearMap A ((twistEquiv k).functor.map (πP i)) p x)
    (H.linearMap A ((twistEquiv k).functor.map (πP i)) p y)]

end ProjSpace

end

end GroundTheory.Arith.SchemeCoh
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits MonoidalCategory
  MvPolynomial

universe w' u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace ProjSpace

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {n : ℕ}
  [HasExt.{w'} (Sheaf (Opens.grothendieckTopology (projectiveSpace A n).toTopCat) AddCommGrpCat.{u})]

attribute [local instance] algebraOfOver

theorem serre_step (p : ℕ)
    (ih : ∀ R : (projectiveSpace A n).Modules, IsCoherent R →
      Module.Finite A (Sheaf.H.{w'} (modulesAb R) (p + 1)) ∧
      ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → Subsingleton (Sheaf.H.{w'} (modulesAb (twist R q)) (p + 1)))
    (G : (projectiveSpace A n).Modules) (hG : IsCoherent G) :
    Module.Finite A (Sheaf.H.{w'} (modulesAb G) p) ∧
      (0 < p → ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
        Subsingleton (Sheaf.H.{w'} (modulesAb (twist G q)) p)) := by
  have := hG.1
  obtain ⟨q₀, hq₀⟩ := exists_generatingSections_twist G hG
  obtain ⟨σ, hσ⟩ := hq₀ q₀ le_rfl
  have : Finite σ.I := hσ.finite
  let ψ : freeP A n σ.I ⟶ twist G q₀ := σ.π
  have : Epi ψ := σ.epi
  have hK : IsCoherent (kernel ψ) := isCoherent_kernel ψ (isCoherent_freeP σ.I)
  let S : ShortComplex (projectiveSpace A n).Modules :=
    ShortComplex.mk (kernel.ι ψ) ψ (kernel.condition ψ)
  have hS : S.ShortExact := ⟨S.exact_of_f_is_kernel (kernelIsKernel ψ)⟩
  have hSk : ∀ k : ℤ, (S.map (twistEquiv (A := A) (n := n) k).functor).ShortExact := fun k =>
    shortExact_tensorEquiv _ hS
  have eK : ∀ k : ℤ, (S.map (twistEquiv (A := A) (n := n) k).functor).X₁ ≅ twist (kernel ψ) k :=
    fun k => eqToIso (twistEquiv_obj k _)
  have eG : ∀ k : ℤ, (S.map (twistEquiv (A := A) (n := n) k).functor).X₃ ≅ twist G (q₀ + k) :=
    fun k => eqToIso (twistEquiv_obj k _) ≪≫ twistTwistIso G q₀ k
  constructor
  · have h1 : Module.Finite A (Sheaf.H.{w'}
        (modulesAb (S.map (twistEquiv (A := A) (n := n) (-q₀)).functor).X₁) (p + 1)) :=
      have := (ih _ (isCoherent_twist hK (-q₀))).1
      Module.Finite.equiv (H.linearEquivOfIso A (eK (-q₀)) (p + 1)).symm
    have h2 : Module.Finite A (Sheaf.H.{w'}
        (modulesAb (S.map (twistEquiv (A := A) (n := n) (-q₀)).functor).X₂) p) :=
      finite_H_twist_free σ.I (-q₀) p
    have h3 := finite_H_X₃ A (hSk (-q₀)) p
    have e : (S.map (twistEquiv (A := A) (n := n) (-q₀)).functor).X₃ ≅ G :=
      eG (-q₀) ≪≫ eqToIso (congrArg (twist G) (add_neg_cancel (q₀ : ℤ))) ≪≫ twistZero G
    exact Module.Finite.equiv (H.linearEquivOfIso A e p)
  · intro hp
    obtain ⟨q₁, hq₁⟩ := (ih (kernel ψ) hK).2
    refine ⟨q₀ + q₁, fun q hq => ?_⟩
    have h1 : Subsingleton (Sheaf.H.{w'}
        (modulesAb (S.map (twistEquiv (A := A) (n := n) ((q - q₀ : ℕ) : ℤ)).functor).X₁) (p + 1)) :=
      have := hq₁ (q - q₀) (by omega)
      (H.linearEquivOfIso A (eK ((q - q₀ : ℕ) : ℤ)) (p + 1)).toEquiv.subsingleton
    have h2 : Subsingleton (Sheaf.H.{w'}
        (modulesAb (S.map (twistEquiv (A := A) (n := n) ((q - q₀ : ℕ) : ℤ)).functor).X₂) p) :=
      subsingleton_H_twist_free σ.I (Int.natCast_nonneg _) hp
    have h3 := subsingleton_H_X₃ (hSk ((q - q₀ : ℕ) : ℤ)) p
    have e : (S.map (twistEquiv (A := A) (n := n) ((q - q₀ : ℕ) : ℤ)).functor).X₃ ≅ twist G q :=
      eG _ ≪≫ eqToIso (congrArg (twist G) (by omega))
    exact (H.linearEquivOfIso A e p).symm.toEquiv.subsingleton

theorem serre_all (d : ℕ) : ∀ p : ℕ, n < p + d →
    ∀ G : (projectiveSpace A n).Modules, IsCoherent G →
      Module.Finite A (Sheaf.H.{w'} (modulesAb G) p) ∧
      (0 < p → ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
        Subsingleton (Sheaf.H.{w'} (modulesAb (twist G q)) p)) := by
  induction d with
  | zero =>
    intro p hp G hG
    have := hG.1
    have : Subsingleton (Sheaf.H.{w'} (modulesAb G) p) := subsingleton_H_of_lt G (by omega)
    exact ⟨Module.Finite.of_finite, fun _ =>
      ⟨0, fun q _ => subsingleton_H_of_lt (twist G q) (by omega)⟩⟩
  | succ d ih =>
    intro p hp G hG
    exact serre_step p (fun R hR => ⟨(ih (p + 1) (by omega) R hR).1,
      (ih (p + 1) (by omega) R hR).2 (Nat.succ_pos p)⟩) G hG

theorem finite_H (G : (projectiveSpace A n).Modules) (hG : IsCoherent G) (p : ℕ) :
    Module.Finite A (Sheaf.H.{w'} (modulesAb G) p) :=
  (serre_all (n + 1) p (by omega) G hG).1

theorem exists_subsingleton_H_twist (G : (projectiveSpace A n).Modules) (hG : IsCoherent G) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ p : ℕ, 0 < p →
      Subsingleton (Sheaf.H.{w'} (modulesAb (twist G q)) p) := by
  have h : ∀ p : ℕ, ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → 0 < p →
      Subsingleton (Sheaf.H.{w'} (modulesAb (twist G q)) p) := fun p => by
    rcases Nat.eq_zero_or_pos p with rfl | hp
    · exact ⟨0, fun _ _ h => absurd h (lt_irrefl 0)⟩
    · obtain ⟨q₀, hq₀⟩ := (serre_all (n + 1) p (by omega) G hG).2 hp
      exact ⟨q₀, fun q hq _ => hq₀ q hq⟩
  choose f hf using h
  refine ⟨∑ p ∈ Finset.range (n + 1), f p, fun q hq p hp => ?_⟩
  by_cases hpn : p ≤ n
  · exact hf p q (le_trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.2 (by omega))) hq) hp
  · have := hG.1
    exact subsingleton_H_of_lt (twist G q) (by omega)

end ProjSpace

end

end GroundTheory.Arith.SchemeCoh
end

section -- merged from GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.Immersion
section -- merged from GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.ImmersionProj
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits MonoidalCategory
  MvPolynomial
open GroundTheory.Arith.Etale (pullbackUnitApp pullbackUnitApp_res)

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace ProjScheme

variable {A : Type u} [CommRing A] {n : ℕ} {X : Scheme.{u}} (i : X ⟶ projectiveSpace A n)

abbrev secX {Y : Scheme.{u}} (F : Y.Modules) (W : Y.Opens) (m : Γ(F, W)) :
    ((preMod Y).obj F).obj (op W) := m

abbrev secΓ {Y : Scheme.{u}} (F : Y.Modules) (W : Y.Opens) (m : ((preMod Y).obj F).obj (op W)) :
    Γ(F, W) := m

def projFun (F : X.Modules) (k : ℤ) (V : (projectiveSpace A n).Opens) (m : Γ(F, i ⁻¹ᵁ V))
    (s : Γ(SchemeCoh.twistingSheaf (ProjSpace.grading A n) k, V)) :
    ((preMod X).obj (F ⊗ twistingSheaf i k)).obj (op (i ⁻¹ᵁ V)) :=
  (tensorToSheaf F (twistingSheaf i k)).app (op (i ⁻¹ᵁ V))
    (secX F _ m ⊗ₜ secX (twistingSheaf i k) _ (pullbackUnitApp i _ V s))

variable (F : X.Modules) (k : ℤ) (V : (projectiveSpace A n).Opens)

lemma projFun_add_left (m m' : Γ(F, i ⁻¹ᵁ V))
    (s : Γ(SchemeCoh.twistingSheaf (ProjSpace.grading A n) k, V)) :
    projFun i F k V (m + m') s = projFun i F k V m s + projFun i F k V m' s := by
  unfold projFun
  rw [show secX F _ (m + m') = secX F _ m + secX F _ m' from rfl, TensorProduct.add_tmul]
  exact map_add _ _ _

lemma projFun_add_right (m : Γ(F, i ⁻¹ᵁ V))
    (s s' : Γ(SchemeCoh.twistingSheaf (ProjSpace.grading A n) k, V)) :
    projFun i F k V m (s + s') = projFun i F k V m s + projFun i F k V m s' := by
  unfold projFun
  rw [map_add (f := _), show secX (twistingSheaf i k) _ (pullbackUnitApp i _ V s + pullbackUnitApp i _ V s') =
    secX (twistingSheaf i k) _ (pullbackUnitApp i _ V s) +
      secX (twistingSheaf i k) _ (pullbackUnitApp i _ V s') from rfl, TensorProduct.tmul_add]
  exact map_add _ _ _

lemma projFun_smul_left (r : ringOn _ V) (m : Γ(F, i ⁻¹ᵁ V))
    (s : Γ(SchemeCoh.twistingSheaf (ProjSpace.grading A n) k, V)) :
    projFun i F k V (secΓ F _ (appR i V r • secX F _ m)) s =
      appR i V r • projFun i F k V m s := by
  let a : X.sheaf.obj.obj (op (i ⁻¹ᵁ V)) := i.app V r
  unfold projFun
  rw [show secX F _ (secΓ F _ (appR i V r • secX F _ m)) =
    a • secX F _ m from rfl, ← TensorProduct.smul_tmul' a]
  exact map_smul _ a _

lemma projFun_smul_right (r : ringOn _ V) (m : Γ(F, i ⁻¹ᵁ V))
    (s : Γ(SchemeCoh.twistingSheaf (ProjSpace.grading A n) k, V)) :
    projFun i F k V m (secΓ (SchemeCoh.twistingSheaf (ProjSpace.grading A n) k) _
        (r • secX (SchemeCoh.twistingSheaf (ProjSpace.grading A n) k) _ s)) =
      appR i V r • projFun i F k V m s := by
  let a : X.sheaf.obj.obj (op (i ⁻¹ᵁ V)) := i.app V r
  unfold projFun
  rw [show secX (twistingSheaf i k) _ (pullbackUnitApp i _ V (secΓ (SchemeCoh.twistingSheaf
    (ProjSpace.grading A n) k) _ (r • secX (SchemeCoh.twistingSheaf (ProjSpace.grading A n) k)
      _ s))) = a • secX (twistingSheaf i k) _ (pullbackUnitApp i _ V s) from
    pullbackUnitApp_smul i _ V r s, TensorProduct.tmul_smul a]
  exact map_smul _ a _

def projLin :
    ((preMod _).obj ((Scheme.Modules.pushforward i).obj F)).obj (op V) →ₗ[Γ(projectiveSpace A n, V)]
      ((preMod _).obj (SchemeCoh.twistingSheaf (ProjSpace.grading A n) k)).obj (op V)
        →ₗ[Γ(projectiveSpace A n, V)]
      ((preMod _).obj ((Scheme.Modules.pushforward i).obj (twist i F k))).obj (op V) :=
  LinearMap.mk₂ Γ(projectiveSpace A n, V) (fun m s => projFun i F k V m s)
    (fun m m' s => projFun_add_left i F k V m m' s)
    (fun r m s => projFun_smul_left i F k V r m s)
    (fun m s s' => projFun_add_right i F k V m s s')
    (fun r m s => projFun_smul_right i F k V r m s)

def projPre : (preMod _).obj ((Scheme.Modules.pushforward i).obj F) ⊗
      (preMod _).obj (SchemeCoh.twistingSheaf (ProjSpace.grading A n) k) ⟶
    (preMod _).obj ((Scheme.Modules.pushforward i).obj (twist i F k)) :=
  PresheafOfModulesOfCommRing.homMk
    (R := (projectiveSpace A n).sheaf.obj)
    (fun V => ModuleCat.ofHom (TensorProduct.lift (projLin i F k V.unop)))
    (fun {V V'} f => ModuleCat.MonoidalCategory.tensor_ext fun m s => by
      have e1 := pullbackUnitApp_res i (SchemeCoh.twistingSheaf (ProjSpace.grading A n) k) f.unop s
      have e2 := PresheafOfModules.naturality_apply (tensorToSheaf F (twistingSheaf i k))
        ((Opens.map i.base).map f.unop).op
        (secX F _ m ⊗ₜ secX (twistingSheaf i k) _ (pullbackUnitApp i _ V.unop s))
      change projFun i F k V'.unop (F.presheaf.map ((Opens.map i.base).map f.unop).op m)
          ((SchemeCoh.twistingSheaf (ProjSpace.grading A n) k).presheaf.map f.unop.op s) =
        ((preMod X).obj (F ⊗ twistingSheaf i k)).map ((Opens.map i.base).map f.unop).op
          (projFun i F k V.unop m s)
      unfold projFun
      rw [e1]
      exact e2)

def projectionMap :
    ProjSpace.twist ((Scheme.Modules.pushforward i).obj F) k ⟶
      (Scheme.Modules.pushforward i).obj (twist i F k) :=
  tensorLift (projPre i F k)

lemma projectionMap_tensorBasisMap (j : Fin (n + 1)) {V : (projectiveSpace A n).Opens}
    (hV : V ≤ ProjSpace.stdOpen A n j) (m : Γ((Scheme.Modules.pushforward i).obj F, V)) :
    (projectionMap i F k).app V (tensorBasisMap ((Scheme.Modules.pushforward i).obj F)
        (SchemeCoh.twistingSheaf (ProjSpace.grading A n) k)
        (ProjTwist.upow (ProjSpace.grading A n) (ProjSpace.X_mem j) k) hV m) =
      tensorBasisMap F (twistingSheaf i k)
        (pullbackUnitApp i _ (ProjSpace.stdOpen A n j)
          (ProjTwist.upow (ProjSpace.grading A n) (ProjSpace.X_mem j) k))
        ((Opens.map i.base).monotone hV) (secΓ F _ m) := by
  have h := congrArg (fun φ => (PresheafOfModules.Hom.app φ (op V)).hom
      ((show ((preMod _).obj ((Scheme.Modules.pushforward i).obj F)).obj (op V) from m) ⊗ₜ
        resM ((preMod _).obj (SchemeCoh.twistingSheaf (ProjSpace.grading A n) k)) hV
          (ProjTwist.upow (ProjSpace.grading A n) (ProjSpace.X_mem j) k) :
        ((preMod _).obj ((Scheme.Modules.pushforward i).obj F) ⊗
          (preMod _).obj (SchemeCoh.twistingSheaf (ProjSpace.grading A n) k)).obj (op V)))
    (tensorToSheaf_tensorLift (projPre i F k))
  refine h.trans ?_
  change projFun i F k V m (resM _ hV (ProjTwist.upow (ProjSpace.grading A n)
    (ProjSpace.X_mem j) k)) = _
  unfold projFun
  have e := pullbackUnitApp_res i (SchemeCoh.twistingSheaf (ProjSpace.grading A n) k) (homOfLE hV)
    (ProjTwist.upow (ProjSpace.grading A n) (ProjSpace.X_mem j) k)
  exact congrArg (fun y => (tensorToSheaf F (twistingSheaf i k)).app (op (i ⁻¹ᵁ V))
    (secX F _ m ⊗ₜ secX (twistingSheaf i k) _ y)) e

instance isIso_projectionMap : IsIso (projectionMap i F k) := by
  apply isIso_of_locally_bijective
  intro x
  obtain ⟨j, hj⟩ : ∃ j, x ∈ ProjSpace.stdOpen A n j :=
    Opens.mem_iSup.1 (by rw [ProjSpace.iSup_stdOpen]; trivial)
  refine ⟨ProjSpace.stdOpen A n j, hj, fun V hV => ?_⟩
  have hb₁ := tensorBasisMap_bijective (M := (Scheme.Modules.pushforward i).obj F)
    (ProjTwist.isBasisOn_upow (ProjSpace.grading A n) (ProjSpace.X_mem j) k) hV
  have hb₂ := tensorBasisMap_bijective (M := F)
    (isBasisOn_pullbackUnitApp i
      (ProjTwist.isBasisOn_upow (ProjSpace.grading A n) (ProjSpace.X_mem j) k))
    ((Opens.map i.base).monotone hV)
  have comm : (fun m => (projectionMap i F k).app V (tensorBasisMap
      ((Scheme.Modules.pushforward i).obj F) (SchemeCoh.twistingSheaf (ProjSpace.grading A n) k)
      (ProjTwist.upow (ProjSpace.grading A n) (ProjSpace.X_mem j) k) hV m)) =
      (fun m => tensorBasisMap F (twistingSheaf i k)
        (pullbackUnitApp i _ (ProjSpace.stdOpen A n j)
          (ProjTwist.upow (ProjSpace.grading A n) (ProjSpace.X_mem j) k))
        ((Opens.map i.base).monotone hV) (secΓ F _ m)) :=
    funext fun m => projectionMap_tensorBasisMap i F k j hV m
  have h2 : Function.Bijective (fun m => (projectionMap i F k).app V (tensorBasisMap
      ((Scheme.Modules.pushforward i).obj F) (SchemeCoh.twistingSheaf (ProjSpace.grading A n) k)
      (ProjTwist.upow (ProjSpace.grading A n) (ProjSpace.X_mem j) k) hV m)) := by
    rw [comm]
    exact hb₂
  exact (Function.Bijective.of_comp_iff _ hb₁).1 h2

def pushforwardTwistIso' :
    ProjSpace.twist ((Scheme.Modules.pushforward i).obj F) k ≅
      (Scheme.Modules.pushforward i).obj (twist i F k) :=
  asIso (projectionMap i F k)

end ProjScheme

end

end GroundTheory.Arith.SchemeCoh
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits MonoidalCategory
  MvPolynomial

universe w' u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace ProjScheme

variable {A : Type u} [CommRing A] {n : ℕ} {X : Scheme.{u}} (i : X ⟶ projectiveSpace A n)
  [IsClosedImmersion i]

instance isQuasicoherent_pushforward (F : X.Modules) [F.IsQuasicoherent] :
    ((Scheme.Modules.pushforward i).obj F).IsQuasicoherent :=
  isQuasicoherent_pushforward_of_isAffineHom i F

theorem isCoherent_pushforward {F : X.Modules} (hF : IsCoherent F) :
    IsCoherent ((Scheme.Modules.pushforward i).obj F) :=
  isCoherent_pushforward_of_isClosedImmersion i hF

omit [IsClosedImmersion i] in
theorem isInvertibleSheaf_twistingSheaf (k : ℤ) : IsInvertibleSheaf (twistingSheaf i k) := by
  intro x
  obtain ⟨j, hj⟩ : ∃ j, i.base x ∈ ProjSpace.stdOpen A n j :=
    Opens.mem_iSup.1 (by rw [ProjSpace.iSup_stdOpen]; trivial)
  exact ⟨i ⁻¹ᵁ ProjSpace.stdOpen A n j, hj, _,
    isBasisOn_pullbackUnitApp i (ProjTwist.isBasisOn_upow _ (ProjSpace.X_mem j) k)⟩

instance isQuasicoherent_twist (F : X.Modules) [F.IsQuasicoherent] (k : ℤ) :
    (twist i F k).IsQuasicoherent :=
  isQuasicoherent_tensor_of_invertible F (isInvertibleSheaf_twistingSheaf i k)

def pushforwardTwistIso (F : X.Modules) (k : ℤ) :
    ProjSpace.twist ((Scheme.Modules.pushforward i).obj F) k ≅
      (Scheme.Modules.pushforward i).obj (twist i F k) :=
  pushforwardTwistIso' i F k

theorem exists_generatingSections_of_pushforward (M : X.Modules) [M.IsQuasicoherent]
    (h : ∃ σ : ((Scheme.Modules.pushforward i).obj M).GeneratingSections, σ.IsFiniteType) :
    ∃ σ : M.GeneratingSections, σ.IsFiniteType :=
  exists_generatingSections_of_pushforward_of_isAffineHom i M h

variable [X.Over (Spec (.of A))] [i.IsOver (Spec (.of A))]
  [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u})]
  [HasExt.{w'} (Sheaf (Opens.grothendieckTopology (projectiveSpace A n).toTopCat) AddCommGrpCat.{u})]

attribute [local instance] algebraOfOver

def HLinearEquivPushforward (F : X.Modules) [F.IsQuasicoherent] (p : ℕ) :
    Sheaf.H.{w'} (modulesAb F) p ≃ₗ[A]
      Sheaf.H.{w'} (modulesAb ((Scheme.Modules.pushforward i).obj F)) p :=
  have hUP : ⨆ j, ProjSpace.stdOpen A n j = ⊤ := ProjSpace.iSup_stdOpen
  have hUPaff : ∀ (m : ℕ) (t : Fin (m + 1) → Fin (n + 1)),
      IsAffineOpen (⨅ a, ProjSpace.stdOpen A n (t a)) := fun _ t => by
    rw [← inter_eq_iInf]
    exact ProjSpace.isAffineOpen_inter t
  have hUX : ⨆ j, i ⁻¹ᵁ ProjSpace.stdOpen A n j = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, ProjSpace.iSup_stdOpen]
    rfl
  have hUXaff : ∀ (m : ℕ) (t : Fin (m + 1) → Fin (n + 1)),
      IsAffineOpen (⨅ a, i ⁻¹ᵁ ProjSpace.stdOpen A n (t a)) := fun _ t => by
    have h := preimage_inter i (ProjSpace.stdOpen A n) t
    rw [← inter_eq_iInf (fun j => i ⁻¹ᵁ ProjSpace.stdOpen A n j) t, ← h]
    exact (ProjSpace.isAffineOpen_inter t).preimage i
  (cechHLinearEquivH (fun j => i ⁻¹ᵁ ProjSpace.stdOpen A n j) hUX hUXaff A F p).symm ≪≫ₗ
    (cechHPushforwardLinearEquiv i A F (ProjSpace.stdOpen A n) p).symm ≪≫ₗ
    cechHLinearEquivH (ProjSpace.stdOpen A n) hUP hUPaff A _ p

end ProjScheme

end

end GroundTheory.Arith.SchemeCoh
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits MonoidalCategory
  MvPolynomial

universe w' u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace ProjScheme

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {n : ℕ} {X : Scheme.{u}}
  [X.Over (Spec (.of A))] (i : X ⟶ projectiveSpace A n) [IsClosedImmersion i]
  [i.IsOver (Spec (.of A))]

omit [IsNoetherianRing A] [X.Over (Spec (.of A))] [i.IsOver (Spec (.of A))] in
theorem exists_generatingSections_twist (F : X.Modules) (hF : IsCoherent F) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∃ σ : (twist i F q).GeneratingSections, σ.IsFiniteType := by
  have := hF.1
  obtain ⟨q₀, hq₀⟩ := ProjSpace.exists_generatingSections_twist _ (isCoherent_pushforward i hF)
  refine ⟨q₀, fun q hq => ?_⟩
  obtain ⟨σ, hσ⟩ := hq₀ q hq
  exact exists_generatingSections_of_pushforward i (twist i F q)
    (exists_generatingSections_of_iso (pushforwardTwistIso i F q) ⟨σ, hσ⟩)

variable [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u})]
  [HasExt.{w'} (Sheaf (Opens.grothendieckTopology (projectiveSpace A n).toTopCat) AddCommGrpCat.{u})]

attribute [local instance] algebraOfOver

include i in
theorem finite_H (F : X.Modules) (hF : IsCoherent F) (p : ℕ) :
    Module.Finite A (Sheaf.H.{w'} (modulesAb F) p) := by
  letI := hF.1
  letI := ProjSpace.finite_H.{w'} _ (isCoherent_pushforward i hF) p
  exact Module.Finite.equiv (HLinearEquivPushforward.{w'} i F p).symm

theorem exists_subsingleton_H_twist (F : X.Modules) (hF : IsCoherent F) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ p : ℕ, 0 < p →
      Subsingleton (Sheaf.H.{w'} (modulesAb (twist i F q)) p) := by
  letI := hF.1
  obtain ⟨q₀, hq₀⟩ := ProjSpace.exists_subsingleton_H_twist.{w'} _ (isCoherent_pushforward i hF)
  refine ⟨q₀, fun q hq p hp => ?_⟩
  have h₁ := hq₀ q hq p hp
  have e₁ := HLinearEquivPushforward.{w'} i (twist i F q) p
  have e₂ : Sheaf.H.{w'} (modulesAb (ProjSpace.twist ((Scheme.Modules.pushforward i).obj F) q)) p ≃+
      Sheaf.H.{w'} (modulesAb ((Scheme.Modules.pushforward i).obj (twist i F q))) p :=
    ((H.moduleFunctor.{w'} A p).mapIso (pushforwardTwistIso i F q)).toLinearEquiv.toAddEquiv
  exact e₁.toEquiv.subsingleton_congr.2 (e₂.toEquiv.subsingleton_congr.1 h₁)

end ProjScheme

end

end GroundTheory.Arith.SchemeCoh
