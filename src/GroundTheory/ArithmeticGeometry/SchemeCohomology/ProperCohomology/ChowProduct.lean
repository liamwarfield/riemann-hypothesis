module

public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.TwistingSheafCore
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.QcohLocal

@[expose] public section

section -- merged from GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ChowProduct
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Limits MvPolynomial

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace ProjSpace

variable (A : Type u) [CommRing A]

lemma bijective_algebraMap_gradeZero (n : ℕ) :
    Function.Bijective (algebraMap A (grading A n 0)) := by
  refine ⟨fun a b h => ?_, ?_⟩
  · have h' := congrArg Subtype.val h
    rw [SetLike.GradeZero.coe_algebraMap, SetLike.GradeZero.coe_algebraMap,
      MvPolynomial.algebraMap_eq] at h'
    exact MvPolynomial.C_injective _ _ h'
  · rintro ⟨p, hp⟩
    refine ⟨AddMonoidAlgebra.coeff p 0, Subtype.ext ?_⟩
    rw [SetLike.GradeZero.coe_algebraMap, MvPolynomial.algebraMap_eq]
    by_cases h0 : p = 0
    · subst h0
      simp
    · exact (totalDegree_eq_zero_iff_eq_C.1
        (((mem_homogeneousSubmodule _ _).1 hp).totalDegree h0)).symm

instance isIso_SpecMap_gradeZero (n : ℕ) :
    IsIso (Spec.map (CommRingCat.ofHom (algebraMap A (grading A n 0)))) := by
  have : IsIso (CommRingCat.ofHom (algebraMap A (grading A n 0))) :=
    (ConcreteCategory.isIso_iff_bijective _).2 (bijective_algebraMap_gradeZero A n)
  infer_instance

instance isProper_toSpecBase (n : ℕ) : IsProper (toSpecBase A n) := by
  dsimp only [toSpecBase]
  infer_instance

def multiProj : (k : ℕ) → (Fin (k + 1) → ℕ) → Σ P : Scheme.{u}, P ⟶ Spec (.of A)
  | 0, n => ⟨projectiveSpace A (n 0), toSpecBase A (n 0)⟩
  | k + 1, n => ⟨pullback (toSpecBase A (n 0)) (multiProj k (Fin.tail n)).2,
      pullback.fst _ _ ≫ toSpecBase A (n 0)⟩

abbrev MP (k : ℕ) (n : Fin (k + 1) → ℕ) : Scheme.{u} := (multiProj A k n).1

abbrev mpStr (k : ℕ) (n : Fin (k + 1) → ℕ) : MP A k n ⟶ Spec (.of A) := (multiProj A k n).2

instance isProper_mpStr : (k : ℕ) → (n : Fin (k + 1) → ℕ) → IsProper (mpStr A k n)
  | 0, n => isProper_toSpecBase A (n 0)
  | k + 1, n => by
    have := isProper_mpStr k (Fin.tail n)
    change IsProper (pullback.fst (toSpecBase A (n 0)) (mpStr A k (Fin.tail n)) ≫ _)
    infer_instance

def pr : (k : ℕ) → (n : Fin (k + 1) → ℕ) → (i : Fin (k + 1)) →
    MP A k n ⟶ projectiveSpace A (n i)
  | 0, n, i => Fin.cases (motive := fun i => MP A 0 n ⟶ projectiveSpace A (n i)) (𝟙 _)
      (fun j => j.elim0) i
  | k + 1, n, i => Fin.cases (motive := fun i => MP A (k + 1) n ⟶ projectiveSpace A (n i))
      (pullback.fst (toSpecBase A (n 0)) (mpStr A k (Fin.tail n)))
      (fun j => pullback.snd (toSpecBase A (n 0)) (mpStr A k (Fin.tail n)) ≫ pr k (Fin.tail n) j) i

lemma pr_toSpecBase : (k : ℕ) → (n : Fin (k + 1) → ℕ) → (i : Fin (k + 1)) →
    pr A k n i ≫ toSpecBase A (n i) = mpStr A k n
  | 0, n, i => by
    induction i using Fin.cases with
    | zero => exact Category.id_comp _
    | succ j => exact j.elim0
  | k + 1, n, i => by
    induction i using Fin.cases with
    | zero => rfl
    | succ j =>
      change (pullback.snd _ _ ≫ pr A k (Fin.tail n) j) ≫ toSpecBase A (Fin.tail n j) = _
      rw [Category.assoc, pr_toSpecBase k (Fin.tail n) j, ← pullback.condition]
      rfl

variable {A}

@[simp] lemma pr_zero_zero (n : Fin 1 → ℕ) : pr A 0 n 0 = 𝟙 _ := rfl

@[simp] lemma pr_succ_succ (k : ℕ) (n : Fin (k + 2) → ℕ) (j : Fin (k + 1)) :
    pr A (k + 1) n j.succ =
      pullback.snd (toSpecBase A (n 0)) (mpStr A k (Fin.tail n)) ≫ pr A k (Fin.tail n) j := rfl

def liftAux : (k : ℕ) → (n : Fin (k + 1) → ℕ) → {T : Scheme.{u}} → (t : T ⟶ Spec (.of A)) →
    (a : ∀ i, T ⟶ projectiveSpace A (n i)) → (∀ i, a i ≫ toSpecBase A (n i) = t) →
    {f : T ⟶ MP A k n // f ≫ mpStr A k n = t}
  | 0, _, _, _, a, ha => ⟨a 0, ha 0⟩
  | k + 1, n, _, t, a, ha =>
    ⟨pullback.lift (a 0) (liftAux k (Fin.tail n) t (fun j => a j.succ) (fun j => ha j.succ)).1
      (by rw [ha 0]; exact (liftAux k (Fin.tail n) t _ _).2.symm), by
      change pullback.lift _ _ _ ≫ pullback.fst _ _ ≫ _ = _
      rw [pullback.lift_fst_assoc, ha 0]⟩

def lift (k : ℕ) (n : Fin (k + 1) → ℕ) {T : Scheme.{u}} (t : T ⟶ Spec (.of A))
    (a : ∀ i, T ⟶ projectiveSpace A (n i)) (ha : ∀ i, a i ≫ toSpecBase A (n i) = t) :
    T ⟶ MP A k n :=
  (liftAux k n t a ha).1

lemma lift_mpStr (k : ℕ) (n : Fin (k + 1) → ℕ) {T : Scheme.{u}} (t : T ⟶ Spec (.of A))
    (a : ∀ i, T ⟶ projectiveSpace A (n i)) (ha : ∀ i, a i ≫ toSpecBase A (n i) = t) :
    lift k n t a ha ≫ mpStr A k n = t :=
  (liftAux k n t a ha).2

lemma lift_pr : (k : ℕ) → (n : Fin (k + 1) → ℕ) → {T : Scheme.{u}} → (t : T ⟶ Spec (.of A)) →
    (a : ∀ i, T ⟶ projectiveSpace A (n i)) → (ha : ∀ i, a i ≫ toSpecBase A (n i) = t) →
    (i : Fin (k + 1)) → lift k n t a ha ≫ pr A k n i = a i
  | 0, n, _, t, a, ha, i => by
    induction i using Fin.cases with
    | zero => exact Category.comp_id _
    | succ j => exact j.elim0
  | k + 1, n, _, t, a, ha, i => by
    induction i using Fin.cases with
    | zero => exact pullback.lift_fst _ _ _
    | succ j =>
      rw [pr_succ_succ]
      change pullback.lift _ _ _ ≫ pullback.snd _ _ ≫ pr A k (Fin.tail n) j = _
      rw [pullback.lift_snd_assoc]
      exact lift_pr k (Fin.tail n) t _ _ j

lemma hom_ext : (k : ℕ) → (n : Fin (k + 1) → ℕ) → {T : Scheme.{u}} → (f g : T ⟶ MP A k n) →
    (∀ i, f ≫ pr A k n i = g ≫ pr A k n i) → f = g := by
  intro k
  induction k with
  | zero =>
    intro n T f g h
    have h₀ : f ≫ 𝟙 (MP A 0 n) = g ≫ 𝟙 (MP A 0 n) := h 0
    exact (Category.comp_id f).symm.trans (h₀.trans (Category.comp_id g))
  | succ k ih =>
    intro n T f g h
    apply pullback.hom_ext
    · exact h 0
    · refine ih (Fin.tail n) _ _ fun j => ?_
      exact (Category.assoc _ _ _).trans ((h j.succ).trans (Category.assoc _ _ _).symm)

end ProjSpace

end

end GroundTheory.Arith.SchemeCoh
end

section -- merged from GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.Support
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits

universe u

noncomputable section

variable {X : Scheme.{u}}

def Scheme.Modules.SupportedIn (F : X.Modules) (T : Set X) : Prop :=
  ∀ U : X.Opens, Disjoint (U : Set X) T → ∀ s : Γ(F, U), s = 0

namespace Scheme.Modules.SupportedIn

lemma mono {F : X.Modules} {T T' : Set X} (h : Scheme.Modules.SupportedIn F T) (hT : T ⊆ T') :
    Scheme.Modules.SupportedIn F T' :=
  fun U hU s => h U (hU.mono_right hT) s

lemma of_iso {F G : X.Modules} (e : F ≅ G) {T : Set X} (h : Scheme.Modules.SupportedIn F T) :
    Scheme.Modules.SupportedIn G T := by
  intro U hU s
  have h1 : e.inv.app U s = 0 := h U hU _
  have h2 : e.hom.app U (e.inv.app U s) = s := by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, e.inv_hom_id]
    rfl
  rw [← h2, h1, map_zero]

lemma pushforward {Z : Scheme.{u}} (j : Z ⟶ X) {G : Z.Modules} {T' : Set Z}
    (h : Scheme.Modules.SupportedIn G T') :
    Scheme.Modules.SupportedIn ((Scheme.Modules.pushforward j).obj G) (j.base '' T') := by
  intro U hU s
  refine h (j ⁻¹ᵁ U) ?_ s
  rw [Set.disjoint_left]
  intro z hz hzT
  exact Set.disjoint_left.1 hU hz ⟨z, hzT, rfl⟩

end Scheme.Modules.SupportedIn

lemma isIso_of_bijective_app {F G : X.Modules} (φ : F ⟶ G)
    (h : ∀ U : X.Opens, Function.Bijective (φ.app U)) : IsIso φ := by
  have : IsIso ((Scheme.Modules.toPresheaf X).map φ) := by
    have : ∀ U : (X.Opens)ᵒᵖ, IsIso (((Scheme.Modules.toPresheaf X).map φ).app U) := fun U =>
      (ConcreteCategory.isIso_iff_bijective _).2 (h U.unop)
    exact NatIso.isIso_of_isIso_app _
  exact isIso_of_reflects_iso φ (Scheme.Modules.toPresheaf X)

lemma eq_zero_of_isZero {F : X.Modules} (hF : IsZero F) (U : X.Opens) (s : Γ(F, U)) : s = 0 := by
  have : (𝟙 F : F ⟶ F).app U s = (0 : F ⟶ F).app U s := by rw [hF.eq_of_src (𝟙 F) 0]
  simpa using this

section Restrict

variable {F G : X.Modules} (φ : F ⟶ G) (W : X.Opens)

lemma kernel_supportedIn (h : ∀ U : X.Opens, U ≤ W → Function.Bijective (φ.app U)) :
    Scheme.Modules.SupportedIn (kernel φ) (W : Set X)ᶜ := by
  intro U hU s
  have hUW : U ≤ W := fun x hx => by
    by_contra hxW
    exact Set.disjoint_left.1 hU hx hxW
  apply kernel_ι_app_injective φ U
  apply (h U hUW).1
  rw [map_zero, map_zero, ← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app,
    kernel.condition]
  rfl

lemma cokernel_supportedIn (h : ∀ U : X.Opens, U ≤ W → Function.Bijective (φ.app U)) :
    Scheme.Modules.SupportedIn (cokernel φ) (W : Set X)ᶜ := by
  intro U hU s
  have hUW : U ≤ W := fun x hx => by
    by_contra hxW
    exact Set.disjoint_left.1 hU hx hxW
  let R := Scheme.Modules.restrictFunctor W.ι
  have hφ : IsIso (R.map φ) := isIso_of_bijective_app _ fun V =>
    h _ ((W.ι.image_le_opensRange V).trans (by simp))
  have hZ : IsZero (R.obj (cokernel φ)) :=
    (isZero_cokernel_of_epi (R.map φ)).of_iso (PreservesCokernel.iso R φ)
  have hE : W.ι ''ᵁ (W.ι ⁻¹ᵁ U) = U := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.2 hUW
  have h0 : (cokernel φ).presheaf.map (eqToHom hE).op s = 0 :=
    eq_zero_of_isZero hZ (W.ι ⁻¹ᵁ U) _
  have hinv : (cokernel φ).presheaf.map (eqToHom hE.symm).op
      ((cokernel φ).presheaf.map (eqToHom hE).op s) = s := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, eqToHom_trans, eqToHom_refl,
      op_id, CategoryTheory.Functor.map_id]
    rfl
  rw [← hinv, h0, map_zero]

end Restrict

end

end GroundTheory.Arith.SchemeCoh
end
