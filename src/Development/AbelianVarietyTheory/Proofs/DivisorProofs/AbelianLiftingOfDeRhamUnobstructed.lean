module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareZeroLiftingOfNoetherianCase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGrpObjIsAbelianSchemeSmoothLiftNilpotent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionLiftSmoothNilpotentThickening
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtensionOverNormalQuasiProjectiveBase

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntermediateGrpPullbackAbelianScheme
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntermediateGrpPullbackAbelianScheme
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing GlobalTheory

attribute [local instance] Over.cartesianMonoidalCategory

open scoped CategoryTheory.Obj

namespace GlobalTheory.SqLift

theorem exists_intermediate_grpPullback : ∀ (R R₁ R₀ : Type) [CommRing R] [CommRing R₁] [CommRing R₀] (ρ : R →+* R₁) (π₁ : R₁ →+* R₀) (g : ℕ)
    (A₀ : Over (Sp R₀)) [GrpObj A₀] (A : Over (Sp R)) [GrpObj A] (i : A₀.left ⟶ A.left),
    IsGrpPullback A₀ A (spMap (π₁.comp ρ)) i → IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∃ (A₁ : Over (Sp R₁)) (_ : GrpObj A₁) (i₁ : A₀.left ⟶ A₁.left) (i₂ : A₁.left ⟶ A.left),
      IsGrpPullback A₀ A₁ (spMap π₁) i₁ ∧ IsGrpPullback A₁ A (spMap ρ) i₂ ∧ i₁ ≫ i₂ = i ∧ IsAbelianScheme A₁ ∧
      SmoothOfRelativeDimension g A₁.hom := by
  intro R R₁ R₀ _ _ _ ρ π₁ g A₀ _ A _ i h hA hg
  have e : spMap (π₁.comp ρ) = spMap π₁ ≫ spMap ρ := by
    simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  have h₂ := isGrpPullback_pullback A (spMap ρ)
  have hw : i ≫ A.hom = (A₀.hom ≫ spMap π₁) ≫ spMap ρ := by
    rw [h.1.w, e, Category.assoc]
  let i₁ : A₀.left ⟶ ((Over.pullback (spMap ρ)).obj A).left := h₂.1.lift i (A₀.hom ≫ spMap π₁) hw
  have c₁ : i₁ ≫ Limits.pullback.fst A.hom (spMap ρ) = i := h₂.1.lift_fst _ _ _
  have c₂ : i₁ ≫ ((Over.pullback (spMap ρ)).obj A).hom = A₀.hom ≫ spMap π₁ := h₂.1.lift_snd _ _ _
  have h₁ : IsGrpPullback A₀ ((Over.pullback (spMap ρ)).obj A) (spMap π₁) i₁ :=
    h₂.cancel (h.congr e c₁.symm) c₂
  refine ⟨(Over.pullback (spMap ρ)).obj A, Functor.grpObjObj, i₁, Limits.pullback.fst A.hom (spMap ρ), h₁, h₂, c₁,
    isAbelianScheme_pullback_obj (spMap ρ) A hA, ?_⟩
  exact (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback (IsPullback.of_hasPullback _ _) hg

end GlobalTheory.SqLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntermediateGrpPullbackAbelianSchemeStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_intermediate_grpPullback_abelianScheme : ∀ (R R₁ R₀ : Type) [CommRing R] [CommRing R₁] [CommRing R₀] (ρ : R →+* R₁) (π₁ : R₁ →+* R₀) (g : ℕ)
    (A₀ : Over (Sp R₀)) [GrpObj A₀] (A : Over (Sp R)) [GrpObj A] (i : A₀.left ⟶ A.left),
    IsGrpPullback A₀ A (spMap (π₁.comp ρ)) i → IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∃ (A₁ : Over (Sp R₁)) (_ : GrpObj A₁) (i₁ : A₀.left ⟶ A₁.left) (i₂ : A₁.left ⟶ A.left),
      IsGrpPullback A₀ A₁ (spMap π₁) i₁ ∧ IsGrpPullback A₁ A (spMap ρ) i₂ ∧ i₁ ≫ i₂ = i ∧ IsAbelianScheme A₁ ∧
      SmoothOfRelativeDimension g A₁.hom := by
  first | exact @GlobalTheory.SqLift.exists_intermediate_grpPullback | exact GlobalTheory.SqLift.exists_intermediate_grpPullback | (intros; apply GlobalTheory.SqLift.exists_intermediate_grpPullback <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrothendieckMessingLiftAbelianSchemeOfSquareZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrothendieckMessingLiftAbelianSchemeOfSquareZero
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqLift

theorem liftObj_sq : AbelianDeRham → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I → AbelianSchemeLifts.At hI π → LiftObj (divided₂ hI) π := by
  intro P R R₀ _ _ I hI π hπ hk H g A₀ _ A' _ i' h' hA' hg' F hF
  have hn : IsNilpotent (RingHom.ker π) := ⟨2, hk ▸ hI⟩
  obtain ⟨X, i, h, hX, hFil⟩ := H.exists_lift h' hA' hg' hF
  have hA₀ : IsAbelianScheme A₀ := PolPull.isAbelianScheme_of_isGrpPullback hA' h'
  have hg₀ : SmoothOfRelativeDimension g A₀.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h'.1 hg'
  obtain ⟨e, he, he₀⟩ := GlobalTheory.T.exists_section_lift_smooth_nilpotent_thickening R R₀ π hπ hn X A₀ i h hX (1 : Over.mk (𝟙 (Sp R₀)) ⟶ A₀).left
    (Over.w (1 : Over.mk (𝟙 (Sp R₀)) ⟶ A₀))
  have w : ((fst A₀ A₀).left ≫ i) ≫ X.hom = ((snd A₀ A₀).left ≫ i) ≫ X.hom := by
    rw [Category.assoc, Category.assoc, h.w, Over.w_assoc, Over.w_assoc]
  have hl₁ : (Limits.pullback.lift _ _ w : (A₀ ⊗ A₀).left ⟶ (X ⊗ X).left) ≫ (fst X X).left
      = (fst A₀ A₀).left ≫ i := Limits.pullback.lift_fst _ _ _
  have hl₂ : (Limits.pullback.lift _ _ w : (A₀ ⊗ A₀).left ⟶ (X ⊗ X).left) ≫ (snd X X).left
      = (snd A₀ A₀).left ≫ i := Limits.pullback.lift_snd _ _ _
  obtain ⟨m, hm⟩ := GlobalTheory.T.exists_lift_shearMap_squareZero_abelianSchemes R R₀ I hI π hπ hk H g g A₀ A₀ A' A' i' i' h' h' hA' hA' hg' hg' X X i i h h hX hX
    e e he he he₀ he₀ _ hl₁ hl₂ (𝟙 A₀) (fun d hd ↦ by rw [push_id]; exact hd)
  have hμ : (fst A₀ A₀ ≫ 𝟙 A₀) * snd A₀ A₀ = μ[A₀] := by
    rw [Category.comp_id, Hom.mul_def, lift_fst_snd, Category.id_comp]
  rw [hμ] at hm
  obtain ⟨_, hp, hab⟩ := GlobalTheory.T.exists_grpObj_isAbelianScheme_smoothLift_nilpotent R R₀ π hπ hn A₀ hA₀ X i h hX e he he₀ _ hl₁ hl₂ m hm
  have hg : SmoothOfRelativeDimension g X.hom := GlobalTheory.T.smoothOfRelativeDimension_of_nilpotent_reduction R R₀ π hπ hn g X A₀ i h hX hg₀
  exact ⟨X, _, i, hp, hab, hg, (schemeFil_eq_liftFil _ hp (P.1 R X g hab hg).1).symm.trans hFil⟩

end GlobalTheory.SqLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrothendieckMessingLiftAbelianSchemeOfSquareZeroStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.grothendieckMessingLiftAbelianScheme_of_squareZero : AbelianDeRham → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I → AbelianSchemeLifts.At hI π → LiftObj (divided₂ hI) π := by
  first | exact @GlobalTheory.SqLift.liftObj_sq | exact GlobalTheory.SqLift.liftObj_sq | (intros; apply GlobalTheory.SqLift.liftObj_sq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftAbelianSchemeAlongSquareZeroFactorization
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupSchemeDividedPowerLiftTower
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupSchemeDividedPowerLiftTower
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SqLift

theorem dual_eq_sum_of_ker {R R₁ : Type} [CommRing R] [CommRing R₁] (ρ : R →+* R₁) {P : Type*}
    [AddCommGroup P] [Module R P] [Module.Finite R P] [Module.Projective R P] (x : Module.Dual R P)
    (hx : ∀ c, ρ (x c) = 0) :
    ∃ (n : ℕ) (j : Fin n → R) (d : Fin n → Module.Dual R P), (∀ k, ρ (j k) = 0) ∧
      x = ∑ k, j k • d k := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R P
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  refine ⟨n, fun k ↦ x (f (Pi.single k 1)), fun k ↦ (LinearMap.proj k) ∘ₗ s, fun k ↦ hx _, ?_⟩
  ext c
  have e1 : s c = ∑ k, s c k • (Pi.single k (1 : R) : Fin n → R) := by
    ext i; simp [Finset.sum_apply, Pi.single_apply]
  have e2 : x c = x (f (s c)) := by rw [← LinearMap.comp_apply f s, hs, LinearMap.id_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e2, e1, map_sum, map_sum]
  simp [mul_comm]

theorem isAdmissible_reduce : AbelianDeRham → ∀ (R R₁ R₀ : Type) [CommRing R] [CommRing R₁] [CommRing R₀] (I J : Ideal R) (I₁ : Ideal R₁) (κ : DividedPowers I) (π : R →+* R₀)
    (hJ : J ^ 2 = 0) (ρ : R →+* R₁) (κ₁ : DividedPowers I₁) (π₁ : R₁ →+* R₀), IsStep κ π hJ ρ κ₁ π₁ →
    ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A₁ : Over (Sp R₁)) [GrpObj A₁] (A : Over (Sp R)) [GrpObj A]
      (i₁ : A₀.left ⟶ A₁.left) (i₂ : A₁.left ⟶ A.left) (i : A₀.left ⟶ A.left)
      (h₁ : IsGrpPullback A₀ A₁ (spMap π₁) i₁) (h₂ : IsGrpPullback A₁ A (spMap ρ) i₂) (h : IsGrpPullback A₀ A (spMap π) i),
      i₁ ≫ i₂ = i → IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ F : Submodule R (HdR A), IsAdmissible h F → ∃ F₁ : Submodule R₁ (HdR A₁), IsAdmissible h₁ F₁ ∧
      ∀ y : HdR A₁, y ∈ F₁ ↔ ∃ x ∈ F, (redMor h₂).Corr x y := by
  intro P R R₁ R₀ _ _ _ I J I₁ κ π hJ ρ κ₁ π₁ hs g A₀ _ A₁ _ A _ i₁ i₂ i h₁ h₂ h hi hA hg F hF
  obtain ⟨PF, -, PB, -, -⟩ := P
  letI : Algebra R R₁ := ρ.toAlgebra
  have hbc : (AbelianDeRham.bcMor h₂).IsBC := (PB R A g hA hg R₁ A₁ i₂ h₂).1
  obtain ⟨hfin, hproj, -⟩ := PF.prim hA hg

  have hPs : Function.Surjective (redMor h₂).pull := by
    intro c₁
    obtain ⟨z, rfl⟩ := hbc.2 c₁
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, by rw [map_zero, map_zero]⟩
    | tmul r c =>
      obtain ⟨r', rfl⟩ := hs.surj r
      exact ⟨r' • c, by rw [liftSemi_tmul, LinearMap.map_smulₛₗ]⟩
    | add x y hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [map_add (f := _), map_add (f := _), ha, hb]⟩
  have hex : ∀ x : HdR A, ∃ y : HdR A₁, (redMor h₂).Corr x y := fun x ↦ hbc.exists x
  have huniq : ∀ {x : HdR A} {y y' : HdR A₁}, (redMor h₂).Corr x y → (redMor h₂).Corr x y' → y = y' := by
    intro x y y' e e'
    refine LinearMap.ext fun c₁ ↦ ?_
    obtain ⟨c, rfl⟩ := hPs c₁
    rw [e c, e' c]
  have hlift : ∀ y : HdR A₁, ∃ x : HdR A, (redMor h₂).Corr x y := by
    intro y
    let l : primDR A →ₗ[R] R₁ :=
      { toFun c := y ((redMor h₂).pull c)
        map_add' := by simp
        map_smul' r c := by rw [LinearMap.map_smulₛₗ, map_smul]; rfl }
    obtain ⟨x, hx⟩ := Module.projective_lifting_property (Algebra.linearMap R R₁) l hs.surj
    exact ⟨x, fun c ↦ (LinearMap.congr_fun hx c).symm⟩
  let S : Submodule R (HdR A) → Submodule R₁ (HdR A₁) := fun F ↦
    { carrier := {y | ∃ x ∈ F, (redMor h₂).Corr x y}
      add_mem' := by
        rintro a b ⟨x, hx, ex⟩ ⟨x', hx', ex'⟩
        exact ⟨x + x', F.add_mem hx hx', fun c ↦ by simp [ex c, ex' c]⟩
      zero_mem' := ⟨0, F.zero_mem, fun c ↦ by simp⟩
      smul_mem' := by
        rintro r₁ y ⟨x, hx, ex⟩
        obtain ⟨r, rfl⟩ := hs.surj r₁
        exact ⟨r • x, F.smul_mem r hx, fun c ↦ by simp [ex c]⟩ }
  have comp : ∀ c, (redMor h₁).pull ((redMor h₂).pull c) = (redMor h).pull c :=
    fun c ↦ GrpMor.pull_pull (redMor h₂) (redMor h₁) (redMor h) (fun r ↦ RingHom.congr_fun hs.comp r) hi c
  obtain ⟨⟨N, hN⟩, hFil⟩ := hF
  refine ⟨S F, ⟨⟨S N, ⟨?_, ?_⟩⟩, fun y ↦ ?_⟩, fun y ↦ Iff.rfl⟩
  · refine Submodule.disjoint_def.2 fun y ⟨f, hf, ef⟩ ⟨n, hn, en⟩ ↦ ?_
    have hx : ∀ c, ρ ((f - n) c) = 0 := fun c ↦ by
      rw [LinearMap.sub_apply, map_sub, ← ef c, ← en c, sub_self]
    obtain ⟨k, j, d, hj, hsum⟩ := dual_eq_sum_of_ker ρ (f - n) hx
    have hfp : f = (Submodule.linearProjOfIsCompl F N hN (f - n) : HdR A) := by
      have e1 : Submodule.linearProjOfIsCompl F N hN f = ⟨f, hf⟩ :=
        Submodule.linearProjOfIsCompl_apply_left hN ⟨f, hf⟩
      have e2 : Submodule.linearProjOfIsCompl F N hN n = 0 :=
        (Submodule.linearProjOfIsCompl_apply_eq_zero_iff hN).2 hn
      rw [map_sub, e1, e2, sub_zero]
    refine LinearMap.ext fun c₁ ↦ ?_
    obtain ⟨c, rfl⟩ := hPs c₁
    rw [ef c, hfp, hsum]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, Submodule.coe_sum, hj]
  · refine codisjoint_iff_le_sup.2 fun y _ ↦ ?_
    obtain ⟨x, ex⟩ := hlift y
    obtain ⟨f, hf, n, hn, rfl⟩ := Submodule.mem_sup.1 (hN.sup_eq_top ▸ Submodule.mem_top : x ∈ F ⊔ N)
    obtain ⟨yf, ef⟩ := hex f
    obtain ⟨yn, en⟩ := hex n
    refine Submodule.mem_sup.2 ⟨yf, ⟨f, hf, ef⟩, yn, ⟨n, hn, en⟩, huniq (fun c ↦ ?_) ex⟩
    rw [LinearMap.add_apply, LinearMap.add_apply, ef c, en c, map_add (f := _)]
  · rw [hFil y]
    constructor
    · rintro ⟨x, hx, e⟩
      obtain ⟨x₁, e₁⟩ := hex x
      refine ⟨x₁, ⟨x, hx, e₁⟩, fun c₁ ↦ ?_⟩
      obtain ⟨c, rfl⟩ := hPs c₁
      rw [comp, e c, e₁ c]
      exact (RingHom.congr_fun hs.comp _).symm
    · rintro ⟨x₁, ⟨x, hx, e₁⟩, e⟩
      exact ⟨x, hx, fun c ↦ by rw [← comp, e, e₁ c]; exact RingHom.congr_fun hs.comp _⟩

end GlobalTheory.SqLift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupSchemeDividedPowerLiftTowerStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.group_scheme_divided_power_lift_tower : AbelianDeRham → ∀ (R R₁ R₀ : Type) [CommRing R] [CommRing R₁] [CommRing R₀] (I J : Ideal R) (I₁ : Ideal R₁) (κ : DividedPowers I) (π : R →+* R₀)
    (hJ : J ^ 2 = 0) (ρ : R →+* R₁) (κ₁ : DividedPowers I₁) (π₁ : R₁ →+* R₀), IsStep κ π hJ ρ κ₁ π₁ →
    ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A₁ : Over (Sp R₁)) [GrpObj A₁] (A : Over (Sp R)) [GrpObj A]
      (i₁ : A₀.left ⟶ A₁.left) (i₂ : A₁.left ⟶ A.left) (i : A₀.left ⟶ A.left)
      (h₁ : IsGrpPullback A₀ A₁ (spMap π₁) i₁) (h₂ : IsGrpPullback A₁ A (spMap ρ) i₂) (h : IsGrpPullback A₀ A (spMap π) i),
      i₁ ≫ i₂ = i → IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ F : Submodule R (HdR A), IsAdmissible h F → ∃ F₁ : Submodule R₁ (HdR A₁), IsAdmissible h₁ F₁ ∧
      ∀ y : HdR A₁, y ∈ F₁ ↔ ∃ x ∈ F, (redMor h₂).Corr x y := by
  first | exact @GlobalTheory.SqLift.isAdmissible_reduce | exact GlobalTheory.SqLift.isAdmissible_reduce | (intros; apply GlobalTheory.SqLift.isAdmissible_reduce <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftAbelianSchemeAlongSquareZeroFactorization
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqLift

theorem corr_crysToDR_step_iff {R R₁ R₀ : Type} [CommRing R] [CommRing R₁] [CommRing R₀] {I : Ideal R}
    {I₁ : Ideal R₁} {κ : DividedPowers I} {κ₁ : DividedPowers I₁} {π : R →+* R₀} {ρ : R →+* R₁}
    {π₁ : R₁ →+* R₀} {A₀ : Over (Sp R₀)} [GrpObj A₀] {X₁ : Over (Sp R₁)} [GrpObj X₁] {X : Over (Sp R)}
    [GrpObj X] {i₁ : A₀.left ⟶ X₁.left} {i₂ : X₁.left ⟶ X.left} {i : A₀.left ⟶ X.left}
    (h₁ : IsGrpPullback A₀ X₁ (spMap π₁) i₁) (h₂ : IsGrpPullback X₁ X (spMap ρ) i₂)
    (h : IsGrpPullback A₀ X (spMap π) i) (e : i₁ ≫ i₂ = i)
    (M : GrpMor κ (spMap π) A₀ κ₁ (spMap π₁) A₀ ρ (𝟙 _) (𝟙 _))
    (hs : Function.Surjective (liftMor κ h).pull) (d : Crys κ (spMap π) A₀) (d₁ : Crys κ₁ (spMap π₁) A₀) :
    (redMor h₂).Corr (crysToDR κ h d) (crysToDR κ₁ h₁ d₁) ↔ M.Corr d d₁ := by
  have k : GrpMor (dp0 R) (𝟙 _) X κ₁ (spMap π₁) A₀
      (ρ.comp (RingHom.id R)) ((𝟙 _) ≫ spMap π) ((𝟙 _) ≫ i) := by
    apply GrpMor.of_isGrpPullback
    · exact IsDPMorphism.comp _ M.dp (liftMor κ h).dp
    · simpa using M.base
    · simpa using h
  have e1 : ∀ c, (liftMor κ₁ h₁).pull ((redMor h₂).pull c) = k.pull c := fun c ↦
    GrpMor.pull_pull _ _ _ (fun _ ↦ rfl) (by rw [Category.id_comp, e]) c
  have e2 : ∀ c, M.pull ((liftMor κ h).pull c) = k.pull c := fun c ↦
    GrpMor.pull_pull _ _ _ (fun _ ↦ rfl) rfl c
  constructor
  · intro H c
    obtain ⟨c, rfl⟩ := hs c
    have := H c
    rw [crysToDR_apply, crysToDR_apply, e1, ← e2] at this
    exact this
  · intro H c
    rw [crysToDR_apply, crysToDR_apply, e1, ← e2]
    exact H _

theorem liftObj_step : AbelianDeRham → AbelianUnobstructed → ∀ (R R₁ R₀ : Type) [CommRing R] [CommRing R₁]
    [CommRing R₀] (I J : Ideal R) (I₁ : Ideal R₁) (κ : DividedPowers I) (π : R →+* R₀)
    (hJ : J ^ 2 = 0) (ρ : R →+* R₁) (κ₁ : DividedPowers I₁) (π₁ : R₁ →+* R₀), IsStep κ π hJ ρ κ₁ π₁ →
    LiftObj (divided₂ hJ) ρ → LiftObj κ₁ π₁ → LiftObj κ π := by
  intro P U R R₁ R₀ _ _ _ I J I₁ κ π hJ ρ κ₁ π₁ S L₂ L₁
  intro g A₀ _ A' _ i' h' hA' hg F hF
  have hπ : Function.Surjective π := S.comp ▸ S.surj₁.comp S.surj
  have hrig := P.2.2.2.1
  have hsp : spMap π = spMap π₁ ≫ spMap ρ := by rw [← S.comp, Cris.spMap_comp]
  have M : GrpMor κ (spMap π) A₀ κ₁ (spMap π₁) A₀ ρ (𝟙 _) (𝟙 _) := by
    refine ⟨S.dp, ?_, ?_, ?_⟩
    · simpa using hsp
    · simp
    · intro T x y x₀ y₀ hx hy
      have mul_left {U : Over (Sp R₀)} (a b : U ⟶ A₀) :
          (a * b).left = CategoryTheory.Limits.pullback.lift a.left b.left ((Over.w a).trans (Over.w b).symm) ≫ μ[A₀].left := by
        rw [Hom.mul_def, Over.comp_left, Over.lift_left]
      rw [mul_left, mul_left]
      congr 1
      apply CategoryTheory.Limits.pullback.hom_ext
      · simpa using hx
      · simpa using hy

  obtain ⟨A₁, _, i₁, i₂, h₁, h₂, e₁₂, hA₁, hg₁⟩ :=
    GlobalTheory.T.exists_intermediate_grpPullback_abelianScheme R R₁ R₀ ρ π₁ g A₀ A' i' (by rw [S.comp]; exact h') hA' hg
  obtain ⟨F₁, hF₁, hF₁F⟩ :=
    GlobalTheory.T.group_scheme_divided_power_lift_tower P R R₁ R₀ I J I₁ κ π hJ ρ κ₁ π₁ S g A₀ A₁ A' i₁ i₂ i' h₁ h₂ h' e₁₂ hA' hg F hF

  obtain ⟨B₁, _, j₁, k₁, hB₁, hgB₁, hfB₁⟩ := L₁ g A₀ A₁ i₁ h₁ hA₁ hg₁ F₁ hF₁
  obtain ⟨C, _, j₂, k₂, hC⟩ := U R J hJ R₁ ρ S.surj S.kerJ B₁ hB₁
  have hgC : SmoothOfRelativeDimension g C.hom :=
    GlobalTheory.T.smoothOfRelativeDimension_of_nilpotent_reduction R R₁ ρ S.surj (by rw [S.kerJ]; exact ⟨2, hJ⟩) g C B₁ j₂ k₂.1 hC.smooth hgB₁
  have kC : IsGrpPullback A₀ C (spMap π) (j₁ ≫ j₂) := (k₁.comp k₂).congr hsp.symm rfl
  have b' : Function.Bijective (crysToDR κ h') :=
    AbelianDeRham.Rigid.crysToDR_bijective hrig hA' hg S.nil hπ S.ker h'
  have bC : Function.Bijective (crysToDR κ kC) :=
    AbelianDeRham.Rigid.crysToDR_bijective hrig hC hgC S.nil hπ S.ker kC
  have bB₁ : Function.Bijective (crysToDR κ₁ k₁) :=
    AbelianDeRham.Rigid.crysToDR_bijective hrig hB₁ hgB₁ S.nil₁ S.surj₁ S.ker₁ k₁
  have s' := (hrig R A' g hA' hg I κ S.nil R₀ π hπ S.ker A₀ i' h').2
  have sC := (hrig R C g hC hgC I κ S.nil R₀ π hπ S.ker A₀ _ kC).2

  set E := F.comap (crysToDR κ h') with hE
  set FC := E.map (crysToDR κ kC) with hFC
  have hFCa : IsAdmissible k₂ FC := by
    obtain ⟨N, hN⟩ := hF.1
    refine ⟨⟨(N.comap (crysToDR κ h')).map (crysToDR κ kC), ?_⟩, fun y ↦ ?_⟩
    · exact (Submodule.orderIsoMapComap (LinearEquiv.ofBijective _ bC)).isCompl
        ((Submodule.orderIsoMapComap (LinearEquiv.ofBijective _ b')).symm.isCompl hN)
    obtain ⟨d₁, rfl⟩ := bB₁.2 y
    have l1 : crysToDR κ₁ k₁ d₁ ∈ Fil B₁ ↔ ∃ d ∈ E, M.Corr d d₁ := by
      change d₁ ∈ liftFil κ₁ k₁ ↔ _
      rw [hfB₁, Submodule.mem_comap, hF₁F]
      constructor
      · rintro ⟨x, hx, ex⟩
        obtain ⟨d, rfl⟩ := b'.2 x
        exact ⟨d, hx, (corr_crysToDR_step_iff h₁ h₂ h' e₁₂ M s' d d₁).1 ex⟩
      · rintro ⟨d, hd, ed⟩
        exact ⟨_, hd, (corr_crysToDR_step_iff h₁ h₂ h' e₁₂ M s' d d₁).2 ed⟩
    rw [l1]
    constructor
    · rintro ⟨d, hd, ed⟩
      exact ⟨_, ⟨d, hd, rfl⟩, (corr_crysToDR_step_iff k₁ k₂ kC rfl M sC d d₁).2 ed⟩
    · rintro ⟨_, ⟨d, hd, rfl⟩, ex⟩
      exact ⟨d, hd, (corr_crysToDR_step_iff k₁ k₂ kC rfl M sC d d₁).1 ex⟩

  obtain ⟨A, _, j₃, k₃, hA, hgA, hfA⟩ := L₂ g B₁ C j₂ k₂ hC hgC FC hFCa
  have kA : IsGrpPullback A₀ A (spMap π) (j₁ ≫ j₃) := (k₁.comp k₃).congr hsp.symm rfl
  refine ⟨A, inferInstance, j₁ ≫ j₃, kA, hA, hgA, ?_⟩
  obtain ⟨N, -, hNC⟩ :=
    GlobalTheory.T.deRham_crystal_two_reductions_agree P R R₁ R₀ I J I₁ κ π hJ ρ κ₁ π₁ S g A₀ B₁ C j₁ j₂ (j₁ ≫ j₂) k₁ k₂ kC rfl hC hgC
  obtain ⟨N', -, hNA⟩ :=
    GlobalTheory.T.deRham_crystal_two_reductions_agree P R R₁ R₀ I J I₁ κ π hJ ρ κ₁ π₁ S g A₀ B₁ A j₁ j₃ (j₁ ≫ j₃) k₁ k₃ kA rfl hA hgA
  obtain rfl : N' = N := rfl
  ext d
  change crysToDR κ kA d ∈ Fil A ↔ d ∈ E
  rw [hNA d]
  change _ ∈ liftFil (divided₂ hJ) k₃ ↔ _
  rw [hfA, Submodule.mem_comap, ← hNC d]
  exact ⟨fun ⟨d', hd', e⟩ ↦ bC.1 e ▸ hd', fun hd ↦ ⟨d, hd, rfl⟩⟩

end GlobalTheory.SqLift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftAbelianSchemeAlongSquareZeroFactorizationStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftAbelianScheme_along_squareZero_factorization : AbelianDeRham → AbelianUnobstructed → ∀ (R R₁ R₀ : Type) [CommRing R] [CommRing R₁] [CommRing R₀] (I J : Ideal R) (I₁ : Ideal R₁) (κ : DividedPowers I) (π : R →+* R₀)
    (hJ : J ^ 2 = 0) (ρ : R →+* R₁) (κ₁ : DividedPowers I₁) (π₁ : R₁ →+* R₀), IsStep κ π hJ ρ κ₁ π₁ →
    LiftObj (divided₂ hJ) ρ → LiftObj κ₁ π₁ → LiftObj κ π := by
  first | exact @GlobalTheory.SqLift.liftObj_step | exact GlobalTheory.SqLift.liftObj_step | (intros; apply GlobalTheory.SqLift.liftObj_step <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftHomOfIsStep
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeFiltrationMiddleEqReductionOfTop
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeFiltrationMiddleEqReductionOfTop
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FilRed

theorem filtration_reduction : AbelianDeRham → ∀ (R R₁ R₀ : Type) [CommRing R] [CommRing R₁] [CommRing R₀] (I J : Ideal R) (I₁ : Ideal R₁) (κ : DividedPowers I) (π : R →+* R₀)
    (hJ : J ^ 2 = 0) (ρ : R →+* R₁) (κ₁ : DividedPowers I₁) (π₁ : R₁ →+* R₀), IsStep κ π hJ ρ κ₁ π₁ →
    ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A₁ : Over (Sp R₁)) [GrpObj A₁] (A : Over (Sp R)) [GrpObj A]
      (i₁ : A₀.left ⟶ A₁.left) (i₂ : A₁.left ⟶ A.left) (i : A₀.left ⟶ A.left)
      (h₁ : IsGrpPullback A₀ A₁ (spMap π₁) i₁) (h₂ : IsGrpPullback A₁ A (spMap ρ) i₂) (h : IsGrpPullback A₀ A (spMap π) i),
      i₁ ≫ i₂ = i → IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ (M : GrpMor κ (spMap π) A₀ κ₁ (spMap π₁) A₀ ρ (𝟙 _) (𝟙 _)) (F : Submodule R (HdR A)) (F₁ : Submodule R₁ (HdR A₁)),
      (∀ y : HdR A₁, y ∈ F₁ ↔ ∃ x ∈ F, (redMor h₂).Corr x y) →
      (∀ d₁, crysToDR κ₁ h₁ d₁ ∈ F₁ ↔ ∃ d, crysToDR κ h d ∈ F ∧ M.Corr d d₁) ∧
      ((∀ y : HdR A₁, y ∈ Fil A₁ ↔ ∃ x ∈ Fil A, (redMor h₂).Corr x y)) := by
  intro P R R₁ R₀ _ _ _ I J I₁ κ π hJ ρ κ₁ π₁ hS g A₀ _ A₁ _ A _ i₁ i₂ i h₁ h₂ h e hA hg M F F₁ hF
  have hπ : Function.Surjective π := hS.comp ▸ hS.surj₁.comp hS.surj
  have H := canonical_of_abelianDeRham P hS.nil hπ hS.ker
  have hb := H.crysToDR_bijective h hA hg
  have hs := (H g A₀ A i h hA hg).1.2
  have e' : i₁ ≫ i₂ = 𝟙 _ ≫ i := by rw [e, Category.id_comp]
  have key : ∀ d d₁, (redMor h₂).Corr (crysToDR κ h d) (crysToDR κ₁ h₁ d₁) ↔ M.Corr d d₁ := by
    intro d d₁
    refine ⟨fun H' c' ↦ ?_, fun H' ↦ crysToDR_corr κ h h₁ M (redMor h₂) e' H'⟩
    obtain ⟨c, rfl⟩ := hs c'
    have k : GrpMor (dp0 R) (𝟙 (Sp R)) A κ₁ (spMap π₁) A₀
        (ρ.comp (RingHom.id R)) (𝟙 _ ≫ spMap π) (𝟙 _ ≫ i) := by
      let m := liftMor κ h
      refine ⟨IsDPMorphism.comp _ M.dp m.dp, ?_, ?_, ?_⟩
      · rw [Category.assoc, m.base, ← Category.assoc, M.base, Category.assoc, Cris.spMap_comp]
      · rw [Category.assoc, m.w, ← Category.assoc, M.w, Category.assoc]
      · intro T x y x₀ y₀ hx hy
        let x₁ : Over.mk (T.hom ≫ 𝟙 _) ⟶ A₀ := Over.homMk (x.left ≫ 𝟙 _) (by
          simp only [Over.mk_hom, Category.assoc]; rw [M.w, reassoc_of% (Over.w x)])
        let y₁ : Over.mk (T.hom ≫ 𝟙 _) ⟶ A₀ := Over.homMk (y.left ≫ 𝟙 _) (by
          simp only [Over.mk_hom, Category.assoc]; rw [M.w, reassoc_of% (Over.w y)])
        let x₂ : Over.mk ((Over.mk (T.hom ≫ 𝟙 _)).hom ≫ spMap π) ⟶ A := Over.homMk x₀.left (by simpa using Over.w x₀)
        let y₂ : Over.mk ((Over.mk (T.hom ≫ 𝟙 _)).hom ≫ spMap π) ⟶ A := Over.homMk y₀.left (by simpa using Over.w y₀)
        have h₁ : (x₁ * y₁).left = (x * y).left ≫ 𝟙 _ := M.mul T x y x₁ y₁ rfl rfl
        have h₂ : (x₂ * y₂).left = (x₁ * y₁).left ≫ i :=
          m.mul _ x₁ y₁ x₂ y₂ (by simp [x₂, x₁, hx]) (by simp [y₂, y₁, hy])
        have h₃ : (x₀ * y₀).left = (x₂ * y₂).left := by
          simp only [Hom.mul_def, Over.comp_left, Over.lift_left, x₂, y₂, Over.homMk_left]
        rw [h₃, h₂, h₁, Category.assoc]
    rw [GrpMor.pull_pull (liftMor κ h) M k (fun _ ↦ rfl) rfl c,
      ← GrpMor.pull_pull (redMor h₂) (liftMor κ₁ h₁) k (fun _ ↦ rfl) e' c]
    exact H' c
  refine ⟨fun d₁ ↦ ?_, (canonical_of_abelianDeRham P (isDPNilpotent_squareZero hJ) hS.surj hS.kerJ g A₁ A i₂ h₂ hA hg).2.2⟩
  rw [hF]
  constructor
  · rintro ⟨x, hx, c⟩
    obtain ⟨d, rfl⟩ := hb.2 x
    exact ⟨d, hx, (key d d₁).1 c⟩
  · rintro ⟨d, hd, c⟩
    exact ⟨_, hd, (key d d₁).2 c⟩

end GlobalTheory.FilRed
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeFiltrationMiddleEqReductionOfTopStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeFiltration_middle_eq_reduction_of_top : AbelianDeRham → ∀ (R R₁ R₀ : Type) [CommRing R] [CommRing R₁] [CommRing R₀] (I J : Ideal R) (I₁ : Ideal R₁) (κ : DividedPowers I) (π : R →+* R₀)
    (hJ : J ^ 2 = 0) (ρ : R →+* R₁) (κ₁ : DividedPowers I₁) (π₁ : R₁ →+* R₀), IsStep κ π hJ ρ κ₁ π₁ →
    ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A₁ : Over (Sp R₁)) [GrpObj A₁] (A : Over (Sp R)) [GrpObj A]
      (i₁ : A₀.left ⟶ A₁.left) (i₂ : A₁.left ⟶ A.left) (i : A₀.left ⟶ A.left)
      (h₁ : IsGrpPullback A₀ A₁ (spMap π₁) i₁) (h₂ : IsGrpPullback A₁ A (spMap ρ) i₂) (h : IsGrpPullback A₀ A (spMap π) i),
      i₁ ≫ i₂ = i → IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ (M : GrpMor κ (spMap π) A₀ κ₁ (spMap π₁) A₀ ρ (𝟙 _) (𝟙 _)) (F : Submodule R (HdR A)) (F₁ : Submodule R₁ (HdR A₁)),
      (∀ y : HdR A₁, y ∈ F₁ ↔ ∃ x ∈ F, (redMor h₂).Corr x y) →
      (∀ d₁, crysToDR κ₁ h₁ d₁ ∈ F₁ ↔ ∃ d, crysToDR κ h d ∈ F ∧ M.Corr d d₁) ∧
      ((∀ y : HdR A₁, y ∈ Fil A₁ ↔ ∃ x ∈ Fil A, (redMor h₂).Corr x y)) := by
  first | exact @GlobalTheory.FilRed.filtration_reduction | exact GlobalTheory.FilRed.filtration_reduction | (intros; apply GlobalTheory.FilRed.filtration_reduction <;> assumption)
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqLift

section Step

variable {R R₁ R₀ : Type} [CommRing R] [CommRing R₁] [CommRing R₀] {I J : Ideal R} {I₁ : Ideal R₁}
  {κ : DividedPowers I} {π : R →+* R₀} {hJ : J ^ 2 = 0} {ρ : R →+* R₁} {κ₁ : DividedPowers I₁}
  {π₁ : R₁ →+* R₀}

theorem IsStep.spMap_eq (st : IsStep κ π hJ ρ κ₁ π₁) : spMap π = spMap π₁ ≫ spMap ρ := by
  rw [← st.comp, Cris.spMap_comp]

theorem IsStep.idMor (st : IsStep κ π hJ ρ κ₁ π₁) (A₀ : Over (Sp R₀)) [GrpObj A₀] :
    GrpMor κ (spMap π) A₀ κ₁ (spMap π₁) A₀ ρ (𝟙 _) (𝟙 _) :=
  ⟨st.dp, by simpa using st.spMap_eq, by simp, by
    intro T x y x₀ y₀ hx hy
    have ex : x₀ = x := Over.OverMorphism.ext (by simpa using hx)
    have ey : y₀ = y := Over.OverMorphism.ext (by simpa using hy)
    subst x₀; subst y₀
    exact Category.comp_id _ |>.symm⟩

def redSub (hρ : Function.Surjective ρ) {A₁ : Over (Sp R₁)} [GrpObj A₁] {A : Over (Sp R)} [GrpObj A]
    {i₂ : A₁.left ⟶ A.left} (h₂ : IsGrpPullback A₁ A (spMap ρ) i₂) (F : Submodule R (HdR A)) :
    Submodule R₁ (HdR A₁) where
  carrier := {y | ∃ x ∈ F, (redMor h₂).Corr x y}
  add_mem' := by
    rintro y y' ⟨x, hx, e⟩ ⟨x', hx', e'⟩
    exact ⟨x + x', F.add_mem hx hx', fun c ↦ by
      rw [LinearMap.add_apply, LinearMap.add_apply, e, e', map_add (f := _)]⟩
  zero_mem' := ⟨0, F.zero_mem, fun c ↦ by simp⟩
  smul_mem' := by
    rintro r₁ y ⟨x, hx, e⟩
    obtain ⟨r, rfl⟩ := hρ r₁
    exact ⟨r • x, F.smul_mem r hx, fun c ↦ by
      rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, e, map_mul]⟩

theorem mem_liftFil_iff (P : AbelianDeRham) (st : IsStep κ π hJ ρ κ₁ π₁) {g : ℕ} {A₀ : Over (Sp R₀)}
    [GrpObj A₀] {A₁ : Over (Sp R₁)} [GrpObj A₁] {A : Over (Sp R)} [GrpObj A] {i₁ : A₀.left ⟶ A₁.left}
    {i₂ : A₁.left ⟶ A.left} {i : A₀.left ⟶ A.left} (h₁ : IsGrpPullback A₀ A₁ (spMap π₁) i₁)
    (h₂ : IsGrpPullback A₁ A (spMap ρ) i₂) (h : IsGrpPullback A₀ A (spMap π) i) (ei : i₁ ≫ i₂ = i)
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) (d₁ : Crys κ₁ (spMap π₁) A₀) :
    d₁ ∈ liftFil κ₁ h₁ ↔ ∃ d ∈ liftFil κ h, (st.idMor A₀).Corr d d₁ := by
  have T := GlobalTheory.T.hodgeFiltration_middle_eq_reduction_of_top P R R₁ R₀ I J I₁ κ π hJ ρ κ₁ π₁ st g A₀ A₁ A i₁ i₂ i h₁ h₂ h ei hA hg
    (st.idMor A₀) (Fil A) (redSub st.surj h₂ (Fil A)) (fun _ ↦ Iff.rfl)
  have e : Fil A₁ = redSub st.surj h₂ (Fil A) := Submodule.ext T.2
  rw [liftFil, Submodule.mem_comap, e, T.1 d₁]
  exact Iff.rfl

theorem dualMap_push {A₀ B₀ : Over (Sp R₀)} [GrpObj A₀] [GrpObj B₀] {A₁ B₁ : Over (Sp R₁)} [GrpObj A₁]
    [GrpObj B₁] {i₁ : A₀.left ⟶ A₁.left} {j₁ : B₀.left ⟶ B₁.left}
    (NA : GrpMor (divided₂ hJ) (spMap ρ) A₁ κ (spMap π) A₀ (RingHom.id R) (spMap π₁) i₁)
    (NB : GrpMor (divided₂ hJ) (spMap ρ) B₁ κ (spMap π) B₀ (RingHom.id R) (spMap π₁) j₁)
    (f₀ : A₀ ⟶ B₀) (f₁ : A₁ ⟶ B₁) [IsMonHom f₀] [IsMonHom f₁] (e : i₁ ≫ f₁.left = f₀.left ≫ j₁)
    (d : Crys κ (spMap π) A₀) :
    (NB.pull : prim (divided₂ hJ) (spMap ρ) B₁ →ₗ[R] prim κ (spMap π) B₀).dualMap (push κ (spMap π) f₀ d) =
      push (divided₂ hJ) (spMap ρ) f₁
        ((NA.pull : prim (divided₂ hJ) (spMap ρ) A₁ →ₗ[R] prim κ (spMap π) A₀).dualMap d) := by
  refine LinearMap.ext fun c ↦ ?_
  let m : GrpMor (divided₂ hJ) (spMap ρ) B₁ κ (spMap π) A₀
      (RingHom.id R) (spMap π₁ ≫ 𝟙 _) (i₁ ≫ f₁.left) := by
    refine ⟨NA.dp, ?_, ?_, ?_⟩
    · simpa using NA.base
    · simpa only [Category.comp_id, Category.assoc, Over.w f₁] using NA.w
    · intro T x y x₀ y₀ hx hy
      let x₁ : Over.mk (T.hom ≫ spMap π₁) ⟶ A₁ :=
        Over.homMk (x.left ≫ i₁) (by simp only [Over.mk_hom, Category.assoc, NA.w, reassoc_of% (Over.w x)])
      let y₁ : Over.mk (T.hom ≫ spMap π₁) ⟶ A₁ :=
        Over.homMk (y.left ≫ i₁) (by simp only [Over.mk_hom, Category.assoc, NA.w, reassoc_of% (Over.w y)])
      let x₂ : Over.mk ((Over.mk (T.hom ≫ spMap π₁)).hom ≫ 𝟙 _) ⟶ B₁ :=
        Over.homMk x₀.left (by simpa using Over.w x₀)
      let y₂ : Over.mk ((Over.mk (T.hom ≫ spMap π₁)).hom ≫ 𝟙 _) ⟶ B₁ :=
        Over.homMk y₀.left (by simpa using Over.w y₀)
      have h₁ := NA.mul T x y x₁ y₁ rfl rfl
      have h₂ := (homMor (divided₂ hJ) (spMap ρ) f₁).mul _ x₁ y₁ x₂ y₂
        (by simpa [x₂, x₁, Category.assoc] using hx)
        (by simpa [y₂, y₁, Category.assoc] using hy)
      have h₃ : (x₀ * y₀).left = (x₂ * y₂).left := by
        simp [Hom.mul_def, Over.comp_left, Over.lift_left, x₂, y₂]
      rw [h₃, h₂, h₁, Category.assoc]
  have e1 : (homMor κ (spMap π) f₀).pull (NB.pull c) = m.pull c :=
    GrpMor.pull_pull NB (homMor κ (spMap π) f₀) m (fun _ ↦ rfl) e.symm c
  have e2 : NA.pull ((homMor (divided₂ hJ) (spMap ρ) f₁).pull c) = m.pull c :=
    GrpMor.pull_pull (homMor (divided₂ hJ) (spMap ρ) f₁) NA m (fun _ ↦ rfl) rfl c
  exact congrArg d (e1.trans e2.symm)

end Step

theorem liftHom_of_isStep : AbelianDeRham → ∀ (R R₁ R₀ : Type) [CommRing R] [CommRing R₁] [CommRing R₀] (I J : Ideal R) (I₁ : Ideal R₁) (κ : DividedPowers I) (π : R →+* R₀)
    (hJ : J ^ 2 = 0) (ρ : R →+* R₁) (κ₁ : DividedPowers I₁) (π₁ : R₁ →+* R₀), IsStep κ π hJ ρ κ₁ π₁ →
    LiftHom (divided₂ hJ) ρ → LiftHom κ₁ π₁ → LiftHom κ π := by
  intro P R R₁ R₀ _ _ _ I J I₁ κ π hJ ρ κ₁ π₁ st H₂ H₁
  intro g A₀ _ A _ i h hA hg g' B₀ _ B _ j k hB hg' f₀ _ hf
  have hc : spMap (π₁.comp ρ) = spMap π := by rw [st.comp]
  obtain ⟨A₁, _, i₁, i₂, h₁, h₂, ei, hA₁, hgA⟩ :=
    GlobalTheory.T.exists_intermediate_grpPullback_abelianScheme R R₁ R₀ ρ π₁ g A₀ A i (by rw [hc]; exact h) hA hg
  obtain ⟨B₁, _, j₁, j₂, k₁, k₂, ej, hB₁, hgB⟩ :=
    GlobalTheory.T.exists_intermediate_grpPullback_abelianScheme R R₁ R₀ ρ π₁ g' B₀ B j (by rw [hc]; exact k) hB hg'

  have hf₁ : ∀ d₁ ∈ liftFil κ₁ h₁, push κ₁ (spMap π₁) f₀ d₁ ∈ liftFil κ₁ k₁ := by
    intro d₁ hd₁
    obtain ⟨d, hd, e⟩ := (mem_liftFil_iff P st h₁ h₂ h ei hA hg d₁).1 hd₁
    exact (mem_liftFil_iff P st k₁ k₂ k ej hB hg' _).2
      ⟨_, hf d hd, GrpMor.Corr.push (st.idMor B₀) f₀ f₀ (by simp) e⟩
  obtain ⟨f₁, ⟨_, ef₁⟩, uf₁⟩ := H₁ g A₀ A₁ i₁ h₁ hA₁ hgA g' B₀ B₁ j₁ k₁ hB₁ hgB f₀ hf₁

  obtain ⟨NA, bA, cA⟩ := GlobalTheory.T.deRham_crystal_two_reductions_agree P R R₁ R₀ I J I₁ κ π hJ ρ κ₁ π₁ st g A₀ A₁ A i₁ i₂ i h₁ h₂ h ei hA hg
  obtain ⟨NB, -, cB⟩ := GlobalTheory.T.deRham_crystal_two_reductions_agree P R R₁ R₀ I J I₁ κ π hJ ρ κ₁ π₁ st g' B₀ B₁ B j₁ j₂ j k₁ k₂ k ej hB hg'
  have sA : Function.Surjective
      (NA.pull : prim (divided₂ hJ) (spMap ρ) A₁ →ₗ[R] prim κ (spMap π) A₀).dualMap :=
    (LinearEquiv.ofBijective _ bA).dualMap.surjective
  have hf₂ : ∀ e ∈ liftFil (divided₂ hJ) h₂, push (divided₂ hJ) (spMap ρ) f₁ e ∈ liftFil (divided₂ hJ) k₂ := by
    intro e he
    obtain ⟨d, rfl⟩ := sA e
    have hd : d ∈ liftFil κ h := by
      rw [liftFil, Submodule.mem_comap, cA]; exact he
    have hk := hf d hd
    rw [liftFil, Submodule.mem_comap, cB] at hk
    rw [liftFil, Submodule.mem_comap, ← dualMap_push NA NB f₀ f₁ ef₁ d]
    exact hk
  obtain ⟨f, ⟨_, ef⟩, uf⟩ := H₂ g A₁ A i₂ h₂ hA hg g' B₁ B j₂ k₂ hB hg' f₁ hf₂
  refine ⟨f, ⟨inferInstance, ?_⟩, ?_⟩
  · rw [← ei, ← ej, Category.assoc, ef, ← Category.assoc, ef₁, Category.assoc]
  · rintro f' ⟨_, ef'⟩
    let f₁' : A₁ ⟶ B₁ := Over.homMk (k₂.1.lift (i₂ ≫ f'.left) A₁.hom
      (by rw [Category.assoc, Over.w f', h₂.1.w])) (k₂.1.lift_snd _ _ _)
    have e₁ : f₁'.left ≫ j₂ = i₂ ≫ f'.left := k₂.1.lift_fst _ _ _
    haveI := ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.isMonHom_of_grpPullback h₂ k₂ f' f₁' e₁
    have e₂ : i₁ ≫ f₁'.left = f₀.left ≫ j₁ := by
      refine k₂.1.hom_ext ?_ ?_
      · rw [Category.assoc, e₁, ← Category.assoc, ei, ef', Category.assoc, ej]
      · rw [Category.assoc, Category.assoc, Over.w f₁', h₁.1.w, k₁.1.w, ← Category.assoc, Over.w f₀]
    have e₃ : f₁' = f₁ := uf₁ f₁' ⟨inferInstance, e₂⟩
    exact uf f' ⟨inferInstance, by rw [← e₁, e₃]⟩

end GlobalTheory.SqLift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsStepNilExp
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SqLift.DPStep

variable {R : Type} [CommRing R] {I : Ideal R}

def prods (κ : DividedPowers I) (m : ℕ) : Set R :=
  {x | ∃ l : List (ℕ × R), (∀ p ∈ l, p.2 ∈ I) ∧ m ≤ (l.map Prod.fst).sum ∧
    x = (l.map fun p ↦ κ.dpow p.1 p.2).prod}

theorem prod_mem (κ : DividedPowers I) : ∀ l : List (ℕ × R), (∀ p ∈ l, p.2 ∈ I) →
    1 ≤ (l.map Prod.fst).sum → (l.map fun p ↦ κ.dpow p.1 p.2).prod ∈ I := by
  intro l
  induction l with
  | nil => simp
  | cons p l ih =>
    intro hl hs
    have hp : p.2 ∈ I := hl p (by simp)
    simp only [List.map_cons, List.sum_cons, List.prod_cons] at hs ⊢
    rcases Nat.eq_zero_or_pos p.1 with h | h
    · rw [h] at hs
      exact I.mul_mem_left _ (ih (fun q hq ↦ hl q (by simp [hq])) (by omega))
    · exact I.mul_mem_right _ (κ.dpow_mem (by omega) hp)

theorem dpow_prod_eq_zero (κ : DividedPowers I) {N : ℕ} (hN : NilExp κ (N + 2)) :
    ∀ l : List (ℕ × R), (∀ p ∈ l, p.2 ∈ I) → N + 1 ≤ (l.map Prod.fst).sum →
      ∀ n, 2 ≤ n → κ.dpow n (l.map fun p ↦ κ.dpow p.1 p.2).prod = 0 := by
  intro l
  induction l with
  | nil => intro _ h; simp at h
  | cons p l ih =>
    intro hl hs n hn
    have hp : p.2 ∈ I := hl p (by simp)
    have hl' : ∀ q ∈ l, q.2 ∈ I := fun q hq ↦ hl q (by simp [hq])
    simp only [List.map_cons, List.sum_cons, List.prod_cons] at hs ⊢
    rcases Nat.eq_zero_or_pos p.1 with h | h
    · rw [h, κ.dpow_zero hp, _root_.one_mul]
      exact ih hl' (by omega) n hn
    · set P := (l.map fun p ↦ κ.dpow p.1 p.2).prod
      have hm : κ.dpow p.1 p.2 ∈ I := κ.dpow_mem (by omega) hp
      have hz : P * κ.dpow (n * p.1) p.2 = 0 := by
        have := hN ((n * p.1, p.2) :: l) (by
          intro q hq
          rcases List.mem_cons.1 hq with rfl | hq
          · exact hp
          · exact hl' q hq) (by
          have : 2 * p.1 ≤ n * p.1 := Nat.mul_le_mul_right _ hn
          simp only [List.map_cons, List.sum_cons]
          omega)
        simpa [List.map_cons, List.prod_cons, mul_comm] using this
      rw [mul_comm, κ.dpow_mul hm, κ.dpow_comp (by omega) hp]
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      rw [pow_succ, mul_left_comm, _root_.mul_assoc, hz, mul_zero, mul_zero]

end GlobalTheory.SqLift.DPStep

namespace GlobalTheory.SqLift.DPStep

variable {R : Type} [CommRing R] {I : Ideal R}

def idl (κ : DividedPowers I) (m : ℕ) : Ideal R := Ideal.span (prods κ m)

theorem idl_le (κ : DividedPowers I) (N : ℕ) : idl κ (N + 1) ≤ I := by
  refine Ideal.span_le.2 ?_
  rintro x ⟨l, hl, hs, rfl⟩
  exact prod_mem κ l hl (by omega)

theorem mul_idl_eq_zero (κ : DividedPowers I) {N : ℕ} (hN : NilExp κ (N + 2)) {a : R} (ha : a ∈ I) :
    ∀ b ∈ idl κ (N + 1), a * b = 0 := by
  intro b hb
  induction hb using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, hs, rfl⟩ := hx
    have := hN ((1, a) :: l) (by
      intro q hq
      rcases List.mem_cons.1 hq with rfl | hq
      · exact ha
      · exact hl q hq) (by simp only [List.map_cons, List.sum_cons]; omega)
    simpa [κ.dpow_one ha] using this
  | zero => exact mul_zero a
  | add x y _ _ hx hy => rw [mul_add, hx, hy, add_zero]
  | smul r x _ hx => rw [smul_eq_mul, mul_left_comm, hx, mul_zero]

theorem idl_sq (κ : DividedPowers I) {N : ℕ} (hN : NilExp κ (N + 2)) : idl κ (N + 1) ^ 2 = 0 := by
  rw [Ideal.zero_eq_bot, eq_bot_iff, pow_two]
  refine Ideal.mul_le.2 fun a ha b hb ↦ ?_
  rw [Ideal.mem_bot]
  exact mul_idl_eq_zero κ hN (idl_le κ N ha) b hb

theorem dpow_idl (κ : DividedPowers I) {N : ℕ} (hN : NilExp κ (N + 2)) :
    ∀ x ∈ idl κ (N + 1), ∀ n, 2 ≤ n → κ.dpow n x = 0 := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, hs, rfl⟩ := hx
    exact dpow_prod_eq_zero κ hN l hl hs
  | zero => intro n hn; exact κ.dpow_eval_zero (by omega)
  | add x y hxm hym hx hy =>
    intro n hn
    have hxI := idl_le κ N hxm
    have hyI := idl_le κ N hym
    rw [κ.dpow_add hxI hyI]
    refine Finset.sum_eq_zero fun k hk ↦ ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hk
    by_cases h1 : 2 ≤ k.1
    · rw [hx _ h1, MulZeroClass.zero_mul]
    by_cases h2 : 2 ≤ k.2
    · rw [hy _ h2, mul_zero]
    obtain ⟨a, b⟩ := k
    simp only at h1 h2 hk
    obtain rfl : a = 1 := by omega
    obtain rfl : b = 1 := by omega
    rw [κ.dpow_one hxI, κ.dpow_one hyI]
    exact mul_idl_eq_zero κ hN hxI y hym
  | smul r x hxm hx =>
    intro n hn
    rw [smul_eq_mul, κ.dpow_mul (idl_le κ N hxm), hx n hn, mul_zero]

theorem isSubDPIdeal (κ : DividedPowers I) {N : ℕ} (hN : NilExp κ (N + 2)) :
    IsSubDPIdeal κ (idl κ (N + 1) ⊓ I) := by
  refine DividedPowers.IsSubDPIdeal.mk inf_le_right ?_
  intro n hn j hj
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    rw [κ.dpow_one hj.2]
    exact hj
  · rw [dpow_idl κ hN j hj.1 n h]
    exact Ideal.zero_mem _

end GlobalTheory.SqLift.DPStep


open GlobalTheory.SqLift.DPStep in
theorem GlobalTheory.SqLift.exists_isStep_nilExp :
    ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (κ : DividedPowers I) (π : R →+* R₀),
    Function.Surjective π → RingHom.ker π = I → ∀ N : ℕ, NilExp κ (N + 2) →
    ∃ (R₁ : Type) (_ : CommRing R₁) (J : Ideal R) (hJ : J ^ 2 = 0) (ρ : R →+* R₁) (I₁ : Ideal R₁) (κ₁ : DividedPowers I₁) (π₁ : R₁ →+* R₀),
      IsStep κ π hJ ρ κ₁ π₁ ∧ NilExp κ₁ (N + 1) := by
  intro R R₀ _ _ I κ π hπ hker N hN
  set J := idl κ (N + 1)
  have hJI : J ≤ I := idl_le κ N
  have hsub := isSubDPIdeal κ hN
  have hz : ∀ a ∈ J, π a = 0 := fun a ha ↦ by rw [← RingHom.mem_ker, hker]; exact hJI ha
  let π₁ : R ⧸ J →+* R₀ := Ideal.Quotient.lift J π hz
  have hnil1 : NilExp (DividedPowers.Quotient.dividedPowers κ hsub) (N + 1) := by
    intro l hl hs
    have key : ∀ l : List (ℕ × (R ⧸ J)), (∀ p ∈ l, p.2 ∈ I.map (Ideal.Quotient.mk J)) →
        ∃ l' : List (ℕ × R), (∀ p ∈ l', p.2 ∈ I) ∧ l'.map Prod.fst = l.map Prod.fst ∧
          (l.map fun p ↦ (DividedPowers.Quotient.dividedPowers κ hsub).dpow p.1 p.2).prod =
            Ideal.Quotient.mk J (l'.map fun p ↦ κ.dpow p.1 p.2).prod := by
      intro l
      induction l with
      | nil => intro _; exact ⟨[], by simp, by simp, by simp⟩
      | cons p l ih =>
        intro hl
        obtain ⟨l', hl', he, hp⟩ := ih fun q hq ↦ hl q (by simp [hq])
        obtain ⟨a, ha, hae⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1
          (hl p (by simp))
        refine ⟨(p.1, a) :: l', ?_, by simp [he], ?_⟩
        · intro q hq
          rcases List.mem_cons.1 hq with rfl | hq
          · exact ha
          · exact hl' q hq
        · simp only [List.map_cons, List.prod_cons, map_mul, hp, ← hae]
          rw [DividedPowers.Quotient.dpow_apply κ hsub ha]
    obtain ⟨l', hl', he, hp⟩ := key l hl
    rw [hp, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span ⟨l', hl', by rw [he]; exact hs, rfl⟩
  refine ⟨R ⧸ J, inferInstance, J, idl_sq κ hN, Ideal.Quotient.mk J, I.map (Ideal.Quotient.mk J),
    DividedPowers.Quotient.dividedPowers κ hsub, π₁, ?_, hnil1⟩
  refine
    { nil := ⟨N + 2, hN⟩
      nil₁ := ⟨N + 1, hnil1⟩
      surj := Ideal.Quotient.mk_surjective
      surj₁ := ?_
      comp := Ideal.Quotient.lift_comp_mk J π hz
      ker := hker
      kerJ := Ideal.mk_ker
      ker₁ := ?_
      dp := DividedPowers.Quotient.isDPMorphism κ hsub
      dpJ := ?_ }
  · intro y
    obtain ⟨a, rfl⟩ := hπ y
    exact ⟨Ideal.Quotient.mk J a, Ideal.Quotient.lift_mk J π hz⟩
  · ext y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [RingHom.mem_ker, Ideal.Quotient.lift_mk, ← RingHom.mem_ker, hker, Ideal.mem_quotient_iff_mem hJI]
  · refine (isDPMorphism_iff _ _ _).2 ⟨by rw [Ideal.map_id]; exact hJI, fun n hn a ha ↦ ?_⟩
    rcases Nat.lt_or_ge n 2 with h | h
    · obtain rfl : n = 1 := by omega
      rw [RingHom.id_apply, RingHom.id_apply, κ.dpow_one (hJI ha), (divided₂ _).dpow_one ha]
    · rw [RingHom.id_apply, RingHom.id_apply, squareZeroDividedPowers_dpow _ h, dpow_idl κ hN a ha n h]
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqLift

theorem NilExp.mono {R : Type} [CommRing R] {I : Ideal R} {κ : DividedPowers I} {N M : ℕ} (h : NilExp κ N)
    (e : N ≤ M) : NilExp κ M :=
  fun l hl hs ↦ h l hl (e.trans hs)

theorem NilExp.eq_zero {R : Type} [CommRing R] {I : Ideal R} {κ : DividedPowers I} (h : NilExp κ 1) {a : R}
    (ha : a ∈ I) : a = 0 := by

  have h1 := h [(1, a)] (by simpa using ha) (by simp)
  simpa [κ.dpow_one ha] using h1

theorem NilExp.eq_sqDP {R : Type} [CommRing R] {I : Ideal R} {κ : DividedPowers I} (h : NilExp κ 1) :
    ∃ hI : I ^ 2 = 0, κ = divided₂ hI := by
  have hbot : I = ⊥ := eq_bot_iff.2 fun a ha ↦ (Ideal.mem_bot).2 (h.eq_zero ha)
  have hI : I ^ 2 = 0 := by
    rw [hbot, pow_two, Ideal.mul_bot]
    rfl
  refine ⟨hI, ?_⟩

  ext n x hx
  obtain rfl := h.eq_zero hx
  rcases n with _ | _ | n
  · rw [κ.dpow_zero hx, (divided₂ hI).dpow_zero hx]
  · rw [κ.dpow_one hx, (divided₂ hI).dpow_one hx]
  · rw [squareZeroDividedPowers_dpow hI (by omega), κ.dpow_eval_zero (by omega)]

theorem abelianLifting_of_sqLifting (hD : AbelianDeRham) (hU : AbelianUnobstructed) (hS : SqLifting) :
    AbelianLifting := by

  have key : ∀ n : ℕ, ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (R₀ : Type) [CommRing R₀]
      (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I → NilExp κ (n + 1) →
        LiftObj κ π ∧ LiftHom κ π := by
    intro n
    induction n with
    | zero =>
      intro R _ I κ R₀ _ π hπ hker h
      obtain ⟨hI, rfl⟩ := NilExp.eq_sqDP h
      exact hS R I hI R₀ π hπ hker
    | succ n ih =>
      intro R _ I κ R₀ _ π hπ hker h
      obtain ⟨R₁, _, J, hJ, ρ, I₁, κ₁, π₁, st, h₁⟩ := exists_isStep_nilExp R R₀ I κ π hπ hker n h
      have hsq := hS R J hJ R₁ ρ st.surj st.kerJ
      have hih := ih R₁ I₁ κ₁ R₀ π₁ st.surj₁ st.ker₁ h₁
      exact ⟨GlobalTheory.T.liftAbelianScheme_along_squareZero_factorization hD hU R R₁ R₀ I J I₁ κ π hJ ρ κ₁ π₁ st hsq.1 hih.1,
        liftHom_of_isStep hD R R₁ R₀ I J I₁ κ π hJ ρ κ₁ π₁ st hsq.2 hih.2⟩
  intro R _ I κ hκ R₀ _ π hπ hker
  obtain ⟨N, hN⟩ := (isPDNilpotent_iff κ).1 hκ
  exact key N R I κ R₀ π hπ hker (hN.mono (Nat.le_succ N))

theorem abelianLifting_of_schemeLifts :
    AbelianDeRham → AbelianSchemeLifts → AbelianUnobstructed → AbelianLifting := by
  intro hD hL hU
  refine abelianLifting_of_sqLifting hD hU (GlobalTheory.T.squareZeroLifting_of_noetherian_case hD ?_)
  intro R _ _ I hI R₀ _ π hπ hk
  exact ⟨GlobalTheory.T.grothendieckMessingLiftAbelianScheme_of_squareZero hD R R₀ I hI π hπ hk (hL R I hI R₀ π hπ hk),
    GlobalTheory.T.grothendieckMessingLiftHomomorphism_of_squareZero hD R R₀ I hI π hπ hk (hL R I hI R₀ π hπ hk)⟩

end GlobalTheory.SqLift
