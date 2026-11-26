module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MonodromyVanishesWeilTwistIff

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.AffineCechOpenFunctionFieldGeneric
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD GlobalTheory.CechDR GlobalTheory.HodgeCoh ReciprocityTheory.ChartRestriction.G.Geo.Tor

private theorem smooth_sections_of_affine_open (d : ℕ) (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp ℂ)
    [SmoothOfRelativeDimension d p] (V : Z.Opens) (hV : IsAffineOpen V) :
    Algebra.Smooth ℂ (Sec p V) := by
  have h1 := HasRingHomProperty.appLE @Smooth p (SmoothOfRelativeDimension.smooth d p)
    ⟨⊤, isAffineOpen_top (Sp ℂ)⟩ ⟨V, hV⟩ (by simp)
  have h2 : RingHom.Smooth (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom :=
    RingHom.Smooth.of_bijective (ConcreteCategory.bijective_of_isIso _)
  exact RingHom.Smooth.comp h2 h1

theorem UpperTheory.affineCechOpen_functionField_generic :
    ∀ (d : ℕ) (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp ℂ) [SmoothOfRelativeDimension d p] [inst : Algebra ℂ Z.functionField] (ι : Type) (U : ι → Z.Opens) (B : Finset ι → Subalgebra ℂ Z.functionField) (hinst : inst = ffAlg p) (hU : IsAffCover p U B) (a : ℕ) (s : Finset ι) (hs : s.Nonempty) (hV : IsAffineOpen (cechOpen ⊤ U s)) (hη : genericPoint Z ∈ cechOpen ⊤ U s), letI := algΓ p; Function.Injective (formGermI p a hV hη hinst) ∧ LinearMap.range (formGermI p a hV hη hinst) = omB ℂ Z.functionField (B s) a := by
  intro d Z _ p _ inst ι U B hinst hU a s hs hV hη
  letI := algΓ p
  subst hinst
  letI : Algebra ℂ Z.functionField := ffAlg p
  set V := cechOpen ⊤ U s with hVdef
  letI : Algebra (Sec p V) Z.functionField := (germSec p hη).toAlgebra
  haveI : IsScalarTower ℂ (Sec p V) Z.functionField :=
    IsScalarTower.of_algebraMap_eq (fun r => ((semiHom_germSec p hη).map_algebraMap r).symm)
  haveI : Nonempty V := ⟨⟨_, hη⟩⟩
  haveI : IsFractionRing (Sec p V) Z.functionField :=
    functionField_isFractionRing_of_isAffineOpen Z V hV
  haveI := smooth_sections_of_affine_open d Z p V hV
  have hring : ∀ y, y ∈ B s ↔ ∃ f : Sec p V, algebraMap (Sec p V) Z.functionField f = y := by
    intro y
    rw [hU.ring s hs y]
    have hVeq : s.inf U = V := by
      rw [hVdef]
      simp [cechOpen, Finset.inf_eq_iInf]
    have gen : ∀ (W W' : Z.Opens) (_ : W = W') (h1 : genericPoint Z ∈ W)
        (h2 : genericPoint Z ∈ W'), ((∃ f, (Z.presheaf.germ W _ h1).hom f = y) ↔
          ∃ f, (Z.presheaf.germ W' _ h2).hom f = y) := by
      rintro W W' rfl h1 h2
      rfl
    exact gen _ _ hVeq _ hη
  obtain ⟨hinj, hom⟩ := mOm_injective_and_omB ℂ Z.functionField (Sec p V) (B s) hring a
  have hform : ∀ x, formGermI p a hV hη rfl x =
      ↑((semiHom_algebraMap ℂ (Sec p V) Z.functionField).mOm a
        ((toOmEquiv p a hV).symm ((sectionsOn.toΓ (Omega p a) V) x))) := fun x => rfl
  constructor
  · intro x y hxy
    rw [hform, hform] at hxy
    have h3 := hinj (Subtype.ext hxy)
    exact (sectionsOn.toΓ _ _).injective ((toOmEquiv p a hV).symm.injective h3)
  · ext y
    rw [LinearMap.mem_range, hom y]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨_, (hform x).symm⟩
    · rintro ⟨z, rfl⟩
      refine ⟨(sectionsOn.toΓ (Omega p a) V).symm (toOmEquiv p a hV z), ?_⟩
      rw [hform, AddEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
end

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD GlobalTheory.CechDR GlobalTheory.HodgeCoh ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option autoImplicit false

noncomputable section

namespace UpperTheory.GenericCoverClass

section Cover

variable {ι : Type} {Z : Scheme.{0}} [IsIntegral Z] {p : Z ⟶ Sp ℂ} [inst : Algebra ℂ Z.functionField]
  {U : ι → Z.Opens} {B : Finset ι → Subalgebra ℂ Z.functionField}

theorem cover_affine (hU : IsAffCover p U B) {s : Finset ι} (h : s.Nonempty) :
    IsAffineOpen (cechOpen ⊤ U s) := by
  rw [cechOpen_eq_inf, top_inf_eq]
  exact hU.affine s h

theorem cover_generic (hU : IsAffCover p U B) (s : Finset ι) :
    genericPoint Z ∈ cechOpen ⊤ U s := by
  rw [cechOpen_eq_inf, top_inf_eq]
  exact hU.ne s

theorem cover_biInf (hU : IsAffCover p U B) (s : Finset ι) (h : s.Nonempty) :
    IsAffineOpen (⨅ i ∈ s, U i) := by
  rw [← Finset.inf_eq_iInf]
  exact hU.affine s h


variable (p) in
def gm (hinst : inst = ffAlg p) (hU : IsAffCover p U B) (a : ℕ) (s : Finset ι) :
    letI := algΓ p; (cechCube ℂ (Omega p a) ⊤ U).obj s →ₗ[ℂ] DR ℂ Z.functionField :=
  letI := algΓ p
  if h : s.Nonempty then formGermI p a (cover_affine hU h) (cover_generic hU s) hinst else 0

theorem gm_pos (hinst : inst = ffAlg p) (hU : IsAffCover p U B) (a : ℕ) {s : Finset ι}
    (h : s.Nonempty) :
    gm p hinst hU a s = formGermI p a (cover_affine hU h) (cover_generic hU s) hinst :=
  dif_pos h

theorem gm_spec (d : ℕ) [SmoothOfRelativeDimension d p] (hinst : inst = ffAlg p)
    (hU : IsAffCover p U B) (a : ℕ) :
    letI := algΓ p
    (∀ s, s.Nonempty → Function.Injective (gm p hinst hU a s)) ∧
    (∀ s, s.Nonempty → LinearMap.range (gm p hinst hU a s) = omB ℂ Z.functionField (B s) a) ∧
    (∀ s t (h : s ⊆ t), s.Nonempty → ∀ y,
      gm p hinst hU a t (Cube.res (cechCube ℂ (Omega p a) ⊤ U) h y) = gm p hinst hU a s y) := by
  refine ⟨fun s hs => ?_, fun s hs => ?_, fun s t h hs y => ?_⟩
  · rw [gm_pos hinst hU a hs]
    exact (affineCechOpen_functionField_generic d Z p ι U B hinst hU a s hs _ _).1
  · rw [gm_pos hinst hU a hs]
    exact (affineCechOpen_functionField_generic d Z p ι U B hinst hU a s hs _ _).2
  · have ht : t.Nonempty := hs.mono h
    rw [gm_pos hinst hU a ht, gm_pos hinst hU a hs]
    have hle : cechOpen ⊤ U t ≤ cechOpen ⊤ U s := by
      rw [cechOpen_eq_inf, cechOpen_eq_inf]
      exact inf_le_inf_left _ (Finset.inf_mono h)
    exact T.genericGerm_differentialForm_restrict_affineOpen Z p hinst a _ _ _ _ _ _ hle y

end Cover

section Cmp

variable (d : ℕ) {Z : Scheme.{0}} [IsIntegral Z] (p : Z ⟶ Sp ℂ) [SmoothOfRelativeDimension d p]
  [inst : Algebra ℂ Z.functionField] {ι : Type} [LinearOrder ι] [Fintype ι] {U : ι → Z.Opens}
  {B : Finset ι → Subalgebra ℂ Z.functionField}

include d

theorem cube_exists (hinst : inst = ffAlg p) (hU : IsAffCover p U B) (a b : ℕ) :
    letI := algΓ p
    ∃ e : (cechComplex (cechCube ℂ (Omega p a) ⊤ U)).homology b ≃ₗ[ℂ]
        (GlobalTheory.PD.cech fun I => omB ℂ Z.functionField (B I) a).H (b : ℤ),
      (∀ (z : LinearMap.ker (Cube.d (cechCube ℂ (Omega p a) ⊤ U) (b + 1)))
        (w : (GlobalTheory.PD.cech fun I => omB ℂ Z.functionField (B I) a).Z (b : ℤ)),
        (∀ t : {s : Finset ι // s.card = b + 1},
          (w : Finset ι → DR ℂ Z.functionField) t.1 = gm p hinst hU a t.1 (z.1 t)) →
        e (cechClass _ b z) = Submodule.Quotient.mk w) ∧
      (∀ z : LinearMap.ker (Cube.d (cechCube ℂ (Omega p a) ⊤ U) (b + 1)),
        ∃ w : (GlobalTheory.PD.cech fun I => omB ℂ Z.functionField (B I) a).Z (b : ℤ),
          ∀ t : {s : Finset ι // s.card = b + 1},
            (w : Finset ι → DR ℂ Z.functionField) t.1 = gm p hinst hU a t.1 (z.1 t)) ∧
      (∀ (x : Cube.Term (cechCube ℂ (Omega p a) ⊤ U) (b + 1))
        (w : (GlobalTheory.PD.cech fun I => omB ℂ Z.functionField (B I) a).Z (b : ℤ)),
        (∀ t : {s : Finset ι // s.card = b + 1},
          (w : Finset ι → DR ℂ Z.functionField) t.1 = gm p hinst hU a t.1 (x t)) →
        Cube.d (cechCube ℂ (Omega p a) ⊤ U) (b + 1) x = 0) := by
  letI := algΓ p
  have hs := gm_spec (p := p) d hinst hU a
  exact GlobalTheory.T.cechHomologyEquivFamAlt ℂ ι (DR ℂ Z.functionField) (fun I => omB ℂ Z.functionField (B I) a)
    (cechCube ℂ (Omega p a) ⊤ U) (gm p hinst hU a) hs.1 hs.2.1 hs.2.2 b

def cmp (hinst : inst = ffAlg p) (hU : IsAffCover p U B) (a b : ℕ) :
    hodgeH p a b ≃ₗ[ℂ] (GlobalTheory.PD.cech fun I => omB ℂ Z.functionField (B I) a).H b :=
  letI := algΓ p
  (cechHEquivCoh ℂ hU.cover (cover_biInf hU) (Omega p a) b).symm ≪≫ₗ
    Classical.choose (cube_exists d p hinst hU a b)

theorem cmp_class (hinst : inst = ffAlg p) (hU : IsAffCover p U B) (a b : ℕ) :
    letI := algΓ p
    ∀ (z : LinearMap.ker (Cube.d (cechCube ℂ (Omega p a) ⊤ U) (b + 1)))
      (w : (GlobalTheory.PD.cech fun I => omB ℂ Z.functionField (B I) a).Z (b : ℤ)),
      (∀ t : {s : Finset ι // s.card = b + 1},
        (w : Finset ι → DR ℂ Z.functionField) t.1 = gm p hinst hU a t.1 (z.1 t)) →
      cmp d p hinst hU a b (cechHEquivCoh ℂ hU.cover (cover_biInf hU) (Omega p a) b
        (cechClass _ b z)) = Submodule.Quotient.mk w := by
  letI := algΓ p
  intro z w h
  exact (congrArg (DFunLike.coe (Classical.choose (cube_exists d p hinst hU a b)))
    (LinearEquiv.symm_apply_apply (cechHEquivCoh ℂ hU.cover (cover_biInf hU) (Omega p a) b)
      (cechClass _ b z))).trans ((Classical.choose_spec (cube_exists d p hinst hU a b)).1 z w h)

end Cmp

end UpperTheory.GenericCoverClass
