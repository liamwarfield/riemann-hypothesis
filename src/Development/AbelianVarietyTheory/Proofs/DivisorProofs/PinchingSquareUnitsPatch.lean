module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheaf

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PinchingSquareUnitsPatch
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedImmersionBaseChangeKerMemMapAffine
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedImmersionBaseChangeKerMemMapAffine
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace GlobalTheory

theorem closedImmersion_baseChange_ker_mem_map : ∀ (X X' Z Z' : Scheme.{0}) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z), IsPullback i' p' p i → IsAffineHom p → IsClosedImmersion i → ∀ W : X.Opens, IsAffineOpen W → ∀ s : Γ(X', p ⁻¹ᵁ W), (i'.app (p ⁻¹ᵁ W)).hom s = 0 → s ∈ Ideal.map (p.app W).hom (RingHom.ker (i.app W).hom) := by
  intro X X' Z Z' p i i' p' h hp hi W hW s hs
  set J : Ideal Γ(X', p ⁻¹ᵁ W) := Ideal.map (p.app W).hom (RingHom.ker (i.app W).hom) with hJ
  have hU' : IsAffineOpen (p ⁻¹ᵁ W) := hW.preimage p
  have hZ : IsAffineOpen (i ⁻¹ᵁ W) := hW.preimage i
  have hsurj : Function.Surjective (i.app W).hom := i.app_surjective W hW
  let ψ : Γ(X, W) →+* (Γ(X', p ⁻¹ᵁ W) ⧸ J) := (Ideal.Quotient.mk J).comp (p.app W).hom
  have hker : RingHom.ker (i.app W).hom ≤ RingHom.ker ψ := by
    intro a ha
    simp only [RingHom.mem_ker, ψ, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem _ ha
  let φ : Γ(Z, i ⁻¹ᵁ W) →+* (Γ(X', p ⁻¹ᵁ W) ⧸ J) :=
    (i.app W).hom.liftOfSurjective hsurj ⟨ψ, hker⟩
  have hφ : φ.comp (i.app W).hom = ψ := (i.app W).hom.liftOfRightInverse_comp _ _ _
  let e : Spec (CommRingCat.of (Γ(X', p ⁻¹ᵁ W) ⧸ J)) ⟶ X' :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ hU'.fromSpec
  let t : Spec (CommRingCat.of (Γ(X', p ⁻¹ᵁ W) ⧸ J)) ⟶ Z :=
    Spec.map (CommRingCat.ofHom φ) ≫ hZ.fromSpec
  have hw : e ≫ p = t ≫ i := by
    have h1 := IsAffineOpen.SpecMap_appLE_fromSpec p hW hU' le_rfl
    have h2 := IsAffineOpen.SpecMap_appLE_fromSpec i hW hZ le_rfl
    simp only [e, t, Category.assoc, ← h1, ← h2, ← Spec.map_comp, ← Scheme.Hom.app_eq_appLE]
    simp only [← Spec.map_comp_assoc]
    congr 2
    ext x
    exact (RingHom.congr_fun hφ x).symm
  let l := h.lift e t hw
  have hl : l ≫ i' = e := h.lift_fst e t hw
  have hle : (⊤ : (Spec (CommRingCat.of (Γ(X', p ⁻¹ᵁ W) ⧸ J))).Opens) ≤ e ⁻¹ᵁ (p ⁻¹ᵁ W) := by
    simp [e, Scheme.Hom.comp_preimage, hU'.fromSpec_preimage_self]
  have h0 : (e.appLE (p ⁻¹ᵁ W) ⊤ hle).hom s = 0 := by
    have key : ∀ (g : Spec (CommRingCat.of (Γ(X', p ⁻¹ᵁ W) ⧸ J)) ⟶ X') (hg : g = e) (hle' : ⊤ ≤ g ⁻¹ᵁ (p ⁻¹ᵁ W)),
        g.appLE (p ⁻¹ᵁ W) ⊤ hle' = e.appLE (p ⁻¹ᵁ W) ⊤ hle := by
      rintro g rfl _; rfl
    rw [← key (l ≫ i') hl (by rw [hl]; exact hle), Scheme.Hom.comp_appLE, CommRingCat.comp_apply, hs, map_zero]
  have h1 : (e.appLE (p ⁻¹ᵁ W) ⊤ hle).hom s = (Scheme.ΓSpecIso (CommRingCat.of (Γ(X', p ⁻¹ᵁ W) ⧸ J))).inv.hom (Ideal.Quotient.mk J s) := by
    simp only [e, Scheme.Hom.comp_appLE, hU'.fromSpec_app_self]
    rw [Category.assoc]
    erw [Scheme.Hom.map_appLE]
    rw [show ∀ hh, (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))).appLE ⊤ ⊤ hh = (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))).appTop from fun _ => (Scheme.Hom.app_eq_appLE _).symm]
    rw [← Scheme.ΓSpecIso_inv_naturality]
    rfl
  rw [h1] at h0
  have h2 : Ideal.Quotient.mk J s = 0 := by
    have := congrArg (Scheme.ΓSpecIso (CommRingCat.of (Γ(X', p ⁻¹ᵁ W) ⧸ J))).hom.hom h0
    simpa using this
  exact Ideal.Quotient.eq_zero_iff_mem.mp h2

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedImmersionBaseChangeKerMemMapAffineStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closedImmersion_baseChange_ker_mem_map_affine : ∀ (X X' Z Z' : Scheme.{0}) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z), IsPullback i' p' p i → IsAffineHom p → IsClosedImmersion i → ∀ W : X.Opens, IsAffineOpen W → ∀ s : Γ(X', p ⁻¹ᵁ W), (i'.app (p ⁻¹ᵁ W)).hom s = 0 → s ∈ Ideal.map (p.app W).hom (RingHom.ker (i.app W).hom) := by
  first | exact @GlobalTheory.closedImmersion_baseChange_ker_mem_map | exact GlobalTheory.closedImmersion_baseChange_ker_mem_map | (intros; apply GlobalTheory.closedImmersion_baseChange_ker_mem_map <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PinchingSquareUnitsPatch
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Pinch

theorem germ_app_congr {Y X : Scheme.{0}} {f g : Y ⟶ X} (e : f = g) (W : X.Opens) (y : Y) (hf : f y ∈ W)
    (hg : g y ∈ W) (s : Γ(X, W)) :
    Y.presheaf.germ (f ⁻¹ᵁ W) y hf ((f.app W).hom s) = Y.presheaf.germ (g ⁻¹ᵁ W) y hg ((g.app W).hom s) := by
  subst e; rfl

theorem affine_descent_units : ∀ (X X' Z Z' : Scheme.{0}) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z),
    IsPullback i' p' p i → IsAffineHom p → IsClosedImmersion i → GlobalTheory.Pinch.Cond p i →
    ∀ W : X.Opens, IsAffineOpen W → ∀ (u' : Γ(X', p ⁻¹ᵁ W)ˣ) (v : Γ(Z, i ⁻¹ᵁ W)ˣ),
      (∀ z : Z', p (i' z) ∈ W → gm i' z (p ⁻¹ᵁ W) u' = gm p' z (i ⁻¹ᵁ W) v) →
      ∃ u : Γ(X, W)ˣ, pullU p W u = u' := by
  intro X X' Z Z' p i i' p' h hp hi hc W hW u' v huv
  have hw : ∀ z : Z', p (i' z) = i (p' z) := fun z => by
    have := congrArg (fun f : Z' ⟶ X => f z) h.w
    simpa using this
  have claim : ∀ (s' : Γ(X', p ⁻¹ᵁ W)) (t : Γ(Z, i ⁻¹ᵁ W)),
      (∀ z : Z', ∀ hz : p (i' z) ∈ W,
        Z'.presheaf.germ (i' ⁻¹ᵁ (p ⁻¹ᵁ W)) z hz ((i'.app (p ⁻¹ᵁ W)).hom s') =
          Z'.presheaf.germ (p' ⁻¹ᵁ (i ⁻¹ᵁ W)) z (show i (p' z) ∈ W from hw z ▸ hz) ((p'.app (i ⁻¹ᵁ W)).hom t)) →
      ∃ s : Γ(X, W), (p.app W).hom s = s' := by
    intro s' t hst
    obtain ⟨s₀, rfl⟩ := Scheme.Hom.app_surjective i W hW t
    have hd : (i'.app (p ⁻¹ᵁ W)).hom (s' - (p.app W).hom s₀) = 0 := by
      apply TopCat.Presheaf.section_ext Z'.sheaf
      intro z hz
      show (Z'.presheaf.germ (i' ⁻¹ᵁ p ⁻¹ᵁ W) z hz).hom ((i'.app (p ⁻¹ᵁ W)).hom (s' - (p.app W).hom s₀)) =
        (Z'.presheaf.germ (i' ⁻¹ᵁ p ⁻¹ᵁ W) z hz).hom 0
      rw [map_sub, map_sub, map_zero, sub_eq_zero, hst z hz]
      have e1 := germ_app_congr h.w W z hz (show i (p' z) ∈ W from hw z ▸ hz) s₀
      exact e1.symm
    have hmem := GlobalTheory.T.closedImmersion_baseChange_ker_mem_map_affine X X' Z Z' p i i' p' h hp hi W hW _ hd
    have key : ∃ y, (i.app W).hom y = 0 ∧ (p.app W).hom y = s' - (p.app W).hom s₀ := by
      refine Submodule.span_induction (p := fun x _ => ∃ y, (i.app W).hom y = 0 ∧ (p.app W).hom y = x)
        ?_ ?_ ?_ ?_ hmem
      · rintro _ ⟨y, hy, rfl⟩
        exact ⟨y, hy, rfl⟩
      · exact ⟨0, map_zero _, map_zero _⟩
      · rintro _ _ _ _ ⟨y₁, h₁, e₁⟩ ⟨y₂, h₂, e₂⟩
        exact ⟨y₁ + y₂, by rw [map_add (f := _), h₁, h₂, add_zero], by rw [map_add (f := _), e₁, e₂]⟩
      · rintro r _ _ ⟨y, hy, rfl⟩
        obtain ⟨y', hy', e'⟩ := (hc W hW).2 y hy r
        exact ⟨y', hy', by rw [smul_eq_mul, mul_comm]; exact e'⟩
    obtain ⟨y, -, hy⟩ := key
    exact ⟨s₀ + y, by rw [map_add (f := _), hy, add_sub_cancel]⟩
  have germs : ∀ (a : Γ(X', p ⁻¹ᵁ W)ˣ) (b : Γ(Z, i ⁻¹ᵁ W)ˣ),
      (∀ z : Z', p (i' z) ∈ W → gm i' z (p ⁻¹ᵁ W) a = gm p' z (i ⁻¹ᵁ W) b) →
      ∃ s : Γ(X, W), (p.app W).hom s = a.val := by
    intro a b hab
    refine claim a.val b.val fun z hz => ?_
    have := congrArg Units.val (hab z hz)
    rwa [gm_val i' z _ hz, gm_val p' z _ (show i (p' z) ∈ W from hw z ▸ hz)] at this
  obtain ⟨x, hx⟩ := germs u' v huv
  obtain ⟨y, hy⟩ := germs u'⁻¹ v⁻¹ fun z hz => by rw [map_inv, map_inv, huv z hz]
  have hxy : x * y = 1 := (hc W hW).1 (by
    show (p.app W).hom (x * y) = (p.app W).hom 1
    rw [map_mul, map_one, hx, hy, Units.mul_inv])
  exact ⟨⟨x, y, hxy, by rw [mul_comm]; exact hxy⟩, Units.ext hx⟩

theorem pullU_injective {X X' : Scheme.{0}} (p : X' ⟶ X)
    (hp : ∀ W : X.Opens, IsAffineOpen W → Function.Injective (p.app W)) (W : X.Opens) :
    Function.Injective (pullU p W) := by
  intro a b hab
  apply unit_ext
  intro x hx
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx W.2
  have hle : V ≤ W := hVW
  have e : res hle a = res hle b := by
    apply Units.ext
    apply hp V hV
    have := congrArg Units.val (show pullU p V (res hle a) = pullU p V (res hle b) by
      rw [pullU_res₂, pullU_res₂, hab])
    exact this
  rw [← gm_res (𝟙 X) x hle hxV a, ← gm_res (𝟙 X) x hle hxV b, e]

theorem unitsPatch : ∀ (X X' Z Z' : Scheme.{0}) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z),
    IsPullback i' p' p i → IsAffineHom p → IsClosedImmersion i → GlobalTheory.Pinch.Cond p i →
    GlobalTheory.Pinch.UnitsPatch p i i' p' := by
  intro X X' Z Z' p i i' p' h hp hi hc W
  have hinj : ∀ V : X.Opens, Function.Injective (pullU p V) :=
    pullU_injective p (fun V hV => (hc V hV).1)
  refine ⟨hinj W, fun u' v huv => ?_⟩
  have hw : ∀ z : Z', p (i' z) = i (p' z) := fun z => by
    have := congrArg (fun f : Z' ⟶ X => f z) h.w
    simpa using this
  let J : Type := {V : X.Opens // IsAffineOpen V ∧ V ≤ W}
  have hsub : ∀ j : J, p ⁻¹ᵁ j.1 ≤ p ⁻¹ᵁ W := fun j x hx => j.2.2 hx
  have hsubZ : ∀ j : J, i ⁻¹ᵁ j.1 ≤ i ⁻¹ᵁ W := fun j x hx => j.2.2 hx
  have loc : ∀ j : J, ∃ a : Γ(X, j.1)ˣ, pullU p j.1 a = res (hsub j) u' := by
    intro j
    refine affine_descent_units X X' Z Z' p i i' p' h hp hi hc j.1 j.2.1 _ (res (hsubZ j) v) ?_
    intro z hz
    rw [gm_res i' z (hsub j) hz, gm_res p' z (hsubZ j) (show i (p' z) ∈ j.1 from hw z ▸ hz)]
    exact huv z (j.2.2 hz)
  choose a ha using loc

  have hD : ∀ j : J, ∀ y : X', ∀ hy : p y ∈ j.1, gm p y j.1 (a j) = gm (𝟙 X') y (p ⁻¹ᵁ W) u' := by
    intro j y hy
    rw [← gm_id_pull p y j.1 hy, ha j, gm_res (𝟙 X') y (hsub j) hy]
  obtain ⟨s, hs⟩ := glue_unit W (fun j : J => j.1) (fun j => j.2.2) (by
      intro x hx
      obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx W.2
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨V, hV, hVW⟩, hxV⟩) a (by
      intro j k x hx
      have hle1 : j.1 ⊓ k.1 ≤ j.1 := inf_le_left
      have hle2 : j.1 ⊓ k.1 ≤ k.1 := inf_le_right
      have e : res hle1 (a j) = res hle2 (a k) := by
        apply hinj
        apply unit_ext
        intro y hy
        rw [gm_id_pull p y _ hy, gm_id_pull p y _ hy, gm_res p y hle1 hy, gm_res p y hle2 hy,
          hD j y (hle1 hy), hD k y (hle2 hy)]
      rw [← gm_res (𝟙 X) x hle1 hx, ← gm_res (𝟙 X) x hle2 hx, e])
  refine ⟨s, unit_ext fun y hy => ?_⟩
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open (show p y ∈ W from hy) W.2
  let j : J := ⟨V, hV, hVW⟩
  rw [gm_id_pull p y W hy, ← gm_res p y j.2.2 hxV, hs j]
  exact hD j y hxV

end GlobalTheory.Pinch
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PinchingSquareUnitsPatchStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pinchingSquare_unitsPatch : ∀ (X X' Z Z' : Scheme.{0}) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z), IsPullback i' p' p i → IsAffineHom p → IsClosedImmersion i → GlobalTheory.Pinch.Cond p i → GlobalTheory.Pinch.UnitsPatch p i i' p' := by
  first | exact @GlobalTheory.Pinch.unitsPatch | exact GlobalTheory.Pinch.unitsPatch | (intros; apply GlobalTheory.Pinch.unitsPatch <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConductorSquareFlatBaseChangeSchemes
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConductorSquareFlatBaseChangeSchemes
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Pinch.FlatSq

open TensorProduct

theorem inj_of_isPushout {A B F G : Type} [CommRing A] [CommRing B] [CommRing F] [CommRing G]
    (f : A →+* F) (g : A →+* B) (h : F →+* G) (k : B →+* G)
    (sq : IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom g) (CommRingCat.ofHom h) (CommRingCat.ofHom k))
    (hf : f.Flat) (hg : Function.Injective g) : Function.Injective h := by
  letI := f.toAlgebra
  letI := g.toAlgebra
  letI := h.toAlgebra
  letI := k.toAlgebra
  letI : Algebra A G := (h.comp f).toAlgebra
  haveI : IsScalarTower A F G := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower A B G := IsScalarTower.of_algebraMap_eq (fun a => by
    have := congrArg (fun φ => (CommRingCat.Hom.hom φ) a) sq.w
    simpa [RingHom.algebraMap_toAlgebra] using this)
  haveI : Module.Flat A F := hf
  have hP : Algebra.IsPushout A F B G := (CommRingCat.isPushout_iff_isPushout).1 sq
  have hP' : Algebra.IsPushout A B F G := hP.symm
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  have e1 : Algebra.IsPushout.equiv A B F G ((1 : B) ⊗ₜ x) = 0 := by
    rw [Algebra.IsPushout.equiv_tmul]; simpa [RingHom.algebraMap_toAlgebra] using hx
  have e2 : ((1 : B) ⊗ₜ[A] x) = 0 := by
    simpa using (Algebra.IsPushout.equiv A B F G).injective (e1.trans (map_zero _).symm)
  have hinj := Module.Flat.rTensor_preserves_injective_linearMap (M := F) (Algebra.linearMap A B) hg
  have e3 : LinearMap.rTensor F (Algebra.linearMap A B) ((1 : A) ⊗ₜ x) = 0 := by simpa using e2
  have e4 : ((1 : A) ⊗ₜ[A] x) = 0 := hinj (e3.trans (map_zero _).symm)
  simpa using congrArg (TensorProduct.lid A F) e4

end GlobalTheory.Pinch.FlatSq

namespace GlobalTheory.Pinch.FlatSq

open TensorProduct

theorem ideal_mul_of_isPushout {A B F G : Type} [CommRing A] [CommRing B] [CommRing F] [CommRing G]
    (f : A →+* F) (g : A →+* B) (h : F →+* G) (k : B →+* G)
    (sq : IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom g) (CommRingCat.ofHom h) (CommRingCat.ofHom k))
    (J : Ideal A) (hJ : ∀ a ∈ J, ∀ b : B, ∃ a' ∈ J, g a' = g a * b) :
    ∀ x ∈ J.map f, ∀ r : G, ∃ y ∈ J.map f, h y = h x * r := by
  have hw : ∀ a, k (g a) = h (f a) := fun a => by
    have := congrArg (fun φ => (CommRingCat.Hom.hom φ) a) sq.w
    simpa using this.symm
  have hQ : ∀ x ∈ J.map f, ∀ b : B, ∃ y ∈ J.map f, h y = h x * k b := by
    intro x hx
    change x ∈ Ideal.span _ at hx
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, ha, rfl⟩ := hz
      intro b
      obtain ⟨a', ha', e⟩ := hJ a ha b
      refine ⟨f a', Ideal.mem_map_of_mem f ha', ?_⟩
      rw [← hw, ← hw, e, map_mul]
    | zero => intro b; exact ⟨0, Ideal.zero_mem _, by simp⟩
    | add z w _ _ hz hw' =>
      intro b
      obtain ⟨y1, hy1, e1⟩ := hz b
      obtain ⟨y2, hy2, e2⟩ := hw' b
      exact ⟨y1 + y2, Ideal.add_mem _ hy1 hy2, by rw [map_add (f := _), e1, e2, map_add (f := _), add_mul]⟩
    | smul m z _ hz =>
      intro b
      obtain ⟨y1, hy1, e1⟩ := hz b
      refine ⟨m * y1, Ideal.mul_mem_left _ m hy1, ?_⟩
      rw [smul_eq_mul, map_mul, e1, map_mul]; ring
  letI := f.toAlgebra
  letI := g.toAlgebra
  letI := h.toAlgebra
  letI := k.toAlgebra
  letI : Algebra A G := (h.comp f).toAlgebra
  haveI : IsScalarTower A F G := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower A B G := IsScalarTower.of_algebraMap_eq (fun a => (hw a).symm)
  have hP : Algebra.IsPushout A F B G := (CommRingCat.isPushout_iff_isPushout).1 sq
  have hP' : Algebra.IsPushout A B F G := hP.symm
  intro x hx r
  induction r using hP'.out.inductionOn with
  | tmul m =>
    refine ⟨x * m, Ideal.mul_mem_right _ _ hx, ?_⟩
    rw [map_mul]; rfl
  | smul b n hn =>
    obtain ⟨y1, hy1, e1⟩ := hn
    obtain ⟨y, hy, e⟩ := hQ y1 hy1 b
    refine ⟨y, hy, ?_⟩
    rw [e, e1, Algebra.smul_def, RingHom.algebraMap_toAlgebra]; ring
  | add n1 n2 h1 h2 =>
    obtain ⟨y1, hy1, e1⟩ := h1
    obtain ⟨y2, hy2, e2⟩ := h2
    exact ⟨y1 + y2, Ideal.add_mem _ hy1 hy2, by rw [map_add (f := _), e1, e2, mul_add]⟩

theorem ker_le_of_isPushout {A Q F G : Type} [CommRing A] [CommRing Q] [CommRing F] [CommRing G]
    (f : A →+* F) (q : A →+* Q) (h : F →+* G) (k : Q →+* G)
    (sq : IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom q) (CommRingCat.ofHom h) (CommRingCat.ofHom k))
    (hq : Function.Surjective q) (x : F) (hx : h x = 0) : x ∈ (RingHom.ker q).map f := by
  letI := f.toAlgebra
  letI := q.toAlgebra
  letI := h.toAlgebra
  letI := k.toAlgebra
  letI : Algebra A G := (h.comp f).toAlgebra
  haveI : IsScalarTower A F G := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower A Q G := IsScalarTower.of_algebraMap_eq (fun a => by
    have := congrArg (fun φ => (CommRingCat.Hom.hom φ) a) sq.w
    simpa [RingHom.algebraMap_toAlgebra] using this)
  have hP : Algebra.IsPushout A F Q G := (CommRingCat.isPushout_iff_isPushout).1 sq
  have hs : Function.Surjective (Algebra.ofId A Q) := hq
  let e1 := Algebra.TensorProduct.quotIdealMapEquivTensorQuot F (RingHom.ker (Algebra.ofId A Q))
  let e2 : F ⊗[A] (A ⧸ RingHom.ker (Algebra.ofId A Q)) ≃ₐ[A] F ⊗[A] Q :=
    Algebra.TensorProduct.congr AlgEquiv.refl (Ideal.quotientKerAlgEquivOfSurjective hs)
  let e3 := Algebra.IsPushout.equiv A F Q G
  have key : e3 (e2 (e1 (Ideal.Quotient.mk _ x))) = 0 := by
    rw [Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk]
    simp only [e2, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul, AlgEquiv.coe_algHom, map_one]
    rw [Algebra.IsPushout.equiv_tmul]
    simpa [RingHom.algebraMap_toAlgebra] using hx
  have : Ideal.Quotient.mk (Ideal.map (algebraMap A F) (RingHom.ker (Algebra.ofId A Q))) x = 0 := by
    apply e1.injective; apply e2.injective; apply e3.injective
    rw [key]; simp
  rw [Ideal.Quotient.eq_zero_iff_mem] at this
  exact this

end GlobalTheory.Pinch.FlatSq

namespace GlobalTheory.Pinch.FlatSq

theorem spMap_appLE_apply {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R')
    (e : (⊤ : (Sp R').Opens) ≤ spMap φ ⁻¹ᵁ ⊤) (a : Γ(Sp R, ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of R')).hom (((spMap φ).appLE ⊤ ⊤ e).hom a) =
      φ ((Scheme.ΓSpecIso (CommRingCat.of R)).hom a) := by
  have h1 : (spMap φ).appLE ⊤ ⊤ e = (spMap φ).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  have := congrArg (fun t => t.hom a) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ))
  rw [h1]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
  exact this

theorem cond_of_flat (R : Type) [CommRing R] (R' : Type) [CommRing R'] [Algebra R R']
    (hinj : Function.Injective (algebraMap R R')) (c : Ideal R)
    (hc : ∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r)
    (X X' Z : Scheme.{0}) (u : X ⟶ Sp R) (p : X' ⟶ X) (u' : X' ⟶ Sp R') (i : Z ⟶ X) (v : Z ⟶ Sp (R ⧸ c))
    (hu : Flat u) (hp : IsPullback p u' u (spMap (algebraMap R R')))
    (hi : IsPullback i v u (spMap (Ideal.Quotient.mk c))) : GlobalTheory.Pinch.Cond p i := by
  intro W hW
  have poP := (isIso_pushoutSection_iff hp (US := ⊤) (UT := ⊤) (UX := W) (UY := p ⁻¹ᵁ W) le_top
    le_top (by simp)).mp (isIso_pushoutSection_of_isAffineOpen hp _ _ _ (isAffineOpen_top _)
    (isAffineOpen_top _) hW)
  have poZ := (isIso_pushoutSection_iff hi (US := ⊤) (UT := ⊤) (UX := W) (UY := i ⁻¹ᵁ W) le_top
    le_top (by simp)).mp (isIso_pushoutSection_of_isAffineOpen hi _ _ _ (isAffineOpen_top _)
    (isAffineOpen_top _) hW)
  have hfl : (u.appLE ⊤ W le_top).hom.Flat :=
    HasRingHomProperty.appLE (P := @Flat) u hu ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ le_top
  let eR := (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv
  let eR' := (Scheme.ΓSpecIso (CommRingCat.of R')).commRingCatIsoToRingEquiv
  let eQ := (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ c))).commRingCatIsoToRingEquiv
  let gA := ((spMap (algebraMap R R')).appLE ⊤ ⊤ le_top).hom
  let qA := ((spMap (Ideal.Quotient.mk c)).appLE ⊤ ⊤ le_top).hom
  have hg : ∀ a, eR' (gA a) = algebraMap R R' (eR a) := fun a => spMap_appLE_apply _ _ a
  have hq : ∀ a, eQ (qA a) = Ideal.Quotient.mk c (eR a) := fun a => spMap_appLE_apply _ _ a
  have gA_inj : Function.Injective gA := by
    intro a b hab
    apply eR.injective; apply hinj
    rw [← hg, ← hg, hab]
  have qA_surj : Function.Surjective qA := by
    intro t
    obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (eQ t)
    refine ⟨eR.symm z, eQ.injective ?_⟩
    rw [hq, RingEquiv.apply_symm_apply, hz]
  let J := RingHom.ker qA
  have hJ : ∀ a ∈ J, ∀ b, ∃ a' ∈ J, gA a' = gA a * b := by
    intro a ha b
    have hx : eR a ∈ c := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← hq, RingHom.mem_ker.1 ha, map_zero]
    obtain ⟨y, hy, e⟩ := hc (eR a) hx (eR' b)
    refine ⟨eR.symm y, ?_, eR'.injective ?_⟩
    · rw [RingHom.mem_ker]; apply eQ.injective
      rw [hq, RingEquiv.apply_symm_apply, map_zero, Ideal.Quotient.eq_zero_iff_mem]; exact hy
    · rw [hg, RingEquiv.apply_symm_apply, e, map_mul, hg]
  refine ⟨?_, ?_⟩
  · rw [Scheme.Hom.app_eq_appLE]
    exact inj_of_isPushout _ _ _ _ poP hfl gA_inj
  · intro x hx r
    rw [Scheme.Hom.app_eq_appLE] at hx
    have hxJ := ker_le_of_isPushout _ _ _ _ poZ qA_surj x hx
    obtain ⟨y, hy, e⟩ := ideal_mul_of_isPushout _ _ _ _ poP J hJ x hxJ r
    refine ⟨y, ?_, ?_⟩
    · rw [Scheme.Hom.app_eq_appLE]
      have hle : J.map (u.appLE ⊤ W le_top).hom ≤ RingHom.ker (i.appLE W (i ⁻¹ᵁ W) le_rfl).hom := by
        rw [Ideal.map_le_iff_le_comap]
        intro a ha
        rw [Ideal.mem_comap, RingHom.mem_ker]
        have := congrArg (fun φ => (CommRingCat.Hom.hom φ) a) poZ.w
        simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
        have h0 : qA a = 0 := RingHom.mem_ker.1 ha
        simp only [qA] at h0
        rw [this, h0, map_zero]
      exact hle hy
    · rw [Scheme.Hom.app_eq_appLE]; exact e

end GlobalTheory.Pinch.FlatSq
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConductorSquareFlatBaseChangeSchemesStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conductorSquare_flat_baseChange_schemes : ∀ (R : Type) [CommRing R] (R' : Type) [CommRing R'] [Algebra R R'], Function.Injective (algebraMap R R') → ∀ c : Ideal R, (∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r) → ∀ (X X' Z : Scheme.{0}) (u : X ⟶ Sp R) (p : X' ⟶ X) (u' : X' ⟶ Sp R') (i : Z ⟶ X) (v : Z ⟶ Sp (R ⧸ c)), Flat u → IsPullback p u' u (spMap (algebraMap R R')) → IsPullback i v u (spMap (Ideal.Quotient.mk c)) → GlobalTheory.Pinch.Cond p i := by
  first | exact @GlobalTheory.Pinch.FlatSq.cond_of_flat | exact GlobalTheory.Pinch.FlatSq.cond_of_flat | (intros; apply GlobalTheory.Pinch.FlatSq.cond_of_flat <;> assumption)
end
end
