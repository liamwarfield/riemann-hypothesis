module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivHomDivisibleByPowOfKillsPowTorsion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NondegeneratePairingOfGenericFibre
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PinchingSquareUnitsPatch
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleLocalGeneratorNearFiniteSet
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLiftSystemFiltrationSupIffHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPushoutLocalizedPresentationBaseChange

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalGeneratorFiniteCoverNearPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalGeneratorFiniteCoverNearPoint
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Pinch

theorem locGen_near_fibre_of_finite : (∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (W : X.Opens), IsAffineOpen W → ∀ F : Set X, F.Finite → F ⊆ W → ∃ (V : X.Opens) (a : ∀ k, Γ(X, V ⊓ L.U k)ˣ), F ⊆ V ∧ GlobalTheory.Pinch.LocGen L V a) → ∀ (X X' : Scheme.{0}) (p : X' ⟶ X), IsFinite p → ∀ (L : LB X'), L.IsLB → ∀ x : X, ∃ (W : X.Opens) (a : ∀ k, Γ(X', p ⁻¹ᵁ W ⊓ L.U k)ˣ), x ∈ W ∧ GlobalTheory.Pinch.LocGen L (p ⁻¹ᵁ W) a := by
  intro H X X' p hp L hL x
  obtain ⟨W₀, hW₀, hxW₀, -⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) (show x ∈ (⊤ : X.Opens) from trivial)
  have hA : IsAffineOpen (p ⁻¹ᵁ W₀) := IsAffineOpen.preimage hW₀ p
  have hF : (p.base ⁻¹' {x}).Finite := Scheme.Hom.finite_preimage_singleton p x
  have hFW : p.base ⁻¹' {x} ⊆ (p ⁻¹ᵁ W₀ : Set X') := by
    intro y hy
    show p.base y ∈ W₀
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hy
    rw [hy]; exact hxW₀
  obtain ⟨V, a, hFV, ha⟩ := H X' L hL (p ⁻¹ᵁ W₀) hA _ hF hFW
  have hcl : IsClosed (p.base '' (V : Set X')ᶜ) := p.isClosedMap _ V.isOpen.isClosed_compl
  let W : X.Opens := ⟨(p.base '' (V : Set X')ᶜ)ᶜ, hcl.isOpen_compl⟩
  have hWV : p ⁻¹ᵁ W ≤ V := by
    intro y hy
    by_contra h
    exact hy ⟨y, h, rfl⟩
  have hxW : x ∈ W := by
    rintro ⟨y, hy, hyx⟩
    exact hy (hFV (show p.base y = x from hyx))
  refine ⟨W, fun k ↦ res (inf_le_inf_right _ hWV) (a k), hxW, ?_⟩
  intro y k k' hy hk hk'
  rw [gm_res (𝟙 X') y (inf_le_inf_right _ hWV) ⟨hy, hk⟩, gm_res (𝟙 X') y (inf_le_inf_right _ hWV) ⟨hy, hk'⟩]
  exact ha y k k' (hWV hy) hk hk'

end GlobalTheory.Pinch
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalGeneratorFiniteCoverNearPointStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_generator_finite_cover_near_point : (∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (W : X.Opens), IsAffineOpen W → ∀ F : Set X, F.Finite → F ⊆ W → ∃ (V : X.Opens) (a : ∀ k, Γ(X, V ⊓ L.U k)ˣ), F ⊆ V ∧ GlobalTheory.Pinch.LocGen L V a) → ∀ (X X' : Scheme.{0}) (p : X' ⟶ X), IsFinite p → ∀ (L : LB X'), L.IsLB → ∀ x : X, ∃ (W : X.Opens) (a : ∀ k, Γ(X', p ⁻¹ᵁ W ⊓ L.U k)ˣ), x ∈ W ∧ GlobalTheory.Pinch.LocGen L (p ⁻¹ᵁ W) a := by
  first | exact @GlobalTheory.Pinch.locGen_near_fibre_of_finite | exact GlobalTheory.Pinch.locGen_near_fibre_of_finite | (intros; apply GlobalTheory.Pinch.locGen_near_fibre_of_finite <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitLiftClosedSubschemeNearFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitLiftClosedSubschemeNearFibre
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Pinch

theorem unit_lift_near_fibre : ∀ (X X' Z Z' : Scheme.{0}) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z), IsPullback i' p' p i → IsFinite p → IsClosedImmersion i → ∀ (W : X.Opens) (x : X), x ∈ W → ∀ u : Γ(Z', i' ⁻¹ᵁ (p ⁻¹ᵁ W))ˣ, ∃ (W' : X.Opens) (u' : Γ(X', p ⁻¹ᵁ W')ˣ), W' ≤ W ∧ x ∈ W' ∧ ∀ z : Z', p (i' z) ∈ W' → gm i' z (p ⁻¹ᵁ W') u' = gm (𝟙 Z') z (i' ⁻¹ᵁ (p ⁻¹ᵁ W)) u := by
  intro X X' Z Z' p i i' p' h hp hi W x hx u
  have hi' : IsClosedImmersion i' := MorphismProperty.of_isPullback h.flip hi
  have hw : ∀ z : Z', p (i' z) = i (p' z) := fun z => by
    rw [← Scheme.Hom.comp_apply, h.w, Scheme.Hom.comp_apply]
  by_cases hxr : x ∈ Set.range i
  swap
  · refine ⟨W ⊓ ⟨(Set.range i)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩, 1, inf_le_left, ⟨hx, hxr⟩,
      fun z hz => ?_⟩
    exact absurd ⟨p' z, (hw z).symm⟩ hz.2
  obtain ⟨z0, hz0⟩ := hxr
  obtain ⟨W₀, hW₀, hxW₀, hW₀W⟩ := exists_isAffineOpen_mem_and_subset hx
  have hle0 : W₀ ≤ W := hW₀W
  have hA : IsAffineOpen (p ⁻¹ᵁ W₀) := IsAffineHom.isAffine_preimage _ hW₀
  let u0 : Γ(Z', i' ⁻¹ᵁ (p ⁻¹ᵁ W₀)) :=
    (Z'.presheaf.map (homOfLE (i'.preimage_mono (p.preimage_mono hle0))).op).hom u.val
  have hu0 : IsUnit u0 := (Units.isUnit u).map _
  obtain ⟨t, ht⟩ := Scheme.Hom.app_surjective i' (p ⁻¹ᵁ W₀) hA u0
  have hC : IsClosed ((X'.basicOpen t : Set X')ᶜ) := (X'.basicOpen t).isOpen.isClosed_compl
  let W' : X.Opens := W₀ ⊓ ⟨(p '' (X'.basicOpen t : Set X')ᶜ)ᶜ, (p.isClosedMap _ hC).isOpen_compl⟩
  have hsub : p ⁻¹ᵁ W' ≤ X'.basicOpen t := fun y hy => by
    by_contra hc
    exact hy.2 ⟨y, hc, rfl⟩
  have hx' : x ∈ W' := by
    refine ⟨hxW₀, ?_⟩
    rintro ⟨y, hyC, hy⟩
    obtain ⟨z', hz'1, -⟩ := Scheme.exists_preimage_of_isPullback h y z0 (hy.trans hz0.symm)
    apply hyC
    have hz'W : z' ∈ i' ⁻¹ᵁ (p ⁻¹ᵁ W₀) := by
      show p (i' z') ∈ W₀
      rw [hz'1, hy]; exact hxW₀
    have : z' ∈ i' ⁻¹ᵁ X'.basicOpen t := by
      rw [Scheme.preimage_basicOpen, ht, Scheme.basicOpen_of_isUnit _ hu0]
      exact hz'W
    rw [← hz'1]; exact this
  have hle' : p ⁻¹ᵁ W' ≤ p ⁻¹ᵁ W₀ := hsub.trans (X'.basicOpen_le t)
  have hunit : IsUnit ((X'.presheaf.map (homOfLE hle').op).hom t) := by
    have := (X'.toRingedSpace.isUnit_res_basicOpen t).map (X'.presheaf.map (homOfLE hsub).op).hom
    convert this using 1
    change _ = (X'.presheaf.map (homOfLE (X'.basicOpen_le t)).op ≫ X'.presheaf.map (homOfLE hsub).op).hom t
    rw [← Functor.map_comp]
    rfl
  refine ⟨W', hunit.unit, inf_le_left.trans hle0, hx', fun z hz => ?_⟩
  have hle2 : i' ⁻¹ᵁ (p ⁻¹ᵁ W') ≤ i' ⁻¹ᵁ (p ⁻¹ᵁ W) :=
    i'.preimage_mono (p.preimage_mono (inf_le_left.trans hle0))
  rw [← gm_id_pull i' z (p ⁻¹ᵁ W') hz, ← gm_res (𝟙 Z') z hle2 hz]
  congr 1
  apply Units.ext
  show (i'.app (p ⁻¹ᵁ W')).hom ((X'.presheaf.map (homOfLE hle').op).hom t) =
    (Z'.presheaf.map (homOfLE hle2).op).hom u.val
  have e := congrArg (fun φ => φ.hom t) (i'.naturality (homOfLE hle').op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  rw [e, ht]
  show (Z'.presheaf.map _).hom ((Z'.presheaf.map _).hom u.val) = _
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

end GlobalTheory.Pinch
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitLiftClosedSubschemeNearFibreStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_lift_closed_subscheme_near_fibre : ∀ (X X' Z Z' : Scheme.{0}) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z), IsPullback i' p' p i → IsFinite p → IsClosedImmersion i → ∀ (W : X.Opens) (x : X), x ∈ W → ∀ u : Γ(Z', i' ⁻¹ᵁ (p ⁻¹ᵁ W))ˣ, ∃ (W' : X.Opens) (u' : Γ(X', p ⁻¹ᵁ W')ˣ), W' ≤ W ∧ x ∈ W' ∧ ∀ z : Z', p (i' z) ∈ W' → gm i' z (p ⁻¹ᵁ W') u' = gm (𝟙 Z') z (i' ⁻¹ᵁ (p ⁻¹ᵁ W)) u := by
  first | exact @GlobalTheory.Pinch.unit_lift_near_fibre | exact GlobalTheory.Pinch.unit_lift_near_fibre | (intros; apply GlobalTheory.Pinch.unit_lift_near_fibre <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundlePinchedOfMatchingGenerators
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundlePinchedOfMatchingGenerators
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Pinch

theorem alg_cancel {G : Type*} [CommGroup G] (c a b : G) : a * b⁻¹ = (c * a) * (c * b)⁻¹ := by
  apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv]; abel

theorem alg_chain {G : Type*} [CommGroup G] (a b c : G) : (b * a⁻¹) * (c * b⁻¹) = c * a⁻¹ := by
  apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv]; abel

theorem alg_swap {G : Type*} [CommGroup G] (c a b : G) : c * a = c * (b * a⁻¹)⁻¹ * b := by
  apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv]; abel

theorem ratio_unit {Y : Scheme.{0}} {L : LB Y} (hL : L.IsLB) {V V₁ V₂ : Y.Opens} (h₁ : V ≤ V₁) (h₂ : V ≤ V₂)
    {a₁ : ∀ k, Γ(Y, V₁ ⊓ L.U k)ˣ} {a₂ : ∀ k, Γ(Y, V₂ ⊓ L.U k)ˣ} (ha₁ : LocGen L V₁ a₁) (ha₂ : LocGen L V₂ a₂) :
    ∃ s : Γ(Y, V)ˣ, ∀ (T : Scheme.{0}) (f : T ⟶ Y) (t : T) (k : L.ι), f t ∈ V → f t ∈ L.U k →
      gm f t V s = gm f t (V₂ ⊓ L.U k) (a₂ k) * (gm f t (V₁ ⊓ L.U k) (a₁ k))⁻¹ := by
  have l₁ : ∀ k, V ⊓ L.U k ≤ V₁ ⊓ L.U k := fun k => inf_le_inf_right _ h₁
  have l₂ : ∀ k, V ⊓ L.U k ≤ V₂ ⊓ L.U k := fun k => inf_le_inf_right _ h₂
  obtain ⟨s, hs⟩ := glue_unit V (fun k => V ⊓ L.U k) (fun k => inf_le_left)
    (fun y hy => by
      obtain ⟨k, hk⟩ := exists_chart hL y
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hy, hk⟩)
    (fun k => res (l₂ k) (a₂ k) * (res (l₁ k) (a₁ k))⁻¹)
    (fun k k' y hy => by
      rw [map_mul, map_inv, map_mul, map_inv, gm_res _ y (l₂ k) hy.1, gm_res _ y (l₁ k) hy.1,
        gm_res _ y (l₂ k') hy.2, gm_res _ y (l₁ k') hy.2, ha₁ y k k' (h₁ hy.1.1) hy.1.2 hy.2.2,
        ha₂ y k k' (h₂ hy.1.1) hy.1.2 hy.2.2]
      exact (alg_cancel _ _ _).symm)
  refine ⟨s, fun T f t k ht hk => ?_⟩
  have hm : f t ∈ V ⊓ L.U k := ⟨ht, hk⟩
  rw [← gm_res f t (inf_le_left : V ⊓ L.U k ≤ V) hm s, hs k, map_mul, map_inv, gm_res f t (l₂ k) hm,
    gm_res f t (l₁ k) hm]

theorem eq_of_gm {X X' : Scheme.{0}} (p : X' ⟶ X) {V : X.Opens} (hinj : Function.Injective (pullU p V))
    {u v : Γ(X, V)ˣ} (h : ∀ x' : X', p x' ∈ V → gm p x' V u = gm p x' V v) : u = v :=
  hinj (unit_ext fun x' hx' => by
    rw [gm_pull (𝟙 X') p x' V hx', gm_pull (𝟙 X') p x' V hx', Category.id_comp]
    exact h x' hx')

end GlobalTheory.Pinch

namespace GlobalTheory.Pinch

theorem exists_lb_of_matching_gens : ∀ (X X' Z Z' : Scheme.{0}) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z),
    i' ≫ p = p' ≫ i → GlobalTheory.Pinch.UnitsPatch p i i' p' → ∀ (L' : LB X') (N : LB Z), L'.IsLB → N.IsLB →
    ∀ (w : LB.Iso (L'.pull i') (N.pull p')) (W : X → X.Opens) (a : ∀ x k, Γ(X', p ⁻¹ᵁ (W x) ⊓ L'.U k)ˣ)
      (b : ∀ x l, Γ(Z, i ⁻¹ᵁ (W x) ⊓ N.U l)ˣ), (∀ x, x ∈ W x) →
      (∀ x, GlobalTheory.Pinch.LocGen L' (p ⁻¹ᵁ (W x)) (a x)) → (∀ x, GlobalTheory.Pinch.LocGen N (i ⁻¹ᵁ (W x)) (b x)) →
      (∀ x, GlobalTheory.Pinch.Matches i' p' w (a x) (b x)) → ∃ L : LB X, L.IsLB ∧ LBIso (L.pull p) L' := by
  intro X X' Z Z' p i i' p' hsq hU L' N hL' hN w W a b hW ha hb hm
  have pt : ∀ z : Z', p (i' z) = i (p' z) := fun z => congrArg (fun f => f z) hsq
  have key : ∀ x y, ∃ g : Γ(X, W x ⊓ W y)ˣ, ∀ (x' : X') (k : L'.ι), p x' ∈ W x ⊓ W y → x' ∈ L'.U k →
      gm p x' _ g = gm (𝟙 X') x' _ (a y k) * (gm (𝟙 X') x' _ (a x k))⁻¹ := by
    intro x y
    obtain ⟨s, hs⟩ := ratio_unit hL' (V := p ⁻¹ᵁ (W x ⊓ W y)) (fun _ h => h.1) (fun _ h => h.2) (ha x) (ha y)
    obtain ⟨t, ht⟩ := ratio_unit hN (V := i ⁻¹ᵁ (W x ⊓ W y)) (fun _ h => h.1) (fun _ h => h.2) (hb x) (hb y)
    obtain ⟨u, hu⟩ := (hU (W x ⊓ W y)).2 s t (fun z hz => by
      obtain ⟨k, hk⟩ := exists_chart hL' (i' z)
      obtain ⟨l, hl⟩ := exists_chart hN (p' z)
      have hz' : i (p' z) ∈ W x ⊓ W y := pt z ▸ hz
      rw [hs Z' i' z k hz hk, ht Z' p' z l hz' hl, hm x z k l hz.1 hz'.1 hk hl, hm y z k l hz.2 hz'.2 hk hl]
      exact alg_cancel _ _ _)
    refine ⟨u, fun x' k hx hk => ?_⟩
    have e := gm_pull (𝟙 X') p x' _ hx u
    rw [Category.id_comp] at e
    rw [← e, hu]
    exact hs X' (𝟙 X') x' k hx hk
  choose g hg using key
  have hL : (⟨X, W, g⟩ : LB X).IsLB :=
    { cover := eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hW x⟩
      g_self := fun x => eq_of_gm p (hU (W x)).1 fun x' hx => by
        obtain ⟨k, hk⟩ := exists_chart hL' x'
        refine (gm_res p x' _ hx _).trans ((hg x x x' k ⟨hx, hx⟩ hk).trans ?_)
        rw [mul_inv_cancel, map_one]
      cocycle := fun x y z => eq_of_gm p (hU _).1 fun x' hx => by
        obtain ⟨k, hk⟩ := exists_chart hL' x'
        exact ((map_mul _ _ _).trans (congrArg₂ (· * ·)
          ((gm_res p x' _ hx _).trans (hg x y x' k ⟨hx.1.1, hx.1.2⟩ hk))
          ((gm_res p x' _ hx _).trans (hg y z x' k ⟨hx.1.2, hx.2⟩ hk)))).trans
          ((alg_chain _ _ _).trans ((gm_res p x' _ hx _).trans (hg x z x' k ⟨hx.1.1, hx.2⟩ hk)).symm) }
  refine ⟨⟨X, W, g⟩, hL, ⟨fun P => res (fun x' hx' => ⟨mem_pull.1 hx'.2, hx'.1⟩ :
    L'.U P.1 ⊓ ((⟨X, W, g⟩ : LB X).pull p).U P.2 ≤ p ⁻¹ᵁ W (P.2 PUnit.unit) ⊓ L'.U P.1) (a (P.2 PUnit.unit) P.1)⟩, ?_⟩
  rintro ⟨k, J⟩ ⟨k', J'⟩
  apply unit_ext
  intro x' hx'
  have hJ : p x' ∈ W (J PUnit.unit) := mem_pull.1 hx'.1.2
  have hJ' : p x' ∈ W (J' PUnit.unit) := mem_pull.1 hx'.2.2
  have e : gm (𝟙 X') x' (((⟨X, W, g⟩ : LB X).pull p).U J ⊓ ((⟨X, W, g⟩ : LB X).pull p).U J')
      (((⟨X, W, g⟩ : LB X).pull p).g J J') = gm p x' _ (g (J PUnit.unit) (J' PUnit.unit)) := by
    show gm (𝟙 X') x' _ (∏ _k : PUnit, (res _ (pullU p _ (g (J PUnit.unit) (J' PUnit.unit)))) ^ (1 : ℤ)) = _
    rw [Fintype.prod_unique, zpow_one]
    have hq : x' ∈ ((⟨X, W, g⟩ : LB X).pull p).U J ⊓ ((⟨X, W, g⟩ : LB X).pull p).U J' := ⟨hx'.1.2, hx'.2.2⟩
    exact (gm_res _ x' _ hq _).trans ((gm_pull (𝟙 X') p x' (W (J PUnit.unit) ⊓ W (J' PUnit.unit))
      (⟨hJ, hJ'⟩ : p x' ∈ W (J PUnit.unit) ⊓ W (J' PUnit.unit)) _).trans (congrArg (fun f => gm f x' _ (g (J PUnit.unit) (J' PUnit.unit))) (Category.id_comp p)))
  have hdiv : gm (𝟙 X') x' _ ((LB.div L' ((⟨X, W, g⟩ : LB X).pull p)).g (k, J) (k', J')) =
      gm (𝟙 X') x' _ (L'.g k k') * (gm p x' _ (g (J PUnit.unit) (J' PUnit.unit)))⁻¹ :=
    (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res _ x' _ hx' _)
      ((map_inv _ _).trans (congrArg (·⁻¹) ((gm_res _ x' _ hx' _).trans e))))
  refine (gm_res _ x' _ hx' _).trans ((gm_res _ x' _ hx'.1 _).trans ?_)
  refine Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·) hdiv
    ((gm_res _ x' _ hx' _).trans (gm_res _ x' _ hx'.2 _)))).symm
  have h2 := hg (J PUnit.unit) (J' PUnit.unit) x' k' ⟨hJ, hJ'⟩ hx'.2.1
  rw [h2]
  exact (ha (J PUnit.unit) x' k k' hJ hx'.1.1 hx'.2.1).trans (alg_swap _ _ _)

end GlobalTheory.Pinch
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundlePinchedOfMatchingGeneratorsStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lineBundle_pinched_of_matching_generators : ∀ (X X' Z Z' : Scheme.{0}) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z), i' ≫ p = p' ≫ i → GlobalTheory.Pinch.UnitsPatch p i i' p' → ∀ (L' : LB X') (N : LB Z), L'.IsLB → N.IsLB → ∀ (w : LB.Iso (L'.pull i') (N.pull p')) (W : X → X.Opens) (a : ∀ x k, Γ(X', p ⁻¹ᵁ (W x) ⊓ L'.U k)ˣ) (b : ∀ x l, Γ(Z, i ⁻¹ᵁ (W x) ⊓ N.U l)ˣ), (∀ x, x ∈ W x) → (∀ x, GlobalTheory.Pinch.LocGen L' (p ⁻¹ᵁ (W x)) (a x)) → (∀ x, GlobalTheory.Pinch.LocGen N (i ⁻¹ᵁ (W x)) (b x)) → (∀ x, GlobalTheory.Pinch.Matches i' p' w (a x) (b x)) → ∃ L : LB X, L.IsLB ∧ LBIso (L.pull p) L' := by
  first | exact @GlobalTheory.Pinch.exists_lb_of_matching_gens | exact GlobalTheory.Pinch.exists_lb_of_matching_gens | (intros; apply GlobalTheory.Pinch.exists_lb_of_matching_gens <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSubOneMemMulKerNakayamaFlat
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSubOneMemMulKerNakayamaFlat
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Pinch

theorem mem_map_mul_ker_of_flat {R' A C' : Type} [CommRing R'] [CommRing A] [CommRing C']
    [Algebra R' A] [Algebra R' C'] [Module.Flat R' C'] (f : A →ₐ[R'] C')
    (hf : Function.Surjective f) (J : Ideal R') {x : A}
    (hx : x ∈ J.map (algebraMap R' A)) (hfx : f x = 0) :
    x ∈ J.map (algebraMap R' A) * RingHom.ker f := by
  rw [Ideal.map, Ideal.span, Submodule.mem_span_set'] at hx
  obtain ⟨n, c, g, rfl⟩ := hx
  have hg : ∀ i, ∃ j ∈ J, algebraMap R' A j = (g i : A) := fun i => (g i).2
  choose j hjJ hjg using hg
  have hsum : ∑ i, j i • f (c i) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hfx, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul, ← hjg i, map_mul, AlgHom.commutes, Algebra.smul_def, _root_.mul_comm]
  obtain ⟨k, a, y, hy, ha⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := R') (M := C') (f := j)
    (x := fun i => f (c i)) hsum
  choose z hz using fun l => hf (y l)
  have hd : ∀ i, c i - ∑ l, a i l • z l ∈ RingHom.ker f := by
    intro i
    rw [RingHom.mem_ker]
    change f (c i - ∑ l, a i l • z l) = 0
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_sum]
    simp only [map_smul, hz]
    rw [← hy i, sub_self]
  have h0 : ∑ i, algebraMap R' A (j i) * ∑ l, a i l • z l = 0 := by
    have hl : ∀ l, ∑ i, algebraMap R' A (j i) * (a i l • z l) = 0 := by
      intro l
      have : ∑ i, algebraMap R' A (j i) * (a i l • z l) = (∑ i, j i * a i l) • z l := by
        rw [Finset.sum_smul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Algebra.smul_def, Algebra.smul_def, map_mul, _root_.mul_assoc]
      rw [this, ha l, zero_smul]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero fun l _ => hl l
  have key : ∑ i, c i • (g i : A) =
      ∑ i, algebraMap R' A (j i) * (c i - ∑ l, a i l • z l) := by
    simp only [mul_sub, Finset.sum_sub_distrib, h0, sub_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul, ← hjg i, _root_.mul_comm]
  rw [key]
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ (hjJ i)) (hd i)

theorem exists_sub_one_mem_mul_ker_le :
    ∀ (R' A C' : Type) [CommRing R'] [CommRing A] [CommRing C'] [Algebra R' A] [Algebra R' C']
      [IsNoetherianRing A] [Module.Flat R' C'] (f : A →ₐ[R'] C'), Function.Surjective f →
      ∀ (I : Ideal A) (J : Ideal R'), I ≤ RingHom.ker f →
        RingHom.ker f ≤ I ⊔ J.map (algebraMap R' A) →
          ∃ s : A, s - 1 ∈ J.map (algebraMap R' A) ∧ ∀ G ∈ RingHom.ker f, s * G ∈ I := by
  intro R' A C' _ _ _ _ _ _ _ f hf I J hI hK
  have hle : RingHom.ker f ≤ I ⊔ (J.map (algebraMap R' A)) • RingHom.ker f := by
    intro G hG
    obtain ⟨i, hi, x, hx, rfl⟩ := Submodule.mem_sup.1 (hK hG)
    have hfx : f x = 0 := by
      have h1 : f (i + x) = 0 := hG
      have h2 : f i = 0 := hI hi
      rw [map_add (f := _), h2, zero_add] at h1
      exact h1
    exact Submodule.add_mem_sup hi (mem_map_mul_ker_of_flat f hf J hx hfx)
  obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup
    (IsNoetherian.noetherian (RingHom.ker f)) le_rfl hle
  refine ⟨r, hr1, fun G hG => ?_⟩
  exact hr (Submodule.smul_mem_pointwise_smul G r _ hG)

end GlobalTheory.Pinch
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSubOneMemMulKerNakayamaFlatStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sub_one_mem_mul_ker_nakayama_flat : ∀ (R' A C' : Type) [CommRing R'] [CommRing A] [CommRing C'] [Algebra R' A] [Algebra R' C'] [IsNoetherianRing A] [Module.Flat R' C'] (f : A →ₐ[R'] C'), Function.Surjective f → ∀ (I : Ideal A) (J : Ideal R'), I ≤ RingHom.ker f → RingHom.ker f ≤ I ⊔ J.map (algebraMap R' A) → ∃ s : A, s - 1 ∈ J.map (algebraMap R' A) ∧ ∀ G ∈ RingHom.ker f, s * G ∈ I := by
  first | exact @GlobalTheory.Pinch.exists_sub_one_mem_mul_ker_le | exact GlobalTheory.Pinch.exists_sub_one_mem_mul_ker_le | (intros; apply GlobalTheory.Pinch.exists_sub_one_mem_mul_ker_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineNbhdBasicOpenStandardSmooth
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineNbhdBasicOpenStandardSmooth
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace GlobalTheory.Pinch

theorem appTop_ι_comp_eq {C Z : Scheme.{0}} (e : C ⟶ Z) (U : C.Opens) :
    (U.ι ≫ e).appTop = e.appLE ⊤ U le_top ≫ U.topIso.inv := by
  simp only [Scheme.Hom.appLE, Scheme.Opens.topIso, Scheme.Hom.comp_appTop, Scheme.Opens.ι_app]
  simp [← Functor.map_comp]

theorem exists_affine_basicOpen_standardSmooth : ∀ (g : ℕ) (C Z : Scheme.{0}) [IsAffine Z] (e : C ⟶ Z),
    SmoothOfRelativeDimension g e → ∀ x : C, ∃ O : C.Opens, IsAffineOpen O ∧ x ∈ O ∧
      ∀ r : Γ(C, O), (((C.basicOpen r).ι ≫ e).appTop).hom.IsStandardSmoothOfRelativeDimension g := by
  intro g C Z _ e he x
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ := C.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hW : IsAffineOpen W := hW
  have h0 := HasRingHomProperty.appLE (@SmoothOfRelativeDimension g) e he
    ⟨⊤, isAffineOpen_top Z⟩ ⟨W, hW⟩ le_top
  obtain ⟨s, hs, h'⟩ := (RingHom.locally_iff_isLocalization
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso _).1 h0
  have hcov := hW.self_le_iSup_basicOpen_iff.2 hs hxW
  obtain ⟨⟨t, ht⟩, hxt⟩ := TopologicalSpace.Opens.mem_iSup.1 hcov
  have hl := hW.isLocalization_basicOpen t
  have h1 := h' t ht Γ(C, C.basicOpen t)
  refine ⟨C.basicOpen t, hW.basicOpen t, hxt, fun r => ?_⟩
  have hl2 := (hW.basicOpen t).isLocalization_basicOpen r
  have h2 := (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway g).right
    Γ(C, C.basicOpen r) r _ h1
  have h3 : (e.appLE ⊤ (C.basicOpen r) le_top).hom.IsStandardSmoothOfRelativeDimension g := by
    convert h2 using 1
    ext a
    change _ = (C.presheaf.map (homOfLE (C.basicOpen_le r)).op) ((C.presheaf.map (homOfLE (C.basicOpen_le t)).op) _)
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map_assoc, Scheme.Hom.appLE_map]
  rw [appTop_ι_comp_eq, CommRingCat.hom_comp]
  exact RingHom.isStandardSmoothOfRelativeDimension_respectsIso.1 _
    (C.basicOpen r).topIso.symm.commRingCatIsoToRingEquiv h3

end GlobalTheory.Pinch
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineNbhdBasicOpenStandardSmoothStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_nbhd_basicOpen_standardSmooth : ∀ (g : ℕ) (C Z : Scheme.{0}) [IsAffine Z] (e : C ⟶ Z), SmoothOfRelativeDimension g e → ∀ x : C, ∃ O : C.Opens, IsAffineOpen O ∧ x ∈ O ∧ ∀ r : Γ(C, O), (((C.basicOpen r).ι ≫ e).appTop).hom.IsStandardSmoothOfRelativeDimension g := by
  first | exact @GlobalTheory.Pinch.exists_affine_basicOpen_standardSmooth | exact GlobalTheory.Pinch.exists_affine_basicOpen_standardSmooth | (intros; apply GlobalTheory.Pinch.exists_affine_basicOpen_standardSmooth <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorsAdaptedToQuotientGenerators
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorsAdaptedToQuotientGenerators
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem pinch_gens_adapted : ∀ (R R₀ R' C' D E ν : Type) [CommRing R] [CommRing R₀] [CommRing R'] [CommRing C'] [CommRing D] [CommRing E] [Algebra R' C'] [Algebra.FiniteType R' C'] [Algebra R₀ D] (a : R →+* R') (m : R →+* R₀) (π : C' →+* E) (ψ : D →+* E) (ζ : ν → D), Function.Surjective m → Function.Surjective π → Function.Surjective (MvPolynomial.aeval ζ : MvPolynomial ν R₀ →ₐ[R₀] D) → IsPushout (CommRingCat.ofHom ((algebraMap R₀ D).comp m)) (CommRingCat.ofHom a) (CommRingCat.ofHom ψ) (CommRingCat.ofHom (π.comp (algebraMap R' C'))) → ∃ (κ : Type) (_ : Finite κ) (ξ : κ ⊕ ν → C'), (∀ s, π (ξ s) = ψ (Sum.elim (fun _ ↦ 0) ζ s)) ∧ Function.Surjective (MvPolynomial.aeval ξ : MvPolynomial (κ ⊕ ν) R' →ₐ[R'] C') := by
  intro R R₀ R' C' D E ν _ _ _ _ _ _ _ _ _ a m π ψ ζ hm hπ hζ po
  choose ξ₀ hξ₀ using fun s => hπ (ψ (ζ s))
  have hcomm : ψ.comp ((algebraMap R₀ D).comp m) = (π.comp (algebraMap R' C')).comp a := by
    have := po.w
    exact congrArg CommRingCat.Hom.hom this
  have hsurj : Function.Surjective (π.comp (MvPolynomial.aeval ξ₀ : MvPolynomial ν R' →ₐ[R'] C').toRingHom) := by
    rw [← RingHom.range_eq_top, ← top_le_iff,
      ← CommRingCat.closure_range_union_range_eq_top_of_isPushout po, Subring.closure_le]
    rintro _ (⟨d, rfl⟩ | ⟨r, rfl⟩)
    · obtain ⟨f, rfl⟩ := hζ d
      obtain ⟨g, rfl⟩ := MvPolynomial.map_surjective m hm f
      refine ⟨MvPolynomial.map a g, ?_⟩
      simp only [CommRingCat.hom_ofHom, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
      induction g using MvPolynomial.induction_on with
      | C c =>
        have := congrArg (fun h => h c) hcomm
        simpa using this.symm
      | add p q hp hq => simp [hp, hq]
      | mul_X p s hp => simp [hp, hξ₀]
    · exact ⟨MvPolynomial.C r, by simp⟩
  obtain ⟨S, hS⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra R' C').FG)
  choose p hp using fun t : S => hsurj (π t)
  refine ⟨S, inferInstance, Sum.elim (fun t => (t : C') - MvPolynomial.aeval ξ₀ (p t)) ξ₀, ?_, ?_⟩
  · rintro (t | s)
    · have := hp t
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at this
      simp [map_sub, this]
    · simp [hξ₀]
  · intro x
    have hx : x ∈ Algebra.adjoin R' (S : Set C') := by rw [hS]; trivial
    have hle : Algebra.adjoin R' (S : Set C') ≤
        (MvPolynomial.aeval (Sum.elim (fun t : S => (t : C') - MvPolynomial.aeval ξ₀ (p t)) ξ₀) :
          MvPolynomial (S ⊕ ν) R' →ₐ[R'] C').range := by
      rw [Algebra.adjoin_le_iff]
      intro t ht
      refine ⟨MvPolynomial.X (Sum.inl ⟨t, ht⟩) + MvPolynomial.rename Sum.inr (p ⟨t, ht⟩), ?_⟩
      simp [MvPolynomial.aeval_rename, Function.comp_def]
    obtain ⟨y, hy⟩ := hle hx
    exact ⟨y, hy⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorsAdaptedToQuotientGeneratorsStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generators_adapted_to_quotient_generators : ∀ (R R₀ R' C' D E ν : Type) [CommRing R] [CommRing R₀] [CommRing R'] [CommRing C'] [CommRing D] [CommRing E] [Algebra R' C'] [Algebra.FiniteType R' C'] [Algebra R₀ D] (a : R →+* R') (m : R →+* R₀) (π : C' →+* E) (ψ : D →+* E) (ζ : ν → D), Function.Surjective m → Function.Surjective π → Function.Surjective (MvPolynomial.aeval ζ : MvPolynomial ν R₀ →ₐ[R₀] D) → IsPushout (CommRingCat.ofHom ((algebraMap R₀ D).comp m)) (CommRingCat.ofHom a) (CommRingCat.ofHom ψ) (CommRingCat.ofHom (π.comp (algebraMap R' C'))) → ∃ (κ : Type) (_ : Finite κ) (ξ : κ ⊕ ν → C'), (∀ s, π (ξ s) = ψ (Sum.elim (fun _ ↦ 0) ζ s)) ∧ Function.Surjective (MvPolynomial.aeval ξ : MvPolynomial (κ ⊕ ν) R' →ₐ[R'] C') := by
  first | exact @GlobalTheory.pinch_gens_adapted | exact GlobalTheory.pinch_gens_adapted | (intros; apply GlobalTheory.pinch_gens_adapted <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitRatioLocalGeneratorsCommonPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitRatioLocalGeneratorsCommonPullback
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Pinch

theorem commGroup_mul_eq_mul_mul_div {G : Type*} [CommGroup G] (g h w b a : G) :
    g * b * (g * h⁻¹ * w * (h * a))⁻¹ = b * (w * a)⁻¹ := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem comm_aux₂ {G : Type*} [CommGroup G] (w b a : G) : b = w * (b * (w * a)⁻¹ * a) := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem locGen_gm {Y T : Scheme.{0}} {L : LB Y} {V : Y.Opens} {a : ∀ k, Γ(Y, V ⊓ L.U k)ˣ} (h : LocGen L V a)
    (f : T ⟶ Y) (t : T) (k k' : L.ι) (hv : f t ∈ V) (hk : f t ∈ L.U k) (hk' : f t ∈ L.U k') :
    gm f t (V ⊓ L.U k) (a k) = gm f t (L.U k ⊓ L.U k') (L.g k k') * gm f t (V ⊓ L.U k') (a k') := by
  have e : res (inf_le_left : V ⊓ L.U k ⊓ L.U k' ≤ V ⊓ L.U k) (a k) =
      res (le_inf (inf_le_left.trans inf_le_right) inf_le_right : V ⊓ L.U k ⊓ L.U k' ≤ L.U k ⊓ L.U k') (L.g k k') *
      res (le_inf (inf_le_left.trans inf_le_left) inf_le_right : V ⊓ L.U k ⊓ L.U k' ≤ V ⊓ L.U k') (a k') := by
    apply unit_ext
    intro y hy
    rw [map_mul, gm_res _ y _ hy, gm_res _ y _ hy, gm_res _ y _ hy]
    exact h y k k' hy.1.1 hy.1.2 hy.2
  have hm : f t ∈ V ⊓ L.U k ⊓ L.U k' := ⟨⟨hv, hk⟩, hk'⟩
  have := congrArg (gm f t (V ⊓ L.U k ⊓ L.U k')) e
  rwa [map_mul, gm_res _ _ _ hm, gm_res _ _ _ hm, gm_res _ _ _ hm] at this

theorem iso_gm {X' Z Z' : Scheme.{0}} {i' : Z' ⟶ X'} {p' : Z' ⟶ Z} {L' : LB X'} {N : LB Z}
    {w : LB.Iso (L'.pull i') (N.pull p')} (hw : w.IsGen) (x : Z') (k k' : L'.ι) (l l' : N.ι)
    (hk : i' x ∈ L'.U k) (hk' : i' x ∈ L'.U k') (hl : p' x ∈ N.U l) (hl' : p' x ∈ N.U l') :
    gm (𝟙 Z') x ((N.pull p').U (fun _ ↦ l) ⊓ (L'.pull i').U (fun _ ↦ k)) (w.s (fun _ ↦ l, fun _ ↦ k)) =
      gm p' x (N.U l ⊓ N.U l') (N.g l l') * (gm i' x (L'.U k ⊓ L'.U k') (L'.g k k'))⁻¹ *
        gm (𝟙 Z') x ((N.pull p').U (fun _ ↦ l') ⊓ (L'.pull i').U (fun _ ↦ k')) (w.s (fun _ ↦ l', fun _ ↦ k')) := by
  have hp : x ∈ (N.pull p').U (fun _ ↦ l) ⊓ (L'.pull i').U (fun _ ↦ k) := ⟨mem_pull.2 hl, mem_pull.2 hk⟩
  have hq : x ∈ (N.pull p').U (fun _ ↦ l') ⊓ (L'.pull i').U (fun _ ↦ k') := ⟨mem_pull.2 hl', mem_pull.2 hk'⟩
  have e := (isGen_iff_germ w).1 hw x (fun _ ↦ l, fun _ ↦ k) (fun _ ↦ l', fun _ ↦ k') hp hq
  have d := gm_div' (N.pull p') (L'.pull i') (𝟙 Z') x (fun _ ↦ l, fun _ ↦ k) (fun _ ↦ l', fun _ ↦ k') hp hq
  have g1 := gm_pull_g N p' (𝟙 Z') x (fun _ ↦ l) (fun _ ↦ l') hp.1 hq.1
  have g2 := gm_pull_g L' i' (𝟙 Z') x (fun _ ↦ k) (fun _ ↦ k') hp.2 hq.2
  rw [Category.id_comp] at g1 g2
  rw [d, g1, g2] at e
  exact e

theorem exists_ratio_unit : ∀ (X' Z Z' : Scheme.{0}) (i' : Z' ⟶ X') (p' : Z' ⟶ Z) (L' : LB X') (N : LB Z), L'.IsLB → N.IsLB → ∀ (w : LB.Iso (L'.pull i') (N.pull p')), w.IsGen → ∀ (V' : X'.Opens) (V : Z.Opens) (a : ∀ k, Γ(X', V' ⊓ L'.U k)ˣ) (b : ∀ l, Γ(Z, V ⊓ N.U l)ˣ), GlobalTheory.Pinch.LocGen L' V' a → GlobalTheory.Pinch.LocGen N V b → ∀ O : Z'.Opens, O ≤ i' ⁻¹ᵁ V' → O ≤ p' ⁻¹ᵁ V → ∃ u : Γ(Z', O)ˣ, ∀ (z : Z') (k : L'.ι) (l : N.ι), z ∈ O → i' z ∈ L'.U k → p' z ∈ N.U l → gm p' z (V ⊓ N.U l) (b l) = gm (𝟙 Z') z ((N.pull p').U (fun _ ↦ l) ⊓ (L'.pull i').U (fun _ ↦ k)) (w.s (fun _ ↦ l, fun _ ↦ k)) * (gm (𝟙 Z') z O u * gm i' z (V' ⊓ L'.U k) (a k)) := by
  intro X' Z Z' i' p' L' N hL' hN w hw V' V a b ha hb O hO hO'
  let W : L'.ι × N.ι → Z'.Opens := fun q ↦ O ⊓ (i' ⁻¹ᵁ (V' ⊓ L'.U q.1) ⊓ p' ⁻¹ᵁ (V ⊓ N.U q.2))
  have hW : ∀ q, W q ≤ O := fun q ↦ inf_le_left
  have hWw : ∀ q, W q ≤ (N.pull p').U (fun _ ↦ q.2) ⊓ (L'.pull i').U (fun _ ↦ q.1) := fun q x hx ↦
    ⟨mem_pull.2 hx.2.2.2, mem_pull.2 hx.2.1.2⟩
  have hWb : ∀ q, W q ≤ p' ⁻¹ᵁ (V ⊓ N.U q.2) := fun q x hx ↦ hx.2.2
  have hWa : ∀ q, W q ≤ i' ⁻¹ᵁ (V' ⊓ L'.U q.1) := fun q x hx ↦ hx.2.1
  let u : ∀ q, Γ(Z', W q)ˣ := fun q ↦ res (hWb q) (pullU p' _ (b q.2)) *
    (res (hWw q) (w.s (fun _ ↦ q.2, fun _ ↦ q.1)) * res (hWa q) (pullU i' _ (a q.1)))⁻¹
  have gu : ∀ q, ∀ x ∈ W q, gm (𝟙 Z') x (W q) (u q) = gm p' x _ (b q.2) *
      (gm (𝟙 Z') x ((N.pull p').U (fun _ ↦ q.2) ⊓ (L'.pull i').U (fun _ ↦ q.1)) (w.s (fun _ ↦ q.2, fun _ ↦ q.1)) *
        gm i' x _ (a q.1))⁻¹ := by
    intro q x hx
    simp only [u, map_mul, map_inv]
    rw [gm_rp₁ p' x _ _ (hWb q) hx, gm_rp₁ i' x _ _ (hWa q) hx]
    exact congrArg (fun t ↦ _ * (t * _)⁻¹) (gm_res (𝟙 Z') x (hWw q) hx _)
  have cover : O ≤ iSup W := by
    intro x hx
    obtain ⟨k, hk⟩ := exists_chart hL' (i' x)
    obtain ⟨l, hl⟩ := exists_chart hN (p' x)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨(k, l), hx, ⟨hO hx, hk⟩, ⟨hO' hx, hl⟩⟩
  obtain ⟨s, hs⟩ := glue_unit O W hW cover u (by
    rintro ⟨k, l⟩ ⟨k', l'⟩ x hx
    rw [gu _ x hx.1, gu _ x hx.2]
    have hx1 := hx.1
    have hx2 := hx.2
    rw [locGen_gm hb p' x l l' hx1.2.2.1 hx1.2.2.2 hx2.2.2.2, locGen_gm ha i' x k k' hx1.2.1.1 hx1.2.1.2 hx2.2.1.2,
      iso_gm hw x k k' l l' hx1.2.1.2 hx2.2.1.2 hx1.2.2.2 hx2.2.2.2]
    exact commGroup_mul_eq_mul_mul_div _ _ _ _ _)
  refine ⟨s, fun z k l hz hk hl ↦ ?_⟩
  have hzW : z ∈ W (k, l) := ⟨hz, ⟨hO hz, hk⟩, ⟨hO' hz, hl⟩⟩
  have e := gu (k, l) z hzW
  rw [← hs (k, l), gm_res _ z _ hzW] at e
  rw [e]
  exact comm_aux₂ _ _ _

end GlobalTheory.Pinch
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitRatioLocalGeneratorsCommonPullbackStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_ratio_local_generators_common_pullback : ∀ (X' Z Z' : Scheme.{0}) (i' : Z' ⟶ X') (p' : Z' ⟶ Z) (L' : LB X') (N : LB Z), L'.IsLB → N.IsLB → ∀ (w : LB.Iso (L'.pull i') (N.pull p')), w.IsGen → ∀ (V' : X'.Opens) (V : Z.Opens) (a : ∀ k, Γ(X', V' ⊓ L'.U k)ˣ) (b : ∀ l, Γ(Z, V ⊓ N.U l)ˣ), GlobalTheory.Pinch.LocGen L' V' a → GlobalTheory.Pinch.LocGen N V b → ∀ O : Z'.Opens, O ≤ i' ⁻¹ᵁ V' → O ≤ p' ⁻¹ᵁ V → ∃ u : Γ(Z', O)ˣ, ∀ (z : Z') (k : L'.ι) (l : N.ι), z ∈ O → i' z ∈ L'.U k → p' z ∈ N.U l → gm p' z (V ⊓ N.U l) (b l) = gm (𝟙 Z') z ((N.pull p').U (fun _ ↦ l) ⊓ (L'.pull i').U (fun _ ↦ k)) (w.s (fun _ ↦ l, fun _ ↦ k)) * (gm (𝟙 Z') z O u * gm i' z (V' ⊓ L'.U k) (a k)) := by
  first | exact @GlobalTheory.Pinch.exists_ratio_unit | exact GlobalTheory.Pinch.exists_ratio_unit | (intros; apply GlobalTheory.Pinch.exists_ratio_unit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasRepresentingSchemePinchedBase
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Pinch


open MvPolynomial in
theorem exists_standardSmooth : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (R' : Type) [CommRing R'] [Algebra R R'] [Module.Finite R R'], Function.Injective (algebraMap R R') → ∀ c : Ideal R, (∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r) → ∀ (g : ℕ) (C' D E : Type) [CommRing C'] [CommRing D] [CommRing E] (φ : R' →+* C') (δ : R ⧸ c →+* D) (π : C' →+* E) (ψ : D →+* E), φ.Smooth → δ.IsStandardSmoothOfRelativeDimension g → IsPushout (CommRingCat.ofHom (φ.comp (algebraMap R R'))) (CommRingCat.ofHom (Ideal.Quotient.mk c)) (CommRingCat.ofHom π) (CommRingCat.ofHom (ψ.comp δ)) → IsPushout (CommRingCat.ofHom (δ.comp (Ideal.Quotient.mk c))) (CommRingCat.ofHom (algebraMap R R')) (CommRingCat.ofHom ψ) (CommRingCat.ofHom (π.comp φ)) → ∃ (F : Type) (_ : CommRing F) (ε : R →+* F) (t : C') (α : F →+* Localization.Away t) (β : F →+* D) (τ : Localization.Away t →+* E), ε.IsStandardSmoothOfRelativeDimension g ∧ IsPushout (CommRingCat.ofHom ε) (CommRingCat.ofHom (algebraMap R R')) (CommRingCat.ofHom α) (CommRingCat.ofHom ((algebraMap C' (Localization.Away t)).comp φ)) ∧ IsPushout (CommRingCat.ofHom ε) (CommRingCat.ofHom (Ideal.Quotient.mk c)) (CommRingCat.ofHom β) (CommRingCat.ofHom δ) ∧ τ.comp (algebraMap C' (Localization.Away t)) = π ∧ τ.comp α = ψ.comp β := by
  intro R _ _ R' _ _ _ hinj c hc g C' D E _ _ _ φ δ π ψ hφ hδ h1 h2
  classical
  letI : Algebra R' C' := φ.toAlgebra
  letI : Algebra (R ⧸ c) D := δ.toAlgebra
  haveI : Algebra.Smooth R' C' := hφ
  haveI : IsNoetherianRing R' := IsNoetherianRing.of_finite R R'
  obtain ⟨ν₀, σ₀, _, _, P₀, hP₀⟩ := (show Algebra.IsStandardSmoothOfRelativeDimension g (R ⧸ c) D from hδ).out
  obtain ⟨hπ, hker⟩ := GlobalTheory.T.pushout_quotient_surjective_ker_eq_map R C' E c _ π _ h1
  obtain ⟨κ, _, ξ, hξ, hsurj⟩ := GlobalTheory.T.exists_generators_adapted_to_quotient_generators R (R ⧸ c) R' C' D E ν₀ (algebraMap R R') (Ideal.Quotient.mk c) π ψ P₀.val
    Ideal.Quotient.mk_surjective hπ P₀.aeval_val_surjective h2
  obtain ⟨P, hP⟩ := GlobalTheory.T.exists_submersivePresentation_add_zero_variables (R ⧸ c) D ν₀ σ₀ κ P₀
  rw [← hP] at hξ
  have hw : ψ.comp ((algebraMap (R ⧸ c) D).comp (Ideal.Quotient.mk c)) =
      (π.comp (algebraMap R' C')).comp (algebraMap R R') := congrArg CommRingCat.Hom.hom h2.w
  choose F hF hF0 using fun s ↦ GlobalTheory.T.exists_relations_lift_vanishing_conductor GlobalTheory.T.exists_mvPolynomial_lift_conductor_coeffs R R' C' D E _ c hc π ψ P.val ξ hker hw hξ hsurj (P.relation s)
    (P.aeval_val_relation s)
  have hrel : (fun s ↦ map (Ideal.Quotient.mk c) (F s)) = P.relation := funext hF
  have hkP : RingHom.ker (aeval P.val : MvPolynomial _ (R ⧸ c) →ₐ[R ⧸ c] D) =
      Ideal.span (Set.range fun s ↦ map (Ideal.Quotient.mk c) (F s)) := by
    rw [hrel, P.span_range_relation_eq_ker, P.ker_eq_ker_aeval_val]
  have key : ∀ G : MvPolynomial (κ ⊕ ν₀) R', π (aeval ξ G) = eval₂ (π.comp φ) (fun s ↦ ψ (P.val s)) G := fun G ↦ by
    rw [aeval_def, eval₂_comp_left]
    exact congrArg (fun v ↦ eval₂ _ v G) (funext hξ)
  have key2 : ∀ G : MvPolynomial (κ ⊕ ν₀) R, π (aeval ξ (map (algebraMap R R') G)) =
      ψ (aeval P.val (map (Ideal.Quotient.mk c) G)) := fun G ↦ by
    rw [key, aeval_def, eval₂_comp_left, eval₂_map, eval₂_map]
    exact congrArg (fun f ↦ eval₂ f _ G) hw.symm
  obtain ⟨s', hs1, hs2⟩ := GlobalTheory.T.exists_sub_one_mem_mul_ker_nakayama_flat R' (MvPolynomial (κ ⊕ ν₀) R') C' (aeval ξ) hsurj
    (Ideal.span (Set.range fun s ↦ map (algebraMap R R') (F s))) (c.map (algebraMap R R'))
    (Ideal.span_le.2 (by rintro _ ⟨s, rfl⟩; exact hF0 s))
    (fun G hG ↦ GlobalTheory.T.mem_span_relations_conductor_of_eval_eq_zero R R' D E _ _ (algebraMap R R') c (π.comp φ) ψ P.val F P.aeval_val_surjective hkP h2 G
      (by rw [← key, show aeval ξ G = 0 from hG, map_zero]))
  obtain ⟨H, hH0, hH⟩ := GlobalTheory.T.exists_mvPolynomial_lift_conductor_coeffs R R' _ c hc _ hs1
  letI : Fintype (κ ⊕ σ₀) := Fintype.ofFinite _
  let Δ : MvPolynomial (κ ⊕ ν₀) R := (Matrix.of fun s t ↦ pderiv (P.map s) (F t)).det
  have hΔ : aeval P.val (map (Ideal.Quotient.mk c) (Δ * (H + 1))) = P.jacobian := by
    rw [map_mul, map_add (f := _), hH0, map_one, zero_add, _root_.mul_one, P.jacobian_eq_jacobiMatrix_det, P.algebraMap_apply,
      RingHom.map_det]
    congr 2
    ext1 s t
    rw [P.jacobiMatrix_apply, ← hF, pderiv_map]
    rfl
  have hu : IsUnit (aeval P.val (map (Ideal.Quotient.mk c) (Δ * (H + 1)))) := hΔ ▸ P.jacobian_isUnit
  obtain ⟨α, hα, hα'⟩ := GlobalTheory.T.isPushout_localized_presentation_baseChange R R' C' (Localization.Away (aeval ξ (map (algebraMap R R') (Δ * (H + 1))))) _ _
    (algebraMap R R') F (Δ * (H + 1)) ξ hsurj hF0 (fun G hG ↦ by
      rw [map_mul, map_add (f := _), hH, map_one, sub_add_cancel, _root_.mul_assoc]
      exact Ideal.mul_mem_left _ _ (hs2 G hG)) inferInstance
  obtain ⟨β, hβ, hβ'⟩ := GlobalTheory.T.isPushout_localized_presentation_baseChange R (R ⧸ c) D D _ _ (Ideal.Quotient.mk c) F (Δ * (H + 1)) P.val
    P.aeval_val_surjective (fun s ↦ by rw [hF]; exact P.aeval_val_relation s)
    (fun G hG ↦ Ideal.mul_mem_left _ _ (hkP ▸ hG)) (IsLocalization.away_of_isUnit_of_bijective _ hu Function.bijective_id)
  have ht : IsUnit (π (aeval ξ (map (algebraMap R R') (Δ * (H + 1))))) := by
    rw [key2]
    exact hu.map ψ
  refine ⟨_, inferInstance, algebraMap R _, _, α, β, IsLocalization.Away.lift _ ht, ?_, hα, hβ,
    IsLocalization.Away.lift_comp _ ht, ?_⟩
  · have := GlobalTheory.T.isStandardSmooth_localizationAway_jacobian_dvd R _ _ P.map P.map_inj F (Δ * (H + 1)) (dvd_mul_right _ _)
    have hd : Nat.card (κ ⊕ ν₀) - Nat.card (κ ⊕ σ₀) = g := by
      rw [← hP₀, Algebra.Presentation.dimension, Nat.card_sum, Nat.card_sum]
      omega
    rw [hd] at this
    exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap g).2 this
  · refine IsLocalization.ringHom_ext (Submonoid.powers (Ideal.Quotient.mk (Ideal.span (Set.range F)) (Δ * (H + 1)))) ?_
    refine Ideal.Quotient.ringHom_ext (RingHom.ext fun G ↦ ?_)
    simp only [RingHom.comp_apply]
    rw [hα', hβ', IsLocalization.Away.lift_eq, key2]
    rfl

theorem pinched_spec : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (R' : Type) [CommRing R'] [Algebra R R'] [Module.Finite R R'], Function.Injective (algebraMap R R') → ∀ c : Ideal R, (∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r) → ∀ (g : ℕ) (C' D E : Type) [CommRing C'] [CommRing D] [CommRing E] (φ : R' →+* C') (δ : R ⧸ c →+* D) (π : C' →+* E) (ψ : D →+* E), φ.Smooth → δ.IsStandardSmoothOfRelativeDimension g → IsPushout (CommRingCat.ofHom (φ.comp (algebraMap R R'))) (CommRingCat.ofHom (Ideal.Quotient.mk c)) (CommRingCat.ofHom π) (CommRingCat.ofHom (ψ.comp δ)) → IsPushout (CommRingCat.ofHom (δ.comp (Ideal.Quotient.mk c))) (CommRingCat.ofHom (algebraMap R R')) (CommRingCat.ofHom ψ) (CommRingCat.ofHom (π.comp φ)) → ∀ y : Sp E, GlobalTheory.Pinch.Pinched g (spMap (algebraMap R R')) (spMap (Ideal.Quotient.mk c)) (spMap φ) (spMap δ) (spMap π) (spMap ψ) (spMap π y) := by
  intro R _ _ R' _ _ _ hinj c hc g C' D E _ _ _ φ δ π ψ hφ hδ h1 h2 y
  obtain ⟨F, _, ε, t, α, β, τ, hε, k1, k2, e1, e2⟩ := exists_standardSmooth R R' hinj c hc g C' D E φ δ π ψ hφ hδ h1 h2
  have p1 := isPullback_SpecMap_of_isPushout _ _ _ _ h1
  have q1 := isPullback_SpecMap_of_isPushout _ _ _ _ k1
  have q2 := isPullback_SpecMap_of_isPushout _ _ _ _ k2
  have hcl : IsClosedImmersion (spMap (Ideal.Quotient.mk c)) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hβ : IsClosedImmersion (spMap β) := MorphismProperty.of_isPullback q2.flip hcl
  have cmp : ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (f' : B →+* C),
      spMap (f'.comp f) = spMap f' ≫ spMap f := fun f f' ↦ by
    rw [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  have hj : IsOpenImmersion (spMap (algebraMap C' (Localization.Away t))) := inferInstance
  have f1 : spMap τ ≫ spMap (algebraMap C' (Localization.Away t)) = spMap π := by rw [← cmp, e1]
  have f2 : spMap τ ≫ spMap α = spMap ψ ≫ spMap β := by rw [← cmp, ← cmp, e2]
  refine ⟨Sp F, Sp (Localization.Away t), Sp D, spMap ε, spMap α, spMap (algebraMap C' _), spMap β, 𝟙 _, ?_, ?_, hj,
    ⟨spMap τ y, ?_⟩, ?_, fun T a a' h ↦ ?_⟩
  · exact (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension g)).2
      (RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ hε)
  · rw [← cmp]
    exact q1
  · rw [← Scheme.Hom.comp_apply, f1]
  · rw [Category.id_comp]
    exact q2
  · have w : (a ≫ spMap (algebraMap C' (Localization.Away t))) ≫ spMap (φ.comp (algebraMap R R')) =
        (a' ≫ spMap δ) ≫ spMap (Ideal.Quotient.mk c) := by
      have w1 : spMap α ≫ spMap ε = spMap ((algebraMap C' (Localization.Away t)).comp φ) ≫
        spMap (algebraMap R R') := q1.w
      have w2 : spMap β ≫ spMap ε = spMap δ ≫ spMap (Ideal.Quotient.mk c) := q2.w
      rw [Category.assoc, Category.assoc, ← w2, ← Category.assoc a', ← h, Category.assoc, w1, cmp (algebraMap R R') φ,
        cmp φ (algebraMap C' (Localization.Away t)), Category.assoc]
    have l1 : p1.lift _ _ w ≫ spMap π = _ := p1.lift_fst _ _ w
    refine ⟨p1.lift _ _ w, l1, ?_⟩
    have l2 : p1.lift _ _ w ≫ spMap τ = a := by
      rw [← cancel_mono (spMap (algebraMap C' (Localization.Away t))), Category.assoc, f1, l1]
    rw [Category.comp_id, ← cancel_mono (spMap β), Category.assoc, ← f2, ← Category.assoc, l2, h]

theorem pinched : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (R' : Type) [CommRing R'] [Algebra R R'] [Module.Finite R R'], Function.Injective (algebraMap R R') → ∀ c : Ideal R, (∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r) → ∀ (g : ℕ) (B' C Y : Scheme.{0}) (b' : B' ⟶ Sp R') (e : C ⟶ Sp (R ⧸ c)) (i : Y ⟶ B') (q : Y ⟶ C), SmoothOfRelativeDimension g b' → SmoothOfRelativeDimension g e → FinAff B' → IsPullback i (q ≫ e) (b' ≫ spMap (algebraMap R R')) (spMap (Ideal.Quotient.mk c)) → IsPullback q (i ≫ b') (e ≫ spMap (Ideal.Quotient.mk c)) (spMap (algebraMap R R')) → ∀ x : B', GlobalTheory.Pinch.Pinched g (spMap (algebraMap R R')) (spMap (Ideal.Quotient.mk c)) b' e i q x := by
  intro R _ _ R' _ _ _ hinj c hc g B' C Y b' e i q hb he hF h1 h2 x
  by_cases hx : (b' ≫ spMap (algebraMap R R')) x ∈ Set.range (spMap (Ideal.Quotient.mk c))
  swap
  · exact GlobalTheory.T.pinched_chart_off_closed_part_from_base R R' hinj c hc g B' C Y b' e i q hb x hx
  have hfin : IsFinite (spMap (algebraMap R R')) :=
    (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 inferInstance)
  have hcl : IsClosedImmersion (spMap (Ideal.Quotient.mk c)) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  obtain ⟨y, rfl⟩ : x ∈ Set.range i := by
    obtain ⟨t, ht⟩ := hx
    obtain ⟨y, hy, -⟩ := Scheme.exists_preimage_of_isPullback h1 x t ht.symm
    exact ⟨y, hy⟩
  obtain ⟨O, hO, hyO, hstd⟩ := GlobalTheory.T.exists_affine_nbhd_basicOpen_standardSmooth g C _ e he (q y)
  obtain ⟨V', r, hV', hy, hV⟩ := GlobalTheory.T.exists_affine_open_saturated_basicOpen_preimage B' C Y i q (MorphismProperty.of_isPullback h1.flip hcl)
    (MorphismProperty.of_isPullback h2.flip hfin) hF y O hO hyO
  obtain ⟨q₀, k1, k2, k3⟩ := GlobalTheory.T.pinched_charts_restrict_matching_opens g _ _ _ B' C Y _ _ b' e i q h1 h2 V' (C.basicOpen r) hV
  have hsm : Smooth b' := SmoothOfRelativeDimension.smooth g b'
  have := k3 _ (GlobalTheory.T.pinched_charts_affine_of_spectra pinched_spec R R' hinj c hc g _ _ _ (V'.ι ≫ b') ((C.basicOpen r).ι ≫ e) (i ∣_ V') q₀ hV'
    (hO.basicOpen r) inferInstance (hstd r) k1 k2 ⟨y, hy⟩)
  have e0 : V'.ι ((i ∣_ V') ⟨y, hy⟩) = i y :=
    (Scheme.Hom.comp_apply (i ∣_ V') V'.ι ⟨y, hy⟩).symm.trans (by rw [morphismRestrict_ι]; rfl)
  rwa [e0] at this

theorem exists_pic_patch : ∀ (X X' Z Z' : Scheme.{0}) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z), IsPullback i' p' p i → IsFinite p → IsClosedImmersion i → GlobalTheory.Pinch.Cond p i → ∀ (c' : Pic X') (d : Pic Z), GlobalTheory.CechPic.pull i' c' = GlobalTheory.CechPic.pull p' d → ∃ c : Pic X, GlobalTheory.CechPic.pull p c = c' := by
  intro X X' Z Z' p i i' p' hsq hp hi hc c' d h
  obtain ⟨L', hL', rfl⟩ := cls_surj c'
  obtain ⟨N, hN, rfl⟩ := cls_surj d
  obtain ⟨w, hw⟩ := (cls_eq_iff (pull_isLB hL' i') (pull_isLB hN p')).1 h
  have hw' : ∀ z : Z', p (i' z) = i (p' z) := fun z ↦ by
    rw [← Scheme.Hom.comp_apply, hsq.w, Scheme.Hom.comp_apply]
  have loc : ∀ x : X, ∃ (W : X.Opens) (a : ∀ k, Γ(X', p ⁻¹ᵁ W ⊓ L'.U k)ˣ) (b : ∀ l, Γ(Z, i ⁻¹ᵁ W ⊓ N.U l)ˣ),
      x ∈ W ∧ GlobalTheory.Pinch.LocGen L' (p ⁻¹ᵁ W) a ∧ GlobalTheory.Pinch.LocGen N (i ⁻¹ᵁ W) b ∧ GlobalTheory.Pinch.Matches i' p' w a b := by
    intro x
    obtain ⟨W₁, a, h₁, ha⟩ := GlobalTheory.T.exists_local_generator_finite_cover_near_point GlobalTheory.T.exists_lineBundle_localGenerator_near_finiteSet X X' p hp L' hL' x
    obtain ⟨W₂, b, h₂, hb⟩ := GlobalTheory.T.exists_local_generator_finite_cover_near_point GlobalTheory.T.exists_lineBundle_localGenerator_near_finiteSet X Z i inferInstance N hN x
    obtain ⟨u, hu⟩ := GlobalTheory.T.exists_unit_ratio_local_generators_common_pullback X' Z Z' i' p' L' N hL' hN w hw _ _ a b ha hb (i' ⁻¹ᵁ (p ⁻¹ᵁ (W₁ ⊓ W₂)))
      (fun z hz ↦ hz.1) (fun z hz ↦ show i (p' z) ∈ W₂ from hw' z ▸ hz.2)
    obtain ⟨W, u', hW, hx, hu'⟩ := GlobalTheory.T.exists_unit_lift_closed_subscheme_near_fibre X X' Z Z' p i i' p' hsq hp hi (W₁ ⊓ W₂) x ⟨h₁, h₂⟩ u
    have l₁ : ∀ k, p ⁻¹ᵁ W ⊓ L'.U k ≤ p ⁻¹ᵁ W₁ ⊓ L'.U k := fun k y hy ↦ ⟨(hW hy.1).1, hy.2⟩
    have l₂ : ∀ l, i ⁻¹ᵁ W ⊓ N.U l ≤ i ⁻¹ᵁ W₂ ⊓ N.U l := fun k y hy ↦ ⟨(hW hy.1).2, hy.2⟩
    refine ⟨W, fun k ↦ res inf_le_left u' * res (l₁ k) (a k), fun l ↦ res (l₂ l) (b l), hx, ?_, ?_, ?_⟩
    · intro y k k' hy hk hk'
      have m : (𝟙 X' : X' ⟶ X') y ∈ p ⁻¹ᵁ W ⊓ L'.U k := ⟨hy, hk⟩
      have m' : (𝟙 X' : X' ⟶ X') y ∈ p ⁻¹ᵁ W ⊓ L'.U k' := ⟨hy, hk'⟩
      rw [map_mul, map_mul, gm_res _ _ _ m, gm_res _ _ _ m, gm_res _ _ _ m', gm_res _ _ _ m',
        ha y k k' (hW hy).1 hk hk', mul_left_comm]
    · intro y k k' hy hk hk'
      have m : (𝟙 Z : Z ⟶ Z) y ∈ i ⁻¹ᵁ W ⊓ N.U k := ⟨hy, hk⟩
      have m' : (𝟙 Z : Z ⟶ Z) y ∈ i ⁻¹ᵁ W ⊓ N.U k' := ⟨hy, hk'⟩
      rw [gm_res _ _ _ m, gm_res _ _ _ m', hb y k k' (hW hy).2 hk hk']
    · intro z k l h1 h2 hk hl
      have m : i' z ∈ p ⁻¹ᵁ W ⊓ L'.U k := ⟨h1, hk⟩
      have m' : p' z ∈ i ⁻¹ᵁ W ⊓ N.U l := ⟨h2, hl⟩
      rw [map_mul, gm_res _ _ _ m, gm_res _ _ _ m, gm_res _ _ _ m', hu' z h1]
      exact hu z k l (hW h1) hk hl
  choose W a b hx ha hb hm using loc
  obtain ⟨L, hL, hiso⟩ := GlobalTheory.T.exists_lineBundle_pinched_of_matching_generators X X' Z Z' p i i' p' hsq.w (GlobalTheory.T.pinchingSquare_unitsPatch X X' Z Z' p i i' p' hsq inferInstance hi hc)
    L' N hL' hN w W a b hx ha hb hm
  exact ⟨cls L hL, (cls_eq_iff (pull_isLB hL p) hL').2 hiso⟩

theorem isPullback_whisker {S : Scheme.{0}} (A : Over S) {T T' : Over S} (f : T' ⟶ T) :
    IsPullback (A ◁ f).left (snd A T').left (snd A T).left f.left := by
  have : IsPullback (A ◁ f) (snd A T') (snd A T) f := by
    refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ (fun s ↦ lift (s.fst ≫ fst A T) s.snd) (fun s ↦ ?_)
      (fun s ↦ by simp) (fun s m h₁ h₂ ↦ ?_)⟩⟩
    · ext
      · simp
      · simp [s.condition]
    · ext
      · simp [← h₁]
      · simp [← h₂]
  exact this.map (Over.forget S)

theorem hasRep_pinched : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (R' : Type) [CommRing R'] [Algebra R R'] [Module.Finite R R'], Function.Injective (algebraMap R R') → ∀ c : Ideal R, (∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r) → HasRepAF A g (Over.mk (spMap (algebraMap R R'))) → HasRep A g (Over.mk (spMap (Ideal.Quotient.mk c))) → HasRep A g (𝟙_ _) := by
  intro R _ _ A _ g hA hg R' _ _ _ hinj c hc ⟨B', b', P', hP', hG', hF⟩ ⟨C, e, Q, hQ, hG⟩
  have hfin : IsFinite (spMap (algebraMap R R')) :=
    (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 inferInstance)
  have hsur : Surjective (spMap (algebraMap R R')) := by
    refine ⟨fun x ↦ ?_⟩
    have : FaithfulSMul R R' := (faithfulSMul_iff_algebraMap_injective R R').2 hinj
    exact Algebra.IsIntegral.comap_surjective R R' x
  have hcl : IsClosedImmersion (spMap (Ideal.Quotient.mk c)) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  refine GlobalTheory.T.representingScheme_of_finite_surjective_lift R A g hA hg B' _ b' P' hfin hsur hP' hG' fun x ↦ ?_
  obtain ⟨q, hq, hpb, hS⟩ := GlobalTheory.T.representsAdditiveLineBundleFamilies_compare _ A B' _ C _ b' P' e Q hP' hQ
  have wb : b'.left ≫ spMap (algebraMap R R') = B'.hom := Over.w b'
  have we : e.left ≫ spMap (Ideal.Quotient.mk c) = C.hom := Over.w e
  have hq' : q.left ≫ e.left = pullback.snd B'.hom (spMap (Ideal.Quotient.mk c)) := congrArg (·.left) hq
  obtain ⟨U, U', V, u, p, j, n, k, hu, h1, hj, hx, h2, h3⟩ := pinched R R' hinj c hc g B'.left C.left
    (B' ⊗ Over.mk (spMap (Ideal.Quotient.mk c))).left b'.left e.left (fst B' _).left q.left hG'.smooth hG.smooth hF
    (by rw [wb, hq']; exact IsPullback.of_hasPullback _ _) (by rw [we]; exact hpb) x
  let Uo : Over (Sp R) := Over.mk u
  let U'o : Over (Sp R) := Over.mk (p ≫ u)
  let Vo : Over (Sp R) := Over.mk (n ≫ u)
  let po : U'o ⟶ Uo := Over.homMk p rfl
  let no : Vo ⟶ Uo := Over.homMk n rfl
  let jo : U'o ⟶ B' := Over.homMk j (by change j ≫ B'.hom = p ≫ u; rw [← wb, h1.w, Category.assoc])
  let ko : Vo ⟶ C := Over.homMk k (by change k ≫ C.hom = n ≫ u; rw [← we, h2.w, Category.assoc])
  let Wo : Over (Sp R) := Over.mk (pullback.fst p n ≫ p ≫ u)
  let ao : Wo ⟶ U'o := Over.homMk (pullback.fst p n) rfl
  let bo : Wo ⟶ Vo := Over.homMk (pullback.snd p n) (by
    change pullback.snd p n ≫ n ≫ u = pullback.fst p n ≫ p ≫ u
    rw [pullback.condition_assoc])
  obtain ⟨y, hy1, hy2⟩ := h3 _ (pullback.fst p n) (pullback.snd p n) pullback.condition
  let yo : Wo ⟶ B' ⊗ Over.mk (spMap (Ideal.Quotient.mk c)) := Over.homMk y (by
    rw [← Over.w (fst B' (Over.mk (spMap (Ideal.Quotient.mk c)))), ← Category.assoc, hy1]
    exact Over.w (ao ≫ jo))
  have hy1' : yo ≫ fst _ _ = ao ≫ jo := Over.OverMorphism.ext hy1
  have hy2' : yo ≫ q = bo ≫ ko := Over.OverMorphism.ext hy2
  have hsm : Smooth u := SmoothOfRelativeDimension.smooth g u
  have hsA : Smooth A.hom := SmoothOfRelativeDimension.smooth g _
  have hp : IsFinite p := MorphismProperty.of_isPullback h1.flip hfin
  have hps : Surjective p := MorphismProperty.of_isPullback h1.flip hsur
  have hn : IsClosedImmersion n := MorphismProperty.of_isPullback h2.flip hcl
  have hnoe : IsLocallyNoetherian Uo.left := LocallyOfFiniteType.isLocallyNoetherian u
  have hfl : Flat ((snd A Uo).left ≫ u) := by
    have : Flat (snd A Uo).left := inferInstanceAs (Flat (pullback.snd A.hom u))
    infer_instance
  have hcond := GlobalTheory.T.conductorSquare_flat_baseChange_schemes R R' hinj c hc _ _ _ _ _ _ _ _ hfl ((isPullback_whisker A po).paste_vert h1)
    ((isPullback_whisker A no).paste_vert h2)
  have hsq : IsPullback (A ◁ ao).left (A ◁ bo).left (A ◁ po).left (A ◁ no).left := by
    have big : IsPullback (A ◁ ao).left ((snd A Wo).left ≫ bo.left) ((snd A U'o).left ≫ po.left) no.left := (isPullback_whisker A ao).paste_vert
      ((IsPullback.of_hasPullback p n) : IsPullback ao.left bo.left po.left no.left)
    have e1 : (snd A Wo).left ≫ bo.left = (A ◁ bo).left ≫ (snd A Vo).left := (isPullback_whisker A bo).w.symm
    have e2 : (snd A U'o).left ≫ po.left = (A ◁ po).left ≫ (snd A Uo).left := (isPullback_whisker A po).w.symm
    rw [e1, e2] at big
    refine IsPullback.of_bot big ?_ (isPullback_whisker A no)
    rw [← Over.comp_left, ← Over.comp_left, ← MonoidalCategory.whiskerLeft_comp, ← MonoidalCategory.whiskerLeft_comp]
    exact congrArg (fun t ↦ (A ◁ t).left) (Over.OverMorphism.ext pullback.condition)
  have hN : Fam A (ev P' (fst A U'o) (snd A U'o ≫ jo)) := by
    have hl : (ev P' (fst A U'o) (snd A U'o ≫ jo)).IsLB := pull_isLB hP'.fam.isLB _
    refine ⟨hl, (isAdditive_iff hl).2 fun Y a a' t ↦ ?_⟩
    simp only [evc_ev hP'.fam.isLB, lift_fst, lift_snd_assoc]
    exact (isAdditive_iff hP'.fam.isLB).1 hP'.fam.add _ _ _ _
  obtain ⟨c₀, hc₀⟩ := exists_pic_patch _ _ _ _ _ _ _ _ hsq
    (MorphismProperty.of_isPullback (isPullback_whisker A po).flip hp)
    (MorphismProperty.of_isPullback (isPullback_whisker A no).flip hn) hcond
    (evc hP'.fam.isLB (fst A U'o) (snd A U'o ≫ jo)) (evc hQ.fam.isLB (fst A Vo) (snd A Vo ≫ ko)) (by
      have := congrArg (GlobalTheory.CechPic.pull (A ◁ yo).left) ((same_iff hP'.fam.isLB hQ.fam.isLB _ _).1 hS)
      simp only [pull_evc, whiskerLeft_fst, whiskerLeft_snd_assoc, hy1', hy2'] at this ⊢
      exact this)
  obtain ⟨M, hM, hMS⟩ := GlobalTheory.T.exists_additiveFamily_of_pullback_finiteSurjective _ A Uo U'o hA po hp hps _ hN c₀ hc₀
  let S' : Over (Sp R) := Over.mk (spMap (algebraMap R R'))
  let r : Uo ⊗ S' ⟶ U'o := Over.homMk h1.isoPullback.inv (by
    change h1.isoPullback.inv ≫ p ≫ u = pullback.fst u (spMap (algebraMap R R')) ≫ u
    rw [h1.isoPullback_inv_fst_assoc])
  have r1 : r ≫ po = fst Uo S' := Over.OverMorphism.ext h1.isoPullback_inv_fst
  refine ⟨Uo, M, r ≫ jo, hM, hu, Over.OverMorphism.ext h1.isoPullback_inv_snd, ?_, ?_, ?_⟩
  · change IsOpenImmersion (h1.isoPullback.inv ≫ j)
    infer_instance
  · obtain ⟨x', rfl⟩ := hx
    refine ⟨h1.isoPullback.hom x', ?_⟩
    change (h1.isoPullback.hom ≫ h1.isoPullback.inv ≫ j) x' = _
    rw [Iso.hom_inv_id_assoc]
  · refine (same_iff hM.isLB hP'.fam.isLB _ _).2 ?_
    have := congrArg (GlobalTheory.CechPic.pull (A ◁ r).left) ((same_iff hM.isLB hN.isLB _ _).1 hMS)
    simp only [pull_evc, whiskerLeft_fst, whiskerLeft_snd_assoc, r1, evc_ev hP'.fam.isLB, lift_fst, lift_snd_assoc,
      Category.comp_id, whiskerLeft_snd] at this
    simpa only [Category.assoc] using this

end GlobalTheory.Pinch
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasRepresentingSchemePinchedBaseStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasRepresentingScheme_pinchedBase : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (R' : Type) [CommRing R'] [Algebra R R'] [Module.Finite R R'], Function.Injective (algebraMap R R') → ∀ c : Ideal R, (∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r) → HasRepAF A g (Over.mk (spMap (algebraMap R R'))) → HasRep A g (Over.mk (spMap (Ideal.Quotient.mk c))) → HasRep A g (𝟙_ _) := by
  first | exact @GlobalTheory.Pinch.hasRep_pinched | exact GlobalTheory.Pinch.hasRep_pinched | (intros; apply GlobalTheory.Pinch.hasRep_pinched <;> assumption)
end
