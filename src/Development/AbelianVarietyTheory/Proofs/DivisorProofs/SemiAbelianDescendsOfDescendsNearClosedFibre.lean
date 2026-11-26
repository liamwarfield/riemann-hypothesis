module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianDescendsNearClosedFibre

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiAbelianDescentAlongProperSurjective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupInverseDescendsProperSurjection
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupInverseDescendsProperSurjection
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum

theorem inv_pullback_left_fst {X Y : Scheme.{0}} (f : X ⟶ Y) (G' : Over Y) [GrpObj G'] {T : Over X}
    (z : T ⟶ (Over.pullback f).obj G') :
    (z⁻¹).left ≫ pullback.fst G'.hom f = z.left ≫ pullback.fst G'.hom f ≫ ι[G'].left := by
  show (z ≫ (Over.pullback f).map ι[G']).left ≫ _ = _
  rw [Over.comp_left, Category.assoc]
  congr 1
  simp only [Over.pullback_map_left]
  first | exact pullback.lift_fst _ _ _ | erw [pullback.lift_fst]

theorem exists_inv_descent : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] (G : Over (Sp R)) (β : G'.left ⟶ G.left), Smooth G.hom → IsPullback β G'.hom G.hom π → ∀ φ : (Over.pullback (pullback.fst π π)).obj G' ≅ (Over.pullback (pullback.snd π π)).obj G', IsMonHom φ.hom → pullback.fst G'.hom (pullback.fst π π) ≫ β = φ.hom.left ≫ pullback.fst G'.hom (pullback.snd π π) ≫ β → ∃ i : G ⟶ G, ∀ (T : Over S) (x : T ⟶ G') (x₀ : Over.mk (T.hom ≫ π) ⟶ G), x₀.left = x.left ≫ β → (x₀ ≫ i).left = x⁻¹.left ≫ β := by
  intro R _ _ _ _ S π hP hS hI G' _ G β hsm hpb φ hφ hc
  have hfl : Flat G.hom := inferInstance
  have D := fun (W : Scheme.{0}) => GlobalTheory.T.exists_descent_of_equalised_proper_cover_normal R S G.left G'.left W π G.hom β G'.hom hP hS hI hfl hpb
  have epi : ∀ {W : Scheme.{0}} (a b : G.left ⟶ W), β ≫ a = β ≫ b → a = b := by
    intro W a b hab
    obtain ⟨h₀, -, hu⟩ := D W (β ≫ a) (by rw [pullback.condition_assoc])
    exact (hu a rfl).trans (hu b hab.symm).symm
  have hw : β ≫ G.hom = G'.hom ≫ π := hpb.w
  set a₁ := pullback.fst β β
  set a₂ := pullback.snd β β
  have hσ : (a₁ ≫ G'.hom) ≫ π = (a₂ ≫ G'.hom) ≫ π := by
    simp only [Category.assoc, ← hw]; rw [pullback.condition_assoc]
  let σ : pullback β β ⟶ pullback π π := pullback.lift _ _ hσ
  let x : Over.mk σ ⟶ (Over.pullback (pullback.fst π π)).obj G' :=
    Over.homMk (pullback.lift a₁ σ (pullback.lift_fst _ _ _).symm) (pullback.lift_snd _ _ _)
  have hcx : ∀ y : Over.mk σ ⟶ (Over.pullback (pullback.fst π π)).obj G',
      y.left ≫ pullback.fst G'.hom (pullback.fst π π) ≫ β =
        (y ≫ φ.hom).left ≫ pullback.fst G'.hom (pullback.snd π π) ≫ β := by
    intro y; rw [Over.comp_left, Category.assoc, ← hc]
  have h2 : (x ≫ φ.hom).left ≫ pullback.fst G'.hom (pullback.snd π π) = a₂ := by
    apply hpb.hom_ext
    · rw [Category.assoc, ← hcx x]
      show pullback.lift a₁ σ _ ≫ _ ≫ β = _
      rw [pullback.lift_fst_assoc]
      exact pullback.condition
    · rw [Category.assoc, pullback.condition, ← Category.assoc,
        show (x ≫ φ.hom).left ≫ pullback.snd G'.hom (pullback.snd π π) = σ from Over.w (x ≫ φ.hom)]
      exact pullback.lift_snd _ _ _
  have eq : a₁ ≫ ι[G'].left ≫ β = a₂ ≫ ι[G'].left ≫ β := by
    have := hcx x⁻¹
    rw [GrpObj.inv_comp, reassoc_of% inv_pullback_left_fst, reassoc_of% inv_pullback_left_fst,
      reassoc_of% h2] at this
    simp only [x, Over.homMk_left] at this
    rwa [pullback.lift_fst_assoc] at this
  obtain ⟨h₀, hh₀, -⟩ := D G.left (ι[G'].left ≫ β) eq
  have hover : h₀ ≫ G.hom = G.hom := by
    apply epi
    rw [reassoc_of% hh₀, hw, ← Category.assoc, Over.w ι[G']]
  refine ⟨Over.homMk h₀ hover, ?_⟩
  intro T x' x₀ hx
  rw [Over.comp_left]
  show x₀.left ≫ h₀ = _
  rw [hx, Category.assoc, hh₀]
  show _ = (x' ≫ ι[G']).left ≫ β
  rw [Over.comp_left, Category.assoc]

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupInverseDescendsProperSurjectionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.group_inverse_descends_proper_surjection : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] (G : Over (Sp R)) (β : G'.left ⟶ G.left), Smooth G.hom → IsPullback β G'.hom G.hom π → ∀ φ : (Over.pullback (pullback.fst π π)).obj G' ≅ (Over.pullback (pullback.snd π π)).obj G', IsMonHom φ.hom → pullback.fst G'.hom (pullback.fst π π) ≫ β = φ.hom.left ≫ pullback.fst G'.hom (pullback.snd π π) ≫ β → ∃ i : G ⟶ G, ∀ (T : Over S) (x : T ⟶ G') (x₀ : Over.mk (T.hom ≫ π) ⟶ G), x₀.left = x.left ≫ β → (x₀ ≫ i).left = x⁻¹.left ≫ β := by
  first | exact @GlobalTheory.Mum.exists_inv_descent | exact GlobalTheory.Mum.exists_inv_descent | (intros; apply GlobalTheory.Mum.exists_inv_descent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedCommGroupOfPullbackProperSurjection
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedCommGroupOfPullbackProperSurjection
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.DescGrp

variable {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] {S : Scheme.{0}}
  {π : S ⟶ Sp R}

theorem ext_of_pts (hP : IsProper π) (hS : Surjective π) (hI : IsIntegral S) {Y W : Over (Sp R)} (hY : Flat Y.hom)
    (f₁ f₂ : Y ⟶ W) (h : ∀ (T : Over S) (P : Over.mk (T.hom ≫ π) ⟶ Y), P ≫ f₁ = P ≫ f₂) : f₁ = f₂ := by
  have hpb : IsPullback (pullback.fst Y.hom π) (pullback.snd Y.hom π) Y.hom π := IsPullback.of_hasPullback _ _
  have key : pullback.fst Y.hom π ≫ f₁.left = pullback.fst Y.hom π ≫ f₂.left := by
    have := h (Over.mk (pullback.snd Y.hom π)) (Over.homMk (pullback.fst Y.hom π) pullback.condition)
    simpa using congrArg CommaMorphism.left this
  obtain ⟨h₀, _, hu⟩ := GlobalTheory.T.exists_descent_of_equalised_proper_cover_normal R S Y.left (pullback Y.hom π) W.left π Y.hom (pullback.fst Y.hom π)
    (pullback.snd Y.hom π) hP hS hI hY hpb (pullback.fst Y.hom π ≫ f₁.left)
    (by rw [← Category.assoc, ← Category.assoc, pullback.condition])
  ext
  exact (hu _ rfl).trans (hu _ key.symm).symm

variable {G' : Over S} {G : Over (Sp R)} {β : G'.left ⟶ G.left}

def dn (hpb : IsPullback β G'.hom G.hom π) {T : Over S} (x : T ⟶ G') : Over.mk (T.hom ≫ π) ⟶ G :=
  Over.homMk (x.left ≫ β) (by
    change x.left ≫ β ≫ G.hom = T.hom ≫ π
    rw [hpb.w, ← Category.assoc, Over.w x])

def up (hpb : IsPullback β G'.hom G.hom π) {T : Over S} (a : Over.mk (T.hom ≫ π) ⟶ G) : T ⟶ G' :=
  Over.homMk (hpb.lift a.left T.hom (by simpa using Over.w a)) (hpb.lift_snd _ _ _)

theorem dn_up (hpb : IsPullback β G'.hom G.hom π) {T : Over S} (a : Over.mk (T.hom ≫ π) ⟶ G) :
    dn hpb (up hpb a) = a := by
  ext; simp [dn, up]

theorem up_dn (hpb : IsPullback β G'.hom G.hom π) {T : Over S} (x : T ⟶ G') : up hpb (dn hpb x) = x := by
  ext; apply hpb.hom_ext <;> simp [dn, up]

end GlobalTheory.Mum.DescGrp

end

namespace GlobalTheory.Mum.DescGrp

variable {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] {S : Scheme.{0}}
  {π : S ⟶ Sp R} {G' : Over S} [GrpObj G'] {G : Over (Sp R)} {β : G'.left ⟶ G.left}

theorem pt_mul (hpb : IsPullback β G'.hom G.hom π) (m : G ⊗ G ⟶ G)
    (hm : ∀ (T : Over S) (x y : T ⟶ G') (x₀ y₀ : Over.mk (T.hom ≫ π) ⟶ G), x₀.left = x.left ≫ β →
      y₀.left = y.left ≫ β → (lift x₀ y₀ ≫ m).left = (x * y).left ≫ β)
    (T : Over S) (a b : Over.mk (T.hom ≫ π) ⟶ G) : lift a b ≫ m = dn hpb (up hpb a * up hpb b) := by
  ext
  rw [hm T (up hpb a) (up hpb b) a b (by simp [up]) (by simp [up])]
  rfl

theorem pt_one (hpb : IsPullback β G'.hom G.hom π) (e : 𝟙_ (Over (Sp R)) ⟶ G)
    (he : ∀ (T : Over S), (toUnit (Over.mk (T.hom ≫ π)) ≫ e).left = (1 : T ⟶ G').left ≫ β) (T : Over S) :
    toUnit (Over.mk (T.hom ≫ π)) ≫ e = dn hpb 1 := by
  ext; rw [he]; rfl

theorem pt_inv (hpb : IsPullback β G'.hom G.hom π) (i : G ⟶ G)
    (hi : ∀ (T : Over S) (x : T ⟶ G') (x₀ : Over.mk (T.hom ≫ π) ⟶ G), x₀.left = x.left ≫ β →
      (x₀ ≫ i).left = x⁻¹.left ≫ β) (T : Over S) (a : Over.mk (T.hom ≫ π) ⟶ G) :
    a ≫ i = dn hpb (up hpb a)⁻¹ := by
  ext; rw [hi T (up hpb a) a (by simp [up])]; rfl

section shapes
variable {G : Over (Sp R)} {T : Over (Sp R)}

theorem sh_assocL (P : T ⟶ (G ⊗ G) ⊗ G) (m : G ⊗ G ⟶ G) :
    P ≫ (m ▷ G) ≫ m = lift (lift (P ≫ fst _ _ ≫ fst _ _) (P ≫ fst _ _ ≫ snd _ _) ≫ m) (P ≫ snd _ _) ≫ m := by
  simp only [← Category.assoc]; congr 1; apply CartesianMonoidalCategory.hom_ext <;> simp <;> (simp only [← Category.assoc]; congr 1; apply CartesianMonoidalCategory.hom_ext <;> simp)
theorem sh_assocR (P : T ⟶ (G ⊗ G) ⊗ G) (m : G ⊗ G ⟶ G) :
    P ≫ (α_ G G G).hom ≫ (G ◁ m) ≫ m =
      lift (P ≫ fst _ _ ≫ fst _ _) (lift (P ≫ fst _ _ ≫ snd _ _) (P ≫ snd _ _) ≫ m) ≫ m := by
  simp only [← Category.assoc]; congr 1; apply CartesianMonoidalCategory.hom_ext <;> simp <;> (simp only [← Category.assoc]; congr 1; apply CartesianMonoidalCategory.hom_ext <;> simp)
theorem sh_oneL (P : T ⟶ G) (e : 𝟙_ (Over (Sp R)) ⟶ G) (m : G ⊗ G ⟶ G) :
    P ≫ (λ_ G).inv ≫ (e ▷ G) ≫ m = lift (toUnit T ≫ e) P ≫ m := by
  simp only [← Category.assoc]; congr 1; apply CartesianMonoidalCategory.hom_ext <;> simp <;> (simp only [← Category.assoc]; congr 1; apply CartesianMonoidalCategory.hom_ext <;> simp)
theorem sh_oneR (P : T ⟶ G) (e : 𝟙_ (Over (Sp R)) ⟶ G) (m : G ⊗ G ⟶ G) :
    P ≫ (ρ_ G).inv ≫ (G ◁ e) ≫ m = lift P (toUnit T ≫ e) ≫ m := by
  simp only [← Category.assoc]; congr 1; apply CartesianMonoidalCategory.hom_ext <;> simp <;> (simp only [← Category.assoc]; congr 1; apply CartesianMonoidalCategory.hom_ext <;> simp)
theorem sh_comm (P : T ⟶ G ⊗ G) (m : G ⊗ G ⟶ G) :
    P ≫ (β_ G G).hom ≫ m = lift (P ≫ snd _ _) (P ≫ fst _ _) ≫ m := by
  simp only [← Category.assoc]; congr 1; apply CartesianMonoidalCategory.hom_ext <;> simp <;> (simp only [← Category.assoc]; congr 1; apply CartesianMonoidalCategory.hom_ext <;> simp)
theorem sh_id (P : T ⟶ G ⊗ G) (m : G ⊗ G ⟶ G) :
    P ≫ m = lift (P ≫ fst _ _) (P ≫ snd _ _) ≫ m := by
  rw [← comp_lift, lift_fst_snd, Category.comp_id]
theorem sh_invL (P : T ⟶ G) (i : G ⟶ G) (m : G ⊗ G ⟶ G) :
    P ≫ lift i (𝟙 G) ≫ m = lift (P ≫ i) P ≫ m := by
  simp only [← Category.assoc]; congr 1; apply CartesianMonoidalCategory.hom_ext <;> simp <;> (simp only [← Category.assoc]; congr 1; apply CartesianMonoidalCategory.hom_ext <;> simp)
theorem sh_invR (P : T ⟶ G) (i : G ⟶ G) (m : G ⊗ G ⟶ G) :
    P ≫ lift (𝟙 G) i ≫ m = lift P (P ≫ i) ≫ m := by
  simp only [← Category.assoc]; congr 1; apply CartesianMonoidalCategory.hom_ext <;> simp <;> (simp only [← Category.assoc]; congr 1; apply CartesianMonoidalCategory.hom_ext <;> simp)
theorem sh_unit (P : T ⟶ G) (e : 𝟙_ (Over (Sp R)) ⟶ G) : P ≫ toUnit G ≫ e = toUnit T ≫ e := by
  rw [← Category.assoc, comp_toUnit]
end shapes

theorem flat_prod2 (G : Over (Sp R)) [Flat G.hom] : Flat (G ⊗ G).hom :=
  inferInstanceAs (Flat (pullback.fst G.hom G.hom ≫ G.hom))
theorem flat_prod3 (G : Over (Sp R)) [Flat G.hom] : Flat ((G ⊗ G) ⊗ G).hom := by
  have := flat_prod2 G
  exact inferInstanceAs (Flat (pullback.fst (G ⊗ G).hom G.hom ≫ (G ⊗ G).hom))

end GlobalTheory.Mum.DescGrp


open GlobalTheory.Mum.DescGrp in
theorem GlobalTheory.Mum.descGrpObj_of_pullback : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] [IsCommMonObj G'] (G : Over (Sp R)) (β : G'.left ⟶ G.left), Smooth G.hom → IsPullback β G'.hom G.hom π → ∀ (m : G ⊗ G ⟶ G) (e : 𝟙_ (Over (Sp R)) ⟶ G) (i : G ⟶ G), (∀ (T : Over S) (x y : T ⟶ G') (x₀ y₀ : Over.mk (T.hom ≫ π) ⟶ G), x₀.left = x.left ≫ β → y₀.left = y.left ≫ β → (lift x₀ y₀ ≫ m).left = (x * y).left ≫ β) → (∀ (T : Over S), (toUnit (Over.mk (T.hom ≫ π)) ≫ e).left = (1 : T ⟶ G').left ≫ β) → (∀ (T : Over S) (x : T ⟶ G') (x₀ : Over.mk (T.hom ≫ π) ⟶ G), x₀.left = x.left ≫ β → (x₀ ≫ i).left = x⁻¹.left ≫ β) → ∃ (_ : GrpObj G) (_ : IsCommMonObj G), IsGrpPullback G' G π β := by
  intro R _ _ _ _ S π hP hS hI G' _ _ G β hsm hpb m e i hm he hi
  haveI : Smooth G.hom := hsm
  have f1 : Flat G.hom := inferInstance
  have f2 : Flat (G ⊗ G).hom := flat_prod2 G
  have f3 : Flat ((G ⊗ G) ⊗ G).hom := flat_prod3 G
  have hM := pt_mul hpb m hm
  have hE := pt_one hpb e he
  have hI' := pt_inv hpb i hi
  have a1 : e ▷ G ≫ m = (λ_ G).hom := by
    rw [← cancel_epi (λ_ G).inv, Iso.inv_hom_id]
    refine ext_of_pts hP hS hI f1 _ _ (fun T P => ?_)
    rw [sh_oneL, Category.comp_id, hE, hM, up_dn, _root_.one_mul, dn_up]
  have a2 : G ◁ e ≫ m = (ρ_ G).hom := by
    rw [← cancel_epi (ρ_ G).inv, Iso.inv_hom_id]
    refine ext_of_pts hP hS hI f1 _ _ (fun T P => ?_)
    rw [sh_oneR, Category.comp_id, hE, hM, up_dn, _root_.mul_one, dn_up]
  have a3 : m ▷ G ≫ m = (α_ G G G).hom ≫ G ◁ m ≫ m := by
    refine ext_of_pts hP hS hI f3 _ _ (fun T P => ?_)
    rw [sh_assocL, sh_assocR]
    simp only [hM, up_dn, _root_.mul_assoc]
  have a4 : lift i (𝟙 G) ≫ m = toUnit G ≫ e := by
    refine ext_of_pts hP hS hI f1 _ _ (fun T P => ?_)
    rw [sh_invL, sh_unit, hE, hI', hM, up_dn, _root_.inv_mul_cancel]
  have a5 : lift (𝟙 G) i ≫ m = toUnit G ≫ e := by
    refine ext_of_pts hP hS hI f1 _ _ (fun T P => ?_)
    rw [sh_invR, sh_unit, hE, hI', hM, up_dn, _root_.mul_inv_cancel]
  have a6 : (β_ G G).hom ≫ m = m := by
    refine ext_of_pts hP hS hI f2 _ _ (fun T P => ?_)
    rw [sh_comm, sh_id P m, hM, hM]
    letI : CommMonoid (T ⟶ G') := Hom.commMonoid
    rw [_root_.mul_comm]
  letI inst : GrpObj G :=
    { one := e, mul := m, inv := i, one_mul := a1, mul_one := a2, mul_assoc := a3, left_inv := a4,
      right_inv := a5 }
  exact ⟨inst, ⟨a6⟩, hpb, fun T x y x₀ y₀ hx hy => by
    rw [Hom.mul_def]; exact hm T x y x₀ y₀ hx hy⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedCommGroupOfPullbackProperSurjectionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.descended_comm_group_of_pullback_proper_surjection : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] [IsCommMonObj G'] (G : Over (Sp R)) (β : G'.left ⟶ G.left), Smooth G.hom → IsPullback β G'.hom G.hom π → ∀ (m : G ⊗ G ⟶ G) (e : 𝟙_ (Over (Sp R)) ⟶ G) (i : G ⟶ G), (∀ (T : Over S) (x y : T ⟶ G') (x₀ y₀ : Over.mk (T.hom ≫ π) ⟶ G), x₀.left = x.left ≫ β → y₀.left = y.left ≫ β → (lift x₀ y₀ ≫ m).left = (x * y).left ≫ β) → (∀ (T : Over S), (toUnit (Over.mk (T.hom ≫ π)) ≫ e).left = (1 : T ⟶ G').left ≫ β) → (∀ (T : Over S) (x : T ⟶ G') (x₀ : Over.mk (T.hom ≫ π) ⟶ G), x₀.left = x.left ≫ β → (x₀ ≫ i).left = x⁻¹.left ≫ β) → ∃ (_ : GrpObj G) (_ : IsCommMonObj G), IsGrpPullback G' G π β := by
  first | exact @GlobalTheory.Mum.descGrpObj_of_pullback | exact GlobalTheory.Mum.descGrpObj_of_pullback | (intros; apply GlobalTheory.Mum.descGrpObj_of_pullback <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupUnitDescendsProperSurjection
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupUnitDescendsProperSurjection
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem pullback_one_left_fst {S P : Scheme.{0}} (f : P ⟶ S) (G' : Over S) [GrpObj G'] :
    (η[(Over.pullback f).obj G'] : _ ⟶ _).left ≫ pullback.fst G'.hom f = f ≫ η[G'].left := by
  simp [Functor.monObjObj]

theorem descend_one : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S : Scheme.{0})
    (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] (G : Over (Sp R))
    (β : G'.left ⟶ G.left), IsPullback β G'.hom G.hom π →
    ∀ φ : (Over.pullback (pullback.fst π π)).obj G' ≅ (Over.pullback (pullback.snd π π)).obj G', IsMonHom φ.hom →
    pullback.fst G'.hom (pullback.fst π π) ≫ β = φ.hom.left ≫ pullback.fst G'.hom (pullback.snd π π) ≫ β →
    ∃ e : 𝟙_ (Over (Sp R)) ⟶ G, ∀ (T : Over S),
      (toUnit (Over.mk (T.hom ≫ π)) ≫ e).left = (1 : T ⟶ G').left ≫ β := by
  intro R _ _ _ _ S π hP hS hI G' _ G β hβ φ hφ hc
  have sq : IsPullback π (𝟙 S) (𝟙 (Sp R)) π := IsPullback.of_id_snd
  have hfl : Flat (𝟙 (Sp R)) := inferInstance

  have heq : pullback.fst π π ≫ (η[G'].left ≫ β) = pullback.snd π π ≫ (η[G'].left ≫ β) := by
    have h1 := pullback_one_left_fst (pullback.fst π π) G'
    have h2 := pullback_one_left_fst (pullback.snd π π) G'
    have hu : (η : _ ⟶ (Over.pullback (pullback.fst π π)).obj G').left ≫ φ.hom.left =
        (η : _ ⟶ (Over.pullback (pullback.snd π π)).obj G').left := by
      rw [← Over.comp_left, IsMonHom.one_hom]
    calc pullback.fst π π ≫ (η[G'].left ≫ β)
        = (η : _ ⟶ (Over.pullback (pullback.fst π π)).obj G').left ≫ pullback.fst G'.hom (pullback.fst π π) ≫ β := by
          rw [reassoc_of% h1]
      _ = (η : _ ⟶ (Over.pullback (pullback.fst π π)).obj G').left ≫ φ.hom.left ≫
            pullback.fst G'.hom (pullback.snd π π) ≫ β := by rw [hc]
      _ = pullback.snd π π ≫ (η[G'].left ≫ β) := by rw [reassoc_of% hu, reassoc_of% h2]
  obtain ⟨h₀, hh₀, -⟩ := GlobalTheory.T.exists_descent_of_equalised_proper_cover_normal R S (Sp R) S G.left π (𝟙 _) π (𝟙 S) hP hS hI hfl sq _ heq

  have hepi : ∀ {W : Scheme.{0}} (a b : Sp R ⟶ W), π ≫ a = π ≫ b → a = b := by
    intro W a b hab
    obtain ⟨c, -, hc'⟩ := GlobalTheory.T.exists_descent_of_equalised_proper_cover_normal R S (Sp R) S W π (𝟙 _) π (𝟙 S) hP hS hI hfl sq (π ≫ a)
      (by rw [pullback.condition_assoc])
    exact (hc' a rfl).trans (hc' b hab.symm).symm
  have hsec : h₀ ≫ G.hom = 𝟙 (Sp R) := by
    apply hepi
    rw [reassoc_of% hh₀, hβ.w]
    simp
  refine ⟨Over.homMk h₀ (by simpa using hsec), fun T => ?_⟩
  simp [Hom.one_def]
  rw [hh₀]

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupUnitDescendsProperSurjectionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.group_unit_descends_proper_surjection : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] (G : Over (Sp R)) (β : G'.left ⟶ G.left), IsPullback β G'.hom G.hom π → ∀ φ : (Over.pullback (pullback.fst π π)).obj G' ≅ (Over.pullback (pullback.snd π π)).obj G', IsMonHom φ.hom → pullback.fst G'.hom (pullback.fst π π) ≫ β = φ.hom.left ≫ pullback.fst G'.hom (pullback.snd π π) ≫ β → ∃ e : 𝟙_ (Over (Sp R)) ⟶ G, ∀ (T : Over S), (toUnit (Over.mk (T.hom ≫ π)) ≫ e).left = (1 : T ⟶ G').left ≫ β := by
  first | exact @GlobalTheory.Mum.descend_one | exact GlobalTheory.Mum.descend_one | (intros; apply GlobalTheory.Mum.descend_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupMultiplicationDescendsProperSurjection
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupMultiplicationDescendsProperSurjection
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.GrpDescent

section Pt
variable {S X : Scheme.{0}} (G' : Over S) (f : X ⟶ S)

def ptOf {T : Over X} (a : T.left ⟶ G'.left) (ha : a ≫ G'.hom = T.hom ≫ f) : T ⟶ (Over.pullback f).obj G' :=
  Over.homMk (pullback.lift a T.hom ha) (pullback.lift_snd _ _ _)

theorem ptOf_fst {T : Over X} (a : T.left ⟶ G'.left) (ha : a ≫ G'.hom = T.hom ≫ f) :
    (ptOf G' f a ha).left ≫ pullback.fst G'.hom f = a := pullback.lift_fst _ _ _

theorem ptOf_mul [GrpObj G'] {T : Over X} (w : T.left ⟶ (G' ⊗ G').left) (hw : w ≫ (G' ⊗ G').hom = T.hom ≫ f)
    (h₁ : (w ≫ (fst G' G').left) ≫ G'.hom = T.hom ≫ f) (h₂ : (w ≫ (snd G' G').left) ≫ G'.hom = T.hom ≫ f) :
    (ptOf G' f _ h₁ * ptOf G' f _ h₂).left ≫ pullback.fst G'.hom f = w ≫ μ[G'].left := by
  let U : Over.mk (T.hom ≫ f) ⟶ G' ⊗ G' := Over.homMk w hw
  have e := (isGrpPullback_pullback G' f).2 T (ptOf G' f _ h₁) (ptOf G' f _ h₂) (U ≫ fst G' G') (U ≫ snd G' G')
    (ptOf_fst G' f _ h₁).symm (ptOf_fst G' f _ h₂).symm
  rw [← e, ← MonObj.comp_mul, Hom.mul_def, lift_fst_snd, Category.id_comp]
  rfl

end Pt

theorem mul_descends : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] (G : Over (Sp R)) (β : G'.left ⟶ G.left), Smooth G.hom → IsPullback β G'.hom G.hom π → ∀ φ : (Over.pullback (pullback.fst π π)).obj G' ≅ (Over.pullback (pullback.snd π π)).obj G', IsMonHom φ.hom → pullback.fst G'.hom (pullback.fst π π) ≫ β = φ.hom.left ≫ pullback.fst G'.hom (pullback.snd π π) ≫ β → ∃ m : G ⊗ G ⟶ G, ∀ (T : Over S) (x y : T ⟶ G') (x₀ y₀ : Over.mk (T.hom ≫ π) ⟶ G), x₀.left = x.left ≫ β → y₀.left = y.left ≫ β → (lift x₀ y₀ ≫ m).left = (x * y).left ≫ β := by
  intro R _ _ _ _ S π hprop hsurj hint G' _ G β hsm hβ φ hφ hdat
  haveI := hsm
  haveI : Smooth (G ⊗ G).hom := inferInstanceAs (Smooth (pullback.fst G.hom G.hom ≫ G.hom))
  have hflat : Flat (G ⊗ G).hom := inferInstance
  let Z' : Over (Sp R) := Over.mk ((G' ⊗ G').hom ≫ π)
  let u : Z' ⟶ G := Over.homMk ((fst G' G').left ≫ β) (by
    show ((fst G' G').left ≫ β) ≫ G.hom = (G' ⊗ G').hom ≫ π
    rw [Category.assoc, hβ.w, ← Category.assoc, Over.w])
  let v : Z' ⟶ G := Over.homMk ((snd G' G').left ≫ β) (by
    show ((snd G' G').left ≫ β) ≫ G.hom = (G' ⊗ G').hom ≫ π
    rw [Category.assoc, hβ.w, ← Category.assoc, Over.w])
  let p : (G' ⊗ G').left ⟶ (G ⊗ G).left := (lift u v).left
  have hp1 : p ≫ (fst G G).left = (fst G' G').left ≫ β := by
    show (lift u v ≫ fst G G).left = _
    rw [lift_fst]; rfl
  have hp2 : p ≫ (snd G G).left = (snd G' G').left ≫ β := by
    show (lift u v ≫ snd G G).left = _
    rw [lift_snd]; rfl
  have hA : IsPullback (fst G' G').left (snd G' G').left G'.hom G'.hom := IsPullback.of_hasPullback _ _
  have hB : IsPullback (fst G G).left (snd G G).left G.hom G.hom := IsPullback.of_hasPullback _ _
  have htop : IsPullback p (snd G' G').left (snd G G).left β := by
    refine IsPullback.of_right (h₁₂ := (fst G G).left) (h₂₂ := G.hom) ?_ hp2 hB
    rw [hp1, hβ.w]
    exact hA.paste_horiz hβ
  have hpb : IsPullback p (G' ⊗ G').hom (G ⊗ G).hom π := by
    have h := htop.paste_vert hβ
    rwa [Over.w (snd G' G'), Over.w (snd G G)] at h

  have hepi : ∀ {W : Scheme.{0}} (a b : (G ⊗ G).left ⟶ W), p ≫ a = p ≫ b → a = b := by
    intro W a b hab
    obtain ⟨c, -, hc⟩ := GlobalTheory.T.exists_descent_of_equalised_proper_cover_normal R S _ _ W π _ p _ hprop hsurj hint hflat hpb (p ≫ a)
      (by rw [← Category.assoc, pullback.condition, Category.assoc])
    exact (hc a rfl).trans (hc b hab.symm).symm

  have heq : pullback.fst p p ≫ μ[G'].left ≫ β = pullback.snd p p ≫ μ[G'].left ≫ β := by
    set f₁ := pullback.fst p p
    set f₂ := pullback.snd p p
    have hf : f₁ ≫ p = f₂ ≫ p := pullback.condition
    have hs : (f₁ ≫ (G' ⊗ G').hom) ≫ π = (f₂ ≫ (G' ⊗ G').hom) ≫ π := by
      rw [Category.assoc, Category.assoc, ← hpb.w, ← Category.assoc, hf, Category.assoc]
    let σ := pullback.lift _ _ hs
    let T₀ : Over (pullback π π) := Over.mk σ
    have hw₁ : f₁ ≫ (G' ⊗ G').hom = T₀.hom ≫ pullback.fst π π := (pullback.lift_fst _ _ hs).symm
    have hw₂ : f₂ ≫ (G' ⊗ G').hom = T₀.hom ≫ pullback.snd π π := (pullback.lift_snd _ _ hs).symm

    have htr : ∀ (a₁ a₂ : T₀.left ⟶ G'.left) (h₁ : a₁ ≫ G'.hom = T₀.hom ≫ pullback.fst π π)
        (h₂ : a₂ ≫ G'.hom = T₀.hom ≫ pullback.snd π π), a₁ ≫ β = a₂ ≫ β →
        ptOf G' (pullback.fst π π) a₁ h₁ ≫ φ.hom = ptOf G' (pullback.snd π π) a₂ h₂ := by
      intro a₁ a₂ h₁ h₂ hb
      apply Over.OverMorphism.ext
      apply pullback.hom_ext
      · apply hβ.hom_ext
        · rw [Over.comp_left, Category.assoc, Category.assoc, ← hdat, ← Category.assoc, ptOf_fst, ptOf_fst, hb]
        · rw [Category.assoc, pullback.condition, ptOf_fst, h₂, ← Category.assoc]
          exact congrArg (· ≫ pullback.snd π π) (Over.w (ptOf G' (pullback.fst π π) a₁ h₁ ≫ φ.hom))
      · exact (Over.w (ptOf G' (pullback.fst π π) a₁ h₁ ≫ φ.hom)).trans (Over.w (ptOf G' (pullback.snd π π) a₂ h₂)).symm
    have hb₁ : (f₁ ≫ (fst G' G').left) ≫ β = (f₂ ≫ (fst G' G').left) ≫ β := by
      rw [Category.assoc, Category.assoc, ← hp1, ← Category.assoc, hf, Category.assoc]
    have hb₂ : (f₁ ≫ (snd G' G').left) ≫ β = (f₂ ≫ (snd G' G').left) ≫ β := by
      rw [Category.assoc, Category.assoc, ← hp2, ← Category.assoc, hf, Category.assoc]
    have k₁ : (f₁ ≫ (fst G' G').left) ≫ G'.hom = T₀.hom ≫ pullback.fst π π := by rw [Category.assoc, Over.w, hw₁]
    have k₂ : (f₁ ≫ (snd G' G').left) ≫ G'.hom = T₀.hom ≫ pullback.fst π π := by rw [Category.assoc, Over.w, hw₁]
    have l₁ : (f₂ ≫ (fst G' G').left) ≫ G'.hom = T₀.hom ≫ pullback.snd π π := by rw [Category.assoc, Over.w, hw₂]
    have l₂ : (f₂ ≫ (snd G' G').left) ≫ G'.hom = T₀.hom ≫ pullback.snd π π := by rw [Category.assoc, Over.w, hw₂]
    have e₁ := ptOf_mul G' (pullback.fst π π) (T := T₀) f₁ hw₁ k₁ k₂
    have e₂ := ptOf_mul G' (pullback.snd π π) (T := T₀) f₂ hw₂ l₁ l₂
    have hAB : (ptOf G' (pullback.fst π π) (T := T₀) _ k₁ * ptOf G' (pullback.fst π π) (T := T₀) _ k₂) ≫ φ.hom =
        ptOf G' (pullback.snd π π) (T := T₀) _ l₁ * ptOf G' (pullback.snd π π) (T := T₀) _ l₂ := by
      refine ((IsMonHom.monoidHom φ.hom T₀).map_mul _ _).trans ?_
      show (ptOf G' (pullback.fst π π) (T := T₀) _ k₁ ≫ φ.hom) * (ptOf G' (pullback.fst π π) (T := T₀) _ k₂ ≫ φ.hom) = _
      rw [htr _ _ k₁ l₁ hb₁, htr _ _ k₂ l₂ hb₂]
    rw [← Category.assoc f₁, ← e₁, ← Category.assoc f₂, ← e₂, ← hAB, Over.comp_left]
    simp only [Category.assoc]
    rw [hdat]
  obtain ⟨h₀, hh₀, -⟩ := GlobalTheory.T.exists_descent_of_equalised_proper_cover_normal R S _ _ _ π _ p _ hprop hsurj hint hflat hpb (μ[G'].left ≫ β) heq
  have hover : h₀ ≫ G.hom = (G ⊗ G).hom := by
    apply hepi
    rw [← Category.assoc, hh₀, Category.assoc, hβ.w, ← Category.assoc, Over.w μ[G'], hpb.w]
  refine ⟨Over.homMk h₀ hover, fun T x y x₀ y₀ hx hy => ?_⟩
  have hl : (lift x₀ y₀).left = (lift x y).left ≫ p := by
    apply hB.hom_ext
    · rw [Category.assoc, hp1, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst, hx]
    · rw [Category.assoc, hp2, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_snd, lift_snd, hy]
  rw [Over.comp_left, hl]
  change ((lift x y).left ≫ p) ≫ h₀ = _
  rw [Category.assoc, hh₀, Hom.mul_def, Over.comp_left, Category.assoc]

end GlobalTheory.GrpDescent
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupMultiplicationDescendsProperSurjectionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.group_multiplication_descends_proper_surjection : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] (G : Over (Sp R)) (β : G'.left ⟶ G.left), Smooth G.hom → IsPullback β G'.hom G.hom π → ∀ φ : (Over.pullback (pullback.fst π π)).obj G' ≅ (Over.pullback (pullback.snd π π)).obj G', IsMonHom φ.hom → pullback.fst G'.hom (pullback.fst π π) ≫ β = φ.hom.left ≫ pullback.fst G'.hom (pullback.snd π π) ≫ β → ∃ m : G ⊗ G ⟶ G, ∀ (T : Over S) (x y : T ⟶ G') (x₀ y₀ : Over.mk (T.hom ≫ π) ⟶ G), x₀.left = x.left ≫ β → y₀.left = y.left ≫ β → (lift x₀ y₀ ≫ m).left = (x * y).left ≫ β := by
  first | exact @GlobalTheory.GrpDescent.mul_descends | exact GlobalTheory.GrpDescent.mul_descends | (intros; apply GlobalTheory.GrpDescent.mul_descends <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSeparatedOfIsPullbackUniversallyClosedSurjectiStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSeparatedOfIsPullbackUniversallyClosedSurjective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.SepDescent

def closedRange : MorphismProperty Scheme.{0} := fun _ _ f => IsClosed (Set.range f.base)

lemma range_iso_comp {X Y Z : Scheme.{0}} (e : X ≅ Y) (f : Y ⟶ Z) :
    Set.range (e.hom ≫ f).base = Set.range f.base := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨e.hom.base x, by simp⟩
  · rintro ⟨y, rfl⟩
    refine ⟨e.inv.base y, ?_⟩
    rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id_assoc]

instance : closedRange.RespectsIso := by
  apply MorphismProperty.RespectsIso.mk
  · intro X Y Z e f hf
    change IsClosed _
    rw [range_iso_comp]
    exact hf
  · intro X Y Z e f hf
    change IsClosed _
    have : Set.range (f ≫ e.hom).base = e.hom.base '' Set.range f.base := by
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    rw [this]
    exact e.hom.isClosedMap _ hf

instance : closedRange.DescendsAlong (@UniversallyClosed ⊓ @Surjective) := by
  apply MorphismProperty.DescendsAlong.mk'
  intro X Y Z f g _ hf hfst
  haveI : UniversallyClosed f := hf.1
  have hs : Function.Surjective f.base := hf.2.surj
  have e : Set.range g.base = f.base '' Set.range (pullback.fst f g).base := by
    rw [Scheme.Pullback.range_fst, Set.image_preimage_eq _ hs]
  change IsClosed _
  rw [e]
  exact f.isClosedMap _ hfst

instance : (@UniversallyClosed ⊓ @Surjective : MorphismProperty Scheme.{0}).IsStableUnderBaseChange :=
  @MorphismProperty.IsStableUnderBaseChange.inf _ _ _ _ inferInstance inferInstance

instance : (MorphismProperty.diagonal closedRange).DescendsAlong
    (@UniversallyClosed ⊓ @Surjective : MorphismProperty Scheme.{0}) :=
  inferInstance

end GlobalTheory.SepDescent


open GlobalTheory.SepDescent in
theorem GlobalTheory.isSeparated_of_isPullback_universallyClosed_surjective :
    ∀ (R : Type) [CommRing R] (S : Scheme.{0}) (π : S ⟶ Sp R), UniversallyClosed π → Surjective π →
    ∀ (G' : Over S) (G : Over (Sp R)) (β : G'.left ⟶ G.left),
    IsPullback β G'.hom G.hom π → IsSeparated G'.hom → IsSeparated G.hom := by
  intro R _ S π h1 h2 G' G β hp hs
  have hd : (MorphismProperty.diagonal closedRange) G.hom :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := MorphismProperty.diagonal closedRange)
      (Q := @UniversallyClosed ⊓ @Surjective) hp.flip ⟨h1, h2⟩
      (pullback.diagonal G'.hom).isClosedMap.isClosed_range
  exact ⟨IsClosedImmersion.of_isPreimmersion _ hd⟩
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSeparated_of_isPullback_universallyClosed_surjective' : ∀ (R : Type) [CommRing R] (S : Scheme.{0}) (π : S ⟶ Sp R), UniversallyClosed π → Surjective π → ∀ (G' : Over S) (G : Over (Sp R)) (β : G'.left ⟶ G.left), IsPullback β G'.hom G.hom π → IsSeparated G'.hom → IsSeparated G.hom := by
  first | exact @GlobalTheory.isSeparated_of_isPullback_universallyClosed_surjective | exact GlobalTheory.isSeparated_of_isPullback_universallyClosed_surjective | (intros; apply GlobalTheory.isSeparated_of_isPullback_universallyClosed_surjective <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricallyConnectedOfIsPullbackSurjectiveLft
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricallyConnectedOfIsPullbackSurjectiveLft
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem geometricallyConnected_of_isPullback_of_surjective :
    ∀ (R : Type) [CommRing R] (S : Scheme.{0}) (π : S ⟶ Sp R), LocallyOfFiniteType π → Surjective π →
    ∀ (G' : Over S) (G : Over (Sp R)) (β : G'.left ⟶ G.left), IsPullback β G'.hom G.hom π →
    GeometricallyConnected G'.hom → GeometricallyConnected G.hom := by
  intro R _ S π hlft hsurj G' G β hpb hG'
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ y ↦ ?_⟩
  let jK : Spec (.of (AlgebraicClosure K)) ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))
  obtain ⟨t, ht⟩ := GlobalTheory.GeomSurj.exists_lift_of_surjective (Ω := AlgebraicClosure K) π (jK ≫ y)
  have hct : ConnectedSpace ↥(pullback G'.hom t) :=
    pullback_of_geometrically hG'.geometrically_connectedSpace _ t
  have hP : IsPullback (pullback.fst G'.hom t ≫ β) (pullback.snd G'.hom t) G.hom (t ≫ π) :=
    (IsPullback.of_hasPullback G'.hom t).paste_horiz hpb
  rw [← ht] at hP
  have hc' : ConnectedSpace ↥(pullback G.hom (jK ≫ y)) :=
    hP.isoPullback.hom.homeomorph.connectedSpace_iff.mp hct
  have hjK : Surjective jK := ⟨fun z ↦ by
    obtain ⟨w⟩ : Nonempty ↥(Spec (.of (AlgebraicClosure K))) := inferInstance
    exact ⟨w, Subsingleton.elim _ _⟩⟩
  have hc'' : ConnectedSpace ↥(pullback (pullback.snd G.hom y) jK) :=
    (pullbackLeftPullbackSndIso G.hom y jK).hom.homeomorph.connectedSpace_iff.mpr hc'
  exact (pullback.fst (pullback.snd G.hom y) jK).surjective.connectedSpace
    (pullback.fst (pullback.snd G.hom y) jK).continuous

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricallyConnectedOfIsPullbackSurjectiveLftStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometricallyConnected_of_isPullback_surjective_lft : ∀ (R : Type) [CommRing R] (S : Scheme.{0}) (π : S ⟶ Sp R), LocallyOfFiniteType π → Surjective π → ∀ (G' : Over S) (G : Over (Sp R)) (β : G'.left ⟶ G.left), IsPullback β G'.hom G.hom π → GeometricallyConnected G'.hom → GeometricallyConnected G.hom := by
  first | exact @GlobalTheory.Mum.geometricallyConnected_of_isPullback_of_surjective | exact GlobalTheory.Mum.geometricallyConnected_of_isPullback_of_surjective | (intros; apply GlobalTheory.Mum.geometricallyConnected_of_isPullback_of_surjective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionGeometricFibresOfDescendedGroup
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionGeometricFibresOfDescendedGroup
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem torusExtension_of_descended : ∀ (R : Type) [CommRing R] (S : Scheme.{0}) (π : S ⟶ Sp R), LocallyOfFiniteType π → Surjective π → ∀ (G' : Over S) [GrpObj G'] (G : Over (Sp R)) [GrpObj G] (β : G'.left ⟶ G.left), IsGrpPullback G' G π β → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ S), Nonempty (TorusExtension ((Over.pullback t).obj G'))) → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (p : Spec (.of Ω) ⟶ Sp R), Nonempty (TorusExtension ((Over.pullback p).obj G)) := by
  intro R _ S π hlft hsurj G' _ G _ β h hG' Ω _ _ p
  haveI := hlft
  haveI := hsurj
  obtain ⟨t, rfl⟩ := GlobalTheory.GeomSurj.exists_lift_of_surjective π p
  have h1 := (isGrpPullback_pullback G' t).comp h
  have h2 := isGrpPullback_pullback G (t ≫ π)
  obtain ⟨e, he, -⟩ := grpPullback_iso h1 h2
  haveI := he
  exact ⟨torusExtOfIso e (hG' Ω t).some⟩

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionGeometricFibresOfDescendedGroupStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusExtension_geometricFibres_of_descended_group : ∀ (R : Type) [CommRing R] (S : Scheme.{0}) (π : S ⟶ Sp R), LocallyOfFiniteType π → Surjective π → ∀ (G' : Over S) [GrpObj G'] (G : Over (Sp R)) [GrpObj G] (β : G'.left ⟶ G.left), IsGrpPullback G' G π β → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ S), Nonempty (TorusExtension ((Over.pullback t).obj G'))) → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (p : Spec (.of Ω) ⟶ Sp R), Nonempty (TorusExtension ((Over.pullback p).obj G)) := by
  first | exact @GlobalTheory.Mum.torusExtension_of_descended | exact GlobalTheory.Mum.torusExtension_of_descended | (intros; apply GlobalTheory.Mum.torusExtension_of_descended <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiAbelianDescentAlongProperSurjective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.DescGrp

theorem quasiCompact_of_isPullback {R : Type} [CommRing R] {S : Scheme.{0}} (π : S ⟶ Sp R) [Surjective π]
    (G' : Over S) (G : Over (Sp R)) (β : G'.left ⟶ G.left) (h : IsPullback β G'.hom G.hom π) [QuasiCompact π]
    [QuasiCompact G'.hom] : QuasiCompact G.hom := by
  have hs : Surjective β := MorphismProperty.of_isPullback (P := @Surjective) h.flip ‹_›
  have hc : QuasiCompact (β ≫ G.hom) := by rw [h.w]; infer_instance
  rw [quasiCompact_iff] at hc ⊢
  intro U hU hK
  have := (hc U hU hK).image β.continuous
  rwa [Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp, Set.image_preimage_eq _ hs.surj] at this

theorem exists_semiAbelian_descent : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (G : Over (Sp R)) (β : G'.left ⟶ G.left), Smooth G.hom → IsPullback β G'.hom G.hom π → ∀ φ : (Over.pullback (pullback.fst π π)).obj G' ≅ (Over.pullback (pullback.snd π π)).obj G', IsMonHom φ.hom → pullback.fst G'.hom (pullback.fst π π) ≫ β = φ.hom.left ≫ pullback.fst G'.hom (pullback.snd π π) ≫ β → ∃ (_ : GrpObj G) (_ : IsCommMonObj G), IsSemiAbelian G ∧ IsGrpPullback G' G π β := by
  intro R _ _ _ _ S π hp hs hi G' _ _ hG G β hsm hpb φ hφ hc
  obtain ⟨m, hm⟩ := GlobalTheory.T.group_multiplication_descends_proper_surjection R S π hp hs hi G' G β hsm hpb φ hφ hc
  obtain ⟨e, he⟩ := GlobalTheory.T.group_unit_descends_proper_surjection R S π hp hs hi G' G β hpb φ hφ hc
  obtain ⟨i, hiv⟩ := GlobalTheory.T.group_inverse_descends_proper_surjection R S π hp hs hi G' G β hsm hpb φ hφ hc
  obtain ⟨g, c, hP⟩ := GlobalTheory.T.descended_comm_group_of_pullback_proper_surjection R S π hp hs hi G' G β hsm hpb m e i hm he hiv
  haveI := hG.quasiCompact
  refine ⟨g, c, ⟨c, hsm, GlobalTheory.T.isSeparated_of_isPullback_universallyClosed_surjective' R S π inferInstance hs G' G β hpb hG.separated,
    quasiCompact_of_isPullback π G' G β hpb,
    GlobalTheory.T.geometricallyConnected_of_isPullback_surjective_lft R S π inferInstance hs G' G β hpb hG.geomConnected,
    GlobalTheory.T.torusExtension_geometricFibres_of_descended_group R S π inferInstance hs G' G β hP hG.fibres⟩, hP⟩

end GlobalTheory.DescGrp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiAbelianDescentAlongProperSurjectiveStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_semiAbelian_descent_along_proper_surjective : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (G : Over (Sp R)) (β : G'.left ⟶ G.left), Smooth G.hom → IsPullback β G'.hom G.hom π → ∀ φ : (Over.pullback (pullback.fst π π)).obj G' ≅ (Over.pullback (pullback.snd π π)).obj G', IsMonHom φ.hom → pullback.fst G'.hom (pullback.fst π π) ≫ β = φ.hom.left ≫ pullback.fst G'.hom (pullback.snd π π) ≫ β → ∃ (_ : GrpObj G) (_ : IsCommMonObj G), IsSemiAbelian G ∧ IsGrpPullback G' G π β := by
  first | exact @GlobalTheory.DescGrp.exists_semiAbelian_descent | exact GlobalTheory.DescGrp.exists_semiAbelian_descent | (intros; apply GlobalTheory.DescGrp.exists_semiAbelian_descent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianDescendsOfDescendsNearClosedFibre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem descend_of_near : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) →
    ∀ (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G']
    [IsCommMonObj G'], IsSemiAbelian G' → ∀ N : Near π G', N.Law → ∃ (G : Over (Sp R)) (_ : GrpObj G)
    (_ : IsCommMonObj G) (β : G'.left ⟶ G.left) (i : N.U ⟶ G), IsSemiAbelian G ∧ IsGrpPullback G' G π β ∧
    IsOpenImmersion i.left ∧ N.u ≫ β = pullback.fst _ _ ≫ i.left := by
  intro R _ _ _ hA S π hP hS hI G' _ _ hG' N hL
  have hNoeth : IsNoetherianRing R := hA.1
  have hIC : IsIntegrallyClosed R := hA.2.2.1
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.exists_descentDatum_of_descendedMultiplication R hA S π hP hS hI G' hG' N hL
  obtain ⟨G, β, i, hsm, hpb, hop, hu, hc⟩ := GlobalTheory.T.semiAbelian_descends_near_closedFibre R hA S π hP hS hI G' hG' N hL φ hφ
  obtain ⟨g, c, hsa, hgp⟩ := GlobalTheory.T.exists_semiAbelian_descent_along_proper_surjective R S π hP hS hI G' hG' G β hsm hpb φ hφ.1 hc
  exact ⟨G, g, c, β, i, hsa, hgp, hop, hu⟩

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianDescendsOfDescendsNearClosedFibreStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiAbelian_descends_of_descends_near_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ N : Near π G', N.Law → ∃ (G : Over (Sp R)) (_ : GrpObj G) (_ : IsCommMonObj G) (β : G'.left ⟶ G.left) (i : N.U ⟶ G), IsSemiAbelian G ∧ IsGrpPullback G' G π β ∧ IsOpenImmersion i.left ∧ N.u ≫ β = pullback.fst _ _ ≫ i.left := by
  first | exact @GlobalTheory.Mum.descend_of_near | exact GlobalTheory.Mum.descend_of_near | (intros; apply GlobalTheory.Mum.descend_of_near <;> assumption)
end
