module

public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEquivOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueTorusExtensionPointOfGroupPoint
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NonemptyGtCoordOfIsGt
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CommGroupCommonFactorQuotientCancel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AbelianPartImageEqOneIffTorusPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AbelianPartImageEqOneIffTorusPoint
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UU

section Kernel

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {G B T : Over S} {G' : Over S'} [GrpObj B] [GrpObj G']
  {X : Type} [AddCommGroup X]

theorem TQ.mono_i_left (Q : TQ G' X) : Mono Q.i.left := by
  have : Mono Q.i := ⟨fun _ _ h => Q.isKernel.hom_ext h (toUnit_unique _ _)⟩
  infer_instance

theorem TQ.image_eq_one_iff (Q : TQ G' X) {β : Q.B.left ⟶ B.left} (hB : IsGrpPullback Q.B B f β)
    {Z : Scheme.{0}} (r : Z ⟶ T.left) (xe : Z ⟶ G'.left) (hc : r ≫ T.hom = (xe ≫ G'.hom) ≫ f) :
    xe ≫ Q.q.left ≫ β = r ≫ (1 : T ⟶ B).left ↔ ∃ τ : Z ⟶ (splitTorus S' X).left, τ ≫ Q.i.left = xe := by
  obtain ⟨eB, heB⟩ := GlobalTheory.exists_mulEquiv_of_isGrpPullback hB _ _ hc
  let R : Over.mk (r ≫ T.hom) ⟶ T := Over.homMk r rfl
  let xe' : Over.mk (xe ≫ G'.hom) ⟶ G' := Over.homMk xe rfl
  have e₁ : (eB (xe' ≫ Q.q)).left = xe ≫ Q.q.left ≫ β := (heB _).trans (Category.assoc _ _ _)
  have e₂ : (eB 1).left = r ≫ (1 : T ⟶ B).left := by
    rw [map_one, ← MonObj.comp_one R]; rfl
  rw [← e₁, ← e₂]
  constructor
  · intro h
    have h₁ : xe' ≫ Q.q = toUnit _ ≫ η[Q.B] := eB.injective (Over.OverMorphism.ext h)
    exact ⟨(Q.isKernel.lift _ _ h₁).left, congrArg (fun z => z.left) (Q.isKernel.lift_fst _ _ h₁)⟩
  · rintro ⟨τ, hτ⟩
    let τ' : Over.mk (xe ≫ G'.hom) ⟶ splitTorus S' X := Over.homMk τ (by
      rw [← hτ, ← Over.w Q.i]; exact (Category.assoc _ _ _).symm)
    have h₁ : τ' ≫ Q.i = xe' := Over.OverMorphism.ext hτ
    have h₂ : xe' ≫ Q.q = 1 := by
      rw [← h₁, Category.assoc, Q.isKernel.w, ← Category.assoc, Hom.one_def, toUnit_unique (τ' ≫ toUnit _)]
    rw [h₂]

end Kernel

section Scal

variable {A C : Type} [CommRing A] [CommRing C] {Y Y' : Scheme.{0}}

noncomputable def scalRingHom (p : Y ⟶ Spec (CommRingCat.of A)) : A →+* Γ(Y, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ p.appTop).hom

theorem scalRingHom_specMap (p : Y ⟶ Spec (CommRingCat.of C)) (φ : A →+* C) :
    scalRingHom (p ≫ Spec.map (CommRingCat.ofHom φ)) = (scalRingHom p).comp φ :=
  congrArg CommRingCat.Hom.hom (SplitTorusPoints.ΓSpecIso_inv_comp_specMap p (CommRingCat.ofHom φ))

theorem exists_factor_quotient (r : Y ⟶ Spec (CommRingCat.of C)) (J : Ideal C)
    (h : J ≤ RingHom.ker (scalRingHom r)) :
    ∃ r' : Y ⟶ Spec (CommRingCat.of (C ⧸ J)), r' ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) = r := by
  refine ⟨Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift J (scalRingHom r) fun _ ha => RingHom.mem_ker.1 (h ha))), ?_⟩
  rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.Quotient.lift_comp_mk]
  apply ext_to_Spec
  refine (SplitTorusPoints.ΓSpecIso_inv_comp_specMap _ _).trans ?_
  rw [Scheme.toSpecΓ_appTop, Iso.inv_hom_id, Category.comp_id]
  rfl

theorem exists_factor_thick (φ : A →+* C) (I : Ideal A) (e : ℕ) (r : Y ⟶ Spec (CommRingCat.of C))
    (p : Y ⟶ Spec (CommRingCat.of (A ⧸ I ^ (e + 1))))
    (h : p ≫ thick A I e = r ≫ Spec.map (CommRingCat.ofHom φ)) :
    ∃ r' : Y ⟶ Spec (CommRingCat.of (C ⧸ I.map φ ^ (e + 1))), r' ≫ thick C (I.map φ) e = r := by
  refine exists_factor_quotient r _ ?_
  rw [← Ideal.map_pow, Ideal.map_le_iff_le_comap]
  intro a ha
  have := congrArg (fun q => scalRingHom q a) h
  simp only [scalRingHom_specMap, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero] at this
  exact this.symm

theorem exists_torus_point {S : Scheme.{0}} {X : Type} [AddCommGroup X] (c : Multiplicative X →* Cˣ)
    (r : Y ⟶ Spec (CommRingCat.of C)) (p : Y ⟶ S) : ∃ τ : Y ⟶ (splitTorus S X).left, τ ≫ (splitTorus S X).hom = p ∧
      ∀ χ, τ.appTop.hom (charUnit S X χ).val = scal r (c (Multiplicative.ofAdd χ)).val := by
  obtain ⟨τ, hτ⟩ := (splitTorusPointsEquiv S X (Over.mk p)).surjective
    ((Units.map (scalRingHom r).toMonoidHom).comp c)
  refine ⟨τ.left, Over.w τ, fun χ => ?_⟩
  refine (splitTorusPointsEquiv_val S X _ τ χ).symm.trans ?_
  rw [hτ]; rfl

theorem exists_hom_of_thick {X : Type} [AddCommGroup X] (J : Ideal C) [IsAdicComplete J C] {S : ℕ → Scheme.{0}}
    (τ : ∀ e, Spec (CommRingCat.of (C ⧸ J ^ (e + 1))) ⟶ (splitTorus (S e) X).left)
    (h : ∀ e χ, (thickTrans C J e ≫ τ (e + 1)).appTop.hom (charUnit _ X χ).val =
      (τ e).appTop.hom (charUnit _ X χ).val) :
    ∃ c : Multiplicative X →* Cˣ, ∀ e χ,
      (τ e).appTop.hom (charUnit _ X χ).val = scal (thick C J e) (c (Multiplicative.ofAdd χ)).val := by
  let u := fun e => splitTorusPointsEquiv (S e) X (Over.mk (τ e ≫ (splitTorus (S e) X).hom)) (Over.homMk (τ e) rfl)
  have hu : ∀ e χ, (u e (Multiplicative.ofAdd χ)).val = (τ e).appTop.hom (charUnit _ X χ).val := fun e χ =>
    splitTorusPointsEquiv_val _ _ _ _ χ
  choose b hb using fun χ : X => CompletePoint.exists_fn_of_thick J (fun e => (τ e).appTop.hom (charUnit _ X χ).val)
    fun e => by rw [← h e χ, Scheme.Hom.comp_appTop]; rfl
  let b' : Multiplicative X →* Γ(Spec (CommRingCat.of C), ⊤) :=
    { toFun := fun χ => b χ.toAdd
      map_one' := CompletePoint.fn_eq_of_thick J fun e => by
        rw [hb, ← hu]; exact (congrArg Units.val (map_one (u e))).trans (map_one _).symm
      map_mul' := fun χ χ' => CompletePoint.fn_eq_of_thick J fun e => by
        rw [(thick C J e).appTop.hom.map_mul, hb, hb, hb, ← hu, ← hu, ← hu]
        exact congrArg Units.val (map_mul (u e) χ χ') }
  refine ⟨((Scheme.ΓSpecIso (CommRingCat.of C)).hom.hom.toMonoidHom.comp b').toHomUnits, fun e χ => ?_⟩
  rw [← hb]
  exact congrArg (thick C J e).appTop.hom (Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of C)) (b χ)).symm

end Scal

theorem image_eq_one_iff_torus_point : AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (a : t.Alg) (W : Type) [CommRing W] [IsLocalRing W] [Algebra V W], IsAdicComplete ((IsLocalRing.maximalIdeal V).map (algebraMap V W)) W → IsLocalHom (algebraMap V W) → ∀ x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ (x).left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ ((1 : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ a.B)).left) ↔ ∃ c : Multiplicative s.X →* Wˣ, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (τ : Z ⟶ (splitTorus _ s.X).left), τ ≫ (splitTorus (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1)))) s.X).hom ≫ thick V _ e = r ≫ (Spec.map (CommRingCat.ofHom (algebraMap V W))) → (∀ χ, τ.appTop.hom (charUnit _ s.X χ).val = scal r (c (Multiplicative.ofAdd χ)).val) → τ ≫ (t.l e).Q.i.left ≫ (fstG _ e G).left = r ≫ (x).left) := by
  intro V _ _ _ A G _ _ s t a W _ _ _ hW _ x
  let I := IsLocalRing.maximalIdeal V
  let φ := algebraMap V W
  have hx : x.left ≫ G.hom = Spec.map (CommRingCat.ofHom φ) := Over.w x
  have hF : ∀ e, (fstG I e G).left ≫ G.hom = (thickObj V I e G).hom ≫ thick V I e := fun e => pullback.condition
  have mF : ∀ e, Mono (fstG I e G).left := fun e => pullback.fst_of_mono (f := G.hom) (g := thick V I e)
  have base : ∀ (e : ℕ) {Z : Scheme.{0}} (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V I e G).left),
      xe ≫ (fstG I e G).left = r ≫ x.left →
      r ≫ Spec.map (CommRingCat.ofHom φ) = (xe ≫ (thickObj V I e G).hom) ≫ thick V I e := fun e Z r xe h => by
    rw [Category.assoc, ← hF, ← hx, ← Category.assoc, ← h]
    exact Category.assoc _ _ _
  have ker := fun (e : ℕ) {Z : Scheme.{0}} (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V I e G).left)
    (h : xe ≫ (fstG I e G).left = r ≫ x.left) =>
    (t.l e).Q.image_eq_one_iff (T := Over.mk (Spec.map (CommRingCat.ofHom φ))) (a.b_pb e).1 r xe (base e r xe h)
  constructor
  · intro H
    let J := I.map φ
    have hle : ∀ e : ℕ, I ^ (e + 1) ≤ (J ^ (e + 1)).comap φ := fun e => by
      rw [← Ideal.map_pow]; exact Ideal.le_comap_map
    have hp : ∀ e, (thick W J e ≫ x.left) ≫ G.hom =
        Spec.map (CommRingCat.ofHom (Ideal.quotientMap _ φ (hle e))) ≫ thick V I e := fun e => by
      rw [Category.assoc, hx, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        ← CommRingCat.ofHom_comp, Ideal.quotientMap_comp_mk]
    obtain ⟨y, hy⟩ : ∃ y : ∀ e, Spec (CommRingCat.of (W ⧸ J ^ (e + 1))) ⟶ (thickObj V I e G).left,
        ∀ e, y e ≫ (fstG I e G).left = thick W J e ≫ x.left :=
      ⟨fun e => pullback.lift _ _ (hp e), fun e => pullback.lift_fst _ _ _⟩
    choose τ hτ using fun e => (ker e _ _ (hy e)).1 (H e _ _ _ (hy e))
    obtain ⟨c, hc⟩ := exists_hom_of_thick J τ fun e χ => by
      obtain ⟨σ, -, h₁, h₂⟩ := t.tor e
      have := (t.l (e + 1)).Q.mono_i_left
      have := mF (e + 1)
      have h₃ : thickMap V I e G ≫ (fstG I (e + 1) G).left = (fstG I e G).left :=
        (pullback.lift_fst _ _ _).trans (Category.comp_id _)
      have h₄ : thickTrans W J e ≫ y (e + 1) = y e ≫ thickMap V I e G := by
        refine (cancel_mono (fstG I (e + 1) G).left).1 ?_
        refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (hy (e + 1))).trans ?_)
        refine Eq.trans ?_ ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) h₃)).symm
        rw [← Category.assoc, thickTrans_comp]
        exact (hy e).symm
      have h₅ : thickTrans W J e ≫ τ (e + 1) = τ e ≫ σ := by
        rw [← cancel_mono (t.l (e + 1)).Q.i.left, Category.assoc, hτ, h₄, Category.assoc, h₂, ← Category.assoc, hτ]
      rw [h₅, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, h₁]
    refine ⟨c, fun e Z r τ' h₁ h₂ => ?_⟩
    obtain ⟨r', rfl⟩ := exists_factor_thick φ I e r _ ((Category.assoc _ _ _).trans h₁)
    have h₃ : τ' = r' ≫ τ e := by
      refine splitTorus_left_hom_ext _ _ ?_ fun χ => ?_
      · rw [← cancel_mono (thick V I e), Category.assoc]
        refine h₁.trans ?_
        rw [Category.assoc, base e _ _ (hy e), ← hτ e, Category.assoc (τ e), Over.w]
        simp only [Category.assoc]
      · rw [h₂, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, hc, scal, scal,
          Scheme.Hom.comp_appTop]
        rfl
    have h₄ : τ e ≫ (t.l e).Q.i.left ≫ (fstG I e G).left = thick W J e ≫ x.left :=
      (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (fstG I e G).left) (hτ e)).trans (hy e))
    rw [h₃]
    exact (Category.assoc _ _ _).trans ((congrArg (r' ≫ ·) h₄).trans (Category.assoc _ _ _).symm)
  · rintro ⟨c, hc⟩ e Z r xe h
    obtain ⟨τ, h₁, h₂⟩ := exists_torus_point c r (xe ≫ (thickObj V I e G).hom)
    have := mF e
    refine (ker e r xe h).2 ⟨τ, (cancel_mono (fstG I e G).left).1 ?_⟩
    refine (Category.assoc _ _ _).trans ((hc e Z r τ ?_ h₂).trans h.symm)
    rw [← Category.assoc, h₁]
    exact (base e r xe h).symm

end GlobalTheory.UU
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AbelianPartImageEqOneIffTorusPointStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.abelianPart_image_eq_one_iff_torus_point : AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (a : t.Alg) (W : Type) [CommRing W] [IsLocalRing W] [Algebra V W], IsAdicComplete ((IsLocalRing.maximalIdeal V).map (algebraMap V W)) W → IsLocalHom (algebraMap V W) → ∀ x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ (x).left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ ((1 : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ a.B)).left) ↔ ∃ c : Multiplicative s.X →* Wˣ, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (τ : Z ⟶ (splitTorus _ s.X).left), τ ≫ (splitTorus (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1)))) s.X).hom ≫ thick V _ e = r ≫ (Spec.map (CommRingCat.ofHom (algebraMap V W))) → (∀ χ, τ.appTop.hom (charUnit _ s.X χ).val = scal r (c (Multiplicative.ofAdd χ)).val) → τ ≫ (t.l e).Q.i.left ≫ (fstG _ e G).left = r ≫ (x).left) := by
  first | exact @GlobalTheory.UU.image_eq_one_iff_torus_point | exact GlobalTheory.UU.image_eq_one_iff_torus_point | (intros; apply GlobalTheory.UU.image_eq_one_iff_torus_point <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFormalTorusPointsSemiAbelianModel
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFormalTorusPointsSemiAbelianModel
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UU.FormalTorusPts

theorem scal_comp {W : Type} [CommRing W] {Z Z' : Scheme.{0}} (h : Z' ⟶ Z)
    (r : Z ⟶ Spec (CommRingCat.of W)) (w : W) : scal (h ≫ r) w = h.appTop.hom (scal r w) := by
  rw [scal, scal, Scheme.Hom.comp_appTop]; rfl

theorem scal_specMap {W W' : Type} [CommRing W] [CommRing W'] {Z : Scheme.{0}} (φ : W →+* W')
    (r : Z ⟶ Spec (CommRingCat.of W')) (w : W) :
    scal (r ≫ Spec.map (CommRingCat.ofHom φ)) w = scal r (φ w) :=
  congr($(SplitTorusPoints.ΓSpecIso_inv_comp_specMap r (CommRingCat.ofHom φ)).hom w)

theorem exists_lift_quot {W : Type} [CommRing W] (J : Ideal W) {Z : Scheme.{0}}
    (r : Z ⟶ Spec (CommRingCat.of W)) (h : ∀ w ∈ J, scal r w = 0) :
    ∃ r' : Z ⟶ Spec (CommRingCat.of (W ⧸ J)),
      r' ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) = r := by
  let φ : CommRingCat.of W ⟶ Γ(Z, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of W)).inv ≫ r.appTop
  refine ⟨Z.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift J φ.hom h)), ?_⟩
  rw [Category.assoc, ← Spec.map_comp]
  change Z.toSpecΓ ≫ Spec.map φ = r
  apply ext_of_isAffine
  rw [← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of W)).inv,
    SplitTorusPoints.ΓSpecIso_inv_comp_specMap, Scheme.toSpecΓ_appTop, Iso.inv_hom_id,
    Category.comp_id]

variable {R : Type} [CommRing R] (I : Ideal R) (W : Type) [CommRing W] [Algebra R W]

theorem pow_le_comap (n : ℕ) : I ^ n ≤ ((I.map (algebraMap R W)) ^ n).comap (algebraMap R W) := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]

def lev (e : ℕ) : Spec (CommRingCat.of (W ⧸ (I.map (algebraMap R W)) ^ (e + 1))) ⟶
    Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) :=
  Spec.map (CommRingCat.ofHom (Ideal.quotientMap _ (algebraMap R W) (pow_le_comap I W (e + 1))))

theorem lev_thick (e : ℕ) : lev I W e ≫ thick R I e =
    adicLevelι (I.map (algebraMap R W)) (e + 1) ≫ Spec.map (CommRingCat.ofHom (algebraMap R W)) := by
  rw [lev, ← Spec.map_comp, ← Spec.map_comp]; rfl

instance mono_thick (e : ℕ) : Mono (thick R I e) := by
  have := isClosedImmersion_red (I ^ (e + 1))
  infer_instance

variable {X : Type} [AddCommGroup X] {W}

def pt (e : ℕ) (a : Multiplicative X →* Wˣ) :
    Over.mk (lev I W e) ⟶ splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) X :=
  (splitTorusPointsEquiv _ X (Over.mk (lev I W e))).symm
    ((Units.map ((Scheme.ΓSpecIso (CommRingCat.of W)).inv ≫
      (adicLevelι (I.map (algebraMap R W)) (e + 1)).appTop).hom.toMonoidHom).comp a)

theorem pt_mul (e : ℕ) (a b : Multiplicative X →* Wˣ) : pt I e (a * b) = pt I e a * pt I e b := by
  rw [pt, pt, pt, ← map_mul]
  congr 1
  ext χ
  simp

theorem pt_char (e : ℕ) (a : Multiplicative X →* Wˣ) (χ : X) :
    (pt I e a).left.appTop.hom (charUnit _ X χ).val =
      scal (adicLevelι (I.map (algebraMap R W)) (e + 1)) (a (Multiplicative.ofAdd χ)).val := by
  rw [← splitTorusPointsEquiv_val, pt, MulEquiv.apply_symm_apply]
  rfl

theorem pt_hom (e : ℕ) (a : Multiplicative X →* Wˣ) :
    (pt I e a).left ≫ (splitTorus _ X).hom = lev I W e := Over.w (pt I e a)

theorem exists_factor (e : ℕ) (a : Multiplicative X →* Wˣ) {Z : Scheme.{0}}
    (r : Z ⟶ Spec (CommRingCat.of W)) (τ : Z ⟶ (splitTorus _ X).left)
    (h : τ ≫ (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) X).hom ≫ thick R I e =
      r ≫ Spec.map (CommRingCat.ofHom (algebraMap R W)))
    (hχ : ∀ χ, τ.appTop.hom (charUnit _ X χ).val = scal r (a (Multiplicative.ofAdd χ)).val) :
    ∃ r', r' ≫ adicLevelι (I.map (algebraMap R W)) (e + 1) = r ∧ r' ≫ (pt I e a).left = τ := by
  have hk : ∀ w ∈ (I.map (algebraMap R W)) ^ (e + 1), scal r w = 0 := by
    have : (I.map (algebraMap R W)) ^ (e + 1) ≤ RingHom.ker
        ((Scheme.ΓSpecIso (CommRingCat.of W)).inv ≫ r.appTop).hom := by
      rw [← Ideal.map_pow, Ideal.map_le_iff_le_comap]
      intro v hv
      change scal r (algebraMap R W v) = 0
      rw [← scal_specMap, ← h, ← Category.assoc, scal_specMap, Ideal.Quotient.eq_zero_iff_mem.2 hv]
      simp [scal]
    exact fun w hw => this hw
  obtain ⟨r', hr⟩ := exists_lift_quot _ r hk
  refine ⟨r', hr, splitTorus_left_hom_ext _ _ ?_ fun χ => ?_⟩
  · rw [← cancel_mono (thick R I e), Category.assoc, Category.assoc, Category.assoc, h,
      ← Category.assoc (pt I e a).left, pt_hom, lev_thick, ← hr]
    exact (Category.assoc _ _ _).symm
  · rw [hχ, ← hr, scal_comp, ← pt_char, Scheme.Hom.comp_appTop]
    rfl

variable {G : Over (Spec (CommRingCat.of R))}
  (i : ∀ e, splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) X ⟶ thickObj R I e G)

def gpt (a : Multiplicative X →* Wˣ) (e : ℕ) :
    Spec (CommRingCat.of (W ⧸ (I.map (algebraMap R W)) ^ (e + 1))) ⟶ G.left :=
  (pt I e a).left ≫ (i e).left ≫ pullback.fst G.hom (thick R I e)

theorem gpt_hom (a : Multiplicative X →* Wˣ) (e : ℕ) : gpt I i a e ≫ G.hom =
    adicLevelι (I.map (algebraMap R W)) (e + 1) ≫ Spec.map (CommRingCat.ofHom (algebraMap R W)) := by
  rw [← lev_thick, ← pt_hom I e a, ← Over.w (i e), gpt]
  simp only [Category.assoc]
  congr 2
  exact pullback.condition

theorem isAdicFamily_aux
    (hi : ∀ e, TorusCompat (thickTrans R I e) (thickMap R I e G) (i e) (i (e + 1)))
    (a : Multiplicative X →* Wˣ) : IsAdicFamily (I.map (algebraMap R W)) (gpt I i a) := by
  intro e
  obtain ⟨τ, h1, h2, h3⟩ := hi e
  have h4 : adicLevelMap (I.map (algebraMap R W)) (Nat.le_succ (e + 1)) ≫ (pt I (e + 1) a).left =
      (pt I e a).left ≫ τ := by
    refine splitTorus_left_hom_ext _ _ ?_ fun χ => ?_
    · rw [← cancel_mono (thick R I (e + 1))]
      simp only [Category.assoc]
      rw [← Category.assoc (pt I (e + 1) a).left, pt_hom, lev_thick, adicLevelMap_ι_assoc,
        ← Category.assoc τ, h1, Category.assoc, thickTrans_comp, ← Category.assoc, pt_hom, lev_thick]
    · rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, CommRingCat.hom_comp,
        RingHom.comp_apply, RingHom.comp_apply, h2, pt_char, pt_char, ← scal_comp, adicLevelMap_ι]
  have h5 : thickMap R I e G ≫ pullback.fst G.hom (thick R I (e + 1)) =
      pullback.fst G.hom (thick R I e) := (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  rw [gpt, gpt, ← Category.assoc, h4, Category.assoc, ← Category.assoc τ, h3, Category.assoc, h5]

theorem exists_hom [GrpObj G] [IsLocalRing W] [IsAdicComplete (I.map (algebraMap R W)) W]
    (hi : ∀ e, TorusCompat (thickTrans R I e) (thickMap R I e G) (i e) (i (e + 1)))
    (hm : ∀ e, IsMonHom (i e)) (hmono : ∀ e, Mono (i e)) :
    ∃ ι' : (Multiplicative X →* Wˣ) →* (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R W))) ⟶ G),
      Function.Injective ι' ∧ ∀ (x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R W))) ⟶ G)
        (a : Multiplicative X →* Wˣ), x = ι' a ↔
        ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (τ : Z ⟶ (splitTorus _ X).left),
          τ ≫ (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) X).hom ≫ thick R I e =
            r ≫ Spec.map (CommRingCat.ofHom (algebraMap R W)) →
          (∀ χ, τ.appTop.hom (charUnit _ X χ).val = scal r (a (Multiplicative.ofAdd χ)).val) →
          τ ≫ (i e).left ≫ pullback.fst G.hom (thick R I e) = r ≫ x.left := by
  have ex := fun a : Multiplicative X →* Wˣ =>
    (existsUnique_over_of_isAdicFamily _ G.hom (isAdicFamily_aux I i hi a) (gpt_hom I i a)).exists
  choose g hg hg' using ex
  let T : Over (Spec (CommRingCat.of R)) := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R W)))
  let f : (Multiplicative X →* Wˣ) → (T ⟶ G) := fun a => Over.homMk (g a) (hg a)
  have hf : ∀ a e, adicLevelι (I.map (algebraMap R W)) (e + 1) ≫ (f a).left = gpt I i a e := hg'
  have hext : ∀ (x : T ⟶ G) a,
      (∀ e, adicLevelι (I.map (algebraMap R W)) (e + 1) ≫ x.left = gpt I i a e) → x = f a :=
    fun x a h => Over.OverMorphism.ext
      (hom_ext_of_isHausdorff (I.map (algebraMap R W)) fun e => (h e).trans (hf a e).symm)
  have hmul : ∀ a b, f (a * b) = f a * f b := by
    intro a b
    refine (hext _ _ fun e => ?_).symm
    have := hm e
    let k : Over.mk ((Over.mk (lev I W e)).hom ≫ thick R I e) ⟶ T :=
      Over.homMk (adicLevelι (I.map (algebraMap R W)) (e + 1)) (lev_thick I W e).symm
    have hk : ∀ c, (k ≫ f c).left = (pt I e c ≫ i e).left ≫ pullback.fst G.hom (thick R I e) :=
      fun c => (hf c e).trans (Category.assoc _ _ _).symm
    have h := SplitTorus.mul_left_comp_fst G (thick R I e) (pt I e a ≫ i e) (pt I e b ≫ i e)
      (k ≫ f a) (k ≫ f b) (hk a) (hk b)
    rw [← MonObj.comp_mul, ← MonObj.mul_comp, ← pt_mul] at h
    exact h.trans (Category.assoc _ _ _)
  refine ⟨MonoidHom.mk' f hmul, fun a b hab => ?_, fun x a => ⟨?_, fun h => hext x a fun e => ?_⟩⟩
  · refine MonoidHom.ext fun χ => Units.ext ?_
    refine IsHausdorff.StrictMono.funext' (I.map (algebraMap R W)) (a := fun n => n + 1)
      (strictMono_id.add_const 1) (f := fun _ : Unit => (a χ).val) (g := fun _ => (b χ).val)
      (fun e _ => ?_) |> (congrFun · ())
    have := hmono e
    have : Mono (i e).left := inferInstanceAs (Mono ((Over.forget _).map (i e)))
    have h1 : gpt I i a e = gpt I i b e := by
      rw [← hf, ← hf]; exact congrArg (fun y : T ⟶ G => _ ≫ y.left) hab
    rw [gpt, gpt, cancel_mono] at h1
    have h2 := pt_char I e a χ.toAdd
    rw [h1, pt_char, ← Category.id_comp (adicLevelι _ _), scal_specMap, scal_specMap] at h2
    simp only [scal, Scheme.Hom.id_appTop, CommRingCat.hom_id, RingHom.id_apply] at h2
    exact ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso _).inv).1 h2).symm
  · rintro rfl e Z r τ h hχ
    obtain ⟨r', rfl, rfl⟩ := exists_factor I e a r τ h hχ
    rw [Category.assoc, Category.assoc]
    exact congrArg (r' ≫ ·) (hf a e).symm
  · refine (h e _ _ (pt I e a).left ?_ (pt_char I e a)).symm
    rw [← Category.assoc, pt_hom, lev_thick]

end GlobalTheory.UU.FormalTorusPts

namespace GlobalTheory.UU

theorem exists_formalTorus_points :
    AllSet fun {V} _ _ _ {_} {G} _ _ s => ∀ (t : Tower s) (W : Type) [CommRing W] [IsLocalRing W] [Algebra V W], IsAdicComplete ((IsLocalRing.maximalIdeal V).map (algebraMap V W)) W → IsLocalHom (algebraMap V W) → ∃ ι' : (Multiplicative s.X →* Wˣ) →* (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G), Function.Injective ι' ∧ ∀ (x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G) (a : Multiplicative s.X →* Wˣ), x = ι' a ↔ ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (τ : Z ⟶ (splitTorus _ s.X).left), τ ≫ (splitTorus (Spec (CommRingCat.of (V ⧸ IsLocalRing.maximalIdeal V ^ (e + 1)))) s.X).hom ≫ thick V _ e = r ≫ Spec.map (CommRingCat.ofHom (algebraMap V W)) → (∀ χ, τ.appTop.hom (charUnit _ s.X χ).val = scal r (a (Multiplicative.ofAdd χ)).val) → τ ≫ (t.l e).Q.i.left ≫ (fstG _ e G).left = r ≫ x.left := by
  intro V _ _ _ A G _ _ s t W _ _ _ hW _
  refine FormalTorusPts.exists_hom (IsLocalRing.maximalIdeal V) (fun e => (t.l e).Q.i) t.tor
    (fun e => (t.l e).Q.i_hom) fun e => ?_
  exact ⟨fun a b h => (t.l e).Q.isKernel.hom_ext h (toUnit_unique _ _)⟩

end GlobalTheory.UU
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFormalTorusPointsSemiAbelianModelStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.exists_formalTorus_points_semiAbelian_model : AllSet fun {V} _ _ _ {_} {G} _ _ s => ∀ (t : Tower s) (W : Type) [CommRing W] [IsLocalRing W] [Algebra V W], IsAdicComplete ((IsLocalRing.maximalIdeal V).map (algebraMap V W)) W → IsLocalHom (algebraMap V W) → ∃ ι' : (Multiplicative s.X →* Wˣ) →* (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G), Function.Injective ι' ∧ ∀ (x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G) (a : Multiplicative s.X →* Wˣ), x = ι' a ↔ ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (τ : Z ⟶ (splitTorus _ s.X).left), τ ≫ (splitTorus (Spec (CommRingCat.of (V ⧸ IsLocalRing.maximalIdeal V ^ (e + 1)))) s.X).hom ≫ thick V _ e = r ≫ Spec.map (CommRingCat.ofHom (algebraMap V W)) → (∀ χ, τ.appTop.hom (charUnit _ s.X χ).val = scal r (a (Multiplicative.ofAdd χ)).val) → τ ≫ (t.l e).Q.i.left ≫ (fstG _ e G).left = r ≫ x.left := by
  first | exact @GlobalTheory.UU.exists_formalTorus_points | exact GlobalTheory.UU.exists_formalTorus_points | (intros; apply GlobalTheory.UU.exists_formalTorus_points <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGtCoordOfTorusQuotient
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.QuotCoord

open WeightGen

theorem exists_flat {X B Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (B ⟶ X)} {ε : K → ℤ}
    (f : Y ⟶ B) (u : LB.Gen ((LB.LinComb L φ ε).pull f)) (hu : u.IsGen) :
    ∃ t : LB.Gen (LB.LinComb L (fun k => f ≫ φ k) ε), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : K → L.ι), r z ∈ LB.wchart L (fun k => f ≫ φ k) j →
        r z ∈ ((LB.LinComb L φ ε).pull f).U (fun _ => j) ∧
        gm r z (LB.wchart L (fun k => f ≫ φ k) j) (t.s j) =
          gm r z (((LB.LinComb L φ ε).pull f).U (fun _ => j)) (u.s fun _ => j) := by
  have le : ∀ j : K → L.ι, LB.wchart L (fun k => f ≫ φ k) j ≤ ((LB.LinComb L φ ε).pull f).U (fun _ => j) :=
    fun _ _ hy => mem_pull.2 (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k)
  refine ⟨⟨fun j => res (le j) (u.s fun _ => j)⟩, fun j j' => unit_ext fun y hy => ?_,
    fun Z r z j hj => ⟨le j hj, gm_res r z (le j) hj _⟩⟩
  refine ((gm_res _ y _ hy _).trans (gm_res (𝟙 Y) y (le j) hy.1 _)).trans (Eq.trans ?_ ((map_mul _ _ _).trans
      (congrArg₂ (· * ·) (gm_linComb L _ _ (𝟙 Y) y j j' hy.1 hy.2)
        ((gm_res _ y _ hy _).trans (gm_res (𝟙 Y) y (le j') hy.2 _)))).symm)
  refine (gm_gen hu (𝟙 Y) y (le j hy.1) (le j' hy.2)).trans (congrArg (· * _) ?_)
  refine (gm_pull_g _ f (𝟙 Y) y _ _ (le j hy.1) (le j' hy.2)).trans
    ((gm_linComb L φ ε (𝟙 Y ≫ f) y j j' (mem_pull.1 (le j hy.1)) (mem_pull.1 (le j' hy.2))).trans ?_)
  simp only [Category.assoc]

section
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X]

noncomputable abbrev tact (i : splitTorus S X ⟶ G) : splitTorus S X ⊗ G ⟶ G :=
  lift (fst (splitTorus S X) G ≫ i) (snd (splitTorus S X) G) ≫ μ[G]

theorem comp_tact (i : splitTorus S X ⟶ G) {Z : Over S} (ρ : Z ⟶ splitTorus S X ⊗ G) :
    ρ ≫ tact i = ((ρ ≫ fst _ _) ≫ i) * (ρ ≫ snd _ _) := by
  rw [Hom.mul_def, comp_lift_assoc, Category.assoc]

theorem exists_wt_gen (i : splitTorus S X ⟶ G) {Y B : Scheme.{0}} {L : LB Y} {K : Type} [Fintype K]
    {φ : K → (B ⟶ Y)} {ε : K → ℤ} (f : G.left ⟶ B)
    (hf : (tact i).left ≫ f = (snd (splitTorus S X) G).left ≫ f) (χ : X)
    (u : LB.Gen ((LB.LinComb L φ ε).pull f)) (hu : u.IsGen) (hw : ∀ j, IsWt i _ (u.s j).val χ) :
    ∃ t : LB.Gen (LB.LinComb L (fun k => f ≫ φ k) ε), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (splitTorus S X ⊗ G).left) (z : Z) (J), Good L z J →
        val t (r ≫ (tact i).left) z J = wt X G χ Z r z * val t (r ≫ (snd (splitTorus S X) G).left) z J := by
  obtain ⟨t, ht, hv⟩ := exists_flat f u hu
  refine ⟨t, ht, fun Z r z J hJ => ?_⟩
  have m := hJ.mem (fun k => f ≫ φ k) (r ≫ (snd (splitTorus S X) G).left)
  have m' := hJ.mem (fun k => f ≫ φ k) (r ≫ (tact i).left)
  have e : ∀ k, J ((r ≫ (tact i).left) ≫ f ≫ φ k) = J ((r ≫ (snd (splitTorus S X) G).left) ≫ f ≫ φ k) :=
    fun k => by rw [Category.assoc, Category.assoc, reassoc_of% hf]
  rw [funext e] at m'
  rw [val_of _ (r ≫ (tact i).left) z J _ e]
  obtain ⟨n, v⟩ := hv Z _ z _ m
  obtain ⟨n', v'⟩ := hv Z _ z _ m'
  refine v'.trans (Eq.trans ?_ (congrArg _ v).symm)
  let Z' : Over S := Over.mk (r ≫ (splitTorus S X ⊗ G).hom)
  let ρ : Z' ⟶ splitTorus S X ⊗ G := Over.homMk r rfl
  have k := WtBundle.gm_of_isWt (hw fun _ => fun k => J ((r ≫ (snd (splitTorus S X) G).left) ≫ f ≫ φ k))
    (ρ ≫ fst _ _) (ρ ≫ snd _ _) z (by rw [← comp_tact]; exact n') n
  rw [← comp_tact, ← gm_charUnit] at k
  exact k

variable (Q : TQ G X)

theorem tact_q : tact Q.i ≫ Q.q = snd _ _ ≫ Q.q := WtBundle.act_comp Q (fst _ _) (snd _ _)

theorem exists_const (hG : GlobalFnsSt) (f : Γ(G.left, ⊤))
    (hf : (tact Q.i).left.appTop.hom f = (snd (splitTorus S X) G).left.appTop.hom f) :
    ∃ c, G.hom.appTop.hom c = f := by
  have := Q.q_affine
  obtain ⟨b, hb⟩ := (invariant_functions_descend S G Q.B _ Q.q Q.i Q.q_hom Q.i_hom Q.q_flat
    Q.q_surj inferInstance Q.isKernel ⊤).2.2 f (fun Z t g h₁ h₂ => by
      have e₁ : (t ≫ Q.i) * g = lift t g ≫ tact Q.i := by
        rw [comp_tact, lift_fst, lift_snd]
      have key : ((t ≫ Q.i) * g).left.appTop.hom f = g.left.appTop.hom f := by
        rw [e₁, Over.comp_left, FunDescent.comp_appTop_apply, hf, ← FunDescent.comp_appTop_apply,
          ← Over.comp_left, lift_snd]
      rw [Scheme.Hom.appTop, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE,
        Scheme.Hom.app_eq_appLE] at key
      exact key)
  obtain ⟨c, hc⟩ := (hG S Q.B Q.isAb).2 b
  refine ⟨c, ?_⟩
  rw [← Over.w Q.q, FunDescent.comp_appTop_apply, hc]
  exact hb

end

theorem exists_iso_pullback {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {F : G'.left ⟶ G.left} (h : IsGrpPullback G' G f F) :
    ∃ e : G' ≅ (Over.pullback f).obj G, IsMonHom e.hom ∧ e.hom.left ≫ pullback.fst G.hom f = F := by
  let e : G' ≅ (Over.pullback f).obj G := Over.isoMk h.1.isoPullback h.1.isoPullback_hom_snd
  have he : e.hom.left ≫ pullback.fst G.hom f = F := h.1.isoPullback_hom_fst
  refine ⟨e, isMonHom_of_mul _ fun T x y => ?_, he⟩
  have h₁ := h.2 T x y (pushPt h.1.w x) (pushPt h.1.w y) rfl rfl
  have h₂ := (isGrpPullback_pullback G f).2 T (x ≫ e.hom) (y ≫ e.hom) (pushPt h.1.w x) (pushPt h.1.w y)
    (by rw [Over.comp_left, Category.assoc, he]; rfl) (by rw [Over.comp_left, Category.assoc, he]; rfl)
  refine Over.OverMorphism.ext ((isGrpPullback_pullback G f).1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
  rw [← h₂, h₁, Over.comp_left, Category.assoc, he]

section
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

theorem prod_transl {T : Over (Spec (CommRingCat.of R))} (p : T ⟶ D.P.A) (χ : D.X) {U : Type} [CommGroup U]
    (h : (T.left ⟶ D.P.A.left) → U) :
    ∏ k : Fin 2, h (p.left ≫ ![((toUnit D.P.A ≫ D.c χ) * 𝟙 D.P.A).left, 𝟙 D.P.A.left] k) ^
      (![-1, 1] : Fin 2 → ℤ) k = (h ((toUnit T ≫ D.c χ) * p).left)⁻¹ * h p.left := by
  have e : p ≫ ((toUnit D.P.A ≫ D.c χ) * 𝟙 D.P.A) = (toUnit T ≫ D.c χ) * p := by
    rw [MonObj.comp_mul, comp_toUnit_assoc, Category.comp_id]
  rw [Fin.prod_univ_two, ← e]
  show h (p ≫ ((toUnit D.P.A ≫ D.c χ) * 𝟙 D.P.A)).left ^ (-1 : ℤ) * h (p.left ≫ 𝟙 _) ^ (1 : ℤ) = _
  rw [Category.comp_id, zpow_one, zpow_neg, zpow_one]

theorem exists_four {T : Over (Spec (CommRingCat.of R))} (q : T ⟶ D.P.A) (σ : T ⟶ T) (hσ : σ ≫ q = 1) (χ : D.X)
    (f : T.left ⟶ D.P.A.left) (hf : q.left = f)
    (t₀ : LB.Gen (LB.LinComb D.P.L (K := Fin 2)
      (fun k => f ≫ ![((toUnit D.P.A ≫ D.c χ) * 𝟙 D.P.A).left, 𝟙 D.P.A.left] k) ![-1, 1])) (g₀ : t₀.IsGen) :
    ∃ t : LB.Gen (LB.LinComb D.P.L (D.Oφ q χ) Oinvε), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) (J), Good D.P.L z J →
        val t r z J = val t₀ r z J * (val t₀ (r ≫ σ.left) z J)⁻¹ := by
  subst hf
  obtain ⟨t, ht, hv⟩ := exists_gen D.P.isLB (φ' := D.Oφ q χ) (ε' := Oinvε) (fun U _ h => by
      have a := prod_transl D (σ ≫ q) χ h
      refine Eq.trans (DVR.prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := U) _
        (prod_transl D q χ h) (DVR.prod_neg _ _
          ((Finset.prod_congr rfl fun k _ =>
            congrArg (fun g => h g ^ (![-1, 1] : Fin 2 → ℤ) k) (Category.assoc _ _ _).symm).trans a))) ?_
      rw [prod_Oφ, hσ, _root_.mul_one, mul_comm q]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
    (LB.mulGen D.P.L _ _ _ _ t₀ (LB.invGen D.P.L _ _ (LB.pullGen D.P.L _ _ t₀ σ.left)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ g₀ (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ g₀ _)))
  exact ⟨t, ht, fun Z r z J hJ => by rw [hv Z r z J hJ, val_mul hJ, val_inv, val_pull hJ]⟩

end

end GlobalTheory.QuotCoord

namespace GlobalTheory

open WeightGen QuotCoord

theorem exists_gtCoord_of_torusQuotient : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R) (D : DegPre R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (Q : TQ (thickObj R I e G) D.X) (b : Q.B.left ⟶ D.P.A.left), IsGrpPullback Q.B D.P.A (thick R I e) b → (∀ χ, ∃ u : LB.Gen ((LB.LinComb D.P.L (K := Fin 2) ![((toUnit D.P.A ≫ D.c χ) * 𝟙 D.P.A).left, 𝟙 D.P.A.left] ![-1, 1]).pull (Q.q.left ≫ b)), u.IsGen ∧ ∀ j, IsWt Q.i _ (u.s j).val χ) → ∃ g : GtCoord I D e G, g.i = Q.i ∧ g.pG.left = Q.q.left ≫ b := by
  intro hG R _ _ _ I D e G _ _ Q b hb hu
  obtain ⟨β, hβ, hβb⟩ : ∃ β : Q.B ≅ thickObj R I e D.P.A, IsMonHom β.hom ∧
    β.hom.left ≫ pullback.fst D.P.A.hom (thick R I e) = b := exists_iso_pullback hb
  have hL := D.P.isLB
  have := Q.q_hom
  have := Q.i_hom
  have := Q.q_flat
  have := Q.q_surj
  have := Q.q_affine
  have : IsIso β.hom.left := inferInstanceAs (IsIso ((Over.forget _).map β.hom))
  let F := Over.map (thick R I e)
  have hp : (F.map (Q.q ≫ β.hom) ≫ D.prBe I e).left = Q.q.left ≫ b := by
    rw [← hβb, ← Category.assoc]
    rfl
  have unit_q : F.map η[thickObj R I e G] ≫ F.map (Q.q ≫ β.hom) ≫ D.prBe I e = 1 := by
    rw [← F.map_comp_assoc, IsMonHom.one_hom]
    exact Over.OverMorphism.ext (unit_fst (thick R I e) D.P.A)
  have hπ : F.map (tact Q.i) ≫ F.map (toUnit _) = F.map (snd _ _) ≫ F.map (toUnit _) := by
    rw [← F.map_comp, ← F.map_comp, comp_toUnit, comp_toUnit]
  obtain ⟨t, g, m, u, w⟩ := exists_normalised D (F.map (Q.q ≫ β.hom) ≫ D.prBe I e)
    (F.map (toUnit _)) (F.map η[thickObj R I e G])
    (by rw [← F.map_comp, comp_toUnit, toUnit_unit, F.map_id]) unit_q
    (F.map (tact Q.i)) (F.map (snd _ _))
    (by rw [← F.map_comp_assoc, ← F.map_comp_assoc, ← Category.assoc (tact Q.i), tact_q Q,
      Category.assoc])
    hπ (QuotCoord.exists_const Q hG) (fun χ => wt D.X (thickObj R I e G) χ)
    (fun χ χ' Z r z => wt_add _ _ _ _ Z r z)
    (fun χ => by
      obtain ⟨u, gu, wu⟩ := hu χ
      obtain ⟨t₀, g₀, w₀⟩ := exists_wt_gen Q.i (Q.q.left ≫ b) (by
        rw [← Category.assoc, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, tact_q]) χ u gu wu
      obtain ⟨t, g, v⟩ := exists_four D (F.map (Q.q ≫ β.hom) ≫ D.prBe I e)
        (F.map (toUnit _) ≫ F.map η[thickObj R I e G])
        (by rw [Category.assoc, unit_q, MonObj.comp_one]) χ _ hp t₀ g₀
      refine ⟨t, g, fun Z r z J hJ => ?_⟩
      have k : (F.map (tact Q.i)).left ≫ (F.map (toUnit _) ≫ F.map η[thickObj R I e G]).left =
          (F.map (snd _ _)).left ≫ (F.map (toUnit _) ≫ F.map η[thickObj R I e G]).left :=
        congrArg (fun g => g.left) (show F.map (tact Q.i) ≫ F.map (toUnit _) ≫ F.map η[thickObj R I e G] =
          F.map (snd _ _) ≫ F.map (toUnit _) ≫ F.map η[thickObj R I e G] by rw [reassoc_of% hπ])
      rw [v _ _ z J hJ, v _ _ z J hJ, Category.assoc, Category.assoc, k, ← _root_.mul_assoc]
      exact congrArg (· * _) (w₀ Z r z J hJ))
  refine ⟨{ q := Q.q ≫ β.hom
            q_hom := inferInstance
            q_flat := by rw [Over.comp_left]; infer_instance
            q_surj := by rw [Over.comp_left]; infer_instance
            q_affine := by rw [Over.comp_left]; infer_instance
            i := Q.i
            i_hom := inferInstance
            isKernel := Q.isKernel.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) β (by simp)
              (toUnit_unique _ _) (by simp) (by simp)
            t := t
            t_gen := g
            t_mul := m
            t_unit := fun χ => corr_of_val hL fun y J hJ => ?_
            t_weight := fun χ => corr_of_val hL fun y J hJ => ?_ }, rfl, hp⟩
  · refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_one _).symm)
    rw [Category.id_comp]
    exact u χ y J hJ
  · exact (val_pull hJ _ _ _).trans ((w χ _ (𝟙 _) y J hJ).trans ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) (val_charGen _ _ _ _ _ _ _) (val_pull hJ _ _ _))).symm)

end GlobalTheory
end
