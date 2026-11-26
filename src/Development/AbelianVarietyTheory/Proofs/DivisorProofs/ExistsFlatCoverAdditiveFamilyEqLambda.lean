module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SndSectionValueTranslateProdFirstOrderLinear
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedKernelFiniteFlatSurjectiveOverBase

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistedKernelClosedFiniteFlatAffineBase
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistedKernelClosedFiniteFlatAffineBase
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCover

theorem twistedKernel_affine : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A],
    IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → Out.RelAmple A L → ∀ (T : Over (Sp R)) [IsAffine T.left]
    (N : LB (A ⊗ T).left), Fam A N → ∃ (H : Over (Sp R)) (h : H ⟶ A ⊗ T), IsClosedImmersion h.left ∧
    IsFinite (h ≫ snd A T).left ∧ Flat (h ≫ snd A T).left ∧ Surjective (h ≫ snd A T).left ∧
    ∀ (Y : Over (Sp R)) (a : Y ⟶ A) (t : Y ⟶ T), Same A (abelian₂ A L) N a t ↔ ∃ z : Y ⟶ H, z ≫ h = lift a t := by
  intro R _ _ A _ hA L hL hamp T _ N hN
  obtain ⟨T₀, φ, N₀, hT₀, hft, hN₀, hsame⟩ := GlobalTheory.DualApprox.exists_fam_finiteType R A hA T N hN
  obtain ⟨H₀, h₀, hci, hfin, hfl, hsurj, hrep⟩ := GlobalTheory.T.twistedKernel_finite_flat_surjective_over_base R A hA L hL hamp T₀ hft N₀ hN₀
  have sq₂ : IsPullback (A ◁ φ) (snd A T) (snd A T₀) φ := GlobalTheory.SS.TorusSlice.isPullback_whiskerLeft A φ
  have sq₁ : IsPullback (pullback.fst h₀ (A ◁ φ)) (pullback.snd h₀ (A ◁ φ)) h₀ (A ◁ φ) :=
    IsPullback.of_hasPullback _ _
  have sq : IsPullback (pullback.fst h₀ (A ◁ φ)) (pullback.snd h₀ (A ◁ φ) ≫ snd A T) (h₀ ≫ snd A T₀) φ :=
    sq₁.paste_vert sq₂
  have sq₁' := sq₁.map (Over.forget (Sp R))
  have sq' := sq.map (Over.forget (Sp R))
  have hΛ : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  refine ⟨pullback h₀ (A ◁ φ), pullback.snd h₀ (A ◁ φ), ?_, ?_, ?_, ?_, ?_⟩
  · exact MorphismProperty.of_isPullback (P := @IsClosedImmersion) sq₁' hci
  · exact MorphismProperty.of_isPullback (P := @IsFinite) sq' hfin
  · exact MorphismProperty.of_isPullback (P := @Flat) sq' hfl
  · exact MorphismProperty.of_isPullback (P := @Surjective) sq' hsurj
  · intro Y a t

    have key : evc hN.isLB (fst A Y) (snd A Y ≫ t) = evc hN₀.isLB (fst A Y) (snd A Y ≫ t ≫ φ) := by
      have e := congrArg (CechPic.pull (lift (fst A Y) (snd A Y ≫ t)).left)
        ((same_iff hN.isLB hN₀.isLB (𝟙 T) φ).1 hsame)
      simpa only [pull_evc, lift_fst, lift_snd_assoc, lift_snd, Category.comp_id, Category.assoc] using e
    have e₁ : Same A (abelian₂ A L) N a t ↔ Same A (abelian₂ A L) N₀ a (t ≫ φ) := by
      rw [same_iff hΛ hN.isLB, same_iff hΛ hN₀.isLB, key]
    have e₂ : lift a (t ≫ φ) = lift a t ≫ (A ◁ φ) := by
      ext <;> simp
    rw [e₁, hrep, e₂]
    constructor
    · rintro ⟨z₀, hz₀⟩
      exact ⟨pullback.lift z₀ (lift a t) hz₀, pullback.lift_snd _ _ _⟩
    · rintro ⟨z, hz⟩
      exact ⟨z ≫ pullback.fst h₀ (A ◁ φ), by rw [Category.assoc, pullback.condition, ← Category.assoc, hz]⟩

end GlobalTheory.DualCover
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistedKernelClosedFiniteFlatAffineBaseStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_twistedKernel_closed_finiteFlat_affineBase : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → Out.RelAmple A L → ∀ (T : Over (Sp R)) [IsAffine T.left] (N : LB (A ⊗ T).left), Fam A N → ∃ (H : Over (Sp R)) (h : H ⟶ A ⊗ T), IsClosedImmersion h.left ∧ IsFinite (h ≫ snd A T).left ∧ Flat (h ≫ snd A T).left ∧ Surjective (h ≫ snd A T).left ∧ ∀ (Y : Over (Sp R)) (a : Y ⟶ A) (t : Y ⟶ T), Same A (abelian₂ A L) N a t ↔ ∃ z : Y ⟶ H, z ≫ h = lift a t := by
  first | exact @GlobalTheory.DualCover.twistedKernel_affine | exact GlobalTheory.DualCover.twistedKernel_affine | (intros; apply GlobalTheory.DualCover.twistedKernel_affine <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleFamilyAgreementLocusOfAffineOpen
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SameRigidifiedFamilyAbelianSchemeOfLocal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SameRigidifiedFamilyAbelianSchemeOfLocal
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon.SameLocal

theorem injective_app_of_section {X Y : Scheme.{0}} (p : X ⟶ Y) (e : Y ⟶ X) (he : e ≫ p = 𝟙 Y)
    (V : Y.Opens) : Function.Injective (p.app V).hom := by
  have hi : IsIso ((e ≫ p).app V) := by
    rw [Scheme.Hom.congr_app he V]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance (Functor.map_isIso _ _)
  have k : ∀ z, ((e ≫ p).app V).hom z = (e.app (p ⁻¹ᵁ V)).hom ((p.app V).hom z) := fun z => rfl
  intro x x' hx
  apply (ConcreteCategory.bijective_of_isIso ((e ≫ p).app V)).1
  change ((e ≫ p).app V).hom x = ((e ≫ p).app V).hom x'
  rw [k, k, hx]

theorem same_of_local : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (U T : Over (Sp R)) (M : LB (A ⊗ U).left) (N : LB (A ⊗ T).left) (hM : M.IsLB) (hN : N.IsLB), (∀ (Y : Over (Sp R)) (u : Y ⟶ U), evc hM (1 : Y ⟶ A) u = 0) → (∀ (Y : Over (Sp R)) (t : Y ⟶ T), evc hN (1 : Y ⟶ A) t = 0) → ∀ (Y : Over (Sp R)) (u : Y ⟶ U) (t : Y ⟶ T), (∀ y : Y.left, ∃ W : Y.left.Opens, y ∈ W ∧ Same A M N (Over.homMk W.ι rfl ≫ u : Over.mk (W.ι ≫ Y.hom) ⟶ U) (Over.homMk W.ι rfl ≫ t)) → Same A M N u t := by
  intro R _ _ A _ hA U T M N hM hN hMr hNr Y u t hloc
  let p := (snd A Y).left
  let e := (lift (1 : Y ⟶ A) (𝟙 Y)).left
  have he : e ≫ p = 𝟙 Y.left := by
    simp only [p, e, ← Over.comp_left, lift_snd, Over.id_left]
  have hp : ∀ V : Y.left.Opens, Function.Bijective (p.app V).hom := fun V =>
    ⟨injective_app_of_section p e he V,
      GlobalTheory.surjective_app_of_isAbelianScheme GlobalTheory.SemiRigid.globalFns _ (Out.TLinPf.isAb_pullback Y.hom A hA) V⟩
  rw [same_iff hM hN, ← sub_eq_zero]
  obtain ⟨L, hL, hLc⟩ := cls_surj (evc hM (fst A Y) (snd A Y ≫ u) - evc hN (fst A Y) (snd A Y ≫ t))
  have hloc' : ∀ y : Y.left, ∃ V : Y.left.Opens, y ∈ V ∧ ∃ g : LB.Gen (L.pull (p ⁻¹ᵁ V).ι), g.IsGen := by
    intro y
    obtain ⟨W, hyW, hW⟩ := hloc y
    refine ⟨W, hyW, (cls_eq_zero_iff (pull_isLB hL _)).1 ?_⟩
    rw [cls_pull hL, hLc]
    let j : Over.mk (W.ι ≫ Y.hom) ⟶ Y := Over.homMk W.ι rfl
    have h0 : CechPic.pull (A ◁ j).left
        (evc hM (fst A Y) (snd A Y ≫ u) - evc hN (fst A Y) (snd A Y ≫ t)) = 0 := by
      rw [map_sub, pull_evc, pull_evc, whiskerLeft_fst, whiskerLeft_snd_assoc, whiskerLeft_snd_assoc, sub_eq_zero]
      exact (same_iff hM hN _ _).1 hW
    let P : Over (Sp R) := Over.mk ((p ⁻¹ᵁ W).ι ≫ (A ⊗ Y).hom)
    let k : P ⟶ A ⊗ Y := Over.homMk (p ⁻¹ᵁ W).ι rfl
    have hr : Set.range ((p ⁻¹ᵁ W).ι ≫ p) ⊆ Set.range W.ι := by
      rintro _ ⟨z, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact z.2
    let w : P ⟶ Over.mk (W.ι ≫ Y.hom) := Over.homMk (IsOpenImmersion.lift W.ι ((p ⁻¹ᵁ W).ι ≫ p) hr) (by
      simp only [Over.mk_hom, P]
      rw [← Category.assoc, IsOpenImmersion.lift_fac, Category.assoc, Over.w (snd A Y)])
    let φ : P ⟶ A ⊗ Over.mk (W.ι ≫ Y.hom) := lift (k ≫ fst A Y) w
    have hφ : φ ≫ (A ◁ j) = k := by
      refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
      · rw [Category.assoc, whiskerLeft_fst, lift_fst]
      · rw [Category.assoc, whiskerLeft_snd, lift_snd_assoc]
        exact Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)
    have e2 : (p ⁻¹ᵁ W).ι = φ.left ≫ (A ◁ j).left := by rw [← Over.comp_left, hφ]; rfl
    rw [e2, pull_comp, h0, map_zero]
  obtain ⟨N', hN', w, hw⟩ := GlobalTheory.CubeLawCompare.iso_pull_of_locally_trivial p hp hL hloc'
  have h1 : CechPic.pull p (cls N' hN') = cls L hL := by
    rw [← cls_pull hN' p (pull_isLB hN' p)]
    exact (cls_eq_iff _ hL).2 ⟨w, hw⟩
  have h2 : CechPic.pull e (cls L hL) = 0 := by
    rw [hLc, map_sub, pull_evc, pull_evc, lift_fst, lift_snd_assoc, Category.id_comp, hMr, hNr, sub_zero]
  have h3 : cls N' hN' = 0 := by
    rw [← h2, ← h1, ← pull_comp, he, pull_id]
  rw [← hLc, ← h1, h3, map_zero]

end GlobalTheory.DualCon.SameLocal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SameRigidifiedFamilyAbelianSchemeOfLocalStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sameRigidifiedFamily_abelianScheme_of_local : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (U T : Over (Sp R)) (M : LB (A ⊗ U).left) (N : LB (A ⊗ T).left) (hM : M.IsLB) (hN : N.IsLB), (∀ (Y : Over (Sp R)) (u : Y ⟶ U), evc hM (1 : Y ⟶ A) u = 0) → (∀ (Y : Over (Sp R)) (t : Y ⟶ T), evc hN (1 : Y ⟶ A) t = 0) → ∀ (Y : Over (Sp R)) (u : Y ⟶ U) (t : Y ⟶ T), (∀ y : Y.left, ∃ W : Y.left.Opens, y ∈ W ∧ Same A M N (Over.homMk W.ι rfl ≫ u : Over.mk (W.ι ≫ Y.hom) ⟶ U) (Over.homMk W.ι rfl ≫ t)) → Same A M N u t := by
  first | exact @GlobalTheory.DualCon.SameLocal.same_of_local | exact GlobalTheory.DualCon.SameLocal.same_of_local | (intros; apply GlobalTheory.DualCon.SameLocal.same_of_local <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedImmersionRepresentsOfAffineOpens
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlueClosedImmersionsOpenCover
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlueClosedImmersionsOpenCover
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GlueClosed

theorem exists_lift_eq {X : Scheme.{0}} (U V : X.Opens) (x : (pullback U.ι V.ι).carrier) :
    ∃ y : (U ⊓ V).toScheme, pullback.lift (X.homOfLE (inf_le_left : U ⊓ V ≤ U))
      (X.homOfLE (inf_le_right : U ⊓ V ≤ V)) (by simp) y = x := by
  have hx : U.ι (pullback.fst U.ι V.ι x) ∈ U ⊓ V := by
    refine ⟨(pullback.fst U.ι V.ι x).2, ?_⟩
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    exact (pullback.snd U.ι V.ι x).2
  obtain ⟨y, hy⟩ : ∃ y : (U ⊓ V).toScheme, (U ⊓ V).ι y = U.ι (pullback.fst U.ι V.ι x) :=
    ⟨⟨_, hx⟩, rfl⟩
  refine ⟨y, ?_⟩
  apply (pullback.fst U.ι V.ι ≫ U.ι).isOpenEmbedding.injective
  rw [← Scheme.Hom.comp_apply _ (pullback.fst U.ι V.ι ≫ U.ι), pullback.lift_fst_assoc,
    Scheme.homOfLE_ι, hy]
  rfl

section
variable {X : Scheme.{0}} (S : Set X.Opens) (hcov : ∀ x : X, ∃ U ∈ S, x ∈ U)

noncomputable def coverOfSet : X.OpenCover where
  I₀ := S
  X U := U.1.toScheme
  f U := U.1.ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, fun U ↦ inferInstanceAs (IsOpenImmersion U.1.ι)⟩
    obtain ⟨U, hU, hx⟩ := hcov x
    exact ⟨⟨U, hU⟩, ⟨x, hx⟩, rfl⟩

instance : Preorder (coverOfSet S hcov).I₀ := inferInstanceAs (Preorder S)

@[reducible] noncomputable def locallyDirected (hinf : ∀ U ∈ S, ∀ V ∈ S, U ⊓ V ∈ S) :
    (coverOfSet S hcov).LocallyDirected where
  trans {U V} h := X.homOfLE (show U.1 ≤ V.1 from h.le)
  trans_id U := X.homOfLE_rfl _
  trans_comp h k := (X.homOfLE_homOfLE _ _).symm
  w h := X.homOfLE_ι _
  directed {U V} x := by
    obtain ⟨y, hy⟩ := exists_lift_eq U.1 V.1 x
    exact ⟨⟨U.1 ⊓ V.1, hinf _ U.2 _ V.2⟩, homOfLE (inf_le_left : U.1 ⊓ V.1 ≤ U.1),
      homOfLE (inf_le_right : U.1 ⊓ V.1 ≤ V.1), y, hy⟩
  property_trans h := inferInstanceAs (IsOpenImmersion (X.homOfLE _))

end

theorem exists_glue {X : Scheme.{0}} (S : Set X.Opens) (hcov : ∀ x : X, ∃ U ∈ S, x ∈ U)
    (hinf : ∀ U ∈ S, ∀ V ∈ S, U ⊓ V ∈ S) (C : S → Scheme.{0}) (c : ∀ U, C U ⟶ U.1.toScheme)
    [∀ U, Mono (c U)]
    (H : ∀ (U V : S) (h : U.1 ≤ V.1) (Y : Scheme.{0}) (g : Y ⟶ U.1.toScheme),
      (∃ z : Y ⟶ C U, z ≫ c U = g) ↔ ∃ z : Y ⟶ C V, z ≫ c V = g ≫ X.homOfLE h) :
    ∃ (B : Scheme.{0}) (b : B ⟶ X) (e : ∀ U, C U ⟶ B), ∀ U, IsPullback (c U) (e U) U.1.ι b := by
  choose t ht using fun (U V : S) (h : U.1 ≤ V.1) ↦ (H U V h _ (c U)).1 ⟨𝟙 _, Category.id_comp _⟩
  have hid : ∀ U : S, t U U le_rfl = 𝟙 _ := fun U ↦ by
    rw [← cancel_mono (c U), ht, X.homOfLE_rfl]; simp
  have hcomp : ∀ (U V W : S) (h : U.1 ≤ V.1) (k : V.1 ≤ W.1),
      t U W (h.trans k) = t U V h ≫ t V W k := fun U V W h k ↦ by
    rw [← cancel_mono (c W), ht, Category.assoc, ht, ← Category.assoc, ht, Category.assoc,
      X.homOfLE_homOfLE]
  have hpb : ∀ (U V : S) (h : U.1 ≤ V.1),
      IsPullback (t U V h) (c U) (c V) (X.homOfLE h) := fun U V h ↦ by
    refine ⟨⟨ht _ _ _⟩, ⟨PullbackCone.IsLimit.mk _
      (fun s ↦ ((H U V h _ s.snd).2 ⟨s.fst, s.condition⟩).choose) ?_ ?_ ?_⟩⟩
    · intro s
      rw [← cancel_mono (c V), Category.assoc, ht, ← Category.assoc,
        ((H U V h _ s.snd).2 ⟨s.fst, s.condition⟩).choose_spec, s.condition]
    · intro s
      exact ((H U V h _ s.snd).2 ⟨s.fst, s.condition⟩).choose_spec
    · intro s m _ h2
      rw [← cancel_mono (c U), h2, ((H U V h _ s.snd).2 ⟨s.fst, s.condition⟩).choose_spec]
  letI := locallyDirected S hcov hinf
  let d : (coverOfSet S hcov).RelativeGluingData :=
    { functor :=
        { obj := C
          map := fun {U V} h ↦ t U V h.le
          map_id := hid
          map_comp := fun {U V W} h k ↦ hcomp U V W h.le k.le }
      natTrans := { app := c, naturality := fun U V h ↦ ht U V h.le }
      equifibered := fun {U V} h ↦ hpb U V h.le }
  exact ⟨d.glued, d.toBase, d.cover.f, d.isPullback_natTrans_ι_toBase⟩

theorem exists_glue_isClosedImmersion : ∀ (X : Scheme.{0}) (ι : Type) (Xi : ι → Scheme.{0}) (m : ∀ i, Xi i ⟶ X), (∀ i, IsOpenImmersion (m i)) → (∀ x : X, ∃ i, x ∈ Set.range (m i)) → ∀ (A : ι → Scheme.{0}) (a : ∀ i, A i ⟶ Xi i), (∀ i, IsClosedImmersion (a i)) → (∀ (i j : ι) (Y : Scheme.{0}) (g : Y ⟶ Xi i) (g' : Y ⟶ Xi j), g ≫ m i = g' ≫ m j → ((∃ z : Y ⟶ A i, z ≫ a i = g) ↔ (∃ z : Y ⟶ A j, z ≫ a j = g'))) → ∃ (B : Scheme.{0}) (b : B ⟶ X), IsClosedImmersion b ∧ ∀ (i : ι) (Y : Scheme.{0}) (g : Y ⟶ Xi i), ((∃ z : Y ⟶ B, z ≫ b = g ≫ m i) ↔ (∃ z : Y ⟶ A i, z ≫ a i = g)) := by
  intro X ι Xi m hm hcov A a ha hcomp
  let S : Set X.Opens := {U | ∃ i, U ≤ (m i).opensRange}
  have hS : ∀ x : X, ∃ U ∈ S, x ∈ U := fun x ↦ by
    obtain ⟨i, hi⟩ := hcov x
    exact ⟨(m i).opensRange, ⟨i, le_rfl⟩, hi⟩
  have hinf : ∀ U ∈ S, ∀ V ∈ S, U ⊓ V ∈ S := fun U ⟨i, hi⟩ V _ ↦ ⟨i, inf_le_left.trans hi⟩
  have hl : ∀ (U : X.Opens) (i : ι), U ≤ (m i).opensRange →
      ∃ l : U.toScheme ⟶ Xi i, l ≫ m i = U.ι := fun U i h ↦
    ⟨IsOpenImmersion.lift (m i) U.ι (by rw [Scheme.Opens.range_ι]; exact h),
      IsOpenImmersion.lift_fac _ _ _⟩
  choose l hl using hl
  have hC : ∀ U : S, ∃ (C : Scheme.{0}) (c : C ⟶ U.1.toScheme), IsClosedImmersion c ∧
      ∀ (i : ι) (Y : Scheme.{0}) (g : Y ⟶ Xi i) (h : Y ⟶ U.1.toScheme), h ≫ U.1.ι = g ≫ m i →
        ((∃ z : Y ⟶ C, z ≫ c = h) ↔ ∃ z : Y ⟶ A i, z ≫ a i = g) := by
    rintro ⟨U, j, hj⟩
    refine ⟨pullback (a j) (l U j hj), pullback.snd _ _, inferInstance, fun i Y g h hg ↦ ?_⟩
    rw [← hcomp j i Y (h ≫ l U j hj) g (by rw [Category.assoc, hl, hg])]
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z ≫ pullback.fst _ _, by simp [pullback.condition]⟩
    · rintro ⟨z, hz⟩
      exact ⟨pullback.lift z h hz, pullback.lift_snd _ _ _⟩
  choose C c hc hCa using hC
  obtain ⟨B, b, e, he⟩ := exists_glue S hS hinf C c (by
    intro U V h Y g
    obtain ⟨i, hi⟩ := V.2
    rw [hCa U i Y (g ≫ l U.1 i (h.trans hi)) g (by rw [Category.assoc, hl]),
      hCa V i Y (g ≫ l U.1 i (h.trans hi)) (g ≫ X.homOfLE h)
        (by rw [Category.assoc, Category.assoc, hl, X.homOfLE_ι])])
  refine ⟨B, b, ?_, fun i Y g ↦ ?_⟩
  · apply IsZariskiLocalAtTarget.of_openCover (P := @IsClosedImmersion) (coverOfSet S hS)
    intro U
    have := hc U
    change IsClosedImmersion (pullback.snd b U.1.ι)
    rw [← (he U).flip.isoPullback_inv_snd]
    infer_instance
  · let U : S := ⟨(m i).opensRange, i, le_rfl⟩
    have hh : (g ≫ (m i).isoOpensRange.hom) ≫ U.1.ι = g ≫ m i := by simp [U]
    rw [← hCa U i Y g _ hh]
    constructor
    · rintro ⟨z, hz⟩
      exact ⟨(he U).lift _ z (hh.trans hz.symm), (he U).lift_fst _ _ _⟩
    · rintro ⟨z, hz⟩
      exact ⟨z ≫ e U, by rw [Category.assoc, ← (he U).w, ← Category.assoc, hz, hh]⟩

end GlobalTheory.GlueClosed
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlueClosedImmersionsOpenCoverStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_glue_closedImmersions_open_cover : ∀ (X : Scheme.{0}) (ι : Type) (Xi : ι → Scheme.{0}) (m : ∀ i, Xi i ⟶ X), (∀ i, IsOpenImmersion (m i)) → (∀ x : X, ∃ i, x ∈ Set.range (m i)) → ∀ (A : ι → Scheme.{0}) (a : ∀ i, A i ⟶ Xi i), (∀ i, IsClosedImmersion (a i)) → (∀ (i j : ι) (Y : Scheme.{0}) (g : Y ⟶ Xi i) (g' : Y ⟶ Xi j), g ≫ m i = g' ≫ m j → ((∃ z : Y ⟶ A i, z ≫ a i = g) ↔ (∃ z : Y ⟶ A j, z ≫ a j = g'))) → ∃ (B : Scheme.{0}) (b : B ⟶ X), IsClosedImmersion b ∧ ∀ (i : ι) (Y : Scheme.{0}) (g : Y ⟶ Xi i), ((∃ z : Y ⟶ B, z ≫ b = g ≫ m i) ↔ (∃ z : Y ⟶ A i, z ≫ a i = g)) := by
  first | exact @GlobalTheory.GlueClosed.exists_glue_isClosedImmersion | exact GlobalTheory.GlueClosed.exists_glue_isClosedImmersion | (intros; apply GlobalTheory.GlueClosed.exists_glue_isClosedImmersion <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhiskerLeftLeftIsPullbackSnd
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhiskerLeftLeftIsPullbackSnd
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem whiskerLeft_left_isPullback_snd (S : Scheme.{0}) (U T T' : Over S) (f : T' ⟶ T) :
    IsPullback (U ◁ f).left (snd U T').left (snd U T).left f.left := by
  have hw : (U ◁ f).left ≫ (snd U T).left = (snd U T').left ≫ f.left := by
    rw [← Over.comp_left, ← Over.comp_left, whiskerLeft_snd]
  refine IsPullback.of_right (h₁₂ := (fst U T).left) (h₂₂ := T.hom) (v₁₃ := U.hom) ?_ hw ?_
  · have h1 : (U ◁ f).left ≫ (fst U T).left = (fst U T').left := by
      rw [← Over.comp_left, whiskerLeft_fst]
    have h2 : f.left ≫ T.hom = T'.hom := Over.w f
    rw [h1, h2, Over.fst_left, Over.snd_left]
    exact IsPullback.of_hasPullback U.hom T'.hom
  · rw [Over.fst_left, Over.snd_left]
    exact IsPullback.of_hasPullback U.hom T.hom

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhiskerLeftLeftIsPullbackSndStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPullback_whiskerLeft_left_snd : ∀ (S : Scheme.{0}) (U T T' : Over S) (f : T' ⟶ T), IsPullback (U ◁ f).left (snd U T').left (snd U T).left f.left := by
  first | exact @GlobalTheory.whiskerLeft_left_isPullback_snd | exact GlobalTheory.whiskerLeft_left_isPullback_snd | (intros; apply GlobalTheory.whiskerLeft_left_isPullback_snd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFlatSurjectiveClosedSubschemeOfOpenCover
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFlatSurjectiveClosedSubschemeOfOpenCover
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_isPullback_of_factor_iff {C : Type*} [Category C] {X X' A B : C} (m : X' ⟶ X)
    (b : B ⟶ X) (a : A ⟶ X') [Mono a] [Mono b]
    (h : ∀ (Y : C) (g : Y ⟶ X'), (∃ z : Y ⟶ B, z ≫ b = g ≫ m) ↔ (∃ z : Y ⟶ A, z ≫ a = g)) :
    ∃ k : A ⟶ B, IsPullback k a b m := by
  obtain ⟨k, hk⟩ := (h A a).2 ⟨𝟙 A, Category.id_comp a⟩
  refine ⟨k, ⟨hk⟩, ⟨PullbackCone.IsLimit.mk hk
    (fun s => ((h s.pt s.snd).1 ⟨s.fst, s.condition⟩).choose) ?_ ?_ ?_⟩⟩
  · intro s
    have hs := ((h s.pt s.snd).1 ⟨s.fst, s.condition⟩).choose_spec
    rw [← cancel_mono b, Category.assoc, hk, ← Category.assoc, hs, s.condition]
  · intro s
    exact ((h s.pt s.snd).1 ⟨s.fst, s.condition⟩).choose_spec
  · intro s l _ hl
    have hs := ((h s.pt s.snd).1 ⟨s.fst, s.condition⟩).choose_spec
    rw [← cancel_mono a, hl, hs]

theorem of_isPullback_openCover (P : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget P]
    {B T : Scheme.{0}} (f : B ⟶ T) {ι : Type} (V : ι → T.Opens) (hV : iSup V = ⊤)
    (A : ι → Scheme.{0}) (k : ∀ i, A i ⟶ B) (g : ∀ i, A i ⟶ (V i).toScheme)
    (h : ∀ i, IsPullback (k i) (g i) f (V i).ι) (hg : ∀ i, P (g i)) : P f := by
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := P) V hV]
  intro i
  have h' := (isPullback_morphismRestrict f (V i)).flip
  have e : (h'.isoIsPullback _ _ (h i)).hom ≫ g i = f ∣_ V i := by simp
  rw [← e]
  exact (P.cancel_left_of_respectsIso _ _).2 (hg i)


set_option backward.isDefEq.respectTransparency.types false in
theorem finite_flat_surjective_of_openCover : ∀ (X T₀ : Scheme.{0}) (p : X ⟶ T₀) (ι : Type) (V : ι → T₀.Opens), iSup V = ⊤ → ∀ (Xi : ι → Scheme.{0}) (m : ∀ i, Xi i ⟶ X) (q : ∀ i, Xi i ⟶ (V i).toScheme), (∀ i, IsPullback (m i) (q i) p (V i).ι) → ∀ (B : Scheme.{0}) (b : B ⟶ X), IsClosedImmersion b → ∀ (A : ι → Scheme.{0}) (a : ∀ i, A i ⟶ Xi i), (∀ i, IsClosedImmersion (a i)) → (∀ (i : ι) (Y : Scheme.{0}) (g : Y ⟶ Xi i), (∃ z : Y ⟶ B, z ≫ b = g ≫ m i) ↔ (∃ z : Y ⟶ A i, z ≫ a i = g)) → (∀ i, IsFinite (a i ≫ q i) ∧ Flat (a i ≫ q i) ∧ Surjective (a i ≫ q i)) → IsFinite (b ≫ p) ∧ Flat (b ≫ p) ∧ Surjective (b ≫ p) := by
  intro X T₀ p ι V hV Xi m q hpb B b hb A a ha hrep hP
  have H : ∀ i, ∃ k : A i ⟶ B, IsPullback k (a i ≫ q i) (b ≫ p) (V i).ι := by
    intro i
    have := ha i
    obtain ⟨k, hk⟩ := exists_isPullback_of_factor_iff (m i) b (a i) (hrep i)
    exact ⟨k, hk.paste_vert (hpb i)⟩
  choose k hk using H
  have hfin : IsZariskiLocalAtTarget @IsFinite.{0} :=
    inferInstance
  have hflat : IsZariskiLocalAtTarget @Flat.{0} :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Flat.{0})
  exact ⟨of_isPullback_openCover @IsFinite _ V hV A k _ hk (fun i => (hP i).1),
    of_isPullback_openCover @Flat _ V hV A k _ hk (fun i => (hP i).2.1),
    of_isPullback_openCover @Surjective _ V hV A k _ hk (fun i => (hP i).2.2)⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFlatSurjectiveClosedSubschemeOfOpenCoverStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_flat_surjective_closedSubscheme_of_openCover : ∀ (X T₀ : Scheme.{0}) (p : X ⟶ T₀) (ι : Type) (V : ι → T₀.Opens), iSup V = ⊤ → ∀ (Xi : ι → Scheme.{0}) (m : ∀ i, Xi i ⟶ X) (q : ∀ i, Xi i ⟶ (V i).toScheme), (∀ i, IsPullback (m i) (q i) p (V i).ι) → ∀ (B : Scheme.{0}) (b : B ⟶ X), IsClosedImmersion b → ∀ (A : ι → Scheme.{0}) (a : ∀ i, A i ⟶ Xi i), (∀ i, IsClosedImmersion (a i)) → (∀ (i : ι) (Y : Scheme.{0}) (g : Y ⟶ Xi i), (∃ z : Y ⟶ B, z ≫ b = g ≫ m i) ↔ (∃ z : Y ⟶ A i, z ≫ a i = g)) → (∀ i, IsFinite (a i ≫ q i) ∧ Flat (a i ≫ q i) ∧ Surjective (a i ≫ q i)) → IsFinite (b ≫ p) ∧ Flat (b ≫ p) ∧ Surjective (b ≫ p) := by
  first | exact @GlobalTheory.finite_flat_surjective_of_openCover | exact GlobalTheory.finite_flat_surjective_of_openCover | (intros; apply GlobalTheory.finite_flat_surjective_of_openCover <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorClosedImmersionOfLocallyOnSource
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorClosedImmersionOfLocallyOnSource
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_factor_closedImmersion_of_locally :
    ∀ (Z A Y : Scheme.{0}) (a : A ⟶ Z), IsClosedImmersion a → ∀ (g : Y ⟶ Z),
      (∀ y : Y, ∃ W : Y.Opens, y ∈ W ∧ ∃ z : W.toScheme ⟶ A, z ≫ a = W.ι ≫ g) →
      ∃ z : Y ⟶ A, z ≫ a = g := by
  intro Z A Y a ha g h
  choose W hW z hz using h
  have hc : TopologicalSpace.IsOpenCover W := by
    refine TopologicalSpace.IsOpenCover.mk ?_
    rw [eq_top_iff]
    intro y _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hW y⟩
  let 𝒰 := Y.openCoverOfIsOpenCover W hc
  obtain ⟨u, hu⟩ : ∃ u : ∀ i, 𝒰.X i ⟶ A, ∀ i, u i ≫ a = 𝒰.f i ≫ g := ⟨z, hz⟩
  have hglue : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ u i =
      pullback.snd (𝒰.f i) (𝒰.f j) ≫ u j := by
    intro i j
    rw [← cancel_mono a, Category.assoc, Category.assoc, hu, hu, pullback.condition_assoc]
  refine ⟨𝒰.glueMorphisms u hglue, ?_⟩
  refine 𝒰.hom_ext _ _ fun i => ?_
  rw [← Category.assoc, Scheme.Cover.ι_glueMorphisms]
  exact hu i

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorClosedImmersionOfLocallyOnSourceStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_factor_closedImmersion_of_locally_on_source : ∀ (Z A Y : Scheme.{0}) (a : A ⟶ Z), IsClosedImmersion a → ∀ (g : Y ⟶ Z), (∀ y : Y, ∃ W : Y.Opens, y ∈ W ∧ ∃ z : W.toScheme ⟶ A, z ≫ a = W.ι ≫ g) → ∃ z : Y ⟶ A, z ≫ a = g := by
  first | exact @GlobalTheory.exists_factor_closedImmersion_of_locally | exact GlobalTheory.exists_factor_closedImmersion_of_locally | (intros; apply GlobalTheory.exists_factor_closedImmersion_of_locally <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedImmersionRepresentsOfAffineOpens
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_closedImmersion_represents_of_affineOpens : ∀ (S : Scheme.{0}) (U T : Over S) (P : ∀ Y : Over S, (Y ⟶ U) → (Y ⟶ T) → Prop), (∀ (Y Y' : Over S) (f : Y' ⟶ Y) (u : Y ⟶ U) (t : Y ⟶ T), P Y u t → P Y' (f ≫ u) (f ≫ t)) → (∀ (Y : Over S) (u : Y ⟶ U) (t : Y ⟶ T), (∀ y : Y.left, ∃ W : Y.left.Opens, y ∈ W ∧ P (Over.mk (W.ι ≫ Y.hom)) (Over.homMk W.ι rfl ≫ u) (Over.homMk W.ι rfl ≫ t)) → P Y u t) → (∀ V : T.left.affineOpens, ∃ (H : Over S) (h : H ⟶ U ⊗ Over.mk (V.1.ι ≫ T.hom)), IsClosedImmersion h.left ∧ IsFinite (h ≫ snd U (Over.mk (V.1.ι ≫ T.hom))).left ∧ Flat (h ≫ snd U (Over.mk (V.1.ι ≫ T.hom))).left ∧ Surjective (h ≫ snd U (Over.mk (V.1.ι ≫ T.hom))).left ∧ ∀ (Y : Over S) (u : Y ⟶ U) (t : Y ⟶ Over.mk (V.1.ι ≫ T.hom)), P Y u (t ≫ Over.homMk V.1.ι rfl) ↔ ∃ z : Y ⟶ H, z ≫ h = lift u t) → ∃ (H : Over S) (h : H ⟶ U ⊗ T), IsClosedImmersion h.left ∧ IsFinite (h ≫ snd U T).left ∧ Flat (h ≫ snd U T).left ∧ Surjective (h ≫ snd U T).left ∧ ∀ (Y : Over S) (u : Y ⟶ U) (t : Y ⟶ T), P Y u t ↔ ∃ z : Y ⟶ H, z ≫ h = lift u t := by
  intro S U T P hres hloc hV
  choose H h hci hfin hflat hsurj hrep using hV
  have key : ∀ (V : T.left.affineOpens) (Y : Over S) (g : Y ⟶ U ⊗ Over.mk (V.1.ι ≫ T.hom)),
      P Y (g ≫ (U ◁ (Over.homMk V.1.ι rfl : Over.mk (V.1.ι ≫ T.hom) ⟶ T)) ≫ fst U T)
        (g ≫ (U ◁ (Over.homMk V.1.ι rfl : Over.mk (V.1.ι ≫ T.hom) ⟶ T)) ≫ snd U T) ↔
      ∃ z : Y.left ⟶ (H V).left, z ≫ (h V).left = g.left := by
    intro V Y g
    rw [whiskerLeft_fst, whiskerLeft_snd, ← Category.assoc g]
    rw [hrep V Y (g ≫ fst _ _) (g ≫ snd _ _), lift_comp_fst_snd]
    constructor
    · rintro ⟨z, hz⟩; exact ⟨z.left, by rw [← Over.comp_left, hz]⟩
    · rintro ⟨z, hz⟩
      refine ⟨Over.homMk z ?_, ?_⟩
      · rw [← Over.w (h V), ← Category.assoc, hz, Over.w g]
      · apply Over.OverMorphism.ext; simpa using hz

  have hpb : ∀ V : T.left.affineOpens,
      IsPullback (U ◁ (Over.homMk V.1.ι rfl : Over.mk (V.1.ι ≫ T.hom) ⟶ T)).left
        (snd U (Over.mk (V.1.ι ≫ T.hom))).left (snd U T).left V.1.ι :=
    fun V => _root_.GlobalTheory.T.isPullback_whiskerLeft_left_snd S U T _ _
  have hoi : ∀ V : T.left.affineOpens,
      IsOpenImmersion (U ◁ (Over.homMk V.1.ι rfl : Over.mk (V.1.ι ≫ T.hom) ⟶ T)).left :=
    fun V => MorphismProperty.of_isPullback (P := @IsOpenImmersion) (hpb V).flip inferInstance
  have hmem : ∀ y : T.left, ∃ V : T.left.affineOpens, y ∈ V.1 := by
    intro y
    obtain ⟨_, ⟨V, hV, rfl⟩, hyV, -⟩ :=
      T.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
    exact ⟨⟨V, hV⟩, hyV⟩
  have hsup : (⨆ V : T.left.affineOpens, (V.1 : T.left.Opens)) = ⊤ := by
    rw [eq_top_iff]; intro y _
    obtain ⟨V, hV⟩ := hmem y
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨V, hV⟩
  have hcov : ∀ x : (U ⊗ T).left, ∃ V : T.left.affineOpens,
      x ∈ Set.range (U ◁ (Over.homMk V.1.ι rfl : Over.mk (V.1.ι ≫ T.hom) ⟶ T)).left := by
    intro x
    obtain ⟨V, hV⟩ := hmem ((snd U T).left x)
    obtain ⟨v, hv⟩ : (snd U T).left x ∈ Set.range V.1.ι := by rw [Scheme.Opens.range_ι]; exact hV
    obtain ⟨w, hw1, -⟩ := Scheme.Pullback.exists_preimage_pullback x v hv.symm
    refine ⟨V, (hpb V).isoPullback.inv w, ?_⟩
    rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst]; exact hw1
  have compat : ∀ (V V' : T.left.affineOpens) (Y : Scheme.{0})
      (g : Y ⟶ (U ⊗ Over.mk (V.1.ι ≫ T.hom)).left) (g' : Y ⟶ (U ⊗ Over.mk (V'.1.ι ≫ T.hom)).left),
      g ≫ (U ◁ (Over.homMk V.1.ι rfl : Over.mk (V.1.ι ≫ T.hom) ⟶ T)).left =
        g' ≫ (U ◁ (Over.homMk V'.1.ι rfl : Over.mk (V'.1.ι ≫ T.hom) ⟶ T)).left →
      ((∃ z : Y ⟶ (H V).left, z ≫ (h V).left = g) ↔ (∃ z : Y ⟶ (H V').left, z ≫ (h V').left = g')) := by
    intro V V' Y g g' hgg
    let Y' : Over S := Over.mk (g ≫ (U ◁ (Over.homMk V.1.ι rfl : Over.mk (V.1.ι ≫ T.hom) ⟶ T)).left ≫ (U ⊗ T).hom)
    let e : Y' ⟶ U ⊗ Over.mk (V.1.ι ≫ T.hom) := Over.homMk g (by simp [Y'])
    let e' : Y' ⟶ U ⊗ Over.mk (V'.1.ι ≫ T.hom) := Over.homMk g' (by
      show _ = g ≫ _ ≫ _; rw [← Category.assoc g, hgg, Category.assoc, Over.w])
    have hm : e ≫ (U ◁ (Over.homMk V.1.ι rfl : Over.mk (V.1.ι ≫ T.hom) ⟶ T)) =
        e' ≫ (U ◁ (Over.homMk V'.1.ι rfl : Over.mk (V'.1.ι ≫ T.hom) ⟶ T)) := by
      apply Over.OverMorphism.ext; simpa [e, e'] using hgg
    have k := key V Y' e
    have k' := key V' Y' e'
    rw [reassoc_of% hm, reassoc_of% hm] at k
    exact k.symm.trans k'
  obtain ⟨B, b, hb, hbrep⟩ := _root_.GlobalTheory.T.exists_glue_closedImmersions_open_cover (U ⊗ T).left T.left.affineOpens _ _ hoi hcov
    (fun V => (H V).left) (fun V => (h V).left) hci compat
  have hprops := _root_.GlobalTheory.T.finite_flat_surjective_closedSubscheme_of_openCover (U ⊗ T).left T.left (snd U T).left T.left.affineOpens
    (fun V => V.1) hsup _ _ _ hpb B b hb _ _ hci hbrep
    (fun V => ⟨hfin V, hflat V, hsurj V⟩)
  refine ⟨Over.mk (b ≫ (U ⊗ T).hom), Over.homMk b rfl, hb, hprops.1, hprops.2.1, hprops.2.2, ?_⟩
  intro Y u t

  have hW : ∀ (V : T.left.affineOpens),
      P (Over.mk ((t.left ⁻¹ᵁ V.1).ι ≫ Y.hom)) (Over.homMk (t.left ⁻¹ᵁ V.1).ι rfl ≫ u)
        (Over.homMk (t.left ⁻¹ᵁ V.1).ι rfl ≫ t) ↔
      ∃ z : (t.left ⁻¹ᵁ V.1).toScheme ⟶ B, z ≫ b = (t.left ⁻¹ᵁ V.1).ι ≫ (lift u t).left := by
    intro V
    have hr : Set.range ((t.left ⁻¹ᵁ V.1).ι ≫ t.left) ⊆ Set.range V.1.ι := by
      rintro _ ⟨w, rfl⟩
      rw [Scheme.Opens.range_ι]
      have h1 : (t.left ⁻¹ᵁ V.1).ι w ∈ ((t.left ⁻¹ᵁ V.1 : Y.left.Opens) : Set Y.left) := by
        rw [← Scheme.Opens.range_ι]; exact Set.mem_range_self w
      rw [Scheme.Hom.comp_apply]; exact h1
    let tW : Over.mk ((t.left ⁻¹ᵁ V.1).ι ≫ Y.hom) ⟶ Over.mk (V.1.ι ≫ T.hom) :=
      Over.homMk (IsOpenImmersion.lift V.1.ι _ hr) (by simp [IsOpenImmersion.lift_fac_assoc])
    have htW : tW ≫ (Over.homMk V.1.ι rfl : Over.mk (V.1.ι ≫ T.hom) ⟶ T) =
        Over.homMk (t.left ⁻¹ᵁ V.1).ι rfl ≫ t := by
      apply Over.OverMorphism.ext; simp [tW, IsOpenImmersion.lift_fac]
    let gW := lift (Over.homMk (t.left ⁻¹ᵁ V.1).ι rfl ≫ u) tW
    have hgW : gW ≫ (U ◁ (Over.homMk V.1.ι rfl : Over.mk (V.1.ι ≫ T.hom) ⟶ T)) =
        Over.homMk (t.left ⁻¹ᵁ V.1).ι rfl ≫ lift u t := by
      apply CartesianMonoidalCategory.hom_ext <;> simp [gW, htW]
    have k := key V _ gW
    rw [reassoc_of% hgW, reassoc_of% hgW, lift_fst, lift_snd] at k
    rw [k, ← hbrep V _ gW.left, ← Over.comp_left, hgW]
    rfl
  constructor
  · intro hP
    obtain ⟨z, hz⟩ := _root_.GlobalTheory.T.exists_factor_closedImmersion_of_locally_on_source _ _ _ b hb (lift u t).left (fun y => by
      obtain ⟨V, hV⟩ := hmem (t.left y)
      exact ⟨t.left ⁻¹ᵁ V.1, hV, (hW V).mp (hres _ _ _ u t hP)⟩)
    refine ⟨Over.homMk z ?_, ?_⟩
    · simp only [Over.mk_hom]; rw [← Category.assoc, hz, Over.w]
    · apply Over.OverMorphism.ext; simpa using hz
  · rintro ⟨z, hz⟩
    apply hloc
    intro y
    obtain ⟨V, hV⟩ := hmem (t.left y)
    refine ⟨t.left ⁻¹ᵁ V.1, hV, (hW V).mpr ⟨(t.left ⁻¹ᵁ V.1).ι ≫ z.left, ?_⟩⟩
    rw [Category.assoc, ← hz]; rfl
end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedImmersionRepresentsOfAffineOpensStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_closedImmersion_represents_of_affineOpens_alt : ∀ (S : Scheme.{0}) (U T : Over S) (P : ∀ Y : Over S, (Y ⟶ U) → (Y ⟶ T) → Prop), (∀ (Y Y' : Over S) (f : Y' ⟶ Y) (u : Y ⟶ U) (t : Y ⟶ T), P Y u t → P Y' (f ≫ u) (f ≫ t)) → (∀ (Y : Over S) (u : Y ⟶ U) (t : Y ⟶ T), (∀ y : Y.left, ∃ W : Y.left.Opens, y ∈ W ∧ P (Over.mk (W.ι ≫ Y.hom)) (Over.homMk W.ι rfl ≫ u) (Over.homMk W.ι rfl ≫ t)) → P Y u t) → (∀ V : T.left.affineOpens, ∃ (H : Over S) (h : H ⟶ U ⊗ Over.mk (V.1.ι ≫ T.hom)), IsClosedImmersion h.left ∧ IsFinite (h ≫ snd U (Over.mk (V.1.ι ≫ T.hom))).left ∧ Flat (h ≫ snd U (Over.mk (V.1.ι ≫ T.hom))).left ∧ Surjective (h ≫ snd U (Over.mk (V.1.ι ≫ T.hom))).left ∧ ∀ (Y : Over S) (u : Y ⟶ U) (t : Y ⟶ Over.mk (V.1.ι ≫ T.hom)), P Y u (t ≫ Over.homMk V.1.ι rfl) ↔ ∃ z : Y ⟶ H, z ≫ h = lift u t) → ∃ (H : Over S) (h : H ⟶ U ⊗ T), IsClosedImmersion h.left ∧ IsFinite (h ≫ snd U T).left ∧ Flat (h ≫ snd U T).left ∧ Surjective (h ≫ snd U T).left ∧ ∀ (Y : Over S) (u : Y ⟶ U) (t : Y ⟶ T), P Y u t ↔ ∃ z : Y ⟶ H, z ≫ h = lift u t := by
  first | exact @GlobalTheory.exists_closedImmersion_represents_of_affineOpens | exact GlobalTheory.exists_closedImmersion_represents_of_affineOpens | (intros; apply GlobalTheory.exists_closedImmersion_represents_of_affineOpens <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleFamilyAgreementLocusOfAffineOpen
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon.GlueKernel

theorem same_comp {S : Scheme.{0}} {A U T Y Y' : Over S} {M : LB (A ⊗ U).left} {N : LB (A ⊗ T).left}
    (hM : M.IsLB) (hN : N.IsLB) (f : Y' ⟶ Y) (u : Y ⟶ U) (t : Y ⟶ T) (h : Same A M N u t) :
    Same A M N (f ≫ u) (f ≫ t) := by
  rw [same_iff hM hN] at h ⊢
  have e := congrArg (GlobalTheory.CechPic.pull (A ◁ f).left) h
  rw [pull_evc, pull_evc] at e
  simpa only [whiskerLeft_fst, whiskerLeft_snd_assoc] using e

theorem exists_kernel_of_affine : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (U T : Over (Sp R)) (M : LB (A ⊗ U).left) (N : LB (A ⊗ T).left) (hM : M.IsLB) (hN : N.IsLB), (∀ (Y : Over (Sp R)) (u : Y ⟶ U), evc hM (1 : Y ⟶ A) u = 0) → (∀ (Y : Over (Sp R)) (t : Y ⟶ T), evc hN (1 : Y ⟶ A) t = 0) → (∀ V : T.left.affineOpens, ∃ (H : Over (Sp R)) (h : H ⟶ U ⊗ Over.mk (V.1.ι ≫ T.hom)), IsClosedImmersion h.left ∧ IsFinite (h ≫ snd U (Over.mk (V.1.ι ≫ T.hom))).left ∧ Flat (h ≫ snd U (Over.mk (V.1.ι ≫ T.hom))).left ∧ Surjective (h ≫ snd U (Over.mk (V.1.ι ≫ T.hom))).left ∧ ∀ (Y : Over (Sp R)) (u : Y ⟶ U) (t : Y ⟶ Over.mk (V.1.ι ≫ T.hom)), Same A M N u (t ≫ Over.homMk V.1.ι rfl) ↔ ∃ z : Y ⟶ H, z ≫ h = lift u t) → ∃ (H : Over (Sp R)) (h : H ⟶ U ⊗ T), IsClosedImmersion h.left ∧ IsFinite (h ≫ snd U T).left ∧ Flat (h ≫ snd U T).left ∧ Surjective (h ≫ snd U T).left ∧ ∀ (Y : Over (Sp R)) (u : Y ⟶ U) (t : Y ⟶ T), Same A M N u t ↔ ∃ z : Y ⟶ H, z ≫ h = lift u t := by
  intro R _ _ A _ hA U T M N hM hN h0M h0N hV
  exact GlobalTheory.T.exists_closedImmersion_represents_of_affineOpens_alt (Sp R) U T (fun Y u t => Same A M N u t)
    (fun Y Y' f u t h => same_comp hM hN f u t h)
    (fun Y u t h => GlobalTheory.T.sameRigidifiedFamily_abelianScheme_of_local R A hA U T M N hM hN h0M h0N Y u t h) hV

end GlobalTheory.DualCon.GlueKernel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleFamilyAgreementLocusOfAffineOpenStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lineBundleFamily_agreementLocus_of_affineOpens : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (U T : Over (Sp R)) (M : LB (A ⊗ U).left) (N : LB (A ⊗ T).left) (hM : M.IsLB) (hN : N.IsLB), (∀ (Y : Over (Sp R)) (u : Y ⟶ U), evc hM (1 : Y ⟶ A) u = 0) → (∀ (Y : Over (Sp R)) (t : Y ⟶ T), evc hN (1 : Y ⟶ A) t = 0) → (∀ V : T.left.affineOpens, ∃ (H : Over (Sp R)) (h : H ⟶ U ⊗ Over.mk (V.1.ι ≫ T.hom)), IsClosedImmersion h.left ∧ IsFinite (h ≫ snd U (Over.mk (V.1.ι ≫ T.hom))).left ∧ Flat (h ≫ snd U (Over.mk (V.1.ι ≫ T.hom))).left ∧ Surjective (h ≫ snd U (Over.mk (V.1.ι ≫ T.hom))).left ∧ ∀ (Y : Over (Sp R)) (u : Y ⟶ U) (t : Y ⟶ Over.mk (V.1.ι ≫ T.hom)), Same A M N u (t ≫ Over.homMk V.1.ι rfl) ↔ ∃ z : Y ⟶ H, z ≫ h = lift u t) → ∃ (H : Over (Sp R)) (h : H ⟶ U ⊗ T), IsClosedImmersion h.left ∧ IsFinite (h ≫ snd U T).left ∧ Flat (h ≫ snd U T).left ∧ Surjective (h ≫ snd U T).left ∧ ∀ (Y : Over (Sp R)) (u : Y ⟶ U) (t : Y ⟶ T), Same A M N u t ↔ ∃ z : Y ⟶ H, z ≫ h = lift u t := by
  first | exact @GlobalTheory.DualCon.GlueKernel.exists_kernel_of_affine | exact GlobalTheory.DualCon.GlueKernel.exists_kernel_of_affine | (intros; apply GlobalTheory.DualCon.GlueKernel.exists_kernel_of_affine <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlatCoverAdditiveFamilyEqLambda
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCover

theorem exists_cover : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (L : LB A.left) (hL : L.IsLB), Out.RelAmple A L → ∀ (T : Over (Sp R)) (N : LB (A ⊗ T).left) (hN : Fam A N), ∃ (H : Over (Sp R)) (h : H ⟶ T) (x : H ⟶ A), Flat h.left ∧ Surjective h.left ∧ QuasiCompact h.left ∧ (∀ (Y : Over (Sp R)) (a : Y ⟶ A) (y : Y ⟶ H), evc hN.isLB a (y ≫ h) = GlobalTheory.CechPic.pull (a * (y ≫ x)).left (cls L hL) - GlobalTheory.CechPic.pull a.left (cls L hL) - GlobalTheory.CechPic.pull (y ≫ x).left (cls L hL) + GlobalTheory.CechPic.pull (1 : Y ⟶ A).left (cls L hL)) := by
  intro R _ _ A _ g hA _ L hL hamp T N hN
  have hP : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  have eP : ∀ (Y : Over (Sp R)) (a b : Y ⟶ A), evc hP a b = lam (cls L hL) a b := fun Y a b ↦ by
    rw [evc, show cls _ hP = lam (cls L hL) (fst A A) (snd A A) from cls_cube_two hL _ _ hP, pull_lam, lift_fst,
      lift_snd]
  have loc : ∀ V : T.left.affineOpens, ∃ (H : Over (Sp R)) (h : H ⟶ A ⊗ Over.mk (V.1.ι ≫ T.hom)),
      IsClosedImmersion h.left ∧ IsFinite (h ≫ snd A (Over.mk (V.1.ι ≫ T.hom))).left ∧
      Flat (h ≫ snd A (Over.mk (V.1.ι ≫ T.hom))).left ∧ Surjective (h ≫ snd A (Over.mk (V.1.ι ≫ T.hom))).left ∧
      ∀ (Y : Over (Sp R)) (u : Y ⟶ A) (t : Y ⟶ Over.mk (V.1.ι ≫ T.hom)),
        Same A (abelian₂ A L) N u (t ≫ Over.homMk V.1.ι rfl) ↔ ∃ z : Y ⟶ H, z ≫ h = lift u t := by
    intro V
    haveI : IsAffine (Over.mk (V.1.ι ≫ T.hom)).left := V.2
    set j : Over.mk (V.1.ι ≫ T.hom) ⟶ T := Over.homMk V.1.ι rfl
    have hNV : (ev N (fst A (Over.mk (V.1.ι ≫ T.hom))) (snd A _ ≫ j)).IsLB := pull_isLB hN.isLB _
    have eV : ∀ (Y : Over (Sp R)) (a : Y ⟶ A) (t : Y ⟶ Over.mk (V.1.ι ≫ T.hom)),
        evc hNV a t = evc hN.isLB a (t ≫ j) := fun Y a t ↦ by
      rw [evc_ev hN.isLB, lift_fst, lift_snd_assoc]
    have fV : Fam A (ev N (fst A (Over.mk (V.1.ι ≫ T.hom))) (snd A _ ≫ j)) :=
      ⟨hNV, (isAdditive_iff hNV).2 fun Y a a' t ↦ by
        rw [eV, eV, eV]; exact (isAdditive_iff hN.isLB).1 hN.add Y a a' (t ≫ j)⟩
    obtain ⟨H, h, h1, h2, h3, h4, h5⟩ := GlobalTheory.T.exists_twistedKernel_closed_finiteFlat_affineBase R A hA L hL hamp _ _ fV
    refine ⟨H, h, h1, h2, h3, h4, fun Y u t ↦ ?_⟩
    rw [← h5, same_iff hP hN.isLB, same_iff hP hNV, eV, Category.assoc]
  obtain ⟨H, h, -, hfin, hfl, hsu, hrep⟩ := GlobalTheory.T.exists_lineBundleFamily_agreementLocus_of_affineOpens R A hA A T (abelian₂ A L) N hP hN.isLB
    (fun Y u ↦ by rw [eP, lam_one_left]) (fun Y t ↦ hN.add.evc_one hN.isLB t) loc
  refine ⟨H, h ≫ snd A T, h ≫ fst A T, hfl, hsu, inferInstance, fun Y a y ↦ ?_⟩
  have hs : Same A (abelian₂ A L) N (y ≫ h ≫ fst A T) (y ≫ h ≫ snd A T) :=
    (hrep Y _ _).2 ⟨y, by ext <;> simp⟩
  have e := congrArg (CechPic.pull (lift a (𝟙 Y)).left) ((same_iff hP hN.isLB _ _).1 hs)
  rw [pull_evc, pull_evc, lift_fst, lift_snd_assoc, Category.id_comp, lift_snd_assoc, Category.id_comp, eP] at e
  rw [← e, lam]

end GlobalTheory.DualCover
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlatCoverAdditiveFamilyEqLambdaStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_flatCover_additiveFamily_eq_lambda : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (L : LB A.left) (hL : L.IsLB), Out.RelAmple A L → ∀ (T : Over (Sp R)) (N : LB (A ⊗ T).left) (hN : Fam A N), ∃ (H : Over (Sp R)) (h : H ⟶ T) (x : H ⟶ A), Flat h.left ∧ Surjective h.left ∧ QuasiCompact h.left ∧ (∀ (Y : Over (Sp R)) (a : Y ⟶ A) (y : Y ⟶ H), evc hN.isLB a (y ≫ h) = GlobalTheory.CechPic.pull (a * (y ≫ x)).left (cls L hL) - GlobalTheory.CechPic.pull a.left (cls L hL) - GlobalTheory.CechPic.pull (y ≫ x).left (cls L hL) + GlobalTheory.CechPic.pull (1 : Y ⟶ A).left (cls L hL)) := by
  first | exact @GlobalTheory.DualCover.exists_cover | exact GlobalTheory.DualCover.exists_cover | (intros; apply GlobalTheory.DualCover.exists_cover <;> assumption)
end
