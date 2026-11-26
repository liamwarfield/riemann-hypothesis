module

public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.NEvalSqZero
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ESecCompOfIsGrpPullback

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TorusPointRelationSuccThickening
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TorusPointRelationSuccThickening
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.ChF

theorem iRel_succ : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : Out.DegData R I) (A : Out.PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : Out.UnifPre I D A G) (k : ℕ) (S : Type) [CommRing S] [Algebra R S] χ z, IRel (U.gt k) S χ z → IRel (U.gt (k + 1)) S χ z := by
  rintro R _ _ I D A G _ _ U k S _ _ χ z ⟨w, hw, hz⟩
  have t : Out.thickMap R I k G ≫ (Out.fstG I (k + 1) G).left = (Out.fstG I k G).left :=
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  let Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (k + 1)))) :=
    Over.mk (w ≫ (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (k + 1)))) D.toPre.X).hom)
  let τ : Z ⟶ splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (k + 1)))) D.toPre.X := Over.homMk w rfl
  let r : Spec (CommRingCat.of S) ⟶ (Out.thickObj R I k G).left := (τ ≫ (U.gt k).i).left
  have hr : r ≫ (Out.fstG I k G).left = z.left := (Category.assoc _ _ _).trans hz
  have c : r ≫ (U.gt k).pG.left = r ≫ (Out.fstG I k G).left ≫ G.hom ≫ eSec D.toPre.P.A :=
    (CharAgree.comp_q_eq_one_iff (U.gt k) (τ ≫ (U.gt k).i)).1 (by
      rw [Category.assoc, (U.gt k).isKernel.w, ← Category.assoc]
      exact congrArg (· ≫ _) (toUnit_unique _ _))
  let Z' : Over (Spec (CommRingCat.of (R ⧸ I ^ (k + 1 + 1)))) :=
    Over.mk ((r ≫ Out.thickMap R I k G) ≫ (Out.thickObj R I (k + 1) G).hom)
  let a : Z' ⟶ Out.thickObj R I (k + 1) G := Over.homMk (r ≫ Out.thickMap R I k G) rfl
  have c' : a.left ≫ (U.gt (k + 1)).pG.left =
      a.left ≫ (Out.fstG I (k + 1) G).left ≫ G.hom ≫ eSec D.toPre.P.A := by
    refine (Category.assoc _ _ _).trans ((congrArg (r ≫ ·) (U.gt_q k)).trans (c.trans ?_))
    refine Eq.trans (congrArg (r ≫ ·) ?_) (Category.assoc _ _ _).symm
    exact (congrArg (· ≫ G.hom ≫ eSec D.toPre.P.A) t.symm).trans (Category.assoc _ _ _)
  let τ' := (U.gt (k + 1)).isKernel.lift a (toUnit _) ((CharAgree.comp_q_eq_one_iff (U.gt (k + 1)) a).2 c')
  have hτ : τ' ≫ (U.gt (k + 1)).i = a := (U.gt (k + 1)).isKernel.lift_fst _ _ _
  refine ⟨τ'.left, fun x => ?_, ?_⟩
  · refine Eq.trans (congrArg (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom ?_) (hw x)
    apply TopCat.Presheaf.section_ext (Spec (CommRingCat.of S)).sheaf ⊤
    intro y hy
    choose J hJ using fun ψ : Spec (CommRingCat.of S) ⟶ D.toPre.P.A.left =>
      Geo.Tor.exists_chart D.toPre.P.isLB (ψ y)
    have k₀ := (TorusCoord.val_torus_point_and_translate R I D.toPre k G (U.gt k) Z τ 1 y J hJ x).1
    have k₁ := (TorusCoord.val_torus_point_and_translate R I D.toPre (k + 1) G (U.gt (k + 1)) Z' τ' 1 y J hJ x).1
    rw [hτ] at k₁
    have e := congrArg Units.val (k₁.symm.trans ((Geo.Tor.val_pull hJ _ (Out.thickMap R I k G) r).symm.trans
      ((Geo.Tor.val_corr hJ (U.gt_t k x) r).trans k₀)))
    exact (Geo.Tor.gm_val _ _ ⊤ trivial _).symm.trans (e.trans (Geo.Tor.gm_val _ _ ⊤ trivial _))
  · refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (fun φ => φ.left ≫ (Out.fstG I (k + 1) G).left) hτ).trans ?_
    exact (Category.assoc _ _ _).trans ((congrArg (r ≫ ·) t).trans hr)

end GlobalTheory.ChF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TorusPointRelationSuccThickeningStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_point_relation_succ_thickening : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : Out.DegData R I) (A : Out.PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : Out.UnifPre I D A G) (k : ℕ) (S : Type) [CommRing S] [Algebra R S] χ z, IRel (U.gt k) S χ z → IRel (U.gt (k + 1)) S χ z := by
  first | exact @GlobalTheory.ChF.iRel_succ | exact GlobalTheory.ChF.iRel_succ | (intros; apply GlobalTheory.ChF.iRel_succ <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AbelianPartLiftSquareZeroUnitPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AbelianPartLiftSquareZeroUnitPoint
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.ChF

private theorem lift_of_smooth_affine {G B : Scheme.{0}} (q : G ⟶ B) [Smooth q] [IsAffineHom q]
    {S S' : Type} [CommRing S] [CommRing S'] (π : S →+* S') (hπ : Function.Surjective π)
    (hk : IsNilpotent (RingHom.ker π)) (y : Spec (CommRingCat.of S) ⟶ B) (x : Spec (CommRingCat.of S') ⟶ G)
    (h : x ≫ q = Spec.map (CommRingCat.ofHom π) ≫ y) :
    ∃ w : Spec (CommRingCat.of S) ⟶ G, w ≫ q = y ∧ Spec.map (CommRingCat.ofHom π) ≫ w = x := by
  have : IsAffine (pullback q y) := isAffine_of_isAffineHom (pullback.snd q y)
  let e := (pullback q y).isoSpec
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (pullback.lift x _ h ≫ e.hom)
  obtain ⟨α, hα⟩ := Spec.map_surjective (e.inv ≫ pullback.snd q y)
  have hs : RingHom.Smooth α.hom := by
    rw [← HasRingHomProperty.Spec_iff (P := @Smooth), hα]
    infer_instance
  have hφα : α ≫ φ = CommRingCat.ofHom π := by
    apply Spec.map_injective
    rw [Spec.map_comp, hα, hφ, Category.assoc, Iso.hom_inv_id_assoc, pullback.lift_snd]
  letI : Algebra S Γ(pullback q y, ⊤) := α.hom.toAlgebra
  letI : Algebra S S' := π.toAlgebra
  haveI : Algebra.Smooth S Γ(pullback q y, ⊤) := hs
  let φ' : Γ(pullback q y, ⊤) →ₐ[S] S' := ⟨φ.hom, fun r => congr($hφα r)⟩
  let ψ := Algebra.FormallySmooth.liftOfSurjective φ' (Algebra.ofId S S') hπ hk
  have hψ : (Algebra.ofId S S').comp ψ = φ' :=
    Algebra.FormallySmooth.comp_liftOfSurjective φ' (Algebra.ofId S S') hπ hk
  let ψ' : Γ(pullback q y, ⊤) ⟶ CommRingCat.of S := CommRingCat.ofHom ψ.toRingHom
  have h₁ : α ≫ ψ' = 𝟙 _ := by
    ext r
    exact ψ.commutes r
  have h₂ : ψ' ≫ CommRingCat.ofHom π = φ := by
    ext a
    exact congr($hψ a)
  refine ⟨Spec.map ψ' ≫ e.inv ≫ pullback.fst q y, ?_, ?_⟩
  · rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc e.inv, ← hα, ← Category.assoc,
      ← Spec.map_comp, h₁, Spec.map_id, Category.id_comp]
  · rw [← Category.assoc, ← Spec.map_comp, h₂, hφ, Category.assoc, Iso.hom_inv_id_assoc, pullback.lift_fst]

theorem qRel_lift : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : Out.DegPre R) (k : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (c : Out.GtCoord I D k G) (S : Type) [CommRing S] [Algebra R S], Kills I k S → ∀ (S' : Type) [CommRing S'] [Algebra R S'] (ρ : S →ₐ[R] S') (σ : S' →ₐ[R] S), ρ.comp σ = AlgHom.id R S' → RingHom.ker ρ ^ 2 = ⊥ → ∀ y : sp (R₀ := R) S ⟶ D.P.A, spMap ρ ≫ y = 1 → ∃ z : sp (R₀ := R) S ⟶ G, spMap ρ ≫ z = 1 ∧ QRel c S z y := by
  intro R _ _ I D k G _ _ c S _ _ hS S' _ _ ρ σ hρσ hk y hy
  have hS' : Kills I k S' := fun t ht => by rw [← ρ.commutes, hS t ht, map_zero]
  obtain ⟨hex, hmul⟩ := (qRel_existsUnique_mul_nat R I D k G c).1 S' hS'
  obtain ⟨y₀, hy₀, hu⟩ := hex 1
  have h1 : y₀ = 1 := by
    have h := hmul 1 1 y₀ y₀ hy₀ hy₀
    rw [_root_.mul_one] at h
    exact mul_eq_left.1 (hu _ h)
  subst h1
  obtain ⟨x, hx₁, hx₂⟩ := hy₀
  have := c.q_hom
  have := c.q_flat
  have := c.q_surj
  have := c.q_affine
  have := (H1.torus_dim (Spec (CommRingCat.of (R ⧸ I ^ (k + 1)))) D.X).smooth
  have : Smooth c.q.left := by
    refine MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      ((H1.torsor_pullback c.i c.q c.isKernel).map (Over.forget _)).flip
      ⟨⟨‹_›, ‹_›⟩, inferInstanceAs (QuasiCompact c.q.left)⟩ ?_
    exact smooth_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) this
  have : IsClosedImmersion (Out.thick R I k) := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hf : Mono (pullback.fst D.P.A.hom (Out.thick R I k)) := inferInstance
  let t : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (k + 1))) :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift (I ^ (k + 1)) (algebraMap R S) hS))
  have ht : t ≫ Out.thick R I k = Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  let y' : Spec (CommRingCat.of S) ⟶ (Out.thickObj R I k D.P.A).left :=
    pullback.lift y.left t ((Over.w y).trans ht.symm)
  have hy' : y' ≫ pullback.fst D.P.A.hom (Out.thick R I k) = y.left := pullback.lift_fst _ _ _
  have hyl : Spec.map (CommRingCat.ofHom ρ.toRingHom) ≫ y.left = (1 : sp (R₀ := R) S' ⟶ D.P.A).left :=
    congrArg (·.left) hy
  obtain ⟨w, hw₁, hw₂⟩ := lift_of_smooth_affine c.q.left ρ.toRingHom
    (fun a => ⟨σ a, congr($hρσ a)⟩) ⟨2, hk⟩ y' x (by
      refine (cancel_mono (pullback.fst D.P.A.hom (Out.thick R I k))).1 ?_
      exact ((Category.assoc _ _ _).trans hx₂).trans
        (hyl.symm.trans ((congrArg (_ ≫ ·) hy'.symm).trans (Category.assoc _ _ _).symm)))
  have hq : w ≫ c.pG.left = y.left := (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hw₁).trans hy')
  have hz : (w ≫ (Out.fstG I k G).left) ≫ G.hom = Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
    have a : (Out.fstG I k G).left ≫ G.hom = c.pG.left ≫ D.P.A.hom := (Over.w _).trans (Over.w _).symm
    exact (Category.assoc _ _ _).trans ((congrArg (w ≫ ·) a).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ D.P.A.hom) hq).trans (Over.w y))))
  refine ⟨Over.homMk (w ≫ (Out.fstG I k G).left) hz, ?_, w, rfl, hq⟩
  apply Over.OverMorphism.ext
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (Out.fstG I k G).left) hw₂).trans hx₁)

end GlobalTheory.ChF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AbelianPartLiftSquareZeroUnitPointStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianPart_lift_square_zero_unit_point : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : Out.DegPre R) (k : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (c : Out.GtCoord I D k G) (S : Type) [CommRing S] [Algebra R S], Kills I k S → ∀ (S' : Type) [CommRing S'] [Algebra R S'] (ρ : S →ₐ[R] S') (σ : S' →ₐ[R] S), ρ.comp σ = AlgHom.id R S' → RingHom.ker ρ ^ 2 = ⊥ → ∀ y : sp (R₀ := R) S ⟶ D.P.A, spMap ρ ≫ y = 1 → ∃ z : sp (R₀ := R) S ⟶ G, spMap ρ ≫ z = 1 ∧ QRel c S z y := by
  first | exact @GlobalTheory.ChF.qRel_lift | exact GlobalTheory.ChF.qRel_lift | (intros; apply GlobalTheory.ChF.qRel_lift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ThickMapCompFstG
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem thickMap_comp_fstG {R : Type} [CommRing R] (I : Ideal R) (e : ℕ)
    (G : Over (Spec (CommRingCat.of R))) :
    Out.thickMap R I e G ≫ (Out.fstG I (e + 1) G).left = (Out.fstG I e G).left :=
  pullback.lift_fst _ _ _ |>.trans (Category.comp_id _)

theorem qRel_succ : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : Out.DegData R I) (A : Out.PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : Out.UnifPre I D A G) (k : ℕ) (S : Type) [CommRing S] [Algebra R S] z y, QRel (U.gt k) S z y → QRel (U.gt (k + 1)) S z y := by
  intro R _ _ I D A G _ _ U k S _ _ z y h
  obtain ⟨w, h₁, h₂⟩ := h
  refine ⟨w ≫ Out.thickMap R I k G, ?_, ?_⟩
  · exact (Category.assoc _ _ _).trans ((congrArg (w ≫ ·) (thickMap_comp_fstG I k G)).trans h₁)
  · exact (Category.assoc _ _ _).trans ((congrArg (w ≫ ·) (U.gt_q k)).trans h₂)

end GlobalTheory.ChF
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AppTopCharUnitOfTorusEndOf
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem appTop_charUnit_of_torusEndOf {S : Scheme.{0}} {X : Type} [AddCommGroup X] {h : X → X}
    {t : splitTorus S X ⟶ splitTorus S X} (ht : Out.TorusEndOf X h t) (χ : X) :
    t.left.appTop.hom (charUnit S X χ).val = (charUnit S X (h χ)).val := by
  have : (res (fun x _ => show t.left.base x ∈ (⊤ : TopologicalSpace.Opens _) from trivial)
      (pullU t.left ⊤ (charUnit S X χ)) : Γ((splitTorus S X).left, ⊤)ˣ).val =
      t.left.appTop.hom (charUnit S X χ).val := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  rw [← this, ht χ]

theorem qRel_iRel_equivariant : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : Out.DegData R I) (A : Out.PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : Out.UnifPre I D A G), ∀ (OE : Type) [CommRing OE] [StarRing OE] [Module OE D.toPre.X] (io : Out.RingAct G OE) (oD : D.OAct OE) (oA : A.OAct OE), U.OLinear OE oD oA io → ∀ (k : ℕ) (a : OE) (S : Type) [CommRing S] [Algebra R S], (∀ z y, QRel (U.gt k) S z y → QRel (U.gt k) S (z ≫ io.act a) (y ≫ oD.onB.act a)) ∧ ∀ χ χ' z, (∀ x, χ' (Multiplicative.ofAdd x) = χ (Multiplicative.ofAdd (star a • x))) → IRel (U.gt k) S χ z → IRel (U.gt k) S χ' (z ≫ io.act a) := by
  intro R _ _ I D A G _ _ U OE _ _ _ io oD oA hl k a S _ _
  have hG : ((Over.pullback (Out.thick R I k)).map (io.act a)).left ≫ (Out.fstG I k G).left =
      (Out.fstG I k G).left ≫ (io.act a).left :=
    GlobalTheory.SplitTorusPoints.map_left_fst (Out.thick R I k) (io.act a)
  refine ⟨?_, ?_⟩
  · rintro z y ⟨w, h1, h2⟩
    refine ⟨w ≫ ((Over.pullback (Out.thick R I k)).map (io.act a)).left, ?_, ?_⟩
    · rw [Over.comp_left, ← h1]
      exact (Category.assoc _ _ _).trans ((congrArg (w ≫ ·) hG).trans (Category.assoc _ _ _).symm)
    · have hB : ((Over.pullback (Out.thick R I k)).map (oD.onB.act a)).left ≫
          (D.toPre.prBe I k).left = (D.toPre.prBe I k).left ≫ (oD.onB.act a).left :=
        GlobalTheory.SplitTorusPoints.map_left_fst (Out.thick R I k) (oD.onB.act a)
      have hq : ((Over.pullback (Out.thick R I k)).map (io.act a)).left ≫ (U.gt k).q.left =
          (U.gt k).q.left ≫ ((Over.pullback (Out.thick R I k)).map (oD.onB.act a)).left :=
        congrArg (·.left) (hl.q_lin k a)
      have hp : ((Over.pullback (Out.thick R I k)).map (io.act a)).left ≫ (U.gt k).pG.left =
          (U.gt k).pG.left ≫ (oD.onB.act a).left :=
        (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (D.toPre.prBe I k).left) hq).trans
          ((Category.assoc _ _ _).trans ((congrArg ((U.gt k).q.left ≫ ·) hB).trans
            (Category.assoc _ _ _).symm)))
      rw [Over.comp_left (g := oD.onB.act a), ← h2]
      exact (Category.assoc _ _ _).trans ((congrArg (w ≫ ·) hp).trans (Category.assoc _ _ _).symm)
  · rintro χ χ' z hχ ⟨w, h1, h2⟩
    obtain ⟨t, ht, hi⟩ := hl.i_lin k a
    refine ⟨w ≫ t.left, fun x => ?_, ?_⟩
    · rw [hχ, ← h1, ← appTop_charUnit_of_torusEndOf ht x, Scheme.Hom.comp_appTop]
      rfl
    · have hi' : (U.gt k).i.left ≫ ((Over.pullback (Out.thick R I k)).map (io.act a)).left =
          t.left ≫ (U.gt k).i.left := congrArg (·.left) hi
      have hp : t.left ≫ (U.gt k).i.left ≫ (Out.fstG I k G).left =
          ((U.gt k).i.left ≫ (Out.fstG I k G).left) ≫ (io.act a).left :=
        (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (Out.fstG I k G).left) hi'.symm).trans
          ((Category.assoc _ _ _).trans ((congrArg ((U.gt k).i.left ≫ ·) hG).trans
            (Category.assoc _ _ _).symm)))
      rw [Over.comp_left, ← h2]
      exact (Category.assoc _ _ _).trans ((congrArg (w ≫ ·) hp).trans (Category.assoc _ _ _).symm)

end GlobalTheory.ChF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ThickeningQuotientImageOneIffExistsTorusImage
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ThickeningQuotientImageOneIffExistsTorusImage
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.ChF

private theorem one_left_fst {S S' Z : Scheme.{0}} (G : Over S) [GrpObj G] (f : S' ⟶ S) {t : Z ⟶ S'} {r : Z ⟶ S}
    (h : t ≫ f = r) :
    (1 : Over.mk t ⟶ (Over.pullback f).obj G).left ≫ pullback.fst G.hom f = (1 : Over.mk r ⟶ G).left := by
  have A : ∀ {X Y : Over S} (a : X ⟶ Y),
      ((Over.pullback f).map a).left ≫ pullback.fst Y.hom f = pullback.fst X.hom f ≫ a.left :=
    fun a => pullback.lift_fst _ _ _
  let z : Over.mk t ⟶ (Over.pullback f).obj (𝟙_ (Over S)) :=
    toUnit _ ≫ Functor.LaxMonoidal.ε (Over.pullback f)
  have h1 : (1 : Over.mk t ⟶ (Over.pullback f).obj G) = z ≫ (Over.pullback f).map η[G] := by
    rw [Hom.one_def, Functor.obj.η_def, ← Category.assoc]
  have h2 : z.left ≫ pullback.fst (𝟙_ (Over S)).hom f = (toUnit (Over.mk r)).left := by
    have a1 : pullback.fst (𝟙_ (Over S)).hom f ≫ (𝟙_ (Over S)).hom = pullback.snd _ f ≫ f := pullback.condition
    have a2 : z.left ≫ pullback.snd (𝟙_ (Over S)).hom f = t := Over.w z
    have a3 : (toUnit (Over.mk r)).left ≫ (𝟙_ (Over S)).hom = r := Over.w _
    have : Mono (𝟙_ (Over S)).hom := inferInstanceAs (Mono (𝟙 S))
    rw [← cancel_mono (𝟙_ (Over S)).hom, a3, Category.assoc, a1, ← Category.assoc, a2, h]
  rw [h1, Over.comp_left, Category.assoc, A, ← Category.assoc, h2, Hom.one_def, Over.comp_left]

private theorem mono_thick (R : Type) [CommRing R] (I : Ideal R) (k : ℕ) : Mono (Out.thick R I k) := by
  have : IsClosedImmersion (Out.thick R I k) := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  infer_instance

theorem qRel_one_iff_exists_iRel : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : Out.DegPre R) (k : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (c : Out.GtCoord I D k G) (S : Type) [CommRing S] [Algebra R S], Kills I k S → ∀ z, QRel c S z 1 ↔ ∃ χ, IRel c S χ z := by
  intro R _ _ I D k G _ _ c S _ _ hS z
  have hm := mono_thick R I k
  have hf : Mono (pullback.fst D.P.A.hom (Out.thick R I k)) := inferInstance
  let t : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (k + 1))) :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift (I ^ (k + 1)) (algebraMap R S) hS))
  have ht : t ≫ Out.thick R I k = Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have hw : ∀ (w : Spec (CommRingCat.of S) ⟶ (Out.thickObj R I k G).left),
      w ≫ (Out.fstG I k G).left = z.left → w ≫ (Out.thickObj R I k G).hom = t := by
    intro w h
    rw [← cancel_mono (Out.thick R I k), ht]
    have h1 : (Out.thickObj R I k G).hom ≫ Out.thick R I k = (Out.fstG I k G).left ≫ G.hom :=
      (pullback.condition (f := G.hom) (g := Out.thick R I k)).symm
    rw [Category.assoc, h1, ← Category.assoc, h]
    exact Over.w z
  have h1 : (1 : Over.mk t ⟶ Out.thickObj R I k D.P.A).left ≫ pullback.fst D.P.A.hom (Out.thick R I k) =
      (1 : sp (R₀ := R) S ⟶ D.P.A).left := one_left_fst D.P.A (Out.thick R I k) ht
  constructor
  · rintro ⟨w, a, b⟩
    let x : Over.mk t ⟶ Out.thickObj R I k G := Over.homMk w (hw w a)
    have hx : x ≫ c.q = toUnit _ ≫ η[Out.thickObj R I k D.P.A] := by
      apply Over.OverMorphism.ext
      refine (cancel_mono (pullback.fst D.P.A.hom (Out.thick R I k))).1 ?_
      exact ((Category.assoc _ _ _).trans b).trans h1.symm
    let u := c.isKernel.lift x (toUnit _) hx
    have hu : u ≫ c.i = x := c.isKernel.lift_fst _ _ _
    refine ⟨(Units.map (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom.toMonoidHom).comp
      (splitTorusPointsEquiv _ D.X (Over.mk t) u), u.left, fun χ => ?_, ?_⟩
    · exact (congrArg (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom
        (splitTorusPointsEquiv_val _ D.X (Over.mk t) u χ)).symm
    · have e : u.left ≫ c.i.left = w := congrArg (·.left) hu
      exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) e)).trans a
  · rintro ⟨χ, w, -, a⟩
    have a' : (w ≫ c.i.left) ≫ (Out.fstG I k G).left = z.left := (Category.assoc _ _ _).trans a
    refine ⟨w ≫ c.i.left, a', ?_⟩
    let u : Over.mk t ⟶ splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (k + 1)))) D.X := Over.homMk w (by
      have := hw _ a'
      rw [Category.assoc, Over.w c.i] at this
      exact this)
    have hu : u ≫ c.i ≫ c.q = 1 := by
      rw [c.isKernel.w, Hom.one_def, ← Category.assoc]
      congr 1
      exact toUnit_unique _ _
    have e : (w ≫ c.i.left) ≫ c.q.left = (1 : Over.mk t ⟶ Out.thickObj R I k D.P.A).left :=
      (Category.assoc _ _ _).trans (congrArg (·.left) hu)
    exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) e)).trans h1

end GlobalTheory.ChF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ThickeningQuotientImageOneIffExistsTorusImageStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thickeningQuotientImage_one_iff_exists_torusImage : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : Out.DegPre R) (k : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (c : Out.GtCoord I D k G) (S : Type) [CommRing S] [Algebra R S], Kills I k S → ∀ z, QRel c S z 1 ↔ ∃ χ, IRel c S χ z := by
  first | exact @GlobalTheory.ChF.qRel_one_iff_exists_iRel | exact GlobalTheory.ChF.qRel_one_iff_exists_iRel | (intros; apply GlobalTheory.ChF.qRel_one_iff_exists_iRel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsStruct
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

section
open scoped CategoryTheory.Obj

private theorem mul_left_fst {S' S : Scheme.{0}} (f : S' ⟶ S) (G : Over S) [GrpObj G] {Y : Over S} {Z : Over S'}
    (e : Y.left ⟶ Z.left) (a b : Z ⟶ (Over.pullback f).obj G) (za zb : Y ⟶ G)
    (ha : e ≫ a.left ≫ pullback.fst G.hom f = za.left) (hb : e ≫ b.left ≫ pullback.fst G.hom f = zb.left) :
    e ≫ (a * b).left ≫ pullback.fst G.hom f = (za * zb).left := by
  let F := Over.pullback f
  let m : Z ⟶ F.obj (G ⊗ G) := lift a b ≫ Functor.LaxMonoidal.μ F G G
  have key : ∀ g : G ⊗ G ⟶ G, (m.left ≫ pullback.fst (G ⊗ G).hom f) ≫ g.left =
      (m ≫ F.map g).left ≫ pullback.fst G.hom f := by
    intro g
    rw [Category.assoc, ← SplitTorusPoints.map_left_fst, Over.comp_left]
    exact (Category.assoc _ _ _).symm
  have h1 : m ≫ F.map (fst G G) = a := (Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (Functor.Monoidal.μ_fst F G G)).trans (lift_fst _ _))
  have h2 : m ≫ F.map (snd G G) = b := (Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (Functor.Monoidal.μ_snd F G G)).trans (lift_snd _ _))
  have h3 : m ≫ F.map μ[G] = a * b := Category.assoc _ _ _
  have hq : e ≫ m.left ≫ pullback.fst (G ⊗ G).hom f = (lift za zb).left := by
    apply pullback.hom_ext
    · have := key (fst G G)
      rw [h1] at this
      exact (Category.assoc _ _ _).trans ((congrArg (e ≫ ·) this).trans (ha.trans
        (congrArg (fun t => t.left) (lift_fst za zb)).symm))
    · have := key (snd G G)
      rw [h2] at this
      exact (Category.assoc _ _ _).trans ((congrArg (e ≫ ·) this).trans (hb.trans
        (congrArg (fun t => t.left) (lift_snd za zb)).symm))
  have := key μ[G]
  rw [h3] at this
  rw [← this, ← Category.assoc, hq]
  rfl

end

private theorem mono_thick {R : Type} [CommRing R] (I : Ideal R) (e : ℕ) : Mono (Out.thick R I e) := by
  have : IsClosedImmersion (Out.thick R I e) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  infer_instance

private theorem exists_struct {R : Type} [CommRing R] (I : Ideal R) (k : ℕ) (S : Type) [CommRing S] [Algebra R S]
    (h : Kills I k S) : ∃ s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (k + 1))),
      s ≫ Out.thick R I k = (sp (R₀ := R) S).hom := by
  refine ⟨Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift _ (algebraMap R S) h)), ?_⟩
  change Spec.map _ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (k + 1)))) = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

private theorem exists_equiv {B : Scheme.{0}} (X : Type) [AddCommGroup X] (S : Type) [CommRing S]
    (s : Spec (CommRingCat.of S) ⟶ B) :
    ∃ e : (Over.mk s ⟶ splitTorus B X) ≃* (Multiplicative X →* Sˣ), ∀ t χ, e t = χ ↔
      ∀ x : X, (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom
        (t.left.appTop.hom (charUnit B X x).val) = (χ (Multiplicative.ofAdd x) : S) := by
  let u : Γ(Spec (CommRingCat.of S), ⊤)ˣ ≃* Sˣ :=
    Units.mapEquiv (Scheme.ΓSpecIso (CommRingCat.of S)).commRingCatIsoToRingEquiv.toMulEquiv
  refine ⟨(splitTorusPointsEquiv B X (Over.mk s)).trans (u.monoidHomCongrRight), fun t χ => ?_⟩
  have hv : ∀ x : X, ((((splitTorusPointsEquiv B X (Over.mk s)).trans (u.monoidHomCongrRight)) t
      (Multiplicative.ofAdd x) : Sˣ) : S) = (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom
        (t.left.appTop.hom (charUnit B X x).val) := fun x =>
    congrArg (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom (splitTorusPointsEquiv_val B X (Over.mk s) t x)
  constructor
  · rintro rfl x
    exact (hv x).symm
  · intro h
    ext x
    exact (hv x).trans (h x)

private theorem irel_iff {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : Out.DegPre R} {k : ℕ}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (c : Out.GtCoord I D k G)
    (S : Type) [CommRing S] [Algebra R S]
    (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (k + 1))))
    (hs : s ≫ Out.thick R I k = (sp (R₀ := R) S).hom) :
    ∃ e : (Over.mk s ⟶ splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (k + 1)))) D.X) ≃* (Multiplicative D.X →* Sˣ),
      ∀ χ z, IRel c S χ z ↔ (e.symm χ ≫ c.i).left ≫ pullback.fst G.hom (Out.thick R I k) = z.left := by
  obtain ⟨e, he⟩ := exists_equiv D.X S s
  refine ⟨e, fun χ z => ⟨?_, fun h => ?_⟩⟩
  · rintro ⟨w, hw, hz⟩
    have := mono_thick I k
    have hws : w ≫ (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (k + 1)))) D.X).hom = s := by
      rw [← cancel_mono (Out.thick R I k), hs, ← Over.w z, ← hz, ← Over.w c.i]
      simp only [Category.assoc]
      exact congrArg (fun g => w ≫ c.i.left ≫ g) (Over.w (Out.fstG I k G)).symm
    let t : Over.mk s ⟶ splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (k + 1)))) D.X := Over.homMk w hws
    have ht : e t = χ := (he t χ).2 hw
    rw [← ht, MulEquiv.symm_apply_apply]
    exact (Category.assoc _ _ _).trans hz
  · exact ⟨(e.symm χ).left, (he _ χ).1 (e.apply_symm_apply χ), (Category.assoc _ _ _).symm.trans h⟩


open scoped CategoryTheory.Obj in
theorem irel_points : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : Out.DegPre R) (k : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (c : Out.GtCoord I D k G), (∀ (S : Type) [CommRing S] [Algebra R S], Kills I k S → (∀ χ, ∃! z, IRel c S χ z) ∧ (∀ χ χ' z z', IRel c S χ z → IRel c S χ' z' → IRel c S (χ * χ') (z * z')) ∧ ∀ χ χ' z, IRel c S χ z → IRel c S χ' z → χ = χ') ∧ ∀ (S : Type) [CommRing S] [Algebra R S] (S' : Type) [CommRing S'] [Algebra R S'] (φ : S →ₐ[R] S') χ z, IRel c S χ z → IRel c S' ((Units.map (φ : S →* S')).comp χ) (spMap φ ≫ z) := by
  intro R _ _ I D k G _ _ c
  refine ⟨fun S _ _ hS => ?_, ?_⟩
  · obtain ⟨s, hs⟩ := exists_struct I k S hS
    obtain ⟨e, he⟩ := irel_iff c S s hs
    refine ⟨fun χ => ?_, fun χ χ' z z' h h' => ?_, fun χ χ' z h h' => ?_⟩
    · refine ⟨Over.homMk ((e.symm χ ≫ c.i).left ≫ pullback.fst G.hom (Out.thick R I k)) ?_,
        (he _ _).2 rfl, fun z hz => Over.OverMorphism.ext ((he _ _).1 hz).symm⟩
      rw [← hs]
      exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) pullback.condition).trans
        ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ Out.thick R I k) (Over.w (e.symm χ ≫ c.i)))))
    · rw [he] at h h' ⊢
      have := c.i_hom
      rw [map_mul, MonObj.mul_comp]
      exact (Category.id_comp _).symm.trans (mul_left_fst (Out.thick R I k) G (Y := sp S) (Z := Over.mk s) (𝟙 _)
        _ _ z z' ((Category.id_comp _).trans h) ((Category.id_comp _).trans h'))
    · rw [he] at h h'
      have := mono_thick I k
      have h1 : e.symm χ ≫ c.i = e.symm χ' ≫ c.i :=
        Over.OverMorphism.ext ((cancel_mono (pullback.fst G.hom (Out.thick R I k))).1 (h.trans h'.symm))
      exact e.symm.injective (c.isKernel.hom_ext h1 (toUnit_unique _ _))
  · rintro S _ _ S' _ _ φ χ z ⟨w, hw, hz⟩
    refine ⟨Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ w, fun x => ?_, ?_⟩
    · rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, ← RingHom.comp_apply,
        ← CommRingCat.hom_comp, Scheme.ΓSpecIso_naturality, CommRingCat.hom_comp, RingHom.comp_apply, hw]
      rfl
    · rw [Category.assoc, hz]
      rfl

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsTorusExtensionPointsOfUniformisation
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem kills_mono {R : Type} [CommRing R] {I : Ideal R} {k l : ℕ} (hkl : k ≤ l) {S : Type} [CommRing S]
    [Algebra R S] (h : Kills I k S) : Kills I l S :=
  fun t ht => h t (Ideal.pow_le_pow_right (by omega) ht)

section
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : Out.DegData R I}
  {A : Out.PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  [IsCommMonObj G] (U : Out.UnifPre I D A G) (S : Type) [CommRing S] [Algebra R S]

private theorem qRel_mono {k l : ℕ} (hkl : k ≤ l) {z y} (h : QRel (U.gt k) S z y) : QRel (U.gt l) S z y := by
  induction l, hkl using Nat.le_induction with
  | base => exact h
  | succ n _ ih => exact GlobalTheory.ChF.qRel_succ R I D A G U n S z y ih

private theorem iRel_mono {k l : ℕ} (hkl : k ≤ l) {χ z} (h : IRel (U.gt k) S χ z) : IRel (U.gt l) S χ z := by
  induction l, hkl using Nat.le_induction with
  | base => exact h
  | succ n _ ih => exact GlobalTheory.T.torus_point_relation_succ_thickening R I D A G U n S χ z ih

private def qFun (h : ∃ k, Kills I k S) (z : sp (R₀ := R) S ⟶ G) : sp (R₀ := R) S ⟶ D.toPre.P.A :=
  (((qRel_existsUnique_mul_nat R I _ h.choose G (U.gt h.choose)).1 S h.choose_spec).1 z).exists.choose

private theorem qFun_spec (h : ∃ k, Kills I k S) (z : sp (R₀ := R) S ⟶ G) :
    QRel (U.gt h.choose) S z (qFun U S h z) :=
  (((qRel_existsUnique_mul_nat R I _ h.choose G (U.gt h.choose)).1 S h.choose_spec).1 z).exists.choose_spec

private theorem qFun_eq (h : ∃ k, Kills I k S) {k : ℕ} {z y} (hq : QRel (U.gt k) S z y) : qFun U S h z = y :=
  (((qRel_existsUnique_mul_nat R I _ _ G (U.gt (max h.choose k))).1 S
    (kills_mono (le_max_left _ _) h.choose_spec)).1 z).unique
    (qRel_mono U S (le_max_left _ _) (qFun_spec U S h z)) (qRel_mono U S (le_max_right _ _) hq)

private def iFun (h : ∃ k, Kills I k S) (χ : Multiplicative D.toPre.X →* Sˣ) : sp (R₀ := R) S ⟶ G :=
  (((GlobalTheory.irel_points R I _ h.choose G (U.gt h.choose)).1 S h.choose_spec).1 χ).exists.choose

private theorem iFun_spec (h : ∃ k, Kills I k S) (χ : Multiplicative D.toPre.X →* Sˣ) :
    IRel (U.gt h.choose) S χ (iFun U S h χ) :=
  (((GlobalTheory.irel_points R I _ h.choose G (U.gt h.choose)).1 S h.choose_spec).1 χ).exists.choose_spec

private theorem iFun_eq (h : ∃ k, Kills I k S) {k : ℕ} {χ z} (hq : IRel (U.gt k) S χ z) : iFun U S h χ = z :=
  (((GlobalTheory.irel_points R I _ _ G (U.gt (max h.choose k))).1 S
    (kills_mono (le_max_left _ _) h.choose_spec)).1 χ).unique
    (iRel_mono U S (le_max_left _ _) (iFun_spec U S h χ)) (iRel_mono U S (le_max_right _ _) hq)

end

private def ptExt {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : Out.DegData R I}
    {A : Out.PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    [IsCommMonObj G] (U : Out.UnifPre I D A G) : PtExt I G D.toPre.P.A D.toPre.X where
  q S _ _ h := MonoidHom.mk' (qFun U S h) fun z z' => qFun_eq U S h
    (((qRel_existsUnique_mul_nat R I _ h.choose G (U.gt h.choose)).1 S h.choose_spec).2 _ _ _ _
      (qFun_spec U S h z) (qFun_spec U S h z'))
  i S _ _ h := MonoidHom.mk' (iFun U S h) fun χ χ' => iFun_eq U S h
    (((GlobalTheory.irel_points R I _ h.choose G (U.gt h.choose)).1 S h.choose_spec).2.1 _ _ _ _
      (iFun_spec U S h χ) (iFun_spec U S h χ'))
  q_nat S _ _ S' _ _ φ h h' z := qFun_eq U S' h'
    ((qRel_existsUnique_mul_nat R I _ h.choose G (U.gt h.choose)).2 S S' φ _ _ (qFun_spec U S h z))
  i_nat S _ _ S' _ _ φ h h' χ := iFun_eq U S' h'
    ((GlobalTheory.irel_points R I _ h.choose G (U.gt h.choose)).2 S S' φ _ _ (iFun_spec U S h χ))
  i_inj S _ _ h χ χ' e := by
    have e' : iFun U S h χ = iFun U S h χ' := e
    exact ((GlobalTheory.irel_points R I _ h.choose G (U.gt h.choose)).1 S h.choose_spec).2.2 _ _ _
      (iFun_spec U S h χ) (e' ▸ iFun_spec U S h χ')
  exact S _ _ h z := by
    have key := GlobalTheory.T.thickeningQuotientImage_one_iff_exists_torusImage R I _ h.choose G (U.gt h.choose) S h.choose_spec z
    constructor
    · intro e
      have e' : qFun U S h z = 1 := e
      obtain ⟨χ, hχ⟩ := key.1 (e' ▸ qFun_spec U S h z)
      exact ⟨χ, iFun_eq U S h hχ⟩
    · rintro ⟨χ, e⟩
      have e' : iFun U S h χ = z := e
      exact qFun_eq U S h (key.2 ⟨χ, e' ▸ iFun_spec U S h χ⟩)
  lift S _ _ h S' _ _ ρ σ h1 h2 y hy := by
    obtain ⟨z, hz, hq⟩ := GlobalTheory.T.abelianPart_lift_square_zero_unit_point R I _ h.choose G (U.gt h.choose) S h.choose_spec S' ρ σ h1 h2 y hy
    exact ⟨z, hz, qFun_eq U S h hq⟩

theorem exists_ptExt_of_unif : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : Out.DegData R I) (A : Out.PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : Out.UnifPre I D A G), ∃ E : PtExt I G D.toPre.P.A D.toPre.X, ∀ (OE : Type) [CommRing OE] [StarRing OE] [Module OE D.toPre.X] (io : Out.RingAct G OE) (oD : D.OAct OE) (oA : A.OAct OE), U.OLinear OE oD oA io → ∀ (a : OE) (S : Type) [CommRing S] [Algebra R S] (h : ∃ k, Kills I k S), (∀ z, E.q S h (z ≫ io.act a) = E.q S h z ≫ oD.onB.act a) ∧ ∀ χ χ', (∀ x, χ' (Multiplicative.ofAdd x) = χ (Multiplicative.ofAdd (star a • x))) → E.i S h χ ≫ io.act a = E.i S h χ' := by
  intro R _ _ I D A G _ _ U
  refine ⟨ptExt U, ?_⟩
  intro OE _ _ _ io oD oA hL a S _ _ h
  have key := qRel_iRel_equivariant R I D A G U OE io oD oA hL h.choose a S
  refine ⟨fun z => qFun_eq U S h (key.1 _ _ (qFun_spec U S h z)), fun χ χ' e => ?_⟩
  exact (iFun_eq U S h (key.2 _ _ _ e (iFun_spec U S h χ))).symm

end GlobalTheory.ChF
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsTorusExtensionPointsOfUniformisationStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torus_extension_points_of_uniformisation : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : Out.DegData R I) (A : Out.PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : Out.UnifPre I D A G), ∃ E : PtExt I G D.toPre.P.A D.toPre.X, ∀ (OE : Type) [CommRing OE] [StarRing OE] [Module OE D.toPre.X] (io : Out.RingAct G OE) (oD : D.OAct OE) (oA : A.OAct OE), U.OLinear OE oD oA io → ∀ (a : OE) (S : Type) [CommRing S] [Algebra R S] (h : ∃ k, Kills I k S), (∀ z, E.q S h (z ≫ io.act a) = E.q S h z ≫ oD.onB.act a) ∧ ∀ χ χ', (∀ x, χ' (Multiplicative.ofAdd x) = χ (Multiplicative.ofAdd (star a • x))) → E.i S h χ ≫ io.act a = E.i S h χ' := by
  first | exact @GlobalTheory.ChF.exists_ptExt_of_unif | exact GlobalTheory.ChF.exists_ptExt_of_unif | (intros; apply GlobalTheory.ChF.exists_ptExt_of_unif <;> assumption)
end
