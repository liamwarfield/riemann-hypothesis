module

public import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefPullLLStepEx
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomExtOfAgreeOnFibreDenseOpenSmooth

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionSmoothAffineSurjectiveFourierTerms
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionSmoothAffineSurjectiveFourierTerms
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum.Ext

open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht GlobalTheory.TorusModel GlobalTheory.TorusExt GlobalTheory.Serre GlobalTheory.RayEv _root_.Formalism.L2.Pj

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} (Y : Ext D)

theorem Φ_b {T : Over (Sp R)} (x : T ⟶ Y.H) : (Y.Φ T x).b = x ≫ Y.q := by
  have h := ((isPull_iff _ _ _).1 (Y.rep.1 T Y.H x (𝟙 _))).1
  rwa [Category.comp_id] at h

theorem isMonHom_q : IsMonHom Y.q :=
  isMonHom_of_mul _ fun T x x' => by
    rw [← Φ_b, ← Φ_b, ← Φ_b]; exact ((TorusModel.isAdd_iff _ _ _).1 (Y.rep.2 T x x')).1

theorem exists_q_eq (c : GtCoord (⊥ : Ideal R) D 0 Y.H) : ∃ a : Y.H.left ⟶ (thickObj R ⊥ 0 Y.H).left, IsIso a ∧
    Y.q.left = a ≫ c.q.left ≫ pullback.fst D.P.A.hom (thick R ⊥ 0) := by
  let F := fstG (⊥ : Ideal R) 0 Y.H
  let j := inv F.left
  have hF : F.left ≫ Y.H.hom = (thickObj R ⊥ 0 Y.H).hom ≫ thick R ⊥ 0 := Over.w F
  let ξ := Y.Φ Y.H (𝟙 _)
  obtain ⟨x, hx⟩ := GlobalTheory.TorusCoord.exists_point c (T := Y.H) (Y.H.hom ≫ inv (thick R ⊥ 0)) (by simp) ξ
  obtain ⟨ξ', hξ'⟩ := GlobalTheory.TorusCoord.exists_isPointOf c (T := Y.H) j (by
    rw [← hF]; exact IsIso.inv_hom_id_assoc _ _)
  let b : Y.H ⟶ Y.H := (Y.Φ Y.H).symm ξ'
  have hb : Y.Φ Y.H b = ξ' := Equiv.apply_symm_apply _ _
  let a := x ≫ F.left
  have ha : a ≫ Y.H.hom = Y.H.hom := by
    rw [Category.assoc, hF]
    exact GlobalTheory.TorusCoord.IsPointOf.comp_hom c hx
  let a' : Y.H ⟶ Y.H := Over.homMk a ha
  have haj : a ≫ j = x := by simp [a, j]
  have e1 : b.left ≫ x = j := by
    have h1 : GtPt.IsPull b.left ξ (Y.Φ Y.H (b ≫ 𝟙 _)) := Y.rep.1 Y.H Y.H b (𝟙 _)
    rw [Category.comp_id, hb] at h1
    exact (GlobalTheory.TorusCoord.IsPointOf.pull c hx h1).unique_left c hξ'
  have e1' : b.left ≫ a = 𝟙 _ := by
    rw [← Category.assoc, e1]; simp [j]
  have e2 : a' ≫ b = 𝟙 _ := by
    have h2 : GtPt.IsPull a (Y.Φ Y.H b) (Y.Φ Y.H (a' ≫ b)) := Y.rep.1 Y.H Y.H a' b
    rw [hb] at h2
    have h3 := GlobalTheory.TorusCoord.IsPointOf.pull c hξ' h2
    rw [haj] at h3
    exact (Y.Φ Y.H).injective (h3.unique_right c hx)
  have e2' : a ≫ b.left = 𝟙 _ := congrArg (·.left) e2
  have : IsIso a := ⟨⟨b.left, e2', e1'⟩⟩
  refine ⟨a ≫ j, inferInstance, ?_⟩
  rw [haj, ← GlobalTheory.TorusCoord.pG_left]
  exact hx.1

theorem q_props : Smooth Y.q.left ∧ IsAffineHom Y.q.left ∧ Surjective Y.q.left := by
  obtain ⟨c⟩ := GlobalTheory.TorusModel.nonempty_gtCoord GlobalTheory.allSixLaws.1.globalFns Y.isGt ⊥ 0
  have := smooth_gtCoord_q c
  have := c.q_surj
  have := c.q_affine
  obtain ⟨a, _, h⟩ := Y.exists_q_eq c
  rw [h]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

theorem formEq_term (k : ℕ) (α : D.X) :
    FormEq (Sum.elim (fun i => Y.q.left ≫ DegPre.famφB D α i) (DegPre.gtφT D Y.H Y.q α))
      (Sum.elim (DegPre.famε k) DegPre.gtε) (K' := Fin 1) (fun _ => Y.q.left) (fun _ => (k : ℤ)) := by
  have e1 : Y.q ≫ padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c α) = padd D.P.A (DegPre.cT D Y.H α) Y.q := by
    simp only [padd, comp_lift_assoc, Category.comp_id]
    rw [← Hom.mul_def, ← Hom.mul_def, mul_comm, comp_toUnit_assoc]
  have e2 : Y.q.left ≫ (toUnit D.P.A ≫ D.c α).left = (DegPre.cT D Y.H α).left := by
    rw [← Over.comp_left, comp_toUnit_assoc]
  have e3 : Y.q.left ≫ (toUnit D.P.A ≫ η[D.P.A]).left = (DegPre.zeroT D Y.H).left := by
    rw [← Over.comp_left, comp_toUnit_assoc]
  have e0 : Y.q.left ≫ (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c α)).left =
      (padd D.P.A (DegPre.cT D Y.H α) Y.q).left := by
    rw [← Over.comp_left, e1]
  intro U _ h
  rw [Fintype.prod_sum_type, Fin.prod_univ_four, Fin.prod_univ_four, Fin.prod_univ_one]
  simp only [Sum.elim_inl, Sum.elim_inr]
  simp only [DegPre.famφB, DegPre.famε, DegPre.gtφT, DegPre.gtε, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Category.comp_id, e0, e2, e3]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow]
  module

theorem exists_isTermOf (k : ℕ) (α : D.X) (σ : D.SecB k α) : ∃ τ : SecK D.P.L Y.q.left k, IsTermOf Y σ τ := by
  obtain ⟨τ, hτ⟩ := exists_sec D.P.isLB (Y.formEq_term k α)
    (pullMulSec σ Y.q.left ((Y.Φ Y.H (𝟙 _)).s α) ((Y.Φ Y.H (𝟙 _)).isGen α))
  refine ⟨τ, fun T x y J hJ => ?_⟩
  refine (hτ _ _ y J hJ).trans ((sval_pullMulSec σ Y.q.left ((Y.Φ Y.H (𝟙 _)).s α) ((Y.Φ Y.H (𝟙 _)).isGen α)
    x.left y hJ).trans ?_)
  obtain ⟨-, h₂⟩ := (isPull_iff _ _ _).1 (Y.rep.1 T Y.H x (𝟙 _))
  have e := h₂ α y J hJ
  rw [Category.comp_id] at e
  rw [Over.comp_left]
  exact congrArg _ (congrArg Units.val e.symm)

end GlobalTheory.Mum.Ext

namespace GlobalTheory.Mum

theorem ext_smooth_affine_surj_terms (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (Y : Ext D) :
    Smooth Y.H.hom ∧ IsAffineHom Y.q.left ∧ Surjective Y.q.left ∧ IsMonHom Y.q ∧
      ∀ (k : ℕ) (α : D.X) (b : D.SecB k α), ∃ τ : SecK D.P.L Y.q.left k, IsTermOf Y b τ := by
  obtain ⟨h1, h2, h3⟩ := Y.q_props
  refine ⟨?_, h2, h3, Y.isMonHom_q, Y.exists_isTermOf⟩
  have : Smooth D.P.A.hom := D.P.isAb.smooth
  rw [← Over.w Y.q]
  infer_instance

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionSmoothAffineSurjectiveFourierTermsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusExtension_smooth_affine_surjective_fourierTerms : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (Y : Ext D), Smooth Y.H.hom ∧ IsAffineHom Y.q.left ∧ Surjective Y.q.left ∧ IsMonHom Y.q ∧ ∀ (k : ℕ) (α : D.X) (b : D.SecB k α), ∃ τ : SecK D.P.L Y.q.left k, IsTermOf Y b τ := by
  first | exact @GlobalTheory.Mum.ext_smooth_affine_surj_terms | exact GlobalTheory.Mum.ext_smooth_affine_surj_terms | (intros; apply GlobalTheory.Mum.ext_smooth_affine_surj_terms <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordMapOfIsPullDeg
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.Eq8.PullUnif

theorem coordMap_of_isPullDeg {R V : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing V] [IsDomain V]
    [IsLocalRing V] {g : R →+* V} {D : DegPre R} {D' : DegPre V} (hD : IsPullDeg g D D') :
    CoordMap D D' g hD.xe.symm.toAddMonoidHom := by
  intro y r r' hr hr'
  have hr2 : PsiCoord D (hD.xe (hD.xe.symm y)) r := by rwa [AddEquiv.apply_symm_apply]
  obtain ⟨u, hu⟩ := GlobalTheory.PelCoordPull.psiCoord_pull hD (hD.xe.symm y) r hr2
  have h1 : Associated (u * g r) r' := GlobalTheory.TorRef.psiCoord_associated hu hr'
  exact Associated.trans ⟨u, mul_comm _ _⟩ h1


set_option maxHeartbeats 1600000 in
theorem gtTorus_pull {R V : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    [CommRing V] [IsDomain V] [IsLocalRing V] {D' : DegData V (maximalIdeal V)}
    {A' : PolAV (Sp (FractionRing V))} {G' : Over (Sp V)} [GrpObj G'] [IsCommMonObj G']
    {U : Unif (maximalIdeal R) D A G} {U' : Unif (maximalIdeal V) D' A' G'} {g : R →+* V}
    {bc : G' ≅ (Over.pullback (specOf g)).obj G} {hD : IsPullDeg g D.toPre D'.toPre}
    (H : IsPullUnif g hD bc U U')
    {κ : Type} [Field κ] {b : V →+* κ} (hb : ∀ x ∈ maximalIdeal V ^ (0 + 1), b x = 0)
    (hb' : ∀ x ∈ maximalIdeal R ^ (0 + 1), (b.comp g) x = 0)
    {G₀ : Over (Sp κ)} [GrpObj G₀] {φ' : G₀.left ⟶ G'.left}
    (hp' : IsGrpPullback G₀ G' (spMap b) φ')
    (hp : IsGrpPullback G₀ G (spMap (b.comp g)) (φ' ≫ bc.hom.left ≫ pullback.fst G.hom (specOf g))) :
    GlobalTheory.TorusPart.gtTorus (U'.gt 0) hb hp' =
      GlobalTheory.SplitTorus.torusMap (Sp κ) hD.xe.symm.toAddMonoidHom ≫ GlobalTheory.TorusPart.gtTorus (U.gt 0) hb' hp := by
  obtain ⟨wL, -, he, -, Hs⟩ := (isPullUnif_iff_stalks R V _ _ g D D' hD A A' G G' bc U U').1 H
  obtain ⟨h, hf, ⟨hpG, hψ⟩, -⟩ := Hs 0
  obtain ⟨s, τ, hτ⟩ := GlobalTheory.PullLinear.exists_point (U.gt 0) (U'.gt 0) hpG (hψ 0).1 (𝟙 _)
  have : IsClosedImmersion (thick R (maximalIdeal R) 0) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have C1 : GlobalTheory.TorusPart.thickLift hb' hp = GlobalTheory.TorusPart.thickLift hb hp' ≫ h := by
    rw [← cancel_mono (pullback.fst G.hom (thick R (maximalIdeal R) 0)), GlobalTheory.TorusPart.thickLift_fst,
      Category.assoc]
    erw [hf]
    erw [← Category.assoc (GlobalTheory.TorusPart.thickLift hb hp'), GlobalTheory.TorusPart.thickLift_fst hb hp']
  have hτ' : (U'.gt 0).i.left ≫ h = τ.left ≫ (U.gt 0).i.left := by
    rw [← Over.comp_left, hτ, Category.id_comp]
  have key : GlobalTheory.SplitTorus.bcMap (GlobalTheory.TorusPart.thickPt 0 hb) D'.toPre.X ≫ τ.left =
      (GlobalTheory.SplitTorus.torusMap (Sp κ) hD.xe.symm.toAddMonoidHom).left ≫
        GlobalTheory.SplitTorus.bcMap (GlobalTheory.TorusPart.thickPt 0 hb') D.toPre.X := by
    have wA : (GlobalTheory.SplitTorus.bcMap (GlobalTheory.TorusPart.thickPt 0 hb) D'.toPre.X ≫ τ.left) ≫
        (splitTorus (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (0 + 1)))) D.toPre.X).hom =
        (splitTorus (Sp κ) D'.toPre.X).hom ≫ GlobalTheory.TorusPart.thickPt 0 hb' := by
      rw [Category.assoc, ← Over.w (U.gt 0).i, ← Category.assoc τ.left, ← hτ', Category.assoc,
        ← Category.assoc _ (U'.gt 0).i.left]
      erw [← GlobalTheory.TorusPart.pullTorus_left (GlobalTheory.TorusPart.isGrpPullback_thickLift hb hp') (U'.gt 0).i]
      rw [Category.assoc, ← Category.assoc _ h, ← C1, (GlobalTheory.TorusPart.isGrpPullback_thickLift hb' hp).1.w,
        ← Category.assoc, Over.w]
    have wB : ((GlobalTheory.SplitTorus.torusMap (Sp κ) hD.xe.symm.toAddMonoidHom).left ≫
        GlobalTheory.SplitTorus.bcMap (GlobalTheory.TorusPart.thickPt 0 hb') D.toPre.X) ≫
        (splitTorus (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (0 + 1)))) D.toPre.X).hom =
        (splitTorus (Sp κ) D'.toPre.X).hom ≫ GlobalTheory.TorusPart.thickPt 0 hb' := by
      rw [Category.assoc, GlobalTheory.SplitTorus.bcMap_hom, ← Category.assoc, Over.w]
    have hchar : ∀ x' : D'.toPre.X, τ.left.appTop.hom (Rosenlicht.chi D.toPre.X (hD.xe x')) =
        Rosenlicht.chi D'.toPre.X x' := by
      intro x'
      apply TopCat.Presheaf.section_ext (splitTorus _ D'.toPre.X).left.sheaf ⊤
      intro z hz
      have e := congrArg Units.val
        (GlobalTheory.PullLinear.char_eq (U.gt 0) (U'.gt 0) hD.w (hψ x').1 (hψ x').2 (𝟙 _) τ hτ z)
      rw [gm_val τ.left z ⊤ trivial, gm_val (Over.Hom.left (𝟙 (WeightPf.Te D'.toPre (maximalIdeal V) 0))) z ⊤ trivial, GlobalTheory.SplitTorus.charUnit_val,
        GlobalTheory.SplitTorus.charUnit_val] at e
      exact e
    have e := GlobalTheory.SplitTorus.hom_ext (T := Over.mk ((splitTorus (Sp κ) D'.toPre.X).hom ≫ GlobalTheory.TorusPart.thickPt 0 hb'))
      (g := Over.homMk _ wA) (g' := Over.homMk _ wB) (fun a => by
        rw [GlobalTheory.SplitTorus.val_eq, GlobalTheory.SplitTorus.val_eq]
        simp only [Over.homMk_left, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
        rw [GlobalTheory.SplitTorus.bcMap_appTop_chi, GlobalTheory.SplitTorus.torusMap_appTop_chi,
          ← AddEquiv.apply_symm_apply hD.xe a, hchar, GlobalTheory.SplitTorus.bcMap_appTop_chi,
          AddEquiv.apply_symm_apply]
        rfl)
    exact congrArg (·.left) e
  apply GlobalTheory.TorusPart.hom_ext_of_pullback (GlobalTheory.TorusPart.isGrpPullback_thickLift hb' hp)
  rw [Over.comp_left, Category.assoc]
  erw [GlobalTheory.TorusPart.pullTorus_left (GlobalTheory.TorusPart.isGrpPullback_thickLift hb' hp) (U.gt 0).i]
  rw [C1, ← Category.assoc]
  erw [GlobalTheory.TorusPart.pullTorus_left (GlobalTheory.TorusPart.isGrpPullback_thickLift hb hp') (U'.gt 0).i]
  rw [Category.assoc, hτ', ← Category.assoc, key, Category.assoc]


set_option maxHeartbeats 800000 in
theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (U' : Unif (maximalIdeal V) D' A' G') (g : R →+* V) (β : G'.left ⟶ G.left), IsLocalHom g → ∀ (bc : G' ≅ (Over.pullback (specOf g)).obj G), IsMonHom bc.hom → β = bc.hom.left ≫ pullback.fst G.hom (specOf g) → ∀ hD : IsPullDeg g D.toPre D'.toPre, IsPullUnif g hD bc U U' → LBIso U'.LG.L (U.LG.L.pull β) ∧ CoordMap D.toPre D'.toPre g hD.xe.symm.toAddMonoidHom ∧ EquivMap U U' β hD.xe.symm.toAddMonoidHom := by
  intro R _ _ _ _ G _ _ _ D A U V _ _ _ _ G' _ _ _ D' A' U' g β hloc bc hbc hβ hD H
  subst hβ
  refine ⟨?_, coordMap_of_isPullDeg hD, ?_⟩
  · obtain ⟨wL, hwL, -⟩ := H.lg
    exact ⟨wL, hwL⟩
  intro f f' _ _ hcomm m m' hm hm' y
  have hb : ∀ x ∈ maximalIdeal V ^ (0 + 1), residue V x = 0 := fun x hx =>
    (residue_eq_zero_iff x).2 (Ideal.pow_le_self (Nat.succ_ne_zero 0) hx)
  have hb' : ∀ x ∈ maximalIdeal R ^ (0 + 1), ((residue V).comp g) x = 0 := fun x hx =>
    (residue_eq_zero_iff _).2 ((map_mem_nonunits_iff g x).2 (Ideal.pow_le_self (Nat.succ_ne_zero 0) hx))
  have hp' := isGrpPullback_pullback G' (spMap (residue V))
  have hβ : IsGrpPullback G' G (spMap g) (bc.hom.left ≫ pullback.fst G.hom (specOf g)) :=
    ((isGrpPullback_of_iso bc).comp (isGrpPullback_pullback G (specOf g))).congr (Category.id_comp _) rfl
  have hp : IsGrpPullback ((Over.pullback (spMap (residue V))).obj G') G (spMap ((residue V).comp g))
      (pullback.fst G'.hom (spMap (residue V)) ≫ bc.hom.left ≫ pullback.fst G.hom (specOf g)) :=
    (hp'.comp hβ).congr (Spec.map_comp (CommRingCat.ofHom g) (CommRingCat.ofHom (residue V))).symm rfl
  have e' : ((Over.pullback (spMap (residue V))).map f').left ≫ pullback.fst G'.hom (spMap (residue V)) =
      pullback.fst G'.hom (spMap (residue V)) ≫ f'.left := pullback.lift_fst _ _ _
  have e : ((Over.pullback (spMap (residue V))).map f').left ≫
      (pullback.fst G'.hom (spMap (residue V)) ≫ bc.hom.left ≫ pullback.fst G.hom (specOf g)) =
      (pullback.fst G'.hom (spMap (residue V)) ≫ bc.hom.left ≫ pullback.fst G.hom (specOf g)) ≫ f.left := by
    rw [← Category.assoc, e', Category.assoc, hcomm]
    simp only [Category.assoc]
  have k' := hm' _ _ hb _ _ hp' _ e'
  have k := hm _ _ hb' _ _ hp _ e
  have K := gtTorus_pull H hb hb' hp' hp
  have hmono := (GlobalTheory.TorusPart.mono_gtTorus_and_factor (U.gt 0) hb' hp).1
  have k2 := (Category.assoc _ _ _).trans ((congrArg (GlobalTheory.SplitTorus.torusMap (Sp (ResidueField V))
    hD.xe.symm.toAddMonoidHom ≫ ·) k.symm).trans ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ (Over.pullback (spMap (residue V))).map f') K.symm).trans (k'.trans
    ((congrArg (GlobalTheory.SplitTorus.torusMap (Sp (ResidueField V)) m' ≫ ·) K).trans (Category.assoc _ _ _).symm)))))
  have k3 := (cancel_mono _).1 k2
  rw [← GlobalTheory.SplitTorus.torusMap_comp, ← GlobalTheory.SplitTorus.torusMap_comp] at k3
  exact congrArg (fun φ : D.toPre.X →+ D'.toPre.X => φ y) (GlobalTheory.SplitTorus.torusMap_injective k3)

end GlobalTheory.Poinc.Eq8.PullUnif
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndDataOfAdj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

noncomputable section

namespace GlobalTheory.MumFam.AdjEnd

section Iso

variable {X Y : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
  {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}

theorem wchart_le (j : K' ⊕ K → L.ι) :
    LB.wchart L (Sum.elim φ' φ) j ≤ LB.wchart L φ' (j ∘ Sum.inl) ⊓ LB.wchart L φ (j ∘ Sum.inr) := fun _ hy =>
  ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inl k), Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inr k)⟩

def isoGen (w : LB.Iso (LB.LinComb L φ ε) (LB.LinComb L φ' ε')) :
    LB.Gen (LB.LinComb L (Sum.elim φ' φ) (Sum.elim ε' (fun k => - ε k))) :=
  ⟨fun j => res (wchart_le j) (w.s (j ∘ Sum.inl, j ∘ Sum.inr))⟩

theorem isoGen_isGen {w : LB.Iso (LB.LinComb L φ ε) (LB.LinComb L φ' ε')} (hw : w.IsGen) : (isoGen w).IsGen := by
  intro p q
  refine unit_ext fun y hy => ?_
  have le := fun j : K' ⊕ K → L.ι => (wchart_le (φ := φ) (φ' := φ') j)
  have hm : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L φ' (p ∘ Sum.inl) ⊓ LB.wchart L φ (p ∘ Sum.inr) ⊓
      (LB.wchart L φ' (q ∘ Sum.inl) ⊓ LB.wchart L φ (q ∘ Sum.inr)) := ⟨le p hy.1, le q hy.2⟩
  have e := congrArg (gm (𝟙 Y) y (LB.wchart L φ' (p ∘ Sum.inl) ⊓ LB.wchart L φ (p ∘ Sum.inr) ⊓
      (LB.wchart L φ' (q ∘ Sum.inl) ⊓ LB.wchart L φ (q ∘ Sum.inr))))
    (hw (p ∘ Sum.inl, p ∘ Sum.inr) (q ∘ Sum.inl, q ∘ Sum.inr))
  have e' := (gm_res (𝟙 Y) y _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_div (LB.LinComb L φ ε) (LB.LinComb L φ' ε') (𝟙 Y) y (p ∘ Sum.inl, p ∘ Sum.inr) (q ∘ Sum.inl, q ∘ Sum.inr) hm)
    (gm_res (𝟙 Y) y _ hm _))))
  refine ((gm_res (𝟙 Y) y _ hy _).trans (gm_res (𝟙 Y) y (le p) hy.1 _)).trans (e'.trans (Eq.symm ?_))
  refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_linComb L _ _ (𝟙 Y) y p q hy.1 hy.2).trans ?_)
    ((gm_res (𝟙 Y) y _ hy _).trans (gm_res (𝟙 Y) y (le q) hy.2 _)))
  refine (Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) (gm_linComb L φ' ε' (𝟙 Y) y _ _ hm.1.1 hm.2.1).symm ?_)
  refine Eq.trans ?_ (congrArg (·⁻¹) (gm_linComb L φ ε (𝟙 Y) y _ _ hm.1.2 hm.2.2).symm)
  simp only [Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, Function.comp_apply]
  rfl

theorem val_isoGen (w : LB.Iso (LB.LinComb L φ ε) (LB.LinComb L φ' ε')) {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z)
    {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    val (isoGen w) r z J = gm r z _ (w.s (fun k => J (r ≫ φ' k), fun k => J (r ≫ φ k))) :=
  gm_res r z _ (hJ.mem _ r) _

end Iso

end GlobalTheory.MumFam.AdjEnd

namespace GlobalTheory.MumFam.AdjEnd

theorem endData_of_adj : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), Adj (pol D) (pol D) a a' h h' → EndData D.toPre a a' h h' := by
  intro R _ _ _ _ D a a' h h' H
  obtain ⟨ha, ha', hc, hc', w, hw, hτ⟩ := H
  have hL := D.toPre.P.isLB
  let B := D.toPre.P.A
  let t := isoGen w
  have ht : t.IsGen := isoGen_isGen hw
  let ℓ : (B ⊗ B).left ⟶ (B ⊗ B).left := (lift (1 : B ⊗ B ⟶ B) 1).left
  let v := LB.mulGen _ _ _ _ _ (LB.invGen _ _ _ t) (LB.pullGen _ _ _ t ℓ)
  have hv : v.IsGen := DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.invGen_isGen _ _ _ _ ht) (DVR.pullGen_isGen _ _ _ _ ht _)
  let φ₀ : ULift.{0} (Finset (Fin 2)) → ((B ⊗ B).left ⟶ B.left) := fun I => (psum B ![fst B B ≫ a, snd B B] I.down).left
  let φ₁ : ULift.{0} (Finset (Fin 2)) → ((B ⊗ B).left ⟶ B.left) := fun I => (psum B ![fst B B, snd B B ≫ a'] I.down).left
  let e₂ : ULift.{0} (Finset (Fin 2)) → ℤ := fun I => (-1) ^ (2 - I.down.card)
  have hF : FormEq (Sum.elim (Sum.elim φ₁ φ₀) (fun k => ℓ ≫ Sum.elim φ₁ φ₀ k))
      (Sum.elim (fun k => - Sum.elim e₂ (fun k => - e₂ k) k) (Sum.elim e₂ (fun k => - e₂ k))) (rosatiφ B a a') rosatiε := by
    intro U _ k
    haveI : IsMonHom a := ha
    haveI : IsMonHom a' := ha'
    have p := prod_ros a a' (fst B B) (snd B B) k
    rw [lift_fst_snd] at p
    rw [(Finset.prod_congr rfl fun i _ => by erw [Over.id_left, Category.id_comp]).trans p]
    have one : ∀ q : B ⊗ B ⟶ B, lift (1 : B ⊗ B ⟶ B) 1 ≫ q = 1 → k (ℓ ≫ q.left) = k (1 : B ⊗ B ⟶ B).left :=
      fun q hq => by rw [← hq]; rfl
    have o1 : lift (1 : B ⊗ B ⟶ B) 1 ≫ fst B B = 1 := lift_fst _ _
    have o2 : lift (1 : B ⊗ B ⟶ B) 1 ≫ snd B B = 1 := lift_snd _ _
    have o3 : lift (1 : B ⊗ B ⟶ B) 1 ≫ fst B B ≫ a = 1 := by rw [← Category.assoc, o1, MonObj.one_comp]
    have o4 : lift (1 : B ⊗ B ⟶ B) 1 ≫ snd B B ≫ a' = 1 := by rw [← Category.assoc, o2, MonObj.one_comp]
    have o5 : lift (1 : B ⊗ B ⟶ B) 1 ≫ (1 : B ⊗ B ⟶ B) = 1 := MonObj.comp_one _
    have o6 : lift (1 : B ⊗ B ⟶ B) 1 ≫ ((fst B B ≫ a) * snd B B) = 1 := by
      rw [MonObj.comp_mul, o3, o2, _root_.mul_one]
    have o7 : lift (1 : B ⊗ B ⟶ B) 1 ≫ (fst B B * (snd B B ≫ a')) = 1 := by
      rw [MonObj.comp_mul, o1, o4, _root_.mul_one]
    have s1 : ∏ I, k (φ₁ I) ^ e₂ I = _ := GlobalTheory.NormRos.prod_square (fst B B) (snd B B ≫ a') k
    have s0 : ∏ I, k (φ₀ I) ^ e₂ I = _ := GlobalTheory.NormRos.prod_square (fst B B ≫ a) (snd B B) k
    have s1' : ∏ I, k (ℓ ≫ φ₁ I) ^ e₂ I = _ := GlobalTheory.NormRos.prod_square (fst B B) (snd B B ≫ a') (fun ψ => k (ℓ ≫ ψ))
    have s0' : ∏ I, k (ℓ ≫ φ₀ I) ^ e₂ I = _ := GlobalTheory.NormRos.prod_square (fst B B ≫ a) (snd B B) (fun ψ => k (ℓ ≫ ψ))
    rw [Fintype.prod_sum_type, Fintype.prod_sum_type, Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, neg_neg, zpow_neg, Finset.prod_inv_distrib]
    rw [s1, s0, s1', s0']
    simp only [one _ o1, one _ o2, one _ o3, one _ o4, one _ o5, one _ o6, one _ o7]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  refine ⟨ha, ha', ?_, hc, hc', ?_⟩
  · obtain ⟨u, hu, -⟩ := exists_gen hL hF v hv
    exact fun _ => ⟨⊤, trivial, LB.pullGen _ _ _ u _, DVR.pullGen_isGen _ _ _ _ hu _⟩
  · intro u hu h₀ y y'
    haveI : IsMonHom a := ha
    haveI : IsMonHom a' := ha'
    have o : ∀ {T : Over (Spec (CommRingCat.of R))} (x x' : T ⟶ B), (lift x x').left ≫ ℓ = (lift (1 : T ⟶ B) 1).left :=
      fun x x' => by rw [← Over.comp_left, comp_lift, MonObj.comp_one]
    have hvv : ∀ (Z : Scheme.{0}) (r : Z ⟶ (B ⊗ B).left) (z : Z) (J), Good D.toPre.P.L z J →
        val v r z J = (val t r z J)⁻¹ * val t (r ≫ ℓ) z J := fun Z r z J hJ =>
      (val_mul hJ _ _ r).trans (congrArg₂ (· * ·) (val_inv _ _) (val_pull hJ _ _ _))
    have hn : ∀ (yy : (𝟙_ (Over (Spec (CommRingCat.of R)))).left) (J), Good D.toPre.P.L yy J →
        val v (lift (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ B) 1).left yy J = 1 := fun yy J hJ =>
      (hvv _ _ yy J hJ).trans (by erw [o, inv_mul_cancel])
    have eq := DVR.gen_unique₂ GlobalTheory.globalFns_holds D.toPre.P.isAb hL hF hu hv (fun yy J hJ =>
      (DVR.val₂_one h₀ hJ).trans (hn yy J hJ).symm)
    have c0 : D.toPre.c 0 = 1 := mul_eq_left.1 ((D.toPre.c_add 0 0).symm.trans (by rw [add_zero]))
    refine corr_of_val hL fun z J hJ => ?_
    have hp : ∀ a b, val ((pol D).tau a b) (𝟙 _) z J = val (D.toPre.tau a b) (𝟙 _) z J :=
      fun a b => (Wit.exists_tau D.toPre a b).choose_spec.2 _ _ z J hJ
    have h00 : val t (D.toPre.pt2 0 0) z J = 1 := by
      have e := hτ 0 0 z J J hJ hJ
      erw [map_zero h, map_zero h', Data.val_tau_zero (pol D) 0 z J hJ] at e
      refine (val_isoGen w _ z hJ).trans ?_
      exact (_root_.mul_one _).symm.trans e.symm
    have e2 : D.toPre.pt2 y y' ≫ ℓ = D.toPre.pt2 0 0 := by rw [DegPre.pt2, o, DegPre.pt2, c0, MonObj.comp_one]
    have k1 : val v (D.toPre.pt2 y y') z J = (val t (D.toPre.pt2 y y') z J)⁻¹ :=
      (hvv _ _ z J hJ).trans (by erw [e2, h00, _root_.mul_one])
    have k2 : val t (D.toPre.pt2 y y') z J = adjVal w (D.toPre.pt2 y y') z J J := val_isoGen w _ z hJ
    have k4 : val (D.toPre.tau (h y) y') (𝟙 _) z J =
        adjVal w (D.toPre.pt2 y y') z J J * val (D.toPre.tau y (h' y')) (𝟙 _) z J :=
      (hp _ _).symm.trans ((hτ y y' z J J hJ hJ).trans (congrArg _ (hp _ _)))
    rw [val_mul hJ, val_pull hJ, Category.id_comp]
    refine (congrArg (_ * ·) ((eq _ _ z J hJ).trans (k1.trans (congrArg (·⁻¹) k2)))).trans ?_
    rw [k4, mul_comm, inv_mul_cancel_left]

end GlobalTheory.MumFam.AdjEnd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionLabelsUniformisedDominatingTrait
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionLabelsUniformisedDominatingTrait
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem grpPullback_pow_left {S' S : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S}
    {a : G'.left ⟶ G.left} (h : IsGrpPullback G' G f a) {T : Over S'} (x : T ⟶ G') (x₀ : Over.mk (T.hom ≫ f) ⟶ G)
    (hx : x₀.left = x.left ≫ a) : ∀ n : ℕ, (x₀ ^ n).left = (x ^ n).left ≫ a := by
  intro n
  induction n with
  | zero =>
    let u : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk ((1 : T ⟶ G').left ≫ a) (by
      show ((1 : T ⟶ G').left ≫ a) ≫ G.hom = T.hom ≫ f
      rw [Category.assoc, h.1.w, ← Category.assoc, Over.w])
    have hm := h.2 T 1 1 u u rfl rfl
    rw [_root_.mul_one] at hm
    have hu : u * u = u := Over.OverMorphism.ext hm
    have hu1 : u = 1 := mul_eq_left.1 hu
    rw [pow_zero, pow_zero, ← hu1]
    rfl
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact h.2 T (x ^ n) x (x₀ ^ n) x₀ ih hx

end GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_oneTrait : ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁], Base R₁ →
    ∀ (D₁ : DegData R₁ (maximalIdeal R₁)) (A : PolAV (Sp (FractionRing R₁))), UniTrait D₁.toPre A →
      ∃ lab : Labels D₁.toPre A, OneTrait D₁.toPre A lab := by
  intro R _ _ _ hR D A hU
  obtain ⟨W, _, _, _, φ, G', _, _, D', A', U', hD, a, hW, hφ, hloc, hG', ga, hga, hpb, hLa⟩ := hU
  haveI : CharZero R := hR.2
  haveI : CharZero W := charZero_of_injective_ringHom hφ
  have := hW.1
  have hW' : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  letI iW : Algebra (FractionRing R) (Kb W) := ((algebraMap (FractionRing W) (Kb W)).comp ga).toAlgebra
  have tf : ∀ (K M : Type) [Field K] [Field M] [Algebra K M], Module.IsTorsionFree K M := fun _ _ _ _ _ => inferInstance
  haveI := tf (FractionRing R) (Kb W)
  haveI := tf (FractionRing R) (Kb R)
  let em : Kb R →ₐ[FractionRing R] Kb W := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hF : ∀ r, algebraMap (FractionRing R) (Kb W) (algebraMap R _ r) =
      algebraMap (FractionRing W) (Kb W) (algebraMap W _ (φ r)) := fun r =>
    congrArg (algebraMap (FractionRing W) (Kb W)) (hga r)
  obtain ⟨hL, -⟩ := GlobalTheory.firstFiveLaws
  haveI : CharZero (FractionRing R) := charZero_of_injective_ringHom (IsFractionRing.injective R (FractionRing R))
  haveI : CharZero (Kb R) := charZero_of_injective_ringHom (algebraMap (FractionRing R) (Kb R)).injective
  haveI : CharZero (Kb W) := charZero_of_injective_ringHom em.toRingHom.injective
  haveI := GlobalTheory.ArcExt.epi_spMap em.toRingHom
  have hρ : spMap em.toRingHom ≫ jFK (R := R) (Kb R) = (TFK (R := W) (Kb W)).hom ≫ spMap ga := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext x
    exact em.commutes x
  let ρ : Over.mk ((TFK (R := W) (Kb W)).hom ≫ spMap ga) ⟶ TFK (R := R) (Kb R) := Over.homMk (spMap em.toRingHom) hρ
  let Φ : (TFK (R := R) (Kb R) ⟶ A.A) →* (Over.mk ((TFK (R := W) (Kb W)).hom ≫ spMap ga) ⟶ A.A) :=
    MonoidHom.mk' (fun y => ρ ≫ y) fun x y => by rw [MonObj.comp_mul]
  have hΦ : ∀ y, (Φ y).left = spMap em.toRingHom ≫ y.left := fun _ => rfl
  have hΦinj : Function.Injective Φ := fun x y e => Over.OverMorphism.ext
    ((cancel_epi (spMap em.toRingHom)).1 ((hΦ x).symm.trans ((congrArg (fun q => q.left) e).trans (hΦ y))))
  have desc : ∀ k : ℕ, 1 ≤ k → ∀ z : Over.mk ((TFK (R := W) (Kb W)).hom ≫ spMap ga) ⟶ A.A, z ^ k = 1 →
      ∃ y : TFK (R := R) (Kb R) ⟶ A.A, Φ y = z := by
    intro k hk z hz
    let u : {y : TFK (R := R) (Kb R) ⟶ A.A // y ^ k = 1} →
        {z : Over.mk ((TFK (R := W) (Kb W)).hom ≫ spMap ga) ⟶ A.A // z ^ k = 1} :=
      fun y => ⟨Φ y.1, by rw [← map_pow, y.2, map_one]⟩
    have hu : Function.Injective u := fun y y' e => Subtype.ext (hΦinj (congrArg Subtype.val e))
    have c := GlobalTheory.ArcExt.card_torsion hL A (jFK (R := R) (Kb R)) (n := k) (Nat.cast_ne_zero.2 (by omega))
    have c' := GlobalTheory.ArcExt.card_torsion hL A ((TFK (R := W) (Kb W)).hom ≫ spMap ga) (n := k)
      (Nat.cast_ne_zero.2 (by omega))
    haveI : Finite {z : Over.mk ((TFK (R := W) (Kb W)).hom ≫ spMap ga) ⟶ A.A // z ^ k = 1} :=
      Nat.finite_of_card_ne_zero (by rw [c']; positivity)
    obtain ⟨y, e⟩ := (hu.bijective_of_nat_card_le (c'.trans c.symm).le).2 ⟨z, hz⟩
    exact ⟨y.1, congrArg Subtype.val e⟩
  have toA : ∀ (k : ℕ) (x' : TFK (R := W) (Kb W) ⟶ A'.A), x' ^ k = 1 →
      ∃ z : Over.mk ((TFK (R := W) (Kb W)).hom ≫ spMap ga) ⟶ A.A, z.left = x'.left ≫ a ∧ z ^ k = 1 := by
    intro k x' hx
    let z : Over.mk ((TFK (R := W) (Kb W)).hom ≫ spMap ga) ⟶ A.A := Over.homMk (x'.left ≫ a) (by
      show (x'.left ≫ a) ≫ A.A.hom = (TFK (R := W) (Kb W)).hom ≫ spMap ga
      rw [Category.assoc, hpb.1.w, ← Category.assoc, Over.w])
    refine ⟨z, rfl, Over.OverMorphism.ext ?_⟩
    rw [grpPullback_pow_left hpb x' z rfl k, hx]
    exact ((grpPullback_pow_left hpb x' z rfl 0).trans (by rw [pow_zero])).symm
  have key : ∀ (k : ℕ) (p : QkPt D.toPre (Kb R) k), ∃ y : TFK (R := R) (Kb R) ⟶ A.A, 1 ≤ k →
      ∀ (p₁ : QkPt D.toPre (Kb W) k) (p' : QkPt D'.toPre (Kb W) k) (x' : TFK (R := W) (Kb W) ⟶ A'.A),
        QkExt em.toRingHom p p₁ → p'.y = hD.xe.symm p₁.y → IsPullGtF φ hD (Kb W) p₁.g p'.g →
        x'.left ≫ a = spMap em.toRingHom ≫ y.left → QkToAkU U'.toUnifPre (Kb W) k p' x' := by
    intro k p
    by_cases hk : 1 ≤ k
    swap
    · exact ⟨1, fun h => absurd h hk⟩
    by_cases hex : ∃ (p₁ : QkPt D.toPre (Kb W) k) (p' : QkPt D'.toPre (Kb W) k),
        QkExt em.toRingHom p p₁ ∧ p'.y = hD.xe.symm p₁.y ∧ IsPullGtF φ hD (Kb W) p₁.g p'.g
    swap
    · exact ⟨1, fun _ p₁ p' _ h₁ h₂ h₃ _ => absurd ⟨p₁, p', h₁, h₂, h₃⟩ hex⟩
    obtain ⟨p₁, p', h₁, h₂, h₃⟩ := hex
    obtain ⟨f, hf, hfk⟩ := GlobalTheory.TorsionIso.torsion_clause W (maximalIdeal W) hW' D' A' G' hG' U' (Kb W) k hk
    obtain ⟨z, hz, hzk⟩ := toA k (f p') (hfk p')
    obtain ⟨y, hy⟩ := desc k hk z hzk
    refine ⟨y, fun _ q₁ q' x' e₁ e₂ e₃ e₄ => ?_⟩
    obtain rfl : q₁ = p₁ := GlobalTheory.DegActCompare.qkExt_unique e₁ h₁
    obtain rfl : q' = p' := GlobalTheory.TorusExt.qk_ext (e₂.trans h₂.symm) (GlobalTheory.ArcPull.pullGt_unique hD hF e₃ h₃)
    rw [(hf.1 q' x')]
    refine Over.OverMorphism.ext (hpb.1.hom_ext ?_ ?_)
    · rw [e₄, ← hz, ← hy]
      exact (hΦ y).symm
    · rw [Over.w x', Over.w (f q')]
  choose lab hlab using key
  exact ⟨lab, W, inferInstance, inferInstance, inferInstance, φ, G', inferInstance, inferInstance, D', A', U', hD, a, iW, em,
    hW, hφ, hloc, hG', ⟨ga, hga, hpb, hLa⟩, hF, fun k hk p p₁ p' x' h₁ h₂ h₃ h₄ => hlab k p hk p₁ p' x' h₁ h₂ h₃ h₄⟩

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionLabelsUniformisedDominatingTraitStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torsionLabels_uniformisedDominatingTrait : ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁], Base R₁ → ∀ (D₁ : DegData R₁ (maximalIdeal R₁)) (A : PolAV (Sp (FractionRing R₁))), UniTrait D₁.toPre A → ∃ lab : Labels D₁.toPre A, OneTrait D₁.toPre A lab := by
  first | exact @GlobalTheory.Mum.exists_oneTrait | exact GlobalTheory.Mum.exists_oneTrait | (intros; apply GlobalTheory.Mum.exists_oneTrait <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomOfSumMapCompFixingNearOpen
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomOfSumMapCompFixingNearOpen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.DescHom

theorem ext_of_open {T : Scheme.{0}} {W X Y : Over T} (j : W ⟶ X) [IsOpenImmersion j.left] [Surjective W.hom]
    [Smooth X.hom] [GeometricallyIrreducible X.hom] [IsSeparated Y.hom] {f g : X ⟶ Y} (h : j ≫ f = j ≫ g) : f = g := by
  have hfib : ∀ x : X.left, x ∈ closure ((j.left.opensRange : Set X.left) ∩ X.hom ⁻¹' {X.hom x}) := by
    intro x
    have hirr : IsIrreducible (X.hom ⁻¹' {X.hom x}) :=
      X.hom.isIrreducible_preimage X.hom.isOpenMap isIrreducible_singleton
    obtain ⟨w, hw⟩ := W.hom.surjective (X.hom x)
    have hne : (X.hom ⁻¹' {X.hom x} ∩ (j.left.opensRange : Set X.left)).Nonempty := by
      refine ⟨j.left w, ?_, ⟨w, rfl⟩⟩
      show X.hom (j.left w) = X.hom x
      rw [← Scheme.Hom.comp_apply, Over.w]
      exact hw
    have hsub := subset_closure_inter_of_isPreirreducible_of_isOpen hirr.isPreirreducible
      j.left.opensRange.isOpen hne (show x ∈ X.hom ⁻¹' {X.hom x} from rfl)
    rwa [Set.inter_comm] at hsub
  have hl : j.left ≫ f.left = j.left ≫ g.left := by
    simpa only [Over.comp_left] using congrArg CommaMorphism.left h
  apply Over.OverMorphism.ext
  refine GlobalTheory.FibreDense.main X.left T Y.left X.hom Y.hom j.left.opensRange hfib f.left g.left
    (by rw [Over.w f, Over.w g]) ?_
  rw [← Scheme.Hom.isoOpensRange_inv_comp, Category.assoc, Category.assoc, hl]

theorem isMonHom_of_open {T : Scheme.{0}} {W X Y : Over T} [GrpObj X] [GrpObj Y] (j : W ⟶ X) [IsOpenImmersion j.left]
    [Surjective W.hom] [Smooth X.hom] [GeometricallyIrreducible X.hom] [IsSeparated Y.hom] (φ : X ⟶ Y)
    (h : ((fst W W ≫ j) * (snd W W ≫ j)) ≫ φ = (fst W W ≫ j ≫ φ) * (snd W W ≫ j ≫ φ)) : IsMonHom φ := by
  have hmuX : (μ : X ⊗ X ⟶ X) = fst X X * snd X X := by
    rw [Hom.mul_def, lift_fst_snd, Category.id_comp]
  have hmuY : (μ : Y ⊗ Y ⟶ Y) = fst Y Y * snd Y Y := by
    rw [Hom.mul_def, lift_fst_snd, Category.id_comp]
  have hoi : IsOpenImmersion (j ⊗ₘ j).left := by
    rw [Over.tensorHom_left]
    exact MorphismProperty.pullbackMap (P := @IsOpenImmersion) ‹_› ‹_› (by simp) (by simp)
  have hsurj : Surjective (W ⊗ W).hom := by
    rw [Over.tensorObj_hom]; infer_instance
  have hsm : Smooth (X ⊗ X).hom := by
    rw [Over.tensorObj_hom]; infer_instance
  have hgi : GeometricallyIrreducible (X ⊗ X).hom := by
    rw [Over.tensorObj_hom]
    exact GeometricallyIrreducible.comp _ _
  have hmul : μ ≫ φ = (φ ⊗ₘ φ) ≫ μ := by
    apply ext_of_open (j ⊗ₘ j)
    have lhs : (j ⊗ₘ j) ≫ μ ≫ φ = ((fst W W ≫ j) * (snd W W ≫ j)) ≫ φ := by
      rw [hmuX, ← Category.assoc, MonObj.comp_mul, tensorHom_fst, tensorHom_snd]
    have rhs : (j ⊗ₘ j) ≫ (φ ⊗ₘ φ) ≫ μ = (fst W W ≫ j ≫ φ) * (snd W W ≫ j ≫ φ) := by
      rw [hmuY, MonObj.comp_mul, tensorHom_fst, tensorHom_snd, MonObj.comp_mul, tensorHom_fst_assoc,
        tensorHom_snd_assoc]
    rw [lhs, rhs, h]
  have hcomp : ∀ {Z : Over T} (a b : Z ⟶ X), (a * b) ≫ φ = (a ≫ φ) * (b ≫ φ) := by
    intro Z a b
    rw [Hom.mul_def, Hom.mul_def, Category.assoc, hmul, ← Category.assoc, lift_map]
  have hone : η ≫ φ = η := by
    have h1 : ((1 : 𝟙_ (Over T) ⟶ X) ≫ φ) * ((1 : 𝟙_ (Over T) ⟶ X) ≫ φ) = (1 : 𝟙_ (Over T) ⟶ X) ≫ φ := by
      rw [← hcomp, _root_.mul_one]
    have h2 : (1 : 𝟙_ (Over T) ⟶ X) ≫ φ = 1 := _root_.mul_eq_left.mp h1
    have e1 : ∀ {M : Over T} [MonObj M], (1 : 𝟙_ (Over T) ⟶ M) = η := by
      intro M _
      rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    rw [← e1, ← e1]
    exact h2
  exact ⟨hone, hmul⟩

theorem geometricallyIrreducible_of_semiAbelian {S : Scheme.{0}} (G : Over S) [GrpObj G] (hG : IsSemiAbelian G) :
    GeometricallyIrreducible G.hom := by
  obtain ⟨_, hsm, _, _, hgc, _⟩ := hG
  have := GlobalTheory.grpObj_geometricallyIntegral_of_smooth S G
  infer_instance

variable {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S}

theorem surjective_near [GrpObj G] [Surjective π] (N : Near π G) : Surjective N.U.hom := by
  have := N.smooth
  have hcl : closedPoint R ∈ Set.range N.U.hom := by
    obtain ⟨s, hs⟩ := π.surjective (closedPoint R)
    have he : (η[G] : 𝟙_ (Over S) ⟶ G).left ≫ G.hom = 𝟙 S := Over.w η[G]
    have hGs : G.hom ((η[G] : 𝟙_ (Over S) ⟶ G).left s) = s := by
      rw [← Scheme.Hom.comp_apply, he]; rfl
    obtain ⟨y, hy⟩ := N.all _ (by rw [hGs, hs])
    refine ⟨pullback.fst N.U.hom π y, ?_⟩
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, ← N.u_over,
      Scheme.Hom.comp_apply, hy, hGs, hs]
  exact ⟨fun x => (Flat.generalizingMap N.U.hom).stableUnderGeneralization_range
    (specializes_closedPoint x) hcl⟩

theorem isPullback_embL (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    IsPullback (Desc.toS N p hp) (Desc.embL N p hp) N.u (pullback.fst G.hom p) := by
  have hA : IsPullback (Desc.toS N p hp) (pullback.snd N.U.hom (pullback.fst π π ≫ π))
      (pullback.snd N.U.hom π) p := by
    have outer : IsPullback (Desc.toS N p hp ≫ pullback.fst N.U.hom π)
        (pullback.snd N.U.hom (pullback.fst π π ≫ π)) N.U.hom (p ≫ π) := by
      rw [Desc.toS, pullback.lift_fst, hp]
      exact IsPullback.of_hasPullback _ _
    exact IsPullback.of_right outer (by rw [Desc.toS, pullback.lift_snd]) (IsPullback.of_hasPullback _ _)
  refine IsPullback.of_bot ?_ ?_ (IsPullback.of_hasPullback G.hom p)
  · rw [Desc.embL, pullback.lift_snd, N.u_over]
    exact hA
  · rw [Desc.embL, pullback.lift_fst]

theorem isOpenImmersion_emb (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    IsOpenImmersion (Desc.emb N p hp).left := by
  have := N.isOpen
  exact MorphismProperty.of_isPullback (P := @IsOpenImmersion) (isPullback_embL N p hp) N.isOpen

theorem isMonHom_of_sum_of_emb : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ N : Near π G', ∀ (p p' : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) (hp' : p' ≫ π = pullback.fst π π ≫ π), ∀ φ : (Over.pullback p).obj G' ⟶ (Over.pullback p').obj G', Desc.sum N p hp ≫ φ = Desc.sum N p' hp' → Desc.emb N p hp ≫ φ = Desc.emb N p' hp' → IsMonHom φ := by
  intro R _ _ _ _ S π _ _ _ G' _ _ hG N p p' hp hp' φ hsum hemb
  have : Surjective N.U.hom := surjective_near N
  have : GeometricallyIrreducible G'.hom := geometricallyIrreducible_of_semiAbelian G' hG
  obtain ⟨_, hsm, hsep, _, _, _⟩ := hG
  have : IsOpenImmersion (Desc.emb N p hp).left := isOpenImmersion_emb N p hp
  have : Surjective (Desc.UT N).hom := by
    show Surjective (pullback.snd N.U.hom (pullback.fst π π ≫ π)); infer_instance
  have : Smooth ((Over.pullback p).obj G').hom := by
    show Smooth (pullback.snd G'.hom p); infer_instance
  have : GeometricallyIrreducible ((Over.pullback p).obj G').hom := by
    show GeometricallyIrreducible (pullback.snd G'.hom p); infer_instance
  have : IsSeparated ((Over.pullback p').obj G').hom := by
    show IsSeparated (pullback.snd G'.hom p'); infer_instance
  refine isMonHom_of_open (Desc.emb N p hp) φ ?_
  change Desc.sum N p hp ≫ φ = _
  rw [hsum, Desc.sum, ← hemb]

end GlobalTheory.Mum.DescHom
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomOfSumMapCompFixingNearOpenStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isMonHom_of_sumMap_comp_fixing_nearOpen : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ N : Near π G', ∀ (p p' : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) (hp' : p' ≫ π = pullback.fst π π ≫ π), ∀ φ : (Over.pullback p).obj G' ⟶ (Over.pullback p').obj G', Desc.sum N p hp ≫ φ = Desc.sum N p' hp' → Desc.emb N p hp ≫ φ = Desc.emb N p' hp' → IsMonHom φ := by
  first | exact @GlobalTheory.Mum.DescHom.isMonHom_of_sum_of_emb | exact GlobalTheory.Mum.DescHom.isMonHom_of_sum_of_emb | (intros; apply GlobalTheory.Mum.DescHom.isMonHom_of_sum_of_emb <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoGluedFromLinCombPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoGluedFromLinCombPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem trF_sum_elim {X Y Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
    (φ₁ : K → (Y ⟶ X)) (φ₂ : K' → (Y ⟶ X)) (ε₁ : K → ℤ) (ε₂ : K' → ℤ) (r : Z ⟶ Y) (z : Z)
    (p p' : K → L.ι) (q q' : K' → L.ι) :
    trF (Sum.elim φ₁ φ₂) (Sum.elim ε₁ ε₂) r z (Sum.elim p q) (Sum.elim p' q') =
      trF φ₁ ε₁ r z p p' * trF φ₂ ε₂ r z q q' := by
  rw [trF, trF, trF, Fintype.prod_sum_type]; rfl

theorem trF_self' {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (r : Z ⟶ Y) (z : Z) (p : K → L.ι) (hp : r z ∈ LB.wchart L φ p) :
    trF φ ε r z p p = 1 := by
  unfold trF
  refine Finset.prod_eq_one fun k _ => ?_
  rw [gm_self hL (r ≫ φ k) z (Set.mem_iInter.1 hp k), _root_.one_zpow]

theorem iso_linComb_pull_glue : ∀ {X X' Y : Scheme.{0}} {M : LB Y}, M.IsLB → ∀ {L' : LB X'}, L'.IsLB →
    ∀ {K K' : Type} [Fintype K] [Fintype K'] (φ : K → (X' ⟶ Y)) (ε : K → ℤ) (ψ : K' → (X ⟶ Y)) (e : K' → ℤ)
    (F : X ⟶ X') (w₁ : LB.Iso L' (LB.LinComb M φ ε)), w₁.IsGen →
    ∀ (u : LB.Gen (LB.LinComb M (Sum.elim (fun k => F ≫ φ k) ψ) (Sum.elim ε (fun i => - e i)))), u.IsGen →
    ∃ w : LB.Iso (LB.LinComb M ψ e) (L'.pull F), w.IsGen ∧
      ∀ (Z : Scheme.{0}) (f : Z ⟶ X) (z : Z) (J : (Z ⟶ Y) → M.ι), Good M z J → ∀ j' : L'.ι, F (f z) ∈ L'.U j' →
        gw w f z j' (fun i => J (f ≫ ψ i)) = (gv w₁ (f ≫ F) z (fun k => J ((f ≫ F) ≫ φ k)) j')⁻¹ * val u f z J := by
  intro X X' Y M hM L' hL' K K' _ _ φ ε ψ e F w₁ hw₁ u hu

  have memE : ∀ {Z : Scheme.{0}} (f : Z ⟶ X) (z : Z) (p : K → M.ι) (q : K' → M.ι),
      F (f z) ∈ LB.wchart M φ p → f z ∈ LB.wchart M ψ q →
      f z ∈ LB.wchart M (Sum.elim (fun k => F ≫ φ k) ψ) (Sum.elim p q) := by
    intro Z f z p q hp hq
    refine Set.mem_iInter.2 fun k => ?_
    cases k with
    | inl k => exact Set.mem_iInter.1 hp k
    | inr i => exact Set.mem_iInter.1 hq i

  have key : ∀ {Z : Scheme.{0}} (f : Z ⟶ X) (z : Z) (j' : L'.ι) (q : K' → M.ι) (p p' : K → M.ι),
      F (f z) ∈ L'.U j' → f z ∈ LB.wchart M ψ q → F (f z) ∈ LB.wchart M φ p → F (f z) ∈ LB.wchart M φ p' →
      gm f z _ (u.s (Sum.elim p q)) * (gm (f ≫ F) z _ (w₁.s (p, j')))⁻¹ =
        gm f z _ (u.s (Sum.elim p' q)) * (gm (f ≫ F) z _ (w₁.s (p', j')))⁻¹ := by
    intro Z f z j' q p p' hj hq hp hp'
    have a := gen_trans hu f z (memE f z p q hp hq) (memE f z p' q hp' hq)
    rw [trF_sum_elim, trF_self' hM ψ _ f z q hq, _root_.mul_one] at a
    have b := gm_isGen hw₁ (f ≫ F) z p p' j' j' hp hp' hj hj
    have c : gm (f ≫ F) z _ ((LB.LinComb M φ ε).g p p') = trF (fun k => F ≫ φ k) ε f z p p' := by
      refine (gm_linComb M φ ε (f ≫ F) z p p' hp hp').trans ?_
      simp only [trF, Category.assoc]
    rw [c, gm_self hL' (f ≫ F) z hj, inv_one, _root_.mul_one] at b
    show gm f z (LB.wchart M (Sum.elim (fun k => F ≫ φ k) ψ) (Sum.elim p q)) (u.s (Sum.elim p q)) * (gv w₁ (f ≫ F) z p j')⁻¹ =
      gm f z (LB.wchart M (Sum.elim (fun k => F ≫ φ k) ψ) (Sum.elim p' q)) (u.s (Sum.elim p' q)) * (gv w₁ (f ≫ F) z p' j')⁻¹
    rw [a, b]
    generalize trF (fun k => F ≫ φ k) ε f z p p' = T
    generalize gm f z _ (u.s (Sum.elim p' q)) = U
    generalize gv w₁ (f ≫ F) z p' j' = V
    rw [_root_.mul_inv, _root_.mul_mul_mul_comm, _root_.mul_inv_cancel, _root_.one_mul]
  have glue : ∀ (j' : L'.ι) (q : K' → M.ι),
      ∃ s : Γ(X, (L'.pull F).U (fun _ => j') ⊓ (LB.LinComb M ψ e).U q)ˣ,
      ∀ (Z : Scheme.{0}) (f : Z ⟶ X) (z : Z) (p : K → M.ι), F (f z) ∈ L'.U j' → f z ∈ LB.wchart M ψ q →
        F (f z) ∈ LB.wchart M φ p →
        gm f z _ s = gm f z _ (u.s (Sum.elim p q)) * (gm (f ≫ F) z _ (w₁.s (p, j')))⁻¹ := by
    intro j' q
    obtain ⟨W, hW⟩ : ∃ W : (K → M.ι) → X.Opens, ∀ p x, x ∈ W p ↔
        F x ∈ L'.U j' ∧ x ∈ LB.wchart M ψ q ∧ F x ∈ LB.wchart M φ p :=
      ⟨fun p => F ⁻¹ᵁ L'.U j' ⊓ (LB.wchart M ψ q ⊓ F ⁻¹ᵁ LB.wchart M φ p), fun _ _ => Iff.rfl⟩
    have l₀ : ∀ p, W p ≤ (L'.pull F).U (fun _ => j') ⊓ (LB.LinComb M ψ e).U q := fun p x hx =>
      ⟨mem_pull.2 ((hW p x).1 hx).1, ((hW p x).1 hx).2.1⟩
    have l₁ : ∀ p, W p ≤ LB.wchart M (Sum.elim (fun k => F ≫ φ k) ψ) (Sum.elim p q) := fun p x hx =>
      memE (𝟙 X) x p q ((hW p x).1 hx).2.2 ((hW p x).1 hx).2.1
    have l₂ : ∀ p, W p ≤ F ⁻¹ᵁ (LB.wchart M φ p ⊓ L'.U j') := fun p x hx =>
      ⟨((hW p x).1 hx).2.2, ((hW p x).1 hx).1⟩
    obtain ⟨v, hv⟩ : ∃ v : ∀ p, Γ(X, W p)ˣ, ∀ (Z : Scheme.{0}) (f : Z ⟶ X) (z : Z) (p : K → M.ι), f z ∈ W p →
        gm f z (W p) (v p) = gm f z _ (u.s (Sum.elim p q)) * (gm (f ≫ F) z _ (w₁.s (p, j')))⁻¹ :=
      ⟨fun p => res (l₁ p) (u.s (Sum.elim p q)) * (res (l₂ p) (pullU F _ (w₁.s (p, j'))))⁻¹,
        fun Z f z p hz => (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res f z (l₁ p) hz _)
          ((map_inv _ _).trans (congrArg (·⁻¹) ((gm_res f z (l₂ p) hz _).trans (gm_pull f F z _ (l₂ p hz) _)))))⟩
    obtain ⟨s, hs⟩ := glue_unit _ W l₀ (fun x hx => by
        choose p hp using fun k => exists_chart hM (φ k (F x))
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨p, (hW p x).2 ⟨mem_pull.1 hx.1, hx.2, Set.mem_iInter.2 hp⟩⟩) v (fun p p' x hx => by
        have h₁ := (hW p x).1 hx.1
        have h₂ := (hW p' x).1 hx.2
        exact (hv _ (𝟙 X) x p hx.1).trans ((key (𝟙 X) x j' q p p' h₁.1 h₁.2.1 h₁.2.2 h₂.2.2).trans
          (hv _ (𝟙 X) x p' hx.2).symm))
    refine ⟨s, fun Z f z p hj hq hp => ?_⟩
    have hz := (hW p (f z)).2 ⟨hj, hq, hp⟩
    exact (gm_res f z (l₀ p) hz s).symm.trans ((congrArg (gm f z (W p)) (hs p)).trans (hv Z f z p hz))
  choose s hs using glue
  refine ⟨⟨fun P => s (P.1 PUnit.unit) P.2⟩, (isGen_iff _).2 ?_, ?_⟩
  · intro Z f z j j' (k : K' → M.ι) (k' : K' → M.ι) hj hj' hk hk'
    choose p hp using fun a => exists_chart hM (φ a (F (f z)))
    have hpm : F (f z) ∈ LB.wchart M φ p := Set.mem_iInter.2 hp
    show gm f z _ (s j k) = gm (f ≫ F) z _ (L'.g j j') * (gm f z _ ((LB.LinComb M ψ e).g k k'))⁻¹ *
      gm f z _ (s j' k')
    rw [hs j k Z f z p hj hk hpm, hs j' k' Z f z p hj' hk' hpm]
    have a := gen_trans hu f z (memE f z p k hpm hk) (memE f z p k' hpm hk')
    rw [trF_sum_elim, trF_self' hM (fun a => F ≫ φ a) ε f z p (Set.mem_iInter.2 fun a => Set.mem_iInter.1 hpm a), _root_.one_mul] at a
    have c : gm f z _ ((LB.LinComb M ψ e).g k k') = trF ψ e f z k k' := gm_linComb M ψ e f z k k' hk hk'
    have d : trF ψ (fun i => - e i) f z k k' = (trF ψ e f z k k')⁻¹ := by
      simp only [trF, zpow_neg, Finset.prod_inv_distrib]
    rw [d] at a
    have b := gm_isGen hw₁ (f ≫ F) z p p j j' hpm hpm hj hj'
    have c' : gm (f ≫ F) z _ ((LB.LinComb M φ ε).g p p) = 1 :=
      (gm_linComb M φ ε (f ≫ F) z p p hpm hpm).trans (trF_self' hM φ ε (f ≫ F) z p hpm)
    rw [c', _root_.one_mul] at b
    show gm f z (LB.wchart M (Sum.elim (fun k => F ≫ φ k) ψ) (Sum.elim p k)) (u.s (Sum.elim p k)) * (gv w₁ (f ≫ F) z p j)⁻¹ =
      gm (f ≫ F) z _ (L'.g j j') * (gm f z _ ((LB.LinComb M ψ e).g k k'))⁻¹ *
      (gm f z (LB.wchart M (Sum.elim (fun k => F ≫ φ k) ψ) (Sum.elim p k')) (u.s (Sum.elim p k')) * (gv w₁ (f ≫ F) z p j')⁻¹)
    rw [a, b, c]
    generalize trF ψ e f z k k' = T
    generalize gm f z _ (u.s (Sum.elim p k')) = U
    generalize gv w₁ (f ≫ F) z p j' = V
    generalize gm (f ≫ F) z _ (L'.g j j') = G
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · intro Z f z J hJ j' hj
    have hp : F (f z) ∈ LB.wchart M φ (fun k => J ((f ≫ F) ≫ φ k)) :=
      Set.mem_iInter.2 fun k => hJ ((f ≫ F) ≫ φ k)
    show gm f z _ (s j' (fun i => J (f ≫ ψ i))) = _
    rw [hs j' _ Z f z _ hj (hJ.mem ψ f) hp,
      val_of u f z J (Sum.elim (fun k => J ((f ≫ F) ≫ φ k)) (fun i => J (f ≫ ψ i)))
        (by rintro (k | i) <;> simp only [Sum.elim_inl, Sum.elim_inr, Category.assoc])]
    exact mul_comm _ _

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoGluedFromLinCombPullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_iso_glued_from_linComb_pullback : ∀ {X X' Y : Scheme.{0}} {M : LB Y}, M.IsLB → ∀ {L' : LB X'}, L'.IsLB →
    ∀ {K K' : Type} [Fintype K] [Fintype K'] (φ : K → (X' ⟶ Y)) (ε : K → ℤ) (ψ : K' → (X ⟶ Y)) (e : K' → ℤ)
    (F : X ⟶ X') (w₁ : LB.Iso L' (LB.LinComb M φ ε)), w₁.IsGen →
    ∀ (u : LB.Gen (LB.LinComb M (Sum.elim (fun k => F ≫ φ k) ψ) (Sum.elim ε (fun i => - e i)))), u.IsGen →
    ∃ w : LB.Iso (LB.LinComb M ψ e) (L'.pull F), w.IsGen ∧
      ∀ (Z : Scheme.{0}) (f : Z ⟶ X) (z : Z) (J : (Z ⟶ Y) → M.ι), Good M z J → ∀ j' : L'.ι, F (f z) ∈ L'.U j' →
        gw w f z j' (fun i => J (f ≫ ψ i)) = (gv w₁ (f ≫ F) z (fun k => J ((f ≫ F) ≫ φ k)) j')⁻¹ * val u f z J := by
  first | exact @GlobalTheory.Mum.iso_linComb_pull_glue | exact GlobalTheory.Mum.iso_linComb_pull_glue | (intros; apply GlobalTheory.Mum.iso_linComb_pull_glue <;> assumption)
end
end
