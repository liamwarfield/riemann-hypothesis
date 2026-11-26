module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.WeightIndep
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGenFlat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.AppCompatGeneric

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGenDiv
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGenLevel
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGenThick
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ReciprocityTheory.ChartRestriction.G.DVR.TG

noncomputable section

variable {R : Type} [CommRing R]

lemma toW_res {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of R)) {V W : X.Opens} (h : W ≤ V) (r : R) :
    (X.presheaf.map (homOfLE h).op).hom (toW p V r) = toW p W r := by
  simp only [toW, RingHom.comp_apply]
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

lemma app_toW {X Y : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of R)) (f : Y ⟶ X) (W : X.Opens) (r : R) :
    (f.app W).hom (toW p W r) = toW (f ≫ p) (f ⁻¹ᵁ W) r := by
  simp only [toW, RingHom.comp_apply]
  rw [← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE]
  erw [Scheme.Hom.appLE_comp_appLE]

lemma toW_congr {X : Scheme.{0}} {p p' : X ⟶ Spec (CommRingCat.of R)} (h : p = p') (W : X.Opens) (r : R) :
    toW p W r = toW p' W r := by subst h; rfl

lemma app_res {X Y : Scheme.{0}} (f : Y ⟶ X) {V W : X.Opens} (h : W ≤ V) (x : Γ(X, V)) :
    (Y.presheaf.map (homOfLE (f.preimage_mono h)).op).hom ((f.app V).hom x) =
      (f.app W).hom ((X.presheaf.map (homOfLE h).op).hom x) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.naturality]
  rfl

variable [IsDomain R]

theorem exists_div {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of R)) [Flat p] {a : R} (ha : a ≠ 0)
    {J : Ideal R} (hJ : J ≤ Ideal.span {a})
    (V : X.Opens) (x : Γ(X, V)) (hx : (pullback.fst p (tq J)).app V x = 0) :
    ∃ g : Γ(X, V), x = toW p V a * g := by
  classical
  set π := pullback.fst p (tq J)
  let ι := {W : X.affineOpens // (W : X.Opens) ≤ V}
  let U : ι → X.Opens := fun W => W.1
  have hloc : ∀ W : ι, ∃ g : Γ(X, U W), (X.presheaf.map (homOfLE W.2).op).hom x = toW p (U W) a * g := by
    intro W
    have h0 : (π.app (U W)).hom ((X.presheaf.map (homOfLE W.2).op).hom x) = 0 := by
      rw [← app_res, hx, map_zero]
    have hm := Ideal.map_mono hJ ((app_fst_tq p J (U W) W.1.2).2 _ h0)
    rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at hm
    obtain ⟨g, hg⟩ := hm
    exact ⟨g, by rw [← hg, mul_comm]⟩
  choose g hg using hloc
  have hcover : V ≤ iSup U := by
    intro y hy
    obtain ⟨W, hW, hyW, hWV⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hy
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨W, hW⟩, hWV⟩, hyW⟩
  have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.1 U g := by
    intro i j
    show (X.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op).hom (g i) =
      (X.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op).hom (g j)
    rw [← sub_eq_zero]
    apply toW_mul_eq_zero p _ ha
    rw [mul_sub]
    have e1 := congrArg (X.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op).hom (hg i)
    have e2 := congrArg (X.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op).hom (hg j)
    rw [map_mul, toW_res, ← CommRingCat.comp_apply, ← Functor.map_comp] at e1 e2
    rw [sub_eq_zero]
    exact e1.symm.trans e2
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' X.sheaf U V (fun i => homOfLE i.2) hcover g hcompat
  refine ⟨s, ?_⟩
  apply TopCat.Sheaf.eq_of_locally_eq' X.sheaf U V (fun i => homOfLE i.2) hcover
  intro i
  show (X.presheaf.map (homOfLE i.2).op).hom x = (X.presheaf.map (homOfLE i.2).op).hom (toW p V a * (show Γ(X, V) from s))
  rw [hg i, map_mul, toW_res]
  exact congrArg _ (hs i).symm

end

end ReciprocityTheory.ChartRestriction.G.DVR.TG

namespace ReciprocityTheory.ChartRestriction.G.DVR.TG

noncomputable section

variable {R : Type} [CommRing R]

lemma app_toW_of_mem {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of R)) (J : Ideal R) (W : X.Opens)
    {r : R} (hr : r ∈ J) : (pullback.fst p (tq J)).app W (toW p W r) = 0 := by
  have e1 : (pullback.fst p (tq J)).app W (toW p W r) =
      ((pullback.snd p (tq J) ≫ tq J).appLE ⊤ (pullback.fst p (tq J) ⁻¹ᵁ W) le_top).hom
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) := by
    rw [toW, RingHom.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE]
    erw [Scheme.Hom.appLE_comp_appLE]
    rw [appLE_of_eq pullback.condition]
  have e2 : (pullback.snd p (tq J) ≫ tq J).appLE ⊤ (pullback.fst p (tq J) ⁻¹ᵁ W) le_top =
      (tq J).appLE ⊤ (tq J ⁻¹ᵁ ⊤) le_rfl ≫
        (pullback.snd p (tq J)).appLE (tq J ⁻¹ᵁ ⊤) (pullback.fst p (tq J) ⁻¹ᵁ W) le_top := by
    erw [Scheme.Hom.appLE_comp_appLE]
  have e3 : (tq J).appLE ⊤ (tq J ⁻¹ᵁ ⊤) le_rfl =
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫ CommRingCat.ofHom (Ideal.Quotient.mk J) ≫
        (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ J))).inv := by
    rw [Scheme.Hom.appLE_eq_app, ← Scheme.Hom.appTop,
      (Iso.eq_comp_inv _).2 (Scheme.ΓSpecIso_naturality _), Category.assoc]
  have eR : (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) = r := by
    rw [← CommRingCat.comp_apply, Iso.inv_hom_id]; rfl
  have e4 : ((Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫ CommRingCat.ofHom (Ideal.Quotient.mk J) ≫
        (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ J))).inv).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) = 0 := by
    rw [CommRingCat.comp_apply, CommRingCat.comp_apply, eR]
    erw [Ideal.Quotient.eq_zero_iff_mem.2 hr, map_zero]
  rw [e1, e2, CommRingCat.comp_apply, e3]
  erw [e4, map_zero]

variable [IsDomain R]


set_option maxHeartbeats 400000 in
theorem vanish_of_mul {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of R)) [Flat p] {a : R} (ha : a ≠ 0)
    (e : ℕ) {J₁ J₂ : Ideal R} (h1 : J₁ ≤ Ideal.span {a ^ (e + 2)}) (h2 : a ^ (e + 1) ∈ J₂)
    (ι : pullback p (tq J₂) ⟶ pullback p (tq J₁)) (hι : ι ≫ pullback.fst p (tq J₁) = pullback.fst p (tq J₂))
    (V : (pullback p (tq J₁)).Opens) (y : Γ(pullback p (tq J₁), V))
    (hy : toW (pullback.fst p (tq J₁) ≫ p) V a * y = 0) :
    (ι.app V) y = 0 := by
  set π₁ := pullback.fst p (tq J₁)
  set π₂ := pullback.fst p (tq J₂)
  have : IsClosedImmersion (tq J₁) := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have : IsClosedImmersion π₁ := inferInstance
  refine TopCat.Presheaf.section_ext (pullback p (tq J₂)).sheaf _ _ 0 fun z hz => ?_

  have hemb : Topology.IsEmbedding π₁.base := π₁.isClosedEmbedding.isEmbedding
  obtain ⟨V₀, hV₀, hV₀e⟩ := hemb.isInducing.isOpen_iff.1 V.isOpen
  have hz0 : π₁.base (ι.base z) ∈ V₀ := by
    have : ι.base z ∈ (π₁.base ⁻¹' V₀) := by rw [hV₀e]; exact hz
    exact this
  obtain ⟨W, hW, hzW, hWV₀⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
    (show π₁.base (ι.base z) ∈ (⟨V₀, hV₀⟩ : X.Opens) from hz0)
  have hWV : π₁ ⁻¹ᵁ W ≤ V := by
    intro u hu
    have : u ∈ π₁.base ⁻¹' V₀ := hWV₀ hu
    rw [hV₀e] at this; exact this

  obtain ⟨hs, hk⟩ := app_fst_tq p J₁ W hW
  obtain ⟨yt, hyt⟩ := hs (((pullback p (tq J₁)).presheaf.map (homOfLE hWV).op).hom y)
  have hay : π₁.app W (toW p W a * yt) = 0 := by
    rw [map_mul, hyt, app_toW, ← toW_res (π₁ ≫ p) hWV, ← map_mul, hy, map_zero]
  have hm := Ideal.map_mono h1 (hk _ hay)
  rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at hm
  obtain ⟨c, hc⟩ := hm
  have hyt' : yt = toW p W (a ^ (e + 1)) * c := by
    apply sub_eq_zero.1
    apply toW_mul_eq_zero p W ha
    rw [mul_sub, ← hc, map_pow, map_pow, pow_succ' _ (e + 1)]
    ring

  have hW2 : π₂ ⁻¹ᵁ W ≤ ι ⁻¹ᵁ V := by
    intro u hu
    apply hWV
    show π₁.base (ι.base u) ∈ W
    rw [← Scheme.Hom.comp_apply, hι]; exact hu
  have hW2' : π₂ ⁻¹ᵁ W ≤ ι ⁻¹ᵁ (π₁ ⁻¹ᵁ W) := by
    intro u hu
    show π₁.base (ι.base u) ∈ W
    rw [← Scheme.Hom.comp_apply, hι]; exact hu
  have hzW2 : z ∈ π₂ ⁻¹ᵁ W := by
    show π₂.base z ∈ W
    rw [← hι, Scheme.Hom.comp_apply]; exact hzW
  have e5 : ((pullback p (tq J₂)).presheaf.map (homOfLE hW2).op).hom ((ι.app V) y) = (π₂.app W) yt := by
    have a1 : ((pullback p (tq J₂)).presheaf.map (homOfLE hW2).op).hom ((ι.app V) y) =
        (ι.appLE V (π₂ ⁻¹ᵁ W) hW2) y := by
      rw [Scheme.Hom.app_eq_appLE, ← CommRingCat.comp_apply]
      erw [Scheme.Hom.appLE_map]
    have a2 : (ι.appLE V (π₂ ⁻¹ᵁ W) hW2) y =
        (ι.appLE (π₁ ⁻¹ᵁ W) (π₂ ⁻¹ᵁ W) hW2') (((pullback p (tq J₁)).presheaf.map (homOfLE hWV).op).hom y) := by
      rw [← CommRingCat.comp_apply]
      erw [Scheme.Hom.map_appLE]
    have a3 : (ι.appLE (π₁ ⁻¹ᵁ W) (π₂ ⁻¹ᵁ W) hW2') ((π₁.app W) yt) = (π₂.app W) yt := by
      rw [Scheme.Hom.app_eq_appLE, ← CommRingCat.comp_apply]
      erw [Scheme.Hom.appLE_comp_appLE]
      rw [appLE_of_eq hι, Scheme.Hom.app_eq_appLE]
    rw [a1, a2, ← hyt, a3]
  have hzero : ((pullback p (tq J₂)).presheaf.map (homOfLE hW2).op).hom ((ι.app V) y) = 0 := by
    rw [e5, hyt', map_mul, app_toW_of_mem p J₂ W h2, zero_mul]
  show (pullback p (tq J₂)).presheaf.germ _ z hz ((ι.app V) y) = (pullback p (tq J₂)).presheaf.germ _ z hz 0
  rw [← TopCat.Presheaf.germ_res_apply _ (homOfLE hW2) z hzW2, hzero, map_zero, map_zero]

end

end ReciprocityTheory.ChartRestriction.G.DVR.TG
end

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.TG

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

lemma resTop_scal {R : Type} [CommRing R] {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) (W : Y.Opens)
    (r : R) : resTop W (scal p r) = toW p W r := rfl

theorem sec_div {R : Type} [CommRing R] [IsDomain R] {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) [Flat p]
    {M : LB Y} (s : LB.Sec M) {a : R} (ha : a ≠ 0) {J : Ideal R} (hJ : J ≤ Ideal.span {a})
    (h0 : ∀ j, (pullback.fst p (tq J)).app _ (s.f j) = 0) :
    ∃ g : LB.Sec M, ∀ j, s.f j = toW p _ a * g.f j := by
  choose g hg using fun j => exists_div p ha hJ (M.U j) (s.f j) (h0 j)
  refine ⟨⟨g, fun i j => ?_⟩, hg⟩
  apply sub_eq_zero.1
  apply toW_mul_eq_zero p _ ha
  have c := s.compat i j
  rw [hg i, hg j, map_mul, map_mul, toW_res, toW_res] at c
  rw [mul_sub, sub_eq_zero, c]
  ring

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

lemma thickMap_fst (e : ℕ) : thickMap R I e G ≫ (fstG I (e + 1) G).left = (fstG I e G).left := by
  unfold thickMap fstG pullback.map
  simp only [Over.homMk_left]
  try simp

lemma pG_struct {e : ℕ} (g : GtCoord I D.toPre e G) :
    g.pG.left ≫ D.toPre.P.A.hom = (fstG I e G).left ≫ G.hom :=
  (Over.w g.pG).trans (Over.w (fstG I e G)).symm

end ReciprocityTheory.ChartRestriction.G.DVR.TG

namespace ReciprocityTheory.ChartRestriction.G.DVR.TG

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

lemma app_eq_zero_of_comp {X Y Z : Scheme.{0}} {f : X ⟶ Z} {g : X ⟶ Y} {h : Y ⟶ Z} (hf : g ≫ h = f)
    (W : Z.Opens) (x : Γ(Z, W)) (hx : g.app (h ⁻¹ᵁ W) (h.app W x) = 0) : f.app W x = 0 := by
  subst hf
  first
  | exact hx
  | (rw [Scheme.comp_app]; exact hx)
  | (simp only [Scheme.comp_app, CommRingCat.comp_apply]; exact hx)

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

def thickO (e : ℕ) : (Over.map (thick R I e)).obj (thickObj R I e G) ⟶
    (Over.map (thick R I (e + 1))).obj (thickObj R I (e + 1) G) :=
  Over.homMk (thickMap R I e G) (by
    show thickMap R I e G ≫ pullback.snd G.hom (thick R I (e + 1)) ≫ thick R I (e + 1) =
      pullback.snd G.hom (thick R I e) ≫ thick R I e
    rw [thickMap, pullback.lift_snd_assoc, Category.assoc, thickTrans_comp])

lemma thickO_pG (U : UnifPre I D A G) (e : ℕ) : thickO e ≫ (U.gt (e + 1)).pG = (U.gt e).pG :=
  Over.OverMorphism.ext (U.gt_q e)

lemma Oφ_thick (U : UnifPre I D A G) (e : ℕ) (α : D.toPre.X) (k : Fin 4) :
    thickMap R I e G ≫ D.toPre.Oφ (U.gt (e + 1)).pG α k = D.toPre.Oφ (U.gt e).pG α k := by
  have := WeightPf.Oφ_comp (thickO (G := G) (I := I) e) (U.gt (e + 1)).pG α k
  rw [thickO_pG] at this
  exact this

end ReciprocityTheory.ChartRestriction.G.DVR.TG
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.TG

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

lemma appLE_res {X Y : Scheme.{0}} (i0 : X ⟶ Y) {V1 W : Y.Opens} {V0 : X.Opens} (hV : V0 ≤ i0 ⁻¹ᵁ V1)
    (h1 : V1 ≤ W) (h0 : V0 ≤ i0 ⁻¹ᵁ W) (y : Γ(Y, W)) :
    (i0.appLE V1 V0 hV) ((Y.presheaf.map (homOfLE h1).op).hom y) =
      (X.presheaf.map (homOfLE h0).op).hom ((i0.app W).hom y) := by
  have e1 := i0.map_appLE hV (homOfLE h1).op
  have e2 : i0.app W ≫ X.presheaf.map (homOfLE h0).op = i0.appLE W V0 h0 := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]
  calc (i0.appLE V1 V0 hV) ((Y.presheaf.map (homOfLE h1).op).hom y)
      = (Y.presheaf.map (homOfLE h1).op ≫ i0.appLE V1 V0 hV).hom y := rfl
    _ = (i0.appLE W V0 h0).hom y := by rw [e1]
    _ = (i0.app W ≫ X.presheaf.map (homOfLE h0).op).hom y := by rw [e2]
    _ = _ := rfl

lemma appLE_pull {X Y Z : Scheme.{0}} (i0 : X ⟶ Y) (m : Y ⟶ Z) (m' : X ⟶ Z) (h : i0 ≫ m = m')
    {V1 : Y.Opens} {V0 : X.Opens} (hV : V0 ≤ i0 ⁻¹ᵁ V1) {W : Z.Opens} (h1 : V1 ≤ m ⁻¹ᵁ W)
    (h0 : V0 ≤ m' ⁻¹ᵁ W) (x : Γ(Z, W)) :
    (i0.appLE V1 V0 hV) ((Y.presheaf.map (homOfLE h1).op).hom ((m.app W).hom x)) =
      (X.presheaf.map (homOfLE h0).op).hom ((m'.app W).hom x) := by
  subst h
  have e1 : m.app W ≫ Y.presheaf.map (homOfLE h1).op = m.appLE W V1 h1 := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]
  have e2 : (i0 ≫ m).app W ≫ X.presheaf.map (homOfLE h0).op = (i0 ≫ m).appLE W V0 h0 := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]
  calc (i0.appLE V1 V0 hV) ((Y.presheaf.map (homOfLE h1).op).hom ((m.app W).hom x))
      = ((m.app W ≫ Y.presheaf.map (homOfLE h1).op) ≫ i0.appLE V1 V0 hV).hom x := rfl
    _ = ((i0 ≫ m).appLE W V0 h0).hom x := by rw [e1, Scheme.Hom.appLE_comp_appLE]
    _ = ((i0 ≫ m).app W ≫ X.presheaf.map (homOfLE h0).op).hom x := by rw [e2]
    _ = _ := rfl

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

def expL (U : UnifPre I D A G) (e : ℕ) (p : (PUnit.{1} → D.toPre.P.L.ι) × (PUnit.{1} → U.LG.L.ι))
    (j₁ : Fin 1 → U.LG.L.ι) (S : Finset D.toPre.X) (jf jt : D.toPre.X → Fin 4 → D.toPre.P.L.ι)
    (σ : H0 U.LG.L 1) : Γ((thickObj R I e G).left, U.expW e p j₁ S jf jt) :=
  (res (inf_le_left.trans inf_le_left :
      U.expW e p j₁ S jf jt ≤ (LB.div (D.toPre.P.L.pull (U.gt e).pG.left)
        (U.LG.L.pull (fstG I e G).left)).U p) ((U.w e).s p)).val ^ 1 *
    ((thickObj R I e G).left.presheaf.map (homOfLE (inf_le_left.trans inf_le_right :
      U.expW e p j₁ S jf jt ≤
        (fstG I e G).left ⁻¹ᵁ LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) j₁)).op).hom
      (((fstG I e G).left.app _).hom (σ.f j₁))

def expR (U : UnifPre I D A G) (e : ℕ) (p : (PUnit.{1} → D.toPre.P.L.ι) × (PUnit.{1} → U.LG.L.ι))
    (j₁ : Fin 1 → U.LG.L.ι) (S : Finset D.toPre.X) (jf jt : D.toPre.X → Fin 4 → D.toPre.P.L.ι)
    (f : ∀ α : D.toPre.X, D.toPre.SecB 1 α) : Γ((thickObj R I e G).left, U.expW e p j₁ S jf jt) :=
  ∑ α ∈ S.attach,
    ((thickObj R I e G).left.presheaf.map (homOfLE (U.expW_le_f e p j₁ jf jt α.2)).op).hom
        (((U.gt e).pG.left.app _).hom ((f α.1).f (jf α.1))) *
      (res (U.expWeight_le_chart_weight e p j₁ jf jt α.2) (((U.gt e).t α.1).s (jt α.1))).val


set_option maxHeartbeats 1000000 in
theorem expandsAt_of_div (U : UnifPre I D A G) [Flat G.hom] {ϖ : R} (hϖ : ϖ ≠ 0) (hI : I = Ideal.span {ϖ})
    (σ τ : H0 U.LG.L 1) (hστ : ∀ j, σ.f j = toW G.hom _ ϖ * τ.f j)
    (f g : ∀ α, D.toPre.SecB 1 α) (hfg : ∀ α j, (f α).f j = toW D.toPre.P.A.hom _ ϖ * (g α).f j)
    (e : ℕ) (h : U.ExpandsAt (e + 1) 1 σ f) : U.ExpandsAt e 1 τ g := by
  classical
  obtain ⟨S, hout, hmain⟩ := h
  have hι : thickMap R I e G ≫ pullback.fst G.hom (thick R I (e + 1)) = pullback.fst G.hom (thick R I e) :=
    thickMap_fst e
  have hq : thickMap R I e G ≫ (U.gt (e + 1)).pG.left = (U.gt e).pG.left := U.gt_q e
  have hJ1 : I ^ (e + 1 + 1) ≤ Ideal.span {ϖ ^ (e + 2)} := by
    rw [hI, Ideal.span_singleton_pow]
  have hJ2 : ϖ ^ (e + 1) ∈ I ^ (e + 1) := by
    rw [hI, Ideal.span_singleton_pow]; exact Ideal.subset_span rfl
  have van : ∀ (V : (thickObj R I (e + 1) G).left.Opens) (y : Γ((thickObj R I (e + 1) G).left, V)),
      toW (X := (thickObj R I (e + 1) G).left) ((fstG I (e + 1) G).left ≫ G.hom) V ϖ * y = 0 →
        (thickMap R I e G).app V y = 0 :=
    fun V y hy => vanish_of_mul G.hom hϖ e hJ1 hJ2 (thickMap R I e G) hι V y hy
  refine ⟨S, fun α hα j => ?_, fun p j₁ jf jt hj hcoh => ?_⟩
  · have h1 := hout α hα j
    erw [hfg α j, map_mul, app_toW, toW_congr (pG_struct _)] at h1
    exact app_eq_zero_of_comp hq _ _ (van _ _ h1)
  ·
    have hfam : ∀ z, (Sum.elim (fun _ : PUnit.{1} => (U.gt e).pG.left)
          (Sum.elim (fun a : S × Fin 4 => (U.gt e).pG.left ≫ D.toPre.famφB a.1.1 a.2)
            (fun a : S × Fin 4 => D.toPre.Oφ (U.gt e).pG a.1.1 a.2))) z =
        thickMap R I e G ≫ (Sum.elim (fun _ : PUnit.{1} => (U.gt (e + 1)).pG.left)
          (Sum.elim (fun a : S × Fin 4 => (U.gt (e + 1)).pG.left ≫ D.toPre.famφB a.1.1 a.2)
            (fun a : S × Fin 4 => D.toPre.Oφ (U.gt (e + 1)).pG a.1.1 a.2))) z := by
      rintro (z | z | z)
      · exact hq.symm
      · show (U.gt e).pG.left ≫ D.toPre.famφB z.1.1 z.2 =
          thickMap R I e G ≫ (U.gt (e + 1)).pG.left ≫ D.toPre.famφB z.1.1 z.2
        rw [← Category.assoc, hq]
      · exact (Oφ_thick U e z.1.1 z.2).symm
    have hcoh1 := fun a b (hab : (Sum.elim (fun _ : PUnit.{1} => (U.gt (e + 1)).pG.left)
          (Sum.elim (fun a : S × Fin 4 => (U.gt (e + 1)).pG.left ≫ D.toPre.famφB a.1.1 a.2)
            (fun a : S × Fin 4 => D.toPre.Oφ (U.gt (e + 1)).pG a.1.1 a.2))) a =
        (Sum.elim (fun _ : PUnit.{1} => (U.gt (e + 1)).pG.left)
          (Sum.elim (fun a : S × Fin 4 => (U.gt (e + 1)).pG.left ≫ D.toPre.famφB a.1.1 a.2)
            (fun a : S × Fin 4 => D.toPre.Oφ (U.gt (e + 1)).pG a.1.1 a.2))) b) =>
      hcoh a b (by rw [hfam a, hfam b, hab])
    have E := hmain p j₁ jf jt hj hcoh1
    have E' : expL U (e + 1) p j₁ S jf jt σ = expR U (e + 1) p j₁ S jf jt f := E
    show expL U e p j₁ S jf jt τ = expR U e p j₁ S jf jt g

    have hι' : thickMap R I e G ≫ (fstG I (e + 1) G).left = (fstG I e G).left := thickMap_fst e
    have hV : U.expW e p j₁ S jf jt ≤ thickMap R I e G ⁻¹ᵁ U.expW (e + 1) p j₁ S jf jt := by
      intro x hx
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hx
      refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
      · exact wchart_le_preimage D.toPre.P.L (thickMap R I e G) (fun _ => (U.gt (e + 1)).pG.left)
          (fun _ => (U.gt e).pG.left) (fun _ => hq.symm) p.1 h1
      · exact wchart_le_preimage U.LG.L (thickMap R I e G) (fun _ => (fstG I (e + 1) G).left)
          (fun _ => (fstG I e G).left) (fun _ => hι'.symm) p.2 h2
      · show (fstG I (e + 1) G).left.base ((thickMap R I e G).base x) ∈
          LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) j₁
        rw [← Scheme.Hom.comp_apply, hι']; exact h3
      · refine WeightPf.mem_finset_inf _ _ _ fun α hα => ?_
        have hx' := WeightPf.mem_of_finset_inf h4 hα
        refine ⟨?_, wchart_le_preimage D.toPre.P.L (thickMap R I e G) (D.toPre.Oφ (U.gt (e + 1)).pG α)
          (D.toPre.Oφ (U.gt e).pG α) (fun k => (Oφ_thick U e α k).symm) (jt α) hx'.2⟩
        show (U.gt (e + 1)).pG.left.base ((thickMap R I e G).base x) ∈
          LB.wchart D.toPre.P.L (D.toPre.famφB α) (jf α)
        rw [← Scheme.Hom.comp_apply, hq]; exact hx'.1
    set c1 := toW (X := (thickObj R I (e + 1) G).left) ((fstG I (e + 1) G).left ≫ G.hom)
      (U.expW (e + 1) p j₁ S jf jt) ϖ with hc1
    have hL1 : expL U (e + 1) p j₁ S jf jt σ = c1 * expL U (e + 1) p j₁ S jf jt τ := by
      simp only [expL]
      erw [hστ j₁, map_mul, map_mul, app_toW, toW_res]
      ring
    have hR1 : expR U (e + 1) p j₁ S jf jt f = c1 * expR U (e + 1) p j₁ S jf jt g := by
      simp only [expR, Finset.mul_sum]
      refine Finset.sum_congr rfl fun α _ => ?_
      erw [hfg α.1 (jf α.1), map_mul, map_mul, app_toW, toW_res, toW_congr (pG_struct _)]
      ring
    have hdiff : c1 * (expL U (e + 1) p j₁ S jf jt τ - expR U (e + 1) p j₁ S jf jt g) = 0 := by
      rw [mul_sub, ← hL1, ← hR1, E', sub_self]
    have hvan := van _ _ hdiff
    have hres : (thickMap R I e G).appLE _ _ hV
        (expL U (e + 1) p j₁ S jf jt τ - expR U (e + 1) p j₁ S jf jt g) = 0 := by
      show ((thickMap R I e G).app _ ≫ (thickObj R I e G).left.presheaf.map (homOfLE hV).op).hom _ = 0
      rw [CommRingCat.comp_apply, hvan, map_zero]
    have h0w : U.expW e p j₁ S jf jt ≤ thickMap R I e G ⁻¹ᵁ
        (LB.div (D.toPre.P.L.pull (U.gt (e + 1)).pG.left) (U.LG.L.pull (fstG I (e + 1) G).left)).U p :=
      fun x hx => (inf_le_left.trans inf_le_left :
        U.expW (e + 1) p j₁ S jf jt ≤ (LB.div (D.toPre.P.L.pull (U.gt (e + 1)).pG.left)
          (U.LG.L.pull (fstG I (e + 1) G).left)).U p) (hV hx)
    have hL2 : (thickMap R I e G).appLE _ _ hV (expL U (e + 1) p j₁ S jf jt τ) = expL U e p j₁ S jf jt τ := by
      simp only [expL, map_mul, map_pow]
      congr 1
      · congr 1
        rw [WeightPf.res_val, appLE_res (thickMap R I e G) hV _ h0w]
        exact congrArg Units.val (U.w_compat e p (U.expW e p j₁ S jf jt) h0w (inf_le_left.trans inf_le_left))
      · exact appLE_pull _ _ _ hι' hV _ _ _
    have ht : ∀ α : S, (thickMap R I e G).appLE _ _ hV
        (res (U.expWeight_le_chart_weight (e + 1) p j₁ jf jt α.2) (((U.gt (e + 1)).t α.1).s (jt α.1))).val =
        (res (U.expWeight_le_chart_weight e p j₁ jf jt α.2) (((U.gt e).t α.1).s (jt α.1))).val := by
      intro α
      have hfun : (fun k => thickMap R I e G ≫ D.toPre.Oφ (U.gt (e + 1)).pG α.1 k) =
          D.toPre.Oφ (U.gt e).pG α.1 := funext (Oφ_thick U e α.1)
      have hW : U.expW e p j₁ S jf jt ≤
          LB.wchart D.toPre.P.L (fun k => thickMap R I e G ≫ D.toPre.Oφ (U.gt (e + 1)).pG α.1 k) (jt α.1) := by
        rw [hfun]; exact U.expWeight_le_chart_weight e p j₁ jf jt α.2
      have hcohE : ∀ k1 k2, D.toPre.Oφ (U.gt e).pG α.1 k1 = D.toPre.Oφ (U.gt e).pG α.1 k2 →
          jt α.1 k1 = jt α.1 k2 :=
        fun k1 k2 h => hcoh (Sum.inr (Sum.inr (α, k1))) (Sum.inr (Sum.inr (α, k2))) h
      have C2 := LBVal.corr_val D.toPre.P.L _ _ _ _ _ _ (U.gt_t e α.1) (jt α.1) (jt α.1)
        (fun k1 k2 h => hcohE k1 k2 ((Oφ_thick U e α.1 k1).symm.trans (h.trans (Oφ_thick U e α.1 k2)))) hcohE
        (fun k k' h => hcohE k k' ((Oφ_thick U e α.1 k).symm.trans h)) (U.expW e p j₁ S jf jt)
        (le_inf hW (U.expWeight_le_chart_weight e p j₁ jf jt α.2))
      show ((thickObj R I (e + 1) G).left.presheaf.map (homOfLE (U.expWeight_le_chart_weight (e + 1) p j₁ jf jt α.2)).op ≫
          (thickMap R I e G).appLE _ _ hV).hom (((U.gt (e + 1)).t α.1).s (jt α.1)).val =
        ((thickObj R I e G).left.presheaf.map (homOfLE (U.expWeight_le_chart_weight e p j₁ jf jt α.2)).op).hom
          (((U.gt e).t α.1).s (jt α.1)).val
      erw [Scheme.Hom.map_appLE]
      rw [← LBVal.pullGen_val (L := D.toPre.P.L) _ _ ((U.gt (e + 1)).t α.1) (thickMap R I e G) (jt α.1) _ hW]
      exact C2
    have hR2 : (thickMap R I e G).appLE _ _ hV (expR U (e + 1) p j₁ S jf jt g) = expR U e p j₁ S jf jt g := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [expR, map_sum, map_mul]
      refine Finset.sum_congr rfl fun α _ => ?_
      congr 1
      · exact appLE_pull _ _ _ hq hV _ _ _
      · exact ht α
    rw [map_sub, hL2, hR2, sub_eq_zero] at hres
    exact hres

end ReciprocityTheory.ChartRestriction.G.DVR.TG

namespace ReciprocityTheory.ChartRestriction.G.DVR.TG

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

lemma flat_G (U : UnifPre I D A G) : Flat G.hom := by
  haveI := U.smooth
  exact AlgebraicGeometry.instFlatOfSmooth _

lemma flat_B : Flat D.toPre.P.A.hom := by
  haveI := D.toPre.P.smoothDim
  haveI : AlgebraicGeometry.Smooth D.toPre.P.A.hom :=
    AlgebraicGeometry.SmoothOfRelativeDimension.smooth D.toPre.P.g _
  exact AlgebraicGeometry.instFlatOfSmooth _

theorem expandsAt_scale (U : UnifPre I D A G) (c : R) (τ τ' : H0 U.LG.L 1)
    (hτ : ∀ j, τ'.f j = toW G.hom _ c * τ.f j)
    (g g' : ∀ α, D.toPre.SecB 1 α) (hg : ∀ α j, (g' α).f j = toW D.toPre.P.A.hom _ c * (g α).f j)
    (e : ℕ) (h : U.ExpandsAt e 1 τ g) : U.ExpandsAt e 1 τ' g' := by
  obtain ⟨S, hout, hmain⟩ := h
  refine ⟨S, fun α hα j => ?_, fun p j₁ jf jt hj hcoh => ?_⟩
  · erw [hg α j, map_mul, hout α hα j, mul_zero]
  · have E : expL U e p j₁ S jf jt τ = expR U e p j₁ S jf jt g := hmain p j₁ jf jt hj hcoh
    show expL U e p j₁ S jf jt τ' = expR U e p j₁ S jf jt g'
    set c1 := toW (X := (thickObj R I e G).left) ((fstG I e G).left ≫ G.hom) (U.expW e p j₁ S jf jt) c
    have hL : expL U e p j₁ S jf jt τ' = c1 * expL U e p j₁ S jf jt τ := by
      simp only [expL]
      erw [hτ j₁, map_mul, map_mul, app_toW, toW_res]
      ring
    have hR : expR U e p j₁ S jf jt g' = c1 * expR U e p j₁ S jf jt g := by
      simp only [expR, Finset.mul_sum]
      refine Finset.sum_congr rfl fun α _ => ?_
      erw [hg α.1 (jf α.1), map_mul, map_mul, app_toW, toW_res, toW_congr (pG_struct _)]
      ring
    rw [hL, hR, E]

theorem expand_div_one (U : UnifPre I D A G) (hWI : WeightIndepSt) {ϖ : R} (hϖ : ϖ ≠ 0)
    (hI : I = Ideal.span {ϖ}) (σ τ : H0 U.LG.L 1) (hστ : ∀ j, σ.f j = toW G.hom _ ϖ * τ.f j)
    (f : ∀ α, D.toPre.SecB 1 α) (hf : ∀ e, U.ExpandsAt e 1 σ f) :
    ∃ g : ∀ α, D.toPre.SecB 1 α, (∀ α j, (f α).f j = toW D.toPre.P.A.hom _ ϖ * (g α).f j) ∧
      ∀ e, U.ExpandsAt e 1 τ g := by
  have := flat_G U
  have := flat_B (D := D)
  have hϖI : ϖ ∈ I ^ (0 + 1) := by rw [hI, zero_add, pow_one]; exact Ideal.mem_span_singleton_self ϖ
  have hσ0 : ∀ j, ((fstG I 0 G).left.app _).hom (σ.f j) = 0 := by
    intro j
    rw [hστ, map_mul]
    erw [app_toW_of_mem G.hom (I ^ (0 + 1)) _ hϖI, zero_mul]
  have hpG := hWI R I D A G U 0 1 σ f hσ0 (hf 0)
  have hB : ∀ α j, (pullback.fst D.toPre.P.A.hom (thick R I 0)).app _ ((f α).f j) = 0 := by
    intro α j
    have := (U.gt 0).q_flat
    have := (U.gt 0).q_surj
    apply app_injective_of_flat_surj (U.gt 0).q.left
    rw [map_zero]
    have h := hpG α j
    have e : (U.gt 0).pG.left = (U.gt 0).q.left ≫ pullback.fst D.toPre.P.A.hom (thick R I 0) := rfl
    rw [e, Scheme.Hom.comp_app] at h
    exact h
  choose g hg using fun α => sec_div D.toPre.P.A.hom (f α) hϖ (J := I ^ (0 + 1))
    (by rw [hI, zero_add, pow_one]) (hB α)
  exact ⟨g, hg, fun e => expandsAt_of_div U hϖ hI σ τ hστ f g hg e (hf (e + 1))⟩

theorem expand_div_pow (U : UnifPre I D A G) (hWI : WeightIndepSt) {ϖ : R} (hϖ : ϖ ≠ 0)
    (hI : I = Ideal.span {ϖ}) (n : ℕ) : ∀ (σ τ : H0 U.LG.L 1), (∀ j, σ.f j = toW G.hom _ (ϖ ^ n) * τ.f j) →
    ∀ (f : ∀ α, D.toPre.SecB 1 α), (∀ e, U.ExpandsAt e 1 σ f) →
    ∃ g : ∀ α, D.toPre.SecB 1 α, (∀ α j, (f α).f j = toW D.toPre.P.A.hom _ (ϖ ^ n) * (g α).f j) ∧
      ∀ e, U.ExpandsAt e 1 τ g := by
  induction n with
  | zero =>
    intro σ τ hστ f hf
    refine ⟨f, fun α j => by rw [pow_zero, map_one, _root_.one_mul], fun e => ?_⟩
    have : σ = τ := SecOps.sec_ext fun j => by rw [hστ, pow_zero, map_one, _root_.one_mul]
    rw [← this]; exact hf e
  | succ n ih =>
    intro σ τ hστ f hf
    let σ' : H0 U.LG.L 1 := SecOps.secScale (scal G.hom (ϖ ^ n)) τ
    have h1 : ∀ j, σ.f j = toW G.hom _ ϖ * σ'.f j := fun j => by
      rw [hστ]
      show _ = _ * (toW G.hom _ (ϖ ^ n) * τ.f j)
      rw [pow_succ', map_mul, _root_.mul_assoc]
    obtain ⟨g1, hg1, he1⟩ := expand_div_one U hWI hϖ hI σ σ' h1 f hf
    obtain ⟨g, hg, he⟩ := ih σ' τ (fun j => rfl) g1 he1
    refine ⟨g, fun α j => ?_, he⟩
    rw [hg1, hg, pow_succ', map_mul, _root_.mul_assoc]

end ReciprocityTheory.ChartRestriction.G.DVR.TG
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.TG

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

def pullSec' {X Y Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (s : LB.Sec (LB.LinComb L φ ε)) (h : Z ⟶ Y) (φ' : K → (Z ⟶ X)) (hφ : ∀ k, φ' k = h ≫ φ k) :
    LB.Sec (LB.LinComb L φ' ε) := by
  have e : φ' = fun k => h ≫ φ k := funext hφ
  subst e
  exact pullSec L φ ε s h

lemma pullSec'_f {X Y Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (s : LB.Sec (LB.LinComb L φ ε)) (h : Z ⟶ Y) (φ' : K → (Z ⟶ X)) (hφ : ∀ k, φ' k = h ≫ φ k)
    (j : K → L.ι) :
    (pullSec' L φ ε s h φ' hφ).f j =
      (Z.presheaf.map (homOfLE (wchart_le_preimage L h φ φ' hφ j)).op).hom ((h.app _).hom (s.f j)) := by
  obtain rfl : φ' = fun k => h ≫ φ k := funext hφ
  rfl

lemma map_inj_of_le_ge {X : Scheme.{0}} {V W : X.Opens} (h1 : W ≤ V) (h2 : V ≤ W) {a b : Γ(X, V)}
    (h : (X.presheaf.map (homOfLE h1).op).hom a = (X.presheaf.map (homOfLE h1).op).hom b) : a = b := by
  obtain rfl : W = V := le_antisymm h1 h2
  have e : homOfLE h1 = 𝟙 W := Subsingleton.elim _ _
  rw [e] at h
  simpa using h

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

def secK (U : UnifPre I D A G) (s : H0 U.LG.L 1) : U.SecK 1 :=
  pullSec' U.LG.L _ _ s (pullback.fst G.hom (jK R)) _ (fun _ => (Category.comp_id _).symm)

lemma secK_rel (U : UnifPre I D A G) (s : H0 U.LG.L 1) :
    GeneratorPullback.SecScal U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) (fun _ => ((1 : ℕ) : ℤ)) (secK U s)
      (fun _ : Fin 1 => 𝟙 G.left) (fun _ => ((1 : ℕ) : ℤ)) s (pullback.fst G.hom (jK R)) 1 := by
  intro j₁ j₂ hc
  have hj : j₁ = j₂ := funext fun k => by
    rw [Subsingleton.elim k 0]
    exact hc (Sum.inl 0) (Sum.inr 0) (Category.comp_id _).symm
  subst hj
  rw [secK, pullSec'_f]
  have h1 : resTop (LB.wchart U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) j₁ ⊓
      LB.wchart U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R) ≫ 𝟙 G.left) j₁)
      (1 : Γ(pullback G.hom (jK R), ⊤)) = 1 := map_one _
  rw [h1, _root_.one_mul, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem sec_eq_of_secScal (U : UnifPre I D A G) [Flat G.hom] (s σ : H0 U.LG.L 1) (sK : U.SecK 1) (r : R)
    (h1 : GeneratorPullback.SecScal U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) (fun _ => ((1 : ℕ) : ℤ)) sK
      (fun _ : Fin 1 => 𝟙 G.left) (fun _ => ((1 : ℕ) : ℤ)) s (pullback.fst G.hom (jK R)) 1)
    (h2 : GeneratorPullback.SecScal U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) (fun _ => ((1 : ℕ) : ℤ)) sK
      (fun _ : Fin 1 => 𝟙 G.left) (fun _ => ((1 : ℕ) : ℤ)) σ (pullback.fst G.hom (jK R))
      (scal (pullback.snd G.hom (jK R) ≫ jK R) r)) :
    ∀ j, σ.f j = toW G.hom _ r * s.f j := by
  intro (j : Fin 1 → U.LG.L.ι)
  have hc : LB.Coh U.LG.L (Sum.elim (fun _ : Fin 1 => pullback.fst G.hom (jK R))
      (fun k : Fin 1 => pullback.fst G.hom (jK R) ≫ (fun _ : Fin 1 => 𝟙 G.left) k)) (Sum.elim j j) := by
    intro a b _
    rcases a with a | a <;> rcases b with b | b <;> exact congrArg j (Subsingleton.elim _ _)
  have e1 := h1 j j hc
  have e2 := h2 j j hc
  have h1' : resTop (LB.wchart U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) j ⊓
      LB.wchart U.LG.L (fun k : Fin 1 => pullback.fst G.hom (jK R) ≫ (fun _ : Fin 1 => 𝟙 G.left) k) j)
      (1 : Γ(pullback G.hom (jK R), ⊤)) = 1 := map_one _
  rw [h1', _root_.one_mul] at e1
  rw [← e1] at e2
  have hle : pullback.fst G.hom (jK R) ⁻¹ᵁ LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) j ≤
      LB.wchart U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) j ⊓
        LB.wchart U.LG.L (fun k : Fin 1 => pullback.fst G.hom (jK R) ≫ (fun _ : Fin 1 => 𝟙 G.left) k) j :=
    fun x hx => ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx k, Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx k⟩
  apply app_fst_jF_injective G.hom
  apply map_inj_of_le_ge (inf_le_right.trans (wchart_comp_le _ _ j)) hle
  refine e2.trans ?_
  have e3 : (((pullback.fst G.hom (jK R)).app (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) j)).hom
      (toW G.hom (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) j) r *
        (show Γ(G.left, LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) j) from s.f j))) =
      toW (pullback.fst G.hom (jK R) ≫ G.hom) _ r *
        ((pullback.fst G.hom (jK R)).app (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) j)).hom
          (show Γ(G.left, LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) j) from s.f j) := by
    rw [map_mul, app_toW]
  erw [e3, map_mul, toW_res, resTop_scal, toW_congr pullback.condition.symm]

end ReciprocityTheory.ChartRestriction.G.DVR.TG
