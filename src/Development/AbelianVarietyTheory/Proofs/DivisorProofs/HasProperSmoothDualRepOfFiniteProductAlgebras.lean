module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechPicardGlueFiniteDisjointCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingEqOneTrivialOnAxis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSemiAbelianUniformisationOfFiniteExtTrans

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfHasRepUnit
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon.Model

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem fam_ev {U T : Over S} {M : LB (A ⊗ U).left} (h : Fam A M) (u : T ⟶ U) :
    Fam A (ev M (fst A T) (snd A T ≫ u)) := by
  have hM : (ev M (fst A T) (snd A T ≫ u)).IsLB := pull_isLB h.isLB _
  refine ⟨hM, (isAdditive_iff hM).2 fun Y a a' t ↦ ?_⟩
  simp only [evc_ev h.isLB, lift_fst, lift_snd_assoc]
  exact (isAdditive_iff h.isLB).1 h.add Y a a' _

theorem rep_ext {B S' Y : Over S} {b : B ⟶ S'} {P : LB (A ⊗ B).left} (h : Rep A b P) {u u' : Y ⟶ B}
    (hb : u ≫ b = u' ≫ b) (e : Same A P P u u') : u = u' := by
  have hu := fam_ev h.fam u
  exact (h.univ Y (u ≫ b) _ hu).unique ⟨rfl, (cls_eq_iff hu.isLB hu.isLB).1 rfl⟩ ⟨hb.symm, e⟩




end GlobalTheory.DualCon.Model
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardEqZeroOfTrivialOnDisjointCover
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardEqZeroOfTrivialOnDisjointCover
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PicDisj

open TopologicalSpace

theorem map_gm {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)ˣ) :
    Units.map (f.stalkMap y).hom.toMonoidHom (gm (𝟙 X) (f y) U a) = gm f y U a := by
  refine Units.ext ?_
  rw [gm, gm, dite_eq_left h, dite_eq_left (show (𝟙 X : X ⟶ X) (f y) ∈ U from h)]
  exact Scheme.Hom.germ_stalkMap_apply f U y h a.val

theorem gm_image {X Y : Scheme.{0}} (f : Y ⟶ X) [IsOpenImmersion f] (y : Y) (V : Y.Opens) (h : y ∈ V) (a : Γ(Y, V)ˣ) :
    gm f y (f ''ᵁ V) (Units.map (f.appIso V).inv.hom.toMonoidHom a) = gm (𝟙 Y) y V a := by
  refine Units.ext ?_
  have h' : f y ∈ f ''ᵁ V := ⟨y, h, rfl⟩
  rw [gm, gm, dite_eq_left h', dite_eq_left (show (𝟙 Y : Y ⟶ Y) y ∈ V from h)]
  change (Y.presheaf.germ (f ⁻¹ᵁ (f ''ᵁ V)) y h').hom (((f.appIso V).inv ≫ f.app (f ''ᵁ V)).hom a.val) =
    (Y.presheaf.germ V y h).hom a.val
  rw [Scheme.Hom.appIso_inv_app]
  exact Y.presheaf.germ_res_apply _ y _ _

theorem exists_gen_of_rel {Y : Scheme.{0}} {N : LB Y} (hN : N.IsLB) (P : N.ι → ∀ y : Y, (Y.presheaf.stalk y)ˣ → Prop)
    (loc : ∀ p, ∀ y ∈ N.U p, ∃ W : Y.Opens, W ≤ N.U p ∧ y ∈ W ∧ ∃ s : Γ(Y, W)ˣ, ∀ y' ∈ W, P p y' (gm (𝟙 Y) y' W s))
    (cmp : ∀ p q y u u', y ∈ N.U p → y ∈ N.U q → P p y u → P q y u' → u = gm (𝟙 Y) y _ (N.g p q) * u') :
    ∃ t : N.Gen, t.IsGen := by
  have uniq : ∀ p y u u', y ∈ N.U p → P p y u → P p y u' → u = u' := fun p y u u' hy h h' => by
    have e := gm_cocycle hN (𝟙 Y) y hy hy hy
    rw [cmp p p y u u' hy hy h h', mul_eq_left.1 e, _root_.one_mul]
  have key : ∀ p, ∃ a : Γ(Y, N.U p)ˣ, ∀ y ∈ N.U p, P p y (gm (𝟙 Y) y _ a) := fun p => by
    choose W hW hy s hs using fun y : (N.U p : Set Y) => loc p y.1 y.2
    have cp : ∀ k l, res (inf_le_left : W k ⊓ W l ≤ W k) (s k) = res inf_le_right (s l) := fun k l =>
      unit_ext fun y h => by
        rw [gm_res _ y _ h, gm_res _ y _ h]
        exact uniq p y _ _ (hW k h.1) (hs k y h.1) (hs l y h.2)
    have hc : N.U p ≤ iSup W := fun x hx => Opens.mem_iSup.2 ⟨⟨x, hx⟩, hy _⟩
    obtain ⟨b, hb, -⟩ := Y.sheaf.existsUnique_gluing' W (N.U p) (fun k => homOfLE (hW k)) hc (fun k => (s k).val)
      fun k l => congrArg Units.val (cp k l)
    have hu : IsUnit (M := Γ(Y, N.U p)) b := Y.toRingedSpace.isUnit_of_isUnit_germ _ _ fun x hx => by
      have := (s ⟨x, hx⟩).isUnit.map (Y.presheaf.germ _ x (hy ⟨x, hx⟩)).hom
      rw [← hb] at this
      exact (Y.presheaf.germ_res_apply (homOfLE (hW ⟨x, hx⟩)) x (hy ⟨x, hx⟩) b) ▸ this
    refine ⟨hu.unit, fun y h => ?_⟩
    have e : res (hW ⟨y, h⟩) hu.unit = s ⟨y, h⟩ := Units.ext (hb _)
    rw [← gm_res _ y (hW ⟨y, h⟩) (hy ⟨y, h⟩), e]
    exact hs _ y (hy _)
  choose a ha using key
  exact ⟨⟨a⟩, (isGen_iff_germ _).2 fun y i j hi hj => cmp i j y _ _ hi hj (ha i y hi) (ha j y hj)⟩

theorem eq_zero_of_pull_eq_zero : ∀ {Y : Scheme.{0}} {κ : Type} [Finite κ] {Z : κ → Scheme.{0}} (f : ∀ i, Z i ⟶ Y) [∀ i, IsOpenImmersion (f i)], (⨆ i, (f i).opensRange = ⊤) → (Pairwise fun i i' => Disjoint (f i).opensRange (f i').opensRange) → ∀ d : Pic Y, (∀ i, GlobalTheory.CechPic.pull (f i) d = 0) → d = 0 := by
  intro Y κ _ Z f _ hcov hdis d hd
  obtain ⟨L, hL, rfl⟩ := cls_surj d
  choose t ht using fun i => (cls_eq_zero_iff (pull_isLB hL (f i))).1 (hd i)
  have surj : ∀ y : Y, ∃ i z, f i z = y := fun y => by
    have : y ∈ ⨆ i, (f i).opensRange := by rw [hcov]; trivial
    obtain ⟨i, z, hz⟩ := Opens.mem_iSup.1 this
    exact ⟨i, z, hz⟩
  refine (cls_eq_zero_iff hL).2 (exists_gen_of_rel hL (fun p y u => ∀ i (z : Z i) (u' : (Y.presheaf.stalk (f i z))ˣ),
    f i z = y → HEq u' u → Units.map ((f i).stalkMap z).hom.toMonoidHom u' =
      gm (𝟙 _) z ((L.pull (f i)).U fun _ => p) ((t i).s fun _ => p)) ?_ ?_)
  · intro p y hy
    obtain ⟨i, z, rfl⟩ := surj y
    refine ⟨f i ''ᵁ ((L.pull (f i)).U fun _ => p), ?_, ⟨z, mem_pull.2 hy, rfl⟩,
      Units.map ((f i).appIso _).inv.hom.toMonoidHom ((t i).s fun _ => p), ?_⟩
    · rintro _ ⟨w, hw, rfl⟩
      exact mem_pull.1 hw
    · rintro y' ⟨w, hw, hy'⟩ j z' u' rfl hu
      obtain rfl : i = j := by
        by_contra hne
        have hm : f j z' ∈ (f i).opensRange ⊓ (f j).opensRange := ⟨⟨w, hy'⟩, ⟨z', rfl⟩⟩
        rw [(hdis hne).eq_bot] at hm
        exact hm
      obtain rfl : w = z' := (f i).isOpenEmbedding.injective hy'
      rw [eq_of_heq hu, map_gm (f i) w _ (show f i w ∈ f i ''ᵁ ((L.pull (f i)).U fun _ => p) from ⟨w, hw, rfl⟩), gm_image _ _ _ hw]
  · intro p q y u u' hp hq h h'
    obtain ⟨i, z, rfl⟩ := surj y
    apply Units.map_injective (f := ((f i).stalkMap z).hom.toMonoidHom)
      (ConcreteCategory.bijective_of_isIso ((f i).stalkMap z)).1
    rw [map_mul, h i z u rfl HEq.rfl, h' i z u' rfl HEq.rfl, map_gm (f i) z (L.U p ⊓ L.U q) ⟨hp, hq⟩,
      (isGen_iff_germ _).1 (ht i) z (fun _ => p) (fun _ => q) (mem_pull.2 hp) (mem_pull.2 hq),
      gm_pull_g L (f i) (𝟙 _) z _ _ (mem_pull.2 hp) (mem_pull.2 hq), Category.id_comp]

end GlobalTheory.PicDisj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardEqZeroOfTrivialOnDisjointCoverStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechPicard_eq_zero_of_trivial_on_disjoint_cover : ∀ {Y : Scheme.{0}} {κ : Type} [Finite κ] {Z : κ → Scheme.{0}} (f : ∀ i, Z i ⟶ Y) [∀ i, IsOpenImmersion (f i)], (⨆ i, (f i).opensRange = ⊤) → (Pairwise fun i i' => Disjoint (f i).opensRange (f i').opensRange) → ∀ d : Pic Y, (∀ i, GlobalTheory.CechPic.pull (f i) d = 0) → d = 0 := by
  first | exact @GlobalTheory.PicDisj.eq_zero_of_pull_eq_zero | exact GlobalTheory.PicDisj.eq_zero_of_pull_eq_zero | (intros; apply GlobalTheory.PicDisj.eq_zero_of_pull_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvcCompOfIso
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon.ProdGlue

theorem evc_comp_of_iso {S : Scheme.{0}} {A B' B Y : Over S} (j : B' ⟶ B) {P : LB (A ⊗ B).left} (hP : P.IsLB)
    {Q : LB (A ⊗ B').left} (hQ : Q.IsLB) (h : LBIso (P.pull (A ◁ j).left) Q) (a : Y ⟶ A) (u : Y ⟶ B') :
    evc hP a (u ≫ j) = evc hQ a u := by
  have e : cls Q hQ = CechPic.pull (A ◁ j).left (cls P hP) :=
    ((cls_eq_iff (pull_isLB hP _) hQ).2 h).symm.trans (cls_pull hP _ _)
  rw [evc, evc, e, ← pull_comp, ← Over.comp_left, lift_whiskerLeft]

end GlobalTheory.DualCon.ProdGlue
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointDisjointUnionRepresentingAdditiveFami
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointDisjointUnionRepresentingAdditiveFami
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon.ProdGlue

theorem opens_disjoint_of {Y : Scheme.{0}} {U U' : Y.Opens} (h : ∀ z, z ∈ U → z ∉ U') : Disjoint U U' :=
  disjoint_iff.2 (eq_bot_iff.2 fun z hz ↦ (h z hz.1 hz.2).elim)

theorem not_mem_of_disjoint {Y : Scheme.{0}} {U U' : Y.Opens} (h : Disjoint U U') {z : Y} (hz : z ∈ U)
    (hz' : z ∈ U') : False := by
  have := h.le_bot (show z ∈ U ⊓ U' from ⟨hz, hz'⟩)
  simpa using this

theorem rep_exists {S : Scheme.{0}} (A : Over S) [GrpObj A] {κ : Type} [Finite κ] (X : Over S)
    (V : κ → X.left.Opens) (hV : ⨆ i, V i = ⊤) (hVd : Pairwise fun i i' => Disjoint (V i) (V i'))
    (Bt : Over S) (B : κ → Over S) (j : ∀ i, B i ⟶ Bt) [∀ i, IsOpenImmersion (j i).left]
    (hj : ⨆ i, (j i).left.opensRange = ⊤)
    (hjd : Pairwise fun i i' => Disjoint (j i).left.opensRange (j i').left.opensRange)
    (b : ∀ i, B i ⟶ Over.mk ((V i).ι ≫ X.hom)) (bt : Bt ⟶ X) (hb : ∀ i, j i ≫ bt = b i ≫ Over.homMk (V i).ι)
    (P : ∀ i, LB (A ⊗ B i).left) (Pt : LB (A ⊗ Bt).left) (hP : ∀ i, Rep A (b i) (P i)) (hPt : Pt.IsLB)
    (hiso : ∀ i, LBIso (Pt.pull (A ◁ j i).left) (P i)) (T : Over S) (t : T ⟶ X) (N : LB (A ⊗ T).left)
    (hN : Fam A N) : ∃ x : T ⟶ Bt, x ≫ bt = t ∧ LBIso N (ev Pt (fst A T) (snd A T ≫ x)) := by
  let W : κ → T.left.Opens := fun i ↦ t.left ⁻¹ᵁ V i
  let Ti : κ → Over S := fun i ↦ Over.mk ((W i).ι ≫ T.hom)
  let w : ∀ i, Ti i ⟶ T := fun i ↦ Over.homMk (W i).ι
  let ti : ∀ i, Ti i ⟶ Over.mk ((V i).ι ≫ X.hom) := fun i ↦ Over.homMk (t.left ∣_ V i) (by
    simp [Ti, W, morphismRestrict_ι_assoc])
  have hti : ∀ i, ti i ≫ Over.homMk (V i).ι = w i ≫ t := fun i ↦ by
    ext1; simp [ti, w, W, morphismRestrict_ι]
  have hNi : ∀ i, Fam A (ev N (fst A (Ti i)) (snd A (Ti i) ≫ w i)) := fun i ↦ Model.fam_ev hN (w i)
  choose x hx _ using fun i ↦ (hP i).univ (Ti i) (ti i) _ (hNi i)
  have hWc : ⨆ i, (W i).ι.opensRange = ⊤ := by
    refine eq_top_iff.2 fun z _ ↦ ?_
    have : t.left z ∈ ⨆ i, V i := hV ▸ trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 this
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, by simpa [W] using hi⟩
  have hWd : _root_.Pairwise fun i i' ↦ Disjoint (W i).ι.opensRange (W i').ι.opensRange := by
    intro i i' h
    refine opens_disjoint_of fun z hz hz' ↦ ?_
    simp only [Scheme.Opens.opensRange_ι, W] at hz hz'
    exact not_mem_of_disjoint (hVd h) hz hz'
  obtain ⟨hT⟩ := nonempty_isColimit_cofanMk_of (fun i ↦ (W i).ι) hWc hWd
  let xl : T.left ⟶ Bt.left := Cofan.IsColimit.desc hT fun i ↦ (x i).left ≫ (j i).left
  have hxl : ∀ i, (W i).ι ≫ xl = (x i).left ≫ (j i).left := fun i ↦ Cofan.IsColimit.fac hT _ i
  have hxo : xl ≫ Bt.hom = T.hom := Cofan.IsColimit.hom_ext hT _ _ fun i ↦ by
    change (W i).ι ≫ _ = (W i).ι ≫ _
    rw [reassoc_of% hxl i, Over.w (j i), Over.w (x i)]
    rfl
  let xx : T ⟶ Bt := Over.homMk xl hxo
  have wxx : ∀ i, w i ≫ xx = x i ≫ j i := fun i ↦ by
    ext1
    simp only [Over.comp_left, Over.homMk_left, w, xx]
    exact hxl i
  have hxt : xx ≫ bt = t := by
    ext1
    refine Cofan.IsColimit.hom_ext hT _ _ fun i ↦ ?_
    change (W i).ι ≫ _ = (W i).ι ≫ _
    have e : w i ≫ xx ≫ bt = w i ≫ t := by
      rw [reassoc_of% wxx i, hb i, reassoc_of% (hx i).1, hti i]
    simpa [w, xx] using congrArg (fun q ↦ q.left) e
  refine ⟨xx, hxt, ?_⟩
  have hNl := hN.isLB
  refine (same_id_iff hNl hPt xx).1 ((same_iff hNl hPt _ _).2 ?_)
  have hwo : ∀ i, IsOpenImmersion (w i).left := fun i ↦ by
    show IsOpenImmersion (W i).ι; infer_instance
  have hwa : ∀ i, IsOpenImmersion (A ◁ w i).left := fun i ↦
    (@isOpenImmersion_whiskerLeft_left_and_range _ A _ _ (w i) (hwo i)).1
  have hwr : ∀ i z, z ∈ (A ◁ w i).left.opensRange ↔ (snd A T).left z ∈ W i := fun i z ↦ by
    have := (@isOpenImmersion_whiskerLeft_left_and_range _ A _ _ (w i) (hwo i)).2
    change z ∈ Set.range (A ◁ w i).left ↔ _
    rw [this, Set.mem_preimage]
    change _ ∈ Set.range (W i).ι ↔ _
    rw [Scheme.Opens.range_ι]
    rfl
  rw [← sub_eq_zero]
  refine GlobalTheory.T.cechPicard_eq_zero_of_trivial_on_disjoint_cover (fun i ↦ (A ◁ w i).left) ?_ ?_ _ fun i ↦ ?_
  · refine eq_top_iff.2 fun z _ ↦ ?_
    have : t.left ((snd A T).left z) ∈ ⨆ i, V i := hV ▸ trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 this
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, (hwr i z).2 hi⟩
  · intro i i' h
    refine opens_disjoint_of fun z hz hz' ↦ ?_
    exact not_mem_of_disjoint (hVd h) ((hwr i z).1 hz) ((hwr i' z).1 hz')
  · rw [map_sub, pull_evc, pull_evc, sub_eq_zero]
    simp only [whiskerLeft_fst, whiskerLeft_snd_assoc, whiskerLeft_snd, Category.comp_id]
    rw [wxx i, ← Category.assoc, evc_comp_of_iso (j i) hPt (hP i).fam.isLB (hiso i)]
    exact (cls_eq_iff (hNi i).isLB (pull_isLB (hP i).fam.isLB _)).2 (hx i).2

end GlobalTheory.DualCon.ProdGlue
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointDisjointUnionRepresentingAdditiveFamiStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_point_disjointUnion_representingAdditiveFamily : ∀ {S : Scheme.{0}} (A : Over S) [GrpObj A] {κ : Type} [Finite κ] (X : Over S) (V : κ → X.left.Opens), (⨆ i, V i = ⊤) → (Pairwise fun i i' => Disjoint (V i) (V i')) → ∀ (Bt : Over S) (B : κ → Over S) (j : ∀ i, B i ⟶ Bt) [∀ i, IsOpenImmersion (j i).left], (⨆ i, (j i).left.opensRange = ⊤) → (Pairwise fun i i' => Disjoint (j i).left.opensRange (j i').left.opensRange) → ∀ (b : ∀ i, B i ⟶ Over.mk ((V i).ι ≫ X.hom)) (bt : Bt ⟶ X), (∀ i, j i ≫ bt = b i ≫ Over.homMk (V i).ι) → ∀ (P : ∀ i, LB (A ⊗ B i).left) (Pt : LB (A ⊗ Bt).left), (∀ i, Rep A (b i) (P i)) → Pt.IsLB → (∀ i, LBIso (Pt.pull (A ◁ j i).left) (P i)) → ∀ (T : Over S) (t : T ⟶ X) (N : LB (A ⊗ T).left), Fam A N → ∃ x : T ⟶ Bt, x ≫ bt = t ∧ LBIso N (ev Pt (fst A T) (snd A T ≫ x)) := by
  first | exact @GlobalTheory.DualCon.ProdGlue.rep_exists | exact GlobalTheory.DualCon.ProdGlue.rep_exists | (intros; apply GlobalTheory.DualCon.ProdGlue.rep_exists <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointDisjointUnionRepresentingFamilyUnique
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointDisjointUnionRepresentingFamilyUnique
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualCon.ProdGlue

theorem same_precomp {S : Scheme.{0}} {A T U Y Z : Over S} {N : LB (A ⊗ T).left} {M : LB (A ⊗ U).left}
    (hN : N.IsLB) (hM : M.IsLB) {y : Y ⟶ T} {u : Y ⟶ U} (z : Z ⟶ Y)
    (e : Same A N M y u) : Same A N M (z ≫ y) (z ≫ u) := by
  have e' := congrArg (CechPic.pull (lift (fst A Z) (snd A Z ≫ z)).left) ((same_iff hN hM _ _).1 e)
  rw [pull_evc, pull_evc, lift_fst, lift_snd_assoc, lift_snd_assoc, Category.assoc, Category.assoc] at e'
  exact (same_iff hN hM _ _).2 e'

theorem eq_of_same_of_disjoint_cover : ∀ {S : Scheme.{0}} (A : Over S) [GrpObj A] {κ : Type} [Finite κ] (X : Over S) (V : κ → X.left.Opens), (⨆ i, V i = ⊤) → (Pairwise fun i i' => Disjoint (V i) (V i')) → ∀ (Bt : Over S) (B : κ → Over S) (j : ∀ i, B i ⟶ Bt) [∀ i, IsOpenImmersion (j i).left], (⨆ i, (j i).left.opensRange = ⊤) → (Pairwise fun i i' => Disjoint (j i).left.opensRange (j i').left.opensRange) → ∀ (b : ∀ i, B i ⟶ Over.mk ((V i).ι ≫ X.hom)) (bt : Bt ⟶ X), (∀ i, j i ≫ bt = b i ≫ Over.homMk (V i).ι) → ∀ (P : ∀ i, LB (A ⊗ B i).left) (Pt : LB (A ⊗ Bt).left), (∀ i, Rep A (b i) (P i)) → Pt.IsLB → (∀ i, LBIso (Pt.pull (A ◁ j i).left) (P i)) → ∀ (T : Over S) (x y : T ⟶ Bt), x ≫ bt = y ≫ bt → Same A Pt Pt x y → x = y := by
  intro S A _ κ _ X V hV hVd Bt B j _ hj hjd b bt hb P Pt hP hPt hPi T x y hxy e

  have mem : ∀ i (p : Bt.left), bt.left p ∈ V i → p ∈ Set.range (j i).left := by
    intro i p hp
    have hp' : p ∈ (⨆ i', (j i').left.opensRange) := by rw [hj]; trivial
    obtain ⟨i', q, rfl⟩ := (TopologicalSpace.Opens.mem_iSup.1 hp')
    have h1 : bt.left ((j i').left q) ∈ V i' := by
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hb i', Over.comp_left, Scheme.Hom.comp_apply]
      change (V i').ι ((b i').left q) ∈ V i'
      exact (Scheme.Opens.range_ι (V i')).subset ⟨_, rfl⟩
    by_cases hii : i' = i
    · subst hii; exact ⟨q, rfl⟩
    · exact absurd (⟨h1, hp⟩ : bt.left ((j i').left q) ∈ (V i' ⊓ V i : X.left.Opens))
        (fun h ↦ (hVd hii).le_bot h)
  have loc : ∀ i, ((x ≫ bt).left ⁻¹ᵁ V i).ι ≫ x.left = ((x ≫ bt).left ⁻¹ᵁ V i).ι ≫ y.left := by
    intro i
    let Ti : Over S := Over.mk (((x ≫ bt).left ⁻¹ᵁ V i).ι ≫ T.hom)
    let w : Ti ⟶ T := Over.homMk ((x ≫ bt).left ⁻¹ᵁ V i).ι rfl
    have lf : ∀ z : T ⟶ Bt, z ≫ bt = x ≫ bt → ∃ zi : Ti ⟶ B i, zi ≫ j i = w ≫ z := by
      intro z hz
      have r : Set.range (w ≫ z).left ⊆ Set.range (j i).left := by
        rintro _ ⟨p, rfl⟩
        apply mem i
        rw [← Scheme.Hom.comp_apply, ← Over.comp_left, Category.assoc, hz, Over.comp_left,
          Scheme.Hom.comp_apply]
        exact (Scheme.Opens.range_ι ((x ≫ bt).left ⁻¹ᵁ V i)).subset ⟨p, rfl⟩
      exact ⟨Over.homMk (IsOpenImmersion.lift (j i).left _ r)
        (by rw [← Over.w (j i), IsOpenImmersion.lift_fac_assoc, Over.w]),
        Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)⟩
    obtain ⟨xi, hx⟩ := lf x rfl
    obtain ⟨yi, hy⟩ := lf y hxy.symm
    have hQ := (hP i).fam.isLB
    have hb' : xi ≫ b i = yi ≫ b i := by
      have k : xi ≫ b i ≫ Over.homMk (V i).ι = yi ≫ b i ≫ Over.homMk (V i).ι := by
        rw [← hb, reassoc_of% hx, reassoc_of% hy, hxy]
      apply Over.OverMorphism.ext
      rw [← cancel_mono (V i).ι]
      exact congrArg (fun q ↦ q.left) k
    have hs : Same A (P i) (P i) xi yi := by
      have e2 := (same_iff hPt hPt _ _).1 (same_precomp hPt hPt w e)
      rw [same_iff hQ hQ, ← evc_comp_of_iso (j i) hPt hQ (hPi i), ← evc_comp_of_iso (j i) hPt hQ (hPi i),
        Category.assoc, Category.assoc, hx, hy]
      exact e2
    have h3 := Model.rep_ext (hP i) hb' hs
    exact congrArg (fun q ↦ q.left) (show w ≫ x = w ≫ y by rw [← hx, ← hy, h3])
  refine Over.OverMorphism.ext (Scheme.hom_ext_of_forall _ _ fun z ↦ ?_)
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1
    (show (x ≫ bt).left z ∈ ⨆ i, V i by rw [hV]; trivial)
  exact ⟨_, hi, loc i⟩

end GlobalTheory.DualCon.ProdGlue
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointDisjointUnionRepresentingFamilyUniqueStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.point_disjointUnion_representingFamily_unique : ∀ {S : Scheme.{0}} (A : Over S) [GrpObj A] {κ : Type} [Finite κ] (X : Over S) (V : κ → X.left.Opens), (⨆ i, V i = ⊤) → (Pairwise fun i i' => Disjoint (V i) (V i')) → ∀ (Bt : Over S) (B : κ → Over S) (j : ∀ i, B i ⟶ Bt) [∀ i, IsOpenImmersion (j i).left], (⨆ i, (j i).left.opensRange = ⊤) → (Pairwise fun i i' => Disjoint (j i).left.opensRange (j i').left.opensRange) → ∀ (b : ∀ i, B i ⟶ Over.mk ((V i).ι ≫ X.hom)) (bt : Bt ⟶ X), (∀ i, j i ≫ bt = b i ≫ Over.homMk (V i).ι) → ∀ (P : ∀ i, LB (A ⊗ B i).left) (Pt : LB (A ⊗ Bt).left), (∀ i, Rep A (b i) (P i)) → Pt.IsLB → (∀ i, LBIso (Pt.pull (A ◁ j i).left) (P i)) → ∀ (T : Over S) (x y : T ⟶ Bt), x ≫ bt = y ≫ bt → Same A Pt Pt x y → x = y := by
  first | exact @GlobalTheory.DualCon.ProdGlue.eq_of_same_of_disjoint_cover | exact GlobalTheory.DualCon.ProdGlue.eq_of_same_of_disjoint_cover | (intros; apply GlobalTheory.DualCon.ProdGlue.eq_of_same_of_disjoint_cover <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveLineBundleFamilyOfDisjointOpenPieces
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveLineBundleFamilyOfDisjointOpenPieces
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualCon.ProdGlue

theorem fam_of_pieces {S : Scheme.{0}} (A : Over S) [GrpObj A] {κ : Type} [Finite κ] (Bt : Over S) (B : κ → Over S) (j : ∀ i, B i ⟶ Bt) [∀ i, IsOpenImmersion (j i).left] (hcov : ⨆ i, (j i).left.opensRange = ⊤) (hdisj : Pairwise fun i i' => Disjoint (j i).left.opensRange (j i').left.opensRange) (P : ∀ i, LB (A ⊗ B i).left) (Pt : LB (A ⊗ Bt).left) (hP : ∀ i, Fam A (P i)) (hPt : Pt.IsLB) (hiso : ∀ i, LBIso (Pt.pull (A ◁ j i).left) (P i)) : Fam A Pt := by
  refine ⟨hPt, (GlobalTheory.AbDual.isAdditive_iff hPt).mpr ?_⟩
  intro Y a a' t

  have hcovY : ⨆ i, (pullback.fst t.left (j i).left).opensRange = ⊤ := by
    simp only [Scheme.Hom.opensRange_pullbackFst]
    rw [← Scheme.Hom.preimage_iSup, hcov]
    try simp
  have hdisjY : Pairwise fun i i' => Disjoint (pullback.fst t.left (j i).left).opensRange
      (pullback.fst t.left (j i').left).opensRange := by
    intro i i' hii
    have h : Disjoint (j i).left.opensRange (j i').left.opensRange := hdisj hii
    rw [Scheme.Hom.opensRange_pullbackFst, Scheme.Hom.opensRange_pullbackFst]
    rw [disjoint_iff] at h ⊢
    refine le_antisymm (fun x hx => ?_) bot_le
    have hx' : t.left x ∈ (j i).left.opensRange ⊓ (j i').left.opensRange := ⟨hx.1, hx.2⟩
    rw [h] at hx'
    simp at hx'

  rw [← sub_eq_zero]
  refine GlobalTheory.T.cechPicard_eq_zero_of_trivial_on_disjoint_cover (fun i => pullback.fst t.left (j i).left) hcovY hdisjY _ (fun i => ?_)
  let Zi : Over S := Over.mk (pullback.fst t.left (j i).left ≫ Y.hom)
  let u : Zi ⟶ Y := Over.homMk (pullback.fst t.left (j i).left) rfl
  have hv : pullback.snd t.left (j i).left ≫ (B i).hom = Zi.hom := by
    show pullback.snd t.left (j i).left ≫ (B i).hom = pullback.fst t.left (j i).left ≫ Y.hom
    rw [← Over.w (j i), ← Over.w t, ← Category.assoc, ← Category.assoc, pullback.condition]
  let v : Zi ⟶ B i := Over.homMk (pullback.snd t.left (j i).left) hv
  have huv : u ≫ t = v ≫ j i := by
    ext
    simp [u, v, pullback.condition]
  change GlobalTheory.CechPic.pull u.left _ = 0
  rw [map_sub, map_add (f := _), GlobalTheory.AbDual.pull_evc, GlobalTheory.AbDual.pull_evc, GlobalTheory.AbDual.pull_evc, huv,
    evc_comp_of_iso (j i) hPt (hP i).isLB (hiso i), evc_comp_of_iso (j i) hPt (hP i).isLB (hiso i),
    evc_comp_of_iso (j i) hPt (hP i).isLB (hiso i), MonObj.comp_mul,
    (GlobalTheory.AbDual.isAdditive_iff (hP i).isLB).mp (hP i).add]
  exact sub_self _

end GlobalTheory.DualCon.ProdGlue
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveLineBundleFamilyOfDisjointOpenPiecesStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additiveLineBundleFamily_of_disjoint_open_pieces : ∀ {S : Scheme.{0}} (A : Over S) [GrpObj A] {κ : Type} [Finite κ] (Bt : Over S) (B : κ → Over S) (j : ∀ i, B i ⟶ Bt) [∀ i, IsOpenImmersion (j i).left], (⨆ i, (j i).left.opensRange = ⊤) → (Pairwise fun i i' => Disjoint (j i).left.opensRange (j i').left.opensRange) → ∀ (P : ∀ i, LB (A ⊗ B i).left) (Pt : LB (A ⊗ Bt).left), (∀ i, Fam A (P i)) → Pt.IsLB → (∀ i, LBIso (Pt.pull (A ◁ j i).left) (P i)) → Fam A Pt := by
  first | exact @GlobalTheory.DualCon.ProdGlue.fam_of_pieces | exact GlobalTheory.DualCon.ProdGlue.fam_of_pieces | (intros; apply GlobalTheory.DualCon.ProdGlue.fam_of_pieces <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasProperSmoothDualRepresentativeFinAffineOfIso
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasProperSmoothDualRepresentativeFinAffineOfIso
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem hasRepAF_of_iso : ∀ {S : Scheme.{0}} (A : Over S) [GrpObj A] (g : ℕ) {Y Y' : Over S}, (Y ≅ Y') → HasRepAF A g Y → HasRepAF A g Y' := by
  intro S A _ g Y Y' e h
  obtain ⟨B, b, P, hR, hG, hF⟩ := h
  refine ⟨B, b ≫ e.hom, P, ⟨hR.fam, ?_⟩, ?_, hF⟩
  · intro T t N hN
    obtain ⟨x, ⟨hx1, hx2⟩, hu⟩ := hR.univ T (t ≫ e.inv) N hN
    refine ⟨x, ⟨?_, hx2⟩, fun y hy => hu y ⟨?_, hy.2⟩⟩
    · rw [← Category.assoc, hx1, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    · rw [← hy.1, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · rw [Over.comp_left]
    obtain ⟨hp, hs, hc⟩ := hG
    have hi : IsIso e.hom.left := ⟨⟨e.inv.left, by rw [← Over.comp_left, Iso.hom_inv_id, Over.id_left],
      by rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]⟩⟩
    have hR : MorphismProperty.RespectsIso (@GeometricallyConnected : MorphismProperty Scheme.{0}) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    refine ⟨inferInstance, ?_, MorphismProperty.RespectsIso.postcomp (@GeometricallyConnected : MorphismProperty Scheme.{0}) e.hom.left b.left hc⟩
    have := smoothOfRelativeDimension_comp (n := g) (m := 0) b.left e.hom.left
    simpa using this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasProperSmoothDualRepresentativeFinAffineOfIsoStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasProperSmoothDualRepresentativeFinAffine_of_iso : ∀ {S : Scheme.{0}} (A : Over S) [GrpObj A] (g : ℕ) {Y Y' : Over S}, (Y ≅ Y') → HasRepAF A g Y → HasRepAF A g Y' := by
  first | exact @GlobalTheory.hasRepAF_of_iso | exact GlobalTheory.hasRepAF_of_iso | (intros; apply GlobalTheory.hasRepAF_of_iso <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecPiDisjointOpenCoverFactors
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecPiDisjointOpenCoverFactors
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SpecPi

theorem specPi_cover : ∀ (R : Type) [CommRing R] (n : ℕ) (D : Fin n → Type) [∀ i, CommRing (D i)] [∀ i, Algebra R (D i)], ∃ V : Fin n → (Sp (∀ i, D i)).Opens, (⨆ i, V i = ⊤) ∧ (Pairwise fun i i' => Disjoint (V i) (V i')) ∧ ∀ i, Nonempty (Over.mk ((V i).ι ≫ spMap (algebraMap R (∀ i, D i))) ≅ Over.mk (spMap (algebraMap R (D i)))) := by
  intro R _ n D _ _
  let S := sigmaSpec (fun i => CommRingCat.of (D i))
  have hS : ∀ i, Sigma.ι (fun i => Spec (CommRingCat.of (D i))) i ≫ S = spMap (Pi.evalRingHom D i) :=
    fun i => ι_sigmaSpec _ i
  have hinv : ∀ y, (inv S) (S y) = y := fun y => by
    rw [← Scheme.Hom.comp_apply, IsIso.hom_inv_id]; rfl
  have hsurj : ∀ x, S ((inv S) x) = x := fun x => by
    rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl
  refine ⟨fun i => (spMap (Pi.evalRingHom D i)).opensRange, ?_, ?_, ?_⟩
  · rw [eq_top_iff]
    rintro x -
    have hcov : ∀ y : ↥(∐ fun i => Spec (CommRingCat.of (D i))), ∃ k, ∃ z : Sp (D k),
        (Sigma.ι (fun i => Spec (CommRingCat.of (D i))) k) z = y :=
      fun y => ⟨_, (sigmaOpenCover (fun i => Spec (CommRingCat.of (D i)))).covers y⟩
    obtain ⟨k, z, hz⟩ := hcov ((inv S) x)
    rw [TopologicalSpace.Opens.mem_iSup]
    refine ⟨k, z, ?_⟩
    rw [← hS k, Scheme.Hom.comp_apply, hz, hsurj]
  · intro i j hij
    rw [disjoint_iff, eq_bot_iff]
    rintro x ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    rw [← hS, Scheme.Hom.comp_apply] at ha hb
    have e := congrArg (inv S) (ha.trans hb.symm)
    rw [hinv, hinv] at e
    obtain ⟨rfl⟩ := (sigmaι_eq_iff _ _ _ _ _).mp e
    exact absurd rfl hij
  · intro i
    refine ⟨Over.isoMk (spMap (Pi.evalRingHom D i)).isoOpensRange.symm ?_⟩
    simp only [Over.mk_hom, Iso.symm_hom]
    rw [← Scheme.Hom.isoOpensRange_inv_comp, Category.assoc]
    congr 1
    rw [← Spec.map_comp]
    rfl

end GlobalTheory.SpecPi
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecPiDisjointOpenCoverFactorsStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spec_pi_disjoint_open_cover_factors : ∀ (R : Type) [CommRing R] (n : ℕ) (D : Fin n → Type) [∀ i, CommRing (D i)] [∀ i, Algebra R (D i)], ∃ V : Fin n → (Sp (∀ i, D i)).Opens, (⨆ i, V i = ⊤) ∧ (Pairwise fun i i' => Disjoint (V i) (V i')) ∧ ∀ i, Nonempty (Over.mk ((V i).ι ≫ spMap (algebraMap R (∀ i, D i))) ≅ Over.mk (spMap (algebraMap R (D i)))) := by
  first | exact @GlobalTheory.SpecPi.specPi_cover | exact GlobalTheory.SpecPi.specPi_cover | (intros; apply GlobalTheory.SpecPi.specPi_cover <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperSmoothGeomConnectedSigmaDescDisjointCover
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperSmoothGeomConnectedSigmaDescDisjointCover
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualCon

theorem of_isPullback_opens_cover (Q : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget Q]
    {S X : Scheme.{0}} {I : Type} {U : I → S.Opens} (hU : iSup U = ⊤) {Z : I → Scheme.{0}} {p : X ⟶ S}
    {q : ∀ i, Z i ⟶ (U i).toScheme} {ψ : ∀ i, Z i ⟶ X} (h : ∀ i, IsPullback (ψ i) (q i) p (U i).ι)
    (hq : ∀ i, Q (q i)) : Q p := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top U hU fun i => ?_
  have e := (isPullback_morphismRestrict p (U i)).flip
  rw [← IsPullback.isoIsPullback_hom_snd _ _ e (h i), MorphismProperty.cancel_left_of_respectsIso Q]
  exact hq i

theorem isPullback_sigmaι_desc {X : Scheme.{0}} {κ : Type} (V : κ → X.Opens)
    (hd : Pairwise fun i i' => Disjoint (V i) (V i')) {B : κ → Scheme.{0}} (f : ∀ i, B i ⟶ (V i).toScheme)
    (i : κ) : IsPullback (Sigma.ι B i) (f i) (Sigma.desc fun j => f j ≫ (V j).ι) (V i).ι := by
  have : IsOpenImmersion (Sigma.ι B i) := inferInstance
  have hr : ∀ s : PullbackCone (Sigma.desc fun j => f j ≫ (V j).ι) (V i).ι,
      Set.range s.fst ⊆ Set.range (Sigma.ι B i) := by
    rintro s _ ⟨t, rfl⟩
    obtain ⟨⟨j, y⟩, hy⟩ := (sigmaMk B).surjective (s.fst t)
    rw [sigmaMk_mk] at hy
    have e1 : (Sigma.desc fun j => f j ≫ (V j).ι) (s.fst t) = (V i).ι (s.snd t) := congr($(s.condition) t)
    rw [← hy, ← Scheme.Hom.comp_apply, Sigma.ι_desc, Scheme.Hom.comp_apply] at e1
    by_cases hji : j = i
    · subst hji
      exact ⟨y, hy⟩
    · exfalso
      have h1 : (V j).ι (f j y) ∈ V j := ((V j).ι_apply _ ▸ ((f j y).2))
      have h2 : (V i).ι (s.snd t) ∈ V i := ((V i).ι_apply _ ▸ ((s.snd t).2))
      rw [e1] at h1
      have h3 := (hd hji).le_bot (show (V i).ι (s.snd t) ∈ V j ⊓ V i from ⟨h1, h2⟩)
      simp at h3
  refine ⟨⟨Sigma.ι_desc _ _⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => IsOpenImmersion.lift (Sigma.ι B i) s.fst (hr s)) ?_ ?_ ?_⟩⟩
  · intro s
    exact IsOpenImmersion.lift_fac _ _ _
  · intro s
    rw [← cancel_mono (V i).ι, Category.assoc, ← Sigma.ι_desc (fun j => f j ≫ (V j).ι) i,
      IsOpenImmersion.lift_fac_assoc, s.condition]
  · intro s m h1 _
    rw [← cancel_mono (Sigma.ι B i), IsOpenImmersion.lift_fac, h1]

theorem good_sigmaDesc_of_disjoint_cover : ∀ {X : Scheme.{0}} {κ : Type} [Finite κ] (V : κ → X.Opens), (⨆ i, V i = ⊤) → (Pairwise fun i i' => Disjoint (V i) (V i')) → ∀ {B : κ → Scheme.{0}} (f : ∀ i, B i ⟶ (V i).toScheme) (g : ℕ), (∀ i, Good g (f i)) → Good g (Sigma.desc fun i => f i ≫ (V i).ι) := by
  intro X κ _ V hU hd B f g hf
  have sq := isPullback_sigmaι_desc V hd f
  have hc : IsZariskiLocalAtTarget (@GeometricallyConnected.{0}) := by
    rw [GeometricallyConnected.eq_geometrically]; infer_instance
  have hs : IsZariskiLocalAtTarget (@SmoothOfRelativeDimension.{0} g) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _
  exact
    { proper := of_isPullback_opens_cover @IsProper hU sq fun i => (hf i).proper
      smooth := of_isPullback_opens_cover (@SmoothOfRelativeDimension.{0} g) hU sq fun i => (hf i).smooth
      conn := of_isPullback_opens_cover @GeometricallyConnected hU sq fun i => (hf i).conn }

end GlobalTheory.DualCon
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperSmoothGeomConnectedSigmaDescDisjointCoverStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.properSmoothGeomConnected_sigmaDesc_disjoint_cover : ∀ {X : Scheme.{0}} {κ : Type} [Finite κ] (V : κ → X.Opens), (⨆ i, V i = ⊤) → (Pairwise fun i i' => Disjoint (V i) (V i')) → ∀ {B : κ → Scheme.{0}} (f : ∀ i, B i ⟶ (V i).toScheme) (g : ℕ), (∀ i, Good g (f i)) → Good g (Sigma.desc fun i => f i ≫ (V i).ι) := by
  first | exact @GlobalTheory.DualCon.good_sigmaDesc_of_disjoint_cover | exact GlobalTheory.DualCon.good_sigmaDesc_of_disjoint_cover | (intros; apply GlobalTheory.DualCon.good_sigmaDesc_of_disjoint_cover <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSetsInAffineOpenFiniteCoproduct
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSetsInAffineOpenFiniteCoproduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon

theorem finAff_sigma : ∀ {κ : Type} [Finite κ] (B : κ → Scheme.{0}), (∀ i, FinAff (B i)) → FinAff (∐ B) := by
  intro κ _ B hB F
  classical
  have hfin : ∀ i, {y : B i | Sigma.ι B i y ∈ F}.Finite := fun i =>
    (F.finite_toSet).preimage (Sigma.ι B i).isOpenEmbedding.injective.injOn
  choose V hV hFV using fun i => hB i (hfin i).toFinset
  refine ⟨⨆ i, Sigma.ι B i ''ᵁ V i, IsAffineOpen.iSup_of_disjoint
    (fun i => (hV i).image_of_isOpenImmersion _) fun i j hij => ?_, fun x hx => ?_⟩
  · exact (disjoint_opensRange_sigmaι B i j hij).mono (Scheme.Hom.image_le_opensRange _ _)
      (Scheme.Hom.image_le_opensRange _ _)
  · obtain ⟨i, y, rfl⟩ := (sigmaOpenCover B).exists_eq x
    have hy : y ∈ V i := hFV i y ((Set.Finite.mem_toFinset _).2 hx)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, ⟨y, hy, rfl⟩⟩

end GlobalTheory.DualCon
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSetsInAffineOpenFiniteCoproductStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteSetsInAffineOpen_finite_coproduct : ∀ {κ : Type} [Finite κ] (B : κ → Scheme.{0}), (∀ i, FinAff (B i)) → FinAff (∐ B) := by
  first | exact @GlobalTheory.DualCon.finAff_sigma | exact GlobalTheory.DualCon.finAff_sigma | (intros; apply GlobalTheory.DualCon.finAff_sigma <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasProperSmoothDualRepOfFiniteProductAlgebras
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon.ProdGlue

theorem hasRepAF_of_disjoint_cover {S : Scheme.{0}} (A : Over S) [GrpObj A] (g : ℕ) {κ : Type} [Finite κ] (X : Over S)
    (V : κ → X.left.Opens) (hcov : ⨆ i, V i = ⊤) (hdisj : Pairwise fun i i' => Disjoint (V i) (V i'))
    (h : ∀ i, HasRepAF A g (Over.mk ((V i).ι ≫ X.hom))) : HasRepAF A g X := by
  choose B b P hP using h
  let Bt : Over S := Over.mk (Sigma.desc fun i => (B i).hom)
  let j : ∀ i, B i ⟶ Bt := fun i => Over.homMk (Sigma.ι (fun i => (B i).left) i) (by simp [Bt])
  have hjl : ∀ i, (j i).left = Sigma.ι (fun i => (B i).left) i := fun i => rfl
  haveI : ∀ i, IsOpenImmersion (j i).left := fun i => by rw [hjl]; infer_instance
  have hjc : ⨆ i, (j i).left.opensRange = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨⟨i, y⟩, rfl⟩ := (sigmaMk fun i => (B i).left).surjective x
    rw [sigmaMk_mk]
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, y, by rw [hjl]⟩
  have hjd : Pairwise fun i i' => Disjoint (j i).left.opensRange (j i').left.opensRange := fun i i' hii' => by
    simp only [hjl]; exact disjoint_opensRange_sigmaι _ i i' hii'
  let bt : Bt ⟶ X := Over.homMk (Sigma.desc fun i => (b i).left ≫ (V i).ι) (by
    refine Sigma.hom_ext _ _ fun i => ?_
    simp only [Bt, Over.mk_hom, colimit.ι_desc_assoc, Cofan.mk_ι_app, Discrete.functor_obj_eq_as, colimit.ι_desc, Category.assoc]
    exact Over.w (b i))
  have hb : ∀ i, j i ≫ bt = b i ≫ Over.homMk (V i).ι := fun i => by
    ext1; simp [j, bt]

  haveI hk : ∀ i, IsOpenImmersion (A ◁ j i).left := fun i => (GlobalTheory.T.isOpenImmersion_whiskerLeft_range_preimage_snd A (j i)).1
  have hkc : ⨆ i, (A ◁ j i).left.opensRange = ⊤ := by
    rw [eq_top_iff]
    intro z _
    have hz : (snd A Bt).left z ∈ ⨆ i, (j i).left.opensRange := by rw [hjc]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨i, ?_⟩
    change z ∈ Set.range (A ◁ j i).left
    rw [(GlobalTheory.T.isOpenImmersion_whiskerLeft_range_preimage_snd A (j i)).2]
    exact hi
  have hkd : Pairwise fun i i' => Disjoint (A ◁ j i).left.opensRange (A ◁ j i').left.opensRange := by
    intro i i' hii'
    rw [disjoint_iff, eq_bot_iff]
    rintro z ⟨h1, h2⟩
    change z ∈ Set.range (A ◁ j i).left at h1
    change z ∈ Set.range (A ◁ j i').left at h2
    rw [(GlobalTheory.T.isOpenImmersion_whiskerLeft_range_preimage_snd A (j i)).2] at h1
    rw [(GlobalTheory.T.isOpenImmersion_whiskerLeft_range_preimage_snd A (j i')).2] at h2
    exact (disjoint_iff.1 (hjd hii')).le ⟨h1, h2⟩
  obtain ⟨d, hd⟩ := GlobalTheory.T.exists_cechPicard_glue_finite_disjoint_cover (fun i => (A ◁ j i).left) hkc hkd (fun i => cls (P i) (hP i).1.fam.isLB)
  obtain ⟨Pt, hPt, rfl⟩ := cls_surj d
  have hPi : ∀ i, LBIso (Pt.pull (A ◁ j i).left) (P i) := fun i =>
    (cls_eq_iff (pull_isLB hPt _) (hP i).1.fam.isLB).1 ((cls_pull hPt _ _).trans (hd i))
  refine ⟨Bt, bt, Pt, ⟨GlobalTheory.T.additiveLineBundleFamily_of_disjoint_open_pieces A Bt B j hjc hjd P Pt (fun i => (hP i).1.fam) hPt hPi, fun T t N hN => ?_⟩, ?_, ?_⟩
  · obtain ⟨x, hx, hxN⟩ := GlobalTheory.T.exists_point_disjointUnion_representingAdditiveFamily A X V hcov hdisj Bt B j hjc hjd b bt hb P Pt (fun i => (hP i).1) hPt hPi T t N hN
    refine ⟨x, ⟨hx, hxN⟩, fun y hy => ?_⟩
    refine GlobalTheory.T.point_disjointUnion_representingFamily_unique A X V hcov hdisj Bt B j hjc hjd b bt hb P Pt (fun i => (hP i).1) hPt hPi T y x (hy.1.trans hx.symm) ?_
    rw [Same, ← cls_eq_iff (pull_isLB hPt _) (pull_isLB hPt _), ← (cls_eq_iff hN.isLB (pull_isLB hPt _)).2 hy.2,
      ← (cls_eq_iff hN.isLB (pull_isLB hPt _)).2 hxN]
  · exact GlobalTheory.T.properSmoothGeomConnected_sigmaDesc_disjoint_cover V hcov hdisj (fun i => (b i).left) g (fun i => (hP i).2.1)
  · exact GlobalTheory.T.finiteSetsInAffineOpen_finite_coproduct (fun i => (B i).left) (fun i => (hP i).2.2)

theorem hasRepAF_pi : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → ∀ (n : ℕ) (D : Fin n → Type) [∀ i, CommRing (D i)] [∀ i, Algebra R (D i)], (∀ i, HasRepAF A g (Over.mk (spMap (algebraMap R (D i))))) → HasRepAF A g (Over.mk (spMap (algebraMap R (∀ i, D i)))) := by
  intro R _ A _ g _ n D _ _ h
  obtain ⟨V, hcov, hdisj, he⟩ := GlobalTheory.T.spec_pi_disjoint_open_cover_factors R n D
  exact hasRepAF_of_disjoint_cover A g (Over.mk (spMap (algebraMap R (∀ i, D i)))) V hcov hdisj
    (fun i => GlobalTheory.T.hasProperSmoothDualRepresentativeFinAffine_of_iso A g (he i).some.symm (h i))

end GlobalTheory.DualCon.ProdGlue
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasProperSmoothDualRepOfFiniteProductAlgebrasStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasProperSmoothDualRep_of_finite_product_algebras : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → ∀ (n : ℕ) (D : Fin n → Type) [∀ i, CommRing (D i)] [∀ i, Algebra R (D i)], (∀ i, HasRepAF A g (Over.mk (spMap (algebraMap R (D i))))) → HasRepAF A g (Over.mk (spMap (algebraMap R (∀ i, D i)))) := by
  first | exact @GlobalTheory.DualCon.ProdGlue.hasRepAF_pi | exact GlobalTheory.DualCon.ProdGlue.hasRepAF_pi | (intros; apply GlobalTheory.DualCon.ProdGlue.hasRepAF_pi <;> assumption)
end
