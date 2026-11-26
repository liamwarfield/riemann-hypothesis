module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueOpenChartsAdditiveFamiliesRepresenting
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSemiAbelianImage
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPointOfSize
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsFlatBaseChangeAffineMilnorSquareOpen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCocycleFirstOrderTaylorSqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomLiftsSqZeroClassifiedByDifferentials
public import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefOverOfFiniteOrbit

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveFamilyRepresentativeZariskiGlue
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveFamilyRepresentativeZariskiGlue
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon.ZarGlue

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem fam_pull {T Y : Over S} {N : LB (A ⊗ T).left} (hN : Fam A N) (y : Y ⟶ T) :
    Fam A (ev N (fst A Y) (snd A Y ≫ y)) := by
  have hL : (ev N (fst A Y) (snd A Y ≫ y)).IsLB := pull_isLB hN.isLB _
  refine ⟨hL, (isAdditive_iff hL).2 fun Z a a' t => ?_⟩
  rw [evc_ev hN.isLB _ _ hL, evc_ev hN.isLB _ _ hL, evc_ev hN.isLB _ _ hL]
  simp only [lift_fst, lift_snd_assoc]
  exact (isAdditive_iff hN.isLB).1 hN.add Z a a' (t ≫ y)


omit [GrpObj A] in
theorem hom_open_eq (V : S.Opens) {Y : Over S} (u u' : Y ⟶ Over.mk V.ι) : u = u' := by
  apply Over.OverMorphism.ext
  have h : u.left ≫ V.ι = u'.left ≫ V.ι := (Over.w u).trans (Over.w u').symm
  exact (cancel_mono V.ι).1 h


omit [GrpObj A] in
theorem exists_hom_open (V : S.Opens) (Y : Over S) (h : ∀ z, Y.hom z ∈ V) : Nonempty (Y ⟶ Over.mk V.ι) := by
  refine ⟨Over.homMk (IsOpenImmersion.lift V.ι Y.hom ?_) (IsOpenImmersion.lift_fac _ _ _)⟩
  rintro _ ⟨z, rfl⟩
  rw [Scheme.Opens.range_ι]
  exact h z

theorem isChart_of_rep (V : S.Opens) {B : Over S} (b : B ⟶ Over.mk V.ι) {P : LB (A ⊗ B).left} (h : Rep A b P) :
    IsChart A P := by
  refine ⟨h.fam, ?_, ?_⟩
  · intro Y u u' hs
    have hA : (ev P (fst A Y) (snd A Y ≫ u)).IsLB := pull_isLB h.fam.isLB _
    have hB : (ev P (fst A Y) (snd A Y ≫ u')).IsLB := pull_isLB h.fam.isLB _
    obtain ⟨x, -, hx⟩ := h.univ Y (u ≫ b) _ (fam_pull h.fam u)
    rw [hx u ⟨rfl, LBIso.trans hA hB hA hs (LBIso.symm hs)⟩, hx u' ⟨hom_open_eq V _ _, hs⟩]
  · intro T N hN
    refine ⟨T.hom ⁻¹ᵁ V, fun Y y => ⟨?_, ?_⟩⟩
    · rintro ⟨u, -⟩ z
      have hb : b.left ≫ V.ι = B.hom := Over.w b
      have e : (u.left ≫ b.left) ≫ V.ι = y.left ≫ T.hom := by
        rw [Over.w y, Category.assoc, hb, Over.w u]
      have hmem : (y.left ≫ T.hom) z ∈ Set.range V.ι := ⟨(u.left ≫ b.left) z, by rw [← e]; rfl⟩
      rw [Scheme.Opens.range_ι] at hmem
      exact hmem
    · intro hz
      have hY : ∀ z, Y.hom z ∈ V := fun z => by
        rw [← Over.w y]
        exact hz z
      obtain ⟨t⟩ := exists_hom_open V Y hY
      obtain ⟨x, ⟨-, hx⟩, -⟩ := h.univ Y t _ (fam_pull hN y)
      exact ⟨x, hx⟩


omit [GrpObj A] in
theorem good_iso_comp {g : ℕ} {X X' Y : Scheme.{0}} (e : X' ⟶ X) [IsIso e] {f : X ⟶ Y}
    (h : GlobalTheory.DualCon.Good g f) : GlobalTheory.DualCon.Good g (e ≫ f) := ⟨MorphismProperty.RespectsIso.precomp @IsProper e f h.proper,
  by
    haveI := h.smooth
    have h0 : SmoothOfRelativeDimension (0 + g) (e ≫ f) := inferInstance
    rwa [zero_add] at h0,
  by
    haveI := h.conn
    have hsq : IsPullback e (e ≫ f) f (𝟙 Y) := IsPullback.of_horiz_isIso ⟨by simp⟩
    exact MorphismProperty.of_isPullback (P := @GeometricallyConnected) hsq h.conn⟩

theorem zariski_glue : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (Ix : Type) (V : Ix → S.Opens) (g : Ix → ℕ), (∀ s : S, ∃ i, s ∈ V i) → (∀ i, HasRep A (g i) (Over.mk (V i).ι)) → ∃ (B : Over S) (P : LB (A ⊗ B).left), Rep A (toUnit B) P ∧ ∀ i, GlobalTheory.DualCon.Good (g i) (pullback.snd B.hom (V i).ι) := by
  intro S A _ hA Ix V g hcov hrep
  have hrep' : ∀ i, ∃ (B : Over S) (b : B ⟶ Over.mk (V i).ι) (P : LB (A ⊗ B).left),
      Rep A b P ∧ GlobalTheory.DualCon.Good (g i) b.left := hrep
  choose Bi bi Pi hRi hGi using hrep'
  obtain ⟨B, P, j, hR, -, -, -⟩ := GlobalTheory.T.glue_openCharts_additiveFamilies_representing S A hA Ix Bi Pi
    (fun i => isChart_of_rep (V i) (bi i) (hRi i)) (by
      intro K _ _ s N hN
      obtain ⟨i, hi⟩ := hcov (s (default : Sp K))
      have hs : ∀ z : Sp K, s z ∈ V i := fun z => by
        rw [Subsingleton.elim z default]
        exact hi
      obtain ⟨t⟩ := exists_hom_open (V i) (Over.mk s) hs
      obtain ⟨x, ⟨-, hx⟩, -⟩ := (hRi i).univ _ t N hN
      exact ⟨i, x, (same_id_iff hN.isLB (hRi i).fam.isLB x).2 hx⟩)
  refine ⟨B, P, hR, fun i => ?_⟩
  have hpb : IsPullback (fst B (Over.mk (V i).ι)) (snd B (Over.mk (V i).ι)) (toUnit B)
      (toUnit (Over.mk (V i).ι)) :=
    IsPullback.of_is_product' (CartesianMonoidalCategory.tensorProductIsBinaryProduct _ _)
      SemiCartesianMonoidalCategory.isTerminalTensorUnit
  have hR' := GlobalTheory.T.rep_ev_of_isPullback S A B (𝟙_ (Over S)) (Over.mk (V i).ι) (B ⊗ Over.mk (V i).ι) (toUnit B) P
    (toUnit _) (fst _ _) (snd _ _) hR hpb
  obtain ⟨e, he, -⟩ := GlobalTheory.T.representsAdditiveLineBundleFamilies_unique_iso S A _ _ _ (snd B (Over.mk (V i).ι)) _ (bi i) (Pi i) hR' (hRi i)
  haveI : IsIso e.hom.left := Functor.map_isIso (Over.forget _) e.hom
  have h2 := good_iso_comp e.hom.left (hGi i)
  rw [← Over.comp_left, he] at h2
  exact h2

end GlobalTheory.DualCon.ZarGlue
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveFamilyRepresentativeZariskiGlueStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_additiveFamily_representative_zariski_glue : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (Ix : Type) (V : Ix → S.Opens) (g : Ix → ℕ), (∀ s : S, ∃ i, s ∈ V i) → (∀ i, HasRep A (g i) (Over.mk (V i).ι)) → ∃ (B : Over S) (P : LB (A ⊗ B).left), Rep A (toUnit B) P ∧ ∀ i, GlobalTheory.DualCon.Good (g i) (pullback.snd B.hom (V i).ι) := by
  first | exact @GlobalTheory.DualCon.ZarGlue.zariski_glue | exact GlobalTheory.DualCon.ZarGlue.zariski_glue | (intros; apply GlobalTheory.DualCon.ZarGlue.zariski_glue <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicardClassEqZeroAffineMilnorSquare
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicardClassEqZeroAffineMilnorSquare
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.DualOpen

open TopologicalSpace

theorem exists_units_of_pull_eq_zero {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (f : Y ⟶ X)
    (h : CechPic.pull f (cls L hL) = 0) : ∃ b : ∀ i, Γ(Y, f ⁻¹ᵁ L.U i)ˣ,
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i j : L.ι), f (r z) ∈ L.U i → f (r z) ∈ L.U j →
        gm r z _ (b i) = gm (r ≫ f) z _ (L.g i j) * gm r z _ (b j) := by
  rw [← cls_pull hL f (pull_isLB hL f)] at h
  obtain ⟨t, ht⟩ := (cls_eq_zero_iff _).1 h
  have le : ∀ i, f ⁻¹ᵁ L.U i ≤ (L.pull f).U (fun _ ↦ i) := fun i y hy ↦ mem_pull.2 hy
  refine ⟨fun i ↦ res (le i) (t.s fun _ ↦ i), fun Z r z i j hi hj ↦ ?_⟩
  have mi : r z ∈ (L.pull f).U (fun _ ↦ i) := mem_pull.2 hi
  have mj : r z ∈ (L.pull f).U (fun _ ↦ j) := mem_pull.2 hj
  have hm : r z ∈ (L.pull f).U (fun _ ↦ i) ⊓ (L.pull f).U (fun _ ↦ j) := ⟨mi, mj⟩
  have e := congrArg (gm r z _) (ht (fun _ ↦ i) (fun _ ↦ j))
  rw [map_mul, gm_res r z _ hm, gm_res r z _ hm, gm_pull_g L f r z _ _ mi mj] at e
  rw [gm_res r z (le i) hi, gm_res r z (le j) hj]
  exact e

theorem eq_zero_of_square {X X₁ X₂ X₀ : Scheme.{0}} (f₁ : X₁ ⟶ X) (f₂ : X₂ ⟶ X) (g₁ : X₀ ⟶ X₁) (g₂ : X₀ ⟶ X₂)
    (w : g₁ ≫ f₁ = g₂ ≫ f₂)
    (inj : ∀ (W : X.Opens) (a b : Γ(X, W)), f₁.app W a = f₁.app W b → f₂.app W a = f₂.app W b → a = b)
    (ex : ∀ (W : X.Opens) (h₂ : g₁ ⁻¹ᵁ (f₁ ⁻¹ᵁ W) ≤ g₂ ⁻¹ᵁ (f₂ ⁻¹ᵁ W)) (a₁ : Γ(X₁, f₁ ⁻¹ᵁ W))
      (a₂ : Γ(X₂, f₂ ⁻¹ᵁ W)), g₁.appLE _ _ le_rfl a₁ = g₂.appLE _ _ h₂ a₂ →
        ∃ a : Γ(X, W), f₁.app W a = a₁ ∧ f₂.app W a = a₂)
    (lift : Function.Surjective (Units.map g₂.appTop.hom.toMonoidHom))
    (c : Pic X) (h₁ : CechPic.pull f₁ c = 0) (h₂ : CechPic.pull f₂ c = 0) : c = 0 := by
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  obtain ⟨b₁, hb₁⟩ := exists_units_of_pull_eq_zero hL f₁ h₁
  obtain ⟨b₂, hb₂⟩ := exists_units_of_pull_eq_zero hL f₂ h₂
  have le : ∀ W : X.Opens, g₁ ⁻¹ᵁ (f₁ ⁻¹ᵁ W) ≤ g₂ ⁻¹ᵁ (f₂ ⁻¹ᵁ W) := fun W ↦ by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, w]
  have injU : ∀ (W : X.Opens) (a b : Γ(X, W)ˣ), pullU f₁ W a = pullU f₁ W b → pullU f₂ W a = pullU f₂ W b → a = b :=
    fun W a b e₁ e₂ ↦ Units.ext (inj W _ _ (congrArg Units.val e₁) (congrArg Units.val e₂))
  have exU : ∀ (W : X.Opens) (a₁ : Γ(X₁, f₁ ⁻¹ᵁ W)ˣ) (a₂ : Γ(X₂, f₂ ⁻¹ᵁ W)ˣ),
      res le_rfl (pullU g₁ _ a₁) = res (le W) (pullU g₂ _ a₂) →
        ∃ a : Γ(X, W)ˣ, pullU f₁ W a = a₁ ∧ pullU f₂ W a = a₂ := fun W a₁ a₂ e ↦ by
    have e' : res le_rfl (pullU g₁ _ a₁⁻¹) = res (le W) (pullU g₂ _ a₂⁻¹) := by
      rw [map_inv, map_inv, map_inv, map_inv, e]
    obtain ⟨a, p₁, p₂⟩ := ex W (le W) a₁.val a₂.val (congrArg Units.val e)
    obtain ⟨a', q₁, q₂⟩ := ex W (le W) (a₁⁻¹).val (a₂⁻¹).val (congrArg Units.val e')
    have k : a * a' = 1 := inj W _ _ (by rw [map_mul, map_one, p₁, q₁, Units.mul_inv])
      (by rw [map_mul, map_one, p₂, q₂, Units.mul_inv])
    exact ⟨⟨a, a', k, (mul_comm _ _).trans k⟩, Units.ext p₁, Units.ext p₂⟩
  have key : ∀ {G : Type} [CommGroup G] (a x y : G), a * x * (a * y)⁻¹ = x * y⁻¹ := fun a x y ↦ by
    rw [← div_eq_mul_inv, ← div_eq_mul_inv, mul_div_mul_left_eq_div]
  let V : L.ι → X₀.Opens := fun i ↦ g₁ ⁻¹ᵁ (f₁ ⁻¹ᵁ L.U i)
  let q : ∀ i, Γ(X₀, V i)ˣ := fun i ↦ pullU g₁ _ (b₁ i) * (res (le _) (pullU g₂ _ (b₂ i)))⁻¹
  have gq : ∀ i x, x ∈ V i → gm (𝟙 X₀) x (V i) (q i) = gm g₁ x _ (b₁ i) * (gm g₂ x _ (b₂ i))⁻¹ := fun i x hx ↦ by
    have e₁ := gm_pull (𝟙 X₀) g₁ x _ hx (b₁ i)
    have e₂ := (gm_res (𝟙 X₀) x (le (L.U i)) hx _).trans (gm_pull (𝟙 X₀) g₂ x _ (le _ hx) (b₂ i))
    rw [Category.id_comp] at e₁ e₂
    exact (map_mul _ _ _).trans (congrArg₂ (· * ·) e₁ ((map_inv _ _).trans (congrArg (·⁻¹) e₂)))
  obtain ⟨F, hF⟩ := glue_unit ⊤ V (fun _ ↦ le_top) (fun x _ ↦ by
      obtain ⟨i, hi⟩ := exists_chart hL (f₁ (g₁ x))
      exact Opens.mem_iSup.2 ⟨i, hi⟩) q (fun i j x hx ↦ by
      rw [gq i x hx.1, gq j x hx.2, hb₁ _ g₁ x i j hx.1 hx.2, hb₂ _ g₂ x i j (le _ hx.1) (le _ hx.2), w, key])
  obtain ⟨u, hu⟩ := lift F
  have hu' : pullU g₂ ⊤ u = F := hu
  have loc : ∀ i, ∃ s : Γ(X, L.U i)ˣ, pullU f₁ _ s = b₁ i ∧ pullU f₂ _ s = b₂ i * res le_top u := fun i ↦
    exU _ _ _ (unit_ext fun x hx ↦ by
      have e := congrArg (gm (𝟙 X₀) x (V i)) (hF i)
      rw [gm_res (𝟙 X₀) x _ hx, gq i x hx, ← hu'] at e
      have e₀ := gm_pull (𝟙 X₀) g₂ x ⊤ trivial u
      have e₁ := gm_pull (𝟙 X₀) g₁ x _ hx (b₁ i)
      have e₂ := gm_pull (𝟙 X₀) g₂ x _ (le _ hx) (b₂ i * res le_top u)
      rw [Category.id_comp] at e₀ e₁ e₂
      rw [gm_res (𝟙 X₀) x _ hx, gm_res (𝟙 X₀) x _ hx, e₁, e₂, map_mul, gm_res g₂ x _ (le _ hx), ← e₀]
      exact (mul_inv_eq_iff_eq_mul.1 e.symm).trans (mul_comm _ _))
  choose s hs₁ hs₂ using loc
  have gp : ∀ {Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (W : X.Opens) (a : Γ(X, W)ˣ), f y ∈ W →
      gm (𝟙 Y) y (f ⁻¹ᵁ W) (pullU f W a) = gm f y W a := fun f y W a hy ↦
    (gm_pull (𝟙 _) f y W hy a).trans (by rw [Category.id_comp])
  refine (cls_eq_zero_iff hL).2 ⟨⟨s⟩, fun i j ↦ injU _ _ _ (unit_ext fun y hy ↦ ?_) (unit_ext fun y hy ↦ ?_)⟩
  · have e := hb₁ _ (𝟙 _) y i j hy.1 hy.2
    rw [Category.id_comp, ← hs₁, ← hs₁, gp f₁ y _ _ hy.1, gp f₁ y _ _ hy.2] at e
    rw [gp f₁ y _ _ hy, gp f₁ y _ _ hy, map_mul, gm_res f₁ y _ hy, gm_res f₁ y _ hy]
    exact e
  · have e := hb₂ _ (𝟙 _) y i j hy.1 hy.2
    rw [Category.id_comp] at e
    have k : ∀ i, f₂ y ∈ L.U i → gm f₂ y _ (s i) = gm (𝟙 _) y _ (b₂ i) * gm (𝟙 _) y ⊤ u := fun i hi ↦ by
      rw [← gp f₂ y _ _ hi, hs₂, map_mul, gm_res (𝟙 _) y _ hi]
    rw [gp f₂ y _ _ hy, gp f₂ y _ _ hy, map_mul, gm_res f₂ y _ hy, gm_res f₂ y _ hy]
    exact (k i hy.1).trans (by rw [e, k j hy.2, _root_.mul_assoc])

theorem pic_eq_zero_of_milnor : ∀ (S : Scheme.{0}) (A T T₁ T₂ T₀ : Over S) [Flat A.hom] (j₁ : T₁ ⟶ T) (j₂ : T₂ ⟶ T)
    (k₁ : T₀ ⟶ T₁) (k₂ : T₀ ⟶ T₂), Milnor j₁.left j₂.left k₁.left k₂.left →
    Function.Surjective (Units.map (A ◁ k₂).left.appTop.hom.toMonoidHom) →
    ∀ c : Pic (A ⊗ T).left, GlobalTheory.CechPic.pull (A ◁ j₁).left c = 0 → GlobalTheory.CechPic.pull (A ◁ j₂).left c = 0 → c = 0 := by
  intro S A T T₁ T₂ T₀ _ j₁ j₂ k₁ k₂ h hs
  have H := GlobalTheory.T.sections_flat_baseChange_affineMilnorSquare_open S A T T₁ T₂ T₀ j₁ j₂ k₁ k₂ h
  have w : k₁ ≫ j₁ = k₂ ≫ j₂ := Over.OverMorphism.ext h.w
  refine eq_zero_of_square _ _ (A ◁ k₁).left (A ◁ k₂).left ?_ (fun W ↦ (H W).1)
    (fun W h₂ ↦ (H W).2 _ le_rfl h₂ le_rfl) hs
  rw [← Over.comp_left, ← Over.comp_left, ← MonoidalCategory.whiskerLeft_comp, ← MonoidalCategory.whiskerLeft_comp, w]

end GlobalTheory.DualOpen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicardClassEqZeroAffineMilnorSquareStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.picardClass_eq_zero_affineMilnorSquare : ∀ (S : Scheme.{0}) (A T T₁ T₂ T₀ : Over S) [Flat A.hom] (j₁ : T₁ ⟶ T) (j₂ : T₂ ⟶ T) (k₁ : T₀ ⟶ T₁) (k₂ : T₀ ⟶ T₂), Milnor j₁.left j₂.left k₁.left k₂.left → Function.Surjective (Units.map (A ◁ k₂).left.appTop.hom.toMonoidHom) → ∀ c : Pic (A ⊗ T).left, GlobalTheory.CechPic.pull (A ◁ j₁).left c = 0 → GlobalTheory.CechPic.pull (A ◁ j₂).left c = 0 → c = 0 := by
  first | exact @GlobalTheory.DualOpen.pic_eq_zero_of_milnor | exact GlobalTheory.DualOpen.pic_eq_zero_of_milnor | (intros; apply GlobalTheory.DualOpen.pic_eq_zero_of_milnor <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocIsoTransportCochainsInIdeal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocIsoTransportCochainsInIdeal
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LiftSys

theorem mul_eq_zero_of_mem_sqMap {R : Type} [CommRing R] {I : Ideal R} {B : Type} [CommRing B] [Algebra R B]
    (hJ : I.map (algebraMap R B) ^ 2 = 0) {u v : B} (hu : u ∈ I.map (algebraMap R B))
    (hv : v ∈ I.map (algebraMap R B)) : u * v = 0 := by
  have := Ideal.mul_mem_mul hu hv
  rwa [← pow_two, hJ, Ideal.zero_eq_bot, Ideal.mem_bot] at this

theorem algHom_apply_mem_map {R : Type} [CommRing R] {I : Ideal R} {A B : Type} [CommRing A] [Algebra R A] [CommRing B]
    [Algebra R B] (f : A →ₐ[R] B) {x : A} (hx : x ∈ I.map (algebraMap R A)) : f x ∈ I.map (algebraMap R B) := by
  have := Ideal.mem_map_of_mem (f : A →+* B) hx
  rwa [Ideal.map_map, AlgHom.comp_algebraMap] at this

theorem eq_of_sub_mem_map {R : Type} [CommRing R] {I : Ideal R} {A B : Type} [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B] (hJ : I.map (algebraMap R B) ^ 2 = 0) (f g : A →ₐ[R] B)
    (h : ∀ b, f b - g b ∈ I.map (algebraMap R B)) {x : A} (hx : x ∈ I.map (algebraMap R A)) : f x = g x := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨r, -, rfl⟩ := hy
    rw [AlgHom.commutes, AlgHom.commutes]
  | zero => rw [map_zero, map_zero]
  | add y y' _ _ h1 h2 => rw [map_add (f := _), map_add (f := _), h1, h2]
  | smul a y hy ih =>
    rw [smul_eq_mul, map_mul, map_mul, ← ih, ← sub_eq_zero, ← sub_mul]
    exact mul_eq_zero_of_mem_sqMap hJ (h a) (algHom_apply_mem_map f hy)

theorem locIso_transport : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), ∀ (S S' : Sys I π s₀) (Φ : S.LocIso S'), (∀ z : Z1 S.F, S.IsIdealValuedLiftSystemCocycle z → ∃ z' : Z1 S'.F, S'.IsIdealValuedLiftSystemCocycle z' ∧ ∀ U V a, z'.1 U V a = Φ.φ V (z.1 U V a)) ∧ (∀ g : C0 S.F, S.IsIdealValuedLiftSystemCochain g → ∀ U V a, d0 S'.F (fun W ↦ Φ.φ W (g W)) U V a = Φ.φ V (d0 S.F g U V a)) ∧ ∀ c ∈ I • (⊤ : Submodule R (Cr hI π s₀)), ∃ (z : Z1 S.F) (z' : Z1 S'.F), S.IsIdealValuedLiftSystemCocycle z ∧ H1.mk _ z = S.r hI c ∧ H1.mk _ z' = S'.r hI c ∧ ∀ U V a, z'.1 U V a = Φ.φ V (z.1 U V a) := by
  intro R R₀ _ _ I hI π hπ hk X₀ s₀ S S' Φ
  have hres : ∀ (U V : AffOp X₀) (a : U ⟶ V) (b : S.F.obj U),
      mp S'.F a (Φ.φ U b) - Φ.φ V (mp S.F a b) ∈ I.map (algebraMap R (S'.F.obj V)) := fun U V a b ↦ by
    rw [← S'.ker V, map_sub, S'.nat a, Φ.red, Φ.red, S.nat a, sub_self]
  have hcomm : ∀ (U V : AffOp X₀) (a : U ⟶ V) (x : S.F.obj U), x ∈ I.map (algebraMap R (S.F.obj U)) →
      mp S'.F a (Φ.φ U x) = Φ.φ V (mp S.F a x) := fun U V a x hx ↦
    eq_of_sub_mem_map (map_sq hI _) ((mp S'.F a).comp (Φ.φ U : S.F.obj U →ₐ[R] S'.F.obj U))
      ((Φ.φ V : S.F.obj V →ₐ[R] S'.F.obj V).comp (mp S.F a)) (hres U V a) hx
  have c1 : ∀ z : Z1 S.F, S.IsIdealValuedLiftSystemCocycle z → ∃ z' : Z1 S'.F, S'.IsIdealValuedLiftSystemCocycle z' ∧ ∀ U V a, z'.1 U V a = Φ.φ V (z.1 U V a) := by
    intro z hz
    refine ⟨⟨fun U V a ↦ Φ.φ V (z.1 U V a), ?_⟩, fun U V a ↦ ?_, fun _ _ _ ↦ rfl⟩
    · intro U V W a b
      show Φ.φ W (z.1 U W (a ≫ b)) = mp S'.F b (Φ.φ V (z.1 U V a)) + Φ.φ W (z.1 V W b)
      rw [Z1.comp z a b, map_add (f := _), hcomm V W b _ (hz U V a)]
    · exact algHom_apply_mem_map (Φ.φ V : S.F.obj V →ₐ[R] S'.F.obj V) (hz U V a)
  have c2 : ∀ g : C0 S.F, S.IsIdealValuedLiftSystemCochain g → ∀ U V a,
      d0 S'.F (fun W ↦ Φ.φ W (g W)) U V a = Φ.φ V (d0 S.F g U V a) := by
    intro g hg U V a
    rw [amitsur_d0_apply, amitsur_d0_apply, map_sub, hcomm U V a _ (hg U)]
  refine ⟨c1, c2, fun c hc ↦ ?_⟩
  refine Submodule.smul_induction_on hc ?_ ?_
  · intro r hr c₀ _
    obtain ⟨f, rfl⟩ := H1.mk_surjective _ c₀
    let z : Z1 S.F := r • (S.coef hI).pullbackOneCocycle f
    have hzI : S.IsIdealValuedLiftSystemCocycle z := fun U V a ↦ by
      show r • (show S.F.obj V from ev f ((S.thick hI).map a)) ∈ I.map (algebraMap R (S.F.obj V))
      rw [Algebra.smul_def, mul_comm]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hr)
    obtain ⟨z', -, hz'⟩ := c1 z hzI
    refine ⟨z, z', hzI, ?_, ?_, hz'⟩
    · show H1.mk _ (r • _) = S.r hI (r • H1.mk _ f)
      rw [map_smul, map_smul]
      rfl
    · rw [map_smul, show S'.r hI (H1.mk _ f) = H1.mk _ ((S'.coef hI).pullbackOneCocycle f) from rfl, ← map_smul,
        H1.mk_eq_mk]
      let ΦH : ∀ W : AffOp X₀, S.thickObj hI W ⟶ S'.thickObj hI W := fun W ↦
        S.thickHom S' hI (𝟙 W) (Φ.φ W : S.F.obj W →ₐ[R] S'.F.obj W)
          (fun b ↦ (Φ.red W b).trans (mp_id (OAff s₀) W (S.p W b)).symm)
      refine ⟨fun W ↦ -(r • @id (S'.F.obj W) (ev f (ΦH W))), ?_⟩
      funext U V a
      have hz'' := hz' U V a
      have e1 : @id (S'.F.obj V) (ev f (ΦH U ≫ (S'.thick hI).map a)) =
          mp S'.F a (@id (S'.F.obj U) (ev f (ΦH U))) + @id (S'.F.obj V) (ev f ((S'.thick hI).map a)) :=
        ev_comp f (ΦH U) ((S'.thick hI).map a)
      have e2 : @id (S'.F.obj V) (ev f ((S.thick hI).map a ≫ ΦH V)) =
          Φ.φ V (@id (S.F.obj V) (ev f ((S.thick hI).map a))) + @id (S'.F.obj V) (ev f (ΦH V)) :=
        ev_comp f ((S.thick hI).map a) (ΦH V)
      have e3 : algebraMap R (S'.F.obj V) r * (@id (S'.F.obj V) (ev f ((S.thick hI).map a ≫ ΦH V)) -
          @id (S'.F.obj V) (ev f (ΦH U ≫ (S'.thick hI).map a))) = 0 := by
        obtain ⟨⟨Q, hQ⟩, tay⟩ := GlobalTheory.T.crystallineCocycle_firstOrder_taylor_sqZero R R₀ I hI π hπ hk X₀ s₀ S S' U V
        obtain ⟨θ, hθ, -⟩ := (GlobalTheory.T.algHom_lifts_sqZero_classified_by_differentials R R₀ (S.F.obj U) (Sec s₀ U.unop.1) (S'.F.obj V) I hI π hπ (S.p U)
          (S.semi U) (S.surj U) (S.ker U) ((mp S'.F a).comp (Φ.φ U : S.F.obj U →ₐ[R] S'.F.obj U))).1
          ((Φ.φ V : S.F.obj V →ₐ[R] S'.F.obj V).comp (mp S.F a)) (hres U V a)
        have t := tay Q hQ (ΦH U ≫ (S'.thick hI).map a) ((S.thick hI).map a ≫ ΦH V) θ hθ f
        have t' : @id (S'.F.obj V) (ev f ((S.thick hI).map a ≫ ΦH V)) -
            @id (S'.F.obj V) (ev f (ΦH U ≫ (S'.thick hI).map a)) ∈ I.map (algebraMap R (S'.F.obj V)) := by
          rw [show @id (S'.F.obj V) (ev f ((S.thick hI).map a ≫ ΦH V)) -
            @id (S'.F.obj V) (ev f (ΦH U ≫ (S'.thick hI).map a)) = _ from t]
          exact hθ.mem _
        exact mul_eq_zero_of_mem_sqMap (map_sq hI _) (Ideal.mem_map_of_mem _ hr) t'
      show -(r • @id (S'.F.obj V) (ev f (ΦH V))) - mp S'.F a (-(r • @id (S'.F.obj U) (ev f (ΦH U)))) =
        z'.1 U V a - r • @id (S'.F.obj V) (ev f ((S'.thick hI).map a))
      rw [hz'']
      show _ = Φ.φ V (r • @id (S.F.obj V) (ev f ((S.thick hI).map a))) - _
      rw [map_neg, map_smul, map_smul]
      simp only [Algebra.smul_def]
      linear_combination -(algebraMap R (S'.F.obj V) r) * (e1 - e2) - e3
  · rintro x y ⟨z₁, z₁', h₁, hx₁, hx₁', e₁⟩ ⟨z₂, z₂', h₂, hy₂, hy₂', e₂⟩
    refine ⟨z₁ + z₂, z₁' + z₂', fun U V a ↦ ?_, ?_, ?_, fun U V a ↦ ?_⟩
    · show z₁.1 U V a + z₂.1 U V a ∈ _
      exact Ideal.add_mem _ (h₁ U V a) (h₂ U V a)
    · rw [map_add (f := _), map_add (f := _), hx₁, hy₂]
    · rw [map_add (f := _), map_add (f := _), hx₁', hy₂']
    · show z₁'.1 U V a + z₂'.1 U V a = Φ.φ V (z₁.1 U V a + z₂.1 U V a)
      rw [map_add (f := _), e₁, e₂]

end GlobalTheory.LiftSys
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocIsoTransportCochainsInIdealStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locIso_transport_cochains_in_ideal : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), ∀ (S S' : Sys I π s₀) (Φ : S.LocIso S'), (∀ z : Z1 S.F, S.IsIdealValuedLiftSystemCocycle z → ∃ z' : Z1 S'.F, S'.IsIdealValuedLiftSystemCocycle z' ∧ ∀ U V a, z'.1 U V a = Φ.φ V (z.1 U V a)) ∧ (∀ g : C0 S.F, S.IsIdealValuedLiftSystemCochain g → ∀ U V a, d0 S'.F (fun W ↦ Φ.φ W (g W)) U V a = Φ.φ V (d0 S.F g U V a)) ∧ ∀ c ∈ I • (⊤ : Submodule R (Cr hI π s₀)), ∃ (z : Z1 S.F) (z' : Z1 S'.F), S.IsIdealValuedLiftSystemCocycle z ∧ H1.mk _ z = S.r hI c ∧ H1.mk _ z' = S'.r hI c ∧ ∀ U V a, z'.1 U V a = Φ.φ V (z.1 U V a) := by
  first | exact @GlobalTheory.LiftSys.locIso_transport | exact GlobalTheory.LiftSys.locIso_transport | (intros; apply GlobalTheory.LiftSys.locIso_transport <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationBundleGenericFibreDescent
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationBundleGenericFibreDescent
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory

namespace GenericBundleDescent

variable {X X' Y Z : Scheme.{0}}

theorem pull_both {M : LB X} {N : LB X'} {a : Y ⟶ X} {b : Y ⟶ X'} (H : LBIso (M.pull a) (N.pull b)) (h : Z ⟶ Y)
    {a' : Z ⟶ X} {b' : Z ⟶ X'} (ea : a' = h ≫ a) (eb : b' = h ≫ b) : LBIso (M.pull a') (N.pull b') :=
  LBIso.chartPull (chartPullSame M _ _ _ h fun _ => ea) (chartPullSame N _ _ _ h fun _ => eb) H

theorem pull_right {M : LB Y} {N : LB X'} {b : Y ⟶ X'} (H : LBIso M (N.pull b)) (h : Z ⟶ Y)
    {b' : Z ⟶ X'} (eb : b' = h ≫ b) : LBIso (M.pull h) (N.pull b') :=
  LBIso.chartPull (Geo.Tor.chartPullPull M h h rfl) (chartPullSame N _ _ _ h fun _ => eb) H

theorem pull_pull {M : LB X} {N : LB Z} {a : Y ⟶ X} {h : Z ⟶ Y} (H : LBIso (M.pull (h ≫ a)) N) :
    LBIso ((M.pull a).pull h) N :=
  LBIso.chartPull (chartPullLinComb M a (fun _ : PUnit => h) (fun _ => h ≫ a) (fun _ => 1) (𝟙 Z)
    fun _ => (Category.id_comp _).symm) (chartPullId N) H

theorem mono_jK (R : Type) [CommRing R] : Mono (jK R) := by
  have : IsPreimmersion (jK R) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  infer_instance

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

end GenericBundleDescent


open GenericBundleDescent in
theorem unif_bundle_generic_descent : ∀ (R W R₂ W₂ K' Ω' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing W] [IsDomain W] [IsLocalRing W] [CommRing R₂] [IsDomain R₂] [IsLocalRing R₂] [CommRing W₂] [IsDomain W₂] [IsLocalRing W₂] [Field K'] [Field Ω'] (φ : R →+* W) (ρ : R →+* R₂) (σ : W →+* W₂) (φ₂ : R₂ →+* W₂) (io : FractionRing R →+* K') (j : FractionRing W →+* Ω') (l : K' →+* Ω') (i : K' ≃+* FractionRing R₂) (j₂ : FractionRing W₂ →+* Ω'), Function.Injective φ → Function.Injective ρ → Function.Injective σ → Function.Injective φ₂ → φ₂.comp ρ = σ.comp φ → (∀ r, l (io (algebraMap R _ r)) = j (algebraMap W _ (φ r))) → (∀ r, i (io (algebraMap R _ r)) = algebraMap R₂ _ (ρ r)) → (∀ w, j₂ (algebraMap W₂ _ (σ w)) = j (algebraMap W _ w)) → (∀ r, j₂ (algebraMap W₂ _ (φ₂ r)) = l (i.symm (algebraMap R₂ _ r))) → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A) (GW : Over (Sp W)) [GrpObj GW] [IsCommMonObj GW] (βW : GW.left ⟶ G.left) (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW) (α : AW.A.left ⟶ A.A.left), IsGrpPullback GW G (spMap φ) βW → UW.gen.inv.left ≫ pullback.fst GW.hom (jK W) ≫ βW = α ≫ gen.inv.left ≫ pullback.fst G.hom (jK R) → ∀ (A₁ : PolAV (Sp K')) (α₁ : A₁.A.left ⟶ A.A.left) (p : pullback AW.A.hom (spMap j) ⟶ A₁.A.left), IsGrpPullback A₁.A A.A (spMap io) α₁ → p ≫ α₁ = pullback.fst _ _ ≫ α → p ≫ A₁.A.hom = pullback.snd _ _ ≫ spMap l → LBIso (AW.L.pull (pullback.fst AW.A.hom (spMap j))) (A₁.L.pull p) → ∀ (G₂ : Over (Sp R₂)) [GrpObj G₂] [IsCommMonObj G₂] (β : G₂.left ⟶ G.left) (A₂ : PolAV (Sp (FractionRing R₂))) (gen₂ : ((Over.pullback (jK R₂)).obj G₂) ≅ A₂.A) (q : A₂.A.left ⟶ A₁.A.left), IsGrpPullback G₂ G (spMap ρ) β → IsGrpPullback A₂.A A₁.A (spMap i.toRingHom) q → LBIso A₂.L (A₁.L.pull q) → gen₂.inv.left ≫ pullback.fst G₂.hom (jK R₂) ≫ β = q ≫ α₁ ≫ gen.inv.left ≫ pullback.fst G.hom (jK R) → ∀ (GW' : Over (Sp W₂)) [GrpObj GW'] [IsCommMonObj GW'] (βW' : GW'.left ⟶ G₂.left) (τ : GW'.left ⟶ GW.left) (DW' : DegData W₂ (maximalIdeal W₂)) (AW' : PolAV (Sp (FractionRing W₂))) (UW' : Unif (maximalIdeal W₂) DW' AW' GW') (κ : pullback GW'.hom (jK W₂) ⟶ pullback G₂.hom (jK R₂)), IsGrpPullback GW' G₂ (spMap φ₂) βW' → IsGrpPullback GW' GW (spMap σ) τ → βW' ≫ β = τ ≫ βW → κ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ βW' → LBIso (UW'.LG.L.pull (pullback.fst GW'.hom (jK W₂))) (UW.LG.L.pull (pullback.fst GW'.hom (jK W₂) ≫ τ)) → LBIso (UW'.LG.L.pull (pullback.fst GW'.hom (jK W₂))) ((A₂.L.pull gen₂.hom.left).pull κ) := by
  intro R W R₂ W₂ K' Ω' _ _ _ _ _ _ _ _ _ _ _ _ _ _ φ ρ σ φ₂ io j l i j₂ _ _ _ _ _ _ _ hj₂σ hj₂φ G _ _ A gen GW _ _ βW DW
    AW UW α _ hα A₁ α₁ p hA₁ hp₁ hp₂ hLp G₂ _ _ β A₂ gen₂ q _ hq hLq hgq GW' _ _ βW' τ DW' AW' UW' κ hβW' hτ hsq hκ hL
  have := mono_jK R
  have := mono_jK R₂
  let π := pullback.fst (pullback.snd GW'.hom (jK W₂)) (spMap j₂)
  let s := pullback.snd (pullback.snd GW'.hom (jK W₂)) (spMap j₂)
  have hπ : π ≫ pullback.fst GW'.hom (jK W₂) ≫ GW'.hom = s ≫ spMap j₂ ≫ jK W₂ := by
    rw [pullback.condition, pullback.condition_assoc]
  have e₁ : spMap j₂ ≫ jK W₂ ≫ spMap σ = spMap j ≫ jK W := by
    rw [sp_comp, sp_comp, sp_comp]
    exact congrArg spMap (RingHom.ext hj₂σ)
  have e₂ : spMap j₂ ≫ jK W₂ ≫ spMap φ₂ = spMap (l.comp i.symm.toRingHom) ≫ jK R₂ := by
    rw [sp_comp, sp_comp, sp_comp]
    exact congrArg spMap (RingHom.ext hj₂φ)
  have e₃ : spMap (l.comp i.symm.toRingHom) ≫ spMap i.toRingHom = spMap l := by
    rw [sp_comp]
    exact congrArg spMap (RingHom.ext fun x => by simp)
  obtain ⟨ℓ, hℓ₁, hℓ₂⟩ : ∃ ℓ : _ ⟶ pullback GW.hom (jK W),
      ℓ ≫ pullback.fst _ _ = π ≫ pullback.fst GW'.hom (jK W₂) ≫ τ ∧ ℓ ≫ pullback.snd _ _ = s ≫ spMap j :=
    ⟨pullback.lift _ _ (by
      rw [Category.assoc, Category.assoc, hτ.1.w, reassoc_of% hπ, e₁, Category.assoc]),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have wW : UW.gen.hom.left ≫ AW.A.hom = pullback.snd GW.hom (jK W) := Over.w UW.gen.hom
  have w₂ : gen₂.hom.left ≫ A₂.A.hom = pullback.snd G₂.hom (jK R₂) := Over.w gen₂.hom
  let gW : pullback GW.hom (jK W) ⟶ AW.A.left := UW.gen.hom.left
  let g₂ : pullback G₂.hom (jK R₂) ⟶ A₂.A.left := gen₂.hom.left
  let gi : A.A.left ⟶ pullback G.hom (jK R) := gen.inv.left
  have wW' : gW ≫ AW.A.hom = pullback.snd GW.hom (jK W) := wW
  have w₂' : g₂ ≫ A₂.A.hom = pullback.snd G₂.hom (jK R₂) := w₂
  have hα' : gW ≫ α ≫ gi ≫ pullback.fst G.hom (jK R) = pullback.fst GW.hom (jK W) ≫ βW := by
    have c : UW.gen.hom.left ≫ UW.gen.inv.left = 𝟙 _ := congrArg Over.Hom.left UW.gen.hom_inv_id
    exact (congrArg (UW.gen.hom.left ≫ ·) hα.symm).trans (by rw [reassoc_of% c])
  have hgq' : g₂ ≫ q ≫ α₁ ≫ gi ≫ pullback.fst G.hom (jK R) = pullback.fst G₂.hom (jK R₂) ≫ β := by
    have c : gen₂.hom.left ≫ gen₂.inv.left = 𝟙 _ := congrArg Over.Hom.left gen₂.hom_inv_id
    exact (congrArg (gen₂.hom.left ≫ ·) hgq.symm).trans (by rw [reassoc_of% c])
  obtain ⟨n, hn₁, hn₂⟩ : ∃ n : _ ⟶ pullback AW.A.hom (spMap j),
      n ≫ pullback.fst _ _ = ℓ ≫ gW ∧ n ≫ pullback.snd _ _ = s :=
    ⟨pullback.lift _ _ (by rw [Category.assoc, wW', hℓ₂]), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have : IsIso gi := inferInstanceAs (IsIso ((Over.forget _).map gen.inv))
  have hm : n ≫ p = π ≫ κ ≫ g₂ ≫ q := by
    refine hA₁.1.hom_ext ?_ ?_
    · rw [← cancel_mono gi, ← cancel_mono (pullback.fst G.hom (jK R))]
      simp only [Category.assoc]
      rw [reassoc_of% hp₁, reassoc_of% hn₁, hα', reassoc_of% hℓ₁, hgq', reassoc_of% hκ, hsq]
    · have k : π ≫ κ ≫ pullback.snd G₂.hom (jK R₂) = s ≫ spMap (l.comp i.symm.toRingHom) := by
        rw [← cancel_mono (jK R₂)]
        simp only [Category.assoc]
        rw [← pullback.condition, reassoc_of% hκ, hβW'.1.w, reassoc_of% hπ, e₂]
      simp only [Category.assoc]
      rw [hp₂, reassoc_of% hn₂, hq.1.w, reassoc_of% w₂', reassoc_of% k, e₃]
  have H₁ : LBIso (AW.L.pull (ℓ ≫ gW)) (UW.LG.L.pull (π ≫ pullback.fst GW'.hom (jK W₂) ≫ τ)) :=
    pull_both (a := gW) UW.ext ℓ rfl hℓ₁.symm
  have H₂ : LBIso (AW.L.pull (ℓ ≫ gW)) (A₁.L.pull (n ≫ p)) := pull_both hLp n hn₁.symm rfl
  have H₃ : LBIso (A₂.L.pull ((π ≫ κ) ≫ g₂)) (A₁.L.pull (n ≫ p)) :=
    pull_right hLq _ (by simp only [hm, Category.assoc])
  have hG := UW.LG.isLB
  have H : LBIso ((UW.LG.L.pull (pullback.fst GW'.hom (jK W₂) ≫ τ)).pull π) (((A₂.L.pull g₂).pull κ).pull π) :=
    pull_pull (pull_pull (pull_pull (LBIso.trans (pull_isLB A₂.isLB _) (pull_isLB A₁.isLB _) (pull_isLB hG _) H₃
      (LBIso.trans (pull_isLB A₁.isLB _) (pull_isLB AW.isLB _) (pull_isLB hG _) H₂.symm H₁)))).symm
  let g' : pullback GW'.hom (jK W₂) ⟶ AW'.A.left := UW'.gen.hom.left
  have : IsIso g' := inferInstanceAs (IsIso ((Over.forget _).map UW'.gen.hom))
  have w' : g' ≫ AW'.A.hom = pullback.snd GW'.hom (jK W₂) := Over.w UW'.gen.hom
  have := AW'.isAb.smooth
  have := AW'.isAb.proper
  have hc := AW'.isAb.geomConnected
  have hD := (lb_gen_iso_descend_field (FractionRing W₂) Ω' j₂ _ _ (pullback.snd GW'.hom (jK W₂)) s π
    (by rw [← w']; infer_instance) (by rw [← w']; infer_instance)
    (by rw [← w']; exact (MorphismProperty.of_isPullback (P := @GeometricallyConnected)
      (IsPullback.of_horiz_isIso ⟨(Category.comp_id (g' ≫ AW'.A.hom)).symm⟩) hc))
    (IsPullback.of_hasPullback _ _)).2 _ _ (pull_isLB hG _) (pull_isLB (pull_isLB A₂.isLB _) _) H
  exact LBIso.trans (pull_isLB UW'.LG.isLB _) (pull_isLB hG _) (pull_isLB (pull_isLB A₂.isLB _) _) hL hD

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationBundleGenericFibreDescentStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisation_bundle_genericFibre_descent : ∀ (R W R₂ W₂ K' Ω' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing W] [IsDomain W] [IsLocalRing W] [CommRing R₂] [IsDomain R₂] [IsLocalRing R₂] [CommRing W₂] [IsDomain W₂] [IsLocalRing W₂] [Field K'] [Field Ω'] (φ : R →+* W) (ρ : R →+* R₂) (σ : W →+* W₂) (φ₂ : R₂ →+* W₂) (io : FractionRing R →+* K') (j : FractionRing W →+* Ω') (l : K' →+* Ω') (i : K' ≃+* FractionRing R₂) (j₂ : FractionRing W₂ →+* Ω'), Function.Injective φ → Function.Injective ρ → Function.Injective σ → Function.Injective φ₂ → φ₂.comp ρ = σ.comp φ → (∀ r, l (io (algebraMap R _ r)) = j (algebraMap W _ (φ r))) → (∀ r, i (io (algebraMap R _ r)) = algebraMap R₂ _ (ρ r)) → (∀ w, j₂ (algebraMap W₂ _ (σ w)) = j (algebraMap W _ w)) → (∀ r, j₂ (algebraMap W₂ _ (φ₂ r)) = l (i.symm (algebraMap R₂ _ r))) → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A) (GW : Over (Sp W)) [GrpObj GW] [IsCommMonObj GW] (βW : GW.left ⟶ G.left) (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW) (α : AW.A.left ⟶ A.A.left), IsGrpPullback GW G (spMap φ) βW → UW.gen.inv.left ≫ pullback.fst GW.hom (jK W) ≫ βW = α ≫ gen.inv.left ≫ pullback.fst G.hom (jK R) → ∀ (A₁ : PolAV (Sp K')) (α₁ : A₁.A.left ⟶ A.A.left) (p : pullback AW.A.hom (spMap j) ⟶ A₁.A.left), IsGrpPullback A₁.A A.A (spMap io) α₁ → p ≫ α₁ = pullback.fst _ _ ≫ α → p ≫ A₁.A.hom = pullback.snd _ _ ≫ spMap l → LBIso (AW.L.pull (pullback.fst AW.A.hom (spMap j))) (A₁.L.pull p) → ∀ (G₂ : Over (Sp R₂)) [GrpObj G₂] [IsCommMonObj G₂] (β : G₂.left ⟶ G.left) (A₂ : PolAV (Sp (FractionRing R₂))) (gen₂ : ((Over.pullback (jK R₂)).obj G₂) ≅ A₂.A) (q : A₂.A.left ⟶ A₁.A.left), IsGrpPullback G₂ G (spMap ρ) β → IsGrpPullback A₂.A A₁.A (spMap i.toRingHom) q → LBIso A₂.L (A₁.L.pull q) → gen₂.inv.left ≫ pullback.fst G₂.hom (jK R₂) ≫ β = q ≫ α₁ ≫ gen.inv.left ≫ pullback.fst G.hom (jK R) → ∀ (GW' : Over (Sp W₂)) [GrpObj GW'] [IsCommMonObj GW'] (βW' : GW'.left ⟶ G₂.left) (τ : GW'.left ⟶ GW.left) (DW' : DegData W₂ (maximalIdeal W₂)) (AW' : PolAV (Sp (FractionRing W₂))) (UW' : Unif (maximalIdeal W₂) DW' AW' GW') (κ : pullback GW'.hom (jK W₂) ⟶ pullback G₂.hom (jK R₂)), IsGrpPullback GW' G₂ (spMap φ₂) βW' → IsGrpPullback GW' GW (spMap σ) τ → βW' ≫ β = τ ≫ βW → κ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ βW' → LBIso (UW'.LG.L.pull (pullback.fst GW'.hom (jK W₂))) (UW.LG.L.pull (pullback.fst GW'.hom (jK W₂) ≫ τ)) → LBIso (UW'.LG.L.pull (pullback.fst GW'.hom (jK W₂))) ((A₂.L.pull gen₂.hom.left).pull κ) := by
  first | exact @GlobalTheory.unif_bundle_generic_descent | exact GlobalTheory.unif_bundle_generic_descent | (intros; apply GlobalTheory.unif_bundle_generic_descent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmissibleProjectiveThetaModelOverModel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmissibleProjectiveThetaModelOverModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.SegreModel

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω}

theorem hasDiv_left {A B : Type} {a : A → Ω} {b : B → Ω} (h : M.HasDiv fun p : A × B => a p.1 * b p.2) :
    M.HasDiv a := fun z => by
  obtain ⟨i, h0, hi⟩ := h z
  refine ⟨i.1, left_ne_zero_of_mul h0, fun j => ?_⟩
  have := hi (j, i.2)
  rwa [mul_div_mul_right _ _ (right_ne_zero_of_mul h0)] at this

theorem hasDiv_right {A B : Type} {a : A → Ω} {b : B → Ω} (h : M.HasDiv fun p : A × B => a p.1 * b p.2) :
    M.HasDiv b := fun z => by
  obtain ⟨i, h0, hi⟩ := h z
  refine ⟨i.2, right_ne_zero_of_mul h0, fun j => ?_⟩
  have := hi (i.1, j)
  rwa [mul_div_mul_left _ _ (left_ne_zero_of_mul h0)] at this

theorem hasDiv_of_prod {K : Type} [Fintype K] {J : K → Type} {t : ∀ k, J k → Ω}
    (h : M.HasDiv fun i : ∀ k, J k => ∏ k, t k (i k)) (k : K) : M.HasDiv (t k) := fun z => by
  obtain ⟨i, h0, hi⟩ := h z
  have hne := Finset.prod_ne_zero_iff.1 h0
  refine ⟨i k, hne k (Finset.mem_univ _), fun j => ?_⟩
  have := hi (Function.update i k j)
  have e : ∏ l ∈ Finset.univ.erase k, t l (Function.update i k j l) = ∏ l ∈ Finset.univ.erase k, t l (i l) :=
    Finset.prod_congr rfl fun l hl => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]
  have h1 : ∏ l ∈ Finset.univ.erase k, t l (i l) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun l _ => hne l (Finset.mem_univ _)
  simp only at this
  rwa [← Finset.mul_prod_erase _ _ (Finset.mem_univ k), ← Finset.mul_prod_erase _ (fun l => t l (i l)) (Finset.mem_univ k),
    e, Function.update_self, mul_div_mul_right _ _ h1] at this

theorem subfield_eq_top {J : Type} {c : J → Ω} (h : M.IsCl c) (F : Subfield Ω)
    (ho : Set.range (algebraMap o Ω) ⊆ F) (hc : ∀ i j, c i ≠ 0 → c j / c i ∈ F) : F = ⊤ := by
  obtain ⟨i, hi, -⟩ := h.1 (genericPoint M.Z)
  obtain ⟨U, hU, hD, hR⟩ := h.2 i hi
  have hne : (U : Set M.Z).Nonempty := ⟨genericPoint M.Z, hD ▸ RatModel.div_genericPoint hi⟩
  have hle : ∀ x ∈ M.ringOn U, x ∈ F := by
    intro x hx
    rw [hR] at hx
    induction hx using Algebra.adjoin_induction with
    | mem _ h' => obtain ⟨j, rfl⟩ := h'; exact hc i j hi
    | algebraMap r => exact ho ⟨r, rfl⟩
    | add a b _ _ ha hb => exact add_mem ha hb
    | mul a b _ _ ha hb => exact mul_mem ha hb
  refine top_unique fun x _ => ?_
  obtain ⟨a, b, -, rfl⟩ := RatModel.exists_eq_div hU hne x
  exact div_mem (hle _ ((RatModel.mem_ringOn_iff_exists hne).2 ⟨a, rfl⟩))
    (hle _ ((RatModel.mem_ringOn_iff_exists hne).2 ⟨b, rfl⟩))

theorem finite_of_eq_top (F : Subfield Ω) (h : F = ⊤) : Module.Finite F Ω :=
  Module.Finite.of_surjective (Algebra.linearMap F Ω) fun x => ⟨⟨x, h ▸ trivial⟩, rfl⟩

end GlobalTheory.Poinc.SegreModel

theorem GlobalTheory.Poinc.exists_admissible_projective_theta_model : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real), S.Big → ∀ M₁ : RatModel o Ω, IsProjOver M₁.s → ∀ (K : Type) [Finite K] (Jk : K → Type) [∀ k, Finite (Jk k)] (t : ∀ k, Jk k → Ω), (∀ k j, t k j ≠ 0) → ∃ (Y : RatModel o Ω) (πY : Y.Z ⟶ M₁.Z) (U₀ : Y.Z.Opens) (EE : Y.Lat S.J) (_ : ZHOut ρ Y U₀ EE), M₁.IsHom Y (AlgHom.id o Ω) πY ∧ IsProper πY ∧ S.admitted Y U₀ ∧ S.IsEE Y U₀ EE ∧ ∀ k, Nonempty (Jk k) → Y.HasDiv (t k) := by
  intro o Ω _ _ _ _ S ρ hBig M₁ hM₁ K _ Jk _ t ht
  obtain ⟨n, c, hc⟩ := RatModel.exists_isCl_of_isProjOver hM₁
  have hN2 := S.N_ge
  haveI hN0 : NeZero S.N := ⟨by omega⟩
  haveI : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by have := S.r_pos; omega) (by omega)⟩
  haveI : NeZero ((S.r * S.N) ^ 2) := ⟨pow_ne_zero _ (NeZero.ne _)⟩
  haveI : Finite (AddSubgroup S.Gam) :=
    Finite.of_injective (fun H : AddSubgroup S.Gam => (H : Set S.Gam)) SetLike.coe_injective
  haveI : ∀ T₀ : AddSubgroup S.Gam, Finite (T₀ →+ ZMod S.N) := fun T₀ =>
    Finite.of_injective (fun f : T₀ →+ ZMod S.N => (f : T₀ → ZMod S.N)) DFunLike.coe_injective
  let K₁ := {k : K // Nonempty (Jk k)}
  let K₂ := {d : Σ T : AddSubgroup S.Gam, (T →+ ZMod S.N) // S.FF d.1 d.2 ≠ 0}
  letI : Fintype K₁ := Fintype.ofFinite _
  letI : Fintype K₂ := Fintype.ofFinite _
  let J₂ : K₂ → Type := fun d => S.J × (d.1.1 → ZMod ((S.r * S.N) ^ 2))
  let B := (∀ k : K₁, Jk k.1) × (∀ d : K₂, J₂ d)
  let b : B → Ω := fun p => (∏ k : K₁, t k.1 (p.1 k)) * ∏ d : K₂, S.FF d.1.1 d.1.2 (p.2 d)
  haveI : Finite B := inferInstance
  letI : Fintype (Fin (n + 1) × B) := Fintype.ofFinite _
  obtain ⟨p₀, hp₀⟩ : ∃ p, b p ≠ 0 := by
    choose κ hκ using fun d : K₂ => Function.ne_iff.1 d.2
    exact ⟨(fun k => k.2.some, κ), mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => ht _ _)
      (Finset.prod_ne_zero_iff.2 fun d _ => hκ d)⟩
  obtain ⟨i₀, hi₀, -⟩ := hc.1 (genericPoint M₁.Z)
  obtain ⟨x₀, hx₀⟩ := S.th_ne
  obtain ⟨Y, U₀, EE, hO, hD, hE, ⟨FinalForm⟩⟩ := GlobalTheory.zhSt_holds o Ω S ρ hBig (Fin (n + 1) × B) (fun p => c p.1 * b p.2)
    ⟨(i₀, p₀), mul_ne_zero hi₀ hp₀⟩ (by
      refine SegreModel.finite_of_eq_top _ (SegreModel.subfield_eq_top hc _
        (Set.subset_union_left.trans Subfield.subset_closure) fun i j _ =>
        Subfield.subset_closure (Or.inr ⟨(x₀, i, p₀), (x₀, j, p₀), ?_⟩))
      rw [mul_div_mul_left _ _ hx₀, mul_div_mul_right _ _ hp₀])
  have hb : Y.HasDiv b := SegreModel.hasDiv_right hD
  have h1 := SegreModel.hasDiv_left (a := fun q : ∀ k : K₁, Jk k.1 => ∏ k : K₁, t k.1 (q k))
    (b := fun q : ∀ d : K₂, J₂ d => ∏ d : K₂, S.FF d.1.1 d.1.2 (q d)) hb
  have h2 := SegreModel.hasDiv_right (a := fun q : ∀ k : K₁, Jk k.1 => ∏ k : K₁, t k.1 (q k))
    (b := fun q : ∀ d : K₂, J₂ d => ∏ d : K₂, S.FF d.1.1 d.1.2 (q d)) hb
  obtain ⟨π, hπ⟩ := hc.exists_isHom (M' := Y) (φ := AlgHom.id o Ω) (SegreModel.hasDiv_left hD)
  refine ⟨Y, π, U₀, EE, FinalForm, hπ, ?_, ⟨hO, fun T c' _ h => ?_⟩, hE, fun k hk => ?_⟩
  · haveI := M₁.sep
    haveI : IsProper (π ≫ M₁.s) := by
      rw [hπ.inducedModelMorphism_comp_structureMap]
      obtain ⟨m, j, hj, hs⟩ := hO.proj
      rw [← hs]
      have := isProper_str o m
      infer_instance
    exact IsProper.of_comp π M₁.s
  · exact SegreModel.hasDiv_of_prod (t := fun d : K₂ => S.FF d.1.1 d.1.2) h2 ⟨⟨T, c'⟩, h⟩
  · exact SegreModel.hasDiv_of_prod (t := fun k : K₁ => t k.1) h1 ⟨k, hk⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmissibleProjectiveThetaModelOverModelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_admissible_projective_theta_model_over_model : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real), S.Big → ∀ M₁ : RatModel o Ω, IsProjOver M₁.s → ∀ (K : Type) [Finite K] (Jk : K → Type) [∀ k, Finite (Jk k)] (t : ∀ k, Jk k → Ω), (∀ k j, t k j ≠ 0) → ∃ (Y : RatModel o Ω) (πY : Y.Z ⟶ M₁.Z) (U₀ : Y.Z.Opens) (EE : Y.Lat S.J) (_ : ZHOut ρ Y U₀ EE), M₁.IsHom Y (AlgHom.id o Ω) πY ∧ IsProper πY ∧ S.admitted Y U₀ ∧ S.IsEE Y U₀ EE ∧ ∀ k, Nonempty (Jk k) → Y.HasDiv (t k) := by
  first | exact @GlobalTheory.Poinc.exists_admissible_projective_theta_model | exact GlobalTheory.Poinc.exists_admissible_projective_theta_model | (intros; apply GlobalTheory.Poinc.exists_admissible_projective_theta_model <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentCocycleDefectOfCompatible
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentCocycleDefectOfCompatible
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open GlobalTheory.LBDescent GlobalTheory.DescNorm
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DescDefect

variable {X Y : Scheme.{0}} (f : X ⟶ Y)

theorem compat_gm {L : LB X} {φ : ∀ i j, Γ(pullback f f, chart f L i j)ˣ} (hC : DescCompat f L φ)
    {T : Scheme.{0}} (s : T ⟶ pullback f f) (t : T) (i i' j j' : L.ι)
    (hi : pullback.fst f f (s t) ∈ L.U i) (hi' : pullback.fst f f (s t) ∈ L.U i')
    (hj : pullback.snd f f (s t) ∈ L.U j) (hj' : pullback.snd f f (s t) ∈ L.U j') :
    gm s t _ (φ i' j') =
      gm (s ≫ pullback.fst f f) t _ (L.g i i') * gm s t _ (φ i j) * gm (s ≫ pullback.snd f f) t _ (L.g j' j) := by
  have l₁ : chart f L i j ⊓ chart f L i' j' ≤ pullback.fst f f ⁻¹ᵁ (L.U i ⊓ L.U i') :=
    fun z hz => ⟨hz.1.1, hz.2.1⟩
  have l₂ : chart f L i j ⊓ chart f L i' j' ≤ pullback.snd f f ⁻¹ᵁ (L.U j' ⊓ L.U j) :=
    fun z hz => ⟨hz.2.2, hz.1.2⟩
  have hO : res (inf_le_right : chart f L i j ⊓ chart f L i' j' ≤ _) (φ i' j') =
      res l₁ (pullU (pullback.fst f f) _ (L.g i i')) * res inf_le_left (φ i j) *
        res l₂ (pullU (pullback.snd f f) _ (L.g j' j)) := by
    apply unit_ext
    intro z hz
    rw [map_mul, map_mul, gm_res _ z _ hz, gm_res _ z _ hz, gm_res _ z _ hz, gm_res _ z _ hz,
      gm_pull (𝟙 _) (pullback.fst f f) z _ (l₁ hz) _, gm_pull (𝟙 _) (pullback.snd f f) z _ (l₂ hz) _,
      Category.id_comp, Category.id_comp]
    exact hC z i i' j j' hz.1.1 hz.2.1 hz.1.2 hz.2.2
  have hst : s t ∈ chart f L i j ⊓ chart f L i' j' := ⟨⟨hi, hj⟩, ⟨hi', hj'⟩⟩
  have e := congrArg (gm s t (chart f L i j ⊓ chart f L i' j')) hO
  rw [map_mul, map_mul, gm_res _ t _ hst, gm_res _ t _ hst, gm_res _ t _ hst, gm_res _ t _ hst,
    gm_pull s (pullback.fst f f) t _ (l₁ hst) _, gm_pull s (pullback.snd f f) t _ (l₂ hst) _] at e
  exact e

theorem defect_exists : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) (L : LB X) (φ : ∀ i j, Γ(pullback f f, chart f L i j)ˣ),
    L.IsLB → DescCompat f L φ → ∃ D : Γ(Triple f, ⊤)ˣ, Defect f L φ D := by
  intro X Y f L φ hL hC
  set a := pullback.fst (pullback.snd f f) (pullback.fst f f) with ha
  set b := pullback.snd (pullback.snd f f) (pullback.fst f f) with hb
  have hab : a ≫ pullback.snd f f = b ≫ pullback.fst f f := pullback.condition
  have hca : pr13 f ≫ pullback.fst f f = a ≫ pullback.fst f f := pullback.lift_fst _ _ _
  have hcb : pr13 f ≫ pullback.snd f f = b ≫ pullback.snd f f := pullback.lift_snd _ _ _
  have pab : ∀ x, pullback.snd f f (a x) = pullback.fst f f (b x) := fun x => by
    have := congrArg (fun h : Triple f ⟶ X => h x) hab
    simpa only [Scheme.Hom.comp_apply] using this
  have pca : ∀ x, pullback.fst f f (pr13 f x) = pullback.fst f f (a x) := fun x => by
    have := congrArg (fun h : Triple f ⟶ X => h x) hca
    simpa only [Scheme.Hom.comp_apply] using this
  have pcb : ∀ x, pullback.snd f f (pr13 f x) = pullback.snd f f (b x) := fun x => by
    have := congrArg (fun h : Triple f ⟶ X => h x) hcb
    simpa only [Scheme.Hom.comp_apply] using this

  have K : ∀ (T : Scheme.{0}) (s : T ⟶ Triple f) (t : T) (i j k i' j' k' : L.ι),
      pullback.fst f f (a (s t)) ∈ L.U i → pullback.fst f f (a (s t)) ∈ L.U i' →
      pullback.snd f f (a (s t)) ∈ L.U j → pullback.snd f f (a (s t)) ∈ L.U j' →
      pullback.snd f f (b (s t)) ∈ L.U k → pullback.snd f f (b (s t)) ∈ L.U k' →
      gm (s ≫ a) t _ (φ i j) * gm (s ≫ b) t _ (φ j k) * (gm (s ≫ pr13 f) t _ (φ i k))⁻¹ =
        gm (s ≫ a) t _ (φ i' j') * gm (s ≫ b) t _ (φ j' k') * (gm (s ≫ pr13 f) t _ (φ i' k'))⁻¹ := by
    intro T s t i j k i' j' k' hi hi' hj hj' hk hk'
    have hjb : pullback.fst f f (b (s t)) ∈ L.U j := pab (s t) ▸ hj
    have hjb' : pullback.fst f f (b (s t)) ∈ L.U j' := pab (s t) ▸ hj'
    have hic : pullback.fst f f (pr13 f (s t)) ∈ L.U i := (pca (s t)).symm ▸ hi
    have hic' : pullback.fst f f (pr13 f (s t)) ∈ L.U i' := (pca (s t)).symm ▸ hi'
    have hkc : pullback.snd f f (pr13 f (s t)) ∈ L.U k := (pcb (s t)).symm ▸ hk
    have hkc' : pullback.snd f f (pr13 f (s t)) ∈ L.U k' := (pcb (s t)).symm ▸ hk'
    have E1 := compat_gm f hC (s ≫ a) t i i' j j' hi hi' hj hj'
    have E2 := compat_gm f hC (s ≫ b) t j j' k k' hjb hjb' hk hk'
    have E3 := compat_gm f hC (s ≫ pr13 f) t i i' k k' hic hic' hkc hkc'
    have hc := gm_cocycle hL (s ≫ b ≫ pullback.fst f f) t (i := j') (j := j) (k := j') hjb' hjb hjb'
    rw [gm_self hL _ t hjb'] at hc
    simp only [Category.assoc] at E1 E2 E3
    rw [hca, hcb] at E3
    rw [hab] at E1
    rw [E1, E2, E3]
    generalize gm (s ≫ b ≫ pullback.fst f f) t _ (L.g j' j) = G2 at hc ⊢
    generalize gm (s ≫ b ≫ pullback.fst f f) t _ (L.g j j') = G3 at hc ⊢
    have : G3 = G2⁻¹ := eq_inv_of_mul_eq_one_right hc
    subst this
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  let V : L.ι × L.ι × L.ι → (Triple f).Opens := fun p =>
    a ⁻¹ᵁ chart f L p.1 p.2.1 ⊓ b ⁻¹ᵁ chart f L p.2.1 p.2.2 ⊓ pr13 f ⁻¹ᵁ chart f L p.1 p.2.2
  have la : ∀ p, V p ≤ a ⁻¹ᵁ chart f L p.1 p.2.1 := fun p => inf_le_left.trans inf_le_left
  have lb : ∀ p, V p ≤ b ⁻¹ᵁ chart f L p.2.1 p.2.2 := fun p => inf_le_left.trans inf_le_right
  have lc : ∀ p, V p ≤ pr13 f ⁻¹ᵁ chart f L p.1 p.2.2 := fun p => inf_le_right
  have memV : ∀ (x : Triple f) (i j k : L.ι), pullback.fst f f (a x) ∈ L.U i → pullback.snd f f (a x) ∈ L.U j →
      pullback.snd f f (b x) ∈ L.U k → x ∈ V (i, j, k) := fun x i j k hi hj hk =>
    ⟨⟨⟨hi, hj⟩, ⟨(show pullback.fst f f (b x) ∈ L.U j from pab x ▸ hj), hk⟩⟩,
      ⟨(show pullback.fst f f (pr13 f x) ∈ L.U i from (pca x).symm ▸ hi),
        (show pullback.snd f f (pr13 f x) ∈ L.U k from (pcb x).symm ▸ hk)⟩⟩
  let u : ∀ p, Γ(Triple f, V p)ˣ := fun p =>
    res (la p) (pullU a _ (φ p.1 p.2.1)) * res (lb p) (pullU b _ (φ p.2.1 p.2.2)) *
      (res (lc p) (pullU (pr13 f) _ (φ p.1 p.2.2)))⁻¹
  have hu : ∀ (T : Scheme.{0}) (s : T ⟶ Triple f) (t : T) (p : L.ι × L.ι × L.ι), s t ∈ V p →
      gm s t (V p) (u p) = gm (s ≫ a) t _ (φ p.1 p.2.1) * gm (s ≫ b) t _ (φ p.2.1 p.2.2) *
        (gm (s ≫ pr13 f) t _ (φ p.1 p.2.2))⁻¹ := by
    intro T s t p hp
    simp only [u, map_mul, map_inv]
    rw [gm_res _ t _ hp, gm_res _ t _ hp, gm_res _ t _ hp, gm_pull s a t _ (la p hp) _,
      gm_pull s b t _ (lb p hp) _, gm_pull s (pr13 f) t _ (lc p hp) _]
  obtain ⟨D, hD⟩ := glue_unit ⊤ V (fun _ => le_top) (fun x _ => by
      obtain ⟨i, hi⟩ := exists_chart hL (pullback.fst f f (a x))
      obtain ⟨j, hj⟩ := exists_chart hL (pullback.snd f f (a x))
      obtain ⟨k, hk⟩ := exists_chart hL (pullback.snd f f (b x))
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨(i, j, k), memV x i j k hi hj hk⟩) u (fun p p' x hx => by
      rw [hu _ (𝟙 _) x p hx.1, hu _ (𝟙 _) x p' hx.2]
      exact K _ (𝟙 _) x _ _ _ _ _ _ hx.1.1.1.1 hx.2.1.1.1 hx.1.1.1.2 hx.2.1.1.2 hx.1.1.2.2 hx.2.1.2.2)
  refine ⟨D, fun T r t i j k hi hj hk => ?_⟩
  have hm := memV (r t) i j k hi hj hk
  rw [← gm_res r t (fun _ _ => trivial : V (i, j, k) ≤ ⊤) hm D, hD (i, j, k), hu T r t (i, j, k) hm]
  exact inv_mul_cancel_right _ _

end GlobalTheory.DescDefect
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentCocycleDefectOfCompatibleStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open GlobalTheory.LBDescent GlobalTheory.DescNorm
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_descentCocycleDefect_of_compatible : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) (L : LB X) (φ : ∀ i j, Γ(pullback f f, chart f L i j)ˣ), L.IsLB → DescCompat f L φ → ∃ D : Γ(Triple f, ⊤)ˣ, Defect f L φ D := by
  first | exact @GlobalTheory.DescDefect.defect_exists | exact GlobalTheory.DescDefect.defect_exists | (intros; apply GlobalTheory.DescDefect.defect_exists <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMultipleBelowThreshold
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CoefBound

theorem cartierDivisor_mult_nsmul_eq_natCast_mul {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] (D : CartierDiv X)
    (n : ℕ) (z : X) : (n • D).mult z = n * D.mult z := by
  induction n with
  | zero =>
    have h := CartierDiv.mult_add (0 : CartierDiv X) 0 z
    rw [add_zero] at h
    rw [zero_nsmul]; push_cast; omega
  | succ n ih => rw [succ_nsmul, CartierDiv.mult_add, ih]; push_cast; ring

theorem coef_lt_of_large : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] [CompactSpace Y] (R Fd : CartierDiv Y) (m r a : ℕ), 0 < r → (∀ z, R.mult z < m) → ∃ b : ℕ, a ≤ b ∧ ∀ z, ((r * b) • R + m • Fd).mult z < (m * r * b : ℕ) := by
  intro Y _ _ _ R Fd m r a hr hR
  classical
  have hfin := Fd.finite_support_mult
  set S : ℕ := ∑ z ∈ hfin.toFinset, ((m : ℤ) * Fd.mult z).toNat with hS
  refine ⟨a + 1 + S, by omega, fun z => ?_⟩
  have hF : (m : ℤ) * Fd.mult z < ((a + 1 + S : ℕ) : ℤ) := by
    by_cases hz : Fd.mult z = 0
    · rw [hz]; push_cast; omega
    · have hmem : z ∈ hfin.toFinset := by simpa using hz
      have h1 : ((m : ℤ) * Fd.mult z).toNat ≤ S :=
        Finset.single_le_sum (f := fun z => ((m : ℤ) * Fd.mult z).toNat) (fun _ _ => Nat.zero_le _) hmem
      have h2 : (m : ℤ) * Fd.mult z ≤ (((m : ℤ) * Fd.mult z).toNat : ℤ) := Int.self_le_toNat _
      have h3 : ((((m : ℤ) * Fd.mult z).toNat : ℕ) : ℤ) ≤ (S : ℤ) := by exact_mod_cast h1
      push_cast; omega
  rw [CartierDiv.mult_add, cartierDivisor_mult_nsmul_eq_natCast_mul, cartierDivisor_mult_nsmul_eq_natCast_mul]
  set b : ℕ := a + 1 + S
  have hRz : R.mult z ≤ (m : ℤ) - 1 := by have := hR z; omega
  have hrb : (0 : ℤ) ≤ ((r * b : ℕ) : ℤ) := by positivity
  have key : ((r * b : ℕ) : ℤ) * R.mult z ≤ ((r * b : ℕ) : ℤ) * ((m : ℤ) - 1) :=
    mul_le_mul_of_nonneg_left hRz hrb
  have hb : ((b : ℕ) : ℤ) ≤ ((r * b : ℕ) : ℤ) := by
    have : b ≤ r * b := Nat.le_mul_of_pos_left b hr
    exact_mod_cast this
  have e : (((m * r * b : ℕ)) : ℤ) = ((r * b : ℕ) : ℤ) * (m : ℤ) := by push_cast; ring
  rw [e]
  nlinarith

end GlobalTheory.CoefBound
end
end
