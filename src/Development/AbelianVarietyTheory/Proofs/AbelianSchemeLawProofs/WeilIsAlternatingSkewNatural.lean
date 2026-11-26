module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoAppTopOfIsPullbackOfSurjective
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocGenOfTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionDivision
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CommPairing

theorem val_div_eq {X Y S₀ : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (p : Y ⟶ S₀) (hp : Function.Surjective p.appTop.hom)
    {u u' : LB.Gen (LB.LinComb M φ ε)} (hu : u.IsGen) (hu' : u'.IsGen)
    {Z : Scheme.{0}} (r r' : Z ⟶ Y) (hr : r ≫ p = r' ≫ p) (z : Z) (J) (hJ : Good M z J) :
    val u r z J * (val u' r z J)⁻¹ = val u r' z J * (val u' r' z J)⁻¹ := by
  obtain ⟨t, -, hv⟩ := exists_gen hM (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel])
    (LB.mulGen M _ _ _ _ u (LB.invGen M _ _ u')) (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.invGen_isGen _ _ _ _ hu'))
  have le : (⊤ : Y.Opens) ≤ LB.wchart M (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  obtain ⟨a, ha⟩ := hp (res le (t.s PEmpty.elim)).val
  have key : ∀ r : Z ⟶ Y, (val u r z J * (val u' r z J)⁻¹).val = gs (r ≫ p) z ⊤ a := by
    intro r
    rw [← val_inv, ← val_mul hJ, ← hv Z r z J hJ, val_of t r z J PEmpty.elim (fun k => k.elim)]
    exact (congrArg Units.val (gm_res r z le trivial _)).symm.trans ((gs_unit r z ⊤ trivial _).symm.trans
      ((congrArg (gs r z ⊤) ha.symm).trans (gs_pull r p z ⊤ trivial a)))
  apply Units.ext
  rw [key, key, hr]

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ}

theorem surj_fst (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (T : Over S) :
    Function.Surjective (fst T A).left.appTop.hom := by
  have hB : IsAbelianScheme ((Over.pullback T.hom).obj A) :=
    { comm := by have := hA.comm; infer_instance
      smooth := by have := hA.smooth; show Smooth (pullback.snd _ _); infer_instance
      proper := by have := hA.proper; show IsProper (pullback.snd _ _); infer_instance
      geomConnected := by have := hA.geomConnected; show GeometricallyConnected (pullback.snd _ _); infer_instance }
  have hb : Function.Surjective (pullback.snd A.hom T.hom).appTop.hom := (hG _ _ hB).2
  have e : (fst T A).left = (pullbackSymmetry T.hom A.hom).hom ≫ pullback.snd A.hom T.hom :=
    (pullbackSymmetry_hom_comp_snd _ _).symm
  rw [e, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp]
  have : IsIso (pullbackSymmetry T.hom A.hom).hom.appTop :=
    inferInstanceAs (IsIso ((pullbackSymmetry T.hom A.hom).hom.app ⊤))
  exact (ConcreteCategory.bijective_of_isIso (pullbackSymmetry T.hom A.hom).hom.appTop).2.comp hb

def tval {T : Over S} (θ : ThetaGrp A L k T) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z)
    (J : (Z ⟶ A.left) → L.ι) : (Z.presheaf.stalk z)ˣ :=
  val (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ r z J

theorem commIsOf_iff (hL : L.IsLB) {T : Over S} (θx θy : ThetaGrp A L k T) (c : Γ(T.left, ⊤)ˣ) :
    CommIsOf A L k θx θy c ↔ ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J →
      tval θx r z J * tval θy (r ≫ (translT A θx.pt).left) z J =
        tval θy r z J * tval θx (r ≫ (translT A θy.pt).left) z J * gm (r ≫ (fst T A).left) z ⊤ c := by
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J → ∀ θ θ' : ThetaGrp A L k T,
      val (LB.mulGen L _ _ _ _ θ.φ (LB.pullGen L _ _ θ'.φ (translT A θ.pt).left)) r z J =
        tval θ r z J * tval θ' (r ≫ (translT A θ.pt).left) z J := fun Z r z J hJ θ θ' =>
    (val_mul hJ _ _ _).trans (congrArg (tval θ r z J * ·) (val_pull hJ _ _ _))
  constructor
  · intro H Z r z J hJ
    exact (key Z r z J hJ θx θy).symm.trans ((val_corr hJ H r).trans ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) (key Z r z J hJ θy θx) (H1.val_constGen L c r z J))))
  · intro H
    refine corr_of_val hL fun y J hJ => ?_
    exact (key _ _ y J hJ θx θy).trans ((H _ _ y J hJ).trans ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) (key _ _ y J hJ θy θx) (H1.val_constGen L c _ y J))).symm)

theorem translT_fst {T : Over S} (x : T ⟶ A) : (translT A x).left ≫ (fst T A).left = (fst T A).left := by
  rw [← Over.comp_left, translT, lift_fst]

theorem tval_div (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {T : Over S}
    (θ θ' : ThetaGrp A L k T) (h : θ.pt = θ'.pt) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (x : T ⟶ A) (z : Z) (J)
    (hJ : Good L z J) :
    tval θ r z J * (tval θ' r z J)⁻¹ =
      tval θ (r ≫ (translT A x).left) z J * (tval θ' (r ≫ (translT A x).left) z J)⁻¹ := by
  obtain ⟨a, u, hu⟩ := θ
  obtain ⟨a', u', hu'⟩ := θ'
  obtain rfl : a = a' := h
  exact val_div_eq hL (fst T A).left (surj_fst hG hA T) hu hu' r _ (by rw [Category.assoc, translT_fst]) z J hJ

theorem commIsOf_change (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {T : Over S}
    {θx θy θx' θy' : ThetaGrp A L k T} {c : Γ(T.left, ⊤)ˣ} (hx : θx'.pt = θx.pt) (hy : θy'.pt = θy.pt)
    (H : CommIsOf A L k θx θy c) : CommIsOf A L k θx' θy' c := by
  rw [commIsOf_iff hL] at H ⊢
  intro Z r z J hJ
  have e₀ := H Z r z J hJ
  have e₁ := tval_div hG hA hL θx' θx hx r θy.pt z J hJ
  have e₂ := tval_div hG hA hL θy' θy hy r θx.pt z J hJ
  rw [hx, hy]
  apply Additive.ofMul.injective
  have a₀ := congrArg Additive.ofMul e₀
  have a₁ := congrArg Additive.ofMul e₁
  have a₂ := congrArg Additive.ofMul e₂
  simp only [ofMul_mul, ofMul_inv] at a₀ a₁ a₂ ⊢
  linear_combination (norm := abel) a₀ + a₁ - a₂

theorem commIsOf_self (hL : L.IsLB) {T : Over S} (θ : ThetaGrp A L k T) : CommIsOf A L k θ θ 1 := by
  rw [commIsOf_iff hL]
  intro Z r z J hJ
  rw [map_one, _root_.mul_one]

theorem commIsOf_symm (hL : L.IsLB) {T : Over S} {θx θy : ThetaGrp A L k T} {c : Γ(T.left, ⊤)ˣ}
    (H : CommIsOf A L k θx θy c) : CommIsOf A L k θy θx c⁻¹ := by
  rw [commIsOf_iff hL] at H ⊢
  intro Z r z J hJ
  rw [H Z r z J hJ, map_inv, mul_inv_cancel_right]

theorem whisker_translPt {T T' : Over S} (h : T' ⟶ T) (x : T ⟶ A) :
    h ▷ A ≫ translPt A x = translPt A (h ≫ x) := by
  show h ▷ A ≫ ((fst T A ≫ x) * snd T A) = (fst T' A ≫ h ≫ x) * snd T' A
  rw [MonObj.comp_mul, whiskerRight_snd, whiskerRight_fst_assoc]

theorem whisker_translT {T T' : Over S} (h : T' ⟶ T) (x : T ⟶ A) :
    translT A (h ≫ x) ≫ h ▷ A = h ▷ A ≫ translT A x := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [translT]
  · simp [translT, whisker_translPt]

theorem exists_pull (hL : L.IsLB) {T T' : Over S} (h : T' ⟶ T) (θ : ThetaGrp A L k T) :
    ∃ θ' : ThetaGrp A L k T', θ'.pt = h ≫ θ.pt ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (T' ⊗ A).left) (z : Z) (J),
      Good L z J → tval θ' r z J = tval θ (r ≫ (h ▷ A).left) z J := by
  have e₀ : (h ▷ A).left ≫ (snd T A).left = (snd T' A).left := by rw [← Over.comp_left, whiskerRight_snd]
  have e₁ : (h ▷ A).left ≫ (translPt A θ.pt).left = (translPt A (h ≫ θ.pt)).left := by
    rw [← Over.comp_left, whisker_translPt]
  obtain ⟨t, ht, hv⟩ := exists_gen hL (φ' := ![(snd T' A).left, (translPt A (h ≫ θ.pt)).left]) (ε' := ![k, -k])
    (fun U _ f => by
      refine Finset.prod_congr rfl fun i _ => ?_
      fin_cases i
      · exact congrArg (fun q => f q ^ k) e₀
      · exact congrArg (fun q => f q ^ (-k)) e₁)
    (LB.pullGen L ![(snd T A).left, (translPt A θ.pt).left] ![k, -k] θ.φ (h ▷ A).left)
    (DVR.pullGen_isGen _ _ _ _ θ.isGen _)
  exact ⟨⟨h ≫ θ.pt, t, ht⟩, rfl, fun Z r z J hJ => (hv Z r z J hJ).trans (val_pull hJ _ _ _)⟩

theorem exists_commIsOf_pull (hL : L.IsLB) {T T' : Over S} (h : T' ⟶ T) {θx θy : ThetaGrp A L k T}
    {c : Γ(T.left, ⊤)ˣ} (H : CommIsOf A L k θx θy c) :
    ∃ θx' θy' : ThetaGrp A L k T', θx'.pt = h ≫ θx.pt ∧ θy'.pt = h ≫ θy.pt ∧
      CommIsOf A L k θx' θy' (Units.map h.left.appTop.hom.toMonoidHom c) := by
  obtain ⟨θx', hx, vx⟩ := exists_pull hL h θx
  obtain ⟨θy', hy, vy⟩ := exists_pull hL h θy
  refine ⟨θx', θy', hx, hy, ?_⟩
  rw [commIsOf_iff hL] at H ⊢
  intro Z r z J hJ
  have t : ∀ x : T ⟶ A, (r ≫ (translT A (h ≫ x)).left) ≫ (h ▷ A).left =
      (r ≫ (h ▷ A).left) ≫ (translT A x).left := fun x => by
    rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, whisker_translT]
  have g : gm (r ≫ (fst T' A).left) z ⊤ (Units.map h.left.appTop.hom.toMonoidHom c) =
      gm ((r ≫ (h ▷ A).left) ≫ (fst T A).left) z ⊤ c := by
    refine (gm_pull (r ≫ (fst T' A).left) h.left z ⊤ trivial c).trans ?_
    rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, whiskerRight_fst]
  rw [vx _ _ z J hJ, vx _ _ z J hJ, vy _ _ z J hJ, vy _ _ z J hJ, hx, hy, t, t, g]
  exact H Z _ z J hJ

theorem weilIs_symm (hL : L.IsLB) {T : Over S} {x y : T ⟶ A} {c : Γ(T.left, ⊤)ˣ} (H : WeilIs A L k x y c) :
    WeilIs A L k y x c⁻¹ := by
  intro p
  obtain ⟨V, hp, ⟨θx, θy, hx, hy⟩, hc⟩ := H p
  refine ⟨V, hp, ⟨θy, θx, hy, hx⟩, fun θy θx hy hx => ?_⟩
  have e : unitRes V c⁻¹ = (unitRes V c)⁻¹ := map_inv _ _
  rw [e]
  exact commIsOf_symm hL (hc θx θy hx hy)

theorem weilIs_pull (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {T T' : Over S} (h : T' ⟶ T)
    {x y : T ⟶ A} {c : Γ(T.left, ⊤)ˣ} (H : WeilIs A L k x y c) :
    WeilIs A L k (h ≫ x) (h ≫ y) (Units.map h.left.appTop.hom.toMonoidHom c) := by
  intro p
  obtain ⟨V, hp, ⟨θx, θy, hx, hy⟩, hc⟩ := H (h.left p)
  have w : (h.left ∣_ V) ≫ V.ι = (h.left ⁻¹ᵁ V).ι ≫ h.left := morphismRestrict_ι _ _
  let h' : overRes (h.left ⁻¹ᵁ V) ⟶ overRes V := Over.homMk (h.left ∣_ V) (by
    show (h.left ∣_ V) ≫ V.ι ≫ T.hom = (h.left ⁻¹ᵁ V).ι ≫ T'.hom
    rw [← Category.assoc, w, Category.assoc, Over.w h])
  have w' : h' ≫ overResι V = overResι (h.left ⁻¹ᵁ V) ≫ h := Over.OverMorphism.ext w
  obtain ⟨θx', θy', hx', hy', H'⟩ := exists_commIsOf_pull hL h' (hc θx θy hx hy)
  rw [hx, ← Category.assoc, w', Category.assoc] at hx'
  rw [hy, ← Category.assoc, w', Category.assoc] at hy'
  have e : Units.map h'.left.appTop.hom.toMonoidHom (unitRes V c) =
      unitRes (h.left ⁻¹ᵁ V) (Units.map h.left.appTop.hom.toMonoidHom c) := by
    apply Units.ext
    have := congrArg (fun q => q.appTop.hom c.val) w
    simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at this
    exact this
  rw [e] at H'
  exact ⟨h.left ⁻¹ᵁ V, hp, ⟨θx', θy', hx', hy'⟩, fun a b ha hb =>
    commIsOf_change hG hA hL (ha.trans hx'.symm) (hb.trans hy'.symm) H'⟩

end GlobalTheory.CommPairing

namespace GlobalTheory

open CommPairing in
theorem weilIs_alternating_skew_natural : GlobalFnsSt → (∀ (S : Scheme.{0}) (P : PolAV S) (N : ℕ) (T : Over S) (x : T ⟶ P.A), x ^ N = 1 → ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧ ∃ θ : ThetaGrp P.A P.L N (overRes V), θ.pt = overResι V ≫ x) → ∀ (S : Scheme.{0}) (P : PolAV S) (k : ℕ) (T : Over S), (∀ x : T ⟶ P.A, x ^ k = 1 → WeilIs P.A P.L k x x 1) ∧ (∀ (x y : T ⟶ P.A) (c : Γ(T.left, ⊤)ˣ), WeilIs P.A P.L k x y c → WeilIs P.A P.L k y x c⁻¹) ∧ ∀ (T' : Over S) (h : T' ⟶ T) (x y : T ⟶ P.A) (c : Γ(T.left, ⊤)ˣ), WeilIs P.A P.L k x y c → WeilIs P.A P.L k (h ≫ x) (h ≫ y) (Units.map h.left.appTop.hom.toMonoidHom c) := by
  intro hG hlift S P k T
  refine ⟨fun x hx p => ?_, fun x y c H => weilIs_symm P.isLB H,
    fun T' h x y c H => weilIs_pull hG P.isAb P.isLB h H⟩
  obtain ⟨V, hp, θ, hθ⟩ := hlift S P k T x hx p
  refine ⟨V, hp, ⟨θ, θ, hθ, hθ⟩, fun a b ha hb => ?_⟩
  have e : unitRes V (1 : Γ(T.left, ⊤)ˣ) = 1 := map_one _
  rw [e]
  exact commIsOf_change hG P.isAb P.isLB (ha.trans hθ.symm) (hb.trans hθ.symm) (commIsOf_self P.isLB θ)

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineHomOfFlatQuotientOfAffineKernel
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

universe u

section Descent

set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] Over.cartesianMonoidalCategory in
set_option backward.isDefEq.respectTransparency.types false in
theorem _root_.GlobalTheory.quasiCompact_descendsAlong_fpqc :
    MorphismProperty.DescendsAlong (@QuasiCompact : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  refine ⟨fun {A X Y Z fst snd f g} h hf hfst => ?_⟩
  obtain ⟨⟨hs, -⟩, hqc⟩ := hf
  have hsnd : Surjective snd := MorphismProperty.of_isPullback h hs
  have : QuasiCompact f := hqc
  have : QuasiCompact fst := hfst
  show QuasiCompact g
  rw [quasiCompact_iff]
  intro U hU hc
  have h1 : IsCompact (fst ⁻¹' (f ⁻¹' U)) :=
    (quasiCompact_iff fst).1 ‹_› _ (hU.preimage f.continuous) ((quasiCompact_iff f).1 ‹_› U hU hc)
  have hcond : ∀ z, f (fst z) = g (snd z) := fun z => by
    rw [← Scheme.Hom.comp_apply, h.w, Scheme.Hom.comp_apply]
  have : g ⁻¹' U = snd '' (fst ⁻¹' (f ⁻¹' U)) := by
    ext y
    constructor
    · intro hy
      obtain ⟨z, rfl⟩ := hsnd.surj y
      exact ⟨z, by simpa [Set.mem_preimage, hcond] using hy, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      simpa [Set.mem_preimage, ← hcond] using hz
  rw [this]
  exact h1.image snd.continuous

attribute [local instance] Over.cartesianMonoidalCategory in
set_option backward.isDefEq.respectTransparency.types false in
theorem _root_.GlobalTheory.quasiSeparated_descendsAlong_fpqc :
    MorphismProperty.DescendsAlong (@QuasiSeparated : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  have : IsZariskiLocalAtTarget (@QuasiSeparated : MorphismProperty Scheme.{u}) :=
    @HasAffineProperty.instIsZariskiLocalAtTarget _ _
      instHasAffinePropertyQuasiSeparatedQuasiSeparatedSpaceCarrierCarrierCommRingCat
  refine IsZariskiLocalAtTarget.descendsAlong_inf_quasiCompact _ (@Surjective ⊓ @Flat) ?_ ?_
  · rintro X Y f ⟨hl, hs⟩
    exact ⟨hs, IsLocalIso.le_of_isZariskiLocalAtSource @Flat _ _ f hl⟩
  · intro R S Y φ g hφ hfst
    obtain ⟨hs, -⟩ := hφ
    have : QuasiSeparated (pullback.fst (Spec.map φ) g) := hfst
    have : QuasiSeparatedSpace ↥(Limits.pullback (Spec.map φ) g) :=
      quasiSeparatedSpace_of_quasiSeparated (pullback.fst (Spec.map φ) g)
    have hsnd : Surjective (pullback.snd (Spec.map φ) g) :=
      MorphismProperty.pullback_snd _ _ hs
    have : QuasiCompact (pullback.snd (Spec.map φ) g) :=
      MorphismProperty.pullback_snd _ _ (inferInstanceAs (QuasiCompact (Spec.map φ)))
    show QuasiSeparated g
    rw [quasiSeparated_iff_quasiSeparatedSpace]
    refine ⟨fun U V hU hUc hV hVc => ?_⟩
    set s := pullback.snd (Spec.map φ) g
    have hpre : ∀ W : Set Y, IsOpen W → IsCompact W → IsCompact (s ⁻¹' W) :=
      fun W hW hWc => (quasiCompact_iff s).1 ‹_› W hW hWc
    have : U ∩ V = s '' (s ⁻¹' U ∩ s ⁻¹' V) := by
      rw [← Set.preimage_inter, Set.image_preimage_eq _ hsnd.surj]
    rw [this]
    exact (QuasiSeparatedSpace.inter_isCompact _ _ (hU.preimage s.continuous) (hpre U hU hUc)
      (hV.preimage s.continuous) (hpre V hV hVc)).image s.continuous

attribute [local instance] Over.cartesianMonoidalCategory in
set_option backward.isDefEq.respectTransparency.types false in
theorem _root_.GlobalTheory.isAffine_of_isPullback_of_flat_surjective {X Y S T : Scheme.{u}} {f : T ⟶ S} {g : Y ⟶ X}
    {p : X ⟶ S} {q : Y ⟶ T} (H : IsPullback g q p f) [IsAffine S] [IsAffine T] [Flat f]
    [Surjective f] [IsAffine Y] : IsAffine X := by
  have hQf : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) f :=
    ⟨⟨‹Surjective f›, ‹Flat f›⟩, inferInstance⟩
  have : QuasiCompact p :=
    @MorphismProperty.of_isPullback_of_descendsAlong _ _ _ _ _ _ _ _ _ _ _ _
      _root_.GlobalTheory.quasiCompact_descendsAlong_fpqc H.flip hQf (inferInstanceAs (QuasiCompact q))
  have : QuasiSeparated p :=
    @MorphismProperty.of_isPullback_of_descendsAlong _ _ _ _ _ _ _ _ _ _ _ _
      _root_.GlobalTheory.quasiSeparated_descendsAlong_fpqc H.flip hQf (inferInstanceAs (QuasiSeparated q))
  have hSpec : IsPullback (Spec.map g.appTop) (Spec.map q.appTop) (Spec.map p.appTop)
      (Spec.map f.appTop) :=
    isPullback_SpecMap_of_isPushout _ _ _ _ (_root_.GlobalTheory.ProperFunctions.isPushout_appTop H)
  have hfsq : IsPullback (inv T.toSpecΓ) (Spec.map f.appTop) f (inv S.toSpecΓ) :=
    IsPullback.of_horiz_isIso ⟨by
      rw [IsIso.inv_comp_eq, ← Category.assoc, IsIso.eq_comp_inv, Scheme.toSpecΓ_naturality]⟩
  have hQ' : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u})
      (Spec.map g.appTop) :=
    MorphismProperty.of_isPullback hSpec.flip (MorphismProperty.of_isPullback hfsq hQf)
  have hiso : IsPullback T.toSpecΓ f (Spec.map f.appTop) S.toSpecΓ :=
    IsPullback.of_horiz_isIso ⟨(Scheme.toSpecΓ_naturality f).symm⟩
  have hbig : IsPullback (Y.toSpecΓ ≫ Spec.map q.appTop) g (Spec.map f.appTop)
      (X.toSpecΓ ≫ Spec.map p.appTop) := by
    rw [← Scheme.toSpecΓ_naturality, ← Scheme.toSpecΓ_naturality]
    exact H.flip.paste_horiz hiso
  have htop : IsPullback Y.toSpecΓ g (Spec.map g.appTop) X.toSpecΓ :=
    IsPullback.of_right hbig (Scheme.toSpecΓ_naturality g).symm hSpec.flip
  have : MorphismProperty.isomorphisms Scheme.{u} X.toSpecΓ :=
    MorphismProperty.of_isPullback_of_descendsAlong htop hQ'
      (MorphismProperty.isomorphisms.infer_property _)
  exact ⟨this⟩

attribute [local instance] Over.cartesianMonoidalCategory in
set_option backward.isDefEq.respectTransparency.types false in
theorem _root_.GlobalTheory.isAffineHom_descendsAlong_fpqc :
    MorphismProperty.DescendsAlong (@IsAffineHom : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  have : IsZariskiLocalAtTarget (@IsAffineHom : MorphismProperty Scheme.{u}) :=
    @HasAffineProperty.instIsZariskiLocalAtTarget _ _ instHasAffinePropertyIsAffineHomIsAffine
  refine IsZariskiLocalAtTarget.descendsAlong_inf_quasiCompact _ (@Surjective ⊓ @Flat) ?_ ?_
  · rintro X Y f ⟨hl, hs⟩
    exact ⟨hs, IsLocalIso.le_of_isZariskiLocalAtSource @Flat _ _ f hl⟩
  · intro R S Y φ g hφ hfst
    obtain ⟨hs, hfl⟩ := hφ
    have : Surjective (Spec.map φ) := hs
    have : Flat (Spec.map φ) := hfl
    have : IsAffineHom (pullback.fst (Spec.map φ) g) := hfst
    have : IsAffine (Limits.pullback (Spec.map φ) g) :=
      isAffine_of_isAffineHom (pullback.fst (Spec.map φ) g)
    have : IsAffine Y :=
      _root_.GlobalTheory.isAffine_of_isPullback_of_flat_surjective (IsPullback.of_hasPullback (Spec.map φ) g).flip
    show IsAffineHom g
    infer_instance

end Descent

attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.isAffineHom_of_flatQuotient_of_affine_kernel :
    ∀ (S : Scheme.{0}) (G B T : Over S) [GrpObj G] [GrpObj B] [GrpObj T] (q : G ⟶ B) (i : T ⟶ G),
      IsMonHom q → IsMonHom i → Flat q.left → Surjective q.left → QuasiCompact q.left →
      IsPullback i (toUnit _) q (η[B]) → IsAffineHom T.hom → IsAffineHom q.left := by
  intro S G B T _ _ _ q i hq hi hfl hs hqc hker hT
  have hiq : i ≫ q = 1 := by rw [hker.w, Hom.one_def]
  have hw : fst G T ≫ q = (fst G T * (snd G T ≫ i)) ≫ q := by
    rw [mul_comp, Category.assoc, hiq, comp_one, _root_.mul_one]
  have hpb : IsPullback (fst G T) (fst G T * (snd G T ≫ i)) q q := by
    refine ⟨⟨hw⟩, ⟨PullbackCone.IsLimit.mk hw
      (fun s => lift s.fst (hker.lift (s.fst⁻¹ * s.snd) (toUnit _) (by
        rw [mul_comp, GrpObj.inv_comp, s.condition, inv_mul_cancel, Hom.one_def])))
      (fun s => lift_fst _ _) (fun s => ?_) (fun s m h1 h2 => ?_)⟩⟩
    · rw [comp_mul, lift_fst, ← Category.assoc, lift_snd, hker.lift_fst, mul_inv_cancel_left]
    · refine hom_ext _ _ (by rw [h1, lift_fst]) ?_
      rw [lift_snd]
      refine hker.hom_ext ?_ (toUnit_unique _ _)
      rw [hker.lift_fst, ← h1, ← h2, comp_mul, Category.assoc, inv_mul_cancel_left]
  have hfst : IsAffineHom (fst G T).left := by
    show IsAffineHom (pullback.fst G.hom T.hom)
    exact MorphismProperty.of_isPullback (IsPullback.of_hasPullback G.hom T.hom).flip hT
  exact @MorphismProperty.of_isPullback_of_descendsAlong _ _ _ _ _ _ _ _ _ _ _ _
    _root_.GlobalTheory.isAffineHom_descendsAlong_fpqc (hpb.map (Over.forget S)) ⟨⟨hs, hfl⟩, hqc⟩ hfst

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSecValueIsUnit
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic ReciprocityTheory.ChartRestriction.G.H1.SquareUnits

attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.NoBasePoint

theorem exists_section_mem {K : Type} [Field K] [IsAlgClosed K] {Y : Scheme.{0}}
    (f : Y ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f] (W : Y.Opens) (hW : (W : Set Y).Nonempty) :
    ∃ σ : Spec (CommRingCat.of K) ⟶ Y, σ ≫ f = 𝟙 _ ∧ ∀ p, σ p ∈ W := by
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨c, hcW, hc⟩ := nonempty_inter_closedPoints hW W.isOpen.isLocallyClosed
  exact ⟨pointOfClosedPoint f c hc, pointOfClosedPoint_comp f c hc, fun p =>
    (congrArg (· ∈ W) (pointOfClosedPoint_apply f c hc p)).mpr hcW⟩

section
variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem translPt_eq {T : Over S} (a : T ⟶ A) : translPt A a = (fst T A ≫ a) * snd T A := rfl

theorem ptSecT_translT {T : Over S} (a x : T ⟶ A) : ptSecT A x ≫ translT A a = ptSecT A (a * x) := by
  simp [ptSecT, translT, translPt_eq, comp_lift, MonObj.comp_mul]

theorem exists_two_points {K : Type} [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S)
    [LocallyOfFiniteType A.hom] [IsIntegral (Over.mk t ⊗ A).left] (D : (Over.mk t ⊗ A).left.Opens)
    (hD : (D : Set (Over.mk t ⊗ A).left).Nonempty) (x c : Over.mk t ⟶ A) :
    ∃ a : Over.mk t ⟶ A, (∀ p, (ptSecT A (a * x)).left p ∈ D) ∧ ∀ p, (ptSecT A (a⁻¹ * c)).left p ∈ D := by
  let T := Over.mk t
  let u₁ : T ⊗ A ⟶ T ⊗ A := lift (fst T A) (snd T A * (fst T A ≫ x))
  let w₁ : T ⊗ A ⟶ T ⊗ A := lift (fst T A) (snd T A * (fst T A ≫ x)⁻¹)
  let u₂ : T ⊗ A ⟶ T ⊗ A := lift (fst T A) ((snd T A)⁻¹ * (fst T A ≫ c))
  let w₂ : T ⊗ A ⟶ T ⊗ A := lift (fst T A) ((fst T A ≫ c) * (snd T A)⁻¹)
  have e₁ : w₁ ≫ u₁ = 𝟙 _ := by
    ext <;> simp [u₁, w₁, MonObj.comp_mul]
  have e₂ : w₂ ≫ u₂ = 𝟙 _ := by
    ext <;> simp [u₂, w₂, MonObj.comp_mul, GrpObj.comp_inv]
  have ne : ∀ u w : T ⊗ A ⟶ T ⊗ A, w ≫ u = 𝟙 _ → ((u.left ⁻¹ᵁ D : (T ⊗ A).left.Opens) : Set (T ⊗ A).left).Nonempty := by
    intro u w e
    obtain ⟨d, hd⟩ := hD
    refine ⟨w.left d, ?_⟩
    show u.left (w.left d) ∈ D
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, e]
    exact hd
  have hne : ((u₁.left ⁻¹ᵁ D ⊓ u₂.left ⁻¹ᵁ D : (T ⊗ A).left.Opens) : Set (T ⊗ A).left).Nonempty :=
    nonempty_preirreducible_inter (u₁.left ⁻¹ᵁ D).isOpen (u₂.left ⁻¹ᵁ D).isOpen (ne _ _ e₁) (ne _ _ e₂)
  have : LocallyOfFiniteType (X := (T ⊗ A).left) (Y := Spec (CommRingCat.of K)) (fst T A).left :=
    inferInstanceAs (LocallyOfFiniteType (pullback.fst t A.hom))
  obtain ⟨σ, hσ, hm⟩ := exists_section_mem (Y := (T ⊗ A).left) (fst T A).left _ hne
  let σ' : T ⟶ T ⊗ A := Over.homMk σ (by
    rw [← Over.w (fst T A), ← Category.assoc]
    exact (congrArg (· ≫ T.hom) hσ).trans (Category.id_comp _))
  have hf : σ' ≫ fst T A = 𝟙 T := Over.OverMorphism.ext hσ
  have f₁ : σ' ≫ u₁ = ptSecT A ((σ' ≫ snd T A) * x) := by
    simp [u₁, ptSecT, comp_lift, MonObj.comp_mul, hf, reassoc_of% hf]
  have f₂ : σ' ≫ u₂ = ptSecT A ((σ' ≫ snd T A)⁻¹ * c) := by
    simp [u₂, ptSecT, comp_lift, MonObj.comp_mul, GrpObj.comp_inv, hf, reassoc_of% hf]
  refine ⟨σ' ≫ snd T A, fun p => ?_, fun p => ?_⟩
  · rw [← f₁]; exact (hm p).1
  · rw [← f₂]; exact (hm p).2

variable {L : LB A.left}

theorem unitAt_of_local (hL : L.IsLB) {T : Over S} [Subsingleton T.left] {I : Type} [Fintype I]
    (φ : I → ((T ⊗ A).left ⟶ A.left)) (ε : I → ℤ) (p : T.left) (V : T.left.Opens) (hp : p ∈ V)
    (c : LB.Gen ((LB.LinComb L φ ε).pull ((fst T A).left ⁻¹ᵁ V).ι)) (hc : c.IsGen) (y : (T ⊗ A).left) :
    UnitAt L φ ε y := by
  have hV : V = ⊤ := eq_top_iff.2 fun q _ => by rw [Subsingleton.elim q p]; exact hp
  subst hV
  obtain ⟨s, hs⟩ := exists_sec_of_pullGen (Z := (T ⊗ A).left) ((fst T A).left ⁻¹ᵁ ⊤).ι c hc
  let e := IsOpenImmersion.lift ((fst T A).left ⁻¹ᵁ ⊤).ι (𝟙 _)
    (by rintro _ ⟨q, rfl⟩; rw [Scheme.Opens.range_ι]; trivial)
  have he : e ≫ ((fst T A).left ⁻¹ᵁ ⊤).ι = 𝟙 _ := IsOpenImmersion.lift_fac _ _ _
  refine UnitAt.congr hL ?_ ⟨pullSec s e, fun J hJ => ?_⟩
  · refine formEq_of_add fun U _ hh => ?_
    simp only [← Category.assoc, he, Category.id_comp]
  · rw [sval_pullSec s e (𝟙 _) y hJ]
    exact hs _ y J hJ

theorem unitAt_transl (hL : L.IsLB) {T : Over S} (θ : LB.Sec (LPow A L 1 T)) (k : (LPow A L 1 T).ι)
    (a : T ⟶ A) (y : (T ⊗ A).left) (hy : (translT A a).left y ∈ (T ⊗ A).left.basicOpen (θ.f k)) :
    UnitAt L (K := Fin 1) (fun _ => (translPt A a).left) (fun _ => 1) y := by
  refine UnitAt.congr hL ?_ ⟨pullSec θ (translT A a).left, fun J hJ => ?_⟩
  · refine formEq_of_add fun U _ hh => ?_
    simp only [← Over.comp_left, translT, lift_snd]
  · rw [sval_pullSec θ _ (𝟙 _) y hJ]
    exact isUnit_sval θ _ y hJ k hy

theorem exists_value_one (hL : L.IsLB) {T : Over S} [Subsingleton T.left] (n : ℤ) (x : T ⟶ A) (p : T.left)
    (h : UnitAt L (K := Fin 1) (fun _ => (snd T A).left) (fun _ => n) ((ptSecT A x).left p)) :
    ∃ (s : LB.Sec (LPow A L n T))
      (τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => n))),
      τ.IsGen ∧ IsValueAt A L n s x τ 1 := by
  obtain ⟨s, hs⟩ := h
  choose I hI using fun χ : (T ⊗ A).left ⟶ A.left => exists_chart hL (χ ((ptSecT A x).left p))
  have hm := Good.mem hI (fun _ : Fin 1 => (snd T A).left) (𝟙 _)
  have hb : (ptSecT A x).left p ∈ (T ⊗ A).left.basicOpen (s.f (fun _ => I (𝟙 _ ≫ (snd T A).left))) :=
    ((T ⊗ A).left.mem_basicOpen _ _ hm).2 ((congrArg IsUnit (gs_eq (𝟙 _) _ _ hm _)).mp (hs I hI))
  let s' := GlobalTheory.EvVal.pullSec L (fun _ : Fin 1 => (snd T A).left) (fun _ => n) (ptSecT A x).left
    (fun _ => x.left) (fun _ => by rw [← Over.comp_left, ptSecT, lift_snd]) (val_le A L x) s
  have hu : ∀ j, IsUnit (s'.f j) := fun j => T.left.toRingedSpace.isUnit_of_isUnit_germ _ _ fun q hq => by
    obtain rfl : q = p := Subsingleton.elim _ _
    choose J hJ using fun χ : T.left ⟶ A.left => exists_chart hL (χ q)
    have u := isUnit_sval s (ptSecT A x).left q hJ _ hb
    have e := sec_trans s (ptSecT A x).left q (val_le A L x j hq) (Good.mem hJ _ (ptSecT A x).left)
    have e' : gs (𝟙 T.left) q (LB.wchart L (fun _ : Fin 1 => x.left) j) (s'.f j) =
        gs (𝟙 T.left ≫ (ptSecT A x).left) q (LB.wchart L (fun _ : Fin 1 => (snd T A).left) j) (s.f j) :=
      (gs_res (𝟙 T.left) q (val_le A L x j) hq _).trans
        (gs_pull (𝟙 T.left) (ptSecT A x).left q (LB.wchart L (fun _ : Fin 1 => (snd T A).left) j)
          (val_le A L x j hq) (s.f j))
    rw [Category.id_comp] at e'
    exact (congrArg IsUnit ((gs_eq (𝟙 T.left) q (LB.wchart L (fun _ : Fin 1 => x.left) j) hq _).symm.trans
      (e'.trans e))).mpr ((Units.isUnit _).mul u)
  refine ⟨s, ⟨fun j => (hu j).unit⟩, fun i j => Units.ext (s'.compat i j), fun j => ?_⟩
  rw [map_one, _root_.one_mul]
  rfl

end

theorem exists_sec_value_isUnit :
    (∀ (X S : Scheme.{0}) (f : X ⟶ S), Smooth f → GeometricallyConnected f → GeometricallyIntegral f) → (∀ (S : Scheme.{0}) (P : PolAV S) (T : Over S) (x y : T ⟶ P.A) (p : T.left), ∃ V : T.left.Opens, p ∈ V ∧ ∃ c : LB.Gen ((LB.LinComb P.L (K := Fin 4) ![(translPt P.A (x * y)).left, (snd T P.A).left, (translPt P.A x).left, (translPt P.A y).left] ![1, 1, -1, -1]).pull ((fst T P.A).left ⁻¹ᵁ V).ι), c.IsGen) → (∀ (S : Scheme.{0}) (P : PolAV S) (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S) (n : ℕ), 1 ≤ n → Module.finrank Γ((Over.mk t).left, ⊤) (SecM P.A P.L n (Over.mk t)) = n ^ P.g) → (∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (n : ℕ), 1 ≤ n → IsFinite (mulA P.A n).left ∧ Flat (mulA P.A n).left ∧ Surjective (mulA P.A n).left ∧ (IsUnit (n : Γ(S, ⊤)) → Etale (mulA P.A n).left)) → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S) (n : ℕ), 2 ≤ n → ∀ x : Over.mk t ⟶ P.A, ∃ (s : LB.Sec (LPow P.A P.L n (Over.mk t))) (τ : LB.Gen (LB.LinComb P.L (Y := (Over.mk t).left) (K := Fin 1) (fun _ => x.left) (fun _ => (n : ℤ)))) (v : Γ((Over.mk t).left, ⊤)), τ.IsGen ∧ IsValueAt P.A P.L n s x τ v ∧ IsUnit v := by
  intro hGI hsq hH0 _ S _ P K _ _ t n hn x
  have := P.isAb.smooth
  have := P.isAb.geomConnected
  have : GeometricallyIntegral P.A.hom := hGI _ _ _ inferInstance inferInstance
  have : IsIntegral (Over.mk t ⊗ P.A).left :=
    GeometricallyIntegral.geometrically_isIntegral t _ _ (IsPullback.of_hasPullback t P.A.hom).flip
  have : Subsingleton (Over.mk t).left := ⟨spec_pt_eq (k := K)⟩
  have : Nontrivial Γ((Over.mk t).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  have h1 := hH0 S P K t 1 le_rfl
  rw [one_pow] at h1
  have : Nontrivial (SecM P.A P.L (1 : ℕ) (Over.mk t)) := Module.nontrivial_of_finrank_pos (h1 ▸ Nat.one_pos)
  obtain ⟨f, hf⟩ := exists_ne (0 : SecM P.A P.L (1 : ℕ) (Over.mk t))
  let θ : LB.Sec (LPow P.A P.L 1 (Over.mk t)) := SecM.toSec P.A f
  obtain ⟨k, hk⟩ : ∃ k, θ.f k ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (Subtype.ext (funext h))
  have hD : (((Over.mk t ⊗ P.A).left.basicOpen (θ.f k) : (Over.mk t ⊗ P.A).left.Opens) :
      Set (Over.mk t ⊗ P.A).left).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h
    exact hk ((basicOpen_eq_bot_iff _).1 (SetLike.coe_injective h))
  let p : (Over.mk t).left := IsLocalRing.closedPoint K
  let y := (ptSecT P.A x).left p
  have good : ∀ a : Over.mk t ⟶ P.A, (ptSecT P.A (a * x)).left p ∈ (Over.mk t ⊗ P.A).left.basicOpen (θ.f k) →
      UnitAt P.L (K := Fin 1) (fun _ => (translPt P.A a).left) (fun _ => 1) y := fun a ha =>
    unitAt_transl P.isLB θ k a y (by
      rw [← ptSecT_translT] at ha
      exact ha)
  have step : ∀ (m : ℤ) (b a : Over.mk t ⟶ P.A),
      UnitAt P.L ![(translPt P.A b).left, (snd (Over.mk t) P.A).left] ![1, m] y →
      UnitAt P.L (K := Fin 1) (fun _ => (translPt P.A a).left) (fun _ => 1) y →
      UnitAt P.L ![(translPt P.A (b * a)).left, (snd (Over.mk t) P.A).left] ![1, m + 1] y := by
    intro m b a hb ha
    obtain ⟨V, hV, c, hc⟩ := hsq S P (Over.mk t) b a p
    refine UnitAt.congr P.isLB (formEq_of_add fun U _ hh => ?_)
      ((hb.mul ha).mul (unitAt_of_local P.isLB _ _ p V hV c hc y))
    simp [Fin.sum_univ_succ]
    module
  have main : ∀ (m : ℕ) (b : Over.mk t ⟶ P.A),
      UnitAt P.L ![(translPt P.A b).left, (snd (Over.mk t) P.A).left] ![1, (m : ℤ) + 1] y := by
    intro m
    induction m with
    | zero =>
      intro b
      obtain ⟨a, h₁, h₂⟩ := exists_two_points t _ hD x (b * x)
      have := step 0 a (a⁻¹ * b) (UnitAt.congr P.isLB (formEq_of_add fun U _ hh => by simp) (good a (h₁ p)))
        (good _ (by rw [_root_.mul_assoc]; exact h₂ p))
      rwa [mul_inv_cancel_left] at this
    | succ m ih =>
      intro b
      obtain ⟨a, h₁, -⟩ := exists_two_points t _ hD x x
      have := step _ _ a (ih (b * a⁻¹)) (good a (h₁ p))
      rwa [inv_mul_cancel_right] at this
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have e1 : translPt P.A (1 : Over.mk t ⟶ P.A) = snd _ _ := by
    rw [translPt_eq, MonObj.comp_one, _root_.one_mul]
  obtain ⟨s, τ, hτ, hv⟩ := exists_value_one P.isLB ((m + 2 : ℕ) : ℤ) x p
    (UnitAt.congr P.isLB (formEq_of_add fun U _ hh => by
      simp [Fin.sum_univ_succ, e1]
      module) (main m 1))
  exact ⟨s, τ, 1, hτ, hv, isUnit_one⟩

end GlobalTheory.NoBasePoint
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TwistedPowTranslate
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwistTranslate

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic ReciprocityTheory.ChartRestriction.G.H1.SquareUnits

section Gen

variable {X Y : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

theorem exists_gen_of_sec (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε))
    (hs : ∀ (y : Y) J, Good L y J → IsUnit (sval s (𝟙 Y) y J)) :
    ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen := by
  have hu : ∀ j, IsUnit (s.f j) := fun j => Y.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
    obtain ⟨J, hJ, e⟩ := sval_trans hL s y j hy
    exact (congrArg IsUnit ((gs_eq (𝟙 Y) y (LB.wchart L φ j) hy _).symm.trans e)).mpr
      ((Units.isUnit _).mul (hs y J hJ))
  exact ⟨⟨fun j => (hu j).unit⟩, fun i j => Units.ext (s.compat i j)⟩

theorem gen_congr (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    (hf : FormEq φ ε φ' ε') (h : ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen) :
    ∃ t : LB.Gen (LB.LinComb L φ' ε'), t.IsGen := by
  obtain ⟨t, ht⟩ := h
  obtain ⟨t', ht', -⟩ := exists_gen hL hf t ht
  exact ⟨t', ht'⟩

theorem gen_mul {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    (h : ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen) (h' : ∃ t : LB.Gen (LB.LinComb L φ' ε'), t.IsGen) :
    ∃ t : LB.Gen (LB.LinComb L (Sum.elim φ φ') (Sum.elim ε ε')), t.IsGen := by
  obtain ⟨t, ht⟩ := h
  obtain ⟨t', ht'⟩ := h'
  exact ⟨_, DVR.mulGen_isGen L φ ε φ' ε' t t' ht ht'⟩

theorem gen_of_pull_top (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} (W : Y.Opens) (hW : ∀ y, y ∈ W)
    (c : LB.Gen ((LB.LinComb L φ ε).pull W.ι)) (hc : c.IsGen) :
    ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen := by
  obtain ⟨s, hs⟩ := exists_sec_of_pullGen (Z := Y) W.ι c hc
  let e := IsOpenImmersion.lift W.ι (𝟙 Y)
    (by rintro _ ⟨q, rfl⟩; rw [Scheme.Opens.range_ι]; exact hW _)
  have he : e ≫ W.ι = 𝟙 _ := IsOpenImmersion.lift_fac _ _ _
  refine gen_congr hL ?_ (exists_gen_of_sec hL (pullSec s e) fun y J hJ => ?_)
  · refine formEq_of_add fun U _ hh => ?_
    simp only [← Category.assoc, he, Category.id_comp]
  · rw [sval_pullSec s e (𝟙 _) y hJ]
    exact hs _ y J hJ

end Gen

variable {S : Scheme.{0}} (P : PolAV S) {K : Type} [Field K] (t : Spec (CommRingCat.of K) ⟶ S)

theorem gen_square (hsq : ∀ (x y : Over.mk t ⟶ P.A) (p : (Over.mk t).left), ∃ V : (Over.mk t).left.Opens, p ∈ V ∧
      ∃ c : LB.Gen ((LB.LinComb P.L (K := Fin 4) ![(translPt P.A (x * y)).left, (snd (Over.mk t) P.A).left,
        (translPt P.A x).left, (translPt P.A y).left] ![1, 1, -1, -1]).pull
          ((fst (Over.mk t) P.A).left ⁻¹ᵁ V).ι), c.IsGen)
    (x y : Over.mk t ⟶ P.A) :
    ∃ w : LB.Gen (LB.LinComb P.L (K := Fin 4) ![(translPt P.A (x * y)).left, (snd (Over.mk t) P.A).left,
      (translPt P.A x).left, (translPt P.A y).left] ![1, 1, -1, -1]), w.IsGen := by
  obtain ⟨V, hpV, c, hc⟩ := hsq x y (IsLocalRing.closedPoint K)
  refine gen_of_pull_top P.isLB _ (fun z => ?_) c hc
  show (fst (Over.mk t) P.A).left z ∈ V
  rw [spec_pt_eq ((fst (Over.mk t) P.A).left z) (IsLocalRing.closedPoint K)]
  exact hpV

theorem gen_iter (hsq : ∀ (x y : Over.mk t ⟶ P.A) (p : (Over.mk t).left), ∃ V : (Over.mk t).left.Opens, p ∈ V ∧
      ∃ c : LB.Gen ((LB.LinComb P.L (K := Fin 4) ![(translPt P.A (x * y)).left, (snd (Over.mk t) P.A).left,
        (translPt P.A x).left, (translPt P.A y).left] ![1, 1, -1, -1]).pull
          ((fst (Over.mk t) P.A).left ⁻¹ᵁ V).ι), c.IsGen)
    (d : Over.mk t ⟶ P.A) :
    ∀ n : ℕ, ∃ w : LB.Gen (LB.LinComb P.L (K := Fin 3) ![(snd (Over.mk t) P.A).left,
      (translPt P.A (d ^ (n + 1))).left, (translPt P.A d).left] ![(n : ℤ), 1, -((n : ℤ) + 1)]), w.IsGen
  | 0 => by
    refine gen_congr P.isLB (formEq_of_add fun U _ hh => ?_)
      (gen_mul (gen_square P t hsq d d) ⟨_, DVR.invGen_isGen _ _ _ _ (gen_square P t hsq d d).choose_spec⟩)
    simp [Fin.sum_univ_succ]
    module
  | n + 1 => by
    refine gen_congr P.isLB (formEq_of_add fun U _ hh => ?_)
      (gen_mul (gen_iter hsq d n) (gen_square P t hsq (d ^ (n + 1)) d))
    have e : d ^ (n + 1) * d = d ^ (n + 1 + 1) := by rw [← pow_succ]
    simp [Fin.sum_univ_succ, e]
    module

theorem exists_root [IsAlgClosed K] (r : ℕ) [IsFinite (mulA P.A r).left] [Surjective (mulA P.A r).left]
    (c : Over.mk t ⟶ P.A) : ∃ d : Over.mk t ⟶ P.A, d ^ r = c := by
  obtain ⟨u, hu⟩ := H1.SectionDivision.exists_section (k := K) (pullback.snd (mulA P.A r).left c.left)
  have hb' : (u ≫ pullback.fst (mulA P.A r).left c.left) ≫ (mulA P.A r).left = c.left := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hu]; exact Category.id_comp _
  have hw : (u ≫ pullback.fst (mulA P.A r).left c.left) ≫ P.A.hom = (Over.mk t).hom := by
    rw [← Over.w (mulA P.A r), ← Category.assoc, hb']; exact Over.w c
  refine ⟨Over.homMk _ hw, ?_⟩
  have e : ∀ b : Over.mk t ⟶ P.A, b ^ r = b ≫ mulA P.A r := fun b =>
    (congrArg (· ^ r) (Category.comp_id b).symm).trans (MonObj.comp_pow (𝟙 P.A) r b).symm
  rw [e]
  exact Over.OverMorphism.ext hb'

end GlobalTheory.TwistTranslate

namespace GlobalTheory

theorem twisted_pow_translate :
    (∀ (S : Scheme.{0}) (P : PolAV S) (T : Over S) (x y : T ⟶ P.A) (p : T.left), ∃ V : T.left.Opens, p ∈ V ∧ ∃ c : LB.Gen ((LB.LinComb P.L (K := Fin 4) ![(translPt P.A (x * y)).left, (snd T P.A).left, (translPt P.A x).left, (translPt P.A y).left] ![1, 1, -1, -1]).pull ((fst T P.A).left ⁻¹ᵁ V).ι), c.IsGen) → (∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (n : ℕ), 1 ≤ n → IsFinite (mulA P.A n).left ∧ Flat (mulA P.A n).left ∧ Surjective (mulA P.A n).left ∧ (IsUnit (n : Γ(S, ⊤)) → Etale (mulA P.A n).left)) → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S) (q : ℕ), 1 ≤ q → ∀ c : Over.mk t ⟶ P.A, ∃ d : Over.mk t ⟶ P.A, d ^ q = c ∧ ∃ w : LB.Gen (LB.LinComb P.L (K := Fin 3) ![(snd (Over.mk t) P.A).left, (translPt P.A c).left, (translPt P.A d).left] ![(q : ℤ) - 1, 1, -(q : ℤ)]), w.IsGen := by
  intro hsq hmul S _ P K _ _ t q hq c
  obtain ⟨hfin, -, hsurj, -⟩ := hmul S P q hq
  obtain ⟨d, rfl⟩ := TwistTranslate.exists_root P t q c
  refine ⟨d, rfl, ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, by omega⟩
  refine TwistTranslate.gen_congr P.isLB (H1.SquareUnits.formEq_of_add fun U _ hh => ?_)
    (TwistTranslate.gen_iter P t (hsq S P _) d n)
  simp [Fin.sum_univ_succ]

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CorrOfGenericOfIsSeparated
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory

universe u

theorem corr_of_corr_pullGen {X Y Z : Scheme.{u}} (L : LB X) {I I' : Type u} [Fintype I] [Fintype I']
    (φ : I → (Y ⟶ X)) (ε : I → ℤ) (φ' : I' → (Y ⟶ X)) (ε' : I' → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε')) (h : Z ⟶ Y)
    (hinj : ∀ U, Function.Injective (h.app U).hom) (hc : ∀ a b : Y ⟶ X, h ≫ a = h ≫ b → a = b)
    (H : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t h) (LB.pullGen L _ _ t' h)) :
    LB.Gen.Corr L _ _ _ _ t t' := by
  intro j j' c₁ c₂ c₃
  have e := H j j' (fun a b e => c₁ a b (hc _ _ e)) (fun a b e => c₂ a b (hc _ _ e))
    (fun a b e => c₃ a b (hc _ _ e))
  have le : h ⁻¹ᵁ (LB.wchart L φ j ⊓ LB.wchart L φ' j') ≤
      LB.wchart L (fun k => h ≫ φ k) j ⊓ LB.wchart L (fun k => h ≫ φ' k) j' := fun _ hy =>
    ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.1 k, Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.2 k⟩
  have e' := congrArg (res le) e
  change res le (res _ (LB.ts (LB.pullGen L _ _ t h) j)) = res le (res _ (LB.ts (LB.pullGen L _ _ t' h) j')) at e'
  rw [LB.ts_pullGen, LB.ts_pullGen] at e'
  simp only [LB.res_res] at e'
  refine Units.map_injective (f := (h.app (LB.wchart L φ j ⊓ LB.wchart L φ' j')).hom.toMonoidHom)
    (hinj _) ?_
  exact (LB.pullU_res h _ _).trans (e'.trans (LB.pullU_res h _ _).symm)

theorem corr_of_generic_of_isSeparated
    (V : Type u) [CommRing V] (K : Type u) [Field K] [Algebra V K] [IsFractionRing V K]
    (G : Over (Spec (CommRingCat.of V))) [IsSeparated G.hom]
    (T : Over (Spec (CommRingCat.of V))) [Flat T.hom]
    (L : LB G.left) {I I' : Type u} [Fintype I] [Fintype I']
    (φ : I → (T.left ⟶ G.left)) (ε : I → ℤ) (φ' : I' → (T.left ⟶ G.left)) (ε' : I' → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε'))
    (H : LB.Gen.Corr L _ _ _ _
      (LB.pullGen L _ _ t (pullback.fst T.hom (Spec.map (CommRingCat.ofHom (algebraMap V K)))))
      (LB.pullGen L _ _ t' (pullback.fst T.hom (Spec.map (CommRingCat.ofHom (algebraMap V K)))))) :
    LB.Gen.Corr L _ _ _ _ t t' := by
  have := (ExtUnique.spec_fractionRing V K).2
  have : IsSchemeTheoreticallyDominant
      (pullback.fst T.hom (Spec.map (CommRingCat.ofHom (algebraMap V K)))) :=
    .of_isPullback (IsPullback.of_hasPullback _ _).flip
  refine corr_of_corr_pullGen L φ ε φ' ε' t t' _ (fun U => Scheme.Hom.app_injective _ U)
    (fun a b e => ?_) H
  exact ExtUnique.hom_ext_of_dominant (G.hom ≫ terminal.from _) (terminal.hom_ext _ _) _ e

namespace DoubledPoint

variable {X : Scheme.{0}} (U : X.Opens)

end DoubledPoint

end GlobalTheory
end
