module

public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.DualAbelianSchemes.TrivLocusFlat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationDataTranslateOrderTwoIsTwist

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwoTorsionTwistOfSamePolarisedData
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslateOfMumfordBundleMatch
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslateOfMumfordBundleMatch
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumCmp

open GlobalTheory.CechPic GlobalTheory.AbDual

theorem pull_inv_cls {R : Type} [CommRing R] [IsLocalRing R] (P : PolAV (Sp R)) :
    pull (GrpObj.inv : P.A ⟶ P.A).left (cls P.L P.isLB) = cls P.L P.isLB := by
  obtain ⟨U, hU, t, ht⟩ := P.sym (IsLocalRing.closedPoint R)
  obtain rfl : U = ⊤ := DVR.eq_top_of_closedPoint_mem U hU
  have h := (cls_eq_zero_iff (LB.isLB_linComb P.isLB _ _)).2 ⟨t, ht⟩
  rw [cls_linComb P.isLB, Fin.sum_univ_two] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, one_smul, neg_smul, pull_comp] at h
  obtain ⟨m, hm⟩ : ∃ m : P.A.left ⟶ (P.A.hom ⁻¹ᵁ ⊤).toScheme, m ≫ (P.A.hom ⁻¹ᵁ ⊤).ι = 𝟙 _ :=
    ⟨P.A.left.topIso.inv, P.A.left.topIso.inv_hom_id⟩
  have h' := congrArg (pull m) h
  rw [map_add (f := _), map_neg, map_zero, ← pull_comp m, ← pull_comp m, hm, pull_id, pull_id, add_neg_eq_zero] at h'
  exact h'

theorem pull_one_eq_zero {R : Type} [CommRing R] [IsLocalRing R] {G Y : Over (Sp R)} [GrpObj G] (d : Pic G.left) :
    pull (1 : Y ⟶ G).left d = 0 := by
  have e : (1 : Y ⟶ G) = toUnit Y ≫ η[G] := rfl
  rw [e, Over.comp_left, pull_comp, GlobalTheory.DualOpen.pic_sp_local_eq_zero R (pull η[G].left d), map_zero]

theorem exists_translate_of_lam : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (D₀ D : DegPre R)
  (β : D₀.P.A ≅ D.P.A), IsMonHom β.hom →
  (∃ wΛ : LB.Iso (abelian₂ D₀.P.A D₀.P.L)
      ((abelian₂ D.P.A D.P.L).pull (lift (fst D₀.P.A D₀.P.A ≫ β.hom) (snd D₀.P.A D₀.P.A ≫ β.hom) : G2 D₀.P.A ⟶ G2 D.P.A).left),
    wΛ.IsGen) →
  ∃ b : 𝟙_ (Over (Sp R)) ⟶ D.P.A, padd D.P.A b b = η[D.P.A] ∧
    ∃ w : LB.Iso D₀.P.L (LB.LinComb D.P.L (GlobalTheory.MumCmp.twφ D₀ D β.hom b) GlobalTheory.MumCmp.twε), w.IsGen := by
  intro R _ _ _ _ D₀ D β hβ hw
  have := D.P.isAb.comm
  have := D₀.P.isAb.comm
  have hL₀ := D₀.P.isLB
  have hL := D.P.isLB
  set c₀ := cls D₀.P.L hL₀ with hc₀
  set c := cls D.P.L hL with hc
  have hd : IsDual D.P.A D.P.A (abelian₂ D.P.A D.P.L) :=
    CompanionTheory.PfDual.kTrivDual R D.P.A D.P.g D.P.isAb D.P.smoothDim D.P.L hL D.P.ktriv
  have hΛ : (abelian₂ D.P.A D.P.L).IsLB := hd.isLB
  have e : ∀ (Y : Over (Sp R)) (a t : Y ⟶ D.P.A), evc hΛ a t = lam c a t := fun Y a t ↦ by
    rw [evc, show cls _ hΛ = lam c (fst D.P.A D.P.A) (snd D.P.A D.P.A) from
      cls_cube_two hL _ _ hΛ, pull_lam, lift_fst, lift_snd]
  have l₁ : ∀ (Y : Over (Sp R)) (a a' t : Y ⟶ D.P.A), lam c (a * a') t = lam c a t + lam c a' t :=
    fun Y a a' t ↦ by
      rw [← e, ← e, ← e]
      exact (isAdditive_iff hΛ).1 hd.additive Y a a' t
  have l₂ : ∀ (Y : Over (Sp R)) (a t t' : Y ⟶ D.P.A), lam c a (t * t') = lam c a t + lam c a t' :=
    fun Y a t t' ↦ by rw [lam_comm, l₁, lam_comm _ t, lam_comm _ t']

  obtain ⟨wΛ, hwΛ⟩ := hw
  have hΛ₀ : (abelian₂ D₀.P.A D₀.P.L).IsLB := LB.isLB_linComb hL₀ _ _
  have eΛ : lam c₀ (fst D₀.P.A D₀.P.A) (snd D₀.P.A D₀.P.A) =
      lam c (fst D₀.P.A D₀.P.A ≫ β.hom) (snd D₀.P.A D₀.P.A ≫ β.hom) := by
    have h := (cls_eq_iff hΛ₀ (pull_isLB hΛ _)).2 ⟨wΛ, hwΛ⟩
    have h₁ : cls _ hΛ₀ = lam c₀ (fst D₀.P.A D₀.P.A) (snd D₀.P.A D₀.P.A) := cls_cube_two hL₀ _ _ hΛ₀
    have h₂ : cls _ hΛ = lam c (fst D.P.A D.P.A) (snd D.P.A D.P.A) := cls_cube_two hL _ _ hΛ
    rw [← h₁, h, cls_pull hΛ, h₂, pull_lam, lift_fst, lift_snd]
  have s₁ : ∀ (Y : Over (Sp R)) (u v : Y ⟶ D₀.P.A), lam c₀ u v = lam c (u ≫ β.hom) (v ≫ β.hom) := fun Y u v ↦ by
    have h := congrArg (pull (lift u v).left) eΛ
    simpa only [pull_lam, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc] using h

  have Fadd : ∀ (Y : Over (Sp R)) (a a' : Y ⟶ D.P.A),
      pull ((a * a') ≫ β.inv).left c₀ - pull (a * a').left c =
        (pull (a ≫ β.inv).left c₀ - pull a.left c) + (pull (a' ≫ β.inv).left c₀ - pull a'.left c) := by
    intro Y a a'
    have h := s₁ Y (a ≫ β.inv) (a' ≫ β.inv)
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, lam, pull_one_eq_zero, add_zero] at h
    rw [MonObj.mul_comp, ← sub_eq_zero]
    have h' := sub_eq_zero.2 h
    convert h' using 1
    abel
  let N : LB (D.P.A ⊗ 𝟙_ (Over (Sp R))).left :=
    tens (D₀.P.L.pull (fst D.P.A (𝟙_ (Over (Sp R))) ≫ β.inv).left)
      (dual (D.P.L.pull (fst D.P.A (𝟙_ (Over (Sp R)))).left))
  have hN : N.IsLB := isLB_tens (pull_isLB hL₀ _) (isLB_dual (pull_isLB hL _))
  have clsN : cls N hN = pull (fst D.P.A (𝟙_ (Over (Sp R))) ≫ β.inv).left c₀ -
      pull (fst D.P.A (𝟙_ (Over (Sp R)))).left c := by
    rw [show cls N hN = _ from cls_tens (pull_isLB hL₀ _) (isLB_dual (pull_isLB hL _)) hN,
      cls_dual (pull_isLB hL _), cls_pull hL₀, cls_pull hL, sub_eq_add_neg]
  have evN : ∀ (Y : Over (Sp R)) (a : Y ⟶ D.P.A) (t : Y ⟶ 𝟙_ (Over (Sp R))),
      evc hN a t = pull (a ≫ β.inv).left c₀ - pull a.left c := by
    intro Y a t
    rw [evc, clsN, map_sub, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, lift_fst_assoc, lift_fst]
  have hadd : IsAdditive N := (isAdditive_iff hN).2 fun Y a a' t ↦ by rw [evN, evN, evN, Fadd]
  obtain ⟨b, hb, -⟩ := hd.univ _ N hN hadd
  have eb := (cls_eq_iff hN (pull_isLB hΛ _)).2 hb
  have key : ∀ (Y : Over (Sp R)) (a : Y ⟶ D.P.A),
      pull (a ≫ β.inv).left c₀ - pull a.left c = lam c a (toUnit Y ≫ b) := by
    intro Y a
    have h : evc hN a (toUnit Y) = evc hΛ a (toUnit Y ≫ b) := by
      have h := congrArg (pull (lift a (toUnit Y)).left) eb
      rw [cls_pull hΛ] at h
      change evc hN a (toUnit Y) = pull (lift a (toUnit Y)).left
        (evc hΛ (fst D.P.A (𝟙_ (Over (Sp R)))) (snd D.P.A (𝟙_ (Over (Sp R))) ≫ b)) at h
      rw [pull_evc, lift_fst, lift_snd_assoc] at h
      exact h
    rw [← evN Y a (toUnit Y), h, e]
  refine ⟨b, ?_, ?_⟩
  ·
    have sym₀ : pull (GrpObj.inv : D₀.P.A ⟶ D₀.P.A).left c₀ = c₀ := pull_inv_cls D₀.P
    have sym : pull (GrpObj.inv : D.P.A ⟶ D.P.A).left c = c := pull_inv_cls D.P
    have odd : ∀ (Y : Over (Sp R)) (a : Y ⟶ D.P.A), lam c a (toUnit Y ≫ b) + lam c a (toUnit Y ≫ b) = 0 := by
      intro Y a
      have ia : a⁻¹ = a ≫ GrpObj.inv := rfl
      have ia' : (a ≫ β.inv)⁻¹ = (a ≫ β.inv) ≫ GrpObj.inv := rfl
      have h₁ : lam c a⁻¹ (toUnit Y ≫ b) = lam c a (toUnit Y ≫ b) := by
        rw [← key, ← key, GrpObj.inv_comp, ia, ia']
        simp only [Over.comp_left, pull_comp, sym₀, sym]
      have h₂ : lam c (a⁻¹ * a) (toUnit Y ≫ b) = 0 := by rw [inv_mul_cancel, lam_one_left]
      rw [l₁, h₁] at h₂
      exact h₂
    have two : b * b = 1 := by
      refine hd.eq_one (b * b) ((triv_ev_iff hΛ _ _).2 ?_)
      have hs : snd D.P.A (𝟙_ (Over (Sp R))) = toUnit _ := toUnit_unique _ _
      rw [e, hs, MonObj.comp_mul, l₂, odd]
    have e₁ : (1 : 𝟙_ (Over (Sp R)) ⟶ D.P.A) = η[D.P.A] := by
      rw [show (1 : 𝟙_ (Over (Sp R)) ⟶ D.P.A) = toUnit _ ≫ η[D.P.A] from rfl,
        toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    exact two.trans e₁
  ·
    have hC : (LB.LinComb D.P.L (twφ D₀ D β.hom b) twε).IsLB := LB.isLB_linComb hL _ _
    refine (cls_eq_iff hL₀ hC).1 ?_
    have h := key D₀.P.A β.hom
    rw [Iso.hom_inv_id, Over.id_left, pull_id, sub_eq_iff_eq_add] at h
    have e₁ : padd D.P.A β.hom (toUnit D₀.P.A ≫ b) = β.hom * (toUnit D₀.P.A ≫ b) := rfl
    have e₂ : toUnit D₀.P.A ≫ η[D.P.A] = 1 := rfl
    rw [cls_linComb hL, Fin.sum_univ_three]
    simp only [twφ, twε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons, one_smul, neg_smul, e₁, e₂]
    rw [← hc, ← hc₀, h, lam]
    abel

end GlobalTheory.MumCmp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslateOfMumfordBundleMatchStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_translate_of_mumfordBundle_match : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (D₀ D : DegPre R)
  (β : D₀.P.A ≅ D.P.A), IsMonHom β.hom →
  (∃ wΛ : LB.Iso (abelian₂ D₀.P.A D₀.P.L)
      ((abelian₂ D.P.A D.P.L).pull (lift (fst D₀.P.A D₀.P.A ≫ β.hom) (snd D₀.P.A D₀.P.A ≫ β.hom) : G2 D₀.P.A ⟶ G2 D.P.A).left),
    wΛ.IsGen) →
  ∃ b : 𝟙_ (Over (Sp R)) ⟶ D.P.A, padd D.P.A b b = η[D.P.A] ∧
    ∃ w : LB.Iso D₀.P.L (LB.LinComb D.P.L (GlobalTheory.MumCmp.twφ D₀ D β.hom b) GlobalTheory.MumCmp.twε), w.IsGen := by
  first | exact @GlobalTheory.MumCmp.exists_translate_of_lam | exact GlobalTheory.MumCmp.exists_translate_of_lam | (intros; apply GlobalTheory.MumCmp.exists_translate_of_lam <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrderTwoPointTorusExtensionTranslate
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdTw
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumCmp.Point

open GlobalTheory.LamBiext GlobalTheory.LamRigid GlobalTheory.PolDeg

variable {R : Type} [CommRing R] [IsDomain R] (D₀ D : DegPre R) (β : D₀.P.A ⟶ D.P.A)
  (b : 𝟙_ (Over (Sp R)) ⟶ D.P.A)

theorem prod_tw {T : Over (Sp R)} (x : T ⟶ D₀.P.A) {U : Type} [CommGroup U] (h : (T.left ⟶ D.P.A.left) → U) :
    ∏ i, h (x.left ≫ twφ D₀ D β b i) ^ twε i =
      h ((x ≫ β) * (toUnit T ≫ b)).left * (h (toUnit T ≫ b).left)⁻¹ * h (1 : T ⟶ D.P.A).left := by
  have hu : x ≫ toUnit D₀.P.A = toUnit T := toUnit_unique _ _
  rw [Fin.prod_univ_three]
  show h (x ≫ (β * (toUnit D₀.P.A ≫ b))).left ^ (1 : ℤ) * h (x ≫ toUnit D₀.P.A ≫ b).left ^ (-1 : ℤ) *
    h (x ≫ toUnit D₀.P.A ≫ η[D.P.A]).left ^ (1 : ℤ) = _
  rw [MonObj.comp_mul, ← Category.assoc x, ← Category.assoc x, hu, zpow_one, zpow_one, zpow_neg_one]
  rfl

theorem lift_β {T : Over (Sp R)} (p q : T ⟶ D₀.P.A) :
    (lift p q).left ≫ (lift (fst D₀.P.A D₀.P.A ≫ β) (snd D₀.P.A D₀.P.A ≫ β) : G2 D₀.P.A ⟶ G2 D.P.A).left =
      (lift (p ≫ β) (q ≫ β)).left := by
  rw [← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc]

variable {D₀ D β b} [IsMonHom β]

theorem wv_mul {w : LB.Iso D₀.P.L (LB.LinComb D.P.L (twφ D₀ D β b) twε)} (hw : w.IsGen)
    {wΛ : LB.Iso (abelian₂ D₀.P.A D₀.P.L) ((abelian₂ D.P.A D.P.L).pull
      (lift (fst D₀.P.A D₀.P.A ≫ β) (snd D₀.P.A D₀.P.A ≫ β) : G2 D₀.P.A ⟶ G2 D.P.A).left)} (hΛ : wΛ.IsGen)
    {T : Over (Sp R)} (x y : T ⟶ D₀.P.A) {z : T.left} {J J'} (hJ : Good D.P.L z J) (hJ' : Good D₀.P.L z J') :
    wv w (x * y).left z J J' * wv w (1 : T ⟶ D₀.P.A).left z J J' *
        lamVal wΛ (lift (1 : T ⟶ D₀.P.A) (1 : T ⟶ D₀.P.A)).left z J J' =
      wv w x.left z J J' * wv w y.left z J J' * lamVal wΛ (lift x y).left z J J' *
        cubV D.cub z J (x ≫ β) (y ≫ β) (toUnit T ≫ b) := by
  have hG := GlobalTheory.globalFns_holds
  let B₀ := D₀.P.A
  let f : B₀ ⊗ B₀ ⟶ B₀ := fst B₀ B₀
  let s : B₀ ⊗ B₀ ⟶ B₀ := snd B₀ B₀
  have H := (((((reg_wv hw (f * s).left).mul (reg_wv hw f.left).inv).mul (reg_wv hw s.left).inv).mul
    (reg_wv hw (1 : B₀ ⊗ B₀ ⟶ B₀).left)).mul (reg_lam hΛ (lift f s).left).inv).mul
    (reg_val (L' := D₀.P.L) (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.isGen
      (lift (f ≫ β) (lift (s ≫ β) (toUnit (B₀ ⊗ B₀) ≫ b))).left).inv
  have ev : ∀ x y : T ⟶ B₀,
      wv w ((lift x y).left ≫ (f * s).left) z J J' * (wv w ((lift x y).left ≫ f.left) z J J')⁻¹ *
        (wv w ((lift x y).left ≫ s.left) z J J')⁻¹ * wv w ((lift x y).left ≫ (1 : B₀ ⊗ B₀ ⟶ B₀).left) z J J' *
        (lamVal wΛ ((lift x y).left ≫ (lift f s).left) z J J')⁻¹ *
        (val (L := D.P.L) (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.t
          ((lift x y).left ≫ (lift (f ≫ β) (lift (s ≫ β) (toUnit (B₀ ⊗ B₀) ≫ b))).left) z J)⁻¹ =
      wv w (x * y).left z J J' * (wv w x.left z J J')⁻¹ * (wv w y.left z J J')⁻¹ *
        wv w (1 : T ⟶ B₀).left z J J' * (lamVal wΛ (lift x y).left z J J')⁻¹ *
        (cubV D.cub z J (x ≫ β) (y ≫ β) (toUnit T ≫ b))⁻¹ := fun x y => by
    have hu : lift x y ≫ toUnit (B₀ ⊗ B₀) = toUnit T := toUnit_unique _ _
    simp only [← Over.comp_left]
    rw [MonObj.comp_mul, MonObj.comp_one, comp_lift, comp_lift, comp_lift, ← Category.assoc (lift x y) (toUnit _), hu,
      lift_fst_assoc, lift_snd_assoc, lift_fst, lift_snd]
    rfl
  have E := H.rigid D.P.isLB D₀.P.isLB (fun U _ h h' => by
      show _ * _ * _ * _ * _ * _ = _
      rw [prod_tw, prod_tw, prod_tw, prod_tw, lift_β, prod_lam, prod_lam]
      erw [prod_cub (G := D.P.A) (f ≫ β) (s ≫ β) (toUnit (B₀ ⊗ B₀) ≫ b) h]
      rw [MonObj.mul_comp, MonObj.one_comp,
        _root_.one_mul]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_one]
      abel)
    ((snd B₀ B₀).left ≫ B₀.hom) (surj_comp (surj_snd hG D₀.P.isAb _) (hG _ _ D₀.P.isAb).2)
    (lift x y).left (lift (1 : T ⟶ B₀) (1 : T ⟶ B₀)).left (by
      rw [Over.w, Over.w, Over.w]) z hJ hJ'
  have E' := (ev x y).symm.trans (E.trans (ev 1 1))
  rw [MonObj.one_comp, (isCub_cubV D.cub hJ).face, _root_.mul_one (1 : T ⟶ B₀)] at E'
  apply Additive.ofMul.injective
  have e := congrArg Additive.ofMul E'
  simp only [ofMul_mul, ofMul_inv, ofMul_one] at e ⊢
  linear_combination (norm := abel) e

theorem wv_inv (hb : padd D.P.A b b = η[D.P.A]) {w : LB.Iso D₀.P.L (LB.LinComb D.P.L (twφ D₀ D β b) twε)} (hw : w.IsGen)
    {T : Over (Sp R)} (x : T ⟶ D₀.P.A) {z : T.left} {J J'} (hJ : Good D.P.L z J) (hJ' : Good D₀.P.L z J') :
    wv w x.left z J J' * val D.sym (x ≫ β).left z J * cubV D.cub z J (x ≫ β) (toUnit T ≫ b) (toUnit T ≫ b) =
      wv w (x⁻¹).left z J J' * val D₀.sym x.left z J' * cubV D.cub z J (x ≫ β) (x ≫ β)⁻¹ (toUnit T ≫ b) := by
  have hG := GlobalTheory.globalFns_holds
  let B₀ := D₀.P.A
  let f : B₀ ⟶ B₀ := 𝟙 B₀
  have hbb : (toUnit B₀ ≫ b) * (toUnit B₀ ≫ b) = 1 := by
    rw [← MonObj.comp_mul]; exact congrArg (toUnit B₀ ≫ ·) hb
  have H := (((((reg_wv hw f.left).mul (reg_val (L' := D₀.P.L) D.sym_gen (f ≫ β).left)).mul
    (reg_val (L' := D₀.P.L) (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.isGen
      (lift (f ≫ β) (lift (toUnit B₀ ≫ b) (toUnit B₀ ≫ b))).left)).mul (reg_wv hw (f⁻¹).left).inv).mul
      (reg_val' (L := D.P.L) D₀.sym_gen f.left).inv).mul
    (reg_val (L' := D₀.P.L) (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.isGen
      (lift (f ≫ β) (lift (f ≫ β)⁻¹ (toUnit B₀ ≫ b))).left).inv
  have ev : ∀ x : T ⟶ B₀,
      wv w (x.left ≫ f.left) z J J' * val D.sym (x.left ≫ (f ≫ β).left) z J *
        val (L := D.P.L) (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.t
          (x.left ≫ (lift (f ≫ β) (lift (toUnit B₀ ≫ b) (toUnit B₀ ≫ b))).left) z J *
        (wv w (x.left ≫ (f⁻¹).left) z J J')⁻¹ * (val D₀.sym (x.left ≫ f.left) z J')⁻¹ *
        (val (L := D.P.L) (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.t
          (x.left ≫ (lift (f ≫ β) (lift (f ≫ β)⁻¹ (toUnit B₀ ≫ b))).left) z J)⁻¹ =
      wv w x.left z J J' * val D.sym (x ≫ β).left z J * cubV D.cub z J (x ≫ β) (toUnit T ≫ b) (toUnit T ≫ b) *
        (wv w (x⁻¹).left z J J')⁻¹ * (val D₀.sym x.left z J')⁻¹ *
        (cubV D.cub z J (x ≫ β) (x ≫ β)⁻¹ (toUnit T ≫ b))⁻¹ := fun x => by
    have hu : x ≫ toUnit B₀ = toUnit T := toUnit_unique _ _
    simp only [← Over.comp_left]
    rw [comp_lift, comp_lift, comp_lift, comp_lift, ← Category.assoc x (toUnit _), hu, GrpObj.comp_inv, GrpObj.comp_inv,
      ← Category.assoc x f, Category.comp_id]
    rfl
  have E := H.rigid D.P.isLB D₀.P.isLB (fun U _ h h' => by
      show _ * _ * _ * _ * _ * _ = _
      rw [prod_tw, prod_tw, GlobalTheory.GaugeValues.prod_sym, GlobalTheory.GaugeValues.prod_sym]
      erw [prod_cub (G := D.P.A) (f ≫ β) (toUnit B₀ ≫ b) (toUnit B₀ ≫ b) h,
        prod_cub (G := D.P.A) (f ≫ β) (f ≫ β)⁻¹ (toUnit B₀ ≫ b) h]
      rw [GrpObj.inv_comp,
        _root_.mul_assoc (f ≫ β), hbb, _root_.mul_one (f ≫ β), mul_inv_cancel (f ≫ β), _root_.one_mul (toUnit B₀ ≫ b)]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_one]
      abel)
    B₀.hom (hG _ _ D₀.P.isAb).2 x.left (1 : T ⟶ B₀).left (by rw [Over.w, Over.w]) z hJ hJ'
  have E' := (ev x).symm.trans (E.trans (ev 1))
  rw [MonObj.one_comp, (isCub_cubV D.cub hJ).face, (isCub_cubV D.cub hJ).face, inv_one,
    GlobalTheory.GaugeValues.val_sym_one D hJ, GlobalTheory.GaugeValues.val_sym_one D₀ hJ'] at E'
  apply Additive.ofMul.injective
  have e := congrArg Additive.ofMul E'
  simp only [ofMul_mul, ofMul_inv, ofMul_one] at e ⊢
  linear_combination (norm := abel) e

end GlobalTheory.MumCmp.Point
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrderTwoPointTorusExtensionTranslate
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumCmp.Point

open GlobalTheory.LamBiext GlobalTheory.LamRigid GlobalTheory.PolDeg

variable {R : Type} [CommRing R] [IsDomain R]

theorem exists_unit_of_sq [IsIntegrallyClosed R] (a : Γ(Spec (CommRingCat.of (FractionRing R)), ⊤)ˣ)
    (a' : Γ(Spec (CommRingCat.of R), ⊤)ˣ) (h : a * a = pullU (jK R) ⊤ a') :
    ∃ u : Γ(Spec (CommRingCat.of R), ⊤)ˣ, pullU (jK R) ⊤ u = a := by
  let φ := (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm
  let φK := (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).commRingCatIsoToRingEquiv.symm
  have nat : ∀ r : R, (jK R).appTop.hom (φ r) = φK (algebraMap R (FractionRing R) r) := fun r =>
    (congrArg (fun q => q.hom r)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))).symm
  obtain ⟨k, hk⟩ := φK.surjective a.val
  obtain ⟨r, hr⟩ := φ.surjective a'.val
  have e : (show FractionRing R from k) ^ 2 = algebraMap R (FractionRing R) r := by
    apply φK.injective
    rw [← nat, hr, sq]
    exact (map_mul φK k k).trans (by rw [hk]; exact congrArg Units.val h)
  obtain ⟨s, hs⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow (R := R) (K := FractionRing R)
    (x := k) two_pos (by rw [e]; exact isIntegral_algebraMap)
  have e' : s * s = r := IsFractionRing.injective R (FractionRing R) (by rw [map_mul, hs, ← e, sq])
  have hu : IsUnit (φ s) := isUnit_of_mul_isUnit_left (y := φ s) (by
    rw [← map_mul φ s s]
    exact (congrArg IsUnit ((congrArg φ e').trans hr)).mpr a'.isUnit)
  refine ⟨hu.unit, Units.ext ?_⟩
  show (jK R).appTop.hom (φ s) = _
  rw [nat, hs, hk]

theorem prod_gt (D : DegPre R) {T T' : Over (Sp R)} (ρ : T' ⟶ T) (b : T ⟶ D.P.A) (χ : D.X) {U : Type} [CommGroup U]
    (h : (T'.left ⟶ D.P.A.left) → U) :
    ∏ k, h (ρ.left ≫ DegPre.gtφT D T b χ k) ^ DegPre.gtε k =
      (h ((toUnit T' ≫ D.c χ) * (ρ ≫ b)).left)⁻¹ * h (toUnit T' ≫ D.c χ).left * h (ρ ≫ b).left *
        (h (1 : T' ⟶ D.P.A).left)⁻¹ := by
  have hu : ρ ≫ toUnit T = toUnit T' := toUnit_unique _ _
  rw [Fin.prod_univ_four]
  show h (ρ ≫ ((toUnit T ≫ D.c χ) * b)).left ^ (-1 : ℤ) * h (ρ ≫ toUnit T ≫ D.c χ).left ^ (1 : ℤ) *
    h (ρ ≫ b).left ^ (1 : ℤ) * h (ρ ≫ toUnit T ≫ η[D.P.A]).left ^ (-1 : ℤ) = _
  rw [MonObj.comp_mul, ← Category.assoc ρ, ← Category.assoc ρ, hu, zpow_one, zpow_one, zpow_neg_one, zpow_neg_one]
  rfl

variable {D₀ D : DegPre R} {β : D₀.P.A ⟶ D.P.A} {b : 𝟙_ (Over (Sp R)) ⟶ D.P.A} [IsMonHom β]

theorem exists_normalised {w : LB.Iso D₀.P.L (LB.LinComb D.P.L (twφ D₀ D β b) twε)} (hw : w.IsGen) :
    ∃ w' : LB.Iso D₀.P.L (LB.LinComb D.P.L (twφ D₀ D β b) twε), w'.IsGen ∧
      ∀ (T : Over (Sp R)) (z : T.left) J J', Good D.P.L z J → Good D₀.P.L z J' →
        wv w' (1 : T ⟶ D₀.P.A).left z J J' * val D₀.rig (toUnit T).left z J' = val D.rig (toUnit T).left z J := by
  let E := 𝟙_ (Over (Sp R))
  obtain ⟨a, ha⟩ := (((reg_val (L' := D₀.P.L) D.rig_gen (toUnit E).left).mul
    (reg_wv hw (1 : E ⟶ D₀.P.A).left).inv).mul (reg_val' (L := D.P.L) D₀.rig_gen (toUnit E).left).inv).glue
    D.P.isLB D₀.P.isLB (fun U _ h h' => by
      show _ * _ * _ = _
      rw [prod_tw, Fintype.prod_unique, Fintype.prod_unique, MonObj.one_comp, _root_.one_mul]
      show h (1 : E ⟶ D.P.A).left ^ (1 : ℤ) * _ * (h' (1 : E ⟶ D₀.P.A).left ^ (1 : ℤ))⁻¹ = 1
      apply Additive.ofMul.injective
      simp only [zpow_one, ofMul_mul, ofMul_inv, ofMul_one]
      abel)
  refine ⟨scale (pullU (toUnit D₀.P.A).left ⊤ a) w, scale_isGen _ hw, fun T z J J' hJ hJ' => ?_⟩
  have e := ha _ (toUnit T).left z J J' hJ hJ'
  have e₁ : (toUnit T).left ≫ (toUnit E).left = (toUnit T).left := congrArg (·.left) (toUnit_unique (toUnit T ≫ toUnit E) _)
  have e₂ : (toUnit T).left ≫ (1 : E ⟶ D₀.P.A).left = (1 : T ⟶ D₀.P.A).left :=
    congrArg (fun q : T ⟶ D₀.P.A => q.left) (MonObj.comp_one (toUnit T))
  have e₃ : (1 : T ⟶ D₀.P.A).left ≫ (toUnit D₀.P.A).left = (toUnit T).left :=
    congrArg (·.left) (toUnit_unique ((1 : T ⟶ D₀.P.A) ≫ toUnit D₀.P.A) _)
  simp only [e₁, e₂] at e
  have s : wv (scale (pullU (toUnit D₀.P.A).left ⊤ a) w) (1 : T ⟶ D₀.P.A).left z J J' =
      gm (toUnit T).left z ⊤ a * wv w (1 : T ⟶ D₀.P.A).left z J J' :=
    (gm_scale (pullU (toUnit D₀.P.A).left ⊤ a) w (1 : T ⟶ D₀.P.A).left z
      (fun k => J ((1 : T ⟶ D₀.P.A).left ≫ twφ D₀ D β b k), J' (1 : T ⟶ D₀.P.A).left) ⟨hJ.mem _ _, hJ' _⟩).trans (congrArg (· * _)
      ((gm_pull _ (toUnit D₀.P.A).left z ⊤ trivial a).trans (by rw [e₃])))
  rw [s, ← e]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

def sv (xe : D₀.X ≃+ D.X) (w : LB.Iso D₀.P.L (LB.LinComb D.P.L (twφ D₀ D β b) twε)) (χ : D₀.X) (z : (TK R).left)
    (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι) (J' : ((TK R).left ⟶ D₀.P.A.left) → D₀.P.L.ι) :
    ((TK R).left.presheaf.stalk z)ˣ :=
  (wv w (toUnit (TK R) ≫ D₀.c χ).left z J J')⁻¹ * val (D₀.psi χ) (𝟙 _) z J' * (val (D.psi (xe χ)) (𝟙 _) z J)⁻¹

theorem cK_add (D : DegPre R) (T : Over (Sp R)) (χ χ' : D.X) :
    toUnit T ≫ D.c (χ + χ') = (toUnit T ≫ D.c χ) * (toUnit T ≫ D.c χ') := by
  rw [D.c_add, ← MonObj.comp_mul]; rfl

theorem cK_zero (D : DegPre R) (T : Over (Sp R)) : toUnit T ≫ D.c 0 = 1 := PsiZero.cPoint_zero' D T

theorem cK_neg (D : DegPre R) (T : Over (Sp R)) (χ : D.X) : toUnit T ≫ D.c (-χ) = (toUnit T ≫ D.c χ)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← cK_add, neg_add_cancel, cK_zero])

theorem val_rigK (D : DegPre R) {z : (TK R).left} {J} (hJ : Good D.P.L z J) :
    val D.rigK (𝟙 _) z J = val D.rig (toUnit (TK R)).left z J :=
  (val_pull hJ _ _ _).trans (by rw [Category.id_comp])

theorem val_tau' (D : DegPre R) {z : (TK R).left} {J} (hJ : Good D.P.L z J) (a a' : D.X) :
    val (D.tau a a') (𝟙 _) z J = val (D.psi (a + a')) (𝟙 _) z J * (val (D.psi a) (𝟙 _) z J)⁻¹ *
      (val (D.psi a') (𝟙 _) z J)⁻¹ * (val D.rig (toUnit (TK R)).left z J)⁻¹ :=
  (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) ((val_inv _ _).trans (congrArg (·⁻¹) (val_rigK D hJ))))

theorem val_psi_neg {D : DegPre R} (hE : D.PsiEven) {z : (TK R).left} {J} (hJ : Good D.P.L z J) (χ : D.X) :
    val (D.psi (-χ)) (𝟙 _) z J * val D.sym (toUnit (TK R) ≫ D.c χ).left z J = val (D.psi χ) (𝟙 _) z J := by
  refine Eq.trans ?_ (val_corr hJ (hE χ) (𝟙 _))
  refine Eq.trans ?_ ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_pull hJ _ _ _))).symm
  rw [Category.id_comp]

section Laws

variable {xe : D₀.X ≃+ D.X} {w : LB.Iso D₀.P.L (LB.LinComb D.P.L (twφ D₀ D β b) twε)}
  {z : (TK R).left} {J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι} {J' : ((TK R).left ⟶ D₀.P.A.left) → D₀.P.L.ι}

omit [IsMonHom β] in
theorem sv_zero (hB₀ : D₀.TauBimult) (hB : D.TauBimult) (hJ : Good D.P.L z J) (hJ' : Good D₀.P.L z J')
    (hn : wv w (1 : TK R ⟶ D₀.P.A).left z J J' * val D₀.rig (toUnit (TK R)).left z J' =
      val D.rig (toUnit (TK R)).left z J) : sv xe w 0 z J J' = 1 := by
  have p₀ : val (D₀.psi 0) (𝟙 _) z J' = (val D₀.rig (toUnit (TK R)).left z J')⁻¹ := PsiZero.val_psi_zero hB₀ hJ'
  have p : val (D.psi 0) (𝟙 _) z J = (val D.rig (toUnit (TK R)).left z J)⁻¹ := PsiZero.val_psi_zero hB hJ
  have q : val (D.psi (xe 0)) (𝟙 _) z J = val (D.psi 0) (𝟙 _) z J := by rw [map_zero]
  rw [sv, q, p₀, p, cK_zero, ← hn]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_one]
  abel

theorem sv_add (hB₀ : D₀.TauBimult) (hB : D.TauBimult) (hc : ∀ χ, D₀.c χ ≫ β = D.c (xe χ)) (hw : w.IsGen)
    {wΛ : LB.Iso (abelian₂ D₀.P.A D₀.P.L) ((abelian₂ D.P.A D.P.L).pull
      (lift (fst D₀.P.A D₀.P.A ≫ β) (snd D₀.P.A D₀.P.A ≫ β) : G2 D₀.P.A ⟶ G2 D.P.A).left)} (hΛ : wΛ.IsGen)
    (hJ : Good D.P.L z J) (hJ' : Good D₀.P.L z J')
    (hτ : ∀ a a' : D₀.X, val (D₀.tau a a') (𝟙 _) z J' =
      lamVal wΛ (lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left z J J' *
        val (D.tau (xe a) (xe a')) (𝟙 _) z J)
    (hn : wv w (1 : TK R ⟶ D₀.P.A).left z J J' * val D₀.rig (toUnit (TK R)).left z J' =
      val D.rig (toUnit (TK R)).left z J) (χ χ' : D₀.X) :
    sv xe w (χ + χ') z J J' *
        cubV D.cub z J (toUnit (TK R) ≫ D.c (xe χ)) (toUnit (TK R) ≫ D.c (xe χ')) (toUnit (TK R) ≫ b) =
      sv xe w χ z J J' * sv xe w χ' z J J' := by
  have p₀ : val (D₀.psi 0) (𝟙 _) z J' = (val D₀.rig (toUnit (TK R)).left z J')⁻¹ := PsiZero.val_psi_zero hB₀ hJ'
  have p : val (D.psi 0) (𝟙 _) z J = (val D.rig (toUnit (TK R)).left z J)⁻¹ := PsiZero.val_psi_zero hB hJ
  have q₀ : ∀ a a' : D₀.X, a = a' → val (D₀.psi a) (𝟙 _) z J' = val (D₀.psi a') (𝟙 _) z J' := by rintro a a' rfl; rfl
  have q : ∀ a a' : D.X, a = a' → val (D.psi a) (𝟙 _) z J = val (D.psi a') (𝟙 _) z J := by rintro a a' rfl; rfl
  have t₀ := hτ 0 0
  rw [val_tau' D₀ hJ', val_tau' D hJ, q₀ (0 + 0) 0 (add_zero 0), q (xe 0 + xe 0) 0 (by simp), q (xe 0) 0 (map_zero xe),
    p₀, p, cK_zero] at t₀
  have t := hτ χ χ'
  rw [val_tau' D₀ hJ', val_tau' D hJ, q (xe χ + xe χ') (xe (χ + χ')) (map_add xe χ χ').symm] at t
  have m := wv_mul hw hΛ (toUnit (TK R) ≫ D₀.c χ) (toUnit (TK R) ≫ D₀.c χ') hJ hJ'
  rw [Category.assoc, Category.assoc, hc, hc, ← cK_add] at m
  unfold sv
  apply Additive.ofMul.injective
  have E := fun {p q : ((TK R).left.presheaf.stalk z)ˣ} (e : p = q) => congrArg Additive.ofMul e
  have a₁ := E t₀; have a₂ := E t; have a₃ := E m; have a₄ := E hn
  simp only [ofMul_mul, ofMul_inv] at a₁ a₂ a₃ a₄ ⊢
  linear_combination (norm := abel) a₂ - a₁ - a₃ + a₄

theorem sv_sq (hE₀ : D₀.PsiEven) (hE : D.PsiEven) (hc : ∀ χ, D₀.c χ ≫ β = D.c (xe χ)) (hw : w.IsGen)
    (hb : padd D.P.A b b = η[D.P.A]) (hJ : Good D.P.L z J) (hJ' : Good D₀.P.L z J') (h0 : sv xe w 0 z J J' = 1)
    (χ : D₀.X) (hadd : sv xe w (χ + -χ) z J J' *
        cubV D.cub z J (toUnit (TK R) ≫ D.c (xe χ)) (toUnit (TK R) ≫ D.c (xe (-χ))) (toUnit (TK R) ≫ b) =
      sv xe w χ z J J' * sv xe w (-χ) z J J') :
    sv xe w χ z J J' * sv xe w χ z J J' =
      cubV D.cub z J (toUnit (TK R) ≫ D.c (xe χ)) (toUnit (TK R) ≫ b) (toUnit (TK R) ≫ b) := by
  have q : ∀ a a' : D.X, a = a' → val (D.psi a) (𝟙 _) z J = val (D.psi a') (𝟙 _) z J := by rintro a a' rfl; rfl
  rw [add_neg_cancel, h0, map_neg, cK_neg] at hadd
  have e₀ := val_psi_neg hE₀ hJ' χ
  have e := val_psi_neg hE hJ (xe χ)
  have m := wv_inv hb hw (toUnit (TK R) ≫ D₀.c χ) hJ hJ'
  rw [Category.assoc, hc] at m
  unfold sv at hadd ⊢
  rw [cK_neg, q (xe (-χ)) (-xe χ) (map_neg xe χ)] at hadd
  apply Additive.ofMul.injective
  have E := fun {p q : ((TK R).left.presheaf.stalk z)ˣ} (e : p = q) => congrArg Additive.ofMul e
  have a₁ := E e₀; have a₂ := E e; have a₃ := E m; have a₄ := E hadd
  simp only [ofMul_mul, ofMul_inv, ofMul_one] at a₁ a₂ a₃ a₄ ⊢
  linear_combination (norm := abel) a₂ - a₁ - a₃ - a₄

end Laws

theorem exists_coord [IsLocalRing R] [IsIntegrallyClosed R] {xe : D₀.X ≃+ D.X}
    {w : LB.Iso D₀.P.L (LB.LinComb D.P.L (twφ D₀ D β b) twε)} (hc : ∀ χ, D₀.c χ ≫ β = D.c (xe χ)) (hw : w.IsGen)
    (hb : padd D.P.A b b = η[D.P.A]) (χ : D₀.X)
    (hs : ∀ (z : (TK R).left) J J', Good D.P.L z J → Good D₀.P.L z J' → sv xe w χ z J J' * sv xe w χ z J J' =
      cubV D.cub z J (toUnit (TK R) ≫ D.c (xe χ)) (toUnit (TK R) ≫ b) (toUnit (TK R) ≫ b)) :
    ∃ s : LB.Gen (LB.LinComb D.P.L (DegPre.gtφT D (𝟙_ (Over (Sp R))) b (xe χ)) DegPre.gtε), s.IsGen ∧
      ∀ (z : (TK R).left) J J', Good D.P.L z J → Good D₀.P.L z J' →
        val s (toUnit (TK R)).left z J = sv xe w χ z J J' := by
  let E := 𝟙_ (Over (Sp R))
  have hbb : b * b = 1 := hb.trans (by rw [Hom.one_def, toUnit_unit, Category.id_comp])
  obtain ⟨σ, hσ⟩ := DVR.exists_gen_of_local (V := R) D.P.L D.P.isLB (DegPre.gtφT D E b (xe χ)) DegPre.gtε
  obtain ⟨a, ha⟩ := ((((reg_wv hw (toUnit (TK R) ≫ D₀.c χ).left).inv.mul
    (reg_val' (L := D.P.L) (D₀.psi_gen χ) (𝟙 _))).mul (reg_val (L' := D₀.P.L) (D.psi_gen (xe χ)) (𝟙 _)).inv).mul
    (reg_val (L' := D₀.P.L) (φ := DegPre.gtφT D E b (xe χ)) (ε := DegPre.gtε) hσ (toUnit (TK R)).left).inv).glue
    D.P.isLB D₀.P.isLB (fun U _ h h' => by
      show _ * _ * _ * _ = _
      rw [prod_tw, prod_gt, Fintype.prod_unique, Fintype.prod_unique, Category.id_comp, Category.id_comp,
        Category.assoc, hc]
      apply Additive.ofMul.injective
      simp only [zpow_neg, zpow_one, ofMul_mul, ofMul_inv, ofMul_one]
      abel)
  obtain ⟨a', ha'⟩ := (((reg_val (L' := D₀.P.L) (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.isGen
      (lift (toUnit E ≫ D.c (xe χ)) (lift b b)).left).mul
    (reg_val (L' := D₀.P.L) (φ := DegPre.gtφT D E b (xe χ)) (ε := DegPre.gtε) hσ (𝟙 E : E ⟶ E).left).inv).mul
    (reg_val (L' := D₀.P.L) (φ := DegPre.gtφT D E b (xe χ)) (ε := DegPre.gtε) hσ (𝟙 E : E ⟶ E).left).inv).glue
    D.P.isLB D₀.P.isLB (fun U _ h h' => by
      show _ * _ * _ = _
      rw [prod_gt]
      erw [prod_cub (G := D.P.A) (toUnit E ≫ D.c (xe χ)) b b h]
      rw [Category.id_comp, _root_.mul_assoc (toUnit E ≫ D.c (xe χ)), hbb, _root_.mul_one (toUnit E ≫ D.c (xe χ))]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_one]
      abel)
  have va : ∀ (z : (TK R).left) J J', Good D.P.L z J → Good D₀.P.L z J' →
      sv xe w χ z J J' * (val (φ := DegPre.gtφT D E b (xe χ)) (ε := DegPre.gtε) σ (toUnit (TK R)).left z J)⁻¹ =
        gm (𝟙 (TK R).left) z ⊤ a := fun z J J' hJ hJ' => by
    have e := ha _ (𝟙 _) z J J' hJ hJ'
    simp only [Category.id_comp] at e
    exact e
  have va' : ∀ (z : (TK R).left) J J', Good D.P.L z J → Good D₀.P.L z J' →
      cubV D.cub z J (toUnit (TK R) ≫ D.c (xe χ)) (toUnit (TK R) ≫ b) (toUnit (TK R) ≫ b) *
        (val (φ := DegPre.gtφT D E b (xe χ)) (ε := DegPre.gtε) σ (toUnit (TK R)).left z J)⁻¹ *
        (val (φ := DegPre.gtφT D E b (xe χ)) (ε := DegPre.gtε) σ (toUnit (TK R)).left z J)⁻¹ =
        gm (toUnit (TK R)).left z ⊤ a' := fun z J J' hJ hJ' => by
    have e := ha' _ (toUnit (TK R)).left z J J' hJ hJ'
    have hu : toUnit (TK R) ≫ toUnit E = toUnit (TK R) := toUnit_unique _ _
    simp only [← Over.comp_left] at e
    rw [comp_lift, comp_lift, ← Category.assoc, hu, Category.comp_id] at e
    exact e
  obtain ⟨u, hu⟩ := exists_unit_of_sq (R := R) a a' (unit_ext fun z _ => by
    obtain ⟨J, hJ⟩ := good_exists D.P.isLB (Z := (TK R).left) z
    obtain ⟨J', hJ'⟩ := good_exists D₀.P.isLB (Z := (TK R).left) z
    refine (map_mul _ _ _).trans ((congrArg₂ (· * ·) (va z J J' hJ hJ').symm (va z J J' hJ hJ').symm).trans
      (Eq.trans ?_ ((va' z J J' hJ hJ').trans (gm_pull (𝟙 _) (jK R) z ⊤ trivial a').symm)))
    rw [← hs z J J' hJ hJ']
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel)
  refine ⟨scale u σ, scale_isGen u hσ, fun z J J' hJ hJ' => ?_⟩
  refine (gm_scale u σ (toUnit (TK R)).left z _ (hJ.mem _ _)).trans ?_
  have e : gm (toUnit (TK R)).left z ⊤ u = gm (𝟙 (TK R).left) z ⊤ a :=
    (gm_pull (𝟙 _) (jK R) z ⊤ trivial u).symm.trans (congrArg (gm (𝟙 (TK R).left) z ⊤) hu)
  exact (congrArg (· * _) (e.trans (va z J J' hJ hJ').symm)).trans (inv_mul_cancel_right _ _)

theorem exists_zero (D : DegPre R) (T : Over (Sp R)) : ∃ o : GtPt D T, o.IsZero := by
  have H : ∀ χ : D.X, ∃ s : LB.Gen (LB.LinComb D.P.L (DegPre.gtφT D T (DegPre.zeroT D T) χ) DegPre.gtε), s.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) J, Good D.P.L z J → val s r z J = val (LB.oneGen D.P.L) r z J :=
    fun χ => exists_gen D.P.isLB (fun U _ h => by
      have e := prod_gt D (𝟙 T) (1 : T ⟶ D.P.A) χ h
      rw [Category.id_comp, _root_.mul_one] at e
      rw [Fintype.prod_empty]
      refine Eq.trans ?_ e.symm
      simp) (LB.oneGen D.P.L) (oneGen_isGen _)
  choose s hs vs using H
  refine ⟨⟨DegPre.zeroT D T, s, hs, corr_of_val D.P.isLB fun y J hJ => vs 0 _ _ y J hJ,
    fun χ χ' => corr_of_val D.P.isLB fun y J hJ => ?_⟩, rfl, fun χ => corr_of_val D.P.isLB fun y J hJ => vs χ _ _ y J hJ⟩
  refine (val_mul hJ _ _ _).trans (Eq.trans ?_ (val_mul hJ _ _ _).symm)
  rw [vs _ _ _ y J hJ, vs _ _ _ y J hJ, vs _ _ _ y J hJ, val_one, _root_.one_mul, _root_.one_mul]
  refine (val_cub D.cub (𝟙 T) hJ _ _ _).trans ?_
  rw [Category.id_comp (DegPre.zeroT D T)]
  exact (isCub_cubV D.cub hJ).face₃ _ _

theorem exists_point : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₀ D : DegData R (maximalIdeal R))
  (β : D₀.toPre.P.A ≅ D.toPre.P.A) (xe : D₀.toPre.X ≃+ D.toPre.X), IsMonHom β.hom →
  (∀ χ, D₀.toPre.c χ ≫ β.hom = D.toPre.c (xe χ)) →
  ∀ wΛ : LB.Iso (abelian₂ D₀.toPre.P.A D₀.toPre.P.L)
      ((abelian₂ D.toPre.P.A D.toPre.P.L).pull
        (lift (fst D₀.toPre.P.A D₀.toPre.P.A ≫ β.hom) (snd D₀.toPre.P.A D₀.toPre.P.A ≫ β.hom) :
          G2 D₀.toPre.P.A ⟶ G2 D.toPre.P.A).left),
    wΛ.IsGen →
    (∀ (a a' : D₀.toPre.X) (z : (TK R).left) (J : ((TK R).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι)
        (J' : ((TK R).left ⟶ D₀.toPre.P.A.left) → D₀.toPre.P.L.ι), Good D.toPre.P.L z J → Good D₀.toPre.P.L z J' →
        val (D₀.toPre.tau a a') (𝟙 _) z J' =
          GlobalTheory.PolDeg.lamVal wΛ (lift (toUnit (TK R) ≫ D₀.toPre.c a) (toUnit (TK R) ≫ D₀.toPre.c a')).left z J J' *
            val (D.toPre.tau (xe a) (xe a')) (𝟙 _) z J) →
  ∀ b : 𝟙_ (Over (Sp R)) ⟶ D.toPre.P.A, padd D.toPre.P.A b b = η[D.toPre.P.A] →
  ∀ w : LB.Iso D₀.toPre.P.L (LB.LinComb D.toPre.P.L (GlobalTheory.MumCmp.twφ D₀.toPre D.toPre β.hom b) GlobalTheory.MumCmp.twε), w.IsGen →
  ∃ g : GtPt D.toPre (𝟙_ (Over (Sp R))), g.b = b ∧ (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) ∧
    GlobalTheory.MumCmp.IsTwist D₀.toPre D.toPre g := by
  intro R _ _ _ hR D₀ D β xe mβ hc wΛ hΛ hτ b hb w₀ hw₀
  have := hR.1.2.2.1
  obtain ⟨w, hw, hn⟩ := exists_normalised hw₀
  have h0 : ∀ (z : (TK R).left) J J', Good D.toPre.P.L z J → Good D₀.toPre.P.L z J' → sv xe w 0 z J J' = 1 :=
    fun z J J' hJ hJ' => sv_zero D₀.tau_bimult D.tau_bimult hJ hJ' (hn _ z J J' hJ hJ')
  have hadd := fun (z : (TK R).left) J J' (hJ : Good D.toPre.P.L z J) (hJ' : Good D₀.toPre.P.L z J') =>
    sv_add D₀.tau_bimult D.tau_bimult hc hw hΛ hJ hJ' (fun a a' => hτ a a' z J J' hJ hJ') (hn _ z J J' hJ hJ')
  have hsq := fun (z : (TK R).left) J J' (hJ : Good D.toPre.P.L z J) (hJ' : Good D₀.toPre.P.L z J') χ =>
    sv_sq D₀.psi_even D.psi_even hc hw hb hJ hJ' (h0 z J J' hJ hJ') χ (hadd z J J' hJ hJ' χ (-χ))
  let E := 𝟙_ (Over (Sp R))
  have H : ∀ χ' : D.toPre.X, ∃ s : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.gtφT D.toPre E b χ') DegPre.gtε), s.IsGen ∧
      ∀ χ, xe χ = χ' → ∀ (z : (TK R).left) J J', Good D.toPre.P.L z J → Good D₀.toPre.P.L z J' →
        val s (toUnit (TK R)).left z J = sv xe w χ z J J' := fun χ' => by
    obtain ⟨χ, rfl⟩ := xe.surjective χ'
    obtain ⟨s, hs, vs⟩ := exists_coord hc hw hb χ (fun z J J' hJ hJ' => hsq z J J' hJ hJ' χ)
    exact ⟨s, hs, fun χ₂ e => by rw [xe.injective e]; exact vs⟩
  choose s hs vs using H
  obtain ⟨z₀⟩ : Nonempty (TK R).left := inferInstanceAs (Nonempty (PrimeSpectrum (FractionRing R)))
  obtain ⟨J', hJ'⟩ := good_exists D₀.toPre.P.isLB z₀
  have red : IsReduced E.left := inferInstanceAs (IsReduced (Spec (CommRingCat.of R)))
  have sep : D.toPre.P.A.left.IsSeparated := by
    have := D.toPre.P.isAb.proper
    exact ⟨by rw [← terminal.comp_from D.toPre.P.A.hom]; infer_instance⟩
  have hd : ∀ V : E.left.Opens, (V : Set E.left).Nonempty → (toUnit (TK R)).left z₀ ∈ V := TauPull.jK_mem z₀
  have hu : toUnit (TK R) ≫ toUnit E = toUnit (TK R) := toUnit_unique _ _
  have vc : ∀ J, Good D.toPre.P.L z₀ J → ∀ x x' y : E ⟶ D.toPre.P.A,
      val (DegPre.cubAtT D.toPre E x x' y) (toUnit (TK R)).left z₀ J =
        cubV D.toPre.cub z₀ J (toUnit (TK R) ≫ x) (toUnit (TK R) ≫ x') (toUnit (TK R) ≫ y) :=
    fun J hJ x x' y => val_cub D.toPre.cub (toUnit (TK R)) hJ x x' y
  let g : GtPt D.toPre E :=
    { b := b
      s := s
      isGen := hs
      s_zero := TauPull.corr_of_dense D.toPre.P.isLB (toUnit (TK R)).left z₀ hd fun J hJ => by
        rw [vs 0 0 (map_zero xe) z₀ J J' hJ hJ', h0 z₀ J J' hJ hJ', val_one]
      mult := fun χ χ' => TauPull.corr_of_dense D.toPre.P.isLB (toUnit (TK R)).left z₀ hd fun J hJ => by
        obtain ⟨χ, rfl⟩ := xe.surjective χ
        obtain ⟨χ', rfl⟩ := xe.surjective χ'
        refine (val_mul hJ _ _ _).trans (Eq.trans ?_ (val_mul hJ _ _ _).symm)
        rw [vs _ (χ + χ') (map_add xe χ χ') z₀ J J' hJ hJ', vs _ χ rfl z₀ J J' hJ hJ', vs _ χ' rfl z₀ J J' hJ hJ',
          ← hadd z₀ J J' hJ hJ' χ χ']
        refine congrArg (_ * ·) ((vc J hJ _ _ _).trans ?_)
        rw [← Category.assoc, ← Category.assoc, hu] }
  obtain ⟨o, ho⟩ := exists_zero D.toPre E
  refine ⟨g, rfl, ⟨o, ho, ?_, fun χ => TauPull.corr_of_dense D.toPre.P.isLB (toUnit (TK R)).left z₀ hd fun J hJ => ?_⟩,
    β, xe, mβ, hc, w, hw, fun χ => ?_⟩
  · refine ho.1.trans (Eq.trans ?_ hb.symm)
    rw [DegPre.zeroT, toUnit_unit, Category.id_comp]
  · obtain ⟨χ, rfl⟩ := xe.surjective χ
    refine (val_mul hJ _ _ _).trans (Eq.trans ?_ (val_mul hJ _ _ _).symm)
    rw [val_corr hJ (ho.2 _), val_one, _root_.one_mul]
    refine (vc J hJ _ _ _).trans (Eq.trans ?_ (congrArg₂ (· * ·) (vs _ χ rfl z₀ J J' hJ hJ')
      (vs _ χ rfl z₀ J J' hJ hJ')).symm)
    rw [hsq z₀ J J' hJ hJ' χ, ← Category.assoc, hu]
  · obtain ⟨t, ht, vt⟩ := exists_gen D.toPre.P.isLB
      (φ' := fun i => D₀.toPre.xK χ ≫ twφ D₀.toPre D.toPre β.hom b i) (ε' := fun i => -1 * twε i) (fun U _ h => by
        have e₁ := prod_tw D₀.toPre D.toPre β.hom b (toUnit (TK R) ≫ D₀.toPre.c χ) h
        have e₂ := prod_gt D.toPre (toUnit (TK R)) b (xe χ) h
        rw [Category.assoc, hc] at e₁
        rw [Fintype.prod_sum_type, Fintype.prod_unique]
        simp only [neg_mul, _root_.one_mul, zpow_neg, Finset.prod_inv_distrib]
        refine (congrArg₂ (· * ·) (zpow_neg_one _) e₂).trans (Eq.trans ?_ (congrArg (·⁻¹) e₁).symm)
        show (h (toUnit (TK R) ≫ D.toPre.c (xe χ)).left)⁻¹ * _ = _
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel)
      (LB.mulGen D.toPre.P.L _ _ _ _ (D.toPre.psi (xe χ)) (LB.pullGen D.toPre.P.L _ _ (s (xe χ)) (toUnit (TK R)).left))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (D.toPre.psi_gen _) (DVR.pullGen_isGen _ _ _ _ (hs _) _))
    refine ⟨t, mapsAtExp_of_val D.toPre.P.isLB D₀.toPre.P.isLB hw (D₀.toPre.psi_gen χ) ht fun y J J' hJ hJ' => ?_,
      corr_of_val D.toPre.P.isLB fun y J hJ => vt _ _ y J hJ⟩
    refine (vt _ _ y J hJ).trans ((val_mul hJ _ _ _).trans ?_)
    rw [val_pull hJ, Category.id_comp, vs _ χ rfl y J J' hJ hJ', sv, mul_comm, inv_mul_cancel_right, zpow_neg_one]

end GlobalTheory.MumCmp.Point
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrderTwoPointTorusExtensionTranslateStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_order_two_point_torus_extension_translate : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₀ D : DegData R (maximalIdeal R))
  (β : D₀.toPre.P.A ≅ D.toPre.P.A) (xe : D₀.toPre.X ≃+ D.toPre.X), IsMonHom β.hom →
  (∀ χ, D₀.toPre.c χ ≫ β.hom = D.toPre.c (xe χ)) →
  ∀ wΛ : LB.Iso (abelian₂ D₀.toPre.P.A D₀.toPre.P.L)
      ((abelian₂ D.toPre.P.A D.toPre.P.L).pull
        (lift (fst D₀.toPre.P.A D₀.toPre.P.A ≫ β.hom) (snd D₀.toPre.P.A D₀.toPre.P.A ≫ β.hom) :
          G2 D₀.toPre.P.A ⟶ G2 D.toPre.P.A).left),
    wΛ.IsGen →
    (∀ (a a' : D₀.toPre.X) (z : (TK R).left) (J : ((TK R).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι)
        (J' : ((TK R).left ⟶ D₀.toPre.P.A.left) → D₀.toPre.P.L.ι), Good D.toPre.P.L z J → Good D₀.toPre.P.L z J' →
        val (D₀.toPre.tau a a') (𝟙 _) z J' =
          GlobalTheory.PolDeg.lamVal wΛ (lift (toUnit (TK R) ≫ D₀.toPre.c a) (toUnit (TK R) ≫ D₀.toPre.c a')).left z J J' *
            val (D.toPre.tau (xe a) (xe a')) (𝟙 _) z J) →
  ∀ b : 𝟙_ (Over (Sp R)) ⟶ D.toPre.P.A, padd D.toPre.P.A b b = η[D.toPre.P.A] →
  ∀ w : LB.Iso D₀.toPre.P.L (LB.LinComb D.toPre.P.L (GlobalTheory.MumCmp.twφ D₀.toPre D.toPre β.hom b) GlobalTheory.MumCmp.twε), w.IsGen →
  ∃ g : GtPt D.toPre (𝟙_ (Over (Sp R))), g.b = b ∧ (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) ∧
    GlobalTheory.MumCmp.IsTwist D₀.toPre D.toPre g := by
  first | exact @GlobalTheory.MumCmp.Point.exists_point | exact GlobalTheory.MumCmp.Point.exists_point | (intros; apply GlobalTheory.MumCmp.Point.exists_point <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoRefinementsSamePolarised
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoRefinementsSamePolarised
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.MumCmp.SamePolIso
variable {R : Type} [CommRing R] [IsDomain R]

theorem grp_iso {B Q : Over (Sp R)} [GrpObj B] [GrpObj Q] {β : B.left ⟶ Q.left}
    (h : IsGrpPullback B Q (spMap (RingHom.id R)) β) : ∃ f : B ≅ Q, f.hom.left = β ∧ IsMonHom f.hom := by
  have hs : spMap (RingHom.id R) = 𝟙 (Sp R) := Spec.map_id _
  have h1 := h.1
  rw [hs] at h1
  have : IsIso β := h1.isIso_fst_of_isIso
  let f : B ⟶ Q := Over.homMk β (by simpa using h1.w)
  have : IsIso ((Over.forget (Sp R)).map f) := (inferInstance : IsIso β)
  have : IsIso f := isIso_of_reflects_iso f (Over.forget _)
  refine ⟨asIso f, rfl, isMonHom_of_mul _ fun T x y => ?_⟩
  let ρ : Over.mk (T.hom ≫ spMap (RingHom.id R)) ⟶ T := Over.homMk (𝟙 T.left) (by simp [hs])
  have e := h.2 T x y (ρ ≫ x ≫ f) (ρ ≫ y ≫ f) (by simp [ρ, f]) (by simp [ρ, f])
  apply Over.OverMorphism.ext
  rw [← MonObj.comp_mul] at e
  simpa [ρ, f] using e.symm

theorem gw_congr {X X' Y : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (w : LB.Iso L' (L.pull F))
    {f f' : Y ⟶ X'} (hf : f = f') (y : Y) {j j' : L.ι} (hj : j = j') {k k' : L'.ι} (hk : k = k') :
    gw w f y j k = gw w f' y j' k' := by
  subst hf hj hk; rfl

theorem exists_iso : ∀ (R : Type) [CommRing R] [IsDomain R] (D₀ D : DegPre R), SamePol D₀ D →
  ∃ (β : D₀.P.A ≅ D.P.A) (xe : D₀.X ≃+ D.X), IsMonHom β.hom ∧ (∀ χ, D₀.c χ ≫ β.hom = D.c (xe χ)) ∧
    ∃ wΛ : LB.Iso (abelian₂ D₀.P.A D₀.P.L)
        ((abelian₂ D.P.A D.P.L).pull (lift (fst D₀.P.A D₀.P.A ≫ β.hom) (snd D₀.P.A D₀.P.A ≫ β.hom) : G2 D₀.P.A ⟶ G2 D.P.A).left),
      wΛ.IsGen ∧
      ∀ (a a' : D₀.X) (z : (TK R).left) (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι)
        (J' : ((TK R).left ⟶ D₀.P.A.left) → D₀.P.L.ι), Good D.P.L z J → Good D₀.P.L z J' →
        val (D₀.tau a a') (𝟙 _) z J' =
          GlobalTheory.PolDeg.lamVal wΛ (lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left z J J' *
            val (D.tau (xe a) (xe a')) (𝟙 _) z J := by
  intro R _ _ D₀ D h
  obtain ⟨Q, e₀, e, ⟨β₀, β₂₀, w₀, p₀, s₀, g₀, c₀, t₀⟩, ⟨β₁, β₂₁, w₁, p₁, s₁, g₁, c₁, t₁⟩⟩ := h
  have hs : spMap (RingHom.id R) = 𝟙 (Sp R) := Spec.map_id _
  obtain ⟨f₀, hf₀, m₀⟩ := grp_iso p₀
  obtain ⟨f₁, hf₁, m₁⟩ := grp_iso p₁
  have cc₀ : ∀ a, D₀.c a ≫ f₀.hom = Q.c (e₀ a) := fun a => Over.OverMorphism.ext (by
    rw [Over.comp_left, hf₀, c₀ a, hs, Category.id_comp])
  have cc₁ : ∀ a, D.c a ≫ f₁.hom = Q.c (e a) := fun a => Over.OverMorphism.ext (by
    rw [Over.comp_left, hf₁, c₁ a, hs, Category.id_comp])
  have ea : ∀ x, e ((e₀.trans e.symm) x) = e₀ x := fun x => by simp
  have hcβ : ∀ χ, D₀.c χ ≫ (f₀ ≪≫ f₁.symm).hom = D.c ((e₀.trans e.symm) χ) := fun χ => by
    rw [Iso.trans_hom, Iso.symm_hom, ← Category.assoc, cc₀, Iso.comp_inv_eq, cc₁, ea]
  have hF : (lift (fst D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) (snd D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) :
      G2 D₀.P.A ⟶ G2 D.P.A).left ≫ β₂₁ = β₂₀ := by
    apply pullback.hom_ext
    · change _ ≫ β₂₁ ≫ (fst Q.B Q.B).left = β₂₀ ≫ (fst Q.B Q.B).left
      rw [s₁.1, s₀.1, ← Category.assoc, ← Over.comp_left, lift_fst, ← hf₁, ← hf₀, ← Over.comp_left, ← Over.comp_left]
      simp
    · change _ ≫ β₂₁ ≫ (snd Q.B Q.B).left = β₂₀ ≫ (snd Q.B Q.B).left
      rw [s₁.2, s₀.2, ← Category.assoc, ← Over.comp_left, lift_snd, ← hf₁, ← hf₀, ← Over.comp_left, ← Over.comp_left]
      simp

  subst hF
  have hLQ : (abelian₂ Q.B Q.M.L).IsLB := DVR.linComb_isLB _ Q.M.isLB _ _
  have hLD : (abelian₂ D.P.A D.P.L).IsLB := DVR.linComb_isLB _ D.P.isLB _ _
  have hLD₀ : (abelian₂ D₀.P.A D₀.P.L).IsLB := DVR.linComb_isLB _ D₀.P.isLB _ _
  obtain ⟨wΛ, T⟩ := exists_cancel hLQ w₁ w₀ ((isGen_iff _).1 g₁) ((isGen_iff _).1 g₀) hLD hLD₀
  refine ⟨f₀ ≪≫ f₁.symm, e₀.trans e.symm, ?_, hcβ, wΛ,
    (isGen_iff _).2 (T.pgen_cancel hLQ ((isGen_iff _).1 g₁) ((isGen_iff _).1 g₀)), ?_⟩
  · show IsMonHom (f₀.hom ≫ f₁.inv)
    infer_instance
  intro a a' z J J' hJ hJ'
  choose d hd using fun χ : (TK R).left ⟶ Q.B.left => exists_chart Q.M.isLB (χ z)
  have hκ : 𝟙 (TK R).left ≫ jK R = jK R ≫ spMap (RingHom.id R) := by rw [hs]; simp
  have A₀ := t₀ (𝟙 _) hκ a a' z d J' hd hJ'
  have A₁ := t₁ (𝟙 _) hκ ((e₀.trans e.symm) a) ((e₀.trans e.symm) a') z d J hd hJ
  rw [ea, ea] at A₁
  have hP : (lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left ≫ (lift (fst D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) (snd D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) : G2 D₀.P.A ⟶ G2 D.P.A).left = (lift (toUnit (TK R) ≫ D.c ((e₀.trans e.symm) a)) (toUnit (TK R) ≫ D.c ((e₀.trans e.symm) a'))).left := by
    rw [← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc, Category.assoc, Category.assoc, hcβ, hcβ]
  have m₁ : β₂₁ ((lift (fst D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) (snd D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) : G2 D₀.P.A ⟶ G2 D.P.A).left ((lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left z)) ∈ (abelian₂ Q.B Q.M.L).U
      (fun I => d ((lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left ≫ ((lift (fst D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) (snd D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) : G2 D₀.P.A ⟶ G2 D.P.A).left ≫ β₂₁) ≫ (psum Q.B (x2 Q.B) I.down).left)) := by
    have := Good.mem (L := Q.M.L) hd (fun I : ULift (Finset (Fin 2)) => (psum Q.B (x2 Q.B) I.down).left) ((lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left ≫ (lift (fst D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) (snd D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) : G2 D₀.P.A ⟶ G2 D.P.A).left ≫ β₂₁)
    simp only [Category.assoc] at this ⊢
    exact this
  have m₂ : (lift (fst D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) (snd D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) : G2 D₀.P.A ⟶ G2 D.P.A).left ((lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left z) ∈ (abelian₂ D.P.A D.P.L).U (fun I => J ((lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left ≫ (lift (fst D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) (snd D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) : G2 D₀.P.A ⟶ G2 D.P.A).left ≫ (psum D.P.A (x2 D.P.A) I.down).left)) := by
    have := Good.mem (L := D.P.L) hJ (fun I : ULift (Finset (Fin 2)) => (psum D.P.A (x2 D.P.A) I.down).left) ((lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left ≫ (lift (fst D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) (snd D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) : G2 D₀.P.A ⟶ G2 D.P.A).left)
    simp only [Category.assoc] at this
    exact this
  have m₃ : (lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left z ∈ (abelian₂ D₀.P.A D₀.P.L).U (fun I => J' ((lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left ≫ (psum D₀.P.A (x2 D₀.P.A) I.down).left)) :=
    Good.mem (L := D₀.P.L) hJ' (fun I : ULift (Finset (Fin 2)) => (psum D₀.P.A (x2 D₀.P.A) I.down).left) (lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left
  have key := T _ (lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left z _ _ _ m₁ m₂ m₃
  have k₁ : gw w₁ ((lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left ≫ (lift (fst D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) (snd D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) : G2 D₀.P.A ⟶ G2 D.P.A).left) z (fun I => d ((lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left ≫ ((lift (fst D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) (snd D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) : G2 D₀.P.A ⟶ G2 D.P.A).left ≫ β₂₁) ≫ (psum Q.B (x2 Q.B) I.down).left))
      (fun I => J ((lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left ≫ (lift (fst D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) (snd D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) : G2 D₀.P.A ⟶ G2 D.P.A).left ≫ (psum D.P.A (x2 D.P.A) I.down).left)) =
      GlobalTheory.PolDeg.lamVal w₁ (lift (toUnit (TK R) ≫ D.c ((e₀.trans e.symm) a))
        (toUnit (TK R) ≫ D.c ((e₀.trans e.symm) a'))).left z d J :=
    gw_congr w₁ hP z (funext fun I => by rw [← hP]; simp only [Category.assoc])
      (funext fun I => by rw [← hP]; simp only [Category.assoc])
  rw [k₁] at key
  rw [A₀, A₁]
  change gw w₀ (lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left z _ _ * _ = gw wΛ (lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left z _ _ * _
  rw [key, _root_.mul_assoc, _root_.mul_left_comm]
end GlobalTheory.MumCmp.SamePolIso
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoRefinementsSamePolarisedStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_iso_refinements_same_polarised : ∀ (R : Type) [CommRing R] [IsDomain R] (D₀ D : DegPre R), SamePol D₀ D →
  ∃ (β : D₀.P.A ≅ D.P.A) (xe : D₀.X ≃+ D.X), IsMonHom β.hom ∧ (∀ χ, D₀.c χ ≫ β.hom = D.c (xe χ)) ∧
    ∃ wΛ : LB.Iso (abelian₂ D₀.P.A D₀.P.L)
        ((abelian₂ D.P.A D.P.L).pull (lift (fst D₀.P.A D₀.P.A ≫ β.hom) (snd D₀.P.A D₀.P.A ≫ β.hom) : G2 D₀.P.A ⟶ G2 D.P.A).left),
      wΛ.IsGen ∧
      ∀ (a a' : D₀.X) (z : (TK R).left) (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι)
        (J' : ((TK R).left ⟶ D₀.P.A.left) → D₀.P.L.ι), Good D.P.L z J → Good D₀.P.L z J' →
        val (D₀.tau a a') (𝟙 _) z J' =
          GlobalTheory.PolDeg.lamVal wΛ (lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left z J J' *
            val (D.tau (xe a) (xe a')) (𝟙 _) z J := by
  first | exact @GlobalTheory.MumCmp.SamePolIso.exists_iso | exact GlobalTheory.MumCmp.SamePolIso.exists_iso | (intros; apply GlobalTheory.MumCmp.SamePolIso.exists_iso <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwoTorsionTwistOfSamePolarisedData
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumCmp

theorem exists_twist_of_samePol : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₀ D : DegData R (maximalIdeal R)), SamePol D₀.toPre D.toPre → ∃ g : GtPt D.toPre (𝟙_ (Over (Sp R))), (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) ∧ GlobalTheory.MumCmp.IsTwist D₀.toPre D.toPre g := by
  intro R _ _ _ hR D₀ D hS
  obtain ⟨β, xe, hβ, hc, wΛ, hwΛ, hτ⟩ := GlobalTheory.T.exists_iso_refinements_same_polarised R D₀.toPre D.toPre hS
  haveI : IsNoetherianRing R := hR.1.1
  obtain ⟨b, hb, w, hw⟩ := GlobalTheory.T.exists_translate_of_mumfordBundle_match R D₀.toPre D.toPre β hβ ⟨wΛ, hwΛ⟩
  obtain ⟨g, -, h2, ht⟩ := GlobalTheory.T.exists_order_two_point_torus_extension_translate R hR D₀ D β xe hβ hc wΛ hwΛ hτ b hb w hw
  exact ⟨g, h2, ht⟩

end GlobalTheory.MumCmp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwoTorsionTwistOfSamePolarisedDataStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_twoTorsion_twist_of_same_polarisedData : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₀ D : DegData R (maximalIdeal R)), SamePol D₀.toPre D.toPre → ∃ g : GtPt D.toPre (𝟙_ (Over (Sp R))), (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) ∧ GlobalTheory.MumCmp.IsTwist D₀.toPre D.toPre g := by
  first | exact @GlobalTheory.MumCmp.exists_twist_of_samePol | exact GlobalTheory.MumCmp.exists_twist_of_samePol | (intros; apply GlobalTheory.MumCmp.exists_twist_of_samePol <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrderTwoPointRefinementsCompareUnif
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumCmp

theorem point_and_compare : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₀ D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, SamePol D₀.toPre D.toPre → ∃ g : GtPt D.toPre (𝟙_ (Over (Sp R))), (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) ∧ ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → (∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ g.b.left ∧ ∀ χ : D.toPre.X, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ae) (LB.pullGen D.toPre.P.L _ _ (g.s χ) (thick R (maximalIdeal R) e))) → ∀ (A₂ : PolAV (Sp (FractionRing R))) (D₂ : DegData R (maximalIdeal R)) (U₂ : Unif (maximalIdeal R) D₂ A₂ G), LBIso U₂.LG.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left) → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (D₁ D₂' : DegData R' (maximalIdeal R')), FinExt ρ ∧ IsLocalHom ρ ∧ Nonempty (IsPullDeg ρ D₀.toPre D₁.toPre) ∧ Nonempty (IsPullDeg ρ D₂.toPre D₂'.toPre) ∧ Nonempty (IsPullDeg (RingHom.id R') D₁.toPre D₂'.toPre) := by
  have L1 := GlobalTheory.T.exists_twoTorsion_twist_of_same_polarisedData
  have L2 := GlobalTheory.T.uniformisationData_translate_orderTwo_isTwist
  have L3 := GlobalTheory.T.nonempty_isPullDeg_of_same_torus_twist
  intro R _ _ _ hB D₀ D A G _ _ hG U hS
  obtain ⟨g, hz, htw⟩ := L1 R hB D₀ D hS
  refine ⟨g, hz, fun a ha hlev A₂ D₂ U₂ hL => ?_⟩
  have h2 := L2 R hB D A G hG U g hz a ha hlev A₂ D₂ U₂ hL
  obtain ⟨h3⟩ := L3 R hB D₀ D₂ D g htw h2
  obtain ⟨s₀, -⟩ := GlobalTheory.DegPullId.exists_isPullDeg_id_self R (maximalIdeal R) hB.1 D₀
  obtain ⟨s₂, -⟩ := GlobalTheory.DegPullId.exists_isPullDeg_id_self R (maximalIdeal R) hB.1 D₂
  exact ⟨R, inferInstance, inferInstance, inferInstance, RingHom.id R, D₀, D₂,
    ⟨hB.1, Function.injective_id, RingHom.Finite.id R⟩, inferInstance, ⟨s₀⟩, ⟨s₂⟩, ⟨h3⟩⟩

end GlobalTheory.MumCmp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrderTwoPointRefinementsCompareUnifStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orderTwo_point_refinements_compare_unif : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₀ D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, SamePol D₀.toPre D.toPre → ∃ g : GtPt D.toPre (𝟙_ (Over (Sp R))), (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) ∧ ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → (∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ g.b.left ∧ ∀ χ : D.toPre.X, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ae) (LB.pullGen D.toPre.P.L _ _ (g.s χ) (thick R (maximalIdeal R) e))) → ∀ (A₂ : PolAV (Sp (FractionRing R))) (D₂ : DegData R (maximalIdeal R)) (U₂ : Unif (maximalIdeal R) D₂ A₂ G), LBIso U₂.LG.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left) → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (D₁ D₂' : DegData R' (maximalIdeal R')), FinExt ρ ∧ IsLocalHom ρ ∧ Nonempty (IsPullDeg ρ D₀.toPre D₁.toPre) ∧ Nonempty (IsPullDeg ρ D₂.toPre D₂'.toPre) ∧ Nonempty (IsPullDeg (RingHom.id R') D₁.toPre D₂'.toPre) := by
  first | exact @GlobalTheory.MumCmp.point_and_compare | exact GlobalTheory.MumCmp.point_and_compare | (intros; apply GlobalTheory.MumCmp.point_and_compare <;> assumption)
end
