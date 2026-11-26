module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftValuationSubring
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupHomCharacterMapConstant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConstOfPolConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoAlongHomsDescendsAbelianPart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorPeriodsProjectionPeriodPoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianHomTorsionCompatiblePeriodsLattices
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgClosedFieldTorsionMapsCommuteHom

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SamePolarisedOfTwoIdempotentFactors
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SamePolarisedOfTwoIdempotentFactors
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section
namespace GlobalTheory.Mum.TwoFac
variable {R : Type} [CommRing R] [IsDomain R] {D₁ D₂ D' : DegPre R}

theorem inc_pr_inc (F₁ : Factor D₁ D') (F₂ : Factor D₂ D') (he : F₁.o.onB.act F₁.e = F₂.o.onB.act F₂.e) :
    F₂.inc ≫ F₁.pr ≫ F₁.inc = F₂.inc := by
  rw [F₁.pr_inc, he, ← F₂.pr_inc, ← Category.assoc, F₂.inc_pr, Category.id_comp]

theorem comp_inv (F₁ : Factor D₁ D') (F₂ : Factor D₂ D') (he : F₁.o.onB.act F₁.e = F₂.o.onB.act F₂.e) :
    (F₂.inc ≫ F₁.pr) ≫ (F₁.inc ≫ F₂.pr) = 𝟙 _ := by
  simp only [Category.assoc]
  rw [← Category.assoc F₁.pr, ← Category.assoc F₂.inc, inc_pr_inc F₁ F₂ he, F₂.inc_pr]

theorem inv_comp (F₁ : Factor D₁ D') (F₂ : Factor D₂ D') (he : F₁.o.onB.act F₁.e = F₂.o.onB.act F₂.e) :
    (F₁.inc ≫ F₂.pr) ≫ (F₂.inc ≫ F₁.pr) = 𝟙 _ := by
  simp only [Category.assoc]
  rw [← Category.assoc F₂.pr, F₂.pr_inc, ← he, ← F₁.pr_inc, Category.assoc F₁.pr, ← Category.assoc F₁.inc, F₁.inc_pr,
    Category.id_comp]

theorem xi_xp_xi (F₁ : Factor D₁ D') (F₂ : Factor D₂ D') (hXe : ∀ z : D'.X, F₁.e • z = F₂.e • z) (a : D₂.X) :
    F₁.xi (F₁.xp (F₂.xi a)) = F₂.xi a := by
  rw [F₁.xi_xp, hXe, ← F₂.xi_xp, F₂.xp_xi]

theorem c_comp (F₁ : Factor D₁ D') (F₂ : Factor D₂ D') (hXe : ∀ z : D'.X, F₁.e • z = F₂.e • z) (a : D₂.X) :
    D₂.c a ≫ F₂.inc ≫ F₁.pr = D₁.c (F₁.xp (F₂.xi a)) := by
  have h := F₁.c_xi (F₁.xp (F₂.xi a))
  rw [xi_xp_xi F₁ F₂ hXe] at h
  rw [← Category.assoc, ← F₂.c_xi, h, Category.assoc, F₁.inc_pr, Category.comp_id]

def xEquiv (F₁ : Factor D₁ D') (F₂ : Factor D₂ D') (hXe : ∀ z : D'.X, F₁.e • z = F₂.e • z) : D₂.X ≃+ D₁.X where
  toFun a := F₁.xp (F₂.xi a)
  invFun a := F₂.xp (F₁.xi a)
  left_inv a := by
    show F₂.xp (F₁.xi (F₁.xp (F₂.xi a))) = a
    rw [xi_xp_xi F₁ F₂ hXe, F₂.xp_xi]
  right_inv a := by
    show F₁.xp (F₂.xi (F₂.xp (F₁.xi a))) = a
    rw [F₂.xi_xp, ← hXe, ← F₁.xi_xp, F₁.xp_xi, F₁.xp_xi]
  map_add' a b := by simp

theorem lift_comp (F₁ : Factor D₁ D') (F₂ : Factor D₂ D') (he : F₁.o.onB.act F₁.e = F₂.o.onB.act F₂.e)
    (hf : F₁.o.onB.act F₁.f = F₂.o.onB.act F₂.f) :
    (lift (fst D₂.P.A D₂.P.A ≫ F₂.inc ≫ F₁.pr) (snd D₂.P.A D₂.P.A ≫ F₂.inc ≫ F₁.pr) : G2 D₂.P.A ⟶ G2 D₁.P.A).left ≫
      (lift (fst D₁.P.A D₁.P.A ≫ F₁.inc) (snd D₁.P.A D₁.P.A ≫ F₁.inc ≫ F₁.o.onB.act F₁.f) : G2 D₁.P.A ⟶ G2 D'.P.A).left =
    (lift (fst D₂.P.A D₂.P.A ≫ F₂.inc) (snd D₂.P.A D₂.P.A ≫ F₂.inc ≫ F₂.o.onB.act F₂.f) : G2 D₂.P.A ⟶ G2 D'.P.A).left := by
  rw [← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc]
  simp only [Category.assoc]
  rw [reassoc_of% (inc_pr_inc F₁ F₂ he), inc_pr_inc F₁ F₂ he, hf]

theorem formEq_cancel {X Y Y' : Scheme.{0}} {K : Type} [Fintype K] (ε : K → ℤ) (A B : K → (Y ⟶ X)) (A₁ B₁ : K → (Y' ⟶ X))
    (h : Y ⟶ Y') (hA : ∀ k, h ≫ A₁ k = A k) :
    FormEq (Sum.elim (Sum.elim A B) (fun k => h ≫ Sum.elim A₁ B₁ k))
      (Sum.elim (Sum.elim ε (fun k => - ε k)) (fun k => - Sum.elim ε (fun k => - ε k) k))
      (Sum.elim (fun k => h ≫ B₁ k) B) (Sum.elim ε (fun k => - ε k)) := by
  intro U _ g
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, hA, neg_neg, zpow_neg, Finset.prod_inv_distrib]
  generalize ∏ a₁, g (A a₁) ^ ε a₁ = a
  generalize ∏ x, g (B x) ^ ε x = b
  generalize ∏ x, g (h ≫ B₁ x) ^ ε x = c
  rw [mul_inv, inv_inv, _root_.mul_comm a, _root_.mul_assoc, mul_inv_cancel_left, _root_.mul_comm]

theorem samePol_of_two_factors : ∀ (R : Type) [CommRing R] [IsDomain R] (D₁ D₂ D' : DegPre R), D₁.TauBimult → ∀ (F₁ : Factor D₁ D') (F₂ : Factor D₂ D'), F₁.o.onB.act F₁.e = F₂.o.onB.act F₂.e → F₁.o.onB.act F₁.f = F₂.o.onB.act F₂.f → (∀ z : D'.X, F₁.e • z = F₂.e • z) → (∀ z : D'.X, F₁.f • z = F₂.f • z) → SamePol D₁ D₂ := by
  intro R _ _ D₁ D₂ D' hB F₁ F₂ he hf hXe hXf
  haveI := F₂.inc_hom
  haveI := F₁.pr_hom
  let eI : D₂.P.A ≅ D₁.P.A := ⟨F₂.inc ≫ F₁.pr, F₁.inc ≫ F₂.pr, comp_inv F₁ F₂ he, inv_comp F₁ F₂ he⟩
  haveI : IsMonHom eI.hom := inferInstanceAs (IsMonHom (F₂.inc ≫ F₁.pr))
  have hs : spMap (RingHom.id R) = 𝟙 (Sp R) := Spec.map_id _
  refine ⟨GlobalTheory.PolDeg.Wit.ofDeg D₁ hB, AddEquiv.refl _, xEquiv F₁ F₂ hXe, GlobalTheory.PolDeg.Wit.refines_ofDeg D₁ hB, ?_⟩
  let β₂ := (lift (fst D₂.P.A D₂.P.A ≫ F₂.inc ≫ F₁.pr) (snd D₂.P.A D₂.P.A ≫ F₂.inc ≫ F₁.pr) : G2 D₂.P.A ⟶ G2 D₁.P.A).left
  have hsq : IsSquare (F₂.inc ≫ F₁.pr).left β₂ := by
    constructor
    · rw [← Over.comp_left, lift_fst, Over.comp_left]
    · rw [← Over.comp_left, lift_snd, Over.comp_left]

  haveI : Nonempty (D₁.P.A.left ⨿ D₂.P.A.left : Scheme.{0}) :=
    ⟨(coprod.inl : D₁.P.A.left ⟶ _) (Classical.arbitrary _)⟩
  have hL₁ := D₁.P.isLB
  have hL₂ := D₂.P.isLB
  have hL' := D'.P.isLB
  have h₁₂ := join_isLB hL₁ hL₂
  have hN := join_isLB h₁₂ hL'
  have P₁ : IsPart (join (join D₁.P.L D₂.P.L) D'.P.L) D₁.P.L (coprod.inl ≫ coprod.inl) (Prod.fst ∘ Prod.fst) :=
    (isPart_inl _ _).trans (isPart_inl _ _)
  have P₂ : IsPart (join (join D₁.P.L D₂.P.L) D'.P.L) D₂.P.L (coprod.inr ≫ coprod.inl) (Prod.snd ∘ Prod.fst) :=
    (isPart_inl _ _).trans (isPart_inr _ _)
  have P' : IsPart (join (join D₁.P.L D₂.P.L) D'.P.L) D'.P.L coprod.inr Prod.snd := isPart_inr _ _
  have sπ₁ : Function.Surjective (Prod.fst ∘ Prod.fst : (join (join D₁.P.L D₂.P.L) D'.P.L).ι → D₁.P.L.ι) :=
    (fst_surjective hL₂).comp (fst_surjective hL')
  have sπ₂ : Function.Surjective (Prod.snd ∘ Prod.fst : (join (join D₁.P.L D₂.P.L) D'.P.L).ι → D₂.P.L.ι) :=
    (snd_surjective hL₁).comp (fst_surjective hL')
  obtain ⟨t₂, ht₂, vt₂⟩ := exists_gen_of_iso P' P₂ F₂.w F₂.w_gen
  obtain ⟨t₁, ht₁, vt₁⟩ := exists_gen_of_iso P' P₁ F₁.w F₁.w_gen
  have hℓ := lift_comp F₁ F₂ he hf
  let t := LB.mulGen _ _ _ _ _ t₂ (LB.invGen _ _ _ (LB.pullGen _ _ _ t₁ β₂))
  have ht : t.IsGen := LB.isGen_mulGen _ _ _ _ _ _ _ ht₂ (LB.isGen_invGen _ _ _ _ (LB.isGen_pullGen _ _ _ _ ht₁ _))
  obtain ⟨t', ht', vt'⟩ := exists_gen hN (formEq_cancel _ _ _ _ _ β₂ (fun k => by rw [← Category.assoc, hℓ])) t ht
  obtain ⟨w, hw, vw⟩ := exists_iso_of_gen P₁ P₂ hL₁ hL₂ sπ₁ sπ₂ t' ht'
  refine ⟨(F₂.inc ≫ F₁.pr).left, β₂, w, (isGrpPullback_of_iso eI).congr hs.symm rfl, hsq, hw, fun a => ?_, ?_⟩
  · show (D₂.c a).left ≫ (F₂.inc ≫ F₁.pr).left = spMap (RingHom.id R) ≫ (D₁.c (F₁.xp (F₂.xi a))).left
    rw [hs, Category.id_comp, ← Over.comp_left, c_comp F₁ F₂ hXe]
  intro κ hκ a b z J J' hJ hJ'
  obtain rfl : κ = 𝟙 _ := by
    rw [hs, Category.comp_id] at hκ
    have : Mono (jK R) := GlobalTheory.PolDeg.Wit.mono_jK
    exact (cancel_mono (jK R)).1 (hκ.trans (Category.id_comp _).symm)
  obtain ⟨J₁₂, hJ₁₂, e₁, e₂⟩ := exists_good_join hL₁ hL₂ hJ hJ'
  choose I hI using fun χ : (TK R).left ⟶ D'.P.A.left => exists_chart hL' (χ z)
  obtain ⟨JN, hJN, e₃, e₄⟩ := exists_good_join h₁₂ hL' hJ₁₂ (J₂ := I) hI
  have r₁ : GlobalTheory.Mum.Two.rs (coprod.inl ≫ coprod.inl) (Prod.fst ∘ Prod.fst) JN = J := by
    rw [← e₁, ← e₃]; funext ψ; simp only [GlobalTheory.Mum.Two.rs, GlobalTheory.Mum.Two.rl, GlobalTheory.Mum.Two.rr, Function.comp, Category.assoc]
  have r₂ : GlobalTheory.Mum.Two.rs (coprod.inr ≫ coprod.inl) (Prod.snd ∘ Prod.fst) JN = J' := by
    rw [← e₂, ← e₃]; funext ψ; simp only [GlobalTheory.Mum.Two.rs, GlobalTheory.Mum.Two.rl, GlobalTheory.Mum.Two.rr, Function.comp, Category.assoc]
  have r₃ : GlobalTheory.Mum.Two.rs coprod.inr Prod.snd JN = I := e₄
  have hp : (lift (toUnit (TK R) ≫ D₂.c a) (toUnit (TK R) ≫ D₂.c b)).left ≫ β₂ =
      (lift (toUnit (TK R) ≫ D₁.c (F₁.xp (F₂.xi a))) (toUnit (TK R) ≫ D₁.c (F₁.xp (F₂.xi b)))).left := by
    simp only [β₂]
    rw [← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc, Category.assoc, Category.assoc,
      c_comp F₁ F₂ hXe, c_comp F₁ F₂ hXe]
  have v := vw _ (lift (toUnit (TK R) ≫ D₂.c a) (toUnit (TK R) ≫ D₂.c b)).left z JN hJN
  rw [vt' _ _ z JN hJN] at v
  have hv : val t (lift (toUnit (TK R) ≫ D₂.c a) (toUnit (TK R) ≫ D₂.c b)).left z JN =
      val t₂ (lift (toUnit (TK R) ≫ D₂.c a) (toUnit (TK R) ≫ D₂.c b)).left z JN *
        (val t₁ ((lift (toUnit (TK R) ≫ D₂.c a) (toUnit (TK R) ≫ D₂.c b)).left ≫ β₂) z JN)⁻¹ := by
    rw [val_mul hJN, val_inv, val_pull hJN]
  rw [hv, vt₂ _ _ z JN hJN, vt₁ _ _ z JN hJN, r₁, r₂, r₃, hp] at v
  have hF₂ := F₂.tau a b z I J' hI hJ'
  have hF₁ := F₁.tau (F₁.xp (F₂.xi a)) (F₁.xp (F₂.xi b)) z I J hI hJ
  rw [xi_xp_xi F₁ F₂ hXe, xi_xp_xi F₁ F₂ hXe, hXf] at hF₁
  have hQ := (GlobalTheory.PolDeg.Wit.exists_tau D₁ (F₁.xp (F₂.xi a)) (F₁.xp (F₂.xi b))).choose_spec.2 _ (𝟙 _) z J hJ
  change GlobalTheory.PolDeg.lamVal w _ z J J' = GlobalTheory.PolDeg.lamVal F₂.w _ z I J' * (GlobalTheory.PolDeg.lamVal F₁.w _ z I J)⁻¹ at v
  rw [hF₂]
  refine Eq.trans ?_ (congrArg₂ (· * ·) v.symm hQ.symm)
  rw [hF₁, _root_.mul_assoc, inv_mul_cancel_left]

end GlobalTheory.Mum.TwoFac
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SamePolarisedOfTwoIdempotentFactorsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.samePolarised_of_two_idempotentFactors : ∀ (R : Type) [CommRing R] [IsDomain R] (D₁ D₂ D' : DegPre R), D₁.TauBimult → ∀ (F₁ : Factor D₁ D') (F₂ : Factor D₂ D'), F₁.o.onB.act F₁.e = F₂.o.onB.act F₂.e → F₁.o.onB.act F₁.f = F₂.o.onB.act F₂.f → (∀ z : D'.X, F₁.e • z = F₂.e • z) → (∀ z : D'.X, F₁.f • z = F₂.f • z) → SamePol D₁ D₂ := by
  first | exact @GlobalTheory.Mum.TwoFac.samePol_of_two_factors | exact GlobalTheory.Mum.TwoFac.samePol_of_two_factors | (intros; apply GlobalTheory.Mum.TwoFac.samePol_of_two_factors <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SamePolarisedDataOfIdempotentFactorUniformisatio
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.FactorPol

open GlobalTheory.CechPic GlobalTheory.ZH.EndoExtend GlobalTheory.Mum.Two GlobalTheory.UT

theorem lbIso_star : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (oA : A.OAct O) (oG : RingAct G O), U.toUnifPre.OLinear O o oA oG → ∀ a : O, LBIso (cubeLB G ![fst G G ≫ oG.act a, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ oG.act (star a)] U.LG.L) := by
  intro R _ _ _ hR D A G _ _ hG U O _ _ _ o oA oG hlin a
  obtain ⟨hno, -, hic, -⟩ := hR
  have hS : IsSemiAbelian G := hG
  have := hS.smooth
  have := hS.geomConnected
  have := geometricallyIntegral_of_smooth G.hom
  have := smooth_tensorObj_hom G G
  have := geometricallyIntegral_tensorObj_hom G G
  have ha := oG.hom a
  have hsa := oG.hom (star a)
  have hgen := U.gen_hom
  have hL := U.LG.isLB
  have hA := A.isLB
  have h₁ : IsPreimmersion (jK R) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have h₂ : Flat (jK R) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat _ (nonZeroDivisors R))
  have h₃ : IsDominant (jK R) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))).le.trans bot_le)⟩
  have hn : Geo.Tor.IsNormalScheme (Sp R) := (GlobalTheory.isNormalScheme_iff_pred _).1 inferInstance
  have h0 : CechPic.pull (eSec G) (cls U.LG.L hL) = 0 :=
    (cls_eq_zero_iff (pull_isLB hL _)).2 ⟨U.LG.rig, U.LG.rigGen⟩

  have eA : cubeCls A.A ![fst A.A A.A ≫ oA.act a, snd A.A A.A] (cls A.L hA) =
      cubeCls A.A ![fst A.A A.A, snd A.A A.A ≫ oA.act (star a)] (cls A.L hA) :=
    (cls_cubeLB A.A _ hA).symm.trans (((cls_eq_iff (LB.isLB_linComb hA _ _) (LB.isLB_linComb hA _ _)).2
      (GlobalTheory.FullPoint.lbIso_of_rosatiAdj hA (oA.rosati a))).trans (cls_cubeLB A.A _ hA))
  have hc' : CechPic.pull (pullback.fst G.hom (jK R)) (cls U.LG.L hL) =
      CechPic.pull U.gen.hom.left (cls A.L hA) := by
    obtain ⟨w, hw⟩ := U.ext
    rw [← cls_pull hL _ (pull_isLB hL _), ← cls_pull hA _ (pull_isLB hA _)]
    exact ((cls_eq_iff _ _).2 ⟨w, hw⟩).symm

  have hgK : cubeCls ((Over.pullback (jK R)).obj G)
        ![fst ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G) ≫ (Over.pullback (jK R)).map (oG.act a),
          snd ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G)]
        (CechPic.pull (pullback.fst G.hom (jK R)) (cls U.LG.L hL)) =
      cubeCls ((Over.pullback (jK R)).obj G)
        ![fst ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G),
          snd ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G) ≫ (Over.pullback (jK R)).map (oG.act (star a))]
        (CechPic.pull (pullback.fst G.hom (jK R)) (cls U.LG.L hL)) := by
    rw [hc']
    let u := lift (fst ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G) ≫ U.gen.hom)
      (snd ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G) ≫ U.gen.hom)
    have hu : u.left ≫ (A.A ⊗ A.A).hom = ((Over.pullback (jK R)).obj G ⊗ (Over.pullback (jK R)).obj G).hom ≫ 𝟙 _ := by
      rw [Category.comp_id]; exact Over.w u
    have e₁ := hlin.ext a
    have e₂ := hlin.ext (star a)
    rw [← push_cubeCls (isGrpPullback_of_iso U.gen) _ ![fst A.A A.A ≫ oA.act a, snd A.A A.A] u.left hu (fun i => ?_),
      ← push_cubeCls (isGrpPullback_of_iso U.gen) _ ![fst A.A A.A, snd A.A A.A ≫ oA.act (star a)] u.left hu
        (fun i => ?_), eA]
    · fin_cases i
      · show (fst _ _ ≫ U.gen.hom).left = (u ≫ fst A.A A.A).left
        congr 1; simp [u]
      · show ((snd _ _ ≫ (Over.pullback (jK R)).map (oG.act (star a))) ≫ U.gen.hom).left = (u ≫ snd A.A A.A ≫ oA.act (star a)).left
        congr 1; simp [u, e₂]
    · fin_cases i
      · show ((fst _ _ ≫ (Over.pullback (jK R)).map (oG.act a)) ≫ U.gen.hom).left = (u ≫ fst A.A A.A ≫ oA.act a).left
        congr 1; simp [u, e₁]
      · show (snd _ _ ≫ U.gen.hom).left = (u ≫ snd A.A A.A).left
        congr 1; simp [u]
  refine (cls_eq_iff (LB.isLB_linComb hL _ _) (LB.isLB_linComb hL _ _)).1
    ((cls_cubeLB G _ hL).trans (Eq.trans ?_ (cls_cubeLB G _ hL).symm))
  refine pic_ext (jK R) hn (G ⊗ G) (lift η[G] η[G]).left (Over.w _) ?_ ?_
  · refine (pull_cubeCls G _ (fun _ => η[G]) (lift η[G] η[G]) (fun i => ?_) _).trans
      (pull_cubeCls G _ (fun _ => η[G]) (lift η[G] η[G]) (fun i => ?_) _).symm <;>
    fin_cases i <;> simp
  · have hGp := isGrpPullback_pullback G (jK R)
    have Aw : ∀ {Y Z : Over (Sp R)} (q : Y ⟶ Z),
        ((Over.pullback (jK R)).map q).left ≫ pullback.fst Z.hom (jK R) = pullback.fst Y.hom (jK R) ≫ q.left :=
      fun q => pullback.lift_fst _ _ _
    let δ := lift ((Over.pullback (jK R)).map (fst G G)) ((Over.pullback (jK R)).map (snd G G))
    have e := congrArg (CechPic.pull δ.left) hgK
    have e' := fun x : Fin 2 → (G ⊗ G ⟶ G) => push_cubeCls hGp (T' := (Over.pullback (jK R)).obj (G ⊗ G)) (T := G ⊗ G)
      (fun i => (Over.pullback (jK R)).map (x i)) x (pullback.fst (G ⊗ G).hom (jK R)) pullback.condition
      (fun i => Aw _) (cls U.LG.L hL)
    rw [pull_cubeCls _ _ (fun i => (Over.pullback (jK R)).map (![fst G G ≫ oG.act a, snd G G] i)) δ
        (fun i => by fin_cases i <;> simp [δ]),
      pull_cubeCls _ _ (fun i => (Over.pullback (jK R)).map (![fst G G, snd G G ≫ oG.act (star a)] i)) δ
        (fun i => by fin_cases i <;> simp [δ])] at e
    exact (e' _).trans (e.trans (e' _).symm)

section Comp

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D₁ D₂ D₃ : DegData R I}
  {A₁ A₂ A₃ : PolAV (Sp (FractionRing R))} {G₁ G₂ G₃ : Over (Sp R)} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂]
  [IsCommMonObj G₂] [GrpObj G₃] [IsCommMonObj G₃] {U₁ : UnifPre I D₁ A₁ G₁} {U₂ : UnifPre I D₂ A₂ G₂}
  {U₃ : UnifPre I D₃ A₃ G₃} {a : G₁ ⟶ G₂} {a' : G₂ ⟶ G₃}

theorem over_comp {b : D₁.toPre.P.A ⟶ D₂.toPre.P.A} {b' : D₂.toPre.P.A ⟶ D₃.toPre.P.A} (h : Over₀ U₁ U₂ a b)
    (h' : Over₀ U₂ U₃ a' b') : Over₀ U₁ U₃ (a ≫ a') (b ≫ b') := fun e => by
  rw [Functor.map_comp, Functor.map_comp, Category.assoc, h' e, ← Category.assoc, h e, Category.assoc]

theorem over_id : Over₀ U₁ U₁ (𝟙 _) (𝟙 _) := fun e => by
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

theorem onTorus_comp {h : D₂.toPre.X → D₁.toPre.X} {h' : D₃.toPre.X → D₂.toPre.X} (H : OnTorus U₁ U₂ a h)
    (H' : OnTorus U₂ U₃ a' h') : OnTorus U₁ U₃ (a ≫ a') (h ∘ h') := fun e => by
  obtain ⟨t, ht, et⟩ := H e
  obtain ⟨t', ht', et'⟩ := H' e
  refine ⟨t ≫ t', fun χ => unit_ext fun z _ => ?_, by
    rw [Functor.map_comp, ← Category.assoc, et, Category.assoc, et', Category.assoc]⟩
  have e₁ := congrArg (gm (𝟙 _) z ⊤) (ht (h' χ))
  have e₂ := congrArg (gm (𝟙 _ ≫ t.left) z ⊤) (ht' χ)
  refine Eq.trans ?_ e₁
  refine ((gm_res (𝟙 _) z (V := ⊤) _ trivial _).trans (gm_pull (𝟙 _) (t ≫ t').left z ⊤ trivial _)).trans
    (Eq.trans ?_ ((gm_res (𝟙 _) z (V := ⊤) _ trivial _).trans (gm_pull (𝟙 _) t.left z ⊤ trivial _)).symm)
  refine Eq.trans ?_ e₂
  refine Eq.trans ?_ ((gm_res _ z (V := ⊤) _ trivial _).trans (gm_pull (𝟙 _ ≫ t.left) t'.left z ⊤ trivial _)).symm
  rw [Over.comp_left, Category.assoc]

theorem onTorus_id : OnTorus U₁ U₁ (𝟙 _) id := fun e =>
  ⟨𝟙 _, fun χ => unit_ext fun z _ => ((gm_res (𝟙 _) z (V := ⊤) _ trivial _).trans
    (gm_pull (𝟙 _) (𝟙 _) z ⊤ trivial _)).trans (by rw [Category.comp_id]; rfl), by
    rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]⟩

end Comp

theorem lbIso_proj {S : Scheme.{0}} {G G' : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
    {L : LB G.left} {L' : LB G'.left} (hL : L.IsLB) (hL' : L'.IsLB) (inc : G ⟶ G') (pr : G' ⟶ G) (f g g' : G' ⟶ G')
    (hg : pr ≫ inc ≫ f = g)
    (H : LBIso (abelian₂ G L) ((abelian₂ G' L').pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ f) : G2 G ⟶ G2 G').left))
    (adj : LBIso (cubeLB G' ![fst G' G' ≫ g', snd G' G'] L') (cubeLB G' ![fst G' G', snd G' G' ≫ g] L')) :
    LBIso (cubeLB G ![fst G' G' ≫ pr, snd G' G' ≫ pr] L)
      (cubeLB G' ![fst G' G' ≫ (pr ≫ inc) ≫ g', snd G' G' ≫ 𝟙 G'] L') := by
  have hΛ' : (abelian₂ G' L').IsLB := LB.isLB_linComb hL' _ _
  have e₁ : cubeCls G (x2 G) (cls L hL) = CechPic.pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ f) : G2 G ⟶ G2 G').left
      (cubeCls G' (x2 G') (cls L' hL')) :=
    (cls_cubeLB G _ hL).symm.trans (((cls_eq_iff _ (pull_isLB hΛ' _)).2 H).trans
      ((cls_pull hΛ' _ _).trans (congrArg _ (cls_cubeLB G' _ hL'))))
  have e₂ := (cls_cubeLB G' _ hL').symm.trans (((cls_eq_iff (LB.isLB_linComb hL' _ _) (LB.isLB_linComb hL' _ _)).2 adj).trans
    (cls_cubeLB G' _ hL'))
  rw [pull_cubeCls G' _ ![fst G G ≫ inc, snd G G ≫ inc ≫ f] _ (fun i => by fin_cases i <;> simp [x2])] at e₁
  have e₃ := congrArg (CechPic.pull (lift (fst G' G' ≫ pr) (snd G' G' ≫ pr) : G' ⊗ G' ⟶ G ⊗ G).left) e₁
  have e₄ := congrArg (CechPic.pull (lift (fst G' G' ≫ pr ≫ inc) (snd G' G') : G' ⊗ G' ⟶ G' ⊗ G').left) e₂
  rw [pull_cubeCls G _ ![fst G' G' ≫ pr, snd G' G' ≫ pr] _ (fun i => by fin_cases i <;> simp [x2]),
    pull_cubeCls G' _ ![fst G' G' ≫ pr ≫ inc, snd G' G' ≫ g] _ (fun i => by fin_cases i <;> simp [← hg])] at e₃
  rw [pull_cubeCls G' _ ![fst G' G' ≫ (pr ≫ inc) ≫ g', snd G' G' ≫ 𝟙 G'] _ (fun i => by fin_cases i <;> simp),
    pull_cubeCls G' _ ![fst G' G' ≫ pr ≫ inc, snd G' G' ≫ g] _ (fun i => by fin_cases i <;> simp)] at e₄
  exact (cls_eq_iff (LB.isLB_linComb hL _ _) (LB.isLB_linComb hL' _ _)).1
    ((cls_cubeLB G _ hL).trans (e₃.trans (e₄.symm.trans (cls_cubeLB G' _ hL').symm)))


set_option maxHeartbeats 1000000 in
theorem samePol_of_unif_factor : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∀ (D₀ : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D₀ A G), LBIso (abelian₂ G U.LG.L) ((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left) → SamePol D.toPre D₀.toPre := by
  intro R _ _ _ hR D D' F A' G' _ _ hG' U' oA oG lin G _ _ hG inc pr hinc hpr ip pi D₀ A U H
  have := hR.2
  have hA := hR.1
  have := U.gen_hom
  have := U'.gen_hom
  obtain ⟨prB, hprB, qpr⟩ := GlobalTheory.T.exists_abelianPart_hom_uniformisedGroups R _ hA D' D₀ A' A G' G U'.toUnifPre U.toUnifPre pr hpr
  obtain ⟨incB, hincB, qinc⟩ := GlobalTheory.T.exists_abelianPart_hom_uniformisedGroups R _ hA D₀ D' A A' G G' U.toUnifPre U'.toUnifPre inc hinc
  obtain ⟨h, th⟩ := GlobalTheory.T.uniformisedGroupHom_characterMap_constant R _ hA D' D₀ A' A G' G U'.toUnifPre U.toUnifPre pr hpr
  obtain ⟨k, tk⟩ := GlobalTheory.T.uniformisedGroupHom_characterMap_constant R _ hA D₀ D' A A' G G' U.toUnifPre U'.toUnifPre inc hinc
  have un := GlobalTheory.T.uniformisedGroupHom_induced_maps_unique R _ hA D₀ D₀ A A G G U.toUnifPre U.toUnifPre
  have un' := GlobalTheory.T.uniformisedGroupHom_induced_maps_unique R _ hA D' D' A' A' G' G' U'.toUnifPre U'.toUnifPre
  have ql : ∀ x, Over₀ U'.toUnifPre U'.toUnifPre (oG.act x) (F.o.onB.act x) := fun x e => lin.q_lin e x
  have il : ∀ x, OnTorus U'.toUnifPre U'.toUnifPre (oG.act x) (fun χ => star x • χ) := fun x e => lin.i_lin e x
  have ipB : incB ≫ prB = 𝟙 _ := (un _).1 _ _ (ip ▸ over_comp qinc qpr) over_id
  have piB : prB ≫ incB = F.o.onB.act F.e := (un' _).1 _ _ (pi ▸ over_comp qpr qinc) (ql _)
  have kh : ∀ χ, k (h χ) = χ := congrFun ((un _).2 _ _ (ip ▸ onTorus_comp tk th) onTorus_id)
  have hk : ∀ χ, h (k χ) = star F.e • χ := congrFun ((un' _).2 _ _ (pi ▸ onTorus_comp th tk) (il _))
  have hinj : Function.Injective h := Function.LeftInverse.injective kh
  have L : Lin U'.toUnifPre U.toUnifPre pr prB h := ⟨hpr, hprB, qpr, th⟩
  have C := GlobalTheory.T.torusCoordinates_compare_normalisedGenerators R _ hA D' D₀ A' A G' G U'.toUnifPre U.toUnifPre pr prB h L
  obtain ⟨c, hc, gc⟩ : ∃ c : A'.A ⟶ A.A, IsMonHom c ∧ Gen₀ U'.toUnifPre U.toUnifPre pr c :=
    ⟨U'.gen.inv ≫ (Over.pullback (jK R)).map pr ≫ U.gen.hom, inferInstance, by simp [Gen₀]⟩
  have adj := lbIso_star R hA D' A' G' hG' U' F.O F.o oA oG lin
  have ex := fun x => (functorial_of_unif R _ hA D' A' G' hG' U').1 (oG.act x) (oA.act x) (oG.hom x) (oA.hom x) (lin.ext x)
  obtain ⟨E, eG, eA⟩ := ex (star (F.f * F.e) * F.e)
  obtain ⟨E', eG', -⟩ := ex (star (star (F.f * F.e) * F.e))
  have eh : ∀ y, E.h y = star F.e • F.f • F.e • y := fun y =>
    (congrFun ((un' _).2 _ _ (eG ▸ (lin_of_endU E).1.2.2.2) (il _)) y).trans (by
      rw [star_mul, star_star, mul_smul, mul_smul])
  have H₁ := lbIso_proj U.LG.isLB U'.LG.isLB inc pr (oG.act F.f) (oG.act (star (star (F.f * F.e))))
    (oG.act (star (F.f * F.e))) (by rw [star_star, oG.map_mul, ← pi, Category.assoc]) H (adj _)
  rw [pi, ← oG.map_mul, ← eG] at H₁
  have H₂ := GlobalTheory.T.cubeBundleIso_uniformisedGroup_genericFibre R _ D' D₀ A' A G' G U'.toUnifPre U.toUnifPre pr pr E.aG (𝟙 _) c c E.aA (𝟙 _) gc gc E.ext
    (by simp [Gen₀]) H₁
  obtain ⟨Ω, _, _, _, K⟩ := GlobalTheory.T.exists_algClosedField_torsionMaps_commute_hom R _ hA D' D₀ A' A G' G hG' hG U' U pr c prB h hc gc L C hinj
  obtain ⟨φ, hφ, hhφ⟩ := GlobalTheory.T.semiAbelianHom_torsionCompatible_periods_lattices R _ hA D' D₀ A' A G' G hG' hG U' U pr c prB h hc gc L C E E'
    (by rw [eG, eG']; exact adj _) H₂ Ω K
  have := oG.hom F.f
  have := F.o.onB.hom F.f
  have H₃ := GlobalTheory.T.mumfordBundle_iso_along_homs_descends_abelianPart R hA D₀ D' A A' G G' hG hG' U U' inc (inc ≫ oG.act F.f) incB (incB ≫ F.o.onB.act F.f) hinc
    inferInstance hincB inferInstance qinc (over_comp qinc (ql _)) H
  have hφ' : ∀ y, h (φ y) = star F.e • F.f • F.e • y := fun y => (hhφ y).trans (eh y)
  obtain ⟨cφ, w, hw, ht⟩ := GlobalTheory.T.factor_periods_projection_period_points R D₀.toPre D'.toPre D'.tau_bimult F.O F.o F.e F.f incB prB h φ hincB hprB piB
    (fun χ => (C χ).imp fun _ => And.left) H₃ Ω hφ hφ'
  have ex : ∀ y, F.e • F.xi y = F.xi y := fun y => by rw [← F.xi_xp, F.xp_xi]
  let ε : D.toPre.X ≃+ D₀.toPre.X := AddEquiv.ofBijective (φ.comp F.xi) ⟨fun y y' e => F.inj (by
      have := congrArg h e
      simpa only [AddMonoidHom.comp_apply, hφ', ex] using this), fun χ => by
    obtain ⟨y, hy⟩ := F.onto (h χ)
    exact ⟨y, hinj (by rw [AddMonoidHom.comp_apply, hφ', ex, ← hy, ← hk, kh])⟩⟩
  have hε : ∀ χ, φ (F.xi (ε.symm χ)) = χ := ε.apply_symm_apply
  let F₀ : Factor D₀.toPre D'.toPre :=
    { O := F.O, o := F.o, e := F.e, f := F.f, inc := incB, pr := prB, xi := F.xi.comp ε.symm.toAddMonoidHom, xp := φ, w := w
      idem := F.idem, inc_hom := hincB, pr_hom := hprB, inc_pr := ipB, pr_inc := piB, xp_xi := hε
      xi_xp := fun z => by
        have : φ z = ε (F.xp z) := hinj (by
          show _ = h (φ (F.xi (F.xp z)))
          rw [hφ', hφ', F.xi_xp, ← mul_smul F.e F.e, F.idem])
        show F.xi (ε.symm (φ z)) = _
        rw [this, ε.symm_apply_apply, F.xi_xp]
      c_xi := fun χ => by
        show D'.toPre.c (F.xi (ε.symm χ)) = _
        conv_rhs => rw [← hε χ, cφ, Category.assoc, piB, ← F.o.c_lin, ex]
      inj := F.inj.comp ε.symm.injective
      onto := fun z => (F.onto z).elim fun y hy => ⟨ε y, by
        show _ = star F.e • F.f • F.xi (ε.symm (ε y))
        rw [ε.symm_apply_apply, hy]⟩
      w_gen := hw
      tau := fun a b z J J' hJ hJ' => by
        have := ht (F.xi (ε.symm a)) (F.xi (ε.symm b)) z J J' hJ hJ'
        rw [hε, hε, ex, ex] at this
        exact this }
  exact GlobalTheory.T.samePolarised_of_two_idempotentFactors R D.toPre D₀.toPre D'.toPre D.tau_bimult F F₀ rfl rfl (fun _ => rfl) (fun _ => rfl)

end GlobalTheory.Mum.FactorPol
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SamePolarisedDataOfIdempotentFactorUniformisatioStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.samePolarisedData_of_idempotentFactor_uniformisation : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∀ (D₀ : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D₀ A G), LBIso (abelian₂ G U.LG.L) ((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left) → SamePol D.toPre D₀.toPre := by
  first | exact @GlobalTheory.Mum.FactorPol.samePol_of_unif_factor | exact GlobalTheory.Mum.FactorPol.samePol_of_unif_factor | (intros; apply GlobalTheory.Mum.FactorPol.samePol_of_unif_factor <;> assumption)
end
