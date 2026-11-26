module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianEndomorphismUniqueOverDegenerationDat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoOfGenericNormalLocalBase
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.DualAbelianSchemes.TrivLocusFlat

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdjointEndomorphismUniformisedGroup
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdjointEndomorphismUniformisedGroup
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.GroupAdjoint

open GlobalTheory.CechPic GlobalTheory.AbDual

theorem exists_adjoint {K : Type} [CommRing K] (Q : PolAV (Sp K)) (f : Q.A ⟶ Q.A) [IsMonHom f] :
    ∃ x : Q.A ⟶ Q.A, IsMonHom x ∧ ∀ (Y : Over (Sp K)) (a b : Y ⟶ Q.A),
      lam (cls Q.L Q.isLB) (a ≫ f) b = lam (cls Q.L Q.isLB) a (b ≫ x) := by
  have := Q.isAb.comm
  have hd : IsDual Q.A Q.A (abelian₂ Q.A Q.L) := CompanionTheory.PfDual.kTrivDual K Q.A Q.g Q.isAb Q.smoothDim Q.L Q.isLB Q.ktriv
  have hΛ : (abelian₂ Q.A Q.L).IsLB := hd.isLB
  have e : ∀ (Y : Over (Sp K)) (a b : Y ⟶ Q.A), evc hΛ a b = lam (cls Q.L Q.isLB) a b := fun Y a b ↦ by
    rw [evc, show cls _ hΛ = lam (cls Q.L Q.isLB) (fst Q.A Q.A) (snd Q.A Q.A) from
      cls_cube_two Q.isLB _ _ hΛ, pull_lam, lift_fst, lift_snd]
  have l₁ : ∀ (Y : Over (Sp K)) (a a' b : Y ⟶ Q.A), evc hΛ (a * a') b = evc hΛ a b + evc hΛ a' b :=
    (isAdditive_iff hΛ).1 hd.additive
  have l₂ : ∀ (Y : Over (Sp K)) (a b b' : Y ⟶ Q.A), evc hΛ a (b * b') = evc hΛ a b + evc hΛ a b' := fun Y a b b' ↦ by
    rw [e, e, e, lam_comm, lam_comm _ a b, lam_comm _ a b', ← e, ← e, ← e]
    exact l₁ _ _ _ _
  have a₂ : IsAdditive (swap (abelian₂ Q.A Q.L)) := (BirigidLift.isAdditive_swap_iff hΛ).2 l₂
  have hM := pull_isLB hΛ (lift (fst Q.A Q.A ≫ f) (snd Q.A Q.A)).left
  have m : ∀ (Y : Over (Sp K)) (a b : Y ⟶ Q.A), evc hM a b = evc hΛ (a ≫ f) b := fun Y a b ↦ by
    rw [evc_ev hΛ]
    simp only [lift_fst_assoc, lift_snd]
  obtain ⟨x, hx, ex⟩ := BirigidLift.exists_hom hd a₂ hM
    ((isAdditive_iff hM).2 fun Y u u' t ↦ by rw [m, m, m, MonObj.mul_comp, l₁])
    ((BirigidLift.isAdditive_swap_iff hM).2 fun Y u t t' ↦ by rw [m, m, m, l₂])
  refine ⟨x, hx, fun Y a b ↦ ?_⟩
  rw [← e, ← e, ← m]
  exact BirigidLift.evc_of_cls hd.isLB hM ex a b

theorem exists_adjoint_on_group : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ g : G ⟶ G, IsMonHom g → ∃ g' : G ⟶ G, IsMonHom g' ∧ LBIso (cubeLB G ![fst G G ≫ g, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ g'] U.LG.L) := by
  intro R _ _ _ hR D A G _ _ hG U g hg
  have hN : IsNoetherianRing R := hR.1.1
  have hI : IsIntegrallyClosed R := hR.1.2.2.1
  have := U.gen_hom
  have hL := U.LG.isLB
  have hp := isGrpPullback_pullback G (jK R)
  obtain ⟨x, hx, ex⟩ := exists_adjoint A (U.gen.inv ≫ (Over.pullback (jK R)).map g ≫ U.gen.hom)
  have hj : GlobalTheory.IsGenericPointHom (S := Sp R) (jK R) := .fractionField R (FractionRing R)
  obtain ⟨g', ⟨hg', eg'⟩, -⟩ := GlobalTheory.semiAbelianHomExtension_holds.of_isGenericPointHom
    (GlobalTheory.Published.SemiAbelianHomExtension.isNormalScheme_spec R) hj hG hG (U.gen.hom ≫ x ≫ U.gen.inv)
  refine ⟨g', hg', ?_⟩
  have := hG.smooth
  have := hG.geomConnected
  have := GlobalTheory.smooth_tensorObj_hom G G
  have := GlobalTheory.geometricallyIntegral_tensorObj_hom G G
  have h₁ : (cubeLB G ![fst G G ≫ g, snd G G] U.LG.L).IsLB := LB.isLB_linComb hL _ _
  have h₂ : (cubeLB G ![fst G G, snd G G ≫ g'] U.LG.L).IsLB := LB.isLB_linComb hL _ _
  refine GlobalTheory.T.lineBundleIso_of_generic_normal_local_base R (G ⊗ G) (1 : 𝟙_ _ ⟶ G ⊗ G).left (Over.w _) _ _ h₁ h₂ ?_
  refine (cls_eq_iff (pull_isLB h₁ _) (pull_isLB h₂ _)).1 ?_

  have ec : pull U.gen.hom.left (cls A.L A.isLB) = pull (pullback.fst G.hom (jK R)) (cls U.LG.L hL) := by
    rw [← cls_pull A.isLB _ (pull_isLB A.isLB _), ← cls_pull hL _ (pull_isLB hL _)]
    exact (cls_eq_iff _ _).2 U.ext
  have key : ∀ a b : G ⊗ G ⟶ G, pull (pullback.fst (G ⊗ G).hom (jK R)) (lam (cls U.LG.L hL) a b) =
      lam (cls A.L A.isLB) ((Over.pullback (jK R)).map a ≫ U.gen.hom) ((Over.pullback (jK R)).map b ≫ U.gen.hom) := by
    intro a b
    rw [← lam_pull, ec, lam_pull_of_isGrpPullback hp]
    refine GlobalTheory.CompanionTheory.DualScheme.pull_lam_of_left (T' := Over.mk (_ ≫ jK R)) _ _ ?_ ?_
    · exact (ExtUnique.pullback_map_left_fst (jK R) a).symm
    · exact (ExtUnique.pullback_map_left_fst (jK R) b).symm
  rw [cls_pull h₁, cls_pull h₂, cls_cube_two hL, cls_cube_two hL, key, key, Functor.map_comp, Functor.map_comp, eg']
  have := ex _ ((Over.pullback (jK R)).map (fst G G) ≫ U.gen.hom) ((Over.pullback (jK R)).map (snd G G) ≫ U.gen.hom)
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id] using this

end GlobalTheory.Mum.GroupAdjoint
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdjointEndomorphismUniformisedGroupStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adjoint_endomorphism_uniformised_group : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ g : G ⟶ G, IsMonHom g → ∃ g' : G ⟶ G, IsMonHom g' ∧ LBIso (cubeLB G ![fst G G ≫ g, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ g'] U.LG.L) := by
  first | exact @GlobalTheory.Mum.GroupAdjoint.exists_adjoint_on_group | exact GlobalTheory.Mum.GroupAdjoint.exists_adjoint_on_group | (intros; apply GlobalTheory.Mum.GroupAdjoint.exists_adjoint_on_group <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointUniformisationEndomorphismLiesOverAdjoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationEndomorphismCarriesPeriodPointBala
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationEndomorphismCarriesPeriodPointBala
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.UT

noncomputable section

namespace GlobalTheory.Mum.KeepsIota

variable {R : Type} [CommRing R] [IsDomain R]

theorem exists_v (hG : GlobalFnsSt) (D : DegPre R) (f g : D.P.A ⟶ D.P.A) [IsMonHom f] [IsMonHom g]
    (k : D.X → D.X) (hk : ∀ χ, D.c (k χ) = D.c χ ≫ f)
    (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A f g) rosatiε)) (hu : u.IsGen)
    (u₀ : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (zero2 D.P.A)) (LB.oneGen D.P.L)) (χ : D.X) :
    ∃ v : LB.Gen (LB.LinComb D.P.L (Sum.elim (D.Oφ (𝟙 _) (k χ)) (D.Oφ g χ)) (Sum.elim Oε Oinvε)),
      Normd v ∧ ∀ (T : Over (Spec (CommRingCat.of R))) (x : T ⟶ D.P.A) (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) (J),
        Good D.P.L z J → val v (r ≫ x.left) z J = val u (r ≫ (lift (cP D T χ) x).left) z J := by
  have cf : ∀ T, cP D T (k χ) = cP D T χ ≫ f := fun T => by
    rw [cP, hk, ← Category.assoc]; rfl
  obtain ⟨v, hv, vv⟩ := exists_gen D.P.isLB
    (φ' := Sum.elim (D.Oφ (𝟙 _) (k χ)) (D.Oφ g χ)) (ε' := Sum.elim Oε Oinvε)
    (fun U _ h => by
      refine (prod_ros _ _ (cP D _ χ) (𝟙 D.P.A) h).trans (Eq.symm ?_)
      refine (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ (GlobalTheory.UT.OLinEnd.prod_Oφ D (𝟙 _) (k χ) h)
        (GlobalTheory.UT.OLinEnd.prod_Oφ_inv D g χ h)).trans ?_
      rw [cf, Category.id_comp]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
    (LB.pullGen D.P.L _ _ u (lift (cP D D.P.A χ) (𝟙 D.P.A)).left) (pullGen_isGen _ _ _ _ hu _)
  have key : ∀ (T : Over (Spec (CommRingCat.of R))) (x : T ⟶ D.P.A) (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) (J),
      Good D.P.L z J → val v (r ≫ x.left) z J = val u (r ≫ (lift (cP D T χ) x).left) z J := fun T x Z r z J hJ => by
    rw [vv Z _ z J hJ, val_pull hJ, Category.assoc, ← Over.comp_left, comp_lift, comp_cP, Category.comp_id]
  refine ⟨v, ⟨hv, corr_of_val D.P.isLB fun y J hJ => ?_⟩, key⟩
  have C : IsCub (cubV D.cub (T := 𝟙_ (Over (Spec (CommRingCat.of R)))) y J) := isCub_cubV D.cub hJ
  have e := (ros_add D.cub hG D.P.isAb _ _ u hu u₀ (T := 𝟙_ (Over (Spec (CommRingCat.of R)))) hJ 1 1 (cP D _ χ)).2
  rw [_root_.mul_one, MonObj.one_comp, C.face₃, C.face₃, _root_.mul_one, _root_.one_mul] at e
  have e' : val₂ u (T := 𝟙_ (Over (Spec (CommRingCat.of R)))) y J (cP D _ χ) 1 = 1 := mul_eq_left.1 e.symm
  have k' := key (𝟙_ (Over (Spec (CommRingCat.of R)))) 1 _ (𝟙 _) y J hJ
  have o : (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A).left = eSec D.P.A := by
    rw [Hom.one_def, toUnit_unit, Category.id_comp]; rfl
  rw [o] at k'
  refine (val_pull hJ _ _ _).trans (k'.trans (Eq.trans ?_ (val_one _).symm))
  rw [Category.id_comp]
  exact e'

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ E : EndU U.toUnifPre, E.aB = a → E.h = h' → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (y : D.toPre.X) (g g' : GtPtF D.toPre F), GtPtF.IsIota y g → E.Act g g' → GtPtF.IsIota (h y) g' := by
  intro R _ _ _ _ D A G _ _ _ U a a' h h' hd E hEa hEh F _ _ _ y g g' hg hact
  subst hEa hEh
  have hG : GlobalFnsSt := GlobalTheory.SemiRigid.globalFns
  have hs := (endData_symm_and_ofOAct R D.toPre).1 _ _ _ _ hd
  obtain ⟨ha, ha', -, hc, hc', -⟩ := hd
  obtain ⟨-, -, hr', -, -, hbal'⟩ := hs
  obtain ⟨u, hu, u₀⟩ := exists_ros hG D.toPre.P.isAb D.toPre.P.isLB _ _ hr'
  obtain ⟨gb, gv⟩ := (isIota_iff _ _).1 hg
  refine (isIota_iff _ _).2 ⟨?_, fun χ z J hJ => ?_⟩
  · rw [hact.1, gb, cP, cP, hc, ← Category.assoc]
  · obtain ⟨v, hv, vv⟩ := exists_v hG D.toPre a' E.aB E.h hc' u hu u₀ χ
    have k1 : val (E.u χ) g.b.left z J = val u (lift (cP D.toPre _ χ) g.b).left z J := by
      have := vv _ g.b _ (𝟙 _) z J hJ
      rw [Category.id_comp, Category.id_comp] at this
      exact (GlobalTheory.UT.SymFrame.normd_unique hG (E.u_norm χ) hv _ z J hJ).trans this
    rw [hact.2 χ z J hJ, gv _ z J hJ, k1, gb]
    let κ : TF (R := R) F ⟶ TK R := Over.homMk (𝟙 _ ≫ jFK (R := R) F) (by rw [Category.id_comp]; rfl)
    have e := (val_mul hJ _ _ _).symm.trans (val_corr hJ (hbal' u hu u₀ χ y) κ.left)
    have e' : val (LB.pullGen D.toPre.P.L _ _ u (D.toPre.pt2 χ y)) κ.left z J =
        val u (lift (cP D.toPre _ χ) (cP D.toPre _ y)).left z J := by
      rw [val_pull hJ, ← comp_cP D.toPre κ, ← comp_cP D.toPre κ y, ← comp_lift]; rfl
    rw [← e']
    exact (congrArg₂ (· * ·) (tau_symm (𝟙 (TF (R := R) F)) hJ _ _) rfl).trans
      (e.trans (tau_symm (𝟙 (TF (R := R) F)) hJ _ _))

end GlobalTheory.Mum.KeepsIota

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationEndomorphismCarriesPeriodPointBalaStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisationEndomorphism_carries_periodPoint_balanced : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ E : EndU U.toUnifPre, E.aB = a → E.h = h' → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (y : D.toPre.X) (g g' : GtPtF D.toPre F), GtPtF.IsIota y g → E.Act g g' → GtPtF.IsIota (h y) g' := by
  first | exact @GlobalTheory.Mum.KeepsIota.main | exact GlobalTheory.Mum.KeepsIota.main | (intros; apply GlobalTheory.Mum.KeepsIota.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiAdjointUniqueDegenerationData
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiAdjointUniqueDegenerationData
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.Mum.RosUniq
open GlobalTheory.CechPic GlobalTheory.EndRosati

theorem pt_eq_of_cls {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left} (hL : L.IsLB)
    (hK : KTriv A L) {R' : Type} [CommRing R'] {t : Spec (CommRingCat.of R') ⟶ S} (a b : Over.mk t ⟶ A)
    (H : pull (snd (Over.mk t) A * (fst (Over.mk t) A ≫ a)⁻¹ * (fst (Over.mk t) A ≫ b)).left (cls L hL) -
        pull (fst (Over.mk t) A ≫ b).left (cls L hL) =
      pull (snd (Over.mk t) A * (fst (Over.mk t) A ≫ a)⁻¹ * (fst (Over.mk t) A ≫ a)).left (cls L hL) -
        pull (fst (Over.mk t) A ≫ a).left (cls L hL)) : b = a := by
  let T : Over S := Over.mk t
  let x : T ⟶ A := b * a⁻¹
  have hx : lift (fst T A ≫ x) (snd T A) ≫ μ[A] = snd T A * (fst T A ≫ a)⁻¹ * (fst T A ≫ b) := by
    rw [← Hom.mul_def]
    simp only [x, MonObj.comp_mul, GrpObj.comp_inv]
    ac_rfl
  have hy : snd T A * (fst T A ≫ a)⁻¹ * (fst T A ≫ a) = snd T A := inv_mul_cancel_right _ _
  rw [hy, ← hx] at H
  have h1 : x = 1 := hK R' t x fun s => by
    obtain ⟨i, hi⟩ := exists_chart hL (a.left s)
    obtain ⟨i', hi'⟩ := exists_chart hL (b.left s)
    let V : (Spec (CommRingCat.of R')).Opens := a.left ⁻¹ᵁ L.U i ⊓ b.left ⁻¹ᵁ L.U i'
    refine ⟨V, ⟨hi, hi'⟩, ?_⟩
    have z : ∀ (c : T ⟶ A) (l : L.ι), V ≤ c.left ⁻¹ᵁ L.U l →
        pull ((fst T A).left ⁻¹ᵁ V).ι (pull (fst T A ≫ c).left (cls L hL)) = 0 := fun c l hl => by
      rw [← pull_comp]
      exact (cls_eq_zero_iff (LB.isLB_pull hL _)).2 (BoxKernel.gen_of_chart (LB.isLB_pull hL _) (fun _ => l)
        fun y => mem_pull.2 (hl y.2))
    have hT : (translDiff A L x).IsLB := LB.isLB_linComb hL _ _
    refine (cls_eq_zero_iff (LB.isLB_pull hT _)).1 ?_
    refine (cls_pull hT _ _).trans ((congrArg _ (cls_linComb hL _ _ hT)).trans ?_)
    have e : ∑ k : Fin 2, (![1, -1] : Fin 2 → ℤ) k • pull ((![(lift (fst T A ≫ x) (snd T A) ≫ μ[A]).left,
        (snd T A).left] : Fin 2 → _) k) (cls L hL) =
        pull (fst T A ≫ b).left (cls L hL) - pull (fst T A ≫ a).left (cls L hL) := by
      rw [Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul]
      linear_combination (norm := abel) H
    refine (congrArg _ e).trans ?_
    exact (map_sub _ _ _).trans ((congrArg₂ (· - ·) (z b i' inf_le_right) (z a i inf_le_left)).trans (sub_zero _))
  exact mul_inv_eq_one.1 h1

end GlobalTheory.Mum.RosUniq


open GlobalTheory.CechPic GlobalTheory.EndRosati GlobalTheory.Mum.RosUniq in
theorem GlobalTheory.Mum.rosatiAdj_unique : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (f g g' : D.toPre.P.A ⟶ D.toPre.P.A), IsMonHom f → IsMonHom g → IsMonHom g' → RosatiAdj D.toPre.P.A D.toPre.P.L f g → RosatiAdj D.toPre.P.A D.toPre.P.L f g' → g = g' := by
  intro R _ _ _ _ D f g g' hf hg hg' Hg Hg'
  have hGF := GlobalTheory.firstFiveLaws.1.globalFns
  obtain ⟨r, hr, -⟩ := exists_ros hGF D.toPre.P.isAb D.toPre.P.isLB f g Hg
  obtain ⟨r', hr', -⟩ := exists_ros hGF D.toPre.P.isAb D.toPre.P.isLB f g' Hg'
  have key : ∀ {T : Over (Spec (CommRingCat.of R))} (x y : T ⟶ D.toPre.P.A),
      pull (x * (y ≫ g)).left (cls _ D.toPre.P.isLB) - pull (y ≫ g).left (cls _ D.toPre.P.isLB) =
      pull (x * (y ≫ g')).left (cls _ D.toPre.P.isLB) - pull (y ≫ g').left (cls _ D.toPre.P.isLB) :=
    fun x y => by
      have h₁ := cls_of_rosati D.toPre.P.isLB r hr x y
      have h₂ := cls_of_rosati D.toPre.P.isLB r' hr' x y
      linear_combination (norm := abel) h₂ - h₁
  let cv := D.toPre.P.A.left.affineOpenCover
  refine Over.OverMorphism.ext (Scheme.Cover.hom_ext cv.openCover _ _ fun j => ?_)
  let t : Spec (CommRingCat.of (cv.X j)) ⟶ Spec (CommRingCat.of R) := cv.f j ≫ D.toPre.P.A.hom
  let y : Over.mk t ⟶ D.toPre.P.A := Over.homMk (cv.f j) rfl
  have k := key (snd (Over.mk t) D.toPre.P.A * (fst _ _ ≫ y ≫ g')⁻¹) (fst (Over.mk t) D.toPre.P.A ≫ y)
  simp only [Category.assoc] at k
  have e := pt_eq_of_cls D.toPre.P.isLB D.toPre.P.ktriv (y ≫ g') (y ≫ g) k
  exact congrArg (·.left) e
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiAdjointUniqueDegenerationDataStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rosatiAdjoint_unique_degenerationData : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (f g g' : D.toPre.P.A ⟶ D.toPre.P.A), IsMonHom f → IsMonHom g → IsMonHom g' → RosatiAdj D.toPre.P.A D.toPre.P.L f g → RosatiAdj D.toPre.P.A D.toPre.P.L f g' → g = g' := by
  first | exact @GlobalTheory.Mum.rosatiAdj_unique | exact GlobalTheory.Mum.rosatiAdj_unique | (intros; apply GlobalTheory.Mum.rosatiAdj_unique <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointUniformisationEndomorphismLiesOverAdjoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.Mum.AdjEnd

theorem rosati_unique : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (f g g' : D.toPre.P.A ⟶ D.toPre.P.A), IsMonHom f → IsMonHom g → IsMonHom g' → RosatiAdj D.toPre.P.A D.toPre.P.L f g → RosatiAdj D.toPre.P.A D.toPre.P.L f g' → g = g' := GlobalTheory.T.rosatiAdjoint_unique_degenerationData

theorem keepsIota : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ E : EndU U.toUnifPre, E.aB = a → E.h = h' → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (y : D.toPre.X) (g g' : GtPtF D.toPre F), GtPtF.IsIota y g → E.Act g g' → GtPtF.IsIota (h y) g' := GlobalTheory.T.uniformisationEndomorphism_carries_periodPoint_balanced

theorem aB_h_eq (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hR : AdmBase R (maximalIdeal R))
    (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    (U : UnifPre (maximalIdeal R) D A G) (E : EndU U) (a : D.toPre.P.A ⟶ D.toPre.P.A) (h' : D.toPre.X →+ D.toPre.X)
    (ha : IsMonHom a) (hE : FormalEnd U a h' fun e => (Over.pullback (thick R (maximalIdeal R) e)).map E.aG) :
    E.aB = a ∧ E.h = h' := by
  have := E.homG
  have := E.homB
  have hu := fun e => gtCoord_end_torus_abelian GlobalTheory.firstFiveLaws R (maximalIdeal R) hR D.toPre e G (U.gt e)
    ((Over.pullback (thick R (maximalIdeal R) e)).map E.aG) inferInstance
  have hm : ∀ e, (Over.pullback (thick R (maximalIdeal R) e)).map E.aB =
      (Over.pullback (thick R (maximalIdeal R) e)).map a := fun e =>
    (hu e).2.unique ⟨inferInstance, (E.q_lin e)⟩ ⟨inferInstance, hE.2.2.1 e⟩
  have := D.toPre.P.isAb.proper
  haveI : IsNoetherianRing R := hR.1
  refine ⟨GlobalTheory.hom_eq_of_thickenings_of_isProper R (maximalIdeal R) (IsLocalRing.maximalIdeal_le_jacobson _)
    D.toPre.P.A D.toPre.P.A _ _ fun e => ?_, ?_⟩
  · have k := congrArg (fun m => m.left ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e)) (hm e)
    simp only [GlobalTheory.EndData.map_fst] at k
    exact k
  · obtain ⟨t, ht, hi⟩ := hE.2.2.2 0
    obtain ⟨t', ht', hi'⟩ := E.i_lin 0
    exact (hu 0).1.unique ⟨t', ht', hi'⟩ ⟨t, ht, hi⟩

theorem linEnd_of_adjoint : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ g g' : G ⟶ G, LinEnd U.toUnifPre a h' g → IsMonHom g' → LBIso (cubeLB G ![fst G G ≫ g, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ g'] U.LG.L) → LinEnd U.toUnifPre a' h g' := by
  intro R _ _ _ hB D A G _ _ hG U a a' h h' hD g g' hg hg' hL
  obtain ⟨hadm, hc⟩ := hB
  have hF := GlobalTheory.UT.functorial_of_unif R (maximalIdeal R) hadm D A G hG U
  have := U.gen_hom
  have := hg.1
  have ex : ∀ b : G ⟶ G, IsMonHom b → ∃ E : EndU U.toUnifPre, E.aG = b := fun b hb => by
    obtain ⟨E, e1, -⟩ := hF.1 b (U.gen.inv ≫ (Over.pullback (jK R)).map b ≫ U.gen.hom) hb inferInstance (by simp)
    exact ⟨E, e1⟩
  obtain ⟨E, rfl⟩ := ex g hg.1
  obtain ⟨E', rfl⟩ := ex g' hg'
  obtain ⟨⟨-, hRB, -, -⟩, hFp⟩ := hF.2 E E' hL
  obtain ⟨haB, hh⟩ := aB_h_eq R hadm D A G U.toUnifPre E a h' hD.1 hg.2
  have ha' : E'.aB = a' := rosati_unique R ⟨hadm, hc⟩ D a E'.aB a' hD.1 E'.homB hD.2.1 (haB ▸ hRB) hD.2.2.1
  have hh2 : E'.h = h := by
    ext y
    let F := AlgebraicClosure (FractionRing R)
    obtain ⟨g₀, hg₀⟩ := GlobalTheory.TorusExt.exists_iota (F := F) D.tau_bimult y
    obtain ⟨g₁, hg₁, -⟩ := ((hFp F).1 g₀)
    exact GlobalTheory.IotaInj.main GlobalTheory.firstFiveLaws R (maximalIdeal R) hadm D F _ _ g₁ ((hFp F).2.1 y g₀ g₁ hg₀ hg₁)
      (keepsIota R ⟨hadm, hc⟩ D A G hG U a a' h h' hD E haB hh F y g₀ g₁ hg₀ hg₁)
  have := E'.homG
  exact ⟨inferInstance, fun e => inferInstance, fun e => GlobalTheory.Mum.EndModel.thickMap_map _ e,
    fun e => ha' ▸ E'.q_lin e, fun e => hh2 ▸ E'.i_lin e⟩

end GlobalTheory.Mum.AdjEnd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointUniformisationEndomorphismLiesOverAdjointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adjoint_uniformisationEndomorphism_lies_over_adjoint : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ g g' : G ⟶ G, LinEnd U.toUnifPre a h' g → IsMonHom g' → LBIso (cubeLB G ![fst G G ≫ g, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ g'] U.LG.L) → LinEnd U.toUnifPre a' h g' := by
  first | exact @GlobalTheory.Mum.AdjEnd.linEnd_of_adjoint | exact GlobalTheory.Mum.AdjEnd.linEnd_of_adjoint | (intros; apply GlobalTheory.Mum.AdjEnd.linEnd_of_adjoint <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupEndomorphismsAdjointPair
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem linEnd_adjoint_lbIso : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ g g' : G ⟶ G, LinEnd U.toUnifPre a h' g → LinEnd U.toUnifPre a' h g' → LBIso (cubeLB G ![fst G G ≫ g, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ g'] U.LG.L) := by
  intro R _ _ _ hR D A G _ _ hG U a a' h h' hE g g' hg hg'
  obtain ⟨g₁, hg₁, hiso⟩ := GlobalTheory.T.exists_adjoint_endomorphism_uniformised_group R hR D A G hG U g hg.1
  have h₁ : LinEnd U.toUnifPre a' h g₁ := GlobalTheory.T.adjoint_uniformisationEndomorphism_lies_over_adjoint R hR D A G hG U a a' h h' hE g g₁ hg hg₁ hiso
  have hu := GlobalTheory.T.semiAbelian_endomorphism_unique_over_degenerationData R hR.1 D A G hG U a' h
  have heq : g₁ = g' := hu.2 g₁ g' fun e => congrFun (hu.1 _ _ h₁.2 hg'.2) e
  subst heq
  exact hiso

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupEndomorphismsAdjointPairStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisedGroup_endomorphisms_adjoint_pair : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ g g' : G ⟶ G, LinEnd U.toUnifPre a h' g → LinEnd U.toUnifPre a' h g' → LBIso (cubeLB G ![fst G G ≫ g, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ g'] U.LG.L) := by
  first | exact @GlobalTheory.Mum.linEnd_adjoint_lbIso | exact GlobalTheory.Mum.linEnd_adjoint_lbIso | (intros; apply GlobalTheory.Mum.linEnd_adjoint_lbIso <;> assumption)
end
