module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullGenPf

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.CanonicalLiftOrigin
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.CanonicalLiftTraces
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.CanonicalLiftEigen
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.CanonicalLiftValuation
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  IsLocalRing

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.H1.CanonicalLiftValuation

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X]

theorem ros_snd_one (hG : GlobalFnsSt) (f g : D.toPre.P.A ⟶ D.toPre.P.A) [IsMonHom f] [IsMonHom g]
    (r : LB.Gen (LB.LinComb D.toPre.P.L (rosatiφ D.toPre.P.A f g) rosatiε)) (hr : r.IsGen)
    (hr0 : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ r (zero2 D.toPre.P.A)) (LB.oneGen D.toPre.P.L))
    {T : Over (Spec (CommRingCat.of V))} {z : T.left} {J} (hJ : Good D.toPre.P.L z J) (y : T ⟶ D.toPre.P.A) :
    val₂ r z J y 1 = 1 := by
  have face (x y : T ⟶ D.toPre.P.A) : cubV D.toPre.cub z J 1 x y = 1 := by
    have h := val_corr hJ (D.toPre.cub.face 0) (lift x y).left
    rw [val_one] at h
    refine Eq.trans ?_ h
    refine Eq.trans ?_ (val_cub D.toPre.cub (lift x y) hJ (pzero D.toPre.P.A _) (x2 D.toPre.P.A 0) (x2 D.toPre.P.A 1)).symm
    congr 1 <;> simp [x2, pzero, Hom.one_def]
  have c11 (a : T ⟶ D.toPre.P.A) : cubV D.toPre.cub z J a 1 1 = 1 := by
    have h := (val_corr hJ D.toPre.cub.cubeSymmetric_swap_first (lift a (lift (1 : T ⟶ D.toPre.P.A) 1)).left).trans
      (val_cub D.toPre.cub (lift a (lift (1 : T ⟶ D.toPre.P.A) 1)) hJ _ _ _)
    refine h.trans ?_
    simpa [x3] using face a 1
  have h := (ros_add D.toPre.cub hG D.toPre.P.isAb f g r hr hr0 hJ 1 1 y).2
  rw [_root_.mul_one, MonObj.one_comp g, c11 y, c11 (y ≫ f), _root_.mul_one, _root_.one_mul] at h
  have h' : val₂ r z J y 1 * val₂ r z J y 1 = val₂ r z J y 1 * 1 := by
    rw [_root_.mul_one]; exact h.symm
  exact mul_left_cancel h'

private theorem formEq_sumElim_pullφ_rosatiφ (oa : D.toPre.OAct O) (a : O) (k N : ℕ) (χ : D.toPre.X) :
    FormEq (Sum.elim (pullφ D F oa a 0) (fun j => (lift (cP D.toPre _ χ) (DegPre.prB D.toPre F)).left ≫
        rosatiφ D.toPre.P.A (oa.onB.act (star a)) (oa.onB.act a) j))
      (Sum.elim (pullε k N) rosatiε) (pullφ D F oa a χ) (pullε k N) := by
  intro U _ h
  haveI := oa.onB.hom a
  haveI := oa.onB.hom (star a)
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, pullφ, pullε]
  rw [prod_ros]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, DegPre.famφ, DegPre.famε, Matrix.cons_val_zero,
    Matrix.cons_val_succ, smul_zero]
  have E1 : (padd D.toPre.P.A (DegPre.prB D.toPre F) (toUnit _ ≫ D.toPre.c 0)).left =
      (DegPre.prB D.toPre F).left := by
    congr 1
    change DegPre.prB D.toPre F * cP D.toPre _ 0 = _
    rw [cPoint_zero, _root_.mul_one]
  have E2 : (toUnit (DegPre.BF D.toPre F) ≫ D.toPre.c 0).left =
      (toUnit (DegPre.BF D.toPre F) ≫ η[D.toPre.P.A]).left := by
    congr 1
    exact cPoint_zero (D := D.toPre) _
  have E5 : (cP D.toPre _ χ ≫ oa.onB.act (star a)).left =
      (toUnit (DegPre.BF D.toPre F) ≫ D.toPre.c (star a • χ)).left := by
    congr 1
    rw [oa.c_lin]
    simp [cP]
  have E4 : ((cP D.toPre _ χ ≫ oa.onB.act (star a)) * DegPre.prB D.toPre F).left =
      (padd D.toPre.P.A (DegPre.prB D.toPre F) (toUnit _ ≫ D.toPre.c (star a • χ))).left := by
    congr 1
    change _ = DegPre.prB D.toPre F * (toUnit _ ≫ D.toPre.c (star a • χ))
    rw [mul_comm]
    congr 1
    rw [oa.c_lin]
    simp [cP]
  have E6 : (cP D.toPre _ χ * (DegPre.prB D.toPre F ≫ oa.onB.act a)).left =
      (aF D F oa a).left ≫ (padd D.toPre.P.A (DegPre.prB D.toPre F) (toUnit _ ≫ D.toPre.c χ)).left := by
    rw [← Over.comp_left]
    congr 1
    change _ = aF D F oa a ≫ (DegPre.prB D.toPre F * (toUnit _ ≫ D.toPre.c χ))
    rw [mul_comm]
    first
    | rw [MonObj.comp_mul]
    | rw [comp_mul]
    | rw [Hom.comp_mul]
    simp [aF, cP]
  have E7 : (cP D.toPre (DegPre.BF D.toPre F) χ).left =
      (aF D F oa a).left ≫ (toUnit _ ≫ D.toPre.c χ).left := by
    rw [← Over.comp_left]
    congr 1
    simp [aF, cP]
  have E8 : (DegPre.prB D.toPre F ≫ oa.onB.act a).left = (aF D F oa a).left ≫ (DegPre.prB D.toPre F).left := by
    rw [← Over.comp_left]
    congr 1
    simp [aF]
  have E9 : (aF D F oa a).left ≫ (toUnit (DegPre.BF D.toPre F) ≫ η[D.toPre.P.A]).left =
      (toUnit (DegPre.BF D.toPre F) ≫ η[D.toPre.P.A]).left := by
    rw [← Over.comp_left]
    congr 1
    simp
  rw [E1, E2, E4, E5, E6, E7, E8, E9]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
  abel

theorem pull_val_chi (hG : GlobalFnsSt) (oa : D.toPre.OAct O) (a : O) (k N : ℕ) (χ : D.toPre.X)
    (u : LB.Gen (LB.LinComb D.toPre.P.L (pullφ D F oa a χ) (pullε k N))) (hu : u.IsGen)
    (hc : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ u (DegPre.zF D.toPre F).left)
      (LB.pullGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK (k * (N - 1))) (jFK (R := V) F)))
    (u0 : LB.Gen (LB.LinComb D.toPre.P.L (pullφ D F oa a 0) (pullε k N))) (hu0 : u0.IsGen)
    (hc0 : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ u0 (DegPre.zF D.toPre F).left)
      (LB.pullGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK (k * (N - 1))) (jFK (R := V) F)))
    (r : LB.Gen (LB.LinComb D.toPre.P.L (rosatiφ D.toPre.P.A (oa.onB.act (star a)) (oa.onB.act a)) rosatiε))
    (hr : r.IsGen)
    (hr0 : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ r (zero2 D.toPre.P.A)) (LB.oneGen D.toPre.P.L))
    (Z : Scheme.{0}) (ρ : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) (J) (hJ : Good D.toPre.P.L z J) :
    val u ρ z J = val u0 ρ z J *
      val (LB.pullGen D.toPre.P.L _ _ r (lift (cP D.toPre _ χ) (DegPre.prB D.toPre F)).left) ρ z J := by
  haveI := oa.onB.hom a
  haveI := oa.onB.hom (star a)
  refine (gen_unique' D.toPre.P.isLB (formEq_sumElim_pullφ_rosatiφ oa a k N χ) (fst (TF (R := V) F) D.toPre.P.A).left
    (DegPre.zF D.toPre F).left GC.zF_fst (surj_appTop (D := D.toPre) (F := F) hG) hu
    (mulGen_isGen _ _ _ _ _ _ _ hu0 (pullGen_isGen _ _ _ _ hr _)) ?_ Z ρ z J hJ).trans (val_mul hJ _ _ _)
  intro y J' hJ'
  rw [val_mul hJ']
  have e1 : val u (DegPre.zF D.toPre F).left y J' = val (LB.pullGen D.toPre.P.L _ _
      (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK (k * (N - 1))) (jFK (R := V) F)) (𝟙 _) y J' := by
    rw [← Category.id_comp (DegPre.zF D.toPre F).left, ← val_pull hJ']
    exact val_corr hJ' hc _
  have e2 : val u0 (DegPre.zF D.toPre F).left y J' = val (LB.pullGen D.toPre.P.L _ _
      (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK (k * (N - 1))) (jFK (R := V) F)) (𝟙 _) y J' := by
    rw [← Category.id_comp (DegPre.zF D.toPre F).left, ← val_pull hJ']
    exact val_corr hJ' hc0 _
  have hz : DegPre.zF D.toPre F ≫ lift (cP D.toPre _ χ) (DegPre.prB D.toPre F) =
      lift (cP D.toPre (TF (R := V) F) χ) 1 := by
    simp [DegPre.zF, cP, Hom.one_def]
  have e3 : val (LB.pullGen D.toPre.P.L _ _ r (lift (cP D.toPre _ χ) (DegPre.prB D.toPre F)).left)
      (DegPre.zF D.toPre F).left y J' = 1 := by
    rw [val_pull hJ', ← Over.comp_left, hz]
    exact ros_snd_one hG _ _ r hr hr0 hJ' _
  rw [e1, e2, e3]
  exact (_root_.mul_one _).symm
end ReciprocityTheory.ChartRestriction.G.H1.CanonicalLiftValuation
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  IsLocalRing

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.H1.CanonicalLiftEigen

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X]

theorem tr_aF (oa : D.toPre.OAct O) (a : O) (b : TF (R := V) F ⟶ D.toPre.P.A) (z : D.toPre.X)
    (hb : b ≫ oa.onB.act a = cP D.toPre _ (-z)) :
    DegPre.trPt D.toPre F b ≫ aF D F oa a = aF D F oa a ≫ DegPre.trF D.toPre F (-z) := by
  have hmh : IsMonHom (oa.onB.act a) := oa.onB.hom a
  apply CartesianMonoidalCategory.hom_ext
  · simp [DegPre.trPt, aF, DegPre.trF]
  · simp only [DegPre.trPt, aF, DegPre.trF, DegPre.prB, padd, Category.assoc,
      CartesianMonoidalCategory.lift_snd, CartesianMonoidalCategory.comp_lift_assoc,
      CartesianMonoidalCategory.lift_snd_assoc]
    rw [IsMonHom.mul_hom, CartesianMonoidalCategory.lift_map_assoc, Category.assoc, hb]
    unfold cP
    congr 2
    all_goals first | rfl | (apply SemiCartesianMonoidalCategory.toUnit_unique) | simp

theorem eigen_of_origin (hG : GlobalFnsSt) (oa : D.toPre.OAct O) (a : O) (N : ℕ) (p : QkPt D.toPre F (1 * N))
    (z : D.toPre.X) (hy : p.y = -(star a • z)) (hb : p.g.b ≫ oa.onB.act a = cP D.toPre _ (-z)) (χ : D.toPre.X)
    (uχ : LB.Gen (LB.LinComb D.toPre.P.L (pullφ D F oa a χ) (pullε 1 N))) (huχ : uχ.IsGen)
    (uχz : LB.Gen (LB.LinComb D.toPre.P.L (pullφ D F oa a (χ - z)) (pullε 1 N))) (huχz : uχz.IsGen)
    (fe : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.deltaφ D.toPre F 1 χ (-z)) (DegPre.deltaε 1))) (hfe : fe.IsGen)
    (Φ : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.phiφ D.toPre F p.y (star a • χ) p.g.b) (DegPre.deltaε (1 * N))))
    (hΦ : Φ.IsGen)
    (horig : ∀ y J, Good D.toPre.P.L y J →
      val (LB.mulGen D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ uχ (DegPre.trPt D.toPre F p.g.b).left) Φ)
          (DegPre.zF D.toPre F).left y J =
        val (LB.mulGen D.toPre.P.L _ _ _ _ uχz (LB.pullGen D.toPre.P.L _ _ fe (aF D F oa a).left))
          (DegPre.zF D.toPre F).left y J)
    (Z : Scheme.{0}) (ρ : Z ⟶ (DegPre.BF D.toPre F).left) (z' : Z) (J) (hJ : Good D.toPre.P.L z' J) :
    val uχ (ρ ≫ (DegPre.trPt D.toPre F p.g.b).left) z' J * val Φ ρ z' J =
      val uχz ρ z' J * val fe (ρ ≫ (aF D F oa a).left) z' J := by
  have e1 : ∀ i, (DegPre.trPt D.toPre F p.g.b).left ≫ (aF D F oa a).left ≫ DegPre.famφ D.toPre F χ i =
      (aF D F oa a ≫ DegPre.trF D.toPre F (-z)).left ≫ DegPre.famφ D.toPre F χ i := fun i => by
    rw [← Category.assoc, ← Over.comp_left, tr_aF oa a p.g.b z hb]
  have e2 : ∀ i, (aF D F oa a).left ≫ (DegPre.trF D.toPre F (-z)).left ≫ DegPre.famφ D.toPre F χ i =
      (aF D F oa a ≫ DegPre.trF D.toPre F (-z)).left ≫ DegPre.famφ D.toPre F χ i := fun i => by
    rw [← Category.assoc, ← Over.comp_left]
  have e3 : star a • χ + p.y = star a • (χ - z) := by rw [hy, smul_sub, sub_eq_add_neg]
  have e4 : χ + 1 • -z = χ - z := by rw [one_smul, sub_eq_add_neg]
  have hF : FormEq (Sum.elim (pullφ D F oa a (χ - z))
      (fun i => (aF D F oa a).left ≫ DegPre.deltaφ D.toPre F 1 χ (-z) i)) (Sum.elim (pullε 1 N) (DegPre.deltaε 1))
      (Sum.elim (fun i => (DegPre.trPt D.toPre F p.g.b).left ≫ pullφ D F oa a χ i)
        (DegPre.phiφ D.toPre F p.y (star a • χ) p.g.b)) (Sum.elim (pullε 1 N) (DegPre.deltaε (1 * N))) :=
    fun U _ h => by
      simp only [pullφ, pullε, DegPre.phiφ, DegPre.deltaφ, DegPre.deltaε, Fintype.prod_sum_type, Sum.elim_inl,
        Sum.elim_inr, e1, e2, e3, e4]
      simp only [Fin.prod_univ_four]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module
  have key := gen_unique' D.toPre.P.isLB hF (fst (TF (R := V) F) D.toPre.P.A).left (DegPre.zF D.toPre F).left
    (GC.zF_fst (D := D) (F := F)) (surj_appTop D.toPre F hG)
    (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ huχ _) hΦ)
    (mulGen_isGen _ _ _ _ _ _ _ huχz (pullGen_isGen _ _ _ _ hfe _)) horig Z ρ z' J hJ
  rw [val_mul hJ, val_mul hJ, val_pull hJ, val_pull hJ] at key
  exact key
end ReciprocityTheory.ChartRestriction.G.H1.CanonicalLiftEigen
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  IsLocalRing

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.H1.CanonicalLiftTraces

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X]

theorem comp_famφ {T : Over (Spec (CommRingCat.of V))} (X : T ⟶ DegPre.BF D.toPre F) (ξ : D.toPre.X) (i : Fin 4) :
    X.left ≫ DegPre.famφ D.toPre F ξ i =
      (![X ≫ DegPre.prB D.toPre F, (X ≫ DegPre.prB D.toPre F) * cP D.toPre T ξ, cP D.toPre T ξ, 1] i).left := by
  fin_cases i
  · simp [DegPre.famφ]
  · show X.left ≫ (DegPre.prB D.toPre F * (toUnit _ ≫ D.toPre.c ξ)).left =
      ((X ≫ DegPre.prB D.toPre F) * cP D.toPre T ξ).left
    rw [← Over.comp_left, comp_mul, ← Category.assoc, comp_toUnit]
    rfl
  · show X.left ≫ (toUnit _ ≫ D.toPre.c ξ).left = (cP D.toPre T ξ).left
    rw [← Over.comp_left, ← Category.assoc, comp_toUnit]
    rfl
  · show X.left ≫ (toUnit _ ≫ η[D.toPre.P.A]).left = (1 : T ⟶ D.toPre.P.A).left
    rw [← Over.comp_left, ← Hom.one_def, comp_one]

theorem zF_tr_pr (b : TF (R := V) F ⟶ D.toPre.P.A) :
    (DegPre.zF D.toPre F ≫ DegPre.trPt D.toPre F b) ≫ DegPre.prB D.toPre F = b := by
  simp [DegPre.trPt, DegPre.zF, DegPre.prB, padd, ← Hom.mul_def, ← Hom.one_def, comp_mul]

theorem zF_aF (oa : D.toPre.OAct O) (a : O) : DegPre.zF D.toPre F ≫ aF D F oa a = DegPre.zF D.toPre F := by
  haveI := oa.onB.hom a
  apply CartesianMonoidalCategory.hom_ext <;>
    simp [aF, DegPre.zF, DegPre.prB, IsMonHom.one_hom]

theorem exists_w (oa : D.toPre.OAct O) (a : O) (N : ℕ) (hN : 1 ≤ N) (b : TF (R := V) F ⟶ D.toPre.P.A)
    (z : D.toPre.X) (hb : b ≫ oa.onB.act a = cP D.toPre _ (-z))
    (u0 : LB.Gen (LB.LinComb D.toPre.P.L (pullφ D F oa a 0) (pullε 1 N))) (hu0 : u0.IsGen) :
    ∃ w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F b) (DegPre.lineε (1 * N))), w.IsGen ∧
      ∀ (y : (TF (R := V) F).left) J, Good D.toPre.P.L y J → val w (𝟙 (TF (R := V) F).left) y J =
        val (LB.pullGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK (1 * (N - 1))) (jFK (R := V) F))
            (𝟙 (TF (R := V) F).left) y J *
          val (LB.pullGen D.toPre.P.L _ _ (LB.mulGen D.toPre.P.L _ _ _ _
            (GeneratorPullback.powGen D.toPre.P.L _ _ (D.toPre.psi (-z)) 1) (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK 1))
              (jFK (R := V) F)) (𝟙 (TF (R := V) F).left) y J *
          (val u0 (DegPre.zF D.toPre F ≫ DegPre.trPt D.toPre F b).left y J)⁻¹ := by
  have := oa.onB.hom a
  have h1 : (DegPre.zF D.toPre F ≫ DegPre.trPt D.toPre F b) ≫ DegPre.prB D.toPre F = b := zF_tr_pr b
  have h2 : ((DegPre.zF D.toPre F ≫ DegPre.trPt D.toPre F b) ≫ aF D F oa a) ≫ DegPre.prB D.toPre F =
      cP D.toPre _ (-z) := by
    rw [Category.assoc, show aF D F oa a ≫ DegPre.prB D.toPre F = DegPre.prB D.toPre F ≫ oa.onB.act a by
      simp [aF, DegPre.prB], ← Category.assoc, h1, hb]
  have e2 : ∀ i, (DegPre.zF D.toPre F ≫ DegPre.trPt D.toPre F b).left ≫ (aF D F oa a).left ≫
      DegPre.famφ D.toPre F 0 i = ((DegPre.zF D.toPre F ≫ DegPre.trPt D.toPre F b) ≫ aF D F oa a).left ≫
      DegPre.famφ D.toPre F 0 i := fun i => by rw [← Category.assoc, ← Over.comp_left]
  have c0 : cP D.toPre (TF (R := V) F) 0 = 1 := cPoint_zero _
  have p0 : (DegPre.zeroF D.toPre F).left = (1 : TF (R := V) F ⟶ D.toPre.P.A).left := rfl
  have p1 : jFK (R := V) F ≫ (toUnit (TK V)).left ≫ eSec D.toPre.P.A = (1 : TF (R := V) F ⟶ D.toPre.P.A).left :=
    (Category.assoc _ _ _).symm
  have p2 : jFK (R := V) F ≫ D.toPre.xK (-z) = (cP D.toPre (TF (R := V) F) (-z)).left := (Category.assoc _ _ _).symm
  have hN' : ((1 * (N - 1) : ℕ) : ℤ) = ((1 * N : ℕ) : ℤ) - 1 := by omega
  obtain ⟨w, hw, hv⟩ := exists_gen D.toPre.P.isLB (φ' := DegPre.lineφ D.toPre F b) (ε' := DegPre.lineε (1 * N))
    (fun U _ h => by
      simp only [pullφ, pullε, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, e2, p1, p2]
      simp only [comp_famφ, h1, h2, Fin.prod_univ_four, Fin.prod_univ_two, Matrix.cons_val, DegPre.famε, smul_zero, c0,
        _root_.mul_one, DegPre.lineφ, DegPre.lineε, p0, hN']
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      push_cast
      module)
    (LB.mulGen D.toPre.P.L _ _ _ _ (LB.mulGen D.toPre.P.L _ _ _ _
      (LB.pullGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK (1 * (N - 1))) (jFK (R := V) F))
      (LB.pullGen D.toPre.P.L _ _ (LB.mulGen D.toPre.P.L _ _ _ _
        (GeneratorPullback.powGen D.toPre.P.L _ _ (D.toPre.psi (-z)) 1) (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK 1)) (jFK (R := V) F)))
      (LB.invGen D.toPre.P.L _ _ (LB.pullGen D.toPre.P.L _ _ u0 (DegPre.zF D.toPre F ≫ DegPre.trPt D.toPre F b).left)))
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _
      (pullGen_isGen _ _ _ _ (powGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ D.toPre.rig_gen _) _) _)
      (pullGen_isGen _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (powGen_isGen _ _ _ _ (D.toPre.psi_gen _) _)
        (powGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ D.toPre.rig_gen _) _)) _))
      (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ hu0 _)))
  refine ⟨w, hw, fun y J hJ => ?_⟩
  rw [hv _ _ y J hJ, val_mul hJ, val_mul hJ, val_inv, val_pull hJ u0, Category.id_comp]
end ReciprocityTheory.ChartRestriction.G.H1.CanonicalLiftTraces
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  IsLocalRing

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.H1.CanonicalLiftOrigin

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X]

theorem gt_rel (oa : D.toPre.OAct O) (a : O) (g g' h g0 : GtPtF D.toPre F) (z : D.toPre.X)
    (hgt : GtAct oa a g g') (hι : GtPtF.IsIota z h) (hadd : g'.IsAdd h g0) (hz : g0.IsZero)
    (r : LB.Gen (LB.LinComb D.toPre.P.L (rosatiφ D.toPre.P.A (oa.onB.act (star a)) (oa.onB.act a)) rosatiε))
    (hr : r.IsGen)
    (hr0 : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ r (zero2 D.toPre.P.A)) (LB.oneGen D.toPre.P.L)) :
    g.b ≫ oa.onB.act a = cP D.toPre _ (-z) ∧
      ∀ (χ : D.toPre.X) (y : (TF (R := V) F).left) J, Good D.toPre.P.L y J →
        val (g.s (star a • χ)) (𝟙 _) y J * val r (lift (DegPre.cF D.toPre F χ) g.b).left y J =
          val (D.toPre.tau (-z) χ) (𝟙 (TF (R := V) F).left ≫ jFK (R := V) F) y J := by
  obtain ⟨hb', hs'⟩ := hgt
  rw [isIota_iff] at hι
  obtain ⟨hbh, hsh⟩ := hι
  rw [isAdd_iff] at hadd
  obtain ⟨hb0, hs0⟩ := hadd
  rw [isZero_iff] at hz
  obtain ⟨hz0, hzs⟩ := hz
  have hneg : cP D.toPre (TF (R := V) F) z * cP D.toPre (TF (R := V) F) (-z) = 1 := by
    rw [← cPoint_add, add_neg_cancel, cPoint_zero]
  have h1 : g'.b * h.b = 1 := by rw [← hb0, hz0]
  have hgb : g'.b = cP D.toPre (TF (R := V) F) (-z) := by
    calc g'.b = g'.b * (cP D.toPre (TF (R := V) F) z * cP D.toPre (TF (R := V) F) (-z)) := by
          rw [hneg, _root_.mul_one]
      _ = (g'.b * h.b) * cP D.toPre (TF (R := V) F) (-z) := by rw [hbh, _root_.mul_assoc]
      _ = cP D.toPre (TF (R := V) F) (-z) := by rw [h1, _root_.one_mul]
  refine ⟨hb'.symm.trans hgb, ?_⟩
  intro χ y J hJ
  have e1 : val (g.s (star a • χ)) (𝟙 _) y J * val r (lift (DegPre.cF D.toPre F χ) g.b).left y J =
      val (g'.s χ) (𝟙 _) y J := by
    rw [← val_corr (h := hs' r hr hr0 χ) (r := 𝟙 _), val_mul, val_pull, Category.id_comp]
    all_goals first | exact hJ | rfl
  rw [e1]
  have e2 := hs0 χ y J hJ
  rw [hzs χ y J hJ, _root_.one_mul, hsh χ y J hJ] at e2
  have e4 : th D.toPre y J (cP D.toPre _ χ) g'.b h.b =
      th D.toPre y J (cP D.toPre (TF (R := V) F) χ) (cP D.toPre (TF (R := V) F) (-z))
        (cP D.toPre (TF (R := V) F) z) := by
    rw [hgb, hbh]
  rw [e4] at e2
  have hc3 : IsCub (th D.toPre y J) := isCub_cubV _ hJ
  have e5 : val (D.toPre.tau (-z + z) χ) (𝟙 (TF (R := V) F).left ≫ jFK (R := V) F) y J *
        th D.toPre y J (cP D.toPre (TF (R := V) F) (-z)) (cP D.toPre (TF (R := V) F) z)
          (cP D.toPre (TF (R := V) F) χ) =
      val (D.toPre.tau (-z) χ) (𝟙 (TF (R := V) F).left ≫ jFK (R := V) F) y J *
        val (D.toPre.tau z χ) (𝟙 (TF (R := V) F).left ≫ jFK (R := V) F) y J :=
    tau_mul (σ := 𝟙 (TF (R := V) F)) (hJ := hJ) D.tau_bimult (-z) z χ
  have e6 : val (D.toPre.tau (0 + 0) χ) (𝟙 (TF (R := V) F).left ≫ jFK (R := V) F) y J *
        th D.toPre y J (cP D.toPre (TF (R := V) F) 0) (cP D.toPre (TF (R := V) F) 0)
          (cP D.toPre (TF (R := V) F) χ) =
      val (D.toPre.tau 0 χ) (𝟙 (TF (R := V) F).left ≫ jFK (R := V) F) y J *
        val (D.toPre.tau 0 χ) (𝟙 (TF (R := V) F).left ≫ jFK (R := V) F) y J :=
    tau_mul (σ := 𝟙 (TF (R := V) F)) (hJ := hJ) D.tau_bimult 0 0 χ
  rw [cPoint_zero, hc3.face, _root_.mul_one, add_zero] at e6
  have t0 : val (D.toPre.tau 0 χ) (𝟙 (TF (R := V) F).left ≫ jFK (R := V) F) y J = 1 :=
    mul_left_cancel (e6.symm.trans (_root_.mul_one _).symm)
  rw [neg_add_cancel, t0, _root_.one_mul] at e5
  rw [hc3.s01, hc3.s12, e5] at e2
  exact (mul_right_cancel e2).symm

theorem origin (hG : GlobalFnsSt) (oa : D.toPre.OAct O) (a : O) (N : ℕ) (p : QkPt D.toPre F (1 * N))
    (z : D.toPre.X)
    (r : LB.Gen (LB.LinComb D.toPre.P.L (rosatiφ D.toPre.P.A (oa.onB.act (star a)) (oa.onB.act a)) rosatiε))
    (hr : r.IsGen)
    (hr0 : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ r (zero2 D.toPre.P.A)) (LB.oneGen D.toPre.P.L))
    (hrel : ∀ (χ : D.toPre.X) (y : (TF (R := V) F).left) J, Good D.toPre.P.L y J →
        val (p.g.s (star a • χ)) (𝟙 _) y J * val r (lift (DegPre.cF D.toPre F χ) p.g.b).left y J =
          val (D.toPre.tau (-z) χ) (𝟙 (TF (R := V) F).left ≫ jFK (R := V) F) y J)
    (u0 : LB.Gen (LB.LinComb D.toPre.P.L (pullφ D F oa a 0) (pullε 1 N))) (hu0 : u0.IsGen)
    (hc0 : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ u0 (DegPre.zF D.toPre F).left)
      (LB.pullGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK (1 * (N - 1))) (jFK (R := V) F)))
    (w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε (1 * N)))) (hw : w.IsGen)
    (hwv : ∀ (y : (TF (R := V) F).left) J, Good D.toPre.P.L y J → val w (𝟙 (TF (R := V) F).left) y J =
        val (LB.pullGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK (1 * (N - 1))) (jFK (R := V) F))
            (𝟙 (TF (R := V) F).left) y J *
          val (LB.pullGen D.toPre.P.L _ _ (LB.mulGen D.toPre.P.L _ _ _ _
            (GeneratorPullback.powGen D.toPre.P.L _ _ (D.toPre.psi (-z)) 1) (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK 1))
              (jFK (R := V) F)) (𝟙 (TF (R := V) F).left) y J *
          (val u0 (DegPre.zF D.toPre F ≫ DegPre.trPt D.toPre F p.g.b).left y J)⁻¹)
    (χ : D.toPre.X)
    (uχ : LB.Gen (LB.LinComb D.toPre.P.L (pullφ D F oa a χ) (pullε 1 N))) (huχ : uχ.IsGen)
    (hc : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ uχ (DegPre.zF D.toPre F).left)
      (LB.pullGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK (1 * (N - 1))) (jFK (R := V) F)))
    (uχz : LB.Gen (LB.LinComb D.toPre.P.L (pullφ D F oa a (χ - z)) (pullε 1 N)))
    (hcz : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ uχz (DegPre.zF D.toPre F).left)
      (LB.pullGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK (1 * (N - 1))) (jFK (R := V) F)))
    (fe : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.deltaφ D.toPre F 1 χ (-z)) (DegPre.deltaε 1)))
    (hcfe : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ fe (DegPre.zF D.toPre F).left)
      (DegPre.famMult D.toPre F 1 (-z) χ))
    (Φ : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.phiφ D.toPre F p.y (star a • χ) p.g.b) (DegPre.deltaε (1 * N))))
    (hΦ : Φ.IsGen)
    (hcΦ : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ Φ (DegPre.zF D.toPre F).left)
      (LB.mulGen D.toPre.P.L _ _ _ _ (p.g.s (star a • χ)) w))
    (y : (TF (R := V) F).left) (J) (hJ : Good D.toPre.P.L y J) :
    val (LB.mulGen D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ uχ (DegPre.trPt D.toPre F p.g.b).left) Φ)
        (DegPre.zF D.toPre F).left y J =
      val (LB.mulGen D.toPre.P.L _ _ _ _ uχz (LB.pullGen D.toPre.P.L _ _ fe (aF D F oa a).left))
        (DegPre.zF D.toPre F).left y J := by
  have C : IsCub (th D.toPre (T := TF (R := V) F) y J) := isCub_cubV D.toPre.cub hJ
  have z1 : DegPre.zF D.toPre F ≫ fst (TF (R := V) F) D.toPre.P.A = 𝟙 _ := lift_fst _ _
  have z2 : DegPre.zF D.toPre F ≫ DegPre.prB D.toPre F = 1 := lift_snd _ _
  have hu1 : uVal D.toPre F (1 * N) (star a • χ) p.g.b (DegPre.zF D.toPre F) y J = 1 := by
    unfold uVal
    rw [z2, C.N_one, C.face₂, inv_one, _root_.mul_one]
  have hl : ((DegPre.zF D.toPre F).left ≫ (DegPre.trPt D.toPre F p.g.b).left) ≫
      (lift (cP D.toPre _ χ) (DegPre.prB D.toPre F)).left = (lift (DegPre.cF D.toPre F χ) p.g.b).left := by
    rw [← Over.comp_left, ← Over.comp_left, comp_lift, comp_cP, CanonicalLiftTraces.zF_tr_pr]
    rfl
  have e1 := val_corr hJ hcz (𝟙 _)
  rw [val_pull hJ, Category.id_comp] at e1
  have e2 := val_corr hJ hcfe (𝟙 _)
  rw [val_pull hJ, Category.id_comp] at e2
  have e3 := val_famMult (𝟙 (TF (R := V) F)) hJ 1 (-z) χ
  simp only [Over.id_left] at e3
  have e4 : val (LB.pullGen D.toPre.P.L _ _ (LB.mulGen D.toPre.P.L _ _ _ _
      (GeneratorPullback.powGen D.toPre.P.L _ _ (D.toPre.psi (-z)) 1) (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK 1))
        (jFK (R := V) F)) (𝟙 (TF (R := V) F).left) y J =
      val (GeneratorPullback.powGen D.toPre.P.L _ _ (D.toPre.psi (-z)) 1) (𝟙 (TF (R := V) F).left ≫ jFK (R := V) F) y J *
        val (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK 1) (𝟙 (TF (R := V) F).left ≫ jFK (R := V) F) y J := by
    rw [val_pull hJ, val_mul hJ]
  have e5 := hwv y J hJ
  rw [e4, Over.comp_left] at e5
  have e6 := hrel χ y J hJ
  have e7 : val fe ((DegPre.zF D.toPre F).left ≫ (aF D F oa a).left) y J = val fe (DegPre.zF D.toPre F).left y J := by
    rw [← Over.comp_left, CanonicalLiftTraces.zF_aF]
  have hΦv : val Φ (DegPre.zF D.toPre F).left y J = val (LB.mulGen D.toPre.P.L _ _ _ _ (p.g.s (star a • χ)) w)
      (DegPre.zF D.toPre F ≫ fst (TF (R := V) F) D.toPre.P.A).left y J := by
    rw [(gen_phi hG p w hw (star a • χ)).2 Φ hΦ hcΦ _ (DegPre.zF D.toPre F) y J hJ, hu1]
    exact one_mul _
  rw [val_mul hJ, val_pull hJ, val_mul hJ, val_pull hJ,
    hΦv,
    CanonicalLiftValuation.pull_val_chi hG oa a 1 N χ uχ huχ hc u0 hu0 hc0 r hr hr0 _ _ y J hJ, val_pull hJ, hl, z1,
    Over.id_left, val_mul hJ, e5, e7, e1, e2, e3, ← e6]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end ReciprocityTheory.ChartRestriction.G.H1.CanonicalLiftOrigin
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  IsLocalRing

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.H1.CanonicalLiftFrobenius

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem sval_zero {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (hs : ∀ j, s.f j = 0) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) :
    sval s r z J = 0 := by
  unfold sval
  erw [hs (fun k => J (r ≫ φ k))]
  unfold gs
  split_ifs
  · erw [map_zero, map_zero]
  · rfl

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X]

theorem phi_fixes (hG : GlobalFnsSt) (oa : D.toPre.OAct O) (a : O) (N : ℕ) (p : QkPt D.toPre F (1 * N))
    (z : D.toPre.X) (hy : p.y = -(star a • z)) (hb : p.g.b ≫ oa.onB.act a = cP D.toPre _ (-z))
    (r : LB.Gen (LB.LinComb D.toPre.P.L (rosatiφ D.toPre.P.A (oa.onB.act (star a)) (oa.onB.act a)) rosatiε))
    (hr : r.IsGen)
    (hr0 : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ r (zero2 D.toPre.P.A)) (LB.oneGen D.toPre.P.L))
    (hrel : ∀ (χ : D.toPre.X) (y : (TF (R := V) F).left) J, Good D.toPre.P.L y J →
        val (p.g.s (star a • χ)) (𝟙 _) y J * val r (lift (DegPre.cF D.toPre F χ) p.g.b).left y J =
          val (D.toPre.tau (-z) χ) (𝟙 (TF (R := V) F).left ≫ jFK (R := V) F) y J)
    (u0 : LB.Gen (LB.LinComb D.toPre.P.L (pullφ D F oa a 0) (pullε 1 N))) (hu0 : u0.IsGen)
    (hc0 : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ u0 (DegPre.zF D.toPre F).left)
      (LB.pullGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK (1 * (N - 1))) (jFK (R := V) F)))
    (w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε (1 * N)))) (hw : w.IsGen)
    (hwv : ∀ (y : (TF (R := V) F).left) J, Good D.toPre.P.L y J → val w (𝟙 (TF (R := V) F).left) y J =
        val (LB.pullGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK (1 * (N - 1))) (jFK (R := V) F))
            (𝟙 (TF (R := V) F).left) y J *
          val (LB.pullGen D.toPre.P.L _ _ (LB.mulGen D.toPre.P.L _ _ _ _
            (GeneratorPullback.powGen D.toPre.P.L _ _ (D.toPre.psi (-z)) 1) (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK 1))
              (jFK (R := V) F)) (𝟙 (TF (R := V) F).left) y J *
          (val u0 (DegPre.zF D.toPre F ≫ DegPre.trPt D.toPre F p.g.b).left y J)⁻¹)
    (θ : Fam D.toPre F 1) (θα : Fam D.toPre F (1 * N)) (hpull : PullAl D F oa a 1 N θ θα) :
    PhiRel D.toPre F (1 * N) p w θα θα := by
  rw [phiRel_iff hG p w hw θα θα]
  intro a' β hβ T ρ z' J hJ
  by_cases ha : ∃ χ, a' = star a • χ
  · obtain ⟨χ, rfl⟩ := ha
    subst hβ
    have e3 : star a • χ + p.y = star a • (χ - z) := by rw [hy, smul_sub, sub_eq_add_neg]
    have e4 : χ + 1 • -z = χ - z := by rw [one_smul, sub_eq_add_neg]
    rw [e3]
    obtain ⟨uχz, huχz, hcz, hsz⟩ := hpull.1 (χ - z)
    obtain ⟨uχ, huχ, hc, hs⟩ := hpull.1 χ
    obtain ⟨⟨fe, hfe, hcfe⟩, -⟩ := gen_fe (D := D.toPre) (F := F) hG 1 (-z) χ
    obtain ⟨⟨Φ, hΦ, hcΦ⟩, hΦv⟩ := gen_phi hG p w hw (star a • χ)
    have s1 := (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ uχz).1 hsz _ ρ.left z' J hJ
    have s2 := (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ fe).1 (θ.fe (-z) χ fe hfe hcfe) _
      (ρ.left ≫ (aF D F oa a).left) z' J hJ
    rw [e4] at s2
    have s3 := (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ uχ).1 hs _ (ρ ≫ DegPre.trPt D.toPre F p.g.b).left z' J hJ
    have pt : (ρ ≫ DegPre.trPt D.toPre F p.g.b).left ≫ (aF D F oa a).left =
        (ρ.left ≫ (aF D F oa a).left) ≫ (DegPre.trF D.toPre F (-z)).left := by
      rw [← Over.comp_left, Category.assoc, CanonicalLiftEigen.tr_aF oa a p.g.b z hb, ← Category.assoc, Over.comp_left,
        Over.comp_left]
    have eig := CanonicalLiftEigen.eigen_of_origin hG oa a N p z hy hb χ uχ huχ uχz huχz fe hfe Φ hΦ
      (fun y J hJ => CanonicalLiftOrigin.origin hG oa a N p z r hr hr0 hrel u0 hu0 hc0 w hw hwv χ uχ huχ hc uχz hcz fe hcfe
        Φ hΦ hcΦ y J hJ) _ ρ.left z' J hJ
    have hΦρ := hΦv Φ hΦ hcΦ T ρ z' J hJ
    have eig' : (val fe (ρ.left ≫ (aF D F oa a).left) z' J).val * (val uχz ρ.left z' J).val =
        (val uχ (ρ ≫ DegPre.trPt D.toPre F p.g.b).left z' J).val * (val Φ ρ.left z' J).val := by
      rw [← Units.val_mul, ← Units.val_mul, _root_.mul_comm]
      exact congrArg Units.val eig.symm
    rw [s1, s2, s3, pt, ← hΦρ, _root_.mul_assoc, _root_.mul_assoc, eig']
  · have hβn : ∀ χ, β ≠ star a • χ := by
      intro χ h
      apply ha
      refine ⟨χ + z, ?_⟩
      rw [smul_add, ← h, ← hβ, hy]
      abel
    rw [sval_zero _ (hpull.2 β hβn), sval_zero _ (hpull.2 a' (fun χ h => ha ⟨χ, h⟩)), MulZeroClass.zero_mul]

end ReciprocityTheory.ChartRestriction.G.H1.CanonicalLiftFrobenius
