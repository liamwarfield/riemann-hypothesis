module

public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.IntChartPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LiePush
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.ChartSer
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsSecondPartialLaw

@[expose] public section

section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBPrim
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.GermB

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun

attribute [local instance] Over.cartesianMonoidalCategory

section Base

variable {X : Scheme.{0}} (L : LB X) {K : Type} [Fintype K]

def divLinB (φ : K → (X ⟶ X)) (ε : K → ℤ) (w : LB.Gen (LB.div (LB.LinComb L φ ε) L)) :
    LB.Gen (LB.LinComb L (Sum.elim (fun _ : Fin 1 => 𝟙 X) φ) (Sum.elim (fun _ => 1) fun k => -ε k)) :=
  ⟨fun j => res (fun _ hy => ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inr k),
      Set.mem_iInter.1 hy (Sum.inl 0)⟩ :
    LB.wchart L (Sum.elim (fun _ : Fin 1 => 𝟙 X) φ) j ≤ (LB.div (LB.LinComb L φ ε) L).U (j ∘ Sum.inr, j (Sum.inl 0)))
    (w.s (j ∘ Sum.inr, j (Sum.inl 0)))⁻¹⟩

theorem divLinB_isGen (φ : K → (X ⟶ X)) (ε : K → ℤ) (w : LB.Gen (LB.div (LB.LinComb L φ ε) L)) (hw : w.IsGen) :
    (divLinB L φ ε w).IsGen := fun i j => unit_ext fun y hy => by
  have le : ∀ j : Fin 1 ⊕ K → L.ι, LB.wchart L (Sum.elim (fun _ : Fin 1 => 𝟙 X) φ) j ≤
      (LB.div (LB.LinComb L φ ε) L).U (j ∘ Sum.inr, j (Sum.inl 0)) := fun _ _ hy =>
    ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inr k), Set.mem_iInter.1 hy (Sum.inl 0)⟩
  have hi := le i hy.1
  have hj := le j hy.2
  have hij : (𝟙 X : X ⟶ X) y ∈ (LB.div (LB.LinComb L φ ε) L).U (i ∘ Sum.inr, i (Sum.inl 0)) ⊓
      (LB.div (LB.LinComb L φ ε) L).U (j ∘ Sum.inr, j (Sum.inl 0)) := ⟨hi, hj⟩
  have hw' := (gm_res (𝟙 X) y _ hij _).symm.trans ((congrArg (gm (𝟙 X) y _) (hw (i ∘ Sum.inr, i (Sum.inl 0))
    (j ∘ Sum.inr, j (Sum.inl 0)))).trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) rfl (gm_res (𝟙 X) y _ hij _))))
  have hg : gm (𝟙 X) y _ ((LB.div (LB.LinComb L φ ε) L).g (i ∘ Sum.inr, i (Sum.inl 0)) (j ∘ Sum.inr, j (Sum.inl 0))) =
      (gm (𝟙 X) y _ ((LB.LinComb L (Sum.elim (fun _ : Fin 1 => 𝟙 X) φ) (Sum.elim (fun _ => 1) fun k => -ε k)).g i j))⁻¹ := by
    refine (map_mul _ _ _).trans ?_
    refine Eq.trans (congrArg₂ (· * ·) ((gm_res _ y _ hij _).trans (gm_linComb L φ ε (𝟙 _) y _ _ hi.1 hj.1))
      ((map_inv _ _).trans (congrArg _ (gm_res _ y _ hij _)))) ?_
    refine Eq.trans ?_ (congrArg _ (gm_linComb L _ _ (𝟙 _) y i j hy.1 hy.2)).symm
    rw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, Fin.prod_univ_one, zpow_one,
      Category.comp_id, Category.id_comp, mul_inv_rev, inv_inv]
    rfl
  refine (gm_res _ y _ hy _).trans ((gm_res _ y _ hy.1 _).trans ((map_inv _ _).trans ?_))
  refine Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·) rfl ((gm_res _ y _ hy _).trans
    ((gm_res _ y _ hy.2 _).trans (map_inv _ _))))).symm
  exact (congrArg (·⁻¹) (hw'.trans (congrArg (· * _) hg))).trans
    (by simp only [mul_inv_rev, inv_inv]; exact _root_.mul_comm _ _)

end Base

section Tools

theorem prod_cube3 {X0 : Scheme.{0}} (G : Over X0) [GrpObj G] [IsCommMonObj G] {T : Over X0} {M : Type} [CommGroup M]
    (h : (T ⟶ G) → M) (xs : Fin 3 → (T ⟶ G)) :
    ∏ I : thK, h (psum G xs I.down) ^ thε I =
      (h 1)⁻¹ * h (xs 0 * 1) * h (xs 1 * 1) * h (xs 2 * 1) * (h (xs 0 * (xs 1 * 1)))⁻¹ * (h (xs 0 * (xs 2 * 1)))⁻¹ *
        (h (xs 1 * (xs 2 * 1)))⁻¹ * h (xs 0 * (xs 1 * (xs 2 * 1))) := _root_.GlobalTheory.SecondPartialLaw.prod_cube3 (X0 := X0) (T := T) (M := M) G h xs

theorem eta_one {X0 : Scheme.{0}} (G : Over X0) [GrpObj G] : (η[G] : 𝟙_ (Over X0) ⟶ G) = 1 := by
  show η[G] = toUnit _ ≫ η[G]
  rw [toUnit_unique (toUnit (𝟙_ (Over X0))) (𝟙 _), Category.id_comp]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)

theorem scale_isGen {Y : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ t.G.left)) (ε : K → ℤ) (u : Γ(Y, ⊤)ˣ)
    (g : LB.Gen (LB.LinComb t.PP.L φ ε)) (hg : g.IsGen) : (scaleGenG t φ ε u g).IsGen := fun i j =>
  unit_ext fun y hy => by
    have e := (gm_res (𝟙 Y) y _ hy _).symm.trans ((congrArg (gm (𝟙 Y) y _) (hg i j)).trans ((map_mul _ _ _).trans
      (congrArg₂ (· * ·) rfl (gm_res (𝟙 Y) y _ hy _))))
    refine (gm_res _ y _ hy _).trans ((map_mul _ _ _).trans ?_)
    refine Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·) rfl ((gm_res _ y _ hy _).trans (map_mul _ _ _)))).symm
    refine (congrArg₂ (· * ·) (gm_res _ y le_top hy.1 u) e).trans ?_
    refine Eq.trans ?_ (congrArg₂ (· * ·) rfl (congrArg₂ (· * ·) (gm_res _ y le_top hy.2 u).symm rfl))
    exact _root_.mul_left_comm _ _ _

theorem val_rigT {S0 : Scheme.{0}} (A : Over S0) [GrpObj A] (L : LB A.left) (rig : LB.Gen (L.pull (eSec A)))
    (T : Over S0) {Z : Scheme.{0}} (r : Z ⟶ T.left) (z : Z) (J : (Z ⟶ A.left) → L.ι) (hJ : Good L z J) :
    val (rigT A L rig T 1) r z J = val rig (r ≫ T.hom) z J := by
  rw [val_of rig (r ≫ T.hom) z J (fun _ => J (r ≫ T.hom ≫ eSec A)) (fun _ => by rw [Category.assoc])]
  have hm := hJ.mem (fun _ : Fin 1 => T.hom ≫ eSec A) r
  refine (map_zpow _ _ _).trans ((zpow_one _).trans ((gm_res r z _ hm _).trans ?_))
  exact gm_pull r T.hom z _ (show T.hom (r z) ∈ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => J (r ≫ T.hom ≫ eSec A)) from
    Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hm 0) _

end Tools

section Prim

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)

abbrev zz : 𝟙_ (Over X0) ⟶ t.G ⊗ t.G := lift (η[t.G] : 𝟙_ (Over X0) ⟶ t.G) (η[t.G] : 𝟙_ (Over X0) ⟶ t.G)

theorem cube_one_left {T : Over X0} {M : Type} [CommGroup M] (h : (T ⟶ t.G) → M) (b : T ⟶ t.G) :
    ∏ I : ULift (Finset (Fin 2)), h (psum t.G ![1, b] I.down) ^ cε 2 I = 1 := by
  rw [prod_cube2]
  simp

theorem cube_one_right {T : Over X0} {M : Type} [CommGroup M] (h : (T ⟶ t.G) → M) (b : T ⟶ t.G) :
    ∏ I : ULift (Finset (Fin 2)), h (psum t.G ![b, 1] I.down) ^ cε 2 I = 1 := by
  rw [prod_cube2]
  simp

theorem exists_wP : ∃ wP : PrimTyG t, IsPrimG t wP := by
  have hL := t.PP.isLB
  obtain ⟨w, hw⟩ := t.prim
  let w1 : PrimTyG t := divLinB t.PP.L _ _ w
  have hw1 : w1.IsGen := divLinB_isGen t.PP.L _ _ w hw
  have hpt : ∀ I : ULift.{0} (Finset (Fin 2)), eSec t.G ≫ cφG t ![𝟙 t.G, t.act.act H.w0] I =
      (psum t.G ![1, η[t.G] ≫ t.act.act H.w0] I.down).left := by
    intro I
    simp only [cφG, eSec, ← Over.comp_left]
    refine congrArg Over.Hom.left ((psum_hom (preHom _) _ I.down).trans ?_)
    refine congrArg (fun f => psum t.G f I.down) (funext fun i => ?_)
    fin_cases i
    · exact (Category.comp_id _).trans (eta_one t.G)
    · rfl
  obtain ⟨u, hu⟩ := exists_ratio t.PP.L hL (φ' := fun _ : PUnit => eSec t.G) (ε' := fun _ => 1)
    (fun U _ h => by
      rw [Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_one, Category.comp_id, zpow_neg, Finset.prod_inv_distrib,
        hpt, Fintype.prod_unique]
      rw [cube_one_left t (fun p => h p.left), inv_one, _root_.mul_one])
    (LB.pullGen t.PP.L _ _ w1 (eSec t.G)) (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ _ hw1 _) t.PP.rig t.PP.rigGen
  have hes : eSec t.G ≫ t.G.hom = 𝟙 _ := Over.w η[t.G]
  refine ⟨scaleGenG t _ _ (pullU t.G.hom ⊤ u⁻¹) w1, scale_isGen t _ _ _ w1 hw1, corr_of_val hL fun y J hJ => ?_⟩
  refine (val_pull hJ _ _ _).trans ((val_scale t _ _ _ _ _ y J hJ).trans ?_)
  refine (congrArg₂ (· * ·) ((gm_pull (𝟙 _ ≫ eSec t.G) t.G.hom y ⊤ trivial u⁻¹).trans
    (congrArg (fun r => gm r y ⊤ u⁻¹) (by rw [Category.assoc, hes, Category.comp_id])))
    ((val_pull hJ w1 _ _).symm.trans (hu _ (𝟙 _) y J hJ))).trans ?_
  rw [map_inv, inv_mul_cancel_left]

theorem exists_wL (a : 𝓞 E) : ∃ wL : LB.Gen (LB.LinComb t.PP.L
      (Sum.elim (cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)]) (cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G]))
      (Sum.elim (cε 2) fun I => -cε 2 I)), wL.IsGen ∧
    ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over X0)).left) (z : Z) (J : (Z ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J →
      val wL (r ≫ (zz t).left) z J = 1 := by
  have hL := t.PP.isLB
  obtain ⟨w, hw⟩ := t.adj a
  let w2 := divLin t.PP.L (cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)]) (cε 2)
    (cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G]) (cε 2) w
  have hw2 : w2.IsGen := divLin_isGen t.PP.L _ _ _ _ w hw
  have hp1 : ∀ I : ULift.{0} (Finset (Fin 2)), (zz t).left ≫ cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)] I =
      (psum t.G ![1, η[t.G] ≫ t.act.act (H.bar a)] I.down).left := by
    intro I
    simp only [cφG, ← Over.comp_left]
    refine congrArg Over.Hom.left ((psum_hom (preHom _) _ I.down).trans ?_)
    refine congrArg (fun f => psum t.G f I.down) (funext fun i => ?_)
    fin_cases i
    · show zz t ≫ fst t.G t.G = 1
      exact (lift_fst _ _).trans (eta_one t.G)
    · show zz t ≫ (snd t.G t.G ≫ t.act.act (H.bar a)) = η[t.G] ≫ t.act.act (H.bar a)
      exact lift_snd_assoc _ _ _
  have hp2 : ∀ I : ULift.{0} (Finset (Fin 2)), (zz t).left ≫ cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G] I =
      (psum t.G ![η[t.G] ≫ t.act.act a, 1] I.down).left := by
    intro I
    simp only [cφG, ← Over.comp_left]
    refine congrArg Over.Hom.left ((psum_hom (preHom _) _ I.down).trans ?_)
    refine congrArg (fun f => psum t.G f I.down) (funext fun i => ?_)
    fin_cases i
    · show zz t ≫ (fst t.G t.G ≫ t.act.act a) = η[t.G] ≫ t.act.act a
      exact lift_fst_assoc _ _ _
    · show zz t ≫ snd t.G t.G = 1
      exact (lift_snd _ _).trans (eta_one t.G)
  obtain ⟨s, -, hv⟩ := exists_gen hL (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      rw [Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, hp1, hp2, Fintype.prod_empty]
      rw [cube_one_left t (fun p => h p.left), cube_one_right t (fun p => h p.left), inv_one, _root_.mul_one])
    (LB.pullGen t.PP.L _ _ w2 (zz t).left) (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ _ hw2 _)
  have le : (⊤ : ((𝟙_ (Over X0)).left).Opens) ≤ LB.wchart t.PP.L (PEmpty.elim : PEmpty → (_ ⟶ t.G.left)) PEmpty.elim :=
    fun _ _ => Set.mem_iInter.2 fun k => k.elim
  let u := res le (s.s PEmpty.elim)
  have hz : (zz t).left ≫ (t.G ⊗ t.G).hom = 𝟙 _ := Over.w (zz t)
  refine ⟨scaleGenG t _ _ (pullU (t.G ⊗ t.G).hom ⊤ u⁻¹) w2, scale_isGen t _ _ _ w2 hw2, fun Z r z J hJ => ?_⟩
  refine (val_scale t _ _ _ _ _ z J hJ).trans ?_
  have e1 : val w2 (r ≫ (zz t).left) z J = gm r z ⊤ u := by
    refine (val_pull hJ w2 _ _).symm.trans ((hv Z r z J hJ).symm.trans ?_)
    rw [val_of s r z J PEmpty.elim (fun k => k.elim)]
    exact (gm_res r z le trivial _).symm
  refine (congrArg₂ (· * ·) ((gm_pull (r ≫ (zz t).left) (t.G ⊗ t.G).hom z ⊤ trivial u⁻¹).trans
    (congrArg (fun q => gm q z ⊤ u⁻¹) (by rw [Category.assoc, hz, Category.comp_id]))) e1).trans ?_
  rw [map_inv, inv_mul_cancel]

end Prim

end Formalism.MainNotions.ModuliIntegralCharts.H1.GermB
end
end

section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartJetSubPf
noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

theorem tan_coef {V K : Type} [CommRing V] [CommRing K] [Algebra V K] {d : ℕ} (j : Fin d) :
    (jetTan ((0 : Fin 1), j) : Jet K (Fin 1 × Fin d) (0 + 1) →ₐ[K] DualNumber K).toRingHom.comp
      (jetCoef (algebraMap V K) (Fin 1 × Fin d) 1) = (dualMap (algebraMap V K)).comp
      (jetTan ((0 : Fin 1), j) : Jet V (Fin 1 × Fin d) (0 + 1) →ₐ[V] DualNumber V).toRingHom := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro r
    show MvPolynomial.aeval _ (MvPolynomial.map _ (MvPolynomial.C r)) = dualMap _ (MvPolynomial.aeval _ (MvPolynomial.C r))
    rw [MvPolynomial.map_C, MvPolynomial.aeval_C, MvPolynomial.aeval_C]
    ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  · intro s
    show MvPolynomial.aeval _ (MvPolynomial.map _ (MvPolynomial.X s)) = dualMap _ (MvPolynomial.aeval _ (MvPolynomial.X s))
    rw [MvPolynomial.map_X, MvPolynomial.aeval_X, MvPolynomial.aeval_X]
    split_ifs <;> ext <;> simp [dualMap]

set_option maxHeartbeats 1000000 in
theorem chartJetTan_holds : ChartJetTanSt Xo c := by
  intro T io y I d FT actT tgT uvecT xT hb hc hu
  letI := io.toAlgebra
  have hid : IsGrpPullback I.G.G I.G.G (𝟙 _) (𝟙 _) := ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy =>
    (mul_left_congr (Category.comp_id _) x₀ y₀ x y (hx.trans (Category.comp_id _)) (hy.trans (Category.comp_id _))).trans
      (Category.comp_id _).symm⟩
  let D : Fin d → (epsR T.V ⟶ I.G.G) := fun j => Over.homMk (Formalism.L2.Pj.homAt (𝟙 (Sp T.V))
    (jetTan ((0 : Fin 1), j) : Jet T.V (Fin 1 × Fin d) (0 + 1) →ₐ[T.V] DualNumber T.V) ≫ xT 1).left
    ((Over.w _).trans (Category.comp_id _))
  let D' : Fin d → (epsR T.Fr ⟶ I.t'.G) := fun j => Over.homMk (spMap ((jetTan ((0 : Fin 1), j) :
    Jet T.Fr (Fin 1 × Fin d) (0 + 1) →ₐ[T.Fr] DualNumber T.Fr) : _ →+* _) ≫ JetTr.xL I xT 1) (by
      rw [Category.assoc, JetTr.xL_snd]; exact spMap_comp_alg _)
  have hD : ∀ j, (D' j).left ≫ I.m2.φ = spMap (dualMap (algebraMap T.V T.Fr)) ≫ (D j).left := fun j => by
    refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (JetTr.xL_fst I xT 1)).trans ((Category.assoc _ _ _).symm.trans
      (Eq.trans (congrArg (· ≫ (xT 1).left) ?_) (Category.assoc _ _ _))))
    exact (JetTr.spMap_comp' _ _).trans ((congrArg spMap (tan_coef j)).trans (JetTr.spMap_comp' _ _).symm)
  choose u' h₁ h₂ using I.lift
  have ho : ∀ τ i, u' τ i ≫ I.t'.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) := fun τ i => by
    have : Mono (spMap (algebraMap T.V T.Fr)) := by
      have := IsPreimmersion.of_isLocalization (S := T.Fr) (nonZeroDivisors T.V)
      exact inferInstanceAs (Mono (Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr))))
    rw [← cancel_mono (spMap (algebraMap T.V T.Fr)), Category.assoc, ← I.m2.cart.1.w, ← Category.assoc, h₂, Category.assoc,
      Over.w]
    exact (JetTr.spMap_comp' _ _).trans ((congrArg spMap (RingHom.ext fun r => by
      ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl])).trans (JetTr.spMap_comp' _ _).symm)
  let U' : Lt1 Dw → (epsR T.Fr ⟶ I.t'.G) := fun ℓ => Over.homMk (u' ℓ.1 ℓ.2) (ho _ _)
  have cb : ∀ ℓ, IsLieComb (fun i => algebraMap T.V T.Fr (uvecT ℓ i)) D' (U' ℓ) := fun ℓ =>
    Chart.comb_baseChange _ I.m2.cart (w := Over.homMk (I.ub ℓ.1 ℓ.2).left (Over.w (I.ub ℓ.1 ℓ.2)))
      ((Chart.comb_push hid _ D _).2 (by simp only [Category.comp_id]; exact hu ℓ)) hD (h₂ _ _)
  intro ℓ
  obtain ⟨u, a₁, a₂⟩ := (Chart.comb_push I.m1.cart _ _ _).1 (cb ℓ)
  exact ⟨u, fun i => (a₁ i).trans (congrArg (_ ≫ ·) (Category.assoc _ _ _)), a₂.trans (h₁ _ _)⟩

set_option maxHeartbeats 1000000 in
theorem chartJetBasis_holds (hF : FrTanBasisSt Xo c) : ChartJetBasisSt Xo c := by
  intro T io y I d FT actT tgT uvecT xT hb hc hu
  letI := io.toAlgebra
  have hid : IsGrpPullback I.G.G I.G.G (𝟙 _) (𝟙 _) := ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy =>
    (mul_left_congr (Category.comp_id _) x₀ y₀ x y (hx.trans (Category.comp_id _)) (hy.trans (Category.comp_id _))).trans
      (Category.comp_id _).symm⟩
  let D : Fin d → (epsR T.V ⟶ I.G.G) := fun j => Over.homMk (Formalism.L2.Pj.homAt (𝟙 (Sp T.V))
    (jetTan ((0 : Fin 1), j) : Jet T.V (Fin 1 × Fin d) (0 + 1) →ₐ[T.V] DualNumber T.V) ≫ xT 1).left
    ((Over.w _).trans (Category.comp_id _))
  let D' : Fin d → (epsR T.Fr ⟶ I.t'.G) := fun j => Over.homMk (spMap ((jetTan ((0 : Fin 1), j) :
    Jet T.Fr (Fin 1 × Fin d) (0 + 1) →ₐ[T.Fr] DualNumber T.Fr) : _ →+* _) ≫ JetTr.xL I xT 1) (by
      rw [Category.assoc, JetTr.xL_snd]; exact spMap_comp_alg _)
  have hD : ∀ j, (D' j).left ≫ I.m2.φ = spMap (dualMap (algebraMap T.V T.Fr)) ≫ (D j).left := fun j => by
    refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (JetTr.xL_fst I xT 1)).trans ((Category.assoc _ _ _).symm.trans
      (Eq.trans (congrArg (· ≫ (xT 1).left) ?_) (Category.assoc _ _ _))))
    exact (JetTr.spMap_comp' _ _).trans ((congrArg spMap (tan_coef j)).trans (JetTr.spMap_comp' _ _).symm)
  choose u' h₁ h₂ using I.lift
  have ho : ∀ τ i, u' τ i ≫ I.t'.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) := fun τ i => by
    have : Mono (spMap (algebraMap T.V T.Fr)) := by
      have := IsPreimmersion.of_isLocalization (S := T.Fr) (nonZeroDivisors T.V)
      exact inferInstanceAs (Mono (Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr))))
    rw [← cancel_mono (spMap (algebraMap T.V T.Fr)), Category.assoc, ← I.m2.cart.1.w, ← Category.assoc, h₂, Category.assoc,
      Over.w]
    exact (JetTr.spMap_comp' _ _).trans ((congrArg spMap (RingHom.ext fun r => by
      ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl])).trans (JetTr.spMap_comp' _ _).symm)
  let U' : Lt1 Dw → (epsR T.Fr ⟶ I.t'.G) := fun ℓ => Over.homMk (u' ℓ.1 ℓ.2) (ho _ _)
  have cb : ∀ ℓ, IsLieComb (fun i => algebraMap T.V T.Fr (uvecT ℓ i)) D' (U' ℓ) := fun ℓ =>
    Chart.comb_baseChange _ I.m2.cart (w := Over.homMk (I.ub ℓ.1 ℓ.2).left (Over.w (I.ub ℓ.1 ℓ.2)))
      ((Chart.comb_push hid _ D _).2 (by simp only [Category.comp_id]; exact hu ℓ)) hD (h₂ _ _)
  have := I.G.semi.smooth
  have := I.t'.semi.smooth
  let tg : Fin d → (epsR T.V ⟶ I.G.G) := fun j => Over.homMk (tgT j) ((hb.1 j).1.trans (Category.comp_id _))
  have ttg : ∀ j, IsTangent (tg j) := fun j => (Chart.tan_push hid _).2 (by simp only [Category.comp_id]; exact (hb.1 j).2)
  have tD : ∀ j, IsTangent (D j) := fun j => (Chart.tan_push hid _).2 (by
    have e := congrArg (fun q => q.left) (hc.zero 1)
    refine Eq.trans ?_ (e.trans ?_)
    · rw [Category.comp_id]
      refine (Category.assoc _ _ _).symm.trans (congrArg (· ≫ (xT 1).left) ((JetTr.spMap_comp' _ _).trans (congrArg spMap ?_)))
      apply Ideal.Quotient.ringHom_ext
      apply MvPolynomial.ringHom_ext
      · intro r
        show (MvPolynomial.aeval _ (MvPolynomial.C r) : DualNumber T.V).fst = MvPolynomial.aeval _ (MvPolynomial.C r)
        rw [MvPolynomial.aeval_C, MvPolynomial.aeval_C]; rfl
      · intro s
        show (MvPolynomial.aeval _ (MvPolynomial.X s) : DualNumber T.V).fst = MvPolynomial.aeval _ (MvPolynomial.X s)
        rw [MvPolynomial.aeval_X, MvPolynomial.aeval_X]
        split_ifs <;> rfl
    · exact congrArg (· ≫ _) (show Spec.map (CommRingCat.ofHom (RingHom.id T.V)) ≫ 𝟙 _ = 𝟙 _ by simp))
  have eD : tg = D := funext fun j => Chart.eq_of_comb_single tD (ttg j) j
    ((Chart.comb_push hid _ D _).2 (by simp only [Category.comp_id]; exact hc.tan j))
  have bD : IsLieBasis D := eD ▸ ⟨ttg, fun w hw => by
    have := hb.2 w.left ⟨(Over.w w).trans (Category.comp_id _).symm, by
      simpa only [Category.comp_id] using (Chart.tan_push hid w).1 hw⟩
    simp only [Chart.comb_push hid, Category.comp_id]
    exact this⟩
  have bD' : IsLieBasis D' := Chart.isLieBasis_baseChange _ I.m2.cart bD hD
  let e := Fintype.equivFin (Lt1 Dw)
  have bU : IsLieBasis fun i => U' (e.symm i) := ⟨fun i => (Chart.tan_push I.m1.cart _).2
    ((congrArg (_ ≫ ·) (h₁ _ _)).trans (y.1.tan _ _).2), fun w hw => by
      obtain ⟨a, ha, hq⟩ := hF T.Fr y.1 (w.left ≫ I.m1.φ) ⟨Over.w (pushPt I.m1.cart.1.w w), (Chart.tan_push I.m1.cart w).1 hw⟩
      have k : ∀ b, IsLieComb b (fun i => U' (e.symm i)) w ↔ IsCombAt y.1.x (fun i => y.1.u (e.symm i).1 (e.symm i).2) b
          (w.left ≫ I.m1.φ) := fun b => (Chart.comb_push I.m1.cart _ _ _).trans (exists_congr fun u => and_congr_left'
        (forall_congr' fun i => Eq.congr_right (congrArg (_ ≫ ·) (h₁ _ _))))
      refine ⟨fun i => a (e.symm i), (k _).2 ha, fun b hb' => ?_⟩
      have := hq (fun ℓ => b (e ℓ)) (by simpa only [e, Equiv.apply_symm_apply] using (k b).1 hb')
      funext i; rw [← this]; simp⟩
  intro v
  obtain ⟨a, ha, hq⟩ := Chart.coords_basis bD' bU _ (fun i => cb (e.symm i)) v
  refine ⟨fun ℓ => a (e ℓ), fun j => (Fintype.sum_equiv e _ _ fun ℓ => by simp).trans (ha j), fun b hb' => ?_⟩
  have := hq (fun i => b (e.symm i)) fun j => (Fintype.sum_equiv e.symm _ _ fun i => rfl).trans (hb' j)
  funext ℓ; rw [← this]; simp

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartJetTrPf
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

set_option maxHeartbeats 1000000 in
theorem chartJetTr_of (hTan : ChartJetTanSt Xo c) (hBas : ChartJetBasisSt Xo c) : ChartJetTrSt Xo c := by
  intro T io y I d FT actT tgT uvecT xT hbas hch hdir
  letI := io.toAlgebra
  refine ⟨xU I xT, xP I xT, ⟨fun m => ?_, fun m => ?_, fun m => ?_, fun m a => ?_,
    hTan T io y I d FT actT tgT uvecT xT hbas hch hdir, hBas T io y I d FT actT tgT uvecT xT hbas hch hdir⟩,
    fun m => xL_fst I xT m, fun m => rfl⟩
  ·
    apply Over.OverMorphism.ext
    show spMap _ ≫ xL I xT m ≫ I.m1.φ = (spMap (algebraMap T.Fr T.Fr) ≫ y.1.x) ≫ η[Xo.univ.t.G].left
    rw [← Category.assoc, xL_zero I xT hch.zero m, unit_push I.m1.cart, spMap_alg_self, Category.id_comp]
  ·
    apply Over.OverMorphism.ext
    show spMap _ ≫ xL I xT (m + 1) ≫ I.m1.φ = xL I xT m ≫ I.m1.φ
    rw [← Category.assoc, xL_trunc I xT hch.trunc m]
  ·
    simp only [psTrunc_map]
    let W : (jO y.1 d m 2) ⟶ Over.mk ((jOG (𝟙 (Sp T.Fr)) d m 2).hom ≫ y.1.x) :=
      Over.homMk (𝟙 _) (by
        show 𝟙 _ ≫ (spMap _ ≫ 𝟙 _) ≫ y.1.x = spMap _ ≫ y.1.x
        simp)
    have hj : ∀ i : Fin 2, jpt y.1 d (xU I xT) m i =
        W ≫ pushHom I.m1.cart _ (jptG I.t' (𝟙 (Sp T.Fr)) d (xP I xT) m i) := fun i =>
      Over.OverMorphism.ext (by
        show spMap _ ≫ xL I xT m ≫ I.m1.φ = 𝟙 _ ≫ (spMap _ ≫ xL I xT m) ≫ I.m1.φ
        simp)
    rw [hj 0, hj 1, ← MonObj.comp_mul, ← map_mul, ← xP_law I xT FT m (hch.law m)]
    apply Over.OverMorphism.ext
    show spMap _ ≫ xL I xT m ≫ I.m1.φ = 𝟙 _ ≫ (spMap _ ≫ xL I xT m) ≫ I.m1.φ
    simp
  ·
    simp only [psTrunc_map]
    apply Over.OverMorphism.ext
    show (xL I xT m ≫ I.m1.φ) ≫ (Xo.univ.t.act.act a).left = spMap _ ≫ xL I xT m ≫ I.m1.φ
    rw [Category.assoc, ← I.m1.act a, ← Category.assoc, xL_act I xT (actT a) a m (hch.act m a), Category.assoc]

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartDataPf
noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.TB.Canon
open scoped CategoryTheory.Obj

private theorem mem_degLE_lemma {κ : Type} [Fintype κ] [DecidableEq κ] (m : ℕ) (e : κ →₀ ℕ) :
    e ∈ degLE m ↔ Finsupp.degree e ≤ m := by
  constructor
  · intro he
    simp [degLE] at he
    exact he.2
  · intro hd
    have hle : ∀ i, e i ≤ m := by
      intro i
      refine le_trans ?_ hd
      by_cases hi : i ∈ e.support
      · exact Finset.single_le_sum (f := fun j => e j) (fun j _ => Nat.zero_le _) hi
      · have h0 : e i = 0 := by simpa using hi
        omega
    simp [degLE]
    refine ⟨⟨fun i => ⟨e i, Nat.lt_succ_of_le (hle i)⟩, ?_⟩, hd⟩
    ext i
    simp

theorem mk_psTrunc {S : Type} [CommRing S] {κ : Type} [Fintype κ] [DecidableEq κ] (m : ℕ) (f : MvPowerSeries κ S)
    (hf : MvPowerSeries.constantCoeff f = 0) :
    Chart.pj m f = Ideal.Quotient.mk _ (psTrunc m f - MvPolynomial.C (MvPolynomial.constantCoeff (psTrunc m f))) := by
  have h0 : MvPolynomial.constantCoeff (psTrunc m f) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [psTrunc, map_sum, MvPolynomial.constantCoeff_monomial]
    refine Finset.sum_eq_zero fun x _ => ?_
    split_ifs with hx
    · rw [hx, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf]
    · rfl
  rw [h0, map_zero, sub_zero]
  unfold Chart.pj
  congr 1
  ext e
  simp only [psTrunc, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with he
  · have hd : Finsupp.degree e ≤ m := (mem_degLE_lemma m e).1 he
    rw [MvPowerSeries.coeff_truncTotal]
    omega
  · have hd : ¬ Finsupp.degree e ≤ m := fun h => he ((mem_degLE_lemma m e).2 h)
    first
      | rw [MvPowerSeries.coeff_truncTotal_eq_zero]; omega
      | simp [MvPowerSeries.truncTotal, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]; omega

theorem jetMap_zR {S : Type} [CommRing S] {κ κ' : Type} (m : ℕ) (φ : κ → MvPolynomial κ' S) (h) (s : κ) :
    (jetMap φ h : Jet S κ m →ₐ[S] Jet S κ' m) (Ideal.Quotient.mk _ (MvPolynomial.X s)) = Ideal.Quotient.mk _ (φ s) := by
  simp only [jetMap]
  show ((Ideal.Quotient.mkₐ S (orig S κ' ^ (m + 1))).comp (MvPolynomial.bind₁ φ)) (MvPolynomial.X s) = _
  simp

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end
