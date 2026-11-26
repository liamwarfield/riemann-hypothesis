module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LiePush
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullbackFactor
public import ReciprocityTheory.AdicCompleteness.IsAdicCompleteComapConstantCoeff

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem prod_gt (b : TF (R := R) F ⟶ D.P.A) (χ : D.X) {U : Type} [CommGroup U] (h : ((TF (R := R) F).left ⟶ D.P.A.left) → U) :
    ∏ i, h (DegPre.gtφ D F b χ i) ^ DegPre.gtε i =
      (h (cP D _ χ * b).left)⁻¹ * h (cP D _ χ).left * h b.left * (h (1 : TF (R := R) F ⟶ D.P.A).left)⁻¹ := by
  rw [Fin.prod_univ_four]
  simp [DegPre.gtφ, DegPre.gtε] <;> rfl

theorem cPoint_zero (T : Over (Spec (CommRingCat.of R))) : cP D T 0 = 1 := by
  have h0 : D.c 0 = 1 := by
    have e := D.c_add 0 0
    rw [add_zero] at e
    have e' : D.c 0 * D.c 0 = D.c 0 * 1 := by
      rw [_root_.mul_one]
      exact e.symm
    exact _root_.mul_left_cancel e'
  unfold cP
  rw [h0]
  first
  | simp
  | (rw [Hom.one_def, Hom.one_def, ← Category.assoc]
     congr 1
     exact toUnit_unique _ _)

theorem val_cubAt {y : (TF (R := R) F).left} {J} (hJ : Good D.P.L y J) (x x' w : TF (R := R) F ⟶ D.P.A) :
    val (DegPre.cubAt D F x x' w) (𝟙 _) y J = th D y J x x' w := by
  unfold DegPre.cubAt
  refine (val_pull (hJ := hJ) ..).trans ?_
  rw [Category.id_comp]
  rfl

theorem exists_gt (b : TF (R := R) F ⟶ D.P.A) {K : Type} [Fintype K] {φ : D.X → K → ((TF (R := R) F).left ⟶ D.P.A.left)}
    {ε : K → ℤ} (v : ∀ χ, LB.Gen (LB.LinComb D.P.L (φ χ) ε)) (hv : ∀ χ, (v χ).IsGen)
    (hF : ∀ χ, FormEq (φ χ) ε (DegPre.gtφ D F b χ) DegPre.gtε)
    (h₀ : ∀ y J, Good D.P.L y J → val (v 0) (𝟙 _) y J = 1)
    (hm : ∀ χ χ' y J, Good D.P.L y J → val (v (χ + χ')) (𝟙 _) y J * th D y J (cP D _ χ) (cP D _ χ') b =
      val (v χ) (𝟙 _) y J * val (v χ') (𝟙 _) y J) :
    ∃ g : GtPtF D F, g.b = b ∧ ∀ χ y J, Good D.P.L y J → val (g.s χ) (𝟙 _) y J = val (v χ) (𝟙 _) y J := by
  choose s hs hsv using fun χ => exists_gen D.P.isLB (hF χ) (v χ) (hv χ)
  refine ⟨{ b := b, s := s, isGen := hs, s_zero := ?_, mult := ?_ }, rfl, ?_⟩
  · refine corr_of_val D.P.isLB (fun y J hy => ?_)
    refine (hsv 0 _ (𝟙 _) y J hy).trans ?_
    exact (h₀ y J hy).trans (val_one _).symm
  · intro χ χ'
    refine corr_of_val D.P.isLB (fun y J hy => ?_)
    refine (val_mul (hJ := hy) ..).trans ?_
    refine Eq.trans ?_ (val_mul (hJ := hy) ..).symm
    rw [val_cubAt hy, hsv (χ + χ') _ (𝟙 _) y J hy, hsv χ _ (𝟙 _) y J hy, hsv χ' _ (𝟙 _) y J hy]
    exact hm χ χ' y J hy
  · intro χ y J hy
    exact hsv χ _ (𝟙 _) y J hy

theorem isAdd_iff (g g' g'' : GtPtF D F) : g.IsAdd g' g'' ↔ g''.b = g.b * g'.b ∧ ∀ χ y J, Good D.P.L y J →
    val (g''.s χ) (𝟙 _) y J * th D y J (cP D _ χ) g.b g'.b = val (g.s χ) (𝟙 _) y J * val (g'.s χ) (𝟙 _) y J := by
  constructor
  · rintro ⟨hb, hs⟩
    refine ⟨hb, fun χ y J hy => ?_⟩
    rw [← val_cubAt hy]
    refine (val_mul (hJ := hy) ..).symm.trans ?_
    refine (val_corr (hJ := hy) (hs χ) _).trans ?_
    exact val_mul (hJ := hy) ..
  · rintro ⟨hb, hs⟩
    refine ⟨hb, fun χ => corr_of_val D.P.isLB (fun y J hy => ?_)⟩
    refine (val_mul (hJ := hy) ..).trans ?_
    refine Eq.trans ?_ (val_mul (hJ := hy) ..).symm
    rw [val_cubAt hy]
    exact hs χ y J hy

theorem isZero_iff (g : GtPtF D F) : g.IsZero ↔ g.b = 1 ∧ ∀ χ y J, Good D.P.L y J → val (g.s χ) (𝟙 _) y J = 1 := by
  constructor
  · rintro ⟨hb, hs⟩
    exact ⟨hb, fun χ y J hy => (val_corr (hJ := hy) (hs χ) (𝟙 _)).trans (val_one _)⟩
  · rintro ⟨hb, hs⟩
    exact ⟨hb, fun χ => corr_of_val D.P.isLB (fun y J hy => (hs χ y J hy).trans (val_one _).symm)⟩

theorem isIota_iff (x : D.X) (g : GtPtF D F) : GtPtF.IsIota x g ↔ g.b = cP D _ x ∧ ∀ χ y J, Good D.P.L y J →
    val (g.s χ) (𝟙 _) y J = val (D.tau x χ) (𝟙 _ ≫ jFK (R := R) F) y J := by
  constructor
  · rintro ⟨hb, hs⟩
    refine ⟨hb, fun χ y J hy => ?_⟩
    refine (val_corr (hJ := hy) (hs χ) _).trans ?_
    exact val_pull (hJ := hy) ..
  · rintro ⟨hb, hs⟩
    refine ⟨hb, fun χ => corr_of_val D.P.isLB (fun y J hy => ?_)⟩
    refine (hs χ y J hy).trans ?_
    exact (val_pull (hJ := hy) ..).symm

private lemma th_eq_one' {y : (TF (R := R) F).left} {J} (hJ : Good D.P.L y J)
    (x x' : TF (R := R) F ⟶ D.P.A) : th D y J x x' 1 = 1 := by
  have hm : lift x (lift x' 1) = lift x x' ≫ faceMap (G := D.P.A) 2 := by
    simp [faceMap, x2, pzero, Hom.one_def]
  refine Eq.trans ?_ ((val_corr (hJ := hJ) (D.cub.face 2) (lift x x').left).trans (val_one _))
  refine Eq.trans ?_ (val_pull (hJ := hJ) ..).symm
  show val D.cub.t (lift x (lift x' 1)).left y J = _
  rw [hm, Over.comp_left]
  all_goals rfl

theorem exists_zero_gt : ∃ g : GtPtF D F, g.IsZero := by
  have hgen : (LB.oneGen D.P.L (Y := (TF (R := R) F).left)).IsGen := by
    intro i j
    first
    | exact (_root_.one_mul _).symm
    | (simp only [LB.oneGen, LB.LinComb, Finset.univ_eq_empty, Finset.prod_empty]
       exact (_root_.one_mul _).symm)
    | (simp [LB.oneGen, LB.LinComb]
       rw [_root_.one_mul])
  obtain ⟨g, hb, hg⟩ := exists_gt (D := D) (F := F) (1 : TF (R := R) F ⟶ D.P.A) (K := PEmpty)
    (φ := fun _ => PEmpty.elim) (ε := PEmpty.elim) (fun _ => LB.oneGen D.P.L) (fun _ => hgen)
    (fun χ => by
      intro U _ h
      rw [prod_gt]
      simp)
    (fun y J _ => val_one _)
    (fun χ χ' y J hy => by
      rw [th_eq_one' hy]
      congr 1
      exact (val_one _).symm)
  exact ⟨g, (isZero_iff g).2 ⟨hb, fun χ y J hy => (hg χ y J hy).trans (val_one _)⟩⟩

theorem qk_equiv_refl (hB : D.TauBimult) {k : ℕ} (q : QkPt D F k) : QkPt.Equiv D F q q := by
  obtain ⟨h, hh⟩ := exists_zero_gt (D := D) (F := F)
  obtain ⟨hb, hv⟩ := (isZero_iff h).1 hh
  refine ⟨0, by simp, h, (isIota_iff 0 h).2 ⟨hb.trans (cPoint_zero _).symm, fun χ y J hJ => ?_⟩,
    (isAdd_iff _ _ _).2 ⟨by rw [hb, _root_.mul_one], fun χ y J hJ => ?_⟩⟩
  · have C : IsCub (th D (T := TF (R := R) F) y J) := isCub_cubV D.cub hJ
    have t := tau_mul (𝟙 (TF (R := R) F)) hJ hB 0 0 χ
    rw [add_zero, cPoint_zero, C.face, _root_.mul_one] at t
    exact (hv χ y J hJ).trans (mul_eq_left.1 t.symm).symm
  · have C : IsCub (th D (T := TF (R := R) F) y J) := isCub_cubV D.cub hJ
    rw [hv χ y J hJ, hb, C.face₃]

variable {O : Type} [CommRing O] [StarRing O] [Module O D.X]

theorem qkAct_exists (hG : GlobalFnsSt) (hB : D.TauBimult) (oa : D.OAct O) {k : ℕ} (a : O) (p : QkPt D F k) :
    ∃ p', QkAct oa a p p' := by
  have := oa.onB.hom a
  have := oa.onB.hom (star a)
  have hr := oa.onB.rosati (star a)
  have hbal := oa.tau_bal (star a)
  rw [star_star] at hr hbal
  obtain ⟨u, hu, u₀⟩ := exists_ros hG D.P.isAb D.P.isLB _ _ hr
  have cf : ∀ (T) (x : O) χ, cP D T (x • χ) = cP D T χ ≫ oa.onB.act x := fun T x χ => by
    rw [cP, oa.c_lin, ← Category.assoc]; rfl
  have ra := fun {y : (TF (R := R) F).left} {J} (hJ : Good D.P.L y J) =>
    ros_add D.cub hG D.P.isAb _ _ u hu u₀ (T := TF (R := R) F) hJ
  have vu : ∀ {y : (TF (R := R) F).left} {J}, Good D.P.L y J → ∀ x w : TF (R := R) F ⟶ D.P.A,
      val (LB.pullGen D.P.L _ _ u (lift x w).left) (𝟙 _) y J = val₂ u y J x w := fun hJ x w => by
    rw [val_pull hJ, Category.id_comp]; rfl
  have u₁ : ∀ {y : (TF (R := R) F).left} {J}, Good D.P.L y J → ∀ w, val₂ u y J 1 w = 1 := fun {y J} hJ w => by
    have C : IsCub (cubV D.cub y J) := isCub_cubV D.cub hJ
    have e := (ra hJ 1 1 w).1
    rw [_root_.mul_one, MonObj.one_comp, C.face, C.face, _root_.mul_one, _root_.one_mul] at e
    exact mul_eq_left.1 e.symm
  have u₂ : ∀ {y : (TF (R := R) F).left} {J}, Good D.P.L y J → ∀ w, val₂ u y J w 1 = 1 := fun {y J} hJ w => by
    have C : IsCub (cubV D.cub y J) := isCub_cubV D.cub hJ
    have e := (ra hJ 1 1 w).2
    rw [_root_.mul_one, MonObj.one_comp, C.face₃, C.face₃, _root_.mul_one, _root_.one_mul] at e
    exact mul_eq_left.1 e.symm
  have ex : ∀ g : GtPtF D F, ∃ g' : GtPtF D F, g'.b = g.b ≫ oa.onB.act a ∧ ∀ χ y J, Good D.P.L y J →
      val (g'.s χ) (𝟙 _) y J = val (g.s (star a • χ)) (𝟙 _) y J * val₂ u y J (cP D _ χ) g.b := by
    intro g
    have vv : ∀ χ y J, Good D.P.L y J → val (LB.mulGen D.P.L _ _ _ _ (g.s (star a • χ))
        (LB.pullGen D.P.L _ _ u (lift (cP D _ χ) g.b).left)) (𝟙 _) y J =
        val (g.s (star a • χ)) (𝟙 _) y J * val₂ u y J (cP D _ χ) g.b := fun χ y J hJ =>
      (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (vu hJ _ _))
    obtain ⟨g', hb, hv⟩ := exists_gt (g.b ≫ oa.onB.act a) (fun χ => LB.mulGen D.P.L _ _ _ _ (g.s (star a • χ))
        (LB.pullGen D.P.L _ _ u (lift (cP D _ χ) g.b).left))
      (fun χ => mulGen_isGen _ _ _ _ _ _ _ (g.isGen _) (pullGen_isGen _ _ _ _ hu _)) (fun χ U _ h => by
        refine (prod_sum₂ (K := Fin 4) (K' := Fin 6) (U := U) _ (prod_gt g.b (star a • χ) h)
          (prod_ros _ _ (cP D _ χ) g.b h)).trans ?_
        rw [prod_gt, cf]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel) (fun y J hJ => by
        rw [vv 0 y J hJ, smul_zero, cPoint_zero, u₁ hJ, _root_.mul_one]
        exact (val_corr hJ g.s_zero _).trans (val_one _)) (fun χ χ' y J hJ => by
        have e₁ := (ra hJ (cP D _ χ) (cP D _ χ') g.b).1
        have e₂ := gt_mul (𝟙 (TF (R := R) F)) hJ g (star a • χ) (star a • χ')
        rw [Category.id_comp, cf, cf, Over.id_left] at e₂
        rw [vv _ y J hJ, vv _ y J hJ, vv _ y J hJ, smul_add, cPoint_add, _root_.mul_assoc]
        refine (congrArg _ e₁).trans ?_
        rw [← _root_.mul_assoc]
        exact (congrArg (· * _) e₂).trans (mul_mul_mul_comm _ _ _ _))
    exact ⟨g', hb, fun χ y J hJ => (hv χ y J hJ).trans (vv χ y J hJ)⟩
  choose act hb hv using ex
  have add : ∀ g g' g'' : GtPtF D F, g.IsAdd g' g'' → (act g).IsAdd (act g') (act g'') := fun g g' g'' h => by
    obtain ⟨b₁, v₁⟩ := (isAdd_iff _ _ _).1 h
    refine (isAdd_iff _ _ _).2 ⟨by rw [hb, hb, hb, b₁, MonObj.mul_comp], fun χ y J hJ => ?_⟩
    have e₁ := (ra hJ g.b g'.b (cP D _ χ)).2
    have e₂ := v₁ (star a • χ) y J hJ
    rw [cf] at e₂
    rw [← b₁] at e₁
    rw [hv _ _ y J hJ, hv _ _ y J hJ, hv _ _ y J hJ, hb, hb, _root_.mul_assoc]
    refine (congrArg _ e₁).trans ?_
    rw [← _root_.mul_assoc]
    exact (congrArg (· * _) e₂).trans (mul_mul_mul_comm _ _ _ _)
  obtain ⟨h, ⟨gs, g₀, gst, gl⟩, hι⟩ := p.eq
  obtain ⟨ιb, ιv⟩ := (isIota_iff _ _).1 hι
  let q : QkPt D F k := ⟨a • p.y, act p.g, act h, ⟨fun i => act (gs i), by
      obtain ⟨z₁, z₂⟩ := (isZero_iff _).1 g₀
      exact (isZero_iff _).2 ⟨by rw [hb, z₁, MonObj.one_comp], fun χ y J hJ => by
        rw [hv _ _ y J hJ, z₂ _ y J hJ, z₁, u₂ hJ, _root_.mul_one]⟩,
      fun i => add _ _ _ (gst i), congrArg act gl⟩, (isIota_iff _ _).2 ⟨by rw [hb, ιb, cf], fun χ y J hJ => by
      let κ : TF (R := R) F ⟶ TK R := Over.homMk (𝟙 _ ≫ jFK (R := R) F) (by
        rw [Category.id_comp]; rfl)
      have e := (val_mul hJ _ _ _).symm.trans (val_corr hJ (hbal u hu u₀ χ p.y) κ.left)
      have e' : val (LB.pullGen D.P.L _ _ u (D.pt2 χ p.y)) κ.left y J = val₂ u y J (cP D _ χ) (cP D _ p.y) := by
        rw [val_pull hJ, val₂, ← comp_cP D κ, ← comp_cP D κ p.y, ← comp_lift]; rfl
      rw [hv _ _ y J hJ, ιv _ y J hJ, ιb, ← e']
      exact (congrArg₂ (· * ·) (tau_symm (𝟙 (TF (R := R) F)) hJ _ _) rfl).trans
        (e.trans (tau_symm (𝟙 (TF (R := R) F)) hJ _ _))⟩⟩
  refine ⟨q, q, rfl, ⟨hb _, fun u' hu' u₀' χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩, qk_equiv_refl hB q⟩
  refine (val_mul hJ _ _ _).trans (Eq.trans (congrArg₂ (· * ·) rfl ?_) (hv p.g χ y J hJ).symm)
  rw [val_pull hJ, Category.id_comp]
  have z2 : zero2 D.P.A ≫ (snd D.P.A D.P.A).left ≫ D.P.A.hom = 𝟙 _ := by
    rw [Over.w]; exact Over.w (lift η[D.P.A] η[D.P.A])
  exact gen_unique D.P.isLB _ (zero2 D.P.A) z2 (surj_comp (surj_snd hG D.P.isAb _) (hG _ _ D.P.isAb).2) hu' hu
    (fun y I hI => by
      have a₁ := val_corr hI u₀' (𝟙 _)
      have a₂ := val_corr hI u₀ (𝟙 _)
      rw [val_pull hI, Category.id_comp] at a₁ a₂
      exact a₁.trans a₂.symm) _ _ y J hJ

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def WitData {k : Type} [Field k] {b : O →+* k} (a : ArcIn D l β k b)
    (P : Out.DegData (PowerSeries k) (Ideal.span {PowerSeries.X})) [Module (𝓞 E) P.toPre.X]
    (oP : letI := H.starRing; P.toPre.OAct (𝓞 E)) (φ : P.toPre.P.A.left ⟶ a.D₀.P.A.left)
    (he : eSec P.toPre.P.A ≫ φ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (w : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ)) (e : a.D₀.X ≃ₗ[𝓞 E] P.toPre.X) : Prop :=
  letI := H.starRing
  IsGrpPullback P.toPre.P.A a.D₀.P.A (spMap (PowerSeries.C (R := k))) φ ∧ w.IsGen ∧
    LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec P.toPre.P.A) (fun _ => 1)) P.toPre.rig
      (rigPullOf φ (spMap (PowerSeries.C (R := k))) he a.D₀.P.L a.D₀.rig) ∧
    (∀ x, (oP.onB.act x).left ≫ φ = φ ≫ (a.oa.onB.act x).left) ∧
    (∀ y, (P.toPre.c (e y)).left ≫ φ = spMap (PowerSeries.C (R := k)) ≫ (a.D₀.c y).left) ∧
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing (PowerSeries k)) F] [Algebra (FractionRing k) F]
      (uF : F),
      (∀ x, algebraMap (FractionRing k) F (algebraMap k _ x) =
        algebraMap (FractionRing (PowerSeries k)) F (algebraMap (PowerSeries k) _ (PowerSeries.C x))) →
      uF = algebraMap (FractionRing (PowerSeries k)) F (algebraMap (PowerSeries k) _ PowerSeries.X) →
      ∀ y, GenRel w (LB.pullGen _ _ _ (P.toPre.psi (e y)) (Out.jFK (R := PowerSeries k) F))
        (LB.pullGen _ _ _ (a.D₀.psi y) (Out.jFK (R := k) F)) (uF ^ (a.be y y / 2))

def QkToAkInjSt : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), Out.AdmBase R I →
  ∀ (Dd : Out.DegData R I) (A : Out.PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G],
    IsSemiAbelian G → ∀ (U : Out.Unif I Dd A G) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F]
    (n : ℕ), 1 ≤ n → ∀ (p p' : Out.QkPt Dd.toPre F n) (x : Out.TFK (R := R) F ⟶ A.A),
      Out.QkToAkU U.toUnifPre F n p x → Out.QkToAkU U.toUnifPre F n p' x → Out.QkPt.Equiv Dd.toPre F p p'

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushRProdPtsResP
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace ReciprocityTheory.ChartRestriction.G.Chart

attribute [local instance] Over.cartesianMonoidalCategory

variable {S : Type} [CommRing S] {G : Over (Spec (CommRingCat.of S))} [GrpObj G]

theorem tanS_prodPts {d : ℕ} (c : Fin d → S) {u : Fin d → (sp (R₀ := S) (DualNumber S) ⟶ G)} (hu : ∀ i, TanS (u i)) :
    TanS (prodPts c u) := by
  unfold TanS prodPts
  change preH (spMap (TrivSqZeroExt.fstHom S S S)) (List.ofFn fun i => spMap (scaleD (c i)) ≫ u i).prod = 1
  rw [map_list_prod, List.map_ofFn]
  have h1 : ∀ i, preH (spMap (TrivSqZeroExt.fstHom S S S)) (spMap (scaleD (c i)) ≫ u i) = 1 :=
    fun i => tanS_scale (c i) (hu i)
  simp only [Function.comp_def, h1, List.ofFn_const, List.prod_replicate, one_pow]

section Local

variable (p : Ideal S) [p.IsPrime]

abbrev Gp : Over (Spec (CommRingCat.of (Localization.AtPrime p))) := (Over.pullback (fB S (Localization.AtPrime p))).obj G

def resP (v : sp (R₀ := S) (DualNumber S) ⟶ G) :
    sp (R₀ := Localization.AtPrime p) (DualNumber (Localization.AtPrime p)) ⟶ Gp (G := G) p :=
  pullR G (spMap (dualMapS (Algebra.ofId S (Localization.AtPrime p))) ≫ v)

theorem pushR_resP (v : sp (R₀ := S) (DualNumber S) ⟶ G) :
    pushR G (resP p v) = spMap (dualMapS (Algebra.ofId S (Localization.AtPrime p))) ≫ v := by
  unfold resP
  exact pushR_pullR (R := S) (R' := Localization.AtPrime p) (G := G) _

theorem pushR_prodPts_resP {d : ℕ} (c : Fin d → S) (u : Fin d → (sp (R₀ := S) (DualNumber S) ⟶ G)) :
    pushR G (prodPts (fun i => algebraMap S (Localization.AtPrime p) (c i)) (fun i => resP p (u i))) =
      spMap (dualMapS (Algebra.ofId S (Localization.AtPrime p))) ≫ prodPts c u := by
  unfold prodPts
  rw [pushR_prod]
  change _ = preH (spMap (dualMapS (Algebra.ofId S (Localization.AtPrime p))))
    (List.ofFn fun i => spMap (scaleD (c i)) ≫ u i).prod
  rw [map_list_prod, List.map_ofFn]
  refine congrArg List.prod (congrArg List.ofFn (funext fun i => ?_))
  show pushR G (spMap (scaleD _) ≫ resP p (u i)) =
    spMap (dualMapS (Algebra.ofId S (Localization.AtPrime p))) ≫ spMap (scaleD (c i)) ≫ u i
  rw [pushR_spMap, pushR_resP, ← Category.assoc, ← Category.assoc, spMap_comp, spMap_comp]
  congr 2
  exact (dualMapS_comp_scaleS (Algebra.ofId S (Localization.AtPrime p)) (c i)).symm

theorem isTan_iff_tanS (w : sp (R₀ := Localization.AtPrime p) (DualNumber (Localization.AtPrime p)) ⟶ Gp (G := G) p) :
    IsTan w ↔ TanS (pushR G w) := by
  unfold IsTan TanS
  constructor
  · intro h
    have h' := congrArg (pushR G) h
    rw [pushR_spMap, pushR_one] at h'
    exact h'
  · intro h
    apply pushR_inj (G := G)
    rw [pushR_spMap, pushR_one]
    exact h

variable [∀ s : S, Smooth (Gs G s).hom]

theorem prodPts_resP_inj {d : ℕ} {u : Fin d → (Geo.Tor.epsR S ⟶ G)} (hu : Geo.Tor.IsLieBasis u)
    {a b : Fin d → Localization.AtPrime p}
    (h : prodPts a (fun i => resP p (u i)) = prodPts b (fun i => resP p (u i))) : a = b := by
  classical
  unfold Geo.Tor.IsLieBasis at hu
  obtain ⟨hT, hU⟩ := hu
  have hTS : ∀ i, TanS (u i) := fun i => (isTan_iff (u i)).2 (hT i)
  obtain ⟨⟨s, hs⟩, hint⟩ := IsLocalization.exist_integer_multiples (M := p.primeCompl)
    (Finset.univ : Finset (Fin d ⊕ Fin d)) (Sum.elim a b)
  have hint' : ∀ j, ∃ y : S, algebraMap S (Localization.AtPrime p) y = s • Sum.elim a b j :=
    fun j => hint j (Finset.mem_univ _)
  choose y hy using hint'
  let a' : Fin d → S := fun i => y (Sum.inl i)
  let b' : Fin d → S := fun i => y (Sum.inr i)
  have ea : algebraMap S (Localization.AtPrime p) s • a = fun i => algebraMap S _ (a' i) := by
    funext i
    simp only [a', hy, Pi.smul_apply, smul_eq_mul, Sum.elim_inl, Algebra.smul_def]
  have eb : algebraMap S (Localization.AtPrime p) s • b = fun i => algebraMap S _ (b' i) := by
    funext i
    simp only [b', hy, Pi.smul_apply, smul_eq_mul, Sum.elim_inr, Algebra.smul_def]
  have h2 : spMap (scaleD (algebraMap S (Localization.AtPrime p) s)) ≫ prodPts a (fun i => resP p (u i)) =
      spMap (scaleD (algebraMap S (Localization.AtPrime p) s)) ≫ prodPts b (fun i => resP p (u i)) := by
    rw [h]
  rw [scale_prodPts, scale_prodPts, ea, eb] at h2
  have h3 := congrArg (pushR G) h2
  rw [pushR_prodPts_resP, pushR_prodPts_resP] at h3
  have hA : TanS (prodPts a' u) := tanS_prodPts a' hTS
  have hB : TanS (prodPts b' u) := tanS_prodPts b' hTS
  have hx : TanS (prodPts a' u * (prodPts b' u)⁻¹) := by
    unfold TanS at hA hB ⊢
    change preH (spMap (TrivSqZeroExt.fstHom S S S)) (prodPts a' u * (prodPts b' u)⁻¹) = 1
    rw [map_mul, map_inv]
    change (spMap (TrivSqZeroExt.fstHom S S S) ≫ prodPts a' u) *
      (spMap (TrivSqZeroExt.fstHom S S S) ≫ prodPts b' u)⁻¹ = 1
    rw [hA, hB, _root_.inv_one, _root_.mul_one]
  have hx1 : spMap (dualMapS (Algebra.ofId S (Localization.AtPrime p))) ≫
      (prodPts a' u * (prodPts b' u)⁻¹) = 1 := by
    change preH (spMap (dualMapS (Algebra.ofId S (Localization.AtPrime p))))
      (prodPts a' u * (prodPts b' u)⁻¹) = 1
    rw [map_mul, map_inv]
    change (spMap (dualMapS (Algebra.ofId S (Localization.AtPrime p))) ≫ prodPts a' u) *
      (spMap (dualMapS (Algebra.ofId S (Localization.AtPrime p))) ≫ prodPts b' u)⁻¹ = 1
    rw [h3, _root_.mul_inv_cancel]
  obtain ⟨q, hq, hq1⟩ := tan_prime_uniq (p := p) hx hx1
  change preH (spMap (scaleS (S := S) q)) (prodPts a' u * (prodPts b' u)⁻¹) = 1 at hq1
  rw [map_mul, map_inv, _root_.mul_inv_eq_one] at hq1
  have hq2 : prodPts (q • a') u = prodPts (q • b') u := by
    rw [← scale_prodPts, ← scale_prodPts]
    exact hq1
  have hw : Geo.Tor.IsTangent (prodPts (q • a') u) := (isTan_iff _).1 (tanS_prodPts _ hTS)
  obtain ⟨c, _, huniq⟩ := hU _ hw
  have e1 := huniq (q • a') ((isLieComb_iff _ _ _).2 rfl)
  have e2 := huniq (q • b') ((isLieComb_iff _ _ _).2 hq2)
  have hab : q • a' = q • b' := e1.trans e2.symm
  funext i
  have hi := congrArg (algebraMap S (Localization.AtPrime p)) (congrFun hab i)
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, a', b', hy, Sum.elim_inl, Sum.elim_inr,
    Algebra.smul_def] at hi
  have hqu : IsUnit (algebraMap S (Localization.AtPrime p) q) :=
    IsLocalization.map_units (M := p.primeCompl) _ ⟨q, hq⟩
  have hsu : IsUnit (algebraMap S (Localization.AtPrime p) s) :=
    IsLocalization.map_units (M := p.primeCompl) _ ⟨s, hs⟩
  rw [hqu.mul_right_inj, hsu.mul_right_inj] at hi
  exact hi

private theorem scaleD_comp_scaleD {R : Type} [CommRing R] (a b : R) :
    (scaleD a).comp (scaleD b) = scaleD (a * b) := by
  apply AlgHom.ext
  intro x
  ext
  · simp
  · simp only [AlgHom.comp_apply, TrivSqZeroExt.snd_map, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]
    ring

private theorem spMap_scaleD_one {R : Type} [CommRing R] {H : Over (Spec (CommRingCat.of R))}
    (w : sp (R₀ := R) (DualNumber R) ⟶ H) : spMap (scaleD (1 : R)) ≫ w = w := by
  have h1 : scaleD (1 : R) = AlgHom.id R (DualNumber R) := by
    apply AlgHom.ext
    intro x
    ext <;> simp
  have h2 : spMap (R₀ := R) (AlgHom.id R (DualNumber R)) = 𝟙 _ := by
    ext1
    simp [spMap]
  rw [h1, h2, Category.id_comp]

theorem isLieBasis_local {d : ℕ} {u : Fin d → (Geo.Tor.epsR S ⟶ G)} (hu : Geo.Tor.IsLieBasis u) :
    Geo.Tor.IsLieBasis (G := Gp (G := G) p) (fun i => resP p (u i)) := by
  have hu0 := hu
  unfold Geo.Tor.IsLieBasis at hu0 ⊢
  obtain ⟨hT, hU⟩ := hu0
  have hTS : ∀ i, TanS (u i) := fun i => (isTan_iff (u i)).2 (hT i)
  refine ⟨fun i => (isTan_iff _).1 ((isTan_iff_tanS p _).2 ?_), fun w hw => ?_⟩
  · rw [pushR_resP]
    exact tanS_restrict _ (hTS i)
  · have hwS : TanS (pushR G w) := (isTan_iff_tanS p w).1 ((isTan_iff w).2 hw)
    obtain ⟨q, hq, w0, hw0, he⟩ := tan_prime_lift (p := p) hwS
    obtain ⟨c0, hc0, -⟩ := hU w0 ((isTan_iff w0).1 hw0)
    rw [isLieComb_iff] at hc0
    have hQ : IsUnit (algebraMap S (Localization.AtPrime p) q) :=
      IsLocalization.map_units (M := p.primeCompl) _ ⟨q, hq⟩
    have E : prodPts (fun i => algebraMap S (Localization.AtPrime p) (c0 i)) (fun i => resP p (u i)) =
        spMap (scaleD (algebraMap S (Localization.AtPrime p) q)) ≫ w := by
      apply pushR_inj (G := G)
      rw [pushR_prodPts_resP, ← hc0, he, pushR_spMap]
      rfl
    have hw1 : w = prodPts ((hQ.unit⁻¹ : (Localization.AtPrime p)ˣ) •
        (fun i => algebraMap S (Localization.AtPrime p) (c0 i))) (fun i => resP p (u i)) := by
      rw [Units.smul_def, ← scale_prodPts, E, ← Category.assoc, spMap_comp, scaleD_comp_scaleD,
        hQ.val_inv_mul, spMap_scaleD_one]
    refine ⟨_, (isLieComb_iff _ _ _).2 hw1, fun c' hc' => ?_⟩
    exact prodPts_resP_inj p hu (((isLieComb_iff _ _ _).1 hc').symm.trans hw1)

end Local

theorem frameLieBC {S : Type} [CommRing S] (G : Over (Spec (CommRingCat.of S))) [GrpObj G] [Smooth G.hom] {d : ℕ}
    {u : Fin d → (Geo.Tor.epsR S ⟶ G)} (hu : Geo.Tor.IsLieBasis u) {k : Type} [Field k] (φ : S →+* k)
    {G' : Over (Spec (CommRingCat.of k))} [GrpObj G'] {F : G'.left ⟶ G.left}
    (h : Geo.Tor.IsGrpPullback G' G (Geo.Tor.spMap φ) F) {u' : Fin d → (Geo.Tor.epsR k ⟶ G')}
    (hu' : ∀ i, (u' i).left ≫ F = Geo.Tor.spMap (dualMapR φ) ≫ (u i).left) : Geo.Tor.IsLieBasis u' := by
  classical
  haveI : ∀ s : S, Smooth (Gs G s).hom := fun s => by
    show Smooth (pullback.snd G.hom (fB S (Localization.Away s)))
    first
    | infer_instance
    | exact MorphismProperty.pullback_snd (P := @Smooth) _ _ (inferInstance : Smooth G.hom)
  haveI hpr : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  let φp : Localization.AtPrime (RingHom.ker φ) →+* k :=
    IsLocalization.lift (M := (RingHom.ker φ).primeCompl) (S := Localization.AtPrime (RingHom.ker φ)) (g := φ)
      (fun s => isUnit_iff_ne_zero.2 fun h0 => s.2 (RingHom.mem_ker.2 h0))
  have hφ : φp.comp (algebraMap S (Localization.AtPrime (RingHom.ker φ))) = φ := IsLocalization.lift_comp _
  haveI : Smooth (Gp (G := G) (RingHom.ker φ)).hom := by
    show Smooth (pullback.snd G.hom (fB S (Localization.AtPrime (RingHom.ker φ))))
    first
    | infer_instance
    | exact MorphismProperty.pullback_snd (P := @Smooth) _ _ (inferInstance : Smooth G.hom)
  have hsp : Geo.Tor.spMap φ = Geo.Tor.spMap φp ≫ fB S (Localization.AtPrime (RingHom.ker φ)) := by
    simp only [Geo.Tor.spMap, fB]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hφ]
  have h2 : Geo.Tor.IsGrpPullback G' G (Geo.Tor.spMap φp ≫ fB S (Localization.AtPrime (RingHom.ker φ))) F :=
    h.congr hsp rfl
  have h3 := isGrpPullback_factor (fB S (Localization.AtPrime (RingHom.ker φ))) (Geo.Tor.spMap φp) h2
  refine isLieBasis_baseChange (G := Gp (G := G) (RingHom.ker φ)) φp h3
    (isLieBasis_local (RingHom.ker φ) hu) (fun j => ?_)
  have hring : (dualMapR φp).comp (dualMapS (Algebra.ofId S (Localization.AtPrime (RingHom.ker φ)))).toRingHom =
      dualMapR φ := by
    conv_rhs => rw [← hφ]
    apply RingHom.ext
    intro x
    apply TrivSqZeroExt.ext <;> simp [dualMapR, dualMapS_fst, dualMapS_snd]
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, hu' j]
    simp only [resP, pullR, Over.homMk_left, Category.assoc, IsPullback.lift_fst, Over.comp_left, spMap]
    rw [← Category.assoc, Geo.Tor.spMap, Geo.Tor.spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hring]
  · rw [Category.assoc, pullback.lift_snd]
    simp only [resP, pullR, Over.homMk_left, Category.assoc, IsPullback.lift_snd]
    rw [← Category.assoc, Over.w (u' j)]
    simp only [Geo.Tor.epsR, sp, Over.mk_hom, Geo.Tor.spMap]
    erw [IsPullback.lift_snd]
    simp only [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    simp [dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

end ReciprocityTheory.ChartRestriction.G.Chart
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AdmissibleBasePowerSeries
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj

theorem admissibleBase_powerSeries (k : Type) [Field k] : Out.AdmBase (PowerSeries k) (Ideal.span {PowerSeries.X}) := by
  refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
  have : IsAdicComplete (IsLocalRing.maximalIdeal k) k := by
    rw [IsLocalRing.maximalIdeal_eq_bot]; infer_instance
  have h := ReciprocityTheory.P1.isAdicComplete_ps (R := k)
  rwa [PowerSeries.maximalIdeal_eq_span_X] at h

theorem specOf_id (R : Type) [CommRing R] : Out.specOf (RingHom.id R) = 𝟙 _ := by
  simp [Out.specOf]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}


set_option maxHeartbeats 1600000 in
theorem ArcWit.uwMove (hU : Out.UnifBaseChangeSt) (h5 : Out.Laws5) {Y : Model Xo c β} {O' : Type} [CommRing O']
    [IsDomain O'] {b : O →+* O'} {a : ArcIn D l β O' b} {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}
    (hR : Out.AdmBase R I) {f : O' →+* R} {u : R} {χ : Sp R ⟶ Y.X} (W W' : ArcWit Y a I f u χ) (ψ : W.t.G ≅ W'.t.G)
    [IsMonHom ψ.hom] (hφ : ψ.hom.left ≫ W'.m.φ = W.m.φ) (hact : ∀ x, W.t.act.act x ≫ ψ.hom = ψ.hom ≫ W'.t.act.act x) :
    ∃ (bc : W.t.G ≅ (Over.pullback (Out.specOf (RingHom.id R))).obj W'.t.G) (D'' : Out.DegData R I)
      (hD : Out.IsPullDeg (RingHom.id R) W'.P.D.toPre D''.toPre) (U'' : Out.Unif I D'' W'.P.A W.t.G)
      (_ : Module (𝓞 E) D''.toPre.X) (oD : letI := H.starRing; D''.toPre.OAct (𝓞 E)),
      IsMonHom bc.hom ∧ bc.hom.left ≫ pullback.fst W'.t.G.hom (Out.specOf (RingHom.id R)) = ψ.hom.left ∧
      U''.LG = W.P.U.LG ∧
      U''.gen.hom.left ≫ W'.P.U.gen.inv.left ≫ pullback.fst W'.t.G.hom (Out.jK R) =
        pullback.fst W.t.G.hom (Out.jK R) ≫ ψ.hom.left ∧
      Out.IsPullUnif (RingHom.id R) hD bc W'.P.U U'' ∧
      (∀ (x : 𝓞 E) y, hD.xe (x • y) = x • hD.xe y) ∧
      (letI := H.starRing; ∀ x, oD.onB.act x ≫ hD.e.hom =
        hD.e.hom ≫ (Over.pullback (Out.specOf (RingHom.id R))).map (W'.P.oD.onB.act x)) ∧
      (letI := H.starRing; U''.toUnifPre.OLinear (𝓞 E) oD W'.P.oA W.t.act.toRingAct) ∧
      (letI := H.starRing; TraceFormTwistIso D''.toPre oD H.w0) := by
  let _ := H.starRing
  have hs := specOf_id R
  have gp₁ : IsGrpPullback W.t.G W'.t.G (Out.specOf (RingHom.id R)) ψ.hom.left :=
    (isGrpPullback_of_iso ψ).congr hs.symm rfl
  obtain ⟨bc, mbc, hbc⟩ := grpPullback_iso gp₁ (isGrpPullback_pullback W'.t.G (Out.specOf (RingHom.id R)))
  have gpG : IsGrpPullback W'.P.A.A W'.t.G (Out.jK R) (W'.P.U.gen.inv.left ≫ pullback.fst W'.t.G.hom (Out.jK R)) := by
    have := W'.P.U.gen_hom
    have : IsMonHom W'.P.U.gen.symm.hom := by show IsMonHom W'.P.U.gen.inv; infer_instance
    exact ((isGrpPullback_of_iso W'.P.U.gen.symm).comp (isGrpPullback_pullback W'.t.G (Out.jK R))).congr
      (Category.id_comp _) rfl
  have gp₂ : IsGrpPullback ((Over.pullback (Out.jK R)).obj W.t.G) W'.t.G (Out.jK R)
      (pullback.fst W.t.G.hom (Out.jK R) ≫ ψ.hom.left) :=
    ((isGrpPullback_pullback W.t.G (Out.jK R)).comp (isGrpPullback_of_iso ψ)).congr (Category.comp_id _) rfl
  obtain ⟨eA, mE, heA⟩ := grpPullback_iso gp₂ gpG
  have hgi : W'.P.U.gen.inv.left ≫ W'.P.U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have wA : LBIso (W'.P.A.L.pull eA.hom.left) (W'.P.U.LG.L.pull (pullback.fst W.t.G.hom (Out.jK R) ≫ bc.hom.left ≫
      pullback.fst W'.t.G.hom (Out.specOf (RingHom.id R)))) :=
    LBIso.chartPull (h := eA.hom.left ≫ W'.P.U.gen.inv.left)
      (chartPullSame W'.P.A.L (fun _ => eA.hom.left) (fun _ => W'.P.U.gen.hom.left) _ _ fun _ => by
        rw [Category.assoc, hgi, Category.comp_id])
      (chartPullSame W'.P.U.LG.L _ (fun _ => pullback.fst W'.t.G.hom (Out.jK R)) _ _ fun _ => by
        rw [hbc, ← heA]; simp only [Category.assoc]) W'.P.U.ext
  obtain ⟨wL', he', gL, rL⟩ := rigIso_congr W'.P.bundle (CubeMap.ofHom ψ.hom) (sabMap_cubical W.m W'.m ψ hφ) hbc
    (e := Out.specOf (RingHom.id R)) hs
  obtain ⟨Wo, hWo, hψW⟩ := h5.psiOnExists R I hR W'.P.D
  have hgen : (Out.specOf (RingHom.id R)).base (genericPoint (Spec (CommRingCat.of R))) ∈ Wo := by
    rw [hs]; exact hWo
  have hI : I.map (RingHom.id R) ≤ I := by rw [Ideal.map_id]
  obtain ⟨D'', hD, U'', hLG, hgenU, hPU⟩ := hU R R I I hR hR (RingHom.id R) hI W'.P.D W'.P.A W'.t.G W'.t.semi W'.P.U
    Wo hψW hgen W.t.G bc mbc W'.P.A rfl eA mE wA W.t.PP wL' he' gL rL
  have hbcact : ∀ x, W.t.act.toRingAct.act x ≫ bc.hom =
      bc.hom ≫ (Over.pullback (Out.specOf (RingHom.id R))).map (W'.t.act.toRingAct.act x) := by
    intro x
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · have a₂ : ((Over.pullback (Out.specOf (RingHom.id R))).map (W'.t.act.act x)).left ≫
          pullback.fst W'.t.G.hom (Out.specOf (RingHom.id R)) = pullback.fst _ _ ≫ (W'.t.act.act x).left :=
        pullback.lift_fst _ _ _
      show (W.t.act.act x ≫ bc.hom).left ≫ _ =
        (bc.hom ≫ (Over.pullback (Out.specOf (RingHom.id R))).map (W'.t.act.act x)).left ≫ _
      rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, a₂, hbc, ← Category.assoc, hbc,
        ← Over.comp_left, hact, Over.comp_left]
    · exact (Over.w (W.t.act.act x ≫ bc.hom)).trans
        (Over.w (bc.hom ≫ (Over.pullback (Out.specOf (RingHom.id R))).map (W'.t.act.act x))).symm
  have actA : ∀ x, (W'.P.oA.act x).left ≫ W'.P.U.gen.inv.left ≫ pullback.fst W'.t.G.hom (Out.jK R) =
      W'.P.U.gen.inv.left ≫ pullback.fst W'.t.G.hom (Out.jK R) ≫ (W'.t.act.act x).left := by
    intro x
    have e : W'.P.oA.act x ≫ W'.P.U.gen.inv = W'.P.U.gen.inv ≫ (Over.pullback (Out.jK R)).map (W'.t.act.act x) := by
      rw [Iso.comp_inv_eq, Category.assoc]
      exact ((Iso.inv_comp_eq _).2 (W'.P.lin.ext x)).symm
    rw [← Category.assoc, ← Over.comp_left, e, Over.comp_left, Category.assoc]
    exact congrArg _ (pullback.lift_fst _ _ _)
  have extA : ∀ x, (Over.pullback (Out.jK R)).map (W.t.act.toRingAct.act x) ≫ U''.gen.hom =
      U''.gen.hom ≫ W'.P.oA.act x := by
    intro x
    rw [hgenU]
    apply Over.OverMorphism.ext
    apply gpG.1.hom_ext
    · have a₁ : ((Over.pullback (Out.jK R)).map (W.t.act.act x)).left ≫ pullback.fst W.t.G.hom (Out.jK R) =
          pullback.fst W.t.G.hom (Out.jK R) ≫ (W.t.act.act x).left := pullback.lift_fst _ _ _
      have a₃ : (W.t.act.act x).left ≫ ψ.hom.left = ψ.hom.left ≫ (W'.t.act.act x).left := by
        rw [← Over.comp_left, hact, Over.comp_left]
      show ((Over.pullback (Out.jK R)).map (W.t.act.act x) ≫ eA.hom).left ≫ _ = (eA.hom ≫ W'.P.oA.act x).left ≫ _
      rw [Over.comp_left, Category.assoc, heA, ← Category.assoc, a₁, Category.assoc, a₃, Over.comp_left,
        Category.assoc, actA, reassoc_of% heA]
    · rw [Over.w, Over.w]
  obtain ⟨mod'', oD'', xl, el, lin'', w0''⟩ := h5.oLinBaseChange R R I I hR hR (RingHom.id R) W'.P.D W'.P.A W'.t.G W'.P.U
    W.t.G bc mbc W'.P.A D'' hD U'' hPU (𝓞 E) W'.P.oD W'.P.oA W'.t.act.toRingAct W'.P.lin W.t.act.toRingAct hbcact
    W'.P.oA extA
  refine ⟨bc, D'', hD, U'', mod'', oD'', mbc, hbc, hLG.trans W.P.bundle.symm, ?_, hPU, xl, el, lin'', w0'' H.w0 W'.P.w0⟩
  rw [hgenU]; exact heA

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end
