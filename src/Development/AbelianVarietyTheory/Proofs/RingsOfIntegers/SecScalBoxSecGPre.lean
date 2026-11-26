module

public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.RosatiAdjPow

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.PreboxExpansionWeight
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.BoxExpPre

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {j : ℕ} {D D' : DegData R I}
  {A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G G' : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
  {pD : IsPowDeg D'.toPre D.toPre j} {pG : IsPowGrp G' G j}
  {U' : UnifPre I D' A' G'} {U : UnifPre I D A G} {wL : LB.Iso U'.LG.L (boxLB U.LG.L pG.pr)}


variable (pD pG U' U) in
def TPr : Prop := (∀ (e : ℕ) (x : D'.toPre.X), ∃ hψ : ∀ (i : Fin j) (k : Fin 4), D'.toPre.Oφ ((Over.map (thick R I e)).map (U'.gt e).q ≫ D'.toPre.prBe I e) x k ≫ (pD.pw.pr i).left = ((Over.pullback (thick R I e)).map (pG.pr i)).left ≫ D.toPre.Oφ ((Over.map (thick R I e)).map (U.gt e).q ≫ D.toPre.prBe I e) (pD.xe x i) k, LB.Gen.Maps (LB.linCombIso pD.w _ Oinvε) ((U'.gt e).t x) (GeneratorPullback.boxGen D.toPre.P.L (fun i => (pD.pw.pr i).left) _ Oinvε (fun i => GeneratorPullback.pullAlong D.toPre.P.L (pD.pw.pr i).left ((Over.pullback (thick R I e)).map (pG.pr i)).left _ Oinvε _ (hψ i) ((U.gt e).t (pD.xe x i)))))


variable (pD pG U' U wL) in
def WPr : Prop := (∀ (e : ℕ) (jNM : Fin j → D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL' : U'.LG.L.ι) (jNL : Fin j → U.LG.L.ι), res (X := (thickObj R I e G').left) (inf_le_left.trans (inf_le_left.trans inf_le_left) : (U'.gt e).pG.left ⁻¹ᵁ (LB.div (boxLB D.toPre.P.L pD.pw.pr) D'.toPre.P.L).U (jNM, jM') ⊓ (LB.div (D'.toPre.P.L.pull (U'.gt e).pG.left) (U'.LG.L.pull (fstG I e G').left)).U (fun _ => jM', fun _ => jL') ⊓ (⨅ i, ((Over.pullback (thick R I e)).map (pG.pr i)).left ⁻¹ᵁ (LB.div (D.toPre.P.L.pull (U.gt e).pG.left) (U.LG.L.pull (fstG I e G).left)).U (fun _ => jNM i, fun _ => jNL i)) ⊓ (fstG I e G').left ⁻¹ᵁ (LB.div (boxLB U.LG.L pG.pr) U'.LG.L).U (jNL, jL') ≤ (U'.gt e).pG.left ⁻¹ᵁ (LB.div (boxLB D.toPre.P.L pD.pw.pr) D'.toPre.P.L).U (jNM, jM')) (pullU (U'.gt e).pG.left _ (pD.w.s (jNM, jM'))) * res (X := (thickObj R I e G').left) (inf_le_left.trans (inf_le_left.trans inf_le_right)) ((U'.w e).s (fun _ => jM', fun _ => jL')) = (∏ i, res (X := (thickObj R I e G').left) (inf_le_left.trans (inf_le_right.trans (iInf_le _ i))) (pullU ((Over.pullback (thick R I e)).map (pG.pr i)).left _ ((U.w e).s (fun _ => jNM i, fun _ => jNL i)))) * res (X := (thickObj R I e G').left) inf_le_right (pullU (Y := (thickObj R I e G').left) (fstG I e G').left _ (wL.s (jNL, jL'))))

theorem prebox_q (PT : TPr pD pG U' U) (e : ℕ) (i : Fin j) :
    pGl U' e ≫ (pD.pw.pr i).left = rhoE I pG e i ≫ pGl U e := (PT e 0).choose i 2

set_option maxHeartbeats 800000 in
theorem prebox_F (PT : TPr pD pG U' U) {e : ℕ} {y : (thickObj R I e G').left} {J : ((thickObj R I e G').left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι}
    {J' : ((thickObj R I e G').left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι}
    (hJ : Good D.toPre.P.L y J) (hJ' : Good D'.toPre.P.L y J') {k : ℕ} {f : Fin j → ∀ α : D.toPre.X, D.toPre.SecB k α}
    {f' : ∀ α' : D'.toPre.X, D'.toPre.SecB k α'} (hf' : IsBoxFamB pD k f' f) (α' : D'.toPre.X) :
    (∏ a, omB pD y J J' ((pGl U' e) ≫ D'.toPre.famφB α' a) ^ DegPre.famε k a).val * sval (f' α') (pGl U' e) y J' =
      ∏ i, sval (f i (pD.xe α' i)) (rhoE I pG e i ≫ (pGl U e)) y J := by
  obtain ⟨hφ, H⟩ := hf' α'
  have := box_sec_val pD.w hφ (f' α') (fun i => f i (pD.xe α' i)) _ H (pGl U' e) y hJ hJ'
  simp only [prebox_q PT] at this
  exact this

set_option maxHeartbeats 800000 in
theorem prebox_expansion_torus (PT : TPr pD pG U' U) {e : ℕ} {y : (thickObj R I e G').left} {J : ((thickObj R I e G').left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι}
    {J' : ((thickObj R I e G').left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι}
    (hJ : Good D.toPre.P.L y J) (hJ' : Good D'.toPre.P.L y J') (α' : D'.toPre.X) :
    (∏ a, omB pD y J J' (Oφl U' e α' a) ^ Oinvε a) * val (tG U' e α') (𝟙 _) y J' =
      ∏ i, val (tG U e (pD.xe α' i)) (rhoE I pG e i) y J := by
  obtain ⟨hψ, H⟩ := PT e α'
  exact box_gen_val pD.w hψ _ (fun i => tG U e (pD.xe α' i)) H y hJ hJ'

theorem prebox_om {e : ℕ} {y : (thickObj R I e G').left} {J : ((thickObj R I e G').left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι}
    {J' : ((thickObj R I e G').left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι} (k : ℕ) (α' : D'.toPre.X) :
    (∏ a, omB pD y J J' ((pGl U' e) ≫ D'.toPre.famφB α' a) ^ DegPre.famε k a) * ∏ a, omB pD y J J' (Oφl U' e α' a) ^ Oinvε a =
      omB pD y J J' (pGl U' e) ^ k := by
  have a₀ : (pGl U' e) ≫ D'.toPre.famφB α' 0 = (pGl U' e) := Category.comp_id _
  have a₁ : (pGl U' e) ≫ D'.toPre.famφB α' 1 = Oφl U' e α' 0 := congrArg (fun z => z.left)
    ((MonObj.comp_mul (U'.gt e).pG (𝟙 _) (cP D'.toPre _ α')).trans
      (congrArg₂ (· * ·) (Category.comp_id _) (comp_cP D'.toPre _ α')))
  have a₂ : (pGl U' e) ≫ D'.toPre.famφB α' 2 = Oφl U' e α' 1 :=
    congrArg (fun z => z.left) (comp_cP D'.toPre (U'.gt e).pG α')
  have a₃ : (pGl U' e) ≫ D'.toPre.famφB α' 3 = Oφl U' e α' 3 :=
    congrArg (fun z : _ ⟶ D'.toPre.P.A => z.left) (MonObj.comp_one (M := D'.toPre.P.A) (U'.gt e).pG)
  have a₄ : Oφl U' e α' 2 = (pGl U' e) := rfl
  rw [Fin.prod_univ_four, Fin.prod_univ_four, a₀, a₁, a₂, a₃, a₄]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow, ofMul_pow, DegPre.famε, Oinvε, Matrix.cons_val]
  module

set_option maxHeartbeats 800000 in
theorem prebox_expansion_weight (PT : TPr pD pG U' U) (PW : WPr pD pG U' U wL) {e : ℕ} {y : (thickObj R I e G').left} {J : ((thickObj R I e G').left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι}
    {J' : ((thickObj R I e G').left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι}
    (hJ : Good D.toPre.P.L y J) (hJ' : Good D'.toPre.P.L y J') {jL : Fin j → U.LG.L.ι} {jL' : U'.LG.L.ι}
    (hL : ∀ i, (pG.pr i).left (fGl I G' e y) ∈ U.LG.L.U (jL i)) (hL' : fGl I G' e y ∈ U'.LG.L.U jL') :
    omB pD y J J' (pGl U' e) * wv U' e (𝟙 _) y (J' (pGl U' e)) jL' =
        (∏ i, wv U e (rhoE I pG e i) y (J ((pGl U' e) ≫ (pD.pw.pr i).left)) (jL i)) *
          gm (fGl I G' e) y ((LB.div (boxLB U.LG.L pG.pr) U'.LG.L).U (jL, jL')) (wL.s (jL, jL')) := by
  have hρ : ∀ i, rhoE I pG e i ≫ fGl I G e = fGl I G' e ≫ (pG.pr i).left := fun i => pullback.lift_fst _ _ _
  have hL₁ : ∀ i, fGl I G e (rhoE I pG e i y) ∈ U.LG.L.U (jL i) := fun i =>
    (congrArg (fun g => g y ∈ U.LG.L.U (jL i)) (hρ i)).mpr (hL i)
  have mL : fGl I G' e y ∈ (LB.div (boxLB U.LG.L pG.pr) U'.LG.L).U (jL, jL') := ⟨Set.mem_iInter.2 hL, hL'⟩
  have hq := prebox_q PT e
  have mM : (pGl U' e) y ∈ (LB.div (boxLB D.toPre.P.L pD.pw.pr) D'.toPre.P.L).U (fun i => J ((pGl U' e) ≫ (pD.pw.pr i).left), J' (pGl U' e)) :=
    ⟨Set.mem_iInter.2 fun i => hJ ((pGl U' e) ≫ (pD.pw.pr i).left), hJ' (pGl U' e)⟩
  have mW : ∀ i, rhoE I pG e i y ∈ (D.toPre.P.L.pull (pGl U e)).U (fun _ => J ((pGl U' e) ≫ (pD.pw.pr i).left)) ⊓
      (U.LG.L.pull (fGl I G e)).U (fun _ => jL i) := fun i =>
    ⟨mem_pull.2 ((congrArg (fun g => g y ∈ D.toPre.P.L.U (J ((pGl U' e) ≫ (pD.pw.pr i).left))) (hq i)).mp (hJ _)),
      mem_pull.2 (hL₁ i)⟩
  have hm : (𝟙 _ : (thickObj R I e G').left ⟶ _) y ∈ (pGl U' e) ⁻¹ᵁ (LB.div (boxLB D.toPre.P.L pD.pw.pr) D'.toPre.P.L).U
      (fun i => J ((pGl U' e) ≫ (pD.pw.pr i).left), J' (pGl U' e)) ⊓
      (LB.div (D'.toPre.P.L.pull (pGl U' e)) (U'.LG.L.pull (fGl I G' e))).U (fun _ => J' (pGl U' e), fun _ => jL') ⊓
      (⨅ i, rhoE I pG e i ⁻¹ᵁ (LB.div (D.toPre.P.L.pull (pGl U e)) (U.LG.L.pull (fGl I G e))).U
        (fun _ => J ((pGl U' e) ≫ (pD.pw.pr i).left), fun _ => jL i)) ⊓
      (fGl I G' e) ⁻¹ᵁ (LB.div (boxLB U.LG.L pG.pr) U'.LG.L).U (jL, jL') :=
    ⟨⟨⟨mM, mem_pull.2 (hJ' (pGl U' e)), mem_pull.2 hL'⟩, by
      rw [← Finset.inf_univ_eq_iInf]; exact mem_finf _ _ _ fun i _ => mW i⟩, mL⟩
  have W := congrArg (gm (𝟙 _) y _) (PW e (fun i => J ((pGl U' e) ≫ (pD.pw.pr i).left)) (J' (pGl U' e)) jL' jL)
  exact ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_rp₁ (pGl U' e) y _ _ _ hm _) (gm_res (𝟙 _) y _ hm _))).symm.trans (W.trans
        ((map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_prod _ _ _).trans (Finset.prod_congr rfl fun i _ =>
          gm_rp₁ (rhoE I pG e i) y _ _ _ hm _)) (gm_rp₁ (fGl I G' e) y _ _ _ hm _))))

set_option maxHeartbeats 800000 in
theorem prebox_S {e k : ℕ} {y : (thickObj R I e G').left} {σ : Fin j → H0 U.LG.L k} {σ' : H0 U'.LG.L k}
    (hσ' : IsBoxSecG pG wL k σ' σ) {jL : Fin j → U.LG.L.ι} {jL' : U'.LG.L.ι}
    (hL : ∀ i, (pG.pr i).left (fGl I G' e y) ∈ U.LG.L.U (jL i)) (hL' : fGl I G' e y ∈ U'.LG.L.U jL') :
    (gm (fGl I G' e) y ((LB.div (boxLB U.LG.L pG.pr) U'.LG.L).U (jL, jL')) (wL.s (jL, jL')) ^ k).val *
        sv U' k σ' (fGl I G' e) y jL' = ∏ i, sv U k (σ i) (rhoE I pG e i ≫ fGl I G e) y (jL i) := by
  have hρ : ∀ i, rhoE I pG e i ≫ fGl I G e = fGl I G' e ≫ (pG.pr i).left := fun i => pullback.lift_fst _ _ _
  have hL₁ : ∀ i, fGl I G e (rhoE I pG e i y) ∈ U.LG.L.U (jL i) := fun i =>
    (congrArg (fun g => g y ∈ U.LG.L.U (jL i)) (hρ i)).mpr (hL i)
  have mL : fGl I G' e y ∈ (LB.div (boxLB U.LG.L pG.pr) U'.LG.L).U (jL, jL') := ⟨Set.mem_iInter.2 hL, hL'⟩
  have Sg := congrArg (gs (fGl I G' e) y ((LB.div (boxLB U.LG.L pG.pr) U'.LG.L).U (jL, jL'))) (hσ' jL jL')
  rw [gs_mul _ y _ mL, gs_unit _ y _ mL, map_pow] at Sg
  refine (congrArg₂ (· * ·) rfl (gs_res (fGl I G' e) y (boxG_le_b pG jL jL') mL _).symm).trans
    (Sg.trans ((gs_prod _ y _ mL _ _).trans (Finset.prod_congr rfl fun i _ => ?_)))
  rw [hρ]
  exact (gs_res (fGl I G' e) y (boxG_le_c pG jL jL' i) mL _).trans
    (gs_pull (fGl I G' e) (pG.pr i).left y _ (boxG_le_c pG jL jL' i mL) _)

theorem expandsAt_prebox (PT : TPr pD pG U' U) (PW : WPr pD pG U' U wL) (k e : ℕ) (σ : Fin j → H0 U.LG.L k)
    (f : Fin j → ∀ α : D.toPre.X, D.toPre.SecB k α) (hE : ∀ i, U.ExpandsAt e k (σ i) (f i))
    (σ' : H0 U'.LG.L k) (f' : ∀ α' : D'.toPre.X, D'.toPre.SecB k α')
    (hσ' : IsBoxSecG pG wL k σ' σ) (hf' : IsBoxFamB pD k f' f) :
    U'.ExpandsAt e k σ' f' := by
  classical
  choose S hS using fun i => expandsAt_val U e k (σ i) (f i) (hE i)
  refine expandsAt_of_val U' e k σ' f' ((Fintype.piFinset S).map pD.xe.symm.toEquiv.toEmbedding) fun y J' hJ' => ?_
  choose J hJ using fun ψ : (thickObj R I e G').left ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (ψ y)
  have hJ : Good D.toPre.P.L y J := hJ
  have hF := prebox_F PT hJ hJ' hf'
  have hT := prebox_expansion_torus PT hJ hJ'
  have hω := prebox_om (pD := pD) (U' := U') (y := y) (J := J) (J' := J') k
  have hq := prebox_q PT e
  refine ⟨fun α' hα => ?_, fun jL' hL' => ?_⟩
  · obtain ⟨i, hi⟩ : ∃ i, pD.xe α' i ∉ S i := by
      by_contra hc
      exact hα (Finset.mem_map.2 ⟨pD.xe α', Fintype.mem_piFinset.2 fun i => by_contra fun h => hc ⟨i, h⟩,
        pD.xe.symm_apply_apply α'⟩)
    exact (Units.mul_right_eq_zero _).1 ((hF α').trans (Finset.prod_eq_zero (Finset.mem_univ i)
      ((hS i _ (rhoE I pG e i) y J hJ).1 _ hi)))
  · choose jL hL using fun i => exists_chart U.LG.isLB ((pG.pr i).left ((fGl I G' e) y))
    have hL₁ : ∀ i, fGl I G e (rhoE I pG e i y) ∈ U.LG.L.U (jL i) := fun i =>
      (congrArg (fun g => g y ∈ U.LG.L.U (jL i)) (pullback.lift_fst _ _ _ :
        rhoE I pG e i ≫ fGl I G e = fGl I G' e ≫ (pG.pr i).left)).mpr (hL i)
    have W' := prebox_expansion_weight PT PW hJ hJ' hL hL'
    have Sg' := prebox_S hσ' hL hL'
    refine (omB pD y J J' (pGl U' e) ^ k).mul_right_inj.1 ?_
    rw [← _root_.mul_assoc, ← Units.val_mul, ← mul_pow, W', mul_pow, Units.val_mul, _root_.mul_assoc, Sg', ← Finset.prod_pow,
      Units.coe_prod, ← Finset.prod_mul_distrib, Finset.sum_map, Finset.mul_sum]
    refine (Finset.prod_congr rfl fun i _ => ?_).trans ((Finset.prod_univ_sum S fun i α =>
      sval (f i α) (rhoE I pG e i ≫ (pGl U e)) y J * (val (tG U e α) (rhoE I pG e i) y J).val).trans
      (Finset.sum_congr rfl fun x _ => ?_))
    · rw [hq]; exact (hS i _ (rhoE I pG e i) y J hJ).2 (jL i) (hL₁ i)
    · obtain ⟨α', rfl⟩ := pD.xe.surjective x
      have e₀ : pD.xe.symm.toEquiv.toEmbedding (pD.xe α') = α' := pD.xe.symm_apply_apply α'
      rw [e₀, Finset.prod_mul_distrib, ← hF α', ← Units.coe_prod, ← hT α', ← hω α', Units.val_mul, Units.val_mul,
        _root_.mul_mul_mul_comm]

theorem expandsAt_box_unifPre : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (j : ℕ) (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre D.toPre j) (pA : IsPowPolAV A' A j) (pG : IsPowGrp G' G j) (U' : UnifPre I D' A' G') (U : UnifPre I D A G) (wL : LB.Iso U'.LG.L (boxLB U.LG.L pG.pr)), (∀ i, U'.gen.hom ≫ pA.pr i = (Over.pullback (jK R)).map (pG.pr i) ≫ U.gen.hom) ∧ wL.IsGen ∧ (∃ b : LB.Gen (LB.LinComb U.LG.L (K := Fin j) (fun i => eSec G' ≫ (pG.pr i).left) (fun _ => 1)), GeneratorPullback.MapsAt U.LG.L U'.LG.L (fun i => (pG.pr i).left) wL (eSec G') 1 U'.LG.rig b ∧ LB.Gen.Corr U.LG.L _ _ _ _ b (GeneratorPullback.finProdGen U.LG.L (J := Fin j) (fun _ _ => eSec G) (fun _ _ => 1) (fun _ => U.LG.rig))) ∧ (∀ (e : ℕ) (i : Fin j), (U'.gt e).q ≫ (Over.pullback (thick R I e)).map (pD.pw.pr i) = (Over.pullback (thick R I e)).map (pG.pr i) ≫ (U.gt e).q) ∧ (∀ (e : ℕ) (x : D'.toPre.X), ∃ hψ : ∀ (i : Fin j) (k : Fin 4), D'.toPre.Oφ ((Over.map (thick R I e)).map (U'.gt e).q ≫ D'.toPre.prBe I e) x k ≫ (pD.pw.pr i).left = ((Over.pullback (thick R I e)).map (pG.pr i)).left ≫ D.toPre.Oφ ((Over.map (thick R I e)).map (U.gt e).q ≫ D.toPre.prBe I e) (pD.xe x i) k, LB.Gen.Maps (LB.linCombIso pD.w _ Oinvε) ((U'.gt e).t x) (GeneratorPullback.boxGen D.toPre.P.L (fun i => (pD.pw.pr i).left) _ Oinvε (fun i => GeneratorPullback.pullAlong D.toPre.P.L (pD.pw.pr i).left ((Over.pullback (thick R I e)).map (pG.pr i)).left _ Oinvε _ (hψ i) ((U.gt e).t (pD.xe x i))))) ∧ (∀ (e : ℕ) (jNM : Fin j → D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL' : U'.LG.L.ι) (jNL : Fin j → U.LG.L.ι), res (X := (thickObj R I e G').left) (inf_le_left.trans (inf_le_left.trans inf_le_left) : (U'.gt e).pG.left ⁻¹ᵁ (LB.div (boxLB D.toPre.P.L pD.pw.pr) D'.toPre.P.L).U (jNM, jM') ⊓ (LB.div (D'.toPre.P.L.pull (U'.gt e).pG.left) (U'.LG.L.pull (fstG I e G').left)).U (fun _ => jM', fun _ => jL') ⊓ (⨅ i, ((Over.pullback (thick R I e)).map (pG.pr i)).left ⁻¹ᵁ (LB.div (D.toPre.P.L.pull (U.gt e).pG.left) (U.LG.L.pull (fstG I e G).left)).U (fun _ => jNM i, fun _ => jNL i)) ⊓ (fstG I e G').left ⁻¹ᵁ (LB.div (boxLB U.LG.L pG.pr) U'.LG.L).U (jNL, jL') ≤ (U'.gt e).pG.left ⁻¹ᵁ (LB.div (boxLB D.toPre.P.L pD.pw.pr) D'.toPre.P.L).U (jNM, jM')) (pullU (U'.gt e).pG.left _ (pD.w.s (jNM, jM'))) * res (X := (thickObj R I e G').left) (inf_le_left.trans (inf_le_left.trans inf_le_right)) ((U'.w e).s (fun _ => jM', fun _ => jL')) = (∏ i, res (X := (thickObj R I e G').left) (inf_le_left.trans (inf_le_right.trans (iInf_le _ i))) (pullU ((Over.pullback (thick R I e)).map (pG.pr i)).left _ ((U.w e).s (fun _ => jNM i, fun _ => jNL i)))) * res (X := (thickObj R I e G').left) inf_le_right (pullU (Y := (thickObj R I e G').left) (fstG I e G').left _ (wL.s (jNL, jL')))) → ∀ (k e : ℕ) (σ : Fin j → H0 U.LG.L k) (f : Fin j → ∀ α : D.toPre.X, D.toPre.SecB k α), (∀ i, U.ExpandsAt e k (σ i) (f i)) → ∀ (σ' : H0 U'.LG.L k) (f' : ∀ α' : D'.toPre.X, D'.toPre.SecB k α'), IsBoxSecG pG wL k σ' σ → IsBoxFamB pD k f' f → U'.ExpandsAt e k σ' f' := by
  intro R _ _ I j D D' A A' G G' _ _ _ _ pD pA pG U' U wL h k e σ f hE σ' f' hσ hf
  exact expandsAt_prebox h.2.2.2.2.1 h.2.2.2.2.2 k e σ f hE σ' f' hσ hf

end GlobalTheory.BoxExpPre
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SecScalBoxSecGProd
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory

lemma boxScal_prK_snd {R : Type} [CommRing R] [IsDomain R] {j : ℕ}
    {G G' : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
    (pG : IsPowGrp G' G j) (i : Fin j) :
    prK pG i ≫ pullback.snd G.hom (jK R) = pullback.snd G'.hom (jK R) := by
  unfold prK
  exact pullback.lift_snd _ _ _

end GlobalTheory
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.ExpandsBoxPre


set_option maxHeartbeats 2000000 in
theorem secScal_boxSecG_pre : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (j : ℕ) (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (pG : IsPowGrp G' G j) (U' : UnifPre I D' A' G') (U : UnifPre I D A G) (wL : LB.Iso U'.LG.L (boxLB U.LG.L pG.pr)) (hw : wL.IsGen) (k : ℕ) (s : Fin j → U.SecK k) (σ : Fin j → H0 U.LG.L k) (r : Fin j → R), (∀ i, GeneratorPullback.SecScal U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) (fun _ => (k : ℤ)) (s i) (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (k : ℤ)) (σ i) (pullback.fst G.hom (jK R)) (scal (pullback.snd G.hom (jK R) ≫ jK R) (r i))) → ∀ s' : U'.SecK k, IsBoxSecK pG wL k s' s → GeneratorPullback.SecScal U'.LG.L (fun _ : Fin 1 => pullback.fst G'.hom (jK R)) (fun _ => (k : ℤ)) s' (fun _ : Fin 1 => 𝟙 G'.left) (fun _ => (k : ℤ)) (boxSecG pG wL hw U.LG.isLB U'.LG.isLB k σ) (pullback.fst G'.hom (jK R)) (scal (pullback.snd G'.hom (jK R) ≫ jK R) (∏ i, r i)) := by
  intro R _ _ I j D D' A A' G G' _ _ _ _ pG U' U wL hw k s σ r hσ s' hs'
  intro j₁ j₂ hcoh
  have hj0 : j₁ 0 = j₂ 0 := hcoh (Sum.inl 0) (Sum.inr 0) (by simp)
  obtain ⟨jL, rfl⟩ : ∃ jL, j₁ = fun _ => jL := ⟨j₁ 0, funext fun x => by fin_cases x; rfl⟩
  obtain rfl : j₂ = fun _ => jL := funext fun x => by fin_cases x; exact hj0.symm
  set fst' := pullback.fst G'.hom (jK R) with hfst'
  set W := LB.wchart U'.LG.L (fun _ : Fin 1 => fst') (fun _ => jL) ⊓
    LB.wchart U'.LG.L (fun k => fst' ≫ (fun _ : Fin 1 => 𝟙 G'.left) k) (fun _ => jL) with hWdef
  have hcov : W ≤ ⨆ jN : Fin j → U.LG.L.ι, W ⊓ fst' ⁻¹ᵁ (boxLB U.LG.L pG.pr).U jN := by
    intro y hy
    have : fst'.base y ∈ (⨆ jN, (boxLB U.LG.L pG.pr).U jN : G'.left.Opens) := by
      rw [(linComb_isLB _ U.LG.isLB _ _).cover]; trivial
    obtain ⟨jN, hjN⟩ := TopologicalSpace.Opens.mem_iSup.1 this
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨jN, hy, hjN⟩
  apply sec_ext_cover W (fun jN => W ⊓ fst' ⁻¹ᵁ (boxLB U.LG.L pG.pr).U jN) (fun _ => inf_le_left) hcov
  intro jN
  apply ReciprocityTheory.ChartRestriction.G.Geo.Tor.fn_ext
  intro y hy
  have hyW : y ∈ W := hy.1
  have hyB : fst'.base y ∈ (boxLB U.LG.L pG.pr).U jN := hy.2
  have hyL : fst'.base y ∈ U'.LG.L.U jL := Set.mem_iInter.1 hyW.1 0
  have hyV : fst'.base y ∈ (LB.div (boxLB U.LG.L pG.pr) U'.LG.L).U (jN, jL) := ⟨hyB, hyL⟩
  set snd' := pullback.snd G'.hom (jK R) ≫ jK R with hsnd'

  set u := Geo.Tor.gs fst' y ((LB.div (boxLB U.LG.L pG.pr) U'.LG.L).U (jN, jL)) ((wL.s (jN, jL)) ^ k).val with hu
  set Lσ := Geo.Tor.gs fst' y (LB.wchart U'.LG.L (fun _ : Fin 1 => 𝟙 G'.left) (fun _ => jL))
    ((boxSecG pG wL hw U.LG.isLB U'.LG.isLB k σ).f (fun _ => jL)) with hLσ
  set S := Geo.Tor.gs (𝟙 _) y (LB.wchart U'.LG.L (fun _ : Fin 1 => fst') (fun _ => jL)) (s'.f (fun _ => jL)) with hS
  set C := Geo.Tor.gs (𝟙 _) y ⊤ (scal snd' (∏ i, r i)) with hC
  have hA : u * Lσ = ∏ i, Geo.Tor.gs (fst' ≫ (pG.pr i).left) y (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => jN i))
      ((σ i).f (fun _ => jN i)) := by
    have E := congrArg (Geo.Tor.gs fst' y ((LB.div (boxLB U.LG.L pG.pr) U'.LG.L).U (jN, jL)))
      (isBoxSecG_boxSecG pG wL hw U.LG.isLB U'.LG.isLB k σ jN jL)
    refine (congrArg (u * ·) (Geo.Tor.gs_res _ _ (boxG_le_b pG jN jL) hyV _).symm).trans ?_
    refine (Geo.Tor.gs_mul _ _ _ hyV _ _).symm.trans (E.trans ?_)
    refine (gs_prod _ _ _ hyV _ _).trans (Finset.prod_congr rfl fun i _ => ?_)
    exact (Geo.Tor.gs_res _ _ _ hyV _).trans
      (Geo.Tor.gs_pull _ _ _ _ (Set.mem_iInter.2 fun _ => by simpa using Set.mem_iInter.1 hyB i) _)
  have hB : ∀ i, Geo.Tor.gs (fst' ≫ (pG.pr i).left) y (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => jN i))
      ((σ i).f (fun _ => jN i)) = Geo.Tor.gs (𝟙 _) y ⊤ (scal snd' (r i)) *
        Geo.Tor.gs (prK pG i) y (LB.wchart U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) (fun _ => jN i))
          ((s i).f (fun _ => jN i)) := by
    intro i
    have hcoh_i : LB.Coh U.LG.L (Sum.elim (fun _ : Fin 1 => pullback.fst G.hom (jK R))
        (fun k => pullback.fst G.hom (jK R) ≫ (fun _ : Fin 1 => 𝟙 G.left) k))
        (Sum.elim (fun _ : Fin 1 => jN i) (fun _ : Fin 1 => jN i)) := by
      intro a b _; rcases a with a | a <;> rcases b with b | b <;> rfl
    have hmemK : (pullback.fst G.hom (jK R)).base ((prK pG i).base y) ∈ U.LG.L.U (jN i) := by
      rw [← Scheme.Hom.comp_apply, prK_fst, Scheme.Hom.comp_apply]
      exact Set.mem_iInter.1 hyB i
    have hyi : (prK pG i).base y ∈ LB.wchart U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) (fun _ => jN i) ⊓
        LB.wchart U.LG.L (fun k => pullback.fst G.hom (jK R) ≫ (fun _ : Fin 1 => 𝟙 G.left) k) (fun _ => jN i) :=
      ⟨Set.mem_iInter.2 fun _ => hmemK, Set.mem_iInter.2 fun _ => by simpa using hmemK⟩
    have E := congrArg (Geo.Tor.gs (prK pG i) y _) (hσ i (fun _ => jN i) (fun _ => jN i) hcoh_i)
    rw [← prK_fst]
    refine (Geo.Tor.gs_pull _ _ _ _ ?_ _).symm.trans ?_
    · exact Set.mem_iInter.2 fun _ => by simpa using hmemK
    refine (Geo.Tor.gs_res _ _ _ hyi _).symm.trans (E.trans ?_)
    refine (Geo.Tor.gs_mul _ _ _ hyi _ _).trans ?_
    congr 1
    · refine (Geo.Tor.gs_res _ _ _ hyi _).trans ?_
      show Geo.Tor.gs (prK pG i) y ⊤ (((pullback.snd G.hom (jK R) ≫ jK R).app ⊤).hom _) =
        Geo.Tor.gs (𝟙 _) y ⊤ ((snd'.app ⊤).hom _)
      refine (Geo.Tor.gs_pull (prK pG i) (pullback.snd G.hom (jK R) ≫ jK R) y ⊤ (by trivial) _).trans ?_
      refine Eq.trans ?_ (Geo.Tor.gs_pull (𝟙 _) snd' y ⊤ (by trivial) _).symm
      rw [← Category.assoc, boxScal_prK_snd, Category.id_comp]
    · exact Geo.Tor.gs_res _ _ _ hyi _
  have hCc : u * S = ∏ i, Geo.Tor.gs (prK pG i) y
      (LB.wchart U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) (fun _ => jN i)) ((s i).f (fun _ => jN i)) := by
    have hyV' : (𝟙 (pullback G'.hom (jK R)) : _ ⟶ _) y ∈ fst' ⁻¹ᵁ (LB.div (boxLB U.LG.L pG.pr) U'.LG.L).U (jN, jL) := hyV
    have E := congrArg (Geo.Tor.gs (𝟙 _) y (fst' ⁻¹ᵁ (LB.div (boxLB U.LG.L pG.pr) U'.LG.L).U (jN, jL))) (hs' jN jL)
    have hu' : Geo.Tor.gs (𝟙 _) y (fst' ⁻¹ᵁ (LB.div (boxLB U.LG.L pG.pr) U'.LG.L).U (jN, jL))
        ((pullU (Y := pullback G'.hom (jK R)) fst' _ (wL.s (jN, jL))) ^ k).val = u := by
      have e1 : ((pullU (Y := pullback G'.hom (jK R)) fst' _ (wL.s (jN, jL))) ^ k).val =
          (fst'.app _).hom ((wL.s (jN, jL)) ^ k).val := by
        rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_pow]; rfl
      rw [e1]
      exact (Geo.Tor.gs_pull _ _ _ _ hyV _).trans (by rw [Category.id_comp])
    refine (congrArg₂ (· * ·) hu'.symm (Geo.Tor.gs_res _ _ (boxSec_le_a pG jN jL) hyV' _).symm).trans ?_
    refine (Geo.Tor.gs_mul _ _ _ hyV' _ _).symm.trans (E.trans ?_)
    refine (gs_prod _ _ _ hyV' _ _).trans (Finset.prod_congr rfl fun i _ => ?_)
    refine (Geo.Tor.gs_res _ _ _ hyV' _).trans
      ((Geo.Tor.gs_pull (𝟙 _) (prK pG i) y
        (LB.wchart U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) (fun _ => jN i))
        (boxSec_le_b pG jN jL i hyV') _).trans ?_)
    rw [Category.id_comp]
  have hD : C = ∏ i, Geo.Tor.gs (𝟙 _) y ⊤ (scal snd' (r i)) := by
    rw [hC, show scal snd' (∏ i, r i) = ∏ i, scal snd' (r i) by simp [scal, map_prod],
      gs_prod _ _ _ (by trivial)]
  have hU : IsUnit u := by
    rw [hu, Geo.Tor.gs_unit _ _ _ hyV]; exact Units.isUnit _
  have hmain : Lσ = C * S := by
    apply hU.mul_left_cancel
    rw [hA, Finset.prod_congr rfl (fun i _ => hB i), Finset.prod_mul_distrib, ← hD, ← hCc]
    ring
  have hLg : Geo.Tor.gs (𝟙 _) y (W ⊓ fst' ⁻¹ᵁ (boxLB U.LG.L pG.pr).U jN) (rs (inf_le_left : W ⊓ fst' ⁻¹ᵁ (boxLB U.LG.L pG.pr).U jN ≤ W)
      (rs (inf_le_right.trans (fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k) :
        W ≤ fst' ⁻¹ᵁ LB.wchart U'.LG.L (fun _ : Fin 1 => 𝟙 G'.left) (fun _ => jL))
        ((fst'.app (LB.wchart U'.LG.L (fun _ : Fin 1 => 𝟙 G'.left) (fun _ => jL))).hom
          ((boxSecG pG wL hw U.LG.isLB U'.LG.isLB k σ).f (fun _ => jL))))) = Lσ := by
    refine (Geo.Tor.gs_res _ _ _ hy _).trans ((Geo.Tor.gs_res _ _ _ hyW _).trans
      ((Geo.Tor.gs_pull _ _ _ _ ?_ _).trans ?_))
    · exact Set.mem_iInter.2 fun _ => by simpa using hyL
    · rw [Category.id_comp]
  have hRg : Geo.Tor.gs (𝟙 _) y (W ⊓ fst' ⁻¹ᵁ (boxLB U.LG.L pG.pr).U jN) (rs (inf_le_left : W ⊓ fst' ⁻¹ᵁ (boxLB U.LG.L pG.pr).U jN ≤ W)
      (resTop W (scal snd' (∏ i, r i)) * rs (inf_le_left : W ≤ LB.wchart U'.LG.L (fun _ : Fin 1 => fst') (fun _ => jL))
        (s'.f (fun _ => jL)))) = C * S := by
    refine (Geo.Tor.gs_res _ _ _ hy _).trans ((Geo.Tor.gs_mul _ _ _ hyW _ _).trans ?_)
    congr 1
    · exact Geo.Tor.gs_res _ _ _ hyW _
    · exact Geo.Tor.gs_res _ _ _ hyW _
  exact hLg.trans (hmain.trans hRg.symm)


set_option maxHeartbeats 1000000 in
theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (j : ℕ) (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre D.toPre j) (pA : IsPowPolAV A' A j) (pG : IsPowGrp G' G j) (U' : UnifPre I D' A' G') (U : UnifPre I D A G) (wL : LB.Iso U'.LG.L (boxLB U.LG.L pG.pr)), (∀ i, U'.gen.hom ≫ pA.pr i = (Over.pullback (jK R)).map (pG.pr i) ≫ U.gen.hom) ∧ wL.IsGen ∧ (∃ b : LB.Gen (LB.LinComb U.LG.L (K := Fin j) (fun i => eSec G' ≫ (pG.pr i).left) (fun _ => 1)), GeneratorPullback.MapsAt U.LG.L U'.LG.L (fun i => (pG.pr i).left) wL (eSec G') 1 U'.LG.rig b ∧ LB.Gen.Corr U.LG.L _ _ _ _ b (GeneratorPullback.finProdGen U.LG.L (J := Fin j) (fun _ _ => eSec G) (fun _ _ => 1) (fun _ => U.LG.rig))) ∧ (∀ (e : ℕ) (i : Fin j), (U'.gt e).q ≫ (Over.pullback (thick R I e)).map (pD.pw.pr i) = (Over.pullback (thick R I e)).map (pG.pr i) ≫ (U.gt e).q) ∧ (∀ (e : ℕ) (x : D'.toPre.X), ∃ hψ : ∀ (i : Fin j) (k : Fin 4), D'.toPre.Oφ ((Over.map (thick R I e)).map (U'.gt e).q ≫ D'.toPre.prBe I e) x k ≫ (pD.pw.pr i).left = ((Over.pullback (thick R I e)).map (pG.pr i)).left ≫ D.toPre.Oφ ((Over.map (thick R I e)).map (U.gt e).q ≫ D.toPre.prBe I e) (pD.xe x i) k, LB.Gen.Maps (LB.linCombIso pD.w _ Oinvε) ((U'.gt e).t x) (GeneratorPullback.boxGen D.toPre.P.L (fun i => (pD.pw.pr i).left) _ Oinvε (fun i => GeneratorPullback.pullAlong D.toPre.P.L (pD.pw.pr i).left ((Over.pullback (thick R I e)).map (pG.pr i)).left _ Oinvε _ (hψ i) ((U.gt e).t (pD.xe x i))))) ∧ (∀ (e : ℕ) (jNM : Fin j → D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL' : U'.LG.L.ι) (jNL : Fin j → U.LG.L.ι), res (X := (thickObj R I e G').left) (inf_le_left.trans (inf_le_left.trans inf_le_left) : (U'.gt e).pG.left ⁻¹ᵁ (LB.div (boxLB D.toPre.P.L pD.pw.pr) D'.toPre.P.L).U (jNM, jM') ⊓ (LB.div (D'.toPre.P.L.pull (U'.gt e).pG.left) (U'.LG.L.pull (fstG I e G').left)).U (fun _ => jM', fun _ => jL') ⊓ (⨅ i, ((Over.pullback (thick R I e)).map (pG.pr i)).left ⁻¹ᵁ (LB.div (D.toPre.P.L.pull (U.gt e).pG.left) (U.LG.L.pull (fstG I e G).left)).U (fun _ => jNM i, fun _ => jNL i)) ⊓ (fstG I e G').left ⁻¹ᵁ (LB.div (boxLB U.LG.L pG.pr) U'.LG.L).U (jNL, jL') ≤ (U'.gt e).pG.left ⁻¹ᵁ (LB.div (boxLB D.toPre.P.L pD.pw.pr) D'.toPre.P.L).U (jNM, jM')) (pullU (U'.gt e).pG.left _ (pD.w.s (jNM, jM'))) * res (X := (thickObj R I e G').left) (inf_le_left.trans (inf_le_left.trans inf_le_right)) ((U'.w e).s (fun _ => jM', fun _ => jL')) = (∏ i, res (X := (thickObj R I e G').left) (inf_le_left.trans (inf_le_right.trans (iInf_le _ i))) (pullU ((Over.pullback (thick R I e)).map (pG.pr i)).left _ ((U.w e).s (fun _ => jNM i, fun _ => jNL i)))) * res (X := (thickObj R I e G').left) inf_le_right (pullU (Y := (thickObj R I e G').left) (fstG I e G').left _ (wL.s (jNL, jL')))) → ∀ (k : ℕ) (s : Fin j → U.SecK k) (Fs : Fin j → Fam D.toPre (FractionRing R) k), (∀ i, U.Expands k (s i) (Fs i)) → ∀ (s' : U'.SecK k) (F' : Fam D'.toPre (FractionRing R) k), IsBoxSecK pG wL k s' s → IsBoxFam pD (FractionRing R) k F' Fs → U'.Expands k s' F' := by
  intro R _ _ I j D D' A A' G G' _ _ _ _ pD pA pG U' U wL h k s Fs hs s' F' hs' hF'
  choose r hr σ f hσ hf hE using hs
  refine ⟨∏ i, r i, Finset.prod_ne_zero_iff.2 fun i _ => hr i,
    boxSecG pG wL h.2.1 U.LG.isLB U'.LG.isLB k σ, boxFamB pD k f,
    secScal_boxSecG_pre R I j D D' A A' G G' pG U' U wL h.2.1 k s σ r hσ s' hs',
    fun α' => GlobalTheory.BoxFamScalar.main R I j D D' pD k Fs f r hf F' hF' α', fun e => ?_⟩
  exact GlobalTheory.BoxExpPre.expandsAt_box_unifPre R I j D D' A A' G G' pD pA pG U' U wL h k e σ f (fun i => hE i e) _ _
    (isBoxSecG_boxSecG pG wL h.2.1 U.LG.isLB U'.LG.isLB k σ) (isBoxFamB_boxFamB pD k f)

end GlobalTheory.ExpandsBoxPre
