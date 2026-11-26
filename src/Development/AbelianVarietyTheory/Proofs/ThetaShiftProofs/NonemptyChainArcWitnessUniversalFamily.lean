module

public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNeZeroIff
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsChartLoc
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsSecThroughUp

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstPtsAddSmul
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.ArcPts
open ConstGrp

theorem constPts_add_smul : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (Ξ : ConstPts W Λ) , (∀ v v', Ξ.x (v + v') = Ξ.x v * Ξ.x v') ∧ ∀ (e : 𝓞 E) v, Ξ.x (Λ.A.actV e v) = Ξ.x v ≫ W.t.act.act e := by
  intro hL hL2 E _ _ _ H _ D l Xo c O _ β Y _ _ b a χ W Λ Ξ
  obtain ⟨hadd, -, hact⟩ := GlobalTheory.T.analyticDictionaryExp_additive_surjective_linear hL hL2 E H D l c O β b a Λ
  have hG := hL.globalFns
  obtain ⟨gp, hw, -, ho, -, -⟩ := W.spec
  have hw' := (isGen_iff _).1 hw
  have hb : ∀ v, (Ξ.g v).b.left ≫ W.φ = spMap (PowerSeries.C (R := ℂ)) ≫ (Λ.ex0 v).b.left :=
    fun v => (Ξ.g_rel v 0).1 2
  let ρ : Over.mk (selfR.hom ≫ spMap (PowerSeries.C (R := ℂ))) ⟶ Out.TF (R := ℂ) ℂ :=
    Over.homMk (spMap (PowerSeries.C (R := ℂ))) (by
      rw [← Over.w (Λ.ex0 0).b]
      refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) (hb 0).symm).trans ?_)
      refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) gp.1.w).trans ?_)
      exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (Over.w (Ξ.g 0).b)))
  have r : ∀ v, Rel gp W.w W.e ρ (Ξ.g v) (Λ.ex0 v) := fun v =>
    rel_of_pmaps (fun x => (Ξ.g_rel v x).1) fun x =>
      pmaps_of_genRelR hw' W.P.D.toPre.P.isLB a.D₀.P.isLB ((Ξ.g v).isGen _)
        (DVR.pullGen_isGen _ _ _ _ ((Λ.ex0 v).isGen x) _) (Ξ.g_rel v x)
  have hc : ∀ x, pushHom gp selfR (DVR.cP W.P.D.toPre selfR (W.e x)) = ρ ≫ DVR.cP a.D₀ _ x := fun x =>
    Over.OverMorphism.ext ((Ξ.g_rel 0 x).1 1)
  have : IsHausdorff ((Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map (algebraMap ℂ⟦X⟧ ℂ⟦X⟧)) ℂ⟦X⟧ := by
    rw [Algebra.algebraMap_self, Ideal.map_id]
    infer_instance
  refine ⟨fun v v' => (Ξ.x_pt (v + v')).unique (((Ξ.x_pt v).mul hG (Ξ.x_pt v')
    (isAdd_of_rel hG hw' hc W.e.surjective (r v) (r v') (r (v + v')) (hadd v v')))), fun e v => ?_⟩
  have hs := hact e v
  clear hact hadd
  have r₁ := r v
  have r₂ := r (Λ.A.actV e v)
  have x₁ := Ξ.x_pt v
  have x₂ := Ξ.x_pt (Λ.A.actV e v)
  letI := H.starRing
  exact x₂.unique (x₁.smul hG W.P.lin e
    (isSmulPt_of_rel hG hw' hc W.e.surjective W.P.oD a.oa (fun s x => W.e.map_smul s x) ho e r₁ r₂ hs))

end GlobalTheory.ArcPts
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GenericPointsConstantPointsFormalSumValues
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstantPointFrameIsFrameWithRigidification
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstantPointFrameIsFrameWithRigidification
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.ConstFrame

theorem valR_g_self {A : Type} [CommRing A] [IsLocalRing A] {Z : Scheme.{0}} {L : LB Z} (hL : L.IsLB) (x : Sp A ⟶ Z)
    (j : L.ι) (h : ⊤ ≤ x ⁻¹ᵁ L.U j) : valR x (L.U j ⊓ L.U j) (L.g j j).val = 1 := by
  have toStkA_valR {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (z : Sp A) (ht : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(X, U)ˣ) :
      toStkA z (valR x U a.val) = (gm x z U a).val := by
    have hz : x z ∈ U := ht (show z ∈ (⊤ : (Sp A).Opens) from trivial)
    have e1 : ∀ c, (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom c) = c :=
      fun c => congrArg (fun f => CommRingCat.Hom.hom f c) (Iso.hom_inv_id (Scheme.ΓSpecIso (CommRingCat.of A)))
    rw [valR, dif_pos ht, gm, dif_pos hz]
    show ((Sp A).presheaf.germ ⊤ z trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
        ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom ((x.appLE U ⊤ ht).hom a.val))) =
      ((Sp A).presheaf.germ (x ⁻¹ᵁ U) z hz).hom ((x.app U).hom a.val)
    rw [e1]
    exact TopCat.Presheaf.germ_res_apply (Sp A).presheaf (homOfLE ht) z trivial ((x.app U).hom a.val)
  apply toStkA_injective
  rw [toStkA_valR x (L.U j ⊓ L.U j) _ (fun _ hz => ⟨h hz, h hz⟩), map_one]
  exact congrArg Units.val (gm_self hL x _ (h trivial))

theorem valR_rig {A A₀ : Type} [CommRing A] [IsLocalRing A] [CommRing A₀] {B : Over (Sp A)} {B₀ : Over (Sp A₀)}
    [GrpObj B] [IsCommMonObj B] [GrpObj B₀] [IsCommMonObj B₀] {M : LB B.left} {M₀ : LB B₀.left} (f : A₀ →+* A)
    {φ : B.left ⟶ B₀.left} (he : eSec B ≫ φ = spMap f ≫ eSec B₀) (w : LB.Iso M (M₀.pull φ))
    (r : LB.Gen (M.pull (eSec B))) (r₀ : LB.Gen (M₀.pull (eSec B₀)))
    (h : LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec B) (fun _ => 1)) r (rigPullOf φ (spMap f) he M₀ r₀))
    (j : M.ι) (j₀ : M₀.ι) (hj : ⊤ ≤ (show Sp A ⟶ _ from eSec B) ⁻¹ᵁ (LB.div (M₀.pull φ) M).U (fun _ => j₀, j))
    (hj₀ : ⊤ ≤ (M₀.pull (eSec B₀)).U (fun _ => j₀)) :
    f (valR (𝟙 (Sp A₀)) ((M₀.pull (eSec B₀)).U (fun _ => j₀)) (r₀.s (fun _ => j₀)).val) =
      valR (A := A) (eSec B) _ (w.s (fun _ => j₀, j)).val *
        valR (𝟙 (Sp A)) ((M.pull (eSec B)).U (fun _ => j)) (r.s (fun _ => j)).val := by
  have hc := hj (show cpt A ∈ (⊤ : (Sp A).Opens) from trivial)
  have e := gm_maps_pt h (𝟙 (Sp A)) (cpt A) (fun _ => j₀) j hc.1 hc.2
  have hr : ⊤ ≤ (𝟙 (Sp A)) ⁻¹ᵁ (M.pull (eSec B)).U (fun _ => j) := fun z hz => mem_pull.2 (hj hz).2
  have h₀ : ⊤ ≤ (𝟙 (Sp A₀)) ⁻¹ᵁ (M₀.pull (eSec B₀)).U (fun _ => j₀) := hj₀
  have h₁ := FormalValue.top_le_comp h₀ (spMap f)
  apply toStkA_injective
  refine Eq.trans ?_ ((congrArg Units.val e).trans ?_)
  · refine (congrArg _ (FormalValue.valR_spMap f _ _ h₀ _).symm).trans ((toStkA_valR _ _ _ h₁ _).trans
      (congrArg Units.val ?_))
    have hm : (𝟙 (Sp A) : Sp A ⟶ Sp A) (cpt A) ∈ ((M₀.pull φ).pull (eSec B)).U (fun _ _ => j₀) := mem_pull.2 hc.1
    refine Eq.trans ?_ ((gm_res (𝟙 (Sp A)) _ _ hm _).trans (gm_pull (𝟙 (Sp A)) (spMap f) _ _ (hj₀ trivial) _)).symm
    rw [Category.id_comp, Category.comp_id]
  · refine Eq.trans ?_ (map_mul _ _ _).symm
    exact (Units.val_mul _ _).trans (congrArg₂ (· * ·) (toStkA_valR (A := A) (eSec B) _ _ hj _).symm
      (toStkA_valR _ _ _ hr _).symm)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)]
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
variable [Algebra (FractionRing ℂ) ℂ] {Y : Model Xo c β} {b : O →+* ℂ} {a : ArcIn D l β ℂ b} {χ : Sp ℂ⟦X⟧ ⟶ Y.X}
  {W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ} {Λ : GtAn a}
  (Ξ : ConstPts W Λ)


omit [Algebra (FractionRing ℂ) ℂ] in
theorem complete : IsAdicComplete ((Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map (algebraMap ℂ⟦X⟧ ℂ⟦X⟧)) ℂ⟦X⟧ := by
  rw [Algebra.algebraMap_self, Ideal.map_id]
  infer_instance

theorem base_comp (v : Λ.A.V) :
    (show Sp ℂ⟦X⟧ ⟶ _ from (Ξ.g v).b.left) ≫ W.φ = spMap (PowerSeries.C (R := ℂ)) ≫ (Λ.u.ex v.2).left :=
  ((Ξ.g_rel v 0).1 2).trans (congrArg (spMap (PowerSeries.C (R := ℂ)) ≫ ·) (Λ.ex0_b v))

theorem exists_charts (v : Λ.A.V) : ∃ (jM : W.P.D.toPre.P.L.ι) (j₀ : a.D₀.P.L.ι),
    ⊤ ≤ (show Sp ℂ⟦X⟧ ⟶ _ from (Ξ.g v).b.left) ⁻¹ᵁ (LB.div (a.D₀.P.L.pull W.φ) W.P.D.toPre.P.L).U (fun _ => j₀, jM) ∧
    ⊤ ≤ (Λ.u.ex v.2).left ⁻¹ᵁ a.D₀.P.L.U j₀ := by
  obtain ⟨jM, hM⟩ := exists_chart W.P.D.toPre.P.isLB ((show Sp ℂ⟦X⟧ ⟶ _ from (Ξ.g v).b.left) (cpt ℂ⟦X⟧))
  have h₀ := FrameValue.le_chartAt a.D₀.P.isLB (Λ.u.ex v.2).left
  refine ⟨jM, _, (top_le_iff_cpt _ _).2 ⟨mem_pull.2 ?_, hM⟩, h₀⟩
  exact (congrArg (fun q => q (cpt ℂ⟦X⟧) ∈ a.D₀.P.L.U _) (base_comp Ξ v)).mpr (FormalValue.top_le_comp h₀ _ trivial)

theorem isFrm (v : Λ.A.V) : IsFrm W.P.U.LG.L (Ξ.x v).left (Ξ.τ v) := by
  haveI := complete
  obtain ⟨jM, j₀, hj, h₀⟩ := exists_charts Ξ v
  have hw := FormalValue.isUnit_valR (A := ℂ⟦X⟧) (Ξ.g v).b.left _ hj (W.w.s (fun _ => j₀, jM))
  have hM : ⊤ ≤ FormalValue.basePt (Ξ.g v) ⁻¹ᵁ W.P.D.toPre.P.L.U jM := fun z hz => (hj hz).2
  refine ⟨fun j h => ?_, fun j j' h => ?_⟩
  · refine isUnit_of_mul_isUnit_right ((congrArg IsUnit (Ξ.τ_eq v j jM j₀ h hj)).mpr ?_)
    exact (Units.isUnit _).mul ((Ne.isUnit (Λ.u.fr_ne j₀ v.2 h₀)).map _)
  · have h₁ : ⊤ ≤ (Ξ.x v).left ⁻¹ᵁ W.P.U.LG.L.U j := fun z hz => (h hz).1
    have h₂ : ⊤ ≤ (Ξ.x v).left ⁻¹ᵁ W.P.U.LG.L.U j' := fun z hz => (h hz).2
    have t := FormalValue.tau_trans (Ξ.x_fm v) h₁ h₂ hM hM
    rw [valR_g_self W.P.D.toPre.P.isLB _ jM hM, _root_.mul_one] at t
    have e₁ := Ξ.τ_eq v j jM j₀ h₁ hj
    have e₂ := Ξ.τ_eq v j' jM j₀ h₂ hj
    refine hw.mul_left_cancel (e₁.trans ?_)
    refine (congrArg (· * _) t).trans ?_
    rw [_root_.mul_assoc, mul_left_comm]
    exact (mul_left_comm _ _ _).trans ((congrArg (_ * ·) e₂.symm).trans (mul_left_comm _ _ _))

theorem tau_zero (hx : Ξ.x 0 = 1) (j : W.P.U.LG.L.ι) (h : ⊤ ≤ (Ξ.x 0).left ⁻¹ᵁ W.P.U.LG.L.U j) :
    Ξ.τ 0 j = valR (𝟙 (Sp ℂ⟦X⟧)) ((W.P.U.LG.L.pull (eSec W.t.G)).U (fun _ => j))
      (W.P.U.LG.rig.s (fun _ => j)).val := by
  haveI := complete
  have hs : spMap (algebraMap ℂ⟦X⟧ ℂ⟦X⟧) = 𝟙 _ := Spec.map_id _
  obtain ⟨jM, j₀, hj, h₀⟩ := exists_charts Ξ 0
  have hw := FormalValue.isUnit_valR (A := ℂ⟦X⟧) (Ξ.g 0).b.left _ hj (W.w.s (fun _ => j₀, jM))
  have hM : ⊤ ≤ FormalValue.basePt (Ξ.g 0) ⁻¹ᵁ W.P.D.toPre.P.L.U jM := fun z hz => (hj hz).2
  have hx' : (Ξ.x 0).left = spMap (algebraMap ℂ⟦X⟧ ℂ⟦X⟧) ≫ eSec W.t.G := by
    refine (congrArg Over.Hom.left hx).trans ?_
    exact congrArg (· ≫ eSec W.t.G) ((Category.comp_id _).symm.trans (Over.w (toUnit selfR)))
  have hu : (Λ.u.ex (0 : Λ.A.V).2).left = eSec a.D₀.P.A := by
    refine (congrArg Over.Hom.left ((Λ.u.ker 0).2 Λ.u.Λ.zero_mem)).trans ?_
    rw [Hom.one_def]; simp [eSec]
  have hb : FormalValue.basePt (Ξ.g 0) = eSec W.P.D.toPre.P.A := by
    refine W.spec.1.1.hom_ext ?_ ?_
    · exact (base_comp Ξ 0).trans ((congrArg (_ ≫ ·) hu).trans W.he.symm)
    · exact (Over.w (Ξ.g 0).b).trans (hs.trans (Over.w η[W.P.D.toPre.P.A]).symm)
  have hb' : FormalValue.basePt (Ξ.g 0) = spMap (algebraMap ℂ⟦X⟧ ℂ⟦X⟧) ≫ eSec W.P.D.toPre.P.A :=
    hb.trans ((Category.id_comp _).symm.trans (congrArg (· ≫ _) hs.symm))
  have hf := Ξ.x_fm 0
  have e := Ξ.τ_eq 0 j jM j₀ h hj
  rw [hx'] at hf h e
  have t := FormalValue.tau_rig hf hb' h hM
  have hj₀ : ⊤ ≤ (a.D₀.P.L.pull (eSec a.D₀.P.A)).U (fun _ => j₀) := fun z hz =>
    mem_pull.2 ((congrArg (fun q => q z ∈ a.D₀.P.L.U j₀) hu).mp (h₀ hz))
  have r := valR_rig (PowerSeries.C (R := ℂ)) W.he W.w W.P.D.toPre.rig a.D₀.rig W.spec.2.2.1 jM j₀ (hb ▸ hj) hj₀
  have f := (congrArg (PowerSeries.C (R := ℂ)) (Λ.rig (fun _ => j₀) hj₀)).trans r
  replace f := f.trans (congrArg (fun q => valR (A := ℂ⟦X⟧) q _ (W.w.s (fun _ => j₀, jM)).val * _) hb.symm)
  refine hw.mul_left_cancel (e.trans ((congrArg (_ * ·) f).trans ((mul_left_comm _ _ _).trans (congrArg (_ * ·) ?_))))
  have t' := t
  generalize FormalValue.tau W.P.U.toUnifPre ((Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map (algebraMap ℂ⟦X⟧ ℂ⟦X⟧))
    (spMap (algebraMap ℂ⟦X⟧ ℂ⟦X⟧) ≫ eSec W.t.G) j jM = q at t' ⊢
  rw [hs] at t'
  exact t'


omit [Algebra (FractionRing ℂ) ℂ] in
theorem main : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (Ξ : ConstPts W Λ) , (∀ v, IsFrm W.P.U.LG.L (Ξ.x v).left (Ξ.τ v)) ∧ ∀ j, ⊤ ≤ (Ξ.x 0).left ⁻¹ᵁ W.P.U.LG.L.U j → Ξ.τ 0 j = valR (𝟙 (Sp ℂ⟦X⟧)) ((W.P.U.LG.L.pull (eSec W.t.G)).U (fun _ => j)) (W.P.U.LG.rig.s (fun _ => j)).val := by
  intro h₁ h₂ E _ _ _ H _ D l Xo c O _ β Y _ _ b a χ W Λ Ξ
  refine ⟨isFrm Ξ, tau_zero Ξ ?_⟩
  have h := (GlobalTheory.ArcPts.constPts_add_smul h₁ h₂ E H D l Xo c O β Y b a χ W Λ Ξ).1 0 0
  rw [add_zero] at h
  exact left_eq_mul.1 h

end GlobalTheory.ConstFrame
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstantPointFrameIsFrameWithRigidificationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constantPointFrame_isFrame_with_rigidification : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (Ξ : ConstPts W Λ) , (∀ v, IsFrm W.P.U.LG.L (Ξ.x v).left (Ξ.τ v)) ∧ ∀ j, ⊤ ≤ (Ξ.x 0).left ⁻¹ᵁ W.P.U.LG.L.U j → Ξ.τ 0 j = valR (𝟙 (Sp ℂ⟦X⟧)) ((W.P.U.LG.L.pull (eSec W.t.G)).U (fun _ => j)) (W.P.U.LG.rig.s (fun _ => j)).val := by
  first | exact @GlobalTheory.ConstFrame.main | exact GlobalTheory.ConstFrame.main | (intros; apply GlobalTheory.ConstFrame.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GenericPointsConstantPointsFormalSumValues
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.GenericPoints

theorem main : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (Ξ : ConstPts W Λ) , ∃ Φ : GenPts Λ.A W.t gen, Ξ.IsGen Φ := by
  intro h₁ h₂ E _ _ _ H _ D l Xo c O _ β Y _ _ b a χ W Λ Ξ
  have g := GlobalTheory.ArcPts.constPts_add_smul h₁ h₂ E H D l Xo c O β Y b a χ W Λ Ξ
  have f := GlobalTheory.T.constantPointFrame_isFrame_with_rigidification h₁ h₂ E H D l Xo c O β Y b a χ W Λ Ξ
  exact exists_genPts Λ.A W.t W.P.U.LG W.P.bundle Ξ.x Ξ.τ g.1 g.2 f.1 f.2
    (fun j _ α th hth => GlobalTheory.T.exists_section_values_formalThetaSum h₁ h₂ E H D l Xo c O β Y b a χ W Λ Ξ j α th hth)
    (fun j _ σ => GlobalTheory.ConstSpan.main h₁ h₂ E H D l Xo c O β Y b a χ W Λ Ξ j σ)
    (fun k hk s => exists_clear W.P.U k hk s)

end GlobalTheory.GenericPoints
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GenericPointsConstantPointsFormalSumValuesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericPoints_constantPoints_formalSum_values : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (Ξ : ConstPts W Λ) , ∃ Φ : GenPts Λ.A W.t gen, Ξ.IsGen Φ := by
  first | exact @GlobalTheory.GenericPoints.main | exact GlobalTheory.GenericPoints.main | (intros; apply GlobalTheory.GenericPoints.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyConstPts
namespace GlobalTheory.ConstPoint

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

theorem nonempty_constPts : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) , Nonempty (ConstPts W Λ) := by
  intro _ _ E _ _ _ H _ D l Xo c O _ β Y _ _ b a χ W Λ
  choose g x τ h₁ h₂ h₃ h₄ using fun v : Λ.A.V => exists_constPoint W Λ.u (Λ.ex0 v) v.2 (Λ.ex0_b v)
  exact ⟨⟨g, h₁, x, h₂, h₃, τ, h₄⟩⟩

end GlobalTheory.ConstPoint
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyChainArcWitnessUniversalFamily
noncomputable section
namespace GlobalTheory.ArcPts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

theorem algebraMap_laurent_comp_C :
    (algebraMap ℂ⟦X⟧ ℂ⸨X⸩).comp (PowerSeries.C (R := ℂ)) = algebraMap ℂ ℂ⸨X⸩ :=
  RingHom.ext fun _ => rfl

theorem X_not_mem_gen (p : Sp ℂ⸨X⸩) : PowerSeries.X ∉ (gen p).asIdeal := by
  intro h
  have h' : algebraMap ℂ⟦X⟧ ℂ⸨X⸩ PowerSeries.X ∈ p.asIdeal := h
  have hne : algebraMap ℂ⟦X⟧ ℂ⸨X⸩ PowerSeries.X ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective ℂ⟦X⟧ ℂ⸨X⸩)).2 PowerSeries.X_ne_zero
  exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h' (IsUnit.mk0 _ hne))

theorem exists_generic_point {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
    (Y : Model Xo c β) (bF : c.F →+* ℂ) (χ : Sp ℂ⟦X⟧ ⟶ Y.X)
    (hχ : χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (bF.comp β))
    (hab : ∀ x : Sp ℂ⟦X⟧, PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) :
    ∃ yF : Sp ℂ⸨X⸩ ⟶ Xo.XF c, yF ≫ Y.j = gen ≫ χ ∧
      yF ≫ pullback.snd _ _ = spMap ((algebraMap ℂ ℂ⸨X⸩).comp bF) := by
  have h : (gen ≫ χ) ≫ Y.s = spMap ((algebraMap ℂ ℂ⸨X⸩).comp bF) ≫ spMap β := by
    rw [Category.assoc, hχ, ← algebraMap_laurent_comp_C, spMap_comp, spMap_comp, spMap_comp]
    simp only [Category.assoc]
  have := Y.jQ_open
  have hr : Set.range (pullback.lift _ _ h) ⊆ Set.range Y.jQ := by
    rintro _ ⟨p, rfl⟩
    obtain ⟨q, hq⟩ := hab _ (X_not_mem_gen p)
    have hz : Y.jQ q ∈ pullback.fst Y.s (spMap β) ⁻¹' abLocus Y.t.G := by
      rw [Y.ab_gen]; exact ⟨_, rfl⟩
    have hz' : Y.j q ∈ abLocus Y.t.G := by
      simpa only [Model.j, Scheme.Hom.comp_apply, Set.mem_preimage] using hz
    rw [← Y.ab_gen, Set.mem_preimage, ← Scheme.Hom.comp_apply, pullback.lift_fst, Scheme.Hom.comp_apply, ← hq]
    exact hz'
  have hτ := IsOpenImmersion.lift_fac Y.jQ _ hr
  refine ⟨IsOpenImmersion.lift Y.jQ _ hr, ?_, ?_⟩
  · rw [Model.j, ← Category.assoc, hτ, pullback.lift_fst]
  · rw [← Y.jQ_over, ← Category.assoc, hτ, pullback.lift_snd]

theorem nonempty_chain : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (bF : c.F →+* ℂ) (a : ArcIn D l β ℂ (bF.comp β)) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) , χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (bF.comp β) → (∀ x : Sp ℂ⟦X⟧, PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) → Nonempty (Chain W Λ) := by
  intro L₁ L₂ E _ _ _ H _ D l Xo c O _ β Y _ _ bF a χ W Λ hχ hab
  obtain ⟨Ξ⟩ := GlobalTheory.ConstPoint.nonempty_constPts L₁ L₂ E H D l Xo c O β Y _ a χ W Λ
  obtain ⟨ΦW, hW⟩ := GlobalTheory.T.genericPoints_constantPoints_formalSum_values L₁ L₂ E H D l Xo c O β Y _ a χ W Λ Ξ
  obtain ⟨yF, hj, ho⟩ := exists_generic_point Y bF χ hχ hab
  obtain ⟨w₂, r₂⟩ := (GlobalTheory.T.exists_rigidifiedIso_agree_abelianFibres L₁ L₂ E H _ _ Y.t W.t χ W.m).1
  obtain ⟨w₁, r₁⟩ := (GlobalTheory.T.exists_rigidifiedIso_agree_abelianFibres L₁ L₂ E H _ _ Y.t Y.oF.t _ Y.m).1
  obtain ⟨w₀, r₀⟩ := (GlobalTheory.T.exists_rigidifiedIso_agree_abelianFibres L₁ L₂ E H _ _ Xo.univ.t Y.oF.t _ Y.m0.toSABMap).1
  obtain ⟨ΦY, e₂⟩ := (GlobalTheory.ArcPts.genPts_transfer E H _ _ Λ.A Y.t W.t χ W.m w₂ gen (gen ≫ χ) r₂ rfl).1 ΦW
  obtain ⟨ΦF, e₁⟩ := (GlobalTheory.ArcPts.genPts_transfer E H _ _ Λ.A Y.t Y.oF.t _ Y.m w₁ yF (gen ≫ χ) r₁ hj).2 ΦY
  obtain ⟨Φ, e₀⟩ := (GlobalTheory.ArcPts.genPts_transfer E H _ _ Λ.A Xo.univ.t Y.oF.t _ Y.m0.toSABMap w₀ yF
    (yF ≫ pullback.fst _ _) r₀ rfl).1 ΦF
  exact ⟨⟨Ξ, ΦW, hW, yF, hj, ho, ΦY, ΦF, Φ, w₂, w₁, w₀, r₂, r₁, r₀, e₂, e₁, e₀⟩⟩

end GlobalTheory.ArcPts
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyChainArcWitnessUniversalFamilyStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_chain_arc_witness_universal_family : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (bF : c.F →+* ℂ) (a : ArcIn D l β ℂ (bF.comp β)) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) , χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (bF.comp β) → (∀ x : Sp ℂ⟦X⟧, PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) → Nonempty (Chain W Λ) := by
  first | exact @GlobalTheory.ArcPts.nonempty_chain | exact GlobalTheory.ArcPts.nonempty_chain | (intros; apply GlobalTheory.ArcPts.nonempty_chain <;> assumption)
end
