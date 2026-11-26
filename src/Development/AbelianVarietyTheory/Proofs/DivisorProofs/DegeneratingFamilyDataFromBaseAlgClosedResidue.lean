module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsTailExtra
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowerDatumObjectComesFromBaseOfLinearPoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicCompleteOfLeOfIsNoetherianRingStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InhabitedAndRefines
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.PolDeg
variable {R : Type} [CommRing R] [IsDomain R]

def ofDeg (D : DegPre R) (hB : D.TauBimult) : Data R := Wit.ofDeg D hB

theorem refines_ofDeg (D : DegPre R) (hB : D.TauBimult) :
    Refines (ofDeg D hB) (RingHom.id R) D (AddEquiv.refl _) :=
  Wit.refines_ofDeg D hB


end GlobalTheory.PolDeg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPeriodsMonomialFamilyCoordsOverBase
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegDataDifferBySymmBalancedFormOfPsiTau
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiUnitOnUnivOfPullbackReadTop
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiUnitOnUnivOfPullbackReadTop
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PullTopUnit
open GlobalTheory.ArcPull
open GlobalTheory.PsiEvenPull (proj)

theorem psiUnitOn_pull_top {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'}
    {D : DegPre R} {D' : DegPre R'} (hD : IsPullDeg φ D D') (hW : hD.W = ⊤) (x : D'.X) :
    PsiUnitOn D' x Set.univ := by
  have hI : IsIso hD.W.ι := by rw [hW, ← Scheme.topIso_hom]; infer_instance
  let h : Sp R' ⟶ (TW hD.W).left := specOf φ ≫ inv hD.W.ι
  have hh : h ≫ hD.W.ι = specOf φ := by simp [h]
  have hg : hD.g = jK R' ≫ h := by
    rw [← cancel_mono hD.W.ι, hD.g_comm, Category.assoc, hh]
  have sq : (D'.c x).left ≫ proj hD = h ≫ (toUnit (TW hD.W) ≫ D.c (hD.xe x)).left := by
    rw [hD.c_pr x, ← hh, Category.assoc]; rfl
  obtain ⟨a, ha, va⟩ := exists_down_om hD.w_gen D.P.isLB D'.P.isLB (Y' := Sp R') (K := PUnit)
    (φ' := fun _ => (D'.c x).left) h (fun _ => sq) (hD.psiW.psi (hD.xe x)) (hD.psiW.psi_gen _)
  refine (psiUnitOn_univ_iff D' x).2 ⟨a, ha, corr_of_val D'.P.isLB fun y J' hJ' => ?_⟩
  obtain ⟨J, hJ⟩ := DegPull.exists_good' D.P.isLB y
  have e₁ := PsiEvenPull.psi_pull hD x (𝟙 _) y hJ hJ'
  have e₂ := va _ (𝟙 _ ≫ jK R') y J J' hJ hJ'
  rw [Fintype.prod_unique, zpow_neg_one, Category.assoc (𝟙 _) (jK R') h, ← hg] at e₂
  have e := e₁.symm.trans e₂
  exact (val_pull hJ' _ _ _).trans (mul_left_cancel e).symm

end GlobalTheory.PullTopUnit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiUnitOnUnivOfPullbackReadTopStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psiUnitOn_univ_of_pullback_read_top : ∀ {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'} (hD : IsPullDeg φ D D'), hD.W = ⊤ → ∀ x : D'.X, PsiUnitOn D' x Set.univ := by
  first | exact @GlobalTheory.PullTopUnit.psiUnitOn_pull_top | exact GlobalTheory.PullTopUnit.psiUnitOn_pull_top | (intros; apply GlobalTheory.PullTopUnit.psiUnitOn_pull_top <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRescaleIsPullDegGeneratingEverywhere
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRescaleIsPullDegGeneratingEverywhere
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PreLiftData

open GlobalTheory.ArcPull GlobalTheory.ArcQ

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

theorem exists_rescale_isPullDeg_data {i : R →+* R'} (D : DegPre R) (D' : DegPre R')
    {W : (Sp R).Opens} (ψW : PsiOn D W) (g : (TK R').left ⟶ (TW W).left) (hg : g ≫ W.ι = jK R' ≫ specOf i)
    {Φ : D'.P.A.left ⟶ D.P.A.left} (gp : IsGrpPullback D'.P.A D.P.A (spMap i) Φ)
    (w : LB.Iso D'.P.L (D.P.L.pull Φ)) (hw : PGen w)
    (hr : PMaps w (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => eSec D.P.A) (fun _ => 1) D'.rig D.rig (spMap i))
    (xe : D'.X ≃+ D.X) (hc : ∀ x, (D'.c x).left ≫ Φ = spMap i ≫ (D.c (xe x)).left) :
    ∃ (κ : D'.X → (FractionRing R')ˣ) (hD : IsPullDeg i D (GlobalTheory.PolDeg.rescale D' κ)),
      (∀ y, hD.xe y = xe y) ∧ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) = Φ ∧ hD.W = W := by
  obtain ⟨e, e_hom, he⟩ := grpPullback_iso gp (isGrpPullback_pullback D.P.A (specOf i))
  subst he
  have hE : eSec D'.P.A ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) = specOf i ≫ eSec D.P.A :=
    (cubeMapOf gp).e_comm
  have hx : ∀ x, g ≫ (toUnit (TW W) ≫ D.c (xe x)).left =
      D'.xK x ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) := fun x => by
    show g ≫ W.ι ≫ (D.c (xe x)).left = (jK R' ≫ (D'.c x).left) ≫ _
    rw [Category.assoc, hc, ← Category.assoc, hg, Category.assoc]
  choose b hb vb using fun x => exists_gen D.P.isLB (K' := PUnit)
    (φ' := fun _ => D'.xK x ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i)) (ε' := fun _ => -1)
    (fun U _ h => Finset.prod_congr rfl fun _ _ => congrArg (fun q => h q ^ (-1 : ℤ)) (hx x))
    (LB.pullGen D.P.L _ _ (ψW.psi (xe x)) g) (DVR.pullGen_isGen _ _ _ _ (ψW.psi_gen _) g)
  choose psi hpsi vpsi using fun x => DegPull.exists_down_val hw D.P.isLB D'.P.isLB (K := PUnit)
    (φ' := fun _ => D'.xK x) (ε := fun _ => -1) (fun _ => rfl) (b x) (hb x)
  choose u hu using GlobalTheory.FieldPull.exists_psi_ratio D' psi hpsi
  refine ⟨fun x => (u x)⁻¹, ?_⟩
  have eψ : ∀ x, psi x = (GlobalTheory.PolDeg.rescale D' fun x => (u x)⁻¹).psi x := fun x =>
    GlobalTheory.TorusExt.gen_ext_val D'.P.isLB (hpsi x) ((GlobalTheory.PolDeg.rescale D' fun x => (u x)⁻¹).psi_gen x)
      fun y J' hJ' => by
        refine Eq.trans ?_ (GlobalTheory.UU.val_scaleGen _ _ _ hJ').symm
        have h1 : unitOn (u x)⁻¹ * unitOn (u x) = 1 := (map_mul _ _ _).symm.trans
          ((congrArg unitOn (inv_mul_cancel (u x))).trans (map_one _))
        rw [hu x y J' hJ', GlobalTheory.TauTwist.unitAt_apply, ← _root_.mul_assoc, ← map_mul]
        erw [h1]
        rw [map_one, _root_.one_mul]
  have key : ∀ x, GeneratorPullback.MapsAt D.P.L D'.P.L (J := PUnit)
      (fun _ => e.hom.left ≫ pullback.fst D.P.A.hom (specOf i)) w (D'.xK x) (-1) (psi x) (b x) := fun x jN jL => by
    refine unit_ext fun y hy => ?_
    have v := vpsi x _ (𝟙 _) y jN (fun _ => jL) (GeneratorPullback.mapsAt_le_b _ _ _ _ jN jL hy) (GeneratorPullback.mapsAt_le_a _ _ _ _ jN jL hy)
    refine (gm_res _ y _ hy _).trans (v.trans (Eq.symm ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_
      (gm_res _ y _ hy _)))))
    rw [pw, Fintype.prod_unique]
    exact (map_zpow _ _ _).trans (congrArg (· ^ (-1 : ℤ)) (gm_pull (𝟙 _) _ y _ hy _))
  refine ⟨⟨e, e_hom, w, (isGen_iff w).2 hw, hE, ?_, xe, hc, W, ψW, g, hg, fun x => ⟨b x, eψ x ▸ key x,
      corr_of_val D.P.isLB fun y J hJ => vb x _ _ y J hJ⟩⟩, fun _ => rfl, rfl, rfl⟩
  exact (maps_iff w _ (fun _ => eSec D.P.A) _ D'.rig D.rig (specOf i) _
    (rigPull_le (G' := D'.P.A) (G := D.P.A) _ (specOf i) hE D.P.L) (fun _ => rfl)).2 hr

theorem exists_rescale_isPullDeg_top : ∀ {W V : Type} [CommRing W] [IsDomain W] [CommRing V] [IsDomain V] (θ₀ : W →+* V) (D₀ : DegPre W) (Q : DegPre V) (e : Q.X ≃+ D₀.X) (β : Q.P.A.left ⟶ D₀.P.A.left), (∀ y, PsiUnitOn D₀ y Set.univ) → IsGrpPullback Q.P.A D₀.P.A (spMap θ₀) β → LBIso Q.P.L (D₀.P.L.pull β) → (∀ y, (Q.c y).left ≫ β = spMap θ₀ ≫ (D₀.c (e y)).left) → ∃ (g : Q.X → (FractionRing V)ˣ) (hD : IsPullDeg θ₀ D₀ (GlobalTheory.PolDeg.rescale Q g)), (∀ y, hD.xe y = e y) ∧ hD.e.hom.left ≫ pullback.fst D₀.P.A.hom (specOf θ₀) = β ∧ hD.W = ⊤ := by
  intro _ _ _ _ _ _ θ₀ D₀ Q e β hU gp hL hc
  obtain ⟨ψW⟩ := GlobalTheory.ArcPull.nonempty_psiOn_top D₀ hU
  let gg : (TK _).left ⟶ (TW (⊤ : (Sp _).Opens)).left := (jK _ ≫ specOf θ₀) ≫ (Sp _).topIso.inv
  have hg : gg ≫ (⊤ : (Sp _).Opens).ι = jK _ ≫ specOf θ₀ := by
    rw [Category.assoc, ← Scheme.topIso_hom, Iso.inv_hom_id, Category.comp_id]
  obtain ⟨w₀, hw₀⟩ := hL
  have he : eSec Q.P.A ≫ β = spMap θ₀ ≫ eSec D₀.P.A := (cubeMapOf gp).e_comm
  have hσ : eSec Q.P.A ≫ Q.P.A.hom = 𝟙 _ := Over.w η[Q.P.A]
  obtain ⟨w, hw, hr⟩ := GlobalTheory.UnifPreCompare.exists_rigidified D₀.P.isLB Q.P.isLB Q.P.A.hom (eSec Q.P.A) hσ w₀ hw₀
    Q.rig Q.rig_gen (φ := eSec D₀.P.A) D₀.rig D₀.rig_gen (spMap θ₀) he
  exact exists_rescale_isPullDeg_data (i := θ₀) D₀ Q ψW gg hg gp w ((isGen_iff w).1 hw) hr e hc

end GlobalTheory.PreLiftData
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRescaleIsPullDegGeneratingEverywhereStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rescale_isPullDeg_generating_everywhere : ∀ {W V : Type} [CommRing W] [IsDomain W] [CommRing V] [IsDomain V] (θ₀ : W →+* V) (D₀ : DegPre W) (Q : DegPre V) (e : Q.X ≃+ D₀.X) (β : Q.P.A.left ⟶ D₀.P.A.left), (∀ y, PsiUnitOn D₀ y Set.univ) → IsGrpPullback Q.P.A D₀.P.A (spMap θ₀) β → LBIso Q.P.L (D₀.P.L.pull β) → (∀ y, (Q.c y).left ≫ β = spMap θ₀ ≫ (D₀.c (e y)).left) → ∃ (g : Q.X → (FractionRing V)ˣ) (hD : IsPullDeg θ₀ D₀ (GlobalTheory.PolDeg.rescale Q g)), (∀ y, hD.xe y = e y) ∧ hD.e.hom.left ≫ pullback.fst D₀.P.A.hom (specOf θ₀) = β ∧ hD.W = ⊤ := by
  first | exact @GlobalTheory.PreLiftData.exists_rescale_isPullDeg_top | exact GlobalTheory.PreLiftData.exists_rescale_isPullDeg_top | (intros; apply GlobalTheory.PreLiftData.exists_rescale_isPullDeg_top <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullDegKeepsBimultActionPolarisationElement
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullDegKeepsBimultActionPolarisationElement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem tauBimult_and_exists_oAct_of_pullDeg : ∀ {O : Type} [CommRing O] [StarRing O] {W V : Type} [CommRing W] [IsDomain W] [CommRing V] [IsDomain V] {θ₀ : W →+* V} {D₀ : DegPre W} [Module O D₀.X] (o₀ : D₀.OAct O) {D : DegPre V} [Module O D.X] (hD : IsPullDeg θ₀ D₀ D) (ob : D.P.OAct O), (∀ (a : O) y, hD.xe (a • y) = a • hD.xe y) → (∀ (a : O) y, D.c (a • y) = D.c y ≫ ob.act a) → (∀ a : O, (ob.act a).left ≫ hD.e.hom.left ≫ pullback.fst D₀.P.A.hom (specOf θ₀) = (hD.e.hom.left ≫ pullback.fst D₀.P.A.hom (specOf θ₀)) ≫ (o₀.onB.act a).left) → D₀.TauBimult → ∀ w0 : O, TraceFormTwistIso D₀ o₀ w0 → D.TauBimult ∧ ∃ o : D.OAct O, o.onB = ob ∧ TraceFormTwistIso D o w0 := by
  intro O _ _ W V _ _ _ _ θ₀ D₀ _ o₀ D _ hD ob hx hcl hact hB w0 hP
  have hG : GlobalFnsSt := GlobalTheory.allSixLaws.1.globalFns
  have hc : ∀ a : O, ob.act a ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf θ₀)).map (o₀.onB.act a) := by
    intro a
    have a₂ : ((Over.pullback (specOf θ₀)).map (o₀.onB.act a)).left ≫ pullback.fst D₀.P.A.hom (specOf θ₀) =
        pullback.fst _ _ ≫ (o₀.onB.act a).left := pullback.lift_fst _ _ _
    refine Over.OverMorphism.ext (pullback.hom_ext ?_ ?_)
    · have h := hact a
      simp only [Over.comp_left, Category.assoc] at h ⊢
      exact h.trans (congrArg (fun q => hD.e.hom.left ≫ q) a₂.symm)
    · exact (Over.w (ob.act a ≫ hD.e.hom)).trans
        (Over.w (hD.e.hom ≫ (Over.pullback (specOf θ₀)).map (o₀.onB.act a))).symm
  let o : D.OAct O := ⟨ob, hcl, fun a =>
    GlobalTheory.tauBal_of_isPullDeg hG _ _ θ₀ D₀ D hD (o₀.onB.act a) (o₀.onB.act (star a)) (ob.act a) (ob.act (star a))
      (o₀.onB.hom _) (o₀.onB.hom _) (o₀.onB.rosati a) (hc a) (hc (star a)) (fun y => a • y) (fun y => star a • y)
      (fun y => a • y) (fun y => star a • y) (hx a) (hx (star a)) (o₀.c_lin a) (o₀.c_lin (star a)) (o₀.tau_bal a)⟩
  exact ⟨GlobalTheory.TauPull.tauBimult_pull hG hD hB, o, rfl,
    GlobalTheory.traceFormTwistIso_of_overPullback _ _ θ₀ D₀ D hD O o₀ o hx hc w0 hP⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullDegKeepsBimultActionPolarisationElementStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullDeg_keeps_bimult_action_polarisationElement : ∀ {O : Type} [CommRing O] [StarRing O] {W V : Type} [CommRing W] [IsDomain W] [CommRing V] [IsDomain V] {θ₀ : W →+* V} {D₀ : DegPre W} [Module O D₀.X] (o₀ : D₀.OAct O) {D : DegPre V} [Module O D.X] (hD : IsPullDeg θ₀ D₀ D) (ob : D.P.OAct O), (∀ (a : O) y, hD.xe (a • y) = a • hD.xe y) → (∀ (a : O) y, D.c (a • y) = D.c y ≫ ob.act a) → (∀ a : O, (ob.act a).left ≫ hD.e.hom.left ≫ pullback.fst D₀.P.A.hom (specOf θ₀) = (hD.e.hom.left ≫ pullback.fst D₀.P.A.hom (specOf θ₀)) ≫ (o₀.onB.act a).left) → D₀.TauBimult → ∀ w0 : O, TraceFormTwistIso D₀ o₀ w0 → D.TauBimult ∧ ∃ o : D.OAct O, o.onB = ob ∧ TraceFormTwistIso D o w0 := by
  first | exact @GlobalTheory.tauBimult_and_exists_oAct_of_pullDeg | exact GlobalTheory.tauBimult_and_exists_oAct_of_pullDeg | (intros; apply GlobalTheory.tauBimult_and_exists_oAct_of_pullDeg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RescaledDegenerationDataDifferByScalar
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalarOfLaws
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.RescaleForm

open GlobalTheory.TauTwist (unitAt unitAt_injective IsScalarForm)

theorem scalar_of_laws {R : Type} [CommRing R] [IsDomain R] {O : Type} [CommRing O] [StarRing O] (D : DegPre R)
    [inst : Module O D.X] (oa : D.OAct O) (w0 : O) (g : D.X → (FractionRing R)ˣ) (hB : D.TauBimult) (hW : TraceFormTwistIso D oa w0)
    (hB' : (GlobalTheory.PolDeg.rescale D g).TauBimult)
    (oa' : @DegPre.OAct R _ _ O _ _ (GlobalTheory.PolDeg.rescale D g) inst)
    (ho : @DegPre.OAct.onB R _ _ O _ _ (GlobalTheory.PolDeg.rescale D g) inst oa' = oa.onB)
    (hW' : @TraceFormTwistIso R _ _ O _ _ (GlobalTheory.PolDeg.rescale D g) inst oa' w0) :
    IsScalarForm O (fun a b => g (a + b) * (g a)⁻¹ * (g b)⁻¹) ∧
      ∀ y, g y = g (y + w0 • y) * (g y)⁻¹ * (g (w0 • y))⁻¹ := by
  letI : Module O (GlobalTheory.PolDeg.rescale D g).X := inst
  have hG := GlobalTheory.globalFns_holds
  let y : (TK R).left := IsLocalRing.closedPoint (FractionRing R)
  obtain ⟨I, hJ⟩ := GlobalTheory.DegPull.exists_good' D.P.isLB y
  have vt : ∀ a b, val ((GlobalTheory.PolDeg.rescale D g).tau a b) (𝟙 _) y I =
      unitAt (𝟙 (TK R).left) y (g (a + b) * (g a)⁻¹ * (g b)⁻¹) * val (D.tau a b) (𝟙 _) y I := fun a b => by
    rw [map_mul, map_mul, map_inv, map_inv]
    exact GlobalTheory.PolDeg.rescale_tau_val D g a b hJ
  have sy : ∀ a b, g (a + b) * (g a)⁻¹ * (g b)⁻¹ = g (b + a) * (g b)⁻¹ * (g a)⁻¹ := fun a b => by
    rw [add_comm, mul_right_comm]
  have al : ∀ a a' b, g (a + a' + b) * (g (a + a'))⁻¹ * (g b)⁻¹ =
      (g (a + b) * (g a)⁻¹ * (g b)⁻¹) * (g (a' + b) * (g a')⁻¹ * (g b)⁻¹) := fun a a' b => by
    have e := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (hB a a' b) (𝟙 _)).trans (val_mul hJ _ _ _))
    have e' := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (hB' a a' b) (𝟙 _)).trans (val_mul hJ _ _ _))
    have e'' := (congrArg₂ (· * ·) (vt (a + a') b).symm rfl).trans (e'.trans (congrArg₂ (· * ·) (vt a b) (vt a' b)))
    rw [_root_.mul_mul_mul_comm, ← e, _root_.mul_assoc, ← map_mul] at e''
    exact unitAt_injective y (mul_right_cancel e'')
  obtain ⟨onB', cl', tb'⟩ := oa'
  obtain rfl : onB' = oa.onB := ho
  refine ⟨⟨fun a b b' => ?_, sy, fun x a b => ?_⟩, fun a => ?_⟩
  · rw [sy, sy a b, sy a b']
    exact al b b' a
  · have hr := GlobalTheory.TorusExt.exists_isRos hG oa (star x)
    rw [star_star] at hr
    obtain ⟨u, hu, u₀⟩ := hr
    have e := (val_mul hJ _ _ _).symm.trans (val_corr hJ (oa.tau_bal x u hu u₀ a b) (𝟙 _))
    have e' := (val_mul hJ _ _ _).symm.trans (val_corr hJ (tb' x u hu u₀ a b) (𝟙 _))
    have e'' := (congrArg₂ (· * ·) (vt (x • a) b).symm rfl).trans (e'.trans (vt a (star x • b)))
    rw [← e, _root_.mul_assoc] at e''
    exact unitAt_injective y (mul_right_cancel e'')
  · obtain ⟨u, hu, u₀, h⟩ := hW
    obtain ⟨u', hu', u₀', h'⟩ := hW'
    have k := gen_unique' D.P.isLB (fun _ _ _ => rfl) D.P.A.hom (eSec D.P.A) (Over.w η[D.P.A]) (hG _ _ D.P.isAb).2 hu hu'
      (fun z J hz => by
        have a := val_corr hz u₀ (𝟙 _)
        have b := val_corr hz u₀' (𝟙 _)
        rw [val_pull hz, val_one, Category.id_comp] at a
        have b' := ((val_pull hz _ _ _).symm.trans b).trans (val_one _)
        rw [Category.id_comp] at b'
        exact a.trans b'.symm) _ (𝟙 _ ≫ D.xK a) y I hJ
    have e := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (h a) (𝟙 _)).trans (val_mul hJ _ _ _))
    have e' := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (h' a) (𝟙 _)).trans (val_mul hJ _ _ _))
    rw [val_pull hJ] at e
    have e'' := (congrArg₂ (· * ·) (vt a (w0 • a)).symm (k.trans (val_pull hJ _ _ _).symm)).trans (e'.trans
      (congrArg₂ (· * ·) (GlobalTheory.UU.val_scaleGen (unitOn (g a)) (D.psi a) (𝟙 _) hJ) rfl))
    rw [_root_.mul_assoc, e] at e''
    exact (unitAt_injective y (mul_right_cancel (e''.trans (_root_.mul_assoc _ _ _)))).symm

theorem main : ∀ {R : Type} [CommRing R] [IsDomain R] {O : Type} [CommRing O] [StarRing O] (D : DegPre R) [inst : Module O D.X] (oa : D.OAct O) (w0 : O) (g : D.X → (FractionRing R)ˣ), D.TauBimult → TraceFormTwistIso D oa w0 → (GlobalTheory.PolDeg.rescale D g).TauBimult → ∀ (oa' : @DegPre.OAct R _ _ O _ _ (GlobalTheory.PolDeg.rescale D g) inst), @DegPre.OAct.onB R _ _ O _ _ (GlobalTheory.PolDeg.rescale D g) inst oa' = oa.onB → @TraceFormTwistIso R _ _ O _ _ (GlobalTheory.PolDeg.rescale D g) inst oa' w0 → GlobalTheory.TauTwist.IsScalarForm O (fun a b => g (a + b) * (g a)⁻¹ * (g b)⁻¹) ∧ ∀ y, g y = g (y + w0 • y) * (g y)⁻¹ * (g (w0 • y))⁻¹ :=
  fun D _ oa w0 g a b c oa' d e => scalar_of_laws D oa w0 g a b c oa' d e

end GlobalTheory.RescaleForm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RescaledDegenerationDataDifferByScalar
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.RatioScalar

theorem scalar : ∀ {O : Type} [CommRing O] [StarRing O] {V : Type} [CommRing V] [IsDomain V] (Q : DegPre V) [Module O Q.X] (oQ : Q.OAct O) (g : Q.X → (FractionRing V)ˣ) (o' : letI : Module O (GlobalTheory.PolDeg.rescale Q g).X := ‹Module O Q.X›; (GlobalTheory.PolDeg.rescale Q g).OAct O), (letI : Module O (GlobalTheory.PolDeg.rescale Q g).X := ‹Module O Q.X›; o'.onB = oQ.onB) → Q.TauBimult → (GlobalTheory.PolDeg.rescale Q g).TauBimult → ∀ w0 : O, TraceFormTwistIso Q oQ w0 → (letI : Module O (GlobalTheory.PolDeg.rescale Q g).X := ‹Module O Q.X›; TraceFormTwistIso (GlobalTheory.PolDeg.rescale Q g) o' w0) → ∃ q : Q.X → Q.X → (FractionRing V)ˣ, (∀ a b, q a b = q b a) ∧ (∀ a a' b, q (a + a') b = q a b * q a' b) ∧ (∀ (x : O) a b, q (x • a) b = q a (star x • b)) ∧ ∀ y, (g y)⁻¹ = q y (w0 • y) := by
  intro O _ _ V _ _ Q _ oQ g o' ho hB hB' w0 hW hW'
  obtain ⟨hs, hd⟩ := GlobalTheory.RescaleForm.main Q oQ w0 g hB hW hB' o' ho hW'
  exact ⟨fun a b => (g (a + b) * (g a)⁻¹ * (g b)⁻¹)⁻¹, hs.inv.symm, hs.inv.add_left, hs.inv.bal,
    fun y => congrArg (·⁻¹) (hd y)⟩

end GlobalTheory.RatioScalar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RescaledDegenerationDataDifferByScalarStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rescaled_degenerationData_differ_by_scalar : ∀ {O : Type} [CommRing O] [StarRing O] {V : Type} [CommRing V] [IsDomain V] (Q : DegPre V) [Module O Q.X] (oQ : Q.OAct O) (g : Q.X → (FractionRing V)ˣ) (o' : letI : Module O (GlobalTheory.PolDeg.rescale Q g).X := ‹Module O Q.X›; (GlobalTheory.PolDeg.rescale Q g).OAct O), (letI : Module O (GlobalTheory.PolDeg.rescale Q g).X := ‹Module O Q.X›; o'.onB = oQ.onB) → Q.TauBimult → (GlobalTheory.PolDeg.rescale Q g).TauBimult → ∀ w0 : O, TraceFormTwistIso Q oQ w0 → (letI : Module O (GlobalTheory.PolDeg.rescale Q g).X := ‹Module O Q.X›; TraceFormTwistIso (GlobalTheory.PolDeg.rescale Q g) o' w0) → ∃ q : Q.X → Q.X → (FractionRing V)ˣ, (∀ a b, q a b = q b a) ∧ (∀ a a' b, q (a + a') b = q a b * q a' b) ∧ (∀ (x : O) a b, q (x • a) b = q a (star x • b)) ∧ ∀ y, (g y)⁻¹ = q y (w0 • y) := by
  first | exact @GlobalTheory.RatioScalar.scalar | exact GlobalTheory.RatioScalar.scalar | (intros; apply GlobalTheory.RatioScalar.scalar <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegDataDifferBySymmBalancedFormOfPsiTau
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.YRatio

theorem main : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {W V : Type} [CommRing W] [IsDomain W] [IsLocalRing W] [CommRing V] [IsDomain V] [IsLocalRing V] (θ₀ : W →+* V) (D₀ : DegPre W) [Module (𝓞 E) D₀.X] (o₀ : letI := H.starRing; D₀.OAct (𝓞 E)) (Q : DegPre V) [Module (𝓞 E) Q.X] (oQ : letI := H.starRing; Q.OAct (𝓞 E)) (e : Q.X ≃ₗ[𝓞 E] D₀.X) (β : Q.P.A.left ⟶ D₀.P.A.left), D₀.TauBimult → (∀ y, PsiUnitOn D₀ y Set.univ) → (letI := H.starRing; TraceFormTwistIso D₀ o₀ H.w0) → Q.TauBimult → (letI := H.starRing; TraceFormTwistIso Q oQ H.w0) → IsGrpPullback Q.P.A D₀.P.A (spMap θ₀) β → (letI := H.starRing; ∀ a : 𝓞 E, (oQ.onB.act a).left ≫ β = β ≫ (o₀.onB.act a).left) → LBIso Q.P.L (D₀.P.L.pull β) → (∀ y, (Q.c y).left ≫ β = spMap θ₀ ≫ (D₀.c (e y)).left) → ∃ (g : Q.X → (FractionRing V)ˣ) (hD : IsPullDeg θ₀ D₀ (GlobalTheory.PolDeg.rescale Q g)) (q : Q.X → Q.X → (FractionRing V)ˣ), (∀ y : Q.X, hD.xe y = e y) ∧ hD.e.hom.left ≫ pullback.fst D₀.P.A.hom (specOf θ₀) = β ∧ (∀ y, PsiUnitOn (GlobalTheory.PolDeg.rescale Q g) y Set.univ) ∧ (∀ a b, q a b = q b a) ∧ (∀ a a' b, q (a + a') b = q a b * q a' b) ∧ (∀ (x : 𝓞 E) a b, q (x • a) b = q a (H.bar x • b)) ∧ ∀ y, (g y)⁻¹ = q y (H.w0 • y) := by
  intro E _ _ _ H W V _ _ _ _ _ _ θ₀ D₀ _ o₀ Q _ oQ e β hB₀ hU hW₀ hBQ hWQ gp hact hL hc
  letI := H.starRing
  obtain ⟨g, hD, hxe, hβ, hWt⟩ := GlobalTheory.T.exists_rescale_isPullDeg_generating_everywhere θ₀ D₀ Q e.toAddEquiv β hU gp hL hc
  letI : Module (𝓞 E) (GlobalTheory.PolDeg.rescale Q g).X := ‹Module (𝓞 E) Q.X›
  obtain ⟨hB', o', ho', hW'⟩ := GlobalTheory.T.pullDeg_keeps_bimult_action_polarisationElement o₀ hD oQ.onB
    (fun a y => by rw [hxe, hxe]; exact e.map_smul a y) oQ.c_lin
    (fun a => by rw [hβ]; exact hact a) hB₀ H.w0 hW₀
  obtain ⟨q, h1, h2, h3, h4⟩ := GlobalTheory.T.rescaled_degenerationData_differ_by_scalar Q oQ g o' ho' hBQ hB' H.w0 hWQ hW'
  exact ⟨g, hD, q, hxe, hβ, GlobalTheory.T.psiUnitOn_univ_of_pullback_read_top hD hWt, h1, h2, h3, h4⟩

end GlobalTheory.YRatio
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegDataDifferBySymmBalancedFormOfPsiTauStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degData_differ_by_symmBalancedForm_of_psi_tau : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {W V : Type} [CommRing W] [IsDomain W] [IsLocalRing W] [CommRing V] [IsDomain V] [IsLocalRing V] (θ₀ : W →+* V) (D₀ : DegPre W) [Module (𝓞 E) D₀.X] (o₀ : letI := H.starRing; D₀.OAct (𝓞 E)) (Q : DegPre V) [Module (𝓞 E) Q.X] (oQ : letI := H.starRing; Q.OAct (𝓞 E)) (e : Q.X ≃ₗ[𝓞 E] D₀.X) (β : Q.P.A.left ⟶ D₀.P.A.left), D₀.TauBimult → (∀ y, PsiUnitOn D₀ y Set.univ) → (letI := H.starRing; TraceFormTwistIso D₀ o₀ H.w0) → Q.TauBimult → (letI := H.starRing; TraceFormTwistIso Q oQ H.w0) → IsGrpPullback Q.P.A D₀.P.A (spMap θ₀) β → (letI := H.starRing; ∀ a : 𝓞 E, (oQ.onB.act a).left ≫ β = β ≫ (o₀.onB.act a).left) → LBIso Q.P.L (D₀.P.L.pull β) → (∀ y, (Q.c y).left ≫ β = spMap θ₀ ≫ (D₀.c (e y)).left) → ∃ (g : Q.X → (FractionRing V)ˣ) (hD : IsPullDeg θ₀ D₀ (GlobalTheory.PolDeg.rescale Q g)) (q : Q.X → Q.X → (FractionRing V)ˣ), (∀ y : Q.X, hD.xe y = e y) ∧ hD.e.hom.left ≫ pullback.fst D₀.P.A.hom (specOf θ₀) = β ∧ (∀ y, PsiUnitOn (GlobalTheory.PolDeg.rescale Q g) y Set.univ) ∧ (∀ a b, q a b = q b a) ∧ (∀ a a' b, q (a + a') b = q a b * q a' b) ∧ (∀ (x : 𝓞 E) a b, q (x • a) b = q a (H.bar x • b)) ∧ ∀ y, (g y)⁻¹ = q y (H.w0 • y) := by
  first | exact @GlobalTheory.YRatio.main | exact GlobalTheory.YRatio.main | (intros; apply GlobalTheory.YRatio.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitCoordsBalancedSymmetricRoots
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitCoordsBalancedSymmetricRoots
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UnitForm

theorem exists_coords {O : Type} [CommRing O] [StarRing O] [IsDedekindDomain O]
    [Module.Finite ℤ O] [Module.Free ℤ O] {w : O} (hw : w + star w = 1)
    {X : Type} [AddCommGroup X] [Module O X] [Module.Finite ℤ X] [Module.Free ℤ X]
    {J : Type} [Fintype J] (ε : Module.Basis J ℤ (PolFan.balForms (star : O → O) X))
    {B : Type} [AddCommGroup B] (τ : Forms.balForms ℤ O X B) :
    ∃ c : J → B, ∀ a b, (τ : Forms.Bil X B) a b = ∑ k, (ε k : LinearMap.BilinForm ℤ X) a b • c k := by
  classical
  have := Forms.projective_of_int O X
  have := Forms.finite_balTensor (O := O) (X := X)
  have := Forms.free_balTensor (X := X) hw
  let e := Module.Free.chooseBasis ℤ ((TensorProduct ℤ X X) ⧸ Forms.balTensorRel (O := O) (X := X))
  have hm := Forms.balTensorMk_mem_balForms O X
  let β : _ → PolFan.balForms (star : O → O) X := fun j =>
    ⟨(Forms.balTensorMk O).compr₂ (e.coord j),
      fun y x => congrArg (e.coord j) (hm.1 y x), fun a y x => congrArg (e.coord j) (hm.2 a y x)⟩
  refine ⟨fun k => ∑ j, ε.repr (β j) k • Forms.balTensorLift τ (e j), fun a b => ?_⟩
  have h1 (j) : e.repr (Forms.balTensorMk O a b) j =
      ∑ k, ε.repr (β j) k * (ε k : LinearMap.BilinForm ℤ X) a b := by
    have h := congrArg (fun g : PolFan.balForms (star : O → O) X =>
      (g : LinearMap.BilinForm ℤ X) a b) (ε.sum_repr (β j))
    simp only [Submodule.coe_sum, Submodule.coe_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul] at h
    exact h.symm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← Forms.balTensorLift_mk, ← e.sum_repr (Forms.balTensorMk O a b), map_sum]
  simp only [map_zsmul]
  simp only [h1, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [_root_.mul_comm]

theorem exists_root {V : Type} [CommRing V] [IsLocalRing V] [IsAdicComplete (maximalIdeal V) V]
    [IsAlgClosed (ResidueField V)] {n : ℕ} (hn : IsUnit (n : V)) (u : Vˣ) :
    ∃ v : Vˣ, v ^ n = u := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hn
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (residue V u) (Nat.pos_of_ne_zero hn0)
  obtain ⟨a, rfl⟩ := residue_surjective z
  have ha : IsUnit a := by
    rw [← residue_ne_zero_iff_isUnit]
    intro h
    rw [h, zero_pow hn0] at hz
    exact (residue_ne_zero_iff_isUnit _).2 u.isUnit hz.symm
  obtain ⟨y, hy, -⟩ := HenselianRing.is_henselian (R := V) (I := maximalIdeal V)
    (Polynomial.X ^ n - Polynomial.C (u : V)) (Polynomial.monic_X_pow_sub_C _ hn0) a
    (by
      rw [← residue_eq_zero_iff]
      simp [hz])
    (by
      refine IsUnit.map _ ?_
      simpa [Polynomial.derivative_X_pow] using ⟨hn, ha.pow _⟩)
  have hy' : y ^ n = u := by
    simpa [sub_eq_zero] using hy
  have hyu : IsUnit y := (isUnit_pow_iff hn0).1 (hy' ▸ u.isUnit)
  exact ⟨hyu.unit, Units.ext (by simpa using hy')⟩

theorem mem_of_diag {O : Type} [CommRing O] (bar : O → O) {w : O} (hw : w + bar w = 1)
    {X : Type} [AddCommGroup X] [Module O X] {G : Type} [CommGroup G] (U : Subgroup G)
    (q : X → X → G) (hs : ∀ a b, q a b = q b a) (ha : ∀ a a' b, q (a + a') b = q a b * q a' b)
    (hb : ∀ (x : O) a b, q (x • a) b = q a (bar x • b)) (hd : ∀ y, q y (w • y) ∈ U) (a b : X) :
    q a b ∈ U := by
  have hr (a b b') : q a (b + b') = q a b * q a b' := by rw [hs, ha, hs b, hs b']
  have h1 : q a (w • b) * q b (w • a) = q a b := by
    rw [hs b, hb, ← hr, ← add_smul, hw, one_smul]
  have h2 : q a b = q (a + b) (w • (a + b)) / (q a (w • a) * q b (w • b)) := by
    rw [smul_add, ha, hr, hr, ← h1, eq_div_iff_mul_eq']
    simp only [mul_comm, mul_left_comm, mul_assoc]
  rw [h2]
  exact U.div_mem (hd _) (U.mul_mem (hd _) (hd _))

theorem exists_unit_coords : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X] (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsAdicComplete (maximalIdeal V) V → IsAlgClosed (ResidueField V) → ∀ n : ℕ, IsUnit (n : V) → ∀ (m N : ℕ) (ε : Module.Basis (Fin m ⊕ Fin N) ℤ (balForms H.bar X)) (t : Fin m → V), (∀ i, t i ≠ 0) → ∀ q : X → X → (FractionRing V)ˣ, (∀ a b, q a b = q b a) → (∀ a a' b, q (a + a') b = q a b * q a' b) → (∀ (x : 𝓞 E) a b, q (x • a) b = q a (H.bar x • b)) → (∀ y, ∃ u : Vˣ, (q y (H.w0 • y) : FractionRing V) = algebraMap V _ u * ∏ i, algebraMap V (FractionRing V) (t i) ^ ((n : ℤ) * (ε (.inl i) : LinearMap.BilinForm ℤ X) y (H.w0 • y))) → ∃ s : Fin m ⊕ Fin N → V, (∀ i, Associated (s (.inl i)) (t i)) ∧ (∀ j, IsUnit (s (.inr j))) ∧ ∀ a b, (q a b : FractionRing V) = ∏ k, algebraMap V (FractionRing V) (s k) ^ ((n : ℤ) * (ε k : LinearMap.BilinForm ℤ X) a b) := by
  intro E _ _ _ H X _ _ _ _ V _ _ _ hV hk n hn m N ε t ht q hs ha hb hd
  letI : StarRing (𝓞 E) :=
    { star := H.bar
      star_involutive := fun a => by
        apply Subtype.ext
        change ((H.bar (H.bar a) : 𝓞 E) : E) = a
        rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]
      star_mul := fun a b => by rw [map_mul, _root_.mul_comm]
      star_add := fun a b => map_add H.bar a b }
  have hw : H.w0 + H.bar H.w0 = 1 := PullbackSections.CVA.cmHostUnit_add_conj_eq_one H
  have hinj : Function.Injective (algebraMap V (FractionRing V)) := IsFractionRing.injective _ _
  let φ : Vˣ →* (FractionRing V)ˣ := Units.map (algebraMap V (FractionRing V) : V →* FractionRing V)
  have hφ : Function.Injective φ := Units.map_injective hinj
  let τ : Fin m → (FractionRing V)ˣ := fun i =>
    Units.mk0 (algebraMap V (FractionRing V) (t i)) (fun h => ht i (hinj (by rw [h, map_zero])))
  let M : X → X → (FractionRing V)ˣ := fun a b =>
    ∏ i, τ i ^ ((n : ℤ) * (ε (.inl i) : LinearMap.BilinForm ℤ X) a b)
  have Ms (a b) : M a b = M b a := Finset.prod_congr rfl fun i _ => by rw [(ε (.inl i)).2.1 a b]
  have Ma (a a' b) : M (a + a') b = M a b * M a' b := by
    simp only [M, map_add (f := _), LinearMap.add_apply, mul_add, zpow_add, Finset.prod_mul_distrib]
  have Mb (x : 𝓞 E) (a b) : M (x • a) b = M a (H.bar x • b) :=
    Finset.prod_congr rfl fun i _ => by rw [(ε (.inl i)).2.2 x a b]
  have hmem := mem_of_diag H.bar hw φ.range (fun a b => q a b / M a b)
    (fun a b => by rw [hs, Ms]) (fun a a' b => by rw [ha, Ma, mul_div_mul_comm])
    (fun x a b => by rw [hb, Mb]) (fun y => by
      obtain ⟨u, hu⟩ := hd y
      refine ⟨u, ?_⟩
      rw [eq_div_iff_mul_eq']
      apply Units.ext
      rw [hu]
      simp [M, τ, φ])
  choose u hu using hmem
  have us (a b) : u a b = u b a := hφ (by rw [hu, hu, hs, Ms])
  have ua (a a' b) : u (a + a') b = u a b * u a' b :=
    hφ (by rw [map_mul, hu, hu, hu, ha, Ma, mul_div_mul_comm])
  have ub (x : 𝓞 E) (a b) : u (x • a) b = u a (H.bar x • b) := hφ (by rw [hu, hu, hb, Mb])
  have ur (a b b') : u a (b + b') = u a b * u a b' := by rw [us, ua, us b, us b']
  obtain ⟨c, hc⟩ := exists_coords (O := 𝓞 E) hw ε ⟨Forms.bilOfMul u ua ur, us, ub⟩
  choose v hv using fun k => exists_root hn (c k).toMul
  refine ⟨Sum.elim (fun i => t i * v (.inl i)) (fun j => v (.inr j)),
    fun i => ⟨(v (.inl i))⁻¹, by simp⟩, fun j => Units.isUnit _, fun a b => ?_⟩
  have h1 : u a b = ∏ k, v k ^ ((n : ℤ) * (ε k : LinearMap.BilinForm ℤ X) a b) := by
    have h := congrArg Additive.toMul (hc a b)
    simp only [toMul_sum, toMul_zsmul, ← hv] at h
    simp only [zpow_mul, zpow_natCast]
    exact h
  have h2 : q a b = M a b * φ (u a b) := by rw [hu, mul_div_cancel]
  rw [h2, h1]
  simp [M, τ, φ, Fintype.prod_sum_type, mul_zpow, Finset.prod_mul_distrib, _root_.mul_assoc]

end GlobalTheory.UnitForm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitCoordsBalancedSymmetricRootsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_coords_balancedSymmetric_roots : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X] (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsAdicComplete (maximalIdeal V) V → IsAlgClosed (ResidueField V) → ∀ n : ℕ, IsUnit (n : V) → ∀ (m N : ℕ) (ε : Module.Basis (Fin m ⊕ Fin N) ℤ (balForms H.bar X)) (t : Fin m → V), (∀ i, t i ≠ 0) → ∀ q : X → X → (FractionRing V)ˣ, (∀ a b, q a b = q b a) → (∀ a a' b, q (a + a') b = q a b * q a' b) → (∀ (x : 𝓞 E) a b, q (x • a) b = q a (H.bar x • b)) → (∀ y, ∃ u : Vˣ, (q y (H.w0 • y) : FractionRing V) = algebraMap V _ u * ∏ i, algebraMap V (FractionRing V) (t i) ^ ((n : ℤ) * (ε (.inl i) : LinearMap.BilinForm ℤ X) y (H.w0 • y))) → ∃ s : Fin m ⊕ Fin N → V, (∀ i, Associated (s (.inl i)) (t i)) ∧ (∀ j, IsUnit (s (.inr j))) ∧ ∀ a b, (q a b : FractionRing V) = ∏ k, algebraMap V (FractionRing V) (s k) ^ ((n : ℤ) * (ε k : LinearMap.BilinForm ℤ X) a b) := by
  first | exact @GlobalTheory.UnitForm.exists_unit_coords | exact GlobalTheory.UnitForm.exists_unit_coords | (intros; apply GlobalTheory.UnitForm.exists_unit_coords <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPeriodsMonomialFamilyCoordsOverBase
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UCanon.Periods

theorem inv_eq_unit_mul {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R)
    (g : D.X → (FractionRing R)ˣ) {y : D.X} {r : R} (hr : Formalism.L2.Pj.PsiCoord D y r)
    (hU : PsiUnitOn (GlobalTheory.PolDeg.rescale D g) y Set.univ) :
    ∃ u : Rˣ, (((g y)⁻¹ : (FractionRing R)ˣ) : FractionRing R) = algebraMap R _ u * algebraMap R _ r := by
  have hex : ∃ v : Rˣ, Formalism.L2.Pj.PsiCoord (GlobalTheory.TauTwist.rescale D g) y v := by
    let D' := GlobalTheory.TauTwist.rescale D g
    obtain ⟨j, hj⟩ := GlobalTheory.PsiCoordLocal.exists_chart_top D' y
    have hh := GlobalTheory.PsiCoordLocal.generic_le D' y j hj
    obtain ⟨s, hs, e⟩ := hU j ⊤ (isAffineOpen_top _) (Set.subset_univ _) hj hh
    obtain ⟨r, rfl⟩ := GlobalTheory.PsiCoordLocal.toOpen_top_bijective.2 s
    have hu : IsUnit r := (MulEquiv.isUnit_map
      (RingEquiv.ofBijective (Out.DegPre.toOpen (R := R) ⊤) GlobalTheory.PsiCoordLocal.toOpen_top_bijective).toMulEquiv).1 hs
    exact ⟨hu.unit, j, hj, hh, e⟩
  obtain ⟨v, hv⟩ := hex
  obtain ⟨x, ⟨j, h, hj, rfl⟩, e⟩ := (GlobalTheory.PeriodFormCompare.psiCoord_iff D y r).1 hr
  obtain ⟨x', hx', e'⟩ := (GlobalTheory.PeriodFormCompare.psiCoord_iff (GlobalTheory.TauTwist.rescale D g) y _).1 hv
  have h₁ : GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsPsiCoord (GlobalTheory.TauTwist.rescale D g) y (g y * GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.genVal (D.psi y) j h) := by
    refine ⟨j, h, hj, ?_⟩
    dsimp only [GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.genVal, GlobalTheory.TauTwist.rescale, GlobalTheory.TauTwist.withPsi, ReciprocityTheory.ChartRestriction.G.DVR.scaleGen]
    rw [map_mul, map_mul, GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.res_res]
    congr 1
    ext
    show (g y : FractionRing R) = (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom
      (((Sp (FractionRing R)).presheaf.map (𝟙 _)).hom
        ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom (g y : FractionRing R)))
    rw [CategoryTheory.Functor.map_id]
    exact ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv_hom_id_apply _).symm
  obtain ⟨u, hu⟩ := h₁.unique hx'
  have k := congrArg Units.val hu
  rw [Units.val_mul, Units.val_mul, e, e'] at k
  have k' : (g y : FractionRing R) * algebraMap R _ r = algebraMap R _ ((u * v : Rˣ) : R) := by
    rw [k, Units.val_mul, map_mul]; rfl
  refine ⟨(u * v)⁻¹, ?_⟩
  refine Units.inv_eq_of_mul_eq_one_right ?_
  rw [mul_left_comm, k', ← map_mul, Units.inv_mul, map_one]

theorem exists_divFrom : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → IsAlgClosed (ResidueField V) → ∀ (C : MonoFam Xo c φ V) (D' : Datum H) (L : LowBase D' c) (θ₀ : L.W →+* V) (e : C.P.D.toPre.X ≃ₗ[𝓞 E] L.D.X) (β : C.P.D.toPre.P.A.left ⟶ L.D.P.A.left), IsGrpPullback C.P.D.toPre.P.A L.D.P.A (spMap θ₀) β → (letI := H.starRing; ∀ a : 𝓞 E, (C.P.oD.onB.act a).left ≫ β = β ≫ (L.oa.onB.act a).left) → LBIso C.P.D.toPre.P.L (L.D.P.L.pull β) → (∀ y, (C.P.D.toPre.c y).left ≫ β = spMap θ₀ ≫ (L.D.c (l.M' • e y)).left) → ∀ (N : ℕ) (ε : Module.Basis (Fin C.m ⊕ Fin N) ℤ (balForms H.bar L.D.X)), (∀ i, C.δ i = pull e.toLinearMap (ε (.inl i) : LinearMap.BilinForm ℤ L.D.X)) → ∃ s : Fin C.m ⊕ Fin N → V, (∀ i, Associated (s (.inl i)) (C.s i)) ∧ (∀ j, IsUnit (s (.inr j))) ∧ DivFrom L C.P.D.toPre C.P.oD θ₀ s (fun k => (ε k : LinearMap.BilinForm ℤ L.D.X)) e := by
  intro E _ _ _ H Dw l Xo c φ V _ _ _ hV hk C D' L θ₀ e β hβ hact hL hc N ε hε
  letI := H.starRing
  obtain ⟨-, hbm, hgen, o₀, ho₀, hw₀⟩ := GlobalTheory.T.degenerationDataNsmulRescale_keeps_laws L.W L.D (𝓞 E) L.oa H.w0 l.M' L.even L.bimult L.w0 L.gen
  letI : Module (𝓞 E) (mulDeg L.D l.M').X := L.mod
  obtain ⟨g, hD, q, hxe, hpr, hU, qs, qa, qb, hg⟩ := GlobalTheory.T.degData_differ_by_symmBalancedForm_of_psi_tau (H := H) θ₀ (mulDeg L.D l.M') o₀ C.P.D.toPre C.P.oD e β
    hbm hgen hw₀ C.P.D.tau_bimult C.P.w0 hβ (fun a => by rw [ho₀]; exact hact a) hL hc
  have hM : IsUnit ((l.M' : ℕ) : V) := by
    have h1 : IsUnit ((l.M' : ℕ) : c.F) := (Nat.cast_ne_zero.2 (level_pos l).ne').isUnit
    simpa using h1.map C.b
  obtain ⟨s, hs₁, hs₂, hs⟩ := GlobalTheory.T.exists_unit_coords_balancedSymmetric_roots H L.D.X V hV.1.2.2.2 hk l.M' hM C.m N ε C.s C.s_ne_zero
    (fun a b => q (e.symm a) (e.symm b)) (fun a b => qs _ _) (fun a a' b => by simp only [map_add (f := _), qa])
    (fun x a b => by simp only [map_smul, qb]) (fun y => by
      obtain ⟨y, rfl⟩ := e.surjective y
      obtain ⟨u, n, hn, hco⟩ := C.mono y
      obtain ⟨v, hv⟩ := inv_eq_unit_mul _ g hco (hU y)
      refine ⟨v * u, ?_⟩
      rw [map_smul, e.symm_apply_apply, ← hg, hv, Units.val_mul, map_mul, map_mul, map_prod, _root_.mul_assoc]
      congr 2
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [map_pow, ← zpow_natCast]
      congr 1
      have h1 := apply_self_eq_two_mul ((balForms_eq_levelForms H L.D.X).le (ε (.inl i)).2) (e y)
      have h2 := hn i
      rw [LinearMap.smul_apply, LinearMap.smul_apply, hε, pull_apply, LinearEquiv.coe_coe, h1, smul_eq_mul] at h2
      linarith)
  refine ⟨s, hs₁, hs₂, g, hD, fun y => ?_, hxe, fun x => ?_⟩
  · rw [hg, ← hs, map_smul, e.symm_apply_apply]
  · have := hact x
    rw [← hpr] at this
    exact this.trans (Category.assoc _ _ _)

end GlobalTheory.UCanon.Periods
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPeriodsMonomialFamilyCoordsOverBaseStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_periods_monomialFamily_coords_over_base : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → IsAlgClosed (ResidueField V) → ∀ (C : MonoFam Xo c φ V) (D' : Datum H) (L : LowBase D' c) (θ₀ : L.W →+* V) (e : C.P.D.toPre.X ≃ₗ[𝓞 E] L.D.X) (β : C.P.D.toPre.P.A.left ⟶ L.D.P.A.left), IsGrpPullback C.P.D.toPre.P.A L.D.P.A (spMap θ₀) β → (letI := H.starRing; ∀ a : 𝓞 E, (C.P.oD.onB.act a).left ≫ β = β ≫ (L.oa.onB.act a).left) → LBIso C.P.D.toPre.P.L (L.D.P.L.pull β) → (∀ y, (C.P.D.toPre.c y).left ≫ β = spMap θ₀ ≫ (L.D.c (l.M' • e y)).left) → ∀ (N : ℕ) (ε : Module.Basis (Fin C.m ⊕ Fin N) ℤ (balForms H.bar L.D.X)), (∀ i, C.δ i = pull e.toLinearMap (ε (.inl i) : LinearMap.BilinForm ℤ L.D.X)) → ∃ s : Fin C.m ⊕ Fin N → V, (∀ i, Associated (s (.inl i)) (C.s i)) ∧ (∀ j, IsUnit (s (.inr j))) ∧ DivFrom L C.P.D.toPre C.P.oD θ₀ s (fun k => (ε k : LinearMap.BilinForm ℤ L.D.X)) e := by
  first | exact @GlobalTheory.UCanon.Periods.exists_divFrom | exact GlobalTheory.UCanon.Periods.exists_divFrom | (intros; apply GlobalTheory.UCanon.Periods.exists_divFrom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeModuleActionHomomorphism
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeModuleActionHomomorphism
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbDivLocal

theorem exists_pow_eq {V : Type} [CommRing V] [IsLocalRing V] [IsNoetherianRing V]
    (hc : IsAdicComplete (maximalIdeal V) V) (hk : IsAlgClosed (ResidueField V))
    (B : Over (Sp V)) [GrpObj B] (hB : IsAbelianScheme B) (n : ℕ) (hn : IsUnit (n : V))
    (P : 𝟙_ (Over (Sp V)) ⟶ B) : ∃ Q : 𝟙_ (Over (Sp V)) ⟶ B, Q ^ n = P := by
  have hn' : IsUnit (n : Γ(Sp V, ⊤)) := by
    simpa using hn.map (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom
  obtain ⟨-, hfin, het, hsurj⟩ :=
    GlobalTheory.abelianScheme_id_pow_finite_etale_surjective (Sp V) B n hB hn'
  set m : B ⟶ B := (𝟙 B) ^ n with hm
  let U : Over (Sp V) := Over.mk (pullback.snd m.left P.left)
  have hU : Smooth U.hom := by dsimp [U]; infer_instance
  let r : Sp (ResidueField V) ⟶ Sp V := spMap (residue V)
  let P₀ : Sp (ResidueField V) ⟶ B.left := r ≫ P.left
  have : CompactSpace ↥(pullback m.left P₀) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd m.left P₀)
  obtain ⟨p, -⟩ := (pullback.snd m.left P₀).surjective (default : PrimeSpectrum (ResidueField V))
  obtain ⟨z, -, hz⟩ :=
    isClosed_univ.exists_closed_singleton (X := ↥(pullback m.left P₀)) ⟨p, trivial⟩
  have hw := pointOfClosedPoint_comp (pullback.snd m.left P₀) z hz
  let x₀ : Sp (ResidueField V) ⟶ U.left :=
    pullback.lift (pointOfClosedPoint (pullback.snd m.left P₀) z hz ≫ pullback.fst _ _) r (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hw, Category.id_comp])
  have hx₀ : x₀ ≫ U.hom = spMap ((residue V).comp (RingHom.id V)) := by
    rw [RingHom.comp_id]
    exact pullback.lift_snd _ _ _
  obtain ⟨a, ha, -⟩ :=
    GlobalTheory.HenselLift.exists_lift_mem_open V V hc (RingHom.id V) U hU x₀ hx₀ ⊤ (by simp)
  have ha' : a ≫ pullback.snd m.left P.left = 𝟙 _ := by
    refine ha.trans ?_
    rw [spMap, show CommRingCat.ofHom (RingHom.id V) = 𝟙 (CommRingCat.of V) from rfl, Spec.map_id]
  have key : (a ≫ pullback.fst m.left P.left) ≫ m.left = P.left := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, ha', Category.id_comp]
  refine ⟨Over.homMk (a ≫ pullback.fst m.left P.left) ?_, ?_⟩
  · rw [← Over.w m, ← Category.assoc, key]
    exact Over.w P
  · have e : ∀ Q : 𝟙_ (Over (Sp V)) ⟶ B, Q ^ n = Q ≫ m := fun Q => by
      rw [hm, comp_pow, Category.comp_id]
    rw [e]
    exact Over.OverMorphism.ext key

end GlobalTheory.AbDivLocal

namespace GlobalTheory.AbDivLocal

abbrev ptsModule {S : Scheme.{0}} (T : Over S) (B : Over S) [GrpObj B] [IsCommMonObj B] (O : Type)
    [CommRing O] (a : OAct O B) : Module O (Additive (T ⟶ B)) where
  smul o p := Additive.ofMul (p.toMul ≫ a.act o)
  one_smul p := by
    change Additive.ofMul (p.toMul ≫ a.act 1) = p
    rw [a.one, Category.comp_id]; rfl
  mul_smul o o' p := by
    change Additive.ofMul (p.toMul ≫ a.act (o * o')) =
      Additive.ofMul ((p.toMul ≫ a.act o') ≫ a.act o)
    rw [mul_comm, a.mul, Category.assoc]
  smul_zero o := by
    change Additive.ofMul ((1 : T ⟶ B) ≫ a.act o) = Additive.ofMul 1
    haveI := a.hom o
    rw [one_comp]
  smul_add o p q := by
    change Additive.ofMul ((p.toMul * q.toMul) ≫ a.act o) =
      Additive.ofMul ((p.toMul ≫ a.act o) * (q.toMul ≫ a.act o))
    haveI := a.hom o
    rw [mul_comp]
  add_smul o o' p := by
    change Additive.ofMul (p.toMul ≫ a.act (o + o')) =
      Additive.ofMul ((p.toMul ≫ a.act o) * (p.toMul ≫ a.act o'))
    rw [a.add, comp_mul]
  zero_smul p := by
    change Additive.ofMul (p.toMul ≫ a.act 0) = Additive.ofMul 1
    have h0 : a.act 0 = 1 := by
      have h := a.add 0 0
      rw [add_zero] at h
      exact (mul_eq_left.mp h.symm)
    rw [h0, comp_one]

theorem exists_divided_linear : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsNoetherianRing V], IsAdicComplete (maximalIdeal V) V → IsAlgClosed (ResidueField V) → ∀ (B : Over (Sp V)) [GrpObj B], IsAbelianScheme B → ∀ (O : Type) [CommRing O] [IsDomain O] [Module.Finite ℤ O] (a : OAct O B) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] (x : X → (𝟙_ (Over (Sp V)) ⟶ B)), (∀ y z, x (y + z) = x y * x z) → (∀ (o : O) y, x (o • y) = x y ≫ a.act o) → ∀ n : ℕ, IsUnit (n : V) → ∃ x' : X → (𝟙_ (Over (Sp V)) ⟶ B), (∀ y z, x' (y + z) = x' y * x' z) ∧ (∀ (o : O) y, x' (o • y) = x' y ≫ a.act o) ∧ ∀ y, x' (n • y) = x y := by
  intro V _ _ _ _ hc hk B _ hB O _ _ _ a X _ _ _ _ x hadd hsmul n hn
  haveI := hB.comm
  letI := ptsModule (𝟙_ (Over (Sp V))) B O a
  let g : X →ₗ[O] Additive (𝟙_ (Over (Sp V)) ⟶ B) :=
    { toFun := fun y => Additive.ofMul (x y)
      map_add' := fun y z => by rw [hadd]; rfl
      map_smul' := fun o y => by rw [hsmul]; rfl }
  let f : Additive (𝟙_ (Over (Sp V)) ⟶ B) →ₗ[O] Additive (𝟙_ (Over (Sp V)) ⟶ B) :=
    n • LinearMap.id
  have hf : Function.Surjective f := by
    intro p
    obtain ⟨Q, hQ⟩ := exists_pow_eq hc hk B hB n hn p.toMul
    refine ⟨Additive.ofMul Q, ?_⟩
    change n • Additive.ofMul Q = p
    rw [← ofMul_pow, hQ]; rfl
  obtain ⟨h, hh⟩ := Module.projective_lifting_property f g hf
  refine ⟨fun y => (h y).toMul, fun y z => by
      change (h (y + z)).toMul = (h y).toMul * (h z).toMul
      rw [map_add (f := _)]; rfl,
    fun o y => by
      change (h (o • y)).toMul = (h y).toMul ≫ a.act o
      rw [map_smul]; rfl, fun y => ?_⟩
  have e : n • h y = Additive.ofMul (x y) := LinearMap.congr_fun hh y
  change (h (n • y)).toMul = x y
  rw [map_nsmul, e]; rfl

end GlobalTheory.AbDivLocal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeModuleActionHomomorphismStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_scheme_module_action_homomorphism : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsNoetherianRing V], IsAdicComplete (maximalIdeal V) V → IsAlgClosed (ResidueField V) → ∀ (B : Over (Sp V)) [GrpObj B], IsAbelianScheme B → ∀ (O : Type) [CommRing O] [IsDomain O] [Module.Finite ℤ O] (a : OAct O B) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] (x : X → (𝟙_ (Over (Sp V)) ⟶ B)), (∀ y z, x (y + z) = x y * x z) → (∀ (o : O) y, x (o • y) = x y ≫ a.act o) → ∀ n : ℕ, IsUnit (n : V) → ∃ x' : X → (𝟙_ (Over (Sp V)) ⟶ B), (∀ y z, x' (y + z) = x' y * x' z) ∧ (∀ (o : O) y, x' (o • y) = x' y ≫ a.act o) ∧ ∀ y, x' (n • y) = x y := by
  first | exact @GlobalTheory.AbDivLocal.exists_divided_linear | exact GlobalTheory.AbDivLocal.exists_divided_linear | (intros; apply GlobalTheory.AbDivLocal.exists_divided_linear <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegeneratingFamilyDataFromBaseAlgClosedResidue
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.VData

theorem exists_divFrom : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → IsAlgClosed (ResidueField V) → ∀ (C : MonoFam Xo c φ V), Nontrivial C.P.D.toPre.X → ∃ (D' : Datum H) (L : LowBase D' c) (θ₀ : L.W →+* V) (N : ℕ) (ε : Module.Basis (Fin C.m ⊕ Fin N) ℤ (balForms H.bar L.D.X)) (e : C.P.D.toPre.X ≃ₗ[𝓞 E] L.D.X) (s : Fin C.m ⊕ Fin N → V), D'.p + Module.finrank (𝓞 E) C.P.D.toPre.X = Dw.p ∧ D'.q + Module.finrank (𝓞 E) C.P.D.toPre.X = Dw.q ∧ IsLocalHom θ₀ ∧ θ₀.comp L.b = C.b ∧ (∀ i, C.δ i = pull e.toLinearMap (ε (.inl i) : LinearMap.BilinForm ℤ L.D.X)) ∧ (∀ i, Associated (s (.inl i)) (C.s i)) ∧ (∀ j, IsUnit (s (.inr j))) ∧ DivFrom L C.P.D.toPre C.P.oD θ₀ s (fun k => (ε k : LinearMap.BilinForm ℤ L.D.X)) e := by
  intro E _ _ _ H Dw l Xo c φ V _ _ _ hV hk C hX
  haveI : IsNoetherianRing V := hV.1.1
  haveI : CharZero V := hV.2
  haveI : Module.Projective (𝓞 E) C.P.D.toPre.X := GlobalTheory.Forms.projective_of_int (𝓞 E) _
  haveI : Module.Finite (𝓞 E) C.P.D.toPre.X := Module.Finite.of_restrictScalars_finite ℤ _ _
  have hr : 1 ≤ Module.finrank (𝓞 E) C.P.D.toPre.X := Module.finrank_pos
  obtain ⟨Z, D', f, o', φB, -, -, -, hp, hq, hpb, hact, hw, -⟩ := GlobalTheory.LowDat.exists_lower Xo c V hV C.toFam hr
  have hrk := C.rank
  haveI : IsMonHom (Iso.refl C.P.D.toPre.P.A).hom := inferInstanceAs (IsMonHom (𝟙 _))
  obtain ⟨i, hi, hiφ⟩ := grpPullback_iso (isGrpPullback_of_iso (Iso.refl C.P.D.toPre.P.A)) hpb
  have hiφ' : i.hom.left ≫ φB = 𝟙 _ := hiφ
  have hia : ∀ a : 𝓞 E, (letI := H.starRing; C.P.oD.onB.act a) ≫ i.hom = i.hom ≫ o'.t.act.act a := by
    intro a
    apply Over.OverMorphism.ext
    apply hpb.1.hom_ext
    · rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hiφ', hact, ← Category.assoc, hiφ',
        Category.comp_id, Category.id_comp]
    · rw [Over.w, Over.w]
  have hM : IsUnit ((l.M' : ℕ) : V) := by
    have h1 : IsUnit ((l.M' : ℕ) : c.F) := IsUnit.mk0 _ (Nat.cast_ne_zero.2 (level_pos l).ne')
    simpa using h1.map C.b
  obtain ⟨x', hx₁, hx₂, hx₃⟩ := GlobalTheory.T.abelian_scheme_module_action_homomorphism V hV.1.2.2.2 hk o'.t.G
    ⟨o'.t.semi.comm, o'.t.semi.smooth, o'.proper, o'.t.semi.geomConnected⟩ (𝓞 E) o'.t.act
    C.P.D.toPre.X (fun y => C.P.D.toPre.c y ≫ i.hom)
    (fun y z => by
      rw [C.P.D.toPre.c_add, ← MonObj.mul_comp]; rfl)
    (fun a y => by
      letI := H.starRing
      rw [C.P.oD.c_lin, Category.assoc, hia, Category.assoc]) l.M' hM
  obtain ⟨L, θ₀, e, m, hθ, hb, hc⟩ := GlobalTheory.T.lowerDatumObject_comes_from_base_of_linearPoints D' c V C.b o' C.P.D.toPre.X x' hx₁ hx₂
  obtain ⟨N, b, hbas⟩ := C.cone.basis
  let ε := b.map (pullBalEquiv H.bar e).symm
  have hε : ∀ i, C.δ i = pull e.toLinearMap (ε (.inl i) : LinearMap.BilinForm ℤ L.D.X) := fun j => by
    have h1 : pullBalEquiv H.bar e (ε (.inl j)) = ⟨C.δ j, C.cone.mem j⟩ := by
      simp [ε, hbas]
    exact (congrArg Subtype.val h1).symm
  have hPL := C.P.D.toPre.P.isLB
  have l₁ : LBIso C.P.D.toPre.P.L (o'.t.PP.L.pull i.hom.left) :=
    LBIso.trans hPL (pull_isLB hPL _) (pull_isLB o'.t.PP.isLB _)
      ((GlobalTheory.PolBaseChange.lbIso_refl hPL).chartPull (chartPullId _) (Geo.Tor.chartPullPull _ _ _ rfl))
      (GenSpread.lbIso_pull_of_lbIso hw i.hom.left hiφ'.symm).symm
  have l₂ : LBIso o'.t.PP.L (L.o.t.PP.L.pull m.toSABMap.φ) := m.lin.imp fun _ h => h.1
  have l₃ : LBIso o'.t.PP.L (L.D.P.L.pull (m.toSABMap.φ ≫ L.φB)) :=
    LBIso.trans o'.t.PP.isLB (pull_isLB L.o.t.PP.isLB _) (pull_isLB L.D.P.isLB _) l₂ (GenSpread.lbIso_pull_of_lbIso L.ab.2.2 _ rfl)
  obtain ⟨s, h₁, h₂, h₃⟩ := GlobalTheory.T.exists_periods_monomialFamily_coords_over_base Xo c φ V hV hk C D' L θ₀ e (i.hom.left ≫ m.toSABMap.φ ≫ L.φB)
    (((isGrpPullback_of_iso i).comp (m.cart.comp L.ab.1)).congr (by simp) rfl)
    (fun a => by
      have h1 := congrArg (·.left) (hia a)
      simp only [Over.comp_left] at h1
      rw [← Category.assoc, h1, Category.assoc, ← Category.assoc _ m.toSABMap.φ, m.act, Category.assoc, L.ab.2.1]
      simp only [Category.assoc])
    (LBIso.trans hPL (pull_isLB o'.t.PP.isLB _) (pull_isLB L.D.P.isLB _) l₁ (GenSpread.lbIso_pull_of_lbIso l₃ _ rfl))
    (fun y => by
      rw [← map_nsmul, ← hc, hx₃, Over.comp_left, Category.assoc]) N ε hε
  exact ⟨D', L, θ₀, N, ε, e, s, by omega, by omega, hθ, hb, hε, h₁, h₂, h₃⟩

end GlobalTheory.VData
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegeneratingFamilyDataFromBaseAlgClosedResidueStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degeneratingFamily_data_from_base_algClosed_residue : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → IsAlgClosed (ResidueField V) → ∀ (C : MonoFam Xo c φ V), Nontrivial C.P.D.toPre.X → ∃ (D' : Datum H) (L : LowBase D' c) (θ₀ : L.W →+* V) (N : ℕ) (ε : Module.Basis (Fin C.m ⊕ Fin N) ℤ (balForms H.bar L.D.X)) (e : C.P.D.toPre.X ≃ₗ[𝓞 E] L.D.X) (s : Fin C.m ⊕ Fin N → V), D'.p + Module.finrank (𝓞 E) C.P.D.toPre.X = Dw.p ∧ D'.q + Module.finrank (𝓞 E) C.P.D.toPre.X = Dw.q ∧ IsLocalHom θ₀ ∧ θ₀.comp L.b = C.b ∧ (∀ i, C.δ i = pull e.toLinearMap (ε (.inl i) : LinearMap.BilinForm ℤ L.D.X)) ∧ (∀ i, Associated (s (.inl i)) (C.s i)) ∧ (∀ j, IsUnit (s (.inr j))) ∧ DivFrom L C.P.D.toPre C.P.oD θ₀ s (fun k => (ε k : LinearMap.BilinForm ℤ L.D.X)) e := by
  first | exact @GlobalTheory.VData.exists_divFrom | exact GlobalTheory.VData.exists_divFrom | (intros; apply GlobalTheory.VData.exists_divFrom <;> assumption)
end
