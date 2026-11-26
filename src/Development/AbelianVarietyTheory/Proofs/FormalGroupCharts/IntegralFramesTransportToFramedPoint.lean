module

public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FrameSymmetryIffPullback
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.HarmonicValueCopiesGaugeIndependent

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IntegralFramedPointDiagonalBiextensionIsoCompati
section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.PrimitiveIsoGUniqueOnAbelian
section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.PrimitiveIsoGUniqueOnAbelian
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

noncomputable section

namespace GlobalTheory

theorem linComb_gen_eq_of_eSec (hGF : GlobalFnsSt) {S X : Scheme.{0}} (A : Over S) [GrpObj A]
    (hA : IsAbelianScheme A) {L : LB X} (hL : L.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (A.left ⟶ X)} {ε : K → ℤ} {φ' : K' → ((𝟙_ (Over S)).left ⟶ X)} {ε' : K' → ℤ}
    {a b : LB.Gen (LB.LinComb L φ ε)} (ha : a.IsGen) (hb : b.IsGen) {r : LB.Gen (LB.LinComb L φ' ε')}
    (har : LB.Gen.Corr L _ _ _ _ (LB.pullGen L φ ε a (eSec A)) r)
    (hbr : LB.Gen.Corr L _ _ _ _ (LB.pullGen L φ ε b (eSec A)) r) : a = b := by
  have hcov : ∀ x : A.left, ∃ i, x ∈ (LB.LinComb L φ ε).U i := fun x => by
    choose I hI using fun k => exists_chart hL (φ k x)
    exact ⟨I, Set.mem_iInter.2 hI⟩
  obtain ⟨u, hu⟩ := ChartFrameTrA.exists_ratio_gen hcov ha hb
  suffices hu1 : u = 1 by
    cases a
    cases b
    congr 1
    funext p
    exact (hu p).trans (by rw [hu1, map_one, _root_.one_mul])
  apply ChartFrameTrA.unit_eq_one_of_eSec hGF A hA u
  have key : pullU (eSec A) ⊤ u = 1 := by
    refine unit_ext fun z hz => ?_
    choose J hJ using fun χ : (𝟙_ (Over S)).left ⟶ X => exists_chart hL (χ z)
    have hJ' : Good L z J := hJ
    have e1 := (val_pull hJ' a (eSec A) (𝟙 _)).symm.trans ((val_corr hJ' har (𝟙 _)).trans
      ((val_corr hJ' hbr (𝟙 _)).symm.trans (val_pull hJ' b (eSec A) (𝟙 _))))
    have hm := hJ'.mem φ (𝟙 _ ≫ eSec A)
    have e2 : val a (𝟙 _ ≫ eSec A) z J = gm (𝟙 _ ≫ eSec A) z ⊤ u * val b (𝟙 _ ≫ eSec A) z J :=
      (congrArg (gm _ z _) (hu _)).trans ((map_mul _ _ _).trans
        (congrArg₂ (· * ·) (gm_res _ z _ hm _) rfl))
    have e3 : gm (𝟙 _ ≫ eSec A) z ⊤ u = 1 := mul_eq_right.1 (e2.symm.trans e1)
    exact (gm_pull (𝟙 _) (eSec A) z ⊤ trivial u).trans (e3.trans (map_one _).symm)
  exact congrArg Units.val key

theorem isPrimG_unique : GlobalFnsSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (X0 : Scheme.{0}) (t : SAB H X0), IsAbelianScheme t.G → ∀ wP wP' : PrimTyG t,
    IsPrimG t wP → IsPrimG t wP' → wP = wP' :=
  fun hGF _ _ _ _ _ _ t hA _ _ h h' =>
    linComb_gen_eq_of_eSec hGF t.G hA t.PP.isLB h.1 h'.1 h.2 h'.2

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.PrimitiveIsoGUniqueOnAbelianStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitiveIsoG_unique_on_abelian : GlobalFnsSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0), IsAbelianScheme t.G → ∀ wP wP' : PrimTyG t, IsPrimG t wP → IsPrimG t wP' → wP = wP' := by
  first | exact @GlobalTheory.isPrimG_unique | exact GlobalTheory.isPrimG_unique | (intros; apply GlobalTheory.isPrimG_unique <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.PrimitiveIsoGPassesToPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.PrimitiveIsoGPassesToPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

noncomputable section

namespace GlobalTheory.PrimDown

theorem exists_down_id {X₀ X' Y : Scheme.{0}} {L : LB X₀} {L' : LB X'} {F : X' ⟶ X₀} {K : Type} [Fintype K]
    {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB) {φ' : K → (Y ⟶ X')} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) ε)) (ht : t.IsGen) : ∃ a : LB.Gen (LB.LinComb L' φ' ε), a.IsGen ∧
      ∀ (y : Y) p q, y ∈ LB.wchart L (fun k => φ' k ≫ F) p → y ∈ LB.wchart L' φ' q →
        gm (𝟙 Y) y _ (a.s q) = (pw w φ' ε (𝟙 Y) y p q)⁻¹ * gm (𝟙 Y) y (LB.wchart L (fun k => φ' k ≫ F) p) (t.s p) := by
  choose u hu using fun p q => exists_pw w φ' ε p q
  have glue : ∀ q : K → L'.ι, ∃ s : Γ(Y, LB.wchart L' φ' q)ˣ, ∀ (y : Y) p,
      y ∈ LB.wchart L (fun k => φ' k ≫ F) p → y ∈ LB.wchart L' φ' q →
      gm (𝟙 Y) y _ s = (pw w φ' ε (𝟙 Y) y p q)⁻¹ * gm (𝟙 Y) y (LB.wchart L (fun k => φ' k ≫ F) p) (t.s p) := by
    intro q
    have hv : ∀ (y : Y) p, y ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q →
        gm (𝟙 Y) y _ ((u p q)⁻¹ * res inf_le_left (t.s p)) =
          (pw w φ' ε (𝟙 Y) y p q)⁻¹ * gm (𝟙 Y) y (LB.wchart L (fun k => φ' k ≫ F) p) (t.s p) :=
      fun y p hz => (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_inv _ _).trans (congrArg (·⁻¹) (hu p q _ _ y hz)))
        (gm_res _ y _ hz _))
    obtain ⟨s, hs⟩ := glue_unit _ (fun p => LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q) (fun _ => inf_le_right)
      (fun y hy => by
        choose p hp using fun k => exists_chart hL (F (φ' k y))
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨p, Set.mem_iInter.2 hp, hy⟩) (fun p => (u p q)⁻¹ * res inf_le_left (t.s p))
      (fun p p' y hy => by
        rw [hv y p hy.1, hv y p' hy.2, pw_trans hw φ' ε (𝟙 Y) y hy.1.1 hy.2.1 hy.1.2 hy.1.2,
          trF_self hL' _ ε (𝟙 Y) y hy.1.2, gen_trans ht (𝟙 Y) y hy.1.1 hy.2.1, inv_one, _root_.mul_one, mul_inv,
          _root_.mul_mul_mul_comm, inv_mul_cancel, _root_.one_mul])
    refine ⟨s, fun y p h₁ h₂ => ?_⟩
    have hz : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q := ⟨h₁, h₂⟩
    exact (gm_res _ y inf_le_right hz s).symm.trans ((congrArg (gm _ y _) (hs p)).trans (hv y p hz))
  choose s hs using glue
  refine ⟨⟨s⟩, isGen_of_gm _ fun y j j' hj hj' => ?_, fun y p q h₁ h₂ => hs q y p h₁ h₂⟩
  choose p hp using fun k => exists_chart hL (F (φ' k y))
  have m : y ∈ LB.wchart L (fun k => φ' k ≫ F) p := Set.mem_iInter.2 hp
  refine (hs j y p m hj).trans (Eq.trans ?_ (congrArg _ (hs j' y p m hj')).symm)
  rw [pw_trans hw φ' ε (𝟙 Y) y m m hj hj', trF_self hL _ ε (𝟙 Y) y m, _root_.one_mul, mul_inv, inv_inv, _root_.mul_assoc]

theorem exists_down_all {X₀ X' Y : Scheme.{0}} {L : LB X₀} {L' : LB X'} {F : X' ⟶ X₀} {K : Type} [Fintype K]
    {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB) {φ' : K → (Y ⟶ X')} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) ε)) (ht : t.IsGen) :
    ∃ a : LB.Gen (LB.LinComb L' φ' ε), a.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (p : K → L.ι) (q : K → L'.ι),
        r z ∈ LB.wchart L (fun k => φ' k ≫ F) p → r z ∈ LB.wchart L' φ' q →
          gm r z (LB.wchart L (fun k => φ' k ≫ F) p) (t.s p) =
            pw w φ' ε r z p q * gm r z (LB.wchart L' φ' q) (a.s q) := by
  obtain ⟨a, ha, hv⟩ := exists_down_id hw hL hL' t ht
  obtain ⟨t₁, -, hu⟩ := exists_up hw hL hL' a ha
  have e : ∀ p, t.s p = t₁.s p := fun p => unit_ext fun y hy => by
    choose q hq using fun k => exists_chart hL' (φ' k y)
    have m : y ∈ LB.wchart L' φ' q := Set.mem_iInter.2 hq
    refine Eq.trans ?_ (hu _ (𝟙 Y) y p q hy m).symm
    exact (mul_inv_cancel_left _ _).symm.trans (congrArg _ (hv y p q hy m).symm)
  exact ⟨a, ha, fun Z r z p q hp hq => (congrArg (gm r z _) (e p)).trans (hu Z r z p q hp hq)⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem prod_eSec {X0 : Scheme.{0}} (t : SAB H X0) {U : Type} [CommGroup U]
    (h : ((𝟙_ (Over X0)).left ⟶ t.G.left) → U) :
    ∏ k, h (eSec t.G ≫ primφ t k) ^ primε k = h (eSec t.G) := by
  have hpt : ∀ I : ULift.{0} (Finset (Fin 2)), eSec t.G ≫ cφG t ![𝟙 t.G, t.act.act H.w0] I =
      (psum t.G ![1, η[t.G] ≫ t.act.act H.w0] I.down).left := by
    intro I
    simp only [cφG, eSec, ← Over.comp_left]
    refine congrArg Over.Hom.left ((psum_hom (ReciprocityTheory.ChartRestriction.G.Geo.Tor.preHom _) _ I.down).trans ?_)
    refine congrArg (fun f => psum t.G f I.down) (funext fun i => ?_)
    fin_cases i
    · exact (Category.comp_id _).trans (GermB.eta_one t.G)
    · rfl
  rw [Fintype.prod_sum_type]
  simp only [primφ, primε, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_one, Category.comp_id, zpow_neg,
    Finset.prod_inv_distrib, zpow_one]
  have z := (Finset.prod_congr rfl fun I _ => congrArg (fun q => h q ^ cε 2 I) (hpt I)).trans
    (GermB.cube_one_left t (fun p => h p.left) (η[t.G] ≫ t.act.act H.w0))
  exact (congrArg (fun u => h (eSec t.G) * u⁻¹) z).trans (by rw [inv_one, _root_.mul_one])

end GlobalTheory.PrimDown

namespace GlobalTheory

theorem primG_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 X1 : Scheme.{0}) (t : SAB H X0) (t' : SAB H X1) (f : X1 ⟶ X0) (mp : SABMap t' t f) (w : LB.Iso t'.PP.L (t.PP.L.pull mp.φ)), RigIso mp w → ∀ wP : PrimTyG t, IsPrimG t wP → ∃ wP' : PrimTyG t', IsPrimG t' wP' ∧ (∃ c₁ : LB.Gen (LB.LinComb t.PP.L (fun k => primφ t' k ≫ mp.φ) primε), LB.Gen.Corr t.PP.L _ _ _ _ c₁ (LB.pullGen t.PP.L _ _ wP mp.φ) ∧ LB.Gen.Maps (LB.linCombIso w (primφ t') primε) wP' (flatGen t.PP.L mp.φ _ _ c₁)) := by
  intro E _ _ _ H X0 X1 t t' f mp w hw wP hP
  have hL := t.PP.isLB
  have hL' := t'.PP.isLB
  obtain ⟨c₁, hc₁, hcc⟩ := ChartPrimTrPf.exists_reindex t.PP.L (φ := fun k => mp.φ ≫ primφ t k)
    (φ' := fun k => primφ t' k ≫ mp.φ) (funext fun k => ChartPrimTrPf.primφ_comm mp k) primε
    (LB.pullGen t.PP.L (primφ t) primε wP mp.φ) (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ _ hP.1 _)
  obtain ⟨a, ha, R⟩ := PrimDown.exists_down_all ((isGen_iff w).1 hw.1) hL hL' c₁ hc₁
  refine ⟨a, ⟨ha, corr_of_val hL' fun y J' hJ' => ?_⟩, c₁, hcc, ChartPrimTrPf.maps_flat w _ _ a c₁ R⟩
  choose J hJ using fun χ : (𝟙_ (Over X1)).left ⟶ t.G.left => exists_chart hL (χ y)
  have hJ : Good t.PP.L y J := hJ
  have pm := (maps_iff w _ (fun _ => eSec t.G) _ t'.PP.rig t.PP.rig mp.cm.e _
    (rigPull_le mp.cm.F mp.cm.e mp.cm.e_comm t.PP.L) (fun _ => rfl)).1 hw.2
  have e₁ := pm _ (𝟙 _) y (fun _ => J (eSec t'.G ≫ mp.φ)) (fun _ => J' (eSec t'.G)) (fun _ => hJ _) (fun _ => hJ' _)
  rw [Fintype.prod_unique, zpow_one, Category.id_comp, Category.id_comp] at e₁
  have e₂ : val c₁ (eSec t'.G) y J =
      gw w (eSec t'.G) y (J (eSec t'.G ≫ mp.φ)) (J' (eSec t'.G)) * val a (eSec t'.G) y J' := by
    refine (R _ (eSec t'.G) y _ _ (hJ.mem _ _) (hJ'.mem _ _)).trans (congrArg₂ (· * ·) ?_ rfl)
    refine Eq.trans ?_ (PrimDown.prod_eSec t' (fun q => gw w q y (J (q ≫ mp.φ)) (J' q)))
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Category.assoc]
  have e₃ : val c₁ (eSec t'.G) y J = val (L := t.PP.L) (φ := fun _ : PUnit => eSec t.G) (ε := fun _ => 1)
      t.PP.rig mp.cm.e y J := by
    refine (val_corr hJ hcc _).trans ((val_pull hJ _ _ _).trans ?_)
    refine Eq.trans ?_ (val_corr hJ hP.2 _)
    refine Eq.trans ?_ (val_pull hJ _ _ _).symm
    exact congrArg (fun r => val (L := t.PP.L) (φ := primφ t) (ε := primε) wP r y J) mp.cm.e_comm
  have e₄ := (val_of (L := t.PP.L) (φ := fun _ : PUnit => eSec t.G) (ε := fun _ => 1) t.PP.rig mp.cm.e y J
    (fun _ => J (eSec t'.G ≫ mp.φ)) (fun _ => congrArg J mp.cm.e_comm.symm)).trans e₁
  have e₅ := mul_left_cancel (e₂.symm.trans (e₃.trans e₄))
  refine (val_pull hJ' _ _ _).trans ?_
  rw [Category.id_comp]
  refine e₅.trans ?_
  exact (val_of (L := t'.PP.L) (φ := fun _ : PUnit => eSec t'.G) (ε := fun _ => 1) t'.PP.rig (𝟙 _) y J' _
    (fun _ => by rw [Category.id_comp])).symm

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.PrimitiveIsoGPassesToPullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitiveIsoG_passes_to_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 X1 : Scheme.{0}) (t : SAB H X0) (t' : SAB H X1) (f : X1 ⟶ X0) (mp : SABMap t' t f) (w : LB.Iso t'.PP.L (t.PP.L.pull mp.φ)), RigIso mp w → ∀ wP : PrimTyG t, IsPrimG t wP → ∃ wP' : PrimTyG t', IsPrimG t' wP' ∧ (∃ c₁ : LB.Gen (LB.LinComb t.PP.L (fun k => primφ t' k ≫ mp.φ) primε), LB.Gen.Corr t.PP.L _ _ _ _ c₁ (LB.pullGen t.PP.L _ _ wP mp.φ) ∧ LB.Gen.Maps (LB.linCombIso w (primφ t') primε) wP' (flatGen t.PP.L mp.φ _ _ c₁)) := by
  first | exact @GlobalTheory.primG_pullback | exact GlobalTheory.primG_pullback | (intros; apply GlobalTheory.primG_pullback <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IntegralFramedPointDiagonalBiextensionIsoCompati
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

namespace GlobalTheory

theorem chartPrimTr_holds : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ChartPrimTrSt Xo c := by
  intro E _ _ _ H Dw l Xo c T io y I wPT hT
  obtain ⟨wP, hP⟩ := GermB.exists_wP Xo.univ.t
  obtain ⟨w₁, hw₁, h₁⟩ := GlobalTheory.T.primitiveIsoG_passes_to_pullback E H _ _ _ _ _ I.m1 I.w1 I.rig1 wP hP
  obtain ⟨w₂, hw₂, h₂⟩ := GlobalTheory.T.primitiveIsoG_passes_to_pullback E H _ _ _ _ _ I.m2 I.w2 I.rig2 wPT hT
  have hab := GlobalTheory.isAbelianScheme_of_pullback_univ E H Dw l Xo _ _ _ I.m1
  have e : w₁ = w₂ := GlobalTheory.T.primitiveIsoG_unique_on_abelian GlobalTheory.firstFiveLaws.1.globalFns E H _ I.t' hab w₁ w₂ hw₁ hw₂
  subst e
  exact ⟨wP, (isPrim_iff wP).2 hP, w₁, hw₁.1, h₂, h₁⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IntegralFramedPointDiagonalBiextensionIsoCompatiStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralFramedPoint_diagonalBiextensionIso_compatible : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ChartPrimTrSt Xo c := by
  first | exact @GlobalTheory.chartPrimTr_holds | exact GlobalTheory.chartPrimTr_holds | (intros; apply GlobalTheory.chartPrimTr_holds <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FrameAdjointnessSeriesOfPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FrameAdjointnessSeriesOfPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

noncomputable section

namespace GlobalTheory.FrameAdjUp

section Pts

variable {S : Type} [CommRing S] (d : ℕ)

theorem subst_copy (m : ℕ) {n : ℕ} (φ : Fin 2 → Fin d → MvPolynomial (Fin n × Fin d) S) (i : Fin 2) :
    (jetSubstP m (fun p : Fin 2 × Fin d => φ p.1 p.2)).comp (jetCopy d m i) =
      jetSubstP m (fun p : Fin 1 × Fin d => φ i p.2) := by
  apply GermD.jet_hom_ext
  intro p
  simp only [AlgHom.comp_apply, jetSubstP, jetCopy, GermD.jetMap_mk, MvPolynomial.aeval_X]

theorem substX (m : ℕ) {n : ℕ} (k : Fin n) :
    jetSubstP m (fun p : Fin 1 × Fin d => (MvPolynomial.X (k, p.2) : MvPolynomial (Fin n × Fin d) S)) =
      jetCopy d m k := by
  apply GermD.jet_hom_ext
  intro p
  simp [jetSubstP, jetCopy, GermD.jetMap_mk]

def jetRen (m : ℕ) {n n' : ℕ} (r : Fin n → Fin n') : Jet S (Fin n × Fin d) m →ₐ[S] Jet S (Fin n' × Fin d) m :=
  jetMap (fun q : Fin n × Fin d => MvPolynomial.X (r q.1, q.2)) fun _ => X_mem_orig _

theorem ren_one (m : ℕ) {n' : ℕ} (r : Fin 1 → Fin n') : jetRen (S := S) d m r = jetCopy d m (r 0) := by
  apply GermD.jet_hom_ext
  rintro ⟨i, j⟩
  obtain rfl : i = 0 := Subsingleton.elim _ _
  simp only [jetRen, jetCopy, GermD.jetMap_mk, MvPolynomial.aeval_X]

theorem subst_psIn (m : ℕ) {n n' : ℕ} (r : Fin n → Fin n') (g : Fin d → MvPowerSeries (Fin n × Fin d) S) :
    jetSubstP m (fun p : Fin 1 × Fin d => psIn d m r (g p.2)) =
      (jetRen d m r).comp (jetSubstP m (fun p : Fin 1 × Fin d => psTrunc m (g p.2))) := by
  have hr : (MvPolynomial.aeval fun q : Fin n × Fin d => (MvPolynomial.X (r q.1, q.2) : MvPolynomial (Fin n' × Fin d) S)) =
      MvPolynomial.rename fun p : Fin n × Fin d => (r p.1, p.2) := MvPolynomial.algHom_ext fun q => by simp
  apply GermD.jet_hom_ext
  intro p
  simp only [jetSubstP, jetRen, AlgHom.comp_apply, GermD.jetMap_mk, MvPolynomial.aeval_X, map_sub, MvPolynomial.aeval_C,
    MvPolynomial.algebraMap_eq, psIn, MvPolynomial.constantCoeff_rename, hr, MvPolynomial.rename_C]

end Pts

section Chart

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} {t : SAB H X0}
variable {S : Type} [CommRing S] {x0 : Sp S ⟶ X0} {d : ℕ} {x : ∀ m, jOG x0 d m 1 ⟶ t.G}

theorem pt_sub (m : ℕ) {n : ℕ} (φ : Fin 2 → Fin d → MvPolynomial (Fin n × Fin d) S) (i : Fin 2) :
    Formalism.L2.Pj.homAt x0 (jetSubstP m (fun p : Fin 2 × Fin d => φ p.1 p.2)) ≫ jptG t x0 d x m i =
      Formalism.L2.Pj.homAt x0 (jetSubstP m (fun p : Fin 1 × Fin d => φ i p.2)) ≫ x m := by
  rw [jptG, ← Category.assoc, GermD.homAt_comp, subst_copy]

theorem pt_X (m : ℕ) {n : ℕ} (k : Fin n) :
    Formalism.L2.Pj.homAt x0 (jetSubstP m (fun p : Fin 1 × Fin d => (MvPolynomial.X (k, p.2) : MvPolynomial (Fin n × Fin d) S))) ≫ x m =
      jptG t x0 d x m k := by
  rw [substX]
  try rfl

theorem pe_pt (m : ℕ) {n : ℕ} (σ : Jet S (Fin 2 × Fin d) m →ₐ[S] Jet S (Fin n × Fin d) m) (I : ULift.{0} (Finset (Fin 2))) :
    (Formalism.L2.Pj.homAt x0 σ).left ≫ cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)] I =
      (psum t.G ![Formalism.L2.Pj.homAt x0 σ ≫ jptG t x0 d x m (0 : Fin 2), Formalism.L2.Pj.homAt x0 σ ≫ jptG t x0 d x m (1 : Fin 2)] I.down).left := by
  simp only [cφG, ← Over.comp_left]
  refine congrArg Over.Hom.left ((psum_hom (ReciprocityTheory.ChartRestriction.G.Geo.Tor.preHom _) _ I.down).trans ?_)
  refine congrArg (fun f => psum t.G f I.down) (funext fun i => ?_)
  fin_cases i <;> rfl

theorem wl_pt {T : Over X0} (a b : T ⟶ t.G) (c : 𝓞 E) (I : ULift.{0} (Finset (Fin 2))) :
    (lift a b).left ≫ cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act c] I =
      (psum t.G ![a, b ≫ t.act.act c] I.down).left := by
  simp only [cφG, ← Over.comp_left]
  refine congrArg Over.Hom.left ((psum_hom (ReciprocityTheory.ChartRestriction.G.Geo.Tor.preHom _) _ I.down).trans ?_)
  refine congrArg (fun f => psum t.G f I.down) (funext fun i => ?_)
  fin_cases i
  · show lift a b ≫ fst t.G t.G = a
    exact lift_fst _ _
  · show lift a b ≫ (snd t.G t.G ≫ t.act.act c) = b ≫ t.act.act c
    exact lift_snd_assoc _ _ _

theorem wl_pt' {T : Over X0} (a b : T ⟶ t.G) (c : 𝓞 E) (I : ULift.{0} (Finset (Fin 2))) :
    (lift a b).left ≫ cφG t ![fst t.G t.G ≫ t.act.act c, snd t.G t.G] I =
      (psum t.G ![a ≫ t.act.act c, b] I.down).left := by
  simp only [cφG, ← Over.comp_left]
  refine congrArg Over.Hom.left ((psum_hom (ReciprocityTheory.ChartRestriction.G.Geo.Tor.preHom _) _ I.down).trans ?_)
  refine congrArg (fun f => psum t.G f I.down) (funext fun i => ?_)
  fin_cases i
  · show lift a b ≫ (fst t.G t.G ≫ t.act.act c) = a ≫ t.act.act c
    exact lift_fst_assoc _ _ _
  · show lift a b ≫ snd t.G t.G = b
    exact lift_snd _ _

end Chart

section Val

variable {X X' Y P P' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K K₁ W : Type} [Fintype K] [Fintype K₁]
  [Fintype W]

theorem corr_up (hL : L.IsLB) (hL' : L'.IsLB) (w : LB.Iso L' (L.pull F)) (φ' : K → (Y ⟶ X')) (ε : K → ℤ)
    (a : LB.Gen (LB.LinComb L' φ' ε)) (c : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) ε))
    (hm : LB.Gen.Maps (LB.linCombIso w φ' ε) a (flatGen L F φ' ε c))
    (φ : K₁ → (Y ⟶ X)) (ε₁ : K₁ → ℤ) (e : LB.Gen (LB.LinComb L φ ε₁)) (hc : LB.Gen.Corr L _ _ _ _ c e)
    (ψ' : W → (P' ⟶ X')) (ψ : W → (P ⟶ X)) (δ : W → ℤ) (v' : LB.Gen (LB.LinComb L' ψ' δ))
    (v : LB.Gen (LB.LinComb L ψ δ)) (l' : Y ⟶ P') (l : Y ⟶ P)
    (hv : ∀ (y : Y) J J', Good L y J → Good L' y J' → val v l y J =
      (∏ k, gw w (l' ≫ ψ' k) y (J ((l' ≫ ψ' k) ≫ F)) (J' (l' ≫ ψ' k)) ^ δ k) * val v' l' y J')
    (s₁ s₂ : Y ⟶ Y)
    (hs : FormEq (Sum.elim (fun k => l' ≫ ψ' k) (fun k => s₁ ≫ φ' k)) (Sum.elim δ ε) (fun k => s₂ ≫ φ' k) ε)
    (u : Γ(Y, ⊤)ˣ)
    (h : LB.Gen.Corr L' _ _ _ _ (LB.mulGen L' _ _ _ _ (LB.pullGen L' ψ' δ v' l') (LB.pullGen L' φ' ε a s₁))
      (FrameSym.scale _ _ u (LB.pullGen L' φ' ε a s₂))) :
    LB.Gen.Corr L _ _ _ _ (LB.mulGen L _ _ _ _ (LB.pullGen L ψ δ v l) (LB.pullGen L φ ε₁ e s₁))
      (FrameSym.scale _ _ u (LB.pullGen L φ ε₁ e s₂)) := by
  refine corr_of_val hL fun y J hJ => ?_
  obtain ⟨J', hJ'⟩ := FrameSym.good_exists hL' y
  have h' := val_corr hJ' h (𝟙 Y)
  rw [val_mul hJ', FrameSym.val_scale _ _ _ _ hJ', val_pull hJ', val_pull hJ', val_pull hJ'] at h'
  rw [val_mul hJ, FrameSym.val_scale _ _ _ _ hJ, val_pull hJ, val_pull hJ, val_pull hJ, ← val_corr hJ hc,
    ← val_corr hJ hc, FrameSym.val_tie w φ' ε a c hm _ y hJ hJ', FrameSym.val_tie w φ' ε a c hm _ y hJ hJ']
  simp only [Category.id_comp] at h' ⊢
  have p := hs _ (fun q => gw w q y (J (q ≫ F)) (J' q))
  rw [Fintype.prod_sum_type] at p
  simp only [Sum.elim_inl, Sum.elim_inr] at p
  rw [hv y J J' hJ hJ', _root_.mul_mul_mul_comm, p, h', _root_.mul_left_comm]

end Val

section Adj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

abbrev adφ {B : Scheme.{0}} (t : SAB H B) (a : 𝓞 E) :
    ULift.{0} (Finset (Fin 2)) ⊕ ULift.{0} (Finset (Fin 2)) → ((t.G ⊗ t.G).left ⟶ t.G.left) :=
  Sum.elim (cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)]) (cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G])

abbrev adε : ULift.{0} (Finset (Fin 2)) ⊕ ULift.{0} (Finset (Fin 2)) → ℤ := Sum.elim (cε 2) fun I => -cε 2 I

variable {B B' : Scheme.{0}} {t : SAB H B} {t' : SAB H B'} {f : B' ⟶ B} (mp : SABMap t' t f)

def sqMap : Over.mk ((t'.G ⊗ t'.G).hom ≫ f) ⟶ t.G ⊗ t.G :=
  lift (pushPt mp.cart.1.w (fst t'.G t'.G)) (pushPt mp.cart.1.w (snd t'.G t'.G))

theorem push_act {T : Over B'} (x : T ⟶ t'.G) (a : 𝓞 E) :
    pushPt mp.cart.1.w (x ≫ t'.act.act a) = pushPt mp.cart.1.w x ≫ t.act.act a :=
  Over.OverMorphism.ext (by
    show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
    rw [Category.assoc, mp.act, Category.assoc])

theorem adφ_comm (a : 𝓞 E) (k) : adφ t' a k ≫ mp.φ = (sqMap mp).left ≫ adφ t a k := by
  rcases k with I | I
  · refine psum_push mp.cart _ _ (sqMap mp) (fun i => ?_) I.down
    fin_cases i
    · simp [sqMap]
    · exact (push_act mp _ _).trans (by simp [sqMap])
  · refine psum_push mp.cart _ _ (sqMap mp) (fun i => ?_) I.down
    fin_cases i
    · exact (push_act mp _ _).trans (by simp [sqMap])
    · simp [sqMap]

theorem lift_sqMap {T' : Over B'} {T : Over B} (g : T'.left ⟶ T.left) (p' q' : T' ⟶ t'.G) (p q : T ⟶ t.G)
    (hp : p'.left ≫ mp.φ = g ≫ p.left) (hq : q'.left ≫ mp.φ = g ≫ q.left) :
    (lift p' q').left ≫ (sqMap mp).left = g ≫ (lift p q).left := by
  apply pullback.hom_ext
  · show (_ ≫ (sqMap mp).left) ≫ (fst t.G t.G).left = (_ ≫ _) ≫ (fst t.G t.G).left
    rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_fst, sqMap, lift_fst, ← hp]
    show (lift p' q').left ≫ (fst t'.G t'.G).left ≫ mp.φ = _
    rw [← Category.assoc, ← Over.comp_left, lift_fst]
  · show (_ ≫ (sqMap mp).left) ≫ (snd t.G t.G).left = (_ ≫ _) ≫ (snd t.G t.G).left
    rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_snd, sqMap, lift_snd, ← hq]
    show (lift p' q').left ≫ (snd t'.G t'.G).left ≫ mp.φ = _
    rw [← Category.assoc, ← Over.comp_left, lift_snd]

theorem prod_adjointnessBundle_zeroSection_eq_one (a : 𝓞 E) {U : Type} [CommGroup U] (h : ((𝟙_ (Over B)).left ⟶ t.G.left) → U) :
    ∏ k, h ((GermB.zz t).left ≫ adφ t a k) ^ adε k = 1 := by
  rw [Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, wl_pt, wl_pt', zpow_neg, Finset.prod_inv_distrib,
    GermB.eta_one]
  rw [GermB.cube_one_left t (fun p => h p.left), GermB.cube_one_right t (fun p => h p.left), inv_one, _root_.mul_one]

theorem val_ad (hG : GlobalFnsSt) (hA : IsAbelianScheme t'.G) (w : LB.Iso t'.PP.L (t.PP.L.pull mp.φ)) (hw : w.IsGen)
    (a : 𝓞 E) (v' : LB.Gen (LB.LinComb t'.PP.L (adφ t' a) adε)) (hv' : v'.IsGen)
    (h' : ∀ y J', Good t'.PP.L y J' → val v' (GermB.zz t').left y J' = 1)
    (v : LB.Gen (LB.LinComb t.PP.L (adφ t a) adε)) (hv : v.IsGen)
    (h : ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over B)).left) (z : Z) J, Good t.PP.L z J →
      val v (r ≫ (GermB.zz t).left) z J = 1)
    {Z : Scheme.{0}} (r : Z ⟶ (t'.G ⊗ t'.G).left) (z : Z) J J' (hJ : Good t.PP.L z J) (hJ' : Good t'.PP.L z J') :
    val v (r ≫ (sqMap mp).left) z J =
      (∏ k, gw w (r ≫ adφ t' a k) z (J ((r ≫ adφ t' a k) ≫ mp.φ)) (J' (r ≫ adφ t' a k)) ^ adε k) * val v' r z J' := by
  obtain ⟨c, hc, R⟩ := exists_up ((isGen_iff w).1 hw) t.PP.isLB t'.PP.isLB v' hv'
  have R' : ∀ (Z : Scheme.{0}) (r : Z ⟶ (t'.G ⊗ t'.G).left) (z : Z) J J', Good t.PP.L z J → Good t'.PP.L z J' →
      val c r z J = (∏ k, gw w (r ≫ adφ t' a k) z (J ((r ≫ adφ t' a k) ≫ mp.φ)) (J' (r ≫ adφ t' a k)) ^ adε k) *
        val v' r z J' := fun Z r z J J' hJ hJ' => by
    refine (R Z r z _ _ (hJ.mem _ r) (hJ'.mem _ r)).trans (congrArg₂ (· * ·) (Finset.prod_congr rfl fun I _ => ?_) rfl)
    rw [Category.assoc]
  have sj : Function.Surjective ((snd t'.G t'.G).left ≫ t'.G.hom).appTop.hom :=
    surj_comp (surj_snd hG hA _) (hG _ _ hA).2
  have he : (GermB.zz t').left ≫ (snd t'.G t'.G).left ≫ t'.G.hom = 𝟙 _ := by
    rw [Over.w]; exact Over.w (GermB.zz t')
  have key := gen_unique' t.PP.isLB (φ := fun k => (sqMap mp).left ≫ adφ t a k) (ε := adε)
    (fun V _ k => Finset.prod_congr rfl fun I _ => congrArg (fun q => k q ^ adε I) (adφ_comm mp a I))
    _ (GermB.zz t').left he sj (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ _ hv (sqMap mp).left) hc (fun y I hI => by
      obtain ⟨I', hI'⟩ := FrameSym.good_exists t'.PP.isLB y
      refine Eq.trans ?_ ((R' _ _ y I I' hI hI').trans (congrArg₂ (· * ·)
        (prod_adjointnessBundle_zeroSection_eq_one a (fun q => gw w q y (I (q ≫ mp.φ)) (I' q))) (h' y I' hI'))).symm
      rw [_root_.mul_one]
      refine (val_pull hI _ _ _).trans ?_
      rw [lift_sqMap mp mp.cm.e _ _ _ _ mp.cm.e_comm mp.cm.e_comm]
      exact h _ _ y I hI) _ r z J hJ
  exact (val_pull hJ _ _ _).symm.trans (key.trans (R' _ _ z J J' hJ hJ'))

end Adj

theorem psJet_zero_of {S κ : Type} [CommRing S] [Fintype κ] [DecidableEq κ] (f : MvPowerSeries κ S)
    (hf : MvPowerSeries.constantCoeff f = 1) : psJet 0 f = 1 := by
  have hc : MvPolynomial.constantCoeff (psTrunc 0 f) = 1 := by
    rw [MvPolynomial.constantCoeff_eq, GermFun.coeff_psTrunc _ _ _ (by simp),
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf]
  unfold psJet
  rw [← map_one (Ideal.Quotient.mk (orig S κ ^ (0 + 1)))]
  refine Ideal.Quotient.eq.2 ?_
  have := sub_const_mem_orig (psTrunc 0 f)
  rw [hc, map_one] at this
  rwa [zero_add, pow_one]

theorem aug_subst {S κ κ' : Type} [CommRing S] (m : ℕ) (φ : κ → MvPolynomial κ' S) :
    (jetAug : Jet S κ' m →ₐ[S] S).comp (jetSubstP m φ) = jetAug := by
  apply GermD.jet_hom_ext
  intro p
  have h0 : ∀ q : MvPolynomial κ' S, MvPolynomial.aeval (fun _ => (0 : S)) q = MvPolynomial.constantCoeff q := by
    intro q
    induction q using MvPolynomial.induction_on <;> simp_all
  rw [GermB.jetAug_X, AlgHom.comp_apply, jetSubstP, GermD.jetMap_mk, MvPolynomial.aeval_X]
  show MvPolynomial.aeval (fun _ => (0 : S)) _ = 0
  rw [h0]; simp

theorem pt_act' {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} {t : SAB H X0}
    {S : Type} [CommRing S] {x0 : Sp S ⟶ X0} {d : ℕ} {x : ∀ m, jOG x0 d m 1 ⟶ t.G}
    {act : 𝓞 E → Fin d → PS S 1 d}
    (hact : ∀ m (b : 𝓞 E), x m ≫ t.act.act b =
      Formalism.L2.Pj.homAt x0 (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (act b p.2)) ≫ x m)
    (m : ℕ) {n : ℕ} (r : Fin 1 → Fin n) (a : 𝓞 E) :
    Formalism.L2.Pj.homAt x0 (jetSubstP m (fun p : Fin 1 × Fin d => psIn d m r (act a p.2))) ≫ x m =
      jptG t x0 d x m (r 0) ≫ t.act.act a := by
  rw [subst_psIn, ← GermD.homAt_comp, Category.assoc, ← hact m a, ← Category.assoc, ren_one]
  try rfl

set_option maxHeartbeats 1000000 in
theorem frame_adj_up : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (t' : SAB H (Sp S)) (mp : SABMap t' t x0) (w : LB.Iso t'.PP.L (t.PP.L.pull mp.φ)), RigIso mp w → ∀ (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp S)) d m 1 ⟶ t'.G), (∀ m, (x' m).left ≫ mp.φ = (x m).left) → IsAbelianScheme t'.G → (homAt (𝟙 (Sp S)) (jetAug : Jet S (Fin 1 × Fin d) 0 →ₐ[S] S) ≫ x' 0 = 1) → ∀ (e : ∀ m, FrTyG t x0 d x m) (e' : ∀ m, FrTyG t' (𝟙 (Sp S)) d x' m), (∀ m, (e m).IsGen) → (∀ m, (e' m).IsGen) → (∀ m, ∃ c₁ : LB.Gen (LB.LinComb t.PP.L (fun J => cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)] J ≫ mp.φ) (cε 2)), LB.Gen.Corr t.PP.L _ _ _ _ c₁ (e m) ∧ LB.Gen.Maps (LB.linCombIso w (cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)]) (cε 2)) (e' m) (flatGen t.PP.L mp.φ _ _ c₁)) → ∀ (act : 𝓞 E → Fin d → PS S 1 d) (ad : 𝓞 E → PS S 2 d) (a : 𝓞 E), (∀ m (b : 𝓞 E), x' m ≫ t'.act.act b = homAt (𝟙 (Sp S)) (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (act b p.2)) ≫ x' m) → (∀ b j, MvPowerSeries.constantCoeff (act b j) = 0) → MvPowerSeries.constantCoeff (ad a) = 1 → (∃ wL : LB.Gen (LB.LinComb t'.PP.L (Sum.elim (cφG t' ![fst t'.G t'.G, snd t'.G t'.G ≫ t'.act.act (H.bar a)]) (cφG t' ![fst t'.G t'.G ≫ t'.act.act a, snd t'.G t'.G])) (Sum.elim (cε 2) fun I => -cε 2 I)), wL.IsGen ∧ ∀ m, ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ, (u : Jet S (Fin 2 × Fin d) m) = psJet m (ad a) ∧ LB.Gen.Corr t'.PP.L _ _ _ _ (LB.mulGen t'.PP.L _ _ _ _ (LB.pullGen t'.PP.L _ _ wL (lift (jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2)) (jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2))).left) (peG t' (𝟙 (Sp S)) d x' e' m ![fun j => psIn d m ![0] (act a j), fun j => X ((1 : Fin 2), j)])) (scaleGenG t' _ _ (unitΓ u) (peG t' (𝟙 (Sp S)) d x' e' m ![fun j => X ((0 : Fin 2), j), fun j => psIn d m ![1] (act (H.bar a) j)]))) → (∃ wL : LB.Gen (LB.LinComb t.PP.L (Sum.elim (cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)]) (cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G])) (Sum.elim (cε 2) fun I => -cε 2 I)), wL.IsGen ∧ ∀ m, ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ, (u : Jet S (Fin 2 × Fin d) m) = psJet m (ad a) ∧ LB.Gen.Corr t.PP.L _ _ _ _ (LB.mulGen t.PP.L _ _ _ _ (LB.pullGen t.PP.L _ _ wL (lift (jptG t x0 d x m (0 : Fin 2)) (jptG t x0 d x m (1 : Fin 2))).left) (peG t x0 d x e m ![fun j => psIn d m ![0] (act a j), fun j => X ((1 : Fin 2), j)])) (scaleGenG t _ _ (unitΓ u) (peG t x0 d x e m ![fun j => X ((0 : Fin 2), j), fun j => psIn d m ![1] (act (H.bar a) j)]))) := by
  intro hLaws E _ _ _ H X0 t S _ x0 t' mp w hw d x x' hx hA h0 e e' _ _ ht act ad a hact _ had ⟨v', hv', hr⟩
  obtain ⟨v, hv, hv0⟩ := GermB.exists_wL t a
  have hz : ∀ y J', Good t'.PP.L y J' → val v' (GermB.zz t').left y J' = 1 := by
    intro y J' hJ'
    obtain ⟨u, hu, hc⟩ := hr 0
    obtain rfl : u = 1 := Units.ext (hu.trans (psJet_zero_of _ had))
    let ρ : overAt (𝟙 (Sp S)) S ⟶ jOG (𝟙 (Sp S)) d 0 2 :=
      Formalism.L2.Pj.homAt (𝟙 (Sp S)) (jetAug : Jet S (Fin 2 × Fin d) 0 →ₐ[S] S)
    have hρ : ∀ φ : Fin 2 × Fin d → MvPolynomial (Fin 2 × Fin d) S,
        ρ.left ≫ (Formalism.L2.Pj.homAt (𝟙 (Sp S)) (jetSubstP 0 φ)).left = ρ.left := fun φ => by
      rw [← Over.comp_left, GermD.homAt_comp, aug_subst]
    have hj : ∀ i : Fin 2, ρ ≫ jptG t' (𝟙 (Sp S)) d x' 0 i = 1 := fun i => by
      rw [jptG, ← Category.assoc, GermD.homAt_comp, GermB.aug_copy, h0]
    have hl : ρ.left ≫ (lift (jptG t' (𝟙 (Sp S)) d x' 0 (0 : Fin 2)) (jptG t' (𝟙 (Sp S)) d x' 0 (1 : Fin 2))).left =
        (GermB.zz t').left := by
      rw [← Over.comp_left, comp_lift, hj, hj]
      refine (congrArg Over.Hom.left (comp_lift (toUnit (overAt (𝟙 (Sp S)) S)) η[t'.G] η[t'.G]).symm).trans ?_
      show (toUnit (overAt (𝟙 (Sp S)) S)).left ≫ (GermB.zz t').left = _
      have : (toUnit (overAt (𝟙 (Sp S)) S)).left = 𝟙 (Sp S) := by
        show spMap (algebraMap S S) ≫ 𝟙 _ = _
        simp [spMap]
      rw [this]; exact Category.id_comp _
    have hJ'' : Good (Z := Sp S) t'.PP.L y J' := hJ'
    have e1 := (val_mul hJ'' _ _ _).symm.trans ((val_corr hJ'' hc ρ.left).trans (GermB.val_scale t' _ _ _ _ _ y J' hJ''))
    have e2 := (congrArg₂ (· * ·) (val_pull hJ'' _ _ _) (val_pull hJ'' _ _ _)).symm.trans
      (e1.trans (congrArg₂ (· * ·) rfl (val_pull hJ'' _ _ _)))
    rw [hρ, hρ, hl, unitΓ, map_one, map_one] at e2
    exact mul_right_cancel e2
  refine ⟨v, hv, fun m => ?_⟩
  obtain ⟨u, hu, hc⟩ := hr m
  obtain ⟨c₁, hc₁, hm⟩ := ht m
  have hjx : ∀ i : Fin 2, (jptG t' (𝟙 (Sp S)) d x' m i).left ≫ mp.φ = 𝟙 _ ≫ (jptG t x0 d x m i).left := fun i => by
    rw [Category.id_comp]
    show (_ ≫ (x' m).left) ≫ _ = _ ≫ (x m).left
    rw [Category.assoc, hx]; rfl
  have hl := (lift_sqMap mp (T' := jOG (𝟙 (Sp S)) d m 2) (T := jOG x0 d m 2) (𝟙 _) _ _ _ _ (hjx 0) (hjx 1)).trans
    (Category.id_comp _)
  have hF : FormEq (Sum.elim
      (fun k => (lift (jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2)) (jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2))).left ≫ adφ t' a k)
      (fun k => (Formalism.L2.Pj.homAt (𝟙 (Sp S)) (jetSubstP m fun p : Fin 2 × Fin d =>
        (![fun j => psIn d m ![0] (act a j), fun j => X ((1 : Fin 2), j)] :
          Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) p.1 p.2)).left ≫
        cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)] k)) (Sum.elim adε (cε 2))
      (fun k => (Formalism.L2.Pj.homAt (𝟙 (Sp S)) (jetSubstP m fun p : Fin 2 × Fin d =>
        (![fun j => X ((0 : Fin 2), j), fun j => psIn d m ![1] (act (H.bar a) j)] :
          Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) p.1 p.2)).left ≫
        cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)] k) (cε 2) := by
    intro U _ h
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, wl_pt, wl_pt', pe_pt, pt_sub,
      Matrix.cons_val_zero, Matrix.cons_val_one, pt_X, pt_act' hact, zpow_neg, Finset.prod_inv_distrib]
    simp only [inv_mul_cancel_right]
  refine ⟨u, hu, corr_up t.PP.isLB t'.PP.isLB w _ (cε 2) (e' m) c₁ hm
    (cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)]) (cε 2) (e m) hc₁ (adφ t' a) (adφ t a) adε v' v
    _ _ (fun y J J' hJ hJ' => ?_) _ _ hF (unitΓ u) hc⟩
  exact (congrArg (fun r => val v r y J) hl).symm.trans
      (val_ad mp hLaws.globalFns hA w hw.1 a v' hv' hz v hv hv0 _ y J J' hJ hJ')

end GlobalTheory.FrameAdjUp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FrameAdjointnessSeriesOfPullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_adjointness_series_of_pullback : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (t' : SAB H (Sp S)) (mp : SABMap t' t x0) (w : LB.Iso t'.PP.L (t.PP.L.pull mp.φ)), RigIso mp w → ∀ (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp S)) d m 1 ⟶ t'.G), (∀ m, (x' m).left ≫ mp.φ = (x m).left) → IsAbelianScheme t'.G → (homAt (𝟙 (Sp S)) (jetAug : Jet S (Fin 1 × Fin d) 0 →ₐ[S] S) ≫ x' 0 = 1) → ∀ (e : ∀ m, FrTyG t x0 d x m) (e' : ∀ m, FrTyG t' (𝟙 (Sp S)) d x' m), (∀ m, (e m).IsGen) → (∀ m, (e' m).IsGen) → (∀ m, ∃ c₁ : LB.Gen (LB.LinComb t.PP.L (fun J => cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)] J ≫ mp.φ) (cε 2)), LB.Gen.Corr t.PP.L _ _ _ _ c₁ (e m) ∧ LB.Gen.Maps (LB.linCombIso w (cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)]) (cε 2)) (e' m) (flatGen t.PP.L mp.φ _ _ c₁)) → ∀ (act : 𝓞 E → Fin d → PS S 1 d) (ad : 𝓞 E → PS S 2 d) (a : 𝓞 E), (∀ m (b : 𝓞 E), x' m ≫ t'.act.act b = homAt (𝟙 (Sp S)) (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (act b p.2)) ≫ x' m) → (∀ b j, MvPowerSeries.constantCoeff (act b j) = 0) → MvPowerSeries.constantCoeff (ad a) = 1 → (∃ wL : LB.Gen (LB.LinComb t'.PP.L (Sum.elim (cφG t' ![fst t'.G t'.G, snd t'.G t'.G ≫ t'.act.act (H.bar a)]) (cφG t' ![fst t'.G t'.G ≫ t'.act.act a, snd t'.G t'.G])) (Sum.elim (cε 2) fun I => -cε 2 I)), wL.IsGen ∧ ∀ m, ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ, (u : Jet S (Fin 2 × Fin d) m) = psJet m (ad a) ∧ LB.Gen.Corr t'.PP.L _ _ _ _ (LB.mulGen t'.PP.L _ _ _ _ (LB.pullGen t'.PP.L _ _ wL (lift (jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2)) (jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2))).left) (peG t' (𝟙 (Sp S)) d x' e' m ![fun j => psIn d m ![0] (act a j), fun j => X ((1 : Fin 2), j)])) (scaleGenG t' _ _ (unitΓ u) (peG t' (𝟙 (Sp S)) d x' e' m ![fun j => X ((0 : Fin 2), j), fun j => psIn d m ![1] (act (H.bar a) j)]))) → (∃ wL : LB.Gen (LB.LinComb t.PP.L (Sum.elim (cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)]) (cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G])) (Sum.elim (cε 2) fun I => -cε 2 I)), wL.IsGen ∧ ∀ m, ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ, (u : Jet S (Fin 2 × Fin d) m) = psJet m (ad a) ∧ LB.Gen.Corr t.PP.L _ _ _ _ (LB.mulGen t.PP.L _ _ _ _ (LB.pullGen t.PP.L _ _ wL (lift (jptG t x0 d x m (0 : Fin 2)) (jptG t x0 d x m (1 : Fin 2))).left) (peG t x0 d x e m ![fun j => psIn d m ![0] (act a j), fun j => X ((1 : Fin 2), j)])) (scaleGenG t _ _ (unitΓ u) (peG t x0 d x e m ![fun j => X ((0 : Fin 2), j), fun j => psIn d m ![1] (act (H.bar a) j)]))) := by
  first | exact @GlobalTheory.FrameAdjUp.frame_adj_up | exact GlobalTheory.FrameAdjUp.frame_adj_up | (intros; apply GlobalTheory.FrameAdjUp.frame_adj_up <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsCubeFramesFromPullbackTriple
section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsCubeFramesFromPullbackTriple
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Chart.FrameUp

theorem cube_points_push {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}}
    (t : SAB H X0) {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (t' : SAB H (Sp S)) (mp : SABMap t' t x0) (d : ℕ)
    (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp S)) d m 1 ⟶ t'.G)
    (hx : ∀ m, (x' m).left ≫ mp.φ = (x m).left) (m : ℕ) :
    cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)] =
      fun J => cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)] J ≫ mp.φ := by
  funext J
  let U : Over.mk ((jOG (𝟙 (Sp S)) d m 2).hom ≫ x0) ⟶ jOG x0 d m 2 :=
    Over.homMk (𝟙 _) (by simp)
  have key : ∀ i : Fin 2, pushPt mp.cart.1.w (jptG t' (𝟙 (Sp S)) d x' m i) = U ≫ jptG t x0 d x m i := fun i =>
    Over.OverMorphism.ext (by
      show ((homAt (𝟙 (Sp S)) (jetCopy d m i)).left ≫ (x' m).left) ≫ mp.φ =
        𝟙 _ ≫ (homAt x0 (jetCopy d m i)).left ≫ (x m).left
      rw [Category.id_comp, Category.assoc, hx]
      rfl)
  refine ((psum_push mp.cart
    ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)]
    ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)] U (fun i => ?_) J.down).trans
      (Category.id_comp _)).symm
  fin_cases i
  · exact key 0
  · exact key 1

theorem exists_frames_up : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (t' : SAB H (Sp S)) (mp : SABMap t' t x0) (w : LB.Iso t'.PP.L (t.PP.L.pull mp.φ)), RigIso mp w → ∀ (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp S)) d m 1 ⟶ t'.G), (∀ m, (x' m).left ≫ mp.φ = (x m).left) → ∀ e' : ∀ m, FrTyG t' (𝟙 (Sp S)) d x' m, (∀ m, (e' m).IsGen) → ∃ e : ∀ m, FrTyG t x0 d x m, (∀ m, (e m).IsGen) ∧ (∀ m, ∃ c₁ : LB.Gen (LB.LinComb t.PP.L (fun J => cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)] J ≫ mp.φ) (cε 2)), LB.Gen.Corr t.PP.L _ _ _ _ c₁ (e m) ∧ LB.Gen.Maps (LB.linCombIso w (cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)]) (cε 2)) (e' m) (flatGen t.PP.L mp.φ _ _ c₁)) := by
  intro E _ _ _ H X0 t S _ x0 t' mp w hw d x x' hx e' he'
  have main : ∀ m, ∃ e : FrTyG t x0 d x m, e.IsGen ∧
      ∃ c₁ : LB.Gen (LB.LinComb t.PP.L (fun J => cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2),
        jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)] J ≫ mp.φ) (cε 2)), LB.Gen.Corr t.PP.L _ _ _ _ c₁ e ∧
        LB.Gen.Maps (LB.linCombIso w (cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2),
          jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)]) (cε 2)) (e' m) (flatGen t.PP.L mp.φ _ _ c₁) := fun m => by
    obtain ⟨c₁, hc₁, hv⟩ := exists_up ((isGen_iff w).1 hw.1) t.PP.isLB t'.PP.isLB
      (φ' := cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)])
      (ε := cε 2) (e' m) (he' m)
    have gen : ∀ (ψ : ULift (Finset (Fin 2)) → ((jOG x0 d m 2).left ⟶ t.G.left))
        (c : LB.Gen (LB.LinComb t.PP.L ψ (cε 2))), c.IsGen →
        cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)] = ψ →
        ∃ e : FrTyG t x0 d x m, e.IsGen ∧ LB.Gen.Corr t.PP.L _ _ _ _ c e := by
      intro ψ c hc h
      subst h
      exact ⟨c, hc, ChartPrimTrPf.corr_self _ _ _ c⟩
    obtain ⟨e, he, hce⟩ := gen _ c₁ hc₁ (cube_points_push t x0 t' mp d x x' hx m)
    exact ⟨e, he, c₁, hce, ChartPrimTrPf.maps_flat w _ _ (e' m) c₁ hv⟩
  choose e he hc using main
  exact ⟨e, he, hc⟩

end GlobalTheory.Chart.FrameUp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsCubeFramesFromPullbackTripleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cubeFrames_from_pullback_triple : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (t' : SAB H (Sp S)) (mp : SABMap t' t x0) (w : LB.Iso t'.PP.L (t.PP.L.pull mp.φ)), RigIso mp w → ∀ (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp S)) d m 1 ⟶ t'.G), (∀ m, (x' m).left ≫ mp.φ = (x m).left) → ∀ e' : ∀ m, FrTyG t' (𝟙 (Sp S)) d x' m, (∀ m, (e' m).IsGen) → ∃ e : ∀ m, FrTyG t x0 d x m, (∀ m, (e m).IsGen) ∧ (∀ m, ∃ c₁ : LB.Gen (LB.LinComb t.PP.L (fun J => cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)] J ≫ mp.φ) (cε 2)), LB.Gen.Corr t.PP.L _ _ _ _ c₁ (e m) ∧ LB.Gen.Maps (LB.linCombIso w (cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)]) (cε 2)) (e' m) (flatGen t.PP.L mp.φ _ _ c₁)) := by
  first | exact @GlobalTheory.Chart.FrameUp.exists_frames_up | exact GlobalTheory.Chart.FrameUp.exists_frames_up | (intros; apply GlobalTheory.Chart.FrameUp.exists_frames_up <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.RigidifiedIsoMapsCubicalGenerator
section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.RigidifiedIsoMapsCubicalGenerator
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)
open TopologicalSpace Opposite Formalism.MainNotions.ModuliIntegralCharts.H1.ChartFrameTrA

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RigCub

theorem cover_of_isLB {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (x : X) : ∃ i, x ∈ L.U i := by
  have h : x ∈ (⨆ i, L.U i) := by rw [hL.cover]; trivial
  exact TopologicalSpace.Opens.mem_iSup.1 h

theorem div_cover {X : Scheme.{0}} {M L : LB X} (hM : M.IsLB) (hL : L.IsLB) (x : X) :
    ∃ p, x ∈ (LB.div M L).U p := by
  obtain ⟨i, hi⟩ := cover_of_isLB hM x
  obtain ⟨j, hj⟩ := cover_of_isLB hL x
  exact ⟨(i, j), hi, hj⟩

theorem unit_eq_one_of_local {X : Scheme.{0}} {κ : Type} (V : κ → X.Opens) (hcov : ∀ x : X, ∃ i, x ∈ V i)
    (v : Γ(X, ⊤)ˣ) (h : ∀ i, res (le_top : V i ≤ ⊤) v = 1) : v = 1 := by
  refine Units.ext ?_
  apply TopCat.Presheaf.section_ext X.sheaf ⊤
  intro x _
  obtain ⟨i, hi⟩ := hcov x
  have e1 := X.presheaf.germ_res_apply (homOfLE (le_top : V i ≤ ⊤)) x hi v.val
  have e3 : (X.presheaf.map (homOfLE (le_top : V i ≤ ⊤)).op).hom v.val = 1 := congrArg Units.val (h i)
  rw [e3, map_one] at e1
  exact e1.symm.trans (map_one _).symm

theorem linCombIso_punit {X Y : Scheme.{0}} {L M : LB X} (w : LB.Iso L M) (φ0 : Y ⟶ X)
    (p : (PUnit.{1} → M.ι) × (PUnit.{1} → L.ι)) :
    (LB.linCombIso w (K := PUnit.{1}) (fun _ => φ0) (fun _ => 1)).s p =
      res (le_inf (inf_le_left.trans (LB.wchart_le M (fun _ : PUnit.{1} => φ0) p.1 ⟨⟩))
        (inf_le_right.trans (LB.wchart_le L (fun _ : PUnit.{1} => φ0) p.2 ⟨⟩)))
        (pullU φ0 _ (w.s (p.1 ⟨⟩, p.2 ⟨⟩))) := by
  simp only [LB.linCombIso, zpow_one]
  exact Fintype.prod_subsingleton _ PUnit.unit

section Rig

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem rigIso_eq (hGF : GlobalFnsSt) {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S}
    (m : SABMap t' t f) (hab : IsAbelianScheme t'.G) {w w₀ : LB.Iso t'.PP.L (t.PP.L.pull m.φ)}
    (hw : RigIso m w) (hw₀ : w₀.IsGen)
    (hr₀ : LB.Gen.Maps (LB.linCombIso w₀ (K := PUnit.{1}) (fun _ => eSec t'.G) (fun _ => 1)) t'.PP.rig
      (m.cm.rigPull t.PP.L t.PP.rig)) : w = w₀ := by
  have hLp : (t.PP.L.pull m.φ).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB t.PP.L t.PP.isLB _ _
  obtain ⟨u, hu⟩ := exists_ratio_gen (div_cover hLp t'.PP.isLB) hw.1 hw₀
  suffices hu1 : u = 1 by
    cases w
    cases w₀
    congr 1
    funext p
    exact (hu p).trans (by rw [hu1, map_one, _root_.one_mul])
  apply unit_eq_one_of_eSec hGF t'.G hab u
  have hA : ((t'.PP.L).pull (eSec t'.G)).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB t'.PP.L t'.PP.isLB _ _
  have hB : ((t.PP.L.pull m.φ).pull (eSec t'.G)).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ hLp _ _
  have hloc : ∀ p : ((t.PP.L.pull m.φ).pull (eSec t'.G)).ι × ((t'.PP.L).pull (eSec t'.G)).ι,
      res (le_top : ((t.PP.L.pull m.φ).pull (eSec t'.G)).U p.1 ⊓ ((t'.PP.L).pull (eSec t'.G)).U p.2 ≤ ⊤)
        (pullU (eSec t'.G) ⊤ u : Γ((𝟙_ (Over S')).left, ⊤)ˣ) = 1 := by
    rintro ⟨p1, p2⟩
    have e3 := mul_right_cancel ((hw.2 (p1, p2)).symm.trans (hr₀ (p1, p2)))
    have e3' := (linCombIso_punit w (eSec t'.G) (p1, p2)).symm.trans (e3.trans (linCombIso_punit w₀ (eSec t'.G) (p1, p2)))
    have hu' : ∀ a b, w.s (a, b) = res le_top u * w₀.s (a, b) := fun a b => hu (a, b)
    rw [hu', map_mul] at e3'
    have e5 := mul_right_cancel (((map_mul _ _ _).symm.trans e3').trans (_root_.one_mul _).symm)
    rw [ReciprocityTheory.ChartRestriction.G.DVR.pullU_res] at e5
    exact (ReciprocityTheory.ChartRestriction.G.DVR.res_res' _ _ _).symm.trans e5
  have hv1 := unit_eq_one_of_local _ (fun y => by
      obtain ⟨p1, hp1⟩ := cover_of_isLB hB y
      obtain ⟨p2, hp2⟩ := cover_of_isLB hA y
      exact ⟨(p1, p2), hp1, hp2⟩) (pullU (eSec t'.G) ⊤ u : Γ((𝟙_ (Over S')).left, ⊤)ˣ) hloc
  exact congrArg Units.val hv1

end Rig

theorem rigIso_cub : GlobalFnsSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 X1 : Scheme.{0}) (t : SAB H X0) (t' : SAB H X1) (f : X1 ⟶ X0) (mp : SABMap t' t f) (w : LB.Iso t'.PP.L (t.PP.L.pull mp.φ)), RigIso mp w → IsAbelianScheme t'.G → LB.Gen.Maps (LB.linCombIso w (thφ t'.G (x3 t'.G)) thε) t'.cub.t (mp.cm.thetaPull t.PP.L t.cub.t) := by
  intro hGF E _ _ _ H X0 X1 t t' f mp w hw hab
  obtain ⟨w₀, h₀, h₁, h₂⟩ := mp.lin
  rw [rigIso_eq hGF mp hab hw h₀ h₁]
  exact h₂

end GlobalTheory.RigCub
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.RigidifiedIsoMapsCubicalGeneratorStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rigidifiedIso_maps_cubical_generator : GlobalFnsSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 X1 : Scheme.{0}) (t : SAB H X0) (t' : SAB H X1) (f : X1 ⟶ X0) (mp : SABMap t' t f) (w : LB.Iso t'.PP.L (t.PP.L.pull mp.φ)), RigIso mp w → IsAbelianScheme t'.G → LB.Gen.Maps (LB.linCombIso w (thφ t'.G (x3 t'.G)) thε) t'.cub.t (mp.cm.thetaPull t.PP.L t.cub.t) := by
  first | exact @GlobalTheory.RigCub.rigIso_cub | exact GlobalTheory.RigCub.rigIso_cub | (intros; apply GlobalTheory.RigCub.rigIso_cub <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IntegralFramesTransportToFramedPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

namespace GlobalTheory.FrameMove

theorem corr_trans {Z Y : Scheme.{0}} {L : LB Z} (hL : L.IsLB) {K K' K'' : Type} [Fintype K] [Fintype K'] [Fintype K'']
    {φ : K → (Y ⟶ Z)} {ε : K → ℤ} {φ' : K' → (Y ⟶ Z)} {ε' : K' → ℤ} {φ'' : K'' → (Y ⟶ Z)} {ε'' : K'' → ℤ}
    {a : LB.Gen (LB.LinComb L φ ε)} {b : LB.Gen (LB.LinComb L φ' ε')} {c : LB.Gen (LB.LinComb L φ'' ε'')}
    (h : LB.Gen.Corr L φ ε φ' ε' a b) (h' : LB.Gen.Corr L φ' ε' φ'' ε'' b c) : LB.Gen.Corr L φ ε φ'' ε'' a c :=
  corr_of_val hL fun _ _ hJ => (val_corr hJ h _).trans (val_corr hJ h' _)

theorem ad_const {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O] (B : Germ.FB R d O) (a : O) :
    MvPowerSeries.constantCoeff (B.ad a) = 1 := by
  have h := GlobalTheory.GaugeAdjoint.constantCoeff_ev (a := (![0, pt R d 0] : Fin 2 → Pt R 1 d)) (fun j i => by
    fin_cases j
    · simp
    · simp [pt]) (B.ad a)
  rw [B.adjoint_zero_fst a, map_one] at h
  exact h.symm

theorem isFrame_pull_iff {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}}
    (t : SAB H X0) {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (t' : SAB H (Sp S)) (mp : SABMap t' t x0)
    (w : LB.Iso t'.PP.L (t.PP.L.pull mp.φ)) (hw : RigIso mp w) (hab : IsAbelianScheme t'.G) (d : ℕ)
    (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp S)) d m 1 ⟶ t'.G)
    (hx : ∀ m, (x' m).left ≫ mp.φ = (x m).left)
    (e : ∀ m, FrTyG t x0 d x m) (e' : ∀ m, FrTyG t' (𝟙 (Sp S)) d x' m) (he : ∀ m, (e m).IsGen)
    (he' : ∀ m, (e' m).IsGen)
    (tie : ∀ m, ∃ c₁ : LB.Gen (LB.LinComb t.PP.L (fun J => cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2),
        jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)] J ≫ mp.φ) (cε 2)),
      LB.Gen.Corr t.PP.L _ _ _ _ c₁ (e m) ∧
      LB.Gen.Maps (LB.linCombIso w (cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2),
        jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)]) (cε 2)) (e' m) (flatGen t.PP.L mp.φ _ _ c₁))
    (F : Fin d → PS S 2 d) (act : 𝓞 E → Fin d → PS S 1 d) (ph1 ph2 : PS S 3 d) (sy : PS S 2 d)
    (ad : 𝓞 E → PS S 2 d) (hF : ∀ j, MvPowerSeries.constantCoeff (F j) = 0)
    (hact : ∀ b j, MvPowerSeries.constantCoeff (act b j) = 0) (had : ∀ a, MvPowerSeries.constantCoeff (ad a) = 1)
    (h0 : homAt (𝟙 (Sp S)) (jetAug : Jet S (Fin 1 × Fin d) 0 →ₐ[S] S) ≫ x' 0 = 1)
    (hl : ∀ m, homAt (𝟙 (Sp S)) (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (F p.2)) ≫ x' m =
      jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2) * jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2))
    (ha : ∀ m (b : 𝓞 E), x' m ≫ t'.act.act b =
      homAt (𝟙 (Sp S)) (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (act b p.2)) ≫ x' m) :
    IsFrameG t x0 d x F act ph1 ph2 sy ad e ↔ IsFrameG t' (𝟙 (Sp S)) d x' F act ph1 ph2 sy ad e' := by
  have laws : Laws := GlobalTheory.firstFiveLaws.1
  have cub := GlobalTheory.T.rigidifiedIso_maps_cubical_generator laws.globalFns E H X0 (Sp S) t t' x0 mp w hw hab
  have p1 := GlobalTheory.T.frame_firstPartialLaw_iff_pullback E H X0 t S x0 t' mp w hw d x x' hx cub e e' he he' tie F ph1
  have p2 := GlobalTheory.T.frame_second_partial_law_iff_pullback_alt E H X0 t S x0 t' mp w hw d x x' hx cub e e' he he' tie F ph2
  have p3 := GlobalTheory.T.frame_symmetry_iff_pullback E H X0 t S x0 t' mp w hw d x x' hx e e' he he' tie sy
  constructor
  · intro h
    refine ⟨he', ?_, ?_, p3.1 h.sy, fun a =>
      GlobalTheory.T.adjointSeries_frames_pullback E H X0 t S x0 t' mp w hw d x x' hx e e' he he' tie act ad a hact ha (h.ad a)⟩
    · first | exact (p1 hF hl).1 h.ph1 | exact p1.1 fun _ _ => h.ph1
    · first | exact (p2 hF hl).1 h.ph2 | exact p2.1 fun _ _ => h.ph2
  · intro h
    refine ⟨he, ?_, ?_, p3.2 h.sy, fun a =>
      GlobalTheory.T.frame_adjointness_series_of_pullback laws E H X0 t S x0 t' mp w hw d x x' hx hab h0 e e' he he' tie act ad a ha hact (had a) (h.ad a)⟩
    · first | exact (p1 hF hl).2 h.ph1 | exact p1.2 h.ph1 hF hl
    · first | exact (p2 hF hl).2 h.ph2 | exact p2.2 h.ph2 hF hl

end GlobalTheory.FrameMove


open GlobalTheory.FrameMove in
set_option maxHeartbeats 1000000 in
theorem GlobalTheory.chartFrameTransport : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], ChartFrameTrSt Xo c := by
  intro E _ _ _ H Dw l Xo c _ _ T io y I d B B' tgT xT eT wPT hF hA h1 h2 hs had hch hfr hpr _ hrig
  letI := io.toAlgebra
  intro x x' hx2 hx1
  obtain ⟨wP, hwP, wP', hwP', tw2, tw1⟩ := GlobalTheory.T.integralFramedPoint_diagonalBiextensionIso_compatible E H Dw l Xo c T io y I wPT hpr
  have hab : IsAbelianScheme I.t'.G := GlobalTheory.T.isAbelianScheme_pullback_universalTriple E H Dw l Xo _ I.t' _ I.m1
  let ψ : T.V →+* T.Fr := algebraMap T.V T.Fr
  have hb : spMap ψ = spMap ψ ≫ 𝟙 (Sp T.V) := (Category.comp_id _).symm
  obtain ⟨x'', hx''⟩ : ∃ x'' : ∀ m, jOG (spMap ψ) d m 1 ⟶ I.G.G, ∀ m, (x' m).left ≫ I.m2.φ = (x'' m).left :=
    ⟨fun m => Over.homMk ((x' m).left ≫ I.m2.φ) (by
      have h := Over.w (x' m)
      rw [Category.assoc, I.m2.cart.1.w, ← Category.assoc, h]
      simp [ψ]), fun m => rfl⟩
  have hx3 : ∀ m, (x'' m).left = spMap (jetCoef ψ (Fin 1 × Fin d) m) ≫ (xT m).left :=
    fun m => (hx'' m).symm.trans (hx2 m)
  have eF : B'.G.F = fun i => MvPowerSeries.map ψ (B.G.F i) := funext hF
  have eA : B'.A.act = fun a i => MvPowerSeries.map ψ (B.A.act a i) := funext fun a => funext (hA a)
  have ead : B'.ad = fun a => MvPowerSeries.map ψ (B.ad a) := funext had

  obtain ⟨e'', he'', hc''⟩ := GlobalTheory.T.exists_frames_coefficientRing_baseChange E H _ I.G T.V T.Fr ψ _ _ hb d xT x'' hx3 eT hfr.gen
  have fr'' : IsFrameG I.G (spMap ψ) d x'' B'.G.F B'.A.act B'.ph1 B'.ph2 B'.sy B'.ad e'' := by
    rw [eF, eA, ead, h1, h2, hs]
    exact GlobalTheory.T.isFrameG_coefficientRing_baseChange E H _ I.G T.V T.Fr ψ _ _ hb d xT x'' hx3 eT e'' hfr.gen he'' hc'' _ _ _ _ _ _ hfr
  have rig'' : Rig0G I.G (spMap ψ) d x'' B'.A.act e'' wPT := by
    rw [eA]
    exact GlobalTheory.T.rigidificationAtOrigin_baseChange_alt E H _ I.G T.V T.Fr ψ _ _ hb d xT x'' hx3 eT e'' hfr.gen he'' hc'' _ wPT hpr.1 hrig
  obtain ⟨z'', l'', a''⟩ := GlobalTheory.T.jetPoints_unit_law_action_baseChange E H _ I.G T.V T.Fr ψ _ _ hb d xT x'' hx3

  obtain ⟨z', l', a'⟩ := GlobalTheory.T.jetPoints_unit_law_action_iff_pullback E H _ I.G T.Fr _ I.t' I.m2 I.w2 I.rig2 d x'' x' hx''
  have h0 := z'.1 (z'' hch.zero) 0
  have hl := (l' B'.G.F).1 (by rw [eF]; exact l'' _ B.G.const hch.law)
  have ha := (a' B'.A.act).1 (by rw [eA]; exact a'' _ B.A.const hch.act)
  obtain ⟨e', he', tie2⟩ := GlobalTheory.T.cubeFrames_move_to_pullback_triple E H _ I.G T.Fr _ I.t' I.m2 I.w2 I.rig2 d x'' x' hx'' e'' he''
  have fr' := (isFrame_pull_iff I.G _ I.t' I.m2 I.w2 I.rig2 hab d x'' x' hx'' e'' e' he'' he' tie2 _ _ _ _ _ _
    B'.G.const B'.A.const (ad_const B') h0 hl ha).1 fr''
  have rig' := (GlobalTheory.T.rigidificationAtOrigin_iff_pullback E H _ I.G T.Fr _ I.t' I.m2 I.w2 I.rig2 d x'' x' hx'' e'' e' he'' he' tie2 wPT wP' hpr.1
    hwP' tw2 _ h0 B'.A.const).1 rig''

  obtain ⟨e, he, tie1⟩ := GlobalTheory.T.exists_cubeFrames_from_pullback_triple E H _ Xo.univ.t T.Fr _ I.t' I.m1 I.w1 I.rig1 d x x' hx1 e' he'
  have fr := (isFrame_pull_iff Xo.univ.t _ I.t' I.m1 I.w1 I.rig1 hab d x x' hx1 e e' he he' tie1 _ _ _ _ _ _
    B'.G.const B'.A.const (ad_const B') h0 hl ha).2 fr'
  have rig := (GlobalTheory.T.rigidificationAtOrigin_iff_pullback E H _ Xo.univ.t T.Fr _ I.t' I.m1 I.w1 I.rig1 d x x' hx1 e e' he he' tie1 wP wP'
    ((isPrim_iff wP).1 hwP).1 hwP' tw1 _ h0 B'.A.const).2 rig'
  refine ⟨e, wP, (isFrame_iff y.1 d x _ _ _ _ _ _ e).2 fr, hwP, rig, ⟨e', fun m => ⟨he' m, ?_, tie1 m⟩⟩,
    wP', hwP', tw2, tw1⟩
  obtain ⟨c₂, k₁, k₂⟩ := tie2 m
  exact ⟨c₂, corr_trans I.G.PP.isLB k₁ (hc'' m), k₂⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IntegralFramesTransportToFramedPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_frames_transport_to_framed_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], ChartFrameTrSt Xo c := by
  first | exact @GlobalTheory.chartFrameTransport | exact GlobalTheory.chartFrameTransport | (intros; apply GlobalTheory.chartFrameTransport <;> assumption)
end
