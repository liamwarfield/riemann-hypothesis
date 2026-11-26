module

public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsTripleOfAbelianModelDedekind
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SemiAbelianHomExtensionDvr
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicDegenerationArcOfUniformisation
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsFgForallOverLbIso
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CoeffMapDomainMul
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CrossRelationGivesConvolutionRelation

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory

attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.firstFiveLaws : _root_.GlobalTheory.UT.LL := by
  unfold _root_.GlobalTheory.UT.LL
  obtain ⟨h₁, h₂, h₃, h₄, h₅, -⟩ := _root_.GlobalTheory.allSixLaws
  exact ⟨h₁, h₂, h₃, h₄, h₅⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHoldStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.all_uniformization_laws_hold : LL := by
  first | exact @GlobalTheory.firstFiveLaws | exact GlobalTheory.firstFiveLaws | (intros; apply GlobalTheory.firstFiveLaws <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UTorsClosed
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH

theorem uTors_closed : GlobalTheory.ZH.UTorsSt :=
  GlobalTheory.T.uniformisation_torsion_eq_of_laws GlobalTheory.T.all_six_abelian_scheme_laws_hold.1 GlobalTheory.T.all_six_abelian_scheme_laws_hold.2.1 GlobalTheory.T.all_six_abelian_scheme_laws_hold.2.2.1 GlobalTheory.T.all_six_abelian_scheme_laws_hold.2.2.2.1 GlobalTheory.T.all_six_abelian_scheme_laws_hold.2.2.2.2.1

end GlobalTheory.ZH
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCmEllipticCurveWithPeriod
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCmEllipticCurveWithPeriod
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane

namespace GlobalTheory

theorem _root_.GlobalTheory.cmCurve_closed : _root_.GlobalTheory.CMCurve :=
  _root_.GlobalTheory.cmCurve_of_uniformisation _root_.GlobalTheory.thetaUnifAV_all
    _root_.GlobalTheory.polBaseChange_holds _root_.GlobalTheory.homExtension_semiAbelian_dvr_unconditional

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCmEllipticCurveWithPeriodStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cmEllipticCurve_withPeriod : CMCurve := by
  first | exact @GlobalTheory.cmCurve_closed | exact GlobalTheory.cmCurve_closed | (intros; apply GlobalTheory.cmCurve_closed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ArcClauseClosed
namespace GlobalTheory

theorem arcClause_closed : ReciprocityTheory.ChartRestriction.G.Geo.Tor.ToroidalArchimedeanCondition :=
  GlobalTheory.T.holomorphic_degenerationArc_of_uniformisation GlobalTheory.T.abelianScheme_laws_unconditional.1 GlobalTheory.T.abelianScheme_laws_unconditional.2 GlobalTheory.T.thetaUniformisation_complexAbelianVariety

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SixthLawsAndUnifUniq
open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory

theorem sixthLaws_and_unifUniq : Laws6 ∧ UnifUniqSt :=
  ⟨GlobalTheory.allSixLaws.2.2.2.2.2, GlobalTheory.allSixLaws.2.2.2.2.2.unifUniq⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CmPointClosed
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PureType
open scoped CategoryTheory.Obj

namespace GlobalTheory

private theorem weil_pairing_properties : _root_.ReciprocityTheory.ChartRestriction.G.Out.WeilSt :=
  (_root_.GlobalTheory.AbLaw.FromCube.all_of_cubeGen
    (fun S P M a ↦ _root_.GlobalTheory.AbLaw.CubeAssembly.cube_gen S P M a)).2.2.2.2.1

theorem _root_.GlobalTheory.cmPoint_closed : _root_.GlobalTheory.CMPoint :=
  _root_.GlobalTheory.cmPoint _root_.GlobalTheory.thetaUnifAV_all weil_pairing_properties

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionPointEndomorphismImageEqMovedGtPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionPointEndomorphismImageEqMovedGtPoint
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.EndTors
open GlobalTheory.TorusExt GlobalTheory.UT.CoefBasic

attribute [local instance] gtGroup

theorem eq_zero_of_sumV_zero {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) {Ix : Type} {c : F}
    (h : SumV v (0 : Ix → F) c) : c = 0 := by
  by_contra hc
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 (mt (AddValuation.top_iff v).1 hc)
  obtain ⟨S, hS⟩ := h (r + 1)
  have := hS S le_rfl
  simp only [Pi.zero_apply, Finset.sum_const_zero, sub_zero, ← hr, WithTop.coe_le_coe] at this
  linarith

theorem sumV_equiv {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) {Ix Ix' : Type} (e : Ix ≃ Ix') {x : Ix → F}
    {x' : Ix' → F} (hx : ∀ i, x i = x' (e i)) {c : F} (h : SumV v x c) : SumV v x' c := by
  intro q
  obtain ⟨S, hS⟩ := h q
  refine ⟨S.map e.toEmbedding, fun T hT => ?_⟩
  have := hS (T.map e.symm.toEmbedding) fun i hi => Finset.mem_map.2
    ⟨e i, hT (Finset.mem_map.2 ⟨i, hi, rfl⟩), e.symm_apply_apply i⟩
  rw [Finset.sum_map] at this
  simpa only [hx, Equiv.toEmbedding_apply, Equiv.apply_symm_apply] using this

theorem sumV_shift {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) {X : Type} [AddCommGroup X] (h : X →+ X)
    (y y' : X) {B₁ B₂ C₁ C₂ b₁ b₂ c₁ c₂ : X → F} (hB₁ : ∀ α, B₁ (α + y) = b₁ α) (hB₂ : ∀ α, B₂ (α + y) = b₂ α)
    (hC₁ : ∀ α, C₁ (α + y') = c₁ α) (hC₂ : ∀ α, C₂ (α + y') = c₂ α)
    (H : ∀ α, SumV v (fun p : {p : X × X // h p.1 + p.2 = α} => b₁ p.1.1 * c₂ p.1.2 - b₂ p.1.1 * c₁ p.1.2) 0) (α : X) :
    SumV v (fun p : {p : X × X // h p.1 + p.2 = α} => B₁ p.1.1 * C₂ p.1.2 - B₂ p.1.1 * C₁ p.1.2) 0 := by
  refine sumV_equiv v (Equiv.subtypeEquiv ((Equiv.addRight y).prodCongr (Equiv.addRight y')) fun p => ?_) (fun p => ?_)
    (H (α - h y - y'))
  · simp only [Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, Equiv.coe_addRight, map_add (f := _)]
    constructor
    · intro e; rw [show α = α - h y - y' + h y + y' by abel, ← e]; abel
    · intro e; rw [← e]; abel
  · simp only [Equiv.subtypeEquiv_apply, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, Equiv.coe_addRight,
      hB₁, hB₂, hC₁, hC₂]

section
variable {R : Type} [CommRing R] [IsDomain R] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem val_rigT (ρ : LB.Gen (A.L.pull (eSec A.A))) (k : ℤ) {z : (TFK (R := R) F).left} {J} (hJ : Good A.L z J) :
    val (rigT A.A A.L ρ (TFK (R := R) F) k) (𝟙 _) z J =
      val (L := A.L) (φ := fun _ : PUnit => eSec A.A) (ε := fun _ => 1) ρ (𝟙 _ ≫ (TFK (R := R) F).hom) z J ^ k := by
  have hm := hJ.mem (fun _ : Fin 1 => (TFK (R := R) F).hom ≫ eSec A.A) (𝟙 _)
  refine (map_zpow _ _ _).trans (congrArg (· ^ k) ((gm_res _ z _ hm _).trans ?_))
  exact gm_pull (𝟙 _) (TFK (R := R) F).hom z _ (rigT_le A.A A.L _ hm) _

theorem exists_value {ρ : LB.Gen (A.L.pull (eSec A.A))} (hρ : ρ.IsGen) {k : ℕ} (t : SecA A F k) :
    ∃ c : F, ∀ z J, Good A.L z J → sA t (ptSecT A.A 1).left z J =
      @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z c) *
        (val (rigT A.A A.L ρ (TFK (R := R) F) (k : ℤ)) (𝟙 _) z J).val := by
  obtain ⟨z⟩ := exists_pt (R := R) (F := F)
  obtain ⟨J', hJ'⟩ := exists_good' (Z := (TFK (R := R) F).left) A.isLB z
  obtain ⟨c, hc⟩ := cstH_surj z (sA t (ptSecT A.A 1).left z J' *
    ((val (rigT A.A A.L ρ (TFK (R := R) F) (k : ℤ)) (𝟙 _) z J')⁻¹).val :)
  refine ⟨c, fun z' J hJ => ?_⟩
  obtain rfl := CoefBasic.pt_eq z z'
  have a₁ := sval_tr (L := A.L) (φ := fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left) (ε := fun _ => (k : ℤ)) t
    (ptSecT A.A 1).left hJ hJ'
  have a₂ := val_tr (L := A.L) (φ := fun _ : PUnit => eSec A.A) (ε := fun _ => 1) hρ
    (𝟙 _ ≫ (TFK (R := R) F).hom) hJ hJ'
  have e : (ptSecT A.A (1 : TFK (R := R) F ⟶ A.A)).left ≫ (snd (TFK (R := R) F) A.A).left =
      (𝟙 _ ≫ (TFK (R := R) F).hom) ≫ eSec A.A := by
    rw [← Over.comp_left, ptSecT, lift_snd, Category.id_comp]; rfl
  rw [Fin.prod_univ_one, e] at a₁
  rw [Fintype.prod_unique, zpow_one] at a₂
  have hc' : @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z c) = sA t (ptSecT A.A 1).left z J' *
    ((val (rigT A.A A.L ρ (TFK (R := R) F) (k : ℤ)) (𝟙 _) z J')⁻¹).val := (cst_eq z c).trans hc
  rw [hc', val_rigT ρ k hJ, val_rigT ρ k hJ', a₂, mul_zpow, Units.val_mul, mul_comm (Units.val (_ ^ _)),
    ← _root_.mul_assoc, Units.inv_mul_cancel_right, mul_comm]
  exact a₁

theorem exists_act_pre (hG : GlobalFnsSt) {k : ℕ} (θ : ThetaGrp A.A A.L (k : ℤ) (TFK (R := R) F)) (T : SecA A F k) :
    ∃ t : SecA A F k, IsActOf A.A A.L (k : ℤ) θ t T := by
  obtain ⟨ρ, hρ, -⟩ := GlobalTheory.thetaGrp_acts_linearly hG _ A (k : ℤ) (TFK (R := R) F)
  exact ⟨SecM.toSec A.A ((ρ θ).symm (SecM.ofSec A.A T)), (hρ _ _ _).2 ((ρ θ).apply_symm_apply _)⟩

theorem act_zero {I : Ideal R} {D : DegData R I} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
    {U : UnifPre I D A G} (E : EndU U) {o : GtPtF D.toPre F} (ho : o.IsZero) : E.Act o o := by
  obtain ⟨hb, hv⟩ := (isZero_iff o).1 ho
  have := E.homB
  refine ⟨by rw [hb, MonObj.one_comp], fun χ z J hJ => ?_⟩
  have a := val_corr hJ (E.u_norm χ).2 (TF (R := R) F).hom
  rw [val_pull hJ, val_one] at a
  rw [hv _ z J hJ, hv _ z J hJ, hb, _root_.one_mul]
  exact a.symm

end

theorem exists_pre_coef (hL : LL) {R : Type} [CommRing R] [IsDomain R] [CharZero R] {I : Ideal R} (hA : AdmBase R I)
    {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))}
    [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (U : Unif I D A G) {F : Type} [Field F] [IsAlgClosed F]
    [Algebra (FractionRing R) F] {j : ℕ} (hj : 1 ≤ j) (q : QkPt D.toPre F j) {x : TFK (R := R) F ⟶ A.A}
    (hx : QkToAkU U.toUnifPre F j q x) {w₀ : W0 U.toUnifPre} (hw₀ : w₀.IsGen) {g₀ g₁ : GtPtF D.toPre F}
    (hg : g₀.IsAdd q.g g₁) {ω₀ : Frm D.toPre F j g₀.b} (hω₀ : ω₀.IsGen) :
    ∃ θ : ThetaGrp A.A A.L (j : ℤ) (TFK (R := R) F), θ.pt = x ∧ ∃ ω₁ : Frm D.toPre F j g₁.b, ω₁.IsGen ∧
      ∀ T S, U.ExpandsF F j w₀ T S → ∃ t s, IsActOf A.A A.L (j : ℤ) θ t T ∧ U.ExpandsF F j w₀ t s ∧
        ∀ α, coef S g₀ ω₀ (α + q.y) = coef s g₁ ω₁ α := by
  obtain ⟨hp, hθ⟩ := hx w₀ hw₀
  obtain ⟨θ, e, -⟩ := GlobalTheory.TorsionTheta.exists_theta_acts hL.1.kerPow _ A F (jFK (R := R) F) j hj x hp
  obtain ⟨w, hw, H⟩ := hθ θ e
  obtain ⟨ω₁, hω₁, -, K⟩ := GlobalTheory.UT.CoefPhi.coef_phi hL R I hA D F j hj q w hw g₀ g₁ hg ω₀ hω₀
  refine ⟨θ, e, ω₁, hω₁, fun T S hT => ?_⟩
  obtain ⟨t, ht⟩ := exists_act_pre hL.1.globalFns θ T
  obtain ⟨s, hs, -⟩ := ((expBijF_and_expandsF_lin hL R I hA D A G hG U).1 F j hj w₀ hw₀).1 t
  exact ⟨t, s, ht, hs, K 1 j le_rfl (Nat.mul_one j).symm q (one_nsmul _).symm rfl w ω₀ ω₁
    ⟨hw, fun _ _ _ => (pow_one _).symm⟩ ⟨hω₀, fun _ _ _ => (pow_one _).symm⟩ ⟨hω₁, fun _ _ _ => (pow_one _).symm⟩
    s S (H t T s S hs hT ht)⟩

theorem main : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ E : EndU U.toUnifPre, Function.Injective E.h → ∀ (k : ℕ), 1 ≤ k → ∀ (p : QkPt D.toPre F k) x, QkToAkU U.toUnifPre F k p x → ∀ g', E.Act p.g g' → ∃ p' : QkPt D.toPre F k, p'.g = g' ∧ QkToAkU U.toUnifPre F k p' (x ≫ E.aA) := by
  intro hL h₁ h₂ h₃ h₄ V _ _ _ _ hV ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U E hE k hk p x hx g' hg'
  have hA : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hV⟩
  have hB := D.tau_bimult
  have := E.homA
  have CV := GlobalTheory.UT.CoefVal.main hL h₁ h₂ h₃ h₄ V hV ϖ hϖ D Q hQ F v hv
  have EV := GlobalTheory.UT.EvalZero.value_at_origin hL V _ hA D A G hG U F
  have LU := GlobalTheory.T.uniformisation_torsion_maps_compatible_in_level hL V _ hA D A G hG U F
  have MX := GlobalTheory.T.crossRelation_gives_convolution_relation hL V _ hA D A G hG U F E
  have BJ := (expBijF_and_expandsF_lin hL V _ hA D A G hG U).1 F
  have SV := fun Ix => AdicValSum.main V ϖ hϖ F v hv Ix
  obtain ⟨f, f₁, f₂, f₃, -⟩ := GlobalTheory.TorsionIso.torsion_eq hL V _ hA D A G hG U F k hk
  obtain ⟨ρ, hρ⟩ := EV.1
  obtain ⟨w₀, hN⟩ := EV.2.1 ρ hρ
  have hw₀ := hN.1
  have hxk : x ^ k = 1 := (hx w₀ hw₀).1
  obtain ⟨p₀, hp₀⟩ := f₂ (x ≫ E.aA) (by rw [← MonObj.pow_comp, hxk, MonObj.one_comp])
  obtain ⟨l', hl', -⟩ := (CV g').1
  obtain ⟨z, hz⟩ := GlobalTheory.exists_rep_mod_shifted_form_small D.toPre.X Q (QForm.bHom hϖ D hQ)
    (fun a b => by rw [QForm.bHom_apply, QForm.bOf]; ring) (QForm.two_Q_eq hϖ D hQ)
    (fun a ha => QForm.Q_pos hϖ D hQ ha) (k • l') k hk p₀.y
  let p₁ : QkPt D.toPre F k := qkMk hB (p₀.y + k • z) (p₀.g + iota hB F z)
    (by rw [nsmul_add, qk_nsmul hB, map_add (f := _), map_nsmul])
  have hp₁ : QkToAkU U.toUnifPre F k p₁ (x ≫ E.aA) :=
    (f₁ _ _).2 (hp₀.symm.trans ((f₃ _ _).2 ((equiv_iff hB _ _).2 ⟨z, rfl, rfl⟩)))
  let d : GtPtF D.toPre F := g' - p₁.g
  have hd : d.IsAdd p₁.g g' := (isAdd_iff_eq _ _ _).2 (sub_add_cancel _ _).symm
  obtain ⟨l, hl, -⟩ := (CV d).1
  obtain ⟨l₁, hl₁, -⟩ := (CV p₁.g).1
  have ho : (0 : GtPtF D.toPre F).IsZero := (isZero_iff_eq _).2 rfl
  suffices H : d.IsZero from ⟨p₁, (sub_eq_zero.1 ((isZero_iff_eq _).1 H)).symm, hp₁⟩
  have gu : ∀ (g : GtPtF D.toPre F) (a b : D.toPre.X →+ ℚ), GtV hϖ hv g a → GtV hϖ hv g b → a = b := fun g a b ha hb =>
    (CV g).1.unique ha hb
  have k0 : (0 : ℚ) < k := by exact_mod_cast hk
  refine GlobalTheory.T.smallTorusPoint_keeping_ratios_isZero hL h₁ h₂ h₃ h₄ V hV ϖ hϖ D Q hQ F v hv k hk d 0 l ho hl (fun m => ?_) fun n j hn hj w₁ hw₁ => ?_
  · have e₁ := gu g' l' (l + l₁) hl' ((CV d).2.2.2.1 p₁.g g' l l₁ hd hl hl₁)
    have e₂ := gu p₁.g l₁ ((k : ℚ)⁻¹ • (Int.castAddHom ℚ).comp (QForm.bHom hϖ D hQ p₁.y)) hl₁ (by
      have := (CV p₁.g).2.2.2.2.1 k hk p₁
      convert this using 2 with χ
      simp [QForm.bHom_apply, div_eq_inv_mul])
    have e₃ := hz m
    have e₄ : ((QForm.bHom hϖ D hQ (p₀.y + k • z) m : ℤ) : ℚ) - (k • l') m = -(k * l m) := by
      rw [e₁, e₂]
      simp only [AddMonoidHom.smul_apply, AddMonoidHom.add_apply, AddMonoidHom.comp_apply, Int.coe_castAddHom,
        smul_eq_mul, nsmul_eq_mul]
      simp only [p₁, qkMk_y]
      show _ - (k : ℚ) * (l m + (k : ℚ)⁻¹ * ((QForm.bHom hϖ D hQ (p₀.y + k • z) m : ℤ) : ℚ)) = _
      field_simp
      ring
    rw [e₄, abs_neg, abs_mul, abs_of_pos k0] at e₃
    exact le_of_mul_le_mul_left e₃ k0
  have up : ∀ (r : QkPt D.toPre F k) (n N : ℕ), N = k * n → ∃ q : QkPt D.toPre F N, q.y = n • r.y ∧ q.g = r.g :=
    fun r n N h => ⟨qkMk hB (n • r.y) r.g (by rw [h, mul_nsmul, qk_nsmul hB, map_nsmul]), rfl, rfl⟩
  have hj1 : 1 ≤ j := hj ▸ Nat.mul_pos hk hn
  obtain ⟨q₁, qy₁, qg₁⟩ := up p₁ n j hj
  obtain ⟨w, hw⟩ := (coef_basic V D.toPre F j d).1
  obtain ⟨θ, hθ, ω, hω, K⟩ := exists_pre_coef hL hA hG U hj1 q₁ (((LU k n j hk hn hj p₁ q₁ _).1 qy₁ qg₁).1 hp₁) hw₀
    (qg₁ ▸ hd) hw
  refine ⟨w, hw, fun S₁ S₂ hS => ?_⟩
  obtain ⟨T₁, hT₁, -⟩ := (BJ j hj1 w₀ hw₀).2 S₁
  obtain ⟨T₂, hT₂, -⟩ := (BJ j hj1 w₀ hw₀).2 S₂
  obtain ⟨n', hn', CR⟩ := GlobalTheory.PullPair.exists_cross hL V A F E.aA E.homA j k hk
  obtain ⟨T₁', T₂', hC, hne⟩ := CR T₁ T₂
  have hj' : 1 ≤ k * n' := Nat.mul_pos hk hn'
  obtain ⟨S₁', hT₁', -⟩ := (BJ _ hj' w₀ hw₀).1 T₁'
  obtain ⟨S₂', hT₂', -⟩ := (BJ _ hj' w₀ hw₀).1 T₂'
  obtain ⟨w₁', hw₁'⟩ := (coef_basic V D.toPre F (k * n') 0).2.1 zero_b
  obtain ⟨q, qy, qg⟩ := up p n' _ rfl
  obtain ⟨θ', hθ', ω', hω', K'⟩ := exists_pre_coef hL hA hG U hj' q (((LU k n' _ hk hn' rfl p q _).1 qy qg).1 hx) hw₀
    (g₀ := 0) (g₁ := p.g) ((isAdd_iff_eq _ _ _).2 (by rw [qg, zero_add])) hw₁'.1
  obtain ⟨t₁, s₁, a₁, e₁, c₁⟩ := K T₁ S₁ hT₁
  obtain ⟨t₂, s₂, a₂, e₂, c₂⟩ := K T₂ S₂ hT₂
  obtain ⟨t₁', s₁', a₁', e₁', c₁'⟩ := K' T₁' S₁' hT₁'
  obtain ⟨t₂', s₂', a₂', e₂', c₂'⟩ := K' T₂' S₂' hT₂'
  have hC' := (GlobalTheory.cross_iff_of_isActOf hL V A F E.aA E.homA j _ θ θ' (by rw [hθ, hθ']) _ _ _ _ _ _ _ _
    a₁ a₂ a₁' a₂').2 hC
  have nl : ∀ (g : GtPtF D.toPre F) (i : ℕ), 1 ≤ i → ∀ (u : Frm D.toPre F i g.b) (s : Fam D.toPre F i), u.IsGen →
      NullV v (coef s g u) := fun g i hi u s hu => ((CV g).2.2.2.2.2.2 i hi u s hu).1
  refine GlobalTheory.UT.sumV_cancel F v D.toPre.X E.h hE (coef S₁ 0 w₁) (coef S₂ 0 w₁) (coef S₁ d w) (coef S₂ d w)
    (coef S₁' 0 w₁') (coef S₂' 0 w₁') (nl _ _ hj1 _ _ hw₁.1) (nl _ _ hj1 _ _ hw₁.1) (nl _ _ hj1 _ _ hw)
    (nl _ _ hj1 _ _ hw) (nl _ _ hj' _ _ hw₁'.1) (nl _ _ hj' _ _ hw₁'.1)
    (fun α => (SV _ _ _ (MX w₀ hw₀ j _ hj1 hj' _ _ _ _ _ _ _ _ hT₁ hT₂ hT₁' hT₂' hC 0 0 (act_zero E ho) w₁ w₁'
      hw₁.1 hw₁'.1 α)).1)
    (sumV_shift v E.h q₁.y q.y c₁ c₂ c₁' c₂' fun α => (SV _ _ _ (MX w₀ hw₀ j _ hj1 hj' _ _ _ _ _ _ _ _ e₁ e₂ e₁' e₂'
      hC' p.g g' hg' ω ω' hω hω' α)).1) fun h0 => ?_
  obtain ⟨c, hc⟩ := exists_value hρ T₂
  obtain ⟨c', hc'⟩ := exists_value hρ T₂'
  have σ := (SV _ _ _ (EV.2.2 w₀ ρ hN j T₂ S₂ hT₂ 0 w₁ ho hw₁ c hc)).1
  have σ' := (SV _ _ _ (EV.2.2 w₀ ρ hN _ T₂' S₂' hT₂' 0 w₁' ho hw₁' c' hc')).1
  rw [h0] at σ'
  obtain rfl := eq_zero_of_sumV_zero v σ'
  obtain ⟨y⟩ := exists_pt (R := V) (F := F)
  obtain ⟨J, hJ⟩ := exists_good' (Z := (TFK (R := V) F).left) A.isLB y
  refine hne (fun y J hJ h => hS ?_) y J hJ ((hc' y J hJ).trans ?_)
  · have e : cstH (R := V) y c = 0 :=
      (cst_eq y c).symm.trans ((Units.mul_left_eq_zero _).1 ((hc y J hJ).symm.trans h))
    obtain rfl : c = 0 := cstH_inj y (e.trans (map_zero _).symm)
    exact σ
  · exact mul_eq_zero_of_left ((cst_eq y 0).trans (map_zero _)) _

end GlobalTheory.UT.EndTors
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionPointEndomorphismImageEqMovedGtPointStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionPoint_endomorphism_image_eq_moved_gtPoint : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ E : EndU U.toUnifPre, Function.Injective E.h → ∀ (k : ℕ), 1 ≤ k → ∀ (p : QkPt D.toPre F k) x, QkToAkU U.toUnifPre F k p x → ∀ g', E.Act p.g g' → ∃ p' : QkPt D.toPre F k, p'.g = g' ∧ QkToAkU U.toUnifPre F k p' (x ≫ E.aA) := by
  first | exact @GlobalTheory.UT.EndTors.main | exact GlobalTheory.UT.EndTors.main | (intros; apply GlobalTheory.UT.EndTors.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPointRepresentingWeightMumfordQuotient
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsWeightBundleTorusQuotientTowerAlgebraisati
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsWeightBundleTorusQuotientTowerAlgebraisati
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.WtTower

variable {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {A : PolAV (Spec (CommRingCat.of (FractionRing V)))}
  {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G] {s : HidaSetting V A G}

theorem exists_levels (t : Tower s) (χ : s.X) : ∃ (N : ∀ e, LB (t.l e).Q.B.left)
    (u : ∀ e, LB.Gen ((N e).pull (t.l e).Q.q.left)),
    ∀ e, (N e).IsLB ∧ (t.l e).Q.GenWt (N e) (u e) χ ∧ Triv (abelian₂ (t.l e).Q.B (N e)) := by
  have H : ∀ e, ∃ (N : LB (t.l e).Q.B.left) (u : LB.Gen (N.pull (t.l e).Q.q.left)),
      N.IsLB ∧ (t.l e).Q.GenWt N u χ ∧ Triv (abelian₂ (t.l e).Q.B N) := by
    intro e
    haveI := isLocalRing_quotient_pow V e
    obtain ⟨N, u, hN, hu, g, hg⟩ := GlobalTheory.exists_weight_bundle _ _ _ (t.l e).Q χ
    exact ⟨N, u, hN, hu, g, hg⟩
  choose N u h using H
  exact ⟨N, u, h⟩

theorem lbIso_succ (t : Tower s) {χ : s.X} (e : ℕ) {N : LB (t.l e).Q.B.left} {N' : LB (t.l (e + 1)).Q.B.left}
    {u : LB.Gen (N.pull (t.l e).Q.q.left)} {u' : LB.Gen (N'.pull (t.l (e + 1)).Q.q.left)} (hN : N.IsLB)
    (hN' : N'.IsLB) (hu : (t.l e).Q.GenWt N u χ) (hu' : (t.l (e + 1)).Q.GenWt N' u' χ) :
    LBIso N (N'.pull (t.β e)) := by
  obtain ⟨v, hv⟩ := exists_genWt_pull (t.l (e + 1)).Q (t.l e).Q
    (isGrpPullback_thickMap (IsLocalRing.maximalIdeal V) G e) (t.tor e) (t.β_q e) hu'
  exact lbIso_of_genWt _ _ _ (t.l e).Q N (N'.pull (t.β e)) u v χ hN (pull_isLB hN' _) hu hv

theorem isPullback_of_isCPPullback {S S' : Scheme.{0}} {B' : Over S'} {B : Over S} [GrpObj B'] [IsCommMonObj B']
    [GrpObj B] [IsCommMonObj B] {M' : CP B'} {M : CP B} {f : S' ⟶ S} {β : B'.left ⟶ B.left}
    (h : IsCPPullback M' M f β) : IsPullback β B'.hom B.hom f := by
  obtain ⟨hg, -⟩ := h
  exact hg.1

theorem exists_alg_of_lbIso {V : Type} [CommRing V] [IsDomain V] [i : IsLocalRing V] (hV : CDVR V)
    (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1)))))
    (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left)
    (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans V (IsLocalRing.maximalIdeal V) e))
    (B : Over (Spec (CommRingCat.of V))) (b : ∀ e, (Y e).left ⟶ B.left) (hp : IsProjBy B.hom) (hf : Flat B.hom)
    (hb : ∀ e, IsPullback (b e) (Y e).hom B.hom (thick V (IsLocalRing.maximalIdeal V) e))
    (hc : ∀ e, β e ≫ b (e + 1) = b e) (N : ∀ e, LB (Y e).left) (hN : ∀ e, (N e).IsLB)
    (h : ∀ e, LBIso (N e) ((N (e + 1)).pull (β e))) :
    ∃ M : LB B.left, M.IsLB ∧ ∀ e, LBIso (N e) (M.pull (b e)) := by
  haveI : IsDiscreteValuationRing V := hV.1
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal V) V := hV.2.1
  choose w hw using h
  exact GlobalTheory.LBAlg.exists_lineBundle_of_thickenings V Y β hβ B b hp hf hb hc N w fun e => ⟨hN e, hw e⟩

theorem isPullback_β (t : Tower s) (e : ℕ) : IsPullback (t.β e) (t.l e).Q.B.hom (t.l (e + 1)).Q.B.hom
    (thickTrans V (IsLocalRing.maximalIdeal V) e) := isPullback_of_isCPPullback (t.β_pb e)

theorem isPullback_b {t : Tower s} (a : t.Alg) (e : ℕ) : IsPullback (a.b e) (t.l e).Q.B.hom a.B.hom
    (thick V (IsLocalRing.maximalIdeal V) e) := isPullback_of_isCPPullback (a.b_pb e)

theorem flat_alg {t : Tower s} (a : t.Alg) : Flat a.B.hom := by
  haveI := a.isAb.smooth
  infer_instance

theorem exists_alg {t : Tower s} (a : t.Alg) (N : ∀ e, LB (t.l e).Q.B.left) (hN : ∀ e, (N e).IsLB)
    (h : ∀ e, LBIso (N e) ((N (e + 1)).pull (t.β e))) :
    ∃ O : LB a.B.left, O.IsLB ∧ ∀ e, LBIso (N e) (O.pull (a.b e)) := by
  have hp : IsProjBy a.B.hom := isProjBy_of_relAmple a.B a.M.L.3 a.ample
  exact exists_alg_of_lbIso s.cdvr (fun e => (t.l e).Q.B) t.β (isPullback_β t) a.B a.b hp (flat_alg a)
    (isPullback_b a) a.b_β N hN h

theorem triv_lam_alg (hG : GlobalFnsSt) {t : Tower s} (a : t.Alg) {N : ∀ e, LB (t.l e).Q.B.left}
    (hN : ∀ e, (N e).IsLB) {O : LB a.B.left} (hO : O.IsLB) (hi : ∀ e, LBIso (N e) (O.pull (a.b e)))
    (h : ∀ e, Triv (abelian₂ (t.l e).Q.B (N e))) : Triv (abelian₂ a.B O) := by
  haveI : IsDiscreteValuationRing V := s.cdvr.1
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal V) V := s.cdvr.2.1
  have hp : IsProjBy a.B.hom := isProjBy_of_relAmple a.B a.M.L.3 a.ample
  refine triv_lam_of_levels hG a.isAb hp hO fun e => ?_
  obtain ⟨hb, -⟩ := a.b_pb e
  exact triv_lam_pull hb hO (hN e) (hi e) (h e) (fstG (IsLocalRing.maximalIdeal V) e (a.B ⊗ a.B))

theorem exists_weight_bundle_alg : Laws → AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (a : t.Alg) (χ : s.X), ∃ O : LB a.B.left, O.IsLB ∧ (∃ u : LB.Gen (abelian₂ a.B O), u.IsGen) ∧ ∀ e, ∃ u : LB.Gen (O.pull ((t.l e).Q.q.left ≫ a.b e)), u.IsGen ∧ ∀ j, IsWt (t.l e).Q.i _ (u.s j).val χ := by
  intro hL V _ _ _ A G _ _ s t a χ
  obtain ⟨N, u, h⟩ := exists_levels t χ
  have hiso : ∀ e, LBIso (N e) ((N (e + 1)).pull (t.β e)) := fun e =>
    lbIso_succ t e (h e).1 (h (e + 1)).1 (h e).2.1 (h (e + 1)).2.1
  obtain ⟨O, hO, hi⟩ := exists_alg a N (fun e => (h e).1) hiso
  have hT := triv_lam_alg hL.globalFns a (fun e => (h e).1) hO hi (fun e => (h e).2.2)
  refine ⟨O, hO, hT, fun e => ?_⟩
  obtain ⟨v, hv⟩ := exists_genWt_of_lbIso (t.l e).Q (h e).1 (pull_isLB hO _) (hi e) (h e).2.1
  exact exists_gen_comp (t.l e).Q (a.b e) hv

end GlobalTheory.WtTower
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsWeightBundleTorusQuotientTowerAlgebraisatiStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weightBundle_torusQuotientTower_algebraisation : Laws → AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (a : t.Alg) (χ : s.X), ∃ O : LB a.B.left, O.IsLB ∧ (∃ u : LB.Gen (abelian₂ a.B O), u.IsGen) ∧ ∀ e, ∃ u : LB.Gen (O.pull ((t.l e).Q.q.left ≫ a.b e)), u.IsGen ∧ ∀ j, IsWt (t.l e).Q.i _ (u.s j).val χ := by
  first | exact @GlobalTheory.WtTower.exists_weight_bundle_alg | exact GlobalTheory.WtTower.exists_weight_bundle_alg | (intros; apply GlobalTheory.WtTower.exists_weight_bundle_alg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPointRepresentingWeightMumfordQuotient
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.WtPoint

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X] {i : splitTorus S X ⟶ G}
  {Y : Scheme.{0}} {f : G.left ⟶ Y}

theorem gm_gen_pull {Z W : Scheme.{0}} {F : Z ⟶ Y} {M : LB Y} {t : LB.Gen (M.pull F)} (ht : t.IsGen) (r : W ⟶ Z) (y : W)
    {j j' : M.ι} (hj : F (r y) ∈ M.U j) (hj' : F (r y) ∈ M.U j') :
    gm r y ((M.pull F).U fun _ => j) (t.s fun _ => j) =
      gm (r ≫ F) y (M.U j ⊓ M.U j') (M.g j j') * gm r y ((M.pull F).U fun _ => j') (t.s fun _ => j') := by
  have hm : r y ∈ (M.pull F).U (fun _ => j) ⊓ (M.pull F).U (fun _ => j') := ⟨mem_pull.2 hj, mem_pull.2 hj'⟩
  have e := congrArg (gm r y _) (ht (fun _ => j) (fun _ => j'))
  rw [map_mul, gm_res _ y _ hm, gm_res _ y _ hm, gm_pull_g M F r y _ _ hm.1 hm.2] at e
  exact e

theorem gm_iso {W : Scheme.{0}} {O N : LB Y} {w : LB.Iso O N} (hw : w.IsGen) (r : W ⟶ Y) (y : W)
    {j j' : N.ι} {k k' : O.ι} (h : r y ∈ N.U j ⊓ O.U k) (h' : r y ∈ N.U j' ⊓ O.U k') :
    gm r y (N.U j ⊓ O.U k) (w.s (j, k)) =
      gm r y (N.U j ⊓ N.U j') (N.g j j') * (gm r y (O.U k ⊓ O.U k') (O.g k k'))⁻¹ *
        gm r y (N.U j' ⊓ O.U k') (w.s (j', k')) := by
  have hm : r y ∈ N.U j ⊓ O.U k ⊓ (N.U j' ⊓ O.U k') := ⟨h, h'⟩
  exact (gm_res r y _ hm _).symm.trans ((congrArg (gm r y _) (hw (j, k) (j', k'))).trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (gm_div O N r y (j, k) (j', k') hm) (gm_res r y _ hm _))))

theorem exists_gen_of_iso
    (hf : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G), ((t ≫ i) * g).left ≫ f = g.left ≫ f)
    {O N : LB Y} (hO : O.IsLB) (hN : N.IsLB) (h : LBIso O N) {χ : X} (u : LB.Gen (O.pull f)) (hu : u.IsGen)
    (hχ : ∀ k, IsWt i _ (u.s k).val χ) :
    ∃ v : LB.Gen (N.pull f), v.IsGen ∧ ∀ j, IsWt i _ (v.s j).val χ := by
  obtain ⟨w, hw⟩ := h
  have tr : ∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (j j' : N.ι) (k k' : O.ι), f (r z) ∈ N.U j ⊓ O.U k →
      f (r z) ∈ N.U j' ⊓ O.U k' →
      gm (r ≫ f) z (N.U j ⊓ O.U k) (w.s (j, k)) * gm r z ((O.pull f).U fun _ => k) (u.s fun _ => k) =
        gm (r ≫ f) z (N.U j ⊓ N.U j') (N.g j j') *
          (gm (r ≫ f) z (N.U j' ⊓ O.U k') (w.s (j', k')) * gm r z ((O.pull f).U fun _ => k') (u.s fun _ => k')) := by
    intro Z r z j j' k k' h h'
    rw [gm_iso hw (r ≫ f) z h h', gm_gen_pull hu r z h.2 h'.2, _root_.mul_assoc, _root_.mul_assoc,
      mul_left_comm (gm (r ≫ f) z (N.U j' ⊓ O.U k') (w.s (j', k'))), inv_mul_cancel_left]
  have glue : ∀ j : N.ι, ∃ s : Γ(G.left, (N.pull f).U fun _ => j)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (k : O.ι),
      f (r z) ∈ N.U j ⊓ O.U k → gm r z _ s =
        gm (r ≫ f) z (N.U j ⊓ O.U k) (w.s (j, k)) * gm r z ((O.pull f).U fun _ => k) (u.s fun _ => k) := by
    intro j
    have l₀ : ∀ k, f ⁻¹ᵁ (N.U j ⊓ O.U k) ≤ (N.pull f).U fun _ => j := fun k x hx => mem_pull.2 hx.1
    have l₁ : ∀ k, f ⁻¹ᵁ (N.U j ⊓ O.U k) ≤ (O.pull f).U fun _ => k := fun k x hx => mem_pull.2 hx.2
    obtain ⟨a, ha⟩ : ∃ a : ∀ k, Γ(G.left, f ⁻¹ᵁ (N.U j ⊓ O.U k))ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (k : O.ι),
        f (r z) ∈ N.U j ⊓ O.U k → gm r z _ (a k) =
          gm (r ≫ f) z (N.U j ⊓ O.U k) (w.s (j, k)) * gm r z ((O.pull f).U fun _ => k) (u.s fun _ => k) :=
      ⟨fun k => pullU f (N.U j ⊓ O.U k) (w.s (j, k)) * res (l₁ k) (u.s fun _ => k), fun Z r z k hz =>
        (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_pull r f z _ hz _) (gm_res r z (l₁ k) hz _))⟩
    obtain ⟨s, hs⟩ := glue_unit _ _ l₀ (fun x hx => by
        obtain ⟨k, hk⟩ := exists_chart hO (f x)
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, mem_pull.1 hx, hk⟩) a (fun k k' x hx => by
        rw [ha _ (𝟙 _) x k hx.1, ha _ (𝟙 _) x k' hx.2, tr _ (𝟙 _) x j j k k' hx.1 hx.2,
          gm_self hN (𝟙 _ ≫ f) x hx.1.1, _root_.one_mul])
    exact ⟨s, fun Z r z k hz => (gm_res r z (l₀ k) hz s).symm.trans
      ((congrArg (gm r z (f ⁻¹ᵁ (N.U j ⊓ O.U k))) (hs k)).trans (ha Z r z k hz))⟩
  choose s hs using glue
  refine ⟨⟨fun J => s (J PUnit.unit)⟩, fun J J' => unit_ext fun y hy => ?_, fun J => isWt_of_gm _ _ ?_⟩
  · obtain ⟨k, hk⟩ := exists_chart hO (f y)
    have h₁ := mem_pull.1 hy.1
    have h₂ := mem_pull.1 hy.2
    exact ((gm_res _ y _ hy _).trans ((hs _ _ (𝟙 _) y k ⟨h₁, hk⟩).trans
      (tr _ (𝟙 _) y _ _ k k ⟨h₁, hk⟩ ⟨h₂, hk⟩))).trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
        (gm_pull_g N f (𝟙 _) y J J' hy.1 hy.2) ((gm_res _ y _ hy _).trans (hs _ _ (𝟙 _) y k ⟨h₂, hk⟩)))).symm
  · intro Z t g z hz
    obtain ⟨k, hk⟩ := exists_chart hO (f (g.left z))
    have h₂ : f (g.left z) ∈ N.U (J PUnit.unit) ⊓ O.U k := ⟨mem_pull.1 hz, hk⟩
    have h₁ : f (((t ≫ i) * g).left z) ∈ N.U (J PUnit.unit) ⊓ O.U k :=
      (congrArg (fun m : Z.left ⟶ Y => m z ∈ N.U (J PUnit.unit) ⊓ O.U k) (hf Z t g)).mpr h₂
    refine (hs _ _ _ z k h₁).trans (Eq.trans ?_ (congrArg (_ * ·) (hs _ _ _ z k h₂)).symm)
    rw [hf, WtBundle.gm_of_isWt (hχ fun _ => k) t g z (mem_pull.2 h₁.2) (mem_pull.2 h₂.2), gm_charUnit,
      mul_left_comm]

theorem exists_gen_neg {B : Scheme.{0}} {L : LB B} {K : Type} [Fintype K] {φ : K → (Y ⟶ B)} {ε ε' : K → ℤ}
    (hε : ∀ k, ε' k = - ε k) {χ : X} (u : LB.Gen ((LB.LinComb L φ ε).pull f)) (hu : u.IsGen)
    (hχ : ∀ k, IsWt i _ (u.s k).val (-χ)) :
    ∃ v : LB.Gen ((LB.LinComb L φ ε').pull f), v.IsGen ∧ ∀ j, IsWt i _ (v.s j).val χ := by
  refine ⟨⟨fun J => (u.s J)⁻¹⟩, fun J J' => ?_, fun J => ?_⟩
  · refine unit_ext fun y hy => ?_
    have h₁ : f y ∈ LB.wchart L φ (J PUnit.unit) := mem_pull.1 hy.1
    have h₂ : f y ∈ LB.wchart L φ (J' PUnit.unit) := mem_pull.1 hy.2
    have e : gm (𝟙 _ ≫ f) y _ ((LB.LinComb L φ ε').g (J PUnit.unit) (J' PUnit.unit)) =
        (gm (𝟙 _ ≫ f) y _ ((LB.LinComb L φ ε).g (J PUnit.unit) (J' PUnit.unit)))⁻¹ := by
      refine (gm_linComb L φ ε' (𝟙 _ ≫ f) y _ _ h₁ h₂).trans (Eq.trans ?_
        (congrArg (·⁻¹) (gm_linComb L φ ε (𝟙 _ ≫ f) y _ _ h₁ h₂)).symm)
      simp only [hε, zpow_neg, Finset.prod_inv_distrib]
    exact ((gm_res _ y _ hy _).trans ((map_inv _ _).trans ((congrArg (·⁻¹) (gm_gen_pull hu (𝟙 _) y h₁ h₂)).trans
      (mul_inv _ _)))).trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
        ((gm_pull_g (LB.LinComb L φ ε') f (𝟙 _) y J J' hy.1 hy.2).trans e)
        ((gm_res _ y _ hy _).trans (map_inv _ _)))).symm
  · have := (hχ J).inv
    rwa [neg_neg] at this

theorem sym_of_cp [IsCommMonObj G] (P : CP G) : Out.Sym G P.L.L := fun _ => by
  obtain ⟨t, ht, -⟩ := exists_gen P.L.isLB (K' := Fin 2)
    (φ' := ![(G.hom ⁻¹ᵁ ⊤).ι ≫ (GrpObj.inv : G ⟶ G).left, (G.hom ⁻¹ᵁ ⊤).ι]) (ε' := ![1, -1])
    (fun U _ h => by simp [Fin.prod_univ_two]) (LB.pullGen _ _ _ P.sym (G.hom ⁻¹ᵁ ⊤).ι)
    (LB.isGen_pullGen _ _ _ _ P.sym_gen _)
  exact ⟨⊤, trivial, t, ht⟩

end GlobalTheory.WtPoint

namespace GlobalTheory

theorem exists_point_repWt : Laws → AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (a : t.Alg), KTriv a.B a.M.L.L → ∀ χ : s.X, ∃ c : 𝟙_ _ ⟶ a.B, ∀ e, a.RepWt c χ e := by
  intro hL V _ _ _ A G _ _ s t a hK χ
  have : IsDiscreteValuationRing V := s.cdvr.1
  obtain ⟨g, hg⟩ := AbelianDim.exists_relDim V a.B a.isAb
  obtain ⟨O, hO, hΛ, hu⟩ := GlobalTheory.T.exists_weightBundle_torusQuotientTower_algebraisation hL V A G s t a (-χ)
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.PrimitiveOverValuationRing.exists_section_translate hL V
    { A := a.B, isAb := a.isAb, g := g, smoothDim := hg, L := a.M.L.L, isLB := a.M.L.isLB,
      rigid := ⟨a.M.L.rig, a.M.L.rigGen⟩, sym := WtPoint.sym_of_cp a.M, ample := a.ample, ktriv := hK } O hO hΛ
  refine ⟨c, fun e => ?_⟩
  obtain ⟨u, hu, hw⟩ := hu e
  obtain ⟨v, hv, hw'⟩ := WtPoint.exists_gen_of_iso (fun Z τ x => by
    rw [← Category.assoc, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, WtBundle.act_comp])
    hO (LB.isLB_linComb a.M.L.isLB _ _) hc u hu hw
  exact WtPoint.exists_gen_neg (fun k => by fin_cases k <;> rfl) v hv hw'

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPointRepresentingWeightMumfordQuotientStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_point_representing_weight_mumfordQuotient : Laws → AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (a : t.Alg), KTriv a.B a.M.L.L → ∀ χ : s.X, ∃ c : 𝟙_ _ ⟶ a.B, ∀ e, a.RepWt c χ e := by
  first | exact @GlobalTheory.exists_point_repWt | exact GlobalTheory.exists_point_repWt | (intros; apply GlobalTheory.exists_point_repWt <;> assumption)
end
end
