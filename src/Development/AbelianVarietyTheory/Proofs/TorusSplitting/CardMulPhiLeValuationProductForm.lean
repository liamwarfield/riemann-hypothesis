module

public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionIsoOfLinearUniformisationTriple
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.EtaProductRuleValueEqProductFormOfTestRing
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ValuationFormPsiBalancedSymmetricPeriodForm

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusSplitting.LeValuationOddLevelThetaConstantIntegralExpansio
section -- merged from Development.AbelianVarietyTheory.Proofs.TorusSplitting.LeValuationOddLevelThetaConstantIntegralExpansio
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.EtaVal
open GlobalTheory.UT GlobalTheory.TorusExt GlobalTheory.UT.ThetaConstVal

attribute [local instance] gtGroup

theorem le_val_thetaConst : GlobalTheory.UT.AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ ρ, GlobalTheory.UT.NormW U.toUnifPre w₀ ρ → ∀ (th : GlobalTheory.UT.SecA A F 1) (ϑ : Fam D.toPre F 1), U.ExpandsF F 1 w₀ th ϑ → NuGe D Q F v 1 ϑ 0 → ∀ (m : ℕ), Odd m → ∀ (p : QkPt D.toPre F (m ^ 2)) x t c, QkToAkU U.toUnifPre F (m ^ 2) p x → GlobalTheory.UT.ThC A ρ m th x t c → ∀ q : ℚ, (∀ χ, q ≤ (Q (m • χ + p.y) : ℚ) / (m ^ 2 : ℕ)) → (q : WithTop ℚ) ≤ v c := by
  obtain ⟨hL, h₁, h₂, h₃, h₄⟩ := GlobalTheory.lawsAndExpansions
  intro V _ _ _ _ hc ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U w₀ ρ hN th ϑ hE hP m hm p x t c hx hT q hq
  have hA : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hc⟩
  obtain ⟨w, hw⟩ := (GlobalTheory.UT.SymFrame.main hL V _ hA D F (m ^ 2) hm.pow p).1
  obtain ⟨κ, hκ⟩ := exists_kap D.toPre hL.1.mulPull m
  obtain ⟨w', hw', e⟩ := exists_frm D.toPre m p.g.b (m • p.g).b (nsmul_b m p.g) w hw.1 κ hκ.1
  have hg : GtPtF.IsNsmul m p.g (m • p.g) := (isNsmul_iff_eq _ _ _).2 rfl
  have s := (GlobalTheory.UT.ThetaSum.theta_const_sum hL V _ hA D A G hG U F w₀ ρ hN th ϑ hE m hm p x t c hx hT w hw _ hg κ hκ w' hw' e).1
  obtain ⟨-, -, a⟩ := (GlobalTheory.UT.TxVal.main hL h₁ h₂ h₃ h₄ V hc ϖ hϖ D Q hQ F v hv).2 m hm.pos p w hw _ hg κ hκ w' hw' e
  exact le_of_sumV (AdicValSum.main V ϖ hϖ F v hv _ _ _ s).1 fun χ =>
    (WithTop.coe_le_coe.2 (hq χ)).trans (a ϑ hP χ)

end GlobalTheory.EtaVal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusSplitting.LeValuationOddLevelThetaConstantIntegralExpansioStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.le_valuation_oddLevel_thetaConstant_integralExpansion : GlobalTheory.UT.AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ ρ, GlobalTheory.UT.NormW U.toUnifPre w₀ ρ → ∀ (th : GlobalTheory.UT.SecA A F 1) (ϑ : Fam D.toPre F 1), U.ExpandsF F 1 w₀ th ϑ → NuGe D Q F v 1 ϑ 0 → ∀ (m : ℕ), Odd m → ∀ (p : QkPt D.toPre F (m ^ 2)) x t c, QkToAkU U.toUnifPre F (m ^ 2) p x → GlobalTheory.UT.ThC A ρ m th x t c → ∀ q : ℚ, (∀ χ, q ≤ (Q (m • χ + p.y) : ℚ) / (m ^ 2 : ℕ)) → (q : WithTop ℚ) ≤ v c := by
  first | exact @GlobalTheory.EtaVal.le_val_thetaConst | exact GlobalTheory.EtaVal.le_val_thetaConst | (intros; apply GlobalTheory.EtaVal.le_val_thetaConst <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusSplitting.NormalisedThetaConstantOfUniversalOriginValue
section -- merged from Development.AbelianVarietyTheory.Proofs.TorusSplitting.NormalisedThetaConstantOfUniversalOriginValue
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EtaVal.NullMove

open GlobalTheory.TranslMove GlobalTheory.VVRank

theorem map_gm {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (a : Γ(X, U)ˣ) :
    Units.map (r.stalkMap z).hom.toMonoidHom (gm g (r z) U a) = gm (r ≫ g) z U a := by
  symm
  by_cases h : g (r z) ∈ U
  · refine Units.ext ((gs_unit (r ≫ g) z U h a).symm.trans (Eq.trans ?_
      (congrArg (r.stalkMap z).hom (gs_unit g (r z) U h a))))
    rw [← gs_pull r g z U h, gs_stalkMap r z _ h, gs_pull (𝟙 Y) g (r z) U h, Category.id_comp]
  · have h' : (r ≫ g) z ∉ U := h
    rw [gm, dite_eq_right h', gm, dite_eq_right h]
    exact (map_one _).symm

section General

variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A]
  {f : S' ⟶ S} {φ : A.left ⟶ G.left} {L₀ : LB G.left} {L₁ : LB A.left}

theorem pmaps_of_stalks (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) {w : LB.Iso L₁ (L₀.pull φ)}
    {ρ₀ : LB.Gen (L₀.pull (eSec G))} {ρ : LB.Gen (L₁.pull (eSec A))} (he : eSec A ≫ φ = f ≫ eSec G)
    (h : ∀ (z : S') (JA) (J), Good L₁ z JA → Good L₀ z J →
      gw w (eSec A) z (J (f ≫ eSec G)) (JA (eSec A)) *
        val (L := L₁) (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) ρ (𝟙 _) z JA =
      val (L := L₀) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) ρ₀ f z J) :
    PMaps w (K := PUnit) (fun _ => eSec A) (fun _ => eSec G) (fun _ => 1) ρ ρ₀ f := by
  intro Z r z p q hp hq
  obtain ⟨J, hJ, e₀⟩ := exists_good L₀ hL₀ (Z := S') (r z) (fun _ : PUnit => f ≫ eSec G) p
    (fun _ _ _ => rfl) (fun k => by rw [← he]; exact hp k)
  obtain ⟨JA, hJA, e₁⟩ := exists_good L₁ hL₁ (Z := S') (r z) (fun _ : PUnit => eSec A) q
    (fun _ _ _ => rfl) hq
  have a := h (r z) JA J hJA hJ
  rw [val_of (L := L₀) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) ρ₀ f (r z) J p e₀,
    val_of (L := L₁) (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) ρ (𝟙 _) (r z) JA q
      (fun k => by rw [Category.id_comp]; exact e₁ k), e₀ PUnit.unit, e₁ PUnit.unit] at a
  have b := congrArg (Units.map (r.stalkMap z).hom.toMonoidHom) a
  rw [Fintype.prod_unique, zpow_one]
  refine (map_gm r f z _ _).symm.trans (b.symm.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) (map_gm r _ z _ _) ?_)))
  exact (map_gm r (𝟙 _) z _ _).trans (by rw [Category.comp_id])

theorem one_comm (hp : IsGrpPullback A G f φ) {T : Over S'} {T₀ : Over S} {τ : T.left ⟶ T₀.left}
    (hτ : τ ≫ T₀.hom = T.hom ≫ f) : τ ≫ (1 : T₀ ⟶ G).left = (1 : T ⟶ A).left ≫ φ :=
  (pt_iff hp hτ 1 1).2 (by rw [map_one, map_one])

theorem eSec_comm (hp : IsGrpPullback A G f φ) : eSec A ≫ φ = f ≫ eSec G := by
  have h := one_comm hp (T := 𝟙_ (Over S')) (T₀ := 𝟙_ (Over S)) (τ := f)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
  have a : (η[A] : 𝟙_ (Over S') ⟶ A) = 1 := by simp [Hom.one_def]
  have b : (η[G] : 𝟙_ (Over S) ⟶ G) = 1 := by simp [Hom.one_def]
  rw [← a, ← b] at h
  exact h.symm

theorem sv_valueAt {T : Over S'} {a : ℤ} {s : LB.Sec (LPow A L₁ a T)} {x : T ⟶ A}
    {τ : LB.Gen (LB.LinComb L₁ (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => a))} {v : Γ(T.left, ⊤)}
    (H : IsValueAt A L₁ a s x τ v) {Z : Scheme.{0}} (r : Z ⟶ T.left) {z : Z} {J} (hJ : Good L₁ z J) :
    sv A s (r ≫ (ptSecT A x).left) z J = gs r z ⊤ v * (val τ r z J).val := by
  have hy := hJ.mem (fun _ : Fin 1 => x.left) r
  refine (sval_of (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s (r ≫ (ptSecT A x).left) z J
    (fun _ => J (r ≫ x.left)) (fun _ => by rw [Category.assoc, ← Over.comp_left, ptSecT, lift_snd])).trans ?_
  refine Eq.trans ?_ ((congrArg (gs r z _) (H _)).trans ((gs_mul _ z _ hy _ _).trans
    (congrArg₂ (· * ·) (gs_res _ z _ hy _) (gs_unit _ z _ hy _))))
  exact ((gs_res _ z _ hy _).trans (gs_pull r (ptSecT A x).left z
    (LB.wchart L₁ (fun _ : Fin 1 => (snd T A).left) (fun _ => J (r ≫ x.left))) (val_le A L₁ x _ hy) _)).symm

theorem val_rigT_pow (rig : LB.Gen (L₁.pull (eSec A))) (T : Over S') (k : ℤ) {Z : Scheme.{0}} (r : Z ⟶ T.left) {z : Z}
    {J} (hJ : Good L₁ z J) : val (rigT A L₁ rig T k) r z J =
      val (L := L₁) (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) rig (r ≫ T.hom) z J ^ k := by
  rw [val_of (L := L₁) (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) rig (r ≫ T.hom) z J
    (fun _ => J (r ≫ T.hom ≫ eSec A)) (fun _ => congrArg J (Category.assoc _ _ _))]
  have hm := hJ.mem (fun _ : Fin 1 => T.hom ≫ eSec A) r
  refine (map_zpow _ _ _).trans (congrArg (· ^ k) ((gm_res r z _ hm _).trans ?_))
  exact gm_pull r T.hom z _ (rigT_le A L₁ _ hm) _

theorem exists_move [IsCommMonObj G] [IsCommMonObj A] (hp : IsGrpPullback A G f φ)
    {T : Over S'} {T₀ : Over S} {τ : T.left ⟶ T₀.left} {M₀ : RigLB G} (hL₁ : L₁.IsLB)
    {ρ : LB.Gen (L₁.pull (eSec A))} {w : LB.Iso L₁ (M₀.L.pull φ)} (hw : w.IsGen)
    {Ψ : (T ⊗ A).left ⟶ (T₀ ⊗ G).left} (h₁ : Ψ ≫ (fst T₀ G).left = (fst T A).left ≫ τ)
    (h₂ : Ψ ≫ (snd T₀ G).left = (snd T A).left ≫ φ)
    (hρ : PMaps w (K := PUnit) (fun _ => eSec A) (fun _ => eSec G) (fun _ => 1) ρ M₀.rig f) (N : ℕ)
    (hk : ∀ θ : ThetaGrp A L₁ ((N : ℤ) ^ 2) T, θ.pt ^ (N ^ 2) = 1)
    {s₀ : LB.Sec (LPow G M₀.L 1 T₀)} {s : LB.Sec (LPow A L₁ 1 T)} (hs : SecRel w Ψ s₀ s)
    {x : T ⟶ A} {y y' : T₀ ⟶ G} (hx : τ ≫ y.left = x.left ≫ φ)
    {F₀ : LB.Sec (LPow G M₀.L ((N : ℤ) ^ 2) T₀)} (H : IsVtOver G M₀ N (fun t => t = y) s₀ y' F₀)
    {v : Γ(T₀.left, ⊤)} (hv : IsValueAt G M₀.L ((N : ℤ) ^ 2) F₀ 1 (rigT G M₀.L M₀.rig T₀ ((N : ℤ) ^ 2)) v)
    {k : ℤ} (hN : (N : ℤ) ^ 2 = k) :
    ∃ (t : LB.Sec (LPow A L₁ k T))
      (α : LB.Gen (LB.LinComb L₁ (K := Fin 2) ![(snd T A).left, (snd T A ^ N).left] ![k, -1]))
      (s₁ : LB.Sec (LPow A L₁ k T)) (θ : ThetaGrp A L₁ k T),
      α.IsGen ∧ LB.Gen.Corr L₁ _ _ _ _ (LB.pullGen L₁ _ _ α (ptSecT A 1).left) (rigT A L₁ ρ T (k - 1)) ∧
      IsTwistPull A L₁ (mulT A T N) (snd T A ^ N) (lift_snd _ _) k 1 α s s₁ ∧
      SymLift A L₁ k (N ^ 2) x θ ∧ IsActOf A L₁ k θ s₁ t ∧
      ∀ z J, Good L₁ z J → sv A t (ptSecT A 1).left z J = gs τ z ⊤ v * (val (rigT A L₁ ρ T k) (𝟙 _) z J).val := by
  subst hN
  have he := eSec_comm hp
  have hτ := base_comm hp hx
  obtain ⟨_, β₀, β, r₁, V, -, rfl, g₀, n₀, cβ, tw, sl, ac⟩ := H
  obtain ⟨α₀, gα₀, nα₀, v₀⟩ := exists_normMul hp M₀.isLB hL₁ hw he hρ N g₀ n₀
  obtain ⟨α, gα, cα⟩ := NormMulUniv.exists_pull hL₁ α₀ gα₀ T
  have vα : GenRel w Ψ β α := fun Z r z J₀ J hJ₀ hJ => by
    rw [val_corr hJ₀ cβ, val_pull hJ₀, val_corr hJ cα, val_pull hJ, Category.assoc, h₂, ← Category.assoc,
      v₀ Z _ z J₀ J hJ₀ hJ, Category.comp_id, Category.assoc, ← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  obtain ⟨s₁, tw'⟩ := VVRank.exists_isTwistPull A (ψ := mulT A T N) (hm := lift_snd _ _) (b := 1) hL₁ gα s
  have R₁ := secRel_twist (lift_comm h₁ (pt_pow hp h₂ N) h₂) vα tw tw' hs
  obtain ⟨U, l₁, a₁⟩ := exists_symLift hp M₀.isLB hL₁ hw h₁ h₂ hk hx sl
  obtain ⟨t, b₁, R₂⟩ := a₁ _ _ _ ac R₁
  have o₁ : (ptSecT A (1 : T ⟶ A)).left ≫ (snd T A).left = T.hom ≫ eSec A := by
    rw [← Over.comp_left, ptSecT, lift_snd]; rfl
  refine ⟨t, α, s₁, U, gα, corr_of_val hL₁ fun z J hJ => ?_, tw', l₁, b₁, fun z J hJ => ?_⟩
  · have a := (val_pull hJ α₀ (eSec A) T.hom).symm.trans ((val_corr hJ nα₀ T.hom).trans ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) (val_rigPow _ _ _ _ _) (val_inv _ _))))
    refine (val_pull hJ _ _ _).trans ((val_corr hJ cα _).trans ((val_pull hJ _ _ _).trans
      (Eq.trans ?_ (val_rigT_pow ρ T _ _ hJ).symm)))
    rw [Category.id_comp, Category.id_comp, o₁, zpow_sub_one]
    exact a
  · obtain ⟨J₀, hJ₀⟩ := exists_good_pt M₀.isLB z
    have o₂ : (ptSecT A (1 : T ⟶ A)).left ≫ Ψ = τ ≫ (ptSecT G (1 : T₀ ⟶ G)).left := by
      have e₁ : ((ptSecT A (1 : T ⟶ A)).left ≫ Ψ) ≫ (fst T₀ G).left =
          (τ ≫ (ptSecT G (1 : T₀ ⟶ G)).left) ≫ (fst T₀ G).left := by
        rw [Category.assoc, Category.assoc, h₁, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, ptSecT, ptSecT,
          lift_fst, lift_fst, Over.id_left, Over.id_left, Category.id_comp, Category.comp_id]
      have e₂ : ((ptSecT A (1 : T ⟶ A)).left ≫ Ψ) ≫ (snd T₀ G).left =
          (τ ≫ (ptSecT G (1 : T₀ ⟶ G)).left) ≫ (snd T₀ G).left := by
        rw [Category.assoc, Category.assoc, h₂, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, ptSecT, ptSecT,
          lift_snd, lift_snd, one_comm hp hτ]
      exact pullback.hom_ext e₁ e₂
    have a₁ := R₂ _ (ptSecT A 1).left z J₀ J hJ₀ hJ
    have a₂ := (sv_valueAt hv τ hJ₀).trans
      (congrArg (fun u => gs τ z ⊤ v * Units.val u) (val_rigT_pow M₀.rig T₀ _ τ hJ₀))
    have a₃ := val_move (fun _ => he) hρ T.hom hJ₀ hJ
    rw [Fintype.prod_unique, zpow_one] at a₃
    rw [o₂, a₂, hτ, o₁] at a₁
    have a₄ := a₁.symm.trans (congrArg (fun u => gs τ z ⊤ v * Units.val (u ^ ((N : ℤ) ^ 2))) a₃)
    rw [mul_zpow, Units.val_mul, _root_.mul_left_comm] at a₄
    rw [val_rigT_pow ρ T _ _ hJ, Category.id_comp]
    exact (Units.mul_right_inj _).1 a₄

end General

theorem thC_of_isNullVal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (R : Type) [CommRing R] [IsDomain R] [CharZero R] (x : Sp (FractionRing R) ⟶ Xo.X) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (Φ : Fib Xo x A) (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra c.F F] (z : FrPt Xo c F), z.x = spMap (algebraMap (FractionRing R) F) ≫ x → ∀ th : GlobalTheory.UT.SecA A F 1, Φ.SecTie z.x z.s th → ∀ (m : ℕ), Odd m → ∀ (p : ptO Xo z.x ⟶ Xo.univ.t.G) (p' : TFK (R := R) F ⟶ A.A) (w : F), p ^ (m ^ 2) = 1 → p'.left ≫ Φ.φ = p.left → IsNullVal Xo c m z p w → ∃ t, GlobalTheory.UT.ThC A Φ.ρ m th p' t w := by
  intro E _ _ _ H Dw l Xo c R _ _ _ x A Φ F _ _ _ z hz th hth m _ p p' w _ hp hw
  obtain ⟨F₀, hV, hv⟩ := hw
  have := A.isAb.comm
  have hc : (fst (TFK (R := R) F) A.A).left ≫ z.x =
      ((snd (TFK (R := R) F) A.A).left ≫ Φ.φ) ≫ Xo.univ.t.G.hom := by
    rw [Category.assoc, Φ.cart.1.w, ← Category.assoc, Over.w (snd (TFK (R := R) F) A.A),
      ← Over.w (fst (TFK (R := R) F) A.A), hz, Category.assoc]
    rfl
  let Ψ : (TFK (R := R) F ⊗ A.A).left ⟶ (ptO Xo z.x ⊗ Xo.univ.t.G).left := pullback.lift _ _ hc
  have h₁ : Ψ ≫ (fst (ptO Xo z.x) Xo.univ.t.G).left = (fst (TFK (R := R) F) A.A).left := pullback.lift_fst _ _ _
  have h₂ : Ψ ≫ (snd (ptO Xo z.x) Xo.univ.t.G).left = (snd (TFK (R := R) F) A.A).left ≫ Φ.φ := pullback.lift_snd _ _ _
  have hs : SecRel (G := Xo.univ.t.G) (T₀ := ptO Xo z.x) (a := 1) Φ.ω Ψ z.s th := fun Z r y J₀ J hJ₀ hJ => by
    have e : (r ≫ Ψ) ≫ (snd (ptO Xo z.x) Xo.univ.t.G).left = (r ≫ (snd (TFK (R := R) F) A.A).left) ≫ Φ.φ := by
      rw [Category.assoc, h₂, Category.assoc]
    have a := hth.2 Z r (r ≫ Ψ) (e.trans (Category.assoc _ _ _)) (by rw [Category.assoc, h₁]) y J J₀ hJ hJ₀
    rw [zpow_one]
    unfold TranslMove.wv
    rw [← e]
    exact a
  obtain ⟨t, α, s₁, θ, h⟩ := exists_move Φ.cart (T := TFK (R := R) F) (T₀ := ptO Xo z.x) (τ := 𝟙 (Sp F)) A.isLB Φ.ωgen
    (h₁.trans (Category.comp_id _).symm) h₂
    (pmaps_of_stalks Xo.univ.t.PP.isLB A.isLB (eSec_comm Φ.cart) Φ.rig) m
    (fun θ => pt_pow_eq_one GlobalTheory.firstFiveLaws.1.kerPow A (m ^ 2) (Nat.cast_pow m 2).symm θ) hs
    ((Category.id_comp _).trans hp.symm) hV hv (Nat.cast_pow m 2).symm
  exact ⟨t, α, s₁, θ, h⟩

end GlobalTheory.EtaVal.NullMove
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusSplitting.NormalisedThetaConstantOfUniversalOriginValueStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalisedThetaConstant_of_universal_origin_value : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (R : Type) [CommRing R] [IsDomain R] [CharZero R] (x : Sp (FractionRing R) ⟶ Xo.X) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (Φ : Fib Xo x A) (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra c.F F] (z : FrPt Xo c F), z.x = spMap (algebraMap (FractionRing R) F) ≫ x → ∀ th : GlobalTheory.UT.SecA A F 1, Φ.SecTie z.x z.s th → ∀ (m : ℕ), Odd m → ∀ (p : ptO Xo z.x ⟶ Xo.univ.t.G) (p' : TFK (R := R) F ⟶ A.A) (w : F), p ^ (m ^ 2) = 1 → p'.left ≫ Φ.φ = p.left → IsNullVal Xo c m z p w → ∃ t, GlobalTheory.UT.ThC A Φ.ρ m th p' t w := by
  first | exact @GlobalTheory.EtaVal.NullMove.thC_of_isNullVal | exact GlobalTheory.EtaVal.NullMove.thC_of_isNullVal | (intros; apply GlobalTheory.EtaVal.NullMove.thC_of_isNullVal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsAbelianSectionOfUniversalFibreSection
section -- merged from Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsAbelianSectionOfUniversalFibreSection
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EtaVal

theorem exists_secA_secTie :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (R : Type) [CommRing R] [IsDomain R] [CharZero R] (x : Sp (FractionRing R) ⟶ Xo.X) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (Φ : Fib Xo x A) (F : Type) [Field F] [Algebra (FractionRing R) F] (xF : Sp F ⟶ Xo.X), xF = spMap (algebraMap (FractionRing R) F) ≫ x → ∀ s : LB.Sec (PPx xF), ∃ th : GlobalTheory.UT.SecA A F 1, Φ.SecTie xF s th :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ Φ _ _ _ _ hx s => Φ.exists_secTie hx s

end GlobalTheory.EtaVal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsAbelianSectionOfUniversalFibreSectionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_abelianSection_of_universalFibreSection : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (R : Type) [CommRing R] [IsDomain R] [CharZero R] (x : Sp (FractionRing R) ⟶ Xo.X) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (Φ : Fib Xo x A) (F : Type) [Field F] [Algebra (FractionRing R) F] (xF : Sp F ⟶ Xo.X), xF = spMap (algebraMap (FractionRing R) F) ≫ x → ∀ s : LB.Sec (PPx xF), ∃ th : GlobalTheory.UT.SecA A F 1, Φ.SecTie xF s th := by
  first | exact @GlobalTheory.EtaVal.exists_secA_secTie | exact GlobalTheory.EtaVal.exists_secA_secTie | (intros; apply GlobalTheory.EtaVal.exists_secA_secTie <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusSplitting.CardMulLeAddValEtaExpr
section -- merged from Development.AbelianVarietyTheory.Proofs.TorusSplitting.CardMulLeAddValEtaExpr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EtaVal.RatBound

theorem addVal_prod {K : Type} [CommRing K] (ν : AddValuation K (WithTop ℚ)) {I : Type} (s : Finset I) (f : I → K) :
    ν (∏ i ∈ s, f i) = ∑ i ∈ s, ν (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ν.map_mul, ih]

theorem addVal_intCast_nonneg {K : Type} [CommRing K] (ν : AddValuation K (WithTop ℚ)) (m : ℤ) : 0 ≤ ν (m : K) := by
  induction m using Int.induction_on with
  | zero => simp
  | succ i ih =>
    push_cast at ih ⊢
    exact ν.map_le_add ih ν.map_one.ge
  | pred i ih =>
    push_cast at ih ⊢
    exact ν.map_le_sub ih ν.map_one.ge

theorem le_addVal_prod_sum {K : Type} [CommRing K] (ν : AddValuation K (WithTop ℚ)) {G J : Type} [Fintype G]
    [Fintype J] {n : ℕ} (cf : J → ℤ) (a : G → J → Fin n → K) (t : ℚ)
    (h : ∀ g j, (t : WithTop ℚ) ≤ ∑ b, ν (a g j b)) :
    (((Fintype.card G : ℚ) * t : ℚ) : WithTop ℚ) ≤ ν (∏ g, ∑ j, (cf j : K) * ∏ b, a g j b) := by
  rw [addVal_prod]
  have e : (((Fintype.card G : ℚ) * t : ℚ) : WithTop ℚ) = ∑ _g : G, (t : WithTop ℚ) := by
    rw [← WithTop.coe_sum]
    simp
  rw [e]
  refine Finset.sum_le_sum fun g _ => ν.map_le_sum fun j _ => ?_
  rw [ν.map_mul, addVal_prod]
  exact (h g j).trans (le_add_of_nonneg_left (addVal_intCast_nonneg ν _))

end GlobalTheory.EtaVal.RatBound

namespace GlobalTheory.EtaVal

theorem card_mul_le_addVal_etaExpr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (k : ℕ) [Finite (LevGrp Dw k)] (J : Type) [Fintype J] (n : ℕ) (cf : J → ℤ) (xs : J → Fin n → LatMod Dw k) (F : Type) [Field F] (v : AddValuation F (WithTop ℚ)) (w : LatMod Dw k → F) (q : ℚ), (∀ (g : LevGrp Dw k) j, (q : WithTop ℚ) ≤ ∑ b, v (w (g (xs j b)))) → (((Nat.card (LevGrp Dw k) : ℚ) * q : ℚ) : WithTop ℚ) ≤ v (etaExpr k cf xs w) := by
  intro E _ _ _ H Dw k _ J _ n cf xs F _ v w q h
  have := Fintype.ofFinite (LevGrp Dw k)
  have e : etaExpr k cf xs w = ∏ g : LevGrp Dw k, ∑ j, (cf j : F) * ∏ b, w (g (xs j b)) :=
    finprod_eq_prod_of_fintype _
  rw [e, Nat.card_eq_fintype_card]
  exact RatBound.le_addVal_prod_sum v cf (fun (g : LevGrp Dw k) j b => w (g (xs j b))) q h

end GlobalTheory.EtaVal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusSplitting.CardMulLeAddValEtaExprStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_mul_le_val_etaExpr_of_le_sum_val : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (k : ℕ) [Finite (LevGrp Dw k)] (J : Type) [Fintype J] (n : ℕ) (cf : J → ℤ) (xs : J → Fin n → LatMod Dw k) (F : Type) [Field F] (v : AddValuation F (WithTop ℚ)) (w : LatMod Dw k → F) (q : ℚ), (∀ (g : LevGrp Dw k) j, (q : WithTop ℚ) ≤ ∑ b, v (w (g (xs j b)))) → (((Nat.card (LevGrp Dw k) : ℚ) * q : ℚ) : WithTop ℚ) ≤ v (etaExpr k cf xs w) := by
  first | exact @GlobalTheory.EtaVal.card_mul_le_addVal_etaExpr | exact GlobalTheory.EtaVal.card_mul_le_addVal_etaExpr | (intros; apply GlobalTheory.EtaVal.card_mul_le_addVal_etaExpr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusSplitting.FibPointsMulEquiv
section -- merged from Development.AbelianVarietyTheory.Proofs.TorusSplitting.FibPointsMulEquiv
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.EtaVal

theorem exists_mulEquiv_points {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') :
    ∃ tr : (Over.mk (T.hom ≫ f) ⟶ G) ≃* (T ⟶ G'), (∀ p, (tr p).left ≫ φ = p.left) ∧
      ∀ (a : G ⟶ G) (a' : G' ⟶ G'), a'.left ≫ φ = φ ≫ a.left → ∀ p, tr (p ≫ a) = tr p ≫ a' := by
  have hl : ∀ x : T ⟶ G', (pushHom h T x).left = x.left ≫ φ := fun _ => rfl
  have hinj : ∀ x y : T ⟶ G', x.left ≫ φ = y.left ≫ φ → x = y := fun x y e =>
    Over.OverMorphism.ext (h.1.hom_ext e ((Over.w x).trans (Over.w y).symm))
  have hb : Function.Bijective (pushHom h T) := by
    refine ⟨fun x y e => hinj x y (by rw [← hl, ← hl, e]), fun p => ?_⟩
    refine ⟨Over.homMk (h.1.lift p.left T.hom (Over.w p)) (h.1.lift_snd _ _ _), ?_⟩
    exact Over.OverMorphism.ext ((hl _).trans (h.1.lift_fst _ _ _))
  have key : ∀ p, ((MulEquiv.ofBijective _ hb).symm p).left ≫ φ = p.left := fun p =>
    (hl _).symm.trans (congrArg (fun z => z.left) ((MulEquiv.ofBijective _ hb).apply_symm_apply p))
  refine ⟨(MulEquiv.ofBijective _ hb).symm, key, fun a a' e p => hinj _ _ ?_⟩
  rw [key, Over.comp_left, Over.comp_left, Category.assoc, e, ← Category.assoc, key]

theorem fib_points_mulEquiv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (R : Type) [CommRing R] [IsDomain R] [CharZero R] (x : Sp (FractionRing R) ⟶ Xo.X) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (Φ : Fib Xo x A) (F : Type) [Field F] [Algebra (FractionRing R) F] (xF : Sp F ⟶ Xo.X), xF = spMap (algebraMap (FractionRing R) F) ≫ x → ∃ tr : (ptO Xo xF ⟶ Xo.univ.t.G) ≃* (TFK (R := R) F ⟶ A.A), (∀ p, (tr p).left ≫ Φ.φ = p.left) ∧ ∀ (a : Xo.univ.t.G ⟶ Xo.univ.t.G) (a' : A.A ⟶ A.A), a'.left ≫ Φ.φ = Φ.φ ≫ a.left → ∀ p, tr (p ≫ a) = tr p ≫ a' := by
  intro E _ _ _ H Dw l Xo R _ _ _ x A Φ F _ _ xF hx
  subst hx
  exact exists_mulEquiv_points Φ.cart (TFK (R := R) F)

end GlobalTheory.EtaVal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusSplitting.FibPointsMulEquivStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mulEquiv_ptO_hom_of_eq_spMap_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (R : Type) [CommRing R] [IsDomain R] [CharZero R] (x : Sp (FractionRing R) ⟶ Xo.X) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (Φ : Fib Xo x A) (F : Type) [Field F] [Algebra (FractionRing R) F] (xF : Sp F ⟶ Xo.X), xF = spMap (algebraMap (FractionRing R) F) ≫ x → ∃ tr : (ptO Xo xF ⟶ Xo.univ.t.G) ≃* (TFK (R := R) F ⟶ A.A), (∀ p, (tr p).left ≫ Φ.φ = p.left) ∧ ∀ (a : Xo.univ.t.G ⟶ Xo.univ.t.G) (a' : A.A ⟶ A.A), a'.left ≫ Φ.φ = Φ.φ ≫ a.left → ∀ p, tr (p ≫ a) = tr p ≫ a' := by
  first | exact @GlobalTheory.EtaVal.fib_points_mulEquiv | exact GlobalTheory.EtaVal.fib_points_mulEquiv | (intros; apply GlobalTheory.EtaVal.fib_points_mulEquiv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsFibIntTh
section -- merged from Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsFibIntTh
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EtaVal

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace FibEx

theorem exists_along {X Y B : Scheme.{0}} {L : LB X} {M : LB B} {g : Y ⟶ X} {u : X ⟶ Y} (hu : u ≫ g = 𝟙 X)
    {p : Y ⟶ B} (w : LB.Iso (L.pull g) (M.pull p)) (hw : PGen w) {ψ : X ⟶ B} (hψ : u ≫ p = ψ) :
    ∃ v : LB.Iso L (M.pull ψ), PGen v ∧ ∀ (Z : Scheme.{0}) (f : Z ⟶ X) (z : Z) (j : M.ι) (k : L.ι),
      ψ (f z) ∈ M.U j → f z ∈ L.U k → Geo.Tor.gw v f z j k = Geo.Tor.gw w (f ≫ u) z j (fun _ => k) := by
  subst hψ
  have mk : ∀ (x : X) (k : L.ι), x ∈ L.U k → u x ∈ (L.pull g).U (fun _ => k) := fun x k hx =>
    mem_pull.2 ((congrArg (fun q => q x ∈ L.U k) hu).mpr hx)
  have le : ∀ (J : PUnit → M.ι) (k : L.ι), (M.pull (u ≫ p)).U J ⊓ L.U k ≤
      u ⁻¹ᵁ ((M.pull p).U J ⊓ (L.pull g).U (fun _ => k)) := fun J k x hx =>
    ⟨mem_pull.2 (mem_pull₂.1 hx.1), mk x k hx.2⟩
  let v : LB.Iso L (M.pull (u ≫ p)) := ⟨fun q => res (le q.1 q.2) (pullU u _ (w.s (q.1, fun _ => q.2)))⟩
  have hv : ∀ (Z : Scheme.{0}) (f : Z ⟶ X) (z : Z) (j : M.ι) (k : L.ι),
      (u ≫ p) (f z) ∈ M.U j → f z ∈ L.U k → Geo.Tor.gw v f z j k = Geo.Tor.gw w (f ≫ u) z j (fun _ => k) :=
    fun Z f z j k hj hk => by
      have hm : f z ∈ (M.pull (u ≫ p)).U (fun _ => j) ⊓ L.U k := ⟨mem_pull.2 hj, hk⟩
      exact (gm_res f z (le _ _) hm _).trans (gm_pull f u z _ (le _ _ hm) _)
  refine ⟨v, fun Z f z j j' k k' hj hj' hk hk' => ?_, hv⟩
  rw [hv Z f z j k hj hk, hv Z f z j' k' hj' hk',
    hw Z (f ≫ u) z j j' (fun _ => k) (fun _ => k') hj hj' (mk _ k hk) (mk _ k' hk'),
    gm_pull_g L g (f ≫ u) z _ _ (mk _ k hk) (mk _ k' hk'), Category.assoc, Category.assoc, hu, Category.comp_id]

theorem val_of_pmaps {X X' S S' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {w : LB.Iso L' (L.pull F)}
    {e : S ⟶ X} {e' : S' ⟶ X'} {h : S' ⟶ S} (he : e' ≫ F = h ≫ e) {a : LB.Gen (L'.pull e')} {t : LB.Gen (L.pull e)}
    (H : PMaps w (K := PUnit) (fun _ => e') (fun _ => e) (fun _ => 1) a t h) (z : S') {J' J}
    (hJ' : Good L' z J') (hJ : Good L z J) :
    Geo.Tor.gw w e' z (J (h ≫ e)) (J' e') * val (L := L') (φ := fun _ : PUnit => e') (ε := fun _ => 1) a (𝟙 _) z J' =
      val (L := L) (φ := fun _ : PUnit => e) (ε := fun _ => 1) t h z J := by
  have k := H _ (𝟙 _) z (fun _ => J (h ≫ e)) (fun _ => J' e')
    (fun _ => (congrArg (fun q => q z ∈ L.U (J (h ≫ e))) he).mpr (hJ (h ≫ e))) (fun _ => hJ' e')
  rw [Fintype.prod_unique, zpow_one, Category.id_comp, Category.id_comp] at k
  rw [val_of a (𝟙 _) z J' (fun _ => J' e') (fun _ => by rw [Category.id_comp])]
  exact k.symm

theorem gs_isoMaps {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {w : LB.Iso L' (L.pull F)}
    {σ : LB.Sec L'} {s : LB.Sec (L.pull F)} (h : IsoMaps w σ s) (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) (j : L.ι)
    (k : L'.ι) (hj : F (r z) ∈ L.U j) (hk : r z ∈ L'.U k) :
    gs r z _ (s.f (fun _ => j)) = (Geo.Tor.gw w r z j k).val * gs r z _ (σ.f k) := by
  have hz : r z ∈ (L.pull F).U (fun _ => j) ⊓ L'.U k := ⟨mem_pull.2 hj, hk⟩
  have a := congrArg (gs r z _) (h (fun _ => j) k)
  exact (gs_res _ z _ hz _).symm.trans (a.trans ((gs_mul _ z _ hz _ _).trans
    (congrArg₂ (· * ·) (gs_unit _ z _ hz _) (gs_res _ z _ hz _))))

theorem exists_sec_one {X : Scheme.{0}} {L : LB X} (θ : LB.Sec L) :
    ∃ σ : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => ((1 : ℕ) : ℤ))),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (J), Good L z J → sval σ r z J = gs r z _ (θ.f (J (r ≫ 𝟙 _))) := by
  refine ⟨thfPull1 L (𝟙 X) (Category.id_comp _) (thfPull L (𝟙 X) θ), fun Z r z J hJ => ?_⟩
  have h₁ := hJ.mem (fun _ : Fin 1 => 𝟙 X) r
  have h₂ : (r ≫ 𝟙 X) z ∈ (L.pull (𝟙 X)).U (fun _ => J (r ≫ 𝟙 _)) := chart_le_pullback_open L (𝟙 X) (Category.id_comp _) _ h₁
  refine (gs_appLE (𝟙 X) _ _ _ r z h₁ _).trans ((gs_appLE (𝟙 X) _ _ _ (r ≫ 𝟙 X) z h₂ _).trans ?_)
  simp only [Category.comp_id]

theorem core {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
    (U : UnifPre I D A G) (PP : RigLB G) (hPP : U.LG = PP)
    {T : Over (Spec (CommRingCat.of (FractionRing R)))} [GrpObj T] [IsCommMonObj T] (L' : RigLB T)
    {φ : T.left ⟶ G.left} (cart : IsGrpPullback T G (jK R) φ) (w : LB.Iso L'.L (PP.L.pull φ)) (hw : PGen w)
    (hr : PMaps w (K := PUnit) (fun _ => eSec T) (fun _ => eSec G) (fun _ => 1) L'.rig PP.rig (jK R))
    (θ : LB.Sec PP.L) (σ : LB.Sec L'.L)
    (hθ : ∀ (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) j k, φ (r z) ∈ PP.L.U j → r z ∈ L'.L.U k →
      gs (r ≫ φ) z _ (θ.f j) = (Geo.Tor.gw w r z j k).val * gs r z _ (σ.f k)) :
    ∃ (κ : A.A ≅ T) (_ : IsMonHom κ.hom) (_ : κ.hom.left ≫ φ = U.gen.inv.left ≫ pullback.fst G.hom (jK R))
      (w' : LB.Iso A.L (L'.L.pull κ.hom.left)) (ρ : LB.Gen (A.L.pull (eSec A.A))) (w₀ : GlobalTheory.UT.W0 U), PGen w' ∧
      PMaps w' (K := PUnit) (fun _ => eSec A.A) (fun _ => eSec T) (fun _ => 1) ρ L'.rig (𝟙 _) ∧
      GlobalTheory.UT.NormW U w₀ ρ ∧
      ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (th : GlobalTheory.UT.SecA A F 1),
        (∀ (Z : Scheme.{0}) (r : Z ⟶ (TFK (R := R) F ⊗ A.A).left) (z : Z) (JA) (i : L'.L.ι), Good A.L z JA →
          κ.hom.left ((r ≫ (snd (TFK (R := R) F) A.A).left) z) ∈ L'.L.U i →
          gs ((r ≫ (snd (TFK (R := R) F) A.A).left) ≫ κ.hom.left) z _ (σ.f i) =
            (Geo.Tor.gw w' (r ≫ (snd (TFK (R := R) F) A.A).left) z i
              (JA (r ≫ (snd (TFK (R := R) F) A.A).left))).val * GlobalTheory.UT.sA th r z JA) → IntTh U w₀ th := by
  subst hPP
  have := U.gen_hom
  have hi : IsMonHom U.gen.symm.hom := inferInstanceAs (IsMonHom U.gen.inv)
  have hA : IsGrpPullback A.A G (jK R) (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) :=
    ((isGrpPullback_of_iso U.gen.symm).comp (isGrpPullback_pullback G (jK R))).congr (Category.id_comp _) rfl
  obtain ⟨κ, hκ, eκ⟩ := grpPullback_iso hA cart
  obtain ⟨w₀, g₀⟩ := U.ext
  have ug : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, U.gen.inv_hom_id, Over.id_left]
  have gu : U.gen.hom.left ≫ U.gen.inv.left = 𝟙 _ := by rw [← Over.comp_left, U.gen.hom_inv_id, Over.id_left]
  obtain ⟨v, gv', hv⟩ := exists_along ug w₀ ((isGen_iff w₀).1 g₀) eκ.symm
  obtain ⟨w', Tr⟩ := exists_cancel U.LG.isLB w v hw gv' L'.isLB A.isLB
  have g' := Tr.pgen_cancel U.LG.isLB hw gv'
  have e₁ : eSec A.A ≫ κ.hom.left = 𝟙 _ ≫ eSec T := (cubeMapOf (isGrpPullback_of_iso κ)).e_comm
  have e₂ : eSec A.A ≫ U.gen.inv.left = 𝟙 _ ≫ eSec ((Over.pullback (jK R)).obj G) :=
    (cubeMapOf (isGrpPullback_of_iso U.gen.symm)).e_comm
  have e₃ : eSec A.A ≫ κ.hom.left ≫ φ = (𝟙 _ ≫ jK R) ≫ eSec G := by
    rw [eκ, Category.id_comp]; exact (cubeMapOf hA).e_comm
  obtain ⟨ρ, gρ, hρ⟩ := H1.exists_gen_move L'.isLB A.isLB w' g' (K := PUnit) (fun _ => eSec T) (fun _ => eSec A.A)
    (fun _ => 1) (𝟙 _) (fun _ => e₁) L'.rig L'.rigGen
  refine ⟨κ, hκ, eκ, w', ρ, w₀, g', hρ, ⟨g₀, gρ, fun z JA JG hA' hG => ?_⟩, fun F _ _ th H => ?_⟩
  · have k := val_of_pmaps e₃ (Tr.pmaps_comp L'.isLB (fun _ => e₁) hr hρ) z hA' hG
    rw [hv _ _ z _ _ ((congrArg (fun q => q z ∈ U.LG.L.U (JG _)) e₃).mpr (hG _)) (hA' _), e₂,
      Category.id_comp, Category.id_comp] at k
    exact k
  · obtain ⟨σ₁, h₁⟩ := exists_sec_one θ
    refine ⟨g₀, σ₁, fun Z r z JA JG hA' hG => ?_⟩
    rw [h₁ _ _ z JG hG]
    have q₁ : (U.genF F).left ≫ (snd (TFK (R := R) F) A.A).left =
        (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left ≫ U.gen.hom.left :=
      congrArg (fun q => q.left) (lift_snd (fst _ _) (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G) ≫ U.gen.hom))
    have H' := fun i => H Z (r ≫ (U.genF F).left) z JA i hA'
    have q₂ : ((r ≫ (U.genF F).left) ≫ (snd (TFK (R := R) F) A.A).left) ≫ U.gen.inv.left =
        r ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left := by
      rw [Category.assoc r, q₁, Category.assoc, Category.assoc, gu, Category.comp_id]
    have q₃ : r ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left ≫ pullback.fst G.hom (jK R) =
        (((r ≫ (U.genF F).left) ≫ (snd (TFK (R := R) F) A.A).left) ≫ κ.hom.left) ≫ φ := by
      rw [Category.assoc _ κ.hom.left, eκ, ← Category.assoc _ U.gen.inv.left, q₂, Category.assoc]
    rw [q₃, ← q₂]
    generalize (r ≫ (U.genF F).left) ≫ (snd (TFK (R := R) F) A.A).left = a at H' ⊢
    obtain ⟨i, hi'⟩ := exists_chart L'.isLB (κ.hom.left (a z))
    have hj : φ (κ.hom.left (a z)) ∈ U.LG.L.U (JG (((a ≫ κ.hom.left) ≫ φ) ≫ 𝟙 _)) := hG (((a ≫ κ.hom.left) ≫ φ) ≫ 𝟙 _)
    rw [hθ Z (a ≫ κ.hom.left) z _ i hj hi', H' i hi', ← hv Z a z _ _ hj (hA' a), Tr Z a z _ i _ hj hi' (hA' a),
      Units.val_mul, _root_.mul_assoc]

theorem rigIso_pt {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {X Y : Scheme.{0}}
    {t₁ : SAB H Y} {t : SAB H X} {f : Y ⟶ X} {m : SABMap t₁ t f} {w : LB.Iso t₁.PP.L (t.PP.L.pull m.φ)}
    (h : RigIso m w) : PGen w ∧
      PMaps w (K := PUnit) (fun _ => eSec t₁.G) (fun _ => eSec t.G) (fun _ => 1) t₁.PP.rig t.PP.rig f := by
  refine ⟨(isGen_iff w).1 h.1, ?_⟩
  have := (maps_iff w _ (fun _ => eSec t.G) _ t₁.PP.rig t.PP.rig m.cm.e _
    (rigPull_le m.cm.F m.cm.e m.cm.e_comm t.PP.L) (fun _ => rfl)).1 h.2
  rwa [m.base] at this

end FibEx


open FibEx in
theorem exists_fib_intTh : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [Algebra c.F (FractionRing V)] (y : FrPt Xo c (FractionRing V)) (G : SAB H (Sp V)) (_ : IntSec Xo V y.x y.s G) (P : PELUnif (maximalIdeal V) G), ∃ (Φ : Fib Xo y.x P.A) (w₀ : GlobalTheory.UT.W0 P.U.toUnifPre), GlobalTheory.UT.NormW P.U.toUnifPre w₀ Φ.ρ ∧ (∀ a : 𝓞 E, ((letI := H.starRing; P.oA.act a : P.A.A ⟶ P.A.A)).left ≫ Φ.φ = Φ.φ ≫ (Xo.univ.t.act.act a).left) ∧ ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] [Algebra c.F F] (ψ : FractionRing V →ₐ[c.F] F) (z : FrPt Xo c F) (th : GlobalTheory.UT.SecA P.A F 1), ψ.toRingHom = algebraMap (FractionRing V) F → FrMap ψ y z → Φ.SecTie z.x z.s th → IntTh P.U.toUnifPre w₀ th := by
  intro E _ _ _ H Dw l Xo c V _ _ _ _ y G I P
  obtain ⟨g₁, r₁⟩ := rigIso_pt I.rig1
  obtain ⟨g₂, r₂⟩ := rigIso_pt I.rig2
  have hL := Xo.univ.t.PP.isLB
  have hL' := I.t'.PP.isLB
  obtain ⟨κ, hκ, eκ, w', ρ, w₀, g', hρ, hN, hI⟩ := core P.U.toUnifPre G.PP P.bundle I.t'.PP I.m2.cart I.w2 g₂ r₂ I.θ I.σ
    (fun Z r z j k hj hk => by
      have le : (G.PP.L.pull I.m2.φ).U (fun _ => j) ≤ I.m2.φ ⁻¹ᵁ G.PP.L.U j := fun q hq => mem_pull.1 hq
      refine Eq.trans ?_ (gs_isoMaps I.maps2 Z r z j k hj hk)
      rw [I.pull (fun _ => j) le]
      exact (gs_appLE I.m2.φ _ _ le r z (mem_pull.2 hj) _).symm)
  obtain ⟨ω, Tr⟩ := exists_comp hL' I.w1 w' g₁ g' hL P.A.isLB
  have cart : IsGrpPullback P.A.A Xo.univ.t.G y.x (κ.hom.left ≫ I.m1.φ) :=
    ((isGrpPullback_of_iso κ).comp I.m1.cart).congr (Category.id_comp _) rfl
  have e₁ : eSec P.A.A ≫ κ.hom.left = 𝟙 _ ≫ eSec I.t'.G := (cubeMapOf (isGrpPullback_of_iso κ)).e_comm
  have hω := Tr.pmaps_comp hL' (fun _ => e₁) r₁ hρ
  rw [Category.id_comp] at hω
  refine ⟨⟨κ.hom.left ≫ I.m1.φ, cart, ω, (isGen_iff ω).2 (Tr.pgen_comp hL' g₁ g'), ρ, hN.2.1,
    fun z JA J hA hJ => val_of_pmaps (cubeMapOf cart).e_comm hω z hA hJ⟩, w₀, hN, fun a => ?_,
    fun F _ _ _ ψ z th hψ hm hT => hI F th fun Z r p JA i hA hi => ?_⟩
  · let _ := H.starRing
    have x₁ : P.oA.act a ≫ P.U.gen.inv = P.U.gen.inv ≫ (Over.pullback (jK V)).map (G.act.act a) := by
      rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
      exact (P.lin.ext a).symm
    have x₂ : ((Over.pullback (jK V)).map (G.act.act a)).left ≫ pullback.fst G.G.hom (jK V) =
        pullback.fst G.G.hom (jK V) ≫ (G.act.act a).left := pullback.lift_fst _ _ _
    have x₃ : (P.oA.act a).left ≫ κ.hom.left = κ.hom.left ≫ (I.t'.act.act a).left := by
      apply I.m2.cart.1.hom_ext
      · rw [Category.assoc, Category.assoc, I.m2.act, ← Category.assoc κ.hom.left, eκ, ← Category.assoc,
          ← Over.comp_left, x₁, Over.comp_left, Category.assoc, x₂, Category.assoc]
      · simp only [Category.assoc, Over.w]
    show (P.oA.act a).left ≫ κ.hom.left ≫ I.m1.φ = (κ.hom.left ≫ I.m1.φ) ≫ _
    rw [← Category.assoc, x₃, Category.assoc, I.m1.act, Category.assoc]
  · obtain ⟨hx, -, pm, pm₁, pm₂, hpm⟩ := hm
    let a0 : Over.mk (I.t'.G.hom ≫ y.x) ⟶ Over.mk y.x := Over.homMk I.t'.G.hom rfl
    let b0 : Over.mk (I.t'.G.hom ≫ y.x) ⟶ Xo.univ.t.G := Over.homMk I.m1.φ I.m1.cart.1.w
    let g : I.t'.G.left ⟶ Gx y.x := (lift a0 b0).left
    have gf : g ≫ (fst (Over.mk y.x) Xo.univ.t.G).left = I.t'.G.hom := congrArg (fun q => q.left) (lift_fst a0 b0)
    have gs' : g ≫ (snd (Over.mk y.x) Xo.univ.t.G).left = I.m1.φ := congrArg (fun q => q.left) (lift_snd a0 b0)
    clear_value g
    let p₁ : (TFK (R := V) F ⊗ P.A.A).left ⟶ Sp F := (fst (TFK (R := V) F) P.A.A).left
    let a : Z ⟶ P.A.A.left := r ≫ (snd (TFK (R := V) F) P.A.A).left
    have hj : spMap ψ.toRingHom = jFK (R := V) F := by rw [hψ]
    have a2 : (r ≫ p₁) ≫ spMap ψ.toRingHom = a ≫ P.A.A.hom := by
      rw [hj, Category.assoc, Category.assoc]
      exact congrArg (r ≫ ·) ((Over.w (fst (TFK (R := V) F) P.A.A)).trans (Over.w (snd (TFK (R := V) F) P.A.A)).symm)
    have w : (r ≫ p₁) ≫ z.x = (a ≫ κ.hom.left ≫ I.m1.φ) ≫ Xo.univ.t.G.hom := by
      rw [hx, ← Category.assoc, a2, Category.assoc a, Category.assoc a, cart.1.w]
    let r' : Z ⟶ Gx z.x := pullback.lift (r ≫ p₁) (a ≫ κ.hom.left ≫ I.m1.φ) w
    have h1 : r' ≫ (fst (Over.mk z.x) Xo.univ.t.G).left = r ≫ p₁ := pullback.lift_fst _ _ _
    have h2 : r' ≫ (snd (Over.mk z.x) Xo.univ.t.G).left = a ≫ κ.hom.left ≫ I.m1.φ := pullback.lift_snd _ _ _
    clear_value r'
    have e : r' ≫ pm = (a ≫ κ.hom.left) ≫ g := by
      apply pullback.hom_ext
      · show (r' ≫ pm) ≫ (fst (Over.mk y.x) Xo.univ.t.G).left = (_ ≫ g) ≫ (fst (Over.mk y.x) Xo.univ.t.G).left
        rw [Category.assoc, pm₂, ← Category.assoc, h1, Category.assoc _ g, gf, Category.assoc a, Over.w]
        exact a2
      · show (r' ≫ pm) ≫ (snd (Over.mk y.x) Xo.univ.t.G).left = (_ ≫ g) ≫ (snd (Over.mk y.x) Xo.univ.t.G).left
        rw [Category.assoc, pm₁, Category.assoc _ g, gs']
        exact h2.trans (Category.assoc _ _ _).symm
    obtain ⟨J, hJ, -⟩ := exists_good Xo.univ.t.PP.L hL p (K := PEmpty) PEmpty.elim PEmpty.elim (fun a => a.elim)
      (fun a => a.elim)
    have k := hT.2 Z r r' (h2.trans (Category.assoc _ _ _)) h1 p JA J hA hJ
    have mz := hJ.mem (fun _ : Fin 1 => (snd (Over.mk z.x) Xo.univ.t.G).left) r'
    have mj : I.m1.φ (κ.hom.left (a p)) ∈ Xo.univ.t.PP.L.U (J (r' ≫ (snd (Over.mk z.x) Xo.univ.t.G).left)) := by
      rw [h2]; exact hJ (a ≫ κ.hom.left ≫ I.m1.φ)
    unfold sval at k
    beta_reduce at k
    generalize J (r' ≫ (snd (Over.mk z.x) Xo.univ.t.G).left) = j at k mz mj
    have le₁ : (PPx z.x).U (fun _ => j) ≤ pm ⁻¹ᵁ (PPx y.x).U (fun _ => j) := fun q hq =>
      Set.mem_iInter.2 fun _ => (congrArg (fun u => u q ∈ Xo.univ.t.PP.L.U j) pm₁).mpr (Set.mem_iInter.1 hq 0)
    have le₂ : (Xo.univ.t.PP.L.pull I.m1.φ).U (fun _ => j) ≤ g ⁻¹ᵁ (PPx y.x).U (fun _ => j) := fun q hq =>
      Set.mem_iInter.2 fun _ => (congrArg (fun u => u q ∈ Xo.univ.t.PP.L.U j) gs').mpr (mem_pull.1 hq)
    have k₁ : gs r' p ((PPx z.x).U (fun _ => j)) (z.s.f (fun _ => j)) =
        gs (r' ≫ pm) p ((PPx y.x).U (fun _ => j)) (y.s.f (fun _ => j)) :=
      (congrArg (gs r' p _) (hpm (fun _ => j) le₁).symm).trans (gs_appLE pm _ _ le₁ r' p mz _)
    have k₂ : gs (a ≫ κ.hom.left) p _ (I.s1.f (fun _ => j)) =
        gs ((a ≫ κ.hom.left) ≫ g) p ((PPx y.x).U (fun _ => j)) (y.s.f (fun _ => j)) :=
      (congrArg (gs (a ≫ κ.hom.left) p _) (I.gen1 g gs' gf (fun _ => j) le₂)).trans
        (gs_appLE g _ _ le₂ (a ≫ κ.hom.left) p (mem_pull.2 mj) _)
    have k₃ := gs_isoMaps I.maps1 Z (a ≫ κ.hom.left) p j i mj hi
    have k₄ := Tr Z a p j i (JA a) mj hi (hA a)
    rw [e, ← k₂, k₃] at k₁
    have k₅ := k₁.symm.trans (k.trans (congrArg (fun u => u.val * GlobalTheory.UT.sA th r p JA) k₄))
    rw [Units.val_mul, _root_.mul_assoc] at k₅
    exact (Units.mul_right_inj _).1 k₅

end GlobalTheory.EtaVal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsFibIntThStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fib_normW_of_intSec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [Algebra c.F (FractionRing V)] (y : FrPt Xo c (FractionRing V)) (G : SAB H (Sp V)) (_ : IntSec Xo V y.x y.s G) (P : PELUnif (maximalIdeal V) G), ∃ (Φ : Fib Xo y.x P.A) (w₀ : GlobalTheory.UT.W0 P.U.toUnifPre), GlobalTheory.UT.NormW P.U.toUnifPre w₀ Φ.ρ ∧ (∀ a : 𝓞 E, ((letI := H.starRing; P.oA.act a : P.A.A ⟶ P.A.A)).left ≫ Φ.φ = Φ.φ ≫ (Xo.univ.t.act.act a).left) ∧ ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] [Algebra c.F F] (ψ : FractionRing V →ₐ[c.F] F) (z : FrPt Xo c F) (th : GlobalTheory.UT.SecA P.A F 1), ψ.toRingHom = algebraMap (FractionRing V) F → FrMap ψ y z → Φ.SecTie z.x z.s th → IntTh P.U.toUnifPre w₀ th := by
  first | exact @GlobalTheory.EtaVal.exists_fib_intTh | exact GlobalTheory.EtaVal.exists_fib_intTh | (intros; apply GlobalTheory.EtaVal.exists_fib_intTh <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusSplitting.SumCosetMinGePhiCDivSq
section -- merged from Development.AbelianVarietyTheory.Proofs.TorusSplitting.SumCosetMinGePhiCDivSq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EtaVal

theorem sum_cosetMin_ge_phiC_div_sq : ∀ (E : Type) [Field E] [NumberField E] (cj : E → E), (∀ c : 𝓞 E, ∃ c' : 𝓞 E, (c' : E) = cj c) → ∀ w₀ : 𝓞 E, (w₀ : E) + cj w₀ = 1 → ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite ℤ X] (Q : X → ℤ) (β : Formalism.MainNotions.ModuliIntegralCharts.SymB cj X), (∀ a, (β : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) a a = 2 * (Q a : ℝ)) → (∀ a, 0 ≤ Q a) → ∀ (m : ℕ), 2 ≤ m → ∀ (n : ℕ) (y : Fin n → X), (∀ a : X, ∃ u ∈ Submodule.span (𝓞 E) (Set.range y), ∃ t : X, a = u + m ^ 2 • t) → ∀ v : Fin n → WithTop ℚ, (∀ b (q : ℚ), (∀ χ, q ≤ (Q (m • χ + y b) : ℚ) / (m ^ 2 : ℕ)) → (q : WithTop ℚ) ≤ v b) → ∀ q : ℚ, (q : ℝ) ≤ Formalism.MainNotions.ModuliIntegralCharts.phiC cj β / (m : ℝ) ^ 2 → (q : WithTop ℚ) ≤ ∑ b, v b := by
  intro E _ _ cj hcj w₀ hw X _ _ _ Q β hβQ hQnn m hm n y hgen v hv q hq
  have hβpos : ∀ a, 0 ≤ (β : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) a a := fun a => by
    rw [hβQ a]
    have h' : (0 : ℝ) ≤ Q a := by exact_mod_cast hQnn a
    linarith
  choose z hz using fun b => Formalism.MainNotions.ModuliIntegralCharts.H1.etPoint_min Q hQnn (y b) m
  have hgen' : ∀ a : X, ∃ u ∈ Submodule.span (𝓞 E) (Set.range y), ∃ t : X, a = u + m • t := fun a => by
    obtain ⟨u, hu, t, ht⟩ := hgen a
    exact ⟨u, hu, m • t, by rw [ht, smul_smul, pow_two]⟩
  have hspan := Formalism.MainNotions.ModuliIntegralCharts.H1.etSpan_holds E X m hm n y z hgen'
  have hphi := Formalism.MainNotions.ModuliIntegralCharts.H1.phiCSpan_holds E cj hcj X w₀ hw β hβpos n (fun b => y b + m • z b) hspan
  have hsum : Formalism.MainNotions.ModuliIntegralCharts.phiC cj β ≤ ∑ b, (Q (y b + m • z b) : ℝ) := by
    refine hphi.trans (le_of_eq (Finset.sum_congr rfl fun b _ => ?_))
    have h := Formalism.MainNotions.ModuliIntegralCharts.H1.two_mul_form_half_unit hcj w₀ hw β (y b + m • z b)
    rw [hβQ] at h
    linarith
  have hpt : ∀ b, (((Q (y b + m • z b) : ℚ) / ((m ^ 2 : ℕ) : ℚ) : ℚ) : WithTop ℚ) ≤ v b := by
    intro b
    refine hv b _ fun z' => ?_
    have h : (Q (y b + m • z b) : ℚ) ≤ (Q (m • z' + y b) : ℚ) := by
      rw [add_comm (m • z')]
      exact_mod_cast hz b z'
    exact div_le_div_of_nonneg_right h (by positivity)
  have hR : (0 : ℝ) < (m : ℝ) ^ 2 := by
    have : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    positivity
  have hqR : (q : ℝ) ≤ ((∑ b, (Q (y b + m • z b) : ℚ) / ((m ^ 2 : ℕ) : ℚ) : ℚ) : ℝ) := by
    push_cast
    rw [← Finset.sum_div]
    exact hq.trans (div_le_div_of_nonneg_right hsum hR.le)
  have hqQ : q ≤ ∑ b, (Q (y b + m • z b) : ℚ) / ((m ^ 2 : ℕ) : ℚ) := by exact_mod_cast hqR
  calc ((q : ℚ) : WithTop ℚ) ≤ ((∑ b, (Q (y b + m • z b) : ℚ) / ((m ^ 2 : ℕ) : ℚ) : ℚ) : WithTop ℚ) :=
        WithTop.coe_le_coe.2 hqQ
    _ = ∑ b, (((Q (y b + m • z b) : ℚ) / ((m ^ 2 : ℕ) : ℚ) : ℚ) : WithTop ℚ) := WithTop.coe_sum _ _
    _ ≤ ∑ b, v b := Finset.sum_le_sum fun b _ => hpt b

end GlobalTheory.EtaVal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusSplitting.SumCosetMinGePhiCDivSqStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.le_sum_of_le_phiC_div_sq : ∀ (E : Type) [Field E] [NumberField E] (cj : E → E), (∀ c : 𝓞 E, ∃ c' : 𝓞 E, (c' : E) = cj c) → ∀ w₀ : 𝓞 E, (w₀ : E) + cj w₀ = 1 → ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite ℤ X] (Q : X → ℤ) (β : Formalism.MainNotions.ModuliIntegralCharts.SymB cj X), (∀ a, (β : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) a a = 2 * (Q a : ℝ)) → (∀ a, 0 ≤ Q a) → ∀ (m : ℕ), 2 ≤ m → ∀ (n : ℕ) (y : Fin n → X), (∀ a : X, ∃ u ∈ Submodule.span (𝓞 E) (Set.range y), ∃ t : X, a = u + m ^ 2 • t) → ∀ v : Fin n → WithTop ℚ, (∀ b (q : ℚ), (∀ χ, q ≤ (Q (m • χ + y b) : ℚ) / (m ^ 2 : ℕ)) → (q : WithTop ℚ) ≤ v b) → ∀ q : ℚ, (q : ℝ) ≤ Formalism.MainNotions.ModuliIntegralCharts.phiC cj β / (m : ℝ) ^ 2 → (q : WithTop ℚ) ≤ ∑ b, v b := by
  first | exact @GlobalTheory.EtaVal.sum_cosetMin_ge_phiC_div_sq | exact GlobalTheory.EtaVal.sum_cosetMin_ge_phiC_div_sq | (intros; apply GlobalTheory.EtaVal.sum_cosetMin_ge_phiC_div_sq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsExpansionNonneg
section -- merged from Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsExpansionNonneg
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EtaVal

theorem secLin_one {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ₁ : K' → (Y' ⟶ X)} {ε₁ : K' → ℤ} {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)} {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {s : LB.Sec (LB.LinComb L φ ε)} {h : Y' ⟶ Y} {F : Type} [CommRing F] (p : Y' ⟶ Spec (CommRingCat.of F))
    (H : ∀ y J, Good L y J → sval s₁ (𝟙 Y') y J = sval s (𝟙 Y' ≫ h) y J) :
    GeneratorPullback.SecLin L φ₁ ε₁ s₁ φ ε (fun _ : Fin 1 => s) h (fun _ => ReciprocityTheory.ChartRestriction.G.Out.scal p (1 : F)) := by
  refine (GlobalTheory.FieldBaseChange.secLin_iff_val hL _ _ _ _).2 fun y J hJ => ?_
  rw [Fin.sum_univ_one, H y J hJ, ReciprocityTheory.ChartRestriction.G.Out.scal, map_one, map_one, gs_eq _ y ⊤ trivial, map_one, map_one,
    _root_.one_mul]

theorem exists_expansion_nonneg : GlobalTheory.UT.AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ (w₀ : GlobalTheory.UT.W0 U.toUnifPre), w₀.IsGen → ∀ th : GlobalTheory.UT.SecA A F 1, IntTh U.toUnifPre w₀ th → ∃ ϑ : Fam D.toPre F 1, U.ExpandsF F 1 w₀ th ϑ ∧ NuGe D Q F v 1 ϑ 0 := by
  intro V _ _ _ _ _ ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ _ U w₀ _ th ⟨_, σ, hσ⟩
  let s : U.toUnifPre.SecK 1 := GlobalTheory.FieldBaseChange.pullOver (π := G.hom) (π' := pullback.snd G.hom (jK V)) U.LG.L _
    (p := pullback.fst G.hom (jK V)) pullback.condition (fun _ => (Category.comp_id _).symm) σ
  have hs : GeneratorPullback.SecScal U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK V)) (fun _ => ((1 : ℕ) : ℤ)) s
      (fun _ : Fin 1 => 𝟙 G.left) (fun _ => ((1 : ℕ) : ℤ)) σ (pullback.fst G.hom (jK V)) 1 :=
    SectionScalarValuation.secScal_of_sval U.LG.isLB fun y J hJ => (GlobalTheory.FieldBaseChange.sval_pullOver _ _ _ _ hJ).symm
  obtain ⟨E, hE⟩ := ((U.expand 1 le_rfl).1 s).exists
  obtain ⟨g, hg, hgE⟩ := GlobalTheory.ExpInt.main V ϖ hϖ D A G U.toUnifPre 1 σ s hs E hE
  obtain ⟨ϑ, hϑ⟩ := GlobalTheory.FamBaseChange.main GlobalTheory.ExpansionTotal.globalFns V _ D 1 E g hgE F
  refine ⟨ϑ, ?_, (GlobalTheory.integralFamily_levelOne V ϖ hϖ D Q hQ F v hv ϑ g hϑ).1⟩
  obtain ⟨σ', hσ'⟩ := GlobalTheory.BoxExpansion.exists_secLin U.LG.isLB
    (fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G)).left (UnifPre.gFK (G := G) F)
    (fun _ : Fin 1 => UnifPre.gFK (G := G) F) (φ := fun _ : Fin 1 => 𝟙 G.left) (fun _ => (Category.comp_id _).symm)
    (fun _ : Fin 1 => σ) (fun _ => (1 : F))
  refine ⟨σ', ?_, 1, fun _ => 1, fun _ => σ, fun _ => g, fun _ => hg, hσ', fun α => ?_⟩
  · have e₁ : (U.genF F).left ≫ (snd (TFK (R := V) F) A.A).left =
        (snd (TFK (R := V) F) ((Over.pullback (jK V)).obj G)).left ≫ U.gen.hom.left :=
      congrArg (fun q => q.left) (lift_snd _ _ : U.genF F ≫ snd _ _ = _)
    refine GlobalTheory.BoxExpansion.isoRel_of_val A.isLB U.LG.isLB e₁ (Category.id_comp _) fun y J₁ J₂ h₁ h₂ => ?_
    have a := GlobalTheory.BoxExpansion.secLin_val hσ' (𝟙 _) y h₂
    rw [Fin.sum_univ_one, ReciprocityTheory.ChartRestriction.G.Out.scal, map_one, map_one, gs_eq _ y ⊤ trivial, map_one, map_one,
      _root_.one_mul] at a
    have b := hσ _ (𝟙 _) y J₁ J₂ h₁ h₂
    simp only [Category.id_comp, Category.comp_id] at a b
    rw [e₁] at b
    rw [pow_one]
    exact a.trans b
  · exact secLin_one D.toPre.P.isLB _ fun y J hJ => (SectionScalarValuation.secScal_sval (hϑ α) _ y hJ).symm

end GlobalTheory.EtaVal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsExpansionNonnegStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_expandsF_nuGe_zero_of_intTh : GlobalTheory.UT.AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ (w₀ : GlobalTheory.UT.W0 U.toUnifPre), w₀.IsGen → ∀ th : GlobalTheory.UT.SecA A F 1, IntTh U.toUnifPre w₀ th → ∃ ϑ : Fam D.toPre F 1, U.ExpandsF F 1 w₀ th ϑ ∧ NuGe D Q F v 1 ϑ 0 := by
  first | exact @GlobalTheory.EtaVal.exists_expansion_nonneg | exact GlobalTheory.EtaVal.exists_expansion_nonneg | (intros; apply GlobalTheory.EtaVal.exists_expansion_nonneg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusSplitting.CardMulPhiLeValuationProductForm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EtaVal

theorem mul_le_of_forall_rat_le (N : ℕ) (hN : 0 < N) (x : ℝ) (a : ℤ)
    (h : ∀ q : ℚ, (q : ℝ) ≤ x → (N : ℚ) * q ≤ (a : ℚ)) : (N : ℝ) * x ≤ (a : ℝ) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  by_contra hc
  have h1 : (a : ℝ) / N < x := by
    rw [div_lt_iff₀ hN', mul_comm]; exact not_le.mp hc
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn h1
  have h2 : (N : ℝ) * (q : ℝ) ≤ (a : ℝ) := by exact_mod_cast h q hq2.le
  rw [div_lt_iff₀ hN', mul_comm] at hq1
  linarith


set_option maxHeartbeats 1000000 in
theorem card_mul_phiC_le_valuation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V] [IsAdicComplete (maximalIdeal V) V] [Algebra c.F (FractionRing V)] (y : FrPt Xo c (FractionRing V)) (G : SAB H (Sp V)) (_ : IntSec Xo V y.x y.s G) (P : PELUnif (maximalIdeal V) G) (ϖ : V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), QForm.IsQ P.D.toPre ϖ Q → (∀ a, 0 ≤ Q a) → ∀ (cj : E → E), (∀ a, cj a = IsCMField.complexConj E a) → ∀ (β : Formalism.MainNotions.ModuliIntegralCharts.SymB cj P.D.toPre.X), (∀ a, (β : _ →ₗ[ℤ] _ →ₗ[ℤ] ℝ) a a = 2 * (Q a : ℝ)) → ∀ (R : ℕ), Odd R → 1 < R → ∀ (J : Type) [Fintype J] (n : ℕ) (cf : J → ℤ) (xs : J → Fin n → LatMod Dw (R ^ 4)) (val : FractionRing V), GlobalTheory.EtaAn.Spans xs → EtaValAt Xo c R cf xs y val → val ≠ 0 → (Nat.card (LevGrp Dw (R ^ 4)) : ℝ) / (R : ℝ) ^ 4 * Formalism.MainNotions.ModuliIntegralCharts.phiC cj β ≤ (vV V val : ℝ) := by
  intro E _ _ _ H Dw l Xo c V _ _ _ _ hcpl _ y G S P ϖ hϖ Q hQ hQ0 cj hcj β hβ R hR hR1 J _ n cf xs val hsp hval hne
  obtain ⟨hLL, h2, h3, h4, h5⟩ := GlobalTheory.lawsAndExpansions
  have hL : Laws := hLL.1
  have hA : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hcpl⟩
  have htors := GlobalTheory.UT.torsionIso_of_pelUnif hLL h2 h3 h4 h5 E H V _ hA G P
  haveI hfin : Finite (LevGrp Dw (R ^ 4)) := (GlobalTheory.EtaCard.card_levGrp_and_span E H Dw R hR1).1
  obtain ⟨v, hv, hvv⟩ := GlobalTheory.T.exists_valuation_algebraicClosure_extending_vV V ϖ hϖ
  let F := AlgebraicClosure (FractionRing V)
  letI : Algebra c.F F := ((algebraMap (FractionRing V) F).comp (algebraMap c.F (FractionRing V))).toAlgebra
  let ψ : FractionRing V →ₐ[c.F] F := { algebraMap (FractionRing V) F with commutes' := fun _ => rfl }
  have hψ : ψ.toRingHom = algebraMap (FractionRing V) F := rfl
  obtain ⟨z, hz⟩ := GlobalTheory.FramedBaseChange.exists_frMap hL E H Dw l Xo c _ F ψ y
  have hzx : z.x = spMap (algebraMap (FractionRing V) F) ≫ y.x := hz.1
  have hR0 : 0 < R := by omega
  have e4 : (R ^ 2) ^ 2 = R ^ 4 := by rw [← pow_mul]
  have hR2 : Odd (R ^ 2) := hR.pow
  obtain ⟨-, hbc, hloc, hex⟩ := GlobalTheory.fullLevel_cover_baseChange_torsor hL E H Dw l Xo (R ^ 4) (pow_pos hR0 4)
  obtain ⟨ev, hev⟩ := hex F z.x
  have hevt : ∀ q, ev q ^ ((R ^ 2) ^ 2) = 1 := by
    rw [e4]
    exact (hbc F F (RingHom.id F) z.x z.x (𝟙 _) (by simp [spMap]) ev hev).2
  have hevs : ∀ p : ptO Xo z.x ⟶ Xo.univ.t.G, p ^ ((R ^ 2) ^ 2) = 1 → ∃ q, ev q = p := by
    rw [e4]
    exact (hloc F z.x ev hev).1
  have hw := fun q => ((GlobalTheory.nullValue_existsUnique_natural_linear hL E H Dw l Xo c (R ^ 2) hR2).1 F z (ev q) (hevt q)).exists
  choose w hw using hw
  have hz' : EtaValAt Xo c R cf xs z (etaExpr (R ^ 4) cf xs w) :=
    ⟨F, inferInstance, inferInstance, AlgHom.id _ _, z, ev, w,
      RingHom.FaithfullyFlat.of_bijective Function.bijective_id, PullbackSections.frMap_refl z, hev, hw, rfl⟩
  have hvalF : algebraMap (FractionRing V) F val = etaExpr (R ^ 4) cf xs w :=
    (GlobalTheory.EtaForm.etaValAt_existsUnique_natural hL E H Dw l Xo c R hR J n cf xs).2 _ F ψ y z hz _ _ hval hz'
  obtain ⟨Φ, w₀, hN, hact, hint⟩ := GlobalTheory.T.exists_fib_normW_of_intSec E H Dw l Xo c V y G S P
  obtain ⟨th, hth⟩ := GlobalTheory.T.exists_abelianSection_of_universalFibreSection E H Dw l Xo V y.x P.A Φ F z.x hzx z.s
  obtain ⟨ϑ, hϑ, hν⟩ := GlobalTheory.T.exists_expandsF_nuGe_zero_of_intTh V hcpl ϖ hϖ P.D Q hQ F v hv P.A G.G G.semi P.U w₀ hN.1 th
    (hint F ψ z th hψ hz hth)
  obtain ⟨tr, htr, htra⟩ := GlobalTheory.T.exists_mulEquiv_ptO_hom_of_eq_spMap_comp E H Dw l Xo V y.x P.A Φ F z.x hzx
  obtain ⟨pt, hpt, hspan⟩ := GlobalTheory.T.exists_heisenbergLifts_span_latticeClasses E H V G P htors F ((R ^ 2) ^ 2) (pow_pos (pow_pos hR0 2) 2)
    (LatMod Dw (R ^ 4)) (fun a => tr (ev a)) (fun a b => by rw [hev.1, map_mul])
    (fun o a => by rw [hev.2.1]; exact htra _ _ (hact o) _)
    (fun a => by rw [← map_pow, hevt, map_one])
    (fun u hu => by
      obtain ⟨a, ha⟩ := hevs (tr.symm u) (by rw [← map_pow, hu, map_one])
      exact ⟨a, by rw [ha, MulEquiv.apply_symm_apply]⟩)
  have hb : ∀ a (q : ℚ), (∀ χ, q ≤ (Q ((R ^ 2) • χ + (pt a).y) : ℚ) / ((R ^ 2) ^ 2 : ℕ)) →
      (q : WithTop ℚ) ≤ v (w a) := by
    intro a q hq
    obtain ⟨t, ht⟩ := GlobalTheory.T.normalisedThetaConstant_of_universal_origin_value E H Dw l Xo c V y.x P.A Φ F z hzx th hth (R ^ 2) hR2 (ev a) (tr (ev a)) (w a)
      (hevt a) (htr _) (hw a)
    exact GlobalTheory.T.le_valuation_oddLevel_thetaConstant_integralExpansion V hcpl ϖ hϖ P.D Q hQ F v hv P.A G.G G.semi P.U w₀ Φ.ρ hN th ϑ hϑ hν (R ^ 2) hR2 (pt a)
      (tr (ev a)) t (w a) (hpt a) ht q hq
  haveI : Module.Finite ℤ P.D.toPre.X := P.D.toPre.finX
  have hcj1 : ∀ a : 𝓞 E, ∃ a' : 𝓞 E, (a' : E) = cj a := fun a => ⟨H.bar a, by rw [H.bar_eq, hcj]⟩
  have hcj2 : (H.w0 : E) + cj H.w0 = 1 := by
    rw [hcj, ← H.bar_eq, GlobalTheory.HostModel.cmHost_bar_halfIntegerGenerator]; simp
  have key : ∀ q : ℚ, (q : ℝ) ≤ Formalism.MainNotions.ModuliIntegralCharts.phiC cj β / (R : ℝ) ^ 4 →
      (Nat.card (LevGrp Dw (R ^ 4)) : ℚ) * q ≤ ((vV V val : ℤ) : ℚ) := by
    intro q hq
    have h := GlobalTheory.T.card_mul_le_val_etaExpr_of_le_sum_val E H Dw (R ^ 4) J n cf xs F v w q (fun g j => by
      refine GlobalTheory.T.le_sum_of_le_phiC_div_sq E cj hcj1 H.w0 hcj2 P.D.toPre.X Q β hβ hQ0 (R ^ 2) (by nlinarith) n
        (fun b => (pt (g (xs j b))).y) (hspan n (fun b => g (xs j b)) ?_) (fun b => v (w (g (xs j b))))
        (fun b => hb _) q ?_
      · have := congrArg (Submodule.map (g : LatMod Dw (R ^ 4) →ₗ[𝓞 E] LatMod Dw (R ^ 4))) (hsp j)
        rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, LinearEquiv.range] at this
        exact this
      · rw [Nat.cast_pow, ← pow_mul]; exact hq)
    rw [← hvalF, hvv val hne] at h
    exact_mod_cast h
  have := mul_le_of_forall_rat_le _ Nat.card_pos _ _ key
  rw [div_mul_eq_mul_div, mul_div_assoc]
  exact this

end GlobalTheory.EtaVal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusSplitting.CardMulPhiLeValuationProductFormStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_mul_phi_le_valuation_productForm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V] [IsAdicComplete (maximalIdeal V) V] [Algebra c.F (FractionRing V)] (y : FrPt Xo c (FractionRing V)) (G : SAB H (Sp V)) (_ : IntSec Xo V y.x y.s G) (P : PELUnif (maximalIdeal V) G) (ϖ : V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), QForm.IsQ P.D.toPre ϖ Q → (∀ a, 0 ≤ Q a) → ∀ (cj : E → E), (∀ a, cj a = IsCMField.complexConj E a) → ∀ (β : Formalism.MainNotions.ModuliIntegralCharts.SymB cj P.D.toPre.X), (∀ a, (β : _ →ₗ[ℤ] _ →ₗ[ℤ] ℝ) a a = 2 * (Q a : ℝ)) → ∀ (R : ℕ), Odd R → 1 < R → ∀ (J : Type) [Fintype J] (n : ℕ) (cf : J → ℤ) (xs : J → Fin n → LatMod Dw (R ^ 4)) (val : FractionRing V), GlobalTheory.EtaAn.Spans xs → EtaValAt Xo c R cf xs y val → val ≠ 0 → (Nat.card (LevGrp Dw (R ^ 4)) : ℝ) / (R : ℝ) ^ 4 * Formalism.MainNotions.ModuliIntegralCharts.phiC cj β ≤ (vV V val : ℝ) := by
  first | exact @GlobalTheory.EtaVal.card_mul_phiC_le_valuation | exact GlobalTheory.EtaVal.card_mul_phiC_le_valuation | (intros; apply GlobalTheory.EtaVal.card_mul_phiC_le_valuation <;> assumption)
end
