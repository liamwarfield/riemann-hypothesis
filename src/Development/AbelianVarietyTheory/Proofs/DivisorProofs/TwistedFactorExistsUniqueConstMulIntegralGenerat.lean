module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConstOfPolConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdConjDifferentEqZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedGroupsBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSymmetricFunctionsDegreeFactorialBasicPrope
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedFactorExistsUniqueConstMulIntegralGenerat
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedFactorExistsUniqueConstMulIntegralGenerat
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

noncomputable section

namespace GlobalTheory.TwFac

theorem exists_zpow {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (n : ℤ) :
    ∃ t' : LB.Gen (LB.LinComb L φ (fun k => ε k * n)), t'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) J, val t' r z J = val t r z J ^ n := by
  refine ⟨⟨fun j => (show Γ(Y, LB.wchart L φ j)ˣ from t.s j) ^ n⟩, fun i j => ?_, fun Z r z J => map_zpow _ _ _⟩
  refine ((map_zpow _ _ _).trans ((congrArg (· ^ n) (ht i j)).trans (mul_zpow _ _ _))).trans
    (congrArg₂ (· * ·) ?_ (map_zpow _ _ _).symm)
  exact (Finset.prod_zpow _ _ _).symm.trans (Finset.prod_congr rfl fun k _ => (zpow_mul _ _ _).symm)

theorem exists_norm {X Y S₀ : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (S₀ ⟶ X)} {ε' : K' → ℤ}
    (p : Y ⟶ S₀) (e : S₀ ⟶ Y) (he : e ≫ p = 𝟙 _) (hF : FormEq (fun k => e ≫ φ k) ε φ' ε')
    (w : LB.Gen (LB.LinComb M φ ε)) (hw : w.IsGen) (v : LB.Gen (LB.LinComb M φ' ε')) (hv : v.IsGen) :
    ∃ u : LB.Gen (LB.LinComb M φ ε), u.IsGen ∧ ∀ y J, Good M y J → val u e y J = val v (𝟙 _) y J := by
  obtain ⟨u, hu, vu⟩ := exists_gen hM (φ' := φ) (ε' := ε) (fun U _ h => by
      have q := hF U (fun g => h (p ≫ g))
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
      rw [q, mul_inv_cancel, _root_.mul_one])
    (LB.mulGen M _ _ _ _ w (LB.pullGen M _ _ (LB.mulGen M _ _ _ _ v (LB.invGen M _ _ (LB.pullGen M _ _ w e))) p))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hw (DVR.pullGen_isGen _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ hv
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hw _))) _))
  refine ⟨u, hu, fun y J hJ => ?_⟩
  rw [vu _ _ y J hJ, val_mul hJ, val_pull hJ, he, val_mul hJ, val_inv, val_pull hJ, Category.id_comp, mul_comm,
    inv_mul_cancel_right]

variable {R : Type} [CommRing R] [IsDomain R]

theorem tr_left (D : DegPre R) (mu : D.X) :
    (DegPre.trF D (FractionRing R) mu).left ≫ (DegPre.prB D (FractionRing R)).left =
      (DegPre.prB D (FractionRing R)).left ≫ (padd D.P.A (𝟙 _) (toUnit _ ≫ D.c mu)).left := by
  rw [← Over.comp_left, ← Over.comp_left]
  congr 1
  refine (lift_snd _ _).trans ?_
  refine Eq.trans ?_ (MonObj.comp_mul _ _ _).symm
  rw [Category.comp_id]
  exact congrArg (DegPre.prB D (FractionRing R) * ·) (DVR.comp_cP D _ mu).symm

theorem prod_t (D : DegPre R) (a : D.P.A ⟶ D.P.A) (β : D.X) (n j : ℤ) {T : Over (Sp R)} (y : T ⟶ D.P.A)
    {U : Type} [CommGroup U] (g : (T.left ⟶ D.P.A.left) → U) :
    ∏ k, g (y.left ≫ tφ D a β k) ^ tε n j k = g y.left ^ (n - 1) * g (y * DVR.cP D T β).left *
      (g (DVR.cP D T β).left)⁻¹ * g (1 : T ⟶ D.P.A).left * g (y ≫ a).left ^ j := by
  have e₀ : y.left ≫ tφ D a β 0 = y.left := Category.comp_id _
  have e₁ : y.left ≫ tφ D a β 1 = (y * DVR.cP D T β).left :=
    congrArg (fun q => q.left) ((MonObj.comp_mul y (𝟙 _) (DVR.cP D _ β)).trans (by rw [DVR.comp_cP, Category.comp_id]))
  have e₂ : y.left ≫ tφ D a β 2 = (DVR.cP D T β).left := congrArg (fun q => q.left) (DVR.comp_cP D y β)
  have e₃ : y.left ≫ tφ D a β 3 = (1 : T ⟶ D.P.A).left :=
    congrArg (fun q : T ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) y)
  have e₄ : y.left ≫ tφ D a β 4 = (y ≫ a).left := rfl
  rw [Fin.prod_univ_five, e₀, e₁, e₂, e₃, e₄]
  show _ ^ (n - 1) * _ ^ (1 : ℤ) * _ ^ (-1 : ℤ) * _ ^ (1 : ℤ) * _ ^ j = _
  rw [zpow_one, zpow_one, zpow_neg_one]

theorem exists_fac (D : DegPre R) (a : D.P.A ⟶ D.P.A) (h : D.X →+ D.X) [IsMonHom a] (hh : ∀ y, D.c (h y) = D.c y ≫ a)
    (n j : ℤ) (mu β β' : D.X) (w : LB.Gen (LB.LinComb D.P.L (dφ D a mu β β') (dε n j))) (hw : w.IsGen) :
    ∃ u, IsFac D a h n j mu β β' u := by
  obtain ⟨p₁, h₁, v₁⟩ := exists_zpow (D.psi mu) (D.psi_gen mu) n
  obtain ⟨p₂, h₂, v₂⟩ := exists_zpow (D.psi (h mu)) (D.psi_gen _) j
  obtain ⟨p₃, h₃, v₃⟩ := exists_zpow D.rigK (DVR.pullGen_isGen _ _ _ _ D.rig_gen _) (n + j)
  have z₁ : DegPre.zF D (FractionRing R) ≫ fst _ _ = 𝟙 _ := lift_fst _ _
  have z₂ : DegPre.zF D (FractionRing R) ≫ DegPre.prB D (FractionRing R) = 1 := lift_snd _ _
  have z₃ : DegPre.zF D (FractionRing R) ≫ DegPre.trF D (FractionRing R) mu ≫ DegPre.prB D (FractionRing R) =
      DVR.cP D _ mu := by
    rw [DVR.trF_eq, DVR.tr_pr, MonObj.comp_mul, z₂, ← Category.assoc, z₁, Category.id_comp, _root_.one_mul]
  obtain ⟨u, hu, vu⟩ := exists_norm D.P.isLB (fst (TF (R := R) (FractionRing R)) D.P.A).left
    (DegPre.zF D (FractionRing R)).left (congrArg (fun q => q.left) z₁) (fun U _ g => by
      have a₁ : ∀ χ, jFK (R := R) (FractionRing R) ≫ ptK (D.c χ) = (DVR.cP D (TF (R := R) (FractionRing R)) χ).left :=
        fun χ => (Category.assoc _ _ _).symm
      have a₂ : jFK (R := R) (FractionRing R) ≫ (toUnit (TK R)).left ≫ eSec D.P.A =
          (1 : TF (R := R) (FractionRing R) ⟶ D.P.A).left := (Category.assoc _ _ _).symm
      have q₁ := prod_t D a β' n j (DegPre.zF D (FractionRing R) ≫ DegPre.prB D (FractionRing R)) g
      have q₂ := prod_t D a β n j
        (DegPre.zF D (FractionRing R) ≫ DegPre.trF D (FractionRing R) mu ≫ DegPre.prB D (FractionRing R)) g
      have b₁ : (1 : TF (R := R) (FractionRing R) ⟶ D.P.A) ≫ a = 1 := MonObj.one_comp _
      have b₂ : DVR.cP D (TF (R := R) (FractionRing R)) mu ≫ a = DVR.cP D _ (h mu) := by
        rw [DVR.cP, DVR.cP, hh, Category.assoc]
      conv_rhs at q₁ => rw [z₂, b₁, _root_.one_mul]
      conv_rhs at q₂ => rw [z₃, b₂, ← DVR.cPoint_add]
      simp only [Over.comp_left, Category.assoc] at q₁ q₂
      refine (DVR.prod_sum₂ (K := Fin 5) (K' := Fin 5) (U := U) _ q₁ (DVR.prod_neg _ _ q₂)).trans ?_
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, a₁, a₂]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
    w hw (LB.pullGen D.P.L _ _ (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ p₁ p₂)
      (D.tau mu β)) p₃) (jFK (R := R) (FractionRing R)))
    (DVR.pullGen_isGen _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.mulGen_isGen _ _ _ _ _ _ _ h₁ h₂) (DVR.tau_isGen D mu β)) h₃) _)
  refine ⟨u, hu, fun z J hJ => (vu z J hJ).trans ((val_pull hJ _ _ _).trans ?_)⟩
  rw [Category.id_comp]
  exact (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (v₁ _ _ _ _) (v₂ _ _ _ _))) rfl)) (v₃ _ _ _ _))

theorem fac_exists_unique_const : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a : D.toPre.P.A ⟶ D.toPre.P.A), ∀ (h : D.toPre.X →+ D.toPre.X), IsMonHom a → (∀ y, D.toPre.c (h y) = D.toPre.c y ≫ a) → ∀ (n j : ℤ) (mu β β' : D.toPre.X) (u₀ : LB.Gen (LB.LinComb D.toPre.P.L (Sum.elim (tφ D.toPre a β') (fun k => (padd D.toPre.P.A (𝟙 _) (toUnit _ ≫ D.toPre.c mu)).left ≫ tφ D.toPre a β k)) (dε n j))), u₀.IsGen → (∃ u, IsFac D.toPre a h n j mu β β' u) ∧ (∀ u u', IsFac D.toPre a h n j mu β β' u → IsFac D.toPre a h n j mu β β' u' → ∀ (Z : Scheme.{0}) (x : Z ⟶ (DegPre.BF D.toPre (FractionRing R)).left) (z : Z) (J), Good D.toPre.P.L z J → val u x z J = val u' x z J) ∧ ∀ u : LB.Gen (LB.LinComb D.toPre.P.L (dφ D.toPre a mu β β') (dε n j)), u.IsGen → ∃ c : (FractionRing R), ∀ (Z : Scheme.{0}) (x : Z ⟶ (DegPre.BF D.toPre (FractionRing R)).left) (z : Z) (J), Good D.toPre.P.L z J → (val u x z J).val = gs x z ⊤ (scal ((fst _ _ : DegPre.BF D.toPre (FractionRing R) ⟶ TF (R := R) (FractionRing R)).left : (DegPre.BF D.toPre (FractionRing R)).left ⟶ Sp (FractionRing R)) c) * (val u₀ (x ≫ (DegPre.prB D.toPre (FractionRing R)).left) z J).val := by
  intro R _ _ _ _ D a h ha hh n j mu β β' u₀ hu₀
  have hL := D.toPre.P.isLB
  have hs := DVR.surj_appTop D.toPre (FractionRing R) GlobalTheory.globalFns_holds
  obtain ⟨w, hw, vw⟩ := exists_gen hL (φ' := dφ D.toPre a mu β β') (ε' := dε n j) (fun U _ g => by
      refine Finset.prod_congr rfl ?_
      rintro (k | k) -
      · rfl
      · simp only [dφ, Sum.elim_inr]
        rw [← Category.assoc, ← tr_left, Category.assoc])
    (LB.pullGen D.toPre.P.L _ _ u₀ (DegPre.prB D.toPre (FractionRing R)).left) (DVR.pullGen_isGen _ _ _ _ hu₀ _)
  refine ⟨exists_fac D.toPre a h hh n j mu β β' w hw, fun u u' hu hu' => ?_, fun u hu => ?_⟩
  · have z₁ : DegPre.zF D.toPre (FractionRing R) ≫ fst _ _ = 𝟙 _ := lift_fst _ _
    exact gen_unique hL (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left (DegPre.zF D.toPre (FractionRing R)).left
      (congrArg (fun q => q.left) z₁) hs hu.1 hu'.1 (fun y J hJ => (hu.2 y J hJ).trans (hu'.2 y J hJ).symm)
  · obtain ⟨c, hc⟩ := GlobalTheory.WeilMul.exists_ratio hL (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left hs hu hw
    refine ⟨(Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom c, fun Z x z J hJ => ?_⟩
    have e : (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom
        ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom c) = c := Iso.hom_inv_id_apply _ c
    have e₂ := (hc Z x z J hJ).trans ((gs_pull x (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left z ⊤ trivial c).symm)
    rw [vw _ _ z J hJ, val_pull hJ] at e₂
    refine Eq.trans ?_ (congrArg₂ (· * ·) (e₂.trans (congrArg (fun q => gs x z ⊤
      ((fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left.appTop.hom q)) e.symm)) rfl)
    rw [← Units.val_mul, inv_mul_cancel_right]

end GlobalTheory.TwFac
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedFactorExistsUniqueConstMulIntegralGeneratStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedFactor_exists_unique_const_mul_integralGenerator : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a : D.toPre.P.A ⟶ D.toPre.P.A), ∀ (h : D.toPre.X →+ D.toPre.X), IsMonHom a → (∀ y, D.toPre.c (h y) = D.toPre.c y ≫ a) → ∀ (n j : ℤ) (mu β β' : D.toPre.X) (u₀ : LB.Gen (LB.LinComb D.toPre.P.L (Sum.elim (tφ D.toPre a β') (fun k => (padd D.toPre.P.A (𝟙 _) (toUnit _ ≫ D.toPre.c mu)).left ≫ tφ D.toPre a β k)) (dε n j))), u₀.IsGen → (∃ u, IsFac D.toPre a h n j mu β β' u) ∧ (∀ u u', IsFac D.toPre a h n j mu β β' u → IsFac D.toPre a h n j mu β β' u' → ∀ (Z : Scheme.{0}) (x : Z ⟶ (DegPre.BF D.toPre (FractionRing R)).left) (z : Z) (J), Good D.toPre.P.L z J → val u x z J = val u' x z J) ∧ ∀ u : LB.Gen (LB.LinComb D.toPre.P.L (dφ D.toPre a mu β β') (dε n j)), u.IsGen → ∃ c : (FractionRing R), ∀ (Z : Scheme.{0}) (x : Z ⟶ (DegPre.BF D.toPre (FractionRing R)).left) (z : Z) (J), Good D.toPre.P.L z J → (val u x z J).val = gs x z ⊤ (scal ((fst _ _ : DegPre.BF D.toPre (FractionRing R) ⟶ TF (R := R) (FractionRing R)).left : (DegPre.BF D.toPre (FractionRing R)).left ⟶ Sp (FractionRing R)) c) * (val u₀ (x ≫ (DegPre.prB D.toPre (FractionRing R)).left) z J).val := by
  exact @GlobalTheory.TwFac.fac_exists_unique_const
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeySectionInverseRootTwistingSectionSpread
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeySectionInverseRootTwistingSectionSpread
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.KeyRootTw

namespace GlobalTheory.KeyRootSpread

theorem exists_twSec_keyRoot_spread : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ x : ℝ, (∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = x) → FnAlgClosed (Xo := Xo) (c := c) → 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → UnramPts Xo c (badPrimes H l) → Nonempty (GlobalTheory.ShFam.KeySec Xo c) ∧ ∀ Z : Comp Xo c, ∃ t : TwSec U x Z (wtOf Dw 0 1), IntOff (badPrimes H l) t.hi ∧ ∀ w, t.hi w - t.lo w ≤ ∑ τ : E →+* ℂ, (Dw.mult τ : ℝ) * (ord_vw w (conjDifferent (embF c τ)) : ℝ) := by
  intro E _ _ _ H Dw l Xo c r U hU x hx hF hpq hg hun
  obtain ⟨κ, k₁, k₂, k₃, k₄, k₅, k₆, -, -⟩ := GlobalTheory.KeyFamClosing.keyFam_one
  let e : Fin (Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ))) ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ) :=
    (Fintype.equivFin _).symm
  obtain ⟨K, hKmem, hKval⟩ := GlobalTheory.T.exists_unit_section_thetaKeyRule_weightFour κ k₁ k₂ k₆ E H Dw l Xo c _ e hpq
  have hσ0 := goodEmb_goodOf c c.F.val.toRingHom
  obtain ⟨⟨ρ, hρmem⟩, hρ⟩ := GlobalTheory.T.exists_keySection_fourthRoot_perComponent κ k₁ k₂ k₆ k₄ E H Dw l Xo c _ e _ r (U _) K hσ0 (hU _ hσ0) hF hpq hKmem hKval
  have hkr : GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels.IsKeyRule κ := by
    refine ⟨?_, k₂, k₃, k₄, ?_⟩
    · simpa only [GlobalTheory.KeyCl.Homog, mul_one] using k₁
    · simpa only [GlobalTheory.KeyCl.ArchNorm, mul_one] using k₅
  have hval := GlobalTheory.T.theta_key_section_valuation_bounds_different κ hkr E H Dw l Xo c _ e K hpq hg hKmem hKval
  have hC := fun σ : c.F →+* ℂ => GlobalTheory.T.thetaKeySection_norm_complexPoints_eq_two_pi_pow κ k₁ k₂ k₅ E H Dw l Xo c _ e (goodOf c σ) r (U (goodOf c σ)) x K
    (goodEmb_goodOf c σ) (hU _ (goodEmb_goodOf c σ)) (hx _ (goodEmb_goodOf c σ)) ⟨⟨ρ, hρmem⟩⟩ hpq hKmem hKval
  choose C hCpos hClog hCeq using hC
  have hgE := card_frame_index Dw e
  have hsum : ∑ τ : E →+* ℂ, Dw.mult τ = Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) := by
    simp [Fintype.card_sigma]
  have hwt : ∀ (m : ℤ) (τ : E →+* ℂ) (i : ℕ), i < Dw.mult τ → (wtOf Dw 0 m).1 (τ, i) = -m :=
    wtOf_zero_fst E H Dw
  have hex : exZ Dw (wtOf Dw 0 1) = -keyEx Dw := by
    funext i
    rcases i with _ | ⟨τ, i⟩
    · rfl
    · simp only [exZ, keyEx, Pi.neg_apply]
      exact hwt 1 τ i i.2
  have hadd : wtOf Dw 0 1 + wtOf Dw 0 (-1) = 0 := by
    rw [← wtOf_add, add_zero, add_neg_cancel, wtOf_zero]
  refine ⟨⟨⟨ρ, hρmem⟩⟩, fun Z => ?_⟩
  obtain ⟨a, ha, haK⟩ := hρ Z
  have hP : HasPts U Z := hasPts U hpq hg hU Z
  set s : Rul Xo c := idem Z * ((ρ⁻¹ : (Rul Xo c)ˣ) : Rul Xo c) with hs
  set s' : Rul Xo c := idem Z * (ρ : Rul Xo c) with hs'
  have hsm : s ∈ secZ Xo c (exZ Dw (wtOf Dw 0 1)) := by
    have := mul_mem_secZ (idem_mem_secZ Z) (inv_mem_secZ hρmem)
    rwa [zero_add, ← hex] at this
  have hsm' : s' ∈ secZ Xo c (exZ Dw (wtOf Dw 0 (-1))) := by
    have := mul_mem_secZ (idem_mem_secZ Z) hρmem
    have h2 : exZ Dw (wtOf Dw 0 (-1)) = keyEx Dw := by
      have h3 := exZ_add_eq (Dw := Dw) (wtOf Dw 0 1) (wtOf Dw 0 (-1))
      rw [hadd, hex] at h3
      have h4 : exZ Dw (0 : WTZ E) = 0 := by funext i; cases i <;> rfl
      rw [h4] at h3
      exact (neg_add_eq_zero.1 h3.symm).symm
    rwa [zero_add, ← h2] at this
  have hsupp : s ∈ suppOn Z := by rw [hs, mul_comm]; exact mul_mem_suppOn _ (idem_mem_suppOn Z)
  have hsupp' : s' ∈ suppOn Z := by rw [hs', mul_comm]; exact mul_mem_suppOn _ (idem_mem_suppOn Z)
  have hnorm := fun σ : c.F →+* ℂ => fun z (hz : z ∈ framesOn (U (goodOf c σ)) Z) =>
    homN_root E H Dw l Xo c (goodOf c σ) r (U (goodOf c σ)) x Z ρ K a (C σ) ha (hCpos σ) haK (hCeq σ) z hz
      ((hP.1 σ).2 z hz)
  have hgood : ∀ σ, GoodEmb c σ → goodOf c σ = σ := fun σ h => if_pos h
  have hmono : ∀ (m : ℤ) (τ : E →+* ℂ) (i j : ℕ), i ≤ j → j < Dw.mult τ →
      (wtOf Dw 0 m).1 (τ, j) ≤ (wtOf Dw 0 m).1 (τ, i) := fun m τ i j hij hj => by
    rw [hwt m τ i (lt_of_le_of_lt hij hj), hwt m τ j hj]
  have hbd : ∀ σ, GoodEmb c σ → ∃ D : ℝ, ∀ z ∈ framesOn (U σ) Z, homN (U σ) x (wtOf Dw 0 1) s z ≤ D := by
    intro σ hσ
    refine ⟨(‖σ a‖ * C σ) ^ (-(1 / 4) : ℝ), fun z hz => ?_⟩
    have h1 := hnorm σ
    rw [hgood σ hσ] at h1
    exact (h1 z hz).1.le
  have hbd' : ∀ σ, GoodEmb c σ → ∃ D : ℝ, ∀ z ∈ framesOn (U σ) Z, homN (U σ) x (wtOf Dw 0 (-1)) s' z ≤ D := by
    intro σ hσ
    refine ⟨(‖σ a‖ * C σ) ^ ((1 / 4) : ℝ), fun z hz => ?_⟩
    have h1 := hnorm σ
    rw [hgood σ hσ] at h1
    exact (h1 z hz).2.le
  let B : HeightOneSpectrum (𝓞 c.F) → ℝ := fun w =>
    ∑ τ : E →+* ℂ, (Dw.mult τ : ℝ) * (ord_vw w (conjDifferent (embF c τ)) : ℝ)
  have hbnd := fun w (v : Rul Xo c → EReal) (hv : v ∈ valOn Z w) =>
    val_root E H Dw l Xo c Z w v hv ρ K a (B w) ha haK (hval w v (valOn_subset Z w hv)).1
      (hval w v (valOn_subset Z w hv)).2
  let t : TwSec U x Z (wtOf Dw 0 1) :=
    { even := even_wtOf _ _
      sig := s
      inv := s'
      sig_mem := hsm
      inv_mem := by
        have h5 := exZ_neg_eq (Dw := Dw) (wtOf Dw 0 1)
        have h6 : -wtOf Dw 0 1 = wtOf Dw 0 (-1) := neg_eq_of_add_eq_zero_right hadd
        rw [← h5, h6]; exact hsm'
      idem_sig := by rw [hs, ← mul_assoc, idem_mul_idem]
      idem_inv := by rw [hs', ← mul_assoc, idem_mul_idem]
      mul_inv := by rw [hs, hs', mul_mul_mul_comm, idem_mul_idem, Units.inv_mul, mul_one]
      cInf := fun σ => (‖σ a‖ * C σ) ^ (-(1 / 4) : ℝ)
      cInf_pos := fun σ => Real.rpow_pos_of_pos (mul_pos (norm_pos_iff.2 ((map_ne_zero σ).2 ha)) (hCpos σ)) _
      norm_inf := fun σ z hz => by
        rw [(hnorm σ z hz).1, norm_goodOf]
      cusp_sig := fun G hG f hf =>
        GlobalTheory.T.mul_mem_cuspForms_of_boundedSection_component E H Dw l Xo c r U x Z (wtOf Dw 0 1) s ⟨⟨ρ, hρmem⟩⟩ hU hpq (even_wtOf _ _) (hmono 1) hsm hsupp hbd G hG f hf
      cusp_inv := fun G hG f hf => by
        have h7 := GlobalTheory.T.mul_mem_cuspForms_of_boundedSection_component E H Dw l Xo c r U x Z (wtOf Dw 0 (-1)) s' ⟨⟨ρ, hρmem⟩⟩ hU hpq (even_wtOf _ _) (hmono (-1))
          hsm' hsupp' hbd' (G + wtOf Dw 0 1) (hG.add (even_wtOf _ _)) f hf
        rwa [add_assoc, hadd, add_zero] at h7
      lo := fun w => -(vAdd w a : ℝ) / 4 - B w
      hi := fun w => -(vAdd w a : ℝ) / 4
      lo_le := fun w v hv => (hbnd w v hv).1
      le_hi := fun w v hv => (hbnd w v hv).2
      finite_lo := by
        refine ((finite_vAdd ha).union (Set.finite_iUnion fun τ => finite_ord (embF c τ))).subset fun w hw => ?_
        by_contra hn
        simp only [Set.mem_union, Function.mem_support, Set.mem_iUnion, not_or, not_exists, not_not] at hn
        apply hw
        simp [B, hn.1, hn.2]
      finite_hi := by
        refine (finite_vAdd ha).subset fun w hw => ?_
        by_contra hn
        simp only [Function.mem_support, not_not] at hn
        apply hw
        simp [hn]
      pts := hP }
  refine ⟨t, ?_, fun w => ?_⟩
  · intro w hw
    obtain ⟨v, hv, hint⟩ := hun Z w hw
    have hB : B w = 0 := by
      refine Finset.sum_eq_zero fun τ _ => ?_
      rw [ord_conjDifferent_eq_zero c.F E (embF c τ) w fun p hp hd => hw p (mem_badPrimes.2 ⟨hp, Or.inr (Or.inr (Or.inl hd))⟩)]
      simp
    obtain ⟨h1, h2⟩ := hbnd w v hv
    rw [hB, sub_zero] at h1
    rcases hint s with h | ⟨n, hn⟩
    · rw [h] at h2; exact absurd h2 (by simp)
    · refine ⟨n, ?_⟩
      show -(vAdd w a : ℝ) / 4 = n
      rw [hn] at h1 h2
      exact le_antisymm (EReal.coe_le_coe_iff.1 h1) (EReal.coe_le_coe_iff.1 h2)
  · show -(vAdd w a : ℝ) / 4 - (-(vAdd w a : ℝ) / 4 - B w) ≤ B w
    linarith

end GlobalTheory.KeyRootSpread
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeySectionInverseRootTwistingSectionSpreadStatement
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_keySection_inverseRoot_twistingSection_spread : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ x : ℝ, (∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = x) → FnAlgClosed (Xo := Xo) (c := c) → 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → UnramPts Xo c (badPrimes H l) → Nonempty (GlobalTheory.ShFam.KeySec Xo c) ∧ ∀ Z : Comp Xo c, ∃ t : TwSec U x Z (wtOf Dw 0 1), IntOff (badPrimes H l) t.hi ∧ ∀ w, t.hi w - t.lo w ≤ ∑ τ : E →+* ℂ, (Dw.mult τ : ℝ) * (ord_vw w (conjDifferent (embF c τ)) : ℝ) := by
  first | exact @GlobalTheory.KeyRootSpread.exists_twSec_keyRoot_spread | exact GlobalTheory.KeyRootSpread.exists_twSec_keyRoot_spread | (intros; apply GlobalTheory.KeyRootSpread.exists_twSec_keyRoot_spread <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComesFromBaseOfPullbackInjectiveDomains
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefAtPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

noncomputable section

namespace GlobalTheory.MumFam


open GlobalTheory.HalfBC in
theorem refAt_pull : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R'), Function.Injective ρ → ∀ (I : Ideal R) (D : DegData R I) (D' : DegPre R') (hD : IsPullDeg ρ D.toPre D'), RefAt (pol D) ρ D' hD.xe (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf ρ)) := by
  intro R R' _ _ _ _ ρ hρ I D D' hD
  letI := D'.P.isAb.comm
  have gp := pull_grp hD
  refine ⟨sqOf gp, lamIso gp hD.w, gp, isSquare_sqOf gp, isGen_lamIso gp hD.w hD.w_gen, fun a => hD.c_pr a,
    fun κ hκ a b z J J' hJ hJ' => ?_⟩
  obtain rfl : κ = GlobalTheory.ArcPull.genMap hρ := by
    have : Mono (jK R) := Wit.mono_jK
    refine (cancel_mono (jK R)).1 (hκ.trans ?_)
    rw [← GlobalTheory.ArcPull.fracMap_sq hρ, Category.id_comp]
  rw [← GlobalTheory.FactorPull.tau_lam hD hρ a b hJ hJ']
  refine congrArg₂ (· * ·) ?_ ((Wit.exists_tau D.toPre (hD.xe a) (hD.xe b)).choose_spec.2 _ _ z J hJ).symm
  symm
  show gw (lamIso gp hD.w) _ z (fun I => J (_ ≫ sqOf gp ≫ GlobalTheory.PrimCocycle.lamφ D.toPre.P.A I))
    (fun I => J' (_ ≫ GlobalTheory.PrimCocycle.lamφ D'.P.A I)) = _
  refine (gw_lamIso gp hD.w _ z _ _ (fun I => by
      have := hJ ((lift (toUnit (TK R') ≫ D'.c a) (toUnit (TK R') ≫ D'.c b)).left ≫ sqOf gp ≫ GlobalTheory.PrimCocycle.lamφ D.toPre.P.A I)
      erw [← pt_sqOf gp I]
      exact this) (fun I => hJ' _)).trans ?_
  refine Finset.prod_congr rfl fun I _ => ?_
  show _ = gw hD.w _ z _ _ ^ _
  erw [Category.assoc, ← sqOf_lamφ gp I]
  rfl

end GlobalTheory.MumFam
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComesFromBaseOfPullbackInjectiveDomains
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

noncomputable section

namespace GlobalTheory.TInj

theorem gm_spMap_unitOn_top {A B : Type} [CommRing A] [CommRing B] (m : A →+* B) (z : Sp B) (k : Aˣ) :
    gm (spMap m) z ⊤ (unitOn k) = gm (𝟙 (Sp B)) z ⊤ (unitOn (Units.map m.toMonoidHom k)) := by
  apply Units.ext
  rw [gm_val _ z ⊤ trivial, gm_val _ z ⊤ trivial]
  have nat := congrArg (fun q => q.hom k.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom m))
  exact congrArg ((Sp B).presheaf.germ ⊤ z trivial).hom nat.symm

theorem from_pull : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (R : Type) [CommRing R] [IsDomain R] (V : Type) [CommRing V] [IsDomain V] (J : Ideal R) (D₀ : DegData R J) (ω : W →+* R) (s : I → R) (e : D₀.toPre.X ≃+ (Fin T.r → ℤ)) (β : D₀.toPre.P.A.left ⟶ T.B.left) (ββ : (G2 D₀.toPre.P.A).left ⟶ (G2 T.B).left) (w : LB.Iso (abelian₂ D₀.toPre.P.A D₀.toPre.P.L) ((abelian₂ T.B T.M.L).pull ββ)) (f : R →+* V) (D : DegPre V) (hD : IsPullDeg f D₀.toPre D), Function.Injective f → From T ω s ε n D₀.toPre e β ββ w → ∃ ββ' w', From T (f.comp ω) (fun i => f (s i)) ε n D (hD.xe.trans e) ((hD.e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf f)) ≫ β) ββ' w' := by
  intro o W _ _ _ T I _ ε n R _ _ V _ _ Jd D₀ ω s e β ββ w f D hD hf hF
  obtain ⟨pb, sq, gen, hc, hτ⟩ := hF
  have hR : ∃ (β₂₁ : (G2 D.P.A).left ⟶ (G2 D₀.toPre.P.A).left)
      (w₁ : LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ D₀.toPre.P.A D₀.toPre.P.L).pull β₂₁)),
      IsGrpPullback D.P.A D₀.toPre.P.A (spMap f) (hD.e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf f)) ∧
      IsSquare (hD.e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf f)) β₂₁ ∧ w₁.IsGen ∧
      (∀ a, (D.c a).left ≫ (hD.e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf f)) =
        spMap f ≫ (D₀.toPre.c (hD.xe a)).left) ∧
      ∀ κ : (TK V).left ⟶ (TK R).left, κ ≫ jK R = jK V ≫ spMap f → ∀ a b z J J', Good D₀.toPre.P.L z J →
        Good D.P.L z J' → val (D.tau a b) (𝟙 _) z J' =
          lamVal w₁ (lift (toUnit (TK V) ≫ D.c a) (toUnit (TK V) ≫ D.c b)).left z J J' *
            val (D₀.toPre.tau (hD.xe a) (hD.xe b)) κ z J := by
    obtain ⟨β₂₁, w₁, pb₁, sq₁, gen₁, c₁, tau₁⟩ := GlobalTheory.MumFam.refAt_pull R V f hf Jd D₀ D hD
    exact ⟨β₂₁, w₁, pb₁, sq₁, gen₁, c₁, fun κ hκ a b z J J' hJ hJ' => (tau₁ κ hκ a b z J J' hJ hJ').trans
      (congrArg _ ((Wit.exists_tau D₀.toPre (hD.xe a) (hD.xe b)).choose_spec.2 _ κ z J hJ))⟩
  obtain ⟨β₂₁, w₁, pb₁, sq₁, gen₁, c₁, tau₁⟩ := hR
  have hΛT : (abelian₂ T.B T.M.L).IsLB := DVR.linComb_isLB _ T.M.isLB _ _
  have hΛ₀ : (abelian₂ D₀.toPre.P.A D₀.toPre.P.L).IsLB := DVR.linComb_isLB _ D₀.toPre.P.isLB _ _
  have hΛ : (abelian₂ D.P.A D.P.L).IsLB := DVR.linComb_isLB _ D.P.isLB _ _
  obtain ⟨w', T3⟩ := exists_comp hΛ₀ w w₁ ((isGen_iff _).1 gen) ((isGen_iff _).1 gen₁) hΛT hΛ
  refine ⟨β₂₁ ≫ ββ, w', (IsGrpPullback.comp pb₁ pb).congr (GlobalTheory.HalfBC.spMap_comp_spMap' ω f) rfl, ⟨?_, ?_⟩,
    (isGen_iff _).2 (T3.pgen_comp hΛ₀ ((isGen_iff _).1 gen) ((isGen_iff _).1 gen₁)), fun a => ?_, fun a b => ?_⟩
  · exact (Category.assoc _ _ _).trans ((congrArg (β₂₁ ≫ ·) sq.1).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ β) sq₁.1).trans (Category.assoc _ _ _))))
  · exact (Category.assoc _ _ _).trans ((congrArg (β₂₁ ≫ ·) sq.2).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ β) sq₁.2).trans (Category.assoc _ _ _))))
  · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ β) (c₁ a)).trans ((Category.assoc _ _ _).trans
      ((congrArg (spMap f ≫ ·) (hc (hD.xe a))).trans ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ _) (GlobalTheory.HalfBC.spMap_comp_spMap' ω f))))))
  · obtain ⟨k₀, hk₀, hv₀⟩ := hτ (hD.xe a) (hD.xe b)
    let m : FractionRing R →+* FractionRing V := IsLocalization.map (FractionRing V) f (M := nonZeroDivisors R)
      (T := nonZeroDivisors V) (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective f hf)
    have hm : ∀ r, m (algebraMap R (FractionRing R) r) = algebraMap V (FractionRing V) (f r) := fun r =>
      IsLocalization.map_eq _ _
    refine ⟨Units.map m.toMonoidHom k₀, ?_, fun z Jt J' hJt hJ' => ?_⟩
    · show m k₀ = _
      rw [hk₀, map_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [map_zpow₀, hm]
      rfl
    · let κ : (TK V).left ⟶ (TK R).left := spMap m
      have hκ : κ ≫ jK R = jK V ≫ spMap f := by
        show spMap m ≫ spMap (algebraMap R (FractionRing R)) = spMap (algebraMap V (FractionRing V)) ≫ spMap f
        rw [GlobalTheory.HalfBC.spMap_comp_spMap', GlobalTheory.HalfBC.spMap_comp_spMap']
        congr 1
        exact RingHom.ext hm
      choose J₁ hJ₀ using fun χ : (TK V).left ⟶ D₀.toPre.P.A.left => exists_chart D₀.toPre.P.isLB (χ z)
      have hJ₁ : Good D₀.toPre.P.L z J₁ := hJ₀
      have t₁ := tau₁ κ hκ a b z J₁ J' hJ₁ hJ'
      have n₁ : val (D₀.toPre.tau (hD.xe a) (hD.xe b)) (κ ≫ 𝟙 _) z J₁ = Units.map (κ.stalkMap z).hom.toMonoidHom
          (val (D₀.toPre.tau (hD.xe a) (hD.xe b)) (𝟙 _) (κ z) (fun ψ => J₁ (κ ≫ ψ))) :=
        Units.ext ((GlobalTheory.values_natural _ _ _ _ _ _ _ _ (𝟙 _) κ z J₁ hJ₁).2.2.1 _)
      rw [Category.comp_id] at n₁
      have h₀ := hv₀ (κ z) (fun ψ => Jt (κ ≫ ψ)) (fun ψ => J₁ (κ ≫ ψ)) (fun ψ => hJt (κ ≫ ψ)) (fun ψ => hJ₁ (κ ≫ ψ))
      have h₁ := (congrArg (Units.map (κ.stalkMap z).hom.toMonoidHom) h₀).trans
        ((map_mul _ _ _).trans (congrArg₂ (· * ·) rfl (map_mul _ _ _)))
      have g₁ : Units.map (κ.stalkMap z).hom.toMonoidHom (gm (𝟙 (TK R).left) (κ z) ⊤ (unitOn k₀)) =
          gm (𝟙 (TK V).left) z ⊤ (unitOn (Units.map m.toMonoidHom k₀)) := by
        rw [← GlobalTheory.ConstFam.gm_comp_stalkMap κ (𝟙 _) z ⊤ trivial, Category.comp_id]
        exact gm_spMap_unitOn_top m z k₀
      have g₂ := (GlobalTheory.HalfBC.lamVal_comp w κ
        (lift (toUnit (TK R) ≫ D₀.toPre.c (hD.xe a)) (toUnit (TK R) ≫ D₀.toPre.c (hD.xe b))).left z Jt J₁ hJt hJ₁).symm
      have g₃ : Units.map (κ.stalkMap z).hom.toMonoidHom (val (T.τ₀ ((n : ℤ) • e (hD.xe a)) ((n : ℤ) • e (hD.xe b)))
          ((TK R).hom ≫ spMap ω) (κ z) (fun ψ => Jt (κ ≫ ψ))) =
          val (T.τ₀ ((n : ℤ) • e (hD.xe a)) ((n : ℤ) • e (hD.xe b))) (κ ≫ (TK R).hom ≫ spMap ω) z Jt :=
        (Units.ext ((GlobalTheory.values_natural _ _ _ _ _ _ _ _ _ κ z Jt hJt).2.2.1 _)).symm
      have hb : κ ≫ (TK R).hom ≫ spMap ω = (TK V).hom ≫ spMap (f.comp ω) := by
        show κ ≫ jK R ≫ spMap ω = jK V ≫ spMap (f.comp ω)
        rw [← Category.assoc, hκ, Category.assoc, GlobalTheory.HalfBC.spMap_comp_spMap']
      have hx : ∀ χ, (toUnit (TK V) ≫ D.c χ).left ≫ (hD.e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf f)) =
          κ ≫ (toUnit (TK R) ≫ D₀.toPre.c (hD.xe χ)).left := fun χ => by
        show (jK V ≫ (D.c χ).left) ≫ _ = κ ≫ jK R ≫ (D₀.toPre.c (hD.xe χ)).left
        rw [Category.assoc, c₁ χ, ← Category.assoc, ← Category.assoc, hκ]
      have hP : κ ≫ (lift (toUnit (TK R) ≫ D₀.toPre.c (hD.xe a)) (toUnit (TK R) ≫ D₀.toPre.c (hD.xe b))).left =
          (lift (toUnit (TK V) ≫ D.c a) (toUnit (TK V) ≫ D.c b)).left ≫ β₂₁ := by
        refine Eq.symm ?_
        apply pullback.hom_ext
        · show _ ≫ (fst D₀.toPre.P.A D₀.toPre.P.A).left = _ ≫ (fst D₀.toPre.P.A D₀.toPre.P.A).left
          rw [Category.assoc, sq₁.1, ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc, ← Over.comp_left,
            lift_fst]
          exact hx a
        · show _ ≫ (snd D₀.toPre.P.A D₀.toPre.P.A).left = _ ≫ (snd D₀.toPre.P.A D₀.toPre.P.A).left
          rw [Category.assoc, sq₁.2, ← Category.assoc, ← Over.comp_left, lift_snd, Category.assoc, ← Over.comp_left,
            lift_snd]
          exact hx b
      have key : ∀ p : (TK V).left ⟶ (G2 D.P.A).left,
          lamVal w' p z Jt J' = lamVal w (p ≫ β₂₁) z Jt J₁ * lamVal w₁ p z J₁ J' := by
        intro p
        have t := T3 _ p z (fun I => Jt (p ≫ (β₂₁ ≫ ββ) ≫ GlobalTheory.PrimCocycle.lamφ T.B I))
          (fun I => J₁ ((p ≫ β₂₁) ≫ GlobalTheory.PrimCocycle.lamφ D₀.toPre.P.A I))
          (fun I => J' (p ≫ GlobalTheory.PrimCocycle.lamφ D.P.A I))
          (Set.mem_iInter.2 fun I => hJt _) (Set.mem_iInter.2 fun I => hJ₁ _) (Set.mem_iInter.2 fun I => hJ' _)
        refine t.trans (congrArg₂ (· * ·) ?_ ?_)
        · show _ = gw w (p ≫ β₂₁) z (fun I => Jt ((p ≫ β₂₁) ≫ ββ ≫ GlobalTheory.PrimCocycle.lamφ T.B I))
            (fun I => J₁ ((p ≫ β₂₁) ≫ GlobalTheory.PrimCocycle.lamφ D₀.toPre.P.A I))
          simp only [Category.assoc]
        · show _ = gw w₁ p z (fun I => J₁ (p ≫ β₂₁ ≫ GlobalTheory.PrimCocycle.lamφ D₀.toPre.P.A I))
            (fun I => J' (p ≫ GlobalTheory.PrimCocycle.lamφ D.P.A I))
          simp only [Category.assoc]
      show _ = _ * (_ * val (T.τ₀ ((n : ℤ) • e (hD.xe a)) ((n : ℤ) • e (hD.xe b))) _ z Jt)
      rw [t₁, n₁, h₁, g₁, g₂, g₃, hP, hb, key]
      ac_rfl

end GlobalTheory.TInj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComesFromBaseOfPullbackInjectiveDomainsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.comesFromBase_of_pullback_injective_domains : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (R : Type) [CommRing R] [IsDomain R] (V : Type) [CommRing V] [IsDomain V] (J : Ideal R) (D₀ : DegData R J) (ω : W →+* R) (s : I → R) (e : D₀.toPre.X ≃+ (Fin T.r → ℤ)) (β : D₀.toPre.P.A.left ⟶ T.B.left) (ββ : (G2 D₀.toPre.P.A).left ⟶ (G2 T.B).left) (w : LB.Iso (abelian₂ D₀.toPre.P.A D₀.toPre.P.L) ((abelian₂ T.B T.M.L).pull ββ)) (f : R →+* V) (D : DegPre V) (hD : IsPullDeg f D₀.toPre D), Function.Injective f → From T ω s ε n D₀.toPre e β ββ w → ∃ ββ' w', From T (f.comp ω) (fun i => f (s i)) ε n D (hD.xe.trans e) ((hD.e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf f)) ≫ β) ββ' w' := by
  first | exact @GlobalTheory.TInj.from_pull | exact GlobalTheory.TInj.from_pull | (intros; apply GlobalTheory.TInj.from_pull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefShiftedFubiniStudyOfShortGenerators
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroShortGeneratorSectionImageModel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroShortGeneratorSectionImageModel
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.ImageModelGen

theorem basicOpen_sum_le {X : Scheme.{0}} {U : X.Opens} {ι : Type} (t : Finset ι) (f : ι → Γ(X, U)) :
    X.basicOpen (∑ j ∈ t, f j) ≤ ⨆ j ∈ t, X.basicOpen (f j) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.sum_insert ha]
    intro x hx
    have hxU : x ∈ U := X.basicOpen_le _ hx
    rw [Scheme.mem_basicOpen _ _ _ hxU, map_add (f := _)] at hx
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hx with h | h
    · have : x ∈ X.basicOpen (f a) := (Scheme.mem_basicOpen _ _ _ hxU).2 h
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨a, TopologicalSpace.Opens.mem_iSup.2 ⟨Finset.mem_insert_self a t, this⟩⟩
    · have : x ∈ X.basicOpen (∑ j ∈ t, f j) := (Scheme.mem_basicOpen _ _ _ hxU).2 h
      obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 (ih this)
      obtain ⟨hjt, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hj
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, TopologicalSpace.Opens.mem_iSup.2 ⟨Finset.mem_insert_of_mem hjt, hj⟩⟩

theorem exists_mem_nonzeroLocus_of_isShortGen : ∀ (K V Ω : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (Nm : (K →+* ℂ) → V → ℝ) (W : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (D : ℕ) (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (L : GlobalTheory.HermLB p) (ψ : Ω →+* X.functionField) (s : W → L.B.Sec), GlobalTheory.ImageModel.IsModelOf Nm W ev D p L ψ s → ev ≠ 0 → ∀ (n : ℕ) (w : Fin n → V) (abelian₂ : ℝ), GlobalTheory.CompHt.IsShortGen Nm W w abelian₂ → ∀ x : X, ∃ (j : Fin n) (hj : w j ∈ W), x ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s ⟨w j, hj⟩) := by
  intro K V Ω _ _ _ _ _ _ _ _ Nm W ev D X _ p L ψ s hM hev n w abelian₂ hg x
  have hx : x ∈ (⨆ v, ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s v)) := by rw [hM.bpf]; trivial
  obtain ⟨v, hv⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  have hw : ∀ j, w j ∈ W := fun j => (hg.gen _).2 (Submodule.subset_span ⟨j, rfl⟩)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 ((hg.gen (v : V)).1 v.2)
  have hsum : (v : V) = ∑ j, ((c j : 𝓞 K)) • ((⟨w j, hw j⟩ : W) : V) := by
    rw [← hc]; refine Finset.sum_congr rfl fun j _ => ?_
    simp [Int.cast_smul_eq_zsmul]
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hv
  rw [GlobalTheory.T.imageModel_sections_linear_ringOfIntegers K V Ω Nm W ev D X p L ψ s hM hev n (fun j => (c j : 𝓞 K)) (fun j => ⟨w j, hw j⟩) v hsum k] at hk
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 (basicOpen_sum_le _ _ hk)
  obtain ⟨-, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hj
  rw [Scheme.basicOpen_mul] at hj
  exact ⟨j, hw j, TopologicalSpace.Opens.mem_iSup.2 ⟨k, hj.2⟩⟩

end GlobalTheory.ImageModelGen
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroShortGeneratorSectionImageModelStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonzero_shortGenerator_section_imageModel : ∀ (K V Ω : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (Nm : (K →+* ℂ) → V → ℝ) (W : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (D : ℕ) (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (L : GlobalTheory.HermLB p) (ψ : Ω →+* X.functionField) (s : W → L.B.Sec), GlobalTheory.ImageModel.IsModelOf Nm W ev D p L ψ s → ev ≠ 0 → ∀ (n : ℕ) (w : Fin n → V) (abelian₂ : ℝ), GlobalTheory.CompHt.IsShortGen Nm W w abelian₂ → ∀ x : X, ∃ (j : Fin n) (hj : w j ∈ W), x ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s ⟨w j, hj⟩) := by
  first | exact @GlobalTheory.ImageModelGen.exists_mem_nonzeroLocus_of_isShortGen | exact GlobalTheory.ImageModelGen.exists_mem_nonzeroLocus_of_isShortGen | (intros; apply GlobalTheory.ImageModelGen.exists_mem_nonzeroLocus_of_isShortGen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImageModelMetricsSemiPositive
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImageModelMetricsSemiPositive
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.ImageModelSemi

open GlobalTheory.CxPts GlobalTheory.TrueGeo.OfLattice ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

theorem semiPos_of_isModelOf : ∀ (K V Ω : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (Nm : (K →+* ℂ) → V → ℝ) (W : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (D : ℕ) (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (L : GlobalTheory.HermLB p) (ψ : Ω →+* X.functionField) (s : W → L.B.Sec), GlobalTheory.ImageModel.IsModelOf Nm W ev D p L ψ s → ev ≠ 0 → L.SemiPos D := by
  intro K V Ω _ _ _ _ _ _ _ _ Nm W ev D X _ p L ψ s hM hev
  obtain ⟨N, n, b, g, A, c, gw, hF, hg, hc, hφ⟩ := hM.fs
  intro τ
  obtain ⟨σ, rfl⟩ : ∃ σ : K →+* ℂ, σ.comp (algebraMap (𝓞 K) K) = τ := ⟨_, extEmb_comp τ⟩
  let M : Matrix (Fin n) (Fin N) ℂ := fun k a => ∑ m, σ (c k m) * A σ m a
  have hz : Weight.NoCommonZero fun a =>
      ∑ j, M j a • secVal p (σ.comp (algebraMap (𝓞 K) K)) (s (gw j)) := by
    intro i y hy
    by_contra! h0
    have hS : ∑ a, ‖∑ k, M k a * valR y.1 (L.B.U i) ((s (gw k)).f i)‖ ^ 2 = 0 := by
      refine Finset.sum_eq_zero fun a _ => ?_
      have h1 := h0 a
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h1
      rw [show (∑ k, M k a * valR y.1 (L.B.U i) ((s (gw k)).f i)) = 0 from h1]
      simp
    obtain ⟨w, hw⟩ := TopologicalSpace.Opens.mem_iSup.1
      (hM.bpf.ge (TopologicalSpace.Opens.mem_top (y.1 (IsLocalRing.closedPoint ℂ))))
    have hne := (secVal_ne_zero_iff (s w) hy).2 (mem_ptsIn.2 hw)
    have hb := GlobalTheory.T.norm_sq_semilinear_le_latticeFrame_norm_sq K V Nm W N n b g A c gw σ (fun w => valR y.1 (L.B.U i) ((s w).f i)) hF hg hc
      (fun m β u x hx => GlobalTheory.T.valR_imageModelSection_semilinear K V Ω Nm W ev D X p L ψ s hM hev _ i y hy m β u x hx) w
    rw [hS, mul_zero] at hb
    exact hne (by
      have : ‖valR y.1 (L.B.U i) ((s w).f i)‖ = 0 := by nlinarith [norm_nonneg (valR y.1 (L.B.U i) ((s w).f i))]
      exact norm_eq_zero.1 this)
  have key : (L.φ (σ.comp (algebraMap (𝓞 K) K))).φ = (combWeight L.isLB (fun k => s (gw k)) M hz).φ :=
    funext fun i => funext fun y => (hφ σ i y).trans (combWeight_φ L.isLB (fun k => s (gw k)) M hz i y).symm
  intro i ch y hy ξ
  have := semiPosReg_combWeight L.isLB (fun k => s (gw k)) M hz D i ch y hy ξ
  rw [key]
  exact this

end GlobalTheory.ImageModelSemi
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImageModelMetricsSemiPositiveStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.imageModel_metrics_semiPositive : ∀ (K V Ω : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (Nm : (K →+* ℂ) → V → ℝ) (W : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (D : ℕ) (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (L : GlobalTheory.HermLB p) (ψ : Ω →+* X.functionField) (s : W → L.B.Sec), GlobalTheory.ImageModel.IsModelOf Nm W ev D p L ψ s → ev ≠ 0 → L.SemiPos D := by
  first | exact @GlobalTheory.ImageModelSemi.semiPos_of_isModelOf | exact GlobalTheory.ImageModelSemi.semiPos_of_isModelOf | (intros; apply GlobalTheory.ImageModelSemi.semiPos_of_isModelOf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortGeneratorSectionsSmallShiftedFubiniStudy
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortGeneratorSectionsSmallShiftedFubiniStudy
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.ImageModel

theorem smallSec_shift_of_isShortGen : ∀ (K V Ω : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (Nm : (K →+* ℂ) → V → ℝ) (W : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (D : ℕ) (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (L : GlobalTheory.HermLB p) (ψ : Ω →+* X.functionField) (s : W → L.B.Sec), GlobalTheory.ImageModel.IsModelOf Nm W ev D p L ψ s → ev ≠ 0 → ∀ (n : ℕ) (w : Fin n → V) (abelian₂ t : ℝ), GlobalTheory.CompHt.IsShortGen Nm W w abelian₂ → Real.log abelian₂ ≤ t → ∀ (j : Fin n) (hj : w j ∈ W), s ⟨w j, hj⟩ ∈ (L.shift (fun _ => t) (fun _ => rfl)).smallSec := by
  intro K V Ω _ _ _ _ _ _ _ _ Nm W ev D X _ p L ψ s hM hev n w abelian₂ t hw ht j hj τ y
  obtain ⟨N, n', b, g, A, c, gw, hF, hgw, hb, hφ⟩ := hM.fs
  obtain ⟨σ, rfl⟩ : ∃ σ : K →+* ℂ, σ.comp (algebraMap (𝓞 K) K) = τ :=
    ⟨_, GlobalTheory.TrueGeo.OfLattice.extEmb_comp τ⟩
  refine (le_of_eq (GlobalTheory.HermLB.nsq_shift L (fun _ => t) (fun _ => rfl)
    (GlobalTheory.CxPts.secVal p _ (s ⟨w j, hj⟩)) y)).trans ?_
  set i := GlobalTheory.CxPts.pick ((L.φ (σ.comp (algebraMap (𝓞 K) K))).isLB) y with hi_def
  have hi := GlobalTheory.CxPts.mem_pick ((L.φ (σ.comp (algebraMap (𝓞 K) K))).isLB) y
  rw [GlobalTheory.Weight.nsq_eq _ (GlobalTheory.CxPts.secVal_mem _) hi, GlobalTheory.CxPts.secVal_apply, hφ σ i y]
  set ℓ : W → ℂ := fun x => ReciprocityTheory.ChartRestriction.G.Geo.Tor.valR y.1 (L.B.U i) ((s x).f i) with hℓ
  have hlin : ∀ (m : ℕ) (β : Fin m → 𝓞 K) (u : Fin m → W) (x : W), (x : V) = ∑ k, β k • (u k : V) →
      ℓ x = ∑ k, σ (β k : K) * ℓ (u k) := fun m β u x hx =>
    GlobalTheory.T.valR_imageModelSection_semilinear K V Ω Nm W ev D X p L ψ s hM hev _ i y hi m β u x hx
  have hbd := GlobalTheory.T.norm_sq_semilinear_le_latticeFrame_norm_sq K V Nm W N n' b g A c gw σ ℓ hF hgw hb hlin ⟨w j, hj⟩
  set S := ∑ a, ‖∑ k, (∑ m, σ (c k m) * A σ m a) * ℓ (gw k)‖ ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hev' : GlobalTheory.CxPts.ev p (σ.comp (algebraMap (𝓞 K) K)) (L.B.U i) ((s ⟨w j, hj⟩).f i) y = ℓ ⟨w j, hj⟩ := rfl
  rw [hev']
  have hNm0 : 0 ≤ Nm σ (w j) := by
    rw [← hF.norm σ (w j)]; exact Real.sqrt_nonneg _
  have hNm : Nm σ (w j) ≤ abelian₂ := hw.le j σ
  have hLam0 : 0 < abelian₂ := lt_of_lt_of_le one_pos hw.one_le
  have hLt : abelian₂ ≤ Real.exp t := (Real.log_le_iff_le_exp hLam0).1 ht
  have hLam2 : abelian₂ ^ 2 * Real.exp (-(2 * t)) ≤ 1 := by
    have h1 : abelian₂ ^ 2 ≤ Real.exp t ^ 2 := pow_le_pow_left₀ hLam0.le hLt 2
    have h2 : Real.exp t ^ 2 * Real.exp (-(2 * t)) = 1 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; simp
    calc abelian₂ ^ 2 * Real.exp (-(2 * t)) ≤ Real.exp t ^ 2 * Real.exp (-(2 * t)) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = 1 := h2
  rcases hS0.eq_or_lt with h0 | hpos
  · have : ‖ℓ ⟨w j, hj⟩‖ ^ 2 ≤ 0 := by simpa [← h0] using hbd
    have hz : ‖ℓ ⟨w j, hj⟩‖ ^ 2 = 0 := le_antisymm this (sq_nonneg _)
    rw [hz]; simp
  · rw [Real.exp_neg, Real.exp_log hpos]
    have h3 : ‖ℓ ⟨w j, hj⟩‖ ^ 2 * S⁻¹ ≤ abelian₂ ^ 2 := by
      rw [← div_eq_mul_inv, div_le_iff₀ hpos]
      calc ‖ℓ ⟨w j, hj⟩‖ ^ 2 ≤ Nm σ (w j) ^ 2 * S := hbd
        _ ≤ abelian₂ ^ 2 * S := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hNm0 hNm 2) hS0
    calc ‖ℓ ⟨w j, hj⟩‖ ^ 2 * S⁻¹ * Real.exp (-(2 * t)) ≤ abelian₂ ^ 2 * Real.exp (-(2 * t)) :=
          mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
      _ ≤ 1 := hLam2

end GlobalTheory.ImageModel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortGeneratorSectionsSmallShiftedFubiniStudyStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shortGenerator_sections_small_shifted_fubiniStudy : ∀ (K V Ω : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (Nm : (K →+* ℂ) → V → ℝ) (W : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (D : ℕ) (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (L : GlobalTheory.HermLB p) (ψ : Ω →+* X.functionField) (s : W → L.B.Sec), GlobalTheory.ImageModel.IsModelOf Nm W ev D p L ψ s → ev ≠ 0 → ∀ (n : ℕ) (w : Fin n → V) (abelian₂ t : ℝ), GlobalTheory.CompHt.IsShortGen Nm W w abelian₂ → Real.log abelian₂ ≤ t → ∀ (j : Fin n) (hj : w j ∈ W), s ⟨w j, hj⟩ ∈ (L.shift (fun _ => t) (fun _ => rfl)).smallSec := by
  first | exact @GlobalTheory.ImageModel.smallSec_shift_of_isShortGen | exact GlobalTheory.ImageModel.smallSec_shift_of_isShortGen | (intros; apply GlobalTheory.ImageModel.smallSec_shift_of_isShortGen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefShiftedFubiniStudyOfShortGenerators
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.ImageModel

theorem horizontal_of_small : ∀ (k : Type) [CommRing k] (X : AlgebraicGeometry.Scheme.{0}) (p : X ⟶ Sp k) (D : ℕ), GlobalTheory.IsArithVar p D → ∀ (L : GlobalTheory.HermLB p), (∀ x : X, ∃ u ∈ L.smallSec, x ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus u) → ∀ (Z : AlgebraicGeometry.Scheme.{0}) (i : Z ⟶ X) [AlgebraicGeometry.IsClosedImmersion i] [AlgebraicGeometry.IsIntegral Z] [AlgebraicGeometry.IsLocallyNoetherian Z], CharZero Γ(Z, ⊤) → topologicalKrullDim Z = 1 → ∃ (r : (L.restr i).B.ι → Z.functionFieldˣ) (hr : GlobalTheory.Cartier.IsRatSec (L.restr i).B r), 0 ≤ (L.restr i).curveDeg hr := by
  intro k _ X p D hX L hL Z i _ _ _ hc hd
  have hZ : GlobalTheory.IsArithVar (i ≫ p) 0 := hX.of_isClosedImmersion i hc hd
  obtain ⟨u, hu1, hu⟩ := hL (i (genericPoint Z))
  have hu' : genericPoint Z ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (GlobalTheory.secPull u i) := by
    rw [GlobalTheory.nonzeroLocus_secPull]
    exact hu
  have h0 : ∀ σ (y : GlobalTheory.CxPts (i ≫ p) σ), y ∈ GlobalTheory.CxPts.ptsIn _ σ
      (ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (GlobalTheory.secPull u i)) := fun σ y => by
    rw [GlobalTheory.CxPts.mem_ptsIn]
    have e := hZ.under_eq_genericPoint y
    simp only [GlobalTheory.Cartier.under] at e
    rw [e]
    exact hu'
  refine ⟨_, GlobalTheory.Cartier.isRatSec_ratOfSec _ hu', ?_⟩
  rw [GlobalTheory.HermLB.curveDeg_sec (L := L) i _ hu' h0]
  refine sub_nonneg.2 (le_trans ?_ (finsum_nonneg fun z => mul_nonneg
    (by exact_mod_cast GlobalTheory.Cartier.mult_divOfSec_nonneg z) (Real.log_natCast_nonneg _)))
  rw [← neg_nonneg, ← finsum_neg_distrib]
  refine finsum_nonneg fun σ => ?_
  rw [← finsum_neg_distrib]
  refine finsum_nonneg fun y => ?_
  have h1 := hu1 σ (GlobalTheory.Points.PtsOver.map i rfl _ y)
  have h2 := GlobalTheory.Weight.nsq_nonneg (L.φ σ) (GlobalTheory.CxPts.secVal _ σ u) (GlobalTheory.Points.PtsOver.map i rfl _ y)
  have h3 := Real.log_nonpos h2 h1
  linarith

theorem isNef_shift_of_isShortGen : ∀ (K V Ω : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (Nm : (K →+* ℂ) → V → ℝ) (W : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (D : ℕ) (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (L : GlobalTheory.HermLB p) (ψ : Ω →+* X.functionField) (s : W → L.B.Sec) (n : ℕ) (w : Fin n → V) (abelian₂ t : ℝ), GlobalTheory.ImageModel.IsModelOf Nm W ev D p L ψ s → ev ≠ 0 → IsShortGen Nm W w abelian₂ → Real.log abelian₂ ≤ t → (L.shift (fun _ => t) (fun _ => rfl)).IsNef D := by
  intro K V Ω _ _ _ _ _ _ _ _ Nm W ev D X _ p L ψ s n w abelian₂ t hM hev hS ht
  have hw : ∀ j, w j ∈ W := fun j => (hS.gen _).2 (Submodule.subset_span ⟨j, rfl⟩)
  have hX : GlobalTheory.IsArithVar p D := hM.arith
  have hg := GlobalTheory.T.exists_nonzero_shortGenerator_section_imageModel K V Ω Nm W ev D X p L ψ s hM hev n w abelian₂ hS
  have hs := GlobalTheory.T.shortGenerator_sections_small_shifted_fubiniStudy K V Ω Nm W ev D X p L ψ s hM hev n w abelian₂ t hS ht
  refine ⟨(GlobalTheory.T.imageModel_metrics_semiPositive K V Ω Nm W ev D X p L ψ s hM hev).shift _ _, ?_, ?_⟩
  · refine GlobalTheory.TrueGeo.OfLattice.nefFib_of_isGenerated hX _ (GlobalTheory.isGenerated_of_finite (fun j => s ⟨w j, hw j⟩) ?_)
    refine top_le_iff.1 fun x _ => ?_
    obtain ⟨j, hj, hx⟩ := hg x
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, hx⟩
  · intro Z i _ _ _ hc hd
    exact horizontal_of_small _ X p D hX _ (fun x => by
      obtain ⟨j, hj, hx⟩ := hg x
      exact ⟨_, hs j hj, hx⟩) Z i hc hd

end GlobalTheory.ImageModel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefShiftedFubiniStudyOfShortGeneratorsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isNef_shifted_fubiniStudy_of_short_generators : ∀ (K V Ω : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (Nm : (K →+* ℂ) → V → ℝ) (W : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (D : ℕ) (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (L : GlobalTheory.HermLB p) (ψ : Ω →+* X.functionField) (s : W → L.B.Sec) (n : ℕ) (w : Fin n → V) (abelian₂ t : ℝ), GlobalTheory.ImageModel.IsModelOf Nm W ev D p L ψ s → ev ≠ 0 → IsShortGen Nm W w abelian₂ → Real.log abelian₂ ≤ t → (L.shift (fun _ => t) (fun _ => rfl)).IsNef D := by
  first | exact @GlobalTheory.ImageModel.isNef_shift_of_isShortGen | exact GlobalTheory.ImageModel.isNef_shift_of_isShortGen | (intros; apply GlobalTheory.ImageModel.isNef_shift_of_isShortGen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsYy
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

namespace GlobalTheory.Poinc.Sep.UMem

theorem exists_yy : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (mu : Fin 8 → X), ∃ a : X₁.S.Gam, 𝔪.YY a mu := by
  intro g n F W Z i X₁ z₁ act V _ _ _ ev X _ m t δ 𝔪 mu
  haveI : CharZero V := 𝔪.cn.2.2.2
  have hA : AdmBase V (maximalIdeal V) := ⟨𝔪.cn.1, inferInstance, 𝔪.cn.2.1, 𝔪.cn.2.2.1⟩
  have hk : 1 ≤ X₁.S.r * X₁.S.N := by
    obtain ⟨j, -, hj⟩ := X₁.ρ.r_eq
    have hn := X₁.ρ.n_prime.pos
    rw [hj, X₁.ρ.N_eq]
    exact Nat.one_le_iff_ne_zero.2 (by positivity)
  obtain ⟨h, hh⟩ := GlobalTheory.TorusExt.exists_iota (F := AlgebraicClosure (FractionRing V)) 𝔪.D.tau_bimult (𝔪.e₈ mu)
  obtain ⟨g', hg'⟩ := (GlobalTheory.UT.gt_onto_divisible_kernel GlobalTheory.firstFiveLaws V (maximalIdeal V) hA 𝔪.D
    (AlgebraicClosure (FractionRing V))).2.1 _ hk h
  let p : QkPt 𝔪.D.toPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) := ⟨𝔪.e₈ mu, g', h, hg', hh⟩
  obtain ⟨f, hf, -⟩ := GlobalTheory.TorsionIso.torsion_eq GlobalTheory.firstFiveLaws V (maximalIdeal V) hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U
    (AlgebraicClosure (FractionRing V)) _ hk
  have hx := (hf p (f p)).2 rfl
  obtain ⟨w, hw⟩ := 𝔪.U.ext
  have hpow : f p ^ (X₁.S.r * X₁.S.N) = 1 := (hx w hw).1
  let z := pushHom 𝔪.cart (TFK (R := V) (AlgebraicClosure (FractionRing V))) (f p)
  have hz : z ^ (X₁.S.r * X₁.S.N) = 1 := by
    simp only [z]
    rw [← map_pow, hpow, map_one]
  obtain ⟨a, ha, -⟩ := X₁.ρ.pt_bij (AlgebraicClosure (FractionRing V)) _ z hz
  refine ⟨a, p, f p, rfl, hx, ?_⟩
  have e := congrArg (fun q => q.left) ha
  simp only [Over.comp_left, Over.homMk_left] at e
  have e2 : spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) =
      jFK (R := V) (AlgebraicClosure (FractionRing V)) ≫ spMap 𝔪.yK := by
    simp [spMap, jFK, ← Spec.map_comp]
  rw [e2]
  exact e.symm

end GlobalTheory.Poinc.Sep.UMem
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointTorusPartEqOfEquivSameLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointTorusPartEqOfEquivSameLattice
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

namespace GlobalTheory.TInj

theorem qkPt_g_eq_of_equiv : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V), D.TauBimult → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k → ∀ p p' : QkPt D F k, p.y = p'.y → QkPt.Equiv D F p p' → p.g = p'.g := by
  intro V _ _ D hB F _ _ k hk p p' hy ⟨z, hz, h, hi, ha⟩
  letI := GlobalTheory.TorusExt.gtGroup D F
  have hkz : k • z = 0 := by
    rw [hy] at hz
    exact left_eq_add.mp hz
  have z0 : z = 0 := by
    have : ((k : ℤ)) • z = 0 := by rw [natCast_zsmul]; exact hkz
    rcases smul_eq_zero.mp this with h0 | h0
    · omega
    · exact h0
  subst z0
  have h0 : h = 0 := by
    obtain ⟨w, hw, g, hg, hadd⟩ := qk_equiv_refl hB p
    have hw0 : w = 0 := by
      have hkw : k • w = 0 := left_eq_add.mp hw
      have hwz : (k : ℤ) • w = 0 := by rw [natCast_zsmul]; exact hkw
      rcases smul_eq_zero.mp hwz with hk0 | hw0
      · omega
      · exact hw0
    subst w
    have he : h = g := GlobalTheory.TorusExt.isIota_unique hi hg
    have heq := (GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).1 hadd
    have hg0 : g = 0 := by
      have : p.g + g = p.g + 0 := by simpa using heq.symm
      exact add_left_cancel this
    exact he.trans hg0
  rw [(GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).1 ha, h0, add_zero]

end GlobalTheory.TInj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointTorusPartEqOfEquivSameLatticeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionPoint_torusPart_eq_of_equiv_same_lattice : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V), D.TauBimult → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k → ∀ p p' : QkPt D F k, p.y = p'.y → QkPt.Equiv D F p p' → p.g = p'.g := by
  first | exact @GlobalTheory.TInj.qkPt_g_eq_of_equiv | exact GlobalTheory.TInj.qkPt_g_eq_of_equiv | (intros; apply GlobalTheory.TInj.qkPt_g_eq_of_equiv <;> assumption)
end
end
