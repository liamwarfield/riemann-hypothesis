module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramedTorsionPointTorusExtensionEqOfLiesOver
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SiegelWeilLagrangianTermsAbsTsumLeHeightPoly
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransgressionCorrectionIsTopDegreeForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCompletionEqLatticeVectorAddNsmul

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFamilyTermsEqUpToNormalisingThetaConst
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFamilyTermsEqUpToNormalisingThetaConst
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Tors

noncomputable section

namespace GlobalTheory.Poinc.Sep.TermsCompare

section
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
  (F : Type) [Field F] [Algebra (FractionRing R) F]


open GlobalTheory.FieldBaseChange GlobalTheory.ExpFieldCompare in
theorem exists_expandsF_pow {w w' : W0 U} (hw : w.IsGen) (hw' : w'.IsGen) : ∃ d : F, d ≠ 0 ∧
    ∀ (k : ℕ) t s, U.ExpandsF F k w' t s → U.ExpandsF F k w t (d ^ k • s) := by
  obtain ⟨u, hu⟩ := exists_isoVal_ratio A.isLB U.LG.isLB hw' hw
  obtain ⟨c₀, hc₀, huc⟩ := BoxExpansion.unit_const GlobalTheory.firstFiveLaws.1.globalFns A U.gen u
  refine ⟨algebraMap (FractionRing R) F c₀, (map_ne_zero _).2 hc₀, fun k t s h => ?_⟩
  obtain ⟨v, h₁, h₂⟩ := h
  have z : U.ExpandsG F k (0 : GroupSec U F k) 0 := (expandsG_iff U F k _ _).2
    ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, (Fin.sum_univ_zero _).symm,
      fun α => (map_zero _).trans (Fin.sum_univ_zero _).symm⟩
  have h₃ := expandsG_lin U F k (algebraMap (FractionRing R) F c₀ ^ k) h₂ z
  rw [add_zero, add_zero] at h₃
  refine ⟨_, ?_, h₃⟩
  refine (isoRelM_iff w (prGK G F) k (U.genF F).left h₁.1 (𝟙 _) h₁.2.1 t _).2 fun y a b ha hb => ?_
  have e := (isoRelM_iff w' (prGK G F) k (U.genF F).left h₁.1 (𝟙 _) h₁.2.1 t v).1 h₁ _ (𝟙 _) y a b ha hb
  have e₃ : (𝟙 _ ≫ prGK G F) ≫ ((Over.pullback (jK R)).obj G).hom =
      ((𝟙 _ ≫ 𝟙 _) ≫ groupBase G F) ≫ jFK (R := R) F := by
    simp only [Category.id_comp]
    exact (isPullback_groupBase F).w
  have e₄ : (gm (𝟙 _ ≫ prGK G F) y ⊤ u).val = BoxExpansion.constHomVal ((𝟙 _ ≫ 𝟙 _) ≫ groupBase G F) y
      (algebraMap (FractionRing R) F c₀) :=
    ((gs_unit (𝟙 _ ≫ prGK G F) y ⊤ trivial u).symm.trans
      (congrArg (gs _ y ⊤) huc)).trans ((gs_scal _ _ y c₀).trans ((congrArg (fun q => constVal q y c₀) e₃).trans
        ((constVal_specMap _ _ y c₀).trans (BoxExpansion.constVal_eq _ _ _))))
  refine (powVal_smul (π := groupBase G F) _ v (𝟙 _ ≫ 𝟙 _) y (i := a) ha).trans ?_
  rw [e, hu _ (𝟙 _ ≫ prGK G F) y a b ha hb, mul_zpow, Units.val_mul, BoxExpansion.constVal_eq, map_pow, ← e₄,
    zpow_natCast (gm _ _ _ _), Units.val_pow_eq_pow_val, _root_.mul_assoc]


variable {F} in
theorem valAt_congr {k : ℕ} {t : SecA A F k} {x : TFK (R := R) F ⟶ A.A} {e e' : FrAt x} {c : F}
    (h : ∀ z J, Good A.L z J → val e (𝟙 _) z J = val e' (𝟙 _) z J) (H : ValAt t x e c) : ValAt t x e' c := fun z J hJ => by
  refine (H z J hJ).trans ?_
  rw [GlobalTheory.FrameMove.val_powFrame, GlobalTheory.FrameMove.val_powFrame, h z J hJ]


variable {F} in
theorem sec_eq_of_valAt (hT : SecTwistSt) {t t' : SecA A F 1} {x : TFK (R := R) F ⟶ A.A} {e : FrAt x} {c : F} (hc : c ≠ 0)
    (H : ValAt t x e c) (H' : ValAt t' x e c) : t = t' := by
  obtain ⟨b, hb⟩ := GlobalTheory.PowBasis.exists_basis_pow_field hT R A F 1 le_rfl
  have hq : Subsingleton (Fin (1 ^ A.g)) := by rw [one_pow]; infer_instance
  obtain ⟨i₀⟩ : Nonempty (Fin (1 ^ A.g)) := by rw [one_pow]; infer_instance
  obtain ⟨r, hr, -⟩ := hb t
  obtain ⟨r', hr', -⟩ := hb t'
  simp only [Fintype.sum_subsingleton _ i₀] at hr hr'
  obtain ⟨z⟩ := CoefBasic.exists_pt (R := R) (F := F)
  obtain ⟨J, hJ⟩ := CoefBasic.exists_good' A.isLB z
  have a := (GlobalTheory.ThetaCompare.sval_smul hr x hJ).symm.trans (H z J hJ)
  have a' := (GlobalTheory.ThetaCompare.sval_smul hr' x hJ).symm.trans (H' z J hJ)
  obtain ⟨q, hq'⟩ := CoefBasic.cstH_surj (R := R) z (sA (b i₀) (ptSecT A.A x).left z J)
  have b₁ : CoefBasic.cstH (R := R) z (r i₀) * CoefBasic.cstH (R := R) z q =
      CoefBasic.cstH (R := R) z c * (@id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (powFrame A.A A.L x e (1 : ℕ)) (𝟙 _) z J)).val := by
    rw [hq', ← CoefBasic.cst_eq, ← CoefBasic.cst_eq]; exact a
  have b₂ : CoefBasic.cstH (R := R) z (r' i₀) * CoefBasic.cstH (R := R) z q =
      CoefBasic.cstH (R := R) z c * (@id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (powFrame A.A A.L x e (1 : ℕ)) (𝟙 _) z J)).val := by
    rw [hq', ← CoefBasic.cst_eq, ← CoefBasic.cst_eq]; exact a'
  have q0 : q ≠ 0 := fun h => by
    rw [h, map_zero, mul_zero] at b₁
    exact hc (CoefBasic.cstH_inj z (((Units.mul_left_eq_zero _).1 b₁.symm).trans (map_zero _).symm))
  have e₀ : r i₀ = r' i₀ := by
    have := b₁.trans b₂.symm
    rw [← map_mul, ← map_mul] at this
    exact mul_right_cancel₀ q0 (CoefBasic.cstH_inj z this)
  have e₁ : ∀ j, t.f j = t'.f j := fun j => by
    have := hr j
    have e₂ : r = r' := funext fun i => by rw [Subsingleton.elim i i₀]; exact e₀
    rw [e₂] at this
    exact this.trans (hr' j).symm
  obtain ⟨f, _⟩ := t
  obtain ⟨f', _⟩ := t'
  obtain rfl : f = f' := funext e₁
  rfl

variable {F} in
theorem coef_smul {k : ℕ} (g : GtPtF D.toPre F) {w : Frm D.toPre F k g.b} (hw : w.IsGen) (c : F) (s : Fam D.toPre F k) (χ) :
    coef (c • s) g w χ = c * coef s g w χ := by
  have h₁ := ((CoefBasic.coef_basic R D.toPre F k g).2.2 w hw).2.1
  have h₂ : coef (0 : Fam D.toPre F k) g w χ = 0 := by
    have := h₁ 0 0 1 χ
    rw [one_smul, add_zero, _root_.one_mul] at this
    exact left_eq_add.1 this
  have := h₁ s 0 c χ
  rwa [add_zero, h₂, add_zero] at this


variable {U F} in
theorem liesOver_change {w₀ w₀' : W0 U} {d : F}
    (hd : ∀ (k : ℕ) t s, U.ExpandsF F k w₀ t s → U.ExpandsF F k w₀' t (d ^ k • s)) {g : GtPtF D.toPre F}
    {w w' : Frm D.toPre F 1 g.b} (hw' : w'.IsGen)
    (hv : ∀ z J, Good D.toPre.P.L z J → (val w (𝟙 _) z J).val = cst F z d * (val w' (𝟙 _) z J).val)
    {x : TFK (R := R) F ⟶ A.A} {e e' : FrAt x} (he : ∀ z J, Good A.L z J → val e (𝟙 _) z J = val e' (𝟙 _) z J)
    (H : LiesOver U w₀' g w' x e') : LiesOver U w₀ g w x e := by
  intro k hk wk hwk _ s s' v hs hval
  obtain ⟨W, hW, hWv⟩ := TorsionValue.exists_frm_pow w' hw' k
  have a := H k hk W hWv hW s _ v (hd k s s' hs) (valAt_congr he hval)
  have sc := TorsionValue.coef_scale (w' := wk) hW (c := d ^ k) (fun z J hJ => by
    rw [hwk z J hJ, hWv z J hJ, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hv z J hJ, mul_pow,
      CoefBasic.cst_eq, CoefBasic.cst_eq, map_pow]) s'
  convert a using 1
  funext χ
  rw [sc, coef_smul g hW]

end

theorem terms_eq : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (x x' : X₁.S.Gam) (C C' : Type) (lab : C → X₁.S.Gam) (lab' : C' → X₁.S.Gam) (T : (Fin 8 → X) → C → V) (T' : (Fin 8 → X) → C' → V), 𝔪.Terms x lab T → 𝔪.Terms x' lab' T' → ∀ (c : C) (c' : C'), lab c = lab' c' → ∀ mu, algebraMap V (FractionRing V) (T mu c) * 𝔪.yK ⟨X₁.S.th x, X₁.S.th_mem x⟩ = algebraMap V (FractionRing V) (T' mu c') * 𝔪.yK ⟨X₁.S.th x', X₁.S.th_mem x'⟩ := by
  intro g n F W Z i X₁ z₁ act V _ _ _ ev X _ m t δ 𝔪 x₀ x₀' C C' lab lab' T T' hT hT' c c' hc mu
  obtain ⟨x, fr, th, w₀, s, p, w, hx, hfr, hth, hw₀, hs, hg, hT⟩ := hT
  obtain ⟨x', fr', th', w₀', s', p', w', hx', hfr', hth', hw₀', hs', hg', hT'⟩ := hT'
  haveI : CharZero V := 𝔪.cn.2.2.2
  have hL : GlobalTheory.UT.LL := GlobalTheory.firstFiveLaws
  have hA : AdmBase V (maximalIdeal V) := ⟨𝔪.cn.1, inferInstance, 𝔪.cn.2.1, 𝔪.cn.2.2.1⟩
  have hk : 1 ≤ X₁.S.r * X₁.S.N := by
    have := X₁.S.r_pos; have := X₁.S.N_ge
    exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  obtain rfl : x = x' := funext fun a => Over.OverMorphism.ext
    (𝔪.cart.1.hom_ext ((hx a).trans (hx' a).symm) ((Over.w (x a)).trans (Over.w (x' a)).symm))
  have hf : ∀ a z J, Good 𝔪.A.L z J → val (fr a) (𝟙 _) z J = val (fr' a) (𝟙 _) z J := fun a z J hJ => by
    obtain ⟨J₀, hJ₀⟩ := CoefBasic.exists_good' X₁.ρ.P.isLB z
    exact mul_left_cancel (((hfr a).2 z J₀ J hJ₀ hJ).trans ((hfr' a).2 z J₀ J hJ₀ hJ).symm)
  obtain ⟨a, ha⟩ := GlobalTheory.ThetaGeneric.exists_th_ne_zero hL.1 hL.2.1 _ _ X₁.S X₁.ρ (FractionRing V) 𝔪.yK
  obtain rfl : th = th' := sec_eq_of_valAt hL.2.1.secTwist ha (valAt_congr (hf a) (hth a)) (hth' a)
  obtain ⟨d, hd0, hd⟩ := exists_expandsF_pow 𝔪.U.toUnifPre (FractionRing V) hw₀' hw₀
  have hbij := (expBijF_and_expandsF_lin hL V _ hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U).1 (FractionRing V) 1 le_rfl w₀' hw₀'
  obtain rfl : s' = d ^ 1 • s := (hbij.1 th).unique hs' (hd 1 th s hs)
  obtain ⟨h₁, h₂, h₃⟩ := hg c
  obtain ⟨h₁', h₂', h₃'⟩ := hg' c'
  rw [hT, hT']
  rw [← hc] at h₃'
  obtain ⟨w₁, hw₁, hv₁⟩ := TorsionValue.exists_frm_scale (w' c') h₂' hd0
  have h₄ : LiesOver 𝔪.U.toUnifPre w₀ (p' c') w₁ (x (lab c)) (fr (lab c)) :=
    liesOver_change hd h₂' hv₁ (hf _) h₃'
  obtain ⟨e, ev⟩ := GlobalTheory.T.framedTorsionPoint_torusExtension_eq_of_liesOver V 𝔪.cn 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U w₀ hw₀ _ hk _ _ _ _ _ _ h₁ h₁' h₂ hw₁ (hfr _).1 h₃ h₄
  rw [coef_smul _ h₂', pow_one]
  generalize w c = om at h₂ ev
  generalize p c = q at om h₂ e ev
  subst e
  exact TorsionValue.coef_scale h₂' (fun z J hJ => by rw [ev z J hJ, hv₁ z J hJ]) s _

end GlobalTheory.Poinc.Sep.TermsCompare

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFamilyTermsEqUpToNormalisingThetaConstStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaFamily_terms_eq_up_to_normalising_thetaConst : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (x x' : X₁.S.Gam) (C C' : Type) (lab : C → X₁.S.Gam) (lab' : C' → X₁.S.Gam) (T : (Fin 8 → X) → C → V) (T' : (Fin 8 → X) → C' → V), 𝔪.Terms x lab T → 𝔪.Terms x' lab' T' → ∀ (c : C) (c' : C'), lab c = lab' c' → ∀ mu, algebraMap V (FractionRing V) (T mu c) * 𝔪.yK ⟨X₁.S.th x, X₁.S.th_mem x⟩ = algebraMap V (FractionRing V) (T' mu c') * 𝔪.yK ⟨X₁.S.th x', X₁.S.th_mem x'⟩ := by
  first | exact @GlobalTheory.Poinc.Sep.TermsCompare.terms_eq | exact GlobalTheory.Poinc.Sep.TermsCompare.terms_eq | (intros; apply GlobalTheory.Poinc.Sep.TermsCompare.terms_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResEtaOfIsWeilSch
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsMovedNotProportional
set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open MeasureTheory ValuativeRel Matrix IsLocalRing
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LatPair GlobalTheory.SeeSaw

namespace GlobalTheory.PlaceCompare.Spherical

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n'' n' n : Type} [Fintype n''] [DecidableEq n''] [Fintype n'] [DecidableEq n'] [Fintype n] [DecidableEq n]

end Local

section Global

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice _root_.Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum IsDedekindDomain NumberField
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem exists_unram_char (D : D7) (n : ℕ) :
    ∃ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ ∧ ResEta D χ n ∧ UnramEverywhere D χ := by
  obtain ⟨η, h1, h2, h3, -⟩ := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  refine ⟨η ^ n, ⟨?_, fun x => ?_⟩, ⟨h3.1, fun e he a => ?_⟩, fun x a b c => ?_⟩
  · have : ((η ^ n : (AE D)ˣ →* Circle) : (AE D)ˣ → Circle) = fun x => η x ^ n := by
      funext x; simp
    rw [this]
    exact h1.1.pow n
  · rw [MonoidHom.pow_apply, h1.2 x, one_pow]
  · rw [MonoidHom.pow_apply, h3.2 e he a, pow_one]
  · rw [MonoidHom.pow_apply, h2 x a b c, one_pow]

end Global

end GlobalTheory.PlaceCompare.Spherical

end
end

section -- merged from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsSchwartz
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula GlobalTheory.SiegelFormula.Model

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Published.ThetaConvModel

variable {D : D7}

theorem exists_schwartz (θ : InfFam D) (m n : ℕ) : ∃ Φ : schwartzA θ m n, Φ.1 0 ≠ 0 := by
  classical
  let b : ContDiffBump (0 : D.what₂.Tau → Fin m → Fin n → ℂ) := ⟨1, 2, one_pos, one_lt_two⟩
  have hb1 : HasCompactSupport fun x => ((b x : ℝ) : ℂ) := b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  have hb2 : ContDiff ℝ (⊤ : ℕ∞) fun x => ((b x : ℝ) : ℂ) := Complex.ofRealCLM.contDiff.comp b.contDiff
  let f : SchwartzMap (D.what₂.Tau → Fin m → Fin n → ℂ) ℂ := hb1.toSchwartzMap hb2
  have hf : f 0 = 1 := by
    show ((b 0 : ℝ) : ℂ) = 1
    rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)]; simp
  let W : AddSubgroup (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E)) :=
    { carrier := {a | ∀ i j, a i j ∈ Formalism.L2.Theta.intAE D}
      add_mem' := fun ha hb i j => (Formalism.L2.Theta.intAE D).add_mem (ha i j) (hb i j)
      zero_mem' := fun _ _ => (Formalism.L2.Theta.intAE D).zero_mem
      neg_mem' := fun ha i j => (Formalism.L2.Theta.intAE D).neg_mem (ha i j) }
  have hWe : (W : Set (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))) =
      ⋂ i, ⋂ j, (fun a : Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) => a i j) ⁻¹'
        (Formalism.L2.Theta.intAE D : Set (Af D.host.F ⊗[D.host.F] D.host.E)) := by
    ext a
    simp only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
    rfl
  have hWo : IsOpen (W : Set (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))) := by
    rw [hWe]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      (GlobalTheory.SchwartzBruhatTensor.isOpen_intAE D).preimage ((continuous_apply j).comp (continuous_apply i))
  have hWc : IsCompact (W : Set (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))) :=
    isCompact_pi_infinite fun _ => isCompact_pi_infinite fun _ => GlobalTheory.SchwartzBruhatTensor.isCompact_intAE D
  let g : (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ := fun a =>
    if (QuotientAddGroup.mk (show Matrix (Fin m) (Fin n) _ from a) : _ ⧸ W) = 0 then (1 : ℂ) else 0
  have hg : g ∈ GlobalTheory.WeilM.SB (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) :=
    GlobalTheory.SchwartzBruhatTensor.coset_mem_SB W hWo hWc 0
  let φ : Mx D m n → ℂ := fun x =>
    f (fun τ i j => compAt θ τ x i j) * g (fun i j => finPart D (x i j))
  have hφ : φ ∈ schwartzA θ m n := Submodule.subset_span ⟨f, g, hg, rfl⟩
  refine ⟨⟨φ, hφ⟩, ?_⟩
  show f _ * g _ ≠ 0
  have e : (fun τ i j => compAt θ τ (0 : Mx D m n) i j : D.what₂.Tau → Fin m → Fin n → ℂ) = 0 := by
    ext τ i j; simp [compAt]
  rw [e, hf]
  simp [g]
  exact (QuotientAddGroup.eq_zero_iff (N := W) (0 : Matrix (Fin m) (Fin n) _)).2 W.zero_mem

end GlobalTheory.Published.ThetaConvModel

end
end

noncomputable section

open scoped Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory GlobalTheory.RegSch
open Filter Topology

namespace GlobalTheory.RegSch.JointCont


open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model in
theorem levi_weyl_rel {R : Type} [CommRing R] {n : ℕ} {b c : Matrix (Fin n) (Fin n) R} (h1 : b * c = 1) (h2 : c * b = 1) :
    blk4 b 0 0 c * blk4 0 1 (-1) 0 = blk4 1 b 0 1 * blk4 0 1 (-1) 0 * blk4 1 c 0 1 *
      (blk4 0 1 (-1) 0 * blk4 0 1 (-1) 0 * blk4 0 1 (-1) 0) * blk4 1 b 0 1 := by
  simp [submatrix_fromBlocks_mul, h1, h2]


open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model in
theorem resEta_of_isWeilSch {D : D7} {n : ℕ} (hn : 0 < n) {V : HSp D} {ψ : AddChar (AF D.host.F) ℂ}
    (hψ : IsCharAF D.host.F ψ) {θ : InfFam D} (hθ : IsInfFam θ) {χ : (AE D)ˣ →* Circle}
    {μ : Measure (Mx D V.rank n)} {𝓕 : Set (Mx D V.rank n)} (hμ : IsCovolOne (ratMx D V.rank n) μ 𝓕)
    {ω : StdUnn.G D n →* Module.End ℂ (schwartzA θ V.rank n)} (hω : IsWeilSch ψ χ θ V μ ω) : ResEta D χ V.rank := by
  obtain ⟨χ₀, h1, h2, -⟩ := GlobalTheory.PlaceCompare.Spherical.exists_unram_char D V.rank
  obtain ⟨ψ₀, h₀, lam, hlam, hψeq⟩ := GlobalTheory.ThetaAllChar.exists_std hψ
  have hsh : ψ = shift ψ₀ lam := by
    ext x
    rw [hψeq]
    rfl
  obtain ⟨ω₀, hω₀⟩ := Inhab.weil_exists D n V ψ₀ h₀ lam hlam χ₀ h1 h2 θ hθ μ 𝓕 hμ
  rw [← hsh] at hω₀
  suffices h : ∀ t, χ (idF D t) = χ₀ (idF D t) from ⟨h2.1, fun η hη a => (h a).trans (h2.2 η hη a)⟩
  intro t
  let i₀ : Fin n := ⟨0, hn⟩
  let dg : (AF D.host.F)ˣ → Mx D n n := fun u => Matrix.diagonal (Function.update 1 i₀ (idF D u : AE D))
  have hmul : ∀ u u', dg u * dg u' = dg (u * u') := fun u u' => by
    simp only [dg, Matrix.diagonal_mul_diagonal, map_mul, Units.val_mul]
    congr 1
    funext i
    by_cases hi : i = i₀
    · subst hi; simp
    · simp [Function.update_of_ne hi]
  have hone : dg 1 = 1 := by simp [dg]
  have hadj : ∀ u, adj (dg u) = dg u := fun u => by
    ext i j
    simp only [adj, dg, Matrix.transpose_apply, Matrix.map_apply, Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij
      by_cases hi : i = i₀
      · subst hi
        simp only [if_true, Function.update_self]
        exact GlobalTheory.HermTransversal.cA_algebraMap _
      · simp [Function.update_of_ne hi]
    · simp [hij, Ne.symm hij]
  have e1 : dg t * dg t⁻¹ = 1 := by rw [hmul, mul_inv_cancel, hone]
  have e2 : dg t⁻¹ * dg t = 1 := by rw [hmul, inv_mul_cancel, hone]
  let a : GL (Fin n) (AE D) := ⟨dg t, dg t⁻¹, e1, e2⟩
  have hdet : Matrix.GeneralLinearGroup.det a = idF D t := by
    ext
    simp [a, dg, Finset.prod_update_of_mem]
  obtain ⟨g, hg⟩ := exists_levi (D := D) (n := n) a
  obtain ⟨u, hu⟩ := (exists_unip (dg t)).2 (hadj t)
  obtain ⟨u', hu'⟩ := (exists_unip (dg t⁻¹)).2 (hadj t⁻¹)
  obtain ⟨w, hw⟩ := exists_weyl (D := D) (n := n)
  have hinj : ∀ x y : StdUnn.G D n, mat x = mat y → x = y := fun x y h => Subtype.ext (Units.ext h)
  have hrel : g * w = u * w * u' * (w * w * w) * u := by
    refine hinj _ _ ?_
    have e4 : (adj (a⁻¹).1 : Mx D n n) = dg t⁻¹ := hadj t⁻¹
    rw [e4] at hg
    change mat g * mat w = mat u * mat w * mat u' * (mat w * mat w * mat w) * mat u
    rw [hg, hw, hu, hu']
    exact levi_weyl_rel e1 e2
  let S := ω.toHomUnits.eqLocus ω₀.toHomUnits
  have hU : ∀ (x : StdUnn.G D n) (b : Mx D n n), mat x = blk4 1 b 0 1 → x ∈ S := fun x b hx =>
    Units.ext (LinearMap.ext fun Φ => Subtype.ext (funext fun y => (hω.unip x b hx Φ y).trans (hω₀.unip x b hx Φ y).symm))
  have hW : w ∈ S :=
    Units.ext (LinearMap.ext fun Φ => Subtype.ext (funext fun y => (hω.weyl w hw Φ y).trans (hω₀.weyl w hw Φ y).symm))
  have hgS : g ∈ S := by
    rw [← S.mul_mem_cancel_right hW, hrel]
    exact S.mul_mem (S.mul_mem (S.mul_mem (S.mul_mem (hU _ _ hu) hW) (hU _ _ hu')) (S.mul_mem (S.mul_mem hW hW) hW)) (hU _ _ hu)
  have hge : ω g = ω₀ g := congrArg Units.val hgS
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.Published.ThetaConvModel.exists_schwartz θ V.rank n
  have k1 := hω.levi g a hg Φ 0
  rw [hge, hω₀.levi g a hg Φ 0, hdet] at k1
  have z1 : ((0 : Mx D V.rank n) ⬝ a.1 : Mx D V.rank n) = 0 := Matrix.zero_mul _
  rw [z1] at k1
  have hp : npow (absA D (idF D t)) ((V.rank : ℂ) / 2) ≠ 0 := by
    have : absA D (idF D t) ≠ 0 := ((Group.isUnit _).map (absA D)).ne_zero
    rw [npow, Complex.cpow_def_of_ne_zero (by exact_mod_cast this)]
    exact Complex.exp_ne_zero _
  exact Circle.ext (mul_right_cancel₀ hp (mul_right_cancel₀ hΦ k1)).symm

end GlobalTheory.RegSch.JointCont

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BearsFlagUnitriangularIffMemCell
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLuSubring
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.FlagLU

theorem det_lead {K : Type} [CommRing K] {s : ℕ} (g : Matrix (Fin s) (Fin s) K) (l : ℕ) (hl : l ≤ s) :
    (g.submatrix (Fin.castLE hl) (Fin.castLE hl)).det =
      (g.submatrix (Subtype.val : {a : Fin s // (a : ℕ) < l} → Fin s) Subtype.val).det := by
  let e : Fin l ≃ {a : Fin s // (a : ℕ) < l} :=
    { toFun := fun i => ⟨Fin.castLE hl i, i.2⟩
      invFun := fun a => ⟨a.1, a.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← Matrix.det_submatrix_equiv_self e]
  rfl

theorem exists_lu_subring : ∀ (K : Type) [Field K] (O : Subring K) (s : ℕ) (g : Matrix (Fin s) (Fin s) K), (∀ i j, g i j ∈ O) → (∀ k : ℕ, (g.submatrix (Subtype.val : {a : Fin s // (a : ℕ) < k} → Fin s) Subtype.val).det ≠ 0 ∧ ((g.submatrix (Subtype.val : {a : Fin s // (a : ℕ) < k} → Fin s) Subtype.val).det)⁻¹ ∈ O) → ∃ (y : Low s → K) (b : Matrix (Fin s) (Fin s) K), (∀ j, y j ∈ O) ∧ (∀ i j, b i j ∈ O) ∧ (∀ i j, i < j → b i j = 0) ∧ g = b * upU y := by
  intro K _ O s g hg hmin
  let A : Matrix (Fin s) (Fin s) O := Matrix.of fun i j => ⟨g j i, hg j i⟩
  have hA : A.map O.subtype = gᵀ := by ext i j; rfl
  have hu : ∀ l : Fin (s + 1), IsUnit (A.submatrix (Fin.castLE l.is_le) (Fin.castLE l.is_le)).det := by
    intro l
    have h1 : ((A.submatrix (Fin.castLE l.is_le) (Fin.castLE l.is_le)).det : K) =
        (g.submatrix (Subtype.val : {a : Fin s // (a : ℕ) < l} → Fin s) Subtype.val).det := by
      have h2 := det_lead g l l.is_le
      rw [← O.coe_subtype, RingHom.map_det, RingHom.mapMatrix_apply, ← Matrix.submatrix_map, hA,
        ← Matrix.transpose_submatrix, Matrix.det_transpose, h2]
    obtain ⟨h0, hi⟩ := hmin l
    refine isUnit_iff_exists_inv.2 ⟨⟨_, hi⟩, Subtype.ext ?_⟩
    rw [Subring.coe_mul, h1]
    exact mul_inv_cancel₀ h0
  obtain ⟨n, M, hM, -, hAe⟩ := GlobalTheory.FlagCell.exists_lu O s A hu
  refine ⟨fun j => n j, (M.map O.subtype)ᵀ, fun j => (n j).2, fun i j => (M j i).2, ?_, ?_⟩
  · intro i j hij
    show ((M j i : O) : K) = 0
    rw [hM (i := j) (j := i) hij]; rfl
  · have key : A.map O.subtype = (GlobalTheory.FlagCell.uniR n * M).map O.subtype := by rw [← hAe]
    rw [hA, Matrix.map_mul, GlobalTheory.FlagCell.map_uniR] at key
    have h3 : (upU fun j => (n j : K)) = (GlobalTheory.FlagCell.uniR fun j => O.subtype (n j))ᵀ := by
      ext a b
      simp only [upU, Matrix.of_apply, Matrix.transpose_apply, GlobalTheory.FlagCell.uniR_apply, eq_comm]
      rfl
    rw [h3, ← Matrix.transpose_mul, ← key, Matrix.transpose_transpose]

end GlobalTheory.FlagLU
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowMulUpULeadMinorNeZero
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

set_option autoImplicit false

namespace GlobalTheory.FlagCell2

theorem lowMul_upU_leadMinor_ne_zero (K : Type) [Field K] (s : ℕ) (y : Low s → K) (b : Matrix (Fin s) (Fin s) K) (hb : ∀ i j, i < j → b i j = 0) (hdet : b.det ≠ 0) :
    (upU y).det = 1 ∧ ∀ k : ℕ, ((b * upU y).submatrix (Subtype.val : {a : Fin s // (a : ℕ) < k} → Fin s) Subtype.val).det ≠ 0 := by
  have hU : ∀ a c : Fin s, c < a → upU y a c = 0 := by
    intro a c h
    simp [upU, Matrix.of_apply, not_lt.mpr h.le, h.ne']
  have hUd : ∀ a : Fin s, upU y a a = 1 := by
    intro a; simp [upU, Matrix.of_apply]
  have hdiag : ∀ i, b i i ≠ 0 := by
    have h1 : b.det = ∏ i, b i i := Matrix.det_of_lowerTriangular b (fun i j h => hb i j h)
    rw [h1] at hdet
    intro i
    exact (Finset.prod_ne_zero_iff.mp hdet) i (Finset.mem_univ _)
  refine ⟨?_, ?_⟩
  · rw [Matrix.det_of_upperTriangular (fun a c h => hU a c h)]
    simp [hUd]
  · intro k
    have hmul : (b * upU y).submatrix (Subtype.val : {a : Fin s // (a : ℕ) < k} → Fin s)
          (Subtype.val : {a : Fin s // (a : ℕ) < k} → Fin s) =
        b.submatrix (Subtype.val : {a : Fin s // (a : ℕ) < k} → Fin s) (Subtype.val : {a : Fin s // (a : ℕ) < k} → Fin s) *
          (upU y).submatrix (Subtype.val : {a : Fin s // (a : ℕ) < k} → Fin s)
            (Subtype.val : {a : Fin s // (a : ℕ) < k} → Fin s) := by
      ext i j
      simp only [Matrix.submatrix_apply, Matrix.mul_apply]
      rw [← Fintype.sum_subtype_add_sum_subtype (fun a : Fin s => (a : ℕ) < k)]
      have h0 : ∑ l : {a : Fin s // ¬ (a : ℕ) < k}, b i.1 l.1 * upU y l.1 j.1 = 0 := by
        apply Finset.sum_eq_zero
        intro l _
        have : i.1 < l.1 := by
          have := i.2; have := l.2; rw [Fin.lt_iff_val_lt_val]; omega
        rw [hb _ _ this, zero_mul]
      rw [h0, add_zero]
    rw [hmul, Matrix.det_mul]
    refine mul_ne_zero ?_ ?_
    · rw [Matrix.det_of_lowerTriangular _ (fun i j h => hb i.1 j.1 h)]
      exact Finset.prod_ne_zero_iff.mpr (fun i _ => hdiag i.1)
    · rw [Matrix.det_of_upperTriangular (fun i j h => hU i.1 j.1 h)]
      simp [hUd]

end GlobalTheory.FlagCell2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BearsFlagUnitriangularIffMemCell
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.FlagCell2.BearsCell

variable {ι : Type} {m : ι → ℕ}

theorem upM_map {K K' : Type} [Field K] [Field K'] (v : K → K') (h0 : v 0 = 0) (h1 : v 1 = 1) (u : Cell m → K) :
    (upM u).map v = upM fun j => v (u j) := by
  funext τ
  ext a b
  simp only [Mat.map, upM, upU, Matrix.map_apply, Matrix.of_apply]
  split_ifs <;> simp [h0, h1]

theorem det_upM {K : Type} [Field K] (u : Cell m → K) (τ : ι) : (upM u τ).det = 1 :=
  (GlobalTheory.FlagCell2.lowMul_upU_leadMinor_ne_zero K (m τ) _ 1 (fun _ _ h => Matrix.one_apply_ne h.ne) (by simp)).1

theorem exists_lu {K K' : Type} [Field K] [Field K'] {O : Subring K} (v : K → K') (ψ : O →+* K')
    (hv : ∀ x : O, v x = ψ x) (hu : ∀ x : O, ψ x ≠ 0 → (x : K) ≠ 0 ∧ (x : K)⁻¹ ∈ O) {g : Mat m K} (hg : Par 0 O g)
    {y₀ : Cell m → K'} (hP : Par m ⊤ (upM y₀ * (g.map v)⁻¹)) :
    ∃ (u : Cell m → K) (b : Mat m K), Par m O b ∧ g = b * upM u ∧ ∀ j, v (u j) = y₀ j := by
  have hgv := hg.map_of v ψ hv
  have hy : ∀ τ, (upM y₀ τ).det ≠ 0 := fun τ => (det_upM y₀ τ).trans_ne one_ne_zero
  have e : g.map v = (upM y₀ * (g.map v)⁻¹)⁻¹ * upM y₀ := by
    rw [Mat.mul_inv_rev, Mat.inv_inv hgv.det_ne, mul_assoc, Mat.inv_mul hy, mul_one]
  have hmin : ∀ τ (k : ℕ), ((g τ).submatrix (Subtype.val : {a : Fin (m τ) // (a : ℕ) < k} → Fin (m τ)) Subtype.val).det ≠ 0 ∧
      (((g τ).submatrix (Subtype.val : {a : Fin (m τ) // (a : ℕ) < k} → Fin (m τ)) Subtype.val).det)⁻¹ ∈ O := fun τ k => by
    let N : Matrix {a : Fin (m τ) // (a : ℕ) < k} {a : Fin (m τ) // (a : ℕ) < k} O := fun a b => ⟨_, (hg τ).1 a.1 b.1⟩
    have e1 : (N.det : K) = ((g τ).submatrix (Subtype.val : {a : Fin (m τ) // (a : ℕ) < k} → Fin (m τ)) Subtype.val).det :=
      O.subtype.map_det N
    have e2 : ψ.mapMatrix N =
        (g.map v τ).submatrix (Subtype.val : {a : Fin (m τ) // (a : ℕ) < k} → Fin (m τ)) Subtype.val := by
      ext a b
      exact (hv (N a b)).symm
    rw [← e1]
    refine hu _ ?_
    rw [ψ.map_det, e2, e]
    exact (GlobalTheory.FlagCell2.lowMul_upU_leadMinor_ne_zero K' (m τ) _ _ (fun i j h => (hP.inv τ).2.2.2 i j i.2 h) (hP.inv.det_ne τ)).2 k
  choose y b h1 h2 h3 h4 using fun τ => GlobalTheory.FlagLU.exists_lu_subring K O (m τ) (g τ) (hg τ).1 (hmin τ)
  have hgb : g = b * upM (fun j : Cell m => y j.1 j.2) := funext h4
  have hd : ∀ τ, (b τ).det = (g τ).det := fun τ => by
    rw [hgb, Pi.mul_apply, Matrix.det_mul, det_upM, mul_one]
  have hb : Par m O b := fun τ => ⟨h2 τ, hd τ ▸ (hg τ).2.1, hd τ ▸ (hg τ).2.2.1, fun i j _ h => h3 τ i j h⟩
  have hU : Par 0 O (upM fun j : Cell m => y j.1 j.2) := by
    have := (hb.inv.mono (k' := 0) (fun _ => Nat.zero_le _) le_rfl).mul hg
    rwa [hgb, ← mul_assoc, Mat.inv_mul hb.det_ne, one_mul] at this
  refine ⟨_, b, hb, hgb, fun j => ?_⟩
  have e3 : g.map v = Mat.map b v * upM fun j : Cell m => v (y j.1 j.2) := by
    rw [← upM_map v ((hv 0).trans (map_zero ψ)) ((hv 1).trans (map_one ψ)), ← Par.map_mul_of hb hU v ψ hv, ← hgb]
  have e4 : upM y₀ = (upM y₀ * (g.map v)⁻¹ * Mat.map b v) * upM fun j : Cell m => v (y j.1 j.2) := by
    rw [mul_assoc, ← e3, mul_assoc, Mat.inv_mul hgv.det_ne, mul_one]
  have hc := hP.mul (hb.map_of v ψ hv)
  exact (congrFun (GlobalTheory.FlagCell2.upU_unique_of_lower K' (m j.1) _ _ _ (fun i k h => (hc j.1).2.2.2 i k i.2 h) (congrFun e4 j.1)) j.2).symm

theorem bears_iff : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ (A : Mat m X.Fn) (K : Type) [Field K] (p : Sp K ⟶ Y.X), A ∈ E.S (f (p (IsLocalRing.closedPoint K))) → ∀ y₀ : Cell m → K, Bears E' φ A (upM y₀) p ↔ ∃ u : Cell m → Y.Fn, upM u * A.map φ ∈ E'.S (p (IsLocalRing.closedPoint K)) ∧ ∀ j, (ratOf Y).val p (u j) = y₀ j := by
  intro F _ X Y ι _ m E E' φ f hf A K _ p hA y₀
  have hd : ∀ σ, (A.map φ σ).det ≠ 0 := fun σ =>
    (Mat.det_map A (φ : X.Fn →+* Y.Fn) σ).trans_ne ((map_ne_zero _).2 (Fr.det_ne hA σ))
  have hr := GlobalTheory.ZH.RatModel.range_eq_singleton (M := ratOf Y) p (IsLocalRing.closedPoint K)
  constructor
  · rintro ⟨A', hA', hP⟩
    obtain ⟨u, b, hb, hg, hu⟩ := exists_lu ((ratOf Y).val p) (GlobalTheory.ZH.RatModel.valHom (M := ratOf Y) p _ hr)
      (fun _ => rfl) (fun x hx => (GlobalTheory.ZH.RatModel.isUnit_O_iff x).1
        ((GlobalTheory.ZH.RatModel.val_ne_zero_iff (M := ratOf Y) hr x).1 hx)) (hf.sub _ A' hA' A hA) hP
    refine ⟨u, (Fr.mem_iff hA').2 ?_, hu⟩
    have e : upM u * A.map φ * A'⁻¹ = b⁻¹ := by
      have e1 : upM u = b⁻¹ * (A' * (A.map φ)⁻¹) := by
        rw [hg, ← mul_assoc, Mat.inv_mul hb.det_ne, one_mul]
      rw [e1, mul_assoc b⁻¹, mul_assoc A', Mat.inv_mul hd, mul_one, mul_assoc, Mat.mul_inv (Fr.det_ne hA'), mul_one]
    rw [e]
    exact hb.inv
  · rintro ⟨u, hu, hy⟩
    refine ⟨_, hu, ?_⟩
    rw [mul_assoc, Mat.mul_inv hd, mul_one,
      upM_map ((ratOf Y).val p) (GlobalTheory.ZH.RatModel.val_zero (M := ratOf Y) p)
        (GlobalTheory.ZH.RatModel.val_one (M := ratOf Y) p), show (fun j => (ratOf Y).val p (u j)) = y₀ from funext hy,
      Mat.mul_inv fun τ => (det_upM y₀ τ).trans_ne one_ne_zero]
    exact Par.one

end GlobalTheory.FlagCell2.BearsCell
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BearsFlagUnitriangularIffMemCellStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bearsFlag_unitriangular_iff_mem_cell : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ (A : Mat m X.Fn) (K : Type) [Field K] (p : Sp K ⟶ Y.X), A ∈ E.S (f (p (IsLocalRing.closedPoint K))) → ∀ y₀ : Cell m → K, Bears E' φ A (upM y₀) p ↔ ∃ u : Cell m → Y.Fn, upM u * A.map φ ∈ E'.S (p (IsLocalRing.closedPoint K)) ∧ ∀ j, (ratOf Y).val p (u j) = y₀ j := by
  first | exact @GlobalTheory.FlagCell2.BearsCell.bears_iff | exact GlobalTheory.FlagCell2.BearsCell.bears_iff | (intros; apply GlobalTheory.FlagCell2.BearsCell.bears_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorSmallCosetHalfIsSchwartzBruhat
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorSmallCosetHalfIsSchwartzBruhat
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory ValuativeRel
open scoped TensorProduct nonZeroDivisors Pointwise

namespace GlobalTheory.FunObj.CosSB

open GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames _root_.Formalism.L2.Host _root_.Formalism.L2.DIV GlobalTheory.LatVac
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

variable {D : D7}

section Small

variable {a b : ℕ}

theorem frAt_add (w : Pl D.host.E) (β' : GL (Fin b) (Lev.EAf D)) (β : GL (Fin a) (Lev.EAf D)) (x y : Mx D b a) :
    frAt w β' β (x + y) = frAt w β' β x + frAt w β' β y := by
  unfold frAt
  have h : (x + y).map (toEAf D) = x.map (toEAf D) + y.map (toEAf D) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.add_apply, map_add]
  rw [h, Comparison₂.fr_add]
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, map_add]

theorem frAt_sub (w : Pl D.host.E) (β' : GL (Fin b) (Lev.EAf D)) (β : GL (Fin a) (Lev.EAf D)) (x y : Mx D b a) :
    frAt w β' β (x - y) = frAt w β' β x - frAt w β' β y := by
  unfold frAt
  rw [Matrix.map_sub _ (toEAf D).map_sub, Comparison₂.fr_sub, Matrix.map_sub _ (cpt (D := D) w).map_sub]

theorem isSmall_add {P : Finset (Pl D.host.E)} {β' : GL (Fin b) (Lev.EAf D)} {β : GL (Fin a) (Lev.EAf D)} {n : ℤ}
    {x y : Mx D b a} (hx : IsSmall P β' β n x) (hy : IsSmall P β' β n y) : IsSmall P β' β n (x + y) :=
  fun w hw i j => by
    rw [frAt_add, Matrix.add_apply]
    exact Valuation.map_add_le _ (hx w hw i j) (hy w hw i j)

theorem isSmall_sub {P : Finset (Pl D.host.E)} {β' : GL (Fin b) (Lev.EAf D)} {β : GL (Fin a) (Lev.EAf D)} {n : ℤ}
    {x y : Mx D b a} (hx : IsSmall P β' β n x) (hy : IsSmall P β' β n y) : IsSmall P β' β n (x - y) :=
  fun w hw i j => by
    rw [frAt_sub, Matrix.sub_apply]
    exact Valuation.map_sub_le _ (hx w hw i j) (hy w hw i j)

theorem isHalf_add_nsmul {e : AE D} {t u : Mx D b a} (k : ℕ) (hu : IsHalf e u) : IsHalf e (t + k • u) ↔ IsHalf e t := by
  have h : ∀ i j, e * (t + k • u) i j = e * t i j + k • u i j := fun i j => by
    rw [Matrix.add_apply, Matrix.smul_apply, nsmul_eq_mul, mul_add, mul_left_comm, hu i j]
  unfold IsHalf
  refine forall₂_congr fun i j => ?_
  rw [h, Matrix.add_apply, Matrix.smul_apply, add_left_inj]

theorem v_unif_pow (w : Pl D.host.E) (n : ℕ) :
    Valued.v (((unifAt w ^ (n : ℤ) : (Kw w)ˣ)) : Kw w) = WithZero.exp (-(n : ℤ)) := by
  have h : Valued.v (unifAt w : Kw w) = WithZero.exp (-1 : ℤ) := unif_spec w
  rw [zpow_natCast, Units.val_pow_eq_pow_val, map_pow, h, ← WithZero.exp_nsmul]
  simp

theorem val_le_unif_iff (w : Pl D.host.E) (n : ℕ) (x : Kw w) :
    valuation (Kw w) x ≤ valuation (Kw w) (((unifAt w ^ (n : ℤ) : (Kw w)ˣ)) : Kw w) ↔
      Valued.v x ≤ WithZero.exp (-(n : ℤ)) :=
  (Comparison₂.vEq w _ _).trans (by rw [v_unif_pow])

end Small

section Lat

variable {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
  {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

theorem nsmul_mem_hatMx {b : ℕ} (h2 : ∀ x ∈ latRat S T ΛS ΛT, b • x ∈ homLat ΛS ΛT) (𝔪 : Ideal (𝓞 D.host.E))
    {u : WO S T} (hu : u ∈ latO S T ΛS ΛT fun _ => True) :
    (b * Ideal.absNorm 𝔪) • u ∈ hatMx (𝔪 • homLat ΛS ΛT) := by
  refine latO_induction (p := fun u => (b * Ideal.absNorm 𝔪) • u ∈ hatMx (𝔪 • homLat ΛS ΛT)) ?_ ?_ ?_ ?_ hu
  · intro α hα X hX
    rw [← WeilOver.finTens_nsmul]
    refine AddSubgroup.subset_closure ⟨α, hα, _, ?_, rfl⟩
    rw [mul_nsmul, ← Nat.cast_smul_eq_nsmul (𝓞 D.host.E)]
    exact Submodule.smul_mem_smul (Ideal.absNorm_mem _) (h2 X hX)
  · rw [nsmul_zero]; exact zero_mem _
  · intro x y hx hy; rw [nsmul_add]; exact add_mem hx hy
  · intro x hx; rw [neg_nsmul]; exact neg_mem hx

theorem nsmul_mem_latO {a : ℕ} (h1 : ∀ x ∈ homLat ΛS ΛT, a • x ∈ latRat S T ΛS ΛT) (𝔪 : Ideal (𝓞 D.host.E))
    {u : WO S T} (hu : u ∈ hatMx (𝔪 • homLat ΛS ΛT)) : a • u ∈ latO S T ΛS ΛT fun _ => True := by
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, x, hx, rfl⟩ := hw
    exact WeilOver.finTens_nsmul α a x ▸ finTens_mem_latO hα (h1 x (Submodule.smul_le_right hx))
  | zero => rw [nsmul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [nsmul_add]; exact add_mem hx hy
  | neg x _ hx => rw [neg_nsmul]; exact neg_mem hx

theorem isSmall_of_mem_hatMx {βS : GL (Fin S.rank) (Lev.EAf D)} {βT : GL (Fin T.rank) (Lev.EAf D)}
    (hS : IsFrame βS ΛS) (hT : IsFrame βT ΛT) (P : Finset (Pl D.host.E)) (n : ℕ) {u : WO S T}
    (hu : u ∈ hatMx ((∏ w ∈ P, w.asIdeal ^ n) • homLat ΛS ΛT)) : IsSmall P βT βS n u := by
  intro w hw i j
  obtain ⟨s, hs, h⟩ := ((Comparison₂.mem_hatMx_iff hS hT _ u).1 hu).2 i j
  have h3 := Comparison₂.v_le_of_mem_idS (Ideal.le_of_dvd (Finset.dvd_prod_of_mem (fun w : Pl D.host.E => w.asIdeal ^ n) hw)) hs
  rw [val_le_unif_iff]
  change Valued.v (cpt w (Comparison₂.fr βT βS (u.map (toEAf D)) i j)) ≤ _
  rwa [← h]

end Lat

end GlobalTheory.FunObj.CosSB

namespace GlobalTheory.FunObj.CosSB

open GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames _root_.Formalism.L2.Host _root_.Formalism.L2.DIV GlobalTheory.LatVac
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem prod_pow_ne_bot {D : D7} (P : Finset (Pl D.host.E)) (n : ℕ) : (∏ w ∈ P, w.asIdeal ^ n) ≠ ⊥ := by
  rw [← Ideal.zero_eq_bot, Finset.prod_ne_zero_iff]
  exact fun w _ => pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact w.ne_bot)


set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1000000 in
theorem isSBHalf_cosLoc : ∀ {D : D7} (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D))
    (βT : GL (Fin T.rank) (Lev.EAf D)) (P : Finset (Pl D.host.E)) (e : AE D) (n : ℕ) (r : WO S T),
    Submodule.IsFullLattice D.host.E ΛS → Submodule.IsFullLattice D.host.E ΛT → IsFrame βS ΛS → IsFrame βT ΛT →
    IsIdemSum e P → IsHalf e r → IsSBHalf e (latO S T ΛS ΛT fun _ => True) (cosLoc P e βT βS n r) := by
  intro D S T ΛS ΛT βS βT P e n r hS hT hFS hFT he _
  classical
  obtain ⟨a, ha, h1⟩ := WeilOver.exists_hom_le hS hT
  obtain ⟨b, hb, h2⟩ := WeilOver.exists_le_hom hS.toIsLattice hT.toIsLattice
  obtain ⟨e0, e1, e2⟩ := Comparison₂.cpt_idemSum he
  have hM : 0 < Ideal.absNorm (∏ w ∈ P, w.asIdeal ^ n) :=
    Nat.pos_of_ne_zero fun h => prod_pow_ne_bot P n (Ideal.absNorm_eq_zero_iff.1 h)

  set N : ℕ := Ideal.absNorm (∏ w ∈ P, w.asIdeal ^ 1) with hNdef
  have hN : 0 < N := Nat.pos_of_ne_zero fun h => prod_pow_ne_bot P 1 (Ideal.absNorm_eq_zero_iff.1 h)
  have hNmem : ∀ w ∈ P, (N : 𝓞 D.host.E) ∈ w.asIdeal := fun w hw => by
    have := Ideal.le_of_dvd (Finset.dvd_prod_of_mem (fun w : Pl D.host.E => w.asIdeal ^ 1) hw)
      (Ideal.absNorm_mem (∏ w ∈ P, w.asIdeal ^ 1))
    rw [pow_one] at this
    exact this

  have hc1 : ∀ p : Fin T.rank × Fin S.rank, ∃ k : ℕ, ∀ l, k ≤ l →
      ((N ^ l : ℕ) : Lev.EAf D) * (toEAf D e * Comparison₂.fr βT βS (r.map (toEAf D)) p.1 p.2) ∈ OA D :=
    fun p => exists_pow_mul_mem _ fun Q hQ => by
      have hQP : Q ∉ P := fun h => hQ (hNmem Q h)
      rw [map_mul, e2 Q hQP, zero_mul]
      exact zero_mem _
  choose kk hkk using hc1
  set c : ℕ := N ^ (Finset.univ.sup kk) with hcdef
  have hc0 : 0 < c := pow_pos hN _
  have hc : ∀ i j, (c : Lev.EAf D) * (toEAf D e * Comparison₂.fr βT βS (r.map (toEAf D)) i j) ∈ OA D :=
    fun i j => hkk (i, j) _ (Finset.le_sup (f := kk) (Finset.mem_univ (i, j)))
  refine ⟨fun t ht => ?_, (a * c) * (b * Ideal.absNorm (∏ w ∈ P, w.asIdeal ^ n)), by positivity,
    fun u hu hh t => ?_, fun t ht => ?_⟩
  · by_contra h
    exact ht (by unfold cosLoc; rw [if_neg fun H => h H.1])
  · have hk : IsSmall P βT βS n (((a * c) * (b * Ideal.absNorm (∏ w ∈ P, w.asIdeal ^ n))) • u) := by
      refine isSmall_of_mem_hatMx hFS hFT P n ?_
      rw [mul_nsmul']
      exact nsmul_mem (nsmul_mem_hatMx h2 _ hu) _
    unfold cosLoc
    refine if_congr (and_congr (isHalf_add_nsmul _ hh) ?_) rfl rfl
    rw [add_sub_right_comm]
    exact ⟨fun h => by simpa using isSmall_sub h hk, fun h => isSmall_add h hk⟩
  · obtain ⟨hth, hts⟩ : IsHalf e t ∧ IsSmall P βT βS n (t - r) := by
      by_contra h
      exact ht (by unfold cosLoc; rw [if_neg h])
    set X := Comparison₂.fr βT βS (t.map (toEAf D))
    set R := Comparison₂.fr βT βS (r.map (toEAf D))
    have hX : Comparison₂.fr βT βS ((c • t).map (toEAf D)) = (c : Lev.EAf D) • (toEAf D e • X) := by
      have : (c • t).map (toEAf D) = (c : Lev.EAf D) • (toEAf D e • t.map (toEAf D)) := by
        ext i j
        rw [Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.map_apply, nsmul_eq_mul,
          map_mul, map_natCast, smul_eq_mul, smul_eq_mul]
        conv_lhs => rw [← hth i j]
        rw [map_mul]
      rw [this, Comparison₂.fr_smul, Comparison₂.fr_smul]
    have hsm : ∀ i j, toEAf D e * (X - R) i j ∈ OA D := fun i j => by
      refine (mem_OA_iff _).2 fun Q => ?_
      rw [map_mul]
      by_cases hQ : Q ∈ P
      · rw [e1 Q hQ, one_mul]
        have h3 := (val_le_unif_iff Q n _).1 (hts Q hQ i j)
        rw [frAt_sub, Matrix.sub_apply] at h3
        rw [HeightOneSpectrum.mem_adicCompletionIntegers, Matrix.sub_apply, map_sub]
        refine h3.trans ?_
        rw [← WithZero.exp_zero, WithZero.exp_le_exp]
        omega
      · rw [e2 Q hQ, zero_mul]
        exact zero_mem _
    have hint : ∀ i j, Comparison₂.fr βT βS ((c • t).map (toEAf D)) i j ∈ OA D := fun i j => by
      have : Comparison₂.fr βT βS ((c • t).map (toEAf D)) i j =
          (c : Lev.EAf D) * (toEAf D e * (X - R) i j) + (c : Lev.EAf D) * (toEAf D e * R i j) := by
        rw [hX, Matrix.smul_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, smul_eq_mul, ← mul_add, ← mul_add,
          sub_add_cancel]
      rw [this]
      exact add_mem (mul_mem (natCast_mem _ _) (hsm i j)) (hc i j)
    have hmem : c • t ∈ hatMx ((⊤ : Ideal (𝓞 D.host.E)) • homLat ΛS ΛT) := by
      refine (Comparison₂.mem_hatMx_iff hFS hFT ⊤ _).2 ⟨fun i j => ?_, fun i j => ⟨⟨_, hint i j⟩, ?_, rfl⟩⟩
      · rw [Matrix.smul_apply, map_nsmul, ← hth i j, map_mul, e0, zero_mul, smul_zero]
      · rw [idS, Ideal.map_top]
        exact Submodule.mem_top
    have := nsmul_mem (nsmul_mem_latO h1 ⊤ hmem) (b * Ideal.absNorm (∏ w ∈ P, w.asIdeal ^ n))
    convert this using 1
    rw [mul_comm (a * c), ← smul_smul, ← smul_smul a c t]

end GlobalTheory.FunObj.CosSB

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorSmallCosetHalfIsSchwartzBruhatStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory ValuativeRel
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.indicator_smallCoset_half_isSchwartzBruhat : ∀ {D : D7} (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (P : Finset (Pl D.host.E)) (e : AE D) (n : ℕ) (r : WO S T), Submodule.IsFullLattice D.host.E ΛS → Submodule.IsFullLattice D.host.E ΛT → IsFrame βS ΛS → IsFrame βT ΛT → IsIdemSum e P → IsHalf e r → IsSBHalf e (latO S T ΛS ΛT fun _ => True) (cosLoc P e βT βS n r) := by
  first
  | exact @GlobalTheory.FunObj.CosSB.isSBHalf_cosLoc
  | intro D S T ΛS ΛT βS βT P e n r hS hT hFS hFT he hr
    exact GlobalTheory.FunObj.CosSB.isSBHalf_cosLoc S T ΛS ΛT βS βT P e n r
      hS.toIsLattice hT.toIsLattice hFS hFT he hr
end
end
