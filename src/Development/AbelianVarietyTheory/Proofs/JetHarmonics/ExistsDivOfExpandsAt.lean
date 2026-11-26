module

public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.CstDvdOfCstMulEqZero
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsPhiRelSmul
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.StalkMapInjectiveOfFlat
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrameNStHolds
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UniversalStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsDivOfExpandsAt
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IntegralExpansion

section General

variable {X Y Y' Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K'] {φ₁ : K → (Y' ⟶ X)}
  {ε₁ : K → ℤ} {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)} {φ₂ : K' → (Y ⟶ X)} {ε₂ : K' → ℤ}

theorem sval_of_secScal {s₂ : LB.Sec (LB.LinComb L φ₂ ε₂)} {h : Y' ⟶ Y} {c : Γ(Y', ⊤)}
    (H : GeneratorPullback.SecScal L φ₁ ε₁ s₁ φ₂ ε₂ s₂ h c) (r : Z ⟶ Y') (z : Z) {J} (hJ : Good L z J) :
    sval s₂ (r ≫ h) z J = gs r z ⊤ c * sval s₁ r z J := by
  rw [sval_of s₂ (r ≫ h) z J (fun k => J (r ≫ h ≫ φ₂ k)) (fun k => by rw [Category.assoc])]
  have hm : r z ∈ LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k)) ⊓
      LB.wchart L (fun k => h ≫ φ₂ k) (fun k => J (r ≫ h ≫ φ₂ k)) :=
    ⟨hJ.mem φ₁ r, hJ.mem (fun k => h ≫ φ₂ k) r⟩
  have e := congrArg (gs r z _) (H (fun k => J (r ≫ φ₁ k)) (fun k => J (r ≫ h ≫ φ₂ k)) (by
    rintro (a | a) (b | b) e <;> exact congrArg (fun q => J (r ≫ q)) e))
  exact ((gs_res r z _ hm _).trans (gs_pull r h z
    (LB.wchart L φ₂ (fun k => J (r ≫ h ≫ φ₂ k))) (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hm.2 k) _)).symm.trans
    (e.trans ((gs_mul r z _ hm _ _).trans (congrArg₂ (· * ·) (gs_res r z _ hm _) (gs_res r z _ hm _))))

theorem secIsMul_of_secScal (hL : L.IsLB) {R : Type} [CommRing R] (p : Y ⟶ Spec (CommRingCat.of R)) {a : R}
    {s s' : LB.Sec (LB.LinComb L φ₂ ε₂)} {h : Y' ⟶ Y} (hinj : ∀ W : Y.Opens, Function.Injective (h.app W))
    (H : GeneratorPullback.SecScal L φ₁ ε₁ s₁ φ₂ ε₂ s h 1) (H' : GeneratorPullback.SecScal L φ₁ ε₁ s₁ φ₂ ε₂ s' h (scal (h ≫ p) a)) :
    SecIsMul p a s' s := by
  intro j
  refine hinj _ (fn_ext fun y hy => ?_)
  choose J hJ using fun ψ : Y' ⟶ X => exists_chart hL (ψ y)
  have hJ' : Good L y J := hJ
  have hy' : (𝟙 Y' ≫ h) y ∈ LB.wchart L φ₂ j := hy
  have m := hJ'.mem φ₂ (𝟙 Y' ≫ h)
  have e₁ := sval_scal H (𝟙 Y') y hJ'
  have e₂ := sval_of_secScal H' (𝟙 Y') y hJ'
  have e₃ : gs (𝟙 Y' ≫ h) y (LB.wchart L φ₂ j) (Out.resTop _ (scal p a)) = gs (𝟙 Y') y ⊤ (scal (h ≫ p) a) :=
    ((gs_res _ y le_top hy' _).trans (gs_pull _ p y ⊤ trivial _)).trans
      (((gs_pull _ (h ≫ p) y ⊤ trivial _).trans (by rw [Category.assoc])).symm)
  refine (gs_pull (𝟙 Y') h y _ hy _).trans (Eq.trans ?_ (gs_pull (𝟙 Y') h y _ hy _).symm)
  refine (sec_trans s' _ y hy' m).trans (Eq.trans ?_ ((gs_mul _ y _ hy' _ _).trans
    (congrArg₂ (· * ·) e₃ (sec_trans s _ y hy' m))).symm)
  exact (congrArg _ (e₂.trans (congrArg _ e₁))).trans (mul_left_comm _ _ _)

end General

theorem exists_secIsMul {R : Type} [CommRing R] {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) {M : LB Y}
    (a : R) (s : LB.Sec M) : ∃ s' : LB.Sec M, SecIsMul p a s' s :=
  ⟨SectionArithmetic.secCMul (V := ⊤) (fun _ => le_top) (scal p a) s, fun _ => rfl⟩

theorem SecIsMul.comp {R : Type} [CommRing R] {Y : Scheme.{0}} {p : Y ⟶ Spec (CommRingCat.of R)} {M : LB Y}
    {a b : R} {s s' s'' : LB.Sec M} (h : SecIsMul p a s'' s') (h' : SecIsMul p b s' s) :
    SecIsMul p (a * b) s'' s := fun j => by
  rw [h j, h' j, ← _root_.mul_assoc]
  simp only [Out.resTop, scal, map_mul]

theorem prB_app_injective {V : Type} [CommRing V] [IsDomain V] (D : DegPre V) (W : D.P.A.left.Opens) :
    Function.Injective ((DegPre.prB D (FractionRing V)).left.app W) := by
  have := D.P.isAb.smooth
  have : Flat D.P.A.hom := inferInstance
  have e : (TF (R := V) (FractionRing V)).hom = jK V := by
    show Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]; rfl
  have h := GlobalTheory.ExtUnique.spec_fractionRing V (FractionRing V)
  have : IsSchemeTheoreticallyDominant (TF (R := V) (FractionRing V)).hom := by rw [e]; exact h.2
  have : QuasiCompact (TF (R := V) (FractionRing V)).hom := by rw [e]; exact h.1
  exact (pullback.snd (TF (R := V) (FractionRing V)).hom D.P.A.hom).app_injective W

theorem exists_div_of_expandsAt {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
    (hϖ : Irreducible ϖ) {D : DegData V (maximalIdeal V)} {A : PolAV (Spec (CommRingCat.of (FractionRing V)))}
    {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G] (U : UnifPre (maximalIdeal V) D A G)
    (e k : ℕ) (σ : H0 U.LG.L k) (f f' : ∀ α : D.toPre.X, D.toPre.SecB k α)
    (hf : ∀ α, SecIsMul D.toPre.P.A.hom (ϖ ^ (e + 1)) (f' α) (f α)) (hE : U.ExpandsAt e k σ f') :
    ∃ τ : H0 U.LG.L k, SecIsMul G.hom (ϖ ^ (e + 1)) σ τ := by
  have := U.smooth
  have : Flat G.hom := inferInstance
  refine (GlobalTheory.ThickDiv.main V ϖ hϖ G _ σ e).1 fun j => fn_ext fun y hy => ?_
  obtain ⟨jL, rfl⟩ : ∃ jL, j = fun _ => jL := ⟨j 0, funext fun i => congrArg j (Subsingleton.elim i 0)⟩
  obtain ⟨S, hS⟩ := expandsAt_val U e k σ f' hE
  choose J hJ using fun ψ : (thickObj V (maximalIdeal V) e G).left ⟶ D.toPre.P.A.left =>
    exists_chart D.toPre.P.isLB (ψ y)
  have hJ' : Good D.toPre.P.L y J := hJ
  have H := (hS _ (𝟙 _) y J hJ').2 jL (Set.mem_iInter.1 hy 0)
  have hc : pGl U e ≫ D.toPre.P.A.hom = (thickObj V (maximalIdeal V) e G).hom ≫
      spMap (Ideal.Quotient.mk (maximalIdeal V ^ (e + 1))) := Over.w (U.gt e).pG
  have h0 : cst (pGl U e ≫ D.toPre.P.A.hom) y (ϖ ^ (e + 1)) = 0 := by
    rw [hc, cst_comp, Ideal.Quotient.eq_zero_iff_mem.2
      (Ideal.pow_mem_pow ((mem_maximalIdeal _).2 hϖ.not_isUnit) _), cst, map_zero]
    exact gs_zero _ _ _ trivial
  have hF : ∀ α, sval (f' α) (𝟙 _ ≫ pGl U e) y J = 0 := fun α => by
    rw [Category.id_comp]
    exact (secIsMul_gs (hf α) (pGl U e) y _ (hJ'.mem _ _)).trans (by rw [h0, zero_mul])
  simp only [hF, zero_mul, Finset.sum_const_zero, Units.mul_right_eq_zero] at H
  exact (gs_pull (𝟙 _) _ y _ hy _).trans (H.trans (gs_zero (𝟙 _) y _ hy).symm)

theorem main : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal V) D A G) (q : ℕ), 1 ≤ q → ∀ (Φ : Fam D.toPre (FractionRing V) q) (f : ∀ α, D.toPre.SecB q α), (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε q) (Φ.s α) (D.toPre.famφB α) (DegPre.famε q) (f α) (DegPre.prB D.toPre (FractionRing V)).left 1) → ∃ σ : H0 U.LG.L q, ∀ e : ℕ, U.ExpandsAt e q σ f := by
  intro _ V _ _ _ D A G _ _ U q hq Φ f hf
  obtain ⟨s, ⟨r, hr, σ₁, f₁, -, hf₁, hE₁⟩, -⟩ := (U.expand q hq).2 Φ
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hr hϖ
  have h₁ : ∀ α, SecIsMul D.toPre.P.A.hom r (f₁ α) (f α) := fun α =>
    secIsMul_of_secScal D.toPre.P.isLB _ (prB_app_injective D.toPre) (hf α)
      (by rw [Over.w (DegPre.prB D.toPre (FractionRing V))]; exact hf₁ α)
  obtain ⟨σ₂, hσ₂⟩ := exists_secIsMul G.hom (u : V) σ₁
  choose f₂ hf₂ using fun α => exists_secIsMul D.toPre.P.A.hom (u : V) (f₁ α)
  have hE₂ : ∀ e, U.ExpandsAt e q σ₂ f₂ := fun e =>
    expandsAt_secIsMul V _ D A G U.toUnifPre e q u σ₁ σ₂ f₁ f₂ hσ₂ hf₂ (hE₁ e)
  have h₂ : ∀ α, SecIsMul D.toPre.P.A.hom (ϖ ^ n) (f₂ α) (f α) := fun α => by
    rw [← hu, mul_comm]; exact SecIsMul.comp (hf₂ α) (h₁ α)
  obtain ⟨σ, hσ⟩ : ∃ σ : H0 U.LG.L q, SecIsMul G.hom (ϖ ^ n) σ₂ σ := by
    cases n with
    | zero => exact ⟨σ₂, fun j => by rw [pow_zero, scal, map_one, map_one, Out.resTop, map_one, _root_.one_mul]⟩
    | succ m => exact exists_div_of_expandsAt hϖ U.toUnifPre m q σ₂ f f₂ h₂ (hE₂ m)
  exact ⟨σ, fun e => expandsAt_cancel_pow V ϖ hϖ D A G U.toUnifPre e n q σ σ₂ f f₂ hσ h₂ (hE₂ (e + n))⟩

end GlobalTheory.IntegralExpansion
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.PowOActOfGlobalFns
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem powOAct_of_globalFns : GlobalFnsSt → PowOActSt := by
  intro hG E _ _ _ H V _ _ _ t P n D' pD
  letI := H.starRing
  letI M : Module (𝓞 E) D'.toPre.X := pD.xe.module (𝓞 E)
  have h : ∀ (a : 𝓞 E) (x : D'.toPre.X), pD.xe (a • x) = a • pD.xe x := by
    intro a x
    exact pD.xe.apply_symm_apply _
  obtain ⟨oa', hoa'⟩ := powDeg_diagonal_action hG V n P.D.toPre D'.toPre pD (𝓞 E) h P.oD
  exact ⟨M, oa', fun a x i => by rw [h]; rfl, hoa'⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsThetaFrame
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem exists_thetaFrame : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ), QForm.IsQ D.toPre ϖ Q → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∃ θ : Fam D.toPre F 1, NuGe D Q F v 1 θ 0 ∧ ∃ (σ : D.toPre.SecB 1 0) (σF : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F 0) (DegPre.famε 1))), GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F 0) (DegPre.famε 1) σF (D.toPre.famφB 0) (DegPre.famε 1) σ (DegPre.prB D.toPre F).left 1 ∧ (∀ j, (θ.s 0).f j = σF.f j) ∧ ¬ ∃ σ' : D.toPre.SecB 1 0, ∀ j, σ.f j = constFn D.toPre.P.A.hom _ ϖ * σ'.f j := by
  intro hL _ _ _ V _ _ _ ϖ hϖ D Q hQ F _ _ v hv
  obtain ⟨b, hb⟩ := IndivisibleSection.exists_secBGenerates hL.secBaseChange V (maximalIdeal V) D
  obtain ⟨Φ, f, hf, hf0, -, -⟩ := integralFamily_of_strictMin hL V ϖ hϖ D Q hQ 1 le_rfl 0 b (fun z hz => by
    have h := QForm.Q_pos hϖ (D := D) hQ hz
    rw [QForm.Q_zero hϖ (D := D) hQ, zero_add, one_smul]
    omega)
  obtain ⟨θ, hθ⟩ := FamBaseChange.main hL.globalFns V (maximalIdeal V) D 1 Φ f hf F
  refine ⟨θ, (integralFamily_levelOne V ϖ hϖ D Q hQ F v hv θ f hθ).1, b, θ.s 0, hf0 ▸ hθ 0, fun _ => rfl, ?_⟩
  rintro ⟨σ', hσ'⟩
  have h1 : SecIsMul D.toPre.P.A.hom ϖ b σ' := hσ'
  obtain ⟨a, ha, -⟩ := hb σ'
  have h2 : SecIsMul D.toPre.P.A.hom (ϖ * a) b b := fun j => by
    refine (h1 j).trans ?_
    rw [ha j]
    simp only [scal, resTop, map_mul, _root_.mul_assoc]
  have h3 : SecIsMul D.toPre.P.A.hom 1 b b := fun j => by
    simp only [scal, resTop, map_one, _root_.one_mul]
  exact hϖ.not_isUnit (IsUnit.of_mul_eq_one a ((hb b).unique h2 h3))

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsGermLinearMap
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.PairingLinear

def linOfComb {F M N : Type} [Field F] [AddCommGroup M] [Module F M] [AddCommGroup N] [Module F N] (f : M → N)
    (h : ∀ (l : ℕ) (c : Fin l → F) (s : Fin l → M), f (∑ i, c i • s i) = ∑ i, c i • f (s i)) : M →ₗ[F] N where
  toFun := f
  map_add' a b := by simpa using h 2 ![1, 1] ![a, b]
  map_smul' c a := by simpa using h 1 ![c] ![a]

theorem exists_germ_linearMap (hL : Laws) (hL2 : Laws2) (hL4 : Laws4) (hT : TwistBaseChangeStatement)
    (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V]
    (D : DegData V (maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Sp V))
    [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal V) D A G) (κ : Type) [Fintype κ] [DecidableEq κ]
    (z : JetPts G κ) (hz : IsUnivJ G κ z) (τ : Frames U.LG.L z) (hτ : τ.Gen) (hτT : τ.Trunc)
    (F : Type) [Field F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F]
    (q : ℕ) (hq : 1 ≤ q) :
    ∃ gm : Fam D.toPre F q →ₗ[F] MvPowerSeries κ F,
      (∀ t σ' h, U.ExpandsG F q σ' t → GermA U.toUnifPre z τ F q σ' h → h = gm t) ∧
      ∀ t, ∃ σ', U.ExpandsG F q σ' t ∧ GermA U.toUnifPre z τ F q σ' (gm t) := by
  obtain ⟨huniq, hlin, hex⟩ := GlobalTheory.GermBasic.main V D A G U κ z hz τ hτ F q
  have hbij := (GlobalTheory.expandsG_bijective_of_dvr hL hL2 hL4 hT V D A G U F q hq).2
  choose S hS hSu using hbij
  choose Γg hΓ using hex hτT
  have key : ∀ t σ' h, U.ExpandsG F q σ' t → GermA U.toUnifPre z τ F q σ' h → h = Γg (S t) := by
    intro t σ' h he hg
    obtain rfl := hSu t σ' he
    exact huniq _ _ _ hg (hΓ _)
  refine ⟨linOfComb (fun t => Γg (S t)) fun l c s => ?_, key, fun t => ⟨S t, hS t, hΓ _⟩⟩
  let σ' : U.SecGF F q := GlobalTheory.ExpansionLinear.secComb
    (fun i => scal (fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G)).left (c i)) (fun i => S (s i))
  exact (key _ σ' _
    (GlobalTheory.GroupExpansionLinear.expandsG_sum V D A G U F q l c (fun i => S (s i)) s σ' (fun i => hS _) (fun _ => rfl))
    (hlin l c (fun i => S (s i)) _ σ' (fun i => hΓ _) (fun _ => rfl))).symm

end GlobalTheory.PairingLinear
end
end
