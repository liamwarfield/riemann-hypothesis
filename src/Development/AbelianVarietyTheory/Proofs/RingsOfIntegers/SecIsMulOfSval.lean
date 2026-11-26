module

public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsDivOfExpandsAt
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionOfIntegralSectionIsIntegral

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SecIsMulOfSval
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.LevelOneIdeal

theorem exists_psi_val {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {I : Ideal R} (D : DegPre R) (χ : D.X)
    (h : D.PsiIn χ I) :
    ∃ (e : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))), e.IsGen ∧ ∃ a ∈ I,
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (TK R).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J →
        (val (D.psi χ) r z J).val = cst (r ≫ jK R) z a * (val e (r ≫ jK R) z J).val := by
  have hL := D.P.isLB
  obtain ⟨e, he⟩ := exists_gen_of_local (V := R) D.P.L hL (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1)
  obtain ⟨j, hj⟩ := exists_chart_top (V := R) D.P.L hL (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1)
  have le : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ LB.wchart D.P.L (K := PUnit) (fun _ => (D.c χ).left) j := hj.ge
  have hx : D.xK χ = jK R ≫ (D.c χ).left := by
    simp [DegPre.xK, ptK]
  have le' : jK R ⁻¹ᵁ ⊤ ≤ LB.wchart D.P.L (K := PUnit) (fun _ => D.xK χ) j := fun y _ =>
    Set.mem_iInter.2 fun k => by
      rw [hx]; exact Set.mem_iInter.1 (le (show (jK R) y ∈ (⊤ : (Spec (CommRingCat.of R)).Opens) from trivial)) k
  obtain ⟨r₀, hr₀, hψ⟩ := h j ⊤ (isAffineOpen_top _) (le.trans (LB.wchart_le _ _ _ PUnit.unit)) le'
  have hto : ∀ a, DegPre.toOpen (R := R) ⊤ a = (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a := fun a => by
    simp [DegPre.toOpen]
  have hs : Function.Surjective (DegPre.toOpen (R := R) ⊤) := fun x => by
    obtain ⟨a, ha⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).2 x
    exact ⟨a, (hto a).trans ha⟩
  obtain ⟨a₀, ha₀, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ hs).1 hr₀
  obtain ⟨b, hb⟩ := hs (res le (e.s j))⁻¹.val
  refine ⟨e, he, a₀ * b, I.mul_mem_right _ ha₀, fun Z r z J hJ => ?_⟩
  have m₁ : r z ∈ LB.wchart D.P.L (K := PUnit) (fun _ => D.xK χ) j := le' trivial
  have m₂ : (r ≫ jK R) z ∈ LB.wchart D.P.L (K := PUnit) (fun _ => (D.c χ).left) j := le trivial
  have e₁ : val (D.psi χ) r z J = _ := gen_trans (D.psi_gen χ) r z (hJ.mem _ r) m₁
  have e₂ : val e (r ≫ jK R) z J = _ := gen_trans he (r ≫ jK R) z (hJ.mem _ _) m₂
  have e₃ : trF (L := D.P.L) (K := PUnit) (fun _ => D.xK χ) (fun _ => -1) r z (fun _ => J (r ≫ D.xK χ)) j =
      trF (L := D.P.L) (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1) (r ≫ jK R) z
        (fun _ => J ((r ≫ jK R) ≫ (D.c χ).left)) j := by
    have hq : r ≫ D.xK χ = (r ≫ jK R) ≫ (D.c χ).left :=
      (congrArg (r ≫ ·) hx).trans (Category.assoc _ _ _).symm
    simp only [trF]
    rw [hq]
  have e₄ : (gm r z (LB.wchart D.P.L (K := PUnit) (fun _ => D.xK χ) j) ((D.psi χ).s j)).val = cst (r ≫ jK R) z a₀ := by
    refine (gs_unit r z _ m₁ _).symm.trans ((gs_res r z le' trivial _).symm.trans ?_)
    refine (congrArg (gs r z _) hψ.symm).trans ((gs_pull r (jK R) z ⊤ trivial _).trans ?_)
    rw [hto]; rfl
  have e₅ : cst (r ≫ jK R) z b *
      (gm (r ≫ jK R) z (LB.wchart D.P.L (K := PUnit) (fun _ => (D.c χ).left) j) (e.s j)).val = 1 := by
    rw [cst, ← hto, hb, gs_unit _ z ⊤ trivial, map_inv]
    exact (congrArg₂ (fun q c => q⁻¹.val * c) (gm_res (r ≫ jK R) z le trivial (e.s j)) rfl).trans (Units.inv_mul _)
  have e₆ : cst (r ≫ jK R) z (a₀ * b) = cst (r ≫ jK R) z a₀ * cst (r ≫ jK R) z b := by
    rw [cst, map_mul, gs_mul _ z ⊤ trivial]; rfl
  rw [e₁, e₂, e₆, Units.val_mul, Units.val_mul]
  erw [e₃, e₄]
  linear_combination (-(cst (r ≫ jK R) z a₀ * (trF (L := D.P.L) (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1) (r ≫ jK R) z
        (fun _ => J ((r ≫ jK R) ≫ (D.c χ).left)) j).val)) * e₅

theorem val_famMult_one {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} (hB : D.TauBimult) {F : Type} [Field F]
    [Algebra (FractionRing R) F] {T : Over (Spec (CommRingCat.of R))} (σ : T ⟶ TF (R := R) F) {z : T.left}
    {J : (T.left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J) (χ : D.X) :
    val (DegPre.famMult D F 1 χ 0) σ.left z J =
      val (D.psi χ) (σ.left ≫ jFK (R := R) F) z J * val D.rigK (σ.left ≫ jFK (R := R) F) z J := by
  have C : IsCub (th D z J) := isCub_cubV D.cub hJ
  have t0 := tau_mul σ hJ hB 0 0 χ
  rw [add_zero, cPoint_zero, C.face, _root_.mul_one] at t0
  have τ0 : val (D.tau 0 χ) (σ.left ≫ jFK (R := R) F) z J = 1 := mul_eq_left.1 t0.symm
  rw [val_famMult σ hJ, UUA.val_powGen', UUA.val_powGen', tau_symm σ hJ, τ0, _root_.one_mul, pow_one, pow_one]

theorem secIsMul_of_sval {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} {R : Type} [CommRing R] (p : Y ⟶ Spec (CommRingCat.of R)) {a : R}
    {s s' : LB.Sec (LB.LinComb L φ ε)} {h : Y' ⟶ Y} (hinj : ∀ W : Y.Opens, Function.Injective (h.app W))
    (H : ∀ y J, Good L y J → sval s' h y J = cst (h ≫ p) y a * sval s h y J) : SecIsMul p a s' s := by
  intro j
  refine hinj _ (fn_ext fun y hy => ?_)
  choose J hJ using fun ψ : Y' ⟶ X => exists_chart hL (ψ y)
  have hJ' : Good L y J := hJ
  have hy' : h y ∈ LB.wchart L φ j := hy
  have m := hJ'.mem φ h
  have e₃ : gs h y (LB.wchart L φ j) (Out.resTop _ (scal p a)) = cst (h ≫ p) y a :=
    (gs_res _ y le_top hy' _).trans (gs_pull _ p y ⊤ trivial _)
  refine (gs_pull (𝟙 Y') h y _ hy _).trans (Eq.trans ?_ (gs_pull (𝟙 Y') h y _ hy _).symm)
  rw [Category.id_comp]
  refine (sec_trans s' _ y hy' m).trans (Eq.trans ?_ ((gs_mul _ y _ hy' _ _).trans
    (congrArg₂ (· * ·) e₃ (sec_trans s _ y hy' m))).symm)
  exact (congrArg _ (H y J hJ')).trans (mul_left_comm _ _ _)

theorem main : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R) (D : DegData R I) (E : Fam D.toPre (FractionRing R) 1) (g : ∀ α : D.toPre.X, D.toPre.SecB 1 α), (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε 1) (E.s α) (D.toPre.famφB α) (DegPre.famε 1) (g α) (DegPre.prB D.toPre (FractionRing R)).left 1) → ∀ χ, χ ≠ 0 → ∃ a ∈ I, ∃ g' : D.toPre.SecB 1 χ, SecIsMul D.toPre.P.A.hom a (g χ) g' := by
  intro hG R _ _ _ I D E g hg χ hχ
  have hL := D.toPre.P.isLB
  obtain ⟨e, he, a, ha, hψ⟩ := exists_psi_val D.toPre χ (D.psi_pos χ hχ)
  refine ⟨a, ha, ?_⟩
  suffices H : ∃ g' : D.toPre.SecB 1 (0 + 1 • χ), SecIsMul D.toPre.P.A.hom a (g (0 + 1 • χ)) g' by
    rwa [zero_add, one_smul] at H
  have c₁ : D.toPre.P.A.hom ≫ (D.toPre.c χ).left = (SectionScalarValuation.cQ D.toPre D.toPre.P.A χ).left := by simp [SectionScalarValuation.cQ]
  have c₂ : D.toPre.P.A.hom ≫ eSec D.toPre.P.A = (1 : D.toPre.P.A ⟶ D.toPre.P.A).left := by
    rw [Hom.one_def]; simp [eSec]
  have c₃ : SectionScalarValuation.cQ D.toPre D.toPre.P.A 0 = 1 := cPoint_zero (D := D.toPre) _
  obtain ⟨eB, heB, veB⟩ := SectionScalarValuation.exists_eB D.toPre 1 0 χ (LB.mulGen D.toPre.P.L _ _ _ _ e D.toPre.rig)
    (mulGen_isGen _ _ _ _ _ _ _ he D.toPre.rig_gen) (fun U _ h => by
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, c₁, c₂, c₃, _root_.one_mul]
      simp)
  have hformB : FormEq (Sum.elim (fun i => (𝟙 D.toPre.P.A * SectionScalarValuation.cQ D.toPre D.toPre.P.A χ).left ≫ D.toPre.famφB 0 i)
      (Sum.elim (D.toPre.famφB (0 + 1 • χ))
        (fun i => (𝟙 D.toPre.P.A * SectionScalarValuation.cQ D.toPre D.toPre.P.A χ).left ≫ D.toPre.famφB 0 i)))
      (Sum.elim (DegPre.famε 1) (DegPre.deltaε 1)) (D.toPre.famφB (0 + 1 • χ)) (DegPre.famε 1) := fun U _ h => by
    rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, DegPre.deltaε, zpow_neg, Finset.prod_inv_distrib]
    rw [mul_left_comm, mul_inv_cancel, _root_.mul_one]
  obtain ⟨g', hg'⟩ := exists_sec hL hformB
    (pullMulSec (g 0) (𝟙 D.toPre.P.A * SectionScalarValuation.cQ D.toPre D.toPre.P.A χ).left eB heB)
  refine ⟨g', secIsMul_of_sval hL _ (IntegralExpansion.prB_app_injective D.toPre) fun y J hJ => ?_⟩
  obtain ⟨⟨u, hu, hc⟩, hv⟩ := gen_fe (D := D.toPre) (F := FractionRing R) hG 1 χ 0
  have vu := hv u hu hc _ (𝟙 _) y J hJ
  have hrel := (secRel_iff hL _ _ _ _ _ _ _ _ _ u).1 (E.fe χ 0 u hu hc) _ (𝟙 _) y J hJ
  have htr : (DegPre.trF D.toPre (FractionRing R) χ).left ≫ (DegPre.prB D.toPre (FractionRing R)).left =
      (DegPre.prB D.toPre (FractionRing R)).left ≫ (𝟙 D.toPre.P.A * SectionScalarValuation.cQ D.toPre D.toPre.P.A χ).left := by
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    rw [DegPre.trF, DegPre.prB, lift_snd, MonObj.comp_mul, Category.comp_id, SectionScalarValuation.comp_cQ]
    rfl
  rw [H1.sval_scal (hg _) _ y hJ, H1.sval_scal (hg _) _ y hJ, Category.id_comp, Category.id_comp, htr] at hrel
  rw [hrel, hg' _ _ y J hJ, sval_pullMulSec _ _ _ heB _ y hJ, mul_left_comm]
  congr 1
  have w₁ : (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left ≫ jFK (R := R) (FractionRing R) ≫ jK R =
      (DegPre.prB D.toPre (FractionRing R)).left ≫ D.toPre.P.A.hom :=
    (Over.w (fst (TF (R := R) (FractionRing R)) D.toPre.P.A)).trans (Over.w (DegPre.prB D.toPre (FractionRing R))).symm
  have v₁ := veB _ (DegPre.prB D.toPre (FractionRing R)) y J hJ
  have v₂ := hψ _ ((fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left ≫ jFK (R := R) (FractionRing R)) y J hJ
  have v₃ : val D.toPre.rigK ((fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left ≫ jFK (R := R) (FractionRing R)) y J =
      val D.toPre.rig ((DegPre.prB D.toPre (FractionRing R)).left ≫ D.toPre.P.A.hom) y J := by
    rw [← w₁, ← Category.assoc]
    exact val_pull hJ _ _ _
  rw [Category.assoc, w₁] at v₂
  rw [Over.id_left, Category.id_comp, val_famMult_one D.tau_bimult _ hJ, v₃, uVal, Category.id_comp, Category.id_comp,
    comp_cP] at vu
  rw [val_mul hJ] at v₁
  rw [vu, v₁]
  simp only [Units.val_mul]
  rw [v₂]
  simp only [SectionScalarValuation.cQ, cP, th]
  ring

end GlobalTheory.LevelOneIdeal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MixedCrossIdentityGenericFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SecEqOfThick
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.MixedCross

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem cross_pow {Γ : Type} [CommRing Γ] (W W' X : Γˣ) {k₁ k₂ m₁ m₂ N : ℕ} (hm : m₁ * k₁ = m₂ * k₂)
    (s₁ t₁ s₂ t₂ : Γ)
    (h₁ : (W ^ (k₁ * N)).val * s₁ = (X ^ k₁).val * ((W' ^ k₁).val * t₁))
    (h₂ : (W ^ (k₂ * N)).val * s₂ = (X ^ k₂).val * ((W' ^ k₂).val * t₂)) :
    s₁ ^ m₁ * t₂ ^ m₂ = s₂ ^ m₂ * t₁ ^ m₁ := by
  push_cast at h₁ h₂
  have e₁ := congrArg (· ^ m₁) h₁
  have e₂ := congrArg (· ^ m₂) h₂
  simp only [mul_pow, ← pow_mul] at e₁ e₂
  have a₁ : k₁ * N * m₁ = m₁ * k₁ * N := by ring
  have a₂ : k₂ * N * m₂ = m₁ * k₁ * N := by rw [hm]; ring
  have b₁ : k₁ * m₁ = m₁ * k₁ := by ring
  have b₂ : k₂ * m₂ = m₁ * k₁ := by rw [hm]; ring
  rw [a₁, b₁] at e₁
  rw [a₂, b₂] at e₂
  have hu : IsUnit ((W : Γ) ^ (m₁ * k₁ * N)) := W.isUnit.pow _
  apply hu.mul_left_cancel
  calc (W : Γ) ^ (m₁ * k₁ * N) * (s₁ ^ m₁ * t₂ ^ m₂)
      = ((W : Γ) ^ (m₁ * k₁ * N) * s₁ ^ m₁) * t₂ ^ m₂ := by ring
    _ = (X : Γ) ^ (m₁ * k₁) * ((W' : Γ) ^ (m₁ * k₁) * t₁ ^ m₁) * t₂ ^ m₂ := by rw [e₁]
    _ = ((W : Γ) ^ (m₁ * k₁ * N) * s₂ ^ m₂) * t₁ ^ m₁ := by rw [e₂]; ring
    _ = (W : Γ) ^ (m₁ * k₁ * N) * (s₂ ^ m₂ * t₁ ^ m₁) := by ring

theorem gs_sub' {X Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (a b : Γ(X, U)) :
    gs r z U (a - b) = gs r z U a - gs r z U b := by
  simp only [gs, dif_pos h, map_sub]

theorem sec_eq_of_thick (hB : lemmaBSt.{0}) {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G]
    [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom] [GeometricallyConnected G.hom]
    {Y : Scheme.{0}} {L : LB Y} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (G.left ⟶ Y)} {ε : K → ℤ}
    (s s' : LB.Sec (LB.LinComb L φ ε))
    (h : ∀ (e : ℕ) (z : (thickObj V (maximalIdeal V) e G).left) (J), Good L z J →
      sval s (fGl (maximalIdeal V) G e) z J = sval s' (fGl (maximalIdeal V) G e) z J) (j : K → L.ι) :
    s.f j = s'.f j := by
  classical
  unfold sval fGl at h
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hN : (LB.LinComb L φ ε).IsLB := linComb_isLB L hL φ ε
  refine sub_eq_zero.mp (hB V G (LB.LinComb L φ ε) hN (subSec s s') ϖ hϖ (fun i e => ?_) j)
  cases e with
  | zero => simp
  | succ e =>
    have hv : ∀ i', ((fstG (maximalIdeal V) e G).left.app ((LB.LinComb L φ ε).U i')).hom
        ((subSec s s').f i') = 0 := by
      intro i'
      apply fn_ext
      intro z hz
      have hz' : (fstG (maximalIdeal V) e G).left z ∈ LB.wchart L φ i' := hz
      obtain ⟨J, hJ, -⟩ := exists_good L hL z (K := Empty) Empty.elim Empty.elim (fun a => a.elim) (fun a => a.elim)
      have hm := hJ.mem φ (fstG (maximalIdeal V) e G).left
      have h1 := h e z J hJ
      rw [gs_eq (𝟙 _) z _ hz 0, map_zero, map_zero, gs_pull (𝟙 _) _ z ((LB.LinComb L φ ε).U i') hz', Category.id_comp]
      show gs (fstG (maximalIdeal V) e G).left z (LB.wchart L φ i') (s.f i' - s'.f i') = 0
      refine (gs_sub' _ z (LB.wchart L φ i') hz' (s.f i') (s'.f i')).trans (sub_eq_zero.mpr ?_)
      rw [sec_trans s _ z hz' hm, sec_trans s' _ z hz' hm, h1]
    obtain ⟨τ, hτ⟩ := (GlobalTheory.ThickDiv.main V ϖ hϖ G (LB.LinComb L φ ε) (subSec s s') e).1 hv
    unfold SecIsMul at hτ
    rw [hτ i]
    refine Ideal.mul_mem_right _ _ ?_
    have hc : resTop ((LB.LinComb L φ ε).U i) (scal G.hom (ϖ ^ (e + 1))) =
        ((G.left.presheaf.map (homOfLE le_top).op).hom
          ((G.hom.app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom ϖ))) ^ (e + 1) := by
      simp only [resTop, scal, map_pow]
      rfl
    rw [hc]
    exact Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) _

theorem main : lemmaBSt.{0} → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Geo.Tor.Host E) (t : Geo.Tor.SAB H (Spec (CommRingCat.of V))) (P : Geo.Tor.PELUnif (maximalIdeal V) t) (a : NumberField.RingOfIntegers E) (N : ℕ), (letI := H.starRing; a * star a = (N : NumberField.RingOfIntegers E)) → 0 < N → letI := H.starRing;  ∀ (X : LB.Gen (LB.LinComb P.D.toPre.P.L (K := Fin 2) ![𝟙 P.D.toPre.P.A.left, (P.oD.onB.act a).left] ![((1 * N : ℕ) : ℤ), -((1 : ℕ) : ℤ)])) (k₁ k₂ m₁ m₂ : ℕ), m₁ * k₁ = m₂ * k₂ → ∀ (σ₁ : H0 P.U.LG.L (k₁ * N)) (τ₁ : H0 P.U.LG.L k₁) (σ₂ : H0 P.U.LG.L (k₂ * N)) (τ₂ : H0 P.U.LG.L k₂), (∀ e : ℕ, (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj V (maximalIdeal V) e t.G).left) (z : Z) (J), Geo.Tor.Good P.D.toPre.P.L z J → ∀ jL jL', (r ≫ fGl (maximalIdeal V) t.G e) z ∈ P.U.LG.L.U jL → ((r ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) ≫ fGl (maximalIdeal V) t.G e) z ∈ P.U.LG.L.U jL' → (wv P.U.toUnifPre e r z (J (r ≫ pGl P.U.toUnifPre e)) jL ^ (k₁ * N)).val * sv P.U.toUnifPre (k₁ * N) σ₁ (r ≫ fGl (maximalIdeal V) t.G e) z jL = (Geo.Tor.val X (r ≫ pGl P.U.toUnifPre e) z J ^ k₁).val * ((wv P.U.toUnifPre e (r ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) z (J ((r ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) ≫ pGl P.U.toUnifPre e)) jL' ^ k₁).val * sv P.U.toUnifPre k₁ τ₁ ((r ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) ≫ fGl (maximalIdeal V) t.G e) z jL'))) → (∀ e : ℕ, (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj V (maximalIdeal V) e t.G).left) (z : Z) (J), Geo.Tor.Good P.D.toPre.P.L z J → ∀ jL jL', (r ≫ fGl (maximalIdeal V) t.G e) z ∈ P.U.LG.L.U jL → ((r ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) ≫ fGl (maximalIdeal V) t.G e) z ∈ P.U.LG.L.U jL' → (wv P.U.toUnifPre e r z (J (r ≫ pGl P.U.toUnifPre e)) jL ^ (k₂ * N)).val * sv P.U.toUnifPre (k₂ * N) σ₂ (r ≫ fGl (maximalIdeal V) t.G e) z jL = (Geo.Tor.val X (r ≫ pGl P.U.toUnifPre e) z J ^ k₂).val * ((wv P.U.toUnifPre e (r ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) z (J ((r ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) ≫ pGl P.U.toUnifPre e)) jL' ^ k₂).val * sv P.U.toUnifPre k₂ τ₂ ((r ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) ≫ fGl (maximalIdeal V) t.G e) z jL'))) → ∀ (Z : Scheme.{0}) (r : Z ⟶ t.G.left) (y : Z) (J), Geo.Tor.Good P.U.LG.L y J → Geo.Tor.sval σ₁ r y J ^ m₁ * Geo.Tor.sval τ₂ (r ≫ (t.act.act a).left) y J ^ m₂ = Geo.Tor.sval σ₂ r y J ^ m₂ * Geo.Tor.sval τ₁ (r ≫ (t.act.act a).left) y J ^ m₁ := by
  intro hB V _ _ _ E _ _ _ H t P a N haN hN X k₁ k₂ m₁ m₂ hm σ₁ τ₁ σ₂ τ₂ h₁ h₂
  classical
  have : Smooth t.G.hom := t.semi.smooth
  have : IsSeparated t.G.hom := t.semi.separated
  have : QuasiCompact t.G.hom := t.semi.quasiCompact
  have : GeometricallyConnected t.G.hom := t.semi.geomConnected
  have hL : P.U.LG.L.IsLB := P.U.LG.isLB
  have hD : P.D.toPre.P.L.IsLB := P.D.toPre.P.isLB
  have eA : ∀ (Z : Scheme.{0}) (r : Z ⟶ t.G.left) (y : Z) (J : (Z ⟶ t.G.left) → P.U.LG.L.ι), Good P.U.LG.L y J →
      sval (H1.SectionArithmetic.mulSec (H1.SectionArithmetic.powSec (fun _ : Fin m₁ => σ₁)) (H1.SectionArithmetic.pullSec (H1.SectionArithmetic.powSec (fun _ : Fin m₂ => τ₂)) (t.act.act a).left)) r y J = sval σ₁ r y J ^ m₁ * sval τ₂ (r ≫ (t.act.act a).left) y J ^ m₂ := by
    intro Z r y J hJ
    rw [H1.SectionArithmetic.sval_mulSec _ _ r y hJ, H1.SectionArithmetic.sval_pullSec _ _ r y hJ, H1.SectionArithmetic.sval_powSec _ r y hJ,
      H1.SectionArithmetic.sval_powSec _ _ y hJ]
    simp [Finset.prod_const]
  have eB : ∀ (Z : Scheme.{0}) (r : Z ⟶ t.G.left) (y : Z) (J : (Z ⟶ t.G.left) → P.U.LG.L.ι), Good P.U.LG.L y J →
      sval (H1.SectionArithmetic.mulSec (H1.SectionArithmetic.powSec (fun _ : Fin m₂ => σ₂)) (H1.SectionArithmetic.pullSec (H1.SectionArithmetic.powSec (fun _ : Fin m₁ => τ₁)) (t.act.act a).left)) r y J = sval σ₂ r y J ^ m₂ * sval τ₁ (r ≫ (t.act.act a).left) y J ^ m₁ := by
    intro Z r y J hJ
    rw [H1.SectionArithmetic.sval_mulSec _ _ r y hJ, H1.SectionArithmetic.sval_pullSec _ _ r y hJ, H1.SectionArithmetic.sval_powSec _ r y hJ,
      H1.SectionArithmetic.sval_powSec _ _ y hJ]
    simp [Finset.prod_const]
  obtain ⟨B', hB'⟩ : ∃ B' : type_of% (H1.SectionArithmetic.mulSec (H1.SectionArithmetic.powSec (fun _ : Fin m₁ => σ₁)) (H1.SectionArithmetic.pullSec (H1.SectionArithmetic.powSec (fun _ : Fin m₂ => τ₂)) (t.act.act a).left)),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ t.G.left) (z : Z) (J : (Z ⟶ t.G.left) → P.U.LG.L.ι), Good P.U.LG.L z J →
        sval B' r z J = sval (H1.SectionArithmetic.mulSec (H1.SectionArithmetic.powSec (fun _ : Fin m₂ => σ₂)) (H1.SectionArithmetic.pullSec (H1.SectionArithmetic.powSec (fun _ : Fin m₁ => τ₁)) (t.act.act a).left)) r z J := by
    refine exists_sec hL ?_ _
    intro U _ h
    simp only [Fintype.prod_sum_type, Finset.prod_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      Sum.elim_inl, Sum.elim_inr, Category.comp_id]
    have hz : (m₁ : ℤ) * k₁ = m₂ * k₂ := by exact_mod_cast hm
    simp only [← zpow_natCast, ← zpow_mul]
    congr 2
    · push_cast
      linear_combination (-(N : ℤ)) * hz
    · push_cast
      linear_combination hz
  have hthick : ∀ (e : ℕ) (z : (thickObj V (maximalIdeal V) e t.G).left)
      (J : ((thickObj V (maximalIdeal V) e t.G).left ⟶ t.G.left) → P.U.LG.L.ι), Good P.U.LG.L z J →
      sval (H1.SectionArithmetic.mulSec (H1.SectionArithmetic.powSec (fun _ : Fin m₁ => σ₁)) (H1.SectionArithmetic.pullSec (H1.SectionArithmetic.powSec (fun _ : Fin m₂ => τ₂)) (t.act.act a).left)) (fGl (maximalIdeal V) t.G e) z J = sval B' (fGl (maximalIdeal V) t.G e) z J := by
    intro e z J hJ
    rw [hB' _ _ z J hJ, eA _ _ z J hJ, eB _ _ z J hJ]
    obtain ⟨JD, hJD, -⟩ := exists_good P.D.toPre.P.L hD z (K := Empty) Empty.elim Empty.elim
      (fun a => a.elim) (fun a => a.elim)
    have m1 : (𝟙 _ ≫ fGl (maximalIdeal V) t.G e) z ∈ P.U.LG.L.U (J (fGl (maximalIdeal V) t.G e ≫ 𝟙 t.G.left)) := by
      simpa using hJ (fGl (maximalIdeal V) t.G e ≫ 𝟙 t.G.left)
    have m2 : ((𝟙 _ ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) ≫
        fGl (maximalIdeal V) t.G e) z ∈
          P.U.LG.L.U (J ((fGl (maximalIdeal V) t.G e ≫ (t.act.act a).left) ≫ 𝟙 t.G.left)) := by
      have hz := hJ ((fGl (maximalIdeal V) t.G e ≫ (t.act.act a).left) ≫ 𝟙 t.G.left)
      have eq : (𝟙 _ ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) ≫
          fGl (maximalIdeal V) t.G e = (fGl (maximalIdeal V) t.G e ≫ (t.act.act a).left) ≫ 𝟙 t.G.left := by
        rw [Category.id_comp, Category.comp_id]
        exact fstG_act _ _ _
      rw [eq]
      exact hz
    have c := cross_pow _ _ _ hm _ _ _ _ (h₁ e _ (𝟙 _) z JD hJD _ _ m1 m2) (h₂ e _ (𝟙 _) z JD hJD _ _ m1 m2)
    unfold sv at c
    simp only [Category.id_comp, fGl, fstG_act] at c
    unfold sval
    simp only [fGl]
    exact c
  intro Z r y J hJ
  rw [← eA Z r y J hJ, ← eB Z r y J hJ, ← hB' Z r y J hJ]
  have hAB := sec_eq_of_thick hB t.G hL _ B' hthick
  unfold sval
  rw [hAB]

end GlobalTheory.MixedCross
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MixedCrossIdentityGenericFibre
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.GenericCross

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem gs_scal {V : Type} [CommRing V] {Y Z : Scheme.{0}} (r : Z ⟶ Y) (p : Y ⟶ Spec (CommRingCat.of V)) (z : Z)
    (c : V) : gs r z ⊤ (scal p c) = cst (r ≫ p) z c := by
  unfold scal cst
  exact gs_pull r p z ⊤ (by simp) _

theorem isUnit_cst {V : Type} [CommRing V] [IsDomain V] {Z : Scheme.{0}}
    (q : Z ⟶ Spec (CommRingCat.of (FractionRing V))) (z : Z) {c : V} (hc : c ≠ 0) :
    IsUnit (cst (q ≫ jK V) z c) := by
  have hne : algebraMap V (FractionRing V) c ≠ 0 := fun h =>
    hc (IsFractionRing.injective V (FractionRing V) (by rw [h, map_zero]))
  obtain ⟨u, hu⟩ := (IsUnit.mk0 _ hne).map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).inv.hom
  have nat : ((jK V).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom c) =
      (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).inv.hom (algebraMap V (FractionRing V) c) :=
    (congrArg (fun g => g.hom c)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap V (FractionRing V))))).symm
  have h1 : cst (q ≫ jK V) z c = gs q z ⊤ (((jK V).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom c)) :=
    (gs_pull q (jK V) z ⊤ (by simp) _).symm
  rw [h1, nat, ← hu, gs_unit q z ⊤ (by simp) u]
  exact Units.isUnit _

theorem endK_fst {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    {G : Over (Spec (CommRingCat.of V))} (f : G ⟶ G) :
    endK f ≫ pullback.fst G.hom (jK V) = pullback.fst G.hom (jK V) ≫ f.left := by
  unfold endK
  exact pullback.lift_fst _ _ _

theorem endK_snd {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    {G : Over (Spec (CommRingCat.of V))} (f : G ⟶ G) :
    endK f ≫ pullback.snd G.hom (jK V) = pullback.snd G.hom (jK V) := by
  unfold endK
  exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)

theorem main : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Geo.Tor.Host E) (t : Geo.Tor.SAB H (Spec (CommRingCat.of V))) (P : Geo.Tor.PELUnif (maximalIdeal V) t) (a : NumberField.RingOfIntegers E) (N : ℕ), (letI := H.starRing; a * star a = (N : NumberField.RingOfIntegers E)) → 0 < N → letI := H.starRing;  ∀ (k₁ : ℕ) (s₁ : P.U.SecK k₁) (F₁ : Fam P.D.toPre (FractionRing V) k₁) (u₁ : P.U.SecK (k₁ * N)) (F₁' : Fam P.D.toPre (FractionRing V) (k₁ * N)), P.U.Expands k₁ s₁ F₁ → P.U.Expands (k₁ * N) u₁ F₁' → PullAl P.D (FractionRing V) P.oD a k₁ N F₁ F₁' → ∀ (k₂ : ℕ) (s₂ : P.U.SecK k₂) (F₂ : Fam P.D.toPre (FractionRing V) k₂) (u₂ : P.U.SecK (k₂ * N)) (F₂' : Fam P.D.toPre (FractionRing V) (k₂ * N)), P.U.Expands k₂ s₂ F₂ → P.U.Expands (k₂ * N) u₂ F₂' → PullAl P.D (FractionRing V) P.oD a k₂ N F₂ F₂' → ∀ m₁ m₂ : ℕ, m₁ * k₁ = m₂ * k₂ → ∀ (y : (pullback t.G.hom (jK V) : Scheme.{0})) (J), Geo.Tor.Good P.U.LG.L y J → Geo.Tor.sval u₁ (𝟙 _) y J ^ m₁ * Geo.Tor.sval s₂ (endK (t.act.act a)) y J ^ m₂ = Geo.Tor.sval u₂ (𝟙 _) y J ^ m₂ * Geo.Tor.sval s₁ (endK (t.act.act a)) y J ^ m₁ := by
  intro hL V _ _ _ E _ _ _ H t P a N hN hN0 k₁ s₁ F₁ u₁ F₁' he₁ he₁' hp₁ k₂ s₂ F₂ u₂ F₂' he₂ he₂' hp₂
    m₁ m₂ hm y J hJ
  let _ : StarRing (NumberField.RingOfIntegers E) := H.starRing
  obtain ⟨uΨ, huΨ, -⟩ := P.w0
  obtain ⟨X, hX, hXc⟩ := exists_XB (D := P.D) (hL := P.D.toPre.P.isLB) (oa := P.oD) (w0 := H.w0) (uΨ := uΨ)
    (huΨ := huΨ) (a := a) (N := N) (hN := hN) (hN1 := by omega) (k := 1)
  obtain ⟨c₁, σ₁, τ₁, hc₁, hτ₁, hσ₁, ht₁⟩ := GlobalTheory.PullExpInt.main hL.globalFns V E H t P a N hN hN0 X hX hXc
    k₁ s₁ F₁ u₁ F₁' he₁ he₁' hp₁
  obtain ⟨c₂, σ₂, τ₂, hc₂, hτ₂, hσ₂, ht₂⟩ := GlobalTheory.PullExpInt.main hL.globalFns V E H t P a N hN hN0 X hX hXc
    k₂ s₂ F₂ u₂ F₂' he₂ he₂' hp₂
  have hx := GlobalTheory.MixedCross.main hL.lemmaB V E H t P a N hN hN0 X k₁ k₂ m₁ m₂ hm σ₁ τ₁ σ₂ τ₂ ht₁ ht₂ _
    (pullback.fst t.G.hom (jK V)) y J hJ
  have e₁ := GlobalTheory.PullIntegral.sval_of_secScal hσ₁ (𝟙 _) y hJ
  have e₂ := GlobalTheory.PullIntegral.sval_of_secScal hσ₂ (𝟙 _) y hJ
  have f₁ := GlobalTheory.PullIntegral.sval_of_secScal hτ₁ (endK (t.act.act a)) y hJ
  have f₂ := GlobalTheory.PullIntegral.sval_of_secScal hτ₂ (endK (t.act.act a)) y hJ
  rw [gs_scal, Category.id_comp, Category.id_comp] at e₁ e₂
  rw [gs_scal, endK_fst, ← Category.assoc, endK_snd] at f₁ f₂
  rw [e₁, e₂, f₁, f₂] at hx
  have hu : IsUnit (cst (pullback.snd t.G.hom (jK V) ≫ jK V) y c₁ ^ m₁ *
      cst (pullback.snd t.G.hom (jK V) ≫ jK V) y c₂ ^ m₂) :=
    ((isUnit_cst _ y hc₁).pow m₁).mul ((isUnit_cst _ y hc₂).pow m₂)
  apply hu.mul_left_cancel
  linear_combination hx

end GlobalTheory.GenericCross
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MixedCrossIdentityGenericFibreStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj
theorem _root_.GlobalTheory.T.mixed_cross_identity_genericFibre : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Geo.Tor.Host E) (t : Geo.Tor.SAB H (Spec (CommRingCat.of V))) (P : Geo.Tor.PELUnif (maximalIdeal V) t) (a : NumberField.RingOfIntegers E) (N : ℕ), (letI := H.starRing; a * star a = (N : NumberField.RingOfIntegers E)) → 0 < N → letI := H.starRing;  ∀ (k₁ : ℕ) (s₁ : P.U.SecK k₁) (F₁ : Fam P.D.toPre (FractionRing V) k₁) (u₁ : P.U.SecK (k₁ * N)) (F₁' : Fam P.D.toPre (FractionRing V) (k₁ * N)), P.U.Expands k₁ s₁ F₁ → P.U.Expands (k₁ * N) u₁ F₁' → PullAl P.D (FractionRing V) P.oD a k₁ N F₁ F₁' → ∀ (k₂ : ℕ) (s₂ : P.U.SecK k₂) (F₂ : Fam P.D.toPre (FractionRing V) k₂) (u₂ : P.U.SecK (k₂ * N)) (F₂' : Fam P.D.toPre (FractionRing V) (k₂ * N)), P.U.Expands k₂ s₂ F₂ → P.U.Expands (k₂ * N) u₂ F₂' → PullAl P.D (FractionRing V) P.oD a k₂ N F₂ F₂' → ∀ m₁ m₂ : ℕ, m₁ * k₁ = m₂ * k₂ → ∀ (y : (pullback t.G.hom (jK V) : Scheme.{0})) (J), Geo.Tor.Good P.U.LG.L y J → Geo.Tor.sval u₁ (𝟙 _) y J ^ m₁ * Geo.Tor.sval s₂ (endK (t.act.act a)) y J ^ m₂ = Geo.Tor.sval u₂ (𝟙 _) y J ^ m₂ * Geo.Tor.sval s₁ (endK (t.act.act a)) y J ^ m₁ := by
  first | exact @GlobalTheory.GenericCross.main | exact GlobalTheory.GenericCross.main | (intros; apply GlobalTheory.GenericCross.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsIntOfVgeZero
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.IntegralSection

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1 GlobalTheory.IntegralExpansion

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}

theorem exists_eq_of_nonneg (hϖ : Irreducible ϖ) {v : AddValuation (FractionRing V) (WithTop ℚ)}
    (hv : ValOver ϖ (FractionRing V) v) {c : FractionRing V} (h : 0 ≤ v c) :
    ∃ b : V, c = algebraMap V (FractionRing V) b := by
  rcases eq_or_ne c 0 with rfl | hc
  · exact ⟨0, (map_zero _).symm⟩
  obtain ⟨n, u, hu⟩ := hasVal_of_ne_zero hϖ hc

  have hvc : v c = ((n : ℚ) : WithTop ℚ) := hv c n ⟨u, hu⟩
  have hn : (0 : ℤ) ≤ n := by
    rw [hvc] at h
    have h' : (0 : ℚ) ≤ (n : ℚ) := WithTop.coe_le_coe.mp h
    exact_mod_cast h'

  lift n to ℕ using hn
  refine ⟨ϖ ^ n * (u : V), ?_⟩
  rw [hu, map_mul, map_pow, zpow_natCast]

theorem exists_int_of_vge_zero (hϖ : Irreducible ϖ) {D : DegData V (maximalIdeal V)}
    {v : AddValuation (FractionRing V) (WithTop ℚ)} (hv : ValOver ϖ (FractionRing V) v) {k : ℕ} {α : D.toPre.X}
    {s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε k))}
    (hs : VGe D (FractionRing V) v k α s 0) :
    ∃ f : D.toPre.SecB k α,
      GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε k) s
        (D.toPre.famφB α) (DegPre.famε k) f (DegPre.prB D.toPre (FractionRing V)).left 1 := by
  obtain ⟨n, a, σ, σF, hσ, ha, hsum⟩ := hs

  have hint : ∀ i, ∃ b : V, a i = algebraMap V (FractionRing V) b := fun i =>
    exists_eq_of_nonneg hϖ hv (by simpa using ha i)
  choose b hb using hint

  refine ⟨FamInt.secLin (fun i => constFn D.toPre.P.A.hom ⊤ (b i)) σ, ?_⟩
  refine SectionScalarValuation.secScal_of_sval D.toPre.P.isLB fun y J hJ => ?_
  rw [SectionScalarValuation.sval_lin _ σ (fun j => rfl) _ y hJ,
    SectionScalarValuation.sval_lin (fun i => gF D.toPre (FractionRing V) (a i)) σF
      (fun j => (hsum j).trans (by simp only [constBF_eq]; rfl)) _ y hJ]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [SectionScalarValuation.secScal_sval (hσ i) (𝟙 _) y hJ]
  congr 1
  clear hsum hσ ha hJ
  rw [gs_constFn]
  · rw [hb i]

    have e1 := gs_pull (𝟙 _) (fst (TF (R := V) (FractionRing V)) D.toPre.P.A).left y ⊤ trivial
      ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).inv.hom (algebraMap V (FractionRing V) (b i)))
    rw [Category.id_comp] at e1
    have e1' : gs (𝟙 _) y ⊤ (gF D.toPre (FractionRing V) (algebraMap V (FractionRing V) (b i))) =
        cst (fst (TF (R := V) (FractionRing V)) D.toPre.P.A).left y (algebraMap V (FractionRing V) (b i)) := e1
    rw [e1', ← cst_comp, Category.id_comp]
    congr 1

    have h1 := Over.w (DegPre.prB D.toPre (FractionRing V))
    have h2 := Over.w (fst (TF (R := V) (FractionRing V)) D.toPre.P.A)
    rw [h1]
    rw [← h2]
    congr 1

    unfold TF spMap
    change jFK _ ≫ jK V = _
    unfold jFK jK
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  · trivial

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (D : DegData V (maximalIdeal V)) (vK : AddValuation (FractionRing V) (WithTop ℚ)), ValOver ϖ (FractionRing V) vK → ∀ (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : UnifPre (maximalIdeal V) D A G) (k : ℕ) (s : U.SecK k) (E : Fam D.toPre (FractionRing V) k), U.Expands k s E → (∀ α, VGe D (FractionRing V) vK k α (E.s α) 0) → ∃ σ : H0 U.LG.L k, GeneratorPullback.SecScal U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK V)) (fun _ => ((k : ℕ) : ℤ)) s (fun _ : Fin 1 => 𝟙 G.left) (fun _ => ((k : ℕ) : ℤ)) σ (pullback.fst G.hom (jK V)) 1 := by
  intro V _ _ _ ϖ hϖ D vK hvK A G _ _ U k s E hE hvE
  obtain ⟨r, hr, σ, f, hσ, hf, hexp⟩ := hE
  have hg : ∀ α, ∃ g : D.toPre.SecB k α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α)
      (DegPre.famε k) (E.s α) (D.toPre.famφB α) (DegPre.famε k) g (DegPre.prB D.toPre (FractionRing V)).left 1 :=
    fun α => exists_int_of_vge_zero hϖ hvK (hvE α)
  choose g hg using hg
  have hfg : ∀ α, SecIsMul D.toPre.P.A.hom r (f α) (g α) := fun α =>
    secIsMul_of_secScal D.toPre.P.isLB D.toPre.P.A.hom (prB_app_injective D.toPre) (hg α)
      (by rw [Over.w (DegPre.prB D.toPre (FractionRing V))]; exact hf α)
  obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr hϖ

  have hmul : ∀ α, ∃ g' : D.toPre.SecB k α, SecIsMul D.toPre.P.A.hom (ϖ ^ m) (f α) g' := by
    intro α
    obtain ⟨g', hg'⟩ := exists_secIsMul D.toPre.P.A.hom (u : V) (g α)
    obtain ⟨F', hF'⟩ := exists_secIsMul D.toPre.P.A.hom (ϖ ^ m) g'
    have hc := SecIsMul.comp hF' hg'
    have hF'f : F' = f α := SecOps.sec_ext fun j => by
      rw [hc j, hfg α j, hu, mul_comm (u : V)]
    exact ⟨g', hF'f ▸ hF'⟩
  choose g' hg' using hmul

  have hdiv : ∃ τ : H0 U.LG.L k, SecIsMul G.hom (ϖ ^ m) σ τ := by
    rcases m with _ | e
    · refine ⟨σ, fun j => ?_⟩
      simp [scal]
    · exact exists_div_of_expandsAt hϖ U e k σ g' f hg' (hexp e)
  obtain ⟨τ, hτ⟩ := hdiv

  obtain ⟨σ', hσ'⟩ := exists_secIsMul G.hom ((u⁻¹ : Vˣ) : V) τ
  refine ⟨σ', SectionScalarValuation.secScal_of_sval U.LG.isLB fun y J hJ => ?_⟩
  have hlin : ∀ {a : V} {t t' : H0 U.LG.L k}, SecIsMul G.hom a t' t →
      sval t' (𝟙 _ ≫ pullback.fst G.hom (jK V)) y J =
        gs (𝟙 _ ≫ pullback.fst G.hom (jK V)) y ⊤ (scal G.hom a) * sval t (𝟙 _ ≫ pullback.fst G.hom (jK V)) y J := by
    intro a t t' ht
    have hl := SectionScalarValuation.sval_lin (fun _ : Fin 1 => scal G.hom a) (fun _ => t)
      (fun j => by rw [Fin.sum_univ_one]; exact ht j) (𝟙 _ ≫ pullback.fst G.hom (jK V)) y hJ
    rwa [Fin.sum_univ_one] at hl
  have hgs : ∀ {X : Scheme.{0}} (r' : _ ⟶ X) (p : X ⟶ Spec (CommRingCat.of V)) (a : V),
      gs r' y ⊤ (scal p a) = cst (r' ≫ p) y a := fun r' p a => gs_pull r' p y ⊤ trivial _
  have hq : (𝟙 _ ≫ pullback.fst G.hom (jK V)) ≫ G.hom = 𝟙 _ ≫ pullback.snd G.hom (jK V) ≫ jK V := by
    rw [Category.assoc, pullback.condition]
  have key := GlobalTheory.IntegralExpansion.sval_of_secScal hσ (𝟙 _) y hJ
  rw [hlin hτ, hgs, hgs, hq, hu, cst_mul] at key
  rw [hlin hσ', hgs, hq]

  have hunit : IsUnit (cst (𝟙 _ ≫ pullback.snd G.hom (jK V) ≫ jK V) y (ϖ ^ m)) := by
    have hK : algebraMap V (FractionRing V) (ϖ ^ m) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).mpr (pow_ne_zero _ hϖ.ne_zero)
    rw [← Category.assoc]
    change IsUnit (cst (_ ≫ spMap (algebraMap V (FractionRing V))) y _)
    rw [cst_comp]
    have h1 := (cst_mul (𝟙 _ ≫ pullback.snd G.hom (jK V)) y (algebraMap V (FractionRing V) (ϖ ^ m))
      (algebraMap V (FractionRing V) (ϖ ^ m))⁻¹).symm.trans (by rw [mul_inv_cancel₀ hK, cst_one])
    exact ⟨⟨_, _, h1, (mul_comm _ _).trans h1⟩, rfl⟩
  have hT : sval τ (𝟙 _ ≫ pullback.fst G.hom (jK V)) y J =
      cst (𝟙 _ ≫ pullback.snd G.hom (jK V) ≫ jK V) y (u : V) * sval s (𝟙 _) y J :=
    hunit.mul_left_cancel (by rw [key]; ring)
  rw [hT, ← _root_.mul_assoc, ← cst_mul, Units.inv_mul, cst_one, _root_.one_mul]

end GlobalTheory.IntegralSection
end
end
