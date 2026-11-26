module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalTorsionPointLiftSectionTorusExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueIntegralPointEqAdicSumTerms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionFrameEqConstMulIntegralGenerator
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeOneTermEqConstMulPsiMulTheta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveModOfSurjectiveModOpposite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteFlatTorsionHarrisTaylorAbelian
public import Development.AbelianVarietyTheory.Definitions.Divisors.TwistAtEach
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLabelsSurjectiveHomLatticeModLevel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GensOfPsiUnitOn

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemberTermsIntegralUnitShift
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelUnitThetaConstantNeZeroDividesAll
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelUnitThetaConstantNeZeroDividesAll
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Poinc.IntTerm

theorem unit_ne_zero_dvd (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z)
    (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V]
    [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V)
    (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (x₀ : X₁.S.Gam) :
    X₁.M.Div X₁.S.th x₀ z₁ → IsUnit ((X₁.S.r * X₁.S.N : ℕ) : V) ∧ 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ ≠ 0 ∧
      ∀ a, ∃ r : V, 𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩ =
        algebraMap V (FractionRing V) r * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ := by
  intro hdiv
  have sp : ∀ w, X₁.M.Z.fromSpecStalk z₁ w ⤳ z₁ := fun w => by
    have : X₁.M.Z.fromSpecStalk z₁ w ∈ Set.range (X₁.M.Z.fromSpecStalk z₁) := ⟨w, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  set y' : Sp V ⟶ X₁.M.Z := spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ with hy'
  set y : Sp (FractionRing V) ⟶ X₁.M.Z := jK V ≫ y' with hy
  have h1 : y' (closedPoint V) ⤳ z₁ := sp _
  set ξ := y (closedPoint (FractionRing V)) with hξ
  have hξz : ξ ⤳ z₁ := sp _
  have hyξ : ∀ w, y w ⤳ ξ := RatModel.specializes_of_range_eq (RatModel.range_eq_singleton y _)
  have hx₀ : X₁.S.th x₀ ∈ X₁.M.O ξ := 𝔪.reg _ (X₁.S.th_mem x₀)
  have key : ∀ a, 𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩ =
      algebraMap V (FractionRing V) (RatModel.valLoc y' z₁ h1 ⟨_, hdiv.2 a⟩) * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ := by
    intro a
    have hq : X₁.S.th a / X₁.S.th x₀ ∈ X₁.M.O ξ := RatModel.O_le_of_specializes hξz (hdiv.2 a)
    have e : X₁.S.th a = X₁.S.th a / X₁.S.th x₀ * X₁.S.th x₀ := (div_mul_cancel₀ _ hdiv.1).symm
    rw [𝔪.yK_eq, 𝔪.yK_eq]
    change X₁.M.val y (X₁.S.th a) = _ * X₁.M.val y (X₁.S.th x₀)
    rw [show X₁.M.val y (X₁.S.th a) = X₁.M.val y (X₁.S.th a / X₁.S.th x₀ * X₁.S.th x₀) from congrArg _ e,
      RatModel.val_mul hyξ hq hx₀]
    congr 1
    exact RatModel.val_spMap_comp (algebraMap V (FractionRing V)) y' h1 ⟨_, hdiv.2 a⟩
  refine ⟨?_, ?_, fun a => ⟨_, key a⟩⟩
  · have := X₁.S.unit.map (ev.comp ((X₁.M.stalkEquiv z₁).symm.toRingHom.comp (algebraMap X₁.o₁ (X₁.M.O z₁))))
    rwa [map_natCast] at this
  · intro h0
    obtain ⟨c, -, hc⟩ := GoodOut.exists_th_notMem abelianSchemeLaws_all.1 abelianSchemeLaws_all.2 X₁.ρ
      ⟨RingHom.ker 𝔪.yK, RingHom.ker_isPrime _⟩ x₀
    exact hc (by
      change 𝔪.yK _ = 0
      rw [key, h0, mul_zero])

end GlobalTheory.Poinc.IntTerm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelUnitThetaConstantNeZeroDividesAllStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_unit_thetaConstant_ne_zero_divides_all : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → IsUnit ((X₁.S.r * X₁.S.N : ℕ) : V) ∧ 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ ≠ 0 ∧ ∀ a, ∃ r : V, 𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩ = algebraMap V (FractionRing V) r * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ := by
  first | exact @GlobalTheory.Poinc.IntTerm.unit_ne_zero_dvd | exact GlobalTheory.Poinc.IntTerm.unit_ne_zero_dvd | (intros; apply GlobalTheory.Poinc.IntTerm.unit_ne_zero_dvd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemberTermsIntegralUnitShift
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Poinc.IntTerm

theorem mem_of_psiCoord {V : Type} [CommRing V] [IsDomain V] {I : Ideal V} (D : DegData V I) {χ : D.toPre.X} (hχ : χ ≠ 0)
    {r : V} (h : Formalism.L2.Pj.PsiCoord D.toPre χ r) : r ∈ I := by
  obtain ⟨j, h₁, h₂, e⟩ := h
  obtain ⟨r', hr', e'⟩ := D.psi_pos χ hχ j ⊤ (isAffineOpen_top _) h₁ h₂
  have e₁ : r' = DegPre.toOpen (R := V) ⊤ r := GlobalTheory.PsiCoordLocal.jK_app_inj ⊤ (e'.trans e.symm)
  rw [e₁] at hr'
  have hb := GlobalTheory.PsiCoordLocal.toOpen_top_bijective (R := V)
  obtain ⟨s, hs, es⟩ := (Ideal.mem_map_iff_of_surjective _ hb.2).1 hr'
  rwa [← hb.1 es]

theorem mono_zero {s m : ℕ} (W : Matrix (Fin s) (Fin s) ℤ) {X : Type} [AddCommGroup X] {V : Type} [CommRing V]
    (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) : mono W t δ 0 = 1 := by
  simp [mono, qW]

theorem isUnit_of_sub_mem {V : Type} [CommRing V] [IsLocalRing V] {a b : V} (h : a - b ∈ maximalIdeal V) :
    IsUnit a ↔ IsUnit b := by
  rw [← not_iff_not, ← mem_nonunits_iff, ← mem_nonunits_iff, ← mem_maximalIdeal, ← mem_maximalIdeal]
  exact ⟨fun ha => by simpa using sub_mem ha h, fun hb => by simpa using add_mem h hb⟩

theorem exists_terms : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (C : Type) (lab : C → X₁.S.Gam), Set.range lab = X₁.S.HH X₁.M z₁ → ∃ u : (Fin 8 → X) → C → V, 𝔪.Terms x₀ lab (fun mu c => u mu c * mono W t δ mu) ∧ (∀ mu, ∃ c, IsUnit (u mu c)) ∧ ∀ c, lab c = x₀ → IsUnit (u 0 c) := by
  intro g n F W Z i X₁ z₁ act x₀ hdiv V _ _ _ ev X _ m t δ 𝔪 C lab hlab
  have hV := 𝔪.cn
  haveI : IsNoetherianRing V := hV.1
  haveI : CharZero V := hV.2.2.2
  have hA := admissibleBase_of_completeNormalLocalCharZero hV
  have hL := GlobalTheory.firstFiveLaws
  have hN₂ : 2 ≤ X₁.S.r * X₁.S.N := le_trans X₁.S.N_ge (Nat.le_mul_of_pos_left _ X₁.S.r_pos)
  have hN : 1 ≤ X₁.S.r * X₁.S.N := by omega
  obtain ⟨x, fr, th, ρ, hx, hfr, hth, hρ, htf⟩ := GlobalTheory.T.exists_points_frames_thetaSection_genericFibre_member g n F W Z i X₁ z₁ act V ev X m t δ 𝔪
  obtain ⟨hNu, h0, hdv⟩ := GlobalTheory.T.level_unit_thetaConstant_ne_zero_divides_all g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 x₀ hdiv
  obtain ⟨w₀, hw₀⟩ := 𝔪.U.ext
  obtain ⟨s, hs, -⟩ := ((expBijF_and_expandsF_lin hL V _ hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U).1 (FractionRing V) 1 le_rfl w₀ hw₀).1 th
  obtain ⟨l, hl, hlf⟩ := GlobalTheory.T.exists_torsion_frame_eq_const_mul_integral_generator V hV 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U w₀ hw₀ ρ hρ _ hN
  have hint := GlobalTheory.T.dividingThetaConstants_generate_integral_torsion_labels g n F W Z i X₁ z₁ act x₀ hdiv V ev X m t δ 𝔪

  have hxb : ∀ (a) (xb : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ 𝔪.A.A),
      xb.left ≫ 𝔪.φ = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) ≫
        (X₁.ρ.pt a).left →
      xb.left = spMap (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) ≫ (x a).left := by
    intro a xb h
    refine 𝔪.cart.1.hom_ext ?_ ?_
    · rw [h, Category.assoc, hx a, ← Category.assoc]
      congr 1
      rw [spMap, spMap, spMap, ← Spec.map_comp]; rfl
    · rw [Category.assoc, Over.w, Over.w]
      change _ = _ ≫ Spec.map (𝟙 _)
      rw [Spec.map_id, Category.comp_id]; rfl
  have hyy : ∀ c, 𝔪.YY (lab c) 0 := fun c => (hint _).1 (by
    have : lab c ∈ Set.range lab := ⟨c, rfl⟩
    rwa [hlab] at this)
  choose p xb hp hq hxp using hyy
  have hp0 : ∀ c, (p c).y = 0 := fun c => (hp c).trans (map_zero _)
  choose h gi hh hgt hfe hext hpull using fun c => GlobalTheory.T.rationalTorsionPoint_lift_section_torusExtension V hV 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U _ hN (x (lab c)) (xb c) (p c)
    (hxb _ _ (hxp c)) (hp0 c) (hq c)
  choose g' hg' using fun c => GlobalTheory.FieldRestrictionTest.exists_isPullF (toUnit (TF (R := V) (FractionRing V))) (gi c)
  choose w hw hif hlies using fun c => GlobalTheory.T.sectionValue_integralPoint_eq_adicSum_terms V hV 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U w₀ hw₀ (x (lab c)) (fr (lab c)) (h c) (gi c)
    (g' c) l hl (hfe c) (hext c) (hg' c) (hlf _ _ _ (htf _) (hh c) (hext c))
  have htor : ∀ c, ∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) (g' c) o ∧ o.IsZero := fun c => by
    obtain ⟨o, ho, hz⟩ := hgt c
    obtain ⟨o', ho'⟩ := GlobalTheory.FieldRestrictionTest.exists_isPullF (toUnit (TF (R := V) (FractionRing V))) o
    exact ⟨o', GlobalTheory.FieldRestrictionTest.isNsmul_restrict (hg' c) ho' ho,
      GlobalTheory.FieldRestrictionTest.isZero_restrict ho' hz⟩
  have hb : ∀ c, (g' c).b = toUnit _ ≫ (gi c).b := fun c =>
    ((GlobalTheory.FieldRestrictionTest.isPullF_iff _ _ _).1 (hg' c)).1
  have hex : Exhausts 𝔪.D.toPre.P (X₁.S.r * X₁.S.N) fun c => (gi c).b := by
    refine GlobalTheory.T.torsionSections_exhaust_of_generic_geometric V _ _ hN C _ (fun c => (Sep.Frames.torsion_of_nsmul (g' c) _ (hb c) (htor c)).2) fun β hβ => ?_
    obtain ⟨y, hy, ⟨q, hq0, hqy⟩, H⟩ := GlobalTheory.T.geometricTorsionPoint_abelianPart_lies_under_classZero V hV 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U _ hN β hβ
    obtain ⟨a, ha⟩ := GlobalTheory.T.geometricTorsionPoint_genericFibre_member_has_label g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 y hy
    have hmem : a ∈ Set.range lab := by
      rw [hlab]
      exact (hint a).2 ⟨q, y, hq0.trans (map_zero _).symm, hqy, ha⟩
    obtain ⟨c, rfl⟩ := hmem
    have e : xb c = y := Over.OverMorphism.ext ((hxb _ _ (hxp c)).trans (hxb _ _ ha).symm)
    exact ⟨c, (H (p c) (hp0 c) (e ▸ hq c)).symm.trans ((GlobalTheory.FieldRestrictionTest.isPullF_iff _ _ _).1 (hpull c)).1⟩
  obtain ⟨θ, hθ⟩ := exists_isTheta hV 𝔪.D.toPre
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.degree_one_term_eq_const_mul_psi_mul_theta V 𝔪.D.toPre θ hθ s
  choose υ hυ using 𝔪.psi
  choose a ha hau using fun mu c => hκ (gi c) (g' c) (w c) l (hg' c) (hw c) (hif c) (𝔪.e₈ mu) _ (hυ mu)
  have hunit : ∀ mu, ∃ c, IsUnit (a mu c) := fun mu =>
    (GlobalTheory.T.exists_torsionTranslate_thetaSection_unit V 𝔪.D.toPre θ hθ _ hN₂ hNu C _ hex (𝔪.D.toPre.c (𝔪.e₈ mu))).imp fun c hc => hau mu c hc
  have hco : ∀ mu c, coef s (g' c) (w c) (𝔪.e₈ mu) =
      l⁻¹ * κ * algebraMap V (FractionRing V) (υ mu * mono W t δ mu * a mu c) := fun mu c => by
    rw [_root_.mul_assoc, ← ha, inv_mul_cancel_left₀ hl]
  have hsum : ∀ c, ∃ S : V, 𝔪.yK ⟨X₁.S.th (lab c), X₁.S.th_mem _⟩ = l⁻¹ * κ * algebraMap V (FractionRing V) S ∧
      (IsUnit S ↔ IsUnit (a 0 c)) := fun c => by
    obtain ⟨S, hS, hm⟩ := GlobalTheory.T.adicSum_fractionField_eq_mul_integral_congr V _ (𝔪.e₈ 0) (coef s (g' c) (w c))
      (fun χ => υ (𝔪.e₈.symm χ) * mono W t δ (𝔪.e₈.symm χ) * a (𝔪.e₈.symm χ) c) (l⁻¹ * κ) _
      (fun χ => by rw [← hco, AddEquiv.apply_symm_apply])
      (fun χ hχ => Ideal.mul_mem_right _ _ (mem_of_psiCoord 𝔪.D (χ := 𝔪.e₈ (𝔪.e₈.symm χ))
        (by rwa [AddEquiv.apply_symm_apply, ← map_zero 𝔪.e₈]) (hυ _)))
      (hlies c 1 le_rfl (w c) (fun _ _ _ => (pow_one _).symm) (hw c) th s _ hs (hth _))
    refine ⟨S, hS, (isUnit_of_sub_mem hm).trans ?_⟩
    simp only [AddEquiv.symm_apply_apply, mono_zero, _root_.mul_one, Units.isUnit_units_mul]
  choose S hS hSu using hsum
  have hx₀ : x₀ ∈ Set.range lab := by
    rw [hlab]
    exact AddSubgroup.subset_closure hdiv
  obtain ⟨c₀, rfl⟩ := hx₀
  have hκ0 : l⁻¹ * κ ≠ 0 := left_ne_zero_of_mul (hS c₀ ▸ h0)
  have inj := IsFractionRing.injective V (FractionRing V)
  have hS₀ : IsUnit (S c₀) := by
    obtain ⟨c₁, hc₁⟩ := hunit 0
    obtain ⟨r, hr⟩ := hdv (lab c₁)
    rw [hS, hS, mul_left_comm, ← map_mul] at hr
    have e := inj (mul_left_cancel₀ hκ0 hr)
    exact isUnit_of_mul_isUnit_right (e ▸ (hSu c₁).2 hc₁)
  obtain ⟨σ, hσ⟩ := hS₀
  refine ⟨fun mu c => υ mu * a mu c * σ⁻¹, ⟨x, fr, th, w₀, s, g', w, hx, hfr, hth, hw₀, hs,
    fun c => ⟨htor c, hw c, hlies c⟩, fun mu c => ?_⟩, fun mu => (hunit mu).imp fun c hc => ?_, fun c hc => ?_⟩
  · rw [hco, hS, ← hσ, mul_left_comm, ← map_mul]
    congr 2
    linear_combination (υ mu * a mu c * mono W t δ mu : V) * σ.inv_mul
  · exact ((υ mu).isUnit.mul hc).mul (σ⁻¹).isUnit
  · have e₁ := hS c
    have e₂ := hS c₀
    simp only [hc] at e₁
    have e := inj (mul_left_cancel₀ hκ0 (e₁.symm.trans e₂))
    exact ((υ 0).isUnit.mul ((hSu c).1 (e ▸ hσ ▸ σ.isUnit))).mul (σ⁻¹).isUnit

end GlobalTheory.Poinc.IntTerm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemberTermsIntegralUnitShiftStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_member_terms_integral_unit_shift : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (C : Type) (lab : C → X₁.S.Gam), Set.range lab = X₁.S.HH X₁.M z₁ → ∃ u : (Fin 8 → X) → C → V, 𝔪.Terms x₀ lab (fun mu c => u mu c * mono W t δ mu) ∧ (∀ mu, ∃ c, IsUnit (u mu c)) ∧ ∀ c, lab c = x₀ → IsUnit (u 0 c) := by
  first | exact @GlobalTheory.Poinc.IntTerm.exists_terms | exact GlobalTheory.Poinc.IntTerm.exists_terms | (intros; apply GlobalTheory.Poinc.IntTerm.exists_terms <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdemKernel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDominantOpenNatCastIsUnitNonZeroDivisor
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDominantOpenNatCastIsUnitNonZeroDivisor
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_schemeTheoreticallyDominant_isUnit_natCast (T : Scheme.{0}) (c : ℕ)
    (hc : ∀ (U : T.Opens) (f : Γ(T, U)), (c : Γ(T, U)) * f = 0 → f = 0) :
    ∃ (U : Scheme.{0}) (j : U ⟶ T), IsSchemeTheoreticallyDominant j ∧ IsUnit (c : Γ(U, ⊤)) := by
  refine ⟨(T.basicOpen (c : Γ(T, ⊤))).toScheme, (T.basicOpen (c : Γ(T, ⊤))).ι, ?_, ?_⟩
  · refine isSchemeTheoreticallyDominant_ι_of_germ_eq_zero_over_affine T T (𝟙 T) _ ?_
    intro U V hU _ _ b hb
    have key : ∀ (n : ℕ) (b : Γ(T, U)), (c : Γ(T, U)) ^ n * b = 0 → b = 0 := by
      intro n
      induction n with
      | zero => intro b h; simpa using h
      | succ n ih =>
        intro b h
        exact hc U b (ih _ (by rw [← _root_.mul_assoc, ← pow_succ]; exact h))
    have hD : T.basicOpen (c : Γ(T, U)) = U ⊓ T.basicOpen (c : Γ(T, ⊤)) := by
      rw [← T.basicOpen_res (c : Γ(T, ⊤)) (homOfLE (le_top : U ≤ ⊤)).op, map_natCast]
    have h0 : T.presheaf.map (homOfLE (T.basicOpen_le (c : Γ(T, U)))).op b = 0 := by
      refine TopCat.Presheaf.section_ext T.sheaf _ _ 0 (fun x hx => ?_)
      show T.presheaf.germ _ x hx (T.presheaf.map _ b) = T.presheaf.germ _ x hx 0
      rw [TopCat.Presheaf.germ_res_apply, map_zero]
      exact hb x _ (hD ▸ hx).2
    letI := hU.isLocalization_basicOpen (c : Γ(T, U))
    obtain ⟨⟨m, n, rfl⟩, hm⟩ :=
      (IsLocalization.map_eq_zero_iff (Submonoid.powers (c : Γ(T, U)))
        Γ(T, T.basicOpen (c : Γ(T, U))) b).mp h0
    exact key n b hm
  · have := (T.toRingedSpace.isUnit_res_basicOpen (c : Γ(T, ⊤))).map
      (T.basicOpen (c : Γ(T, ⊤))).topIso.inv.hom
    exact (congrArg IsUnit ((congrArg _ (map_natCast _ c)).trans (map_natCast _ c))).mp this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDominantOpenNatCastIsUnitNonZeroDivisorStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dominant_natCast_isUnit_of_nonZeroDivisor : ∀ (T : Scheme.{0}) (c : ℕ), (∀ (U : T.Opens) (f : Γ(T, U)), (c : Γ(T, U)) * f = 0 → f = 0) → ∃ (U : Scheme.{0}) (j : U ⟶ T), IsSchemeTheoreticallyDominant j ∧ IsUnit (c : Γ(U, ⊤)) := by
  first | (exact @GlobalTheory.exists_schemeTheoreticallyDominant_isUnit_natCast) | (exact GlobalTheory.exists_schemeTheoreticallyDominant_isUnit_natCast) | (intros; apply GlobalTheory.exists_schemeTheoreticallyDominant_isUnit_natCast  <;> assumption)
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open scoped CategoryTheory.Obj

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.UPel.HT.ES.OrdCount


open GlobalTheory.IwLevel GlobalTheory.IwLevel.KerGrp in
theorem exists_idem_kernel : ∀ (S : Scheme.{0}) (A A' : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] (ψ : A ⟶ A') (f : A ⟶ A), IsMonHom ψ → IsMonHom f → IsFinite ψ.left → Flat ψ.left → (∀ (T : Over S) (z : T ⟶ A), z ≫ ψ = 1 → (z ≫ f) ≫ ψ = 1 ∧ (z ≫ f) ≫ f = z ≫ f) → ∃ (K : Over S) (_ : GrpObj K) (i : K ⟶ A), IsMonHom i ∧ Mono i ∧ IsFinite K.hom ∧ Flat K.hom ∧ ∀ (T : Over S) (z : T ⟶ A), GlobalTheory.IwLevel.InSub i z ↔ (z ≫ ψ = 1 ∧ z ≫ f = 1) := by
  intro S A A' _ _ _ _ ψ fx _ _ hfin hfl hyp
  letI gH : GrpObj (IwLevel.ker ψ) := grp ψ
  haveI : IsMonHom (pullback.fst ψ η[A']) := isMonHom_fst ψ
  have hPB := (IsPullback.of_hasPullback ψ η[A']).map (Over.forget S)
  have hHfin : IsFinite (IwLevel.ker ψ).hom := by
    rw [← Over.w (pullback.snd ψ η[A'])]
    haveI : IsFinite (pullback.snd ψ η[A']).left := MorphismProperty.of_isPullback (P := @IsFinite) hPB hfin
    exact inferInstanceAs (IsFinite (_ ≫ 𝟙 S))
  have hHflat : Flat (IwLevel.ker ψ).hom := by
    rw [← Over.w (pullback.snd ψ η[A'])]
    haveI : Flat (pullback.snd ψ η[A']).left := MorphismProperty.of_isPullback (P := @Flat) hPB hfl
    exact inferInstanceAs (Flat (_ ≫ 𝟙 S))
  set jH := pullback.fst ψ η[A'] with hjH
  have hj : jH ≫ ψ = 1 := fst_comp ψ
  let g : IwLevel.ker ψ ⟶ IwLevel.ker ψ := KerGrp.lift ψ (jH ≫ fx) (hyp _ jH hj).1
  have hg : g ≫ jH = jH ≫ fx := KerGrp.lift_fst _ _ _
  have hxx' : jH ≫ fx ≫ fx = jH ≫ fx := by rw [← Category.assoc]; exact (hyp _ jH hj).2
  letI gK : GrpObj (IwLevel.ker (jH ≫ fx)) := grp (jH ≫ fx)
  haveI : IsMonHom (pullback.fst (jH ≫ fx) η[A]) := isMonHom_fst (jH ≫ fx)
  set iK := pullback.fst (jH ≫ fx) η[A] with hiK
  have hk : iK ≫ jH ≫ fx = 1 := fst_comp (jH ≫ fx)
  have hrk : (𝟙 (IwLevel.ker ψ) / g) ≫ jH ≫ fx = 1 := by
    rw [← Category.assoc, GrpObj.div_comp, Category.id_comp, hg, GrpObj.div_comp, Category.assoc, hxx',
      div_self']
  let r : IwLevel.ker ψ ⟶ IwLevel.ker (jH ≫ fx) := KerGrp.lift (jH ≫ fx) (𝟙 (IwLevel.ker ψ) / g) hrk
  have hr : r ≫ iK = 𝟙 (IwLevel.ker ψ) / g := KerGrp.lift_fst _ _ _
  have hiKg : iK ≫ g = 1 := KerGrp.hom_ext ψ (by
    rw [Category.assoc, hg, hk, MonObj.one_comp])
  have hir : iK ≫ r = 𝟙 _ := KerGrp.hom_ext (jH ≫ fx) (by
    rw [Category.assoc, hr, GrpObj.comp_div, Category.comp_id, hiKg, div_one, Category.id_comp])
  have hirl : iK.left ≫ r.left = 𝟙 _ := by rw [← Over.comp_left, hir, Over.id_left]
  have hKfin : IsFinite (IwLevel.ker (jH ≫ fx)).hom := by
    haveI : IsFinite (r.left ≫ (IwLevel.ker (jH ≫ fx)).hom) := by rw [Over.w r]; exact hHfin
    haveI : IsSeparated (r.left ≫ (IwLevel.ker (jH ≫ fx)).hom) := by rw [Over.w r]; infer_instance
    haveI : IsSeparated r.left := IsSeparated.of_comp _ (IwLevel.ker (jH ≫ fx)).hom
    haveI : IsFinite (iK.left ≫ r.left) := by rw [hirl]; infer_instance
    haveI : IsFinite iK.left := IsFinite.of_comp _ r.left
    rw [← Over.w iK]; infer_instance
  have hKflat : Flat (IwLevel.ker (jH ≫ fx)).hom := by
    haveI : Flat (r.left ≫ (IwLevel.ker (jH ≫ fx)).hom) := by rw [Over.w r]; exact hHflat
    exact HTTorsionFF.flat_of_retract _ iK.left r.left hirl
  refine ⟨IwLevel.ker (jH ≫ fx), gK, iK ≫ jH, inferInstance, inferInstance, hKfin, hKflat, fun T z => ?_⟩
  refine ⟨?_, fun ⟨h1, h2⟩ => ?_⟩
  · rintro ⟨y, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [Category.assoc, Category.assoc, hj, MonObj.comp_one, MonObj.comp_one]
    · rw [Category.assoc, Category.assoc, hk, MonObj.comp_one]
  · refine ⟨KerGrp.lift (jH ≫ fx) (KerGrp.lift ψ z h1) (by rw [← Category.assoc, KerGrp.lift_fst, h2]), ?_⟩
    rw [← Category.assoc, KerGrp.lift_fst, KerGrp.lift_fst]

def subEquiv {S : Scheme.{0}} {A K T : Over S} (i : K ⟶ A) [Mono i] (P : (T ⟶ A) → Prop)
    (h : ∀ x, GlobalTheory.IwLevel.InSub i x ↔ P x) : (T ⟶ K) ≃ {x : T ⟶ A // P x} :=
  Equiv.ofBijective (fun g => ⟨g ≫ i, (h _).1 ⟨g, rfl⟩⟩)
    ⟨fun g g' hgg => (cancel_mono i).1 (congrArg Subtype.val hgg),
     fun x => let ⟨g, hg⟩ := (h x.1).2 x.2; ⟨g, Subtype.ext hg⟩⟩

theorem eq_one_of_reg {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A)
    {T : Over S} (x : T ⟶ A) (c : ℕ)
    (hc : ∀ (U : T.left.Opens) (f : Γ(T.left, U)), (c : Γ(T.left, U)) * f = 0 → f = 0) (hx : x ^ c = 1)
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k], (c : k) ≠ 0 → ∀ (z : Sp k ⟶ S) (g : Over.mk z ⟶ T), g ≫ x = 1) :
    x = 1 := by
  obtain ⟨U, j, hj, hu⟩ := GlobalTheory.T.exists_dominant_natCast_isUnit_of_nonZeroDivisor T.left c hc
  let j' : Over.mk (j ≫ T.hom) ⟶ T := Over.homMk j
  have h1 : j' ≫ x = 1 := GlobalTheory.T.abelianScheme_torsionPoint_trivial_of_geometric S A hA _ (j' ≫ x) c hu (by rw [← MonObj.comp_pow, hx, MonObj.comp_one])
    (fun k _ _ hk z g => by rw [← Category.assoc]; exact h k hk z _)
  have h2 : j' ≫ x = j' ≫ 1 := by rw [h1, MonObj.comp_one]
  have := hA.proper
  exact Over.OverMorphism.ext (GlobalTheory.hom_ext_of_isSchemeTheoreticallyDominant j A.hom
    (congrArg CommaMorphism.left h2) (by rw [Over.w, Over.w]))

end GlobalTheory.UPel.HT.ES.OrdCount
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumFCompEquiv
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

noncomputable section

namespace GlobalTheory.GSep.TransTerms

variable {I : Type}

def TorChar {X₁ : GSet} {z₁ : X₁.M.Z} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}
    {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
    {X : Type} [AddCommGroup X] {t : X → V} {δ : I → X → X}
    (𝔪 : GMem X₁ z₁ act V ev X t δ) (τ : X₁.S.Gam) (χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ) : Prop :=
  χ ^ (X₁.S.r * X₁.S.N) = 1 ∧ ∀ g₀ : GtPtF 𝔪.D.toPre (FractionRing V), IsTor χ g₀ →
    ∃ (p : QkPt 𝔪.D.toPre (FractionRing V) (X₁.S.r * X₁.S.N)) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A),
      p.y = 0 ∧ p.g = g₀ ∧ QkToAkU 𝔪.U.toUnifPre (FractionRing V) (X₁.S.r * X₁.S.N) p x ∧
      x.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left

def TransExp {X₁ : GSet} {z₁ : X₁.M.Z} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}
    {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
    {X : Type} [AddCommGroup X] {t : X → V} {δ : I → X → X}
    (𝔪 : GMem X₁ z₁ act V ev X t δ) (x₀ a τ : X₁.S.Gam) (e : ℕ) : Prop :=
  ∀ χ, TorChar 𝔪 τ χ → ∀ (C : Type) (lab : C → X₁.S.Gam) (T : X → C → V), 𝔪.Terms x₀ lab T →
    ∀ c, lab c = a → ∀ (C' : Type) (lab' : C' → X₁.S.Gam) (T' : X → C' → V), 𝔪.Terms x₀ lab' T' →
    ∀ c', lab' c' = a + τ → ∀ mu : X,
      ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) * algebraMap V (FractionRing V) (T mu c) =
        𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ e)) * algebraMap V (FractionRing V) (T' mu c')

theorem sumF_comp_equiv {R : Type} [CommRing R] [IsDomain R] {J : Ideal R} {K : Type} [Field K]
    [Algebra (FractionRing R) K] {Ix Jx : Type} {x : Ix → K} {s : K} (e : Jx ≃ Ix) (h : SumF J K x s) :
    SumF J K (fun j => x (e j)) s := by
  letI : Module R K := Module.compHom K (algebraMap R (FractionRing R))
  obtain ⟨N, hN, hs, hx, hlim⟩ := h
  refine ⟨N, hN, hs, fun j => hx _, fun k => ?_⟩
  classical
  obtain ⟨S, hS⟩ := hlim k
  refine ⟨S.map e.symm.toEmbedding, fun T hT => ?_⟩
  have hsub : S ⊆ T.map e.toEmbedding := by
    intro a ha
    have := hT (Finset.mem_map_of_mem e.symm.toEmbedding ha)
    exact Finset.mem_map.2 ⟨e.symm a, this, by simp⟩
  have := hS _ hsub
  rwa [Finset.sum_map] at this

end GlobalTheory.GSep.TransTerms
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPIsogenyOfSimilitudePullbackObjects
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPIsogenyOfSimilitudePullbackObjects
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ESPull

variable {S S' : Scheme.{0}} {f : S' ⟶ S}

theorem hom_ext_of_cart {A : Over S} {A₁ : Over S'} [GrpObj A] [GrpObj A₁] {φ : A₁.left ⟶ A.left}
    (h : IsGrpPullback A₁ A f φ) {T : Over S'} {u v : T ⟶ A₁} (e : u.left ≫ φ = v.left ≫ φ) : u = v :=
  Over.OverMorphism.ext (h.1.hom_ext e (by rw [Over.w u, Over.w v]))

theorem exists_baseChange {A B : Over S} {A₁ B₁ : Over S'} [GrpObj A] [GrpObj B] [GrpObj A₁] [GrpObj B₁]
    {φ : A₁.left ⟶ A.left} {χ : B₁.left ⟶ B.left} (hA : IsGrpPullback A₁ A f φ) (hB : IsGrpPullback B₁ B f χ)
    (ψ : A ⟶ B) : ∃ ψ₁ : A₁ ⟶ B₁, ψ₁.left ≫ χ = φ ≫ ψ.left :=
  ⟨Over.homMk (hB.1.lift (φ ≫ ψ.left) A₁.hom (by rw [Category.assoc, Over.w ψ, hA.1.w]))
    (hB.1.lift_snd _ _ _), hB.1.lift_fst _ _ _⟩

theorem grpSchemeSquareProductMap_comp_fst {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] (ψ : A ⟶ A') :
    Hecke.sq2 ψ ≫ (fst A' A').left = (fst A A).left ≫ ψ.left := by
  rw [Hecke.sq2, ← Over.comp_left, lift_fst, Over.comp_left]

theorem grpSchemeSquareProductMap_comp_snd {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] (ψ : A ⟶ A') :
    Hecke.sq2 ψ ≫ (snd A' A').left = (snd A A).left ≫ ψ.left := by
  rw [Hecke.sq2, ← Over.comp_left, lift_snd, Over.comp_left]

theorem isPIsog_pull : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N c : ℕ) (S S' : Scheme.{0}) (s : S ⟶ Sp R) (s' : S' ⟶ Sp R) (f : S' ⟶ S) (o o' : Obj b N s) (o₁ o₁' : Obj b N s') (m : ObjMap o₁ o f) (m' : ObjMap o₁' o' f) (ψ : o.A ⟶ o'.A), IsPIsog c o o' ψ → ∃ ψ₁ : o₁.A ⟶ o₁'.A, IsPIsog c o₁ o₁' ψ₁ ∧ m.φ ≫ ψ.left = ψ₁.left ≫ m'.φ := by
  intro p _ D R _ b N c S S' s s' f o o' o₁ o₁' m m' ψ hψ
  obtain ⟨hk, hm, hact, heta, ⟨hP⟩, ψ', hm', h₁, h₂⟩ := hψ
  obtain ⟨ψ₁, sq⟩ := exists_baseChange m.cart m'.cart ψ
  obtain ⟨ψ₁', sq'⟩ := exists_baseChange m'.cart m.cart ψ'
  haveI := hm
  haveI := hm'
  have hm₁ : IsMonHom ψ₁ := ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.isMonHom_of_grpPullback m.cart m'.cart ψ ψ₁ sq
  have hm₁' : IsMonHom ψ₁' := ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.isMonHom_of_grpPullback m'.cart m.cart ψ' ψ₁' sq'
  have hsq2 : Hecke.sq2 ψ₁ ≫ m'.φ₂ = m.φ₂ ≫ Hecke.sq2 ψ := by
    apply Over.tensorObj_ext
    · change (Hecke.sq2 ψ₁ ≫ m'.φ₂) ≫ (fst o'.A o'.A).left = (m.φ₂ ≫ Hecke.sq2 ψ) ≫ (fst o'.A o'.A).left
      have l : (Hecke.sq2 ψ₁ ≫ m'.φ₂) ≫ (fst o'.A o'.A).left = (fst o₁.A o₁.A).left ≫ m.φ ≫ ψ.left := by
        rw [Category.assoc, m'.sq.1, ← Category.assoc, grpSchemeSquareProductMap_comp_fst, Category.assoc, sq]
      have r : (m.φ₂ ≫ Hecke.sq2 ψ) ≫ (fst o'.A o'.A).left = (fst o₁.A o₁.A).left ≫ m.φ ≫ ψ.left := by
        rw [Category.assoc, grpSchemeSquareProductMap_comp_fst, ← Category.assoc, m.sq.1, Category.assoc]
      exact l.trans r.symm
    · change (Hecke.sq2 ψ₁ ≫ m'.φ₂) ≫ (snd o'.A o'.A).left = (m.φ₂ ≫ Hecke.sq2 ψ) ≫ (snd o'.A o'.A).left
      have l : (Hecke.sq2 ψ₁ ≫ m'.φ₂) ≫ (snd o'.A o'.A).left = (snd o₁.A o₁.A).left ≫ m.φ ≫ ψ.left := by
        rw [Category.assoc, m'.sq.2, ← Category.assoc, grpSchemeSquareProductMap_comp_snd, Category.assoc, sq]
      have r : (m.φ₂ ≫ Hecke.sq2 ψ) ≫ (snd o'.A o'.A).left = (snd o₁.A o₁.A).left ≫ m.φ ≫ ψ.left := by
        rw [Category.assoc, grpSchemeSquareProductMap_comp_snd, ← Category.assoc, m.sq.2, Category.assoc]
      exact l.trans r.symm
  refine ⟨ψ₁, ⟨hk, hm₁, fun a => ?_, fun x => ?_, ⟨?_⟩, ψ₁', hm₁', ?_, ?_⟩, sq.symm⟩
  · apply hom_ext_of_cart m'.cart
    have e1 : (o₁.act.act a ≫ ψ₁).left ≫ m'.φ = m.φ ≫ (o.act.act a ≫ ψ).left := by
      rw [Over.comp_left, Over.comp_left, Category.assoc, sq, ← Category.assoc, m.act, Category.assoc]
    have e2 : (ψ₁ ≫ o₁'.act.act a).left ≫ m'.φ = m.φ ≫ (ψ ≫ o'.act.act a).left := by
      rw [Over.comp_left, Over.comp_left, Category.assoc, m'.act, ← Category.assoc, sq, Category.assoc]
    rw [e1, e2, hact a]
  · apply hom_ext_of_cart m'.cart
    have e1 : (o₁.eta x ≫ ψ₁).left ≫ m'.φ = f ≫ (o.eta x ≫ ψ).left := by
      rw [Over.comp_left, Over.comp_left, Category.assoc, sq, ← Category.assoc, m.eta, Category.assoc]
    rw [e1, m'.eta, heta x]
  · have hL₁ : (Hecke.lbPow o₁.P c).IsLB := LB.isLB_linComb o₁.isLB _ _
    have hL : (Hecke.lbPow o.P c).IsLB := LB.isLB_linComb o.isLB _ _
    refine (GlobalTheory.CechPic.cls_eq_iff hL₁ (pull_isLB o₁'.isLB _)).1 ?_
    have e₁ := (GlobalTheory.CechPic.cls_eq_iff o₁.isLB (pull_isLB o.isLB m.φ₂)).2 m.pol
    have e₂ := (GlobalTheory.CechPic.cls_eq_iff o₁'.isLB (pull_isLB o'.isLB m'.φ₂)).2 m'.pol
    have e₃ := (GlobalTheory.CechPic.cls_eq_iff hL (pull_isLB o'.isLB (Hecke.sq2 ψ))).2 hP
    rw [GlobalTheory.BirigidPow.cls_lbPow o.isLB, GlobalTheory.CechPic.cls_pull o'.isLB] at e₃
    rw [GlobalTheory.CechPic.cls_pull o.isLB] at e₁
    rw [GlobalTheory.CechPic.cls_pull o'.isLB] at e₂
    rw [GlobalTheory.BirigidPow.cls_lbPow o₁.isLB, GlobalTheory.CechPic.cls_pull o₁'.isLB, e₂, ← GlobalTheory.CechPic.pull_comp, hsq2,
      GlobalTheory.CechPic.pull_comp, ← e₃, map_nsmul, ← e₁]
  · apply hom_ext_of_cart m.cart
    rw [ESDual.pow_left_comm m.cart c, Over.comp_left, Category.assoc, sq', ← Category.assoc, sq, Category.assoc,
      ← Over.comp_left, h₁]
  · apply hom_ext_of_cart m'.cart
    rw [ESDual.pow_left_comm m'.cart c, Over.comp_left, Category.assoc, sq, ← Category.assoc, sq', Category.assoc,
      ← Over.comp_left, h₂]

end GlobalTheory.UPel.HT.ESPull
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPIsogenyOfSimilitudePullbackObjectsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPIsogenyOfSimilitude_pullback_objects : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N c : ℕ) (S S' : Scheme.{0}) (s : S ⟶ Sp R) (s' : S' ⟶ Sp R) (f : S' ⟶ S) (o o' : Obj b N s) (o₁ o₁' : Obj b N s') (m : ObjMap o₁ o f) (m' : ObjMap o₁' o' f) (ψ : o.A ⟶ o'.A), IsPIsog c o o' ψ → ∃ ψ₁ : o₁.A ⟶ o₁'.A, IsPIsog c o₁ o₁' ψ₁ ∧ m.φ ≫ ψ.left = ψ₁.left ≫ m'.φ := by
  first | (exact @GlobalTheory.UPel.HT.ESPull.isPIsog_pull) | (exact GlobalTheory.UPel.HT.ESPull.isPIsog_pull) | (intros; apply GlobalTheory.UPel.HT.ESPull.isPIsog_pull  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedAdicSumTermsOfFractionFieldSum
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedAdicSumTermsOfFractionFieldSum
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

noncomputable section

namespace GlobalTheory.GSep.TwistSum₂

theorem val_stalkHom (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V]
    (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) [IsLocalHom ev] (a : X₁.M.Z.presheaf.stalk z₁) :
    X₁.M.val (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (X₁.M.stalkHom z₁ a) =
      algebraMap V (FractionRing V) (ev a) := by
  have hc : (spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint V) = z₁ := by
    refine (Scheme.Hom.comp_apply _ _ _).trans
      (Eq.trans (congrArg (X₁.M.Z.fromSpecStalk z₁) ?_) (Scheme.fromSpecStalk_closedPoint (x := z₁)))
    exact comap_closedPoint ev
  have h : (spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint V) ⤳ z₁ := specializes_of_eq hc
  have e := RatModel.val_spMap_comp (algebraMap V (FractionRing V)) (spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) h
    (X₁.M.stalkEquiv z₁ a)
  rw [RatModel.coe_stalkEquiv] at e
  refine e.trans (congrArg _ ?_)
  have hψ : Spec.map (X₁.M.Z.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo (spMap ev ≫ X₁.M.Z.fromSpecStalk z₁)) ≫
      X₁.M.Z.fromSpecStalk z₁ = spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ := by
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  have heq : spMap ev = Spec.map (X₁.M.Z.presheaf.stalkSpecializes h ≫
      Scheme.stalkClosedPointTo (spMap ev ≫ X₁.M.Z.fromSpecStalk z₁)) := by
    rw [← cancel_mono (X₁.M.Z.fromSpecStalk z₁), hψ]
  have hφψ := Spec.map_injective heq
  simp only [RatModel.valLoc, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    RingEquiv.symm_apply_apply]
  exact (congrArg (fun φ => φ.hom a) hφψ).symm

theorem twistSum_of_sumF : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (x₀ : X₁.S.Gam) (C : Type) (lab : C → X₁.S.Gam) (T : X → C → V) (sg : ℤˣ) (c : C) (τ : X₁.S.Gam) (χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ) (e : ℕ), 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ ≠ 0 → (∀ mu, ∃ a : X₁.S.Gam, 𝔪.YY a mu) → (∀ a mu, 𝔪.YY a mu → ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) = 𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (((sg : ℤˣ) : ℤ) • eStd X₁.S.g _ τ a).val)))) → SumF (maximalIdeal V) (FractionRing V) (fun mu : X => ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) * (algebraMap V (FractionRing V) (T mu c) * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩)) (𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ e)) * 𝔪.yK ⟨X₁.S.th (lab c + τ), X₁.S.th_mem (lab c + τ)⟩) → GlobalTheory.GSep.TwistSum X₁ z₁ act x₀ 𝔪 lab T sg c τ e := by
  intro I X₁ z₁ act V _ _ _ ev X _ t δ 𝔪 x₀ C lab T sg c τ χ e hθ hY hχ hS
  intro zt h hzt hh wt hwt
  haveI : IsNoetherianRing V := 𝔪.cn.1
  haveI : IsLocalHom ev := 𝔪.loc
  have hc : (spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint V) = z₁ := by
    refine (Scheme.Hom.comp_apply _ _ _).trans
      (Eq.trans (congrArg (X₁.M.Z.fromSpecStalk z₁) ?_) (Scheme.fromSpecStalk_closedPoint (x := z₁)))
    exact comap_closedPoint ev
  have hsp : ∀ w, (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) w ⤳
      (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint (FractionRing V)) :=
    RatModel.specializes_of_range_eq (RatModel.range_eq_singleton (M := X₁.M) (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (IsLocalRing.closedPoint (FractionRing V)))
  have hgen : (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint (FractionRing V)) ⤳ z₁ := by
    have h1 : (jK V) (closedPoint (FractionRing V)) ⤳ closedPoint V := IsLocalRing.specializes_closedPoint _
    have h2 := h1.map (spMap ev ≫ X₁.M.Z.fromSpecStalk z₁).continuous
    rw [hc] at h2
    exact h2
  have hO : ∀ s, X₁.M.stalkHom z₁ s ∈
      X₁.M.O ((jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint (FractionRing V))) := fun s =>
    RatModel.O_le_of_specializes hgen (X₁.M.stalkEquiv z₁ s).2
  have hR : ∀ a ∈ X₁.S.R, a ∈ X₁.M.O ((jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint (FractionRing V))) := 𝔪.reg
  have hyK : ∀ (a : X₁.Ω₁) (ha : a ∈ X₁.S.R), 𝔪.yK ⟨a, ha⟩ = X₁.M.val (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) a :=
    fun a ha => 𝔪.yK_eq ⟨a, ha⟩
  have hyA : ∀ b : X₁.o₁, 𝔪.yK (algebraMap X₁.o₁ X₁.S.R b) =
      X₁.M.val (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (algebraMap X₁.o₁ X₁.Ω₁ b) := fun b => by
    rw [𝔪.yK_eq, Subalgebra.coe_algebraMap]
  have hzt' : algebraMap V (FractionRing V) (ev zt) = 𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N))) := by
    rw [← val_stalkHom X₁ z₁ ev, hzt, hyA]
  have hth0 : X₁.S.th x₀ ≠ 0 := by
    intro h0
    apply hθ
    rw [hyK, h0, RatModel.val_zero]
  have hh' : algebraMap V (FractionRing V) (ev h) * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ =
      𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ e)) * 𝔪.yK ⟨X₁.S.th (lab c + τ), X₁.S.th_mem (lab c + τ)⟩ := by
    rw [← val_stalkHom X₁ z₁ ev, hyA, hyK, hyK, ← RatModel.val_mul hsp (hO h) (hR _ (X₁.S.th_mem x₀)),
      ← RatModel.val_mul hsp (hR _ (Subalgebra.algebraMap_mem _ _)) (hR _ (X₁.S.th_mem _)), hh,
      div_mul_cancel₀ _ hth0]
  have hterm : ∀ mu : X, ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) *
      (algebraMap V (FractionRing V) (T mu c) * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩) =
      algebraMap V (FractionRing V) (ev zt ^ (wt mu).val * T mu c) * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ := by
    intro mu
    obtain ⟨a, ha⟩ := hY mu
    rw [hχ a mu ha, ← hwt a mu ha, pow_mul, map_pow, map_pow, ← hzt', map_mul, map_pow]
    ring
  refine GlobalTheory.Poinc.TwistSum₂.sumI_of_sumF_mul _ _ _ hθ ?_
  convert hS using 1
  · funext mu
    exact (hterm mu).symm

end GlobalTheory.GSep.TwistSum₂
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedAdicSumTermsOfFractionFieldSumStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedAdicSum_terms_of_fractionField_sum : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (x₀ : X₁.S.Gam) (C : Type) (lab : C → X₁.S.Gam) (T : X → C → V) (sg : ℤˣ) (c : C) (τ : X₁.S.Gam) (χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ) (e : ℕ), 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ ≠ 0 → (∀ mu, ∃ a : X₁.S.Gam, 𝔪.YY a mu) → (∀ a mu, 𝔪.YY a mu → ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) = 𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (((sg : ℤˣ) : ℤ) • eStd X₁.S.g _ τ a).val)))) → SumF (maximalIdeal V) (FractionRing V) (fun mu : X => ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) * (algebraMap V (FractionRing V) (T mu c) * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩)) (𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ e)) * 𝔪.yK ⟨X₁.S.th (lab c + τ), X₁.S.th_mem (lab c + τ)⟩) → GlobalTheory.GSep.TwistSum X₁ z₁ act x₀ 𝔪 lab T sg c τ e := by
  first | exact @GlobalTheory.GSep.TwistSum₂.twistSum_of_sumF | exact GlobalTheory.GSep.TwistSum₂.twistSum_of_sumF | (intros; apply GlobalTheory.GSep.TwistSum₂.twistSum_of_sumF <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalFamilyPeriodsInCoordinates
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalFamilyPeriodsInCoordinates
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UCanon.PerCoord

theorem comp_C_injective {W R σ : Type} [CommRing W] [IsLocalRing W] [CommRing R] [IsLocalRing R]
    (ψ : MvPolynomial σ W →+* R) (hf : ψ.Flat) (hl : IsLocalHom (ψ.comp MvPolynomial.C)) :
    Function.Injective (ψ.comp MvPolynomial.C) := by
  have hC : (MvPolynomial.C : W →+* MvPolynomial σ W).Flat := by
    show (algebraMap W (MvPolynomial σ W)).Flat
    rw [RingHom.flat_algebraMap_iff]
    infer_instance
  have h := RingHom.Flat.comp hC hf
  letI := (ψ.comp MvPolynomial.C).toAlgebra
  haveI : Module.Flat W R := h
  haveI : IsLocalHom (algebraMap W R) := hl
  haveI := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := W) (B := R)
  exact FaithfulSMul.algebraMap_injective W R

theorem prod_zpow_add {K Ix : Type} [Field K] [Fintype Ix] (c : Ix → K) (hc : ∀ k, c k ≠ 0) (A B C D : Ix → ℤ)
    (h : ∀ k, A k = D k + B k + C k) :
    ∏ k, c k ^ A k = (∏ k, c k ^ D k) * (∏ k, c k ^ B k) * ∏ k, c k ^ C k := by
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [h k, zpow_add₀ (hc k), zpow_add₀ (hc k)]

end GlobalTheory.UCanon.PerCoord

namespace GlobalTheory.UCanon.PerCoord

theorem second_diff {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) {X Y : Type} [AddCommGroup X]
    [Module (𝓞 E) X] [AddCommGroup Y] [Module (𝓞 E) Y] (e : X ≃ₗ[𝓞 E] Y) {β : LinearMap.BilinForm ℤ Y}
    (hβ : β ∈ balForms H.bar Y) (a b : X) :
    β (e (a + b)) (H.w0 • e (a + b)) = β (e a) (e b) + β (e a) (H.w0 • e a) + β (e b) (H.w0 • e b) := by
  have h1 : β (e b) (H.w0 • e a) = β (e a) (H.bar H.w0 • e b) := (hβ.1 _ _).trans (hβ.2 _ _ _)
  have h2 : β (e a) (H.w0 • e b) + β (e a) (H.bar H.w0 • e b) = β (e a) (e b) := by
    rw [← map_add (f := _), ← add_smul, ReciprocityTheory.ChartRestriction.G.PullbackSections.CVA.cmHostUnit_add_conj_eq_one, one_smul]
  simp only [map_add (f := _), smul_add, LinearMap.add_apply]
  rw [h1]
  linarith

theorem main : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (Cn : Canon C), ∃ (ε' : Module.Basis (Fin C.m ⊕ Fin Cn.N) ℤ (balForms H.bar C.P.D.toPre.X)) (τ₀ : Gens C.P.D.toPre), (∀ k, (ε' k : LinearMap.BilinForm ℤ C.P.D.toPre.X) = pull Cn.e.toLinearMap (Cn.ε k : LinearMap.BilinForm ℤ Cn.L.D.X)) ∧ FromBase C.P.D.toPre τ₀ (Cn.ψ.comp MvPolynomial.C) ∧ TauIn C.P.D.toPre τ₀ (fun k => Cn.ψ (MvPolynomial.X (finSumFinEquiv.symm k))) (fun k => (l.M' : ℤ) • (ε' (finSumFinEquiv.symm k) : LinearMap.BilinForm ℤ C.P.D.toPre.X)) := by
  intro E _ _ _ H Dw l Xo c φ R _ _ _ hR C Cn
  classical
  obtain ⟨g, hD, hg, -, -⟩ := Cn.data
  have hinj := comp_C_injective Cn.ψ Cn.compl.2.2.1 Cn.ψ_loc
  obtain ⟨-, hb, hU, -⟩ := letI := H.starRing
    GlobalTheory.T.degenerationDataNsmulRescale_keeps_laws Cn.L.W Cn.L.D (𝓞 E) Cn.L.oa H.w0 l.M' Cn.L.even Cn.L.bimult Cn.L.w0 Cn.L.gen
  obtain ⟨τ₁, hτ, hF⟩ := GlobalTheory.UTautData.gens_fromBase _ hinj _ _ hD hb hU
  refine ⟨Cn.ε.map (pullBalEquiv H.bar Cn.e), τ₁, fun k => rfl, hF, fun a b => ?_⟩
  have hs : ∀ k, algebraMap R (FractionRing R) (Cn.ψ (MvPolynomial.X k)) ≠ 0 := by
    intro k
    refine (map_ne_zero_iff _ (IsFractionRing.injective R _)).2 ?_
    rcases k with i | k
    · rw [Cn.bd i]; exact C.s_ne_zero i
    · exact (Cn.tor k).ne_zero
  refine ⟨(hτ a b).1, g a * g b * (g (a + b))⁻¹, ?_, fun z J hJ => ?_⟩
  · have hsplit := prod_zpow_add _ hs
      (fun k => (l.M' : ℤ) * (Cn.ε k : LinearMap.BilinForm ℤ Cn.L.D.X) (Cn.e (a + b)) (H.w0 • Cn.e (a + b)))
      (fun k => (l.M' : ℤ) * (Cn.ε k : LinearMap.BilinForm ℤ Cn.L.D.X) (Cn.e a) (H.w0 • Cn.e a))
      (fun k => (l.M' : ℤ) * (Cn.ε k : LinearMap.BilinForm ℤ Cn.L.D.X) (Cn.e b) (H.w0 • Cn.e b))
      (fun k => (l.M' : ℤ) * (Cn.ε k : LinearMap.BilinForm ℤ Cn.L.D.X) (Cn.e a) (Cn.e b))
      (fun k => by simp only [second_diff H Cn.e (Cn.ε k).2 a b]; ring)
    have hne : ∀ y, (((g y)⁻¹ : (FractionRing R)ˣ) : FractionRing R) ≠ 0 := fun y => Units.ne_zero _
    have e1 : (((g a * g b * (g (a + b))⁻¹ : (FractionRing R)ˣ)) : FractionRing R) =
        (((g (a + b))⁻¹ : (FractionRing R)ˣ) : FractionRing R) * ((((g a)⁻¹ : (FractionRing R)ˣ) : FractionRing R))⁻¹ *
          ((((g b)⁻¹ : (FractionRing R)ˣ) : FractionRing R))⁻¹ := by
      simp only [Units.val_mul, Units.val_inv_eq_inv_val, inv_inv]; ring
    have hA := hne a
    have hB := hne b
    rw [hg a] at hA
    rw [hg b] at hB
    rw [e1, hg (a + b), hsplit, hg a, hg b]
    beta_reduce at hA hB ⊢
    have canc : ∀ T x y : FractionRing R, x ≠ 0 → y ≠ 0 → T * x * y * x⁻¹ * y⁻¹ = T := fun T x y hx hy => by
      field_simp
    rw [canc _ _ _ hA hB]
    refine Eq.trans ?_ (Equiv.prod_comp finSumFinEquiv.symm (fun k => algebraMap R (FractionRing R)
      (Cn.ψ (MvPolynomial.X k)) ^ (((l.M' : ℤ) • ((Cn.ε.map (pullBalEquiv H.bar Cn.e)) k :
        LinearMap.BilinForm ℤ C.P.D.toPre.X)) a b))).symm
    exact Finset.prod_congr rfl fun k _ => rfl
  · have h1 := GlobalTheory.TauTwist.val_tau_rescale (D := C.P.D.toPre) g (a := a) (b := b)
      (x := (g a * g b)⁻¹ * g (a + b)) (by group) (𝟙 _) hJ
    have h2 := (hτ a b).2 z J hJ
    have hx : g a * g b * (g (a + b))⁻¹ = ((g a * g b)⁻¹ * g (a + b))⁻¹ := by
      rw [mul_inv_rev, inv_inv, mul_comm]
    rw [hx]
    show _ = GlobalTheory.TauTwist.unitAt (𝟙 _) z _ * _
    rw [map_inv]
    exact eq_inv_mul_of_mul_eq (h1.symm.trans h2)

end GlobalTheory.UCanon.PerCoord
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalFamilyPeriodsInCoordinatesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.canonicalFamily_periods_in_coordinates : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (Cn : Canon C), ∃ (ε' : Module.Basis (Fin C.m ⊕ Fin Cn.N) ℤ (balForms H.bar C.P.D.toPre.X)) (τ₀ : Gens C.P.D.toPre), (∀ k, (ε' k : LinearMap.BilinForm ℤ C.P.D.toPre.X) = pull Cn.e.toLinearMap (Cn.ε k : LinearMap.BilinForm ℤ Cn.L.D.X)) ∧ FromBase C.P.D.toPre τ₀ (Cn.ψ.comp MvPolynomial.C) ∧ TauIn C.P.D.toPre τ₀ (fun k => Cn.ψ (MvPolynomial.X (finSumFinEquiv.symm k))) (fun k => (l.M' : ℤ) • (ε' (finSumFinEquiv.symm k) : LinearMap.BilinForm ℤ C.P.D.toPre.X)) := by
  first | exact @GlobalTheory.UCanon.PerCoord.main | exact GlobalTheory.UCanon.PerCoord.main | (intros; apply GlobalTheory.UCanon.PerCoord.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiInverseRootBundleSymmetric
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiInverseRootBundleSymmetric
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.QuasiInvPull

theorem root_symm : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A), IsUnit ((p : ℕ) : R) → (∃ e : ℕ, c = p ^ e) → IsAbelianScheme B → IsQuasiInv c ψ ψ' → ∀ P' : LB (G2 B).left, IsAxesTriv B P' → LBIso (o.P.pull (Hecke.sq2 ψ')) (Hecke.lbPow P' c) → LBIso (Hecke.lbPow o.P c) (P'.pull (Hecke.sq2 ψ)) → LBIso P' (P'.pull (lift (snd B B) (fst B B)).left) := by
  intro p _ D R _ b N c Y s o B _ _ ψ ψ' hp hc hB hq P' hP' _ H
  obtain ⟨e, rfl⟩ := hc
  have hpos : 0 < p ^ e := pow_pos (Fact.out : p.Prime).pos e
  have hunit : IsUnit (((p ^ e : ℕ)) : Γ(Y, ⊤)) := by
    have := (hp.pow e).map (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
    rwa [← Nat.cast_pow, map_natCast] at this
  obtain ⟨hL, r₁, r₂⟩ := hP'
  set sw' := (lift (snd B B) (fst B B)).left with hsw'
  set sw := (lift (snd o.A o.A) (fst o.A o.A)).left with hsw
  set q := Hecke.sq2 ψ with hqdef
  have hQ : (P'.pull sw').IsLB := pull_isLB hL sw'
  have ax : ∀ (e₁ e₂ : B ⟶ G2 B), e₁ ≫ lift (snd B B) (fst B B) = e₂ →
      (∃ t : (P'.pull e₂.left).Gen, t.IsGen) → ∃ t : ((P'.pull sw').pull e₁.left).Gen, t.IsGen := by
    intro e₁ e₂ he ⟨t, ht⟩
    have hc : ∀ k : PUnit, (fun _ : PUnit => e₁.left) k ≫ sw' = 𝟙 _ ≫ (fun _ : PUnit => e₂.left) k := by
      intro _
      rw [Category.id_comp, hsw', ← Over.comp_left, he]
    have iso : LBIso ((P'.pull sw').pull e₁.left) (P'.pull e₂.left) :=
      LBIso.chartPull (chartPullLinComb P' sw' (fun _ => e₁.left) (fun _ => e₂.left) (fun _ => 1) (𝟙 _) hc)
        (chartPullId _) (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hL _))
    exact GlobalTheory.RigidTranslate.gen_of_lbIso (pull_isLB hL _) (pull_isLB hQ _) iso.symm t ht
  have a₁ := ax (lift (1 : B ⟶ B) (𝟙 B)) (lift (𝟙 B) (1 : B ⟶ B)) (by ext <;> simp) r₂
  have a₂ := ax (lift (𝟙 B) (1 : B ⟶ B)) (lift (1 : B ⟶ B) (𝟙 B)) (by ext <;> simp) r₁
  have E := GlobalTheory.HeckeSym.grpSchemeSquareProductMap_comm_swap ψ
  have hPow : (Hecke.lbPow o.P (p ^ e)).IsLB := DVR.linComb_isLB _ o.isLB _ _
  have step1 : LBIso (Hecke.lbPow o.P (p ^ e))
      (LB.LinComb (o.P.pull sw) (K := Fin (p ^ e)) (fun _ => 𝟙 _) (fun _ => 1)) :=
    GlobalTheory.PowPrimitive.lbIso_linComb o.symm _ _
  have step2 : LBIso (LB.LinComb (o.P.pull sw) (K := Fin (p ^ e)) (fun _ => 𝟙 _) (fun _ => 1))
      ((P'.pull sw').pull q) := by
    refine LBIso.chartPull (h := sw)
      (chartPullLinComb o.P sw (fun _ => 𝟙 _) (fun _ => 𝟙 _) (fun _ => 1) sw (fun _ => by simp))
      (chartPullLinComb P' sw' (fun _ : PUnit => q) (fun _ : PUnit => q) (fun _ => 1) sw (fun _ => E)) H
  have hmid : (LB.LinComb (o.P.pull sw) (K := Fin (p ^ e)) (fun _ => 𝟙 _) (fun _ => 1)).IsLB :=
    DVR.linComb_isLB _ (pull_isLB o.isLB _) _ _
  have key : LBIso (P'.pull q) ((P'.pull sw').pull q) :=
    LBIso.trans (pull_isLB hL q) hPow (pull_isLB hQ q) H.symm
      (LBIso.trans hPow hmid (pull_isLB hQ q) step1 step2)
  exact lbIso_of_pullback_quasiInverseIsogeny_trivial_axes Y o.A B (p ^ e) ψ ψ' P' (P'.pull sw') hB hpos hunit hq ⟨hL, r₁, r₂⟩ ⟨hQ, a₁, a₂⟩ key

end GlobalTheory.QuasiInvPull
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiInverseRootBundleSymmetricStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasiInverse_root_bundle_symmetric : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A), IsUnit ((p : ℕ) : R) → (∃ e : ℕ, c = p ^ e) → IsAbelianScheme B → IsQuasiInv c ψ ψ' → ∀ P' : LB (G2 B).left, IsAxesTriv B P' → LBIso (o.P.pull (Hecke.sq2 ψ')) (Hecke.lbPow P' c) → LBIso (Hecke.lbPow o.P c) (P'.pull (Hecke.sq2 ψ)) → LBIso P' (P'.pull (lift (snd B B) (fst B B)).left) := by
  first | (exact @GlobalTheory.QuasiInvPull.root_symm) | (exact GlobalTheory.QuasiInvPull.root_symm) | (intros; apply GlobalTheory.QuasiInvPull.root_symm  <;> assumption)
end
end
