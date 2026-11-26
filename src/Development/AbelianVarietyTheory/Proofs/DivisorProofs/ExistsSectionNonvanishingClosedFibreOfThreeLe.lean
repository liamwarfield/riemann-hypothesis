module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExpandsAtSectionUniformised
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtTwoTorsionRationalPullbacks

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionExpansionWeightZeroCoefficient
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionExpansionWeightZeroCoefficient
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.LeadZero

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ZH.AdaptedSpan GlobalTheory.IntegralCombination GlobalTheory.PullbackValuation
open GlobalTheory.LN GlobalTheory.TorRef GlobalTheory.UU GlobalTheory.IntFam GlobalTheory.IntFam.TermLift _root_.Formalism.L2.Pj

theorem intGen_pow : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsIntegrallyClosed R → ∀ (D : DegPre R) (k : ℕ), 1 ≤ k →
    ∀ (α mu : D.X) (s : R),
    (∀ (ξ : Spec (CommRingCat.of (FractionRing R))) (J), Good D.P.L ξ J → GlobalTheory.IntFam.IntegralCharts D J →
      ∃ u : Rˣ, (val (GlobalTheory.UU.IntGen.multK D k mu α) (𝟙 _) ξ J).val ^ k = GlobalTheory.PeriodBalance.cst ξ (u * s)) →
    ∃ (u₀ : LB.Gen (LB.LinComb D.P.L (deltaφT D (α + k • mu) α (toUnit (𝟙_ _) ≫ D.c mu)) (DegPre.deltaε k))) (a : R),
      u₀.IsGen ∧ (∃ w : R, a ^ k = w * s) ∧ ∀ (u : LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D (FractionRing R) k α mu) (DegPre.deltaε k))), u.IsGen →
        LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (DegPre.zF D (FractionRing R)).left)
          (DegPre.famMult D (FractionRing R) k mu α) →
        ∀ (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D (FractionRing R)).left) (z : Z) (J), Good D.P.L z J →
          (val u r z J).val = gs r z ⊤ (scal (DegPre.BF D (FractionRing R)).hom a) *
            (val u₀ (r ≫ (toUnit (TF (R := R) (FractionRing R)) ▷ D.P.A).left) z J).val := by
  intro R _ _ _ hR D k hk α mu s hs
  obtain ⟨v, hv⟩ := exists_gen_of_local (V := R) D.P.L D.P.isLB (IntGen.basePts D (𝟙_ _) α mu) (IntGen.baseExp k)
  obtain ⟨u₀, hu₀, vu₀⟩ := IntGen.exists_genT D (𝟙_ _) (𝟙_ _) (toUnit _) k α mu v hv
  obtain ⟨r₁, r₂, h₁, h₂, hr⟩ := IntGen.multK_frac D k α mu v hv
  obtain ⟨a, ha, hak⟩ : ∃ a : R, r₁ = r₂ * a ∧ ∃ w : R, a ^ k = w * s := by
    have : IsProper D.P.A.hom := D.P.isAb.proper
    obtain ⟨ξ⟩ : Nonempty (Spec (CommRingCat.of (FractionRing R))) := ⟨⟨⊥, Ideal.isPrime_bot⟩⟩
    obtain ⟨J, hJ, hJc⟩ := GlobalTheory.PeriodBalance.exists_good_integral ξ D.P.isLB D.P.A.hom
    obtain ⟨u, hu⟩ := hs ξ J hJ hJc
    have e := hr _ (𝟙 _) ξ J hJ
    have hσ : 𝟙 (TK R).left ≫ (toUnit (TK R)).left = jK R := by
      rw [Category.id_comp]; exact Over.w (toUnit (TK R))
    obtain ⟨w, hw⟩ : ∃ w : Rˣ, (val v (𝟙 _ ≫ (toUnit (TK R)).left) ξ J).val = GlobalTheory.PeriodBalance.cst ξ w := by
      rw [hσ]
      refine GlobalTheory.PeriodBalance.unit_gm ξ _ (Set.mem_iInter.2 fun i => ?_) _
      obtain ⟨q, hq⟩ : ∃ q : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A, IntGen.basePts D (𝟙_ _) α mu i = q.left := by
        fin_cases i <;> exact ⟨_, rfl⟩
      have := hJc (IntGen.basePts D (𝟙_ _) α mu i) (by rw [hq]; exact Over.w q)
      exact this
    have g : ∀ c : R, gs (𝟙 (TK R).left ≫ jK R) ξ ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) =
        GlobalTheory.PeriodBalance.cst ξ c := fun c => by
      rw [Category.id_comp, gs_eq (jK R) ξ ⊤ trivial, GlobalTheory.PeriodBalance.cst_eq]; rfl
    rw [g, g, hw] at e
    have e2 : GlobalTheory.PeriodBalance.cst ξ (r₂ ^ k * ((u : R) * s)) = GlobalTheory.PeriodBalance.cst ξ ((r₁ * w) ^ k) := by
      rw [map_mul, map_pow, ← hu, ← mul_pow, e, map_pow, map_mul]
    have e3 := GlobalTheory.PeriodBalance.cst_injective ξ e2
    have e5 : r₁ ^ k = r₂ ^ k * ((u : R) * s * ((w⁻¹ : Rˣ) : R) ^ k) := by
      have hwk : ((w : R) * ((w⁻¹ : Rˣ) : R)) ^ k = 1 := by rw [Units.mul_inv, one_pow]
      linear_combination (-(((w⁻¹ : Rˣ) : R)) ^ k) * e3 - r₁ ^ k * hwk
    have := hR
    have inj := IsFractionRing.injective R (FractionRing R)
    have hr₂ : algebraMap R (FractionRing R) r₂ ≠ 0 := (map_ne_zero_iff _ inj).2 h₂
    have hr₂k : algebraMap R (FractionRing R) (r₂ ^ k) ≠ 0 := (map_ne_zero_iff _ inj).2 (pow_ne_zero _ h₂)
    have hx : (algebraMap R (FractionRing R) r₁ / algebraMap R (FractionRing R) r₂) ^ k =
        algebraMap R (FractionRing R) ((u : R) * s * ((w⁻¹ : Rˣ) : R) ^ k) := by
      rw [div_pow, ← map_pow, ← map_pow, e5, map_mul, mul_div_cancel_left₀ _ hr₂k]
    have hint : IsIntegral R (algebraMap R (FractionRing R) r₁ / algebraMap R (FractionRing R) r₂) :=
      IsIntegral.of_pow (by omega) (hx ▸ isIntegral_algebraMap)
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
    refine ⟨y, inj ?_, (u : R) * ((w⁻¹ : Rˣ) : R) ^ k, inj ?_⟩
    · rw [map_mul, hy, mul_div_cancel₀ _ hr₂]
    · rw [map_pow, hy, hx, mul_right_comm]
  refine ⟨u₀, a, hu₀, hak, fun u hu hc Z r z J hJ => ?_⟩
  have key : gs r z ⊤ (scal (DegPre.BF D (FractionRing R)).hom r₂) * (val u r z J).val =
      gs r z ⊤ (scal (DegPre.BF D (FractionRing R)).hom r₁) *
        (val u₀ (r ≫ (toUnit (TF (R := R) (FractionRing R)) ▷ D.P.A).left) z J).val := by
    let T' : Over (Spec (CommRingCat.of R)) := Over.mk (r ≫ (DegPre.BF D (FractionRing R)).hom)
    let ρ : T' ⟶ DegPre.BF D (FractionRing R) := Over.homMk r rfl
    let κ : T' ⟶ TK R := Over.homMk ((ρ ≫ fst _ _).left ≫ jFK (R := R) (FractionRing R))
      ((Category.assoc _ _ _).trans (Over.w (ρ ≫ fst _ _)))
    have e₁ := (gen_fe (D := D) (F := FractionRing R) GlobalTheory.globalFns_holds k mu α).2 u hu hc T' ρ z J hJ
    have e₂ := vu₀ T' (ρ ≫ toUnit (TF (R := R) (FractionRing R)) ▷ D.P.A) z J hJ
    have e₃ : val (DegPre.famMult D (FractionRing R) k mu α) (ρ ≫ fst _ _).left z J =
        val (IntGen.multK D k mu α) κ.left z J :=
      val_pull hJ _ _ _
    have e₄ := hr _ κ.left z J hJ
    have e₅ : κ.left ≫ jK R = r ≫ (DegPre.BF D (FractionRing R)).hom := Over.w κ
    have e₆ : κ.left ≫ (toUnit (TK R)).left =
        ((ρ ≫ toUnit (TF (R := R) (FractionRing R)) ▷ D.P.A) ≫ toUnit _).left :=
      congrArg (fun q => q.left) (toUnit_unique (κ ≫ toUnit (TK R)) _)
    have e₇ : (ρ ≫ toUnit (TF (R := R) (FractionRing R)) ▷ D.P.A) ≫ snd _ _ = ρ ≫ DegPre.prB D (FractionRing R) := by
      rw [Category.assoc, whiskerRight_snd]
    have g : ∀ c : R, gs r z ⊤ (scal (DegPre.BF D (FractionRing R)).hom c) =
        gs (r ≫ (DegPre.BF D (FractionRing R)).hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) := fun c =>
      gs_pull r (DegPre.BF D (FractionRing R)).hom z ⊤ trivial _
    rw [e₅, e₆] at e₄
    rw [e₃, uVal, ← Category.assoc, comp_cP] at e₁
    rw [e₇] at e₂
    rw [g, g]
    exact IntGen.frac_mul e₁ e₂ e₄
  have sm : scal (DegPre.BF D (FractionRing R)).hom (r₂ * a) =
      scal (DegPre.BF D (FractionRing R)).hom r₂ * scal (DegPre.BF D (FractionRing R)).hom a := by
    simp only [Out.scal, map_mul]
  rw [ha, sm, gs_mul r z ⊤ trivial, _root_.mul_assoc] at key
  exact (GlobalTheory.FieldChange.isUnit_scal D h₂ r z).mul_left_cancel key

theorem termLift_smul : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (k : ℕ) (α mu : D.X)
    (u₀ : LB.Gen (LB.LinComb D.P.L (deltaφT D (α + k • mu) α (toUnit (𝟙_ _) ≫ D.c mu)) (DegPre.deltaε k))) (a : R),
    u₀.IsGen → (∀ (u : LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D (FractionRing R) k α mu) (DegPre.deltaε k))), u.IsGen →
        LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (DegPre.zF D (FractionRing R)).left)
          (DegPre.famMult D (FractionRing R) k mu α) →
        ∀ (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D (FractionRing R)).left) (z : Z) (J), Good D.P.L z J →
          (val u r z J).val = gs r z ⊤ (scal (DegPre.BF D (FractionRing R)).hom a) *
            (val u₀ (r ≫ (toUnit (TF (R := R) (FractionRing R)) ▷ D.P.A).left) z J).val) →
    ∀ (σ : SecAb D k α) (Φ : Fam D (FractionRing R) k), Φ.s α = pullAb D (FractionRing R) k α σ →
      ∃ f : SecAb D k (α + k • mu), pullAb D (FractionRing R) k (α + k • mu) (a • f) = Φ.s (α + k • mu) := by
  intro R _ _ D k α mu u₀ a hu₀ hrel σ Φ hΦ
  have hL := D.P.isLB
  have hG : GlobalFnsSt := GlobalTheory.allSixLaws.1.globalFns
  obtain ⟨t, ht⟩ := exists_sec hL (formEq D k α mu)
    (pullMulSec σ (trB D mu).left (LB.pullGen D.P.L _ _ u₀ (gB D).left) (pullGen_isGen _ _ _ _ hu₀ _))
  refine ⟨(show SecAb D k (α + k • mu) from t), GlobalTheory.FieldBaseChange.sec_ext' hL fun y J hJ => ?_⟩
  obtain ⟨⟨u, hu, hc⟩, -⟩ := gen_fe (D := D) (F := FractionRing R) hG k mu α
  have e₁ := (secRel_iff hL _ _ _ _ _ _ _ _ _ u).1 (Φ.fe mu α u hu hc) _ (𝟙 _) y J hJ
  have e₂ := hrel u hu hc _ (𝟙 _) y J hJ
  rw [e₁, e₂, hΦ, sval_pullAb _ _ _ _ hJ, sval_pullAb _ _ _ _ hJ, GlobalTheory.FieldBaseChange.sval_smul' hJ,
    ht _ _ y J hJ]
  erw [sval_pullMulSec σ (trB D mu).left (LB.pullGen D.P.L _ _ u₀ (gB D).left) (pullGen_isGen _ _ _ _ hu₀ _)
    (𝟙 _ ≫ (DegPre.prB D (FractionRing R)).left) y hJ]
  rw [val_pull hJ, GlobalTheory.FieldBaseChange.gs_scal]
  have m₁ : (𝟙 _ ≫ (DegPre.prB D (FractionRing R)).left) ≫ (trB D mu).left =
      (𝟙 _ ≫ (DegPre.trF D (FractionRing R) mu).left) ≫ (DegPre.prB D (FractionRing R)).left := by
    rw [Category.id_comp, Category.id_comp, ← Over.comp_left, ← Over.comp_left, trF_prB]
  have m₂ : (𝟙 _ ≫ (DegPre.prB D (FractionRing R)).left) ≫ (gB D).left =
      𝟙 _ ≫ (toUnit (TF (R := R) (FractionRing R)) ▷ D.P.A).left := by
    rw [Category.id_comp, Category.id_comp, ← Over.comp_left, prB_gB]
  have m₃ : (𝟙 _ ≫ (DegPre.prB D (FractionRing R)).left) ≫ D.P.A.hom = 𝟙 _ ≫ (DegPre.BF D (FractionRing R)).hom := by
    rw [Category.assoc, Over.w]
  rw [m₁, m₂, m₃]
  ring

theorem vanMod_smul {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegPre R} {k : ℕ} {α : D.X}
    (c : R) (hc : c ∈ maximalIdeal R) (f : SecAb D k α) :
    VanMod (maximalIdeal R) (D := D) (k := k) (α := α) (c • f : SecAb D k α) 0 := fun j => by
  change ((fstG (maximalIdeal R) 0 D.P.A).left.app _).hom (Out.resTop _ (scal D.P.A.hom c) * f.f j) = 0
  rw [map_mul, GlobalTheory.ThickDiv.resTop_scal, GlobalTheory.ThickDiv.app_constFn_eq_zero _ 0 _ _ (by rwa [zero_add, pow_one]),
    zero_mul]


set_option maxHeartbeats 1000000 in
theorem exists_lead_members {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (hB : Base R)
    (D : DegData R (maximalIdeal R)) {k : ℕ} (hk : 1 ≤ k) (b : D.toPre.SecB k 0) :
    ∃ (Φ : Fam D.toPre (FractionRing R) k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α),
      (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε k) (Φ.s α)
        (D.toPre.famφB α) (DegPre.famε k) (f α) (DegPre.prB D.toPre (FractionRing R)).left
        (scal (DegPre.BF D.toPre (FractionRing R)).hom 1)) ∧
      f 0 = b ∧ ∀ α, α ≠ 0 → VanMod (maximalIdeal R) (f α) 0 := by
  classical
  have hR : IsIntegrallyClosed R := hB.1.2.2.1
  have hG := GlobalTheory.allSixLaws.1.globalFns
  have hcan : ∀ x y : D.toPre.X, k • x = k • y → x = y := fun x y h =>
    smul_right_injective D.toPre.X (show (k : ℤ) ≠ 0 by omega) (by simpa only [natCast_zsmul] using h)
  obtain ⟨Φ, hΦ, hΦ₀⟩ := UUA.exists_fam_rep (D := D.toPre) (F := FractionRing R) hG D.tau_bimult k 0
    (fun x y h => hcan x y (add_left_cancel h)) (pullAb D.toPre (FractionRing R) k 0 b)
  obtain ⟨r, hr⟩ := (GlobalTheory.PeriodFormCompare.exists_psiCoord_iff D.toPre 0).2 (GlobalTheory.PeriodFormCompare.psiIn_top D 0)
  have hu : IsUnit r := IsLocalRing.notMem_maximalIdeal.1
    (PsiCoordLocal.not_mem_of_coord (𝔭 := closedPoint R) isOpen_univ trivial
      (PsiCoordLocal.psiUnitOn_zero D.toPre D.tau_bimult) hr)
  have hf : ∀ α : D.toPre.X, ∃ f : SecAb D.toPre k α, pullAb D.toPre (FractionRing R) k α f = Φ.s α ∧
      (∀ h : α = 0, f = h ▸ b) ∧ (α ≠ 0 → VanMod (maximalIdeal R) (D := D.toPre) (k := k) (α := α) f 0) := fun α => by
    by_cases h0 : α = 0
    · subst h0
      exact ⟨b, hΦ.symm, fun _ => rfl, fun h => absurd rfl h⟩
    by_cases h1 : ∃ mu, 0 + k • mu = α
    · obtain ⟨mu, rfl⟩ := h1
      obtain ⟨r', hr'⟩ := (GlobalTheory.PeriodFormCompare.exists_psiCoord_iff D.toPre (0 + k • mu)).2
        (GlobalTheory.PeriodFormCompare.psiIn_top D _)
      have hm : r' ∈ maximalIdeal R := by
        obtain ⟨j, hj, h, e⟩ := hr'
        obtain ⟨s, hs, es⟩ := D.psi_pos _ h0 j ⊤ (isAffineOpen_top _) hj h
        obtain ⟨r'', hm, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ PsiCoordLocal.toOpen_top_bijective.2).1 hs
        have : r'' = r' := PsiCoordLocal.toOpen_top_bijective.1 (PsiCoordLocal.jK_app_inj ⊤ (es.trans e.symm))
        exact this ▸ hm
      have e : r' = r * ((hu.unit⁻¹ : Rˣ) * r') := by rw [← _root_.mul_assoc, IsUnit.mul_val_inv, _root_.one_mul]
      rw [e] at hr'
      obtain ⟨u₀, c, hu₀, ⟨w, hw⟩, hrel⟩ := intGen_pow R hR D.toPre k hk 0 mu _
        (fun ξ J hJ hJc => GlobalTheory.IntFam.CoordPow.main R _ D k _ _ _ _ hr hr' ξ J hJ hJc)
      obtain ⟨f, hf⟩ := termLift_smul R D.toPre k 0 mu u₀ c hu₀ hrel b Φ hΦ
      have hc : c ∈ maximalIdeal R := Ideal.IsPrime.mem_of_pow_mem inferInstance k
        (hw ▸ Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ hm))
      exact ⟨_, hf, fun h => absurd h h0, fun _ => vanMod_smul c hc f⟩
    · refine ⟨0, ?_, fun h => absurd h h0, fun _ j => map_zero _⟩
      rw [map_zero]
      exact SecOps.sec_ext fun j => (hΦ₀ α (fun mu h => h1 ⟨mu, h⟩) j).symm
  choose f hfK hf₁ hf₀ using hf
  refine ⟨Φ, f, fun α => ?_, hf₁ 0 rfl, hf₀⟩
  refine (secScal_iff_pullAb D.toPre _ (famAt D.toPre _ k α Φ) (f α) 1).2 ?_
  rw [map_one, one_smul]
  exact hfK α

end GlobalTheory.Mum.LeadZero

namespace GlobalTheory.Mum.LeadZero

theorem exists_expandsAt_lead_zero : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R →
    ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G]
      [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ k : ℕ, 1 ≤ k →
      ∀ σ : D.toPre.SecB k 0, ∃ (s : H0 U.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α), f 0 = σ ∧
        (∀ α, α ≠ 0 → ∀ j : Fin 4 → D.toPre.P.L.ι, ((U.gt 0).pG.left.app _).hom ((f α).f j) = 0) ∧
        U.toUnifPre.ExpandsAt 0 k s f := by
  intro R _ _ _ hB D A G _ _ hG U k hk σ
  obtain ⟨Φ, f, hext, hf0, hvan⟩ := exists_lead_members hB D hk σ
  have hR : AdmBase R (maximalIdeal R) := hB.1
  have : IsNoetherianRing R := hR.1
  have := hG.geomConnected
  obtain ⟨s, ⟨r, hr, σ₀, f₀, -, hf₀, hE⟩, -⟩ := (U.expand k hk).2 Φ
  have h1 : scal (DegPre.BF D.toPre (FractionRing R)).hom (1 : R) = 1 := by
    rw [scal, map_one, map_one]
  have h₁ : ∀ α j, (f₀ α).f j = resTop _ (scal D.toPre.P.A.hom r) * (f α).f j := fun α =>
    GlobalTheory.IntegralExpansion.secIsMul_of_secScal D.toPre.P.isLB _
      (GlobalTheory.IntegralExpansion.prB_app_injective D.toPre) (h1 ▸ hext α)
      (by rw [Over.w (DegPre.prB D.toPre (FractionRing R))]; exact hf₀ α)
  obtain ⟨τ, hτ⟩ := GlobalTheory.sec_div_of_expandsAt R _ hR D A G U.toUnifPre k r hr σ₀ f₀ f h₁ hE
  refine ⟨τ, f, hf0, fun α hα j => (GlobalTheory.ExtDiv.pG_app_eq_zero_iff (U.gt 0) _ _).2 (hvan α hα j), ?_⟩
  exact GlobalTheory.expandsAt_cancel_of_ne_zero R _ D A G U.toUnifPre k r hr τ σ₀ f f₀ hτ h₁ hE 0

end GlobalTheory.Mum.LeadZero
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionExpansionWeightZeroCoefficientStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_expansion_weightZero_coefficient : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R →
    ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G]
      [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ k : ℕ, 1 ≤ k →
      ∀ σ : D.toPre.SecB k 0, ∃ (s : H0 U.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α), f 0 = σ ∧
        (∀ α, α ≠ 0 → ∀ j : Fin 4 → D.toPre.P.L.ι, ((U.gt 0).pG.left.app _).hom ((f α).f j) = 0) ∧
        U.toUnifPre.ExpandsAt 0 k s f := by
  first | exact @GlobalTheory.Mum.LeadZero.exists_expandsAt_lead_zero | exact GlobalTheory.Mum.LeadZero.exists_expandsAt_lead_zero | (intros; apply GlobalTheory.Mum.LeadZero.exists_expandsAt_lead_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightZeroSectionNotVanishingClosedFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightZeroSectionNotVanishingClosedFibre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1 ReciprocityTheory.ChartRestriction.G.H1.SquareUnits ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic

noncomputable section

namespace GlobalTheory.Mum.SecBZeroBpf

theorem unitAt_pow {S : Scheme.{0}} [IsLocallyNoetherian S] (hL : Laws) (P : PolAV S) {K : Type} [Field K]
    [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S) (x : Over.mk t ⟶ P.A) (m : ℕ) :
    UnitAt P.L ![(translPt P.A (1 : Over.mk t ⟶ P.A)).left, (snd (Over.mk t) P.A).left] ![1, (m : ℤ) + 1]
      ((ptSecT P.A x).left (IsLocalRing.closedPoint K)) := by
  have := P.isAb.smooth
  have := P.isAb.geomConnected
  have : GeometricallyIntegral P.A.hom := GlobalTheory.geometricallyIntegral_of_smooth _
  have : AlgebraicGeometry.IsIntegral (Over.mk t ⊗ P.A).left :=
    GeometricallyIntegral.geometrically_isIntegral t _ _ (IsPullback.of_hasPullback t P.A.hom).flip
  have : Subsingleton (Over.mk t).left := ⟨spec_pt_eq (k := K)⟩
  have : Nontrivial Γ((Over.mk t).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  have h1 := GlobalTheory.ThetaRep.finrank_secM hL.secBaseChange P (n := 1) le_rfl t
  rw [one_pow] at h1
  have : Nontrivial (SecM P.A P.L (1 : ℕ) (Over.mk t)) := Module.nontrivial_of_finrank_pos (h1 ▸ Nat.one_pos)
  obtain ⟨f, hf⟩ := exists_ne (0 : SecM P.A P.L (1 : ℕ) (Over.mk t))
  let θ : LB.Sec (LPow P.A P.L 1 (Over.mk t)) := SecM.toSec P.A f
  obtain ⟨k, hk⟩ : ∃ k, θ.f k ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf (Subtype.ext (funext h))
  have hD : (((Over.mk t ⊗ P.A).left.basicOpen (θ.f k) : (Over.mk t ⊗ P.A).left.Opens) :
      Set (Over.mk t ⊗ P.A).left).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h
    exact hk ((basicOpen_eq_bot_iff _).1 (SetLike.coe_injective h))
  let p : (Over.mk t).left := IsLocalRing.closedPoint K
  let y := (ptSecT P.A x).left p
  have good : ∀ a : Over.mk t ⟶ P.A, (ptSecT P.A (a * x)).left p ∈ (Over.mk t ⊗ P.A).left.basicOpen (θ.f k) →
      UnitAt P.L (K := Fin 1) (fun _ => (translPt P.A a).left) (fun _ => 1) y := fun a ha =>
    GlobalTheory.NoBasePoint.unitAt_transl P.isLB θ k a y (by
      rw [← GlobalTheory.NoBasePoint.ptSecT_translT] at ha
      exact ha)
  have step : ∀ (m : ℤ) (b a : Over.mk t ⟶ P.A),
      UnitAt P.L ![(translPt P.A b).left, (snd (Over.mk t) P.A).left] ![1, m] y →
      UnitAt P.L (K := Fin 1) (fun _ => (translPt P.A a).left) (fun _ => 1) y →
      UnitAt P.L ![(translPt P.A (b * a)).left, (snd (Over.mk t) P.A).left] ![1, m + 1] y := by
    intro m b a hb ha
    obtain ⟨V, hV, c, hc⟩ := hL.square S P (Over.mk t) b a p
    refine UnitAt.congr P.isLB (formEq_of_add fun U _ hh => ?_)
      ((hb.mul ha).mul (GlobalTheory.NoBasePoint.unitAt_of_local P.isLB _ _ p V hV c hc y))
    simp [Fin.sum_univ_succ]
    module
  have main : ∀ (m : ℕ) (b : Over.mk t ⟶ P.A),
      UnitAt P.L ![(translPt P.A b).left, (snd (Over.mk t) P.A).left] ![1, (m : ℤ) + 1] y := by
    intro m
    induction m with
    | zero =>
      intro b
      obtain ⟨a, h₁, h₂⟩ := GlobalTheory.NoBasePoint.exists_two_points t _ hD x (b * x)
      have := step 0 a (a⁻¹ * b) (UnitAt.congr P.isLB (formEq_of_add fun U _ hh => by simp) (good a (h₁ p)))
        (good _ (by rw [_root_.mul_assoc]; exact h₂ p))
      rwa [mul_inv_cancel_left] at this
    | succ m ih =>
      intro b
      obtain ⟨a, h₁, -⟩ := GlobalTheory.NoBasePoint.exists_two_points t _ hD x x
      have := step _ _ a (ih (b * a⁻¹)) (good a (h₁ p))
      rwa [inv_mul_cancel_right] at this
  exact main m 1

theorem mem_basicOpen_of_isUnit {Y Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (U : Y.Opens) (hz : r z ∈ U) (a : Γ(Y, U))
    (h : IsUnit (gs r z U a)) : r z ∈ Y.basicOpen a := by
  rw [gs_eq r z U hz] at h
  exact (SetLike.ext_iff.1 (Scheme.preimage_basicOpen r a) z).2 ((Z.mem_basicOpen _ z hz).2 h)

theorem c_zero {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) : D.c 0 = η[D.P.A] := by
  have h := D.c_add 0 0
  rw [add_zero] at h
  have h' : D.c 0 * D.c 0 = D.c 0 := h.symm
  rw [mul_eq_left] at h'
  rw [h']
  show toUnit _ ≫ η[D.P.A] = η[D.P.A]
  rw [toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]

theorem _root_.GlobalTheory.Mum.exists_secB_zero_mem_basicOpen : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R →
    ∀ (D : DegData R (maximalIdeal R)) (k : ℕ), 2 ≤ k → ∀ x : D.toPre.P.A.left,
      D.toPre.P.A.hom x = closedPoint R →
      ∃ (σ : D.toPre.SecB k 0) (j : Fin 4 → D.toPre.P.L.ι), x ∈ D.toPre.P.A.left.basicOpen (σ.f j) := by
  intro R _ _ _ hB D k hk x hx
  haveI : IsNoetherianRing R := hB.1.1
  have hL : Laws := GlobalTheory.abelianSchemeLaws_all.1
  have hTW : DVR.TwistBCSpanStatement := DVR.twistBCSpan_of GlobalTheory.twistBaseChange
  let P := D.toPre.P
  let K := AlgebraicClosure (P.A.left.residueField x)
  let u : Spec (CommRingCat.of K) ⟶ P.A.left :=
    Spec.map (CommRingCat.ofHom (algebraMap (P.A.left.residueField x) K)) ≫ P.A.left.fromSpecResidueField x
  have hu : ∀ q, u q = x := fun q => (Scheme.Hom.comp_apply _ _ q).trans (Scheme.fromSpecResidueField_apply x _)
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (u ≫ P.A.hom)
  let f : R →+* K := φ.hom
  have hφ' : Spec.map (CommRingCat.ofHom f) = u ≫ P.A.hom := hφ
  have e2 : (u ≫ P.A.hom) (closedPoint K) = closedPoint R :=
    (Scheme.Hom.comp_apply _ _ _).trans ((congrArg _ (hu _)).trans hx)
  have e : (Spec.map (CommRingCat.ofHom f)) (closedPoint K) = closedPoint R := by rw [hφ']; exact e2
  have e3 : Ideal.comap f (maximalIdeal K) = maximalIdeal R := congrArg PrimeSpectrum.asIdeal e
  have hf : IsLocalHom f := ⟨fun a ha => by
    by_contra hna
    have h1 : a ∈ maximalIdeal R := (mem_maximalIdeal a).2 hna
    rw [← e3] at h1
    exact (mem_maximalIdeal _).1 h1 ha⟩
  let T : Over (Spec (CommRingCat.of R)) := Over.mk (Spec.map (CommRingCat.ofHom f))
  let xb : T ⟶ P.A := Over.homMk u hφ'.symm
  let y := (ptSecT P.A xb).left (closedPoint K)
  have hy : (snd T P.A).left y = x := by
    have e4 : ptSecT P.A xb ≫ snd T P.A = xb := lift_snd _ _
    have e5 := congrArg (fun q => q.left (closedPoint K)) e4
    simp only [Over.comp_left, Scheme.Hom.comp_apply] at e5
    exact e5.trans (hu _)
  have c0 := c_zero D.toPre
  have a0 : (snd T P.A).left ≫ D.toPre.famφB 0 0 = (snd T P.A).left := Category.comp_id _
  have a1 : (snd T P.A).left ≫ D.toPre.famφB 0 1 = (translPt P.A (1 : T ⟶ P.A)).left := by
    show (snd T P.A ≫ padd D.toPre.P.A (𝟙 D.toPre.P.A) (toUnit _ ≫ D.toPre.c 0)).left = _
    congr 1
    have e1 : snd T P.A ≫ padd D.toPre.P.A (𝟙 D.toPre.P.A) (toUnit _ ≫ D.toPre.c 0) =
        snd T P.A * (toUnit _ ≫ D.toPre.c 0) := by
      refine (MonObj.comp_mul (snd T P.A) (𝟙 _) (toUnit _ ≫ D.toPre.c 0)).trans ?_
      rw [Category.comp_id, ← Category.assoc, comp_toUnit]
    rw [e1, mul_comm, GlobalTheory.NoBasePoint.translPt_eq, c0, MonObj.comp_one]
    rfl
  have a2 : (snd T P.A).left ≫ D.toPre.famφB 0 2 = (T ⊗ P.A).hom ≫ (η[P.A]).left := by
    show (snd T P.A ≫ toUnit _ ≫ D.toPre.c 0).left = _
    rw [← Category.assoc, comp_toUnit, Over.comp_left, Over.toUnit_left, c0]
  have a3 : (snd T P.A).left ≫ D.toPre.famφB 0 3 = (T ⊗ P.A).hom ≫ (η[P.A]).left := by
    show (snd T P.A ≫ toUnit _ ≫ η[D.toPre.P.A]).left = _
    rw [← Category.assoc, comp_toUnit, Over.comp_left, Over.toUnit_left]
  obtain ⟨σ, hσ⟩ : UnitAt P.L (fun i => (snd T P.A).left ≫ D.toPre.famφB 0 i) (DegPre.famε k) y := by
    refine UnitAt.congr P.isLB (formEq_of_add fun U _ hh => ?_)
      (unitAt_pow hL P (Spec.map (CommRingCat.ofHom f)) xb (k - 2))
    rw [Fin.sum_univ_four, a0, a1, a2, a3, Fin.sum_univ_two]
    have hk' : ((k - 2 : ℕ) : ℤ) + 1 = (k : ℤ) - 1 := by omega
    simp only [DegPre.famε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, hk']
    abel
  obtain ⟨m, c', β, hβ⟩ := hTW R D.toPre k (by omega) 0 K f hf σ
  choose J hJ using fun ψ : (T ⊗ P.A).left ⟶ P.A.left => exists_chart P.isLB (ψ y)
  have hJ' : Good P.L y J := hJ
  have e6 := SectionScalarValuation.sval_lin (fun l => (fst T P.A).left.appTop.hom (c' l))
      (fun l => SectionArithmetic.pullSec (β l) (snd T P.A).left) (fun j => hβ j) (𝟙 _) y hJ'
  obtain ⟨i, -, hi⟩ := IsLocalRing.exists_of_isUnit_sum ((congrArg IsUnit e6).mp (hσ J hJ'))
  have hi' := isUnit_of_mul_isUnit_right hi
  rw [SectionArithmetic.sval_pullSec _ _ (𝟙 _) y hJ', Category.id_comp] at hi'
  rw [← hy]
  exact ⟨β i, _, mem_basicOpen_of_isUnit _ y _ (hJ'.mem _ _) _ hi'⟩

end GlobalTheory.Mum.SecBZeroBpf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightZeroSectionNotVanishingClosedFibreStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weightZero_section_not_vanishing_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R →
    ∀ (D : DegData R (maximalIdeal R)) (k : ℕ), 2 ≤ k → ∀ x : D.toPre.P.A.left,
      D.toPre.P.A.hom x = closedPoint R →
      ∃ (σ : D.toPre.SecB k 0) (j : Fin 4 → D.toPre.P.L.ι), x ∈ D.toPre.P.A.left.basicOpen (σ.f j) := by
  first | exact @GlobalTheory.Mum.exists_secB_zero_mem_basicOpen | exact GlobalTheory.Mum.exists_secB_zero_mem_basicOpen | (intros; apply GlobalTheory.Mum.exists_secB_zero_mem_basicOpen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionNonvanishingClosedFibreOfThreeLe
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.ClosedFibreBpf

theorem thick_zero_apply (R : Type) [CommRing R] [IsLocalRing R]
    (z : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (0 + 1)))) :
    thick R (maximalIdeal R) 0 z = closedPoint R := by
  show (Spec.map _).base z = _
  rw [Spec.map_base]
  apply PrimeSpectrum.ext
  show Ideal.comap _ z.asIdeal = maximalIdeal R
  symm
  apply (IsLocalRing.maximalIdeal.isMaximal R).eq_of_le (by
    haveI := z.isPrime
    exact Ideal.IsPrime.ne_top inferInstance)
  intro a ha
  show _ ∈ z.asIdeal
  have : (Ideal.Quotient.mk (maximalIdeal R ^ (0 + 1))) a = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem]; simpa using ha
  rw [show (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal R ^ (0 + 1)))).hom a = 0 from this]
  exact z.asIdeal.zero_mem

theorem exists_sec_ne_zero_at : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ k : ℕ, 3 ≤ k → ∀ y : (thickObj R (maximalIdeal R) 0 G).left, ∃ (s : H0 U.LG.L k) (i : Fin 1 → U.LG.L.ι), y ∈ (thickObj R (maximalIdeal R) 0 G).left.basicOpen (((fstG (maximalIdeal R) 0 G).left.app (secChart U.LG.L i)).hom (s.f i)) := by
  intro R _ _ _ hB D A G _ _ hG U k hk y
  obtain ⟨σ, j, hx⟩ := GlobalTheory.T.exists_weightZero_section_not_vanishing_closedFibre R hB D k (by omega) ((U.gt 0).pG.left y) (by
    have h := congrArg (fun f => f.base y) (Over.w (U.gt 0).pG)
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h
    exact h.trans (thick_zero_apply R _))
  obtain ⟨s, f, hf0, hfα, hexp⟩ := GlobalTheory.T.exists_section_expansion_weightZero_coefficient R hB D A G hG U k (by omega) σ
  obtain ⟨i, hi⟩ := GlobalTheory.T.section_nonzero_of_expansion_mod_maximalIdeal R D A G U.toUnifPre k s f hexp hfα y ⟨j, by
    subst hf0
    rw [← Scheme.preimage_basicOpen]
    exact hx⟩
  exact ⟨s, i, hi⟩

end GlobalTheory.Mum.ClosedFibreBpf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionNonvanishingClosedFibreOfThreeLeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_nonvanishing_closedFibre_of_three_le : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ k : ℕ, 3 ≤ k → ∀ y : (thickObj R (maximalIdeal R) 0 G).left, ∃ (s : H0 U.LG.L k) (i : Fin 1 → U.LG.L.ι), y ∈ (thickObj R (maximalIdeal R) 0 G).left.basicOpen (((fstG (maximalIdeal R) 0 G).left.app (secChart U.LG.L i)).hom (s.f i)) := by
  first | exact @GlobalTheory.Mum.ClosedFibreBpf.exists_sec_ne_zero_at | exact GlobalTheory.Mum.ClosedFibreBpf.exists_sec_ne_zero_at | (intros; apply GlobalTheory.Mum.ClosedFibreBpf.exists_sec_ne_zero_at <;> assumption)
end
