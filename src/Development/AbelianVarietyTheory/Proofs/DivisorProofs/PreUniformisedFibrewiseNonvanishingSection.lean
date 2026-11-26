module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPreUniformisationEvenTorusCompleteNormal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionQuotientOfExpansionDvd

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDVRComparisonPreUniformised
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSettingOfEvenOn
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.TraitSetting

open GlobalTheory.UU GlobalTheory.LN


set_option maxHeartbeats 1000000 in
theorem exists_setting_of_evenOn (laws : Laws) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (P : CP G) (hS : IsSemiAbelian G) (hE : EvenOn P)
    (A : PolAV (Sp (FractionRing R))) (gen : (Over.pullback (jK R)).obj G ≅ A.A) [IsMonHom gen.hom]
    (hA : LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))))
    {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (hV : CDvr V) (φ : R →+* V) (hφ : Function.Injective φ)
    (hI : maximalIdeal R ≤ (maximalIdeal V).comap φ) :
    ∃ (A' : PolAV (Sp (FractionRing V))) (s : HidaSetting V A' ((Over.pullback (spMap φ)).obj G)) (w : _),
      IsCPMap s.P P (spMap φ) (pullback.fst G.hom (spMap φ)) pullback.condition w := by
  obtain ⟨X, _, _, _, Q₀, P₀, hlev, hev⟩ := hE
  have hG' : IsSemiAbelian ((Over.pullback (spMap φ)).obj G) := IsSemiAbelian.pullback _ G hS
  obtain ⟨ψ, sq'⟩ := ClosedPol.exists_generic_square φ hφ
  obtain ⟨A', gen', hgen', hA'⟩ := ClosedPol.exists_fibre_pull laws sq' P.L.isLB A gen hA
  obtain ⟨P', wP, hP', H⟩ := exists_cp_pull _ _ (spMap φ) G ((Over.pullback (spMap φ)).obj G) _ _
    (toBase_mul_pullback G (spMap φ)) P
  rw [← hP'] at hA'
  obtain ⟨P₀', w₀, H₀⟩ := exists_isLevelCP (maximalIdeal V) 0 P'
  have le : maximalIdeal R ^ (0 + 1) ≤ (maximalIdeal V ^ (0 + 1)).comap φ := by
    rw [zero_add, pow_one, pow_one]; exact hI
  let b : R ⧸ maximalIdeal R ^ (0 + 1) →+* V ⧸ maximalIdeal V ^ (0 + 1) := Ideal.quotientMap _ φ le
  have sq : spMap b ≫ thick R (maximalIdeal R) 0 = thick V (maximalIdeal V) 0 ≫ spMap φ := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      Ideal.quotientMap_comp_mk]
  obtain ⟨wl, hl⟩ := hlev
  obtain ⟨F, pF, w₃, k₃⟩ := ClosedPol.exists_fourth (G := G) (G' := (Over.pullback (spMap φ)).obj G)
    (H := thickObj R (maximalIdeal R) 0 G)
    (H' := thickObj V (maximalIdeal V) 0 ((Over.pullback (spMap φ)).obj G)) (P := P) (P' := P')
    (N := P₀) (N' := P₀') sq (isGrpPullback_pullback G (spMap φ))
    (isGrpPullback_pullback G (thick R (maximalIdeal R) 0))
    (isGrpPullback_pullback _ (thick V (maximalIdeal V) 0)) H hl H₀
  have := hS.smooth
  have := hS.geomConnected
  have : Smooth (thickObj R (maximalIdeal R) 0 G).hom := by
    show Smooth (pullback.snd _ _); infer_instance
  have : GeometricallyConnected (thickObj R (maximalIdeal R) 0 G).hom := by
    show GeometricallyConnected (pullback.snd _ _); infer_instance
  obtain ⟨D₀⟩ := TowerEx.nonempty_desc _ (TowerEx.isNilpotent_max 0) _ P₀ Q₀ hev
  obtain ⟨Q₀', D₀', -, -, -⟩ := ClosedPol.exists_desc_pull pF Q₀ D₀ k₃
  have ev := UniformizationSetting.exists_even_of_desc D₀'
  obtain ⟨wA, hwA⟩ := hA'
  exact ⟨A', ⟨hV, hG', gen', hgen', P', wA, hwA, _, Q₀', P₀', ⟨w₀, H₀⟩, ev⟩, wP, H⟩

end GlobalTheory.Mum.TraitSetting
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDVRComparisonPreUniformised
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.TraitCompare

open GlobalTheory.UU GlobalTheory.LN


set_option maxHeartbeats 1000000 in
theorem exists_cmp_under : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU (maximalIdeal R) D A G), EvenOn U.P → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (φ : R →+* V) (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (G' : Over (Sp V)) (_ : GrpObj G') (_ : IsCommMonObj G') (U' : GlobalTheory.UU.PreU (maximalIdeal V) D'.toPre A' G') (U₀ : Unif (maximalIdeal V) D' A' G') (F : G'.left ⟶ G.left) (_ : GlobalTheory.LN.Cmp φ U U' F), GlobalTheory.LN.CDvr V ∧ Function.Injective φ ∧ (maximalIdeal V).comap φ = maximalIdeal R ∧ GlobalTheory.LN.Under U' U₀.toUnifPre := by
  intro R _ _ _ hB D A G _ _ U hE
  obtain ⟨⟨hL, hL2, -, -, -⟩, -⟩ := GlobalTheory.lawsAndExpansions
  have hEg := GlobalTheory.LN.ega_holds
  have hU := GlobalTheory.uniformisation_dvr_unconditional
  have := hB.1.1
  have := hB.2
  obtain ⟨V, _, _, _, φ, hV, hφ, hc⟩ := GlobalTheory.PrimeUnif.exists_cdvr R (maximalIdeal R)
  have := hV.1
  have hBV : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hV.2.1⟩
  have hle : (maximalIdeal R).map φ ≤ maximalIdeal V := Ideal.map_le_iff_le_comap.2 hc.ge
  have := U.gen_hom
  obtain ⟨A', s, w, hw⟩ :=
    GlobalTheory.Mum.TraitSetting.exists_setting_of_evenOn hL U.P U.semi hE A U.gen ⟨U.wA, U.wA_gen⟩ hV φ hφ hc.ge
  obtain ⟨D', U₀, hLG, -, -⟩ := hU V A' _ s
  obtain ⟨U', hU'⟩ := (GlobalTheory.LN.PreForm.under_exists_and_expands hL hL2 V _ D' A' _ s.semi).1 U₀.toUnifPre
  have := s.semi.smooth
  obtain ⟨w', hw'⟩ := GlobalTheory.PrimeUnif.isCPMap_of_eq hL.globalFns s.gen s.P U'.P (hU'.2.1.trans hLG) hw
  obtain ⟨C, -⟩ := GlobalTheory.T.exists_compare_uniformisationData_pullback hL hL2 hEg R V _ _ hB.1 hBV (maximalIdeal.isMaximal V).ne_top φ hle D D'.toPre A A'
    G _ U U' _ (isGrpPullback_pullback G _) w' hw'
  exact ⟨V, _, _, _, φ, D', A', _, _, _, U', U₀, _, C, hV, hφ, hc, hU'⟩

end GlobalTheory.Mum.TraitCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDVRComparisonPreUniformisedStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_completeDVR_comparison_preUniformised : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU (maximalIdeal R) D A G), EvenOn U.P → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (φ : R →+* V) (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (G' : Over (Sp V)) (_ : GrpObj G') (_ : IsCommMonObj G') (U' : GlobalTheory.UU.PreU (maximalIdeal V) D'.toPre A' G') (U₀ : Unif (maximalIdeal V) D' A' G') (F : G'.left ⟶ G.left) (_ : GlobalTheory.LN.Cmp φ U U' F), GlobalTheory.LN.CDvr V ∧ Function.Injective φ ∧ (maximalIdeal V).comap φ = maximalIdeal R ∧ GlobalTheory.LN.Under U' U₀.toUnifPre := by
  first | exact @GlobalTheory.Mum.TraitCompare.exists_cmp_under | exact GlobalTheory.Mum.TraitCompare.exists_cmp_under | (intros; apply GlobalTheory.Mum.TraitCompare.exists_cmp_under <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoefficientDataOfNonzeroSection
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatedThetaCoefficientSection
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatedThetaCoefficientSection
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU GlobalTheory.LN GlobalTheory.PsiRing GlobalTheory.PsiCoef

namespace GlobalTheory.PsiCoefMk

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

theorem exists_twist (χ : D.X)
    (u : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (hu : u.IsGen)
    (th : SecBT D (𝟙_ _) 1 0) :
    ∃ g : SecBT D (𝟙_ _) 1 χ, ∀ (T : Over (Spec (CommRingCat.of R))) (y : T ⟶ D.P.A) (z : T.left) (J),
      Good D.P.L z J → sval g (lift (toUnit T) y).left z J =
        sval th (lift (toUnit T) (y * cT D T χ)).left z J * (val u (toUnit T).left z J * rigV D z J).val := by
  let Y : Over (Spec (CommRingCat.of R)) := 𝟙_ _ ⊗ D.P.A
  let τ : Y ⟶ Y := lift (toUnit Y) (snd _ _ * cT D Y χ)
  have hF : FormEq
      (Sum.elim (fun k => τ.left ≫ famφT D (𝟙_ _) 0 k)
        (fun k => (toUnit Y).left ≫ Sum.elim (fun _ : PUnit => (D.c χ).left) (fun _ : PUnit => eSec D.P.A) k))
      (Sum.elim (DegPre.famε 1) (Sum.elim (fun _ => -1) (fun _ => 1)))
      (famφT D (𝟙_ _) χ) (DegPre.famε 1) := by
    intro U _ h
    have e₁ : τ.left ≫ famφT D (𝟙_ _) 0 1 = famφT D (𝟙_ _) χ 1 := by
      change (τ ≫ (snd _ _ * cT D Y 0)).left = (snd _ _ * cT D Y χ).left
      rw [cT_zero, _root_.mul_one, lift_snd]
    have e₂ : τ.left ≫ famφT D (𝟙_ _) 0 2 = famφT D (𝟙_ _) χ 3 := by
      change (τ ≫ cT D Y 0).left = (1 : Y ⟶ D.P.A).left
      rw [comp_cT, cT_zero]
    have e₃ : τ.left ≫ famφT D (𝟙_ _) 0 3 = famφT D (𝟙_ _) χ 3 := by
      change (τ ≫ (1 : Y ⟶ D.P.A)).left = (1 : Y ⟶ D.P.A).left
      rw [MonObj.comp_one]
    have e₄ : (toUnit Y).left ≫ (D.c χ).left = famφT D (𝟙_ _) χ 2 := rfl
    have e₅ : (toUnit Y).left ≫ eSec D.P.A = famφT D (𝟙_ _) χ 3 := rfl
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, Fin.prod_univ_four,
      e₁, e₂, e₃, e₄, e₅]
    simp [DegPre.famε, _root_.mul_assoc]
  obtain ⟨g, hg⟩ := exists_sec D.P.isLB hF (pullMulSec th τ.left
    (LB.pullGen D.P.L _ _ (LB.mulGen D.P.L _ _ _ _ u D.rig) (toUnit Y).left)
    (DVR.pullGen_isGen _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ hu D.rig_gen) _))
  refine ⟨g, fun T y z J hJ => ?_⟩
  have e₂ : (lift (toUnit T) y).left ≫ τ.left = (lift (toUnit T) (y * cT D T χ)).left := by
    rw [← Over.comp_left]
    congr 1
    refine (comp_lift _ _ _).trans (congrArg₂ lift (toUnit_unique _ _) ?_)
    rw [MonObj.comp_mul, comp_cT, lift_snd]
  have e₃ : (lift (toUnit T) y).left ≫ (toUnit Y).left = (toUnit T).left := by
    rw [← Over.comp_left]
    exact congrArg _ (toUnit_unique _ _)
  rw [hg _ _ z J hJ, sval_pullMulSec _ _ _ _ _ _ hJ, e₂, val_pull hJ, e₃, val_mul hJ]
  congr 4

theorem exists_sec_coef : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (th : GlobalTheory.UU.SecBT D (𝟙_ _) 1 0) (χ : D.X) (u : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))), u.IsGen → ∀ b : R, ∃ g : GlobalTheory.UU.SecBT D (𝟙_ _) 1 χ, GlobalTheory.PsiRing.Coef D χ u th g b := by
  intro R _ _ _ D th χ u hu b
  obtain ⟨g, hg⟩ := exists_twist D χ u hu th
  refine ⟨GlobalTheory.IndivisibleSection.smulSec (scal (𝟙_ _ ⊗ D.P.A).hom b) g, fun T y z J hJ => ?_⟩
  have e₁ : (lift (toUnit T) y).left ≫ (𝟙_ _ ⊗ D.P.A).hom = T.hom := Over.w _
  have h := GlobalTheory.IndivisibleSection.sval_of_secIsMul (p := (𝟙_ _ ⊗ D.P.A).hom) (a := b)
    (s := GlobalTheory.IndivisibleSection.smulSec (scal (𝟙_ _ ⊗ D.P.A).hom b) g) (t := g) (fun _ => rfl)
    (lift (toUnit T) y).left z hJ
  rw [e₁, hg T y z J hJ] at h
  exact h.trans (by ring)

end GlobalTheory.PsiCoefMk
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatedThetaCoefficientSectionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_translatedThetaCoefficient_section : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (th : GlobalTheory.UU.SecBT D (𝟙_ _) 1 0) (χ : D.X) (u : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))), u.IsGen → ∀ b : R, ∃ g : GlobalTheory.UU.SecBT D (𝟙_ _) 1 χ, GlobalTheory.PsiRing.Coef D χ u th g b := by
  first | exact @GlobalTheory.PsiCoefMk.exists_sec_coef | exact GlobalTheory.PsiCoefMk.exists_sec_coef | (intros; apply GlobalTheory.PsiCoefMk.exists_sec_coef <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroExpansionTermCompleteDVR
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroExpansionTermCompleteDVR
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.ExpansionNonzero

theorem exists_term_ne_zero : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'] (U' : GlobalTheory.UU.PreU (maximalIdeal V) D'.toPre A' G') (U₀ : Unif (maximalIdeal V) D' A' G'), GlobalTheory.LN.Under U' U₀.toUnifPre → ∀ (σ' : U'.SecGT (𝟙_ _) 1) (f' : ∀ α, GlobalTheory.UU.SecBT D'.toPre (𝟙_ _) 1 α), U'.ExpT (𝟙_ _) 1 σ' f' → (∃ j, σ'.f j ≠ 0) → ∃ α j, (f' α).f j ≠ 0 := by
  intro V _ _ _ hV D' A' G' _ _ U' U₀ _ σ' f' hf ⟨j, hj⟩
  have := hV.1
  have := U'.semi.smooth
  have : IsReduced G'.left := isReduced_of_smooth_of_isReduced G'.hom
  have := FibreNonzero.isIso_snd_left G'
  have : IsReduced (𝟙_ _ ⊗ G').left := isReduced_of_isOpenImmersion (snd (𝟙_ _) G').left
  have h : (𝟙_ _ ⊗ G').left.basicOpen (σ'.f j) ≠ ⊥ := fun h => hj ((basicOpen_eq_bot_iff _).1 h)
  obtain ⟨y, hy⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 h
  refine GlobalTheory.SectionUnif.exists_term_ne_zero (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge U' 1 σ' f' hf y ?_
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, hy⟩

end GlobalTheory.ExpansionNonzero
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroExpansionTermCompleteDVRStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonzero_expansionTerm_completeDVR : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'] (U' : GlobalTheory.UU.PreU (maximalIdeal V) D'.toPre A' G') (U₀ : Unif (maximalIdeal V) D' A' G'), GlobalTheory.LN.Under U' U₀.toUnifPre → ∀ (σ' : U'.SecGT (𝟙_ _) 1) (f' : ∀ α, GlobalTheory.UU.SecBT D'.toPre (𝟙_ _) 1 α), U'.ExpT (𝟙_ _) 1 σ' f' → (∃ j, σ'.f j ≠ 0) → ∃ α j, (f' α).f j ≠ 0 := by
  first | exact @GlobalTheory.ExpansionNonzero.exists_term_ne_zero | exact GlobalTheory.ExpansionNonzero.exists_term_ne_zero | (intros; apply GlobalTheory.ExpansionNonzero.exists_term_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecIsMulOfBaseMultipleThetaSection
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecIsMulOfBaseMultipleThetaSection
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.PsiRing

theorem secIsMul_of_mult : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (th g : GlobalTheory.UU.SecBT D (𝟙_ _) 1 0) (b : R), GlobalTheory.PsiRing.Mult D th g b → ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul (𝟙_ _ ⊗ D.P.A).hom b g th := by
  intro R _ _ D th g b h
  refine GlobalTheory.IndivisibleSection.secIsMul_of_sval D.P.isLB fun y J hJ => ?_
  have e := h _ (𝟙 _) y J hJ
  rwa [Category.id_comp] at e

end GlobalTheory.PsiRing
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecIsMulOfBaseMultipleThetaSectionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.secIsMul_of_baseMultiple_thetaSection : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (th g : GlobalTheory.UU.SecBT D (𝟙_ _) 1 0) (b : R), GlobalTheory.PsiRing.Mult D th g b → ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul (𝟙_ _ ⊗ D.P.A).hom b g th := by
  first | exact @GlobalTheory.PsiRing.secIsMul_of_mult | exact GlobalTheory.PsiRing.secIsMul_of_mult | (intros; apply GlobalTheory.PsiRing.secIsMul_of_mult <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiScalarNsmulEqUnitMulPowSq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiScalarNsmulEqUnitMulPowSq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem evenCube_nsmul_pow {X U : Type*} [AddCommGroup X] [CommGroup U] (κ : X → U)
    (hneg : ∀ x, κ (-x) = κ x)
    (hcube : ∀ x y z, κ (x + y + z) * κ x * κ y * κ z = κ (x + y) * κ (x + z) * κ (y + z))
    (x : X) (n : ℕ) : κ (n • x) = κ x ^ (n ^ 2) := by
  have h0 : κ 0 = 1 := by
    have h := hcube 0 0 0
    simp only [add_zero] at h
    exact mul_eq_left.1 h
  have hpow : ∀ n : ℕ, κ (n • x) = κ x ^ (n ^ 2) ∧ κ ((n + 1) • x) = κ x ^ ((n + 1) ^ 2) := by
    intro n
    induction n with
    | zero => simp [h0]
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      have h := hcube ((n + 1) • x) x (-x)
      have e1 : (n + 1) • x + x + -x = (n + 1) • x := by abel
      have e2 : (n + 1) • x + x = (n + 1 + 1) • x := by rw [succ_nsmul _ (n + 1)]
      have e3 : (n + 1) • x + -x = n • x := by rw [succ_nsmul]; abel
      have e4 : x + -x = 0 := by abel
      rw [e1, e2, e3, e4, hneg, h0, ih.1, ih.2, _root_.mul_one] at h
      have hx : κ x ^ ((n + 1) ^ 2) * κ x ^ ((n + 1) ^ 2) * κ x * κ x
          = κ x ^ ((n + 1 + 1) ^ 2) * κ x ^ (n ^ 2) := by
        rw [← pow_add, ← pow_succ, ← pow_succ, ← pow_add]; congr 1; ring
      exact mul_right_cancel (h.symm.trans hx)
  exact (hpow n).1

theorem unitsQuot_eq_iff {R K : Type*} [CommRing R] [CommRing K] [Algebra R K] (p q : Kˣ) :
    QuotientGroup.mk' (Units.map (algebraMap R K).toMonoidHom).range p =
      QuotientGroup.mk' (Units.map (algebraMap R K).toMonoidHom).range q ↔
    ∃ u : Rˣ, (p : K) = algebraMap R K (u : R) * (q : K) := by
  rw [eq_comm, QuotientGroup.mk'_eq_mk']
  constructor
  · rintro ⟨_, ⟨u, rfl⟩, h⟩
    exact ⟨u, by rw [← h, mul_comm q]; rfl⟩
  · rintro ⟨u, h⟩
    exact ⟨_, ⟨u, rfl⟩, Units.ext (by rw [h, mul_comm q]; rfl)⟩

theorem psiScal_nsmul_eq_unit_mul_pow : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (a : D.X → (FractionRing R)ˣ), GlobalTheory.UU.PsiScal D ga a → D.PsiEven → D.TauBimult → ∀ (χ : D.X) (n : ℕ), ∃ u : Rˣ, ((a (n • χ) : (FractionRing R)ˣ) : FractionRing R) = algebraMap R (FractionRing R) (u : R) * ((a χ : (FractionRing R)ˣ) : FractionRing R) ^ (n ^ 2) := by
  intro R _ _ _ D ga a h hE hB χ n
  obtain ⟨hc, he⟩ := GlobalTheory.PsiScalUnit.main R D ga a h
  have key := evenCube_nsmul_pow
    (fun x => QuotientGroup.mk' (Units.map (algebraMap R (FractionRing R)).toMonoidHom).range (a x))
    (fun x => (unitsQuot_eq_iff _ _).2 (he hE x))
    (fun x y z => by
      have := (unitsQuot_eq_iff _ _).2 (hc hB x y z)
      simpa only [map_mul] using this) χ n
  obtain ⟨u, hu⟩ := (unitsQuot_eq_iff (R := R) _ _).1 (key.trans (map_pow _ _ _).symm)
  exact ⟨u, hu.trans (by rw [Units.val_pow_eq_pow_val])⟩

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiScalarNsmulEqUnitMulPowSqStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psiScalar_nsmul_eq_unit_mul_pow_sq : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (a : D.X → (FractionRing R)ˣ), GlobalTheory.UU.PsiScal D ga a → D.PsiEven → D.TauBimult → ∀ (χ : D.X) (n : ℕ), ∃ u : Rˣ, ((a (n • χ) : (FractionRing R)ˣ) : FractionRing R) = algebraMap R (FractionRing R) (u : R) * ((a χ : (FractionRing R)ˣ) : FractionRing R) ^ (n ^ 2) := by
  first | exact @GlobalTheory.Mum.psiScal_nsmul_eq_unit_mul_pow | exact GlobalTheory.Mum.psiScal_nsmul_eq_unit_mul_pow | (intros; apply GlobalTheory.Mum.psiScal_nsmul_eq_unit_mul_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecIsMulOfTranslatedThetaCoefficientProportional
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecIsMulOfTranslatedThetaCoefficientProportional
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.PsiRing

theorem secIsMul_of_coef : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (χ : D.X) (u : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (th : GlobalTheory.UU.SecBT D (𝟙_ _) 1 0) (g₁ g₂ : GlobalTheory.UU.SecBT D (𝟙_ _) 1 χ) (b₁ b₂ q : R), GlobalTheory.PsiRing.Coef D χ u th g₁ b₁ → GlobalTheory.PsiRing.Coef D χ u th g₂ b₂ → b₁ = q * b₂ → ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul (𝟙_ _ ⊗ D.P.A).hom q g₁ g₂ := by
  intro R _ _ D χ u th g₁ g₂ b₁ b₂ q h₁ h₂ hb
  refine GlobalTheory.IndivisibleSection.secIsMul_of_sval D.P.isLB fun y J hJ => ?_
  have e : lift (toUnit (𝟙_ _ ⊗ D.P.A)) (snd (𝟙_ _) D.P.A) = 𝟙 _ := by
    rw [toUnit_unique (toUnit _) (fst (𝟙_ _) D.P.A), lift_fst_snd]
  have e₁ := h₁ (𝟙_ _ ⊗ D.P.A) (snd _ _) y J hJ
  have e₂ := h₂ (𝟙_ _ ⊗ D.P.A) (snd _ _) y J hJ
  rw [e] at e₁ e₂
  refine e₁.trans (Eq.trans ?_ (congrArg (_ * ·) e₂.symm))
  rw [hb, GlobalTheory.IndivisibleSection.cst_mul', _root_.mul_assoc]

end GlobalTheory.PsiRing
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecIsMulOfTranslatedThetaCoefficientProportionalStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.secIsMul_of_translatedThetaCoefficient_proportional : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (χ : D.X) (u : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (th : GlobalTheory.UU.SecBT D (𝟙_ _) 1 0) (g₁ g₂ : GlobalTheory.UU.SecBT D (𝟙_ _) 1 χ) (b₁ b₂ q : R), GlobalTheory.PsiRing.Coef D χ u th g₁ b₁ → GlobalTheory.PsiRing.Coef D χ u th g₂ b₂ → b₁ = q * b₂ → ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul (𝟙_ _ ⊗ D.P.A).hom q g₁ g₂ := by
  first | exact @GlobalTheory.PsiRing.secIsMul_of_coef | exact GlobalTheory.PsiRing.secIsMul_of_coef | (intros; apply GlobalTheory.PsiRing.secIsMul_of_coef <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackNonzeroSectionInjectiveDomainMap
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackNonzeroSectionInjectiveDomainMap
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.PullNonzero

theorem eq_zero_of_dominant {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {ψ : K → (Y ⟶ X)}
    {ε : K → ℤ} (s : LB.Sec (LB.LinComb L ψ ε)) (h : Y' ⟶ Y) [IsSchemeTheoreticallyDominant h] [QuasiCompact h]
    (h0 : ∀ y J, Good L y J → sval s h y J = 0) (j : K → L.ι) : s.f j = 0 := by
  refine h.app_injective (LB.wchart L ψ j) (Eq.trans ?_ (map_zero (h.app (LB.wchart L ψ j)).hom).symm)
  refine fn_ext fun y hy => ?_
  choose I hI using fun χ : Y' ⟶ X => exists_chart hL (χ y)
  have e₁ := gs_pull (𝟙 Y') h y (LB.wchart L ψ j) hy (s.f j)
  rw [Category.id_comp] at e₁
  have e₂ := sec_trans s h y (j := j) hy (Good.mem hI ψ h)
  have e₃ : gs h y _ _ = 0 := h0 y I hI
  rw [e₃, MulZeroClass.mul_zero] at e₂
  refine (e₁.trans e₂).trans ?_
  rw [gs_eq _ y _ hy, map_zero, map_zero]

theorem sval_zero {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {ψ : K → (Y ⟶ X)}
    {ε : K → ℤ} (s : LB.Sec (LB.LinComb L ψ ε)) (h0 : ∀ j, s.f j = 0) (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    sval s r z J = 0 := by
  refine (congrArg (gs r z (LB.wchart L ψ (fun k => J (r ≫ ψ k)))) (h0 _)).trans ((gs_eq r z _ (hJ.mem ψ r) _).trans ?_)
  exact (congrArg _ (map_zero _)).trans (map_zero _)

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU (maximalIdeal R) D A G) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (φ : R →+* V) (D' : DegPre V) (A' : PolAV (Sp (FractionRing V))) (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'] (U' : GlobalTheory.UU.PreU (maximalIdeal V) D' A' G') (F : G'.left ⟶ G.left) (C : GlobalTheory.LN.Cmp φ U U' F), GlobalTheory.LN.CDvr V → Function.Injective φ → ∀ (σ : U.SecGT (𝟙_ _) 1) (σ' : U'.SecGT (𝟙_ _) 1), (∀ (Z : Scheme.{0}) (r' : Z ⟶ (𝟙_ _ ⊗ G').left) (r : Z ⟶ (𝟙_ _ ⊗ G).left), r ≫ (snd _ G).left = r' ≫ (snd _ G').left ≫ F → ∀ z J J', Good U.P.L.L z J → Good U'.P.L.L z J' → sval σ r z J = (gw C.wL (r' ≫ (snd _ G').left) z (J (r ≫ (snd _ G).left)) (J' (r' ≫ (snd _ G').left))).val ^ 1 * sval σ' r' z J') → (∃ j, σ.f j ≠ 0) → ∃ j, σ'.f j ≠ 0 := by
  intro R _ _ _ _ D A G _ _ U V _ _ _ φ D' A' G' _ _ U' F C _ hφ σ σ' H ⟨j, hj⟩
  by_contra h0
  push Not at h0
  have hs := U.semi.smooth
  have : Flat G.hom := inferInstance
  have : IsDominant (spMap φ) := by
    refine ⟨?_⟩
    exact (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical φ).2
      (by rw [(RingHom.injective_iff_ker_eq_bot φ).1 hφ]; exact bot_le)
  have := IsSchemeTheoreticallyDominant.of_isDominant (spMap φ)
  have : IsSchemeTheoreticallyDominant F := IsSchemeTheoreticallyDominant.of_isPullback C.pb.1.flip
  have : QuasiCompact F := MorphismProperty.of_isPullback (P := @QuasiCompact) C.pb.1.flip inferInstance
  have e : ∀ {S : Scheme.{0}} (B : Over S), (λ_ B).inv.left ≫ (snd _ B).left = 𝟙 _ := fun B =>
    congrArg (fun q => q.left) (leftUnitor_inv_snd B)
  have : IsIso (λ_ G).inv.left := inferInstanceAs (IsIso ((Over.forget _).map (λ_ G).inv))
  refine hj (eq_zero_of_dominant U.P.L.isLB σ (F ≫ (λ_ G).inv.left) (fun y J hJ => ?_) j)
  choose J' hJ' using fun χ : G'.left ⟶ G'.left => exists_chart U'.P.L.isLB (χ y)
  have e₁ := H _ (λ_ G').inv.left (F ≫ (λ_ G).inv.left)
    (by rw [Category.assoc, e, ← Category.assoc, e, Category.id_comp, Category.comp_id]) y J J' hJ hJ'
  rw [sval_zero σ' h0 _ y hJ', MulZeroClass.mul_zero] at e₁
  exact e₁

end GlobalTheory.PullNonzero
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackNonzeroSectionInjectiveDomainMapStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_nonzero_section_injective_domain_map : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU (maximalIdeal R) D A G) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (φ : R →+* V) (D' : DegPre V) (A' : PolAV (Sp (FractionRing V))) (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'] (U' : GlobalTheory.UU.PreU (maximalIdeal V) D' A' G') (F : G'.left ⟶ G.left) (C : GlobalTheory.LN.Cmp φ U U' F), GlobalTheory.LN.CDvr V → Function.Injective φ → ∀ (σ : U.SecGT (𝟙_ _) 1) (σ' : U'.SecGT (𝟙_ _) 1), (∀ (Z : Scheme.{0}) (r' : Z ⟶ (𝟙_ _ ⊗ G').left) (r : Z ⟶ (𝟙_ _ ⊗ G).left), r ≫ (snd _ G).left = r' ≫ (snd _ G').left ≫ F → ∀ z J J', Good U.P.L.L z J → Good U'.P.L.L z J' → sval σ r z J = (gw C.wL (r' ≫ (snd _ G').left) z (J (r ≫ (snd _ G).left)) (J' (r' ≫ (snd _ G').left))).val ^ 1 * sval σ' r' z J') → (∃ j, σ.f j ≠ 0) → ∃ j, σ'.f j ≠ 0 := by
  first | exact @GlobalTheory.PullNonzero.main | exact GlobalTheory.PullNonzero.main | (intros; apply GlobalTheory.PullNonzero.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroSectionPreUniformisedCompleteNormal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroSectionPreUniformisedCompleteNormal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.ModelSection
open GlobalTheory.UU GlobalTheory.TwistLoc

theorem isUnit_gc {K : Type} [Field K] {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of K)) (z : Z) {c : K} (hc : c ≠ 0) :
    IsUnit (gc q z c) := by
  have h1 : gc q z (1 : K) = 1 := by
    unfold gc gs
    exact (dif_pos trivial).trans ((congrArg _ ((congrArg _ (map_one _)).trans (map_one _))).trans (map_one _))
  exact IsUnit.of_mul_eq_one (gc q z c⁻¹) (by rw [← gc_mul, mul_inv_cancel₀ hc, h1])

theorem exists_ne_zero {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) :
    ∃ σ : U.SecGT (𝟙_ _) 1, ∃ j, σ.f j ≠ 0 := by
  have h1 := GlobalTheory.abelianSchemeLaws_all.1
  have h2 := GlobalTheory.abelianSchemeLaws_all.2
  obtain ⟨v, hv⟩ := ThetaIntegral.exists_sec_ne_zero h1 h2 _ A (Kbar R) (jFK (R := R) (Kbar R))
  obtain ⟨n, c, a, ha⟩ := ExpTotal.exists_span h1.secBaseChange A 1 le_rfl (Kbar R) (jFK (R := R) (Kbar R))
    (SecM.toSec A.A v)
  choose d hd σ hσ using fun i => ExpTotal.exists_integral U 1 (a i)
  by_contra hn
  have hz : ∀ i j, (σ i).f j = 0 := fun i j => by
    by_contra h
    exact hn ⟨σ i, j, h⟩
  refine hv (Subtype.ext (funext fun j => ?_))
  refine sec_ext_val (L := A.L) (φ := fun _ : Fin 1 => (snd (TFK (R := R) (Kbar R)) A.A).left)
    (ε := fun _ => ((1 : ℕ) : ℤ)) A.isLB (s := SecM.toSec A.A v) (s' := SecM.toSec A.A 0) (fun z JA hJA => ?_) j
  obtain ⟨JG, hJG⟩ := exists_good_pt U.P.L.isLB z
  let y := (snd (TFK (R := R) (Kbar R)) A.A).left ≫ U.gen.inv.left
  let T : Over (Spec (CommRingCat.of R)) := Over.mk ((y ≫ pullback.fst G.hom (jK R)) ≫ G.hom)
  let x : T ⟶ G := Over.homMk (y ≫ pullback.fst G.hom (jK R)) rfl
  have hy : y ≫ U.gen.hom.left = 𝟙 _ ≫ (snd (TFK (R := R) (Kbar R)) A.A).left := by
    rw [Category.id_comp, Category.assoc, ← Over.comp_left, Iso.inv_hom_id, Over.id_left, Category.comp_id]
  refine (ha _ (𝟙 _) z JA hJA).trans (Eq.trans (Finset.sum_eq_zero fun i _ => ?_)
    (ThetaIntegral.sval_eq_zero _ (fun _ => rfl) _ _ _).symm)
  have e := hσ i _ y (lift (toUnit T) x).left (congrArg (fun q => q.left) (lift_snd (toUnit T) x)) z JA JG hJA hJG
  rw [ThetaIntegral.sval_eq_zero (σ i) (hz i)] at e
  have e₃ : y ≫ pullback.fst G.hom (jK R) ≫ G.hom = (y ≫ pullback.snd G.hom (jK R)) ≫ jK R :=
    (congrArg (y ≫ ·) pullback.condition).trans (Category.assoc _ _ _).symm
  have hu : IsUnit (gc (y ≫ pullback.fst G.hom (jK R) ≫ G.hom) z (d i)) := by
    have e₄ := (congrArg (gc · z (d i)) e₃).trans (ExpTotal.gc_map _ _ z _)
    exact e₄ ▸ isUnit_gc _ z ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 (hd i))
  have e₅ := hu.mul_right_eq_zero.1 e.symm
  rw [← Units.val_pow_eq_pow_val, Units.mul_right_eq_zero] at e₅
  have e₆ := (congrArg (fun q => sval (a i) q z JA) hy).symm.trans e₅
  exact (congrArg (_ * ·) e₆).trans (mul_zero _)

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU (maximalIdeal R) D A G), ∃ σ : U.SecGT (𝟙_ _) 1, ∃ j, σ.f j ≠ 0 :=
  fun _ _ _ _ _ _ _ _ _ _ U => exists_ne_zero U

end GlobalTheory.Mum.ModelSection
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroSectionPreUniformisedCompleteNormalStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonzero_section_preUniformised_completeNormal : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU (maximalIdeal R) D A G), ∃ σ : U.SecGT (𝟙_ _) 1, ∃ j, σ.f j ≠ 0 := by
  first | exact @GlobalTheory.Mum.ModelSection.main | exact GlobalTheory.Mum.ModelSection.main | (intros; apply GlobalTheory.Mum.ModelSection.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoefficientDataOfNonzeroSection
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum

theorem integral_of_sqPow_bdd (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (y : FractionRing R) (r : R) (hr : r ≠ 0)
    (h : ∀ n : ℕ, ∃ s : R, algebraMap R (FractionRing R) r * y ^ (n ^ 2) = algebraMap R _ s) :
    ∃ s : R, y = algebraMap R _ s := by
  set c : FractionRing R := algebraMap R (FractionRing R) r with hc
  have hc0 : c ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hr
  have hall : ∀ k : ℕ, ∃ s : R, c ^ 4 * y ^ k = algebraMap R _ s := by
    intro k
    obtain ⟨p, q, u, v, hk⟩ := Nat.sum_four_squares k
    obtain ⟨s1, h1⟩ := h p
    obtain ⟨s2, h2⟩ := h q
    obtain ⟨s3, h3⟩ := h u
    obtain ⟨s4, h4⟩ := h v
    refine ⟨s1 * s2 * s3 * s4, ?_⟩
    rw [← hk, map_mul, map_mul, map_mul, ← h1, ← h2, ← h3, ← h4, pow_add, pow_add, pow_add]
    ring
  let S : Subalgebra R (FractionRing R) := Algebra.adjoin R {y}
  have hle : Subalgebra.toSubmodule S ≤ Submodule.span R {(c ^ 4)⁻¹} := by
    show Subalgebra.toSubmodule (Algebra.adjoin R {y}) ≤ _
    rw [Algebra.adjoin_eq_span, Submodule.span_le]
    intro z hz
    obtain ⟨k, rfl⟩ := Submonoid.mem_closure_singleton.mp hz
    obtain ⟨s, hs⟩ := hall k
    have hc4 : c ^ 4 ≠ 0 := pow_ne_zero _ hc0
    have : y ^ k = s • (c ^ 4)⁻¹ := by
      rw [Algebra.smul_def, ← hs]; field_simp
    rw [SetLike.mem_coe, this]
    exact Submodule.smul_mem _ s (Submodule.mem_span_singleton_self _)
  have hfg : (Subalgebra.toSubmodule S).FG := by
    haveI := isNoetherian_of_fg_of_noetherian _ (Submodule.fg_span_singleton (R := R) ((c ^ 4)⁻¹ : FractionRing R))
    have h1 : ((Subalgebra.toSubmodule S).comap (Submodule.span R {(c ^ 4)⁻¹}).subtype).FG := IsNoetherian.noetherian _
    have h2 := h1.map (Submodule.span R {(c ^ 4)⁻¹}).subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.mpr hle] at h2
  have hint : IsIntegral R y := IsIntegral.of_mem_of_fg S hfg y (Algebra.self_mem_adjoin_singleton R y)
  obtain ⟨s, hs⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  exact ⟨s, hs.symm⟩

theorem exists_coefData_of_ne_zero : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU (maximalIdeal R) D A G) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (φ : R →+* V) (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'] (U' : GlobalTheory.UU.PreU (maximalIdeal V) D'.toPre A' G') (U₀ : Unif (maximalIdeal V) D' A' G') (F : G'.left ⟶ G.left), GlobalTheory.LN.Cmp φ U U' F → GlobalTheory.LN.CDvr V → Function.Injective φ → (maximalIdeal V).comap φ = maximalIdeal R → GlobalTheory.LN.Under U' U₀.toUnifPre → ∃ (σ : U.SecGT (𝟙_ _) 1) (f g : ∀ α, GlobalTheory.UU.SecBT D (𝟙_ _) 1 α) (q : R), q ≠ 0 ∧ U.ExpT (𝟙_ _) 1 σ f ∧ (∀ α, ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul (𝟙_ _ ⊗ D.P.A).hom q (f α) (g α)) ∧ GlobalTheory.PsiRing.FibNZ (𝟙_ _ ⊗ D.P.A).hom (g 0) ∧ ∀ α, α ≠ 0 → ∃ a ∈ maximalIdeal R, ∃ h : GlobalTheory.UU.SecBT D (𝟙_ _) 1 α, ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul (𝟙_ _ ⊗ D.P.A).hom a (g α) h := by

  intro R _ _ _ hB D A G _ _ U V _ _ _ φ D' A' G' _ _ U' U₀ F C hV hφ hI hU
  obtain ⟨⟨h₁, h₂, -, -, -⟩, -⟩ := GlobalTheory.lawsAndExpansions
  have hE := GlobalTheory.LN.ega_of_laws h₁ h₂
  have hR : AdmBase R (maximalIdeal R) := hB.1
  haveI : IsNoetherianRing R := hR.1
  haveI : IsIntegrallyClosed R := hR.2.2.1
  have hmR : maximalIdeal R ≠ ⊤ := (maximalIdeal.isMaximal R).ne_top
  have := hV.1
  have hV' : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hV.2.1⟩
  have hm : maximalIdeal V ≠ ⊤ := (maximalIdeal.isMaximal V).ne_top
  have hIm : (maximalIdeal R).map φ ≤ maximalIdeal V := Ideal.map_le_iff_le_comap.2 hI.ge
  obtain ⟨σ, hσ0⟩ := GlobalTheory.T.exists_nonzero_section_preUniformised_completeNormal R hB D A G U
  obtain ⟨f, hf, -⟩ := GlobalTheory.CompleteBaseExpansion.main h₁ h₂ hE R _ hR hmR D A G U 1 σ
  obtain ⟨σ', f', hf', hσσ, hff⟩ := GlobalTheory.ExpCmp.expT_cmp R V _ _ φ hIm D D'.toPre A A' G G' U U' F C 1 σ f hf
  have hcmp : GlobalTheory.PsiRing.SecCmp D D'.toPre C.β C.v C.xe f f' := hff
  have hrel' := GlobalTheory.T.psiRel_of_expT' h₁ h₂ V _ hV' D' A' G' U' U₀ hU σ' f' hf'
  have hσ'0 := GlobalTheory.T.pullback_nonzero_section_injective_domain_map R hB D A G U V φ D'.toPre A' G' U' F C hV hφ σ σ' hσσ hσ0
  have hne' : ∀ α, ∃ j, (f' α).f j ≠ 0 :=
    GlobalTheory.T.forall_term_ne_zero_of_psiRelation V D'.toPre f' hrel' (GlobalTheory.T.exists_nonzero_expansionTerm_completeDVR V hV D' A' G' U' U₀ hU σ' f' hf' hσ'0)
  have hne := GlobalTheory.PsiRing.ne_zero_of_secCmp C.pbB.1.w hcmp hne'
  obtain ⟨psi, h, hrel⟩ := GlobalTheory.exists_psi_psiRel h₁ h₂ R D f hne
  let E : DegPre R := GlobalTheory.LN.withPsi D psi h
  have hrelE : GlobalTheory.UU.PsiRel E (𝟙_ _) f := hrel
  have hrig : GlobalTheory.PsiRing.RigCmp φ E D'.toPre C.β C.v := GlobalTheory.T.rigidification_comparison_uniformisation R V _ _ φ hm hIm D D'.toPre A G A' G' U U' F C
  obtain ⟨gam, hgam⟩ := GlobalTheory.PsiRing.exists_generic_map hφ
  have hpsi : GlobalTheory.PsiRing.PsiCmp E D'.toPre C.β C.v C.xe gam :=
    GlobalTheory.T.psiCmp_of_secCmp' R V φ E D'.toPre C.β C.v C.xe C.pbB C.v_gen C.c_pr hrig f f' hcmp hrelE hrel' (hne' 0) gam hgam
  have hev : E.PsiEven :=
    GlobalTheory.T.psiEven_descend_baseChange h₁.globalFns R V φ E D'.toPre C.β C.v C.xe C.pbB C.v_gen C.c_pr gam hgam hpsi D'.psi_even
  have hbi : E.TauBimult :=
    GlobalTheory.T.tauBimult_of_baseChange' h₁.globalFns R V φ E D'.toPre C.β C.v C.xe C.pbB C.v_gen C.c_pr hrig gam hgam hpsi D'.tau_bimult
  obtain ⟨ga, a, hS⟩ := GlobalTheory.exists_psiScal R E
  obtain ⟨th, hth, hmul⟩ := GlobalTheory.T.exists_thetaSection_nonzeroFibres_localRing h₂.secTwist R D
  obtain ⟨q, hq⟩ := hmul (f 0)
  choose b hb using fun χ : D.X => GlobalTheory.T.exists_twistedSection_thetaTranslate_coef R D th hmul χ (ga χ) (hS χ).1 (f χ)
  have hab : ∀ χ, algebraMap R (FractionRing R) q * (a χ).val = algebraMap R (FractionRing R) (b χ) := fun χ =>
    GlobalTheory.T.psiScalar_eq_expansionCoef_ratio R E ga a f th hS hrelE hth χ q (b χ) hq (hb χ)
  have hq0 : q ≠ 0 := by
    rintro rfl
    obtain ⟨j, hj⟩ := hne 0
    apply hj
    rw [GlobalTheory.T.secIsMul_of_baseMultiple_thetaSection R D th (f 0) 0 hq j]
    simp [scal]
  have hint : ∀ χ, ∃ c : R, ((a χ : (FractionRing R)ˣ) : FractionRing R) = algebraMap R _ c := fun χ => by
    refine integral_of_sqPow_bdd R _ q hq0 fun n => ?_
    obtain ⟨u, hu⟩ := GlobalTheory.T.psiScalar_nsmul_eq_unit_mul_pow_sq R E ga a hS hev hbi χ n
    refine ⟨((u⁻¹ : Rˣ) : R) * b (n • χ), ?_⟩
    rw [map_mul, ← hab, hu]
    have hu1 : algebraMap R (FractionRing R) ((u⁻¹ : Rˣ) : R) * algebraMap R _ (u : R) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    linear_combination (-(algebraMap R (FractionRing R) q * ((a χ : (FractionRing R)ˣ) : FractionRing R) ^ (n ^ 2))) * hu1
  choose c hc using hint
  have hbc : ∀ χ, b χ = q * c χ := fun χ => by
    apply IsFractionRing.injective R (FractionRing R)
    exact (hab χ).symm.trans (by rw [map_mul, ← hc χ])
  have hcm : ∀ χ : D.X, χ ≠ 0 → c χ ∈ maximalIdeal R := fun χ hχ => by
    obtain ⟨x, rfl⟩ := C.xe.surjective χ
    obtain ⟨m, hm₁, hm₂⟩ := GlobalTheory.T.psiScalar_mem_of_psi_mem_ideal R V φ E D'.toPre C.β C.v C.xe C.pbB C.v_gen C.c_pr gam hgam hpsi ga a hS x _
      (D'.psi_pos x fun h0 => hχ (by rw [h0, map_zero])) _ q (hab _)
    have hm₃ : φ q * φ (c (C.xe x)) = φ q * m := by rw [← map_mul, ← hbc]; exact hm₂
    have hφq : φ q ≠ 0 := (map_ne_zero_iff _ hφ).2 hq0
    have e := mul_left_cancel₀ hφq hm₃
    have hmem : c (C.xe x) ∈ (maximalIdeal V).comap φ := Ideal.mem_comap.2 (by rw [e]; exact hm₁)
    exact (Set.ext_iff.1 (congrArg (fun J : Ideal R => (J : Set R)) hI) _).1 hmem
  choose G₁ hG₁ using fun χ : D.X => GlobalTheory.T.exists_translatedThetaCoefficient_section R D th χ (ga χ) (hS χ).1 (c χ)
  choose H₁ hH₁ using fun χ : D.X => GlobalTheory.T.exists_translatedThetaCoefficient_section R D th χ (ga χ) (hS χ).1 1
  classical
  let g : ∀ α, GlobalTheory.UU.SecBT D (𝟙_ _) 1 α := fun α => if h0 : α = 0 then h0 ▸ th else G₁ α
  refine ⟨σ, f, g, q, hq0, hf, fun α => ?_, ?_, fun α hα => ⟨c α, hcm α hα, H₁ α, ?_⟩⟩
  · by_cases h0 : α = 0
    · subst h0
      simp only [g, dif_pos rfl]
      exact GlobalTheory.T.secIsMul_of_baseMultiple_thetaSection R D th (f 0) q hq
    · simp only [g, dif_neg h0]
      exact GlobalTheory.T.secIsMul_of_translatedThetaCoefficient_proportional R D α (ga α) th (f α) (G₁ α) (b α) (c α) q (hb α) (hG₁ α) (hbc α)
  · simp only [g, dif_pos rfl]
    exact hth
  · simp only [g, dif_neg hα]
    exact GlobalTheory.T.secIsMul_of_translatedThetaCoefficient_proportional R D α (ga α) th (G₁ α) (H₁ α) (c α) 1 (c α) (hG₁ α) (hH₁ α) (_root_.mul_one _).symm

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoefficientDataOfNonzeroSectionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coefficientData_of_nonzero_section : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU (maximalIdeal R) D A G) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (φ : R →+* V) (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'] (U' : GlobalTheory.UU.PreU (maximalIdeal V) D'.toPre A' G') (U₀ : Unif (maximalIdeal V) D' A' G') (F : G'.left ⟶ G.left), GlobalTheory.LN.Cmp φ U U' F → GlobalTheory.LN.CDvr V → Function.Injective φ → (maximalIdeal V).comap φ = maximalIdeal R → GlobalTheory.LN.Under U' U₀.toUnifPre → ∃ (σ : U.SecGT (𝟙_ _) 1) (f g : ∀ α, GlobalTheory.UU.SecBT D (𝟙_ _) 1 α) (q : R), q ≠ 0 ∧ U.ExpT (𝟙_ _) 1 σ f ∧ (∀ α, ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul (𝟙_ _ ⊗ D.P.A).hom q (f α) (g α)) ∧ GlobalTheory.PsiRing.FibNZ (𝟙_ _ ⊗ D.P.A).hom (g 0) ∧ ∀ α, α ≠ 0 → ∃ a ∈ maximalIdeal R, ∃ h : GlobalTheory.UU.SecBT D (𝟙_ _) 1 α, ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul (𝟙_ _ ⊗ D.P.A).hom a (g α) h := by
  first | exact @GlobalTheory.Mum.exists_coefData_of_ne_zero | exact GlobalTheory.Mum.exists_coefData_of_ne_zero | (intros; apply GlobalTheory.Mum.exists_coefData_of_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemNonzeroLocusOfWeightZeroExpansion
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemNonzeroLocusOfWeightZeroExpansion
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.PreUTheta

theorem exists_mem_nonzeroLocus : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU (maximalIdeal R) D A G) (τ : U.SecGT (𝟙_ _) 1) (g : ∀ α, GlobalTheory.UU.SecBT D (𝟙_ _) 1 α), U.ExpT (𝟙_ _) 1 τ g → GlobalTheory.PsiRing.FibNZ (𝟙_ _ ⊗ D.P.A).hom (g 0) → (∀ α, α ≠ 0 → ∃ a ∈ maximalIdeal R, ∃ h : GlobalTheory.UU.SecBT D (𝟙_ _) 1 α, ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul (𝟙_ _ ⊗ D.P.A).hom a (g α) h) → ∃ θ : LB.Sec U.P.L.L, ∃ x ∈ nonzeroLocus θ, G.hom x = closedPoint R := by
  intro R _ _ _ D A G _ _ U τ g hE hnz hmul
  obtain ⟨z₀, hz₀, hn₀⟩ := hnz (closedPoint R)
  have hx : D.P.A.hom ((snd (𝟙_ (Over (Sp R))) D.P.A).left z₀) = closedPoint R :=
    (congrArg (fun q => q z₀) (Over.w (snd (𝟙_ (Over (Sp R))) D.P.A))).trans hz₀
  obtain ⟨y', hy'⟩ := GlobalTheory.ThetaUnit.exists_thick_pt le_rfl 0 D.P.A _ hx
  obtain ⟨y, rfl⟩ := (U.gt 0).q_surj.surj y'
  have hpG : (U.gt 0).pG.left y = (snd (𝟙_ (Over (Sp R))) D.P.A).left z₀ := hy'
  let rG : (thickObj R (maximalIdeal R) 0 G).left ⟶ (𝟙_ (Over (Sp R)) ⊗ G).left :=
    (lift (toUnit _) (fstG (maximalIdeal R) 0 G)).left
  let rB : (thickObj R (maximalIdeal R) 0 G).left ⟶ (𝟙_ (Over (Sp R)) ⊗ D.P.A).left :=
    (lift (toUnit _) (U.gt 0).pG).left
  have h₁ : rG ≫ (snd _ G).left = (fstG (maximalIdeal R) 0 G).left := by
    rw [← Over.comp_left, lift_snd]
  have h₂ : rB ≫ (snd _ D.P.A).left = (U.gt 0).pG.left := by
    rw [← Over.comp_left, lift_snd]
  have h₃ : rB ≫ (fst _ D.P.A).left = rG ≫ (fst _ G).left := by
    rw [← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst]
  have hinj : ∀ a b : (𝟙_ (Over (Sp R)) ⊗ D.P.A).left,
      (snd (𝟙_ (Over (Sp R))) D.P.A).left a = (snd (𝟙_ (Over (Sp R))) D.P.A).left b → a = b := by
    intro a b hab
    have e := GlobalTheory.PsiExpansion.snd_lift_unit D.P.A
    have key : ∀ c, (lift (toUnit D.P.A) (𝟙 D.P.A)).left ((snd (𝟙_ (Over (Sp R))) D.P.A).left c) = c :=
      fun c => by rw [← Scheme.Hom.comp_apply, e]; rfl
    rw [← key a, ← key b, hab]
  have hrB : rB y = z₀ := hinj _ _ ((congrArg (fun q => q y) h₂).trans hpG)
  obtain ⟨J, hJ⟩ := GlobalTheory.ConstFam.exists_good' D.P.isLB y
  obtain ⟨JG, hJG⟩ := GlobalTheory.ConstFam.exists_good' U.P.L.isLB y
  obtain ⟨s, hs⟩ := hE 0
  obtain ⟨H₁, H₂⟩ := hs _ (𝟙 _) rG rB (by rw [Category.id_comp]; exact h₁) (by rw [Category.id_comp]; exact h₂) h₃
    y JG J hJG hJ
  have hu : IsUnit (sval (g 0) rB y J) :=
    (GlobalTheory.Ex.OneGen.isUnit_sval_iff (g 0) rB y hJ).2 (by rw [hrB]; exact hn₀)
  have hc' : rB ≫ (𝟙_ (Over (Sp R)) ⊗ D.P.A).hom =
      (thickObj R (maximalIdeal R) 0 G).hom ≫ spMap (Ideal.Quotient.mk (maximalIdeal R ^ (0 + 1))) :=
    Over.w (lift (toUnit _) (U.gt 0).pG)
  rw [Finset.sum_eq_single 0 (fun α _ hα => by
    obtain ⟨a, ha, h, hh⟩ := hmul α hα
    rw [GlobalTheory.IndivisibleSection.sval_of_secIsMul hh _ y hJ, hc', cst_comp,
      Ideal.Quotient.eq_zero_iff_mem.2 (by simpa using ha), GlobalTheory.GermDiv.cst_zero, zero_mul, zero_mul])
    (fun h => absurd (H₁ 0 h) hu.ne_zero)] at H₂
  have hτ : IsUnit (sval τ rG y JG) :=
    isUnit_of_mul_isUnit_right (H₂ ▸ hu.mul (Units.isUnit _))
  obtain ⟨σ, hσ⟩ := GlobalTheory.PsiExpansion.exists_sameG U.P.L.isLB τ
  rw [hσ _ rG y JG hJG, h₁] at hτ
  have hm := (GlobalTheory.Ex.OneGen.isUnit_sval_iff σ _ y hJG).1 hτ
  refine ⟨ReciprocityTheory.ChartRestriction.G.DVR.secOfH0 σ, _, GlobalTheory.ThetaClosed.nonzeroLocus_firstPower_section_subset σ hm, ?_⟩
  have hc : (fstG (maximalIdeal R) 0 G).left ≫ G.hom = (U.gt 0).pG.left ≫ D.P.A.hom :=
    (Over.w (fstG (maximalIdeal R) 0 G)).trans (Over.w (U.gt 0).pG).symm
  exact (congrArg (fun q => q y) hc).trans ((congrArg D.P.A.hom hpG).trans hx)

end GlobalTheory.PreUTheta
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemNonzeroLocusOfWeightZeroExpansionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mem_nonzeroLocus_of_weightZero_expansion : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU (maximalIdeal R) D A G) (τ : U.SecGT (𝟙_ _) 1) (g : ∀ α, GlobalTheory.UU.SecBT D (𝟙_ _) 1 α), U.ExpT (𝟙_ _) 1 τ g → GlobalTheory.PsiRing.FibNZ (𝟙_ _ ⊗ D.P.A).hom (g 0) → (∀ α, α ≠ 0 → ∃ a ∈ maximalIdeal R, ∃ h : GlobalTheory.UU.SecBT D (𝟙_ _) 1 α, ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul (𝟙_ _ ⊗ D.P.A).hom a (g α) h) → ∃ θ : LB.Sec U.P.L.L, ∃ x ∈ nonzeroLocus θ, G.hom x = closedPoint R := by
  first | exact @GlobalTheory.PreUTheta.exists_mem_nonzeroLocus | exact GlobalTheory.PreUTheta.exists_mem_nonzeroLocus | (intros; apply GlobalTheory.PreUTheta.exists_mem_nonzeroLocus <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreUniformisedFibrewiseNonvanishingSection
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem thetaNZ_of_preU : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU (maximalIdeal R) D A G), EvenOn U.P → GlobalTheory.LN.ThetaNZ G U.P.L.L := by
  intro R _ _ _ hB D A G _ _ U hE
  obtain ⟨V, _, _, _, φ, D', A', G', _, _, U', U₀, F, C, hV, hφ, hc, hU⟩ := GlobalTheory.T.exists_completeDVR_comparison_preUniformised R hB D A G U hE
  obtain ⟨σ, f, g, q, hq, hf, hfg, hg0, hgm⟩ := GlobalTheory.T.exists_coefficientData_of_nonzero_section R hB D A G U V φ D' A' G' U' U₀ F C hV hφ hc hU
  obtain ⟨τ, hτ⟩ := GlobalTheory.T.exists_section_quotient_of_expansion_dvd R hB D A G U σ f g q hq hf hfg
  have := U.semi.smooth
  exact GlobalTheory.UnifNormal.thetaNZ_of_closedPoint G _ (GlobalTheory.T.exists_mem_nonzeroLocus_of_weightZero_expansion R D A G U τ g hτ hg0 hgm)

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreUniformisedFibrewiseNonvanishingSectionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.preUniformised_fibrewise_nonvanishing_section : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU (maximalIdeal R) D A G), EvenOn U.P → GlobalTheory.LN.ThetaNZ G U.P.L.L := by
  first | exact @GlobalTheory.Mum.thetaNZ_of_preU | exact GlobalTheory.Mum.thetaNZ_of_preU | (intros; apply GlobalTheory.Mum.thetaNZ_of_preU <;> assumption)
end
