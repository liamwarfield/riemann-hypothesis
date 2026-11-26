module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSemiAbelianImage

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueFibreClassEqZeroOfSmulPullbackEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueFibreClassEqZeroOfSmulPullbackEqZero
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem isClosedImmersion_of_isPullback_surj {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'}
    (hσ : Function.Surjective σ) {Y Y' : Scheme.{0}} {q : Y ⟶ Sp R} {q' : Y' ⟶ Sp R'} {χ : Y' ⟶ Y}
    (k : IsPullback χ q' q (spMap σ)) : IsClosedImmersion χ := by
  have : IsClosedImmersion (spMap σ) := IsClosedImmersion.spec_of_surjective _ hσ
  exact MorphismProperty.of_isPullback (P := @IsClosedImmersion) k.flip this

theorem tmul_pull_eq_zero : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (X X' X₀ : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (s₀ : X₀ ⟶ Sp R₀) (φ : X' ⟶ X) (φ₀ : X₀ ⟶ X) (h : IsPullback φ s' s (spMap σ)) (h₀ : IsPullback φ₀ s₀ s (spMap σ₀)) (Y Y' Y₀ : Scheme.{0}) (q : Y ⟶ Sp R) (q' : Y' ⟶ Sp R') (q₀ : Y₀ ⟶ Sp R₀) (χ : Y' ⟶ Y) (χ₀ : Y₀ ⟶ Y) (k : IsPullback χ q' q (spMap σ)) (k₀ : IsPullback χ₀ q₀ q (spMap σ₀)) (ψ : Y ⟶ X) (ψ' : Y' ⟶ X') (ψ₀ : Y₀ ⟶ X₀) (w : ψ ≫ s = q ≫ spMap (RingHom.id R)) (w' : ψ' ≫ s' = q' ≫ spMap (RingHom.id R')) (w₀ : ψ₀ ≫ s₀ = q₀ ≫ spMap (RingHom.id R₀)), ψ' ≫ φ = χ ≫ ψ → ψ₀ ≫ φ₀ = χ₀ ≫ ψ → SmallExt t σ σ₀ → Flat s → Flat q → CohomZeroIsConstants (OAff q') → ∀ (u : HO1 s₀) (y : HO1 s), TMul h₀.w t u y → pullHO1 w y = 0 → pullHO1 w₀ u = 0 := by
  intro R R' R₀ _ _ _ t σ σ₀ X X' X₀ s s' s₀ φ φ₀ h h₀ Y Y' Y₀ q q' q₀ χ χ₀ k k₀ ψ ψ' ψ₀ w w' w₀
    _hψ' hψ₀ hE _hs hq hC u y hT hy
  obtain ⟨hσ, hker, hσ₀, hker₀⟩ := hE
  haveI : IsClosedImmersion χ := isClosedImmersion_of_isPullback_surj hσ k
  haveI : IsClosedImmersion χ₀ := isClosedImmersion_of_isPullback_surj hσ₀ k₀
  haveI : IsClosedImmersion φ₀ := isClosedImmersion_of_isPullback_surj hσ₀ h₀
  have ht : σ t = 0 := by rw [← RingHom.mem_ker, hker]; exact Ideal.mem_span_singleton_self t
  obtain ⟨f, c, hcf, hcy, hred⟩ := hT

  have h1 : (pairPull w).pull1 y = 0 := by
    have e := isPullO_pullHO1 w y
    unfold IsPullO at e
    rw [e, hy, map_zero]
  rw [← hcy, CoefMap.pullCohomologyOne_class, GlobalTheory.CatCoh.H1.mk_eq_zero] at h1
  obtain ⟨g, hg⟩ := h1
  obtain ⟨f₁, hf₁⟩ : ∃ f₁ : C1 (OPair ψ q), ∀ T T' (a : T ⟶ T'),
      f₁ T T' a = (pairPull w).α T' (f _ _ ((pairPull w).G.map a)) := ⟨_, fun _ _ _ ↦ rfl⟩
  have hg' : ∀ (T T' : (Pair ψ)ᵒᵖ) (a : T ⟶ T'), g T' - mp (OPair ψ q) a (g T) = t • f₁ T T' a := by
    intro T T' a
    have e := congrFun (congrFun (congrFun hg T) T') a
    rw [amitsur_d0_apply, CoefMap.pullCocycleOne_apply] at e
    rw [e, hf₁, hcf, Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, (pairPull w).smul, RingHom.id_apply]

  let gb : C0 (pairFst ψ ⋙ OPre χ q') := fun T ↦ preα χ q q' ((pairFst ψ).obj T) (g T)
  have hgb : d0 _ gb = 0 := by
    funext T T' a
    rw [amitsur_d0_apply]
    have nat : preα χ q q' _ (mp (OAff q) ((pairFst ψ).map a) (g T)) =
        mp (OPre χ q') ((pairFst ψ).map a) (preα χ q q' _ (g T)) := (preCoef k.w).naturality _ _
    change preα χ q q' _ (g T') - mp (OPre χ q') ((pairFst ψ).map a) (preα χ q q' _ (g T)) = 0
    rw [← nat]
    change preα χ q q' _ (g T') - preα χ q q' _ (mp (OPair ψ q) a (g T)) = 0
    have sm : ∀ U (r0 : R) b, preα χ q q' U (r0 • b) = σ r0 • preα χ q q' U b := (preCoef k.w).smul
    rw [← map_sub, hg', sm, ht, zero_smul]
  obtain ⟨r', hr', -⟩ := (GlobalTheory.T.pairFst_preimage_restriction_bijective_closedImmersion R' X Y Y' ψ χ q').2.2 hC gb hgb
  obtain ⟨r, rfl⟩ := hσ r'
  have hsec := GlobalTheory.T.surjective_deformation_affine_sections R R' R₀ t σ σ₀ Y Y' Y₀ q q' q₀ χ χ₀ k k₀ ⟨hσ, hker, hσ₀, hker₀⟩ hq
  have hex : ∀ T : (Pair ψ)ᵒᵖ, ∃ e, g T - algebraMap R _ r = t • e := by
    intro T
    refine ((hsec ((pairFst ψ).obj T)).2.1 _).1 ?_
    have e : preα χ q q' ((pairFst ψ).obj T) (algebraMap R ((OPair ψ q).obj T) r) =
        algebraMap R' ((pairFst ψ ⋙ OPre χ q').obj T) (σ r) :=
      SemiHom.map_algebraMap ((preCoef k.w).smul _) r
    rw [map_sub, e]
    exact sub_eq_zero.2 (hr' T)
  choose g₁ hg₁ using hex
  have hkill : ∀ (T T' : (Pair ψ)ᵒᵖ) (a : T ⟶ T'),
      t • (f₁ T T' a - (g₁ T' - mp (OPair ψ q) a (g₁ T))) = 0 := by
    intro T T' a
    rw [smul_sub, smul_sub, ← map_smul (mp (OPair ψ q) a), ← hg₁ T', ← hg₁ T, map_sub, AlgHom.commutes,
      ← hg' T T' a]
    abel

  obtain ⟨c₀, hc₀, hc₀'⟩ :=
    (GlobalTheory.T.cohomologyClass_pullback_reduction_pairs R R₀ σ₀ X X₀ Y Y₀ s s₀ q q₀ φ₀ χ₀ h₀.w ψ ψ₀ w w₀ hψ₀ inferInstance).1 f u hred
  have hz : (CoefMap.restrict (OAff q₀) (pairFst ψ ⋙ preAff χ₀)).pull1 (pullHO1 w₀ u) = 0 := by
    rw [← hc₀', GlobalTheory.CatCoh.H1.mk_eq_zero]
    refine ⟨fun T ↦ preα χ₀ q q₀ ((pairFst ψ).obj T) (g₁ T), ?_⟩
    funext T T' a
    rw [hc₀, amitsur_d0_apply, ← hf₁]
    have e1 := ((hsec ((pairFst ψ).obj T')).2.2.2 _).2 (hkill T T' a)
    rw [map_sub, map_sub, sub_eq_zero] at e1
    have nat : preα χ₀ q q₀ _ (mp (OAff q) ((pairFst ψ).map a) (g₁ T)) =
        mp (OPre χ₀ q₀) ((pairFst ψ).map a) (preα χ₀ q q₀ _ (g₁ T)) := (preCoef k₀.w).naturality _ _
    change _ - mp (OPre χ₀ q₀) ((pairFst ψ).map a) (preα χ₀ q q₀ _ (g₁ T)) = _
    rw [← nat]
    exact e1.symm
  exact (GlobalTheory.T.pairFst_preimage_restriction_bijective_closedImmersion R₀ X Y Y₀ ψ χ₀ q₀).1.1 (hz.trans (map_zero _).symm)

end GlobalTheory.AbCoh
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueFibreClassEqZeroOfSmulPullbackEqZeroStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residueFibre_class_eq_zero_of_smul_pullback_eq_zero : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (X X' X₀ : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (s₀ : X₀ ⟶ Sp R₀) (φ : X' ⟶ X) (φ₀ : X₀ ⟶ X) (h : IsPullback φ s' s (spMap σ)) (h₀ : IsPullback φ₀ s₀ s (spMap σ₀)) (Y Y' Y₀ : Scheme.{0}) (q : Y ⟶ Sp R) (q' : Y' ⟶ Sp R') (q₀ : Y₀ ⟶ Sp R₀) (χ : Y' ⟶ Y) (χ₀ : Y₀ ⟶ Y) (k : IsPullback χ q' q (spMap σ)) (k₀ : IsPullback χ₀ q₀ q (spMap σ₀)) (ψ : Y ⟶ X) (ψ' : Y' ⟶ X') (ψ₀ : Y₀ ⟶ X₀) (w : ψ ≫ s = q ≫ spMap (RingHom.id R)) (w' : ψ' ≫ s' = q' ≫ spMap (RingHom.id R')) (w₀ : ψ₀ ≫ s₀ = q₀ ≫ spMap (RingHom.id R₀)), ψ' ≫ φ = χ ≫ ψ → ψ₀ ≫ φ₀ = χ₀ ≫ ψ → SmallExt t σ σ₀ → Flat s → Flat q → CohomZeroIsConstants (OAff q') → ∀ (u : HO1 s₀) (y : HO1 s), TMul h₀.w t u y → pullHO1 w y = 0 → pullHO1 w₀ u = 0 := by
  first | exact @GlobalTheory.AbCoh.tmul_pull_eq_zero | exact GlobalTheory.AbCoh.tmul_pull_eq_zero | (intros; apply GlobalTheory.AbCoh.tmul_pull_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSmulResidueFibreClassOfPullbackEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSmulResidueFibreClassOfPullbackEqZero
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem tmul_of_pull_eq_zero : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (X X' X₀ : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (s₀ : X₀ ⟶ Sp R₀) (φ : X' ⟶ X) (φ₀ : X₀ ⟶ X) (h : IsPullback φ s' s (spMap σ)) (h₀ : IsPullback φ₀ s₀ s (spMap σ₀)), SmallExt t σ σ₀ → Flat s → ∀ y : HO1 s, pullHO1 h.w y = 0 → ∃ u : HO1 s₀, TMul h₀.w t u y := by
  intro R R' R₀ _ _ _ t σ σ₀ X X' X₀ s s' s₀ φ φ₀ h h₀ hse hfl y hy
  have : IsClosedImmersion φ := MorphismProperty.of_isPullback (P := @IsClosedImmersion) h.flip
    (IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom σ) hse.1)
  have : IsClosedImmersion φ₀ := MorphismProperty.of_isPullback (P := @IsClosedImmersion) h₀.flip
    (IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom σ₀) hse.2.2.1)
  have hsec := GlobalTheory.T.surjective_deformation_affine_sections R R' R₀ t σ σ₀ X X' X₀ s s' s₀ φ φ₀ h h₀ hse hfl
  have hred := GlobalTheory.T.cocyclePullback_iff_preimage_affineHom R R' X X' s s' σ φ h.w
  have hred₀ := GlobalTheory.T.cocyclePullback_iff_preimage_affineHom R R₀ X X₀ s s₀ σ₀ φ₀ h₀.w
  have hb₀ := GlobalTheory.T.preimageCochainRestriction_bijective_closedImmersion R₀ X X₀ φ₀ s₀
  have nat : ∀ {U V : AffOp X} (a : U ⟶ V) (b : (OAff s).obj U),
      preα φ s s' V (mp (OAff s) a b) = mp (OPre φ s') a (preα φ s s' U b) :=
    fun a b ↦ (preCoef h.w).naturality a b
  have nat₀ : ∀ {U V : AffOp X} (a : U ⟶ V) (b : (OAff s).obj U),
      preα φ₀ s s₀ V (mp (OAff s) a b) = mp (OPre φ₀ s₀) a (preα φ₀ s s₀ U b) :=
    fun a b ↦ (preCoef h₀.w).naturality a b
  obtain ⟨c, rfl⟩ := H1.mk_surjective _ y
  have h1 : (preCoef h.w).pull1 (H1.mk _ c) = 0 := by rw [← hred.2.2.1, hy, map_zero]
  rw [CoefMap.pullCohomologyOne_class, H1.mk_eq_zero] at h1
  obtain ⟨g', hg'⟩ := h1
  choose g hg using fun U ↦ (hsec U).1 (g' U)
  have hk : ∀ (U V : AffOp X) (a : U ⟶ V), preα φ s s' V (c.1 U V a - d0 _ g U V a) = 0 := by
    intro U V a
    have e := congrFun (congrFun (congrFun hg' U) V) a
    rw [amitsur_d0_apply, CoefMap.pullCocycleOne_apply] at e
    rw [map_sub, amitsur_d0_apply, map_sub, nat, hg, hg]
    exact sub_eq_zero.2 e.symm
  choose f hf using fun U V a ↦ ((hsec V).2.1 _).1 (hk U V a)
  let c' : Z1 (OAff s) := c - ⟨d0 _ g, commAlgFunctorCoboundaryZero_mem_cocyclesOne _ g⟩
  have hc' : c'.1 = t • (f : C1 (OAff s)) := by
    funext U V a; exact hf U V a
  have hz : ∀ ⦃U V W : AffOp X⦄ (a : U ⟶ V) (b : V ⟶ W),
      t • (mp (OAff s) b (f U V a) + f V W b - f U W (a ≫ b)) = 0 := by
    intro U V W a b
    have e := c'.2 a b
    rw [hc'] at e
    simp only [Pi.smul_apply, map_smul] at e
    rw [smul_sub, smul_add, e, sub_self]
  let c₀ : Z1 (OPre φ₀ s₀) := ⟨fun U V a ↦ preα φ₀ s s₀ V (f U V a), fun U V W a b ↦ by
    have e := ((hsec W).2.2.2 _).2 (hz a b)
    rw [map_sub, map_add (f := _), nat₀] at e
    exact (sub_eq_zero.1 e).symm⟩
  obtain ⟨u, hu⟩ := hb₀.1.2 (H1.mk _ c₀)
  refine ⟨u, f, c', hc', ?_, (hred₀.1 f u).2 ⟨c₀, fun _ _ _ ↦ rfl, hu.symm⟩⟩
  rw [map_sub, sub_eq_self]
  exact H1.mk_eq_zero.2 ⟨g, rfl⟩

end GlobalTheory.AbCoh
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSmulResidueFibreClassOfPullbackEqZeroStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_smul_residueFibre_class_of_pullback_eq_zero : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (X X' X₀ : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (s₀ : X₀ ⟶ Sp R₀) (φ : X' ⟶ X) (φ₀ : X₀ ⟶ X) (h : IsPullback φ s' s (spMap σ)) (h₀ : IsPullback φ₀ s₀ s (spMap σ₀)), SmallExt t σ σ₀ → Flat s → ∀ y : HO1 s, pullHO1 h.w y = 0 → ∃ u : HO1 s₀, TMul h₀.w t u y := by
  first | exact @GlobalTheory.AbCoh.tmul_of_pull_eq_zero | exact GlobalTheory.AbCoh.tmul_of_pull_eq_zero | (intros; apply GlobalTheory.AbCoh.tmul_of_pull_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallExtensionElementMulZeroClassEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallExtensionElementMulZeroClassEqZero
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbCoh

theorem tMul_zero_eq_zero : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (X X' X₀ : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (s₀ : X₀ ⟶ Sp R₀) (φ : X' ⟶ X) (φ₀ : X₀ ⟶ X) (h : IsPullback φ s' s (spMap σ)) (h₀ : IsPullback φ₀ s₀ s (spMap σ₀)), SmallExt t σ σ₀ → Flat s → ∀ y : HO1 s, TMul h₀.w t 0 y → y = 0 := by
  intro R R' R₀ _ _ _ t σ σ₀ X X' X₀ s s' s₀ φ φ₀ h h₀ hE hF y hy
  have iφ : IsClosedImmersion φ :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) h.flip
      (IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom σ) hE.1)
  have iφ₀ : IsClosedImmersion φ₀ :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) h₀.flip
      (IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom σ₀) hE.2.2.1)
  obtain ⟨f, c, hc, rfl, hred⟩ := hy
  obtain ⟨c₀, hc₀, hcl⟩ := ((GlobalTheory.AbCoh.red_iff_pre R R₀ X X₀ s s₀ σ₀ φ₀ h₀.w).1 f 0).1 hred
  rw [map_zero, CatCoh.H1.mk_eq_zero] at hcl
  obtain ⟨g₀, hg₀⟩ := hcl
  have hS := GlobalTheory.AbCoh.preα_surjective_and_ker R R' R₀ t σ σ₀ X X' X₀ s s' s₀ φ φ₀ h h₀ hE hF
  choose g hg using fun U => (hS U).2.2.1 (g₀ U)
  have key : ∀ U V (a : U ⟶ V), t • (f U V a - d0 (OAff s) g U V a) = 0 := by
    intro U V a
    rw [← (hS V).2.2.2]
    have hn := (preCoef h₀.w).naturality a (g U)
    have e := congrFun (congrFun (congrFun hg₀ U) V) a
    change preα φ₀ s s₀ V (mp (OAff s) a (g U)) = mp (OPre φ₀ s₀) a (preα φ₀ s s₀ U (g U)) at hn
    rw [amitsur_d0_apply, hc₀] at e
    rw [amitsur_d0_apply, map_sub, map_sub, hn, hg, hg, ← e]
    ring
  refine CatCoh.H1.mk_eq_zero.2 ⟨t • g, ?_⟩
  rw [hc, map_smul]
  funext U V a
  have := key U V a
  simp only [Pi.smul_apply]
  rw [smul_sub, sub_eq_zero] at this
  exact this.symm

end GlobalTheory.AbCoh
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallExtensionElementMulZeroClassEqZeroStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smallExtension_element_mul_zeroClass_eq_zero : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (X X' X₀ : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (s₀ : X₀ ⟶ Sp R₀) (φ : X' ⟶ X) (φ₀ : X₀ ⟶ X) (h : IsPullback φ s' s (spMap σ)) (h₀ : IsPullback φ₀ s₀ s (spMap σ₀)), SmallExt t σ σ₀ → Flat s → ∀ y : HO1 s, TMul h₀.w t 0 y → y = 0 := by
  first | exact @GlobalTheory.AbCoh.tMul_zero_eq_zero | exact GlobalTheory.AbCoh.tMul_zero_eq_zero | (intros; apply GlobalTheory.AbCoh.tMul_zero_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArtinianLiftAxesWedgeLocal
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

noncomputable section
namespace GlobalTheory.AbCoh.StepPrim

theorem pO1_comp {R : Type} [CommRing R] {X Y Z : Over (Sp R)} (f : X ⟶ Y) (g : Y ⟶ Z) (a : HO1 Z.hom) :
    pO1 (f ≫ g) a = pO1 f (pO1 g a) :=
  ((GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id).1 R R Z.left Y.left Z.hom Y.hom (RingHom.id R) g.left (ovw g) R X.left X.hom
    (RingHom.id R) f.left (ovw f) (RingHom.id R) (f ≫ g).left (ovw (f ≫ g)) (Over.comp_left _ _ _ f g)
    (fun _ ↦ rfl)).1 a |>.symm

theorem pO1_id {R : Type} [CommRing R] (A : Over (Sp R)) (a : HO1 A.hom) : pO1 (𝟙 A) a = a :=
  ((GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id).2.2 R A).1 a

theorem eq_zero_of_base {R : Type} [CommRing R] (a : HO1 (𝟙_ (Over (Sp R))).hom) : a = 0 := by
  haveI := ((GlobalTheory.AbCoh.Vanish.main).1 R (𝟙_ (Over (Sp R))).left (𝟙_ (Over (Sp R))).hom
    (inferInstanceAs (IsAffine (Sp R)))).1
  exact Subsingleton.elim _ _

theorem axes_defect {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] (x : HO1 A.hom) :
    pO1 (lift (𝟙 A) (1 : A ⟶ A)) (pO1 μ[A] x - pO1 (fst A A) x - pO1 (snd A A) x) = 0 ∧
    pO1 (lift (1 : A ⟶ A) (𝟙 A)) (pO1 μ[A] x - pO1 (fst A A) x - pO1 (snd A A) x) = 0 := by
  have h1 : ∀ a : HO1 A.hom, pO1 (1 : A ⟶ A) a = 0 := fun a ↦ by
    rw [Hom.one_def, pO1_comp, eq_zero_of_base (pO1 η[A] a), map_zero]
  refine ⟨?_, ?_⟩
  · rw [map_sub, map_sub, ← pO1_comp, ← pO1_comp, ← pO1_comp, lift_fst, lift_snd, ← Hom.mul_def,
      _root_.mul_one, pO1_id, h1, sub_self, sub_zero]
  · rw [map_sub, map_sub, ← pO1_comp, ← pO1_comp, ← pO1_comp, lift_fst, lift_snd, ← Hom.mul_def,
      _root_.one_mul, pO1_id, h1, sub_zero, sub_self]

theorem main : ∀ (R : Type) [CommRing R] [IsLocalRing R] (t : R) (R' : Type) [CommRing R'] (σ' : R →+* R'), Function.Surjective σ' → RingHom.ker σ' = Ideal.span {t} → t ≠ 0 → (∀ a ∈ IsLocalRing.maximalIdeal R, a * t = 0) → (∀ (k : Type) [CommRing k], IsField k → ∀ (B : Over (Sp k)) [GrpObj B] (g : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → AxesVanishingStructureSheafDegOne B ∧ NoPrimitiveStructureSheafH2 B ∧ WedgeO (OAff B.hom)) → (∀ (B : Over (Sp R')) [GrpObj B] (g : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → StructureSheafH1Primitive B) → ∀ (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → StructureSheafH1Primitive A := by
  intro R _ _ t R' _ σ' hsurj hker ht hmt hfield hR' A _ g hab hsm
  letI : Algebra R R' := σ'.toAlgebra
  have hkF : IsField (R ⧸ IsLocalRing.maximalIdeal R) :=
    (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp inferInstance
  have hSE : SmallExt t (algebraMap R R') (algebraMap R (R ⧸ IsLocalRing.maximalIdeal R)) := by
    refine ⟨hsurj, hker, Ideal.Quotient.mk_surjective, fun a ↦ ?_⟩
    rw [Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
    refine ⟨hmt a, fun h ↦ ?_⟩
    by_contra hna
    exact ht ((IsLocalRing.notMem_maximalIdeal.mp hna).mul_right_eq_zero.mp h)
  haveI := hsm
  haveI : Smooth A.hom := SmoothOfRelativeDimension.smooth g A.hom
  haveI : Flat A.hom := inferInstance
  have hfl2 : Flat (A ⊗ A).hom := by rw [Over.tensorObj_hom]; infer_instance
  obtain ⟨B', _, pr, pr', hab', hsm', hpr, hpr', hμ', hf', hs', he1', he2'⟩ := GlobalTheory.T.exists_abelianScheme_baseChange_and_square R R' A g hab hsm
  obtain ⟨B₀, _, pr0, pr0', hab0, hsm0, hpr0, hpr0', -, -, -, he10, he20⟩ :=
    GlobalTheory.T.exists_abelianScheme_baseChange_and_square R (R ⧸ IsLocalRing.maximalIdeal R) A g hab hsm
  intro x
  have key : pO1 μ[A] x - pO1 (fst A A) x - pO1 (snd A A) x = 0 := by
    set y := pO1 μ[A] x - pO1 (fst A A) x - pO1 (snd A A) x with hy
    have hnat := GlobalTheory.AbCoh.pull_over_baseChange_comm R R' (algebraMap R R') A (A ⊗ A) B' (B' ⊗ B')
    have ya : pullHO1 hpr'.w y = 0 := by
      have hP := hR' B' g hab' hsm' (pullHO1 hpr.w x)
      rw [hy, map_sub, map_sub, (hnat μ[A] μ[B'] pr pr' hpr.w hpr'.w hμ').1,
        (hnat (fst A A) (fst B' B') pr pr' hpr.w hpr'.w hf').1,
        (hnat (snd A A) (snd B' B') pr pr' hpr.w hpr'.w hs').1, hP]
      abel
    obtain ⟨u, hu⟩ := GlobalTheory.T.eq_smul_residueFibre_class_of_pullback_eq_zero R R' (R ⧸ IsLocalRing.maximalIdeal R) t (algebraMap R R')
      (algebraMap R (R ⧸ IsLocalRing.maximalIdeal R)) (A ⊗ A).left (B' ⊗ B').left (B₀ ⊗ B₀).left (A ⊗ A).hom
      (B' ⊗ B').hom (B₀ ⊗ B₀).hom pr' pr0' hpr' hpr0' hSE hfl2 y ya
    have hH0 := (GlobalTheory.T.globalFunctionsConstantAfterBaseChange_of_abelianScheme R A hab) R' B'.left B'.hom pr hpr
    have hax := axes_defect A x
    have hu1 : pO1 (lift (𝟙 B₀) (1 : B₀ ⟶ B₀)) u = 0 :=
      GlobalTheory.T.residueFibre_class_eq_zero_of_smul_pullback_eq_zero R R' (R ⧸ IsLocalRing.maximalIdeal R) t (algebraMap R R')
        (algebraMap R (R ⧸ IsLocalRing.maximalIdeal R)) (A ⊗ A).left (B' ⊗ B').left (B₀ ⊗ B₀).left (A ⊗ A).hom
        (B' ⊗ B').hom (B₀ ⊗ B₀).hom pr' pr0' hpr' hpr0' A.left B'.left B₀.left A.hom B'.hom B₀.hom pr pr0 hpr hpr0
        (lift (𝟙 A) (1 : A ⟶ A)).left (lift (𝟙 B') (1 : B' ⟶ B')).left (lift (𝟙 B₀) (1 : B₀ ⟶ B₀)).left
        (ovw _) (ovw _) (ovw _) he1' he10 hSE hfl2 inferInstance hH0 u y hu hax.1
    have hu2 : pO1 (lift (1 : B₀ ⟶ B₀) (𝟙 B₀)) u = 0 :=
      GlobalTheory.T.residueFibre_class_eq_zero_of_smul_pullback_eq_zero R R' (R ⧸ IsLocalRing.maximalIdeal R) t (algebraMap R R')
        (algebraMap R (R ⧸ IsLocalRing.maximalIdeal R)) (A ⊗ A).left (B' ⊗ B').left (B₀ ⊗ B₀).left (A ⊗ A).hom
        (B' ⊗ B').hom (B₀ ⊗ B₀).hom pr' pr0' hpr' hpr0' A.left B'.left B₀.left A.hom B'.hom B₀.hom pr pr0 hpr hpr0
        (lift (1 : A ⟶ A) (𝟙 A)).left (lift (1 : B' ⟶ B') (𝟙 B')).left (lift (1 : B₀ ⟶ B₀) (𝟙 B₀)).left
        (ovw _) (ovw _) (ovw _) he2' he20 hSE hfl2 inferInstance hH0 u y hu hax.2
    have hu0 : u = 0 := (hfield _ hkF B₀ g hab0 hsm0).1 u hu1 hu2
    subst hu0
    exact GlobalTheory.T.smallExtension_element_mul_zeroClass_eq_zero R R' (R ⧸ IsLocalRing.maximalIdeal R) t (algebraMap R R')
      (algebraMap R (R ⧸ IsLocalRing.maximalIdeal R)) (A ⊗ A).left (B' ⊗ B').left (B₀ ⊗ B₀).left (A ⊗ A).hom
      (B' ⊗ B').hom (B₀ ⊗ B₀).hom pr' pr0' hpr' hpr0' hSE hfl2 y hu
  rw [sub_sub, sub_eq_zero] at key
  exact key

end GlobalTheory.AbCoh.StepPrim
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArtinianLiftAxesWedgeLocalStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.artinian_lift_axes_wedge_local : ∀ (R : Type) [CommRing R] [IsLocalRing R] (t : R) (R' : Type) [CommRing R'] (σ' : R →+* R'), Function.Surjective σ' → RingHom.ker σ' = Ideal.span {t} → t ≠ 0 → (∀ a ∈ IsLocalRing.maximalIdeal R, a * t = 0) → (∀ (k : Type) [CommRing k], IsField k → ∀ (B : Over (Sp k)) [GrpObj B] (g : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → AxesVanishingStructureSheafDegOne B ∧ NoPrimitiveStructureSheafH2 B ∧ WedgeO (OAff B.hom)) → (∀ (B : Over (Sp R')) [GrpObj B] (g : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → StructureSheafH1Primitive B) → ∀ (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → StructureSheafH1Primitive A := by
  first | exact @GlobalTheory.AbCoh.StepPrim.main | exact GlobalTheory.AbCoh.StepPrim.main | (intros; apply GlobalTheory.AbCoh.StepPrim.main <;> assumption)
end
