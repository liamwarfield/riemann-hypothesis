module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrivSqZeroExtPinchExistsExtendBasicOpen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantHermitianFormCuspidalRep
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieDerivativeRealLieSmoothingEqDensity
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlCSurjectiveAndLinearIndependentBLie
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicChartSmooth

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecTrivSqZeroExtIsPushout
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrivSqZeroExtPinchBasicOpenMorphismUnique
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrivSqZeroExtPinchBasicOpenMorphismUnique
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh GlobalTheory.AbTan
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PinchUniq

section
variable (R : Type) [CommRing R] (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M]
  [Module Bᵐᵒᵖ M] [IsCentralScalar B M] [Module R M] [IsScalarTower R B M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]

theorem appTop_joint_inj (β : TrivSqZeroExt R M →+* TrivSqZeroExt B M) (hβ : IsSum β (algebraMap R B) id)
    (c : Γ(Sp (TrivSqZeroExt R M), ⊤))
    (h1 : (spMap (TrivSqZeroExt.fstHom R R M).toRingHom).appTop.hom c = 0)
    (h2 : (spMap β).appTop.hom c = 0) : c = 0 := by
  have n1 := congrArg (fun k => k.hom c)
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R M).toRingHom))
  have n2 := congrArg (fun k => k.hom c) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom β))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at n1 n2
  have h1' : (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R M).toRingHom)).appTop.hom c = 0 := h1
  have h2' : (Spec.map (CommRingCat.ofHom β)).appTop.hom c = 0 := h2
  rw [h1', map_zero] at n1
  rw [h2', map_zero] at n2
  set c' := (Scheme.ΓSpecIso (CommRingCat.of (TrivSqZeroExt R M))).hom.hom c with hc'
  have e1 : TrivSqZeroExt.fst c' = 0 := n1.symm
  have e2 : TrivSqZeroExt.snd c' = 0 := by
    have : β c' = TrivSqZeroExt.inl (algebraMap R B (TrivSqZeroExt.fst c')) + TrivSqZeroExt.inr (TrivSqZeroExt.snd c') := by
      conv_lhs => rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq c']
      rw [map_add (f := _), hβ.1, hβ.2]; rfl
    have := congrArg TrivSqZeroExt.snd this
    rw [← n2] at this
    simpa using this.symm
  have hc0 : c' = 0 := TrivSqZeroExt.ext e1 e2
  have : c = (Scheme.ΓSpecIso (CommRingCat.of (TrivSqZeroExt R M))).inv.hom c' := by
    rw [hc']; simp
  rw [this, hc0, map_zero]

theorem exists_pow_of_appLE_eq_zero {A : Type} [CommRing A] (s a : Γ(Sp A, ⊤)) (n : ℕ)
    {Y : Scheme.{0}} [IsAffine Y] (f : Y ⟶ Sp A)
    (hf : (f.appLE _ _ le_rfl).hom
      (IsLocalization.mk' Γ(Sp A, (Sp A).basicOpen s) a (⟨s ^ n, n, rfl⟩ : Submonoid.powers s)) = 0) :
    ∃ N : ℕ, f.appTop.hom (s ^ N * a) = 0 := by
  have hspec := IsLocalization.mk'_spec Γ(Sp A, (Sp A).basicOpen s) a (⟨s ^ n, n, rfl⟩ : Submonoid.powers s)
  have h3 : (f.appLE _ _ le_rfl).hom (algebraMap Γ(Sp A, ⊤) Γ(Sp A, (Sp A).basicOpen s) a) = 0 := by
    rw [← hspec, map_mul, hf, zero_mul]
  have h4 : (f.appLE ⊤ (f ⁻¹ᵁ (Sp A).basicOpen s) (by simp)).hom a = 0 := by
    rw [← h3]
    show _ = (((Sp A).presheaf.map (homOfLE le_top).op) ≫ f.appLE _ _ le_rfl).hom a
    rw [Scheme.Hom.map_appLE]
  have hle : Y.basicOpen (f.appTop.hom s) ≤ f ⁻¹ᵁ (Sp A).basicOpen s := (Scheme.preimage_basicOpen_top f s).ge
  have h6 : (f.appLE ⊤ (Y.basicOpen (f.appTop.hom s)) (by simp)).hom a = 0 := by
    rw [← Scheme.Hom.appLE_map (i := (homOfLE hle).op), CommRingCat.comp_apply, h4, map_zero]
    simp
  have h5 : f.appTop.hom a |_ (Y.basicOpen (f.appTop.hom s)) = 0 := h6
  obtain ⟨N, hN⟩ := exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen Y (isAffineOpen_top Y) _ _ h5
  exact ⟨N, by rw [map_mul, map_pow]; exact hN⟩

theorem appLE_basicOpen_joint_inj (β : TrivSqZeroExt R M →+* TrivSqZeroExt B M) (hβ : IsSum β (algebraMap R B) id)
    (s : Γ(Sp (TrivSqZeroExt R M), ⊤)) (t : Γ(Sp (TrivSqZeroExt R M), (Sp (TrivSqZeroExt R M)).basicOpen s))
    (h1 : ((spMap (TrivSqZeroExt.fstHom R R M).toRingHom).appLE _ _ le_rfl).hom t = 0)
    (h2 : ((spMap β).appLE _ _ le_rfl).hom t = 0) : t = 0 := by
  obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers s) t
  obtain ⟨N₁, hN₁⟩ := exists_pow_of_appLE_eq_zero s a n _ h1
  obtain ⟨N₂, hN₂⟩ := exists_pow_of_appLE_eq_zero s a n _ h2
  have hc : s ^ (N₁ + N₂) * a = 0 := by
    apply appTop_joint_inj R B M β hβ
    · rw [pow_add, mul_comm (s ^ N₁), _root_.mul_assoc, map_mul, hN₁, mul_zero]
    · rw [pow_add, _root_.mul_assoc, map_mul, hN₂, mul_zero]
  rw [IsLocalization.mk'_eq_zero_iff]
  exact ⟨⟨_, N₁ + N₂, rfl⟩, hc⟩

theorem resLE_appTop_joint_inj (β : TrivSqZeroExt R M →+* TrivSqZeroExt B M) (hβ : IsSum β (algebraMap R B) id)
    (s : Γ(Sp (TrivSqZeroExt R M), ⊤)) (a b : Γ(((Sp (TrivSqZeroExt R M)).basicOpen s).toScheme, ⊤))
    (h1 : ((spMap (TrivSqZeroExt.fstHom R R M).toRingHom).resLE _ _ le_rfl).appTop.hom a =
      ((spMap (TrivSqZeroExt.fstHom R R M).toRingHom).resLE _ _ le_rfl).appTop.hom b)
    (h2 : ((spMap β).resLE _ _ le_rfl).appTop.hom a = ((spMap β).resLE _ _ le_rfl).appTop.hom b) : a = b := by
  have conv : ∀ {Y : Scheme.{0}} (f : Y ⟶ Sp (TrivSqZeroExt R M)) (c : Γ(((Sp (TrivSqZeroExt R M)).basicOpen s).toScheme, ⊤)),
      (f.resLE ((Sp (TrivSqZeroExt R M)).basicOpen s) (f ⁻¹ᵁ (Sp (TrivSqZeroExt R M)).basicOpen s) le_rfl).appTop.hom c =
        (f ⁻¹ᵁ (Sp (TrivSqZeroExt R M)).basicOpen s).topIso.inv.hom
          ((f.appLE _ _ le_rfl).hom (((Sp (TrivSqZeroExt R M)).basicOpen s).topIso.hom.hom c)) := by
    intro Y f c
    rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top]
    rfl
  rw [conv, conv] at h1 h2
  replace h1 := congrArg (spMap (TrivSqZeroExt.fstHom R R M).toRingHom ⁻¹ᵁ
    (Sp (TrivSqZeroExt R M)).basicOpen s).topIso.hom.hom h1
  replace h2 := congrArg (spMap β ⁻¹ᵁ (Sp (TrivSqZeroExt R M)).basicOpen s).topIso.hom.hom h2
  simp only [Iso.inv_hom_id_apply] at h1 h2
  have hz := appLE_basicOpen_joint_inj R B M β hβ s
    (((Sp (TrivSqZeroExt R M)).basicOpen s).topIso.hom.hom a - ((Sp (TrivSqZeroExt R M)).basicOpen s).topIso.hom.hom b)
    (by rw [map_sub, h1, sub_self]) (by rw [map_sub, h2, sub_self])
  exact (((Sp (TrivSqZeroExt R M)).basicOpen s).topIso.commRingCatIsoToRingEquiv).injective (sub_eq_zero.mp hz)

end

theorem uniq : ∀ (R : Type) [CommRing R] (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M] [Module R M] [IsScalarTower R B M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M] (β : TrivSqZeroExt R M →+* TrivSqZeroExt B M), IsSum β (algebraMap R B) id → ∀ (X : Scheme.{0}) (x : Sp R ⟶ X) (V : (Sp (TrivSqZeroExt R M)).Opens) (s : Γ((Sp (TrivSqZeroExt R M)), ⊤)), V = (Sp (TrivSqZeroExt R M)).basicOpen s → ∀ (U : X.affineOpens), spMap (TrivSqZeroExt.fstHom R R M).toRingHom ⁻¹ᵁ V ≤ x ⁻¹ᵁ U.1 → ∀ g₁ g₂ : V.toScheme ⟶ X, (spMap (TrivSqZeroExt.fstHom R R M).toRingHom).resLE V _ le_rfl ≫ g₁ = (spMap (TrivSqZeroExt.fstHom R R M).toRingHom ⁻¹ᵁ V).ι ≫ x → (spMap (TrivSqZeroExt.fstHom R R M).toRingHom).resLE V _ le_rfl ≫ g₂ = (spMap (TrivSqZeroExt.fstHom R R M).toRingHom ⁻¹ᵁ V).ι ≫ x → (spMap β).resLE V _ le_rfl ≫ g₁ = (spMap β).resLE V _ le_rfl ≫ g₂ → g₁ = g₂ := by
  intro R _ B M _ _ _ _ _ _ _ _ _ _ β hβ X x V s hV U hU g₁ g₂ h₁ h₂ h₃
  subst hV
  have hrange : ∀ g : ((Sp (TrivSqZeroExt R M)).basicOpen s).toScheme ⟶ X,
      (spMap (TrivSqZeroExt.fstHom R R M).toRingHom).resLE _ _ le_rfl ≫ g =
        (spMap (TrivSqZeroExt.fstHom R R M).toRingHom ⁻¹ᵁ (Sp (TrivSqZeroExt R M)).basicOpen s).ι ≫ x →
      Set.range g ⊆ Set.range U.1.ι := by
    rintro g hg _ ⟨p, rfl⟩
    rw [Scheme.Opens.range_ι]
    obtain ⟨w, hw⟩ := GlobalTheory.Pinch.spMap_fst_surjective R M p.1
    have hwV : w ∈ spMap (TrivSqZeroExt.fstHom R R M).toRingHom ⁻¹ᵁ (Sp (TrivSqZeroExt R M)).basicOpen s := by
      rw [Scheme.Hom.mem_preimage, hw]; exact p.2
    have hp : (spMap (TrivSqZeroExt.fstHom R R M).toRingHom).resLE _ _ le_rfl ⟨w, hwV⟩ = p :=
      Subtype.ext (by rw [Scheme.Hom.coe_resLE_apply]; exact hw)
    rw [← hp]
    change ((spMap (TrivSqZeroExt.fstHom R R M).toRingHom).resLE _ _ le_rfl ≫ g) ⟨w, hwV⟩ ∈ (U.1 : Set X)
    rw [hg]
    exact hU hwV
  haveI : IsAffine U.1.toScheme := U.2
  have f₁ := IsOpenImmersion.lift_fac U.1.ι g₁ (hrange g₁ h₁)
  have f₂ := IsOpenImmersion.lift_fac U.1.ι g₂ (hrange g₂ h₂)
  have ei : (spMap (TrivSqZeroExt.fstHom R R M).toRingHom).resLE _ _ le_rfl ≫ IsOpenImmersion.lift U.1.ι g₁ (hrange g₁ h₁) =
      (spMap (TrivSqZeroExt.fstHom R R M).toRingHom).resLE _ _ le_rfl ≫ IsOpenImmersion.lift U.1.ι g₂ (hrange g₂ h₂) := by
    rw [← cancel_mono U.1.ι, Category.assoc, Category.assoc, f₁, f₂, h₁, h₂]
  have ej : (spMap β).resLE _ _ le_rfl ≫ IsOpenImmersion.lift U.1.ι g₁ (hrange g₁ h₁) =
      (spMap β).resLE _ _ le_rfl ≫ IsOpenImmersion.lift U.1.ι g₂ (hrange g₂ h₂) := by
    rw [← cancel_mono U.1.ι, Category.assoc, Category.assoc, f₁, f₂, h₃]
  have hl : IsOpenImmersion.lift U.1.ι g₁ (hrange g₁ h₁) = IsOpenImmersion.lift U.1.ι g₂ (hrange g₂ h₂) := by
    apply ext_of_isAffine
    ext u
    apply resLE_appTop_joint_inj R B M β hβ s
    · have := congrArg (fun φ => φ.appTop.hom u) ei
      simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using this
    · have := congrArg (fun φ => φ.appTop.hom u) ej
      simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using this
  rw [← f₁, ← f₂, hl]

end GlobalTheory.PinchUniq
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrivSqZeroExtPinchBasicOpenMorphismUniqueStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh GlobalTheory.AbTan
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trivSqZeroExt_pinch_basicOpen_morphism_unique : ∀ (R : Type) [CommRing R] (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M] [Module R M] [IsScalarTower R B M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M] (β : TrivSqZeroExt R M →+* TrivSqZeroExt B M), IsSum β (algebraMap R B) id → ∀ (X : Scheme.{0}) (x : Sp R ⟶ X) (V : (Sp (TrivSqZeroExt R M)).Opens) (s : Γ((Sp (TrivSqZeroExt R M)), ⊤)), V = (Sp (TrivSqZeroExt R M)).basicOpen s → ∀ (U : X.affineOpens), spMap (TrivSqZeroExt.fstHom R R M).toRingHom ⁻¹ᵁ V ≤ x ⁻¹ᵁ U.1 → ∀ g₁ g₂ : V.toScheme ⟶ X, (spMap (TrivSqZeroExt.fstHom R R M).toRingHom).resLE V _ le_rfl ≫ g₁ = (spMap (TrivSqZeroExt.fstHom R R M).toRingHom ⁻¹ᵁ V).ι ≫ x → (spMap (TrivSqZeroExt.fstHom R R M).toRingHom).resLE V _ le_rfl ≫ g₂ = (spMap (TrivSqZeroExt.fstHom R R M).toRingHom ⁻¹ᵁ V).ι ≫ x → (spMap β).resLE V _ le_rfl ≫ g₁ = (spMap β).resLE V _ le_rfl ≫ g₂ → g₁ = g₂ := by
  first | exact @GlobalTheory.PinchUniq.uniq | exact GlobalTheory.PinchUniq.uniq | (intros; apply GlobalTheory.PinchUniq.uniq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecTrivSqZeroExtIsPushout
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh GlobalTheory.AbTan
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Pinch

theorem pinch_main : ∀ (R : Type) [CommRing R] (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M] [Module R M] [IsScalarTower R B M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M] (β : TrivSqZeroExt R M →+* TrivSqZeroExt B M), IsSum β (algebraMap R B) id → ∀ (X : Scheme.{0}) (x : Sp R ⟶ X) (z : Sp (TrivSqZeroExt B M) ⟶ X), spMap (TrivSqZeroExt.fstHom B B M).toRingHom ≫ z = spMap (algebraMap R B) ≫ x → ∃! z₀ : Sp (TrivSqZeroExt R M) ⟶ X, spMap (TrivSqZeroExt.fstHom R R M).toRingHom ≫ z₀ = x ∧ spMap β ≫ z₀ = z := by
  intro R _ B M _ _ _ _ _ _ _ _ _ _ β hβ X x z hxz
  let T := Sp (TrivSqZeroExt R M)
  let i : Sp R ⟶ T := spMap (TrivSqZeroExt.fstHom R R M).toRingHom
  let j : Sp (TrivSqZeroExt B M) ⟶ T := spMap β
  have hcov0 := fun q => exists_basicOpen_inl (M := M) x q
  have EO := GlobalTheory.T.trivSqZeroExt_pinch_exists_extend_basicOpen R B M β hβ X x z hxz
  have UO := GlobalTheory.T.trivSqZeroExt_pinch_basicOpen_morphism_unique R B M β hβ X x
  have RES : ∀ {Y' : Scheme.{0}} (f' : Y' ⟶ T) {V V' : T.Opens} (h : V' ≤ V) (g : V.toScheme ⟶ X) (w : Y' ⟶ X),
      f'.resLE V _ le_rfl ≫ g = (f' ⁻¹ᵁ V).ι ≫ w → f'.resLE V' _ le_rfl ≫ T.homOfLE h ≫ g = (f' ⁻¹ᵁ V').ι ≫ w := by
    intro Y' f' V V' h g w hg
    have e : f'.resLE V' _ le_rfl ≫ T.homOfLE h = Y'.homOfLE (f'.preimage_mono h) ≫ f'.resLE V _ le_rfl := by
      rw [← cancel_mono V.ι]
      simp only [Category.assoc, Scheme.homOfLE_ι, Scheme.Hom.resLE_comp_ι, Scheme.homOfLE_ι_assoc]
    rw [reassoc_of% e, hg, Scheme.homOfLE_ι_assoc]
  let Idx := {p : Γ(T, ⊤) × X.affineOpens // i ⁻¹ᵁ T.basicOpen p.1 ≤ x ⁻¹ᵁ p.2.1}
  have hcov : TopologicalSpace.IsOpenCover (fun p : Idx => T.basicOpen p.1.1) := by
    rw [TopologicalSpace.IsOpenCover, eq_top_iff]
    intro q _
    obtain ⟨s, U, hq, hle⟩ := hcov0 q
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨(s, U), hle⟩, hq⟩
  let 𝒰 := T.openCoverOfIsOpenCover _ hcov
  choose g hg using fun p : Idx => EO p.1.1 p.1.2 p.2
  have hc : ∀ a b : Idx, pullback.fst (𝒰.f a) (𝒰.f b) ≫ g a = pullback.snd (𝒰.f a) (𝒰.f b) ≫ g b := by
    intro a b
    have hP := isPullback_opens_inf (T.basicOpen a.1.1) (T.basicOpen b.1.1)
    change pullback.fst (T.basicOpen a.1.1).ι (T.basicOpen b.1.1).ι ≫ g a =
      pullback.snd (T.basicOpen a.1.1).ι (T.basicOpen b.1.1).ι ≫ g b
    rw [← cancel_epi hP.isoPullback.hom, IsPullback.isoPullback_hom_fst_assoc, IsPullback.isoPullback_hom_snd_assoc]
    refine UO _ (a.1.1 * b.1.1) (T.basicOpen_mul _ _).symm a.1.2 ((i.preimage_mono inf_le_left).trans a.2) _ _
      (RES i _ _ x (hg a).1) (RES i _ _ x (hg b).1) ?_
    rw [RES j _ _ z (hg a).2, RES j _ _ z (hg b).2]
  let z₀ := 𝒰.glueMorphisms g hc
  have hz₀ : ∀ a : Idx, (T.basicOpen a.1.1).ι ≫ z₀ = g a := fun a => 𝒰.ι_glueMorphisms g hc a
  have hi : i ≫ z₀ = x := by
    have hcovR : TopologicalSpace.IsOpenCover (fun p : Idx => i ⁻¹ᵁ T.basicOpen p.1.1) := by
      rw [TopologicalSpace.IsOpenCover, ← Scheme.Hom.preimage_iSup, hcov, Scheme.Hom.preimage_top]
    refine Scheme.Cover.hom_ext ((Sp R).openCoverOfIsOpenCover _ hcovR) _ _ fun a => ?_
    change (i ⁻¹ᵁ T.basicOpen a.1.1).ι ≫ i ≫ z₀ = (i ⁻¹ᵁ T.basicOpen a.1.1).ι ≫ x
    rw [← (hg a).1, ← hz₀ a, ← Category.assoc, ← Scheme.Hom.resLE_comp_ι i (le_rfl), Category.assoc]
  have hj : j ≫ z₀ = z := by
    have hcovA : TopologicalSpace.IsOpenCover (fun p : Idx => j ⁻¹ᵁ T.basicOpen p.1.1) := by
      rw [TopologicalSpace.IsOpenCover, ← Scheme.Hom.preimage_iSup, hcov, Scheme.Hom.preimage_top]
    refine Scheme.Cover.hom_ext ((Sp (TrivSqZeroExt B M)).openCoverOfIsOpenCover _ hcovA) _ _ fun a => ?_
    change (j ⁻¹ᵁ T.basicOpen a.1.1).ι ≫ j ≫ z₀ = (j ⁻¹ᵁ T.basicOpen a.1.1).ι ≫ z
    rw [← (hg a).2, ← hz₀ a, ← Category.assoc, ← Scheme.Hom.resLE_comp_ι j (le_rfl), Category.assoc]
  refine ⟨z₀, ⟨hi, hj⟩, fun z₁ ⟨h1, h2⟩ => ?_⟩
  refine Scheme.Cover.hom_ext 𝒰 _ _ fun a => ?_
  change (T.basicOpen a.1.1).ι ≫ z₁ = (T.basicOpen a.1.1).ι ≫ z₀
  rw [hz₀ a]
  refine UO _ a.1.1 rfl a.1.2 a.2 _ _ ?_ (hg a).1 ?_
  · rw [Scheme.Hom.resLE_comp_ι_assoc, h1]
  · rw [Scheme.Hom.resLE_comp_ι_assoc, h2, (hg a).2]

end GlobalTheory.Pinch
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecTrivSqZeroExtIsPushoutStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh GlobalTheory.AbTan
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spec_trivSqZeroExt_isPushout : ∀ (R : Type) [CommRing R] (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M] [Module R M] [IsScalarTower R B M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M] (β : TrivSqZeroExt R M →+* TrivSqZeroExt B M), IsSum β (algebraMap R B) id → ∀ (X : Scheme.{0}) (x : Sp R ⟶ X) (z : Sp (TrivSqZeroExt B M) ⟶ X), spMap (TrivSqZeroExt.fstHom B B M).toRingHom ≫ z = spMap (algebraMap R B) ≫ x → ∃! z₀ : Sp (TrivSqZeroExt R M) ⟶ X, spMap (TrivSqZeroExt.fstHom R R M).toRingHom ≫ z₀ = x ∧ spMap β ≫ z₀ = z := by
  first | exact @GlobalTheory.Pinch.pinch_main | exact GlobalTheory.Pinch.pinch_main | (intros; apply GlobalTheory.Pinch.pinch_main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToLinTransposeDot
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DualDatumDot

def dotL {O : Type} [CommRing O] {h : ℕ} (u : Fin h → O) : (Fin h → O) →ₗ[O] O where
  toFun m := u ⬝ᵥ m
  map_add' a b := dotProduct_add u a b
  map_smul' c m := by simp

theorem dot_single {O : Type} [CommRing O] {h : ℕ} (g : (Fin h → O) →ₗ[O] O) (x : Fin h → O) :
    (fun i => g (Pi.single i 1)) ⬝ᵥ x = g x := by
  have hx : x = ∑ i, x i • Pi.single i (1 : O) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hx]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, dotProduct, mul_comm]

theorem toLin'_transpose_dot {A O : Type} [CommRing A] [CommRing O] (θ : A →+* O) {h : ℕ}
    (X : Matrix (Fin h) (Fin h) A) (a b : Fin h → O) :
    Matrix.toLin' (Xᵀ.map θ) a ⬝ᵥ b = a ⬝ᵥ Matrix.toLin' (X.map θ) b := by
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.transpose_map, Matrix.mulVec_transpose,
    Matrix.dotProduct_mulVec]

end GlobalTheory.DualDatumDot

open GlobalTheory.DualDatumDot

namespace GlobalTheory.DualDatum

theorem hasDatum_dual : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ G : PDivGroup p O, HasDatum hε G → HasDatum hε G.dual := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε G ⟨D, e, fil, lie, hA, hB⟩
  have hζ : IsPrimitiveRoot (root ε).untilt p := by simpa [zeta] using hε 1
  obtain ⟨hdom, -, -, -, hν, hξ, -⟩ := GlobalTheory.AinfXi.ainf_local_xi_order p C v O hv ε hζ
  have hν' : nu ε ≠ 0 := fun h0 => hν (by rw [h0, map_zero])
  have hμ : Sandwich.mu ε ≠ 0 := by rw [← xi_mul_nu]; exact mul_ne_zero hξ hν'
  obtain ⟨-, h1, -, h3, -⟩ := HodgeTateBound.bound p C v O hv ε hζ ℤ_[p] _ D
  have := hv.isFractionRing
  have := hv.isIntegrallyClosed
  have : IsIntegrallyClosedIn O C :=
    (isIntegrallyClosed_iff_isIntegrallyClosedIn C).1 inferInstance
  obtain ⟨hfin, hproj⟩ := GlobalTheory.PDiv.omega_finite_projective p C v O hv G
  haveI := hfin
  haveI := hproj
  let θ := WittVector.fontaineTheta O p
  let D' := SelfDualFil.dualDatum hμ hξ D

  have perp : ∀ a, a ∈ D'.Fil ↔ ∀ f ∈ D.Fil, a ⬝ᵥ f = 0 := by
    intro a
    change Matrix.toLin' ((D.F)ᵀ.map θ) a = 0 ↔ _
    constructor
    · intro ha f hf
      obtain ⟨w, hw⟩ := h3 f hf
      have e1 : a ⬝ᵥ D.al w = 0 := by
        rw [show D.al w = Matrix.toLin' (D.F.map θ) w from rfl, ← toLin'_transpose_dot, ha,
          zero_dotProduct]
      rw [hw, dotProduct_smul, smul_eq_mul] at e1
      exact (mul_eq_zero.1 e1).resolve_left hν
    · intro ha
      funext i
      have h2 := ha _ (h1 ⟨Pi.single i 1, rfl⟩)
      rw [show D.al (Pi.single i 1) = Matrix.toLin' (D.F.map θ) (Pi.single i 1) from rfl,
        ← toLin'_transpose_dot] at h2
      simpa using h2

  let E : Fin G.height → G.Tate := fun i => e.symm (Pi.single i 1)
  have hexp : ∀ t, t = ∑ i, e t i • E i := by
    intro t
    apply e.injective
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    ext j
    simp [E, Finset.sum_apply, Pi.single_apply]
  let L : G.dual.Tate →ₗ[ℤ_[p]] (Fin G.height → ℤ_[p]) :=
    LinearMap.pi fun i => (epsEquiv hε).symm.toLinearMap ∘ₗ pairing G O (E i)
  have hL : ∀ χ i, L χ i = epsPairing hε G (E i) χ := fun _ _ => rfl
  have hflip := G.pairing_flip_bijective C
  have hLb : Function.Bijective L := by
    constructor
    · refine (injective_iff_map_eq_zero L).2 fun χ hχ => hflip.1 ?_
      rw [map_zero]
      refine LinearMap.ext fun t => ?_
      set_option synthInstance.maxHeartbeats 100000 in
        rw [LinearMap.flip_apply, LinearMap.zero_apply, hexp t, map_sum, LinearMap.sum_apply]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [map_smul, LinearMap.smul_apply, ← epsPairing_smul hε, ← hL, hχ]
      simp
    · intro c
      let φ : G.Tate →ₗ[ℤ_[p]] (PDivGroup.mu p O).Tate :=
        (epsEquiv hε).toLinearMap ∘ₗ (∑ i, c i • LinearMap.proj i) ∘ₗ e.toLinearMap
      obtain ⟨χ, hχ⟩ := hflip.2 φ
      refine ⟨χ, funext fun j => ?_⟩
      have hj : pairing G O (E j) χ = φ (E j) := LinearMap.congr_fun hχ (E j)
      rw [hL, epsPairing, hj]
      simp [φ, E, Pi.single_apply]
  let e' : G.dual.Tate ≃ₗ[ℤ_[p]] (Fin G.height → ℤ_[p]) := LinearEquiv.ofBijective L hLb
  have he' : ∀ χ i, e' χ i = epsPairing hε G (E i) χ := fun _ _ => rfl
  have hdualb : ∀ t i, epsPairing hε G t (e'.symm (Pi.single i 1)) = e t i := by
    intro t i
    have hj : ∀ j, epsPairing hε G (E j) (e'.symm (Pi.single i 1)) = (Pi.single i (1 : ℤ_[p]) : Fin G.height → ℤ_[p]) j := by
      intro j
      rw [← he', LinearEquiv.apply_symm_apply]
    have hs : ∀ s, epsPairing hε G s (e'.symm (Pi.single i 1)) =
        (epsEquiv hε).symm.toLinearMap ((pairing G O).flip (e'.symm (Pi.single i 1)) s) :=
      fun _ => rfl
    rw [hs]
    conv_lhs => rw [hexp t]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum]
    simp only [map_smul, ← hs, hj, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]

  let Φ : G.omega →ₗ[O] (Fin G.height → O) :=
    LinearMap.pi fun i => lie (D.Fil.mkQ (Pi.single i 1))
  let g : G.omega → (Fin G.height → O) →ₗ[O] O := fun w =>
    Module.Dual.eval O G.omega w ∘ₗ lie.toLinearMap ∘ₗ D.Fil.mkQ
  have hΦdot : ∀ w m, Φ w ⬝ᵥ m = lie (D.Fil.mkQ m) w := fun w m => dot_single (g w) m
  have hΦmem : ∀ w, Φ w ∈ D'.Fil := fun w => (perp _).2 fun f hf => by
    rw [hΦdot, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).2 hf, map_zero,
      LinearMap.zero_apply]
  have hΦinj : Function.Injective Φ := by
    refine (injective_iff_map_eq_zero Φ).2 fun w hw => ?_
    apply (Module.evalEquiv O G.omega).injective
    rw [map_zero]
    refine LinearMap.ext fun x => ?_
    obtain ⟨q, rfl⟩ := lie.surjective x
    obtain ⟨m, rfl⟩ := D.Fil.mkQ_surjective q
    rw [Module.evalEquiv_apply, Module.Dual.eval_apply, LinearMap.zero_apply, ← hΦdot, hw,
      zero_dotProduct]
  have hΦsurj : ∀ u ∈ D'.Fil, ∃ w, Φ w = u := by
    intro u hu
    have hle : D.Fil ≤ LinearMap.ker (dotL u) := fun f hf => (perp u).1 hu f hf
    let ℓ : G.Lie →ₗ[O] O := D.Fil.liftQ (dotL u) hle ∘ₗ lie.symm.toLinearMap
    refine ⟨(Module.evalEquiv O G.omega).symm ℓ, funext fun i => ?_⟩
    have hw : ∀ x : G.Lie, x ((Module.evalEquiv O G.omega).symm ℓ) = ℓ x := fun x => by
      have h5 := LinearMap.congr_fun ((Module.evalEquiv O G.omega).apply_symm_apply ℓ) x
      rwa [Module.evalEquiv_apply, Module.Dual.eval_apply] at h5
    change lie (D.Fil.mkQ (Pi.single i 1)) _ = u i
    rw [hw]
    change D.Fil.liftQ (dotL u) hle (lie.symm (lie (D.Fil.mkQ (Pi.single i 1)))) = u i
    rw [LinearEquiv.symm_apply_apply]
    change u ⬝ᵥ Pi.single i 1 = u i
    simp
  let filE : G.omega ≃ₗ[O] D'.Fil := LinearEquiv.ofBijective (Φ.codRestrict D'.Fil hΦmem)
    ⟨fun a b hab => hΦinj (congrArg Subtype.val hab), fun u => by
      obtain ⟨w, hw⟩ := hΦsurj u.1 u.2
      exact ⟨w, Subtype.ext hw⟩⟩
  let fil' : G.dual.dual.omega ≃ₗ[O] D'.Fil := (DlogSpan.pDivGroupOmegaBidualEquiv G).symm ≪≫ₗ filE

  let Ψ : (Fin G.height → O) →ₗ[O] G.dual.Lie :=
    LinearMap.mk₂ O (fun m w => m ⬝ᵥ (fil w : Fin G.height → O))
      (fun _ _ _ => by simp [add_dotProduct]) (fun _ _ _ => by simp)
      (fun _ _ _ => by simp [dotProduct_add]) (fun _ _ _ => by simp)
  have hΨ : ∀ m w, Ψ m w = m ⬝ᵥ (fil w : Fin G.height → O) := fun _ _ => rfl
  have hΨker : LinearMap.ker Ψ = D'.Fil := by
    ext m
    rw [LinearMap.mem_ker, perp]
    constructor
    · intro hm f hf
      obtain ⟨w, hw⟩ := fil.surjective ⟨f, hf⟩
      have h5 := LinearMap.congr_fun hm w
      rwa [hΨ, hw] at h5
    · intro hm
      exact LinearMap.ext fun w => hm _ (fil w).2
  haveI : Module.Projective O ((Fin G.height → O) ⧸ D.Fil) := Module.Projective.of_equiv lie.symm
  obtain ⟨s, hs⟩ := Module.projective_lifting_property D.Fil.mkQ LinearMap.id D.Fil.mkQ_surjective
  let r : (Fin G.height → O) →ₗ[O] D.Fil :=
    (LinearMap.id - s ∘ₗ D.Fil.mkQ).codRestrict D.Fil fun x => by
      rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, LinearMap.sub_apply, map_sub]
      have h5 := LinearMap.congr_fun hs (D.Fil.mkQ x)
      simp only [LinearMap.comp_apply, LinearMap.id_apply] at h5 ⊢
      rw [h5, sub_self]
  have hr : ∀ f : D.Fil, r f = f := fun f => by
    apply Subtype.ext
    have h0 : D.Fil.mkQ (f : Fin G.height → O) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2 f.2
    simp [r, h0]
  have hΨsurj : Function.Surjective Ψ := by
    intro y
    let φ : (Fin G.height → O) →ₗ[O] O := y ∘ₗ fil.symm.toLinearMap ∘ₗ r
    refine ⟨fun i => φ (Pi.single i 1), LinearMap.ext fun w => ?_⟩
    rw [hΨ, dot_single]
    simp [φ, hr]
  let lie' : ((Fin G.height → O) ⧸ D'.Fil) ≃ₗ[O] G.dual.Lie :=
    Submodule.quotEquivOfEq _ _ hΨker.symm ≪≫ₗ Ψ.quotKerEquivOfSurjective hΨsurj
  have hlie' : ∀ m, lie' (D'.Fil.mkQ m) = Ψ m := fun _ => rfl
  refine ⟨D', e', fil', lie', fun χ => ?_, fun y ψ => ?_⟩
  · have hf : fil' (hodgeTate G.dual χ) = filE (dlog G χ) := by
      simp only [fil', LinearEquiv.trans_apply]
      congr 1
      rw [LinearEquiv.symm_apply_eq, DlogSpan.pDivGroupOmegaBidual_dlog_eq_dual_hodgeTate]
    rw [hf]
    change _ = Φ (dlog G χ)
    funext i
    change _ = lie (D.Fil.mkQ (Pi.single i 1)) (dlog G χ)
    rw [← hB, LinearEquiv.symm_apply_apply]
    change Matrix.toLin' ((D.G)ᵀ.map θ) (toO e' χ) i =
      pairingO hε e (Matrix.toLin' (D.G.map θ) (Pi.single i 1)) χ
    simp [pairingO, toO, he', E, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, θ,
      Pi.single_apply, mul_comm]
  · obtain ⟨m, rfl⟩ := hΨsurj y
    obtain ⟨t, rfl⟩ := (tateCongr O G.bidual).surjective ψ
    have hl : lie'.symm (Ψ m) = D'.Fil.mkQ m := by
      rw [LinearEquiv.symm_apply_eq]
      exact (hlie' m).symm
    rw [hl]
    change pairingO hε e' (D'.bb m) (tateMap G G.dual.dual O G.bidual.hom t) =
      Ψ m (dlog G.dual (tateMap G G.dual.dual O G.bidual.hom t))
    rw [← hodgeTate_apply, hΨ, ← hA]
    have hp : ∀ i, epsPairing hε G.dual (e'.symm (Pi.single i 1))
        (tateMap G G.dual.dual O G.bidual.hom t) = e t i := fun i => by
      rw [epsPairing, DetInv.pairing_dual_bidual]
      exact hdualb t i
    simp only [pairingO, hp]
    change Matrix.toLin' ((D.F)ᵀ.map θ) m ⬝ᵥ toO e t = m ⬝ᵥ Matrix.toLin' (D.F.map θ) (toO e t)
    rw [toLin'_transpose_dot]

end GlobalTheory.DualDatum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChowFormZeroSetExtensionFieldIffCommonConeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialSolvabilityTransferAlgClosedFieldsStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialSolvabilityTransferAlgClosedFields
open MvPolynomial

namespace GlobalTheory.PointTransfer

theorem exists_algHom_algebraicClosure (F A : Type) [Field F] [CommRing A] [Nontrivial A] [Algebra F A]
    [Algebra.FiniteType F A] : Nonempty (A →ₐ[F] AlgebraicClosure F) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite F (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing F (A ⧸ m)
  exact ⟨(IsAlgClosed.lift : (A ⧸ m) →ₐ[F] AlgebraicClosure F).comp (Ideal.Quotient.mkₐ F m)⟩

theorem exists_common_zero {Ω τ : Type} [Field Ω] [IsAlgClosed Ω] [Finite τ]
    (I : Ideal (MvPolynomial τ Ω)) (hI : I ≠ ⊤) : ∃ y : τ → Ω, ∀ f ∈ I, aeval y f = 0 := by
  by_contra h
  have he : zeroLocus Ω I = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro y hy
    exact h ⟨y, fun f hf => hy f hf⟩
  have h2 := MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := Ω) I
  rw [he, MvPolynomial.vanishingIdeal_empty] at h2
  exact hI (Ideal.radical_eq_top.1 h2.symm)

noncomputable def partialEval {F A σ τ : Type} [CommRing F] [CommRing A] [Algebra F A] (u : σ → A) :
    MvPolynomial (σ ⊕ τ) F →ₐ[F] MvPolynomial τ A :=
  aeval (Sum.elim (fun s => C (u s)) X)

theorem eval₂Hom_partialEval {F A B σ τ : Type} [CommRing F] [CommRing A] [CommRing B] [Algebra F A]
    [Algebra F B] (ψ : A →ₐ[F] B) (u : σ → A) (y : τ → B) (g : MvPolynomial (σ ⊕ τ) F) :
    eval₂Hom (ψ : A →+* B) y (partialEval u g) = aeval (Sum.elim (fun s => ψ (u s)) y) g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [partialEval, MvPolynomial.algebraMap_apply]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp]
    cases i <;> simp [partialEval]

theorem map_partialEval {F A B σ τ : Type} [CommRing F] [CommRing A] [CommRing B] [Algebra F A]
    [Algebra F B] (ψ : A →ₐ[F] B) (u : σ → A) (g : MvPolynomial (σ ⊕ τ) F) :
    MvPolynomial.map (ψ : A →+* B) (partialEval u g) = partialEval (fun s => ψ (u s)) g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [partialEval, MvPolynomial.algebraMap_apply]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp]
    cases i <;> simp [partialEval]

theorem solvable_transfer (F σ τ : Type) [Field F] [Finite σ] [Finite τ]
    (P : Ideal (MvPolynomial σ F)) (J : Ideal (MvPolynomial (σ ⊕ τ) F))
    (H : ∀ u : σ → AlgebraicClosure F, (∀ g ∈ P, aeval u g = 0) →
      ∃ y : τ → AlgebraicClosure F, ∀ g ∈ J, aeval (Sum.elim u y) g = 0)
    (Ω : Type) [Field Ω] [Algebra F Ω] [IsAlgClosed Ω] (u : σ → Ω)
    (hu : ∀ g ∈ P, aeval u g = 0) :
    ∃ y : τ → Ω, ∀ g ∈ J, aeval (Sum.elim u y) g = 0 := by
  have hI : J.map (partialEval (F := F) (τ := τ) u) ≠ ⊤ := by
    intro htop
    have h1 : (1 : MvPolynomial τ Ω) ∈ Submodule.span (MvPolynomial τ Ω)
        ((partialEval (F := F) (τ := τ) u) '' (J : Set _)) := by
      have : (1 : MvPolynomial τ Ω) ∈ J.map (partialEval (F := F) (τ := τ) u) := by
        rw [htop]; trivial
      exact this
    obtain ⟨n, c, g, hsum⟩ := Submodule.mem_span_set'.1 h1
    choose g' hg'J hg' using fun i => (g i).2
    let S : Set Ω := Set.range u ∪ ⋃ i, ((c i).coeffs : Set Ω)
    have hS : S.Finite :=
      (Set.finite_range u).union (Set.finite_iUnion fun i => (c i).coeffs.finite_toSet)
    let A : Subalgebra F Ω := Algebra.adjoin F S
    haveI : Algebra.FiniteType F A :=
      (Subalgebra.fg_iff_finiteType A).1 (Subalgebra.fg_def.2 ⟨S, hS, rfl⟩)
    obtain ⟨ψ⟩ := exists_algHom_algebraicClosure F A
    let uA : σ → A := fun s => ⟨u s, Algebra.subset_adjoin (Or.inl ⟨s, rfl⟩)⟩
    have hc : ∀ i, c i ∈ Set.range (MvPolynomial.map (σ := τ) (A.val : A →+* Ω)) := by
      intro i
      rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
      intro a ha
      exact ⟨⟨a, Algebra.subset_adjoin (Or.inr (Set.mem_iUnion.2 ⟨i, ha⟩))⟩, rfl⟩
    choose c' hc' using hc
    have hid : ∑ i, c' i * partialEval uA (g' i) = 1 := by
      apply MvPolynomial.map_injective (A.val : A →+* Ω) Subtype.val_injective
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_one, ← hsum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, hc', map_partialEval, smul_eq_mul, ← hg' i]
      rfl
    obtain ⟨y, hy⟩ := H (fun s => ψ (uA s)) (by
      intro p hp
      have h0 : aeval uA p = 0 := by
        apply Subtype.val_injective
        have := DFunLike.congr_fun (MvPolynomial.comp_aeval uA A.val) p
        exact this.trans (hu p hp)
      have := DFunLike.congr_fun (MvPolynomial.comp_aeval uA ψ) p
      rw [← this, AlgHom.comp_apply, h0, map_zero])
    have := congrArg (eval₂Hom (ψ : A →+* AlgebraicClosure F) y) hid
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_one, map_sum, Finset.sum_eq_zero] at this
    · exact zero_ne_one this
    · intro i _
      rw [map_mul, eval₂Hom_partialEval, hy _ (hg'J i), mul_zero]
  obtain ⟨y, hy⟩ := exists_common_zero _ hI
  refine ⟨y, fun g hg => ?_⟩
  have h := hy _ (Ideal.mem_map_of_mem _ hg)
  have h2 := eval₂Hom_partialEval (AlgHom.id F Ω) u y g
  exact h2.symm.trans h

end GlobalTheory.PointTransfer
end

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice GlobalTheory.HSShort
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomial_solvability_transfer_algClosed_fields : ∀ (F σ τ : Type) [Field F] [Finite σ] [Finite τ] (P : Ideal (MvPolynomial σ F)) (J : Ideal (MvPolynomial (σ ⊕ τ) F)), (∀ u : σ → AlgebraicClosure F, (∀ g ∈ P, aeval u g = 0) → ∃ y : τ → AlgebraicClosure F, ∀ g ∈ J, aeval (Sum.elim u y) g = 0) → ∀ (Ω : Type) [Field Ω] [Algebra F Ω] [IsAlgClosed Ω] (u : σ → Ω), (∀ g ∈ P, aeval u g = 0) → ∃ y : τ → Ω, ∀ g ∈ J, aeval (Sum.elim u y) g = 0 := by
  first | exact @GlobalTheory.PointTransfer.solvable_transfer | exact GlobalTheory.PointTransfer.solvable_transfer | (intros; apply GlobalTheory.PointTransfer.solvable_transfer <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChowFormZeroSetExtensionFieldIffCommonConeZero
set_option autoImplicit false

noncomputable section

open MvPolynomial
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.HSChoice

namespace GlobalTheory.ChowZeroExt

def incIdeal {F : Type} [Field F] (B : ℕ) {N : ℕ} (I : Ideal (MvPolynomial (Fin N) F)) :
    Ideal (MvPolynomial ((Fin B × Fin N) ⊕ (Fin N ⊕ Fin N)) F) :=
  Ideal.span ((rename (fun j => Sum.inr (Sum.inl j)) '' (I : Set (MvPolynomial (Fin N) F))) ∪
    (Set.range (fun i : Fin B => ∑ j, X (Sum.inl (i, j)) * X (Sum.inr (Sum.inl j))) ∪
      {∑ j, X (Sum.inr (Sum.inr j)) * X (Sum.inr (Sum.inl j)) - 1}))

theorem forall_span_iff {F Ω ι : Type} [Field F] [Field Ω] [Algebra F Ω] (S : Set (MvPolynomial ι F))
    (x : ι → Ω) : (∀ g ∈ Ideal.span S, aeval x g = 0) ↔ ∀ g ∈ S, aeval x g = 0 := by
  refine ⟨fun h g hg => h g (Ideal.subset_span hg), fun h g hg => ?_⟩
  have : Ideal.span S ≤ RingHom.ker (aeval x : MvPolynomial ι F →ₐ[F] Ω) :=
    Ideal.span_le.2 fun g hg => h g hg
  exact this hg

theorem forall_incIdeal_iff {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] {B N : ℕ}
    (I : Ideal (MvPolynomial (Fin N) F)) (x : (Fin B × Fin N) ⊕ (Fin N ⊕ Fin N) → Ω) :
    (∀ g ∈ incIdeal B I, aeval x g = 0) ↔
      (∀ g ∈ I, aeval (fun j => x (Sum.inr (Sum.inl j))) g = 0) ∧
      (∀ i, ∑ j, x (Sum.inl (i, j)) * x (Sum.inr (Sum.inl j)) = 0) ∧
      ∑ j, x (Sum.inr (Sum.inr j)) * x (Sum.inr (Sum.inl j)) = 1 := by
  rw [incIdeal, forall_span_iff]
  constructor
  · intro h
    refine ⟨fun g hg => ?_, fun i => ?_, ?_⟩
    · have := h _ (Or.inl ⟨g, hg, rfl⟩)
      rwa [aeval_rename] at this
    · simpa using h _ (Or.inr (Or.inl ⟨i, rfl⟩))
    · simpa [sub_eq_zero] using h _ (Or.inr (Or.inr rfl))
  · rintro ⟨h1, h2, h3⟩ g (⟨g, hg, rfl⟩ | ⟨i, rfl⟩ | rfl)
    · rw [aeval_rename]
      exact h1 g hg
    · simpa using h2 i
    · simpa [sub_eq_zero] using h3

theorem exists_dual {Ω : Type} [Field Ω] {N : ℕ} {y : Fin N → Ω} (hy : y ≠ 0) :
    ∃ z : Fin N → Ω, ∑ j, z j * y j = 1 := by
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hy
  refine ⟨Pi.single j (y j)⁻¹, ?_⟩
  rw [Finset.sum_eq_single j]
  · rw [Pi.single_eq_same]
    exact inv_mul_cancel₀ hj
  · intro k _ hk
    rw [Pi.single_eq_of_ne hk, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem ne_zero_of_dual {Ω : Type} [Field Ω] {N : ℕ} {y z : Fin N → Ω} (h : ∑ j, z j * y j = 1) :
    y ≠ 0 := by
  rintro rfl
  simp at h

variable {F : Type} [Field F] {D N d : ℕ} {I : Ideal (MvPolynomial (Fin N) F)}
  {f : MvPolynomial (Fin (D + 1) × Fin N) F}

theorem aeval_eq_zero_of_common_zero (hf : IsChowForm I D d f) {Ω : Type} [Field Ω] [Algebra F Ω]
    (u : Fin (D + 1) × Fin N → Ω) (y : Fin N → Ω) (hy : y ≠ 0) (hI : ∀ g ∈ I, aeval y g = 0)
    (hu : ∀ i, ∑ j, u (i, j) * y j = 0) : aeval u f = 0 := by
  obtain ⟨z, hz⟩ := exists_dual hy
  have key := GlobalTheory.T.vanish_transfer_of_vanish_over_algebraicClosure F _ (incIdeal (D + 1) I) (rename Sum.inl f) (fun x hx => by
    obtain ⟨h1, h2, h3⟩ := (forall_incIdeal_iff I x).1 hx
    rw [aeval_rename]
    exact (hf.zero_iff _).2 ⟨_, ne_zero_of_dual h3, h1, h2⟩) Ω (Sum.elim u (Sum.elim y z))
    ((forall_incIdeal_iff I _).2 ⟨hI, hu, hz⟩)
  rwa [aeval_rename] at key

theorem exists_common_zero (hf : IsChowForm I D d f) {Ω : Type} [Field Ω] [Algebra F Ω] [IsAlgClosed Ω]
    (u : Fin (D + 1) × Fin N → Ω) (hu : aeval u f = 0) :
    ∃ y : Fin N → Ω, y ≠ 0 ∧ (∀ g ∈ I, aeval y g = 0) ∧ ∀ i, ∑ j, u (i, j) * y j = 0 := by
  obtain ⟨w, hw⟩ := GlobalTheory.T.polynomial_solvability_transfer_algClosed_fields F _ _ (Ideal.span {f}) (incIdeal (D + 1) I) (fun v hv => by
    obtain ⟨y, hy, h1, h2⟩ := (hf.zero_iff v).1 (hv f (Ideal.subset_span rfl))
    obtain ⟨z, hz⟩ := exists_dual hy
    exact ⟨Sum.elim y z, (forall_incIdeal_iff I _).2 ⟨h1, h2, hz⟩⟩) Ω u
    ((forall_span_iff _ _).2 (by rintro g rfl; exact hu))
  obtain ⟨h1, h2, h3⟩ := (forall_incIdeal_iff I _).1 hw
  exact ⟨_, ne_zero_of_dual h3, h1, h2⟩

theorem forall_join_iff {Ω : Type} [Field Ω] (s : Fin D → Fin N → Ω) (ξ y : Fin N → Ω) :
    (∀ i, ∑ j, join s ξ (i, j) * y j = 0) ↔ (∀ i, ∑ j, s i j * y j = 0) ∧ ∑ j, ξ j * y j = 0 := by
  rw [Fin.forall_fin_succ']
  simp [join]

theorem zero_set_ext : ∀ (F : Type) [Field F] [CharZero F] (D N d : ℕ) (I : Ideal (MvPolynomial (Fin N) F))
    (f : MvPolynomial (Fin (D + 1) × Fin N) F), IsChowForm I D d f →
    (∀ (Ω : Type) [Field Ω] [Algebra F Ω] (s : Fin D → Fin N → Ω) (ξ y : Fin N → Ω), y ≠ 0 →
      (∀ g ∈ I, aeval y g = 0) → (∀ i, ∑ j, s i j * y j = 0) → ∑ j, ξ j * y j = 0 →
      aeval (join s ξ) f = 0) ∧
    (∀ (Ω : Type) [Field Ω] [Algebra F Ω] [IsAlgClosed Ω] (s : Fin D → Fin N → Ω) (ξ : Fin N → Ω),
      aeval (join s ξ) f = 0 → ∃ y : Fin N → Ω, y ≠ 0 ∧ (∀ g ∈ I, aeval y g = 0) ∧
        (∀ i, ∑ j, s i j * y j = 0) ∧ ∑ j, ξ j * y j = 0) := by
  intro F _ _ D N d I f hf
  refine ⟨fun Ω _ _ s ξ y hy hI hs hξ => ?_, fun Ω _ _ _ s ξ h => ?_⟩
  · exact aeval_eq_zero_of_common_zero hf _ y hy hI ((forall_join_iff s ξ y).2 ⟨hs, hξ⟩)
  · obtain ⟨y, hy, h1, h2⟩ := exists_common_zero hf _ h
    exact ⟨y, hy, h1, (forall_join_iff s ξ y).1 h2⟩

end GlobalTheory.ChowZeroExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChowFormZeroSetExtensionFieldIffCommonConeZeroStatement
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice GlobalTheory.HSShort
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chowForm_zeroSet_extensionField_iff_common_cone_zero : ∀ (F : Type) [Field F] [CharZero F] (D N d : ℕ) (I : Ideal (MvPolynomial (Fin N) F)) (f : MvPolynomial (Fin (D + 1) × Fin N) F), IsChowForm I D d f → (∀ (Ω : Type) [Field Ω] [Algebra F Ω] (s : Fin D → Fin N → Ω) (ξ y : Fin N → Ω), y ≠ 0 → (∀ g ∈ I, aeval y g = 0) → (∀ i, ∑ j, s i j * y j = 0) → ∑ j, ξ j * y j = 0 → aeval (join s ξ) f = 0) ∧ (∀ (Ω : Type) [Field Ω] [Algebra F Ω] [IsAlgClosed Ω] (s : Fin D → Fin N → Ω) (ξ : Fin N → Ω), aeval (join s ξ) f = 0 → ∃ y : Fin N → Ω, y ≠ 0 ∧ (∀ g ∈ I, aeval y g = 0) ∧ (∀ i, ∑ j, s i j * y j = 0) ∧ ∑ j, ξ j * y j = 0) := by
  first | exact @GlobalTheory.ChowZeroExt.zero_set_ext | exact GlobalTheory.ChowZeroExt.zero_set_ext | (intros; apply GlobalTheory.ChowZeroExt.zero_set_ext <;> assumption)
end
end
