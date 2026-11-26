module

public import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ObstructionLifting.H1StructureDimLe
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FibAc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff

@[expose] public section

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.AffineCoverOfProductFibres
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.AffineCoverOfProductFibres
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.PointSurjectivity

noncomputable section

namespace GlobalTheory.CompanionTheory.PointSurjectivity

theorem over_affineOpen_of_isPullback : ∀ {k : Type} [Field k] {X T Z : Scheme.{0}} (a : X ⟶ Sp k) (b : T ⟶ Sp k) (p : Z ⟶ X) (q : Z ⟶ T)
    (H : IsPullback p q a b) {V : T.Opens} (hV : IsAffineOpen V) {κ : Type} [LinearOrder κ] [Fintype κ]
    (D : κ → X.Opens) (hD : ∀ i, IsAffineOpen (D i)) (hc : ⨆ i, D i = ⊤) (G : LB Z) (hG : G.IsLB), (∀ i, IsAffineOpen (p ⁻¹ᵁ D i ⊓ q ⁻¹ᵁ V)) ∧
    ∃ (Y : Scheme.{0}) (π : Y ⟶ Z) (f : Y ⟶ Spec Γ(T, V)) (E : κ → Y.Opens),
      IsPullback π f q hV.fromSpec ∧ (∀ i, IsAffineOpen (E i)) ∧ ⨆ i, E i = ⊤ ∧
      Nonempty (cechLB (f ≫ hV.fromSpec ≫ b) (G.pull π) E ≅ cechLB (p ≫ a) G fun i => p ⁻¹ᵁ D i ⊓ q ⁻¹ᵁ V) := by
  intro k _ X T Z a b p q H V hV κ _ _ D hD hc G hG
  let π := pullback.fst q hV.fromSpec
  let f := pullback.snd q hV.fromSpec
  have H₁ : IsPullback π f q hV.fromSpec := IsPullback.of_hasPullback _ _
  have H' : IsPullback f (π ≫ p) (hV.fromSpec ≫ b) a := H₁.flip.paste_vert H.flip
  have hq : IsAffineHom (π ≫ p) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) H' inferInstance
  have hr : π.opensRange = q ⁻¹ᵁ V := by
    ext1
    rw [Scheme.Hom.coe_opensRange]
    erw [Scheme.Pullback.range_fst]
    rw [hV.range_fromSpec]
    rfl
  have hE (i : κ) : π ⁻¹ᵁ (p ⁻¹ᵁ D i ⊓ q ⁻¹ᵁ V) = (π ≫ p) ⁻¹ᵁ D i := by
    rw [← hr, Scheme.Hom.preimage_inf, Scheme.Hom.preimage_opensRange, inf_top_eq,
      Scheme.Hom.comp_preimage]
  have hA (i : κ) : IsAffineOpen ((π ≫ p) ⁻¹ᵁ D i) := (hD i).preimage _
  refine ⟨fun i => ?_, _, π, f, fun i => π ⁻¹ᵁ (p ⁻¹ᵁ D i ⊓ q ⁻¹ᵁ V), H₁,
    fun i => (congrArg IsAffineOpen (hE i)).mpr (hA i), ?_, ?_⟩
  · have h := (hA i).image_of_isOpenImmersion π
    rwa [Scheme.Hom.comp_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf, hr, inf_comm] at h
  · simp only [hE]
    rw [← Scheme.Hom.preimage_iSup, hc, Scheme.Hom.preimage_top]
  · have e : f ≫ hV.fromSpec ≫ b = π ≫ p ≫ a := by
      rw [← H₁.w_assoc, H.w]
    rw [e]
    exact cechLB_pull_iso_of_isOpenImmersion k _ _ G _ π κ _ hG fun i => hr ▸ inf_le_right

end GlobalTheory.CompanionTheory.PointSurjectivity
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.AffineCoverOfProductFibresStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.PointSurjectivity

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affine_cover_of_product_fibres : ∀ {k : Type} [Field k] {X T Z : Scheme.{0}} (a : X ⟶ Sp k) (b : T ⟶ Sp k) (p : Z ⟶ X) (q : Z ⟶ T)
    (H : IsPullback p q a b) {V : T.Opens} (hV : IsAffineOpen V) {κ : Type} [LinearOrder κ] [Fintype κ]
    (D : κ → X.Opens) (hD : ∀ i, IsAffineOpen (D i)) (hc : ⨆ i, D i = ⊤) (G : LB Z) (hG : G.IsLB), (∀ i, IsAffineOpen (p ⁻¹ᵁ D i ⊓ q ⁻¹ᵁ V)) ∧
    ∃ (Y : Scheme.{0}) (π : Y ⟶ Z) (f : Y ⟶ Spec Γ(T, V)) (E : κ → Y.Opens),
      IsPullback π f q hV.fromSpec ∧ (∀ i, IsAffineOpen (E i)) ∧ ⨆ i, E i = ⊤ ∧
      Nonempty (cechLB (f ≫ hV.fromSpec ≫ b) (G.pull π) E ≅ cechLB (p ≫ a) G fun i => p ⁻¹ᵁ D i ⊓ q ⁻¹ᵁ V) := by
  first | exact @GlobalTheory.CompanionTheory.PointSurjectivity.over_affineOpen_of_isPullback | exact GlobalTheory.CompanionTheory.PointSurjectivity.over_affineOpen_of_isPullback | (intros; apply GlobalTheory.CompanionTheory.PointSurjectivity.over_affineOpen_of_isPullback <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FlatDescentOfUnits
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FlatDescentOfUnits
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.FnDesc

theorem exists_app_eq_of_lfp {X Y : Scheme.{0}} (π : X ⟶ Y) [Flat π] [Surjective π]
    [LocallyOfFinitePresentation π] (U : Y.Opens) (f : Γ(X, π ⁻¹ᵁ U))
    (hf : ∀ (Z : Scheme.{0}) (g₁ g₂ : Z ⟶ X) (h₁ : ⊤ ≤ g₁ ⁻¹ᵁ (π ⁻¹ᵁ U))
      (h₂ : ⊤ ≤ g₂ ⁻¹ᵁ (π ⁻¹ᵁ U)), g₁ ≫ π = g₂ ≫ π →
      (g₁.appLE _ ⊤ h₁).hom f = (g₂.appLE _ ⊤ h₂).hom f) :
    ∃ a, (π.app U).hom a = f := by
  have : Surjective (π ∣_ U) := IsZariskiLocalAtTarget.restrict (P := @Surjective) ‹_› U
  have p := isPullback_morphismRestrict π U
  have : Flat (π ∣_ U) := MorphismProperty.of_isPullback (P := @Flat) p.flip ‹_›
  have : LocallyOfFinitePresentation (π ∣_ U) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) p.flip ‹_›
  obtain ⟨b, hb⟩ := GlobalTheory.FunDescent.exists_appTop_eq (π ∣_ U) ((GlobalTheory.FunDescent.res (π ⁻¹ᵁ U)).hom f) (by
    intro Z g₁ g₂ e
    have k : ∀ g : Z ⟶ (π ⁻¹ᵁ U).toScheme, ⊤ ≤ (g ≫ (π ⁻¹ᵁ U).ι) ⁻¹ᵁ (π ⁻¹ᵁ U) := by
      intro g; simp
    have := hf Z (g₁ ≫ (π ⁻¹ᵁ U).ι) (g₂ ≫ (π ⁻¹ᵁ U).ι) (k _) (k _) (by
      rw [Category.assoc, Category.assoc, ← morphismRestrict_ι, reassoc_of% e])
    rw [← GlobalTheory.FunDescent.res_comp_appTop _ g₁ _ rfl, ← GlobalTheory.FunDescent.res_comp_appTop _ g₂ _ rfl] at this
    exact this)
  obtain ⟨a, rfl⟩ := (GlobalTheory.FunDescent.res_bijective U).2 b
  refine ⟨a, (GlobalTheory.FunDescent.res_bijective _).1 ?_⟩
  rw [← GlobalTheory.FunDescent.res_square_apply, hb]

theorem units_descend :
    ∀ {P Q : Scheme.{0}} (f : P ⟶ Q), Flat f → LocallyOfFinitePresentation f → Surjective f → ∀ V : Q.Opens,
    Function.Injective (pullU f V) ∧ ∀ a : Γ(P, f ⁻¹ᵁ V)ˣ,
      (∀ (W : Scheme.{0}) (b c : W ⟶ P), b ≫ f = c ≫ f → ∀ w : W, f (b w) ∈ V →
        gm b w (f ⁻¹ᵁ V) a = gm c w (f ⁻¹ᵁ V) a) → ∃ s : Γ(Q, V)ˣ, pullU f V s = a := by
  intro P Q f _ _ _ V
  refine ⟨fun a b h => Units.ext (GlobalTheory.FunDescent.app_injective f V (congrArg Units.val h)), fun a ha => ?_⟩
  obtain ⟨t, ht⟩ := exists_app_eq_of_lfp f V a.val (fun Z g₁ g₂ h₁ h₂ e => by
    have k : ∀ (g : Z ⟶ P) (h : ⊤ ≤ g ⁻¹ᵁ (f ⁻¹ᵁ V)) (z : Z),
        gm (𝟙 Z) z ⊤ (res h (pullU g _ a)) = gm g z (f ⁻¹ᵁ V) a := fun g h z =>
      (gm_res (𝟙 Z) z h trivial _).trans ((gm_pull (𝟙 Z) g z _ (h trivial) _).trans (by
        rw [Category.id_comp]))
    have : res h₁ (pullU g₁ _ a) = res h₂ (pullU g₂ _ a) := unit_ext fun z _ =>
      (k g₁ h₁ z).trans ((ha Z g₁ g₂ e z (h₁ trivial)).trans (k g₂ h₂ z).symm)
    exact congrArg Units.val this)
  obtain ⟨s, rfl⟩ := GlobalTheory.FunDescent.isUnit_of_isUnit_app f V t (ht ▸ a.isUnit)
  exact ⟨s, Units.ext ht⟩

end GlobalTheory.CompanionTheory.FnDesc
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FlatDescentOfUnitsStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_descent_of_units : ∀ {P Q : Scheme.{0}} (f : P ⟶ Q), Flat f → LocallyOfFinitePresentation f → Surjective f → ∀ V : Q.Opens,
    Function.Injective (pullU f V) ∧ ∀ a : Γ(P, f ⁻¹ᵁ V)ˣ,
      (∀ (W : Scheme.{0}) (b c : W ⟶ P), b ≫ f = c ≫ f → ∀ w : W, f (b w) ∈ V →
        gm b w (f ⁻¹ᵁ V) a = gm c w (f ⁻¹ᵁ V) a) → ∃ s : Γ(Q, V)ˣ, pullU f V s = a := by
  first | exact @GlobalTheory.CompanionTheory.FnDesc.units_descend | exact GlobalTheory.CompanionTheory.FnDesc.units_descend | (intros; apply GlobalTheory.CompanionTheory.FnDesc.units_descend <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FibrewiseAcyclicityBaseChange
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FibrewiseAcyclicityBaseChange
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.PointSurjectivity

namespace GlobalTheory.CompanionTheory.PointSurjectivity

theorem fibAc_of_closed_fibres : ∀ {k : Type} [Field k] [IsAlgClosed k] {X T Z : Scheme.{0}} (a : X ⟶ Sp k) (b : T ⟶ Sp k) (p : Z ⟶ X)
    (q : Z ⟶ T) (H : IsPullback p q a b) (ha : IsProjBy a) [IsSeparated a] [Flat a] (G : LB Z) (hG : G.IsLB)
    (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ T) [LocallyOfFiniteType (t ≫ b)] (Y : Scheme.{0})
    (π : Y ⟶ Z) (f : Y ⟶ Spec (CommRingCat.of R)) (Hy : IsPullback π f q t)
    (hfib : ∀ (s : Sp k ⟶ Spec (CommRingCat.of R)) (σ : X ⟶ Z), s ≫ t ≫ b = 𝟙 _ → σ ≫ p = 𝟙 X →
      σ ≫ q = a ≫ s ≫ t → FibAc a (G.pull σ)), FibAc f (G.pull π) := by
  intro k _ _ X T Z a b p q H ha _ _ G hG R _ t _ Y π f Hy hfib κ _ _ D hD hc n
  have HP := Hy.paste_horiz H
  have hproj : IsProjBy f := by
    obtain ⟨c, hcb⟩ := Spec.map_surjective (t ≫ b)
    have HP' : IsPullback (π ≫ p) f a (spMap c.hom) := by
      have : spMap c.hom = t ≫ b := by
        rw [← hcb]; rfl
      rw [this]; exact HP
    exact (ProjSpace.isProjBy_iff_isProjOver f).2
      (ProjSpace.isProjOver_of_isPullback_spMap c.hom HP'
        ((ProjSpace.isProjBy_iff_isProjOver a).1 ha))
  haveI : IsSeparated f := MorphismProperty.of_isPullback (P := @IsSeparated) HP inferInstance
  haveI : Flat f := MorphismProperty.of_isPullback (P := @Flat) HP inferInstance
  haveI hN : IsNoetherianRing R := by
    haveI : IsLocallyNoetherian (Spec (CommRingCat.of R)) :=
      LocallyOfFiniteType.isLocallyNoetherian (t ≫ b)
    exact (isLocallyNoetherian_Spec (R := CommRingCat.of R)).1 inferInstance
  have hM := LB.isLB_pull hG π
  have hI := GlobalTheory.MumfordSupport.isAffineOpen_biInf_of_isSeparated f hD
  have hflat : ∀ p, Module.Flat R ((cechLB f (G.pull π) D).X p) := flat_cechLB_X f hM hI
  have hfin := GlobalTheory.T.finite_cechLB_homology_of_affine_cover R Y f _ κ D hM inferInstance hproj hD hc
  rw [HomologicalComplex.exactAt_iff_isZero_homology, ModuleCat.isZero_iff_subsingleton]
  refine GlobalTheory.MumfordAway.subsingleton_of_points k R (t ≫ b) _ fun χ hχ => ?_
  refine exists_smul_homology_eq_zero_of_acyclic_fibre R k χ _ (Fintype.card κ)
    (fun p hp => isZero_cechLB_X _ _ _ hp.le) hflat hfin ?_ n
  have h' := IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom χ))
  have P1 := h'.paste_horiz HP
  rw [hχ] at P1
  let u := pullback.fst f (Spec.map (CommRingCat.ofHom χ))
  let v := pullback.snd f (Spec.map (CommRingCat.ofHom χ))
  let e := u ≫ π ≫ p
  haveI : IsIso e := P1.isIso_fst_of_isIso
  have he : e ≫ a = v := P1.w.trans (Category.comp_id _)
  let σ : X ⟶ Z := inv e ≫ u ≫ π
  have hσp : σ ≫ p = 𝟙 X := by
    simp only [σ, Category.assoc]
    exact IsIso.inv_hom_id e
  have hes : e ≫ σ = u ≫ π := by simp [σ]
  have hσq : σ ≫ q = a ≫ Spec.map (CommRingCat.ofHom χ) ≫ t := by
    rw [← cancel_epi e, ← Category.assoc e σ, hes, ← Category.assoc e a, he, Category.assoc u, Hy.w]
    exact (reassoc_of% h'.w) t
  have hac := hfib (Spec.map (CommRingCat.ofHom χ)) σ hχ hσp hσq κ (fun i => inv e ⁻¹ᵁ u ⁻¹ᵁ D i)
    (fun i => (isAffineOpen_preimage_of_isPullback h' (hD i)).preimage_of_isIso _)
    (by rw [← Scheme.Hom.preimage_iSup, ← Scheme.Hom.preimage_iSup, hc]; rfl)
  obtain ⟨i₁⟩ := cechLB_pull_iso_of_isOpenImmersion k X a (G.pull σ) _ e κ
    (fun i => inv e ⁻¹ᵁ u ⁻¹ᵁ D i) (LB.isLB_pull hG σ)
    (fun i => by rw [Scheme.Hom.opensRange_of_isIso]; exact le_top)
  have hD' : (fun i => e ⁻¹ᵁ inv e ⁻¹ᵁ u ⁻¹ᵁ D i) = fun i => u ⁻¹ᵁ D i := funext fun i => by
    rw [← Scheme.Hom.comp_preimage, IsIso.hom_inv_id]; rfl
  rw [he, hD'] at i₁
  obtain ⟨w₁, hw₁⟩ : ∃ w : LB.Iso ((G.pull σ).pull e) (G.pull (u ≫ π)), w.IsGen :=
    hes ▸ GlobalTheory.MumfordSupport.exists_iso_pull_pull hG σ e
  obtain ⟨w₂, hw₂⟩ := GlobalTheory.MumfordSupport.exists_iso_pull_pull hG π u
  have hL₁ : ((G.pull σ).pull e).IsLB := LB.isLB_pull (LB.isLB_pull hG σ) e
  have hL₂ : ((G.pull π).pull u).IsLB := LB.isLB_pull hM u
  have hL₃ : (G.pull (u ≫ π)).IsLB := LB.isLB_pull hG _
  have c₁ := cechLBCongr v (fun i => u ⁻¹ᵁ D i) hL₁ hL₃ w₁ hw₁
  have c₂ := cechLBCongr v (fun i => u ⁻¹ᵁ D i) hL₂ hL₃ w₂ hw₂
  have E := cechLBBaseChangeIso hM h' hI ≪≫ c₂ ≪≫ c₁.symm ≪≫ i₁
  exact fun m => (hac m).of_iso E.symm

end GlobalTheory.CompanionTheory.PointSurjectivity
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FibrewiseAcyclicityBaseChangeStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.PointSurjectivity

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibrewise_acyclicity_base_change : ∀ {k : Type} [Field k] [IsAlgClosed k] {X T Z : Scheme.{0}} (a : X ⟶ Sp k) (b : T ⟶ Sp k) (p : Z ⟶ X)
    (q : Z ⟶ T) (H : IsPullback p q a b) (ha : IsProjBy a) [IsSeparated a] [Flat a] (G : LB Z) (hG : G.IsLB)
    (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ T) [LocallyOfFiniteType (t ≫ b)] (Y : Scheme.{0})
    (π : Y ⟶ Z) (f : Y ⟶ Spec (CommRingCat.of R)) (Hy : IsPullback π f q t)
    (hfib : ∀ (s : Sp k ⟶ Spec (CommRingCat.of R)) (σ : X ⟶ Z), s ≫ t ≫ b = 𝟙 _ → σ ≫ p = 𝟙 X →
      σ ≫ q = a ≫ s ≫ t → FibAc a (G.pull σ)), FibAc f (G.pull π) := by
  first | exact @GlobalTheory.CompanionTheory.PointSurjectivity.fibAc_of_closed_fibres | exact GlobalTheory.CompanionTheory.PointSurjectivity.fibAc_of_closed_fibres | (intros; apply GlobalTheory.CompanionTheory.PointSurjectivity.fibAc_of_closed_fibres <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FiniteGroupHomKernelPullback
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.KerPull.Kernel

section General

universe v u

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] {A A' H : C} [GrpObj A] [GrpObj A']
  {q : A ⟶ A'} [IsMonHom q] {i : H ⟶ A}

theorem mono_of_isKernel (hp : IsPullback i (toUnit H) q η[A']) : Mono i :=
  ⟨fun _ _ e => hp.hom_ext e (toUnit_unique _ _)⟩

def kerLift (hp : IsPullback i (toUnit H) q η[A']) {W : C} (f : W ⟶ A) (hf : f ≫ q = 1) : W ⟶ H :=
  hp.lift f (toUnit W) (by rw [hf, Hom.one_def])

theorem kerLift_comp (hp : IsPullback i (toUnit H) q η[A']) {W : C} (f : W ⟶ A) (hf : f ≫ q = 1) :
    kerLift hp f hf ≫ i = f :=
  hp.lift_fst ..

theorem comp_kills (hp : IsPullback i (toUnit H) q η[A']) {W : C} (x : W ⟶ H) : (x ≫ i) ≫ q = 1 := by
  rw [Category.assoc, hp.w, ← Category.assoc, toUnit_unique (x ≫ toUnit H) (toUnit W), Hom.one_def]

@[instance_reducible]
def grpObjOfIsKernel (hp : IsPullback i (toUnit H) q η[A']) : GrpObj H :=
  have := mono_of_isKernel hp
  { one := kerLift hp η[A] (by rw [IsMonHom.one_hom, Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp])
    mul := kerLift hp (fst H H ≫ i * snd H H ≫ i) (by
      rw [MonObj.mul_comp, comp_kills hp, comp_kills hp, _root_.mul_one])
    inv := kerLift hp (i ≫ ι[A]) (by
      have e : i ≫ q = 1 := by simpa using comp_kills hp (𝟙 H)
      have h : (i⁻¹ * i) ≫ q = 1 := by rw [inv_mul_cancel, MonObj.one_comp]
      rw [MonObj.mul_comp, e, _root_.mul_one] at h
      exact h)
    one_mul := by
      rw [← cancel_mono i]
      simp [kerLift_comp, MonObj.comp_mul]
      rw [toUnit_unique (fst (𝟙_ C) H) (toUnit _), ← Hom.one_def, _root_.one_mul, leftUnitor_hom]
    mul_one := by
      rw [← cancel_mono i]
      simp [kerLift_comp, MonObj.comp_mul]
      rw [toUnit_unique (snd H (𝟙_ C)) (toUnit _), ← Hom.one_def, _root_.mul_one, rightUnitor_hom]
    mul_assoc := by
      rw [← cancel_mono i]
      simp [kerLift_comp, MonObj.comp_mul]
      exact _root_.mul_assoc _ _ _
    left_inv := by
      rw [← cancel_mono i]
      simp [kerLift_comp, MonObj.comp_mul]
      rw [← Hom.one_def]
      exact inv_mul_cancel i
    right_inv := by
      rw [← cancel_mono i]
      simp [kerLift_comp, MonObj.comp_mul]
      rw [← Hom.one_def]
      exact mul_inv_cancel i }

theorem isMonHom_of_isKernel (hp : IsPullback i (toUnit H) q η[A']) :
    letI := grpObjOfIsKernel hp
    IsMonHom i := by
  letI := grpObjOfIsKernel hp
  refine { one_hom := kerLift_comp hp _ _, mul_hom := ?_ }
  refine (kerLift_comp hp _ _).trans ?_
  rw [Hom.mul_def]
  simp

theorem isCommMonObj_of_isKernel [BraidedCategory C] [IsCommMonObj A]
    (hp : IsPullback i (toUnit H) q η[A']) :
    letI := grpObjOfIsKernel hp
    IsCommMonObj H := by
  letI := grpObjOfIsKernel hp
  have := mono_of_isKernel hp
  have := isMonHom_of_isKernel hp
  refine (isCommMonObj_iff_isMulCommutative _).mpr fun T => ⟨⟨fun x y => ?_⟩⟩
  rw [← cancel_mono i, MonObj.mul_comp, MonObj.mul_comp, mul_comm]

end General

theorem exists_finite_kernel : ∀ (k : Type) [Field k] (A A' : Over (Sp k)) [GrpObj A] [GrpObj A'], IsAbelianScheme A → ∀ (q : A ⟶ A'), IsMonHom q → IsFinite q.left →
    ∃ (H : Over (Sp k)) (_ : GrpObj H) (_ : IsCommMonObj H) (i : H ⟶ A), IsMonHom i ∧ IsFinite H.hom ∧
      IsPullback i (toUnit _) q η[A'] := by
  intro k _ A A' _ _ hA q hq hf
  have := hA.comm
  have hp : IsPullback (pullback.fst q η[A']) (toUnit (pullback q η[A'])) q η[A'] := by
    rw [toUnit_unique (toUnit _) (pullback.snd q η[A'])]
    exact IsPullback.of_hasPullback _ _
  refine ⟨pullback q η[A'], grpObjOfIsKernel hp, isCommMonObj_of_isKernel hp, pullback.fst _ _,
    isMonHom_of_isKernel hp, ?_, hp⟩
  have hl := hp.map (Over.forget _)
  have h1 : IsFinite (toUnit (pullback q η[A'])).left :=
    MorphismProperty.of_isPullback (P := @IsFinite) hl hf
  have h2 : (pullback q η[A']).hom = (toUnit (pullback q η[A'])).left ≫ (𝟙_ (Over (Sp k))).hom :=
    (Over.w _).symm
  rw [h2]
  exact inferInstanceAs (IsFinite (_ ≫ 𝟙 _))
end GlobalTheory.CompanionTheory.KerPull.Kernel
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LinearCombinationGeneratorSectionExists
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LinearCombinationGeneratorSectionExists
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.SecNorm

theorem exists_gen_normalised_along : ∀ {X Y S₀ : Scheme.{0}} {M : LB X}, M.IsLB → ∀ {K K₂ : Type} [Fintype K] [Fintype K₂] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (φ₂ : K₂ → (S₀ ⟶ X)) (ε₂ : K₂ → ℤ) (p : Y ⟶ S₀) (e : S₀ ⟶ Y), e ≫ p = 𝟙 S₀ → FormEq (fun k => e ≫ φ k) ε φ₂ ε₂ →
    ∀ (t : LB.Gen (LB.LinComb M φ ε)), t.IsGen → ∀ (R : LB.Gen (LB.LinComb M φ₂ ε₂)), R.IsGen →
    ∃ t' : LB.Gen (LB.LinComb M φ ε), t'.IsGen ∧
      ∀ (Z : Scheme.{0}) (s : Z ⟶ S₀) (z : Z) (J : (Z ⟶ X) → M.ι), Good M z J → val t' (s ≫ e) z J = val R s z J := by
  intro X Y S₀ M hM K K₂ _ _ φ ε φ₂ ε₂ p e he hF t ht R hR
  obtain ⟨t', ht', hv⟩ := exists_gen hM (φ' := φ) (ε' := ε)
    (fun U _ h => by
      have c := hF U (fun ψ => h (p ≫ ψ))
      simp only [Category.assoc] at c
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Category.assoc, c.symm]
      simp)
    (LB.mulGen M _ _ _ _ (LB.mulGen M _ _ _ _ t (LB.invGen M _ _ (LB.pullGen M _ _ t (p ≫ e))))
      (LB.pullGen M _ _ R p))
    (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _)))
      (DVR.pullGen_isGen _ _ _ _ hR _))
  refine ⟨t', ht', fun Z s z J hJ => ?_⟩
  have h₁ : (s ≫ e) ≫ p = s := by rw [Category.assoc, he, Category.comp_id]
  have h₂ : (s ≫ e) ≫ p ≫ e = s ≫ e := by rw [← Category.assoc, h₁]
  rw [hv Z (s ≫ e) z J hJ, val_mul hJ, val_mul hJ, val_inv, val_pull hJ, val_pull hJ, h₁, h₂, mul_inv_cancel,
    _root_.one_mul]

end GlobalTheory.CompanionTheory.SecNorm
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LinearCombinationGeneratorSectionExistsStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linear_combination_generator_section_exists : ∀ {X Y S₀ : Scheme.{0}} {M : LB X}, M.IsLB → ∀ {K K₂ : Type} [Fintype K] [Fintype K₂] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (φ₂ : K₂ → (S₀ ⟶ X)) (ε₂ : K₂ → ℤ) (p : Y ⟶ S₀) (e : S₀ ⟶ Y), e ≫ p = 𝟙 S₀ → FormEq (fun k => e ≫ φ k) ε φ₂ ε₂ →
    ∀ (t : LB.Gen (LB.LinComb M φ ε)), t.IsGen → ∀ (R : LB.Gen (LB.LinComb M φ₂ ε₂)), R.IsGen →
    ∃ t' : LB.Gen (LB.LinComb M φ ε), t'.IsGen ∧
      ∀ (Z : Scheme.{0}) (s : Z ⟶ S₀) (z : Z) (J : (Z ⟶ X) → M.ι), Good M z J → val t' (s ≫ e) z J = val R s z J := by
  first | exact @GlobalTheory.CompanionTheory.SecNorm.exists_gen_normalised_along | exact GlobalTheory.CompanionTheory.SecNorm.exists_gen_normalised_along | (intros; apply GlobalTheory.CompanionTheory.SecNorm.exists_gen_normalised_along <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FlatCoverBaseChangeProduct
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FlatCoverBaseChangeProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.RigDesc

theorem isPullback_snd_lift_fst_snd_comp {S : Scheme.{0}} (A X Y : Over S) (q : X ⟶ Y) :
    IsPullback (snd A X).left (lift (fst A X) (snd A X ≫ q)).left q.left (snd A Y).left := by
  have hX : IsPullback (fst A X).left (snd A X).left A.hom X.hom := by
    simpa only [Over.fst_left, Over.snd_left] using IsPullback.of_hasPullback A.hom X.hom
  have hY : IsPullback (fst A Y).left (snd A Y).left A.hom Y.hom := by
    simpa only [Over.fst_left, Over.snd_left] using IsPullback.of_hasPullback A.hom Y.hom
  have e₁ : (lift (fst A X) (snd A X ≫ q)).left ≫ (fst A Y).left = (fst A X).left := by
    rw [← Over.comp_left, lift_fst]
  have e₂ : (lift (fst A X) (snd A X ≫ q)).left ≫ (snd A Y).left = (snd A X).left ≫ q.left := by
    rw [← Over.comp_left, lift_snd, Over.comp_left]
  have hout : IsPullback ((lift (fst A X) (snd A X ≫ q)).left ≫ (fst A Y).left) (snd A X).left
      A.hom (q.left ≫ Y.hom) := by
    rw [e₁, Over.w q]
    exact hX
  exact (IsPullback.of_right hout e₂ hY).flip

theorem lift_fst_snd_comp_flat_lfp_surjective :
    ∀ (S : Scheme.{0}) (A X Y : Over S) [GrpObj A], IsAbelianScheme A → ∀ q : X ⟶ Y, Flat q.left →
    LocallyOfFinitePresentation q.left → Surjective q.left →
    Flat (lift (fst A X) (snd A X ≫ q)).left ∧ LocallyOfFinitePresentation (lift (fst A X) (snd A X ≫ q)).left ∧
      Surjective (lift (fst A X) (snd A X ≫ q)).left := by
  intro S A X Y _ _ q hf hl hs
  have h := isPullback_snd_lift_fst_snd_comp A X Y q
  exact ⟨MorphismProperty.of_isPullback (P := @Flat) h hf,
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) h hl,
    MorphismProperty.of_isPullback (P := @Surjective) h hs⟩

end GlobalTheory.CompanionTheory.RigDesc
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FlatCoverBaseChangeProductStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_cover_base_change_product : ∀ (S : Scheme.{0}) (A X Y : Over S) [GrpObj A], IsAbelianScheme A → ∀ q : X ⟶ Y, Flat q.left →
    LocallyOfFinitePresentation q.left → Surjective q.left →
    Flat (lift (fst A X) (snd A X ≫ q)).left ∧ LocallyOfFinitePresentation (lift (fst A X) (snd A X ≫ q)).left ∧
      Surjective (lift (fst A X) (snd A X ≫ q)).left := by
  first | exact @GlobalTheory.CompanionTheory.RigDesc.lift_fst_snd_comp_flat_lfp_surjective | exact GlobalTheory.CompanionTheory.RigDesc.lift_fst_snd_comp_flat_lfp_surjective | (intros; apply GlobalTheory.CompanionTheory.RigDesc.lift_fst_snd_comp_flat_lfp_surjective <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IsIsoOfClosedImmersion
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.DualUniv

theorem isIso_of_closedImmersion {R : Type} [CommRing R] {Z : Scheme.{0}} (f : Z ⟶ Sp R) [IsClosedImmersion f]
    [Flat f] [Surjective f] : IsIso f := by
  have : IsAffine Z := isAffine_of_isAffineHom f
  have h₁ : f.appTop.hom.FaithfullyFlat :=
    (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine f).1 ⟨inferInstance, inferInstance⟩
  have h₂ : Function.Surjective f.appTop.hom := (IsClosedImmersion.isAffine_surjective_of_isAffine f).2
  have h₃ : Function.Bijective f.appTop.hom := ⟨h₁.injective, h₂⟩
  have : IsIso f.appTop := (ConcreteCategory.isIso_iff_bijective _).2 h₃
  exact (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms Scheme) (arrowIsoSpecΓOfIsAffine f)).2
    (inferInstanceAs (IsIso (Spec.map f.appTop)))

variable {S : Scheme.{0}}

def IsAddCls (A : Over S) [GrpObj A] (m : Pic A.left) : Prop :=
  ∀ (Y : Over S) (a a' : Y ⟶ A),
    CechPic.pull (a * a').left m = CechPic.pull a.left m + CechPic.pull a'.left m

theorem preDual_baseChange {S' : Scheme.{0}} {b : S' ⟶ S} {A B : Over S} [GrpObj A] [GrpObj B] {A' B' : Over S'}
    [GrpObj A'] [GrpObj B'] {f : A'.left ⟶ A.left} {g : B'.left ⟶ B.left} {h : (A' ⊗ B').left ⟶ (A ⊗ B).left}
    (hf : IsGrpPullback A' A b f) (hg : IsGrpPullback B' B b g)
    (h₁ : h ≫ (fst A B).left = (fst A' B').left ≫ f) (h₂ : h ≫ (snd A B).left = (snd A' B').left ≫ g)
    {P : LB (A ⊗ B).left} {P' : LB (A' ⊗ B').left} (hP' : P'.IsLB) (e : LBIso (P.pull h) P')
    (hd : PreDual A B P) : PreDual A' B' P' := by
  obtain ⟨a₁, a₂⟩ := GlobalTheory.BirigidLift.additive_pull hf hg h₁ h₂ hd.isLB hP' e hd.add₁ hd.add₂
  refine ⟨hP', a₁, a₂, fun T y hy ↦ ?_, fun k _ _ t ↦ ?_⟩
  · have h0 := hd.right _ (pushP hg (s := T.hom) rfl y) ((triv_ev_iff hd.isLB _ _).2 (by
      rw [← evc_trR hf hg h₁ h₂ hd.isLB hP' e, (triv_ev_iff hP' _ _).1 hy, map_zero]))
    exact pt_ext hg ((congrArg (fun z ↦ z.left) h0).trans (one_left_comp hg (s := T.hom) rfl).symm)
  · refine Set.Finite.of_injOn (f := pushP hf (s := t) rfl) (fun x hx ↦ ?_)
      (fun x _ y _ e ↦ pt_ext hf (congrArg (fun z ↦ z.left) e)) (hd.left k (t ≫ b))
    refine (triv_ev_iff hd.isLB _ _).2 ?_
    have := evc_trL hf hg h₁ h₂ hd.isLB hP' e (Over.mk t) x
    rw [(triv_ev_iff hP' _ _).1 hx, map_zero] at this
    exact this.symm

theorem exists_point_fibre (H3 : PointSurj) {A B : Over S} [GrpObj A] [GrpObj B] (hA : IsAbelianScheme A)
    (hB : IsAbelianScheme B) {P : LB (A ⊗ B).left} (hP : PreDual A B P) {m : Pic A.left} (hm : IsAddCls A m)
    (k : Type) [Field k] [IsAlgClosed k] (s : Sp k ⟶ S) :
    ∃ y : Over.mk ((𝟙_ (Over (Sp k))).hom ≫ s) ⟶ B,
      evc hP.isLB (fst A (Over.mk ((𝟙_ (Over (Sp k))).hom ≫ s)))
          (snd A (Over.mk ((𝟙_ (Over (Sp k))).hom ≫ s)) ≫ y) =
        CechPic.pull (fst A (Over.mk ((𝟙_ (Over (Sp k))).hom ≫ s))).left m := by
  have hf := isGrpPullback_pullback A s
  have hg := isGrpPullback_pullback B s
  obtain ⟨h, h₁, h₂⟩ := exists_prod_pullback hf hg
  have hP' : (P.pull h).IsLB := pull_isLB hP.isLB h
  have e : LBIso (P.pull h) (P.pull h) := (cls_eq_iff hP' hP').1 rfl
  have hd := preDual_baseChange hf hg h₁ h₂ hP' e hP
  have hA' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA hf
  have hB' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hB hg
  obtain ⟨M, hM, eM⟩ := cls_surj (CechPic.pull
    ((fst ((Over.pullback s).obj A) (𝟙_ (Over (Sp k)))).left ≫ pullback.fst A.hom s) m)
  have hadd : IsAdditive M := (isAdditive_iff hM).2 fun Y a a' t ↦ by
    simp only [evc, eM, ← pull_comp, lift_left_fst_assoc]
    rw [mul_left_comp hf (s₀ := Y.hom ≫ s) rfl (x := a) (y := a') (x₀ := pushP hf (s := Y.hom) rfl a)
      (y₀ := pushP hf (s := Y.hom) rfl a') rfl rfl]
    exact hm _ _ _
  have fin : Set.Finite {x : 𝟙_ (Over (Sp k)) ⟶ (Over.pullback s).obj A |
      Triv (ev (P.pull h) (toUnit ((Over.pullback s).obj B) ≫ x) (𝟙 ((Over.pullback s).obj B)))} := by
    refine (hd.left k (𝟙 _)).subset fun x hx ↦ ?_
    refine (triv_ev_iff hP' _ _).2 ?_
    have e₂ := congrArg (CechPic.pull (snd (𝟙_ (Over (Sp k))) ((Over.pullback s).obj B)).left)
      ((triv_ev_iff hP' _ _).1 hx)
    rw [pull_evc, map_zero, Category.comp_id, ← Category.assoc,
      toUnit_unique (snd (𝟙_ (Over (Sp k))) ((Over.pullback s).obj B) ≫ toUnit _) (fst _ _)] at e₂
    exact e₂
  obtain ⟨y, hy⟩ := H3 k _ _ hA' hB' (P.pull h) hP' hd.add₁ hd.add₂ fin M hM hadd
  refine ⟨pushP hg (s := (𝟙_ (Over (Sp k))).hom) rfl y, ?_⟩
  have c := (cls_eq_iff hM (pull_isLB hP' _)).2 hy
  rw [← evc_trR hf hg h₁ h₂ hP.isLB hP' e]
  have c' : evc hP' (fst _ _) (snd _ _ ≫ y) = _ := c.symm.trans eM
  rw [c', ← pull_comp]
  exact congrArg (fun q ↦ CechPic.pull q m) (trR_fst hf _)

theorem exists_section (H1 : TrivLocus) (H2 : TrivLocusFlat) (H3 : PointSurj) {C : Type} [CommRing C]
    [IsNoetherianRing C] (A B : Over (Sp C)) [GrpObj A] [GrpObj B] (g : ℕ) (hA : IsAbelianScheme A)
    (hB : IsAbelianScheme B) (gA : SmoothOfRelativeDimension g A.hom) (gB : SmoothOfRelativeDimension g B.hom)
    {P : LB (A ⊗ B).left} (hP : PreDual A B P) {m : Pic A.left} (hm : IsAddCls A m) :
    ∃ x : Over.mk (𝟙 (Sp C)) ⟶ B, evc hP.isLB (fst A (Over.mk (𝟙 (Sp C)))) (snd A (Over.mk (𝟙 (Sp C))) ≫ x) =
      CechPic.pull (fst A (Over.mk (𝟙 (Sp C)))).left m := by
  obtain ⟨N, hN, eN⟩ := cls_surj (cls P hP.isLB - CechPic.pull (fst A B).left m)
  have ecl : ∀ {Y : Over (Sp C)} (a : Y ⟶ A) (t : Y ⟶ B),
      evc hN a t = evc hP.isLB a t - CechPic.pull a.left m := by
    intro Y a t
    rw [evc, eN, map_sub, ← pull_comp, lift_left_fst]
    rfl
  have rep : ∀ (T : Over (Sp C)) (y : T ⟶ B), Triv (ev N (fst A T) (snd A T ≫ y)) ↔
      evc hP.isLB (fst A T) (snd A T ≫ y) = CechPic.pull (fst A T).left m := fun T y ↦ by
    rw [triv_ev_iff hN, ecl, sub_eq_zero]
  have h0 : Triv (ev N (1 : B ⟶ A) (𝟙 B)) := by
    have z : CechPic.pull (1 : B ⟶ A).left m = 0 := by
      have := hm B 1 1
      rw [_root_.mul_one] at this
      exact left_eq_add.1 this
    rw [triv_ev_iff hN, ecl, hP.add₁.evc_one hP.isLB, z, sub_zero]
  have tr := GlobalTheory.BirigidLift.triv_right hP.isLB hP.add₂
  have uniq : ∀ (T : Over (Sp C)) (y y' : T ⟶ B),
      evc hP.isLB (fst A T) (snd A T ≫ y) = CechPic.pull (fst A T).left m →
      evc hP.isLB (fst A T) (snd A T ≫ y') = CechPic.pull (fst A T).left m → y = y' := by
    intro T y y' e e'
    have a2 := (GlobalTheory.BirigidLift.isAdditive_swap_iff hP.isLB).1 hP.add₂
    have k1 := a2 _ (fst A T) (snd A T ≫ y) (snd A T ≫ y'⁻¹)
    have k2 := a2 _ (fst A T) (snd A T ≫ y') (snd A T ≫ y'⁻¹)
    rw [← MonObj.comp_mul] at k1 k2
    rw [_root_.mul_inv_cancel, MonObj.comp_one, evc_one_right hP.isLB tr] at k2
    have z := hP.right T (y * y'⁻¹) ((triv_ev_iff hP.isLB _ _).2 (by rw [k1, e, ← e', ← k2]))
    exact mul_inv_eq_one.1 z
  have : LocallyOfFiniteType B.hom := by
    have := hB.smooth
    infer_instance
  have : IsLocallyNoetherian B.left := LocallyOfFiniteType.isLocallyNoetherian B.hom
  obtain ⟨Z, i, hci, hiff⟩ := H1 _ A B hA ‹_› N hN h0
  have : IsClosedImmersion i.left := hci
  have hw : i.left ≫ B.hom = Z.hom := Over.w i
  have hmono : Mono Z.hom := ⟨fun {W} u v e ↦ by
    let u' : Over.mk (u ≫ Z.hom) ⟶ Z := Over.homMk u rfl
    let v' : Over.mk (u ≫ Z.hom) ⟶ Z := Over.homMk v e.symm
    have e₁ := uniq _ (u' ≫ i) (v' ≫ i) ((rep _ _).1 ((hiff _ _).2 ⟨u', rfl⟩))
      ((rep _ _).1 ((hiff _ _).2 ⟨v', rfl⟩))
    exact (cancel_mono i.left).1 (congrArg (fun q ↦ q.left) e₁)⟩
  have hprop : IsProper Z.hom := by
    have := hB.proper
    rw [← hw]
    infer_instance
  have hcl : IsClosedImmersion Z.hom := (IsClosedImmersion.iff_isProper_and_mono _).2 ⟨hprop, hmono⟩
  have hfl : Flat Z.hom := H2 _ A B Z g hA gA gB N hN i ⟨hci, hiff⟩ inferInstance
  have hsu : Surjective Z.hom := ⟨fun c ↦ by
    let κ := (Sp C).residueField c
    let k := AlgebraicClosure κ
    let s : Sp k ⟶ Sp C := Spec.map (CommRingCat.ofHom (algebraMap κ k)) ≫ (Sp C).fromSpecResidueField c
    obtain ⟨y, hy⟩ := exists_point_fibre H3 hA hB hP hm k s
    obtain ⟨z, rfl⟩ := (hiff _ y).1 ((rep _ _).2 hy)
    obtain ⟨p⟩ : Nonempty (Sp k) := inferInstance
    refine ⟨z.left p, ?_⟩
    have e : z.left ≫ Z.hom = (𝟙_ (Over (Sp k))).hom ≫ s := Over.w z
    have e' : z.left ≫ Z.hom = s := e.trans (Category.id_comp s)
    rw [← Scheme.Hom.comp_apply, e']
    exact (Scheme.Hom.comp_apply _ _ p).trans (Scheme.fromSpecResidueField_apply c _)⟩
  have : IsIso Z.hom := isIso_of_closedImmersion Z.hom
  let z : Over.mk (𝟙 (Sp C)) ⟶ Z := Over.homMk (inv Z.hom) (by simp)
  exact ⟨z ≫ i, (rep _ _).1 ((hiff _ _).2 ⟨z, rfl⟩)⟩

theorem univNoeth : TrivLocus → TrivLocusFlat → PointSurj → ∀ (R : Type) [CommRing R] [IsNoetherianRing R]
    (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (g : ℕ), IsAbelianScheme A → IsAbelianScheme B →
    SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom →
    ∀ P : LB (A ⊗ B).left, PreDual A B P → UnivNoeth A B P := by
  intro H1 H2 H3 R _ _ A B _ _ g hA hB gA gB P hP C _ _ t M hM hadd
  have hf := isGrpPullback_pullback A t
  have hg := isGrpPullback_pullback B t
  obtain ⟨h, h₁, h₂⟩ := exists_prod_pullback hf hg
  have hP' : (P.pull h).IsLB := pull_isLB hP.isLB h
  have e : LBIso (P.pull h) (P.pull h) := (cls_eq_iff hP' hP').1 rfl
  have hd := preDual_baseChange hf hg h₁ h₂ hP' e hP
  have hA' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA hf
  have hB' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hB hg
  have gA' : SmoothOfRelativeDimension g ((Over.pullback t).obj A).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback hf.1 gA
  have gB' : SmoothOfRelativeDimension g ((Over.pullback t).obj B).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback hg.1 gB
  let r : ((Over.pullback t).obj A).left ⟶ (A ⊗ Over.mk t).left :=
    Limits.pullback.lift (pullback.fst A.hom t) ((Over.pullback t).obj A).hom hf.1.w
  have r₁ : r ≫ (fst A (Over.mk t)).left = pullback.fst A.hom t := Limits.pullback.lift_fst _ _ _
  have r₂ : r ≫ (snd A (Over.mk t)).left = ((Over.pullback t).obj A).hom := Limits.pullback.lift_snd _ _ _
  have key : ∀ (Y : Over (Sp C)) (a : Y ⟶ (Over.pullback t).obj A) (a₀ : Over.mk (Y.hom ≫ t) ⟶ A),
      a.left ≫ pullback.fst A.hom t = a₀.left →
      CechPic.pull a.left (CechPic.pull r (cls M hM)) =
        evc hM a₀ (Over.homMk Y.hom rfl : Over.mk (Y.hom ≫ t) ⟶ Over.mk t) := by
    intro Y a a₀ ea
    rw [← pull_comp, evc]
    refine congrArg (fun q ↦ CechPic.pull q (cls M hM)) (left_ext ?_ ?_)
    · rw [Category.assoc, r₁, lift_left_fst, ea]
    · rw [Category.assoc, r₂, lift_left_snd]
      exact Over.w a
  have hm : IsAddCls ((Over.pullback t).obj A) (CechPic.pull r (cls M hM)) := fun Y a a' ↦ by
    rw [key Y (a * a') (pushP hf (s := Y.hom) rfl a * pushP hf (s := Y.hom) rfl a')
        (mul_left_comp hf rfl rfl rfl), key Y a (pushP hf (s := Y.hom) rfl a) rfl,
      key Y a' (pushP hf (s := Y.hom) rfl a') rfl]
    exact (isAdditive_iff hM).1 hadd _ _ _ _
  obtain ⟨x', hx⟩ := exists_section H1 H2 H3 _ _ g hA' hB' gA' gB' hd hm
  have wx : x'.left ≫ ((Over.pullback t).obj B).hom = 𝟙 (Sp C) := Over.w x'
  let x : Over.mk t ⟶ B := Over.homMk (x'.left ≫ pullback.fst B.hom t) (by
    show (x'.left ≫ pullback.fst B.hom t) ≫ B.hom = t
    rw [Category.assoc, hg.1.w, ← Category.assoc, wx]
    exact Category.id_comp t)
  refine ⟨x, (cls_eq_iff hM (pull_isLB hP.isLB _)).1 ?_⟩
  have w : (fst A (Over.mk t)).left ≫ A.hom = (snd A (Over.mk t)).left ≫ t :=
    (Over.w (fst A (Over.mk t))).trans (Over.w (snd A (Over.mk t))).symm
  let a := liftPt hf (snd A (Over.mk t)).left (fst A (Over.mk t)).left w
  let τ : Over.mk (snd A (Over.mk t)).left ⟶ Over.mk (𝟙 (Sp C)) :=
    Over.homMk (snd A (Over.mk t)).left (by simp)
  have ar : a.left ≫ r = 𝟙 _ := by
    apply left_ext
    · rw [Category.assoc, r₁, Category.id_comp]
      exact liftPt_left _ _ _ _
    · rw [Category.assoc, r₂, Category.id_comp]
      exact Over.w a
  have c := congrArg (CechPic.pull (lift a τ).left) hx
  rw [pull_evc, ← pull_comp, lift_left_fst, lift_fst, lift_snd_assoc,
    evc_eq h₁ h₂ hP.isLB hP' e a (τ ≫ x') (fst A (Over.mk t)) (snd A (Over.mk t) ≫ x)
      (liftPt_left _ _ _ _) rfl, ← pull_comp, ar] at c
  exact (c.trans (pull_id _)).symm

end GlobalTheory.CompanionTheory.DualUniv
end
end
