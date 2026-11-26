module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LineBundleTrivialOfDescendedGenerator
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupHomCharacterMapConstant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPrincipalOfSubring

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.Data
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleDiagonalBundleDescendsSubring
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleDiagonalBundleDescendsSubring
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings

set_option autoImplicit false

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleDiagSubring

theorem relAmple_diag_subring : ∀ (R : Type) [CommRing R] (R₁ : Subring R) [IsNoetherianRing R₁] (A : Over (Sp R)) [GrpObj A] (P : LB (A ⊗ A).left) (A₁ : Over (Sp R₁)) [GrpObj A₁] (P₁ : LB (A₁ ⊗ A₁).left) (φ : A.left ⟶ A₁.left) (φ₂ : (A ⊗ A).left ⟶ (A₁ ⊗ A₁).left), IsAbelianScheme A₁ → P.IsLB → P₁.IsLB → IsGrpPullback A A₁ (spMap R₁.subtype) φ → Geo.Tor.IsSquare φ φ₂ → LBIso P (P₁.pull φ₂) → Out.RelAmple A (diagPull A P) → ∃ F : Finset R, ∀ (R₂ : Subring R) (h : R₁ ≤ R₂), (F : Set R) ⊆ R₂ → ∀ (A₂ : Over (Sp R₂)) [GrpObj A₂] (π : A₂.left ⟶ A₁.left) (π₂ : (A₂ ⊗ A₂).left ⟶ (A₁ ⊗ A₁).left), IsGrpPullback A₂ A₁ (spMap (Subring.inclusion h)) π → Geo.Tor.IsSquare π π₂ → Out.RelAmple A₂ (diagPull A₂ (P₁.pull π₂)) := by
  intro R _ R₁ _ A _ P A₁ _ P₁ φ φ₂ hA₁ hP hP₁ hφ sq e hamp
  classical
  have := hA₁.proper
  have := hA₁.smooth
  let M : LB A₁.left := diagPull A₁ P₁
  have hM : M.IsLB := pull_isLB hP₁ _
  have hL : (diagPull A P).IsLB := pull_isLB hP _
  have e' : LBIso (diagPull A P) (M.pull φ) := GlobalTheory.SiegelPull.diag_iso sq e
  have hspan := GlobalTheory.CompanionTheory.PolSpread.span_good R₁.subtype A A₁ hM hL hφ.1 e' hamp
  have h1 : (1 : R) ∈ Ideal.span (R₁.subtype '' GlobalTheory.CompanionTheory.PolSpread.good A₁ M) := by rw [hspan]; trivial
  obtain ⟨c, hc, hs⟩ := Submodule.mem_span_set.1 h1
  choose! t ht hty using fun y (hy : y ∈ c.support) => hc hy
  refine ⟨c.support.image c, fun R₂ h hF A₂ _ π π₂ hπ sq₂ => ?_⟩
  let τ : R₁ →+* R₂ := Subring.inclusion h
  have hmem : ∀ y ∈ c.support, c y ∈ R₂ := fun y hy =>
    hF (Finset.mem_coe.2 (Finset.mem_image_of_mem c hy))
  have hT : Ideal.span (τ '' (t '' (c.support : Set R))) = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    have e1 : (1 : R₂) = ∑ y ∈ c.support.attach, (⟨c y.1, hmem y.1 y.2⟩ : R₂) * τ (t y.1) := by
      apply Subtype.ext
      refine (OneMemClass.coe_one R₂).trans (hs.symm.trans ?_)
      rw [Finsupp.sum, ← Finset.sum_attach]
      simp only [AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul, smul_eq_mul]
      refine Finset.sum_congr rfl fun y _ => ?_
      have : ((τ (t y.1) : R₂) : R) = y.1 := hty y.1 y.2
      rw [this]
    rw [e1]
    exact Ideal.sum_mem _ fun y _ => Ideal.mul_mem_left _ _
      (Ideal.subset_span ⟨t y.1, ⟨y.1, y.2, rfl⟩, rfl⟩)
  have hB := GlobalTheory.CompanionTheory.PolSpread.relAmple_of_span τ A₁ hM _
    (by rintro _ ⟨y, hy, rfl⟩; exact ht y hy) hT
  have hπ' : Out.RelAmple (Over.mk A₂.hom) (M.pull π) :=
    GlobalTheory.FibreAmple.relAmple_of_factor hM (IsPullback.of_hasPullback A₁.hom (spMap τ)) hπ.1 (𝟙 _)
      (Category.id_comp _) (pull_isLB hM _) (GlobalTheory.lbIso_refl (pull_isLB hM _)) hB
  have : IsProper (Over.mk A₂.hom).hom := MorphismProperty.of_isPullback (P := @IsProper) hπ.1 ‹_›
  have hMπ : (M.pull π).IsLB := pull_isLB hM π
  have hL₂ : (diagPull A₂ (P₁.pull π₂)).IsLB := pull_isLB (pull_isLB hP₁ π₂) _
  have e₂ : LBIso (diagPull A₂ (P₁.pull π₂)) (M.pull π) :=
    GlobalTheory.SiegelPull.diag_iso sq₂ (GlobalTheory.lbIso_refl (pull_isLB hP₁ π₂))
  have e₃ : LBIso (M.pull π) ((M.pull π).pull (𝟙 _)) :=
    GlobalTheory.FibreAmple.lbIso_pull_comp (Category.id_comp π).symm (GlobalTheory.lbIso_refl hMπ)
  exact GlobalTheory.ModelAbLocus.relAmple_of_lbIso_pull (A := Over.mk A₂.hom) (A' := A₂) (f := 𝟙 _) (φ := 𝟙 _)
    (IsPullback.of_horiz_isIso ⟨by simp⟩) hMπ hL₂
    (LBIso.trans hL₂ hMπ (pull_isLB hMπ _) e₂ e₃) hπ'

end GlobalTheory.AmpleDiagSubring
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleDiagonalBundleDescendsSubringStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relAmple_diagonal_bundle_descends_subring : ∀ (R : Type) [CommRing R] (R₁ : Subring R) [IsNoetherianRing R₁] (A : Over (Sp R)) [GrpObj A] (P : LB (A ⊗ A).left) (A₁ : Over (Sp R₁)) [GrpObj A₁] (P₁ : LB (A₁ ⊗ A₁).left) (φ : A.left ⟶ A₁.left) (φ₂ : (A ⊗ A).left ⟶ (A₁ ⊗ A₁).left), IsAbelianScheme A₁ → P.IsLB → P₁.IsLB → IsGrpPullback A A₁ (spMap R₁.subtype) φ → Geo.Tor.IsSquare φ φ₂ → LBIso P (P₁.pull φ₂) → Out.RelAmple A (diagPull A P) → ∃ F : Finset R, ∀ (R₂ : Subring R) (h : R₁ ≤ R₂), (F : Set R) ⊆ R₂ → ∀ (A₂ : Over (Sp R₂)) [GrpObj A₂] (π : A₂.left ⟶ A₁.left) (π₂ : (A₂ ⊗ A₂).left ⟶ (A₁ ⊗ A₁).left), IsGrpPullback A₂ A₁ (spMap (Subring.inclusion h)) π → Geo.Tor.IsSquare π π₂ → Out.RelAmple A₂ (diagPull A₂ (P₁.pull π₂)) := by
  first | exact @GlobalTheory.AmpleDiagSubring.relAmple_diag_subring | exact GlobalTheory.AmpleDiagSubring.relAmple_diag_subring | (intros; apply GlobalTheory.AmpleDiagSubring.relAmple_diag_subring <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsEqOfSpMapSubtypeCompEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsEqOfSpMapSubtypeCompEq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings

namespace GlobalTheory

theorem sections_eq_of_spMap_subtype_comp_eq : ∀ (R : Type) [CommRing R] (R₀ : Subring R) (X : Scheme.{0})
    (p : X ⟶ Sp R₀) [IsSeparated p] (x y : Sp R₀ ⟶ X), x ≫ p = y ≫ p →
    spMap R₀.subtype ≫ x = spMap R₀.subtype ≫ y → x = y := by
  intro R _ R₀ X p _ x y hp hR
  let l : Sp R₀ ⟶ pullback p p := pullback.lift x y hp
  let c : pullback (pullback.diagonal p) l ⟶ Sp R₀ := pullback.snd _ _
  haveI : IsClosedImmersion c := inferInstance
  have e1 : l ≫ pullback.fst p p = x := pullback.lift_fst _ _ _
  have e2 : l ≫ pullback.snd p p = y := pullback.lift_snd _ _ _
  have hc : c ≫ x = c ≫ y := by
    have h1 : c ≫ l ≫ pullback.fst p p = c ≫ l ≫ pullback.snd p p := by
      rw [← Category.assoc c l, ← Category.assoc c l]
      change (pullback.snd (pullback.diagonal p) l ≫ l) ≫ _ = (pullback.snd (pullback.diagonal p) l ≫ l) ≫ _
      rw [← pullback.condition, Category.assoc, Category.assoc,
        pullback.diagonal_fst, pullback.diagonal_snd]
    rwa [e1, e2] at h1
  let k : Sp R ⟶ pullback (pullback.diagonal p) l :=
    pullback.lift (spMap R₀.subtype ≫ x) (spMap R₀.subtype) (by
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, pullback.diagonal_fst, Category.comp_id, Category.assoc, e1]
      · rw [Category.assoc, Category.assoc, pullback.diagonal_snd, Category.comp_id, Category.assoc, e2, hR])
  have hk : k ≫ c = spMap R₀.subtype := pullback.lift_snd _ _ _
  obtain ⟨hZ, hsurj⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine c
  have hinj0 : Function.Injective (spMap R₀.subtype).appTop := by
    have e := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom R₀.subtype)
    have : (spMap R₀.subtype).appTop = (Scheme.ΓSpecIso (CommRingCat.of R₀)).hom ≫
        CommRingCat.ofHom R₀.subtype ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).inv := by
      rw [← Category.assoc, ← e]; simp
    rw [this]
    intro a b hab
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at hab
    have := (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm.injective hab
    exact (Scheme.ΓSpecIso (CommRingCat.of R₀)).commRingCatIsoToRingEquiv.injective (Subtype.val_injective this)
  have hinj : Function.Injective c.appTop := by
    rw [← hk, Scheme.Hom.comp_appTop] at hinj0
    simp only [CommRingCat.hom_comp, RingHom.coe_comp] at hinj0
    exact hinj0.of_comp
  haveI : IsIso c.appTop := (ConcreteCategory.isIso_iff_bijective _).mpr ⟨hinj, hsurj⟩
  haveI : IsIso c :=
    (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms _) (arrowIsoSpecΓOfIsAffine c)).mpr
      (inferInstanceAs (IsIso (Spec.map c.appTop)))
  rw [← cancel_epi c]
  exact hc

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsEqOfSpMapSubtypeCompEqStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_spMap_subtype_comp_eq_of_isSeparated : ∀ (R : Type) [CommRing R] (R₀ : Subring R) (X : Scheme.{0}) (p : X ⟶ Sp R₀) [IsSeparated p] (x y : Sp R₀ ⟶ X), x ≫ p = y ≫ p → spMap R₀.subtype ≫ x = spMap R₀.subtype ≫ y → x = y := by
  first | exact @GlobalTheory.sections_eq_of_spMap_subtype_comp_eq | exact GlobalTheory.sections_eq_of_spMap_subtype_comp_eq | (intros; apply GlobalTheory.sections_eq_of_spMap_subtype_comp_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelObjectDataDescendsFiniteTypeSubring
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelObjectDataDescendsFiniteTypeSubring
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings

namespace GlobalTheory.SiegFg

theorem spMap_subtype_inclusion' {R : Type} [CommRing R] {S₀ R₁ : Subring R} (h : S₀ ≤ R₁) :
    spMap R₁.subtype ≫ spMap (Subring.inclusion h) = spMap S₀.subtype := by
  rw [← Spec.map_comp]
  rfl

theorem smooth_pull {S S' : Scheme.{0}} (f : S' ⟶ S) (B : Over S) (g : ℕ) (hB : SmoothOfRelativeDimension g B.hom) :
    SmoothOfRelativeDimension g ((Over.pullback f).obj B).hom :=
  (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback (IsPullback.of_hasPullback B.hom f) hB

theorem range_le {n : ℕ} {R : Type} [CommRing R] (β : cycAway n →+* R) (S₀ : Subring R)
    (h₁ : β (zetaAway n) ∈ S₀) (h₂ : ∀ hm : ((n : ℂ))⁻¹ ∈ cycAway n, β ⟨((n : ℂ))⁻¹, hm⟩ ∈ S₀) (x : cycAway n) :
    β x ∈ S₀ := by
  obtain ⟨x, hx⟩ := x
  induction hx using Subring.closure_induction with
  | mem y hy =>
    rcases hy with rfl | hy
    · exact h₁
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact h₂ _
  | zero => exact (congrArg (· ∈ S₀) (map_zero β)).mpr S₀.zero_mem
  | one => exact (congrArg (· ∈ S₀) (map_one β)).mpr S₀.one_mem
  | add y z hy hz ihy ihz =>
    have e : β ⟨y + z, Subring.add_mem _ hy hz⟩ = β ⟨y, hy⟩ + β ⟨z, hz⟩ := by rw [← map_add (f := _)]; rfl
    rw [e]; exact S₀.add_mem ihy ihz
  | neg y hy ihy =>
    have e : β ⟨-y, Subring.neg_mem _ hy⟩ = -β ⟨y, hy⟩ := by rw [← map_neg]; rfl
    rw [e]; exact S₀.neg_mem ihy
  | mul y z hy hz ihy ihz =>
    have e : β ⟨y * z, Subring.mul_mem _ hy hz⟩ = β ⟨y, hy⟩ * β ⟨z, hz⟩ := by rw [← map_mul]; rfl
    rw [e]; exact S₀.mul_mem ihy ihz

end GlobalTheory.SiegFg

namespace GlobalTheory.SiegFg

theorem siegPre_data_descends_fg : ∀ (g n : ℕ), 3 ≤ n → ∀ (R : Type) [CommRing R] (β : cycAway n →+* R) (c : SiegPre g n (zetaAway n) (spMap β)), ∃ (R₁ : Subring R) (β₁ : cycAway n →+* R₁) (A₁ : Over (Sp R₁)) (_ : GrpObj A₁) (P₁ : LB (A₁ ⊗ A₁).left) (lv₁ : Std g n → (𝟙_ (Over (Sp R₁)) ⟶ A₁)), Algebra.FiniteType ℤ R₁ ∧ R₁.subtype.comp β₁ = β ∧ IsAbelianScheme A₁ ∧ SmoothOfRelativeDimension g A₁.hom ∧ P₁.IsLB ∧ IsPullbackTriple c.A c.P (lvOf c) A₁ P₁ lv₁ (spMap R₁.subtype) := by
  intro g n hn R _ β c
  classical
  have h0 : n ≠ 0 := by omega
  haveI : NeZero n := ⟨h0⟩
  have hdim : SmoothOfRelativeDimension g c.A.hom :=
    relDim (ζ := (cycBase h0).ζ) (by omega) (isUnit_natCast h0) c
  have hm : ((n : ℂ))⁻¹ ∈ cycAway n := Subring.subset_closure (by simp)
  obtain ⟨S₀, B, _, φ, hF, hS₀, hB, hBd, hφ⟩ := GlobalTheory.AbelianLimit.abelianScheme_descends_to_fg_subring R g c.A
    {β (zetaAway n), β ⟨((n : ℂ))⁻¹, hm⟩} c.ab hdim
  have hβ : ∀ x, β x ∈ S₀ := range_le β S₀ (hF (by simp)) (fun _ => hF (by simp))
  have : IsCommMonObj B := hB.comm
  have : IsProper B.hom := hB.proper
  have : Smooth B.hom := hB.smooth
  have : QuasiCompact (B ⊗ B).hom := by
    change QuasiCompact (pullback.fst B.hom B.hom ≫ B.hom); infer_instance
  have : QuasiSeparated (B ⊗ B).hom := by
    change QuasiSeparated (pullback.fst B.hom B.hom ≫ B.hom); infer_instance

  obtain ⟨φ₂, hsq⟩ := GlobalTheory.SiegDesc.exists_isSquare hφ.1.w
  obtain ⟨SP, hSP⟩ := GlobalTheory.LBLimit.lb_descends_to_fg_subring R S₀ (c.A ⊗ c.A).left (B ⊗ B).left (c.A ⊗ c.A).hom
    (B ⊗ B).hom φ₂ c.P (GlobalTheory.SiegDesc.isPullback_of_isSquare hφ.1 hsq) c.isLB

  have hw : ∀ a : Std g n, ((lvOf c a).left ≫ φ) ≫ B.hom = spMap S₀.subtype ≫ 𝟙 _ := fun a => by
    have e : (lvOf c a).left ≫ c.A.hom = 𝟙 _ := Over.w (lvOf c a)
    rw [Category.assoc, hφ.1.w, reassoc_of% e, Category.comp_id]
  choose SL hSL using fun a : Std g n => GlobalTheory.morphism_descends_to_subring R S₀ (Sp R) (Sp S₀) B.left (𝟙 _) (𝟙 _)
    B.hom (spMap S₀.subtype) ((lvOf c a).left ≫ φ) IsPullback.of_id_snd (hw a)

  let T : Finset R := SP ∪ Finset.univ.biUnion SL
  let R₁ : Subring R := (Algebra.adjoin S₀ (T : Set R)).toSubring
  have hFT : Algebra.FiniteType ℤ R₁ :=
    GlobalTheory.SpreadGroup.finiteType_of_fg hS₀ (Subalgebra.fg_adjoin_finset T)
  have h : S₀ ≤ R₁ := fun x hx => Subalgebra.algebraMap_mem (Algebra.adjoin S₀ (T : Set R)) (⟨x, hx⟩ : S₀)
  have hT : (T : Set R) ⊆ R₁ := Algebra.subset_adjoin
  have hSPs : (SP : Set R) ⊆ R₁ := fun x hx => hT (by simp [T, Finset.mem_coe.1 hx])
  have hSLs : ∀ a, (SL a : Set R) ⊆ R₁ := fun a x hx => hT (by
    simp only [T, Finset.coe_union, Finset.coe_biUnion, Finset.coe_univ, Set.mem_univ, Set.iUnion_true]
    exact Or.inr (Set.mem_iUnion.2 ⟨a, hx⟩))
  have hj : spMap R₁.subtype ≫ spMap (Subring.inclusion h) = spMap S₀.subtype := spMap_subtype_inclusion' h

  let A₁ : Over (Sp R₁) := (Over.pullback (spMap (Subring.inclusion h))).obj B
  have hA₁ : IsAbelianScheme A₁ :=
    { comm := by infer_instance
      smooth := by show Smooth (pullback.snd _ _); infer_instance
      proper := by show IsProper (pullback.snd _ _); infer_instance
      geomConnected := by
        have := hB.geomConnected
        show GeometricallyConnected (pullback.snd _ _); infer_instance }
  have hA₁d : SmoothOfRelativeDimension g A₁.hom := smooth_pull _ B g hBd
  have hpb := Pdiv.PullbackComparison.isGrpPullback (spMap (Subring.inclusion h)) B
  let ψ : c.A.left ⟶ A₁.left := pullback.lift φ (c.A.hom ≫ spMap R₁.subtype)
    (by rw [hφ.1.w, Category.assoc, hj])
  have hψ₁ : ψ ≫ Pdiv.PullbackComparison.pφ (spMap (Subring.inclusion h)) B = φ := pullback.lift_fst _ _ _
  have hψ₂ : ψ ≫ A₁.hom = c.A.hom ≫ spMap R₁.subtype := pullback.lift_snd _ _ _
  have hgp : IsGrpPullback c.A A₁ (spMap R₁.subtype) ψ :=
    IsGrpPullback.cancel hpb (by rw [hψ₁, hj]; exact hφ) hψ₂

  obtain ⟨ψ₂, hsqψ⟩ := GlobalTheory.SiegDesc.exists_isSquare hψ₂
  obtain ⟨P₁, hP₁, hiso⟩ := hSP R₁ h hSPs (A₁ ⊗ A₁).left (A₁ ⊗ A₁).hom
    (Pdiv.PullbackComparison.pφ₂ (spMap (Subring.inclusion h)) B) ψ₂
    (GlobalTheory.SiegDesc.isPullback_of_isSquare hpb.1 (Pdiv.PullbackComparison.isSquare _ B))
    (GlobalTheory.SiegDesc.isSquare_comp hψ₁ hsqψ (Pdiv.PullbackComparison.isSquare _ B) hsq) (GlobalTheory.SiegDesc.isSquare_w hψ₂ hsqψ)

  choose ψa hψa using fun a : Std g n => hSL a R₁ h (hSLs a) (Sp R₁) (𝟙 _) (spMap (Subring.inclusion h))
    (spMap R₁.subtype) IsPullback.of_id_snd hj (by simp)
  let l : Std g n → (Sp R₁ ⟶ A₁.left) := fun a => pullback.lift (ψa a) (𝟙 _)
    (by rw [(hψa a).2, Category.comp_id, Category.id_comp])
  have hl₁ : ∀ a, l a ≫ pullback.fst _ _ = ψa a := fun a => pullback.lift_fst _ _ _
  have hl₂ : ∀ a, l a ≫ A₁.hom = 𝟙 _ := fun a => pullback.lift_snd _ _ _
  let lv₁ : Std g n → (𝟙_ (Over (Sp R₁)) ⟶ A₁) := fun a => Over.homMk (l a) (hl₂ a)
  refine ⟨R₁, β.codRestrict R₁ (fun x => h (hβ x)), A₁, inferInstance, P₁, lv₁, hFT, by ext; rfl, hA₁, hA₁d, hP₁,
    ψ, ψ₂, hgp, hsqψ.1, hsqψ.2, hiso, fun a => ?_⟩
  have e : (lvOf c a).left ≫ c.A.hom = 𝟙 _ := Over.w (lvOf c a)
  apply pullback.hom_ext
  · change (lvOf c a).left ≫ ψ ≫ pullback.fst _ _ = spMap R₁.subtype ≫ l a ≫ pullback.fst _ _
    rw [hl₁]
    exact (congrArg ((lvOf c a).left ≫ ·) hψ₁).trans (hψa a).1.symm
  · change (lvOf c a).left ≫ ψ ≫ A₁.hom = spMap R₁.subtype ≫ l a ≫ A₁.hom
    rw [hψ₂, hl₂, reassoc_of% e, Category.comp_id]

end GlobalTheory.SiegFg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelObjectDataDescendsFiniteTypeSubringStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelObject_data_descends_finiteType_subring : ∀ (g n : ℕ), 3 ≤ n → ∀ (R : Type) [CommRing R] (β : cycAway n →+* R) (c : SiegPre g n (zetaAway n) (spMap β)), ∃ (R₁ : Subring R) (β₁ : cycAway n →+* R₁) (A₁ : Over (Sp R₁)) (_ : GrpObj A₁) (P₁ : LB (A₁ ⊗ A₁).left) (lv₁ : Std g n → (𝟙_ (Over (Sp R₁)) ⟶ A₁)), Algebra.FiniteType ℤ R₁ ∧ R₁.subtype.comp β₁ = β ∧ IsAbelianScheme A₁ ∧ SmoothOfRelativeDimension g A₁.hom ∧ P₁.IsLB ∧ IsPullbackTriple c.A c.P (lvOf c) A₁ P₁ lv₁ (spMap R₁.subtype) := by
  first | exact @GlobalTheory.SiegFg.siegPre_data_descends_fg | exact GlobalTheory.SiegFg.siegPre_data_descends_fg | (intros; apply GlobalTheory.SiegFg.siegPre_data_descends_fg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidSymmetricBundleDescendsToSubringFinset
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidSymmetricBundleDescendsToSubringFinset
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RigSymDescent

theorem axes_sq {S' S : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [GrpObj G] {f : S' ⟶ S}
    {ψ : G'.left ⟶ G.left} {ψ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left} (hG : IsGrpPullback G' G f ψ)
    (sq : Geo.Tor.IsSquare ψ ψ₂) :
    (lift (1 : G' ⟶ G') (𝟙 G')).left ≫ ψ₂ = ψ ≫ (lift (1 : G ⟶ G) (𝟙 G)).left ∧
    (lift (𝟙 G') (1 : G' ⟶ G')).left ≫ ψ₂ = ψ ≫ (lift (𝟙 G) (1 : G ⟶ G)).left ∧
    (lift (snd G' G') (fst G' G')).left ≫ ψ₂ = ψ₂ ≫ (lift (snd G G) (fst G G)).left := by
  let U : Over.mk (G'.hom ≫ f) ⟶ G := Over.homMk ψ hG.1.w
  have o₁ : (1 : G' ⟶ G').left ≫ ψ = ψ ≫ (1 : G ⟶ G).left :=
    congrArg (fun q => q.left) ((map_one (pushHom hG G')).trans (MonObj.comp_one U).symm)
  have e : ∀ (x y : G' ⟶ G') (x₀ y₀ : G ⟶ G), x.left ≫ ψ = ψ ≫ x₀.left → y.left ≫ ψ = ψ ≫ y₀.left →
      (lift x y).left ≫ ψ₂ = ψ ≫ (lift x₀ y₀).left := fun x y x₀ y₀ hx hy =>
    (Category.id_comp _).symm.trans (GlobalTheory.SiegelPull.lift_sq sq (T := Over.mk (G'.hom ≫ f)) (𝟙 G'.left) x y ψ x₀ y₀
      ((Category.id_comp _).trans hx) ((Category.id_comp _).trans hy))
  refine ⟨e _ _ _ _ o₁ (by simp), e _ _ _ _ (by simp) o₁, ?_⟩
  exact (Category.id_comp _).symm.trans (GlobalTheory.SiegelPull.lift_sq sq (T := Over.mk ((G' ⊗ G').hom ≫ f))
    (𝟙 (G' ⊗ G').left) _ _ ψ₂ _ _ ((Category.id_comp _).trans sq.2.symm) ((Category.id_comp _).trans sq.1.symm))

end GlobalTheory.RigSymDescent

namespace GlobalTheory


open GlobalTheory.CechPic in
theorem rigSym_descends_to_subring_containing_finset : ∀ (R : Type) [CommRing R] (R₁ : Subring R) (A : Over (Sp R)) [GrpObj A] (P : LB (A ⊗ A).left) (A₁ : Over (Sp R₁)) [GrpObj A₁] (P₁ : LB (A₁ ⊗ A₁).left) (φ : A.left ⟶ A₁.left) (φ₂ : (A ⊗ A).left ⟶ (A₁ ⊗ A₁).left), IsAbelianScheme A₁ → P.IsLB → P₁.IsLB → IsGrpPullback A A₁ (spMap R₁.subtype) φ → Geo.Tor.IsSquare φ φ₂ → LBIso P (P₁.pull φ₂) → IsTrivial (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left) → IsTrivial (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → ∃ F : Finset R, ∀ (R₂ : Subring R) (h : R₁ ≤ R₂), (F : Set R) ⊆ R₂ → ∀ (A₂ : Over (Sp R₂)) [GrpObj A₂] (π : A₂.left ⟶ A₁.left) (π₂ : (A₂ ⊗ A₂).left ⟶ (A₁ ⊗ A₁).left), IsGrpPullback A₂ A₁ (spMap (Subring.inclusion h)) π → Geo.Tor.IsSquare π π₂ → IsTrivial ((P₁.pull π₂).pull (lift (1 : A₂ ⟶ A₂) (𝟙 A₂)).left) ∧ IsTrivial ((P₁.pull π₂).pull (lift (𝟙 A₂) (1 : A₂ ⟶ A₂)).left) ∧ LBIso (P₁.pull π₂) ((P₁.pull π₂).pull (lift (snd A₂ A₂) (fst A₂ A₂)).left) := by
  intro R _ R₁ A _ P A₁ _ P₁ φ φ₂ hab hP hP₁ hA sq hiso h1 h2 hs
  classical
  have := hab.proper
  haveI : QuasiCompact (A₁ ⊗ A₁).hom := inferInstanceAs (QuasiCompact (pullback.fst A₁.hom A₁.hom ≫ A₁.hom))
  haveI : QuasiSeparated (A₁ ⊗ A₁).hom :=
    inferInstanceAs (QuasiSeparated (pullback.fst A₁.hom A₁.hom ≫ A₁.hom))
  obtain ⟨e₁, e₂, e₃⟩ := GlobalTheory.RigSymDescent.axes_sq hA sq
  have hc : cls P hP = pull φ₂ (cls P₁ hP₁) := (cls_eq_iff hP (pull_isLB hP₁ _)).2 hiso
  have hT := LB.isLB_triv A₁.left
  have z : ∀ {Y : Scheme.{0}} (g : Y ⟶ A₁.left), pull g (cls _ hT) = 0 := fun g => map_zero (pull g)

  have d₁ : LBIso ((P₁.pull (lift (1 : A₁ ⟶ A₁) (𝟙 A₁)).left).pull φ) ((LB.triv A₁.left).pull φ) := by
    refine (cls_eq_iff (pull_isLB (pull_isLB hP₁ _) _) (pull_isLB hT _)).1 ?_
    rw [cls_pull (pull_isLB hP₁ _), cls_pull hP₁, cls_pull hT, z, ← pull_comp, ← e₁, pull_comp, ← hc,
      ← cls_pull hP _ (pull_isLB hP _)]
    exact (cls_eq_zero_iff _).2 h1
  have d₂ : LBIso ((P₁.pull (lift (𝟙 A₁) (1 : A₁ ⟶ A₁)).left).pull φ) ((LB.triv A₁.left).pull φ) := by
    refine (cls_eq_iff (pull_isLB (pull_isLB hP₁ _) _) (pull_isLB hT _)).1 ?_
    rw [cls_pull (pull_isLB hP₁ _), cls_pull hP₁, cls_pull hT, z, ← pull_comp, ← e₂, pull_comp, ← hc,
      ← cls_pull hP _ (pull_isLB hP _)]
    exact (cls_eq_zero_iff _).2 h2
  have d₃ : LBIso (P₁.pull φ₂) ((P₁.pull (lift (snd A₁ A₁) (fst A₁ A₁)).left).pull φ₂) := by
    refine (cls_eq_iff (pull_isLB hP₁ _) (pull_isLB (pull_isLB hP₁ _) _)).1 ?_
    rw [cls_pull hP₁, cls_pull (pull_isLB hP₁ _), cls_pull hP₁, ← pull_comp, ← e₃, pull_comp, ← hc,
      ← cls_pull hP _ (pull_isLB hP _)]
    exact (cls_eq_iff hP (pull_isLB hP _)).2 hs
  obtain ⟨F₁, H₁⟩ := lbIso_descends_to_subring_containing_finset R R₁ A.left A₁.left A.hom A₁.hom φ _ _ hA.1
    (pull_isLB hP₁ _) hT d₁
  obtain ⟨F₂, H₂⟩ := lbIso_descends_to_subring_containing_finset R R₁ A.left A₁.left A.hom A₁.hom φ _ _ hA.1
    (pull_isLB hP₁ _) hT d₂
  obtain ⟨F₃, H₃⟩ := lbIso_descends_to_subring_containing_finset R R₁ (A ⊗ A).left (A₁ ⊗ A₁).left (A ⊗ A).hom
    (A₁ ⊗ A₁).hom φ₂ _ _ (SiegDesc.isPullback_of_isSquare hA.1 sq) hP₁ (pull_isLB hP₁ _) d₃
  refine ⟨F₁ ∪ F₂ ∪ F₃, fun R₂ h hF A₂ _ π π₂ hB sqB => ?_⟩
  simp only [Finset.coe_union, Set.union_subset_iff] at hF
  obtain ⟨f₁, f₂, f₃⟩ := GlobalTheory.RigSymDescent.axes_sq hB sqB
  have k₁ := H₁ R₂ h hF.1.1 A₂.left A₂.hom π hB.1
  have k₂ := H₂ R₂ h hF.1.2 A₂.left A₂.hom π hB.1
  have k₃ := H₃ R₂ h hF.2 (A₂ ⊗ A₂).left (A₂ ⊗ A₂).hom π₂ (SiegDesc.isPullback_of_isSquare hB.1 sqB)
  refine ⟨(cls_eq_zero_iff (pull_isLB (pull_isLB hP₁ _) _)).1 ?_, (cls_eq_zero_iff (pull_isLB (pull_isLB hP₁ _) _)).1 ?_,
    (cls_eq_iff (pull_isLB hP₁ _) (pull_isLB (pull_isLB hP₁ _) _)).1 ?_⟩
  · have := (cls_eq_iff (pull_isLB (pull_isLB hP₁ _) _) (pull_isLB hT _)).2 k₁
    rw [cls_pull (pull_isLB hP₁ _), cls_pull hP₁, cls_pull hT, z, ← pull_comp] at this
    rw [cls_pull (pull_isLB hP₁ _), cls_pull hP₁, ← pull_comp, f₁]
    exact this
  · have := (cls_eq_iff (pull_isLB (pull_isLB hP₁ _) _) (pull_isLB hT _)).2 k₂
    rw [cls_pull (pull_isLB hP₁ _), cls_pull hP₁, cls_pull hT, z, ← pull_comp] at this
    rw [cls_pull (pull_isLB hP₁ _), cls_pull hP₁, ← pull_comp, f₂]
    exact this
  · have := (cls_eq_iff (pull_isLB hP₁ _) (pull_isLB (pull_isLB hP₁ _) _)).2 k₃
    rw [cls_pull hP₁, cls_pull (pull_isLB hP₁ _), cls_pull hP₁, ← pull_comp] at this
    rw [cls_pull hP₁, cls_pull (pull_isLB hP₁ _), cls_pull hP₁, ← pull_comp, f₃]
    exact this

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidSymmetricBundleDescendsToSubringFinsetStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rigidSymmetricBundle_descends_to_subring_finset : ∀ (R : Type) [CommRing R] (R₁ : Subring R) (A : Over (Sp R)) [GrpObj A] (P : LB (A ⊗ A).left) (A₁ : Over (Sp R₁)) [GrpObj A₁] (P₁ : LB (A₁ ⊗ A₁).left) (φ : A.left ⟶ A₁.left) (φ₂ : (A ⊗ A).left ⟶ (A₁ ⊗ A₁).left), IsAbelianScheme A₁ → P.IsLB → P₁.IsLB → IsGrpPullback A A₁ (spMap R₁.subtype) φ → Geo.Tor.IsSquare φ φ₂ → LBIso P (P₁.pull φ₂) → IsTrivial (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left) → IsTrivial (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → ∃ F : Finset R, ∀ (R₂ : Subring R) (h : R₁ ≤ R₂), (F : Set R) ⊆ R₂ → ∀ (A₂ : Over (Sp R₂)) [GrpObj A₂] (π : A₂.left ⟶ A₁.left) (π₂ : (A₂ ⊗ A₂).left ⟶ (A₁ ⊗ A₁).left), IsGrpPullback A₂ A₁ (spMap (Subring.inclusion h)) π → Geo.Tor.IsSquare π π₂ → IsTrivial ((P₁.pull π₂).pull (lift (1 : A₂ ⟶ A₂) (𝟙 A₂)).left) ∧ IsTrivial ((P₁.pull π₂).pull (lift (𝟙 A₂) (1 : A₂ ⟶ A₂)).left) ∧ LBIso (P₁.pull π₂) ((P₁.pull π₂).pull (lift (snd A₂ A₂) (fst A₂ A₂)).left) := by
  first | exact @GlobalTheory.rigSym_descends_to_subring_containing_finset | exact GlobalTheory.rigSym_descends_to_subring_containing_finset | (intros; apply GlobalTheory.rigSym_descends_to_subring_containing_finset <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackPolarizedLevelTripleOfSubringLe
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackPolarizedLevelTripleOfSubringLe
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings

namespace GlobalTheory.SiegBaseChange

open GlobalTheory.CechPic

theorem spMap_subtype_comp_inclusion {R : Type} [CommRing R] {R₁ R₂ : Subring R} (h : R₁ ≤ R₂) :
    spMap R₂.subtype ≫ spMap (Subring.inclusion h) = spMap R₁.subtype := by
  simp only [spMap, ← Spec.map_comp]
  rfl

theorem pullbackTriple_of_le : ∀ (R : Type) [CommRing R] (R₁ R₂ : Subring R) (h : R₁ ≤ R₂) (g M : ℕ) (A : Over (Sp R)) [GrpObj A] (P : LB (A ⊗ A).left) (lv : Std g M → (𝟙_ (Over (Sp R)) ⟶ A)) (A₁ : Over (Sp R₁)) [GrpObj A₁] (P₁ : LB (A₁ ⊗ A₁).left) (lv₁ : Std g M → (𝟙_ (Over (Sp R₁)) ⟶ A₁)), IsAbelianScheme A₁ → SmoothOfRelativeDimension g A₁.hom → P.IsLB → P₁.IsLB → IsPullbackTriple A P lv A₁ P₁ lv₁ (spMap R₁.subtype) → ∃ (A₂ : Over (Sp R₂)) (_ : GrpObj A₂) (lv₂ : Std g M → (𝟙_ (Over (Sp R₂)) ⟶ A₂)) (π : A₂.left ⟶ A₁.left) (π₂ : (A₂ ⊗ A₂).left ⟶ (A₁ ⊗ A₁).left), IsAbelianScheme A₂ ∧ SmoothOfRelativeDimension g A₂.hom ∧ IsGrpPullback A₂ A₁ (spMap (Subring.inclusion h)) π ∧ Geo.Tor.IsSquare π π₂ ∧ IsPullbackTriple A P lv A₂ (P₁.pull π₂) lv₂ (spMap R₂.subtype) := by
  intro R _ R₁ R₂ h g M A _ P lv A₁ _ P₁ lv₁ hab hsm hP hP₁ H
  haveI := hab.comm
  obtain ⟨φ, φ₂, hφ, s₁, s₂, iso, hl⟩ := H
  have e := spMap_subtype_comp_inclusion h
  have pb₂ := Pdiv.PullbackComparison.isGrpPullback (spMap (Subring.inclusion h)) A₁
  have sq₂ := Pdiv.PullbackComparison.isSquare (spMap (Subring.inclusion h)) A₁
  have hw : φ ≫ A₁.hom = (A.hom ≫ spMap R₂.subtype) ≫ spMap (Subring.inclusion h) := by
    rw [hφ.1.w, Category.assoc, e]
  let ψ : A.left ⟶ ((Over.pullback (spMap (Subring.inclusion h))).obj A₁).left := pb₂.1.lift φ _ hw
  have hψ₁ : ψ ≫ Pdiv.PullbackComparison.pφ (spMap (Subring.inclusion h)) A₁ = φ := pb₂.1.lift_fst _ _ _
  have hψ₂ : ψ ≫ ((Over.pullback (spMap (Subring.inclusion h))).obj A₁).hom = A.hom ≫ spMap R₂.subtype :=
    pb₂.1.lift_snd _ _ _
  have hψ : IsGrpPullback A ((Over.pullback (spMap (Subring.inclusion h))).obj A₁) (spMap R₂.subtype) ψ :=
    pb₂.cancel (by rw [hψ₁, e]; exact hφ) hψ₂
  obtain ⟨ψ₂, sqψ⟩ := GlobalTheory.SiegDesc.exists_isSquare hψ₂
  have hc : ψ₂ ≫ Pdiv.PullbackComparison.pφ₂ (spMap (Subring.inclusion h)) A₁ = φ₂ :=
    GlobalTheory.SiegDesc.isSquare_comp hψ₁ sqψ sq₂ ⟨s₁, s₂⟩
  refine ⟨(Over.pullback (spMap (Subring.inclusion h))).obj A₁, inferInstance,
    fun a => GlobalTheory.SiegelPull.secPull pb₂ (lv₁ a), Pdiv.PullbackComparison.pφ _ A₁, Pdiv.PullbackComparison.pφ₂ _ A₁, ?_, ?_, pb₂, sq₂,
    ψ, ψ₂, hψ, sqψ.1, sqψ.2, ?_, fun a => ?_⟩
  · exact
      { comm := inferInstance
        smooth := by have := hab.smooth; show Smooth (pullback.snd _ _); infer_instance
        proper := by have := hab.proper; show IsProper (pullback.snd _ _); infer_instance
        geomConnected := by
          have := hab.geomConnected
          show GeometricallyConnected (pullback.snd _ _); infer_instance }
  · exact (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback pb₂.1 hsm
  · have hP₂ := pull_isLB hP₁ (Pdiv.PullbackComparison.pφ₂ (spMap (Subring.inclusion h)) A₁)
    refine (cls_eq_iff hP (pull_isLB hP₂ ψ₂)).1 ?_
    rw [(cls_eq_iff hP (pull_isLB hP₁ φ₂)).2 iso, cls_pull hP₂ ψ₂, cls_pull hP₁ _ hP₂, ← pull_comp, hc]
    rfl
  · apply pb₂.1.hom_ext
    · rw [Category.assoc, hψ₁, hl a, Category.assoc, GlobalTheory.SiegelPull.secPull_left, ← Category.assoc, e]
    · rw [Category.assoc, hψ₂, ← Category.assoc, Over.w (lv a), Category.assoc, Over.w]
      rfl

end GlobalTheory.SiegBaseChange
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackPolarizedLevelTripleOfSubringLeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullbackPolarizedLevelTriple_of_subring_le : ∀ (R : Type) [CommRing R] (R₁ R₂ : Subring R) (h : R₁ ≤ R₂) (g M : ℕ) (A : Over (Sp R)) [GrpObj A] (P : LB (A ⊗ A).left) (lv : Std g M → (𝟙_ (Over (Sp R)) ⟶ A)) (A₁ : Over (Sp R₁)) [GrpObj A₁] (P₁ : LB (A₁ ⊗ A₁).left) (lv₁ : Std g M → (𝟙_ (Over (Sp R₁)) ⟶ A₁)), IsAbelianScheme A₁ → SmoothOfRelativeDimension g A₁.hom → P.IsLB → P₁.IsLB → IsPullbackTriple A P lv A₁ P₁ lv₁ (spMap R₁.subtype) → ∃ (A₂ : Over (Sp R₂)) (_ : GrpObj A₂) (lv₂ : Std g M → (𝟙_ (Over (Sp R₂)) ⟶ A₂)) (π : A₂.left ⟶ A₁.left) (π₂ : (A₂ ⊗ A₂).left ⟶ (A₁ ⊗ A₁).left), IsAbelianScheme A₂ ∧ SmoothOfRelativeDimension g A₂.hom ∧ IsGrpPullback A₂ A₁ (spMap (Subring.inclusion h)) π ∧ Geo.Tor.IsSquare π π₂ ∧ IsPullbackTriple A P lv A₂ (P₁.pull π₂) lv₂ (spMap R₂.subtype) := by
  first | exact @GlobalTheory.SiegBaseChange.pullbackTriple_of_le | exact GlobalTheory.SiegBaseChange.pullbackTriple_of_le | (intros; apply GlobalTheory.SiegBaseChange.pullbackTriple_of_le <;> assumption)
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings

namespace GlobalTheory.SiegFGData

theorem data : ∀ (g n : ℕ), 3 ≤ n → Odd n → ∀ (R : Type) [CommRing R] (β : cycAway n →+* R) (c : SiegPre g n (zetaAway n) (spMap β)), c.Principal → ∃ (R₀ : Subring R) (β₀ : cycAway n →+* R₀) (A₀ : Over (Sp R₀)) (_ : GrpObj A₀) (P₀ : LB (A₀ ⊗ A₀).left) (lv₀ : Std g n → (𝟙_ (Over (Sp R₀)) ⟶ A₀)), Algebra.FiniteType ℤ R₀ ∧ R₀.subtype.comp β₀ = β ∧ IsSymmetricPair g A₀ P₀ ∧ (∀ a b, lv₀ (a + b) = lv₀ a * lv₀ b) ∧ Out.RelAmple A₀ (diagPull A₀ P₀) ∧ IsPullbackTriple c.A c.P (lvOf c) A₀ P₀ lv₀ (spMap R₀.subtype) := by
  intro g n hn _ R _ β c hc
  have h0 : n ≠ 0 := by omega
  obtain ⟨R₁, β₁, A₁, _, P₁, lv₁, hfg, hβ, hA₁, hd₁, hP₁, htr⟩ := GlobalTheory.T.siegelObject_data_descends_finiteType_subring g n hn R β c
  have htr' := htr
  obtain ⟨φ, φ₂, hφ, sq₁, sq₂, iso, hl⟩ := htr
  have : IsNoetherianRing R₁ := Algebra.FiniteType.isNoetherianRing ℤ R₁
  have hsym : IsSymmetricPair g c.A c.P := isSymmetricPair (ζ := (cycBase h0).ζ) (by omega) (isUnit_natCast h0) c
  have hlev : IsLevel c.A (lvOf c) := isLevel_lvOf (ζ := (cycBase h0).ζ) c
  obtain ⟨hAb, hdim, hPlb, hr1, hr2, hsy⟩ := hsym
  obtain ⟨F₅, H₅⟩ := GlobalTheory.T.rigidSymmetricBundle_descends_to_subring_finset R R₁ c.A c.P A₁ P₁ φ φ₂ hA₁ hPlb hP₁ hφ ⟨sq₁, sq₂⟩ iso hr1 hr2 hsy
  obtain ⟨F₂, H₂⟩ := GlobalTheory.T.relAmple_diagonal_bundle_descends_subring R R₁ c.A c.P A₁ P₁ φ φ₂ hA₁ hPlb hP₁ hφ ⟨sq₁, sq₂⟩ iso hc.1
  classical
  let S : Subalgebra R₁ R := Algebra.adjoin R₁ ((F₅ ∪ F₂ : Finset R) : Set R)
  let R₂ : Subring R := S.toSubring
  have h12 : R₁ ≤ R₂ := fun x hx => S.algebraMap_mem ⟨x, hx⟩
  have hF : ((F₅ ∪ F₂ : Finset R) : Set R) ⊆ R₂ := Algebra.subset_adjoin
  have hfg₂ : Algebra.FiniteType ℤ R₂ := GlobalTheory.SpreadGroup.finiteType_of_fg hfg (Subalgebra.fg_adjoin_finset _)
  obtain ⟨A₂, _, lv₂, π, π₂, hA₂, hd₂, hπ, sqπ, htr₂⟩ :=
    GlobalTheory.T.pullbackPolarizedLevelTriple_of_subring_le R R₁ R₂ h12 g n c.A c.P (lvOf c) A₁ P₁ lv₁ hA₁ hd₁ hPlb hP₁ htr'
  obtain ⟨t1, t2, t3⟩ := H₅ R₂ h12 (fun x hx => hF (by simp [hx])) A₂ π π₂ hπ sqπ
  have am := H₂ R₂ h12 (fun x hx => hF (by simp [hx])) A₂ π π₂ hπ sqπ
  refine ⟨R₂, (Subring.inclusion h12).comp β₁, A₂, inferInstance, P₁.pull π₂, lv₂, hfg₂, ?_,
    ⟨hA₂, hd₂, pull_isLB hP₁ _, t1, t2, t3⟩, ?_, am, htr₂⟩
  · rw [← hβ]
    rfl
  · intro a b
    obtain ⟨ψ, ψ₂, hψ, -, -, -, hl₂⟩ := htr₂
    have : IsSeparated A₂.hom := by have := hA₂.proper; infer_instance
    refine Over.OverMorphism.ext (GlobalTheory.T.eq_of_spMap_subtype_comp_eq_of_isSeparated R R₂ A₂.left A₂.hom _ _ ?_ ?_)
    · exact (Over.w (lv₂ (a + b))).trans (Over.w (lv₂ a * lv₂ b)).symm
    · let f := spMap R₂.subtype
      let u : Over.mk ((𝟙_ (Over (Sp R))).hom ≫ f) ⟶ 𝟙_ (Over (Sp R₂)) := toUnit _
      have hu : u.left = (𝟙_ (Over (Sp R))).hom ≫ f := Over.toUnit_left
      have hid : (𝟙_ (Over (Sp R))).hom = 𝟙 _ := rfl
      have m := hψ.2 (𝟙_ (Over (Sp R))) (lvOf c a) (lvOf c b) (u ≫ lv₂ a) (u ≫ lv₂ b)
        (by rw [Over.comp_left, hu, hid, Category.id_comp]; exact (hl₂ a).symm)
        (by rw [Over.comp_left, hu, hid, Category.id_comp]; exact (hl₂ b).symm)
      rw [← MonObj.comp_mul, Over.comp_left, hu, hid, Category.id_comp, ← hlev.1] at m
      exact (hl₂ (a + b)).symm.trans m.symm

end GlobalTheory.SiegFGData
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymplecticOfSubring
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings

open GlobalTheory.EighthPower GlobalTheory.CechPic GlobalTheory.MatrixBundle GlobalTheory.ZM

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SympDescent

theorem translFixed_of_pair {S : Scheme.{0}} {h M : ℕ} (A : Over S) [GrpObj A] (P : LB (A ⊗ A).left)
    (H : IsSymmetricPair h A P) (ha : Out.RelAmple A (diagPull A P)) (x : 𝟙_ (Over S) ⟶ A) (hx : x ^ M = 1) :
    (M : ℤ) • cls (diagPull A P) (pull_isLB H.2.2.1 _) =
      (M : ℤ) • pull ((toUnit A ≫ x) * 𝟙 A).left (cls (diagPull A P) (pull_isLB H.2.2.1 _)) := by
  haveI := H.1.comm
  have hP := H.2.2.1
  have hb : IsSymBilin (cls P hP) := isSymBilin_of_gen hP (fun T x x' y =>
    (Biadditive.biadditive_of_triv_axes globalFns_holds S A (diagPull A P) H.1 (pull_isLB hP _) ha P hP
      H.2.2.2.1 H.2.2.2.2.1 T x x' y).1) H.2.2.2.2.2
  have d : ∀ f : A ⟶ A, pull f.left (cls (diagPull A P) (pull_isLB hP _)) = pairCls (cls P hP) f f := fun f =>
    (pull_pairCls (cls P hP) f (𝟙 _) (𝟙 _)).trans (by rw [Category.comp_id])
  have z : ∀ y : A ⟶ A, (M : ℤ) • pairCls (cls P hP) (toUnit A ≫ x) y = 0 := fun y => by
    have e := BilinCalc.map_prod_zpow (fun z => pairCls (cls P hP) z y) (fun a b => hb.mul _ a b y)
      (fun _ : Fin 1 => toUnit A ≫ x) fun _ => (M : ℤ)
    simp only [Finset.univ_unique, Finset.prod_const, Finset.card_singleton, pow_one, Finset.sum_const, one_smul,
      zpow_natCast] at e
    rw [← e, ← MonObj.comp_pow, hx, MonObj.comp_one]
    exact one_left (hb.mul _) y
  rw [d, hb.mul, hb.symm _ (𝟙 A) (_ * _), hb.mul, smul_add, smul_add, z, z, zero_add, zero_add]
  rfl

theorem units_map_comp_appTop {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (u : Γ(Z, ⊤)ˣ) :
    Units.map (f ≫ g).appTop.hom.toMonoidHom u =
      Units.map f.appTop.hom.toMonoidHom (Units.map g.appTop.hom.toMonoidHom u) :=
  Units.ext (by simp [Scheme.Hom.comp_appTop]; rfl)

theorem isSymplectic_of_subring : ∀ (h M : ℕ) (B R : Type) [CommRing B] [CommRing R] (ζ : Bˣ) (R₁ : Subring R) (s₁ : Sp R₁ ⟶ Sp B) (A : Over (Sp R)) [GrpObj A] (P : LB (A ⊗ A).left) (lv : Std h M → (𝟙_ (Over (Sp R)) ⟶ A)) (A₁ : Over (Sp R₁)) [GrpObj A₁] (P₁ : LB (A₁ ⊗ A₁).left) (lv₁ : Std h M → (𝟙_ (Over (Sp R₁)) ⟶ A₁)), 0 < M → ζ ^ M = 1 → IsUnit (M : R₁) → IsSymmetricPair h A₁ P₁ → IsPrincipal A₁ P₁ → IsLevel A₁ lv₁ → P.IsLB → IsPullbackTriple A P lv A₁ P₁ lv₁ (spMap R₁.subtype) → IsSymplectic ζ (spMap R₁.subtype ≫ s₁) A P lv → IsSymplectic ζ s₁ A₁ P₁ lv₁ := by
  intro h M B R _ _ ζ R₁ s₁ A _ P lv A₁ _ P₁ lv₁ hM hζ hu H₁ H₂ H₃ hPR Hpb Hs
  haveI := H₁.1.comm
  have hP := H₁.2.2.1
  have hD : (diagPull A₁ P₁).IsLB := pull_isLB hP _
  have z₀ : lv₁ 0 = 1 := by
    have e := H₃.1 0 0
    rw [add_zero] at e
    exact left_eq_mul.1 e
  have tors : ∀ a, lv₁ a ^ M = 1 := fun a => by
    have e : ∀ n : ℕ, lv₁ (n • a) = lv₁ a ^ n := fun n => by
      induction n with
      | zero => rw [zero_smul, pow_zero, z₀]
      | succ n ih => rw [succ_nsmul, H₃.1, ih, pow_succ]
    rw [← e, show M • a = 0 by ext i <;> simp, z₀]
  have th : ∀ a (p : (𝟙_ (Over (Sp R₁))).left), ∃ V : (𝟙_ (Over (Sp R₁))).left.Opens, p ∈ V ∧
      ∃ θ : Out.ThetaGrp A₁ (diagPull A₁ P₁) M (Out.overRes V), θ.pt = Out.overResι V ≫ lv₁ a := fun a p => by
    let T := Out.overRes (T := 𝟙_ (Over (Sp R₁))) ⊤
    have hT : (Out.thetaLB A₁ (diagPull A₁ P₁) M (Out.overResι ⊤ ≫ lv₁ a)).IsLB := LB.isLB_linComb hD _ _
    obtain ⟨t, ht⟩ := (cls_eq_zero_iff hT).1 (by
      unfold Out.thetaLB at hT ⊢
      rw [cls_linComb hD, Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, neg_smul]
      have e : Out.translPt A₁ (Out.overResι ⊤ ≫ lv₁ a) = snd T A₁ ≫ ((toUnit A₁ ≫ lv₁ a) * 𝟙 A₁) := by
        rw [MonObj.comp_mul, Category.comp_id, comp_toUnit_assoc, Out.translPt, ← Hom.mul_def, ← Category.assoc,
          toUnit_unique (fst _ _ ≫ _) (toUnit _)]
      rw [e, Over.comp_left, pull_comp, ← map_zsmul, ← map_zsmul,
        ← GlobalTheory.SympDescent.translFixed_of_pair A₁ P₁ H₁ H₂.1 (lv₁ a) (tors a), add_neg_cancel])
    exact ⟨⊤, trivial, ⟨_, t, ht⟩, rfl⟩
  obtain ⟨φ, φ₂, pb, s₁', s₂', iso, hl⟩ := Hpb
  have hdi : LBIso (diagPull A P) ((diagPull A₁ P₁).pull φ) := GlobalTheory.SiegelPull.diag_iso ⟨s₁', s₂'⟩ iso
  have hL : (diagPull A P).IsLB := pull_isLB hPR _

  have inj : Function.Injective ((𝟙_ (Over (Sp R))).hom ≫ spMap R₁.subtype).appTop.hom := by
    have u₁ : (𝟙_ (Over (Sp R))).hom = 𝟙 _ := rfl
    rw [u₁, Category.id_comp]
    have k : ∀ z, (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((spMap R₁.subtype).appTop.hom z) =
        ((Scheme.ΓSpecIso (CommRingCat.of R₁)).hom.hom z : R) := fun z => by
      have e := congrArg (fun q => q.hom z) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom R₁.subtype))
      first
        | exact e
        | (simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom, Subring.subtype_apply] at e; exact e)
    intro x y hxy
    have h2 := congrArg (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom hxy
    rw [k, k] at h2
    have h3 := congrArg (Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (Subtype.val_injective h2)
    simpa using h3
  intro a b
  obtain ⟨c, hc⟩ := CommutatorPairing.exists_weilIs globalFns_holds H₁.1 hD (th a) (th b)
  let X' : Over (Sp R₁) := Over.mk ((𝟙_ (Over (Sp R))).hom ≫ spMap R₁.subtype)
  have ex : ∀ a, (toUnit X' ≫ lv₁ a).left = (lv a).left ≫ φ := fun a => by
    rw [Over.comp_left, Over.toUnit_left, hl a]
    exact Category.assoc _ _ _
  have w := (weilIs_grpPullback_of_comm (Sp R₁) (Sp R) A₁ A (spMap R₁.subtype) φ (diagPull A₁ P₁) (diagPull A P)
    hD hL pb hdi (𝟙_ (Over (Sp R))) M (lv a) (lv b) (toUnit X' ≫ lv₁ a) (toUnit X' ≫ lv₁ b) _ (ex a) (ex b)).1 (Hs a b)
  have w' := CommPairing.weilIs_pull globalFns_holds H₁.1 hD (toUnit X') hc
  have q := CommutatorPairing.weilIs_unique globalFns_holds H₁.1 hD w' w
  have u₂ : (𝟙_ (Over (Sp R₁))).hom = 𝟙 _ := rfl
  have hinj : Function.Injective (Units.map (toUnit X').left.appTop.hom.toMonoidHom) := fun u v huv =>
    Units.ext (inj (by
      have := congrArg Units.val huv
      simp only [Units.coe_map, MonoidHom.coe_coe, Over.toUnit_left] at this
      exact this))
  have q₂ : Units.map (toUnit X').left.appTop.hom.toMonoidHom
      (Units.map ((𝟙_ (Over (Sp R₁))).hom ≫ s₁).appTop.hom.toMonoidHom (unitOn (ζ ^ (2 * stdForm a b).val))) =
      Units.map ((𝟙_ (Over (Sp R))).hom ≫ spMap R₁.subtype ≫ s₁).appTop.hom.toMonoidHom
        (unitOn (ζ ^ (2 * stdForm a b).val)) := by
    rw [← GlobalTheory.SympDescent.units_map_comp_appTop, Over.toUnit_left, u₂, Category.id_comp]
    rfl
  rw [← hinj (q.trans q₂.symm)]
  exact hc

end GlobalTheory.SympDescent
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeomPtSpecializes
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings

noncomputable section

namespace GlobalTheory.LevelDescent

open GlobalTheory.SiegelPull GlobalTheory.CharZeroPts

theorem exists_geomPt_specializes (R : Type) [CommRing R] (R₁ : Subring R) (p : Sp R₁) :
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (z : Sp K ⟶ Sp R), ∀ u, (z ≫ spMap R₁.subtype) u ⤳ p := by
  haveI := p.isPrime
  obtain ⟨q, hq, hqp⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal R₁)) (J := p.asIdeal) bot_le
  obtain ⟨P, hP, hPq⟩ :=
    Ideal.exists_comap_eq_of_mem_minimalPrimes_of_injective (f := R₁.subtype) Subtype.val_injective q hq
  obtain ⟨K, _, _, t, ht⟩ := GlobalTheory.SiegelTypings.exists_geomPt (S := Sp R) ⟨P, hP⟩
  refine ⟨K, inferInstance, inferInstance, t, fun u => ?_⟩
  have e : t u = ⟨P, hP⟩ := by
    obtain ⟨v, hv⟩ := ht
    rw [Subsingleton.elim u v, hv]
  rw [Scheme.Hom.comp_apply, e]
  refine (PrimeSpectrum.le_iff_specializes _ _).1 ?_
  show P.comap R₁.subtype ≤ p.asIdeal
  rw [hPq]
  exact hqp

section Labels

variable {h M : ℕ}

def toStd : (Fin (h + h) → ZMod M) →+ IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit.Std h M where
  toFun c := (fun i => c (Fin.castAdd h i), fun i => c (Fin.natAdd h i))
  map_zero' := rfl
  map_add' _ _ := rfl

theorem toStd_append (a : IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit.Std h M) : toStd (Fin.append a.1 a.2) = a :=
  Prod.ext (funext fun i => Fin.append_left a.1 a.2 i) (funext fun i => Fin.append_right a.1 a.2 i)

theorem append_toStd (c : Fin (h + h) → ZMod M) : Fin.append (toStd c).1 (toStd c).2 = c :=
  Fin.append_castAdd_natAdd

theorem toStd_injective : Function.Injective (toStd (h := h) (M := M)) := fun c c' e => by
  rw [← append_toStd c, ← append_toStd c', e]

theorem sum_val_smul [NeZero M] (c : Fin (h + h) → ZMod M) :
    ∑ i, (c i).val • toStd (Pi.single i (1 : ZMod M)) = toStd c := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp_rw [← map_nsmul, ← map_sum]
  congr 1
  conv_rhs => rw [← Finset.univ_sum_single c]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Pi.single_smul, nsmul_eq_mul, _root_.mul_one, ZMod.natCast_zmod_val]

end Labels

section Sections

variable {S : Scheme.{0}} {h M : ℕ} {A : Over S} [GrpObj A] {lv : IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit.Std h M → (𝟙_ (Over S) ⟶ A)}

theorem lv_zero (add : ∀ a b, lv (a + b) = lv a * lv b) : lv 0 = 1 := by
  have e := add 0 0
  rw [add_zero] at e
  exact left_eq_mul.1 e

theorem lv_nsmul (add : ∀ a b, lv (a + b) = lv a * lv b) (n : ℕ) (a) : lv (n • a) = lv a ^ n := by
  induction n with
  | zero => rw [zero_smul, pow_zero, lv_zero add]
  | succ n ih => rw [succ_nsmul, add, ih, pow_succ]

theorem lv_pow (add : ∀ a b, lv (a + b) = lv a * lv b) (a) : lv a ^ M = 1 := by
  rw [← lv_nsmul add, show M • a = 0 by ext i <;> simp, lv_zero add]

theorem linComb_lv (add : ∀ a b, lv (a + b) = lv a * lv b) {T : Over S} (g : T ⟶ 𝟙_ (Over S)) :
    ∀ {r : ℕ} (v : Fin r → IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit.Std h M) (n : Fin r → ℕ),
      Out.linComb (fun i => g ≫ lv (v i)) n = g ≫ lv (∑ i, n i • v i) := by
  intro r
  induction r with
  | zero =>
    intro v n
    simp [Out.linComb, lv_zero add]
  | succ r ih =>
    intro v n
    have e := ih (fun i => v i.succ) (fun i => n i.succ)
    simp only [Out.linComb] at e ⊢
    rw [List.ofFn_succ, List.prod_cons, e, Fin.sum_univ_succ, add, MonObj.comp_mul, lv_nsmul add,
      MonObj.comp_pow]

end Sections

end GlobalTheory.LevelDescent

namespace GlobalTheory.LevelDescent

open GlobalTheory.SiegelPull GlobalTheory.CharZeroPts

section Cond

variable {S : Scheme.{0}} {h M : ℕ} {A : Over S} [GrpObj A] {lv : IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit.Std h M → (𝟙_ (Over S) ⟶ A)}

theorem cond_iff [NeZero M] (add : ∀ a b, lv (a + b) = lv a * lv b) {k : Type} [Field k] (x : Sp k ⟶ S) :
    ((Function.Injective fun a => toUnit (Over.mk x) ≫ lv a) ∧
      ∀ g : Over.mk x ⟶ A, g ^ M = 1 ↔ ∃ a, toUnit (Over.mk x) ≫ lv a = g) ↔
    ∀ y : Over.mk x ⟶ A, y ^ M = 1 → ∃! c : Fin (h + h) → ZMod M,
      Out.linComb (fun i => toB x ≫ lv (toStd (Pi.single i 1))) (fun i => (c i).val) = y := by
  have E : ∀ c : Fin (h + h) → ZMod M,
      Out.linComb (fun i => toB x ≫ lv (toStd (Pi.single i 1))) (fun i => (c i).val) =
        toUnit (Over.mk x) ≫ lv (toStd c) := fun c =>
    (linComb_lv add (toB x) _ _).trans (by rw [sum_val_smul]; rfl)
  have tors : ∀ a, (toUnit (Over.mk x) ≫ lv a) ^ M = 1 := fun a => by
    rw [← MonObj.comp_pow, lv_pow add, MonObj.comp_one]
  constructor
  · rintro ⟨inj, sp⟩ y hy
    obtain ⟨a, rfl⟩ := (sp y).1 hy
    refine ⟨Fin.append a.1 a.2, by beta_reduce; rw [E, toStd_append], fun c hc => toStd_injective ?_⟩
    rw [toStd_append]
    exact inj ((E c).symm.trans hc)
  · intro H
    refine ⟨fun a b e => ?_, fun g => ⟨fun hg => ?_, ?_⟩⟩
    · obtain ⟨c, -, hc⟩ := H _ (tors a)
      have ea := hc (Fin.append a.1 a.2) (by beta_reduce; rw [E, toStd_append])
      have eb := hc (Fin.append b.1 b.2) (by beta_reduce; rw [E, toStd_append]; exact e.symm)
      rw [← toStd_append a, ← toStd_append b, ea, eb]
    · obtain ⟨c, hc, -⟩ := H g hg
      exact ⟨toStd c, (E c).symm.trans hc⟩
    · rintro ⟨a, rfl⟩
      exact tors a

end Cond

section Transfer

variable {h M : ℕ} {S S₁ : Scheme.{0}} {A : Over S} [GrpObj A] {A₁ : Over S₁} [GrpObj A₁] {f : S ⟶ S₁}
  {φ : A.left ⟶ A₁.left} {lv : IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit.Std h M → (𝟙_ (Over S) ⟶ A)}
  {lv₁ : IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit.Std h M → (𝟙_ (Over S₁) ⟶ A₁)}

theorem push_lv (hp : IsGrpPullback A A₁ f φ) (hl : ∀ a, (lv a).left ≫ φ = f ≫ (lv₁ a).left) (T : Over S) (a) :
    pushHom hp T (toUnit T ≫ lv a) = toUnit (Over.mk (T.hom ≫ f)) ≫ lv₁ a := by
  apply Over.OverMorphism.ext
  show ((toUnit T).left ≫ (lv a).left) ≫ φ = (toUnit (Over.mk (T.hom ≫ f))).left ≫ (lv₁ a).left
  rw [Category.assoc, hl, Over.toUnit_left, Over.toUnit_left, ← Category.assoc]
  rfl

theorem cond_push (hp : IsGrpPullback A A₁ f φ) (hl : ∀ a, (lv a).left ≫ φ = f ≫ (lv₁ a).left) {k : Type} [Field k]
    (x : Sp k ⟶ S)
    (H : (Function.Injective fun a => toUnit (Over.mk x) ≫ lv a) ∧
      ∀ g : Over.mk x ⟶ A, g ^ M = 1 ↔ ∃ a, toUnit (Over.mk x) ≫ lv a = g) :
    (Function.Injective fun a => toUnit (Over.mk (x ≫ f)) ≫ lv₁ a) ∧
      ∀ g : Over.mk (x ≫ f) ⟶ A₁, g ^ M = 1 ↔ ∃ a, toUnit (Over.mk (x ≫ f)) ≫ lv₁ a = g := by
  have P := push_lv hp hl (Over.mk x)
  have inj := push_injective hp (Over.mk x)
  refine ⟨fun a b e => H.1 (inj ?_), fun g => ?_⟩
  · rw [P, P]
    exact e
  · obtain ⟨g', rfl⟩ := push_surjective hp (Over.mk x) g
    rw [← map_pow, ← map_one (pushHom hp (Over.mk x)), inj.eq_iff, H.2 g']
    refine exists_congr fun a => ?_
    rw [← inj.eq_iff, P]
    rfl

end Transfer

end GlobalTheory.LevelDescent

namespace GlobalTheory.LevelDescent

open GlobalTheory.SiegelPull GlobalTheory.CharZeroPts

theorem isLevel_of_subring : ∀ (h M : ℕ) (R : Type) [CommRing R] (R₁ : Subring R) (A : Over (Sp R)) [GrpObj A] (A₁ : Over (Sp R₁)) [GrpObj A₁] (φ : A.left ⟶ A₁.left) (lv : Std h M → (𝟙_ (Over (Sp R)) ⟶ A)) (lv₁ : Std h M → (𝟙_ (Over (Sp R₁)) ⟶ A₁)), 0 < M → IsUnit (M : R₁) → IsAbelianScheme A₁ → IsGrpPullback A A₁ (spMap R₁.subtype) φ → (∀ a, (lv a).left ≫ φ = spMap R₁.subtype ≫ (lv₁ a).left) → (∀ a b, lv₁ (a + b) = lv₁ a * lv₁ b) → IsLevel A lv → IsLevel A₁ lv₁ := by
  intro h M R _ R₁ A _ A₁ _ φ lv lv₁ hM hu hA hp hl hadd hlev
  haveI : NeZero M := ⟨hM.ne'⟩
  have hu' : IsUnit ((M : ℕ) : Γ(Sp R₁, ⊤)) := by
    simpa using hu.map (Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom
  refine ⟨hadd, fun k _ _ x => (cond_iff hadd x).2 fun y hy => ?_⟩
  refine torsion_basis_of_generization A₁ M (h + h) (fun i => lv₁ (toStd (Pi.single i 1))) hA hM hu'
    (fun i => lv_pow hadd _) (fun p => ?_) k x y hy
  obtain ⟨K, _, _, z, hz⟩ := exists_geomPt_specializes R R₁ p
  exact ⟨K, inferInstance, inferInstance, z ≫ spMap R₁.subtype, hz,
    (cond_iff hadd _).1 (cond_push hp hl z (hlev.2 K z))⟩

end GlobalTheory.LevelDescent
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSiegelDescendsFiniteTypeSubring
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings

namespace GlobalTheory.SiegFG

theorem siegPre_descends_fg : ∀ (g n : ℕ), 3 ≤ n → Odd n → ∀ (R : Type) [CommRing R] (β : cycAway n →+* R) (c : SiegPre g n (zetaAway n) (spMap β)), c.Principal → ∃ (R₀ : Subring R) (β₀ : cycAway n →+* R₀) (c₀ : SiegPre g n (zetaAway n) (spMap β₀)), Algebra.FiniteType ℤ R₀ ∧ R₀.subtype.comp β₀ = β ∧ c₀.Principal ∧ SiegPB c c₀ (spMap R₀.subtype) := by
  intro g n hn hodd R _ β c hc
  have hn0 : n ≠ 0 := by omega
  obtain ⟨R₀, β₀, A₀, _, P₀, lv₀, hft, hβ, hsym, hadd, hamp, hpb⟩ := GlobalTheory.SiegFGData.data g n hn hodd R β c hc
  have : IsNoetherianRing R₀ := Algebra.FiniteType.isNoetherianRing ℤ R₀
  have hpb' := hpb
  obtain ⟨φ, φ₂, hφ, s₁, s₂, iso, hl⟩ := hpb
  have hpr : IsPrincipal A₀ P₀ :=
    GlobalTheory.PrincSubring.isPrincipal_of_subring g R R₀ c.A c.P A₀ P₀ φ φ₂ hsym hamp hφ ⟨s₁, s₂⟩ iso ((principal_iff c).1 hc)
  let u : (cycAway n)ˣ := Units.ofPowEqOne (zetaAway n) n (zetaAway_pow_self hn0) hn0
  have hζ : u ^ n = 1 := Units.ext (by simp [u])
  have hunit : IsUnit (n : R₀) := by simpa using (isUnit_natCast hn0).map β₀
  have hlevR : IsLevel c.A (lvOf c) := isLevel_lvOf (ζ := u) c
  have hlev₀ : IsLevel A₀ lv₀ :=
    GlobalTheory.LevelDescent.isLevel_of_subring g n R R₀ c.A A₀ φ (lvOf c) lv₀ (by omega) hunit hsym.1 hφ hl hadd hlevR
  have hsympR : IsSymplectic u (spMap β) c.A c.P (lvOf c) :=
    isSymplectic_of_translFixed (ζ := u) hn0 hζ (isUnit_natCast hn0) c (translFixed_of_ample c hc.1)
  have hsymp₀ : IsSymplectic u (spMap β₀) A₀ P₀ lv₀ :=
    GlobalTheory.SympDescent.isSymplectic_of_subring g n (cycAway n) R u R₀ (spMap β₀) c.A c.P (lvOf c) A₀ P₀ lv₀ (by omega) hζ hunit hsym hpr hlev₀
      c.isLB hpb' (by rw [← GlobalTheory.SiegelTypings.spMap_comp, hβ]; exact hsympR)
  let c₀ : SiegPre g n (zetaAway n) (spMap β₀) := ofTriple (ζ := u) hn0 hζ A₀ P₀ lv₀ hsym hlev₀ hsymp₀
  refine ⟨R₀, β₀, c₀, hft, hβ, ?_, (siegPB_iff c c₀ _).2 ?_⟩
  · apply (principal_iff c₀).2
    change IsPrincipal A₀ P₀
    exact hpr
  · change IsPullbackTriple c.A c.P (lvOf c) A₀ P₀ (lvOf (ofTriple (ζ := u) hn0 hζ A₀ P₀ lv₀ hsym hlev₀ hsymp₀)) (spMap R₀.subtype)
    rw [lvOf_ofTriple]
    exact hpb'

end GlobalTheory.SiegFG
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSiegelDescendsFiniteTypeSubringStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalSiegel_descends_finiteType_subring : ∀ (g n : ℕ), 3 ≤ n → Odd n → ∀ (R : Type) [CommRing R] (β : cycAway n →+* R) (c : SiegPre g n (zetaAway n) (spMap β)), c.Principal → ∃ (R₀ : Subring R) (β₀ : cycAway n →+* R₀) (c₀ : SiegPre g n (zetaAway n) (spMap β₀)), Algebra.FiniteType ℤ R₀ ∧ R₀.subtype.comp β₀ = β ∧ c₀.Principal ∧ SiegPB c c₀ (spMap R₀.subtype) := by
  first | (exact @GlobalTheory.SiegFG.siegPre_descends_fg) | (exact GlobalTheory.SiegFG.siegPre_descends_fg) | (intros; apply GlobalTheory.SiegFG.siegPre_descends_fg  <;> assumption)
end
