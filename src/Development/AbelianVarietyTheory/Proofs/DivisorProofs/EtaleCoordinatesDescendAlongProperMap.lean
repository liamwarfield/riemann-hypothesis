module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlatChartEtaleOfQuasiFiniteAt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsolatedInFibreCoordinateMapAffineSpace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperSurjectiveAffineChartBijectiveSections
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperSurjectiveAffineChartBijectiveSections
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.FibOpen

theorem universallyOpen_of {X Y : Scheme.{0}} (f : X ⟶ Y) [UniversallyClosed f] [UniversallyInjective f]
    [Surjective f] : UniversallyOpen f := by
  constructor
  intro X' Y' i₁ i₂ f' hf
  have h1 : UniversallyClosed f' := MorphismProperty.of_isPullback hf.flip inferInstance
  have h2 : UniversallyInjective f' := MorphismProperty.of_isPullback hf.flip inferInstance
  have h3 : Surjective f' := MorphismProperty.of_isPullback hf.flip inferInstance
  have hb : Function.Bijective f' := ⟨f'.injective, f'.surjective⟩
  show IsOpenMap f'
  intro U hU
  have e : f' '' U = (f' '' Uᶜ)ᶜ := by rw [Set.image_compl_eq hb, compl_compl]
  rw [e]
  exact (f'.isClosedMap _ hU.isClosed_compl).isOpen_compl

theorem fiber_hom_ext {X Y T : Scheme.{0}} (f : X ⟶ Y) (y : Y) {u v : T ⟶ f.fiber y}
    (h₁ : u ≫ f.fiberι y = v ≫ f.fiberι y)
    (h₂ : u ≫ f.fiberToSpecResidueField y = v ≫ f.fiberToSpecResidueField y) : u = v :=
  pullback.hom_ext h₁ h₂

@[reassoc]
theorem fiber_condition {X Y : Scheme.{0}} (f : X ⟶ Y) (y : Y) :
    f.fiberι y ≫ f = f.fiberToSpecResidueField y ≫ Y.fromSpecResidueField y :=
  pullback.condition

def fiberLift {X Y T : Scheme.{0}} (f : X ⟶ Y) (y : Y) (u : T ⟶ X) (v : T ⟶ Spec (Y.residueField y))
    (h : u ≫ f = v ≫ Y.fromSpecResidueField y) : T ⟶ f.fiber y :=
  pullback.lift u v h

@[reassoc (attr := simp)]
theorem fiberLift_ι {X Y T : Scheme.{0}} (f : X ⟶ Y) (y : Y) (u : T ⟶ X) (v : T ⟶ Spec (Y.residueField y))
    (h : u ≫ f = v ≫ Y.fromSpecResidueField y) : fiberLift f y u v h ≫ f.fiberι y = u :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem fiberLift_snd {X Y T : Scheme.{0}} (f : X ⟶ Y) (y : Y) (u : T ⟶ X) (v : T ⟶ Spec (Y.residueField y))
    (h : u ≫ f = v ≫ Y.fromSpecResidueField y) : fiberLift f y u v h ≫ f.fiberToSpecResidueField y = v :=
  pullback.lift_snd _ _ _

theorem range_comp_fromSpecResidueField {X T : Scheme.{0}} [Nonempty T] (x : X) (t : T ⟶ Spec (X.residueField x)) :
    Set.range (t ≫ X.fromSpecResidueField x) = {x} := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
    rfl
  · rintro rfl
    obtain ⟨z⟩ := ‹Nonempty T›
    exact ⟨z, by rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]⟩

theorem comp_fromSpecResidueField_apply {Y T : Scheme.{0}} (y : Y) (t : T ⟶ Spec (Y.residueField y)) (z : T) :
    (t ≫ Y.fromSpecResidueField y) z = y := by
  rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]

end GlobalTheory.FibOpen
end


set_option backward.isDefEq.respectTransparency.types false in
theorem GlobalTheory.FibOpen.fibre_universallyOpen : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S X : Scheme.{0}) (π : S ⟶ Sp R) (U : Over (Sp R)) (a : X ⟶ U.left) (b : X ⟶ S) (g : ℕ) (τ : U.left ⟶ 𝔸(Fin g; Sp R)) (c : X ⟶ pullback (𝔸(Fin g; Sp R) ↘ Sp R) π), IsProper π → Surjective π → Function.Bijective π.appTop.hom → LocallyOfFiniteType U.hom → IsSeparated U.hom → IsProper a → (∀ V : U.left.Opens, Function.Bijective (a.app V).hom) → τ ≫ (𝔸(Fin g; Sp R) ↘ Sp R) = U.hom → c ≫ pullback.fst _ _ = a ≫ τ → c ≫ pullback.snd _ _ = b → Etale c → ∀ x : U.left, IsClosed ({x} : Set U.left) → U.hom x = closedPoint R → (∀ (Ω : Type) [Field Ω] (p p' : Sp Ω ⟶ X), Set.range (p ≫ a) = {x} → p ≫ a = p' ≫ a → p ≫ b = p' ≫ b → p = p') → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ξ : Sp Ω ⟶ U.left) (s : Sp Ω ⟶ S), Set.range ξ = {x} → ξ ≫ U.hom = s ≫ π → ∃ p : Sp Ω ⟶ X, p ≫ a = ξ ∧ p ≫ b = s) → ∀ φ : a.fiber x ⟶ (pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π).fiber (τ x), φ ≫ (pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π).fiberι (τ x) = a.fiberι x ≫ c → φ ≫ (pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π).fiberToSpecResidueField (τ x) = a.fiberToSpecResidueField x ≫ Spec.map (τ.residueFieldMap x) → UniversallyOpen φ := by
  intro R _ _ _ _ S X π U a b g τ c hπp hπs hΓ hlft hsep hap haO hτ hc₁ hc₂ het x hxc hxcl hinj hsurj φ hφ₁ hφ₂
  let ψ : a.fiber x ⟶ pullback ((pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π).fiberToSpecResidueField (τ x)) (Spec.map (τ.residueFieldMap x)) :=
    pullback.lift φ (a.fiberToSpecResidueField x) hφ₂
  have hψ₁ : ψ ≫ pullback.fst _ _ = φ := pullback.lift_fst _ _ _
  have hψ₂ : ψ ≫ pullback.snd _ _ = a.fiberToSpecResidueField x := pullback.lift_snd _ _ _
  have hSx : pullback.fst ((pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π).fiberToSpecResidueField (τ x)) (Spec.map (τ.residueFieldMap x)) ≫ (pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π).fiberToSpecResidueField (τ x) =
      pullback.snd _ _ ≫ (Spec.map (τ.residueFieldMap x)) := pullback.condition
  have hres : U.left.fromSpecResidueField x ≫ τ = (Spec.map (τ.residueFieldMap x)) ≫ 𝔸(Fin g; Sp R).fromSpecResidueField (τ x) :=
    (τ.SpecMap_residueFieldMap_fromSpecResidueField x).symm
  have hFc : (pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π) ≫ (𝔸(Fin g; Sp R) ↘ Sp R) = pullback.snd (𝔸(Fin g; Sp R) ↘ Sp R) π ≫ π := pullback.condition
  have hb : a.fiberι x ≫ b = φ ≫ (pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π).fiberι (τ x) ≫ pullback.snd _ _ := by
    rw [← hc₂, ← Category.assoc, ← hφ₁, Category.assoc]
  suffices h : UniversallyOpen ψ by
    rw [← hψ₁]; infer_instance
  haveI : IsProper a := hap
  haveI : IsProper π := hπp
  haveI : IsProper (a.fiberToSpecResidueField x) :=
    MorphismProperty.pullback_snd (P := @IsProper) _ _ hap
  haveI : IsSeparated (pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π) := MorphismProperty.pullback_fst (P := @IsSeparated) _ _ inferInstance
  haveI : IsSeparated ((pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π).fiberToSpecResidueField (τ x)) :=
    MorphismProperty.pullback_snd (P := @IsSeparated) _ _ inferInstance
  haveI : IsProper (ψ ≫ pullback.snd _ _) := by rw [hψ₂]; infer_instance
  haveI : IsProper ψ := IsProper.of_comp ψ (pullback.snd ((pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π).fiberToSpecResidueField (τ x)) (Spec.map (τ.residueFieldMap x)))
  haveI : UniversallyInjective ψ := by
    refine ((tfae_universallyInjective ψ).out 1 2).mpr ?_
    intro K _ q q' hq
    simp only at hq
    have e₂ : q ≫ a.fiberToSpecResidueField x = q' ≫ a.fiberToSpecResidueField x := by
      rw [← hψ₂, ← Category.assoc, hq, Category.assoc]
    have e₃ : q ≫ φ = q' ≫ φ := by rw [← hψ₁, ← Category.assoc, hq, Category.assoc]
    have ea : ∀ q : Spec (.of K) ⟶ a.fiber x, (q ≫ a.fiberι x) ≫ a =
        (q ≫ a.fiberToSpecResidueField x) ≫ U.left.fromSpecResidueField x := fun q => by
      rw [Category.assoc, Category.assoc, GlobalTheory.FibOpen.fiber_condition]
    have key := hinj K (q ≫ a.fiberι x) (q' ≫ a.fiberι x)
      (by rw [ea]; exact GlobalTheory.FibOpen.range_comp_fromSpecResidueField x _) (by rw [ea, ea, e₂])
      (by rw [Category.assoc, Category.assoc, hb, ← Category.assoc q, e₃, Category.assoc])
    exact GlobalTheory.FibOpen.fiber_hom_ext a x key e₂
  haveI : Surjective ψ := by
    constructor
    intro y
    let Ω := AlgebraicClosure ((pullback ((pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π).fiberToSpecResidueField (τ x)) (Spec.map (τ.residueFieldMap x))).residueField y)
    let t : Sp Ω ⟶ pullback ((pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π).fiberToSpecResidueField (τ x)) (Spec.map (τ.residueFieldMap x)) :=
      Spec.map (CommRingCat.ofHom (algebraMap ((pullback ((pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π).fiberToSpecResidueField (τ x)) (Spec.map (τ.residueFieldMap x))).residueField y) Ω)) ≫
        (pullback ((pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π).fiberToSpecResidueField (τ x)) (Spec.map (τ.residueFieldMap x))).fromSpecResidueField y
    let ξ := (t ≫ pullback.snd _ _) ≫ U.left.fromSpecResidueField x
    let s := t ≫ pullback.fst _ _ ≫ (pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π).fiberι (τ x) ≫ pullback.snd (𝔸(Fin g; Sp R) ↘ Sp R) π
    have hξ : ξ ≫ U.hom = s ≫ π := by
      simp only [ξ, s, Category.assoc]
      rw [← hτ, ← hFc, reassoc_of% hres, GlobalTheory.FibOpen.fiber_condition_assoc, reassoc_of% hSx]
    obtain ⟨p, hp₁, hp₂⟩ := hsurj Ω ξ s (GlobalTheory.FibOpen.range_comp_fromSpecResidueField x _) hξ
    let q : Sp Ω ⟶ a.fiber x := GlobalTheory.FibOpen.fiberLift a x p (t ≫ pullback.snd _ _) (by rw [hp₁])
    have hqt : q ≫ ψ = t := by
      apply pullback.hom_ext
      · rw [Category.assoc, hψ₁]
        apply GlobalTheory.FibOpen.fiber_hom_ext
        · rw [Category.assoc, hφ₁, GlobalTheory.FibOpen.fiberLift_ι_assoc]
          apply pullback.hom_ext
          · simp only [Category.assoc]
            rw [hc₁, reassoc_of% hp₁]
            simp only [ξ, Category.assoc]
            rw [hres, GlobalTheory.FibOpen.fiber_condition, reassoc_of% hSx]
          · simp only [Category.assoc]
            rw [hc₂, hp₂]
        · rw [Category.assoc, hφ₂, GlobalTheory.FibOpen.fiberLift_snd_assoc]
          simp only [Category.assoc]
          rw [hSx]
      · rw [Category.assoc, hψ₂, GlobalTheory.FibOpen.fiberLift_snd]
    obtain ⟨z⟩ : Nonempty (Sp Ω) := inferInstance
    refine ⟨q z, ?_⟩
    rw [← Scheme.Hom.comp_apply, hqt]
    exact GlobalTheory.FibOpen.comp_fromSpecResidueField_apply y _ z
  exact GlobalTheory.FibOpen.universallyOpen_of ψ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperSurjectiveAffineChartBijectiveSectionsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.proper_surjective_affine_chart_bijective_sections : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S X : Scheme.{0}) (π : S ⟶ Sp R) (U : Over (Sp R)) (a : X ⟶ U.left) (b : X ⟶ S) (g : ℕ) (τ : U.left ⟶ 𝔸(Fin g; Sp R)) (c : X ⟶ pullback (𝔸(Fin g; Sp R) ↘ Sp R) π), IsProper π → Surjective π → Function.Bijective π.appTop.hom → LocallyOfFiniteType U.hom → IsSeparated U.hom → IsProper a → (∀ V : U.left.Opens, Function.Bijective (a.app V).hom) → τ ≫ (𝔸(Fin g; Sp R) ↘ Sp R) = U.hom → c ≫ pullback.fst _ _ = a ≫ τ → c ≫ pullback.snd _ _ = b → Etale c → ∀ x : U.left, IsClosed ({x} : Set U.left) → U.hom x = closedPoint R → (∀ (Ω : Type) [Field Ω] (p p' : Sp Ω ⟶ X), Set.range (p ≫ a) = {x} → p ≫ a = p' ≫ a → p ≫ b = p' ≫ b → p = p') → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ξ : Sp Ω ⟶ U.left) (s : Sp Ω ⟶ S), Set.range ξ = {x} → ξ ≫ U.hom = s ≫ π → ∃ p : Sp Ω ⟶ X, p ≫ a = ξ ∧ p ≫ b = s) → ∀ φ : a.fiber x ⟶ (pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π).fiber (τ x), φ ≫ (pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π).fiberι (τ x) = a.fiberι x ≫ c → φ ≫ (pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π).fiberToSpecResidueField (τ x) = a.fiberToSpecResidueField x ≫ Spec.map (τ.residueFieldMap x) → UniversallyOpen φ := by
  first | exact @GlobalTheory.FibOpen.fibre_universallyOpen | exact GlobalTheory.FibOpen.fibre_universallyOpen | (intros; apply GlobalTheory.FibOpen.fibre_universallyOpen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenRangeEqInterPreimageEtaleUnivOpen
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenRangeEqInterPreimageEtaleUnivOpen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem isOpen_range_of_etale_of_universallyOpen_comp {Y Z T : Scheme.{0}} (i' : Z ⟶ Y) (h : Y ⟶ T)
    [Etale h] (hu : UniversallyOpen (i' ≫ h)) : IsOpen (Set.range i') := by
  have s_open : IsOpenImmersion (pullback.lift (𝟙 Z) i' (by simp) : Z ⟶ pullback (i' ≫ h) h) :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion)
      (pullback_lift_diagonal_isPullback i' h) inferInstance
  have e : Set.range i' = (pullback.snd (i' ≫ h) h) '' Set.range (pullback.lift (𝟙 Z) i' (by simp) : Z ⟶ pullback (i' ≫ h) h) := by
    rw [← Set.range_comp]
    congr 1
    ext z
    rw [Function.comp_apply, ← Scheme.Hom.comp_apply, pullback.lift_snd]
  rw [e]
  exact (pullback.snd (i' ≫ h) h).isOpenMap _ (pullback.lift (𝟙 Z) i' _).isOpenEmbedding.isOpen_range

theorem exists_opens_range_eq_of_etale {X B T Z : Scheme.{0}} (c : X ⟶ B) (j : T ⟶ B) (i : Z ⟶ X) (φ : Z ⟶ T)
    (hc : Etale c) (hj : IsPreimmersion j) (hφ : UniversallyOpen φ) (w : i ≫ c = φ ≫ j) :
    ∃ W : X.Opens, Set.range i = (W : Set X) ∩ c ⁻¹' Set.range j := by
  let i' : Z ⟶ pullback c j := pullback.lift i φ w
  have hi' : i' ≫ pullback.snd c j = φ := pullback.lift_snd _ _ _
  have ho : IsOpen (Set.range i') :=
    isOpen_range_of_etale_of_universallyOpen_comp i' (pullback.snd c j) (by rw [hi']; exact hφ)
  have hemb := IsPreimmersion.isEmbedding (pullback.fst c j)
  obtain ⟨U, hU, hpre⟩ := hemb.isInducing.isOpen_iff.1 ho
  refine ⟨⟨U, hU⟩, ?_⟩
  have hr : Set.range i = (pullback.fst c j) '' Set.range i' := by
    rw [← Set.range_comp]
    congr 1
    ext z
    rw [Function.comp_apply, ← Scheme.Hom.comp_apply, pullback.lift_fst]
  rw [hr, ← hpre, Set.image_preimage_eq_inter_range, Scheme.Pullback.range_fst]
  rfl

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenRangeEqInterPreimageEtaleUnivOpenStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_range_eq_inter_preimage_etale_univOpen : ∀ (X B T Z : Scheme.{0}) (c : X ⟶ B) (j : T ⟶ B) (i : Z ⟶ X) (φ : Z ⟶ T), Etale c → IsPreimmersion j → UniversallyOpen φ → i ≫ c = φ ≫ j → ∃ W : X.Opens, Set.range i = (W : Set X) ∩ c ⁻¹' Set.range j := by
  first | exact @GlobalTheory.Mum.exists_opens_range_eq_of_etale | exact GlobalTheory.Mum.exists_opens_range_eq_of_etale | (intros; apply GlobalTheory.Mum.exists_opens_range_eq_of_etale <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsolatedInFibreCoordinateMapAffineSpace
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem surjective_of_isProper_of_app_injective : ∀ (X Y : Scheme.{0}) (a : X ⟶ Y), IsProper a → (∀ V : Y.Opens, Function.Injective (a.app V).hom) → Function.Surjective a := by
  intro X Y a ha hinj
  haveI := ha
  by_contra hne
  simp only [Function.Surjective, not_forall] at hne
  obtain ⟨y, hy⟩ := hne
  have hcl : IsClosed (Set.range a) := by
    simpa using a.isClosedMap _ isClosed_univ
  let V : Y.Opens := ⟨(Set.range a)ᶜ, hcl.isOpen_compl⟩
  haveI : Nonempty V := ⟨⟨y, fun ⟨p, hp⟩ => hy ⟨p, hp⟩⟩⟩
  have hV : a ⁻¹ᵁ V = ⊥ := by
    ext p
    simp [V]
  haveI : Subsingleton Γ(X, a ⁻¹ᵁ V) :=
    CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty hV)
  have : Subsingleton Γ(Y, V) := (hinj V).subsingleton
  exact not_subsingleton Γ(Y, V) this

theorem isolated_in_coordinate_fibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S X : Scheme.{0}) (π : S ⟶ Sp R) (U : Over (Sp R)) (a : X ⟶ U.left) (b : X ⟶ S) (g : ℕ) (τ : U.left ⟶ 𝔸(Fin g; Sp R)) (c : X ⟶ pullback (𝔸(Fin g; Sp R) ↘ Sp R) π), IsProper π → Surjective π → Function.Bijective π.appTop.hom → LocallyOfFiniteType U.hom → IsSeparated U.hom → IsProper a → (∀ V : U.left.Opens, Function.Bijective (a.app V).hom) → τ ≫ (𝔸(Fin g; Sp R) ↘ Sp R) = U.hom → c ≫ pullback.fst _ _ = a ≫ τ → c ≫ pullback.snd _ _ = b → Etale c → ∀ x : U.left, IsClosed ({x} : Set U.left) → U.hom x = closedPoint R → (∀ (Ω : Type) [Field Ω] (p p' : Sp Ω ⟶ X), Set.range (p ≫ a) = {x} → p ≫ a = p' ≫ a → p ≫ b = p' ≫ b → p = p') → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ξ : Sp Ω ⟶ U.left) (s : Sp Ω ⟶ S), Set.range ξ = {x} → ξ ≫ U.hom = s ≫ π → ∃ p : Sp Ω ⟶ X, p ≫ a = ξ ∧ p ≫ b = s) → ∃ O : U.left.Opens, x ∈ O ∧ ∀ u ∈ O, τ u = τ x → u = x := by
  intro R _ _ _ hR S X π U a b g τ c hπp hπs hπΓ hUf hUs hap haV hτ hc1 hc2 hc x hxc hxR hinj hsurj
  set F := pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π with hF
  have hw : (a.fiberι x ≫ c) ≫ F = (a.fiberToSpecResidueField x ≫ Spec.map (τ.residueFieldMap x)) ≫
      (𝔸(Fin g; Sp R)).fromSpecResidueField (τ x) := by
    rw [Category.assoc, hF, hc1, ← Category.assoc, Scheme.Hom.fiber_fac, Category.assoc, Category.assoc,
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
  let φ : a.fiber x ⟶ F.fiber (τ x) := pullback.lift _ _ hw
  have hφ1 : φ ≫ F.fiberι (τ x) = a.fiberι x ≫ c := pullback.lift_fst _ _ _
  have hφ2 : φ ≫ F.fiberToSpecResidueField (τ x) = a.fiberToSpecResidueField x ≫ Spec.map (τ.residueFieldMap x) :=
    pullback.lift_snd _ _ _
  have hUO := GlobalTheory.T.proper_surjective_affine_chart_bijective_sections R hR S X π U a b g τ c hπp hπs hπΓ hUf hUs hap haV hτ hc1 hc2 hc x hxc hxR hinj hsurj φ hφ1 hφ2
  haveI : IsPreimmersion (F.fiberι (τ x)) := inferInstance
  obtain ⟨W, hW⟩ := GlobalTheory.T.exists_open_range_eq_inter_preimage_etale_univOpen X _ _ _ c (F.fiberι (τ x)) (a.fiberι x) φ hc inferInstance hUO hφ1.symm
  rw [Scheme.Hom.range_fiberι, Scheme.Hom.range_fiberι] at hW
  have hs := surjective_of_isProper_of_app_injective X U.left a hap (fun V => (haV V).1)
  haveI := hap
  refine ⟨⟨(a '' (W : Set X)ᶜ)ᶜ, (a.isClosedMap _ W.isOpen.isClosed_compl).isOpen_compl⟩, ?_, ?_⟩
  · rintro ⟨p, hp, hpx⟩
    have : p ∈ a ⁻¹' {x} := hpx
    rw [hW] at this
    exact hp this.1
  · intro u hu hτu
    obtain ⟨p, rfl⟩ := hs u
    by_cases hp : p ∈ W
    · have : p ∈ (W : Set X) ∩ c ⁻¹' (F ⁻¹' {τ x}) := by
        refine ⟨hp, ?_⟩
        show F (c p) = τ x
        rw [← Scheme.Hom.comp_apply, hF, hc1, Scheme.Hom.comp_apply, hτu]
      rw [← hW] at this
      exact this
    · exact absurd ⟨p, hp, rfl⟩ hu

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsolatedInFibreCoordinateMapAffineSpaceStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isolated_in_fibre_coordinateMap_affineSpace : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S X : Scheme.{0}) (π : S ⟶ Sp R) (U : Over (Sp R)) (a : X ⟶ U.left) (b : X ⟶ S) (g : ℕ) (τ : U.left ⟶ 𝔸(Fin g; Sp R)) (c : X ⟶ pullback (𝔸(Fin g; Sp R) ↘ Sp R) π), IsProper π → Surjective π → Function.Bijective π.appTop.hom → LocallyOfFiniteType U.hom → IsSeparated U.hom → IsProper a → (∀ V : U.left.Opens, Function.Bijective (a.app V).hom) → τ ≫ (𝔸(Fin g; Sp R) ↘ Sp R) = U.hom → c ≫ pullback.fst _ _ = a ≫ τ → c ≫ pullback.snd _ _ = b → Etale c → ∀ x : U.left, IsClosed ({x} : Set U.left) → U.hom x = closedPoint R → (∀ (Ω : Type) [Field Ω] (p p' : Sp Ω ⟶ X), Set.range (p ≫ a) = {x} → p ≫ a = p' ≫ a → p ≫ b = p' ≫ b → p = p') → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ξ : Sp Ω ⟶ U.left) (s : Sp Ω ⟶ S), Set.range ξ = {x} → ξ ≫ U.hom = s ≫ π → ∃ p : Sp Ω ⟶ X, p ≫ a = ξ ∧ p ≫ b = s) → ∃ O : U.left.Opens, x ∈ O ∧ ∀ u ∈ O, τ u = τ x → u = x := by
  first | exact @GlobalTheory.Mum.isolated_in_coordinate_fibre | exact GlobalTheory.Mum.isolated_in_coordinate_fibre | (intros; apply GlobalTheory.Mum.isolated_in_coordinate_fibre <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleNhdsAffineSpaceMapOfFlatBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleNhdsAffineSpaceMapOfFlatBaseChange
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.EtaleAtDescent

open TensorProduct

theorem notMem_support_of_flat {B D M N : Type} [CommRing B] [CommRing D] [Algebra B D] [Module.Flat B D]
    [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N] [Module D N] [IsScalarTower B D N]
    (φ : M →ₗ[B] N) (hφ : Function.Injective (φ.liftBaseChange D)) (Q : PrimeSpectrum D)
    (hQ : Q ∉ Module.support D N) : PrimeSpectrum.comap (algebraMap B D) Q ∉ Module.support B M := by
  rw [Module.notMem_support_iff'] at hQ ⊢
  intro x
  by_contra hx
  push Not at hx
  obtain ⟨f, hf, hfx⟩ := hQ (φ x)
  have h0 : f ⊗ₜ[B] x = 0 := hφ (by simpa using hfx)
  have hex := Module.Flat.lTensor_exact D (LinearMap.exact_subtype_ker_map (LinearMap.toSpanSingleton B M x))
  obtain ⟨z, hz⟩ := (hex (f ⊗ₜ[B] 1)).1 (by simpa using h0)
  have key : ∀ z : D ⊗[B] LinearMap.ker (LinearMap.toSpanSingleton B M x),
      TensorProduct.rid B D (LinearMap.lTensor D (LinearMap.ker (LinearMap.toSpanSingleton B M x)).subtype z) ∈
        Q.asIdeal := by
    intro z
    induction z with
    | add a b ha hb => rw [map_add (f := _), map_add (f := _)]; exact Q.asIdeal.add_mem ha hb
    | tmul d r =>
      have hr : algebraMap B D r.1 ∈ Q.asIdeal := by
        by_contra h
        exact hx r.1 h (LinearMap.mem_ker.1 r.2)
      simpa [Algebra.smul_def] using Q.asIdeal.mul_mem_right d hr
  have := key z
  rw [hz] at this
  exact hf (by simpa using this)


attribute [local instance] Algebra.TensorProduct.rightAlgebra in
theorem mem_etaleLocus_of_flat {A B C : Type} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    [Module.Flat A C] (Q : PrimeSpectrum (C ⊗[A] B)) (hQ : Q ∈ Algebra.etaleLocus C (C ⊗[A] B)) :
    PrimeSpectrum.comap (algebraMap B (C ⊗[A] B)) Q ∈ Algebra.etaleLocus A B := by
  rw [Algebra.etaleLocus_eq_compl_support] at hQ ⊢
  haveI : Module.Flat B (C ⊗[A] B) :=
    Module.Flat.of_linearEquiv (Algebra.IsPushout.equiv A B C (C ⊗[A] B)).toLinearEquiv.symm
  refine ⟨notMem_support_of_flat (KaehlerDifferential.map A C B (C ⊗[A] B)) ?_ Q hQ.1,
    notMem_support_of_flat (Algebra.H1Cotangent.map A C B (C ⊗[A] B)) ?_ Q hQ.2⟩
  · have hc : (KaehlerDifferential.tensorKaehlerEquivBase A C B (C ⊗[A] B) : _ → _) =
        (KaehlerDifferential.map A C B (C ⊗[A] B)).liftBaseChange (C ⊗[A] B) ∘
          (Algebra.IsPushout.cancelBaseChange A C B (C ⊗[A] B) Ω[B⁄A]).symm := by
      funext z
      induction z with
      | add x y hx hy => simp only [Function.comp_apply, map_add (f := _)] at hx hy ⊢; rw [hx, hy]
      | tmul s m =>
        rw [KaehlerDifferential.tensorKaehlerEquivBase_tmul, Function.comp_apply,
          Algebra.IsPushout.cancelBaseChange_symm_tmul, LinearMap.liftBaseChange_tmul, algebraMap_smul]
    have hi := (KaehlerDifferential.tensorKaehlerEquivBase A C B (C ⊗[A] B)).injective
    rw [hc] at hi
    exact hi.of_comp_right (LinearEquiv.surjective _)
  · have hc : (Algebra.tensorH1CotangentOfFlat A B C : _ → _) =
        (Algebra.H1Cotangent.map A C B (C ⊗[A] B)).liftBaseChange (C ⊗[A] B) ∘
          (Algebra.IsPushout.cancelBaseChange A C B (C ⊗[A] B) (Algebra.H1Cotangent A B)).symm := by
      funext z
      induction z with
      | add x y hx hy => simp only [Function.comp_apply, map_add (f := _)] at hx hy ⊢; rw [hx, hy]
      | tmul s m =>
        rw [Algebra.tensorH1CotangentOfFlat_tmul, Function.comp_apply, Algebra.IsPushout.cancelBaseChange_symm_tmul,
          LinearMap.liftBaseChange_tmul, algebraMap_smul]
    have hi := (Algebra.tensorH1CotangentOfFlat A B C).injective
    rw [hc] at hi
    exact hi.of_comp_right (LinearEquiv.surjective _)


attribute [local instance] Algebra.TensorProduct.rightAlgebra in
theorem exists_etale_spec {A B C : Type} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    [Module.Flat A C] [Algebra.FinitePresentation A B] (W : (Spec (.of (C ⊗[A] B))).Opens)
    (p : Spec (.of (C ⊗[A] B))) (hp : p ∈ W)
    (hW : Etale (W.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap C (C ⊗[A] B))))) :
    ∃ V : (Spec (.of B)).Opens, Spec.map (CommRingCat.ofHom (algebraMap B (C ⊗[A] B))) p ∈ V ∧
      Etale (V.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
  obtain ⟨_, ⟨_, ⟨f, rfl⟩, rfl⟩, hpf, hf⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hp W.isOpen
  let j := Spec.map (CommRingCat.ofHom (algebraMap (C ⊗[A] B) (Localization.Away f)))
  have hj : Set.range j ⊆ Set.range W.ι := by
    rw [Scheme.Opens.range_ι]
    refine subset_trans ?_ hf
    exact (PrimeSpectrum.localization_away_comap_range (Localization.Away f) f).le
  have h1 : Etale (IsOpenImmersion.lift W.ι j hj ≫ W.ι ≫
      Spec.map (CommRingCat.ofHom (algebraMap C (C ⊗[A] B)))) := inferInstance
  rw [IsOpenImmersion.lift_fac_assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq,
    HasRingHomProperty.Spec_iff (P := @Etale), CommRingCat.hom_ofHom, RingHom.etale_algebraMap] at h1
  have h2 := mem_etaleLocus_of_flat p (Algebra.basicOpen_subset_etaleLocus_iff_etale.2 h1 hpf)
  rw [Algebra.mem_etaleLocus_iff] at h2
  obtain ⟨g, hg, hE⟩ := Algebra.exists_etale_of_isEtaleAt (R := A)
    (PrimeSpectrum.comap (algebraMap B (C ⊗[A] B)) p).asIdeal
  let i := Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away g)))
  refine ⟨i.opensRange, ?_, ?_⟩
  · exact (PrimeSpectrum.localization_away_comap_range (Localization.Away g) g).ge hg
  · have h3 : Etale (i ≫ Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq,
        HasRingHomProperty.Spec_iff (P := @Etale), CommRingCat.hom_ofHom, RingHom.etale_algebraMap]
      exact hE
    rw [← i.isoOpensRange_inv_comp, Category.assoc]
    infer_instance

theorem exists_etale_of_isAffine {U T S : Scheme.{0}} [IsAffine S] (τ : U ⟶ S) (h : T ⟶ S)
    [LocallyOfFinitePresentation τ] [Flat h] (W : (pullback τ h).Opens) (p : ↥(pullback τ h)) (hp : p ∈ W)
    (hW : Etale (W.ι ≫ pullback.snd τ h)) : ∃ V : U.Opens, pullback.fst τ h p ∈ V ∧ Etale (V.ι ≫ τ) := by
  obtain ⟨B, i, _, q, hq⟩ := U.exists_Spec_apply_eq (pullback.fst τ h p)
  obtain ⟨C, k, _, t, ht⟩ := T.exists_Spec_apply_eq (pullback.snd τ h p)
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (i ≫ τ ≫ S.isoSpec.hom)
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (k ≫ h ≫ S.isoSpec.hom)
  letI := φ.hom.toAlgebra
  letI := ψ.hom.toAlgebra
  letI : Algebra B (C ⊗[Γ(S, ⊤)] B) := Algebra.TensorProduct.rightAlgebra
  haveI : Algebra.FinitePresentation Γ(S, ⊤) B := by
    have : LocallyOfFinitePresentation (Spec.map φ) := by rw [hφ]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).1 this
  haveI : Module.Flat Γ(S, ⊤) C := by
    have : Flat (Spec.map ψ) := by rw [hψ]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @Flat)).1 this
  have hpb : IsPullback (Spec.map (CommRingCat.ofHom (algebraMap B (C ⊗[Γ(S, ⊤)] B))))
      (Spec.map (CommRingCat.ofHom (algebraMap C (C ⊗[Γ(S, ⊤)] B)))) (Spec.map φ) (Spec.map ψ) :=
    (isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct Γ(S, ⊤) C B)).flip
  let m := pullback.map (Spec.map φ) (Spec.map ψ) τ h i k S.isoSpec.inv (by simp [hφ]) (by simp [hψ])
  have hm : IsOpenImmersion m := inferInstance
  have hpm : p ∈ Set.range m := by
    rw [Scheme.Pullback.range_map]
    exact ⟨⟨q, hq⟩, ⟨t, ht⟩⟩
  let j := hpb.isoPullback.hom ≫ m
  have j1 : j ≫ pullback.fst τ h = Spec.map (CommRingCat.ofHom (algebraMap B (C ⊗[Γ(S, ⊤)] B))) ≫ i := by
    simp only [j, m, pullback.map, Category.assoc, pullback.lift_fst, IsPullback.isoPullback_hom_fst_assoc]
  have j2 : j ≫ pullback.snd τ h = Spec.map (CommRingCat.ofHom (algebraMap C (C ⊗[Γ(S, ⊤)] B))) ≫ k := by
    simp only [j, m, pullback.map, Category.assoc, pullback.lift_snd, IsPullback.isoPullback_hom_snd_assoc]
  obtain ⟨p', rfl⟩ : ∃ p', j p' = p := by
    obtain ⟨p₀, rfl⟩ := hpm
    obtain ⟨p₁, rfl⟩ := hpb.isoPullback.hom.surjective p₀
    exact ⟨p₁, by simp [j]⟩
  have h1 : Etale ((j ∣_ W) ≫ W.ι ≫ pullback.snd τ h) := inferInstance
  rw [morphismRestrict_ι_assoc, j2, ← Category.assoc] at h1
  have h2 := Etale.of_comp ((j ⁻¹ᵁ W).ι ≫ Spec.map (CommRingCat.ofHom (algebraMap C (C ⊗[Γ(S, ⊤)] B)))) k
  obtain ⟨V, hV, hE⟩ := exists_etale_spec (j ⁻¹ᵁ W) p' hp h2
  refine ⟨i ''ᵁ V, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, j1, Scheme.Hom.comp_apply]
    exact ⟨_, hV, rfl⟩
  · have hE' : Etale (V.ι ≫ Spec.map φ) := hE
    have e : (i ''ᵁ V).ι ≫ τ = (i.isoImage V).inv ≫ (V.ι ≫ Spec.map φ) ≫ S.isoSpec.inv := by
      simp [hφ]
    rw [e]
    infer_instance

theorem etale_nhds_of_flat_baseChange : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (U : Over (Sp R)) (g : ℕ) (τ : U.left ⟶ 𝔸(Fin g; Sp R)), LocallyOfFiniteType U.hom → τ ≫ (𝔸(Fin g; Sp R) ↘ Sp R) = U.hom → ∀ (T : Scheme.{0}) (h : T ⟶ 𝔸(Fin g; Sp R)), Flat h → ∀ (W : (pullback τ h).Opens) (p : ↥(pullback τ h)), p ∈ W → Etale (W.ι ≫ pullback.snd τ h) → ∃ V : U.left.Opens, pullback.fst τ h p ∈ V ∧ Etale (V.ι ≫ τ) := by
  intro R _ _ _ hR U g τ hU hτ T h hh W p hp hW
  haveI := hR.1
  haveI : LocallyOfFiniteType (τ ≫ (𝔸(Fin g; Sp R) ↘ Sp R)) := by rw [hτ]; exact hU
  haveI : LocallyOfFiniteType τ := locallyOfFiniteType_of_comp τ (𝔸(Fin g; Sp R) ↘ Sp R)
  haveI : IsLocallyNoetherian 𝔸(Fin g; Sp R) := LocallyOfFiniteType.isLocallyNoetherian (𝔸(Fin g; Sp R) ↘ Sp R)
  exact exists_etale_of_isAffine τ h W p hp hW

end GlobalTheory.EtaleAtDescent
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleNhdsAffineSpaceMapOfFlatBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_nhds_affineSpace_map_of_flat_baseChange : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (U : Over (Sp R)) (g : ℕ) (τ : U.left ⟶ 𝔸(Fin g; Sp R)), LocallyOfFiniteType U.hom → τ ≫ (𝔸(Fin g; Sp R) ↘ Sp R) = U.hom → ∀ (T : Scheme.{0}) (h : T ⟶ 𝔸(Fin g; Sp R)), Flat h → ∀ (W : (pullback τ h).Opens) (p : ↥(pullback τ h)), p ∈ W → Etale (W.ι ≫ pullback.snd τ h) → ∃ V : U.left.Opens, pullback.fst τ h p ∈ V ∧ Etale (V.ι ≫ τ) := by
  first | exact @GlobalTheory.EtaleAtDescent.etale_nhds_of_flat_baseChange | exact GlobalTheory.EtaleAtDescent.etale_nhds_of_flat_baseChange | (intros; apply GlobalTheory.EtaleAtDescent.etale_nhds_of_flat_baseChange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamilyPulledBackNearPointOfEtaleCoordinates
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamilyPulledBackNearPointOfEtaleCoordinates
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.EtalePull

theorem range_pt {Ω : Type} [Field Ω] {X : Scheme.{0}} (p : Sp Ω ⟶ X) (t : Sp Ω) : Set.range p = {p t} := by
  ext y
  constructor
  · rintro ⟨s, rfl⟩
    have : s = t := Subsingleton.elim (α := PrimeSpectrum Ω) s t
    simp [this]
  · rintro rfl
    exact ⟨t, rfl⟩

theorem range_comp' {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) : Set.range (f ≫ g) = g '' Set.range f := by
  rw [← Set.range_comp]
  exact congrArg Set.range (funext fun t => Scheme.Hom.comp_apply f g t)

theorem exists_isIso_restrict {X Y U : Scheme.{0}} (f : X ⟶ Y) (q : Y ⟶ U) [Etale f] [UniversallyClosed f]
    [UniversallyClosed q] (x : U)
    (hinj : ∀ (Ω : Type) [Field Ω] (p p' : Sp Ω ⟶ X), Set.range (p ≫ f ≫ q) = {x} → p ≫ f = p' ≫ f → p = p')
    (hsurj : ∀ y : Y, q y = x → y ∈ Set.range f) :
    ∃ W : U.Opens, x ∈ W ∧ IsIso (f ∣_ (q ⁻¹ᵁ W)) := by
  have hΔ : IsOpenImmersion (pullback.diagonal f) := inferInstance
  let r : pullback f f ⟶ U := pullback.fst f f ≫ f ≫ q
  have h1 : IsClosed (r '' (Set.range (pullback.diagonal f))ᶜ) :=
    r.isClosedMap _ (pullback.diagonal f).isOpenEmbedding.isOpen_range.isClosed_compl
  have h2 : IsClosed (q '' (Set.range f)ᶜ) :=
    q.isClosedMap _ f.isOpenMap.isOpen_range.isClosed_compl
  let W : U.Opens := ⟨(r '' (Set.range (pullback.diagonal f))ᶜ)ᶜ ∩ (q '' (Set.range f)ᶜ)ᶜ,
    h1.isOpen_compl.inter h2.isOpen_compl⟩
  refine ⟨W, ⟨?_, ?_⟩, ?_⟩
  · rintro ⟨z, hz, hzx⟩
    apply hz
    let w := (pullback f f).fromSpecResidueField z
    have hw : w ≫ pullback.fst f f = w ≫ pullback.snd f f := by
      refine hinj ((pullback f f).residueField z) _ _ ?_ ?_
      · have : Set.range (w ≫ r) = {x} := by
          rw [range_comp', Scheme.range_fromSpecResidueField, Set.image_singleton, hzx]
        have e : (w ≫ pullback.fst f f) ≫ f ≫ q = w ≫ r := Category.assoc _ _ _
        exact (congrArg (fun k : Spec ((pullback f f).residueField z) ⟶ U => Set.range k) e).trans this
      · simp [pullback.condition]
    have hw2 : w = (w ≫ pullback.fst f f) ≫ pullback.diagonal f := by
      apply pullback.hom_ext
      · simp
      · simp [hw]
    have : z ∈ Set.range w := by rw [Scheme.range_fromSpecResidueField]; rfl
    obtain ⟨t, ht⟩ := this
    refine ⟨(w ≫ pullback.fst f f) t, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← hw2, ht]
  · rintro ⟨y, hy, hyx⟩
    exact hy (hsurj y hyx)
  · have hm : Mono (f ∣_ (q ⁻¹ᵁ W)) := by
      refine ⟨fun {T} u v huv => ?_⟩
      have e : (u ≫ (f ⁻¹ᵁ (q ⁻¹ᵁ W)).ι) ≫ f = (v ≫ (f ⁻¹ᵁ (q ⁻¹ᵁ W)).ι) ≫ f := by
        simp only [Category.assoc, ← morphismRestrict_ι]
        rw [← Category.assoc, huv, Category.assoc]
      let w : T ⟶ pullback f f := pullback.lift _ _ e
      have hr : Set.range w ⊆ Set.range (pullback.diagonal f) := by
        rintro _ ⟨t, rfl⟩
        by_contra hn
        have hW : q (f ((f ⁻¹ᵁ (q ⁻¹ᵁ W)).ι (u t))) ∈ W := (u t).2
        refine hW.1 ⟨w t, hn, ?_⟩
        have e3 : w ≫ r = u ≫ (f ⁻¹ᵁ (q ⁻¹ᵁ W)).ι ≫ f ≫ q := by
          simp only [w, r, pullback.lift_fst_assoc, Category.assoc]
        rw [← Scheme.Hom.comp_apply, e3]
        simp only [Scheme.Hom.comp_apply]
      have hl := IsOpenImmersion.lift_fac (pullback.diagonal f) w hr
      have e1 := congrArg (· ≫ pullback.fst f f) hl
      have e2 := congrArg (· ≫ pullback.snd f f) hl
      simp only [w, Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id,
        pullback.lift_fst, pullback.lift_snd] at e1 e2
      rw [← cancel_mono (f ⁻¹ᵁ (q ⁻¹ᵁ W)).ι, ← e1, e2]
    have ho : IsOpenImmersion (f ∣_ (q ⁻¹ᵁ W)) := IsOpenImmersion.of_flat_of_mono _
    refine (isIso_iff_isOpenImmersion_and_surjective _).2 ⟨ho, ⟨fun y => ?_⟩⟩
    have hW : q y.1 ∈ W := y.2
    have : y.1 ∈ Set.range f := by
      by_contra hn
      exact hW.2 ⟨y.1, hn, rfl⟩
    obtain ⟨s, hs⟩ := this
    refine ⟨⟨s, ?_⟩, ?_⟩
    · show q (f s) ∈ W
      rw [hs]; exact hW
    · apply Subtype.ext
      exact (morphismRestrict_base_coe _ _ _).trans hs

theorem exists_isIso_restrict' {X Y U : Scheme.{0}} (f : X ⟶ Y) (q : Y ⟶ U) [UniversallyClosed f]
    [UniversallyClosed q] (x : U) (V : U.Opens) (hx : x ∈ V) [Etale (f ∣_ (q ⁻¹ᵁ V))]
    (hinj : ∀ (Ω : Type) [Field Ω] (p p' : Sp Ω ⟶ X), Set.range (p ≫ f ≫ q) = {x} → p ≫ f = p' ≫ f → p = p')
    (hsurj : ∀ y : Y, q y = x → y ∈ Set.range f) :
    ∃ W : U.Opens, x ∈ W ∧ W ≤ V ∧ IsIso (f ∣_ (q ⁻¹ᵁ W)) := by
  obtain ⟨W, hW, hiso⟩ := exists_isIso_restrict (f ∣_ (q ⁻¹ᵁ V)) (q ∣_ V) ⟨x, hx⟩ (by
    intro Ω _ p p' h1 h2
    rw [← cancel_mono (f ⁻¹ᵁ (q ⁻¹ᵁ V)).ι]
    apply hinj
    · have e : (p ≫ (f ⁻¹ᵁ (q ⁻¹ᵁ V)).ι) ≫ f ≫ q = (p ≫ f ∣_ (q ⁻¹ᵁ V) ≫ q ∣_ V) ≫ V.ι := by
        simp
      rw [e, range_comp', h1]
      exact Set.image_singleton
    · simp only [Category.assoc, ← morphismRestrict_ι]
      rw [← Category.assoc, h2, Category.assoc]) (by
    intro y hy
    have h1 : q y.1 = x := (morphismRestrict_base_coe q V y).symm.trans (congrArg Subtype.val hy)
    obtain ⟨s, hs⟩ := hsurj y.1 h1
    refine ⟨⟨s, ?_⟩, ?_⟩
    · show q (f s) ∈ V
      rw [hs, h1]; exact hx
    · apply Subtype.ext
      exact (morphismRestrict_base_coe _ _ _).trans hs)
  refine ⟨V.ι ''ᵁ W, ⟨⟨x, hx⟩, hW, rfl⟩, V.ι_image_le W, ?_⟩
  rw [← image_morphismRestrict_preimage]
  exact (MorphismProperty.arrow_mk_iso_iff (.isomorphisms Scheme)
    (morphismRestrictRestrict f (q ⁻¹ᵁ V) ((q ∣_ V) ⁻¹ᵁ W))).1 hiso

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S X : Scheme.{0}) (π : S ⟶ Sp R) (U : Over (Sp R)) (a : X ⟶ U.left) (b : X ⟶ S) (g : ℕ) (τ : U.left ⟶ 𝔸(Fin g; Sp R)) (c : X ⟶ pullback (𝔸(Fin g; Sp R) ↘ Sp R) π), IsProper π → Surjective π → Function.Bijective π.appTop.hom → LocallyOfFiniteType U.hom → IsSeparated U.hom → IsProper a → (∀ V : U.left.Opens, Function.Bijective (a.app V).hom) → τ ≫ (𝔸(Fin g; Sp R) ↘ Sp R) = U.hom → c ≫ pullback.fst _ _ = a ≫ τ → c ≫ pullback.snd _ _ = b → Etale c → ∀ x : U.left, IsClosed ({x} : Set U.left) → U.hom x = closedPoint R → (∀ (Ω : Type) [Field Ω] (p p' : Sp Ω ⟶ X), Set.range (p ≫ a) = {x} → p ≫ a = p' ≫ a → p ≫ b = p' ≫ b → p = p') → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ξ : Sp Ω ⟶ U.left) (s : Sp Ω ⟶ S), Set.range ξ = {x} → ξ ≫ U.hom = s ≫ π → ∃ p : Sp Ω ⟶ X, p ≫ a = ξ ∧ p ≫ b = s) → ∀ V : U.left.Opens, x ∈ V → Etale (V.ι ≫ τ) → ∃ V : U.left.Opens, x ∈ V ∧ Etale (V.ι ≫ τ) ∧ IsPullback (a ∣_ V) ((a ⁻¹ᵁ V).ι ≫ b) (V.ι ≫ U.hom) π := by
  intro R _ _ _ _ S X π U a b g τ c hπ _ _ _ hU ha _ hτ hc1 hc2 hc x _ _ hinj hsurj V hxV hV
  have hcomm : a ≫ U.hom = b ≫ π := by
    rw [← hτ, ← Category.assoc, ← hc1, ← hc2, Category.assoc, Category.assoc, pullback.condition]
  obtain ⟨f, hf1, hf2⟩ : ∃ f : X ⟶ pullback U.hom π, f ≫ pullback.fst _ _ = a ∧ f ≫ pullback.snd _ _ = b :=
    ⟨pullback.lift a b hcomm, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  subst hf1
  have hfp : IsProper f := IsProper.of_comp f (pullback.fst U.hom π)
  let G : pullback U.hom π ⟶ pullback (𝔸(Fin g; Sp R) ↘ Sp R) π :=
    pullback.lift (pullback.fst _ _ ≫ τ) (pullback.snd _ _) (by rw [Category.assoc, hτ, pullback.condition])
  have hG1 : G ≫ pullback.fst _ _ = pullback.fst _ _ ≫ τ := pullback.lift_fst _ _ _
  have hG2 : G ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
  have hG : IsPullback G (pullback.fst U.hom π) (pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π) τ := by
    refine IsPullback.of_right ?_ hG1 (IsPullback.of_hasPullback _ π).flip
    rw [hG2, hτ]
    exact (IsPullback.of_hasPullback _ π).flip
  have hfG : f ≫ G = c := by
    apply pullback.hom_ext
    · rw [Category.assoc, hG1, hc1, Category.assoc]
    · rw [Category.assoc, hG2, hc2, hf2]
  have hG' := (isPullback_morphismRestrict (pullback.fst U.hom π) V).flip.paste_horiz hG
  have hGe : Etale ((pullback.fst U.hom π ⁻¹ᵁ V).ι ≫ G) :=
    MorphismProperty.of_isPullback (P := @Etale) hG'.flip hV
  have hfe : Etale (f ∣_ (pullback.fst U.hom π ⁻¹ᵁ V)) := by
    have : Etale (f ∣_ (pullback.fst U.hom π ⁻¹ᵁ V) ≫ (pullback.fst U.hom π ⁻¹ᵁ V).ι ≫ G) := by
      rw [morphismRestrict_ι_assoc, hfG]; infer_instance
    exact Etale.of_comp _ ((pullback.fst U.hom π ⁻¹ᵁ V).ι ≫ G)
  obtain ⟨W, hxW, hWV, hiso⟩ := exists_isIso_restrict' f (pullback.fst U.hom π) x V hxV (by
    intro Ω _ p p' h1 h2
    refine hinj Ω p p' h1 ?_ ?_
    · rw [← Category.assoc, h2, Category.assoc]
    · rw [← hf2, ← Category.assoc, h2, Category.assoc]) (by
    intro y hy
    let K := (pullback U.hom π).residueField y
    let w : Sp (AlgebraicClosure K) ⟶ pullback U.hom π :=
      Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))) ≫ (pullback U.hom π).fromSpecResidueField y
    let t : Sp (AlgebraicClosure K) := closedPoint (AlgebraicClosure K)
    have hw : w t = y := by
      have : w t ∈ Set.range ((pullback U.hom π).fromSpecResidueField y) := ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩
      rwa [Scheme.range_fromSpecResidueField] at this
    obtain ⟨p, hp1, hp2⟩ := hsurj (AlgebraicClosure K) (w ≫ pullback.fst _ _) (w ≫ pullback.snd _ _)
      (by rw [range_pt _ t, Scheme.Hom.comp_apply, hw, hy]) (by simp [pullback.condition])
    have : p ≫ f = w := by
      apply pullback.hom_ext
      · rw [Category.assoc, hp1]
      · rw [Category.assoc, hf2, hp2]
    exact ⟨p t, by rw [← Scheme.Hom.comp_apply, this, hw]⟩)
  refine ⟨W, hxW, ?_, ?_⟩
  · rw [← U.left.homOfLE_ι hWV, Category.assoc]
    infer_instance
  · have P1 := (isPullback_morphismRestrict (pullback.fst U.hom π) W).paste_vert (IsPullback.of_hasPullback U.hom π)
    have P0 : IsPullback (f ∣_ (pullback.fst U.hom π ⁻¹ᵁ W) ≫ pullback.fst U.hom π ∣_ W)
        (f ∣_ (pullback.fst U.hom π ⁻¹ᵁ W) ≫ (pullback.fst U.hom π ⁻¹ᵁ W).ι ≫ pullback.snd U.hom π)
        (W.ι ≫ U.hom) π :=
      P1.of_iso (asIso (f ∣_ (pullback.fst U.hom π ⁻¹ᵁ W))).symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (by simp) (by simp only [Iso.symm_hom, asIso_inv, IsIso.inv_hom_id_assoc, Iso.refl_hom, Category.comp_id])
        (by simp) (by simp)
    rw [morphismRestrict_ι_assoc, hf2, ← morphismRestrict_comp] at P0
    exact P0

end GlobalTheory.Mum.EtalePull
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamilyPulledBackNearPointOfEtaleCoordinatesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.family_pulled_back_near_point_of_etale_coordinates : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S X : Scheme.{0}) (π : S ⟶ Sp R) (U : Over (Sp R)) (a : X ⟶ U.left) (b : X ⟶ S) (g : ℕ) (τ : U.left ⟶ 𝔸(Fin g; Sp R)) (c : X ⟶ pullback (𝔸(Fin g; Sp R) ↘ Sp R) π), IsProper π → Surjective π → Function.Bijective π.appTop.hom → LocallyOfFiniteType U.hom → IsSeparated U.hom → IsProper a → (∀ V : U.left.Opens, Function.Bijective (a.app V).hom) → τ ≫ (𝔸(Fin g; Sp R) ↘ Sp R) = U.hom → c ≫ pullback.fst _ _ = a ≫ τ → c ≫ pullback.snd _ _ = b → Etale c → ∀ x : U.left, IsClosed ({x} : Set U.left) → U.hom x = closedPoint R → (∀ (Ω : Type) [Field Ω] (p p' : Sp Ω ⟶ X), Set.range (p ≫ a) = {x} → p ≫ a = p' ≫ a → p ≫ b = p' ≫ b → p = p') → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ξ : Sp Ω ⟶ U.left) (s : Sp Ω ⟶ S), Set.range ξ = {x} → ξ ≫ U.hom = s ≫ π → ∃ p : Sp Ω ⟶ X, p ≫ a = ξ ∧ p ≫ b = s) → ∀ V : U.left.Opens, x ∈ V → Etale (V.ι ≫ τ) → ∃ V : U.left.Opens, x ∈ V ∧ Etale (V.ι ≫ τ) ∧ IsPullback (a ∣_ V) ((a ⁻¹ᵁ V).ι ≫ b) (V.ι ≫ U.hom) π := by
  first | exact @GlobalTheory.Mum.EtalePull.main | exact GlobalTheory.Mum.EtalePull.main | (intros; apply GlobalTheory.Mum.EtalePull.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCoordinatesDescendAlongProperMap
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem etale_coord_descend : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S X : Scheme.{0}) (π : S ⟶ Sp R) (U : Over (Sp R)) (a : X ⟶ U.left) (b : X ⟶ S) (g : ℕ) (τ : U.left ⟶ 𝔸(Fin g; Sp R)) (c : X ⟶ pullback (𝔸(Fin g; Sp R) ↘ Sp R) π), IsProper π → Surjective π → Function.Bijective π.appTop.hom → LocallyOfFiniteType U.hom → IsSeparated U.hom → IsProper a → (∀ V : U.left.Opens, Function.Bijective (a.app V).hom) → τ ≫ (𝔸(Fin g; Sp R) ↘ Sp R) = U.hom → c ≫ pullback.fst _ _ = a ≫ τ → c ≫ pullback.snd _ _ = b → Etale c → ∀ x : U.left, IsClosed ({x} : Set U.left) → U.hom x = closedPoint R → (∀ (Ω : Type) [Field Ω] (p p' : Sp Ω ⟶ X), Set.range (p ≫ a) = {x} → p ≫ a = p' ≫ a → p ≫ b = p' ≫ b → p = p') → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ξ : Sp Ω ⟶ U.left) (s : Sp Ω ⟶ S), Set.range ξ = {x} → ξ ≫ U.hom = s ≫ π → ∃ p : Sp Ω ⟶ X, p ≫ a = ξ ∧ p ≫ b = s) → ∃ V : U.left.Opens, x ∈ V ∧ Etale (V.ι ≫ τ) ∧ IsPullback (a ∣_ V) ((a ⁻¹ᵁ V).ι ≫ b) (V.ι ≫ U.hom) π := by
  intro R _ _ _ hR S X π U a b g τ c hπ hs hΓ hlft hsep ha haV hτ hc1 hc2 hc x hx hxc hmono hsurj
  have hq := GlobalTheory.T.isolated_in_fibre_coordinateMap_affineSpace R hR S X π U a b g τ c hπ hs hΓ hlft hsep ha haV hτ hc1 hc2 hc x hx hxc hmono hsurj
  obtain ⟨T, h, W, p, hfl, hpW, hpx, hW⟩ := GlobalTheory.T.exists_flat_chart_etale_of_quasiFiniteAt_alt R hR S X π U a b g τ c hπ hs hΓ hlft hsep ha haV hτ hc1 hc2 hc x hx hxc hmono hsurj hq
  obtain ⟨V, hxV, hV⟩ := GlobalTheory.T.etale_nhds_affineSpace_map_of_flat_baseChange R hR U g τ hlft hτ T h hfl W p hpW hW
  rw [hpx] at hxV
  exact GlobalTheory.T.family_pulled_back_near_point_of_etale_coordinates R hR S X π U a b g τ c hπ hs hΓ hlft hsep ha haV hτ hc1 hc2 hc x hx hxc hmono hsurj V hxV hV

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCoordinatesDescendAlongProperMapStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleCoordinates_descend_along_proper_map : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S X : Scheme.{0}) (π : S ⟶ Sp R) (U : Over (Sp R)) (a : X ⟶ U.left) (b : X ⟶ S) (g : ℕ) (τ : U.left ⟶ 𝔸(Fin g; Sp R)) (c : X ⟶ pullback (𝔸(Fin g; Sp R) ↘ Sp R) π), IsProper π → Surjective π → Function.Bijective π.appTop.hom → LocallyOfFiniteType U.hom → IsSeparated U.hom → IsProper a → (∀ V : U.left.Opens, Function.Bijective (a.app V).hom) → τ ≫ (𝔸(Fin g; Sp R) ↘ Sp R) = U.hom → c ≫ pullback.fst _ _ = a ≫ τ → c ≫ pullback.snd _ _ = b → Etale c → ∀ x : U.left, IsClosed ({x} : Set U.left) → U.hom x = closedPoint R → (∀ (Ω : Type) [Field Ω] (p p' : Sp Ω ⟶ X), Set.range (p ≫ a) = {x} → p ≫ a = p' ≫ a → p ≫ b = p' ≫ b → p = p') → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ξ : Sp Ω ⟶ U.left) (s : Sp Ω ⟶ S), Set.range ξ = {x} → ξ ≫ U.hom = s ≫ π → ∃ p : Sp Ω ⟶ X, p ≫ a = ξ ∧ p ≫ b = s) → ∃ V : U.left.Opens, x ∈ V ∧ Etale (V.ι ≫ τ) ∧ IsPullback (a ∣_ V) ((a ⁻¹ᵁ V).ι ≫ b) (V.ι ≫ U.hom) π := by
  first | exact @GlobalTheory.Mum.etale_coord_descend | exact GlobalTheory.Mum.etale_coord_descend | (intros; apply GlobalTheory.Mum.etale_coord_descend <;> assumption)
end
