module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FerrandGlueFlatArtinianFibreProductStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGluedCommGroupSchemeArtinFibreProduct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleGlueMilnorPatchingArtinLocal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveFamilyRepresentativeZariskiGlue

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeGlueArtinianLocalFibreProduct
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyOfFinitePresentationOfNilpotentThickening
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyOfFinitePresentationOfNilpotentThickening
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

open scoped TensorProduct

namespace GlobalTheory

open Algebra in
theorem finiteType_of_finiteType_quotient_map_nilpotent {P A : Type} [CommRing P] [CommRing A]
    [Algebra P A] (I : Ideal P) (hI : IsNilpotent I)
    [h : Algebra.FiniteType P (A ⧸ I.map (algebraMap P A))] : Algebra.FiniteType P A := by
  set J := I.map (algebraMap P A)
  obtain ⟨s, hs⟩ := h.out
  classical
  let t : Finset A := s.image (fun x => Quotient.out x)
  have hmk : (Ideal.Quotient.mkₐ P J) '' (t : Set A) = (s : Set (A ⧸ J)) := by
    ext x; simp [t]
  let C := Algebra.adjoin P (t : Set A)
  have key : ∀ b : A, ∃ c ∈ C, b - c ∈ J := by
    intro b
    have hb : Ideal.Quotient.mkₐ P J b ∈ (C.map (Ideal.Quotient.mkₐ P J)) := by
      rw [AlgHom.map_adjoin, hmk, hs]; trivial
    obtain ⟨c, hc, hcb⟩ := hb
    exact ⟨c, hc, Ideal.Quotient.eq.mp (by simpa using hcb.symm)⟩
  have base : (⊤ : Submodule P A) ≤ Subalgebra.toSubmodule C ⊔ I • ⊤ := by
    intro b _
    obtain ⟨c, hc, hbc⟩ := key b
    have : b - c ∈ I • (⊤ : Submodule P A) := by
      rw [Ideal.smul_top_eq_map]; exact hbc
    have := Submodule.add_mem_sup (show c ∈ Subalgebra.toSubmodule C from hc) this
    simpa using this
  have step : ∀ n : ℕ, (⊤ : Submodule P A) ≤ Subalgebra.toSubmodule C ⊔ (I ^ n) • ⊤ := by
    intro n
    induction n with
    | zero =>
      intro b _
      exact Submodule.mem_sup_right (by rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]; trivial)
    | succ n ih =>
      refine ih.trans (sup_le le_sup_left ?_)
      calc (I ^ n) • (⊤ : Submodule P A) ≤ (I ^ n) • (Subalgebra.toSubmodule C ⊔ I • ⊤) :=
            Submodule.smul_mono le_rfl base
        _ = (I ^ n) • Subalgebra.toSubmodule C ⊔ (I ^ n) • (I • ⊤) := Submodule.smul_sup _ _ _
        _ ≤ Subalgebra.toSubmodule C ⊔ (I ^ (n + 1)) • ⊤ := by
            rw [pow_succ, Submodule.mul_smul]
            exact sup_le_sup_right Submodule.smul_le_right _
  obtain ⟨N, hN⟩ := hI
  have hC : Subalgebra.toSubmodule C = ⊤ := by
    have := step N
    rw [hN, Submodule.zero_eq_bot, Submodule.bot_smul, sup_bot_eq] at this
    exact top_le_iff.mp this
  exact ⟨⟨t, Algebra.toSubmodule_eq_top.mp hC⟩⟩

theorem finiteType_of_finiteType_tensor_nilpotent {P A R : Type} [CommRing P] [CommRing A]
    [CommRing R] [Algebra P A] [Algebra P R] (hs : Function.Surjective (algebraMap P R))
    (hn : IsNilpotent (RingHom.ker (algebraMap P R)))
    (h : (Algebra.TensorProduct.includeRight : R →ₐ[P] A ⊗[P] R).toRingHom.FiniteType) :
    Algebra.FiniteType P A := by
  have h1 : Algebra.FiniteType P (A ⊗[P] R) := by
    rw [← RingHom.finiteType_algebraMap,
      ← (Algebra.TensorProduct.includeRight : R →ₐ[P] A ⊗[P] R).comp_algebraMap]
    exact h.comp (RingHom.FiniteType.of_surjective _ hs)
  let f : P →ₐ[P] R := Algebra.ofId P R
  have hf : Function.Surjective f := hs
  let I : Ideal P := RingHom.ker f
  let e1 : (A ⧸ I.map (algebraMap P A)) ≃ₐ[P] A ⊗[P] (P ⧸ I) :=
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot A I).restrictScalars P
  let e2 : A ⊗[P] (P ⧸ I) ≃ₐ[P] A ⊗[P] R :=
    Algebra.TensorProduct.congr AlgEquiv.refl (Ideal.quotientKerAlgEquivOfSurjective hf)
  have h2 : Algebra.FiniteType P (A ⧸ I.map (algebraMap P A)) := h1.equiv (e1.trans e2).symm
  exact finiteType_of_finiteType_quotient_map_nilpotent I hn

theorem locallyOfFinitePresentation_specMap_of_isPullback_nilpotent {P R₁ A : CommRingCat.{0}}
    (f₁ : P ⟶ R₁) (hs : Function.Surjective f₁) (hn : IsNilpotent (RingHom.ker f₁.hom))
    [IsNoetherianRing P] (φ : P ⟶ A) {W : Scheme.{0}} (fst : W ⟶ Spec A) (snd : W ⟶ Spec R₁)
    (hsq : IsPullback fst snd (Spec.map φ) (Spec.map f₁)) (hsnd : LocallyOfFinitePresentation snd) :
    LocallyOfFinitePresentation (Spec.map φ) := by
  have h1 : LocallyOfFinitePresentation (pullback.snd (Spec.map φ) (Spec.map f₁)) := by
    have e : pullback.snd (Spec.map φ) (Spec.map f₁) = hsq.isoPullback.inv ≫ snd := by
      rw [Iso.eq_inv_comp, hsq.isoPullback_hom_snd]
    rw [e]
    exact MorphismProperty.comp_mem _ _ _ (locallyOfFinitePresentation_of_isOpenImmersion _) hsnd
  letI := φ.hom.toAlgebra
  letI := f₁.hom.toAlgebra
  have hT : LocallyOfFinitePresentation ((pullbackSpecIso P A R₁).inv ≫ pullback.snd _ _) :=
    MorphismProperty.comp_mem _ _ _ (locallyOfFinitePresentation_of_isOpenImmersion _) h1
  rw [pullbackSpecIso_inv_snd, LocallyOfFinitePresentation.SpecMap_iff] at hT
  rw [LocallyOfFinitePresentation.SpecMap_iff, ← RingHom.FinitePresentation.of_finiteType]
  exact finiteType_of_finiteType_tensor_nilpotent (A := A) hs hn (RingHom.FiniteType.of_finitePresentation hT)

theorem locallyOfFinitePresentation_of_nilpotent_thickening :
    ∀ (P R₁ : CommRingCat.{0}) (f₁ : P ⟶ R₁), Function.Surjective f₁ → IsNilpotent (RingHom.ker f₁.hom) → IsNoetherianRing P → ∀ (Y : Over (Spec P)) (Y₁ : Over (Spec R₁)) (j₁ : Y₁.left ⟶ Y.left), IsPullback j₁ Y₁.hom Y.hom (Spec.map f₁) → LocallyOfFinitePresentation Y₁.hom → LocallyOfFinitePresentation Y.hom := by
  intro P R₁ f₁ hs hn hP Y Y₁ j₁ hpb hY₁
  haveI : IsZariskiLocalAtSource @LocallyOfFinitePresentation.{0} :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := @LocallyOfFinitePresentation.{0})
    Y.left.affineOpenCover.openCover]
  intro i
  haveI : IsOpenImmersion (Y.left.affineOpenCover.f i) :=
    inferInstanceAs (IsOpenImmersion (Y.left.affineOpenCover.openCover.f i))
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (Y.left.affineOpenCover.f i ≫ Y.hom)
  have hsq : IsPullback (pullback.fst (Y.left.affineOpenCover.f i) j₁)
      (pullback.snd (Y.left.affineOpenCover.f i) j₁ ≫ Y₁.hom) (Spec.map φ) (Spec.map f₁) := by
    rw [hφ]; exact (IsPullback.of_hasPullback (Y.left.affineOpenCover.f i) j₁).paste_vert hpb
  have hfin := GlobalTheory.locallyOfFinitePresentation_specMap_of_isPullback_nilpotent f₁ hs hn φ _ _ hsq
    (MorphismProperty.comp_mem _ _ _ (locallyOfFinitePresentation_of_isOpenImmersion _) hY₁)
  rw [hφ] at hfin
  exact hfin

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyOfFinitePresentationOfNilpotentThickeningStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locallyOfFinitePresentation_of_nilpotent_thickening_noetherian : ∀ (P R₁ : CommRingCat.{0}) (f₁ : P ⟶ R₁), Function.Surjective f₁ → IsNilpotent (RingHom.ker f₁.hom) → IsNoetherianRing P → ∀ (Y : Over (Spec P)) (Y₁ : Over (Spec R₁)) (j₁ : Y₁.left ⟶ Y.left), IsPullback j₁ Y₁.hom Y.hom (Spec.map f₁) → LocallyOfFinitePresentation Y₁.hom → LocallyOfFinitePresentation Y.hom := by
  first | exact @GlobalTheory.locallyOfFinitePresentation_of_nilpotent_thickening | exact GlobalTheory.locallyOfFinitePresentation_of_nilpotent_thickening | (intros; apply GlobalTheory.locallyOfFinitePresentation_of_nilpotent_thickening <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeGlueArtinianLocalFibreProduct
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.GlueAb

theorem isNilpotent_ker {P R : CommRingCat.{0}} (f : P ⟶ R) [IsLocalRing P] [IsArtinianRing P]
    [Nontrivial R] : IsNilpotent (RingHom.ker f.hom) := by
  have h : IsNilpotent (IsLocalRing.maximalIdeal P) := by
    have := IsArtinianRing.isNilpotent_jacobson_bot (R := P)
    rwa [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at this
  obtain ⟨n, hn⟩ := h
  refine ⟨n, ?_⟩
  have := Ideal.pow_right_mono (IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top f.hom)) n
  rw [hn] at this
  exact le_antisymm this bot_le

theorem surjective_spec_map {P R : CommRingCat.{0}} (f : P ⟶ R) [IsLocalRing P] [IsArtinianRing P]
    [Nontrivial R] : Surjective (Spec.map f) := by
  constructor
  intro x
  obtain ⟨y⟩ : Nonempty (PrimeSpectrum R) := inferInstance
  refine ⟨y, ?_⟩
  have : Subsingleton (PrimeSpectrum P) := ⟨fun a b => PrimeSpectrum.ext <| by
    have ha := IsArtinianRing.isMaximal_of_isPrime a.asIdeal
    have hb := IsArtinianRing.isMaximal_of_isPrime b.asIdeal
    rw [IsLocalRing.eq_maximalIdeal ha, IsLocalRing.eq_maximalIdeal hb]⟩
  exact Subsingleton.elim (α := PrimeSpectrum P) _ _

theorem pullback_elem {P R₁ R₂ R₀ : CommRingCat.{0}} {f₁ : P ⟶ R₁} {f₂ : P ⟶ R₂} {g₁ : R₁ ⟶ R₀}
    {g₂ : R₂ ⟶ R₀} (h : IsPullback f₁ f₂ g₁ g₂) :
    (∀ x y : P, f₁ x = f₁ y → f₂ x = f₂ y → x = y) ∧
      (Function.Surjective g₂ → Function.Surjective f₁) := by
  have h' := (Types.isPullback_iff _ _ _ _).mp (h.map (forget CommRingCat))
  refine ⟨fun x y h1 h2 => h'.2.1 x y ⟨h1, h2⟩, fun hg r => ?_⟩
  obtain ⟨s, hs⟩ := hg (g₁ r)
  obtain ⟨p, hp, -⟩ := h'.2.2 r s hs.symm
  exact ⟨p, hp⟩

end GlobalTheory.GlueAb

namespace GlobalTheory.GlueAb

theorem main_of_nontrivial (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀)
    (g₂ : R₂ ⟶ R₀) (hpb : IsPullback f₁ f₂ g₁ g₂) (hl : IsLocalRing P) (ha : IsArtinianRing P)
    (hg₁ : Function.Surjective g₁) (hg₂ : Function.Surjective g₂) (hR : Nontrivial R₁)
    (A₁ : Over (Spec R₁)) [GrpObj A₁] (A₂ : Over (Spec R₂)) [GrpObj A₂] (A₀ : Over (Spec R₀))
    [GrpObj A₀] (ψ₁ : A₀.left ⟶ A₁.left) (ψ₂ : A₀.left ⟶ A₂.left) (h₁ : IsAbelianScheme A₁)
    (h₂ : IsAbelianScheme A₂) (hψ₁ : IsGrpPullback A₀ A₁ (Spec.map g₁) ψ₁)
    (hψ₂ : IsGrpPullback A₀ A₂ (Spec.map g₂) ψ₂) :
    ∃ (A : Over (Spec P)) (_ : GrpObj A) (φ₁ : A₁.left ⟶ A.left) (φ₂ : A₂.left ⟶ A.left),
      IsAbelianScheme A ∧ IsGrpPullback A₁ A (Spec.map f₁) φ₁ ∧ IsGrpPullback A₂ A (Spec.map f₂) φ₂ ∧
        ψ₁ ≫ φ₁ = ψ₂ ≫ φ₂ := by
  haveI := h₁.smooth
  haveI := h₂.smooth
  obtain ⟨Y, j₁, j₂, hj₁, hj₂, hY, hpo⟩ := GlobalTheory.T.ferrand_glue_flat_artinian_fibreProduct P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hpb hl ha hg₁ hg₂
    A₁ A₂ A₀ ψ₁ ψ₂ hψ₁.1 hψ₂.1 inferInstance inferInstance
  obtain ⟨G, hc, hG₁, hG₂⟩ := GlobalTheory.T.exists_glued_commGroupScheme_artinFibreProduct P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hpb hl ha hg₁ hg₂ A₁ A₂ A₀ ψ₁ ψ₂
    h₁.comm h₂.comm hψ₁ hψ₂ Y j₁ j₂ hj₁ hj₂ hY hpo
  refine ⟨Y, G, j₁, j₂, ?_, hG₁, hG₂, hpo.w⟩
  have hf₁ : Function.Surjective f₁ := (pullback_elem hpb).2 hg₂
  have hN : IsNilpotent (RingHom.ker f₁.hom) := isNilpotent_ker f₁
  have hlfp : LocallyOfFinitePresentation Y.hom :=
    GlobalTheory.T.locallyOfFinitePresentation_of_nilpotent_thickening_noetherian P R₁ f₁ hf₁ hN inferInstance Y A₁ j₁ hj₁ inferInstance
  have hsm : Smooth Y.hom := GlobalTheory.smooth_of_isPullback_of_surjective_of_flat _ _ _ _ (Spec.map f₁) j₁
    A₁.hom Y.hom hj₁ (surjective_spec_map f₁) hY hlfp h₁.smooth
  obtain ⟨hp, hgc⟩ := GlobalTheory.NilLift.isProper_and_geometricallyConnected_of_smooth_lift P R₁ f₁.hom hf₁ hN
    Y A₁ j₁ hj₁ hsm h₁.proper h₁.geomConnected
  exact ⟨hc, hsm, hp, hgc⟩

theorem main : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (A₁ : Over (Spec R₁)) [GrpObj A₁] (A₂ : Over (Spec R₂)) [GrpObj A₂] (A₀ : Over (Spec R₀)) [GrpObj A₀] (ψ₁ : A₀.left ⟶ A₁.left) (ψ₂ : A₀.left ⟶ A₂.left), IsAbelianScheme A₁ → IsAbelianScheme A₂ → IsGrpPullback A₀ A₁ (Spec.map g₁) ψ₁ → IsGrpPullback A₀ A₂ (Spec.map g₂) ψ₂ → ∃ (A : Over (Spec P)) (_ : GrpObj A) (φ₁ : A₁.left ⟶ A.left) (φ₂ : A₂.left ⟶ A.left), IsAbelianScheme A ∧ IsGrpPullback A₁ A (Spec.map f₁) φ₁ ∧ IsGrpPullback A₂ A (Spec.map f₂) φ₂ ∧ ψ₁ ≫ φ₁ = ψ₂ ≫ φ₂ := by
  intro P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hpb hl ha hg₁ hg₂ A₁ _ A₂ _ A₀ _ ψ₁ ψ₂ h₁ h₂ hψ₁ hψ₂
  by_cases hR : Nontrivial R₁
  · exact main_of_nontrivial P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hpb hl ha hg₁ hg₂ hR A₁ A₂ A₀ ψ₁ ψ₂ h₁ h₂ hψ₁ hψ₂
  · have hR₂ : Nontrivial R₂ := by
      by_contra hR₂
      rw [not_nontrivial_iff_subsingleton] at hR hR₂
      exact zero_ne_one ((pullback_elem hpb).1 0 1 (Subsingleton.elim _ _) (Subsingleton.elim _ _))
    obtain ⟨A, G, φ₂, φ₁, hA, h₂', h₁', hw⟩ := main_of_nontrivial P R₂ R₁ R₀ f₂ f₁ g₂ g₁ hpb.flip hl ha
      hg₂ hg₁ hR₂ A₂ A₁ A₀ ψ₂ ψ₁ h₂ h₁ hψ₂ hψ₁
    exact ⟨A, G, φ₁, φ₂, hA, h₁', h₂', hw.symm⟩

end GlobalTheory.GlueAb
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeGlueArtinianLocalFibreProductStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_glue_artinian_local_fibreProduct : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (A₁ : Over (Spec R₁)) [GrpObj A₁] (A₂ : Over (Spec R₂)) [GrpObj A₂] (A₀ : Over (Spec R₀)) [GrpObj A₀] (ψ₁ : A₀.left ⟶ A₁.left) (ψ₂ : A₀.left ⟶ A₂.left), IsAbelianScheme A₁ → IsAbelianScheme A₂ → IsGrpPullback A₀ A₁ (Spec.map g₁) ψ₁ → IsGrpPullback A₀ A₂ (Spec.map g₂) ψ₂ → ∃ (A : Over (Spec P)) (_ : GrpObj A) (φ₁ : A₁.left ⟶ A.left) (φ₂ : A₂.left ⟶ A.left), IsAbelianScheme A ∧ IsGrpPullback A₁ A (Spec.map f₁) φ₁ ∧ IsGrpPullback A₂ A (Spec.map f₂) φ₂ ∧ ψ₁ ≫ φ₁ = ψ₂ ≫ φ₂ := by
  first | exact @GlobalTheory.GlueAb.main | exact GlobalTheory.GlueAb.main | (intros; apply GlobalTheory.GlueAb.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicEqZeroOfPullbacksEqZeroArtinFibreProduct
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicEqZeroOfPullbacksEqZeroArtinFibreProduct
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ArtinPicGlue

theorem units_lift_of_surjective {R R₀ : Type} [CommRing R] [CommRing R₀] (hR : Nontrivial R₀ → IsLocalRing R) (g : R →+* R₀)
    (hg : Function.Surjective g) (r : R₀ˣ) : ∃ r' : Rˣ, g r' = r := by
  rcases subsingleton_or_nontrivial R₀ with h | h
  · exact ⟨1, Subsingleton.elim _ _⟩
  · haveI := hR h
    haveI : IsLocalHom g := IsLocalHom.of_surjective g hg
    obtain ⟨a, ha⟩ := hg r
    exact ⟨(isUnit_of_map_unit g a (ha ▸ r.isUnit)).unit, ha⟩

theorem units_lift_baseChange (P R₂ R₀ : CommRingCat.{0}) (f₂ : P ⟶ R₂) (g₂ : R₂ ⟶ R₀) (hR : Nontrivial R₀ → IsLocalRing R₂)
    (hg₂ : Function.Surjective g₂) (A : Over (Spec P)) [GrpObj A] (hA : IsAbelianScheme A) :
    Function.Surjective (Units.map (A ◁ (Over.homMk (Spec.map g₂) (by simp [Spec.map_comp]) :
      Over.mk (Spec.map (f₂ ≫ g₂)) ⟶ Over.mk (Spec.map f₂))).left.appTop.hom.toMonoidHom) := by
  have hpb : IsPullback (fst A (Over.mk (Spec.map (f₂ ≫ g₂)))).left (snd A (Over.mk (Spec.map (f₂ ≫ g₂)))).left
      A.hom (Over.mk (Spec.map (f₂ ≫ g₂))).hom := IsPullback.of_hasPullback _ _
  obtain ⟨G, -, hAb, -⟩ := GlobalTheory.AbCoh.exists_grpObj_isGrpPullback_of_isPullback P R₀ (f₂ ≫ g₂).hom A _ _ _ hpb
  letI := G
  have hbij := GlobalTheory.globalFns_holds _ _ (hAb hA)
  let e := RingEquiv.ofBijective _ hbij
  intro u
  let u₀ : Γ((Over.mk (snd A (Over.mk (Spec.map (f₂ ≫ g₂)))).left).left, ⊤) := u.1
  have hu' : IsUnit (e.symm u₀) := by have := u.isUnit.map e.symm; exact this
  have hr : IsUnit ((Scheme.ΓSpecIso R₀).hom.hom (e.symm u₀)) := hu'.map _
  obtain ⟨r₂, hr₂⟩ := units_lift_of_surjective hR g₂.hom hg₂ hr.unit
  have hv : IsUnit ((snd A (Over.mk (Spec.map f₂))).left.appTop.hom ((Scheme.ΓSpecIso R₂).inv.hom r₂)) :=
    (r₂.isUnit.map (Scheme.ΓSpecIso R₂).inv.hom).map _
  refine ⟨hv.unit, Units.ext ?_⟩
  have hw : (A ◁ (Over.homMk (Spec.map g₂) (by simp [Spec.map_comp]) :
      Over.mk (Spec.map (f₂ ≫ g₂)) ⟶ Over.mk (Spec.map f₂))).left ≫ (snd A (Over.mk (Spec.map f₂))).left =
      (snd A (Over.mk (Spec.map (f₂ ≫ g₂)))).left ≫ Spec.map g₂ := by
    rw [← Over.comp_left, whiskerLeft_snd]; rfl
  have hn := Scheme.ΓSpecIso_inv_naturality g₂
  have h1 : (Spec.map g₂).appTop.hom ((Scheme.ΓSpecIso R₂).inv.hom r₂) =
      (Scheme.ΓSpecIso R₀).inv.hom (g₂.hom r₂) := by
    have := congrArg (fun φ => φ.hom (r₂ : R₂)) hn
    exact this.symm
  have key : (Spec.map g₂).appTop.hom ((Scheme.ΓSpecIso R₂).inv.hom r₂) = e.symm u₀ := by
    rw [h1, hr₂, IsUnit.unit_spec]
    exact congrArg (fun φ => φ.hom (e.symm u₀)) (Scheme.ΓSpecIso R₀).hom_inv_id
  have h2 := congrArg (fun φ => φ.appTop.hom ((Scheme.ΓSpecIso R₂).inv.hom r₂)) hw
  simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at h2
  simp only [Units.coe_map, IsUnit.unit_spec, MonoidHom.coe_coe]
  exact h2.trans ((congrArg _ key).trans (e.apply_symm_apply u₀))

theorem surjective_of_isPullback {P R₁ R₂ R₀ : CommRingCat.{0}} {f₁ : P ⟶ R₁} {f₂ : P ⟶ R₂} {g₁ : R₁ ⟶ R₀}
    {g₂ : R₂ ⟶ R₀} (h : IsPullback f₁ f₂ g₁ g₂) (hg₁ : Function.Surjective g₁) : Function.Surjective f₂ := by
  intro y
  obtain ⟨x, hx⟩ := hg₁ (g₂ y)
  have H := (Types.isPullback_iff _ _ _ _).1 (h.map (forget CommRingCat))
  obtain ⟨p, -, hp⟩ := H.2.2 x y hx
  exact ⟨p, hp⟩

theorem pic_eq_zero_of_pull_eq_zero : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (A : Over (Spec P)) [GrpObj A] (A₁ : Over (Spec R₁)) (A₂ : Over (Spec R₂)) (φ₁ : A₁.left ⟶ A.left) (φ₂ : A₂.left ⟶ A.left), IsAbelianScheme A → IsPullback φ₁ A₁.hom A.hom (Spec.map f₁) → IsPullback φ₂ A₂.hom A.hom (Spec.map f₂) → ∀ c : GlobalTheory.CechPic.Pic A.left, GlobalTheory.CechPic.pull φ₁ c = 0 → GlobalTheory.CechPic.pull φ₂ c = 0 → c = 0 := by
  intro P R₁ R₂ R₀ f₁ f₂ g₁ g₂ h hP _ hg₁ hg₂ A _ A₁ A₂ φ₁ φ₂ hA h₁ h₂ c hc₁ hc₂
  haveI : Flat A.hom := by have := hA.smooth; infer_instance
  have hf₂ := surjective_of_isPullback h hg₁
  have hloc : Nontrivial R₀ → IsLocalRing R₂ := fun _ => by
    haveI : Nontrivial R₂ := g₂.hom.domain_nontrivial
    exact IsLocalRing.of_surjective' f₂.hom hf₂
  let T : Over (Spec P) := Over.mk (𝟙 (Spec P))
  let T₁ : Over (Spec P) := Over.mk (Spec.map f₁)
  let T₂ : Over (Spec P) := Over.mk (Spec.map f₂)
  let T₀ : Over (Spec P) := Over.mk (Spec.map (f₂ ≫ g₂))
  let j₁ : T₁ ⟶ T := Over.homMk (Spec.map f₁) (by simp [T, T₁])
  let j₂ : T₂ ⟶ T := Over.homMk (Spec.map f₂) (by simp [T, T₂])
  let k₁ : T₀ ⟶ T₁ := Over.homMk (Spec.map g₁) (by simp only [T₀, T₁, Over.mk_hom]; rw [← Spec.map_comp, h.w])
  let k₂ : T₀ ⟶ T₂ := Over.homMk (Spec.map g₂) (by simp [T₀, T₂, Spec.map_comp])
  have hM : GlobalTheory.DualOpen.Milnor j₁.left j₂.left k₁.left k₂.left := GlobalTheory.DualOpen.Milnor.of_isPullback h hg₂
  have key := GlobalTheory.DualOpen.pic_eq_zero_of_milnor (Spec P) A T T₁ T₂ T₀ j₁ j₂ k₁ k₂ hM
    (units_lift_baseChange P R₂ R₀ f₂ g₂ hloc hg₂ A hA)
  let s : A ⟶ A ⊗ T := lift (𝟙 A) (Over.homMk A.hom (by simp [T]))
  have hs : s.left ≫ (fst A T).left = 𝟙 _ := by rw [← Over.comp_left, lift_fst]; rfl
  have hc : c = GlobalTheory.CechPic.pull s.left (GlobalTheory.CechPic.pull (fst A T).left c) := by
    rw [← GlobalTheory.CechPic.pull_comp, hs, GlobalTheory.CechPic.pull_id]
  rw [hc, key (GlobalTheory.CechPic.pull (fst A T).left c) ?_ ?_, map_zero]
  · rw [← GlobalTheory.CechPic.pull_comp, ← Over.comp_left, whiskerLeft_fst]
    have hm := h₁.lift_fst (fst A T₁).left (snd A T₁).left ((Over.w (fst A T₁)).trans (Over.w (snd A T₁)).symm)
    rw [← hm, GlobalTheory.CechPic.pull_comp, hc₁, map_zero]
  · rw [← GlobalTheory.CechPic.pull_comp, ← Over.comp_left, whiskerLeft_fst]
    have hm := h₂.lift_fst (fst A T₂).left (snd A T₂).left ((Over.w (fst A T₂)).trans (Over.w (snd A T₂)).symm)
    rw [← hm, GlobalTheory.CechPic.pull_comp, hc₂, map_zero]

end GlobalTheory.ArtinPicGlue
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicEqZeroOfPullbacksEqZeroArtinFibreProductStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pic_eq_zero_of_pullbacks_eq_zero_artinFibreProduct : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (A : Over (Spec P)) [GrpObj A] (A₁ : Over (Spec R₁)) (A₂ : Over (Spec R₂)) (φ₁ : A₁.left ⟶ A.left) (φ₂ : A₂.left ⟶ A.left), IsAbelianScheme A → IsPullback φ₁ A₁.hom A.hom (Spec.map f₁) → IsPullback φ₂ A₂.hom A.hom (Spec.map f₂) → ∀ c : GlobalTheory.CechPic.Pic A.left, GlobalTheory.CechPic.pull φ₁ c = 0 → GlobalTheory.CechPic.pull φ₂ c = 0 → c = 0 := by
  first | exact @GlobalTheory.ArtinPicGlue.pic_eq_zero_of_pull_eq_zero | exact GlobalTheory.ArtinPicGlue.pic_eq_zero_of_pull_eq_zero | (intros; apply GlobalTheory.ArtinPicGlue.pic_eq_zero_of_pull_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelPrincipalArtinianOfPrincipalPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleOfClosedProper
open GlobalTheory.AbLaw
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.SharpLift

theorem relAmple_of_closed_proper (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (B : Over (Spec (CommRingCat.of R))) [IsProper B.hom] [Flat B.hom] (M : LB B.left) (hM : M.IsLB)
    (R₀ : Type) [CommRing R₀] [Nontrivial R₀] (g : R →+* R₀) (hg : Function.Surjective g)
    (Y₀ : Over (Spec (CommRingCat.of R₀))) (b : Y₀.left ⟶ B.left)
    (hb : IsPullback b Y₀.hom B.hom (Spec.map (CommRingCat.ofHom g)))
    (N₀ : LB Y₀.left) (hN₀ : N₀.IsLB) (hiso : LBIso N₀ (M.pull b)) (hA : RelAmple Y₀ N₀) : RelAmple B M := by
  have hker : RingHom.ker g ≤ RingHom.ker (IsLocalRing.residue R) := by
    rw [IsLocalRing.ker_residue]
    exact IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top g)
  let g' : R₀ →+* IsLocalRing.ResidueField R :=
    RingHom.liftOfSurjective g hg ⟨IsLocalRing.residue R, hker⟩
  have hg' : g'.comp g = IsLocalRing.residue R := RingHom.liftOfSurjective_comp g hg _
  let k := Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
  have hk : Spec.map (CommRingCat.ofHom g') ≫ Spec.map (CommRingCat.ofHom g) = k := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hg']
  let ψ : pullback B.hom k ⟶ Y₀.left := hb.lift (pullback.fst B.hom k)
    (pullback.snd B.hom k ≫ Spec.map (CommRingCat.ofHom g'))
    (by rw [Category.assoc, hk, pullback.condition])
  have hψ : ψ ≫ b = pullback.fst B.hom k := hb.lift_fst _ _ _
  have hψ' : IsPullback ψ (pullback.snd B.hom k) Y₀.hom (Spec.map (CommRingCat.ofHom g')) := by
    refine IsPullback.of_right ?_ (hb.lift_snd _ _ _) hb
    rw [hψ, hk]
    exact IsPullback.of_hasPullback _ _
  have h₁ : RelAmple ((Over.pullback k).obj B) (M.pull (pullback.fst B.hom k)) :=
    GlobalTheory.AmpleLocalBase.relAmple_baseChange (A' := (Over.pullback k).obj B) hψ' hN₀ (pull_isLB hM _)
      (LBIso.chartPull (Geo.Tor.chartPullPull N₀ ψ ψ rfl)
        (chartPullSame M (fun _ : PUnit => pullback.fst B.hom k) (fun _ => b) (fun _ => 1) ψ
          fun _ => hψ.symm) hiso).symm hA
  obtain ⟨r, hr, h₂⟩ := GlobalTheory.ProperFinite.relAmple_near_fibre B hM (IsLocalRing.residue R) (fun y => by
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
    exact ⟨a, 1, by simp, by simp⟩) h₁
  have hu : IsUnit r := (IsLocalRing.residue_ne_zero_iff_isUnit r).1 hr
  have htop : PrimeSpectrum.basicOpen r = ⊤ := by
    exact top_le_iff.1 fun p _ => fun hp => p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hp hu)
  generalize (PrimeSpectrum.basicOpen r : (Spec (CommRingCat.of R)).Opens) = U at htop h₂
  subst htop
  let j := Scheme.Opens.ι (X := Spec (CommRingCat.of R)) ⊤
  have : IsIso j := inferInstanceAs (IsIso (Spec (CommRingCat.of R)).topIso.hom)
  have : IsAffine (⊤ : (Spec (CommRingCat.of R)).Opens).toScheme := isAffineOpen_top _
  have h₃ : IsPullback (inv (pullback.fst B.hom j)) B.hom (pullback.snd B.hom j) (inv j) :=
    IsPullback.of_horiz_isIso ⟨by
      rw [IsIso.inv_comp_eq, ← Category.assoc, pullback.condition, Category.assoc, IsIso.hom_inv_id,
        Category.comp_id]⟩
  refine GlobalTheory.AmpleLocalBase.relAmple_baseChange (A := (Over.pullback j).obj B) h₃ (pull_isLB hM _) hM ?_ h₂
  exact (LBIso.chartPull (Geo.Tor.chartPullPull _ _ _ rfl) (chartPullSec M _ _ (IsIso.inv_hom_id (pullback.fst B.hom j)))
    ⟨_, idIso_isGen (pull_isLB hM _)⟩).symm

theorem kTriv_of_localHom (R₁ R : Type) [CommRing R₁] [IsLocalRing R₁] [IsNoetherianRing R₁] [CommRing R] [IsLocalRing R]
    (π : R₁ →+* R) [IsLocalHom π] (B : Over (Sp R₁)) [GrpObj B] (hB : IsAbelianScheme B) (M : LB B.left) (hM : M.IsLB)
    (hA : RelAmple B M) (Y₀ : Over (Sp R)) [GrpObj Y₀] (b : Y₀.left ⟶ B.left) (hb : IsGrpPullback Y₀ B (spMap π) b)
    (N₀ : LB Y₀.left) (hN₀ : N₀.IsLB) (hiso : LBIso N₀ (M.pull b)) (hK : KTriv Y₀ N₀) : KTriv B M := by
  obtain ⟨U, hU, H⟩ := GlobalTheory.KTrivGlob.exists_open hM hN₀ hB hA hb hiso hK (IsLocalRing.closedPoint R)
  have hcl : (spMap π) (IsLocalRing.closedPoint R) = IsLocalRing.closedPoint R₁ := by
    exact IsLocalRing.comap_closedPoint π
  have htop : U = ⊤ := by
    rw [hcl] at hU
    exact top_le_iff.1 fun p _ => (IsLocalRing.specializes_closedPoint p).mem_open U.2 hU
  subst htop
  have hL := pull_isLB hM (pullback.fst B.hom (⊤ : (Sp R₁).Opens).ι)
  have hPB := isGrpPullback_pullback B (⊤ : (Sp R₁).Opens).ι
  have hAb : IsAbelianScheme ((Over.pullback (⊤ : (Sp R₁).Opens).ι).obj B) := by
    have := hB.comm
    refine ⟨?_, MorphismProperty.of_isPullback (P := @Smooth) hPB.1 hB.smooth,
      MorphismProperty.of_isPullback (P := @IsProper) hPB.1 hB.proper,
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) hPB.1 hB.geomConnected⟩
    rw [isCommMonObj_iff_isMulCommutative]
    intro T
    refine ⟨⟨fun x y => Over.OverMorphism.ext (hPB.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
    rw [← hPB.2 T x y (pushPt hPB.1.w x) (pushPt hPB.1.w y) rfl rfl,
      ← hPB.2 T y x (pushPt hPB.1.w y) (pushPt hPB.1.w x) rfl rfl, _root_.mul_comm]
  exact GlobalTheory.CoverGlue.kTriv_of_cover _ PUnit (fun _ => ⊤) B _ _ (by simp)
    (fun _ => isGrpPullback_pullback B _) _ _ hM (fun _ => hL) (fun _ => GlobalTheory.lbIso_refl hL) hB
    (fun _ => hAb) (fun _ => H)

end GlobalTheory.SharpLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelPrincipalArtinianOfPrincipalPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.CechPic GlobalTheory.PrincipalIntegral
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ArtinPrinc

theorem surj_of_isPullback {P R₁ R₂ R₀ : CommRingCat.{0}} {f₁ : P ⟶ R₁} {f₂ : P ⟶ R₂} {g₁ : R₁ ⟶ R₀} {g₂ : R₂ ⟶ R₀}
    (hP : IsPullback f₁ f₂ g₁ g₂) (hs : Function.Surjective g₂) : Function.Surjective f₁ := by
  have h := hP.map (forget CommRingCat)
  intro r
  obtain ⟨r₂, hr₂⟩ := hs (g₁ r)
  obtain ⟨x, hx, -⟩ := ((Types.isPullback_iff _ _ _ _).1 h).2.2 r r₂ hr₂.symm
  exact ⟨x, hx⟩

theorem principal_of_pull : ∀ (g n : ℕ), 3 ≤ n → Odd n → ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → Nontrivial R₁ → ∀ (β : CommRingCat.of (cycAway n) ⟶ P) (c : SiegPre g n (zetaAway n) (Spec.map β)) (c₁ : SiegPre g n (zetaAway n) (Spec.map f₁ ≫ Spec.map β)), SiegPB c₁ c (Spec.map f₁) → c₁.Principal → c.Principal := by
  intro g n _ _ P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hloc hart _ hs₂ _ β c c₁ hpb hc₁
  obtain ⟨φ, φ₂, hφ, hsq, hw, -⟩ := hpb
  obtain ⟨hA₁, hK₁⟩ := hc₁
  have hl : Out.Laws := GlobalTheory.abelianSchemeLaws_all.1
  have hf₁ : Function.Surjective f₁.hom := surj_of_isPullback hP hs₂
  let f := Spec.map f₁
  have hPc : cls c₁.P c₁.isLB = pull φ₂ (cls c.P c.isLB) := (cls_eq_iff _ (pull_isLB c.isLB _)).2 hw
  have hpair : ∀ {T : Over (Spec P)} {T' : Over (Spec R₁)} (u : T'.left ⟶ T.left) (a b : T ⟶ c.A)
      (a' b' : T' ⟶ c₁.A), a'.left ≫ φ = u ≫ a.left → b'.left ≫ φ = u ≫ b.left →
      GlobalTheory.PrincipalIntegral.pair (cls c₁.P c₁.isLB) a' b' = pull u (GlobalTheory.PrincipalIntegral.pair (cls c.P c.isLB) a b) := fun u a b a' b' ha hb => by
    rw [GlobalTheory.PrincipalIntegral.pair, GlobalTheory.PrincipalIntegral.pair, hPc, ← pull_comp, ← pull_comp, SiegelDescent.lift_comp_square hsq u a b a' b' ha hb]
  have hD : c.diag.IsLB := pull_isLB c.isLB _
  have hD₁ : c₁.diag.IsLB := pull_isLB c₁.isLB _
  have hd : cls c₁.diag hD₁ = pull φ (cls c.diag hD) :=
    hpair φ (𝟙 c.A) (𝟙 c.A) (𝟙 c₁.A) (𝟙 c₁.A) (by simp) (by simp)
  have hdiso : LBIso c₁.diag (c.diag.pull φ) := by
    refine (cls_eq_iff hD₁ (pull_isLB hD _)).1 ?_
    rw [cls_pull hD, hd]
  haveI := c.ab.proper
  haveI := c.ab.smooth
  have hA : Out.RelAmple c.A c.diag :=
    GlobalTheory.SharpLift.relAmple_of_closed_proper P c.A c.diag hD R₁ f₁.hom hf₁ c₁.A φ hφ.1 c₁.diag hD₁ hdiso hA₁
  refine ⟨hA, fun T x hx => ?_⟩
  obtain ⟨hpos, hdet⟩ := isE8_W8
  let G := Out.powObj c.A 8
  let pr : Fin 8 → (G ⟶ c.A) := Out.powPr c.A
  have hmon : ∀ u, IsMonHom (pr u) := fun u => inferInstance
  have huniv : ∀ (T : Over (Spec P)) (y : Fin 8 → (T ⟶ c.A)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u := fun T y =>
    ⟨(Out.powIsLimit c.A 8).lift (Fan.mk T y), fun u => (Out.powIsLimit c.A 8).fac (Fan.mk T y) ⟨u⟩,
      fun x hx => (Out.powIsLimit c.A 8).uniq (Fan.mk T y) x fun u => hx u.as⟩
  have hG : IsAbelianScheme G := AbelianSchemeGerms.isAbelianScheme_powObj c.A c.ab 7
  let G' := (Over.pullback f).obj G
  let ψ : G'.left ⟶ G.left := Pdiv.PullbackComparison.pφ f G
  have hψ : IsGrpPullback G' G f ψ := Pdiv.PullbackComparison.isGrpPullback f G
  choose pr' hpr using fun u => SharpPull.exists_lift hψ hφ (pr u)
  have hmon' : ∀ u, IsMonHom (pr' u) := fun u => SharpPull.isMonHom_lift hψ hφ (hpr u)
  have huniv' : ∀ (T : Over (Spec R₁)) (y : Fin 8 → (T ⟶ c₁.A)), ∃! x : T ⟶ G', ∀ u, x ≫ pr' u = y u :=
    fun T y => by
    obtain ⟨x₀, hx₀, hu⟩ := huniv (Over.mk (T.hom ≫ f)) (fun u => pushHom hφ T (y u))
    obtain ⟨x, rfl⟩ := SharpPull.push_surj hψ x₀
    refine ⟨x, fun u => SharpPull.push_inj hφ ?_, fun x' hx' => SharpPull.push_inj hψ (hu _ fun u => ?_)⟩
    · rw [SharpPull.push_comp hψ hφ (hpr u), hx₀ u]
    · rw [← SharpPull.push_comp hψ hφ (hpr u), hx' u]
  let L := LB.LinComb c.P (K := Fin 8 × Fin 8) (fun uv => (lift (pr uv.1) (pr uv.2)).left) fun uv => W8 uv.1 uv.2
  let L' := LB.LinComb c₁.P (K := Fin 8 × Fin 8) (fun uv => (lift (pr' uv.1) (pr' uv.2)).left)
    fun uv => W8 uv.1 uv.2
  have hL : L.IsLB := LB.isLB_linComb c.isLB _ _
  have hL' : L'.IsLB := LB.isLB_linComb c₁.isLB _ _
  have hLW : cls L hL = quad (cls c.P c.isLB) W8 pr := cls_linComb c.isLB _ _ _
  have hLW' : cls L' hL' = quad (cls c₁.P c₁.isLB) W8 pr' := cls_linComb c₁.isLB _ _ _
  have hiso : LBIso L' (L.pull ψ) := by
    refine (cls_eq_iff hL' (pull_isLB hL _)).1 ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [cls_pull hL, hLW, hLW', quad, quad, map_sum]
    exact Finset.sum_congr rfl fun uv _ => by rw [map_zsmul, hpair ψ _ _ _ _ (hpr uv.1) (hpr uv.2)]
  have hadd := pair_mul c hl.globalFns hA
  have hadd' := pair_mul c₁ hl.globalFns hA₁
  have hK' : Out.KTriv G' L' := kTriv_of_kernel hadd' (pair_comm c₁) hmon' huniv' hL' hLW' hdet fun T x hx =>
    hK₁ T x ((cls_eq_zero_iff (pull_isLB c₁.isLB _)).1 hx)
  have hAL : Out.RelAmple G L :=
    PosDefAmple.relAmple_linComb_of_posDef hl.globalFns g n 8 _ _ _ _ c G pr W8 hmon huniv hA hpos
  haveI : IsLocalRing R₁ := IsLocalRing.of_surjective' f₁.hom hf₁
  haveI : IsLocalHom f₁.hom := Function.Surjective.isLocalHom f₁.hom hf₁
  have hK : Out.KTriv G L := GlobalTheory.SharpLift.kTriv_of_localHom P R₁ f₁.hom G hG L hL hAL G' ψ hψ L' hL' hiso hK'
  have hx' : GlobalTheory.PrincipalIntegral.pair (cls c.P c.isLB) (snd c.A T ≫ x) (fst c.A T) = 0 := (cls_eq_zero_iff (pull_isLB c.isLB _)).2 hx
  exact kernel_of_kTriv (n := 8) (G := G) hadd (pair_comm c) hmon huniv hL hLW (0 : Fin 8) hK T x hx'

end GlobalTheory.ArtinPrinc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelPrincipalArtinianOfPrincipalPullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_principal_artinian_of_principal_pullback : ∀ (g n : ℕ), 3 ≤ n → Odd n → ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → Nontrivial R₁ → ∀ (β : CommRingCat.of (cycAway n) ⟶ P) (c : SiegPre g n (zetaAway n) (Spec.map β)) (c₁ : SiegPre g n (zetaAway n) (Spec.map f₁ ≫ Spec.map β)), SiegPB c₁ c (Spec.map f₁) → c₁.Principal → c.Principal := by
  first | exact @GlobalTheory.ArtinPrinc.principal_of_pull | exact GlobalTheory.ArtinPrinc.principal_of_pull | (intros; apply GlobalTheory.ArtinPrinc.principal_of_pull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreProductSpecFieldPointFactors
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreProductSpecFieldPointFactors
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.SpecFibreProduct

theorem point_factors (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀)
    (g₂ : R₂ ⟶ R₀) (hP : IsPullback f₁ f₂ g₁ g₂) (hg₁ : Function.Surjective g₁)
    (hg₂ : Function.Surjective g₂) (k : Type) [Field k] (x : Spec (CommRingCat.of k) ⟶ Spec P) :
    (∃ y : Spec (CommRingCat.of k) ⟶ Spec R₁, y ≫ Spec.map f₁ = x) ∨
      (∃ y : Spec (CommRingCat.of k) ⟶ Spec R₂, y ≫ Spec.map f₂ = x) := by
  have H := (Types.isPullback_iff _ _ _ _).1 (hP.map (forget CommRingCat))
  have hinj : ∀ a b : P, f₁.hom a = f₁.hom b → f₂.hom a = f₂.hom b → a = b :=
    fun a b h₁ h₂ ↦ H.2.1 a b ⟨h₁, h₂⟩
  have hex : ∀ (b : R₁) (c : R₂), g₁.hom b = g₂.hom c → ∃ a : P, f₁.hom a = b ∧ f₂.hom a = c :=
    fun b c h ↦ H.2.2 b c h
  have hs₁ : Function.Surjective f₁.hom := by
    intro b
    obtain ⟨c, hc⟩ := hg₂ (g₁.hom b)
    obtain ⟨a, ha, -⟩ := hex b c hc.symm
    exact ⟨a, ha⟩
  have hs₂ : Function.Surjective f₂.hom := by
    intro c
    obtain ⟨b, hb⟩ := hg₁ (g₂.hom c)
    obtain ⟨a, -, ha⟩ := hex b c hb
    exact ⟨a, ha⟩
  set χ : P ⟶ CommRingCat.of k := Spec.preimage x with hχ
  have hx : Spec.map χ = x := Spec.map_preimage x
  by_cases h : RingHom.ker f₁.hom ≤ RingHom.ker χ.hom
  · left
    let ψ : R₁ →+* k := f₁.hom.liftOfRightInverse (Function.surjInv hs₁)
      (Function.rightInverse_surjInv hs₁) ⟨χ.hom, h⟩
    have hψ : ∀ a, ψ (f₁.hom a) = χ.hom a := fun a ↦
      f₁.hom.liftOfRightInverse_comp_apply _ _ ⟨χ.hom, h⟩ a
    have he : f₁ ≫ CommRingCat.ofHom ψ = χ := CommRingCat.hom_ext (RingHom.ext hψ)
    exact ⟨Spec.map (CommRingCat.ofHom ψ), by rw [← Spec.map_comp, he, hx]⟩
  · right
    have h₂ : RingHom.ker f₂.hom ≤ RingHom.ker χ.hom := by
      intro b hb
      obtain ⟨a, ha, ha'⟩ := SetLike.not_le_iff_exists.1 h
      rw [RingHom.mem_ker] at ha hb ⊢
      rw [RingHom.mem_ker] at ha'
      have hab : a * b = 0 := hinj _ _ (by rw [map_mul, ha, zero_mul, map_zero])
        (by rw [map_mul, hb, mul_zero, map_zero])
      have : χ.hom a * χ.hom b = 0 := by rw [← map_mul, hab, map_zero]
      exact (mul_eq_zero.1 this).resolve_left ha'
    let ψ : R₂ →+* k := f₂.hom.liftOfRightInverse (Function.surjInv hs₂)
      (Function.rightInverse_surjInv hs₂) ⟨χ.hom, h₂⟩
    have hψ : ∀ a, ψ (f₂.hom a) = χ.hom a := fun a ↦
      f₂.hom.liftOfRightInverse_comp_apply _ _ ⟨χ.hom, h₂⟩ a
    have he : f₂ ≫ CommRingCat.ofHom ψ = χ := CommRingCat.hom_ext (RingHom.ext hψ)
    exact ⟨Spec.map (CommRingCat.ofHom ψ), by rw [← Spec.map_comp, he, hx]⟩

end GlobalTheory.SpecFibreProduct
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreProductSpecFieldPointFactorsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibreProduct_spec_fieldPoint_factors : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (k : Type) [Field k] (x : Spec (CommRingCat.of k) ⟶ Spec P), (∃ y : Spec (CommRingCat.of k) ⟶ Spec R₁, y ≫ Spec.map f₁ = x) ∨ (∃ y : Spec (CommRingCat.of k) ⟶ Spec R₂, y ≫ Spec.map f₂ = x) := by
  first | exact @GlobalTheory.SpecFibreProduct.point_factors | exact GlobalTheory.SpecFibreProduct.point_factors | (intros; apply GlobalTheory.SpecFibreProduct.point_factors <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrincipalSiegelObjectGlueArtinFibreProduct
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ArtinGlue
open GlobalTheory.SiegelDescent GlobalTheory.SiegDesc GlobalTheory.CechPic

theorem lem_ab : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (A₁ : Over (Spec R₁)) [GrpObj A₁] (A₂ : Over (Spec R₂)) [GrpObj A₂] (A₀ : Over (Spec R₀)) [GrpObj A₀] (ψ₁ : A₀.left ⟶ A₁.left) (ψ₂ : A₀.left ⟶ A₂.left), IsAbelianScheme A₁ → IsAbelianScheme A₂ → IsGrpPullback A₀ A₁ (Spec.map g₁) ψ₁ → IsGrpPullback A₀ A₂ (Spec.map g₂) ψ₂ → ∃ (A : Over (Spec P)) (_ : GrpObj A) (φ₁ : A₁.left ⟶ A.left) (φ₂ : A₂.left ⟶ A.left), IsAbelianScheme A ∧ IsGrpPullback A₁ A (Spec.map f₁) φ₁ ∧ IsGrpPullback A₂ A (Spec.map f₂) φ₂ ∧ ψ₁ ≫ φ₁ = ψ₂ ≫ φ₂ := GlobalTheory.T.abelianScheme_glue_artinian_local_fibreProduct

theorem lem_lb : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (X : Over (Spec P)) (X₁ : Over (Spec R₁)) (X₂ : Over (Spec R₂)) (X₀ : Over (Spec R₀)) (j₁ : X₁.left ⟶ X.left) (j₂ : X₂.left ⟶ X.left) (i₁ : X₀.left ⟶ X₁.left) (i₂ : X₀.left ⟶ X₂.left), Flat X.hom → IsPullback j₁ X₁.hom X.hom (Spec.map f₁) → IsPullback j₂ X₂.hom X.hom (Spec.map f₂) → IsPullback i₁ X₀.hom X₁.hom (Spec.map g₁) → i₁ ≫ j₁ = i₂ ≫ j₂ → i₂ ≫ X₂.hom = X₀.hom ≫ Spec.map g₂ → ∀ (L₁ : LB X₁.left) (L₂ : LB X₂.left), L₁.IsLB → L₂.IsLB → LBIso (L₁.pull i₁) (L₂.pull i₂) → ∃ L : LB X.left, L.IsLB ∧ LBIso L₁ (L.pull j₁) ∧ LBIso L₂ (L.pull j₂) := GlobalTheory.T.exists_lineBundle_glue_milnorPatching_artinLocal

theorem lem_triv : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (A : Over (Spec P)) [GrpObj A] (A₁ : Over (Spec R₁)) (A₂ : Over (Spec R₂)) (φ₁ : A₁.left ⟶ A.left) (φ₂ : A₂.left ⟶ A.left), IsAbelianScheme A → IsPullback φ₁ A₁.hom A.hom (Spec.map f₁) → IsPullback φ₂ A₂.hom A.hom (Spec.map f₂) → ∀ c : GlobalTheory.CechPic.Pic A.left, GlobalTheory.CechPic.pull φ₁ c = 0 → GlobalTheory.CechPic.pull φ₂ c = 0 → c = 0 := GlobalTheory.T.pic_eq_zero_of_pullbacks_eq_zero_artinFibreProduct

theorem lem_pt : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (k : Type) [Field k] (x : Spec (CommRingCat.of k) ⟶ Spec P), (∃ y : Spec (CommRingCat.of k) ⟶ Spec R₁, y ≫ Spec.map f₁ = x) ∨ (∃ y : Spec (CommRingCat.of k) ⟶ Spec R₂, y ≫ Spec.map f₂ = x) := GlobalTheory.T.fibreProduct_spec_fieldPoint_factors

theorem lem_princ : ∀ (g n : ℕ), 3 ≤ n → Odd n → ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → Nontrivial R₁ → ∀ (β : CommRingCat.of (cycAway n) ⟶ P) (c : SiegPre g n (zetaAway n) (Spec.map β)) (c₁ : SiegPre g n (zetaAway n) (Spec.map f₁ ≫ Spec.map β)), SiegPB c₁ c (Spec.map f₁) → c₁.Principal → c.Principal := GlobalTheory.T.siegel_principal_artinian_of_principal_pullback

theorem geom_transfer {S S' : Scheme.{0}} {B : Type} [CommRing B] {ζ : B} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B} {h M : ℕ}
    (c : SiegPre h M ζ s') (A₀ : Over S) [GrpObj A₀] [IsCommMonObj A₀] (f : S' ⟶ S) (φ : c.A.left ⟶ A₀.left)
    (P₀ : LB (G2 A₀).left) (lev₀ : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ A₀)) (hs : s' = f ≫ s)
    (hp : IsGrpPullback c.A A₀ f φ) (hP₀ : P₀.IsLB)
    (diag : LBIso (c.P.pull (lift (𝟙 c.A) (𝟙 c.A)).left) ((P₀.pull (lift (𝟙 A₀) (𝟙 A₀)).left).pull φ))
    (hlev : ∀ a, (c.lev a).left ≫ φ = f ≫ (lev₀ a).left) (k : Type) [Field k] [IsAlgClosed k]
    (x : Sp k ⟶ S) (y : Sp k ⟶ S') (hy : y ≫ f = x) (β : B →+* k) (z : kˣ) (hx : x ≫ s = spMap β)
    (hz : (z : k) = β ζ) :
    (∀ a, (toUnit (Over.mk x) ≫ lev₀ a = 1 ↔ ∃ b, a = M • b)) ∧
    (∀ g : Over.mk x ⟶ A₀, g ^ M = 1 → ∃ a, toUnit _ ≫ lev₀ a = g) ∧
    ∀ a b, Out.WeilIs A₀ (P₀.pull (lift (𝟙 A₀) (𝟙 A₀)).left) M (toUnit (Over.mk x) ≫ lev₀ a) (toUnit _ ≫ lev₀ b)
      (unitOn (z ^ (2 * omegaStd a b))) := by
  have hφ : φ ≫ A₀.hom = c.A.hom ≫ f := hp.1.w
  obtain ⟨g₁, g₂, g₃⟩ := c.geom k y β z (by rw [hs, ← Category.assoc, hy, hx]) hz
  obtain ⟨σ, hσ⟩ := exists_liftHom hp (Over.mk y) (Over.mk x) (𝟙 _) ((Category.id_comp _).trans hy.symm)
  have σinj : Function.Injective σ := fun u v e => Over.OverMorphism.ext (by
    simpa using ((hσ u _).1 rfl).symm.trans ((hσ v _).1 e.symm))
  have pt : ∀ a, (toUnit (Over.mk y) ≫ c.lev a).left ≫ φ = (toUnit (Over.mk x) ≫ lev₀ a).left := fun a => by
    change (y ≫ (c.lev a).left) ≫ φ = x ≫ (lev₀ a).left
    rw [Category.assoc, hlev, ← Category.assoc, hy]
  have σlev : ∀ a, σ (toUnit _ ≫ lev₀ a) = toUnit _ ≫ c.lev a := fun a =>
    (hσ _ _).2 ((pt a).trans (Category.id_comp _).symm)
  refine ⟨fun a => ?_, fun g hg => ?_, fun a b => ?_⟩
  · rw [← g₁ a, ← σlev, map_eq_one_iff σ σinj]
  · obtain ⟨a, ha⟩ := g₂ (σ g) (by rw [← map_pow, hg, map_one])
    exact ⟨a, σinj ((σlev a).trans ha)⟩
  · have hD := pull_isLB hP₀ (lift (𝟙 A₀) (𝟙 A₀)).left
    have H := (GlobalTheory.weilIs_grpPullback_of_comm _ _ A₀ c.A f φ _ _ hD (pull_isLB c.isLB _) hp diag _ _ _ _
      (pushPt hφ _) (pushPt hφ _) _ rfl rfl).1 (g₃ a b)
    exact weilIs_congr hy _ _ _ _ _ _ (pt a) (pt b) _ H

theorem spec_isPushout (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀)
    (hP : IsPullback f₁ f₂ g₁ g₂) (hl : IsLocalRing P) (ha : IsArtinianRing P) (s₁ : Function.Surjective g₁)
    (s₂ : Function.Surjective g₂) : IsPushout (Spec.map g₁) (Spec.map g₂) (Spec.map f₁) (Spec.map f₂) := by
  have w : Spec.map g₁ ≫ Spec.map f₁ = Spec.map g₂ ≫ Spec.map f₂ := by
    rw [← Spec.map_comp, ← Spec.map_comp, hP.w]
  exact GlobalTheory.T.flat_over_artinFibreProduct_isPushout P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hl ha s₁ s₂ (Over.mk (𝟙 _)) (Over.mk (𝟙 _)) (Over.mk (𝟙 _))
    (Over.mk (𝟙 _)) (Spec.map f₁) (Spec.map f₂) (Spec.map g₁) (Spec.map g₂) (show Flat (𝟙 (Spec P)) from inferInstance) (IsPullback.id_vert _)
    (IsPullback.id_vert _) (IsPullback.id_vert _) w (by simp)

theorem nontrivial_of_pt (R : CommRingCat.{0}) (k : Type) [Field k] (y : Spec (CommRingCat.of k) ⟶ Spec R) :
    Nontrivial R := by
  obtain ⟨pt⟩ : Nonempty (PrimeSpectrum k) := inferInstance
  exact PrimeSpectrum.nonempty_iff_nontrivial.1 ⟨y.base pt⟩

theorem exists_principal_glue : ∀ (g n : ℕ), 3 ≤ n → Odd n → ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (β : CommRingCat.of (cycAway n) ⟶ P) (c₁ : SiegPre g n (zetaAway n) (Spec.map f₁ ≫ Spec.map β)) (c₂ : SiegPre g n (zetaAway n) (Spec.map f₂ ≫ Spec.map β)), c₁.Principal → c₂.Principal → (∃ c₀ : SiegPre g n (zetaAway n) (Spec.map g₁ ≫ Spec.map f₁ ≫ Spec.map β), SiegPB c₀ c₁ (Spec.map g₁) ∧ SiegPB c₀ c₂ (Spec.map g₂)) → ∃ c : SiegPre g n (zetaAway n) (Spec.map β), c.Principal ∧ SiegPB c₁ c (Spec.map f₁) ∧ SiegPB c₂ c (Spec.map f₂) := by
  intro g n hn hodd P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hloc hart hs₁ hs₂ β c₁ c₂ hp₁ hp₂ hc₀
  obtain ⟨c₀, ⟨ψ₁, ψ₁₂, hψ₁, sψ₁, iψ₁, lψ₁⟩, ⟨ψ₂, ψ₂₂, hψ₂, sψ₂, iψ₂, lψ₂⟩⟩ := hc₀
  obtain ⟨A, instA, φ₁, φ₂, hA, hφ₁, hφ₂, hcomm⟩ :=
    lem_ab P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hloc hart hs₁ hs₂ c₁.A c₂.A c₀.A ψ₁ ψ₂ c₁.ab c₂.ab hψ₁ hψ₂
  haveI := hA.comm
  have hAA : IsAbelianScheme (G2 A) := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  obtain ⟨φ₁₂, sφ₁⟩ := exists_isSquare hφ₁.1.w
  obtain ⟨φ₂₂, sφ₂⟩ := exists_isSquare hφ₂.1.w
  obtain ⟨χ₂, sχ⟩ := exists_isSquare (f := Spec.map g₁ ≫ Spec.map f₁) (φ := ψ₁ ≫ φ₁)
    (by rw [Category.assoc, hφ₁.1.w]; exact (reassoc_of% hψ₁.1.w) _)
  have e₁₂ : ψ₁₂ ≫ φ₁₂ = χ₂ := isSquare_comp rfl sψ₁ sφ₁ sχ
  have e₂₂ : ψ₂₂ ≫ φ₂₂ = χ₂ := isSquare_comp hcomm.symm sψ₂ sφ₂ sχ
  have flat : Flat (G2 A).hom := by
    haveI := hAA.smooth
    infer_instance
  have hiso₀ : LBIso (c₁.P.pull ψ₁₂) (c₂.P.pull ψ₂₂) :=
    LBIso.trans (pull_isLB c₁.isLB _) c₀.isLB (pull_isLB c₂.isLB _) iψ₁.symm iψ₂
  obtain ⟨L, hL, w₁, w₂⟩ := lem_lb P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hloc hart hs₁ hs₂ (G2 A) (G2 c₁.A) (G2 c₂.A)
    (G2 c₀.A) φ₁₂ φ₂₂ ψ₁₂ ψ₂₂ flat (isPullback_of_isSquare hφ₁.1 sφ₁) (isPullback_of_isSquare hφ₂.1 sφ₂)
    (isPullback_of_isSquare hψ₁.1 sψ₁) (e₁₂.trans e₂₂.symm) (isSquare_w hψ₂.1.w sψ₂) c₁.P c₂.P c₁.isLB c₂.isLB
    hiso₀
  have clsP₁ : cls c₁.P c₁.isLB = pull φ₁₂ (cls L hL) := by
    rw [← cls_pull hL φ₁₂ (pull_isLB hL _)]
    exact (cls_eq_iff _ _).2 w₁
  have clsP₂ : cls c₂.P c₂.isLB = pull φ₂₂ (cls L hL) := by
    rw [← cls_pull hL φ₂₂ (pull_isLB hL _)]
    exact (cls_eq_iff _ _).2 w₂
  have rig : ∀ (a₁ : c₁.A ⟶ c₁.A ⊗ c₁.A) (a₂ : c₂.A ⟶ c₂.A ⊗ c₂.A) (a : A ⟶ A ⊗ A),
      a₁.left ≫ φ₁₂ = φ₁ ≫ a.left → a₂.left ≫ φ₂₂ = φ₂ ≫ a.left →
      (∃ t : (c₁.P.pull a₁.left).Gen, t.IsGen) → (∃ t : (c₂.P.pull a₂.left).Gen, t.IsGen) →
      ∃ t : (L.pull a.left).Gen, t.IsGen := by
    intro a₁ a₂ a e₁ e₂ t₁ t₂
    refine (cls_eq_zero_iff (pull_isLB hL _)).1 ?_
    rw [cls_pull hL _ (pull_isLB hL _)]
    refine lem_triv P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hloc hart hs₁ hs₂ A c₁.A c₂.A φ₁ φ₂ hA hφ₁.1 hφ₂.1 _ ?_ ?_
    · rw [← pull_comp, ← e₁, pull_comp, ← clsP₁, ← cls_pull c₁.isLB _ (pull_isLB c₁.isLB _)]
      exact (cls_eq_zero_iff _).2 t₁
    · rw [← pull_comp, ← e₂, pull_comp, ← clsP₂, ← cls_pull c₂.isLB _ (pull_isLB c₂.isLB _)]
      exact (cls_eq_zero_iff _).2 t₂
  have one₁ := one_comp hφ₁ c₁.A A φ₁ hφ₁.1.w
  have one₂ := one_comp hφ₂ c₂.A A φ₂ hφ₂.1.w
  have idφ₁ : (𝟙 c₁.A : c₁.A ⟶ c₁.A).left ≫ φ₁ = φ₁ ≫ (𝟙 A : A ⟶ A).left := by simp
  have idφ₂ : (𝟙 c₂.A : c₂.A ⟶ c₂.A).left ≫ φ₂ = φ₂ ≫ (𝟙 A : A ⟶ A).left := by simp
  have symm : LBIso L (L.pull (lift (snd A A) (fst A A)).left) := by
    have sw₁ := lift_square sφ₁ sφ₁.2.symm sφ₁.1.symm
    have sw₂ := lift_square sφ₂ sφ₂.2.symm sφ₂.1.symm
    refine (cls_eq_iff hL (pull_isLB hL _)).1 (sub_eq_zero.1 (lem_triv P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hloc hart hs₁ hs₂
      (G2 A) (G2 c₁.A) (G2 c₂.A) φ₁₂ φ₂₂ hAA (isPullback_of_isSquare hφ₁.1 sφ₁)
      (isPullback_of_isSquare hφ₂.1 sφ₂) _ ?_ ?_))
    · rw [map_sub, cls_pull hL _ (pull_isLB hL _), ← pull_comp, ← sw₁, pull_comp, ← clsP₁,
        ← cls_pull c₁.isLB _ (pull_isLB c₁.isLB _), sub_eq_zero]
      exact (cls_eq_iff _ _).2 c₁.symm
    · rw [map_sub, cls_pull hL _ (pull_isLB hL _), ← pull_comp, ← sw₂, pull_comp, ← clsP₂,
        ← cls_pull c₂.isLB _ (pull_isLB c₂.isLB _), sub_eq_zero]
      exact (cls_eq_iff _ _).2 c₂.symm

  have hpo := spec_isPushout P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hloc hart hs₁ hs₂
  have levc : ∀ a, Spec.map g₁ ≫ (c₁.lev a).left ≫ φ₁ = Spec.map g₂ ≫ (c₂.lev a).left ≫ φ₂ := fun a => by
    simp only [← Category.assoc]
    rw [← lψ₁ a, ← lψ₂ a, Category.assoc, Category.assoc, hcomm]
  have sec : ∀ {X : Scheme.{0}} {Bv : Over X} (u : 𝟙_ (Over X) ⟶ Bv), u.left ≫ Bv.hom = 𝟙 X := fun u => by
    simpa using Over.w u
  have hlev : ∀ a, ∃ l : 𝟙_ (Over (Spec P)) ⟶ A, Spec.map f₁ ≫ l.left = (c₁.lev a).left ≫ φ₁ ∧
      Spec.map f₂ ≫ l.left = (c₂.lev a).left ≫ φ₂ := fun a =>
    ⟨Over.homMk (hpo.desc _ _ (levc a)) (by
      refine hpo.hom_ext ?_ ?_
      · rw [← Category.assoc, hpo.inl_desc, Category.assoc, hφ₁.1.w, ← Category.assoc, sec]
        simp
      · rw [← Category.assoc, hpo.inr_desc, Category.assoc, hφ₂.1.w, ← Category.assoc, sec]
        simp), hpo.inl_desc _ _ _, hpo.inr_desc _ _ _⟩
  choose lev hl₁ hl₂ using hlev
  obtain ⟨ρ₁, hρ₁⟩ := exists_liftHom hφ₁ (𝟙_ _) (𝟙_ _) (Spec.map f₁)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
  obtain ⟨ρ₂, hρ₂⟩ := exists_liftHom hφ₂ (𝟙_ _) (𝟙_ _) (Spec.map f₂)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
  have ρl₁ : ∀ a, ρ₁ (lev a) = c₁.lev a := fun a => (hρ₁ _ _).2 (hl₁ a).symm
  have ρl₂ : ∀ a, ρ₂ (lev a) = c₂.lev a := fun a => (hρ₂ _ _).2 (hl₂ a).symm
  have inj : ∀ x y : 𝟙_ (Over (Spec P)) ⟶ A, ρ₁ x = ρ₁ y → ρ₂ x = ρ₂ y → x = y := fun x y e₁ e₂ =>
    Over.OverMorphism.ext (hpo.hom_ext
      (by rw [← (hρ₁ x _).1 rfl, ← (hρ₁ y _).1 rfl, e₁])
      (by rw [← (hρ₂ x _).1 rfl, ← (hρ₂ y _).1 rfl, e₂]))
  have diag₁ : LBIso (c₁.P.pull (lift (𝟙 c₁.A) (𝟙 c₁.A)).left) ((L.pull (lift (𝟙 A) (𝟙 A)).left).pull φ₁) :=
    lbIso_square c₁.isLB hL w₁ (lift_square sφ₁ idφ₁ idφ₁)
  have diag₂ : LBIso (c₂.P.pull (lift (𝟙 c₂.A) (𝟙 c₂.A)).left) ((L.pull (lift (𝟙 A) (𝟙 A)).left).pull φ₂) :=
    lbIso_square c₂.isLB hL w₂ (lift_square sφ₂ idφ₂ idφ₂)
  let c : SiegPre g n (zetaAway n) (Spec.map β) :=
    { A := A, ab := hA, P := L, isLB := hL
      rig₁ := rig _ _ _ (lift_square sφ₁ one₁ idφ₁) (lift_square sφ₂ one₂ idφ₂) c₁.rig₁ c₂.rig₁
      rig₂ := rig _ _ _ (lift_square sφ₁ idφ₁ one₁) (lift_square sφ₂ idφ₂ one₂) c₁.rig₂ c₂.rig₂
      symm := symm, lev := lev
      lev_add := fun a b => inj _ _ (by rw [map_mul, ρl₁, ρl₁, ρl₁, c₁.lev_add])
        (by rw [map_mul, ρl₂, ρl₂, ρl₂, c₂.lev_add])
      lev_tors := fun a => inj _ _ (by rw [map_pow, ρl₁, c₁.lev_tors, map_one])
        (by rw [map_pow, ρl₂, c₂.lev_tors, map_one])
      geom := by
        intro k _ _ x β' z hx hz
        rcases lem_pt P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hs₁ hs₂ k x with ⟨y, hy⟩ | ⟨y, hy⟩
        · exact geom_transfer c₁ A (Spec.map f₁) φ₁ L lev rfl hφ₁ hL diag₁ (fun a => (hl₁ a).symm) k x y hy β' z hx hz
        · exact geom_transfer c₂ A (Spec.map f₂) φ₂ L lev rfl hφ₂ hL diag₂ (fun a => (hl₂ a).symm) k x y hy β' z hx hz }
  have pb₁ : SiegPB c₁ c (Spec.map f₁) := ⟨φ₁, φ₁₂, hφ₁, sφ₁, w₁, fun a => (hl₁ a).symm⟩
  have pb₂ : SiegPB c₂ c (Spec.map f₂) := ⟨φ₂, φ₂₂, hφ₂, sφ₂, w₂, fun a => (hl₂ a).symm⟩
  refine ⟨c, ?_, pb₁, pb₂⟩
  rcases lem_pt P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hs₁ hs₂ (IsLocalRing.ResidueField P)
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue P))) with ⟨y, -⟩ | ⟨y, -⟩
  · haveI := nontrivial_of_pt R₁ _ y
    exact lem_princ g n hn hodd P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hloc hart hs₁ hs₂ inferInstance β c c₁ pb₁ hp₁
  · haveI := nontrivial_of_pt R₂ _ y
    exact lem_princ g n hn hodd P R₂ R₁ R₀ f₂ f₁ g₂ g₁ hP.flip hloc hart hs₂ hs₁ inferInstance β c c₂ pb₂ hp₂

end GlobalTheory.ArtinGlue
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrincipalSiegelObjectGlueArtinFibreProductStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_principalSiegelObject_glue_artinFibreProduct : ∀ (g n : ℕ), 3 ≤ n → Odd n → ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (β : CommRingCat.of (cycAway n) ⟶ P) (c₁ : SiegPre g n (zetaAway n) (Spec.map f₁ ≫ Spec.map β)) (c₂ : SiegPre g n (zetaAway n) (Spec.map f₂ ≫ Spec.map β)), c₁.Principal → c₂.Principal → (∃ c₀ : SiegPre g n (zetaAway n) (Spec.map g₁ ≫ Spec.map f₁ ≫ Spec.map β), SiegPB c₀ c₁ (Spec.map g₁) ∧ SiegPB c₀ c₂ (Spec.map g₂)) → ∃ c : SiegPre g n (zetaAway n) (Spec.map β), c.Principal ∧ SiegPB c₁ c (Spec.map f₁) ∧ SiegPB c₂ c (Spec.map f₂) := by
  first | exact @GlobalTheory.ArtinGlue.exists_principal_glue | exact GlobalTheory.ArtinGlue.exists_principal_glue | (intros; apply GlobalTheory.ArtinGlue.exists_principal_glue <;> assumption)
end
