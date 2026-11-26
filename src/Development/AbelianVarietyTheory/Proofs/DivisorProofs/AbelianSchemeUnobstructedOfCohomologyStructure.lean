module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AxesVanishingDegreeOneExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveDegreeTwoExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveClassDegreeTwoStructureSheafVanish
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeUnobstructedOfFormsStructure

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeUnobstructedOfConstantDimension
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeLiftOfSplitRing
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothCoprodDescOfSmoothPieces
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothCoprodDescOfSmoothPieces
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ProdGlue

theorem smooth_desc_of_isColimit : ∀ {S S₁ S₂ X₁ X₂ : Scheme.{0}} (u₁ : S₁ ⟶ S) (u₂ : S₂ ⟶ S), Nonempty (Limits.IsColimit (Limits.BinaryCofan.mk u₁ u₂)) → ∀ (x₁ : X₁ ⟶ S₁) (x₂ : X₂ ⟶ S₂), Smooth x₁ → Smooth x₂ → Smooth (Limits.coprod.desc (x₁ ≫ u₁) (x₂ ≫ u₂)) := by
  intro S S₁ S₂ X₁ X₂ u₁ u₂ ⟨hc⟩ x₁ x₂ h₁ h₂
  let e := Limits.IsColimit.coconePointUniqueUpToIso (Limits.coprodIsCoprod S₁ S₂) hc
  have e₁ : Limits.coprod.inl ≫ e.hom = u₁ :=
    Limits.IsColimit.comp_coconePointUniqueUpToIso_hom (Limits.coprodIsCoprod S₁ S₂) hc ⟨Limits.WalkingPair.left⟩
  have e₂ : Limits.coprod.inr ≫ e.hom = u₂ :=
    Limits.IsColimit.comp_coconePointUniqueUpToIso_hom (Limits.coprodIsCoprod S₁ S₂) hc ⟨Limits.WalkingPair.right⟩
  have i₁ : IsOpenImmersion (Limits.coprod.inl : S₁ ⟶ S₁ ⨿ S₂) := inferInstance
  have i₂ : IsOpenImmersion (Limits.coprod.inr : S₂ ⟶ S₁ ⨿ S₂) := inferInstance
  have : IsIso e.hom := Iso.isIso_hom e
  have ie : IsOpenImmersion e.hom := inferInstance
  have o₁ : IsOpenImmersion u₁ := e₁ ▸ (@IsOpenImmersion.comp _ _ _ _ _ i₁ ie)
  have o₂ : IsOpenImmersion u₂ := e₂ ▸ (@IsOpenImmersion.comp _ _ _ _ _ i₂ ie)
  have : IsZariskiLocalAtSource @Smooth := HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_openCover (P := @Smooth) (coprodOpenCover.{0, 0} X₁ X₂) ?_
  rintro (_ | _)
  · show Smooth (Limits.coprod.inl ≫ Limits.coprod.desc (x₁ ≫ u₁) (x₂ ≫ u₂))
    rw [Limits.coprod.inl_desc]; infer_instance
  · show Smooth (Limits.coprod.inr ≫ Limits.coprod.desc (x₁ ≫ u₁) (x₂ ≫ u₂))
    rw [Limits.coprod.inr_desc]; infer_instance

end GlobalTheory.ProdGlue
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothCoprodDescOfSmoothPiecesStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_coprodDesc_of_smooth_pieces : ∀ {S S₁ S₂ X₁ X₂ : Scheme.{0}} (u₁ : S₁ ⟶ S) (u₂ : S₂ ⟶ S), Nonempty (Limits.IsColimit (Limits.BinaryCofan.mk u₁ u₂)) → ∀ (x₁ : X₁ ⟶ S₁) (x₂ : X₂ ⟶ S₂), Smooth x₁ → Smooth x₂ → Smooth (Limits.coprod.desc (x₁ ≫ u₁) (x₂ ≫ u₂)) := by
  first | exact @GlobalTheory.ProdGlue.smooth_desc_of_isColimit | exact GlobalTheory.ProdGlue.smooth_desc_of_isColimit | (intros; apply GlobalTheory.ProdGlue.smooth_desc_of_isColimit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackCoprodDescOfPiecesOverCoprod
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackCoprodDescOfPiecesOverCoprod
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem isPullback_coprod_desc_of_pieces : ∀ {S S₁ S₂ T T₁ T₂ : Scheme.{0}} (u₁ : S₁ ⟶ S) (u₂ : S₂ ⟶ S), Nonempty (Limits.IsColimit (Limits.BinaryCofan.mk u₁ u₂)) → ∀ (v₁ : T₁ ⟶ T) (v₂ : T₂ ⟶ T), Nonempty (Limits.IsColimit (Limits.BinaryCofan.mk v₁ v₂)) → ∀ (f : T ⟶ S) (f₁ : T₁ ⟶ S₁) (f₂ : T₂ ⟶ S₂), IsPullback v₁ f₁ f u₁ → IsPullback v₂ f₂ f u₂ → ∀ {X₁ X₂ Y Y₁ Y₂ : Scheme.{0}} (x₁ : X₁ ⟶ S₁) (x₂ : X₂ ⟶ S₂) (y : Y ⟶ T) (y₁ : Y₁ ⟶ T₁) (y₂ : Y₂ ⟶ T₂) (j₁ : Y₁ ⟶ Y) (j₂ : Y₂ ⟶ Y) (i₁ : Y₁ ⟶ X₁) (i₂ : Y₂ ⟶ X₂), IsPullback j₁ y₁ y v₁ → IsPullback j₂ y₂ y v₂ → IsPullback i₁ y₁ x₁ f₁ → IsPullback i₂ y₂ x₂ f₂ → ∃ i : Y ⟶ X₁ ⨿ X₂, j₁ ≫ i = i₁ ≫ Limits.coprod.inl ∧ j₂ ≫ i = i₂ ≫ Limits.coprod.inr ∧ IsPullback i y (Limits.coprod.desc (x₁ ≫ u₁) (x₂ ≫ u₂)) f := by
  intro S S₁ S₂ T T₁ T₂ u₁ u₂ hS v₁ v₂ hT f f₁ f₂ hf₁ hf₂ X₁ X₂ Y Y₁ Y₂ x₁ x₂ y y₁ y₂ j₁ j₂ i₁ i₂
    hj₁ hj₂ hi₁ hi₂
  obtain ⟨hS⟩ := hS
  obtain ⟨hT⟩ := hT
  obtain ⟨hY⟩ := ((CategoryTheory.BinaryCofan.isVanKampen_iff _).mp (FinitaryExtensive.vanKampen _ hT) (Limits.BinaryCofan.mk j₁ j₂) y₁ y₂ y hj₁.w.symm hj₂.w.symm).mpr ⟨hj₁, hj₂⟩
  let x : X₁ ⨿ X₂ ⟶ S := Limits.coprod.desc (x₁ ≫ u₁) (x₂ ≫ u₂)
  obtain ⟨hX₁, hX₂⟩ := ((CategoryTheory.BinaryCofan.isVanKampen_iff _).mp (FinitaryExtensive.vanKampen _ hS) (Limits.BinaryCofan.mk (Limits.coprod.inl : X₁ ⟶ X₁ ⨿ X₂)
    Limits.coprod.inr) x₁ x₂ x (Limits.coprod.inl_desc _ _).symm (Limits.coprod.inr_desc _ _).symm).mp ⟨Limits.coprodIsCoprod X₁ X₂⟩
  obtain ⟨i, hi₁', hi₂'⟩ := Limits.BinaryCofan.IsColimit.desc' hY
    (i₁ ≫ Limits.coprod.inl) (i₂ ≫ Limits.coprod.inr)
  have e₁ : j₁ ≫ i = i₁ ≫ Limits.coprod.inl := hi₁'
  have e₂ : j₂ ≫ i = i₂ ≫ Limits.coprod.inr := hi₂'
  refine ⟨i, e₁, e₂, ?_⟩
  have H₁ : IsPullback (j₁ ≫ i) y₁ x (v₁ ≫ f) := by
    rw [e₁, hf₁.w]; exact hi₁.paste_horiz hX₁
  have H₂ : IsPullback (j₂ ≫ i) y₂ x (v₂ ≫ f) := by
    rw [e₂, hf₂.w]; exact hi₂.paste_horiz hX₂
  have w : i ≫ x = y ≫ f := by
    refine Limits.BinaryCofan.IsColimit.hom_ext hY ?_ ?_
    · change j₁ ≫ i ≫ x = j₁ ≫ y ≫ f
      rw [← Category.assoc j₁ i x, H₁.w, ← Category.assoc j₁ y f, hj₁.w, Category.assoc]
    · change j₂ ≫ i ≫ x = j₂ ≫ y ≫ f
      rw [← Category.assoc j₂ i x, H₂.w, ← Category.assoc j₂ y f, hj₂.w, Category.assoc]
  let c : Y ⟶ Limits.pullback x f := Limits.pullback.lift i y w
  have hcf : c ≫ Limits.pullback.fst x f = i := Limits.pullback.lift_fst _ _ _
  have hcs : c ≫ Limits.pullback.snd x f = y := Limits.pullback.lift_snd _ _ _
  have Q₁ : IsPullback (j₁ ≫ c) y₁ (Limits.pullback.snd x f) v₁ :=
    IsPullback.of_right (by rw [Category.assoc, hcf]; exact H₁)
      (by rw [Category.assoc, hcs]; exact hj₁.w)
      (IsPullback.of_hasPullback x f)
  have Q₂ : IsPullback (j₂ ≫ c) y₂ (Limits.pullback.snd x f) v₂ :=
    IsPullback.of_right (by rw [Category.assoc, hcf]; exact H₂)
      (by rw [Category.assoc, hcs]; exact hj₂.w)
      (IsPullback.of_hasPullback x f)
  obtain ⟨hP⟩ := ((CategoryTheory.BinaryCofan.isVanKampen_iff _).mp (FinitaryExtensive.vanKampen _ hT) (Limits.BinaryCofan.mk (j₁ ≫ c) (j₂ ≫ c)) y₁ y₂ (Limits.pullback.snd x f)
    Q₁.w.symm Q₂.w.symm).mpr ⟨Q₁, Q₂⟩
  have hc : c = (hY.coconePointUniqueUpToIso hP).hom := by
    refine Limits.BinaryCofan.IsColimit.hom_ext hY ?_ ?_
    · exact (hY.comp_coconePointUniqueUpToIso_hom hP ⟨.left⟩).symm
    · exact (hY.comp_coconePointUniqueUpToIso_hom hP ⟨.right⟩).symm
  haveI : IsIso c := by rw [hc]; exact Iso.isIso_hom _
  exact IsPullback.of_iso_pullback ⟨w⟩ (asIso c) hcf hcs

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackCoprodDescOfPiecesOverCoprodStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPullback_coprodDesc_of_pieces_over_coprod : ∀ {S S₁ S₂ T T₁ T₂ : Scheme.{0}} (u₁ : S₁ ⟶ S) (u₂ : S₂ ⟶ S), Nonempty (Limits.IsColimit (Limits.BinaryCofan.mk u₁ u₂)) → ∀ (v₁ : T₁ ⟶ T) (v₂ : T₂ ⟶ T), Nonempty (Limits.IsColimit (Limits.BinaryCofan.mk v₁ v₂)) → ∀ (f : T ⟶ S) (f₁ : T₁ ⟶ S₁) (f₂ : T₂ ⟶ S₂), IsPullback v₁ f₁ f u₁ → IsPullback v₂ f₂ f u₂ → ∀ {X₁ X₂ Y Y₁ Y₂ : Scheme.{0}} (x₁ : X₁ ⟶ S₁) (x₂ : X₂ ⟶ S₂) (y : Y ⟶ T) (y₁ : Y₁ ⟶ T₁) (y₂ : Y₂ ⟶ T₂) (j₁ : Y₁ ⟶ Y) (j₂ : Y₂ ⟶ Y) (i₁ : Y₁ ⟶ X₁) (i₂ : Y₂ ⟶ X₂), IsPullback j₁ y₁ y v₁ → IsPullback j₂ y₂ y v₂ → IsPullback i₁ y₁ x₁ f₁ → IsPullback i₂ y₂ x₂ f₂ → ∃ i : Y ⟶ X₁ ⨿ X₂, j₁ ≫ i = i₁ ≫ Limits.coprod.inl ∧ j₂ ≫ i = i₂ ≫ Limits.coprod.inr ∧ IsPullback i y (Limits.coprod.desc (x₁ ≫ u₁) (x₂ ≫ u₂)) f := by
  first | exact @GlobalTheory.isPullback_coprod_desc_of_pieces | exact GlobalTheory.isPullback_coprod_desc_of_pieces | (intros; apply GlobalTheory.isPullback_coprod_desc_of_pieces <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsColimitSpecQuotientComplementaryIdempotents
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsColimitSpecQuotientComplementaryIdempotents
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open Limits

theorem specQuotIdemCoprod_bij (R : Type) [CommRing R] (e e' : R) (he : IsIdempotentElem e)
    (hs : e + e' = 1) :
    Function.Bijective ((Ideal.Quotient.mk (Ideal.span {e})).prod
      (Ideal.Quotient.mk (Ideal.span {e'}))) := by
  have he' : e' = 1 - e := by rw [← hs]; ring
  have hee : e * e' = 0 := by rw [he', mul_sub, _root_.mul_one, he.eq, sub_self]
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    simp only [RingHom.prod_apply, Prod.mk_eq_zero, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.mem_span_singleton'] at hx
    obtain ⟨⟨a, rfl⟩, ⟨b, hb⟩⟩ := hx
    have h1 : a * e * e' = 0 := by rw [_root_.mul_assoc, hee, mul_zero]
    have h2 : a * e * e = 0 := by
      rw [← hb, _root_.mul_assoc, mul_comm e' e, hee, mul_zero]
    calc a * e = a * e * (e + e') := by rw [hs, _root_.mul_one]
      _ = 0 := by rw [mul_add, h1, h2, add_zero]
  · rintro ⟨x, y⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨a * e' + b * e, ?_⟩
    simp only [RingHom.prod_apply, Prod.mk.injEq]
    constructor
    · rw [Ideal.Quotient.eq, Ideal.mem_span_singleton']
      exact ⟨b - a, by rw [he']; ring⟩
    · rw [Ideal.Quotient.eq, Ideal.mem_span_singleton']
      exact ⟨a - b, by rw [he']; ring⟩

theorem specQuotIdemCoprod : ∀ (R : Type) [CommRing R] (e e' : R), IsIdempotentElem e → e + e' = 1 → Nonempty (Limits.IsColimit (Limits.BinaryCofan.mk (spMap (Ideal.Quotient.mk (Ideal.span {e}))) (spMap (Ideal.Quotient.mk (Ideal.span {e'}))))) := by
  intro R _ e e' he hs
  let A := R ⧸ Ideal.span {e}
  let B := R ⧸ Ideal.span {e'}
  let φ : R →+* A × B := (Ideal.Quotient.mk (Ideal.span {e})).prod
      (Ideal.Quotient.mk (Ideal.span {e'}))
  have hφ : Function.Bijective φ := specQuotIdemCoprod_bij R e e' he hs
  let ψ : R ≃+* A × B := RingEquiv.ofBijective φ hφ
  let g : Spec (CommRingCat.of A) ⨿ Spec (CommRingCat.of B) ⟶ Sp R :=
    coprodSpec A B ≫ Spec.map (CommRingCat.ofHom φ)
  haveI : IsIso (Spec.map (CommRingCat.ofHom φ)) := by
    have : IsIso (CommRingCat.ofHom φ) := by
      change IsIso (RingEquiv.toCommRingCatIso ψ).hom
      infer_instance
    infer_instance
  haveI : IsIso g := by dsimp only [g]; infer_instance
  let i := asIso g
  refine ⟨IsColimit.ofIsoColimit (coprodIsCoprod (Spec (CommRingCat.of A)) (Spec (CommRingCat.of B)))
    (Cocone.ext i ?_)⟩
  rintro ⟨⟨⟩⟩
  · simp only [i, asIso_hom, g]
    show coprod.inl ≫ coprodSpec A B ≫ _ = spMap _
    rw [coprodSpec_inl_assoc, ← Spec.map_comp]
    rfl
  · simp only [i, asIso_hom, g]
    show coprod.inr ≫ coprodSpec A B ≫ _ = spMap _
    rw [coprodSpec_inr_assoc, ← Spec.map_comp]
    rfl

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsColimitSpecQuotientComplementaryIdempotentsStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isColimit_spec_quotient_complementary_idempotents : ∀ (R : Type) [CommRing R] (e e' : R), IsIdempotentElem e → e + e' = 1 → Nonempty (Limits.IsColimit (Limits.BinaryCofan.mk (spMap (Ideal.Quotient.mk (Ideal.span {e}))) (spMap (Ideal.Quotient.mk (Ideal.span {e'}))))) := by
  first | exact @GlobalTheory.specQuotIdemCoprod | exact GlobalTheory.specQuotIdemCoprod | (intros; apply GlobalTheory.specQuotIdemCoprod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupLawGlueOverCoprodBase
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupLawGlueOverCoprodBase
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ProdGlue

variable {T T₁ : Scheme.{0}}

theorem isPb (Y : Over T) : IsPullback (fst Y Y).left (snd Y Y).left Y.hom Y.hom :=
  IsPullback.of_hasPullback Y.hom Y.hom

theorem tens_hom (Y : Over T) : (Y ⊗ Y).hom = (fst Y Y).left ≫ Y.hom := (Over.w (fst Y Y)).symm

noncomputable def incl (v : T₁ ⟶ T) (Y : Over T) (Y₁ : Over T₁) (j : Y₁.left ⟶ Y.left)
    (w : j ≫ Y.hom = Y₁.hom ≫ v) : (Y₁ ⊗ Y₁).left ⟶ (Y ⊗ Y).left :=
  (isPb Y).lift ((fst Y₁ Y₁).left ≫ j) ((snd Y₁ Y₁).left ≫ j) (by
    rw [Category.assoc, Category.assoc, w, ← Category.assoc, ← Category.assoc, (isPb Y₁).w])

@[reassoc (attr := simp)] theorem incl_fst (v : T₁ ⟶ T) (Y : Over T) (Y₁ : Over T₁) (j : Y₁.left ⟶ Y.left)
    (w : j ≫ Y.hom = Y₁.hom ≫ v) : incl v Y Y₁ j w ≫ (fst Y Y).left = (fst Y₁ Y₁).left ≫ j :=
  (isPb Y).lift_fst _ _ _

@[reassoc (attr := simp)] theorem incl_snd (v : T₁ ⟶ T) (Y : Over T) (Y₁ : Over T₁) (j : Y₁.left ⟶ Y.left)
    (w : j ≫ Y.hom = Y₁.hom ≫ v) : incl v Y Y₁ j w ≫ (snd Y Y).left = (snd Y₁ Y₁).left ≫ j :=
  (isPb Y).lift_snd _ _ _

theorem incl_pullback (v : T₁ ⟶ T) (Y : Over T) (Y₁ : Over T₁) (j : Y₁.left ⟶ Y.left)
    (h : IsPullback j Y₁.hom Y.hom v) :
    IsPullback (incl v Y Y₁ j h.w) (Y₁ ⊗ Y₁).hom (Y ⊗ Y).hom v := by
  have w : incl v Y Y₁ j h.w ≫ (Y ⊗ Y).hom = (Y₁ ⊗ Y₁).hom ≫ v := by
    rw [tens_hom, tens_hom, incl_fst_assoc, h.w, Category.assoc]
  have e1 : ∀ s : Limits.PullbackCone (Y ⊗ Y).hom v, (s.fst ≫ (fst Y Y).left) ≫ Y.hom = s.snd ≫ v := fun s => by
    rw [Category.assoc, ← tens_hom, s.condition]
  have e2 : ∀ s : Limits.PullbackCone (Y ⊗ Y).hom v, (s.fst ≫ (snd Y Y).left) ≫ Y.hom = s.snd ≫ v := fun s => by
    rw [Category.assoc, ← (isPb Y).w, ← tens_hom, s.condition]
  let lf : ∀ s : Limits.PullbackCone (Y ⊗ Y).hom v, s.pt ⟶ (Y₁ ⊗ Y₁).left := fun s =>
    (isPb Y₁).lift (h.lift (s.fst ≫ (fst Y Y).left) s.snd (e1 s)) (h.lift (s.fst ≫ (snd Y Y).left) s.snd (e2 s))
      (by rw [h.lift_snd, h.lift_snd])
  have lf1 : ∀ s, lf s ≫ (fst Y₁ Y₁).left = h.lift (s.fst ≫ (fst Y Y).left) s.snd (e1 s) :=
    fun s => (isPb Y₁).lift_fst _ _ _
  have lf2 : ∀ s, lf s ≫ (snd Y₁ Y₁).left = h.lift (s.fst ≫ (snd Y Y).left) s.snd (e2 s) :=
    fun s => (isPb Y₁).lift_snd _ _ _
  refine ⟨⟨w⟩, ⟨Limits.PullbackCone.IsLimit.mk w lf ?_ ?_ ?_⟩⟩
  · intro s
    apply (isPb Y).hom_ext
    · rw [Category.assoc, incl_fst, reassoc_of% (lf1 s), h.lift_fst]
    · rw [Category.assoc, incl_snd, reassoc_of% (lf2 s), h.lift_fst]
  · intro s
    rw [tens_hom Y₁, reassoc_of% (lf1 s), h.lift_snd]
  · intro s m hm1 hm2
    rw [tens_hom Y₁] at hm2
    apply (isPb Y₁).hom_ext
    · rw [lf1]
      apply h.hom_ext
      · rw [h.lift_fst, Category.assoc, ← incl_fst v Y Y₁ j h.w, reassoc_of% hm1]
      · rw [h.lift_snd]; simpa only [Category.assoc] using hm2
    · rw [lf2]
      apply h.hom_ext
      · rw [h.lift_fst, Category.assoc, ← incl_snd v Y Y₁ j h.w, reassoc_of% hm1]
      · rw [h.lift_snd, ← hm2, Category.assoc, (isPb Y₁).w]

theorem incl_mul (f : T₁ ⟶ T) (A : Over T) [GrpObj A] (B : Over T₁) [GrpObj B] (φ : B.left ⟶ A.left)
    (h : IsGrpPullback B A f φ) : incl f A B φ h.1.w ≫ (μ[A]).left = (μ[B]).left ≫ φ := by
  let x₀ : Over.mk ((B ⊗ B).hom ≫ f) ⟶ A := Over.homMk ((fst B B).left ≫ φ) (by
    show _ = (B ⊗ B).hom ≫ f
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w])
  let y₀ : Over.mk ((B ⊗ B).hom ≫ f) ⟶ A := Over.homMk ((snd B B).left ≫ φ) (by
    show _ = (B ⊗ B).hom ≫ f
    rw [Category.assoc, h.1.w, ← Category.assoc, ← (isPb B).w, Over.w])
  have hm := h.2 (B ⊗ B) (fst B B) (snd B B) x₀ y₀ rfl rfl
  rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp, Over.comp_left] at hm
  have e : incl f A B φ h.1.w = (lift x₀ y₀).left := by
    apply (isPb A).hom_ext
    · rw [incl_fst, ← Over.comp_left, lift_fst]; rfl
    · rw [incl_snd, ← Over.comp_left, lift_snd]; rfl
  rw [e]; exact hm

theorem colim_of_pullbacks {T T₁ T₂ : Scheme.{0}} (v₁ : T₁ ⟶ T) (v₂ : T₂ ⟶ T)
    (hT : Limits.IsColimit (Limits.BinaryCofan.mk v₁ v₂)) (Y : Over T) (Y₁ : Over T₁) (Y₂ : Over T₂)
    (j₁ : Y₁.left ⟶ Y.left) (j₂ : Y₂.left ⟶ Y.left)
    (h₁ : IsPullback j₁ Y₁.hom Y.hom v₁) (h₂ : IsPullback j₂ Y₂.hom Y.hom v₂) :
    Nonempty (Limits.IsColimit (Limits.BinaryCofan.mk (incl v₁ Y Y₁ j₁ h₁.w) (incl v₂ Y Y₂ j₂ h₂.w))) := by
  refine (((BinaryCofan.isVanKampen_iff _).1 (FinitaryExtensive.vanKampen _ hT)
    (Limits.BinaryCofan.mk (incl v₁ Y Y₁ j₁ h₁.w) (incl v₂ Y Y₂ j₂ h₂.w)) (Y₁ ⊗ Y₁).hom (Y₂ ⊗ Y₂).hom (Y ⊗ Y).hom
    ?_ ?_).2 ⟨incl_pullback v₁ Y Y₁ j₁ h₁, incl_pullback v₂ Y Y₂ j₂ h₂⟩)
  · exact (incl_pullback v₁ Y Y₁ j₁ h₁).w.symm
  · exact (incl_pullback v₂ Y Y₂ j₂ h₂).w.symm

end GlobalTheory.ProdGlue

open GlobalTheory.ProdGlue in
theorem GlobalTheory.ProdGlue.mul_glue : ∀ {S S₁ S₂ T T₁ T₂ : Scheme.{0}} (u₁ : S₁ ⟶ S) (u₂ : S₂ ⟶ S), Nonempty (Limits.IsColimit (Limits.BinaryCofan.mk u₁ u₂)) → ∀ (v₁ : T₁ ⟶ T) (v₂ : T₂ ⟶ T), Nonempty (Limits.IsColimit (Limits.BinaryCofan.mk v₁ v₂)) → ∀ (f₁ : T₁ ⟶ S₁) (f₂ : T₂ ⟶ S₂) (A₁ : Over S₁) [GrpObj A₁] (A₂ : Over S₂) [GrpObj A₂] (B₁ : Over T₁) [GrpObj B₁] (B₂ : Over T₂) [GrpObj B₂] (A₀ : Over T) [GrpObj A₀] (i₁ : B₁.left ⟶ A₁.left) (i₂ : B₂.left ⟶ A₂.left) (j₁ : B₁.left ⟶ A₀.left) (j₂ : B₂.left ⟶ A₀.left), IsGrpPullback B₁ A₁ f₁ i₁ → IsGrpPullback B₂ A₂ f₂ i₂ → IsGrpPullback B₁ A₀ v₁ j₁ → IsGrpPullback B₂ A₀ v₂ j₂ → ∀ (i : A₀.left ⟶ A₁.left ⨿ A₂.left), j₁ ≫ i = i₁ ≫ Limits.coprod.inl → j₂ ≫ i = i₂ ≫ Limits.coprod.inr → ∃ m : Over.mk (Limits.coprod.desc (A₁.hom ≫ u₁) (A₂.hom ≫ u₂)) ⊗ Over.mk (Limits.coprod.desc (A₁.hom ≫ u₁) (A₂.hom ≫ u₂)) ⟶ Over.mk (Limits.coprod.desc (A₁.hom ≫ u₁) (A₂.hom ≫ u₂)), ∀ l : (A₀ ⊗ A₀).left ⟶ (Over.mk (Limits.coprod.desc (A₁.hom ≫ u₁) (A₂.hom ≫ u₂)) ⊗ Over.mk (Limits.coprod.desc (A₁.hom ≫ u₁) (A₂.hom ≫ u₂))).left, l ≫ (fst (Over.mk (Limits.coprod.desc (A₁.hom ≫ u₁) (A₂.hom ≫ u₂))) (Over.mk (Limits.coprod.desc (A₁.hom ≫ u₁) (A₂.hom ≫ u₂)))).left = (fst A₀ A₀).left ≫ i → l ≫ (snd (Over.mk (Limits.coprod.desc (A₁.hom ≫ u₁) (A₂.hom ≫ u₂))) (Over.mk (Limits.coprod.desc (A₁.hom ≫ u₁) (A₂.hom ≫ u₂)))).left = (snd A₀ A₀).left ≫ i → l ≫ m.left = (μ[A₀]).left ≫ i := by

  intro S S₁ S₂ T T₁ T₂ u₁ u₂ ⟨hS⟩ v₁ v₂ ⟨hT⟩ f₁ f₂ A₁ _ A₂ _ B₁ _ B₂ _ A₀ _ i₁ i₂ j₁ j₂ hi₁ hi₂ hj₁ hj₂ i ei₁ ei₂
  set X := Over.mk (Limits.coprod.desc (A₁.hom ≫ u₁) (A₂.hom ≫ u₂)) with hX
  have hV := (BinaryCofan.isVanKampen_iff _).1 (FinitaryExtensive.vanKampen _ hS)
    (Limits.BinaryCofan.mk (Limits.coprod.inl : A₁.left ⟶ A₁.left ⨿ A₂.left) Limits.coprod.inr) A₁.hom A₂.hom X.hom
    (Limits.coprod.inl_desc _ _).symm (Limits.coprod.inr_desc _ _).symm
  have pX : _ := hV.1 ⟨Limits.coprodIsCoprod _ _⟩
  have pX₁ : IsPullback (Limits.coprod.inl : A₁.left ⟶ A₁.left ⨿ A₂.left) A₁.hom X.hom u₁ := pX.1
  have pX₂ : IsPullback (Limits.coprod.inr : A₂.left ⟶ A₁.left ⨿ A₂.left) A₂.hom X.hom u₂ := pX.2
  obtain ⟨cX⟩ := colim_of_pullbacks u₁ u₂ hS X A₁ A₂ _ _ pX₁ pX₂
  obtain ⟨c0⟩ := colim_of_pullbacks v₁ v₂ hT A₀ B₁ B₂ _ _ hj₁.1 hj₂.1
  have D := Limits.BinaryCofan.IsColimit.desc' cX
    ((μ[A₁]).left ≫ Limits.coprod.inl) ((μ[A₂]).left ≫ Limits.coprod.inr)
  let ml : (X ⊗ X).left ⟶ X.left := D.1
  have hm₁ : incl u₁ X A₁ Limits.coprod.inl pX₁.w ≫ ml = (μ[A₁]).left ≫ Limits.coprod.inl := D.2.1
  have hm₂ : incl u₂ X A₂ Limits.coprod.inr pX₂.w ≫ ml = (μ[A₂]).left ≫ Limits.coprod.inr := D.2.2
  have hw : ml ≫ X.hom = (X ⊗ X).hom := by
    apply Limits.BinaryCofan.IsColimit.hom_ext cX
    · change incl u₁ X A₁ Limits.coprod.inl pX₁.w ≫ ml ≫ X.hom = incl u₁ X A₁ Limits.coprod.inl pX₁.w ≫ (X ⊗ X).hom
      rw [← Category.assoc, hm₁, Category.assoc, tens_hom, incl_fst_assoc]
      simp only [X, Over.mk_hom, Limits.coprod.inl_desc]
      rw [← Category.assoc, Over.w, ← Category.assoc, Over.w]
    · change incl u₂ X A₂ Limits.coprod.inr pX₂.w ≫ ml ≫ X.hom = incl u₂ X A₂ Limits.coprod.inr pX₂.w ≫ (X ⊗ X).hom
      rw [← Category.assoc, hm₂, Category.assoc, tens_hom, incl_fst_assoc]
      simp only [X, Over.mk_hom, Limits.coprod.inr_desc]
      rw [← Category.assoc, Over.w, ← Category.assoc, Over.w]
  refine ⟨Over.homMk ml hw, fun l hl₁ hl₂ => ?_⟩
  change l ≫ ml = _
  have key : ∀ {Tk Sk : Scheme.{0}} (vk : Tk ⟶ T) (uk : Sk ⟶ S) (fk : Tk ⟶ Sk) (Ak : Over Sk) [GrpObj Ak]
      (Bk : Over Tk) [GrpObj Bk] (ik : Bk.left ⟶ Ak.left) (jk : Bk.left ⟶ A₀.left) (ink : Ak.left ⟶ X.left)
      (hik : IsGrpPullback Bk Ak fk ik) (hjk : IsGrpPullback Bk A₀ vk jk) (eik : jk ≫ i = ik ≫ ink)
      (κ : (Ak ⊗ Ak).left ⟶ (X ⊗ X).left)
      (κf : κ ≫ (fst X X).left = (fst Ak Ak).left ≫ ink) (κs : κ ≫ (snd X X).left = (snd Ak Ak).left ≫ ink)
      (hmk : κ ≫ ml = (μ[Ak]).left ≫ ink),
      incl vk A₀ Bk jk hjk.1.w ≫ l ≫ ml = incl vk A₀ Bk jk hjk.1.w ≫ (μ[A₀]).left ≫ i := by
    intro Tk Sk vk uk fk Ak _ Bk _ ik jk ink hik hjk eik κ κf κs hmk
    have e : incl vk A₀ Bk jk hjk.1.w ≫ l = incl fk Ak Bk ik hik.1.w ≫ κ := by
      apply (isPb X).hom_ext
      · rw [Category.assoc, hl₁, incl_fst_assoc, eik, Category.assoc, κf, incl_fst_assoc]
      · rw [Category.assoc, hl₂, incl_snd_assoc, eik, Category.assoc, κs, incl_snd_assoc]
    rw [reassoc_of% e, hmk, reassoc_of% (incl_mul fk Ak Bk ik hik), reassoc_of% (incl_mul vk A₀ Bk jk hjk), eik]
  apply Limits.BinaryCofan.IsColimit.hom_ext c0
  · exact key v₁ u₁ f₁ A₁ B₁ i₁ j₁ _ hi₁ hj₁ ei₁ _ (incl_fst _ _ _ _ _) (incl_snd _ _ _ _ _) hm₁
  · exact key v₂ u₂ f₂ A₂ B₂ i₂ j₂ _ hi₂ hj₂ ei₂ _ (incl_fst _ _ _ _ _) (incl_snd _ _ _ _ _) hm₂
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupLawGlueOverCoprodBaseStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.groupLaw_glue_over_coprod_base : ∀ {S S₁ S₂ T T₁ T₂ : Scheme.{0}} (u₁ : S₁ ⟶ S) (u₂ : S₂ ⟶ S), Nonempty (Limits.IsColimit (Limits.BinaryCofan.mk u₁ u₂)) → ∀ (v₁ : T₁ ⟶ T) (v₂ : T₂ ⟶ T), Nonempty (Limits.IsColimit (Limits.BinaryCofan.mk v₁ v₂)) → ∀ (f₁ : T₁ ⟶ S₁) (f₂ : T₂ ⟶ S₂) (A₁ : Over S₁) [GrpObj A₁] (A₂ : Over S₂) [GrpObj A₂] (B₁ : Over T₁) [GrpObj B₁] (B₂ : Over T₂) [GrpObj B₂] (A₀ : Over T) [GrpObj A₀] (i₁ : B₁.left ⟶ A₁.left) (i₂ : B₂.left ⟶ A₂.left) (j₁ : B₁.left ⟶ A₀.left) (j₂ : B₂.left ⟶ A₀.left), IsGrpPullback B₁ A₁ f₁ i₁ → IsGrpPullback B₂ A₂ f₂ i₂ → IsGrpPullback B₁ A₀ v₁ j₁ → IsGrpPullback B₂ A₀ v₂ j₂ → ∀ (i : A₀.left ⟶ A₁.left ⨿ A₂.left), j₁ ≫ i = i₁ ≫ Limits.coprod.inl → j₂ ≫ i = i₂ ≫ Limits.coprod.inr → ∃ m : Over.mk (Limits.coprod.desc (A₁.hom ≫ u₁) (A₂.hom ≫ u₂)) ⊗ Over.mk (Limits.coprod.desc (A₁.hom ≫ u₁) (A₂.hom ≫ u₂)) ⟶ Over.mk (Limits.coprod.desc (A₁.hom ≫ u₁) (A₂.hom ≫ u₂)), ∀ l : (A₀ ⊗ A₀).left ⟶ (Over.mk (Limits.coprod.desc (A₁.hom ≫ u₁) (A₂.hom ≫ u₂)) ⊗ Over.mk (Limits.coprod.desc (A₁.hom ≫ u₁) (A₂.hom ≫ u₂))).left, l ≫ (fst (Over.mk (Limits.coprod.desc (A₁.hom ≫ u₁) (A₂.hom ≫ u₂))) (Over.mk (Limits.coprod.desc (A₁.hom ≫ u₁) (A₂.hom ≫ u₂)))).left = (fst A₀ A₀).left ≫ i → l ≫ (snd (Over.mk (Limits.coprod.desc (A₁.hom ≫ u₁) (A₂.hom ≫ u₂))) (Over.mk (Limits.coprod.desc (A₁.hom ≫ u₁) (A₂.hom ≫ u₂)))).left = (snd A₀ A₀).left ≫ i → l ≫ m.left = (μ[A₀]).left ≫ i := by
  first | exact @GlobalTheory.ProdGlue.mul_glue | exact GlobalTheory.ProdGlue.mul_glue | (intros; apply GlobalTheory.ProdGlue.mul_glue <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackSpMapQuotientSpanBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackSpMapQuotientSpanBaseChange
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.QuotBaseChange

theorem isPushout_quot_span (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀) (f : R)
    (ρ : R ⧸ Ideal.span {f} →+* R₀ ⧸ Ideal.span {π f})
    (hρ : ρ.comp (Ideal.Quotient.mk _) = (Ideal.Quotient.mk _).comp π) :
    IsPushout (CommRingCat.ofHom π) (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f})))
      (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {π f}))) (CommRingCat.ofHom ρ) := by
  refine ⟨⟨by ext a; exact (congr($hρ a)).symm⟩, ⟨Limits.PushoutCocone.IsColimit.mk _
    (fun s => CommRingCat.ofHom (Ideal.Quotient.lift (Ideal.span {π f}) s.inl.hom ?_)) ?_ ?_ ?_⟩⟩
  · intro b hb
    have e : ∀ a, s.inl.hom (π a) = s.inr.hom (Ideal.Quotient.mk _ a) := fun a => congr($(s.condition) a)
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hb
    rw [map_mul, e, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self f), map_zero, mul_zero]
  · intro s
    ext b
    rfl
  · intro s
    ext a
    have e : s.inl.hom (π a) = s.inr.hom (Ideal.Quotient.mk _ a) := congr($(s.condition) a)
    have e2 : ρ (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (π a) := congr($hρ a)
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
    rw [e2, Ideal.Quotient.lift_mk, e]
  · intro s m h₁ _
    ext b
    have e : m.hom (Ideal.Quotient.mk _ b) = s.inl.hom b := congr($h₁ b)
    exact e

theorem isPullback_spMap_quot : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀) (f : R) (ρ : R ⧸ Ideal.span {f} →+* R₀ ⧸ Ideal.span {π f}), ρ.comp (Ideal.Quotient.mk _) = (Ideal.Quotient.mk _).comp π → IsPullback (spMap (Ideal.Quotient.mk (Ideal.span {π f}))) (spMap ρ) (spMap π) (spMap (Ideal.Quotient.mk (Ideal.span {f}))) := by
  intro R R₀ _ _ π f ρ hρ
  exact isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_quot_span R R₀ π f ρ hρ)

end GlobalTheory.QuotBaseChange
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackSpMapQuotientSpanBaseChangeStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPullback_spMap_quotient_span_baseChange : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀) (f : R) (ρ : R ⧸ Ideal.span {f} →+* R₀ ⧸ Ideal.span {π f}), ρ.comp (Ideal.Quotient.mk _) = (Ideal.Quotient.mk _).comp π → IsPullback (spMap (Ideal.Quotient.mk (Ideal.span {π f}))) (spMap ρ) (spMap π) (spMap (Ideal.Quotient.mk (Ideal.span {f}))) := by
  first | exact @GlobalTheory.QuotBaseChange.isPullback_spMap_quot | exact GlobalTheory.QuotBaseChange.isPullback_spMap_quot | (intros; apply GlobalTheory.QuotBaseChange.isPullback_spMap_quot <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeLiftOfSplitRing
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbLiftGlue

theorem exists_lift_of_split : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (e : R), IsIdempotentElem e → ∀ (A₀ : Over (Sp R₀)) [GrpObj A₀], IsAbelianScheme A₀ → (∀ f : R, (f = e ∨ f = 1 - e) → ∃ (A : Over (Sp (R ⧸ Ideal.span {f}))) (_ : GrpObj A) (B : Over (Sp (R₀ ⧸ Ideal.span {π f}))) (_ : GrpObj B) (i : B.left ⟶ A.left) (j : B.left ⟶ A₀.left) (ρ : R ⧸ Ideal.span {f} →+* R₀ ⧸ Ideal.span {π f}), ρ.comp (Ideal.Quotient.mk _) = (Ideal.Quotient.mk _).comp π ∧ IsGrpPullback B A (spMap ρ) i ∧ IsGrpPullback B A₀ (spMap (Ideal.Quotient.mk _)) j ∧ IsAbelianScheme A) → ∃ (A : Over (Sp R)) (_ : GrpObj A) (i : A₀.left ⟶ A.left), IsGrpPullback A₀ A (spMap π) i ∧ IsAbelianScheme A := by
  intro R R₀ _ _ I hI π hπ hk e he A₀ _ hA₀ H
  obtain ⟨A₁, gA₁, B₁, gB₁, i₁, j₁, ρ₁, hρ₁, hp₁, hq₁, hab₁⟩ := H e (Or.inl rfl)
  obtain ⟨A₂, gA₂, B₂, gB₂, i₂, j₂, ρ₂, hρ₂, hp₂, hq₂, hab₂⟩ := H (1 - e) (Or.inr rfl)
  have cS := GlobalTheory.T.isColimit_spec_quotient_complementary_idempotents R e (1 - e) he (by ring)
  have cT := GlobalTheory.T.isColimit_spec_quotient_complementary_idempotents R₀ (π e) (π (1 - e)) (he.map π) (by rw [← map_add (f := _)]; simp)
  obtain ⟨i, hi₁, hi₂, hpb⟩ := GlobalTheory.T.isPullback_coprodDesc_of_pieces_over_coprod _ _ cS _ _ cT (spMap π) (spMap ρ₁) (spMap ρ₂) (GlobalTheory.T.isPullback_spMap_quotient_span_baseChange R R₀ π e ρ₁ hρ₁) (GlobalTheory.T.isPullback_spMap_quotient_span_baseChange R R₀ π (1 - e) ρ₂ hρ₂)
    A₁.hom A₂.hom A₀.hom B₁.hom B₂.hom j₁ j₂ i₁ i₂ hq₁.1 hq₂.1 hp₁.1 hp₂.1
  have hsm := GlobalTheory.T.smooth_coprodDesc_of_smooth_pieces _ _ cS A₁.hom A₂.hom hab₁.smooth hab₂.smooth
  set X : Over (Sp R) := Over.mk (Limits.coprod.desc (A₁.hom ≫ spMap (Ideal.Quotient.mk (Ideal.span {e}))) (A₂.hom ≫ spMap (Ideal.Quotient.mk (Ideal.span {1 - e})))) with hX
  obtain ⟨m, hm⟩ := GlobalTheory.T.groupLaw_glue_over_coprod_base _ _ cS _ _ cT (spMap ρ₁) (spMap ρ₂) A₁ A₂ B₁ B₂ A₀ i₁ i₂ j₁ j₂ hp₁ hp₂ hq₁ hq₂ i hi₁ hi₂
  have hnil : IsNilpotent (RingHom.ker π) := ⟨2, by rw [hk, hI]⟩
  have hsm' : Smooth X.hom := hsm
  have hpb' : IsPullback i A₀.hom X.hom (spMap π) := hpb
  obtain ⟨e₁, he₁, he₁'⟩ := GlobalTheory.T.exists_section_lift_smooth_nilpotent_thickening R R₀ π hπ hnil X A₀ i hpb' hsm' (1 : Over.mk (𝟙 (Sp R₀)) ⟶ A₀).left (Over.w _)
  have hw : ∀ g : A₀ ⊗ A₀ ⟶ A₀, (g.left ≫ i) ≫ X.hom = (Over.mk ((A₀ ⊗ A₀).hom ≫ spMap π)).hom := fun g ↦ by
    simp only [Over.mk_hom, Category.assoc, hpb'.w]; rw [← Category.assoc, Over.w]
  let l : Over.mk ((A₀ ⊗ A₀).hom ≫ spMap π) ⟶ X ⊗ X := lift (Over.homMk _ (hw (fst A₀ A₀))) (Over.homMk _ (hw (snd A₀ A₀)))
  have hl₁ : l.left ≫ (fst X X).left = (fst A₀ A₀).left ≫ i := by
    rw [← Over.comp_left, lift_fst]; rfl
  have hl₂ : l.left ≫ (snd X X).left = (snd A₀ A₀).left ≫ i := by
    rw [← Over.comp_left, lift_snd]; rfl
  obtain ⟨g, hg, hab⟩ := GlobalTheory.T.exists_grpObj_isAbelianScheme_smoothLift_nilpotent R R₀ π hπ hnil A₀ hA₀ X i hpb' hsm' e₁ he₁ he₁' l.left hl₁ hl₂ m (hm l.left hl₁ hl₂)
  exact ⟨X, g, i, hg, hab⟩

end GlobalTheory.AbLiftGlue
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeLiftOfSplitRingStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_abelianScheme_lift_of_splitRing : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (e : R), IsIdempotentElem e → ∀ (A₀ : Over (Sp R₀)) [GrpObj A₀], IsAbelianScheme A₀ → (∀ f : R, (f = e ∨ f = 1 - e) → ∃ (A : Over (Sp (R ⧸ Ideal.span {f}))) (_ : GrpObj A) (B : Over (Sp (R₀ ⧸ Ideal.span {π f}))) (_ : GrpObj B) (i : B.left ⟶ A.left) (j : B.left ⟶ A₀.left) (ρ : R ⧸ Ideal.span {f} →+* R₀ ⧸ Ideal.span {π f}), ρ.comp (Ideal.Quotient.mk _) = (Ideal.Quotient.mk _).comp π ∧ IsGrpPullback B A (spMap ρ) i ∧ IsGrpPullback B A₀ (spMap (Ideal.Quotient.mk _)) j ∧ IsAbelianScheme A) → ∃ (A : Over (Sp R)) (_ : GrpObj A) (i : A₀.left ⟶ A.left), IsGrpPullback A₀ A (spMap π) i ∧ IsAbelianScheme A := by
  first | exact @GlobalTheory.AbLiftGlue.exists_lift_of_split | exact GlobalTheory.AbLiftGlue.exists_lift_of_split | (intros; apply GlobalTheory.AbLiftGlue.exists_lift_of_split <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeUnobstructedOfConstantDimension
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DimRed

variable {R R₀ : Type} [CommRing R] [CommRing R₀]

abbrev qmap (π : R →+* R₀) (f : R) : R ⧸ Ideal.span {f} →+* R₀ ⧸ Ideal.span {π f} :=
  Ideal.quotientMap _ π (Ideal.span_le.2 (Set.singleton_subset_iff.2 (by
    rw [SetLike.mem_coe, Ideal.mem_comap]; exact Ideal.mem_span_singleton_self _)))

theorem qmap_facts (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π)
    (hk : RingHom.ker π = I) (f : R) :
    Function.Surjective (qmap π f) ∧ RingHom.ker (qmap π f) = I.map (Ideal.Quotient.mk _) ∧
      (I.map (Ideal.Quotient.mk (Ideal.span {f}))) ^ 2 = 0 ∧
      (qmap π f).comp (Ideal.Quotient.mk _) = (Ideal.Quotient.mk _).comp π := by
  refine ⟨Ideal.quotientMap_surjective hπ, ?_, ?_, Ideal.quotientMap_comp_mk _⟩
  · ext x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [RingHom.mem_ker, Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective]
    constructor
    · intro hx
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hx
      obtain ⟨r, rfl⟩ := hπ c
      refine ⟨x - r * f, ?_, ?_⟩
      · rw [← hk, RingHom.mem_ker, map_sub, map_mul, hc, sub_self]
      · rw [Ideal.Quotient.eq]
        simpa using Ideal.mul_mem_left _ r (Ideal.mem_span_singleton_self f)
    · rintro ⟨y, hy, hyx⟩
      rw [Ideal.Quotient.eq] at hyx
      have h1 : π (y - x) ∈ Ideal.span {π f} := by
        obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hyx
        rw [← hc, map_mul]; exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
      have h2 : π y = 0 := by rw [← RingHom.mem_ker, hk]; exact hy
      rw [map_sub, h2, zero_sub] at h1
      simpa using (Ideal.span {π f}).neg_mem h1
  · rw [← Ideal.map_pow, hI, Ideal.zero_eq_bot, Ideal.map_bot]; exact Ideal.zero_eq_bot.symm

theorem smooth_paste {X Y Z S T : Scheme.{0}} (p : X ⟶ S) (u : Y ⟶ S) (v : Z ⟶ Y) (w : T ⟶ S) (d : Z ⟶ T)
    (hw : d ≫ w = v ≫ u) (g : ℕ) (h : SmoothOfRelativeDimension g (pullback.snd p w)) :
    SmoothOfRelativeDimension g (pullback.snd (pullback.snd p u) v) := by
  have outer := (IsPullback.of_hasPullback (pullback.snd p u) v).paste_horiz (IsPullback.of_hasPullback p u)
  rw [← hw] at outer
  have sq := IsPullback.of_right
    (h₁₁ := pullback.lift (pullback.fst (pullback.snd p u) v ≫ pullback.fst p u)
      (pullback.snd (pullback.snd p u) v ≫ d) (by rw [Category.assoc]; exact outer.w))
    (by rw [pullback.lift_fst]; exact outer) (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback p w)
  exact (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback sq h

theorem smooth_zero_of_subsingleton [Subsingleton R₀] {X : Scheme.{0}} (p : X ⟶ Sp R₀) :
    SmoothOfRelativeDimension 0 p :=
  ⟨fun x ↦ absurd (Subsingleton.elim (⊤ : Ideal R₀) (p x).asIdeal) (p x).isPrime.ne_top.symm⟩

theorem lift_of_split (hU : UnobDim) (n : ℕ) : ∀ (R : Type) [CommRing R] (I : Ideal R), I ^ 2 = 0 →
    ∀ (R₀ : Type) [CommRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I →
    ∀ (A₀ : Over (Sp R₀)) [GrpObj A₀], IsAbelianScheme A₀ → ∀ e : Fin n → R₀, CompleteOrthogonalIdempotents e →
    (∀ k, ∃ g : ℕ, SmoothOfRelativeDimension g
      (pullback.snd A₀.hom (spMap (Ideal.Quotient.mk (Ideal.span {1 - e k}))))) →
    ∃ (A : Over (Sp R)) (_ : GrpObj A) (i : A₀.left ⟶ A.left), IsGrpPullback A₀ A (spMap π) i ∧ IsAbelianScheme A := by
  induction n with
  | zero =>
    intro R _ I hI R₀ _ π hπ hk A₀ _ hA e he _
    have h01 : (0 : R₀) = 1 := by simpa using he.complete
    haveI : Subsingleton R₀ := subsingleton_of_zero_eq_one h01
    exact hU R I hI R₀ π hπ hk A₀ 0 hA (smooth_zero_of_subsingleton _)
  | succ n ih =>
    intro R _ I hI R₀ _ π hπ hk A₀ _ hA e he hsm
    have hnil : ∀ x ∈ RingHom.ker π, IsNilpotent x := fun x hx ↦ ⟨2, by
      rw [hk] at hx
      have h2 := Ideal.pow_mem_pow hx 2
      rw [hI] at h2
      simpa using h2⟩
    obtain ⟨ε, hε, hπε⟩ := exists_isIdempotentElem_eq_of_ker_isNilpotent π hnil (e 0) (hπ _) (he.idem 0)
    refine GlobalTheory.T.exists_abelianScheme_lift_of_splitRing R R₀ I hI π hπ hk ε hε A₀ hA ?_
    intro f hf
    obtain ⟨hρs, hρk, hρ2, hρc⟩ := qmap_facts I hI π hπ hk f
    let B : Over (Sp (R₀ ⧸ Ideal.span {π f})) := (Over.pullback (spMap (Ideal.Quotient.mk _))).obj A₀
    letI : GrpObj B := Functor.grpObjObj
    have hB : IsGrpPullback B A₀ (spMap (Ideal.Quotient.mk _)) (pullback.fst _ _) := isGrpPullback_pullback A₀ _
    have hBa : IsAbelianScheme B := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA hB
    suffices H : ∃ (A : Over (Sp (R ⧸ Ideal.span {f}))) (_ : GrpObj A) (i : B.left ⟶ A.left),
        IsGrpPullback B A (spMap (qmap π f)) i ∧ IsAbelianScheme A by
      obtain ⟨A, _, i, h1, h2⟩ := H
      exact ⟨A, _, B, _, i, pullback.fst _ _, qmap π f, hρc, h1, hB, h2⟩
    rcases hf with rfl | rfl
    · have hm := he.map (Ideal.Quotient.mk (Ideal.span {π f}))
      refine ih (R ⧸ Ideal.span {f}) (I.map (Ideal.Quotient.mk _)) hρ2 (R₀ ⧸ Ideal.span {π f}) (qmap π f) hρs hρk
        B hBa (fun k ↦ Ideal.Quotient.mk _ (e k.succ)) ⟨⟨fun k ↦ hm.idem k.succ,
          fun i j hij ↦ hm.ortho ((Fin.succ_injective _).ne hij)⟩, ?_⟩ ?_
      · have hc := hm.complete
        rw [Fin.sum_univ_succ] at hc
        have h0 : Ideal.Quotient.mk (Ideal.span {π f}) (e 0) = 0 := by
          rw [Ideal.Quotient.eq_zero_iff_mem, ← hπε]; exact Ideal.mem_span_singleton_self _
        simpa [h0] using hc
      · intro k
        obtain ⟨g, hg⟩ := hsm k.succ
        refine ⟨g, smooth_paste A₀.hom _ _ _
          (spMap (Ideal.Quotient.lift (Ideal.span {1 - e k.succ})
            ((Ideal.Quotient.mk (Ideal.span {1 - Ideal.Quotient.mk (Ideal.span {π f}) (e k.succ)})).comp
              (Ideal.Quotient.mk (Ideal.span {π f}))) ?_)) ?_ g hg⟩
        · intro a ha
          obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
          have h0 : (Ideal.Quotient.mk (Ideal.span {1 - Ideal.Quotient.mk (Ideal.span {π f}) (e k.succ)}))
              (Ideal.Quotient.mk (Ideal.span {π f}) (1 - e k.succ)) = 0 := by
            rw [Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one]; exact Ideal.mem_span_singleton_self _
          rw [RingHom.comp_apply, map_mul, map_mul, h0, mul_zero]
        · rw [← Spec.map_comp, ← Spec.map_comp]
          congr 1
    · obtain ⟨g, hg⟩ := hsm 0
      have h1 : π (1 - ε) = 1 - e 0 := by rw [map_sub, map_one, hπε]
      rw [← h1] at hg
      exact hU _ _ hρ2 _ _ hρs hρk B g hBa hg

theorem abelianUnobstructed_of_unobDim : UnobDim → GlobalTheory.Published.AbelianUnobstructed := by
  intro hU R _ I hI R₀ _ π hπ hk A₀ _ hA
  obtain ⟨n, e, he, hsm⟩ := GlobalTheory.T.exists_idempotents_abelianScheme_constant_dimension R₀ A₀ hA
  exact lift_of_split hU n R I hI R₀ π hπ hk A₀ hA e he hsm

end GlobalTheory.DimRed
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeUnobstructedOfConstantDimensionStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianSchemeUnobstructed_of_constantDimension : UnobDim → GlobalTheory.Published.AbelianUnobstructed := by
  first | exact @GlobalTheory.DimRed.abelianUnobstructed_of_unobDim | exact GlobalTheory.DimRed.abelianUnobstructed_of_unobDim | (intros; apply GlobalTheory.DimRed.abelianUnobstructed_of_unobDim <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeGlobalFormsPrimitiveOfFrames
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeGlobalFormsPrimitiveOfFrames
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FormsOnAb

open GlobalTheory.AbCoh

variable {R : Type} [CommRing R] {X : Scheme.{0}}

theorem globalFunctionsConstant_of_constant_after_baseChange (s : X ⟶ Sp R) (hU : UConst s) : CohomZeroIsConstants (OAff s) := by
  refine hU R X s (𝟙 X) ?_
  rw [Algebra.algebraMap_self, Cris.spMap_id]
  exact IsPullback.of_horiz_isIso ⟨by simp⟩

variable {s : X ⟶ Sp R} {n : ℕ} (fr : Frame (OAff s) n) (hc : CohomZeroIsConstants (OAff s))

theorem coboundaryZero_frame_vectorField_globalForm_eq_zero (i : Fin n) (ω : GlobForm s) : d0 (OAff s) (fun T ↦ fr.δ i T (ω.1 T)) = 0 := by
  funext T T' φ
  rw [amitsur_d0_apply, ω.2 φ, fr.nat]
  exact sub_self _

def coef (i : Fin n) (ω : GlobForm s) : R := (hc _ (coboundaryZero_frame_vectorField_globalForm_eq_zero fr i ω)).exists.choose

theorem coef_spec (i : Fin n) (ω : GlobForm s) (T : AffOp X) :
    fr.δ i T (ω.1 T) = algebraMap R ((OAff s).obj T) (coef fr hc i ω) :=
  (hc _ (coboundaryZero_frame_vectorField_globalForm_eq_zero fr i ω)).exists.choose_spec T

theorem coef_eq (i : Fin n) (ω : GlobForm s) (r : R)
    (h : ∀ T, fr.δ i T (ω.1 T) = algebraMap R ((OAff s).obj T) r) : coef fr hc i ω = r :=
  (hc _ (coboundaryZero_frame_vectorField_globalForm_eq_zero fr i ω)).unique (coef_spec fr hc i ω) h

def coefL : GlobForm s →ₗ[R] (Fin n → R) where
  toFun ω i := coef fr hc i ω
  map_add' ω ω' := funext fun i ↦ coef_eq fr hc i _ _ fun T ↦ by
    simp only [Submodule.coe_add, Pi.add_apply, map_add (f := _)]
    rw [coef_spec fr hc i ω T, coef_spec fr hc i ω' T]
  map_smul' r ω := funext fun i ↦ coef_eq fr hc i _ _ fun T ↦ by
    simp only [Submodule.coe_smul, Pi.smul_apply, LinearMap.map_smul_of_tower, RingHom.id_apply,
      smul_eq_mul, map_mul, Algebra.smul_def]
    rw [coef_spec fr hc i ω T]

def sumL : (Fin n → R) →ₗ[R] GlobForm s where
  toFun c := ∑ i, c i • fr.w i
  map_add' c c' := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' r c := by simp [Finset.smul_sum, mul_smul]

theorem sumL_coefL (ω : GlobForm s) : sumL fr (coefL fr hc ω) = ω := by
  apply Subtype.ext
  funext T
  conv_rhs => rw [fr.sum T (ω.1 T)]
  simp only [sumL, coefL, LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_sum, Submodule.coe_smul,
    Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [coef_spec, algebraMap_smul]


include fr hc in
theorem projective : Module.Projective R (GlobForm s) :=
  Module.Projective.of_split (coefL fr hc) (sumL fr) (LinearMap.ext (sumL_coefL fr hc))

def back (U : AffOp X) (x : Ω[Sec s U.unop.1⁄R]) : Sec s U.unop.1 ⊗[R] GlobForm s :=
  ∑ i, (fr.δ i U x : Sec s U.unop.1) ⊗ₜ[R] fr.w i

theorem back_add (U : AffOp X) (x y : Ω[Sec s U.unop.1⁄R]) : back fr U (x + y) = back fr U x + back fr U y := by
  simp only [back, map_add (f := _), TensorProduct.add_tmul, Finset.sum_add_distrib]


include fr hc in
theorem par (U : AffOp X) : IsBaseChange (Sec s U.unop.1) (evForm s U) := by
  change Function.Bijective (TensorProduct.lift _)
  rw [Function.bijective_iff_has_inverse]
  refine ⟨back fr U, fun t ↦ ?_, fun x ↦ ?_⟩
  · induction t using TensorProduct.induction_on with
    | zero => simp [back]
    | tmul a ω =>
      simp only [TensorProduct.lift.tmul, LinearMap.restrictScalars_apply, LinearMap.flip_apply,
        Algebra.linearMap_apply, Module.algebraMap_end_apply, LinearMap.smul_apply]
      conv_rhs => rw [← sumL_coefL fr hc ω]
      simp only [back, sumL, coefL, LinearMap.coe_mk, AddHom.coe_mk, TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [← TensorProduct.smul_tmul]
      congr 1
      change fr.δ i U (a • ω.1 U) = coef fr hc i ω • a
      rw [(fr.δ i U).map_smul a (ω.1 U), coef_spec fr hc i ω U, Algebra.smul_def, mul_comm]
      rfl
    | add t t' ht ht' => rw [map_add (f := _), back_add, ht, ht']
  · conv_rhs => rw [fr.sum U x]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [back, map_sum, TensorProduct.lift.tmul, LinearMap.restrictScalars_apply, LinearMap.flip_apply,
        Algebra.linearMap_apply, Module.algebraMap_end_apply, LinearMap.smul_apply]
    rfl

end GlobalTheory.FormsOnAb

namespace GlobalTheory.FormsOnAb

open GlobalTheory.AbCoh

theorem formSt_of (H : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom →
      GlobalTheory.AbCoh.HasFrame (OAff A.hom) ∧ GlobalTheory.AbCoh.UConst A.hom ∧ GlobalTheory.AbCoh.PrimF A) : FormSt := by
  intro R₀ _ A _ g hA hs
  obtain ⟨⟨n, ⟨fr⟩⟩, hU, hP⟩ := H R₀ A g hA hs
  have hc := globalFunctionsConstant_of_constant_after_baseChange A.hom hU
  refine ⟨fun U ↦ par fr hc U, projective fr hc, fun w wm w₁ w₂ hm h1 h2 ↦ ?_⟩
  rw [hm.eq_pullForm, h1.eq_pullForm, h2.eq_pullForm]
  exact hP w

end GlobalTheory.FormsOnAb
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeGlobalFormsPrimitiveOfFramesStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianSchemeGlobalFormsPrimitive_of_frames : (∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → GlobalTheory.AbCoh.HasFrame (OAff A.hom) ∧ GlobalTheory.AbCoh.UConst A.hom ∧ GlobalTheory.AbCoh.PrimF A) → FormSt := by
  first | exact @GlobalTheory.FormsOnAb.formSt_of | exact GlobalTheory.FormsOnAb.formSt_of | (intros; apply GlobalTheory.FormsOnAb.formSt_of <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeUnobstructedOfCohomologyStructure
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem abelianUnobstructed_of_struct (hO : GlobalTheory.AbCoh.OStr)
    (hF : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
      SmoothOfRelativeDimension g A.hom → GlobalTheory.AbCoh.HasFrame (OAff A.hom) ∧ GlobalTheory.AbCoh.UConst A.hom ∧
        GlobalTheory.AbCoh.PrimF A) : GlobalTheory.Published.AbelianUnobstructed := by
  have hS : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
      SmoothOfRelativeDimension g A.hom →
      (Module.Finite R (HO1 A.hom) ∧ Module.Projective R (HO1 A.hom) ∧
        ∀ p : PrimeSpectrum R, Module.rankAtStalk (HO1 A.hom) p = g) ∧
      ∃ e : ⋀[R]^2 (HO1 A.hom) ≃ₗ[R] GlobalTheory.CatCoh.H2 (OAff A.hom),
        ∀ a b, e (exteriorPower.ιMulti R 2 ![a, b]) = GlobalTheory.CatCoh.cup (OAff A.hom) a b := by
    intro R _ A _ g hA hg
    obtain ⟨h1, h2, -, -⟩ := hO R A g hA hg
    exact ⟨h1, h2⟩
  exact GlobalTheory.T.abelianSchemeUnobstructed_of_constantDimension (GlobalTheory.T.abelianScheme_unobstructed_of_forms_structure (GlobalTheory.T.abelianSchemeGlobalFormsPrimitive_of_frames hF) (GlobalTheory.T.primitive_degree_two_extension (GlobalTheory.T.additiveClassDegreeTwo_structureSheaf_vanish hS))
    (GlobalTheory.T.axes_vanishing_degree_one_extension (GlobalTheory.T.axesO1_of_projective_rank_cup hS)))

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeUnobstructedOfCohomologyStructureStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_unobstructed_of_cohomology_structure : GlobalTheory.AbCoh.OStr → (∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → GlobalTheory.AbCoh.HasFrame (OAff A.hom) ∧ GlobalTheory.AbCoh.UConst A.hom ∧ GlobalTheory.AbCoh.PrimF A) → GlobalTheory.Published.AbelianUnobstructed := by
  first | exact @GlobalTheory.abelianUnobstructed_of_struct | exact GlobalTheory.abelianUnobstructed_of_struct | (intros; apply GlobalTheory.abelianUnobstructed_of_struct <;> assumption)
end
