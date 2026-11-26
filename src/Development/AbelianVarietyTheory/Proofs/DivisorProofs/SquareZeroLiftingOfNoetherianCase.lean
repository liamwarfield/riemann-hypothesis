module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDescendsToFinitelyGeneratedSubring
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MorphismDescendsToSubring
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EndoLbIsoSymmetryHypothesisExtendNormalModel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftHomExistsOfNoetherian
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianHomReductionDescendsFinitelyGenerated
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IotaCompTrans
noncomputable section

namespace GlobalTheory.AbHomDesc

variable {R R₀ : Type} [CommRing R] [CommRing R₀] (I : Ideal R) (π : R →+* R₀)

def iota (hI : RingHom.ker π = I) (S : Subring R) : S ⧸ I.comap S.subtype →+* R₀ :=
  Ideal.Quotient.lift _ (π.comp S.subtype) fun x hx => by
    have h : (x : R) ∈ I := hx
    rw [← hI] at h
    exact h

theorem iota_comp_mk (hI : RingHom.ker π = I) (S : Subring R) :
    (iota I π hI S).comp (Ideal.Quotient.mk _) = π.comp S.subtype := rfl

theorem iota_injective (hI : RingHom.ker π = I) (S : Subring R) : Function.Injective (iota I π hI S) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [Ideal.Quotient.eq_zero_iff_mem]
  change (x : R) ∈ I
  rw [← hI]
  exact ha

def trans {S S' : Subring R} (h : S ≤ S') : S ⧸ I.comap S.subtype →+* S' ⧸ I.comap S'.subtype :=
  Ideal.quotientMap _ (Subring.inclusion h) fun x hx => hx

theorem iota_comp_trans (hI : RingHom.ker π = I) {S S' : Subring R} (h : S ≤ S') :
    (iota I π hI S').comp (trans I h) = iota I π hI S := by
  ext x
  rfl

theorem trans_comp_mk {S S' : Subring R} (h : S ≤ S') :
    (trans I h).comp (Ideal.Quotient.mk _) = (Ideal.Quotient.mk _).comp (Subring.inclusion h) := rfl

end GlobalTheory.AbHomDesc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianHomReductionDescendsFinitelyGenerated
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.AbHomDesc

theorem exists_baseChange_subring : ∀ (R : Type) [CommRing R] (S S' : Subring R) (h : S ≤ S') (g : ℕ) (A : Over (Sp R)) [GrpObj A] (AS : Over (Sp S)) [GrpObj AS] (φ : A.left ⟶ AS.left), IsAbelianScheme AS → SmoothOfRelativeDimension g AS.hom → IsGrpPullback A AS (spMap S.subtype) φ → ∃ (AS' : Over (Sp S')) (_ : GrpObj AS') (φ' : A.left ⟶ AS'.left) (ρ : AS'.left ⟶ AS.left), IsAbelianScheme AS' ∧ SmoothOfRelativeDimension g AS'.hom ∧ IsGrpPullback A AS' (spMap S'.subtype) φ' ∧ IsGrpPullback AS' AS (spMap (Subring.inclusion h)) ρ ∧ φ' ≫ ρ = φ := by
  intro R _ S S' h g A _ AS _ φ hab hsm hφ
  have e : spMap S.subtype = spMap S'.subtype ≫ spMap (Subring.inclusion h) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; rfl
  have hf := ReciprocityTheory.ChartRestriction.G.Chart.isGrpPullback_factor (spMap (Subring.inclusion h)) (spMap S'.subtype)
    (hφ.congr e rfl)
  have hs : SmoothOfRelativeDimension g ((Over.pullback (spMap (Subring.inclusion h))).obj AS).hom := by
    exact (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback (IsPullback.of_hasPullback _ _) hsm
  exact ⟨_, inferInstance, _, pullback.fst _ _, isAbelianScheme_overPullback _ AS hab, hs, hf,
    isGrpPullback_pullback _ _, pullback.lift_fst _ _ _⟩

theorem exists_finset_le_of_finiteType : ∀ (R : Type) [CommRing R] (S : Subring R), Algebra.FiniteType ℤ S → ∃ F : Finset R, ∀ T : Subring R, (F : Set R) ⊆ T → S ≤ T := by
  intro R _ S hS
  classical
  obtain ⟨s, hs⟩ := hS.out
  refine ⟨s.image Subtype.val, fun T hT x hx => ?_⟩
  suffices key : ∀ y : S, y ∈ Algebra.adjoin ℤ (s : Set S) → (y : R) ∈ T from
    key ⟨x, hx⟩ (hs ▸ Algebra.mem_top)
  intro y hy
  induction hy using Algebra.adjoin_induction with
  | mem y hy => exact hT (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hy))
  | algebraMap n =>
    rw [eq_intCast]
    push_cast
    exact intCast_mem T n
  | add y z _ _ hy hz => exact T.add_mem hy hz
  | mul y z _ _ hy hz => exact T.mul_mem hy hz

theorem exists_isPullback_reductions : ∀ (R : Type) [CommRing R] (I : Ideal R) (S S' : Subring R) (h : S ≤ S') (AS : Over (Sp S)) (AS' : Over (Sp S')) (ρ : AS'.left ⟶ AS.left), IsPullback ρ AS'.hom AS.hom (spMap (Subring.inclusion h)) → ∃ p : pullback AS'.hom (spMap (Ideal.Quotient.mk (I.comap S'.subtype))) ⟶ pullback AS.hom (spMap (Ideal.Quotient.mk (I.comap S.subtype))), IsPullback p (pullback.snd _ _) (pullback.snd _ _) (spMap (GlobalTheory.AbHomDesc.trans I h)) ∧ p ≫ pullback.fst _ _ = pullback.fst _ _ ≫ ρ := by
  intro R _ I S S' h AS AS' ρ hρ
  have e : spMap (Ideal.Quotient.mk (I.comap S'.subtype)) ≫ spMap (Subring.inclusion h) =
      spMap (trans I h) ≫ spMap (Ideal.Quotient.mk (I.comap S.subtype)) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, trans_comp_mk]
  have big := (IsPullback.of_hasPullback AS'.hom (spMap (Ideal.Quotient.mk (I.comap S'.subtype)))).paste_horiz hρ
  rw [e] at big
  refine ⟨pullback.lift (pullback.fst _ _ ≫ ρ) (pullback.snd _ _ ≫ spMap (trans I h))
    (by simp only [Category.assoc]; rw [hρ.w, pullback.condition_assoc, e]), ?_, pullback.lift_fst _ _ _⟩
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
  rwa [pullback.lift_fst]

theorem spMap_comp_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (g : A →+* B) (f : B →+* C) :
    spMap f ≫ spMap g = spMap (f.comp g) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem isIso_spMap {A B : Type} [CommRing A] [CommRing B] (f : A ≃+* B) : IsIso (spMap (f : A →+* B)) := by
  have : IsIso (CommRingCat.ofHom (f : A →+* B)) := f.toCommRingCatIso.isIso_hom
  infer_instance

noncomputable def redEquiv {R R₀ : Type} [CommRing R] [CommRing R₀] (I : Ideal R) (π : R →+* R₀)
    (hI : RingHom.ker π = I) (S : Subring R) : S ⧸ I.comap S.subtype ≃+* (iota I π hI S).range :=
  RingEquiv.ofBijective (iota I π hI S).rangeRestrict
    ⟨fun x y hxy => iota_injective I π hI S (congrArg Subtype.val hxy), (iota I π hI S).rangeRestrict_surjective⟩

theorem iota_redEquiv_symm {R R₀ : Type} [CommRing R] [CommRing R₀] (I : Ideal R) (π : R →+* R₀)
    (hI : RingHom.ker π = I) (S : Subring R) :
    (iota I π hI S).comp ((redEquiv I π hI S).symm : _ →+* _) = (iota I π hI S).range.subtype := by
  ext t
  exact congrArg Subtype.val ((redEquiv I π hI S).apply_symm_apply t)

noncomputable def redInv {R R₀ : Type} [CommRing R] [CommRing R₀] (I : Ideal R) (π : R →+* R₀)
    (hI : RingHom.ker π = I) (S : Subring R) : (iota I π hI S).range →+* S ⧸ I.comap S.subtype :=
  (redEquiv I π hI S).symm.toRingHom

instance isIso_spMap_redInv {R R₀ : Type} [CommRing R] [CommRing R₀] (I : Ideal R) (π : R →+* R₀)
    (hI : RingHom.ker π = I) (S : Subring R) : IsIso (spMap (redInv I π hI S)) :=
  isIso_spMap (redEquiv I π hI S).symm

theorem iota_redInv {R R₀ : Type} [CommRing R] [CommRing R₀] (I : Ideal R) (π : R →+* R₀)
    (hI : RingHom.ker π = I) (S : Subring R) :
    (iota I π hI S).comp (redInv I π hI S) = (iota I π hI S).range.subtype :=
  iota_redEquiv_symm I π hI S

theorem morphism_descends_to_reduction : ∀ (R : Type) [CommRing R] (I : Ideal R) (R₀ : Type) [CommRing R₀] (π : R →+* R₀) (hπ : Function.Surjective π) (hI : RingHom.ker π = I) (S : Subring R) (X X₀ Y₀ : Scheme.{0}) (p : X ⟶ Sp R₀) (a : X₀ ⟶ Sp (S ⧸ I.comap S.subtype)) (b : Y₀ ⟶ Sp (S ⧸ I.comap S.subtype)) (π' : X ⟶ X₀) [QuasiCompact a] [QuasiSeparated a] [LocallyOfFinitePresentation b] (φ : X ⟶ Y₀), IsPullback π' p a (spMap (GlobalTheory.AbHomDesc.iota I π hI S)) → φ ≫ b = π' ≫ a → ∃ F : Finset R, ∀ (S' : Subring R) (h : S ≤ S'), (F : Set R) ⊆ S' → ∀ (X₁ : Scheme.{0}) (a₁ : X₁ ⟶ Sp (S' ⧸ I.comap S'.subtype)) (π₁ : X₁ ⟶ X₀) (k : X ⟶ X₁), IsPullback π₁ a₁ a (spMap (GlobalTheory.AbHomDesc.trans I h)) → k ≫ π₁ = π' → k ≫ a₁ = p ≫ spMap (GlobalTheory.AbHomDesc.iota I π hI S') → ∃ ψ : X₁ ⟶ Y₀, k ≫ ψ = φ ∧ ψ ≫ b = π₁ ≫ a := by
  intro R _ I R₀ _ π hπ hI S X X₀ Y₀ p a b π' _ _ _ φ hpb hφ
  classical
  have hpb' : IsPullback π' p (a ≫ spMap (redInv I π hI S)) (spMap (iota I π hI S).range.subtype) := by
    refine IsPullback.of_iso hpb (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (asIso (spMap (redInv I π hI S))) (by simp) (by simp) (by simp) ?_
    rw [Iso.refl_hom, Category.id_comp, asIso_hom, spMap_comp_spMap, iota_redInv]
  obtain ⟨F₀, hF₀⟩ := GlobalTheory.morphism_descends_to_subring R₀ (iota I π hI S).range X X₀ Y₀ p
    (a ≫ spMap (redInv I π hI S)) (b ≫ spMap (redInv I π hI S)) π' φ hpb'
    (by rw [← Category.assoc, hφ, Category.assoc])
  refine ⟨F₀.image (Function.surjInv hπ), fun S' h hF X₁ a₁ π₁ k hpb₁ hk₁ hk₂ => ?_⟩
  have hT : (iota I π hI S).range ≤ (iota I π hI S').range := by
    rintro _ ⟨x, rfl⟩
    exact ⟨trans I h x, by rw [← RingHom.comp_apply, iota_comp_trans]⟩
  have hFT : (F₀ : Set R₀) ⊆ (iota I π hI S').range := by
    intro y hy
    have hm : Function.surjInv hπ y ∈ S' := hF (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hy))
    exact ⟨Ideal.Quotient.mk _ ⟨_, hm⟩, Function.surjInv_eq hπ y⟩
  have hring : (trans I h).comp (redInv I π hI S) = (redInv I π hI S').comp (Subring.inclusion hT) := by
    ext t
    apply (redEquiv I π hI S').injective
    show redEquiv I π hI S' (trans I h (redInv I π hI S t)) =
      redEquiv I π hI S' ((redEquiv I π hI S').symm (Subring.inclusion hT t))
    rw [RingEquiv.apply_symm_apply]
    apply Subtype.ext
    show iota I π hI S' (trans I h (redInv I π hI S t)) = (t : R₀)
    rw [← RingHom.comp_apply, iota_comp_trans, ← RingHom.comp_apply, iota_redInv]
    rfl
  have hpb₁' : IsPullback π₁ (a₁ ≫ spMap (redInv I π hI S')) (a ≫ spMap (redInv I π hI S))
      (spMap (Subring.inclusion hT)) := by
    refine IsPullback.of_iso hpb₁ (Iso.refl _) (Iso.refl _) (asIso (spMap (redInv I π hI S')))
      (asIso (spMap (redInv I π hI S))) (by simp) (by simp) (by simp) ?_
    rw [asIso_hom, asIso_hom, spMap_comp_spMap, spMap_comp_spMap, hring]
  have hk₂' : k ≫ a₁ ≫ spMap (redInv I π hI S') = p ≫ spMap (iota I π hI S').range.subtype := by
    rw [← Category.assoc, hk₂, Category.assoc, spMap_comp_spMap, iota_redInv]
  obtain ⟨ψ, hψ₁, hψ₂⟩ := hF₀ _ hT hFT X₁ _ π₁ k hpb₁' hk₁ hk₂'
  refine ⟨ψ, hψ₁, ?_⟩
  rw [← Category.assoc, ← Category.assoc] at hψ₂
  exact (cancel_mono _).1 hψ₂

theorem exists_isGrpPullback_reduction : ∀ (R : Type) [CommRing R] (I : Ideal R) (R₀ : Type) [CommRing R₀] (π : R →+* R₀) (hI : RingHom.ker π = I) (S : Subring R) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A : Over (Sp R)) [GrpObj A] (i : A₀.left ⟶ A.left) (AS : Over (Sp S)) [GrpObj AS] (φ : A.left ⟶ AS.left), IsGrpPullback A₀ A (spMap π) i → IsGrpPullback A AS (spMap S.subtype) φ → ∃ ψ : A₀.left ⟶ ((Over.pullback (spMap (Ideal.Quotient.mk (I.comap S.subtype)))).obj AS).left, IsGrpPullback A₀ ((Over.pullback (spMap (Ideal.Quotient.mk (I.comap S.subtype)))).obj AS) (spMap (GlobalTheory.AbHomDesc.iota I π hI S)) ψ ∧ i ≫ φ = ψ ≫ pullback.fst AS.hom (spMap (Ideal.Quotient.mk (I.comap S.subtype))) := by
  intro R _ I R₀ _ π hI S A₀ _ A _ i AS _ φ hA hφ
  have e : spMap π ≫ spMap S.subtype =
      spMap (iota I π hI S) ≫ spMap (Ideal.Quotient.mk (I.comap S.subtype)) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, iota_comp_mk]
  have h := (hA.comp hφ).congr e rfl
  exact ⟨_, ReciprocityTheory.ChartRestriction.G.Chart.isGrpPullback_factor _ _ h, (pullback.lift_fst _ _ _).symm⟩

theorem abelian_hom_reduction_descends : ∀ (R : Type) [CommRing R] (I : Ideal R) (R₀ : Type) [CommRing R₀] (π : R →+* R₀),
    Function.Surjective π → RingHom.ker π = I →
  ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A : Over (Sp R)) [GrpObj A] (i : A₀.left ⟶ A.left),
    IsGrpPullback A₀ A (spMap π) i → IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
  ∀ (g' : ℕ) (B₀ : Over (Sp R₀)) [GrpObj B₀] (B : Over (Sp R)) [GrpObj B] (j : B₀.left ⟶ B.left),
    IsGrpPullback B₀ B (spMap π) j → IsAbelianScheme B → SmoothOfRelativeDimension g' B.hom →
  ∀ (f₀ : A₀ ⟶ B₀) [IsMonHom f₀],
  ∃ (S : Subring R) (ι₀ : (S ⧸ I.comap S.subtype) →+* R₀)
    (AS₀ : Over (Sp (S ⧸ I.comap S.subtype))) (_ : GrpObj AS₀) (AS : Over (Sp S)) (_ : GrpObj AS) (iS : AS₀.left ⟶ AS.left)
    (BS₀ : Over (Sp (S ⧸ I.comap S.subtype))) (_ : GrpObj BS₀) (BS : Over (Sp S)) (_ : GrpObj BS) (jS : BS₀.left ⟶ BS.left)
    (fS₀ : AS₀ ⟶ BS₀) (φA : A.left ⟶ AS.left) (φB : B.left ⟶ BS.left) (ψA : A₀.left ⟶ AS₀.left) (ψB : B₀.left ⟶ BS₀.left),
    Algebra.FiniteType ℤ S ∧ ι₀.comp (Ideal.Quotient.mk (I.comap S.subtype)) = π.comp S.subtype ∧ IsMonHom fS₀ ∧
    IsGrpPullback AS₀ AS (spMap (Ideal.Quotient.mk (I.comap S.subtype))) iS ∧
    IsGrpPullback BS₀ BS (spMap (Ideal.Quotient.mk (I.comap S.subtype))) jS ∧
    IsAbelianScheme AS ∧ SmoothOfRelativeDimension g AS.hom ∧ IsAbelianScheme BS ∧ SmoothOfRelativeDimension g' BS.hom ∧
    IsGrpPullback A AS (spMap S.subtype) φA ∧ IsGrpPullback B BS (spMap S.subtype) φB ∧
    IsGrpPullback A₀ AS₀ (spMap ι₀) ψA ∧ IsGrpPullback B₀ BS₀ (spMap ι₀) ψB ∧
    i ≫ φA = ψA ≫ iS ∧ j ≫ φB = ψB ≫ jS ∧ f₀.left ≫ ψB = ψA ≫ fS₀.left := by
  intro R _ I R₀ _ π hπ hI g A₀ _ A _ i hA hAab hAsm g' B₀ _ B _ j hB hBab hBsm f₀ _

  obtain ⟨S₀, AS₀, _, φA₀, -, hfg₀, hAS₀ab, hAS₀sm, hφA₀⟩ := GlobalTheory.T.abelianScheme_descends_to_finitelyGenerated_subring R g A ∅ hAab hAsm
  obtain ⟨F₀, hF₀⟩ := exists_finset_le_of_finiteType R S₀ hfg₀
  obtain ⟨S₁, BS₁, _, φB₁, hF₀S₁, hfg₁, hBS₁ab, hBS₁sm, hφB₁⟩ := GlobalTheory.T.abelianScheme_descends_to_finitelyGenerated_subring R g' B F₀ hBab hBsm
  obtain ⟨AS₁, _, φA₁, -, hAS₁ab, hAS₁sm, hφA₁, -, -⟩ :=
    exists_baseChange_subring R S₀ S₁ (hF₀ S₁ hF₀S₁) g A AS₀ φA₀ hAS₀ab hAS₀sm hφA₀

  obtain ⟨ψA, hψA, hiA⟩ := exists_isGrpPullback_reduction R I R₀ π hI S₁ A₀ A i AS₁ φA₁ hA hφA₁
  obtain ⟨ψB, hψB, hiB⟩ := exists_isGrpPullback_reduction R I R₀ π hI S₁ B₀ B j BS₁ φB₁ hB hφB₁
  have wA : ψA ≫ pullback.snd AS₁.hom (spMap (Ideal.Quotient.mk (I.comap S₁.subtype))) =
      A₀.hom ≫ spMap (iota I π hI S₁) := hψA.1.w
  have wB : ψB ≫ pullback.snd BS₁.hom (spMap (Ideal.Quotient.mk (I.comap S₁.subtype))) =
      B₀.hom ≫ spMap (iota I π hI S₁) := hψB.1.w

  have := hAS₁ab.proper
  have := hBS₁ab.smooth
  have hw : (f₀.left ≫ ψB) ≫ pullback.snd BS₁.hom (spMap (Ideal.Quotient.mk (I.comap S₁.subtype))) =
      ψA ≫ pullback.snd AS₁.hom (spMap (Ideal.Quotient.mk (I.comap S₁.subtype))) := by
    rw [Category.assoc, wB, wA, ← Category.assoc, Over.w f₀]
  obtain ⟨F, hF⟩ := morphism_descends_to_reduction R I R₀ π hπ hI S₁ A₀.left _ _ A₀.hom
    (pullback.snd AS₁.hom (spMap (Ideal.Quotient.mk (I.comap S₁.subtype))))
    (pullback.snd BS₁.hom (spMap (Ideal.Quotient.mk (I.comap S₁.subtype)))) ψA (f₀.left ≫ ψB) hψA.1 hw

  obtain ⟨S', h, hFS, hfg'⟩ := GlobalTheory.KeyTf.exists_finiteType_subring_adjoin R S₁ F hfg₁
  obtain ⟨AS', _, φA', ρA, hAS'ab, hAS'sm, hφA', hρA, hφρA⟩ := exists_baseChange_subring R S₁ S' h g A AS₁ φA₁ hAS₁ab hAS₁sm hφA₁
  obtain ⟨BS', _, φB', ρB, hBS'ab, hBS'sm, hφB', hρB, hφρB⟩ := exists_baseChange_subring R S₁ S' h g' B BS₁ φB₁ hBS₁ab hBS₁sm hφB₁
  obtain ⟨ψA', hψA', hiA'⟩ := exists_isGrpPullback_reduction R I R₀ π hI S' A₀ A i AS' φA' hA hφA'
  obtain ⟨ψB', hψB', hiB'⟩ := exists_isGrpPullback_reduction R I R₀ π hI S' B₀ B j BS' φB' hB hφB'
  have wA' : ψA' ≫ pullback.snd AS'.hom (spMap (Ideal.Quotient.mk (I.comap S'.subtype))) =
      A₀.hom ≫ spMap (iota I π hI S') := hψA'.1.w
  have wB' : ψB' ≫ pullback.snd BS'.hom (spMap (Ideal.Quotient.mk (I.comap S'.subtype))) =
      B₀.hom ≫ spMap (iota I π hI S') := hψB'.1.w
  obtain ⟨pA, hpA, hpAf⟩ := exists_isPullback_reductions R I S₁ S' h AS₁ AS' ρA hρA.1
  obtain ⟨pB, hpB, hpBf⟩ := exists_isPullback_reductions R I S₁ S' h BS₁ BS' ρB hρB.1
  have eι : spMap (iota I π hI S') ≫ spMap (trans I h) = spMap (iota I π hI S₁) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, iota_comp_trans]
  have cA : ψA' ≫ pA = ψA := by
    apply pullback.hom_ext
    · rw [Category.assoc, hpAf, ← Category.assoc, ← hiA', Category.assoc, hφρA, hiA]
    · rw [Category.assoc, hpA.w, ← Category.assoc, wA', Category.assoc, eι, wA]
  have cB : ψB' ≫ pB = ψB := by
    apply pullback.hom_ext
    · rw [Category.assoc, hpBf, ← Category.assoc, ← hiB', Category.assoc, hφρB, hiB]
    · rw [Category.assoc, hpB.w, ← Category.assoc, wB', Category.assoc, eι, wB]
  obtain ⟨ψ, hψ₁, hψ₂⟩ := hF S' h hFS _ (pullback.snd AS'.hom _) pA ψA' hpA cA wA'
  let fl := hpB.lift ψ (pullback.snd AS'.hom (spMap (Ideal.Quotient.mk (I.comap S'.subtype))))
    (by rw [hψ₂, hpA.w])
  let fS : (Over.pullback (spMap (Ideal.Quotient.mk (I.comap S'.subtype)))).obj AS' ⟶
      (Over.pullback (spMap (Ideal.Quotient.mk (I.comap S'.subtype)))).obj BS' :=
    Over.homMk fl (hpB.lift_snd _ _ _)
  have key : f₀.left ≫ ψB' = ψA' ≫ fS.left := by
    apply hpB.hom_ext
    · rw [Category.assoc, cB]
      show _ = ψA' ≫ fl ≫ pB
      rw [hpB.lift_fst, hψ₁]
    · rw [Category.assoc, wB', ← Category.assoc, Over.w f₀]
      show _ = ψA' ≫ fl ≫ _
      rw [hpB.lift_snd, wA']

  have : IsSchemeTheoreticallyDominant (spMap (iota I π hI S')) :=
    GlobalTheory.ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective _ (iota_injective I π hI S')
  have := hAS'ab.smooth
  have := hBS'ab.proper
  have : Flat ((Over.pullback (spMap (Ideal.Quotient.mk (I.comap S'.subtype)))).obj AS').hom := by
    show Flat (pullback.snd _ _); infer_instance
  have : IsSeparated ((Over.pullback (spMap (Ideal.Quotient.mk (I.comap S'.subtype)))).obj BS').hom := by
    show IsSeparated (pullback.snd _ _); infer_instance
  have hmon : IsMonHom fS := GlobalTheory.ExtUnique.isMonHom_of_isGrpPullback hψA' hψB' f₀ fS key
  exact ⟨S', iota I π hI S', _, inferInstance, AS', inferInstance, pullback.fst _ _, _, inferInstance, BS',
    inferInstance, pullback.fst _ _, fS, φA', φB', ψA', ψB', hfg', iota_comp_mk I π hI S', hmon,
    isGrpPullback_pullback _ _, isGrpPullback_pullback _ _, hAS'ab, hAS'sm, hBS'ab, hBS'sm, hφA', hφB', hψA',
    hψB', hiA', hiB', key⟩

end GlobalTheory.AbHomDesc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianHomReductionDescendsFinitelyGeneratedStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_hom_reduction_descends_finitely_generated : ∀ (R : Type) [CommRing R] (I : Ideal R) (R₀ : Type) [CommRing R₀] (π : R →+* R₀),
    Function.Surjective π → RingHom.ker π = I →
  ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A : Over (Sp R)) [GrpObj A] (i : A₀.left ⟶ A.left),
    IsGrpPullback A₀ A (spMap π) i → IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
  ∀ (g' : ℕ) (B₀ : Over (Sp R₀)) [GrpObj B₀] (B : Over (Sp R)) [GrpObj B] (j : B₀.left ⟶ B.left),
    IsGrpPullback B₀ B (spMap π) j → IsAbelianScheme B → SmoothOfRelativeDimension g' B.hom →
  ∀ (f₀ : A₀ ⟶ B₀) [IsMonHom f₀],
  ∃ (S : Subring R) (ι₀ : (S ⧸ I.comap S.subtype) →+* R₀)
    (AS₀ : Over (Sp (S ⧸ I.comap S.subtype))) (_ : GrpObj AS₀) (AS : Over (Sp S)) (_ : GrpObj AS) (iS : AS₀.left ⟶ AS.left)
    (BS₀ : Over (Sp (S ⧸ I.comap S.subtype))) (_ : GrpObj BS₀) (BS : Over (Sp S)) (_ : GrpObj BS) (jS : BS₀.left ⟶ BS.left)
    (fS₀ : AS₀ ⟶ BS₀) (φA : A.left ⟶ AS.left) (φB : B.left ⟶ BS.left) (ψA : A₀.left ⟶ AS₀.left) (ψB : B₀.left ⟶ BS₀.left),
    Algebra.FiniteType ℤ S ∧ ι₀.comp (Ideal.Quotient.mk (I.comap S.subtype)) = π.comp S.subtype ∧ IsMonHom fS₀ ∧
    IsGrpPullback AS₀ AS (spMap (Ideal.Quotient.mk (I.comap S.subtype))) iS ∧
    IsGrpPullback BS₀ BS (spMap (Ideal.Quotient.mk (I.comap S.subtype))) jS ∧
    IsAbelianScheme AS ∧ SmoothOfRelativeDimension g AS.hom ∧ IsAbelianScheme BS ∧ SmoothOfRelativeDimension g' BS.hom ∧
    IsGrpPullback A AS (spMap S.subtype) φA ∧ IsGrpPullback B BS (spMap S.subtype) φB ∧
    IsGrpPullback A₀ AS₀ (spMap ι₀) ψA ∧ IsGrpPullback B₀ BS₀ (spMap ι₀) ψB ∧
    i ≫ φA = ψA ≫ iS ∧ j ≫ φB = ψB ≫ jS ∧ f₀.left ≫ ψB = ψA ≫ fS₀.left := by
  first | exact @GlobalTheory.AbHomDesc.abelian_hom_reduction_descends | exact GlobalTheory.AbHomDesc.abelian_hom_reduction_descends | (intros; apply GlobalTheory.AbHomDesc.abelian_hom_reduction_descends <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PushMemLiftFilOfInjective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PushMemLiftFilOfInjective
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqLift

theorem push_mem_liftFil_of_injective : AbelianDeRham →
  ∀ (R : Type) [CommRing R] (I : Ideal R) (h : I ^ 2 = 0) (R₀ : Type) [CommRing R₀] (π : R →+* R₀),
    Function.Surjective π → RingHom.ker π = I →
  ∀ (S : Type) [CommRing S] (σ : S →+* R), Function.Injective σ →
  ∀ (J : Ideal S) (hJ : J ^ 2 = 0) (S₀ : Type) [CommRing S₀] (πS : S →+* S₀),
    Function.Surjective πS → RingHom.ker πS = J →
  ∀ (ι₀ : S₀ →+* R₀), ι₀.comp πS = π.comp σ →
  ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A : Over (Sp R)) [GrpObj A] (i : A₀.left ⟶ A.left)
    (hA : IsGrpPullback A₀ A (spMap π) i)
    (AS₀ : Over (Sp S₀)) [GrpObj AS₀] (AS : Over (Sp S)) [GrpObj AS] (iS : AS₀.left ⟶ AS.left)
    (hAS : IsGrpPullback AS₀ AS (spMap πS) iS), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    IsAbelianScheme AS → SmoothOfRelativeDimension g AS.hom →
  ∀ (φA : A.left ⟶ AS.left) (ψA : A₀.left ⟶ AS₀.left), IsGrpPullback A AS (spMap σ) φA →
    IsGrpPullback A₀ AS₀ (spMap ι₀) ψA → i ≫ φA = ψA ≫ iS →
  ∀ (g' : ℕ) (B₀ : Over (Sp R₀)) [GrpObj B₀] (B : Over (Sp R)) [GrpObj B] (j : B₀.left ⟶ B.left)
    (hB : IsGrpPullback B₀ B (spMap π) j)
    (BS₀ : Over (Sp S₀)) [GrpObj BS₀] (BS : Over (Sp S)) [GrpObj BS] (jS : BS₀.left ⟶ BS.left)
    (hBS : IsGrpPullback BS₀ BS (spMap πS) jS), IsAbelianScheme B → SmoothOfRelativeDimension g' B.hom →
    IsAbelianScheme BS → SmoothOfRelativeDimension g' BS.hom →
  ∀ (φB : B.left ⟶ BS.left) (ψB : B₀.left ⟶ BS₀.left), IsGrpPullback B BS (spMap σ) φB →
    IsGrpPullback B₀ BS₀ (spMap ι₀) ψB → j ≫ φB = ψB ≫ jS →
  ∀ (f₀ : A₀ ⟶ B₀) [IsMonHom f₀] (fS₀ : AS₀ ⟶ BS₀) [IsMonHom fS₀], f₀.left ≫ ψB = ψA ≫ fS₀.left →
    (∀ d ∈ liftFil (divided₂ h) hA, push (divided₂ h) (spMap π) f₀ d ∈ liftFil (divided₂ h) hB) →
    ∀ d ∈ liftFil (divided₂ hJ) hAS, push (divided₂ hJ) (spMap πS) fS₀ d ∈ liftFil (divided₂ hJ) hBS := by
  intro H R _ I h R₀ _ π hπ hI S _ σ hσ J hJ S₀ _ πS hπS hJk ι₀ hι g A₀ _ A _ i hA AS₀ _ AS _ iS hAS hAab hAg
    hASab hASg φA ψA hφA hψA hiA g' B₀ _ B _ j hB BS₀ _ BS _ jS hBS hBab hBg hBSab hBSg φB ψB hφB hψB hjB
    f₀ _ fS₀ _ hf hyp d hd
  obtain ⟨_, _, HBC, HR, _⟩ := H
  letI : Algebra S R := σ.toAlgebra
  have hJI : ∀ a ∈ J, σ a ∈ I := fun a ha ↦ by
    rw [← hI, RingHom.mem_ker]
    have : πS a = 0 := by rw [← RingHom.mem_ker, hJk]; exact ha
    rw [← RingHom.comp_apply, ← hι, RingHom.comp_apply, this, map_zero]
  have hdp : IsDPMorphism (divided₂ hJ) (divided₂ h) σ := isDPMorphism_sqDP hJ h σ hJI
  have hbase : spMap ι₀ ≫ spMap πS = spMap π ≫ spMap σ := by
    rw [← Cris.spMap_comp, ← Cris.spMap_comp, hι]
  have mA := GrpMor.of_isGrpPullback hdp hbase hψA
  have mB := GrpMor.of_isGrpPullback hdp hbase hψB
  have nA := GlobalTheory.Published.AbelianDeRham.bcMor (R := S) (R' := R) hφA
  have nB := GlobalTheory.Published.AbelianDeRham.bcMor (R := S) (R' := R) hφB
  have hBCA := HBC S AS g hASab hASg R A φA hφA
  obtain ⟨y, hy⟩ := hBCA.1.exists (crysToDR (divided₂ hJ) hAS d)
  obtain ⟨d', rfl⟩ :=
    (GlobalTheory.Published.AbelianDeRham.Rigid.crysToDR_bijective HR hAab hAg (isDPNilpotent_squareZero h) hπ hI hA).2 y
  have hsurj := (HR S AS g hASab hASg J (divided₂ hJ) (isDPNilpotent_squareZero hJ) S₀ πS hπS hJk AS₀ iS hAS).2
  have hm : mA.Corr d d' := fun c ↦ by
    obtain ⟨c0, rfl⟩ := hsurj c
    have k : GrpMor (dp0 S) (𝟙 (Sp S)) AS (divided₂ h) (spMap π) A₀ σ
        (spMap ι₀ ≫ spMap πS) (ψA ≫ iS) := GrpMor.of_isGrpPullback (IsDPMorphism.comp _ mA.dp (liftMor (divided₂ hJ) hAS).dp) (by simpa using hbase) (IsGrpPullback.comp hψA hAS)
    rw [GrpMor.pull_pull (liftMor (divided₂ hJ) hAS) mA k (fun _ ↦ rfl) rfl c0,
      ← GrpMor.pull_pull nA (liftMor (divided₂ h) hA) k (fun _ ↦ rfl) hiA c0]
    exact (crysToDR_apply _ hA d' _).symm.trans ((hy c0).trans (congrArg σ (crysToDR_apply _ hAS d c0)))
  have hd' : d' ∈ liftFil (divided₂ h) hA := by
    have hle : PrimitiveSubmodule A ≤ LinearMap.ker (crysToDR (divided₂ h) hA d') := by
      rw [hBCA.2, Submodule.span_le]
      rintro _ ⟨c, hc, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, hy c]
      rw [liftFil, Submodule.mem_comap, Fil, Submodule.mem_dualAnnihilator] at hd
      rw [hd c hc, map_zero]
    exact (Submodule.mem_dualAnnihilator _).2 fun c hc ↦ hle hc
  have hpush := hyp d' hd'
  have hcorr := GrpMor.Corr.push (m := mA) mB fS₀ f₀ hf.symm hm
  have hx := crysToDR_corr (divided₂ hJ) hBS hB mB nB hjB hcorr
  rw [liftFil, Submodule.mem_comap, Fil, Submodule.mem_dualAnnihilator]
  rw [liftFil, Submodule.mem_comap, Fil, Submodule.mem_dualAnnihilator] at hpush
  intro c hc
  apply hσ
  show σ _ = σ 0
  rw [map_zero]
  exact (hx c).symm.trans (hpush _ (nB.isMor.pullback1_mem_hodgeFiltration hc))

end GlobalTheory.SqLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PushMemLiftFilOfInjectiveStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.push_mem_liftFil_of_injective_alt : AbelianDeRham →
  ∀ (R : Type) [CommRing R] (I : Ideal R) (h : I ^ 2 = 0) (R₀ : Type) [CommRing R₀] (π : R →+* R₀),
    Function.Surjective π → RingHom.ker π = I →
  ∀ (S : Type) [CommRing S] (σ : S →+* R), Function.Injective σ →
  ∀ (J : Ideal S) (hJ : J ^ 2 = 0) (S₀ : Type) [CommRing S₀] (πS : S →+* S₀),
    Function.Surjective πS → RingHom.ker πS = J →
  ∀ (ι₀ : S₀ →+* R₀), ι₀.comp πS = π.comp σ →
  ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A : Over (Sp R)) [GrpObj A] (i : A₀.left ⟶ A.left)
    (hA : IsGrpPullback A₀ A (spMap π) i)
    (AS₀ : Over (Sp S₀)) [GrpObj AS₀] (AS : Over (Sp S)) [GrpObj AS] (iS : AS₀.left ⟶ AS.left)
    (hAS : IsGrpPullback AS₀ AS (spMap πS) iS), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    IsAbelianScheme AS → SmoothOfRelativeDimension g AS.hom →
  ∀ (φA : A.left ⟶ AS.left) (ψA : A₀.left ⟶ AS₀.left), IsGrpPullback A AS (spMap σ) φA →
    IsGrpPullback A₀ AS₀ (spMap ι₀) ψA → i ≫ φA = ψA ≫ iS →
  ∀ (g' : ℕ) (B₀ : Over (Sp R₀)) [GrpObj B₀] (B : Over (Sp R)) [GrpObj B] (j : B₀.left ⟶ B.left)
    (hB : IsGrpPullback B₀ B (spMap π) j)
    (BS₀ : Over (Sp S₀)) [GrpObj BS₀] (BS : Over (Sp S)) [GrpObj BS] (jS : BS₀.left ⟶ BS.left)
    (hBS : IsGrpPullback BS₀ BS (spMap πS) jS), IsAbelianScheme B → SmoothOfRelativeDimension g' B.hom →
    IsAbelianScheme BS → SmoothOfRelativeDimension g' BS.hom →
  ∀ (φB : B.left ⟶ BS.left) (ψB : B₀.left ⟶ BS₀.left), IsGrpPullback B BS (spMap σ) φB →
    IsGrpPullback B₀ BS₀ (spMap ι₀) ψB → j ≫ φB = ψB ≫ jS →
  ∀ (f₀ : A₀ ⟶ B₀) [IsMonHom f₀] (fS₀ : AS₀ ⟶ BS₀) [IsMonHom fS₀], f₀.left ≫ ψB = ψA ≫ fS₀.left →
    (∀ d ∈ liftFil (divided₂ h) hA, push (divided₂ h) (spMap π) f₀ d ∈ liftFil (divided₂ h) hB) →
    ∀ d ∈ liftFil (divided₂ hJ) hAS, push (divided₂ hJ) (spMap πS) fS₀ d ∈ liftFil (divided₂ hJ) hBS := by
  first | exact @GlobalTheory.SqLift.push_mem_liftFil_of_injective | exact GlobalTheory.SqLift.push_mem_liftFil_of_injective | (intros; apply GlobalTheory.SqLift.push_mem_liftFil_of_injective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftHomExistsOfNoetherian
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem liftHom_exists_of_noetherian : AbelianDeRham → (∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R) (hI : I ^ 2 = 0) (R₀ : Type) [CommRing R₀] (π : R →+* R₀),
    Function.Surjective π → RingHom.ker π = I → LiftObj (divided₂ hI) π ∧ LiftHom (divided₂ hI) π) →
  ∀ (R : Type) [CommRing R] (I : Ideal R) (h : I ^ 2 = 0) (R₀ : Type) [CommRing R₀] (π : R →+* R₀),
    Function.Surjective π → RingHom.ker π = I →
  ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A : Over (Sp R)) [GrpObj A] (i : A₀.left ⟶ A.left)
    (hA : IsGrpPullback A₀ A (spMap π) i), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
  ∀ (g' : ℕ) (B₀ : Over (Sp R₀)) [GrpObj B₀] (B : Over (Sp R)) [GrpObj B] (j : B₀.left ⟶ B.left)
    (hB : IsGrpPullback B₀ B (spMap π) j), IsAbelianScheme B → SmoothOfRelativeDimension g' B.hom →
  ∀ (f₀ : A₀ ⟶ B₀) [IsMonHom f₀], (∀ d ∈ liftFil (divided₂ h) hA, push (divided₂ h) (spMap π) f₀ d ∈ liftFil (divided₂ h) hB) →
    ∃ f : A ⟶ B, i ≫ f.left = f₀.left ≫ j := by
  intro P H R _ I h R₀ _ π hπ hker g A₀ _ A _ i hA abA smA g' B₀ _ B _ j hB abB smB f₀ _ hfil
  obtain ⟨S, ι₀, AS₀, _, AS, _, iS, BS₀, _, BS, _, jS, fS₀, φA, φB, ψA, ψB, hfg, hι, _, hAS, hBS, abAS, smAS,
    abBS, smBS, pA, pB, qA, qB, cA, cB, cf⟩ := GlobalTheory.T.abelian_hom_reduction_descends_finitely_generated R I R₀ π hπ hker g A₀ A i hA abA smA g' B₀ B j hB abB smB f₀
  have hS : (I.comap S.subtype) ^ 2 = 0 := by
    rw [Ideal.zero_eq_bot, eq_bot_iff]
    refine (Ideal.le_comap_pow _ 2).trans ?_
    rw [h, Ideal.zero_eq_bot, Ideal.comap_bot_of_injective _ Subtype.val_injective]
  haveI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing ℤ S
  have hfilS := GlobalTheory.T.push_mem_liftFil_of_injective_alt P R I h R₀ π hπ hker S S.subtype Subtype.val_injective (I.comap S.subtype) hS
    (S ⧸ I.comap S.subtype) (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective (Ideal.mk_ker) ι₀ hι
    g A₀ A i hA AS₀ AS iS hAS abA smA abAS smAS φA ψA pA qA cA
    g' B₀ B j hB BS₀ BS jS hBS abB smB abBS smBS φB ψB pB qB cB f₀ fS₀ cf hfil
  obtain ⟨fS, ⟨_, efS⟩, -⟩ := (H S (I.comap S.subtype) hS (S ⧸ I.comap S.subtype) (Ideal.Quotient.mk _)
    Ideal.Quotient.mk_surjective Ideal.mk_ker).2 g AS₀ AS iS hAS abAS smAS g' BS₀ BS jS hBS abBS smBS fS₀ hfilS
  let fl : A.left ⟶ B.left := pB.1.lift (φA ≫ fS.left) A.hom (by
    rw [Category.assoc, Over.w fS, pA.1.w])
  refine ⟨Over.homMk fl (pB.1.lift_snd _ _ _), ?_⟩
  apply pB.1.hom_ext
  · simp only [Over.homMk_left, Category.assoc, fl, pB.1.lift_fst]
    rw [reassoc_of% cA, efS, ← Category.assoc, ← cf, Category.assoc, cB]
  · simp only [Over.homMk_left, Category.assoc, fl, pB.1.lift_snd]
    rw [hA.1.w, hB.1.w, ← Category.assoc, Over.w f₀]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftHomExistsOfNoetherianStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftHom_exists_of_noetherian_alt : AbelianDeRham → (∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R) (hI : I ^ 2 = 0) (R₀ : Type) [CommRing R₀] (π : R →+* R₀),
    Function.Surjective π → RingHom.ker π = I → LiftObj (divided₂ hI) π ∧ LiftHom (divided₂ hI) π) →
  ∀ (R : Type) [CommRing R] (I : Ideal R) (h : I ^ 2 = 0) (R₀ : Type) [CommRing R₀] (π : R →+* R₀),
    Function.Surjective π → RingHom.ker π = I →
  ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A : Over (Sp R)) [GrpObj A] (i : A₀.left ⟶ A.left)
    (hA : IsGrpPullback A₀ A (spMap π) i), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
  ∀ (g' : ℕ) (B₀ : Over (Sp R₀)) [GrpObj B₀] (B : Over (Sp R)) [GrpObj B] (j : B₀.left ⟶ B.left)
    (hB : IsGrpPullback B₀ B (spMap π) j), IsAbelianScheme B → SmoothOfRelativeDimension g' B.hom →
  ∀ (f₀ : A₀ ⟶ B₀) [IsMonHom f₀], (∀ d ∈ liftFil (divided₂ h) hA, push (divided₂ h) (spMap π) f₀ d ∈ liftFil (divided₂ h) hB) →
    ∃ f : A ⟶ B, i ≫ f.left = f₀.left ≫ j := by
  first | exact @GlobalTheory.liftHom_exists_of_noetherian | exact GlobalTheory.liftHom_exists_of_noetherian | (intros; apply GlobalTheory.liftHom_exists_of_noetherian <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrothendieckMessingLiftOfNoetherianCase
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrothendieckMessingLiftOfNoetherianCase
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published
  GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.NoethLiftObj

section Linear

open Module

variable {S R S₀ R₀ : Type} [CommRing S] [CommRing R] [CommRing S₀] [CommRing R₀]
  {P P' P₀ P₀' : Type*} [AddCommGroup P] [Module S P] [AddCommGroup P'] [Module R P']
  [AddCommGroup P₀] [Module S₀ P₀] [AddCommGroup P₀'] [Module R₀ P₀']

theorem exists_frame [Module.Finite S P] [Module.Projective S P] :
    ∃ (n : ℕ) (p : Fin n → P) (l : Fin n → Dual S P), ∀ c, ∑ i, l i c • p i = c := by
  obtain ⟨n, f, g, -, -, h⟩ := Module.Finite.exists_comp_eq_id_of_projective S P
  refine ⟨n, fun i ↦ f (Pi.single i 1), fun i ↦ LinearMap.proj i ∘ₗ g, fun c ↦ ?_⟩
  conv_rhs => rw [← LinearMap.id_apply (R := S) c, ← h, LinearMap.comp_apply, LinearMap.pi_apply_eq_sum_univ]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have : (fun j ↦ if i = j then (1 : S) else 0) = Pi.single i 1 := by
    ext j
    simp [Pi.single_apply, eq_comm]
  rw [this]
  rfl

theorem cor_of_span {σ : S →+* R} {Λ : Type*} {v : Λ → P} (hv : Submodule.span S (Set.range v) = ⊤)
    (f : P →ₛₗ[σ] P') {x : Dual S P} {x' : Dual R P'} (h : ∀ c, x' (f (v c)) = σ (x (v c))) (c : P) :
    x' (f c) = σ (x c) := by
  have hc : c ∈ Submodule.span S (Set.range v) := hv ▸ Submodule.mem_top
  induction hc using Submodule.span_induction with
  | mem _ hc => obtain ⟨c, rfl⟩ := hc; exact h c
  | zero => simp
  | add a b _ _ ha hb => simp [ha, hb]
  | smul r a _ ha => simp [LinearMap.map_smulₛₗ, ha]

theorem frame_bc {σ : S →+* R} {n : ℕ} {p : Fin n → P} {l : Fin n → Dual S P}
    (hp : ∀ c, ∑ i, l i c • p i = c) (f : P →ₛₗ[σ] P') (hf : Submodule.span R (Set.range f) = ⊤)
    {l' : Fin n → Dual R P'} (hl : ∀ i c, l' i (f c) = σ (l i c)) (c : P') :
    ∑ i, l' i c • f (p i) = c := by
  have hc : c ∈ Submodule.span R (Set.range f) := hf ▸ Submodule.mem_top
  induction hc using Submodule.span_induction with
  | mem _ hc =>
    obtain ⟨c, rfl⟩ := hc
    set_option synthInstance.maxHeartbeats 100000 in
      conv_rhs => rw [← hp c, map_sum]
    simp [hl, LinearMap.map_smulₛₗ]
  | zero => simp
  | add a b _ _ ha hb => simp only [map_add (f := _), add_smul, Finset.sum_add_distrib, ha, hb]
  | smul r a _ ha => simp only [map_smul, smul_eq_mul, mul_smul, ← Finset.smul_sum, ha]

theorem dual_frame {n : ℕ} {p : Fin n → P} {l : Fin n → Dual S P}
    (hp : ∀ c, ∑ i, l i c • p i = c) (x : Dual S P) : ∑ i, x (p i) • l i = x := by
  ext c
  set_option synthInstance.maxHeartbeats 100000 in
    conv_rhs => rw [← hp c, map_sum]
  simp [mul_comm]

theorem exists_descent {τ : S →+* S₀} {σ₁ : S₀ →+* R} {σ : S →+* R} (hσ : ∀ a, σ₁ (τ a) = σ a)
    {n : ℕ} {p : Fin n → P} {l : Fin n → Dual S P} (hp : ∀ c, ∑ i, l i c • p i = c)
    (f : P →ₛₗ[σ] P') (hf : Submodule.span R (Set.range f) = ⊤)
    {l' : Fin n → Dual R P'} (hl : ∀ i c, l' i (f c) = σ (l i c))
    (e : Dual R P' →ₗ[R] Dual R P') (b : Fin n → Fin n → S₀) (hb : ∀ i j, σ₁ (b i j) = e (l' i) (f (p j)))
    (f₀ : P →ₛₗ[τ] P₀) (h₀ : Submodule.span S₀ (Set.range f₀) = ⊤)
    (h₀' : ∀ x : Dual S P, ∃ x' : Dual S₀ P₀, ∀ c, x' (f₀ c) = τ (x c))
    (f₁ : P₀ →ₛₗ[σ₁] P') (hc : ∀ c, f₁ (f₀ c) = f c) :
    ∃ e₁ : Dual S₀ P₀ →ₗ[S₀] Dual S₀ P₀, ∀ (x : Dual S₀ P₀) (x' : Dual R P'),
      (∀ c, x' (f₁ c) = σ₁ (x c)) → ∀ c, e x' (f₁ c) = σ₁ (e₁ x c) := by
  choose l₁ hl₁ using fun i ↦ h₀' (l i)
  have k : ∀ i c, l' i (f₁ c) = σ₁ (l₁ i c) := fun i ↦
    cor_of_span h₀ f₁ fun c ↦ by rw [hc, hl, hl₁, hσ]
  have fr := frame_bc hp f hf hl
  refine ⟨∑ i, (LinearMap.applyₗ (f₀ (p i))).smulRight (∑ j, b i j • l₁ j), fun x x' hx c ↦ ?_⟩
  conv_lhs => rw [← dual_frame fr x', ← fr (f₁ c)]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.smulRight_apply,
    LinearMap.applyₗ_apply_apply, smul_eq_mul, map_mul, hb, k, ← hx, hc, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring

theorem red_descent [Module.Projective S P] [Module.Finite R P'] [Module.Projective R P']
    {σ : S →+* R} {π₁ : S →+* S₀} {π : R →+* R₀} {ρ : S₀ →+* R₀} (hρ : Function.Injective ρ)
    (hπ₁ : Function.Surjective π₁) (hsq : ∀ a, ρ (π₁ a) = π (σ a))
    (f : P →ₛₗ[σ] P') (r₁ : P →ₛₗ[π₁] P₀) (r : P' →ₛₗ[π] P₀') (f₀ : P₀ →ₛₗ[ρ] P₀')
    (hc : ∀ c, r (f c) = f₀ (r₁ c))
    (hf : Submodule.span R (Set.range f) = ⊤) (hr₁ : Submodule.span S₀ (Set.range r₁) = ⊤)
    (ef : ∀ x : Dual S P, ∃ x' : Dual R P', ∀ c, x' (f c) = σ (x c))
    (er : ∀ x : Dual R P', ∃ x' : Dual R₀ P₀', ∀ c, x' (r c) = π (x c))
    (ef₀ : ∀ x : Dual S₀ P₀, ∃ x' : Dual R₀ P₀', ∀ c, x' (f₀ c) = ρ (x c))
    (e : Dual R P' →ₗ[R] Dual R P') (he : ∀ x, e (e x) = e x) (e₁ : Dual S P →ₗ[S] Dual S P)
    (hee : ∀ (x : Dual S P) (x' : Dual R P'), (∀ c, x' (f c) = σ (x c)) → ∀ c, e x' (f c) = σ (e₁ x c))
    (W₀ : Submodule S₀ P₀) (W : Submodule R₀ P₀') (hW : W = Submodule.span R₀ (f₀ '' W₀))
    (H : ∀ y, y ∈ W.dualAnnihilator ↔ ∃ x ∈ LinearMap.range e, ∀ c, y (r c) = π (x c)) (y : Dual S₀ P₀) :
    y ∈ W₀.dualAnnihilator ↔ ∃ x ∈ LinearMap.range e₁, ∀ c, y (r₁ c) = π₁ (x c) := by
  constructor
  · intro hy
    obtain ⟨y', hy'⟩ := ef₀ y
    have m : y' ∈ W.dualAnnihilator := by
      rw [Submodule.mem_dualAnnihilator, hW]
      intro c hc
      refine (Submodule.span_le (p := LinearMap.ker y')).2 (fun c hc ↦ ?_) hc
      obtain ⟨c, hc, rfl⟩ := hc
      exact (hy' c).trans (by rw [(Submodule.mem_dualAnnihilator _).1 hy c hc, map_zero])
    obtain ⟨_, ⟨w, rfl⟩, hx'⟩ := (H y').1 m
    letI : Algebra S S₀ := π₁.toAlgebra
    let t : P →ₗ[S] S₀ :=
      { toFun c := y (r₁ c)
        map_add' := by simp
        map_smul' a c := by rw [LinearMap.map_smulₛₗ, map_smul]; rfl }
    obtain ⟨x, hx⟩ := Module.projective_lifting_property (Algebra.linearMap S S₀) t hπ₁
    have hx : ∀ c, π₁ (x c) = y (r₁ c) := fun c ↦ LinearMap.congr_fun hx c
    obtain ⟨x', hxx⟩ := ef x
    have k : ∀ c, y' (r c) = π (x' c) := cor_of_span hf r fun c ↦ by rw [hc, hy', ← hx, hsq, hxx]
    obtain ⟨n, p, l, hp⟩ := exists_frame (S := R) (P := P')
    have z : ∀ c, π (e (x' - e w) c) = 0 := fun c ↦ by
      rw [← dual_frame hp (x' - e w)]
      simp [← k, ← hx']
    refine ⟨_, ⟨x, rfl⟩, fun c ↦ hρ ?_⟩
    have := z (f c)
    rw [map_sub, he, LinearMap.sub_apply, map_sub, sub_eq_zero] at this
    rw [hsq, ← hee x x' hxx, this, ← hx', hc, hy']
  · rintro ⟨_, ⟨x, rfl⟩, hx⟩
    obtain ⟨x', hxx⟩ := ef x
    obtain ⟨y', hy'⟩ := er (e x')
    have m := (H y').2 ⟨_, ⟨x', rfl⟩, hy'⟩
    have k : ∀ c, y' (f₀ c) = ρ (y c) := cor_of_span hr₁ f₀ fun c ↦ by
      rw [← hc, hy', hee x x' hxx, hx, hsq]
    refine (Submodule.mem_dualAnnihilator _).2 fun c hc ↦ hρ ?_
    rw [← k, map_zero]
    exact (Submodule.mem_dualAnnihilator _).1 m _ (hW ▸ Submodule.subset_span ⟨c, hc, rfl⟩)

theorem ann_bc {Q Q' : Type*} [AddCommGroup Q] [Module S Q] [AddCommGroup Q'] [Module R Q']
    [Module.Finite S P] [Module.Projective S P] {σ : S →+* R} (θ : Q ≃ₗ[S] P)
    (f : P →ₛₗ[σ] P') (g : Q →ₛₗ[σ] Q') (hf : Submodule.span R (Set.range f) = ⊤)
    (ef : ∀ x : Dual S P, ∃ x' : Dual R P', ∀ c, x' (f c) = σ (x c))
    (e : Dual R P' →ₗ[R] Dual R P') (e₁ : Dual S P →ₗ[S] Dual S P)
    (hee : ∀ (x : Dual S P) (x' : Dual R P'), (∀ c, x' (f c) = σ (x c)) → ∀ c, e x' (f c) = σ (e₁ x c))
    (W N : Submodule S Q) (hN : IsCompl W N) (W' : Submodule R Q') (hW : W' = Submodule.span R (g '' W))
    (H : ∀ x : Dual S P, x ∈ LinearMap.range e₁ ↔ ∀ c ∈ W, x (θ c) = 0)
    (u : Dual R Q') (v : Dual R P') (huv : ∀ c, u (g c) = v (f (θ c))) :
    u ∈ W'.dualAnnihilator ↔ v ∈ LinearMap.range e := by
  obtain ⟨n, p, l, hp⟩ := exists_frame (S := S) (P := P)
  constructor
  · intro hu
    let q : P →ₗ[S] P := θ.toLinearMap ∘ₗ Submodule.projection _ _ hN.symm ∘ₗ θ.symm.toLinearMap
    have m : ∀ i, l i ∘ₗ q ∈ LinearMap.range e₁ := fun i ↦ (H _).2 fun c hc ↦ by
      simp [q, (Submodule.projection_apply_eq_zero_iff hN.symm).2 hc]
    choose a ha using m
    choose a' ha' using fun i ↦ ef (a i)
    refine ⟨∑ i, v (f (p i)) • a' i, LinearMap.ext_on_range hf fun c ↦ ?_⟩
    obtain ⟨c, rfl⟩ := θ.surjective c
    have z : v (f (θ (Submodule.projection _ _ hN c))) = 0 := by
      rw [← huv]
      exact (Submodule.mem_dualAnnihilator _).1 hu _
        (hW ▸ Submodule.subset_span ⟨_, Submodule.projection_apply_mem hN c, rfl⟩)
    have : v (f (θ c)) = v (f (q (θ c))) := by
      conv_lhs => rw [← Submodule.projection_add_projection_eq_self hN c, map_add (f := _), map_add (f := _), map_add (f := _), z,
        zero_add]
      simp [q]
    rw [this, ← hp (q (θ c))]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hee _ _ (ha' _), ha,
      LinearMap.map_smulₛₗ, smul_eq_mul, LinearMap.comp_apply, mul_comm]
  · rintro ⟨w, rfl⟩
    choose l' hl using fun i ↦ ef (l i)
    rw [Submodule.mem_dualAnnihilator, hW]
    intro c hc
    refine (Submodule.span_le (p := LinearMap.ker u)).2 (fun c hc ↦ ?_) hc
    obtain ⟨c, hc, rfl⟩ := hc
    change u (g c) = 0
    rw [huv, ← dual_frame (frame_bc hp f hf hl) w]
    simp [hee _ _ (hl _), (H _).1 ⟨_, rfl⟩ c hc]

end Linear


open scoped CategoryTheory.Obj in
theorem exists_factor {S S' S'' : Scheme.{0}} {G : Over S} [GrpObj G] {G'' : Over S''} [GrpObj G'']
    {f : S' ⟶ S} {k : S'' ⟶ S'} {t : S'' ⟶ S} {φ : G''.left ⟶ G.left} (h : IsGrpPullback G'' G t φ)
    (e : k ≫ f = t) {g : ℕ} (hG : IsAbelianScheme G) (hg : SmoothOfRelativeDimension g G.hom) :
    ∃ (G' : Over S') (_ : GrpObj G') (ψ : G'.left ⟶ G.left) (χ : G''.left ⟶ G'.left),
      IsGrpPullback G' G f ψ ∧ IsGrpPullback G'' G' k χ ∧ χ ≫ ψ = φ ∧ IsAbelianScheme G' ∧
        SmoothOfRelativeDimension g G'.hom := by
  subst e
  have p := isGrpPullback_pullback G f
  have e₁ := p.1.lift_fst φ (G''.hom ≫ k) (by rw [h.1.w, Category.assoc])
  exact ⟨_, inferInstance, _, _, p, p.cancel (by rw [e₁]; exact h) (p.1.lift_snd _ _ _), e₁,
    PolPull.isAbelianScheme_of_isGrpPullback hG p,
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback p.1 hg⟩

theorem bc_facts (P : AbelianDeRham) {S R : Type} [CommRing S] [CommRing R] {σ : S →+* R} {g : ℕ}
    {B : Over (Sp S)} [GrpObj B] {A : Over (Sp R)} [GrpObj A] {φ : A.left ⟶ B.left}
    (h : IsGrpPullback A B (spMap σ) φ) (hB : IsAbelianScheme B) (hg : SmoothOfRelativeDimension g B.hom) :
    Submodule.span R (Set.range (redMor h).pull) = ⊤ ∧
      (∀ x : HdR B, ∃ x' : HdR A, ∀ c, x' ((redMor h).pull c) = σ (x c)) ∧
      PrimitiveSubmodule A = Submodule.span R ((redMor h).pull '' (PrimitiveSubmodule B)) := by
  letI : Algebra S R := σ.toAlgebra
  obtain ⟨h₁, h₂⟩ := P.2.2.1 S B g hB hg R A φ h
  refine ⟨top_le_iff.1 fun c _ ↦ ?_, h₁.exists, h₂⟩
  obtain ⟨z, rfl⟩ := h₁.2 c
  induction z with
  | add x y hx hy => simpa only [map_add] using add_mem (hx trivial) (hy trivial)
  | tmul x c => rw [liftSemi_tmul]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)

theorem exists_noeth_model (P : AbelianDeRham) {R : Type} [CommRing R] {g : ℕ} (A : Over (Sp R)) [GrpObj A]
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) (e : HdR A →ₗ[R] HdR A) :
    ∃ (S : Type) (_ : CommRing S) (_ : IsNoetherianRing S) (σ : S →+* R) (B : Over (Sp S)) (_ : GrpObj B)
      (φ : A.left ⟶ B.left) (h : IsGrpPullback A B (spMap σ) φ) (e₁ : HdR B →ₗ[S] HdR B),
      Function.Injective σ ∧ IsAbelianScheme B ∧ SmoothOfRelativeDimension g B.hom ∧
      ∀ (x : HdR B) (x' : HdR A), (∀ c, x' ((redMor h).pull c) = σ (x c)) →
        ∀ c, e x' ((redMor h).pull c) = σ (e₁ x c) := by
  obtain ⟨S, B, _, φ, -, hS, hB, hgB, h⟩ := GlobalTheory.T.abelianScheme_descends_to_finitelyGenerated_subring R g A ∅ hA hg
  haveI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing ℤ S
  obtain ⟨hf, hp, -⟩ := P.1.prim hB hgB
  obtain ⟨n, p, l, hpl⟩ := exists_frame (S := S) (P := primDR B)
  obtain ⟨b₁, b₂, -⟩ := bc_facts P h hB hgB
  choose l' hl using fun i ↦ b₂ (l i)
  let a : Fin n × Fin n → R := fun ij ↦ e (l' ij.1) ((redMor h).pull (p ij.2))
  let T := Algebra.adjoin S (Set.range a)
  haveI : Algebra.FiniteType S T := Algebra.FiniteType.adjoin_of_finite (Set.finite_range a)
  haveI : IsNoetherianRing T := Algebra.FiniteType.isNoetherianRing S T
  obtain ⟨C, _, ψ, χ, h₀, h₁, hc, hC, hgC⟩ := exists_factor (f := spMap (algebraMap S T))
    (k := spMap T.val.toRingHom) h (Cris.spMap_comp _ _).symm hB hgB
  obtain ⟨c₁, c₂, -⟩ := bc_facts P h₀ hB hgB
  obtain ⟨e₁, he₁⟩ := exists_descent (τ := algebraMap S T) (σ₁ := T.val.toRingHom) (fun _ ↦ rfl) hpl _ b₁ hl e
    (fun i j ↦ ⟨a (i, j), Algebra.subset_adjoin ⟨_, rfl⟩⟩) (fun _ _ ↦ rfl) _ c₁ c₂ (redMor h₁).pull
    (GrpMor.pull_pull _ _ _ (fun _ ↦ rfl) hc)
  exact ⟨T, inferInstance, inferInstance, _, C, inferInstance, χ, h₁, e₁, Subtype.val_injective, hC, hgC, he₁⟩

theorem liftObj_of_noetherian (P : AbelianDeRham)
    (H : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R) (hI : I ^ 2 = 0) (R₀ : Type) [CommRing R₀]
      (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I → LiftObj (divided₂ hI) π ∧ LiftHom (divided₂ hI) π)
    (R : Type) [CommRing R] (I : Ideal R) (hI : I ^ 2 = 0) (R₀ : Type) [CommRing R₀] (π : R →+* R₀)
    (hπ : Function.Surjective π) (hk : RingHom.ker π = I) : LiftObj (divided₂ hI) π := by
  intro g A₀ _ A' _ i' h' hA hg F ⟨⟨N, hN⟩, hF⟩
  obtain ⟨e, he, rfl⟩ : ∃ e : HdR A' →ₗ[R] HdR A', (∀ x, e (e x) = e x) ∧ F = LinearMap.range e :=
    ⟨Submodule.projection _ _ hN, fun x ↦ Submodule.projection_apply_left hN
      ⟨_, Submodule.projection_apply_mem hN x⟩, (Submodule.range_projection hN).symm⟩
  obtain ⟨S, _, _, σ, B, _, φ, h, e₁, hσ, hB, hgB, hee⟩ := exists_noeth_model P A' hA hg e
  let J : Ideal S := RingHom.ker (π.comp σ)
  have hJI : ∀ a ∈ J, σ a ∈ I := fun a ha ↦ hk ▸ ha
  have hJ : J ^ 2 = 0 := by
    rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
    intro a ha b hb
    have := Ideal.mul_mem_mul (hJI a ha) (hJI b hb)
    rw [← pow_two, hI, Ideal.zero_eq_bot, Ideal.mem_bot, ← map_mul] at this
    exact hσ (this.trans (map_zero σ).symm)
  let π₁ : S →+* S ⧸ J := Ideal.Quotient.mk J
  let ρ : S ⧸ J →+* R₀ := RingHom.kerLift (π.comp σ)
  have hρ : Function.Injective ρ := RingHom.kerLift_injective _
  have hsq : ∀ a, ρ (π₁ a) = π (σ a) := fun _ ↦ rfl
  have sq : spMap ρ ≫ spMap π₁ = spMap π ≫ spMap σ := by
    rw [← Cris.spMap_comp, ← Cris.spMap_comp]; rfl
  obtain ⟨B₀, _, j, ψ, k, k₀, hj, hB₀, hgB₀⟩ := exists_factor (h'.comp h) sq hB hgB
  obtain ⟨b₁, b₂, -⟩ := bc_facts P h hB hgB
  obtain ⟨hf, hp, -⟩ := P.1.prim hB hgB
  have adm : IsAdmissible k (LinearMap.range e₁) := by
    obtain ⟨hf', hp', -⟩ := P.1.prim hA hg
    obtain ⟨-, c₂, c₃⟩ := bc_facts P k₀ hB₀ hgB₀
    refine ⟨⟨LinearMap.ker e₁, LinearMap.IsIdempotentElem.isCompl (LinearMap.ext fun x ↦ ?_)⟩,
      red_descent hρ Ideal.Quotient.mk_surjective hsq (redMor h).pull (redMor k).pull (redMor h').pull
        (redMor k₀).pull (fun c ↦ ?_) b₁ (bc_facts P k hB hgB).1 b₂ (bc_facts P h' hA hg).2.1 c₂ e he e₁ hee
        _ _ c₃ hF⟩
    · obtain ⟨x', hx⟩ := b₂ x
      refine LinearMap.ext fun c ↦ hσ ?_
      rw [← hee x x' hx, ← he]
      exact (hee _ _ (hee x x' hx) c).symm
    · exact (GrpMor.pull_pull _ _ ((redMor h).comp (redMor h')) (fun _ ↦ rfl) rfl c).trans
        (GrpMor.pull_pull _ _ _ hsq hj c).symm
  obtain ⟨C, _, l, hl, hC, hgC, hfil⟩ := (H S J hJ (S ⧸ J) π₁ Ideal.Quotient.mk_surjective
    Ideal.mk_ker).1 g B₀ B j k hB hgB _ adm
  obtain ⟨A, _, χ, i, n, hi, hχ, hA₁, hg₁⟩ := exists_factor (k₀.comp hl) sq.symm hC hgC
  refine ⟨A, inferInstance, i, hi, hA₁, hg₁, Submodule.ext fun d ↦ ?_⟩
  let α := LinearEquiv.ofBijective _ (P.2.2.2.1 S C g hC hgC J _ (isDPNilpotent_squareZero hJ) _ π₁
    Ideal.Quotient.mk_surjective Ideal.mk_ker B₀ l hl)
  let β := LinearEquiv.ofBijective _ (P.2.2.2.1 S B g hB hgB J _ (isDPNilpotent_squareZero hJ) _ π₁
    Ideal.Quotient.mk_surjective Ideal.mk_ker B₀ j k)
  have m : GrpMor (divided₂ hJ) (spMap π₁) B₀ (divided₂ hI) (spMap π) A₀ σ (spMap ρ) ψ :=
    GrpMor.of_isGrpPullback (isDPMorphism_sqDP hJ hI σ hJI) sq k₀
  obtain ⟨-, ⟨M, hM⟩, -⟩ := P.2.1 S C g hC hgC
  refine ann_bc (α.trans β.symm) (redMor h).pull (redMor n).pull b₁ b₂ e e₁ hee _ M hM _
    (bc_facts P n hC hgC).2.2 (fun x ↦ ?_) (crysToDR _ hi d) (crysToDR _ h' d) fun c ↦ ?_
  · have := SetLike.ext_iff.1 hfil (x ∘ₗ β.symm.toLinearMap)
    have e₂ : crysToDR (divided₂ hJ) k (x ∘ₗ β.symm.toLinearMap) = x :=
      LinearMap.ext fun c ↦ congrArg x (β.symm_apply_apply c)
    rw [Submodule.mem_comap (f := crysToDR (divided₂ hJ) k), e₂] at this
    exact this.symm.trans (Submodule.mem_dualAnnihilator _)
  · have e₂ : (liftMor (divided₂ hJ) k).pull (β.symm (α c)) = (liftMor (divided₂ hJ) hl).pull c :=
      β.apply_symm_apply _
    refine congrArg d ?_
    exact (GrpMor.pull_pull (redMor n) (liftMor _ hi) ((liftMor (divided₂ hJ) hl).comp m) (fun _ ↦ rfl)
      hχ c).trans ((GrpMor.pull_pull (liftMor (divided₂ hJ) hl) m _ (fun _ ↦ rfl) rfl c).symm.trans
        ((congrArg m.pull e₂.symm).trans ((GrpMor.pull_pull (liftMor (divided₂ hJ) k) m
          ((liftMor (divided₂ hJ) k).comp m) (fun _ ↦ rfl) rfl _).trans
            (GrpMor.pull_pull (redMor h) (liftMor _ h') _ (fun _ ↦ rfl) hj.symm _).symm)))

end GlobalTheory.NoethLiftObj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrothendieckMessingLiftOfNoetherianCaseStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.grothendieckMessing_lift_of_noetherian_case : AbelianDeRham → (∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R) (hI : I ^ 2 = 0) (R₀ : Type) [CommRing R₀] (π : R →+* R₀),
    Function.Surjective π → RingHom.ker π = I → LiftObj (divided₂ hI) π ∧ LiftHom (divided₂ hI) π) →
  ∀ (R : Type) [CommRing R] (I : Ideal R) (h : I ^ 2 = 0) (R₀ : Type) [CommRing R₀] (π : R →+* R₀),
    Function.Surjective π → RingHom.ker π = I → LiftObj (divided₂ h) π := by
  first | exact @GlobalTheory.NoethLiftObj.liftObj_of_noetherian | exact GlobalTheory.NoethLiftObj.liftObj_of_noetherian | (intros; apply GlobalTheory.NoethLiftObj.liftObj_of_noetherian <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareZeroLiftingOfNoetherianCase
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqLift

theorem sqLifting_of_noetherian : AbelianDeRham → (∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R) (hI : I ^ 2 = 0) (R₀ : Type) [CommRing R₀] (π : R →+* R₀),
    Function.Surjective π → RingHom.ker π = I → LiftObj (divided₂ hI) π ∧ LiftHom (divided₂ hI) π) → SqLifting := by
  intro P H R _ I h R₀ _ π hπ hI
  refine ⟨GlobalTheory.T.grothendieckMessing_lift_of_noetherian_case P H R I h R₀ π hπ hI, ?_⟩
  intro g A₀ _ A _ i hA hAa hg g' B₀ _ B _ j hB hBa hg' f₀ _ hf
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.liftHom_exists_of_noetherian_alt P H R I h R₀ π hπ hI g A₀ A i hA hAa hg g' B₀ B j hB hBa hg' f₀ hf
  exact GlobalTheory.T.existsUnique_isMonHom_lift_of_grpPullback_abelian R R₀ π hπ ⟨2, by rw [hI]; exact h⟩ A₀ B₀ A B i j hA hB hAa hBa f₀ φ hφ

end GlobalTheory.SqLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareZeroLiftingOfNoetherianCaseStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.squareZeroLifting_of_noetherian_case : AbelianDeRham → (∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R) (hI : I ^ 2 = 0) (R₀ : Type) [CommRing R₀] (π : R →+* R₀),
    Function.Surjective π → RingHom.ker π = I → LiftObj (divided₂ hI) π ∧ LiftHom (divided₂ hI) π) → SqLifting := by
  first | exact @GlobalTheory.SqLift.sqLifting_of_noetherian | exact GlobalTheory.SqLift.sqLifting_of_noetherian | (intros; apply GlobalTheory.SqLift.sqLifting_of_noetherian <;> assumption)
end
