module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalChartEvalSquareProperties
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiIsoChainsCechOfIsLocallySurjectiveStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechAugEqvOfIsIntegralHomOfStrictlyHenselian
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCechAugmentationEquivOfSection
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCechAugmentationEquivOfSection
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory

theorem cechAug_eqv_of_section : ∀ (R : Type) [CommRing R] (F : Shv R) (Y X : Scheme.{0}) (f : Y ⟶ X) (s : X ⟶ Y),
    s ≫ f = 𝟙 X → Eqv R (GlobalTheory.EtC.cechAug f) F := by
  intro R _ F Y X f s hs
  have hsec : yoneda.map s ≫ yoneda.map f = 𝟙 (yoneda.obj X) := by
    rw [← yoneda.map_comp, hs, yoneda.map_id]
  have hls : Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} (yoneda.map f) :=
    (GlobalTheory.T.isLocallySurjective_etale_baseChange).2.1 _ _ (yoneda.map f) (yoneda.map s) hsec
  have hq := GlobalTheory.T.quasiIso_chains_cech_of_isLocallySurjective' R (yoneda.obj Y) (yoneda.obj X) (yoneda.map f) hls
  exact ((GlobalTheory.T.etaleCohomologyEquivalence_basic_properties R F).2.2.1 _ _ (GlobalTheory.EtC.cechAug f)) hq

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCechAugmentationEquivOfSectionStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleCechAugmentation_equiv_of_section : ∀ (R : Type) [CommRing R] (F : Shv R) (Y X : Scheme.{0}) (f : Y ⟶ X) (s : X ⟶ Y), s ≫ f = 𝟙 X → Eqv R (GlobalTheory.EtC.cechAug f) F := by
  first | exact @GlobalTheory.cechAug_eqv_of_section | exact GlobalTheory.cechAug_eqv_of_section | (intros; apply GlobalTheory.cechAug_eqv_of_section <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechNerveLevelwiseEquivalenceIntegralPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechNerveLevelwiseEquivalenceIntegralPullback
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory

theorem cech_level_eqv_of_integral_pullback :
    ∀ (R : Type) [CommRing R] (F : Shv R) (Y X Y' X' : Scheme.{0}) (a : Y' ⟶ Y) (f' : Y' ⟶ X') (f : Y ⟶ X) (b : X' ⟶ X),
    IsPullback a f' f b → IsIntegralHom f →
    (∀ (Z Z' : Scheme.{0}) (h : Z ⟶ X) (h' : Z' ⟶ X') (φ : Z' ⟶ Z), IsIntegralHom h → IsPullback φ h' h b → Eqv R (sch.map φ) F) →
    ∀ (m : cech f' ⟶ cech f), IsPullback m (GlobalTheory.EtC.cechAug f') (GlobalTheory.EtC.cechAug f) (sch.map b) → ∀ n, Eqv R (disc.map (m.app n)) F := by
  intro R _ F Y X Y' X' a f' f b hab hf H m hm n
  have hf' : IsIntegralHom f' := MorphismProperty.of_isPullback (P := @IsIntegralHom) hab hf

  have hn : IsPullback (m.app n) ((GlobalTheory.EtC.cechAug f').app n) ((GlobalTheory.EtC.cechAug f).app n) (yoneda.map b) :=
    hm.map ((evaluation SimplexCategoryᵒᵖ PSh).obj n)
  obtain ⟨Z, π, e, hπ, he⟩ := GlobalTheory.T.exists_representable_cech_level_of_stable (@IsIntegralHom) Y X f hf n
  obtain ⟨Z', π', e', hπ', he'⟩ := GlobalTheory.T.exists_representable_cech_level_of_stable (@IsIntegralHom) Y' X' f' hf' n
  have hh : IsIntegralHom (π ≫ f) := inferInstance
  have hh' : IsIntegralHom (π' ≫ f') := inferInstance
  let φ : Z' ⟶ Z := yoneda.preimage (e'.hom ≫ m.app n ≫ e.inv)
  have hφ : yoneda.map φ = e'.hom ≫ m.app n ≫ e.inv := yoneda.map_preimage _
  have hsqY : IsPullback (yoneda.map φ) (yoneda.map (π' ≫ f')) (yoneda.map (π ≫ f)) (yoneda.map b) := by
    refine IsPullback.of_iso hn e'.symm e.symm (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp [hφ]
    · simp [← he']; exact Category.comp_id _
    · simp [← he]; exact Category.comp_id _
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
  have hsq : IsPullback φ (π' ≫ f') (π ≫ f) b := by
    refine IsPullback.of_map yoneda ?_ hsqY
    apply yoneda.map_injective
    simpa using hsqY.w
  have hE := H Z Z' (π ≫ f) (π' ≫ f') φ hh hsq
  obtain ⟨hiso, hcomp, -, -⟩ := GlobalTheory.T.etaleCohomologyEquivalence_basic_properties R F
  have hdec : disc.map (m.app n) = disc.map e'.inv ≫ sch.map φ ≫ disc.map e.hom := by
    change _ = disc.map e'.inv ≫ disc.map (yoneda.map φ) ≫ disc.map e.hom
    simp only [hφ, ← Functor.map_comp, Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hdec]
  exact (hcomp _ _ _ _ _).1 (hiso _ _ (disc.map e'.inv) inferInstance)
    ((hcomp _ _ _ _ _).1 hE (hiso _ _ (disc.map e.hom) inferInstance))

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechNerveLevelwiseEquivalenceIntegralPullbackStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechNerve_levelwise_equivalence_integral_pullback : ∀ (R : Type) [CommRing R] (F : Shv R) (Y X Y' X' : Scheme.{0}) (a : Y' ⟶ Y) (f' : Y' ⟶ X') (f : Y ⟶ X) (b : X' ⟶ X),
    IsPullback a f' f b → IsIntegralHom f →
    (∀ (Z Z' : Scheme.{0}) (h : Z ⟶ X) (h' : Z' ⟶ X') (φ : Z' ⟶ Z), IsIntegralHom h → IsPullback φ h' h b → Eqv R (sch.map φ) F) →
    ∀ (m : cech f' ⟶ cech f), IsPullback m (GlobalTheory.EtC.cechAug f') (GlobalTheory.EtC.cechAug f) (sch.map b) → ∀ n, Eqv R (disc.map (m.app n)) F := by
  first | (exact @GlobalTheory.cech_level_eqv_of_integral_pullback) | (exact GlobalTheory.cech_level_eqv_of_integral_pullback) | (intros; apply GlobalTheory.cech_level_eqv_of_integral_pullback  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyEquivalencePullbackIntegralAffine
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyEquivalencePullbackIntegralAffine
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem eqv_pullback_integral_affine : ∀ (R : Type) [CommRing R] (F : Shv R) (A C : Type) [CommRing A] [CommRing C] [Algebra A C],
    (∀ (B : Type) [CommRing B] [Algebra A B] [Algebra.IsIntegral A B],
      Eqv R (spMap (Algebra.TensorProduct.includeRight : B →ₐ[A] C ⊗[A] B).toRingHom) F) →
    ∀ (Z Z' : Scheme.{0}) (h : Z ⟶ Spec (CommRingCat.of A)) (h' : Z' ⟶ Spec (CommRingCat.of C)) (φ : Z' ⟶ Z),
    IsIntegralHom h → IsPullback φ h' h (Spec.map (CommRingCat.ofHom (algebraMap A C))) → Eqv R (sch.map φ) F := by
  intro R _ F A C _ _ _ hB Z Z' h h' φ hh hP
  have E := GlobalTheory.T.etaleCohomologyEquivalence_basic_properties R F
  haveI : IsAffine Z := isAffine_of_isAffineHom h

  set f : CommRingCat.of A ⟶ Γ(Z, ⊤) := Spec.preimage (Z.isoSpec.inv ≫ h) with hf
  have hfh : Z.isoSpec.hom ≫ Spec.map f = h := by
    rw [hf, Spec.map_preimage, Iso.hom_inv_id_assoc]
  have hint : IsIntegralHom (Spec.map f) := by
    have : Spec.map f = Z.isoSpec.inv ≫ h := by rw [hf, Spec.map_preimage]
    rw [this]; infer_instance
  letI : Algebra A Γ(Z, ⊤) := f.hom.toAlgebra
  haveI : Algebra.IsIntegral A Γ(Z, ⊤) := ⟨IsIntegralHom.SpecMap_iff.mp hint⟩
  have hsq := (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct A C Γ(Z, ⊤))).flip
  have hsq' : IsPullback
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : Γ(Z, ⊤) →ₐ[A] C ⊗[A] Γ(Z, ⊤)).toRingHom) ≫ Z.isoSpec.inv)
      (Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom)) h
      (Spec.map (CommRingCat.ofHom (algebraMap A C))) := by
    have hr : IsPullback Z.isoSpec.inv (Spec.map f) h (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by rw [← hfh, Iso.inv_hom_id_assoc, Category.comp_id]⟩
    simpa using IsPullback.paste_horiz hsq hr
  let e := IsPullback.isoIsPullback _ _ hP hsq'
  have he : φ = e.hom ≫ (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : Γ(Z, ⊤) →ₐ[A] C ⊗[A] Γ(Z, ⊤)).toRingHom) ≫ Z.isoSpec.inv) :=
    (IsPullback.isoIsPullback_hom_fst _ _ hP hsq').symm
  rw [he, Functor.map_comp, Functor.map_comp]
  refine (E.2.1 _ _ _ _ _).1 (E.1 _ _ _ inferInstance) ((E.2.1 _ _ _ _ _).1 (hB Γ(Z, ⊤)) (E.1 _ _ _ inferInstance))

end GlobalTheory.EtC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyEquivalencePullbackIntegralAffineStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleCohomologyEquivalence_pullback_integral_affine : ∀ (R : Type) [CommRing R] (F : Shv R) (A C : Type) [CommRing A] [CommRing C] [Algebra A C],
    (∀ (B : Type) [CommRing B] [Algebra A B] [Algebra.IsIntegral A B],
      Eqv R (spMap (Algebra.TensorProduct.includeRight : B →ₐ[A] C ⊗[A] B).toRingHom) F) →
    ∀ (Z Z' : Scheme.{0}) (h : Z ⟶ Spec (CommRingCat.of A)) (h' : Z' ⟶ Spec (CommRingCat.of C)) (φ : Z' ⟶ Z),
    IsIntegralHom h → IsPullback φ h' h (Spec.map (CommRingCat.ofHom (algebraMap A C))) → Eqv R (sch.map φ) F := by
  first | (exact @GlobalTheory.EtC.eqv_pullback_integral_affine) | (exact GlobalTheory.EtC.eqv_pullback_integral_affine) | (intros; apply GlobalTheory.EtC.eqv_pullback_integral_affine  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveLocallyConstantComapAlgClosureTensorOfH
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveLocallyConstantComapAlgClosureTensorOfH
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

noncomputable section

namespace GlobalTheory

open IsLocalRing

theorem locallyConstant_eq_of_specializes {Y Λ : Type*} [TopologicalSpace Y]
    (φ : LocallyConstant Y Λ) {y y' : Y} (h : y ⤳ y') : φ y = φ y' :=
  h.mem_open (φ.isLocallyConstant.isOpen_fiber (φ y')) rfl

theorem mem_iff_of_specializes_of_isClopen {Y : Type*} [TopologicalSpace Y] {V : Set Y}
    (hV : IsClopen V) {y y' : Y} (h : y ⤳ y') : y ∈ V ↔ y' ∈ V :=
  ⟨fun hy ↦ h.mem_closed hV.1 hy, fun hy ↦ h.mem_open hV.2 hy⟩

theorem bijective_locallyConstant_comap_of_specializes_of_isClopen {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (Λ : Type*) (f : C(X, Y))
    (h1 : ∀ y : Y, ∃ x : X, y ⤳ f x)
    (h2 : ∀ U : Set X, IsClopen U → ∃ V : Set Y, IsClopen V ∧ f ⁻¹' V = U) :
    Function.Bijective (fun φ : LocallyConstant Y Λ ↦ φ.comap f) := by
  choose g hg using h1
  refine ⟨fun φ ψ hφψ ↦ ?_, fun ψ ↦ ?_⟩
  · ext y
    have h : (φ.comap f) (g y) = (ψ.comap f) (g y) := by
      rw [show φ.comap f = ψ.comap f from hφψ]
    rw [locallyConstant_eq_of_specializes φ (hg y), locallyConstant_eq_of_specializes ψ (hg y)]
    simpa using h
  · have key : ∀ l : Λ, ∃ V : Set Y, IsClopen V ∧ f ⁻¹' V = {x | ψ x = l} ∧
        (fun y ↦ ψ (g y)) ⁻¹' {l} = V := by
      intro l
      obtain ⟨V, hV, hVU⟩ := h2 _ (ψ.isLocallyConstant.isClopen_fiber l)
      refine ⟨V, hV, hVU, ?_⟩
      ext y
      show ψ (g y) = l ↔ y ∈ V
      rw [mem_iff_of_specializes_of_isClopen hV (hg y)]
      change ψ (g y) = l ↔ g y ∈ f ⁻¹' V
      rw [hVU]
      rfl
    refine ⟨⟨fun y ↦ ψ (g y), IsLocallyConstant.iff_isOpen_fiber.2 fun l ↦ ?_⟩, ?_⟩
    · obtain ⟨V, hV, -, hV'⟩ := key l
      rw [hV']
      exact hV.2
    · ext x
      obtain ⟨V, -, hVU, hV'⟩ := key (ψ x)
      have hx : x ∈ f ⁻¹' V := by rw [hVU]; rfl
      rw [← hV'] at hx
      exact hx

theorem map_maximalIdeal_le_of_isIntegral (A B : Type*) [CommRing A] [IsLocalRing A] [CommRing B]
    [Algebra A B] [Algebra.IsIntegral A B] (M : Ideal B) [M.IsMaximal] :
    (maximalIdeal A).map (algebraMap A B) ≤ M := by
  rw [Ideal.map_le_iff_le_comap]
  have : (M.comap (algebraMap A B)).IsMaximal :=
    Ideal.isMaximal_under_of_isIntegral_of_isMaximal M
  exact (IsLocalRing.eq_maximalIdeal this).ge

theorem exists_isIdempotentElem_lift_quotient_of_isIntegral (A B : Type) [CommRing A]
    [HenselianLocalRing A] [CommRing B] [Algebra A B] [Algebra.IsIntegral A B]
    {c : B ⧸ (maximalIdeal A).map (algebraMap A B)} (hc : IsIdempotentElem c) :
    ∃ e : B, IsIdempotentElem e ∧ Ideal.Quotient.mk _ e = c := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
  have hb : b * b - b ∈ (maximalIdeal A).map (algebraMap A B) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hc.eq, sub_self]
  have hb' : b * b - b ∈ Submodule.span B (algebraMap A B '' (maximalIdeal A : Set A)) := hb
  obtain ⟨n, r, s, hs⟩ := Submodule.mem_span_set'.1 hb'
  choose a ha hsa using fun i ↦ (s i).2
  set B₀ := Algebra.adjoin A (insert b (Set.range r)) with hB₀
  haveI : Module.Finite A B₀ := Algebra.finite_adjoin_of_finite_of_isIntegral
    ((Set.finite_range r).insert b) fun x _ ↦ Algebra.IsIntegral.isIntegral x
  let b₀ : B₀ := ⟨b, Algebra.subset_adjoin (Set.mem_insert _ _)⟩
  let r₀ : Fin n → B₀ := fun i ↦ ⟨r i, Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨i, rfl⟩)⟩
  have hsum : b₀ * b₀ - b₀ = ∑ i, r₀ i * algebraMap A B₀ (a i) := by
    apply Subtype.ext
    show b * b - b = B₀.val (∑ i, r₀ i * algebraMap A B₀ (a i))
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, ← hs]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_mul, AlgHom.commutes, hsa i, smul_eq_mul]
    rfl
  have hb₀ : b₀ * b₀ - b₀ ∈ (maximalIdeal A).map (algebraMap A B₀) := by
    rw [hsum]
    exact Ideal.sum_mem _ fun i _ ↦ Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (ha i))
  obtain ⟨e₀, ⟨he₀, he₀b⟩, -⟩ := existsUnique_idempotent_lift_quotient A (S := B₀)
    (c := Ideal.Quotient.mk _ b₀) (by
      show Ideal.Quotient.mk _ b₀ * Ideal.Quotient.mk _ b₀ = Ideal.Quotient.mk _ b₀
      rw [← map_mul, Ideal.Quotient.eq]
      exact hb₀)
  refine ⟨(e₀ : B), he₀.map B₀.val, ?_⟩
  have h := Ideal.mem_map_of_mem (B₀.val : B₀ →+* B) (Ideal.Quotient.eq.1 he₀b)
  rw [Ideal.map_map, AlgHom.comp_algebraMap] at h
  rw [Ideal.Quotient.eq]
  simpa using h

theorem bijective_locallyConstant_comap_algebraicClosure_tensor : ∀ (Λ : Type) (A : Type) [CommRing A] [IsLocalRing A] [HenselianLocalRing A] [IsSepClosed (IsLocalRing.ResidueField A)] (B : Type) [CommRing B] [Algebra A B] [Algebra.IsIntegral A B], Function.Bijective (fun φ : LocallyConstant (PrimeSpectrum B) Λ => φ.comap ⟨PrimeSpectrum.comap (Algebra.TensorProduct.includeRight : B →ₐ[A] AlgebraicClosure (IsLocalRing.ResidueField A) ⊗[A] B).toRingHom, PrimeSpectrum.continuous_comap _⟩) := by
  intro Λ A _ _ _ _ B _ _ _
  let k := ResidueField A
  let Ω := AlgebraicClosure k
  let I : Ideal B := (maximalIdeal A).map (algebraMap A B)
  let ιk : B →ₐ[A] k ⊗[A] B := Algebra.TensorProduct.includeRight
  let μ : k ⊗[A] B →+* Ω ⊗[A] B :=
    (Algebra.TensorProduct.map (Algebra.ofId k Ω) (AlgHom.id A B)).toRingHom
  have hμ : IsHomeomorph (PrimeSpectrum.comap μ) :=
    PrimeSpectrum.isHomeomorph_comap_tensorProductMap_of_isPurelyInseparable (R := A) (K := k)
      (S := B) Ω
  have hIk : ∀ x ∈ I, ιk x = 0 := by
    intro x hx
    have hle : I ≤ RingHom.ker ιk := by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap, RingHom.mem_ker]
      show ιk (algebraMap A B a) = 0
      rw [AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply,
        show algebraMap A k a = 0 from (IsLocalRing.residue_eq_zero_iff a).2 ha, zero_tmul]
    exact hle hx
  let e' : B ⧸ I →+* k ⊗[A] B := Ideal.Quotient.lift I ιk.toRingHom hIk
  have he'mk : ∀ b : B, e' (Ideal.Quotient.mk I b) = ιk b := fun b ↦ rfl
  let σ : k →ₐ[A] B ⧸ I := Ideal.Quotient.liftₐ (maximalIdeal A) (Algebra.ofId A (B ⧸ I))
    fun a ha ↦ by
      rw [Algebra.ofId_apply]
      show Ideal.Quotient.mk I (algebraMap A B a) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ ha)
  let τ : k ⊗[A] B →ₐ[A] B ⧸ I :=
    Algebra.TensorProduct.lift σ (Ideal.Quotient.mkₐ A I) fun _ _ ↦ Commute.all _ _
  have hτ : ∀ q, τ (e' q) = q := by
    intro q
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
    rw [he'mk]
    show τ ((1 : k) ⊗ₜ[A] b) = _
    simp [τ]
  have he' : Function.Bijective e' := by
    refine ⟨Function.LeftInverse.injective hτ, fun y ↦ ?_⟩
    obtain ⟨b, rfl⟩ := includeRight_residueField_surjective A B y
    exact ⟨Ideal.Quotient.mk I b, rfl⟩
  let ρ : B ⧸ I →+* Ω ⊗[A] B := μ.comp e'
  have hρ : IsHomeomorph (PrimeSpectrum.comap ρ) := by
    rw [PrimeSpectrum.comap_comp]
    exact (PrimeSpectrum.isHomeomorph_comap_of_bijective he').comp hμ
  have hfac : ∀ x : PrimeSpectrum (Ω ⊗[A] B),
      PrimeSpectrum.comap (Algebra.TensorProduct.includeRight : B →ₐ[A] Ω ⊗[A] B).toRingHom x =
        PrimeSpectrum.comap (Ideal.Quotient.mk I) (PrimeSpectrum.comap ρ x) := by
    intro x
    have : (Algebra.TensorProduct.includeRight : B →ₐ[A] Ω ⊗[A] B).toRingHom =
        ρ.comp (Ideal.Quotient.mk I) := by
      ext b
      show (1 : Ω) ⊗ₜ[A] b = μ ((1 : k) ⊗ₜ[A] b)
      simp [μ]
    rw [this]
    rfl
  apply bijective_locallyConstant_comap_of_specializes_of_isClopen
  · intro y
    obtain ⟨M, hM, hyM⟩ := Ideal.exists_le_maximal y.asIdeal y.isPrime.ne_top
    have hIM : I ≤ M := map_maximalIdeal_le_of_isIntegral A B M
    haveI := hM.isPrime
    let P : PrimeSpectrum (B ⧸ I) := ⟨M.map (Ideal.Quotient.mk I),
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])⟩
    have hPM : (PrimeSpectrum.comap (Ideal.Quotient.mk I) P).asIdeal = M := by
      show (M.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I) = M
      rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
        Ideal.mk_ker, sup_eq_left.2 hIM]
    obtain ⟨x, hx⟩ := hρ.surjective P
    refine ⟨x, ?_⟩
    rw [← PrimeSpectrum.le_iff_specializes, ← PrimeSpectrum.asIdeal_le_asIdeal]
    show y.asIdeal ≤ (PrimeSpectrum.comap
      (Algebra.TensorProduct.includeRight : B →ₐ[A] Ω ⊗[A] B).toRingHom x).asIdeal
    rw [hfac, hx, hPM]
    exact hyM
  · intro U hU
    have hU' : IsClopen (PrimeSpectrum.comap ρ '' U) :=
      ⟨hρ.isClosedMap U hU.1, hρ.isOpenMap U hU.2⟩
    set c := PrimeSpectrum.isIdempotentElemEquivClopens.symm ⟨_, hU'⟩ with hc
    obtain ⟨e, he, hec⟩ := exists_isIdempotentElem_lift_quotient_of_isIntegral A B c.2
    have hU'c : (PrimeSpectrum.basicOpen (Ideal.Quotient.mk I e) : Set (PrimeSpectrum (B ⧸ I))) =
        PrimeSpectrum.comap ρ '' U := by
      rw [hec]
      exact congrArg SetLike.coe (PrimeSpectrum.basicOpen_isIdempotentElemEquivClopens_symm _)
    refine ⟨PrimeSpectrum.basicOpen e, ?_, ?_⟩
    · have := (PrimeSpectrum.isIdempotentElemEquivClopens ⟨e, he⟩).isClopen
      rwa [PrimeSpectrum.coe_isIdempotentElemEquivClopens_apply] at this
    · ext x
      change PrimeSpectrum.comap (Algebra.TensorProduct.includeRight : B →ₐ[A] Ω ⊗[A] B).toRingHom x ∈
        PrimeSpectrum.basicOpen e ↔ x ∈ U
      rw [hfac, PrimeSpectrum.mem_basicOpen, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap,
        ← PrimeSpectrum.mem_basicOpen, ← SetLike.mem_coe, hU'c, hρ.injective.mem_set_image]

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveLocallyConstantComapAlgClosureTensorOfHStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bijective_locallyConstant_comap_algClosure_tensor_of_henselian : ∀ (Λ : Type) (A : Type) [CommRing A] [IsLocalRing A] [HenselianLocalRing A] [IsSepClosed (IsLocalRing.ResidueField A)] (B : Type) [CommRing B] [Algebra A B] [Algebra.IsIntegral A B], Function.Bijective (fun φ : LocallyConstant (PrimeSpectrum B) Λ => φ.comap ⟨PrimeSpectrum.comap (Algebra.TensorProduct.includeRight : B →ₐ[A] AlgebraicClosure (IsLocalRing.ResidueField A) ⊗[A] B).toRingHom, PrimeSpectrum.continuous_comap _⟩) := by
  first | exact @GlobalTheory.bijective_locallyConstant_comap_algebraicClosure_tensor | exact GlobalTheory.bijective_locallyConstant_comap_algebraicClosure_tensor | (intros; apply GlobalTheory.bijective_locallyConstant_comap_algebraicClosure_tensor <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointAlgClosureResidueFieldOfIntegralSurje
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointAlgClosureResidueFieldOfIntegralSurje
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory

theorem exists_ringHom_algClosure_residueField_of_isIntegral (A B : Type) [CommRing A]
    [IsLocalRing A] [CommRing B] (φ : A →+* B) (hφ : φ.IsIntegral) (P : Ideal B) [P.IsPrime]
    (hP : P.comap φ = IsLocalRing.maximalIdeal A) :
    ∃ ψ : B →+* AlgebraicClosure (IsLocalRing.ResidueField A),
      ψ.comp φ = algebraMap A (AlgebraicClosure (IsLocalRing.ResidueField A)) := by
  letI : Algebra A B := φ.toAlgebra
  haveI : Algebra.IsIntegral A B := ⟨hφ⟩
  haveI : P.LiesOver (IsLocalRing.maximalIdeal A) := ⟨hP.symm⟩
  letI : Algebra (IsLocalRing.ResidueField A) (B ⧸ P) :=
    Ideal.Quotient.algebraOfLiesOver P (IsLocalRing.maximalIdeal A)
  haveI : IsScalarTower A (IsLocalRing.ResidueField A) (B ⧸ P) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.IsIntegral A (B ⧸ P) := inferInstance
  haveI : Algebra.IsIntegral (IsLocalRing.ResidueField A) (B ⧸ P) :=
    Algebra.IsIntegral.tower_top (R := A)
  let l : (B ⧸ P) →ₐ[IsLocalRing.ResidueField A] AlgebraicClosure (IsLocalRing.ResidueField A) :=
    IsAlgClosed.lift
  refine ⟨l.toRingHom.comp (Ideal.Quotient.mk P), ?_⟩
  ext a
  have h := l.commutes (algebraMap A (IsLocalRing.ResidueField A) a)
  rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at h
  exact h

theorem exists_point_algClosure_residueField_of_isIntegralHom :
    ∀ (A : Type) [CommRing A] [IsLocalRing A] (Y : Scheme.{0}) (g : Y ⟶ Spec (CommRingCat.of A)),
    IsIntegralHom g → Surjective g → ∃ s : Spec (CommRingCat.of (AlgebraicClosure (IsLocalRing.ResidueField A))) ⟶ Y,
    s ≫ g = Spec.map (CommRingCat.ofHom (algebraMap A (AlgebraicClosure (IsLocalRing.ResidueField A)))) := by
  intro A _ _ Y g hi hs
  haveI : IsAffine Y := isAffine_of_isAffineHom g
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (Y.isoSpec.inv ≫ g)
  have h1 : IsIntegralHom (Spec.map φ) := by rw [hφ]; infer_instance
  have h2 : Surjective (Spec.map φ) := by rw [hφ]; infer_instance
  have h3 : φ.hom.IsIntegral := IsIntegralHom.SpecMap_iff.mp h1
  obtain ⟨P, hP⟩ := h2.surj (IsLocalRing.closedPoint A)
  have hP' : (PrimeSpectrum.asIdeal P).comap φ.hom = IsLocalRing.maximalIdeal A :=
    congrArg PrimeSpectrum.asIdeal hP
  haveI := PrimeSpectrum.isPrime P
  obtain ⟨ψ, hψ⟩ := exists_ringHom_algClosure_residueField_of_isIntegral A Γ(Y, ⊤) φ.hom h3
    (PrimeSpectrum.asIdeal P) hP'
  refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ Y.isoSpec.inv, ?_⟩
  rw [Category.assoc, ← hφ, ← Spec.map_comp, ← hψ]
  rfl

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointAlgClosureResidueFieldOfIntegralSurjeStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_point_algClosure_residueField_of_integral_surjective : ∀ (A : Type) [CommRing A] [IsLocalRing A] (Y : Scheme.{0}) (g : Y ⟶ Spec (CommRingCat.of A)),
    IsIntegralHom g → Surjective g → ∃ s : Spec (CommRingCat.of (AlgebraicClosure (IsLocalRing.ResidueField A))) ⟶ Y,
    s ≫ g = Spec.map (CommRingCat.ofHom (algebraMap A (AlgebraicClosure (IsLocalRing.ResidueField A)))) := by
  first | exact @GlobalTheory.exists_point_algClosure_residueField_of_isIntegralHom | exact GlobalTheory.exists_point_algClosure_residueField_of_isIntegralHom | (intros; apply GlobalTheory.exists_point_algClosure_residueField_of_isIntegralHom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechAugEqvOfIsIntegralHomOfStrictlyHenselian
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.IntDescent

theorem isIntegral_algClosure_residue (A : Type) [CommRing A] [IsLocalRing A] :
    Algebra.IsIntegral A (AlgebraicClosure (IsLocalRing.ResidueField A)) := by
  haveI : Algebra.IsIntegral A (IsLocalRing.ResidueField A) :=
    Algebra.IsIntegral.of_surjective (Algebra.ofId A (IsLocalRing.ResidueField A)) IsLocalRing.residue_surjective
  haveI : Algebra.IsIntegral (IsLocalRing.ResidueField A) (AlgebraicClosure (IsLocalRing.ResidueField A)) :=
    Algebra.IsAlgebraic.isIntegral
  exact Algebra.IsIntegral.trans (IsLocalRing.ResidueField A)

theorem isIntegral_tensor (A C B : Type) [CommRing A] [CommRing C] [CommRing B] [Algebra A C] [Algebra A B]
    [Algebra.IsIntegral A C] [Algebra.IsIntegral A B] : Algebra.IsIntegral A (C ⊗[A] B) := by
  constructor
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact isIntegral_zero
  | tmul x y =>
      have h1 : IsIntegral A (Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := C) (B := B) x) :=
        (Algebra.IsIntegral.isIntegral x).map _
      have h2 : IsIntegral A (Algebra.TensorProduct.includeRight (R := A) (A := C) (B := B) y) :=
        (Algebra.IsIntegral.isIntegral y).map _
      have := h1.mul h2
      simpa [Algebra.TensorProduct.tmul_mul_tmul] using this
  | add x y hx hy => exact hx.add hy

theorem L1 : ∀ (q : ℕ) (i : ℤ) (A : Type) [CommRing A] [HenselianLocalRing A] [IsSepClosed (IsLocalRing.ResidueField A)],
    IsUnit (q : A) → ∀ (B : Type) [CommRing B] [Algebra A B] [Algebra.IsIntegral A B],
    Eqv (ZMod q) (spMap (Algebra.TensorProduct.includeRight : B →ₐ[A] AlgebraicClosure (IsLocalRing.ResidueField A) ⊗[A] B).toRingHom) (tw q i) := by
  intro q i A _ _ _ hq B _ _ _
  have hSH : SH A := ⟨inferInstance, inferInstance⟩
  obtain ⟨ζ0⟩ := GlobalTheory.T.nonempty_cyclotomicPrimitiveRoots_of_strictlyHenselian q A hSH hq
  let ζ : Prim q Γ(Spec (CommRingCat.of A), ⊤) := ζ0.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  have hgen := GlobalTheory.T.tateTwist_isFreeRankOne_on_generatorSection q i (Spec (CommRingCat.of A)) ζ
  haveI := isIntegral_algClosure_residue A
  haveI := isIntegral_tensor A (AlgebraicClosure (IsLocalRing.ResidueField A)) B
  have hfin := GlobalTheory.T.tateTwist_finitary q i
  have hU := GlobalTheory.T.integral_strictHenselian_acyclic_finitary (ZMod q) (tw q i) hfin A B hSH
  have hU' := GlobalTheory.T.integral_strictHenselian_acyclic_finitary (ZMod q) (tw q i) hfin A (AlgebraicClosure (IsLocalRing.ResidueField A) ⊗[A] B) hSH
  have hbij := GlobalTheory.T.bijective_locallyConstant_comap_algClosure_tensor_of_henselian (ZMod q) A B
  exact GlobalTheory.T.etaleCohomologyEquiv_of_locallyConstant_bijective (ZMod q) (tw q i) _ _ hgen (Spec (CommRingCat.of B)) _
    (Spec.map (CommRingCat.ofHom (algebraMap A B))) _ hU hU' hbij

end GlobalTheory.EtC.IntDescent

namespace GlobalTheory.EtC


open IntDescent in
theorem cechAug_eqv_of_isIntegralHom_of_strictlyHenselian : ∀ (q : ℕ) (i : ℤ) (A : Type) [CommRing A], SH A → IsUnit (q : A) →
    ∀ (Y : Scheme.{0}) (g : Y ⟶ Spec (CommRingCat.of A)), IsIntegralHom g → Surjective g → Eqv _ (cechAug g) (tw q i) := by
  intro q i A _ hSH hq Y g hg hsurj
  obtain ⟨_, _⟩ := hSH
  set Ω := AlgebraicClosure (IsLocalRing.ResidueField A)
  set u : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of A) := Spec.map (CommRingCat.ofHom (algebraMap A Ω)) with hu_def
  have hpb : IsPullback (pullback.fst g u) (pullback.snd g u) g u := IsPullback.of_hasPullback g u
  obtain ⟨m, hm, -⟩ := GlobalTheory.T.etaleCechNerve_baseChange_isPullback _ _ _ _ (pullback.fst g u) (pullback.snd g u) g u hpb
  have hsq : ∀ (Z Z' : Scheme.{0}) (h : Z ⟶ Spec (CommRingCat.of A)) (h' : Z' ⟶ Spec (CommRingCat.of Ω)) (φ : Z' ⟶ Z),
      IsIntegralHom h → IsPullback φ h' h u → Eqv (ZMod q) (sch.map φ) (tw q i) :=
    GlobalTheory.T.etaleCohomologyEquivalence_pullback_integral_affine (ZMod q) (tw q i) A Ω (fun B _ _ _ => L1 q i A hq B)
  have hEm : Eqv (ZMod q) m (tw q i) :=
    GlobalTheory.T.levelwiseEquivalence_isEquivalence (ZMod q) m (tw q i) (GlobalTheory.T.cechNerve_levelwise_equivalence_integral_pullback (ZMod q) (tw q i) _ _ _ _ _ _ g u hpb hg hsq m hm)
  have hEu : Eqv (ZMod q) (sch.map u) (tw q i) :=
    hsq _ _ (𝟙 _) (𝟙 _) u inferInstance (IsPullback.id_vert u)
  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_point_algClosure_residueField_of_integral_surjective A Y g hg hsurj
  have hEs : Eqv (ZMod q) (cechAug (pullback.snd g u)) (tw q i) :=
    GlobalTheory.T.etaleCechAugmentation_equiv_of_section (ZMod q) (tw q i) _ _ (pullback.snd g u) (pullback.lift s (𝟙 _) (by rw [hs, Category.id_comp]))
      (pullback.lift_snd _ _ _)
  obtain ⟨-, hcomp, -, -⟩ := GlobalTheory.T.etaleCohomologyEquivalence_basic_properties (ZMod q) (tw q i)
  have h1 : Eqv (ZMod q) (cechAug (pullback.snd g u) ≫ sch.map u) (tw q i) :=
    (hcomp _ _ _ _ _).1 hEs hEu
  rw [← hm.w] at h1
  exact (hcomp _ _ _ _ _).2.1 hEm h1

end GlobalTheory.EtC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechAugEqvOfIsIntegralHomOfStrictlyHenselianStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eqv_cechAug_of_isIntegralHom_of_surjective_of_sh : ∀ (q : ℕ) (i : ℤ) (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ (Y : Scheme.{0}) (g : Y ⟶ Spec (CommRingCat.of A)), IsIntegralHom g → Surjective g → Eqv _ (cechAug g) (tw q i) := by
  first
  | exact @GlobalTheory.EtC.cechAug_eqv_of_isIntegralHom_of_strictlyHenselian
  | exact GlobalTheory.EtC.cechAug_eqv_of_isIntegralHom_of_strictlyHenselian
  | (intros; apply GlobalTheory.EtC.cechAug_eqv_of_isIntegralHom_of_strictlyHenselian <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSurjectionCechDescentTateTwist
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem eqv_cechAug_of_comp_iso (R : Type) [CommRing R] (F : Shv R) {V W T : Scheme.{0}} (g : V ⟶ W) (t : W ⟶ T) [IsIso t]
    (h : Eqv R (cechAug (g ≫ t)) F) : Eqv R (cechAug g) F := by
  have E := GlobalTheory.T.etaleCohomologyEquivalence_basic_properties R F
  let e : Arrow.mk (yoneda.map g) ≅ Arrow.mk (yoneda.map (g ≫ t)) :=
    Arrow.isoMk (Iso.refl _) (yoneda.mapIso (asIso t)) (by simp)
  let φ := SimplicialObject.augmentedCechNerve.mapIso e
  have hw : φ.hom.left ≫ cechAug (g ≫ t) = cechAug g ≫ (SimplicialObject.const _).map φ.hom.right := φ.hom.w
  have hl : IsIso φ.hom.left := (SimplicialObject.Augmented.drop.mapIso φ).isIso_hom
  have hr : IsIso ((SimplicialObject.const _).map φ.hom.right) := by
    have : IsIso φ.hom.right := (SimplicialObject.Augmented.point.mapIso φ).isIso_hom
    infer_instance
  have h1 : Eqv R (φ.hom.left ≫ cechAug (g ≫ t)) F := ((E.2.1 _ _ _ _ _).1 (E.1 _ _ _ hl)) h
  rw [hw] at h1
  exact (E.2.1 _ _ _ _ _).2.2 (E.1 _ _ _ hr) h1

theorem b4 : B4 := by
  intro q Y X f _ _ hq i
  have E := GlobalTheory.T.etaleCohomologyEquivalence_basic_properties (ZMod q) (tw q i)
  refine GlobalTheory.T.equiv_of_stalkwise_base_change (ZMod q) (tw q i) X (cech f) (sch.obj X) (cechAug f) (sch.map (𝟙 X))
    (GlobalTheory.T.tateTwist_finitary q i) ?_ ?_ ?_
  · intro k
    obtain ⟨Z, π, e, hπ, he⟩ := GlobalTheory.T.exists_representable_cech_level_of_stable @IsIntegralHom Y X f ‹_› k
    haveI := hπ
    refine ⟨Z, π ≫ f, e, inferInstance, inferInstance, ?_⟩
    rw [CategoryTheory.Functor.map_id, Category.comp_id, he]
  · intro k
    refine ⟨X, 𝟙 X, Iso.refl _, inferInstance, inferInstance, ?_⟩
    simp [sch]
  · intro O _ s hs
    obtain ⟨e₁, e₂, h⟩ := GlobalTheory.T.baseChange_cechNerveAugmentation_iso X X Y (𝟙 X) f (Over.mk s)
    have hqO : IsUnit ((q : ℕ) : O) := by
      have := hq.map (s.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of O)).hom).hom
      simpa using this
    have hg : Eqv _ (cechAug (pullback.snd f (pullback.fst (𝟙 X) (Over.mk s).hom))) (tw q i) :=
      eqv_cechAug_of_comp_iso _ _ _ (pullback.snd (𝟙 X) s)
        (GlobalTheory.T.eqv_cechAug_of_isIntegralHom_of_surjective_of_sh q i O hs.1 hqO _ _ inferInstance inferInstance)
    have hm : (bcMap (cechAug f) (sch.map (𝟙 X))).app (Over.mk s) =
        e₁.inv ≫ cechAug (pullback.snd f (pullback.fst (𝟙 X) (Over.mk s).hom)) ≫ e₂.hom := by
      rw [← h, Iso.inv_hom_id_assoc]
    rw [hm]
    exact (E.2.1 _ _ _ _ _).1 (E.1 _ _ _ inferInstance) ((E.2.1 _ _ _ _ _).1 hg (E.1 _ _ _ inferInstance))

end GlobalTheory.EtC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSurjectionCechDescentTateTwistStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralSurjection_cechDescent_tateTwist : GlobalTheory.EtC.B4 := by
  first | (exact @GlobalTheory.EtC.b4) | (exact GlobalTheory.EtC.b4) | (intros; apply GlobalTheory.EtC.b4  <;> assumption)
end
