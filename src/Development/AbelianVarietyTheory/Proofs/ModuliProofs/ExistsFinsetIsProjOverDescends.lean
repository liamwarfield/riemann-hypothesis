module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueComapEqVanishingIdeal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFinsetIsProjOverDescends
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFinsetIsProjOverDescends
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.ProjSpace

theorem baseChange_appLE_chartAlgEquiv {R R' : Type} [CommRing R] [CommRing R'] (N : ℕ) (φ : R →+* R')
    (i : Fin (N + 1)) (q : MvPolynomial {j // j ≠ i} R) :
    ((baseChange N φ).appLE (chart R N i) (chart R' N i) (baseChange_preimage_chart N φ i).ge).hom
      (chartAlgEquiv R N i q) = chartAlgEquiv R' N i (MvPolynomial.map φ q) := by
  have h : ((baseChange N φ).appLE (chart R N i) (chart R' N i)
      (baseChange_preimage_chart N φ i).ge).hom.comp (RingHomClass.toRingHom (chartAlgEquiv R N i)) =
      (RingHomClass.toRingHom (chartAlgEquiv R' N i)).comp (MvPolynomial.map φ) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun j => ?_)
    · simp only [RingHom.comp_apply, RingHom.coe_coe, MvPolynomial.map_C]
      have h1 : chartAlgEquiv R N i (MvPolynomial.C r) = _ := (chartAlgEquiv R N i).commutes r
      have h2 : chartAlgEquiv R' N i (MvPolynomial.C (φ r)) = _ := (chartAlgEquiv R' N i).commutes (φ r)
      rw [h1, h2, ← formOn_C (i := i) (hi := le_rfl), ← formOn_C (i := i) (hi := le_rfl)]
      have h3 := baseChange_app_formOn φ (le_refl (chart R N i)) (MvPolynomial.isHomogeneous_C _ r)
      refine (congrArg (resG _ (baseChange_preimage_chart N φ i).ge) h3).trans ?_
      rw [resG_formOn]
      congr 1
      exact MvPolynomial.map_C _ _
    · simp only [RingHom.comp_apply, RingHom.coe_coe, MvPolynomial.map_X, chartAlgEquiv_X]
      have h3 := baseChange_app_ratioOn φ (le_refl (chart R N i)) j.1
      exact congrArg (resG _ (baseChange_preimage_chart N φ i).ge) h3
  exact congrArg (fun ψ => ψ q) h


set_option backward.isDefEq.respectTransparency false in
theorem comap_map_baseChange {R R' : Type} [CommRing R] [CommRing R'] (N : ℕ) (φ : R →+* R')
    (I : (PSpace R' N).IdealSheafData) (T : ∀ i : Fin (N + 1), Set (MvPolynomial {j // j ≠ i} R'))
    (hT : ∀ i, Ideal.span (chartAlgEquiv R' N i '' T i) = I.ideal ⟨_, isAffineOpen_chart R' N i⟩)
    (hφ : ∀ i, T i ⊆ Set.range (MvPolynomial.map φ)) :
    (I.map (baseChange N φ)).comap (baseChange N φ) = I := by
  have : IsAffineHom (baseChange N φ) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) (isPullback_baseChange N φ).flip inferInstance
  refine le_antisymm (Scheme.IdealSheafData.comap_map_le _ _) ?_
  refine Scheme.IdealSheafData.le_of_iSup_eq_top
    (fun i => ⟨_, isAffineOpen_chart R' N i⟩) (iSup_chart R' N) fun i => ?_
  rw [← hT, Ideal.span_le]
  rintro _ ⟨t, ht, rfl⟩
  obtain ⟨q, rfl⟩ := hφ i ht
  have h0 : chartAlgEquiv R' N i (MvPolynomial.map φ q) ∈ I.ideal ⟨_, isAffineOpen_chart R' N i⟩ := by
    rw [← hT]
    exact Ideal.subset_span ⟨_, ht, rfl⟩
  rw [← baseChange_appLE_chartAlgEquiv] at h0 ⊢
  refine GlobalTheory.GaloisDescent.ideal_le_comap_appLE (baseChange N φ) le_rfl ⟨_, isAffineOpen_chart R N i⟩
    ⟨_, isAffineOpen_chart R' N i⟩ (baseChange_preimage_chart N φ i).ge ?_
  rw [Scheme.IdealSheafData.ideal_map_of_isAffineHom, Ideal.mem_comap]
  have h1 := I.ideal_le_comap_ideal
    (U := ⟨_, (isAffineOpen_chart R N i).preimage (baseChange N φ)⟩)
    (V := ⟨_, isAffineOpen_chart R' N i⟩) (baseChange_preimage_chart N φ i).le h0
  rw [Ideal.mem_comap, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map] at h1
  rw [Scheme.Hom.app_eq_appLE]
  exact h1

end GlobalTheory.ProjSpace

namespace GlobalTheory


open ProjSpace in
theorem exists_finset_isProjOver_descends : ∀ (K : Type) [Field K] (K₀ : Subfield K) (X : Scheme.{0}) (p : X ⟶ Sp K), IsProjOver p → ∃ s : Finset K, ∀ K₁ : Subfield K, K₀ ≤ K₁ → (s : Set K) ⊆ K₁ → ∃ (X₁ : Scheme.{0}) (p₁ : X₁ ⟶ Sp K₁) (φ : X ⟶ X₁), IsProjOver p₁ ∧ IsPullback φ p p₁ (spMap K₁.subtype) := by
  classical
  rintro K _ K₀ X p ⟨N, e, he, rfl⟩
  have hT : ∀ i : Fin (N + 1), ∃ T : Finset (MvPolynomial {j // j ≠ i} K),
      Ideal.span (chartAlgEquiv K N i '' T) = e.ker.ideal ⟨_, isAffineOpen_chart K N i⟩ := fun i => by
    obtain ⟨T, hT⟩ := (IsNoetherian.noetherian
      ((e.ker.ideal ⟨_, isAffineOpen_chart K N i⟩).comap (chartAlgEquiv K N i)))
    refine ⟨T, ?_⟩
    have := congrArg (Ideal.map (chartAlgEquiv K N i)) hT
    rw [Ideal.map_comap_of_surjective _ (chartAlgEquiv K N i).surjective] at this
    rw [← this]
    exact (Ideal.map_span _ _).symm
  choose T hT using hT
  refine ⟨Finset.univ.biUnion fun i => (T i).biUnion MvPolynomial.coeffs, fun K₁ _ hs => ?_⟩
  have key := comap_map_baseChange N K₁.subtype e.ker (fun i => T i) hT fun i t ht => by
    apply MvPolynomial.mem_range_map_iff_coeffs_subset.2
    intro c hc
    refine ⟨⟨c, hs ?_⟩, rfl⟩
    simp only [Finset.coe_biUnion, Set.mem_iUnion]
    exact ⟨i, Finset.mem_univ i, t, ht, hc⟩
  rw [Scheme.IdealSheafData.map_ker] at key
  refine ⟨(e ≫ baseChange N K₁.subtype).image, (e ≫ baseChange N K₁.subtype).imageι ≫ PSpace.str K₁ N,
    (e ≫ baseChange N K₁.subtype).toImage, ⟨N, _, inferInstance, rfl⟩, ?_⟩
  have h := isPullback_of_isClosedImmersion e (e ≫ baseChange N K₁.subtype).imageι
    (e ≫ baseChange N K₁.subtype).toImage (baseChange N K₁.subtype) (by simp)
    (by rw [← key]; congr 1; exact Scheme.IdealSheafData.ker_subschemeι _)
  exact h.flip.paste_vert (isPullback_baseChange N K₁.subtype)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFinsetIsProjOverDescendsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
theorem _root_.GlobalTheory.T.exists_finset_isProjOver_descends_to_subfield : ∀ (K : Type) [Field K] (K₀ : Subfield K) (X : Scheme.{0}) (p : X ⟶ Sp K), IsProjOver p → ∃ s : Finset K, ∀ K₁ : Subfield K, K₀ ≤ K₁ → (s : Set K) ⊆ K₁ → ∃ (X₁ : Scheme.{0}) (p₁ : X₁ ⟶ Sp K₁) (φ : X ⟶ X₁), IsProjOver p₁ ∧ IsPullback φ p p₁ (spMap K₁.subtype) := by
  first | exact @GlobalTheory.exists_finset_isProjOver_descends | exact GlobalTheory.exists_finset_isProjOver_descends | (intros; apply GlobalTheory.exists_finset_isProjOver_descends <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionOfDimOfFinrankDerivatio
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.SmoothTangent

theorem exists_section_of_ker_sq_eq_bot {k B F : Type*} [CommRing k] [CommRing B] [CommRing F]
    [Algebra k B] [Algebra k F] [Algebra.FormallySmooth k F] (π : B →ₐ[k] F)
    (hπ : Function.Surjective π) (h : RingHom.ker π.toRingHom ^ 2 = ⊥) :
    ∃ g : F →ₐ[k] B, π.comp g = AlgHom.id k F :=
  ⟨_, Algebra.FormallySmooth.comp_liftOfSurjective (AlgHom.id k F) π hπ ⟨2, h⟩⟩

theorem kerCotangentToTensor_injective (k R F : Type*) [CommRing k] [CommRing R] [CommRing F]
    [Algebra k R] [Algebra k F] [Algebra R F] [IsScalarTower k R F] [Algebra.FormallySmooth k F]
    (hs : Function.Surjective (algebraMap R F)) :
    Function.Injective (KaehlerDifferential.kerCotangentToTensor k R F) := by
  have hsurj : Function.Surjective (IsScalarTower.toAlgHom k R F).kerSquareLift :=
    fun x ↦ by
      obtain ⟨y, rfl⟩ := hs x
      exact ⟨Ideal.Quotient.mk _ y, rfl⟩
  have hnil : RingHom.ker (IsScalarTower.toAlgHom k R F).kerSquareLift.toRingHom ^ 2 = ⊥ := by
    rw [AlgHom.ker_kerSquareLift, Ideal.cotangentIdeal_square]
  obtain ⟨g, hg⟩ := exists_section_of_ker_sq_eq_bot _ hsurj hnil
  obtain ⟨l, hl⟩ := (retractionKerCotangentToTensorEquivSection (R := k) hs).symm ⟨g, hg⟩
  exact Function.LeftInverse.injective (g := l) fun x ↦ congr($hl x)

noncomputable def derivationEquivDual (k R C : Type*) [CommRing k] [CommRing R] [CommRing C]
    [Algebra k R] [Algebra k C] [Algebra R C] [IsScalarTower k R C] :
    Derivation k R C ≃ₗ[C] Module.Dual C (C ⊗[R] Ω[R⁄k]) :=
  (({ (KaehlerDifferential.linearMapEquivDerivation k R (M := C)).toAddEquiv with
      map_smul' := fun _ _ ↦ rfl } : (Ω[R⁄k] →ₗ[R] C) ≃ₗ[C] Derivation k R C).symm).trans
    (LinearMap.liftBaseChangeEquiv C)

theorem finrank_cotangent_le_finrank_derivation (k : Type*) [Field k] [PerfectField k]
    {R : Type*} [CommRing R] [Algebra k R] [Algebra.FiniteType k R] (m : Ideal R) [m.IsMaximal]
    (C : Type*) [Field C] [Algebra k C] [Algebra R C] [IsScalarTower k R C]
    [Algebra (R ⧸ m) C] [IsScalarTower R (R ⧸ m) C] :
    Module.finrank (R ⧸ m) m.Cotangent ≤ Module.finrank C (Derivation k R C) := by
  let := Ideal.Quotient.field m
  have : Module.Finite k (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing _ _
  have : Algebra.FormallyEtale k (R ⧸ m) := Algebra.FormallyEtale.of_isSeparable k _
  have hs : Function.Surjective (algebraMap R (R ⧸ m)) := Ideal.Quotient.mk_surjective
  have hinj := kerCotangentToTensor_injective k R (R ⧸ m) hs
  let e : m.Cotangent →ₗ[R] (R ⧸ m) ⊗[R] Ω[R⁄k] :=
    KaehlerDifferential.kerCotangentToTensor k R (R ⧸ m) ∘ₗ
      (Ideal.Cotangent.equivOfEq _ _ Ideal.mk_ker.symm).toLinearMap
  have he : Function.Injective (e.extendScalarsOfSurjective hs) :=
    hinj.comp (Ideal.Cotangent.equivOfEq _ _ Ideal.mk_ker.symm).injective
  rw [(derivationEquivDual k R C).finrank_eq, Subspace.dual_finrank_eq,
    ← (TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ m) C C Ω[R⁄k]).finrank_eq,
    Module.finrank_baseChange]
  exact LinearMap.finrank_le_finrank_of_injective he

theorem le_height_of_forall_minimalPrimes (k : Type) [Field k] {R : Type} [CommRing R]
    [Algebra k R] [Algebra.FiniteType k R] {d : ℕ}
    (hd : ∀ q ∈ minimalPrimes R, (d : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ q))
    (m : Ideal R) [m.IsMaximal] : (d : ℕ∞) ≤ m.height := by
  obtain ⟨p, hp, hpm⟩ := Ideal.exists_minimalPrimes_le (bot_le : ⊥ ≤ m)
  have := hp.1.1
  obtain ⟨n, h₁, h₂⟩ := GlobalTheory.exists_ringKrullDim_eq_and_trdeg_eq k (R ⧸ p)
  have hdn : (d : ℕ∞) ≤ n := by
    have := hd p hp
    rw [h₁] at this
    exact_mod_cast this
  have hψ : Function.Surjective (Ideal.Quotient.mk p) := Ideal.Quotient.mk_surjective
  have hcm : (m.map (Ideal.Quotient.mk p)).comap (Ideal.Quotient.mk p) = m := by
    rw [Ideal.comap_map_of_surjective _ hψ, sup_eq_left]
    exact Ideal.mk_ker.le.trans hpm
  have : (m.map (Ideal.Quotient.mk p)).IsMaximal := by
    refine (Ideal.map_eq_top_or_isMaximal_of_surjective _ hψ inferInstance).resolve_left fun h ↦ ?_
    rw [h, Ideal.comap_top] at hcm
    exact Ideal.IsMaximal.ne_top inferInstance hcm.symm
  have h := height_le_height_comap_of_surjective _ hψ (m.map (Ideal.Quotient.mk p))
  rw [hcm, ReciprocityTheory.CA.height_eq_of_isMaximal_of_trdeg_eq_field n h₂] at h
  exact hdn.trans h

end GlobalTheory.SmoothTangent

namespace GlobalTheory

open SmoothTangent

theorem smoothOfRelativeDimension_of_dim_of_finrank_derivation_le :
    ∀ (k : Type) [Field k] [CharZero k] (e : k →+* ℂ) (R : Type) [CommRing R] [Algebra k R] (d : ℕ),
      Algebra.FiniteType k R →
      (∀ q ∈ minimalPrimes R, (d : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ q)) →
      (∀ [Algebra k ℂ] [Algebra R ℂ] [IsScalarTower k R ℂ], algebraMap k ℂ = e →
        Module.finrank ℂ (Derivation k R ℂ) ≤ d) →
      SmoothOfRelativeDimension d (spMap (algebraMap k R)) := by
  intro k _ _ e R _ _ d _ hd ht
  have : Algebra.FinitePresentation k R := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  have key (m : Ideal R) (hm : m.IsMaximal) :
      ∃ f ∉ m, Algebra.IsStandardSmoothOfRelativeDimension d k (Localization.Away f) := by
    have h₁ : (d : WithBot ℕ∞) ≤ ringKrullDim (Localization.AtPrime m) := by
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height m (Localization.AtPrime m)]
      exact_mod_cast le_height_of_forall_minimalPrimes k hd m
    have h₂ : Module.finrank (R ⧸ m) m.Cotangent ≤ d := by
      let := Ideal.Quotient.field m
      have : Module.Finite k (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing _ _
      let : Algebra k ℂ := e.toAlgebra
      let φ : (R ⧸ m) →ₐ[k] ℂ := (by
        refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
        solve_by_elim* (maxDepth := 2) only [*,
          @_root_.DivisionSemiring.to_moduleIsTorsionFree,
          @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
      let : Algebra (R ⧸ m) ℂ := φ.toRingHom.toAlgebra
      let : Algebra R ℂ := (φ.toRingHom.comp (Ideal.Quotient.mk m)).toAlgebra
      have : IsScalarTower R (R ⧸ m) ℂ := .of_algebraMap_eq fun _ ↦ rfl
      have : IsScalarTower k R ℂ := .of_algebraMap_eq fun x ↦ (φ.commutes x).symm
      exact (finrank_cotangent_le_finrank_derivation k m ℂ).trans (ht rfl)
    obtain ⟨-, -, -, h₃, -, h₄⟩ := isSmoothAt_of_finrank_cotangent_le_of_perfectField k m h₁ h₂
    exact exists_isStandardSmoothOfRelativeDimension_of_isSmoothAt k m h₄
  refine (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension d)).mpr ?_
  refine ⟨{f | Algebra.IsStandardSmoothOfRelativeDimension d k (Localization.Away f)}, ?_, ?_⟩
  · by_contra h
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h
    obtain ⟨f, hf, hs⟩ := key m hm
    exact hf (hle (Ideal.subset_span hs))
  · intro f hf
    have := (RingHom.isStandardSmoothOfRelativeDimension_algebraMap d).mpr hf
    rwa [IsScalarTower.algebraMap_eq k R] at this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TateIsometryOfFiniteLevelIsometries
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TateIsometryOfFiniteLevelIsometries
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.TateTower

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def LevelIso (D : Datum H) {K : Type} [Field K] {Q : Type} [Group Q] (act : 𝓞 E → Q → Q)
    (e : ℕ → Q → Q → Kˣ → Prop) (N : ℕ) (p : Kˣ × (D.La → Q)) : Prop :=
  IsPrimitiveRoot p.1 N ∧ (∀ a c, p.2 (a + c) = p.2 a * p.2 c) ∧ (∀ (c : 𝓞 E) a, p.2 (c • a) = act c (p.2 a)) ∧
    (∀ a, p.2 a = 1 ↔ ∃ c, a = N • c) ∧ (∀ x, x ^ N = 1 ↔ ∃ a, p.2 a = x) ∧
    ∀ a c, e N (p.2 a) (p.2 c) (p.1 ^ D.EF a c)

variable {D : Datum H} {K : Type} [Field K] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → Kˣ → Prop}

theorem map_nsmul_of_add {M : Type} [AddCommGroup M] {f : M → Q} (hf : ∀ a c, f (a + c) = f a * f c)
    (n : ℕ) (a : M) : f (n • a) = f a ^ n :=
  map_nsmul (AddMonoidHom.mk' (fun a => Additive.ofMul (f a)) hf) n a

theorem nsmul_cancel (D : Datum H) {r : ℕ} (hr : 0 < r) {a c : D.La} (h : r • a = r • c) : a = c := by
  have := D.proj
  have : Module.Flat ℤ D.La := Module.Flat.trans ℤ (𝓞 E) D.La
  have h' : (r : ℤ) • a = (r : ℤ) • c := by simpa only [natCast_zsmul] using h
  exact smul_right_injective D.La (by exact_mod_cast hr.ne' : (r : ℤ) ≠ 0) h'

theorem LevelIso.pow
    (he : ∀ n m x x' c, 0 < n → 0 < m → x ^ (n * m) = 1 → x' ^ (n * m) = 1 → e (n * m) x x' c →
      e n (x ^ m) (x' ^ m) (c ^ m))
    {N r : ℕ} (hN : 0 < N) (hr : 0 < r) {p : Kˣ × (D.La → Q)} (h : LevelIso D act e (N * r) p) :
    LevelIso D act e N (p ^ r) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have hp : ∀ a, (p ^ r).2 a = p.2 (r • a) := fun a => (map_nsmul_of_add h2 r a).symm
  refine ⟨h1.pow (Nat.mul_pos hN hr) (mul_comm _ _), fun a c => ?_, fun c a => ?_, fun a => ?_, fun x => ?_,
    fun a c => ?_⟩
  · rw [hp, hp, hp, smul_add, h2]
  · rw [hp, hp, smul_comm, h3]
  · rw [hp, h4]
    refine exists_congr fun c => ⟨fun h => nsmul_cancel D hr ?_, fun h => ?_⟩
    · rw [h, mul_comm, mul_smul]
    · rw [h, mul_comm, mul_smul]
  · constructor
    · intro hx
      obtain ⟨a, rfl⟩ := (h5 x).1 (by rw [pow_mul, hx, one_pow])
      rw [← map_nsmul_of_add h2, h4] at hx
      obtain ⟨c, hc⟩ := hx
      rw [mul_smul] at hc
      exact ⟨c, by rw [hp, nsmul_cancel D hN hc]⟩
    · rintro ⟨a, rfl⟩
      rw [hp, ← map_nsmul_of_add h2, h4]
      exact ⟨a, by rw [mul_smul]⟩
  · have := he N r _ _ _ hN hr ((h5 _).2 ⟨a, rfl⟩) ((h5 _).2 ⟨c, rfl⟩) (h6 a c)
    have e1 : (p.1 ^ D.EF a c) ^ r = (p.1 ^ r) ^ D.EF a c := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
    rw [e1] at this
    exact this

theorem finite_levelIso {N : ℕ} (hN : 0 < N) (hQ : Finite {x : Q // x ^ N = 1}) :
    {p | LevelIso D act e N p}.Finite := by
  have := D.fin
  have hf : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  obtain ⟨S, hS, hSf⟩ := AddGroup.fg_iff.1 (Module.Finite.iff_addGroup_fg.1 hf)
  have := hSf.to_subtype
  have hQ' : {x : Q | x ^ N = 1}.Finite := hQ
  have hζ : {ζ : Kˣ | ζ ^ N = 1}.Finite := by
    have : NeZero N := ⟨hN.ne'⟩
    have : Finite (rootsOfUnity N K) := inferInstance
    exact this
  refine Set.Finite.of_finite_image (f := fun p => (p.1, fun s : S => p.2 s))
    ((hζ.prod (Set.Finite.pi' (fun _ : S => hQ'))).subset ?_) ?_
  · rintro _ ⟨p, hp, rfl⟩
    exact ⟨hp.1.pow_eq_one, fun s => (hp.2.2.2.2.1 _).2 ⟨_, rfl⟩⟩
  · intro p hp q hq h
    refine Prod.ext (Prod.ext_iff.1 h).1 (funext fun a => ?_)
    have := AddMonoidHom.eq_of_eqOn_dense hS
      (f := AddMonoidHom.mk' (fun a => Additive.ofMul (p.2 a)) hp.2.1)
      (g := AddMonoidHom.mk' (fun a => Additive.ofMul (q.2 a)) hq.2.1)
      (fun s hs => congrFun (Prod.ext_iff.1 h).2 ⟨s, hs⟩)
    exact DFunLike.congr_fun this a

theorem tateIso_of_levels : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (K : Type) [Field K] (Q : Type) [Group Q] (act : 𝓞 E → Q → Q) (e : ℕ → Q → Q → Kˣ → Prop) (k : ℕ) (z : K) (κ : Type) (lam : κ → D.La) (y : κ → Q), 0 < k → (∀ n, 0 < n → Finite {x : Q // x ^ n = 1}) → (∀ n m x x' c, 0 < n → 0 < m → x ^ (n * m) = 1 → x' ^ (n * m) = 1 → e (n * m) x x' c → e n (x ^ m) (x' ^ m) (c ^ m)) → (∀ m, 0 < m → ∃ (ζ : Kˣ) (ev : D.La → Q), IsPrimitiveRoot ζ (k * m) ∧ (∀ a c, ev (a + c) = ev a * ev c) ∧ (∀ (c : 𝓞 E) a, ev (c • a) = act c (ev a)) ∧ (∀ a, ev a = 1 ↔ ∃ c, a = (k * m) • c) ∧ (∀ x, x ^ (k * m) = 1 ↔ ∃ a, ev a = x) ∧ (∀ a c, e (k * m) (ev a) (ev c) (ζ ^ D.EF a c)) ∧ (ζ : K) ^ m = z ∧ ∀ i, ev (lam i) ^ m = y i) → ∃ I : TateIso D K Q act e, (I.ζ k : K) = z ∧ ∀ i, I.ev k (lam i) = y i := by
  intro E _ _ _ H D K _ Q _ act e k z κ lam y hk hQ he hex
  have hx : ∀ j : ℕ, ∃ p : Kˣ × (D.La → Q), LevelIso D act e (k * j.factorial) p ∧
      (p.1 : K) ^ j.factorial = z ∧ ∀ i, p.2 (lam i) ^ j.factorial = y i := fun j => by
    obtain ⟨ζ, ev, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hex _ j.factorial_pos
    exact ⟨(ζ, ev), ⟨h1, h2, h3, h4, h5, h6⟩, h7, h8⟩
  choose x hx hz hy using hx
  let U : Ultrafilter ℕ := Ultrafilter.of Filter.atTop
  have hU : ∀ n, 0 < n → ∀ᶠ j : ℕ in U, n ∣ k * j.factorial := fun n hn =>
    Ultrafilter.of_le _ ((Filter.eventually_ge_atTop n).mono fun j hj =>
      Dvd.dvd.mul_left (Nat.dvd_factorial hn hj) k)
  have hs : ∀ n, 0 < n → ∃ s, LevelIso D act e n s ∧ ∀ᶠ j in U, x j ^ (k * j.factorial / n) = s := fun n hn => by
    have hm : {p | LevelIso D act e n p} ∈ U.map fun j => x j ^ (k * j.factorial / n) := by
      refine (hU n hn).mono fun j hj => ?_
      have hj' := hx j
      have hpos := Nat.mul_pos hk j.factorial_pos
      rw [← Nat.mul_div_cancel' hj] at hj'
      exact hj'.pow he hn (Nat.div_pos (Nat.le_of_dvd hpos hj) hn)
    obtain ⟨s, h1, h2⟩ := Ultrafilter.eq_pure_of_finite_mem (finite_levelIso hn (hQ n hn)) hm
    refine ⟨s, h1, ?_⟩
    have : {s} ∈ U.map fun j => x j ^ (k * j.factorial / n) := by
      rw [h2]
      exact rfl
    exact this
  have hs' : ∀ n, ∃ s, LevelIso D act e (max n 1) s ∧ ∀ᶠ j in U, x j ^ (k * j.factorial / max n 1) = s :=
    fun n => hs _ (by omega)
  choose s hs1 hs2 using hs'
  have hs3 : ∀ n, 0 < n → LevelIso D act e n (s n) := fun n hn => by
    have := hs1 n
    rwa [max_eq_left hn] at this
  have hs4 : ∀ n, 0 < n → ∀ᶠ j in U, x j ^ (k * j.factorial / n) = s n := fun n hn => by
    have := hs2 n
    rwa [max_eq_left hn] at this
  have htow : ∀ n m, 0 < n → 0 < m → s (n * m) ^ m = s n := fun n m hn hm => by
    have hnm := Nat.mul_pos hn hm
    obtain ⟨j, h1, h2, c, h3⟩ := ((hs4 _ hnm).and ((hs4 n hn).and (hU _ hnm))).exists
    rw [← h1, ← h2, h3, ← pow_mul, Nat.mul_div_cancel_left _ hnm, Nat.mul_assoc, Nat.mul_div_cancel_left _ hn,
      mul_comm c m]
  obtain ⟨j, hj⟩ := (hs4 k hk).exists
  rw [Nat.mul_div_cancel_left _ hk] at hj
  refine ⟨⟨fun n => (s n).1, fun n hn => (hs3 n hn).1, fun n m hn hm => congrArg Prod.fst (htow n m hn hm),
    fun n => (s n).2, fun n => (hs1 n).2.1, fun n => (hs1 n).2.2.1, fun n hn => (hs3 n hn).2.2.2.1,
    fun n hn => (hs3 n hn).2.2.2.2.1, fun n m hn hm a => congrFun (congrArg Prod.snd (htow n m hn hm)) a,
    fun n hn => (hs3 n hn).2.2.2.2.2⟩, ?_, fun i => ?_⟩
  · show ((s k).1 : K) = z
    rw [← hj, ← hz j]
    exact Units.val_pow_eq_pow_val _ _
  · show (s k).2 (lam i) = y i
    rw [← hj, ← hy j i]
    rfl

end GlobalTheory.TateTower
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TateIsometryOfFiniteLevelIsometriesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateIsometry_of_finiteLevel_isometries : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (K : Type) [Field K] (Q : Type) [Group Q] (act : 𝓞 E → Q → Q) (e : ℕ → Q → Q → Kˣ → Prop) (k : ℕ) (z : K) (κ : Type) (lam : κ → D.La) (y : κ → Q), 0 < k → (∀ n, 0 < n → Finite {x : Q // x ^ n = 1}) → (∀ n m x x' c, 0 < n → 0 < m → x ^ (n * m) = 1 → x' ^ (n * m) = 1 → e (n * m) x x' c → e n (x ^ m) (x' ^ m) (c ^ m)) → (∀ m, 0 < m → ∃ (ζ : Kˣ) (ev : D.La → Q), IsPrimitiveRoot ζ (k * m) ∧ (∀ a c, ev (a + c) = ev a * ev c) ∧ (∀ (c : 𝓞 E) a, ev (c • a) = act c (ev a)) ∧ (∀ a, ev a = 1 ↔ ∃ c, a = (k * m) • c) ∧ (∀ x, x ^ (k * m) = 1 ↔ ∃ a, ev a = x) ∧ (∀ a c, e (k * m) (ev a) (ev c) (ζ ^ D.EF a c)) ∧ (ζ : K) ^ m = z ∧ ∀ i, ev (lam i) ^ m = y i) → ∃ I : TateIso D K Q act e, (I.ζ k : K) = z ∧ ∀ i, I.ev k (lam i) = y i := by
  first | exact @GlobalTheory.TateTower.tateIso_of_levels | exact GlobalTheory.TateTower.tateIso_of_levels | (intros; apply GlobalTheory.TateTower.tateIso_of_levels <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LatContMapContinuous
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem latCont_discrete {E : Type} [NormedAddCommGroup E] (H : AddSubgroup E) (r : ℝ) (hr : 0 < r)
    (h : ∀ z ∈ H, ‖z‖ < r → z = 0) : DiscreteTopology H := by
  apply discreteTopology_of_isOpen_singleton_zero
  have e : ({0} : Set H) = Subtype.val ⁻¹' Metric.ball (0 : E) r := by
    ext z
    simp only [Set.mem_singleton_iff, Set.mem_preimage, Metric.mem_ball, dist_zero_right]
    constructor
    · rintro rfl
      simpa using hr
    · intro hz
      have := h z z.2 hz
      simpa using this
  rw [e]
  exact Metric.isOpen_ball.preimage continuous_subtype_val

noncomputable def latContMap {E J : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype J]
    (v : J → E) : (J → ℝ) →L[ℝ] E :=
  ∑ i, (ContinuousLinearMap.proj i : (J → ℝ) →L[ℝ] ℝ).smulRight (v i)

theorem latContMap_apply {E J : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype J]
    (v : J → E) (c : J → ℝ) : latContMap v c = ∑ i, c i • v i := by
  simp [latContMap]

theorem latContMap_repr {La E J : Type} [AddCommGroup La] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype J] (e : Module.Basis J ℤ La) (p : La →+ E) (n : J → ℤ) :
    latContMap (fun i => p (e i)) (fun i => (n i : ℝ)) = p (e.equivFun.symm n) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [latContMap_apply, Module.Basis.equivFun_symm_apply, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_zsmul, Int.cast_smul_eq_zsmul]

theorem latCont_card {La E J : Type} [AddCommGroup La] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Fintype J] (e : Module.Basis J ℤ La) (p : La →+ E)
    (hd : DiscreteTopology p.range) (hi : Function.Injective p)
    (hs : Submodule.span ℝ (Set.range p) = ⊤) :
    Module.finrank ℝ (J → ℝ) = Module.finrank ℝ E := by
  let L : Submodule ℤ E := AddSubgroup.toIntSubmodule p.range
  have : DiscreteTopology L := hd
  have : IsZLattice ℝ L := ⟨by simpa [L] using hs⟩
  have h1 : Module.finrank ℤ L = Module.finrank ℝ E := ZLattice.rank (K := ℝ) (L := L)
  have hL : LinearMap.range p.toIntLinearMap = L := by
    ext x
    simp [L]
  have h2 : Module.finrank ℤ La = Module.finrank ℤ L := by
    rw [← hL]
    exact (LinearEquiv.ofInjective p.toIntLinearMap hi).finrank_eq
  rw [Module.finrank_fintype_fun_eq_card, ← Module.finrank_eq_card_basis e, h2, h1]

theorem latContinuation : ∀ (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (g m : ℕ) (B : Set (Fin m → ℂ)) (b₀ : Fin m → ℂ) (K : (Fin m → ℂ) → AddSubgroup (Fin g → ℂ)) (P : (Fin m → ℂ) → (La →+ (Fin g → ℂ))) (r : ℝ), IsOpen B → b₀ ∈ B → 0 < r → (∀ b ∈ B, ∀ z ∈ K b, ‖z‖ < r → z = 0) → (∀ (b : ℕ → (Fin m → ℂ)) (z : ℕ → (Fin g → ℂ)) (z₀ : Fin g → ℂ), Filter.Tendsto b Filter.atTop (nhds b₀) → Filter.Tendsto z Filter.atTop (nhds z₀) → (∀ i, z i ∈ K (b i)) → z₀ ∈ K b₀) → (∀ x, ContinuousAt (fun b => P b x) b₀) → (∀ b ∈ B, (P b).range ≤ K b) → (P b₀).range = K b₀ → Function.Injective (P b₀) → Submodule.span ℝ (Set.range (P b₀)) = ⊤ → ∀ᶠ b in nhds b₀, (P b).range = K b ∧ Function.Injective (P b) ∧ Submodule.span ℝ (Set.range (P b)) = ⊤ ∧ DiscreteTopology (P b).range := by
  intro La _ _ _ g m B b₀ K P r hB hb₀ hr hdisc hclosed hcont hle heq hinj hspan
  obtain ⟨J, _, ⟨e⟩⟩ : ∃ (J : Type) (_ : Fintype J), Nonempty (Module.Basis J ℤ La) :=
    ⟨_, inferInstance, ⟨Module.Free.chooseBasis ℤ La⟩⟩
  have hrepr : ∀ b (k : J → ℤ), P b (e.equivFun.symm k) = ∑ j, ((k j : ℤ) : ℝ) • P b (e j) := by
    intro b k
    rw [← latContMap_repr e (P b) k, latContMap_apply]
  have hcoord : ∀ b x, P b x = ∑ j, ((e.equivFun x j : ℤ) : ℝ) • P b (e j) := by
    intro b x
    rw [← hrepr]
    simp
  have hdiscR : ∀ b ∈ B, DiscreteTopology (P b).range := fun b hb =>
    latCont_discrete _ r hr (fun z hz hzr => hdisc b hb z (hle b hb hz) hzr)
  have hcard : Fintype.card J = Module.finrank ℝ (Fin g → ℂ) := by
    rw [← Module.finrank_fintype_fun_eq_card ℝ]
    exact latCont_card e (P b₀) (hdiscR b₀ hb₀) hinj hspan
  have hspan0 : ⊤ ≤ Submodule.span ℝ (Set.range (fun j => P b₀ (e j))) := by
    rw [← hspan]
    apply Submodule.span_le.mpr
    rintro _ ⟨x, rfl⟩
    rw [hcoord]
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
  have hli0 : LinearIndependent ℝ (fun j => P b₀ (e j)) :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hspan0 hcard
  have hvc : ContinuousAt (fun b => fun j => P b (e j)) b₀ :=
    continuousAt_pi.mpr (fun j => hcont (e j))
  have hev_li : ∀ᶠ b in nhds b₀, LinearIndependent ℝ (fun j => P b (e j)) :=
    hvc.tendsto.eventually hli0.eventually
  have hev_B : ∀ᶠ b in nhds b₀, b ∈ B := hB.mem_nhds hb₀
  have hspanv : ∀ b, LinearIndependent ℝ (fun j => P b (e j)) →
      Submodule.span ℝ (Set.range (fun j => P b (e j))) = ⊤ :=
    fun b hb => hb.span_eq_top_of_card_eq_finrank' hcard
  have hsurj : ∀ b, LinearIndependent ℝ (fun j => P b (e j)) →
      ∀ z, ∃ c : J → ℝ, ∑ j, c j • P b (e j) = z := by
    intro b hb z
    have hz : z ∈ Submodule.span ℝ (Set.range (fun j => P b (e j))) := by
      rw [hspanv b hb]
      trivial
    exact (Submodule.mem_span_range_iff_exists_fun ℝ).mp hz
  have hev_eq : ∀ᶠ b in nhds b₀, ∀ z ∈ K b, z ∈ (P b).range := by
    by_contra hne
    rw [Filter.not_eventually] at hne
    have hfr : ∃ᶠ b in nhds b₀, b ∈ B ∧ LinearIndependent ℝ (fun j => P b (e j)) ∧
        ∃ z ∈ K b, z ∉ (P b).range := by
      refine (hne.and_eventually (hev_B.and hev_li)).mono ?_
      rintro b ⟨h1, h2, h3⟩
      push Not at h1
      exact ⟨h2, h3, h1⟩
    obtain ⟨bs, hbs, hprop⟩ := Filter.exists_seq_forall_of_frequently hfr
    choose hbsB hbsli z hzK hzR using hprop
    choose c hc using fun i => hsurj (bs i) (hbsli i) (z i)
    have hshift : ∀ i (k : J → ℤ),
        (∑ j, (Int.fract (c i j) - (k j : ℝ)) • P (bs i) (e j)) ∈ K (bs i) ∧
        (∑ j, (Int.fract (c i j) - (k j : ℝ)) • P (bs i) (e j)) ∉ (P (bs i)).range := by
      intro i k
      have e1 : ∑ j, (Int.fract (c i j) - (k j : ℝ)) • P (bs i) (e j)
          = z i - P (bs i) (e.equivFun.symm (fun j => ⌊c i j⌋ + k j)) := by
        rw [hrepr, ← hc i, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [← sub_smul]
        congr 1
        push_cast
        rw [← Int.self_sub_floor]
        ring
      rw [e1]
      have hmem : P (bs i) (e.equivFun.symm (fun j => ⌊c i j⌋ + k j)) ∈ (P (bs i)).range :=
        ⟨_, rfl⟩
      refine ⟨sub_mem (hzK i) (hle _ (hbsB i) hmem), fun h => hzR i ?_⟩
      have := add_mem h hmem
      rwa [sub_add_cancel] at this
    have hIcc : ∀ i, (fun j => Int.fract (c i j)) ∈ Set.Icc (0 : J → ℝ) 1 := fun i =>
      ⟨fun j => Int.fract_nonneg _, fun j => (Int.fract_lt_one _).le⟩
    obtain ⟨a, -, φ, hφ, ha⟩ := (isCompact_Icc (a := (0 : J → ℝ)) (b := 1)).tendsto_subseq hIcc
    have hbφ : Filter.Tendsto (bs ∘ φ) Filter.atTop (nhds b₀) := hbs.comp hφ.tendsto_atTop
    have hvφ : ∀ j, Filter.Tendsto (fun i => P (bs (φ i)) (e j)) Filter.atTop
        (nhds (P b₀ (e j))) := fun j => (hcont (e j)).tendsto.comp hbφ
    have haj : ∀ j, Filter.Tendsto (fun i => Int.fract (c (φ i) j)) Filter.atTop (nhds (a j)) :=
      fun j => ((continuous_apply j).tendsto a).comp ha
    have hlim : ∀ k : J → ℤ, Filter.Tendsto
        (fun i => ∑ j, (Int.fract (c (φ i) j) - (k j : ℝ)) • P (bs (φ i)) (e j)) Filter.atTop
        (nhds (∑ j, (a j - (k j : ℝ)) • P b₀ (e j))) := fun k =>
      tendsto_finsetSum _ (fun j _ => ((haj j).sub_const _).smul (hvφ j))
    have hz0 : (∑ j, (a j - ((0 : J → ℤ) j : ℝ)) • P b₀ (e j)) ∈ K b₀ :=
      hclosed (bs ∘ φ) _ _ hbφ (hlim 0) (fun i => (hshift (φ i) 0).1)
    simp only [Pi.zero_apply, Int.cast_zero, sub_zero] at hz0
    rw [← heq] at hz0
    obtain ⟨x, hx⟩ := AddMonoidHom.mem_range.mp hz0
    have hzero : ∑ j, (a j - ((e.equivFun x j : ℤ) : ℝ)) • P b₀ (e j) = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [← hcoord b₀ x, ← hx, sub_self]
    have hlim0 := hlim (e.equivFun x)
    rw [hzero] at hlim0
    obtain ⟨i, hi⟩ := (hlim0.eventually (Metric.ball_mem_nhds (0 : Fin g → ℂ) hr)).exists
    rw [dist_zero_right] at hi
    obtain ⟨hK', hR'⟩ := hshift (φ i) (e.equivFun x)
    exact hR' (by rw [hdisc _ (hbsB (φ i)) _ hK' hi]; exact zero_mem _)
  filter_upwards [hev_B, hev_li, hev_eq] with b hb hli hrange
  refine ⟨le_antisymm (hle b hb) (fun z hz => hrange z hz), ?_, ?_, hdiscR b hb⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    rw [hcoord] at hx
    have h0 := (Fintype.linearIndependent_iff.mp hli) _ hx
    have h1 : e.equivFun x = 0 := funext fun j => by simpa using h0 j
    simpa using congrArg e.equivFun.symm h1
  · rw [eq_top_iff, ← hspanv b hli]
    apply Submodule.span_mono
    rintro _ ⟨j, rfl⟩
    exact ⟨e j, rfl⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SymplecticTorsionSystemIsGeometricBasis
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SymplecticTorsionSystemIsGeometricBasis
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.SympBasis

private theorem sum_inv_mulVec_smul_col_of_det_ne_zero {R : Type} [CommRing R] {g : ℕ} (c : Fin (2 * g) → R) (i j : Fin (2 * g))
    (hij : (i : ℕ) < g ∧ (j : ℕ) = i + g) : ∑ l, c l * (Out.stdSymp g l j : R) = c i := by
  rw [Finset.sum_eq_single i]
  · unfold Out.stdSymp
    rw [if_pos hij]
    simp
  · intro l _ hl
    have h1 : ¬ ((l : ℕ) < g ∧ (j : ℕ) = l + g) := fun h => hl (Fin.ext (by omega))
    have h2 : ¬ ((j : ℕ) < g ∧ (l : ℕ) = j + g) := by omega
    unfold Out.stdSymp
    rw [if_neg h1, if_neg h2]
    simp
  · simp

private theorem sum_mul_stdSymp_eq_neg_of_eq_add {R : Type} [CommRing R] {g : ℕ} (c : Fin (2 * g) → R) (i j : Fin (2 * g))
    (hij : (j : ℕ) < g ∧ (i : ℕ) = j + g) : ∑ l, c l * (Out.stdSymp g l j : R) = - c i := by
  rw [Finset.sum_eq_single i]
  · have h1 : ¬ ((i : ℕ) < g ∧ (j : ℕ) = i + g) := by omega
    unfold Out.stdSymp
    rw [if_neg h1, if_pos hij]
    simp
  · intro l _ hl
    have h1 : ¬ ((l : ℕ) < g ∧ (j : ℕ) = l + g) := by omega
    have h2 : ¬ ((j : ℕ) < g ∧ (l : ℕ) = j + g) := fun h => hl (Fin.ext (by omega))
    unfold Out.stdSymp
    rw [if_neg h1, if_neg h2]
    simp
  · simp

theorem eq_of_sum_stdSymp {R : Type} [CommRing R] {g : ℕ} (a b : Fin (2 * g) → R)
    (h : ∀ j, ∑ i, a i * (Out.stdSymp g i j : R) = ∑ i, b i * (Out.stdSymp g i j : R)) : a = b := by
  funext i
  have hi2 := i.isLt
  by_cases hi : (i : ℕ) < g
  ·
    have h1 := h ⟨i + g, by omega⟩
    rwa [sum_inv_mulVec_smul_col_of_det_ne_zero a i _ ⟨hi, rfl⟩, sum_inv_mulVec_smul_col_of_det_ne_zero b i _ ⟨hi, rfl⟩] at h1
  ·
    have h1 := h ⟨i - g, by omega⟩
    rw [sum_mul_stdSymp_eq_neg_of_eq_add a i _ ⟨by simp; omega, by simp; omega⟩,
      sum_mul_stdSymp_eq_neg_of_eq_add b i _ ⟨by simp; omega, by simp; omega⟩] at h1
    exact neg_inj.mp h1

theorem rel_prod {M U : Type} [CommMonoid M] [CommGroup U] (W : M → U → Prop) (h1 : W 1 1)
    (hm : ∀ x x' c c', W x c → W x' c' → W (x * x') (c * c')) {J : Type} (s : Finset J) (p : J → M) (u : J → U)
    (a : J → ℕ) (hp : ∀ i, W (p i) (u i)) : W (∏ i ∈ s, p i ^ a i) (∏ i ∈ s, u i ^ a i) := by
  classical
  have hpow : ∀ i (n : ℕ), W (p i ^ n) (u i ^ n) := by
    intro i n
    induction n with
    | zero => simpa using h1
    | succ n ih =>
      rw [pow_succ, pow_succ]
      exact hm _ _ _ _ ih (hp i)
  refine Finset.induction_on s (by simpa using h1) ?_
  intro j t hj ih
  rw [Finset.prod_insert hj, Finset.prod_insert hj]
  exact hm _ _ _ _ (hpow j (a j)) ih

private theorem zpow_finset_sum_divisor {U : Type} [CommGroup U] (z : U) {I : Type} (s : Finset I) (f : I → ℤ) :
    z ^ (∑ i ∈ s, f i) = ∏ i ∈ s, z ^ f i := by
  classical
  refine Finset.induction_on s (by simp) ?_
  intro j t hj ih
  rw [Finset.sum_insert hj, Finset.prod_insert hj, zpow_add, ih]

theorem injective_of_pairing {M U : Type} [CommMonoid M] [CommGroup U] (W : M → M → U → Prop) (k : ℕ) [NeZero k]
    (hu : ∀ x y, x ^ k = 1 → y ^ k = 1 → ∃! c, W x y c)
    (hm : ∀ x x' y c c', W x y c → W x' y c' → W (x * x') y (c * c')) {g : ℕ} (p : Fin (2 * g) → M)
    (hp : ∀ i, p i ^ k = 1) (z : U) (hz : IsPrimitiveRoot z k)
    (hw : ∀ i j, W (p i) (p j) (z ^ Out.stdSymp g i j)) :
    Function.Injective fun c : Fin (2 * g) → ZMod k => ∏ i, p i ^ (c i).val := by
  classical

  have hone : ∀ y, y ^ k = 1 → W 1 y 1 := by
    intro y hy
    obtain ⟨c, hc, huniq⟩ := hu 1 y (one_pow k) hy
    have h2 : W 1 y (c * c) := by simpa using hm 1 1 y c c hc hc
    have hcc : c * c = c := huniq _ h2
    have hc1 : c = 1 := by simpa using hcc
    rw [hc1] at hc
    exact hc

  let e : (Fin (2 * g) → ZMod k) → Fin (2 * g) → ℤ := fun c j => ∑ i, Out.stdSymp g i j * ((c i).val : ℤ)
  have hW : ∀ (c : Fin (2 * g) → ZMod k) j, W (∏ i, p i ^ (c i).val) (p j) (z ^ e c j) := by
    intro c j
    have h := rel_prod (fun x v => W x (p j) v) (hone _ (hp j))
      (fun x x' v v' hx hx' => hm x x' (p j) v v' hx hx') Finset.univ p
      (fun i => z ^ Out.stdSymp g i j) (fun i => (c i).val) (fun i => hw i j)
    have hz' : (∏ i, (z ^ Out.stdSymp g i j) ^ (c i).val) = z ^ e c j := by
      simp only [e, zpow_finset_sum_divisor]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← zpow_natCast, ← zpow_mul]
    simpa only [hz'] using h
  have htors : ∀ c : Fin (2 * g) → ZMod k, (∏ i, p i ^ (c i).val) ^ k = 1 := by
    intro c
    rw [← Finset.prod_pow]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [← pow_mul, mul_comm, pow_mul, hp i, one_pow]
  intro c c' hcc
  have hcc' : (∏ i, p i ^ (c i).val) = ∏ i, p i ^ (c' i).val := hcc
  have key : ∀ j, z ^ e c j = z ^ e c' j := by
    intro j
    obtain ⟨w, _, huniq⟩ := hu _ (p j) (htors c) (hp j)
    have h1 := huniq _ (hW c j)
    have h2 := huniq _ (hcc' ▸ hW c' j)
    rw [h1, h2]
  apply eq_of_sum_stdSymp (R := ZMod k) c c'
  intro j
  have hd : ((e c j : ℤ) : ZMod k) = ((e c' j : ℤ) : ZMod k) := by
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub, ← hz.zpow_eq_one_iff_dvd, zpow_sub, key j, mul_inv_cancel]
  simpa [e, mul_comm] using hd

private theorem comp_list_prod_eq_prod_map_comp_over {S : Scheme.{0}} {A T T' : Over S} [GrpObj A] (f : T' ⟶ T)
    (l : List (T ⟶ A)) : f ≫ l.prod = (l.map (f ≫ ·)).prod := by
  induction l with
  | nil => simp [MonObj.comp_one]
  | cons x l ih => simp [List.prod_cons, MonObj.comp_mul, ih]

theorem comp_linComb {S : Scheme.{0}} {A T T' : Over S} [GrpObj A] (f : T' ⟶ T) {n : ℕ} (y : Fin n → (T ⟶ A))
    (a : Fin n → ℕ) : f ≫ Out.linComb y a = Out.linComb (fun i => f ≫ y i) a := by
  unfold Out.linComb
  rw [comp_list_prod_eq_prod_map_comp_over, List.map_ofFn]
  simp [Function.comp_def, MonObj.comp_pow]

end GlobalTheory.SympBasis

namespace GlobalTheory


open SympBasis in
theorem symplectic_system_torsion_basis :
    Out.Laws → ∀ (K₀ : Type) [Field K₀] (P : Out.PolAV (Sp K₀)) (k : ℕ) (ze : K₀ˣ) (pt : Fin (2 * P.g) → (Out.baseOver (Sp K₀) ⟶ P.A)), (k : K₀) ≠ 0 → IsPrimitiveRoot ze k → (∀ i, pt i ^ k = 1) → (∀ i j, Out.WeilIs P.A P.L k (pt i) (pt j) (unitOn ze ^ Out.stdSymp P.g i j)) → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp K₀) (y : Over.mk x ⟶ P.A), y ^ k = 1 → ∃! c : Fin (2 * P.g) → ZMod k, Out.linComb (fun i => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver (Sp K₀)) ≫ pt i) (fun i => (c i).val) = y := by
  intro hL K₀ _ P k ze pt hk hze hpt hw K _ _ x y hy
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hk (by simp)
  have : NeZero k := ⟨hk0⟩
  have hsep : IsSeparated P.A.hom := by
    obtain ⟨_, _, _, _⟩ := P.isAb
    infer_instance

  let h : Over.mk x ⟶ Out.baseOver (Sp K₀) := Over.homMk x (by simp)

  have hpre : ∀ s s' : Out.baseOver (Sp K₀) ⟶ P.A, h ≫ s = h ≫ s' → s = s' := by
    intro s s' hss
    have : IsReduced (Out.baseOver (Sp K₀)).left := inferInstanceAs (IsReduced (Sp K₀))
    have : IsDominant (X := Sp K) (Y := (Out.baseOver (Sp K₀)).left) x :=
      inferInstanceAs (IsDominant (X := Sp K) (Y := Sp K₀) x)
    apply Over.OverMorphism.ext
    refine ext_of_isDominant_of_isSeparated P.A.hom ?_ x ?_
    · rw [Over.w s, Over.w s']
    · simpa [h] using congrArg CommaMorphism.left hss

  have hzu : IsPrimitiveRoot (unitOn ze) k := by
    unfold unitOn
    refine hze.map_of_injective (Units.map_injective ?_)
    exact Function.LeftInverse.injective
      (g := (Scheme.ΓSpecIso (CommRingCat.of K₀)).hom.hom) fun a => by simp

  obtain ⟨hu, hm, -, -⟩ := hL.weil (Sp K₀) P k (Out.baseOver (Sp K₀))
  have hinj0 := SympBasis.injective_of_pairing (fun a b c => Out.WeilIs P.A P.L (k : ℤ) a b c) k hu
    (fun a a' b c c' => hm a a' b c c') pt hpt (unitOn ze) hzu hw

  have hlin : ∀ c : Fin (2 * P.g) → ZMod k,
      Out.linComb (fun i => h ≫ pt i) (fun i => (c i).val) = h ≫ ∏ i, pt i ^ (c i).val := by
    intro c
    rw [← SympBasis.comp_linComb]
    unfold Out.linComb
    rw [List.prod_ofFn]
  have htors : ∀ c : Fin (2 * P.g) → ZMod k,
      (Out.linComb (fun i => h ≫ pt i) (fun i => (c i).val)) ^ k = 1 := by
    intro c
    rw [hlin, ← MonObj.comp_pow, ← Finset.prod_pow,
      Finset.prod_eq_one fun i _ => by rw [← pow_mul, mul_comm, pow_mul, hpt i, one_pow]]
    exact MonObj.comp_one _
  let Φ : (Fin (2 * P.g) → ZMod k) → {y : Over.mk x ⟶ P.A // y ^ k = 1} := fun c => ⟨_, htors c⟩
  have hΦ : Function.Injective Φ := by
    intro c c' hcc
    have h1 : Out.linComb (fun i => h ≫ pt i) (fun i => (c i).val) =
        Out.linComb (fun i => h ≫ pt i) (fun i => (c' i).val) := congrArg Subtype.val hcc
    rw [hlin, hlin] at h1
    exact hinj0 (hpre _ _ h1)

  have hkK : ((k : ℕ) : K) ≠ 0 := by
    have hc : ((k : ℕ) : K) = (Spec.preimage x).hom (k : K₀) := by simp
    rw [hc]
    exact (map_ne_zero_iff _ (Spec.preimage x).hom.injective).2 hk
  have hcard := (hL.mulN (Sp K₀) P k (Nat.one_le_iff_ne_zero.2 hk0)).2.2.2.2 K x hkK
  have : Finite {y : Over.mk x ⟶ P.A // y ^ k = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  have hbij : Function.Bijective Φ := hΦ.bijective_of_nat_card_le (by
    rw [hcard, Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin])
  obtain ⟨c, hc⟩ := hbij.2 ⟨y, hy⟩
  exact ⟨c, congrArg Subtype.val hc,
    fun c' hc' => hbij.1 (Subtype.ext (hc'.trans (congrArg Subtype.val hc).symm))⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SymplecticTorsionSystemIsGeometricBasisStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
theorem _root_.GlobalTheory.T.symplectic_torsion_system_is_geometric_basis : Out.Laws → ∀ (K₀ : Type) [Field K₀] (P : Out.PolAV (Sp K₀)) (k : ℕ) (ze : K₀ˣ) (pt : Fin (2 * P.g) → (Out.baseOver (Sp K₀) ⟶ P.A)), (k : K₀) ≠ 0 → IsPrimitiveRoot ze k → (∀ i, pt i ^ k = 1) → (∀ i j, Out.WeilIs P.A P.L k (pt i) (pt j) (unitOn ze ^ Out.stdSymp P.g i j)) → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp K₀) (y : Over.mk x ⟶ P.A), y ^ k = 1 → ∃! c : Fin (2 * P.g) → ZMod k, Out.linComb (fun i => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver (Sp K₀)) ≫ pt i) (fun i => (c i).val) = y := by
  first | exact @GlobalTheory.symplectic_system_torsion_basis | exact GlobalTheory.symplectic_system_torsion_basis | (intros; apply GlobalTheory.symplectic_system_torsion_basis <;> assumption)
end
end
