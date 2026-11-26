module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreCompatibility
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicFiniteVolumeIntegralBound
open IsLocalRing Polynomial

namespace GlobalTheory.GenFibBaseChange

theorem exists_genFib_maps : ∀ (T O A A₁ R R₁ : Type) [CommRing T] [IsDomain T] [CommRing O] [Algebra T O]
    [CommRing A] [IsDomain A] [CommRing A₁] [IsDomain A₁] [CommRing R] [Algebra A R] [CommRing R₁] [Algebra A₁ R₁]
    (j : A →+* A₁) (i₁ : A₁ →+* T), Function.Injective j → Function.Injective i₁ →
    ∀ (jA : R →+* O) (jA₁ : R₁ →+* O) (γ : R →+* R₁)
      (ψA : GlobalTheory.LocAcyc.GenFib A R →+* GlobalTheory.LocAcyc.GenFib T O),
    jA₁.comp (algebraMap A₁ R₁) = (algebraMap T O).comp i₁ →
    γ.comp (algebraMap A R) = (algebraMap A₁ R₁).comp j →
    jA₁.comp γ = jA →
    ψA.comp (algebraMap R (GlobalTheory.LocAcyc.GenFib A R)) = (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp jA →
    ∃ (ψA₁ : GlobalTheory.LocAcyc.GenFib A₁ R₁ →+* GlobalTheory.LocAcyc.GenFib T O)
      (β : GlobalTheory.LocAcyc.GenFib A R →+* GlobalTheory.LocAcyc.GenFib A₁ R₁),
      ψA₁.comp (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)) = (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp jA₁ ∧
      ψA₁.comp β = ψA ∧
      β.comp (algebraMap R (GlobalTheory.LocAcyc.GenFib A R)) = (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)).comp γ := by
  intro T O A A₁ R R₁ _ _ _ _ _ _ _ _ _ _ _ _ j i₁ hj hi₁ jA jA₁ γ ψA h1 h2 h3 h4
  have hu1 : ∀ y : Algebra.algebraMapSubmonoid R₁ (nonZeroDivisors A₁),
      IsUnit (((algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp jA₁) y) := by
    rintro ⟨y, a, ha, rfl⟩
    have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
    have hi : i₁ a ∈ nonZeroDivisors T := mem_nonZeroDivisors_of_ne_zero (fun h => ha0 (hi₁ (by simpa using h)))
    have e : jA₁ (algebraMap A₁ R₁ a) = algebraMap T O (i₁ a) := by
      simpa using congrArg (fun f => f a) h1
    simp only [RingHom.coe_comp, Function.comp_apply, e]
    exact IsLocalization.map_units (GlobalTheory.LocAcyc.GenFib T O)
      (⟨algebraMap T O (i₁ a), ⟨i₁ a, hi, rfl⟩⟩ : Algebra.algebraMapSubmonoid O (nonZeroDivisors T))
  have hu2 : ∀ y : Algebra.algebraMapSubmonoid R (nonZeroDivisors A),
      IsUnit (((algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)).comp γ) y) := by
    rintro ⟨y, a, ha, rfl⟩
    have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
    have hi : j a ∈ nonZeroDivisors A₁ := mem_nonZeroDivisors_of_ne_zero (fun h => ha0 (hj (by simpa using h)))
    have e : γ (algebraMap A R a) = algebraMap A₁ R₁ (j a) := by
      simpa using congrArg (fun f => f a) h2
    simp only [RingHom.coe_comp, Function.comp_apply, e]
    exact IsLocalization.map_units (GlobalTheory.LocAcyc.GenFib A₁ R₁)
      (⟨algebraMap A₁ R₁ (j a), ⟨j a, hi, rfl⟩⟩ : Algebra.algebraMapSubmonoid R₁ (nonZeroDivisors A₁))
  let ψA₁ : GlobalTheory.LocAcyc.GenFib A₁ R₁ →+* GlobalTheory.LocAcyc.GenFib T O :=
    IsLocalization.lift (M := Algebra.algebraMapSubmonoid R₁ (nonZeroDivisors A₁)) hu1
  let β : GlobalTheory.LocAcyc.GenFib A R →+* GlobalTheory.LocAcyc.GenFib A₁ R₁ :=
    IsLocalization.lift (M := Algebra.algebraMapSubmonoid R (nonZeroDivisors A)) hu2
  have k1 : ψA₁.comp (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)) =
      (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp jA₁ := IsLocalization.lift_comp hu1
  have k3 : β.comp (algebraMap R (GlobalTheory.LocAcyc.GenFib A R)) =
      (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)).comp γ := IsLocalization.lift_comp hu2
  refine ⟨ψA₁, β, k1, ?_, k3⟩
  apply IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid R (nonZeroDivisors A))
  rw [RingHom.comp_assoc, k3, ← RingHom.comp_assoc, k1, RingHom.comp_assoc, h3, h4]

end GlobalTheory.GenFibBaseChange
end

open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_fibre_compatibility : ∀ (T O A A₁ R R₁ : Type) [CommRing T] [IsDomain T] [CommRing O] [Algebra T O]
    [CommRing A] [IsDomain A] [CommRing A₁] [IsDomain A₁] [CommRing R] [Algebra A R] [CommRing R₁] [Algebra A₁ R₁]
    (j : A →+* A₁) (i₁ : A₁ →+* T), Function.Injective j → Function.Injective i₁ →
    ∀ (jA : R →+* O) (jA₁ : R₁ →+* O) (γ : R →+* R₁)
      (ψA : GlobalTheory.LocAcyc.GenFib A R →+* GlobalTheory.LocAcyc.GenFib T O),
    jA₁.comp (algebraMap A₁ R₁) = (algebraMap T O).comp i₁ →
    γ.comp (algebraMap A R) = (algebraMap A₁ R₁).comp j →
    jA₁.comp γ = jA →
    ψA.comp (algebraMap R (GlobalTheory.LocAcyc.GenFib A R)) = (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp jA →
    ∃ (ψA₁ : GlobalTheory.LocAcyc.GenFib A₁ R₁ →+* GlobalTheory.LocAcyc.GenFib T O)
      (β : GlobalTheory.LocAcyc.GenFib A R →+* GlobalTheory.LocAcyc.GenFib A₁ R₁),
      ψA₁.comp (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)) = (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp jA₁ ∧
      ψA₁.comp β = ψA ∧
      β.comp (algebraMap R (GlobalTheory.LocAcyc.GenFib A R)) = (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)).comp γ := by
  first | (exact @GlobalTheory.GenFibBaseChange.exists_genFib_maps) | (exact GlobalTheory.GenFibBaseChange.exists_genFib_maps) | (intros; apply GlobalTheory.GenFibBaseChange.exists_genFib_maps  <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyOriginRetractionLocalises
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyOriginRetractionLocalises
open IsLocalRing Polynomial

namespace GlobalTheory.KeyOriginEnlargeLoc

theorem retract_localises : ∀ (T O A₁ EA₁ : Type) [CommRing T] [CommRing O] [IsLocalRing O] [Algebra T O] [Algebra (Polynomial T) O]
    [CommRing A₁] [IsLocalRing A₁] (i₁ : A₁ →+* T), IsLocalHom i₁ → IsLocalHom (algebraMap T O) →
    ∀ [CommRing EA₁] [Algebra (Polynomial A₁) EA₁] [Algebra A₁ EA₁]
      (QA₁ : Ideal EA₁) [QA₁.IsPrime] (jA₁ : Localization.AtPrime QA₁ →+* O) (ρ' : EA₁ →+* A₁),
    algebraMap (Polynomial T) O Polynomial.X ∈ maximalIdeal O →
    ρ'.comp (algebraMap A₁ EA₁) = RingHom.id A₁ →
    ρ' (algebraMap (Polynomial A₁) EA₁ Polynomial.X) = 0 →
    (∀ x : EA₁, algebraMap T O (i₁ (ρ' x)) - jA₁ (algebraMap EA₁ (Localization.AtPrime QA₁) x) ∈
      Ideal.span {algebraMap (Polynomial T) O Polynomial.X}) →
    (∀ x : EA₁, ρ' x = 0 → ∃ s ∉ QA₁, s * x ∈ Ideal.span {algebraMap (Polynomial A₁) EA₁ Polynomial.X}) →
    ∃ ρ₁ : Localization.AtPrime QA₁ →+* A₁,
      GlobalTheory.KeyOriginEnlarge.Retracts T O A₁ i₁ EA₁ QA₁ jA₁ ρ₁ ∧
      ρ₁.comp (algebraMap EA₁ (Localization.AtPrime QA₁)) = ρ' := by
  intro T O A₁ EA₁ _ _ _ _ _ _ _ i₁ hi₁ hTO _ _ _ QA₁ _ jA₁ ρ' hX hret hρX hcong hker
  set L := Localization.AtPrime QA₁
  set I : Ideal O := Ideal.span {algebraMap (Polynomial T) O Polynomial.X}
  have hI : I ≤ maximalIdeal O := by
    rw [Ideal.span_le]; simpa using hX
  have hunit : ∀ y : QA₁.primeCompl, IsUnit (ρ' y) := by
    intro y
    by_contra hy
    have h1 : ρ' y ∈ maximalIdeal A₁ := (mem_maximalIdeal _).2 hy
    have h2 : algebraMap T O (i₁ (ρ' y)) ∈ maximalIdeal O := by
      rw [mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      exact hy ((isUnit_map_iff i₁ _).1 ((isUnit_map_iff (algebraMap T O) _).1 hu))
    have h3 : jA₁ (algebraMap EA₁ L y) ∈ maximalIdeal O := by
      have := hI (hcong y)
      have := (maximalIdeal O).sub_mem h2 this
      simpa using this
    have h4 : IsUnit (jA₁ (algebraMap EA₁ L y)) :=
      (IsLocalization.map_units L y).map jA₁
    exact (mem_maximalIdeal _ |>.1 h3) h4
  let ρ₁ : L →+* A₁ := IsLocalization.lift (M := QA₁.primeCompl) hunit
  have hcomp : ρ₁.comp (algebraMap EA₁ L) = ρ' := by
    ext x; exact IsLocalization.lift_eq _ _
  refine ⟨ρ₁, ⟨?_, ?_, ?_⟩, hcomp⟩
  · rw [IsScalarTower.algebraMap_eq A₁ EA₁ L, ← RingHom.comp_assoc, hcomp, hret]
  · apply le_antisymm
    · intro z hz
      rw [RingHom.mem_ker] at hz
      obtain ⟨⟨x, y⟩, rfl⟩ := IsLocalization.mk'_surjective QA₁.primeCompl z
      dsimp only at hz ⊢
      have hx : ρ' x = 0 := by
        have := IsLocalization.lift_mk' (M := QA₁.primeCompl) (S := L) hunit x y
        change ρ₁ _ = _ at this
        rw [hz] at this
        exact (Units.mul_left_eq_zero _).1 this.symm
      obtain ⟨s, hs, hsx⟩ := hker x hx
      have hsy : s * (y : EA₁) ∈ QA₁.primeCompl := QA₁.primeCompl.mul_mem hs y.2
      have heq : IsLocalization.mk' L x y = IsLocalization.mk' L (s * x) (⟨s * y, hsy⟩ : QA₁.primeCompl) := by
        rw [IsLocalization.mk'_eq_iff_eq]
        simp only
        ring_nf
      rw [heq, IsLocalization.mk'_eq_mul_mk'_one]
      apply Ideal.mul_mem_right
      have : algebraMap EA₁ L (s * x) ∈ (Ideal.span {algebraMap (Polynomial A₁) EA₁ Polynomial.X}).map (algebraMap EA₁ L) :=
        Ideal.mem_map_of_mem _ hsx
      rwa [Ideal.map_span, Set.image_singleton, ← IsScalarTower.algebraMap_apply] at this
    · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker,
        IsScalarTower.algebraMap_apply (Polynomial A₁) EA₁ L]
      change (ρ₁.comp (algebraMap EA₁ L)) _ = 0
      rw [hcomp, hρX]
  · have key : (Ideal.Quotient.mk I).comp ((algebraMap T O).comp (i₁.comp ρ₁)) = (Ideal.Quotient.mk I).comp jA₁ := by
      apply IsLocalization.ringHom_ext QA₁.primeCompl
      ext x
      simp only [RingHom.comp_apply]
      rw [Ideal.Quotient.eq]
      have := hcong x
      rw [← hcomp] at this
      simpa using this
    intro x
    have := congrArg (fun f => f x) key
    simp only [RingHom.comp_apply] at this
    exact Ideal.Quotient.eq.1 this

end GlobalTheory.KeyOriginEnlargeLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyOriginRetractionLocalisesStatement
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.keyOrigin_retraction_localises : ∀ (T O A₁ EA₁ : Type) [CommRing T] [CommRing O] [IsLocalRing O] [Algebra T O] [Algebra (Polynomial T) O]
    [CommRing A₁] [IsLocalRing A₁] (i₁ : A₁ →+* T), IsLocalHom i₁ → IsLocalHom (algebraMap T O) →
    ∀ [CommRing EA₁] [Algebra (Polynomial A₁) EA₁] [Algebra A₁ EA₁]
      (QA₁ : Ideal EA₁) [QA₁.IsPrime] (jA₁ : Localization.AtPrime QA₁ →+* O) (ρ' : EA₁ →+* A₁),
    algebraMap (Polynomial T) O Polynomial.X ∈ maximalIdeal O →
    ρ'.comp (algebraMap A₁ EA₁) = RingHom.id A₁ →
    ρ' (algebraMap (Polynomial A₁) EA₁ Polynomial.X) = 0 →
    (∀ x : EA₁, algebraMap T O (i₁ (ρ' x)) - jA₁ (algebraMap EA₁ (Localization.AtPrime QA₁) x) ∈
      Ideal.span {algebraMap (Polynomial T) O Polynomial.X}) →
    (∀ x : EA₁, ρ' x = 0 → ∃ s ∉ QA₁, s * x ∈ Ideal.span {algebraMap (Polynomial A₁) EA₁ Polynomial.X}) →
    ∃ ρ₁ : Localization.AtPrime QA₁ →+* A₁,
      GlobalTheory.KeyOriginEnlarge.Retracts T O A₁ i₁ EA₁ QA₁ jA₁ ρ₁ ∧
      ρ₁.comp (algebraMap EA₁ (Localization.AtPrime QA₁)) = ρ' := by
  first | (exact @GlobalTheory.KeyOriginEnlargeLoc.retract_localises) | (exact GlobalTheory.KeyOriginEnlargeLoc.retract_localises) | (intros; apply GlobalTheory.KeyOriginEnlargeLoc.retract_localises  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZmodTorsorBaseChangeTransportPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZmodTorsorBaseChangeTransportPoint
open IsLocalRing Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.KeyOriginCut

theorem torsor_baseChange_point :
    ∀ (A A₁ R R₁ : Type) [CommRing A] [CommRing A₁] [IsDomain A₁] [CommRing R] [Algebra A R]
    [CommRing R₁] [Algebra A₁ R₁] (j : A →+* A₁) (γ : R →+* R₁) (ρ : R →+* A) (ρ₁ : R₁ →+* A₁)
    (β : GlobalTheory.LocAcyc.GenFib A R →+* GlobalTheory.LocAcyc.GenFib A₁ R₁),
    β.comp (algebraMap R (GlobalTheory.LocAcyc.GenFib A R)) = (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)).comp γ →
    ρ₁.comp (algebraMap A₁ R₁) = RingHom.id A₁ →
    ρ₁.comp γ = j.comp ρ →
    ∀ (q : ℕ), 0 < q → ∀ (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A R) DA]
      (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A R] DA)),
    GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A R) DA q actA →
    ∃ (DA₁ : Type) (_ : CommRing DA₁) (_ : Algebra (GlobalTheory.LocAcyc.GenFib A₁ R₁) DA₁)
      (actA₁ : Multiplicative (ZMod q) →* (DA₁ ≃ₐ[GlobalTheory.LocAcyc.GenFib A₁ R₁] DA₁)) (h : DA →+* DA₁),
      GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A₁ R₁) DA₁ q actA₁ ∧
      h.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A R) DA) = (algebraMap (GlobalTheory.LocAcyc.GenFib A₁ R₁) DA₁).comp β ∧
      ∀ σ : DA →+* FractionRing A₁,
        (σ.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A R) DA)).comp (algebraMap R (GlobalTheory.LocAcyc.GenFib A R)) =
          (algebraMap A₁ (FractionRing A₁)).comp (j.comp ρ) →
        ∃ σ₁ : DA₁ →+* FractionRing A₁,
          (σ₁.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A₁ R₁) DA₁)).comp (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)) =
            (algebraMap A₁ (FractionRing A₁)).comp ρ₁ := by
  intro A A₁ R R₁ _ _ _ _ _ _ _ j γ ρ ρ₁ β hβ hret hργ q hq DA _ _ actA hT
  letI : Algebra (GlobalTheory.LocAcyc.GenFib A R) (GlobalTheory.LocAcyc.GenFib A₁ R₁) := β.toAlgebra
  obtain ⟨act', -, hT'⟩ := GlobalTheory.LocAcyc.isZModTorsor_baseChange (GlobalTheory.LocAcyc.GenFib A R)
    (GlobalTheory.LocAcyc.GenFib A₁ R₁) DA q hq actA hT

  let M₁ := Algebra.algebraMapSubmonoid R₁ (nonZeroDivisors A₁)
  let f : R₁ →+* FractionRing A₁ := (algebraMap A₁ (FractionRing A₁)).comp ρ₁
  have hf : ∀ m : M₁, IsUnit (f m) := by
    rintro ⟨m, hm⟩
    obtain ⟨a, ha, rfl⟩ := hm
    have : ρ₁ (algebraMap A₁ R₁ a) = a := by
      simpa using congrArg (fun φ : A₁ →+* A₁ => φ a) hret
    simp only [f, RingHom.comp_apply, this]
    exact IsLocalization.map_units (FractionRing A₁) (⟨a, ha⟩ : nonZeroDivisors A₁)
  let ρK : GlobalTheory.LocAcyc.GenFib A₁ R₁ →+* FractionRing A₁ :=
    IsLocalization.lift (M := M₁) (S := GlobalTheory.LocAcyc.GenFib A₁ R₁) hf
  have hρK : ρK.comp (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)) = f :=
    IsLocalization.lift_comp hf
  refine ⟨TensorProduct (GlobalTheory.LocAcyc.GenFib A R) (GlobalTheory.LocAcyc.GenFib A₁ R₁) DA, inferInstance,
    inferInstance, act', Algebra.TensorProduct.includeRight.toRingHom, hT', ?_, ?_⟩
  · ext b
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.algebraMap_apply]
    rw [← Algebra.TensorProduct.tmul_one_eq_one_tmul]
    rfl
  · intro σ hσ
    have hagree : ρK.comp β = σ.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A R) DA) := by
      apply IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid R (nonZeroDivisors A))
      rw [hσ, RingHom.comp_assoc, hβ, ← RingHom.comp_assoc, hρK, ← hργ]
      rfl
    letI : Algebra (GlobalTheory.LocAcyc.GenFib A R) (FractionRing A₁) := (ρK.comp β).toAlgebra
    let fA : GlobalTheory.LocAcyc.GenFib A₁ R₁ →ₐ[GlobalTheory.LocAcyc.GenFib A R] FractionRing A₁ :=
      { ρK with commutes' := fun _ => rfl }
    let gA : DA →ₐ[GlobalTheory.LocAcyc.GenFib A R] FractionRing A₁ :=
      { σ with commutes' := fun b => (congrArg (fun φ => φ b) hagree).symm }
    refine ⟨(Algebra.TensorProduct.productMap fA gA).toRingHom, ?_⟩
    ext r
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.productMap_apply_tmul, map_one,
      mul_one]
    show ρK (algebraMap R₁ _ r) = _
    rw [← RingHom.comp_apply ρK, hρK]
    rfl

end GlobalTheory.KeyOriginCut
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZmodTorsorBaseChangeTransportPointStatement
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zmodTorsor_baseChange_transport_point : ∀ (A A₁ R R₁ : Type) [CommRing A] [CommRing A₁] [IsDomain A₁] [CommRing R] [Algebra A R]
    [CommRing R₁] [Algebra A₁ R₁] (j : A →+* A₁) (γ : R →+* R₁) (ρ : R →+* A) (ρ₁ : R₁ →+* A₁)
    (β : GlobalTheory.LocAcyc.GenFib A R →+* GlobalTheory.LocAcyc.GenFib A₁ R₁),
    β.comp (algebraMap R (GlobalTheory.LocAcyc.GenFib A R)) = (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)).comp γ →
    ρ₁.comp (algebraMap A₁ R₁) = RingHom.id A₁ →
    ρ₁.comp γ = j.comp ρ →
    ∀ (q : ℕ), 0 < q → ∀ (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A R) DA]
      (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A R] DA)),
    GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A R) DA q actA →
    ∃ (DA₁ : Type) (_ : CommRing DA₁) (_ : Algebra (GlobalTheory.LocAcyc.GenFib A₁ R₁) DA₁)
      (actA₁ : Multiplicative (ZMod q) →* (DA₁ ≃ₐ[GlobalTheory.LocAcyc.GenFib A₁ R₁] DA₁)) (h : DA →+* DA₁),
      GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A₁ R₁) DA₁ q actA₁ ∧
      h.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A R) DA) = (algebraMap (GlobalTheory.LocAcyc.GenFib A₁ R₁) DA₁).comp β ∧
      ∀ σ : DA →+* FractionRing A₁,
        (σ.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A R) DA)).comp (algebraMap R (GlobalTheory.LocAcyc.GenFib A R)) =
          (algebraMap A₁ (FractionRing A₁)).comp (j.comp ρ) →
        ∃ σ₁ : DA₁ →+* FractionRing A₁,
          (σ₁.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A₁ R₁) DA₁)).comp (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)) =
            (algebraMap A₁ (FractionRing A₁)).comp ρ₁ := by
  first | (exact @GlobalTheory.KeyOriginCut.torsor_baseChange_point) | (exact GlobalTheory.KeyOriginCut.torsor_baseChange_point) | (intros; apply GlobalTheory.KeyOriginCut.torsor_baseChange_point  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseChangeRetract
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomExtTensorAlt
namespace GlobalTheory.TensorRingHomExtensionality

open scoped TensorProduct

theorem ringHom_ext_tensor {R S B C : Type} [CommRing R] [CommRing S] [CommRing B] [CommRing C]
    [Algebra R S] [Algebra R B] (φ ψ : TensorProduct R S B →+* C)
    (h₁ : ∀ s : S, φ (s ⊗ₜ[R] (1 : B)) = ψ (s ⊗ₜ[R] (1 : B)))
    (h₂ : ∀ b : B, φ ((1 : S) ⊗ₜ[R] b) = ψ ((1 : S) ⊗ₜ[R] b)) : φ = ψ := by
  refine RingHom.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul s b =>
    have h : s ⊗ₜ[R] b = (s ⊗ₜ[R] (1 : B)) * ((1 : S) ⊗ₜ[R] b) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [h, map_mul, map_mul, h₁, h₂]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

end GlobalTheory.TensorRingHomExtensionality
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseChangeRetract
open IsLocalRing Polynomial

open scoped TensorProduct

noncomputable section

namespace GlobalTheory.KeyOriginBaseChangeCons

theorem tensor_ringHom_ext {R S B C : Type} [CommRing R] [CommRing S] [CommRing B] [CommRing C]
    [Algebra R S] [Algebra R B] (φ ψ : S ⊗[R] B →+* C)
    (h₁ : ∀ s : S, φ (s ⊗ₜ[R] (1 : B)) = ψ (s ⊗ₜ[R] (1 : B)))
    (h₂ : ∀ b : B, φ ((1 : S) ⊗ₜ[R] b) = ψ ((1 : S) ⊗ₜ[R] b)) : φ = ψ := by
  first
  | exact @_root_.GlobalTheory.TensorRingHomExtensionality.ringHom_ext_tensor
  | exact _root_.GlobalTheory.TensorRingHomExtensionality.ringHom_ext_tensor
  | (apply _root_.GlobalTheory.TensorRingHomExtensionality.ringHom_ext_tensor <;> assumption)
  | (intros; apply _root_.GlobalTheory.TensorRingHomExtensionality.ringHom_ext_tensor <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TensorRingHomExtensionality.ringHom_ext_tensor <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TensorRingHomExtensionality.ringHom_ext_tensor ..)

theorem one_tmul_algebraMap {R S B : Type} [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra R B] (r : R) :
    (1 : S) ⊗ₜ[R] algebraMap R B r = algebraMap R S r ⊗ₜ[R] (1 : B) := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

theorem sub_C_coeff_mem {R : Type} [CommRing R] (p : Polynomial R) :
    p - C (p.coeff 0) ∈ Ideal.span {(X : Polynomial R)} :=
  Ideal.mem_span_singleton.mpr X_dvd_sub_C

theorem mem_originIdeal_iff {R : Type} [CommRing R] [IsLocalRing R] (f : Polynomial R) :
    f ∈ GlobalTheory.KeyOriginCut.originIdeal R ↔ f.coeff 0 ∈ maximalIdeal R := by
  constructor
  · intro hf
    have hle : GlobalTheory.KeyOriginCut.originIdeal R ≤ (maximalIdeal R).comap (constantCoeff (R := R)) := by
      refine sup_le ?_ ?_
      · rw [Ideal.map_le_iff_le_comap]
        intro a ha
        simpa [Ideal.mem_comap] using ha
      · rw [Ideal.span_le]
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst hx
        simp [Ideal.mem_comap]
    simpa [Ideal.mem_comap] using hle hf
  · intro hf
    have h1 : C (f.coeff 0) ∈ GlobalTheory.KeyOriginCut.originIdeal R :=
      Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hf)
    have h2 : f - C (f.coeff 0) ∈ GlobalTheory.KeyOriginCut.originIdeal R :=
      Ideal.mem_sup_right (sub_C_coeff_mem f)
    simpa using Ideal.add_mem _ h2 h1

theorem comap_maximalIdeal_eq_originIdeal {T O A₁ : Type} [CommRing T] [IsLocalRing T] [CommRing O]
    [IsLocalRing O] [Algebra T O] [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O]
    [IsLocalHom (algebraMap T O)] (hXO : algebraMap (Polynomial T) O X ∈ maximalIdeal O)
    [CommRing A₁] [IsLocalRing A₁] (i₁ : A₁ →+* T) [IsLocalHom i₁] :
    (maximalIdeal O).comap ((algebraMap (Polynomial T) O).comp (mapRingHom i₁)) =
      GlobalTheory.KeyOriginCut.originIdeal A₁ := by
  ext p
  rw [Ideal.mem_comap, mem_originIdeal_iff, RingHom.comp_apply, coe_mapRingHom]
  set q := p.map i₁
  have hsplit : algebraMap (Polynomial T) O q =
      algebraMap (Polynomial T) O (q - C (q.coeff 0)) + algebraMap T O (q.coeff 0) := by
    rw [map_sub, IsScalarTower.algebraMap_apply T (Polynomial T) O, algebraMap_eq]; ring
  have hX : algebraMap (Polynomial T) O (q - C (q.coeff 0)) ∈ maximalIdeal O := by
    obtain ⟨r, hr⟩ := (X_dvd_sub_C (p := q))
    rw [hr, map_mul]
    exact Ideal.mul_mem_right _ _ hXO
  rw [hsplit]
  constructor
  · intro h
    have h' : algebraMap T O (q.coeff 0) ∈ maximalIdeal O := by
      have := Ideal.sub_mem _ h hX
      simpa using this
    rw [mem_maximalIdeal, map_mem_nonunits_iff, ← mem_maximalIdeal, coeff_map,
      mem_maximalIdeal, map_mem_nonunits_iff, ← mem_maximalIdeal] at h'
    exact h'
  · intro h
    refine Ideal.add_mem _ hX ?_
    rw [mem_maximalIdeal, map_mem_nonunits_iff, ← mem_maximalIdeal, coeff_map,
      mem_maximalIdeal, map_mem_nonunits_iff, ← mem_maximalIdeal]
    exact h

theorem exists_mul_mem_span_X {A EA : Type} [CommRing A] [IsNoetherianRing A] [CommRing EA]
    [Algebra (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA] (QA : Ideal EA) [QA.IsPrime]
    (ρ : Localization.AtPrime QA →+* A)
    (hker : RingHom.ker ρ = Ideal.span {algebraMap (Polynomial A) (Localization.AtPrime QA) X}) :
    ∃ s ∉ QA, ∀ e : EA, ρ (algebraMap EA (Localization.AtPrime QA) e) = 0 →
      s * e ∈ Ideal.span {algebraMap (Polynomial A) EA X} := by
  haveI : IsNoetherianRing EA := Algebra.FiniteType.isNoetherianRing (Polynomial A) EA
  set L := Localization.AtPrime QA
  set I := RingHom.ker (ρ.comp (algebraMap EA L))
  set N := Ideal.span {algebraMap (Polynomial A) EA X}
  have key : ∀ (J : Ideal EA) (hJ : J.FG), J ≤ I → ∃ s ∉ QA, ∀ e ∈ J, s * e ∈ N := by
    intro J hJ
    induction J, hJ using Submodule.fg_induction with
    | singleton x =>
      intro hx
      have hxI : x ∈ I := hx (Submodule.mem_span_singleton_self x)
      have hk : algebraMap EA L x ∈ RingHom.ker ρ := hxI
      rw [hker, Ideal.mem_span_singleton'] at hk
      obtain ⟨a, ha⟩ := hk
      obtain ⟨⟨y, m⟩, hy⟩ := IsLocalization.surj QA.primeCompl a
      have he : algebraMap EA L (y * algebraMap (Polynomial A) EA X) =
          algebraMap EA L (m * x) := by
        rw [map_mul, map_mul, ← ha, ← IsScalarTower.algebraMap_apply, ← hy]
        simp only at *
        ring
      obtain ⟨u, hu⟩ := (IsLocalization.eq_iff_exists QA.primeCompl L).mp he
      refine ⟨u * m, (u * m).2, ?_⟩
      intro e hex
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hex
      have : (u : EA) * (y * algebraMap (Polynomial A) EA X) ∈ N :=
        Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))
      rw [hu] at this
      have h2 := Ideal.mul_mem_left N c this
      rw [smul_eq_mul]
      convert h2 using 1
      push_cast
      ring
    | sup J₁ J₂ _ _ h₁ h₂ =>
      intro hle
      obtain ⟨s₁, hs₁, H₁⟩ := h₁ (le_trans le_sup_left hle)
      obtain ⟨s₂, hs₂, H₂⟩ := h₂ (le_trans le_sup_right hle)
      refine ⟨s₁ * s₂, fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hs₁ hs₂, ?_⟩
      intro e he
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp he
      rw [mul_add]
      refine N.add_mem ?_ ?_
      · have := N.mul_mem_left s₂ (H₁ y hy)
        convert this using 1; ring
      · have := N.mul_mem_left s₁ (H₂ z hz)
        convert this using 1; ring
  obtain ⟨s, hs, H⟩ := key I (IsNoetherian.noetherian I) le_rfl
  exact ⟨s, hs, fun e he => H e he⟩

end GlobalTheory.KeyOriginBaseChangeCons

namespace GlobalTheory.KeyOriginBaseChangeCons

theorem exists_baseChange_retract : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O],
    IsLocalHom (algebraMap T O) → algebraMap (Polynomial T) O Polynomial.X ∈ maximalIdeal O →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (i : A →+* T)
      (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O) (ρ : Localization.AtPrime QA →+* A),
    QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A →
    jA.comp (algebraMap (Polynomial A) (Localization.AtPrime QA)) =
      (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) →
    GlobalTheory.KeyOriginEnlarge.Retracts T O A i EA QA jA ρ →
    ∀ (A₁ : Type) [CommRing A₁] [IsDomain A₁] [IsLocalRing A₁] (j : A →+* A₁) (i₁ : A₁ →+* T),
      Function.Injective i₁ → IsLocalHom i₁ → i₁.comp j = i →
    ∃ (EA₁ : Type) (_ : CommRing EA₁) (_ : Algebra (Polynomial A₁) EA₁) (_ : Algebra A₁ EA₁)
      (_ : IsScalarTower A₁ (Polynomial A₁) EA₁) (_ : Algebra.Etale (Polynomial A₁) EA₁)
      (QA₁ : Ideal EA₁) (_ : QA₁.IsPrime) (jA₁ : Localization.AtPrime QA₁ →+* O)
      (γ₀ : EA →+* EA₁) (γ : Localization.AtPrime QA →+* Localization.AtPrime QA₁) (ρ' : EA₁ →+* A₁),
      QA₁.comap (algebraMap (Polynomial A₁) EA₁) = GlobalTheory.KeyOriginCut.originIdeal A₁ ∧
      jA₁.comp (algebraMap (Polynomial A₁) (Localization.AtPrime QA₁)) =
        (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i₁) ∧
      jA₁.comp γ = jA ∧
      γ.comp (algebraMap EA (Localization.AtPrime QA)) = (algebraMap EA₁ (Localization.AtPrime QA₁)).comp γ₀ ∧
      γ.comp (algebraMap A (Localization.AtPrime QA)) = (algebraMap A₁ (Localization.AtPrime QA₁)).comp j ∧
      ρ'.comp γ₀ = j.comp (ρ.comp (algebraMap EA (Localization.AtPrime QA))) ∧
      ρ'.comp (algebraMap A₁ EA₁) = RingHom.id A₁ ∧
      ρ' (algebraMap (Polynomial A₁) EA₁ Polynomial.X) = 0 ∧
      (∀ x : EA₁, algebraMap T O (i₁ (ρ' x)) - jA₁ (algebraMap EA₁ (Localization.AtPrime QA₁) x) ∈
        Ideal.span {algebraMap (Polynomial T) O Polynomial.X}) ∧
      (∀ x : EA₁, ρ' x = 0 → ∃ s ∉ QA₁, s * x ∈ Ideal.span {algebraMap (Polynomial A₁) EA₁ Polynomial.X}) := by
  intro T O _ _ _ _ _ _ _ _ hTO hXO A _ _ _ _ i EA _ _ _ _ _ QA _ jA ρ hQA hjA hρ A₁ _ _ _ j i₁ hi₁ hloc hij
  haveI := hTO
  haveI := hloc
  letI algP : Algebra (Polynomial A) (Polynomial A₁) := (mapRingHom j).toAlgebra
  letI algO : Algebra (Polynomial A) O := ((algebraMap (Polynomial T) O).comp (mapRingHom i)).toAlgebra
  set L := Localization.AtPrime QA with hL

  have hρpoly : ρ.comp (algebraMap (Polynomial A) L) = evalRingHom 0 := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · rw [RingHom.comp_apply, ← algebraMap_eq (R := A), ← IsScalarTower.algebraMap_apply,
        ← RingHom.comp_apply ρ, hρ.1, algebraMap_eq]
      simp
    · have hx : algebraMap (Polynomial A) L X ∈ RingHom.ker ρ := by
        rw [hρ.2.1]; exact Ideal.mem_span_singleton_self _
      rw [RingHom.comp_apply, RingHom.mem_ker.mp hx]; simp
  let f₁ : Polynomial A₁ →ₐ[Polynomial A] O :=
    { toRingHom := (algebraMap (Polynomial T) O).comp (mapRingHom i₁)
      commutes' := fun r => by
        show algebraMap (Polynomial T) O (mapRingHom i₁ (mapRingHom j r)) =
          algebraMap (Polynomial T) O (mapRingHom i r)
        rw [coe_mapRingHom, coe_mapRingHom, coe_mapRingHom, Polynomial.map_map, hij] }
  let f₂ : EA →ₐ[Polynomial A] O :=
    { toRingHom := jA.comp (algebraMap EA L)
      commutes' := fun r => by
        show jA (algebraMap EA L (algebraMap (Polynomial A) EA r)) =
          algebraMap (Polynomial T) O (mapRingHom i r)
        rw [← IsScalarTower.algebraMap_apply (Polynomial A) EA L r]
        exact congrArg (fun φ => φ r) hjA }
  let EA₁ := TensorProduct (Polynomial A) (Polynomial A₁) EA
  let g : EA₁ →+* O := (Algebra.TensorProduct.lift f₁ f₂ (fun _ _ => Commute.all _ _)).toRingHom
  have hg : ∀ p e, g (p ⊗ₜ[Polynomial A] e) = algebraMap (Polynomial T) O (p.map i₁) * jA (algebraMap EA L e) :=
    fun p e => Algebra.TensorProduct.lift_tmul _ _ _ p e
  letI iA1 : Algebra A₁ EA₁ := ((algebraMap (Polynomial A₁) EA₁).comp C).toAlgebra
  have hmapP : ∀ p : Polynomial A₁, algebraMap (Polynomial A₁) EA₁ p = p ⊗ₜ[Polynomial A] (1 : EA) := by
    intro p; rw [Algebra.TensorProduct.algebraMap_apply]; rfl
  have hAP : ∀ a : A₁, algebraMap A₁ EA₁ a = algebraMap (Polynomial A₁) EA₁ (C a) := fun a => rfl
  have hmapA : ∀ a : A₁, algebraMap A₁ EA₁ a = C a ⊗ₜ[Polynomial A] (1 : EA) := fun a => hmapP (C a)
  let γ₀ : EA →+* EA₁ := (Algebra.TensorProduct.includeRight : EA →ₐ[Polynomial A] EA₁).toRingHom
  have hγ₀ : ∀ e, γ₀ e = (1 : Polynomial A₁) ⊗ₜ[Polynomial A] e := fun e => rfl
  have hγ₀A : ∀ a : A, γ₀ (algebraMap A EA a) = algebraMap A₁ EA₁ (j a) := by
    intro a
    rw [hγ₀, hmapA, IsScalarTower.algebraMap_apply A (Polynomial A) EA, one_tmul_algebraMap, algebraMap_eq]
    show (mapRingHom j (C a)) ⊗ₜ[Polynomial A] (1 : EA) = _
    rw [coe_mapRingHom, Polynomial.map_C]
  have hγ₀X : γ₀ (algebraMap (Polynomial A) EA X) = algebraMap (Polynomial A₁) EA₁ X := by
    rw [hγ₀, hmapP, one_tmul_algebraMap]
    show (mapRingHom j X) ⊗ₜ[Polynomial A] (1 : EA) = _
    rw [coe_mapRingHom, Polynomial.map_X]
  have hgP : ∀ p, g (algebraMap (Polynomial A₁) EA₁ p) = algebraMap (Polynomial T) O (p.map i₁) := by
    intro p; rw [hmapP, hg, map_one, map_one, mul_one]
  have hgγ : ∀ e, g (γ₀ e) = jA (algebraMap EA L e) := by
    intro e; rw [hγ₀, hg, Polynomial.map_one, map_one, one_mul]
  let QA₁ : Ideal EA₁ := (maximalIdeal O).comap g
  have hunit : ∀ y : EA₁, y ∉ QA₁ → IsUnit (g y) := by
    intro y hy
    by_contra h
    exact hy ((mem_maximalIdeal _).2 h)
  let L₁ := Localization.AtPrime QA₁
  let jA₁ : L₁ →+* O := IsLocalization.lift (M := QA₁.primeCompl) (g := g) (fun y => hunit y y.2)
  have hjA₁ : ∀ x, jA₁ (algebraMap EA₁ L₁ x) = g x := fun x => IsLocalization.lift_eq _ x
  have hγ₀Q : ∀ e : EA, e ∉ QA → γ₀ e ∉ QA₁ := by
    intro e he h
    have h1 : g (γ₀ e) ∈ maximalIdeal O := h
    rw [hgγ] at h1
    have hu : IsUnit (algebraMap EA L e) := IsLocalization.map_units L (⟨e, he⟩ : QA.primeCompl)
    exact (mem_maximalIdeal _).1 h1 (hu.map jA)
  let γ : L →+* L₁ := IsLocalization.lift (M := QA.primeCompl) (g := (algebraMap EA₁ L₁).comp γ₀)
    (fun y => IsLocalization.map_units L₁ (⟨γ₀ y, hγ₀Q y y.2⟩ : QA₁.primeCompl))
  have hγ : ∀ e, γ (algebraMap EA L e) = algebraMap EA₁ L₁ (γ₀ e) := fun e => IsLocalization.lift_eq _ e
  have hρA : ∀ b : A, ρ (algebraMap EA L (algebraMap A EA b)) = b := by
    intro b; rw [← IsScalarTower.algebraMap_apply A EA L b]; exact congrArg (fun φ => φ b) hρ.1
  let Xs : Ideal (Polynomial A₁) := Ideal.span {X}
  let φ0 : Polynomial A₁ ⧸ Xs →+* A₁ := Ideal.Quotient.lift Xs (evalRingHom 0) (fun a ha => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    simp)
  have hφ0 : ∀ p, φ0 (Ideal.Quotient.mk Xs p) = eval 0 p := fun p => Ideal.Quotient.lift_mk _ _ _
  let r₁ : Polynomial A₁ →ₐ[Polynomial A] Polynomial A₁ ⧸ Xs := Ideal.Quotient.mkₐ (Polynomial A) Xs
  let r₂ : EA →ₐ[Polynomial A] Polynomial A₁ ⧸ Xs :=
    { toRingHom := (Ideal.Quotient.mk Xs).comp (C.comp (j.comp (ρ.comp (algebraMap EA L))))
      commutes' := fun r => by
        show Ideal.Quotient.mk Xs (C (j (ρ (algebraMap EA L (algebraMap (Polynomial A) EA r))))) =
          Ideal.Quotient.mk Xs (mapRingHom j r)
        rw [← IsScalarTower.algebraMap_apply (Polynomial A) EA L r, ← RingHom.comp_apply ρ, hρpoly,
          Ideal.Quotient.eq, coe_mapRingHom, coe_evalRingHom, ← coeff_zero_eq_eval_zero]
        have : C (j (r.coeff 0)) - r.map j = -((r.map j) - C ((r.map j).coeff 0)) := by
          rw [coeff_map]; ring
        rw [this]
        exact Xs.neg_mem (sub_C_coeff_mem _) }
  let ρ' : EA₁ →+* A₁ := φ0.comp (Algebra.TensorProduct.lift r₁ r₂ (fun _ _ => Commute.all _ _)).toRingHom
  have hρ' : ∀ p e, ρ' (p ⊗ₜ[Polynomial A] e) = eval 0 p * j (ρ (algebraMap EA L e)) := by
    intro p e
    show φ0 (Algebra.TensorProduct.lift r₁ r₂ (fun _ _ => Commute.all _ _) (p ⊗ₜ[Polynomial A] e)) = _
    rw [Algebra.TensorProduct.lift_tmul, map_mul]
    show φ0 (Ideal.Quotient.mk Xs p) * φ0 (Ideal.Quotient.mk Xs (C (j (ρ (algebraMap EA L e))))) = _
    rw [hφ0, hφ0, eval_C]
  have hρ'P : ∀ p, ρ' (algebraMap (Polynomial A₁) EA₁ p) = eval 0 p := by
    intro p; rw [hmapP, hρ']; simp only [map_one, mul_one]
  have hρ'γ : ∀ e, ρ' (γ₀ e) = j (ρ (algebraMap EA L e)) := by
    intro e; rw [hγ₀, hρ', eval_one, one_mul]
  have hρ'A : ∀ a, ρ' (algebraMap A₁ EA₁ a) = a := by
    intro a
    show ρ' (algebraMap (Polynomial A₁) EA₁ (C a)) = a
    rw [hρ'P, eval_C]
  have hcong : ∀ x : EA₁, algebraMap T O (i₁ (ρ' x)) - jA₁ (algebraMap EA₁ L₁ x) ∈
      Ideal.span {algebraMap (Polynomial T) O X} := by
    set I := Ideal.span {algebraMap (Polynomial T) O X}
    have hext : (Ideal.Quotient.mk I).comp ((algebraMap T O).comp (i₁.comp ρ')) =
        (Ideal.Quotient.mk I).comp g := by
      apply tensor_ringHom_ext
      · intro p
        simp only [RingHom.comp_apply]
        rw [Ideal.Quotient.eq]
        rw [← hmapP p, hρ'P, hgP, IsScalarTower.algebraMap_apply T (Polynomial T) O, algebraMap_eq, ← map_sub]
        have : C (i₁ (eval 0 p)) - p.map i₁ = -((p.map i₁) - C ((p.map i₁).coeff 0)) := by
          rw [coeff_map, coeff_zero_eq_eval_zero]; ring
        rw [this, map_neg]
        exact I.neg_mem (Ideal.mem_span_singleton.mpr (map_dvd _ X_dvd_sub_C))
      · intro e
        simp only [RingHom.comp_apply]
        rw [Ideal.Quotient.eq]
        rw [← hγ₀ e, hρ'γ, hgγ, ← RingHom.comp_apply i₁ j, hij]
        exact hρ.2.2 _
    intro x
    rw [hjA₁, ← Ideal.Quotient.eq]
    exact congrArg (fun φ => φ x) hext
  obtain ⟨s₀, hs₀, Hs₀⟩ := exists_mul_mem_span_X QA ρ hρ.2.1
  have hker : ∀ x : EA₁, ρ' x = 0 →
      ∃ s ∉ QA₁, s * x ∈ Ideal.span {algebraMap (Polynomial A₁) EA₁ X} := by
    set N₁ := Ideal.span {algebraMap (Polynomial A₁) EA₁ X}
    set Ik := RingHom.ker (ρ.comp (algebraMap EA L))
    set J := N₁ ⊔ Ik.map γ₀
    have hext : (Ideal.Quotient.mk J).comp ((algebraMap A₁ EA₁).comp ρ') = Ideal.Quotient.mk J := by
      apply tensor_ringHom_ext
      · intro p
        simp only [RingHom.comp_apply]
        rw [Ideal.Quotient.eq]
        rw [← hmapP p, hρ'P, hAP, ← map_sub]
        have : C (eval 0 p) - p = -(p - C (p.coeff 0)) := by rw [coeff_zero_eq_eval_zero]; ring
        rw [this, map_neg]
        refine J.neg_mem (Ideal.mem_sup_left ?_)
        exact Ideal.mem_span_singleton.mpr (map_dvd _ X_dvd_sub_C)
      · intro e
        simp only [RingHom.comp_apply]
        rw [Ideal.Quotient.eq]
        rw [← hγ₀ e, hρ'γ, ← hγ₀A, ← map_sub]
        refine Ideal.mem_sup_right (Ideal.mem_map_of_mem _ ?_)
        rw [RingHom.mem_ker, RingHom.comp_apply, map_sub, map_sub, hρA, sub_self]
    intro x hx
    have hxJ : x ∈ J := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← congrArg (fun φ => φ x) hext]
      simp [hx]
    refine ⟨γ₀ s₀, hγ₀Q s₀ hs₀, ?_⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hxJ
    rw [mul_add]
    refine N₁.add_mem (N₁.mul_mem_left _ hy) ?_
    have h1 : Ideal.span {γ₀ s₀} * Ik.map γ₀ = (Ideal.span {s₀} * Ik).map γ₀ := by
      rw [Ideal.map_mul, Ideal.map_span, Set.image_singleton]
    have h2 : Ideal.span {s₀} * Ik ≤ Ideal.span {algebraMap (Polynomial A) EA X} := by
      rw [Ideal.span_singleton_mul_le_iff]
      intro w hw; exact Hs₀ w (RingHom.mem_ker.mp hw)
    have h3 : (Ideal.span {algebraMap (Polynomial A) EA X}).map γ₀ = N₁ := by
      rw [Ideal.map_span, Set.image_singleton, hγ₀X]
    have h4 := Ideal.mul_mem_mul (Ideal.mem_span_singleton_self (γ₀ s₀)) hz
    rw [h1] at h4
    exact h3 ▸ Ideal.map_mono h2 h4
  refine ⟨EA₁, inferInstance, inferInstance, iA1, IsScalarTower.of_algebraMap_eq (fun x => ?_),
    inferInstance, QA₁, inferInstance, jA₁, γ₀, γ, ρ', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hcong, hker⟩
  · show algebraMap (Polynomial A₁) EA₁ (C x) = algebraMap (Polynomial A₁) EA₁ (algebraMap A₁ (Polynomial A₁) x)
    rw [algebraMap_eq]
  · rw [← comap_maximalIdeal_eq_originIdeal hXO i₁]
    ext p
    show g (algebraMap _ EA₁ p) ∈ maximalIdeal O ↔ _
    rw [Ideal.mem_comap, hgP]; rfl
  · refine RingHom.ext fun p => ?_
    rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply (Polynomial A₁) EA₁ L₁, hjA₁, hgP]; rfl
  · refine IsLocalization.ringHom_ext QA.primeCompl (RingHom.ext fun e => ?_)
    simp only [RingHom.comp_apply]
    rw [hγ, hjA₁, hgγ]
  · exact RingHom.ext fun e => hγ e
  · refine RingHom.ext fun a => ?_
    rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply A EA L, hγ, hγ₀A, RingHom.comp_apply,
      IsScalarTower.algebraMap_apply A₁ EA₁ L₁]
  · exact RingHom.ext fun e => hρ'γ e
  · exact RingHom.ext fun a => hρ'A a
  · rw [hρ'P, eval_X]

end GlobalTheory.KeyOriginBaseChangeCons
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseChangeRetractStatement
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_baseChange_retract_alt : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O],
    IsLocalHom (algebraMap T O) → algebraMap (Polynomial T) O Polynomial.X ∈ maximalIdeal O →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (i : A →+* T)
      (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O) (ρ : Localization.AtPrime QA →+* A),
    QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A →
    jA.comp (algebraMap (Polynomial A) (Localization.AtPrime QA)) =
      (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) →
    GlobalTheory.KeyOriginEnlarge.Retracts T O A i EA QA jA ρ →
    ∀ (A₁ : Type) [CommRing A₁] [IsDomain A₁] [IsLocalRing A₁] (j : A →+* A₁) (i₁ : A₁ →+* T),
      Function.Injective i₁ → IsLocalHom i₁ → i₁.comp j = i →
    ∃ (EA₁ : Type) (_ : CommRing EA₁) (_ : Algebra (Polynomial A₁) EA₁) (_ : Algebra A₁ EA₁)
      (_ : IsScalarTower A₁ (Polynomial A₁) EA₁) (_ : Algebra.Etale (Polynomial A₁) EA₁)
      (QA₁ : Ideal EA₁) (_ : QA₁.IsPrime) (jA₁ : Localization.AtPrime QA₁ →+* O)
      (γ₀ : EA →+* EA₁) (γ : Localization.AtPrime QA →+* Localization.AtPrime QA₁) (ρ' : EA₁ →+* A₁),
      QA₁.comap (algebraMap (Polynomial A₁) EA₁) = GlobalTheory.KeyOriginCut.originIdeal A₁ ∧
      jA₁.comp (algebraMap (Polynomial A₁) (Localization.AtPrime QA₁)) =
        (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i₁) ∧
      jA₁.comp γ = jA ∧
      γ.comp (algebraMap EA (Localization.AtPrime QA)) = (algebraMap EA₁ (Localization.AtPrime QA₁)).comp γ₀ ∧
      γ.comp (algebraMap A (Localization.AtPrime QA)) = (algebraMap A₁ (Localization.AtPrime QA₁)).comp j ∧
      ρ'.comp γ₀ = j.comp (ρ.comp (algebraMap EA (Localization.AtPrime QA))) ∧
      ρ'.comp (algebraMap A₁ EA₁) = RingHom.id A₁ ∧
      ρ' (algebraMap (Polynomial A₁) EA₁ Polynomial.X) = 0 ∧
      (∀ x : EA₁, algebraMap T O (i₁ (ρ' x)) - jA₁ (algebraMap EA₁ (Localization.AtPrime QA₁) x) ∈
        Ideal.span {algebraMap (Polynomial T) O Polynomial.X}) ∧
      (∀ x : EA₁, ρ' x = 0 → ∃ s ∉ QA₁, s * x ∈ Ideal.span {algebraMap (Polynomial A₁) EA₁ Polynomial.X}) := by
  first | (exact @GlobalTheory.KeyOriginBaseChangeCons.exists_baseChange_retract) | (exact GlobalTheory.KeyOriginBaseChangeCons.exists_baseChange_retract) | (intros; apply GlobalTheory.KeyOriginBaseChangeCons.exists_baseChange_retract <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseChangeFittingDatumRetraction
open IsLocalRing Polynomial

noncomputable section

namespace GlobalTheory.KeyOriginEnlarge

theorem exists_baseChange_fits : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O]
    (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (q : ℕ), 0 < q →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T)
      (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O)
      (ψA : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
      (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
    GlobalTheory.KeyOriginEnlarge.Fits T O q A i EA QA jA ψA DA actA →
    ∀ ρ : Localization.AtPrime QA →+* A, GlobalTheory.KeyOriginEnlarge.Retracts T O A i EA QA jA ρ →
    ∀ (A₁ : Type) [CommRing A₁] [IsDomain A₁] [IsLocalRing A₁] [IsNoetherianRing A₁] [IsIntegrallyClosed A₁]
      [Algebra.EssFiniteType ℤ A₁] (j : A →+* A₁) (i₁ : A₁ →+* T),
      Function.Injective j → Function.Injective i₁ → IsLocalHom i₁ → i₁.comp j = i →
    ∃ (EA₁ : Type) (_ : CommRing EA₁) (_ : Algebra (Polynomial A₁) EA₁) (_ : Algebra A₁ EA₁)
      (_ : IsScalarTower A₁ (Polynomial A₁) EA₁) (_ : Algebra.Etale (Polynomial A₁) EA₁)
      (QA₁ : Ideal EA₁) (_ : QA₁.IsPrime) (jA₁ : Localization.AtPrime QA₁ →+* O)
      (ψA₁ : GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁) →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA₁ : Type) (_ : CommRing DA₁) (_ : Algebra (GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁)) DA₁)
      (actA₁ : Multiplicative (ZMod q) →* (DA₁ ≃ₐ[GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁)] DA₁))
      (ρ₁ : Localization.AtPrime QA₁ →+* A₁),
      GlobalTheory.KeyOriginEnlarge.Fits T O q A₁ i₁ EA₁ QA₁ jA₁ ψA₁ DA₁ actA₁ ∧
      GlobalTheory.KeyOriginEnlarge.Retracts T O A₁ i₁ EA₁ QA₁ jA₁ ρ₁ ∧
      ∃ (β : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁))
        (h : DA →+* DA₁),
        ψA₁.comp β = ψA ∧
        h.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA) =
          (algebraMap (GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁)) DA₁).comp β ∧
        ∀ σ : DA →+* FractionRing A₁,
          (σ.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA)).comp
              (algebraMap (Localization.AtPrime QA) (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA))) =
            (algebraMap A₁ (FractionRing A₁)).comp (j.comp ρ) →
          ∃ σ₁ : DA₁ →+* FractionRing A₁,
            (σ₁.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁)) DA₁)).comp
                (algebraMap (Localization.AtPrime QA₁) (GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁))) =
              (algebraMap A₁ (FractionRing A₁)).comp ρ₁ := by
  intro T O _ _ _ _ _ _ _ _ P _ φ hφ hSH hP q hq A _ _ _ _ _ _ i EA _ _ _ _ _ QA _ jA ψA DA _ _ actA hFits ρ hRet
    A₁ _ _ _ _ _ _ j i₁ hj hi₁ hi₁l hij
  haveI hφl : IsLocalHom φ := hSH.2.2.1
  have hX : algebraMap (Polynomial T) O Polynomial.X ∈ maximalIdeal O := by
    rw [← hφ, RingHom.comp_apply]
    apply map_nonunit φ
    refine (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime P) P _).2 ?_
    rw [hP]; exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
  have hTO : IsLocalHom (algebraMap T O) := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have h1 : Polynomial.C a ∈ P := by
      rw [hP]; exact Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ((IsLocalRing.mem_maximalIdeal _).2 hna))
    refine (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime P) P (Polynomial.C a)).1
      (isUnit_of_map_unit φ _ ?_) h1
    rw [← RingHom.comp_apply, hφ]
    rw [IsScalarTower.algebraMap_apply T (Polynomial T) O] at ha
    exact ha
  obtain ⟨hi, hil, hqu, hQA, hjA, hψA, htors⟩ := hFits
  obtain ⟨EA₁, _, _, _, _, _, QA₁, _, jA₁, γ₀, γ, ρ', hQA₁, hjA₁, hjγ, hγ₀, hγA, hρ'γ, hρ'id, hρ'X, hρ'c, hρ'k⟩ :=
    GlobalTheory.T.exists_baseChange_retract_alt T O hTO hX A i EA QA jA ρ hQA hjA hRet A₁ j i₁ hi₁ hi₁l hij
  obtain ⟨ρ₁, hRet₁, hρ₁⟩ := GlobalTheory.T.keyOrigin_retraction_localises T O A₁ EA₁ i₁ hi₁l hTO QA₁ jA₁ ρ' hX hρ'id hρ'X hρ'c hρ'k
  have hjA₁c : jA₁.comp (algebraMap A₁ (Localization.AtPrime QA₁)) = (algebraMap T O).comp i₁ := by
    ext a
    have e1 : algebraMap A₁ (Localization.AtPrime QA₁) a =
        algebraMap (Polynomial A₁) (Localization.AtPrime QA₁) (Polynomial.C a) := by
      rw [IsScalarTower.algebraMap_apply A₁ EA₁ (Localization.AtPrime QA₁),
        IsScalarTower.algebraMap_apply A₁ (Polynomial A₁) EA₁,
        IsScalarTower.algebraMap_apply (Polynomial A₁) EA₁ (Localization.AtPrime QA₁)]
      rfl
    rw [RingHom.comp_apply, e1, ← RingHom.comp_apply, hjA₁, RingHom.comp_apply, Polynomial.coe_mapRingHom,
      Polynomial.map_C, RingHom.comp_apply, IsScalarTower.algebraMap_apply T (Polynomial T) O]
    rfl
  obtain ⟨ψA₁, β, hψA₁, hψβ, hβ⟩ := GlobalTheory.T.generic_fibre_compatibility T O A A₁ _ _ j i₁ hj hi₁ jA jA₁ γ ψA hjA₁c hγA hjγ hψA
  have hργ : ρ₁.comp γ = j.comp ρ := by
    apply IsLocalization.ringHom_ext QA.primeCompl
    rw [RingHom.comp_assoc, hγ₀, ← RingHom.comp_assoc, hρ₁, hρ'γ, RingHom.comp_assoc]
  obtain ⟨DA₁, _, _, actA₁, h, htors₁, hh, hpt⟩ :=
    GlobalTheory.T.zmodTorsor_baseChange_transport_point A A₁ _ _ j γ ρ ρ₁ β hβ hRet₁.1 hργ q hq DA actA htors
  refine ⟨EA₁, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, QA₁, inferInstance,
    jA₁, ψA₁, DA₁, inferInstance, inferInstance, actA₁, ρ₁, ⟨hi₁, hi₁l, ?_, hQA₁, hjA₁, hψA₁, htors₁⟩, hRet₁,
    β, h, hψβ, hh, hpt⟩
  have := hqu.map j
  simpa using this

end GlobalTheory.KeyOriginEnlarge
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseChangeFittingDatumRetractionStatement
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_baseChange_fittingDatum_retraction : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O]
    (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (q : ℕ), 0 < q →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T)
      (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O)
      (ψA : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
      (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
    GlobalTheory.KeyOriginEnlarge.Fits T O q A i EA QA jA ψA DA actA →
    ∀ ρ : Localization.AtPrime QA →+* A, GlobalTheory.KeyOriginEnlarge.Retracts T O A i EA QA jA ρ →
    ∀ (A₁ : Type) [CommRing A₁] [IsDomain A₁] [IsLocalRing A₁] [IsNoetherianRing A₁] [IsIntegrallyClosed A₁]
      [Algebra.EssFiniteType ℤ A₁] (j : A →+* A₁) (i₁ : A₁ →+* T),
      Function.Injective j → Function.Injective i₁ → IsLocalHom i₁ → i₁.comp j = i →
    ∃ (EA₁ : Type) (_ : CommRing EA₁) (_ : Algebra (Polynomial A₁) EA₁) (_ : Algebra A₁ EA₁)
      (_ : IsScalarTower A₁ (Polynomial A₁) EA₁) (_ : Algebra.Etale (Polynomial A₁) EA₁)
      (QA₁ : Ideal EA₁) (_ : QA₁.IsPrime) (jA₁ : Localization.AtPrime QA₁ →+* O)
      (ψA₁ : GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁) →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA₁ : Type) (_ : CommRing DA₁) (_ : Algebra (GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁)) DA₁)
      (actA₁ : Multiplicative (ZMod q) →* (DA₁ ≃ₐ[GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁)] DA₁))
      (ρ₁ : Localization.AtPrime QA₁ →+* A₁),
      GlobalTheory.KeyOriginEnlarge.Fits T O q A₁ i₁ EA₁ QA₁ jA₁ ψA₁ DA₁ actA₁ ∧
      GlobalTheory.KeyOriginEnlarge.Retracts T O A₁ i₁ EA₁ QA₁ jA₁ ρ₁ ∧
      ∃ (β : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁))
        (h : DA →+* DA₁),
        ψA₁.comp β = ψA ∧
        h.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA) =
          (algebraMap (GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁)) DA₁).comp β ∧
        ∀ σ : DA →+* FractionRing A₁,
          (σ.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA)).comp
              (algebraMap (Localization.AtPrime QA) (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA))) =
            (algebraMap A₁ (FractionRing A₁)).comp (j.comp ρ) →
          ∃ σ₁ : DA₁ →+* FractionRing A₁,
            (σ₁.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁)) DA₁)).comp
                (algebraMap (Localization.AtPrime QA₁) (GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁))) =
              (algebraMap A₁ (FractionRing A₁)).comp ρ₁ := by
  first | (exact @GlobalTheory.KeyOriginEnlarge.exists_baseChange_fits) | (exact GlobalTheory.KeyOriginEnlarge.exists_baseChange_fits) | (intros; apply GlobalTheory.KeyOriginEnlarge.exists_baseChange_fits <;> assumption)
end
