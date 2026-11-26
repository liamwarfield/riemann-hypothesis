module

public import ReciprocityTheory.GaloisValuations.Global
public import Formalism.ConjugateSelfDual.StatementRest

@[expose] public section

section -- merged from ReciprocityTheory.GaloisValuations.ArithOfA
noncomputable section

open NumberField IsDedekindDomain Pointwise

namespace ReciprocityTheory.Gal

open Formalism.ConjugateSelfDual

section deg

variable {F : Type*} [Field F] [NumberField F]

def locDegree (v : HeightOneSpectrum (𝓞 F)) : ℕ :=
  v.asIdeal.ramificationIdx ℤ * v.asIdeal.inertiaDeg ℤ

theorem isMaximal_span_prime (l : ℕ) [hl : Fact l.Prime] : (Ideal.span {(l : ℤ)}).IsMaximal := by
  first
    | exact PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hl.out).irreducible
    | exact Ideal.IsPrime.isMaximal
        ((Ideal.span_singleton_prime (by exact_mod_cast hl.out.ne_zero)).2
          (Nat.prime_iff_prime_int.mp hl.out))
        (by simp [hl.out.ne_zero])

theorem liesOver_span_iff (l : ℕ) [Fact l.Prime] (P : Ideal (𝓞 F)) [P.IsPrime] :
    P.LiesOver (Ideal.span {(l : ℤ)}) ↔ ((l : ℕ) : 𝓞 F) ∈ P := by
  constructor
  · intro h
    have hmem : ((l : ℤ)) ∈ P.under ℤ := by
      rw [← h.over]
      exact Ideal.mem_span_singleton_self _
    have h2 : algebraMap ℤ (𝓞 F) (l : ℤ) ∈ P := hmem
    simpa using h2
  · intro h
    refine ⟨?_⟩
    refine (isMaximal_span_prime l).eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_
    rw [Ideal.span_le, Set.singleton_subset_iff]
    show algebraMap ℤ (𝓞 F) (l : ℤ) ∈ P
    simpa using h

theorem sum_locDegree (l : ℕ) [Fact l.Prime] (T : Finset (HeightOneSpectrum (𝓞 F)))
    (hT : ∀ v, v ∈ T ↔ ((l : ℕ) : 𝓞 F) ∈ v.asIdeal) :
    ∑ v ∈ T, locDegree v = Module.finrank ℚ F := by
  haveI := isMaximal_span_prime l
  have hl0 : (l : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hp0 : Ideal.span {(l : ℤ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact hl0
  have h := Ideal.sum_ramification_inertia (𝓞 F) ℚ F hp0
  rw [← h]
  refine Finset.sum_nbij (fun v => v.asIdeal) ?_ ?_ ?_ ?_
  · intro v hv
    rw [IsDedekindDomain.mem_primesOverFinset_iff hp0 (𝓞 F)]
    haveI : v.asIdeal.LiesOver (Ideal.span {(l : ℤ)}) :=
      (liesOver_span_iff l v.asIdeal).2 ((hT v).1 hv)
    exact ⟨v.isPrime, inferInstance⟩
  · intro v _ w _ hvw
    exact HeightOneSpectrum.ext hvw
  · intro P hP
    rw [Finset.mem_coe, IsDedekindDomain.mem_primesOverFinset_iff hp0 (𝓞 F)] at hP
    obtain ⟨hPp, hPl⟩ := hP
    have hPne : P ≠ ⊥ := by
      intro hb
      have hm := (liesOver_span_iff l P).1 hPl
      rw [hb, Ideal.mem_bot] at hm
      exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast hm)
    refine ⟨⟨P, hPp, hPne⟩, ?_, rfl⟩
    rw [Finset.mem_coe, hT]
    exact (liesOver_span_iff l P).1 hPl
  · intro v hv
    haveI : v.asIdeal.LiesOver (Ideal.span {(l : ℤ)}) :=
      (liesOver_span_iff l v.asIdeal).2 ((hT v).1 hv)
    haveI := v.isMaximal
    unfold locDegree
    rw [Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(l : ℤ)}) v.asIdeal hp0,
      Ideal.inertiaDeg'_eq_inertiaDeg (Ideal.span {(l : ℤ)}) v.asIdeal]

end deg

section conj

variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]

theorem smul_valuation_le_one_iff (γ : G F Ω) (A : ValuationSubring Ω) (y : Ω) :
    (γ • A).valuation y ≤ 1 ↔ A.valuation ((γ⁻¹ : G F Ω) y) ≤ 1 := by
  rw [ValuationSubring.valuation_le_one_iff, ValuationSubring.valuation_le_one_iff,
    ValuationSubring.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨s, hs, rfl⟩
    show γ⁻¹ • γ • s ∈ A
    rwa [inv_smul_smul]
  · intro h
    exact ⟨γ⁻¹ • y, h, smul_inv_smul γ y⟩

private theorem smul_valuationSubring_valuation_lt_one_iff (γ : G F Ω) (A : ValuationSubring Ω) (y : Ω) :
    (γ • A).valuation y < 1 ↔ A.valuation ((γ⁻¹ : G F Ω) y) < 1 := by
  by_cases hy : y = 0
  · simp [hy]
  · have hy' : (γ⁻¹ : G F Ω) y ≠ 0 := (map_ne_zero (γ⁻¹ : G F Ω)).2 hy
    rw [Valuation.val_lt_one_iff _ hy, Valuation.val_lt_one_iff _ hy', ← not_le, ← not_le,
      smul_valuation_le_one_iff, map_inv₀]

theorem conj_mem_Ine_smul {A : ValuationSubring Ω} {γ σ : G F Ω} (hσ : σ ∈ Ine (F := F) A) :
    γ * σ * γ⁻¹ ∈ Ine (F := F) (γ • A) := by
  obtain ⟨hσ1, hσ2⟩ := hσ
  show γ * σ * γ⁻¹ ∈ Inertia (F := F) (γ • A)
  refine ⟨?_, fun x hx => ?_⟩
  · have h1 : σ • A = A := hσ1
    show (γ * σ * γ⁻¹) • (γ • A) = γ • A
    rw [mul_smul, mul_smul, inv_smul_smul, h1]
  · rw [smul_valuation_le_one_iff] at hx
    rw [smul_valuationSubring_valuation_lt_one_iff]
    have e : (γ⁻¹ : G F Ω) ((γ * σ * γ⁻¹) x - x) =
        σ ((γ⁻¹ : G F Ω) x) - (γ⁻¹ : G F Ω) x := by
      rw [map_sub]
      congr 1
      show (γ⁻¹ : G F Ω) (γ (σ ((γ⁻¹ : G F Ω) x))) = σ ((γ⁻¹ : G F Ω) x)
      first | exact γ.symm_apply_apply _ | simp
    rw [e]
    exact hσ2 _ hx

end conj

end ReciprocityTheory.Gal
end
end

section -- merged from ReciprocityTheory.GaloisValuations.GlobalE
section -- merged from ReciprocityTheory.Hypotheses.Descent
section -- merged from ReciprocityTheory.GaloisValuations.SymplecticRankFourModularity
noncomputable section

open NumberField IsDedekindDomain Polynomial Filter

namespace ReciprocityTheory.Gal

open Formalism.ConjugateSelfDual

section basic

variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {n l : ℕ} [Fact l.Prime]

def tw (e : ℤ) (χ : G F Ω →* (Qbar l)ˣ) : G F Ω →* (Qbar l)ˣ := (cyc F Ω l) ^ e * χ

end basic

section proposals

variable {l : ℕ} [Fact l.Prime]

end proposals

end ReciprocityTheory.Gal
end
end

noncomputable section

open NumberField IsDedekindDomain Polynomial Filter

namespace ReciprocityTheory.Hyp

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal

def resGal (K L Ω : Type*) [Field K] [Field L] [Field Ω] [Algebra K L] [Algebra K Ω] [Algebra L Ω]
    [IsScalarTower K L Ω] : G L Ω →* G K Ω :=
  AlgEquiv.restrictScalarsHom K

end ReciprocityTheory.Hyp
end
end

section -- merged from ReciprocityTheory.GaloisValuations.GlobalEA
noncomputable section

open NumberField IsDedekindDomain Pointwise

namespace ReciprocityTheory.Gal

open Formalism.ConjugateSelfDual ReciprocityTheory.Hyp

section res

variable {F L Ω : Type*} [Field F] [Field L] [Field Ω] [Algebra F L] [Algebra F Ω] [Algebra L Ω]
  [IsScalarTower F L Ω]

@[simp] theorem resGal_apply (σ : G L Ω) (x : Ω) : resGal F L Ω σ x = σ x := rfl

theorem resGal_injective : Function.Injective (resGal F L Ω) := fun σ τ h =>
  AlgEquiv.ext fun x => by simpa using DFunLike.congr_fun h x

theorem continuous_resGal [Algebra.IsAlgebraic F Ω] : Continuous (resGal F L Ω) := by
  refine continuous_of_continuousAt_one (resGal F L Ω) ?_
  rw [ContinuousAt, map_one]
  intro s hs
  obtain ⟨E, hE, hEs⟩ := (krullTopology_mem_nhds_one_iff F Ω s).1 hs
  let b := Module.finBasis F E
  let S : Set Ω := Set.range (fun i => (b i : Ω))
  have hint : ∀ x ∈ S, IsIntegral L x := fun x _ =>
    (Algebra.IsIntegral.isIntegral (R := F) x).tower_top
  have : FiniteDimensional L (IntermediateField.adjoin L S) :=
    IntermediateField.finiteDimensional_adjoin hint
  rw [Filter.mem_map, krullTopology_mem_nhds_one_iff]
  refine ⟨IntermediateField.adjoin L S, this, fun σ hσ => hEs ?_⟩
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
  have hb : ∀ i, σ (b i : Ω) = b i := fun i =>
    hσ _ (IntermediateField.subset_adjoin L S ⟨i, rfl⟩)
  intro x hx
  have hx' : x = ((⟨x, hx⟩ : E) : Ω) := rfl
  rw [hx', ← b.sum_repr ⟨x, hx⟩]
  simp only [IntermediateField.coe_sum, IntermediateField.coe_smul]
  change resGal F L Ω σ _ = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  change σ (((b.repr ⟨x, hx⟩) i) • (b i : Ω)) = _
  rw [← algebraMap_smul L ((b.repr ⟨x, hx⟩) i) (b i : Ω), map_smul, hb]

theorem isAlgClosure_top [IsAlgClosure F Ω] : IsAlgClosure L Ω :=
  ⟨IsAlgClosure.isAlgClosed F, Algebra.IsAlgebraic.tower_top (K := F) L⟩

theorem isClosedEmbedding_resGal [IsAlgClosure F Ω] [CharZero L] :
    Topology.IsClosedEmbedding (resGal F L Ω) := by
  have := isAlgClosure_top (F := F) (L := L) (Ω := Ω)
  have : T2Space (G F Ω) := krullTopology_t2
  exact continuous_resGal.isClosedEmbedding resGal_injective

end res

section places

variable {F L Ω : Type*} [Field F] [NumberField F] [Field L] [NumberField L] [Field Ω] [Algebra F L]
  [Algebra F Ω] [Algebra L Ω] [IsScalarTower F L Ω]


end places

end ReciprocityTheory.Gal
end
end

noncomputable section

open NumberField IsDedekindDomain Pointwise Polynomial

namespace ReciprocityTheory.Gal

open Formalism.ConjugateSelfDual ReciprocityTheory.Hyp

section split

variable {F L Ω : Type*} [Field F] [NumberField F] [Field L] [NumberField L] [Field Ω] [Algebra F L]
  [Algebra F Ω] [Algebra L Ω] [IsScalarTower F L Ω] {A : ValuationSubring Ω}

private theorem mem_decompositionSubgroup_iff_galois_valuations {K : Type*} [Field K] [Algebra K Ω] {B : ValuationSubring Ω}
    {σ : Ω ≃ₐ[K] Ω} : σ ∈ B.decompositionSubgroup K ↔ ∀ x, σ x ∈ B ↔ x ∈ B := by
  constructor
  · intro h x
    have h' : σ • B = B := h
    have e := ValuationSubring.smul_mem_pointwise_smul_iff (g := σ) (S := B) (x := x)
    rw [h'] at e
    exact e
  · intro h
    show σ • B = B
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← h (σ⁻¹ • x), AlgEquiv.smul_def]
    rw [show σ (σ⁻¹ x) = x from AlgEquiv.apply_symm_apply σ x]

theorem resGal_mem_Dec_iff {σ : G L Ω} :
    resGal F L Ω σ ∈ Dec (F := F) A ↔ σ ∈ Dec (F := L) A := by
  show resGal F L Ω σ ∈ A.decompositionSubgroup F ↔ σ ∈ A.decompositionSubgroup L
  rw [mem_decompositionSubgroup_iff_galois_valuations, mem_decompositionSubgroup_iff_galois_valuations]
  simp only [resGal_apply]


variable (F L) in
def decRes (A : ValuationSubring Ω) : Dec (F := L) A →* Dec (F := F) A :=
  ((resGal F L Ω).comp (Dec (F := L) A).subtype).codRestrict (Dec (F := F) A)
    (fun σ => resGal_mem_Dec_iff.mpr σ.2)

theorem decRes_apply (σ : Dec (F := L) A) : (decRes F L A σ : G F Ω) = resGal F L Ω σ := rfl

theorem decRes_injective : Function.Injective (decRes F L A) := by
  intro σ τ h
  apply Subtype.ext
  apply AlgEquiv.ext
  intro x
  have := congrArg (fun g : Dec (F := F) A => (g : G F Ω) x) h
  simpa [decRes_apply, resGal_apply] using this

theorem decRes_surjective (h : Dec (F := F) A ≤ (resGal F L Ω).range) :
    Function.Surjective (decRes F L A) := by
  intro τ
  obtain ⟨σ, hσ⟩ := MonoidHom.mem_range.mp (h τ.2)
  refine ⟨⟨σ, resGal_mem_Dec_iff.mp (by rw [hσ]; exact τ.2)⟩, ?_⟩
  apply Subtype.ext
  rw [decRes_apply]
  exact hσ

theorem continuous_decRes [IsAlgClosure F Ω] : Continuous (decRes F L A) := by
  refine continuous_induced_rng.2 ?_
  have hc : Continuous (resGal F L Ω) :=
    (isClosedEmbedding_resGal (F := F) (L := L) (Ω := Ω)).continuous
  have e : ((↑) : Dec (F := F) A → G F Ω) ∘ decRes F L A =
      resGal F L Ω ∘ ((↑) : Dec (F := L) A → G L Ω) := by
    funext σ
    exact decRes_apply σ
  rw [e]
  exact hc.comp continuous_subtype_val

def decEquiv [IsAlgClosure F Ω] (h : Dec (F := F) A ≤ (resGal F L Ω).range) :
    Dec (F := L) A ≃ₜ* Dec (F := F) A where
  toMulEquiv := MulEquiv.ofBijective (decRes F L A) ⟨decRes_injective, decRes_surjective h⟩
  continuous_toFun := continuous_decRes
  continuous_invFun := by
    have hI : Topology.IsInducing (resGal F L Ω) :=
      (isClosedEmbedding_resGal (F := F) (L := L) (Ω := Ω)).toIsEmbedding.toIsInducing
    refine continuous_induced_rng.2 (hI.continuous_iff.2 ?_)
    convert (continuous_subtype_val : Continuous (fun τ : Dec (F := F) A => (τ : G F Ω))) using 1
    funext τ
    exact congrArg Subtype.val
      ((MulEquiv.ofBijective (decRes F L A) ⟨decRes_injective, decRes_surjective h⟩).apply_symm_apply τ)

theorem one_lt_normV (v : HeightOneSpectrum (𝓞 F)) : 1 < normV v := by
  have e : normV v = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rfl
  rw [e]
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact v.isPrime.ne_top
  omega

end split

section frob

variable {F L Ω : Type*} [Field F] [NumberField F] [Field L] [NumberField L] [Field Ω] [Algebra F L]
  [Algebra F Ω] [Algebra L Ω] [IsScalarTower F L Ω] {A : ValuationSubring Ω}

end frob

section conj

variable {L Ω : Type*} [Field L] [NumberField L] [Field Ω] [Algebra L Ω]

def conjV (s : L ≃+* L) (w : HeightOneSpectrum (𝓞 L)) : HeightOneSpectrum (𝓞 L) where
  asIdeal := w.asIdeal.comap (RingOfIntegers.mapRingEquiv s.symm : 𝓞 L →+* 𝓞 L)
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
    refine (Submodule.ne_bot_iff _).mpr ⟨RingOfIntegers.mapRingEquiv s y, ?_, ?_⟩
    · rw [Ideal.mem_comap]
      convert hy using 1
      exact RingOfIntegers.ext (by simp)
    · exact (map_ne_zero_iff _ (RingOfIntegers.mapRingEquiv s).injective).mpr hy0

variable (s : L ≃+* L) (τ : Ω ≃+* Ω) (hτ : ∀ x : L, τ (algebraMap L Ω x) = algebraMap L Ω (s x))

end conj

end ReciprocityTheory.Gal
end
end
