module

public import Mathlib

@[expose] public section

section -- merged from GroundTheory.GlobalFields.ComplexMultiplication.EllipticFunctions
open Complex Filter Topology Set

noncomputable section

namespace GroundTheory.Global
namespace Elliptic

variable (L : PeriodPair)

abbrev Torus : Type := ℂ ⧸ L.lattice.toAddSubgroup

abbrev Torus.mk (z : ℂ) : Torus L := QuotientAddGroup.mk z

lemma Torus.mk_eq_mk_iff {z w : ℂ} : Torus.mk L z = Torus.mk L w ↔ z - w ∈ L.lattice := by
  rw [Torus.mk, Torus.mk, QuotientAddGroup.eq_iff_sub_mem]
  rfl

lemma Torus.mk_surjective : Function.Surjective (Torus.mk L) :=
  QuotientAddGroup.mk_surjective

def IsPeriodic {E : Type*} (f : ℂ → E) : Prop :=
  ∀ z : ℂ, ∀ l ∈ L.lattice, f (z + l) = f z

def IsEllipticFunction (f : ℂ → ℂ) : Prop :=
  Meromorphic f ∧ IsPeriodic L f

variable {L}

lemma IsPeriodic.sub {E : Type*} {f : ℂ → E} (hf : IsPeriodic L f) (z : ℂ) {l : ℂ}
    (hl : l ∈ L.lattice) : f (z - l) = f z := by
  simpa using (hf (z - l) l hl).symm

lemma IsPeriodic.comp_add {E : Type*} {f : ℂ → E} (hf : IsPeriodic L f) {l : ℂ}
    (hl : l ∈ L.lattice) : (fun z ↦ f (z + l)) = f :=
  funext fun z ↦ hf z l hl

lemma IsPeriodic.eq_of_mk_eq {E : Type*} {f : ℂ → E} (hf : IsPeriodic L f) {z w : ℂ}
    (h : Torus.mk L z = Torus.mk L w) : f z = f w := by
  have hzw := (Torus.mk_eq_mk_iff L).1 h
  simpa using hf w (z - w) hzw

variable (L)

def fundamentalCompact : Set ℂ := closure (ZSpan.fundamentalDomain L.basis)

lemma isCompact_fundamentalCompact : IsCompact (fundamentalCompact L) :=
  (ZSpan.fundamentalDomain_isBounded L.basis).isCompact_closure

lemma exists_sub_mem_fundamentalCompact (z : ℂ) :
    ∃ l ∈ L.lattice, z - l ∈ fundamentalCompact L := by
  refine ⟨ZSpan.floor L.basis z, ?_, subset_closure ?_⟩
  · rw [L.lattice_eq_span_range_basis]
    exact (ZSpan.floor L.basis z).2
  · rw [← ZSpan.fract_apply]
    exact ZSpan.fract_mem_fundamentalDomain _ _

theorem isCompact_range_of_isPeriodic {E : Type*} [TopologicalSpace E] {f : ℂ → E}
    (hc : Continuous f) (hf : IsPeriodic L f) : IsCompact (range f) :=
  IsZLattice.isCompact_range_of_periodic L.lattice f hc fun z w hw ↦ hf z w hw

theorem eq_of_differentiable_of_isPeriodic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℂ → E} (hd : Differentiable ℂ f) (hf : IsPeriodic L f) (z w : ℂ) : f z = f w :=
  hd.apply_eq_apply_of_bounded (isCompact_range_of_isPeriodic L hd.continuous hf).isBounded z w

variable {L}

lemma IsPeriodic.analyticAt_add_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℂ → E} (hf : IsPeriodic L f) {l : ℂ} (hl : l ∈ L.lattice) (z : ℂ) :
    AnalyticAt ℂ f (z + l) ↔ AnalyticAt ℂ f z := by
  constructor
  · intro h
    have : AnalyticAt ℂ (f ∘ fun w ↦ w + l) z := AnalyticAt.comp (g := f) h (by fun_prop)
    rwa [Function.comp_def, hf.comp_add hl] at this
  · intro h
    have h' : AnalyticAt ℂ f ((z + l) - l) := by simpa using h
    have : AnalyticAt ℂ (f ∘ fun w ↦ w - l) (z + l) := AnalyticAt.comp (g := f) h' (by fun_prop)
    have e : (fun w ↦ f (w - l)) = f := funext fun w ↦ hf.sub w hl
    rwa [Function.comp_def, e] at this

lemma IsPeriodic.meromorphicOrderAt_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℂ → E} (hf : IsPeriodic L f) {l : ℂ} (hl : l ∈ L.lattice) (z : ℂ) :
    meromorphicOrderAt f (z + l) = meromorphicOrderAt f z := by
  have := meromorphicOrderAt_fun_comp_add_const_eq_meromorphicOrderAt (f := f) (x := z) (c := l)
  rw [hf.comp_add hl] at this
  exact this.symm

def singularSet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (f : ℂ → E) : Set ℂ :=
  {z | ¬ AnalyticAt ℂ f z}

theorem finite_inter_singularSet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {f : ℂ → E} (hf : Meromorphic f) {K : Set ℂ} (hK : IsCompact K) :
    (K ∩ singularSet f).Finite := by
  have h := hK.finite_sdiff_of_mem_codiscreteWithin
    ((hf.meromorphicOn (s := K)).analyticAt_mem_codiscreteWithin)
  exact h.subset fun z hz ↦ ⟨hz.1, hz.2⟩

variable (L)

theorem finite_image_singularSet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {f : ℂ → E} (hf : Meromorphic f) (hp : IsPeriodic L f) :
    (Torus.mk L '' singularSet f).Finite := by
  refine ((finite_inter_singularSet hf (isCompact_fundamentalCompact L)).image
    (Torus.mk L)).subset ?_
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨l, hl, hzl⟩ := exists_sub_mem_fundamentalCompact L z
  refine ⟨z - l, ⟨hzl, fun h ↦ hz ?_⟩, ?_⟩
  · have := (hp.analyticAt_add_iff hl (z - l)).2 h
    simpa using this
  · exact (Torus.mk_eq_mk_iff L).2 (by simpa using L.lattice.neg_mem hl)

end Elliptic
end GroundTheory.Global
end
end

section -- merged from GroundTheory.GlobalFields.ComplexMultiplication.VariableChangePoints
namespace GroundTheory.Global

open WeierstrassCurve

variable {F : Type*} [Field F]

section VariableChangePoint

theorem nonsingular_variableChange (C : VariableChange F) (W : WeierstrassCurve F) {x y : F}
    (h : W.toAffine.Nonsingular x y) :
    (C • W).toAffine.Nonsingular (↑C.u⁻¹ ^ 2 * (x - C.r))
      (↑C.u⁻¹ ^ 3 * (y - C.s * (x - C.r) - C.t)) := by
  rw [Affine.nonsingular_iff'] at h ⊢
  obtain ⟨he, hd⟩ := h
  rw [Affine.equation_iff'] at he ⊢
  have hv : (↑C.u⁻¹ : F) ≠ 0 := Units.ne_zero _
  simp only [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
    variableChange_a₆]
  set v : F := ↑C.u⁻¹
  refine ⟨?_, ?_⟩
  · linear_combination v ^ 6 * he
  · by_contra hc
    push Not at hc
    obtain ⟨h1, h2⟩ := hc
    have hY : 2 * y + W.a₁ * x + W.a₃ = 0 := by
      have : v ^ 3 * (2 * y + W.a₁ * x + W.a₃) = 0 := by linear_combination h2
      simpa [hv] using this
    have hX : W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) = 0 := by
      have : v ^ 4 * (W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄)) = 0 := by
        linear_combination h1 - v ^ 4 * C.s * hY
      simpa [hv] using this
    rcases hd with hd | hd
    · exact hd hX
    · exact hd hY

def variableChangePoint (C : VariableChange F) {W W' : WeierstrassCurve F} (hC : C • W = W') :
    W.toAffine.Point → W'.toAffine.Point
  | .zero => .zero
  | .some x y h => .some (↑C.u⁻¹ ^ 2 * (x - C.r)) (↑C.u⁻¹ ^ 3 * (y - C.s * (x - C.r) - C.t))
      (by subst hC; exact nonsingular_variableChange C W h)

theorem variableChangePoint_some (C : VariableChange F) {W W' : WeierstrassCurve F}
    (hC : C • W = W') {x y : F} (h : W.toAffine.Nonsingular x y) :
    variableChangePoint C hC (.some x y h) =
      .some (↑C.u⁻¹ ^ 2 * (x - C.r)) (↑C.u⁻¹ ^ 3 * (y - C.s * (x - C.r) - C.t))
        (by subst hC; exact nonsingular_variableChange C W h) := rfl

end VariableChangePoint

end GroundTheory.Global
end

section -- merged from GroundTheory.GlobalFields.ComplexMultiplication.ExistsRingEquivExtendOfIsTranscendenceBasis
namespace GroundTheory.Global

open Cardinal Polynomial IntermediateField

section General

variable {Ω : Type*} [Field Ω] [IsAlgClosed Ω]

theorem exists_ringEquiv_extend_of_isTranscendenceBasis
    {F₁ F₂ : Type*} [Field F₁] [Field F₂] [Algebra F₁ Ω] [Algebra F₂ Ω]
    (e : F₁ ≃+* F₂) {ι κ : Type*} {v₁ : ι → Ω} {v₂ : κ → Ω}
    (h₁ : IsTranscendenceBasis F₁ v₁) (h₂ : IsTranscendenceBasis F₂ v₂) (φ : ι ≃ κ) :
    ∃ σ : Ω ≃+* Ω, (∀ a : F₁, σ (algebraMap F₁ Ω a) = algebraMap F₂ Ω (e a)) ∧
      ∀ i, σ (v₁ i) = v₂ (φ i) := by
  have := IsAlgClosed.isAlgClosure_of_transcendence_basis v₁ h₁
  have := IsAlgClosed.isAlgClosure_of_transcendence_basis v₂ h₂
  let e' : Algebra.adjoin F₁ (Set.range v₁) ≃+* Algebra.adjoin F₂ (Set.range v₂) :=
    h₁.1.aevalEquiv.symm.toRingEquiv.trans <| (MvPolynomial.mapEquiv ι e).trans <|
      (MvPolynomial.renameEquiv F₂ φ).toRingEquiv.trans h₂.1.aevalEquiv.toRingEquiv
  have key : ∀ p : MvPolynomial ι F₁,
      IsAlgClosure.equivOfEquiv Ω Ω e' (MvPolynomial.aeval v₁ p) =
        MvPolynomial.aeval v₂ (MvPolynomial.rename φ (MvPolynomial.map (e : F₁ →+* F₂) p)) := by
    intro p
    rw [← h₁.1.algebraMap_aevalEquiv, IsAlgClosure.equivOfEquiv_algebraMap,
      ← h₂.1.algebraMap_aevalEquiv]
    congr 1
    simp [e']
  refine ⟨IsAlgClosure.equivOfEquiv Ω Ω e', fun a => ?_, fun i => ?_⟩
  · simpa using key (MvPolynomial.C a)
  · simpa using key (MvPolynomial.X i)

theorem exists_ringEquiv_extend_of_trdeg_eq
    {F₁ F₂ : Type*} [Field F₁] [Field F₂] [Algebra F₁ Ω] [Algebra F₂ Ω]
    (e : F₁ ≃+* F₂) (h : Algebra.trdeg F₁ Ω = Algebra.trdeg F₂ Ω) :
    ∃ σ : Ω ≃+* Ω, ∀ a : F₁, σ (algebraMap F₁ Ω a) = algebraMap F₂ Ω (e a) := by
  obtain ⟨s₁, hs₁⟩ := exists_isTranscendenceBasis F₁ Ω
  obtain ⟨s₂, hs₂⟩ := exists_isTranscendenceBasis F₂ Ω
  obtain ⟨φ⟩ := Cardinal.eq.1 (hs₁.cardinalMk_eq_trdeg.trans (h.trans hs₂.cardinalMk_eq_trdeg.symm))
  obtain ⟨σ, hσ, -⟩ := exists_ringEquiv_extend_of_isTranscendenceBasis e hs₁ hs₂ φ
  exact ⟨σ, hσ⟩

theorem trdeg_eq_cardinalMk_of_countable (F : Type*) [Field F] [Algebra F Ω] [Countable F]
    (hΩ : ℵ₀ < #Ω) : Algebra.trdeg F Ω = #Ω := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis F Ω
  rw [← hs.cardinalMk_eq_trdeg]
  simpa using (IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt _ hs
    Cardinal.mk_le_aleph0 hΩ).symm

end General

end GroundTheory.Global
end

section -- merged from GroundTheory.GlobalFields.ComplexMultiplication.PrimeLocalization
namespace GroundTheory.Global

open NumberField IsDedekindDomain Polynomial

noncomputable section

variable (L : Type*) [Field L] [NumberField L]

def localizationAt (v : HeightOneSpectrum (𝓞 L)) : Subalgebra (𝓞 L) L :=
  Localization.subalgebra.ofField L v.asIdeal.primeCompl v.asIdeal.primeCompl_le_nonZeroDivisors

variable {L}

instance (v : HeightOneSpectrum (𝓞 L)) : IsLocalization.AtPrime (localizationAt L v) v.asIdeal :=
  Localization.subalgebra.isLocalization_ofField _ _ _

instance (v : HeightOneSpectrum (𝓞 L)) : IsDiscreteValuationRing (localizationAt L v) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 L) v.ne_bot _

theorem mem_localizationAt_iff {v : HeightOneSpectrum (𝓞 L)} {x : L} :
    x ∈ localizationAt L v ↔ ∃ a s : 𝓞 L, s ∉ v.asIdeal ∧
      x = algebraMap (𝓞 L) L a * (algebraMap (𝓞 L) L s)⁻¹ := by
  unfold localizationAt Localization.subalgebra.ofField
  rw [← SetLike.mem_coe, Subalgebra.coe_copy]
  simp only [Set.mem_ofPred_eq, Ideal.primeCompl, Submonoid.mem_mk, Subsemigroup.mem_mk,
    Set.mem_compl_iff, SetLike.mem_coe, exists_prop]

theorem finite_setOf_mem_asIdeal {b : 𝓞 L} (hb : b ≠ 0) :
    {v : HeightOneSpectrum (𝓞 L) | b ∈ v.asIdeal}.Finite :=
  (Ideal.finite_factors (I := Ideal.span {b}) (by rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot])).subset
    fun _ hv => Ideal.dvd_span_singleton.mpr hv

theorem eventually_mem_localizationAt (x : L) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 L) in Filter.cofinite, x ∈ localizationAt L v := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 L) x
  refine Filter.eventually_cofinite.mpr
    ((finite_setOf_mem_asIdeal (nonZeroDivisors.ne_zero hb)).subset fun v hv => ?_)
  by_contra h
  exact hv (mem_localizationAt_iff.mpr ⟨a, b, h, div_eq_mul_inv _ _⟩)


omit [NumberField L] in
theorem isUnit_of_mem_of_inv_mem {R : Type*} [CommRing R] [Algebra R L] {S : Subalgebra R L}
    {x : L} (hx : x ≠ 0) (h : x ∈ S) (h' : x⁻¹ ∈ S) : IsUnit (⟨x, h⟩ : S) :=
  isUnit_iff_exists_inv.mpr ⟨⟨x⁻¹, h'⟩, Subtype.ext (mul_inv_cancel₀ hx)⟩

theorem eventually_isUnit_localizationAt {x : L} (hx : x ≠ 0) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 L) in Filter.cofinite,
      ∃ h : x ∈ localizationAt L v, IsUnit (⟨x, h⟩ : localizationAt L v) := by
  filter_upwards [eventually_mem_localizationAt x, eventually_mem_localizationAt x⁻¹] with v h h'
  exact ⟨h, isUnit_of_mem_of_inv_mem hx h h'⟩

end

end GroundTheory.Global
end
