module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.MulConjTransposeEqOneOfOrthonormal
open Matrix

namespace GlobalTheory

section Ring

variable {R : Type*} [CommRing R]

abbrev subsetEnum {n : Type*} [LinearOrder n] {i : ℕ} (S : Set.powersetCard n i) : Fin i → n :=
  S.1.orderEmbOfFin S.2

theorem range_subsetEnum {n : Type*} [LinearOrder n] {i : ℕ} (S : Set.powersetCard n i) :
    Set.range (subsetEnum S) = (S.1 : Set n) :=
  Finset.range_orderEmbOfFin _ _

theorem subsetEnum_injective {n : Type*} [LinearOrder n] {i : ℕ} (S : Set.powersetCard n i) :
    Function.Injective (subsetEnum S) :=
  (S.1.orderEmbOfFin S.2).injective

theorem alternatingMap_apply_eq_sum_minors {n : Type*} [Fintype n] [LinearOrder n] {i : ℕ}
    {M : Type*} [AddCommGroup M] [Module R M] (f : (n → R) [⋀^Fin i]→ₗ[R] M)
    (A : Fin i → n → R) :
    f A = ∑ S : Set.powersetCard n i,
      ((Matrix.of A).submatrix id (subsetEnum S)).det • f (fun a => Pi.single (subsetEnum S a) 1) := by
  classical
  let b := Pi.basisFun R n
  have h := (b.exteriorPower i).sum_repr (exteriorPower.ιMulti R i A)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← exteriorPower.alternatingMapLinearEquiv_apply_ιMulti f A, ← h, map_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [map_smul, exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti,
    exteriorPower.basis_apply, exteriorPower.ιMulti_family,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  congr 2
  ext a
  simp [b, subsetEnum, Set.powersetCard.ofFinEmbEquiv_symm_apply, Pi.basisFun_apply]

theorem det_mul_eq_sum_minors {n : Type*} [Fintype n] [LinearOrder n] {i : ℕ}
    (A : Matrix (Fin i) n R) (B : Matrix n (Fin i) R) :
    (A * B).det = ∑ S : Set.powersetCard n i,
      (A.submatrix id (subsetEnum S)).det * (B.submatrix (subsetEnum S) id).det := by
  classical
  have h := alternatingMap_apply_eq_sum_minors
    ((Matrix.detRowAlternating (n := Fin i) (R := R)).compLinearMap B.vecMulLinear) A
  have h0 : (A * B).det =
      ((Matrix.detRowAlternating (n := Fin i) (R := R)).compLinearMap B.vecMulLinear) A := rfl
  rw [h0, h]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [smul_eq_mul]
  congr 1
  rw [AlternatingMap.compLinearMap_apply]
  change Matrix.det _ = _
  congr 1
  ext a c
  simp [Matrix.vecMulLinear_apply, Matrix.single_one_vecMul]

theorem det_mul_det_eq_of_range_eq {m k n : Type*} [Fintype m] [DecidableEq m] [Fintype k]
    [DecidableEq k] (A : Matrix m n R) (B : Matrix n m R) (φ : k ≃ m) (e : m → n) (g : k → n)
    (hg : Function.Injective g) (h : Set.range e = Set.range g) :
    (A.submatrix id e).det * (B.submatrix e id).det =
      (A.submatrix φ g).det * (B.submatrix g φ).det := by
  have h1 : ∀ a : k, ∃ c : m, e c = g a := fun a => by
    have : g a ∈ Set.range e := h ▸ Set.mem_range_self a
    exact this
  choose s hs using h1
  have hinj : Function.Injective (φ.symm ∘ s) := by
    intro a a' haa
    have : s a = s a' := φ.symm.injective haa
    exact hg (by rw [← hs a, ← hs a', this])
  let σ : Equiv.Perm k := Equiv.ofBijective _ (Finite.injective_iff_bijective.mp hinj)
  have hσ : ∀ a, e (φ (σ a)) = g a := fun a => by simp [σ, hs]
  have hA : A.submatrix φ g = ((A.submatrix id e).submatrix φ φ).submatrix id σ := by
    ext a c; simp [hσ]
  have hB : B.submatrix g φ = ((B.submatrix e id).submatrix φ φ).submatrix σ id := by
    ext a c; simp [hσ]
  rw [hA, hB, det_permute, det_permute', det_submatrix_equiv_self, det_submatrix_equiv_self]
  have : ((Equiv.Perm.sign σ : ℤ) : R) * ((Equiv.Perm.sign σ : ℤ) : R) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]; simp
  linear_combination (-(A.submatrix id e).det * (B.submatrix e id).det) * this

theorem det_mul_eq_sum_minors_of_enum {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n]
    (e : Set.powersetCard n (Fintype.card m) → m → n)
    (he : ∀ S, Set.range (e S) = (S.1 : Set n)) (A : Matrix m n R) (B : Matrix n m R) :
    (A * B).det = ∑ S : Set.powersetCard n (Fintype.card m),
      (A.submatrix id (e S)).det * (B.submatrix (e S) id).det := by
  classical
  letI : LinearOrder n := linearOrderOfSTO WellOrderingRel
  let φ : Fin (Fintype.card m) ≃ m := (Fintype.equivFin m).symm
  rw [← det_submatrix_equiv_self φ (A * B), submatrix_mul A B φ id φ Function.bijective_id,
    det_mul_eq_sum_minors]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [det_mul_det_eq_of_range_eq A B φ (e S) (subsetEnum S) (subsetEnum_injective S)
    ((he S).trans (range_subsetEnum S).symm)]
  rfl

theorem det_submatrix_mul_eq_sum_minors {l n o : Type*} [Fintype n] [LinearOrder n] {i : ℕ}
    (A : Matrix l n R) (B : Matrix n o R) (r : Fin i → l) (c : Fin i → o) :
    ((A * B).submatrix r c).det = ∑ S : Set.powersetCard n i,
      (A.submatrix r (subsetEnum S)).det * (B.submatrix (subsetEnum S) c).det := by
  rw [submatrix_mul A B r id c Function.bijective_id, det_mul_eq_sum_minors]
  rfl

theorem det_mul_diagonal_mul_eq_sum_minors {n : Type*} [Fintype n] [LinearOrder n] {i : ℕ}
    (A : Matrix (Fin i) n R) (d : n → R) (B : Matrix n (Fin i) R) :
    (A * diagonal d * B).det = ∑ S : Set.powersetCard n i,
      (∏ s ∈ S.1, d s) *
        ((A.submatrix id (subsetEnum S)).det * (B.submatrix (subsetEnum S) id).det) := by
  rw [det_mul_eq_sum_minors]
  refine Finset.sum_congr rfl fun S _ => ?_
  have h1 : (A * diagonal d).submatrix id (subsetEnum S) =
      A.submatrix id (subsetEnum S) * diagonal (d ∘ subsetEnum S) := by
    ext a c; simp
  have h2 : ∏ a, d (subsetEnum S a) = ∏ s ∈ S.1, d s := by
    refine Finset.prod_bij (fun a _ => subsetEnum S a) (fun a _ => Finset.orderEmbOfFin_mem _ _ _)
      (fun a _ b _ h => subsetEnum_injective S h) (fun s hs => ?_) (fun _ _ => rfl)
    have : s ∈ Set.range (subsetEnum S) := by rw [range_subsetEnum]; exact hs
    obtain ⟨a, ha⟩ := this
    exact ⟨a, Finset.mem_univ _, ha⟩
  rw [h1, det_mul, det_diagonal, ← h2]
  simp only [Function.comp_apply]
  ring

end Ring

section Normed

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [LinearOrder n] {i : ℕ}

theorem det_mul_conjTranspose_eq_sum_norm_sq (A : Matrix (Fin i) n 𝕜) :
    (A * Aᴴ).det =
      ((∑ S : Set.powersetCard n i, ‖(A.submatrix id (subsetEnum S)).det‖ ^ 2 : ℝ) : 𝕜) := by
  rw [det_mul_eq_sum_minors]
  push_cast
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [← conjTranspose_submatrix, det_conjTranspose, RCLike.star_def, RCLike.mul_conj]

theorem sum_norm_sq_minors_eq_one (A : Matrix (Fin i) n 𝕜) (hA : A * Aᴴ = 1) :
    ∑ S : Set.powersetCard n i, ‖(A.submatrix id (subsetEnum S)).det‖ ^ 2 = 1 := by
  have h := det_mul_conjTranspose_eq_sum_norm_sq A
  rw [hA, det_one] at h
  exact_mod_cast h.symm

theorem two_rpow_neg_half_le_choose_rpow {i N r : ℕ} (hi : i ≤ N) (hr : N ≤ r) :
    (2 : ℝ) ^ (-(r : ℝ) / 2) ≤ (N.choose i : ℝ) ^ (-(1 : ℝ) / 2) := by
  have hpos : (0 : ℝ) < N.choose i := by exact_mod_cast Nat.choose_pos hi
  have hle : (N.choose i : ℝ) ≤ (2 : ℝ) ^ (r : ℝ) := by
    rw [Real.rpow_natCast]
    exact_mod_cast (Nat.choose_le_two_pow N i).trans (Nat.pow_le_pow_right two_pos hr)
  calc (2 : ℝ) ^ (-(r : ℝ) / 2) = ((2 : ℝ) ^ (r : ℝ)) ^ (-(1 : ℝ) / 2) := by
        rw [← Real.rpow_mul zero_le_two]; congr 1; ring
    _ ≤ _ := Real.rpow_le_rpow_of_nonpos hpos hle (by norm_num)

theorem exists_choose_rpow_le_norm_minor (A : Matrix (Fin i) n 𝕜) (hA : A * Aᴴ = 1) :
    i ≤ Fintype.card n ∧ ∃ S : Set.powersetCard n i,
      ((Fintype.card n).choose i : ℝ) ^ (-(1 : ℝ) / 2) ≤
        ‖(A.submatrix id (subsetEnum S)).det‖ := by
  have h := sum_norm_sq_minors_eq_one A hA
  have hne : (Finset.univ : Finset (Set.powersetCard n i)).Nonempty := by
    rcases (Finset.univ : Finset (Set.powersetCard n i)).eq_empty_or_nonempty with h0 | h0
    · rw [h0] at h; simp at h
    · exact h0
  have hi : i ≤ Fintype.card n := by
    obtain ⟨S, -⟩ := hne
    exact S.2 ▸ Finset.card_le_univ S.1
  have hcard : Fintype.card (Set.powersetCard n i) = (Fintype.card n).choose i := by
    rw [Fintype.card_eq_nat_card, Set.powersetCard.card, Nat.card_eq_fintype_card]
  have hpos : (0 : ℝ) < (Fintype.card n).choose i := by exact_mod_cast Nat.choose_pos hi
  refine ⟨hi, ?_⟩
  obtain ⟨S, -, hS⟩ := Finset.exists_le_of_sum_le hne
    (f := fun _ => (((Fintype.card n).choose i : ℝ))⁻¹)
    (g := fun S => ‖(A.submatrix id (subsetEnum S)).det‖ ^ 2) (by
      rw [h, Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul, mul_inv_cancel₀ hpos.ne'])
  refine ⟨S, (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).mp ?_⟩
  refine le_of_eq_of_le ?_ hS
  rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le, ← Real.rpow_neg_one]
  norm_num

theorem exists_two_rpow_le_norm_minor (A : Matrix (Fin i) n 𝕜) (hA : A * Aᴴ = 1) {r : ℕ}
    (hr : Fintype.card n ≤ r) :
    ∃ S : Set.powersetCard n i,
      (2 : ℝ) ^ (-(r : ℝ) / 2) ≤ ‖(A.submatrix id (subsetEnum S)).det‖ := by
  obtain ⟨hi, S, hS⟩ := exists_choose_rpow_le_norm_minor A hA
  exact ⟨S, (two_rpow_neg_half_le_choose_rpow hi hr).trans hS⟩

end Normed

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegrableMonomialMulConjComplexGaussian
open MeasureTheory Set Real
open scoped Nat ComplexConjugate

namespace GlobalTheory

section General

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

noncomputable def complexGaussian (g : ℕ) : Measure E :=
  volume.withDensity fun z => ENNReal.ofReal ((π ^ g)⁻¹ * exp (-‖z‖ ^ 2))

variable {E}

theorem integrable_exp_neg_mul_norm_sq {b : ℝ} (hb : 0 < b) :
    Integrable fun z : E => exp (-b * ‖z‖ ^ 2) := by
  by_contra h
  have h1 := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := E) hb
  rw [integral_undef h] at h1
  exact absurd h1 (by positivity)

theorem integral_exp_neg_mul_norm_sq {g : ℕ} (hE : Module.finrank ℝ E = 2 * g) {b : ℝ}
    (hb : 0 < b) : ∫ z : E, exp (-b * ‖z‖ ^ 2) = (π / b) ^ g := by
  rw [GaussianFourier.integral_rexp_neg_mul_sq_norm hb, hE, ← rpow_natCast]
  congr 1
  push_cast
  ring

theorem isProbabilityMeasure_complexGaussian {g : ℕ} (hE : Module.finrank ℝ E = 2 * g) :
    IsProbabilityMeasure (complexGaussian E g) := by
  constructor
  have h := integral_exp_neg_mul_norm_sq hE one_pos
  have hi := integrable_exp_neg_mul_norm_sq (E := E) one_pos
  simp only [neg_mul, one_mul, div_one] at h hi
  rw [complexGaussian, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (hi.const_mul _) (.of_forall fun z => by positivity),
    integral_const_mul, h, inv_mul_cancel₀ (by positivity), ENNReal.ofReal_one]

theorem integrable_norm_pow_mul_exp_neg_mul_norm_sq (n : ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable fun z : E => ‖z‖ ^ n * exp (-b * ‖z‖ ^ 2) := by
  rcases subsingleton_or_nontrivial E with h | h
  · exact Integrable.of_finite
  rw [integrable_fun_norm_addHaar volume (f := fun r => r ^ n * exp (-b * r ^ 2))]
  have := integrableOn_rpow_mul_exp_neg_mul_sq hb
    (s := ((Module.finrank ℝ E - 1 + n : ℕ) : ℝ)) (lt_of_lt_of_le neg_one_lt_zero (by positivity))
  refine this.congr_fun (fun x _ => ?_) measurableSet_Ioi
  simp only [rpow_natCast, smul_eq_mul, pow_add, mul_assoc]

end General

section Combinatorics

end Combinatorics

section Kernel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

end Kernel

section Monomials

theorem finrank_real_euclideanSpace_complex (ι : Type*) [Fintype ι] :
    Module.finrank ℝ (EuclideanSpace ℂ ι) = 2 * Fintype.card ι := by
  rw [finrank_real_of_complex, finrank_euclideanSpace]

theorem volume_preserving_ofLp_complex (ι : Type*) [Fintype ι] :
    MeasurePreserving (@WithLp.ofLp 2 (ι → ℂ)) := by
  let e : EuclideanSpace ℂ ι ≃L[ℝ] (ι → ℂ) := PiLp.continuousLinearEquiv 2 ℝ fun _ : ι => ℂ
  change MeasurePreserving e
  refine ⟨e.continuous.measurable, ?_⟩
  obtain ⟨c, hc⟩ : ∃ c : NNReal, Measure.map e volume = c • (volume : Measure (ι → ℂ)) :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩
  have h1 : ∫ w : ι → ℂ, ∏ i, exp (-1 * ‖w i‖ ^ 2) = π ^ Fintype.card ι := by
    rw [integral_fintype_prod_volume_eq_pow fun w : ℂ => exp (-1 * ‖w‖ ^ 2),
      integral_exp_neg_mul_norm_sq (E := ℂ) (g := 1) (by simp) one_pos]
    simp
  have h2 : ∫ w : ι → ℂ, ∏ i, exp (-1 * ‖w i‖ ^ 2) ∂(Measure.map e volume) =
      π ^ Fintype.card ι := by
    rw [integral_map e.continuous.measurable.aemeasurable
      (Continuous.aestronglyMeasurable (by fun_prop))]
    have := integral_exp_neg_mul_norm_sq (finrank_real_euclideanSpace_complex ι) one_pos
    rw [div_one] at this
    rw [← this]
    refine integral_congr_ae (.of_forall fun z => ?_)
    simp only
    rw [← exp_sum, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
    rfl
  rw [hc, integral_smul_nnreal_measure, h1, NNReal.smul_def, smul_eq_mul,
    mul_eq_right₀ (by positivity)] at h2
  rw [hc, show c = 1 by exact_mod_cast h2, one_smul]

end Monomials

section Fin

end Fin

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FderivIntegralApplyOfHolomorphicOfDominated
open MeasureTheory Filter Metric Set
open scoped Topology Interval

namespace GlobalTheory

variable {T : Type*} [MeasurableSpace T] {μ : Measure T}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem aestronglyMeasurable_fderiv_apply_of_param {F : T → E → V} {x₀ : E}
    (hmeas : ∀ᶠ y in 𝓝 x₀, AEStronglyMeasurable (fun t => F t y) μ)
    (hdiff : ∀ᵐ t ∂μ, DifferentiableAt ℂ (F t) x₀) (v : E) :
    AEStronglyMeasurable (fun t => fderiv ℂ (F t) x₀ v) μ := by
  classical
  let f : ℂ → T → V := fun c t =>
    if AEStronglyMeasurable (fun t => F t (x₀ + c • v)) μ then
      c⁻¹ • (F t (x₀ + c • v) - F t x₀) else 0
  have h0 : AEStronglyMeasurable (fun t => F t x₀) μ := hmeas.self_of_nhds
  have hev : ∀ᶠ c : ℂ in 𝓝[≠] 0, AEStronglyMeasurable (fun t => F t (x₀ + c • v)) μ := by
    have hc : Tendsto (fun c : ℂ => x₀ + c • v) (𝓝 0) (𝓝 x₀) := by
      have : Continuous (fun c : ℂ => x₀ + c • v) := by fun_prop
      simpa using this.tendsto 0
    exact (hc.eventually hmeas).filter_mono nhdsWithin_le_nhds
  refine aestronglyMeasurable_of_tendsto_ae (𝓝[≠] (0 : ℂ)) (f := f) (fun c => ?_) ?_
  · by_cases h : AEStronglyMeasurable (fun t => F t (x₀ + c • v)) μ
    · simp only [f, if_pos h]
      exact (h.sub h0).const_smul c⁻¹
    · simp only [f, if_neg h]
      exact aestronglyMeasurable_const
  · filter_upwards [hdiff] with t ht
    have h1 := hasLineDerivAt_iff_tendsto_slope_zero.1 (ht.hasFDerivAt.hasLineDerivAt v)
    refine h1.congr' ?_
    filter_upwards [hev] with c hc
    simp only [f, if_pos hc]

variable [FiniteDimensional ℂ E]

theorem aestronglyMeasurable_fderiv_of_param {F : T → E → V} {x₀ : E}
    (hmeas : ∀ᶠ y in 𝓝 x₀, AEStronglyMeasurable (fun t => F t y) μ)
    (hdiff : ∀ᵐ t ∂μ, DifferentiableAt ℂ (F t) x₀) :
    AEStronglyMeasurable (fun t => fderiv ℂ (F t) x₀) μ := by
  let b := Module.finBasis ℂ E
  have key : (fun t => fderiv ℂ (F t) x₀) = fun t =>
      ∑ i, ContinuousLinearMap.smulRightL ℂ E V
        (LinearMap.toContinuousLinearMap (b.coord i)) (fderiv ℂ (F t) x₀ (b i)) := by
    funext t
    ext v
    have h : fderiv ℂ (F t) x₀ v = ∑ i, (b.repr v) i • fderiv ℂ (F t) x₀ (b i) := by
      conv_lhs => rw [← b.sum_repr v]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul]
    simpa using h
  rw [key]
  refine Finset.aestronglyMeasurable_fun_sum _ fun i _ => ?_
  exact (ContinuousLinearMap.smulRightL ℂ E V
    (LinearMap.toContinuousLinearMap (b.coord i))).continuous.comp_aestronglyMeasurable
      (aestronglyMeasurable_fderiv_apply_of_param hmeas hdiff (b i))

set_option linter.unusedSectionVars false

variable [CompleteSpace V]

theorem hasFDerivAt_integral_of_holomorphic_of_dominated {F : T → E → V} {x₀ : E} {s : Set E}
    {bound : T → ℝ} (hs : s ∈ 𝓝 x₀)
    (hmeas : ∀ y ∈ s, AEStronglyMeasurable (fun t => F t y) μ)
    (hdiff : ∀ᵐ t ∂μ, DifferentiableOn ℂ (F t) s)
    (hbound : ∀ᵐ t ∂μ, ∀ y ∈ s, ‖F t y‖ ≤ bound t) (hint : Integrable bound μ) :
    Integrable (fun t => F t x₀) μ ∧ Integrable (fun t => fderiv ℂ (F t) x₀) μ ∧
      HasFDerivAt (fun y => ∫ t, F t y ∂μ) (∫ t, fderiv ℂ (F t) x₀ ∂μ) x₀ := by
  obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.1 hs
  have hx₀ : x₀ ∈ s := mem_of_mem_nhds hs
  have hat : ∀ᵐ t ∂μ, DifferentiableAt ℂ (F t) x₀ := hdiff.mono fun t ht => ht.differentiableAt hs
  have hF₀ : Integrable (fun t => F t x₀) μ :=
    hint.mono' (hmeas x₀ hx₀) (hbound.mono fun t ht => ht x₀ hx₀)
  refine ⟨hF₀, ?_⟩
  refine hasFDerivAt_integral_of_dominated_loc_of_lip' (𝕜 := ℂ) (F := fun y t => F t y)
    (F' := fun t => fderiv ℂ (F t) x₀) (bound := fun t => 2 * bound t / r)
    (ball_mem_nhds x₀ hr) (fun y hy => hmeas y (hrs hy)) hF₀
    (aestronglyMeasurable_fderiv_of_param (Filter.mem_of_superset hs hmeas) hat) ?_
    ((hint.const_mul 2).div_const r) (hat.mono fun t ht => ht.hasFDerivAt)
  filter_upwards [hdiff, hbound] with t ht hb y hy
  have hmaps : MapsTo (F t) (ball x₀ r) (closedBall (F t x₀) (2 * bound t)) := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm]
    have h1 := hb z (hrs hz)
    have h2 := hb x₀ hx₀
    linarith [norm_sub_le (F t z) (F t x₀)]
  simpa [dist_eq_norm] using
    Complex.dist_le_div_mul_dist_of_mapsTo_ball (ht.mono hrs) hmaps hy

theorem differentiableOn_integral_of_holomorphic_of_locally_dominated {F : T → E → V}
    {U : Set E} (hU : IsOpen U)
    (hmeas : ∀ y ∈ U, AEStronglyMeasurable (fun t => F t y) μ)
    (hdiff : ∀ᵐ t ∂μ, DifferentiableOn ℂ (F t) U)
    (hdom : ∀ x ∈ U, ∃ s ∈ 𝓝 x, ∃ bound : T → ℝ, Integrable bound μ ∧
      ∀ᵐ t ∂μ, ∀ y ∈ s, ‖F t y‖ ≤ bound t) :
    DifferentiableOn ℂ (fun y => ∫ t, F t y ∂μ) U ∧
      ∀ x ∈ U, Integrable (fun t => F t x) μ ∧ Integrable (fun t => fderiv ℂ (F t) x) μ ∧
        HasFDerivAt (fun y => ∫ t, F t y ∂μ) (∫ t, fderiv ℂ (F t) x ∂μ) x := by
  have key : ∀ x ∈ U, Integrable (fun t => F t x) μ ∧ Integrable (fun t => fderiv ℂ (F t) x) μ ∧
      HasFDerivAt (fun y => ∫ t, F t y ∂μ) (∫ t, fderiv ℂ (F t) x ∂μ) x := by
    intro x hx
    obtain ⟨s, hs, bound, hint, hb⟩ := hdom x hx
    exact hasFDerivAt_integral_of_holomorphic_of_dominated (s := s ∩ U)
      (inter_mem hs (hU.mem_nhds hx)) (fun y hy => hmeas y hy.2)
      (hdiff.mono fun t ht => ht.mono inter_subset_right)
      (hb.mono fun t ht y hy => ht y hy.1) hint
  exact ⟨fun x hx => (key x hx).2.2.differentiableAt.differentiableWithinAt, key⟩

theorem differentiableOn_setIntegral_of_holomorphic_of_continuousOn [TopologicalSpace T]
    [OpensMeasurableSpace T] {F : T → E → V} {U : Set E} (hU : IsOpen U) {S K : Set T}
    (hK : IsCompact K) (hSK : S ⊆ K) (hS : MeasurableSet S) (hfin : μ S ≠ ⊤)
    (hcont : ContinuousOn (Function.uncurry F) (K ×ˢ U))
    (hdiff : ∀ t ∈ S, DifferentiableOn ℂ (F t) U) :
    DifferentiableOn ℂ (fun y => ∫ t in S, F t y ∂μ) U ∧
      ∀ x ∈ U, IntegrableOn (fun t => F t x) S μ ∧
        IntegrableOn (fun t => fderiv ℂ (F t) x) S μ ∧
        HasFDerivAt (fun y => ∫ t in S, F t y ∂μ) (∫ t in S, fderiv ℂ (F t) x ∂μ) x := by
  have : ProperSpace E := FiniteDimensional.proper ℂ E
  have : IsFiniteMeasure (μ.restrict S) := ⟨by simpa using hfin.lt_top⟩
  refine differentiableOn_integral_of_holomorphic_of_locally_dominated (μ := μ.restrict S) hU
    (fun y hy => ?_) (ae_restrict_of_forall_mem hS hdiff) (fun x hx => ?_)
  · have : ContinuousOn (fun t => F t y) K :=
      hcont.comp (f := fun t => (t, y)) (by fun_prop) fun t ht => ⟨ht, hy⟩
    exact this.aestronglyMeasurable_of_subset_isCompact hK hS hSK
  · obtain ⟨r, hr, hrU⟩ := nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds hx)
    obtain ⟨C, hC⟩ := (hK.prod (isCompact_closedBall x r)).exists_bound_of_continuousOn
      (hcont.mono (prod_mono subset_rfl hrU))
    refine ⟨closedBall x r, closedBall_mem_nhds x hr, fun _ => C, integrable_const C, ?_⟩
    exact ae_restrict_of_forall_mem hS fun t ht y hy => hC (t, y) ⟨hSK ht, hy⟩

theorem differentiableOn_integral_of_holomorphic_of_continuousOn [TopologicalSpace T]
    [OpensMeasurableSpace T] [CompactSpace T] [IsFiniteMeasure μ] {F : T → E → V} {U : Set E}
    (hU : IsOpen U) (hcont : ContinuousOn (Function.uncurry F) (univ ×ˢ U))
    (hdiff : ∀ t, DifferentiableOn ℂ (F t) U) :
    DifferentiableOn ℂ (fun y => ∫ t, F t y ∂μ) U ∧
      ∀ x ∈ U, Integrable (fun t => F t x) μ ∧ Integrable (fun t => fderiv ℂ (F t) x) μ ∧
        HasFDerivAt (fun y => ∫ t, F t y ∂μ) (∫ t, fderiv ℂ (F t) x ∂μ) x := by
  simpa only [Measure.restrict_univ, integrableOn_univ] using
    differentiableOn_setIntegral_of_holomorphic_of_continuousOn (μ := μ) hU isCompact_univ
      subset_rfl MeasurableSet.univ (measure_ne_top μ _) hcont fun t _ => hdiff t

theorem differentiableOn_intervalIntegral_of_holomorphic_of_continuousOn {F : ℝ → E → V}
    {U : Set E} (hU : IsOpen U) {a b : ℝ}
    (hcont : ContinuousOn (Function.uncurry F) ([[a, b]] ×ˢ U))
    (hdiff : ∀ t ∈ [[a, b]], DifferentiableOn ℂ (F t) U) :
    DifferentiableOn ℂ (fun y => ∫ t in a..b, F t y) U ∧
      ∀ x ∈ U, IntervalIntegrable (fun t => F t x) volume a b ∧
        IntervalIntegrable (fun t => fderiv ℂ (F t) x) volume a b ∧
        HasFDerivAt (fun y => ∫ t in a..b, F t y) (∫ t in a..b, fderiv ℂ (F t) x) x := by
  have h := differentiableOn_setIntegral_of_holomorphic_of_continuousOn (μ := volume) hU
    (isCompact_uIcc (a := a) (b := b)) uIoc_subset_uIcc measurableSet_uIoc
    (by simp [uIoc]) hcont fun t ht => hdiff t (uIoc_subset_uIcc ht)
  have key : ∀ x ∈ U, IntervalIntegrable (fun t => F t x) volume a b ∧
      IntervalIntegrable (fun t => fderiv ℂ (F t) x) volume a b ∧
      HasFDerivAt (fun y => ∫ t in a..b, F t y) (∫ t in a..b, fderiv ℂ (F t) x) x := by
    intro x hx
    obtain ⟨h1, h2, h3⟩ := h.2 x hx
    refine ⟨intervalIntegrable_iff.2 h1, intervalIntegrable_iff.2 h2, ?_⟩
    simp only [intervalIntegral.intervalIntegral_eq_integral_uIoc]
    split_ifs
    · simpa using h3
    · simpa using h3.fun_neg
  exact ⟨fun x hx => (key x hx).2.2.differentiableAt.differentiableWithinAt, key⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EntireApplyEqOfPeriodicOfSpanReal
open Set Metric Filter Topology
open scoped Nat

namespace GlobalTheory

section Periodic

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem entire_apply_eq_of_isZLattice_periodic [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {F : E → V} (hF : Differentiable ℂ F) (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L] (hper : ∀ x, ∀ g ∈ L, F (x + g) = F x) (z w : E) : F z = F w :=
  hF.apply_eq_apply_of_bounded
    (IsZLattice.isCompact_range_of_periodic L F hF.continuous hper).isBounded z w


omit [NormedSpace ℂ E] [NormedAddCommGroup V] [NormedSpace ℂ V] in
theorem periodic_of_mem_span_int {F : E → V} {S : Set E}
    (hper : ∀ x, ∀ g ∈ S, F (x + g) = F x) :
    ∀ x, ∀ g ∈ Submodule.span ℤ S, F (x + g) = F x := by
  let P : AddSubgroup E :=
    { carrier := {g | ∀ x, F (x + g) = F x}
      zero_mem' := fun x => by simp
      add_mem' := fun {a b} ha hb x => by rw [← add_assoc, hb, ha]
      neg_mem' := fun {a} ha x => by rw [← ha (x + -a)]; simp }
  intro x g hg
  have : Submodule.span ℤ S ≤ AddSubgroup.toIntSubmodule P :=
    Submodule.span_le.2 fun s hs y => hper y s hs
  exact this hg x

theorem entire_apply_eq_of_periodic_of_span_real [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {F : E → V} (hF : Differentiable ℂ F) {S : Set E} (hS : Submodule.span ℝ S = ⊤)
    (hper : ∀ x, ∀ g ∈ S, F (x + g) = F x) (z w : E) : F z = F w := by
  obtain ⟨t, htS, hspan, hli⟩ := exists_linearIndependent ℝ S
  let b : Module.Basis t ℝ E := Module.Basis.mk hli (by simp [hspan, hS])
  haveI : Finite t := Module.Finite.finite_basis b
  refine entire_apply_eq_of_isZLattice_periodic hF (Submodule.span ℤ (range b))
    (periodic_of_mem_span_int ?_) z w
  rintro x _ ⟨i, rfl⟩
  exact hper x _ (by simpa [b] using htS i.2)

end Periodic

section Polynomial

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

theorem iteratedDeriv_zero_eq_zero_of_poly_bound {F : ℂ → V} (hF : Differentiable ℂ F) {C : ℝ}
    {m : ℕ} (hb : ∀ z, ‖F z‖ ≤ C * (1 + ‖z‖) ^ m) {n : ℕ} (hn : m < n) :
    iteratedDeriv n F 0 = 0 := by
  have hC : 0 ≤ C := by simpa using (norm_nonneg _).trans (hb 0)
  have key : ∀ R : ℝ, 1 ≤ R → ‖iteratedDeriv n F 0‖ ≤ (n ! * C * 2 ^ m) / R := by
    intro R hR
    have hR0 : 0 < R := by linarith
    have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (c := 0) (R := R)
      (C := C * (2 ^ m * R ^ m)) n hR0 hF.diffContOnCl (fun z hz => by
        have hz' : ‖z‖ = R := by simpa using hz
        refine (hb z).trans ?_
        rw [hz', ← mul_pow]
        gcongr
        linarith)
    refine h.trans ?_
    rw [div_le_div_iff₀ (by positivity) hR0]
    have : R ^ m * R ≤ R ^ n := by
      rw [← pow_succ]
      exact pow_le_pow_right₀ hR hn
    calc (n ! : ℝ) * (C * (2 ^ m * R ^ m)) * R = (n ! * C * 2 ^ m) * (R ^ m * R) := by ring
      _ ≤ _ := by gcongr
  have lim : Tendsto (fun R : ℝ => (n ! * C * 2 ^ m) / R) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  exact norm_le_zero_iff.1 (ge_of_tendsto lim ((eventually_ge_atTop 1).mono key))

theorem entire_eq_taylor_sum_of_poly_bound {F : ℂ → V} (hF : Differentiable ℂ F) {C : ℝ}
    {m : ℕ} (hb : ∀ z, ‖F z‖ ≤ C * (1 + ‖z‖) ^ m) (z : ℂ) :
    F z = ∑ k ∈ Finset.range (m + 1), z ^ k • ((k ! : ℂ)⁻¹ • iteratedDeriv k F 0) := by
  have h := Complex.hasSum_taylorSeries_of_entire hF 0 z
  have h2 := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℕ)
    (f := fun n : ℕ => (n ! : ℂ)⁻¹ • (z - 0) ^ n • iteratedDeriv n F 0)
    (s := Finset.range (m + 1)) (fun n hn => by
      have : m < n := by simpa using hn
      simp [iteratedDeriv_zero_eq_zero_of_poly_bound hF hb this])
  rw [h.unique h2]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [sub_zero, smul_comm]

theorem entire_exists_coeff_of_poly_bound {F : ℂ → V} (hF : Differentiable ℂ F) {C : ℝ}
    {m : ℕ} (hb : ∀ z, ‖F z‖ ≤ C * (1 + ‖z‖) ^ m) :
    ∃ a : ℕ → V, ∀ z, F z = ∑ k ∈ Finset.range (m + 1), z ^ k • a k :=
  ⟨_, entire_eq_taylor_sum_of_poly_bound hF hb⟩

theorem entire_exists_polynomial_of_poly_bound {F : ℂ → ℂ} (hF : Differentiable ℂ F) {C : ℝ}
    {m : ℕ} (hb : ∀ z, ‖F z‖ ≤ C * (1 + ‖z‖) ^ m) :
    ∃ p : Polynomial ℂ, p.natDegree ≤ m ∧ ∀ z, F z = p.eval z := by
  obtain ⟨a, ha⟩ := entire_exists_coeff_of_poly_bound hF hb
  refine ⟨∑ k ∈ Finset.range (m + 1), Polynomial.monomial k (a k), ?_, fun z => ?_⟩
  · refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
    exact (Polynomial.natDegree_monomial_le _).trans (by simpa [Nat.lt_succ_iff] using hk)
  · rw [ha z, Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [mul_comm]

end Polynomial

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FinrankMulDiscrRpowLeSumSqOfMemTraceDual
open NumberField Module
open scoped nonZeroDivisors

namespace GlobalTheory

theorem card_mul_rpow_prod_le_sum {ι : Type*} [Fintype ι] [Nonempty ι] (z : ι → ℝ)
    (hz : ∀ i, 0 ≤ z i) :
    (Fintype.card ι : ℝ) * (∏ i, z i) ^ ((Fintype.card ι : ℝ)⁻¹) ≤ ∑ i, z i := by
  have hc : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have h := Real.geom_mean_le_arith_mean_weighted Finset.univ
    (fun _ : ι => (Fintype.card ι : ℝ)⁻¹) z (fun _ _ => by positivity)
    (by simp [hc.ne']) (fun i _ => hz i)
  rw [Real.finsetProd_rpow _ _ (fun i _ => hz i), ← Finset.mul_sum] at h
  calc _ ≤ (Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ)⁻¹ * ∑ i, z i) := by gcongr
    _ = _ := by field_simp

section General

variable {K : Type*} [Field K] [NumberField K]

theorem norm_eq_prod_complexEmbeddings (x : K) :
    ((Algebra.norm ℚ x : ℚ) : ℂ) = ∏ σ : K →+* ℂ, σ x := by
  rw [Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) (fun f => f x) (fun φ => φ x)
    (fun _ => rfl), ← Algebra.norm_eq_prod_embeddings ℚ ℂ x]
  simp

theorem trace_eq_sum_complexEmbeddings (x : K) :
    ((Algebra.trace ℚ K x : ℚ) : ℂ) = ∑ σ : K →+* ℂ, σ x := by
  rw [Fintype.sum_equiv (RingHom.equivRatAlgHom K ℂ) (fun f => f x) (fun φ => φ x)
    (fun _ => rfl), ← trace_eq_sum_embeddings ℂ (K := ℚ) (x := x)]
  simp

theorem abs_norm_eq_prod_complexEmbeddings (x : K) :
    |((Algebra.norm ℚ x : ℚ) : ℝ)| = ∏ σ : K →+* ℂ, ‖σ x‖ := by
  rw [← norm_prod, ← norm_eq_prod_complexEmbeddings, Complex.norm_ratCast]

theorem finrank_mul_abs_norm_rpow_le_sum (x : K) :
    (finrank ℚ K : ℝ) * |((Algebra.norm ℚ x : ℚ) : ℝ)| ^ ((finrank ℚ K : ℝ)⁻¹)
      ≤ ∑ σ : K →+* ℂ, ‖σ x‖ := by
  rw [abs_norm_eq_prod_complexEmbeddings, ← Embeddings.card K ℂ]
  exact card_mul_rpow_prod_le_sum _ fun _ => norm_nonneg _

theorem finrank_mul_abs_norm_rpow_le_sum_sq (x : K) :
    (finrank ℚ K : ℝ) * |((Algebra.norm ℚ x : ℚ) : ℝ)| ^ (2 / (finrank ℚ K : ℝ))
      ≤ ∑ σ : K →+* ℂ, ‖σ x‖ ^ 2 := by
  have h := finrank_mul_abs_norm_rpow_le_sum (x ^ 2)
  simp only [map_pow, norm_pow, Rat.cast_pow, abs_pow] at h
  rwa [div_eq_mul_inv, Real.rpow_mul (abs_nonneg _), Real.rpow_two]

theorem one_le_abs_norm_of_isIntegral {x : K} (hx : IsIntegral ℤ x) (h0 : x ≠ 0) :
    1 ≤ |Algebra.norm ℚ x| := by
  have hn : IsIntegral ℤ (Algebra.norm ℚ x) := Algebra.isIntegral_norm ℚ hx
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.mp hn
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [map_zero, eq_comm, Algebra.norm_eq_zero_iff] at hm
    exact h0 hm
  rw [← hm, eq_intCast]
  exact_mod_cast Int.one_le_abs hm0

theorem absNorm_le_abs_norm_of_mem {J : FractionalIdeal (𝓞 K)⁰ K} {x : K} (hx : x ∈ J)
    (h0 : x ≠ 0) : FractionalIdeal.absNorm J ≤ |Algebra.norm ℚ x| := by
  have hJ : J ≠ 0 := by
    rintro rfl
    exact h0 ((FractionalIdeal.mem_zero_iff _).mp hx)
  have hle : FractionalIdeal.spanSingleton (𝓞 K)⁰ x * J⁻¹ ≤ 1 := by
    calc _ ≤ J * J⁻¹ := by
          gcongr
          exact FractionalIdeal.spanSingleton_le_iff_mem.mpr hx
      _ = 1 := mul_inv_cancel₀ hJ
  obtain ⟨I, hI⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hle
  have hI' : FractionalIdeal.spanSingleton (𝓞 K)⁰ x = I * J := by
    rw [hI, inv_mul_cancel_right₀ hJ]
  have hI0 : I ≠ ⊥ := by
    rintro rfl
    exact h0 (by simpa using hI')
  have h1 : (1 : ℚ) ≤ Ideal.absNorm I := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI0)
  rw [← FractionalIdeal.absNorm_span_singleton (𝓞 K), hI', map_mul,
    FractionalIdeal.coeIdeal_absNorm]
  exact le_mul_of_one_le_left (FractionalIdeal.absNorm_nonneg _) h1

theorem finrank_mul_absNorm_rpow_le_sum_sq {J : FractionalIdeal (𝓞 K)⁰ K} {x : K} (hx : x ∈ J)
    (h0 : x ≠ 0) :
    (finrank ℚ K : ℝ) * ((FractionalIdeal.absNorm J : ℚ) : ℝ) ^ (2 / (finrank ℚ K : ℝ))
      ≤ ∑ σ : K →+* ℂ, ‖σ x‖ ^ 2 := by
  refine le_trans ?_ (finrank_mul_abs_norm_rpow_le_sum_sq x)
  have h1 : ((FractionalIdeal.absNorm J : ℚ) : ℝ) ≤ |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
    exact_mod_cast absNorm_le_abs_norm_of_mem hx h0
  have h2 : (0 : ℝ) ≤ ((FractionalIdeal.absNorm J : ℚ) : ℝ) := by
    exact_mod_cast FractionalIdeal.absNorm_nonneg J
  gcongr


variable (K) in
theorem dual_one_eq_inv_differentIdeal :
    FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K)
      = (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
  rw [coeIdeal_differentIdeal ℤ ℚ K (𝓞 K), inv_inv]


variable (K) in
theorem absNorm_inv_differentIdeal :
    FractionalIdeal.absNorm (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K)⁻¹
      = |(discr K : ℚ)|⁻¹ := by
  rw [map_inv₀, FractionalIdeal.coeIdeal_absNorm, absNorm_differentIdeal K]
  simp

theorem finrank_mul_discr_rpow_le_sum_sq {x : K}
    (hx : x ∈ (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K)⁻¹) (h0 : x ≠ 0) :
    (finrank ℚ K : ℝ) * |(discr K : ℝ)| ^ (-2 / (finrank ℚ K : ℝ))
      ≤ ∑ σ : K →+* ℂ, ‖σ x‖ ^ 2 := by
  have h := finrank_mul_absNorm_rpow_le_sum_sq hx h0
  rw [absNorm_inv_differentIdeal] at h
  rw [neg_div, Real.rpow_neg (abs_nonneg _), ← Real.inv_rpow (abs_nonneg _)]
  simpa using h

theorem finrank_div_rootDiscr_sq_le_sum_sq {x : K}
    (hx : x ∈ (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K)⁻¹) (h0 : x ≠ 0) :
    (finrank ℚ K : ℝ) / rootDiscr K ^ 2 ≤ ∑ σ : K →+* ℂ, ‖σ x‖ ^ 2 := by
  have h := finrank_mul_discr_rpow_le_sum_sq hx h0
  rw [neg_div, Real.rpow_neg (abs_nonneg _), div_eq_inv_mul, Real.rpow_mul (abs_nonneg _),
    Real.rpow_two] at h
  rw [rootDiscr_def, div_eq_mul_inv]
  simpa using h

theorem finrank_mul_discr_rpow_le_sum_sq_of_mem_traceDual {x : K}
    (hx : x ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 K) K)) (h0 : x ≠ 0) :
    (finrank ℚ K : ℝ) * |(discr K : ℝ)| ^ (-2 / (finrank ℚ K : ℝ))
      ≤ ∑ σ : K →+* ℂ, ‖σ x‖ ^ 2 := by
  refine finrank_mul_discr_rpow_le_sum_sq ?_ h0
  rw [← dual_one_eq_inv_differentIdeal, ← FractionalIdeal.mem_coe, FractionalIdeal.coe_dual_one]
  exact hx

end General

section TotallyReal

variable {F : Type*} [Field F] [NumberField F] [IsTotallyReal F]


omit [NumberField F] in
variable (F) in
theorem bijective_ofRealHom_comp :
    Function.Bijective (fun σ : F →+* ℝ => Complex.ofRealHom.comp σ) := by
  refine ⟨fun σ τ h => RingHom.ext fun x => ?_, fun φ => ?_⟩
  · simpa using RingHom.congr_fun h x
  · exact ⟨(IsTotallyReal.complexEmbedding_isReal φ).embedding, RingHom.ext fun x => by simp⟩


variable (F) in
theorem card_realEmbeddings : Fintype.card (F →+* ℝ) = finrank ℚ F := by
  rw [← Embeddings.card F ℂ]
  exact Fintype.card_of_bijective (bijective_ofRealHom_comp F)

theorem trace_eq_sum_realEmbeddings (x : F) :
    ((Algebra.trace ℚ F x : ℚ) : ℝ) = ∑ σ : F →+* ℝ, σ x := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_ratCast, trace_eq_sum_complexEmbeddings, Complex.ofReal_sum]
  exact ((bijective_ofRealHom_comp F).sum_comp (fun φ => φ x)).symm

end TotallyReal

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.LinearIndependentRealOfIntOfDiscrete
open scoped ComplexOrder InnerProductSpace MatrixOrder
open Module Submodule MeasureTheory Matrix

namespace GlobalTheory

section Gram

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem det_gram_eq_normSq_det {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
    (b : OrthonormalBasis ι 𝕜 V) (v : ι → V) :
    (gram 𝕜 v).det = ((‖b.toBasis.det v‖ ^ 2 : ℝ) : 𝕜) := by
  have h : b.toBasis.det v = (Matrix.of fun i j ↦ b.repr (v j) i).det := by
    rw [Basis.det_apply]; congr 1
  rw [gram_eq_conjTranspose_mul b v, det_mul, det_conjTranspose, h, RCLike.star_def,
    RCLike.conj_mul]
  push_cast; rfl

theorem det_gram_le_of_finrank_eq {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
    [FiniteDimensional 𝕜 V] (h : finrank 𝕜 V = Fintype.card ι) (v : ι → V) :
    (gram 𝕜 v).det ≤ ((∏ i, ‖v i‖ ^ 2 : ℝ) : 𝕜) := by
  let e := (Fintype.equivFin ι).symm
  have h' : finrank 𝕜 V = Fintype.card (Fin (Fintype.card ι)) := by simpa using h
  have h1 : (gram 𝕜 v).det = (gram 𝕜 (v ∘ e)).det := by
    rw [← det_submatrix_equiv_self e]; rfl
  let b := InnerProductSpace.gramSchmidtOrthonormalBasis h' (v ∘ e)
  have hb : b.toBasis.det (v ∘ e) = ∏ i, ⟪b i, (v ∘ e) i⟫_𝕜 :=
    InnerProductSpace.gramSchmidtOrthonormalBasis_det h' _
  rw [h1, det_gram_eq_normSq_det b, hb, RCLike.ofReal_le_ofReal, norm_prod, ← Finset.prod_pow,
    ← e.prod_comp (fun i ↦ ‖v i‖ ^ 2)]
  refine Finset.prod_le_prod₀ (fun i _ ↦ by positivity) fun i _ ↦ ?_
  gcongr
  simpa using norm_inner_le_norm (𝕜 := 𝕜) (b i) (v (e i))

theorem norm_det_sq_le_prod_col (A : Matrix ι ι 𝕜) :
    ‖A.det‖ ^ 2 ≤ ∏ j, ∑ i, ‖A i j‖ ^ 2 := by
  let v : ι → EuclideanSpace 𝕜 ι := fun j ↦ WithLp.toLp 2 fun i ↦ A i j
  have h := det_gram_le_of_finrank_eq (𝕜 := 𝕜) (by simp) v
  rw [det_gram_eq_normSq_det (EuclideanSpace.basisFun ι 𝕜), RCLike.ofReal_le_ofReal] at h
  have h2 : (EuclideanSpace.basisFun ι 𝕜).toBasis.det v = A.det := by
    rw [Basis.det_apply]; congr 1
  rw [h2] at h
  refine h.trans_eq (Finset.prod_congr rfl fun j _ ↦ ?_)
  rw [EuclideanSpace.norm_sq_eq]

theorem posSemidef_det_le_prod_diag {A : Matrix ι ι 𝕜} (hA : A.PosSemidef) :
    A.det ≤ ∏ i, A i i := by
  obtain ⟨B, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.1 hA.nonneg
  have h := norm_det_sq_le_prod_col B
  rw [← RCLike.ofReal_le_ofReal (K := 𝕜)] at h
  convert h using 1
  · rw [det_mul, star_eq_conjTranspose, det_conjTranspose, RCLike.star_def, RCLike.conj_mul]
    push_cast; rfl
  · push_cast
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    simp [Matrix.mul_apply, RCLike.conj_mul]

variable {V : Type*} [SeminormedAddCommGroup V] [InnerProductSpace 𝕜 V]

end Gram

section Covolume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι]

theorem linearIndependent_real_of_int_of_discrete {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] (L : Submodule ℤ F) [DiscreteTopology L]
    {v : ι → F} (hv : ∀ i, v i ∈ L) (hli : LinearIndependent ℤ v) : LinearIndependent ℝ v := by
  have hle : span ℤ (Set.range v) ≤ L := span_le.2 (Set.range_subset_iff.2 hv)
  have hd : DiscreteTopology (span ℤ (Set.range v)) :=
    DiscreteTopology.of_continuous_injective (β := L) (f := Set.inclusion hle)
      (continuous_inclusion hle) (Set.inclusion_injective hle)
  rw [linearIndependent_iff_card_eq_finrank_span] at hli ⊢
  rw [Real.finrank_eq_int_finrank_of_discrete hd, hli]

variable [MeasurableSpace E] [BorelSpace E]

theorem covolume_span_basis_eq_sqrt_det_gram [DecidableEq ι] (b : Basis ι ℝ E) :
    ZLattice.covolume (span ℤ (Set.range b)) = √(gram ℝ b).det := by
  let o : OrthonormalBasis ι ℝ E := (stdOrthonormalBasis ℝ E).reindex
    (Fintype.equivFinOfCardEq (finrank_eq_card_basis b).symm).symm
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ volume
      (ZSpan.isAddFundamentalDomain b volume),
    ZSpan.measureReal_fundamentalDomain b volume o.toBasis,
    measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped o.toBasis volume),
    det_gram_eq_normSq_det o, measureReal_def, o.coe_toBasis, o.volume_parallelepiped]
  simp [Real.sqrt_sq_eq_abs]

theorem covolume_eq_sqrt_det_gram [DecidableEq ι] (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L] (b : Basis ι ℤ L) :
    ZLattice.covolume L = √(gram ℝ fun i ↦ (b i : E)).det := by
  have h := covolume_span_basis_eq_sqrt_det_gram (b.ofZLatticeBasis ℝ L)
  rw [b.ofZLatticeBasis_span ℝ] at h
  rw [h]
  congr 3
  ext i
  simp

end Covolume

end GlobalTheory
end
