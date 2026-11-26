module

public import Mathlib

@[expose] public section

section -- merged from GroundTheory.AutomorphicForms.HilbertSchmidt
namespace GroundTheory.Automorphic

open scoped ENNReal InnerProductSpace InnerProduct
open ContinuousLinearMap

noncomputable section

section Auxiliary

theorem ennreal_add_sq_le (a b : ℝ≥0∞) : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  rcases eq_or_ne a ∞ with rfl | ha
  · simp
  rcases eq_or_ne b ∞ with rfl | hb
  · simp
  lift a to NNReal using ha
  lift b to NNReal using hb
  norm_cast
  rw [← NNReal.coe_le_coe]
  push_cast
  nlinarith [sq_nonneg ((a : ℝ) - b)]

theorem ennreal_mul_le_sq_add_sq (a b : ℝ≥0∞) : a * b ≤ a ^ 2 + b ^ 2 := by
  rcases le_total a b with h | h
  · calc a * b ≤ b * b := by gcongr
      _ = b ^ 2 := (sq b).symm
      _ ≤ a ^ 2 + b ^ 2 := le_add_self
  · calc a * b ≤ a * a := by gcongr
      _ = a ^ 2 := (sq a).symm
      _ ≤ a ^ 2 + b ^ 2 := le_self_add

end Auxiliary

section HilbertSchmidt

variable {𝕜 : Type*} [RCLike 𝕜]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]
  {L : Type*} [NormedAddCommGroup L] [InnerProductSpace 𝕜 L] [CompleteSpace L]

theorem enorm_inner_le (x y : H) : ‖⟪x, y⟫_𝕜‖ₑ ≤ ‖x‖ₑ * ‖y‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (norm_inner_le_norm x y)

theorem enorm_inner_comm (x y : H) : ‖⟪x, y⟫_𝕜‖ₑ = ‖⟪y, x⟫_𝕜‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, norm_inner_symm]

theorem enorm_apply_le (A : H →L[𝕜] K) (x : H) : ‖A x‖ₑ ≤ ‖A‖ₑ * ‖x‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (A.le_opNorm x)

theorem enorm_sq_eq_tsum {ι : Type*} (b : HilbertBasis ι 𝕜 H) (x : H) :
    ‖x‖ₑ ^ 2 = ∑' i, ‖⟪b i, x⟫_𝕜‖ₑ ^ 2 := by
  have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  have h1 := lp.norm_rpow_eq_tsum hp (b.repr x)
  have h2 := (lp.memℓp (b.repr x)).summable hp
  simp only [LinearIsometryEquiv.norm_map, HilbertBasis.repr_apply_apply, ENNReal.toReal_ofNat,
    Real.rpow_two] at h1 h2
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), h1,
    ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) h2]
  congr 1
  ext i
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

theorem tsum_enorm_sq_eq_adjoint {ι κ : Type*} (b : HilbertBasis ι 𝕜 H)
    (c : HilbertBasis κ 𝕜 K) (T : H →L[𝕜] K) :
    ∑' i, ‖T (b i)‖ₑ ^ 2 = ∑' j, ‖(T†) (c j)‖ₑ ^ 2 := by
  calc ∑' i, ‖T (b i)‖ₑ ^ 2 = ∑' i, ∑' j, ‖⟪c j, T (b i)⟫_𝕜‖ₑ ^ 2 := by
        congr 1; ext i; exact enorm_sq_eq_tsum c _
    _ = ∑' j, ∑' i, ‖⟪c j, T (b i)⟫_𝕜‖ₑ ^ 2 := ENNReal.tsum_comm
    _ = ∑' j, ∑' i, ‖⟪b i, (T†) (c j)⟫_𝕜‖ₑ ^ 2 := by
        congr 1; ext j; congr 1; ext i
        rw [← adjoint_inner_left, enorm_inner_comm]
    _ = ∑' j, ‖(T†) (c j)‖ₑ ^ 2 := by
        congr 1; ext j; exact (enorm_sq_eq_tsum b _).symm


variable (𝕜 H) in
def stdHilbertBasis : HilbertBasis (exists_hilbertBasis 𝕜 H).choose 𝕜 H :=
  (exists_hilbertBasis 𝕜 H).choose_spec.choose

def hsNormSq (T : H →L[𝕜] K) : ℝ≥0∞ := ∑' i, ‖T (stdHilbertBasis 𝕜 H i)‖ₑ ^ 2

theorem hsNormSq_eq_tsum {ι : Type*} (b : HilbertBasis ι 𝕜 H) (T : H →L[𝕜] K) :
    hsNormSq T = ∑' i, ‖T (b i)‖ₑ ^ 2 := by
  rw [hsNormSq, tsum_enorm_sq_eq_adjoint _ (stdHilbertBasis 𝕜 K),
    tsum_enorm_sq_eq_adjoint b (stdHilbertBasis 𝕜 K)]

theorem hsNormSq_adjoint (T : H →L[𝕜] K) : hsNormSq (T†) = hsNormSq T := by
  rw [hsNormSq_eq_tsum (stdHilbertBasis 𝕜 K) (T†), hsNormSq,
    tsum_enorm_sq_eq_adjoint (stdHilbertBasis 𝕜 H) (stdHilbertBasis 𝕜 K)]

def IsHilbertSchmidt (T : H →L[𝕜] K) : Prop := hsNormSq T < ∞

theorem isHilbertSchmidt_iff {ι : Type*} (b : HilbertBasis ι 𝕜 H) (T : H →L[𝕜] K) :
    IsHilbertSchmidt T ↔ ∑' i, ‖T (b i)‖ₑ ^ 2 < ∞ := by
  rw [IsHilbertSchmidt, hsNormSq_eq_tsum b]

theorem isHilbertSchmidt_adjoint_iff (T : H →L[𝕜] K) :
    IsHilbertSchmidt (T†) ↔ IsHilbertSchmidt T := by
  rw [IsHilbertSchmidt, IsHilbertSchmidt, hsNormSq_adjoint]

theorem IsHilbertSchmidt.adjoint {T : H →L[𝕜] K} (hT : IsHilbertSchmidt T) :
    IsHilbertSchmidt (T†) :=
  (isHilbertSchmidt_adjoint_iff T).2 hT

def hsNorm (T : H →L[𝕜] K) : ℝ := √(hsNormSq T).toReal

theorem hsNorm_nonneg (T : H →L[𝕜] K) : 0 ≤ hsNorm T := Real.sqrt_nonneg _

theorem hsNorm_sq (T : H →L[𝕜] K) : hsNorm T ^ 2 = (hsNormSq T).toReal :=
  Real.sq_sqrt ENNReal.toReal_nonneg

theorem hsNorm_adjoint (T : H →L[𝕜] K) : hsNorm (T†) = hsNorm T := by
  rw [hsNorm, hsNorm, hsNormSq_adjoint]

theorem enorm_apply_sq_le (T : H →L[𝕜] K) (x : H) :
    ‖T x‖ₑ ^ 2 ≤ hsNormSq T * ‖x‖ₑ ^ 2 := by
  let c := stdHilbertBasis 𝕜 K
  rw [← hsNormSq_adjoint, hsNormSq_eq_tsum c, enorm_sq_eq_tsum c, ← ENNReal.tsum_mul_right]
  refine ENNReal.tsum_le_tsum fun j => ?_
  rw [← adjoint_inner_left, ← mul_pow]
  gcongr
  exact enorm_inner_le _ _

theorem norm_le_hsNorm {T : H →L[𝕜] K} (hT : IsHilbertSchmidt T) : ‖T‖ ≤ hsNorm T := by
  refine T.opNorm_le_bound (hsNorm_nonneg T) fun x => ?_
  have h := enorm_apply_sq_le T x
  rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_toReal hT.ne,
    ← ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
  rw [← Real.sqrt_sq (norm_nonneg (T x)), hsNorm, ← Real.sqrt_sq (norm_nonneg x),
    ← Real.sqrt_mul ENNReal.toReal_nonneg]
  exact Real.sqrt_le_sqrt h

theorem hsNormSq_zero : hsNormSq (0 : H →L[𝕜] K) = 0 := by
  simp [hsNormSq]

theorem hsNormSq_smul (c : 𝕜) (T : H →L[𝕜] K) : hsNormSq (c • T) = ‖c‖ₑ ^ 2 * hsNormSq T := by
  simp only [hsNormSq, smul_apply, enorm_smul, mul_pow, ENNReal.tsum_mul_left]

theorem hsNormSq_add_le (S T : H →L[𝕜] K) :
    hsNormSq (S + T) ≤ 2 * hsNormSq S + 2 * hsNormSq T := by
  simp only [hsNormSq, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun i => ?_
  calc ‖(S + T) _‖ₑ ^ 2 ≤ (‖S _‖ₑ + ‖T _‖ₑ) ^ 2 := by
        gcongr; exact enorm_add_le _ _
    _ ≤ _ := ennreal_add_sq_le _ _

theorem hsNormSq_comp_left_le (A : K →L[𝕜] L) (T : H →L[𝕜] K) :
    hsNormSq (A.comp T) ≤ ‖A‖ₑ ^ 2 * hsNormSq T := by
  simp only [hsNormSq, ← ENNReal.tsum_mul_left, comp_apply]
  refine ENNReal.tsum_le_tsum fun i => ?_
  rw [← mul_pow]
  gcongr
  exact enorm_apply_le _ _

theorem hsNormSq_comp_right_le (T : K →L[𝕜] L) (B : H →L[𝕜] K) :
    hsNormSq (T.comp B) ≤ ‖B‖ₑ ^ 2 * hsNormSq T := by
  rw [← hsNormSq_adjoint, adjoint_comp, ← hsNormSq_adjoint T]
  calc hsNormSq ((B†).comp (T†)) ≤ ‖B†‖ₑ ^ 2 * hsNormSq (T†) := hsNormSq_comp_left_le _ _
    _ = ‖B‖ₑ ^ 2 * hsNormSq (T†) := by
        rw [← ofReal_norm, ← ofReal_norm, adjoint.norm_map]

theorem IsHilbertSchmidt.comp_left {T : H →L[𝕜] K} (hT : IsHilbertSchmidt T) (A : K →L[𝕜] L) :
    IsHilbertSchmidt (A.comp T) :=
  (hsNormSq_comp_left_le A T).trans_lt (ENNReal.mul_lt_top (by simp) hT)

theorem IsHilbertSchmidt.comp_right {T : K →L[𝕜] L} (hT : IsHilbertSchmidt T) (B : H →L[𝕜] K) :
    IsHilbertSchmidt (T.comp B) :=
  (hsNormSq_comp_right_le T B).trans_lt (ENNReal.mul_lt_top (by simp) hT)


variable (𝕜 H K) in
def hilbertSchmidt : Submodule 𝕜 (H →L[𝕜] K) where
  carrier := {T | IsHilbertSchmidt T}
  add_mem' {S T} hS hT := by
    refine (hsNormSq_add_le S T).trans_lt ?_
    exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by simp) hS, ENNReal.mul_lt_top (by simp) hT⟩
  zero_mem' := by
    show hsNormSq (0 : H →L[𝕜] K) < ∞
    simp [hsNormSq_zero]
  smul_mem' c T hT := by
    show hsNormSq (c • T) < ∞
    rw [hsNormSq_smul]
    exact ENNReal.mul_lt_top (by simp) hT

theorem IsHilbertSchmidt.add {S T : H →L[𝕜] K} (hS : IsHilbertSchmidt S)
    (hT : IsHilbertSchmidt T) : IsHilbertSchmidt (S + T) :=
  (hilbertSchmidt (𝕜 := 𝕜) (H := H) (K := K)).add_mem hS hT

theorem IsHilbertSchmidt.hasSum_norm_sq {T : H →L[𝕜] K} (hT : IsHilbertSchmidt T) {ι : Type*}
    (b : HilbertBasis ι 𝕜 H) : HasSum (fun i => ‖T (b i)‖ ^ 2) (hsNorm T ^ 2) := by
  have hfin : ∑' i, ‖T (b i)‖ₑ ^ 2 ≠ ∞ := by rw [← hsNormSq_eq_tsum b]; exact hT.ne
  have hs := ENNReal.summable_toReal hfin
  rw [hsNorm_sq, hsNormSq_eq_tsum b, ENNReal.tsum_toReal_eq fun i => by simp]
  convert hs.hasSum using 2 with i; simp

theorem hasSum_inner_comp_comm {ι κ : Type*} (e : HilbertBasis ι 𝕜 H) (f : HilbertBasis κ 𝕜 K)
    {A : K →L[𝕜] H} {B : H →L[𝕜] K} (hA : IsHilbertSchmidt A) (hB : IsHilbertSchmidt B) :
    HasSum (fun i => ⟪e i, A (B (e i))⟫_𝕜) (∑' j, ⟪f j, B (A (f j))⟫_𝕜) := by
  let F : ι → κ → 𝕜 := fun i j => ⟪(B†) (f j), e i⟫_𝕜 * ⟪e i, A (f j)⟫_𝕜

  have hfin : ∑' p : ι × κ, ‖Function.uncurry F p‖ₑ ≠ ∞ := by
    refine ne_top_of_le_ne_top (b := ∑' p : ι × κ,
      (‖⟪e p.1, (B†) (f p.2)⟫_𝕜‖ₑ ^ 2 + ‖⟪e p.1, A (f p.2)⟫_𝕜‖ₑ ^ 2)) ?_ ?_
    · rw [ENNReal.tsum_add, ENNReal.tsum_prod', ENNReal.tsum_prod', ENNReal.tsum_comm,
        ENNReal.tsum_comm (f := fun i j => ‖⟪e i, A (f j)⟫_𝕜‖ₑ ^ 2)]
      simp only [← enorm_sq_eq_tsum e, ← hsNormSq_eq_tsum f]
      exact ENNReal.add_ne_top.2 ⟨(hB.adjoint).ne, hA.ne⟩
    · refine ENNReal.tsum_le_tsum fun p => ?_
      simp only [Function.uncurry, F, enorm_mul]
      rw [enorm_inner_comm ((B†) (f p.2))]
      exact ennreal_mul_le_sq_add_sq _ _
  have hF : Summable (Function.uncurry F) := by
    refine Summable.of_norm ?_
    convert ENNReal.summable_toReal hfin using 2 with p
    simp
  have h1 : ∀ i, ∑' j, F i j = ⟪e i, A (B (e i))⟫_𝕜 := by
    intro i
    rw [← adjoint_inner_left A]
    refine ((f.hasSum_inner_mul_inner ((A†) (e i)) (B (e i))).congr_fun fun j => ?_).tsum_eq
    simp only [F]
    rw [adjoint_inner_left, adjoint_inner_left, mul_comm]
  have h2 : ∀ j, ∑' i, F i j = ⟪f j, B (A (f j))⟫_𝕜 := by
    intro j
    rw [← adjoint_inner_left B]
    exact (e.hasSum_inner_mul_inner ((B†) (f j)) (A (f j))).tsum_eq
  have hsum := hF.prod
  simp only [Function.uncurry_apply_pair] at hsum
  have hval : ∑' j, ⟪f j, B (A (f j))⟫_𝕜 = ∑' i, ∑' j, F i j := by
    simp_rw [← h2]
    exact hF.tsum_comm
  rw [hval, show (fun i => ⟪e i, A (B (e i))⟫_𝕜) = fun i => ∑' j, F i j from
    funext fun i => (h1 i).symm]
  exact hsum.hasSum

end HilbertSchmidt

end

end GroundTheory.Automorphic
end

section -- merged from GroundTheory.AutomorphicForms.QuadraticConj
namespace GroundTheory.Automorphic

open Module

variable (F E : Type*) [Field F] [CommRing E] [Algebra F E]

noncomputable def conjLinear : E →ₗ[F] E :=
  (Algebra.linearMap F E).comp (Algebra.trace F E) - LinearMap.id

variable {F E}

theorem conjLinear_apply (x : E) :
    conjLinear F E x = algebraMap F E (Algebra.trace F E x) - x := rfl

variable [Algebra.IsQuadraticExtension F E]

theorem trace_algebraMap_quadratic (c : F) : Algebra.trace F E (algebraMap F E c) = 2 * c := by
  rw [Algebra.trace_algebraMap, Algebra.IsQuadraticExtension.finrank_eq_two, nsmul_eq_mul]
  norm_num

theorem conjLinear_algebraMap (c : F) : conjLinear F E (algebraMap F E c) = algebraMap F E c := by
  rw [conjLinear_apply, trace_algebraMap_quadratic, map_mul, map_ofNat]
  ring

theorem conjLinear_one : conjLinear F E 1 = 1 := by
  simpa using conjLinear_algebraMap (F := F) (E := E) 1


omit [Algebra.IsQuadraticExtension F E] in
theorem linearIndependent_one_of_not_mem [Nontrivial E] {x : E}
    (hx : x ∉ Set.range (algebraMap F E)) : LinearIndependent F ![1, x] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  by_cases ht : t = 0
  · subst ht
    simp only [zero_smul, add_zero] at hst
    refine ⟨?_, rfl⟩
    by_contra hs
    exact one_ne_zero ((smul_eq_zero.mp hst).resolve_left hs)
  · exfalso
    apply hx
    refine ⟨-(s / t), ?_⟩
    have : t • x = -(s • (1 : E)) := eq_neg_of_add_eq_zero_right hst
    rw [Algebra.algebraMap_eq_smul_one]
    have h2 : x = t⁻¹ • (t • x) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
    rw [h2, this, smul_neg, smul_smul, neg_smul, div_eq_inv_mul]

theorem nontrivial_quadratic (K A : Type*) [Field K] [CommRing A] [Algebra K A]
    [Algebra.IsQuadraticExtension K A] : Nontrivial A :=
  Module.nontrivial_of_finrank_pos (R := K) (by
    rw [Algebra.IsQuadraticExtension.finrank_eq_two]; norm_num)

noncomputable def basisOneOf {x : E} (hx : x ∉ Set.range (algebraMap F E)) : Basis (Fin 2) F E :=
  haveI := nontrivial_quadratic F E
  basisOfLinearIndependentOfCardEqFinrank (linearIndependent_one_of_not_mem hx)
    (by rw [Algebra.IsQuadraticExtension.finrank_eq_two, Fintype.card_fin])

theorem basisOneOf_zero {x : E} (hx : x ∉ Set.range (algebraMap F E)) : basisOneOf hx 0 = 1 := by
  simp [basisOneOf]

theorem basisOneOf_one {x : E} (hx : x ∉ Set.range (algebraMap F E)) : basisOneOf hx 1 = x := by
  simp [basisOneOf]

theorem sq_eq_of_not_mem {x : E} (hx : x ∉ Set.range (algebraMap F E)) :
    x * x = algebraMap F E ((basisOneOf hx).repr (x * x) 0) +
      algebraMap F E ((basisOneOf hx).repr (x * x) 1) * x := by
  conv_lhs => rw [← (basisOneOf hx).sum_repr (x * x)]
  rw [Fin.sum_univ_two, basisOneOf_zero, basisOneOf_one, Algebra.smul_def, Algebra.smul_def,
    mul_one]

theorem repr_self_zero {x : E} (hx : x ∉ Set.range (algebraMap F E)) :
    (basisOneOf hx).repr x 0 = 0 := by
  have h := (basisOneOf hx).repr_self 1
  rw [basisOneOf_one] at h
  rw [h]; simp

theorem repr_self_one {x : E} (hx : x ∉ Set.range (algebraMap F E)) :
    (basisOneOf hx).repr x 1 = 1 := by
  have h := (basisOneOf hx).repr_self 1
  rw [basisOneOf_one] at h
  rw [h]; simp

theorem trace_eq_of_not_mem {x : E} (hx : x ∉ Set.range (algebraMap F E)) :
    Algebra.trace F E x = (basisOneOf hx).repr (x * x) 1 := by
  rw [Algebra.trace_eq_matrix_trace (basisOneOf hx), Matrix.trace_fin_two,
    Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul, basisOneOf_zero,
    basisOneOf_one, mul_one, repr_self_zero, zero_add]

theorem norm_eq_of_not_mem {x : E} (hx : x ∉ Set.range (algebraMap F E)) :
    Algebra.norm F x = -(basisOneOf hx).repr (x * x) 0 := by
  rw [Algebra.norm_eq_matrix_det (basisOneOf hx), Matrix.det_fin_two,
    Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul, basisOneOf_zero,
    basisOneOf_one, mul_one, repr_self_zero, repr_self_one]
  ring

theorem conjLinear_mul_self (x : E) :
    conjLinear F E (x * x) = conjLinear F E x * conjLinear F E x := by
  by_cases hx : x ∈ Set.range (algebraMap F E)
  · obtain ⟨c, rfl⟩ := hx
    rw [← map_mul, conjLinear_algebraMap, conjLinear_algebraMap, map_mul]
  · have hsq := sq_eq_of_not_mem hx
    have htr : Algebra.trace F E x = (basisOneOf hx).repr (x * x) 1 := trace_eq_of_not_mem hx
    have htr2 : Algebra.trace F E (x * x) = 2 * (basisOneOf hx).repr (x * x) 0 +
        (basisOneOf hx).repr (x * x) 1 * (basisOneOf hx).repr (x * x) 1 := by
      conv_lhs => rw [hsq]
      rw [map_add (f := _), trace_algebraMap_quadratic, ← Algebra.smul_def, map_smul, htr, smul_eq_mul]
    rw [conjLinear_apply, conjLinear_apply, htr2, htr]
    simp only [map_add (f := _), map_mul, map_ofNat]
    linear_combination (-2 : E) * hsq

theorem conjLinear_mul (x y : E) :
    conjLinear F E (x * y) = conjLinear F E x * conjLinear F E y := by
  by_cases hx : x ∈ Set.range (algebraMap F E)
  · obtain ⟨c, rfl⟩ := hx
    rw [conjLinear_algebraMap, ← Algebra.smul_def, ← Algebra.smul_def, map_smul]
  · have key : (conjLinear F E).comp (LinearMap.mulLeft F x) =
        (LinearMap.mulLeft F (conjLinear F E x)).comp (conjLinear F E) := by
      refine (basisOneOf hx).ext fun i => ?_
      fin_cases i
      · simp [basisOneOf_zero, conjLinear_one]
      · simp only [Fin.mk_one, basisOneOf_one, LinearMap.coe_comp, Function.comp_apply,
          LinearMap.mulLeft_apply]
        exact conjLinear_mul_self x
    exact LinearMap.congr_fun key y

theorem conjLinear_conjLinear (x : E) : conjLinear F E (conjLinear F E x) = x := by
  rw [conjLinear_apply, conjLinear_apply x, map_sub, trace_algebraMap_quadratic, map_sub,
    map_mul, map_ofNat]
  ring

variable (F E) in
noncomputable def conj : E ≃ₐ[F] E :=
  AlgEquiv.ofLinearEquiv
    (LinearEquiv.ofInvolutive (conjLinear F E) (fun x => conjLinear_conjLinear x))
    conjLinear_one conjLinear_mul

theorem conj_apply (x : E) : conj F E x = algebraMap F E (Algebra.trace F E x) - x := rfl

@[simp]
theorem conj_conj (x : E) : conj F E (conj F E x) = x := conjLinear_conjLinear x

theorem conj_algebraMap (c : F) : conj F E (algebraMap F E c) = algebraMap F E c :=
  conjLinear_algebraMap c

theorem add_conj (x : E) : x + conj F E x = algebraMap F E (Algebra.trace F E x) := by
  rw [conj_apply]; ring

theorem mul_conj (x : E) : x * conj F E x = algebraMap F E (Algebra.norm F x) := by
  by_cases hx : x ∈ Set.range (algebraMap F E)
  · obtain ⟨c, rfl⟩ := hx
    rw [conj_algebraMap, Algebra.norm_algebraMap, Algebra.IsQuadraticExtension.finrank_eq_two,
      map_pow, sq]
  · have hsq := sq_eq_of_not_mem hx
    rw [conj_apply, trace_eq_of_not_mem hx, norm_eq_of_not_mem hx, map_neg]
    linear_combination (-1 : E) * hsq

end GroundTheory.Automorphic
end

section -- merged from GroundTheory.AutomorphicForms.SphericalLaurent
noncomputable section

namespace GroundTheory.Automorphic

namespace Spherical

open AddMonoidAlgebra

variable {n : ℕ}


variable (n) in
abbrev LaurentRing (n : ℕ) : Type := AddMonoidAlgebra ℂ (Fin n → ℤ)

abbrev monomial (l : Fin n → ℤ) : LaurentRing n := single l 1

def monomialChar (l : Fin n → ℤ) : (Fin n → ℂˣ) →* ℂ where
  toFun w := ∏ i, ((w i ^ l i : ℂˣ) : ℂ)
  map_one' := by simp
  map_mul' w w' := by
    simp only [Pi.mul_apply, mul_zpow, Units.val_mul, Finset.prod_mul_distrib]

theorem monomialChar_apply (l : Fin n → ℤ) (w : Fin n → ℂˣ) :
    monomialChar l w = ∏ i, ((w i ^ l i : ℂˣ) : ℂ) := rfl

@[simp]
theorem monomialChar_zero (w : Fin n → ℂˣ) : monomialChar 0 w = 1 := by
  simp [monomialChar_apply]

theorem monomialChar_add (l l' : Fin n → ℤ) (w : Fin n → ℂˣ) :
    monomialChar (l + l') w = monomialChar l w * monomialChar l' w := by
  simp only [monomialChar_apply, Pi.add_apply, zpow_add, Units.val_mul, Finset.prod_mul_distrib]

def pointHom (w : Fin n → ℂˣ) : Multiplicative (Fin n → ℤ) →* ℂ where
  toFun l := monomialChar (Multiplicative.toAdd l) w
  map_one' := by simp [monomialChar_apply]
  map_mul' l l' := by
    simp only [toAdd_mul, monomialChar_apply, Pi.add_apply, zpow_add, Units.val_mul,
      Finset.prod_mul_distrib]

def evalAt (w : Fin n → ℂˣ) : LaurentRing n →ₐ[ℂ] ℂ :=
  AddMonoidAlgebra.lift ℂ ℂ (Fin n → ℤ) (pointHom w)

theorem evalAt_single (w : Fin n → ℂˣ) (l : Fin n → ℤ) (c : ℂ) :
    evalAt w (single l c) = c * monomialChar l w := by
  rw [evalAt, AddMonoidAlgebra.lift_single, smul_eq_mul]
  rfl

theorem evalAt_apply (w : Fin n → ℂˣ) (p : LaurentRing n) :
    evalAt w p = p.coeff.sum fun l c => c * monomialChar l w := by
  rw [evalAt, AddMonoidAlgebra.lift_apply]
  rfl

theorem monomialChar_injective : Function.Injective (monomialChar : (Fin n → ℤ) → _) := by
  intro l l' h
  funext i
  have h2 := DFunLike.congr_fun h (Pi.mulSingle i (Units.mk0 (2 : ℂ) two_ne_zero))
  simp only [monomialChar_apply] at h2
  rw [Finset.prod_eq_single i (fun j _ hj => by simp [Pi.mulSingle_eq_of_ne hj])
      (by simp), Finset.prod_eq_single i (fun j _ hj => by simp [Pi.mulSingle_eq_of_ne hj])
      (by simp)] at h2
  simp only [Pi.mulSingle_eq_same, Units.val_zpow_eq_zpow_val, Units.val_mk0] at h2
  have hn : ‖(2 : ℂ) ^ l i‖ = ‖(2 : ℂ) ^ l' i‖ := by rw [h2]
  rw [norm_zpow, norm_zpow, Complex.norm_two] at hn
  exact zpow_right_injective₀ (by norm_num : (0 : ℝ) < 2) (by norm_num) hn

theorem eq_zero_of_forall_evalAt {p : LaurentRing n} (h : ∀ w, evalAt w p = 0) : p = 0 := by
  have hli : LinearIndependent ℂ (fun l : Fin n → ℤ => ((monomialChar l : (Fin n → ℂˣ) →* ℂ) :
      (Fin n → ℂˣ) → ℂ)) :=
    (linearIndependent_monoidHom (Fin n → ℂˣ) ℂ).comp _ monomialChar_injective
  have hz : Finsupp.linearCombination ℂ (fun l : Fin n → ℤ =>
      ((monomialChar l : (Fin n → ℂˣ) →* ℂ) : (Fin n → ℂˣ) → ℂ)) p.coeff =
      Finsupp.linearCombination ℂ (fun l : Fin n → ℤ =>
      ((monomialChar l : (Fin n → ℂˣ) →* ℂ) : (Fin n → ℂˣ) → ℂ)) 0 := by
    rw [map_zero]
    funext w
    rw [Finsupp.linearCombination_apply, Pi.zero_apply, ← h w, evalAt_apply, Finsupp.sum,
      Finsupp.sum, Finset.sum_apply]
    rfl
  exact AddMonoidAlgebra.coeff_eq_zero.1 (hli hz)

theorem eq_of_forall_evalAt {p q : LaurentRing n} (h : ∀ w, evalAt w p = evalAt w q) : p = q :=
  sub_eq_zero.1 (eq_zero_of_forall_evalAt fun w => by rw [map_sub, h, sub_self])

theorem exists_eq_evalAt (ψ : LaurentRing n →ₐ[ℂ] ℂ) : ∃ w : Fin n → ℂˣ, ψ = evalAt w := by
  set M : Multiplicative (Fin n → ℤ) →* ℂ := (AddMonoidAlgebra.lift ℂ ℂ (Fin n → ℤ)).symm ψ
  let U : Multiplicative (Fin n → ℤ) →* ℂˣ := M.toHomUnits
  set w : Fin n → ℂˣ := fun i => U (Multiplicative.ofAdd (Pi.single i 1))
  refine ⟨w, ?_⟩
  have hl : ∀ l : Multiplicative (Fin n → ℤ),
      l = ∏ i, (Multiplicative.ofAdd (Pi.single i 1 : Fin n → ℤ)) ^ (Multiplicative.toAdd l i) := by
    intro l
    apply Multiplicative.toAdd.injective
    rw [toAdd_prod]
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hM : M = pointHom w := by
    refine MonoidHom.ext fun l => ?_
    have h1 : M l = (U l : ℂ) := rfl
    rw [h1]
    conv_lhs => rw [hl l]
    rw [map_prod, Units.coe_prod]
    simp only [map_zpow]
    rfl
  rw [evalAt, ← hM, Equiv.apply_symm_apply]

instance : Algebra.FiniteType ℂ (LaurentRing n) := by
  infer_instance

theorem exists_ker_evalAt_comp_eq {A : Type*} [CommRing A] [Algebra ℂ A]
    (Φ : A →ₐ[ℂ] LaurentRing n) (hΦ : Function.Injective Φ)
    [hint : Algebra.IsIntegral Φ.range (LaurentRing n)] (I : Ideal A) [hI : I.IsMaximal] :
    ∃ w : Fin n → ℂˣ, RingHom.ker ((evalAt w).comp Φ) = I := by
  let e : A ≃ₐ[ℂ] Φ.range := AlgEquiv.ofInjective Φ hΦ
  let P : Ideal Φ.range := I.comap (e.symm : Φ.range →+* A)
  haveI : P.IsMaximal := Ideal.comap_isMaximal_of_surjective _ e.symm.surjective
  have hP : RingHom.ker (algebraMap Φ.range (LaurentRing n)) ≤ P := by
    intro x hx
    have : x = 0 := Subtype.ext hx
    rw [this]
    exact P.zero_mem
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral P hP
  letI := Ideal.Quotient.field Q
  haveI : Algebra.FiniteType ℂ (LaurentRing n ⧸ Q) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ Q)
      (Ideal.Quotient.mkₐ_surjective ℂ Q)
  haveI := finite_of_finite_type_of_isJacobsonRing ℂ (LaurentRing n ⧸ Q)
  have hbij : Function.Bijective (Algebra.ofId ℂ (LaurentRing n ⧸ Q)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ℂ) (K := LaurentRing n ⧸ Q)
  let e' : ℂ ≃ₐ[ℂ] LaurentRing n ⧸ Q := AlgEquiv.ofBijective (Algebra.ofId ℂ (LaurentRing n ⧸ Q)) hbij
  let ψ : LaurentRing n →ₐ[ℂ] ℂ := e'.symm.toAlgHom.comp (Ideal.Quotient.mkₐ ℂ Q)
  have hker : ∀ p, ψ p = 0 ↔ p ∈ Q := by
    intro p
    simp only [ψ, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
      Ideal.Quotient.mkₐ_eq_mk]
    rw [AlgEquiv.symm_apply_eq, map_zero, Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨w, hw⟩ := exists_eq_evalAt ψ
  refine ⟨w, Ideal.ext fun a => ?_⟩
  rw [RingHom.mem_ker, AlgHom.comp_apply, ← hw, hker]
  have h1 : Φ a = algebraMap Φ.range (LaurentRing n) (e a) := rfl
  rw [h1, ← Ideal.mem_under, hQP]
  change e.symm (e a) ∈ I ↔ a ∈ I
  rw [AlgEquiv.symm_apply_apply]

theorem isIntegral_of_forall (A : Subalgebra ℂ (LaurentRing n))
    (h₁ : ∀ i, IsIntegral A (monomial (Pi.single i 1 : Fin n → ℤ)))
    (h₂ : ∀ i, IsIntegral A (monomial (Pi.single i (-1) : Fin n → ℤ))) :
    Algebra.IsIntegral A (LaurentRing n) := by
  let S : Subalgebra ℂ (LaurentRing n) := (integralClosure A (LaurentRing n)).restrictScalars ℂ
  have hmono : ∀ l : Fin n → ℤ, monomial l ∈ S := by
    intro l
    have hl : monomial l = ∏ i, monomial (Pi.single i (l i) : Fin n → ℤ) := by
      rw [AddMonoidAlgebra.prod_single]
      simp only [Finset.prod_const_one]
      congr 1
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hl]
    refine Subalgebra.prod_mem _ fun i _ => ?_
    rcases le_or_gt 0 (l i) with h | h
    · obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le h
      have : monomial (Pi.single i (l i) : Fin n → ℤ) = monomial (Pi.single i 1) ^ k := by
        rw [AddMonoidAlgebra.single_pow, one_pow, hk, ← Pi.single_smul]
        simp
      rw [this]
      exact Subalgebra.pow_mem _ (h₁ i) k
    · obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (neg_nonneg.2 h.le)
      have : monomial (Pi.single i (l i) : Fin n → ℤ) = monomial (Pi.single i (-1)) ^ k := by
        rw [AddMonoidAlgebra.single_pow, one_pow, ← Pi.single_smul]
        congr 2
        simp only [nsmul_eq_mul, mul_neg, mul_one]
        omega
      rw [this]
      exact Subalgebra.pow_mem _ (h₂ i) k
  refine ⟨fun p => ?_⟩
  have : p ∈ S := by
    rw [← AddMonoidAlgebra.sum_coeff_single p]
    refine Subalgebra.sum_mem _ fun l _ => ?_
    have : (single l (p.coeff l) : LaurentRing n) = p.coeff l • monomial l := by
      rw [AddMonoidAlgebra.smul_single', mul_one]
    rw [this]
    exact Subalgebra.smul_mem _ (hmono l) _
  exact this

end Spherical

end GroundTheory.Automorphic
end
end

section -- merged from GroundTheory.AutomorphicForms.WhittakerRelevance
namespace GroundTheory.Automorphic

namespace Whittaker

open Finset

variable {n : ℕ} {w : Equiv.Perm (Fin n)}

theorem val_eq_of_le_of_le
    (hB : ∀ i j : Fin n, i < j → (w j).val = (w i).val + 1 → j.val = i.val + 1) :
    ∀ (g : ℕ) (z y : Fin n), (w y).val = (w z).val + g → z ≤ y →
      ∀ x : Fin n, z ≤ x → x ≤ y → (w x).val = (w z).val + (x.val - z.val) := by
  intro g
  induction g using Nat.strong_induction_on with
  | _ g ih =>
  intro z y hgap hzy x hzx hxy
  rw [Fin.le_iff_val_le_val] at hzy hzx hxy
  rcases Nat.eq_zero_or_pos g with hg | hg
  · subst hg
    have hyz : y = z := w.injective (Fin.ext (by omega))
    subst hyz
    have hxy' : x = y := Fin.ext (by omega)
    subst hxy'
    simp
  · have hlt : (w z).val + 1 < n := by have := (w y).isLt; omega
    set p := w.symm ⟨(w z).val + 1, hlt⟩ with hp
    have hwp : (w p).val = (w z).val + 1 := by simp [hp]
    have hzy' : z.val < y.val := by
      rcases Nat.lt_or_eq_of_le hzy with h | h
      · exact h
      · have : z = y := Fin.ext h
        subst this
        omega
    rcases lt_trichotomy p.val z.val with hpz | hpz | hpz
    ·
      exfalso
      have key := ih (g - 1) (by omega) p y (by omega) (Fin.le_iff_val_le_val.2 (by omega)) z
        (Fin.le_iff_val_le_val.2 (by omega)) (Fin.le_iff_val_le_val.2 hzy)
      omega
    · exfalso
      have : p = z := Fin.ext hpz
      rw [this] at hwp
      omega
    ·
      have hp1 : p.val = z.val + 1 := hB z p (Fin.lt_def.2 hpz) hwp
      rcases Nat.eq_or_lt_of_le hzx with hx | hx
      · have : x = z := Fin.ext hx.symm
        subst this
        simp
      · have key := ih (g - 1) (by omega) p y (by omega) (Fin.le_iff_val_le_val.2 (by omega)) x
          (Fin.le_iff_val_le_val.2 (by omega)) (Fin.le_iff_val_le_val.2 hxy)
        omega

theorem val_eq_of_le_right
    (hB : ∀ i j : Fin n, i < j → (w j).val = (w i).val + 1 → j.val = i.val + 1) (b x : Fin n)
    (hbx : b ≤ x) (hx : x.val ≤ b.val + #(univ.filter fun y : Fin n => b < y ∧ w b < w y)) :
    (w x).val = (w b).val + (x.val - b.val) := by
  set R := univ.filter fun y : Fin n => b < y ∧ w b < w y with hR
  by_cases hne : R.Nonempty
  · set m := R.max' hne
    have hm : m ∈ R := R.max'_mem hne
    rw [hR, mem_filter] at hm
    have hsub : R ⊆ Ioc b m := by
      intro y hy
      have hy' := hy
      rw [hR, mem_filter] at hy'
      exact mem_Ioc.2 ⟨hy'.2.1, R.le_max' y hy⟩
    have hcard : #R ≤ m.val - b.val := by
      have := card_le_card hsub
      rwa [Fin.card_Ioc] at this
    have hbm := Fin.lt_def.1 hm.2.1
    have hwbm := Fin.lt_def.1 hm.2.2
    exact val_eq_of_le_of_le hB ((w m).val - (w b).val) b m (by omega) (le_of_lt hm.2.1) x hbx
      (Fin.le_iff_val_le_val.2 (by omega))
  · rw [not_nonempty_iff_eq_empty] at hne
    rw [hne, card_empty] at hx
    have : x = b := Fin.ext (by rw [Fin.le_iff_val_le_val] at hbx; omega)
    subst this
    simp

theorem val_add_eq_of_le_left
    (hB : ∀ i j : Fin n, i < j → (w j).val = (w i).val + 1 → j.val = i.val + 1) (b x : Fin n)
    (hxb : x ≤ b) (hx : b.val ≤ x.val + #(univ.filter fun y : Fin n => y < b ∧ w y < w b)) :
    (w x).val + (b.val - x.val) = (w b).val := by
  set L := univ.filter fun y : Fin n => y < b ∧ w y < w b with hL
  by_cases hne : L.Nonempty
  · set m := L.min' hne
    have hm : m ∈ L := L.min'_mem hne
    rw [hL, mem_filter] at hm
    have hsub : L ⊆ Ico m b := by
      intro y hy
      have hy' := hy
      rw [hL, mem_filter] at hy'
      exact mem_Ico.2 ⟨L.min'_le y hy, hy'.2.1⟩
    have hcard : #L ≤ b.val - m.val := by
      have := card_le_card hsub
      rwa [Fin.card_Ico] at this
    have hmb := Fin.lt_def.1 hm.2.1
    have hwmb := Fin.lt_def.1 hm.2.2
    have h1 := val_eq_of_le_of_le hB ((w b).val - (w m).val) m b (by omega) (le_of_lt hm.2.1) x
      (Fin.le_iff_val_le_val.2 (by omega)) hxb
    have h2 := val_eq_of_le_of_le hB ((w b).val - (w m).val) m b (by omega) (le_of_lt hm.2.1) b
      (le_of_lt hm.2.1) le_rfl
    rw [Fin.le_iff_val_le_val] at hxb
    omega
  · rw [not_nonempty_iff_eq_empty] at hne
    rw [hne, card_empty] at hx
    have : x = b := Fin.ext (by rw [Fin.le_iff_val_le_val] at hxb; omega)
    subst this
    simp

theorem card_filter_lt_apply (w : Equiv.Perm (Fin n)) (b : Fin n) :
    #(univ.filter fun x : Fin n => w x < w b) = (w b).val := by
  have : (univ.filter fun x : Fin n => w x < w b) = (Iio (w b)).map w.symm.toEmbedding := by
    ext x
    simp [mem_map_equiv]
  rw [this, card_map, Fin.card_Iio]

theorem val_add_card_right (w : Equiv.Perm (Fin n)) (b : Fin n) :
    (w b).val + #(univ.filter fun y : Fin n => b < y ∧ w b < w y) =
      #(univ.filter fun y : Fin n => y < b ∧ w y < w b) + (n - 1 - b.val) := by
  have hIoi : #(univ.filter fun y : Fin n => b < y) = n - 1 - b.val := by
    have : (univ.filter fun y : Fin n => b < y) = Ioi b := by
      ext y
      simp
    rw [this, Fin.card_Ioi]
  rw [← card_filter_lt_apply w b, ← hIoi, card_filter, card_filter, card_filter, card_filter,
    ← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun y _ => ?_
  have hne : y ≠ b → w y ≠ w b := fun h e => h (w.injective e)
  rcases lt_trichotomy y b with h | h | h
  · have h' : ¬ b < y := not_lt.2 (le_of_lt h)
    by_cases hw : w y < w b <;> simp [h, h', hw]
  · subst h
    simp
  · have h' : ¬ y < b := not_lt.2 (le_of_lt h)
    have hyb : w y ≠ w b := hne (ne_of_gt h)
    rcases lt_or_gt_of_ne hyb with hw | hw
    · have hw' : ¬ w b < w y := not_lt.2 (le_of_lt hw)
      simp [h, h', hw, hw']
    · have hw' : ¬ w y < w b := not_lt.2 (le_of_lt hw)
      simp [h, h', hw, hw']

theorem relevant_involution
    (hB : ∀ i j : Fin n, i < j → (w j).val = (w i).val + 1 → j.val = i.val + 1) (b : Fin n) :
    w (Fin.rev (w b)) = Fin.rev b := by
  have hid := val_add_card_right w b
  set r := #(univ.filter fun y : Fin n => b < y ∧ w b < w y)
  set l := #(univ.filter fun y : Fin n => y < b ∧ w y < w b)
  set c := Fin.rev (w b) with hc
  have hcv : c.val = n - (↑(w b) + 1) := by rw [hc, Fin.val_rev]
  have hb := b.isLt
  have hwb := (w b).isLt
  apply Fin.ext
  rw [Fin.val_rev]
  by_cases hcb : b.val ≤ c.val
  · have := val_eq_of_le_right hB b c (Fin.le_iff_val_le_val.2 hcb) (by omega)
    omega
  · have := val_add_eq_of_le_left hB b c (Fin.le_iff_val_le_val.2 (by omega)) (by omega)
    omega

theorem apply_eq_of_run_right {α : Type*} (t : Fin n → α)
    (hB : ∀ i j : Fin n, i < j → (w j).val = (w i).val + 1 → j.val = i.val + 1)
    (ht : ∀ (i : Fin n) (h : i.val + 1 < n), w i < w ⟨i.val + 1, h⟩ →
      t (w i) = t (w ⟨i.val + 1, h⟩))
    (b : Fin n) :
    ∀ k : ℕ, ∀ x : Fin n, x.val = b.val + k →
      k ≤ #(univ.filter fun y : Fin n => b < y ∧ w b < w y) → t (w x) = t (w b) := by
  intro k
  induction k with
  | zero =>
    intro x hx _
    have : x = b := Fin.ext (by omega)
    rw [this]
  | succ k ih =>
    intro x hx hk
    have hxn := x.isLt
    have hk1 : b.val + k < n := by omega
    have h1 := ih ⟨b.val + k, hk1⟩ rfl (by omega)
    have e1 := val_eq_of_le_right hB b x (Fin.le_iff_val_le_val.2 (by omega)) (by omega)
    have e2 := val_eq_of_le_right hB b ⟨b.val + k, hk1⟩ (Fin.le_iff_val_le_val.2 (by simp))
      (by simp; omega)
    have hk2 : b.val + k + 1 < n := by omega
    have hnext : (⟨b.val + k + 1, hk2⟩ : Fin n) = x := Fin.ext (by simp; omega)
    have hasc : w ⟨b.val + k, hk1⟩ < w ⟨b.val + k + 1, hk2⟩ := by
      rw [hnext, Fin.lt_def]
      simp only at e2
      omega
    have := ht ⟨b.val + k, hk1⟩ hk2 hasc
    simp only at this
    rw [hnext] at this
    rw [← this, h1]

theorem apply_eq_of_run_left {α : Type*} (t : Fin n → α)
    (hB : ∀ i j : Fin n, i < j → (w j).val = (w i).val + 1 → j.val = i.val + 1)
    (ht : ∀ (i : Fin n) (h : i.val + 1 < n), w i < w ⟨i.val + 1, h⟩ →
      t (w i) = t (w ⟨i.val + 1, h⟩))
    (b : Fin n) :
    ∀ k : ℕ, ∀ x : Fin n, x.val + k = b.val →
      k ≤ #(univ.filter fun y : Fin n => y < b ∧ w y < w b) → t (w x) = t (w b) := by
  intro k
  induction k with
  | zero =>
    intro x hx _
    have : x = b := Fin.ext (by omega)
    rw [this]
  | succ k ih =>
    intro x hx hk
    have hbn := b.isLt
    have hx1 : x.val + 1 < n := by omega
    have h1 := ih ⟨x.val + 1, hx1⟩ (by simp; omega) (by omega)
    have e1 := val_add_eq_of_le_left hB b x (Fin.le_iff_val_le_val.2 (by omega)) (by omega)
    have e2 := val_add_eq_of_le_left hB b ⟨x.val + 1, hx1⟩ (Fin.le_iff_val_le_val.2 (by simp; omega))
      (by simp; omega)
    have hasc : w x < w ⟨x.val + 1, hx1⟩ := by
      rw [Fin.lt_def]
      simp only at e2
      omega
    have := ht x hx1 hasc
    rw [this]
    exact h1

theorem relevant_torus {α : Type*} (t : Fin n → α)
    (hB : ∀ i j : Fin n, i < j → (w j).val = (w i).val + 1 → j.val = i.val + 1)
    (ht : ∀ (i : Fin n) (h : i.val + 1 < n), w i < w ⟨i.val + 1, h⟩ →
      t (w i) = t (w ⟨i.val + 1, h⟩))
    (b : Fin n) : t (w b) = t (Fin.rev b) := by
  have hid := val_add_card_right w b
  rw [← relevant_involution hB b]
  set c := Fin.rev (w b) with hc
  have hcv : c.val = n - (↑(w b) + 1) := by rw [hc, Fin.val_rev]
  have hb := b.isLt
  have hwb := (w b).isLt
  by_cases hcb : b.val ≤ c.val
  · exact (apply_eq_of_run_right t hB ht b (c.val - b.val) c (by omega) (by omega)).symm
  · exact (apply_eq_of_run_left t hB ht b (b.val - c.val) c (by omega) (by omega)).symm

end Whittaker

end GroundTheory.Automorphic
end
