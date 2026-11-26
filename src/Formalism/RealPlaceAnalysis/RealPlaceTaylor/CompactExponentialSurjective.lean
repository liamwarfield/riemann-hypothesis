module

public import Formalism.RealPlaceAnalysis.SmoothOnGVIff
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IndefiniteUnitaryPreservesForm
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CartanInvolutionConjTransposeMul

@[expose] public section

section -- merged from Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactExponentialSurjective
open Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section
namespace Formalism.REAL

lemma norm_log_sq_le_unit_circle (z : ℂ) (hz : ‖z‖ = 1) : ‖Complex.log z‖ ^ 2 ≤ 3 * ‖z - 1‖ ^ 2 := by
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp at hz
  set θ := Complex.arg z with hθ
  have hre : z.re = Real.cos θ := by rw [Complex.cos_arg hz0, hz, div_one]
  have him : z.im = Real.sin θ := by rw [Complex.sin_arg, hz, div_one]
  have hlog : ‖Complex.log z‖ ^ 2 = θ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.log_re, Complex.log_im, hz, Real.log_one]
    ring
  have hc : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
    have h1 := Real.cos_sq_add_sin_sq (θ / 2)
    have h2 := Real.cos_two_mul (θ / 2)
    rw [show 2 * (θ / 2) = θ by ring] at h2
    linarith
  have hsub : ‖z - 1‖ ^ 2 = 4 * Real.sin (θ / 2) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im, hre, him]
    linear_combination Real.cos_sq_add_sin_sq θ - 2 * hc
  have key : ∀ y : ℝ, 0 ≤ y → y ≤ Real.pi / 2 → 4 * y ^ 2 ≤ 12 * Real.sin y ^ 2 := by
    intro y hy0 hy1
    have hs := Real.mul_le_sin hy0 hy1
    have hpi0 := Real.pi_pos
    have hpi : Real.pi ^ 2 ≤ 12 := by nlinarith [Real.pi_lt_d2]
    have ha0 : 0 ≤ 2 / Real.pi * y := by positivity
    have h1 : (2 / Real.pi * y) ^ 2 ≤ Real.sin y ^ 2 := pow_le_pow_left₀ ha0 hs 2
    have h2 : 4 * y ^ 2 = Real.pi ^ 2 * (2 / Real.pi * y) ^ 2 := by
      field_simp
      ring
    rw [h2]
    nlinarith [sq_nonneg (2 / Real.pi * y)]
  have hb : |θ| ≤ Real.pi := abs_le.2 ⟨(Complex.neg_pi_lt_arg z).le, Complex.arg_le_pi z⟩
  rw [hlog, hsub]
  rcases le_or_gt 0 θ with h | h
  · have := key (θ / 2) (by linarith) (by rw [abs_of_nonneg h] at hb; linarith)
    nlinarith
  · have := key (-(θ / 2)) (by linarith) (by rw [abs_of_neg h] at hb; linarith)
    rw [Real.sin_neg, neg_sq, neg_sq] at this
    nlinarith

lemma frobenius_eq_trace {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    ((hs A : ℝ) : ℂ) = (star A * A).trace := by
  simp only [hs, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.star_apply]
  push_cast
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.conj_mul']

lemma frobenius_nonneg_matrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ hs A := by
  unfold hs
  positivity

lemma compact_exists_log_bounded {n : ℕ} (ε : Fin n → Bool) (k : Matrix (Fin n) (Fin n) ℂ) (hk : k ∈ Kset ε) :
    ∃ Y : Matrix (Fin n) (Fin n) ℂ, inK ε Y ∧ NormedSpace.exp Y = k ∧ hs Y ≤ 3 * hs (k - 1) := by
  obtain ⟨hu, hJ⟩ := hk
  have hN : IsStarNormal k := isStarNormal_of_mem_unitary hu
  have hcont : ∀ f : ℂ → ℂ, ContinuousOn f (spectrum ℂ k) :=
    fun f => (Matrix.finite_spectrum k).continuousOn f
  have hcirc : ∀ z ∈ spectrum ℂ k, ‖z‖ = 1 := fun z hz => spectrum.norm_eq_one_of_unitary hu hz
  have hJs : star (Jm ε) = Jm ε := by rw [Matrix.star_eq_conjTranspose, Jm_conjTranspose]
  have hstarJ : star k * Jm ε = Jm ε * star k := by
    have := congrArg star hJ
    simp only [star_mul, hJs] at this
    exact this.symm
  set Y := cfc Complex.log k with hY
  have hcomm : Commute Y (Jm ε) := Commute.cfc hJ hstarJ Complex.log
  have hstarY : star Y = -Y := by
    rw [hY, ← cfc_star, ← cfc_neg Complex.log k]
    refine cfc_congr fun z hz => ?_
    have h1 := hcirc z hz
    apply Complex.ext <;> simp [Complex.log_re, Complex.log_im, h1]
  refine ⟨Y, ⟨?_, hcomm.eq⟩, ?_, ?_⟩
  · show Yᴴ * Jm ε + Jm ε * Y = 0
    rw [← Matrix.star_eq_conjTranspose, hstarY, neg_mul, hcomm.eq]
    exact neg_add_cancel _
  · rw [← CFC.complex_exp_eq_normedSpace_exp, hY,
      ← cfc_comp Complex.exp Complex.log k (hg := Complex.continuous_exp.continuousOn) (hf := hcont _)]
    rw [cfc_congr (g := id) (fun z hz => by
      have h1 := hcirc z hz
      have h0 : z ≠ 0 := by
        rintro rfl
        simp at h1
      simp [Complex.exp_log h0])]
    exact cfc_id ℂ k
  · (have hF : cfc (fun z => 3 * (star (z - 1) * (z - 1)) - star (Complex.log z) * Complex.log z) k =
        (3 : ℂ) • (star (k - 1) * (k - 1)) - star Y * Y := by
       rw [cfc_sub (fun z => 3 * (star (z - 1) * (z - 1))) (fun z => star (Complex.log z) * Complex.log z) k
         (hcont _) (hcont _)]
       rw [cfc_const_mul 3 (fun z => star (z - 1) * (z - 1)) k (hcont _)]
       rw [cfc_mul (fun z => star (z - 1)) (fun z => z - 1) k (hcont _) (hcont _)]
       rw [cfc_mul (fun z => star (Complex.log z)) Complex.log k (hcont _) (hcont _)]
       rw [cfc_star (fun z => z - 1) k, cfc_star Complex.log k]
       rw [cfc_sub (fun z => z) (fun _ => 1) k (hcont _) (hcont _), cfc_id' ℂ k, cfc_const_one ℂ k]
     set G := cfc (fun z => ((Real.sqrt (3 * ‖z - 1‖ ^ 2 - ‖Complex.log z‖ ^ 2) : ℝ) : ℂ)) k with hG
     have hFG : cfc (fun z => 3 * (star (z - 1) * (z - 1)) - star (Complex.log z) * Complex.log z) k =
         star G * G := by
       rw [hG, ← cfc_star, ← cfc_mul _ _ k (hcont _) (hcont _)]
       refine cfc_congr fun z hz => ?_
       have hsc := norm_log_sq_le_unit_circle z (hcirc z hz)
       have hnn : 0 ≤ 3 * ‖z - 1‖ ^ 2 - ‖Complex.log z‖ ^ 2 := by linarith
       simp only [Complex.star_def, Complex.conj_ofReal]
       rw [Complex.conj_mul', Complex.conj_mul', ← Complex.ofReal_mul, Real.mul_self_sqrt hnn]
       push_cast
       ring
     have htr := congrArg Matrix.trace (hF.symm.trans hFG)
     rw [Matrix.trace_sub, Matrix.trace_smul, ← frobenius_eq_trace, ← frobenius_eq_trace, ← frobenius_eq_trace,
       smul_eq_mul] at htr
     have h4 : (3 : ℂ) * (hs (k - 1) : ℂ) - (hs Y : ℂ) = ((3 * hs (k - 1) - hs Y : ℝ) : ℂ) := by push_cast; ring
     rw [h4] at htr
     have h5 := Complex.ofReal_injective htr
     have h6 := frobenius_nonneg_matrix G
     linarith)

theorem compact_exponential_surjective : KExp := fun _ ε k hk => compact_exists_log_bounded ε k hk

theorem genExp_of (h : KExp) : GenExp := by
  intro n ε g hg
  obtain ⟨k, X, hk, hX, rfl⟩ := (polar_decomposition_holds n ε).1 g hg
  obtain ⟨Z, hZ, hZk, -⟩ := h n ε k hk
  exact ⟨Z, X, hZ, hX, by rw [hZk]⟩

end Formalism.REAL
end
end

section -- merged from Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactHaarRightInvariantInst
open Matrix MeasureTheory MeasureTheory.Measure

noncomputable section

namespace Formalism.REAL

section P0KLinfty
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

lemma continuous_exp_real_smul {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    Continuous (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) := by
  exact NormedSpace.exp_continuous.comp (by fun_prop)

end P0KLinfty

lemma toM_injective' {n : ℕ} {ε : Fin n → Bool} {g h : UJ ε} (hgh : toM g = toM h) : g = h := by
  exact Subtype.ext (Units.ext hgh)

theorem group_exponential_facts : ExpGFacts := by
  intro n ε X hX
  have hE : ∀ t : ℝ, toM (expG ε X t) = NormedSpace.exp ((t : ℂ) • X) := fun t => toM_expG ε X t hX
  have hcont : Continuous (fun t : ℝ => expG ε X t) := by
    have hcU : Continuous (fun t : ℝ => ((expG ε X t : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ)) := by
      rw [Units.continuous_iff]
      refine ⟨?_, ?_⟩
      · have h1 : (Units.val ∘ fun t : ℝ => ((expG ε X t : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ)) =
            fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) := funext hE
        rw [h1]
        exact continuous_exp_real_smul X
      · have h2 : (fun t : ℝ => ((((expG ε X t : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ)⁻¹ :
            (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) =
            fun t : ℝ => NormedSpace.exp (((-t : ℝ) : ℂ) • X) := by
          funext t
          apply Units.inv_eq_of_mul_eq_one_right
          show toM (expG ε X t) * _ = 1
          rw [hE, ← Matrix.exp_add_of_commute _ _
            (((Commute.refl X).smul_left ((t : ℝ) : ℂ)).smul_right (((-t : ℝ)) : ℂ)), ← add_smul]
          push_cast
          rw [add_neg_cancel, zero_smul, NormedSpace.exp_zero]
        rw [h2]
        exact (continuous_exp_real_smul X).comp continuous_neg
    exact continuous_induced_rng.2 hcU
  refine ⟨?_, ?_, hcont, ?_⟩
  · apply toM_injective'
    rw [hE]
    simp
    rfl
  · intro s t
    apply toM_injective'
    show toM (expG ε X (s + t)) = toM (expG ε X s) * toM (expG ε X t)
    rw [hE, hE, hE, ← Matrix.exp_add_of_commute _ _
      (((Commute.refl X).smul_left ((s : ℝ) : ℂ)).smul_right ((t : ℝ) : ℂ))]
    congr 1
    push_cast
    rw [add_smul]
  · intro hK
    have hk : ∀ t : ℝ, ((expK ε X t : KG ε) : UJ ε) = expG ε X t := by
      intro t
      unfold expK
      rw [dite_eq_left hK]
    refine ⟨hk, ?_⟩
    apply continuous_induced_rng.2
    have h3 : (Subtype.val ∘ fun t : ℝ => expK ε X t) = fun t : ℝ => expG ε X t := funext hk
    rw [h3]
    exact hcont

lemma compact_haar_probability (n : ℕ) (ε : Fin n → Bool) : IsProbabilityMeasure (muK ε) := by
  unfold muK
  constructor
  have h := MeasureTheory.Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts (KG ε)))
  rwa [TopologicalSpace.PositiveCompacts.coe_top] at h

instance compact_haar_probability_inst (n : ℕ) (ε : Fin n → Bool) : IsProbabilityMeasure (muK ε) := compact_haar_probability n ε

lemma compact_haar_unique_left {n : ℕ} {ε : Fin n → Bool} (ν : Measure (KG ε)) [IsMulLeftInvariant ν]
    [IsProbabilityMeasure ν] : ν = muK ε := by
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ)ᵐᵒᵖ :=
    TopologicalSpace.secondCountableTopology_induced _ _ MulOpposite.unop
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ)ˣ :=
    TopologicalSpace.secondCountableTopology_induced _ _ (Units.embedProduct _)
  haveI : SecondCountableTopology (UJ ε) :=
    TopologicalSpace.Subtype.secondCountableTopology (UJ ε : Set (Matrix (Fin n) (Fin n) ℂ)ˣ)
  haveI : SecondCountableTopology (KG ε) :=
    TopologicalSpace.Subtype.secondCountableTopology (KG ε : Set (UJ ε))
  have h := MeasureTheory.Measure.haarMeasure_unique ν (⊤ : TopologicalSpace.PositiveCompacts (KG ε))
  rw [h, TopologicalSpace.PositiveCompacts.coe_top, measure_univ, one_smul]
  rfl

lemma compact_haar_right_invariant (n : ℕ) (ε : Fin n → Bool) (k : KG ε) :
    Measure.map (fun x => x * k) (muK ε) = muK ε := by
  haveI : IsMulLeftInvariant (muK ε) := by
    unfold muK
    infer_instance
  have hm : Measurable (fun x : KG ε => x * k) := measurable_mul_const k
  haveI : IsProbabilityMeasure (Measure.map (fun x => x * k) (muK ε)) :=
    inferInstance
  haveI : IsMulLeftInvariant (Measure.map (fun x => x * k) (muK ε)) := by
    constructor
    intro g
    rw [Measure.map_map (measurable_const_mul g) hm]
    have e : ((g * ·) ∘ (· * k)) = ((· * k) ∘ (g * ·) : KG ε → KG ε) := by
      funext x
      simp [mul_assoc]
    rw [e, ← Measure.map_map hm (measurable_const_mul g), map_mul_left_eq_self]
  exact compact_haar_unique_left _

instance compact_haar_right_invariant_inst (n : ℕ) (ε : Fin n → Bool) : IsMulRightInvariant (muK ε) :=
  ⟨fun k => compact_haar_right_invariant n ε k⟩

theorem compact_haar_holds : KHaar := by
  intro n ε
  haveI : IsMulLeftInvariant (muK ε) := by
    unfold muK
    infer_instance
  refine ⟨compact_haar_probability n ε, fun k => map_mul_left_eq_self _ k, fun k => compact_haar_right_invariant n ε k, ?_⟩
  haveI : IsProbabilityMeasure (Measure.map (fun x : KG ε => x⁻¹) (muK ε)) :=
    inferInstance
  haveI : IsMulLeftInvariant (Measure.map (fun x : KG ε => x⁻¹) (muK ε)) := by
    constructor
    intro g
    rw [Measure.map_map (measurable_const_mul g) measurable_inv]
    have e : ((g * ·) ∘ (fun x : KG ε => x⁻¹)) = ((fun x : KG ε => x⁻¹) ∘ (· * g⁻¹)) := by
      funext x
      simp
    rw [e, ← Measure.map_map measurable_inv (measurable_mul_const g⁻¹), compact_haar_right_invariant]
  exact compact_haar_unique_left _

theorem compact_integration_by_parts : KByParts := by
  intro n ε E _ _ _ F D Z hZ hF hD hder
  haveI : IsMulRightInvariant (muK ε) := ⟨fun g => compact_haar_right_invariant n ε g⟩
  haveI : IsProbabilityMeasure (muK ε) := compact_haar_probability n ε
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ)ᵐᵒᵖ :=
    TopologicalSpace.secondCountableTopology_induced _ _ MulOpposite.unop
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ)ˣ :=
    TopologicalSpace.secondCountableTopology_induced _ _ (Units.embedProduct _)
  haveI : SecondCountableTopology (UJ ε) :=
    TopologicalSpace.Subtype.secondCountableTopology (UJ ε : Set (Matrix (Fin n) (Fin n) ℂ)ˣ)
  haveI : SecondCountableTopology (KG ε) :=
    TopologicalSpace.Subtype.secondCountableTopology (KG ε : Set (UJ ε))
  obtain ⟨h0, hadd, -, hKf⟩ := group_exponential_facts n ε Z hZ.1
  obtain ⟨hk, -⟩ := hKf hZ
  have hhom : ∀ s t : ℝ, expK ε Z (s + t) = expK ε Z s * expK ε Z t := by
    intro s t
    apply Subtype.ext
    rw [Subgroup.coe_mul, hk, hk, hk, hadd]
  have hzero : expK ε Z 0 = 1 := by
    apply Subtype.ext
    exact (hk 0).trans h0
  have hderiv : ∀ (k : KG ε) (t : ℝ),
      HasDerivAt (fun s => F (k * expK ε Z s)) (D (k * expK ε Z t)) t := by
    intro k t
    have h := hder (k * expK ε Z t)
    rw [← sub_self t] at h
    have e : (fun s => F (k * expK ε Z s)) = fun s => F (k * expK ε Z t * expK ε Z (s - t)) := by
      funext s
      rw [mul_assoc, ← hhom, add_sub_cancel]
    rw [e]
    exact h.comp_sub_const t t
  obtain ⟨C, hC⟩ : ∃ C, ∀ y : KG ε, ‖D y‖ ≤ C := by
    obtain ⟨C, hC⟩ := (isCompact_univ.image hD.norm).bddAbove
    exact ⟨C, fun y => hC ⟨y, Set.mem_univ _, rfl⟩⟩
  obtain ⟨CF, hCF⟩ : ∃ C, ∀ y : KG ε, ‖F y‖ ≤ C := by
    obtain ⟨C, hC⟩ := (isCompact_univ.image hF.norm).bddAbove
    exact ⟨C, fun y => hC ⟨y, Set.mem_univ _, rfl⟩⟩
  have hcomp : ∀ t : ℝ, Continuous (fun k : KG ε => k * expK ε Z t) := fun t =>
    continuous_id.mul continuous_const
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := muK ε) (x₀ := (0 : ℝ))
    (F := fun t k => F (k * expK ε Z t)) (F' := fun t k => D (k * expK ε Z t))
    (bound := fun _ => C) (s := Set.univ) Filter.univ_mem
    (Filter.Eventually.of_forall fun t => (hF.comp (hcomp t)).aestronglyMeasurable)
    (Integrable.mono' (integrable_const CF) (hF.comp (hcomp 0)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun k => hCF _))
    (hD.comp (hcomp 0)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun k t _ => hC _)
    (integrable_const C)
    (Filter.Eventually.of_forall fun k t _ => hderiv k t)
  have hconst : (fun t : ℝ => ∫ k, F (k * expK ε Z t) ∂(muK ε)) = fun _ => ∫ k, F k ∂(muK ε) := by
    funext t
    exact integral_mul_right_eq_self F (expK ε Z t)
  have h2 : HasDerivAt (fun _ : ℝ => ∫ k, F k ∂(muK ε)) (∫ k, D (k * expK ε Z 0) ∂(muK ε)) 0 := by
    rw [← hconst]
    exact key.2
  have h3 := h2.unique (hasDerivAt_const (0 : ℝ) (∫ k, F k ∂(muK ε)))
  simp only [hzero, mul_one] at h3
  exact h3

end Formalism.REAL
end
end

section -- merged from Formalism.RealPlaceAnalysis.RealPlaceTaylor.LieOperatorConjHolds
open Matrix Finset
open scoped ContDiff

noncomputable section

namespace Formalism.REAL

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

lemma p0auxiliary_rdV_neg {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (X : Matrix (Fin n) (Fin n) ℂ) (f : Matrix (Fin n) (Fin n) ℂ → E) (g : Matrix (Fin n) (Fin n) ℂ) :
    RdV (-X) f g = -RdV X f g := by
  have key := deriv_comp_neg (f := fun s : ℝ => f (g * NormedSpace.exp ((s : ℂ) • X))) (x := (0 : ℝ))
  simp only [neg_zero, Complex.ofReal_neg, neg_smul] at key
  simp only [RdV, smul_neg]
  exact key

lemma p0auxiliary_theta_single {n : ℕ} (ε : Fin n → Bool) (a b : Fin n) :
    Jm ε * (Matrix.single a b (1 : ℂ))ᴴ * Jm ε = (sgn ε a b : ℂ) • Matrix.single b a 1 := by
  ext i j
  simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply,
    Matrix.smul_apply, Matrix.single_apply, sgn, smul_eq_mul]
  push_cast
  split_ifs <;> simp_all

private lemma Jm_mul_selfRealPlaceTaylor {n : ℕ} (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  rw [Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

private lemma conjTranspose_Jm {n : ℕ} (ε : Fin n → Bool) : (Jm ε)ᴴ = Jm ε := by
  rw [Jm, Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  split_ifs <;> simp_all

private lemma Jm_mul_conjTranspose_smul_mul_Jm {n : ℕ} (ε : Fin n → Bool) (c : ℂ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    Jm ε * (c • Z)ᴴ * Jm ε = star c • (Jm ε * Zᴴ * Jm ε) := by
  rw [Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul]

private lemma inG_cpart1_real_place_taylor {n : ℕ} (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    inG ε (cpart1 ε Z) := by
  have hAH : (Jm ε * Zᴴ * Jm ε)ᴴ = Jm ε * Z * Jm ε := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      conjTranspose_Jm, Matrix.mul_assoc]
  have h1 : Jm ε * Z * Jm ε * Jm ε = Jm ε * Z := by
    rw [Matrix.mul_assoc, Jm_mul_selfRealPlaceTaylor, Matrix.mul_one]
  have h2 : Jm ε * (Jm ε * Zᴴ * Jm ε) = Zᴴ * Jm ε := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Jm_mul_selfRealPlaceTaylor, Matrix.one_mul]
  rw [inG, cpart1, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, hAH, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, h1, h2]
  simp <;> module

lemma p0auxiliary_cpart1_add {n : ℕ} (ε : Fin n → Bool) (Z W : Matrix (Fin n) (Fin n) ℂ) :
    cpart1 ε (Z + W) = cpart1 ε Z + cpart1 ε W := by
  rw [cpart1, cpart1, cpart1, Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul, ← smul_add]
  congr 1
  abel

lemma p0auxiliary_cpart2_add {n : ℕ} (ε : Fin n → Bool) (Z W : Matrix (Fin n) (Fin n) ℂ) :
    cpart2 ε (Z + W) = cpart2 ε Z + cpart2 ε W := by
  rw [cpart2, cpart2, cpart2, Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul, ← smul_add]
  congr 1
  abel

lemma p0auxiliary_cpart1_real {n : ℕ} (ε : Fin n → Bool) (x : ℝ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    cpart1 ε ((x : ℂ) • Z) = (x : ℂ) • cpart1 ε Z := by
  have hx : star (x : ℂ) = x := Complex.conj_ofReal x
  rw [cpart1, cpart1, Jm_mul_conjTranspose_smul_mul_Jm, hx, ← smul_sub, smul_comm]

lemma p0auxiliary_cpart2_real {n : ℕ} (ε : Fin n → Bool) (x : ℝ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    cpart2 ε ((x : ℂ) • Z) = (x : ℂ) • cpart2 ε Z := by
  have hx : star (x : ℂ) = x := Complex.conj_ofReal x
  rw [cpart2, cpart2, Jm_mul_conjTranspose_smul_mul_Jm, hx, ← smul_add, smul_comm]

lemma p0auxiliary_half_I : (1 / (2 * Complex.I) : ℂ) = -(1 / 2) * Complex.I := by
  rw [one_div, mul_inv, Complex.inv_I]
  ring

lemma p0auxiliary_cpart1_I {n : ℕ} (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    cpart1 ε (Complex.I • Z) = -cpart2 ε Z := by
  have hI : star Complex.I = -Complex.I := Complex.conj_I
  rw [cpart1, cpart2, Jm_mul_conjTranspose_smul_mul_Jm, hI, p0auxiliary_half_I]
  module

private lemma inG_cpart2_real_place_taylor {n : ℕ} (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    inG ε (cpart2 ε Z) := by
  have h := inG_cpart1_real_place_taylor ε (Complex.I • Z)
  rw [p0auxiliary_cpart1_I] at h
  rw [inG] at h ⊢
  rw [Matrix.conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, ← neg_add] at h
  exact neg_eq_zero.mp h

lemma p0auxiliary_cpart2_I {n : ℕ} (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    cpart2 ε (Complex.I • Z) = cpart1 ε Z := by
  have hI : star Complex.I = -Complex.I := Complex.conj_I
  have k1 : (-(1 / 2) * Complex.I) * Complex.I = 1 / 2 := by
    linear_combination (-(1 / 2) : ℂ) * Complex.I_sq
  have k2 : (-(1 / 2) * Complex.I) * -Complex.I = -(1 / 2) := by
    linear_combination ((1 / 2) : ℂ) * Complex.I_sq
  rw [cpart2, cpart1, Jm_mul_conjTranspose_smul_mul_Jm, hI, p0auxiliary_half_I, smul_add, smul_smul, smul_smul, k1, k2]
  module

section EcV
variable (hl : RdLinV) {n : ℕ} {ε : Fin n → Bool} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f : Matrix (Fin n) (Fin n) ℂ → E} {g : Matrix (Fin n) (Fin n) ℂ}
include hl

lemma p0auxiliary_ecV_add (hf : SmoothOnGV ε f) (hg : inUJ ε g) (Z W : Matrix (Fin n) (Fin n) ℂ) :
    EcV ε (Z + W) f g = EcV ε Z f g + EcV ε W f g := by
  have H := hl
  unfold RdLinV at H
  simp only [EcV]
  rw [p0auxiliary_cpart1_add, p0auxiliary_cpart2_add,
    (H n ε E f f _ _ 0 0 g hf hf (inG_cpart1_real_place_taylor ε Z) (inG_cpart1_real_place_taylor ε W) hg).1,
    (H n ε E f f _ _ 0 0 g hf hf (inG_cpart2_real_place_taylor ε Z) (inG_cpart2_real_place_taylor ε W) hg).1, smul_add]
  abel

lemma p0auxiliary_ecV_real (hf : SmoothOnGV ε f) (hg : inUJ ε g) (x : ℝ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    EcV ε ((x : ℂ) • Z) f g = (x : ℂ) • EcV ε Z f g := by
  have H := hl
  unfold RdLinV at H
  simp only [EcV]
  rw [p0auxiliary_cpart1_real, p0auxiliary_cpart2_real,
    (H n ε E f f _ _ x 0 g hf hf (inG_cpart1_real_place_taylor ε Z) (inG_cpart1_real_place_taylor ε Z) hg).2.1,
    (H n ε E f f _ _ x 0 g hf hf (inG_cpart2_real_place_taylor ε Z) (inG_cpart2_real_place_taylor ε Z) hg).2.1, smul_add,
    smul_comm Complex.I (x : ℂ)]

lemma p0auxiliary_ecV_I (Z : Matrix (Fin n) (Fin n) ℂ) :
    EcV ε (Complex.I • Z) f g = Complex.I • EcV ε Z f g := by
  simp only [EcV]
  rw [p0auxiliary_cpart1_I, p0auxiliary_cpart2_I, p0auxiliary_rdV_neg, smul_add, smul_smul, Complex.I_mul_I,
    neg_one_smul]
  abel

lemma p0auxiliary_ecV_smul (hf : SmoothOnGV ε f) (hg : inUJ ε g) (c : ℂ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    EcV ε (c • Z) f g = c • EcV ε Z f g := by
  have hc : c • Z = (c.re : ℂ) • Z + (c.im : ℂ) • (Complex.I • Z) := by
    rw [smul_smul, ← add_smul, Complex.re_add_im]
  rw [hc, p0auxiliary_ecV_add hl hf hg, p0auxiliary_ecV_real hl hf hg, p0auxiliary_ecV_real hl hf hg,
    p0auxiliary_ecV_I hl, smul_smul, ← add_smul, Complex.re_add_im]

end EcV

theorem ecSumV_of (h : RdLinV) : EcSumV := by
  unfold EcSumV
  intro n ε E _ _ f Z g hf hg
  let L : Matrix (Fin n) (Fin n) ℂ →+ E :=
    AddMonoidHom.mk' (fun Y => EcV ε Y f g) (fun Y W => p0auxiliary_ecV_add h hf hg Y W)
  have hL : ∀ Y, L Y = EcV ε Y f g := fun Y => rfl
  calc EcV ε Z f g = L (∑ a, ∑ b, Matrix.single a b (Z a b)) := by
        rw [hL, ← Matrix.matrix_eq_sum_single Z]
    _ = ∑ a, ∑ b, L (Matrix.single a b (Z a b)) := by simp only [map_sum]
    _ = ∑ a, ∑ b, Z a b • EabV ε a b f g := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        have hs : Matrix.single a b (Z a b) = Z a b • Matrix.single a b (1 : ℂ) := by
          ext i j
          simp [Matrix.single_apply]
        rw [hL, hs, p0auxiliary_ecV_smul h hf hg, EabV]

end Formalism.REAL
end
end
