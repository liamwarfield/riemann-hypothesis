module

public import GroundTheory.HeightsAndTheta.Heights.FubiniStudyIntegral
public import GroundTheory.HeightsAndTheta.Heights.ArithDegreeIdeal
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.TwistingSheaf

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.FubiniStudy
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open scoped LinearAlgebra.Projectivization ContDiff
open MeasureTheory Topology Set MvPolynomial

noncomputable section

variable {N : ℕ}

namespace CP

instance instMeasurableSpace : MeasurableSpace (CP N) := borel (CP N)

instance instBorelSpace : BorelSpace (CP N) := ⟨rfl⟩

def fsChartMeasure (i : Fin (N + 1)) : Measure (Fin N → ℂ) :=
  volume.withDensity fun z => ENNReal.ofReal (fsVolumeDensity i z)

def fsMeasure (N : ℕ) : Measure (CP N) := (fsChartMeasure (N := N) 0).map (chartInv 0)

lemma measurable_chartInv (i : Fin (N + 1)) : Measurable (chartInv (N := N) i) :=
  (continuous_chartInv i).measurable

lemma measurable_fsVolumeDensity (i : Fin (N + 1)) :
    Measurable (fsVolumeDensity (N := N) i) := by
  have : fsVolumeDensity (N := N) i = fun z =>
      N.factorial / (Real.pi ^ N * (1 + normSqSum z) ^ (N + 1)) := by
    funext z; exact fsVolumeDensity_eq i z
  rw [this]
  unfold normSqSum
  fun_prop

theorem lintegral_fsVolumeDensity (i : Fin (N + 1)) :
    ∫⁻ z, ENNReal.ofReal (fsVolumeDensity i z) = 1 := by
  have h := lintegral_pi_complex_monomial 0 N (fun _ => 0) 1 one_pos
  simp only [mul_zero, pow_zero, Finset.prod_const_one, Finset.sum_const_zero, zero_add,
    add_zero, Nat.factorial_zero, Nat.cast_one, mul_one, one_pow, div_one] at h
  have hpt : ∀ z : Fin N → ℂ, ENNReal.ofReal (fsVolumeDensity i z) =
      ENNReal.ofReal (N.factorial / Real.pi ^ N) *
        ENNReal.ofReal (1 / (1 + ∑ j, ‖z j‖ ^ 2) ^ (N + 1)) := by
    intro z
    rw [← ENNReal.ofReal_mul (by positivity), fsVolumeDensity_eq]
    congr 1
    rw [normSqSum]
    field_simp
  rw [lintegral_congr hpt, lintegral_const_mul _ (by fun_prop), h, ← ENNReal.ofReal_mul (by positivity)]
  have hpi := Real.pi_pos
  have hN : (N.factorial : ℝ) ≠ 0 := by positivity
  rw [show (N.factorial : ℝ) / Real.pi ^ N * (Real.pi ^ N / N.factorial) = 1 by field_simp]
  simp

theorem fsMeasure_univ : fsMeasure N univ = 1 := by
  rw [fsMeasure, Measure.map_apply (measurable_chartInv 0) MeasurableSet.univ, preimage_univ,
    fsChartMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_fsVolumeDensity]

instance (N : ℕ) : IsProbabilityMeasure (fsMeasure N) := ⟨fsMeasure_univ⟩

def fsNormPoly (n : ℕ) (P : MvPolynomial (Fin (N + 1)) ℂ) (x : CP N) : ℝ :=
  ‖eval x.rep P‖ / norm2 x.rep ^ n

theorem fsNormPoly_mk {n : ℕ} {P : MvPolynomial (Fin (N + 1)) ℂ} (hP : P.IsHomogeneous n)
    (v : Fin (N + 1) → ℂ) (hv : v ≠ 0) :
    fsNormPoly n P (Projectivization.mk ℂ v hv) = ‖eval v P‖ / norm2 v ^ n := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v hv
  rw [fsNormPoly, ← ha, Units.smul_def]
  have he : eval ((a : ℂ) • v) P = (a : ℂ) ^ n * eval v P :=
    evalAt_smul (RingHom.id ℂ) hP (a : ℂ) v
  have hn : 0 < norm2 v := euclideanNorm_pos hv
  have ha0 : 0 < ‖(a : ℂ)‖ := norm_pos_iff.mpr a.ne_zero
  rw [he, norm_mul, norm_pow, euclideanNorm_smul, mul_pow]
  field_simp

theorem continuous_fsNormPoly {n : ℕ} {P : MvPolynomial (Fin (N + 1)) ℂ} (hP : P.IsHomogeneous n) :
    Continuous (fsNormPoly (N := N) n P) := by
  rw [ProjTopology.continuous_iff]
  have : fsNormPoly (N := N) n P ∘ Projectivization.mk' ℂ =
      fun v : {v : Fin (N + 1) → ℂ // v ≠ 0} => ‖eval v.1 P‖ / norm2 v.1 ^ n := by
    funext ⟨v, hv⟩; exact fsNormPoly_mk hP v hv
  rw [this]
  have hc : Continuous fun v : Fin (N + 1) → ℂ => norm2 v :=
    Real.continuous_sqrt.comp (continuous_finsetSum _ fun j _ =>
      (continuous_norm.comp (continuous_apply j)).pow 2)
  refine Continuous.div ?_ ((hc.comp continuous_subtype_val).pow n)
    fun v => (pow_pos (euclideanNorm_pos v.2) n).ne'
  exact continuous_norm.comp ((MvPolynomial.continuous_eval P).comp continuous_subtype_val)

def sectionL2NormSq (n : ℕ) (P : MvPolynomial (Fin (N + 1)) ℂ) : ℝ :=
  ∫ x, fsNormPoly n P x ^ 2 ∂fsMeasure N

def l2Norm (n : ℕ) (P : MvPolynomial (Fin (N + 1)) ℂ) : ℝ := √(sectionL2NormSq (N := N) n P)

lemma sectionL2NormSq_nonneg (n : ℕ) (P : MvPolynomial (Fin (N + 1)) ℂ) : 0 ≤ sectionL2NormSq (N := N) n P :=
  integral_nonneg fun _ => sq_nonneg _

lemma fubiniStudy_l2Norm_sq_eq (n : ℕ) (P : MvPolynomial (Fin (N + 1)) ℂ) :
    l2Norm (N := N) n P ^ 2 = sectionL2NormSq n P := Real.sq_sqrt (sectionL2NormSq_nonneg n P)

lemma chartVec_zero_succ (z : Fin N → ℂ) (j : Fin N) : chartVec 0 z j.succ = z j := by
  rw [← Fin.succAbove_zero, chartVec_succAbove]

lemma fsNormPoly_monomial_sq_chartInv (a : Fin (N + 1) →₀ ℕ) (z : Fin N → ℂ) :
    fsNormPoly a.degree (monomial a (1 : ℂ)) (chartInv 0 z) ^ 2 =
      (∏ j, ‖z j‖ ^ (2 * a j.succ)) / (1 + ∑ j, ‖z j‖ ^ 2) ^ a.degree := by
  rw [chartInv, fsNormPoly_mk (isHomogeneous_monomial 1 rfl), eval_monomial, one_mul,
    Finsupp.prod_fintype _ _ (fun i => pow_zero _), div_pow,
    show (norm2 (chartVec 0 z) ^ a.degree) ^ 2 = (norm2 (chartVec 0 z) ^ 2) ^ a.degree by ring,
    euclideanNorm_sq, normSq2_chartVec, norm_prod, Fin.prod_univ_succ, chartVec_self]
  simp only [one_pow, norm_one, one_mul, norm_pow, chartVec_zero_succ]
  congr 1
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← pow_mul, mul_comm]

theorem fubiniStudy_l2Norm_monomial_sq (a : Fin (N + 1) →₀ ℕ) :
    l2Norm (N := N) a.degree (monomial a (1 : ℂ)) ^ 2 =
      (∏ i, ((a i).factorial : ℝ)) * N.factorial / (a.degree + N).factorial := by
  have hdeg : a.degree = a 0 + ∑ j : Fin N, a j.succ := by
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_succ]
  have hfm : AEStronglyMeasurable (fun x : CP N => fsNormPoly a.degree (monomial a (1 : ℂ)) x ^ 2)
      (Measure.map (chartInv 0) (fsChartMeasure (N := N) 0)) :=
    ((continuous_fsNormPoly (isHomogeneous_monomial (1 : ℂ) rfl)).pow 2).aestronglyMeasurable
  rw [fubiniStudy_l2Norm_sq_eq, sectionL2NormSq, fsMeasure, integral_map (measurable_chartInv 0).aemeasurable hfm,
    fsChartMeasure]
  have hd : (fun z => ENNReal.ofReal (fsVolumeDensity (N := N) 0 z)) =
      fun z => (((fsVolumeDensity (N := N) 0 z).toNNReal : NNReal) : ENNReal) := rfl
  rw [hd, integral_withDensity_eq_integral_smul (measurable_fsVolumeDensity 0).real_toNNReal]
  have hpt : ∀ z : Fin N → ℂ, (fsVolumeDensity (N := N) 0 z).toNNReal •
      fsNormPoly a.degree (monomial a (1 : ℂ)) (chartInv 0 z) ^ 2 =
      (N.factorial / Real.pi ^ N) * ((∏ j, ‖z j‖ ^ (2 * a j.succ)) /
        (1 + ∑ j, ‖z j‖ ^ 2) ^ (∑ j : Fin N, a j.succ + N + 1 + a 0)) := by
    intro z
    rw [NNReal.smul_def, Real.coe_toNNReal _ (fsVolumeDensity_pos 0 z).le, smul_eq_mul,
      fsNormPoly_monomial_sq_chartInv, fsVolumeDensity_eq, normSqSum,
      show ∑ j : Fin N, a j.succ + N + 1 + a 0 = a.degree + (N + 1) by rw [hdeg]; ring, pow_add]
    have hS : 0 < 1 + ∑ j, ‖z j‖ ^ 2 := by positivity
    have hpi := Real.pi_pos
    field_simp
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul,
    (integral_pi_complex_monomial (a 0) N (fun j => a j.succ) 1 one_pos).2,
    Fin.prod_univ_succ, show ∑ j : Fin N, a j.succ + N + a 0 = a.degree + N by rw [hdeg]; ring]
  have hpi := Real.pi_pos
  have hf : ((a.degree + N).factorial : ℝ) ≠ 0 := by positivity
  simp only [one_pow, div_one]
  field_simp

end CP

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexPoints
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open AlgebraicGeometry CategoryTheory MvPolynomial GroundTheory.Arith.SchemeCoh
open scoped LinearAlgebra.Projectivization

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

structure ProjScheme (A : Type u) [CommRing A] (N : ℕ) where

  X : Scheme.{u}

  ι : X ⟶ projectiveSpace A N

  isClosedImmersion : IsClosedImmersion ι

attribute [instance] ProjScheme.isClosedImmersion

namespace ProjScheme

variable {A : Type u} [CommRing A] {N : ℕ}

variable (X : ProjScheme A N)

end ProjScheme

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.CovolumeCount
namespace GroundTheory.Heights₂.Heights

open MeasureTheory Metric Module ZSpan NumberField

noncomputable section

section Euclidean

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] (L : Submodule ℤ V) [DiscreteTopology L]


omit [MeasurableSpace V] [BorelSpace V] in
theorem finite_lattice_closedBall (r : ℝ) : {x : V | x ∈ L ∧ ‖x‖ ≤ r}.Finite := by
  have h := Metric.finite_isBounded_inter_isClosed (K := closedBall (0 : V) r)
    (s := (L : Set V)) DiscreteTopology.isDiscrete isBounded_closedBall
    (by rw [← Submodule.coe_toAddSubgroup]; exact AddSubgroup.isClosed_of_discrete)
  refine h.subset ?_
  rintro v ⟨hv, hr⟩
  exact ⟨by simpa using hr, hv⟩

variable [IsZLattice ℝ L]


end Euclidean

section Bundle

variable {K : Type*} [Field K] [NumberField K] {E : Type*} [AddCommGroup E] [Module (𝓞 K) E]
  [Module.Finite (𝓞 K) E] [Module.Projective (𝓞 K) E] (h : HermitianMetric K E)

end Bundle

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FubiniStudyTransition
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open scoped ComplexConjugate Matrix
open Set

noncomputable section

variable {N : ℕ}

namespace CP

def hpair (V W : Fin (N + 1) → ℂ) : ℂ := ∑ m, V m * conj (W m)

lemma hpair_add_left (V V' W : Fin (N + 1) → ℂ) : hpair (V + V') W = hpair V W + hpair V' W := by
  simp [hpair, add_mul, Finset.sum_add_distrib]

lemma hpair_add_right (V W W' : Fin (N + 1) → ℂ) : hpair V (W + W') = hpair V W + hpair V W' := by
  simp [hpair, mul_add, Finset.sum_add_distrib]

lemma hpair_smul_left (c : ℂ) (V W : Fin (N + 1) → ℂ) : hpair (c • V) W = c * hpair V W := by
  rw [hpair, hpair, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

lemma hpair_smul_right (c : ℂ) (V W : Fin (N + 1) → ℂ) :
    hpair V (c • W) = conj c * hpair V W := by
  rw [hpair, hpair, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  ring

def fsHerm (p V W : Fin (N + 1) → ℂ) : ℂ :=
  (hpair V W * hpair p p - hpair V p * hpair p W) / ((2 * Real.pi : ℂ) * hpair p p ^ 2)

lemma fsHerm_smul {c : ℂ} (hc : c ≠ 0) (p V W : Fin (N + 1) → ℂ) :
    fsHerm (c • p) (c • V) (c • W) = fsHerm p V W := by
  simp only [fsHerm, hpair_smul_left, hpair_smul_right]
  have hr : c * conj c ≠ 0 := mul_ne_zero hc ((map_ne_zero _).mpr hc)
  rw [← mul_div_mul_left (hpair V W * hpair p p - hpair V p * hpair p W) _ (pow_ne_zero 2 hr)]
  congr 1 <;> ring

lemma fsHerm_add_smul (p V W : Fin (N + 1) → ℂ) (a b : ℂ) :
    fsHerm p (V + a • p) (W + b • p) = fsHerm p V W := by
  simp only [fsHerm, hpair_add_left, hpair_add_right, hpair_smul_left, hpair_smul_right]
  congr 1
  ring

def liftVec (i : Fin (N + 1)) (ξ : Fin N → ℂ) : Fin (N + 1) → ℂ := Fin.insertNth i 0 ξ

@[simp] lemma liftVec_self (i : Fin (N + 1)) (ξ : Fin N → ℂ) : liftVec i ξ i = 0 := by
  simp [liftVec]

@[simp] lemma liftVec_succAbove (i : Fin (N + 1)) (ξ : Fin N → ℂ) (k : Fin N) :
    liftVec i ξ (i.succAbove k) = ξ k := by
  simp [liftVec]

lemma hpair_liftVec_liftVec (i : Fin (N + 1)) (ξ η : Fin N → ℂ) :
    hpair (liftVec i ξ) (liftVec i η) = ∑ k, ξ k * conj (η k) := by
  rw [hpair, Fin.sum_univ_succAbove _ i]; simp

lemma hpair_liftVec_chartVec (i : Fin (N + 1)) (ξ z : Fin N → ℂ) :
    hpair (liftVec i ξ) (chartVec i z) = ∑ k, ξ k * conj (z k) := by
  rw [hpair, Fin.sum_univ_succAbove _ i]; simp

lemma hpair_chartVec_liftVec (i : Fin (N + 1)) (z η : Fin N → ℂ) :
    hpair (chartVec i z) (liftVec i η) = ∑ k, z k * conj (η k) := by
  rw [hpair, Fin.sum_univ_succAbove _ i]; simp

lemma hpair_chartVec_self (i : Fin (N + 1)) (z : Fin N → ℂ) :
    hpair (chartVec i z) (chartVec i z) = 1 + (normSqSum z : ℂ) := by
  rw [hpair, Fin.sum_univ_succAbove _ i]
  simp [normSqSum, Complex.mul_conj']

theorem chernForm_eq_fsHerm (i : Fin (N + 1)) (z ξ η : Fin N → ℂ) :
    ∑ a, ∑ b, chernCoeff i z a b * ξ a * conj (η b) =
      fsHerm (chartVec i z) (liftVec i ξ) (liftVec i η) := by
  have hS := one_add_normSqSum_pos z
  have h1 : ∑ a, ∑ b, (1 : Matrix (Fin N) (Fin N) ℂ) a b * ξ a * conj (η b) =
      ∑ a, ξ a * conj (η a) := by
    simp [Matrix.one_apply]
  have h2 : ∑ a, ∑ b, conj (z a) * z b * ξ a * conj (η b) =
      (∑ a, ξ a * conj (z a)) * ∑ b, z b * conj (η b) := by
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have hpt : ∀ a b, chernCoeff i z a b * ξ a * conj (η b) =
      ((1 / (2 * Real.pi * (1 + normSqSum z)) : ℝ) : ℂ) *
          ((1 : Matrix (Fin N) (Fin N) ℂ) a b * ξ a * conj (η b)) -
        ((1 / (2 * Real.pi * (1 + normSqSum z)) : ℝ) : ℂ) * (((1 + normSqSum z)⁻¹ : ℝ) : ℂ) *
          (conj (z a) * z b * ξ a * conj (η b)) := by
    intro a b; rw [chernCoeff_apply]; ring
  simp_rw [hpt, Finset.sum_sub_distrib, ← Finset.mul_sum, h1, h2]
  rw [fsHerm, hpair_liftVec_liftVec, hpair_chartVec_self, hpair_liftVec_chartVec,
    hpair_chartVec_liftVec]
  have hS' : (1 + (normSqSum z : ℂ)) ≠ 0 := by exact_mod_cast hS.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp

def transition (i j : Fin (N + 1)) (z : Fin N → ℂ) : Fin N → ℂ := chartCoord j (chartInv i z)

lemma transition_apply (i j : Fin (N + 1)) (z : Fin N → ℂ) (k : Fin N) :
    transition i j z k = chartVec i z (j.succAbove k) / chartVec i z j := rfl

def liftCLM (i : Fin (N + 1)) : (Fin N → ℂ) →L[ℂ] (Fin (N + 1) → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := liftVec i
      map_add' := fun ξ η => by
        funext m
        obtain rfl | ⟨k, rfl⟩ := Fin.eq_self_or_eq_succAbove i m <;> simp
      map_smul' := fun c ξ => by
        funext m
        obtain rfl | ⟨k, rfl⟩ := Fin.eq_self_or_eq_succAbove i m <;> simp }

@[simp] lemma liftCLM_apply (i : Fin (N + 1)) (ξ : Fin N → ℂ) : liftCLM i ξ = liftVec i ξ := rfl

lemma chartVec_eq_add (i : Fin (N + 1)) (z : Fin N → ℂ) :
    chartVec i z = chartVec i 0 + liftVec i z := by
  funext m
  obtain rfl | ⟨k, rfl⟩ := Fin.eq_self_or_eq_succAbove i m <;> simp

lemma hasFDerivAt_chartVec (i : Fin (N + 1)) (z : Fin N → ℂ) :
    HasFDerivAt (chartVec (N := N) i) (liftCLM i) z := by
  have h : chartVec (N := N) i = fun w => chartVec i 0 + liftCLM i w := by
    funext w; exact chartVec_eq_add i w
  rw [h]
  exact (liftCLM i).hasFDerivAt.const_add _

theorem hasFDerivAt_transition (i j : Fin (N + 1)) {z : Fin N → ℂ} (hz : chartVec i z j ≠ 0) :
    HasFDerivAt (transition i j) (ContinuousLinearMap.pi fun k =>
      chartVec i z (j.succAbove k) • ((-(chartVec i z j ^ 2)⁻¹) •
          (ContinuousLinearMap.proj j).comp (liftCLM i)) +
        (chartVec i z j)⁻¹ • (ContinuousLinearMap.proj (j.succAbove k)).comp (liftCLM i)) z := by
  have hc := hasFDerivAt_pi'.mp (hasFDerivAt_chartVec (N := N) i z)
  have hfun : transition (N := N) i j =
      fun w k => chartVec i w (j.succAbove k) * (chartVec i w j)⁻¹ := by
    funext w k; rw [transition_apply, div_eq_mul_inv]
  rw [hfun]
  refine hasFDerivAt_pi.mpr fun k => ?_
  exact (hc (j.succAbove k)).mul ((hasDerivAt_inv hz).comp_hasFDerivAt z (hc j))

lemma differentiableAt_transition (i j : Fin (N + 1)) {z : Fin N → ℂ}
    (hz : chartVec i z j ≠ 0) : DifferentiableAt ℂ (transition i j) z :=
  (hasFDerivAt_transition i j hz).differentiableAt

theorem liftVec_fderiv_transition (i j : Fin (N + 1)) {z : Fin N → ℂ} (hz : chartVec i z j ≠ 0)
    (ξ : Fin N → ℂ) :
    liftVec j (fderiv ℂ (transition i j) z ξ) = (chartVec i z j)⁻¹ •
      (liftVec i ξ + (-(liftVec i ξ j / chartVec i z j)) • chartVec i z) := by
  rw [(hasFDerivAt_transition i j hz).fderiv]
  funext m
  obtain rfl | ⟨k, rfl⟩ := Fin.eq_self_or_eq_succAbove j m
  · simp only [liftVec_self, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    field_simp
    ring
  · simp only [liftVec_succAbove, ContinuousLinearMap.pi_apply, FunLike.coe_add,
      FunLike.coe_smul, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
      liftCLM_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    field_simp
    ring

lemma chartVec_transition (i j : Fin (N + 1)) {z : Fin N → ℂ} (hz : chartVec i z j ≠ 0) :
    chartVec j (transition i j z) = (chartVec i z j)⁻¹ • chartVec i z := by
  funext m
  obtain rfl | ⟨k, rfl⟩ := Fin.eq_self_or_eq_succAbove j m
  · simp [hz]
  · simp only [chartVec_succAbove, transition_apply, Pi.smul_apply, smul_eq_mul]
    rw [div_eq_mul_inv, mul_comm]

theorem chernForm_transition (i j : Fin (N + 1)) {z : Fin N → ℂ} (hz : chartVec i z j ≠ 0)
    (ξ η : Fin N → ℂ) :
    ∑ a, ∑ b, chernCoeff i z a b * ξ a * conj (η b) =
      ∑ a, ∑ b, chernCoeff j (transition i j z) a b * fderiv ℂ (transition i j) z ξ a *
        conj (fderiv ℂ (transition i j) z η b) := by
  rw [chernForm_eq_fsHerm, chernForm_eq_fsHerm, chartVec_transition i j hz,
    liftVec_fderiv_transition i j hz, liftVec_fderiv_transition i j hz,
    fsHerm_smul (inv_ne_zero hz), fsHerm_add_smul]

def transitionJac (i j : Fin (N + 1)) (z : Fin N → ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  LinearMap.toMatrix' (fderiv ℂ (transition i j) z : (Fin N → ℂ) →ₗ[ℂ] (Fin N → ℂ))

lemma fderiv_transition_single (i j : Fin (N + 1)) (z : Fin N → ℂ) (b a : Fin N) :
    fderiv ℂ (transition i j) z (Pi.single b 1) a = transitionJac i j z a b := by
  simp [transitionJac, LinearMap.toMatrix'_apply]

theorem chernCoeff_transition (i j : Fin (N + 1)) {z : Fin N → ℂ} (hz : chartVec i z j ≠ 0) :
    chernCoeff i z = (transitionJac i j z)ᵀ * chernCoeff j (transition i j z) *
      (transitionJac i j z).map conj := by
  ext b d
  have h := chernForm_transition i j hz (Pi.single b 1) (Pi.single d 1)
  simp only [fderiv_transition_single] at h
  simp [Pi.single_apply] at h
  rw [h, Matrix.mul_apply]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem det_chernCoeff_transition (i j : Fin (N + 1)) {z : Fin N → ℂ} (hz : chartVec i z j ≠ 0) :
    (chernCoeff i z).det =
      (Complex.normSq (transitionJac i j z).det : ℂ) * (chernCoeff j (transition i j z)).det := by
  rw [chernCoeff_transition i j hz, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← Complex.mul_conj]
  ring

theorem det_fderiv_real_transition (i j : Fin (N + 1)) {z : Fin N → ℂ}
    (hz : chartVec i z j ≠ 0) :
    (fderiv ℝ (transition i j) z).det = Complex.normSq (transitionJac i j z).det := by
  rw [((hasFDerivAt_transition i j hz).restrictScalars ℝ).fderiv, ← (hasFDerivAt_transition i j hz).fderiv,
    ContinuousLinearMap.det, ContinuousLinearMap.coe_restrictScalars,
    LinearMap.det_restrictScalars, Algebra.norm_complex_apply, transitionJac, LinearMap.det_toMatrix']

theorem fsVolumeDensity_transition (i j : Fin (N + 1)) {z : Fin N → ℂ}
    (hz : chartVec i z j ≠ 0) :
    fsVolumeDensity i z =
      |(fderiv ℝ (transition i j) z).det| * fsVolumeDensity j (transition i j z) := by
  rw [det_fderiv_real_transition i j hz, abs_of_nonneg (Complex.normSq_nonneg _), fsVolumeDensity,
    fsVolumeDensity, det_chernCoeff_transition i j hz, Complex.re_ofReal_mul]
  ring

end CP

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithDegreeDetIdeal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField Matrix

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

def detIdeal {r : ℕ} (E : Submodule (𝓞 K) (Fin r → 𝓞 K)) : Ideal (𝓞 K) :=
  Ideal.span {d | ∃ v : Fin r → Fin r → 𝓞 K, (∀ i, v i ∈ E) ∧ (Matrix.of v).det = d}

omit [NumberField K] in
theorem det_mem_detIdeal {r : ℕ} (E : Submodule (𝓞 K) (Fin r → 𝓞 K)) (v : Fin r → Fin r → 𝓞 K)
    (hv : ∀ i, v i ∈ E) : (Matrix.of v).det ∈ detIdeal E :=
  Ideal.subset_span ⟨v, hv, rfl⟩

def consZero (r : ℕ) : (Fin r → 𝓞 K) →ₗ[𝓞 K] (Fin (r + 1) → 𝓞 K) where
  toFun y := Fin.cons 0 y
  map_add' y z := by
    ext i
    refine Fin.cases ?_ (fun k ↦ ?_) i <;> simp
  map_smul' c y := by
    ext i
    refine Fin.cases ?_ (fun k ↦ ?_) i <;> simp

omit [NumberField K] in
theorem consZero_zero {r : ℕ} (y : Fin r → 𝓞 K) : consZero r y 0 = 0 := rfl


omit [NumberField K] in
theorem range_consZero (r : ℕ) :
    LinearMap.range (consZero (K := K) r) = LinearMap.ker (LinearMap.proj 0) := by
  ext x
  simp only [LinearMap.mem_range, LinearMap.mem_ker, LinearMap.proj_apply]
  constructor
  · rintro ⟨y, rfl⟩; rfl
  · intro hx
    refine ⟨Fin.tail x, ?_⟩
    rw [← Fin.cons_self_tail x, hx]
    rfl


omit [NumberField K] in
theorem card_quotient_succ {r : ℕ} (E : Submodule (𝓞 K) (Fin (r + 1) → 𝓞 K)) :
    Nat.card ((Fin (r + 1) → 𝓞 K) ⧸ E) =
      Nat.card ((Fin r → 𝓞 K) ⧸ E.comap (consZero r)) *
        Nat.card (𝓞 K ⧸ E.map (LinearMap.proj 0)) := by
  set π : (Fin (r + 1) → 𝓞 K) →ₗ[𝓞 K] 𝓞 K := LinearMap.proj 0
  set S := E ⊔ LinearMap.ker π
  rw [← Submodule.card_quotient_mul_card_quotient S E le_sup_left]
  congr 1
  · have hS : S.map E.mkQ = LinearMap.range (E.mkQ ∘ₗ consZero r) := by
      rw [Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq, LinearMap.range_comp,
        range_consZero]
    have hker : LinearMap.ker (E.mkQ ∘ₗ consZero r) = E.comap (consZero r) := by
      ext y
      simp [Submodule.Quotient.mk_eq_zero]
    rw [hS, ← hker]
    exact Nat.card_congr (LinearMap.quotKerEquivRange _).toEquiv.symm
  · set φ := (E.map π).mkQ ∘ₗ π
    have hπ : Function.Surjective π := fun a ↦ ⟨fun _ ↦ a, rfl⟩
    have hφ : Function.Surjective φ := (Submodule.mkQ_surjective _).comp hπ
    have hker : LinearMap.ker φ = S := by
      ext x
      simp only [φ, LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
        Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_map, S,
        Submodule.mem_sup]
      constructor
      · rintro ⟨e, he, hex⟩
        refine ⟨e, he, x - e, ?_, add_sub_cancel _ _⟩
        show π (x - e) = 0
        rw [map_sub, hex, sub_self]
      · rintro ⟨e, he, k, hk, rfl⟩
        refine ⟨e, he, ?_⟩
        rw [map_add (f := _), LinearMap.mem_ker.mp hk, add_zero]
    rw [← hker]
    exact Nat.card_congr (φ.quotKerEquivOfSurjective hφ).toEquiv


omit [NumberField K] in
theorem mul_le_detIdeal {r : ℕ} (E : Submodule (𝓞 K) (Fin (r + 1) → 𝓞 K)) :
    E.map (LinearMap.proj 0) * detIdeal (E.comap (consZero r)) ≤ detIdeal E := by
  rw [Ideal.mul_le]
  intro a ha d hd
  obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp ha
  induction hd using Submodule.span_induction with
  | mem d hd =>
    obtain ⟨v', hv', rfl⟩ := hd
    let v : Fin (r + 1) → Fin (r + 1) → 𝓞 K := Fin.cons w (fun k ↦ consZero r (v' k))
    have hv : ∀ i, v i ∈ E := by
      intro i
      refine Fin.cases ?_ (fun k ↦ ?_) i
      · exact hw
      · exact hv' k
    have hdet : (Matrix.of v).det = w 0 * (Matrix.of v').det := by
      rw [det_succ_column_zero, Fin.sum_univ_succ]
      simp only [v, of_apply, Fin.cons_zero, Fin.cons_succ, consZero_zero, Fin.succAbove_zero,
        Fin.val_zero, pow_zero, one_mul, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
      congr 2
    rw [LinearMap.proj_apply, ← hdet]
    exact det_mem_detIdeal E v hv
  | zero => rw [mul_zero]; exact Ideal.zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact Ideal.add_mem _ hx hy
  | smul c x _ hx =>
    rw [smul_eq_mul, mul_left_comm]
    exact Ideal.mul_mem_left _ c hx

theorem detIdeal_le_mul {r : ℕ} (E : Submodule (𝓞 K) (Fin (r + 1) → 𝓞 K)) :
    detIdeal E ≤ E.map (LinearMap.proj 0) * detIdeal (E.comap (consZero r)) := by
  classical
  set π : (Fin (r + 1) → 𝓞 K) →ₗ[𝓞 K] 𝓞 K := LinearMap.proj 0
  set 𝔞 := E.map π
  set E' := E.comap (consZero r)
  let πE : E →ₗ[𝓞 K] 𝔞 := (π ∘ₗ E.subtype).codRestrict 𝔞 (fun x ↦ Submodule.mem_map_of_mem x.2)
  have hπE : Function.Surjective πE := by
    rintro ⟨a, ha⟩
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp ha
    exact ⟨⟨w, hw⟩, rfl⟩
  obtain ⟨t, ht⟩ := Module.projective_lifting_property πE LinearMap.id hπE
  have htπ : ∀ a : 𝔞, π (t a) = a := fun a ↦ congrArg Subtype.val (LinearMap.congr_fun ht a)
  rw [detIdeal, Ideal.span_le]
  rintro _ ⟨v, hv, rfl⟩
  let a : Fin (r + 1) → 𝔞 := fun i ↦ ⟨π (v i), Submodule.mem_map_of_mem (hv i)⟩
  let w : Fin (r + 1) → Fin (r + 1) → 𝓞 K := fun i ↦ (t (a i) : Fin (r + 1) → 𝓞 K)
  let e : Fin (r + 1) → Fin (r + 1) → 𝓞 K := fun i ↦ v i - w i
  have hw0 : ∀ i, w i 0 = (a i : 𝓞 K) := fun i ↦ htπ (a i)
  have he0 : ∀ i, e i 0 = 0 := fun i ↦ by
    simp only [e, Pi.sub_apply, hw0]
    exact sub_self _
  have he' : ∀ i, Fin.tail (e i) ∈ E' := by
    intro i
    show consZero r (Fin.tail (e i)) ∈ E
    have : consZero r (Fin.tail (e i)) = e i := by
      conv_rhs => rw [← Fin.cons_self_tail (e i), he0]
      rfl
    rw [this]
    exact E.sub_mem (hv i) (t (a i)).2
  have hvew : v = e + w := by
    funext i
    simp [e]
  have hprop : ∀ i j, (a j : 𝓞 K) • w i = (a i : 𝓞 K) • w j := by
    intro i j
    have h1 : (a j : 𝓞 K) • t (a i) = (a i : 𝓞 K) • t (a j) := by
      rw [← map_smul, ← map_smul]
      congr 1
      ext
      simp only [SetLike.val_smul, smul_eq_mul]
      exact mul_comm _ _
    exact congrArg Subtype.val h1
  have hwzero : ∀ j, (a j : 𝓞 K) = 0 → w j = 0 := by
    intro j hj
    have : a j = 0 := Subtype.ext hj
    simp only [w, this, map_zero, ZeroMemClass.coe_zero]
  rw [hvew]
  change (detRowAlternating : (Fin (r + 1) → 𝓞 K) [⋀^Fin (r + 1)]→ₗ[𝓞 K] 𝓞 K) (e + w) ∈ _
  rw [← AlternatingMap.coe_multilinearMap, MultilinearMap.map_add_univ]
  refine Ideal.sum_mem _ fun S _ ↦ ?_
  set R := S.piecewise e w
  change (Matrix.of R).det ∈ _
  have hRS : ∀ k ∈ S, R k = e k := fun k hk ↦ Finset.piecewise_eq_of_mem _ _ _ hk
  have hRT : ∀ k ∉ S, R k = w k := fun k hk ↦ Finset.piecewise_eq_of_notMem _ _ _ hk
  set T := Finset.univ \ S
  have hT : ∀ k, k ∈ T ↔ k ∉ S := fun k ↦ by simp [T]
  by_cases h2 : 1 < T.card
  ·
    obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp h2
    have hi' := (hT i).mp hi
    have hj' := (hT j).mp hj
    suffices (Matrix.of R).det = 0 by rw [this]; exact Ideal.zero_mem _
    by_cases haj : (a j : 𝓞 K) = 0
    · apply det_eq_zero_of_row_eq_zero j
      intro k
      rw [of_apply, hRT j hj', hwzero j haj]
      rfl
    · have key : (a j : 𝓞 K) * (Matrix.of R).det = 0 := by
        have hRi : (Matrix.of R) i = w i := hRT i hi'
        have e1 : (a j : 𝓞 K) * (Matrix.of R).det =
            (updateRow (Matrix.of R) i ((a j : 𝓞 K) • w i)).det := by
          rw [det_updateRow_smul, ← hRi, updateRow_eq_self]
        rw [e1, hprop i j, det_updateRow_smul]
        refine mul_eq_zero_of_right _ (det_zero_of_row_eq hij ?_)
        rw [updateRow_self, updateRow_ne (Ne.symm hij)]
        exact (hRT j hj').symm
      exact (mul_eq_zero.mp key).resolve_left haj
  · rcases Nat.lt_or_ge T.card 1 with h0 | h1
    ·
      have hTe : T = ∅ := Finset.card_eq_zero.mp (by omega)
      suffices (Matrix.of R).det = 0 by rw [this]; exact Ideal.zero_mem _
      apply det_eq_zero_of_column_eq_zero 0
      intro k
      have hk : k ∈ S := by
        by_contra hk
        have := (hT k).mpr hk
        rw [hTe] at this
        exact Finset.notMem_empty k this
      rw [of_apply, hRS k hk, he0]
    ·
      obtain ⟨j, hTj⟩ := Finset.card_eq_one.mp (by omega : T.card = 1)
      have hjS : j ∉ S := (hT j).mp (by rw [hTj]; exact Finset.mem_singleton_self j)
      have hkS : ∀ k, k ≠ j → k ∈ S := by
        intro k hk
        by_contra hkS
        have := (hT k).mpr hkS
        rw [hTj, Finset.mem_singleton] at this
        exact hk this
      rw [det_succ_column_zero, Finset.sum_eq_single j]
      · rw [of_apply, hRT j hjS, hw0]
        have hsub : (Matrix.of R).submatrix j.succAbove Fin.succ =
            Matrix.of fun k ↦ Fin.tail (e (j.succAbove k)) := by
          ext k l
          simp only [submatrix_apply, of_apply, Fin.tail]
          rw [hRS _ (hkS _ (Fin.succAbove_ne j k))]
        rw [hsub, mul_assoc]
        exact Ideal.mul_mem_left _ _
          (Ideal.mul_mem_mul (a j).2 (det_mem_detIdeal E' _ fun k ↦ he' _))
      · intro k _ hk
        rw [of_apply, hRS k (hkS k hk), he0, mul_zero, zero_mul]
      · intro h
        exact absurd (Finset.mem_univ j) h

theorem detIdeal_succ {r : ℕ} (E : Submodule (𝓞 K) (Fin (r + 1) → 𝓞 K)) :
    detIdeal E = E.map (LinearMap.proj 0) * detIdeal (E.comap (consZero r)) :=
  le_antisymm (detIdeal_le_mul E) (mul_le_detIdeal E)

theorem card_quotient_eq_absNorm_detIdeal :
    ∀ (r : ℕ) (E : Submodule (𝓞 K) (Fin r → 𝓞 K)),
      Nat.card ((Fin r → 𝓞 K) ⧸ E) = Ideal.absNorm (detIdeal E)
  | 0, E => by
    have hE : E = ⊤ := Subsingleton.elim _ _
    have hd : detIdeal E = ⊤ := by
      rw [Ideal.eq_top_iff_one]
      have := det_mem_detIdeal E (fun i ↦ Fin.elim0 i) (fun i ↦ Fin.elim0 i)
      rwa [det_isEmpty] at this
    rw [hd, Ideal.absNorm_top, hE]
    exact Nat.card_unique
  | r + 1, E => by
    rw [card_quotient_succ, card_quotient_eq_absNorm_detIdeal r, detIdeal_succ, map_mul,
      Ideal.absNorm_apply (E.map (LinearMap.proj 0)), Submodule.cardQuot_apply, mul_comm]

end

end GroundTheory.Heights₂.Heights
end
