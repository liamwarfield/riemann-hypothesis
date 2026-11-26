module

public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
public import Formalism.HarderNarasimhan.ShiftInvariance

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EqZeroOfExpDecayOfFourierEqZeroOnHalfLine
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrableExpNegMulAbs
namespace GlobalTheory.IntegrableExpNegAbs

open MeasureTheory Set

theorem integrable_exp_neg_mul_abs {c : ℝ} (hc : (0 : ℝ) < c) :
    MeasureTheory.Integrable (fun (s : ℝ) ↦ Real.exp (-(c * |s|))) MeasureTheory.MeasureSpace.volume := by
  have h1 : IntegrableOn (fun s : ℝ ↦ Real.exp (-(c * |s|))) (Ioi 0) volume := by
    refine (integrableOn_exp_mul_Ioi (a := -c) (by linarith) 0).congr_fun ?_ measurableSet_Ioi
    intro x hx
    have hx' : 0 < x := hx
    simp only [abs_of_pos hx', neg_mul]
  have h2 : IntegrableOn (fun s : ℝ ↦ Real.exp (-(c * |s|))) (Iic 0) volume := by
    refine (integrableOn_exp_mul_Iic (a := c) hc 0).congr_fun ?_ measurableSet_Iic
    intro x hx
    have hx' : x ≤ 0 := hx
    simp only [abs_of_nonpos hx', mul_neg, neg_neg]
  have h := h2.union h1
  rwa [Iic_union_Ioi, integrableOn_univ] at h

end GlobalTheory.IntegrableExpNegAbs
end

open MeasureTheory Filter Set
open scoped Topology FourierTransform

namespace GlobalTheory

theorem integrable_exp_neg_mul_abs_line {c : ℝ} (hc : 0 < c) :
    Integrable (fun s : ℝ => Real.exp (-(c * |s|))) := by
  first
  | exact @_root_.GlobalTheory.IntegrableExpNegAbs.integrable_exp_neg_mul_abs
  | exact _root_.GlobalTheory.IntegrableExpNegAbs.integrable_exp_neg_mul_abs
  | (apply _root_.GlobalTheory.IntegrableExpNegAbs.integrable_exp_neg_mul_abs <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegrableExpNegAbs.integrable_exp_neg_mul_abs <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegrableExpNegAbs.integrable_exp_neg_mul_abs <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegrableExpNegAbs.integrable_exp_neg_mul_abs ..)

theorem eq_zero_of_exp_decay_of_fourier_eq_zero_on_halfLine :
    ∀ (φ : ℝ → ℂ) (R : ℝ), Continuous φ →
      (∃ A e : ℝ, 0 < e ∧ ∀ s, ‖φ s‖ ≤ A * Real.exp (-(e * |s|))) →
      (∀ ξ : ℝ, R ≤ ξ → ∫ s : ℝ, Complex.exp (-(Complex.I * ξ * s)) * φ s = 0) → φ = 0 := by
  rintro φ R hφ ⟨A, e, he, hb⟩ hz
  set U : Set ℂ := {z | -(e / 2) < z.im} ∩ {z | z.im < e / 2} with hUdef
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_im).inter
      (isOpen_lt Complex.continuous_im continuous_const)
  have hUc : Convex ℝ U := (convex_halfSpace_im_gt _).inter (convex_halfSpace_im_lt _)
  have hre : ∀ x : ℝ, (x : ℂ) ∈ U := fun x => by
    simp only [hUdef, mem_inter_iff, mem_setOf_eq, Complex.ofReal_im]
    constructor <;> linarith
  have hint : Integrable (fun s : ℝ => A * Real.exp (-(e / 2 * |s|))) :=
    (integrable_exp_neg_mul_abs_line (half_pos he)).const_mul A
  have hA : 0 ≤ A := by
    have := (norm_nonneg _).trans (hb 0)
    simpa using this
  have hbound : ∀ s : ℝ, ∀ y ∈ U,
      ‖Complex.exp (-(Complex.I * y * s)) * φ s‖ ≤ A * Real.exp (-(e / 2 * |s|)) := by
    intro s y hy
    have hy' : |y.im| ≤ e / 2 := abs_le.2 ⟨hy.1.le, hy.2.le⟩
    have h1 : (-(Complex.I * y * s)).re = y.im * s := by simp
    have h2 : y.im * s ≤ e / 2 * |s| := by
      refine (le_abs_self _).trans ?_
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right hy' (abs_nonneg _)
    rw [norm_mul, Complex.norm_exp, h1]
    calc Real.exp (y.im * s) * ‖φ s‖
        ≤ Real.exp (e / 2 * |s|) * (A * Real.exp (-(e * |s|))) :=
          mul_le_mul (Real.exp_le_exp.2 h2) (hb s) (norm_nonneg _) (Real.exp_pos _).le
      _ = A * Real.exp (-(e / 2 * |s|)) := by
          rw [mul_left_comm, ← Real.exp_add]
          congr 2
          ring
  have hdiff := (differentiableOn_integral_of_holomorphic_of_locally_dominated
    (μ := (volume : Measure ℝ))
    (F := fun (s : ℝ) (y : ℂ) => Complex.exp (-(Complex.I * y * s)) * φ s) hUo
    (fun y _ => Continuous.aestronglyMeasurable (by fun_prop))
    (Eventually.of_forall fun s => Differentiable.differentiableOn (by fun_prop))
    (fun x hx => ⟨U, hUo.mem_nhds hx, _, hint, Eventually.of_forall hbound⟩)).1
  have han := hdiff.analyticOnNhd hUo
  have hfr : ∃ᶠ y in 𝓝[≠] (R : ℂ),
      ∫ s : ℝ, Complex.exp (-(Complex.I * y * s)) * φ s = 0 := by
    have ht : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[>] R) (𝓝[≠] (R : ℂ)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · exact (Complex.continuous_ofReal.tendsto R).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with x hx
        simpa using (ne_of_gt hx)
    refine ht.frequently (Eventually.frequently ?_)
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact hz x (le_of_lt hx)
  have hzero := han.eqOn_zero_of_preconnected_of_frequently_eq_zero hUc.isPreconnected
    (hre R) hfr
  have hF : 𝓕 φ = 0 := by
    funext w
    rw [Real.fourier_real_eq_integral_exp_smul]
    have := hzero (hre (2 * Real.pi * w))
    simp only [Pi.zero_apply] at this ⊢
    rw [← this]
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    simp only [smul_eq_mul]
    congr 2
    push_cast
    ring
  have hφi : Integrable φ :=
    ((integrable_exp_neg_mul_abs_line he).const_mul A).mono' hφ.aestronglyMeasurable
      (Eventually.of_forall hb)
  have hinv := hφ.fourierInv_fourier_eq hφi (by rw [hF]; exact integrable_zero _ _ _)
  rw [← hinv, hF]
  funext x
  simp [Real.fourierInv_eq]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CauchySchwarz
open scoped ComplexOrder

namespace GlobalTheory.HermitianCauchySchwarz

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem herm (I : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (hI : ∀ x : V, (0 : ℂ) ≤ I x x) (x y : V) :
    I y x = starRingEnd ℂ (I x y) := by
  have h1 := hI (x + y)
  have h2 := hI (x + Complex.I • y)
  have hx := hI x
  have hy := hI y
  rw [Complex.nonneg_iff] at h1 h2 hx hy
  simp only [map_add (f := _), LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
    Complex.add_im, Complex.add_re, Complex.mul_im, Complex.mul_re, Complex.conj_re,
    Complex.conj_im, Complex.I_re, Complex.I_im, RingHom.id_apply] at h1 h2
  apply Complex.ext <;> simp [Complex.conj_re, Complex.conj_im] <;> linarith [h1.2, h2.2, hx.2, hy.2]

theorem cauchy_schwarz (I : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (hI : ∀ x : V, (0 : ℂ) ≤ I x x) (x y : V) :
    ‖I x y‖ ^ 2 ≤ (I x x).re * (I y y).re := by
  set b := I x y with hb
  have hyx := herm I hI x y
  have hx := (Complex.nonneg_iff.mp (hI x))
  have hy := (Complex.nonneg_iff.mp (hI y))
  have hq : ∀ s : ℝ, 0 ≤ ((I y y).re * (b.re * b.re + b.im * b.im)) * (s * s)
      + (-2 * (b.re * b.re + b.im * b.im)) * s + (I x x).re := by
    intro s
    have h := (Complex.nonneg_iff.mp (hI (x + ((-(s : ℂ)) * starRingEnd ℂ b) • y))).1
    simp only [map_add (f := _), LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
      RingHom.id_apply] at h
    rw [hyx] at h
    simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, map_mul, map_neg,
      Complex.conj_ofReal, RingHom.map_neg, Complex.conj_conj, ← hb, Complex.add_im, mul_zero,
      sub_zero, neg_zero, zero_mul, add_zero] at h
    rw [← hy.2] at h
    nlinarith [h, hx.2, hy.2]
  have hd := discrim_le_zero hq
  unfold discrim at hd
  rw [Complex.sq_norm, Complex.normSq_apply]
  set n := b.re * b.re + b.im * b.im
  have hn : 0 ≤ n := by nlinarith [mul_self_nonneg b.re, mul_self_nonneg b.im]
  have hac : 0 ≤ (I x x).re * (I y y).re := mul_nonneg hx.1 hy.1
  rcases hn.eq_or_lt with h0 | hpos
  · rw [← h0]; exact hac
  · nlinarith

end GlobalTheory.HermitianCauchySchwarz

theorem GlobalTheory.HermitianCauchySchwarz.main : ∀ {V : Type} [inst : AddCommGroup V] [inst_1 : Module ℂ V] (I : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ), (∀ (x : V), (0 : ℂ) ≤ ((I : V → V →ₗ[ℂ] ℂ) x : V → ℂ) x) → ∀ (x y : V), ‖((I : V → V →ₗ[ℂ] ℂ) x : V → ℂ) y‖ ^ (2 : ℕ) ≤ Complex.re (((I : V → V →ₗ[ℂ] ℂ) x : V → ℂ) x) * Complex.re (((I : V → V →ₗ[ℂ] ℂ) y : V → ℂ) y) :=
  fun I hI x y => GlobalTheory.HermitianCauchySchwarz.cauchy_schwarz I hI x y
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralNonnegOfSums
open MeasureTheory Filter Topology
open scoped ComplexOrder

namespace GlobalTheory.PosDefFT

theorem integral_prod_nonneg (ψ : ℝ → ℂ) (hc : Continuous ψ) (C : ℝ) (hb : ∀ s, ‖ψ s‖ ≤ C)
    (hp : ∀ (k : ℕ) (t : Fin k → ℝ), 0 ≤ ∑ i, ∑ j, ψ (t j - t i))
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    0 ≤ ∫ p : ℝ × ℝ, ψ (p.2 - p.1) ∂(μ.prod μ) := by
  set I := ∫ p : ℝ × ℝ, ψ (p.2 - p.1) ∂(μ.prod μ) with hI
  have key : ∀ k : ℕ, 0 ≤ (k : ℂ) * (ψ 0 - I + k * I) := by
    intro k
    let P : Measure (Fin k → ℝ) := Measure.pi (fun _ => μ)
    have hint : ∀ i j : Fin k, Integrable (fun t : Fin k → ℝ => ψ (t j - t i)) P := by
      intro i j
      refine Integrable.of_bound ?_ C (Eventually.of_forall fun t => hb _)
      exact (hc.comp (by fun_prop)).aestronglyMeasurable
    have hval : ∀ i j : Fin k, ∫ t, ψ (t j - t i) ∂P = (if i = j then ψ 0 - I else 0) + I := by
      intro i j
      by_cases h : i = j
      · subst h
        simp
      · have hind : ProbabilityTheory.iIndepFun (fun (i : Fin k) (t : Fin k → ℝ) => t i) P :=
          ProbabilityTheory.iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
        have h2 := hind.indepFun h
        rw [ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
          (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable] at h2
        have e : ∀ l : Fin k, P.map (fun t => t l) = μ := fun l =>
          (measurePreserving_eval (fun _ : Fin k => μ) l).map_eq
        rw [e, e] at h2
        rw [if_neg h, zero_add, hI, ← h2, integral_map (by fun_prop)]
        exact (hc.comp (by fun_prop)).aestronglyMeasurable
    have h0 : 0 ≤ ∫ t, ∑ i, ∑ j, ψ (t j - t i) ∂P := integral_nonneg (fun t => hp k t)
    rw [MeasureTheory.integral_finsetSum _ (fun i _ => MeasureTheory.integrable_finsetSum _ (fun j _ => hint i j))] at h0
    simp_rw [MeasureTheory.integral_finsetSum _ (fun j _ => hint _ j), hval] at h0
    simpa [Finset.sum_add_distrib, mul_add] using h0
  have key2 : ∀ k : ℕ, 0 ≤ (1 / ((k : ℝ) + 1) : ℝ) • (ψ 0 - I) + I := by
    intro k
    have h1 := key (k + 1)
    have h2 : (0 : ℝ) ≤ (1 / ((k : ℝ) + 1)) ^ 2 := by positivity
    have h3 := smul_nonneg h2 h1
    convert h3 using 1
    have : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    simp only [Complex.real_smul]
    push_cast
    field_simp
  have hlim : Tendsto (fun k : ℕ => (1 / ((k : ℝ) + 1) : ℝ) • (ψ 0 - I) + I) atTop
      (𝓝 ((0 : ℝ) • (ψ 0 - I) + I)) :=
    (tendsto_one_div_add_atTop_nhds_zero_nat.smul_const _).add_const _
  simpa using ge_of_tendsto' hlim key2

theorem integral_nonneg_of_sums (ψ : ℝ → ℂ) (hc : Continuous ψ) (C : ℝ) (hb : ∀ s, ‖ψ s‖ ≤ C)
    (hi : Integrable ψ)
    (hp : ∀ (k : ℕ) (t : Fin k → ℝ), 0 ≤ ∑ i, ∑ j, ψ (t j - t i)) :
    0 ≤ ∫ s, ψ s := by
  let μ : Measure ℝ := volume.restrict (Set.Ioo 0 1)
  haveI : IsProbabilityMeasure μ := ⟨by simp [μ]⟩
  let G : ℕ → ℝ → ℂ := fun n x => ∫ s in (-((n : ℝ) * x))..((n : ℝ) * (1 - x)), ψ s
  have hG : ∀ n x, G n x = (n : ℝ) • ∫ y, ψ ((n : ℝ) * (y - x)) ∂μ := by
    intro n x
    have h := intervalIntegral.smul_integral_comp_mul_sub (f := ψ) (a := 0) (b := 1) (n : ℝ)
      ((n : ℝ) * x)
    rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo] at h
    simp only [G, μ, mul_sub]
    rw [h]
    simp
  have hint : ∀ n : ℕ, Integrable (fun p : ℝ × ℝ => ψ ((n : ℝ) * (p.2 - p.1))) (μ.prod μ) := by
    intro n
    refine Integrable.of_bound ?_ C (Eventually.of_forall fun t => hb _)
    exact (hc.comp (by fun_prop)).aestronglyMeasurable
  have hnn : ∀ n, 0 ≤ ∫ x, G n x ∂μ := by
    intro n
    have h := integral_prod_nonneg (fun s => ψ ((n : ℝ) * s)) (hc.comp (by fun_prop)) C
      (fun s => hb _) (fun k t => by simpa [mul_sub] using hp k (fun i => (n : ℝ) * t i)) μ
    rw [integral_prod _ (hint n)] at h
    simp_rw [hG, integral_smul]
    exact smul_nonneg (Nat.cast_nonneg n) h
  have hlim : Tendsto (fun n => ∫ x, G n x ∂μ) atTop (𝓝 (∫ _x, (∫ s, ψ s) ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => ∫ s, ‖ψ s‖) ?_
      (integrable_const _) ?_ ?_
    · intro n
      have : G n = fun x => (n : ℝ) • ∫ y, ψ ((n : ℝ) * (y - x)) ∂μ := funext (hG n)
      rw [this]
      exact ((hint n).integral_prod_left.smul (n : ℝ)).aestronglyMeasurable
    · intro n
      refine Eventually.of_forall fun x => ?_
      refine (intervalIntegral.norm_integral_le_integral_norm_uIoc).trans ?_
      exact setIntegral_le_integral hi.norm (Eventually.of_forall fun _ => norm_nonneg _)
    · refine (ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun x hx => ?_)
      refine intervalIntegral_tendsto_integral hi ?_ ?_
      · exact tendsto_neg_atTop_atBot.comp
          (tendsto_natCast_atTop_atTop.atTop_mul_const hx.1)
      · exact tendsto_natCast_atTop_atTop.atTop_mul_const (sub_pos.2 hx.2)
  simpa using ge_of_tendsto' hlim hnn

theorem fourier_nonneg : ∀ φ : ℝ → ℂ, Continuous φ →
    (∃ A e : ℝ, 0 < e ∧ ∀ s, ‖φ s‖ ≤ A * Real.exp (-(e * |s|))) →
    (∀ (k : ℕ) (t : Fin k → ℝ) (z : Fin k → ℂ),
      0 ≤ ∑ i, ∑ j, star (z i) * z j * φ (t j - t i)) →
    ∀ ξ : ℝ, 0 ≤ ∫ s : ℝ, Complex.exp (-(Complex.I * ξ * s)) * φ s := by
  rintro φ hc ⟨A, e, he, hb⟩ hp ξ
  have hn : ∀ s : ℝ, ‖Complex.exp (-(Complex.I * ξ * s)) * φ s‖ = ‖φ s‖ := by
    intro s
    rw [norm_mul, Complex.norm_exp]
    simp
  have hc' : Continuous fun s : ℝ => Complex.exp (-(Complex.I * ξ * s)) * φ s := by fun_prop
  have hA : 0 ≤ A := by simpa using (norm_nonneg _).trans (hb 0)
  refine integral_nonneg_of_sums _ hc' A (fun s => ?_) ?_ (fun k t => ?_)
  · rw [hn]
    refine (hb s).trans (mul_le_of_le_one_right hA ?_)
    rw [Real.exp_le_one_iff, neg_nonpos]
    positivity
  · have h1 : IntegrableOn (fun s : ℝ => Real.exp (-(e * |s|))) (Set.Ioi 0) := by
      refine (exp_neg_integrableOn_Ioi 0 he).congr_fun (fun s hs => ?_) measurableSet_Ioi
      simp [abs_of_pos (Set.mem_Ioi.1 hs)]
    have h2 : IntegrableOn (fun s : ℝ => Real.exp (-(e * |s|))) (Set.Iic 0) := by
      refine (integrableOn_exp_mul_Iic he 0).congr_fun (fun s hs => ?_) measurableSet_Iic
      simp [abs_of_nonpos (Set.mem_Iic.1 hs)]
    have h3 : Integrable (fun s : ℝ => Real.exp (-(e * |s|))) := by
      have := h2.union h1
      rwa [Set.Iic_union_Ioi, integrableOn_univ] at this
    refine (h3.const_mul A).mono' hc'.aestronglyMeasurable (Eventually.of_forall fun s => ?_)
    rw [hn]
    exact hb s
  · convert hp k t (fun j => Complex.exp (-(Complex.I * ξ * t j))) using 4 with i _ j _
    rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    simp
    ring

end GlobalTheory.PosDefFT
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoeffEqZeroOfLipschitzUnitaryFlowDecay
open MeasureTheory NumberField Matrix Finset
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.LipFlow

theorem cauchy {V : Type} [AddCommGroup V] [Module ℂ V] (I : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)
    (h : ∀ x, 0 ≤ I x x) (x y : V) : ‖I x y‖ ^ 2 ≤ (I x x).re * (I y y).re := by
  first
  | exact @_root_.GlobalTheory.HermitianCauchySchwarz.main
  | exact _root_.GlobalTheory.HermitianCauchySchwarz.main
  | (apply _root_.GlobalTheory.HermitianCauchySchwarz.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.HermitianCauchySchwarz.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.HermitianCauchySchwarz.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.HermitianCauchySchwarz.main ..)

theorem integrable_exp_abs {e : ℝ} (he : 0 < e) :
    Integrable (fun s : ℝ => Real.exp (-(e * |s|))) := by
  rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (0:ℝ))]
  refine IntegrableOn.union ?_ ?_
  · refine (integrableOn_exp_mul_Iic he 0).congr_fun (fun x hx => ?_) measurableSet_Iic
    simp only [abs_of_nonpos (Set.mem_Iic.1 hx)]
    congr 1; ring
  · refine (exp_neg_integrableOn_Ioi 0 he).congr_fun (fun x hx => ?_) measurableSet_Ioi
    simp only [abs_of_pos (Set.mem_Ioi.1 hx)]
    congr 1; ring

theorem decay_shift {φ : ℝ → ℂ} {A e : ℝ} (he : 0 < e)
    (h : ∀ s, ‖φ s‖ ≤ A * Real.exp (-(e * |s|))) (r t : ℝ) :
    ‖φ (r + t)‖ ≤ A * Real.exp (e * |r|) * Real.exp (-(e * |t|)) := by
  have hA : 0 ≤ A := by
    have := (norm_nonneg _).trans (h 0)
    simpa using this
  refine (h _).trans ?_
  rw [mul_assoc, ← Real.exp_add]
  gcongr
  have : |t| ≤ |r| + |r + t| := by
    have := abs_sub (r + t) r
    simp only [add_sub_cancel_left] at this
    linarith
  nlinarith

theorem integrable_fourier {φ : ℝ → ℂ} (hc : Continuous φ) {A e : ℝ} (he : 0 < e)
    (h : ∀ s, ‖φ s‖ ≤ A * Real.exp (-(e * |s|))) (ξ : ℝ) :
    Integrable (fun s : ℝ => Complex.exp (-(Complex.I * ξ * s)) * φ s) := by
  refine ((integrable_exp_abs he).const_mul A).mono' (by fun_prop) (ae_of_all _ fun s => ?_)
  rw [norm_mul, Complex.norm_exp]
  simpa using h s

theorem fourier_shift (φ : ℝ → ℂ) (ξ r : ℝ) :
    ∫ s : ℝ, Complex.exp (-(Complex.I * ξ * s)) * φ (r + s)
      = Complex.exp (Complex.I * ξ * r) * ∫ s : ℝ, Complex.exp (-(Complex.I * ξ * s)) * φ s := by
  rw [← integral_const_mul,
    ← integral_add_left_eq_self (fun s : ℝ => Complex.exp (Complex.I * ξ * r) *
      (Complex.exp (-(Complex.I * ξ * s)) * φ s)) r]
  congr 1; funext s
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2; push_cast; ring

theorem coeff_eq_zero : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (I : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (U : ℝ → V →ₗ[ℂ] V) (C : ℝ) (v : V), (∀ x, 0 ≤ I x x) → U 0 = LinearMap.id → (∀ s t, U (s + t) = (U s).comp (U t)) → (∀ s x y, I (U s x) (U s y) = I x y) → (∀ s x, |s| ≤ 1 → (I (U s x - x) (U s x - x)).re ≤ C * s ^ 2 * (I x x).re) → (∃ A e : ℝ, 0 < e ∧ ∀ s, ‖I v (U s v)‖ ≤ A * Real.exp (-(e * |s|))) → I v v = 0 := by
  intro V _ _ I U C v hpos h0 hadd hiso hlip ⟨A, e, he, hdec⟩
  set φ : ℝ → ℂ := fun s => I v (U s v) with hφ
  have hU : ∀ s t x, U s (U t x) = U (s + t) x := fun s t x => by rw [hadd]; rfl
  have hre : ∀ x, 0 ≤ (I x x).re := fun x => (Complex.le_def.1 (hpos x)).1
  have him : ∀ x, (I x x).im = 0 := fun x => ((Complex.le_def.1 (hpos x)).2).symm
  have hcont : Continuous φ := by
    rw [continuous_iff_continuousAt]
    intro t
    rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
    have hb : ∀ᶠ u in nhds t, ‖φ u - φ t‖ ≤
        Real.sqrt ((I v v).re * (C * (u - t) ^ 2 * (I v v).re)) := by
      filter_upwards [Metric.closedBall_mem_nhds t one_pos] with u hu
      have hu' : |u - t| ≤ 1 := by simpa [Real.dist_eq] using hu
      apply Real.le_sqrt_of_sq_le
      have e1 : φ u - φ t = I v (U (u - t) (U t v) - U t v) := by
        simp [hφ, hU]
      rw [e1]
      refine (cauchy I hpos _ _).trans ?_
      have := hlip (u - t) (U t v) hu'
      rw [hiso] at this
      exact mul_le_mul_of_nonneg_left this (hre v)
    refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) hb ?_
    have : Continuous fun u : ℝ => Real.sqrt ((I v v).re * (C * (u - t) ^ 2 * (I v v).re)) := by
      fun_prop
    simpa using this.tendsto t
  have hsum : ∀ (k : ℕ) (t : Fin k → ℝ) (z : Fin k → ℂ) (r : ℝ),
      I (∑ i, z i • U (t i) v) (U r (∑ i, z i • U (t i) v))
        = ∑ i, ∑ j, star (z i) * z j * φ (r + (t j - t i)) := by
    intro k t z r
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum (U r), map_sum I, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have : I (U (t i) v) (U r (U (t j) v)) = φ (r + (t j - t i)) := by
      simp only [hφ]
      rw [← hiso (t i) v (U (r + (t j - t i)) v), hU, hU]
      congr 3; ring
    simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, this]
    simp only [RCLike.star_def]
    ring
  have hφpos := GlobalTheory.PosDefFT.fourier_nonneg φ hcont ⟨A, e, he, hdec⟩ (fun k t z => by
    have := hsum k t z 0
    simp only [h0, LinearMap.id_apply, zero_add] at this
    rw [← this]; exact hpos _)
  have hzero : φ = 0 := by
    refine GlobalTheory.eq_zero_of_exp_decay_of_fourier_eq_zero_on_halfLine φ (Real.pi * (|C| + 1)) hcont ⟨A, e, he, hdec⟩ fun ξ hξ => ?_
    have hC : 0 ≤ |C| := abs_nonneg C
    have hξ0 : 0 < ξ := lt_of_lt_of_le (by positivity) hξ
    set s : ℝ := Real.pi / ξ with hs
    have hs0 : 0 < s := by positivity
    have hs1 : s * (|C| + 1) ≤ 1 := by
      rw [hs, div_mul_eq_mul_div, div_le_one hξ0]; exact hξ
    have hs2 : s ≤ 1 := by nlinarith
    have hCs : C * s ^ 2 ≤ 1 := by
      have := le_abs_self C
      nlinarith [mul_nonneg hC hs0.le]
    let ψ : ℝ → ℂ := fun t => ((C * s ^ 2 - 2 : ℝ) : ℂ) * φ t + φ (s + t) + φ (-s + t)
    have hψc : Continuous ψ := by fun_prop
    have hψd : ∀ t, ‖ψ t‖ ≤ (|C * s ^ 2 - 2| * A + A * Real.exp (e * |s|)
        + A * Real.exp (e * |-s|)) * Real.exp (-(e * |t|)) := by
      intro t
      have a1 := decay_shift he hdec s t
      have a2 := decay_shift he hdec (-s) t
      have a3 : ‖((C * s ^ 2 - 2 : ℝ) : ℂ) * φ t‖
          ≤ |C * s ^ 2 - 2| * (A * Real.exp (-(e * |t|))) := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hdec t) (abs_nonneg _)
      refine (norm_add₃_le).trans ?_
      refine (add_le_add (add_le_add a3 a1) a2).trans (le_of_eq (by ring))
    have hψpos := GlobalTheory.PosDefFT.fourier_nonneg ψ hψc ⟨_, e, he, hψd⟩ (fun k t z => by
      set x := ∑ i, z i • U (t i) v with hx
      have b0 := hsum k t z 0
      have b1 := hsum k t z s
      have b2 := hsum k t z (-s)
      rw [← hx] at b0 b1 b2
      simp only [h0, LinearMap.id_apply, zero_add] at b0
      have b3 : I (U s x) x = I x (U (-s) x) := by
        rw [← hiso s x (U (-s) x), hU]; simp [h0]
      have b4 : ∑ i, ∑ j, star (z i) * z j * ψ (t j - t i)
          = ((C * s ^ 2 - 2 : ℝ) : ℂ) * I x x + I x (U s x) + I x (U (-s) x) := by
        rw [b0, b1, b2]
        simp only [ψ, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      have b5 : ((C * s ^ 2 - 2 : ℝ) : ℂ) * I x x + I x (U s x) + I x (U (-s) x)
          = ((C * s ^ 2 : ℝ) : ℂ) * I x x - I (U s x - x) (U s x - x) := by
        simp only [map_sub, LinearMap.sub_apply, hiso, b3]
        push_cast; ring
      rw [b4, b5, Complex.le_def]
      have := hlip s x (by rwa [abs_of_pos hs0])
      constructor
      · rw [Complex.sub_re, Complex.re_ofReal_mul]; simpa using this
      · rw [Complex.sub_im, Complex.im_ofReal_mul, him, him]; simp) ξ
    have i0 := integrable_fourier hcont he hdec ξ
    have i1 := integrable_fourier (φ := fun t => φ (s + t)) (by fun_prop) he
      (decay_shift he hdec s) ξ
    have i2 := integrable_fourier (φ := fun t => φ (-s + t)) (by fun_prop) he
      (decay_shift he hdec (-s)) ξ
    have hξs : Complex.I * ξ * s = Real.pi * Complex.I := by
      have : (ξ : ℂ) * s = Real.pi := by
        rw [← Complex.ofReal_mul, hs, mul_div_cancel₀ _ hξ0.ne']
      rw [← this]; ring
    have hF : ∫ t : ℝ, Complex.exp (-(Complex.I * ξ * t)) * ψ t
        = ((C * s ^ 2 - 4 : ℝ) : ℂ) * ∫ t : ℝ, Complex.exp (-(Complex.I * ξ * t)) * φ t := by
      have : (fun t : ℝ => Complex.exp (-(Complex.I * ξ * t)) * ψ t) = fun t : ℝ =>
          ((C * s ^ 2 - 2 : ℝ) : ℂ) * (Complex.exp (-(Complex.I * ξ * t)) * φ t)
          + Complex.exp (-(Complex.I * ξ * t)) * φ (s + t)
          + Complex.exp (-(Complex.I * ξ * t)) * φ (-s + t) := by
        funext t; simp only [ψ]; ring
      rw [this, integral_add (by exact (i0.const_mul _).add i1) i2, integral_add (i0.const_mul _) i1,
        integral_const_mul, fourier_shift, fourier_shift, hξs]
      have h2 : Complex.I * ξ * ((-s : ℝ) : ℂ) = -(Real.pi * Complex.I) := by
        rw [← hξs]; push_cast; ring
      rw [h2, Complex.exp_neg, Complex.exp_pi_mul_I]
      push_cast; ring
    rw [hF] at hψpos
    have p0 := hφpos ξ
    set F := ∫ t : ℝ, Complex.exp (-(Complex.I * ξ * t)) * φ t
    obtain ⟨p1, p2⟩ := Complex.le_def.1 p0
    have p3 := (Complex.le_def.1 hψpos).1
    rw [Complex.re_ofReal_mul] at p3
    simp only [Complex.zero_re, Complex.zero_im] at p1 p2 p3
    apply Complex.ext
    · simp only [Complex.zero_re]; nlinarith
    · simp [← p2]
  have := congrFun hzero 0
  simpa [hφ, h0] using this

end GlobalTheory.LipFlow
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoeffEqZeroOfLipschitzUnitaryFlowDecayStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_eq_zero_of_lipschitz_unitary_flow_decay : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (I : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (U : ℝ → V →ₗ[ℂ] V) (C : ℝ) (v : V), (∀ x, 0 ≤ I x x) → U 0 = LinearMap.id → (∀ s t, U (s + t) = (U s).comp (U t)) → (∀ s x y, I (U s x) (U s y) = I x y) → (∀ s x, |s| ≤ 1 → (I (U s x - x) (U s x - x)).re ≤ C * s ^ 2 * (I x x).re) → (∃ A e : ℝ, 0 < e ∧ ∀ s, ‖I v (U s v)‖ ≤ A * Real.exp (-(e * |s|))) → I v v = 0 := by
  first | exact @GlobalTheory.LipFlow.coeff_eq_zero | exact GlobalTheory.LipFlow.coeff_eq_zero | (intros; apply GlobalTheory.LipFlow.coeff_eq_zero <;> assumption)
end
