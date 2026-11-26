module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyTwistedFilteredColimitContinuity

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousTerm
noncomputable section

open NumberField

namespace GlobalTheory.HeckeMellin

variable {I : Type} [Fintype I]

def term (n : I → ℤ) (s : ℂ) (v : I → ℂ) (y : I → ℝ) : ℂ :=
  GlobalTheory.HeckeTheta.gauss n (GlobalTheory.HeckeTheta.dil y v) * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ))

theorem term_zero {n : I → ℤ} (hn : ∃ i, n i ≠ 0) (s : ℂ) (y : I → ℝ) : term n s 0 y = 0 := by
  have : GlobalTheory.HeckeTheta.dil y (0 : I → ℂ) = 0 := by
    funext i; simp [GlobalTheory.HeckeTheta.dil]
  rw [term, this, GlobalTheory.HeckeTheta.gauss_zero hn, zero_mul]

end GlobalTheory.HeckeMellin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeMellinGaussIntegralNonzeroInteger
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralHeckeMellinGaussIntegrandEqProdGamma
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GammaIntegralExpSubstitutionRealLine
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GammaIntegralExpSubstitutionRealLine
open NumberField MeasureTheory

namespace GlobalTheory.HeckeMellin

open Set

theorem integrableOn_cpow_mul_exp_neg_mul {w : ℂ} (hw : 0 < w.re) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (w - 1) * Complex.exp (-((c : ℂ) * x))) (Ioi 0) := by
  have h := Complex.GammaIntegral_convergent hw
  rw [← mul_zero c, ← integrableOn_Ioi_comp_mul_left_iff _ _ hc] at h
  refine (IntegrableOn.congr_fun (h.const_mul (1 / (c : ℂ) ^ (w - 1)))
    (fun t (ht : 0 < t) => ?_) measurableSet_Ioi)
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hc.le ht.le, Complex.ofReal_exp]
  push_cast
  have hne : (c : ℂ) ^ (w - 1) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
    exact Or.inl (Complex.ofReal_ne_zero.mpr hc.ne')
  field_simp

theorem exp_smul_integrand (w : ℂ) (c t : ℝ) :
    |Real.exp t| • (((Real.exp t : ℝ) : ℂ) ^ (w - 1) * Complex.exp (-((c : ℂ) * (Real.exp t : ℝ)))) =
      Complex.exp (w * t) * Complex.exp (-(c * Real.exp t : ℝ)) := by
  rw [abs_of_pos (Real.exp_pos t), Complex.real_smul]
  have hne : ((Real.exp t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_pos t).ne'
  rw [Complex.cpow_def_of_ne_zero hne, ← Complex.ofReal_log (Real.exp_pos t).le, Real.log_exp]
  rw [Complex.ofReal_exp]
  push_cast
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

theorem gamma_integral_exp_substitution :
    ∀ (r : ℝ), 0 < r → ∀ w : ℂ, 0 < w.re → Integrable (fun t : ℝ => Complex.exp (w * t) * Complex.exp (-(2 * Real.pi * r * Real.exp t : ℝ))) ∧ ∫ t : ℝ, Complex.exp (w * t) * Complex.exp (-(2 * Real.pi * r * Real.exp t : ℝ)) = Complex.Gamma w * ((2 * Real.pi * r : ℝ) : ℂ) ^ (-w) := by
  intro r hr w hw
  set c : ℝ := 2 * Real.pi * r with hcdef
  have hc : 0 < c := by positivity
  set g : ℝ → ℂ := fun x => (x : ℂ) ^ (w - 1) * Complex.exp (-((c : ℂ) * x)) with hg
  have himg : Real.exp '' univ = Ioi 0 := by rw [image_univ, Real.range_exp]
  have hder : ∀ x ∈ (univ : Set ℝ), HasDerivWithinAt Real.exp (Real.exp x) univ x :=
    fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt
  have hinj : InjOn Real.exp univ := fun x _ y _ h => Real.exp_injective h
  have hfun : (fun t : ℝ => |Real.exp t| • g (Real.exp t)) =
      fun t : ℝ => Complex.exp (w * t) * Complex.exp (-(c * Real.exp t : ℝ)) := by
    funext t
    exact exp_smul_integrand w c t
  constructor
  · have h1 := (integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ hder hinj g).mp
      (by rw [himg]; exact integrableOn_cpow_mul_exp_neg_mul hw hc)
    rw [hfun, integrableOn_univ] at h1
    exact h1
  · have h2 := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ hder hinj g
    rw [himg, hfun, Measure.restrict_univ] at h2
    rw [← h2, hg, Complex.integral_cpow_mul_exp_neg_mul_Ioi hw hc, one_div,
      Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg hc.le]; exact Real.pi_pos.ne),
      Complex.cpow_neg, mul_comm]

end GlobalTheory.HeckeMellin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GammaIntegralExpSubstitutionRealLineStatement
open NumberField MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gamma_integral_exp_substitution_real_line : ∀ (r : ℝ), 0 < r → ∀ w : ℂ, 0 < w.re → Integrable (fun t : ℝ => Complex.exp (w * t) * Complex.exp (-(2 * Real.pi * r * Real.exp t : ℝ))) ∧ ∫ t : ℝ, Complex.exp (w * t) * Complex.exp (-(2 * Real.pi * r * Real.exp t : ℝ)) = Complex.Gamma w * ((2 * Real.pi * r : ℝ) : ℂ) ^ (-w) := by
  first | exact @GlobalTheory.HeckeMellin.gamma_integral_exp_substitution | exact GlobalTheory.HeckeMellin.gamma_integral_exp_substitution | (intros; apply GlobalTheory.HeckeMellin.gamma_integral_exp_substitution <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralHeckeMellinGaussIntegrandEqProdGamma
open NumberField MeasureTheory

noncomputable section
namespace GlobalTheory.HeckeMellinProd

theorem hmon_real_mul (n : ℤ) (c : ℝ) (z : ℂ) :
    GlobalTheory.HeckeTheta.hmon n ((c : ℂ) * z) = (c : ℂ) ^ n.natAbs * GlobalTheory.HeckeTheta.hmon n z := by
  unfold GlobalTheory.HeckeTheta.hmon
  split_ifs with h
  · rw [map_mul, Complex.conj_ofReal, mul_pow]; congr 2; omega
  · rw [mul_pow]; congr 2; omega

def fac (w : ℂ) (r : ℝ) (t : ℝ) : ℂ :=
  Complex.exp (w * t) * Complex.exp (-(2 * Real.pi * r * Real.exp t : ℝ))

theorem coord (n : ℤ) (s : ℂ) (v : ℂ) (y : ℝ) :
    GlobalTheory.HeckeTheta.hmon n ((Real.exp (y / 2) : ℂ) * v) *
      Complex.exp ((-2 * Real.pi * ‖(Real.exp (y / 2) : ℂ) * v‖ ^ 2 : ℝ) : ℂ) * Complex.exp (s * (y : ℂ)) =
    GlobalTheory.HeckeTheta.hmon n v * fac (s + ((|n| : ℤ) : ℂ) / 2) (‖v‖ ^ 2) y := by
  rw [hmon_real_mul, fac]
  have h1 : ((Real.exp (y / 2) : ℝ) : ℂ) ^ n.natAbs = Complex.exp ((n.natAbs : ℂ) * (y / 2)) := by
    rw [Complex.ofReal_exp, ← Complex.exp_nat_mul]; push_cast; rfl
  have h2 : ‖(Real.exp (y / 2) : ℂ) * v‖ ^ 2 = Real.exp y * ‖v‖ ^ 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow,
      ← Real.exp_nat_mul]; congr 2; push_cast; ring
  have h3 : ((|n| : ℤ) : ℂ) = (n.natAbs : ℂ) := by
    rw [← Int.natCast_natAbs, Int.cast_natCast]
  rw [h1, h2, h3]
  have e1 : ((-2 * Real.pi * (Real.exp y * ‖v‖ ^ 2) : ℝ) : ℂ) = -(((2 * Real.pi * ‖v‖ ^ 2 * Real.exp y) : ℝ) : ℂ) := by
    push_cast; ring
  rw [e1]
  calc _ = GlobalTheory.HeckeTheta.hmon n v * (Complex.exp ((n.natAbs : ℂ) * (y / 2)) * Complex.exp (s * (y : ℂ))) *
        Complex.exp (-(((2 * Real.pi * ‖v‖ ^ 2 * Real.exp y) : ℝ) : ℂ)) := by ring
    _ = _ := by rw [← Complex.exp_add, mul_assoc]; congr 3; ring

theorem term_eq (I : Type) [Fintype I] (n : I → ℤ) (s : ℂ) (v : I → ℂ) (y : I → ℝ) :
    GlobalTheory.HeckeMellin.term n s v y =
      ∏ i, GlobalTheory.HeckeTheta.hmon (n i) (v i) * fac (s + ((|n i| : ℤ) : ℂ) / 2) (‖v i‖ ^ 2) (y i) := by
  unfold GlobalTheory.HeckeMellin.term GlobalTheory.HeckeTheta.gauss GlobalTheory.HeckeTheta.dil
  rw [Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  exact coord (n i) s (v i) (y i)

theorem norm_fac (w : ℂ) (r : ℝ) (t : ℝ) :
    ‖fac w r t‖ = Real.exp (w.re * t) * Real.exp (-(2 * Real.pi * r * Real.exp t)) := by
  rw [fac, norm_mul, Complex.norm_exp, Complex.norm_exp]
  congr 2
  · simp

theorem ofReal_norm_fac (w : ℂ) (r : ℝ) (t : ℝ) :
    ((‖fac w r t‖ : ℝ) : ℂ) = fac (w.re : ℂ) r t := by
  rw [norm_fac, fac]; push_cast; rfl

end GlobalTheory.HeckeMellinProd

namespace GlobalTheory.HeckeMellinProd

theorem fac_int (w : ℂ) (hw : 0 < w.re) (r : ℝ) (hr : 0 < r) :
    Integrable (fac w r) ∧ ∫ t, fac w r t = Complex.Gamma w * ((2 * Real.pi * r : ℝ) : ℂ) ^ (-w) :=
  GlobalTheory.T.gamma_integral_exp_substitution_real_line r hr w hw

theorem norm_fac_int (w : ℂ) (hw : 0 < w.re) (r : ℝ) (hr : 0 < r) :
    ∫ t, ‖fac w r t‖ = Real.Gamma w.re * (2 * Real.pi * r) ^ (-w.re) := by
  have h := (fac_int (w.re : ℂ) (by simpa using hw) r hr).2
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp_rw [ofReal_norm_fac]
  rw [h, Complex.ofReal_mul (Real.Gamma w.re), Complex.ofReal_cpow (by positivity), ← Complex.Gamma_ofReal]
  push_cast; ring_nf

theorem mellin_prod : ∀ (I : Type) [Fintype I] (n : I → ℤ) (s : ℂ), 0 < s.re → ∀ v : I → ℂ, (∀ i, v i ≠ 0) → Integrable (GlobalTheory.HeckeMellin.term n s v) ∧ ∫ y, GlobalTheory.HeckeMellin.term n s v y = ∏ i, GlobalTheory.HeckeTheta.hmon (n i) (v i) * Complex.Gamma (s + ((|n i| : ℤ) : ℂ) / 2) * ((2 * Real.pi * ‖v i‖ ^ 2 : ℝ) : ℂ) ^ (-(s + ((|n i| : ℤ) : ℂ) / 2)) ∧ ∫ y, ‖GlobalTheory.HeckeMellin.term n s v y‖ = ∏ i, ‖v i‖ ^ (n i).natAbs * Real.Gamma (s.re + (|n i| : ℝ) / 2) * (2 * Real.pi * ‖v i‖ ^ 2) ^ (-(s.re + (|n i| : ℝ) / 2)) := by
  intro I _ n s hs v hv
  have hw : ∀ i, 0 < (s + ((|n i| : ℤ) : ℂ) / 2).re := fun i => by
    have : (0 : ℝ) ≤ |((n i : ℤ) : ℝ)| := abs_nonneg _
    simp only [Complex.add_re, Complex.div_re, Complex.intCast_re, Complex.intCast_im]
    norm_num
    positivity
  have hr : ∀ i, 0 < ‖v i‖ ^ 2 := fun i => pow_pos (norm_pos_iff.2 (hv i)) 2
  have hwre : ∀ i, (s + ((|n i| : ℤ) : ℂ) / 2).re = s.re + (|n i| : ℝ) / 2 := fun i => by
    simp [Complex.add_re, Complex.div_re]
  set g : I → ℝ → ℂ := fun i t => GlobalTheory.HeckeTheta.hmon (n i) (v i) * fac (s + ((|n i| : ℤ) : ℂ) / 2) (‖v i‖ ^ 2) t with hg
  have hterm : GlobalTheory.HeckeMellin.term n s v = fun y => ∏ i, g i (y i) := funext (term_eq I n s v)
  have hgi : ∀ i, Integrable (g i) := fun i => ((fac_int _ (hw i) _ (hr i)).1.const_mul _)
  refine ⟨?_, ?_, ?_⟩
  · rw [hterm]; exact Integrable.fintype_prod (μ := fun _ => volume) hgi
  · rw [hterm, integral_fintype_prod_volume_eq_prod g]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [hg]
    rw [integral_const_mul, (fac_int _ (hw i) _ (hr i)).2]; ring
  · have hn : (fun y => ‖GlobalTheory.HeckeMellin.term n s v y‖) = fun y => ∏ i, (fun i t => ‖g i t‖) i (y i) := by
      rw [hterm]; funext y; exact norm_prod _ _
    rw [hn, integral_fintype_prod_volume_eq_prod (fun i t => ‖g i t‖)]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [hg, norm_mul]
    rw [integral_const_mul, norm_fac_int _ (hw i) _ (hr i), GlobalTheory.HeckeTheta.norm_hmon, hwre]; ring

end GlobalTheory.HeckeMellinProd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralHeckeMellinGaussIntegrandEqProdGammaStatement
open NumberField MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_heckeMellinGaussIntegrand_eq_prod_gamma : ∀ (I : Type) [Fintype I] (n : I → ℤ) (s : ℂ), 0 < s.re → ∀ v : I → ℂ, (∀ i, v i ≠ 0) → Integrable (GlobalTheory.HeckeMellin.term n s v) ∧ ∫ y, GlobalTheory.HeckeMellin.term n s v y = ∏ i, GlobalTheory.HeckeTheta.hmon (n i) (v i) * Complex.Gamma (s + ((|n i| : ℤ) : ℂ) / 2) * ((2 * Real.pi * ‖v i‖ ^ 2 : ℝ) : ℂ) ^ (-(s + ((|n i| : ℤ) : ℂ) / 2)) ∧ ∫ y, ‖GlobalTheory.HeckeMellin.term n s v y‖ = ∏ i, ‖v i‖ ^ (n i).natAbs * Real.Gamma (s.re + (|n i| : ℝ) / 2) * (2 * Real.pi * ‖v i‖ ^ 2) ^ (-(s.re + (|n i| : ℝ) / 2)) := by
  first | exact @GlobalTheory.HeckeMellinProd.mellin_prod | exact GlobalTheory.HeckeMellinProd.mellin_prod | (intros; apply GlobalTheory.HeckeMellinProd.mellin_prod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypeProdNormSqEqAbsNormSpan
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypeProdNormSqEqAbsNormSpan
open NumberField MeasureTheory

namespace GlobalTheory.CMTypeNorm

theorem place_bijective {K : Type} [Field K] [NumberField K] {I : Type} {φ : I → K →+* ℂ} (h : GlobalTheory.CMVal.IsCMType φ) :
    Function.Bijective fun i => InfinitePlace.mk (φ i) := by
  constructor
  · intro i j hij
    obtain ⟨k, -, hk⟩ := h (φ j)
    have hj : j = k := hk j (Or.inl rfl)
    have hi : i = k := by
      apply hk i
      rcases InfinitePlace.mk_eq_iff.mp hij with h1 | h1
      · exact Or.inl h1.symm
      · exact Or.inr h1.symm
    rw [hi, hj]
  · intro w
    obtain ⟨k, hk, -⟩ := h w.embedding
    refine ⟨k, ?_⟩
    show InfinitePlace.mk (φ k) = w
    rw [← InfinitePlace.mk_embedding w, InfinitePlace.mk_eq_iff]
    rcases hk with h1 | h1
    · exact Or.inl h1.symm
    · exact Or.inr h1.symm

theorem prod_norm_sq_eq_absNorm :
    ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I] (φ : I → K →+* ℂ),
      GlobalTheory.CMVal.IsCMType φ → ∀ α : 𝓞 K,
        ∏ i, ‖φ i (α : K)‖ ^ 2 = ((Ideal.absNorm (Ideal.span {α}) : ℕ) : ℝ) := by
  intro K _ _ _ I _ φ h α
  have h1 : ∏ i, ‖φ i (α : K)‖ ^ 2 = ∏ w : InfinitePlace K, w (α : K) ^ w.mult := by
    refine Fintype.prod_bijective _ (place_bijective h) _ _ fun i => ?_
    rw [InfinitePlace.apply, IsTotallyComplex.mult_eq]
  rw [h1, InfinitePlace.prod_eq_abs_norm, Ideal.absNorm_span_singleton, ← Algebra.coe_norm_int, Nat.cast_natAbs]
  push_cast
  rfl

end GlobalTheory.CMTypeNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypeProdNormSqEqAbsNormSpanStatement
open NumberField MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmType_prod_norm_sq_eq_absNorm_span : ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I] (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ → ∀ α : 𝓞 K, ∏ i, ‖φ i (α : K)‖ ^ 2 = ((Ideal.absNorm (Ideal.span {α}) : ℕ) : ℝ) := by
  first | exact @GlobalTheory.CMTypeNorm.prod_norm_sq_eq_absNorm | exact GlobalTheory.CMTypeNorm.prod_norm_sq_eq_absNorm | (intros; apply GlobalTheory.CMTypeNorm.prod_norm_sq_eq_absNorm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeMellinGaussIntegralNonzeroInteger
noncomputable section

open NumberField MeasureTheory

namespace GlobalTheory.HeckeMellinOne

theorem hmon_eq_mul (n : ℤ) {z : ℂ} (hz : z ≠ 0) :
    GlobalTheory.HeckeTheta.hmon n z = ((‖z‖ : ℝ) : ℂ) ^ n.natAbs * (z / ((‖z‖ : ℝ) : ℂ)) ^ (-n) := by
  have hn : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hz
  have hc : starRingEnd ℂ z * z = ((‖z‖ : ℝ) : ℂ) ^ 2 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  unfold GlobalTheory.HeckeTheta.hmon
  split_ifs with h
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h
    simp only [Int.toNat_natCast, Int.natAbs_natCast, zpow_neg, zpow_natCast]
    rw [← inv_pow, ← mul_pow]
    congr 1
    field_simp
    linear_combination hc
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, -n = m := ⟨(-n).toNat, by omega⟩
    have hm' : n.natAbs = m := by omega
    rw [hm, hm', Int.toNat_natCast, zpow_natCast, ← mul_pow]
    congr 1
    field_simp

theorem ofReal_prod_cpow {J : Type} (t : Finset J) (f : J → ℝ) (hf : ∀ j, 0 ≤ f j) (w : ℂ) :
    (((∏ j ∈ t, f j : ℝ)) : ℂ) ^ w = ∏ j ∈ t, ((f j : ℝ) : ℂ) ^ w := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (hf a) (Finset.prod_nonneg fun j _ => hf j), ih]

theorem real_factor (r σ a G : ℝ) (k : ℕ) (hr : 0 < r) (hk : (k : ℝ) = a) :
    r ^ k * G * (2 * Real.pi * r ^ 2) ^ (-(σ + a / 2)) =
      (2 * Real.pi) ^ (-(σ + a / 2)) * G * (r ^ 2) ^ (-σ) := by
  subst hk
  have h2π : 0 < 2 * Real.pi := by positivity
  rw [Real.rpow_def_of_pos (by positivity), Real.rpow_def_of_pos h2π, Real.rpow_def_of_pos (by positivity),
    Real.log_mul h2π.ne' (by positivity), Real.log_pow, ← Real.exp_log (pow_pos hr k), Real.log_pow]
  have key : Real.exp (k * Real.log r) * Real.exp ((Real.log (2 * Real.pi) + (2 : ℕ) * Real.log r) * -(σ + k / 2)) =
      Real.exp (Real.log (2 * Real.pi) * -(σ + k / 2)) * Real.exp ((2 : ℕ) * Real.log r * -σ) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; push_cast; ring
  linear_combination G * key

theorem complex_factor (z : ℂ) (hz : z ≠ 0) (n : ℤ) (s G : ℂ) :
    2 * (GlobalTheory.HeckeTheta.hmon n z * G *
      ((2 * Real.pi * ‖z‖ ^ 2 : ℝ) : ℂ) ^ (-(s + ((|n| : ℤ) : ℂ) / 2))) =
      2 * (2 * (Real.pi : ℂ)) ^ (-(s + ((|n| : ℤ) : ℂ) / 2)) * G *
        ((z / ((‖z‖ : ℝ) : ℂ)) ^ (-n) * ((‖z‖ ^ 2 : ℝ) : ℂ) ^ (-s)) := by
  have hr : 0 < ‖z‖ := norm_pos_iff.2 hz
  have h2π : 0 < 2 * Real.pi := by positivity
  have e2 : (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
  have hk : ((n.natAbs : ℕ) : ℂ) = ((|n| : ℤ) : ℂ) := by
    rw [← Int.cast_natCast, Int.natCast_natAbs]
  rw [hmon_eq_mul n hz, e2, ← Complex.cpow_natCast,
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hr.ne'),
    Complex.cpow_def_of_ne_zero (by exact_mod_cast (by positivity : (0:ℝ) < 2 * Real.pi * ‖z‖ ^ 2).ne'),
    Complex.cpow_def_of_ne_zero (by exact_mod_cast h2π.ne'),
    Complex.cpow_def_of_ne_zero (by exact_mod_cast (by positivity : (0:ℝ) < ‖z‖ ^ 2).ne'),
    ← Complex.ofReal_log hr.le, ← Complex.ofReal_log (by positivity), ← Complex.ofReal_log h2π.le,
    ← Complex.ofReal_log (by positivity), Real.log_mul h2π.ne' (by positivity), Real.log_pow, hk]
  have key : Complex.exp (((Real.log ‖z‖ : ℝ) : ℂ) * ((|n| : ℤ) : ℂ)) *
      Complex.exp (((Real.log (2 * Real.pi) + (2 : ℕ) * Real.log ‖z‖ : ℝ) : ℂ) * -(s + ((|n| : ℤ) : ℂ) / 2)) =
      Complex.exp (((Real.log (2 * Real.pi) : ℝ) : ℂ) * -(s + ((|n| : ℤ) : ℂ) / 2)) *
      Complex.exp ((((2 : ℕ) * Real.log ‖z‖ : ℝ) : ℂ) * -s) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; push_cast; ring
  linear_combination (2 * (z / ((‖z‖ : ℝ) : ℂ)) ^ (-n) * G) * key

end GlobalTheory.HeckeMellinOne

namespace GlobalTheory.HeckeMellinOne

theorem real_prod_rpow {J : Type} (t : Finset J) (f : J → ℝ) (hf : ∀ j, 0 ≤ f j) (w : ℝ) :
    (∏ j ∈ t, f j) ^ w = ∏ j ∈ t, f j ^ w := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      Real.mul_rpow (hf a) (Finset.prod_nonneg fun j _ => hf j), ih]

theorem mellin_term : ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I] (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ → ∀ (n : I → ℤ) (s : ℂ), 0 < s.re → ∀ α : 𝓞 K, α ≠ 0 → Integrable (GlobalTheory.HeckeMellin.term n s (GlobalTheory.HeckeTheta.emb φ (α : K))) ∧ 2 ^ Fintype.card I * ∫ y, GlobalTheory.HeckeMellin.term n s (GlobalTheory.HeckeTheta.emb φ (α : K)) y = GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.archFactor n s * GlobalTheory.HeckeStrip.wt φ n (α : K) * ((Ideal.absNorm (Ideal.span {α}) : ℕ) : ℂ) ^ (-s) ∧ ∫ y, ‖GlobalTheory.HeckeMellin.term n s (GlobalTheory.HeckeTheta.emb φ (α : K)) y‖ = (∏ i, (2 * Real.pi) ^ (-(s.re + (|n i| : ℝ) / 2)) * Real.Gamma (s.re + (|n i| : ℝ) / 2)) * ((Ideal.absNorm (Ideal.span {α}) : ℕ) : ℝ) ^ (-s.re) := by
  intro K _ _ _ I _ φ hφ n s hs α hα
  have hαK : (α : K) ≠ 0 := by exact_mod_cast hα
  have hv : ∀ i, GlobalTheory.HeckeTheta.emb φ (α : K) i ≠ 0 := fun i => (map_ne_zero (φ i)).2 hαK
  obtain ⟨hint, hI, hN⟩ := GlobalTheory.T.integral_heckeMellinGaussIntegrand_eq_prod_gamma I n s hs _ hv
  have hnorm := GlobalTheory.T.cmType_prod_norm_sq_eq_absNorm_span K I φ hφ α
  refine ⟨hint, ?_, ?_⟩
  · rw [hI, ← Complex.ofReal_natCast, ← hnorm, ofReal_prod_cpow _ _ (fun i => by positivity),
      ← Finset.card_univ, Finset.pow_card_mul_prod]
    unfold GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.archFactor GlobalTheory.HeckeStrip.wt
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [complex_factor _ (hv i)]
    simp only [GlobalTheory.HeckeTheta.emb]
    ring
  · rw [hN, ← hnorm, real_prod_rpow _ _ (fun i => by positivity), ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    exact real_factor _ _ _ _ _ (norm_pos_iff.2 (hv i)) (by rw [Nat.cast_natAbs, Int.cast_abs])

end GlobalTheory.HeckeMellinOne
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeMellinGaussIntegralNonzeroIntegerStatement
open NumberField MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeMellinGaussIntegral_nonzero_integer : ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I] (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ → ∀ (n : I → ℤ) (s : ℂ), 0 < s.re → ∀ α : 𝓞 K, α ≠ 0 → Integrable (GlobalTheory.HeckeMellin.term n s (GlobalTheory.HeckeTheta.emb φ (α : K))) ∧ 2 ^ Fintype.card I * ∫ y, GlobalTheory.HeckeMellin.term n s (GlobalTheory.HeckeTheta.emb φ (α : K)) y = GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.archFactor n s * GlobalTheory.HeckeStrip.wt φ n (α : K) * ((Ideal.absNorm (Ideal.span {α}) : ℕ) : ℂ) ^ (-s) ∧ ∫ y, ‖GlobalTheory.HeckeMellin.term n s (GlobalTheory.HeckeTheta.emb φ (α : K)) y‖ = (∏ i, (2 * Real.pi) ^ (-(s.re + (|n i| : ℝ) / 2)) * Real.Gamma (s.re + (|n i| : ℝ) / 2)) * ((Ideal.absNorm (Ideal.span {α}) : ℕ) : ℝ) ^ (-s.re) := by
  first | exact @GlobalTheory.HeckeMellinOne.mellin_term | exact GlobalTheory.HeckeMellinOne.mellin_term | (intros; apply GlobalTheory.HeckeMellinOne.mellin_term <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitUnfoldIntegralPartitionOfUnity
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitUnfoldIntegralPartitionOfUnity
open NumberField MeasureTheory

namespace GlobalTheory.OrbitUnfold

theorem hasSum_integral_translate {I : Type} [Fintype I] {U : Type} [Countable U]
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (t : U → I → ℝ) (p : (I → ℝ) → ℝ) (hp : Measurable p) (hp0 : ∀ y, 0 ≤ p y)
    (hsum : ∀ y, HasSum (fun u => p (y - t u)) 1) (h : (I → ℝ) → E) (hh : Integrable h) :
    HasSum (fun u => ∫ y, p y • h (y + t u)) (∫ y, h y) := by
  have key : ∀ u, ∫ y, p y • h (y + t u) = ∫ y, p (y - t u) • h y := by
    intro u
    have := integral_add_right_eq_self (μ := (volume : Measure (I → ℝ)))
      (fun y => p (y - t u) • h y) (t u)
    simpa using this
  simp_rw [key]
  refine hasSum_integral_of_dominated_convergence (fun u y => p (y - t u) * ‖h y‖) ?_ ?_ ?_ ?_ ?_
  · intro u
    exact ((hp.comp (measurable_sub_const (t u))).aestronglyMeasurable).smul
      hh.aestronglyMeasurable
  · intro u
    refine ae_of_all _ (fun y => ?_)
    rw [norm_smul, Real.norm_of_nonneg (hp0 _)]
  · exact ae_of_all _ (fun y => ((hsum y).mul_right ‖h y‖).summable)
  · refine hh.norm.congr (ae_of_all _ (fun y => ?_))
    simp only [((hsum y).mul_right ‖h y‖).tsum_eq, one_mul]
  · refine ae_of_all _ (fun y => ?_)
    simpa using (hsum y).smul_const (h y)

theorem orbit_unfold : ∀ (I : Type) [Fintype I] (U : Type) [Countable U] (t : U → I → ℝ)
    (p : (I → ℝ) → ℝ), Measurable p → (∀ y, 0 ≤ p y) → (∀ y, HasSum (fun u => p (y - t u)) 1) →
    ∀ g : (I → ℝ) → ℂ, Integrable g →
      HasSum (fun u => ∫ y, (p y : ℂ) * g (y + t u)) (∫ y, g y) ∧
      HasSum (fun u => ∫ y, p y * ‖g (y + t u)‖) (∫ y, ‖g y‖) := by
  intro I _ U _ t p hp hp0 hsum g hg
  refine ⟨?_, ?_⟩
  · have := hasSum_integral_translate t p hp hp0 hsum g hg
    simpa [Complex.real_smul] using this
  · have := hasSum_integral_translate t p hp hp0 hsum (fun y => ‖g y‖) hg.norm
    simpa [smul_eq_mul] using this

end GlobalTheory.OrbitUnfold
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitUnfoldIntegralPartitionOfUnityStatement
open NumberField MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbit_unfold_integral_partition_of_unity : ∀ (I : Type) [Fintype I] (U : Type) [Countable U] (t : U → I → ℝ) (p : (I → ℝ) → ℝ), Measurable p → (∀ y, 0 ≤ p y) → (∀ y, HasSum (fun u => p (y - t u)) 1) → ∀ g : (I → ℝ) → ℂ, Integrable g → HasSum (fun u => ∫ y, (p y : ℂ) * g (y + t u)) (∫ y, g y) ∧ HasSum (fun u => ∫ y, p y * ‖g (y + t u)‖) (∫ y, ‖g y‖) := by
  first | exact @GlobalTheory.OrbitUnfold.orbit_unfold | exact GlobalTheory.OrbitUnfold.orbit_unfold | (intros; apply GlobalTheory.OrbitUnfold.orbit_unfold <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumNonzeroIntegersPrincipalIdealsUnits
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumNonzeroIntegersPrincipalIdealsUnits
open NumberField MeasureTheory

namespace GlobalTheory

theorem sum_over_principal_ideals_units (K : Type) [Field K] [NumberField K] (E : Type) [NormedAddCommGroup E] [CompleteSpace E] (f : 𝓞 K → E) : f 0 = 0 → ∀ (c : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal} → E) (β : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal} → (𝓞 K)ˣ → ℝ) (b : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal} → ℝ), (∀ J : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal}, HasSum (fun u : (𝓞 K)ˣ => f ((u : 𝓞 K) * (haveI := J.2.2; Submodule.IsPrincipal.generator J.1))) (c J)) → (∀ (J : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal}) (u : (𝓞 K)ˣ), ‖f ((u : 𝓞 K) * (haveI := J.2.2; Submodule.IsPrincipal.generator J.1))‖ ≤ β J u) → (∀ J, HasSum (β J) (b J)) → Summable b → HasSum f (∑' J, c J) := by
  intro hf0 c β b hc hbd hβ hbs
  classical
  let gen : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal} → 𝓞 K := fun J => haveI := J.2.2; Submodule.IsPrincipal.generator J.1
  have hspan : ∀ J : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal}, Ideal.span {gen J} = J.1 := fun J => by
    haveI := J.2.2
    exact Submodule.IsPrincipal.span_singleton_generator J.1
  have hgen0 : ∀ J : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal}, gen J ≠ 0 := fun J => by
    intro h
    apply J.2.1
    rw [← hspan J, h, Ideal.span_singleton_eq_bot]
  let g : (Σ _ : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal}, (𝓞 K)ˣ) → 𝓞 K := fun p => (p.2 : 𝓞 K) * gen p.1
  have hginj : Function.Injective g := by
    rintro ⟨J, u⟩ ⟨J', u'⟩ h
    simp only [g] at h
    have hJ : J = J' := by
      apply Subtype.ext
      rw [← hspan J, ← hspan J', Ideal.span_singleton_eq_span_singleton]
      have h1 : gen J = ((u⁻¹ * u' : (𝓞 K)ˣ) : 𝓞 K) * gen J' := by
        rw [Units.val_mul, mul_assoc, ← h, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
      rw [h1]
      exact (associated_unit_mul_left _ _ (Units.isUnit _))
    subst hJ
    have hu : u = u' := Units.ext (mul_right_cancel₀ (hgen0 J) h)
    subst hu
    rfl
  have hrange : ∀ x ∉ Set.range g, f x = 0 := by
    intro x hx
    by_cases h0 : x = 0
    · rw [h0, hf0]
    · exfalso
      apply hx
      let J : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal} := ⟨Ideal.span {x}, by rwa [Ne, Ideal.span_singleton_eq_bot], ⟨⟨x, rfl⟩⟩⟩
      have hass : Associated (gen J) x := by
        rw [← Ideal.span_singleton_eq_span_singleton, hspan J]
      obtain ⟨u, hu⟩ := hass
      exact ⟨⟨J, u⟩, by simp only [g]; rw [mul_comm]; exact hu⟩
  have hnorm : Summable (fun p : (Σ _ : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal}, (𝓞 K)ˣ) => β p.1 p.2) := by
    rw [summable_sigma_of_nonneg]
    · refine ⟨fun J => (hβ J).summable, ?_⟩
      simpa [(hβ _).tsum_eq] using hbs
    · intro p
      exact (norm_nonneg _).trans (hbd p.1 p.2)
  have hF : Summable (fun p : (Σ _ : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal}, (𝓞 K)ˣ) => f (g p)) :=
    Summable.of_norm_bounded hnorm (fun p => hbd p.1 p.2)
  have hcs : HasSum c (∑' p : (Σ _ : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal}, (𝓞 K)ˣ), f (g p)) :=
    HasSum.sigma hF.hasSum (fun J => hc J)
  rw [hcs.tsum_eq]
  exact (hginj.hasSum_iff hrange).mp hF.hasSum
end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumNonzeroIntegersPrincipalIdealsUnitsStatement
open NumberField MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_nonzero_integers_principal_ideals_units : ∀ (K : Type) [Field K] [NumberField K] (E : Type) [NormedAddCommGroup E] [CompleteSpace E] (f : 𝓞 K → E), f 0 = 0 → ∀ (c : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal} → E) (β : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal} → (𝓞 K)ˣ → ℝ) (b : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal} → ℝ), (∀ J : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal}, HasSum (fun u : (𝓞 K)ˣ => f ((u : 𝓞 K) * (haveI := J.2.2; Submodule.IsPrincipal.generator J.1))) (c J)) → (∀ (J : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal}) (u : (𝓞 K)ˣ), ‖f ((u : 𝓞 K) * (haveI := J.2.2; Submodule.IsPrincipal.generator J.1))‖ ≤ β J u) → (∀ J, HasSum (β J) (b J)) → Summable b → HasSum f (∑' J, c J) := by
  first | exact @GlobalTheory.sum_over_principal_ideals_units | exact GlobalTheory.sum_over_principal_ideals_units | (intros; apply GlobalTheory.sum_over_principal_ideals_units <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeMellinGaussIntegrandUnitMul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeMellinGaussIntegrandUnitMul
open NumberField MeasureTheory

noncomputable section

namespace GlobalTheory.HeckeShift

theorem hmon_mul_unit {ζ : ℂ} (hζ : ‖ζ‖ = 1) (n : ℤ) (v : ℂ) :
    GlobalTheory.HeckeTheta.hmon n (ζ * v) = ζ ^ (-n) * GlobalTheory.HeckeTheta.hmon n v := by
  have hζ0 : ζ ≠ 0 := by rintro rfl; simp at hζ
  unfold GlobalTheory.HeckeTheta.hmon
  split_ifs with h
  · have hc : starRingEnd ℂ ζ = ζ⁻¹ := by
      rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hζ]; simp
    rw [map_mul, mul_pow, hc, inv_pow, ← zpow_natCast, ← zpow_neg, Int.toNat_of_nonneg h]
  · rw [mul_pow, ← zpow_natCast ζ, Int.toNat_of_nonneg (by omega)]

theorem factor_shift (n : ℤ) (y : ℝ) {z : ℂ} (hz : z ≠ 0) (w : ℂ) :
    GlobalTheory.HeckeTheta.hmon n ((Real.exp (y / 2) : ℂ) * (z * w)) *
                 Complex.exp ((-2 * Real.pi * ‖(Real.exp (y / 2) : ℂ) * (z * w)‖ ^ 2 : ℝ) : ℂ) =
      (z / ((‖z‖ : ℝ) : ℂ)) ^ (-n) *
        (GlobalTheory.HeckeTheta.hmon n ((Real.exp ((y + Real.log (‖z‖ ^ 2)) / 2) : ℂ) * w) *
          Complex.exp ((-2 * Real.pi * ‖(Real.exp ((y + Real.log (‖z‖ ^ 2)) / 2) : ℂ) * w‖ ^ 2 : ℝ) : ℂ)) := by
  have hn0 : (0 : ℝ) < ‖z‖ := norm_pos_iff.2 hz
  have hE : Real.exp ((y + Real.log (‖z‖ ^ 2)) / 2) = Real.exp (y / 2) * ‖z‖ := by
    rw [Real.log_pow, add_div, Real.exp_add]
    congr 1
    rw [show ((2 : ℕ) : ℝ) * Real.log ‖z‖ / 2 = Real.log ‖z‖ by push_cast; ring, Real.exp_log hn0]
  have hzc : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
  have hζ : ‖z / ((‖z‖ : ℝ) : ℂ)‖ = 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm, div_self hn0.ne']
  have hv : (Real.exp (y / 2) : ℂ) * (z * w) =
      (z / ((‖z‖ : ℝ) : ℂ)) * ((Real.exp ((y + Real.log (‖z‖ ^ 2)) / 2) : ℂ) * w) := by
    rw [hE]; push_cast; field_simp
  rw [hv, hmon_mul_unit hζ, norm_mul, hζ, one_mul, mul_assoc]

theorem sum_ulog {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] {I : Type} [Fintype I]
    (φ : I → K →+* ℂ) (hφ : GlobalTheory.CMVal.IsCMType φ) (u : (𝓞 K)ˣ) : ∑ i, GlobalTheory.HeckeTheta.ulog φ u i = 0 := by
  have hbij : Function.Bijective (fun i => InfinitePlace.mk (φ i)) := by
    constructor
    · intro i j hij
      obtain ⟨k, _, hk⟩ := hφ (φ i)
      have hi := hk i (Or.inl rfl)
      rcases InfinitePlace.mk_eq_iff.1 hij with h | h
      · rw [hi, hk j (Or.inl h)]
      · rw [hi, hk j (Or.inr (by rw [← h]; ext x; simp [ComplexEmbedding.conjugate_coe_eq]))]
    · intro w
      obtain ⟨k, hk, _⟩ := hφ w.embedding
      refine ⟨k, ?_⟩
      rcases hk with h | h
      · simp only; rw [← h, InfinitePlace.mk_embedding]
      · simp only; rw [← InfinitePlace.mk_conjugate_eq (φ k), ← h, InfinitePlace.mk_embedding]
  have h0 := NumberField.Units.sum_mult_mul_log u
  rw [← (Equiv.ofBijective _ hbij).sum_comp] at h0
  rw [← h0]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hm : (InfinitePlace.mk (φ i)).mult = 2 :=
    InfinitePlace.mult_isComplex ⟨_, IsTotallyComplex.isComplex _⟩
  simp only [Equiv.ofBijective_apply, InfinitePlace.apply, hm, GlobalTheory.HeckeTheta.ulog, Real.log_pow]

end GlobalTheory.HeckeShift

theorem GlobalTheory.HeckeShift.term_unit_mul : ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I]
    (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ → ∀ (n : I → ℤ) (s : ℂ) (u : (𝓞 K)ˣ) (α : K) (y : I → ℝ),
    GlobalTheory.HeckeMellin.term n s (GlobalTheory.HeckeTheta.emb φ (((u : 𝓞 K) : K) * α)) y =
      GlobalTheory.HeckeStrip.wt φ n ((u : 𝓞 K) : K) *
        GlobalTheory.HeckeMellin.term n s (GlobalTheory.HeckeTheta.emb φ α) (y + GlobalTheory.HeckeTheta.ulog φ u) := by
  intro K _ _ _ I _ φ hφ n s u α y
  have hsum : (∑ i, (y + GlobalTheory.HeckeTheta.ulog φ u) i) = ∑ i, y i := by
    simp only [Pi.add_apply, Finset.sum_add_distrib, GlobalTheory.HeckeShift.sum_ulog φ hφ u, add_zero]
  have hu0 : ((u : 𝓞 K) : K) ≠ 0 := by
    intro h
    exact (Units.ne_zero u) (by exact_mod_cast h)
  unfold GlobalTheory.HeckeMellin.term
  rw [hsum, ← mul_assoc]
  congr 1
  unfold GlobalTheory.HeckeTheta.gauss GlobalTheory.HeckeStrip.wt
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [GlobalTheory.HeckeTheta.dil, GlobalTheory.HeckeTheta.emb, GlobalTheory.HeckeTheta.ulog, Pi.add_apply, map_mul]
  exact GlobalTheory.HeckeShift.factor_shift (n i) (y i) ((map_ne_zero _).2 hu0) (φ i α)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeMellinGaussIntegrandUnitMulStatement
open NumberField MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeMellinGaussIntegrand_unit_mul : ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I] (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ → ∀ (n : I → ℤ) (s : ℂ) (u : (𝓞 K)ˣ) (α : K) (y : I → ℝ), GlobalTheory.HeckeMellin.term n s (GlobalTheory.HeckeTheta.emb φ (((u : 𝓞 K) : K) * α)) y = GlobalTheory.HeckeStrip.wt φ n ((u : 𝓞 K) : K) * GlobalTheory.HeckeMellin.term n s (GlobalTheory.HeckeTheta.emb φ α) (y + GlobalTheory.HeckeTheta.ulog φ u) := by
  first | exact @GlobalTheory.HeckeShift.term_unit_mul | exact GlobalTheory.HeckeShift.term_unit_mul | (intros; apply GlobalTheory.HeckeShift.term_unit_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumIntegralThetaMellinInterchange
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumIntegralThetaMellinInterchange
noncomputable section

open NumberField MeasureTheory

namespace GlobalTheory.HeckeMellin

theorem hasSum_integral_theta (I : Type) [Fintype I] (ι : Type) [Countable ι] (e : ι → I → ℂ) (a : ι → ℂ) (C : ℝ)
    (hC : ∀ j, ‖a j‖ ≤ C) (n : I → ℤ) (s : ℂ) (p : (I → ℝ) → ℝ) (hp : Measurable p) (hp0 : ∀ y, 0 ≤ p y)
    (hp1 : ∀ y, p y ≤ 1) (hint : ∀ j, Integrable (GlobalTheory.HeckeMellin.term n s (e j)))
    (hsum : Summable (fun j => ∫ y, p y * ‖GlobalTheory.HeckeMellin.term n s (e j) y‖)) :
    HasSum (fun j => a j * ∫ y, (p y : ℂ) * GlobalTheory.HeckeMellin.term n s (e j) y)
      (∫ y, (p y : ℂ) * GlobalTheory.HeckeTheta.theta e a n y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ))) := by
  set F : ι → (I → ℝ) → ℂ := fun j y => a j * ((p y : ℂ) * term n s (e j) y) with hF
  have hpm : AEStronglyMeasurable (fun y => (p y : ℂ)) volume :=
    (Complex.measurable_ofReal.comp hp).aestronglyMeasurable
  have hpb : ∀ᵐ y ∂(volume : Measure (I → ℝ)), ‖(p y : ℂ)‖ ≤ 1 := by
    refine Filter.Eventually.of_forall fun y => ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp0 y)]; exact hp1 y
  have hpint : ∀ j, Integrable (fun y => (p y : ℂ) * term n s (e j) y) :=
    fun j => (hint j).bdd_mul hpm hpb
  have hFint : ∀ j, Integrable (F j) := fun j => (hpint j).const_mul (a j)
  have hnorm : ∀ j y, ‖F j y‖ = ‖a j‖ * (p y * ‖term n s (e j) y‖) := by
    intro j y
    simp only [hF, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp0 y)]
  have hFsum : Summable fun j => ∫ y, ‖F j y‖ := by
    have hi : ∀ j, ∫ y, ‖F j y‖ = ‖a j‖ * ∫ y, p y * ‖term n s (e j) y‖ := by
      intro j; simp_rw [hnorm]; exact integral_const_mul _ _
    refine Summable.of_nonneg_of_le (fun j => integral_nonneg fun y => norm_nonneg _) (fun j => ?_) (hsum.mul_left C)
    rw [hi]
    exact mul_le_mul_of_nonneg_right (hC j)
      (integral_nonneg fun y => mul_nonneg (hp0 y) (norm_nonneg _))
  have h := hasSum_integral_of_summable_integral_norm hFint hFsum
  have hl : (fun j => ∫ y, F j y) = fun j => a j * ∫ y, (p y : ℂ) * term n s (e j) y := by
    funext j; exact integral_const_mul _ _
  have hr : (fun y => ∑' j, F j y) =
      fun y => (p y : ℂ) * GlobalTheory.HeckeTheta.theta e a n y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ)) := by
    funext y
    simp only [hF, GlobalTheory.HeckeTheta.theta, term]
    rw [← tsum_mul_left, ← tsum_mul_right]
    congr 1; funext j; ring
  rw [hl, hr] at h
  exact h

end GlobalTheory.HeckeMellin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumIntegralThetaMellinInterchangeStatement
open NumberField MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_integral_theta_mellin_interchange : ∀ (I : Type) [Fintype I] (ι : Type) [Countable ι] (e : ι → I → ℂ) (a : ι → ℂ) (C : ℝ), (∀ j, ‖a j‖ ≤ C) → ∀ (n : I → ℤ) (s : ℂ) (p : (I → ℝ) → ℝ), Measurable p → (∀ y, 0 ≤ p y) → (∀ y, p y ≤ 1) → (∀ j, Integrable (GlobalTheory.HeckeMellin.term n s (e j))) → Summable (fun j => ∫ y, p y * ‖GlobalTheory.HeckeMellin.term n s (e j) y‖) → HasSum (fun j => a j * ∫ y, (p y : ℂ) * GlobalTheory.HeckeMellin.term n s (e j) y) (∫ y, (p y : ℂ) * GlobalTheory.HeckeTheta.theta e a n y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ))) := by
  first | exact @GlobalTheory.HeckeMellin.hasSum_integral_theta | exact GlobalTheory.HeckeMellin.hasSum_integral_theta | (intros; apply GlobalTheory.HeckeMellin.hasSum_integral_theta <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchFactorMulPSeriesEqIntegral
noncomputable section

open NumberField MeasureTheory

namespace GlobalTheory.HeckeMellin

theorem archFactor_mul_pSeries_eq_integral : ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I] (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ → ∀ (n : I → ℤ), (∃ i, n i ≠ 0) → ∀ (F : NumberField.RingOfIntegers K → ℂ) (C : ℝ), (∀ α, ‖F α‖ ≤ C) → (∀ (u : (NumberField.RingOfIntegers K)ˣ) (α : NumberField.RingOfIntegers K), F ((u : NumberField.RingOfIntegers K) * α) * GlobalTheory.HeckeStrip.wt φ n (((u : NumberField.RingOfIntegers K) * α : NumberField.RingOfIntegers K) : K) = F α * GlobalTheory.HeckeStrip.wt φ n (α : K)) → ∀ p : (I → ℝ) → ℝ, Measurable p → (∀ y, 0 ≤ p y) → (∀ y, HasSum (fun u : (NumberField.RingOfIntegers K)ˣ => p (y + GlobalTheory.HeckeTheta.ulog φ u)) 1) → ∀ s : ℂ, 1 < s.re → GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.archFactor n s * GlobalTheory.HeckeStrip.pSeries F φ n s = 2 ^ Fintype.card I * ∫ y, (p y : ℂ) * GlobalTheory.HeckeTheta.theta (fun α : NumberField.RingOfIntegers K => GlobalTheory.HeckeTheta.emb φ (α : K)) F n y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ)) := by
  intro K _ _ _ I _ φ hφ n hn F C hF hinv p hp hp0 hsum s hs
  haveI : Countable (𝓞 K) := (RingOfIntegers.basis K).equivFun.injective.countable
  haveI : Countable (𝓞 K)ˣ := (Units.val_injective (α := 𝓞 K)).countable
  have hs0 : 0 < s.re := by linarith
  set tm : 𝓞 K → (I → ℝ) → ℂ := fun α => GlobalTheory.HeckeMellin.term n s (GlobalTheory.HeckeTheta.emb φ (α : K)) with htm
  have hulog_inv : ∀ u : (𝓞 K)ˣ, GlobalTheory.HeckeTheta.ulog φ u⁻¹ = - GlobalTheory.HeckeTheta.ulog φ u := by
    intro u; funext i
    simp only [GlobalTheory.HeckeTheta.ulog, Pi.neg_apply]
    rw [← Real.log_inv, ← inv_pow, ← norm_inv, ← map_inv₀]
    congr 4
    have h := congrArg (fun x : 𝓞 K => (x : K)) (Units.inv_mul u)
    push_cast at h
    exact eq_inv_of_mul_eq_one_left h
  have hsum' : ∀ y, HasSum (fun u : (𝓞 K)ˣ => p (y - GlobalTheory.HeckeTheta.ulog φ u)) 1 := by
    intro y
    rw [← (Equiv.inv (𝓞 K)ˣ).hasSum_iff]
    simpa [Function.comp_def, hulog_inv, sub_neg_eq_add] using hsum y
  have hp1 : ∀ y, p y ≤ 1 := fun y => by
    have h := le_hasSum (hsum y) 1 (fun u _ => hp0 _)
    have h1 : GlobalTheory.HeckeTheta.ulog φ (1 : (𝓞 K)ˣ) = 0 := by funext i; simp [GlobalTheory.HeckeTheta.ulog]
    simpa [h1] using h
  have hemb0 : GlobalTheory.HeckeTheta.emb φ ((0 : 𝓞 K) : K) = 0 := by funext i; simp [GlobalTheory.HeckeTheta.emb]
  have htm0 : tm 0 = 0 := by funext y; simp only [htm, hemb0, GlobalTheory.HeckeMellin.term_zero hn]; rfl
  have hint : ∀ α : 𝓞 K, Integrable (tm α) := by
    intro α
    by_cases h : α = 0
    · subst h; rw [htm0]; exact integrable_zero _ _ _
    · exact (GlobalTheory.T.heckeMellinGaussIntegral_nonzero_integer K I φ hφ n s hs0 α h).1
  have hshift : ∀ (u : (𝓞 K)ˣ) (α : 𝓞 K) y, tm ((u : 𝓞 K) * α) y =
      GlobalTheory.HeckeStrip.wt φ n ((u : 𝓞 K) : K) * tm α (y + GlobalTheory.HeckeTheta.ulog φ u) := by
    intro u α y
    have : (((u : 𝓞 K) * α : 𝓞 K) : K) = ((u : 𝓞 K) : K) * (α : K) := by push_cast; rfl
    simp only [htm, this]
    exact GlobalTheory.T.heckeMellinGaussIntegrand_unit_mul K I φ hφ n s u α y
  have hwtu : ∀ u : (𝓞 K)ˣ, ‖GlobalTheory.HeckeStrip.wt φ n ((u : 𝓞 K) : K)‖ = 1 := fun u =>
    GlobalTheory.HeckeStrip.norm_wt φ n (by
      have := u.ne_zero
      exact_mod_cast this)
  have hgen : ∀ J : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal}, (haveI := J.2.2; Submodule.IsPrincipal.generator J.1) ≠ 0 := by
    intro J h
    haveI := J.2.2
    exact J.2.1 ((Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero J.1).2 h)
  have hspan : ∀ J : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal}, Ideal.span {(haveI := J.2.2; Submodule.IsPrincipal.generator J.1)} = J.1 := by
    intro J; haveI := J.2.2; exact Ideal.span_singleton_generator J.1

  have horb : ∀ g : 𝓞 K, g ≠ 0 → HasSum (fun u : (𝓞 K)ˣ => ∫ y, p y * ‖tm ((u : 𝓞 K) * g) y‖) (∫ y, ‖tm g y‖) ∧
      HasSum (fun u : (𝓞 K)ˣ => F ((u : 𝓞 K) * g) * ∫ y, (p y : ℂ) * tm ((u : 𝓞 K) * g) y) (F g * ∫ y, tm g y) := by
    intro g hg
    have hO := GlobalTheory.T.orbit_unfold_integral_partition_of_unity I (𝓞 K)ˣ (GlobalTheory.HeckeTheta.ulog φ) p hp hp0 hsum' (tm g) (hint g)
    constructor
    · refine (congrArg (fun f => HasSum f _) (funext fun u => ?_)).mpr hO.2
      simp only [hshift, norm_mul, hwtu, one_mul]
    · refine (congrArg (fun f => HasSum f _) (funext fun u => ?_)).mpr (hO.1.mul_left (F g))
      have hw : F ((u : 𝓞 K) * g) * GlobalTheory.HeckeStrip.wt φ n ((u : 𝓞 K) : K) = F g := by
        have h1 := hinv u g
        have hgK : (g : K) ≠ 0 := by exact_mod_cast hg
        have : (((u : 𝓞 K) * g : 𝓞 K) : K) = ((u : 𝓞 K) : K) * (g : K) := by push_cast; rfl
        rw [this, GlobalTheory.HeckeStrip.wt_mul] at h1
        have hne : GlobalTheory.HeckeStrip.wt φ n (g : K) ≠ 0 := by
          rw [← norm_ne_zero_iff, GlobalTheory.HeckeStrip.norm_wt φ n hgK]; exact one_ne_zero
        exact mul_right_cancel₀ hne (by rw [mul_assoc, h1])
      simp only [hshift]
      rw [← hw, mul_assoc]
      congr 1
      rw [← integral_const_mul]
      congr 1; funext y; ring

  set cst : ℝ := ∏ i, (2 * Real.pi) ^ (-(s.re + (|n i| : ℝ) / 2)) * Real.Gamma (s.re + (|n i| : ℝ) / 2) with hcst
  have hnorm : ∀ J : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal}, ∫ y, ‖tm (haveI := J.2.2; Submodule.IsPrincipal.generator J.1) y‖ = cst * ((Ideal.absNorm J.1 : ℕ) : ℝ) ^ (-s.re) := by
    intro J
    rw [(GlobalTheory.T.heckeMellinGaussIntegral_nonzero_integer K I φ hφ n s hs0 _ (hgen J)).2.2, hspan J]
  have hb : Summable (fun J : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal} => ∫ y, ‖tm (haveI := J.2.2; Submodule.IsPrincipal.generator J.1) y‖) := by
    simp only [hnorm]
    exact (((ReciprocityTheory.Cheb.summable_absNorm_rpow_ideal K hs).comp_injective Subtype.val_injective).mul_left cst)
  have hR := GlobalTheory.T.sum_nonzero_integers_principal_ideals_units K ℝ (fun α => ∫ y, p y * ‖tm α y‖) (by simp [htm0])
    (fun J => ∫ y, ‖tm (haveI := J.2.2; Submodule.IsPrincipal.generator J.1) y‖) (fun J u => ∫ y, p y * ‖tm ((u : 𝓞 K) * (haveI := J.2.2; Submodule.IsPrincipal.generator J.1)) y‖)
    (fun J => ∫ y, ‖tm (haveI := J.2.2; Submodule.IsPrincipal.generator J.1) y‖) (fun J => (horb _ (hgen J)).1)
    (fun J u => le_of_eq (Real.norm_of_nonneg (integral_nonneg fun y => mul_nonneg (hp0 y) (norm_nonneg _))))
    (fun J => (horb _ (hgen J)).1) hb
  have hI := GlobalTheory.T.hasSum_integral_theta_mellin_interchange I (𝓞 K) (fun α => GlobalTheory.HeckeTheta.emb φ (α : K)) F C hF n s p hp hp0 hp1 hint hR.summable
  have hU := GlobalTheory.T.sum_nonzero_integers_principal_ideals_units K ℂ (fun α => F α * ∫ y, (p y : ℂ) * tm α y) (by simp [htm0])
    (fun J => F (haveI := J.2.2; Submodule.IsPrincipal.generator J.1) * ∫ y, tm (haveI := J.2.2; Submodule.IsPrincipal.generator J.1) y) (fun J u => C * ∫ y, p y * ‖tm ((u : 𝓞 K) * (haveI := J.2.2; Submodule.IsPrincipal.generator J.1)) y‖)
    (fun J => C * ∫ y, ‖tm (haveI := J.2.2; Submodule.IsPrincipal.generator J.1) y‖) (fun J => (horb _ (hgen J)).2)
    (fun J u => by
      rw [norm_mul]
      refine mul_le_mul (hF _) ((norm_integral_le_integral_norm _).trans (le_of_eq ?_)) (norm_nonneg _)
        ((norm_nonneg _).trans (hF 0))
      congr 1; funext y; rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hp0 y)])
    (fun J => (horb _ (hgen J)).1.mul_left C) (hb.mul_left C)
  rw [hI.unique hU, GlobalTheory.HeckeStrip.pSeries, ← tsum_mul_left, ← tsum_mul_left]
  congr 1; funext J
  have h3 := (GlobalTheory.T.heckeMellinGaussIntegral_nonzero_integer K I φ hφ n s hs0 _ (hgen J)).2.1
  rw [hspan J] at h3
  simp only [GlobalTheory.HeckeStrip.pval]
  linear_combination (-F (haveI := J.2.2; Submodule.IsPrincipal.generator J.1)) * h3

end GlobalTheory.HeckeMellin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchFactorMulPSeriesEqIntegralStatement
open NumberField MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archFactor_mul_pSeries_eq_integral_alt : ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I] (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ → ∀ (n : I → ℤ), (∃ i, n i ≠ 0) → ∀ (F : NumberField.RingOfIntegers K → ℂ) (C : ℝ), (∀ α, ‖F α‖ ≤ C) → (∀ (u : (NumberField.RingOfIntegers K)ˣ) (α : NumberField.RingOfIntegers K), F ((u : NumberField.RingOfIntegers K) * α) * GlobalTheory.HeckeStrip.wt φ n (((u : NumberField.RingOfIntegers K) * α : NumberField.RingOfIntegers K) : K) = F α * GlobalTheory.HeckeStrip.wt φ n (α : K)) → ∀ p : (I → ℝ) → ℝ, Measurable p → (∀ y, 0 ≤ p y) → (∀ y, HasSum (fun u : (NumberField.RingOfIntegers K)ˣ => p (y + GlobalTheory.HeckeTheta.ulog φ u)) 1) → ∀ s : ℂ, 1 < s.re → GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.archFactor n s * GlobalTheory.HeckeStrip.pSeries F φ n s = 2 ^ Fintype.card I * ∫ y, (p y : ℂ) * GlobalTheory.HeckeTheta.theta (fun α : NumberField.RingOfIntegers K => GlobalTheory.HeckeTheta.emb φ (α : K)) F n y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ)) := by
  first | exact @GlobalTheory.HeckeMellin.archFactor_mul_pSeries_eq_integral | exact GlobalTheory.HeckeMellin.archFactor_mul_pSeries_eq_integral | (intros; apply GlobalTheory.HeckeMellin.archFactor_mul_pSeries_eq_integral <;> assumption)
end
