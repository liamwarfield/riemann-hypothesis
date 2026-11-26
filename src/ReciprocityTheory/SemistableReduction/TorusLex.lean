module

public import ReciprocityTheory.SemistableReduction.SphereLogIntegrableStatement

@[expose] public section

section -- merged from ReciprocityTheory.SemistableReduction.TorusLexC
section -- merged from ReciprocityTheory.SemistableReduction.TorusLexB
namespace ReciprocityTheory.MultiplicativeHeights.TorusLexOrder

open MeasureTheory ComplexConjugate

theorem torusProb_isProb (ι : Type) [Fintype ι] : IsProbabilityMeasure (torusProb ι) := by
  constructor
  rw [torusProb, Measure.pi_univ]
  simp [Real.volume_Ioc]

noncomputable def torusFactor (a b : ℕ) (x : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ^ a *
    conj (Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))) ^ b

theorem torus_one_dim (a b : ℕ) :
    ∫ x in Set.Ioc (0 : ℝ) 1, torusFactor a b x = if a = b then 1 else 0 := by
  have key : ∀ x : ℝ, torusFactor a b x =
      Complex.exp ((2 * Real.pi * Complex.I * ((a : ℂ) - b)) * x) := by
    intro x
    simp only [torusFactor, ← Complex.exp_conj, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [← intervalIntegral.integral_of_le zero_le_one]
  simp_rw [key]
  split_ifs with h
  · subst h; simp
  · have hab : ((a : ℂ) - b) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast h)
    have hc : (2 * Real.pi * Complex.I * ((a : ℂ) - b)) ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero ?_) Complex.I_ne_zero) hab
      exact_mod_cast Real.pi_ne_zero
    rw [integral_exp_mul_complex hc]
    have h1 : Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) - b) * ((1 : ℝ) : ℂ)) = 1 := by
      rw [Complex.exp_eq_one_iff]
      exact ⟨(a : ℤ) - b, by push_cast; ring⟩
    rw [h1]; simp

noncomputable def torusMono {ι : Type} [Fintype ι] (θ : ι → ℝ) (s : ι →₀ ℕ) : ℂ :=
  ∏ i, torusPoint θ i ^ s i

theorem norm_torusPoint {ι : Type} (θ : ι → ℝ) (i : ι) : ‖torusPoint θ i‖ = 1 := by
  simp only [torusPoint]
  have h : 2 * (Real.pi : ℂ) * Complex.I * (θ i : ℂ) = ((2 * Real.pi * θ i : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

theorem norm_torusMono {ι : Type} [Fintype ι] (θ : ι → ℝ) (s : ι →₀ ℕ) :
    ‖torusMono θ s‖ = 1 := by
  simp [torusMono, norm_prod, norm_pow, norm_torusPoint]

theorem continuous_torusPoint {ι : Type} : Continuous (fun θ : ι → ℝ => torusPoint θ) := by
  exact continuous_pi fun i => by simp only [torusPoint]; fun_prop

theorem torus_orth {ι : Type} [Fintype ι] (s t : ι →₀ ℕ) :
    ∫ θ, torusMono θ t * conj (torusMono θ s) ∂(torusProb ι) = if t = s then 1 else 0 := by
  classical
  have h : ∀ θ : ι → ℝ, torusMono θ t * conj (torusMono θ s) =
      ∏ i, torusFactor (t i) (s i) (θ i) := by
    intro θ
    simp only [torusMono, torusFactor, torusPoint, map_prod, map_pow, ← Finset.prod_mul_distrib]
  simp_rw [h]
  rw [torusProb, integral_fintype_prod_eq_prod (f := fun i x => torusFactor (t i) (s i) x)]
  simp_rw [torus_one_dim]
  split_ifs with hts
  · subst hts; simp
  · have : ∃ i, t i ≠ s i := by
      by_contra hc; push_neg at hc; exact hts (Finsupp.ext hc)
    obtain ⟨i, hi⟩ := this
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

theorem integrable_of_bdd {ι : Type} [Fintype ι] {E : Type*} [NormedAddCommGroup E]
    {g : (ι → ℝ) → E} (hg : Continuous g) (C : ℝ) (hC : ∀ θ, ‖g θ‖ ≤ C) :
    Integrable g (torusProb ι) := by
  haveI := torusProb_isProb ι
  exact Integrable.of_bound hg.aestronglyMeasurable C (Filter.Eventually.of_forall hC)

theorem eval_torus {ι : Type} [Fintype ι] (f : MvPolynomial ι ℂ) (θ : ι → ℝ) :
    MvPolynomial.eval (torusPoint θ) f = ∑ s ∈ f.support, f.coeff s * torusMono θ s := by
  rw [MvPolynomial.eval_eq']; rfl

theorem norm_eval_torus_le {ι : Type} [Fintype ι] (f : MvPolynomial ι ℂ) (θ : ι → ℝ) :
    ‖MvPolynomial.eval (torusPoint θ) f‖ ≤ ∑ s ∈ f.support, ‖f.coeff s‖ := by
  rw [eval_torus]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [norm_mul, norm_torusMono, mul_one]

theorem continuous_eval_torus {ι : Type} [Fintype ι] (f : MvPolynomial ι ℂ) :
    Continuous (fun θ : ι → ℝ => MvPolynomial.eval (torusPoint θ) f) := by
  exact (MvPolynomial.continuous_eval f).comp continuous_torusPoint

end ReciprocityTheory.MultiplicativeHeights.TorusLexOrder
end

namespace ReciprocityTheory.MultiplicativeHeights.TorusLexOrder

open MeasureTheory ComplexConjugate

private theorem norm_torusMono_eq_one {ι : Type} [Fintype ι] (θ : ι → ℝ) (s : ι →₀ ℕ) :
    ‖torusMono θ s‖ = 1 := by
  unfold torusMono
  rw [norm_prod]
  simp [norm_pow, norm_torusPoint]

private theorem continuous_torusMono' {ι : Type} [Fintype ι] (s : ι →₀ ℕ) :
    Continuous (fun θ : ι → ℝ => torusMono θ s) := by
  have h : ∀ i, Continuous fun θ : ι → ℝ => torusPoint θ i :=
    fun i => (continuous_apply i).comp continuous_torusPoint
  unfold torusMono
  exact continuous_finsetProd _ (fun i _ => (h i).pow _)

theorem integrable_torus_term {ι : Type} [Fintype ι] (f : MvPolynomial ι ℂ) (s : ι →₀ ℕ) :
    Integrable (fun θ => MvPolynomial.eval (torusPoint θ) f * conj (torusMono θ s))
      (torusProb ι) := by
  refine integrable_of_bdd ((continuous_eval_torus f).mul
    (Complex.continuous_conj.comp (continuous_torusMono' s))) (∑ t ∈ f.support, ‖f.coeff t‖)
    (fun θ => ?_)
  have h := norm_eval_torus_le f θ
  simpa [norm_torusMono_eq_one] using h

theorem integrable_mono_term {ι : Type} [Fintype ι] (t s : ι →₀ ℕ) :
    Integrable (fun θ => torusMono θ t * conj (torusMono θ s)) (torusProb ι) := by
  refine integrable_of_bdd ((continuous_torusMono' t).mul
    (Complex.continuous_conj.comp (continuous_torusMono' s))) 1 (fun θ => ?_)
  simp [norm_torusMono_eq_one]

theorem torus_coeff_integral {ι : Type} [Fintype ι] (f : MvPolynomial ι ℂ) (s : ι →₀ ℕ) :
    ∫ θ, MvPolynomial.eval (torusPoint θ) f * conj (torusMono θ s) ∂(torusProb ι) =
      f.coeff s := by
  simp_rw [eval_torus, Finset.sum_mul]
  rw [MeasureTheory.integral_finsetSum _ (fun t _ => by
    simpa [mul_assoc] using (integrable_mono_term t s).const_mul (f.coeff t))]
  simp_rw [mul_assoc, integral_const_mul, torus_orth, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · exact (MvPolynomial.notMem_support_iff.mp h).symm

theorem torus_parseval {ι : Type} [Fintype ι] (f : MvPolynomial ι ℂ) :
    ∫ θ, ‖MvPolynomial.eval (torusPoint θ) f‖ ^ 2 ∂(torusProb ι) =
      ∑ s ∈ f.support, ‖f.coeff s‖ ^ 2 := by
  have key : ∀ θ, ((‖MvPolynomial.eval (torusPoint θ) f‖ ^ 2 : ℝ) : ℂ) =
      ∑ s ∈ f.support, conj (f.coeff s) *
        (MvPolynomial.eval (torusPoint θ) f * conj (torusMono θ s)) := by
    intro θ
    have hc : conj (MvPolynomial.eval (torusPoint θ) f) =
        ∑ s ∈ f.support, conj (f.coeff s) * conj (torusMono θ s) := by
      conv_lhs => rw [eval_torus]
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sum, map_mul]
    push_cast
    rw [show ((‖MvPolynomial.eval (torusPoint θ) f‖ : ℂ)) ^ 2 =
        MvPolynomial.eval (torusPoint θ) f * conj (MvPolynomial.eval (torusPoint θ) f) by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring]
    rw [hc, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    ring
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp_rw [key]
  rw [MeasureTheory.integral_finsetSum _ (fun s _ => (integrable_torus_term f s).const_mul _)]
  simp_rw [integral_const_mul, torus_coeff_integral]
  push_cast
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

theorem torusPoint_fract {ι : Type} (θ : ι → ℝ) :
    torusPoint (fun i => Int.fract (θ i)) = torusPoint θ := by
  funext i
  simp only [torusPoint]
  rw [← Int.self_sub_floor]
  push_cast
  rw [mul_sub, Complex.exp_sub]
  have h : Complex.exp (2 * Real.pi * Complex.I * ((⌊θ i⌋ : ℤ) : ℂ)) = 1 := by
    rw [show 2 * Real.pi * Complex.I * ((⌊θ i⌋ : ℤ) : ℂ) = (⌊θ i⌋ : ℤ) * (2 * Real.pi * Complex.I) by
      ring]
    exact Complex.exp_int_mul_two_pi_mul_I _
  rw [h, div_one]

theorem exists_torus_max {ι : Type} [Fintype ι] (f : MvPolynomial ι ℂ) :
    ∃ θ₀ : ι → ℝ, ∀ θ, ‖MvPolynomial.eval (torusPoint θ) f‖ ≤
      ‖MvPolynomial.eval (torusPoint θ₀) f‖ := by
  obtain ⟨θ₀, -, hθ₀⟩ := (isCompact_univ_pi (fun _ : ι => isCompact_Icc (a := (0 : ℝ)) (b := 1))).exists_isMaxOn
    ⟨fun _ => 0, fun i _ => by simp⟩ (continuous_eval_torus f).norm.continuousOn
  refine ⟨θ₀, fun θ => ?_⟩
  have hmem : (fun i => Int.fract (θ i)) ∈ Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) 1) :=
    fun i _ => ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  have h := isMaxOn_iff.mp hθ₀ _ hmem
  simp only [torusPoint_fract] at h
  exact h

theorem torus_l2_cauchy_of_basic (hBasic : TorusMeanBasicStatement) : TorusL2Cauchy := by
  intro ι _ f
  haveI := torusProb_isProb ι
  obtain ⟨hInt, hMul, hMono⟩ := hBasic ι
  constructor
  · intro hf
    set A := ∑ s ∈ f.support, ‖f.coeff s‖ ^ 2 with hA
    have hApos : 0 < A := by
      obtain ⟨s, hs⟩ := Finset.nonempty_of_ne_empty (mt MvPolynomial.support_eq_empty.mp hf)
      exact Finset.sum_pos' (fun _ _ => by positivity)
        ⟨s, hs, pow_pos (norm_pos_iff.mpr (MvPolynomial.mem_support_iff.mp hs)) 2⟩
    have hq : 0 < Real.exp 1 / A := div_pos (Real.exp_pos 1) hApos
    set r : ℝ := Real.sqrt (Real.exp 1 / A) with hrdef
    have hr : 0 < r := Real.sqrt_pos.mpr hq
    have hr2 : r ^ 2 = Real.exp 1 / A := Real.sq_sqrt hq.le
    have hc : ((r : ℂ)) ≠ 0 := by exact_mod_cast hr.ne'
    have hcn : ‖(r : ℂ)‖ = r := by simp [abs_of_pos hr]
    have hCc : (MvPolynomial.C (r : ℂ) : MvPolynomial ι ℂ) ≠ 0 := by simpa using hc
    have hmean : torusMean (MvPolynomial.C (r : ℂ) * f) = Real.log r + torusMean f := by
      rw [hMul _ _ hCc hf, MvPolynomial.C_apply, hMono, hcn]
    have hpt : ∀ θ, Real.log ‖MvPolynomial.eval (torusPoint θ) (MvPolynomial.C (r : ℂ) * f)‖ ≤
        r ^ 2 / Real.exp 1 * ‖MvPolynomial.eval (torusPoint θ) f‖ ^ 2 / 2 := by
      intro θ
      rw [MvPolynomial.eval_mul, MvPolynomial.eval_C, norm_mul, hcn]
      have hx : 0 ≤ ‖MvPolynomial.eval (torusPoint θ) f‖ := norm_nonneg _
      rcases hx.eq_or_lt with h0 | hpos
      · rw [← h0]; simp
      · have hy : 0 < (r * ‖MvPolynomial.eval (torusPoint θ) f‖) ^ 2 / Real.exp 1 := by positivity
        have h1 := Real.log_le_sub_one_of_pos hy
        rw [Real.log_div (ne_of_gt (by positivity)) (Real.exp_pos 1).ne', Real.log_exp,
          Real.log_pow] at h1
        have e2 : (r * ‖MvPolynomial.eval (torusPoint θ) f‖) ^ 2 / Real.exp 1 =
            r ^ 2 / Real.exp 1 * ‖MvPolynomial.eval (torusPoint θ) f‖ ^ 2 := by ring
        push_cast at h1
        linarith
    have hint2 : Integrable (fun θ => ‖MvPolynomial.eval (torusPoint θ) f‖ ^ 2) (torusProb ι) :=
      integrable_of_bdd ((continuous_eval_torus f).norm.pow 2) ((∑ s ∈ f.support, ‖f.coeff s‖) ^ 2)
        (fun θ => by
          rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          exact pow_le_pow_left₀ (norm_nonneg _) (norm_eval_torus_le f θ) 2)
    have hle : torusMean (MvPolynomial.C (r : ℂ) * f) ≤ r ^ 2 / Real.exp 1 * A / 2 := by
      unfold torusMean
      calc _ ≤ ∫ θ, r ^ 2 / Real.exp 1 * ‖MvPolynomial.eval (torusPoint θ) f‖ ^ 2 / 2 ∂(torusProb ι) :=
            integral_mono (hInt _ (mul_ne_zero hCc hf)) ((hint2.const_mul _).div_const 2) hpt
        _ = r ^ 2 / Real.exp 1 * A / 2 := by
            rw [integral_div, integral_const_mul, torus_parseval]
    have h12 : r ^ 2 / Real.exp 1 * A / 2 = 1 / 2 := by
      rw [hr2]; field_simp
    have hlogr : Real.log r = (1 - Real.log A) / 2 := by
      rw [hrdef, Real.log_sqrt hq.le, Real.log_div (Real.exp_pos 1).ne' hApos.ne', Real.log_exp]
    unfold polyL2
    rw [← hA, Real.log_sqrt hApos.le]
    linarith
  · intro s
    obtain ⟨θ₀, hθ₀⟩ := exists_torus_max f
    refine ⟨θ₀, ?_⟩
    rw [← torus_coeff_integral f s]
    have hb : ∀ᵐ θ ∂(torusProb ι), ‖MvPolynomial.eval (torusPoint θ) f * conj (torusMono θ s)‖ ≤
        ‖MvPolynomial.eval (torusPoint θ₀) f‖ :=
      Filter.Eventually.of_forall (fun θ => by simpa [norm_torusMono_eq_one] using hθ₀ θ)
    simpa using norm_integral_le_of_norm_le_const hb

end ReciprocityTheory.MultiplicativeHeights.TorusLexOrder
end

section -- merged from ReciprocityTheory.SemistableReduction.TorusLexA
namespace ReciprocityTheory.MultiplicativeHeights.TorusLexOrder

private theorem erase_eq_and_apply_eq_iff_eq_add_single {ι : Type} (i : ι) (k : ℕ) (s u : ι →₀ ℕ) (hu : u i = 0) :
    (s.erase i = u ∧ s i = k) ↔ s = u + Finsupp.single i k := by
  classical
  constructor
  · rintro ⟨h1, h2⟩
    ext j
    by_cases hj : j = i
    · subst hj
      simp [hu, h2]
    · have h3 : (s.erase i) j = u j := by rw [h1]
      rw [Finsupp.erase_ne hj] at h3
      simp [Ne.symm hj, h3]
  · rintro rfl
    refine ⟨?_, by simp [hu]⟩
    ext j
    by_cases hj : j = i
    · subst hj
      simp [hu]
    · simp [Finsupp.erase_ne hj]

theorem coeff_coeffIn {ι : Type} (i : ι) (k : ℕ) (f : MvPolynomial ι ℂ) (u : ι →₀ ℕ) :
    (coeffIn i k f).coeff u = if u i = 0 then f.coeff (u + Finsupp.single i k) else 0 := by
  classical
  unfold coeffIn
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  split_ifs with hu
  · have hsp := (erase_eq_and_apply_eq_iff_eq_add_single i k (u + Finsupp.single i k) u hu).mpr rfl
    rw [Finset.sum_eq_single (u + Finsupp.single i k)]
    · rw [if_pos hsp.1]
    · intro t ht hne
      rw [if_neg]
      intro hte
      exact hne ((erase_eq_and_apply_eq_iff_eq_add_single i k t u hu).mp ⟨hte, (Finset.mem_filter.mp ht).2⟩)
    · intro hnot
      rw [if_pos hsp.1]
      by_contra hc
      exact hnot (Finset.mem_filter.mpr ⟨MvPolynomial.mem_support_iff.mpr hc, hsp.2⟩)
  · apply Finset.sum_eq_zero
    intro t _
    rw [if_neg]
    rintro rfl
    exact hu (by simp)

private theorem apply_eq_zero_and_add_single_mem_support_of_coeffIn {ι : Type} (i : ι) (k : ℕ) (f : MvPolynomial ι ℂ)
    (u : ι →₀ ℕ) (hu : u ∈ (coeffIn i k f).support) :
    u i = 0 ∧ u + Finsupp.single i k ∈ f.support := by
  rw [MvPolynomial.mem_support_iff, coeff_coeffIn] at hu
  by_cases h : u i = 0
  · rw [if_pos h] at hu
    exact ⟨h, MvPolynomial.mem_support_iff.mpr hu⟩
  · rw [if_neg h] at hu
    exact absurd rfl hu

private theorem eq_monomial_of_vars_eq_empty {ι : Type} [LinearOrder ι] (g : MvPolynomial ι ℂ)
    (s : ι →₀ ℕ) (hmin : ∀ t ∈ g.support, t ≠ s → ∃ i, (∀ j < i, s j = t j) ∧ s i < t i)
    (hv : g.vars = ∅) : g = MvPolynomial.monomial s (g.coeff s) := by
  classical
  ext u
  rw [MvPolynomial.coeff_monomial]
  split_ifs with h
  · rw [h]
  · by_contra hc
    obtain ⟨i, -, hi⟩ := hmin u (MvPolynomial.mem_support_iff.mpr hc) (Ne.symm h)
    have hmem : i ∈ g.vars := (MvPolynomial.mem_vars_iff_mem_support i).mpr
      ⟨u, MvPolynomial.mem_support_iff.mpr hc,
        Finsupp.mem_support_iff.mpr ((Nat.zero_le _).trans_lt hi).ne'⟩
    rw [hv] at hmem
    simp at hmem

theorem torusLex_of (hBasic : TorusMeanBasicStatement) (hCoeff : TorusCoeffStatement) :
    TorusLexStatement := by
  unfold ReciprocityTheory.MultiplicativeHeights.TorusLexStatement
  intro ι _ _ f s hs hmin
  have base : ∀ (g : MvPolynomial ι ℂ) (s : ι →₀ ℕ),
      (∀ t ∈ g.support, t ≠ s → ∃ i, (∀ j < i, s j = t j) ∧ s i < t i) → g.vars = ∅ →
      Real.log ‖g.coeff s‖ ≤ ReciprocityTheory.MultiplicativeHeights.torusMean g := by
    intro g s hmin hv
    have hg := eq_monomial_of_vars_eq_empty g s hmin hv
    have h1 : ReciprocityTheory.MultiplicativeHeights.torusMean g = Real.log ‖g.coeff s‖ :=
      (congrArg ReciprocityTheory.MultiplicativeHeights.torusMean hg).trans ((hBasic ι).2.2 s _)
    exact h1.ge
  suffices key : ∀ n : ℕ, ∀ (g : MvPolynomial ι ℂ) (s : ι →₀ ℕ), g.vars.card ≤ n →
      s ∈ g.support → (∀ t ∈ g.support, t ≠ s → ∃ i, (∀ j < i, s j = t j) ∧ s i < t i) →
      Real.log ‖g.coeff s‖ ≤ ReciprocityTheory.MultiplicativeHeights.torusMean g from key _ f s le_rfl hs hmin
  intro n
  induction n with
  | zero =>
    intro g s hcard _ hmin
    exact base g s hmin (Finset.card_eq_zero.mp (Nat.le_zero.mp hcard))
  | succ n ih =>
    intro g s hcard hs hmin
    by_cases hv : g.vars = ∅
    · exact base g s hmin hv
    have hne : g.vars.Nonempty := Finset.nonempty_iff_ne_empty.mpr hv
    obtain ⟨i, hiv, himin⟩ : ∃ i ∈ g.vars, ∀ j ∈ g.vars, i ≤ j :=
      ⟨g.vars.min' hne, Finset.min'_mem _ _, fun j hj => Finset.min'_le _ _ hj⟩
    have hlow : ∀ t ∈ g.support, s i ≤ t i := by
      intro t ht
      by_cases hts : t = s
      · rw [hts]
      · obtain ⟨i', hpre, hlt⟩ := hmin t ht hts
        have hi'v : i' ∈ g.vars := (MvPolynomial.mem_vars_iff_mem_support i').mpr
          ⟨t, ht, Finsupp.mem_support_iff.mpr ((Nat.zero_le _).trans_lt hlt).ne'⟩
        rcases (himin i' hi'v).lt_or_eq with h | h
        · exact (hpre i h).le
        · rw [h]
          exact hlt.le
    have h0 : (s.erase i) i = 0 := by simp
    have hsplit : s = s.erase i + Finsupp.single i (s i) :=
      (erase_eq_and_apply_eq_iff_eq_add_single i (s i) s (s.erase i) h0).mp ⟨rfl, rfl⟩
    have hcoef : (coeffIn i (s i) g).coeff (s.erase i) = g.coeff s := by
      rw [coeff_coeffIn, if_pos h0, ← hsplit]
    have hne' : coeffIn i (s i) g ≠ 0 := by
      intro hz
      have h2 := hcoef
      rw [hz, MvPolynomial.coeff_zero] at h2
      exact (MvPolynomial.mem_support_iff.mp hs) h2.symm
    have hs' : s.erase i ∈ (coeffIn i (s i) g).support := by
      rw [MvPolynomial.mem_support_iff, hcoef]
      exact MvPolynomial.mem_support_iff.mp hs
    have hvan : ∀ k', k' < s i → coeffIn i k' g = 0 := by
      intro k' hk'
      unfold coeffIn
      apply Finset.sum_eq_zero
      intro t ht
      obtain ⟨ht1, ht2⟩ := Finset.mem_filter.mp ht
      exact absurd (hlow t ht1) (by omega)
    have hmin' : ∀ t' ∈ (coeffIn i (s i) g).support, t' ≠ s.erase i →
        ∃ j, (∀ l < j, (s.erase i) l = t' l) ∧ (s.erase i) j < t' j := by
      intro t' ht' hne2
      obtain ⟨ht0, ht⟩ := apply_eq_zero_and_add_single_mem_support_of_coeffIn i (s i) g t' ht'
      have hsp := (erase_eq_and_apply_eq_iff_eq_add_single i (s i) (t' + Finsupp.single i (s i)) t' ht0).mpr rfl
      have hts : t' + Finsupp.single i (s i) ≠ s := by
        intro h
        apply hne2
        rw [← hsp.1, h]
      obtain ⟨j, hpre, hlt⟩ := hmin _ ht hts
      have hji : j ≠ i := by
        rintro rfl
        rw [hsp.2] at hlt
        exact lt_irrefl _ hlt
      refine ⟨j, fun l hl => ?_, ?_⟩
      · rw [← hsp.1]
        by_cases hli : l = i
        · simp [hli]
        · rw [Finsupp.erase_ne hli, Finsupp.erase_ne hli]
          exact hpre l hl
      · rw [← hsp.1, Finsupp.erase_ne hji, Finsupp.erase_ne hji]
        exact hlt
    have hvars : (coeffIn i (s i) g).vars ⊆ g.vars.erase i := by
      intro j hj
      obtain ⟨t', ht', hjt⟩ := (MvPolynomial.mem_vars_iff_mem_support j).mp hj
      obtain ⟨ht0, ht⟩ := apply_eq_zero_and_add_single_mem_support_of_coeffIn i (s i) g t' ht'
      have hji : j ≠ i := by
        rintro rfl
        exact (Finsupp.mem_support_iff.mp hjt) ht0
      refine Finset.mem_erase.mpr ⟨hji, (MvPolynomial.mem_vars_iff_mem_support j).mpr ⟨_, ht, ?_⟩⟩
      rw [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm hji),
        add_zero]
      exact Finsupp.mem_support_iff.mp hjt
    have hcard' : (coeffIn i (s i) g).vars.card ≤ n := by
      have h1 := Finset.card_le_card hvars
      rw [Finset.card_erase_of_mem hiv] at h1
      omega
    calc Real.log ‖g.coeff s‖ = Real.log ‖(coeffIn i (s i) g).coeff (s.erase i)‖ := by rw [hcoef]
      _ ≤ ReciprocityTheory.MultiplicativeHeights.torusMean (coeffIn i (s i) g) := ih _ _ hcard' hs' hmin'
      _ ≤ ReciprocityTheory.MultiplicativeHeights.torusMean g := hCoeff ι g i (s i) hne' (Or.inr hvan)

end ReciprocityTheory.MultiplicativeHeights.TorusLexOrder
end

namespace ReciprocityTheory.MultiplicativeHeights

theorem torusLex_holds (hBasic : TorusMeanBasicStatement) (hCoeff : TorusCoeffStatement) :
    TorusLexStatement ∧ TorusL2Cauchy :=
  ⟨TorusLexOrder.torusLex_of hBasic hCoeff, TorusLexOrder.torus_l2_cauchy_of_basic hBasic⟩

end ReciprocityTheory.MultiplicativeHeights
