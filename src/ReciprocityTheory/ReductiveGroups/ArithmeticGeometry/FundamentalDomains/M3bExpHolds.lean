module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajorantConjugateTransfer
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourIndep

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FrequencyIndexing
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.TubeFourierExpansion
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.TubeSummability
namespace ReciprocityTheory.ChartRestriction.G.FD.TubeSummability

open NumberField Complex MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
  ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity ReciprocityTheory.ChartRestriction.G.FD.RealEmbeddingCharacters
  ReciprocityTheory.ChartRestriction.G.FD.FlowMeanContinuity ReciprocityTheory.L2DbarEstimates.Y
open scoped ComplexConjugate

lemma summable_exp_abs (c : ℝ) (hc : 0 < c) :
    ∀ n : ℕ, Summable (fun k : Fin n → ℤ => Real.exp (-c * ∑ j, |(k j : ℝ)|)) := by
  have hgeo : Summable (fun m : ℕ => Real.exp (-c) ^ m) :=
    summable_geometric_of_lt_one (Real.exp_pos _).le (by simpa using Real.exp_lt_exp.2 (by linarith : -c < 0))
  have h1 : Summable (fun m : ℤ => Real.exp (-c * |(m : ℝ)|)) := by
    apply Summable.of_nat_of_neg
    · refine hgeo.congr fun m => ?_
      simp only [Function.comp, Int.cast_natCast, Nat.abs_cast]
      rw [← Real.exp_nat_mul]
      ring_nf
    · refine hgeo.congr fun m => ?_
      simp only [Int.cast_neg, Int.cast_natCast, abs_neg, Nat.abs_cast]
      rw [← Real.exp_nat_mul]
      ring_nf
  intro n
  induction n with
  | zero => exact Summable.of_finite
  | succ n ih =>
    rw [← (Fin.consEquiv fun _ : Fin (n + 1) => ℤ).summable_iff]
    convert h1.mul_of_nonneg ih (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le) using 1
    funext p
    simp [Fin.consEquiv, Fin.sum_univ_succ, mul_add, Real.exp_add]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

section line

variable (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (ξ : Fin r → E) (x : Frame X.Ψ r)
  {n : ℕ} (ω : Fin n → X.Ψ → ℝ)

def Lc (t : Fin n → ℂ) : X.Ψ → ℂ := fun τ => ∑ j, t j * (ω j τ : ℂ)

noncomputable def hline (t : Fin n → ℂ) : ℂ := P (X.flow ξ (Lc X ω t) x)

def Om : Set (Fin n → ℝ) := (Fintype.linearCombination ℝ ω) ⁻¹' admissibleImaginary X ξ x

lemma lincomb_apply (y : Fin n → ℝ) (τ : X.Ψ) :
    Fintype.linearCombination ℝ ω y τ = ∑ j, y j * ω j τ := by
  simp [Fintype.linearCombination_apply, Finset.sum_apply]

lemma Lc_im (t : Fin n → ℂ) :
    (fun τ => (Lc X ω t τ).im) = Fintype.linearCombination ℝ ω (fun j => (t j).im) := by
  funext τ
  rw [lincomb_apply]
  simp [Lc, Complex.im_sum]

variable {X ξ x}

lemma flow_Lc_mem_dom (hξ : herm X.Gm ξ ξ = 0) (hx : x ∈ X.dom) (t : Fin n → ℂ) :
    X.flow ξ (Lc X ω t) x ∈ X.dom ↔ t ∈ tube n (Om X ξ x ω) := by
  rw [flow_mem_dom_iff (X := X) hξ x hx, Lc_im]
  rfl

lemma Om_open_convex (hx : x ∈ X.dom) : IsOpen (Om X ξ x ω) ∧ Convex ℝ (Om X ξ x ω) := by
  have hc : Continuous (Fintype.linearCombination ℝ ω) := LinearMap.continuous_of_finiteDimensional _
  obtain ⟨ho, hcv⟩ := admissibleImaginary_open_convex (X := X) (ξ := ξ) x hx
  exact ⟨ho.preimage hc, hcv.linear_preimage _⟩

lemma zero_mem_Om (hξ : herm X.Gm ξ ξ = 0) (hx : x ∈ X.dom) : (0 : Fin n → ℝ) ∈ Om X ξ x ω := by
  have h0 := (flow_mem_dom_iff (X := X) hξ x hx 0).1 (by rw [flow_zero]; exact hx)
  show Fintype.linearCombination ℝ ω 0 ∈ admissibleImaginary X ξ x
  rw [map_zero]
  simp only [Pi.zero_apply, Complex.zero_im] at h0
  exact h0

variable (X ξ x)

lemma hline_diff (hP : X.IsSec la P) (hξ : herm X.Gm ξ ξ = 0) (hx : x ∈ X.dom) :
    DifferentiableOn ℂ (hline X P ξ x ω) (tube n (Om X ξ x ω)) := by
  intro t ht
  have hmem : X.flow ξ (Lc X ω t) x ∈ X.dom := (flow_Lc_mem_dom ω hξ hx t).2 ht
  have hLc : Differentiable ℂ (fun t : Fin n → ℂ => Lc X ω t) :=
    differentiable_pi.2 fun τ => Differentiable.fun_sum fun j _ =>
      (differentiable_apply j).mul_const _
  have hd1 : DifferentiableAt ℂ (fun t => X.flow ξ (Lc X ω t) x) t :=
    (flow_differentiable X ξ x).differentiableAt.comp t (hLc t)
  exact (hP.1 _ hmem).comp t hd1.differentiableWithinAt
    (fun t' ht' => (flow_Lc_mem_dom ω hξ hx t').2 ht')

lemma hline_periodic (hP : X.IsSec la P) (hξΛ : ξ ∈ X.Λ) (hξ : herm X.Gm ξ ξ = 0)
    (hx : x ∈ X.dom) (hωp : ∀ j, ω j ∈ X.periods la) :
    ∀ t ∈ tube n (Om X ξ x ω), ∀ m : Fin n → ℤ,
      hline X P ξ x ω (t + fun j => (m j : ℂ)) = hline X P ξ x ω t := by
  intro t ht m
  have hmem : X.flow ξ (Lc X ω t) x ∈ X.dom := (flow_Lc_mem_dom ω hξ hx t).2 ht
  have hp : (∑ j, (m j : ℝ) • ω j) ∈ X.periods la :=
    sum_mem fun j _ => by
      rw [Int.cast_smul_eq_zsmul]
      exact zsmul_mem (hωp j) _
  have hLc : Lc X ω (t + fun j => (m j : ℂ)) = cR X (∑ j, (m j : ℝ) • ω j) + Lc X ω t := by
    funext τ
    simp [Lc, cR, add_mul, Finset.sum_add_distrib, Finset.sum_apply, add_comm]
  simp only [hline]
  rw [hLc, ← flow_flow X hξ]
  exact sec_periodic X la P hP hξΛ hξ hp _ hmem

end line

end ReciprocityTheory.ChartRestriction.G.FD.TubeSummability
end

namespace ReciprocityTheory.ChartRestriction.G.FD.TubeFourierExpansion

open Complex MeasureTheory Metric ReciprocityTheory.L2DbarEstimates.Y ReciprocityTheory.ChartRestriction.G.FD.TubeSummability

variable {n : ℕ}

lemma fourCoeff_shift (g : (Fin n → ℂ) → ℂ) (y0 : Fin n → ℝ) (k : Fin n → ℤ) :
    fourCoeff (fun t => g (t + fun j => (y0 j : ℂ) * I)) 0 k =
      (Real.exp (-2 * Real.pi * ∑ j, (k j : ℝ) * y0 j) : ℂ) * fourCoeff g y0 k := by
  have hx : ∀ (G Sx Sy : ℂ), G * cexp (-2 * Real.pi * I * Sx) =
      cexp (-2 * Real.pi * Sy) * (G * cexp (-2 * Real.pi * I * (Sx + Sy * I))) := by
    intro G Sx Sy
    rw [mul_left_comm, ← Complex.exp_add]
    congr 2
    linear_combination (2 * (Real.pi : ℂ) * Sy) * Complex.I_sq
  have key : ∀ x : Fin n → ℝ,
      g ((fun j => (x j : ℂ) + (((0 : Fin n → ℝ) j : ℝ) : ℂ) * I) + fun j => (y0 j : ℂ) * I) *
        cexp (-2 * Real.pi * I * ∑ j, (k j : ℂ) * ((x j : ℂ) + (((0 : Fin n → ℝ) j : ℝ) : ℂ) * I)) =
      (Real.exp (-2 * Real.pi * ∑ j, (k j : ℝ) * y0 j) : ℂ) *
        (g (fun j => (x j : ℂ) + (y0 j : ℂ) * I) *
          cexp (-2 * Real.pi * I * ∑ j, (k j : ℂ) * ((x j : ℂ) + (y0 j : ℂ) * I))) := by
    intro x
    have hg : ((fun j => (x j : ℂ) + (((0 : Fin n → ℝ) j : ℝ) : ℂ) * I) + fun j => (y0 j : ℂ) * I) =
        fun j => (x j : ℂ) + (y0 j : ℂ) * I := by
      funext j; simp
    have e1 : ∑ j, (k j : ℂ) * ((x j : ℂ) + (((0 : Fin n → ℝ) j : ℝ) : ℂ) * I) =
        ∑ j, (k j : ℂ) * (x j : ℂ) := by simp
    have e2 : ∑ j, (k j : ℂ) * ((x j : ℂ) + (y0 j : ℂ) * I) =
        ∑ j, (k j : ℂ) * (x j : ℂ) + (∑ j, (k j : ℂ) * (y0 j : ℂ)) * I := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
    have e3 : ((Real.exp (-2 * Real.pi * ∑ j, (k j : ℝ) * y0 j) : ℝ) : ℂ) =
        cexp (-2 * Real.pi * ∑ j, (k j : ℂ) * (y0 j : ℂ)) := by
      rw [Complex.ofReal_exp]
      congr 1
      push_cast
      ring
    rw [hg, e1, e2, e3]
    exact hx _ _ _
  unfold fourCoeff
  rw [← MeasureTheory.integral_const_mul]
  exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall key)

lemma mul_sign_abs (a : ℤ) : (a : ℝ) * (a.sign : ℝ) = |(a : ℝ)| := by
  rcases lt_trichotomy a 0 with h | rfl | h
  · rw [Int.sign_eq_neg_one_of_neg h, abs_of_neg (by exact_mod_cast h)]
    push_cast
    ring
  · simp
  · rw [Int.sign_eq_one_of_pos h, abs_of_pos (by exact_mod_cast h)]
    push_cast
    ring

lemma abs_sign_le (a : ℤ) : |(a.sign : ℝ)| ≤ 1 := by
  rcases Int.sign_trichotomy a with h | h | h <;> simp [h]

lemma norm_exp_real_I (c : ℝ) (k : Fin n → ℤ) (x0 : Fin n → ℝ) :
    ‖cexp (c * I * ∑ j, (k j : ℂ) * (x0 j : ℂ))‖ = 1 := by
  have e : (c : ℂ) * I * ∑ j, (k j : ℂ) * (x0 j : ℂ) =
      ((c * ∑ j, (k j : ℝ) * x0 j : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [e, Complex.norm_exp_ofReal_mul_I]

theorem tube_expansion (Ω : Set (Fin n → ℝ)) (h : (Fin n → ℂ) → ℂ) (hΩ : IsOpen Ω)
    (hc : Convex ℝ Ω) (h0 : (0 : Fin n → ℝ) ∈ Ω) (hd : DifferentiableOn ℂ h (tube n Ω))
    (hp : ∀ s ∈ tube n Ω, ∀ m : Fin n → ℤ, h (s + fun k => (m k : ℂ)) = h s)
    (u : Fin n → ℂ) (hu : u ∈ tube n Ω) :
    Summable (fun k : Fin n → ℤ =>
      ‖fourCoeff h 0 k * cexp (2 * Real.pi * I * ∑ j, (k j : ℂ) * u j)‖) ∧
    HasSum (fun k : Fin n → ℤ => fourCoeff h 0 k * cexp (2 * Real.pi * I * ∑ j, (k j : ℂ) * u j))
      (h u) := by
  classical
  obtain ⟨x0, y0, hux, hy0Ω⟩ : ∃ x0 y0 : Fin n → ℝ,
      (∀ j, u j = (x0 j : ℂ) + (y0 j : ℂ) * I) ∧ y0 ∈ Ω :=
    ⟨fun j => (u j).re, fun j => (u j).im, fun j => (Complex.re_add_im (u j)).symm, hu⟩
  have hpre : IsPreconnected Ω := hc.isPreconnected

  have hind : ∀ b ∈ Ω, ∀ k, fourCoeff h 0 k = fourCoeff h b k :=
    fun b hb k => four_indep n Ω h hΩ hpre hd hp 0 h0 b hb k
  have htube : ∀ x b : Fin n → ℝ, b ∈ Ω → (fun j => (x j : ℂ) + (b j : ℂ) * I) ∈ tube n Ω := by
    intro x b hb
    simp only [tube, Set.mem_ofPred_eq]
    simpa using hb

  have hslice : ∀ b ∈ Ω, ∃ C, ∀ x : Fin n → ℝ, ‖h (fun j => (x j : ℂ) + (b j : ℂ) * I)‖ ≤ C := by
    intro b hb
    have hcont : ContinuousOn (fun x : Fin n → ℝ => h (fun j => (x j : ℂ) + (b j : ℂ) * I))
        (Set.Icc 0 1) := by
      refine hd.continuousOn.comp (Continuous.continuousOn ?_) (fun x _ => htube x b hb)
      exact continuous_pi fun j => (Complex.continuous_ofReal.comp (continuous_apply j)).add
        continuous_const
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
    refine ⟨C, fun x => ?_⟩
    have hxm : (fun j => x j - (⌊x j⌋ : ℝ)) ∈ Set.Icc (0 : Fin n → ℝ) 1 := by
      refine ⟨fun j => ?_, fun j => ?_⟩
      · have := Int.floor_le (x j)
        show (0 : ℝ) ≤ x j - (⌊x j⌋ : ℝ)
        linarith
      · have := Int.lt_floor_add_one (x j)
        show x j - (⌊x j⌋ : ℝ) ≤ 1
        linarith
    have hper := hp _ (htube (fun j => x j - (⌊x j⌋ : ℝ)) b hb) (fun j => ⌊x j⌋)
    have heq : ((fun j => (((x j - (⌊x j⌋ : ℝ)) : ℝ) : ℂ) + (b j : ℂ) * I) +
        fun j => ((⌊x j⌋ : ℤ) : ℂ)) = fun j => (x j : ℂ) + (b j : ℂ) * I := by
      funext j
      simp only [Pi.add_apply]
      push_cast
      ring
    rw [heq] at hper
    rw [hper]
    exact hC _ hxm

  have hcoef : ∀ b ∈ Ω, ∃ C, ∀ k : Fin n → ℤ,
      ‖fourCoeff h 0 k‖ ≤ C * Real.exp (2 * Real.pi * ∑ j, (k j : ℝ) * b j) := by
    intro b hb
    obtain ⟨C, hC⟩ := hslice b hb
    refine ⟨C, fun k => ?_⟩
    have hB := four_bound n h b k C hC
    rw [hind b hb k]
    have hmul : Real.exp (-2 * Real.pi * ∑ j, (k j : ℝ) * b j) *
        Real.exp (2 * Real.pi * ∑ j, (k j : ℝ) * b j) = 1 := by
      rw [← Real.exp_add, ← Real.exp_zero]
      congr 1
      ring
    calc ‖fourCoeff h b k‖
        = ‖fourCoeff h b k‖ * Real.exp (-2 * Real.pi * ∑ j, (k j : ℝ) * b j) *
            Real.exp (2 * Real.pi * ∑ j, (k j : ℝ) * b j) := by rw [mul_assoc, hmul, mul_one]
      _ ≤ C * Real.exp (2 * Real.pi * ∑ j, (k j : ℝ) * b j) :=
          mul_le_mul_of_nonneg_right hB (Real.exp_pos _).le

  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hΩ y0 hy0Ω
  have hbσ : ∀ k : Fin n → ℤ, (fun j => y0 j - ε / 2 * (((k j).sign : ℤ) : ℝ)) ∈ Ω := by
    intro k
    apply hball
    rw [Metric.mem_ball, dist_pi_lt_iff hε]
    intro j
    rw [Real.dist_eq, show y0 j - ε / 2 * (((k j).sign : ℤ) : ℝ) - y0 j =
      -(ε / 2 * (((k j).sign : ℤ) : ℝ)) by ring, abs_neg, abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < ε / 2)]
    have := abs_sign_le (k j)
    nlinarith
  have hcoefσ : ∀ σ : Fin n → ℤ, ∃ C, 0 ≤ C ∧
      ((fun j => y0 j - ε / 2 * ((σ j : ℤ) : ℝ)) ∈ Ω → ∀ k : Fin n → ℤ,
        ‖fourCoeff h 0 k‖ ≤
          C * Real.exp (2 * Real.pi * ∑ j, (k j : ℝ) * (y0 j - ε / 2 * ((σ j : ℤ) : ℝ)))) := by
    intro σ
    by_cases hσ : (fun j => y0 j - ε / 2 * ((σ j : ℤ) : ℝ)) ∈ Ω
    · obtain ⟨C, hC⟩ := hcoef _ hσ
      exact ⟨max C 0, le_max_right _ _, fun _ k =>
        (hC k).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)⟩
    · exact ⟨0, le_rfl, fun h' => absurd h' hσ⟩
  choose Cf hCf0 hCf using hcoefσ
  have hsignS : ∀ k : Fin n → ℤ,
      (fun j => (k j).sign) ∈ Fintype.piFinset (fun _ : Fin n => ({-1, 0, 1} : Finset ℤ)) := by
    intro k
    rw [Fintype.mem_piFinset]
    intro j
    rcases Int.sign_trichotomy (k j) with h' | h' | h' <;> simp [h']
  have hCK : ∀ k : Fin n → ℤ, Cf (fun j => (k j).sign) ≤
      ∑ σ ∈ Fintype.piFinset (fun _ : Fin n => ({-1, 0, 1} : Finset ℤ)), Cf σ :=
    fun k => Finset.single_le_sum (fun σ _ => hCf0 σ) (hsignS k)
  have hexpo : ∀ k : Fin n → ℤ,
      2 * Real.pi * ∑ j, (k j : ℝ) * (y0 j - ε / 2 * (((k j).sign : ℤ) : ℝ)) +
        -2 * Real.pi * ∑ j, (k j : ℝ) * y0 j = -(Real.pi * ε) * ∑ j, |(k j : ℝ)| := by
    intro k
    have e : ∑ j, (k j : ℝ) * (y0 j - ε / 2 * (((k j).sign : ℤ) : ℝ)) =
        ∑ j, (k j : ℝ) * y0 j - ε / 2 * ∑ j, |(k j : ℝ)| := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [← mul_sign_abs (k j)]
      ring
    rw [e]
    ring

  have hsumu : ∀ k : Fin n → ℤ, ∑ j, (k j : ℂ) * u j =
      ((∑ j, (k j : ℝ) * x0 j : ℝ) : ℂ) + ((∑ j, (k j : ℝ) * y0 j : ℝ) : ℂ) * I := by
    intro k
    simp only [hux]
    push_cast
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  have hexpu : ∀ A B : ℝ, cexp (2 * Real.pi * I * ((A : ℂ) + (B : ℂ) * I)) =
      ((Real.exp (-2 * Real.pi * B) : ℝ) : ℂ) * cexp (((2 * Real.pi * A : ℝ) : ℂ) * I) := by
    intro A B
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    linear_combination (2 * (Real.pi : ℂ) * B) * Complex.I_sq
  have hterm : ∀ k : Fin n → ℤ,
      ‖fourCoeff h 0 k * cexp (2 * Real.pi * I * ∑ j, (k j : ℂ) * u j)‖ =
        ‖fourCoeff h 0 k‖ * Real.exp (-2 * Real.pi * ∑ j, (k j : ℝ) * y0 j) := by
    intro k
    rw [hsumu k, hexpu, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
      Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  have hbound : ∀ k : Fin n → ℤ,
      ‖fourCoeff h 0 k * cexp (2 * Real.pi * I * ∑ j, (k j : ℂ) * u j)‖ ≤
        (∑ σ ∈ Fintype.piFinset (fun _ : Fin n => ({-1, 0, 1} : Finset ℤ)), Cf σ) *
          Real.exp (-(Real.pi * ε) * ∑ j, |(k j : ℝ)|) := by
    intro k
    rw [hterm k]
    refine le_trans (mul_le_mul_of_nonneg_right (hCf _ (hbσ k) k) (Real.exp_pos _).le) ?_
    rw [mul_assoc, ← Real.exp_add]
    refine mul_le_mul (hCK k) (le_of_eq ?_) (Real.exp_pos _).le (le_trans (hCf0 _) (hCK k))
    congr 1
    exact hexpo k
  have hsumm : Summable (fun k : Fin n → ℤ =>
      ‖fourCoeff h 0 k * cexp (2 * Real.pi * I * ∑ j, (k j : ℂ) * u j)‖) :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) hbound
      ((summable_exp_abs (Real.pi * ε) (by positivity) n).mul_left _)
  refine ⟨hsumm, ?_⟩

  have hΩ'o : IsOpen ((fun b => b + y0) ⁻¹' Ω) := hΩ.preimage (continuous_id.add continuous_const)
  have h0' : (0 : Fin n → ℝ) ∈ (fun b => b + y0) ⁻¹' Ω := by simpa using hy0Ω
  have hmaps : ∀ t ∈ tube n ((fun b => b + y0) ⁻¹' Ω),
      t + (fun j => (y0 j : ℂ) * I) ∈ tube n Ω := by
    intro t ht
    simp only [tube, Set.mem_ofPred_eq, Set.mem_preimage] at ht ⊢
    convert ht using 1
    funext j
    simp only [Pi.add_apply, Complex.add_im, Complex.mul_I_im, Complex.ofReal_re]
  have hdg : DifferentiableOn ℂ (fun t => h (t + fun j => (y0 j : ℂ) * I))
      (tube n ((fun b => b + y0) ⁻¹' Ω)) :=
    hd.comp (differentiable_id.add_const _).differentiableOn (fun t ht => hmaps t ht)
  have hpg : ∀ s ∈ tube n ((fun b => b + y0) ⁻¹' Ω), ∀ m : Fin n → ℤ,
      h (s + (fun k => (m k : ℂ)) + fun j => (y0 j : ℂ) * I) = h (s + fun j => (y0 j : ℂ) * I) := by
    intro s hs m
    rw [add_right_comm]
    exact hp _ (hmaps s hs) m
  have hcoefg : ∀ k, fourCoeff (fun t => h (t + fun j => (y0 j : ℂ) * I)) 0 k =
      (Real.exp (-2 * Real.pi * ∑ j, (k j : ℝ) * y0 j) : ℂ) * fourCoeff h 0 k := by
    intro k
    rw [fourCoeff_shift h y0 k, hind y0 hy0Ω k]
  have hsummg : Summable (fun k => ‖fourCoeff (fun t => h (t + fun j => (y0 j : ℂ) * I)) 0 k‖) := by
    refine hsumm.congr (fun k => ?_)
    rw [hterm k, hcoefg k, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
      mul_comm]
  have hs := four_sum n ((fun b => b + y0) ⁻¹' Ω) (fun t => h (t + fun j => (y0 j : ℂ) * I))
    hΩ'o hdg hpg h0' hsummg x0
  convert (preTransparency := .reducible) hs using 1
  · funext k
    rw [hcoefg k, hsumu k, hexpu]
    have e : ((2 * Real.pi * (∑ j, (k j : ℝ) * x0 j) : ℝ) : ℂ) * I =
        2 * Real.pi * I * ∑ j, (k j : ℂ) * (x0 j : ℂ) := by
      push_cast
      ring
    rw [e]
    ring
  · show h u = h ((fun k => (x0 k : ℂ)) + fun j => (y0 j : ℂ) * I)
    congr 1
    funext j
    rw [hux j]
    rfl

end ReciprocityTheory.ChartRestriction.G.FD.TubeFourierExpansion
end

namespace ReciprocityTheory.ChartRestriction.G.FD.FrequencyIndexing

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (ω : Module.Basis (Fin n) ℝ (ι → ℝ))

noncomputable def νk (k : Fin n → ℤ) : ι → ℝ :=
  fun τ => (∑ j, (k j : ℝ) * ω.repr (Pi.single τ 1) j) / 2

lemma pairing (ν : ι → ℝ) (k : Fin n → ℤ) (hk : ∀ j, 2 * ∑ τ, ν τ * ω j τ = k j) (v : ι → ℝ) :
    ∑ τ, ν τ * v τ = (∑ j, (k j : ℝ) * ω.repr v j) / 2 := by
  have hv : v = ∑ j, ω.repr v j • ω j := (ω.sum_repr v).symm
  have h1 : ∀ j, (k j : ℝ) * ω.repr v j / 2 = ∑ τ, ν τ * (ω.repr v j * ω j τ) := by
    intro j
    rw [← hk j, Finset.mul_sum, Finset.sum_mul, Finset.sum_div]
    exact Finset.sum_congr rfl (fun τ _ => by ring)
  rw [Finset.sum_div]
  simp_rw [h1]
  rw [Finset.sum_comm]
  conv_lhs => rw [hv]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]

lemma repr_sum_single (v : ι → ℝ) (j : Fin n) :
    ∑ τ, v τ * ω.repr (Pi.single τ 1) j = ω.repr v j := by
  have hv : v = ∑ τ, v τ • (Pi.single τ (1 : ℝ) : ι → ℝ) := by
    funext x
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hv]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul]

lemma νk_spec (k : Fin n → ℤ) (i : Fin n) : 2 * ∑ τ, νk ω k τ * ω i τ = k i := by
  have h : ∀ τ, νk ω k τ * ω i τ =
      (∑ j, (k j : ℝ) * (ω i τ * ω.repr (Pi.single τ 1) j)) / 2 := by
    intro τ
    simp only [νk]
    rw [div_mul_eq_mul_div, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl (fun j _ => by ring)
  simp_rw [h]
  rw [← Finset.sum_div, Finset.sum_comm]
  simp_rw [← Finset.mul_sum, repr_sum_single, Module.Basis.repr_self, Finsupp.single_apply]
  simp
  ring

lemma νk_injective : Function.Injective (νk ω) := by
  intro k k' h
  funext i
  have h1 := νk_spec ω k i
  have h2 := νk_spec ω k' i
  rw [h] at h1
  exact_mod_cast h1.symm.trans h2

lemma eq_νk (ν : ι → ℝ) (k : Fin n → ℤ) (hk : ∀ j, 2 * ∑ τ, ν τ * ω j τ = k j) : ν = νk ω k := by
  funext τ
  have h1 := pairing ω ν k hk (Pi.single τ 1)
  have h2 := pairing ω (νk ω k) k (νk_spec ω k) (Pi.single τ 1)
  have e : ∀ μ : ι → ℝ, ∑ σ, μ σ * (Pi.single τ (1 : ℝ) : ι → ℝ) σ = μ τ := by
    intro μ
    simp [Pi.single_apply]
  rw [e] at h1 h2
  rw [h1, h2]

end ReciprocityTheory.ChartRestriction.G.FD.FrequencyIndexing
end

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex ReciprocityTheory.L2DbarEstimates.Y ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
  ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity ReciprocityTheory.ChartRestriction.G.FD.RealEmbeddingCharacters
  ReciprocityTheory.ChartRestriction.G.FD.FlowMeanContinuity ReciprocityTheory.ChartRestriction.G.FD.TubeSummability ReciprocityTheory.ChartRestriction.G.FD.TubeFourierExpansion
  ReciprocityTheory.ChartRestriction.G.FD.FrequencyIndexing

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem m3bExp_holds : FourierJacobiExpansion (E := E) := by
  classical
  intro r X la P hP ξ hξ x hx s hs
  obtain ⟨hξΛ, hξ0, -⟩ := id hξ

  obtain ⟨n, ω, hω⟩ : ∃ (n : ℕ) (ω : Module.Basis (Fin n) ℝ (X.Ψ → ℝ)),
      Submodule.span ℤ (Set.range ω) = perL X la := by
    let b := (Module.Free.chooseBasis ℤ (perL X la)).reindex (Fintype.equivFin _)
    exact ⟨_, b.ofZLatticeBasis ℝ (perL X la), b.ofZLatticeBasis_span ℝ (perL X la)⟩
  have hωp : ∀ j, ω j ∈ X.periods la := by
    intro j
    have h1 : ω j ∈ perL X la := by
      rw [← hω]
      exact Submodule.subset_span ⟨j, rfl⟩
    exact h1

  have hsurj : ∀ u : X.Ψ → ℂ, ∃ t : Fin n → ℂ, TubeSummability.Lc X ω t = u := by
    intro u
    refine ⟨fun j => (ω.repr (fun τ => (u τ).re) j : ℂ) +
      (ω.repr (fun τ => (u τ).im) j : ℂ) * I, ?_⟩
    funext τ
    have hre : ∑ j, ω.repr (fun τ => (u τ).re) j * ω j τ = (u τ).re := by
      have := congrFun (ω.sum_repr (fun τ => (u τ).re)) τ
      simpa [Finset.sum_apply, smul_eq_mul] using this
    have him : ∑ j, ω.repr (fun τ => (u τ).im) j * ω j τ = (u τ).im := by
      have := congrFun (ω.sum_repr (fun τ => (u τ).im)) τ
      simpa [Finset.sum_apply, smul_eq_mul] using this
    simp only [TubeSummability.Lc]
    calc _ = ((∑ j, ω.repr (fun τ => (u τ).re) j * ω j τ : ℝ) : ℂ) +
          ((∑ j, ω.repr (fun τ => (u τ).im) j * ω j τ : ℝ) : ℂ) * I := by
          push_cast
          rw [Finset.sum_mul, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl (fun j _ => by ring)
      _ = u τ := by
          rw [hre, him]
          exact Complex.re_add_im (u τ)
  obtain ⟨t, rfl⟩ := hsurj s
  have ht : t ∈ tube n (TubeSummability.Om X ξ x ω) :=
    (TubeSummability.flow_Lc_mem_dom (ω := ω) hξ0 hx t).mp hs
  have hΩ := TubeSummability.Om_open_convex (ξ := ξ) (ω := ω) hx
  have hexp : HasSum (fun k : Fin n → ℤ =>
      fourCoeff (TubeSummability.hline X P ξ x ω) 0 k * cexp (2 * Real.pi * I * ∑ j, (k j : ℂ) * t j))
      (P (X.flow ξ (TubeSummability.Lc X ω t) x)) :=
    (TubeFourierExpansion.tube_expansion (TubeSummability.Om X ξ x ω) (TubeSummability.hline X P ξ x ω) hΩ.1 hΩ.2
      (TubeSummability.zero_mem_Om (ω := ω) hξ0 hx) (TubeSummability.hline_diff (X := X) (la := la) (P := P) (ξ := ξ) (x := x) (ω := ω) hP hξ0 hx)
      (TubeSummability.hline_periodic (X := X) (la := la) (P := P) (ξ := ξ) (x := x) (ω := ω)
        hP hξΛ hξ0 hx hωp) t ht).2
  refine ((FrequencyIndexing.νk_injective (ω := ω)).hasSum_iff ?_).mp ?_
  · intro ν hν
    have hfj : X.fj la ξ ν P x = 0 := by
      rw [Data.fj]
      refine if_neg ?_
      intro hall
      apply hν
      choose k hk using fun j => hall (ω j) (hωp j)
      exact ⟨k, (FrequencyIndexing.eq_νk (ω := ω) ν k hk).symm⟩
    simp only [hfj, zero_mul]
  · convert hexp using 1
    funext k
    simp only [Function.comp_apply]
    congr 1
    · exact FlowMeanContinuity.fj_eq_fourCoeff (X := X) (la := la) P hP hξ hx ω hω
        (FrequencyIndexing.νk ω k) k (FrequencyIndexing.νk_spec (ω := ω) k)
    · congr 1
      have key : ∀ j, ∑ τ, (FrequencyIndexing.νk ω k τ : ℂ) * (ω j τ : ℂ) = (k j : ℂ) / 2 := by
        intro j
        have h2 := FrequencyIndexing.νk_spec (ω := ω) k j
        have h3 : ∑ τ, FrequencyIndexing.νk ω k τ * ω j τ = (k j : ℝ) / 2 := by linarith
        exact_mod_cast h3
      have hsw : ∑ τ, (FrequencyIndexing.νk ω k τ : ℂ) * TubeSummability.Lc X ω t τ =
          ∑ j, t j * ((k j : ℂ) / 2) := by
        simp only [TubeSummability.Lc, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [← key j, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun τ _ => by ring)
      rw [hsw, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by ring)

end ReciprocityTheory.ChartRestriction.G.FD
