module

public import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.LandauFinite

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.LandauDichotomy
open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Deduction

theorem eq_ofReal_sub_of_dist_le_of_le_sub_re {w : ℂ} {σ D : ℝ} (h1 : dist w (σ : ℂ) ≤ D) (h2 : D ≤ σ - w.re) :
    w = ((σ - D : ℝ) : ℂ) := by
  have hD0 : 0 ≤ D := dist_nonneg.trans h1
  rw [Complex.dist_eq_re_im, Complex.ofReal_re, Complex.ofReal_im] at h1
  have hq : (w.re - σ) ^ 2 + (w.im - 0) ^ 2 ≤ D ^ 2 := by
    have hs := Real.sq_sqrt (by positivity : (0:ℝ) ≤ (w.re - σ) ^ 2 + (w.im - 0) ^ 2)
    have h0 := Real.sqrt_nonneg ((w.re - σ) ^ 2 + (w.im - 0) ^ 2)
    nlinarith
  have him : w.im = 0 := by nlinarith [sq_nonneg w.im]
  have hre : w.re = σ - D := by nlinarith [sq_nonneg w.im]
  apply Complex.ext
  · rw [Complex.ofReal_re]; exact hre
  · rw [Complex.ofReal_im]; exact him

theorem landau_dichotomy {Z : Set ℂ} (hiso : ∀ z : ℂ, 0 < z.re → ∀ᶠ w in 𝓝[≠] z, w ∉ Z) {σ θ : ℝ}
    (hle : ∀ ρ ∈ Z, ρ.re < σ) (hθ : 0 < θ) (hθσ : θ < σ) {ρ₀ : ℂ} (h₀ : ρ₀ ∈ Z) (hρ₀ : θ < ρ₀.re) :
    (∃ D : ℝ, D ≤ σ - θ ∧ (∀ w ∈ Z, w ∉ Metric.ball (σ : ℂ) D) ∧ ∃ ρ₁ ∈ Z, σ - ρ₁.re < D) ∨
    (∃ β : ℝ, (β : ℂ) ∈ Z ∧ θ < β ∧ ∃ r : ℝ, σ - β < r ∧ r ≤ σ - θ ∧
      ∀ w ∈ Z, w ∈ Metric.ball (σ : ℂ) r → w = β) := by
  have hfin : (Z ∩ Metric.closedBall (σ : ℂ) (σ - θ)).Finite :=
    landau_finite hiso (by rw [Complex.ofReal_re]; linarith)
  set F := Z ∩ Metric.closedBall (σ : ℂ) (σ - θ) with hFdef
  rcases F.eq_empty_or_nonempty with hF | hF
  · left
    refine ⟨σ - θ, le_rfl, ?_, ρ₀, h₀, by linarith⟩
    intro w hw hb
    have hwF : w ∈ F := ⟨hw, Metric.ball_subset_closedBall hb⟩
    rw [hF] at hwF
    exact hwF
  · obtain ⟨ρs, hρsF, hmin⟩ := Set.exists_min_image F (fun w => dist w (σ : ℂ)) hfin hF
    have hdle : dist ρs (σ : ℂ) ≤ σ - θ := Metric.mem_closedBall.mp hρsF.2
    have hball : ∀ w ∈ Z, w ∉ Metric.ball (σ : ℂ) (dist ρs (σ : ℂ)) := by
      intro w hw hb
      rw [Metric.mem_ball] at hb
      have hwF : w ∈ F := ⟨hw, Metric.mem_closedBall.mpr (by linarith)⟩
      have := hmin w hwF
      linarith
    by_cases hex : ∃ ρ₁ ∈ Z, σ - ρ₁.re < dist ρs (σ : ℂ)
    · left
      exact ⟨dist ρs (σ : ℂ), hdle, hball, hex⟩
    · right
      push_neg at hex
      set d := dist ρs (σ : ℂ) with hd
      have hreal : ∀ w ∈ F, dist w (σ : ℂ) = d → w = ((σ - d : ℝ) : ℂ) :=
        fun w hw he => eq_ofReal_sub_of_dist_le_of_le_sub_re (le_of_eq he) (hex w hw.1)
      have hρs := hreal ρs hρsF rfl
      have hdlt : d < σ - θ := by
        rcases lt_or_eq_of_le hdle with h | h
        · exact h
        · exfalso
          have := hex ρ₀ h₀
          linarith
      refine ⟨σ - d, hρs ▸ hρsF.1, by linarith, ?_⟩
      have hT : ∀ t ∈ F \ {((σ - d : ℝ) : ℂ)}, d < dist t (σ : ℂ) := by
        intro t ht
        have hm : d ≤ dist t (σ : ℂ) := hmin t ht.1
        rcases lt_or_eq_of_le hm with h | h
        · exact h
        · exact absurd (hreal t ht.1 h.symm) ht.2
      obtain ⟨r, hr, hrT⟩ : ∃ r, d < r ∧ ∀ t ∈ F \ {((σ - d : ℝ) : ℂ)}, r ≤ dist t (σ : ℂ) := by
        rcases (F \ {((σ - d : ℝ) : ℂ)}).eq_empty_or_nonempty with hTe | hTne
        · refine ⟨d + 1, by linarith, ?_⟩
          intro t ht
          rw [hTe] at ht
          exact absurd ht (Set.notMem_empty t)
        · obtain ⟨t₀, ht₀, htmin⟩ := Set.exists_min_image (F \ {((σ - d : ℝ) : ℂ)})
            (fun w => dist w (σ : ℂ)) (hfin.subset Set.diff_subset) hTne
          exact ⟨dist t₀ (σ : ℂ), hT t₀ ht₀, htmin⟩
      refine ⟨min r (σ - θ), ?_, min_le_right _ _, ?_⟩
      · rw [sub_sub_cancel]
        exact lt_min hr hdlt
      · intro w hw hb
        rw [Metric.mem_ball] at hb
        have hwF : w ∈ F := ⟨hw, Metric.mem_closedBall.mpr (le_trans hb.le (min_le_right _ _))⟩
        by_contra hne
        have h3 := hrT w ⟨hwF, hne⟩
        have h4 := min_le_left r (σ - θ)
        linarith

end Deduction

end
end

section -- merged from Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.mellinGchiOfNeOne
open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Deduction

theorem mellin_Gchi_of_ne_one_ne {s : ℂ} (hs : 1 < s.re) : s ≠ 0 ∧ s - 1 ≠ 0 := by
  constructor
  · rintro rfl
    simp at hs
    linarith
  · intro h
    rw [sub_eq_zero.mp h] at hs
    simp at hs

theorem mellin_Gchi_of_ne_one_int (n : ℕ) (hn : 1 ≤ n) (s : ℂ) (hs : 1 < s.re) :
    IntegrableOn (fun y : ℝ => ((max (y / n - 1) 0 : ℝ) : ℂ) * (y : ℂ) ^ (-s - 1)) (Ioi 1) := by
  obtain ⟨h0, h1⟩ := mellin_Gchi_of_ne_one_ne hs
  apply Integrable.of_integral_ne_zero
  rw [mellin_ramp n hn s hs]
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  exact div_ne_zero (cpow_ne_zero_iff.mpr (Or.inl hnC)) (mul_ne_zero h0 h1)

theorem mellin_Gchi_of_ne_one_norm (n : ℕ) (hn : 1 ≤ n) (s : ℂ) (hs : 1 < s.re) :
    ∫ y in Ioi (1 : ℝ), ‖((max (y / n - 1) 0 : ℝ) : ℂ) * (y : ℂ) ^ (-s - 1)‖ =
      (n : ℝ) ^ (-s.re) / (s.re * (s.re - 1)) := by
  have h := mellin_ramp n hn (s.re : ℂ) (by simpa using hs)
  apply ofReal_injective
  rw [← integral_complex_ofReal, ofReal_div, ofReal_cpow (Nat.cast_nonneg n)]
  push_cast
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
  have hy0 : (0 : ℝ) < y := lt_trans one_pos hy
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hy0, Complex.norm_real,
    Real.norm_of_nonneg (le_max_right _ _)]
  change (((max (y / n - 1) 0 * y ^ (-s - 1).re : ℝ)) : ℂ) = _
  rw [ofReal_mul, ofReal_cpow hy0.le]
  simp

theorem mellin_Gchi_of_ne_one_hasSum (f : ℕ → ℂ) (y : ℝ) :
    HasSum (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * f n *
      ((max (y / n - 1) 0 : ℝ) : ℂ)) (ramp f y) := by
  unfold ramp
  apply hasSum_sum_of_ne_finset_zero
  intro n hn
  have hn' : ⌊y⌋₊ + 1 ≤ n := by simpa using hn
  have hpos : (0 : ℝ) < n := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hlt : y < n := by
    have h1 := Nat.lt_floor_add_one y
    have h2 : ((⌊y⌋₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn'
    push_cast at h2
    linarith
  have : max (y / n - 1) 0 = 0 := by
    apply max_eq_right
    have := (div_lt_one hpos).mpr hlt
    linarith
  rw [this]
  simp

theorem mellin_Gchi_of_ne_one_ramp (f : ℕ → ℂ) (s : ℂ) (hs : 1 < s.re)
    (hf : LSeriesSummable (fun n => f n * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) s)
    (g : ℝ → ℂ) (hg : IntegrableOn g (Ioi 1)) :
    ∫ y in Ioi (1 : ℝ), (ramp f y * (y : ℂ) ^ (-s - 1) + g y) =
      LSeries (fun n => f n * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) s / (s * (s - 1)) +
        ∫ y in Ioi (1 : ℝ), g y := by
  set a : ℕ → ℂ := fun n => f n * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) with ha
  let F : ℕ → ℝ → ℂ := fun n y => match n with
    | 0 => g y
    | m + 1 => a (m + 1) * (((max (y / ((m + 1 : ℕ) : ℝ) - 1) 0 : ℝ) : ℂ) * (y : ℂ) ^ (-s - 1))
  have hint : ∀ n, Integrable (F n) (volume.restrict (Ioi 1)) := by
    rintro (_ | m)
    · exact hg
    · exact (mellin_Gchi_of_ne_one_int (m + 1) (by omega) s hs).const_mul _
  have hsum : Summable fun n => ∫ y in Ioi (1 : ℝ), ‖F n y‖ := by
    rw [← summable_nat_add_iff 1]
    have h1 := ((summable_nat_add_iff 1).mpr hf.norm).div_const (s.re * (s.re - 1))
    refine h1.congr fun m => ?_
    simp only [F]
    simp_rw [norm_mul (a (m + 1))]
    rw [integral_const_mul, mellin_Gchi_of_ne_one_norm (m + 1) (by omega) s hs,
      LSeries.norm_term_eq, if_neg (by omega), Real.rpow_neg (Nat.cast_nonneg _)]
    ring
  have h := hasSum_integral_of_summable_integral_norm hint hsum
  have hF : ∀ y, ∑' n, F n y = ramp f y * (y : ℂ) ^ (-s - 1) + g y := by
    intro y
    have h1 := (hasSum_nat_add_iff' 1).mpr
      ((mellin_Gchi_of_ne_one_hasSum f y).mul_right ((y : ℂ) ^ (-s - 1)))
    have h2 : HasSum (fun n => F (n + 1) y) (ramp f y * (y : ℂ) ^ (-s - 1)) := by
      convert h1 using 1
      · funext m
        simp only [F, ha]
        ring
      · simp
    have h3 := (hasSum_nat_add_iff (f := fun n => F n y) 1).mp h2
    simpa [F] using h3.tsum_eq
  simp_rw [hF] at h
  have h1 := (hasSum_nat_add_iff' 1).mpr (hf.hasSum.div_const (s * (s - 1)))
  have h2 : HasSum (fun n => ∫ y in Ioi (1 : ℝ), F (n + 1) y) (LSeries a s / (s * (s - 1))) := by
    convert h1 using 1
    · funext m
      simp only [F]
      rw [integral_const_mul, mellin_ramp (m + 1) (by omega) s hs,
        LSeries.term_of_ne_zero (by omega), cpow_neg]
      ring
    · simp [LSeries]
  have h3 := (hasSum_nat_add_iff (f := fun n => ∫ y in Ioi (1 : ℝ), F n y) 1).mp h2
  simpa [F] using h.unique h3

theorem mellin_Gchi_of_ne_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (s : ℂ) (hs : 1 < s.re) :
    ∫ y in Ioi (1 : ℝ), Gchi χ y * (y : ℂ) ^ (-s - 1) =
      -(deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s -
          s * (deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1)) / (s * (s - 1)) := by
  obtain ⟨h0, h1⟩ := mellin_Gchi_of_ne_one_ne hs
  set c := deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1 with hc
  have ha : (-s).re < -1 := by simp; linarith
  have h := mellin_Gchi_of_ne_one_ramp (fun n => χ n) s hs
    (χ.LSeriesSummable_twist_vonMangoldt hs) (fun y => c * (y : ℂ) ^ (-s))
    ((integrableOn_Ioi_cpow_of_lt ha one_pos).const_mul c)
  have hL : LSeries (fun n : ℕ => χ n * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) s = _ :=
    χ.LSeries_twist_vonMangoldt_eq hs
  rw [hL, ← χ.LFunction_eq_LSeries hs, ← χ.deriv_LFunction_eq_deriv_LSeries hs,
    integral_const_mul, integral_Ioi_cpow_of_lt ha one_pos] at h
  rw [setIntegral_congr_fun measurableSet_Ioi (g := fun y : ℝ =>
    ramp (fun n => χ n) y * (y : ℂ) ^ (-s - 1) + c * (y : ℂ) ^ (-s)), h]
  · have e2 : -s + 1 = -(s - 1) := by ring
    rw [e2, neg_div (DirichletCharacter.LFunction χ s)]
    generalize deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s = d
    simp only [ofReal_one, one_cpow]
    field_simp
    ring
  · intro y hy
    have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast (lt_trans one_pos hy).ne'
    simp only [Gchi, if_neg hχ, ← hc]
    rw [cpow_sub _ _ hy0, cpow_one]
    field_simp

end Deduction

end
end
