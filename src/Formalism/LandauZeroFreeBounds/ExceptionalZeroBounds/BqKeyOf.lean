module

public import Formalism.LandauZeroFreeBounds.SameCharacterLFunctionOne

@[expose] public section

section -- merged from Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.IteratedDerivLseriesAlternatingNonneg
section -- merged from Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.IteratedDerivInvSubOneAtTwo
open Complex
open scoped ComplexOrder Nat

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma iteratedDeriv_inv_sub_one_at_two (m : ℕ) :
    iteratedDeriv m (fun s : ℂ => (s - 1)⁻¹) 2 = (-1) ^ m * (m ! : ℂ) := by
  have h : (fun s : ℂ => (s - 1)⁻¹) = fun x => (1 * x - 1)⁻¹ := by simp
  rw [iteratedDeriv_eq_iterate, h, iter_deriv_inv_linear_sub]
  norm_num

lemma iteratedDeriv_lseries_at_two {a : ℕ → ℂ} {G : ℂ → ℂ} {lam : ℂ} (hG : Differentiable ℂ G)
    (hFG : ∀ s : ℂ, 1 < s.re → LSeries a s = G s + lam * (s - 1)⁻¹) (m : ℕ) :
    iteratedDeriv m (LSeries a) 2 = iteratedDeriv m G 2 + lam * ((-1) ^ m * (m ! : ℂ)) := by
  have hU : {s : ℂ | 1 < s.re} ∈ nhds (2 : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  have hev : LSeries a =ᶠ[nhds (2 : ℂ)] fun s => G s + lam * (s - 1)⁻¹ := by
    filter_upwards [hU] with s hs using hFG s hs
  have hinv : ContDiffAt ℂ m (fun s : ℂ => lam * (s - 1)⁻¹) 2 :=
    contDiffAt_const.mul ((contDiffAt_id.sub contDiffAt_const).inv (by norm_num))
  rw [(hev.iteratedDeriv m).eq_of_nhds, iteratedDeriv_fun_add hG.contDiff.contDiffAt hinv,
    iteratedDeriv_const_mul_field, iteratedDeriv_inv_sub_one_at_two]

end Formalism.ZeroFreeDirichlet
end
end

open Complex
open scoped ComplexOrder Nat

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma one_le_lseries_at_two {a : ℕ → ℂ} (ha0 : ∀ n, 0 ≤ a n) (ha1 : a 1 = 1)
    (habs : LSeries.abscissaOfAbsConv a ≤ 1) : 1 ≤ LSeries a 2 := by
  have hlt : LSeries.abscissaOfAbsConv a < ((2 : ℂ).re : EReal) := by
    have e : ((2 : ℂ).re : EReal) = ((2 : ℝ) : EReal) := by norm_num
    rw [e]
    exact lt_of_le_of_lt habs (by exact_mod_cast (by norm_num : (1 : ℝ) < 2))
  have hs : LSeriesSummable a 2 := LSeriesSummable_of_abscissaOfAbsConv_lt_re hlt
  have h1 : LSeries.term a 2 1 = 1 := by simp [LSeries.term, ha1]
  have hnn : ∀ j, 0 ≤ LSeries.term a 2 j := fun j => by simpa using LSeries.term_nonneg (ha0 j) 2
  rw [← h1]
  exact hs.le_tsum 1 (fun j _ => hnn j)

lemma iteratedDeriv_lseries_alternating_nonneg {a : ℕ → ℂ} (ha0 : ∀ n, 0 ≤ a n)
    (habs : LSeries.abscissaOfAbsConv a ≤ 1) (n : ℕ) :
    0 ≤ (-1 : ℂ) ^ n * iteratedDeriv n (LSeries a) 2 := by
  have hlt : LSeries.abscissaOfAbsConv a < ((2 : ℝ) : EReal) :=
    lt_of_le_of_lt habs (by exact_mod_cast (by norm_num : (1 : ℝ) < 2))
  have h := LSeries.iteratedDeriv_alternating (a := a) (fun m => ha0 m) (x := 2) hlt n
  simpa using h

theorem lseries_taylor_lower_bound {a : ℕ → ℂ} (ha0 : ∀ n, 0 ≤ a n) (ha1 : a 1 = 1)
    (habs : LSeries.abscissaOfAbsConv a ≤ 1) {F G : ℂ → ℂ} {lam : ℂ} (hG : Differentiable ℂ G)
    (hF : ∀ s : ℂ, 1 < s.re → F s = LSeries a s) (hFG : ∀ s : ℂ, s ≠ 1 → F s = G s + lam / (s - 1))
    {B : ℝ} (hB : ∀ s ∈ Metric.sphere (2 : ℂ) (3 / 2), ‖G s‖ ≤ B) {σ : ℝ} (hσ1 : 7 / 8 ≤ σ)
    (hσ2 : σ < 1) {M : ℕ} (hM : 1 ≤ M) :
    1 - ‖lam‖ * (2 - σ) ^ M / (1 - σ) - 4 * B * (3 / 4) ^ M ≤ (F σ).re := by
  set x : ℝ := 2 - σ with hxdef
  have hx1 : 1 < x := by rw [hxdef]; linarith
  have hx2 : x ≤ 9 / 8 := by rw [hxdef]; linarith
  have hFG' : ∀ s : ℂ, 1 < s.re → LSeries a s = G s + lam * (s - 1)⁻¹ := by
    intro s hs
    have hs1 : s ≠ 1 := by
      intro h; rw [h] at hs; simp at hs
    rw [← hF s hs, hFG s hs1, div_eq_mul_inv]
  have hcoef := iteratedDeriv_lseries_at_two hG hFG'

  have hB0 : 0 ≤ B := by
    have hmem : (2 : ℂ) + ((3 / 2 : ℝ) : ℂ) ∈ Metric.sphere (2 : ℂ) (3 / 2) := by
      rw [Metric.mem_sphere, dist_eq_norm, add_sub_cancel_left, Complex.norm_real]
      norm_num
    exact (norm_nonneg _).trans (hB _ hmem)

  set t : ℕ → ℂ := fun n => (n ! : ℂ)⁻¹ • ((σ : ℂ) - 2) ^ n • iteratedDeriv n G 2 with htdef
  have hT : HasSum t (G σ) := Complex.hasSum_taylorSeries_of_entire hG 2 (σ : ℂ)
  have hsplit := hT.summable.sum_add_tsum_nat_add M
  rw [hT.tsum_eq] at hsplit
  set β : ℕ → ℂ := fun n => (n ! : ℂ)⁻¹ * ((-1) ^ n * iteratedDeriv n (LSeries a) 2) with hβdef
  have hβ0 : ∀ n, 0 ≤ β n := by
    intro n
    refine mul_nonneg ?_ (iteratedDeriv_lseries_alternating_nonneg ha0 habs n)
    have : (0 : ℂ) ≤ (n ! : ℂ) := by exact_mod_cast (Nat.zero_le _)
    exact inv_nonneg.mpr this
  have hσx : (σ : ℂ) - 2 = -(x : ℂ) := by rw [hxdef]; push_cast; ring
  have ht : ∀ n, t n = (x : ℂ) ^ n * β n - lam * (x : ℂ) ^ n := by
    intro n
    have hg : iteratedDeriv n G 2 = iteratedDeriv n (LSeries a) 2 - lam * ((-1) ^ n * (n ! : ℂ)) := by
      rw [hcoef n]; ring
    have hpow : ((-1 : ℂ) ^ n) * ((-1) ^ n) = 1 := by rw [← mul_pow]; simp
    have hfac : (n ! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    simp only [htdef, hβdef, smul_eq_mul, hσx, hg, neg_pow (x : ℂ) n]
    have hQ : (n ! : ℂ)⁻¹ * (n ! : ℂ) = 1 := inv_mul_cancel₀ hfac
    linear_combination (-(lam * (x : ℂ) ^ n * ((n ! : ℂ)⁻¹ * (n ! : ℂ)))) * hpow + (-(lam * (x : ℂ) ^ n)) * hQ

  have hfin : ∑ i ∈ Finset.range M, t i =
      ∑ i ∈ Finset.range M, (x : ℂ) ^ i * β i - lam * (((x : ℂ) ^ M - 1) / ((x : ℂ) - 1)) := by
    rw [Finset.sum_congr rfl (fun i _ => ht i), Finset.sum_sub_distrib, ← Finset.mul_sum, geom_sum_eq]
    intro h
    have : x = 1 := by exact_mod_cast h
    linarith
  have hpos : 1 ≤ ∑ i ∈ Finset.range M, (x : ℂ) ^ i * β i := by
    have hnn : ∀ i ∈ Finset.range M, 0 ≤ (x : ℂ) ^ i * β i := by
      intro i _
      refine mul_nonneg ?_ (hβ0 i)
      have : (0 : ℂ) ≤ (x : ℂ) := by exact_mod_cast (by linarith : (0 : ℝ) ≤ x)
      exact pow_nonneg this i
    have h0 := Finset.single_le_sum hnn (Finset.mem_range.mpr (by omega : 0 < M))
    have hb0 : (x : ℂ) ^ 0 * β 0 = LSeries a 2 := by simp [hβdef]
    rw [hb0] at h0
    exact (one_le_lseries_at_two ha0 ha1 habs).trans h0

  have htail : ‖∑' i, t (i + M)‖ ≤ 4 * B * (3 / 4) ^ M := by
    have hg : HasSum (fun i : ℕ => B * (3 / 4) ^ M * (3 / 4 : ℝ) ^ i) (B * (3 / 4) ^ M * (1 - 3 / 4)⁻¹) :=
      (hasSum_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
    have hle := tsum_of_norm_bounded hg (f := fun i => t (i + M)) (by
      intro i
      have hC := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (i + M)
        (by norm_num : (0 : ℝ) < 3 / 2) hG.diffContOnCl hB
      have hnorm : ‖t (i + M)‖ = ((i + M) ! : ℝ)⁻¹ * x ^ (i + M) * ‖iteratedDeriv (i + M) G 2‖ := by
        simp only [htdef, smul_eq_mul, norm_mul, norm_inv, norm_pow, hσx, norm_neg, Complex.norm_real,
          Complex.norm_natCast]
        rw [Real.norm_of_nonneg (by linarith)]
        ring
      rw [hnorm]
      have hfac : (0 : ℝ) < ((i + M) ! : ℝ) := by exact_mod_cast Nat.factorial_pos _
      have hxp : 0 ≤ x ^ (i + M) := pow_nonneg (by linarith) _
      calc ((i + M) ! : ℝ)⁻¹ * x ^ (i + M) * ‖iteratedDeriv (i + M) G 2‖
          ≤ ((i + M) ! : ℝ)⁻¹ * x ^ (i + M) * (((i + M) ! : ℝ) * B / (3 / 2) ^ (i + M)) := by
            gcongr
        _ = B * (x ^ (i + M) / (3 / 2) ^ (i + M)) := by field_simp
        _ = B * (x / (3 / 2)) ^ (i + M) := by rw [div_pow x (3 / 2 : ℝ)]
        _ ≤ B * (3 / 4) ^ (i + M) := by
            have hq : x / (3 / 2) ≤ 3 / 4 := by rw [div_le_iff₀ (by norm_num)]; linarith
            have hq0 : 0 ≤ x / (3 / 2) := by positivity
            exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq0 hq _) hB0
        _ = B * (3 / 4) ^ M * (3 / 4 : ℝ) ^ i := by rw [pow_add]; ring)
    calc ‖∑' i, t (i + M)‖ ≤ B * (3 / 4) ^ M * (1 - 3 / 4)⁻¹ := hle
      _ = 4 * B * (3 / 4) ^ M := by norm_num; ring

  have hσ1' : (σ : ℂ) ≠ 1 := by
    intro h; have : σ = 1 := by exact_mod_cast h
    linarith
  have hkey : F σ = ∑ i ∈ Finset.range M, (x : ℂ) ^ i * β i
      - lam * (((x ^ M / (x - 1) : ℝ)) : ℂ) + ∑' i, t (i + M) := by
    rw [hFG σ hσ1', ← hsplit, hfin]
    have hx1' : (x : ℂ) - 1 ≠ 0 := by
      intro h; have : x = 1 := by
        have h' : ((x - 1 : ℝ) : ℂ) = 0 := by push_cast; exact h
        have := Complex.ofReal_eq_zero.mp h'; linarith
      linarith
    have hσc : (σ : ℂ) - 1 = -((x : ℂ) - 1) := by rw [hxdef]; push_cast; ring
    rw [hσc]
    push_cast
    field_simp
    ring
  have hre := congrArg Complex.re hkey
  rw [Complex.add_re, Complex.sub_re] at hre
  have h1 : 1 ≤ (∑ i ∈ Finset.range M, (x : ℂ) ^ i * β i).re := by
    have := (Complex.le_def.mp hpos).1
    simpa using this
  have h2 : (lam * (((x ^ M / (x - 1) : ℝ)) : ℂ)).re ≤ ‖lam‖ * x ^ M / (x - 1) := by
    refine (Complex.re_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg]
    · ring_nf; rfl
    · exact div_nonneg (pow_nonneg (by linarith) _) (by linarith)
  have h3 : -(4 * B * (3 / 4) ^ M) ≤ (∑' i, t (i + M)).re := by
    have := Complex.abs_re_le_norm (∑' i, t (i + M))
    have := neg_abs_le (∑' i, t (i + M)).re
    linarith
  have hx1s : x - 1 = 1 - σ := by rw [hxdef]; ring
  rw [hx1s] at h2 hre
  rw [hre]
  linarith

end Formalism.ZeroFreeDirichlet
end
end

open Complex
open scoped ComplexOrder Nat

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma norm_le_of_log_bound {z : ℂ} {CL : ℝ} (q : ℕ) [NeZero q] (h : ‖z‖ ≤ CL * Real.log (3 * q)) :
    ‖z‖ ≤ |CL| * (3 * q) := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have h3 : (0 : ℝ) ≤ 3 * q := by positivity
  have hl0 : 0 ≤ Real.log (3 * q) := Real.log_nonneg (by linarith)
  have hl : Real.log (3 * q) ≤ 3 * q := Real.log_le_self h3
  calc ‖z‖ ≤ CL * Real.log (3 * q) := h
    _ ≤ |CL| * Real.log (3 * q) := mul_le_mul_of_nonneg_right (le_abs_self CL) hl0
    _ ≤ |CL| * (3 * q) := mul_le_mul_of_nonneg_left hl (abs_nonneg CL)

lemma exists_taylor_truncation_order (T : ℝ) (hT : 1 ≤ T) :
    ∃ M : ℕ, 1 ≤ M ∧ T * (3 / 4 : ℝ) ^ M ≤ 1 ∧ (M : ℝ) ≤ Real.log T / Real.log (4 / 3) + 2 := by
  have hl43 : 0 < Real.log (4 / 3 : ℝ) := Real.log_pos (by norm_num)
  have hT0 : 0 < T := by linarith
  have hx0 : 0 ≤ Real.log T / Real.log (4 / 3) := div_nonneg (Real.log_nonneg hT) hl43.le
  refine ⟨⌈Real.log T / Real.log (4 / 3)⌉₊ + 1, by omega, ?_, ?_⟩
  · have hM : Real.log T / Real.log (4 / 3) ≤ ((⌈Real.log T / Real.log (4 / 3)⌉₊ + 1 : ℕ) : ℝ) := by
      push_cast; linarith [Nat.le_ceil (Real.log T / Real.log (4 / 3))]
    have hlog : Real.log T ≤ ((⌈Real.log T / Real.log (4 / 3)⌉₊ + 1 : ℕ) : ℝ) * Real.log (4 / 3) := by
      have h := mul_le_mul_of_nonneg_right hM hl43.le
      rwa [div_mul_cancel₀ _ hl43.ne'] at h
    have hT' : T ≤ (4 / 3 : ℝ) ^ (⌈Real.log T / Real.log (4 / 3)⌉₊ + 1) := by
      calc T = Real.exp (Real.log T) := (Real.exp_log hT0).symm
        _ ≤ Real.exp (((⌈Real.log T / Real.log (4 / 3)⌉₊ + 1 : ℕ) : ℝ) * Real.log (4 / 3)) :=
          Real.exp_le_exp.mpr hlog
        _ = (4 / 3 : ℝ) ^ (⌈Real.log T / Real.log (4 / 3)⌉₊ + 1) := by
          rw [← Real.log_pow, Real.exp_log (by positivity)]
    have h34 : (4 / 3 : ℝ) ^ (⌈Real.log T / Real.log (4 / 3)⌉₊ + 1) * (3 / 4 : ℝ) ^ (⌈Real.log T / Real.log (4 / 3)⌉₊ + 1) = 1 := by
      rw [← mul_pow]; norm_num
    have hp : 0 < (3 / 4 : ℝ) ^ (⌈Real.log T / Real.log (4 / 3)⌉₊ + 1) := by positivity
    calc T * (3 / 4 : ℝ) ^ (⌈Real.log T / Real.log (4 / 3)⌉₊ + 1)
        ≤ (4 / 3 : ℝ) ^ (⌈Real.log T / Real.log (4 / 3)⌉₊ + 1) * (3 / 4 : ℝ) ^ (⌈Real.log T / Real.log (4 / 3)⌉₊ + 1) :=
          mul_le_mul_of_nonneg_right hT' hp.le
      _ = 1 := h34
  · push_cast
    linarith [Nat.ceil_lt_add_one hx0]

lemma two_sub_pow_le_exp {A P σ : ℝ} {M : ℕ} (hA : 0 ≤ A) (hσ1 : 7 / 8 ≤ σ) (hσ2 : σ < 1)
    (hM : (M : ℝ) ≤ A + P) : (2 - σ) ^ M ≤ Real.exp A * Real.exp (P * (1 - σ)) := by
  have h1 : 0 < 1 - σ := by linarith
  have hb : 2 - σ ≤ Real.exp (1 - σ) := by
    have := Real.add_one_le_exp (1 - σ); linarith
  have hb0 : 0 ≤ 2 - σ := by linarith
  calc (2 - σ) ^ M ≤ Real.exp (1 - σ) ^ M := pow_le_pow_left₀ hb0 hb M
    _ = Real.exp (M * (1 - σ)) := by rw [← Real.exp_nat_mul]
    _ ≤ Real.exp (A + P * (1 - σ)) := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_right hM h1.le, mul_nonneg hA (by linarith : (0 : ℝ) ≤ σ)]
    _ = Real.exp A * Real.exp (P * (1 - σ)) := Real.exp_add _ _

theorem product_lfunction_key_inequality : BqKeyOf := by
  intro hCoeff hEnt hGrow hL1
  obtain ⟨Cg, Kg, hg⟩ := hGrow
  obtain ⟨CL, hL⟩ := hL1
  obtain ⟨c0, hc0def⟩ : ∃ c : ℝ, c = |Cg| + 54 * |CL| ^ 3 + 1 := ⟨_, rfl⟩
  obtain ⟨K', hK'def⟩ : ∃ k : ℝ, k = max Kg 2 := ⟨_, rfl⟩
  obtain ⟨ℓ, hℓdef⟩ : ∃ l : ℝ, l = Real.log (4 / 3) := ⟨_, rfl⟩
  have hℓ : 0 < ℓ := by rw [hℓdef]; exact Real.log_pos (by norm_num)
  have hc0 : 1 ≤ c0 := by
    rw [hc0def]; have := abs_nonneg Cg; have := pow_nonneg (abs_nonneg CL) 3; linarith
  have hKgK : Kg ≤ K' := by rw [hK'def]; exact le_max_left _ _
  have h2K : (2 : ℝ) ≤ K' := by rw [hK'def]; exact le_max_right _ _
  refine ⟨Real.exp 2 * Real.exp (Real.log (8 * c0) / (8 * ℓ)), K' / ℓ,
    div_nonneg (by linarith) hℓ.le, ?_⟩
  intro q₁ q₂ _ _ _ χ₁ χ₂ ψ h1 h2 h1ne h2ne hψne hψ σ hσ1 hσ2
  have h1σ : 0 < 1 - σ := by linarith
  have hq₁ : (1 : ℝ) ≤ q₁ := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q₁)
  have hq₂ : (1 : ℝ) ≤ q₂ := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q₂)
  have hN : ((q₁ * q₂ : ℕ) : ℝ) = (q₁ : ℝ) * q₂ := by push_cast; ring
  have hN1 : (1 : ℝ) ≤ ((q₁ * q₂ : ℕ) : ℝ) := by rw [hN]; nlinarith
  obtain ⟨a, ha0, ha1, habs, hFa⟩ := hCoeff q₁ q₂ χ₁ χ₂ ψ h1 h2 hψ
  obtain ⟨G, hG, hFG⟩ := hEnt q₁ q₂ χ₁ χ₂ ψ h1ne h2ne hψne
  have hlam : ‖lamBq χ₁ χ₂ ψ‖ ≤ 27 * |CL| ^ 3 * ((q₁ * q₂ : ℕ) : ℝ) ^ 2 := by
    have e1 := norm_le_of_log_bound q₁ (hL q₁ χ₁ h1ne)
    have e2 := norm_le_of_log_bound q₂ (hL q₂ χ₂ h2ne)
    have e3 := norm_le_of_log_bound (q₁ * q₂) (hL (q₁ * q₂) ψ hψne)
    simp only [lamBq, norm_mul]
    calc _ ≤ (|CL| * (3 * q₁)) * (|CL| * (3 * q₂)) * (|CL| * (3 * ((q₁ * q₂ : ℕ) : ℝ))) :=
          mul_le_mul (mul_le_mul e1 e2 (norm_nonneg _) (by positivity)) e3 (norm_nonneg _) (by positivity)
      _ = 27 * |CL| ^ 3 * ((q₁ * q₂ : ℕ) : ℝ) ^ 2 := by rw [hN]; ring
  have hKg : ((q₁ * q₂ : ℕ) : ℝ) ^ Kg ≤ ((q₁ * q₂ : ℕ) : ℝ) ^ K' :=
    Real.rpow_le_rpow_of_exponent_le hN1 hKgK
  have hK2 : ((q₁ * q₂ : ℕ) : ℝ) ^ (2 : ℕ) ≤ ((q₁ * q₂ : ℕ) : ℝ) ^ K' := by
    rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num; linarith)
  have hNK0 : 0 ≤ ((q₁ * q₂ : ℕ) : ℝ) ^ K' := by positivity
  have hB : ∀ s ∈ Metric.sphere (2 : ℂ) (3 / 2), ‖G s‖ ≤ c0 * ((q₁ * q₂ : ℕ) : ℝ) ^ K' := by
    intro s hs
    rw [mem_sphere_iff_norm] at hs
    have hs1 : s ≠ 1 := by rintro rfl; norm_num at hs
    have hd : (1 / 2 : ℝ) ≤ ‖s - 1‖ := by
      have h := norm_sub_le (s - 1) (1 : ℂ)
      have e : s - 1 - 1 = s - 2 := by ring
      rw [e, hs, norm_one] at h
      linarith
    have hGs : G s = Fbq χ₁ χ₂ ψ s - lamBq χ₁ χ₂ ψ / (s - 1) := by rw [hFG s hs1]; ring
    have hF := hg q₁ q₂ χ₁ χ₂ ψ h1ne h2ne hψne s hs
    have hdiv : ‖lamBq χ₁ χ₂ ψ / (s - 1)‖ ≤ 2 * ‖lamBq χ₁ χ₂ ψ‖ := by
      rw [norm_div, div_le_iff₀ (by linarith)]
      nlinarith [norm_nonneg (lamBq χ₁ χ₂ ψ)]
    have hc3 : 0 ≤ 54 * |CL| ^ 3 := by positivity
    calc ‖G s‖ ≤ ‖Fbq χ₁ χ₂ ψ s‖ + ‖lamBq χ₁ χ₂ ψ / (s - 1)‖ := by rw [hGs]; exact norm_sub_le _ _
      _ ≤ Cg * ((q₁ * q₂ : ℕ) : ℝ) ^ Kg + 2 * (27 * |CL| ^ 3 * ((q₁ * q₂ : ℕ) : ℝ) ^ 2) := by linarith
      _ ≤ c0 * ((q₁ * q₂ : ℕ) : ℝ) ^ K' := by
        rw [hc0def]
        nlinarith [mul_le_mul_of_nonneg_right (le_abs_self Cg) (by positivity : (0 : ℝ) ≤ ((q₁ * q₂ : ℕ) : ℝ) ^ Kg),
          mul_le_mul_of_nonneg_left hKg (abs_nonneg Cg), mul_le_mul_of_nonneg_left hK2 hc3]
  have hNK1 : 1 ≤ ((q₁ * q₂ : ℕ) : ℝ) ^ K' := Real.one_le_rpow hN1 (by linarith)
  have hT : 1 ≤ 8 * (c0 * ((q₁ * q₂ : ℕ) : ℝ) ^ K') := by
    nlinarith [mul_le_mul hc0 hNK1 zero_le_one (by linarith)]
  obtain ⟨M, hM1, hTM, hMle⟩ := exists_taylor_truncation_order _ hT
  rw [← hℓdef] at hMle
  have hcore := lseries_taylor_lower_bound ha0 ha1 habs hG hFa hFG hB hσ1 hσ2 hM1
  have hpow := two_sub_pow_le_exp (A := 2) (P := Real.log (8 * (c0 * ((q₁ * q₂ : ℕ) : ℝ) ^ K')) / ℓ)
    (M := M) (by norm_num) hσ1 hσ2 (by linarith)
  have hlogT : Real.log (8 * (c0 * ((q₁ * q₂ : ℕ) : ℝ) ^ K')) =
      Real.log (8 * c0) + K' * Real.log ((q₁ * q₂ : ℕ) : ℝ) := by
    rw [← mul_assoc, Real.log_mul (by positivity) (Real.rpow_pos_of_pos (by linarith) _).ne',
      Real.log_rpow (by linarith)]
  have hlogc : 0 ≤ Real.log (8 * c0) := Real.log_nonneg (by linarith)
  have hexp : Real.exp (Real.log (8 * (c0 * ((q₁ * q₂ : ℕ) : ℝ) ^ K')) / ℓ * (1 - σ)) ≤
      Real.exp (Real.log (8 * c0) / (8 * ℓ)) * ((q₁ * q₂ : ℕ) : ℝ) ^ (K' / ℓ * (1 - σ)) := by
    rw [Real.rpow_def_of_pos (show (0 : ℝ) < ((q₁ * q₂ : ℕ) : ℝ) by linarith) (K' / ℓ * (1 - σ)),
      ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [hlogT]
    have eL : (Real.log (8 * c0) + K' * Real.log ((q₁ * q₂ : ℕ) : ℝ)) / ℓ * (1 - σ) =
        (Real.log (8 * c0) * (1 - σ) + K' * Real.log ((q₁ * q₂ : ℕ) : ℝ) * (1 - σ)) / ℓ := by ring
    have eR : Real.log (8 * c0) / (8 * ℓ) + Real.log ((q₁ * q₂ : ℕ) : ℝ) * (K' / ℓ * (1 - σ)) =
        (Real.log (8 * c0) / 8 + K' * Real.log ((q₁ * q₂ : ℕ) : ℝ) * (1 - σ)) / ℓ := by ring
    rw [eL, eR]
    apply div_le_div_of_nonneg_right _ hℓ.le
    nlinarith [mul_le_mul_of_nonneg_left (by linarith : 1 - σ ≤ 1 / 8) hlogc]
  have hpow' : (2 - σ) ^ M ≤ Real.exp 2 * Real.exp (Real.log (8 * c0) / (8 * ℓ)) *
      ((q₁ * q₂ : ℕ) : ℝ) ^ (K' / ℓ * (1 - σ)) :=
    hpow.trans ((mul_le_mul_of_nonneg_left hexp (Real.exp_pos 2).le).trans_eq (by ring))
  have h34 : 4 * (c0 * ((q₁ * q₂ : ℕ) : ℝ) ^ K') * (3 / 4 : ℝ) ^ M ≤ 1 / 2 := by linarith
  have hlam0 := norm_nonneg (lamBq χ₁ χ₂ ψ)
  have hdiv : ‖lamBq χ₁ χ₂ ψ‖ * (2 - σ) ^ M / (1 - σ) ≤
      Real.exp 2 * Real.exp (Real.log (8 * c0) / (8 * ℓ)) * ‖lamBq χ₁ χ₂ ψ‖ *
        ((q₁ * q₂ : ℕ) : ℝ) ^ (K' / ℓ * (1 - σ)) / (1 - σ) := by
    apply div_le_div_of_nonneg_right _ h1σ.le
    nlinarith [mul_le_mul_of_nonneg_left hpow' hlam0]
  linarith

end Formalism.ZeroFreeDirichlet
