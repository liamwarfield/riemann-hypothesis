module

public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.ZetaInvBound
public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.ZetaGrowth

@[expose] public section

section -- merged from Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.ZeroFreeOf
section -- merged from Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.ZfoNegReLeNorm
section -- merged from Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.ZfoTermReNonneg
open Complex Metric

noncomputable section

namespace Formalism.ZF

lemma zfo_zero_re_lt {ρ : ℂ} {σ : ℝ} (hσ : 1 < σ) (h : riemannZeta ρ = 0) : ρ.re < σ := by
  by_contra hc
  push_neg at hc
  exact riemannZeta_ne_zero_of_one_lt_re (lt_of_lt_of_le hσ hc) h

lemma zfo_term_re_nonneg {z ρ : ℂ} (n : ℕ) (h : ρ.re < z.re) :
    0 ≤ ((n : ℂ) / (z - ρ)).re := by
  rw [Complex.div_re]
  simp only [Complex.natCast_re, Complex.natCast_im, zero_mul, zero_div, add_zero, Complex.sub_re]
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg n) (by linarith)) (Complex.normSq_nonneg _)

lemma zfo_landau (hLL : LandauLocal) {σ τ M : ℝ} (hσ : 1 < σ) (hM : 1 ≤ M)
    (hdiff : DifferentiableOn ℂ riemannZeta (closedBall ((σ : ℂ) + τ * I) (1 / 2)))
    (hbd : ∀ w ∈ closedBall ((σ : ℂ) + τ * I) (1 / 2),
      ‖riemannZeta w‖ ≤ M * ‖riemannZeta ((σ : ℂ) + τ * I)‖) :
    ∃ S : ℝ, 0 ≤ S ∧
      (-(deriv riemannZeta ((σ : ℂ) + τ * I) / riemannZeta ((σ : ℂ) + τ * I))).re
        ≤ 144 * Real.log M - S ∧
      ∀ β : ℝ, riemannZeta ((β : ℂ) + τ * I) = 0 → σ - β ≤ 1 / 6 → 1 / (σ - β) ≤ S := by
  set s : ℂ := (σ : ℂ) + τ * I with hs
  have hsre : s.re = σ := by simp [hs]
  have hs0 : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by rw [hsre]; exact hσ)
  obtain ⟨Z, m, hZ, hm, -, hbound⟩ := hLL riemannZeta s (1 / 2) M (by norm_num) hM hdiff hs0 hbd
  have hZre : ∀ ρ ∈ Z, ρ.re < s.re := fun ρ hρ => by
    rw [hsre]; exact zfo_zero_re_lt hσ ((hZ ρ).1 hρ).2
  refine ⟨∑ ρ ∈ Z, ((m ρ : ℂ) / (s - ρ)).re,
    Finset.sum_nonneg (fun ρ hρ => zfo_term_re_nonneg _ (hZre ρ hρ)), ?_, ?_⟩
  · have hb := hbound s (Metric.mem_closedBall_self (by norm_num)) hs0
    have hw := (abs_le.1 ((Complex.abs_re_le_norm _).trans hb)).1
    rw [Complex.sub_re, Complex.re_sum] at hw
    rw [Complex.neg_re]
    have h72 : 72 * Real.log M / (1 / 2) = 144 * Real.log M := by ring
    linarith
  · intro β hβ hβσ
    set ρ : ℂ := (β : ℂ) + τ * I with hρ
    have hρre : ρ.re = β := by simp [hρ]
    have hβlt : β < σ := by
      have := zfo_zero_re_lt hσ hβ
      rwa [hρre] at this
    have hdiff' : s - ρ = ((σ - β : ℝ) : ℂ) := by
      rw [hs, hρ]; push_cast; ring
    have hρZ : ρ ∈ Z := by
      rw [hZ]
      refine ⟨?_, hβ⟩
      rw [Metric.mem_closedBall, dist_eq_norm, ← neg_sub, norm_neg, hdiff', Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by linarith)]
      linarith
    have hterm : ((m ρ : ℂ) / (s - ρ)).re = (m ρ : ℝ) / (σ - β) := by
      rw [hdiff', ← Complex.ofReal_natCast, ← Complex.ofReal_div, Complex.ofReal_re]
    calc 1 / (σ - β) ≤ (m ρ : ℝ) / (σ - β) :=
          (div_le_div_iff_of_pos_right (by linarith)).2 (by exact_mod_cast hm ρ hρZ)
      _ = ((m ρ : ℂ) / (s - ρ)).re := hterm.symm
      _ ≤ ∑ ρ' ∈ Z, ((m ρ' : ℂ) / (s - ρ')).re :=
          Finset.single_le_sum (f := fun ρ' => ((m ρ' : ℂ) / (s - ρ')).re)
            (fun ρ' hρ' => zfo_term_re_nonneg _ (hZre ρ' hρ')) hρZ

end Formalism.ZF
end
end

open Complex Metric

noncomputable section

namespace Formalism.ZF

lemma zfo_neg_re_le_norm (x : ℂ) : (-x).re ≤ ‖x‖ := by
  rw [Complex.neg_re]
  exact (neg_le_abs x.re).trans (Complex.abs_re_le_norm x)

lemma zfo_large (h341 : ThreeFourOne) (hLDR : LogDerivRight) (hG : ZetaGrowth)
    (hI : ZetaInvBound) (hLL : LandauLocal) :
    ∃ t₀ : ℝ, 3 ≤ t₀ ∧ ∀ β t : ℝ, t₀ ≤ |t| → riemannZeta ((β : ℂ) + t * I) = 0 →
      β < 1 - (1 / 200000) / Real.log (|t| + 2) := by
  obtain ⟨C, hC0, hC⟩ := hLDR
  refine ⟨max 3 (Real.exp (3 * C)), le_max_left _ _, fun β t ht hzero => ?_⟩
  have hT3 : 3 ≤ |t| := le_trans (le_max_left _ _) ht
  have hTe : Real.exp (3 * C) ≤ |t| := le_trans (le_max_right _ _) ht
  obtain ⟨L, hLdef⟩ : ∃ L, L = Real.log (|t| + 2) := ⟨_, rfl⟩
  rw [← hLdef]
  have hL1 : 1 < L := by
    rw [hLdef, Real.lt_log_iff_exp_lt (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hL0 : 0 < L := by linarith
  have hLC : 3 * C ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le (by linarith)]
    linarith
  have hLT : L ≤ |t| + 2 := by
    rw [hLdef]
    have := Real.log_le_sub_one_of_pos (show 0 < |t| + 2 by linarith)
    linarith
  obtain ⟨σ, hσdef⟩ : ∃ σ : ℝ, σ = 1 + (1 / 10000) / L := ⟨_, rfl⟩
  have hsm : 0 < (1 / 10000) / L := by positivity
  have hσ1 : 1 < σ := by rw [hσdef]; linarith
  have hsm1 : (1 / 10000) / L ≤ 1 := by
    rw [div_le_one hL0]
    linarith
  have hσ2 : σ ≤ 2 := by rw [hσdef]; linarith
  have hσinv : 1 / (σ - 1) = 10000 * L := by
    rw [hσdef, show (1 : ℝ) + 1 / 10000 / L - 1 = (1 / 10000) / L by ring, one_div_div]
    ring
  have hσK : 2 / (σ - 1) ≤ 20000 * (|t| + 2) := by
    have : 2 / (σ - 1) = 2 * (1 / (σ - 1)) := by ring
    rw [this, hσinv]
    linarith
  have hτ2 : 3 ≤ |2 * t| := by
    rw [abs_mul]
    norm_num
    linarith
  have hτ2T : |2 * t| ≤ 2 * |t| := by
    rw [abs_mul]
    norm_num
  have hM1 : (1 : ℝ) ≤ (|t| + 2) ^ 10 := one_le_pow₀ (by linarith)
  obtain ⟨S1, hS10, hS1, hS1z⟩ := zfo_landau hLL hσ1 hM1 (zfo_diff_ball hT3)
    (zfo_M_bound hG hI hσ1 hσ2 hσK hT3 hT3 (by linarith))
  obtain ⟨S2, hS20, hS2, -⟩ := zfo_landau hLL hσ1 hM1 (zfo_diff_ball hτ2)
    (zfo_M_bound hG hI hσ1 hσ2 hσK hT3 hτ2 hτ2T)
  have e2 : ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * I) = (σ : ℂ) + 2 * t * I := by
    push_cast
    ring
  rw [e2] at hS2
  have hlogM : Real.log ((|t| + 2) ^ 10) = 10 * L := by
    rw [Real.log_pow, hLdef]
    push_cast
    ring
  rw [hlogM] at hS1 hS2
  have h341' := h341 σ t hσ1
  have hR1 : (-(deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ))).re ≤ 1 / (σ - 1) + C := by
    have h := hC (σ : ℂ) (by simpa using hσ1)
    simp only [Complex.ofReal_re] at h
    exact (zfo_neg_re_le_norm _).trans h
  rw [hσinv] at hR1
  have hβσ : β < σ := by
    have := zfo_zero_re_lt (ρ := (β : ℂ) + t * I) hσ1 hzero
    simpa using this
  by_cases hcase : σ - β ≤ 1 / 6
  · have hA := hS1z β hzero hcase
    have hd : 0 < σ - β := by linarith
    have key : 4 * (1 / (σ - β)) ≤ 37201 * L := by linarith
    rw [mul_one_div, div_le_iff₀ hd] at key
    have h3 : (21 / 200000) / L < σ - β := by
      rw [div_lt_iff₀ hL0]
      nlinarith
    have h4 : (21 / 200000) / L = (1 / 200000) / L + (1 / 10000) / L := by ring
    linarith
  · push_neg at hcase
    have h4 : (1 / 10000) / L ≤ 1 / 10000 := div_le_self (by norm_num) hL1.le
    have h5 : (1 / 200000) / L ≤ 1 / 200000 := div_le_self (by norm_num) hL1.le
    linarith

end Formalism.ZF
end
end

open Complex

noncomputable section

namespace Formalism.ZF

theorem classicalZeroFreeRegionOfBounds : ZeroFreeOf := by
  intro h341 hLDR hG hI hSH hLL
  obtain ⟨t₀, -, ht₀⟩ := zfo_large h341 hLDR hG hI hLL
  obtain ⟨c₂, hc₂, hsmall⟩ := hSH t₀
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨min (1 / 200000) (c₂ * Real.log 2), lt_min (by norm_num) (mul_pos hc₂ hlog2), ?_⟩
  intro s hs1 hre
  have hL : Real.log 2 ≤ Real.log (|s.im| + 2) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg s.im])
  have hLpos : 0 < Real.log (|s.im| + 2) := lt_of_lt_of_le hlog2 hL
  rcases le_or_gt |s.im| t₀ with hT | hT
  · apply hsmall s hT _ hs1
    have hc : min (1 / 200000) (c₂ * Real.log 2) / Real.log (|s.im| + 2) ≤ c₂ := by
      rw [div_le_iff₀ hLpos]
      calc min (1 / 200000) (c₂ * Real.log 2) ≤ c₂ * Real.log 2 := min_le_right _ _
        _ ≤ c₂ * Real.log (|s.im| + 2) := mul_le_mul_of_nonneg_left hL hc₂.le
    linarith
  · intro hz
    have hs : s = (s.re : ℂ) + s.im * I := (Complex.re_add_im s).symm
    have hβ := ht₀ s.re s.im hT.le (by rw [← hs]; exact hz)
    have h2 : min (1 / 200000) (c₂ * Real.log 2) / Real.log (|s.im| + 2) ≤ (1 / 200000) / Real.log (|s.im| + 2) :=
      div_le_div_of_nonneg_right (min_le_left _ _) hLpos.le
    linarith

end Formalism.ZF
end
end

section -- merged from Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.SmallHeight
open Complex Set Filter Topology

noncomputable section

namespace Formalism.ZF

theorem zeroFreeBoundedHeight : SmallHeight := by
  unfold SmallHeight
  intro T
  have hopen : IsOpen {s : ℂ | s ≠ 1 → riemannZeta s ≠ 0} := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    by_cases hz1 : z = 1
    · subst hz1
      have h := riemannZeta_residue_one.eventually_ne one_ne_zero
      rw [eventually_nhdsWithin_iff] at h
      filter_upwards [h] with x hx hx1
      exact right_ne_zero_of_mul (hx hx1)
    · have hc : ContinuousAt riemannZeta z := (differentiableAt_riemannZeta hz1).continuousAt
      filter_upwards [hc.eventually_ne (hz hz1)] with x hx _
      exact hx
  set K : Set ℂ := (fun y : ℝ => (1 : ℂ) + (y : ℂ) * I) '' Icc (-T) T
  have hKc : IsCompact K :=
    isCompact_Icc.image (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))
  have hKsub : K ⊆ {s : ℂ | s ≠ 1 → riemannZeta s ≠ 0} := by
    rintro _ ⟨y, -, rfl⟩ _
    apply riemannZeta_ne_zero_of_one_le_re
    simp
  obtain ⟨δ, hδ, hsub⟩ := hKc.exists_cthickening_subset_open hopen hKsub
  refine ⟨δ, hδ, fun s hs hre hs1 => ?_⟩
  by_cases hle : 1 ≤ s.re
  · exact riemannZeta_ne_zero_of_one_le_re hle
  · push_neg at hle
    have hp : (1 : ℂ) + (s.im : ℂ) * I ∈ K := ⟨s.im, abs_le.mp hs, rfl⟩
    have hre1 : ((1 : ℂ) + (s.im : ℂ) * I).re = 1 := by simp
    have him1 : s.im = ((1 : ℂ) + (s.im : ℂ) * I).im := by simp
    have hd : dist s ((1 : ℂ) + (s.im : ℂ) * I) ≤ δ := by
      rw [Complex.dist_of_im_eq him1, Real.dist_eq, hre1, abs_le]
      constructor <;> linarith
    exact hsub (Metric.mem_cthickening_of_dist_le _ _ _ _ hp hd) hs1

end Formalism.ZF
end
end

section -- merged from Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.ThreeFourOne
open Complex ArithmeticFunction

noncomputable section

namespace Formalism.ZF

namespace VonMangoldtMertensInequality

lemma re_term_vonMangoldt {n : ℕ} (hn : n ≠ 0) (σ y : ℝ) :
    (LSeries.term (fun m => (Λ m : ℂ)) ((σ : ℂ) + y * I) n).re =
      Λ n * Real.exp (-σ * Real.log n) * Real.cos (y * Real.log n) := by
  rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← Complex.cpow_neg, Complex.re_ofReal_mul,
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hn), Complex.exp_re]
  have hre : (Complex.log (n : ℂ)).re = Real.log n := by
    rw [Complex.log_re, Complex.norm_natCast]
  have him : (Complex.log (n : ℂ)).im = 0 := by
    rw [Complex.log_im, Complex.natCast_arg]
  simp only [Complex.mul_re, Complex.mul_im, hre, him, Complex.neg_re, Complex.neg_im,
    Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  rw [mul_assoc]
  congr 2
  · congr 1
    ring
  · rw [← Real.cos_neg]
    congr 1
    ring

lemma hasSum_re_L {σ : ℝ} (hσ : 1 < σ) (y : ℝ) :
    HasSum (fun n => (LSeries.term (fun m => (Λ m : ℂ)) ((σ : ℂ) + y * I) n).re)
      (-(deriv riemannZeta ((σ : ℂ) + y * I) / riemannZeta ((σ : ℂ) + y * I))).re := by
  have hs : 1 < ((σ : ℂ) + y * I).re := by simp [hσ]
  have h1 := (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).LSeriesHasSum
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs, neg_div] at h1
  simpa only [Complex.reCLM_apply] using Complex.reCLM.hasSum h1

lemma comb_nonneg (a θ : ℝ) (ha : 0 ≤ a) :
    0 ≤ 3 * a + 4 * (a * Real.cos θ) + a * Real.cos (2 * θ) := by
  rw [Real.cos_two_mul]
  nlinarith [mul_nonneg ha (sq_nonneg (1 + Real.cos θ))]

end VonMangoldtMertensInequality

open VonMangoldtMertensInequality in
theorem mertensInequality : ThreeFourOne := by
  intro σ t hσ
  have h0 := hasSum_re_L hσ 0
  have h1 := hasSum_re_L hσ t
  have h2 := hasSum_re_L hσ (2 * t)
  have hs := ((h0.mul_left 3).add (h1.mul_left 4)).add h2
  have key := HasSum.nonneg (fun n => ?_) hs
  · have e0 : ((σ : ℂ) + ((0 : ℝ) : ℂ) * I) = σ := by simp
    have e2 : ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * I) = σ + 2 * t * I := by push_cast; ring
    rw [e0, e2] at key
    exact key
  · by_cases hn : n = 0
    · subst hn
      simp [LSeries.term_zero]
    · rw [re_term_vonMangoldt hn, re_term_vonMangoldt hn, re_term_vonMangoldt hn]
      have ha : 0 ≤ Λ n * Real.exp (-σ * Real.log n) :=
        mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.exp_pos _).le
      have hc := comb_nonneg _ (t * Real.log n) ha
      rw [zero_mul, Real.cos_zero, mul_one, show 2 * t * Real.log n = 2 * (t * Real.log n) by ring]
      linarith

end Formalism.ZF
end
end

noncomputable section

namespace Formalism.ZF

theorem landauLocal : LandauLocal := localZeroExpansionOfFactorization zeroFactorization logDerivBoundOnBall

theorem zeroFreeRegion : ZeroFreeRegion :=
  classicalZeroFreeRegionOfBounds mertensInequality logDerivBoundRightHalfPlane growthBound zetaInvBound_statement
    zeroFreeBoundedHeight landauLocal

end Formalism.ZF
