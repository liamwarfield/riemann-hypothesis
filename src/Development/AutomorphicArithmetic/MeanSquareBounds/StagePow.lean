module

public import Development.AutomorphicArithmetic.MeanSquareBounds.meanSqK
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.TailContour
public import Formalism.GL3MeanSquares.HookFormulaTorsion.NumericalZeroDensityBound
public import Formalism.GL3MeanSquares.HookFormulaTorsion.CharacterEstimateOfHypothesis
public import Development.AutomorphicArithmetic.MeanSquareBounds.IndUnique
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.CountZAll

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.MeanSquareBounds.TailKExp
open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace QH

private theorem tailK_exp (ε K A : ℝ) (hε : 0 < ε) :
    ∀ᶠ Y : ℝ in Filter.atTop, A * (Y ^ (404 * K) * Real.exp (-(Y ^ (ε / 6)))) ≤ 1 / 3 := by
  have hc : 0 < ε / 6 := by positivity
  have hg := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (404 * K / (ε / 6)) 1 one_pos).comp
    (tendsto_rpow_atTop hc)
  have hlim : Filter.Tendsto (fun Y : ℝ => A * (Y ^ (404 * K) * Real.exp (-(Y ^ (ε / 6)))))
      Filter.atTop (nhds 0) := by
    have := hg.const_mul A
    rw [mul_zero] at this
    refine this.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop 0] with Y hY
    simp only [Function.comp_apply, neg_mul, one_mul]
    rw [← Real.rpow_mul hY.le, mul_div_cancel₀ _ hc.ne']
  exact hlim.eventually (ge_mem_nhds (by norm_num))

private theorem tailK_num (ε K A : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hK : 1 ≤ K) (hA0 : 0 ≤ A) :
    ∃ Y₀ : ℝ, 3 ≤ Y₀ ∧
    ∀ Y x Q : ℝ, Y₀ ≤ Y → x = Y ^ K → 0 < Q → Y ^ (ε / 6) ≤ Real.log Q → Real.log Q ≤ Y ^ (ε / 4) →
      x * ((A * Real.log Q * (Real.log Q * (1 / x ^ 2) * (x ^ 400) ^ (1 - 1 / 400 + ε / K / 1600) + (x ^ 400) ^ 2 / Q)
          + x ^ 400 * (1 / x ^ 2) * (x ^ 400 * (1 / x ^ 2) + 1) * Real.log (x ^ 400 + x ^ 400 * (1 / x ^ 2)) / x ^ 400)
          / (x ^ 400 * (1 / x ^ 2))) ≤ Y ^ ε := by
  have hev1 := tailK_exp ε K A hε
  have hev2 : ∀ᶠ Y : ℝ in Filter.atTop, 3 * A ≤ Y ^ (ε / 4) :=
    (tendsto_rpow_atTop (by positivity)).eventually_ge_atTop _
  have hev3 : ∀ᶠ Y : ℝ in Filter.atTop, 3 * 802 ≤ Y ^ ε :=
    (tendsto_rpow_atTop hε).eventually_ge_atTop _
  obtain ⟨Y₁, hY₁⟩ := Filter.eventually_atTop.1 (hev1.and (hev2.and hev3))
  refine ⟨max Y₁ 3, le_max_right _ _, ?_⟩
  intro Y x Q hY hx hQ hl1 hl2
  have hY1 : Y₁ ≤ Y := (le_max_left _ _).trans hY
  have hY3 : 3 ≤ Y := (le_max_right _ _).trans hY
  obtain ⟨h1, h2, h3⟩ := hY₁ Y hY1
  have hY0 : 0 < Y := by linarith
  have hK0 : K ≠ 0 := by positivity
  have hxY : Y ≤ x := by
    rw [hx]; simpa using Real.rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ) ≤ Y) hK
  have hx0 : 0 < x := by linarith
  have hx3 : 3 ≤ x := by linarith
  rw [Formalism.HermitianLattices.Ext.BoxTail.tail_num_rpow x (ε / K) hx0,
    Formalism.HermitianLattices.Ext.BoxTail.tail_num_alg x Q A (Real.log Q) (x ^ (ε / K / 4))
      (Real.log (x ^ 400 + x ^ 400 * (1 / x ^ 2))) hx0 hQ]
  have ha : x ^ (ε / K / 4) = Y ^ (ε / 4) := by
    rw [hx, ← Real.rpow_mul hY0.le]
    congr 1
    field_simp
  have hlpos : 0 ≤ Real.log Q := le_trans (by positivity) hl1
  have hu1 : Y ^ (ε / 4) ≤ Y := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ) ≤ Y) (by linarith : ε / 4 ≤ 1)
  have huY : Y ^ (ε / 4) ≤ x := hu1.trans hxY
  have hlx : Real.log Q ≤ x := hl2.trans huY
  have ht : Real.exp (Y ^ (ε / 6)) ≤ Q := (Real.le_log_iff_exp_le hQ).1 hl1
  have hx404 : Y ^ (404 * K) = x ^ 404 := by
    rw [hx, ← Real.rpow_mul_natCast hY0.le]
    congr 1
    push_cast
    ring
  have hsecond : A * (Real.log Q * x ^ 403 / Q) ≤ 1 / 3 := by
    have hQe : 1 / Q ≤ Real.exp (-(Y ^ (ε / 6))) := by
      rw [Real.exp_neg, ← one_div]
      exact one_div_le_one_div_of_le (Real.exp_pos _) ht
    have hm : Real.log Q * x ^ 403 / Q ≤ Y ^ (404 * K) * Real.exp (-(Y ^ (ε / 6))) := by
      rw [hx404]
      calc Real.log Q * x ^ 403 / Q = Real.log Q * x ^ 403 * (1 / Q) := by ring
        _ ≤ x * x ^ 403 * Real.exp (-(Y ^ (ε / 6))) := by gcongr
        _ = x ^ 404 * Real.exp (-(Y ^ (ε / 6))) := by ring
    exact (mul_le_mul_of_nonneg_left hm hA0).trans h1
  have hthird := Formalism.HermitianLattices.Ext.BoxTail.tail_num_third x hx3
  rw [ha]
  have hu0 : 0 < Y ^ (ε / 4) := Real.rpow_pos_of_pos hY0 _
  have hu4 : Y ^ ε = (Y ^ (ε / 4)) ^ 4 := by
    rw [← Real.rpow_mul_natCast hY0.le]
    congr 1
    push_cast
    ring
  have hfirst : A * Real.log Q ^ 2 * Y ^ (ε / 4) ≤ (Y ^ (ε / 4)) ^ 4 / 3 := by
    have hl2' : Real.log Q ^ 2 ≤ (Y ^ (ε / 4)) ^ 2 := pow_le_pow_left₀ hlpos hl2 2
    have hm : A * Real.log Q ^ 2 * Y ^ (ε / 4) ≤ A * (Y ^ (ε / 4)) ^ 3 := by
      calc A * Real.log Q ^ 2 * Y ^ (ε / 4) ≤ A * (Y ^ (ε / 4)) ^ 2 * Y ^ (ε / 4) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hl2' hA0) hu0.le
        _ = A * (Y ^ (ε / 4)) ^ 3 := by ring
    nlinarith [mul_nonneg (sub_nonneg.2 h2) (pow_pos hu0 3).le]
  rw [hu4] at h3 ⊢
  linarith

theorem tailK :
    ∀ ε K : ℝ, 0 < ε → ε ≤ 1 → 1 ≤ K → ∃ Y₀ : ℝ, ∀ Y ≥ Y₀, ∀ (Q : ℝ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
      Y ^ (ε / 6) ≤ Real.log Q → Real.log Q ≤ Y ^ (ε / 4) → GoodC Q χ →
      ‖((Y ^ K : ℝ) : ℂ) * tailL χ ((Y ^ K) ^ 400)‖ ≤ Y ^ ε := by
  intro ε K hε hε1 hK
  have hK0 : 0 < K := by linarith
  have hδ0 : 0 < ε / K / 1600 := by positivity
  have hδ1 : ε / K / 1600 ≤ 1 / 800 := by
    have : ε / K ≤ 1 := (div_le_one hK0).2 (by linarith)
    linarith
  obtain ⟨A, hA0, hA⟩ := Formalism.HermitianLattices.Ext.BoxTail.tail_contour (ε / K / 1600) hδ0 hδ1
  obtain ⟨Y₀, hY₀3, hY₀⟩ := tailK_num ε K A hε hε1 hK hA0
  refine ⟨Y₀, fun Y hY Q N _ χ hl1 hl2 hG => ?_⟩
  obtain ⟨hχ1, hNQ, hZ⟩ := hG
  have hY3 : 3 ≤ Y := le_trans hY₀3 hY
  have hY0 : 0 < Y := by linarith
  have hxY : Y ≤ Y ^ K := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ) ≤ Y) hK
  generalize hxd : Y ^ K = x at hxY ⊢
  have hx0 : 0 < x := by linarith
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  have hQ0 : 0 < Q := by linarith
  have hc1 : 1 ≤ Y ^ (ε / 6) := Real.one_le_rpow (by linarith) (by positivity)
  have hQ2 : 2 ≤ Q := by
    have e1 : Real.exp 1 ≤ Q := (Real.le_log_iff_exp_le hQ0).1 (hc1.trans hl1)
    have e2 := Real.add_one_le_exp (1:ℝ)
    linarith
  have hz1 : (1:ℝ) ≤ x ^ 400 := one_le_pow₀ (by linarith)
  have hη0 : (0:ℝ) < 1 / x ^ 2 := by positivity
  have hη1 : 1 / x ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith
  have hh0 : (0:ℝ) < x ^ 400 * (1 / x ^ 2) := by positivity
  have hc := hA N χ Q (x ^ 400) (1 / x ^ 2) hχ1 hQ2 hNQ hZ hz1 hη0 hη1
  have hd := Formalism.HermitianLattices.Ext.BoxTail.tail_diff_schi χ (x ^ 400) (x ^ 400 * (1 / x ^ 2)) hz1 hh0
  have key : ((x ^ 400 * (1 / x ^ 2) : ℝ) : ℂ) * tailL χ (x ^ 400) =
      (Formalism.ZeroFreeDirichlet.Schi χ (x ^ 400 + x ^ 400 * (1 / x ^ 2)) - Formalism.ZeroFreeDirichlet.Schi χ (x ^ 400) -
        ((x ^ 400 * (1 / x ^ 2) : ℝ) : ℂ) *
          ∑ n ∈ Icc 1 ⌊x ^ 400⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * χ n / n) -
      (Formalism.ZeroFreeDirichlet.Schi χ (x ^ 400 + x ^ 400 * (1 / x ^ 2)) - Formalism.ZeroFreeDirichlet.Schi χ (x ^ 400) -
        ((x ^ 400 * (1 / x ^ 2) : ℝ) : ℂ) * Formalism.ZeroFreeDirichlet.negLD χ 1) := by
    simp only [tailL, Formalism.ZeroFreeDirichlet.negLD, logDerivLAtOne]
    ring
  have hnorm := (norm_sub_le _ _).trans (add_le_add hd hc)
  rw [← key, norm_mul, Complex.norm_real, Real.norm_of_nonneg hh0.le] at hnorm
  have hfin := hY₀ Y x Q hY hxd.symm hQ0 hl1 hl2
  have ht : ‖tailL χ (x ^ 400)‖ ≤ (A * Real.log Q * (Real.log Q * (1 / x ^ 2) *
      (x ^ 400) ^ (1 - 1 / 400 + ε / K / 1600) + (x ^ 400) ^ 2 / Q) +
      x ^ 400 * (1 / x ^ 2) * (x ^ 400 * (1 / x ^ 2) + 1) *
      Real.log (x ^ 400 + x ^ 400 * (1 / x ^ 2)) / x ^ 400) / (x ^ 400 * (1 / x ^ 2)) := by
    rw [le_div_iff₀ hh0]
    linarith
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hx0.le]
  exact (mul_le_mul_of_nonneg_left ht hx0.le).trans hfin

end QH
end

section -- merged from Development.AutomorphicArithmetic.MeanSquareBounds.BoxOfS
section -- merged from Development.AutomorphicArithmetic.MeanSquareBounds.kappaC
open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace QH

theorem kappaC :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ Y₀ : ℝ, ∀ Y ≥ Y₀, ∀ (Q : ℝ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
      Y ^ (ε / 6) ≤ Real.log Q → Real.log Q ≤ Y ^ (ε / 4) → GoodC Q χ → ‖logDerivLAtOne χ‖ ≤ C * Real.log Y := by
  obtain ⟨C0, hC0, hM⟩ := Formalism.HermitianLattices.Ext.BoxTail.tail_mertens
  refine ⟨400 * C0 + 1, by positivity, ?_⟩
  intro ε hε hε1
  obtain ⟨Y1, hY1⟩ := tailK ε 1 hε hε1 le_rfl
  refine ⟨max Y1 3, ?_⟩
  intro Y hY Q N _ χ hQ1 hQ2 hG
  have hYY1 : Y ≥ Y1 := le_trans (le_max_left _ _) hY
  have hY3 : (3 : ℝ) ≤ Y := le_trans (le_max_right _ _) hY
  have hY0 : (0 : ℝ) < Y := by linarith
  have hT := hY1 Y hYY1 Q N χ hQ1 hQ2 hG
  have e1 : (Y ^ (1 : ℝ)) ^ 400 = Y ^ (400 : ℕ) := by simp
  rw [e1, Real.rpow_one] at hT
  set z : ℝ := Y ^ (400 : ℕ) with hz
  have hlogY : 1 ≤ Real.log Y := by
    rw [Real.le_log_iff_exp_le hY0]
    have := Real.exp_one_lt_d9
    linarith
  have hz2 : (2 : ℝ) ≤ z := by
    have : Y ≤ Y ^ (400 : ℕ) := le_self_pow₀ (by linarith) (by norm_num)
    linarith
  have htail : ‖tailL χ z‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hY0] at hT
    have hYe : Y ^ ε ≤ Y := by
      have := Real.rpow_le_rpow_of_exponent_le (x := Y) (by linarith) hε1
      simpa using this
    have : Y * ‖tailL χ z‖ ≤ Y * 1 := by linarith
    exact le_of_mul_le_mul_left this hY0
  have hsum : ‖∑ n ∈ Icc 1 ⌊z⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * χ n / n‖ ≤ 400 * C0 * Real.log Y := by
    calc ‖∑ n ∈ Icc 1 ⌊z⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * χ n / n‖
        ≤ ∑ n ∈ Icc 1 ⌊z⌋₊, ‖(ArithmeticFunction.vonMangoldt n : ℂ) * χ n / n‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Icc 1 ⌊z⌋₊, ArithmeticFunction.vonMangoldt n / n := by
        apply Finset.sum_le_sum
        intro n hn
        rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, Complex.norm_natCast]
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
        have := DirichletCharacter.norm_le_one χ (n : ZMod N)
        have h0 := (ArithmeticFunction.vonMangoldt_nonneg (n := n))
        nlinarith
      _ ≤ C0 * Real.log z := hM z hz2
      _ = 400 * C0 * Real.log Y := by rw [hz, Real.log_pow]; push_cast; ring
  have hL : logDerivLAtOne χ = -tailL χ z - ∑ n ∈ Icc 1 ⌊z⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * χ n / n := by
    unfold tailL
    ring
  rw [hL]
  calc ‖-tailL χ z - ∑ n ∈ Icc 1 ⌊z⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * χ n / n‖
      ≤ ‖tailL χ z‖ + ‖∑ n ∈ Icc 1 ⌊z⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * χ n / n‖ := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_neg]
    _ ≤ 1 + 400 * C0 * Real.log Y := add_le_add htail hsum
    _ ≤ (400 * C0 + 1) * Real.log Y := by nlinarith

end QH
end

open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace QH

private lemma num_box {ε τ Y y : ℝ} (hε : ε ≤ 1 / 4) (hτ : 0 < τ) (hY : 16 ≤ Y) (hy : Y ≤ y) :
    Y ^ ε ≤ y ^ (1 / 2 + τ) / 2 := by
  have hY1 : (1 : ℝ) ≤ Y := by linarith
  have hY0 : (0 : ℝ) < Y := by linarith
  have h1 : Y ^ ε ≤ Y ^ (1 / 4 : ℝ) := Real.rpow_le_rpow_of_exponent_le hY1 hε
  have h2 : (2 : ℝ) ≤ Y ^ (1 / 4 : ℝ) := by
    have h16 : (16 : ℝ) ^ (1 / 4 : ℝ) = 2 := by
      rw [show (16 : ℝ) = 2 ^ (4 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [← h16]
    exact Real.rpow_le_rpow (by norm_num) hY (by norm_num)
  have h3 : Y ^ (1 / 2 : ℝ) = Y ^ (1 / 4 : ℝ) * Y ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_add hY0]; norm_num
  have h4 : Y ^ (1 / 2 : ℝ) ≤ y ^ (1 / 2 : ℝ) := Real.rpow_le_rpow hY0.le hy (by norm_num)
  have h5 : y ^ (1 / 2 : ℝ) ≤ y ^ (1 / 2 + τ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  nlinarith

theorem box_of_S :
    ∃ C : ℝ, 0 < C ∧ ∀ ε τ K : ℝ, 0 < ε → ε ≤ 1 / 4 → 0 < τ → 1 ≤ K → ∃ Y₀ : ℝ, ∀ Y ≥ Y₀, ∀ (Q : ℝ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (q : ℕ) (κ : ℕ → ℂ),
      Y ^ (ε / 6) ≤ Real.log Q → Real.log Q ≤ Y ^ (ε / 4) → GoodC Q χ → (∀ n : ℕ, χ (n : ZMod N) = κ n * J q n) →
      (∀ y ∈ Set.Icc Y (Y ^ K), ‖S ((Y ^ K) ^ 400) y q κ‖ ≤ y ^ (1 / 2 + τ) / 2) → Box Q C τ Y (Y ^ K) χ := by
  obtain ⟨C, hC, hk⟩ := kappaC
  refine ⟨C, hC, fun ε τ K hε hε4 hτ hK => ?_⟩
  obtain ⟨Y₁, h1⟩ := hk ε hε (by linarith)
  obtain ⟨Y₂, h2⟩ := tailK ε K hε (by linarith) hK
  refine ⟨max (max Y₁ Y₂) 16, fun Y hY Q N _ χ q κ hlo hhi hg hχ hS => ?_⟩
  have hY1 : Y₁ ≤ Y := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hY
  have hY2 : Y₂ ≤ Y := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hY
  have hY16 : 16 ≤ Y := le_trans (le_max_right _ _) hY
  refine ⟨hg, h1 Y hY1 Q N χ hlo hhi hg, fun y hy => ?_⟩
  have ht := h2 Y hY2 Q N χ hlo hhi hg
  have hy0 : 0 < y := by linarith [hy.1]
  have hX1 : 1 ≤ Y ^ K := by linarith [hy.1, hy.2]
  have hyz : y ≤ (Y ^ K) ^ 400 := le_trans hy.2 (le_self_pow₀ hX1 (by norm_num))
  rw [finite_splitting_of_group N χ y ((Y ^ K) ^ 400) hy0 hyz]
  have hSz : Sz χ y ((Y ^ K) ^ 400) = S ((Y ^ K) ^ 400) y q κ := by
    unfold Sz S
    apply Finset.sum_congr rfl
    intro n _
    rw [hχ n, J, mul_assoc]
  have htail : ‖(y : ℂ) * tailL χ ((Y ^ K) ^ 400)‖ ≤ Y ^ ε := by
    refine le_trans ?_ ht
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hy0.le,
      Real.norm_of_nonneg (by linarith)]
    exact mul_le_mul_of_nonneg_right hy.2 (norm_nonneg _)
  have hn := num_box hε4 hτ hY16 hy.1
  have hs := hS y hy
  calc ‖- Sz χ y ((Y ^ K) ^ 400) - (y : ℂ) * tailL χ ((Y ^ K) ^ 400)‖
      ≤ ‖- Sz χ y ((Y ^ K) ^ 400)‖ + ‖(y : ℂ) * tailL χ ((Y ^ K) ^ 400)‖ := norm_sub_le _ _
    _ ≤ y ^ (1 / 2 + τ) := by rw [norm_neg, hSz]; linarith

end QH
end

section -- merged from Development.AutomorphicArithmetic.MeanSquareBounds.CountBad
section -- merged from Development.AutomorphicArithmetic.MeanSquareBounds.CountBadCore
open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace QH

private theorem aux (Q : ℝ) (M : ℕ) [NeZero M] (ψ : DirichletCharacter ℂ M) (hp : ψ.IsPrimitive) (hM : (M : ℝ) ≤ Q)
    (hz : ¬ ZeroFreeBox Q ψ) :
    ∃ p : (Σ N : ℕ, DirichletCharacter ℂ (N + 1)), p.1 + 1 = M ∧ p.2.IsPrimitive ∧ ((p.1 + 1 : ℕ) : ℝ) ≤ Q ∧
      ∃ s : ℂ, 1 - 1 / 400 < s.re ∧ |s.im| ≤ Q ∧ DirichletCharacter.LFunction p.2 s = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, M = k + 1 := Nat.exists_eq_succ_of_ne_zero (NeZero.ne M)
  refine ⟨⟨k, ψ⟩, rfl, hp, hM, ?_⟩
  unfold ZeroFreeBox at hz
  push Not at hz
  exact hz

theorem count_bad_core :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Q F : ℝ) (S : Finset ℕ), 3 ≤ Q →
      (∀ q ∈ S, q.Prime ∧ F < q ∧ ∃ (N f : ℕ) (_ : NeZero N) (ψ : DirichletCharacter ℂ N),
        N = f * q ∧ (f : ℝ) ≤ F ∧ ψ.IsPrimitive ∧ (N : ℝ) ≤ Q ∧ ¬ ZeroFreeBox Q ψ) →
      (S.card : ℝ) ≤ C * Q ^ (1 / 4 : ℝ) := by
  classical
  obtain ⟨C, hC⟩ := Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD.zero_density_box
  refine ⟨max C 0, le_max_right _ _, fun Q F S hQ hS => ?_⟩
  have key : ∀ q : ℕ, ∃ p : (Σ N : ℕ, DirichletCharacter ℂ (N + 1)), q ∈ S →
      (∃ f : ℕ, p.1 + 1 = f * q ∧ (f : ℝ) ≤ F) ∧ p.2.IsPrimitive ∧ ((p.1 + 1 : ℕ) : ℝ) ≤ Q ∧
      ∃ s : ℂ, 1 - 1 / 400 < s.re ∧ |s.im| ≤ Q ∧ DirichletCharacter.LFunction p.2 s = 0 := by
    intro q
    by_cases hq : q ∈ S
    · obtain ⟨-, -, N, f, _, ψ, hN, hf, hp, hNQ, hz⟩ := hS q hq
      obtain ⟨p, h1, h2⟩ := aux Q N ψ hp hNQ hz
      exact ⟨p, fun _ => ⟨⟨f, h1.trans hN, hf⟩, h2⟩⟩
    · exact ⟨⟨0, 1⟩, fun h => absurd h hq⟩
  choose g hg using key
  have hinj : Set.InjOn g S := by
    intro q hq q' hq' h
    obtain ⟨⟨f, hf, -⟩, -⟩ := hg q hq
    obtain ⟨⟨f', hf', hF'⟩, -⟩ := hg q' hq'
    have hpq := (hS q hq).1
    have hpq' := (hS q' hq').1
    have hlt := (hS q hq).2.1
    have he : f * q = f' * q' := by rw [← hf, ← hf', h]
    have hd : q ∣ f' * q' := ⟨f, by rw [← he, mul_comm]⟩
    rcases (Nat.Prime.dvd_mul hpq).1 hd with h1 | h1
    · have hpos : 0 < f' := by
        rcases Nat.eq_zero_or_pos f' with h0 | h0
        · rw [h0] at hf'; simp at hf'
        · exact h0
      have : (q : ℝ) ≤ f' := by exact_mod_cast Nat.le_of_dvd hpos h1
      linarith
    · exact (Nat.prime_dvd_prime_iff_eq hpq hpq').1 h1
  have h1 := hC Q (S.image g) hQ (by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hp
    exact (hg q hq).2)
  rw [Finset.card_image_of_injOn hinj] at h1
  refine h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ?_)
  exact Real.rpow_nonneg (by linarith) _

end QH
end

open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace QH

theorem count_bad :
    ∃ C : ℝ, ∀ (Q F : ℝ) (B : Finset ℕ), 3 ≤ Q →
      (∀ q ∈ B, q.Prime ∧ F < q ∧ ∃ (f : ℕ) (_ : NeZero (f * q)) (ψ : DirichletCharacter ℂ (f * q)),
        (f : ℝ) ≤ F ∧ ((f * q : ℕ) : ℝ) ≤ Q ∧ ψ.IsPrimitive ∧ ¬ ZeroFreeBox Q ψ) → (B.card : ℝ) ≤ C * Q ^ (1 / 4 : ℝ) := by
  obtain ⟨C, -, hC⟩ := count_bad_core
  refine ⟨C, fun Q F B hQ hB => hC Q F B hQ fun q hq => ?_⟩
  obtain ⟨hp, hF, f, hne, ψ, hf, hN, hψ, hz⟩ := hB q hq
  exact ⟨hp, hF, f * q, f, hne, ψ, rfl, hf, hψ, hN, hz⟩

end QH
end

section -- merged from Development.AutomorphicArithmetic.MeanSquareBounds.BadShare
open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
open scoped ArithmeticFunction.vonMangoldt
open Filter MeasureTheory

namespace QH

private noncomputable def bsD (Z v : ℝ) (q : ℕ) (κ : ℕ → ℂ) : ℂ :=
  ∑ m ∈ Icc 1 ⌊Z⌋₊,
    if v < (m : ℝ) then ((Λ m : ℝ) : ℂ) * κ m * ((jacobiSym (m : ℤ) q : ℤ) : ℂ) / m else 0

private theorem bs_continuous_S (Z : ℝ) (q : ℕ) (κ : ℕ → ℂ) : Continuous (fun y => S Z y q κ) := by
  unfold S cN
  refine continuous_finsetSum _ (fun m _ => ?_)
  fun_prop

private theorem bs_measurable_D (Z : ℝ) (q : ℕ) (κ : ℕ → ℂ) :
    Measurable (fun v => bsD Z v q κ) := by
  unfold bsD
  refine Finset.measurable_sum _ (fun m _ => ?_)
  exact Measurable.ite measurableSet_Iio measurable_const measurable_const

private theorem bs_norm_D_le (Z v : ℝ) (q : ℕ) (κ : ℕ → ℂ) :
    ‖bsD Z v q κ‖ ≤
      ∑ m ∈ Icc 1 ⌊Z⌋₊, ‖((Λ m : ℝ) : ℂ) * κ m * ((jacobiSym (m : ℤ) q : ℤ) : ℂ) / m‖ := by
  unfold bsD
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun m _ => ?_))
  split_ifs
  · exact le_rfl
  · simp only [norm_zero]; exact norm_nonneg _

private theorem bs_intervalIntegrable_D (Z : ℝ) (q : ℕ) (κ : ℕ → ℂ) (a b : ℝ) :
    IntervalIntegrable (fun v => bsD Z v q κ) volume a b ∧
      IntervalIntegrable (fun v => ‖bsD Z v q κ‖ ^ 2) volume a b := by
  set C := ∑ m ∈ Icc 1 ⌊Z⌋₊, ‖((Λ m : ℝ) : ℂ) * κ m * ((jacobiSym (m : ℤ) q : ℤ) : ℂ) / m‖ with hC
  constructor
  · refine IntervalIntegrable.mono_fun' (g := fun _ => C) intervalIntegrable_const
      (bs_measurable_D Z q κ).aestronglyMeasurable ?_
    exact Eventually.of_forall (fun v => bs_norm_D_le Z v q κ)
  · refine IntervalIntegrable.mono_fun' (g := fun _ => C ^ 2) intervalIntegrable_const
      ((bs_measurable_D Z q κ).norm.pow_const 2).aestronglyMeasurable ?_
    refine Eventually.of_forall (fun v => ?_)
    have := bs_norm_D_le Z v q κ
    simp only [norm_pow, norm_norm]
    exact pow_le_pow_left₀ (norm_nonneg _) this 2

private theorem bs_hasDeriv_min (m x : ℝ) (hm : 0 < m) :
    HasDerivWithinAt (fun y : ℝ => min 1 (y / m)) (if x < m then 1 / m else 0) (Set.Ioi x) x := by
  split_ifs with h
  · have h1 : HasDerivAt (fun y : ℝ => y / m) (1 / m) x := (hasDerivAt_id x).div_const m
    refine (h1.congr_of_eventuallyEq ?_).hasDerivWithinAt
    filter_upwards [Iio_mem_nhds h] with y hy
    exact min_eq_right ((div_le_one hm).2 (le_of_lt hy))
  · push Not at h
    have h1 : HasDerivWithinAt (fun _ : ℝ => (1 : ℝ)) 0 (Set.Ioi x) x :=
      (hasDerivAt_const x 1).hasDerivWithinAt
    refine h1.congr (fun y hy => ?_) ?_
    · exact min_eq_left ((one_le_div hm).2 (h.trans (le_of_lt hy)))
    · exact min_eq_left ((one_le_div hm).2 h)

private theorem bs_hasDeriv_S (Z : ℝ) (q : ℕ) (κ : ℕ → ℂ) (x : ℝ) :
    HasDerivWithinAt (fun y => S Z y q κ) (bsD Z x q κ) (Set.Ioi x) x := by
  unfold bsD S cN
  refine HasDerivWithinAt.fun_sum (fun m hm => ?_)
  have hm0 : (0 : ℝ) < m := by
    have := (Finset.mem_Icc.1 hm).1
    exact_mod_cast this
  have h1 := (((bs_hasDeriv_min m x hm0).const_mul (Λ m)).ofReal_comp.mul_const (κ m)).mul_const
    ((jacobiSym (m : ℤ) q : ℤ) : ℂ)
  refine HasDerivWithinAt.congr_deriv h1 ?_
  split_ifs
  · push_cast; ring
  · simp

private theorem bs_S_sub_S (Z : ℝ) (q : ℕ) (κ : ℕ → ℂ) (a b : ℝ) :
    S Z b q κ - S Z a q κ = ∫ v in a..b, bsD Z v q κ := by
  symm
  exact intervalIntegral.integral_eq_sub_of_hasDeriv_right (f := fun y => S Z y q κ)
    (bs_continuous_S Z q κ).continuousOn (fun x _ => bs_hasDeriv_S Z q κ x)
    (bs_intervalIntegrable_D Z q κ a b).1

private theorem bs_mul_D_eq_S (Z : ℝ) (y : ℝ) (q : ℕ) (κ : ℕ → ℂ) :
    (y : ℂ) * bsD Z y q κ = S Z y q (fun m => if y < (m : ℝ) then κ m else 0) := by
  unfold bsD S cN
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm0 : (0 : ℝ) < m := by
    have := (Finset.mem_Icc.1 hm).1
    exact_mod_cast this
  by_cases h : y < (m : ℝ)
  · simp only [h, if_true]
    rw [min_eq_right ((div_le_one hm0).2 h.le)]
    push_cast
    ring
  · simp [h]

private theorem bs_sq_integral_le {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (h1 : IntervalIntegrable f volume a b)
    (h2 : IntervalIntegrable (fun v => f v ^ 2) volume a b) :
    (∫ v in a..b, f v) ^ 2 ≤ (b - a) * ∫ v in a..b, f v ^ 2 := by
  rcases hab.eq_or_lt with h | h
  · subst h; simp
  set I := ∫ v in a..b, f v with hI
  set A := ∫ v in a..b, f v ^ 2 with hA
  have hL : 0 < b - a := sub_pos.2 h
  have h0 : 0 ≤ ∫ v in a..b, (((b - a) ^ 2 * f v ^ 2 - (2 * (b - a) * I) * f v) + I ^ 2) :=
    intervalIntegral.integral_nonneg_of_forall hab (fun v => by
      nlinarith [sq_nonneg ((b - a) * f v - I)])
  rw [intervalIntegral.integral_add ((h2.const_mul _).sub (h1.const_mul _))
      intervalIntegrable_const,
    intervalIntegral.integral_sub (h2.const_mul _) (h1.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const, ← hI, ← hA, smul_eq_mul] at h0
  have h3 : (b - a) * I ^ 2 ≤ (b - a) * ((b - a) * A) := by nlinarith
  exact le_of_mul_le_mul_left h3 hL

private theorem bs_normSq_S_le (Z : ℝ) (q : ℕ) (κ : ℕ → ℂ) {Y W y : ℝ} (hW : W ≤ 2 * Y)
    (hY : 0 ≤ Y) (hy : y ∈ Set.Icc Y W) :
    ‖S Z y q κ‖ ^ 2 ≤ 2 * ‖S Z Y q κ‖ ^ 2 + 2 * Y * ∫ v in Y..W, ‖bsD Z v q κ‖ ^ 2 := by
  obtain ⟨h1, h2⟩ := hy
  have hS : S Z y q κ = S Z Y q κ + ∫ v in Y..y, bsD Z v q κ := by
    rw [← bs_S_sub_S]; ring
  have hn : ‖∫ v in Y..y, bsD Z v q κ‖ ≤ ∫ v in Y..y, ‖bsD Z v q κ‖ :=
    intervalIntegral.norm_integral_le_integral_norm h1
  have hcs := bs_sq_integral_le (f := fun v => ‖bsD Z v q κ‖) h1
    (bs_intervalIntegrable_D Z q κ Y y).1.norm (bs_intervalIntegrable_D Z q κ Y y).2
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (bs_intervalIntegrable_D Z q κ Y y).2 (bs_intervalIntegrable_D Z q κ y W).2
  have hA : 0 ≤ ∫ v in Y..y, ‖bsD Z v q κ‖ ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall h1 (fun v => sq_nonneg _)
  have hB : 0 ≤ ∫ v in y..W, ‖bsD Z v q κ‖ ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall h2 (fun v => sq_nonneg _)
  have htri : ‖S Z y q κ‖ ≤ ‖S Z Y q κ‖ + ∫ v in Y..y, ‖bsD Z v q κ‖ := by
    rw [hS]; exact (norm_add_le _ _).trans (by linarith)
  rw [← hadd]
  set I := ∫ v in Y..y, ‖bsD Z v q κ‖
  set A := ∫ v in Y..y, ‖bsD Z v q κ‖ ^ 2
  set B := ∫ v in y..W, ‖bsD Z v q κ‖ ^ 2
  have h3 : ‖S Z y q κ‖ ^ 2 ≤ (‖S Z Y q κ‖ + I) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) htri 2
  have h4 : (y - Y) * A ≤ Y * A := mul_le_mul_of_nonneg_right (by linarith) hA
  have h5 : 0 ≤ Y * B := mul_nonneg hY hB
  nlinarith [sq_nonneg (‖S Z Y q κ‖ - I)]

private theorem bs_sum_D_le {C Z : ℝ} {P : Finset ℕ} {A : Set ℝ} (h : MeanSq C Z P A) {y : ℝ}
    (hy : y ∈ A) (hy0 : 0 < y) {κ : ℕ → ℂ} (hκ : ∀ m, ‖κ m‖ ≤ 1) :
    ∑ q ∈ P, ‖bsD Z y q κ‖ ^ 2 ≤ C * Real.log y * P.card / y := by
  have h1 := h y hy (fun m => if y < (m : ℝ) then κ m else 0) (fun m => by
    by_cases hm : y < (m : ℝ)
    · simpa [hm] using hκ m
    · simp [hm])
  have h2 : ∀ q, ‖S Z y q (fun m => if y < (m : ℝ) then κ m else 0)‖ ^ 2
      = y ^ 2 * ‖bsD Z y q κ‖ ^ 2 := by
    intro q
    rw [← bs_mul_D_eq_S Z y q κ, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp only [h2] at h1
  rw [← Finset.mul_sum] at h1
  rw [le_div_iff₀ hy0]
  refine le_of_mul_le_mul_left ?_ hy0
  nlinarith [h1]

private theorem bs_block {C Z Y W : ℝ} {P : Finset ℕ} (hC : 0 ≤ C) (hY : 1 ≤ Y) (hYW : Y ≤ W)
    (hW2 : W ≤ 2 * Y) (h : MeanSq C Z P (Set.Icc Y W)) {κ : ℕ → ℂ} (hκ : ∀ m, ‖κ m‖ ≤ 1)
    (w : ℕ → ℝ) (hw : ∀ q, w q ∈ Set.Icc Y W) :
    ∑ q ∈ P, ‖S Z (w q) q κ‖ ^ 2 ≤ 4 * C * Y * Real.log (2 * Y) * P.card := by
  have hY0 : 0 < Y := by linarith
  have hP : (0 : ℝ) ≤ P.card := Nat.cast_nonneg _
  have h1 : ∑ q ∈ P, ‖S Z (w q) q κ‖ ^ 2 ≤
      ∑ q ∈ P, (2 * ‖S Z Y q κ‖ ^ 2 + (2 * Y) * ∫ v in Y..W, ‖bsD Z v q κ‖ ^ 2) :=
    Finset.sum_le_sum fun q _ => bs_normSq_S_le Z q κ hW2 hY0.le (hw q)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at h1
  have h2 := h Y ⟨le_rfl, hYW⟩ κ hκ
  have hL : 0 ≤ Real.log (2 * Y) := Real.log_nonneg (by linarith)
  have hLY : Real.log Y ≤ Real.log (2 * Y) := Real.log_le_log hY0 (by linarith)
  have hint : IntervalIntegrable (fun v => ∑ q ∈ P, ‖bsD Z v q κ‖ ^ 2) volume Y W := by
    have := IntervalIntegrable.sum (μ := volume) (a := Y) (b := W) P
      (f := fun q v => ‖bsD Z v q κ‖ ^ 2) (fun q _ => (bs_intervalIntegrable_D Z q κ Y W).2)
    have e : (fun v => ∑ q ∈ P, ‖bsD Z v q κ‖ ^ 2) = ∑ q ∈ P, fun v => ‖bsD Z v q κ‖ ^ 2 := by
      funext v
      simp [Finset.sum_apply]
    rw [e]
    exact this
  rw [← intervalIntegral.integral_finsetSum
    (fun q _ => (bs_intervalIntegrable_D Z q κ Y W).2)] at h1
  set K := C * Real.log (2 * Y) * P.card with hK
  have hK0 : 0 ≤ K := by positivity
  have h4 : (∫ v in Y..W, ∑ q ∈ P, ‖bsD Z v q κ‖ ^ 2) ≤ ∫ _ in Y..W, K / Y := by
    refine intervalIntegral.integral_mono_on hYW hint intervalIntegrable_const ?_
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hY0 hx.1
    refine (bs_sum_D_le h hx hx0 hκ).trans ?_
    have : Real.log x ≤ Real.log (2 * Y) := Real.log_le_log hx0 (hx.2.trans hW2)
    refine div_le_div₀ hK0 ?_ hY0 hx.1
    rw [hK]
    gcongr
  rw [intervalIntegral.integral_const, smul_eq_mul] at h4
  have h5 : (W - Y) * (K / Y) ≤ K := by
    calc (W - Y) * (K / Y) ≤ Y * (K / Y) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = K := by field_simp
  have h7 := mul_le_mul_of_nonneg_left (h4.trans h5) (show 0 ≤ 2 * Y by positivity)
  have h8 : C * Y * Real.log Y * P.card ≤ C * Y * Real.log (2 * Y) * P.card := by gcongr
  have h9 : 2 * Y * K = 2 * (C * Y * Real.log (2 * Y) * P.card) := by rw [hK]; ring
  linarith

private theorem bs_markov {C τ Z Y W : ℝ} {P B : Finset ℕ} (hC : 0 ≤ C) (hτ : 0 < τ) (hY : 2 ≤ Y)
    (hYW : Y ≤ W) (hW2 : W ≤ 2 * Y) (h : MeanSq C Z P (Set.Icc Y W)) {κ : ℕ → ℂ}
    (hκ : ∀ m, ‖κ m‖ ≤ 1) (hBP : B ⊆ P)
    (hB : ∀ q ∈ B, ∃ y ∈ Set.Icc Y W, y ^ (1 / 2 + τ) / 2 < ‖S Z y q κ‖) :
    (B.card : ℝ) ≤ 32 * C / τ * Y ^ (-τ) * P.card := by
  have hY0 : 0 < Y := by linarith
  have hP : (0 : ℝ) ≤ P.card := Nat.cast_nonneg _
  have hex : ∀ q, ∃ y ∈ Set.Icc Y W, q ∈ B → y ^ (1 / 2 + τ) / 2 < ‖S Z y q κ‖ := by
    intro q
    by_cases hq : q ∈ B
    · obtain ⟨y, hy, hy'⟩ := hB q hq
      exact ⟨y, hy, fun _ => hy'⟩
    · exact ⟨Y, ⟨le_rfl, hYW⟩, fun h => absurd h hq⟩
  choose w hw hw' using hex
  have h1 := bs_block hC (by linarith) hYW hW2 h hκ w hw
  have h2 : ∑ q ∈ B, ‖S Z (w q) q κ‖ ^ 2 ≤ ∑ q ∈ P, ‖S Z (w q) q κ‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hBP (fun q _ _ => sq_nonneg _)
  have ht : 0 < Y ^ τ := Real.rpow_pos_of_pos hY0 τ
  have e : (Y ^ (1 / 2 + τ) / 2) ^ 2 = Y * Y ^ τ * Y ^ τ / 4 := by
    rw [div_pow, sq (Y ^ _), ← Real.rpow_add hY0,
      show 1 / 2 + τ + (1 / 2 + τ) = 1 + τ + τ by ring, Real.rpow_add hY0, Real.rpow_add hY0,
      Real.rpow_one]
    norm_num
  have h3 : (B.card : ℝ) * (Y * Y ^ τ * Y ^ τ / 4) ≤ ∑ q ∈ B, ‖S Z (w q) q κ‖ ^ 2 := by
    rw [← nsmul_eq_mul]
    refine Finset.card_nsmul_le_sum _ _ _ (fun q hq => ?_)
    rw [← e]
    refine pow_le_pow_left₀ (by positivity) (le_trans ?_ (hw' q hq).le) 2
    have : Y ^ (1 / 2 + τ) ≤ w q ^ (1 / 2 + τ) :=
      Real.rpow_le_rpow hY0.le (hw q).1 (by linarith)
    linarith
  have h4 : Real.log (2 * Y) ≤ 2 * (Y ^ τ / τ) := by
    have a1 := Real.log_le_rpow_div hY0.le hτ
    have a2 : Real.log 2 ≤ Real.log Y := Real.log_le_log (by norm_num) hY
    rw [Real.log_mul (by norm_num) hY0.ne']
    linarith
  have h5 : 4 * C * Y * Real.log (2 * Y) * P.card ≤ 4 * C * Y * (2 * (Y ^ τ / τ)) * P.card := by
    gcongr
  have hpos : 0 < Y * Y ^ τ * Y ^ τ / 4 := by positivity
  refine le_of_mul_le_mul_right (h3.trans (h2.trans (h1.trans (h5.trans (le_of_eq ?_))))) hpos
  rw [Real.rpow_neg hY0.le]
  field_simp
  ring

theorem bad_share :
    ∀ C τ η : ℝ, 0 ≤ C → 0 < τ → 0 < η → ∃ Y₀ : ℝ, ∀ Y ≥ Y₀, ∀ (X Z : ℝ) (P B : Finset ℕ) (κ : ℕ → ℂ),
      (∀ n, ‖κ n‖ ≤ 1) → MeanSq C Z P (Set.Icc Y X) → B ⊆ P →
      (∀ q ∈ B, ∃ y ∈ Set.Icc Y X, y ^ (1 / 2 + τ) / 2 < ‖S Z y q κ‖) → (B.card : ℝ) ≤ η * P.card := by
  classical
  intro C τ η hC hτ hη
  set r : ℝ := (2 : ℝ) ^ (-τ) with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hlim : Tendsto (fun Y : ℝ => 32 * C / τ * Y ^ (-τ) * (1 - r)⁻¹) atTop (nhds 0) := by
    have := ((tendsto_rpow_neg_atTop hτ).const_mul (32 * C / τ)).mul_const (1 - r)⁻¹
    simpa using this
  obtain ⟨Y₀, hY₀⟩ := Filter.eventually_atTop.1
    ((hlim.eventually (ge_mem_nhds hη)).and (eventually_ge_atTop (2 : ℝ)))
  refine ⟨Y₀, fun Y hY X Z P B κ hκ hM hBP hB => ?_⟩
  obtain ⟨hη', hY2⟩ := hY₀ Y hY
  have hY0 : 0 < Y := by linarith
  have hP : (0 : ℝ) ≤ P.card := Nat.cast_nonneg _
  have hidx : ∀ q, ∃ i : ℕ, q ∈ B → 2 ^ i * Y ≤ X ∧
      ∃ y ∈ Set.Icc (2 ^ i * Y) (min (2 * (2 ^ i * Y)) X), y ^ (1 / 2 + τ) / 2 < ‖S Z y q κ‖ := by
    intro q
    by_cases hq : q ∈ B
    · obtain ⟨y, ⟨h1, h2⟩, hy'⟩ := hB q hq
      have h3 : 1 ≤ y / Y := by rw [le_div_iff₀ hY0]; linarith
      obtain ⟨i, hi1, hi2⟩ := exists_nat_pow_near h3 (by norm_num : (1 : ℝ) < 2)
      rw [le_div_iff₀ hY0] at hi1
      rw [div_lt_iff₀ hY0, pow_succ] at hi2
      refine ⟨i, fun _ => ⟨hi1.trans h2, y, ⟨hi1, le_min ?_ h2⟩, hy'⟩⟩
      nlinarith
    · exact ⟨0, fun h => absurd h hq⟩
  choose f hf using hidx
  have hcard : (B.card : ℝ) = ∑ i ∈ B.image f, ((B.filter (fun q => f q = i)).card : ℝ) := by
    rw [Finset.card_eq_sum_card_image f B]
    push_cast
    rfl
  have hblock : ∀ i ∈ B.image f, ((B.filter (fun q => f q = i)).card : ℝ) ≤
      32 * C / τ * Y ^ (-τ) * P.card * r ^ i := by
    intro i hi
    obtain ⟨q₀, hq₀, rfl⟩ := Finset.mem_image.1 hi
    have hX := (hf q₀ hq₀).1
    have h1 : (1 : ℝ) ≤ 2 ^ f q₀ := one_le_pow₀ (by norm_num)
    have hYY : Y ≤ 2 ^ f q₀ * Y := by nlinarith
    have := bs_markov (Y := 2 ^ f q₀ * Y) (W := min (2 * (2 ^ f q₀ * Y)) X) (P := P) (Z := Z)
      (B := B.filter (fun q => f q = f q₀)) hC hτ (by linarith) (le_min (by linarith) hX)
      (min_le_left _ _)
      (fun y hy => hM y ⟨hYY.trans hy.1, hy.2.trans (min_le_right _ _)⟩) hκ
      ((Finset.filter_subset _ _).trans hBP)
      (fun q hq => by
        obtain ⟨hq1, hq2⟩ := Finset.mem_filter.1 hq
        rw [← hq2]
        exact (hf q hq1).2)
    refine this.trans (le_of_eq ?_)
    have e : ((2 : ℝ) ^ f q₀ * Y) ^ (-τ) = Y ^ (-τ) * r ^ f q₀ := by
      rw [hr, Real.mul_rpow (by positivity) hY0.le, mul_comm, ← Real.rpow_natCast,
        ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num),
        mul_comm (f q₀ : ℝ)]
    rw [e]
    ring
  have hg : ∑ i ∈ B.image f, r ^ i ≤ (1 - r)⁻¹ := by
    rw [← tsum_geometric_of_lt_one hr0 hr1]
    exact (summable_geometric_of_lt_one hr0 hr1).sum_le_tsum _ (fun i _ => by positivity)
  calc (B.card : ℝ) ≤ ∑ i ∈ B.image f, 32 * C / τ * Y ^ (-τ) * P.card * r ^ i := by
        rw [hcard]; exact Finset.sum_le_sum hblock
    _ = 32 * C / τ * Y ^ (-τ) * P.card * ∑ i ∈ B.image f, r ^ i := by rw [Finset.mul_sum]
    _ ≤ 32 * C / τ * Y ^ (-τ) * P.card * (1 - r)⁻¹ :=
        mul_le_mul_of_nonneg_left hg (by positivity)
    _ = 32 * C / τ * Y ^ (-τ) * (1 - r)⁻¹ * P.card := by ring
    _ ≤ η * P.card := mul_le_mul_of_nonneg_right hη' hP

end QH
end

open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace QH

private theorem stage_log {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ Y : ℝ in Filter.atTop, 3 / 2 * (Y ^ (ε / 5) * Real.log Y ^ 2) ≤ Y ^ (ε / 4) := by
  have h := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (show 0 < ε / 20 by positivity)).bound
    (show (0 : ℝ) < 2 / 3 by norm_num)
  filter_upwards [h, Filter.eventually_gt_atTop (0 : ℝ)] with Y hY hY0
  rw [Real.rpow_two, Real.norm_of_nonneg (sq_nonneg _),
    Real.norm_of_nonneg (Real.rpow_nonneg hY0.le _)] at hY
  have e : Y ^ (ε / 4) = Y ^ (ε / 5) * Y ^ (ε / 20) := by
    rw [← Real.rpow_add hY0]; congr 1; ring
  have h5 : 0 < Y ^ (ε / 5) := Real.rpow_pos_of_pos hY0 _
  rw [e]
  nlinarith

private theorem stage_pow (C : ℝ) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ U : ℝ in Filter.atTop, |C| * U ^ (3 / 8 : ℝ) ≤ η / 2 * U ^ (9 / 10 : ℝ) := by
  have h := (tendsto_rpow_atTop (show (0 : ℝ) < 21 / 40 by norm_num)).eventually_ge_atTop
    (2 * |C| / η)
  filter_upwards [h, Filter.eventually_gt_atTop (0 : ℝ)] with U hU hU0
  have e : U ^ (9 / 10 : ℝ) = U ^ (21 / 40 : ℝ) * U ^ (3 / 8 : ℝ) := by
    rw [← Real.rpow_add hU0]; norm_num
  have h5 : 0 < U ^ (3 / 8 : ℝ) := Real.rpow_pos_of_pos hU0 _
  rw [div_le_iff₀ hη] at hU
  rw [e]
  nlinarith

theorem stage :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε τ K η : ℝ) (R : ℕ), 0 < ε → ε ≤ 1 / 4 → 0 < τ → 1 ≤ K → 0 < η → ∃ Y₀ : ℝ, ∀ Y ≥ Y₀,
      ∀ (U F : ℝ) (m₀ a₀ : ℕ) (Ξ : Finset (Σ N : ℕ, DirichletCharacter ℂ (N + 1))), admitted ε Y U m₀ a₀ → (∀ p : ℕ, p.Prime → p ∣ m₀ → (p : ℝ) ≤ Y ^ (ε / 5) ∨ (Y ^ K) ^ 400 < (p : ℝ)) →
      1 ≤ F → F ≤ U ^ (1 / 2 : ℝ) → Ξ.card ≤ R → (∀ ξ ∈ Ξ, ξ.2.IsPrimitive ∧ ((ξ.1 + 1 : ℕ) : ℝ) ≤ F) →
      (PPset m₀ a₀ U).Nonempty ∧ ∀ B ⊆ PPset m₀ a₀ U,
        (∀ q ∈ B, ∃ ξ ∈ Ξ, ∃ M : ℕ, M ≠ 0 ∧ ¬ BoxAll (F * U) C τ Y (Y ^ K) (fun n => ξ.2 n * J q n) M) →
        (B.card : ℝ) ≤ η * (PPset m₀ a₀ U).card := by
  classical
  obtain ⟨C, hC, hbox⟩ := box_of_S
  obtain ⟨Cm, hCm, hms⟩ := meanSqK
  obtain ⟨Cb, hcb⟩ := count_bad
  refine ⟨C, hC, fun ε τ K η R hε hε4 hτ hK hη => ?_⟩
  obtain ⟨Y₁, hY₁⟩ := hbox ε τ K hε hε4 hτ hK
  obtain ⟨Y₂, hY₂⟩ := hms ε K hε (by linarith) hK
  obtain ⟨Y₃, hY₃⟩ := bad_share Cm τ (η / (2 * (R + 1))) hCm.le hτ (by positivity)
  obtain ⟨Y₄, hY₄⟩ := count_a Formalism.HermitianLattices.Ext.PrimesInProgressions.pnt_progressions_relative_weak_holds Formalism.ZeroFreeDirichlet.excBound ε hε
  obtain ⟨U₀, hU₀⟩ := Filter.eventually_atTop.1
    ((stage_pow Cb hη).and (Filter.eventually_ge_atTop (4 : ℝ)))
  obtain ⟨Y₅, hY₅⟩ := Filter.eventually_atTop.1 ((stage_log hε).and
    ((tendsto_rpow_atTop (show 0 < ε / 6 by positivity)).eventually_ge_atTop U₀))
  refine ⟨max (max (max Y₁ Y₂) (max Y₃ Y₄)) Y₅, ?_⟩
  intro Y hY U F m₀ a₀ Ξ hA hp hF1 hFU hR hΞ
  simp only [ge_iff_le, max_le_iff] at hY
  obtain ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5⟩ := hY
  obtain ⟨hlog, hU₀Y⟩ := hY₅ Y h5
  have hU0 : 0 < U := by
    by_contra hneg
    push Not at hneg
    rcases hneg.eq_or_lt with h | h
    · rw [h, Real.zero_rpow (by norm_num)] at hFU; linarith
    · rw [Real.rpow_def_of_neg h, show (1 / 2 : ℝ) * Real.pi = Real.pi / 2 by ring,
        Real.cos_pi_div_two, mul_zero] at hFU
      linarith
  obtain ⟨hpow, hU4⟩ := hU₀ U (by
    have := Real.log_le_sub_one_of_pos hU0
    have := hA.lo
    linarith)
  have hcount := hY₄ Y U m₀ a₀ h4 hA.pos hA.eight hA.coprime hA.log_m hA.lo hA.hi
  have hM := hY₂ Y h2 U m₀ a₀ hA hp
  have hsq2 : (2 : ℝ) ≤ U ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.le_sqrt_of_sq_le (by linarith)
  have hF0 : 0 < F := by linarith
  have hlogF0 : 0 ≤ Real.log F := Real.log_nonneg hF1
  have hlogF : Real.log F ≤ 1 / 2 * Real.log U := by
    rw [← Real.log_rpow hU0]; exact Real.log_le_log hF0 hFU
  have hlo : Y ^ (ε / 6) ≤ Real.log (F * U) := by
    rw [Real.log_mul hF0.ne' hU0.ne']; linarith [hA.lo]
  have hhi : Real.log (F * U) ≤ Y ^ (ε / 4) := by
    rw [Real.log_mul hF0.ne' hU0.ne']; linarith [hA.hi]
  refine ⟨?_, fun B hB hbad => ?_⟩
  · rw [← Finset.card_pos]
    have : (0 : ℝ) < (PPset m₀ a₀ U).card := lt_of_lt_of_le (Real.rpow_pos_of_pos hU0 _) hcount
    exact_mod_cast this
  have hPP : ∀ q ∈ B, q.Prime ∧ U ^ (1 / 2 : ℝ) < q ∧ (q : ℝ) ≤ U := by
    intro q hq
    have := Finset.mem_filter.1 (hB hq)
    refine ⟨this.2.1, this.2.2.2, ?_⟩
    exact (Nat.le_floor_iff hU0.le).1 (Finset.mem_Icc.1 this.1).2
  set B₁ := B.filter (fun q => ∃ (f : ℕ) (_ : NeZero (f * q)) (ψ : DirichletCharacter ℂ (f * q)),
    (f : ℝ) ≤ F ∧ ((f * q : ℕ) : ℝ) ≤ F * U ∧ ψ.IsPrimitive ∧ ¬ ZeroFreeBox (F * U) ψ) with hB₁
  set B₂ : (Σ N : ℕ, DirichletCharacter ℂ (N + 1)) → Finset ℕ := fun ξ => B.filter (fun q =>
    ∃ y ∈ Set.Icc Y (Y ^ K), y ^ (1 / 2 + τ) / 2 < ‖S ((Y ^ K) ^ 400) y q (fun n => ξ.2 n)‖) with hB₂
  have hsub : B ⊆ B₁ ∪ Ξ.biUnion B₂ := by
    intro q hq
    obtain ⟨ξ, hξ, M, hM0, hnb⟩ := hbad q hq
    obtain ⟨hqp, hq1, hq2⟩ := hPP q hq
    obtain ⟨hξp, hξF⟩ := hΞ ξ hξ
    have hq2' : q ≠ 2 := by
      rintro rfl
      push_cast at hq1
      linarith
    have hnd : ¬ q ∣ ξ.1 + 1 := by
      intro hd
      have : (q : ℝ) ≤ ((ξ.1 + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_of_dvd (Nat.succ_pos _) hd
      linarith
    obtain ⟨ψ, hψp, hψ1, hψ⟩ := twist_prim (ξ.1 + 1) q ξ.2 hξp hqp hq2' hnd
    haveI hne : NeZero ((ξ.1 + 1) * q) := ⟨mul_ne_zero (Nat.succ_ne_zero _) hqp.ne_zero⟩
    have hlev : (((ξ.1 + 1) * q : ℕ) : ℝ) ≤ F * U := by
      rw [Nat.cast_mul]
      exact mul_le_mul hξF hq2 (Nat.cast_nonneg _) hF0.le
    by_contra hcon
    rw [Finset.mem_union, not_or] at hcon
    obtain ⟨hc1, hc2⟩ := hcon
    have hz : ZeroFreeBox (F * U) ψ := by
      by_contra hz
      exact hc1 (Finset.mem_filter.2 ⟨hq, ξ.1 + 1, hne, ψ, hξF, hlev, hψp, hz⟩)
    have hS : ∀ y ∈ Set.Icc Y (Y ^ K),
        ‖S ((Y ^ K) ^ 400) y q (fun n => ξ.2 n)‖ ≤ y ^ (1 / 2 + τ) / 2 := by
      intro y hy
      by_contra hy'
      exact hc2 (Finset.mem_biUnion.2 ⟨ξ, hξ, Finset.mem_filter.2 ⟨hq, y, hy, not_le.1 hy'⟩⟩)
    have hB := hY₁ Y h1 (F * U) _ ψ q (fun n => ξ.2 n) hlo hhi ⟨hψ1, hlev, hz⟩ hψ hS
    apply hnb
    intro N _ ψ' hI
    have he := ind_unique N _ M ψ' ψ hM0 hI.1 hψp (fun n hn => (hI.2 n hn).trans (hψ n).symm)
    obtain ⟨rfl, he2⟩ := Sigma.mk.inj_iff.1 he
    obtain rfl := eq_of_heq he2
    exact hB
  have hP0 : (0 : ℝ) ≤ (PPset m₀ a₀ U).card := Nat.cast_nonneg _
  have hb1 : (B₁.card : ℝ) ≤ η / 2 * (PPset m₀ a₀ U).card := by
    have h := hcb (F * U) F B₁ (by nlinarith) (fun q hq => by
      obtain ⟨hq1, hq2⟩ := Finset.mem_filter.1 hq
      exact ⟨(hPP q hq1).1, lt_of_le_of_lt hFU (hPP q hq1).2.1, hq2⟩)
    have e : (U ^ (1 / 2 : ℝ) * U) ^ (1 / 4 : ℝ) = U ^ (3 / 8 : ℝ) := by
      rw [← Real.rpow_add_one hU0.ne', ← Real.rpow_mul hU0.le]; norm_num
    have h' : (F * U) ^ (1 / 4 : ℝ) ≤ U ^ (3 / 8 : ℝ) := by
      rw [← e]
      exact Real.rpow_le_rpow (by positivity) (mul_le_mul_of_nonneg_right hFU hU0.le) (by norm_num)
    calc (B₁.card : ℝ) ≤ Cb * (F * U) ^ (1 / 4 : ℝ) := h
      _ ≤ |Cb| * U ^ (3 / 8 : ℝ) :=
          mul_le_mul (le_abs_self _) h' (by positivity) (abs_nonneg _)
      _ ≤ η / 2 * U ^ (9 / 10 : ℝ) := hpow
      _ ≤ _ := mul_le_mul_of_nonneg_left hcount (by positivity)
  have hb2 : ∀ ξ ∈ Ξ, ((B₂ ξ).card : ℝ) ≤ η / (2 * (R + 1)) * (PPset m₀ a₀ U).card := by
    intro ξ _
    exact hY₃ Y h3 (Y ^ K) _ _ (B₂ ξ) (fun n => ξ.2 n) (fun n => ξ.2.norm_le_one _) hM
      ((Finset.filter_subset _ _).trans hB) (fun q hq => (Finset.mem_filter.1 hq).2)
  have hb3 : ((Ξ.biUnion B₂).card : ℝ) ≤ η / 2 * (PPset m₀ a₀ U).card := by
    have hR' : (Ξ.card : ℝ) ≤ R + 1 := by exact_mod_cast hR.trans (Nat.le_succ R)
    calc ((Ξ.biUnion B₂).card : ℝ) ≤ ∑ ξ ∈ Ξ, ((B₂ ξ).card : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ ≤ Ξ.card • (η / (2 * (R + 1)) * (PPset m₀ a₀ U).card) := Finset.sum_le_card_nsmul _ _ _ hb2
      _ ≤ (R + 1) * (η / (2 * (R + 1)) * (PPset m₀ a₀ U).card) := by
          rw [nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right hR' (by positivity)
      _ = _ := by field_simp
  have hc : (B.card : ℝ) ≤ B₁.card + (Ξ.biUnion B₂).card := by
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  linarith

end QH
