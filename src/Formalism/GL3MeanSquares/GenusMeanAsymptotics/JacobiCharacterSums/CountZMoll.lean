module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.CountZDefs
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MSqDiagA

@[expose] public section

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.CountZMoll
open Complex Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD

lemma mco_one {Y N : ℕ} (hY : 1 ≤ Y) (hN : 1 ≤ N) : mco Y N 1 = 1 := by
  unfold mco
  have h : (Icc 1 Y ×ˢ Icc 1 N).filter (fun p : ℕ × ℕ => p.1 * p.2 = 1) = {(1, 1)} := by
    ext ⟨a, b⟩
    simp only [mem_filter, mem_product, mem_Icc, mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨⟨ha1, -⟩, hb1, -⟩, h⟩
      constructor <;> nlinarith
    · rintro ⟨rfl, rfl⟩
      exact ⟨⟨⟨le_rfl, hY⟩, le_rfl, hN⟩, rfl⟩
  rw [h, sum_singleton]
  simp

lemma mco_filter_eq_antidiag {Y N n : ℕ} (hn : 1 ≤ n) (hnY : n ≤ Y) (hYN : Y ≤ N) :
    (Icc 1 Y ×ˢ Icc 1 N).filter (fun p : ℕ × ℕ => p.1 * p.2 = n) = n.divisorsAntidiagonal := by
  ext ⟨a, b⟩
  simp only [mem_filter, mem_product, mem_Icc, Nat.mem_divisorsAntidiagonal]
  constructor
  · rintro ⟨-, h⟩
    exact ⟨h, by omega⟩
  · rintro ⟨h, -⟩
    have ha : a ≠ 0 := by
      rintro rfl
      omega
    have hb : b ≠ 0 := by
      rintro rfl
      omega
    have ha' : a ≤ n := Nat.le_of_dvd (by omega) (Dvd.intro b h)
    have hb' : b ≤ n := Nat.le_of_dvd (by omega) (Dvd.intro_left a h)
    exact ⟨⟨⟨by omega, by omega⟩, by omega, by omega⟩, h⟩

lemma mco_filter_subset_antidiag {Y N n : ℕ} (hn : 1 ≤ n) :
    (Icc 1 Y ×ˢ Icc 1 N).filter (fun p : ℕ × ℕ => p.1 * p.2 = n) ⊆ n.divisorsAntidiagonal := by
  intro x hx
  rw [mem_filter] at hx
  rw [Nat.mem_divisorsAntidiagonal]
  exact ⟨hx.2, by omega⟩

lemma mco_sum_moebius_divisors {n : ℕ} (hn : 2 ≤ n) : ∑ i ∈ n.divisors, (μ i : ℤ) = 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f n) moebius_mul_coe_zeta
  simp only [coe_mul_zeta_apply] at h
  rw [h, one_apply_ne (by omega)]

lemma mco_eq_zero {Y N n : ℕ} (h2 : 2 ≤ n) (hnY : n ≤ Y) (hYN : Y ≤ N) : mco Y N n = 0 := by
  unfold mco
  rw [mco_filter_eq_antidiag (by omega) hnY hYN]
  have h := Nat.sum_divisorsAntidiagonal (fun a _ => ((μ a : ℤ) : ℂ)) (n := n)
  rw [h]
  exact_mod_cast mco_sum_moebius_divisors h2

lemma mco_norm_le (Y N : ℕ) {n : ℕ} (hn : 1 ≤ n) : ‖mco Y N n‖ ≤ (n.divisors.card : ℝ) := by
  unfold mco
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (sum_le_sum (g := fun _ => (1 : ℝ)) ?_) ?_
  · intro p _
    have h1 := abs_moebius_le_one (n := p.1)
    first
      | (rw [Complex.norm_intCast]; exact_mod_cast h1)
      | (rw [Complex.norm_int]; exact_mod_cast h1)
      | (rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]; exact_mod_cast h1)
  · rw [sum_const, nsmul_eq_mul, mul_one]
    have hc := card_le_card (mco_filter_subset_antidiag (Y := Y) (N := N) hn)
    have he : n.divisorsAntidiagonal.card = n.divisors.card := by
      first
        | exact Nat.card_divisorsAntidiagonal_eq_card_divisors n
        | (rw [← Nat.map_div_right_divisors, card_map])
    rw [he] at hc
    exact_mod_cast hc

theorem mollifier_identity : MollId := by
  unfold MollId
  intro q _ χ s Y N K hY hYN hK
  have hN : 1 ≤ N := le_trans hY hYN
  have hYK : Y ≤ K := by
    calc Y = Y * 1 := (mul_one Y).symm
      _ ≤ Y * N := Nat.mul_le_mul le_rfl hN
      _ ≤ K := hK
  have hmaps : ∀ p ∈ Icc 1 Y ×ˢ Icc 1 N, p.1 * p.2 ∈ Icc 1 K := by
    intro p hp
    simp only [mem_product, mem_Icc] at hp ⊢
    constructor
    · have := Nat.mul_le_mul hp.1.1 hp.2.1
      simpa using this
    · exact le_trans (Nat.mul_le_mul hp.1.2 hp.2.2) hK
  rw [sum_mul]
  simp_rw [mul_sum]
  rw [sum_comm, ← sum_product',
    ← sum_fiberwise_of_maps_to (g := fun p : ℕ × ℕ => p.1 * p.2) (t := Icc 1 K) hmaps]
  calc _ = ∑ k ∈ Icc 1 K, mco Y N k * χ k * (k : ℂ) ^ (-s) := by
        apply sum_congr rfl
        intro k _
        unfold mco
        rw [sum_mul, sum_mul]
        apply sum_congr rfl
        intro p hp
        rw [mem_filter] at hp
        obtain ⟨-, hpk⟩ := hp
        subst hpk
        simp only [Nat.cast_mul, map_mul, Complex.natCast_mul_natCast_cpow]
        ring
    _ = 1 + ∑ n ∈ Ioc Y K, mco Y N n * χ n * (n : ℂ) ^ (-s) := by
        have hsplit : Icc 1 K = Icc 1 Y ∪ Ioc Y K := by
          ext k
          simp only [mem_union, mem_Icc, mem_Ioc]
          omega
        have hdisj : Disjoint (Icc 1 Y) (Ioc Y K) := by
          rw [disjoint_left]
          intro k hk hk'
          rw [mem_Icc] at hk
          rw [mem_Ioc] at hk'
          omega
        rw [hsplit, sum_union hdisj]
        congr 1
        rw [sum_eq_single 1]
        · rw [mco_one hY hN]
          simp
        · intro k hk hk1
          rw [mem_Icc] at hk
          rw [mco_eq_zero (by omega) hk.2 hYN]
          simp
        · intro h
          exact absurd (mem_Icc.mpr ⟨le_rfl, hY⟩) h

theorem coefficient_square_bound : CoeffSqOf := by
  unfold CoeffSqOf
  intro hD
  unfold CoeffSq
  unfold FX.DivisorBound at hD
  have hs0 : s0 = 399 / 400 := by
    unfold s0
    norm_num
  obtain ⟨C, hC⟩ := hD (1 / 400) (by norm_num)
  have hC1 : 1 ≤ C := by
    have h := hC 1 le_rfl
    simpa using h
  refine ⟨C ^ 2, by positivity, ?_⟩
  intro Y N U hU
  have hUpos : (0 : ℝ) < U := by exact_mod_cast hU
  have hU1 : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hterm : ∀ n ∈ Ioc U (2 * U),
      (‖mco Y N n‖ * (n : ℝ) ^ (-s0)) ^ 2 ≤ (C * (U : ℝ) ^ (-(199 / 200 : ℝ))) ^ 2 := by
    intro n hn
    rw [mem_Ioc] at hn
    have hn1 : 1 ≤ n := by omega
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have hUn : (U : ℝ) ≤ n := by exact_mod_cast hn.1.le
    have h1 : ‖mco Y N n‖ ≤ C * (n : ℝ) ^ (1 / 400 : ℝ) := le_trans (mco_norm_le Y N hn1) (hC n hn1)
    have h2 : (n : ℝ) ^ (1 / 400 : ℝ) * (n : ℝ) ^ (-s0) = (n : ℝ) ^ (-(199 / 200 : ℝ)) := by
      rw [← Real.rpow_add hnpos, hs0]
      norm_num
    have h3 : (n : ℝ) ^ (-(199 / 200 : ℝ)) ≤ (U : ℝ) ^ (-(199 / 200 : ℝ)) := by
      first
        | exact Real.rpow_le_rpow_of_nonpos hUpos hUn (by norm_num)
        | exact Real.rpow_le_rpow_of_exponent_nonpos hUpos hUn (by norm_num)
        | (rw [Real.rpow_neg hnpos.le, Real.rpow_neg hUpos.le]
           exact inv_anti₀ (Real.rpow_pos_of_pos hUpos _) (Real.rpow_le_rpow hUpos.le hUn (by norm_num)))
        | (rw [Real.rpow_neg hnpos.le, Real.rpow_neg hUpos.le]
           exact inv_le_inv_of_le (Real.rpow_pos_of_pos hUpos _) (Real.rpow_le_rpow hUpos.le hUn (by norm_num)))
    have h4 : 0 ≤ ‖mco Y N n‖ * (n : ℝ) ^ (-s0) := mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hnpos.le _)
    have h5 : ‖mco Y N n‖ * (n : ℝ) ^ (-s0) ≤ C * (U : ℝ) ^ (-(199 / 200 : ℝ)) := by
      calc ‖mco Y N n‖ * (n : ℝ) ^ (-s0) ≤ C * (n : ℝ) ^ (1 / 400 : ℝ) * (n : ℝ) ^ (-s0) :=
            mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hnpos.le _)
        _ = C * (n : ℝ) ^ (-(199 / 200 : ℝ)) := by rw [mul_assoc, h2]
        _ ≤ C * (U : ℝ) ^ (-(199 / 200 : ℝ)) := mul_le_mul_of_nonneg_left h3 (by linarith)
    first
      | exact pow_le_pow_left h4 h5 2
      | exact pow_le_pow_left₀ h4 h5 2
      | nlinarith
  have e1 : ((U : ℝ) ^ (-(199 / 200 : ℝ))) ^ 2 = (U : ℝ) ^ (-(199 / 100 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hUpos.le]
    norm_num
  have e2 : (U : ℝ) * (U : ℝ) ^ (-(199 / 100 : ℝ)) = (U : ℝ) ^ (-(99 / 100 : ℝ)) := by
    rw [show (U : ℝ) ^ (-(99 / 100 : ℝ)) = (U : ℝ) ^ ((1 : ℝ) + -(199 / 100 : ℝ)) by norm_num,
      Real.rpow_add hUpos, Real.rpow_one]
  calc ∑ n ∈ Ioc U (2 * U), (‖mco Y N n‖ * (n : ℝ) ^ (-s0)) ^ 2
      ≤ ∑ n ∈ Ioc U (2 * U), (C * (U : ℝ) ^ (-(199 / 200 : ℝ))) ^ 2 := sum_le_sum hterm
    _ = (U : ℝ) * (C * (U : ℝ) ^ (-(199 / 200 : ℝ))) ^ 2 := by
        rw [sum_const, Nat.card_Ioc, show 2 * U - U = U by omega, nsmul_eq_mul]
    _ = C ^ 2 * ((U : ℝ) * ((U : ℝ) ^ (-(199 / 200 : ℝ))) ^ 2) := by ring
    _ = C ^ 2 * (U : ℝ) ^ (-(99 / 100 : ℝ)) := by rw [e1, e2]
    _ ≤ C ^ 2 * (U : ℝ) ^ (-(197 / 200 : ℝ)) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU1 (by norm_num)) (by positivity)

end Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
end
end

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.CountZDetect
open Complex Finset
open scoped ArithmeticFunction.Moebius

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD

lemma sum_blocks (f : ℕ → ℂ) (Y : ℕ) : ∀ J : ℕ,
    ∑ n ∈ Ioc Y (Y * 2 ^ J), f n = ∑ j ∈ range J, ∑ n ∈ Ioc (Y * 2 ^ j) (2 * (Y * 2 ^ j)), f n
  | 0 => by simp
  | J + 1 => by
    rw [sum_range_succ, ← sum_blocks f Y J]
    have h1 : Y ≤ Y * 2 ^ J := Nat.le_mul_of_pos_right Y (by positivity)
    have h2 : Y * 2 ^ J ≤ Y * 2 ^ (J + 1) := Nat.mul_le_mul_left Y (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [show 2 * (Y * 2 ^ J) = Y * 2 ^ (J + 1) by ring]
    exact (Finset.sum_Ioc_consecutive _ h1 h2).symm

lemma mollM_norm_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) (hs : 0 ≤ s.re) (Y : ℕ) :
    ‖∑ d ∈ Icc 1 Y, (((μ d : ℤ)) : ℂ) * χ (d : ZMod q) * (d : ℂ) ^ (-s)‖ ≤ Y := by
  refine le_trans (norm_sum_le _ _) ?_
  have h1 : ∀ d ∈ Icc 1 Y, ‖(((μ d : ℤ)) : ℂ) * χ (d : ZMod q) * (d : ℂ) ^ (-s)‖ ≤ 1 := by
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.1 hd).1
    rw [norm_mul, norm_mul]
    have hμ : ‖(((μ d : ℤ)) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    have hχ : ‖χ (d : ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
    have hp : ‖(d : ℂ) ^ (-s)‖ ≤ 1 := by
      rw [Complex.norm_natCast_cpow_of_pos (by omega)]
      refine Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hd1) ?_
      simp only [Complex.neg_re]
      linarith
    calc ‖(((μ d : ℤ)) : ℂ)‖ * ‖χ (d : ZMod q)‖ * ‖(d : ℂ) ^ (-s)‖ ≤ 1 * 1 * 1 := by gcongr
      _ = 1 := by ring
  calc ∑ d ∈ Icc 1 Y, ‖(((μ d : ℤ)) : ℂ) * χ (d : ZMod q) * (d : ℂ) ^ (-s)‖ ≤ ∑ d ∈ Icc 1 Y, (1 : ℝ) :=
        Finset.sum_le_sum h1
    _ = Y := by simp

attribute [local irreducible] q0 pY pJ pN in
theorem zero_detection : DetectOf := by
  intro hM Q hQ p hp hp1 hpQ ρ hρ hρim hL
  obtain ⟨N0, χ⟩ := p
  simp only at hp hp1 hpQ hL
  obtain ⟨X, hX⟩ : ∃ X : ℕ, q0 Q = X := ⟨_, rfl⟩
  have hXQ : Q ≤ (X : ℝ) := by rw [← hX]; unfold q0; exact Nat.le_ceil Q
  have hX20 : (20 : ℝ) ≤ X := le_trans hQ hXQ
  have hX1 : 1 ≤ X := by exact_mod_cast (show (1 : ℝ) ≤ X by linarith)
  have hs0 : s0 = 399 / 400 := by unfold s0; norm_num
  have hre0 : 0 < ρ.re := by rw [hs0] at hρ; linarith

  have hχ1 : χ ≠ 1 := by
    intro h
    have hc : χ.conductor = N0 + 1 := hp
    rw [h, DirichletCharacter.conductor_one] at hc
    omega

  have hJ8 : 8 ≤ pJ Q := by unfold pJ; omega
  have hNX : X ^ 8 ≤ pN Q := by
    have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) X
    unfold pN pJ
    rw [hX, mul_comm 8, pow_mul]
    exact Nat.pow_le_pow_left h.le 8
  have hY : pY Q = X ^ 4 := by unfold pY; rw [hX]
  have hYN : pY Q ≤ pN Q := by
    rw [hY]; exact le_trans (Nat.pow_le_pow_right hX1 (by norm_num)) hNX
  have hY1 : 1 ≤ pY Q := by rw [hY]; exact Nat.one_le_pow _ _ (by omega)
  have hN1 : 1 ≤ pN Q := le_trans hY1 hYN

  have hB := Formalism.ZeroFreeDirichlet.norm_character_sum_Icc_le χ hχ1
  have hP := Formalism.FX.l_function_partial_sum (N0 + 1) χ hχ1 _ hB ρ hre0 (pN Q) hN1
  rw [hL, zero_sub, norm_neg] at hP

  have hMI := hM (N0 + 1) χ ρ (pY Q) (pN Q) (pY Q * pN Q) hY1 hYN le_rfl
  have hMo := mollM_norm_le χ ρ hre0.le (pY Q)
  set P := ∑ n ∈ Icc 1 (pN Q), χ (n : ZMod (N0 + 1)) * (n : ℂ) ^ (-ρ) with hPdef
  set Mo := ∑ d ∈ Icc 1 (pY Q), (((μ d : ℤ)) : ℂ) * χ (d : ZMod (N0 + 1)) * (d : ℂ) ^ (-ρ) with hMdef
  set D := ∑ n ∈ Ioc (pY Q) (pY Q * pN Q), mco (pY Q) (pN Q) n * χ (n : ZMod (N0 + 1)) * (n : ℂ) ^ (-ρ) with hD

  have hnum : ‖P‖ * (pY Q : ℝ) ≤ 1 / 2 := by
    have hq : ((N0 + 1 : ℕ) : ℝ) + 1 ≤ 2 * X := by
      have : ((N0 + 1 : ℕ) : ℝ) ≤ Q := hpQ
      linarith
    have hrho : 1 + ‖ρ‖ / ρ.re ≤ 3 * X := by
      have h1 : ‖ρ‖ ≤ ρ.re + Q := by
        refine (Complex.norm_le_abs_re_add_abs_im ρ).trans ?_
        rw [abs_of_pos hre0]; linarith
      have h2 : ‖ρ‖ / ρ.re ≤ 1 + Q / ρ.re := by
        rw [div_le_iff₀ hre0]; rw [add_mul, one_mul, div_mul_cancel₀ _ hre0.ne']; linarith
      have h3 : Q / ρ.re ≤ 2 * Q := by
        rw [div_le_iff₀ hre0]; rw [hs0] at hρ; nlinarith
      linarith
    have hNpos : (0 : ℝ) < pN Q := by exact_mod_cast hN1
    have hXpos : (0 : ℝ) < X := by linarith
    have hpow : ((pN Q : ℕ) : ℝ) ^ (-ρ.re) ≤ ((pN Q : ℕ) : ℝ) ^ (-(15 / 16 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1) (by rw [hs0] at hρ; linarith)
    have hN8 : (X : ℝ) ^ (8 : ℕ) ≤ (pN Q : ℝ) := by exact_mod_cast hNX
    have hpow2 : 4 * (X : ℝ) ^ (7 : ℕ) ≤ ((pN Q : ℕ) : ℝ) ^ (15 / 16 : ℝ) := by
      have e : ((X : ℝ) ^ (8 : ℕ)) ^ (15 / 16 : ℝ) = (X : ℝ) ^ (7 : ℕ) * Real.sqrt X := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hXpos.le, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
          ← Real.rpow_add hXpos]
        norm_num
      have hs : (4 : ℝ) ≤ Real.sqrt X := by
        rw [show (4 : ℝ) = Real.sqrt 16 by rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_le_sqrt (by linarith)
      calc 4 * (X : ℝ) ^ (7 : ℕ) ≤ (X : ℝ) ^ (7 : ℕ) * Real.sqrt X := by
            have : (0 : ℝ) ≤ (X : ℝ) ^ (7 : ℕ) := by positivity
            rw [mul_comm]; exact mul_le_mul_of_nonneg_left hs this
        _ = ((X : ℝ) ^ (8 : ℕ)) ^ (15 / 16 : ℝ) := e.symm
        _ ≤ _ := Real.rpow_le_rpow (by positivity) hN8 (by norm_num)
    have hinv : ((pN Q : ℕ) : ℝ) ^ (-(15 / 16 : ℝ)) ≤ 1 / (4 * (X : ℝ) ^ (7 : ℕ)) := by
      rw [Real.rpow_neg hNpos.le, one_div]
      exact inv_anti₀ (by positivity) hpow2
    have hYr : (pY Q : ℝ) = (X : ℝ) ^ (4 : ℕ) := by rw [hY, Nat.cast_pow]
    have hPle : ‖P‖ ≤ 2 * (2 * X) * (3 * X) * (1 / (4 * (X : ℝ) ^ (7 : ℕ))) := by
      refine hP.trans ?_
      have hpos1 : (0 : ℝ) ≤ ((N0 + 1 : ℕ) : ℝ) + 1 := by positivity
      have hpos2 : (0 : ℝ) ≤ 1 + ‖ρ‖ / ρ.re := by positivity
      have a1 : 2 * (((N0 + 1 : ℕ) : ℝ) + 1) ≤ 2 * (2 * X) := by linarith
      have a12 : 2 * (((N0 + 1 : ℕ) : ℝ) + 1) * (1 + ‖ρ‖ / ρ.re) ≤ 2 * (2 * X) * (3 * X) :=
        mul_le_mul a1 hrho hpos2 (by positivity)
      have a3 : ((pN Q : ℕ) : ℝ) ^ (-ρ.re) ≤ 1 / (4 * (X : ℝ) ^ (7 : ℕ)) := hpow.trans hinv
      calc 2 * (((N0 + 1 : ℕ) : ℝ) + 1) * (1 + ‖ρ‖ / ρ.re) * ((pN Q : ℕ) : ℝ) ^ (-ρ.re)
          ≤ 2 * (2 * X) * (3 * X) * ((pN Q : ℕ) : ℝ) ^ (-ρ.re) :=
            mul_le_mul_of_nonneg_right a12 (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        _ ≤ 2 * (2 * X) * (3 * X) * (1 / (4 * (X : ℝ) ^ (7 : ℕ))) :=
            mul_le_mul_of_nonneg_left a3 (by positivity)
    rw [hYr]
    calc ‖P‖ * (X : ℝ) ^ (4 : ℕ) ≤ 2 * (2 * X) * (3 * X) * (1 / (4 * (X : ℝ) ^ (7 : ℕ))) * (X : ℝ) ^ (4 : ℕ) :=
          mul_le_mul_of_nonneg_right hPle (by positivity)
      _ = 3 / X := by
          have hX0 : (X : ℝ) ≠ 0 := hXpos.ne'
          rw [eq_div_iff hX0]
          field_simp
          ring
      _ ≤ 1 / 2 := by rw [div_le_iff₀ hXpos]; linarith
  have h1D : ‖1 + D‖ ≤ 1 / 2 := by
    rw [← hMI]
    rw [norm_mul]
    calc ‖P‖ * ‖Mo‖ ≤ ‖P‖ * (pY Q : ℝ) := mul_le_mul_of_nonneg_left hMo (norm_nonneg _)
      _ ≤ 1 / 2 := hnum
  have hDge : 1 / 2 ≤ ‖D‖ := by
    have := norm_sub_le (1 + D) D
    simp only [add_sub_cancel_right, norm_one] at this
    linarith

  have hsplit : D = ∑ j ∈ range (pJ Q), blk (pY Q) (pN Q) (pY Q * 2 ^ j) ⟨N0, χ⟩ ρ := by
    rw [hD, show pN Q = 2 ^ pJ Q by unfold pN; rfl, sum_blocks]
    rfl
  by_contra hcon
  push_neg at hcon
  have hJpos : (0 : ℝ) < pJ Q := by exact_mod_cast (by omega : 0 < pJ Q)
  have hlt : ‖D‖ < 1 / 2 := by
    rw [hsplit]
    refine (norm_sum_le _ _).trans_lt ?_
    have hne : (range (pJ Q)).Nonempty := nonempty_range_iff.mpr (by omega)
    calc ∑ j ∈ range (pJ Q), ‖blk (pY Q) (pN Q) (pY Q * 2 ^ j) ⟨N0, χ⟩ ρ‖
        < ∑ j ∈ range (pJ Q), 1 / (2 * (pJ Q : ℝ)) := sum_lt_sum_of_nonempty hne hcon
      _ = 1 / 2 := by rw [sum_const, card_range, nsmul_eq_mul]; field_simp
  linarith

end Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
end
end

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.CountZDual
open Complex Finset

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD

theorem duality_inequality : DualIneq := by
  intro ι κ S I b v Δ hΔ hrow
  classical
  have hz : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * (starRingEnd ℂ) z := by
    intro z
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  obtain ⟨s, hs⟩ : ∃ s : ι → ℂ, s = fun i => ∑ n ∈ I, b n * v i n := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : κ → ℂ, w = fun n => ∑ i ∈ S, (starRingEnd ℂ) (s i) * v i n := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : ι → ι → ℂ, G = fun i j => ∑ n ∈ I, v i n * (starRingEnd ℂ) (v j n) :=
    ⟨_, rfl⟩
  have hs' : ∀ i, ∑ n ∈ I, b n * v i n = s i := fun i => by rw [hs]
  have hG' : ∀ i j, ∑ n ∈ I, v i n * (starRingEnd ℂ) (v j n) = G i j := fun i j => by rw [hG]
  simp_rw [hs']
  simp_rw [hG'] at hrow
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = ∑ i ∈ S, ‖s i‖ ^ 2 := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = ∑ n ∈ I, ‖b n‖ ^ 2 := ⟨_, rfl⟩
  rw [← hX, ← hB]
  have hXnn : 0 ≤ X := by rw [hX]; positivity
  have hBnn : 0 ≤ B := by rw [hB]; positivity

  have h1 : ((X : ℝ) : ℂ) = ∑ n ∈ I, b n * w n := by
    rw [hX, Complex.ofReal_sum]
    simp_rw [hz]
    simp only [hw, Finset.mul_sum]
    conv_lhs => enter [2, i]; rw [hs]
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n _
    apply Finset.sum_congr rfl
    intro i _
    rw [hs]
    ring
  have h2 : X ≤ ∑ n ∈ I, ‖b n‖ * ‖w n‖ := by
    calc X = ‖((X : ℝ) : ℂ)‖ := by rw [Complex.norm_real, Real.norm_of_nonneg hXnn]
      _ = ‖∑ n ∈ I, b n * w n‖ := by rw [h1]
      _ ≤ ∑ n ∈ I, ‖b n * w n‖ := norm_sum_le _ _
      _ = ∑ n ∈ I, ‖b n‖ * ‖w n‖ := by simp_rw [norm_mul]
  have h3 := Finset.sum_mul_sq_le_sq_mul_sq I (fun n => ‖b n‖) (fun n => ‖w n‖)

  have hGsym : ∀ i j, ‖G i j‖ = ‖G j i‖ := by
    intro i j
    have e : G j i = (starRingEnd ℂ) (G i j) := by
      rw [hG]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_mul, Complex.conj_conj]
      apply Finset.sum_congr rfl
      intro n _
      ring
    rw [e, Complex.norm_conj]
  have e : ((∑ n ∈ I, ‖w n‖ ^ 2 : ℝ) : ℂ) =
      ∑ i ∈ S, ∑ j ∈ S, (starRingEnd ℂ) (s i) * s j * G i j := by
    conv_rhs => rw [Finset.sum_comm]
    rw [Complex.ofReal_sum]
    simp_rw [hz]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hw, hG, map_sum, map_mul, Complex.conj_conj, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm (s := I) (t := S)]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm (s := I) (t := S)]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro n _
    ring
  have hle : ∑ n ∈ I, ‖w n‖ ^ 2 ≤ ∑ i ∈ S, ∑ j ∈ S, ‖s i‖ * ‖s j‖ * ‖G i j‖ := by
    have hnn : (0 : ℝ) ≤ ∑ n ∈ I, ‖w n‖ ^ 2 := by positivity
    calc ∑ n ∈ I, ‖w n‖ ^ 2 = ‖((∑ n ∈ I, ‖w n‖ ^ 2 : ℝ) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_of_nonneg hnn]
      _ = ‖∑ i ∈ S, ∑ j ∈ S, (starRingEnd ℂ) (s i) * s j * G i j‖ := by rw [e]
      _ ≤ ∑ i ∈ S, ‖∑ j ∈ S, (starRingEnd ℂ) (s i) * s j * G i j‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ S, ∑ j ∈ S, ‖s i‖ * ‖s j‖ * ‖G i j‖ := by
          apply Finset.sum_le_sum
          intro i _
          refine (norm_sum_le _ _).trans (le_of_eq ?_)
          apply Finset.sum_congr rfl
          intro j _
          rw [norm_mul, norm_mul, Complex.norm_conj]
  have hsplit : ∑ i ∈ S, ∑ j ∈ S, (‖s i‖ ^ 2 * ‖G i j‖ / 2 + ‖s j‖ ^ 2 * ‖G j i‖ / 2) =
      ∑ i ∈ S, ∑ j ∈ S, ‖s i‖ ^ 2 * ‖G i j‖ := by
    simp only [Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun i j => ‖s j‖ ^ 2 * ‖G j i‖ / 2), ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hamgm : ∑ i ∈ S, ∑ j ∈ S, ‖s i‖ * ‖s j‖ * ‖G i j‖ ≤ Δ * X := by
    calc ∑ i ∈ S, ∑ j ∈ S, ‖s i‖ * ‖s j‖ * ‖G i j‖
        ≤ ∑ i ∈ S, ∑ j ∈ S, (‖s i‖ ^ 2 * ‖G i j‖ / 2 + ‖s j‖ ^ 2 * ‖G j i‖ / 2) := by
          apply Finset.sum_le_sum
          intro i _
          apply Finset.sum_le_sum
          intro j _
          rw [← hGsym i j]
          have h0 := sq_nonneg (‖s i‖ - ‖s j‖)
          have hg := norm_nonneg (G i j)
          nlinarith
      _ = ∑ i ∈ S, ∑ j ∈ S, ‖s i‖ ^ 2 * ‖G i j‖ := hsplit
      _ = ∑ i ∈ S, ‖s i‖ ^ 2 * ∑ j ∈ S, ‖G i j‖ := by simp_rw [Finset.mul_sum]
      _ ≤ ∑ i ∈ S, ‖s i‖ ^ 2 * Δ := by
          apply Finset.sum_le_sum
          intro i hi
          exact mul_le_mul_of_nonneg_left (hrow i hi) (sq_nonneg _)
      _ = Δ * X := by rw [hX, Finset.mul_sum]; simp_rw [mul_comm]
  have hXsq : X ^ 2 ≤ B * (Δ * X) := by
    have hY : 0 ≤ ∑ n ∈ I, ‖b n‖ * ‖w n‖ := by positivity
    calc X ^ 2 ≤ (∑ n ∈ I, ‖b n‖ * ‖w n‖) ^ 2 := by nlinarith
      _ ≤ (∑ n ∈ I, ‖b n‖ ^ 2) * ∑ n ∈ I, ‖w n‖ ^ 2 := h3
      _ ≤ B * (Δ * X) := by
          rw [← hB]
          exact mul_le_mul_of_nonneg_left (hle.trans hamgm) hBnn
  rcases hXnn.eq_or_lt with h0 | hpos
  · rw [← h0]
    positivity
  · nlinarith

end Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
end
end

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MSqDiagB
open Finset Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

open Formalism.HermitianLattices.ZeroFreeRegionGL2

theorem sum_log_sq_div_sq_primes_dyadic_le (y : ℕ) (hy : 1 ≤ y) :
    ∑ p ∈ (Ioc y (2 * y)).filter Nat.Prime, Real.log p ^ 2 / (p : ℝ) ^ 2 ≤
      2 * Real.log 4 * Real.log (2 * y) / y := by
  have hyR : (1:ℝ) ≤ y := by exact_mod_cast hy
  have hy0 : (0:ℝ) < y := by linarith
  have hy0' : (y:ℝ) ≠ 0 := ne_of_gt hy0
  have hL0 : 0 ≤ Real.log (2 * y) := Real.log_nonneg (by linarith)
  have hy2pos : 0 < (y:ℝ) ^ 2 := by positivity
  have hterm : ∀ p ∈ (Ioc y (2 * y)).filter Nat.Prime,
      Real.log p ^ 2 / (p : ℝ) ^ 2 ≤ Real.log (2 * y) / (y:ℝ) ^ 2 * Real.log p := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Ioc] at hp
    obtain ⟨⟨h1, h2⟩, hpr⟩ := hp
    have hp1 : (y:ℝ) < p := by exact_mod_cast h1
    have hp2 : (p:ℝ) ≤ 2 * y := by exact_mod_cast h2
    have hppos : (0:ℝ) < p := by linarith
    have hp2pos : 0 < (p:ℝ) ^ 2 := by positivity
    have hlp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpr.one_lt.le)
    have hlle : Real.log p ≤ Real.log (2 * y) := Real.log_le_log hppos hp2
    have hyp : (y:ℝ) ^ 2 ≤ (p:ℝ) ^ 2 := by nlinarith
    have hnum : 0 ≤ Real.log (2 * y) * Real.log p := mul_nonneg hL0 hlp
    calc Real.log p ^ 2 / (p:ℝ) ^ 2 = Real.log p * Real.log p / (p:ℝ) ^ 2 := by ring
      _ ≤ Real.log (2 * y) * Real.log p / (p:ℝ) ^ 2 := by
          gcongr ?_ * _ / _
      _ ≤ Real.log (2 * y) * Real.log p / (y:ℝ) ^ 2 := by
          gcongr _ / ?_
      _ = Real.log (2 * y) / (y:ℝ) ^ 2 * Real.log p := by ring
  have hsum : ∑ p ∈ (Ioc y (2 * y)).filter Nat.Prime, Real.log p ≤ 2 * y * Real.log 4 := by
    have hsub : (Ioc y (2 * y)).filter Nat.Prime ⊆ (Finset.range (2 * y + 1)).filter Nat.Prime := by
      intro p hp
      rw [Finset.mem_filter, Finset.mem_Ioc] at hp
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hp.2⟩
    calc ∑ p ∈ (Ioc y (2 * y)).filter Nat.Prime, Real.log p
        ≤ ∑ p ∈ (Finset.range (2 * y + 1)).filter Nat.Prime, Real.log p :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => Real.log_natCast_nonneg p)
      _ = Real.log (primorial (2 * y)) := by
          rw [primorial, Nat.cast_prod, Real.log_prod]
          intro p hp
          rw [Finset.mem_filter] at hp
          exact_mod_cast hp.2.ne_zero
      _ ≤ Real.log (4 ^ (2 * y)) := by
          apply Real.log_le_log
          · exact_mod_cast primorial_pos (2 * y)
          · exact_mod_cast primorial_le_four_pow (2 * y)
      _ = 2 * y * Real.log 4 := by
          rw [Real.log_pow]
          push_cast
          ring
  calc ∑ p ∈ (Ioc y (2 * y)).filter Nat.Prime, Real.log p ^ 2 / (p : ℝ) ^ 2
      ≤ ∑ p ∈ (Ioc y (2 * y)).filter Nat.Prime, Real.log (2 * y) / (y:ℝ) ^ 2 * Real.log p :=
        Finset.sum_le_sum hterm
    _ = Real.log (2 * y) / (y:ℝ) ^ 2 * ∑ p ∈ (Ioc y (2 * y)).filter Nat.Prime, Real.log p := by
        rw [Finset.mul_sum]
    _ ≤ Real.log (2 * y) / (y:ℝ) ^ 2 * (2 * y * Real.log 4) :=
        mul_le_mul_of_nonneg_left hsum (div_nonneg hL0 (sq_nonneg _))
    _ = 2 * Real.log 4 * Real.log (2 * y) / y := by
        field_simp

theorem sum_log_sq_div_sq_primes_tail_le (N : ℕ) : ∀ d y : ℕ, 1 ≤ y → N - y ≤ d →
    ∑ p ∈ (Ioc y N).filter Nat.Prime, Real.log p ^ 2 / (p : ℝ) ^ 2 ≤
      4 * Real.log 4 * (Real.log y + 2 * Real.log 2) / y := by
  intro d
  induction d with
  | zero =>
    intro y hy hd
    have hN : N ≤ y := by omega
    rw [Finset.Ioc_eq_empty_of_le hN, Finset.filter_empty, Finset.sum_empty]
    have hyR : (1:ℝ) ≤ y := by exact_mod_cast hy
    have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have hly : 0 ≤ Real.log y := Real.log_nonneg hyR
    have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) h4) (by linarith)) (by positivity)
  | succ d ih =>
    intro y hy hd
    have hyR : (1:ℝ) ≤ y := by exact_mod_cast hy
    have hy0 : (0:ℝ) < y := by linarith
    have hy0' : (y:ℝ) ≠ 0 := ne_of_gt hy0
    have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have hly : 0 ≤ Real.log y := Real.log_nonneg hyR
    have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hlog2y : Real.log (2 * y) = Real.log 2 + Real.log y :=
      Real.log_mul (by norm_num) hy0'
    have hblock := sum_log_sq_div_sq_primes_dyadic_le y hy
    by_cases hN : N ≤ 2 * y
    · have hsub : (Ioc y N).filter Nat.Prime ⊆ (Ioc y (2 * y)).filter Nat.Prime :=
        Finset.filter_subset_filter _ (Finset.Ioc_subset_Ioc_right hN)
      calc ∑ p ∈ (Ioc y N).filter Nat.Prime, Real.log p ^ 2 / (p : ℝ) ^ 2
          ≤ ∑ p ∈ (Ioc y (2 * y)).filter Nat.Prime, Real.log p ^ 2 / (p : ℝ) ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)
        _ ≤ 2 * Real.log 4 * Real.log (2 * y) / y := hblock
        _ ≤ 4 * Real.log 4 * (Real.log y + 2 * Real.log 2) / y := by
            gcongr ?_ / _
            rw [hlog2y]
            nlinarith [mul_nonneg hl4 hly, mul_nonneg hl4 hl2]
    · push_neg at hN
      have hsplit : (Ioc y N).filter Nat.Prime =
          (Ioc y (2 * y)).filter Nat.Prime ∪ (Ioc (2 * y) N).filter Nat.Prime := by
        rw [← Finset.filter_union, Finset.Ioc_union_Ioc_eq_Ioc (by omega) hN.le]
      have hdisj : Disjoint ((Ioc y (2 * y)).filter Nat.Prime) ((Ioc (2 * y) N).filter Nat.Prime) := by
        apply Finset.disjoint_filter_filter
        rw [Finset.disjoint_left]
        intro a ha hb
        rw [Finset.mem_Ioc] at ha hb
        omega
      have ht := ih (2 * y) (by omega) (by omega)
      rw [hsplit, Finset.sum_union hdisj]
      calc ∑ p ∈ (Ioc y (2 * y)).filter Nat.Prime, Real.log p ^ 2 / (p : ℝ) ^ 2 +
            ∑ p ∈ (Ioc (2 * y) N).filter Nat.Prime, Real.log p ^ 2 / (p : ℝ) ^ 2
          ≤ 2 * Real.log 4 * Real.log (2 * y) / y +
            4 * Real.log 4 * (Real.log ((2 * y : ℕ) : ℝ) + 2 * Real.log 2) / ((2 * y : ℕ) : ℝ) :=
            add_le_add hblock ht
        _ = 4 * Real.log 4 * (Real.log y + 2 * Real.log 2) / y := by
            push_cast
            rw [hlog2y]
            field_simp <;> ring

theorem sP_cN_nonneg (x : ℝ) (hx : 0 ≤ x) (N p : ℕ) : 0 ≤ sP (cN x) N p := by
  unfold sP cN
  apply Finset.sum_nonneg
  intro n _
  exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
    (le_min zero_le_one (div_nonneg hx (Nat.cast_nonneg n)))

theorem sP_cN_le_log_div (x : ℝ) (hx : 0 ≤ x) (N p : ℕ) (hp : p.Prime) :
    sP (cN x) N p ≤ 2 * x * Real.log p / p := by
  have hp2 : 2 ≤ p := hp.two_le
  have hpR : (2:ℝ) ≤ p := by exact_mod_cast hp2
  have hppos : (0:ℝ) < p := by linarith
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  set r : ℝ := 1 / (p:ℝ) with hr
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hr1 : r < 1 := by rw [hr, div_lt_one hppos]; linarith
  have hrh : r ≤ 1 / 2 := by rw [hr]; exact one_div_le_one_div_of_le (by norm_num) hpR
  have hsub : (Icc 1 N).filter (fun n => IsPrimePow n ∧ n.minFac = p) ⊆
      (Icc 1 N).image (fun k => p ^ k) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, hnN⟩, hpp, hmf⟩ := hn
    obtain ⟨q, k, hq, hk, rfl⟩ := (isPrimePow_nat_iff _).mp hpp
    have hpq : p = q := by
      have h1 : p ∣ q ^ k := by rw [← hmf]; exact Nat.minFac_dvd _
      exact (Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow h1)
    subst hpq
    rw [Finset.mem_image]
    refine ⟨k, Finset.mem_Icc.mpr ⟨hk, ?_⟩, rfl⟩
    have hlt := Nat.lt_pow_self (by omega : 1 < p) (n := k)
    exact le_of_lt (lt_of_lt_of_le hlt hnN)
  have h1 : sP (cN x) N p ≤ ∑ n ∈ (Icc 1 N).filter (fun n => IsPrimePow n ∧ n.minFac = p),
      Real.log p * (x / n) := by
    unfold sP
    apply Finset.sum_le_sum
    intro n hn
    rw [Finset.mem_filter] at hn
    unfold cN
    rw [ArithmeticFunction.vonMangoldt_apply, if_pos hn.2.1, hn.2.2]
    exact mul_le_mul_of_nonneg_left (min_le_right _ _) hlog
  calc sP (cN x) N p ≤ ∑ n ∈ (Icc 1 N).filter (fun n => IsPrimePow n ∧ n.minFac = p),
        Real.log p * (x / n) := h1
    _ ≤ ∑ n ∈ (Icc 1 N).image (fun k => p ^ k), Real.log p * (x / n) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun n _ _ => mul_nonneg hlog (div_nonneg hx (Nat.cast_nonneg n)))
    _ = ∑ k ∈ Icc 1 N, Real.log p * x * r ^ k := by
        rw [Finset.sum_image (Nat.pow_right_injective hp2).injOn]
        apply Finset.sum_congr rfl
        intro k _
        show Real.log p * (x / ((p ^ k : ℕ) : ℝ)) = Real.log p * x * r ^ k
        rw [hr, Nat.cast_pow, one_div, inv_pow]
        ring
    _ ≤ ∑ k ∈ Ico 1 (N + 1), Real.log p * x * r ^ k := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro k hk
          rw [Finset.mem_Icc] at hk
          rw [Finset.mem_Ico]
          omega
        · intro k _ _
          exact mul_nonneg (mul_nonneg hlog hx) (pow_nonneg hr0 k)
    _ = Real.log p * x * ∑ k ∈ Ico 1 (N + 1), r ^ k := by rw [Finset.mul_sum]
    _ ≤ Real.log p * x * (r ^ 1 / (1 - r)) :=
        mul_le_mul_of_nonneg_left (geom_sum_Ico_le_of_lt_one hr0 hr1) (mul_nonneg hlog hx)
    _ ≤ Real.log p * x * (2 * r) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hlog hx)
        rw [pow_one, div_le_iff₀ (by linarith)]
        nlinarith
    _ = 2 * x * Real.log p / p := by rw [hr]; ring

end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
end
end
