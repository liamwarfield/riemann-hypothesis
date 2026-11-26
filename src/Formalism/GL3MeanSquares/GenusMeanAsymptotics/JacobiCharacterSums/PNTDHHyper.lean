module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.DHFinish2Of

@[expose] public section

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHHyperC
section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHHyperB
section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHHyperA
open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

def cS (U : ℕ) : ℂ := ∑ b ∈ Ioc 0 U, χ (b : ZMod q) / (b : ℂ)

def cT (U : ℕ) : ℂ := ∑ b ∈ Ioc 0 U, χ (b : ZMod q) * (Real.log b : ℂ) / (b : ℂ)

def cF (N : ℕ) : ℂ := ∑ n ∈ Ioc 0 N, (∑ d ∈ n.divisors, χ (d : ZMod q)) / (n : ℂ)

def hH (k : ℕ) : ℝ := ∑ a ∈ Ioc 0 k, ((a : ℝ))⁻¹

theorem cF_eq (N : ℕ) :
    cF χ N = ∑ b ∈ Ioc 0 N, χ (b : ZMod q) / (b : ℂ) * (hH (N / b) : ℂ) := by
  have hcond : ∀ (n d : ℕ), n ∈ Finset.Ioc 0 N ∧ d ∈ n.divisors ↔
      n ∈ (Finset.Ioc 0 N).filter (d ∣ ·) ∧ d ∈ Finset.Ioc 0 N := by
    intro n d
    simp only [Finset.mem_Ioc, Nat.mem_divisors, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hn0, hnN⟩, hdn, -⟩
      have h1 := Nat.le_of_dvd hn0 hdn
      have h2 := Nat.pos_of_dvd_of_pos hdn hn0
      exact ⟨⟨⟨hn0, hnN⟩, hdn⟩, h2, by omega⟩
    · rintro ⟨⟨⟨hn0, hnN⟩, hdn⟩, -, -⟩
      exact ⟨⟨hn0, hnN⟩, hdn, by omega⟩
  unfold cF hH
  simp only [Finset.sum_div]
  rw [Finset.sum_comm' hcond]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd0 : 0 < d := (Finset.mem_Ioc.mp hd).1
  have himg : (Finset.Ioc 0 N).filter (d ∣ ·) = (Finset.Ioc 0 (N / d)).image (fun a => d * a) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, ⟨a, rfl⟩⟩
      refine ⟨a, ⟨?_, ?_⟩, rfl⟩
      · rcases Nat.eq_zero_or_pos a with h | h
        · subst h
          simp at h1
        · exact h
      · exact (Nat.le_div_iff_mul_le hd0).mpr (by rw [mul_comm]; exact h2)
    · rintro ⟨a, ⟨h1, h2⟩, rfl⟩
      refine ⟨⟨Nat.mul_pos hd0 h1, ?_⟩, dvd_mul_right d a⟩
      have h3 := (Nat.le_div_iff_mul_le hd0).mp h2
      rw [mul_comm]
      exact h3
  rw [himg, Finset.sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hd0 h)]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  have ha0 : (a : ℂ) ≠ 0 := by
    have h1 := (Finset.mem_Ioc.mp ha).1
    exact_mod_cast h1.ne'
  have hd0' : (d : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
  field_simp

theorem cF_split (N U : ℕ) (hUN : U ≤ N) :
    cF χ N = ∑ b ∈ Ioc 0 U, χ (b : ZMod q) / (b : ℂ) * (hH (N / b) : ℂ) +
      ∑ a ∈ Ioc 0 N, ((a : ℂ))⁻¹ * ∑ b ∈ Ioc U (N / a), χ (b : ZMod q) / (b : ℂ) := by
  rw [cF_eq, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le U) hUN]
  congr 1
  have hcond : ∀ (b a : ℕ), b ∈ Finset.Ioc U N ∧ a ∈ Finset.Ioc 0 (N / b) ↔
      b ∈ Finset.Ioc U (N / a) ∧ a ∈ Finset.Ioc 0 N := by
    intro b a
    simp only [Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨hUb, hbN⟩, ha0, haN⟩
      have hb0 : 0 < b := by omega
      have h1 : a * b ≤ N := (Nat.le_div_iff_mul_le hb0).mp haN
      refine ⟨⟨hUb, (Nat.le_div_iff_mul_le ha0).mpr (by linarith)⟩, ha0, ?_⟩
      exact le_trans (Nat.le_mul_of_pos_right a hb0) h1
    · rintro ⟨⟨hUb, hbNa⟩, ha0, haN⟩
      have h1 : b * a ≤ N := (Nat.le_div_iff_mul_le ha0).mp hbNa
      have hb0 : 0 < b := by omega
      exact ⟨⟨hUb, le_trans (Nat.le_mul_of_pos_right b ha0) h1⟩, ha0,
        (Nat.le_div_iff_mul_le hb0).mpr (by linarith)⟩
  unfold hH
  push_cast
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm' hcond]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

end Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp
end
end

open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

theorem charSum_le (hχ : χ ≠ 1) (m : ℕ) : ‖∑ n ∈ Ioc 0 m, χ (n : ZMod q)‖ ≤ (q : ℝ) + 1 := by
  have e : Icc 1 m = Ioc 0 m := by ext x; simp; omega
  have := Formalism.ZeroFreeDirichlet.norm_character_sum_Icc_le χ hχ m
  rwa [e] at this

theorem cS_approx (hχ : χ ≠ 1) (N : ℕ) (hN : 1 ≤ N) :
    ‖DirichletCharacter.LFunction χ 1 - cS χ N‖ ≤ 4 * ((q : ℝ) + 1) / N := by
  have h := Formalism.FX.l_function_partial_sum q χ hχ ((q : ℝ) + 1) (Formalism.ZeroFreeDirichlet.norm_character_sum_Icc_le χ hχ)
    1 (by simp) N hN
  have e : Icc 1 N = Ioc 0 N := by ext x; simp; omega
  have e2 : ∑ n ∈ Icc 1 N, χ (n : ZMod q) * (n : ℂ) ^ (-(1 : ℂ)) = cS χ N := by
    rw [e, cS]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Complex.cpow_neg_one, div_eq_mul_inv]
  rw [e2] at h
  have e3 : (N : ℝ) ^ (-(1 : ℂ).re) = (N : ℝ)⁻¹ := by simp [Real.rpow_neg_one]
  rw [e3] at h
  simp only [norm_one, Complex.one_re, div_one] at h
  calc _ ≤ 2 * ((q : ℝ) + 1) * (1 + 1) * (N : ℝ)⁻¹ := h
    _ = 4 * ((q : ℝ) + 1) / N := by ring

theorem abel_identity (c : ℕ → ℂ) (w : ℕ → ℝ) (U : ℕ) : ∀ V, U ≤ V →
    ∑ n ∈ Ioc U V, c n * (w n : ℂ) =
      (∑ n ∈ Ioc 0 V, c n) * (w (V + 1) : ℂ) - (∑ n ∈ Ioc 0 U, c n) * (w (U + 1) : ℂ) +
        ∑ n ∈ Ioc U V, (∑ k ∈ Ioc 0 n, c k) * ((w n - w (n + 1) : ℝ) : ℂ) := by
  intro V hV
  induction V, hV using Nat.le_induction with
  | base => simp
  | succ V hUV ih =>
    rw [Finset.sum_Ioc_succ_top hUV, ih, Finset.sum_Ioc_succ_top hUV,
      Finset.sum_Ioc_succ_top (Nat.zero_le V)]
    push_cast
    ring

theorem tele (w : ℕ → ℝ) (U : ℕ) : ∀ V, U ≤ V →
    ∑ n ∈ Ioc U V, (w n - w (n + 1)) = w (U + 1) - w (V + 1) := by
  intro V hV
  induction V, hV using Nat.le_induction with
  | base => simp
  | succ V hUV ih => rw [Finset.sum_Ioc_succ_top hUV, ih]; ring

theorem abel_bound (c : ℕ → ℂ) (w : ℕ → ℝ) (B : ℝ) (hA : ∀ m, ‖∑ n ∈ Ioc 0 m, c n‖ ≤ B)
    (U V : ℕ) (hUV : U ≤ V) (hw0 : 0 ≤ w (U + 1))
    (hw : ∀ n, U < n → 0 ≤ w (n + 1) ∧ w (n + 1) ≤ w n) :
    ‖∑ n ∈ Ioc U V, c n * (w n : ℂ)‖ ≤ 2 * B * w (U + 1) := by
  rw [abel_identity c w U V hUV]
  have hV : 0 ≤ w (V + 1) := by
    rcases hUV.lt_or_eq with h | h
    · exact (hw V h).1
    · rw [← h]; exact hw0
  have h1 : ‖(∑ n ∈ Ioc 0 V, c n) * (w (V + 1) : ℂ)‖ ≤ B * w (V + 1) := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hV]
    exact mul_le_mul_of_nonneg_right (hA V) hV
  have h2 : ‖(∑ n ∈ Ioc 0 U, c n) * (w (U + 1) : ℂ)‖ ≤ B * w (U + 1) := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hw0]
    exact mul_le_mul_of_nonneg_right (hA U) hw0
  have h3 : ‖∑ n ∈ Ioc U V, (∑ k ∈ Ioc 0 n, c k) * ((w n - w (n + 1) : ℝ) : ℂ)‖ ≤
      B * (w (U + 1) - w (V + 1)) := by
    calc _ ≤ ∑ n ∈ Ioc U V, ‖(∑ k ∈ Ioc 0 n, c k) * ((w n - w (n + 1) : ℝ) : ℂ)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ n ∈ Ioc U V, B * (w n - w (n + 1)) := by
        refine Finset.sum_le_sum fun n hn => ?_
        have hn' : U < n := (Finset.mem_Ioc.mp hn).1
        have hd : 0 ≤ w n - w (n + 1) := by linarith [(hw n hn').2]
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hd]
        exact mul_le_mul_of_nonneg_right (hA n) hd
      _ = B * (w (U + 1) - w (V + 1)) := by rw [← Finset.mul_sum, tele w U V hUV]
  have h4 := norm_add_le ((∑ n ∈ Ioc 0 V, c n) * (w (V + 1) : ℂ) - (∑ n ∈ Ioc 0 U, c n) * (w (U + 1) : ℂ))
    (∑ n ∈ Ioc U V, (∑ k ∈ Ioc 0 n, c k) * ((w n - w (n + 1) : ℝ) : ℂ))
  have h5 := norm_sub_le ((∑ n ∈ Ioc 0 V, c n) * (w (V + 1) : ℂ)) ((∑ n ∈ Ioc 0 U, c n) * (w (U + 1) : ℂ))
  linarith

def lw (n : ℕ) : ℝ := Real.log n / n

theorem lw_nonneg (n : ℕ) : 0 ≤ lw n :=
  div_nonneg (Real.log_natCast_nonneg n) (Nat.cast_nonneg n)

theorem lw_anti (n : ℕ) (hn : 3 ≤ n) : 0 ≤ lw (n + 1) ∧ lw (n + 1) ≤ lw n := by
  refine ⟨lw_nonneg _, ?_⟩
  have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have he : Real.exp 1 ≤ (n : ℝ) := by
    have := Real.exp_one_lt_d9; linarith
  unfold lw
  push_cast
  exact Real.log_div_self_antitoneOn (Set.mem_Ici.mpr he) (Set.mem_Ici.mpr (by linarith)) (by linarith)

theorem cT_sub (U V : ℕ) (hUV : U ≤ V) :
    cT χ V - cT χ U = ∑ n ∈ Ioc U V, χ (n : ZMod q) * (lw n : ℂ) := by
  rw [cT, cT, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le U) hUV, add_sub_cancel_left]
  refine Finset.sum_congr rfl fun n _ => ?_
  unfold lw; push_cast; ring

theorem cT_diff2 (hχ : χ ≠ 1) (U V : ℕ) (hU : 2 ≤ U) (hUV : U ≤ V) :
    ‖cT χ V - cT χ U‖ ≤ 2 * ((q : ℝ) + 1) * lw (U + 1) := by
  rw [cT_sub χ U V hUV]
  exact abel_bound (fun n => χ (n : ZMod q)) lw _ (charSum_le χ hχ) U V hUV (lw_nonneg _)
    (fun n hn => lw_anti n (by omega))

theorem cT_diff (hχ : χ ≠ 1) (U V : ℕ) (hU : 1 ≤ U) (hUV : U ≤ V) :
    ‖cT χ V - cT χ U‖ ≤ 4 * ((q : ℝ) + 1) * ((1 + Real.log ((U : ℝ) + 1)) / ((U : ℝ) + 1)) := by
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hU0 : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hlU : 0 ≤ Real.log ((U : ℝ) + 1) := Real.log_nonneg (by linarith)
  rcases (show 2 ≤ U ∨ U = 1 by omega) with h2 | h1
  · have h := cT_diff2 χ hχ U V h2 hUV
    have e : lw (U + 1) = Real.log ((U : ℝ) + 1) / ((U : ℝ) + 1) := by unfold lw; push_cast; rfl
    rw [e] at h
    have : Real.log ((U : ℝ) + 1) / ((U : ℝ) + 1) ≤ (1 + Real.log ((U : ℝ) + 1)) / ((U : ℝ) + 1) :=
      div_le_div_of_nonneg_right (by linarith) (by linarith)
    have hy : 0 ≤ (1 + Real.log ((U : ℝ) + 1)) / ((U : ℝ) + 1) := by positivity
    calc _ ≤ _ := h
      _ ≤ 2 * ((q : ℝ) + 1) * ((1 + Real.log ((U : ℝ) + 1)) / ((U : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ ≤ _ := by nlinarith
  · subst h1
    rcases (show V = 1 ∨ 2 ≤ V by omega) with hv | hv
    · subst hv; simp only [sub_self, norm_zero]; positivity
    · have hA := cT_diff2 χ hχ 2 V le_rfl hv
      have hB : ‖cT χ 2 - cT χ 1‖ ≤ 1 / 2 := by
        rw [cT_sub χ 1 2 (by norm_num)]
        have e : Ioc 1 2 = {2} := by decide
        rw [e, Finset.sum_singleton]
        rw [norm_mul, Complex.norm_real]
        have hc : ‖χ ((2 : ℕ) : ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
        have hl : ‖lw 2‖ ≤ 1 / 2 := by
          rw [Real.norm_of_nonneg (lw_nonneg 2)]
          unfold lw; push_cast
          have := Real.log_two_lt_d9
          rw [div_le_div_iff₀ (by norm_num) (by norm_num)]; linarith
        calc _ ≤ 1 * (1 / 2 : ℝ) := mul_le_mul hc hl (norm_nonneg _) (by norm_num)
          _ = 1 / 2 := by ring
      have hl3 : lw 3 ≤ 2 / 3 := by
        unfold lw; push_cast
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
        rw [div_le_div_iff₀ (by norm_num) (by norm_num)]; linarith
      have hsplit : cT χ V - cT χ 1 = (cT χ V - cT χ 2) + (cT χ 2 - cT χ 1) := by ring
      rw [hsplit]
      have hl2 : 0 ≤ Real.log ((1 : ℕ) + (1 : ℝ)) := Real.log_nonneg (by norm_num)
      have : (1 : ℝ) ≤ (1 + Real.log ((1 : ℕ) + (1 : ℝ))) / ((1 : ℕ) + (1 : ℝ)) * 2 := by
        push_cast; push_cast at hl2
        rw [div_mul_eq_mul_div, le_div_iff₀ (by norm_num)]; linarith
      calc _ ≤ ‖cT χ V - cT χ 2‖ + ‖cT χ 2 - cT χ 1‖ := norm_add_le _ _
        _ ≤ 2 * ((q : ℝ) + 1) * (2 / 3) + 1 / 2 := by
          have : 2 * ((q : ℝ) + 1) * lw (2 + 1) ≤ 2 * ((q : ℝ) + 1) * (2 / 3) :=
            mul_le_mul_of_nonneg_left hl3 (by positivity)
          linarith
        _ ≤ _ := by nlinarith

end Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp
end
end

open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

private theorem hH_eq_harmonic' (k : ℕ) : hH k = ((harmonic k : ℚ) : ℝ) := by
  unfold hH
  rw [harmonic_eq_sum_Icc,
    show Finset.Ioc 0 k = Finset.Icc 1 k by
      ext a
      simp only [Finset.mem_Ioc, Finset.mem_Icc]
      omega]
  push_cast
  rfl

theorem term_bound (N U b : ℕ) (hb : 1 ≤ b) (hbU : b ≤ U) (hUN : U * U ≤ N) :
    |hH (N / b) - (Real.log N + Real.eulerMascheroniConstant - Real.log b)| ≤ 2 * b / N := by
  have hbpos : 0 < b := by omega
  have hbb : b * b ≤ N := le_trans (Nat.mul_le_mul hbU hbU) hUN
  have hk1 : 1 ≤ N / b := by
    rw [Nat.le_div_iff_mul_le hbpos]
    nlinarith
  have hdm := Nat.div_add_mod N b
  have hml := Nat.mod_lt N hbpos
  have hkb : N / b * b ≤ N := Nat.div_mul_le_self N b
  have hNlt : N < (N / b + 1) * b := by nlinarith
  have hk0 : N / b ≠ 0 := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by nlinarith)
  have hkR : (1 : ℝ) ≤ ((N / b : ℕ) : ℝ) := by exact_mod_cast hk1
  have hbR : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hkbR : ((N / b : ℕ) : ℝ) * b ≤ N := by exact_mod_cast hkb
  have hNltR : (N : ℝ) < (((N / b : ℕ) : ℝ) + 1) * b := by exact_mod_cast hNlt
  have hHk : hH (N / b) = ((harmonic (N / b) : ℚ) : ℝ) := hH_eq_harmonic' (N / b)
  have hA1 := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' (N / b)
  have hA2 := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant (N / b)
  simp only [Real.eulerMascheroniSeq', Real.eulerMascheroniSeq, hk0, if_false] at hA1 hA2
  rw [← hHk] at hA1 hA2
  set K : ℝ := ((N / b : ℕ) : ℝ) with hK
  have hlog1 : Real.log (K + 1) - Real.log K ≤ 1 / K := by
    rw [← Real.log_div (by positivity) (by positivity), add_div, div_self (by positivity)]
    have h := Real.log_le_sub_one_of_pos (show 0 < 1 + 1 / K by positivity)
    linarith
  have hlogB1 : Real.log K + Real.log b - Real.log N ≤ 0 := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    linarith [Real.log_le_log (by positivity) hkbR]
  have hlogB2 : -(1 / K) ≤ Real.log K + Real.log b - Real.log N := by
    have h1 : Real.log N < Real.log ((K + 1) * b) := Real.log_lt_log hN0 hNltR
    rw [Real.log_mul (by positivity) (by positivity)] at h1
    linarith
  have hfin : 1 / K ≤ 2 * b / N := by
    rw [le_div_iff₀ hN0, div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
    nlinarith
  rw [abs_le]
  constructor <;> linarith

theorem cF_main (hχ : χ ≠ 1) (N U : ℕ) (hU : 1 ≤ U) (hUN : U * U ≤ N) :
    ‖cF χ N - (((Real.log N + Real.eulerMascheroniConstant : ℝ) : ℂ) * cS χ U - cT χ U)‖ ≤
      2 * U / N + 8 * ((q : ℝ) + 1) * (1 + Real.log N) / U := by
  have hUle : U ≤ N := le_trans (Nat.le_mul_of_pos_left U (by omega)) hUN
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hU0 : (0 : ℝ) < U := by exact_mod_cast hU
  rw [cF_split χ N U hUle]
  have hX : (((Real.log N + Real.eulerMascheroniConstant : ℝ) : ℂ) * cS χ U - cT χ U) =
      ∑ b ∈ Ioc 0 U, χ (b : ZMod q) / (b : ℂ) *
        (((Real.log N + Real.eulerMascheroniConstant - Real.log b : ℝ)) : ℂ) := by
    unfold cS cT
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    push_cast
    ring
  rw [hX]
  have hre : ∀ A B C : ℂ, A + B - C = (A - C) + B := fun A B C => by ring
  rw [hre, ← Finset.sum_sub_distrib]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (norm_sum_le _ _).trans ?_
    calc ∑ b ∈ Ioc 0 U, ‖χ (b : ZMod q) / (b : ℂ) * (hH (N / b) : ℂ) - χ (b : ZMod q) / (b : ℂ) *
          (((Real.log N + Real.eulerMascheroniConstant - Real.log b : ℝ)) : ℂ)‖
        ≤ ∑ b ∈ Ioc 0 U, 2 / (N : ℝ) := by
          apply Finset.sum_le_sum
          intro b hb
          rw [Finset.mem_Ioc] at hb
          have hb0 : (0 : ℝ) < b := by exact_mod_cast hb.1
          rw [← mul_sub, norm_mul, norm_div, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
            Complex.norm_natCast]
          have h1 := term_bound N U b hb.1 hb.2 hUN
          have h2 : ‖χ (b : ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
          calc ‖χ (b : ZMod q)‖ / b * |hH (N / b) - (Real.log N + Real.eulerMascheroniConstant - Real.log b)|
              ≤ 1 / b * (2 * b / N) := by gcongr
            _ = 2 / N := by field_simp
      _ = 2 * U / N := by simp; ring
  · have htail : ∀ a ∈ Ioc 0 N, ‖∑ b ∈ Ioc U (N / a), χ (b : ZMod q) / (b : ℂ)‖ ≤ 8 * ((q : ℝ) + 1) / U := by
      intro a ha
      by_cases hM : N / a ≤ U
      · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty, norm_zero]
        positivity
      · push_neg at hM
        have hsplit : ∑ b ∈ Ioc U (N / a), χ (b : ZMod q) / (b : ℂ) = cS χ (N / a) - cS χ U := by
          unfold cS
          rw [← Finset.sum_Ioc_consecutive _ (Nat.zero_le U) hM.le]
          ring
        rw [hsplit]
        have h1 := cS_approx χ hχ U hU
        have h2 := cS_approx χ hχ (N / a) (by omega)
        have hMR : (U : ℝ) ≤ ((N / a : ℕ) : ℝ) := by exact_mod_cast hM.le
        have h3 : 4 * ((q : ℝ) + 1) / ((N / a : ℕ) : ℝ) ≤ 4 * ((q : ℝ) + 1) / U :=
          div_le_div_of_nonneg_left (by positivity) hU0 hMR
        calc ‖cS χ (N / a) - cS χ U‖ = ‖(DirichletCharacter.LFunction χ 1 - cS χ U) -
              (DirichletCharacter.LFunction χ 1 - cS χ (N / a))‖ := by
              congr 1
              ring
          _ ≤ ‖DirichletCharacter.LFunction χ 1 - cS χ U‖ +
              ‖DirichletCharacter.LFunction χ 1 - cS χ (N / a)‖ := norm_sub_le _ _
          _ ≤ 4 * ((q : ℝ) + 1) / U + 4 * ((q : ℝ) + 1) / U := add_le_add h1 (h2.trans h3)
          _ = 8 * ((q : ℝ) + 1) / U := by ring
    refine (norm_sum_le _ _).trans ?_
    calc ∑ a ∈ Ioc 0 N, ‖((a : ℂ))⁻¹ * ∑ b ∈ Ioc U (N / a), χ (b : ZMod q) / (b : ℂ)‖
        ≤ ∑ a ∈ Ioc 0 N, ((a : ℝ))⁻¹ * (8 * ((q : ℝ) + 1) / U) := by
          apply Finset.sum_le_sum
          intro a ha
          rw [norm_mul, norm_inv, Complex.norm_natCast]
          exact mul_le_mul_of_nonneg_left (htail a ha) (by positivity)
      _ = hH N * (8 * ((q : ℝ) + 1) / U) := by rw [hH, Finset.sum_mul]
      _ ≤ (1 + Real.log N) * (8 * ((q : ℝ) + 1) / U) := by
          have hh : hH N ≤ 1 + Real.log N := by
            rw [hH_eq_harmonic']
            exact harmonic_le_one_add_log N
          exact mul_le_mul_of_nonneg_right hh (by positivity)
      _ = 8 * ((q : ℝ) + 1) * (1 + Real.log N) / U := by ring

theorem cF_approx (hχ : χ ≠ 1) (N : ℕ) (hN : 1 ≤ N) :
    ‖cF χ N - (((Real.log N + Real.eulerMascheroniConstant : ℝ) : ℂ) *
        DirichletCharacter.LFunction χ 1 - cT χ (Nat.sqrt N))‖ ≤
      26 * ((q : ℝ) + 1) * (Real.log N + 1) / √(N : ℝ) := by
  have hU : 1 ≤ Nat.sqrt N := Nat.le_sqrt.2 (by omega)
  have hUN : Nat.sqrt N * Nat.sqrt N ≤ N := Nat.sqrt_le N
  have hlt : N < (Nat.sqrt N + 1) * (Nat.sqrt N + 1) := Nat.lt_succ_sqrt N
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hUR : (1 : ℝ) ≤ (Nat.sqrt N : ℝ) := by exact_mod_cast hU
  have hs0 : 0 < √(N : ℝ) := Real.sqrt_pos.2 hNR
  have hsq : √(N : ℝ) < (Nat.sqrt N : ℝ) + 1 := by
    have h := Real.sqrt_lt_sqrt (by positivity)
      (show (N : ℝ) < ((Nat.sqrt N : ℝ) + 1) * ((Nat.sqrt N : ℝ) + 1) by exact_mod_cast hlt)
    rwa [Real.sqrt_mul_self (by positivity)] at h
  have hsq2 : (Nat.sqrt N : ℝ) ≤ √(N : ℝ) := by
    have h := Real.sqrt_le_sqrt (show ((Nat.sqrt N : ℝ) * (Nat.sqrt N : ℝ)) ≤ N by exact_mod_cast hUN)
    rwa [Real.sqrt_mul_self (by positivity)] at h
  have hL0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hγ0 : 0 ≤ Real.eulerMascheroniConstant := by
    linarith [Real.one_half_lt_eulerMascheroniConstant]
  have hγ1 : Real.eulerMascheroniConstant ≤ 1 := by
    linarith [Real.eulerMascheroniConstant_lt_two_thirds]
  have hc : 0 ≤ Real.log N + Real.eulerMascheroniConstant := by linarith
  have h1 := cF_main χ hχ N (Nat.sqrt N) hU hUN
  have h2 := cS_approx χ hχ (Nat.sqrt N) hU
  have hdec : cF χ N - (((Real.log N + Real.eulerMascheroniConstant : ℝ) : ℂ) *
        DirichletCharacter.LFunction χ 1 - cT χ (Nat.sqrt N)) =
      (cF χ N - (((Real.log N + Real.eulerMascheroniConstant : ℝ) : ℂ) * cS χ (Nat.sqrt N) - cT χ (Nat.sqrt N))) +
        ((Real.log N + Real.eulerMascheroniConstant : ℝ) : ℂ) * (cS χ (Nat.sqrt N) - DirichletCharacter.LFunction χ 1) := by
    ring
  rw [hdec]
  have hw : 1 / (Nat.sqrt N : ℝ) ≤ 2 * (1 / √(N : ℝ)) := by
    have h := one_div_le_one_div_of_le hs0 (show √(N : ℝ) ≤ 2 * (Nat.sqrt N : ℝ) by linarith)
    calc 1 / (Nat.sqrt N : ℝ) = 2 * (1 / (2 * (Nat.sqrt N : ℝ))) := by field_simp
      _ ≤ 2 * (1 / √(N : ℝ)) := by linarith
  have hv : (Nat.sqrt N : ℝ) / N ≤ 1 / √(N : ℝ) := by
    calc (Nat.sqrt N : ℝ) / N = (Nat.sqrt N : ℝ) / (√(N : ℝ) * √(N : ℝ)) := by
          rw [Real.mul_self_sqrt hNR.le]
      _ ≤ √(N : ℝ) / (√(N : ℝ) * √(N : ℝ)) := by gcongr
      _ = 1 / √(N : ℝ) := by field_simp
  calc _ ≤ ‖cF χ N - (((Real.log N + Real.eulerMascheroniConstant : ℝ) : ℂ) * cS χ (Nat.sqrt N) -
          cT χ (Nat.sqrt N))‖ + ‖((Real.log N + Real.eulerMascheroniConstant : ℝ) : ℂ) *
          (cS χ (Nat.sqrt N) - DirichletCharacter.LFunction χ 1)‖ := norm_add_le _ _
    _ ≤ (2 * (Nat.sqrt N : ℝ) / N + 8 * ((q : ℝ) + 1) * (1 + Real.log N) / (Nat.sqrt N : ℝ)) +
          (Real.log N + Real.eulerMascheroniConstant) * (4 * ((q : ℝ) + 1) / (Nat.sqrt N : ℝ)) := by
        refine add_le_add h1 ?_
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc, norm_sub_rev]
        exact mul_le_mul_of_nonneg_left h2 hc
    _ = 2 * ((Nat.sqrt N : ℝ) / N) + (8 * ((q : ℝ) + 1) * (1 + Real.log N) +
          4 * ((q : ℝ) + 1) * (Real.log N + Real.eulerMascheroniConstant)) * (1 / (Nat.sqrt N : ℝ)) := by
        ring
    _ ≤ 2 * (1 / √(N : ℝ)) + (8 * ((q : ℝ) + 1) * (1 + Real.log N) +
          4 * ((q : ℝ) + 1) * (Real.log N + Real.eulerMascheroniConstant)) * (2 * (1 / √(N : ℝ))) := by
        gcongr
    _ ≤ 26 * ((q : ℝ) + 1) * (Real.log N + 1) * (1 / √(N : ℝ)) := by
        have hZ : 0 ≤ 1 / √(N : ℝ) := by positivity
        have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
        have a3 : ((q : ℝ) + 1) * (1 / √(N : ℝ)) * Real.eulerMascheroniConstant ≤
            ((q : ℝ) + 1) * (1 / √(N : ℝ)) * 1 := mul_le_mul_of_nonneg_left hγ1 (by positivity)
        have a4 : 1 * (1 / √(N : ℝ)) ≤ ((q : ℝ) + 1) * (Real.log N + 1) * (1 / √(N : ℝ)) :=
          mul_le_mul_of_nonneg_right (by nlinarith) hZ
        nlinarith
    _ = 26 * ((q : ℝ) + 1) * (Real.log N + 1) / √(N : ℝ) := by ring

end Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp
end
end

open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet

namespace Hyp

theorem g_mono (a b : ℝ) (ha : 1 ≤ a) (hab : a ≤ b) :
    (Real.log b + 1) / √b ≤ 2 * ((Real.log a + 1) / √a) := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hL : 0 ≤ Real.log a := Real.log_nonneg ha
  have hsa : 0 < √a := Real.sqrt_pos.2 ha0
  have hsb : 0 < √b := Real.sqrt_pos.2 hb0
  set s := √b / √a with hs
  have hs1 : 1 ≤ s := by
    rw [hs, le_div_iff₀ hsa, one_mul]
    exact Real.sqrt_le_sqrt hab
  have hs0 : 0 < s := by linarith
  have hsb' : √b = √a * s := by
    rw [hs]
    field_simp
  have hb' : b = a * s ^ 2 := by
    rw [hs, div_pow, Real.sq_sqrt hb0.le, Real.sq_sqrt ha0.le]
    field_simp
  have hlogb : Real.log b = Real.log a + 2 * Real.log s := by
    rw [hb', Real.log_mul ha0.ne' (by positivity), Real.log_pow]
    push_cast
    ring
  have hlogs : Real.log s ≤ s - 1 := Real.log_le_sub_one_of_pos hs0
  rw [hsb', hlogb, div_le_iff₀ (by positivity)]
  have e : 2 * ((Real.log a + 1) / √a) * (√a * s) = 2 * (Real.log a + 1) * s := by
    field_simp
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_left hs1 hL]

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

theorem diff_bound (hχ : χ ≠ 1) (N₀ N₁ : ℕ) (h0 : 1 ≤ N₀) (h01 : N₀ ≤ N₁) :
    (cF χ N₁ - cF χ N₀).re ≤ ‖DirichletCharacter.LFunction χ 1‖ * (Real.log N₁ - Real.log N₀) +
      86 * ((q : ℝ) + 1) * ((Real.log N₀ + 1) / √(N₀ : ℝ)) := by
  set L := DirichletCharacter.LFunction χ 1
  set U₀ := Nat.sqrt N₀ with hU₀
  set U₁ := Nat.sqrt N₁ with hU₁
  set B := (q : ℝ) + 1 with hBdef
  have hB : 1 ≤ B := by have := Nat.cast_nonneg (α := ℝ) q; linarith
  have hN0r : (1 : ℝ) ≤ N₀ := by exact_mod_cast h0
  have hN01r : (N₀ : ℝ) ≤ N₁ := by exact_mod_cast h01
  have hU01 : U₀ ≤ U₁ := Nat.sqrt_le_sqrt h01
  have hU0 : 1 ≤ U₀ := Nat.sqrt_pos.mpr (by omega)
  have hR1 := cF_approx χ hχ N₁ (by omega)
  have hR0 := cF_approx χ hχ N₀ h0
  have hT := cT_diff χ hχ U₀ U₁ hU0 hU01
  set R₁ := cF χ N₁ - (((Real.log N₁ + Real.eulerMascheroniConstant : ℝ) : ℂ) * L - cT χ U₁)
  set R₀ := cF χ N₀ - (((Real.log N₀ + Real.eulerMascheroniConstant : ℝ) : ℂ) * L - cT χ U₀)
  set t := Real.log N₁ - Real.log N₀ with ht
  have ht0 : 0 ≤ t := by
    have := Real.log_le_log (by linarith) hN01r; linarith
  set W := -(cT χ U₁ - cT χ U₀) + R₁ - R₀ with hW
  have eD : cF χ N₁ - cF χ N₀ = (t : ℂ) * L + W := by
    simp only [hW, R₁, R₀, ht]; push_cast; ring
  rw [eD, Complex.add_re, Complex.re_ofReal_mul]
  have hLre : L.re ≤ ‖L‖ := Complex.re_le_norm L
  have hWre : W.re ≤ ‖W‖ := Complex.re_le_norm W
  have hWn : ‖W‖ ≤ ‖cT χ U₁ - cT χ U₀‖ + ‖R₁‖ + ‖R₀‖ := by
    rw [hW]
    calc ‖-(cT χ U₁ - cT χ U₀) + R₁ - R₀‖ ≤ ‖-(cT χ U₁ - cT χ U₀) + R₁‖ + ‖R₀‖ := norm_sub_le _ _
      _ ≤ ‖-(cT χ U₁ - cT χ U₀)‖ + ‖R₁‖ + ‖R₀‖ := by gcongr; exact norm_add_le _ _
      _ = _ := by rw [norm_neg]
  have hg := g_mono (N₀ : ℝ) (N₁ : ℝ) hN0r hN01r
  set g₀ := (Real.log N₀ + 1) / √(N₀ : ℝ)
  have hg0 : 0 ≤ g₀ := div_nonneg (by linarith [Real.log_natCast_nonneg N₀]) (Real.sqrt_nonneg _)
  have hR1' : ‖R₁‖ ≤ 52 * B * g₀ := by
    have e : 26 * B * (Real.log N₁ + 1) / √(N₁ : ℝ) = 26 * B * ((Real.log N₁ + 1) / √(N₁ : ℝ)) := by ring
    rw [e] at hR1
    have := mul_le_mul_of_nonneg_left hg (by positivity : (0 : ℝ) ≤ 26 * B)
    nlinarith
  have hR0' : ‖R₀‖ ≤ 26 * B * g₀ := by
    have e : 26 * B * (Real.log N₀ + 1) / √(N₀ : ℝ) = 26 * B * g₀ := by ring
    rw [e] at hR0; exact hR0
  have hT' : ‖cT χ U₁ - cT χ U₀‖ ≤ 8 * B * g₀ := by
    have hUr : (1 : ℝ) ≤ U₀ := by exact_mod_cast hU0
    have hUN : U₀ ≤ N₀ := Nat.sqrt_le_self N₀
    have hUNr : (U₀ : ℝ) ≤ N₀ := by exact_mod_cast hUN
    have hlt : N₀ < (U₀ + 1) * (U₀ + 1) := Nat.lt_succ_sqrt N₀
    have hltr : (N₀ : ℝ) < ((U₀ : ℝ) + 1) * ((U₀ : ℝ) + 1) := by exact_mod_cast hlt
    have hsU : √(N₀ : ℝ) < (U₀ : ℝ) + 1 := by
      have := Real.sqrt_lt_sqrt (Nat.cast_nonneg N₀) hltr
      rwa [Real.sqrt_mul_self (by linarith)] at this
    have hs0 : 0 < √(N₀ : ℝ) := Real.sqrt_pos.mpr (by linarith)
    have hlog : Real.log ((U₀ : ℝ) + 1) ≤ 1 + Real.log N₀ := by
      have h1 : Real.log ((U₀ : ℝ) + 1) ≤ Real.log (2 * N₀) := Real.log_le_log (by linarith) (by linarith)
      rw [Real.log_mul (by norm_num) (by linarith)] at h1
      have := Real.log_two_lt_d9
      linarith
    have hln : 0 ≤ Real.log N₀ := Real.log_natCast_nonneg N₀
    have h2 : (1 + Real.log ((U₀ : ℝ) + 1)) / ((U₀ : ℝ) + 1) ≤ 2 * g₀ := by
      have e : 2 * g₀ = 2 * (Real.log N₀ + 1) / √(N₀ : ℝ) := by ring
      rw [e, div_le_div_iff₀ (by linarith) hs0]
      nlinarith
    have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 4 * B)
    linarith
  have hLt : t * L.re ≤ ‖L‖ * t := by nlinarith
  linarith

end Hyp

theorem deuring_heilbronn_hypergeometric : DHHyper := by
  refine ⟨400, by norm_num, ?_⟩
  intro M _ χ₁ y x hM _ hne hy hyx
  have e : ∀ N₀ N₁ : ℕ, N₀ ≤ N₁ → ∑ n ∈ Finset.Ioc N₀ N₁, (∑ d ∈ n.divisors, χ₁ (d : ZMod M)).re / (n : ℝ) =
      (Hyp.cF χ₁ N₁ - Hyp.cF χ₁ N₀).re := by
    intro N₀ N₁ h
    rw [Hyp.cF, Hyp.cF, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le N₀) h, add_sub_cancel_left,
      Complex.re_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Complex.div_natCast_re]
  have h0 : 1 ≤ ⌊y⌋₊ := Nat.le_floor (by simpa using hy)
  have h01 : ⌊y⌋₊ ≤ ⌊x⌋₊ := Nat.floor_mono hyx
  rw [e _ _ h01]
  have hd := Hyp.diff_bound χ₁ hne ⌊y⌋₊ ⌊x⌋₊ h0 h01
  set N₀ := ⌊y⌋₊ with hN₀
  set N₁ := ⌊x⌋₊ with hN₁
  set L := DirichletCharacter.LFunction χ₁ 1
  set B := (M : ℝ) + 1 with hBdef
  have hMr : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hN0y : (N₀ : ℝ) ≤ y := Nat.floor_le (by linarith)
  have hyN0 : y < N₀ + 1 := Nat.lt_floor_add_one y
  have hN1x : (N₁ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hN0r : (1 : ℝ) ≤ N₀ := by exact_mod_cast h0
  have hN01r : (N₀ : ℝ) ≤ N₁ := by exact_mod_cast h01
  have hly : 0 ≤ Real.log y := Real.log_nonneg hy

  have hlog1 : Real.log N₁ ≤ Real.log x := Real.log_le_log (by linarith) hN1x
  have hlog0 : Real.log y - Real.log N₀ ≤ 2 / y := by
    rw [← Real.log_div (by linarith) (by linarith)]
    have h := Real.log_le_sub_one_of_pos (show 0 < y / N₀ by positivity)
    have h' : y / N₀ - 1 ≤ 2 / y := by
      rw [div_sub_one (by linarith), div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith
    linarith
  have hxy : Real.log (x / y) = Real.log x - Real.log y := Real.log_div (by linarith) (by linarith)

  have hLB : ‖L‖ ≤ 5 * B := by
    have h := Hyp.cS_approx χ₁ hne 1 le_rfl
    have h1 : Hyp.cS χ₁ 1 = 1 := by simp [Hyp.cS]
    rw [h1] at h
    have := norm_sub_norm_le L 1
    simp only [norm_one, Nat.cast_one, div_one] at h this
    linarith

  have hsy : 0 < √y := Real.sqrt_pos.mpr (by linarith)
  have hs0 : 0 < √(N₀ : ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hsyN : √y ≤ 2 * √(N₀ : ℝ) := by
    have h4 : (2 * √(N₀ : ℝ)) * (2 * √(N₀ : ℝ)) = 4 * N₀ := by
      have := Real.mul_self_sqrt (Nat.cast_nonneg (α := ℝ) N₀); nlinarith
    have := Real.sqrt_le_sqrt (show y ≤ (2 * √(N₀ : ℝ)) * (2 * √(N₀ : ℝ)) by rw [h4]; linarith)
    rwa [Real.sqrt_mul_self (by positivity)] at this
  have hlN0 : Real.log N₀ ≤ Real.log y := Real.log_le_log (by linarith) hN0y
  set Y := (Real.log y + 1) / √y with hY
  have hY0 : 0 ≤ Y := by positivity
  have hg0 : (Real.log N₀ + 1) / √(N₀ : ℝ) ≤ 2 * Y := by
    have e2 : 2 * Y = 2 * (Real.log y + 1) / √y := by ring
    rw [e2, div_le_div_iff₀ hs0 hsy]
    have hln : 0 ≤ Real.log N₀ := Real.log_natCast_nonneg N₀
    nlinarith
  have hyY : 2 / y ≤ 2 * Y := by
    have hsyy : √y ≤ y := by
      have := Real.sqrt_le_sqrt (show y ≤ y * y by nlinarith)
      rwa [Real.sqrt_mul_self (by linarith)] at this
    have e2 : 2 * Y = 2 * (Real.log y + 1) / √y := by ring
    rw [e2, div_le_div_iff₀ (by linarith) hsy]
    nlinarith
  have hLn : 0 ≤ ‖L‖ := norm_nonneg _
  have i1 : ‖L‖ * (Real.log N₁ - Real.log N₀) ≤ ‖L‖ * Real.log (x / y) + ‖L‖ * (2 / y) := by
    rw [hxy, ← mul_add]; exact mul_le_mul_of_nonneg_left (by linarith) hLn
  have i2 : ‖L‖ * (2 / y) ≤ 5 * B * (2 * Y) := mul_le_mul hLB hyY (by positivity) (by positivity)
  have i3 : 86 * B * ((Real.log N₀ + 1) / √(N₀ : ℝ)) ≤ 86 * B * (2 * Y) :=
    mul_le_mul_of_nonneg_left hg0 (by positivity)
  have e3 : 400 * (M : ℝ) * (Real.log y + 1) / √y = 400 * M * Y := by rw [hY]; ring
  rw [e3]
  have hB2 : B ≤ 2 * M := by rw [hBdef]; linarith
  have i4 : 5 * B * (2 * Y) + 86 * B * (2 * Y) ≤ 400 * M * Y := by nlinarith
  linarith

end Formalism.HermitianLattices.Ext.PrimesInProgressions
