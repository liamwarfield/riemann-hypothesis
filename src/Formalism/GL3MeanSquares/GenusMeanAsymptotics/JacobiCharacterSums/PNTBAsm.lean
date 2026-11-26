module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHSt

@[expose] public section

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTBAsmB
open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet

def excI {M : ℕ} (e : Option (DirichletCharacter ℂ M × ℝ)) (χ : DirichletCharacter ℂ M) : ℝ :=
  match e with
  | none => 0
  | some (χ₁, _) => if χ = χ₁ then 1 else 0

def excT {M : ℕ} (e : Option (DirichletCharacter ℂ M × ℝ)) (χ : DirichletCharacter ℂ M) (y : ℝ) : ℂ :=
  match e with
  | none => 0
  | some (χ₁, β₁) => if χ = χ₁ then (y : ℂ) ^ (β₁ : ℂ) / (β₁ : ℂ) else 0

theorem mainPsi_eq {M : ℕ} (e : Option (DirichletCharacter ℂ M × ℝ)) (χ : DirichletCharacter ℂ M) (y : ℝ) :
    mainPsi e χ y = (if χ = 1 then (y : ℂ) else 0) - excT e χ y := rfl

theorem sum_excI_le {M : ℕ} [NeZero M] (e : Option (DirichletCharacter ℂ M × ℝ)) :
    ∑ χ : DirichletCharacter ℂ M, excI e χ ≤ 1 := by
  rcases e with _ | ⟨χ₁, β₁⟩
  · simp [excI]
  · have h : (∑ χ : DirichletCharacter ℂ M, excI (some (χ₁, β₁)) χ) = excI (some (χ₁, β₁)) χ₁ :=
      Finset.sum_eq_single χ₁ (fun b _ hb => if_neg hb) (fun h => absurd (Finset.mem_univ _) h)
    rw [h]
    exact (if_pos rfl).le

theorem excW_le_one {M : ℕ} (e : Option (DirichletCharacter ℂ M × ℝ)) (χ : DirichletCharacter ℂ M) (ρ : ℂ) :
    excW e χ ρ ≤ 1 := by
  rcases e with _ | ⟨χ₁, β₁⟩
  · simp [excW]
  · simp only [excW]; split_ifs <;> norm_num

theorem card_char_le (M : ℕ) [NeZero M] :
    ((Finset.univ : Finset (DirichletCharacter ℂ M)).card : ℝ) ≤ M := by
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card,
    DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ M]
  exact_mod_cast Nat.totient_le M

theorem sum_excW_le {M : ℕ} (e : Option (DirichletCharacter ℂ M × ℝ)) (χ : DirichletCharacter ℂ M)
    (Z : Finset ℂ) (y : ℝ) (hy : 1 ≤ y) (hZ : ∀ ρ ∈ Z, ρ.re < 1) :
    ∑ ρ ∈ Z, (excW e χ ρ : ℝ) * y ^ (ρ.re - 1) ≤ excI e χ := by
  rcases e with _ | ⟨χ₁, β₁⟩
  · simp [excW, excI]
  · simp only [excW, excI]
    by_cases h : χ = χ₁
    · simp only [h, true_and, if_true]
      have : ∀ ρ ∈ Z, (((if ρ = (β₁ : ℂ) then 1 else 0 : ℕ) : ℝ)) * y ^ (ρ.re - 1)
          = if ρ = (β₁ : ℂ) then y ^ (ρ.re - 1) else 0 := by
        intro ρ _; split_ifs <;> simp
      rw [Finset.sum_congr rfl this, Finset.sum_ite_eq']
      split_ifs with hm
      · exact Real.rpow_le_one_of_one_le_of_nonpos hy (by linarith [hZ _ hm])
      · norm_num
    · simp [h]

theorem excT_sub_le {M : ℕ} [NeZero M] (hM : 3 ≤ M) (e : Option (DirichletCharacter ℂ M × ℝ))
    (he : ∀ p, e = some p → IsExcPair p.1 p.2) (χ : DirichletCharacter ℂ M)
    (Z : Finset ℂ) (y κ T : ℝ) (hy : 1 ≤ y) (hT : 0 ≤ T)
    (hZ : ∀ ρ : ℂ, IsLZero χ ρ → 1 - κ / 2 ≤ ρ.re → |ρ.im| ≤ T → ρ ∈ Z) :
    ‖excT e χ y - ∑ ρ ∈ Z, (excW e χ ρ : ℂ) * (y : ℂ) ^ ρ / ρ‖ ≤ excI e χ * (2 * y * y ^ (-(κ / 2))) := by
  rcases e with _ | ⟨χ₁, β₁⟩
  · simp [excW, excI, excT]
  · obtain ⟨-, hne, hz, hlo, hhi⟩ := he _ rfl
    simp only at hne hz hlo hhi
    simp only [excW, excI, excT]
    by_cases h : χ = χ₁
    · subst h
      simp only [true_and, if_true]
      have : ∀ ρ ∈ Z, (((if ρ = (β₁ : ℂ) then 1 else 0 : ℕ) : ℂ)) * (y : ℂ) ^ ρ / ρ
          = if ρ = (β₁ : ℂ) then (y : ℂ) ^ ρ / ρ else 0 := by
        intro ρ _; split_ifs <;> simp
      rw [Finset.sum_congr rfl this, Finset.sum_ite_eq']
      have hy0 : 0 < y := by linarith
      split_ifs with hm
      · simp only [sub_self, norm_zero, one_mul]; positivity
      · have hb : β₁ < 1 - κ / 2 := by
          by_contra hcon
          push Not at hcon
          exact hm (hZ _ ⟨Or.inl hne, hz⟩ (by simpa using hcon) (by simpa using hT))
        have hl : 1 ≤ Real.log M := by
          rw [Real.le_log_iff_exp_le (by positivity)]
          have : (3 : ℝ) ≤ M := by exact_mod_cast hM
          linarith [Real.exp_one_lt_d9]
        have hb2 : 1 / 2 ≤ β₁ := by
          have : 1 / (8 * Real.log M) ≤ 1 / 8 := by
            apply one_div_le_one_div_of_le (by norm_num); linarith
          linarith
        rw [sub_zero, one_mul, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy0, Complex.ofReal_re,
          Complex.norm_real, Real.norm_of_nonneg (by linarith)]
        have h1 : y ^ β₁ ≤ y ^ (1 - κ / 2) := Real.rpow_le_rpow_of_exponent_le hy hb.le
        have h2 : y ^ (1 - κ / 2) = y * y ^ (-(κ / 2)) := by
          rw [sub_eq_add_neg, Real.rpow_add hy0, Real.rpow_one]
        rw [div_le_iff₀ (by linarith)]
        have h3 : 0 ≤ y * y ^ (-(κ / 2)) := by positivity
        nlinarith
    · simp [h]

theorem one_char {M : ℕ} [NeZero M] (hM : 3 ≤ M) (e : Option (DirichletCharacter ℂ M × ℝ))
    (he : ∀ p, e = some p → IsExcPair p.1 p.2) (χ : DirichletCharacter ℂ M)
    (Z : Finset ℂ) (m : ℂ → ℕ) (y κ T R : ℝ) (hy : 1 ≤ y) (hT : 0 ≤ T)
    (hZ : ∀ ρ : ℂ, IsLZero χ ρ → 1 - κ / 2 ≤ ρ.re → |ρ.im| ≤ T → ρ ∈ Z)
    (hre : ∀ ρ ∈ Z, 1 / 2 ≤ ρ.re) (hm : ∀ ρ ∈ Z, 1 ≤ m ρ)
    (hR : ‖psiChi χ y - (if χ = 1 then (y : ℂ) else 0) + ∑ ρ ∈ Z, (m ρ : ℂ) * (y : ℂ) ^ ρ / ρ‖ ≤ R) :
    ‖psiChi χ y - mainPsi e χ y‖ ≤
      R + 2 * y * ∑ ρ ∈ Z, ((m ρ : ℝ) - (excW e χ ρ : ℝ)) * y ^ (ρ.re - 1)
        + excI e χ * (2 * y * y ^ (-(κ / 2))) := by
  have hy0 : 0 < y := by linarith
  have e1 : psiChi χ y - mainPsi e χ y
      = (psiChi χ y - (if χ = 1 then (y : ℂ) else 0) + ∑ ρ ∈ Z, (m ρ : ℂ) * (y : ℂ) ^ ρ / ρ)
        - ∑ ρ ∈ Z, ((m ρ : ℂ) - (excW e χ ρ : ℂ)) * (y : ℂ) ^ ρ / ρ
        + (excT e χ y - ∑ ρ ∈ Z, (excW e χ ρ : ℂ) * (y : ℂ) ^ ρ / ρ) := by
    rw [mainPsi_eq]
    have : ∑ ρ ∈ Z, ((m ρ : ℂ) - (excW e χ ρ : ℂ)) * (y : ℂ) ^ ρ / ρ
        = ∑ ρ ∈ Z, (m ρ : ℂ) * (y : ℂ) ^ ρ / ρ - ∑ ρ ∈ Z, (excW e χ ρ : ℂ) * (y : ℂ) ^ ρ / ρ := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun ρ _ => by ring)
    rw [this]
    by_cases hχ : χ = 1
    · simp only [if_pos hχ]; ring
    · simp only [if_neg hχ]; ring
  have h2 : ‖∑ ρ ∈ Z, ((m ρ : ℂ) - (excW e χ ρ : ℂ)) * (y : ℂ) ^ ρ / ρ‖
      ≤ 2 * y * ∑ ρ ∈ Z, ((m ρ : ℝ) - (excW e χ ρ : ℝ)) * y ^ (ρ.re - 1) := by
    rw [Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
    intro ρ hρ
    have hw : (0 : ℝ) ≤ (m ρ : ℝ) - (excW e χ ρ : ℝ) := by
      have : ((excW e χ ρ : ℕ) : ℝ) ≤ (m ρ : ℝ) := by exact_mod_cast (excW_le_one e χ ρ).trans (hm ρ hρ)
      linarith
    have hn : ‖(m ρ : ℂ) - (excW e χ ρ : ℂ)‖ = (m ρ : ℝ) - (excW e χ ρ : ℝ) := by
      have : (m ρ : ℂ) - (excW e χ ρ : ℂ) = (((m ρ : ℝ) - (excW e χ ρ : ℝ) : ℝ) : ℂ) := by push_cast; rfl
      rw [this, Complex.norm_real, Real.norm_of_nonneg hw]
    have hρn : 1 / 2 ≤ ‖ρ‖ := (hre ρ hρ).trans ((le_abs_self _).trans (Complex.abs_re_le_norm ρ))
    rw [norm_div, norm_mul, hn, Complex.norm_cpow_eq_rpow_re_of_pos hy0]
    have h3 : y ^ ρ.re = y * y ^ (ρ.re - 1) := by
      rw [Real.rpow_sub hy0, Real.rpow_one]; field_simp
    rw [div_le_iff₀ (by linarith), h3]
    have h4 : 0 ≤ ((m ρ : ℝ) - (excW e χ ρ : ℝ)) * (y * y ^ (ρ.re - 1)) := by positivity
    nlinarith
  rw [e1]
  refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add hR h2)) ?_)
  exact excT_sub_le hM e he χ Z y κ T hy hT hZ

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTBAsmA
noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

theorem num_alg (M y C D Pt t lg lm : ℝ) (hM : 1 ≤ M) (hy : M ^ 5 ≤ y) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hPt : Pt ≤ (M ^ 8)⁻¹) (ht : t ≤ (M ^ 2)⁻¹) (hlg : lg ≤ D * M ^ 2)
    (hlm0 : 0 ≤ lm) (hlm : lm ≤ 13 * M) :
    M * (4 * y * (C * (Pt + lg * lm ^ 2 / M ^ 12)) / (M ^ 5)⁻¹ + 4 * ((M ^ 5)⁻¹ * y + 1) * lg)
        + 20 * (M ^ 5)⁻¹ * y + 2 * y * t ≤ (4 * C + 676 * C * D + 8 * D + 22) * y * (M ^ 2)⁻¹ := by
  have hM0 : 0 < M := by linarith
  have hy0 : 0 ≤ y := le_trans (by positivity) hy
  have hA : M ^ 6 * Pt ≤ (M ^ 2)⁻¹ := by
    calc M ^ 6 * Pt ≤ M ^ 6 * (M ^ 8)⁻¹ := mul_le_mul_of_nonneg_left hPt (by positivity)
      _ = (M ^ 2)⁻¹ := by field_simp
  have hB : lg * lm ^ 2 / M ^ 6 ≤ 169 * D * (M ^ 2)⁻¹ := by
    have hlm2 : lm ^ 2 ≤ 169 * M ^ 2 := by nlinarith
    have h2 : lg * lm ^ 2 ≤ D * M ^ 2 * (169 * M ^ 2) :=
      calc lg * lm ^ 2 ≤ D * M ^ 2 * lm ^ 2 := mul_le_mul_of_nonneg_right hlg (sq_nonneg _)
        _ ≤ D * M ^ 2 * (169 * M ^ 2) := mul_le_mul_of_nonneg_left hlm2 (by positivity)
    calc lg * lm ^ 2 / M ^ 6 ≤ D * M ^ 2 * (169 * M ^ 2) / M ^ 6 :=
          div_le_div_of_nonneg_right h2 (by positivity)
      _ = 169 * D * (M ^ 2)⁻¹ := by field_simp <;> ring
  have e1 : M * (4 * y * (C * (Pt + lg * lm ^ 2 / M ^ 12)) / (M ^ 5)⁻¹)
      = 4 * C * y * (M ^ 6 * Pt + lg * lm ^ 2 / M ^ 6) := by
    field_simp <;> ring
  have h1 : M * (4 * y * (C * (Pt + lg * lm ^ 2 / M ^ 12)) / (M ^ 5)⁻¹)
      ≤ 4 * C * y * ((M ^ 2)⁻¹ + 169 * D * (M ^ 2)⁻¹) := by
    rw [e1]; exact mul_le_mul_of_nonneg_left (add_le_add hA hB) (by positivity)
  have hM3 : M ^ 3 ≤ y * (M ^ 2)⁻¹ := by
    rw [le_mul_inv_iff₀ (by positivity)]; calc M ^ 3 * M ^ 2 = M ^ 5 := by ring
      _ ≤ y := hy
  have h2 : M * (4 * ((M ^ 5)⁻¹ * y + 1) * lg) ≤ 8 * D * y * (M ^ 2)⁻¹ := by
    have hc : 0 ≤ 4 * M * ((M ^ 5)⁻¹ * y + 1) := by positivity
    calc M * (4 * ((M ^ 5)⁻¹ * y + 1) * lg) = 4 * M * ((M ^ 5)⁻¹ * y + 1) * lg := by ring
      _ ≤ 4 * M * ((M ^ 5)⁻¹ * y + 1) * (D * M ^ 2) := mul_le_mul_of_nonneg_left hlg hc
      _ = 4 * D * (y * (M ^ 2)⁻¹ + M ^ 3) := by field_simp <;> ring
      _ ≤ 4 * D * (y * (M ^ 2)⁻¹ + y * (M ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 8 * D * y * (M ^ 2)⁻¹ := by ring
  have h5 : (M ^ 5)⁻¹ ≤ (M ^ 2)⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_right₀ hM (by norm_num))
  have h3 : 20 * (M ^ 5)⁻¹ * y ≤ 20 * (M ^ 2)⁻¹ * y := by
    have := mul_le_mul_of_nonneg_right h5 hy0; linarith
  have h4 : 2 * y * t ≤ 2 * y * (M ^ 2)⁻¹ := mul_le_mul_of_nonneg_left ht (by positivity)
  have e2 : M * (4 * y * (C * (Pt + lg * lm ^ 2 / M ^ 12)) / (M ^ 5)⁻¹ + 4 * ((M ^ 5)⁻¹ * y + 1) * lg)
      = M * (4 * y * (C * (Pt + lg * lm ^ 2 / M ^ 12)) / (M ^ 5)⁻¹)
        + M * (4 * ((M ^ 5)⁻¹ * y + 1) * lg) := by ring
  rw [e2]
  have e3 : (4 * C + 676 * C * D + 8 * D + 22) * y * (M ^ 2)⁻¹
      = 4 * C * y * ((M ^ 2)⁻¹ + 169 * D * (M ^ 2)⁻¹) + 8 * D * y * (M ^ 2)⁻¹
        + 20 * (M ^ 2)⁻¹ * y + 2 * y * (M ^ 2)⁻¹ := by ring
  rw [e3]
  linarith

theorem one_le_log_of_three_le {x : ℝ} (hx : 3 ≤ x) : 1 ≤ Real.log x := by
  have h3 : Real.exp 1 ≤ x := by linarith [Real.exp_one_lt_d9]
  calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ Real.log x := Real.log_le_log (Real.exp_pos 1) h3

theorem inv_pow_eq_exp {M : ℝ} (hM : 0 < M) (n : ℕ) : (M ^ n)⁻¹ = Real.exp (-(n * Real.log M)) := by
  rw [Real.exp_neg, ← Real.log_pow, Real.exp_log (pow_pos hM n)]

theorem logy_lt {cA M y : ℝ} (hcA : 0 < cA) (hy : 2 ≤ y)
    (h : cA * Real.sqrt (Real.log y) < Real.log M) : cA ^ 2 * Real.log y < Real.log M ^ 2 := by
  have hl : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have hs := Real.sq_sqrt hl
  have h0 : 0 ≤ cA * Real.sqrt (Real.log y) := by positivity
  have h2 : (cA * Real.sqrt (Real.log y)) ^ 2 < Real.log M ^ 2 := by nlinarith
  calc cA ^ 2 * Real.log y = (cA * Real.sqrt (Real.log y)) ^ 2 := by rw [mul_pow, hs]
    _ < Real.log M ^ 2 := h2

theorem inv_le_exp {cA c M y : ℝ} (hcA : 0 < cA) (hc : 0 < c) (hc' : c ≤ cA ^ 2) (hM : 8 ≤ M) (hy : 2 ≤ y)
    (h : cA * Real.sqrt (Real.log y) < Real.log M) :
    M⁻¹ ≤ Real.exp (-(c * Real.log y / Real.log M)) := by
  have hM0 : 0 < M := by linarith
  have hlM : 0 < Real.log M := Real.log_pos (by linarith)
  have hly : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have h2 := logy_lt hcA hy h
  have h3 : c * Real.log y ≤ Real.log M ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hc' hly]
  have h4 : c * Real.log y / Real.log M ≤ Real.log M := by
    rw [div_le_iff₀ hlM]; nlinarith
  calc M⁻¹ = Real.exp (-Real.log M) := by rw [Real.exp_neg, Real.exp_log hM0]
    _ ≤ Real.exp (-(c * Real.log y / Real.log M)) := Real.exp_le_exp.mpr (by linarith)

theorem num_main (cA κ C : ℝ) (hcA : 0 < cA) (hκ : 0 < κ) (hC : 0 < C) :
    ∃ C₀ B : ℝ, 0 ≤ C₀ ∧ 0 ≤ B ∧ ∀ M y : ℝ, 8 ≤ M → 2 ≤ y →
      C₀ * Real.log M * Real.log (Real.log M + 2) ≤ Real.log y →
      cA * Real.sqrt (Real.log y) < Real.log M →
      M * (4 * y * (C * ((M * M ^ (12 : ℝ)) ^ C * y ^ (-(κ / 2))
          + Real.log (2 * y) * Real.log (M * M ^ (12 : ℝ)) ^ 2 / M ^ (12 : ℝ))) / (M ^ 5)⁻¹
          + 4 * ((M ^ 5)⁻¹ * y + 1) * Real.log (2 * y))
        + 20 * (M ^ 5)⁻¹ * y + 2 * y * y ^ (-(κ / 2)) ≤ B * y * (M⁻¹ * M⁻¹) := by
  set D : ℝ := 1 + (cA ^ 2)⁻¹ with hDdef
  have hD : 0 ≤ D := by positivity
  refine ⟨5 + (26 * C + 20) / κ, 4 * C + 676 * C * D + 8 * D + 22, by positivity, by positivity, ?_⟩
  intro M y hM hy hlog hsq
  have hM0 : 0 < M := by linarith
  have hy0 : 0 < y := by linarith
  have hL1 : 1 ≤ Real.log M := one_le_log_of_three_le (by linarith)
  have hl1 : 1 ≤ Real.log (Real.log M + 2) := one_le_log_of_three_le (by linarith)
  have hLM : Real.log M ≤ M := by linarith [Real.log_le_sub_one_of_pos hM0]
  have hC0 : 0 ≤ 5 + (26 * C + 20) / κ := by positivity
  have hlog' : (5 + (26 * C + 20) / κ) * Real.log M ≤ Real.log y := by
    have : (5 + (26 * C + 20) / κ) * Real.log M * 1
        ≤ (5 + (26 * C + 20) / κ) * Real.log M * Real.log (Real.log M + 2) :=
      mul_le_mul_of_nonneg_left hl1 (by positivity)
    linarith
  have hkC : κ * (5 + (26 * C + 20) / κ) = 5 * κ + (26 * C + 20) := by field_simp
  have hK : (26 * C + 20) * Real.log M ≤ κ * Real.log y := by
    have := mul_le_mul_of_nonneg_left hlog' hκ.le
    have h5 : 0 ≤ 5 * κ * Real.log M := by positivity
    nlinarith
  have hy5 : M ^ 5 ≤ y := by
    rw [← Real.log_le_log_iff (by positivity) hy0, Real.log_pow]
    have : 5 * Real.log M ≤ (5 + (26 * C + 20) / κ) * Real.log M := by
      have : 0 ≤ (26 * C + 20) / κ * Real.log M := by positivity
      nlinarith
    push_cast; linarith
  have h12 : M ^ (12 : ℝ) = M ^ 12 := by
    rw [show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [h12]
  have hlm : Real.log (M * M ^ 12) = 13 * Real.log M := by
    rw [show M * M ^ 12 = M ^ 13 by ring, Real.log_pow]; push_cast; ring
  have hpow : (M * M ^ 12) ^ C = Real.exp (13 * C * Real.log M) := by
    rw [Real.rpow_def_of_pos (by positivity), hlm]; ring_nf
  have hyk : y ^ (-(κ / 2)) = Real.exp (-(κ / 2 * Real.log y)) := by
    rw [Real.rpow_def_of_pos hy0]; ring_nf
  have hPt : (M * M ^ 12) ^ C * y ^ (-(κ / 2)) ≤ (M ^ 8)⁻¹ := by
    rw [hpow, hyk, ← Real.exp_add, inv_pow_eq_exp hM0]
    apply Real.exp_le_exp.mpr
    push_cast
    nlinarith
  have ht : y ^ (-(κ / 2)) ≤ (M ^ 2)⁻¹ := by
    rw [hyk, inv_pow_eq_exp hM0]
    apply Real.exp_le_exp.mpr
    push_cast
    have : 0 ≤ 26 * C * Real.log M := by positivity
    nlinarith
  have hlg : Real.log (2 * y) ≤ D * M ^ 2 := by
    have hq := logy_lt hcA hy hsq
    have hq' : Real.log y ≤ Real.log M ^ 2 * (cA ^ 2)⁻¹ := by
      rw [le_mul_inv_iff₀ (by positivity)]; linarith
    have hLM2 : Real.log M ^ 2 ≤ M ^ 2 := by nlinarith
    have hq'' : Real.log M ^ 2 * (cA ^ 2)⁻¹ ≤ M ^ 2 * (cA ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_right hLM2 (by positivity)
    have h2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)]
    have hM1 : 1 ≤ M ^ 2 := by nlinarith
    rw [Real.log_mul (by norm_num) hy0.ne', hDdef]
    nlinarith
  have hlm0 : 0 ≤ Real.log (M * M ^ 12) := by rw [hlm]; linarith
  have hlm13 : Real.log (M * M ^ 12) ≤ 13 * M := by rw [hlm]; linarith
  have key := num_alg M y C D ((M * M ^ 12) ^ C * y ^ (-(κ / 2))) (y ^ (-(κ / 2)))
    (Real.log (2 * y)) (Real.log (M * M ^ 12)) (by linarith) hy5 hC.le hD hPt ht hlg hlm0 hlm13
  refine key.trans (le_of_eq ?_)
  ring

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet


set_option maxHeartbeats 400000 in
theorem psi_relative_far_range : PsiRelBOf := by
  intro hE hS hZS cA hcA
  obtain ⟨κ, hκ, hκ', hZ⟩ := hZS
  obtain ⟨C, hC, hEx⟩ := hE κ hκ hκ'
  obtain ⟨cz, Az, Cz, hcz, hZ⟩ := hZ C 12 (by norm_num)
  obtain ⟨C₀, B, hC₀, hB, hnum⟩ := num_main cA κ C hcA hκ hC
  obtain ⟨c₁, hc₁, heta⟩ := etaOf_lower 1 one_pos
  refine ⟨min cz (cA ^ 2), 22 * |Az| + B / c₁, max Cz C₀, lt_min hcz (by positivity), ?_⟩
  intro M _ h8 y hy hr1 hr2
  have hM8 : 8 ≤ M := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) h8
  have hM8r : (8 : ℝ) ≤ M := by exact_mod_cast hM8
  have hM3 : 3 ≤ M := by omega
  have hM0 : (0 : ℝ) < M := by linarith
  have hy0 : 0 < y := by linarith
  have hT8 : (8 : ℝ) ≤ (M : ℝ) ^ (12 : ℝ) := by
    calc (8 : ℝ) ≤ (M : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]; exact hM8r
      _ ≤ (M : ℝ) ^ (12 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hδ0 : 0 < ((M : ℝ) ^ 5)⁻¹ := by positivity
  have hδ : ((M : ℝ) ^ 5)⁻¹ ≤ 1 / 2 := by
    rw [one_div]
    apply inv_anti₀ (by norm_num)
    calc (2 : ℝ) ≤ (M : ℝ) ^ 1 := by rw [pow_one]; linarith
      _ ≤ (M : ℝ) ^ 5 := pow_le_pow_right₀ (by linarith) (by norm_num)
  choose Z m K h1 h2 h3 h4 h5 h6 using fun χ => hEx M χ ((M : ℝ) ^ (12 : ℝ)) hM3 (by linarith)
  have hl : 1 ≤ Real.log M := one_le_log_of_three_le (by linarith)
  have hll : 1 ≤ Real.log (Real.log M + 2) := one_le_log_of_three_le (by linarith)
  have hL : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have hrz : Cz * Real.log M * Real.log (Real.log M + 2) ≤ Real.log y := by
    refine le_trans ?_ hr1
    have : Cz ≤ max Cz C₀ := le_max_left _ _
    gcongr
  have hrn : C₀ * Real.log M * Real.log (Real.log M + 2) ≤ Real.log y := by
    refine le_trans ?_ hr1
    have : C₀ ≤ max Cz C₀ := le_max_right _ _
    gcongr
  have hZS := hZ M Z m h8 h1 h3 h4 h5 y hy hrz
  have hN := hnum M y hM8r hy hrn hr2
  generalize hTdef : (M : ℝ) ^ (12 : ℝ) = T at *
  generalize hδdef : ((M : ℝ) ^ 5)⁻¹ = δ at *
  generalize htdef : y ^ (-(κ / 2)) = t at *
  obtain ⟨E, hEdef⟩ : ∃ E : ℝ, E = C * (((M : ℝ) * T) ^ C * t
      + Real.log (2 * y) * Real.log ((M : ℝ) * T) ^ 2 / T) := ⟨_, rfl⟩
  rw [← hEdef] at hN
  have hT0 : 0 < T := by linarith
  have ht0 : 0 ≤ t := by rw [← htdef]; positivity
  have hlg : 0 ≤ Real.log (2 * y) := Real.log_nonneg (by linarith)
  have hE0 : 0 ≤ E := by rw [hEdef]; positivity
  have hre : ∀ χ, ∀ ρ ∈ Z χ, 1 / 2 ≤ ρ.re ∧ ρ.re < 1 := by
    intro χ ρ hρ
    obtain ⟨hz, hlo, -⟩ := h1 χ ρ hρ
    refine ⟨by linarith, ?_⟩
    by_contra hcon
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ hz.1 (not_lt.1 hcon) hz.2
  have hEu : ∀ u : ℝ, y ≤ u → u ≤ 2 * y →
      C * (((M : ℝ) * T) ^ C * u ^ (-(κ / 2)) + Real.log u * Real.log ((M : ℝ) * T) ^ 2 / T) ≤ E := by
    intro u hu1 hu2
    rw [hEdef]
    have a1 : u ^ (-(κ / 2)) ≤ t := by
      rw [← htdef]; exact Real.rpow_le_rpow_of_nonpos hy0 hu1 (by linarith)
    have a2 : Real.log u ≤ Real.log (2 * y) := Real.log_le_log (by linarith) hu2
    gcongr
  have hsharp : ∀ χ : DirichletCharacter ℂ M,
      ‖psiChi χ y - (if χ = 1 then (y : ℂ) else 0) + ∑ ρ ∈ Z χ, (m χ ρ : ℂ) * (y : ℂ) ^ ρ / ρ‖ ≤
      4 * y * E / δ + 20 * δ * y * ∑ ρ ∈ Z χ, (m χ ρ : ℝ) * y ^ (ρ.re - 1)
        + 4 * (δ * y + 1) * Real.log (2 * y) := by
    intro χ
    refine hS M χ (Z χ) (m χ) (K χ) E y δ (hre χ) hy hδ0 hδ ?_
    intro u hu
    have hu1 : y ≤ u := by
      rcases hu with rfl | rfl
      · exact le_rfl
      · nlinarith
    have hu2 : u ≤ 2 * y := by
      rcases hu with rfl | rfl
      · linarith
      · nlinarith
    exact (h6 χ u (by linarith)).trans (hEu u hu1 hu2)
  obtain ⟨W, hW⟩ : ∃ W : DirichletCharacter ℂ M → ℝ, W = fun χ =>
      ∑ ρ ∈ Z χ, ((m χ ρ : ℝ) - (excW (eOf M) χ ρ : ℝ)) * y ^ (ρ.re - 1) := ⟨_, rfl⟩
  have hW0 : ∀ χ, 0 ≤ W χ := by
    intro χ
    rw [hW]
    apply Finset.sum_nonneg
    intro ρ hρ
    have : ((excW (eOf M) χ ρ : ℕ) : ℝ) ≤ (m χ ρ : ℝ) := by
      exact_mod_cast (excW_le_one (eOf M) χ ρ).trans (h3 χ ρ hρ)
    have h0 : (0 : ℝ) ≤ (m χ ρ : ℝ) - (excW (eOf M) χ ρ : ℝ) := by linarith
    positivity
  have hmW : ∀ χ, ∑ ρ ∈ Z χ, (m χ ρ : ℝ) * y ^ (ρ.re - 1) ≤ W χ + excI (eOf M) χ := by
    intro χ
    have := sum_excW_le (eOf M) χ (Z χ) y (by linarith) (fun ρ hρ => (hre χ ρ hρ).2)
    have e : ∑ ρ ∈ Z χ, (m χ ρ : ℝ) * y ^ (ρ.re - 1)
        = W χ + ∑ ρ ∈ Z χ, (excW (eOf M) χ ρ : ℝ) * y ^ (ρ.re - 1) := by
      rw [hW, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun ρ _ => by ring)
    linarith
  have hper : ∀ χ : DirichletCharacter ℂ M, ‖psiChi χ y - mainPsi (eOf M) χ y‖ ≤
      (4 * y * E / δ + 4 * (δ * y + 1) * Real.log (2 * y)) + 22 * y * W χ
        + excI (eOf M) χ * (20 * δ * y + 2 * y * t) := by
    intro χ
    have a := one_char hM3 (eOf M) (fun p hp => eOf_exc M p hp) χ (Z χ) (m χ) y κ T _ (by linarith)
      hT0.le (h2 χ) (fun ρ hρ => (hre χ ρ hρ).1) (h3 χ) (hsharp χ)
    rw [htdef] at a
    have a' : ‖psiChi χ y - mainPsi (eOf M) χ y‖ ≤
        4 * y * E / δ + 20 * δ * y * ∑ ρ ∈ Z χ, (m χ ρ : ℝ) * y ^ (ρ.re - 1)
        + 4 * (δ * y + 1) * Real.log (2 * y) + 2 * y * W χ + excI (eOf M) χ * (2 * y * t) := by
      rw [hW]; exact a
    have b : 20 * δ * y * ∑ ρ ∈ Z χ, (m χ ρ : ℝ) * y ^ (ρ.re - 1)
        ≤ 20 * δ * y * (W χ + excI (eOf M) χ) := mul_le_mul_of_nonneg_left (hmW χ) (by positivity)
    have c : 20 * δ * y * W χ ≤ 20 * y * W χ := by
      have : 0 ≤ y * W χ := mul_nonneg hy0.le (hW0 χ)
      nlinarith
    linarith
  have hsum : ∑ χ : DirichletCharacter ℂ M, ‖psiChi χ y - mainPsi (eOf M) χ y‖ ≤
      (M : ℝ) * (4 * y * E / δ + 4 * (δ * y + 1) * Real.log (2 * y)) + 22 * y * ∑ χ, W χ
        + (20 * δ * y + 2 * y * t) := by
    refine (Finset.sum_le_sum (fun χ _ => hper χ)).trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
      ← Finset.mul_sum, ← Finset.sum_mul]
    have q0 : 0 ≤ 4 * y * E / δ + 4 * (δ * y + 1) * Real.log (2 * y) := by positivity
    have q1 : 0 ≤ 20 * δ * y + 2 * y * t := by positivity
    have r1 := mul_le_mul_of_nonneg_right (card_char_le M) q0
    have r2 := mul_le_mul_of_nonneg_right (sum_excI_le (eOf M)) q1
    linarith
  have hη0 : 0 < etaOf M := etaOf_pos M (by omega)
  have hex := inv_le_exp hcA (lt_min hcz (by positivity : 0 < cA ^ 2)) (min_le_right _ _) hM8r hy hr2
  have hηM : (M : ℝ)⁻¹ ≤ etaOf M / c₁ := by
    have := heta M hM3
    rw [Real.rpow_neg_one] at this
    rw [le_div_iff₀ hc₁]; linarith
  have hMi : 0 < (M : ℝ)⁻¹ := by positivity
  have hWs : ∑ χ, W χ ≤ |Az| * etaOf M * Real.exp (-(min cz (cA ^ 2) * Real.log y / Real.log M)) := by
    rw [hW]
    refine hZS.trans ?_
    have e1 : Real.exp (-(cz * Real.log y / Real.log M))
        ≤ Real.exp (-(min cz (cA ^ 2) * Real.log y / Real.log M)) := by
      apply Real.exp_le_exp.2
      apply neg_le_neg
      have : min cz (cA ^ 2) ≤ cz := min_le_left _ _
      gcongr
    have e2 : Az ≤ |Az| := le_abs_self _
    gcongr
  have hfin : B * y * ((M : ℝ)⁻¹ * (M : ℝ)⁻¹)
      ≤ B * y * (etaOf M / c₁ * Real.exp (-(min cz (cA ^ 2) * Real.log y / Real.log M))) := by
    gcongr
  generalize Real.exp (-(min cz (cA ^ 2) * Real.log y / Real.log M)) = ex at *
  have f1 : 22 * y * ∑ χ, W χ ≤ 22 * y * (|Az| * etaOf M * ex) :=
    mul_le_mul_of_nonneg_left hWs (by positivity)
  have f2 : (22 * |Az| + B / c₁) * y * etaOf M * ex
      = 22 * y * (|Az| * etaOf M * ex) + B * y * (etaOf M / c₁ * ex) := by ring
  rw [f2]
  linarith

end Formalism.HermitianLattices.Ext.PrimesInProgressions
