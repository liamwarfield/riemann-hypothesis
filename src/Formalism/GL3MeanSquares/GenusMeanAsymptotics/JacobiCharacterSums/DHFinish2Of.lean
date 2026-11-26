module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHSt

@[expose] public section

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.DHFinish2Of
open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet

def DHTuran2 : Prop :=
  ∃ (C : ℝ) (A : ℕ), 0 < C ∧ 1 ≤ A ∧ ∀ (n m : ℕ) (z : Fin n → ℂ), 1 ≤ n →
    (∀ i, ‖z i‖ ≤ 1) → (∃ i, ‖z i‖ = 1) →
    ∃ k : ℕ, m + 1 ≤ k ∧ k ≤ m + A * n ∧ ((n : ℝ) / (C * ((m : ℝ) + n))) ^ (A * n) ≤ ‖∑ i, z i ^ k‖

def DHDom : Prop :=
  ∀ (M : ℕ) [NeZero M] (χ₁ χ : DirichletCharacter ℂ M) (γ σ : ℝ) (k : ℕ), χ₁ ^ 2 = 1 → 1 < σ →
    ‖iteratedDeriv k (negLD χ) ((σ : ℂ) + γ * I) + iteratedDeriv k (negLD (χ * χ₁)) ((σ : ℂ) + γ * I)‖ ≤
      ((-1 : ℂ) ^ k * (iteratedDeriv k (negLD (1 : DirichletCharacter ℂ M)) (σ : ℂ)
        + iteratedDeriv k (negLD χ₁) (σ : ℂ))).re

def DHIneqF : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (M : ℕ) [NeZero M] (χ₁ χ : DirichletCharacter ℂ M) (β₁ T η : ℝ) (ρ : ℂ),
    3 ≤ M → 2 ≤ T → χ₁ ^ 2 = 1 → χ₁ ≠ 1 → DirichletCharacter.LFunction χ₁ (β₁ : ℂ) = 0 →
    19 / 20 ≤ β₁ → β₁ < 1 → IsLZero χ ρ → 22 / 25 ≤ ρ.re → |ρ.im| ≤ T → (χ, ρ) ≠ (χ₁, (β₁ : ℂ)) →
    0 < η → η ≤ 2 / 25 →
    ∃ (N : ℕ) (w : Fin N → ℂ),
      (∀ i, η ≤ (w i).re) ∧
      (∃ i, w i = ((η + (1 - ρ.re) : ℝ) : ℂ)) ∧
      (∑ i, 1 / w i).re ≤ 2 * (1 - β₁) / η ^ 2 + C * Real.log ((M : ℝ) * T) * 25 ∧
      ∀ j : ℕ, 1 ≤ j →
        ‖∑ i, 1 / (w i) ^ j‖ ≤
          ((-1 : ℂ) ^ (j - 1) * (iteratedDeriv (j - 1) (negLD (1 : DirichletCharacter ℂ M)) ((1 + η : ℝ) : ℂ)
              + iteratedDeriv (j - 1) (negLD χ₁) ((1 + η : ℝ) : ℂ))).re / ((j - 1).factorial : ℝ)
          + 2 * j * (1 - β₁) / η ^ (j + 1) + C * Real.log ((M : ℝ) * T) * 25 ^ j

def DHHyper : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (M : ℕ) [NeZero M] (χ₁ : DirichletCharacter ℂ M) (y x : ℝ), 3 ≤ M → χ₁ ^ 2 = 1 → χ₁ ≠ 1 →
    1 ≤ y → y ≤ x →
    ∑ n ∈ Finset.Ioc ⌊y⌋₊ ⌊x⌋₊, (∑ d ∈ n.divisors, χ₁ (d : ZMod M)).re / (n : ℝ) ≤
      ‖DirichletCharacter.LFunction χ₁ 1‖ * Real.log (x / y) + C * M * (Real.log y + 1) / Real.sqrt y

def DHPrime : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (M : ℕ) [NeZero M] (χ₁ : DirichletCharacter ℂ M) (β₁ σ : ℝ) (k : ℕ),
    3 ≤ M → χ₁ ^ 2 = 1 → χ₁ ≠ 1 → DirichletCharacter.LFunction χ₁ (β₁ : ℂ) = 0 →
    1 - 1 / Real.log (3 * M) ≤ β₁ → β₁ < 1 → 1 < σ → σ ≤ 2 →
    ((-1 : ℂ) ^ k * (iteratedDeriv k (negLD (1 : DirichletCharacter ℂ M)) (σ : ℂ)
        + iteratedDeriv k (negLD χ₁) (σ : ℂ))).re / (k.factorial : ℝ) ≤
      C * (1 - β₁) * Real.log (3 * M) ^ 2 * (k + 2) ^ 2 / (σ - 1) ^ (k + 2)
        + (C * Real.log (3 * M)) ^ (k + 1) / (k.factorial : ℝ)
        + C * (k + 2) * Real.log (3 * M) ^ 2 / (M * (σ - 1) ^ (k + 1))

def DHIneqFOf : Prop := DHPos → DHLocal → DHDom → DHIneqF

def DHPrimeOf : Prop := DHHyper → DHPrime

def DHFinish2Of : Prop := DHTuran2 → DHIneqF → DHPrime → DeuringHeilbronnMB

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHPos
open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet
open LSeries ArithmeticFunction DirichletCharacter
open scoped LSeries.notation

lemma dhPos_iter_logMul (f : ℕ → ℂ) (k n : ℕ) :
    (logMul^[k] f) n = (Complex.log n) ^ k * f n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', LSeries.logMul, ih]
    ring

lemma dhPos_abscissa {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    abscissaOfAbsConv (↗ψ * ↗Λ) < s.re := by
  have h : abscissaOfAbsConv (↗ψ * ↗Λ) ≤ ((1 : ℝ) : EReal) := by
    apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
    intro y hy
    exact DirichletCharacter.LSeriesSummable_twist_vonMangoldt ψ (by simp only [Complex.ofReal_re]; exact_mod_cast hy)
  exact lt_of_le_of_lt h (by exact_mod_cast hs)

lemma dhPos_iter {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) (k : ℕ) {s : ℂ}
    (hs : 1 < s.re) :
    (-1 : ℂ) ^ k * iteratedDeriv k (negLD ψ) s = LSeries (logMul^[k] (↗ψ * ↗Λ)) s := by
  have hopen : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hEq : ∀ z : ℂ, 1 < z.re → negLD ψ z = LSeries (↗ψ * ↗Λ) z := by
    intro z hz
    have hev : DirichletCharacter.LFunction ψ =ᶠ[nhds z] LSeries (fun n => ψ n) := by
      filter_upwards [hopen.mem_nhds hz] with w hw
      exact DirichletCharacter.LFunction_eq_LSeries ψ hw
    unfold negLD
    rw [hev.deriv_eq, DirichletCharacter.LFunction_eq_LSeries ψ hz,
      DirichletCharacter.LSeries_twist_vonMangoldt_eq ψ hz]
    ring
  have heq : negLD ψ =ᶠ[nhds s] LSeries (↗ψ * ↗Λ) := by
    filter_upwards [hopen.mem_nhds hs] with z hz
    exact hEq z hz
  rw [heq.iteratedDeriv_eq, LSeries_iteratedDeriv k (dhPos_abscissa ψ hs), ← mul_assoc, ← mul_pow]
  norm_num

lemma dhPos_hasSum {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) (k : ℕ) {s : ℂ}
    (hs : 1 < s.re) :
    HasSum (fun n ↦ (term (logMul^[k] (↗ψ * ↗Λ)) s n).re)
      ((-1 : ℂ) ^ k * iteratedDeriv k (negLD ψ) s).re := by
  rw [dhPos_iter ψ k hs]
  have habs : abscissaOfAbsConv (logMul^[k] (↗ψ * ↗Λ)) < s.re := by
    have e : ∀ j : ℕ, abscissaOfAbsConv (logMul^[j] (↗ψ * ↗Λ)) = abscissaOfAbsConv (↗ψ * ↗Λ) := by
      intro j
      induction j with
      | zero => rfl
      | succ j ih => rw [Function.iterate_succ_apply', LSeries.abscissaOfAbsConv_logMul, ih]
    rw [e]
    exact dhPos_abscissa ψ hs
  have hs2 := (LSeriesSummable_of_abscissaOfAbsConv_lt_re habs).LSeriesHasSum
  exact Complex.reCLM.hasSum hs2

lemma dhPos_term {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) (k : ℕ) (σ u : ℝ) (n : ℕ) :
    term (logMul^[k] (↗ψ * ↗Λ)) ((σ : ℂ) + u * I) n =
      (((Real.log n) ^ k * (Λ n / (n : ℝ) ^ σ) : ℝ) : ℂ) * (ψ n / (n : ℂ) ^ ((u : ℂ) * I)) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
    have hlog : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
      rw [Complex.ofReal_log (Nat.cast_nonneg n)]
      simp
    have hpow : (n : ℂ) ^ (σ : ℂ) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
      simp
    have hpos : ((n : ℝ) ^ σ) ≠ 0 := (Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) σ).ne'
    have hu : (n : ℂ) ^ ((u : ℂ) * I) ≠ 0 := Complex.cpow_ne_zero_iff.2 (Or.inl hn')
    rw [LSeries.term_of_ne_zero hn, dhPos_iter_logMul, Complex.cpow_add _ _ hn', hpow, hlog]
    simp only [Pi.mul_apply]
    push_cast
    field_simp

lemma dhPos_term_real {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) (k : ℕ) (σ : ℝ) (n : ℕ) :
    term (logMul^[k] (↗ψ * ↗Λ)) (σ : ℂ) n =
      (((Real.log n) ^ k * (Λ n / (n : ℝ) ^ σ) : ℝ) : ℂ) * ψ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have hlog : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
      rw [Complex.ofReal_log (Nat.cast_nonneg n)]
      simp
    have hpow : (n : ℂ) ^ (σ : ℂ) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
      simp
    have hpos : ((n : ℝ) ^ σ) ≠ 0 := (Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) σ).ne'
    rw [LSeries.term_of_ne_zero hn, dhPos_iter_logMul, hpow, hlog]
    simp only [Pi.mul_apply]
    push_cast
    field_simp

lemma dhPos_term_nonneg {q : ℕ} [NeZero q] (χ₁ χ : DirichletCharacter ℂ q) (h1 : χ₁ ^ 2 = 1)
    (k : ℕ) (σ γ : ℝ) (n : ℕ) :
    0 ≤ (term (logMul^[k] (↗(1 : DirichletCharacter ℂ q) * ↗Λ)) (σ : ℂ) n).re
      + (term (logMul^[k] (↗χ₁ * ↗Λ)) (σ : ℂ) n).re
      + (term (logMul^[k] (↗χ * ↗Λ)) ((σ : ℂ) + γ * I) n).re
      + (term (logMul^[k] (↗(χ * χ₁) * ↗Λ)) ((σ : ℂ) + γ * I) n).re := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [dhPos_term_real, dhPos_term_real, dhPos_term, dhPos_term]
  simp only [Complex.re_ofReal_mul]
  have hA0 : 0 ≤ (Real.log n) ^ k * (Λ n / (n : ℝ) ^ σ) :=
    mul_nonneg (pow_nonneg (Real.log_natCast_nonneg n) k)
      (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity))
  have hz1 : ‖(n : ℂ) ^ ((γ : ℂ) * I)‖ = 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hn]
    simp
  have hw : -1 ≤ (χ n / (n : ℂ) ^ ((γ : ℂ) * I)).re := by
    have hnorm : ‖χ n / (n : ℂ) ^ ((γ : ℂ) * I)‖ ≤ 1 := by
      rw [norm_div, hz1, div_one]
      exact DirichletCharacter.norm_le_one χ _
    have h2 := Complex.abs_re_le_norm (χ n / (n : ℂ) ^ ((γ : ℂ) * I))
    linarith [(abs_le.1 h2).1]
  have key : 0 ≤ ((1 : DirichletCharacter ℂ q) n).re + (χ₁ n).re + (χ n / (n : ℂ) ^ ((γ : ℂ) * I)).re +
      ((χ * χ₁) n / (n : ℂ) ^ ((γ : ℂ) * I)).re := by
    by_cases hu : IsUnit (n : ZMod q)
    · have h1n : (1 : DirichletCharacter ℂ q) n = 1 := MulChar.one_apply hu
      have hsq : χ₁ n * χ₁ n = 1 := by
        have e := congrArg (fun ψ : DirichletCharacter ℂ q => ψ n) h1
        simpa only [pow_two, MulChar.mul_apply, MulChar.one_apply hu] using e
      have hχ₁ : χ₁ n = 1 ∨ χ₁ n = -1 := by
        have h' : (χ₁ n - 1) * (χ₁ n + 1) = 0 := by linear_combination hsq
        rcases mul_eq_zero.1 h' with h | h
        · left
          linear_combination h
        · right
          linear_combination h
      rw [MulChar.mul_apply, h1n]
      rcases hχ₁ with h | h
      · rw [h, mul_one]
        simp only [Complex.one_re]
        linarith
      · rw [h]
        simp only [Complex.one_re, Complex.neg_re, mul_neg, mul_one, neg_div]
        linarith
    · have h0 : ∀ ψ : DirichletCharacter ℂ q, ψ n = 0 := fun ψ => MulChar.map_nonunit ψ hu
      simp [h0]
  nlinarith [mul_nonneg hA0 key]

theorem deuring_heilbronn_positivity : DHPos := by
  intro M _ χ₁ χ γ σ k h1 hσ
  have hs1 : 1 < ((σ : ℂ)).re := by simpa using hσ
  have hs2 : 1 < ((σ : ℂ) + γ * I).re := by simpa using hσ
  have H1 := dhPos_hasSum (1 : DirichletCharacter ℂ M) k hs1
  have H2 := dhPos_hasSum χ₁ k hs1
  have H3 := dhPos_hasSum χ k hs2
  have H4 := dhPos_hasSum (χ * χ₁) k hs2
  have Hall := ((H1.add H2).add H3).add H4
  rw [mul_add, mul_add, mul_add, Complex.add_re, Complex.add_re, Complex.add_re]
  exact Hall.nonneg (fun n => dhPos_term_nonneg χ₁ χ h1 k σ γ n)

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDensSpace
open Complex Finset

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens

open Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD Formalism.ZeroFreeDirichlet

lemma space_harm (x : ℕ) : ∑ k ∈ Icc 1 x, ((k : ℝ))⁻¹ ≤ 1 + Real.log x := by
  rcases Nat.eq_zero_or_pos x with hx | hx
  · subst hx; simp
  · have h := harmonic_le_one_add_log x
    have e : ((harmonic x : ℚ) : ℝ) = ∑ k ∈ Icc 1 x, ((k : ℝ))⁻¹ := by
      rw [harmonic_eq_sum_Icc]; push_cast; rfl
    rw [← e]; exact h

lemma floor_eq_close {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : ⌊a⌋₊ = ⌊b⌋₊) : |a - b| < 1 := by
  have h1 := Nat.floor_le ha
  have h2 := Nat.lt_floor_add_one a
  have h3 := Nat.floor_le hb
  have h4 := Nat.lt_floor_add_one b
  rw [h] at h1 h2
  rw [abs_lt]; constructor <;> linarith

lemma space_side (Q : Finset ℝ) (f : ℝ → ℝ) (T : ℝ) (hT : 0 ≤ T) (h1 : ∀ x ∈ Q, 1 ≤ f x)
    (h2 : ∀ x ∈ Q, f x ≤ 2 * T) (hsp : ∀ x ∈ Q, ∀ y ∈ Q, x ≠ y → 1 ≤ |f x - f y|) :
    ∑ x ∈ Q, 1 / f x ≤ 1 + Real.log (2 * T + 1) := by
  have hinj : Set.InjOn (fun x => ⌊f x⌋₊) Q := by
    intro x hx y hy hxy
    by_contra hne
    have := floor_eq_close (by linarith [h1 x hx]) (by linarith [h1 y hy]) hxy
    have := hsp x hx y hy hne
    linarith
  have step1 : ∑ x ∈ Q, 1 / f x ≤ ∑ x ∈ Q, ((⌊f x⌋₊ : ℕ) : ℝ)⁻¹ := by
    refine sum_le_sum (fun x hx => ?_)
    have hf1 := h1 x hx
    have hfl : (1 : ℝ) ≤ (⌊f x⌋₊ : ℝ) := by
      have : 1 ≤ ⌊f x⌋₊ := Nat.le_floor (by exact_mod_cast hf1)
      exact_mod_cast this
    rw [one_div]
    exact inv_anti₀ (by linarith) (Nat.floor_le (by linarith))
  have step2 : ∑ x ∈ Q, ((⌊f x⌋₊ : ℕ) : ℝ)⁻¹ = ∑ k ∈ Q.image (fun x => ⌊f x⌋₊), ((k : ℕ) : ℝ)⁻¹ := by
    rw [sum_image hinj]
  have hsub : Q.image (fun x => ⌊f x⌋₊) ⊆ Icc 1 ⌊2 * T⌋₊ := by
    intro k hk
    rw [mem_image] at hk
    obtain ⟨x, hx, rfl⟩ := hk
    rw [mem_Icc]
    exact ⟨Nat.le_floor (by exact_mod_cast h1 x hx), Nat.floor_le_floor (h2 x hx)⟩
  have step3 : ∑ k ∈ Q.image (fun x => ⌊f x⌋₊), ((k : ℕ) : ℝ)⁻¹ ≤ ∑ k ∈ Icc 1 ⌊2 * T⌋₊, ((k : ℕ) : ℝ)⁻¹ :=
    sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
  have step4 : Real.log (⌊2 * T⌋₊ : ℝ) ≤ Real.log (2 * T + 1) := by
    rcases Nat.eq_zero_or_pos ⌊2 * T⌋₊ with h0 | h0
    · rw [h0, Nat.cast_zero, Real.log_zero]; exact Real.log_nonneg (by linarith)
    · exact Real.log_le_log (by exact_mod_cast h0) (by linarith [Nat.floor_le (by linarith : (0 : ℝ) ≤ 2 * T)])
  linarith [space_harm ⌊2 * T⌋₊]

theorem zero_spacing : Spacing := by
  intro P T hT hP hsp
  constructor
  · have hinj : Set.InjOn (fun x => ⌊x + T⌋₊) P := by
      intro x hx y hy hxy
      by_contra hne
      have hx' := abs_le.1 (hP x hx)
      have hy' := abs_le.1 (hP y hy)
      have := floor_eq_close (by linarith) (by linarith) hxy
      have := hsp x hx y hy hne
      rw [show x + T - (y + T) = x - y by ring] at *
      linarith
    have hsub : P.image (fun x => ⌊x + T⌋₊) ⊆ range (⌊2 * T⌋₊ + 1) := by
      intro k hk
      rw [mem_image] at hk
      obtain ⟨x, hx, rfl⟩ := hk
      rw [mem_range, Nat.lt_succ_iff]
      exact Nat.floor_le_floor (by linarith [(abs_le.1 (hP x hx)).2])
    have h1 : P.card ≤ ⌊2 * T⌋₊ + 1 := by
      rw [← card_image_of_injOn hinj]
      exact (card_le_card hsub).trans (by simp)
    have h2 : ((⌊2 * T⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * T + 1 := by
      push_cast; linarith [Nat.floor_le (by linarith : (0 : ℝ) ≤ 2 * T)]
    exact (by exact_mod_cast h1 : (P.card : ℝ) ≤ ((⌊2 * T⌋₊ + 1 : ℕ) : ℝ)).trans h2
  · intro t ht
    have hsplit := sum_filter_add_sum_filter_not (P.erase t) (fun x => t < x) (fun x => 1 / |t - x|)
    rw [← hsplit]
    have hR : ∑ x ∈ (P.erase t).filter (fun x => t < x), 1 / |t - x| ≤ 1 + Real.log (2 * T + 1) := by
      have e : ∑ x ∈ (P.erase t).filter (fun x => t < x), 1 / |t - x| =
          ∑ x ∈ (P.erase t).filter (fun x => t < x), 1 / (x - t) := by
        refine sum_congr rfl (fun x hx => ?_)
        rw [mem_filter] at hx
        rw [abs_sub_comm, abs_of_pos (by linarith [hx.2])]
      rw [e]
      refine space_side _ (fun x => x - t) T hT (fun x hx => ?_) (fun x hx => ?_) (fun x hx y hy hne => ?_)
      · rw [mem_filter, mem_erase] at hx
        have := hsp x hx.1.2 t ht hx.1.1
        rw [abs_of_pos (by linarith [hx.2])] at this
        exact this
      · rw [mem_filter, mem_erase] at hx
        have a := abs_le.1 (hP x hx.1.2)
        have b := abs_le.1 (hP t ht)
        show x - t ≤ 2 * T
        linarith
      · rw [mem_filter, mem_erase] at hx hy
        have := hsp x hx.1.2 y hy.1.2 hne
        rwa [show x - t - (y - t) = x - y by ring]
    have hL : ∑ x ∈ (P.erase t).filter (fun x => ¬ t < x), 1 / |t - x| ≤ 1 + Real.log (2 * T + 1) := by
      have e : ∑ x ∈ (P.erase t).filter (fun x => ¬ t < x), 1 / |t - x| =
          ∑ x ∈ (P.erase t).filter (fun x => ¬ t < x), 1 / (t - x) := by
        refine sum_congr rfl (fun x hx => ?_)
        rw [mem_filter, mem_erase] at hx
        have hlt : x < t := lt_of_le_of_ne (not_lt.1 hx.2) hx.1.1
        rw [abs_of_pos (by linarith)]
      rw [e]
      refine space_side _ (fun x => t - x) T hT (fun x hx => ?_) (fun x hx => ?_) (fun x hx y hy hne => ?_)
      · rw [mem_filter, mem_erase] at hx
        have hlt : x < t := lt_of_le_of_ne (not_lt.1 hx.2) hx.1.1
        have := hsp x hx.1.2 t ht hx.1.1
        rw [abs_of_neg (by linarith)] at this
        show 1 ≤ t - x
        linarith
      · rw [mem_filter, mem_erase] at hx
        have a := abs_le.1 (hP x hx.1.2)
        have b := abs_le.1 (hP t ht)
        show t - x ≤ 2 * T
        linarith
      · rw [mem_filter, mem_erase] at hx hy
        have := hsp x hx.1.2 y hy.1.2 hne
        rwa [show t - x - (t - y) = -(x - y) by ring, abs_neg]
    linarith

theorem space_card_char_le (M : ℕ) [NeZero M] :
    ((Finset.univ : Finset (DirichletCharacter ℂ M)).card : ℝ) ≤ M := by
  have h : (Finset.univ : Finset (DirichletCharacter ℂ M)).card = M.totient := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card,
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ M]
  rw [h]
  exact_mod_cast Nat.totient_le M

theorem trivial_bound : Triv := by
  intro M _ T S hT hS hsp
  classical
  have hfib : ∀ χ : DirichletCharacter ℂ M, ((S.filter (fun p => p.1 = χ)).card : ℝ) ≤ 2 * T + 1 := by
    intro χ
    set F := S.filter (fun p => p.1 = χ) with hF
    have hinj : Set.InjOn (fun p : DirichletCharacter ℂ M × ℂ => p.2.im) F := by
      intro p hp p' hp' h
      by_contra hne
      rw [hF, coe_filter] at hp hp'
      have := hsp p hp.1 p' hp'.1 hne (hp.2.trans hp'.2.symm)
      simp only at h
      rw [h, sub_self, abs_zero] at this
      linarith
    have hsp' := (zero_spacing (F.image (fun p => p.2.im)) T hT
      (fun x hx => by
        rw [mem_image] at hx
        obtain ⟨p, hp, rfl⟩ := hx
        exact hS p (mem_of_mem_filter _ hp))
      (fun x hx y hy hne => by
        rw [mem_image] at hx hy
        obtain ⟨p, hp, rfl⟩ := hx
        obtain ⟨p', hp', rfl⟩ := hy
        have hpp : p ≠ p' := fun h => hne (by rw [h])
        rw [hF, mem_filter] at hp hp'
        exact hsp p hp.1 p' hp'.1 hpp (hp.2.trans hp'.2.symm))).1
    rwa [card_image_of_injOn hinj] at hsp'
  have hsum : (S.card : ℝ) = ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ M)),
      ((S.filter (fun p => p.1 = χ)).card : ℝ) := by
    rw [card_eq_sum_card_fiberwise (f := fun p : DirichletCharacter ℂ M × ℂ => p.1) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)]
    push_cast; rfl
  rw [hsum]
  calc ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ M)), ((S.filter (fun p => p.1 = χ)).card : ℝ)
      ≤ ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ M)), (2 * T + 1) := sum_le_sum (fun χ _ => hfib χ)
    _ = ((Finset.univ : Finset (DirichletCharacter ℂ M)).card : ℝ) * (2 * T + 1) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ (M : ℝ) * (2 * T + 1) := mul_le_mul_of_nonneg_right (space_card_char_le M) (by linarith)

end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
end
end

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTExplLF
open Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.ZeroFreeDirichlet

variable {M : ℕ} [NeZero M]

theorem exLF_of_ne {χ : DirichletCharacter ℂ M} (h : χ ≠ 1) : exLF χ = DirichletCharacter.LFunction χ := by
  unfold exLF; rw [if_neg h]

theorem exLF_one_char : exLF (1 : DirichletCharacter ℂ M) = DirichletCharacter.LFunctionTrivChar₁ M := by
  unfold exLF; rw [if_pos rfl]

theorem exLF_one_char_apply {s : ℂ} (hs : s ≠ 1) :
    exLF (1 : DirichletCharacter ℂ M) s = (s - 1) * DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M) s := by
  rw [exLF_one_char, DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hs]

theorem exLF_differentiable (χ : DirichletCharacter ℂ M) : Differentiable ℂ (exLF χ) := by
  by_cases h : χ = 1
  · subst h; rw [exLF_one_char]; exact DirichletCharacter.differentiable_LFunctionTrivChar₁ M
  · rw [exLF_of_ne h]; exact DirichletCharacter.differentiable_LFunction h

theorem exLF_one_ne_zero (χ : DirichletCharacter ℂ M) : exLF χ 1 ≠ 0 := by
  by_cases h : χ = 1
  · subst h; rw [exLF_one_char]; exact DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero M
  · rw [exLF_of_ne h]; exact DirichletCharacter.LFunction_apply_one_ne_zero h

theorem exLF_eq_zero_iff (χ : DirichletCharacter ℂ M) {s : ℂ} (hs : s ≠ 1) :
    exLF χ s = 0 ↔ DirichletCharacter.LFunction χ s = 0 := by
  by_cases h : χ = 1
  · subst h; rw [exLF_one_char_apply hs, mul_eq_zero]
    exact ⟨fun h => h.resolve_left (sub_ne_zero_of_ne hs), Or.inr⟩
  · rw [exLF_of_ne h]

theorem isLZero_iff_exLF (χ : DirichletCharacter ℂ M) (s : ℂ) : IsLZero χ s ↔ exLF χ s = 0 := by
  unfold IsLZero
  by_cases hs : s = 1
  · subst hs
    constructor
    · rintro ⟨h1, h2⟩
      exact absurd h2 (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ h1 (by simp))
    · intro h; exact absurd h (exLF_one_ne_zero χ)
  · rw [exLF_eq_zero_iff χ hs]
    exact ⟨fun h => h.2, fun h => ⟨Or.inr hs, h⟩⟩

theorem exLF_re_lt_one (χ : DirichletCharacter ℂ M) {s : ℂ} (hs : exLF χ s = 0) : s.re < 1 := by
  by_contra hlt
  obtain ⟨h1, h2⟩ := (isLZero_iff_exLF χ s).2 hs
  exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ h1 (not_lt.1 hlt) h2

theorem negLD_eq_exLF (χ : DirichletCharacter ℂ M) {s : ℂ} (hs : s ≠ 1) (h0 : exLF χ s ≠ 0) :
    negLD χ s = (if χ = 1 then 1 / (s - 1) else 0) - deriv (exLF χ) s / exLF χ s := by
  unfold negLD
  by_cases h : χ = 1
  · subst h
    have hL : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M) s ≠ 0 :=
      fun hz => h0 ((exLF_eq_zero_iff _ hs).2 hz)
    have hs1 : s - 1 ≠ 0 := sub_ne_zero_of_ne hs
    rw [if_pos rfl, exLF_one_char_apply hs, exLF_one_char,
      DirichletCharacter.deriv_LFunctionTrivChar₁_apply_of_ne_one M hs]
    simp only [DirichletCharacter.LFunctionTrivChar]
    field_simp
    ring
  · rw [if_neg h, exLF_of_ne h, zero_sub]

theorem exLF_deriv_ne_zero (χ : DirichletCharacter ℂ M) {ρ : ℂ} (hρ : exLF χ ρ = 0)
    (hd : deriv (DirichletCharacter.LFunction χ) ρ ≠ 0) : deriv (exLF χ) ρ ≠ 0 := by
  by_cases h : χ = 1
  · subst h
    have hs : ρ ≠ 1 := by
      rintro rfl; exact exLF_one_ne_zero _ hρ
    have hL := (exLF_eq_zero_iff _ hs).1 hρ
    rw [exLF_one_char, DirichletCharacter.deriv_LFunctionTrivChar₁_apply_of_ne_one M hs]
    simp only [DirichletCharacter.LFunctionTrivChar]
    rw [hL, add_zero]
    exact mul_ne_zero (sub_ne_zero_of_ne hs) hd
  · rw [exLF_of_ne h]; exact hd

theorem exLF_analyticAt (χ : DirichletCharacter ℂ M) (z : ℂ) : AnalyticAt ℂ (exLF χ) z :=
  (exLF_differentiable χ).analyticAt z

theorem exLF_order_ne_top (χ : DirichletCharacter ℂ M) (ρ : ℂ) : analyticOrderAt (exLF χ) ρ ≠ ⊤ := by
  intro h
  have := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero ρ (exLF_analyticAt χ)).1 h
  exact exLF_one_ne_zero χ (by rw [this]; rfl)

theorem exOrd_pos (χ : DirichletCharacter ℂ M) {ρ : ℂ} (hρ : exLF χ ρ = 0) : 1 ≤ exOrd χ ρ := by
  unfold exOrd
  rw [Nat.one_le_iff_ne_zero]
  intro h
  have h1 : analyticOrderAt (exLF χ) ρ = 0 := by
    rw [← Nat.cast_analyticOrderNatAt (exLF_order_ne_top χ ρ), h]; rfl
  exact ((exLF_analyticAt χ ρ).analyticOrderAt_eq_zero.1 h1) hρ

theorem exOrd_eq_one (χ : DirichletCharacter ℂ M) {ρ : ℂ} (hρ : exLF χ ρ = 0) (hd : deriv (exLF χ) ρ ≠ 0) :
    exOrd χ ρ = 1 := by
  unfold exOrd analyticOrderNatAt
  rw [(exLF_analyticAt χ ρ).analyticOrderAt_eq_one_of_zero_deriv_ne_zero hρ hd]
  rfl

theorem exLF_prod_le (M : ℕ) [NeZero M] (s : ℂ) (hs : 1 / 2 ≤ s.re) :
    ‖∏ p ∈ M.primeFactors, (1 - (p : ℂ) ^ (-s))‖ ≤ M := by
  have h1 : ‖∏ p ∈ M.primeFactors, (1 - (p : ℂ) ^ (-s))‖ ≤ ∏ p ∈ M.primeFactors, (p : ℝ) := by
    rw [norm_prod]
    refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun p hp => ?_)
    have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
    have hn : ‖(p : ℂ) ^ (-s)‖ ≤ 1 := by
      rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hp0]
      apply Real.rpow_le_one_of_one_le_of_nonpos
      · exact_mod_cast (by omega : 1 ≤ p)
      · simp only [Complex.neg_re]; linarith
    calc ‖1 - (p : ℂ) ^ (-s)‖ ≤ ‖(1 : ℂ)‖ + ‖(p : ℂ) ^ (-s)‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := by rw [norm_one]; linarith
      _ ≤ p := by
        have : (2 : ℝ) ≤ p := by exact_mod_cast hp2
        linarith
  have h2 : ∏ p ∈ M.primeFactors, (p : ℝ) ≤ M := by
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) (Nat.prod_primeFactors_dvd M)
    calc ∏ p ∈ M.primeFactors, (p : ℝ) = ((∏ p ∈ M.primeFactors, p : ℕ) : ℝ) := by push_cast; rfl
      _ ≤ M := by exact_mod_cast this
  exact h1.trans h2

theorem exLF_growth : ∃ C : ℝ, 1 ≤ C ∧ ∀ (M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M) (s : ℂ), 1 / 2 ≤ s.re →
    ‖exLF χ s‖ ≤ C * M * (1 + ‖s‖) ^ 2 := by
  obtain ⟨C0, hC0⟩ := lfunction_polynomial_growth
  refine ⟨max C0 6, le_trans (by norm_num) (le_max_right _ _), ?_⟩
  intro M _ χ s hs
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast NeZero.one_le
  have hn : 0 ≤ ‖s‖ := norm_nonneg s
  by_cases h : χ = 1
  · subst h
    have h6 : 6 * (M : ℝ) * (1 + ‖s‖) ^ 2 ≤ max C0 6 * M * (1 + ‖s‖) ^ 2 := by
      gcongr; exact le_max_right _ _
    refine le_trans ?_ h6
    by_cases hs1 : s = 1
    · subst hs1
      rw [exLF_one_char]
      simp only [Function.update_self]
      have := exLF_prod_le M 1 (by norm_num)
      have he : ∏ p ∈ M.primeFactors, (1 - (p : ℂ) ^ (-(1 : ℂ))) = ∏ p ∈ M.primeFactors, (1 - (p : ℂ)⁻¹) := by
        refine Finset.prod_congr rfl (fun p _ => ?_)
        rw [Complex.cpow_neg_one]
      rw [he] at this
      refine this.trans ?_
      rw [norm_one]; nlinarith
    · rw [exLF_one_char_apply hs1]
      have hz := DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta (N := M) hs1
      simp only [DirichletCharacter.LFunctionTrivChar] at hz
      rw [hz]
      have hP := exLF_prod_le M s hs
      have hZ := Formalism.ZF.growthBound s (by linarith) hs1
      have hpos : 0 < ‖s - 1‖ := norm_pos_iff.2 (sub_ne_zero_of_ne hs1)
      have hle : ‖s - 1‖ ≤ 1 + ‖s‖ := by
        calc ‖s - 1‖ ≤ ‖s‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
          _ = 1 + ‖s‖ := by rw [norm_one]; ring
      have hre : 1 / s.re ≤ 2 := by
        rw [div_le_iff₀ (by linarith)]; linarith
      have hA : ‖s - 1‖ * ‖riemannZeta s‖ ≤ 6 * (1 + ‖s‖) ^ 2 := by
        calc ‖s - 1‖ * ‖riemannZeta s‖ ≤ ‖s - 1‖ * (1 + 1 / ‖s - 1‖ + ‖s‖ * (1 + 1 / s.re)) := by gcongr
          _ = ‖s - 1‖ + 1 + ‖s - 1‖ * (‖s‖ * (1 + 1 / s.re)) := by field_simp
          _ ≤ (1 + ‖s‖) + 1 + (1 + ‖s‖) * (‖s‖ * (1 + 2)) := by gcongr
          _ ≤ 6 * (1 + ‖s‖) ^ 2 := by nlinarith
      calc ‖(s - 1) * ((∏ p ∈ M.primeFactors, (1 - (p : ℂ) ^ (-s))) * riemannZeta s)‖
          = ‖∏ p ∈ M.primeFactors, (1 - (p : ℂ) ^ (-s))‖ * (‖s - 1‖ * ‖riemannZeta s‖) := by
            rw [norm_mul, norm_mul]; ring
        _ ≤ M * (6 * (1 + ‖s‖) ^ 2) := by gcongr
        _ = 6 * (M : ℝ) * (1 + ‖s‖) ^ 2 := by ring
  · rw [exLF_of_ne h]
    have h1 := hC0 M χ h s hs
    have h2 : C0 * M * (1 + ‖s‖) ≤ max C0 6 * M * (1 + ‖s‖) := by
      gcongr; exact le_max_left _ _
    have h3 : max C0 6 * M * (1 + ‖s‖) ≤ max C0 6 * M * (1 + ‖s‖) ^ 2 := by
      have hc : 0 ≤ max C0 6 * M := by
        have : (0 : ℝ) ≤ max C0 6 := le_trans (by norm_num) (le_max_right _ _)
        positivity
      have : (1 + ‖s‖) ≤ (1 + ‖s‖) ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_left this hc
    linarith

theorem exLF_lower (χ : DirichletCharacter ℂ M) (s : ℂ) (hs : 1 < s.re) :
    min 1 ‖s - 1‖ * ((s.re - 1) / s.re) ≤ ‖exLF χ s‖ := by
  have hI := inverseBound M χ s hs
  have hs1 : s ≠ 1 := by rintro rfl; simp at hs
  have hne : DirichletCharacter.LFunction χ s ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr hs1) hs.le
  have hpos : 0 < ‖DirichletCharacter.LFunction χ s‖ := norm_pos_iff.2 hne
  have hq : 0 < (s.re - 1) / s.re := div_pos (by linarith) (by linarith)
  have hL : (s.re - 1) / s.re ≤ ‖DirichletCharacter.LFunction χ s‖ := by
    have h1 : (s.re / (s.re - 1))⁻¹ ≤ (‖DirichletCharacter.LFunction χ s‖⁻¹)⁻¹ :=
      inv_anti₀ (inv_pos.2 hpos) hI
    rwa [inv_inv, inv_div] at h1
  by_cases h : χ = 1
  · subst h
    rw [exLF_one_char_apply hs1, norm_mul]
    exact mul_le_mul (min_le_right _ _) hL hq.le (norm_nonneg _)
  · rw [exLF_of_ne h]
    calc min 1 ‖s - 1‖ * ((s.re - 1) / s.re) ≤ 1 * ((s.re - 1) / s.re) :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) hq.le
      _ ≤ _ := by rw [one_mul]; exact hL

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHFinish
open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet

namespace DHF

theorem logMT_ge_one (M : ℕ) (T : ℝ) (hM : 3 ≤ M) (hT : 2 ≤ T) : 1 ≤ Real.log ((M : ℝ) * T) := by
  have hMr : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hx : (6 : ℝ) ≤ M * T := by nlinarith
  have he := Real.exp_one_lt_d9
  have h1 : Real.exp 1 ≤ (M : ℝ) * T := by linarith
  calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ Real.log ((M : ℝ) * T) := Real.log_le_log (Real.exp_pos 1) h1

theorem region_gap : ∃ cR : ℝ, 0 < cR ∧ ∀ (M : ℕ) [NeZero M] (χ₁ χ : DirichletCharacter ℂ M) (β₁ T c₁ : ℝ)
    (ρ : ℂ), 3 ≤ M → 2 ≤ T → χ₁ ≠ 1 → DirichletCharacter.LFunction χ₁ (β₁ : ℂ) = 0 → 0 < c₁ → c₁ ≤ cR →
    1 - c₁ / Real.log ((M : ℝ) * T) < β₁ → IsLZero χ ρ → |ρ.im| ≤ T → (χ, ρ) ≠ (χ₁, (β₁ : ℂ)) →
    cR / 2 ≤ (1 - ρ.re) * Real.log ((M : ℝ) * T) := by
  obtain ⟨cR, hcR, hZ⟩ := Formalism.ZeroFreeDirichlet.zFRDirichlet
  refine ⟨cR, hcR, ?_⟩
  intro M _ χ₁ χ β₁ T c₁ ρ hM hT2 hχ1ne hLz hc₁0 hc₁ hβ₁ hρ hρim hne
  have hLg1 := logMT_ge_one M T hM hT2
  have hLg0 : 0 < Real.log ((M : ℝ) * T) := by linarith
  have hM3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hlog2M : Real.log ((M : ℝ) * (|((β₁ : ℂ)).im| + 2)) ≤ Real.log ((M : ℝ) * T) := by
    simp only [Complex.ofReal_im, abs_zero, zero_add]
    exact Real.log_le_log (by positivity) (by nlinarith)
  have hlog2M0 : 0 < Real.log ((M : ℝ) * (|((β₁ : ℂ)).im| + 2)) := by
    apply Real.log_pos; simp only [Complex.ofReal_im, abs_zero, zero_add]; nlinarith
  have hreg : InRegion cR M (β₁ : ℂ) := by
    unfold InRegion
    have h1 : c₁ / Real.log ((M : ℝ) * T) ≤ cR / Real.log ((M : ℝ) * (|((β₁ : ℂ)).im| + 2)) := by
      rw [div_le_div_iff₀ hLg0 hlog2M0]
      have h2 := mul_le_mul_of_nonneg_left hlog2M hc₁0.le
      have h3 := mul_le_mul_of_nonneg_right hc₁ hLg0.le
      linarith only [h2, h3]
    rw [Complex.ofReal_re]; linarith only [h1, hβ₁]
  have hLz' : IsLZero χ₁ (β₁ : ℂ) := ⟨Or.inl hχ1ne, hLz⟩
  have hZ1 := (hZ M χ₁ (β₁ : ℂ) hreg hLz').2.2.2.2
  have hnreg : ¬ InRegion cR M ρ := by
    intro h
    obtain ⟨h1, h2⟩ := hZ1 χ ρ h hρ
    exact hne (Prod.ext h1 h2)
  unfold InRegion at hnreg
  push Not at hnreg
  have hlogρ0 : 0 < Real.log ((M : ℝ) * (|ρ.im| + 2)) := by
    apply Real.log_pos; have := abs_nonneg ρ.im; nlinarith
  have hlogρ : Real.log ((M : ℝ) * (|ρ.im| + 2)) ≤ 2 * Real.log ((M : ℝ) * T) := by
    rw [show (2 : ℝ) * Real.log ((M : ℝ) * T) = Real.log (((M : ℝ) * T) ^ 2) by
      rw [Real.log_pow]; push_cast; ring]
    apply Real.log_le_log (by have := abs_nonneg ρ.im; positivity)
    have : |ρ.im| + 2 ≤ 2 * T := by linarith
    have hM0 : (0 : ℝ) ≤ M := by positivity
    have hMT : (2 : ℝ) ≤ M * T := by nlinarith
    have hMT2 := mul_le_mul_of_nonneg_left hMT (by positivity : (0 : ℝ) ≤ M * T)
    calc (M : ℝ) * (|ρ.im| + 2) ≤ M * (2 * T) := mul_le_mul_of_nonneg_left this hM0
      _ ≤ _ := by rw [sq]; linarith
  have h1 : cR / Real.log ((M : ℝ) * (|ρ.im| + 2)) < 1 - ρ.re := by linarith
  rw [div_lt_iff₀ hlogρ0] at h1
  have hδ0 : 0 < 1 - ρ.re := by
    by_contra h; push Not at h
    have := mul_nonpos_of_nonpos_of_nonneg h hlogρ0.le
    linarith
  have := mul_le_mul_of_nonneg_left hlogρ hδ0.le
  linarith

end DHF

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end
