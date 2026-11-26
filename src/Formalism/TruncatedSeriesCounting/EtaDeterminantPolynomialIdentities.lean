module

public import Formalism.GaussValuationBounds.GaussValueContraction.GaussValueContractionProofFactBis
public import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.ColTwoStep
public import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.RrBound
public import Formalism.CharacterColumnKernels.IdempotentNormalForms.LengthQuotSmulRangeFree
public import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.BridgeDet
public import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.LemmaDetPoly
public import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.TruncZero

@[expose] public section

section -- merged from Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.FirstSigmaValuationBound
noncomputable section

namespace Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains

open Finset

private lemma sum_erase_union_le (f : ℤ → ℕ) (A B : Finset ℤ) :
    (∑ j ∈ (A ∪ B).erase 0, f j) ≤ (∑ j ∈ A.erase 0, f j) + ∑ j ∈ B.erase 0, f j := by
  classical
  rw [Finset.erase_union_distrib]
  have h := Finset.sum_union_inter (s₁ := A.erase 0) (s₂ := B.erase 0) (f := f)
  first
  | omega
  | (rw [← h]; exact Nat.le_add_right _ _)

private lemma sum_Icc_padicValNat_add_factorial_eq (ℓ : ℕ) [Fact ℓ.Prime] (m L : ℕ) :
    (∑ n ∈ Finset.Icc (m + 1) (m + L), padicValNat ℓ n) + padicValNat ℓ m.factorial =
      padicValNat ℓ (m + L).factorial := by
  induction L with
  | zero =>
    simp only [add_zero]
    rw [Finset.Icc_eq_empty (by omega)]
    simp
  | succ L ih =>
    rw [show m + (L + 1) = m + L + 1 by omega, Finset.sum_Icc_succ_top (by omega), Nat.factorial_succ,
      (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (by omega) (Nat.factorial_ne_zero _), ← ih]
    omega

private lemma sub_one_mul_padicValNat_factorial_le' (ℓ : ℕ) [Fact ℓ.Prime] (N : ℕ) :
    (ℓ - 1) * padicValNat ℓ N.factorial ≤ N := by
  rw [Nat.padicValNat_def, (Fact.out : ℓ.Prime).sub_one_mul_multiplicity_factorial]
  omega

private lemma padicValNat_factorial_add_le_add_log (ℓ : ℕ) [Fact ℓ.Prime] (m L : ℕ) :
    padicValNat ℓ (m + L).factorial ≤
      padicValNat ℓ m.factorial + padicValNat ℓ L.factorial + Nat.log ℓ (m + L) := by
  have h := Nat.add_choose_mul_factorial_mul_factorial m L
  have hc : (m + L).choose L ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have hlog : padicValNat ℓ ((m + L).choose L) ≤ Nat.log ℓ (m + L) := by
    rw [Nat.padicValNat_def, ← Nat.factorization_def _ (Fact.out : ℓ.Prime)]
    exact Nat.factorization_choose_le_log
  rw [← h, (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (by positivity) (Nat.factorial_ne_zero _),
    (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) hc (Nat.factorial_ne_zero _)]
  omega

private lemma sum_Icc_one_padicValNat_eq_factorial (ℓ : ℕ) [Fact ℓ.Prime] (L : ℕ) :
    (∑ n ∈ Finset.Icc 1 L, padicValNat ℓ n) = padicValNat ℓ L.factorial := by
  have h := sum_Icc_padicValNat_add_factorial_eq ℓ 0 L
  simpa [Nat.padicValNat_def] using h

theorem first_sigma_valuation_bound : TwoIntervalValuationSumBound := by
  intro ℓ _ h η S b a hab hbS
  have hℓ : ℓ.Prime := Fact.out
  have hℓ2 : 2 ≤ ℓ := hℓ.two_le
  have step1 := sum_erase_union_le (padicValInt ℓ) (Finset.Icc (1 - (η : ℤ)) ((η : ℤ) + a))
    (Finset.Icc (1 - ((b + S : ℕ) : ℤ)) ((a : ℤ) - b))
  have hI1 : (∑ j ∈ (Finset.Icc (1 - (η : ℤ)) ((η : ℤ) + a)).erase 0, padicValInt ℓ j) ≤
      padicValNat ℓ (η - 1).factorial + padicValNat ℓ (η + a).factorial := by
    have hsub : (Finset.Icc (1 - (η : ℤ)) ((η : ℤ) + a)).erase 0 ⊆
        Finset.Icc (1 - (η : ℤ)) (-1) ∪ Finset.Icc 1 ((η : ℤ) + a) := by
      intro j hj
      simp only [Finset.mem_erase, Finset.mem_Icc, Finset.mem_union] at hj ⊢
      omega
    have hdisj : Disjoint (Finset.Icc (1 - (η : ℤ)) (-1)) (Finset.Icc 1 ((η : ℤ) + a)) := by
      rw [Finset.disjoint_left]
      intro j h1 h2
      simp only [Finset.mem_Icc] at h1 h2
      omega
    have hneg : (∑ j ∈ Finset.Icc (1 - (η : ℤ)) (-1), padicValInt ℓ j) =
        ∑ n ∈ Finset.Icc 1 (η - 1), padicValNat ℓ n := by
      apply Finset.sum_nbij' (fun j : ℤ => ((-j).toNat : ℕ)) (fun n : ℕ => -(n : ℤ))
      · intro j hj
        simp only [Finset.mem_Icc] at hj ⊢
        omega
      · intro n hn
        simp only [Finset.mem_Icc] at hn ⊢
        omega
      · intro j hj
        simp only [Finset.mem_Icc] at hj
        try dsimp only
        omega
      · intro n hn
        try dsimp only
        omega
      · intro j hj
        simp only [Finset.mem_Icc] at hj
        try dsimp only
        rw [padicValInt, Nat.padicValNat_def]
        congr 1
        omega
    have hpos : (∑ j ∈ Finset.Icc 1 ((η : ℤ) + a), padicValInt ℓ j) =
        ∑ n ∈ Finset.Icc 1 (η + a), padicValNat ℓ n := by
      apply Finset.sum_nbij' (fun j : ℤ => (j.toNat : ℕ)) (fun n : ℕ => (n : ℤ))
      · intro j hj
        simp only [Finset.mem_Icc] at hj ⊢
        omega
      · intro n hn
        simp only [Finset.mem_Icc] at hn ⊢
        omega
      · intro j hj
        simp only [Finset.mem_Icc] at hj
        try dsimp only
        omega
      · intro n hn
        try dsimp only
        omega
      · intro j hj
        simp only [Finset.mem_Icc] at hj
        try dsimp only
        rw [padicValInt, Nat.padicValNat_def]
        congr 1
        omega
    calc _ ≤ ∑ j ∈ Finset.Icc (1 - (η : ℤ)) (-1) ∪ Finset.Icc 1 ((η : ℤ) + a), padicValInt ℓ j :=
          Finset.sum_le_sum_of_subset hsub
      _ = _ := by rw [Finset.sum_union hdisj, hneg, hpos, sum_Icc_one_padicValNat_eq_factorial, sum_Icc_one_padicValNat_eq_factorial]
  have hI2 : (∑ j ∈ (Finset.Icc (1 - ((b + S : ℕ) : ℤ)) ((a : ℤ) - b)).erase 0, padicValInt ℓ j) ≤
      padicValNat ℓ (a + S).factorial + Nat.log ℓ (b - a - 1 + (a + S)) := by
    have heq : (∑ j ∈ Finset.Icc (1 - ((b + S : ℕ) : ℤ)) ((a : ℤ) - b), padicValInt ℓ j) =
        ∑ n ∈ Finset.Icc (b - a - 1 + 1) (b - a - 1 + (a + S)), padicValNat ℓ n := by
      apply Finset.sum_nbij' (fun j : ℤ => ((-j).toNat : ℕ)) (fun n : ℕ => -(n : ℤ))
      · intro j hj
        simp only [Finset.mem_Icc] at hj ⊢
        omega
      · intro n hn
        simp only [Finset.mem_Icc] at hn ⊢
        omega
      · intro j hj
        simp only [Finset.mem_Icc] at hj
        try dsimp only
        omega
      · intro n hn
        try dsimp only
        omega
      · intro j hj
        simp only [Finset.mem_Icc] at hj
        try dsimp only
        rw [padicValInt, Nat.padicValNat_def]
        congr 1
        omega
    have h1 := sum_Icc_padicValNat_add_factorial_eq ℓ (b - a - 1) (a + S)
    have h2 := padicValNat_factorial_add_le_add_log ℓ (b - a - 1) (a + S)
    calc _ ≤ ∑ j ∈ Finset.Icc (1 - ((b + S : ℕ) : ℤ)) ((a : ℤ) - b), padicValInt ℓ j :=
          Finset.sum_le_sum_of_subset (Finset.erase_subset _ _)
      _ = _ := heq
      _ ≤ _ := by omega
  have tot : (∑ j ∈ (Finset.Icc (1 - (η : ℤ)) ((η : ℤ) + a) ∪
        Finset.Icc (1 - ((b + S : ℕ) : ℤ)) ((a : ℤ) - b)).erase 0, padicValInt ℓ j) ≤
      padicValNat ℓ (η - 1).factorial + padicValNat ℓ (η + a).factorial +
        padicValNat ℓ (a + S).factorial + Nat.log ℓ (b - a - 1 + (a + S)) := by
    omega
  have hℓR : (1 : ℝ) < ℓ := by exact_mod_cast (show 1 < ℓ by omega)
  have hpos : (0 : ℝ) < (ℓ : ℝ) - 1 := by linarith
  have hsubℓ : ((ℓ - 1 : ℕ) : ℝ) = (ℓ : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    simp
  have r : ∀ N : ℕ, ((ℓ : ℝ) - 1) * (padicValNat ℓ N.factorial : ℝ) ≤ (N : ℝ) := by
    intro N
    have c := sub_one_mul_padicValNat_factorial_le' ℓ N
    have c' : ((ℓ - 1 : ℕ) : ℝ) * (padicValNat ℓ N.factorial : ℝ) ≤ (N : ℝ) := by exact_mod_cast c
    rwa [hsubℓ] at c'
  have hsum : (padicValNat ℓ (η - 1).factorial : ℝ) + (padicValNat ℓ (η + a).factorial : ℝ) +
      (padicValNat ℓ (a + S).factorial : ℝ) ≤ (2 * (a : ℝ) + 2 * (η : ℝ) + (S : ℝ)) / ((ℓ : ℝ) - 1) := by
    rw [le_div_iff₀ hpos]
    have e1 := r (η - 1)
    have e2 := r (η + a)
    have e3 := r (a + S)
    have e4 : ((η - 1 : ℕ) : ℝ) ≤ (η : ℝ) := by exact_mod_cast Nat.sub_le η 1
    push_cast at e2 e3
    nlinarith [e1, e2, e3, e4]
  have hlam0 : 0 ≤ lam ℓ (h + η) := by
    unfold lam
    by_cases h0 : h + η = 0
    · rw [h0]
      simp
    · have h1 : (1 : ℝ) ≤ ((h + η : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h0
      have h2 : (1 : ℝ) ≤ 2 * ((h + η : ℕ) : ℝ) := by linarith
      have := Real.logb_nonneg hℓR h2
      linarith
  have hk : ((Nat.log ℓ (b - a - 1 + (a + S)) : ℕ) : ℝ) ≤ lam ℓ (h + η) := by
    by_cases hN : b - a - 1 + (a + S) = 0
    · rw [hN, Nat.log_zero_right]
      simpa using hlam0
    · have hpow : ℓ ^ Nat.log ℓ (b - a - 1 + (a + S)) ≤ b - a - 1 + (a + S) :=
        Nat.pow_log_le_self ℓ hN
      have hNh : b - a - 1 + (a + S) ≤ 2 * (h + η) := by omega
      have hNpos : (0 : ℝ) < ((b - a - 1 + (a + S) : ℕ) : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hN
      have h1 : ((Nat.log ℓ (b - a - 1 + (a + S)) : ℕ) : ℝ) ≤
          Real.logb ℓ ((b - a - 1 + (a + S) : ℕ) : ℝ) := by
        rw [Real.le_logb_iff_rpow_le hℓR hNpos, Real.rpow_natCast]
        exact_mod_cast hpow
      have h2 : Real.logb ℓ ((b - a - 1 + (a + S) : ℕ) : ℝ) ≤
          Real.logb ℓ (2 * ((h + η : ℕ) : ℝ)) := by
        apply Real.logb_le_logb_of_le hℓR hNpos
        exact_mod_cast hNh
      unfold lam
      linarith
  refine le_trans (Nat.cast_le.mpr tot) ?_
  push_cast
  linarith

end Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains
end
end

section -- merged from Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.LemmaGVal
namespace Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains

open Finset

private lemma sum_shift_val (ℓ : ℕ) (j₀ : ℤ) (T : Finset ℤ) :
    ∑ j ∈ T, padicValInt ℓ (j₀ - j) = ∑ i ∈ T.image (fun j => j₀ - j), padicValInt ℓ i := by
  rw [Finset.sum_image]
  intro a _ b _ h
  simp only at h
  omega

theorem g_coeff_valuation_statement : LemmaGVal := by
  intro ℓ _ h η S b a S₂ hb hbS hS₂ j₀ hj₀
  rw [Finset.mem_Icc] at hj₀
  obtain ⟨hj1, hj2⟩ := hj₀
  have hℓ : (2 : ℝ) ≤ ℓ := by exact_mod_cast (Fact.out : ℓ.Prime).two_le
  have hmem : ∀ j ∈ S₂, ((b : ℤ) + 1 ≤ j ∧ j ≤ (b : ℤ) + S + a) ∨
      (1 - (η : ℤ) ≤ j ∧ j ≤ (η : ℤ) + a) := by
    intro j hj
    have := hS₂ hj
    simpa only [Finset.mem_union, Finset.mem_Icc] using this
  set T₁ : Finset ℤ := (Finset.Icc ((b : ℤ) - a + 1) b).erase j₀ ∪
    S₂.filter (fun j => (b : ℤ) < j) with hT₁
  set T₂ : Finset ℤ := S₂.filter (fun j => ¬ (b : ℤ) < j) with hT₂
  have hsplit : (∑ j ∈ (Finset.Icc ((b : ℤ) - a + 1) (b : ℤ)).erase j₀, padicValInt ℓ (j₀ - j)) +
      ∑ j ∈ S₂, padicValInt ℓ (j₀ - j) =
      ∑ j ∈ T₁, padicValInt ℓ (j₀ - j) + ∑ j ∈ T₂, padicValInt ℓ (j₀ - j) := by
    rw [← Finset.sum_filter_add_sum_filter_not S₂ (fun j => (b : ℤ) < j), ← add_assoc, hT₁,
      hT₂, Finset.sum_union]
    rw [Finset.disjoint_left]
    intro x hx hx'
    have h1 := (Finset.mem_Icc.mp (Finset.mem_of_mem_erase hx)).2
    have h2 := (Finset.mem_filter.mp hx').2
    omega
  rw [hsplit, sum_shift_val, sum_shift_val]
  have c1 : T₁.image (fun j => j₀ - j) ⊆
      Finset.Ico (j₀ - b - S - a) (j₀ - b - S - a + ((2 * a + S : ℕ) : ℤ)) := by
    intro i hi
    rw [Finset.mem_image] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    rw [Finset.mem_Ico]
    push_cast
    rw [hT₁, Finset.mem_union] at hj
    rcases hj with hj | hj
    · have := Finset.mem_Icc.mp (Finset.mem_of_mem_erase hj)
      omega
    · have h1 := (Finset.mem_filter.mp hj).2
      have h2 := hmem j (Finset.mem_filter.mp hj).1
      omega
  have c2 : (0 : ℤ) ∉ T₁.image (fun j => j₀ - j) := by
    intro hi
    rw [Finset.mem_image] at hi
    obtain ⟨j, hj, hj0⟩ := hi
    rw [hT₁, Finset.mem_union] at hj
    rcases hj with hj | hj
    · have := Finset.ne_of_mem_erase hj
      omega
    · have h1 := (Finset.mem_filter.mp hj).2
      omega
  have c3 : ∀ i ∈ T₁.image (fun j => j₀ - j), |i| ≤ ((2 * (h + η) : ℕ) : ℤ) := by
    intro i hi
    rw [Finset.mem_image] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    push_cast
    rw [hT₁, Finset.mem_union] at hj
    rw [abs_le]
    rcases hj with hj | hj
    · have := Finset.mem_Icc.mp (Finset.mem_of_mem_erase hj)
      constructor <;> omega
    · have h1 := (Finset.mem_filter.mp hj).2
      have h2 := hmem j (Finset.mem_filter.mp hj).1
      constructor <;> omega
  have d1 : T₂.image (fun j => j₀ - j) ⊆
      Finset.Ico (j₀ - η - a) (j₀ - η - a + ((2 * η + a : ℕ) : ℤ)) := by
    intro i hi
    rw [Finset.mem_image] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    rw [Finset.mem_Ico]
    push_cast
    have h1 := (Finset.mem_filter.mp hj).2
    have h2 := hmem j (Finset.mem_filter.mp hj).1
    omega
  have d2 : (0 : ℤ) ∉ T₂.image (fun j => j₀ - j) := by
    intro hi
    rw [Finset.mem_image] at hi
    obtain ⟨j, hj, hj0⟩ := hi
    have h1 := (Finset.mem_filter.mp hj).2
    have h2 := hmem j (Finset.mem_filter.mp hj).1
    omega
  have d3 : ∀ i ∈ T₂.image (fun j => j₀ - j), |i| ≤ ((2 * (h + η) : ℕ) : ℤ) := by
    intro i hi
    rw [Finset.mem_image] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    push_cast
    rw [abs_le]
    have h1 := (Finset.mem_filter.mp hj).2
    have h2 := hmem j (Finset.mem_filter.mp hj).1
    constructor <;> omega
  have w1 := Formalism.WindowSums.arc_WindowSum ℓ (j₀ - b - S - a) (2 * a + S) (2 * (h + η)) _ c1 c2 c3
  have w2 := Formalism.WindowSums.arc_WindowSum ℓ (j₀ - η - a) (2 * η + a) (2 * (h + η)) _ d1 d2 d3
  have hDpos : (1 : ℝ) ≤ ((2 * (h + η) : ℕ) : ℝ) := by
    have : 1 ≤ 2 * (h + η) := by omega
    exact_mod_cast this
  have hlog : 0 ≤ Real.logb ℓ ((2 * (h + η) : ℕ) : ℝ) := Real.logb_nonneg (by linarith) hDpos
  have hlam : lam ℓ (h + η) = Real.logb ℓ ((2 * (h + η) : ℕ) : ℝ) + 1 := by
    simp only [lam]
    push_cast
    ring_nf
  have hsum : ((2 * a + S : ℕ) : ℝ) / ((ℓ : ℝ) - 1) + ((2 * η + a : ℕ) : ℝ) / ((ℓ : ℝ) - 1) =
      (3 * (a : ℝ) + (S : ℝ) + 2 * (η : ℝ)) / ((ℓ : ℝ) - 1) := by
    rw [← add_div]
    push_cast
    ring_nf
  rw [hlam]
  push_cast at w1 w2 hlog hsum ⊢
  linarith

end Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains
end

section -- merged from Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.HCoefficientBound
namespace Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains

private lemma hCoef_num (x : ℝ) (hx : 11 ≤ x) : 0 ≤ 7 * x ^ 3 - 78 * x ^ 2 + 95 * x - 32 := by

  have hy : 0 ≤ x - 11 := by linarith
  nlinarith [mul_nonneg (mul_nonneg hy hy) hy, mul_nonneg hy hy]

theorem h_coefficient_bound : HCoef := by
  intro x hx
  have h0 : (0 : ℝ) < x := by linarith
  have h1 : (0 : ℝ) < x - 1 := by linarith
  have hx0 : x ≠ 0 := ne_of_gt h0
  have hx1 : x - 1 ≠ 0 := ne_of_gt h1
  have key := hCoef_num x hx
  have e : 32 / x ^ 2 - (8 * (2 * x - 1) / (x - 1) ^ 3 + 8 / (x - 1) ^ 2 + 1 / (x * (x - 1)))
      = (7 * x ^ 3 - 78 * x ^ 2 + 95 * x - 32) / (x ^ 2 * (x - 1) ^ 3) := by
    field_simp
    ring
  have hd : 0 ≤ (7 * x ^ 3 - 78 * x ^ 2 + 95 * x - 32) / (x ^ 2 * (x - 1) ^ 3) :=
    div_nonneg key (by positivity)
  linarith

end Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains
end

section -- merged from Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.KappaSecondExponentBound
noncomputable section

namespace Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains

theorem second_exponent_bound : MaxZeroExponentInequality := by
  intro ℓ hℓ b b' S h'' E s₂ L c' hE hs hL hc
  have hℓ' : (2 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ
  have hl1 : (0 : ℝ) < (ℓ : ℝ) - 1 := by linarith
  have hl0 : (0 : ℝ) < (ℓ : ℝ) := by linarith
  have hb : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b
  have hS : (0 : ℝ) ≤ (S : ℝ) := Nat.cast_nonneg S
  have hcast : (((b + S + 1 : ℕ) : ℝ)) = (b : ℝ) + (S : ℝ) + 1 := by push_cast; ring

  have e2 : (b : ℝ) / ((ℓ : ℝ) - 1) = (b : ℝ) / ((ℓ : ℝ) * ((ℓ : ℝ) - 1)) + (b : ℝ) / (ℓ : ℝ) := by
    field_simp
    ring
  have e1 : ((b : ℝ) + (S : ℝ) + 1) / ((ℓ : ℝ) - 1)
      = (b : ℝ) / ((ℓ : ℝ) - 1) + ((S : ℝ) + 1) / ((ℓ : ℝ) - 1) := by ring

  have e3 : ((S : ℝ) + 1) / ((ℓ : ℝ) - 1) ≤ (S : ℝ) + 1 := by
    have hq : 0 ≤ ((S : ℝ) + 1) / ((ℓ : ℝ) - 1) := div_nonneg (by linarith) hl1.le
    have hm : ((S : ℝ) + 1) / ((ℓ : ℝ) - 1) * ((ℓ : ℝ) - 1) = (S : ℝ) + 1 := by
      field_simp
    nlinarith [mul_nonneg hq (by linarith : (0 : ℝ) ≤ (ℓ : ℝ) - 2)]
  have h4 : 0 ≤ (b : ℝ) / ((ℓ : ℝ) * ((ℓ : ℝ) - 1)) := div_nonneg hb (mul_pos hl0 hl1).le
  rw [hcast]
  apply max_le
  · linarith
  · rw [e1, e2]
    linarith

end Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains
end
end

section -- merged from Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.ColChain
noncomputable section

namespace Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains

section Chain

variable {O : Type} [CommRing O] {M : Type} [AddCommGroup M] [Module O M]

theorem chain_len_add (X Y Z : Submodule O M) (hXY : X ≤ Y) (hYZ : Y ≤ Z) :
    Module.length O (↥Z ⧸ X.comap Z.subtype) =
      Module.length O (↥Y ⧸ X.comap Y.subtype) + Module.length O (↥Z ⧸ Y.comap Z.subtype) := by
  have hle : X.comap Y.subtype ≤ (X.comap Z.subtype).comap (Submodule.inclusion hYZ) :=
    fun x hx => hx
  have hle2 : X.comap Z.subtype ≤ (Y.comap Z.subtype).comap LinearMap.id := fun x hx => hXY hx
  let f := Submodule.mapQ (X.comap Y.subtype) (X.comap Z.subtype) (Submodule.inclusion hYZ) hle
  let g := Submodule.mapQ (X.comap Z.subtype) (Y.comap Z.subtype) LinearMap.id hle2
  have hf : Function.Injective f := by
    refine (injective_iff_map_eq_zero f).2 ?_
    intro q hq
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hq
    rw [Submodule.Quotient.mk_eq_zero]
    exact hq
  have hg : Function.Surjective g := by
    intro q
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    exact ⟨Submodule.Quotient.mk z, by rw [Submodule.mapQ_apply, LinearMap.id_apply]⟩
  have hfg : Function.Exact f g := by
    intro q
    constructor
    · intro hz
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      rw [Submodule.mapQ_apply, LinearMap.id_apply, Submodule.Quotient.mk_eq_zero] at hz
      have hz' : (z : M) ∈ Y := hz
      exact ⟨Submodule.Quotient.mk ⟨z, hz'⟩, by rw [Submodule.mapQ_apply]; rfl⟩
    · rintro ⟨q', rfl⟩
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q'
      rw [Submodule.mapQ_apply, Submodule.mapQ_apply, LinearMap.id_apply,
        Submodule.Quotient.mk_eq_zero]
      exact y.2
  exact Module.length_eq_add_of_exact f g hf hg hfg

theorem chain_len_le_of_le_sup (A X Z : Submodule O M) (hAZ : A ≤ Z) (hZ : Z ≤ A ⊔ X) :
    Module.length O (↥Z ⧸ X.comap Z.subtype) ≤ Module.length O (↥A ⧸ X.comap A.subtype) := by
  have hle : X.comap A.subtype ≤ (X.comap Z.subtype).comap (Submodule.inclusion hAZ) :=
    fun x hx => hx
  apply Module.length_le_of_surjective (Submodule.mapQ _ _ (Submodule.inclusion hAZ) hle)
  intro q
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨a, ha, x, hx, hax⟩ := Submodule.mem_sup.1 (hZ z.2)
  refine ⟨Submodule.Quotient.mk ⟨a, ha⟩, ?_⟩
  rw [Submodule.mapQ_apply, Submodule.Quotient.eq]
  show (a - (z : M)) ∈ X
  rw [← hax, show a - (a + x) = -x by abel]
  exact X.neg_mem hx

theorem chain_len_le_top (A P : Submodule O M) (hA : ⊤ ≤ A ⊔ P) :
    Module.length O (M ⧸ P) ≤ Module.length O (↥A ⧸ P.comap A.subtype) := by
  apply Module.length_le_of_surjective (Submodule.mapQ (P.comap A.subtype) P A.subtype le_rfl)
  intro q
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨a, ha, x, hx, hax⟩ :=
    Submodule.mem_sup.1 (hA (Submodule.mem_top : m ∈ (⊤ : Submodule O M)))
  refine ⟨Submodule.Quotient.mk ⟨a, ha⟩, ?_⟩
  rw [Submodule.mapQ_apply, Submodule.Quotient.eq]
  show (a - m) ∈ P
  rw [← hax, show a - (a + x) = -x by abel]
  exact P.neg_mem hx

end Chain

private lemma comap_subtype_inf_of_le {O : Type} [CommRing O] {M : Type} [AddCommGroup M] [Module O M]
    (A B C : Submodule O M) (h : A ≤ C) : (B ⊓ C).comap A.subtype = B.comap A.subtype := by
  ext x
  simp [h x.2]

theorem column_chain_bound : ColChain := by
  unfold ColChain
  intro O _ M _ _ P k F h0 hF
  induction k with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, zero_add]
    exact chain_len_le_top (F 0) P (by rw [h0]; exact le_sup_left)
  | succ k ih =>
    have hk : F (k + 1) ≤ F k := hF k (Nat.lt_succ_self k)
    have ih' := ih (fun i hi => hF i (Nat.lt_succ_of_lt hi))
    have e1 := chain_len_add (P ⊓ F k) ((F (k + 1) ⊔ P) ⊓ F k) (F k)
      (inf_le_inf_right _ le_sup_right) inf_le_right
    rw [comap_subtype_inf_of_le (F k) P (F k) le_rfl, comap_subtype_inf_of_le (F k) (F (k + 1) ⊔ P) (F k) le_rfl] at e1
    have e2 := chain_len_le_of_le_sup (F (k + 1)) (P ⊓ F k) ((F (k + 1) ⊔ P) ⊓ F k)
      (le_inf le_sup_left hk) (le_of_eq (sup_inf_assoc_of_le P hk))
    rw [comap_subtype_inf_of_le (F (k + 1)) P (F k) hk] at e2
    rw [Finset.sum_range_succ, add_assoc]
    refine le_trans ih' (add_le_add le_rfl ?_)
    rw [e1, add_comm]
    exact add_le_add le_rfl e2

end Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains
end
end

section -- merged from Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.SubSmulOneInjective
noncomputable section

namespace Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains

open Module

section Snake

variable {O : Type} [CommRing O]

theorem len_coker_add {A B C : Type} [AddCommGroup A] [Module O A] [AddCommGroup B] [Module O B]
    [AddCommGroup C] [Module O C] (f : A →ₗ[O] B) (g : B →ₗ[O] C) (hf : Function.Injective f)
    (hg : Function.Surjective g) (hfg : Function.Exact f g)
    (a : Module.End O A) (b : Module.End O B) (c : Module.End O C)
    (h1 : ∀ x, b (f x) = f (a x)) (h2 : ∀ y, c (g y) = g (b y)) (hc : Function.Injective c) :
    Module.length O (B ⧸ LinearMap.range b) =
      Module.length O (A ⧸ LinearMap.range a) + Module.length O (C ⧸ LinearMap.range c) := by
  have hF : LinearMap.range a ≤ (LinearMap.range b).comap f := by
    rintro _ ⟨x, rfl⟩
    exact ⟨f x, h1 x⟩
  have hG : LinearMap.range b ≤ (LinearMap.range c).comap g := by
    rintro _ ⟨y, rfl⟩
    exact ⟨g y, h2 y⟩
  let F := Submodule.mapQ (LinearMap.range a) (LinearMap.range b) f hF
  let G := Submodule.mapQ (LinearMap.range b) (LinearMap.range c) g hG
  refine Module.length_eq_add_of_exact F G ?_ ?_ ?_
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [LinearMap.mem_ker] at hx
    simp only [F, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
    obtain ⟨y, hy⟩ := hx
    have hgy : g y = 0 := by
      apply hc
      rw [h2, hy, hfg.apply_apply_eq_zero, map_zero]
    obtain ⟨z, rfl⟩ := (hfg y).1 hgy
    have : a z = x := hf (by rw [← h1, hy])
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
    exact ⟨z, this⟩
  · intro w
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    obtain ⟨y, rfl⟩ := hg w
    exact ⟨Submodule.Quotient.mk y, by simp [G]⟩
  · intro w
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    simp only [G, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]
    constructor
    · rintro ⟨u, hu⟩
      obtain ⟨v, rfl⟩ := hg u
      have : g (y - b v) = 0 := by rw [map_sub, ← h2, hu, sub_self]
      obtain ⟨z, hz⟩ := (hfg _).1 this
      refine ⟨Submodule.Quotient.mk z, ?_⟩
      simp only [F, Submodule.mapQ_apply, hz]
      rw [Submodule.Quotient.eq]
      exact ⟨-v, by simp⟩
    · rintro ⟨z, hz⟩
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ z
      simp only [F, Submodule.mapQ_apply] at hz
      rw [Submodule.Quotient.eq'] at hz
      obtain ⟨t, ht⟩ := hz
      refine ⟨g t, ?_⟩
      rw [h2, ht, map_add (f := _), map_neg, hfg.apply_apply_eq_zero, neg_zero, zero_add]

end Snake

section Main

variable {O : Type} [CommRing O] [IsDomain O]

theorem sub_smul_one_injective {M : Type} [AddCommGroup M] [Module O M] [IsTorsionFree O M]
    (ℓ : O) (hℓ : ℓ ≠ 0) (q : Module.End O M) (n : ℕ) (hq : q ^ n = 0) :
    Function.Injective (q - ℓ • (1 : Module.End O M)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  have h1 : q x = ℓ • x := by
    rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at hx
    exact hx
  have h2 : ∀ k : ℕ, (q ^ k) x = ℓ ^ k • x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, h1, smul_smul, pow_succ]
  have h3 := h2 n
  rw [hq, LinearMap.zero_apply] at h3
  exact (smul_eq_zero.mp h3.symm).resolve_left (pow_ne_zero n hℓ)

theorem len_base (R : Type) [AddCommGroup R] [Module O R] [Module.Free O R] [Module.Finite O R]
    (ℓ : O) :
    Module.length O (R ⧸ LinearMap.range ((0 : Module.End O R) - ℓ • (1 : Module.End O R))) =
      (Module.finrank O R : ℕ∞) * Module.length O (O ⧸ Ideal.span {ℓ}) := by
  let e := (Module.finBasis O R).equivFun
  have hmap : (LinearMap.range ((0 : Module.End O R) - ℓ • (1 : Module.End O R))).map
      (e : R →ₗ[O] (Fin (finrank O R) → O)) =
      Submodule.pi Set.univ (fun _ => Ideal.span {ℓ}) := by
    ext v
    simp only [Submodule.mem_map, LinearMap.mem_range, Submodule.mem_pi, Set.mem_univ,
      true_implies, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩ i
      exact ⟨-(e y i), by simp [mul_comm]⟩
    · intro h
      choose c hc using h
      refine ⟨_, ⟨e.symm (fun i => -c i), rfl⟩, ?_⟩
      ext i
      change e (((0 : Module.End O R) - ℓ • (1 : Module.End O R)) (e.symm fun i => -c i)) i = v i
      simp [← hc, mul_comm]
  rw [(Submodule.Quotient.equiv _ _ e hmap).length_eq, (Submodule.quotientPi _).length_eq,
    Module.length_pi_of_fintype]
  simp [Finset.sum_const, nsmul_eq_mul]

theorem len_main [IsPrincipalIdealRing O] (ℓ : O) (hℓ : ℓ ≠ 0) (n : ℕ) :
    ∀ (R : Type) [AddCommGroup R] [Module O R] [Module.Free O R] [Module.Finite O R]
      (q : Module.End O R), q ^ (n + 1) = 0 →
      Module.length O (R ⧸ LinearMap.range (q - ℓ • (1 : Module.End O R))) =
        (Module.finrank O R : ℕ∞) * Module.length O (O ⧸ Ideal.span {ℓ}) := by
  induction n with
  | zero =>
    intro R _ _ _ _ q hq
    rw [zero_add, pow_one] at hq
    subst hq
    exact len_base R ℓ
  | succ n ih =>
    intro R _ _ _ _ q hq
    have hK : ∀ x ∈ LinearMap.ker q, q x ∈ LinearMap.ker q := fun x hx => by
      rw [LinearMap.mem_ker.mp hx]; exact Submodule.zero_mem _
    have hQ : ∀ x ∈ LinearMap.range q, q x ∈ LinearMap.range q :=
      fun x _ => LinearMap.mem_range_self q x
    let qK := q.restrict hK
    let qQ := q.restrict hQ
    have hqK : qK = 0 := by
      ext ⟨x, hx⟩
      simpa [qK] using hx
    have key : ∀ (k : ℕ) (x : LinearMap.range q), (((qQ ^ k) x : LinearMap.range q) : R) =
        (q ^ k) (x : R) := by
      intro k
      induction k with
      | zero => intro x; simp
      | succ k ihk =>
        intro x
        rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, ← ihk]
        rfl
    have hqQ : qQ ^ (n + 1) = 0 := by
      ext ⟨x, y, rfl⟩
      rw [key, LinearMap.zero_apply, Submodule.coe_zero, ← Module.End.mul_apply, ← pow_succ, hq,
        LinearMap.zero_apply]
    have hex : Function.Exact (LinearMap.ker q).subtype q.rangeRestrict :=
      LinearMap.exact_iff.mpr (by rw [LinearMap.ker_rangeRestrict, Submodule.range_subtype])
    have hsn := len_coker_add (LinearMap.ker q).subtype q.rangeRestrict
      (LinearMap.ker q).injective_subtype q.surjective_rangeRestrict hex
      (qK - ℓ • (1 : Module.End O _)) (q - ℓ • (1 : Module.End O R))
      (qQ - ℓ • (1 : Module.End O _))
      (fun x => by simp [qK]) (fun y => by ext; simp [qQ])
      (sub_smul_one_injective ℓ hℓ qQ (n + 1) hqQ)
    rw [hsn, ih _ qK (by rw [hqK, zero_pow (Nat.succ_ne_zero _)]), ih _ qQ hqQ, ← add_mul,
      ← Nat.cast_add]
    congr 2
    have h1 := (LinearMap.ker q).finrank_quotient_add_finrank
    rw [LinearEquiv.finrank_eq q.quotKerEquivRange] at h1
    omega

end Main

theorem length_pi_zero_bound : LenPi0 := by
  intro O _ _ _ R _ _ _ _ ℓ hℓ q hq
  obtain ⟨n, hn⟩ := hq
  exact len_main ℓ hℓ n R q (by rw [pow_succ, hn, zero_mul])

end Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains
end
end

section -- merged from Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.RamifiedValuationInequality
noncomputable section

namespace Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains

open PowerSeries

theorem ramified_valuation_inequality : RamifiedValuationInequality := by
  intro O _ _ _ ℓ hℓ ϖ e hϖ he hass ε u hε hu b y t hb hby hmem
  have hℓpos : 0 < ℓ := hℓ.out.pos
  obtain ⟨v₀, hv₀⟩ := hass

  have hℓnu : ¬ IsUnit (ℓ : O) := by
    intro h
    have h1 : IsUnit (ϖ ^ e) := by rw [← hv₀]; exact h.mul v₀.isUnit
    exact hϖ.not_isUnit ((isUnit_pow_iff (by omega)).mp h1)

  have hpow : ∀ k : ℕ, (ℓ : O) ^ k = ((v₀⁻¹ : Oˣ) : O) ^ k * ϖ ^ (e * k) := by
    intro k
    have : (ℓ : O) = ((v₀⁻¹ : Oˣ) : O) * ϖ ^ e := by
      rw [← hv₀, mul_comm (ℓ : O), ← mul_assoc, Units.inv_mul, one_mul]
    rw [this, mul_pow, ← pow_mul]

  set i₀ := (b - 1) / ℓ with hi₀def
  have h1 : ℓ * i₀ ≤ b - 1 := Nat.mul_div_le (b - 1) ℓ
  have h2 : b - 1 < ℓ * (i₀ + 1) := Nat.lt_mul_div_succ (b - 1) hℓpos
  have hi₀b : ℓ * i₀ < b := by omega
  have hbi : b ≤ ℓ * (i₀ + 1) := by omega
  have hyb : b ≤ ℓ * y := by
    have : (b : ℝ) ≤ (ℓ : ℝ) * (y : ℝ) := by
      rw [div_le_iff₀ (by exact_mod_cast hℓpos)] at hby; linarith
    exact_mod_cast this
  have hi₀y : i₀ < y := Nat.lt_of_mul_lt_mul_left (lt_of_lt_of_le hi₀b hyb)

  let vv : ℕ → ℕ := fun i => (y.choose i).factorization ℓ
  let mm : ℕ → ℕ := fun i => ordCompl[ℓ] (y.choose i)
  have hmmU : ∀ i ∈ Finset.range (y + 1), IsUnit ((mm i : ℕ) : O) := by
    intro i hi
    have hle : i ≤ y := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hcop : Nat.Coprime ℓ (mm i) := Nat.coprime_ordCompl hℓ.out (Nat.choose_pos hle).ne'
    have hic : IsCoprime (ℓ : ℤ) (mm i : ℤ) := Nat.isCoprime_iff_coprime.2 hcop
    obtain ⟨a, c, hac⟩ := hic
    have hac' : (a : O) * ℓ + (c : O) * (mm i : O) = 1 := by
      have := congrArg (Int.cast : ℤ → O) hac
      push_cast at this
      exact this
    have : IsUnit ((a : O) * ℓ + (c : O) * (mm i : O)) := by rw [hac']; exact isUnit_one
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add this with h | h
    · exact absurd (isUnit_of_mul_isUnit_right h) hℓnu
    · exact isUnit_of_mul_isUnit_right h
  let mexp : ℕ → ℕ := fun i => vv i + (y - i)
  let w : ℕ → PowerSeries O := fun i =>
    C ((mm i : ℕ) : O) * ε ^ (y - i) * u ^ i * C (((v₀⁻¹ : Oˣ) : O) ^ mexp i)
  let ee : ℕ → ℕ := fun i => ℓ * i
  let ms : ℕ → ℕ := fun i => e * mexp i
  have hsum : (Formalism.WindowSums.p1 ℓ ε u) ^ y =
      ∑ i ∈ Finset.range (y + 1), w i * X ^ ee i * C (ϖ ^ ms i) := by
    unfold Formalism.WindowSums.p1
    rw [add_comm, add_pow]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hn : ((y.choose i : ℕ) : PowerSeries O) = C (ℓ : O) ^ vv i * C ((mm i : ℕ) : O) := by
      conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self (y.choose i) ℓ]
      rw [Nat.cast_mul, Nat.cast_pow, ← map_natCast (C (R := O)) ℓ,
        ← map_natCast (C (R := O)) (mm i)]
    have hC : C (ℓ : O) ^ vv i * C (ℓ : O) ^ (y - i) =
        C (((v₀⁻¹ : Oˣ) : O) ^ mexp i) * C (ϖ ^ ms i) := by
      rw [← pow_add, ← map_pow, ← map_mul, ← hpow]
    have : (u * X ^ ℓ) ^ i * (C (ℓ : O) * ε) ^ (y - i) * ((y.choose i : ℕ) : PowerSeries O)
        = (C (ℓ : O) ^ vv i * C (ℓ : O) ^ (y - i)) * (C ((mm i : ℕ) : O) * ε ^ (y - i) * u ^ i)
          * X ^ (ℓ * i) := by
      rw [hn, mul_pow, mul_pow, ← pow_mul]; ring
    rw [this, hC]
    simp only [w, ee]
    ring
  have hw : ∀ i ∈ Finset.range (y + 1), IsUnit (w i) := fun i hi =>
    ((((hmmU i hi).map C).mul (hε.pow _)).mul (hu.pow _)).mul
      (((v₀⁻¹).isUnit.pow _).map C)
  have hinj : Set.InjOn ee (Finset.range (y + 1) : Set ℕ) := fun a _ c _ h =>
    Nat.eq_of_mul_eq_mul_left hℓpos h
  have hmem' : (∑ i ∈ Finset.range (y + 1), w i * X ^ ee i * C (ϖ ^ ms i)) ∈
      Ideal.span {(X : PowerSeries O) ^ b, C (ϖ ^ t)} := by
    rw [← hsum, Set.pair_comm]; exact hmem
  have hterm := (Formalism.WindowSums.mem_span_iff_of_distinct_exponents O ϖ hϖ.ne_zero hϖ.not_isUnit (Finset.range (y + 1))
    w ee ms b t hw hinj).1 hmem' i₀ (Finset.mem_range.2 (by omega))
  have htm : t ≤ e * (vv i₀ + (y - i₀)) := by
    rcases hterm with h | h
    · exact absurd h (by simp only [ee]; omega)
    · exact h
  have hv : vv i₀ ≤ Nat.log ℓ y := Nat.factorization_choose_le_log
  have hlog : ((Nat.log ℓ y : ℕ) : ℝ) ≤ Real.logb ℓ y := Real.natLog_le_logb y ℓ
  have hbl : (b : ℝ) / (ℓ : ℝ) ≤ (i₀ : ℝ) + 1 := by
    rw [div_le_iff₀ (by exact_mod_cast hℓpos)]
    exact_mod_cast (by linarith [hbi] : b ≤ (i₀ + 1) * ℓ)
  have hepos : (0 : ℝ) < (e : ℝ) := by exact_mod_cast (by omega : 0 < e)
  have hte : (t : ℝ) / (e : ℝ) ≤ ((vv i₀ + (y - i₀) : ℕ) : ℝ) := by
    rw [div_le_iff₀ hepos]
    have : (t : ℝ) ≤ ((e * (vv i₀ + (y - i₀)) : ℕ) : ℝ) := by exact_mod_cast htm
    rw [Nat.cast_mul] at this
    linarith
  rw [Nat.cast_add, Nat.cast_sub hi₀y.le] at hte
  have hvR : (vv i₀ : ℝ) ≤ (Nat.log ℓ y : ℝ) := by exact_mod_cast hv
  linarith

end Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains
end
end

section -- merged from Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.CancelC
noncomputable section

namespace Formalism.TruncatedSeriesCounting.R9

open PowerSeries

theorem mem_span_of_C_pow_mul : CancelC := by
  intro O _ _ a v t b g ha hvt hg
  rw [Ideal.mem_span_pair] at hg ⊢
  obtain ⟨p, q, hpq⟩ := hg
  have hdiv : (X : PowerSeries O) ^ b ∣ g - p * C (a ^ (t - v)) := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro n hn
    have h1 := congrArg (PowerSeries.coeff n) hpq
    simp only [map_add (f := _), PowerSeries.coeff_mul_C, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
      if_neg (show ¬ b ≤ n by omega), add_zero] at h1
    rw [map_sub, PowerSeries.coeff_mul_C, sub_eq_zero]
    apply mul_left_cancel₀ (pow_ne_zero v ha)
    rw [← h1]
    have ht : a ^ t = a ^ v * a ^ (t - v) := by rw [← pow_add, Nat.add_sub_cancel' hvt]
    rw [ht]
    ring
  obtain ⟨r, hr⟩ := hdiv
  exact ⟨p, r, by linear_combination (-1 : PowerSeries O) * hr⟩

end Formalism.TruncatedSeriesCounting.R9
end
end

section -- merged from Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.CancelQ
noncomputable section

namespace Formalism.TruncatedSeriesCounting.R9

open PowerSeries

theorem mem_span_of_X_pow_mul : CancelQ := by
  intro O _ _ a η b g hg
  rw [Ideal.mem_span_pair] at hg ⊢
  obtain ⟨F, G, hFG⟩ := hg
  have hX : (X : PowerSeries O) ^ η ≠ 0 := pow_ne_zero _ PowerSeries.X_ne_zero
  by_cases ha : a = 0
  · subst ha
    refine ⟨0, G, ?_⟩
    have h1 : (X : PowerSeries O) ^ η * (G * X ^ b) = X ^ η * g := by
      rw [← hFG, map_zero, mul_zero, zero_add, pow_add]
      ring
    rw [zero_mul, zero_add]
    exact mul_left_cancel₀ hX h1
  · have hdvd : (X : PowerSeries O) ^ η ∣ F := by
      rw [PowerSeries.X_pow_dvd_iff]
      intro m hm
      have h1 : (X : PowerSeries O) ^ η ∣ F * C a := by
        have h0 : F * C a = X ^ η * (g - G * X ^ b) := by
          rw [mul_sub, ← hFG, pow_add]
          ring
        rw [h0]
        exact dvd_mul_right _ _
      rw [PowerSeries.X_pow_dvd_iff] at h1
      have h2 := h1 m hm
      rw [mul_comm, PowerSeries.coeff_C_mul] at h2
      exact (mul_eq_zero.mp h2).resolve_left ha
    obtain ⟨F', rfl⟩ := hdvd
    refine ⟨F', G, ?_⟩
    apply mul_left_cancel₀ hX
    rw [← hFG, pow_add]
    ring

end Formalism.TruncatedSeriesCounting.R9
end
end

namespace Formalism.TruncatedSeriesCounting.WachCoordinates

end Formalism.TruncatedSeriesCounting.WachCoordinates

namespace Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains

theorem ramified_coefficient_chain_bounds : HCoef ∧ ExpBound ∧ MaxZeroExponentInequality ∧ TwoIntervalValuationSumBound ∧ LemmaGVal ∧ LemmaGIdeal ∧ RamifiedValuationInequality ∧ LenPi0 ∧ ColChain ∧ SubGen ∧ ColAssembly :=
  ⟨h_coefficient_bound, expBound_statement, second_exponent_bound, first_sigma_valuation_bound, g_coeff_valuation_statement, g_ideal_valuation_statement, ramified_valuation_inequality, length_pi_zero_bound, column_chain_bound, submodule_generator_count, column_assembly_bound⟩

end Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains

namespace Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities

end Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities

namespace Formalism.TruncatedSeriesCounting.tableLineDegreeTwo

end Formalism.TruncatedSeriesCounting.tableLineDegreeTwo

namespace Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingBounds

end Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingBounds

namespace Formalism.TruncatedSeriesCounting.R9

end Formalism.TruncatedSeriesCounting.R9

section -- restored from Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.QNumericalIdentity
namespace Formalism.TruncatedSeriesCounting.X

theorem q_numerical_identity : QaNum := by
  intro ℓ hℓ H' H eW hH heW
  unfold Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.aR Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.lam
  have hℓ1 : (1 : ℝ) < ℓ := by exact_mod_cast (by omega : 1 < ℓ)
  have hd : (0 : ℝ) < (ℓ : ℝ) - 1 := by linarith
  have hdiv : ((H' / (ℓ - 1) : ℕ) : ℝ) ≤ (H' : ℝ) / ((ℓ : ℝ) - 1) := by
    have h := Nat.cast_div_le (m := H') (n := ℓ - 1) (α := ℝ)
    rwa [Nat.cast_sub (by omega : 1 ≤ ℓ), Nat.cast_one] at h
  have hlog : Real.logb ℓ ((H' : ℝ) + 1) ≤ Real.logb ℓ (2 * (H : ℝ)) + 1 := by
    rcases Nat.eq_zero_or_pos H with h0 | hpos
    · subst h0
      have h0' : H' = 0 := by omega
      subst h0'
      simp
    · have h1 : (H' : ℝ) + 1 ≤ 2 * H := by
        have h2 : (H' : ℝ) ≤ H := by exact_mod_cast hH
        have h3 : (1 : ℝ) ≤ H := by exact_mod_cast hpos
        linarith
      have h4 := Real.logb_le_logb_of_le hℓ1 (by positivity) h1
      linarith
  have hfrac : (H' : ℝ) / ((ℓ : ℝ) - 1) + (H' : ℝ) * ℓ / ((ℓ : ℝ) - 1) ^ 2 ≤
      (H : ℝ) * (2 * ℓ - 1) / ((ℓ : ℝ) - 1) ^ 2 := by
    have heq : (H' : ℝ) / ((ℓ : ℝ) - 1) + (H' : ℝ) * ℓ / ((ℓ : ℝ) - 1) ^ 2 =
        (H' : ℝ) * (2 * ℓ - 1) / ((ℓ : ℝ) - 1) ^ 2 := by
      have := hd.ne'
      field_simp
      ring
    rw [heq]
    apply div_le_div_of_nonneg_right _ (pow_pos hd 2).le
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hH) (by linarith)
  push_cast
  linarith

end Formalism.TruncatedSeriesCounting.X
end

section -- restored from Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.UnitCoefficientPowerMod
noncomputable section

namespace Formalism.TruncatedSeriesCounting.X

open PowerSeries

theorem unit_coefficient_power_mod : UnitCoefficientPowerMod := by
  intro O _ ℓ ε u y
  have hsplit : ∃ W : PowerSeries O,
      (Formalism.WindowSums.p1 ℓ ε u) ^ y = (u * X ^ ℓ) ^ y + C (ℓ : O) * W := by
    obtain ⟨V, hV⟩ := sub_dvd_pow_sub_pow (Formalism.WindowSums.p1 ℓ ε u) (u * X ^ ℓ) y
    refine ⟨ε * V, ?_⟩
    have : Formalism.WindowSums.p1 ℓ ε u - u * X ^ ℓ = C (ℓ : O) * ε := by unfold Formalism.WindowSums.p1; ring
    rw [this] at hV
    linear_combination hV
  obtain ⟨W, hW⟩ := hsplit
  have hc : coeff (ℓ * y) ((Formalism.WindowSums.p1 ℓ ε u) ^ y) =
      constantCoeff u ^ y + (ℓ : O) * coeff (ℓ * y) W := by
    rw [hW, map_add (f := _), coeff_C_mul, mul_pow, ← pow_mul, mul_comm ℓ y]
    have := coeff_mul_X_pow (u ^ y) (y * ℓ) 0
    rw [zero_add] at this
    rw [this, coeff_zero_eq_constantCoeff, map_pow]
  refine ⟨?_, ?_⟩
  · rw [hc, add_sub_cancel_left, Ideal.mem_span_singleton]; exact dvd_mul_right _ _
  · intro hloc hℓ hu
    rw [hc]
    have h0 : IsUnit (constantCoeff u ^ y) := (hu.map constantCoeff).pow y
    have h1 : (ℓ : O) * coeff (ℓ * y) W ∈ IsLocalRing.maximalIdeal O :=
      Ideal.mul_mem_right _ _ ((IsLocalRing.mem_maximalIdeal _).mpr hℓ)
    by_contra hne
    have h2 : constantCoeff u ^ y + (ℓ : O) * coeff (ℓ * y) W ∈ IsLocalRing.maximalIdeal O :=
      (IsLocalRing.mem_maximalIdeal _).mpr hne
    have h3 := Ideal.sub_mem _ h2 h1
    rw [add_sub_cancel_right] at h3
    exact ((IsLocalRing.mem_maximalIdeal _).mp h3) h0

end Formalism.TruncatedSeriesCounting.X
end
end

namespace Formalism.TruncatedSeriesCounting.X

theorem pX_conditions : QaNum ∧ TruncSig ∧ TruncRem1 ∧ ArcExp ∧ SatA ∧ UnitCoefficientPowerMod :=
  ⟨q_numerical_identity, truncation_signature_bound, truncation_remainder_bound, arc_exponential_identity, saturation_criterion, unit_coefficient_power_mod⟩

end Formalism.TruncatedSeriesCounting.X
