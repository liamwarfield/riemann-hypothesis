module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsNormSubEqOne
open NumberField

namespace GlobalTheory.SplitEmbSep

theorem _root_.GlobalTheory.SplitEmbSep.norm_le_one_of_isIntegral {C : Type*} [NormedField C] [IsUltrametricDist C]
    {x : C} (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  obtain ⟨p, hm, hp⟩ := hx
  by_contra h
  push_neg at h
  rw [← Polynomial.aeval_def, hm.as_sum] at hp
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_add (f := _), map_pow, Polynomial.aeval_X, map_sum, map_mul, Polynomial.aeval_C,
    algebraMap_int_eq, eq_intCast, map_intCast] at hp
  set n := p.natDegree
  rcases Nat.eq_zero_or_pos n with hn | hn
  · rw [hn] at hp
    simp at hp
  have hs : (Finset.range n).Nonempty := Finset.nonempty_range_iff.mpr hn.ne'
  obtain ⟨i, hi, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty hs
    (fun i => ((p.coeff i : ℤ) : C) * x ^ i)
  have hxn : x ^ n = -∑ i ∈ Finset.range n, ((p.coeff i : ℤ) : C) * x ^ i :=
    eq_neg_of_add_eq_zero_left hp
  have h1 : ‖x‖ ^ n ≤ ‖x‖ ^ i := by
    calc ‖x‖ ^ n = ‖x ^ n‖ := (norm_pow x n).symm
      _ = ‖∑ i ∈ Finset.range n, ((p.coeff i : ℤ) : C) * x ^ i‖ := by rw [hxn, norm_neg]
      _ ≤ ‖((p.coeff i : ℤ) : C) * x ^ i‖ := hle
      _ = ‖((p.coeff i : ℤ) : C)‖ * ‖x‖ ^ i := by rw [norm_mul, norm_pow]
      _ ≤ 1 * ‖x‖ ^ i := by
        gcongr
        exact IsUltrametricDist.norm_intCast_le_one C _
      _ = ‖x‖ ^ i := one_mul _
  have h2 : ‖x‖ ^ i < ‖x‖ ^ n := pow_lt_pow_right₀ h (Finset.mem_range.mp hi)
  exact absurd h1 (not_le.mpr h2)

theorem _root_.GlobalTheory.SplitEmbSep.norm_det_lt_one {C ι : Type*} [NormedField C] [IsUltrametricDist C]
    [Fintype ι] [DecidableEq ι] (M : Matrix ι ι C) (hM : ∀ i j, ‖M i j‖ ≤ 1) (k : ι)
    (hk : ∀ i, ‖M i k‖ < 1) : ‖M.det‖ < 1 := by
  rw [Matrix.det_apply]
  obtain ⟨σ, -, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty
    (Finset.univ_nonempty (α := Equiv.Perm ι))
    (fun σ => Equiv.Perm.sign σ • ∏ i, M (σ i) i)
  refine lt_of_le_of_lt hle ?_
  have hprod : ‖∏ i, M (σ i) i‖ < 1 := by
    rw [norm_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
    exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) (hk _)
      (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun i _ => hM _ _))
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;>
    simpa [hs, Units.smul_def] using hprod

theorem _root_.GlobalTheory.SplitEmbSep.one_le_norm_intCast {C : Type*} [NormedField C] [IsUltrametricDist C] {g : ℕ}
    (hg : g.Prime) (hgC : ‖(g : C)‖ < 1) {d : ℤ} (hd : ¬ (g : ℤ) ∣ d) : 1 ≤ ‖(d : C)‖ := by
  obtain ⟨a, b, hab⟩ :=
    ((Nat.prime_iff_prime_int.mp hg).irreducible.coprime_iff_not_dvd).mpr hd
  have hC : (a : C) * (g : C) + (b : C) * (d : C) = 1 := by exact_mod_cast congrArg (Int.cast (R := C)) hab
  have h1 : ‖(a : C) * (g : C)‖ < 1 := by
    rw [norm_mul]
    calc ‖(a : C)‖ * ‖(g : C)‖ ≤ 1 * ‖(g : C)‖ := by
          gcongr
          exact IsUltrametricDist.norm_intCast_le_one C a
      _ < 1 := by rwa [one_mul]
  have h2 : 1 ≤ max ‖(a : C) * (g : C)‖ ‖(b : C) * (d : C)‖ := by
    rw [← norm_one (α := C), ← hC]
    exact IsUltrametricDist.norm_add_le_max _ _
  have h3 : 1 ≤ ‖(b : C) * (d : C)‖ := by
    rcases le_max_iff.mp h2 with h | h
    · exact absurd h (not_le.mpr h1)
    · exact h
  calc 1 ≤ ‖(b : C)‖ * ‖(d : C)‖ := by rwa [← norm_mul]
    _ ≤ 1 * ‖(d : C)‖ := by
      gcongr
      exact IsUltrametricDist.norm_intCast_le_one C b
    _ = ‖(d : C)‖ := one_mul _

theorem _root_.GlobalTheory.SplitEmbSep.not_dvd_discr_of_split {g : ℕ} (hg : g.Prime) (E : Type*) [Field E]
    [NumberField E]
    (h : (Ideal.primesOver (Ideal.span {(g : ℤ)}) (𝓞 E)).ncard = Module.finrank ℚ E) :
    ¬ (g : ℤ) ∣ discr E := by
  have hgp : Prime (g : ℤ) := Nat.prime_iff_prime_int.mp hg
  set p : Ideal ℤ := Ideal.span {(g : ℤ)} with hp_def
  have hp0 : p ≠ ⊥ := by simpa [hp_def] using hgp.ne_zero
  haveI hpprime : p.IsPrime := (Ideal.span_singleton_prime hgp.ne_zero).mpr hgp
  haveI hpmax : p.IsMaximal := hpprime.isMaximal hp0
  have hsum := Ideal.sum_ramification_inertia (𝓞 E) ℚ E hp0
  have hcard : (IsDedekindDomain.primesOverFinset p (𝓞 E)).card = Module.finrank ℚ E := by
    rw [← h, ← IsDedekindDomain.coe_primesOverFinset hp0, Set.ncard_coe_finset]
  have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) p ≠ ⊥ := by
    rw [Ne, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective ℤ (𝓞 E))]
    exact hp0
  have hge : ∀ P ∈ IsDedekindDomain.primesOverFinset p (𝓞 E),
      1 ≤ p.ramificationIdx' P * p.inertiaDeg' P := by
    intro P hP
    have hP' : P ∈ p.primesOver (𝓞 E) := by
      rw [← IsDedekindDomain.coe_primesOverFinset hp0]
      exact hP
    haveI := hP'.1
    haveI := hP'.2
    have he : p.ramificationIdx' P ≠ 0 :=
      Ideal.IsDedekindDomain.ramificationIdx'_ne_zero hmap hP'.1
        (Ideal.map_le_iff_le_comap.mpr (le_of_eq (Ideal.over_def P p)))
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero he (Ideal.inertiaDeg'_pos p P).ne')
  have hone := (Finset.sum_eq_sum_iff_of_le hge).mp (by
    rw [← Finset.card_eq_sum_ones, hcard, hsum])
  rw [NumberField.not_dvd_discr_iff_forall_mem E (𝓞 E) hgp]
  intro P hPprime hgP
  have hunder : p = P.under ℤ := by
    have hle : p ≤ P.under ℤ := by
      rw [hp_def, Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.mem_comap.mpr (by simpa using hgP)
    exact hpmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) hle
  haveI : P.LiesOver p := ⟨hunder⟩
  have hPF : P ∈ IsDedekindDomain.primesOverFinset p (𝓞 E) := by
    rw [← Finset.mem_coe, IsDedekindDomain.coe_primesOverFinset hp0]
    exact ⟨hPprime, this⟩
  have he := Nat.eq_one_of_mul_eq_one_right (hone P hPF).symm
  rw [Algebra.isUnramifiedAt_iff_of_isDedekindDomain,
    ← Ideal.ramificationIdx'_eq_ramificationIdx p P hp0]
  exact he

end GlobalTheory.SplitEmbSep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumPrimeLogDivPredLeLogAdd
namespace GlobalTheory.PrimeLogSum
open Finset

private lemma log_three_lt_one_point_one_one : Real.log 3 < 1.11 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have h1 := Real.exp_one_gt_d9
  have h2 := Real.add_one_le_exp 0.11
  have h3 : Real.exp 1.11 = Real.exp 1 * Real.exp 0.11 := by
    rw [← Real.exp_add]; norm_num
  rw [h3]
  nlinarith

private lemma log_succ_div_le_telescoping_sub (n : ℕ) (hn : 3 ≤ n) :
    Real.log ((n + 1 : ℕ) : ℝ) / (((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) - 1))
      ≤ (Real.log n + 4 / 3) / n - (Real.log ((n + 1 : ℕ) : ℝ) + 4 / 3) / ((n + 1 : ℕ) : ℝ) := by
  push_cast
  set x : ℝ := (n : ℝ) with hx
  have hx3 : (3 : ℝ) ≤ x := by rw [hx]; exact_mod_cast hn
  have hx0 : 0 < x := by linarith
  have hd : Real.log (x + 1) - Real.log x ≤ 1 / x := by
    have h := Real.log_le_sub_one_of_pos (show 0 < (x + 1) / x by positivity)
    rw [Real.log_div (by positivity) hx0.ne'] at h
    have : (x + 1) / x - 1 = 1 / x := by field_simp; ring
    linarith
  have h1 : (x + 1) * (Real.log (x + 1) - Real.log x) ≤ (x + 1) * (1 / x) :=
    mul_le_mul_of_nonneg_left hd (by linarith)
  have h2 : (x + 1) * (1 / x) ≤ 4 / 3 := by
    rw [mul_one_div, div_le_iff₀ hx0]; linarith
  have key : Real.log (x + 1)
      ≤ (x + 1) * (Real.log x + 4 / 3) - x * (Real.log (x + 1) + 4 / 3) := by
    nlinarith
  have hpos : 0 < (x + 1) * x := by positivity
  calc Real.log (x + 1) / ((x + 1) * (x + 1 - 1))
      = Real.log (x + 1) / ((x + 1) * x) := by ring_nf
    _ ≤ ((x + 1) * (Real.log x + 4 / 3) - x * (Real.log (x + 1) + 4 / 3)) / ((x + 1) * x) :=
        div_le_div_of_nonneg_right key hpos.le
    _ = (Real.log x + 4 / 3) / x - (Real.log (x + 1) + 4 / 3) / (x + 1) := by
        field_simp

private lemma sum_log_div_mul_pred_add_le_const (N : ℕ) (hN : 3 ≤ N) :
    ∑ n ∈ Finset.range (N + 1), Real.log n / ((n : ℝ) * ((n : ℝ) - 1)) + (Real.log N + 4 / 3) / N
      ≤ Real.log 2 / 2 + Real.log 3 / 6 + (Real.log 3 + 4 / 3) / 3 := by
  induction N, hN using Nat.le_induction with
  | base =>
    simp [Finset.sum_range_succ]
    norm_num
  | succ n hn ih =>
    rw [Finset.sum_range_succ]
    have := log_succ_div_le_telescoping_sub n hn
    linarith

private lemma div_le_factorization_factorial' (N p : ℕ) (hp : p.Prime) :
    N / p ≤ (N.factorial).factorization p := by
  rw [Nat.factorization_factorial hp (lt_add_one (Nat.log p N))]
  rcases Nat.lt_or_ge N p with h | h
  · simp [Nat.div_eq_of_lt h]
  · have h1 : 1 ∈ Ico 1 (Nat.log p N + 1) := by
      simp [Nat.log_pos hp.one_lt h]
    simpa using single_le_sum (f := fun i => N / p ^ i) (fun _ _ => Nat.zero_le _) h1

private lemma mul_sum_prime_log_div_le_log_factorial_add (N : ℕ) :
    (N : ℝ) * ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, Real.log p / p
      ≤ Real.log (N.factorial : ℝ) + N * Real.log 4 := by
  set P := (Finset.range (N + 1)).filter Nat.Prime with hP
  have hfac : Real.log (N.factorial : ℝ)
      = ∑ p ∈ P, ((N.factorial).factorization p : ℝ) * Real.log p := by
    rw [Real.log_nat_eq_sum_factorization]
    apply Finsupp.sum_of_support_subset
    · intro p hp
      rw [Nat.support_factorization, Nat.mem_primeFactors] at hp
      simp only [hP, Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.lt_succ_of_le ((hp.1.dvd_factorial).1 hp.2.1), hp.1⟩
    · intro i _
      simp
  have htheta : ∑ p ∈ P, Real.log p ≤ N * Real.log 4 := by
    rw [← Real.log_prod (fun p hp => by
      have := (Finset.mem_filter.1 hp).2.pos
      positivity), ← Real.log_pow]
    apply Real.log_le_log
    · exact Finset.prod_pos fun p hp => by
        have := (Finset.mem_filter.1 hp).2.pos
        positivity
    · have h := primorial_le_four_pow N
      have h' : ((primorial N : ℕ) : ℝ) ≤ ((4 ^ N : ℕ) : ℝ) := by exact_mod_cast h
      simpa [primorial, hP, Nat.cast_prod] using h'
  rw [Finset.mul_sum, hfac]
  calc ∑ p ∈ P, (N : ℝ) * (Real.log p / p)
      ≤ ∑ p ∈ P, (((N.factorial).factorization p : ℝ) * Real.log p + Real.log p) := by
        apply Finset.sum_le_sum
        intro p hp
        have hp' := (Finset.mem_filter.1 hp).2
        have hp0 : (0 : ℝ) < p := by exact_mod_cast hp'.pos
        have hlog : 0 ≤ Real.log p := Real.log_natCast_nonneg p
        have hv : ((N / p : ℕ) : ℝ) ≤ ((N.factorial).factorization p : ℝ) := by
          exact_mod_cast div_le_factorization_factorial' N p hp'
        have hlt : (N : ℝ) < ((N / p : ℕ) : ℝ) * p + p := by
          exact_mod_cast Nat.lt_div_mul_add hp'.pos
        have hq : (N : ℝ) / p ≤ ((N.factorial).factorization p : ℝ) + 1 := by
          rw [div_le_iff₀ hp0]
          nlinarith
        calc (N : ℝ) * (Real.log p / p) = (N : ℝ) / p * Real.log p := by ring
          _ ≤ (((N.factorial).factorization p : ℝ) + 1) * Real.log p :=
            mul_le_mul_of_nonneg_right hq hlog
          _ = _ := by ring
    _ = ∑ p ∈ P, ((N.factorial).factorization p : ℝ) * Real.log p + ∑ p ∈ P, Real.log p :=
        Finset.sum_add_distrib
    _ ≤ _ := by linarith

private lemma log_factorial_le_stirling_bound (n : ℕ) (hn : 1 ≤ n) :
    Real.log (n.factorial : ℝ) ≤ n * Real.log n - n + 1 + Real.log n / 2 := by
  have h1 : Real.log (Stirling.stirlingSeq n) ≤ Real.log (Stirling.stirlingSeq 1) := by
    have := Stirling.log_stirlingSeq'_antitone (Nat.zero_le (n - 1))
    simpa [Function.comp, Nat.sub_add_cancel hn] using this
  rw [Stirling.log_stirlingSeq_formula, Stirling.log_stirlingSeq_formula] at h1
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  rw [Real.log_mul (by norm_num) hn0, Real.log_div hn0 (Real.exp_pos 1).ne', Real.log_exp] at h1
  simp only [Nat.factorial_one, Nat.cast_one, mul_one, Real.log_one, one_div, Real.log_inv,
    Real.log_exp] at h1
  linarith [h1]

theorem _root_.GlobalTheory.PrimeLogSum.sum_log_div_pred_le : ∀ N : ℕ,
    ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, Real.log p / ((p : ℝ) - 1)
      ≤ Real.log N + 2.2 := by
  intro N
  have hl2 := Real.log_two_lt_d9
  have hl3 := log_three_lt_one_point_one_one
  have hl3' : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  rcases Nat.lt_or_ge N 4 with hN | hN
  · interval_cases N <;>
      simp [Finset.sum_filter, Finset.sum_range_succ, Nat.prime_two, Nat.prime_three] <;>
      norm_num <;> linarith
  set P := (Finset.range (N + 1)).filter Nat.Prime with hP
  have hsplit : ∑ p ∈ P, Real.log p / ((p : ℝ) - 1)
      = ∑ p ∈ P, Real.log p / p + ∑ p ∈ P, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.1 hp).2.two_le
    have h3 : (p : ℝ) - 1 ≠ 0 := by linarith
    have h4 : (p : ℝ) ≠ 0 := by linarith
    field_simp
    ring
  have hB : ∑ p ∈ P, Real.log p / ((p : ℝ) * ((p : ℝ) - 1))
      ≤ ∑ n ∈ Finset.range (N + 1), Real.log n / ((n : ℝ) * ((n : ℝ) - 1)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro n _ _
    apply div_nonneg (Real.log_natCast_nonneg n)
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h]
    · have : (1 : ℝ) ≤ n := by exact_mod_cast h
      exact mul_nonneg (by linarith) (by linarith)
  have hC := sum_log_div_mul_pred_add_le_const N (by omega)
  have hg : 0 ≤ (Real.log N + 4 / 3) / N :=
    div_nonneg (by linarith [Real.log_natCast_nonneg N]) (Nat.cast_nonneg N)
  have hA := mul_sum_prime_log_div_le_log_factorial_add N
  have hF := log_factorial_le_stirling_bound N (by omega)
  have hN4 : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hlogN : Real.log N ≤ 0.4 * N := by
    have h := Real.log_le_sub_one_of_pos (show 0 < (N : ℝ) / Real.exp 1 by positivity)
    rw [Real.log_div hNpos.ne' (Real.exp_pos 1).ne', Real.log_exp] at h
    have he := Real.exp_one_gt_d9
    have h5 : (N : ℝ) / Real.exp 1 ≤ 0.4 * N := by
      rw [div_le_iff₀ (Real.exp_pos 1)]
      nlinarith
    linarith
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hA' : ∑ p ∈ P, Real.log p / p ≤ Real.log N - 1 + 0.25 + 0.2 + Real.log 4 := by
    have h : (N : ℝ) * ∑ p ∈ P, Real.log p / p
        ≤ N * (Real.log N - 1 + 0.25 + 0.2 + Real.log 4) := by
      linarith
    exact le_of_mul_le_mul_left h hNpos
  rw [hsplit]
  linarith

end GlobalTheory.PrimeLogSum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsDualFormsOfSeparatedTypes
namespace GlobalTheory

theorem exists_matrix_fix_type_kill {O A : Type} [CommRing O] {d : ℕ}
    (ρ : A → Matrix (Fin d) (Fin d) O) {T : Type} [DecidableEq T] {r : T → ℕ} (σ : T → A → O)
    (u : (Σ t : T, Fin (r t)) → Fin d → O)
    (hsep : ∀ t t', t ≠ t' → ∃ a, IsUnit (σ t a - σ t' a))
    (heig : ∀ a l, (ρ a).mulVec (u l) = σ l.1 a • u l) (t₀ : T) (S : Finset T) (hS : t₀ ∉ S) :
    ∃ P : Matrix (Fin d) (Fin d) O, (∀ l, l.1 = t₀ → P.mulVec (u l) = u l) ∧
      (∀ l, l.1 ∈ S → P.mulVec (u l) = 0) := by
  induction S using Finset.induction_on with
  | empty => exact ⟨1, fun l _ => Matrix.one_mulVec _, fun l hl => absurd hl (by simp)⟩
  | insert t S htS ih =>
    obtain ⟨P, hP1, hP2⟩ := ih (fun h => hS (Finset.mem_insert_of_mem h))
    have hne : t₀ ≠ t := fun h => hS (h ▸ Finset.mem_insert_self t S)
    obtain ⟨a, c, hc⟩ := hsep t₀ t hne
    have key : ∀ l, (P * ((↑c⁻¹ : O) • (ρ a - σ t a • (1 : Matrix (Fin d) (Fin d) O)))).mulVec (u l)
        = ((↑c⁻¹ : O) * (σ l.1 a - σ t a)) • P.mulVec (u l) := by
      intro l
      rw [← Matrix.mulVec_mulVec, Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
        Matrix.one_mulVec, heig, ← sub_smul, smul_smul, Matrix.mulVec_smul]
    refine ⟨P * ((↑c⁻¹ : O) • (ρ a - σ t a • (1 : Matrix (Fin d) (Fin d) O))),
      fun l hl => ?_, fun l hl => ?_⟩
    · rw [key, hP1 l hl, hl, ← hc, Units.inv_mul, one_smul]
    · rw [key]
      rcases Finset.mem_insert.mp hl with h | h
      · rw [h, sub_self, mul_zero, zero_smul]
      · rw [hP2 l h, smul_zero]

theorem exists_dual_forms_of_separated_types :
    ∀ (O A : Type) [CommRing O] (d : ℕ) (ρ : A → Matrix (Fin d) (Fin d) O) (T : Type) [Fintype T] [DecidableEq T] (r : T → ℕ) (σ : T → A → O) (u : (Σ t : T, Fin (r t)) → Fin d → O), (∀ t t', t ≠ t' → ∃ a, IsUnit (σ t a - σ t' a)) → (∀ a l, (ρ a).mulVec (u l) = σ l.1 a • u l) → (∀ t, ∃ lam : Fin (r t) → Fin d → O, ∀ i i', ∑ s, lam i s * u ⟨t, i'⟩ s = if i = i' then 1 else 0) → ∃ lam : (Σ t : T, Fin (r t)) → Fin d → O, ∀ l l', ∑ s, lam l s * u l' s = if l = l' then 1 else 0 := by
  intro O A _ d ρ T _ _ r σ u hsep heig hdual
  choose lam hlam using hdual
  choose P hP1 hP2 using fun t₀ : T =>
    exists_matrix_fix_type_kill ρ σ u hsep heig t₀ (Finset.univ.erase t₀) (by simp)
  refine ⟨fun l => Matrix.vecMul (lam l.1 l.2) (P l.1), ?_⟩
  rintro ⟨t, i⟩ ⟨t', i'⟩
  change Matrix.vecMul (lam t i) (P t) ⬝ᵥ u ⟨t', i'⟩ = _
  rw [← Matrix.dotProduct_mulVec]
  by_cases h : t' = t
  · subst h
    rw [hP1 t' ⟨t', i'⟩ rfl]
    have := hlam t' i i'
    simpa [dotProduct] using this
  · rw [hP2 t ⟨t', i'⟩ (by simpa using h), dotProduct_zero, if_neg]
    intro h'
    exact h (congrArg Sigma.fst h').symm

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsGeneratingCharacters
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsExtensionCharacter
namespace GlobalTheory.ExtensionCharacter

theorem units_zpow_surjective {F : Type} [Field F] [IsAlgClosed F] {n : ℤ} (hn : n ≠ 0) :
    Function.Surjective (fun u : Fˣ => u ^ n) := by
  intro x
  have hpos : 0 < n.natAbs := Int.natAbs_pos.mpr hn
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq ((x : F)) hpos
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hpos.ne'] at hz
    exact x.ne_zero hz.symm
  have hu : (Units.mk0 z hz0) ^ n.natAbs = x := by
    ext; simp [hz]
  rcases Int.natAbs_eq n with h | h
  · refine ⟨Units.mk0 z hz0, ?_⟩
    simp only
    rw [h, zpow_natCast, hu]
  · refine ⟨(Units.mk0 z hz0)⁻¹, ?_⟩
    simp only
    rw [h, inv_zpow', neg_neg, zpow_natCast, hu]

noncomputable instance divisibleUnits (F : Type) [Field F] [IsAlgClosed F] :
    DivisibleBy (Additive Fˣ) ℤ :=
  divisibleByOfSMulRightSurj _ _ fun {n} hn x => by
    obtain ⟨y, hy⟩ := units_zpow_surjective (F := F) hn (Additive.toMul x)
    exact ⟨Additive.ofMul y, by simpa [ofMul_zpow] using congrArg Additive.ofMul hy⟩

theorem exists_extension_character : ∀ {H M F : Type} [inst : CommGroup H] [inst_1 : CommGroup M]
    [inst_2 : Field F] [IsAlgClosed F] (Φ : H →* M), Function.Injective (⇑Φ : H → M) →
    ∀ (χ : H →* Fˣ), ∃ (κ : M →* Fˣ), ∀ (x : H), (κ : M → Fˣ) ((Φ : H → M) x) = (χ : H → Fˣ) x := by
  intro H M F _ _ _ _ Φ hΦ χ
  obtain ⟨h, hh⟩ := (Module.Baer.of_divisible (Additive Fˣ)).extension_property_addMonoidHom
    (MonoidHom.toAdditive Φ) hΦ (MonoidHom.toAdditive χ)
  refine ⟨MonoidHom.toAdditive.symm h, fun x => ?_⟩
  have := DFunLike.congr_fun hh (Additive.ofMul x)
  exact this

end GlobalTheory.ExtensionCharacter
end

namespace GlobalTheory.PrimaryCharacter

theorem exists_extend_of_injective {H M F : Type} [CommGroup H] [CommGroup M] [Field F] [IsAlgClosed F]
    (Φ : H →* M) (hΦ : Function.Injective Φ) (χ : H →* Fˣ) : ∃ κ : M →* Fˣ, ∀ x, κ (Φ x) = χ x := by
  apply _root_.GlobalTheory.ExtensionCharacter.exists_extension_character <;> assumption

theorem exists_factor_of_ker_le {H M F : Type} [CommGroup H] [CommGroup M] [Field F] [IsAlgClosed F]
    (Φ : H →* M) (χ : H →* Fˣ) (h : Φ.ker ≤ χ.ker) : ∃ κ : M →* Fˣ, ∀ x, κ (Φ x) = χ x := by
  obtain ⟨κ, hκ⟩ := exists_extend_of_injective (QuotientGroup.kerLift Φ)
    (QuotientGroup.kerLift_injective Φ) (QuotientGroup.lift Φ.ker χ h)
  exact ⟨κ, fun x => hκ (QuotientGroup.mk x)⟩

end GlobalTheory.PrimaryCharacter
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ReInnerLeOnImageOfIntertwining
open Finset
open scoped InnerProductSpace

namespace GlobalTheory

theorem re_inner_sum_eigen_le {N ι : Type} [NormedAddCommGroup N] [InnerProductSpace ℂ N]
    [Fintype ι] (B : N →ₗ[ℂ] N) (hB : B.IsSymmetric) (C : ℝ) (v : ι → N) (l : ι → ℝ)
    (hv : ∀ i, B (v i) = (l i : ℂ) • v i) (hl : ∀ i, l i ≤ C) :
    (⟪∑ i, v i, B (∑ i, v i)⟫_ℂ).re ≤ C * ‖∑ i, v i‖ ^ 2 := by
  have key : ∀ i j, ((C : ℂ) - l j) * ⟪v i, v j⟫_ℂ =
      ⟪((√(C - l i) : ℝ) : ℂ) • v i, ((√(C - l j) : ℝ) : ℂ) • v j⟫_ℂ := by
    intro i j
    rw [inner_smul_left, inner_smul_right, Complex.conj_ofReal, ← mul_assoc]
    by_cases h : l i = l j
    · rw [h, ← Complex.ofReal_mul, Real.mul_self_sqrt (sub_nonneg.2 (hl j))]
      push_cast
      rfl
    · have h1 := hB (v i) (v j)
      rw [hv, hv, inner_smul_left, inner_smul_right, Complex.conj_ofReal] at h1
      have h2 : ((l i : ℂ) - l j) * ⟪v i, v j⟫_ℂ = 0 := by rw [sub_mul, h1, sub_self]
      have h3 : ((l i : ℂ) - l j) ≠ 0 := by
        rw [sub_ne_zero]; exact_mod_cast h
      have h4 : ⟪v i, v j⟫_ℂ = 0 := (mul_eq_zero.1 h2).resolve_left h3
      rw [h4, mul_zero, mul_zero]
  have hsum : (C : ℂ) * ⟪∑ i, v i, ∑ i, v i⟫_ℂ - ⟪∑ i, v i, B (∑ i, v i)⟫_ℂ =
      ⟪∑ i, ((√(C - l i) : ℝ) : ℂ) • v i, ∑ i, ((√(C - l i) : ℝ) : ℂ) • v i⟫_ℂ := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [sum_inner, inner_sum, ← key, hv, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [inner_smul_right, sub_mul]
  have hre := congrArg Complex.re hsum
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at hre
  simp only [Complex.coe_algebraMap, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
    Complex.sub_re, Complex.ofReal_re] at hre
  nlinarith [sq_nonneg ‖∑ i, ((√(C - l i) : ℝ) : ℂ) • v i‖]

theorem re_inner_le_on_image_of_intertwining :
    ∀ (T N : Type) [NormedAddCommGroup T] [InnerProductSpace ℂ T] [FiniteDimensional ℂ T]
      [NormedAddCommGroup N] [InnerProductSpace ℂ N] (Φ : T →ₗ[ℂ] N) (A : T →ₗ[ℂ] T)
      (B : N →ₗ[ℂ] N) (C : ℝ), A.IsSymmetric → B.IsSymmetric → (∀ x, Φ (A x) = B (Φ x)) →
      (∀ x, (⟪x, A x⟫_ℂ).re ≤ C * ‖x‖ ^ 2) →
      ∀ x, (⟪Φ x, B (Φ x)⟫_ℂ).re ≤ C * ‖Φ x‖ ^ 2 := by
  intro T N _ _ _ _ _ Φ A B C hA hB hΦ hC x
  set b := hA.eigenvectorBasis (n := Module.finrank ℂ T) rfl with hb
  set l := hA.eigenvalues (n := Module.finrank ℂ T) rfl with hl
  have hAb : ∀ i, A (b i) = (l i : ℂ) • b i := fun i => hA.apply_eigenvectorBasis rfl i
  have hle : ∀ i, l i ≤ C := by
    intro i
    have h := hC (b i)
    rw [hAb, inner_smul_right, inner_self_eq_norm_sq_to_K, b.orthonormal.1 i] at h
    simpa using h
  have hx : Φ x = ∑ i, Φ (b.repr x i • b i) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, b.sum_repr]
  rw [hx]
  refine re_inner_sum_eigen_le B hB C _ l (fun i => ?_) hle
  rw [← hΦ, map_smul A, hAb, smul_comm, map_smul]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumStarProjectionEigenspaceEqSelfOfEigenvaluesLi
namespace GlobalTheory

open Module

theorem _root_.GlobalTheory.ev_starProjection_eigenspace_eq_residue :
    ∀ (Y : Type) [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y] (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (t : ℕ) (m : Fin t → ℂ) (s : ℂ) (Om : Module.End ℂ Y) (ev : Y →ₗ[ℂ] V) (K : ℂ → (Y →ₗ[ℂ] V)) (q : ℂ → ℂ) (y : Y) (v : V) (l : Fin t), Function.Injective m → Om.IsSymmetric → (∀ (lam : ℂ) (x : Y), x ≠ 0 → Om x = lam • x → ∃ j, lam = m j + s) → (∀ (u : ℂ) (x : Y), K u ((u - s) • x + Om x) = (∏ j, (u + m j)) • ev x) → Continuous q → (∀ u, K u y = q u • v) → ev ((Module.End.eigenspace Om (m l + s)).starProjection y) = (q (-m l) / ∏ j ∈ Finset.univ.erase l, (m j - m l)) • v := by
  intro Y _ _ _ V _ _ t m s Om ev K q y v l hm hOm hspec hK hq hKy
  set P : Fin t → Y → Y := fun j x => (Module.End.eigenspace Om (m j + s)).starProjection x with hP
  set c : Fin t → ℂ → ℂ := fun j u => ∏ k ∈ Finset.univ.erase j, (u + m k) with hc
  have key : ∀ x : Y, ∀ u : ℂ, (∏ k, (u + m k)) • K u x = (∏ k, (u + m k)) • ∑ j, c j u • ev (P j x) := by
    intro x u
    have hx : x ∈ ⨆ μ, Module.End.eigenspace Om μ := by
      rw [Submodule.orthogonal_eq_bot_iff.mp hOm.orthogonalComplement_iSup_eigenspaces_eq_bot]
      exact Submodule.mem_top
    refine Submodule.iSup_induction (fun μ => Module.End.eigenspace Om μ) (motive := fun x => (∏ k, (u + m k)) • K u x = (∏ k, (u + m k)) • ∑ j, c j u • ev (P j x)) hx ?_ ?_ ?_
    · intro μ x hxμ
      by_cases hx0 : x = 0
      · subst hx0; simp [hP]
      have hOmx : Om x = μ • x := Module.End.mem_eigenspace_iff.mp hxμ
      obtain ⟨i, rfl⟩ := hspec μ x hx0 hOmx
      have hPx : ∀ j, P j x = if j = i then x else 0 := by
        intro j
        split_ifs with hji
        · subst hji; exact Submodule.starProjection_eq_self_iff.mpr hxμ
        · have hne : m j + s ≠ m i + s := fun h => hji (hm (add_right_cancel h))
          have hortho := hOm.orthogonalFamily_eigenspaces.isOrtho hne
          exact (Submodule.starProjection_apply_eq_zero_iff _).mpr (hortho.symm hxμ)
      have hsum : ∑ j, c j u • ev (P j x) = c i u • ev x := by
        rw [Finset.sum_eq_single i (fun j _ hji => by rw [hPx, if_neg hji, map_zero, smul_zero]) (by simp), hPx, if_pos rfl]
      have hKx : (u + m i) • K u x = (∏ k, (u + m k)) • ev x := by
        rw [← hK u x, hOmx, ← map_smul]
        congr 1
        rw [← add_smul]; congr 1; ring
      have hprod : ∏ k, (u + m k) = c i u * (u + m i) := by
        simp only [hc]; exact (Finset.prod_erase_mul _ _ (Finset.mem_univ i)).symm
      rw [hsum, smul_comm (∏ k, (u + m k)) (c i u), ← hKx, hprod, mul_smul]
    · simp [hP]
    · intro x₁ x₂ h₁ h₂
      simp only [hP] at h₁ h₂ ⊢
      simp only [map_add (f := _), smul_add, Finset.sum_add_distrib, h₁, h₂]
  have hgen : ∀ u, ∏ k, (u + m k) ≠ 0 → q u • v = ∑ j, c j u • ev (P j y) := by
    intro u hu
    rw [← hKy]
    exact smul_right_injective V hu (key y u)
  have hdense : Dense {u : ℂ | ∏ k, (u + m k) ≠ 0} := by
    have hfin : {u : ℂ | ∏ k, (u + m k) = 0}.Countable := by
      apply Set.Finite.countable
      apply (Set.finite_range (fun k => -m k)).subset
      intro u hu
      simp only [Set.mem_setOf_eq, Finset.prod_eq_zero_iff, Finset.mem_univ, true_and] at hu
      obtain ⟨k, hk⟩ := hu
      exact ⟨k, by linear_combination -hk⟩
    simpa [Set.compl_setOf] using hfin.dense_compl ℝ
  have hcont : Continuous fun u => ∑ j, c j u • ev (P j y) := by
    simp only [hc]; fun_prop
  have hf : Continuous fun u => q u • v := hq.smul continuous_const
  have hl := congrFun (Continuous.ext_on hdense hf hcont hgen) (-m l)
  rw [Finset.sum_eq_single l (fun j _ hjl => by
    simp only [hc]
    rw [Finset.prod_eq_zero (i := l) (Finset.mem_erase.mpr ⟨Ne.symm hjl, Finset.mem_univ l⟩) (by ring), zero_smul]) (by simp)] at hl
  have hcl : c l (-m l) = ∏ j ∈ Finset.univ.erase l, (m j - m l) :=
    Finset.prod_congr rfl (fun k _ => by ring)
  have hD : ∏ j ∈ Finset.univ.erase l, (m j - m l) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j hj => sub_ne_zero.mpr (hm.ne (Finset.ne_of_mem_erase hj)))
  rw [hcl] at hl
  change ev (P l y) = _
  rw [div_eq_inv_mul, mul_smul, hl, smul_smul, inv_mul_cancel₀ hD, one_smul]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IteratedFDerivProdCoordAt
open scoped BigOperators

namespace GlobalTheory.CoordProdDeriv

theorem card_filter_cons {g k : ℕ} (a : Fin g) (σ : Fin k → Fin g) (i : Fin g) :
    (Finset.univ.filter (fun j => (Fin.cons a σ : Fin (k + 1) → Fin g) j = i)).card
      = (Finset.univ.filter (fun j => σ j = i)).card + if a = i then 1 else 0 := by
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  rw [add_comm]

theorem fderiv_prod_iteratedDeriv {g : ℕ} (f : Fin g → ℂ → ℂ) (hf : ∀ i, Differentiable ℂ (f i))
    (n : Fin g → ℕ) (z : Fin g → ℂ) :
    HasFDerivAt (fun z : Fin g → ℂ => ∏ i, iteratedDeriv (n i) (f i) (z i))
      (∑ a : Fin g, (∏ i, iteratedDeriv (n i + if a = i then 1 else 0) (f i) (z i)) •
        (ContinuousLinearMap.proj a : (Fin g → ℂ) →L[ℂ] ℂ)) z := by
  have h : ∀ i ∈ (Finset.univ : Finset (Fin g)),
      HasFDerivAt (fun z : Fin g → ℂ => iteratedDeriv (n i) (f i) (z i))
        (iteratedDeriv (n i + 1) (f i) (z i) •
          (ContinuousLinearMap.proj i : (Fin g → ℂ) →L[ℂ] ℂ)) z := by
    intro i _
    have hd : Differentiable ℂ (iteratedDeriv (n i) (f i)) :=
      ((hf i).contDiff (n := ⊤)).differentiable_iteratedDeriv _ (by
        exact WithTop.coe_lt_top _)
    have h1 : HasDerivAt (iteratedDeriv (n i) (f i)) (iteratedDeriv (n i + 1) (f i) (z i)) (z i) := by
      rw [iteratedDeriv_succ]
      exact (hd (z i)).hasDerivAt
    exact h1.comp_hasFDerivAt z
      (ContinuousLinearMap.proj i : (Fin g → ℂ) →L[ℂ] ℂ).hasFDerivAt
  have h2 := HasFDerivAt.finsetProd h
  refine h2.congr_fderiv (Eq.symm ?_)
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [smul_smul, ← Finset.prod_erase_mul _ _ (Finset.mem_univ a)]
  congr 2
  · refine Finset.prod_congr rfl fun i hi => ?_
    rw [if_neg (Finset.ne_of_mem_erase hi).symm, add_zero]
  · rw [if_pos rfl]

theorem iteratedFDeriv_prod_coord_at {g : ℕ} (f : Fin g → ℂ → ℂ)
    (hf : ∀ i, Differentiable ℂ (f i)) (k : ℕ) :
    ∀ (ys : Fin k → Fin g → ℂ) (z : Fin g → ℂ),
      iteratedFDeriv ℂ k (fun z : Fin g → ℂ => ∏ i, f i (z i)) z ys
        = ∑ σ : Fin k → Fin g, (∏ j, ys j (σ j)) *
          ∏ i, iteratedDeriv (Finset.univ.filter (fun j => σ j = i)).card (f i) (z i) := by
  have hF : ContDiff ℂ ⊤ (fun z : Fin g → ℂ => ∏ i, f i (z i)) :=
    contDiff_prod fun i _ => ((hf i).contDiff).comp (contDiff_apply ℂ (fun _ => ℂ) i)
  induction k with
  | zero => intro ys z; simp
  | succ k ih =>
    intro ys z
    have hd : DifferentiableAt ℂ (iteratedFDeriv ℂ k (fun z : Fin g → ℂ => ∏ i, f i (z i))) z :=
      hF.differentiable_iteratedFDeriv (m := k) (by exact WithTop.coe_lt_top _) z
    rw [iteratedFDeriv_succ_apply_left, ← fderiv_continuousMultilinear_apply_const_apply hd]
    have e : (fun z => iteratedFDeriv ℂ k (fun z : Fin g → ℂ => ∏ i, f i (z i)) z (Fin.tail ys))
        = fun z => ∑ σ : Fin k → Fin g, (∏ j, Fin.tail ys j (σ j)) *
          ∏ i, iteratedDeriv (Finset.univ.filter (fun j => σ j = i)).card (f i) (z i) :=
      funext fun z => ih _ z
    rw [e]
    have h3 := HasFDerivAt.fun_sum (u := Finset.univ) (fun (σ : Fin k → Fin g) _ =>
      (fderiv_prod_iteratedDeriv f hf
        (fun i => (Finset.univ.filter (fun j => σ j = i)).card) z).const_mul
        (∏ j, Fin.tail ys j (σ j)))
    rw [h3.fderiv]
    rw [← (Fin.consEquiv (fun _ : Fin (k + 1) => Fin g)).sum_comp, Fintype.sum_prod_type,
      Finset.sum_comm]
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
      ContinuousLinearMap.proj_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun a _ => ?_
    have e2 : (Fin.consEquiv (fun _ : Fin (k + 1) => Fin g)) (a, σ) = Fin.cons a σ := rfl
    simp only [e2, card_filter_cons, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.tail]
    ring

theorem iteratedFDeriv_prod_coord :
    ∀ (g k : ℕ) (f : Fin g → ℂ → ℂ) (ys : Fin k → Fin g → ℂ), (∀ i, Differentiable ℂ (f i)) →
      iteratedFDeriv ℂ k (fun z : Fin g → ℂ => ∏ i, f i (z i)) 0 ys
        = ∑ σ : Fin k → Fin g, (∏ j, ys j (σ j)) *
          ∏ i, iteratedDeriv (Finset.univ.filter (fun j => σ j = i)).card (f i) 0 :=
  fun _ k f ys hf => iteratedFDeriv_prod_coord_at f hf k ys 0

end GlobalTheory.CoordProdDeriv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsCutIntoBoundedGroupsFinset
namespace GlobalTheory

theorem exists_le_sum_eq_of_le_sum (S : Finset ℕ) (e : ℕ → ℕ) :
    ∀ n, n ≤ ∑ k ∈ S, e k →
      ∃ f : ℕ → ℕ, (∀ k, f k ≤ e k) ∧ ∑ k ∈ S, f k = n ∧ ∀ k, k ∉ S → f k = 0 := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro n hn
    refine ⟨fun _ => 0, fun _ => Nat.zero_le _, ?_, fun _ _ => rfl⟩
    simp only [Finset.sum_empty] at hn ⊢
    omega
  | insert a S ha ih =>
    intro n hn
    rw [Finset.sum_insert ha] at hn
    obtain ⟨g, hge, hgs, hgo⟩ := ih (min n (∑ k ∈ S, e k)) (min_le_right _ _)
    refine ⟨fun k => if k = a then n - min n (∑ k ∈ S, e k) else g k, ?_, ?_, ?_⟩
    · intro k
      by_cases hk : k = a
      · subst hk
        simp only [if_true]
        omega
      · simp only [hk, if_false]
        exact hge k
    · rw [Finset.sum_insert ha, if_pos rfl]
      have hS : ∑ k ∈ S, (if k = a then n - min n (∑ k ∈ S, e k) else g k) = ∑ k ∈ S, g k := by
        refine Finset.sum_congr rfl fun k hk => ?_
        have : k ≠ a := fun h => ha (h ▸ hk)
        simp only [this, if_false]
      rw [hS, hgs]
      omega
    · intro k hk
      have hka : k ≠ a := fun h => hk (h ▸ Finset.mem_insert_self _ _)
      have hkS : k ∉ S := fun h => hk (Finset.mem_insert_of_mem h)
      simp only [hka, if_false]
      exact hgo k hkS

theorem exists_cut_into_bounded_groups_finset (S : Finset ℕ) (B : ℕ) :
    ∀ (s : ℕ) (e : ℕ → ℕ), ∑ k ∈ S, e k ≤ s * B →
      ∃ pc : Fin s → ℕ → ℕ, (∀ k ∈ S, ∑ u, pc u k = e k) ∧ (∀ u, ∑ k ∈ S, pc u k ≤ B) ∧
        ∀ u k, k ∉ S → pc u k = 0 := by
  classical
  intro s
  induction s with
  | zero =>
    intro e he
    refine ⟨fun _ _ => 0, ?_, fun u => u.elim0, fun u => u.elim0⟩
    intro k hk
    simp only [zero_mul, nonpos_iff_eq_zero] at he
    rw [Finset.sum_eq_zero_iff] at he
    simp [he k hk]
  | succ s ih =>
    intro e he
    obtain ⟨f, hfe, hfs, hfo⟩ :=
      exists_le_sum_eq_of_le_sum S e (min B (∑ k ∈ S, e k)) (min_le_right _ _)
    have hsplit : ∑ k ∈ S, (e k - f k) + ∑ k ∈ S, f k = ∑ k ∈ S, e k := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => Nat.sub_add_cancel (hfe k)
    have hmul : (s + 1) * B = s * B + B := by ring
    obtain ⟨pc, hpcs, hpcb, hpco⟩ := ih (fun k => e k - f k) (by omega)
    refine ⟨Fin.cons f pc, ?_, ?_, ?_⟩
    · intro k hk
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [hpcs k hk]
      exact Nat.add_sub_cancel' (hfe k)
    · intro u
      refine Fin.cases ?_ (fun i => ?_) u
      · simp only [Fin.cons_zero]
        omega
      · simp only [Fin.cons_succ]
        exact hpcb i
    · intro u k hk
      refine Fin.cases ?_ (fun i => ?_) u
      · simp only [Fin.cons_zero]
        exact hfo k hk
      · simp only [Fin.cons_succ]
        exact hpco i k hk

theorem exists_cut_columns_bounded_width : ∀ (K s B : ℕ) (e : ℕ → ℕ), ∑ k ∈ Finset.Icc 1 K, e k ≤ s * B → ∃ pc : Fin s → ℕ → ℕ, (∀ k ∈ Finset.Icc 1 K, ∑ u, pc u k = e k) ∧ (∀ u, ∑ k ∈ Finset.Icc 1 K, pc u k ≤ B) ∧ ∀ u k, k ∉ Finset.Icc 1 K → pc u k = 0 := by
  intro K s B e h
  exact exists_cut_into_bounded_groups_finset (Finset.Icc 1 K) B s e h

end GlobalTheory
end
