module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EndOmega

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormSubLeMaxOfUltrametricField
noncomputable section

namespace GlobalTheory.Honda.TwistedDivision

variable {K : Type} [NormedField K]

theorem norm_sub_le_max_of_ultrametric_field [IsUltrametricDist K] (x y : K) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  rw [sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max x (-y)).trans_eq (by rw [norm_neg])

theorem norm_pow_apply (τ : K →+* K) (hτ : ∀ x, ‖τ x‖ = ‖x‖) (i : ℕ) (x : K) :
    ‖(τ ^ i) x‖ = ‖x‖ := by
  induction i generalizing x with
  | zero => simp
  | succ i ih => rw [pow_succ, RingHom.mul_def, RingHom.comp_apply, ih, hτ]

noncomputable def step (τ : K →+* K) (π : K) (c : ℕ → K) (t : ℕ → K) : ℕ → K
  | 0 => 1
  | m + 1 => (π * t (m + 2) - ∑ i : Fin (m + 1), step τ π c t i * (τ ^ (i : ℕ)) (c (m + 1 - i))) /
      (τ ^ (m + 1)) (c 0)
termination_by m => m
decreasing_by exact i.isLt

theorem step_zero (τ : K →+* K) (π : K) (c : ℕ → K) (t : ℕ → K) : step τ π c t 0 = 1 := by
  rw [step]

theorem step_succ (τ : K →+* K) (π : K) (c : ℕ → K) (t : ℕ → K) (m : ℕ) :
    step τ π c t (m + 1) = (π * t (m + 2) - ∑ i ∈ Finset.range (m + 1), step τ π c t i * (τ ^ i) (c (m + 1 - i))) /
      (τ ^ (m + 1)) (c 0) := by
  rw [step, Fin.sum_univ_eq_sum_range (fun i => step τ π c t i * (τ ^ i) (c (m + 1 - i)))]

variable (τ : K →+* K) (hτ : ∀ x, ‖τ x‖ = ‖x‖) (π : K) (c : ℕ → K) (hc0 : ‖c 0‖ = 1) (hc : ∀ i, ‖c i‖ ≤ 1)
include hτ hc0

include hc in
theorem step_bound [IsUltrametricDist K] (hπ : ‖π‖ ≤ 1) (t : ℕ → K) (ht : ∀ j, ‖t j‖ ≤ 1) (m : ℕ) : ‖step τ π c t m‖ ≤ 1 := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    cases m with
    | zero => simp [step_zero]
    | succ m =>
      rw [step_succ, norm_div, norm_pow_apply τ hτ, hc0, div_one]
      refine (norm_sub_le_max_of_ultrametric_field _ _).trans (max_le ?_ ?_)
      · rw [norm_mul]; exact mul_le_one₀ hπ (norm_nonneg _) (ht _)
      · refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i hi => ?_
        rw [norm_mul, norm_pow_apply τ hτ]
        exact mul_le_one₀ (ih i (Finset.mem_range.1 hi)) (norm_nonneg _) (hc _)

include hc in
theorem step_diff [IsUltrametricDist K] (t t' : ℕ → K) (ε : ℝ) (hε : 0 ≤ ε) (h : ∀ j, ‖t j - t' j‖ ≤ ε) (m : ℕ) :
    ‖step τ π c t m - step τ π c t' m‖ ≤ ‖π‖ * ε := by
  have hπε : 0 ≤ ‖π‖ * ε := mul_nonneg (norm_nonneg _) hε
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    cases m with
    | zero => simpa [step_zero] using hπε
    | succ m =>
      rw [step_succ, step_succ, ← sub_div, norm_div, norm_pow_apply τ hτ, hc0, div_one]
      have key : (π * t (m + 2) - ∑ i ∈ Finset.range (m + 1), step τ π c t i * (τ ^ i) (c (m + 1 - i))) -
          (π * t' (m + 2) - ∑ i ∈ Finset.range (m + 1), step τ π c t' i * (τ ^ i) (c (m + 1 - i))) =
          π * (t (m + 2) - t' (m + 2)) -
            ∑ i ∈ Finset.range (m + 1), (step τ π c t i - step τ π c t' i) * (τ ^ i) (c (m + 1 - i)) := by
        simp only [sub_mul, Finset.sum_sub_distrib]; ring
      rw [key]
      refine (norm_sub_le_max_of_ultrametric_field _ _).trans (max_le ?_ ?_)
      · rw [norm_mul]; exact mul_le_mul_of_nonneg_left (h _) (norm_nonneg _)
      · refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hπε fun i hi => ?_
        rw [norm_mul, norm_pow_apply τ hτ]
        have hi' : i < m + 1 := Finset.mem_range.1 hi
        calc ‖step τ π c t i - step τ π c t' i‖ * ‖c (m + 1 - i)‖ ≤ (‖π‖ * ε) * 1 :=
              mul_le_mul (ih i hi') (hc _) (norm_nonneg _) hπε
          _ = ‖π‖ * ε := mul_one _

theorem step_eq (t : ℕ → K) (m : ℕ) :
    π * t (m + 2) = ∑ i ∈ Finset.range (m + 2), step τ π c t i * (τ ^ i) (c (m + 2 - 1 - i)) := by
  have hu : (τ ^ (m + 1)) (c 0) ≠ 0 := by
    intro h0; have := norm_pow_apply τ hτ (m + 1) (c 0); rw [h0, norm_zero, hc0] at this; exact zero_ne_one this
  rw [Finset.sum_range_succ, step_succ]
  have h1 : m + 2 - 1 - (m + 1) = 0 := by omega
  rw [h1, div_mul_cancel₀ _ hu]
  have h2 : ∑ i ∈ Finset.range (m + 1), step τ π c t i * (τ ^ i) (c (m + 2 - 1 - i)) =
      ∑ i ∈ Finset.range (m + 1), step τ π c t i * (τ ^ i) (c (m + 1 - i)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    have : m + 2 - 1 - i = m + 1 - i := by omega
    rw [this]
  rw [h2]; ring

end GlobalTheory.Honda.TwistedDivision

namespace GlobalTheory.Honda

open PowerSeries Filter Topology

theorem exists_twisted_division : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (τ : K →+* K),
    (∀ x, ‖τ x‖ = ‖x‖) → ∀ π : K, ‖π‖ < 1 → ∀ c : ℕ → K, ‖c 0‖ = 1 → (∀ i, ‖c i‖ ≤ 1) →
    ∃ t : ℕ → K, t 0 = 1 ∧ (∀ n, ‖t n‖ ≤ 1) ∧
      ∀ n, 2 ≤ n → π * t n = ∑ i ∈ Finset.range n, t i * (τ ^ i) (c (n - 1 - i)) := by
  intro K _ _ _ τ hτ π hπ c hc0 hc
  let T : ℕ → ℕ → K := fun k => (TwistedDivision.step τ π c)^[k] (fun _ => 1)
  have hTs : ∀ k, T (k + 1) = TwistedDivision.step τ π c (T k) := fun k =>
    Function.iterate_succ_apply' _ _ _
  have hπ1 : ‖π‖ ≤ 1 := hπ.le
  have hB : ∀ k j, ‖T k j‖ ≤ 1 := by
    intro k
    induction k with
    | zero => intro j; simp [T]
    | succ k ih => intro j; rw [hTs]; exact TwistedDivision.step_bound τ hτ π c hc0 hc hπ1 _ ih j
  have hD : ∀ k j, ‖T (k + 1) j - T k j‖ ≤ ‖π‖ ^ k := by
    intro k
    induction k with
    | zero => intro j; simpa using (TwistedDivision.norm_sub_le_max_of_ultrametric_field _ _).trans (max_le (hB 1 j) (hB 0 j))
    | succ k ih =>
      intro j
      have := TwistedDivision.step_diff τ hτ π c hc0 hc (T (k + 1)) (T k) _ (pow_nonneg (norm_nonneg _) _) ih j
      rw [← hTs (k + 1), ← hTs k, ← pow_succ'] at this
      exact this
  have hC : ∀ j, ∃ x, Tendsto (fun k => T k j) atTop (𝓝 x) := fun j =>
    cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric ‖π‖ 1 hπ fun k => by
      rw [dist_eq_norm, norm_sub_rev, one_mul]; exact hD k j)
  choose t ht using hC
  refine ⟨t, ?_, ?_, ?_⟩
  · have h0 : ∀ k, T k 0 = 1 := by
      intro k; cases k with
      | zero => rfl
      | succ k => rw [hTs]; exact TwistedDivision.step_zero _ _ _ _
    have : Tendsto (fun k => T k 0) atTop (𝓝 1) := by simp only [h0]; exact tendsto_const_nhds
    exact tendsto_nhds_unique (ht 0) this
  · intro j
    exact le_of_tendsto' (ht j).norm fun k => hB k j
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    have hL : Tendsto (fun k => π * T k (m + 2)) atTop (𝓝 (π * t (m + 2))) := (ht _).const_mul π
    have hR : Tendsto (fun k => ∑ i ∈ Finset.range (m + 2), T (k + 1) i * (τ ^ i) (c (m + 2 - 1 - i))) atTop
        (𝓝 (∑ i ∈ Finset.range (m + 2), t i * (τ ^ i) (c (m + 2 - 1 - i)))) :=
      tendsto_finsetSum _ fun i _ => (((ht i).comp (tendsto_add_atTop_nat 1)).mul_const _)
    have hEq : (fun k => π * T k (m + 2)) =
        fun k => ∑ i ∈ Finset.range (m + 2), T (k + 1) i * (τ ^ i) (c (m + 2 - 1 - i)) := by
      funext k; rw [hTs]; exact TwistedDivision.step_eq τ hτ π c hc0 _ m
    rw [hEq] at hL
    exact tendsto_nhds_unique hL hR

end GlobalTheory.Honda
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HondaTypeReductionToOneTerm
open PowerSeries GlobalTheory.Honda

namespace GlobalTheory.Honda.OneTerm

variable {K : Type} [NormedField K]

theorem coeff_frobOp (τ : K →+* K) {q : ℕ} (hq : q ≠ 0) (i : ℕ) (f : K⟦X⟧) (n : ℕ) :
    coeff n (frobOp τ q i f) = if q ^ i ∣ n then (τ ^ i) (coeff (n / q ^ i) f) else 0 := by
  unfold frobOp
  rw [coeff_subst_X_pow (pow_ne_zero _ hq)]
  simp [coeff_map]

theorem pow_apply_pow (τ : K →+* K) (i k : ℕ) (x : K) : (τ ^ i) ((τ ^ k) x) = (τ ^ (i + k)) x := by
  rw [pow_add]; rfl

theorem norm_pow_apply (τ : K →+* K) (hτ : ∀ x, ‖τ x‖ = ‖x‖) (i : ℕ) (x : K) : ‖(τ ^ i) x‖ = ‖x‖ := by
  induction i generalizing x with
  | zero => rfl
  | succ i ih => rw [← pow_apply_pow, ih, pow_one, hτ]

theorem coeff_frobOp_eq_zero (τ : K →+* K) {q : ℕ} (hq : 2 ≤ q) {f : K⟦X⟧} (hf : constantCoeff f = 0)
    {k n : ℕ} (h : n ≤ k) : coeff n (frobOp τ q k f) = 0 := by
  rw [coeff_frobOp τ (by omega)]
  split_ifs with hd
  · have hlt : n < q ^ k := lt_of_le_of_lt h (Nat.lt_pow_self (by omega))
    have h0 : n = 0 := Nat.eq_zero_of_dvd_of_lt hd hlt
    subst h0
    simp [hf]
  · rfl

theorem pow_apply_coeff_frobOp (τ : K →+* K) {q : ℕ} (hq : q ≠ 0) (f : K⟦X⟧) (i k : ℕ) {n : ℕ} (hd : q ^ i ∣ n) :
    (τ ^ i) (coeff (n / q ^ i) (frobOp τ q k f)) = coeff n (frobOp τ q (i + k) f) := by
  rw [coeff_frobOp τ hq, coeff_frobOp τ hq, pow_add q i k]
  by_cases h : q ^ i * q ^ k ∣ n
  · rw [if_pos h, if_pos ((Nat.dvd_div_iff_mul_dvd hd).2 h), pow_apply_pow, Nat.div_div_eq_div_mul]
  · rw [if_neg h, if_neg (fun h' => h ((Nat.dvd_div_iff_mul_dvd hd).1 h')), map_zero]

theorem coeff_frobOp_sub_hondaSum (τ : K →+* K) (l : ℕ) {q : ℕ} (hq : 2 ≤ q) {f : K⟦X⟧} (hf : constantCoeff f = 0)
    (c : ℕ → K) (i n N : ℕ) (hN : n ≤ N) :
    coeff n (frobOp τ q i (C (l : K) * f - hondaSum τ q c f)) =
      (l : K) * coeff n (frobOp τ q i f) -
        ∑ j ∈ Finset.range N, (τ ^ i) (c j) * coeff n (frobOp τ q (i + (j + 1)) f) := by
  have hq0 : q ≠ 0 := by omega
  rw [coeff_frobOp τ hq0]
  set_option synthInstance.maxHeartbeats 100000 in
   by_cases hd : q ^ i ∣ n
   · rw [if_pos hd, coeff_frobOp τ hq0 i f, if_pos hd, map_sub, coeff_C_mul, hondaSum, coeff_mk,
      ← Finset.eventually_constant_sum (N := n / q ^ i) (n := N)
        (fun j hj => by rw [coeff_frobOp_eq_zero τ hq hf (by omega), mul_zero])
        (le_trans (Nat.div_le_self _ _) hN),
      map_sub, map_mul, map_natCast, map_sum]
     congr 1
     refine Finset.sum_congr rfl fun j _ => ?_
     rw [map_mul, pow_apply_coeff_frobOp τ hq0 f i (j + 1) hd]
   · rw [if_neg hd, coeff_frobOp τ hq0 i f, if_neg hd, mul_zero, Finset.sum_eq_zero, sub_zero]
     intro j _
     rw [coeff_frobOp τ hq0, if_neg, mul_zero]
     exact fun h => hd (dvd_trans (pow_dvd_pow q (Nat.le_add_right _ _)) h)

theorem sum_square_eq_sum_diag (N : ℕ) (F : ℕ → ℕ → K) (hF : ∀ i j, N ≤ i + j → F i j = 0) :
    ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, F i j =
      ∑ m ∈ Finset.range N, ∑ i ∈ Finset.range (m + 1), F i (m - i) := by
  rw [Finset.sum_range_diag_flip]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Finset.eventually_constant_sum (fun j hj => hF i j (by omega)) (Nat.sub_le _ _)

theorem coeff_identity (τ : K →+* K) (l : ℕ) {q : ℕ} (hq : 2 ≤ q) {f : K⟦X⟧} (hf : constantCoeff f = 0)
    (c t : ℕ → K) (ht0 : t 0 = 1)
    (ht : ∀ n, 2 ≤ n → (l : K) * t n = ∑ i ∈ Finset.range n, t i * (τ ^ i) (c (n - 1 - i))) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), t i * coeff n (frobOp τ q i (C (l : K) * f - hondaSum τ q c f)) =
      (l : K) * coeff n f - (c 0 - l * t 1) * coeff n (frobOp τ q 1 f) := by
  have hq0 : q ≠ 0 := by omega
  have h1 : ∀ i ∈ Finset.range (n + 1), t i * coeff n (frobOp τ q i (C (l : K) * f - hondaSum τ q c f)) =
      (l : K) * t i * coeff n (frobOp τ q i f) -
        ∑ j ∈ Finset.range (n + 1), t i * (τ ^ i) (c j) * coeff n (frobOp τ q (i + (j + 1)) f) := by
    intro i _
    rw [coeff_frobOp_sub_hondaSum τ l hq hf c i n (n + 1) (Nat.le_succ n), mul_sub, Finset.mul_sum]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun j _ => by ring
  rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib,
    sum_square_eq_sum_diag (n + 1) (fun i j => t i * (τ ^ i) (c j) * coeff n (frobOp τ q (i + (j + 1)) f))
      (fun i j hij => by simp only [coeff_frobOp_eq_zero τ hq hf (show n ≤ i + (j + 1) by omega), mul_zero])]
  have h2 : ∀ m ∈ Finset.range (n + 1),
      ∑ i ∈ Finset.range (m + 1), t i * (τ ^ i) (c (m - i)) * coeff n (frobOp τ q (i + (m - i + 1)) f) =
      (∑ i ∈ Finset.range (m + 1), t i * (τ ^ i) (c (m - i))) * coeff n (frobOp τ q (m + 1) f) := by
    intro m _
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    have : i + (m - i + 1) = m + 1 := by have := Finset.mem_range.1 hi; omega
    rw [this]
  rw [Finset.sum_congr rfl h2, Finset.sum_range_succ', Finset.sum_range_succ _ n,
    coeff_frobOp_eq_zero τ hq hf (Nat.le_succ n), mul_zero, add_zero, add_sub_right_comm,
    ← Finset.sum_sub_distrib, Finset.sum_eq_single 0]
  · have h0 : coeff n (frobOp τ q 0 f) = coeff n f := by
      rw [coeff_frobOp τ hq0]; simp
    rw [h0, ht0]
    simp only [zero_add, Finset.sum_range_one, pow_zero, Nat.sub_zero, ht0, RingHom.one_def, RingHom.id_apply]
    ring
  · intro m _ hm
    rw [ht (m + 1) (by omega), Nat.add_sub_cancel, sub_self]
  · intro h
    have hn : n = 0 := by simpa using h
    rw [coeff_frobOp_eq_zero τ hq hf (show n ≤ 0 + 1 by omega), mul_zero, mul_zero, sub_self]

theorem exists_one_term : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] [CompleteSpace K]
    (l q : ℕ) (τ : K →+* K), 2 ≤ q → ‖(l : K)‖ < 1 → (∀ x, ‖τ x‖ = ‖x‖) → ∀ (f : K⟦X⟧), constantCoeff f = 0 →
    ∀ c : ℕ → K, (∀ j, ‖c j‖ ≤ 1) → ‖c 0‖ = 1 → CoefLe ‖(l : K)‖ (C (l : K) * f - hondaSum τ q c f) →
    ∃ c' : K, ‖c'‖ = 1 ∧ CoefLe ‖(l : K)‖ (C (l : K) * f - C c' * frobOp τ q 1 f) := by
  intro K _ _ _ _ l q τ hq hl hτ f hf c hc hc0 hg
  obtain ⟨t, ht0, ht1, ht⟩ := GlobalTheory.Honda.exists_twisted_division K τ hτ (l : K) hl c hc0 hc
  refine ⟨c 0 - l * t 1, ?_, fun n => ?_⟩
  · have hlt : ‖-((l : K) * t 1)‖ < ‖c 0‖ := by
      rw [norm_neg, norm_mul, hc0]
      exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) (ht1 1)) hl
    rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne', max_eq_left hlt.le, hc0]
  · rw [map_sub, coeff_C_mul, coeff_C_mul, ← coeff_identity τ l hq hf c t ht0 ht n]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => ?_
    rw [norm_mul]
    refine le_trans (mul_le_of_le_one_left (norm_nonneg _) (ht1 i)) ?_
    rw [coeff_frobOp τ (by omega)]
    split_ifs
    · rw [norm_pow_apply τ hτ]; exact hg _
    · simp

end GlobalTheory.Honda.OneTerm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HondaTypeReductionToOneTermStatement
open PowerSeries GlobalTheory.Honda
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hondaType_reduction_to_one_term : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] [CompleteSpace K] (l q : ℕ) (τ : K →+* K), 2 ≤ q → ‖(l : K)‖ < 1 → (∀ x, ‖τ x‖ = ‖x‖) → ∀ (f : K⟦X⟧), constantCoeff f = 0 → ∀ c : ℕ → K, (∀ j, ‖c j‖ ≤ 1) → ‖c 0‖ = 1 → CoefLe ‖(l : K)‖ (C (l : K) * f - hondaSum τ q c f) → ∃ c' : K, ‖c'‖ = 1 ∧ CoefLe ‖(l : K)‖ (C (l : K) * f - C c' * frobOp τ q 1 f) := by
  first | exact @GlobalTheory.Honda.OneTerm.exists_one_term | exact GlobalTheory.Honda.OneTerm.exists_one_term | (intros; apply GlobalTheory.Honda.OneTerm.exists_one_term <;> assumption)
end
