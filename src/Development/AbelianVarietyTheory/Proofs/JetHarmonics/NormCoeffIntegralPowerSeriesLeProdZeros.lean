module

public import Development.AbelianVarietyTheory.Definitions.Jets.PowerSeriesHasSumAt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormCoeffIntegralPowerSeriesLeProdZeros
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormCoeffIntegralPowerSeriesLeProdZeros
open GlobalTheory.ConvSer

namespace GlobalTheory.ConvSer

variable {K : Type} [NormedField K] in
private lemma summable_coeff_mul_pow [CompleteSpace K] (c : ℕ → K) (hc : ∀ n, ‖c n‖ ≤ 1) (y : K)
    (hy : ‖y‖ < 1) : Summable (fun n => c n * y ^ n) :=
  Summable.of_norm_bounded (summable_geometric_of_lt_one (norm_nonneg y) hy) fun n => by
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_left (by positivity) (hc n)

variable {K : Type} [NormedField K] in
private lemma exists_quotient_by_linear_of_zero [IsUltrametricDist K] [CompleteSpace K] (c : ℕ → K)
    (hc : ∀ n, ‖c n‖ ≤ 1) (x : K) (hx : ‖x‖ < 1) (h0 : ∑' n, c n * x ^ n = 0) :
    ∃ d : ℕ → K, (∀ n, ‖d n‖ ≤ 1) ∧ c 0 = -(x * d 0) ∧ ∀ n, c (n + 1) = d n - x * d (n + 1) := by
  refine ⟨fun k => ∑' m, c (m + k + 1) * x ^ m, fun k => ?_, ?_, fun n => ?_⟩
  · refine IsUltrametricDist.norm_tsum_le_of_forall_le fun m => ?_
    rw [norm_mul, norm_pow]
    exact mul_le_one₀ (hc _) (by positivity) (pow_le_one₀ (norm_nonneg x) hx.le)
  · have hs := summable_coeff_mul_pow c hc x hx
    rw [hs.tsum_eq_zero_add] at h0
    have : ∑' m, c (m + 1) * x ^ (m + 1) = x * ∑' m, c (m + 0 + 1) * x ^ m := by
      rw [← tsum_mul_left]
      exact tsum_congr fun m => by rw [add_zero, pow_succ]; ring
    rw [this, pow_zero, mul_one] at h0
    linear_combination h0
  · have hs : Summable (fun m => c (m + n + 1) * x ^ m) :=
      summable_coeff_mul_pow (fun m => c (m + n + 1)) (fun m => hc _) x hx
    show c (n + 1) = ∑' m, c (m + n + 1) * x ^ m - x * ∑' m, c (m + (n + 1) + 1) * x ^ m
    rw [hs.tsum_eq_zero_add, ← tsum_mul_left]
    have : ∑' m, c (m + 1 + n + 1) * x ^ (m + 1) = ∑' m, x * (c (m + (n + 1) + 1) * x ^ m) :=
      tsum_congr fun m => by
        rw [show m + 1 + n + 1 = m + (n + 1) + 1 by omega, pow_succ]
        ring
    rw [this, pow_zero, mul_one, zero_add]
    ring

variable {K : Type} [NormedField K] in
private lemma tsum_eq_sub_mul_tsum [CompleteSpace K] (c d : ℕ → K) (hd : ∀ n, ‖d n‖ ≤ 1) (x : K)
    (hc : ∀ n, ‖c n‖ ≤ 1) (h0 : c 0 = -(x * d 0)) (hrel : ∀ n, c (n + 1) = d n - x * d (n + 1))
    (y : K) (hy : ‖y‖ < 1) :
    ∑' n, c n * y ^ n = (y - x) * ∑' n, d n * y ^ n := by
  have hsc := summable_coeff_mul_pow c hc y hy
  have hsd := summable_coeff_mul_pow d hd y hy
  have e1 : ∑' n, c n * y ^ n = c 0 + ∑' n, c (n + 1) * y ^ (n + 1) := by
    simpa using hsc.tsum_eq_zero_add
  have e2 : ∑' n, d n * y ^ n = d 0 + ∑' n, d (n + 1) * y ^ (n + 1) := by
    simpa using hsd.tsum_eq_zero_add
  have hA : Summable (fun n => y * (d n * y ^ n)) := hsd.mul_left y
  have hB : Summable (fun n => x * (d (n + 1) * y ^ (n + 1))) :=
    ((summable_nat_add_iff 1).mpr hsd).mul_left x
  have e3 : ∑' n, c (n + 1) * y ^ (n + 1) =
      y * ∑' n, d n * y ^ n - x * ∑' n, d (n + 1) * y ^ (n + 1) := by
    rw [← tsum_mul_left, ← tsum_mul_left, ← hA.tsum_sub hB]
    exact tsum_congr fun n => by rw [hrel n, pow_succ]; ring
  rw [e1, e3, h0]
  linear_combination x * e2

variable {K : Type} [NormedField K] in
private lemma coeff_bounds_of_zeros [IsUltrametricDist K] [CompleteSpace K] (S : Finset K) :
    ∀ c : ℕ → K, (∀ n, ‖c n‖ ≤ 1) → (∀ x ∈ S, ‖x‖ < 1 ∧ ∑' n, c n * x ^ n = 0) →
      (∀ r : ℝ, 0 < r → r ≤ 1 → (∀ x ∈ S, r ≤ ‖x‖) → ∀ k, ‖c k‖ * r ^ k ≤ ∏ x ∈ S, ‖x‖) ∧
      (‖c S.card‖ = 1 → (∀ k < S.card, ‖c k‖ < 1) → ∏ x ∈ S, ‖x‖ = ‖c 0‖) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro c hc _
    refine ⟨fun r hr0 hr1 _ k => ?_, fun h1 _ => ?_⟩
    · rw [Finset.prod_empty]
      exact mul_le_one₀ (hc k) (by positivity) (pow_le_one₀ hr0.le hr1)
    · simpa using h1.symm
  | insert x S hxS ih =>
    intro c hc hz
    obtain ⟨hx, hx0⟩ := hz x (Finset.mem_insert_self x S)
    obtain ⟨d, hd, h0, hrel⟩ := exists_quotient_by_linear_of_zero c hc x hx hx0
    have hzd : ∀ y ∈ S, ‖y‖ < 1 ∧ ∑' n, d n * y ^ n = 0 := by
      intro y hy
      obtain ⟨hy1, hy0⟩ := hz y (Finset.mem_insert_of_mem hy)
      refine ⟨hy1, ?_⟩
      rw [tsum_eq_sub_mul_tsum c d hd x hc h0 hrel y hy1] at hy0
      have hne : y - x ≠ 0 := sub_ne_zero.mpr fun h => hxS (h ▸ hy)
      exact (mul_eq_zero.mp hy0).resolve_left hne
    obtain ⟨ih1, ih2⟩ := ih d hd hzd
    have hP : 0 ≤ ∏ y ∈ S, ‖y‖ := Finset.prod_nonneg fun _ _ => norm_nonneg _
    refine ⟨fun r hr0 hr1 hrS k => ?_, fun h1 hlt => ?_⟩
    · rw [Finset.prod_insert hxS]
      have hrx : r ≤ ‖x‖ := hrS x (Finset.mem_insert_self x S)
      have hrS' : ∀ y ∈ S, r ≤ ‖y‖ := fun y hy => hrS y (Finset.mem_insert_of_mem hy)
      have hb := ih1 r hr0 hr1 hrS'
      cases k with
      | zero =>
        rw [h0, norm_neg, norm_mul, pow_zero, mul_one]
        have := hb 0
        rw [pow_zero, mul_one] at this
        exact mul_le_mul_of_nonneg_left this (norm_nonneg x)
      | succ n =>
        have hm : ‖c (n + 1)‖ ≤ max ‖d n‖ (‖x‖ * ‖d (n + 1)‖) := by
          rw [hrel n, sub_eq_add_neg]
          simpa [norm_mul] using IsUltrametricDist.norm_add_le_max (d n) (-(x * d (n + 1)))
        have e1 : ‖d n‖ * r ^ (n + 1) ≤ ‖x‖ * ∏ y ∈ S, ‖y‖ := by
          rw [pow_succ, ← mul_assoc, mul_comm ‖x‖]
          exact mul_le_mul (hb n) hrx hr0.le hP
        have e2 : ‖x‖ * ‖d (n + 1)‖ * r ^ (n + 1) ≤ ‖x‖ * ∏ y ∈ S, ‖y‖ := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (hb (n + 1)) (norm_nonneg x)
        calc ‖c (n + 1)‖ * r ^ (n + 1)
            ≤ max ‖d n‖ (‖x‖ * ‖d (n + 1)‖) * r ^ (n + 1) :=
              mul_le_mul_of_nonneg_right hm (by positivity)
          _ = max (‖d n‖ * r ^ (n + 1)) (‖x‖ * ‖d (n + 1)‖ * r ^ (n + 1)) :=
              max_mul_of_nonneg _ _ (by positivity)
          _ ≤ ‖x‖ * ∏ y ∈ S, ‖y‖ := max_le e1 e2
    · rw [Finset.card_insert_of_notMem hxS] at h1 hlt
      have hsmall : ∀ k, ‖x * d k‖ < 1 := fun k => by
        rw [norm_mul]
        exact (mul_le_of_le_one_right (norm_nonneg x) (hd k)).trans_lt hx
      have hdk : ∀ k, d k = c (k + 1) + x * d (k + 1) := fun k => by rw [hrel k]; ring
      have hd1 : ‖d S.card‖ = 1 := by
        rw [hdk, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm, h1]
        · exact max_eq_left (hsmall _).le
        · rw [h1]
          exact (hsmall _).ne'
      have hdlt : ∀ k < S.card, ‖d k‖ < 1 := fun k hk => by
        rw [hdk]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt
          (max_lt (hlt (k + 1) (by omega)) (hsmall _))
      rw [Finset.prod_insert hxS, ih2 hd1 hdlt, h0, norm_neg, norm_mul]

theorem _root_.GlobalTheory.ConvSer.norm_coeff_le_prod_zeros : ∀ (K : Type) [NormedField K]
    [IsUltrametricDist K] [CompleteSpace K] (h : PowerSeries K) (S : Finset K),
    _root_.GlobalTheory.ConvSer.Intg h → (∀ x ∈ S, ‖x‖ < 1 ∧ _root_.GlobalTheory.ConvSer.ev1 h x = 0) →
    (∀ r : ℝ, 0 < r → r ≤ 1 → (∀ x ∈ S, r ≤ ‖x‖) → ∀ k, ‖PowerSeries.coeff k h‖ * r ^ k ≤
      ∏ x ∈ S, ‖x‖) ∧ (‖PowerSeries.coeff S.card h‖ = 1 → (∀ k < S.card,
      ‖PowerSeries.coeff k h‖ < 1) → ∏ x ∈ S, ‖x‖ = ‖PowerSeries.coeff 0 h‖) := by
  intro K _ _ _ h S hI hS
  exact coeff_bounds_of_zeros S (fun n => PowerSeries.coeff n h)
    (fun n => hI (Finsupp.single () n)) hS

end GlobalTheory.ConvSer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormCoeffIntegralPowerSeriesLeProdZerosStatement
open GlobalTheory.ConvSer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_coeff_integral_powerSeries_le_prod_zeros : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (h : PowerSeries K) (S : Finset K), Intg h → (∀ x ∈ S, ‖x‖ < 1 ∧ ev1 h x = 0) → (∀ r : ℝ, 0 < r → r ≤ 1 → (∀ x ∈ S, r ≤ ‖x‖) → ∀ k, ‖PowerSeries.coeff k h‖ * r ^ k ≤ ∏ x ∈ S, ‖x‖) ∧ (‖PowerSeries.coeff S.card h‖ = 1 → (∀ k < S.card, ‖PowerSeries.coeff k h‖ < 1) → ∏ x ∈ S, ‖x‖ = ‖PowerSeries.coeff 0 h‖) := by
  first | exact @GlobalTheory.ConvSer.norm_coeff_le_prod_zeros | exact GlobalTheory.ConvSer.norm_coeff_le_prod_zeros | (intros; apply GlobalTheory.ConvSer.norm_coeff_le_prod_zeros <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MvPowerSeriesConvergentSubstHasSumAndBounds
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MvPowerSeriesConvergentSubstHasSumAndBounds
open GlobalTheory.ConvSer

namespace GlobalTheory.ConvSer.SubstSum

variable {K : Type} [NormedField K] [IsUltrametricDist K] {τ : Type}

def Decay (θ : ℝ) (m : ℕ) (S : MvPowerSeries τ K) : Prop :=
  ∀ μ : τ →₀ ℕ, ‖MvPowerSeries.coeff μ S‖ ≤ θ ^ (m - μ.degree)

omit [IsUltrametricDist K] in
theorem decay_one (θ : ℝ) : Decay θ 0 (1 : MvPowerSeries τ K) := by
  classical
  intro μ
  rw [MvPowerSeries.coeff_one]
  split_ifs <;> simp

theorem Decay.mul {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) {m n : ℕ} {S T : MvPowerSeries τ K}
    (hS : Decay θ m S) (hT : Decay θ n T) : Decay θ (m + n) (S * T) := by
  classical
  intro μ
  rw [MvPowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_nonneg h0 _) fun p hp => ?_
  have hp' : p.1 + p.2 = μ := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
  rw [norm_mul]
  calc ‖MvPowerSeries.coeff p.1 S‖ * ‖MvPowerSeries.coeff p.2 T‖
      ≤ θ ^ (m - p.1.degree) * θ ^ (n - p.2.degree) :=
        mul_le_mul (hS _) (hT _) (norm_nonneg _) (pow_nonneg h0 _)
    _ = θ ^ ((m - p.1.degree) + (n - p.2.degree)) := (pow_add _ _ _).symm
    _ ≤ θ ^ (m + n - μ.degree) := by
        apply pow_le_pow_of_le_one h0 h1
        rw [← hp', map_add (f := _)]
        omega

theorem Decay.pow {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) {S : MvPowerSeries τ K}
    (hS : Decay θ 1 S) (n : ℕ) : Decay θ n (S ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact decay_one θ
  | succ n ih => rw [pow_succ]; exact ih.mul h0 h1 hS

theorem decay_prod {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) {σ : Type} (t : Finset σ)
    (s : σ → MvPowerSeries τ K) (hs : ∀ i, Decay θ 1 (s i)) (ν : σ → ℕ) :
    Decay θ (∑ i ∈ t, ν i) (∏ i ∈ t, s i ^ ν i) := by
  classical
  refine Finset.induction_on t ?_ ?_
  · rw [Finset.prod_empty, Finset.sum_empty]
    exact decay_one θ
  · intro a t ha ih
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact (Decay.pow h0 h1 (hs a) (ν a)).mul h0 h1 ih

omit [IsUltrametricDist K] in
theorem decay_of_small {θ : ℝ} {S : MvPowerSeries τ K} (hS : Intg S)
    (hθ : ‖MvPowerSeries.constantCoeff S‖ ≤ θ) : Decay θ 1 S := by
  intro μ
  by_cases hμ : μ = 0
  · subst hμ
    rw [map_zero, Nat.sub_zero, pow_one, MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact hθ
  · have hd : μ.degree ≠ 0 := (Finsupp.degree_eq_zero_iff μ).not.2 hμ
    have : 1 - μ.degree = 0 := by omega
    rw [this, pow_zero]
    exact hS μ

theorem exists_decay {σ : Type} [Fintype σ] (s : σ → MvPowerSeries τ K) (hs : ∀ i, Small (s i)) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧ ∀ (ν : σ →₀ ℕ) (μ : τ →₀ ℕ),
      ‖MvPowerSeries.coeff μ (∏ i, s i ^ ν i)‖ ≤ θ ^ (ν.degree - μ.degree) := by
  classical
  set θ : ℝ := ((Finset.univ.sup fun i => ‖MvPowerSeries.constantCoeff (s i)‖₊ : NNReal) : ℝ)
    with hθdef
  have hsi : ∀ i, Intg (s i) ∧ ‖MvPowerSeries.constantCoeff (s i)‖ < 1 := hs
  have h0 : 0 ≤ θ := NNReal.coe_nonneg _
  have hlt : θ < 1 := by
    have : (Finset.univ.sup fun i => ‖MvPowerSeries.constantCoeff (s i)‖₊) < 1 :=
      (Finset.sup_lt_iff (by simp)).2 fun i _ => by
        have h := (hsi i).2
        rw [← coe_nnnorm] at h
        exact_mod_cast h
    exact_mod_cast this
  have hle : ∀ i, ‖MvPowerSeries.constantCoeff (s i)‖ ≤ θ := fun i => by
    rw [hθdef, ← coe_nnnorm]
    exact_mod_cast Finset.le_sup (f := fun i => ‖MvPowerSeries.constantCoeff (s i)‖₊)
      (Finset.mem_univ i)
  refine ⟨θ, h0, hlt, fun ν μ => ?_⟩
  have h := decay_prod h0 hlt.le Finset.univ s (fun i => decay_of_small (hsi i).1 (hle i)) ν μ
  rwa [← Finsupp.degree_eq_sum] at h

theorem tendsto_degree {σ : Type} [Fintype σ] :
    Filter.Tendsto (fun ν : σ →₀ ℕ => ν.degree) Filter.cofinite Filter.atTop := by
  classical
  rw [Filter.tendsto_atTop]
  intro b
  rw [Filter.eventually_cofinite]
  refine (Set.finite_Icc (0 : σ →₀ ℕ) (Finsupp.equivFunOnFinite.symm fun _ => b)).subset
    fun ν hν => ?_
  simp only [Set.mem_ofPred_eq, not_le] at hν
  refine Set.mem_Icc.2 ⟨zero_le, Finsupp.le_def.2 fun i => ?_⟩
  simpa using (Finsupp.le_degree i ν).trans hν.le

end GlobalTheory.ConvSer.SubstSum


open GlobalTheory.ConvSer.SubstSum in
theorem GlobalTheory.ConvSer.csub_hasSum_and_bounds :
    ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (σ τ : Type) [Fintype σ] (s : σ → MvPowerSeries τ K) (S : MvPowerSeries σ K), (∀ i, Small (s i)) → Bdd S → (∀ μ, HasSum (fun ν : σ →₀ ℕ => MvPowerSeries.coeff ν S * MvPowerSeries.coeff μ (∏ i, s i ^ ν i)) (MvPowerSeries.coeff μ (csub s S))) ∧ Bdd (csub s S) ∧ (Intg S → Intg (csub s S)) ∧ (Intg S → MvPowerSeries.constantCoeff S = 0 → Small (csub s S)) := by
  intro K _ _ _ σ τ _ s S hs hS
  obtain ⟨θ, h0, h1, hθ⟩ := exists_decay s hs
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ ν, ‖MvPowerSeries.coeff ν S‖ ≤ C := hS
  set t : (τ →₀ ℕ) → (σ →₀ ℕ) → K := fun μ ν =>
    MvPowerSeries.coeff ν S * MvPowerSeries.coeff μ (∏ i, s i ^ ν i) with ht
  have hprod1 : ∀ (ν : σ →₀ ℕ) μ, ‖MvPowerSeries.coeff μ (∏ i, s i ^ ν i)‖ ≤ 1 := fun ν μ =>
    (hθ ν μ).trans (pow_le_one₀ h0 h1.le)
  have hsum : ∀ μ, HasSum (t μ) (MvPowerSeries.coeff μ (csub s S)) := by
    intro μ
    have hC0 : 0 ≤ max C 0 := le_max_right _ _
    have htend : Filter.Tendsto (t μ) Filter.cofinite (nhds 0) := by
      refine squeeze_zero_norm (a := fun ν => max C 0 * θ ^ (ν.degree - μ.degree))
        (fun ν => ?_) ?_
      · rw [ht, norm_mul]
        exact mul_le_mul ((hC ν).trans (le_max_left _ _)) (hθ ν μ) (norm_nonneg _) hC0
      · have h : Filter.Tendsto (fun ν : σ →₀ ℕ => θ ^ (ν.degree - μ.degree))
            Filter.cofinite (nhds 0) :=
          (tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1).comp
            ((Filter.tendsto_sub_atTop_nat μ.degree).comp tendsto_degree)
        simpa using h.const_mul (max C 0)
    have heq : MvPowerSeries.coeff μ (csub s S) = ∑' ν, t μ ν := rfl
    rw [heq]
    exact (NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero htend).hasSum
  have hbound : ∀ B : ℝ, 0 ≤ B → (∀ μ ν, ‖t μ ν‖ ≤ B) →
      ∀ μ, ‖MvPowerSeries.coeff μ (csub s S)‖ ≤ B := fun B hB h μ => by
    rw [← (hsum μ).tsum_eq]
    exact IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hB (h μ)
  have hterm : ∀ μ ν, ‖t μ ν‖ ≤ ‖MvPowerSeries.coeff ν S‖ := fun μ ν => by
    rw [ht, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hprod1 ν μ)
  have hintg : Intg S → Intg (csub s S) := fun hI =>
    hbound 1 zero_le_one fun μ ν => (hterm μ ν).trans (hI ν)
  refine ⟨hsum, ?_, hintg, fun hI h00 => ?_⟩
  · exact Exists.intro (max C 0) (hbound _ (le_max_right _ _) fun μ ν =>
      (hterm μ ν).trans ((hC ν).trans (le_max_left _ _)))
  · have hc : ‖MvPowerSeries.coeff 0 (csub s S)‖ ≤ θ := by
      rw [← (hsum 0).tsum_eq]
      refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg h0 fun ν => ?_
      by_cases hν : ν = 0
      · subst hν
        simp [ht, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h00, h0]
      · rw [ht, norm_mul]
        have hd : 1 ≤ ν.degree - (0 : τ →₀ ℕ).degree := by
          have a := (Finsupp.degree_eq_zero_iff ν).not.2 hν
          rw [map_zero]
          omega
        calc ‖MvPowerSeries.coeff ν S‖ * ‖MvPowerSeries.coeff 0 (∏ i, s i ^ ν i)‖
            ≤ 1 * θ := mul_le_mul (hI ν)
              ((hθ ν 0).trans ((pow_le_pow_of_le_one h0 h1.le hd).trans_eq (pow_one θ)))
              (norm_nonneg _) zero_le_one
          _ = θ := one_mul θ
    exact And.intro (hintg hI)
      (by rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]; exact hc.trans_lt h1)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MvPowerSeriesConvergentSubstHasSumAndBoundsStatement
open GlobalTheory.ConvSer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mvPowerSeriesConvergentSubst_hasSum_and_bounds : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (σ τ : Type) [Fintype σ] (s : σ → MvPowerSeries τ K) (S : MvPowerSeries σ K), (∀ i, Small (s i)) → Bdd S → (∀ μ, HasSum (fun ν : σ →₀ ℕ => MvPowerSeries.coeff ν S * MvPowerSeries.coeff μ (∏ i, s i ^ ν i)) (MvPowerSeries.coeff μ (csub s S))) ∧ Bdd (csub s S) ∧ (Intg S → Intg (csub s S)) ∧ (Intg S → MvPowerSeries.constantCoeff S = 0 → Small (csub s S)) := by
  first | exact @GlobalTheory.ConvSer.csub_hasSum_and_bounds | exact GlobalTheory.ConvSer.csub_hasSum_and_bounds | (intros; apply GlobalTheory.ConvSer.csub_hasSum_and_bounds <;> assumption)
end
end
