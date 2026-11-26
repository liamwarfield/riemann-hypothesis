module

public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.IterDifferentiableOn
open Set Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat.LocalLog

noncomputable def iter {B V : Type} (h : B × V → V) : ℕ → B × V → V
  | 0, p => p.2
  | k + 1, p => h (p.1, iter h k p)

@[simp] theorem iter_zero {B V : Type} (h : B × V → V) (p : B × V) : iter h 0 p = p.2 := rfl

theorem iter_succ {B V : Type} (h : B × V → V) (k : ℕ) (p : B × V) :
    iter h (k + 1) p = h (p.1, iter h k p) := rfl

section Norms

variable {B V : Type} [NormedAddCommGroup B] [NormedAddCommGroup V]

theorem norm_iter_le (b₀ : B) (h : B × V → V) (ρ : ℝ)
    (hcontr : ∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, ‖h (b, s)‖ ≤ 3 / 5 * ‖s‖)
    {b : B} (hb : b ∈ ball b₀ ρ) {s : V} (hs : s ∈ ball (0 : V) ρ) (k : ℕ) :
    ‖iter h k (b, s)‖ ≤ (3 / 5) ^ k * ‖s‖ := by
  have key : ∀ k : ℕ, ‖iter h k (b, s)‖ ≤ (3 / 5) ^ k * ‖s‖ ∧ iter h k (b, s) ∈ ball (0 : V) ρ := by
    intro k
    induction k with
    | zero =>
      refine ⟨by simp, ?_⟩
      simpa using hs
    | succ k ih =>
      have hk := hcontr b hb _ ih.2
      have e : iter h (k + 1) (b, s) = h (b, iter h k (b, s)) := rfl
      rw [e]
      refine ⟨?_, ?_⟩
      · calc ‖h (b, iter h k (b, s))‖ ≤ 3 / 5 * ‖iter h k (b, s)‖ := hk
          _ ≤ 3 / 5 * ((3 / 5) ^ k * ‖s‖) := by gcongr; exact ih.1
          _ = (3 / 5) ^ (k + 1) * ‖s‖ := by ring
      · have h2 := mem_ball_zero_iff.mp ih.2
        rw [mem_ball_zero_iff]
        nlinarith [norm_nonneg (iter h k (b, s))]
  exact (key k).1

theorem iter_mem_ball (b₀ : B) (h : B × V → V) (ρ : ℝ)
    (hcontr : ∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, ‖h (b, s)‖ ≤ 3 / 5 * ‖s‖)
    {b : B} (hb : b ∈ ball b₀ ρ) {s : V} (hs : s ∈ ball (0 : V) ρ) (k : ℕ) :
    iter h k (b, s) ∈ ball (0 : V) ρ := by
  rw [mem_ball_zero_iff]
  have h1 := norm_iter_le b₀ h ρ hcontr hb hs k
  have h2 : (3 / 5 : ℝ) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h3 : ‖s‖ < ρ := mem_ball_zero_iff.mp hs
  nlinarith [norm_nonneg s]

end Norms

theorem iter_differentiableOn {B V : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]
    [NormedAddCommGroup V] [NormedSpace ℂ V] (b₀ : B) (h : B × V → V) (ρ : ℝ)
    (hd : DifferentiableOn ℂ h (ball b₀ ρ ×ˢ ball (0 : V) ρ))
    (hcontr : ∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, ‖h (b, s)‖ ≤ 3 / 5 * ‖s‖) (k : ℕ) :
    DifferentiableOn ℂ (iter h k) (ball b₀ ρ ×ˢ ball (0 : V) ρ) := by
  induction k with
  | zero =>
    have e : iter h 0 = Prod.snd := funext fun p => rfl
    rw [e]
    exact differentiableOn_snd
  | succ k ih =>
    have e : iter h (k + 1) = h ∘ fun p => (p.1, iter h k p) := funext fun p => rfl
    rw [e]
    refine hd.comp (differentiableOn_fst.prodMk ih) ?_
    intro p hp
    exact Set.mk_mem_prod hp.1 (iter_mem_ball b₀ h ρ hcontr hp.1 hp.2 k)

theorem medial_eventually {B V : Type} [TopologicalSpace B] [Zero V] [TopologicalSpace V] (b₀ : B)
    (μ : B × V × V → V) (hc : ContinuousAt μ (b₀, 0, 0)) (h0 : μ (b₀, 0, 0) = 0)
    (hcomm : ∀ᶠ p : B × V × V in 𝓝 (b₀, 0, 0), μ (p.1, p.2.1, p.2.2) = μ (p.1, p.2.2, p.2.1))
    (hassoc : ∀ᶠ p : B × V × V × V in 𝓝 (b₀, 0, 0, 0),
      μ (p.1, μ (p.1, p.2.1, p.2.2.1), p.2.2.2) = μ (p.1, p.2.1, μ (p.1, p.2.2.1, p.2.2.2))) :
    ∀ᶠ p : B × V × V in 𝓝 (b₀, 0, 0),
      μ (p.1, μ (p.1, p.2.1, p.2.1), μ (p.1, p.2.2, p.2.2)) = μ (p.1, μ p, μ p) := by
  have hfst : Tendsto (fun p : B × V × V => p.1) (𝓝 (b₀, 0, 0)) (𝓝 b₀) := continuous_fst.tendsto _
  have hs : Tendsto (fun p : B × V × V => p.2.1) (𝓝 (b₀, 0, 0)) (𝓝 0) :=
    (continuous_fst.comp continuous_snd).tendsto _
  have ht : Tendsto (fun p : B × V × V => p.2.2) (𝓝 (b₀, 0, 0)) (𝓝 0) :=
    (continuous_snd.comp continuous_snd).tendsto _
  have hμ : Tendsto μ (𝓝 (b₀, 0, 0)) (𝓝 0) := by
    have := hc.tendsto
    rwa [h0] at this
  have htt : Tendsto (fun p : B × V × V => μ (p.1, p.2.2, p.2.2)) (𝓝 (b₀, 0, 0)) (𝓝 0) :=
    hμ.comp (hfst.prodMk_nhds (ht.prodMk_nhds ht))
  have orbitMap_conj_smul_one := (hfst.prodMk_nhds (hs.prodMk_nhds (hs.prodMk_nhds htt))).eventually hassoc
  have orbitMap_conj_smul_two := (hfst.prodMk_nhds (hs.prodMk_nhds (ht.prodMk_nhds ht))).eventually hassoc
  have selfLieBasisVector := (hfst.prodMk_nhds (ht.prodMk_nhds (hs.prodMk_nhds ht))).eventually hassoc
  have eA4 := (hfst.prodMk_nhds (hs.prodMk_nhds (ht.prodMk_nhds hμ))).eventually hassoc
  filter_upwards [orbitMap_conj_smul_one, orbitMap_conj_smul_two, selfLieBasisVector, eA4, hcomm] with ⟨b, s, t⟩ a1 a2 a3 a4 c
  dsimp only at a1 a2 a3 a4 c ⊢
  calc μ (b, μ (b, s, s), μ (b, t, t)) = μ (b, s, μ (b, s, μ (b, t, t))) := a1
    _ = μ (b, s, μ (b, μ (b, s, t), t)) := by rw [a2]
    _ = μ (b, s, μ (b, μ (b, t, s), t)) := by rw [c]
    _ = μ (b, s, μ (b, t, μ (b, s, t))) := by rw [a3]
    _ = μ (b, μ (b, s, t), μ (b, s, t)) := a4.symm

end GlobalTheory.CompanionTheory.Ar.Flat.LocalLog
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.DoublingLimitLocalLogarithm
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.DoublingLimitLocalLogarithm
open Set Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat.LocalLog

theorem koenigs_step {B V : Type} [NormedAddCommGroup B] [NormedAddCommGroup V]
    [NormedSpace ℂ V] (b₀ : B) (h : B × V → V) (ρ C : ℝ) (hC : 0 ≤ C)
    (hcontr : ∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, ‖h (b, s)‖ ≤ 3 / 5 * ‖s‖)
    (hquad : ∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, ‖(2 : ℂ) • h (b, s) - s‖ ≤ C * ‖s‖ ^ 2)
    {b : B} (hb : b ∈ ball b₀ ρ) {s : V} (hs : s ∈ ball (0 : V) ρ) (k : ℕ) :
    dist ((2 : ℂ) ^ k • iter h k (b, s)) ((2 : ℂ) ^ (k + 1) • iter h (k + 1) (b, s))
      ≤ C * ‖s‖ ^ 2 * (18 / 25) ^ k := by
  rw [dist_eq_norm, iter_succ, pow_succ, mul_smul, ← smul_sub, norm_smul, norm_sub_rev]
  have hx := iter_mem_ball b₀ h ρ hcontr hb hs k
  have hxn := norm_iter_le b₀ h ρ hcontr hb hs k
  have h2 : ‖(2 : ℂ) ^ k‖ = (2 : ℝ) ^ k := by simp
  rw [h2]
  calc (2 : ℝ) ^ k * ‖(2 : ℂ) • h (b, iter h k (b, s)) - iter h k (b, s)‖
      ≤ (2 : ℝ) ^ k * (C * ‖iter h k (b, s)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (hquad b hb _ hx) (by positivity)
    _ ≤ (2 : ℝ) ^ k * (C * ((3 / 5) ^ k * ‖s‖) ^ 2) := by gcongr
    _ = C * ‖s‖ ^ 2 * (18 / 25) ^ k := by
        have e : (18 / 25 : ℝ) ^ k = 2 ^ k * ((3 / 5) ^ k) ^ 2 := by
          rw [← pow_mul, mul_comm k 2, pow_mul, ← mul_pow]
          norm_num
        rw [e]
        ring

theorem koenigs_limit : ∀ {B V : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]
    [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (b₀ : B) (h : B × V → V)
    (ρ C : ℝ), 0 < ρ → 0 ≤ C →
    (∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, ‖h (b, s)‖ ≤ 3 / 5 * ‖s‖) →
    (∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, ‖(2 : ℂ) • h (b, s) - s‖ ≤ C * ‖s‖ ^ 2) →
    ∃ L : B × V → V,
      TendstoUniformlyOn (fun (k : ℕ) (p : B × V) => (2 : ℂ) ^ k • iter h k p) L atTop
        (ball b₀ ρ ×ˢ ball (0 : V) ρ) ∧
      ∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, ‖L (b, s) - s‖ ≤ 4 * C * ‖s‖ ^ 2 := by
  intro B V _ _ _ _ _ b₀ h ρ C hρ hC hcontr hquad
  set F : ℕ → B × V → V := fun k p => (2 : ℂ) ^ k • iter h k p with hF
  have hstep : ∀ p ∈ ball b₀ ρ ×ˢ ball (0 : V) ρ, ∀ k : ℕ,
      dist (F k p) (F (k + 1) p) ≤ C * ‖p.2‖ ^ 2 * (18 / 25) ^ k := by
    rintro ⟨b, s⟩ ⟨hb, hs⟩ k
    exact koenigs_step b₀ h ρ C hC hcontr hquad hb hs k
  have hr : (18 / 25 : ℝ) < 1 := by norm_num
  have hcauchy : ∀ p ∈ ball b₀ ρ ×ˢ ball (0 : V) ρ, CauchySeq (fun k => F k p) :=
    fun p hp => cauchySeq_of_le_geometric _ _ hr (hstep p hp)
  let L : B × V → V := fun p => limUnder atTop (fun k => F k p)
  have hlim : ∀ p ∈ ball b₀ ρ ×ˢ ball (0 : V) ρ, Tendsto (fun k => F k p) atTop (𝓝 (L p)) :=
    fun p hp => (hcauchy p hp).tendsto_limUnder
  have hdist : ∀ p ∈ ball b₀ ρ ×ˢ ball (0 : V) ρ, ∀ n : ℕ,
      dist (F n p) (L p) ≤ C * ‖p.2‖ ^ 2 * (18 / 25) ^ n / (7 / 25) := by
    intro p hp n
    have h1 := dist_le_of_le_geometric_of_tendsto _ _ hr (hstep p hp) (hlim p hp) n
    rwa [show (1 - 18 / 25 : ℝ) = 7 / 25 by norm_num] at h1
  refine ⟨L, ?_, ?_⟩
  · rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hg : Tendsto (fun n : ℕ => C * ρ ^ 2 * (18 / 25 : ℝ) ^ n / (7 / 25)) atTop (𝓝 0) := by
      have h1 := ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 18 / 25) hr).const_mul
        (C * ρ ^ 2)).div_const (7 / 25 : ℝ)
      simpa using h1
    filter_upwards [hg.eventually (gt_mem_nhds hε)] with n hn
    rintro ⟨b, s⟩ hp
    rw [dist_comm]
    refine lt_of_le_of_lt ((hdist _ hp n).trans ?_) hn
    have hs : ‖s‖ < ρ := by simpa using hp.2
    have hsle : ‖s‖ ≤ ρ := hs.le
    have hsq : ‖s‖ ^ 2 ≤ ρ ^ 2 := by gcongr
    show C * ‖s‖ ^ 2 * (18 / 25) ^ n / (7 / 25) ≤ C * ρ ^ 2 * (18 / 25) ^ n / (7 / 25)
    apply div_le_div_of_nonneg_right _ (by norm_num)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left hsq hC
  · intro b hb s hs
    have h0 := hdist (b, s) ⟨hb, hs⟩ 0
    have e0 : F 0 (b, s) = s := by simp [hF]
    rw [e0, dist_comm, dist_eq_norm] at h0
    calc ‖L (b, s) - s‖ ≤ C * ‖s‖ ^ 2 * (18 / 25) ^ 0 / (7 / 25) := h0
      _ ≤ 4 * C * ‖s‖ ^ 2 := by
        rw [pow_zero, mul_one, div_le_iff₀ (by norm_num)]
        nlinarith [mul_nonneg hC (sq_nonneg ‖s‖)]

end GlobalTheory.CompanionTheory.Ar.Flat.LocalLog
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.DoublingLimitLocalLogarithmStatement
open Set Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubling_limit_local_logarithm : ∀ {B V : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (b₀ : B) (h : B × V → V) (ρ C : ℝ), 0 < ρ → 0 ≤ C → (∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, ‖h (b, s)‖ ≤ 3 / 5 * ‖s‖) → (∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, ‖(2 : ℂ) • h (b, s) - s‖ ≤ C * ‖s‖ ^ 2) → ∃ L : B × V → V, TendstoUniformlyOn (fun (k : ℕ) (p : B × V) => (2 : ℂ) ^ k • GlobalTheory.CompanionTheory.Ar.Flat.LocalLog.iter h k p) L atTop (ball b₀ ρ ×ˢ ball (0 : V) ρ) ∧ ∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, ‖L (b, s) - s‖ ≤ 4 * C * ‖s‖ ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.LocalLog.koenigs_limit | exact GlobalTheory.CompanionTheory.Ar.Flat.LocalLog.koenigs_limit | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.LocalLog.koenigs_limit <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalLogarithmHomomorphism
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalLogarithmHomomorphism
open Set Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat.LocalLog

theorem koenigs_limit_additive_for_law : ∀ {B V : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [NormedAddCommGroup V] [NormedSpace ℂ V] (b₀ : B) (h : B × V → V) (μ : B × V × V → V) (L : B × V → V) (ρ C : ℝ), 0 < ρ → 0 ≤ C → (∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, ‖h (b, s)‖ ≤ 3 / 5 * ‖s‖) → (∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, ∀ t ∈ ball (0 : V) ρ, ‖μ (b, s, t) - s - t‖ ≤ C * ‖s‖ * ‖t‖) → (∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, ∀ t ∈ ball (0 : V) ρ, h (b, μ (b, s, t)) = μ (b, h (b, s), h (b, t))) → (∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, Tendsto (fun k : ℕ => (2 : ℂ) ^ k • GlobalTheory.CompanionTheory.Ar.Flat.LocalLog.iter h k (b, s)) atTop (𝓝 (L (b, s)))) → ∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, ∀ t ∈ ball (0 : V) ρ, μ (b, s, t) ∈ ball (0 : V) ρ → L (b, μ (b, s, t)) = L (b, s) + L (b, t) := by
  intro B V _ _ _ _ b₀ h μ L ρ C _hρ hC hcontr happrox hhom hlim b hb s hs t ht hm
  have hsk := fun k => iter_mem_ball b₀ h ρ hcontr hb hs k
  have htk := fun k => iter_mem_ball b₀ h ρ hcontr hb ht k
  have hiter : ∀ k : ℕ, iter h k (b, μ (b, s, t)) = μ (b, iter h k (b, s), iter h k (b, t)) := by
    intro k
    induction k with
    | zero => rw [iter_zero, iter_zero, iter_zero]
    | succ k ih =>
      rw [iter_succ, iter_succ, iter_succ, ih]
      exact hhom b hb _ (hsk k) _ (htk k)
  have hn2 : ‖(2 : ℂ)‖ = 2 := by simp
  have herr : Tendsto (fun k : ℕ => (2 : ℂ) ^ k •
      (μ (b, iter h k (b, s), iter h k (b, t)) - iter h k (b, s) - iter h k (b, t))) atTop (𝓝 0) := by
    have hg : Tendsto (fun k : ℕ => C * ‖s‖ * ‖t‖ * (18 / 25 : ℝ) ^ k) atTop (𝓝 0) := by
      have := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 18 / 25)
        (by norm_num : (18 / 25 : ℝ) < 1)
      simpa using this.const_mul (C * ‖s‖ * ‖t‖)
    refine squeeze_zero_norm (fun k => ?_) hg
    rw [norm_smul, norm_pow, hn2]
    have h1 := happrox b hb _ (hsk k) _ (htk k)
    have h2 := norm_iter_le b₀ h ρ hcontr hb hs k
    have h3 := norm_iter_le b₀ h ρ hcontr hb ht k
    calc (2 : ℝ) ^ k * ‖μ (b, iter h k (b, s), iter h k (b, t)) - iter h k (b, s) - iter h k (b, t)‖
        ≤ 2 ^ k * (C * ‖iter h k (b, s)‖ * ‖iter h k (b, t)‖) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ 2 ^ k * (C * ((3 / 5) ^ k * ‖s‖) * ((3 / 5) ^ k * ‖t‖)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul (mul_le_mul_of_nonneg_left h2 hC) h3 (norm_nonneg _)
            (mul_nonneg hC (by positivity))
      _ = C * ‖s‖ * ‖t‖ * (18 / 25) ^ k := by
          rw [show (18 / 25 : ℝ) = 2 * (3 / 5) * (3 / 5) by norm_num, mul_pow, mul_pow]
          ring
  have hsum : Tendsto (fun k : ℕ => (2 : ℂ) ^ k • iter h k (b, μ (b, s, t))) atTop
      (𝓝 (L (b, s) + L (b, t) + 0)) := by
    refine (((hlim b hb s hs).add (hlim b hb t ht)).add herr).congr (fun k => ?_)
    rw [hiter k, smul_sub, smul_sub]
    abel
  rw [add_zero] at hsum
  exact tendsto_nhds_unique (hlim b hb _ hm) hsum

end GlobalTheory.CompanionTheory.Ar.Flat.LocalLog
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalLogarithmHomomorphismStatement
open Set Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_logarithm_homomorphism : ∀ {B V : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [NormedAddCommGroup V] [NormedSpace ℂ V] (b₀ : B) (h : B × V → V) (μ : B × V × V → V) (L : B × V → V) (ρ C : ℝ), 0 < ρ → 0 ≤ C → (∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, ‖h (b, s)‖ ≤ 3 / 5 * ‖s‖) → (∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, ∀ t ∈ ball (0 : V) ρ, ‖μ (b, s, t) - s - t‖ ≤ C * ‖s‖ * ‖t‖) → (∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, ∀ t ∈ ball (0 : V) ρ, h (b, μ (b, s, t)) = μ (b, h (b, s), h (b, t))) → (∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, Tendsto (fun k : ℕ => (2 : ℂ) ^ k • GlobalTheory.CompanionTheory.Ar.Flat.LocalLog.iter h k (b, s)) atTop (𝓝 (L (b, s)))) → ∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, ∀ t ∈ ball (0 : V) ρ, μ (b, s, t) ∈ ball (0 : V) ρ → L (b, μ (b, s, t)) = L (b, s) + L (b, t) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.LocalLog.koenigs_limit_additive_for_law | exact GlobalTheory.CompanionTheory.Ar.Flat.LocalLog.koenigs_limit_additive_for_law | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.LocalLog.koenigs_limit_additive_for_law <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.AnalyticDoublingMapLocalInverse
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.AnalyticDoublingMapLocalInverse
open Set Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Metric.FamilyInverse

theorem exists_analytic_family_inverse {B V : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]
    [CompleteSpace B] [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (b₀ : B) (d : B × V → V) (han : AnalyticAt ℂ d (b₀, 0)) (h0 : d (b₀, 0) = 0)
    (hd : HasFDerivAt d ((2 : ℂ) • ContinuousLinearMap.snd ℂ B V) (b₀, 0)) :
    ∃ h : B × V → V, AnalyticAt ℂ h (b₀, 0) ∧ h (b₀, 0) = 0 ∧
      (∀ᶠ p : B × V in 𝓝 (b₀, 0), d (p.1, h p) = p.2) ∧
      (∀ᶠ p : B × V in 𝓝 (b₀, 0), h (p.1, d p) = p.2) := by
  let Φ : B × V → B × V := fun p => (p.1, d p)
  let L : (B × V) →L[ℂ] (B × V) :=
    (ContinuousLinearMap.fst ℂ B V).prod ((2 : ℂ) • ContinuousLinearMap.snd ℂ B V)
  let L' : (B × V) →L[ℂ] (B × V) :=
    (ContinuousLinearMap.fst ℂ B V).prod ((2⁻¹ : ℂ) • ContinuousLinearMap.snd ℂ B V)
  let Le : (B × V) ≃L[ℂ] (B × V) :=
    ContinuousLinearEquiv.equivOfInverse L L'
      (fun p => by simp [L, L', smul_smul]) (fun p => by simp [L, L', smul_smul])
  have hLe : (Le : (B × V) →L[ℂ] (B × V)) = L := rfl
  have hΦan : AnalyticAt ℂ Φ (b₀, 0) := analyticAt_fst.prod han
  have hΦd : HasFDerivAt Φ L (b₀, 0) := hasFDerivAt_fst.prodMk hd
  have hs : HasStrictFDerivAt Φ (Le : (B × V) →L[ℂ] (B × V)) (b₀, 0) := by
    have := hΦan.hasStrictFDerivAt
    rwa [hΦd.fderiv, ← hLe] at this
  have hfix : Φ (b₀, 0) = (b₀, 0) := by simp [Φ, h0]
  let P := hs.toOpenPartialHomeomorph Φ
  have hPc : (P : B × V → B × V) = Φ := hs.toOpenPartialHomeomorph_coe
  have hPan : AnalyticAt ℂ P.symm (P (b₀, 0)) :=
    P.analyticAt_symm' (i := Le) hs.mem_toOpenPartialHomeomorph_source
      (by rw [hPc]; exact hΦan) (by rw [hPc, hΦd.fderiv, hLe])
  have hΨan : AnalyticAt ℂ P.symm (b₀, 0) := by
    have : P (b₀, 0) = (b₀, 0) := by rw [hPc]; exact hfix
    rwa [this] at hPan
  have hright : ∀ᶠ q in 𝓝 (b₀, 0), Φ (P.symm q) = q := by
    have := hs.eventually_right_inverse
    rw [hfix] at this
    exact this
  have hleft : ∀ᶠ p in 𝓝 (b₀, 0), P.symm (Φ p) = p := hs.eventually_left_inverse
  have hΨ0 : P.symm (b₀, 0) = (b₀, 0) := by
    have := hs.localInverse_apply_image
    rw [hfix] at this
    exact this
  refine ⟨fun q => (P.symm q).2, analyticAt_snd.comp hΨan, by simp [hΨ0], ?_, ?_⟩
  · filter_upwards [hright] with q hq
    have e1 := congrArg Prod.fst hq
    have e2 := congrArg Prod.snd hq
    have h1 : (P.symm q).1 = q.1 := e1
    have h2 : d (P.symm q) = q.2 := e2
    have h3 : (q.1, (P.symm q).2) = P.symm q := by rw [← h1]
    rw [h3, h2]
  · filter_upwards [hleft] with p hp
    have e := congrArg Prod.snd hp
    exact e

end GlobalTheory.CompanionTheory.Metric.FamilyInverse
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.AnalyticDoublingMapLocalInverseStatement
open Set Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.analytic_doubling_map_local_inverse : ∀ {B V : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (b₀ : B) (d : B × V → V), AnalyticAt ℂ d (b₀, 0) → d (b₀, 0) = 0 → HasFDerivAt d ((2 : ℂ) • ContinuousLinearMap.snd ℂ B V) (b₀, 0) → ∃ h : B × V → V, AnalyticAt ℂ h (b₀, 0) ∧ h (b₀, 0) = 0 ∧ (∀ᶠ p : B × V in 𝓝 (b₀, 0), d (p.1, h p) = p.2) ∧ (∀ᶠ p : B × V in 𝓝 (b₀, 0), h (p.1, d p) = p.2) := by
  first | exact @GlobalTheory.CompanionTheory.Metric.FamilyInverse.exists_analytic_family_inverse | exact GlobalTheory.CompanionTheory.Metric.FamilyInverse.exists_analytic_family_inverse | (intros; apply GlobalTheory.CompanionTheory.Metric.FamilyInverse.exists_analytic_family_inverse <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.AnalyticGroupLawBoundedCommutator
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.AnalyticGroupLawBoundedCommutator
open Set Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Metric

theorem norm_le_mul_norm_div_of_bounded_on_ball {V W : Type} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] {ψ : V → W} {R M : ℝ}
    (hd : DifferentiableOn ℂ ψ (ball (0 : V) R)) (h0 : ψ 0 = 0)
    (hM : ∀ x ∈ ball (0 : V) R, ‖ψ x‖ ≤ M) {x : V} (hx : x ∈ ball (0 : V) R) :
    ‖ψ x‖ ≤ M * ‖x‖ / R := by
  have h := Complex.dist_le_div_mul_dist_of_mapsTo_ball (R₂ := M) hd (by
    intro y hy
    rw [mem_closedBall, h0, dist_zero_right]
    exact hM y hy) hx
  rw [h0, dist_zero_right, dist_zero_right] at h
  calc ‖ψ x‖ ≤ M / R * ‖x‖ := h
    _ = M * ‖x‖ / R := by ring

theorem norm_le_of_vanishing_on_axes {B V W : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]
    [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
    (b₀ : B) (G : B × V × V → W) (R : ℝ) (hR : 0 < R)
    (hG : DifferentiableOn ℂ G (ball b₀ R ×ˢ ball (0 : V) R ×ˢ ball (0 : V) R))
    (hb : ∀ p ∈ ball b₀ R ×ˢ ball (0 : V) R ×ˢ ball (0 : V) R, ‖G p‖ ≤ 1)
    (hz : ∀ b ∈ ball b₀ R, ∀ s ∈ ball (0 : V) R, G (b, s, 0) = 0 ∧ G (b, 0, s) = 0) :
    ∀ b ∈ ball b₀ R, ∀ s ∈ ball (0 : V) R, ∀ t ∈ ball (0 : V) R,
      ‖G (b, s, t)‖ ≤ ‖s‖ * ‖t‖ / R ^ 2 := by
  intro b hbm s hs t ht

  have h1 : ∀ s ∈ ball (0 : V) R, ∀ t ∈ ball (0 : V) R, ‖G (b, s, t)‖ ≤ ‖s‖ / R := by
    intro s hs t ht
    have hd : DifferentiableOn ℂ (fun s' => G (b, s', t)) (ball (0 : V) R) :=
      hG.comp ((differentiableOn_const b).prodMk (differentiableOn_id.prodMk (differentiableOn_const t)))
        (by intro s' hs'; exact ⟨hbm, hs', ht⟩)
    have h := norm_le_mul_norm_div_of_bounded_on_ball hd (hz b hbm t ht).2
      (fun s' hs' => hb _ ⟨hbm, hs', ht⟩) hs
    rwa [one_mul] at h

  have hd : DifferentiableOn ℂ (fun t' => G (b, s, t')) (ball (0 : V) R) :=
    hG.comp ((differentiableOn_const b).prodMk ((differentiableOn_const s).prodMk differentiableOn_id))
      (by intro t' ht'; exact ⟨hbm, hs, ht'⟩)
  have h := norm_le_mul_norm_div_of_bounded_on_ball hd (hz b hbm s hs).1
    (fun t' ht' => h1 s hs t' ht') ht
  calc ‖G (b, s, t)‖ ≤ ‖s‖ / R * ‖t‖ / R := h
    _ = ‖s‖ * ‖t‖ / R ^ 2 := by ring

end GlobalTheory.CompanionTheory.Metric
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.AnalyticGroupLawBoundedCommutatorStatement
open Set Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.analytic_group_law_bounded_commutator : ∀ {B V W : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] (b₀ : B) (G : B × V × V → W) (R : ℝ), 0 < R → DifferentiableOn ℂ G (ball b₀ R ×ˢ ball (0 : V) R ×ˢ ball (0 : V) R) → (∀ p ∈ ball b₀ R ×ˢ ball (0 : V) R ×ˢ ball (0 : V) R, ‖G p‖ ≤ 1) → (∀ b ∈ ball b₀ R, ∀ s ∈ ball (0 : V) R, G (b, s, 0) = 0 ∧ G (b, 0, s) = 0) → ∀ b ∈ ball b₀ R, ∀ s ∈ ball (0 : V) R, ∀ t ∈ ball (0 : V) R, ‖G (b, s, t)‖ ≤ ‖s‖ * ‖t‖ / R ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.Metric.norm_le_of_vanishing_on_axes | exact GlobalTheory.CompanionTheory.Metric.norm_le_of_vanishing_on_axes | (intros; apply GlobalTheory.CompanionTheory.Metric.norm_le_of_vanishing_on_axes <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannFormPeriodDeterminant
open Set Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_local_log_of_commutative_law : ∀ (n g : ℕ) (b₀ : Fin n → ℂ) (μ : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) → (Fin g → ℂ)), AnalyticAt ℂ μ (b₀, 0, 0) → (∀ᶠ p : (Fin n → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, 0), μ (p.1, p.2, 0) = p.2 ∧ μ (p.1, 0, p.2) = p.2) → (∀ᶠ p : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, 0, 0), μ (p.1, p.2.1, p.2.2) = μ (p.1, p.2.2, p.2.1)) → (∀ᶠ p : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, 0, 0, 0), μ (p.1, μ (p.1, p.2.1, p.2.2.1), p.2.2.2) = μ (p.1, p.2.1, μ (p.1, p.2.2.1, p.2.2.2))) → ∃ L : (Fin n → ℂ) × (Fin g → ℂ) → (Fin g → ℂ), AnalyticAt ℂ L (b₀, 0) ∧ (∀ᶠ b in 𝓝 b₀, L (b, 0) = 0 ∧ HasFDerivAt (fun s => L (b, s)) (ContinuousLinearMap.id ℂ (Fin g → ℂ)) 0) ∧ ∀ᶠ p : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, 0, 0), L (p.1, μ p) = L (p.1, p.2.1) + L (p.1, p.2.2) := by
  intro n g b₀ μ hμ hunit hcomm hassoc
  have hμ0 : μ (b₀, 0, 0) = 0 := hunit.self_of_nhds.1

  set G : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) → (Fin g → ℂ) := fun p => μ p - p.2.1 - p.2.2 with hG
  have hGan : AnalyticAt ℂ G (b₀, 0, 0) :=
    (hμ.sub (analyticAt_fst.comp_of_eq analyticAt_snd rfl)).sub (analyticAt_snd.comp_of_eq analyticAt_snd rfl)
  have hG0 : G (b₀, 0, 0) = 0 := by simp [hG, hμ0]
  have hGsmall : ∀ᶠ p in 𝓝 ((b₀, 0, 0) : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ)), ‖G p‖ < 1 := by
    filter_upwards [hGan.continuousAt (ball_mem_nhds (G (b₀, 0, 0)) one_pos)] with p hp
    simpa [hG0] using hp
  obtain ⟨R₁, hR₁, hball₁⟩ := Metric.eventually_nhds_iff_ball.1 (hGsmall.and hGan.eventually_analyticAt)
  obtain ⟨R₂, hR₂, hball₂⟩ := Metric.eventually_nhds_iff_ball.1 hunit
  set R := min R₁ R₂ with hRdef
  have hR : 0 < R := lt_min hR₁ hR₂
  have hRG : ∀ b ∈ ball b₀ R, ∀ s ∈ ball (0 : Fin g → ℂ) R, ∀ t ∈ ball (0 : Fin g → ℂ) R, ‖G (b, s, t)‖ < 1 ∧ AnalyticAt ℂ G (b, s, t) := by
    intro b hb s hs t ht
    refine hball₁ (b, s, t) ?_
    rw [← ball_prod_same, ← ball_prod_same]
    exact ⟨ball_subset_ball (min_le_left _ _) hb, ball_subset_ball (min_le_left _ _) hs, ball_subset_ball (min_le_left _ _) ht⟩
  have hRu : ∀ b ∈ ball b₀ R, ∀ s ∈ ball (0 : Fin g → ℂ) R, μ (b, s, 0) = s ∧ μ (b, 0, s) = s := by
    intro b hb s hs
    refine hball₂ (b, s) ?_
    rw [← ball_prod_same]
    exact ⟨ball_subset_ball (min_le_right _ _) hb, ball_subset_ball (min_le_right _ _) hs⟩
  have hGbound : ∀ b ∈ ball b₀ R, ∀ s ∈ ball (0 : Fin g → ℂ) R, ∀ t ∈ ball (0 : Fin g → ℂ) R, ‖μ (b, s, t) - s - t‖ ≤ ‖s‖ * ‖t‖ / R ^ 2 := by
    refine GlobalTheory.T.analytic_group_law_bounded_commutator b₀ G R hR ?_ ?_ ?_
    · rintro ⟨b, s, t⟩ ⟨hb, hs, ht⟩
      exact (hRG b hb s hs t ht).2.differentiableAt.differentiableWithinAt
    · rintro ⟨b, s, t⟩ ⟨hb, hs, ht⟩
      exact (hRG b hb s hs t ht).1.le
    · intro b hb s hs
      have := hRu b hb s hs
      simp [hG, this.1, this.2]
  set C : ℝ := 1 / R ^ 2 with hCdef
  have hCpos : 0 < C := by positivity
  have hbound : ∀ b ∈ ball b₀ R, ∀ s ∈ ball (0 : Fin g → ℂ) R, ∀ t ∈ ball (0 : Fin g → ℂ) R, ‖μ (b, s, t) - s - t‖ ≤ C * ‖s‖ * ‖t‖ := by
    intro b hb s hs t ht
    refine (hGbound b hb s hs t ht).trans (le_of_eq ?_)
    rw [hCdef]; ring
  set d : (Fin n → ℂ) × (Fin g → ℂ) → (Fin g → ℂ) := fun p => μ (p.1, p.2, p.2) with hd
  have hdan : AnalyticAt ℂ d (b₀, 0) := by
    have h1 : AnalyticAt ℂ (fun p : (Fin n → ℂ) × (Fin g → ℂ) => (p.1, p.2, p.2)) (b₀, 0) :=
      analyticAt_fst.prod (analyticAt_snd.prod analyticAt_snd)
    exact AnalyticAt.comp_of_eq hμ h1 rfl
  have hd0 : d (b₀, 0) = 0 := hμ0
  have hdderiv : HasFDerivAt d ((2 : ℂ) • ContinuousLinearMap.snd ℂ (Fin n → ℂ) (Fin g → ℂ)) (b₀, 0) := by
    refine HasFDerivAt.of_isLittleO ?_
    rw [Asymptotics.isLittleO_iff]
    intro c hc
    have hmem : ball ((b₀, 0) : (Fin n → ℂ) × (Fin g → ℂ)) (min R (c / C)) ∈ 𝓝 ((b₀, 0) : (Fin n → ℂ) × (Fin g → ℂ)) :=
      ball_mem_nhds _ (lt_min hR (by positivity))
    filter_upwards [hmem] with p hp
    obtain ⟨b, s⟩ := p
    rw [← ball_prod_same] at hp
    obtain ⟨hb, hs⟩ := hp
    have hb' : b ∈ ball b₀ R := ball_subset_ball (min_le_left _ _) hb
    have hs' : s ∈ ball (0 : Fin g → ℂ) R := ball_subset_ball (min_le_left _ _) hs
    have h1 := hbound b hb' s hs' s hs'
    have hsn : ‖s‖ < c / C := by simpa using (ball_subset_ball (min_le_right _ _) hs)
    have heq : d (b, s) - d (b₀, 0) - ((2 : ℂ) • ContinuousLinearMap.snd ℂ (Fin n → ℂ) (Fin g → ℂ)) ((b, s) - (b₀, 0)) = μ (b, s, s) - s - s := by
      rw [hd0]
      simp [hd, two_smul]
      abel
    rw [heq]
    have hle : ‖s‖ ≤ ‖((b, s) : (Fin n → ℂ) × (Fin g → ℂ)) - (b₀, 0)‖ := by
      simp [Prod.norm_def]
    have hCs : C * ‖s‖ ≤ c := ((lt_div_iff₀' hCpos).1 hsn).le
    calc ‖μ (b, s, s) - s - s‖ ≤ C * ‖s‖ * ‖s‖ := h1
      _ ≤ c * ‖s‖ := by gcongr
      _ ≤ c * ‖((b, s) : (Fin n → ℂ) × (Fin g → ℂ)) - (b₀, 0)‖ := by gcongr
  obtain ⟨h, hhan, hh0, H1, H2⟩ := GlobalTheory.T.analytic_doubling_map_local_inverse b₀ d hdan hd0 hdderiv
  have hmed := LocalLog.medial_eventually b₀ μ hμ.continuousAt hμ0 hcomm hassoc
  have hhc : ContinuousAt h (b₀, 0) := hhan.continuousAt
  have t0 : Tendsto (fun p : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) => p.1) (𝓝 (b₀, 0, 0)) (𝓝 b₀) :=
    continuous_fst.tendsto _
  have t1 : Tendsto (fun p : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) => (p.1, p.2.1)) (𝓝 (b₀, 0, 0)) (𝓝 (b₀, 0)) :=
    t0.prodMk_nhds ((continuous_fst.comp continuous_snd).tendsto _)
  have t2 : Tendsto (fun p : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) => (p.1, p.2.2)) (𝓝 (b₀, 0, 0)) (𝓝 (b₀, 0)) :=
    t0.prodMk_nhds ((continuous_snd.comp continuous_snd).tendsto _)
  have ts : Tendsto (fun p : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) => h (p.1, p.2.1)) (𝓝 (b₀, 0, 0)) (𝓝 0) := by
    simpa [Function.comp_def, hh0] using hhc.tendsto.comp t1
  have tt : Tendsto (fun p : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) => h (p.1, p.2.2)) (𝓝 (b₀, 0, 0)) (𝓝 0) := by
    simpa [Function.comp_def, hh0] using hhc.tendsto.comp t2
  have t3 : Tendsto (fun p : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) => (p.1, h (p.1, p.2.1), h (p.1, p.2.2))) (𝓝 (b₀, 0, 0)) (𝓝 (b₀, 0, 0)) :=
    t0.prodMk_nhds (ts.prodMk_nhds tt)
  have t4 : Tendsto (fun p : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) => (p.1, μ (p.1, h (p.1, p.2.1), h (p.1, p.2.2)))) (𝓝 (b₀, 0, 0)) (𝓝 (b₀, 0)) :=
    t0.prodMk_nhds (by simpa [Function.comp_def, hμ0] using hμ.continuousAt.tendsto.comp t3)
  have hhom : ∀ᶠ p : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, 0, 0), h (p.1, μ p) = μ (p.1, h (p.1, p.2.1), h (p.1, p.2.2)) := by
    filter_upwards [t1.eventually H1, t2.eventually H1, t3.eventually hmed, t4.eventually H2] with p e1 e2 e3 e4
    obtain ⟨b, s, t⟩ := p
    have e1' : μ (b, h (b, s), h (b, s)) = s := e1
    have e2' : μ (b, h (b, t), h (b, t)) = t := e2
    have e3' : μ (b, μ (b, h (b, s), h (b, s)), μ (b, h (b, t), h (b, t))) = μ (b, μ (b, h (b, s), h (b, t)), μ (b, h (b, s), h (b, t))) := e3
    have e4' : h (b, μ (b, μ (b, h (b, s), h (b, t)), μ (b, h (b, s), h (b, t)))) = μ (b, h (b, s), h (b, t)) := e4
    rw [e1', e2'] at e3'
    show h (b, μ (b, s, t)) = μ (b, h (b, s), h (b, t))
    rw [e3', e4']
  have hsmall : ∀ᶠ q in 𝓝 ((b₀, 0) : (Fin n → ℂ) × (Fin g → ℂ)), ‖h q‖ < min R (1 / (3 * C)) := by
    have hpos : 0 < min R (1 / (3 * C)) := lt_min hR (by positivity)
    filter_upwards [hhc (ball_mem_nhds (h (b₀, 0)) hpos)] with p hp
    simpa [hh0] using hp
  obtain ⟨ρ₁, hρ₁, hb₁⟩ := Metric.eventually_nhds_iff_ball.1 (H1.and (hhan.eventually_analyticAt.and hsmall))
  obtain ⟨ρ₂, hρ₂, hb₂⟩ := Metric.eventually_nhds_iff_ball.1 hhom
  set ρ := min R (min ρ₁ ρ₂) with hρdef
  have hρ : 0 < ρ := lt_min hR (lt_min hρ₁ hρ₂)
  have hρR : ρ ≤ R := min_le_left _ _
  have hρ1 : ρ ≤ ρ₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hρ2 : ρ ≤ ρ₂ := (min_le_right _ _).trans (min_le_right _ _)
  have hq : ∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : Fin g → ℂ) ρ, μ (b, h (b, s), h (b, s)) = s ∧ AnalyticAt ℂ h (b, s) ∧ ‖h (b, s)‖ < min R (1 / (3 * C)) := by
    intro b hb s hs
    refine hb₁ (b, s) ?_
    rw [← ball_prod_same]
    exact ⟨ball_subset_ball hρ1 hb, ball_subset_ball hρ1 hs⟩
  have hhomρ : ∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : Fin g → ℂ) ρ, ∀ t ∈ ball (0 : Fin g → ℂ) ρ, h (b, μ (b, s, t)) = μ (b, h (b, s), h (b, t)) := by
    intro b hb s hs t ht
    refine hb₂ (b, s, t) ?_
    rw [← ball_prod_same, ← ball_prod_same]
    exact ⟨ball_subset_ball hρ2 hb, ball_subset_ball hρ2 hs, ball_subset_ball hρ2 ht⟩
  have hboundρ : ∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : Fin g → ℂ) ρ, ∀ t ∈ ball (0 : Fin g → ℂ) ρ, ‖μ (b, s, t) - s - t‖ ≤ C * ‖s‖ * ‖t‖ :=
    fun b hb s hs t ht => hbound b (ball_subset_ball hρR hb) s (ball_subset_ball hρR hs) t (ball_subset_ball hρR ht)
  have key : ∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : Fin g → ℂ) ρ, ‖(2 : ℂ) • h (b, s) - s‖ ≤ C * ‖h (b, s)‖ ^ 2 := by
    intro b hb s hs
    obtain ⟨e1, -, e3⟩ := hq b hb s hs
    have hs' : h (b, s) ∈ ball (0 : Fin g → ℂ) R := by
      rw [mem_ball_zero_iff]; exact e3.trans_le (min_le_left _ _)
    have h1 := hbound b (ball_subset_ball hρR hb) _ hs' _ hs'
    rw [e1] at h1
    have h2 : (2 : ℂ) • h (b, s) - s = -(s - h (b, s) - h (b, s)) := by
      rw [two_smul]; abel
    rw [h2, norm_neg]
    calc _ ≤ _ := h1
      _ = _ := by ring
  have hcontr : ∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : Fin g → ℂ) ρ, ‖h (b, s)‖ ≤ 3 / 5 * ‖s‖ := by
    intro b hb s hs
    have h1 := key b hb s hs
    obtain ⟨-, -, e3⟩ := hq b hb s hs
    have h3 : ‖h (b, s)‖ < 1 / (3 * C) := e3.trans_le (min_le_right _ _)
    have h4 : C * ‖h (b, s)‖ ≤ 1 / 3 := by
      rw [lt_div_iff₀ (by positivity)] at h3
      nlinarith
    have h5 : ‖(2 : ℂ) • h (b, s)‖ = 2 * ‖h (b, s)‖ := by simp [norm_smul]
    have h6 : ‖(2 : ℂ) • h (b, s)‖ ≤ ‖(2 : ℂ) • h (b, s) - s‖ + ‖s‖ := norm_le_norm_sub_add _ _
    have h7 := norm_nonneg (h (b, s))
    nlinarith
  have hquad : ∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : Fin g → ℂ) ρ, ‖(2 : ℂ) • h (b, s) - s‖ ≤ C * ‖s‖ ^ 2 := by
    intro b hb s hs
    refine (key b hb s hs).trans ?_
    have h1 := hcontr b hb s hs
    have h2 : ‖h (b, s)‖ ≤ ‖s‖ := by linarith [norm_nonneg s]
    gcongr
  obtain ⟨L, hLu, hLb⟩ := GlobalTheory.T.doubling_limit_local_logarithm b₀ h ρ C hρ hCpos.le hcontr hquad
  have hdiffh : DifferentiableOn ℂ h (ball b₀ ρ ×ˢ ball (0 : Fin g → ℂ) ρ) := by
    rintro ⟨b, s⟩ ⟨hb, hs⟩
    exact (hq b hb s hs).2.1.differentiableAt.differentiableWithinAt
  have hit := fun k => LocalLog.iter_differentiableOn b₀ h ρ hdiffh hcontr k
  have hDopen : IsOpen (ball b₀ ρ ×ˢ ball (0 : Fin g → ℂ) ρ) := isOpen_ball.prod isOpen_ball
  have hLd : DifferentiableOn ℂ L (ball b₀ ρ ×ˢ ball (0 : Fin g → ℂ) ρ) :=
    GlobalTheory.SCV.differentiableOn_of_tendstoLocallyUniformlyOn hDopen hLu.tendstoLocallyUniformlyOn
      (Eventually.of_forall fun k => by
        show DifferentiableOn ℂ ((2 : ℂ) ^ k • GlobalTheory.CompanionTheory.Ar.Flat.LocalLog.iter h k) _
        exact (hit k).const_smul _)
  have hLan : AnalyticAt ℂ L (b₀, 0) :=
    GlobalTheory.SCV.analyticOnNhd_of_differentiableOn hDopen hLd (b₀, 0)
      (Set.mk_mem_prod (mem_ball_self hρ) (mem_ball_self (x := (0 : Fin g → ℂ)) hρ))
  refine ⟨L, hLan, ?_, ?_⟩
  · filter_upwards [ball_mem_nhds b₀ hρ] with b hb
    have hL0 : L (b, 0) = 0 := by
      have := hLb b hb 0 (mem_ball_self hρ)
      simpa using this
    refine ⟨hL0, ?_⟩
    refine HasFDerivAt.of_isLittleO ?_
    rw [Asymptotics.isLittleO_iff]
    intro c hc
    have hc' : 0 < c / (4 * C) := by positivity
    filter_upwards [ball_mem_nhds (0 : Fin g → ℂ) (lt_min hρ hc')] with s hs
    have hs1 : s ∈ ball (0 : Fin g → ℂ) ρ := ball_subset_ball (min_le_left _ _) hs
    have hs2 : ‖s‖ < c / (4 * C) := by simpa using (ball_subset_ball (min_le_right _ _) hs)
    have h1 := hLb b hb s hs1
    have h2 : 4 * C * ‖s‖ ≤ c := ((lt_div_iff₀' (by positivity)).1 hs2).le
    simp only [hL0, sub_zero, ContinuousLinearMap.id_apply]
    calc ‖L (b, s) - s‖ ≤ 4 * C * ‖s‖ ^ 2 := h1
      _ = 4 * C * ‖s‖ * ‖s‖ := by ring
      _ ≤ c * ‖s‖ := by gcongr
  · have hpt : ∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : Fin g → ℂ) ρ, Tendsto (fun k : ℕ => (2 : ℂ) ^ k • GlobalTheory.CompanionTheory.Ar.Flat.LocalLog.iter h k (b, s)) atTop (𝓝 (L (b, s))) :=
      fun b hb s hs => hLu.tendsto_at ⟨hb, hs⟩
    have hadd := GlobalTheory.T.local_logarithm_homomorphism b₀ h μ L ρ C hρ hCpos.le hcontr hboundρ hhomρ hpt
    have hμs : ∀ᶠ p in 𝓝 ((b₀, 0, 0) : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ)), μ p ∈ ball (0 : Fin g → ℂ) ρ := by
      filter_upwards [hμ.continuousAt (ball_mem_nhds (μ (b₀, 0, 0)) hρ)] with p hp
      simpa [hμ0] using hp
    filter_upwards [ball_mem_nhds ((b₀, 0, 0) : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ)) hρ, hμs] with p hp hq'
    obtain ⟨b, s, t⟩ := p
    rw [← ball_prod_same, ← ball_prod_same] at hp
    exact hadd b hp.1 s hp.2.1 t hp.2.2 hq'

end GlobalTheory.CompanionTheory.Ar.Flat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannFormPeriodDeterminantStatement
open Set Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_group_law_germ : ∀ (n g : ℕ) (b₀ : Fin n → ℂ) (μ : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) → (Fin g → ℂ)), AnalyticAt ℂ μ (b₀, 0, 0) → (∀ᶠ p : (Fin n → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, 0), μ (p.1, p.2, 0) = p.2 ∧ μ (p.1, 0, p.2) = p.2) → (∀ᶠ p : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, 0, 0), μ (p.1, p.2.1, p.2.2) = μ (p.1, p.2.2, p.2.1)) → (∀ᶠ p : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, 0, 0, 0), μ (p.1, μ (p.1, p.2.1, p.2.2.1), p.2.2.2) = μ (p.1, p.2.1, μ (p.1, p.2.2.1, p.2.2.2))) → ∃ L : (Fin n → ℂ) × (Fin g → ℂ) → (Fin g → ℂ), AnalyticAt ℂ L (b₀, 0) ∧ (∀ᶠ b in 𝓝 b₀, L (b, 0) = 0 ∧ HasFDerivAt (fun s => L (b, s)) (ContinuousLinearMap.id ℂ (Fin g → ℂ)) 0) ∧ ∀ᶠ p : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, 0, 0), L (p.1, μ p) = L (p.1, p.2.1) + L (p.1, p.2.2) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.exists_local_log_of_commutative_law | exact GlobalTheory.CompanionTheory.Ar.Flat.exists_local_log_of_commutative_law | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.exists_local_log_of_commutative_law <;> assumption)
end
