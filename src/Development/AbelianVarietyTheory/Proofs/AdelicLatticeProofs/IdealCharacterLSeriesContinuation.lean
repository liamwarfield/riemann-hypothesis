module

public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmoothedIdealCharacterSumMainTermIdealClassRepre
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CountableIdealSummableAbsNormRpow

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsEntireMellinSmoothedDirichletSum
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors
open Set Filter Asymptotics Topology

namespace GlobalTheory.SmoothedSumMellin

lemma weight_bound {wt : ℝ → ℂ} (hc : Continuous wt) {a b : ℝ}
    (hs : ∀ y, wt y ≠ 0 → a ≤ y ∧ y ≤ b) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y : ℝ, 0 < y → ‖wt y‖ ≤ M * y ^ (-2 : ℝ) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max C 0 * (max b 1) ^ 2, by positivity, fun y hy => ?_⟩
  by_cases h0 : wt y = 0
  · rw [h0, norm_zero]
    positivity
  obtain ⟨hay, hyb⟩ := hs y h0
  have hB : ‖wt y‖ ≤ max C 0 := (hC y ⟨hay, hyb⟩).trans (le_max_left _ _)
  rw [Real.rpow_neg hy.le, Real.rpow_two]
  have hyb' : y ^ 2 ≤ (max b 1) ^ 2 := pow_le_pow_left₀ hy.le (hyb.trans (le_max_left _ _)) 2
  have h1 : 1 ≤ (max b 1) ^ 2 * (y ^ 2)⁻¹ := by
    rw [le_mul_inv_iff₀ (by positivity)]
    linarith
  calc ‖wt y‖ ≤ max C 0 * 1 := by rw [mul_one]; exact hB
    _ ≤ max C 0 * ((max b 1) ^ 2 * (y ^ 2)⁻¹) := mul_le_mul_of_nonneg_left h1 (le_max_right _ _)
    _ = _ := by ring

lemma weight_mellinConvergent {wt : ℝ → ℂ} (hc : Continuous wt) {a b : ℝ} (ha : 0 < a)
    (hs : ∀ y, wt y ≠ 0 → a ≤ y ∧ y ≤ b) (s : ℂ) : MellinConvergent wt s := by
  have hev0 : ∀ᶠ t in 𝓝[>] (0 : ℝ), wt t = 0 := by
    filter_upwards [Ioo_mem_nhdsGT ha] with t ht
    by_contra h
    exact absurd (hs t h).1 (not_le.2 ht.2)
  have hevT : ∀ᶠ t in atTop, wt t = 0 := by
    filter_upwards [eventually_gt_atTop b] with t ht
    by_contra h
    exact absurd (hs t h).2 (not_le.2 ht)
  exact mellinConvergent_of_isBigO_rpow (a := s.re + 1) (b := s.re - 1)
    (hc.locallyIntegrable.locallyIntegrableOn _)
    ((Asymptotics.isBigO_zero _ _).congr' (hevT.mono fun t ht => ht.symm) EventuallyEq.rfl)
    (by linarith)
    ((Asymptotics.isBigO_zero _ _).congr' (hev0.mono fun t ht => ht.symm) EventuallyEq.rfl)
    (by linarith)

lemma continuousOn_sum {ι : Type} {a : ι → ℂ} {N : ι → ℝ} {wt : ℝ → ℂ} (hc : Continuous wt)
    {α β : ℝ} (hs : ∀ y, wt y ≠ 0 → α ≤ y ∧ y ≤ β) (hN : ∀ i, a i ≠ 0 → 1 ≤ N i)
    (hsum : Summable fun i => ‖a i‖ * N i ^ (-2 : ℝ)) :
    ContinuousOn (fun t : ℝ => ∑' i, a i * wt (t * N i)) (Ioi 0) := by
  obtain ⟨M, hM0, hM⟩ := weight_bound hc hs
  intro t0 ht0
  have ht0' : (0 : ℝ) < t0 := ht0
  have hcont : ContinuousOn (fun t : ℝ => ∑' i, a i * wt (t * N i)) (Ioi (t0 / 2)) := by
    refine continuousOn_tsum (u := fun i => ‖a i‖ * N i ^ (-2 : ℝ) * (M * (t0 / 2) ^ (-2 : ℝ)))
      (fun i => (continuous_const.mul (hc.comp (continuous_id.mul continuous_const))).continuousOn)
      (hsum.mul_right _) ?_
    intro i t ht
    have ht' : t0 / 2 < t := ht
    by_cases hai : a i = 0
    · simp [hai]
    have hNi : (1 : ℝ) ≤ N i := hN i hai
    have htN : 0 < t * N i := mul_pos (by linarith) (by linarith)
    rw [norm_mul]
    have h1 := hM (t * N i) htN
    rw [Real.mul_rpow (by linarith) (by linarith)] at h1
    have h2 : t ^ (-2 : ℝ) ≤ (t0 / 2) ^ (-2 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) ht'.le (by norm_num)
    have hNn : 0 ≤ N i ^ (-2 : ℝ) := Real.rpow_nonneg (by linarith) _
    calc ‖a i‖ * ‖wt (t * N i)‖ ≤ ‖a i‖ * (M * (t ^ (-2 : ℝ) * N i ^ (-2 : ℝ))) :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ ≤ ‖a i‖ * (M * ((t0 / 2) ^ (-2 : ℝ) * N i ^ (-2 : ℝ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right h2 hNn) hM0) (norm_nonneg _)
      _ = _ := by ring
  exact (hcont.continuousAt (Ioi_mem_nhds (by linarith))).continuousWithinAt

lemma integral_norm_comp (wt : ℝ → ℂ) (s : ℂ) {n : ℝ} (hn : 0 < n) :
    ∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ (s - 1) • wt (t * n)‖
      = n ^ (-s.re) * ∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ (s - 1) • wt t‖ := by
  have h1 : ∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ (s - 1) • wt (t * n)‖ =
      ∫ t in Ioi (0 : ℝ), (fun u : ℝ => (u / n) ^ (s.re - 1) * ‖wt u‖) (t * n) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    simp only
    rw [_root_.norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht, mul_div_cancel_right₀ t hn.ne']
    simp
  have h2 : ∫ t in Ioi (0 : ℝ), (t / n) ^ (s.re - 1) * ‖wt t‖ =
      n ^ (1 - s.re) * ∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ (s - 1) • wt t‖ := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have ht' : (0 : ℝ) < t := ht
    rw [_root_.norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht', Real.div_rpow ht'.le hn.le]
    have h3 : n ^ (1 - s.re) = (n ^ (s.re - 1))⁻¹ := by rw [← Real.rpow_neg hn.le, neg_sub]
    rw [h3]
    simp only [Complex.sub_re, Complex.one_re]
    ring
  rw [h1, integral_comp_mul_right_Ioi (fun u : ℝ => (u / n) ^ (s.re - 1) * ‖wt u‖) 0 hn, zero_mul]
  rw [h2, smul_eq_mul, ← mul_assoc]
  congr 1
  rw [← Real.rpow_neg_one, ← Real.rpow_add hn]
  congr 1
  ring

lemma mellin_sum {ι : Type} [Countable ι] {a : ι → ℂ} {N : ι → ℝ} {wt : ℝ → ℂ} {s : ℂ}
    (hw : MellinConvergent wt s) (hN : ∀ i, a i ≠ 0 → 1 ≤ N i)
    (hsum : Summable fun i => ‖a i‖ * N i ^ (-s.re)) :
    mellin (fun t : ℝ => ∑' i, a i * wt (t * N i)) s
      = mellin wt s * ∑' i, a i * (N i : ℂ) ^ (-s) := by
  have hI : ∀ i, a i ≠ 0 → 0 < N i := fun i hi => by linarith [hN i hi]
  set I := ∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ (s - 1) • wt t‖ with hIdef
  set G : ι → ℝ → ℂ := fun i t => (t : ℂ) ^ (s - 1) • (a i * wt (t * N i)) with hG
  have hGint : ∀ i, Integrable (G i) (volume.restrict (Ioi 0)) := by
    intro i
    by_cases hai : a i = 0
    · simp [hG, hai]
    · have hc : MellinConvergent (fun t => wt (t * N i)) s := by
        have := (MellinConvergent.comp_mul_left (f := wt) (s := s) (hI i hai)).2 hw
        simpa only [mul_comm] using this
      exact hc.const_smul (a i)
  have hGnorm : ∀ i, ∫ t in Ioi (0 : ℝ), ‖G i t‖ = ‖a i‖ * N i ^ (-s.re) * I := by
    intro i
    by_cases hai : a i = 0
    · simp [hG, hai]
    · have h1 : ∀ t, ‖G i t‖ = ‖a i‖ * ‖(t : ℂ) ^ (s - 1) • wt (t * N i)‖ := fun t => by
        simp only [hG, _root_.norm_smul, norm_mul]
        ring
      simp_rw [h1]
      rw [integral_const_mul, integral_norm_comp wt s (hI i hai)]
      ring
  have hsumG : Summable fun i => ∫ t in Ioi (0 : ℝ), ‖G i t‖ := by
    simp_rw [hGnorm]
    exact hsum.mul_right I
  have key := integral_tsum_of_summable_integral_norm hGint hsumG
  have hM : mellin (fun t : ℝ => ∑' i, a i * wt (t * N i)) s = ∫ t in Ioi (0 : ℝ), ∑' i, G i t := by
    rw [mellin]
    congr 1
    funext t
    exact (tsum_const_smul'' _).symm
  have hGi : ∀ i, ∫ t in Ioi (0 : ℝ), G i t = a i * (N i : ℂ) ^ (-s) * mellin wt s := by
    intro i
    by_cases hai : a i = 0
    · simp [hG, hai]
    · have h1 : ∫ t in Ioi (0 : ℝ), G i t = a i * mellin (fun t => wt (t * N i)) s := by
        rw [mellin, ← integral_const_mul]
        congr 1
        funext t
        simp only [hG, smul_eq_mul]
        ring
      rw [h1, mellin_comp_mul_right wt s (hI i hai), smul_eq_mul, mul_assoc]
  rw [hM, ← key]
  simp_rw [hGi]
  rw [tsum_mul_right, mul_comm]

theorem exists_entire_mellin : ∀ (ι : Type) [Countable ι] (a : ι → ℂ) (N : ι → ℝ) (R : ℂ) (wt : ℝ → ℂ), ContDiff ℝ ∞ wt → (∃ a b : ℝ, 0 < a ∧ ∀ y, wt y ≠ 0 → a ≤ y ∧ y ≤ b) → (∀ i, a i ≠ 0 → 1 ≤ N i) → (∀ σ : ℝ, 1 < σ → Summable fun i => ‖a i‖ * N i ^ (-σ)) → (∀ A : ℕ, ∃ C : ℝ, ∀ t : ℝ, 0 < t → t ≤ 1 → ‖∑' i, a i * wt (t * N i) - R / (t : ℂ)‖ ≤ C * t ^ A) → ∃ Z : ℂ → ℂ, Differentiable ℂ Z ∧ Z 1 = R ∧ ∀ s : ℂ, 1 < s.re → Z s = mellin wt s * ((s - 1) * ∑' i, a i * (N i : ℂ) ^ (-s)) := by
  intro ι _ a N R wt hwt hsupp0 hN hsum hasym
  obtain ⟨α, β, hα, hsupp⟩ := hsupp0
  have hc : Continuous wt := hwt.continuous
  set F : ℝ → ℂ := fun t => ∑' i, a i * wt (t * N i) with hF
  set G : ℝ → ℂ := indicator (Ioc 0 1) (fun t : ℝ => (t : ℂ) ^ (-1 : ℂ)) with hG
  set H : ℝ → ℂ := fun t => F t - R * G t with hH
  have hFtop : ∀ t, max β 1 < t → F t = 0 := by
    intro t ht
    have h1 : ∀ i, a i * wt (t * N i) = 0 := by
      intro i
      by_cases hai : a i = 0
      · rw [hai, zero_mul]
      · have hNi := hN i hai
        have hw0 : wt (t * N i) = 0 := by
          by_contra h
          have h2 := (hsupp _ h).2
          have h3 : t ≤ t * N i := le_mul_of_one_le_right (by linarith [le_max_right β 1]) hNi
          linarith [le_max_left β 1]
        rw [hw0, mul_zero]
    simp only [hF, h1, tsum_zero]
  have hFc : ContinuousOn F (Ioi 0) := continuousOn_sum hc hsupp hN (hsum 2 (by norm_num))
  have hGc : ContinuousOn (fun t : ℝ => R * (t : ℂ) ^ (-1 : ℂ)) (Ioi 0) := fun t ht =>
    (continuousAt_const.mul (ContinuousAt.cpow (Complex.continuous_ofReal.continuousAt (x := t))
      continuousAt_const (Complex.ofReal_mem_slitPlane.2 ht))).continuousWithinAt
  have hRGloc : LocallyIntegrableOn (fun t => R * G t) (Ioi 0) := by
    rw [locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed]
    intro k hk hkc
    have h1 : IntegrableOn (fun t : ℝ => R * (t : ℂ) ^ (-1 : ℂ)) k :=
      (hGc.mono hk).integrableOn_compact hkc
    have h2 := h1.indicator (measurableSet_Ioc (a := (0 : ℝ)) (b := 1))
    refine h2.congr_fun (fun t _ => ?_) hkc.measurableSet
    simp only [hG, indicator]
    split_ifs <;> simp
  have hHloc : LocallyIntegrableOn H (Ioi 0) :=
    (hFc.locallyIntegrableOn measurableSet_Ioi).sub hRGloc
  have htop : ∀ c : ℝ, H =O[atTop] (· ^ c) := by
    intro c
    refine (Asymptotics.isBigO_zero _ _).congr' ?_ EventuallyEq.rfl
    filter_upwards [eventually_gt_atTop (max β 1)] with t ht
    have ht1 : t ∉ Ioc (0 : ℝ) 1 := fun h => by linarith [h.2, le_max_right β 1]
    simp only [hH, hFtop t ht, hG, Set.indicator_of_notMem ht1, mul_zero, sub_zero]
  have hbot : ∀ A : ℕ, H =O[𝓝[>] 0] (· ^ (A : ℝ)) := by
    intro A
    obtain ⟨C, hC⟩ := hasym A
    refine Asymptotics.IsBigO.of_bound C ?_
    filter_upwards [Ioc_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
    have ht0 : 0 < t := ht.1
    have hHt : H t = F t - R / t := by
      simp only [hH, hG, Set.indicator_of_mem ht, Complex.cpow_neg_one, div_eq_mul_inv]
    rw [hHt, Real.rpow_natCast, Real.norm_of_nonneg (pow_nonneg ht0.le A)]
    exact hC t ht0 ht.2
  have hbot' : ∀ s : ℂ, ∃ b : ℝ, b < s.re ∧ H =O[𝓝[>] 0] (· ^ (-b)) := by
    intro s
    refine ⟨-((⌈-s.re⌉₊ + 1 : ℕ) : ℝ), ?_, ?_⟩
    · push_cast
      linarith [Nat.le_ceil (-s.re)]
    · simpa only [neg_neg] using hbot (⌈-s.re⌉₊ + 1)
  have hHconv : ∀ s : ℂ, MellinConvergent H s := by
    intro s
    obtain ⟨b, hb, hbO⟩ := hbot' s
    exact mellinConvergent_of_isBigO_rpow (a := s.re + 1) (b := b) hHloc (htop _) (by linarith) hbO hb
  have hdiff : Differentiable ℂ (mellin H) := by
    intro s
    obtain ⟨b, hb, hbO⟩ := hbot' s
    exact mellin_differentiableAt_of_isBigO_rpow (a := s.re + 1) (b := b) hHloc (htop _)
      (by linarith) hbO hb
  refine ⟨fun s => (s - 1) * mellin H s + R, ?_, by simp, ?_⟩
  · exact ((differentiable_id.sub_const 1).mul hdiff).add_const R
  · intro s hs
    have hs1 : s + -1 ≠ 0 := by
      intro h
      have : (s + -1).re = 0 := by rw [h]; simp
      simp at this
      linarith
    have hGm := hasMellin_cpow_Ioc (-1) (s := s) (by rw [Complex.neg_re, Complex.one_re]; linarith)
    have hGconv : MellinConvergent G s := hGm.1
    have hGval : mellin G s = 1 / (s + -1) := hGm.2
    have e1 : F = fun t => H t + R • G t := by
      funext t
      simp only [hH, smul_eq_mul]
      ring
    have hmF : mellin F s = mellin H s + R * (1 / (s + -1)) := by
      rw [e1, (hasMellin_add (hHconv s) (hGconv.const_smul R)).2, mellin_const_smul, hGval,
        smul_eq_mul]
    have hmel : mellin F s = mellin wt s * ∑' i, a i * (N i : ℂ) ^ (-s) :=
      mellin_sum (weight_mellinConvergent hc hα hsupp s) hN (hsum s.re hs)
    have hHs : mellin H s = mellin F s - R * (1 / (s + -1)) := by rw [hmF]; ring
    show (s - 1) * mellin H s + R = mellin wt s * ((s - 1) * ∑' i, a i * (N i : ℂ) ^ (-s))
    rw [hHs, hmel, ← sub_eq_add_neg]
    rw [← sub_eq_add_neg] at hs1
    field_simp
    ring

end GlobalTheory.SmoothedSumMellin
end

open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors

namespace GlobalTheory

open Filter Topology Set Asymptotics in
private theorem eq_of_norm_sub_div_le {f : ℝ → ℂ} {R R' : ℂ} {C C' : ℝ}
    (h : ∀ t : ℝ, 0 < t → t ≤ 1 → ‖f t - R / t‖ ≤ C)
    (h' : ∀ t : ℝ, 0 < t → t ≤ 1 → ‖f t - R' / t‖ ≤ C') : R = R' := by
  by_contra hne
  have hd : 0 < ‖R - R'‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  set D := |C| + |C'| + 1 with hD_def
  have hD : 0 < D := by positivity
  set t := min 1 (‖R - R'‖ / (2 * D)) with ht_def
  have ht0 : 0 < t := lt_min one_pos (by positivity)
  have ht1 : t ≤ 1 := min_le_left _ _
  have htD : t * D ≤ ‖R - R'‖ / 2 := by
    calc t * D ≤ ‖R - R'‖ / (2 * D) * D := by gcongr; exact min_le_right _ _
      _ = ‖R - R'‖ / 2 := by field_simp
  have htc : (t : ℂ) ≠ 0 := ofReal_ne_zero.2 ht0.ne'
  have key : R - R' = (t : ℂ) * ((f t - R' / t) - (f t - R / t)) := by
    field_simp
    ring
  have hle : ‖R - R'‖ ≤ t * (C' + C) := by
    rw [key, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0.le]
    gcongr
    exact (norm_sub_le _ _).trans (add_le_add (h' t ht0 ht1) (h t ht0 ht1))
  have : t * (C' + C) ≤ t * D :=
    mul_le_mul_of_nonneg_left (by linarith [le_abs_self C, le_abs_self C']) ht0.le
  linarith

open Filter Topology Set Asymptotics in
private theorem exists_differentiable_eq_div_of_family {ι : Type} (M G : ι → ℂ → ℂ)
    (F : ℂ → ℂ) (hM : ∀ i, Differentiable ℂ (M i)) (hG : ∀ i, Differentiable ℂ (G i))
    (hGF : ∀ i s, 1 < s.re → G i s = M i s * F s) (hne : ∀ s, ∃ i, M i s ≠ 0) :
    ∃ Z : ℂ → ℂ, Differentiable ℂ Z ∧ (∀ s, 1 < s.re → Z s = F s) ∧
      ∀ i s, M i s ≠ 0 → Z s = G i s / M i s := by
  have hcross : ∀ i j s, G i s * M j s = G j s * M i s := by
    intro i j s
    have hU : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    have h2 : (fun s => G i s * M j s) =ᶠ[𝓝 (2 : ℂ)] fun s => G j s * M i s := by
      filter_upwards [hU.mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with s hs
      rw [hGF i s hs, hGF j s hs]
      ring
    have hf : AnalyticOnNhd ℂ (fun s => G i s * M j s) univ :=
      fun z _ => ((hG i).mul (hM j)).analyticAt z
    have hg : AnalyticOnNhd ℂ (fun s => G j s * M i s) univ :=
      fun z _ => ((hG j).mul (hM i)).analyticAt z
    exact hf.eqOn_of_preconnected_of_eventuallyEq hg isPreconnected_univ (mem_univ _) h2
      (mem_univ s)
  choose w hw using hne
  have hZ : ∀ i s, M i s ≠ 0 → G (w s) s / M (w s) s = G i s / M i s := by
    intro i s hi
    rw [div_eq_div_iff (hw s) hi]
    exact hcross (w s) i s
  refine ⟨fun s => G (w s) s / M (w s) s, ?_, ?_, hZ⟩
  · intro s₀
    have hev : ∀ᶠ s in 𝓝 s₀, M (w s₀) s ≠ 0 :=
      (hM (w s₀)).continuous.continuousAt.eventually_ne (hw s₀)
    exact (((hG _) s₀).div ((hM _) s₀) (hw s₀)).congr_of_eventuallyEq
      (hev.mono fun s hs => hZ _ s hs)
  · intro s hs
    simp only
    rw [hGF _ s hs, mul_div_cancel_left₀ _ (hw s)]

open Filter Topology Set Asymptotics in
private theorem differentiable_mellin_of_support_in_Icc_pos {w : ℝ → ℂ} (hw : Continuous w) {a b : ℝ}
    (ha : 0 < a) (hab : ∀ y, w y ≠ 0 → a ≤ y ∧ y ≤ b) : Differentiable ℂ (mellin w) := by
  intro s
  have htop : w =ᶠ[atTop] 0 := by
    filter_upwards [eventually_gt_atTop b] with y hy
    by_contra h
    exact absurd (hab y h).2 (not_le.2 hy)
  have hzero : w =ᶠ[𝓝[>] 0] 0 := by
    filter_upwards [Ioo_mem_nhdsGT ha] with y hy
    by_contra h
    exact absurd (hab y h).1 (not_le.2 hy.2)
  exact mellin_differentiableAt_of_isBigO_rpow (a := s.re + 1) (b := s.re - 1)
    (hw.locallyIntegrable.locallyIntegrableOn _)
    ((isBigO_zero _ _).congr' htop.symm EventuallyEq.rfl) (by linarith)
    ((isBigO_zero _ _).congr' hzero.symm EventuallyEq.rfl) (by linarith)

open Filter Topology Set Asymptotics in
private theorem exists_weight_mellin_ne_zero (s₀ : ℂ) :
    ∃ w : ℝ → ℂ, ContDiff ℝ ∞ w ∧ (∃ a b : ℝ, 0 < a ∧ ∀ y, w y ≠ 0 → a ≤ y ∧ y ≤ b) ∧
      mellin w s₀ ≠ 0 := by
  let ψ : ContDiffBump (2 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  have hψ0 : ∀ y : ℝ, y ≤ 0 → ψ y = 0 := fun y hy => ψ.zero_of_le_dist (by
    rw [Real.dist_eq, abs_of_neg (by linarith)]
    show (1 : ℝ) ≤ _
    linarith)
  refine ⟨fun y => Complex.exp (-(s₀ - 1) * (Real.log y : ℂ)) * (ψ y : ℂ), ?_,
    ⟨1, 3, one_pos, ?_⟩, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ tsupport ψ
    · have hx0 : x ≠ 0 := by
        rintro rfl
        rw [ψ.tsupport_eq, Metric.mem_closedBall, Real.dist_eq] at hx
        norm_num at hx
      have h1 : ContDiffAt ℝ ∞ (fun y : ℝ => Complex.exp (-(s₀ - 1) * (Real.log y : ℂ))) x :=
        Complex.contDiff_exp.contDiffAt.comp x (contDiffAt_const.mul
          (ofRealCLM.contDiff.contDiffAt.comp x (Real.contDiffAt_log.2 hx0)))
      exact h1.mul (ofRealCLM.contDiff.comp ψ.contDiff).contDiffAt
    · have hev : (fun y => Complex.exp (-(s₀ - 1) * (Real.log y : ℂ)) * (ψ y : ℂ)) =ᶠ[𝓝 x]
          fun _ => 0 :=
        (notMem_tsupport_iff_eventuallyEq.1 hx).mono fun y hy => by simp [hy]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  · intro y hy
    have hψy : ψ y ≠ 0 := fun h => hy (by simp [h])
    have hmem : y ∈ Metric.ball (2 : ℝ) 1 := by
      rw [← ψ.support_eq]
      exact hψy
    rw [Real.ball_eq_Ioo] at hmem
    constructor <;> linarith [hmem.1, hmem.2]
  · have hint : ∫ y in Ioi (0 : ℝ), (y : ℂ) ^ (s₀ - 1) •
        (Complex.exp (-(s₀ - 1) * (Real.log y : ℂ)) * (ψ y : ℂ)) =
        ∫ y in Ioi (0 : ℝ), ((ψ y : ℝ) : ℂ) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
      simp only [smul_eq_mul]
      rw [Complex.cpow_def_of_ne_zero (ofReal_ne_zero.2 (ne_of_gt hy)),
        ← Complex.ofReal_log (le_of_lt hy), ← mul_assoc, ← Complex.exp_add,
        show (Real.log y : ℂ) * (s₀ - 1) + -(s₀ - 1) * (Real.log y : ℂ) = 0 by ring,
        Complex.exp_zero, one_mul]
    unfold mellin
    rw [hint, integral_complex_ofReal, setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun y (hy : y ∉ Ioi (0 : ℝ)) => hψ0 y (not_lt.1 hy))]
    exact ofReal_ne_zero.2 ψ.integral_pos.ne'

open Filter Topology Set Asymptotics in
theorem _root_.GlobalTheory.idealCharacter_LSeries_continuation : ∀ (K : Type) [Field K] [NumberField K] (m : Ideal (𝓞 K)) (X : Ideal (𝓞 K) → ℂ) (φ : mixedSpace K → ℂ), m ≠ ⊥ → X ⊥ = 0 → (∀ I J, X (I * J) = X I * X J) → (∀ I, I ≠ ⊥ → I ⊔ m = ⊤ → ‖X I‖ = 1) → (∀ I, I ⊔ m ≠ ⊤ → X I = 0) → (∀ x y, φ (x * y) = φ x * φ y) → (∀ (t : ℝ) x, 0 < t → φ (t • x) = φ x) → ContDiffOn ℝ ∞ φ {x | mixedEmbedding.norm x ≠ 0} → (∀ x, mixedEmbedding.norm x ≠ 0 → ‖φ x‖ = 1) → (∀ β : 𝓞 K, β ≠ 0 → β - 1 ∈ m → X (Ideal.span {β}) = φ (mixedEmbedding K β)) → ∃ Z : ℂ → ℂ, Differentiable ℂ Z ∧ (∀ s : ℂ, 1 < s.re → Z s = (s - 1) * ∑' I, X I * ((Ideal.absNorm I : ℕ) : ℂ) ^ (-s)) ∧ ((∃ J, J ≠ ⊥ ∧ J ⊔ m = ⊤ ∧ X J ≠ 1) → Z 1 = 0) := by
  intro K _ _ m X φ hm hX0 hXmul hXn hXz hφmul hφh hφs hφn hβ
  have hmain := _root_.GlobalTheory.smoothedSum_main_term_representatives K m X φ hm hX0 hXmul
    hXn hXz hφmul hφh hφs hφn hβ
  obtain ⟨hcount, hsum⟩ := _root_.GlobalTheory.countable_ideal_and_summable_absNorm_rpow K
  haveI := hcount
  choose b hb using _root_.GlobalTheory.exists_integral_ideal_in_class_coprime K m hm
  have hbij : Function.Bijective fun c => ClassGroup.mk0 (b c) := by
    have : (fun c => ClassGroup.mk0 (b c)) = id := funext fun c => (hb c).1
    rw [this]
    exact Function.bijective_id
  have hbm : ∀ c, (b c : Ideal (𝓞 K)) ⊔ m = ⊤ := fun c => (hb c).2
  have hXle : ∀ I, ‖X I‖ ≤ 1 := by
    intro I
    by_cases hI : I = ⊥
    · rw [hI, hX0, norm_zero]
      exact zero_le_one
    by_cases hIm : I ⊔ m = ⊤
    · rw [hXn I hI hIm]
    · rw [hXz I hIm, norm_zero]
      exact zero_le_one
  have hN : ∀ I, X I ≠ 0 → (1 : ℝ) ≤ (Ideal.absNorm I : ℝ) := by
    intro I hI
    have hI0 : I ≠ ⊥ := fun h => hI (h ▸ hX0)
    have : Ideal.absNorm I ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
    exact_mod_cast Nat.one_le_iff_ne_zero.2 this
  have hsumm : ∀ σ : ℝ, 1 < σ → Summable fun I => ‖X I‖ * (Ideal.absNorm I : ℝ) ^ (-σ) := by
    intro σ hσ
    refine ((hsum σ hσ).1).of_nonneg_of_le
      (fun I => mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)) fun I => ?_
    exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hXle I)
  set S := ∑ c, (X (b c : Ideal (𝓞 K)))⁻¹ with hS
  set F : ℂ → ℂ := fun s => (s - 1) * ∑' I, X I * ((Ideal.absNorm I : ℕ) : ℂ) ^ (-s) with hF
  have hweight : ∀ w : {w : ℝ → ℂ // ContDiff ℝ ∞ w ∧
      ∃ a b : ℝ, 0 < a ∧ ∀ y, w y ≠ 0 → a ≤ y ∧ y ≤ b},
      ∃ G : ℂ → ℂ, Differentiable ℂ G ∧ (∀ s, 1 < s.re → G s = mellin w.1 s * F s) ∧
        ((∃ J, J ≠ ⊥ ∧ J ⊔ m = ⊤ ∧ X J ≠ 1) → G 1 = 0) := by
    rintro ⟨w, hw, hwsupp⟩
    obtain ⟨κ, hκ⟩ := hmain w hw hwsupp
    obtain ⟨G, hGd, hG1, hGs⟩ := _root_.GlobalTheory.SmoothedSumMellin.exists_entire_mellin (Ideal (𝓞 K)) X
      (fun I => (Ideal.absNorm I : ℝ)) (κ * S) w hw hwsupp hN hsumm (hκ b hbij hbm)
    refine ⟨G, hGd, fun s hs => ?_, fun hJ => ?_⟩
    · rw [hGs s hs]
      simp only [F, Complex.ofReal_natCast]
    · rw [hG1]
      obtain ⟨J, hJ0, hJm, hXJ⟩ := hJ
      let J' : (Ideal (𝓞 K))⁰ := ⟨J, mem_nonZeroDivisors_of_ne_zero hJ0⟩
      let b' : ClassGroup (𝓞 K) → (Ideal (𝓞 K))⁰ :=
        fun c => b (c * (ClassGroup.mk0 J')⁻¹) * J'
      have hb'mk : ∀ c, ClassGroup.mk0 (b' c) = c := by
        intro c
        simp only [b', map_mul, (hb _).1, inv_mul_cancel_right]
      have hbij' : Function.Bijective fun c => ClassGroup.mk0 (b' c) := by
        have : (fun c => ClassGroup.mk0 (b' c)) = id := funext hb'mk
        rw [this]
        exact Function.bijective_id
      have hbm' : ∀ c, (b' c : Ideal (𝓞 K)) ⊔ m = ⊤ := by
        intro c
        simp only [b', Submonoid.coe_mul]
        rw [sup_comm, Ideal.sup_mul_eq_of_coprime_left (by rw [sup_comm]; exact hbm _), sup_comm]
        exact hJm
      have hS' : ∑ c, (X (b' c : Ideal (𝓞 K)))⁻¹ = (X J)⁻¹ * S := by
        simp only [b', Submonoid.coe_mul, hXmul, mul_inv, hS, Finset.mul_sum]
        exact Fintype.sum_equiv (Equiv.mulRight (ClassGroup.mk0 J')⁻¹) _ _ fun c => by
          simp only [Equiv.coe_mulRight]
          ring
      have heq : κ * S = κ * ((X J)⁻¹ * S) := by
        obtain ⟨C, hC⟩ := hκ b hbij hbm 0
        obtain ⟨C', hC'⟩ := hκ b' hbij' hbm' 0
        rw [← hS']
        refine eq_of_norm_sub_div_le (f := fun t => ∑' I, X I * w (t * (Ideal.absNorm I : ℝ))) (C := C) (C' := C') (fun t h0 h1 => ?_) (fun t h0 h1 => ?_)
        · have := hC t h0 h1
          rwa [pow_zero, mul_one] at this
        · have := hC' t h0 h1
          rwa [pow_zero, mul_one] at this
      have hinv : (X J)⁻¹ ≠ 1 := fun h => hXJ (inv_eq_one.1 h)
      have h0 : κ * S * (1 - (X J)⁻¹) = 0 := by linear_combination heq
      rcases mul_eq_zero.1 h0 with h | h
      · exact h
      · exact absurd (sub_eq_zero.1 h).symm hinv
  choose G hGd hGF hG1 using hweight
  obtain ⟨Z, hZd, hZF, hZdiv⟩ := exists_differentiable_eq_div_of_family (fun w => mellin w.1) G F
    (fun w => by
      obtain ⟨a, c, ha, hac⟩ := w.2.2
      exact differentiable_mellin_of_support_in_Icc_pos w.2.1.continuous ha hac)
    hGd hGF (fun s => by
      obtain ⟨w, hw, hws, hne⟩ := exists_weight_mellin_ne_zero s
      exact ⟨⟨w, hw, hws⟩, hne⟩)
  refine ⟨Z, hZd, hZF, fun hJ => ?_⟩
  obtain ⟨w, hw, hws, hne⟩ := exists_weight_mellin_ne_zero 1
  rw [hZdiv ⟨w, hw, hws⟩ 1 hne, hG1 _ hJ, zero_div]

end GlobalTheory
