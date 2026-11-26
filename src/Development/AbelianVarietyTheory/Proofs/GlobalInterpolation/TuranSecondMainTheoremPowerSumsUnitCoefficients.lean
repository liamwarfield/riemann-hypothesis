module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsProdAbsSubGeOnSegment
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology Polynomial

namespace GlobalTheory

theorem exists_prod_abs_sub_ge_on_segment : ∀ (N : ℕ) (x : Fin N → ℝ) (a δ : ℝ), 0 < δ →
    ∃ r : ℝ, a ≤ r ∧ r ≤ a + δ ∧ (δ / (2 * Real.exp 1)) ^ N ≤ ∏ i, |r - x i| := by
  intro N x a δ hδ
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact ⟨a, le_rfl, by linarith, by simp⟩
  by_contra hcon
  push Not at hcon
  have he : (2 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have he0 : (0 : ℝ) < Real.exp 1 := by linarith
  set m : ℝ := δ / (2 * Real.exp 1) with hm
  have hm0 : 0 < m := by positivity
  let P : ℝ[X] := ∏ i : Fin N, (C (Real.exp 1) * X + C ((a + δ / 2 - x i) / m))
  have hlc : P.leadingCoeff = Real.exp 1 ^ N := by
    simp only [P, leadingCoeff_prod, leadingCoeff_linear he0.ne']
    simp
  have hdeg : P.degree ≤ N := by
    have : P.degree = ∑ _i : Fin N, (1 : WithBot ℕ) := by
      simp only [P, degree_prod, degree_linear he0.ne']
    rw [this]; simp
  have hb : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |P.eval t| ≤ 1 := by
    intro t ht
    have h1 := hcon (a + δ / 2 + δ / 2 * t) (by nlinarith [ht.1]) (by nlinarith [ht.2])
    have h2 : |P.eval t| = (∏ i, |a + δ / 2 + δ / 2 * t - x i|) / m ^ N := by
      simp only [P, eval_prod, Finset.abs_prod]
      have : ∀ i : Fin N, |eval t (C (Real.exp 1) * X + C ((a + δ / 2 - x i) / m))|
          = |a + δ / 2 + δ / 2 * t - x i| / m := by
        intro i
        have : eval t (C (Real.exp 1) * X + C ((a + δ / 2 - x i) / m))
            = (a + δ / 2 + δ / 2 * t - x i) / m := by
          simp only [eval_add, eval_mul, eval_C, eval_X, hm]
          field_simp
          ring
        rw [this, abs_div, abs_of_pos hm0]
      simp only [this, Finset.prod_div_distrib]
      simp
    rw [h2, div_le_one (by positivity)]
    exact h1.le
  have h3 := Polynomial.Chebyshev.leadingCoeff_le_of_forall_abs_le_one hdeg hb
  rw [hlc] at h3
  have h4 : (2 : ℝ) ^ (N - 1) ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
  have h5 : (2 : ℝ) ^ N < Real.exp 1 ^ N := pow_lt_pow_left₀ he (by norm_num) hN.ne'
  linarith

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsInterpolationExteriorSmallCoeffs
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsInterpolationExteriorSmallCoeffs
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology

namespace GlobalTheory.ExteriorInterpolation

theorem exists_coeffs (l : ℕ) (z : Fin l → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1) :
    ∃ a : ℕ → ℂ, (∀ w : ℂ, ∏ i, (w - z i) = ∑ k ∈ Finset.range (l + 1), a k * w ^ k) ∧
      ∑ k ∈ Finset.range (l + 1), ‖a k‖ ≤ 2 ^ l := by
  classical
  obtain ⟨P, hP⟩ : ∃ P : Polynomial ℂ, P = ∏ i, (Polynomial.X + Polynomial.C (-z i)) := ⟨_, rfl⟩
  refine ⟨fun k => P.coeff k, fun w => ?_, ?_⟩
  · have hdeg : P.natDegree < l + 1 := by
      have h1 := Polynomial.natDegree_prod_le (s := Finset.univ)
        (f := fun i => Polynomial.X + Polynomial.C (-z i))
      simp only [Polynomial.natDegree_X_add_C, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul, mul_one] at h1
      rw [hP]
      omega
    rw [← Polynomial.eval_eq_sum_range' hdeg, hP, Polynomial.eval_prod]
    simp [sub_eq_add_neg]
  · calc ∑ k ∈ Finset.range (l + 1), ‖P.coeff k‖
          ≤ ∑ k ∈ Finset.range (l + 1), ((l.choose (l - k) : ℕ) : ℝ) := by
          apply Finset.sum_le_sum
          intro k hk
          have hk' : k ≤ (Finset.univ : Finset (Fin l)).card := by
            simpa [Nat.lt_succ_iff] using hk
          rw [hP, Finset.prod_X_add_C_coeff _ _ hk']
          calc ‖∑ t ∈ (Finset.univ : Finset (Fin l)).powersetCard
                  ((Finset.univ : Finset (Fin l)).card - k), ∏ i ∈ t, -z i‖
              ≤ ∑ t ∈ (Finset.univ : Finset (Fin l)).powersetCard
                  ((Finset.univ : Finset (Fin l)).card - k), (1 : ℝ) := by
                apply norm_sum_le_of_le
                intro t _
                rw [norm_prod]
                exact Finset.prod_le_one₀ (fun i _ => norm_nonneg _)
                  (fun i _ => by rw [norm_neg]; exact hz i)
            _ = ((l.choose (l - k) : ℕ) : ℝ) := by
                simp [Finset.card_powersetCard, Finset.card_univ]
      _ = ∑ k ∈ Finset.range (l + 1), ((l.choose k : ℕ) : ℝ) := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [Nat.choose_symm (by simpa [Nat.lt_succ_iff] using hk)]
      _ = 2 ^ l := by exact_mod_cast Nat.sum_range_choose l

theorem exists_divided (l : ℕ) (z : Fin l → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1) :
    ∃ b : Fin l → ℂ → ℂ, (∀ j, Continuous (b j)) ∧ (∀ j ζ, ‖ζ‖ ≤ 1 → ‖b j ζ‖ ≤ 2 ^ l) ∧
      ∀ ζ w : ℂ, (∑ j, b j ζ * w ^ (j : ℕ)) * (ζ - w) = ∏ i, (ζ - z i) - ∏ i, (w - z i) := by
  obtain ⟨a, ha, hsum⟩ := exists_coeffs l z hz
  refine ⟨fun j ζ => ∑ k ∈ Finset.range (l + 1),
    if (j : ℕ) < k then a k * ζ ^ (k - 1 - j) else 0, ?_, ?_, ?_⟩
  · intro j
    exact continuous_finsetSum _ (fun k _ => by split_ifs <;> fun_prop)
  · intro j ζ hζ
    calc ‖∑ k ∈ Finset.range (l + 1), if (j : ℕ) < k then a k * ζ ^ (k - 1 - j) else 0‖
        ≤ ∑ k ∈ Finset.range (l + 1), ‖a k‖ := by
          apply norm_sum_le_of_le
          intro k _
          split_ifs
          · rw [norm_mul, norm_pow]
            exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hζ)
          · simp
      _ ≤ 2 ^ l := hsum
  · intro ζ w
    rw [ha ζ, ha w, ← Finset.sum_sub_distrib]
    have e1 : (∑ j : Fin l, (∑ k ∈ Finset.range (l + 1),
          if (j : ℕ) < k then a k * ζ ^ (k - 1 - j) else 0) * w ^ (j : ℕ))
        = ∑ k ∈ Finset.range (l + 1), ∑ j ∈ Finset.range l,
          (if j < k then a k * ζ ^ (k - 1 - j) else 0) * w ^ j := by
      rw [Fin.sum_univ_eq_sum_range (fun j => (∑ k ∈ Finset.range (l + 1),
        if j < k then a k * ζ ^ (k - 1 - j) else 0) * w ^ j) l]
      simp_rw [Finset.sum_mul]
      exact Finset.sum_comm
    rw [e1, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    have hkl : k ≤ l := by simpa [Nat.lt_succ_iff] using hk
    have e2 : ∑ j ∈ Finset.range l, (if j < k then a k * ζ ^ (k - 1 - j) else 0) * w ^ j
        = a k * ∑ j ∈ Finset.range k, w ^ j * ζ ^ (k - 1 - j) := by
      rw [Finset.mul_sum,
        show Finset.range k = (Finset.range l).filter (· < k) by ext j; simp; omega,
        Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> ring
    have e3 : (∑ j ∈ Finset.range k, w ^ j * ζ ^ (k - 1 - j)) * (ζ - w) = ζ ^ k - w ^ k := by
      rw [← neg_sub w ζ, mul_neg, geom_sum₂_mul]
      ring
    rw [e2, mul_assoc, e3]
    ring

theorem cauchy_exterior (g : ℂ → ℂ) (r : ℝ) (hr : 0 < r)
    (hg : DifferentiableOn ℂ g {w | r ≤ ‖w‖}) (h0 : Tendsto g (Filter.cocompact ℂ) (𝓝 0))
    (w : ℂ) (hw : r < ‖w‖) :
    ∮ ζ in C(0, r), (ζ - w)⁻¹ * g ζ = -(2 * Real.pi * I * g w) := by
  have hS : {ζ : ℂ | r ≤ ‖ζ‖} ∈ 𝓝 w :=
    Filter.mem_of_superset ((isOpen_lt continuous_const continuous_norm).mem_nhds hw)
      (fun ζ hζ => by simp only [Set.mem_ofPred_eq] at hζ ⊢; exact hζ.le)
  have hgw : DifferentiableAt ℂ g w := hg.differentiableAt hS
  obtain ⟨F, hF⟩ : ∃ F : ℂ → ℂ, F = dslope g w := ⟨_, rfl⟩
  have hFc : ContinuousOn F {ζ : ℂ | r ≤ ‖ζ‖} := by
    rw [hF]
    exact (continuousOn_dslope hS).mpr ⟨hg.continuousOn, hgw⟩
  have main : ∀ R : ℝ, ‖w‖ < R → (∮ ζ in C(0, r), (ζ - w)⁻¹ * g ζ)
      = (∮ ζ in C(0, R), (ζ - w)⁻¹ * g ζ) - 2 * Real.pi * I * g w := by
    intro R hR
    have hrR : r ≤ R := (hw.trans hR).le
    have hsub : ∀ ρ, r ≤ ρ → Metric.sphere (0 : ℂ) ρ ⊆ {ζ : ℂ | r ≤ ‖ζ‖} := by
      intro ρ h1 ζ hζ
      rw [mem_sphere_zero_iff_norm] at hζ
      show r ≤ ‖ζ‖
      rw [hζ]
      exact h1
    have split : ∀ ρ, r ≤ ρ → ‖w‖ ≠ ρ → (∮ ζ in C(0, ρ), (ζ - w)⁻¹ * g ζ)
        = g w * (∮ ζ in C(0, ρ), (ζ - w)⁻¹) + ∮ ζ in C(0, ρ), F ζ := by
      intro ρ h1 hne
      have hρ : 0 ≤ ρ := hr.le.trans h1
      have hne' : ∀ ζ ∈ Metric.sphere (0 : ℂ) ρ, ζ - w ≠ 0 := by
        intro ζ hζ h
        rw [mem_sphere_zero_iff_norm] at hζ
        rw [sub_eq_zero] at h
        rw [h] at hζ
        exact hne hζ
      have c1 : ContinuousOn (fun ζ : ℂ => (ζ - w)⁻¹) (Metric.sphere (0 : ℂ) ρ) :=
        (continuousOn_id.sub continuousOn_const).inv₀ hne'
      rw [← smul_eq_mul (g w), ← circleIntegral.integral_smul (g w) _ 0 ρ,
        ← circleIntegral.integral_add
          (show CircleIntegrable (fun ζ => g w • (ζ - w)⁻¹) 0 ρ from
            (ContinuousOn.circleIntegrable hρ (by fun_prop (disch := exact hne'))))
          ((hFc.mono (hsub ρ h1)).circleIntegrable hρ)]
      apply circleIntegral.integral_congr hρ
      intro ζ hζ
      have hz := hne' ζ hζ
      simp only [hF, dslope_of_ne _ (sub_ne_zero.mp hz), slope_def_field, smul_eq_mul]
      field_simp
      ring
    have hann : (∮ ζ in C(0, R), F ζ) = ∮ ζ in C(0, r), F ζ := by
      apply circleIntegral_eq_of_differentiable_on_annulus_off_countable hr hrR
        (Set.countable_singleton w)
      · refine hFc.mono ?_
        intro ζ hζ
        have := hζ.2
        rw [Metric.mem_ball, dist_zero_right, not_lt] at this
        exact this
      · intro ζ hζ
        have hζ1 := hζ.1.2
        rw [Metric.mem_closedBall, dist_zero_right, not_le] at hζ1
        have hζw : ζ ≠ w := hζ.2
        rw [hF, differentiableAt_dslope_of_ne hζw]
        exact hg.differentiableAt
          (Filter.mem_of_superset ((isOpen_lt continuous_const continuous_norm).mem_nhds hζ1)
            (fun x hx => by simp only [Set.mem_ofPred_eq] at hx ⊢; exact hx.le))
    have hzero : (∮ ζ in C(0, r), (ζ - w)⁻¹) = 0 := by
      have hne0 : ∀ ζ ∈ Metric.closedBall (0 : ℂ) r, ζ - w ≠ 0 := by
        intro ζ hζ h
        rw [Metric.mem_closedBall, dist_zero_right] at hζ
        rw [sub_eq_zero] at h
        rw [h] at hζ
        linarith
      apply circleIntegral_eq_zero_of_differentiable_on_off_countable hr.le Set.countable_empty
      · exact (continuousOn_id.sub continuousOn_const).inv₀ hne0
      · intro ζ hζ
        exact (differentiableAt_id.sub_const w).inv
          (hne0 ζ (Metric.ball_subset_closedBall hζ.1))
    have hone : (∮ ζ in C(0, R), (ζ - w)⁻¹) = 2 * Real.pi * I :=
      circleIntegral.integral_sub_inv_of_mem_ball (by simpa using hR)
    rw [split r le_rfl (ne_of_gt hw), split R hrR (ne_of_lt hR), hann, hzero, hone]
    ring
  obtain ⟨S, hS'⟩ : ∃ S, S = ∮ ζ in C(0, r), (ζ - w)⁻¹ * g ζ := ⟨_, rfl⟩
  rw [← hS']
  have hK : ∀ ε > 0, ‖S + 2 * Real.pi * I * g w‖ ≤ 4 * Real.pi * ε := by
    intro ε hε
    have hev : ∀ᶠ ζ in cocompact ℂ, ‖g ζ‖ ≤ ε := by
      filter_upwards [h0 (Metric.closedBall_mem_nhds 0 hε)] with ζ hζ
      simpa using hζ
    obtain ⟨K, hKc, hKs⟩ := (Filter.hasBasis_cocompact.eventually_iff).mp hev
    obtain ⟨M, hM⟩ := hKc.isBounded.subset_closedBall 0
    set R : ℝ := max (M + 1) (2 * ‖w‖ + 1) with hRdef
    have hR1 : M + 1 ≤ R := le_max_left _ _
    have hR2 : 2 * ‖w‖ + 1 ≤ R := le_max_right _ _
    have hRpos : 0 < R := by linarith [norm_nonneg w]
    have hwR : ‖w‖ < R := by linarith [norm_nonneg w]
    rw [hS', main R hwR]
    simp only [sub_add_cancel]
    have hb : ∀ ζ ∈ Metric.sphere (0 : ℂ) R, ‖(ζ - w)⁻¹ * g ζ‖ ≤ 2 / R * ε := by
      intro ζ hζ
      rw [mem_sphere_zero_iff_norm] at hζ
      have hgz : ‖g ζ‖ ≤ ε := by
        apply hKs
        intro hK'
        have := hM hK'
        rw [Metric.mem_closedBall, dist_zero_right] at this
        linarith
      have hd : R / 2 ≤ ‖ζ - w‖ := by
        have := norm_sub_norm_le ζ w
        linarith
      have hinv : ‖ζ - w‖⁻¹ ≤ 2 / R := by
        rw [show 2 / R = (R / 2)⁻¹ by field_simp]
        exact inv_anti₀ (by positivity) hd
      rw [norm_mul, norm_inv]
      exact mul_le_mul hinv hgz (norm_nonneg _) (by positivity)
    calc ‖∮ ζ in C(0, R), (ζ - w)⁻¹ * g ζ‖ ≤ 2 * Real.pi * R * (2 / R * ε) :=
          circleIntegral.norm_integral_le_of_norm_le_const hRpos.le hb
      _ = 4 * Real.pi * ε := by field_simp; ring
  have h00 : ‖S + 2 * Real.pi * I * g w‖ = 0 := by
    apply le_antisymm _ (norm_nonneg _)
    by_contra hpos'
    have hpos := lt_of_not_ge hpos'
    have h8 := hK (‖S + 2 * Real.pi * I * g w‖ / (8 * Real.pi)) (by positivity)
    have : 4 * Real.pi * (‖S + 2 * Real.pi * I * g w‖ / (8 * Real.pi))
        = ‖S + 2 * Real.pi * I * g w‖ / 2 := by
      field_simp
      ring
    rw [this] at h8
    linarith
  have := norm_eq_zero.mp h00
  linear_combination this

private theorem circleIntegral_finset_sum' {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ) (c : ℂ) (R : ℝ)
    (hf : ∀ i ∈ s, CircleIntegrable (f i) c R) :
    (∮ z in C(c, R), ∑ i ∈ s, f i z) = ∑ i ∈ s, ∮ z in C(c, R), f i z := by
  simp only [circleIntegral, Finset.smul_sum]
  exact intervalIntegral.integral_finsetSum (fun i hi => (hf i hi).out)

theorem interpolation : ∀ (l : ℕ) (z : Fin l → ℂ) (g : ℂ → ℂ) (r G : ℝ), 0 < r → r ≤ 1 → (∀ i, r < ‖z i‖ ∧ ‖z i‖ ≤ 1) → DifferentiableOn ℂ g {w | r ≤ ‖w‖} → Tendsto g (Filter.cocompact ℂ) (𝓝 0) → (∀ w : ℂ, ‖w‖ = r → ‖g w‖ ≤ G * ‖∏ i, (w - z i)‖) → ∃ c : Fin l → ℂ, (∀ i, ∑ j, c j * z i ^ (j : ℕ) = g (z i)) ∧ ∑ j, ‖c j‖ ≤ 4 ^ l * r * G := by
  intro l z g r G hr hr1 hz hg h0 hG
  obtain ⟨b, hbc, hbb, hbid⟩ := exists_divided l z (fun i => (hz i).2)
  have hPne : ∀ ζ ∈ Metric.sphere (0 : ℂ) r, ∏ k, (ζ - z k) ≠ 0 := by
    intro ζ hζ
    rw [Finset.prod_ne_zero_iff]
    intro k _ h
    rw [mem_sphere_zero_iff_norm] at hζ
    rw [sub_eq_zero] at h
    have := (hz k).1
    rw [← h, hζ] at this
    exact lt_irrefl _ this
  have hsph : Metric.sphere (0 : ℂ) r ⊆ {w : ℂ | r ≤ ‖w‖} := by
    intro ζ hζ
    rw [mem_sphere_zero_iff_norm] at hζ
    show r ≤ ‖ζ‖
    rw [hζ]
  have hcont : ∀ j, ContinuousOn (fun ζ => g ζ / (∏ k, (ζ - z k)) * b j ζ)
      (Metric.sphere (0 : ℂ) r) := by
    intro j
    refine ContinuousOn.mul ?_ (hbc j).continuousOn
    exact (hg.continuousOn.mono hsph).div (by fun_prop) hPne
  obtain ⟨c, hc⟩ : ∃ c : Fin l → ℂ,
      c = fun j => -(2 * (Real.pi : ℂ) * I)⁻¹ * ∮ ζ in C(0, r), g ζ / (∏ k, (ζ - z k)) * b j ζ :=
    ⟨_, rfl⟩
  have hpi : (2 * (Real.pi : ℂ) * I) ≠ 0 := by
    simp [Real.pi_ne_zero, I_ne_zero]
  refine ⟨c, fun i => ?_, ?_⟩
  · have hwi := (hz i).1
    have e1 : ∑ j, c j * z i ^ (j : ℕ) = -(2 * (Real.pi : ℂ) * I)⁻¹ *
        ∑ j : Fin l, ∮ ζ in C(0, r), z i ^ (j : ℕ) • (g ζ / (∏ k, (ζ - z k)) * b j ζ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [circleIntegral.integral_smul, hc, smul_eq_mul]
      ring
    rw [e1, ← circleIntegral_finset_sum' Finset.univ
      (fun (j : Fin l) ζ => z i ^ (j : ℕ) • ((g ζ / ∏ k, (ζ - z k)) * b j ζ)) 0 r
      (fun j _ => ContinuousOn.circleIntegrable hr.le ((hcont j).const_smul (z i ^ (j : ℕ))))]
    have e2 : (∮ ζ in C(0, r), ∑ j : Fin l, z i ^ (j : ℕ) • (g ζ / (∏ k, (ζ - z k)) * b j ζ))
        = ∮ ζ in C(0, r), (ζ - z i)⁻¹ * g ζ := by
      apply circleIntegral.integral_congr hr.le
      intro ζ hζ
      have hPζ := hPne ζ hζ
      have hzne : ζ - z i ≠ 0 := by
        intro h
        rw [sub_eq_zero] at h
        rw [mem_sphere_zero_iff_norm, h] at hζ
        rw [hζ] at hwi
        exact lt_irrefl _ hwi
      have e := hbid ζ (z i)
      have hPz : ∏ k, (z i - z k) = 0 := Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)
      rw [hPz, sub_zero] at e
      have hsum : ∑ j, b j ζ * z i ^ (j : ℕ) = (∏ k, (ζ - z k)) / (ζ - z i) :=
        eq_div_of_mul_eq hzne e
      have e3 : ∑ j : Fin l, z i ^ (j : ℕ) • (g ζ / (∏ k, (ζ - z k)) * b j ζ)
          = g ζ / (∏ k, (ζ - z k)) * ∑ j, b j ζ * z i ^ (j : ℕ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [smul_eq_mul]
        ring
      simp only
      rw [e3, hsum]
      field_simp
    rw [e2, cauchy_exterior g r hr hg h0 (z i) hwi]
    field_simp
  · have hsph1 : ∀ ζ ∈ Metric.sphere (0 : ℂ) r, ‖ζ‖ = r := fun ζ hζ =>
      mem_sphere_zero_iff_norm.mp hζ
    have hG0 : 0 ≤ G := by
      have hmem : ((r : ℂ)) ∈ Metric.sphere (0 : ℂ) r := by
        rw [mem_sphere_zero_iff_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
      have hpos : 0 < ‖∏ k, ((r : ℂ) - z k)‖ := norm_pos_iff.mpr (hPne _ hmem)
      have h1 := hG (r : ℂ) (hsph1 _ hmem)
      by_contra hneg
      have hlt : G * ‖∏ k, ((r : ℂ) - z k)‖ < 0 := mul_neg_of_neg_of_pos (lt_of_not_ge hneg) hpos
      linarith [norm_nonneg (g (r : ℂ))]
    have hbound : ∀ j, ∀ ζ ∈ Metric.sphere (0 : ℂ) r,
        ‖g ζ / (∏ k, (ζ - z k)) * b j ζ‖ ≤ G * 2 ^ l := by
      intro j ζ hζ
      have hpos : 0 < ‖∏ k, (ζ - z k)‖ := norm_pos_iff.mpr (hPne ζ hζ)
      have hq : ‖g ζ‖ / ‖∏ k, (ζ - z k)‖ ≤ G := by
        rw [div_le_iff₀ hpos]
        exact hG ζ (hsph1 ζ hζ)
      have hb := hbb j ζ (by rw [hsph1 ζ hζ]; exact hr1)
      rw [norm_mul, norm_div]
      exact mul_le_mul hq hb (norm_nonneg _) hG0
    have hcj : ∀ j, ‖c j‖ ≤ 2 ^ l * (r * G) := by
      intro j
      have hI := circleIntegral.norm_integral_le_of_norm_le_const hr.le (hbound j)
      have hn : ‖-(2 * (Real.pi : ℂ) * I)⁻¹‖ = (2 * Real.pi)⁻¹ := by
        rw [norm_neg, norm_inv, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos Real.pi_pos, mul_one]
        norm_num
      rw [hc]
      simp only
      rw [norm_mul, hn]
      calc (2 * Real.pi)⁻¹ * ‖∮ ζ in C(0, r), g ζ / (∏ k, (ζ - z k)) * b j ζ‖
          ≤ (2 * Real.pi)⁻¹ * (2 * Real.pi * r * (G * 2 ^ l)) := by
            gcongr
        _ = 2 ^ l * (r * G) := by
            field_simp
    have hl : (l : ℝ) ≤ 2 ^ l := by exact_mod_cast (Nat.lt_two_pow_self (n := l)).le
    calc ∑ j, ‖c j‖ ≤ ∑ _j : Fin l, 2 ^ l * (r * G) := Finset.sum_le_sum (fun j _ => hcj j)
      _ = (l : ℝ) * (2 ^ l * (r * G)) := by simp
      _ ≤ 2 ^ l * (2 ^ l * (r * G)) := by
          gcongr
      _ = 4 ^ l * r * G := by
          rw [show (4 : ℝ) ^ l = 2 ^ l * 2 ^ l by rw [← mul_pow]; norm_num]
          ring

end GlobalTheory.ExteriorInterpolation
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsInterpolationExteriorSmallCoeffsStatement
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_interpolation_exterior_small_coeffs : ∀ (l : ℕ) (z : Fin l → ℂ) (g : ℂ → ℂ) (r G : ℝ), 0 < r → r ≤ 1 → (∀ i, r < ‖z i‖ ∧ ‖z i‖ ≤ 1) → DifferentiableOn ℂ g {w | r ≤ ‖w‖} → Tendsto g (Filter.cocompact ℂ) (𝓝 0) → (∀ w : ℂ, ‖w‖ = r → ‖g w‖ ≤ G * ‖∏ i, (w - z i)‖) → ∃ c : Fin l → ℂ, (∀ i, ∑ j, c j * z i ^ (j : ℕ) = g (z i)) ∧ ∑ j, ‖c j‖ ≤ 4 ^ l * r * G := by
  first | exact @GlobalTheory.ExteriorInterpolation.interpolation | exact GlobalTheory.ExteriorInterpolation.interpolation | (intros; apply GlobalTheory.ExteriorInterpolation.interpolation <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TuranSecondMainTheoremPowerSumsUnitCoefficients
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology

namespace GlobalTheory
namespace PowerSumSecond

lemma norm_sum_pow_mul_prod_le {ι κ : Type*} [Fintype ι] (z : ι → ℂ) (a : κ → ℂ) (B : ℝ)
    (T : Finset κ) (ha : ∀ t ∈ T, ‖a t‖ ≤ 1) :
    ∀ m : ℕ, (∀ k, m ≤ k → k ≤ m + T.card → ‖∑ i, z i ^ k‖ ≤ B) →
      ‖∑ i, z i ^ m * ∏ t ∈ T, (z i - a t)‖ ≤ 2 ^ T.card * B := by
  classical
  induction T using Finset.induction_on with
  | empty => intro m h; simpa using h m le_rfl (by simp)
  | insert t T ht ih =>
    intro m h
    rw [Finset.card_insert_of_notMem ht] at h ⊢
    have ha' : ∀ s ∈ T, ‖a s‖ ≤ 1 := fun s hs => ha s (Finset.mem_insert_of_mem hs)
    have h1 := ih ha' (m + 1) (fun k h1 h2 => h k (by omega) (by omega))
    have h2 := ih ha' m (fun k h1 h2 => h k (by omega) (by omega))
    have e : ∑ i, z i ^ m * ∏ s ∈ insert t T, (z i - a s)
        = ∑ i, z i ^ (m + 1) * ∏ s ∈ T, (z i - a s)
          - a t * ∑ i, z i ^ m * ∏ s ∈ T, (z i - a s) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.prod_insert ht]; ring
    rw [e]
    have h3 : ‖a t * ∑ i, z i ^ m * ∏ s ∈ T, (z i - a s)‖ ≤ 2 ^ T.card * B := by
      rw [norm_mul]
      calc _ ≤ 1 * ‖∑ i, z i ^ m * ∏ s ∈ T, (z i - a s)‖ :=
            mul_le_mul_of_nonneg_right (ha t (Finset.mem_insert_self _ _)) (norm_nonneg _)
        _ ≤ _ := by rw [one_mul]; exact h2
    calc _ ≤ _ := norm_sub_le _ _
      _ ≤ 2 ^ T.card * B + 2 ^ T.card * B := add_le_add h1 h3
      _ = _ := by ring

lemma tendsto_inv_prod {κ : Type*} (a : κ → ℂ) (T : Finset κ) (ha : ∀ t ∈ T, ‖a t‖ ≤ 1) (M : ℕ) :
    Tendsto (fun w : ℂ => (w ^ (M + 1) * ∏ t ∈ T, (w - a t))⁻¹) (Filter.cocompact ℂ) (𝓝 0) := by
  have h0 : Tendsto (fun w : ℂ => ‖w‖) (Filter.cocompact ℂ) atTop :=
    tendsto_norm_cocompact_atTop
  have h1 : Tendsto (fun w : ℂ => ‖w‖⁻¹) (Filter.cocompact ℂ) (𝓝 0) := h0.inv_tendsto_atTop
  refine squeeze_zero_norm' ?_ h1
  filter_upwards [h0.eventually_ge_atTop 2] with w hw
  rw [norm_inv, norm_mul, norm_pow, norm_prod]
  have hp : 1 ≤ ∏ t ∈ T, ‖w - a t‖ := by
    calc (1 : ℝ) = ∏ t ∈ T, (1 : ℝ) := by simp
      _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => zero_le_one) (fun t ht => by
        have := norm_sub_norm_le w (a t)
        have := ha t ht
        linarith)
  have hq : ‖w‖ ≤ ‖w‖ ^ (M + 1) := le_self_pow₀ (by linarith) (by omega)
  apply inv_anti₀ (by linarith)
  nlinarith

lemma inv_pow_le_exp (N M : ℕ) (hN : 0 < N) (r : ℝ) (hr : 1 - (N : ℝ) / (2 * (M + N)) ≤ r) :
    1 ≤ r ^ M * Real.exp 1 ^ N := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hM' : (0 : ℝ) ≤ M := by positivity
  set u : ℝ := N / (2 * M + N) with hu
  have hu0 : 0 ≤ u := by positivity
  have h1 : (1 - (N : ℝ) / (2 * (M + N))) * (u + 1) = 1 := by
    rw [hu]; field_simp; ring
  have h2 : 1 ≤ r * Real.exp u := by
    have hs : 0 ≤ 1 - (N : ℝ) / (2 * (M + N)) := by
      rw [sub_nonneg, div_le_one (by positivity)]; linarith
    calc (1 : ℝ) = _ := h1.symm
      _ ≤ _ := mul_le_mul hr (Real.add_one_le_exp u) (by linarith) (hs.trans hr)
  have hr0 : 0 ≤ r := by
    have hs : 0 ≤ 1 - (N : ℝ) / (2 * (M + N)) := by
      rw [sub_nonneg, div_le_one (by positivity)]; linarith
    exact hs.trans hr
  have h3 : Real.exp u ^ M ≤ Real.exp 1 ^ N := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.2
    rw [hu, mul_one, ← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg hM' hN'.le]
  calc (1 : ℝ) ≤ (r * Real.exp u) ^ M := one_le_pow₀ h2
    _ = r ^ M * Real.exp u ^ M := mul_pow _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left h3 (by positivity)

lemma core (N M : ℕ) (z : Fin N → ℂ) (i₁ : Fin N) (h1 : ‖z i₁‖ = 1) (hz : ∀ i, ‖z i‖ ≤ 1)
    (B : ℝ) (hB : ∀ k, M + 1 ≤ k → k ≤ M + N → ‖∑ i, z i ^ k‖ ≤ B) :
    ((N : ℝ) / (16 * Real.exp 1 ^ 2 * (M + N))) ^ N ≤ B := by
  classical
  have hN : 0 < N := i₁.pos
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hM' : (0 : ℝ) ≤ M := by positivity
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB (M + 1) le_rfl (by omega))
  set δ : ℝ := N / (2 * (M + N)) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 / 2 := by
    rw [hδ, div_le_iff₀ (by positivity)]; linarith
  obtain ⟨r, hr1, hr2, hr3⟩ := GlobalTheory.exists_prod_abs_sub_ge_on_segment N (fun i => ‖z i‖) (1 - δ) δ hδ0
  have hr0 : 0 < r := by linarith
  have hr1' : r ≤ 1 := by linarith
  set D : ℝ := (δ / (2 * Real.exp 1)) ^ N with hD
  have hD0 : 0 < D := by positivity
  have hne : ∀ i, r ≠ ‖z i‖ := by
    intro i hi
    have : ∏ i, |r - ‖z i‖| = 0 := Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
    linarith
  set S : Finset (Fin N) := Finset.univ.filter (fun i => r < ‖z i‖) with hS
  have hmemS : ∀ i, i ∈ S ↔ r < ‖z i‖ := by simp [hS]
  have hmemT : ∀ i ∈ Sᶜ, ‖z i‖ < r := by
    intro i hi
    rw [Finset.mem_compl, hmemS, not_lt] at hi
    exact lt_of_le_of_ne hi (hne i).symm
  have hi₁ : i₁ ∈ S := by
    rw [hmemS]; exact lt_of_le_of_ne (h1 ▸ hr1') (hne i₁)
  set e : Fin S.card ≃ S := S.equivFin.symm with he
  set f : ℂ → ℂ := fun w => ∏ t ∈ Sᶜ, (w - z t) with hf
  have hfne : ∀ w : ℂ, r ≤ ‖w‖ → w ^ (M + 1) * f w ≠ 0 := by
    intro w hw
    refine mul_ne_zero (pow_ne_zero _ ?_) (Finset.prod_ne_zero_iff.2 fun t ht h => ?_)
    · rintro rfl; simp at hw; linarith
    · have := hmemT t ht
      rw [sub_eq_zero] at h
      rw [h] at hw; linarith
  set G : ℝ := (r ^ (M + 1) * D)⁻¹ with hG
  obtain ⟨c, hc1, hc2⟩ := GlobalTheory.T.exists_interpolation_exterior_small_coeffs S.card (fun j => z (e j))
    (fun w => (w ^ (M + 1) * f w)⁻¹) r G hr0 hr1'
    (fun j => ⟨(hmemS _).1 (e j).2, hz _⟩)
    (by
      refine DifferentiableOn.inv ?_ (fun w hw => hfne w hw)
      refine Differentiable.differentiableOn ?_
      simp only [hf]
      fun_prop)
    (tendsto_inv_prod z Sᶜ (fun t _ => hz t) M)
    (by
      intro w hw
      have e1 : ∏ j, (w - z (e j)) = ∏ t ∈ S, (w - z t) := by
        rw [Equiv.prod_comp e (fun s : S => w - z s), Finset.prod_coe_sort S (fun t => w - z t)]
      have e2 : D ≤ ‖∏ t ∈ S, (w - z t)‖ * ‖f w‖ := by
        rw [← norm_mul, hf]
        simp only
        rw [Finset.prod_mul_prod_compl, norm_prod]
        refine hr3.trans (Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun i _ => ?_)
        rw [← hw]; exact abs_norm_sub_norm_le _ _
      have e3 : 0 < ‖f w‖ := norm_pos_iff.2 (right_ne_zero_of_mul (hfne w hw.ge))
      rw [e1, norm_inv, norm_mul, norm_pow, hw, hG, inv_mul_eq_div, inv_eq_one_div,
        div_le_div_iff₀ (by positivity) (by positivity)]
      have : 0 < r ^ (M + 1) := by positivity
      nlinarith)
  have key : (S.card : ℂ) = ∑ j, c j * ∑ i, z i ^ (M + 1 + (j : ℕ)) * f (z i) := by
    have e1 : ∑ j, c j * ∑ i, z i ^ (M + 1 + (j : ℕ)) * f (z i)
        = ∑ i, (z i ^ (M + 1) * f (z i)) * ∑ j, c j * z i ^ (j : ℕ) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [e1, ← Finset.sum_add_sum_compl S]
    have e2 : ∑ i ∈ Sᶜ, (z i ^ (M + 1) * f (z i)) * ∑ j, c j * z i ^ (j : ℕ) = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      have : f (z i) = 0 := Finset.prod_eq_zero hi (sub_self _)
      simp [this]
    have e3 : (S.card : ℂ) = ∑ i ∈ S, (1 : ℂ) := by simp
    rw [e2, add_zero]
    refine e3.trans ?_
    refine Finset.sum_congr rfl fun i hi => ?_
    have := hc1 (e.symm ⟨i, hi⟩)
    simp only [Equiv.apply_symm_apply] at this
    rw [this, mul_inv_cancel₀ (hfne _ ((hmemS i).1 hi).le)]
  have hcard : S.card + Sᶜ.card = N := by simp
  have hl : (1 : ℝ) ≤ S.card := by exact_mod_cast Finset.card_pos.2 ⟨i₁, hi₁⟩
  have hbound : (1 : ℝ) ≤ 4 ^ S.card * r * G * (2 ^ Sᶜ.card * B) := by
    calc (1 : ℝ) ≤ ‖(S.card : ℂ)‖ := by simpa using hl
      _ ≤ ∑ j, ‖c j‖ * (2 ^ Sᶜ.card * B) := by
        rw [key]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [norm_mul]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        have hj := j.2
        exact norm_sum_pow_mul_prod_le z z B Sᶜ (fun t _ => hz t) _
          (fun k h1 h2 => hB k (by omega) (by omega))
      _ ≤ _ := by
        rw [← Finset.sum_mul]
        exact mul_le_mul_of_nonneg_right hc2 (by positivity)
  have h4 : (4 : ℝ) ^ S.card * 2 ^ Sᶜ.card ≤ 4 ^ N := by
    calc (4 : ℝ) ^ S.card * 2 ^ Sᶜ.card ≤ 4 ^ S.card * 4 ^ Sᶜ.card := by gcongr; norm_num
      _ = 4 ^ N := by rw [← pow_add, hcard]
  have h5 : r ^ M * D ≤ 4 ^ N * B := by
    have : 4 ^ S.card * r * G * (2 ^ Sᶜ.card * B)
        = (4 ^ S.card * 2 ^ Sᶜ.card * B) / (r ^ M * D) := by
      rw [hG]; field_simp; ring
    rw [this, one_le_div (by positivity)] at hbound
    exact hbound.trans (mul_le_mul_of_nonneg_right h4 hB0)
  have h6 := inv_pow_le_exp N M hN r hr1
  have h7 : ((N : ℝ) / (16 * Real.exp 1 ^ 2 * (M + N))) ^ N = D / (4 ^ N * Real.exp 1 ^ N) := by
    rw [hD, ← mul_pow, ← div_pow, hδ]
    congr 1
    field_simp
    ring
  rw [h7, div_le_iff₀ (by positivity)]
  have h8 : 0 < Real.exp 1 ^ N := by positivity
  calc D ≤ (r ^ M * Real.exp 1 ^ N) * D := le_mul_of_one_le_left hD0.le h6
    _ = (r ^ M * D) * Real.exp 1 ^ N := by ring
    _ ≤ (4 ^ N * B) * Real.exp 1 ^ N := mul_le_mul_of_nonneg_right h5 h8.le
    _ = _ := by ring

end PowerSumSecond

open PowerSumSecond in
theorem powerSum_second_main :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (N M : ℕ) (z : Fin N → ℂ) (i₀ : Fin N), ∃ k : ℕ, M + 1 ≤ k ∧ k ≤ M + N ∧
      ((N : ℝ) / (C * (M + N))) ^ N * ‖z i₀‖ ^ k ≤ ‖∑ i, z i ^ k‖ := by
  refine ⟨16 * Real.exp 1 ^ 2, ?_, fun N M z i₀ => ?_⟩
  · have : 1 ≤ Real.exp 1 ^ 2 := one_le_pow₀ (Real.one_le_exp zero_le_one)
    linarith
  have hN : 0 < N := i₀.pos
  obtain ⟨i₁, -, hi₁⟩ := Finset.exists_max_image Finset.univ (fun i => ‖z i‖) ⟨i₀, Finset.mem_univ _⟩
  by_cases h0 : z i₁ = 0
  · refine ⟨M + 1, le_rfl, by omega, ?_⟩
    have : ‖z i₀‖ = 0 := le_antisymm (by simpa [h0] using hi₁ i₀ (Finset.mem_univ _)) (norm_nonneg _)
    rw [this, zero_pow (by omega), mul_zero]
    exact norm_nonneg _
  have hR : 0 < ‖z i₁‖ := norm_pos_iff.2 h0
  obtain ⟨k, hk, hk'⟩ := Finset.exists_max_image (Finset.Icc (M + 1) (M + N))
    (fun k => ‖∑ i, (z i / z i₁) ^ k‖) ⟨M + 1, Finset.mem_Icc.2 ⟨le_rfl, by omega⟩⟩
  rw [Finset.mem_Icc] at hk
  refine ⟨k, hk.1, hk.2, ?_⟩
  have hc := core N M (fun i => z i / z i₁) i₁ (by simp [h0])
    (fun i => by
      rw [norm_div, div_le_one hR]; exact hi₁ i (Finset.mem_univ _))
    _ (fun j h1 h2 => hk' j (Finset.mem_Icc.2 ⟨h1, h2⟩))
  simp only [div_pow] at hc
  rw [← Finset.sum_div, norm_div, norm_pow, le_div_iff₀ (by positivity), ← div_pow] at hc
  refine le_trans ?_ hc
  gcongr
  exact hi₁ i₀ (Finset.mem_univ _)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TuranSecondMainTheoremPowerSumsUnitCoefficientsStatement
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.turan_second_main_theorem_power_sums_unit_coefficients : ∃ C : ℝ, 1 ≤ C ∧ ∀ (N M : ℕ) (z : Fin N → ℂ) (i₀ : Fin N), ∃ k : ℕ, M + 1 ≤ k ∧ k ≤ M + N ∧ ((N : ℝ) / (C * (M + N))) ^ N * ‖z i₀‖ ^ k ≤ ‖∑ i, z i ^ k‖ := by
  first | exact @GlobalTheory.powerSum_second_main | exact GlobalTheory.powerSum_second_main | (intros; apply GlobalTheory.powerSum_second_main <;> assumption)
end
