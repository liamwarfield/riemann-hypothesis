module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasFDerivAtOfContinuousPartials
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasFDerivAtOfContinuousPartials
open Filter Topology

namespace GlobalTheory

private theorem norm_update_sub_update_sub_smul_le {k : ℕ} (F : (Fin k → ℝ) → ℂ)
    (d : Fin k → (Fin k → ℝ) → ℂ)
    (hF : ∀ i t, HasDerivAt (fun s : ℝ => F (Function.update t i s)) (d i t) (t i))
    (i : Fin k) (t y : Fin k → ℝ) {ε δ : ℝ} (hδ : 0 < δ)
    (hgood : ∀ z, dist z t < δ → ‖d i z - d i t‖ ≤ ε) (hy : dist y t < δ) {a b : ℝ}
    (ha : dist a (t i) < δ) (hb : dist b (t i) < δ) :
    ‖F (Function.update y i b) - F (Function.update y i a) - (b - a) • d i t‖ ≤ ε * |b - a| := by
  set g : ℝ → ℂ := fun s => F (Function.update y i s) - s • d i t with hg
  have hmem : ∀ s ∈ Metric.ball (t i) δ, dist (Function.update y i s) t < δ := by
    intro s hs
    rw [dist_pi_lt_iff hδ]
    intro m
    by_cases hm : m = i
    · subst hm
      simpa using hs
    · rw [Function.update_of_ne hm]
      exact lt_of_le_of_lt (dist_le_pi_dist y t m) hy
  have hderiv : ∀ s ∈ Metric.ball (t i) δ,
      HasDerivWithinAt g (d i (Function.update y i s) - d i t) (Metric.ball (t i) δ) s := by
    intro s _
    have h1 := hF i (Function.update y i s)
    simp only [Function.update_idem, Function.update_self] at h1
    have h2 : HasDerivAt (fun u : ℝ => u • d i t) ((1 : ℝ) • d i t) s :=
      (hasDerivAt_id s).smul_const (d i t)
    rw [one_smul] at h2
    exact (h1.sub h2).hasDerivWithinAt
  have hbound : ∀ s ∈ Metric.ball (t i) δ, ‖d i (Function.update y i s) - d i t‖ ≤ ε :=
    fun s hs => hgood _ (hmem s hs)
  have key := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
    (convex_ball (t i) δ) (Metric.mem_ball.2 ha) (Metric.mem_ball.2 hb)
  have hdiff : g b - g a = F (Function.update y i b) - F (Function.update y i a) - (b - a) • d i t := by
    simp only [hg, sub_smul]
    abel
  rw [hdiff, Real.norm_eq_abs] at key
  exact key

theorem _root_.GlobalTheory.hasFDerivAt_of_continuous_partials :
    ∀ (k : ℕ) (F : (Fin k → ℝ) → ℂ) (d : Fin k → (Fin k → ℝ) → ℂ),
      (∀ i t, HasDerivAt (fun s : ℝ => F (Function.update t i s)) (d i t) (t i)) →
      (∀ i, Continuous (d i)) →
      ∀ t, HasFDerivAt F (∑ i, (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (d i t)) t := by
  intro k F d hF hd t
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  set ε : ℝ := c / (k + 1) with hε
  have hεpos : 0 < ε := div_pos hc (by positivity)
  have hev : ∀ᶠ z in 𝓝 t, ∀ i, dist (d i z) (d i t) < ε :=
    eventually_all.2 fun i => (hd i).continuousAt.eventually (Metric.ball_mem_nhds (d i t) hεpos)
  obtain ⟨δ, hδ, hδgood⟩ := Metric.eventually_nhds_iff.1 hev
  have hgood : ∀ i z, dist z t < δ → ‖d i z - d i t‖ ≤ ε := fun i z hz =>
    (dist_eq_norm (d i z) (d i t) ▸ (hδgood hz i)).le
  rw [Metric.eventually_nhds_iff]
  refine ⟨δ, hδ, fun h hh => ?_⟩
  rw [dist_zero_right] at hh
  set p : ℕ → (Fin k → ℝ) := fun j m => if (m : ℕ) < j then t m + h m else t m with hp
  set a : ℕ → ℂ := fun j => if hj : j < k then h ⟨j, hj⟩ • d ⟨j, hj⟩ t else 0 with ha
  have hp0 : p 0 = t := by
    funext m
    simp [hp]
  have hpk : p k = t + h := by
    funext m
    simp [hp, m.isLt]
  have hsumL : (∑ i, (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (d i t)) h =
      ∑ j ∈ Finset.range k, a j := by
    rw [Finset.sum_range]
    simp [ha, ContinuousLinearMap.sum_apply]
  have htel : F (t + h) - F t = ∑ j ∈ Finset.range k, (F (p (j + 1)) - F (p j)) := by
    rw [Finset.sum_range_sub (fun j => F (p j)) k, hpk, hp0]
  have hpdist : ∀ j, dist (p j) t < δ := by
    intro j
    rw [dist_pi_lt_iff hδ]
    intro m
    simp only [hp]
    split_ifs
    · rw [Real.dist_eq, add_sub_cancel_left]
      exact lt_of_le_of_lt (by simpa using norm_le_pi_norm h m) hh
    · simpa using hδ
  have hstep : ∀ j ∈ Finset.range k, ‖F (p (j + 1)) - F (p j) - a j‖ ≤ ε * ‖h‖ := by
    intro j hj
    have hjk : j < k := Finset.mem_range.1 hj
    set i : Fin k := ⟨j, hjk⟩ with hi
    have haj : a j = ((t i + h i) - t i) • d i t := by
      simp [ha, hjk, hi]
    have hnext : p (j + 1) = Function.update (p j) i (t i + h i) := by
      funext m
      by_cases hm : m = i
      · subst hm
        simp [hp, hi]
      · have hm' : (m : ℕ) ≠ j := fun e => hm (Fin.ext e)
        rw [Function.update_of_ne hm]
        simp only [hp]
        have : (m : ℕ) < j + 1 ↔ (m : ℕ) < j := by omega
        simp only [this]
    have hcur : p j = Function.update (p j) i (t i) := by
      symm
      rw [Function.update_eq_self_iff]
      simp [hp, hi]
    have hx : dist (t i + h i) (t i) < δ := by
      rw [Real.dist_eq, add_sub_cancel_left]
      exact lt_of_le_of_lt (by simpa using norm_le_pi_norm h i) hh
    have hmain := norm_update_sub_update_sub_smul_le F d hF i t (p j) hδ (hgood i) (hpdist j)
      (a := t i) (b := t i + h i) (by rw [dist_self]; exact hδ) hx
    rw [haj, hnext]
    conv_lhs => rw [hcur]
    rw [Function.update_idem]
    refine hmain.trans ?_
    gcongr
    rw [add_sub_cancel_left]
    simpa using norm_le_pi_norm h i
  calc ‖F (t + h) - F t - (∑ i, (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (d i t)) h‖
      = ‖∑ j ∈ Finset.range k, (F (p (j + 1)) - F (p j) - a j)‖ := by
        rw [hsumL, htel, ← Finset.sum_sub_distrib]
    _ ≤ ∑ j ∈ Finset.range k, ‖F (p (j + 1)) - F (p j) - a j‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range k, ε * ‖h‖ := Finset.sum_le_sum hstep
    _ = k * (ε * ‖h‖) := by simp
    _ ≤ c * ‖h‖ := by
        rw [← mul_assoc]
        gcongr
        rw [hε, mul_div_assoc']
        rw [div_le_iff₀ (by positivity)]
        nlinarith

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasFDerivAtOfContinuousPartialsStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasFDerivAt_of_continuous_coordinate_derivs : ∀ (k : ℕ) (F : (Fin k → ℝ) → ℂ) (d : Fin k → (Fin k → ℝ) → ℂ), (∀ i t, HasDerivAt (fun s : ℝ => F (Function.update t i s)) (d i t) (t i)) → (∀ i, Continuous (d i)) → ∀ t, HasFDerivAt F (∑ i, (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (d i t)) t := by
  first | exact @GlobalTheory.hasFDerivAt_of_continuous_partials | exact GlobalTheory.hasFDerivAt_of_continuous_partials | (intros; apply GlobalTheory.hasFDerivAt_of_continuous_partials <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrableExpNegMulOfSublevelGrowth
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrableExpNegMulOfSublevelGrowth
open MeasureTheory

namespace GlobalTheory

theorem integrable_exp_neg_mul_of_sublevel_growth :
    ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (d : X → ℝ) (a b C : ℝ), Measurable d →
      (∀ x, 0 ≤ d x) →
      (∀ r : ℝ, 0 ≤ r → μ {x | d x ≤ r} ≤ ENNReal.ofReal (C * Real.exp (a * r))) → a < b →
      Integrable (fun x => Real.exp (-(b * d x))) μ := by
  intro X _ μ d a b C hd hd0 hgrowth hab
  set C' : ℝ := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hmeas : Measurable fun x => Real.exp (-(b * d x)) :=
    Real.measurable_exp.comp ((hd.const_mul b).neg)
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  have hpos : 0 ≤ᵐ[μ] fun x => Real.exp (-(b * d x)) :=
    Filter.Eventually.of_forall fun x => (Real.exp_pos _).le
  rw [hasFiniteIntegral_iff_ofReal hpos]

  let s : ℕ → Set X := fun n => {x | d x ≤ (n : ℝ) + 1}
  have hs : ∀ n, MeasurableSet (s n) := fun n => measurableSet_le hd measurable_const
  let g : ℕ → X → ENNReal := fun n =>
    (s n).indicator (fun _ => ENNReal.ofReal (Real.exp (|b| - b * n)))
  have hpt : ∀ x, ENNReal.ofReal (Real.exp (-(b * d x))) ≤ ∑' n, g n x := by
    intro x
    set n := ⌊d x⌋₊ with hn
    have h1 : (n : ℝ) ≤ d x := Nat.floor_le (hd0 x)
    have h2 : d x < (n : ℝ) + 1 := Nat.lt_floor_add_one (d x)
    have hxs : x ∈ s n := by
      show d x ≤ (n : ℝ) + 1
      exact h2.le
    have hexp : Real.exp (-(b * d x)) ≤ Real.exp (|b| - b * n) := by
      apply Real.exp_le_exp.mpr
      have hdist : |d x - n| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith
      have : |b * (d x - n)| ≤ |b| := by
        rw [abs_mul]
        calc |b| * |d x - n| ≤ |b| * 1 := mul_le_mul_of_nonneg_left hdist (abs_nonneg b)
          _ = |b| := mul_one _
      have hlow := neg_abs_le (b * (d x - n))
      have hy : -(b * d x) = |b| - b * n - (|b| + b * (d x - n)) := by ring
      rw [hy]
      linarith
    calc ENNReal.ofReal (Real.exp (-(b * d x))) ≤ ENNReal.ofReal (Real.exp (|b| - b * n)) :=
          ENNReal.ofReal_le_ofReal hexp
      _ = g n x := by simp only [g, Set.indicator_of_mem hxs]
      _ ≤ ∑' m, g m x := ENNReal.le_tsum (f := fun m => g m x) n

  let u : ℕ → ℝ := fun n => C' * Real.exp (|b| + a) * Real.exp (a - b) ^ n
  have hu0 : ∀ n, 0 ≤ u n := fun n => by positivity
  have hr0 : 0 ≤ Real.exp (a - b) := (Real.exp_pos _).le
  have hr1 : Real.exp (a - b) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hsum : Summable u := (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hterm : ∀ n, ∫⁻ x, g n x ∂μ ≤ ENNReal.ofReal (u n) := by
    intro n
    simp only [g]
    rw [lintegral_indicator_const (hs n)]
    have hμ : μ (s n) ≤ ENNReal.ofReal (C' * Real.exp (a * ((n : ℝ) + 1))) := by
      calc μ (s n) ≤ ENNReal.ofReal (C * Real.exp (a * ((n : ℝ) + 1))) :=
            hgrowth _ (by positivity)
        _ ≤ ENNReal.ofReal (C' * Real.exp (a * ((n : ℝ) + 1))) :=
            ENNReal.ofReal_le_ofReal
              (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
    calc ENNReal.ofReal (Real.exp (|b| - b * n)) * μ (s n)
        ≤ ENNReal.ofReal (Real.exp (|b| - b * n)) *
            ENNReal.ofReal (C' * Real.exp (a * ((n : ℝ) + 1))) := by gcongr
      _ = ENNReal.ofReal (Real.exp (|b| - b * n) * (C' * Real.exp (a * ((n : ℝ) + 1)))) :=
          (ENNReal.ofReal_mul (Real.exp_pos _).le).symm
      _ = ENNReal.ofReal (u n) := by
          congr 1
          simp only [u]
          rw [← Real.exp_nat_mul]
          have hE : Real.exp (|b| - b * n) * Real.exp (a * ((n : ℝ) + 1)) =
              Real.exp (|b| + a) * Real.exp (n * (a - b)) := by
            rw [← Real.exp_add, ← Real.exp_add]; ring_nf
          linear_combination C' * hE
  calc ∫⁻ x, ENNReal.ofReal (Real.exp (-(b * d x))) ∂μ ≤ ∫⁻ x, ∑' n, g n x ∂μ :=
        MeasureTheory.lintegral_mono hpt
    _ = ∑' n, ∫⁻ x, g n x ∂μ :=
        MeasureTheory.lintegral_tsum fun n => (measurable_const.indicator (hs n)).aemeasurable
    _ ≤ ∑' n, ENNReal.ofReal (u n) := ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (∑' n, u n) := (ENNReal.ofReal_tsum_of_nonneg hu0 hsum).symm
    _ < ⊤ := ENNReal.ofReal_lt_top

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrableExpNegMulOfSublevelGrowthStatement
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_exp_neg_mul_of_sublevel_le_exp : ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (d : X → ℝ) (a b C : ℝ), Measurable d → (∀ x, 0 ≤ d x) → (∀ r : ℝ, 0 ≤ r → μ {x | d x ≤ r} ≤ ENNReal.ofReal (C * Real.exp (a * r))) → a < b → Integrable (fun x => Real.exp (-(b * d x))) μ := by
  first | exact @GlobalTheory.integrable_exp_neg_mul_of_sublevel_growth | exact GlobalTheory.integrable_exp_neg_mul_of_sublevel_growth | (intros; apply GlobalTheory.integrable_exp_neg_mul_of_sublevel_growth <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PackingGeometricMeanSeparated
open Matrix Finset Real

namespace GlobalTheory

open MeasureTheory Metric in
theorem card_le_of_separated_in_ball {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (T : Finset E) (R la : ℝ) (hR : 0 ≤ R) (hla : 0 < la)
    (hT : ∀ x ∈ T, ‖x‖ ≤ R) (hsep : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → la ≤ ‖x - y‖) :
    (T.card : ℝ) ≤ (1 + 2 * R / la) ^ Module.finrank ℝ E := by
  classical
  rcases subsingleton_or_nontrivial E with hE | hE
  · have h1 : T.card ≤ 1 := Finset.card_le_one_of_subsingleton T
    rw [Module.finrank_zero_of_subsingleton, pow_zero]
    exact_mod_cast h1
  let _ : MeasurableSpace E := borel E
  have _ : BorelSpace E := ⟨rfl⟩
  obtain ⟨μ, hμ⟩ : ∃ μ : Measure E, μ.IsAddHaarMeasure := ⟨Measure.addHaar, inferInstance⟩
  have hr : 0 < la / 2 := by positivity
  have hdisj : (T : Set E).PairwiseDisjoint (fun x => ball x (la / 2)) := by
    intro x hx y hy hxy
    refine Set.disjoint_left.mpr ?_
    intro z hzx hzy
    rw [mem_ball, dist_eq_norm] at hzx hzy
    have h1 := hsep x hx y hy hxy
    have h2 : ‖x - y‖ < la := by
      calc ‖x - y‖ = ‖(z - y) - (z - x)‖ := by congr 1; abel
        _ ≤ ‖z - y‖ + ‖z - x‖ := norm_sub_le _ _
        _ < la / 2 + la / 2 := add_lt_add hzy hzx
        _ = la := by ring
    linarith
  have hsub : (⋃ x ∈ T, ball x (la / 2)) ⊆ ball (0 : E) (R + la / 2) := by
    intro z hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨x, hx, hzx⟩ := hz
    rw [mem_ball, dist_eq_norm] at hzx ⊢
    calc ‖z - 0‖ = ‖(z - x) + x‖ := by simp
      _ ≤ ‖z - x‖ + ‖x‖ := norm_add_le _ _
      _ < la / 2 + R := by linarith [hT x hx]
      _ = R + la / 2 := by ring
  have hle := measure_mono (μ := μ) hsub
  rw [measure_biUnion_finset hdisj (fun x _ => measurableSet_ball)] at hle
  simp only [Measure.addHaar_ball_center, Finset.sum_const, nsmul_eq_mul] at hle
  rw [Measure.addHaar_ball μ 0 hr.le, Measure.addHaar_ball μ 0 (by positivity : (0 : ℝ) ≤ R + la / 2),
    ← mul_assoc] at hle
  have hm0 : μ (ball (0 : E) 1) ≠ 0 := (measure_ball_pos μ 0 one_pos).ne'
  have hmtop : μ (ball (0 : E) 1) ≠ ⊤ := measure_ball_lt_top.ne
  rw [ENNReal.mul_le_mul_iff_left hm0 hmtop, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_le_ofReal_iff (by positivity)] at hle
  have hpos : 0 < (la / 2) ^ Module.finrank ℝ E := by positivity
  have hq : (1 + 2 * R / la) ^ Module.finrank ℝ E
      = (R + la / 2) ^ Module.finrank ℝ E / (la / 2) ^ Module.finrank ℝ E := by
    rw [← div_pow]
    congr 1
    field_simp
    ring
  rw [hq, le_div_iff₀ hpos]
  exact hle

theorem packing_geometric_mean_separated : ∀ (ι : Type) [Fintype ι] [Nonempty ι] (W : ι → Type) [∀ v, NormedAddCommGroup (W v)] [∀ v, NormedSpace ℝ (W v)] [∀ v, FiniteDimensional ℝ (W v)] (N : ℕ), 1 ≤ N → (∀ v, Module.finrank ℝ (W v) = N) → ∀ (la : ℝ) (S : Set (∀ v, W v)) (X : ι → ℝ), 0 < la → (∀ v, 0 < X v) → (∀ s ∈ S, ∀ s' ∈ S, s ≠ s' → la ≤ (∏ v, ‖s v - s' v‖) ^ ((1 : ℝ) / Fintype.card ι)) → {s ∈ S | ∀ v, ‖s v‖ ≤ X v}.Finite ∧ (({s ∈ S | ∀ v, ‖s v‖ ≤ X v}.ncard : ℕ) : ℝ) ≤ (1 + 2 * (∏ v, X v) ^ ((1 : ℝ) / Fintype.card ι) / la) ^ (N * Fintype.card ι) := by
  intro ι _ _ W _ _ _ N hN hdim la S X hla hX hsep
  classical
  set k := Fintype.card ι with hk
  have hkpos : 0 < k := Fintype.card_pos
  set P := ∏ v, X v with hP
  have hPpos : 0 < P := Finset.prod_pos (fun v _ => hX v)
  set G := P ^ ((1 : ℝ) / k) with hG
  have hGpos : 0 < G := Real.rpow_pos_of_pos hPpos _
  have hGk : G ^ k = P := by
    rw [hG, one_div]
    exact Real.rpow_inv_natCast_pow hPpos.le hkpos.ne'
  set c : ι → ℝ := fun v => G / X v with hc
  have hcpos : ∀ v, 0 < c v := fun v => div_pos hGpos (hX v)
  have hcprod : ∏ v, c v = 1 := by
    rw [hc, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, ← hk, hGk]
    exact div_self hPpos.ne'
  let φ : (∀ v, W v) → (∀ v, W v) := fun s v => c v • s v
  have hφinj : Function.Injective φ := by
    intro s s' h
    funext v
    exact smul_right_injective _ (hcpos v).ne' (congrFun h v)
  set A := {s ∈ S | ∀ v, ‖s v‖ ≤ X v} with hA
  have hdimPi : Module.finrank ℝ (∀ v, W v) = N * k := by
    rw [Module.finrank_pi_fintype]
    simp [hdim, hk, mul_comm]
  have key : ∀ F : Finset (∀ v, W v), (↑F : Set (∀ v, W v)) ⊆ A →
      (F.card : ℝ) ≤ (1 + 2 * G / la) ^ (N * k) := by
    intro F hF
    have hbound := card_le_of_separated_in_ball (F.image φ) G la hGpos.le hla ?_ ?_
    · rw [Finset.card_image_of_injective _ hφinj, hdimPi] at hbound
      exact hbound
    · intro y hy
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hy
      have hsA := hF hs
      refine (pi_norm_le_iff_of_nonneg hGpos.le).mpr (fun v => ?_)
      simp only [φ, norm_smul, Real.norm_eq_abs, abs_of_pos (hcpos v)]
      calc c v * ‖s v‖ ≤ c v * X v := mul_le_mul_of_nonneg_left (hsA.2 v) (hcpos v).le
        _ = G := by
          simp only [hc]
          field_simp [(hX v).ne']
    · intro y hy y' hy' hne
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨s', hs', rfl⟩ := Finset.mem_image.mp hy'
      have hss : s ≠ s' := fun h => hne (by rw [h])
      have h1 := hsep s (hF hs).1 s' (hF hs').1 hss
      have hprod : ∏ v, ‖(φ s - φ s') v‖ = ∏ v, ‖s v - s' v‖ := by
        simp only [φ, Pi.sub_apply, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (hcpos _),
          Finset.prod_mul_distrib, hcprod, one_mul]
      have hgm : (∏ v, ‖(φ s - φ s') v‖) ^ ((1 : ℝ) / k) ≤ ‖φ s - φ s'‖ := by
        have hle : ∏ v, ‖(φ s - φ s') v‖ ≤ ‖φ s - φ s'‖ ^ k := by
          rw [hk, ← Finset.card_univ, ← Finset.prod_const]
          exact Finset.prod_le_prod₀ (fun v _ => norm_nonneg _) (fun v _ => norm_le_pi_norm _ v)
        calc (∏ v, ‖(φ s - φ s') v‖) ^ ((1 : ℝ) / k) ≤ (‖φ s - φ s'‖ ^ k) ^ ((1 : ℝ) / k) :=
              Real.rpow_le_rpow (Finset.prod_nonneg (fun v _ => norm_nonneg _)) hle (by positivity)
          _ = ‖φ s - φ s'‖ := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _),
                mul_one_div_cancel (by exact_mod_cast hkpos.ne'), Real.rpow_one]
      rw [hprod] at hgm
      exact h1.trans hgm
  have hfin : A.Finite := by
    by_contra hinf
    obtain ⟨F, hF, hcard⟩ :=
      Set.Infinite.exists_subset_card_eq hinf (⌈(1 + 2 * G / la) ^ (N * k)⌉₊ + 1)
    have h3 := key F hF
    rw [hcard] at h3
    push_cast at h3
    linarith [Nat.le_ceil ((1 + 2 * G / la) ^ (N * k))]
  refine ⟨hfin, ?_⟩
  rw [Set.ncard_eq_toFinset_card A hfin]
  exact key _ (by simp)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DeepRegionExponents
open Matrix Finset Real

namespace GlobalTheory

theorem deep_exponent_core (X τ be n g : ℝ) (q : ℕ) (hX : 16 ≤ X) (hq : 1 ≤ q) (hτ : 0 < τ)
    (hτX : τ ≤ X⁻¹ ^ (11 * q)) (hbe0 : 0 ≤ be) (hbe : be ≤ X ^ 6) (hn0 : 0 ≤ n) (hn : n ≤ X)
    (hg0 : 0 ≤ g) (hg : g ≤ X) :
    (X ^ (96 * q) * (2 * τ) ^ 16) * ((6 * be) * Real.exp 1 * (289 * n / τ ^ 4)) * g ^ 2 * X
      ≤ Real.exp (-1) := by
  have hX0 : 0 < X := by linarith
  obtain ⟨Y, hYdef⟩ : ∃ Y : ℝ, Y = X ^ q := ⟨_, rfl⟩
  have hXY : X ≤ Y := by
    rw [hYdef]; simpa using pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ X) hq
  have hY16 : 16 ≤ Y := le_trans hX hXY
  have hY0 : 0 < Y := by linarith
  have hτY : τ * Y ^ 11 ≤ 1 := by
    have h1 : X⁻¹ ^ (11 * q) * Y ^ 11 = 1 := by
      rw [hYdef, ← pow_mul, inv_pow, mul_comm q 11]
      exact inv_mul_cancel₀ (by positivity)
    calc τ * Y ^ 11 ≤ X⁻¹ ^ (11 * q) * Y ^ 11 := by gcongr
      _ = 1 := h1
  have hA : Y ^ 96 * τ ^ 12 * Y ^ 36 ≤ 1 := by
    have e : Y ^ 96 * τ ^ 12 * Y ^ 36 = (τ * Y ^ 11) ^ 12 := by ring
    rw [e]
    exact pow_le_one₀ (by positivity) hτY
  have hB : be * n * g ^ 2 * X ≤ Y ^ 10 :=
    calc be * n * g ^ 2 * X ≤ X ^ 6 * X * X ^ 2 * X := by gcongr
      _ = X ^ 10 := by ring
      _ ≤ Y ^ 10 := by gcongr
  have hC0 : 0 ≤ (Y ^ 96 * τ ^ 12) * (be * n * g ^ 2 * X) := by positivity
  have hC : (Y ^ 96 * τ ^ 12) * (be * n * g ^ 2 * X) * 16 ^ 26 ≤ 1 :=
    calc (Y ^ 96 * τ ^ 12) * (be * n * g ^ 2 * X) * 16 ^ 26
        ≤ (Y ^ 96 * τ ^ 12) * Y ^ 10 * Y ^ 26 := by gcongr
      _ = Y ^ 96 * τ ^ 12 * Y ^ 36 := by ring
      _ ≤ 1 := hA
  have hE : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hE' : 1 / 3 ≤ Real.exp (-1) := by
    have h := one_div_le_one_div_of_le (Real.exp_pos 1) hE.le
    rwa [Real.exp_neg, ← one_div]
  have hXq : X ^ (96 * q) = Y ^ 96 := by rw [hYdef, ← pow_mul, mul_comm]
  have hτ0 : τ ≠ 0 := hτ.ne'
  have e : Y ^ 96 * (2 * τ) ^ 16 * (6 * be * Real.exp 1 * (289 * n / τ ^ 4)) * g ^ 2 * X
      = (2 ^ 16 * 6 * 289) * Real.exp 1 * ((Y ^ 96 * τ ^ 12) * (be * n * g ^ 2 * X)) := by
    field_simp
  rw [hXq, e]
  calc (2 ^ 16 * 6 * 289) * Real.exp 1 * ((Y ^ 96 * τ ^ 12) * (be * n * g ^ 2 * X))
      ≤ (2 ^ 16 * 6 * 289) * 3 * ((Y ^ 96 * τ ^ 12) * (be * n * g ^ 2 * X)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE.le (by norm_num)) hC0
    _ ≤ 1 / 3 := by norm_num at hC ⊢; linarith
    _ ≤ Real.exp (-1) := hE'

theorem deep_region_exponents : ∀ (n f q : ℕ) (rd g b : ℝ) (τ : ℝ), 8 ≤ n → 1 ≤ f → 1 ≤ q → q ^ 2 ≤ n → 1 ≤ rd → 2 ≤ b → 1 ≤ g → 0 < τ → τ ≤ ((n : ℝ) * f * rd * g * b)⁻¹ ^ (11 * q) → let N : ℕ := n ^ 2 * f; let rh : ℝ := (n : ℝ) ^ 2 * Real.sqrt f * g * rd * (2 * τ) ^ ((1 : ℝ) / q) / 4; let be : ℝ := Real.sqrt n * b ^ 2 + 1.5 * (n : ℝ) ^ ((3 : ℝ) / 2) + 3 * ((8 * q * N + N : ℕ) : ℝ); rh ≤ Real.log 2 ∧ (2 * rh * Real.sqrt f * be) ^ (2 * (8 * q * N)) * ((6 * be) ^ N * Real.exp f * (17 * Real.sqrt n / τ ^ 2) ^ (2 * N)) * g ^ (2 * N) * ((n : ℝ) * f * rd * g * b) ^ N ≤ Real.exp (-(N : ℝ)) := by
  intro n f q rd g b τ hn hf hq hqn hrd hb hg hτ hτP N rh be
  have hN : N = n ^ 2 * f := rfl
  have hrh : rh = (n : ℝ) ^ 2 * Real.sqrt f * g * rd * (2 * τ) ^ ((1 : ℝ) / q) / 4 := rfl
  have hbe : be = Real.sqrt n * b ^ 2 + 1.5 * (n : ℝ) ^ ((3 : ℝ) / 2)
      + 3 * ((8 * q * N + N : ℕ) : ℝ) := rfl
  clear_value N rh be
  generalize hPdef : ((n : ℝ) * f * rd * g * b) = P at hτP ⊢
  have hn8 : (8 : ℝ) ≤ n := by exact_mod_cast hn
  have hf1 : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hqn' : (q : ℝ) ≤ n := by
    have h : q ≤ n := le_trans (by nlinarith) hqn
    exact_mod_cast h
  have hq0 : q ≠ 0 := by omega
  have hNr : (N : ℝ) = (n : ℝ) ^ 2 * f := by rw [hN]; push_cast; ring
  have hn0 : (0 : ℝ) ≤ n := by linarith
  have hf0 : (0 : ℝ) ≤ f := by linarith
  have hrd0 : 0 ≤ rd := by linarith
  have hg0 : 0 ≤ g := by linarith
  have hb0 : 0 ≤ b := by linarith
  have hnf : (n : ℝ) ≤ n * f := le_mul_of_one_le_right hn0 hf1
  have hnfr : (n : ℝ) * f ≤ n * f * rd := le_mul_of_one_le_right (by positivity) hrd
  have hnfrg : (n : ℝ) * f * rd ≤ n * f * rd * g := le_mul_of_one_le_right (by positivity) hg
  have hmP : (n : ℝ) * f * rd * g ≤ P := by
    rw [← hPdef]; exact le_mul_of_one_le_right (by positivity) (by linarith)
  have hP16 : (16 : ℝ) ≤ P := by
    rw [← hPdef]
    linarith [mul_le_mul (by linarith : (8 : ℝ) ≤ n * f * rd * g) hb (by norm_num) (by positivity)]
  have hP0 : 0 ≤ P := by linarith
  have hnP : (n : ℝ) ≤ P := by linarith
  have hnfP : (n : ℝ) * f ≤ P := by linarith
  have hgP : g ≤ P := by
    have h : g ≤ n * f * rd * g := le_mul_of_one_le_left hg0 (by linarith)
    linarith
  have hbP : b ≤ P := by
    rw [← hPdef]; exact le_mul_of_one_le_left hb0 (by linarith)
  have hnbP : (n : ℝ) * b ≤ P := by
    rw [← hPdef]; exact mul_le_mul_of_nonneg_right (by linarith) hb0
  have hnmP : (n : ℝ) * (n * f * rd * g) ≤ P ^ 2 := by
    rw [sq]; exact mul_le_mul hnP hmP (by positivity) hP0
  have hs2 : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn0
  have hs1 : 1 ≤ Real.sqrt n := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
  have hsn : Real.sqrt n ≤ n :=
    calc Real.sqrt n = Real.sqrt n * 1 := by ring
      _ ≤ Real.sqrt n * Real.sqrt n := mul_le_mul_of_nonneg_left hs1 (Real.sqrt_nonneg n)
      _ = n := Real.mul_self_sqrt hn0
  have hfs : Real.sqrt f * Real.sqrt f = f := Real.mul_self_sqrt hf0
  have hf1s : 1 ≤ Real.sqrt f := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hf1
  have hsf : Real.sqrt f ≤ f :=
    calc Real.sqrt f = Real.sqrt f * 1 := by ring
      _ ≤ Real.sqrt f * Real.sqrt f := mul_le_mul_of_nonneg_left hf1s (Real.sqrt_nonneg f)
      _ = f := hfs
  have h32 : (n : ℝ) ^ ((3 : ℝ) / 2) ≤ (n : ℝ) ^ 2 := by
    rw [← Real.rpow_two]; exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hcast : ((8 * q * N + N : ℕ) : ℝ) ≤ 9 * (n : ℝ) ^ 3 * f := by
    push_cast
    rw [hNr]
    linarith [mul_nonneg (sub_nonneg.2 hqn') (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 2 * f),
      mul_nonneg (by linarith : (0 : ℝ) ≤ n - 1) (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 2 * f)]
  have t1 : Real.sqrt n * b ^ 2 ≤ P ^ 2 :=
    calc Real.sqrt n * b ^ 2 ≤ n * b ^ 2 := by gcongr
      _ = (n * b) * b := by ring
      _ ≤ P * P := mul_le_mul hnbP hbP hb0 hP0
      _ = P ^ 2 := by ring
  have t2 : (n : ℝ) ^ 2 ≤ P ^ 2 := pow_le_pow_left₀ hn0 hnP 2
  have t3 : (n : ℝ) ^ 3 * f ≤ P ^ 3 :=
    calc (n : ℝ) ^ 3 * f = n * n * (n * f) := by ring
      _ ≤ P * P * P := by gcongr
      _ = P ^ 3 := by ring
  have hP23 : P ^ 2 ≤ P ^ 3 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hbe0 : 0 ≤ be := by rw [hbe]; positivity
  have hbeP : be ≤ 30 * P ^ 3 := by rw [hbe]; linarith
  have hP3 : (30 : ℝ) ≤ P ^ 3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 16) hP16 3
    norm_num at h; linarith
  have hbe6 : be ≤ P ^ 6 := by linarith [mul_le_mul_of_nonneg_right hP3 (by positivity : (0 : ℝ) ≤ P ^ 3)]
  have hK : (n : ℝ) ^ 2 * f * g * rd * be / 2 ≤ P ^ 6 := by
    have e : (n : ℝ) ^ 2 * f * g * rd * be / 2 = (n * (n * f * rd * g)) * be / 2 := by ring
    rw [e]
    have h : (n * (n * f * rd * g)) * be ≤ P ^ 2 * (30 * P ^ 3) :=
      mul_le_mul hnmP hbeP hbe0 (by positivity)
    linarith [mul_nonneg (pow_nonneg hP0 5) (by linarith : (0 : ℝ) ≤ P - 15)]
  have hsq : ((2 * τ) ^ ((1 : ℝ) / q)) ^ q = 2 * τ := by
    rw [one_div]; exact Real.rpow_inv_natCast_pow (by positivity) hq0
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = (2 * τ) ^ ((1 : ℝ) / q) := ⟨_, rfl⟩
  rw [← hsdef] at hsq hrh
  have hs0 : 0 ≤ s := by rw [hsdef]; positivity
  have hτP' : τ * P ^ (11 * q) ≤ 1 := by
    have h1 : P⁻¹ ^ (11 * q) * P ^ (11 * q) = 1 := by
      rw [inv_pow]; exact inv_mul_cancel₀ (by positivity)
    calc τ * P ^ (11 * q) ≤ P⁻¹ ^ (11 * q) * P ^ (11 * q) := by gcongr
      _ = 1 := h1
  have hu : (s * P ^ 11) ^ q ≤ 2 ^ q :=
    calc (s * P ^ 11) ^ q = s ^ q * P ^ (11 * q) := by rw [mul_pow, ← pow_mul]
      _ = 2 * (τ * P ^ (11 * q)) := by rw [hsq]; ring
      _ ≤ 2 * 1 := by gcongr
      _ = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ q := pow_le_pow_right₀ (by norm_num) hq
  have hsP : s * P ^ 11 ≤ 2 := (pow_le_pow_iff_left₀ (by positivity) (by norm_num) hq0).1 hu
  have hrh0 : 0 ≤ rh := by rw [hrh]; positivity
  constructor
  · have hP211 : P ^ 2 ≤ P ^ 11 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have hA1 : (n : ℝ) ^ 2 * Real.sqrt f * g * rd ≤ P ^ 2 :=
      calc (n : ℝ) ^ 2 * Real.sqrt f * g * rd ≤ (n : ℝ) ^ 2 * f * g * rd := by gcongr
        _ = n * (n * f * rd * g) := by ring
        _ ≤ P ^ 2 := hnmP
    have h : (n : ℝ) ^ 2 * Real.sqrt f * g * rd * s ≤ P ^ 11 * s :=
      calc (n : ℝ) ^ 2 * Real.sqrt f * g * rd * s ≤ P ^ 2 * s := mul_le_mul_of_nonneg_right hA1 hs0
        _ ≤ P ^ 11 * s := mul_le_mul_of_nonneg_right hP211 hs0
    have hl := Real.log_two_gt_d9
    rw [hrh]
    linarith
  · have hAeq : 2 * rh * Real.sqrt f * be = ((n : ℝ) ^ 2 * f * g * rd * be / 2) * s := by
      rw [hrh]; linear_combination ((n : ℝ) ^ 2 * g * rd * s * be / 2) * hfs
    have hA16 : (2 * rh * Real.sqrt f * be) ^ (16 * q) ≤ P ^ (96 * q) * (2 * τ) ^ 16 := by
      rw [hAeq]
      calc (((n : ℝ) ^ 2 * f * g * rd * be / 2) * s) ^ (16 * q) ≤ (P ^ 6 * s) ^ (16 * q) :=
            pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hK hs0) _
        _ = P ^ (96 * q) * (2 * τ) ^ 16 := by
          rw [mul_pow, ← pow_mul, show 6 * (16 * q) = 96 * q by ring,
            show 16 * q = q * 16 by ring, pow_mul s q 16, hsq]
    have hW := deep_exponent_core P τ be n g q hP16 hq hτ hτP hbe0 hbe6 hn0 hnP hg0 hgP
    have hsq17 : (17 * Real.sqrt n / τ ^ 2) ^ 2 = 289 * (n : ℝ) / τ ^ 4 := by
      rw [div_pow, mul_pow, hs2, ← pow_mul]; norm_num
    have hexp : Real.exp f ≤ Real.exp 1 ^ N := by
      rw [← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      rw [hNr]
      have h1 : (1 : ℝ) ≤ (n : ℝ) ^ 2 :=
        le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) (by linarith : (1 : ℝ) ≤ n) 2)
      linarith [mul_le_mul_of_nonneg_right h1 hf0]
    have e1 : (2 * rh * Real.sqrt f * be) ^ (2 * (8 * q * N))
        = ((2 * rh * Real.sqrt f * be) ^ (16 * q)) ^ N := by
      rw [← pow_mul]; congr 1; ring
    have e2 : (17 * Real.sqrt n / τ ^ 2) ^ (2 * N) = (289 * (n : ℝ) / τ ^ 4) ^ N := by
      rw [pow_mul, hsq17]
    have e3 : g ^ (2 * N) = (g ^ 2) ^ N := pow_mul g 2 N
    rw [e1, e2, e3]
    calc ((2 * rh * Real.sqrt f * be) ^ (16 * q)) ^ N
          * ((6 * be) ^ N * Real.exp f * (289 * (n : ℝ) / τ ^ 4) ^ N) * (g ^ 2) ^ N * P ^ N
        ≤ (P ^ (96 * q) * (2 * τ) ^ 16) ^ N
          * ((6 * be) ^ N * Real.exp 1 ^ N * (289 * (n : ℝ) / τ ^ 4) ^ N) * (g ^ 2) ^ N * P ^ N := by
          gcongr
      _ = ((P ^ (96 * q) * (2 * τ) ^ 16) * ((6 * be) * Real.exp 1 * (289 * (n : ℝ) / τ ^ 4))
            * g ^ 2 * P) ^ N := by
          simp only [mul_pow]
      _ ≤ Real.exp (-1) ^ N := pow_le_pow_left₀ (by positivity) hW N
      _ = Real.exp (-(N : ℝ)) := by
          rw [← Real.exp_nat_mul]; congr 1; ring

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimOfIsUnitDet
namespace GlobalTheory.GramCount

variable {A : Type} [CommRing A]

def ip (c : A →+* A) {n : ℕ} (x y : Fin n → A) : A := ∑ i, x i * c (y i)

def Prim (c : A →+* A) {m n : ℕ} (x : Fin m → Fin n → A) : Prop :=
  ∃ y : Fin m → Fin n → A, ∀ a b, ip c (x a) (y b) = if a = b then 1 else 0

def sols (c : A →+* A) {m : ℕ} (n : ℕ) (G : Matrix (Fin m) (Fin m) A) :
    Set (Fin m → Fin n → A) :=
  {x | Prim c x ∧ ∀ a b, ip c (x b) (x a) = G a b}

variable (c : A →+* A) {n : ℕ}

theorem ip_add_left (x x' y : Fin n → A) : ip c (x + x') y = ip c x y + ip c x' y := by
  simp only [ip, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem ip_add_right (x y y' : Fin n → A) : ip c x (y + y') = ip c x y + ip c x y' := by
  simp only [ip, Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]

theorem ip_sub_left (x x' y : Fin n → A) : ip c (x - x') y = ip c x y - ip c x' y := by
  simp only [ip, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem ip_zero_left (y : Fin n → A) : ip c 0 y = 0 := by
  simp [ip]

theorem ip_zero_right (x : Fin n → A) : ip c x 0 = 0 := by
  simp [ip]

theorem ip_smul_left (a : A) (x y : Fin n → A) : ip c (a • x) y = a * ip c x y := by
  unfold ip
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem ip_smul_right (a : A) (x y : Fin n → A) : ip c x (a • y) = c a * ip c x y := by
  unfold ip
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  ring

theorem ip_sum_left {ι : Type} (s : Finset ι) (x : ι → Fin n → A) (y : Fin n → A) :
    ip c (∑ a ∈ s, x a) y = ∑ a ∈ s, ip c (x a) y := by
  unfold ip
  simp only [Finset.sum_apply, Finset.sum_mul]
  exact Finset.sum_comm

theorem ip_sum_right {ι : Type} (s : Finset ι) (x : Fin n → A) (y : ι → Fin n → A) :
    ip c x (∑ a ∈ s, y a) = ∑ a ∈ s, ip c x (y a) := by
  unfold ip
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finset.sum_apply, map_sum, Finset.mul_sum]
  exact Finset.sum_comm

theorem cj_ip (hc : ∀ u, c (c u) = u) (x y : Fin n → A) : c (ip c x y) = ip c y x := by
  unfold ip
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, hc, mul_comm]

theorem map_ip {B : Type} [CommRing B] (c' : B →+* B) (φ : A →+* B)
    (hφ : ∀ u, φ (c u) = c' (φ u)) (x y : Fin n → A) :
    φ (ip c x y) = ip c' (fun i => φ (x i)) (fun i => φ (y i)) := by
  unfold ip
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, hφ]

theorem prim_of_isUnit_det (hc : ∀ u, c (c u) = u) {m : ℕ} (x y : Fin m → Fin n → A)
    (h : IsUnit (Matrix.of fun a b => ip c (x a) (y b)).det) : Prim c x := by

  unfold Prim
  refine ⟨fun b => ∑ k, c ((Matrix.of fun a b => ip c (x a) (y b))⁻¹ k b) • y k,
    fun a b => ?_⟩
  have h1 := congrFun (congrFun (Matrix.mul_nonsing_inv _ h) a) b
  rw [Matrix.mul_apply, Matrix.one_apply] at h1
  simp only [Matrix.of_apply] at h1
  rw [ip_sum_right]
  simp only [ip_smul_right, hc]
  rw [← h1]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

theorem prim_of_sub_mem (hc : ∀ u, c (c u) = u) (I : Ideal A) (hI : ∀ u ∈ I, IsUnit (1 + u))
    {m : ℕ} (x y : Fin m → Fin n → A)
    (h : ∀ a b, ip c (x a) (y b) - (if a = b then 1 else 0) ∈ I) : Prim c x := by

  apply prim_of_isUnit_det c hc x y
  have hone : (Ideal.Quotient.mk I).mapMatrix (Matrix.of fun a b => ip c (x a) (y b)) = 1 := by
    ext a b
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.one_apply]
    have hab := h a b
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero] at hab
    rw [hab]
    split_ifs <;> simp
  have key : (Matrix.of fun a b => ip c (x a) (y b)).det - 1 ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, RingHom.map_det, hone,
      Matrix.det_one, sub_self]
  simpa using hI _ key

theorem Prim.map {B : Type} [CommRing B] (c' : B →+* B) (φ : A →+* B)
    (hφ : ∀ u, φ (c u) = c' (φ u)) {m : ℕ} {x : Fin m → Fin n → A} (h : Prim c x) :
    Prim c' (fun a i => φ (x a i)) := by
  unfold Prim at h ⊢
  obtain ⟨y, hy⟩ := h
  refine ⟨fun b i => φ (y b i), fun a b => ?_⟩
  show ip c' (fun i => φ (x a i)) (fun i => φ (y b i)) = _
  rw [← map_ip c c' φ hφ (x a) (y b), hy a b]
  split_ifs <;> simp

theorem prim_of_map (hc : ∀ u, c (c u) = u) {B : Type} [CommRing B] (c' : B →+* B) (φ : A →+* B)
    (hφ : ∀ u, φ (c u) = c' (φ u)) (hs : Function.Surjective φ)
    (hk : ∀ u, φ u = 0 → IsUnit (1 + u)) {m : ℕ} {x : Fin m → Fin n → A}
    (h : Prim c' (fun a i => φ (x a i))) : Prim c x := by

  unfold Prim at h
  obtain ⟨y', hy'⟩ := h
  choose y hy using fun b i => hs (y' b i)
  apply prim_of_sub_mem c hc (RingHom.ker φ) (fun u hu => hk u (RingHom.mem_ker.mp hu)) x y
  intro a b
  have h2 : ip c' (fun i => φ (x a i)) (y' b) = if a = b then 1 else 0 := hy' a b
  have e : (fun i => φ (y b i)) = y' b := funext (hy b)
  rw [RingHom.mem_ker, map_sub, map_ip c c' φ hφ, e, h2]
  split_ifs <;> simp

theorem Prim.eq_zero {m : ℕ} {x : Fin m → Fin n → A} (h : Prim c x) (s : Fin m → A)
    (hs : ∑ a, s a • x a = 0) : s = 0 := by

  unfold Prim at h
  obtain ⟨y, hy⟩ := h
  funext b
  have hb := congrArg (fun z => ip c z (y b)) hs
  simp only [ip_sum_left, ip_smul_left, hy, ip_zero_left] at hb
  simpa using hb

theorem exists_trace_one (hc : ∀ u, c (c u) = u) {ω : A} (hω : IsUnit (ω - c ω)) :
    ∃ θ e : A, θ + c θ = 1 ∧ IsUnit e ∧ c e = -e := by
  obtain ⟨U, hU⟩ := hω
  have h1 : (ω - c ω) * ↑U⁻¹ = 1 := by rw [← hU]; exact U.mul_inv
  have h2 : (c ω - ω) * c ↑U⁻¹ = 1 := by
    have h3 := congrArg c h1
    rwa [map_mul, map_sub, hc, map_one] at h3
  have hv : c ↑U⁻¹ = -(↑U⁻¹ : A) := by
    linear_combination (-(c ↑U⁻¹)) * h1 + (-(↑U⁻¹ : A)) * h2
  refine ⟨ω * ↑U⁻¹, ω - c ω, ?_, ⟨U, hU⟩, ?_⟩
  · rw [map_mul, hv]
    linear_combination h1
  · rw [map_sub, hc]
    ring

theorem card_fixed_sq (hc : ∀ u, c (c u) = u) {ω : A} (hω : IsUnit (ω - c ω))
    {M : Type} [AddCommGroup M] [Module A M] (σ : M →+ M) (hσ : ∀ x, σ (σ x) = x)
    (hs : ∀ (a : A) x, σ (a • x) = c a • σ x) :
    Nat.card {x : M // σ x = x} ^ 2 = Nat.card M ∧
      Nat.card {x : M // σ x = -x} ^ 2 = Nat.card M := by

  obtain ⟨U, hU⟩ := hω
  have h1 : (ω - c ω) * ↑U⁻¹ = 1 := by rw [← hU]; exact U.mul_inv
  have h2 : (c ω - ω) * c ↑U⁻¹ = 1 := by
    have h3 := congrArg c h1
    rwa [map_mul, map_sub, hc, map_one] at h3
  have hvn : c ↑U⁻¹ = -(↑U⁻¹ : A) := by
    linear_combination (-(c ↑U⁻¹)) * h1 + (-(↑U⁻¹ : A)) * h2
  obtain ⟨v, hv1, hv2⟩ : ∃ v : A, (ω - c ω) * v = 1 ∧ c v = -v := ⟨_, h1, hvn⟩
  have hu : c (ω - c ω) = -(ω - c ω) := by
    rw [map_sub, hc]
    ring
  have hg : ∀ x, σ (v • (x - σ x)) = v • (x - σ x) := by
    intro x
    rw [hs, map_sub, hσ, hv2, neg_smul, ← smul_neg, neg_sub]
  have hab : ω * v = c ω * v + 1 := by linear_combination hv1
  have hf : ∀ x, σ (x - ω • v • (x - σ x)) = x - ω • v • (x - σ x) := by
    intro x
    rw [map_sub, hs, hg, smul_smul, smul_smul, hab, add_smul, one_smul]
    abel
  have e : M ≃ {x : M // σ x = x} × {x : M // σ x = x} :=
    { toFun := fun x => (⟨x - ω • v • (x - σ x), hf x⟩, ⟨v • (x - σ x), hg x⟩)
      invFun := fun p => p.1.1 + ω • p.2.1
      left_inv := fun x => sub_add_cancel _ _
      right_inv := fun p => by
        obtain ⟨⟨f, hf0⟩, ⟨g, hg0⟩⟩ := p
        have key : v • (f + ω • g - σ (f + ω • g)) = g := by
          rw [map_add (f := _), hs, hf0, hg0, add_sub_add_left_eq_sub, ← sub_smul, smul_smul, mul_comm,
            hv1, one_smul]
        refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
        · show f + ω • g - ω • v • (f + ω • g - σ (f + ω • g)) = f
          rw [key, add_sub_cancel_right]
        · exact key }
  have e2 : {x : M // σ x = -x} ≃ {x : M // σ x = x} :=
    { toFun := fun x => ⟨v • x.1, by rw [hs, x.2, hv2, smul_neg, neg_smul, neg_neg]⟩
      invFun := fun y => ⟨(ω - c ω) • y.1, by rw [hs, y.2, hu, neg_smul]⟩
      left_inv := fun x => Subtype.ext (by
        show (ω - c ω) • v • x.1 = x.1
        rw [smul_smul, hv1, one_smul])
      right_inv := fun y => Subtype.ext (by
        show v • (ω - c ω) • y.1 = y.1
        rw [smul_smul, mul_comm, hv1, one_smul]) }
  have hM : Nat.card M = Nat.card {x : M // σ x = x} ^ 2 := by
    rw [Nat.card_congr e, Nat.card_prod, sq]
  exact ⟨hM.symm, by rw [Nat.card_congr e2, hM]⟩

end GlobalTheory.GramCount
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsHaarMapProdEq
open MeasureTheory Measure
open scoped NNReal ENNReal

namespace GlobalTheory.St.HaarSplit

theorem exists_haar_map_prod_eq {A B C : Type*} [Group A] [Group B] [Group C]
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    [IsTopologicalGroup A] [IsTopologicalGroup B] [IsTopologicalGroup C]
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    [BorelSpace A] [BorelSpace B] [BorelSpace C]
    [LocallyCompactSpace A] [LocallyCompactSpace B] [LocallyCompactSpace C]
    [SecondCountableTopology A] [SecondCountableTopology B] [SecondCountableTopology C]
    (e : (A × B) ≃ₜ* C) (μA : Measure A) [μA.IsHaarMeasure] (μC : Measure C) [μC.IsHaarMeasure] :
    ∃ μB : Measure B, μB.IsHaarMeasure ∧ (μA.prod μB).map e = μC := by
  let ν : Measure B := Measure.haar
  have : ((μA.prod ν).map e).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map (μA.prod ν) e
  have h := isMulLeftInvariant_eq_smul μC ((μA.prod ν).map e)
  have hc : 0 < haarScalarFactor μC ((μA.prod ν).map e) := haarScalarFactor_pos_of_isHaarMeasure _ _
  refine ⟨haarScalarFactor μC ((μA.prod ν).map e) • ν, IsHaarMeasure.nnreal_smul _ hc.ne', ?_⟩
  conv_rhs => rw [h]
  generalize haarScalarFactor μC ((μA.prod ν).map e) = c
  have he : AEMeasurable (e : A × B → C) (μA.prod ν) :=
    e.continuous.measurable.aemeasurable
  rw [← Measure.map_smul c he]
  congr 1
  rw [ENNReal.smul_def, ENNReal.smul_def, Measure.prod_smul_right]

end GlobalTheory.St.HaarSplit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InnerAddInnerEqZeroSpan
namespace GlobalTheory.InnerSumZeroSpan

theorem main : (let d1 : ℕ → Type := @(fun (n : ℕ) ↦ EuclideanSpace ℂ (Fin n)); ∀ {n : ℕ} (L M : d1 n →L[ℂ] d1 n) (s t : Set (d1 n)), (∀ u ∈ s, ∀ z ∈ t, Inner.inner ℂ ((L : d1 n → d1 n) u) z + Inner.inner ℂ u ((M : d1 n → d1 n) z) = (0 : ℂ)) → ∀ u ∈ Submodule.span ℂ s, ∀ z ∈ Submodule.span ℂ t, Inner.inner ℂ ((L : d1 n → d1 n) u) z + Inner.inner ℂ u ((M : d1 n → d1 n) z) = (0 : ℂ)) := by
  intro d1 n L M s t h u hu z hz
  induction hz using Submodule.span_induction with
  | mem z hz' =>
    induction hu using Submodule.span_induction with
    | mem u hu' => exact h u hu' z hz'
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add (f := _), inner_add_left, inner_add_left, add_add_add_comm, hx, hy, add_zero]
    | smul c x _ hx =>
      rw [map_smul, inner_smul_left, inner_smul_left, ← mul_add, hx, mul_zero]
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add (f := _), inner_add_right, inner_add_right, add_add_add_comm, hx, hy, add_zero]
  | smul c x _ hx =>
    rw [map_smul, inner_smul_right, inner_smul_right, ← mul_add, hx, mul_zero]

end GlobalTheory.InnerSumZeroSpan
end
