module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.SummableAndAbsTsumSubIntegralLe
open Filter Topology MeasureTheory Set
open scoped Real

namespace GlobalTheory.KroneckerLimit

private theorem le_apply_zero_of_monotoneOn_Iic_antitoneOn_Ici {f : ℝ → ℝ} (hm : MonotoneOn f (Iic 0))
    (ha : AntitoneOn f (Ici 0)) (t : ℝ) : f t ≤ f 0 := by
  rcases le_total t 0 with h | h
  · exact hm (Set.mem_Iic.2 h) (Set.mem_Iic.2 le_rfl) h
  · exact ha (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 h) h

theorem abs_sum_range_sub_integral_le {f : ℝ → ℝ} (h0 : ∀ t, 0 ≤ f t) (hc : Continuous f)
    (hm : MonotoneOn f (Iic 0)) (ha : AntitoneOn f (Ici 0)) (x : ℝ) (k : ℕ) :
    |∑ i ∈ Finset.range k, f (x + i) - ∫ t in x..x + k, f t| ≤ f 0 := by
  have htop : ∀ t, f t ≤ f 0 := fun t => le_apply_zero_of_monotoneOn_Iic_antitoneOn_Ici hm ha t
  have hbd : ∀ (a lo hi : ℝ), (∀ t ∈ Icc a (a + 1), lo ≤ f t ∧ f t ≤ hi) →
      lo ≤ ∫ t in a..a + 1, f t ∧ ∫ t in a..a + 1, f t ≤ hi := by
    intro a lo hi h
    have hab : a ≤ a + 1 := by linarith
    constructor
    · have := intervalIntegral.integral_mono_on (μ := volume) hab (continuous_const.intervalIntegrable _ _)
        (hc.intervalIntegrable _ _) (fun t ht => (h t ht).1)
      simpa using this
    · have := intervalIntegral.integral_mono_on (μ := volume) hab (hc.intervalIntegrable _ _)
        (continuous_const.intervalIntegrable _ _) (fun t ht => (h t ht).2)
      simpa using this
  obtain ⟨D, hD⟩ : ∃ D : ℕ → ℝ, ∀ j : ℕ,
      D j = ∑ i ∈ Finset.range j, f (x + i) - ∫ t in x..x + j, f t := ⟨_, fun j => rfl⟩
  have hstep : ∀ j : ℕ, D (j + 1) = D j + (f (x + j) - ∫ t in (x + j)..(x + j + 1), f t) := by
    intro j
    rw [hD, hD, show x + ((j + 1 : ℕ) : ℝ) = x + j + 1 by push_cast; ring, Finset.sum_range_succ,
      ← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable x (x + j))
        (hc.intervalIntegrable (x + j) (x + j + 1))]
    ring
  have key : ∀ j : ℕ, (x + j ≤ 0 → D j ≤ 0) ∧ D j + f (x + j) ≤ f 0 ∧ -f 0 ≤ D j ∧
      (x + j ≤ 0 → -f (x + j) ≤ D j) := by
    intro j
    induction j with
    | zero =>
      have hD0 : D 0 = 0 := by simp [hD]
      simp only [Nat.cast_zero, add_zero, hD0]
      exact ⟨fun _ => le_rfl, by linarith [htop x], by linarith [h0 0], fun _ => by linarith [h0 x]⟩
    | succ j ih =>
      obtain ⟨ih1, ih2, ih3, ih4⟩ := ih
      rw [hstep j, show x + ((j + 1 : ℕ) : ℝ) = x + j + 1 by push_cast; ring]
      rcases le_or_gt (x + j + 1) 0 with hl | hl
      · obtain ⟨hb1, hb2⟩ := hbd (x + j) (f (x + j)) (f (x + j + 1)) (fun t ht =>
          ⟨hm (Set.mem_Iic.2 (by linarith)) (Set.mem_Iic.2 (by linarith [ht.2])) ht.1,
           hm (Set.mem_Iic.2 (by linarith [ht.2])) (Set.mem_Iic.2 hl) ht.2⟩)
        have e1 := ih1 (by linarith)
        have e4 := ih4 (by linarith)
        refine ⟨fun _ => by linarith, by linarith [htop (x + j + 1)],
          by linarith [htop (x + j + 1)], fun _ => by linarith⟩
      · rcases le_or_gt 0 (x + j) with hr | hr
        · obtain ⟨hb1, hb2⟩ := hbd (x + j) (f (x + j + 1)) (f (x + j)) (fun t ht =>
            ⟨ha (Set.mem_Ici.2 (by linarith [ht.1])) (Set.mem_Ici.2 (by linarith)) ht.2,
             ha (Set.mem_Ici.2 hr) (Set.mem_Ici.2 (by linarith [ht.1])) ht.1⟩)
          refine ⟨fun h => by linarith, by linarith, by linarith, fun h => by linarith⟩
        · obtain ⟨hb1, hb2⟩ := hbd (x + j) (f (x + j) + f (x + j + 1) - f 0) (f 0) (fun t ht => by
            refine ⟨?_, htop t⟩
            rcases le_total t 0 with h | h
            · have := hm (Set.mem_Iic.2 hr.le) (Set.mem_Iic.2 h) ht.1
              linarith [htop (x + j + 1)]
            · have := ha (Set.mem_Ici.2 h) (Set.mem_Ici.2 hl.le) ht.2
              linarith [htop (x + j)])
          have e1 := ih1 hr.le
          have e4 := ih4 hr.le
          refine ⟨fun h => by linarith, by linarith, by linarith, fun h => by linarith⟩
  obtain ⟨-, h2, h3, -⟩ := key k
  rw [hD] at h2 h3
  rw [abs_le]
  exact ⟨h3, by linarith [h0 (x + k)]⟩

theorem summable_and_abs_tsum_sub_integral_le {f : ℝ → ℝ} (h0 : ∀ t, 0 ≤ f t) (hc : Continuous f)
    (hm : MonotoneOn f (Iic 0)) (ha : AntitoneOn f (Ici 0)) (hi : Integrable f) (a : ℝ) :
    Summable (fun n : ℤ => f (a + n)) ∧ |∑' n : ℤ, f (a + n) - ∫ t, f t| ≤ f 0 := by
  have htop : ∀ t, f t ≤ f 0 := fun t => le_apply_zero_of_monotoneOn_Iic_antitoneOn_Ici hm ha t
  have hfin : ∀ N : ℕ, ∑ i ∈ Finset.range (2 * N), f (a - N + i) ≤ (∫ t, f t) + f 0 ∧
      ∫ t in (a - N)..(a + N), f t ≤ ∑ i ∈ Finset.range (2 * N), f (a - N + i) + f 0 := by
    intro N
    have h := abs_le.1 (abs_sum_range_sub_integral_le h0 hc hm ha (a - N) (2 * N))
    have he : a - N + ((2 * N : ℕ) : ℝ) = a + N := by push_cast; ring
    rw [he] at h
    have hle : ∫ t in (a - N)..(a + N), f t ≤ ∫ t, f t := by
      rw [intervalIntegral.integral_of_le (by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)])]
      exact setIntegral_le_integral hi (Filter.Eventually.of_forall fun t => h0 t)
    obtain ⟨hl1, hl2⟩ := h
    constructor <;> linarith
  have himg : ∀ N : ℕ, ∑ n ∈ (Finset.range (2 * N)).image (fun i : ℕ => (i : ℤ) - N), f (a + n) =
      ∑ i ∈ Finset.range (2 * N), f (a - N + i) := by
    intro N
    rw [Finset.sum_image (by intro i _ j _ h; simpa using h)]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    push_cast
    ring
  have hset : ∀ s : Finset ℤ, ∃ N : ℕ,
      s ⊆ (Finset.range (2 * N)).image (fun i : ℕ => (i : ℤ) - N) := by
    intro s
    obtain ⟨S, hS⟩ : ∃ S : ℕ, S = ∑ m ∈ s, m.natAbs := ⟨_, rfl⟩
    refine ⟨S + 1, fun n hn => ?_⟩
    have hle : n.natAbs ≤ S := hS ▸
      Finset.single_le_sum (f := fun m : ℤ => m.natAbs) (fun _ _ => Nat.zero_le _) hn
    rw [Finset.mem_image]
    refine ⟨(n + ((S + 1 : ℕ) : ℤ)).toNat, ?_, ?_⟩
    · rw [Finset.mem_range]
      omega
    · omega
  have hbound : ∀ s : Finset ℤ, ∑ n ∈ s, f (a + n) ≤ (∫ t, f t) + f 0 := by
    intro s
    obtain ⟨N, hN⟩ := hset s
    have := Finset.sum_le_sum_of_subset_of_nonneg hN (fun n _ _ => h0 (a + n))
    rw [himg N] at this
    linarith [(hfin N).1]
  have hsum : Summable (fun n : ℤ => f (a + n)) := summable_of_sum_le (fun n => h0 _) hbound
  refine ⟨hsum, abs_le.2 ⟨?_, ?_⟩⟩
  · have hbot : Tendsto (fun N : ℕ => a - (N : ℝ)) atTop atBot :=
      tendsto_atBot.2 fun b => eventually_atTop.2 ⟨⌈a - b⌉₊, fun N hN => by
        have h1 := Nat.le_ceil (a - b)
        have h2 : ((⌈a - b⌉₊ : ℕ) : ℝ) ≤ N := by exact_mod_cast hN
        linarith⟩
    have htop' : Tendsto (fun N : ℕ => a + (N : ℝ)) atTop atTop :=
      tendsto_atTop.2 fun b => eventually_atTop.2 ⟨⌈b - a⌉₊, fun N hN => by
        have h1 := Nat.le_ceil (b - a)
        have h2 : ((⌈b - a⌉₊ : ℕ) : ℝ) ≤ N := by exact_mod_cast hN
        linarith⟩
    have hlim := intervalIntegral_tendsto_integral hi hbot htop'
    have : ∫ t, f t ≤ ∑' n : ℤ, f (a + n) + f 0 := le_of_tendsto' hlim fun N => by
      show ∫ t in (a - N)..(a + N), f t ≤ _
      have h1 := (hfin N).2
      have h2 := hsum.sum_le_tsum ((Finset.range (2 * N)).image (fun i : ℕ => (i : ℤ) - N))
        (fun n _ => h0 _)
      rw [himg N] at h2
      linarith
    linarith
  · have := Real.tsum_le_of_sum_le (fun n => h0 _) hbound
    linarith

noncomputable def betaConst (s : ℝ) : ℝ := √π * Real.Gamma (s - 1 / 2) / Real.Gamma s

private theorem integral_rpow_mul_exp_neg_sq_add_mul_eq {Y s u : ℝ} (hu : 0 < u) :
    ∫ t : ℝ, u ^ (s - 1) * Real.exp (-((t ^ 2 + Y ^ 2) * u)) =
      √π * (u ^ (s - 1 / 2 - 1) * Real.exp (-(Y ^ 2 * u))) := by
  have h : (fun t : ℝ => u ^ (s - 1) * Real.exp (-((t ^ 2 + Y ^ 2) * u))) =
      fun t : ℝ => (u ^ (s - 1) * Real.exp (-(Y ^ 2 * u))) * Real.exp (-u * t ^ 2) := by
    funext t
    rw [show -((t ^ 2 + Y ^ 2) * u) = -(Y ^ 2 * u) + -u * t ^ 2 by ring, Real.exp_add]
    ring
  rw [h, integral_const_mul, integral_gaussian, Real.sqrt_div Real.pi_pos.le,
    show s - 1 / 2 - 1 = (s - 1) - 1 / 2 by ring, Real.rpow_sub hu (s - 1) (1 / 2), Real.sqrt_eq_rpow u]
  ring

private theorem integral_Ioi_rpow_mul_exp_neg_eq_rpow_mul_Gamma {Y s t : ℝ} (hY : 0 < Y) (hs : 0 < s) :
    ∫ u in Ioi (0 : ℝ), u ^ (s - 1) * Real.exp (-((t ^ 2 + Y ^ 2) * u)) =
      (t ^ 2 + Y ^ 2) ^ (-s) * Real.Gamma s := by
  have hp : 0 < t ^ 2 + Y ^ 2 := by positivity
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi hs hp, one_div, Real.inv_rpow hp.le,
    Real.rpow_neg hp.le]

private theorem integrable_uncurry_rpow_mul_exp_neg_sq_add {Y s : ℝ} (hY : 0 < Y) (hs : 1 / 2 < s) :
    Integrable (Function.uncurry fun u t : ℝ => u ^ (s - 1) * Real.exp (-((t ^ 2 + Y ^ 2) * u)))
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
  have hmeas : Measurable fun p : ℝ × ℝ => p.1 ^ (s - 1) * Real.exp (-((p.2 ^ 2 + Y ^ 2) * p.1)) := by
    fun_prop
  refine (integrable_prod_iff hmeas.aestronglyMeasurable).2 ⟨?_, ?_⟩
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun u hu => ?_)
    have h : (fun t : ℝ => u ^ (s - 1) * Real.exp (-((t ^ 2 + Y ^ 2) * u))) =
        fun t : ℝ => (u ^ (s - 1) * Real.exp (-(Y ^ 2 * u))) * Real.exp (-u * t ^ 2) := by
      funext t
      rw [show -((t ^ 2 + Y ^ 2) * u) = -(Y ^ 2 * u) + -u * t ^ 2 by ring, Real.exp_add]
      ring
    rw [h]
    exact (integrable_exp_neg_mul_sq hu).const_mul _
  · have hI := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := s - 1 / 2 - 1) (b := Y ^ 2)
      (by linarith) one_pos (by positivity)
    simp only [Real.rpow_one, neg_mul] at hI
    refine IntegrableOn.congr_fun (hI.const_mul √π) (fun u hu => ?_) measurableSet_Ioi
    have hu' : 0 < u := hu
    try dsimp only
    rw [← integral_rpow_mul_exp_neg_sq_add_mul_eq hu']
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    try dsimp only
    rw [Real.norm_of_nonneg (by positivity)]

theorem integrable_rpow_sq_add {Y s : ℝ} (hY : 0 < Y) (hs : 1 ≤ s) :
    Integrable (fun t : ℝ => (t ^ 2 + Y ^ 2) ^ (-s)) := by
  have hK := integrable_uncurry_rpow_mul_exp_neg_sq_add hY (by linarith : 1 / 2 < s)
  have hΓ : 0 < Real.Gamma s := Real.Gamma_pos_of_pos (by linarith)
  have h := hK.integral_prod_right
  simp only [Function.uncurry_apply_pair] at h
  have h' : Integrable (fun t : ℝ => (t ^ 2 + Y ^ 2) ^ (-s) * Real.Gamma s) := by
    refine h.congr (Filter.Eventually.of_forall fun t => ?_)
    exact integral_Ioi_rpow_mul_exp_neg_eq_rpow_mul_Gamma hY (by linarith)
  have := h'.div_const (Real.Gamma s)
  simpa [hΓ.ne'] using this

theorem integral_rpow_sq_add {Y s : ℝ} (hY : 0 < Y) (hs : 1 / 2 < s) :
    ∫ t : ℝ, (t ^ 2 + Y ^ 2) ^ (-s) = betaConst s * Y ^ (1 - 2 * s) := by
  have hΓ : 0 < Real.Gamma s := Real.Gamma_pos_of_pos (by linarith)
  have hK := integrable_uncurry_rpow_mul_exp_neg_sq_add hY hs
  have hswap := integral_integral_swap hK
  have hB : ∫ u in Ioi (0 : ℝ), ∫ t : ℝ, u ^ (s - 1) * Real.exp (-((t ^ 2 + Y ^ 2) * u)) =
      √π * ((1 / Y ^ 2) ^ (s - 1 / 2) * Real.Gamma (s - 1 / 2)) := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun u hu => integral_rpow_mul_exp_neg_sq_add_mul_eq (s := s) (Y := Y) hu),
      integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi (by linarith) (by positivity)]
  have hA : ∀ t : ℝ, ∫ u in Ioi (0 : ℝ), u ^ (s - 1) * Real.exp (-((t ^ 2 + Y ^ 2) * u)) =
      (t ^ 2 + Y ^ 2) ^ (-s) * Real.Gamma s := fun t => integral_Ioi_rpow_mul_exp_neg_eq_rpow_mul_Gamma hY (by linarith)
  simp only [hA, hB, integral_mul_const] at hswap
  have hY2 : (1 / Y ^ 2) ^ (s - 1 / 2) = Y ^ (1 - 2 * s) := by
    rw [one_div, Real.inv_rpow (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hY.le,
      ← Real.rpow_neg hY.le]
    congr 1
    push_cast
    ring
  rw [hY2] at hswap
  unfold betaConst
  rw [show √π * Real.Gamma (s - 1 / 2) / Real.Gamma s * Y ^ (1 - 2 * s) =
      √π * (Y ^ (1 - 2 * s) * Real.Gamma (s - 1 / 2)) / Real.Gamma s by ring, hswap,
    mul_div_assoc, div_self hΓ.ne', mul_one]

theorem betaConst_one : betaConst 1 = π := by
  unfold betaConst
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, Real.Gamma_one_half_eq, Real.Gamma_one, div_one,
    Real.mul_self_sqrt Real.pi_pos.le]

theorem hasDerivAt_betaConst_one : HasDerivAt betaConst (-2 * π * Real.log 2) 1 := by
  have h1 : HasDerivAt Real.Gamma (-√π * (Real.eulerMascheroniConstant + 2 * Real.log 2)) (1 - 1 / 2) := by
    convert Real.hasDerivAt_Gamma_one_half using 1
    norm_num
  have h2 := ((h1.comp_sub_const 1 (1 / 2)).const_mul √π).div Real.hasDerivAt_Gamma_one
    (by rw [Real.Gamma_one]; exact one_ne_zero)
  have hp := Real.mul_self_sqrt Real.pi_pos.le
  have hf : betaConst = (fun y => √π * Real.Gamma (y - 1 / 2)) / Real.Gamma := by
    funext y
    rfl
  rw [hf]
  refine h2.congr_deriv ?_
  rw [Real.Gamma_one, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, Real.Gamma_one_half_eq]
  linear_combination (-(2 * Real.log 2)) * hp

end GlobalTheory.KroneckerLimit
end

open Filter Topology MeasureTheory Set
open scoped Real

namespace GlobalTheory.KroneckerLimit

noncomputable def rowSum (a Y s : ℝ) : ℝ := ∑' n : ℤ, ((a + n) ^ 2 + Y ^ 2) ^ (-s)

theorem rowSum_bound (a : ℝ) {Y s : ℝ} (hY : 0 < Y) (hs : 1 ≤ s) :
    Summable (fun n : ℤ => ((a + n) ^ 2 + Y ^ 2) ^ (-s)) ∧
      |rowSum a Y s - betaConst s * Y ^ (1 - 2 * s)| ≤ (Y ^ 2) ^ (-s) := by
  have := summable_and_abs_tsum_sub_integral_le (f := fun t : ℝ => (t ^ 2 + Y ^ 2) ^ (-s))
    (fun t => by positivity)
    (Continuous.rpow_const (by fun_prop) fun t => Or.inl (by positivity))
    (fun u (hu : u ≤ 0) v (hv : v ≤ 0) huv => Real.rpow_le_rpow_of_nonpos (by positivity)
      (by nlinarith) (by linarith))
    (fun u (hu : 0 ≤ u) v (hv : 0 ≤ v) huv => Real.rpow_le_rpow_of_nonpos (by positivity)
      (by nlinarith) (by linarith))
    (integrable_rpow_sq_add hY hs) a
  rw [integral_rpow_sq_add hY (by linarith)] at this
  simpa [rowSum] using this

theorem rpow_neg_le {r s : ℝ} (hr : 0 < r) (h1 : 1 ≤ s) (h2 : s ≤ 2) :
    r ^ (-s) ≤ r ^ (-1 : ℝ) + r ^ (-2 : ℝ) := by
  have p1 : 0 ≤ r ^ (-1 : ℝ) := by positivity
  have p2 : 0 ≤ r ^ (-2 : ℝ) := by positivity
  rcases le_total r 1 with h | h
  · have := Real.rpow_le_rpow_of_exponent_ge hr h (show (-2 : ℝ) ≤ -s by linarith)
    linarith
  · have := Real.rpow_le_rpow_of_exponent_le h (show -s ≤ (-1 : ℝ) by linarith)
    linarith

theorem eventually_mem_Ioc_one_two : ∀ᶠ s : ℝ in 𝓝[>] 1, 1 < s ∧ s ≤ 2 :=
  Ioc_mem_nhdsGT (by norm_num)

theorem tendsto_rpow_neg {r : ℝ} (hr : 0 < r) :
    Tendsto (fun s : ℝ => r ^ (-s)) (𝓝[>] 1) (𝓝 (r ^ (-1 : ℝ))) :=
  ((Real.continuousAt_const_rpow hr.ne').comp (f := fun s : ℝ => -s)
    continuous_neg.continuousAt).tendsto.mono_left nhdsWithin_le_nhds

theorem tendsto_rowSum (a : ℝ) {Y : ℝ} (hY : 0 < Y) :
    Tendsto (rowSum a Y) (𝓝[>] 1) (𝓝 (rowSum a Y 1)) := by
  refine tendsto_tsum_of_dominated_convergence
    ((rowSum_bound a hY le_rfl).1.add (rowSum_bound a hY one_le_two).1)
    (fun n => tendsto_rpow_neg (by positivity)) ?_
  filter_upwards [eventually_mem_Ioc_one_two] with s hs n
  rw [Real.norm_of_nonneg (by positivity)]
  exact rpow_neg_le (by positivity) hs.1.le hs.2

theorem rowSum_one (z : ℂ) (hz : 0 < z.im) :
    rowSum z.re z.im 1 = π / z.im + 2 * π / z.im *
      (Complex.exp (2 * π * Complex.I * z) / (1 - Complex.exp (2 * π * Complex.I * z))).re := by
  have hzZ : z ∈ Complex.integerComplement :=
    UpperHalfPlane.coe_mem_integerComplement ⟨z, hz⟩
  have h1 := Complex.hasSum_im (summable_cotTerm hzZ).hasSum
  rw [← cot_series_rep' hzZ] at h1
  set f : ℤ → ℝ := fun n => ((z.re + n) ^ 2 + z.im ^ 2) ^ (-1 : ℝ) with hf
  have h2 : HasSum f (rowSum z.re z.im 1) := (rowSum_bound z.re hz le_rfl).1.hasSum
  have h3 := ((hasSum_nat_add_iff' 1).2 h2.nat_add_neg).mul_left (-z.im)
  have him : ∀ n : ℤ, (1 / (z + n)).im = -z.im * f n := by
    intro n
    simp [hf, Real.rpow_neg_one, Complex.normSq_apply, div_eq_mul_inv, sq]
  have h4 : (fun n : ℕ => (cotTerm z n).im)
      = fun n : ℕ => -z.im * (f ((n + 1 : ℕ) : ℤ) + f (-((n + 1 : ℕ) : ℤ))) := by
    ext n
    rw [mul_add, ← him, ← him, cotTerm, Complex.add_im, add_comm]
    push_cast
    rw [sub_eq_add_neg]
  rw [h4] at h1
  have h5 := h1.unique h3
  have h6 := him 0
  simp only [Int.cast_zero, add_zero] at h6
  have hq : 1 - Complex.exp (2 * π * Complex.I * z) ≠ 0 := by
    have := UpperHalfPlane.norm_exp_two_pi_I_lt_one ⟨z, hz⟩
    intro h
    rw [sub_eq_zero] at h
    simp [← h] at this
  have h7 : π * Complex.cot (π * z) = -Complex.I * (π + 2 * π *
      (Complex.exp (2 * π * Complex.I * z) / (1 - Complex.exp (2 * π * Complex.I * z)))) := by
    rw [Complex.cot_pi_eq_exp_ratio]
    generalize Complex.exp (2 * π * Complex.I * z) = w at hq ⊢
    field_simp
    rw [Complex.I_sq]
    ring
  rw [h7, Complex.sub_im, h6] at h5
  generalize Complex.exp (2 * π * Complex.I * z) / (1 - Complex.exp (2 * π * Complex.I * z)) = w
    at h5 ⊢
  simp at h5
  field_simp
  linarith

theorem hasSum_lambert {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun m : ℕ => (q ^ (m + 1) / (1 - q ^ (m + 1))).re / (m + 1))
      (-Real.log ‖∏' k : ℕ, (1 - q ^ (k + 1))‖) := by
  set F : ℕ × ℕ → ℂ := fun p => (q ^ (p.1 + 1)) ^ (p.2 + 1) / (p.2 + 1) with hF
  have hq0 := norm_nonneg q
  have hpow : ∀ k : ℕ, ‖q ^ (k + 1)‖ < 1 := fun k => by
    rw [norm_pow]; exact pow_lt_one₀ hq0 hq (by omega)
  have hs : Summable F := by
    have g := summable_geometric_of_lt_one hq0 hq
    refine .of_norm_bounded (g.mul_of_nonneg g (fun _ => by positivity) fun _ => by positivity) ?_
    rintro ⟨k, m⟩
    simp only [hF, norm_div, norm_pow, ← pow_mul, ← pow_add]
    have : (1 : ℝ) ≤ ‖(m + 1 : ℂ)‖ := by
      rw [show (m + 1 : ℂ) = ((m + 1 : ℕ) : ℂ) by push_cast; rfl, Complex.norm_natCast]
      push_cast; linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]
    refine (div_le_self (by positivity) this).trans ?_
    exact pow_le_pow_of_le_one hq0 hq.le (by nlinarith)
  have hA : HasSum (fun k : ℕ => -Complex.log (1 - q ^ (k + 1))) (∑' p, F p) := by
    refine hs.hasSum.prod_fiberwise fun k => ?_
    simpa [hF] using Complex.hasSum_taylorSeries_neg_log' (hpow k)
  have hB : HasSum (fun m : ℕ => q ^ (m + 1) / (1 - q ^ (m + 1)) / (m + 1)) (∑' p, F p) := by
    refine ((Equiv.prodComm ℕ ℕ).hasSum_iff.2 hs.hasSum).prod_fiberwise fun m => ?_
    have := ((hasSum_geometric_of_norm_lt_one (hpow m)).mul_left (q ^ (m + 1))).div_const
      (m + 1 : ℂ)
    rw [← div_eq_mul_inv] at this
    refine this.congr_fun fun k => ?_
    simp only [hF, Function.comp_apply, Equiv.prodComm_apply, Prod.swap_prod_mk]
    ring
  have hne : ∀ k : ℕ, 1 - q ^ (k + 1) ≠ 0 := fun k h => by
    have := hpow k
    rw [sub_eq_zero] at h
    simp [← h] at this
  have hA' : HasSum (fun k : ℕ => Complex.log (1 - q ^ (k + 1))) (-∑' p, F p) := by
    simpa using hA.neg
  rw [← Complex.cexp_tsum_eq_tprod hne hA'.summable, hA'.tsum_eq, Complex.norm_exp, Real.log_exp,
    Complex.neg_re, neg_neg]
  convert Complex.hasSum_re hB using 2 with m
  rw [show (m + 1 : ℂ) = ((m + 1 : ℝ) : ℂ) by push_cast; rfl, Complex.div_ofReal_re]

theorem tendsto_zeta_two_mul_sub_one :
    Tendsto (fun s : ℝ => (∑' n : ℕ, (n + 1 : ℝ) ^ (1 - 2 * s)) - 1 / (2 * (s - 1))) (𝓝[>] 1)
      (𝓝 Real.eulerMascheroniConstant) := by
  have h0 : Tendsto (fun s : ℝ => 2 * s - 1) (𝓝[>] 1) (𝓝[>] 1) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Continuous fun s : ℝ => 2 * s - 1 := by fun_prop
      have := (this.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Ioi 1))
      norm_num at this
      exact this
    · filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
      show 1 < 2 * s - 1
      linarith
  have h1 := (Complex.continuous_re.tendsto _).comp
    (ZetaAsymptotics.tendsto_riemannZeta_sub_one_div_nhds_right.comp h0)
  rw [Complex.ofReal_re] at h1
  refine h1.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
  simp only [Function.comp_apply]
  refine (congrArg Complex.re ?_).trans (Complex.ofReal_re _)
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by rw [Complex.ofReal_re]; linarith),
    Complex.ofReal_sub (∑' _, _), Complex.ofReal_tsum]
  congr 1
  · congr 1 with n
    rw [Complex.ofReal_cpow (by positivity), one_div, ← Complex.cpow_neg]
    congr 1 <;> push_cast <;> ring
  · push_cast
    congr 1
    ring

theorem tendsto_integral_part {y : ℝ} (hy : 0 < y) :
    Tendsto (fun s : ℝ => 2 * (betaConst s * y ^ (1 - s)) * (∑' n : ℕ, (n + 1 : ℝ) ^ (1 - 2 * s))
      - π / (s - 1)) (𝓝[>] 1)
      (𝓝 (2 * π * (Real.eulerMascheroniConstant - Real.log 2) - π * Real.log y)) := by
  set g : ℝ → ℝ := fun s => betaConst s * y ^ (1 - s) with hg
  have hg1 : g 1 = π := by simp [hg, betaConst_one]
  have hd : HasDerivAt g (-2 * π * Real.log 2 - π * Real.log y) 1 := by
    have h1 : HasDerivAt (fun s : ℝ => y ^ (1 - s)) _ 1 :=
      ((hasDerivAt_id' (1 : ℝ)).const_sub 1).const_rpow hy
    refine (hasDerivAt_betaConst_one.mul h1).congr_deriv ?_
    simp [betaConst_one]
    ring
  have t1 : Tendsto g (𝓝[>] 1) (𝓝 π) :=
    hg1 ▸ hd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have t2 := (hasDerivAt_iff_tendsto_slope.1 hd).mono_left
    (nhdsWithin_mono _ (show Ioi (1 : ℝ) ⊆ {1}ᶜ from fun _ h => ne_of_gt h))
  have t3 := ((t1.const_mul 2).mul tendsto_zeta_two_mul_sub_one).add t2
  convert t3.congr' ?_ using 2
  · ring
  · filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
    have : s - 1 ≠ 0 := by linarith
    rw [slope_def_field, hg1]
    change _ = 2 * g s * _ - _
    field_simp
    ring

theorem summable_zero_row {s : ℝ} (hs : 1 ≤ s) :
    Summable (fun n : ℤ => (((0 : ℝ) + n) ^ 2 + 0 ^ 2) ^ (-s)) := by
  refine (Real.summable_abs_int_rpow (b := 2 * s) (by linarith)).congr fun n => ?_
  rw [show -(2 * s) = ((2 : ℕ) : ℝ) * (-s) by push_cast; ring, Real.rpow_natCast_mul (abs_nonneg _)]
  simp

theorem tendsto_zero_row : Tendsto (rowSum 0 0) (𝓝[>] 1) (𝓝 (π ^ 2 / 3)) := by
  have h1 : rowSum 0 0 1 = π ^ 2 / 3 := by
    have h2 := (summable_zero_row le_rfl).hasSum.nat_add_neg
    have h3 := hasSum_zeta_two.mul_left 2
    have := h2.unique (h3.congr_fun fun n => by simp [Real.rpow_neg_one]; ring)
    simp at this
    simp [rowSum, this]
    ring
  rw [← h1]
  refine tendsto_tsum_of_dominated_convergence (summable_zero_row le_rfl) (fun n => ?_) ?_
  · rcases eq_or_ne n 0 with rfl | hn
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
      simp [Real.zero_rpow (show -s ≠ 0 by linarith)]
    · exact tendsto_rpow_neg (by simp; positivity)
  · filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s) n
    rw [Real.norm_of_nonneg (by positivity)]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [Real.zero_rpow (show -s ≠ 0 by linarith)]
    · refine Real.rpow_le_rpow_of_exponent_le ?_ (by linarith)
      have : (1 : ℤ) ≤ n ^ 2 := (by positivity : (0 : ℤ) < n ^ 2)
      simpa using (by exact_mod_cast this : (1 : ℝ) ≤ (n : ℝ) ^ 2)

noncomputable def rowError (x y : ℝ) (m : ℕ) (s : ℝ) : ℝ :=
  rowSum ((m + 1) * x) ((m + 1) * y) s - betaConst s * ((m + 1) * y) ^ (1 - 2 * s)

theorem summable_sq_rpow {y s : ℝ} (hy : 0 < y) (hs : 1 ≤ s) :
    Summable fun m : ℕ => (((m + 1) * y) ^ 2) ^ (-s) := by
  have := ((summable_nat_add_iff 1).2
    (Real.summable_nat_rpow.2 (show -(2 * s) < -1 by linarith))).mul_right ((y ^ 2) ^ (-s))
  refine this.congr fun m => ?_
  rw [mul_pow, Real.mul_rpow (by positivity) (by positivity),
    show -(2 * s) = ((2 : ℕ) : ℝ) * (-s) by push_cast; ring, Real.rpow_natCast_mul (by positivity)]
  push_cast
  rfl

theorem summable_rowError (x : ℝ) {y s : ℝ} (hy : 0 < y) (hs : 1 ≤ s) :
    Summable fun m => rowError x y m s :=
  .of_norm_bounded (summable_sq_rpow hy hs) fun m =>
    (rowSum_bound _ (by positivity) hs).2

theorem tendsto_tsum_rowError (x : ℝ) {y : ℝ} (hy : 0 < y) :
    Tendsto (fun s => ∑' m, rowError x y m s) (𝓝[>] 1) (𝓝 (∑' m, rowError x y m 1)) := by
  refine tendsto_tsum_of_dominated_convergence
    ((summable_sq_rpow hy le_rfl).add (summable_sq_rpow hy one_le_two)) (fun m => ?_) ?_
  · have hY : 0 < ((m : ℝ) + 1) * y := by positivity
    refine (tendsto_rowSum _ hY).sub (Tendsto.mono_left ?_ nhdsWithin_le_nhds)
    refine hasDerivAt_betaConst_one.continuousAt.tendsto.mul ?_
    exact ((Real.continuousAt_const_rpow hY.ne').comp (f := fun s : ℝ => 1 - 2 * s)
      (by fun_prop)).tendsto
  · filter_upwards [eventually_mem_Ioc_one_two] with s hs m
    exact (rowSum_bound _ (by positivity) hs.1.le).2.trans (rpow_neg_le (by positivity) hs.1.le hs.2)

theorem tsum_rowError_one (z : ℂ) (hz : 0 < z.im) :
    ∑' m, rowError z.re z.im m 1
      = -(2 * π / z.im) * Real.log ‖∏' k : ℕ, (1 - ModularForm.eta_q k z)‖ := by
  have hq := UpperHalfPlane.norm_exp_two_pi_I_lt_one ⟨z, hz⟩
  have h := (hasSum_lambert hq).mul_left (2 * π / z.im)
  simp only [ModularForm.eta_q_eq_pow]
  rw [neg_mul, ← mul_neg]
  refine HasSum.tsum_eq (h.congr_fun fun m => ?_)
  have hY : 0 < ((m : ℝ) + 1) * z.im := by positivity
  have := rowSum_one ((m + 1) * z) (by simpa using hY)
  rw [show 2 * π * Complex.I * ((m + 1) * z) = ((m + 1 : ℕ) : ℂ) * (2 * π * Complex.I * z) by
    push_cast; ring, Complex.exp_nat_mul] at this
  have e1 : ((m + 1) * z).re = (m + 1) * z.re := by simp
  have e2 : ((m + 1) * z).im = (m + 1) * z.im := by simp
  rw [e1, e2] at this
  rw [rowError, this, betaConst_one, show (1 : ℝ) - 2 * 1 = -1 by norm_num, Real.rpow_neg_one]
  simp only
  field_simp
  ring

theorem rowSum_neg (a Y s : ℝ) : rowSum (-a) (-Y) s = rowSum a Y s := by
  rw [rowSum, rowSum, ← (Equiv.neg ℤ).tsum_eq]
  congr 1 with n
  congr 1
  simp only [Equiv.neg_apply, Int.cast_neg]
  ring

theorem summable_row (x : ℝ) {y s : ℝ} (hy : 0 < y) (hs : 1 ≤ s) (m : ℤ) :
    Summable fun n : ℤ => (((m : ℝ) * x + n) ^ 2 + (m * y) ^ 2) ^ (-s) := by
  rcases eq_or_ne m 0 with rfl | hm
  · simpa using summable_zero_row hs
  · have := (rowSum_bound (m * x) (Y := |m * y|) (by positivity) hs).1
    simpa only [sq_abs] using this

theorem hasSum_rows (x : ℝ) {y s : ℝ} (hy : 0 < y) (hs : 1 < s) :
    HasSum (fun m : ℤ => rowSum (m * x) (m * y) s)
      (rowSum 0 0 s + 2 * (∑' m, rowError x y m s)
        + 2 * (betaConst s * y ^ (1 - 2 * s)) * ∑' n : ℕ, (n + 1 : ℝ) ^ (1 - 2 * s)) := by
  have h1 : Summable fun n : ℕ => (n + 1 : ℝ) ^ (1 - 2 * s) := by
    exact_mod_cast (summable_nat_add_iff 1).2
      (Real.summable_nat_rpow.2 (show 1 - 2 * s < -1 by linarith))
  have h2 : HasSum (fun m : ℕ => rowSum ((m + 1) * x) ((m + 1) * y) s)
      ((∑' m, rowError x y m s)
        + (betaConst s * y ^ (1 - 2 * s)) * ∑' n : ℕ, (n + 1 : ℝ) ^ (1 - 2 * s)) := by
    refine ((summable_rowError x hy hs.le).hasSum.add (h1.hasSum.mul_left _)).congr_fun fun m => ?_
    rw [rowError, Real.mul_rpow (by positivity) hy.le]
    ring
  have h3 := HasSum.of_add_one_of_neg_add_one (f := fun m : ℤ => rowSum (m * x) (m * y) s)
    (h2.congr_fun fun m => by push_cast; rfl)
    (h2.congr_fun fun m => by push_cast; rw [neg_mul, neg_mul, rowSum_neg])
  convert h3 using 1
  simp
  ring

theorem hasSum_lattice (x : ℝ) {y s : ℝ} (hy : 0 < y) (hs : 1 < s) :
    HasSum (fun p : ℤ × ℤ => (((p.1 : ℝ) * x + p.2) ^ 2 + (p.1 * y) ^ 2) ^ (-s))
      (rowSum 0 0 s + 2 * (∑' m, rowError x y m s)
        + 2 * (betaConst s * y ^ (1 - 2 * s)) * ∑' n : ℕ, (n + 1 : ℝ) ^ (1 - 2 * s)) := by
  have h : Summable fun p : ℤ × ℤ => (((p.1 : ℝ) * x + p.2) ^ 2 + (p.1 * y) ^ 2) ^ (-s) :=
    (summable_prod_of_nonneg fun p => by positivity).2
      ⟨summable_row x hy hs.le, (hasSum_rows x hy hs).summable⟩
  rw [← (hasSum_rows x hy hs).tsum_eq]
  exact h.tsum_prod ▸ h.hasSum

theorem log_norm_eta_sq (z : ℂ) (hz : 0 < z.im) :
    Real.log (‖ModularForm.eta z‖ ^ 2)
      = -(π * z.im / 6) + 2 * Real.log ‖∏' k : ℕ, (1 - ModularForm.eta_q k z)‖ := by
  rw [Real.log_pow, ModularForm.eta, norm_mul, Real.log_mul
    (norm_ne_zero_iff.2 (Function.Periodic.qParam_ne_zero _))
    (norm_ne_zero_iff.2 (ModularForm.eta_tprod_ne_zero hz)), Function.Periodic.norm_qParam,
    Real.log_exp]
  push_cast
  ring

theorem hasSum_eisenstein (τ : UpperHalfPlane) {s : ℝ} (hs : 1 < s) :
    HasSum (fun p : {p : ℤ × ℤ // p ≠ 0} =>
        τ.im ^ s / ‖(p.1.1 * τ + p.1.2 : ℂ)‖ ^ (2 * s))
      (τ.im ^ s * (rowSum 0 0 s + 2 * (∑' m, rowError τ.re τ.im m s))
        + 2 * (betaConst s * τ.im ^ (1 - s)) * ∑' n : ℕ, (n + 1 : ℝ) ^ (1 - 2 * s)) := by
  have hy := τ.im_pos
  have h := (hasSum_lattice τ.re hy hs).mul_left (τ.im ^ s)
  have e : τ.im ^ (1 - s) = τ.im ^ s * τ.im ^ (1 - 2 * s) := by
    rw [← Real.rpow_add hy]; congr 1; ring
  have h' := (hasSum_subtype_iff_of_support_subset (s := {p : ℤ × ℤ | p ≠ 0}) (by
    intro p hp h0
    apply hp
    simp [h0, Real.zero_rpow (show -s ≠ 0 by linarith)])).2 h
  rw [mul_add (τ.im ^ s), show ∀ a b c d : ℝ, a * (2 * (b * c) * d) = 2 * (b * (a * c)) * d by
    intros; ring, ← e] at h'
  refine h'.congr_fun (fun p => ?_)
  · rw [show 2 * s = ((2 : ℕ) : ℝ) * s by norm_num, Real.rpow_natCast_mul (norm_nonneg _),
      Complex.sq_norm, Complex.normSq_apply, Function.comp_apply,
      Real.rpow_neg (by positivity), div_eq_mul_inv]
    simp [sq]

end GlobalTheory.KroneckerLimit

namespace GlobalTheory

open KroneckerLimit

theorem summable_realEisenstein (τ : UpperHalfPlane) {s : ℝ} (hs : 1 < s) :
    Summable fun p : {p : ℤ × ℤ // p ≠ 0} => τ.im ^ s / ‖(p.1.1 * τ + p.1.2 : ℂ)‖ ^ (2 * s) :=
  (hasSum_eisenstein τ hs).summable

theorem tendsto_realEisenstein_sub_pole (τ : UpperHalfPlane) :
    Tendsto (fun s : ℝ =>
        (∑' p : {p : ℤ × ℤ // p ≠ 0}, τ.im ^ s / ‖(p.1.1 * τ + p.1.2 : ℂ)‖ ^ (2 * s))
          - π / (s - 1)) (𝓝[>] 1)
      (𝓝 (2 * π * (Real.eulerMascheroniConstant - Real.log 2) - π * Real.log τ.im
        - 2 * π * Real.log (‖ModularForm.eta τ‖ ^ 2))) := by
  have hy := τ.im_pos
  have t0 : Tendsto (fun s : ℝ => τ.im ^ s) (𝓝[>] 1) (𝓝 τ.im) := by
    simpa using (Real.continuousAt_const_rpow (b := 1) hy.ne').tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi 1))
  have t1 := (t0.mul (tendsto_zero_row.add ((tendsto_tsum_rowError τ.re hy).const_mul 2))).add
    (tendsto_integral_part hy)
  have e1 := tsum_rowError_one τ hy
  have e2 := log_norm_eta_sq τ hy
  rw [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at e1
  rw [UpperHalfPlane.coe_im] at e2
  convert t1.congr' ?_ using 2
  · rw [e1, e2]
    field_simp
    ring
  · filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
    rw [(hasSum_eisenstein τ hs).tsum_eq]
    ring

end GlobalTheory
