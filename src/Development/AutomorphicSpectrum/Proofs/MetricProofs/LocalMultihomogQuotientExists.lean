module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.CxSimple
public import Development.WeilBound.CoreStatements.RationalSupMetrics.AevalCoordProd

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.RationalSupMetrics.ValuationUniqueOnForms
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Small Filter Topology

theorem MultiProjectiveCoordinates.valuation_unique_on_forms : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (𝕜 : Type) [Field 𝕜] (a : K → ℤ) (s : Ω) (z : (Σ k, ι k) → 𝕜) (w : 𝕜), z ∈ ptsOver 𝕜 (mCoordIdeal y) → HasVal y a s z w → (∀ (dg dh : K → ℕ) (g h : MRing ι), IsMultiHomog g dg → IsMultiHomog h dh → (∀ k, (dg k : ℤ) = dh k + a k) → aeval y g = s * aeval y h → aeval z g = w * aeval z h) ∧ ∀ w', HasVal y a s z w' → w' = w := by
  intro K _ ι _ Ω _ y 𝕜 _ a s z w hz hw
  obtain ⟨dg0, dh0, g0, h0, hg0, hh0, hd0, e0, hne, e1⟩ := hw
  have key : ∀ (dg dh : K → ℕ) (g h : MRing ι), IsMultiHomog g dg → IsMultiHomog h dh →
      (∀ k, (dg k : ℤ) = dh k + a k) → aeval y g = s * aeval y h → aeval z g = w * aeval z h := by
    intro dg dh g h hg hh hd e
    have hdeg : dg0 + dh = dg + dh0 := by
      funext k
      have h1 := hd k
      have h2 := hd0 k
      simp only [Pi.add_apply]
      omega
    have f1 := MultiProjectiveCoordinates.Val.mh_mul hg hh0
    have f2 := MultiProjectiveCoordinates.Val.mh_mul hg0 hh
    rw [hdeg] at f2
    have h3 := MultiProjectiveCoordinates.Val.form_vanish y hz (MultiProjectiveCoordinates.Val.mh_sub f1 f2) (by
      rw [map_sub, map_mul, map_mul, e, e0]
      ring)
    rw [map_sub, map_mul, map_mul, e1] at h3
    apply mul_right_cancel₀ hne
    linear_combination h3
  refine ⟨key, ?_⟩
  rintro w' ⟨dg, dh, g, h, hg, hh, hd, e, hn, e'⟩
  have := key dg dh g h hg hh hd e
  exact mul_right_cancel₀ hn (e'.symm.trans this)
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.MetricQuotientOfMultihomogPair
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LojasiewiczInequalityAnalytic
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LojasiewiczInequalityAnalytic
open Filter Topology Metric

noncomputable section
namespace GlobalTheory.CompanionTheory.Loj

theorem one_variable {f g : ℂ → ℂ} {ρ m M : ℝ} {d : ℕ} (hρ : 0 < ρ) (hm : 0 < m)
    (hf : ∀ z ∈ closedBall (0 : ℂ) ρ, AnalyticAt ℂ f z)
    (hg : ∀ z ∈ closedBall (0 : ℂ) ρ, AnalyticAt ℂ g z)
    (hgm : ∀ z ∈ sphere (0 : ℂ) ρ, m ≤ ‖g z‖) (hfM : ∀ z ∈ sphere (0 : ℂ) ρ, ‖f z‖ ≤ M)
    (hz : ∀ z ∈ closedBall (0 : ℂ) ρ, g z = 0 → f z = 0 ∧ analyticOrderAt g z ≤ d) :
    ‖f 0‖ ^ (d + 1) ≤ M ^ (d + 1) / m * ‖g 0‖ := by
  have h0mem : (0 : ℂ) ∈ closedBall (0 : ℂ) ρ := by simp [hρ.le]
  have hQ : ∀ z ∈ closedBall (0 : ℂ) ρ, AnalyticAt ℂ (fun w => f w ^ (d + 1) / g w) z := by
    intro z hzm
    by_cases h0 : g z = 0
    · obtain ⟨hf0, hord⟩ := hz z hzm h0
      have hne : analyticOrderAt g z ≠ ⊤ := ne_top_of_le_ne_top (by simp) hord
      obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 hne
      have hkd : k ≤ d := by
        rw [← hk] at hord
        exact_mod_cast hord
      obtain ⟨h, hh, hh0, eh⟩ := (hg z hzm).analyticOrderAt_eq_natCast.1 hk.symm
      obtain ⟨u, hu, eu⟩ := (natCast_le_analyticOrderAt (hf z hzm) (n := 1)).1
        ((natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hf z hzm)).2 (fun i hi => by
          obtain rfl : i = 0 := by omega
          simpa using hf0))
      obtain ⟨n, hn⟩ : ∃ n, d + 1 = (n + 1) + k := ⟨d - k, by omega⟩
      have ha : AnalyticAt ℂ (fun w => (w - z) ^ (n + 1) * (u w ^ (d + 1) / h w)) z := by
        have h1 : AnalyticAt ℂ (fun w => u w ^ (d + 1) / h w) z := (hu.fun_pow _).fun_div hh hh0
        have h2 : AnalyticAt ℂ (fun w : ℂ => (w - z) ^ (n + 1)) z := by fun_prop
        exact h2.fun_mul h1
      refine ha.congr ?_
      filter_upwards [eh, eu, hh.continuousAt.eventually_ne hh0] with w e1 e2 e3
      by_cases hw : w = z
      · subst hw
        simp [h0]
      · have hwz : w - z ≠ 0 := sub_ne_zero.2 hw
        rw [e1, e2, smul_eq_mul, smul_eq_mul, pow_one, mul_pow, hn]
        field_simp
        ring
    · exact ((hf z hzm).fun_pow _).fun_div (hg z hzm) h0
  have hdiff : DiffContOnCl ℂ (fun w => f w ^ (d + 1) / g w) (ball (0 : ℂ) ρ) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ hρ.ne']
    exact fun z hzm => (hQ z hzm).differentiableAt.differentiableWithinAt
  have hbd : ∀ z ∈ frontier (ball (0 : ℂ) ρ), ‖f z ^ (d + 1) / g z‖ ≤ M ^ (d + 1) / m := by
    intro z hzm
    rw [frontier_ball _ hρ.ne'] at hzm
    rw [norm_div, norm_pow]
    have hM : 0 ≤ M := (norm_nonneg _).trans (hfM z hzm)
    exact div_le_div₀ (pow_nonneg hM _) (pow_le_pow_left₀ (norm_nonneg _) (hfM z hzm) _) hm
      (hgm z hzm)
  have hmax := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hdiff hbd
    (subset_closure (mem_ball_self hρ))
  by_cases h0 : g 0 = 0
  · simp [(hz 0 h0mem h0).1, h0]
  · have hpos : 0 < ‖g 0‖ := norm_pos_iff.2 h0
    rw [norm_div, norm_pow, div_le_iff₀ hpos] at hmax
    exact hmax

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def dirDeriv (v : E) (h : E → ℂ) : E → ℂ := fun y => fderiv ℂ h y v

theorem analyticAt_dirDeriv (v : E) {h : E → ℂ} {y : E} (hh : AnalyticAt ℂ h y) :
    AnalyticAt ℂ (dirDeriv v h) y :=
  ((ContinuousLinearMap.apply ℂ ℂ v).analyticAt _).comp hh.fderiv

theorem analyticAt_iterate_dirDeriv (v : E) {h : E → ℂ} {y : E} (hh : AnalyticAt ℂ h y) (k : ℕ) :
    AnalyticAt ℂ ((dirDeriv v)^[k] h) y := by
  induction k with
  | zero => simpa using hh
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact analyticAt_dirDeriv v ih

theorem continuous_line (y v : E) : Continuous (fun ζ : ℂ => y + ζ • v) := by fun_prop

theorem analyticAt_line (y v : E) (z : ℂ) : AnalyticAt ℂ (fun ζ : ℂ => y + ζ • v) z := by
  fun_prop

theorem iteratedDeriv_line {U : Set E} (hU : IsOpen U) {g : E → ℂ}
    (hg : ∀ y ∈ U, AnalyticAt ℂ g y) (y v : E) (k : ℕ) :
    ∀ z : ℂ, y + z • v ∈ U →
      iteratedDeriv k (fun ζ : ℂ => g (y + ζ • v)) z = ((dirDeriv v)^[k] g) (y + z • v) := by
  induction k with
  | zero => intro z _; simp
  | succ k ih =>
    intro z hz
    have hev : ∀ᶠ ζ in 𝓝 z, y + ζ • v ∈ U :=
      (continuous_line y v).continuousAt.eventually_mem (hU.mem_nhds hz)
    have e : iteratedDeriv k (fun ζ : ℂ => g (y + ζ • v)) =ᶠ[𝓝 z]
        fun ζ => ((dirDeriv v)^[k] g) (y + ζ • v) := by
      filter_upwards [hev] with ζ hζ using ih ζ hζ
    rw [iteratedDeriv_succ, e.deriv_eq, Function.iterate_succ_apply']
    have hd : HasFDerivAt ((dirDeriv v)^[k] g) (fderiv ℂ ((dirDeriv v)^[k] g) (y + z • v))
        (y + z • v) := (analyticAt_iterate_dirDeriv v (hg _ hz) k).differentiableAt.hasFDerivAt
    have hl : HasDerivAt (fun ζ : ℂ => y + ζ • v) v z := by
      simpa using ((hasDerivAt_id z).smul_const v).const_add y
    exact (hd.comp_hasDerivAt z hl).deriv

theorem order_le_of_iteratedDeriv_ne {h : ℂ → ℂ} {z : ℂ} (hh : AnalyticAt ℂ h z) {d : ℕ}
    (hd : iteratedDeriv d h z ≠ 0) : analyticOrderAt h z ≤ d := by
  by_contra hlt
  rw [not_le] at hlt
  have h1 : ((d + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt h z := by
    simpa using Order.add_one_le_of_lt hlt
  exact hd ((natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hh).1 h1 d (Nat.lt_succ_self d))

theorem lojasiewicz (e : ℕ) (f g : (Fin e → ℂ) → ℂ) (x : Fin e → ℂ) (hf : AnalyticAt ℂ f x)
    (hg : AnalyticAt ℂ g x) (hfg : ∀ᶠ y in 𝓝 x, g y = 0 → f y = 0) :
    ∃ (N : ℕ) (C : ℝ), 0 < N ∧ ∀ᶠ y in 𝓝 x, ‖f y‖ ^ N ≤ C * ‖g y‖ := by
  by_cases hz : ∀ᶠ y in 𝓝 x, g y = 0
  · refine ⟨1, 0, one_pos, ?_⟩
    filter_upwards [hz, hfg] with y h1 h2
    simp [h2 h1]
  obtain ⟨r₀, hr₀, han⟩ := Metric.eventually_nhds_iff_ball.1
    (hf.eventually_analyticAt.and hg.eventually_analyticAt)
  obtain ⟨y₁, hy₁, hgy₁⟩ : ∃ y₁ ∈ ball x r₀, g y₁ ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hz (by filter_upwards [ball_mem_nhds x hr₀] with y hy using hcon y hy)
  set v := y₁ - x with hv
  have hvr : ‖v‖ < r₀ := by simpa [hv, dist_eq_norm] using hy₁
  set φ : ℂ → ℂ := fun ζ => g (x + ζ • v) with hφ
  have hgU : ∀ y ∈ ball x r₀, AnalyticAt ℂ g y := fun y hy => (han y hy).2
  have hφa : ∀ ζ : ℂ, x + ζ • v ∈ ball x r₀ → AnalyticAt ℂ φ ζ := fun ζ hζ =>
    AnalyticAt.comp (g := g) (f := fun ζ : ℂ => x + ζ • v) (hgU _ hζ) (analyticAt_line x v ζ)
  have hunit : ∀ ζ ∈ closedBall (0 : ℂ) 1, x + ζ • v ∈ ball x r₀ := by
    intro ζ hζ
    have h1 : ‖ζ‖ ≤ 1 := by simpa using hζ
    have h2 : ‖ζ • v‖ ≤ ‖v‖ := by
      rw [norm_smul]
      exact mul_le_of_le_one_left (norm_nonneg _) h1
    simpa [dist_eq_norm] using lt_of_le_of_lt h2 hvr
  have hφ0 : ∀ᶠ ζ in 𝓝[≠] (0 : ℂ), φ ζ ≠ 0 := by
    refine ((hφa 0 (hunit 0 (by simp))).eventually_eq_zero_or_eventually_ne_zero).resolve_left ?_
    intro hev
    have hA : AnalyticOnNhd ℂ φ (closedBall (0 : ℂ) 1) := fun ζ hζ => hφa ζ (hunit ζ hζ)
    have := hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_closedBall (0 : ℂ) 1).isPreconnected (z₀ := 0) (by simp) hev
      (show (1 : ℂ) ∈ closedBall (0 : ℂ) 1 by simp)
    apply hgy₁
    simpa [hφ, hv] using this
  obtain ⟨i, hi⟩ : ∃ i, iteratedDeriv i φ 0 ≠ 0 := by
    have hφ00 := hφa 0 (hunit 0 (by simp))
    have hne : analyticOrderAt φ 0 ≠ ⊤ := by
      intro htop
      have h' := (analyticOrderAt_eq_top.1 htop).filter_mono (nhdsWithin_le_nhds (s := {0}ᶜ))
      obtain ⟨z, hz1, hz2⟩ := (hφ0.and h').exists
      exact hz1 hz2
    obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.1 hne
    by_contra hcon
    push_neg at hcon
    have := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (n := d + 1) hφ00).2
      (fun j _ => hcon j)
    rw [← hd] at this
    have h2 : d + 1 ≤ d := by exact_mod_cast this
    omega
  set G := (dirDeriv v)^[i] g with hG
  have hGx : G x ≠ 0 := by
    have := iteratedDeriv_line isOpen_ball hgU x v i 0 (hunit 0 (by simp))
    rw [show (fun ζ : ℂ => g (x + ζ • v)) = φ from rfl] at this
    simpa [this] using hi
  have hGc : ContinuousAt G x :=
    (analyticAt_iterate_dirDeriv v hg i).continuousAt
  set M := ‖f x‖ + 1 with hM
  have hfb : ∀ᶠ y in 𝓝 x, ‖f y‖ ≤ M :=
    (hf.continuousAt.norm.eventually (gt_mem_nhds (lt_add_one _))).mono fun y hy => le_of_lt hy
  obtain ⟨r, hr, hP⟩ := Metric.eventually_nhds_iff_ball.1
    (((hfg.and (hGc.eventually_ne hGx)).and hfb).and (ball_mem_nhds x hr₀))
  obtain ⟨ε, hε, hφε⟩ := Metric.eventually_nhds_iff_ball.1 (eventually_nhdsWithin_iff.1 hφ0)
  set ρ := min (ε / 2) (r / (2 * (‖v‖ + 1))) with hρdef
  have hv1 : 0 < ‖v‖ + 1 := by positivity
  have hρ : 0 < ρ := lt_min (by positivity) (by positivity)
  have hρε : ρ < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hρv : ρ * ‖v‖ < r / 2 := by
    have h1 : ρ * (‖v‖ + 1) ≤ r / 2 := by
      have h2 : ρ ≤ r / (2 * (‖v‖ + 1)) := min_le_right _ _
      calc ρ * (‖v‖ + 1) ≤ r / (2 * (‖v‖ + 1)) * (‖v‖ + 1) :=
            mul_le_mul_of_nonneg_right h2 hv1.le
        _ = r / 2 := by field_simp
    nlinarith
  have hclose : ∀ y ∈ ball x (r / 2), ∀ ζ ∈ closedBall (0 : ℂ) ρ, y + ζ • v ∈ ball x r := by
    intro y hy ζ hζ
    have h1 : ‖ζ‖ ≤ ρ := by simpa using hζ
    have h2 : ‖ζ • v‖ ≤ ρ * ‖v‖ := by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    have h3 : ‖y - x‖ < r / 2 := by simpa [dist_eq_norm] using hy
    rw [mem_ball, dist_eq_norm]
    calc ‖y + ζ • v - x‖ = ‖(y - x) + ζ • v‖ := by congr 1; abel
      _ ≤ ‖y - x‖ + ‖ζ • v‖ := norm_add_le _ _
      _ < r := by linarith
  have hxr : x ∈ ball x (r / 2) := mem_ball_self (by positivity)
  have hsph : ∀ ζ ∈ sphere (0 : ℂ) ρ, ζ ∈ closedBall (0 : ℂ) ρ := fun ζ hζ => sphere_subset_closedBall hζ
  have hcont : ContinuousOn (fun ζ => ‖φ ζ‖) (sphere (0 : ℂ) ρ) := by
    intro ζ hζ
    have h1 := (hP _ (hclose x hxr ζ (hsph ζ hζ))).2
    exact (hφa ζ h1).continuousAt.norm.continuousWithinAt
  have hne : (sphere (0 : ℂ) ρ).Nonempty := NormedSpace.sphere_nonempty.2 hρ.le
  obtain ⟨ζ₀, hζ₀, hmin⟩ := (isCompact_sphere (0 : ℂ) ρ).exists_isMinOn hne hcont
  have hφpos : ∀ ζ ∈ sphere (0 : ℂ) ρ, φ ζ ≠ 0 := by
    intro ζ hζ
    have h1 : ‖ζ‖ = ρ := by simpa using hζ
    refine hφε ζ (by simp [h1, hρε]) ?_
    intro h0
    have h00 : ζ = 0 := by simpa using h0
    rw [h00, norm_zero] at h1
    exact hρ.ne h1
  set m := ‖φ ζ₀‖ / 2 with hmdef
  have hm : 0 < m := by
    have := norm_pos_iff.2 (hφpos ζ₀ hζ₀)
    positivity
  have htube : ∀ᶠ y in 𝓝 x, ∀ ζ ∈ sphere (0 : ℂ) ρ, m < ‖g (y + ζ • v)‖ := by
    refine (isCompact_sphere (0 : ℂ) ρ).eventually_forall_of_forall_eventually fun ζ hζ => ?_
    have h1 : x + ζ • v ∈ ball x r₀ := (hP _ (hclose x hxr ζ (hsph ζ hζ))).2
    have hc : ContinuousAt (fun p : (Fin e → ℂ) × ℂ => ‖g (p.1 + p.2 • v)‖) (x, ζ) := by
      have h2 : ContinuousAt (fun p : (Fin e → ℂ) × ℂ => p.1 + p.2 • v) (x, ζ) := by fun_prop
      exact (ContinuousAt.comp (g := g) (f := fun p : (Fin e → ℂ) × ℂ => p.1 + p.2 • v)
        (x := (x, ζ)) (hgU _ h1).continuousAt h2).norm
    have hlt : m < ‖g (x + ζ • v)‖ := by
      have h3 : ‖φ ζ₀‖ ≤ ‖φ ζ‖ := hmin hζ
      have h4 : 0 < ‖φ ζ₀‖ := norm_pos_iff.2 (hφpos ζ₀ hζ₀)
      have h5 : ‖φ ζ‖ = ‖g (x + ζ • v)‖ := rfl
      rw [hmdef]
      linarith
    exact hc.eventually (lt_mem_nhds hlt)
  refine ⟨i + 1, M ^ (i + 1) / m, Nat.succ_pos i, ?_⟩
  filter_upwards [htube, ball_mem_nhds x (half_pos hr)] with y ht hy
  have hin := hclose y hy
  have key := one_variable (f := fun ζ : ℂ => f (y + ζ • v)) (g := fun ζ : ℂ => g (y + ζ • v))
    (ρ := ρ) (m := m) (M := M) (d := i) hρ hm
    (fun z hzm => AnalyticAt.comp (g := f) (f := fun ζ : ℂ => y + ζ • v)
      (han _ (hP _ (hin z hzm)).2).1 (analyticAt_line y v z))
    (fun z hzm => AnalyticAt.comp (g := g) (f := fun ζ : ℂ => y + ζ • v)
      (han _ (hP _ (hin z hzm)).2).2 (analyticAt_line y v z))
    (fun z hzm => (ht z hzm).le)
    (fun z hzm => (hP _ (hin z (hsph z hzm))).1.2)
    (fun z hzm h0 => by
      have hQ := hP _ (hin z hzm)
      refine ⟨hQ.1.1.1 h0, order_le_of_iteratedDeriv_ne
        (AnalyticAt.comp (g := g) (f := fun ζ : ℂ => y + ζ • v)
          (han _ hQ.2).2 (analyticAt_line y v z)) ?_⟩
      show iteratedDeriv i (fun ζ : ℂ => g (y + ζ • v)) z ≠ 0
      rw [iteratedDeriv_line isOpen_ball hgU y v i z hQ.2]
      exact hQ.1.1.2)
  simpa using key

end GlobalTheory.CompanionTheory.Loj
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LojasiewiczInequalityAnalyticStatement
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lojasiewicz_inequality_analytic : ∀ (e : ℕ) (f g : (Fin e → ℂ) → ℂ) (x : Fin e → ℂ), AnalyticAt ℂ f x → AnalyticAt ℂ g x → (∀ᶠ y in nhds x, g y = 0 → f y = 0) → ∃ (N : ℕ) (C : ℝ), 0 < N ∧ ∀ᶠ y in nhds x, ‖f y‖ ^ N ≤ C * ‖g y‖ := by
  first | exact @GlobalTheory.CompanionTheory.Loj.lojasiewicz | exact GlobalTheory.CompanionTheory.Loj.lojasiewicz | (intros; apply GlobalTheory.CompanionTheory.Loj.lojasiewicz <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.MetricQuotientOfMultihomogPair
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Small.Fund

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Small.Decay

open Filter Topology

theorem analyticAt_aeval {E σ : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {v : E → σ → ℂ} {z : E}
    (hv : ∀ p, AnalyticAt ℂ (fun w => v w p) z) (q : MvPolynomial σ ℤ) :
    AnalyticAt ℂ (fun w => (aeval (v w) q : ℂ)) z := by
  induction q using MvPolynomial.induction_on with
  | C a => simpa using analyticAt_const
  | add p q hp hq =>
    simp only [map_add (f := _)]
    exact hp.add hq
  | mul_X p i hp =>
    simp only [map_mul, aeval_X]
    exact hp.mul (hv i)

theorem continuousAt_of_chart {X Y E : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace E]
    (c : OpenPartialHomeomorph X E) {x : X} (hx : x ∈ c.source) {F : X → Y}
    (h : ContinuousAt (fun z => F (c.symm z)) (c x)) : ContinuousAt F x := by
  have h1 : ContinuousAt (fun y => F (c.symm (c y))) x :=
    ContinuousAt.comp (f := c) (g := fun z => F (c.symm z)) h (c.continuousAt hx)
  refine h1.congr ?_
  filter_upwards [c.open_source.mem_nhds hx] with y hy
  rw [c.left_inv hy]

theorem isOpen_multicone {K : Type*} [Finite K] {ι : K → Type*} :
    IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have h : {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} = ⋂ k, ⋃ i, {z | z ⟨k, i⟩ ≠ 0} := by
    ext z
    simp
  rw [h]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

theorem eventually_abs_le {X : Type*} [TopologicalSpace X] {u : X → ℝ} {x : X} (h : ContinuousAt u x) :
    ∀ᶠ y in 𝓝 x, |u y| ≤ |u x| + 1 :=
  (h.abs.eventually_lt (continuousAt_const (y := |u x| + 1)) (by linarith)).mono fun _ hy => hy.le

theorem section_zero {e : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas e X} {L : LocPot X}
    {s : X → X → ℂ} (hs : IsSection A L s) {x x' y : X} (hy : y ∈ L.U x ∩ L.U x') (h0 : s x y = 0) :
    s x' y = 0 := by
  have h := hs.2 x x' y hy
  rw [h0, norm_zero, zero_mul] at h
  exact norm_eq_zero.1 ((mul_eq_zero.1 h.symm).resolve_right (Real.exp_ne_zero _))

theorem logNormSec_eq {e : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas e X} {L : LocPot X}
    {s : X → X → ℂ} (hs : IsSection A L s) {x y : X} (hy : y ∈ L.U x) (h0 : s x y ≠ 0) :
    logNormSec L s y = Real.log ‖s x y‖ - L.φ x y := by
  unfold logNormSec
  rw [hs.2 y x y ⟨L.mem_U y, hy⟩, Real.log_mul (norm_ne_zero_iff.2 h0) (Real.exp_ne_zero _), Real.log_exp]
  ring

theorem log_ratio_scale {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (Eh : HermLine ι)
    {dg dh : K → ℕ} {G Hf : MRing ι} (hG : IsMultiHomog G dg) (hH : IsMultiHomog Hf dh)
    (hdeg : ∀ k, (dg k : ℤ) = dh k + Eh.a k) (t : K → ℂ) (ht : ∀ k, t k ≠ 0) (w : (Σ k, ι k) → ℂ)
    (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) (hGw : aeval w G ≠ (0 : ℂ)) (hHw : aeval w Hf ≠ (0 : ℂ)) :
    Real.log ‖(aeval w G : ℂ) / aeval w Hf‖ - Real.log (Eh.h w) =
      Real.log ‖(aeval (fun p => t p.1 * w p) G : ℂ) / aeval (fun p => t p.1 * w p) Hf‖ -
        Real.log (Eh.h fun p => t p.1 * w p) := by
  rw [aeval_scale hG, aeval_scale hH, Eh.smul t w ht]
  have hT : 0 < ∏ k, ‖t k‖ ^ Eh.a k := Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.2 (ht k)) _
  have hP : ‖∏ k, t k ^ dg k‖ = ‖∏ k, t k ^ dh k‖ * ∏ k, ‖t k‖ ^ Eh.a k := by
    simp only [norm_prod, norm_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_natCast, hdeg k, zpow_add₀ (norm_ne_zero_iff.2 (ht k)), zpow_natCast]
  have hPh : ‖∏ k, t k ^ dh k‖ ≠ 0 :=
    norm_ne_zero_iff.2 (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (ht k))
  have hn : ‖((∏ k, t k ^ dg k) * aeval w G : ℂ) / ((∏ k, t k ^ dh k) * aeval w Hf)‖ =
      (∏ k, ‖t k‖ ^ Eh.a k) * ‖(aeval w G : ℂ) / aeval w Hf‖ := by
    rw [norm_div, norm_mul, norm_mul, hP, norm_div]
    field_simp
  have hq : ‖(aeval w G : ℂ) / aeval w Hf‖ ≠ 0 := norm_ne_zero_iff.2 (div_ne_zero hGw hHw)
  rw [hn, Real.log_mul hT.ne' hq, Real.log_mul hT.ne' (Eh.pos w hw).ne']
  ring

theorem decay_arith {N : ℕ} (hN : 0 < N) {Lf lh lg φ lC Bh Bφ : ℝ} (h1 : (N : ℝ) * Lf ≤ lC + lg)
    (h2 : |lh| ≤ Bh) (h3 : |φ| ≤ Bφ) :
    Lf - lh ≤ -(1 / (2 * (N : ℝ))) * (Real.exp 1 - 2 * (lg - φ)) +
      ((lC + Real.exp 1 / 2 + Bφ) / (N : ℝ) + Bh) := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have e1 : Lf ≤ (lC + lg) / N := by
    rw [le_div_iff₀ hn]
    linarith
  have e2 : -(1 / (2 * (N : ℝ))) * (Real.exp 1 - 2 * (lg - φ)) + (lC + Real.exp 1 / 2 + Bφ) / N =
      (lC + lg) / N + (Bφ - φ) / N := by
    field_simp
    ring
  have e3 : 0 ≤ (Bφ - φ) / N := div_nonneg (by linarith [le_abs_self φ]) hn.le
  have e4 : -lh ≤ Bh := by linarith [neg_abs_le lh]
  linarith

theorem local_decay : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (e : ℕ) (R : AnLogRes P J e) (σ : Type) (S : PB.AnSys e σ) (π : R.X → S.X), HoloMap R.A S.A π → ∀ (Eh : HermLine ι), IsSmoothHerm Eh → ∀ (dg dh : K → ℕ) (G Hf : MRing ι), IsMultiHomog G dg → IsMultiHomog Hf dh → (∀ k, (dg k : ℤ) = dh k + Eh.a k) → (∀ y : R.X, aeval (R.lift y y) G ≠ (0 : ℂ) → aeval (R.lift y y) Hf ≠ (0 : ℂ) → π y ∈ S.open') → ∀ x₀ : R.X, aeval (R.lift x₀ x₀) Hf ≠ (0 : ℂ) → ∃ (V : Set R.X) (N : ℕ) (C : ℝ), IsOpen V ∧ x₀ ∈ V ∧ 0 < N ∧ ∀ y ∈ V, aeval (R.lift y y) Hf ≠ (0 : ℂ) ∧ (π y ∈ S.open' → aeval (R.lift y y) G ≠ (0 : ℂ) → Real.log ‖(aeval (R.lift y y) G : ℂ) / aeval (R.lift y y) Hf‖ - Real.log (Eh.h (R.lift y y)) ≤ -(1 / (2 * (N : ℝ))) * rW S.L S.s (π y) + C) := by
  intro K _ ι _ P J e R σ S π hπ Eh hEh dg dh G Hf hG hH hdeg hyp x₀ hx₀
  obtain ⟨j, hj⟩ := R.A.cover x₀
  obtain ⟨k, hk⟩ := S.A.cover (π x₀)
  have hz₀ : (R.A.chart j).symm (R.A.chart j x₀) = x₀ := (R.A.chart j).left_inv hj
  have hd₀ : (S.A.chart k).symm (S.A.chart k (π x₀)) = π x₀ := (S.A.chart k).left_inv hk
  have hcoord : ∀ p, AnalyticAt ℂ (fun z => R.lift x₀ ((R.A.chart j).symm z) p) (R.A.chart j x₀) := fun p =>
    R.holo x₀ p j _ ⟨(R.A.chart j).map_source hj, by
      show (R.A.chart j).symm (R.A.chart j x₀) ∈ R.U x₀
      rw [hz₀]; exact R.mem_U x₀⟩
  have hGa := analyticAt_aeval hcoord G
  have hHa := analyticAt_aeval hcoord Hf
  have hHc : ContinuousAt (fun y => (aeval (R.lift x₀ y) Hf : ℂ)) x₀ :=
    continuousAt_of_chart (R.A.chart j) hj hHa.continuousAt
  have hne : ∀ᶠ y in 𝓝 x₀, (aeval (R.lift x₀ y) Hf : ℂ) ≠ 0 := hHc.eventually_ne hx₀
  have hU : ∀ᶠ y in 𝓝 x₀, y ∈ R.U x₀ := (R.isOpen_U x₀).mem_nhds (R.mem_U x₀)
  have hS : ∀ᶠ y in 𝓝 x₀, y ∈ (R.A.chart j).source := (R.A.chart j).open_source.mem_nhds hj
  have hπc : ContinuousAt π x₀ := hπ.1.continuousAt
  have hπU : ∀ᶠ y in 𝓝 x₀, π y ∈ S.L.U (π x₀) :=
    hπc.eventually_mem ((S.L.isOpen_U _).mem_nhds (S.L.mem_U _))
  have hπk : ∀ᶠ y in 𝓝 x₀, π y ∈ (S.A.chart k).source :=
    hπc.eventually_mem ((S.A.chart k).open_source.mem_nhds hk)
  have tend : Tendsto (R.A.chart j).symm (𝓝 (R.A.chart j x₀)) (𝓝 x₀) := by
    have h := (R.A.chart j).continuousAt_symm ((R.A.chart j).map_source hj)
    rwa [ContinuousAt, hz₀] at h

  let f : (Fin e → ℂ) → ℂ := fun z =>
    (aeval (R.lift x₀ ((R.A.chart j).symm z)) G : ℂ) / aeval (R.lift x₀ ((R.A.chart j).symm z)) Hf
  let g : (Fin e → ℂ) → ℂ := fun z => S.s (π x₀) (π ((R.A.chart j).symm z))
  have hf : AnalyticAt ℂ f (R.A.chart j x₀) := hGa.div hHa (by simpa only [hz₀] using hx₀)
  have hg : AnalyticAt ℂ g (R.A.chart j x₀) := by
    have h1 : AnalyticAt ℂ ((S.A.chart k) ∘ π ∘ (R.A.chart j).symm) (R.A.chart j x₀) :=
      hπ.2 j k _ ⟨(R.A.chart j).map_source hj, by
        show π ((R.A.chart j).symm (R.A.chart j x₀)) ∈ (S.A.chart k).source
        rw [hz₀]; exact hk⟩
    have h2 : AnalyticAt ℂ (S.s (π x₀) ∘ (S.A.chart k).symm)
        (((S.A.chart k) ∘ π ∘ (R.A.chart j).symm) (R.A.chart j x₀)) := by
      have e1 : ((S.A.chart k) ∘ π ∘ (R.A.chart j).symm) (R.A.chart j x₀) = S.A.chart k (π x₀) := by
        simp only [Function.comp_apply, hz₀]
      rw [e1]
      exact S.sec.1 (π x₀) k _ ⟨(S.A.chart k).map_source hk, by
        show (S.A.chart k).symm (S.A.chart k (π x₀)) ∈ S.L.U (π x₀)
        rw [hd₀]; exact S.L.mem_U _⟩
    refine (h2.comp h1).congr ?_
    filter_upwards [tend.eventually hπk] with z hz
    simp only [Function.comp_apply, g, (S.A.chart k).left_inv hz]

  have hzero : ∀ᶠ z in 𝓝 (R.A.chart j x₀), g z = 0 → f z = 0 := by
    filter_upwards [tend.eventually hU, tend.eventually hπU, tend.eventually hne] with z h1 h2 h3 h0
    obtain ⟨t, ht, hlt⟩ := R.compat x₀ _ _ ⟨h1, R.mem_U ((R.A.chart j).symm z)⟩
    have hs := section_zero S.sec (x := π x₀) (x' := π ((R.A.chart j).symm z))
      ⟨h2, S.L.mem_U _⟩ h0
    have hHy : (aeval (R.lift ((R.A.chart j).symm z) ((R.A.chart j).symm z)) Hf : ℂ) ≠ 0 := by
      intro h00
      apply h3
      rw [hlt, aeval_scale hH, h00, mul_zero]
    have hGy : (aeval (R.lift ((R.A.chart j).symm z) ((R.A.chart j).symm z)) G : ℂ) = 0 := by
      by_contra hG0
      exact hyp _ hG0 hHy hs
    show (aeval (R.lift x₀ ((R.A.chart j).symm z)) G : ℂ) / _ = 0
    rw [hlt, aeval_scale hG, hGy, mul_zero, zero_div]
  obtain ⟨N, C₀, hN, hloj⟩ := GlobalTheory.T.lojasiewicz_inequality_analytic e f g _ hf hg hzero
  have hloj' : ∀ᶠ y in 𝓝 x₀, ‖f (R.A.chart j y)‖ ^ N ≤ C₀ * ‖g (R.A.chart j y)‖ :=
    ((R.A.chart j).continuousAt hj).eventually hloj

  have hφc : ContinuousAt (S.L.φ (π x₀)) (π x₀) :=
    continuousAt_of_chart (S.A.chart k) hk
      (((S.potL.1 (π x₀) k).continuousOn).continuousAt
        (((S.A.chart k).isOpen_inter_preimage_symm (S.L.isOpen_U _)).mem_nhds
          ⟨(S.A.chart k).map_source hk, by
            show (S.A.chart k).symm (S.A.chart k (π x₀)) ∈ S.L.U (π x₀)
            rw [hd₀]; exact S.L.mem_U _⟩))
  have hφb := eventually_abs_le (u := fun y => S.L.φ (π x₀) (π y)) (ContinuousAt.comp (g := S.L.φ (π x₀)) hφc hπc)
  have hℓ : ContinuousAt (fun y => R.lift x₀ y) x₀ :=
    continuousAt_pi.2 fun p => continuousAt_of_chart (R.A.chart j) hj (hcoord p).continuousAt
  have hmem : R.lift x₀ x₀ ∈ {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := (R.mem x₀ x₀ (R.mem_U x₀)).1
  have hhc : ContinuousAt Eh.h (R.lift x₀ x₀) :=
    (ContDiffOn.continuousOn hEh).continuousAt (isOpen_multicone.mem_nhds hmem)
  have hlogc : ContinuousAt (fun y => Real.log (Eh.h (R.lift x₀ y))) x₀ :=
    ContinuousAt.log (ContinuousAt.comp (g := Eh.h) hhc hℓ) (Eh.pos _ hmem).ne'
  have hhb := eventually_abs_le hlogc
  obtain ⟨V, hV, hVo, hxV⟩ := eventually_nhds_iff.1
    (hU.and (hS.and (hπU.and (hne.and (hloj'.and (hφb.and hhb))))))
  refine ⟨V, N, (Real.log (max C₀ 1) + Real.exp 1 / 2 + (|S.L.φ (π x₀) (π x₀)| + 1)) / (N : ℝ) +
    (|Real.log (Eh.h (R.lift x₀ x₀))| + 1), hVo, hxV, hN, fun y hy => ?_⟩
  obtain ⟨y1, y2, y3, y4, y5, y6, y7⟩ := hV y hy
  obtain ⟨t, ht, hlt⟩ := R.compat x₀ y y ⟨y1, R.mem_U y⟩
  have hw : ∀ k, ∃ i, R.lift y y ⟨k, i⟩ ≠ 0 := (R.mem y y (R.mem_U y)).1
  have hHy : (aeval (R.lift y y) Hf : ℂ) ≠ 0 := by
    intro h00
    apply y4
    rw [hlt, aeval_scale hH, h00, mul_zero]
  refine ⟨hHy, fun hop hGy => ?_⟩
  have hs : S.s (π y) (π y) ≠ 0 := hop
  have hgne : S.s (π x₀) (π y) ≠ 0 := fun h0 => hs (section_zero S.sec ⟨y3, S.L.mem_U _⟩ h0)
  have hGl : (aeval (R.lift x₀ y) G : ℂ) ≠ 0 := by
    rw [hlt, aeval_scale hG]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (ht k)) hGy
  have hfy : f (R.A.chart j y) = (aeval (R.lift x₀ y) G : ℂ) / aeval (R.lift x₀ y) Hf := by
    simp only [f, (R.A.chart j).left_inv y2]
  have hgy : g (R.A.chart j y) = S.s (π x₀) (π y) := by
    simp only [g, (R.A.chart j).left_inv y2]
  rw [hfy, hgy] at y5
  have hfne : (aeval (R.lift x₀ y) G : ℂ) / aeval (R.lift x₀ y) Hf ≠ 0 := div_ne_zero hGl y4
  have key := log_ratio_scale Eh hG hH hdeg t ht (R.lift y y) hw hGy hHy
  rw [← hlt] at key
  rw [key, rW, logNormSec_eq S.sec y3 hgne]
  have hloglog : (N : ℝ) * Real.log ‖(aeval (R.lift x₀ y) G : ℂ) / aeval (R.lift x₀ y) Hf‖ ≤
      Real.log (max C₀ 1) + Real.log ‖S.s (π x₀) (π y)‖ := by
    have hC : 0 < max C₀ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    have hgp : 0 < ‖S.s (π x₀) (π y)‖ := norm_pos_iff.2 hgne
    have hle : ‖(aeval (R.lift x₀ y) G : ℂ) / aeval (R.lift x₀ y) Hf‖ ^ N ≤
        max C₀ 1 * ‖S.s (π x₀) (π y)‖ :=
      y5.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hgp.le)
    have := Real.log_le_log (pow_pos (norm_pos_iff.2 hfne) N) hle
    rwa [Real.log_pow, Real.log_mul hC.ne' hgp.ne'] at this
  exact decay_arith hN hloglog y7 y6

end GlobalTheory.CompanionTheory.Ar.Small.Decay
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.MetricQuotientOfMultihomogPairStatement
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Small.Fund

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.metric_quotient_of_multihomog_pair : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (e : ℕ) (R : AnLogRes P J e) (σ : Type) (S : PB.AnSys e σ) (π : R.X → S.X), HoloMap R.A S.A π → ∀ (Eh : HermLine ι), IsSmoothHerm Eh → ∀ (dg dh : K → ℕ) (G Hf : MRing ι), IsMultiHomog G dg → IsMultiHomog Hf dh → (∀ k, (dg k : ℤ) = dh k + Eh.a k) → (∀ y : R.X, aeval (R.lift y y) G ≠ (0 : ℂ) → aeval (R.lift y y) Hf ≠ (0 : ℂ) → π y ∈ S.open') → ∀ x₀ : R.X, aeval (R.lift x₀ x₀) Hf ≠ (0 : ℂ) → ∃ (V : Set R.X) (N : ℕ) (C : ℝ), IsOpen V ∧ x₀ ∈ V ∧ 0 < N ∧ ∀ y ∈ V, aeval (R.lift y y) Hf ≠ (0 : ℂ) ∧ (π y ∈ S.open' → aeval (R.lift y y) G ≠ (0 : ℂ) → Real.log ‖(aeval (R.lift y y) G : ℂ) / aeval (R.lift y y) Hf‖ - Real.log (Eh.h (R.lift y y)) ≤ -(1 / (2 * (N : ℝ))) * rW S.L S.s (π y) + C) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Small.Decay.local_decay | exact GlobalTheory.CompanionTheory.Ar.Small.Decay.local_decay | (intros; apply GlobalTheory.CompanionTheory.Ar.Small.Decay.local_decay <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.MultihomogeneousValueWellDefined
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.MultihomogeneousValueWellDefined
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Small Filter Topology

namespace GlobalTheory.CompanionTheory.Ar.Small

theorem hasVal_read_of_rep : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (𝕜 : Type) [Field 𝕜] (a : K → ℤ) (s : Ω) (z : (Σ k, ι k) → 𝕜) (w : 𝕜), z ∈ ptsOver 𝕜 (mCoordIdeal y) → HasVal y a s z w → (∀ (dg dh : K → ℕ) (g h : MRing ι), IsMultiHomog g dg → IsMultiHomog h dh → (∀ k, (dg k : ℤ) = dh k + a k) → aeval y g = s * aeval y h → aeval z g = w * aeval z h) ∧ ∀ w', HasVal y a s z w' → w' = w :=
  MultiProjectiveCoordinates.valuation_unique_on_forms

end GlobalTheory.CompanionTheory.Ar.Small
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.MultihomogeneousValueWellDefinedStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Small Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multihomogeneous_value_well_defined : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (𝕜 : Type) [Field 𝕜] (a : K → ℤ) (s : Ω) (z : (Σ k, ι k) → 𝕜) (w : 𝕜), z ∈ ptsOver 𝕜 (mCoordIdeal y) → HasVal y a s z w → (∀ (dg dh : K → ℕ) (g h : MRing ι), IsMultiHomog g dg → IsMultiHomog h dh → (∀ k, (dg k : ℤ) = dh k + a k) → aeval y g = s * aeval y h → aeval z g = w * aeval z h) ∧ ∀ w', HasVal y a s z w' → w' = w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Small.hasVal_read_of_rep | exact GlobalTheory.CompanionTheory.Ar.Small.hasVal_read_of_rep | (intros; apply GlobalTheory.CompanionTheory.Ar.Small.hasVal_read_of_rep <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalMultihomogQuotientExists
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Small.Fund

namespace GlobalTheory.CompanionTheory.Ar.Small.GlobDecay

theorem mem_ptsOver_of_mem_mcPts {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) : z ∈ ptsOver ℂ P := by
  refine ⟨hz.1, fun f hf => ?_⟩
  have h := hz.2 f hf
  rw [eval_map] at h
  rw [aeval_def]
  simpa [algebraMap_int_eq] using h

end GlobalTheory.CompanionTheory.Ar.Small.GlobDecay

namespace GlobalTheory.CompanionTheory.Ar.Small.GlobDecay

theorem global_decay : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (J : Ideal (MRing ι)) (e : ℕ) (R : AnLogRes (mCoordIdeal y) J e) (σ : Type) (S : PB.AnSys e σ) (π : R.X → S.X), HoloMap R.A S.A π → ∀ (Eh : HermLine ι), IsSmoothHerm Eh → ∀ ε : Ω, (∀ x : R.X, ∃ (dg dh : K → ℕ) (G Hf : MRing ι), IsMultiHomog G dg ∧ IsMultiHomog Hf dh ∧ (∀ k, (dg k : ℤ) = dh k + Eh.a k) ∧ aeval y G = ε * aeval y Hf ∧ aeval (R.lift x x) Hf ≠ (0 : ℂ)) → (∀ (x : R.X) (dg dh : K → ℕ) (G Hf : MRing ι), IsMultiHomog G dg → IsMultiHomog Hf dh → (∀ k, (dg k : ℤ) = dh k + Eh.a k) → aeval y G = ε * aeval y Hf → aeval (R.lift x x) G ≠ (0 : ℂ) → aeval (R.lift x x) Hf ≠ (0 : ℂ) → π x ∈ S.open') → ∃ δ C : ℝ, 0 < δ ∧ ∀ x : R.X, π x ∈ S.open' → ∀ v : ℂ, HasVal y Eh.a ε (R.lift x x) v → v ≠ 0 → Real.log ‖v‖ - Real.log (Eh.h (R.lift x x)) ≤ -δ * rW S.L S.s (π x) + C := by
  intro K _ ι _ Ω _ y J e R σ S π hπ Eh hEh ε h1 h2
  choose dg dh G Hf hG hH hd hy hne using h1
  have loc := fun x₀ : R.X => GlobalTheory.T.metric_quotient_of_multihomog_pair K ι (mCoordIdeal y) J e R σ S π hπ Eh hEh (dg x₀) (dh x₀)
    (G x₀) (Hf x₀) (hG x₀) (hH x₀) (hd x₀)
    (fun x a b => h2 x _ _ _ _ (hG x₀) (hH x₀) (hd x₀) (hy x₀) a b) x₀ (hne x₀)
  choose V N C hVo hV hN hb using loc
  obtain ⟨t, ht⟩ := isCompact_univ.elim_nhds_subcover V (fun x _ => (hVo x).mem_nhds (hV x))
  refine ⟨1 / (2 * (1 + ∑ x₀ ∈ t, (N x₀ : ℝ))), ∑ x₀ ∈ t, |C x₀|, by positivity, ?_⟩
  intro x hx v hv hv0
  obtain ⟨x₀, hx₀t, hxV⟩ : ∃ x₀ ∈ t, x ∈ V x₀ := by simpa using ht.2 (Set.mem_univ x)
  have hz : R.lift x x ∈ ptsOver ℂ (mCoordIdeal y) :=
    mem_ptsOver_of_mem_mcPts (R.mem x x (R.mem_U x))
  obtain ⟨hHf, hbd⟩ := hb x₀ x hxV
  have hrep := (GlobalTheory.T.multihomogeneous_value_well_defined K ι Ω y ℂ Eh.a ε (R.lift x x) v hz hv).1 _ _ _ _
    (hG x₀) (hH x₀) (hd x₀) (hy x₀)
  have hGne : aeval (R.lift x x) (G x₀) ≠ (0 : ℂ) := by
    rw [hrep]; exact mul_ne_zero hv0 hHf
  have hbd' := hbd hx hGne
  have hval : (aeval (R.lift x x) (G x₀) : ℂ) / aeval (R.lift x x) (Hf x₀) = v := by
    rw [hrep]; exact mul_div_cancel_right₀ v hHf
  rw [hval] at hbd'
  have hr : 0 ≤ rW S.L S.s (π x) := by
    have h0 := S.norm_le (π x)
    have h1 : 0 < Real.exp 1 := Real.exp_pos 1
    unfold rW
    linarith
  have hNpos : (0 : ℝ) < N x₀ := by exact_mod_cast hN x₀
  have hsum : (N x₀ : ℝ) ≤ ∑ a ∈ t, (N a : ℝ) :=
    Finset.single_le_sum (f := fun a => (N a : ℝ)) (fun a _ => Nat.cast_nonneg _) hx₀t
  have hδ : 1 / (2 * (1 + ∑ a ∈ t, (N a : ℝ))) ≤ 1 / (2 * (N x₀ : ℝ)) := by
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  have hC : C x₀ ≤ ∑ a ∈ t, |C a| :=
    (le_abs_self _).trans
      (Finset.single_le_sum (f := fun a => |C a|) (fun a _ => abs_nonneg _) hx₀t)
  have hmul := mul_le_mul_of_nonneg_right hδ hr
  linarith

end GlobalTheory.CompanionTheory.Ar.Small.GlobDecay
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalMultihomogQuotientExistsStatement
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Small.Fund

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_multihomog_quotient_exists : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (J : Ideal (MRing ι)) (e : ℕ) (R : AnLogRes (mCoordIdeal y) J e) (σ : Type) (S : PB.AnSys e σ) (π : R.X → S.X), HoloMap R.A S.A π → ∀ (Eh : HermLine ι), IsSmoothHerm Eh → ∀ ε : Ω, (∀ x : R.X, ∃ (dg dh : K → ℕ) (G Hf : MRing ι), IsMultiHomog G dg ∧ IsMultiHomog Hf dh ∧ (∀ k, (dg k : ℤ) = dh k + Eh.a k) ∧ aeval y G = ε * aeval y Hf ∧ aeval (R.lift x x) Hf ≠ (0 : ℂ)) → (∀ (x : R.X) (dg dh : K → ℕ) (G Hf : MRing ι), IsMultiHomog G dg → IsMultiHomog Hf dh → (∀ k, (dg k : ℤ) = dh k + Eh.a k) → aeval y G = ε * aeval y Hf → aeval (R.lift x x) G ≠ (0 : ℂ) → aeval (R.lift x x) Hf ≠ (0 : ℂ) → π x ∈ S.open') → ∃ δ C : ℝ, 0 < δ ∧ ∀ x : R.X, π x ∈ S.open' → ∀ v : ℂ, HasVal y Eh.a ε (R.lift x x) v → v ≠ 0 → Real.log ‖v‖ - Real.log (Eh.h (R.lift x x)) ≤ -δ * rW S.L S.s (π x) + C := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Small.GlobDecay.global_decay | exact GlobalTheory.CompanionTheory.Ar.Small.GlobDecay.global_decay | (intros; apply GlobalTheory.CompanionTheory.Ar.Small.GlobDecay.global_decay <;> assumption)
end
