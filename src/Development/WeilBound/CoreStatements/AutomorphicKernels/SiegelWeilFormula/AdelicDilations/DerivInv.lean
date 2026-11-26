module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.FourierZero
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.SigmaSigmaOfGood

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AutomorphicFunctionalHolomorphicDerivative
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AutomorphicFunctionalHolomorphicDerivative
open Topology Filter

namespace GlobalTheory.CompanionTheory.HolFamily

theorem continuousOn_deriv_param {G : Type} [TopologicalSpace G] {U : Set ℂ} (hU : IsOpen U)
    {E : ℂ → G → ℂ} (hd : ∀ g, DifferentiableOn ℂ (E · g) U)
    (hc : ContinuousOn (fun y : ℂ × G => E y.1 y.2) (U ×ˢ Set.univ)) :
    ContinuousOn (fun y : ℂ × G => deriv (E · y.2) y.1) (U ×ˢ Set.univ) := by
  have hc' : ContinuousOn (fun q : G × ℂ => E q.2 q.1) (Set.univ ×ˢ U) :=
    hc.comp continuous_swap.continuousOn fun q hq => ⟨hq.2, Set.mem_univ _⟩
  have h := continuousOn_deriv_family G U hU (fun g z => E z g) hc' hd
  exact h.comp continuous_swap.continuousOn fun y hy => ⟨Set.mem_univ _, hy.1⟩

theorem deriv_param_invariant {G : Type} [Group G] (Γ : Subgroup G) {U : Set ℂ} (hU : IsOpen U)
    {E : ℂ → G → ℂ} (hinv : ∀ z ∈ U, ∀ γ ∈ Γ, ∀ g, E z (γ * g) = E z g) :
    ∀ z ∈ U, ∀ γ ∈ Γ, ∀ g, deriv (E · (γ * g)) z = deriv (E · g) z := by
  intro z hz γ hγ g
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [hU.mem_nhds hz] with w hw using hinv w hw γ hγ g

theorem hasDerivAt_functional {G : Type} [Group G] [TopologicalSpace G] (Γ : Subgroup G)
    (Lf : (G → ℂ) → ℂ)
    (hlin : ∀ (a : ℂ) (f f' : G → ℂ), Continuous f → Continuous f' →
      (∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) → (∀ γ ∈ Γ, ∀ g, f' (γ * g) = f' g) →
      Lf (a • f + f') = a * Lf f + Lf f')
    {C : Set G} (hC : IsCompact C)
    (hb : ∀ (f : G → ℂ) (M : ℝ), Continuous f → (∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) →
      (∀ x ∈ C, ‖f x‖ ≤ M) → ‖Lf f‖ ≤ M)
    {U : Set ℂ} {E : ℂ → G → ℂ} (hU : IsOpen U) (hd : ∀ g, DifferentiableOn ℂ (E · g) U)
    (hc : ContinuousOn (fun y : ℂ × G => E y.1 y.2) (U ×ˢ Set.univ))
    (hinv : ∀ z ∈ U, ∀ γ ∈ Γ, ∀ g, E z (γ * g) = E z g) {z : ℂ} (hz : z ∈ U) :
    HasDerivAt (fun w => Lf (E w)) (Lf fun g => deriv (E · g) z) z := by
  obtain ⟨D, hD⟩ : ∃ D : G → ℂ, D = fun g => deriv (E · g) z := ⟨_, rfl⟩
  rw [← hD]
  have hD' := continuousOn_deriv_param hU hd hc
  have hslice : ∀ w ∈ U, Continuous (E w) := fun w hw =>
    hc.comp_continuous (continuous_const.prodMk continuous_id) fun _ => ⟨hw, Set.mem_univ _⟩
  have hDc : Continuous D := by
    rw [hD]
    exact hD'.comp_continuous (continuous_const.prodMk continuous_id) fun _ => ⟨hz, Set.mem_univ _⟩
  have hDinv : ∀ γ ∈ Γ, ∀ g, D (γ * g) = D g := by
    rw [hD]
    intro γ hγ g
    exact deriv_param_invariant Γ hU hinv z hz γ hγ g
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hcpos
  have hunif : ∀ᶠ ζ in 𝓝 z, ∀ g ∈ C, ‖deriv (E · g) ζ - deriv (E · g) z‖ ≤ c := by
    apply hC.eventually_forall_of_forall_eventually
    intro g _
    have hcont : ContinuousAt (fun y : ℂ × G => deriv (E · y.2) y.1) (z, g) :=
      hD'.continuousAt ((hU.prod isOpen_univ).mem_nhds ⟨hz, Set.mem_univ _⟩)
    have hcont2 : ContinuousAt (fun y : ℂ × G => deriv (E · y.2) z) (z, g) :=
      hcont.comp_of_eq (continuous_const.prodMk continuous_snd).continuousAt rfl
    have h1 := Metric.tendsto_nhds.mp hcont (c / 2) (by positivity)
    have h2 := Metric.tendsto_nhds.mp hcont2 (c / 2) (by positivity)
    filter_upwards [h1, h2] with y hy1 hy2
    rw [dist_eq_norm] at hy1 hy2
    calc ‖deriv (E · y.2) y.1 - deriv (E · y.2) z‖
        = ‖(deriv (E · y.2) y.1 - deriv (E · g) z) - (deriv (E · y.2) z - deriv (E · g) z)‖ := by
          congr 1
          ring
      _ ≤ ‖deriv (E · y.2) y.1 - deriv (E · g) z‖ + ‖deriv (E · y.2) z - deriv (E · g) z‖ :=
          norm_sub_le _ _
      _ ≤ c := by linarith
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.mp (hunif.and (hU.mem_nhds hz))
  filter_upwards [Metric.ball_mem_nhds z hδ] with w hw
  have hwU : w ∈ U := (hball w hw).2
  have hbound : ∀ g ∈ C, ‖E w g - E z g - (w - z) * D g‖ ≤ c * ‖w - z‖ := by
    intro g hg
    rw [hD]
    have hφ : ∀ ζ ∈ Metric.ball z δ, HasDerivAt (fun ζ => E ζ g - ζ * deriv (E · g) z)
        (deriv (E · g) ζ - 1 * deriv (E · g) z) ζ := by
      intro ζ hζ
      have hdiff : DifferentiableAt ℂ (E · g) ζ := (hd g).differentiableAt (hU.mem_nhds (hball ζ hζ).2)
      exact hdiff.hasDerivAt.sub ((hasDerivAt_id ζ).mul_const _)
    have hmv := Convex.norm_image_sub_le_of_norm_deriv_le (fun ζ hζ => (hφ ζ hζ).differentiableAt)
      (fun ζ hζ => by rw [(hφ ζ hζ).deriv, one_mul]; exact (hball ζ hζ).1 g hg)
      (convex_ball z δ) (Metric.mem_ball_self hδ) hw
    calc ‖E w g - E z g - (w - z) * deriv (E · g) z‖
        = ‖(E w g - w * deriv (E · g) z) - (E z g - z * deriv (E · g) z)‖ := by
          congr 1
          ring
      _ ≤ c * ‖w - z‖ := hmv
  have hEw := hslice w hwU
  have hEz := hslice z hz
  set F : G → ℂ := fun g => E w g - E z g - (w - z) * D g with hF
  have hFc : Continuous F := (hEw.sub hEz).sub (continuous_const.mul hDc)
  have hFi : ∀ γ ∈ Γ, ∀ g, F (γ * g) = F g := by
    intro γ hγ g
    simp only [hF, hinv w hwU γ hγ g, hinv z hz γ hγ g, hDinv γ hγ g]
  have hGc : Continuous ((w - z) • D + E z) := (hDc.const_smul _).add hEz
  have hGi : ∀ γ ∈ Γ, ∀ g, ((w - z) • D + E z) (γ * g) = ((w - z) • D + E z) g := by
    intro γ hγ g
    simp only [Pi.add_apply, Pi.smul_apply, hDinv γ hγ g, hinv z hz γ hγ g]
  have hsplit : E w = (1 : ℂ) • F + ((w - z) • D + E z) := by
    funext g
    simp only [hF, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have h1 := hlin 1 F ((w - z) • D + E z) hFc hGc hFi hGi
  have h2 := hlin (w - z) D (E z) hDc hEz hDinv (hinv z hz)
  have hLF : ‖Lf F‖ ≤ c * ‖w - z‖ := hb F _ hFc hFi hbound
  rw [hsplit, h1, h2, smul_eq_mul]
  have hring : 1 * Lf F + ((w - z) * Lf D + Lf (E z)) - Lf (E z) - (w - z) * Lf D = Lf F := by ring
  rw [hring]
  exact hLF

theorem iteratedDeriv_functional {G : Type} [Group G] [TopologicalSpace G] (Γ : Subgroup G)
    (Lf : (G → ℂ) → ℂ)
    (hlin : ∀ (a : ℂ) (f f' : G → ℂ), Continuous f → Continuous f' →
      (∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) → (∀ γ ∈ Γ, ∀ g, f' (γ * g) = f' g) →
      Lf (a • f + f') = a * Lf f + Lf f')
    {C : Set G} (hC : IsCompact C)
    (hb : ∀ (f : G → ℂ) (M : ℝ), Continuous f → (∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) →
      (∀ x ∈ C, ‖f x‖ ≤ M) → ‖Lf f‖ ≤ M)
    {U : Set ℂ} (hU : IsOpen U) (j : ℕ) :
    ∀ E : ℂ → G → ℂ, (∀ g, DifferentiableOn ℂ (E · g) U) →
      ContinuousOn (fun y : ℂ × G => E y.1 y.2) (U ×ˢ Set.univ) →
      (∀ z ∈ U, ∀ γ ∈ Γ, ∀ g, E z (γ * g) = E z g) →
      ∀ z ∈ U, iteratedDeriv j (fun z => Lf (E z)) z = Lf fun g => iteratedDeriv j (E · g) z := by
  induction j with
  | zero =>
    intro E _ _ _ z _
    simp
  | succ j ih =>
    intro E hd hc hinv z hz
    have key := ih (fun z g => deriv (E · g) z) (fun g => (hd g).deriv hU)
      (continuousOn_deriv_param hU hd hc) (deriv_param_invariant Γ hU hinv) z hz
    have hloc : deriv (fun z => Lf (E z)) =ᶠ[𝓝 z] fun z => Lf (fun g => deriv (E · g) z) := by
      filter_upwards [hU.mem_nhds hz] with w hw
      exact (hasDerivAt_functional Γ Lf hlin hC hb hU hd hc hinv hw).deriv
    rw [iteratedDeriv_succ', Filter.EventuallyEq.iteratedDeriv_eq j hloc, key]
    congr 1
    funext g
    rw [iteratedDeriv_succ']

theorem functional_commutes_iteratedDeriv :
    ∀ {G : Type} [Group G] [TopologicalSpace G] (Γ : Subgroup G) (Lf : (G → ℂ) → ℂ), (∀ (a : ℂ) (f f' : G → ℂ), Continuous f → Continuous f' → (∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) → (∀ γ ∈ Γ, ∀ g, f' (γ * g) = f' g) → Lf (a • f + f') = a * Lf f + Lf f') → (∃ C : Set G, IsCompact C ∧ ∀ (f : G → ℂ) (M : ℝ), Continuous f → (∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) → (∀ x ∈ C, ‖f x‖ ≤ M) → ‖Lf f‖ ≤ M) → ∀ (U : Set ℂ) (Ê : ℂ → G → ℂ), IsOpen U → (∀ g, DifferentiableOn ℂ (Ê · g) U) → ContinuousOn (fun y : ℂ × G => Ê y.1 y.2) (U ×ˢ Set.univ) → (∀ z ∈ U, ∀ γ ∈ Γ, ∀ g, Ê z (γ * g) = Ê z g) → DifferentiableOn ℂ (fun z => Lf (Ê z)) U ∧ ∀ z ∈ U, ∀ j : ℕ, iteratedDeriv j (fun z => Lf (Ê z)) z = Lf fun g => iteratedDeriv j (Ê · g) z := by
  intro G _ _ Γ Lf hlin hCex U Ê hU hd hc hinv
  obtain ⟨C, hC, hb⟩ := hCex
  exact ⟨fun z hz => (hasDerivAt_functional Γ Lf hlin hC hb hU hd hc hinv hz).differentiableAt.differentiableWithinAt,
    fun z hz j => iteratedDeriv_functional Γ Lf hlin hC hb hU j Ê hd hc hinv z hz⟩

end GlobalTheory.CompanionTheory.HolFamily
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AutomorphicFunctionalHolomorphicDerivativeStatement
open Topology Filter
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.automorphic_functional_holomorphic_derivative : ∀ {G : Type} [Group G] [TopologicalSpace G] (Γ : Subgroup G) (Lf : (G → ℂ) → ℂ), (∀ (a : ℂ) (f f' : G → ℂ), Continuous f → Continuous f' → (∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) → (∀ γ ∈ Γ, ∀ g, f' (γ * g) = f' g) → Lf (a • f + f') = a * Lf f + Lf f') → (∃ C : Set G, IsCompact C ∧ ∀ (f : G → ℂ) (M : ℝ), Continuous f → (∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) → (∀ x ∈ C, ‖f x‖ ≤ M) → ‖Lf f‖ ≤ M) → ∀ (U : Set ℂ) (Ê : ℂ → G → ℂ), IsOpen U → (∀ g, DifferentiableOn ℂ (Ê · g) U) → ContinuousOn (fun y : ℂ × G => Ê y.1 y.2) (U ×ˢ Set.univ) → (∀ z ∈ U, ∀ γ ∈ Γ, ∀ g, Ê z (γ * g) = Ê z g) → DifferentiableOn ℂ (fun z => Lf (Ê z)) U ∧ ∀ z ∈ U, ∀ j : ℕ, iteratedDeriv j (fun z => Lf (Ê z)) z = Lf fun g => iteratedDeriv j (Ê · g) z := by
  first | exact @GlobalTheory.CompanionTheory.HolFamily.functional_commutes_iteratedDeriv | exact GlobalTheory.CompanionTheory.HolFamily.functional_commutes_iteratedDeriv | (intros; apply GlobalTheory.CompanionTheory.HolFamily.functional_commutes_iteratedDeriv <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousIteratedDerivHolomorphicFamily
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousIteratedDerivHolomorphicFamily
open Topology Filter

namespace GlobalTheory.CompanionTheory.HolFamily

theorem continuous_iteratedDeriv_family :
    ∀ {G : Type} [TopologicalSpace G] (U : Set ℂ) (Ê : ℂ → G → ℂ), IsOpen U →
      (∀ g, DifferentiableOn ℂ (Ê · g) U) →
      ContinuousOn (fun y : ℂ × G => Ê y.1 y.2) (U ×ˢ Set.univ) →
      ∀ z ∈ U, ∀ j : ℕ, Continuous fun g => iteratedDeriv j (Ê · g) z := by
  intro G _ U E hU hd hc z hz j
  obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.1 hU z hz
  have hr : 0 < R / 2 := by positivity
  have hcl : Metric.closedBall z (R / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  rw [continuous_iff_continuousAt]
  intro g0
  rw [Metric.continuousAt_iff']
  intro ε hε
  have hfac : (0 : ℝ) < (j.factorial : ℝ) := by exact_mod_cast j.factorial_pos
  have hrj : 0 < (R / 2) ^ j := pow_pos hr j
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = ε * (R / 2) ^ j / (2 * (j.factorial : ℝ)) := ⟨_, rfl⟩
  have hδ : 0 < δ := by rw [hδdef]; positivity
  have htube : ∀ᶠ g in 𝓝 g0, ∀ w ∈ Metric.sphere z (R / 2), ‖E w g - E w g0‖ < δ := by
    refine (isCompact_sphere z (R / 2)).eventually_forall_of_forall_eventually
      (P := fun g w => ‖E w g - E w g0‖ < δ) ?_
    intro w hw
    have hwU : w ∈ U := hcl (Metric.sphere_subset_closedBall hw)
    have hcont : ContinuousAt (fun y : ℂ × G => E y.1 y.2) (w, g0) :=
      hc.continuousAt ((hU.prod isOpen_univ).mem_nhds ⟨hwU, trivial⟩)
    have hA : ContinuousAt (fun p : G × ℂ => E p.2 p.1) (g0, w) :=
      ContinuousAt.comp (f := fun p : G × ℂ => (p.2, p.1))
        (g := fun y : ℂ × G => E y.1 y.2) hcont continuous_swap.continuousAt
    have hB : ContinuousAt (fun p : G × ℂ => E p.2 g0) (g0, w) :=
      ContinuousAt.comp (f := fun p : G × ℂ => (p.2, g0))
        (g := fun y : ℂ × G => E y.1 y.2) hcont (by fun_prop)
    have hN : ContinuousAt (fun p : G × ℂ => ‖E p.2 p.1 - E p.2 g0‖) (g0, w) := (hA.sub hB).norm
    have hlt : ‖E w g0 - E w g0‖ < δ := by simpa using hδ
    exact hN.eventually_lt continuousAt_const hlt
  filter_upwards [htube] with g hg
  have hzn : U ∈ 𝓝 z := hU.mem_nhds hz
  have h1 : ContDiffAt ℂ j (E · g) z := ((hd g).analyticAt hzn).contDiffAt
  have h2 : ContDiffAt ℂ j (E · g0) z := ((hd g0).analyticAt hzn).contDiffAt
  rw [dist_eq_norm, ← iteratedDeriv_fun_sub h1 h2]
  have hdc : DiffContOnCl ℂ (fun x => E x g - E x g0) (Metric.ball z (R / 2)) :=
    ((hd g).sub (hd g0)).diffContOnCl_ball hcl
  have hb := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (C := δ) j hr hdc
    (fun w hw => (hg w hw).le)
  refine hb.trans_lt ?_
  have : (j.factorial : ℝ) * δ / (R / 2) ^ j = ε / 2 := by
    rw [hδdef]; field_simp
  rw [this]
  linarith

end GlobalTheory.CompanionTheory.HolFamily
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousIteratedDerivHolomorphicFamilyStatement
open Topology Filter
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_iteratedDeriv_holomorphic_family : ∀ {G : Type} [TopologicalSpace G] (U : Set ℂ) (Ê : ℂ → G → ℂ), IsOpen U → (∀ g, DifferentiableOn ℂ (Ê · g) U) → ContinuousOn (fun y : ℂ × G => Ê y.1 y.2) (U ×ˢ Set.univ) → ∀ z ∈ U, ∀ j : ℕ, Continuous fun g => iteratedDeriv j (Ê · g) z := by
  first | exact @GlobalTheory.CompanionTheory.HolFamily.continuous_iteratedDeriv_family | exact GlobalTheory.CompanionTheory.HolFamily.continuous_iteratedDeriv_family | (intros; apply GlobalTheory.CompanionTheory.HolFamily.continuous_iteratedDeriv_family <;> assumption)
end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.IsExtAtOfDiff
noncomputable section

open Filter Topology GlobalTheory.Cont

namespace PositivityTheory.SiegelWeilFormula.AStep

theorem iterDerivPow (k : ℕ) : ∀ (f g : ℂ → ℂ) (s₀ : ℂ), AnalyticAt ℂ g s₀ → (f =ᶠ[𝓝 s₀] fun z => (z - s₀) ^ k * g z) →
    (∀ i < k, iteratedDeriv i f s₀ = 0) ∧ iteratedDeriv k f s₀ = (k.factorial : ℂ) * g s₀ := by
  induction k with
  | zero =>
    intro f g s₀ _ hf
    refine ⟨fun i hi => absurd hi (Nat.not_lt_zero _), ?_⟩
    simp [iteratedDeriv_zero, hf.self_of_nhds]
  | succ k ih =>
    intro f g s₀ hg hf
    set h : ℂ → ℂ := fun z => ((k : ℂ) + 1) * g z + (z - s₀) * deriv g z with hh
    have hha : AnalyticAt ℂ h s₀ := by
      have := hg.deriv
      simp only [hh]; fun_prop
    have hdf : deriv f =ᶠ[𝓝 s₀] fun z => (z - s₀) ^ k * h z := by
      refine hf.deriv.trans ?_
      filter_upwards [hg.eventually_analyticAt] with z hz
      have hd : HasDerivAt (fun z => (z - s₀) ^ (k + 1) * g z)
          (((k + 1 : ℕ) : ℂ) * (z - s₀) ^ k * 1 * g z + (z - s₀) ^ (k + 1) * deriv g z) z :=
        (((hasDerivAt_id z).sub_const s₀).pow (k + 1)).mul hz.differentiableAt.hasDerivAt
      rw [hd.deriv, hh]; push_cast; ring
    obtain ⟨ih1, ih2⟩ := ih (deriv f) h s₀ hha hdf
    refine ⟨fun i hi => ?_, ?_⟩
    · rcases i with _ | i
      · simp [iteratedDeriv_zero, hf.self_of_nhds]
      · rw [iteratedDeriv_succ']; exact ih1 i (by omega)
    · rw [iteratedDeriv_succ', ih2, hh, Nat.factorial_succ]; push_cast; simp; ring

theorem polyFac (p : Polynomial ℂ) (s₀ : ℂ) :
    ∃ q : Polynomial ℂ, (∀ z, p.eval z = (z - s₀) ^ p.rootMultiplicity s₀ * q.eval z) ∧ (p ≠ 0 → q.eval s₀ ≠ 0) := by
  refine ⟨p /ₘ (Polynomial.X - Polynomial.C s₀) ^ p.rootMultiplicity s₀, fun z => ?_,
    fun hp => Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero s₀ hp⟩
  conv_lhs => rw [← p.pow_mul_divByMonic_rootMultiplicity_eq s₀]
  simp

theorem eqNhds {f g : ℂ → ℂ} {x : ℂ} (h : f =ᶠ[𝓝[≠] x] g) (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    f =ᶠ[𝓝 x] g := by
  have hx : f x = g x :=
    tendsto_nhds_unique (hf.tendsto.mono_left nhdsWithin_le_nhds) ((hg.tendsto.mono_left nhdsWithin_le_nhds).congr' h.symm)
  filter_upwards [eventually_nhdsWithin_iff.mp h] with z hz
  by_cases e : z = x
  · subst e; exact hx
  · exact hz e

theorem isExtAt_of_diff {U : Set ℂ} {e φ : ℂ → ℂ} {t : ℝ} {s₀ : ℂ} (hU : IsOpen U) (hR : IsRightDomain U) (hs : s₀ ∈ U)
    (he : DifferentiableOn ℂ e U) (heq : ∀ z : ℂ, t < z.re → e z = φ z) : IsExtAt φ s₀ e :=
  ⟨U, hs, hR, fun z hz => ((he.analyticOnNhd hU) z hz).meromorphicAt, t, fun z hz => heq z hz⟩

theorem isExtAt_entire {f : ℂ → ℂ} (hf : Differentiable ℂ f) (s₀ : ℂ) : IsExtAt f s₀ f :=
  (isMerExt_self isRightDomain_univ fun z _ => (hf.analyticAt z).meromorphicAt).isExtAt trivial

theorem pderiv_lt (p : Polynomial ℂ) (s₀ : ℂ) (j : ℕ) (hj : j < p.rootMultiplicity s₀) :
    iteratedDeriv j (fun z => p.eval z) s₀ = 0 := by
  obtain ⟨q, hq, -⟩ := polyFac p s₀
  exact (iterDerivPow _ _ (fun z => q.eval z) s₀ (q.differentiable.analyticAt s₀)
    (Eventually.of_forall hq)).1 j hj

theorem ordVal (U : Set ℂ) (p : Polynomial ℂ) (e h : ℂ → ℂ) (t : ℝ) (s₀ c : ℂ) (hU : IsOpen U) (hR : IsRightDomain U)
    (hs : s₀ ∈ U) (hp : p ≠ 0) (he : DifferentiableOn ℂ e U) (heq : ∀ z : ℂ, t < z.re → e z = p.eval z * h z)
    (hv : HolValueAt h s₀ c) : ∀ j ≤ p.rootMultiplicity s₀, iteratedDeriv j e s₀ = iteratedDeriv j (fun z => p.eval z) s₀ * c := by
  obtain ⟨H, hH, hHa, hHc⟩ := hv
  obtain ⟨q, hq, -⟩ := polyFac p s₀
  set k := p.rootMultiplicity s₀
  have hE : IsExtAt (fun z => p.eval z * h z) s₀ e := isExtAt_of_diff hU hR hs he heq
  have hP : IsExtAt (fun z => p.eval z * h z) s₀ (fun z => p.eval z * H z) := (isExtAt_entire p.differentiable s₀).mul hH
  have hea : AnalyticAt ℂ e s₀ := (he.analyticOnNhd hU) s₀ hs
  have hPa : AnalyticAt ℂ (fun z => p.eval z * H z) s₀ := (p.differentiable.analyticAt s₀).mul hHa
  have h1 : e =ᶠ[𝓝 s₀] fun z => (z - s₀) ^ k * (q.eval z * H z) := by
    refine (eqNhds (hE.eventuallyEq hP) hea.continuousAt hPa.continuousAt).trans (Eventually.of_forall fun z => ?_)
    simp only [hq z]; ring
  have A := iterDerivPow k e _ s₀ ((q.differentiable.analyticAt s₀).mul hHa) h1
  have B := iterDerivPow k _ (fun z => q.eval z) s₀ (q.differentiable.analyticAt s₀) (Eventually.of_forall hq)
  intro j hj
  rcases hj.lt_or_eq with hj | hj
  · rw [A.1 j hj, B.1 j hj, zero_mul]
  · subst hj; rw [A.2, B.2, Pi.mul_apply, hHc]; ring

theorem wrap (U : Set ℂ) (p : Polynomial ℂ) (e h : ℂ → ℂ) (t : ℝ) (s₀ c : ℂ) (hU : IsOpen U) (hR : IsRightDomain U)
    (hs : s₀ ∈ U) (hp : p ≠ 0) (he : DifferentiableOn ℂ e U) (heq : ∀ z : ℂ, t < z.re → e z = p.eval z * h z)
    (hlow : ∀ j < p.rootMultiplicity s₀, iteratedDeriv j e s₀ = 0)
    (htop : iteratedDeriv (p.rootMultiplicity s₀) e s₀ =
      iteratedDeriv (p.rootMultiplicity s₀) (fun z => p.eval z) s₀ * c) : HolValueAt h s₀ c := by
  obtain ⟨q, hq, hq0⟩ := polyFac p s₀
  have hq0 := hq0 hp
  set k := p.rootMultiplicity s₀
  have hea : AnalyticAt ℂ e s₀ := (he.analyticOnNhd hU) s₀ hs
  obtain ⟨g, hg, hge⟩ := (natCast_le_analyticOrderAt hea).1 ((natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hea).2 hlow)
  have hge' : e =ᶠ[𝓝 s₀] fun z => (z - s₀) ^ k * g z := hge.mono fun z hz => by rw [hz, smul_eq_mul]
  have A := (iterDerivPow k e g s₀ hg hge').2
  have B := (iterDerivPow k _ (fun z => q.eval z) s₀ (q.differentiable.analyticAt s₀) (Eventually.of_forall hq)).2
  have hgc : g s₀ = q.eval s₀ * c := by
    rw [A, B] at htop
    have hf : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    apply mul_left_cancel₀ hf; rw [htop]; ring

  have hE : IsExtAt (fun z => p.eval z * h z) s₀ e := isExtAt_of_diff hU hR hs he heq
  have hD : IsExtAt (fun z => p.eval z * h z / p.eval z) s₀ (fun z => e z / p.eval z) :=
    hE.div (isExtAt_entire p.differentiable s₀)
  obtain ⟨σ, hσ⟩ := ((Polynomial.finite_setOfPred_isRoot hp).image Complex.re).bddAbove
  have hR' : EqRight (fun z => p.eval z * h z / p.eval z) h := by
    refine ⟨σ, fun z hz => ?_⟩
    have hpz : p.eval z ≠ 0 := fun h0 => by
      have := hσ ⟨z, h0, rfl⟩
      exact absurd (mem_rightOf.1 hz) (not_lt.2 this)
    exact mul_div_cancel_left₀ (h z) hpz
  refine (hD.congr hR').holValueAt_iff.2 ?_
  have hlim : Tendsto (fun z => g z / q.eval z) (𝓝[≠] s₀) (𝓝 c) := by
    have : ContinuousAt (fun z => g z / q.eval z) s₀ :=
      hg.continuousAt.div (q.differentiable.analyticAt s₀).continuousAt hq0
    have hv : g s₀ / q.eval s₀ = c := by rw [hgc]; field_simp
    rw [← hv]; exact this.tendsto.mono_left nhdsWithin_le_nhds
  refine hlim.congr' ?_
  filter_upwards [nhdsWithin_le_nhds hge', self_mem_nhdsWithin] with z hz hz'
  have hne : (z - s₀) ^ k ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hz')
  rw [hz, hq z, mul_div_mul_left _ _ hne]

theorem valLaw (h h' : ℂ → ℂ) (t : ℝ) (α β s₀ v v' : ℂ) (hl : ∀ z : ℂ, t < z.re → h' z = Complex.exp (α + β * z) * h z)
    (hv : HolValueAt h s₀ v) (hv' : HolValueAt h' s₀ v') : v' = Complex.exp (α + β * s₀) * v := by
  have hx : Differentiable ℂ fun z => Complex.exp (α + β * z) := by fun_prop
  have h1 : HolValueAt (fun z => Complex.exp (α + β * z)) s₀ (Complex.exp (α + β * s₀)) :=
    ⟨_, isExtAt_entire hx s₀, hx.analyticAt s₀, rfl⟩
  have h2 := (h1.mul hv).congr ⟨t, fun z hz => (hl z hz).symm⟩
  exact hv'.unique h2

theorem lawSep (U : Set ℂ) (p : Polynomial ℂ) (t : ℝ) (s₀ : ℂ) (j : ℕ) (a a' c₁ c₁' c₂ c₂' : ℂ → ℂ) (v v' α β : ℂ)
    (hU : IsOpen U) (hR : IsRightDomain U) (hs : s₀ ∈ U) (hp : p ≠ 0) (hj : j ≤ p.rootMultiplicity s₀)
    (ha : DifferentiableOn ℂ a U) (ha' : DifferentiableOn ℂ a' U)
    (hlo : ∀ i < j, iteratedDeriv i a s₀ = 0) (hlo' : ∀ i < j, iteratedDeriv i a' s₀ = 0)
    (he : ∀ z : ℂ, t < z.re → a z = p.eval z * (c₁ z + c₂ z)) (he' : ∀ z : ℂ, t < z.re → a' z = p.eval z * (c₁' z + c₂' z))
    (hv : HolValueAt c₁ s₀ v) (hv' : HolValueAt c₁' s₀ v')
    (hl : ∀ z : ℂ, t < z.re → c₂' z = Complex.exp (α + β * z) * c₂ z) :
    iteratedDeriv j a' s₀ - iteratedDeriv j (fun z => p.eval z) s₀ * v' =
      Complex.exp (α + β * s₀) * (iteratedDeriv j a s₀ - iteratedDeriv j (fun z => p.eval z) s₀ * v) := by
  obtain ⟨C, hC, hCa, hCv⟩ := hv
  obtain ⟨C', hC', hCa', hCv'⟩ := hv'
  obtain ⟨q, hq, -⟩ := polyFac p s₀
  set k := p.rootMultiplicity s₀
  set E : ℂ → ℂ := fun z => Complex.exp (α + β * z) with hEdef
  have hEd : Differentiable ℂ E := by simp only [hEdef]; fun_prop

  set gp : ℂ → ℂ := fun z => (z - s₀) ^ (k - j) * q.eval z with hgp
  have hgpa : AnalyticAt ℂ gp s₀ := by
    have := q.differentiable.analyticAt s₀
    simp only [hgp]; fun_prop
  have hpj : ∀ z, p.eval z = (z - s₀) ^ j * gp z := fun z => by
    rw [hq z, hgp]; simp only; rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hj]
  have hP := (iterDerivPow j _ gp s₀ hgpa (Eventually.of_forall hpj)).2

  have haa : AnalyticAt ℂ a s₀ := (ha.analyticOnNhd hU) s₀ hs
  have haa' : AnalyticAt ℂ a' s₀ := (ha'.analyticOnNhd hU) s₀ hs
  obtain ⟨ga, hga, hgae⟩ := (natCast_le_analyticOrderAt haa).1 ((natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero haa).2 hlo)
  obtain ⟨ga', hga', hgae'⟩ :=
    (natCast_le_analyticOrderAt haa').1 ((natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero haa').2 hlo')
  simp only [smul_eq_mul] at hgae hgae'
  have hA := (iterDerivPow j a ga s₀ hga hgae).2
  have hA' := (iterDerivPow j a' ga' s₀ hga' hgae').2

  have hX : IsExtAt (fun z => p.eval z * (c₁ z + c₂ z) - p.eval z * c₁ z) s₀ (fun z => a z - p.eval z * C z) :=
    (isExtAt_of_diff hU hR hs ha he).map₂ (· - ·) (fun _ => .fun_sub) ((isExtAt_entire p.differentiable s₀).mul hC)
  have hX' : IsExtAt (fun z => p.eval z * (c₁' z + c₂' z) - p.eval z * c₁' z) s₀ (fun z => a' z - p.eval z * C' z) :=
    (isExtAt_of_diff hU hR hs ha' he').map₂ (· - ·) (fun _ => .fun_sub) ((isExtAt_entire p.differentiable s₀).mul hC')
  have hY : IsExtAt (fun z => E z * (p.eval z * (c₁ z + c₂ z) - p.eval z * c₁ z)) s₀
      (fun z => E z * (a z - p.eval z * C z)) := (isExtAt_entire hEd s₀).mul hX
  have hY' : IsExtAt (fun z => p.eval z * (c₁' z + c₂' z) - p.eval z * c₁' z) s₀ (fun z => E z * (a z - p.eval z * C z)) :=
    hY.congr ⟨t, fun z hz => by simp only [hEdef]; rw [hl z hz]; ring⟩
  have hev := hX'.eventuallyEq hY'

  set Φ : ℂ → ℂ := fun z => ga z - gp z * C z with hΦ
  set Φ' : ℂ → ℂ := fun z => ga' z - gp z * C' z with hΦ'
  have hΦa : AnalyticAt ℂ (fun z => E z * Φ z) s₀ := by
    have := hEd.analyticAt s₀
    simp only [hΦ]; fun_prop
  have hΦa' : AnalyticAt ℂ Φ' s₀ := by simp only [hΦ']; fun_prop
  have hlim : Φ' =ᶠ[𝓝[≠] s₀] fun z => E z * Φ z := by
    filter_upwards [hev, nhdsWithin_le_nhds hgae, nhdsWithin_le_nhds hgae', self_mem_nhdsWithin] with z h1 h2 h3 hz
    have hne : (z - s₀) ^ j ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hz)
    apply mul_left_cancel₀ hne
    have := h1; simp only [h2, h3, hpj z] at this
    simp only [hΦ, hΦ']; linear_combination this
  have hval : Φ' s₀ = E s₀ * Φ s₀ := (eqNhds hlim hΦa'.continuousAt hΦa.continuousAt).self_of_nhds
  simp only [hΦ, hΦ', hEdef, hCv, hCv'] at hval
  rw [hA, hA', hP]; linear_combination (j.factorial : ℂ) * hval

end PositivityTheory.SiegelWeilFormula.AStep

end
end

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.AStep

theorem famCont {G : Type} [TopologicalSpace G] (U : Set ℂ) (Ê : ℂ → G → ℂ) (hU : IsOpen U)
    (hd : ∀ g, DifferentiableOn ℂ (Ê · g) U) (hc : ContinuousOn (fun y : ℂ × G => Ê y.1 y.2) (U ×ˢ Set.univ)) :
    ∀ z ∈ U, ∀ j : ℕ, Continuous fun g => iteratedDeriv j (Ê · g) z :=
  GlobalTheory.T.continuous_iteratedDeriv_holomorphic_family U Ê hU hd hc

theorem lamDeriv {G : Type} [Group G] [TopologicalSpace G] (Γ : Subgroup G) (Lf : (G → ℂ) → ℂ)
    (hadd : ∀ (a : ℂ) (f f' : G → ℂ), Continuous f → Continuous f' → (∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) →
      (∀ γ ∈ Γ, ∀ g, f' (γ * g) = f' g) → Lf (a • f + f') = a * Lf f + Lf f')
    (hbd : ∃ C : Set G, IsCompact C ∧ ∀ (f : G → ℂ) (M : ℝ), Continuous f → (∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) →
      (∀ x ∈ C, ‖f x‖ ≤ M) → ‖Lf f‖ ≤ M)
    (U : Set ℂ) (Ê : ℂ → G → ℂ) (hU : IsOpen U) (hd : ∀ g, DifferentiableOn ℂ (Ê · g) U)
    (hc : ContinuousOn (fun y : ℂ × G => Ê y.1 y.2) (U ×ˢ Set.univ)) (hinv : ∀ z ∈ U, ∀ γ ∈ Γ, ∀ g, Ê z (γ * g) = Ê z g) :
    DifferentiableOn ℂ (fun z => Lf (Ê z)) U ∧
      ∀ z ∈ U, ∀ j : ℕ, iteratedDeriv j (fun z => Lf (Ê z)) z = Lf fun g => iteratedDeriv j (Ê · g) z :=
  GlobalTheory.T.automorphic_functional_holomorphic_derivative Γ Lf hadd hbd U Ê hU hd hc hinv

theorem derivInv {G : Type} [Mul G] (U : Set ℂ) (Ê : ℂ → G → ℂ) (hU : IsOpen U) (z : ℂ) (hz : z ∈ U) (γ g : G)
    (h : ∀ z ∈ U, Ê z (γ * g) = Ê z g) (j : ℕ) : iteratedDeriv j (Ê · (γ * g)) z = iteratedDeriv j (Ê · g) z := by
  have : (Ê · (γ * g)) =ᶠ[𝓝 z] (Ê · g) := Filter.eventually_of_mem (hU.mem_nhds hz) fun w hw => h w hw
  exact this.iteratedDeriv_eq j

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem nbRat (d : SD σ) {nb lam 𝓖} (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) :
    ∀ β ∈ nF σ d.Y d.b, nb β ∈ rat2 σ d.Y :=
  fun β hβ => kfour.nb_rat hc.1 β hβ

def Bj (d : SD σ) (Φ : d.Fn) (p : Polynomial ℂ) (Ê : ℂ → d.G → ℂ) (j : ℕ) (g : d.G) : ℂ :=
  iteratedDeriv j (Ê · g) (s0 d.m d.n) - iteratedDeriv j (fun z => p.eval z) (s0 d.m d.n) * (2 * d.I Φ g)

end PositivityTheory.SiegelWeilFormula.AStep

end
