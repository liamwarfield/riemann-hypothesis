module

public import GroundTheory.AutomorphicForms.HarishChandraRegularity.ExpHaar
public import GroundTheory.AutomorphicForms.HarishChandraRegularity.TupleOp
public import GroundTheory.AutomorphicForms.PartialDifferential.AnalyticHypoelliptic
public import GroundTheory.AutomorphicForms.HarishChandraRegularity.CartanBasis

@[expose] public section

section -- merged from GroundTheory.AutomorphicForms.PartialDifferential.EllipticParametrix
section -- merged from GroundTheory.AutomorphicForms.PartialDifferential.EllipticSolutions
namespace GroundTheory.Automorphic.Sobolev

open TemperedDistribution MeasureTheory FourierTransform LineDeriv
open scoped SchwartzMap ENNReal ContDiff

noncomputable section

variable {n : ℕ}

section Integrable

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

end Integrable

theorem integrable_smul_of_locallyIntegrableOn {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {Ω : Set E} {u : E → ℂ} (hu : LocallyIntegrableOn u Ω) {φ : 𝓢(E, ℂ)} (hφc : HasCompactSupport φ)
    (hφΩ : tsupport φ ⊆ Ω) : Integrable (fun x ↦ φ x • u x) := by
  have hK := (hu.mono_set hφΩ).integrableOn_isCompact hφc.isCompact
  have hind := hK.integrable_indicator (isClosed_tsupport _).measurableSet
  have h := hind.bdd_mul (c := SchwartzMap.seminorm ℝ 0 0 φ) φ.continuous.aestronglyMeasurable
    (ae_of_all _ fun x ↦ SchwartzMap.norm_le_seminorm ℝ _ _)
  refine h.congr (ae_of_all _ fun x ↦ ?_)
  simp only [smul_eq_mul]
  by_cases hx : x ∈ tsupport φ
  · rw [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hx, zero_mul, zero_mul]

end

end GroundTheory.Automorphic.Sobolev
end

namespace GroundTheory.Automorphic.Sobolev

open TemperedDistribution MeasureTheory FourierTransform LineDeriv
open scoped SchwartzMap ENNReal ContDiff

noncomputable section

set_option linter.unusedSectionVars false

section Helpers

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem smulLeftCLM_delta (θ : 𝓢(E, ℂ)) (x₀ : E) :
    smulLeftCLM ℂ (θ : E → ℂ) (TemperedDistribution.delta x₀ : 𝓢'(E, ℂ)) =
      θ x₀ • (TemperedDistribution.delta x₀ : 𝓢'(E, ℂ)) := by
  ext φ
  rw [smulLeftCLM_apply_apply, TemperedDistribution.delta_apply, smul_apply,
    TemperedDistribution.delta_apply, SchwartzMap.smulLeftCLM_apply_apply θ.hasTemperateGrowth]

theorem smulLeft_comm_eq {T : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)} (hT : IsLocal T) (θ : 𝓢(E, ℂ))
    {ψ ψ₁ : 𝓢(E, ℂ)} {V : Set E} (hV : IsOpen V) (hψ₁ : ∀ x ∈ V, ψ₁ x = 1)
    (hψ : tsupport (ψ : E → ℂ) ⊆ V) (u : 𝓢'(E, ℂ)) :
    smulLeftCLM ℂ (ψ : E → ℂ) (comm T θ u) =
      smulLeftCLM ℂ (ψ : E → ℂ) (comm T θ (smulLeftCLM ℂ (ψ₁ : E → ℂ) u)) := by
  have hz : Distribution.IsVanishingOn (u - smulLeftCLM ℂ (ψ₁ : E → ℂ) u) V := by
    have h2 := isVanishingOn_neg (isVanishingOn_smulLeftCLM_sub ψ₁.hasTemperateGrowth hψ₁ u)
    rwa [neg_sub] at h2
  have hc : Distribution.IsVanishingOn (comm T θ (u - smulLeftCLM ℂ (ψ₁ : E → ℂ) u)) V :=
    isLocal_comm hT θ V hV _ hz
  have h0 := smulLeftCLM_eq_zero_of_isVanishingOn ψ.hasTemperateGrowth hc hψ
  rw [map_sub, map_sub, sub_eq_zero] at h0
  exact h0

theorem pderiv_congr {n : ℕ} {α : Fin n → ℕ} {f f' : EuclideanSpace ℝ (Fin n) → ℂ}
    {x : EuclideanSpace ℝ (Fin n)} (h : f =ᶠ[nhds x] f') : pderiv α f x = pderiv α f' x := by
  rw [pderiv, pderiv, (h.iteratedFDeriv ℝ (mabs α)).eq_of_nhds]

end Helpers

section Comm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem memSobolev_zero_distribution (t : ℝ) : MemSobolev t 2 (0 : 𝓢'(E, ℂ)) := by
  have := SobolevSpace.memSobolev_toDistribution (0 : SobolevSpace E ℂ t)
  rwa [SobolevSpace.toDistribution_zero] at this

theorem exists_contDiff_comm {T : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)} (hT : IsLocal T) (θ : 𝓢(E, ℂ)) {k : ℝ}
    (hc : HasOrder (comm T θ) k) {u : 𝓢'(E, ℂ)} {Ω' : Set E} (hΩ' : IsOpen Ω')
    {g : E → ℂ} (hg : ContDiffOn ℝ ∞ g Ω')
    (hu : ∀ φ : 𝓢(E, ℂ), HasCompactSupport φ → tsupport φ ⊆ Ω' → u φ = ∫ x, φ x • g x)
    (hcover : ∀ y, y ∈ Ω' ∨ ∃ V : Set E, IsOpen V ∧ y ∈ V ∧
      Distribution.IsVanishingOn (comm T θ u) V) :
    ∃ β : E → ℂ, ContDiff ℝ ∞ β ∧ ∀ φ : 𝓢(E, ℂ), HasCompactSupport φ →
      comm T θ u φ = ∫ x, φ x • β x := by
  suffices hloc : ∀ y ∈ (Set.univ : Set E), ∃ ψ : 𝓢(E, ℂ), (∀ᶠ x in nhds y, ψ x = 1) ∧
      ∀ t, MemSobolev t 2 (smulLeftCLM ℂ (ψ : E → ℂ) (comm T θ u)) by
    obtain ⟨β, hβ, hrep⟩ := exists_contDiffOn_of_locally_memSobolev isOpen_univ hloc
    exact ⟨β, contDiffOn_univ.1 hβ, fun φ hφ ↦ hrep φ hφ (Set.subset_univ _)⟩
  intro y _
  rcases hcover y with hy | hy
  · obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hΩ' y hy
    have hr : 0 < ε / 8 := by positivity
    have h3 : 0 < 3 * (ε / 8) := by positivity
    have h34 : 3 * (ε / 8) < 7 * (ε / 16) := by linarith
    set ψ₁ := bumpG y h3 h34
    have hψ₁Ω : tsupport (ψ₁ : E → ℂ) ⊆ Ω' := (tsupport_bumpG y h3 h34).trans fun x hx ↦
      hball (by rw [Metric.mem_closedBall] at hx; rw [Metric.mem_ball]; linarith)
    have hψ₁c : HasCompactSupport (ψ₁ : E → ℂ) :=
      IsCompact.of_isClosed_subset (isCompact_closedBall y _) (isClosed_tsupport _)
        (tsupport_bumpG y h3 h34)

    have hψ₁u : smulLeftCLM ℂ (ψ₁ : E → ℂ) u =
        ((cutMul hΩ' hg ψ₁ hψ₁c hψ₁Ω : 𝓢(E, ℂ)) : 𝓢'(E, ℂ)) := by
      ext φ
      rw [smulLeftCLM_apply_apply, SchwartzMap.coe_apply]
      have hc' : HasCompactSupport (SchwartzMap.smulLeftCLM ℂ (ψ₁ : E → ℂ) φ : E → ℂ) := by
        rw [SchwartzMap.smulLeftCLM_apply ψ₁.hasTemperateGrowth]
        exact hψ₁c.smul_right
      have hs' : tsupport (SchwartzMap.smulLeftCLM ℂ (ψ₁ : E → ℂ) φ : E → ℂ) ⊆ Ω' := by
        rw [SchwartzMap.smulLeftCLM_apply ψ₁.hasTemperateGrowth]
        exact (tsupport_smul_subset_left (ψ₁ : E → ℂ) (φ : E → ℂ)).trans hψ₁Ω
      rw [hu _ hc' hs']
      congr 1; ext x
      rw [SchwartzMap.smulLeftCLM_apply_apply ψ₁.hasTemperateGrowth, cutMul_apply, smul_eq_mul,
        smul_eq_mul, smul_eq_mul]
      ring
    refine ⟨bump y hr, ?_, fun t ↦ ?_⟩
    · filter_upwards [Metric.ball_mem_nhds y hr] with x hx
      exact bump_eq_one y hr (Metric.ball_subset_closedBall hx)
    · rw [smulLeft_comm_eq hT θ (ψ₁ := ψ₁) (V := Metric.ball y (3 * (ε / 8))) Metric.isOpen_ball
        (fun x hx ↦ bumpG_eq_one y h3 h34 (Metric.ball_subset_closedBall hx))
        ((tsupport_bump y hr).trans (Metric.closedBall_subset_ball (by linarith))), hψ₁u]
      refine memSobolev_smulLeft _ ?_
      exact hc.memSobolev' (s := t + k) (by ring) (cutMul hΩ' hg ψ₁ hψ₁c hψ₁Ω).memSobolev
  · obtain ⟨V₀, hV₀, hyV, hZ⟩ := hy
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hV₀ y hyV
    have hr : 0 < ε / 4 := by positivity
    refine ⟨bump y hr, ?_, fun t ↦ ?_⟩
    · filter_upwards [Metric.ball_mem_nhds y hr] with x hx
      exact bump_eq_one y hr (Metric.ball_subset_closedBall hx)
    · rw [smulLeftCLM_eq_zero_of_isVanishingOn (bump y hr).hasTemperateGrowth hZ
        ((tsupport_bump y hr).trans fun x hx ↦ hball (by
          rw [Metric.mem_closedBall] at hx; rw [Metric.mem_ball]; linarith))]
      exact memSobolev_zero_distribution t

end Comm

section Parametrix

variable {n : ℕ}

theorem exists_parametrix {m : ℕ} (hn : 0 < n) (hm : 1 ≤ m) (hnm : n < 2 * m)
    {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩ : IsOpen Ω) {A : Finset (Fin n → ℕ)}
    {a : (Fin n → ℕ) → EuclideanSpace ℝ (Fin n) → ℂ}
    (hA : ∀ α ∈ A, mabs α ≤ m) (ha : ∀ α ∈ A, ContDiffOn ℝ ∞ (a α) Ω)
    (hell : ∀ x ∈ Ω, ∀ ξ : EuclideanSpace ℝ (Fin n), ξ ≠ 0 → prinSymbol A a m x ξ ≠ 0)
    {x₀ : EuclideanSpace ℝ (Fin n)} {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    (hx₀U : x₀ ∈ U) (hUΩ : U ⊆ Ω) :
    ∃ E β : EuclideanSpace ℝ (Fin n) → ℂ, Integrable E ∧ HasCompactSupport E ∧ tsupport E ⊆ U ∧
      ContDiffOn ℝ ∞ E {x₀}ᶜ ∧ ContDiff ℝ ∞ β ∧ HasCompactSupport β ∧ tsupport β ⊆ U ∧
      ∀ φ : EuclideanSpace ℝ (Fin n) → ℂ, ContDiffOn ℝ ∞ φ U →
        ∫ x, E x * diffOp A a φ x = φ x₀ - ∫ x, β x * φ x := by
  have : Nontrivial (EuclideanSpace ℝ (Fin n)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by simpa using hn)

  obtain ⟨r, hr, hrU, b, hb⟩ := exists_schwartz_coeff hU (fun α hα ↦ (ha α hα).mono hUΩ) hx₀U
  have hell' : ∀ y ∈ Metric.closedBall x₀ r, IsEllipticAt (opST A b) m y := fun y hy ↦
    isEllipticAt_opST A b hA y fun ξ hξ ↦ by
      have e : ∑ α ∈ A with mabs α = m, b α y * (mpow α ξ : ℂ) = prinSymbol A a m y ξ :=
        Finset.sum_congr rfl fun α hα ↦ by rw [hb α (Finset.mem_filter.1 hα).1 y hy]
      rw [e]
      exact hell y (hUΩ (hrU ((Metric.closedBall_subset_closedBall (by linarith)) hy))) ξ hξ
  have hx₀r : x₀ ∈ Metric.closedBall x₀ r := Metric.mem_closedBall_self hr.le

  have hnm' : (n : ℝ) < 2 * m := by exact_mod_cast hnm
  have hfin : (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ) = n := by simp
  have ht : -((m : ℝ) + (n : ℝ) / 2) / 2 < -(Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ) / 2 := by
    rw [hfin]; linarith
  have htm : (0 : ℝ) ≤ -((m : ℝ) + (n : ℝ) / 2) / 2 + m := by linarith
  obtain ⟨r₁, hr₁, E₀, hE₀, hvan⟩ := (hell' x₀ hx₀r).exists_local_solution hm ht
  obtain ⟨ρ, hρ, hρr₁, hρr⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ r₁ ∧ ρ ≤ r :=
    ⟨min r₁ r, lt_min hr₁ hr, min_le_left _ _, min_le_right _ _⟩

  set Ω' := Metric.ball x₀ ρ \ {x₀}
  have hΩ' : IsOpen Ω' := Metric.isOpen_ball.sdiff isClosed_singleton
  have hΩ'r : Ω' ⊆ Metric.closedBall x₀ r := fun y hy ↦
    Metric.ball_subset_closedBall (Metric.ball_subset_ball hρr hy.1)
  obtain ⟨g, hg, hgrep⟩ := contDiffOn_of_isEllipticAt hm hΩ' (fun y hy ↦ hell' y (hΩ'r hy)) hE₀
    (F := 0) memSobolev_zero_distribution (by
      rw [sub_zero]
      have h1 := hvan.mono (show Ω' ⊆ Metric.ball x₀ r₁ from fun y hy ↦
        Metric.ball_subset_ball hρr₁ hy.1)
      have h2 := (TemperedDistribution.isVanishingOn_delta x₀).mono
        (show Ω' ⊆ {x₀}ᶜ from fun y hy ↦ hy.2)
      have := isVanishingOn_add h1 h2
      rwa [sub_add_cancel] at this)

  obtain ⟨e, he⟩ := memSobolev_zero_iff.1 (hE₀.mono htm)
  have hE₀e : ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), E₀ φ = ∫ x, φ x • e x := fun φ ↦ by
    rw [he, MeasureTheory.Lp.toTemperedDistribution_apply]
  have he_loc : LocallyIntegrable (e : EuclideanSpace ℝ (Fin n) → ℂ) volume :=
    (Lp.memLp e).locallyIntegrable (by norm_num)

  have hae : ∀ᵐ x, x ∈ Ω' → e x = g x := by
    have h := hΩ'.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume)
      (f := fun x ↦ e x - g x)
      (he_loc.locallyIntegrableOn _ |>.sub (hg.continuousOn.locallyIntegrableOn hΩ'.measurableSet))
      fun g' hg' hg'c hg'Ω ↦ by
        have hc₁ : HasCompactSupport (Complex.ofRealCLM ∘ g') := hg'c.comp_left rfl
        have hc₂ : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g') := by fun_prop
        obtain ⟨φ, hφdef⟩ : ∃ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), φ = hc₁.toSchwartzMap hc₂ :=
          ⟨_, rfl⟩
        have hφf : (φ : EuclideanSpace ℝ (Fin n) → ℂ) = Complex.ofRealCLM ∘ g' := by
          rw [hφdef]; rfl
        have hφ : ∀ x, φ x = (g' x : ℂ) := fun x ↦ by rw [hφf]; rfl
        have hφc : HasCompactSupport (φ : EuclideanSpace ℝ (Fin n) → ℂ) := by rw [hφf]; exact hc₁
        have hφΩ : tsupport (φ : EuclideanSpace ℝ (Fin n) → ℂ) ⊆ Ω' := by
          rw [hφf]; exact (tsupport_comp_subset (g := Complex.ofRealCLM) (by simp) _).trans hg'Ω
        have hi1 : Integrable (fun x ↦ φ x • e x) :=
          integrable_smul_of_locallyIntegrableOn (he_loc.locallyIntegrableOn _) hφc
            (Set.subset_univ _)
        have hi2 := integrable_smul_of_tsupport_subset hΩ' hg.continuousOn hφc hφΩ
        have e1 : ∫ x, g' x • (e x - g x) = (∫ x, φ x • e x) - ∫ x, φ x • g x := by
          rw [← integral_sub hi1 hi2]
          congr 1; ext x
          rw [hφ, smul_sub, Complex.real_smul, Complex.real_smul, smul_eq_mul, smul_eq_mul]
        rw [e1, ← hE₀e, ← hgrep φ hφc hφΩ, sub_self]
    filter_upwards [h] with x hx hxΩ
    exact sub_eq_zero.1 (hx hxΩ)

  have hq1 : 0 < ρ / 4 := by positivity
  have hq2 : ρ / 4 < ρ / 2 := by linarith
  set θ := bumpG x₀ hq1 hq2
  have hθs : tsupport (θ : EuclideanSpace ℝ (Fin n) → ℂ) ⊆ Metric.closedBall x₀ (ρ / 2) :=
    tsupport_bumpG x₀ hq1 hq2
  have hθ0 : ∀ x, x ∉ Metric.closedBall x₀ (ρ / 2) → θ x = 0 := fun x hx ↦
    image_eq_zero_of_notMem_tsupport fun h ↦ hx (hθs h)
  have hθx₀ : θ x₀ = 1 := bumpG_eq_one x₀ hq1 hq2 (Metric.mem_closedBall_self hq1.le)
  have hhalfU : Metric.closedBall x₀ (ρ / 2) ⊆ U :=
    (Metric.closedBall_subset_closedBall (by linarith)).trans hrU

  set E : EuclideanSpace ℝ (Fin n) → ℂ := fun x ↦ θ x * g x
  have hEs : tsupport E ⊆ Metric.closedBall x₀ (ρ / 2) :=
    (tsupport_mul_subset_left).trans hθs
  have hEc : HasCompactSupport E :=
    IsCompact.of_isClosed_subset (isCompact_closedBall x₀ _) (isClosed_tsupport _) hEs
  have hEe : E =ᵐ[volume] fun x ↦ θ x * e x := by
    have hx₀ : ∀ᵐ x : EuclideanSpace ℝ (Fin n), x ≠ x₀ := by
      rw [ae_iff]; simp only [not_not, Set.ofPred_eq_eq_singleton]; exact measure_singleton x₀
    filter_upwards [hae, hx₀] with x hx hxx₀
    by_cases hxb : x ∈ Metric.ball x₀ ρ
    · simp only [E]; rw [hx ⟨hxb, hxx₀⟩]
    · have : x ∉ Metric.closedBall x₀ (ρ / 2) := by
        intro h; apply hxb; rw [Metric.mem_closedBall] at h; rw [Metric.mem_ball]; linarith
      simp only [E, hθ0 x this, zero_mul]
  have hEint : Integrable E := by
    have h := (θ.memLp 2 volume).integrable_mul (Lp.memLp e)
    exact h.congr hEe.symm
  have hEsmooth : ContDiffOn ℝ ∞ E {x₀}ᶜ := by
    refine contDiffOn_of_locally_contDiffOn fun x hx ↦ ?_
    by_cases hxb : x ∈ Metric.ball x₀ ρ
    · refine ⟨Ω', hΩ', ⟨hxb, hx⟩, ?_⟩
      exact (θ.smooth'.contDiffOn.mul hg).mono Set.inter_subset_right
    · refine ⟨(Metric.closedBall x₀ (ρ / 2))ᶜ, Metric.isClosed_closedBall.isOpen_compl, ?_, ?_⟩
      · intro h; apply hxb; rw [Metric.mem_closedBall] at h; rw [Metric.mem_ball]; linarith
      · refine (contDiffOn_const (c := (0 : ℂ))).congr fun y hy ↦ ?_
        simp only [E, hθ0 y hy.2, zero_mul]

  have hT'loc : IsLocal (opST A b) := (hell' x₀ hx₀r).isLocal
  have hZ1 : Distribution.IsVanishingOn (comm (opST A b) θ E₀) (Metric.ball x₀ (ρ / 4)) := by
    have hθE : Distribution.IsVanishingOn (smulLeftCLM ℂ (θ : EuclideanSpace ℝ (Fin n) → ℂ) E₀ - E₀)
        (Metric.ball x₀ (ρ / 4)) := isVanishingOn_smulLeftCLM_sub θ.hasTemperateGrowth
      (fun x hx ↦ bumpG_eq_one x₀ hq1 hq2 (Metric.ball_subset_closedBall hx)) E₀
    have hθT : Distribution.IsVanishingOn
        (smulLeftCLM ℂ (θ : EuclideanSpace ℝ (Fin n) → ℂ) (opST A b E₀) - opST A b E₀)
        (Metric.ball x₀ (ρ / 4)) := isVanishingOn_smulLeftCLM_sub θ.hasTemperateGrowth
      (fun x hx ↦ bumpG_eq_one x₀ hq1 hq2 (Metric.ball_subset_closedBall hx)) _
    have h1 := hT'loc _ Metric.isOpen_ball _ hθE
    rw [map_sub] at h1
    have e : comm (opST A b) θ E₀ = (opST A b (smulLeftCLM ℂ (θ : EuclideanSpace ℝ (Fin n) → ℂ) E₀) -
        opST A b E₀) - (smulLeftCLM ℂ (θ : EuclideanSpace ℝ (Fin n) → ℂ) (opST A b E₀) -
        opST A b E₀) := by rw [comm_apply]; abel
    rw [e]
    exact isVanishingOn_sub h1 hθT
  have hZ2 : Distribution.IsVanishingOn (comm (opST A b) θ E₀) (Metric.closedBall x₀ (ρ / 2))ᶜ := by
    have hU' : IsOpen (Metric.closedBall x₀ (ρ / 2))ᶜ := Metric.isClosed_closedBall.isOpen_compl
    have h1 := (isVanishingOn_smulLeftCLM_compl θ.hasTemperateGrowth E₀).mono
      (Set.compl_subset_compl.2 hθs)
    have h2 := hT'loc _ hU' _ h1
    have h3 := (isVanishingOn_smulLeftCLM_compl θ.hasTemperateGrowth (opST A b E₀)).mono
      (Set.compl_subset_compl.2 hθs)
    rw [comm_apply]
    exact isVanishingOn_sub h2 h3
  obtain ⟨β', hβ', hβ'rep⟩ := exists_contDiff_comm hT'loc θ ((hell' x₀ hx₀r).hasOrder_comm θ) hΩ' hg
    hgrep fun y ↦ by
      by_cases hy1 : y ∈ Metric.ball x₀ (ρ / 4)
      · exact Or.inr ⟨_, Metric.isOpen_ball, hy1, hZ1⟩
      · by_cases hy2 : y ∈ Metric.closedBall x₀ (ρ / 2)
        · left
          refine ⟨Metric.closedBall_subset_ball (by linarith) hy2, fun h ↦ hy1 ?_⟩
          rw [Set.mem_singleton_iff] at h; rw [h]; exact Metric.mem_ball_self hq1
        · exact Or.inr ⟨_, Metric.isClosed_closedBall.isOpen_compl, hy2, hZ2⟩

  have hβ'0 : Set.EqOn β' 0 (Metric.closedBall x₀ (ρ / 2))ᶜ := by
    refine eqOn_of_integral_smul_eq hβ'.continuous continuous_const
      Metric.isClosed_closedBall.isOpen_compl fun φ hφc hφ ↦ ?_
    rw [← hβ'rep φ hφc, hZ2 φ hφ]
    symm
    exact integral_eq_zero_of_ae (ae_of_all _ fun x ↦ by simp [Complex.ext_iff])
  have hβ's : tsupport β' ⊆ Metric.closedBall x₀ (ρ / 2) := by
    refine closure_minimal (fun x hx ↦ ?_) Metric.isClosed_closedBall
    by_contra h
    exact hx (hβ'0 h)

  have hTθ : opST A b (smulLeftCLM ℂ (θ : EuclideanSpace ℝ (Fin n) → ℂ) E₀) =
      TemperedDistribution.delta x₀ + comm (opST A b) θ E₀ := by
    have h1 : smulLeftCLM ℂ (θ : EuclideanSpace ℝ (Fin n) → ℂ) (opST A b E₀) =
        TemperedDistribution.delta x₀ := by
      have h0 := smulLeftCLM_eq_zero_of_isVanishingOn θ.hasTemperateGrowth hvan
        (hθs.trans (Metric.closedBall_subset_ball (by linarith)))
      rw [map_sub, sub_eq_zero, smulLeftCLM_delta, hθx₀, one_smul] at h0
      exact h0
    rw [comm_apply, h1]; abel
  refine ⟨E, fun x ↦ -β' x, hEint, hEc, hEs.trans hhalfU, hEsmooth, hβ'.neg, ?_, ?_, fun φ hφ ↦ ?_⟩
  · refine IsCompact.of_isClosed_subset (isCompact_closedBall x₀ (ρ / 2)) (isClosed_tsupport _) ?_
    show tsupport (-β') ⊆ _
    rw [tsupport_neg]; exact hβ's
  · show tsupport (-β') ⊆ _
    rw [tsupport_neg]; exact hβ's.trans hhalfU

  have hq3 : 0 < 3 * ρ / 4 := by positivity
  have hq4 : 3 * ρ / 4 < ρ := by linarith
  set θ₂ := bumpG x₀ hq3 hq4
  have hθ₂U : tsupport (θ₂ : EuclideanSpace ℝ (Fin n) → ℂ) ⊆ U :=
    (tsupport_bumpG x₀ hq3 hq4).trans ((Metric.closedBall_subset_closedBall (by linarith)).trans hrU)
  have hθ₂c : HasCompactSupport (θ₂ : EuclideanSpace ℝ (Fin n) → ℂ) :=
    IsCompact.of_isClosed_subset (isCompact_closedBall x₀ _) (isClosed_tsupport _)
      (tsupport_bumpG x₀ hq3 hq4)
  set φ' := cutMul hU hφ θ₂ hθ₂c hθ₂U
  have hφ' : ∀ x ∈ Metric.closedBall x₀ (3 * ρ / 4), φ' x = φ x := fun x hx ↦ by
    rw [cutMul_apply, bumpG_eq_one x₀ hq3 hq4 hx, one_mul]
  have hφ'c : HasCompactSupport (φ' : EuclideanSpace ℝ (Fin n) → ℂ) := by
    rw [show (φ' : EuclideanSpace ℝ (Fin n) → ℂ) = fun x ↦ θ₂ x * φ x from rfl]
    exact hθ₂c.mul_right
  set ψ' := ∑ α ∈ A, SchwartzMap.smulLeftCLM ℂ (b α : EuclideanSpace ℝ (Fin n) → ℂ) (∂^{mdir α} φ')
  have hDψ : ∀ x ∈ Metric.ball x₀ (3 * ρ / 4), diffOp A a φ x = ψ' x := by
    intro x hx
    rw [sum_smulLeft_apply_eq_diffOp A a b φ' (fun α hα ↦ hb α hα x (Metric.ball_subset_closedBall
      (Metric.ball_subset_ball (by linarith) hx)))]
    simp only [diffOp]
    refine Finset.sum_congr rfl fun α _ ↦ ?_
    congr 1
    refine pderiv_congr ?_
    filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy
    exact (hφ' y (Metric.ball_subset_closedBall hy)).symm
  have step1 : ∫ x, E x * diffOp A a φ x = ∫ x, ψ' x • (θ x * e x) := by
    calc ∫ x, E x * diffOp A a φ x = ∫ x, ψ' x • E x := by
          congr 1; ext x
          by_cases hx : x ∈ Metric.closedBall x₀ (ρ / 2)
          · rw [hDψ x (Metric.closedBall_subset_ball (by linarith) hx), smul_eq_mul, mul_comm]
          · simp only [E, hθ0 x hx, zero_mul, mul_zero, smul_zero]
      _ = _ := integral_congr_ae (hEe.mono fun x hx ↦ by show ψ' x • E x = _; rw [hx])
  have step2 : ∫ x, ψ' x • (θ x * e x) =
      smulLeftCLM ℂ (θ : EuclideanSpace ℝ (Fin n) → ℂ) E₀ ψ' := by
    rw [smulLeftCLM_apply_apply, hE₀e]
    congr 1; ext x
    rw [SchwartzMap.smulLeftCLM_apply_apply θ.hasTemperateGrowth, smul_eq_mul, smul_eq_mul,
      smul_eq_mul]
    ring
  have step3 : smulLeftCLM ℂ (θ : EuclideanSpace ℝ (Fin n) → ℂ) E₀ ψ' =
      opST A b (smulLeftCLM ℂ (θ : EuclideanSpace ℝ (Fin n) → ℂ) E₀) φ' :=
    (opST_apply_apply A b _ φ').symm
  rw [step1, step2, step3, hTθ, add_apply, TemperedDistribution.delta_apply,
    hφ' x₀ (Metric.mem_closedBall_self hq3.le), hβ'rep φ' hφ'c]
  have step4 : ∫ x, φ' x • β' x = ∫ x, φ x * β' x := by
    congr 1; ext x
    by_cases hx : x ∈ Metric.closedBall x₀ (ρ / 2)
    · rw [hφ' x (Metric.closedBall_subset_closedBall (by linarith) hx), smul_eq_mul]
    · rw [hβ'0 hx]; simp
  have e5 : ∫ x, (fun x ↦ -β' x) x * φ x = -∫ x, φ x * β' x := by
    rw [← integral_neg]; congr 1; ext x; simp only; ring
  rw [step4, e5, sub_neg_eq_add]

end Parametrix

end

end GroundTheory.Automorphic.Sobolev
end

section -- merged from GroundTheory.AutomorphicForms.HarishChandraRegularity.ExpChart
namespace GroundTheory.Automorphic

open NormedSpace Set Filter Topology
open scoped ContDiff

set_option linter.unusedSectionVars false

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]

theorem analyticAt_expPartialHomeomorph_symm {y : 𝔸}
    (hy : y ∈ (expPartialHomeomorph ℝ 𝔸).target) :
    AnalyticAt ℝ (expPartialHomeomorph ℝ 𝔸).symm y := by
  set e := expPartialHomeomorph ℝ 𝔸 with he
  have hs : e.symm y ∈ e.source := e.map_target hy
  have hu : IsUnit (fderiv ℝ (exp : 𝔸 → 𝔸) (e.symm y)) :=
    expPartialHomeomorph_source_subset ℝ 𝔸 hs
  obtain ⟨p, hp⟩ := exp_analytic (𝕂 := ℝ) (e.symm y)
  have hp' : HasFPowerSeriesAt e p (e.symm y) := by
    rw [he, coe_expPartialHomeomorph]; exact hp
  have h1 : p 1 = (continuousMultilinearCurryFin1 ℝ 𝔸 𝔸).symm
      ((ContinuousLinearEquiv.unitsEquiv ℝ 𝔸 hu.unit : 𝔸 ≃L[ℝ] 𝔸) : 𝔸 →L[ℝ] 𝔸) := by
    have h2 := hp.fderiv_eq
    have h3 : ((ContinuousLinearEquiv.unitsEquiv ℝ 𝔸 hu.unit : 𝔸 ≃L[ℝ] 𝔸) : 𝔸 →L[ℝ] 𝔸) =
        fderiv ℝ (exp : 𝔸 → 𝔸) (e.symm y) := by
      ext x; simp
    rw [h3, h2, LinearIsometryEquiv.symm_apply_apply]
  have := e.hasFPowerSeriesAt_symm hs hp' h1
  rw [e.right_inv hy] at this
  exact this.analyticAt

variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}

noncomputable def expChartProd {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) (X : 𝔤)
    (p : EuclideanSpace ℝ (Fin d) × ℝ) : 𝔸 :=
  exp ((coordEquiv b p.1 : 𝔤) : 𝔸) * exp (p.2 • (X : 𝔸))

noncomputable def expChartFlow {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) (X : 𝔤)
    (p : EuclideanSpace ℝ (Fin d) × ℝ) : EuclideanSpace ℝ (Fin d) :=
  (coordEquiv b).symm (subspaceProj 𝔤 ((expPartialHomeomorph ℝ 𝔸).symm (expChartProd b X p)))

noncomputable def expChartCoeff {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) (X : 𝔤)
    (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  fderiv ℝ (expChartFlow b X) (x, 0) (0, 1)

theorem continuous_expChartProd {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) (X : 𝔤) :
    Continuous (expChartProd b X) := by
  unfold expChartProd
  refine Continuous.mul ?_ ?_
  · exact (contDiff_exp ℝ 𝔸 (n := 0)).continuous.comp
      (continuous_subtype_val.comp ((coordEquiv b).continuous.comp continuous_fst))
  · exact (contDiff_exp ℝ 𝔸 (n := 0)).continuous.comp (continuous_snd.smul continuous_const)

theorem analyticAt_expChartProd {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) (X : 𝔤)
    (p : EuclideanSpace ℝ (Fin d) × ℝ) : AnalyticAt ℝ (expChartProd b X) p := by
  have h1 : AnalyticAt ℝ (fun q : EuclideanSpace ℝ (Fin d) × ℝ => ((coordEquiv b q.1 : 𝔤) : 𝔸)) p :=
    (𝔤.subtypeL.comp ((coordEquiv b : EuclideanSpace ℝ (Fin d) →L[ℝ] 𝔤).comp
      (ContinuousLinearMap.fst ℝ _ ℝ))).analyticAt p
  have h2 : AnalyticAt ℝ (fun q : EuclideanSpace ℝ (Fin d) × ℝ => q.2 • (X : 𝔸)) p :=
    ((ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin d)) ℝ).smulRight (X : 𝔸)).analyticAt p
  have h1' := (exp_analytic (𝕂 := ℝ) _).comp h1
  have h2' := (exp_analytic (𝕂 := ℝ) _).comp h2
  exact h1'.mul h2'

theorem analyticAt_expChartFlow {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) (X : 𝔤)
    {p : EuclideanSpace ℝ (Fin d) × ℝ}
    (hp : expChartProd b X p ∈ (expPartialHomeomorph ℝ 𝔸).target) :
    AnalyticAt ℝ (expChartFlow b X) p := by
  have hL : AnalyticAt ℝ (fun w : 𝔸 => (coordEquiv b).symm (subspaceProj 𝔤 w))
      ((expPartialHomeomorph ℝ 𝔸).symm (expChartProd b X p)) :=
    (((coordEquiv b).symm : 𝔤 →L[ℝ] EuclideanSpace ℝ (Fin d)).comp (subspaceProj 𝔤)).analyticAt _
  have h2 : AnalyticAt ℝ ((expPartialHomeomorph ℝ 𝔸).symm ∘ expChartProd b X) p :=
    (analyticAt_expPartialHomeomorph_symm hp).comp (analyticAt_expChartProd b X p)
  exact AnalyticAt.comp (f := (expPartialHomeomorph ℝ 𝔸).symm ∘ expChartProd b X)
    (g := fun w : 𝔸 => (coordEquiv b).symm (subspaceProj 𝔤 w)) hL h2

theorem analyticOnNhd_expChartFlow {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) (X : 𝔤) :
    AnalyticOnNhd ℝ (expChartFlow b X) (expChartProd b X ⁻¹' (expPartialHomeomorph ℝ 𝔸).target) :=
  fun _ hp => analyticAt_expChartFlow b X hp

namespace IsExpLieAlgebra

variable (h : IsExpLieAlgebra G 𝔤)

theorem exists_ball_coordEquiv_mem_nhd {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) :
    ∃ r > 0, ∀ x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r,
      ((coordEquiv b x : 𝔤) : 𝔸) ∈ h.nhd := by
  have hc : Continuous (fun x : EuclideanSpace ℝ (Fin d) => ((coordEquiv b x : 𝔤) : 𝔸)) :=
    continuous_subtype_val.comp (coordEquiv b).continuous
  have h0 : h.nhd ∈ 𝓝 ((fun x : EuclideanSpace ℝ (Fin d) => ((coordEquiv b x : 𝔤) : 𝔸)) 0) := by
    simp only [map_zero, ZeroMemClass.coe_zero]
    exact h.isOpen_nhd.mem_nhds h.zero_mem_nhd
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (hc.continuousAt.preimage_mem_nhds h0)
  exact ⟨r, hr, fun x hx => hball hx⟩

theorem val_expG_mul_expG {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) (X : 𝔤)
    (p : EuclideanSpace ℝ (Fin d) × ℝ) :
    (((h.expG (coordEquiv b p.1) * h.expG (p.2 • X) : G) : 𝔸ˣ) : 𝔸) = expChartProd b X p := by
  simp [expChartProd]

theorem expG_expChartFlow {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) (X : 𝔤)
    {p : EuclideanSpace ℝ (Fin d) × ℝ} (hp : expChartProd b X p ∈ h.nhdOne) :
    h.expG (coordEquiv b (expChartFlow b X p)) = h.expG (coordEquiv b p.1) * h.expG (p.2 • X) := by
  set w : G := h.expG (coordEquiv b p.1) * h.expG (p.2 • X) with hw
  have hwv : ((w : 𝔸ˣ) : 𝔸) = expChartProd b X p := h.val_expG_mul_expG b X p
  have hwN : ((w : 𝔸ˣ) : 𝔸) ∈ h.nhdOne := hwv ▸ hp
  have hmem := h.symm_mem_lie hwN
  have e1 : coordEquiv b (expChartFlow b X p) =
      subspaceProj 𝔤 ((expPartialHomeomorph ℝ 𝔸).symm ((w : 𝔸ˣ) : 𝔸)) := by
    rw [hwv]; exact (coordEquiv b).apply_symm_apply _
  apply Subtype.ext; apply Units.ext
  rw [coe_expG, e1, subspaceProj_of_mem hmem, h.exp_symm hwN]

theorem expChartFlow_zero {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) (X : 𝔤)
    {x : EuclideanSpace ℝ (Fin d)} (hx : ((coordEquiv b x : 𝔤) : 𝔸) ∈ h.nhd) :
    expChartFlow b X (x, 0) = x := by
  simp only [expChartFlow, expChartProd, zero_smul, exp_zero, mul_one]
  rw [h.symm_exp hx, subspaceProj_coe, ContinuousLinearEquiv.symm_apply_apply]

theorem expChartProd_zero_mem_nhdOne {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) (X : 𝔤)
    {x : EuclideanSpace ℝ (Fin d)} (hx : ((coordEquiv b x : 𝔤) : 𝔸) ∈ h.nhd) :
    expChartProd b X (x, 0) ∈ h.nhdOne := by
  simp only [expChartProd, zero_smul, exp_zero, mul_one]
  exact h.exp_mem_nhdOne hx

theorem hasDerivAt_expChartFlow {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) (X : 𝔤)
    {x : EuclideanSpace ℝ (Fin d)} (hx : ((coordEquiv b x : 𝔤) : 𝔸) ∈ h.nhd) :
    HasDerivAt (fun t : ℝ => expChartFlow b X (x, t)) (expChartCoeff b X x) 0 := by
  have hA : AnalyticAt ℝ (expChartFlow b X) (x, 0) :=
    analyticAt_expChartFlow b X (h.nhdOne_subset_target (h.expChartProd_zero_mem_nhdOne b X hx))
  have hl : HasDerivAt (fun t : ℝ => (x, t)) ((0 : EuclideanSpace ℝ (Fin d)), (1 : ℝ)) 0 :=
    (hasDerivAt_const (0 : ℝ) x).prodMk (hasDerivAt_id 0)
  exact hA.differentiableAt.hasFDerivAt.comp_hasDerivAt (x := (0 : ℝ)) hl

theorem exists_expChart_coeff {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) :
    ∃ r > 0, ∃ c : 𝔤 → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
      (∀ X, AnalyticOnNhd ℝ (c X) (Metric.ball 0 r)) ∧
      (∀ X, c X 0 = (coordEquiv b).symm X) ∧
      ∀ (X : 𝔤) (f : G → ℂ), h.IsSmoothFun f → ∀ (g : G),
        ∀ x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r,
          h.rightDeriv X f (g * h.expG (coordEquiv b x)) =
            fderiv ℝ (fun y => f (g * h.expG (coordEquiv b y))) x (c X x) := by
  obtain ⟨r, hr, hball⟩ := h.exists_ball_coordEquiv_mem_nhd b
  refine ⟨r, hr, expChartCoeff b, ?_, ?_, ?_⟩
  ·
    intro X x hx
    have hS : (x, (0 : ℝ)) ∈ expChartProd b X ⁻¹' (expPartialHomeomorph ℝ 𝔸).target :=
      h.nhdOne_subset_target (h.expChartProd_zero_mem_nhdOne b X (hball x hx))
    have hD := (analyticOnNhd_expChartFlow b X).fderiv (𝕜 := ℝ) _ hS
    have hinl : AnalyticAt ℝ (fun y : EuclideanSpace ℝ (Fin d) => (y, (0 : ℝ))) x :=
      (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin d)) ℝ).analyticAt x
    have hD' : AnalyticAt ℝ (fun y : EuclideanSpace ℝ (Fin d) =>
        fderiv ℝ (expChartFlow b X) (y, 0)) x :=
      AnalyticAt.comp (g := fderiv ℝ (expChartFlow b X))
        (f := fun y : EuclideanSpace ℝ (Fin d) => (y, (0 : ℝ))) hD hinl
    have hap := (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin d))
      ((0 : EuclideanSpace ℝ (Fin d)), (1 : ℝ))).analyticAt (fderiv ℝ (expChartFlow b X) (x, 0))
    exact AnalyticAt.comp (f := fun y : EuclideanSpace ℝ (Fin d) => fderiv ℝ (expChartFlow b X) (y, 0))
      hap hD'
  ·
    intro X
    have h0 : ((coordEquiv b (0 : EuclideanSpace ℝ (Fin d)) : 𝔤) : 𝔸) ∈ h.nhd := by
      simp only [map_zero, ZeroMemClass.coe_zero]; exact h.zero_mem_nhd
    have hd := h.hasDerivAt_expChartFlow b X h0
    have hev : (fun t : ℝ => expChartFlow b X (0, t)) =ᶠ[𝓝 0]
        fun t : ℝ => t • (coordEquiv b).symm X := by
      have hc : Continuous (fun t : ℝ => t • (X : 𝔸)) := continuous_id.smul continuous_const
      have : ∀ᶠ t in 𝓝 (0 : ℝ), t • (X : 𝔸) ∈ h.nhd := by
        have h1 := hc.continuousAt (x := 0)
        rw [ContinuousAt, zero_smul] at h1
        exact h1 (h.isOpen_nhd.mem_nhds h.zero_mem_nhd)
      filter_upwards [this] with t ht
      simp only [expChartFlow, expChartProd, map_zero, ZeroMemClass.coe_zero, exp_zero, one_mul]
      rw [h.symm_exp ht, show t • (X : 𝔸) = ((t • X : 𝔤) : 𝔸) from rfl, subspaceProj_coe, map_smul]
    have hd2 : HasDerivAt (fun t : ℝ => t • (coordEquiv b).symm X) ((coordEquiv b).symm X) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const ((coordEquiv b).symm X)
    exact hd.unique (hd2.congr_of_eventuallyEq hev)
  ·
    intro X f hf g x hx
    have hxN := hball x hx
    set u : EuclideanSpace ℝ (Fin d) → ℂ := fun y => f (g * h.expG (coordEquiv b y)) with hu
    have hud : Differentiable ℝ u := (h.contDiff_comp_coordEquiv hf g b).differentiable (by simp)
    have hφ := h.hasDerivAt_expChartFlow b X hxN
    have h1 : HasDerivAt (fun t : ℝ => u (expChartFlow b X (x, t)))
        (fderiv ℝ u x (expChartCoeff b X x)) 0 := by
      have := (hud (expChartFlow b X (x, 0))).hasFDerivAt.comp_hasDerivAt (x := (0 : ℝ)) hφ
      rw [h.expChartFlow_zero b X hxN] at this
      exact this
    have h2 := h.hasDerivAt_rightDeriv hf X (g * h.expG (coordEquiv b x))
    have hev : (fun t : ℝ => f (g * h.expG (coordEquiv b x) * h.expG (t • X))) =ᶠ[𝓝 0]
        fun t : ℝ => u (expChartFlow b X (x, t)) := by
      have hc : Continuous (fun t : ℝ => expChartProd b X (x, t)) :=
        (continuous_expChartProd b X).comp (continuous_const.prodMk continuous_id)
      have : ∀ᶠ t in 𝓝 (0 : ℝ), expChartProd b X (x, t) ∈ h.nhdOne :=
        hc.continuousAt.preimage_mem_nhds
          (h.isOpen_nhdOne.mem_nhds (h.expChartProd_zero_mem_nhdOne b X hxN))
      filter_upwards [this] with t ht
      simp only [hu]
      rw [h.expG_expChartFlow b X ht, mul_assoc]
    exact h2.unique (h1.congr_of_eventuallyEq hev)

end IsExpLieAlgebra

end GroundTheory.Automorphic
end

namespace GroundTheory.Automorphic

open Sobolev Set Filter Topology MeasureTheory
open scoped ContDiff Manifold

set_option linter.unusedSectionVars false

namespace Sobolev

variable {n : ℕ}

def sqSymbol {ι : Type*} [Fintype ι] (c : ι → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x ξ : EuclideanSpace ℝ (Fin n)) : ℂ :=
  ∑ i, (∑ j, ((c i x j : ℝ) : ℂ) * ((ξ j : ℝ) : ℂ)) ^ 2

theorem sqSymbol_eq {ι : Type*} [Fintype ι] (c : ι → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x ξ : EuclideanSpace ℝ (Fin n)) :
    sqSymbol c x ξ = ((∑ i, (inner ℝ (c i x) ξ) ^ 2 : ℝ) : ℂ) := by
  simp only [sqSymbol, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem exists_ball_sqSymbol_ne_zero {ι : Type*} [Fintype ι]
    {c : ι → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} (hc : ∀ i, ContinuousAt (c i) 0)
    (hspan : ∀ ξ : EuclideanSpace ℝ (Fin n), (∀ i, inner ℝ (c i 0) ξ = 0) → ξ = 0) :
    ∃ δ > 0, ∀ x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ, ∀ ξ, ξ ≠ 0 → sqSymbol c x ξ ≠ 0 := by
  classical
  let Q : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) := fun x => ∑ i, (innerSL ℝ (c i x)).smulRight (c i x)
  have hQ : ∀ x ξ, Q x ξ = ∑ i, inner ℝ (c i x) ξ • c i x := by
    intro x ξ; simp [Q]
  have hquad : ∀ x ξ, inner ℝ (Q x ξ) ξ = ∑ i, (inner ℝ (c i x) ξ) ^ 2 := by
    intro x ξ
    rw [hQ, sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_smul_left, sq]
  have hzero : ∀ x ξ, ∑ i, (inner ℝ (c i x) ξ) ^ 2 = 0 → Q x ξ = 0 := by
    intro x ξ h0
    have hall := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg (inner ℝ (c i x) ξ)).1 h0
    rw [hQ]
    exact Finset.sum_eq_zero fun i hi => by
      rw [pow_eq_zero_iff two_ne_zero |>.1 (hall i hi), zero_smul]
  have hinj : Function.Injective (Q 0) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro ξ hξ
    apply hspan
    have h0 : ∑ i, (inner ℝ (c i 0) ξ) ^ 2 = 0 := by rw [← hquad, hξ, inner_zero_left]
    intro i
    exact pow_eq_zero_iff two_ne_zero |>.1
      ((Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg (inner ℝ (c i 0) ξ)).1 h0 i
        (Finset.mem_univ _))
  have hsurj : Function.Surjective (Q 0) :=
    LinearMap.injective_iff_surjective (f := ((Q 0 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
      EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))).1 hinj
  let e := ContinuousLinearEquiv.ofBijective (Q 0) (LinearMap.ker_eq_bot.2 hinj)
    (LinearMap.range_eq_top.2 hsurj)
  have hU : IsUnit (Q 0) :=
    ⟨(ContinuousLinearEquiv.unitsEquiv ℝ (EuclideanSpace ℝ (Fin n))).symm e, ContinuousLinearMap.ext fun _ => rfl⟩
  have hQc : ContinuousAt Q 0 := by
    rw [continuousAt_clm_apply]
    intro ξ
    simp only [hQ]
    exact tendsto_finsetSum _ fun i _ =>
      (Filter.Tendsto.inner (hc i) tendsto_const_nhds).smul (hc i)
  set_option synthInstance.maxHeartbeats 200000 in
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 (hQc.preimage_mem_nhds (Units.isOpen.mem_nhds hU))
  refine ⟨δ, hδ, fun x hx ξ hξ hs => hξ ?_⟩
  obtain ⟨u, hu⟩ := hball hx
  rw [sqSymbol_eq, Complex.ofReal_eq_zero] at hs
  have h1 := hzero x ξ hs
  rw [← hu] at h1
  have h2 := congrArg (fun v => ((↑u⁻¹ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) v) h1
  have h3 : ((↑u⁻¹ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) *
      (↑u : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) ξ = 0 := by
    change (↑u⁻¹ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
      ((↑u : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) ξ) = 0
    rw [h1, map_zero]
  rw [Units.inv_mul] at h3
  simpa using h3

theorem integral_euclideanSpace_of_eq_zero {d : ℕ} (hd : d = 0) (F : EuclideanSpace ℝ (Fin d) → ℂ) :
    ∫ x, F x = F 0 := by
  subst hd
  rw [volume_euclideanSpace_eq_dirac, integral_dirac]

end Sobolev

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}

namespace IsExpLieAlgebra

variable (h : IsExpLieAlgebra G 𝔤)

def lieEquiv : h.lieSubalgebra ≃ₗ[ℝ] 𝔤 where
  toFun := h.ofLie
  invFun := h.toLie
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem lieEquiv_apply (X : h.lieSubalgebra) : h.lieEquiv X = h.ofLie X := rfl

theorem span_coord_of_basis {ι : Type*} [Fintype ι] (bL : Module.Basis ι ℝ h.lieSubalgebra) {d : ℕ}
    (b : Module.Basis (Fin d) ℝ 𝔤) (ξ : EuclideanSpace ℝ (Fin d))
    (hξ : ∀ i, inner ℝ ((coordEquiv b).symm (h.ofLie (bL i))) ξ = 0) : ξ = 0 := by
  have hall : ∀ v : h.lieSubalgebra, inner ℝ ((coordEquiv b).symm (h.lieEquiv v)) ξ = 0 := by
    intro v
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← bL.sum_repr v, map_sum, map_sum, sum_inner]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_smul, map_smul, real_inner_smul_left, lieEquiv_apply, hξ i, mul_zero]
  have := hall (h.lieEquiv.symm (coordEquiv b ξ))
  rw [LinearEquiv.apply_symm_apply, ContinuousLinearEquiv.symm_apply_apply] at this
  exact inner_self_eq_zero.1 this

theorem laplacian_apply_coe {ι : Type*} [Fintype ι] (bL : Module.Basis ι ℝ h.lieSubalgebra)
    (w : h.smoothFuns (F := ℂ)) :
    ((h.laplacian bL w : h.smoothFuns (F := ℂ)) : G → ℂ) =
      ∑ i, h.rightDeriv (h.ofLie (bL i)) (h.rightDeriv (h.ofLie (bL i)) (w : G → ℂ)) := by
  simp [laplacian, LinearMap.sum_apply, Module.End.mul_apply]

theorem exists_tupleOp_laplacian_pow {ι : Type*} [Fintype ι] (bL : Module.Basis ι ℝ h.lieSubalgebra)
    {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsOpen Ω)
    (c : ι → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hc : ∀ i, AnalyticOnNhd ℝ (c i) Ω)
    (hR : ∀ i (F : G → ℂ), h.IsSmoothFun F → ∀ g : G, ∀ x ∈ Ω,
      h.rightDeriv (h.ofLie (bL i)) F (g * h.expG (coordEquiv b x)) =
        vfOp (c i) (fun y => F (g * h.expG (coordEquiv b y))) x)
    (k : ℕ) : ∃ a : (k : ℕ) → (Fin k → Fin d) → EuclideanSpace ℝ (Fin d) → ℂ,
      (∀ k' J, AnalyticOnNhd ℝ (a k' J) Ω) ∧
      (∀ x ∈ Ω, ∀ ξ, tupleSymbol (2 * k) a x ξ = sqSymbol c x ξ ^ k) ∧
      ∀ (F : h.smoothFuns (F := ℂ)) (g : G), ∀ x ∈ Ω,
        ((((h.laplacian bL) ^ k) F : h.smoothFuns (F := ℂ)) : G → ℂ) (g * h.expG (coordEquiv b x)) =
          tupleOp (2 * k) a (fun y => (F : G → ℂ) (g * h.expG (coordEquiv b y))) x := by
  induction k with
  | zero =>
    refine ⟨idCoeff, fun k J => analyticOnNhd_idCoeff k J Ω,
      fun x _ ξ => by simpa using tupleSymbol_idCoeff x ξ, fun F g x _ => ?_⟩
    simp [tupleOp_idCoeff]
  | succ k ih =>
    obtain ⟨a, ha, hs, hop⟩ := ih
    have s1 := fun i => exists_vfOp_tupleOp (hc i) (m := 2 * k) ha
    choose a1 ha1 hs1 hop1 using s1
    have s2 := fun i => exists_vfOp_tupleOp (hc i) (m := 2 * k + 1) (ha1 i)
    choose a2 ha2 hs2 hop2 using s2
    have e2 : 2 * (k + 1) = 2 * k + 1 + 1 := by ring
    refine ⟨∑ i, a2 i, fun k' J => ?_, fun x hx ξ => ?_, fun F g x hx => ?_⟩
    · have : (∑ i, a2 i) k' J = ∑ i, a2 i k' J := by ext y; simp [Finset.sum_apply]
      rw [this]; exact Finset.analyticOnNhd_sum _ fun i _ => ha2 i k' J
    · rw [e2, tupleSymbol_sum]
      simp only [hs2 _ x, hs1 _ x, hs x hx]
      rw [pow_succ', sqSymbol, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    · set u := fun y => (F : G → ℂ) (g * h.expG (coordEquiv b y)) with hu_def
      have hu : ContDiff ℝ ∞ u := h.contDiff_comp_coordEquiv F.2 g b
      rw [pow_succ', Module.End.mul_apply, laplacian_apply_coe, Finset.sum_apply, e2, tupleOp_sum]
      set w := ((h.laplacian bL) ^ k) F
      have hw : h.IsSmoothFun (w : G → ℂ) := w.2
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hR i _ (h.isSmoothFun_rightDeriv hw _) g x hx]
      have E1 : EqOn (fun y => h.rightDeriv (h.ofLie (bL i)) (w : G → ℂ) (g * h.expG (coordEquiv b y)))
          (vfOp (c i) (fun y => (w : G → ℂ) (g * h.expG (coordEquiv b y)))) Ω :=
        fun y hy => hR i _ hw g y hy
      have E2 : EqOn (fun y => (w : G → ℂ) (g * h.expG (coordEquiv b y))) (tupleOp (2 * k) a u) Ω :=
        fun y hy => hop F g y hy
      have E3 : EqOn (vfOp (c i) (fun y => (w : G → ℂ) (g * h.expG (coordEquiv b y))))
          (tupleOp (2 * k + 1) (a1 i) u) Ω :=
        fun y hy => (vfOp_congr_of_eqOn hΩ E2 (c i) hy).trans (hop1 i u hu y hy)
      rw [vfOp_congr_of_eqOn hΩ (E1.trans E3) (c i) hx, hop2 i u hu x hx]

theorem exists_tupleOp_aeval_laplacian {ι : Type*} [Fintype ι] (bL : Module.Basis ι ℝ h.lieSubalgebra)
    {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsOpen Ω)
    (c : ι → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hc : ∀ i, AnalyticOnNhd ℝ (c i) Ω)
    (hR : ∀ i (F : G → ℂ), h.IsSmoothFun F → ∀ g : G, ∀ x ∈ Ω,
      h.rightDeriv (h.ofLie (bL i)) F (g * h.expG (coordEquiv b x)) =
        vfOp (c i) (fun y => F (g * h.expG (coordEquiv b y))) x)
    (P : Polynomial ℂ) (hP : P.Monic) :
    ∃ a : (k : ℕ) → (Fin k → Fin d) → EuclideanSpace ℝ (Fin d) → ℂ,
      (∀ k J, AnalyticOnNhd ℝ (a k J) Ω) ∧
      (∀ x ∈ Ω, ∀ ξ, tupleSymbol (2 * P.natDegree) a x ξ = sqSymbol c x ξ ^ P.natDegree) ∧
      ∀ (F : h.smoothFuns (F := ℂ)) (g : G), ∀ x ∈ Ω,
        ((Polynomial.aeval (h.laplacian bL) P F : h.smoothFuns (F := ℂ)) : G → ℂ)
            (g * h.expG (coordEquiv b x)) =
          tupleOp (2 * P.natDegree) a (fun y => (F : G → ℂ) (g * h.expG (coordEquiv b y))) x := by
  classical
  set N := P.natDegree with hN
  have s := fun i => h.exists_tupleOp_laplacian_pow bL b hΩ c hc hR i
  choose a ha hs hop using s
  let a' : ℕ → (k : ℕ) → (Fin k → Fin d) → EuclideanSpace ℝ (Fin d) → ℂ :=
    fun i => P.coeff i • raiseCoeff (2 * i) (a i)
  refine ⟨∑ i ∈ Finset.range (N + 1), a' i, fun k J => ?_, fun x hx ξ => ?_, fun F g x hx => ?_⟩
  · exact analyticOnNhd_sum_coeff _
      (fun i _ => analyticOnNhd_smul_coeff _ (analyticOnNhd_raiseCoeff _ (ha i))) k J
  · rw [tupleSymbol_sum, Finset.sum_range_succ, Finset.sum_eq_zero, zero_add]
    · simp only [a']
      rw [tupleSymbol_smul, tupleSymbol_raiseCoeff, hs N x hx, show P.coeff N = 1 from hP.coeff_natDegree,
        one_mul]
    · intro i hi
      simp only [a']
      rw [tupleSymbol_smul, tupleSymbol_raiseCoeff_of_lt (by simp at hi; omega), mul_zero]
  · rw [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply,
      tupleOp_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [a']
    rw [LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, hop i F g x hx,
      tupleOp_smul, tupleOp_raiseCoeff (by simp at hi; omega)]

theorem exists_elliptic_aeval_laplacian {ι : Type*} [Fintype ι] (bL : Module.Basis ι ℝ h.lieSubalgebra)
    {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) (P : Polynomial ℂ) (hP : P.Monic) :
    ∃ δ > 0, ∃ (A : Finset (Fin d → ℕ)) (a : (Fin d → ℕ) → EuclideanSpace ℝ (Fin d) → ℂ),
      (∀ α ∈ A, mabs α ≤ 2 * P.natDegree) ∧
      (∀ α ∈ A, AnalyticOn ℝ (a α) (Metric.ball 0 δ)) ∧
      (∀ x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) δ, ∀ ξ, ξ ≠ 0 →
        prinSymbol A a (2 * P.natDegree) x ξ ≠ 0) ∧
      ∀ (F : h.smoothFuns (F := ℂ)) (g : G), ∀ x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) δ,
        diffOp A a (fun y => (F : G → ℂ) (g * h.expG (coordEquiv b y))) x =
          ((Polynomial.aeval (h.laplacian bL) P F : h.smoothFuns (F := ℂ)) : G → ℂ)
            (g * h.expG (coordEquiv b x)) := by
  obtain ⟨r, hr, cX, hcan, hc0, hchart⟩ := h.exists_expChart_coeff b
  set c : ι → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) := fun i => cX (h.ofLie (bL i))
  have hcont : ∀ i, ContinuousAt (c i) 0 := fun i =>
    (hcan _ 0 (Metric.mem_ball_self hr)).continuousAt
  have hspan : ∀ ξ : EuclideanSpace ℝ (Fin d), (∀ i, inner ℝ (c i 0) ξ = 0) → ξ = 0 := by
    intro ξ hξ
    exact h.span_coord_of_basis bL b ξ fun i => by rw [← hc0]; exact hξ i
  obtain ⟨δ₀, hδ₀, hell⟩ := exists_ball_sqSymbol_ne_zero hcont hspan
  set δ := min r δ₀
  have hδ : 0 < δ := lt_min hr hδ₀
  have hΩr : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) δ ⊆ Metric.ball 0 r :=
    Metric.ball_subset_ball (min_le_left _ _)
  have hΩδ : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) δ ⊆ Metric.ball 0 δ₀ :=
    Metric.ball_subset_ball (min_le_right _ _)
  have hR : ∀ i (F : G → ℂ), h.IsSmoothFun F → ∀ g : G, ∀ x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) δ,
      h.rightDeriv (h.ofLie (bL i)) F (g * h.expG (coordEquiv b x)) =
        vfOp (c i) (fun y => F (g * h.expG (coordEquiv b y))) x := fun i F hF g x hx =>
    hchart _ F hF g x (hΩr hx)
  obtain ⟨a, ha, hs, hop⟩ := h.exists_tupleOp_aeval_laplacian bL b Metric.isOpen_ball c
    (fun i => (hcan _).mono hΩr) hR P hP
  obtain ⟨A, a', hA, ha', hsym, hconv⟩ := exists_diffOp_eq_tupleOp _ a ha
  refine ⟨δ, hδ, A, a', hA, fun α hα => (ha' α hα).analyticOn, fun x hx ξ hξ => ?_,
    fun F g x hx => ?_⟩
  · rw [hsym x ξ, hs x hx]
    exact pow_ne_zero _ (hell x (hΩδ hx) ξ hξ)
  · rw [hconv _ (h.contDiff_comp_coordEquiv F.2 g b), hop F g x hx]

theorem analyticAt_of_aeval_laplacian_eq_zero {ι : Type*} [Fintype ι]
    (bL : Module.Basis ι ℝ h.lieSubalgebra) (P : Polynomial ℂ) (hP : P.Monic)
    (f : h.smoothFuns (F := ℂ)) (hf : Polynomial.aeval (h.laplacian bL) P f = 0) (g : G) :
    AnalyticAt ℝ (fun Y : 𝔤 => (f : G → ℂ) (g * h.expG Y)) 0 := by
  set b := Module.finBasis ℝ 𝔤
  obtain ⟨δ, hδ, A, a, hA, ha, hell, hop⟩ := h.exists_elliptic_aeval_laplacian bL b P hP
  set u := fun y => (f : G → ℂ) (g * h.expG (coordEquiv b y))
  have hu : ContDiff ℝ ∞ u := h.contDiff_comp_coordEquiv f.2 g b
  have han : AnalyticOn ℝ u (Metric.ball 0 δ) :=
    analyticOn_of_elliptic Metric.isOpen_ball hA ha hell hu.contDiffOn fun x hx => by
      rw [hop f g x hx, hf]; rfl
  have hu0 : AnalyticAt ℝ u 0 :=
    (Metric.isOpen_ball.analyticOn_iff_analyticOnNhd.1 han) 0 (Metric.mem_ball_self hδ)
  have e : (fun Y : 𝔤 => (f : G → ℂ) (g * h.expG Y)) = u ∘ (coordEquiv b).symm := by
    funext Y; simp [u]
  rw [e]
  refine AnalyticAt.comp (by simpa using hu0) ?_
  exact (coordEquiv b).symm.toContinuousLinearMap.analyticAt _

end IsExpLieAlgebra

section Groups

open Matrix
open scoped Matrix.Norms.L2Operator

namespace IsExpLieAlgebra

end IsExpLieAlgebra

end Groups

end GroundTheory.Automorphic
