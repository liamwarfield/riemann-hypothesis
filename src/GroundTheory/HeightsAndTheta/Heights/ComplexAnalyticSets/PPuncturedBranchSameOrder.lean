module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLelongRegularise
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetAreaCompare
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPrimeGermPrimitivePresentation
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveResidueDegree

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPuncturedBranchSameOrder
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

noncomputable section

namespace PuncturedBranchSameOrder

theorem const_mem_ball_iff (τ : ℂ) (r : ℝ) :
    (fun _ : Fin 1 ↦ τ) ∈ Metric.ball (0 : Fin 1 → ℂ) r ↔ τ ∈ Metric.ball (0 : ℂ) r := by
  simp only [Metric.mem_ball, dist_zero_right, pi_norm_const]

theorem disc_props {n : ℕ} {I : Ideal (MvPolynomial (Fin n) ℂ)} {q : Fin n → ℂ} (b : VarBranch I 1 q) :
    DifferentiableOn ℂ (fun τ : ℂ ↦ b.toFun fun _ ↦ τ) (Metric.ball 0 b.radius) ∧
    Set.InjOn (fun τ : ℂ ↦ b.toFun fun _ ↦ τ) (Metric.ball 0 b.radius) ∧
    Set.MapsTo (fun τ : ℂ ↦ b.toFun fun _ ↦ τ) (Metric.ball 0 b.radius) (zeroSet I) ∧
    (b.toFun fun _ ↦ (0 : ℂ)) = q ∧
    ∀ x, x ∈ b.image ↔ ∃ σ ∈ Metric.ball (0 : ℂ) b.radius, (b.toFun fun _ ↦ σ) = x := by
  have hι : Differentiable ℂ (fun τ : ℂ ↦ fun _ : Fin 1 ↦ τ) := differentiable_pi.2 fun _ ↦ differentiable_id
  refine ⟨b.differentiableOn.comp hι.differentiableOn fun τ hτ ↦ (const_mem_ball_iff τ _).2 hτ,
    fun s hs t ht h ↦ congrFun (b.injOn ((const_mem_ball_iff s _).2 hs) ((const_mem_ball_iff t _).2 ht) h) 0,
    fun τ hτ ↦ b.mapsTo ((const_mem_ball_iff τ _).2 hτ), b.map_zero, fun x ↦ ⟨?_, ?_⟩⟩
  · rintro ⟨t, ht, rfl⟩
    have ht' : (fun _ : Fin 1 ↦ t 0) = t := funext fun i ↦ by rw [Subsingleton.elim i 0]
    refine ⟨t 0, (const_mem_ball_iff _ _).1 ?_, by rw [ht']⟩
    rw [ht']
    exact ht
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨_, (const_mem_ball_iff σ _).2 hσ, rfl⟩

theorem factor_of_punctured {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {C D : ℂ → E} {ψ : ℂ → ℂ}
    {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ)
    (hCd : DifferentiableOn ℂ C (Metric.ball 0 r)) (hCi : Set.InjOn C (Metric.ball 0 r))
    (hDd : DifferentiableOn ℂ D (Metric.ball 0 ρ)) (hDi : Set.InjOn D (Metric.ball 0 ρ)) (h0 : C 0 = D 0)
    (hψd : DifferentiableOn ℂ ψ (Metric.ball 0 ρ \ {0}))
    (hψ : ∀ τ ∈ Metric.ball (0 : ℂ) ρ \ {0}, ψ τ ∈ Metric.ball (0 : ℂ) r ∧ C (ψ τ) = D τ) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ g 0 = 0 ∧ (∀ᶠ τ in 𝓝 0, D τ = C (g τ)) ∧ 𝓝 0 ≤ map g (𝓝 0) := by
  obtain ⟨g, hg_def⟩ : ∃ g : ℂ → ℂ, g = Function.update ψ 0 (limUnder (𝓝[≠] (0 : ℂ)) ψ) := ⟨_, rfl⟩
  have hB : Metric.ball (0 : ℂ) ρ ∈ 𝓝 0 := Metric.ball_mem_nhds 0 hρ
  have hgd : DifferentiableOn ℂ g (Metric.ball 0 ρ) := by
    rw [hg_def]
    refine Complex.differentiableOn_update_limUnder_of_bddAbove hB hψd ⟨r, ?_⟩
    rintro _ ⟨τ, hτ, rfl⟩
    exact (mem_ball_zero_iff.1 (hψ τ hτ).1).le
  have hgψ : ∀ τ, τ ≠ 0 → g τ = ψ τ := fun τ hτ ↦ by rw [hg_def]; exact Function.update_of_ne hτ _ _
  have hgc : ContinuousAt g 0 := (hgd.differentiableAt hB).continuousAt
  have hpunct : ∀ᶠ τ in 𝓝[≠] (0 : ℂ), τ ∈ Metric.ball (0 : ℂ) ρ \ {0} :=
    Filter.mem_of_superset (inter_mem_nhdsWithin _ hB) fun τ h ↦ ⟨h.2, h.1⟩
  have hpt : ∀ s : ℝ, 0 < s → s < ρ → (s : ℂ) ∈ Metric.ball (0 : ℂ) ρ \ {0} := fun s hs hsρ ↦
    ⟨by rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg hs.le]; exact hsρ, by simpa using hs.ne'⟩
  have hle : ‖g 0‖ ≤ r := by
    refine le_of_tendsto (hgc.norm.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℂ) ≤ 𝓝 0)) ?_
    filter_upwards [hpunct] with τ hτ
    rw [hgψ τ hτ.2]
    exact (mem_ball_zero_iff.1 (hψ τ hτ).1).le
  have hlt : ‖g 0‖ < r := by
    refine lt_of_le_of_ne hle fun heq ↦ ?_
    have hmax : IsMaxOn (norm ∘ g) (Metric.ball 0 ρ) 0 := isMaxOn_iff.2 fun τ hτ ↦ by
      show ‖g τ‖ ≤ ‖g 0‖
      by_cases h : τ = 0
      · rw [h]
      · rw [hgψ τ h, heq]
        exact (mem_ball_zero_iff.1 (hψ τ ⟨hτ, h⟩).1).le
    have hconst := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm (convex_ball (0 : ℂ) ρ).isPreconnected
      Metric.isOpen_ball hgd (Metric.mem_ball_self hρ) hmax
    have h1 := hpt (ρ / 2) (by positivity) (by linarith)
    have h2 := hpt (ρ / 4) (by positivity) (by linarith)
    have e1 : D ((ρ / 2 : ℝ) : ℂ) = C (g 0) := by
      rw [← (hψ _ h1).2, ← hgψ _ h1.2]
      exact congrArg C (hconst h1.1)
    have e2 : D ((ρ / 4 : ℝ) : ℂ) = C (g 0) := by
      rw [← (hψ _ h2).2, ← hgψ _ h2.2]
      exact congrArg C (hconst h2.1)
    have := Complex.ofReal_injective (hDi h1.1 h2.1 (e1.trans e2.symm))
    linarith
  have hgr : g 0 ∈ Metric.ball (0 : ℂ) r := mem_ball_zero_iff.2 hlt
  have hCg0 : C (g 0) = D 0 := by
    have hC : ContinuousAt C (g 0) := (hCd.differentiableAt (Metric.isOpen_ball.mem_nhds hgr)).continuousAt
    have hD : ContinuousAt D 0 := (hDd.differentiableAt hB).continuousAt
    refine tendsto_nhds_unique_of_eventuallyEq ((hC.comp hgc).tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℂ) ≤ 𝓝 0))
      (hD.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℂ) ≤ 𝓝 0)) ?_
    filter_upwards [hpunct] with τ hτ
    rw [Function.comp_apply, hgψ τ hτ.2]
    exact (hψ τ hτ).2
  have hg0 : g 0 = 0 := hCi hgr (Metric.mem_ball_self hr) (hCg0.trans h0.symm)
  have hev : ∀ᶠ τ in 𝓝 (0 : ℂ), D τ = C (g τ) := by
    filter_upwards [hB] with τ hτ
    by_cases h : τ = 0
    · rw [h, hCg0]
    · rw [hgψ τ h]
      exact (hψ τ ⟨hτ, h⟩).2.symm
  have hga : AnalyticAt ℂ g 0 := hgd.analyticAt hB
  refine ⟨g, hga, hg0, hev, ?_⟩
  rcases hga.eventually_constant_or_nhds_le_map_nhds with hc | hc
  · exfalso
    obtain ⟨ε, hε, hεb⟩ := Metric.eventually_nhds_iff.1 (hc.and hev)
    have hm : 0 < min ε ρ := lt_min hε hρ
    have hs : 0 < min ε ρ / 2 := half_pos hm
    have hsε : min ε ρ / 2 < ε := by have := min_le_left ε ρ; linarith
    have hsρ : min ε ρ / 2 < ρ := by have := min_le_right ε ρ; linarith
    have h1 := hpt _ hs hsρ
    obtain ⟨hgc1, hD1⟩ := hεb (by rw [dist_zero_right, Complex.norm_real, Real.norm_of_nonneg hs.le]; exact hsε)
    exact h1.2 (hDi h1.1 (Metric.mem_ball_self hρ) (by rw [hD1, hgc1, hg0, h0]))
  · rwa [hg0] at hc

theorem punctured_factor (hcut : PuncturedCurveDiscInverse.Statement) {n : ℕ} {I : Ideal (MvPolynomial (Fin n) ℂ)}
    {q : Fin n → ℂ} (hI : IsRadicalAt I q) (hdim : ringKrullDim (curveLocalRing I q) = 1) (c d : VarBranch I 1 q)
    (ρ : ℝ) (hρ : 0 < ρ) (hcd : ∀ τ : ℂ, 0 < ‖τ‖ → ‖τ‖ < ρ → d.toFun (fun _ ↦ τ) ∈ c.image) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ g 0 = 0 ∧ (∀ᶠ τ in 𝓝 0, (d.toFun fun _ ↦ τ) = c.toFun fun _ ↦ g τ) ∧
      𝓝 0 ≤ map g (𝓝 0) := by
  obtain ⟨hCd, hCi, hCm, hC0, hCim⟩ := disc_props c
  obtain ⟨hDd, hDi, hDm, hD0, -⟩ := disc_props d
  obtain ⟨ε, hε, hcutε⟩ := hcut n I q hI hdim
  have hDc : ContinuousAt (fun τ : ℂ ↦ d.toFun fun _ ↦ τ) 0 :=
    (hDd.differentiableAt (Metric.ball_mem_nhds 0 d.radius_pos)).continuousAt
  obtain ⟨ρ₁, hρ₁, hρ₁ε⟩ := Metric.continuousAt_iff.1 hDc ε hε
  obtain ⟨ρ', hρ'⟩ : ∃ ρ' : ℝ, ρ' = min (min ρ ρ₁) d.radius := ⟨_, rfl⟩
  have hρ'pos : 0 < ρ' := hρ' ▸ lt_min (lt_min hρ hρ₁) d.radius_pos
  have hρ'ρ : ρ' ≤ ρ := hρ' ▸ (min_le_left _ _).trans (min_le_left _ _)
  have hρ'1 : ρ' ≤ ρ₁ := hρ' ▸ (min_le_left _ _).trans (min_le_right _ _)
  have hsub : Metric.ball (0 : ℂ) ρ' ⊆ Metric.ball 0 d.radius := Metric.ball_subset_ball (hρ' ▸ min_le_right _ _)
  let ψ : ℂ → ℂ := fun τ ↦
    Function.invFunOn (fun σ : ℂ ↦ c.toFun fun _ ↦ σ) (Metric.ball 0 c.radius) (d.toFun fun _ ↦ τ)
  have hψ : ∀ τ ∈ Metric.ball (0 : ℂ) ρ' \ {0},
      ψ τ ∈ Metric.ball (0 : ℂ) c.radius ∧ (c.toFun fun _ ↦ ψ τ) = d.toFun fun _ ↦ τ := by
    intro τ hτ
    have hex := (hCim _).1 (hcd τ (norm_pos_iff.2 hτ.2) (lt_of_lt_of_le (mem_ball_zero_iff.1 hτ.1) hρ'ρ))
    exact ⟨Function.invFunOn_mem hex, Function.invFunOn_eq hex⟩
  have hopen : IsOpen (Metric.ball (0 : ℂ) ρ' \ {0}) := Metric.isOpen_ball.sdiff isClosed_singleton
  have hψd : DifferentiableOn ℂ ψ (Metric.ball 0 ρ' \ {0}) := by
    intro τ₀ hτ₀
    obtain ⟨hσ₀r, hσ₀⟩ := hψ τ₀ hτ₀
    have hδ : 0 < c.radius - ‖ψ τ₀‖ := sub_pos.2 (mem_ball_zero_iff.1 hσ₀r)
    have hballsub : Metric.ball (ψ τ₀) (c.radius - ‖ψ τ₀‖) ⊆ Metric.ball 0 c.radius :=
      Metric.ball_subset_ball' (by rw [dist_zero_right]; linarith)
    have hne : (d.toFun fun _ ↦ τ₀) ≠ q := fun h ↦
      hτ₀.2 (hDi (hsub hτ₀.1) (Metric.mem_ball_self d.radius_pos) (h.trans hD0.symm))
    have hε₀ : (d.toFun fun _ ↦ τ₀) ∈ Metric.ball q ε := by
      have := hρ₁ε (x := τ₀) (by rw [dist_zero_right]; exact lt_of_lt_of_le (mem_ball_zero_iff.1 hτ₀.1) hρ'1)
      rw [Metric.mem_ball]
      rwa [hD0] at this
    obtain ⟨U, hUo, hUx, Ψ, hΨd, hΨ⟩ := hcutε (fun σ ↦ c.toFun fun _ ↦ σ) (ψ τ₀) (c.radius - ‖ψ τ₀‖) hδ
      (hCd.mono hballsub) (hCi.mono hballsub) (fun σ hσ ↦ hCm (hballsub hσ))
      (by show (c.toFun fun _ ↦ ψ τ₀) ∈ Metric.ball q ε; rw [hσ₀]; exact hε₀)
      (by show (c.toFun fun _ ↦ ψ τ₀) ≠ q; rw [hσ₀]; exact hne)
    have hUD : (d.toFun fun _ ↦ τ₀) ∈ U := by
      have hUx' : (c.toFun fun _ ↦ ψ τ₀) ∈ U := hUx
      rwa [hσ₀] at hUx'
    have hDdiff : DifferentiableAt ℂ (fun τ : ℂ ↦ d.toFun fun _ ↦ τ) τ₀ :=
      hDd.differentiableAt (Metric.isOpen_ball.mem_nhds (hsub hτ₀.1))
    have hevU : ∀ᶠ τ in 𝓝 τ₀, (d.toFun fun _ ↦ τ) ∈ U :=
      hDdiff.continuousAt.preimage_mem_nhds (hUo.mem_nhds hUD)
    have heq : ψ =ᶠ[𝓝 τ₀] fun τ ↦ Ψ (d.toFun fun _ ↦ τ) := by
      filter_upwards [hevU, hopen.mem_nhds hτ₀] with τ hτU hτ
      obtain ⟨σ, hσ, hσz, hΨσ⟩ := hΨ (d.toFun fun _ ↦ τ) ⟨hDm (hsub hτ.1), hτU⟩
      rw [hΨσ]
      exact hCi (hψ τ hτ).1 (hballsub hσ) ((hψ τ hτ).2.trans hσz.symm)
    have hdiff : DifferentiableAt ℂ (fun τ ↦ Ψ (d.toFun fun _ ↦ τ)) τ₀ :=
      (hΨd.differentiableAt (hUo.mem_nhds hUD)).comp τ₀ hDdiff
    exact (hdiff.congr_of_eventuallyEq heq).differentiableWithinAt
  exact factor_of_punctured (C := fun σ : ℂ ↦ c.toFun fun _ ↦ σ) (D := fun τ : ℂ ↦ d.toFun fun _ ↦ τ)
    c.radius_pos hρ'pos hCd hCi (hDd.mono hsub) (hDi.mono hsub) (hC0.trans hD0.symm) hψd hψ

end PuncturedBranchSameOrder

theorem PuncturedBranchSameOrder.proof (hcut : PuncturedCurveDiscInverse.Statement) :
    PuncturedBranchSameOrder.Statement := by
  intro n I q c d ρ hI hdim hρ hcd f
  obtain ⟨g, hga, hg0, hev, hmap⟩ := PuncturedBranchSameOrder.punctured_factor hcut hI hdim c d ρ hρ hcd
  have hBd : Metric.ball (0 : ℂ) d.radius ∈ 𝓝 0 := Metric.ball_mem_nhds 0 d.radius_pos
  have hdc : ∃ ρ'' > 0, ∀ σ : ℂ, 0 < ‖σ‖ → ‖σ‖ < ρ'' → c.toFun (fun _ ↦ σ) ∈ d.image := by
    have hA : {τ : ℂ | τ ∈ Metric.ball 0 d.radius ∧ (d.toFun fun _ ↦ τ) = c.toFun fun _ ↦ g τ} ∈ 𝓝 0 :=
      Filter.Eventually.and hBd hev
    obtain ⟨ρ'', hρ'', hball⟩ := Metric.mem_nhds_iff.1 (hmap (Filter.image_mem_map hA))
    refine ⟨ρ'', hρ'', fun σ _ hσ ↦ ?_⟩
    obtain ⟨τ, ⟨hτd, hτeq⟩, rfl⟩ := hball (mem_ball_zero_iff.2 hσ)
    exact ((PuncturedBranchSameOrder.disc_props d).2.2.2.2 _).2 ⟨τ, hτd, hτeq⟩
  obtain ⟨ρ'', hρ'', hdc'⟩ := hdc
  obtain ⟨k, hka, hk0, hev', -⟩ := PuncturedBranchSameOrder.punctured_factor hcut hI hdim d c ρ'' hρ'' hdc'
  have hgt : Tendsto g (𝓝 0) (𝓝 0) := by
    have := hga.continuousAt.tendsto
    rwa [hg0] at this
  have hkt : Tendsto k (𝓝 0) (𝓝 0) := by
    have := hka.continuousAt.tendsto
    rwa [hk0] at this
  have hid : (fun τ ↦ k (g τ)) =ᶠ[𝓝 0] id := by
    filter_upwards [hgt.eventually hev', (hkt.comp hgt).eventually hBd, hev, hBd] with τ h1 h2 h3 h4
    exact (PuncturedBranchSameOrder.disc_props d).2.1 h2 h4 (h1.symm.trans h3.symm)
  have hgd : deriv g 0 ≠ 0 := by
    intro hz
    have hk' : HasDerivAt k (deriv k 0) (g 0) := by
      rw [hg0]
      exact hka.differentiableAt.hasDerivAt
    have e1 : HasDerivAt (fun τ ↦ k (g τ)) (deriv k 0 * deriv g 0) 0 :=
      hk'.comp 0 hga.differentiableAt.hasDerivAt
    have e2 : HasDerivAt (fun τ ↦ k (g τ)) 1 0 := (hasDerivAt_id 0).congr_of_eventuallyEq hid
    have := e1.unique e2
    rw [hz, mul_zero] at this
    exact zero_ne_one this
  have hcong : (fun τ : ℂ ↦ eval (d.toFun fun _ ↦ τ) f) =ᶠ[𝓝 0]
      (fun σ : ℂ ↦ eval (c.toFun fun _ ↦ σ) f) ∘ g := by
    filter_upwards [hev] with τ hτ
    rw [Function.comp_apply, hτ]
  show analyticOrderAt (fun τ : ℂ ↦ eval (c.toFun fun _ ↦ τ) f) 0 =
    analyticOrderAt (fun τ : ℂ ↦ eval (d.toFun fun _ ↦ τ) f) 0
  rw [analyticOrderAt_congr hcong, analyticOrderAt_comp_of_deriv_ne_zero hga hgd, hg0]

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PGermProjectionFunctionForm
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter PrimeGermPrimitivePresentation

noncomputable section

namespace GermProjectionFunctionForm

variable {σ : Type} [Fintype σ]

theorem germPull_toGerm {d : ℕ} (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (w : σ → ℂ) (u : anFun (A w)) :
    germPull A (A.analyticAt w) rfl (toGerm (A w) u) = toGerm w (compA A w u) :=
  Subtype.ext (germPull_coe A (A.analyticAt w) rfl _ u.1 rfl)

theorem coordGerm_eq_toGerm (w : σ → ℂ) (i : σ) :
    coordGerm w i = toGerm w (mkA (fun z : σ → ℂ => z i)
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) i).analyticAt w)) :=
  Subtype.ext rfl

theorem isGermCombination_of_mem {w : σ → ℂ} {k : ℕ} (p : Fin k → (σ → ℂ) → ℂ) (u : anFun w)
    (hu : toGerm w u ∈ holGermIdeal w p) (f : (σ → ℂ) → ℂ) (hf : ∀ z, u.1 z = f z) :
    IsGermCombination w p f := by
  obtain ⟨h, hh, e⟩ := exists_of_mem_holGermIdeal p hu
  exact ⟨h, hh, (Germ.coe_eq.1 e).mono fun z hz => by rw [← hf]; exact hz⟩

end GermProjectionFunctionForm


open GermProjectionFunctionForm in
theorem GermProjectionFunctionForm.proof : GermProjectionFunctionForm.Statement := by
  classical
  intro σ _ w k p d A hp ⟨hinj, hgen, hint⟩
  let Z : σ → anFun w := fun i => mkA (fun z : σ → ℂ => z i)
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) i).analyticAt w)
  have hZ : ∀ i, coordGerm w i = toGerm w (Z i) := coordGerm_eq_toGerm w
  have hpull : ∀ φ : holGerms (A w), germPull A (A.analyticAt w) rfl φ = toGerm w (compA A w (rep φ)) := by
    intro φ
    conv_lhs => rw [← toGerm_rep φ]
    exact germPull_toGerm A w (rep φ)
  refine ⟨?_, ?_, ?_⟩
  · intro h hh hcomb
    have hmem := (toGerm_mem_iff hp (compA A w (mkA h hh))).2 hcomb
    rw [← germPull_toGerm] at hmem
    have h0 := congrArg Subtype.val (hinj _ hmem)
    exact Germ.coe_eq.1 (h0.trans (Germ.coe_zero (l := 𝓝 (A w)) (M := ℂ)).symm)
  · intro i
    obtain ⟨q, hq, hqP⟩ := hint i
    refine ⟨q.natDegree, fun j => (rep (q.coeff j)).1, fun j => (rep (q.coeff j)).2, ?_⟩
    have key : q.eval₂ (germPull A (A.analyticAt w) rfl) (coordGerm w i) =
        toGerm w (Z i ^ q.natDegree + ∑ j : Fin q.natDegree, compA A w (rep (q.coeff j)) * Z i ^ (j : ℕ)) := by
      conv_lhs => rw [hq.as_sum]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_finsetSum,
        Polynomial.eval₂_mul, Polynomial.eval₂_C, map_add, map_pow, map_sum, map_mul, hpull, hZ]
      rw [Fin.sum_univ_eq_sum_range (fun j => toGerm w (compA A w (rep (q.coeff j))) * toGerm w (Z i) ^ j)]
    rw [key] at hqP
    refine isGermCombination_of_mem p _ hqP _ fun z => ?_
    simp [Z, mkA, compA, Finset.sum_apply]
  · intro g hg
    obtain ⟨F, hF⟩ := hgen (toGerm w (mkA g hg))
    let e := Finsupp.equivFunOnFinite (α := σ) (M := ℕ)
    refine ⟨F.support.image e, fun m => (rep (F.coeff (e.symm m))).1, fun m _ => (rep (F.coeff (e.symm m))).2, ?_⟩
    have key : toGerm w (mkA g hg) - MvPolynomial.eval₂ (germPull A (A.analyticAt w) rfl) (coordGerm w) F =
        toGerm w (mkA g hg - ∑ m ∈ F.support, compA A w (rep (F.coeff m)) * ∏ i, Z i ^ m i) := by
      rw [MvPolynomial.eval₂_eq']
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sub, map_sum, map_mul, map_prod, map_pow, hpull, hZ]
    rw [key] at hF
    refine isGermCombination_of_mem p _ hF _ fun z => ?_
    rw [Finset.sum_image (fun x _ y _ h => e.injective h)]
    simp [Z, mkA, compA, Finset.sum_apply, Finset.prod_apply, e]

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRegMassNearSmall
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

theorem RegMassNearSmall.proof (hCmp : RegFormCompare.Statement) (hBall : RegBallMass.Statement)
    (hCov : SmallSetBallCover.Statement) : RegMassNearSmall.Statement := by
  classical
  intro n d J I u φ f hJ hdim hu hφ hIdim hf hfc δ hδ
  by_cases h : ∃ A : Matrix (Fin (d + 1)) (Fin n) ℂ, IsFiniteProjection J A
  swap
  · exact ⟨Set.univ, isOpen_univ, Set.subset_univ _, fun χ _ _ _ ε _ => by simp [varInt, h, hδ.le]⟩
  set A := h.choose
  have hA : IsFiniteProjection J A := h.choose_spec
  have hfin : ∀ y, (ComplexSets.fibre J A y).Finite := fun y => (FibreBound.proof n (d + 1) J A hJ hdim hA y).2.1
  set K := tsupport f
  obtain ⟨C₁, hC₁, h₁⟩ := hCmp n d J A φ f hJ hdim hA hφ hf hfc
  obtain ⟨C₂, hC₂, h₂⟩ := hBall n d J A u K hJ hdim hA hu hfc
  obtain ⟨C₃, hC₃, h₃⟩ := hCov n d I K hIdim hfc
  have hM : 0 ≤ C₁ * C₂ * C₃ := by positivity
  set r := min 1 (δ / (C₁ * C₂ * C₃ + 1))
  have hr : r ∈ Set.Ioc (0 : ℝ) 1 := ⟨lt_min one_pos (by positivity), min_le_left _ _⟩
  obtain ⟨T, hTK, hcov, hcard⟩ := h₃ r hr
  have hUo : IsOpen ((⋃ c ∈ T, Metric.ball c r) ∪ Kᶜ) :=
    (isOpen_biUnion fun (c : Fin n → ℂ) _ => Metric.isOpen_ball).union hfc.isClosed.isOpen_compl
  refine ⟨(⋃ c ∈ T, Metric.ball c r) ∪ Kᶜ, hUo, fun x hx => ?_, fun χ _ hχ1 hχU ε hε => ?_⟩
  · by_cases hxK : x ∈ K
    · exact Or.inl (hcov ⟨hx, hxK⟩)
    · exact Or.inr hxK
  set ψ : Fin (d + 1) → (Fin n → ℂ) → ℝ := vecCons (logReg u ε) fun _ => euclPot
  set w : (Fin n → ℂ) → ℝ := fun x => ∑ c ∈ T, (Metric.ball c r).indicator (fun _ => (1 : ℝ)) x with hw
  have hi0 : ∀ c x : Fin n → ℂ, 0 ≤ (Metric.ball c r).indicator (fun _ => (1 : ℝ)) x :=
    fun c x => Set.indicator_nonneg (fun _ _ => zero_le_one) x
  have hw0 : ∀ x, 0 ≤ w x := fun x => Finset.sum_nonneg fun c _ => hi0 c x
  have hvw : ∀ x ∈ K, |χ x| ≤ w x := by
    intro x hxK
    by_cases h0 : χ x = 0
    · rw [h0, abs_zero]
      exact hw0 x
    rcases hχU (subset_tsupport χ h0) with hxB | hxK'
    · obtain ⟨c, hc, hxc⟩ := Set.mem_iUnion₂.1 hxB
      calc |χ x| ≤ 1 := hχ1 x
        _ = (Metric.ball c r).indicator (fun _ => (1 : ℝ)) x := (Set.indicator_of_mem hxc (fun _ => (1 : ℝ))).symm
        _ ≤ w x := Finset.single_le_sum (f := fun c => (Metric.ball c r).indicator (fun _ => (1 : ℝ)) x)
            (fun c _ => hi0 c x) hc
    · exact absurd hxK hxK'
  have hsum : chartDens J A w ψ =
      fun y => ∑ c ∈ T, chartDens J A ((Metric.ball c r).indicator fun _ => 1) ψ y := by
    funext y
    simp only [chartDens, sheetSum]
    simp_rw [finsum_mem_eq_finite_toFinset_sum _ (hfin y)]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> simp [hw, Finset.sum_mul]
  have hball := fun c (hc : c ∈ T) => h₂ ε hε c (hTK hc).2 r hr
  have hint : Integrable (chartDens J A w ψ) := by
    rw [hsum]
    exact integrable_finsetSum _ fun c hc => (hball c hc).1
  have hT : ∫ y, chartDens J A w ψ y ≤ T.card * (C₂ * r ^ (2 * d)) := by
    rw [hsum, integral_finsetSum _ fun c hc => (hball c hc).1, ← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun c hc => (hball c hc).2
  rw [varInt, dite_eq_left h]
  calc |chartInt J A (fun x => χ x * f x) (vecCons (logReg u ε) φ)|
      ≤ ∫ y, C₁ * chartDens J A w ψ y := by
        refine abs_integral_le_integral_abs.trans (integral_mono_of_nonneg
          (Eventually.of_forall fun y => abs_nonneg _) (hint.const_mul C₁) (Eventually.of_forall fun y => ?_))
        exact (VarIntAdd.abs_chartDens_le hfin _ _ y).trans (h₁ u ε hε.1 χ w hw0 hvw y)
    _ = C₁ * ∫ y, chartDens J A w ψ y := integral_const_mul _ _
    _ ≤ C₁ * (T.card * (C₂ * r ^ (2 * d))) := mul_le_mul_of_nonneg_left hT hC₁
    _ = C₁ * C₂ * (T.card * r ^ (2 * d)) := by ring
    _ ≤ C₁ * C₂ * (C₃ * r ^ 2) := mul_le_mul_of_nonneg_left hcard (by positivity)
    _ ≤ (C₁ * C₂ * C₃ + 1) * r := by
        nlinarith [mul_le_mul_of_nonneg_left hr.2 (mul_nonneg hM hr.1.le), hr.1]
    _ ≤ (C₁ * C₂ * C₃ + 1) * (δ / (C₁ * C₂ * C₃ + 1)) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
    _ = δ := mul_div_cancel₀ _ (by positivity)

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceLocalDimGeneral
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

noncomputable section

theorem ringKrullDim_quotient_le_sup_span_add {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (I : Ideal R)
    (hI : I ≠ ⊤) {d : ℕ} (t : Fin d → R) (ht : ∀ i, t i ∈ IsLocalRing.maximalIdeal R) :
    ringKrullDim (R ⧸ I) ≤ ringKrullDim (R ⧸ (I ⊔ Ideal.span (Set.range t))) + (d : ℕ) := by
  classical
  let s : Finset (R ⧸ I) := Finset.univ.image fun i => Ideal.Quotient.mk I (t i)
  have hs : Ideal.span (s : Set (R ⧸ I)) = (Ideal.span (Set.range t)).map (Ideal.Quotient.mk I) := by
    rw [Ideal.map_span]
    congr 1
    ext x
    simp [s]
  have hjac : (Ideal.span (Set.range t)).map (Ideal.Quotient.mk I) ≤ Ring.jacobson (R ⧸ I) := by
    rw [← Ideal.jacobson_bot, ← Ideal.map_quotient_self I,
      ← Ideal.map_jacobson_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]),
      IsLocalRing.jacobson_eq_maximalIdeal I hI]
    refine Ideal.map_mono ?_
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact ht i
  have hkey := ringKrullDim_le_ringKrullDim_quotient_add_card s
    fun x hx => hjac (hs ▸ Ideal.subset_span hx)
  rw [hs, ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotSup I _)] at hkey
  refine hkey.trans ?_
  gcongr
  exact_mod_cast Finset.card_image_le.trans (by simp)

theorem one_le_ringKrullDim_localRingAt_sliceIdeal {n d : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ))
    (L : Matrix (Fin d) (Fin n) ℂ) (q : Fin n → ℂ)
    (hdim : ringKrullDim (localRingAt J q) = (d + 1 : ℕ)) :
    ((1 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (localRingAt (sliceIdeal J L q) q) := by
  let φ := algebraMap (MvPolynomial (Fin n) ℂ)
    (Localization.AtPrime (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)))
  let t : Fin d → MvPolynomial (Fin n) ℂ := fun i => linPoly L i - C ((L *ᵥ q) i)
  have hI : J.map φ ≠ ⊤ := by
    intro h
    unfold localRingAt at hdim
    have : Subsingleton (Localization.AtPrime (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)) ⧸
        J.map φ) := Ideal.Quotient.subsingleton_iff.mpr h
    rw [ringKrullDim_eq_bot_of_subsingleton] at hdim
    exact WithBot.bot_ne_coe hdim
  have ht : ∀ i, φ (t i) ∈ IsLocalRing.maximalIdeal
      (Localization.AtPrime (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ))) := by
    intro i
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    refine Ideal.mem_map_of_mem _ ?_
    simp [t, RingHom.mem_ker, eval_linPoly]
  have hkey := ringKrullDim_quotient_le_sup_span_add (J.map φ) hI (fun i => φ (t i)) ht
  have hsl : (sliceIdeal J L q).map φ = J.map φ ⊔ Ideal.span (Set.range fun i => φ (t i)) := by
    rw [sliceIdeal, Ideal.map_sup, Ideal.map_span, ← Set.range_comp]
    rfl
  rw [← hsl] at hkey
  change ringKrullDim (localRingAt J q) ≤ ringKrullDim (localRingAt (sliceIdeal J L q) q) + (d : ℕ)
    at hkey
  rw [hdim] at hkey
  generalize ringKrullDim (localRingAt (sliceIdeal J L q) q) = D at hkey ⊢
  induction D using WithBot.recBotCoe with
  | bot => simp at hkey
  | coe e =>
    induction e using ENat.recTopCoe with
    | top => exact WithBot.coe_le_coe.2 le_top
    | coe k =>
      have h2 : ((d + 1 : ℕ) : WithBot ℕ∞) ≤ ((k + d : ℕ) : WithBot ℕ∞) := by simpa using hkey
      have h3 : d + 1 ≤ k + d := by exact_mod_cast h2
      exact_mod_cast (show 1 ≤ k by omega)

theorem SliceLocalDimGeneral.proof (hL : LocalDimDomain.Statement)
    (hU : SliceLocalDimUpperZariski.Statement) : SliceLocalDimGeneral.Statement := by
  intro n d J q hJ hdim hq
  obtain ⟨F, hF, hgood⟩ := hU n d J q hJ hdim hq
  have hloc := hL n (d + 1) J hJ hdim q hq
  let e : Matrix (Fin d) (Fin n) ℂ → (Fin d × Fin n → ℂ) := fun L ij => L ij.1 ij.2
  let ψ : (Fin d × Fin n → ℂ) → Matrix (Fin d) (Fin n) ℂ := fun y => Matrix.of fun i j => y (i, j)
  have he : Continuous e := continuous_pi fun ij => continuous_id.matrix_elem ij.1 ij.2
  have hψ : Continuous ψ :=
    continuous_pi fun i => continuous_pi fun j => continuous_apply (i, j)
  refine ⟨{L | eval (e L) F ≠ 0}, ?_, ?_, fun L hLF => le_antisymm (hgood L hLF)
    (one_le_ringKrullDim_localRingAt_sliceIdeal J L q hloc)⟩
  · exact isOpen_ne_fun ((MvPolynomial.continuous_eval F).comp he) continuous_const
  · rw [dense_iff_inter_open]
    rintro U hU ⟨L₀, hL₀⟩
    obtain ⟨y, hyU, hyF⟩ := exists_eval_ne_zero_of_isOpen_pi hF (hU.preimage hψ) ⟨e L₀, hL₀⟩
    exact ⟨ψ y, hyU, hyF⟩

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCMProjDimCriterion
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing CategoryTheory RingTheory.Sequence

theorem exists_nat_eq_of_ne_bot_of_le {x : WithBot ℕ∞} {d : ℕ} (h0 : x ≠ ⊥) (hle : x ≤ (d : WithBot ℕ∞)) :
    ∃ e : ℕ, x = e := by
  induction x using WithBot.recBotCoe with
  | bot => exact absurd rfl h0
  | coe y =>
    have hy : y ≤ (d : ℕ∞) := by exact_mod_cast hle
    have hyt : y ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top d) hy
    exact ⟨y.toNat, by rw [← ENat.natCast_toNat hyt]; rfl⟩

theorem quotient_mk_mem_maximalIdeal {S : Type*} [CommRing S] [IsLocalRing S] {J : Ideal S}
    [IsLocalRing (S ⧸ J)] (hJ : J ≤ maximalIdeal S) {r : S} (hr : r ∈ maximalIdeal S) :
    Ideal.Quotient.mk J r ∈ maximalIdeal (S ⧸ J) := by
  rw [mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  obtain ⟨t, ht⟩ := hu.exists_right_inv
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective t
  have h1 : r * s - 1 ∈ J := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, ht, map_one, sub_self]
  have h2 : (1 : S) ∈ maximalIdeal S := by
    have := sub_mem ((maximalIdeal S).mul_mem_right s hr) (hJ h1)
    rwa [sub_sub_cancel] at this
  exact (maximalIdeal.isMaximal S).ne_top ((Ideal.eq_top_iff_one _).mpr h2)

theorem mem_maximalIdeal_of_quotient_mk {S : Type*} [CommRing S] [IsLocalRing S] {J : Ideal S}
    [IsLocalRing (S ⧸ J)] {r : S} (hr : Ideal.Quotient.mk J r ∈ maximalIdeal (S ⧸ J)) : r ∈ maximalIdeal S := by
  rw [mem_maximalIdeal, mem_nonunits_iff] at hr ⊢
  exact fun hu => hr (hu.map _)

theorem isCohenMacaulayLocalRing_quotient_iff_of_isRegularLocalRing
    (hlow : AuslanderBuchsbaumDepthLower.Statement.{0}) (hup : AuslanderBuchsbaumProjDimUpper.Statement.{0})
    (hlen : RegularSequenceLengthLeDim.Statement.{0}) (hcm : CMHeightAddDim.Statement.{0})
    {S : Type} [CommRing S] [IsRegularLocalRing S] (J : Ideal S) (hJm : J ≤ maximalIdeal S) :
    IsCohenMacaulayLocalRing (S ⧸ J) ↔
      ∃ ℓ : ℕ, HasProjectiveDimensionLE (ModuleCat.of S (S ⧸ J)) ℓ ∧ (ℓ : ℕ∞) ≤ J.height := by
  have hJ : J ≠ ⊤ := fun h => (maximalIdeal.isMaximal S).ne_top (top_le_iff.mp (h ▸ hJm))
  have : Nontrivial (S ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
  have : IsLocalRing (S ⧸ J) := .of_surjective' _ Ideal.Quotient.mk_surjective
  obtain ⟨rs0, hrs0, hofl, hlen0⟩ := GroundTheory.Arith.SchemeCoh.exists_isRegular_ofList_eq_maximalIdeal (R := S)
  have hrs0m : ∀ r ∈ rs0, r ∈ maximalIdeal S := fun r hr => hofl ▸ Ideal.subset_span hr
  set d := rs0.length with hd_def
  have hcmS : IsCohenMacaulayLocalRing S :=
    { exists_isWeaklyRegular := ⟨rs0, hrs0m, hrs0.toIsWeaklyRegular, hlen0.symm⟩ }
  have hsum := hcm S J hJ
  rw [← hlen0] at hsum
  obtain ⟨e, he⟩ := exists_nat_eq_of_ne_bot_of_le (x := ringKrullDim (S ⧸ J)) (d := d)
    (ringKrullDim_ne_bot) (hlen0 ▸ ringKrullDim_quotient_le J)
  have hht : J.height ≠ ⊤ := by
    intro h
    rw [h, he] at hsum
    have h2 : ((⊤ : ℕ∞) + e : ℕ∞) = d := by exact_mod_cast hsum
    simp at h2
  obtain ⟨h, hh⟩ : ∃ h : ℕ, J.height = h := ⟨J.height.toNat, (ENat.natCast_toNat hht).symm⟩
  have hhe : h + e = d := by
    rw [hh, he] at hsum; exact_mod_cast hsum
  have hserre : HasProjectiveDimensionLE (ModuleCat.of S (S ⧸ J)) d :=
    GroundTheory.Arith.SchemeCoh.hasProjectiveDimensionLT_of_isRegularLocalRing hlen0.symm (S ⧸ J)
  constructor
  · intro hCM
    obtain ⟨as, has_m, has_reg, has_len⟩ := hCM.exists_isWeaklyRegular
    obtain ⟨ms, hms⟩ : ∃ ms : List S, ms.map (algebraMap S (S ⧸ J)) = as :=
      ⟨as.map fun a => (Ideal.Quotient.mk_surjective a).choose, by
        rw [List.map_map]; conv_rhs => rw [← List.map_id as]
        exact List.map_congr_left fun a _ => (Ideal.Quotient.mk_surjective a).choose_spec⟩
    have hmsreg : IsWeaklyRegular (S ⧸ J) ms := by
      rw [← isWeaklyRegular_map_algebraMap_iff (S ⧸ J) (S ⧸ J) ms, hms]; exact has_reg
    have hmsm : ∀ r ∈ ms, r ∈ maximalIdeal S := fun r hr =>
      mem_maximalIdeal_of_quotient_mk (has_m _ (hms ▸ List.mem_map_of_mem hr))
    have hmslen : ms.length = e := by
      have : (as.length : WithBot ℕ∞) = e := has_len.symm.trans he
      rw [← hms, List.length_map] at this; exact_mod_cast this
    have hbound : ∀ rs : List S, (∀ r ∈ rs, r ∈ maximalIdeal S) → IsWeaklyRegular S rs → rs.length ≤ d :=
      fun rs hm hr => by have := hlen S rs hm hr; rw [← hlen0] at this; exact_mod_cast this
    refine ⟨d - e, ?_, ?_⟩
    · have := hup S (S ⧸ J) d d ms hserre hbound hmsm hmsreg
      rwa [hmslen] at this
    · rw [hh]; exact_mod_cast (by omega : d - e ≤ h)
  · rintro ⟨ℓ, hpd, hℓ⟩
    obtain ⟨ms, hmsm, hmsreg, hmslen⟩ := hlow S (S ⧸ J) ℓ rs0 hpd hrs0m hrs0.toIsWeaklyRegular
    have hℓh : ℓ ≤ h := by rw [hh] at hℓ; exact_mod_cast hℓ
    have hle : e ≤ ms.length := by rw [hmslen]; omega
    have hreg' : IsWeaklyRegular (S ⧸ J) (ms.take e) := by
      have := hmsreg; rw [← List.take_append_drop e ms] at this
      exact ((isWeaklyRegular_append_iff (S ⧸ J) _ _).mp this).1
    refine { exists_isWeaklyRegular := ⟨(ms.take e).map (algebraMap S (S ⧸ J)), ?_, ?_, ?_⟩ }
    · intro a ha
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ha
      exact quotient_mk_mem_maximalIdeal hJm (hmsm r (List.mem_of_mem_take hr))
    · exact (isWeaklyRegular_map_algebraMap_iff (S ⧸ J) (S ⧸ J) _).mpr hreg'
    · rw [he, List.length_map, List.length_take, min_eq_left hle]

theorem CMProjDimCriterion.proof (hlow : AuslanderBuchsbaumDepthLower.Statement.{0})
    (hup : AuslanderBuchsbaumProjDimUpper.Statement.{0}) (hlen : RegularSequenceLengthLeDim.Statement.{0})
    (hcm : CMHeightAddDim.Statement.{0}) : CMProjDimCriterion.Statement := by
  intro n I Q _ hIQ
  have : Algebra.Smooth ℂ (MvPolynomial (Fin n) ℂ) := {}
  have : IsRegularLocalRing (Localization.AtPrime Q) :=
    GroundTheory.Arith.SchemeCoh.isRegularLocalRing_localization_of_smooth ℂ (MvPolynomial (Fin n) ℂ) Q
  refine isCohenMacaulayLocalRing_quotient_iff_of_isRegularLocalRing hlow hup hlen hcm _ ?_
  rw [← Localization.AtPrime.map_eq_maximalIdeal]
  exact Ideal.map_mono hIQ

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCurveResidueDegree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

theorem CurveResidueDegree.proof : CurveResidueDegree.Statement := by
  intro n I q _ hdim P
  have := P.isMaximal
  let _ : Field (curveNormalisation I q ⧸ P.asIdeal) := Ideal.Quotient.field _

  have hO : Nontrivial (curveLocalRing I q) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    rw [ringKrullDim_eq_bot_of_subsingleton] at hdim
    exact absurd hdim (by decide)

  have hIq : ∀ g ∈ I, eval q g = 0 := by
    intro g hg
    by_contra hgq
    have hu := isUnit_algebraMap_curveLocalRing I q g hgq
    have h0 : algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) g = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ hg)
    rw [h0] at hu
    exact not_isUnit_zero hu

  let evL : Localization.AtPrime (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)) →+* ℂ :=
    IsLocalization.lift (M := (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)).primeCompl) (g := eval q)
      (fun s ↦ isUnit_iff_ne_zero.2 fun h ↦ s.2 (RingHom.mem_ker.2 h))
  have hJ : ∀ a ∈ I.map (algebraMap (MvPolynomial (Fin n) ℂ)
      (Localization.AtPrime (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)))), evL a = 0 := by
    intro a ha
    have hle : I.map (algebraMap (MvPolynomial (Fin n) ℂ)
        (Localization.AtPrime (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)))) ≤ RingHom.ker evL := by
      rw [Ideal.map_le_iff_le_comap]
      intro g hg
      simp [evL, IsLocalization.lift_eq, hIq g hg]
    exact hle ha
  let ε : curveLocalRing I q →+* ℂ := Ideal.Quotient.lift _ evL hJ
  let K := curveNormalisation I q ⧸ P.asIdeal
  let π : curveLocalRing I q →+* K := algebraMap (curveLocalRing I q) K
  let ι : ℂ →+* K := π.comp ((algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q)).comp C)

  have : Algebra.IsIntegral (curveLocalRing I q) (curveNormalisation I q) :=
    inferInstanceAs (Algebra.IsIntegral (curveLocalRing I q)
      ↥(integralClosure (curveLocalRing I q) (FractionRing (curveLocalRing I q))))
  have hmax : (P.asIdeal.comap (algebraMap (curveLocalRing I q) (curveNormalisation I q))).IsMaximal :=
    Ideal.isMaximal_under_of_isIntegral_of_isMaximal P.asIdeal
  have hmax' := Ideal.comap_isMaximal_of_surjective
    (Ideal.Quotient.mk (I.map (algebraMap (MvPolynomial (Fin n) ℂ)
      (Localization.AtPrime (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ))))))
    Ideal.Quotient.mk_surjective (K := P.asIdeal.comap (algebraMap (curveLocalRing I q) (curveNormalisation I q)))
    (H := hmax)
  have hloc := IsLocalRing.eq_maximalIdeal hmax'
  have hker : ∀ a ∈ RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ),
      π (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) a) = 0 := by
    intro a ha
    rw [← Localization.AtPrime.under_maximalIdeal (I := RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)),
      Ideal.under, Ideal.mem_comap, ← hloc] at ha
    exact Ideal.Quotient.eq_zero_iff_mem.2 ha

  have hcomp : π = ι.comp ε := by
    refine Ideal.Quotient.ringHom_ext ?_
    refine IsLocalization.ringHom_ext (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)).primeCompl ?_
    refine MvPolynomial.ringHom_ext (fun c ↦ ?_) (fun i ↦ ?_)
    · show π (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) (C c)) =
        ι (ε (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) (C c)))
      have he : ε (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) (C c)) = c := by
        show evL (algebraMap (MvPolynomial (Fin n) ℂ)
          (Localization.AtPrime (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ))) (C c)) = c
        simp [evL, IsLocalization.lift_eq]
      rw [he]
      rfl
    · have h1 : (X i - C (q i) : MvPolynomial (Fin n) ℂ) ∈ RingHom.ker (eval q) := by simp
      have h2 := hker _ h1
      rw [map_sub, map_sub, sub_eq_zero] at h2
      show π (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) (X i)) =
        ι (ε (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) (X i)))
      have he : ε (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) (X i)) = q i := by
        show evL (algebraMap (MvPolynomial (Fin n) ℂ)
          (Localization.AtPrime (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ))) (X i)) = q i
        simp [evL, IsLocalization.lift_eq]
      rw [he]
      exact h2

  have hint : ι.IsIntegral := by
    intro z
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
    have hb : IsIntegral (curveLocalRing I q) b := Algebra.IsIntegral.isIntegral b
    obtain ⟨p, hp, he⟩ := hb.map (Ideal.Quotient.mkₐ (curveLocalRing I q) P.asIdeal)
    refine ⟨p.map ε, hp.map ε, ?_⟩
    rw [Polynomial.eval₂_map, ← hcomp]
    exact he
  have hsurj : Function.Surjective ι := (IsAlgClosed.ringHom_bijective_of_isIntegral ι hint).2
  have hπ : Function.Surjective π := fun y ↦ by
    obtain ⟨c, hc⟩ := hsurj y
    exact ⟨_, hc⟩

  rw [Module.length_eq_one_iff, isSimpleModule_iff_toSpanSingleton_surjective]
  refine ⟨inferInstance, fun x hx y ↦ ?_⟩
  obtain ⟨r, hr⟩ := hπ (y * x⁻¹)
  refine ⟨r, ?_⟩
  rw [LinearMap.toSpanSingleton_apply, Algebra.smul_def]
  change π r * x = y
  rw [hr, mul_assoc, inv_mul_cancel₀ hx, mul_one]

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceLocalDimUpperZariski
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

noncomputable section

theorem SliceLocalDimUpperZariski.ringKrullDim_le_of_finite {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.Finite) : ringKrullDim S ≤ ringKrullDim R := by
  let _ := f.toAlgebra
  have : Module.Finite R S := hf
  have : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
  refine Order.krullDim_le_of_strictMono
    (fun p : PrimeSpectrum S => PrimeSpectrum.comap (algebraMap R S) p) ?_
  intro p p' h
  have h' : p.asIdeal < p'.asIdeal := h
  exact Ideal.IsIntegral.comap_lt_comap (R := R) h'

theorem SliceLocalDimUpperZariski.localDim_le {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ))
    (q : Fin n → ℂ) (hq : q ∈ zeroSet I) :
    ringKrullDim (localRingAt I q) ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) := by
  set M : Ideal (MvPolynomial (Fin n) ℂ) := RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)
  have hIM : I ≤ M := fun f hf => RingHom.mem_ker.mpr (hq f hf)
  let m : Ideal (MvPolynomial (Fin n) ℂ ⧸ I) := M.map (Ideal.Quotient.mk I)
  have hm : m.IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hIM)
  have hsub : Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) ℂ ⧸ I) M.primeCompl =
      m.primeCompl := by
    ext x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    constructor
    · rintro ⟨z, hz, hzy⟩
      change Ideal.Quotient.mk I y ∉ m
      rw [← hzy]
      change Ideal.Quotient.mk I z ∉ M.map (Ideal.Quotient.mk I)
      rw [Ideal.mem_quotient_iff_mem hIM]
      exact hz
    · intro h
      change Ideal.Quotient.mk I y ∉ M.map (Ideal.Quotient.mk I) at h
      rw [Ideal.mem_quotient_iff_mem hIM] at h
      exact ⟨y, h, rfl⟩
  have : m.IsPrime := hm.isPrime
  have : IsLocalization.AtPrime (localRingAt I q) m := by
    unfold IsLocalization.AtPrime
    rw [← hsub]
    unfold localRingAt
    infer_instance
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height m (localRingAt I q)]
  exact Ideal.height_le_ringKrullDim_of_isPrime

theorem SliceLocalDimUpperZariski.quotient_dim_le_one {n d : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ))
    (L : Matrix (Fin d) (Fin n) ℂ) (q : Fin n → ℂ) (M : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (hML : ∀ i j, M (Fin.castSucc i) j = L i j) (hfin : (projHom J M).toRingHom.Finite) :
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ sliceIdeal J L q) ≤ (1 : ℕ) := by
  set I := sliceIdeal J L q with hI
  have hJI : J ≤ I := le_sup_left
  let g : MvPolynomial (Fin (d + 1)) ℂ →+* MvPolynomial (Fin n) ℂ ⧸ I :=
    (Ideal.Quotient.factor hJI).comp (projHom J M).toRingHom
  have hg : g.Finite :=
    RingHom.Finite.comp (RingHom.Finite.of_surjective _ (Ideal.Quotient.factor_surjective hJI)) hfin
  let π : MvPolynomial (Fin (d + 1)) ℂ →+* Polynomial ℂ :=
    (aeval (Fin.lastCases (motive := fun _ => Polynomial ℂ) Polynomial.X
      (fun k => Polynomial.C ((L *ᵥ q) k)))).toRingHom
  let ψ : Polynomial ℂ →+* MvPolynomial (Fin n) ℂ ⧸ I :=
    Polynomial.eval₂RingHom (algebraMap ℂ _) (Ideal.Quotient.mk I (linPoly M (Fin.last d)))
  have hlin : ∀ k : Fin d, linPoly M k.castSucc = linPoly L k := by
    intro k
    simp only [linPoly, hML]
  have hCI : ∀ c : ℂ, algebraMap ℂ (MvPolynomial (Fin n) ℂ ⧸ I) c = Ideal.Quotient.mk I (C c) :=
    fun c => rfl
  have hcomp : ψ.comp π = g := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [π, ψ, g, projHom, pullback, hCI]
    · intro i
      refine Fin.lastCases ?_ (fun k => ?_) i
      · simp [π, ψ, g, projHom, pullback]
      · have hmem : linPoly L k - C ((L *ᵥ q) k) ∈ I :=
          Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩)
        have hq : Ideal.Quotient.mk I (linPoly L k) = Ideal.Quotient.mk I (C ((L *ᵥ q) k)) :=
          Ideal.Quotient.eq.mpr hmem
        simp [π, ψ, g, projHom, pullback, hlin, hq, hCI]
  have hψ : ψ.Finite := RingHom.Finite.of_comp_finite (f := π) (by rw [hcomp]; exact hg)
  calc ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) ≤ ringKrullDim (Polynomial ℂ) :=
        SliceLocalDimUpperZariski.ringKrullDim_le_of_finite ψ hψ
    _ = (1 : ℕ) := by
        rw [Polynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
        rfl

theorem SliceLocalDimUpperZariski.proof : SliceLocalDimUpperZariski.Statement := by
  intro n d J q hJ hdim hq
  obtain ⟨W, ⟨S, hS⟩, ⟨A₀, hA₀⟩, hWfin⟩ :=
    ComplexSets.FiniteProjectionsContainOpen.proof ComplexSets.ConeAvoidsFinite.proof
      ComplexSets.FiniteProjHomInjective.proof ComplexSets.ConeAvoidsOpen.proof
      (ComplexSets.ConeAvoidsExists.proof ComplexSets.LeadIdealDim.proof
        ComplexSets.LinearFormCut.proof ComplexSets.HomogDimZeroPow.proof) n (d + 1) J hJ hdim
  rw [hS] at hA₀
  obtain ⟨G, hGS, hG⟩ := hA₀
  let ext : Matrix (Fin d) (Fin n) ℂ → Matrix (Fin (d + 1)) (Fin n) ℂ :=
    fun L i j => if h : (i : ℕ) < d then L ⟨i, h⟩ j else A₀ i j
  let F : MvPolynomial (Fin d × Fin n) ℂ :=
    bind₁ (fun ij : Fin (d + 1) × Fin n =>
      if h : (ij.1 : ℕ) < d then X (⟨ij.1, h⟩, ij.2) else C (A₀ ij.1 ij.2)) G
  have hevF : ∀ L : Matrix (Fin d) (Fin n) ℂ,
      eval (fun ij : Fin d × Fin n => L ij.1 ij.2) F =
        eval (fun ij : Fin (d + 1) × Fin n => ext L ij.1 ij.2) G := by
    intro L
    change eval₂Hom (RingHom.id ℂ) _ (bind₁ _ G) = _
    rw [eval₂Hom_bind₁]
    change eval _ G = _
    refine congrArg (fun f => eval f G) (funext fun ij => ?_)
    simp only [ext]
    split_ifs <;> simp
  have hext0 : ext (fun i j => A₀ i.castSucc j) = A₀ := by
    funext i j
    simp only [ext]
    split_ifs with h
    · rfl
    · rfl
  refine ⟨F, fun h0 => hG ?_, fun L hL => ?_⟩
  · have h1 := hevF (fun i j => A₀ i.castSucc j)
    rw [hext0, h0, map_zero] at h1
    exact h1.symm
  · have hmem : ext L ∈ W := by
      rw [hS]
      exact ⟨G, hGS, (hevF L) ▸ hL⟩
    have hfp : IsFiniteProjection J (ext L) := hWfin hmem
    have hq' : q ∈ zeroSet (sliceIdeal J L q) := by
      rw [zeroSet_sliceIdeal]
      exact ⟨hq, rfl⟩
    refine (SliceLocalDimUpperZariski.localDim_le _ q hq').trans
      (SliceLocalDimUpperZariski.quotient_dim_le_one J L q (ext L) (fun i j => ?_) hfp.finite)
    simp [ext, i.isLt]

end

end GroundTheory.Heights₂.Heights
end
