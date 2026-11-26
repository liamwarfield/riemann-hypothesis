module

public import GroundTheory.AutomorphicForms.PartialDifferential.EllipticLocal

@[expose] public section

section -- merged from GroundTheory.AutomorphicForms.PartialDifferential.EllipticLocalRegularity
namespace GroundTheory.Automorphic.Sobolev

open TemperedDistribution MeasureTheory FourierTransform LineDeriv
open scoped SchwartzMap ENNReal ContDiff

noncomputable section

set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem norm_symb0 {ι : Type*} [Fintype ι] {m : ℕ} (c : ι → ℂ) (w : ι → Fin m → E) (ξ : E) :
    ‖symb0 c w ξ‖ = (2 * Real.pi) ^ m * ‖prinSymb c w ξ‖ := by
  rw [symb0, norm_mul, norm_pow, norm_mul, Complex.norm_I, mul_one, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg Real.pi_pos.le]
  norm_num

theorem exists_symb0_bounds {ι : Type*} [Fintype ι] {m : ℕ} (hm : 1 ≤ m) (c : ι → ℂ)
    (w : ι → Fin m → E) (hell : ∀ ξ : E, ξ ≠ 0 → prinSymb c w ξ ≠ 0) :
    ∃ cl Cu : ℝ, 0 < cl ∧ 0 ≤ Cu ∧ (∀ ξ, cl * ‖ξ‖ ^ m ≤ ‖symb0 c w ξ‖) ∧
      ∀ ξ, ‖symb0 c w ξ‖ ≤ Cu * ‖ξ‖ ^ m := by
  obtain ⟨c₀, hc₀, hlow⟩ := exists_pos_le_norm_prinSymb hm c w hell
  refine ⟨(2 * Real.pi) ^ m * c₀, (2 * Real.pi) ^ m * ∑ i, ‖c i‖ * ∏ j, ‖w i j‖, by positivity,
    by positivity, fun ξ ↦ ?_, fun ξ ↦ ?_⟩
  · rw [norm_symb0, mul_assoc]; gcongr; exact hlow ξ
  · rw [norm_symb0, mul_assoc]; gcongr; exact norm_prinSymb_le c w ξ

def bumpGR (x₀ : E) {r R : ℝ} (hr : 0 < r) (hrR : r < R) : ContDiffBump x₀ := ⟨r, R, hr, hrR⟩

def bumpG (x₀ : E) {r R : ℝ} (hr : 0 < r) (hrR : r < R) : 𝓢(E, ℂ) :=
  have h₁ : HasCompactSupport (Complex.ofRealCLM ∘ (bumpGR x₀ hr hrR : E → ℝ)) :=
    (bumpGR x₀ hr hrR).hasCompactSupport.comp_left rfl
  have h₂ : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ (bumpGR x₀ hr hrR : E → ℝ)) :=
    Complex.ofRealCLM.contDiff.comp (bumpGR x₀ hr hrR).contDiff
  h₁.toSchwartzMap h₂

theorem bumpG_apply (x₀ : E) {r R : ℝ} (hr : 0 < r) (hrR : r < R) (x : E) :
    bumpG x₀ hr hrR x = ((bumpGR x₀ hr hrR x : ℝ) : ℂ) := rfl

theorem bumpG_eq_one (x₀ : E) {r R : ℝ} (hr : 0 < r) (hrR : r < R) {x : E}
    (hx : x ∈ Metric.closedBall x₀ r) : bumpG x₀ hr hrR x = 1 := by
  rw [bumpG_apply, (bumpGR x₀ hr hrR).one_of_mem_closedBall hx, Complex.ofReal_one]

theorem tsupport_bumpG (x₀ : E) {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    tsupport (bumpG x₀ hr hrR : E → ℂ) ⊆ Metric.closedBall x₀ R := by
  have : (bumpG x₀ hr hrR : E → ℂ) = Complex.ofRealCLM ∘ (bumpGR x₀ hr hrR : E → ℝ) := rfl
  rw [this]
  refine (tsupport_comp_subset (g := Complex.ofRealCLM) (by simp) _).trans ?_
  rw [(bumpGR x₀ hr hrR).tsupport_eq]; rfl

theorem IsEllipticAt.exists_data {T : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)} {m : ℕ} {x₀ : E}
    (hT : IsEllipticAt T m x₀) (hm : 1 ≤ m) :
    ∃ (n : ℕ) (a : Fin n → 𝓢(E, ℂ)) (w : Fin n → Fin m → E) (N : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)),
      T = prinOp a w + N ∧ HasOrder N ((m : ℝ) - 1) ∧ IsLocal N ∧
      ∃ cl Cu : ℝ, 0 < cl ∧ 0 ≤ Cu ∧ (∀ ξ, cl * ‖ξ‖ ^ m ≤ ‖symb0 (fun i ↦ a i x₀) w ξ‖) ∧
        ∀ ξ, ‖symb0 (fun i ↦ a i x₀) w ξ‖ ≤ Cu * ‖ξ‖ ^ m := by
  obtain ⟨n, a, w, N, hTeq, hN, hNl, hell⟩ := hT
  exact ⟨n, a, w, N, hTeq, hN, hNl, exists_symb0_bounds hm _ w hell⟩

theorem IsEllipticAt.exists_regularity_radius {T : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)} {m : ℕ} {x₀ : E}
    (hT : IsEllipticAt T m x₀) (hm : 1 ≤ m) :
    ∃ δ > 0, ∀ (s : ℝ) (u : 𝓢'(E, ℂ)), MemSobolev s 2 u →
      (∃ ρ < δ, Distribution.IsVanishingOn u (Metric.closedBall x₀ ρ)ᶜ) →
      MemSobolev (s - m + 1) 2 (T u) → MemSobolev (s + 1) 2 u := by
  obtain ⟨n, a, w, N, rfl, hN, hNl, cl, Cu, hcl, hCu, hlow, hup⟩ := hT.exists_data hm
  obtain ⟨δ, hδ, hsmall⟩ := exists_small a w N x₀ hcl hCu hlow hup hm hN 1
  refine ⟨δ, hδ, fun s u hu ⟨ρ, hρ, hvan⟩ hTu ↦ ?_⟩
  obtain ⟨μ, hμ0, hμ1, hK⟩ := hsmall {s, s + 1}
  have hKs := (hK s (by simp)).1
  have hKs1 := (hK (s + 1) (by simp)).1
  set K := Qop a w x₀ μ 1 ∘L locM a w N x₀ hδ

  have hTu' : (prinOp a w + N) u = P0 a w x₀ u + locM a w N x₀ hδ u :=
    prinOp_add_apply_eq a w N x₀ hNl hδ hρ hvan
  have hid : u + K u = Qop a w x₀ μ 1 ((prinOp a w + N) u) + Rop a w x₀ μ 1 u := by
    have h1 := congrArg (fun A : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ) ↦ A u) (parametrix_comp_frozenOperator a w x₀ hμ0.le 1)
    simp only [ContinuousLinearMap.comp_apply, sub_apply, ContinuousLinearMap.id_apply] at h1
    rw [hTu', map_add (f := _), h1]
    simp only [K, ContinuousLinearMap.comp_apply]
    abel
  have hz : MemSobolev (s + 1) 2 (Qop a w x₀ μ 1 ((prinOp a w + N) u) + Rop a w x₀ μ 1 u) := by
    have h1 := (opBound_Qop a w x₀ hcl hCu hlow hup hμ0.le hμ1 1 (s + 1)).memSobolev
      (u := (prinOp a w + N) u) (by convert hTu using 2; ring)
    have h2 := (opBound_Rop a w x₀ hcl hCu hlow hup hμ0 1 s).memSobolev hu
    refine h1.add (h2.mono ?_)
    have : (1 : ℝ) ≤ ((2 * m * 1 : ℕ) : ℝ) := by
      have : 1 ≤ 2 * m * 1 := by omega
      exact_mod_cast this
    linarith
  obtain ⟨v, hv, hvK⟩ := exists_add_eq_of_opBound hKs1 hz
  have hdiff : (u - v) + K (u - v) = 0 := by
    rw [map_sub, show u - v + (K u - K v) = (u + K u) - (v + K v) by abel, hid, hvK, sub_self]
  have h0 := eq_zero_of_add_eq_zero hKs (hu.sub (hv.mono (by linarith))) hdiff
  rw [sub_eq_zero] at h0
  rw [h0]; exact hv

theorem isVanishingOn_prinOp_add_sub {m n : ℕ} (a : Fin n → 𝓢(E, ℂ)) (w : Fin n → Fin m → E)
    (N : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)) (x₀ : E) {δ : ℝ} (hδ : 0 < δ) (u : 𝓢'(E, ℂ)) :
    Distribution.IsVanishingOn ((prinOp a w + N) u - (P0 a w x₀ u + locM a w N x₀ hδ u))
      (Metric.ball x₀ δ) := by
  have hb : ∀ z : 𝓢'(E, ℂ), Distribution.IsVanishingOn
      (z - smulLeftCLM ℂ (bump x₀ hδ : E → ℂ) z) (Metric.ball x₀ δ) := fun z ↦ by
    have := isVanishingOn_smulLeftCLM_sub (bump x₀ hδ).hasTemperateGrowth
      (V := Metric.ball x₀ δ) (fun x hx ↦ bump_eq_one x₀ hδ (Metric.ball_subset_closedBall hx)) z
    have h2 := isVanishingOn_neg this
    rwa [neg_sub] at h2
  have e : (prinOp a w + N) u - (P0 a w x₀ u + locM a w N x₀ hδ u) =
      ∑ i, ((smulLeftCLM ℂ (a i : E → ℂ) (∂^{w i} u) -
          smulLeftCLM ℂ (bump x₀ hδ : E → ℂ) (smulLeftCLM ℂ (a i : E → ℂ) (∂^{w i} u))) -
        a i x₀ • (∂^{w i} u - smulLeftCLM ℂ (bump x₀ hδ : E → ℂ) (∂^{w i} u))) +
      (N u - smulLeftCLM ℂ (bump x₀ hδ : E → ℂ) (N u)) := by
    simp only [add_apply, locM, P0, prinOp, constOp, sum_apply, ContinuousLinearMap.comp_apply,
      smul_apply, iteratedLineDerivOpCLM_apply, locCoeff, smulLeftCLM_schwartz_sub_smul,
      smulLeftCLM_schwartz_mul, smul_sub]
    simp only [Finset.sum_sub_distrib]
    abel
  rw [e]
  have hsum : ∀ S : Finset (Fin n), Distribution.IsVanishingOn ((∑ i ∈ S,
      ((smulLeftCLM ℂ (a i : E → ℂ) (∂^{w i} u) -
          smulLeftCLM ℂ (bump x₀ hδ : E → ℂ) (smulLeftCLM ℂ (a i : E → ℂ) (∂^{w i} u))) -
        a i x₀ • (∂^{w i} u - smulLeftCLM ℂ (bump x₀ hδ : E → ℂ) (∂^{w i} u))) : 𝓢'(E, ℂ)))
      (Metric.ball x₀ δ) := by
    intro S
    classical
    induction S using Finset.induction_on with
    | empty => simpa using isVanishingOn_zero _
    | insert i S hi ih =>
      rw [Finset.sum_insert hi]
      exact isVanishingOn_add (isVanishingOn_sub (hb _) (isVanishingOn_smul _ (hb _))) ih
  exact isVanishingOn_add (hsum _) (hb _)

theorem memSobolev_delta (x₀ : E) {t : ℝ} (ht : t < -(Module.finrank ℝ E : ℝ) / 2) :
    MemSobolev t 2 (TemperedDistribution.delta x₀ : 𝓢'(E, ℂ)) := by
  rw [memSobolev_iff_fourier]
  refine ⟨fun ξ ↦ ((𝐞 (-inner ℝ ξ x₀) : Circle) : ℂ), ?_, fun φ ↦ ?_⟩
  · have hint := integrable_rpow_neg_one_add_norm_sq (E := E) (μ := (volume : Measure E))
      (r := -2 * t) (by linarith)
    have hmeas : AEStronglyMeasurable (fun ξ : E ↦ weight t ξ • ((𝐞 (-inner ℝ ξ x₀) : Circle) : ℂ))
        volume :=
      ((weight_hasTemperateGrowth (E := E) t).1.continuous.smul (by fun_prop)).aestronglyMeasurable
    rw [memLp_two_iff_integrable_sq_norm hmeas]
    refine hint.congr (ae_of_all _ fun ξ ↦ ?_)
    simp only [smul_eq_mul, norm_mul, Circle.norm_coe, mul_one, norm_weight]
    rw [← Real.rpow_natCast ((1 + ‖ξ‖ ^ 2) ^ (t / 2)) 2, ← Real.rpow_mul (by positivity)]
    congr 1; push_cast; ring
  · rw [TemperedDistribution.fourier_apply, TemperedDistribution.delta_apply,
      SchwartzMap.fourier_coe, Real.fourier_eq]
    congr 1; ext v
    rw [Circle.smul_def, smul_eq_mul, smul_eq_mul, mul_comm]

theorem exists_add_eq_of_opBound_lt {K : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)} {s c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hK : OpBound K s s c) {z : 𝓢'(E, ℂ)} (hz : MemSobolev s 2 z) :
    ∃ v, MemSobolev s 2 v ∧ v + K v = z := by
  have hmem : ∀ v : SobolevSpace E ℂ s, MemSobolev s 2 (z - K (SobolevSpace.toDistribution v)) :=
    fun v ↦ (SobolevSpace.exists_toDistribution_eq_iff _).1
      ⟨SobolevSpace.mk z hz - SobolevSpace.mk _ (hK.memSobolev (SobolevSpace.memSobolev_toDistribution v)),
        by simp⟩
  let f : SobolevSpace E ℂ s → SobolevSpace E ℂ s := fun v ↦ SobolevSpace.mk _ (hmem v)
  have hf : ContractingWith c.toNNReal f := by
    refine ⟨by rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hc0]; exact hc1,
      LipschitzWith.of_dist_le_mul fun v v' ↦ ?_⟩
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hc0]
    have e : f v - f v' = SobolevSpace.mk (K (SobolevSpace.toDistribution (v' - v)))
        (hK.memSobolev (SobolevSpace.memSobolev_toDistribution _)) := by
      apply SobolevSpace.toDistribution_injective
      simp [f, map_sub]
    rw [e]
    have h := hK _ (SobolevSpace.memSobolev_toDistribution (v' - v))
    rw [sob_of_mem (hK.memSobolev (SobolevSpace.memSobolev_toDistribution _)), sob_toDistribution,
      ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul hc0] at h
    have h' := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h
    rw [norm_sub_rev] at h'
    exact h'
  obtain ⟨v, hv⟩ : ∃ v, f v = v := ⟨_, hf.fixedPoint_isFixedPt (f := f)⟩
  refine ⟨SobolevSpace.toDistribution v, SobolevSpace.memSobolev_toDistribution v, ?_⟩
  have := congrArg SobolevSpace.toDistribution hv
  simp only [f, SobolevSpace.toDistribution_mk] at this
  exact eq_sub_iff_add_eq.1 this.symm

theorem OpBound.neg {A : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)} {s t C : ℝ} (h : OpBound A s t C) :
    OpBound (-A) s t C := fun u hu ↦ by rw [neg_apply, sob_neg]; exact h u hu

theorem OpBound.sub {A B : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)} {s t C D : ℝ} (hA : OpBound A s t C)
    (hB : OpBound B s t D) (hC : 0 ≤ C) (hD : 0 ≤ D) : OpBound (A - B) s t (C + D) := by
  rw [sub_eq_add_neg]; exact hA.add hB.neg hC hD

theorem lintegral_mul_le_eLpNorm_mul (f g : E → ℂ) (hf : AEMeasurable (fun x ↦ ‖f x‖ₑ) volume)
    (hg : AEMeasurable (fun x ↦ ‖g x‖ₑ) volume) :
    ∫⁻ x, ‖f x‖ₑ * ‖g x‖ₑ ≤ eLpNorm f 2 volume * eLpNorm g 2 volume := by
  have norm_le (u : E → ℂ) : eLpNorm' u 2 volume ≤ eLpNorm u 2 volume := by
    by_cases hu : AEStronglyMeasurable u volume
    · simp [eLpNorm_eq_eLpNorm' two_ne_zero ENNReal.ofNat_ne_top hu]
    · rw [eLpNorm_of_not_aestronglyMeasurable hu]
      exact le_top
  have h := L2Kernel.lintegral_mul_sq_le (volume : Measure E) hf hg
  rw [← L2Kernel.eLpNorm_two_sq, ← L2Kernel.eLpNorm_two_sq, ← mul_pow] at h
  exact ((ENNReal.pow_le_pow_left_iff two_ne_zero).1 h).trans (mul_le_mul' (norm_le f) (norm_le g))

theorem norm_ofSchwartz_smulLeft_fourierMultiplier_le (χ : 𝓢(E, ℂ)) {g : E → ℂ}
    (hg : g.HasTemperateGrowth) (t : ℝ) (hA : MemLp (weight t : E → ℂ) 2 volume)
    (hB : MemLp (fun ξ ↦ g ξ * weight (-t) ξ) 2 volume) (φ : 𝓢(E, ℂ)) :
    ‖SobolevSpace.ofSchwartz t (SchwartzMap.smulLeftCLM ℂ (χ : E → ℂ)
        (SchwartzMap.fourierMultiplierCLM ℂ g φ))‖ ≤
      ((∫ x, ‖χ x‖) * (eLpNorm (weight t : E → ℂ) 2 volume).toReal *
        (eLpNorm (fun ξ ↦ g ξ * weight (-t) ξ) 2 volume).toReal) * ‖SobolevSpace.ofSchwartz t φ‖ := by
  set ψ := SchwartzMap.fourierMultiplierCLM ℂ g φ
  have hψ : ∀ η, (𝓕 ψ : 𝓢(E, ℂ)) η = (g η * weight (-t) η) * (weight t η * (𝓕 φ : 𝓢(E, ℂ)) η) := by
    intro η
    rw [show ψ = SchwartzMap.fourierMultiplierCLM ℂ g φ from rfl,
      SchwartzMap.fourierMultiplierCLM_apply, FourierTransform.fourier_fourierInv_eq,
      SchwartzMap.smulLeftCLM_apply_apply hg, smul_eq_mul]
    have : weight (-t) η * weight t η = 1 := by
      rw [weight_mul_weight, neg_add_cancel]; simp [weight]
    calc g η * (𝓕 φ : 𝓢(E, ℂ)) η = g η * (weight (-t) η * weight t η) * (𝓕 φ : 𝓢(E, ℂ)) η := by
          rw [this, mul_one]
      _ = _ := by ring
  set Cst : ℝ≥0∞ := ENNReal.ofReal (∫ x, ‖χ x‖) * eLpNorm (fun ξ ↦ g ξ * weight (-t) ξ) 2 volume *
    eLpNorm (fun ξ ↦ weight t ξ * (𝓕 φ : 𝓢(E, ℂ)) ξ) 2 volume
  have hCst : Cst ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hB.eLpNorm_ne_top)
    (eLpNorm_weight_fourier_lt_top t φ).ne
  have hpt : ∀ ξ, ‖weight t ξ * (𝓕 (SchwartzMap.smulLeftCLM ℂ (χ : E → ℂ) ψ) : 𝓢(E, ℂ)) ξ‖ₑ ≤
      ‖(Cst.toReal : ℂ) * weight t ξ‖ₑ := by
    intro ξ
    rw [enorm_mul, enorm_mul, fourier_smulLeftCLM_apply, ← ofReal_norm (Cst.toReal : ℂ),
      Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hCst,
      mul_comm Cst]
    gcongr
    calc ‖∫ η, (𝓕 χ : 𝓢(E, ℂ)) (ξ - η) * (𝓕 ψ : 𝓢(E, ℂ)) η‖ₑ
        ≤ ∫⁻ η, ‖(𝓕 χ : 𝓢(E, ℂ)) (ξ - η) * (𝓕 ψ : 𝓢(E, ℂ)) η‖ₑ :=
          enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ η, ENNReal.ofReal (∫ x, ‖χ x‖) * (‖g η * weight (-t) η‖ₑ *
            ‖weight t η * (𝓕 φ : 𝓢(E, ℂ)) η‖ₑ) := by
          refine lintegral_mono fun η ↦ ?_
          rw [enorm_mul, hψ, enorm_mul]
          gcongr
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (norm_fourier_le_integral χ _)
      _ = ENNReal.ofReal (∫ x, ‖χ x‖) * ∫⁻ η, ‖g η * weight (-t) η‖ₑ *
            ‖weight t η * (𝓕 φ : 𝓢(E, ℂ)) η‖ₑ := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal (∫ x, ‖χ x‖) * (eLpNorm (fun ξ ↦ g ξ * weight (-t) ξ) 2 volume *
            eLpNorm (fun ξ ↦ weight t ξ * (𝓕 φ : 𝓢(E, ℂ)) ξ) 2 volume) := by
          gcongr
          exact lintegral_mul_le_eLpNorm_mul _ _ hB.aestronglyMeasurable.enorm
            (measurable_weight_mul_fourier t φ).enorm.aemeasurable
      _ = Cst := by rw [← mul_assoc]
  have hle := eLpNorm_mono_eNorm (measurable_weight_mul_fourier t _).aestronglyMeasurable hpt (p := 2) (μ := (volume : Measure E))
  rw [show (fun ξ ↦ (Cst.toReal : ℂ) * weight t ξ) = (Cst.toReal : ℂ) • (weight t : E → ℂ) from rfl,
    eLpNorm_const_smul, ← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal hCst] at hle
  rw [norm_ofSchwartz_eq, norm_ofSchwartz_eq]
  calc _ ≤ (Cst * eLpNorm (weight t : E → ℂ) 2 volume).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top hCst hA.eLpNorm_ne_top) hle
    _ = _ := by
        simp only [Cst, ENNReal.toReal_mul, ENNReal.toReal_ofReal (integral_nonneg fun x ↦ norm_nonneg _)]
        ring

theorem opBound_smulLeft_fourierMultiplier (χ : 𝓢(E, ℂ)) {g : E → ℂ} (hg : g.HasTemperateGrowth)
    (t : ℝ) (hA : MemLp (weight t : E → ℂ) 2 volume)
    (hB : MemLp (fun ξ ↦ g ξ * weight (-t) ξ) 2 volume) :
    OpBound (smulLeftCLM ℂ (χ : E → ℂ) ∘L fourierMultiplierCLM ℂ g) t t
      ((∫ x, ‖χ x‖) * (eLpNorm (weight t : E → ℂ) 2 volume).toReal *
        (eLpNorm (fun ξ ↦ g ξ * weight (-t) ξ) 2 volume).toReal) := by
  intro u hu
  refine sob_le_of_schwartz _ (by positivity) (fun φ ↦ ?_) hu
  rw [ContinuousLinearMap.comp_apply, fourierMultiplierCLM_toTemperedDistributionCLM_eq hg,
    smulLeftCLM_coe, sob_ofSchwartz, sob_ofSchwartz, ← ofReal_norm, ← ofReal_norm,
    ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal
    (norm_ofSchwartz_smulLeft_fourierMultiplier_le χ hg t hA hB φ)

theorem integral_norm_bump_le (x₀ : E) {r : ℝ} (hr : 0 < r) :
    ∫ x, ‖bump x₀ hr x‖ ≤ volume.real (Metric.closedBall x₀ (2 * r)) := by
  rw [← integral_indicator_one Metric.isClosed_closedBall.measurableSet]
  refine integral_mono (bump x₀ hr).integrable.norm ?_ fun x ↦ ?_
  · exact (integrable_indicator_iff Metric.isClosed_closedBall.measurableSet).2
      (integrableOn_const (measure_closedBall_lt_top).ne)
  · by_cases hx : x ∈ Metric.closedBall x₀ (2 * r)
    · rw [Set.indicator_of_mem hx]; exact norm_bump_le x₀ hr x
    · rw [Set.indicator_of_notMem hx, bump_eq_zero x₀ hr hx, norm_zero]

theorem exists_bump_small [Nontrivial E] (x₀ : E) {C r₀ : ℝ} (hC : 0 ≤ C) (hr₀ : 0 < r₀) :
    ∃ r, ∃ hr : 0 < r, r ≤ r₀ ∧ (∫ x, ‖bump x₀ hr x‖) * C ≤ 1 / 4 := by
  set V := volume.real (Metric.ball (0 : E) 1)
  have hV : 0 ≤ V := measureReal_nonneg
  set r := min r₀ (min (1 / 2) (1 / (8 * (C + 1) * (V + 1))))
  have hr : 0 < r := lt_min hr₀ (lt_min (by norm_num) (by positivity))
  refine ⟨r, hr, min_le_left _ _, ?_⟩
  have hr2 : 2 * r ≤ 1 := by
    have : r ≤ 1 / 2 := (min_le_right _ _).trans (min_le_left _ _)
    linarith
  have hr3 : r ≤ 1 / (8 * (C + 1) * (V + 1)) := (min_le_right _ _).trans (min_le_right _ _)
  have hn : 1 ≤ Module.finrank ℝ E := Module.finrank_pos
  have hvol : volume.real (Metric.closedBall x₀ (2 * r)) ≤ 2 * r * V := by
    rw [Measure.addHaar_real_closedBall _ _ (by linarith)]
    gcongr
    calc (2 * r) ^ Module.finrank ℝ E ≤ (2 * r) ^ 1 := pow_le_pow_of_le_one (by linarith) hr2 hn
      _ = 2 * r := pow_one _
  calc (∫ x, ‖bump x₀ hr x‖) * C ≤ (2 * r * V) * C := by
        gcongr; exact (integral_norm_bump_le x₀ hr).trans hvol
    _ ≤ (2 * (1 / (8 * (C + 1) * (V + 1))) * V) * C := by gcongr
    _ = (1 / 4) * ((V / (V + 1)) * (C / (C + 1))) := by field_simp; ring
    _ ≤ (1 / 4) * (1 * 1) := by
        gcongr
        · rw [div_le_one (by linarith)]; linarith
        · rw [div_le_one (by linarith)]; linarith
    _ = 1 / 4 := by ring

theorem memLp_weight {t : ℝ} (ht : t < -(Module.finrank ℝ E : ℝ) / 2) :
    MemLp (weight t : E → ℂ) 2 volume := by
  have hint := integrable_rpow_neg_one_add_norm_sq (E := E) (μ := (volume : Measure E))
    (r := -2 * t) (by linarith)
  have hmeas : AEStronglyMeasurable (weight t : E → ℂ) volume :=
    (weight_hasTemperateGrowth (E := E) t).1.continuous.aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  refine hint.congr (ae_of_all _ fun ξ ↦ ?_)
  simp only [norm_weight]
  rw [← Real.rpow_natCast ((1 + ‖ξ‖ ^ 2) ^ (t / 2)) 2, ← Real.rpow_mul (by positivity)]
  congr 1; push_cast; ring

theorem memLp_mul_weight {g : E → ℂ} (hg : g.HasTemperateGrowth) {t K : ℝ} {j : ℕ}
    (hj : (Module.finrank ℝ E : ℝ) < 2 * j + 2 * t)
    (hbound : ∀ ξ, ‖g ξ‖ ≤ K * (1 + ‖ξ‖ ^ 2) ^ (-(j : ℝ) / 2)) :
    MemLp (fun ξ ↦ g ξ * weight (-t) ξ) 2 volume := by
  have hint := (integrable_rpow_neg_one_add_norm_sq (E := E) (μ := (volume : Measure E))
    (r := 2 * j + 2 * t) hj).const_mul (K ^ 2)
  have hmeas : AEStronglyMeasurable (fun ξ ↦ g ξ * weight (-t) ξ) volume :=
    (hg.1.continuous.mul (weight_hasTemperateGrowth (E := E) (-t)).1.continuous).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  refine hint.mono' (hmeas.norm.pow 2) (ae_of_all _ fun ξ ↦ ?_)
  have hp : (0 : ℝ) < 1 + ‖ξ‖ ^ 2 := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_mul, norm_weight, mul_pow]
  calc ‖g ξ‖ ^ 2 * ((1 + ‖ξ‖ ^ 2) ^ (-t / 2)) ^ 2
      ≤ (K * (1 + ‖ξ‖ ^ 2) ^ (-(j : ℝ) / 2)) ^ 2 * ((1 + ‖ξ‖ ^ 2) ^ (-t / 2)) ^ 2 := by
        gcongr; exact hbound ξ
    _ = K ^ 2 * (1 + ‖ξ‖ ^ 2) ^ (-(2 * j + 2 * t) / 2) := by
        rw [mul_pow, mul_assoc, ← Real.rpow_natCast ((1 + ‖ξ‖ ^ 2) ^ (-(j : ℝ) / 2)) 2,
          ← Real.rpow_natCast ((1 + ‖ξ‖ ^ 2) ^ (-t / 2)) 2, ← Real.rpow_mul hp.le,
          ← Real.rpow_mul hp.le, ← Real.rpow_add hp]
        congr 2; push_cast; ring

theorem IsEllipticAt.exists_local_solution [Nontrivial E] {T : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)} {m : ℕ}
    {x₀ : E} (hT : IsEllipticAt T m x₀) (hm : 1 ≤ m) {t : ℝ}
    (ht : t < -(Module.finrank ℝ E : ℝ) / 2) :
    ∃ r > 0, ∃ E₀ : 𝓢'(E, ℂ), MemSobolev (t + m) 2 E₀ ∧
      Distribution.IsVanishingOn (T E₀ - TemperedDistribution.delta x₀) (Metric.ball x₀ r) := by
  obtain ⟨n, a, w, N, rfl, hN, hNl, cl, Cu, hcl, hCu, hlow, hup⟩ := hT.exists_data hm
  set k : ℕ := ⌈(Module.finrank ℝ E : ℝ) - 2 * t⌉₊ + 1
  have hk : (Module.finrank ℝ E : ℝ) < 2 * ((2 * m * k : ℕ) : ℝ) + 2 * t := by
    have h1 : (Module.finrank ℝ E : ℝ) - 2 * t < k := by
      have := Nat.le_ceil ((Module.finrank ℝ E : ℝ) - 2 * t)
      simp only [k]; push_cast; linarith
    have h2 : (k : ℝ) ≤ ((2 * m * k : ℕ) : ℝ) := by
      have : k ≤ 2 * m * k := by nlinarith
      exact_mod_cast this
    linarith
  obtain ⟨δ₀, hδ₀, hsmall⟩ := exists_small a w N x₀ hcl hCu hlow hup hm hN k
  obtain ⟨μ, hμ0, hμ1, hb⟩ := hsmall {t}
  have hK' := (hb t (by simp)).2
  set g := rNSymb (fun i ↦ a i x₀) w μ k
  have hg : g.HasTemperateGrowth := rNSymb_hasTemperateGrowth _ w μ k
  have hA := memLp_weight (E := E) ht
  have hB : MemLp (fun ξ ↦ g ξ * weight (-t) ξ) 2 volume :=
    memLp_mul_weight hg hk (rNSymb_bound _ w hcl hCu hlow hup hμ0 k)
  obtain ⟨r, hr, hrδ, hrsmall⟩ := exists_bump_small x₀
    (C := (eLpNorm (weight t : E → ℂ) 2 volume).toReal *
      (eLpNorm (fun ξ ↦ g ξ * weight (-t) ξ) 2 volume).toReal) (by positivity) hδ₀
  have hχR : OpBound (smulLeftCLM ℂ (bump x₀ hr : E → ℂ) ∘L Rop a w x₀ μ k) t t (1 / 4) :=
    (opBound_smulLeft_fourierMultiplier (bump x₀ hr) hg t hA hB).mono (by rw [mul_assoc]; exact hrsmall)
  have hK'' := hK'.sub hχR (by norm_num) (by norm_num)
  obtain ⟨v, hv, hvK⟩ := exists_add_eq_of_opBound_lt (by norm_num) (by norm_num) hK''
    (memSobolev_delta x₀ ht)
  refine ⟨r, hr, Qop a w x₀ μ k v, ?_, ?_⟩
  · exact (opBound_Qop a w x₀ hcl hCu hlow hup hμ0.le hμ1 k (t + m)).memSobolev
      (by convert hv using 2; ring)
  · have hZ := isVanishingOn_prinOp_add_sub a w N x₀ hδ₀ (Qop a w x₀ μ k v)
    have hP : P0 a w x₀ (Qop a w x₀ μ k v) = v - Rop a w x₀ μ k v := by
      have := congrArg (fun A : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ) ↦ A v) (frozenOperator_comp_parametrix a w x₀ hμ0.le k)
      simpa using this
    have hcut : Distribution.IsVanishingOn
        (smulLeftCLM ℂ (bump x₀ hr : E → ℂ) (Rop a w x₀ μ k v) - Rop a w x₀ μ k v)
        (Metric.ball x₀ r) :=
      isVanishingOn_smulLeftCLM_sub (bump x₀ hr).hasTemperateGrowth
        (fun x hx ↦ bump_eq_one x₀ hr (Metric.ball_subset_closedBall hx)) _
    have e : (prinOp a w + N) (Qop a w x₀ μ k v) - TemperedDistribution.delta x₀ =
        ((prinOp a w + N) (Qop a w x₀ μ k v) -
          (P0 a w x₀ (Qop a w x₀ μ k v) + locM a w N x₀ hδ₀ (Qop a w x₀ μ k v))) +
        (smulLeftCLM ℂ (bump x₀ hr : E → ℂ) (Rop a w x₀ μ k v) - Rop a w x₀ μ k v) := by
      rw [← hvK, hP]
      simp only [sub_apply, ContinuousLinearMap.comp_apply]
      abel
    rw [e]
    exact isVanishingOn_add (hZ.mono (Metric.ball_subset_ball hrδ)) hcut

end

end GroundTheory.Automorphic.Sobolev
end

namespace GroundTheory.Automorphic.Sobolev

open TemperedDistribution MeasureTheory FourierTransform LineDeriv
open scoped SchwartzMap ENNReal ContDiff

noncomputable section

set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem eq_of_integral_smul_eq {g h : E → ℂ} (hg : Continuous g) (hh : Continuous h)
    (H : ∀ φ : 𝓢(E, ℂ), HasCompactSupport φ → ∫ x, φ x • g x = ∫ x, φ x • h x) : g = h := by
  have hae := ae_eq_of_integral_schwartz_smul_eq hg.locallyIntegrable hh.locallyIntegrable H
  exact (hg.ae_eq_iff_eq volume hh).1 hae

theorem eqOn_of_integral_smul_eq {g h : E → ℂ} (hg : Continuous g) (hh : Continuous h) {V : Set E}
    (hV : IsOpen V) (H : ∀ φ : 𝓢(E, ℂ), HasCompactSupport φ → tsupport φ ⊆ V →
      ∫ x, φ x • g x = ∫ x, φ x • h x) : Set.EqOn g h V := by
  intro y hy
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hV y hy
  have hr : 0 < ε / 4 := by positivity
  obtain ⟨θ, hθ⟩ : ∃ θ : 𝓢(E, ℂ), θ = bump y hr := ⟨_, rfl⟩
  have hθV : tsupport (θ : E → ℂ) ⊆ V := hθ ▸ (tsupport_bump y hr).trans fun x hx ↦
    hball (by rw [Metric.mem_closedBall] at hx; rw [Metric.mem_ball]; linarith)
  have key : (fun x ↦ θ x * g x) = fun x ↦ θ x * h x := by
    refine eq_of_integral_smul_eq (θ.continuous.mul hg) (θ.continuous.mul hh) fun φ hφ ↦ ?_
    have h1 := H (SchwartzMap.smulLeftCLM ℂ (θ : E → ℂ) φ)
      (by
        rw [SchwartzMap.smulLeftCLM_apply θ.hasTemperateGrowth]
        exact HasCompactSupport.smul_left (f := (θ : E → ℂ)) hφ)
      (by
        rw [SchwartzMap.smulLeftCLM_apply θ.hasTemperateGrowth]
        exact (tsupport_smul_subset_left (θ : E → ℂ) (φ : E → ℂ)).trans hθV)
    simp only [SchwartzMap.smulLeftCLM_apply_apply θ.hasTemperateGrowth, smul_eq_mul] at h1
    simp only [smul_eq_mul]
    calc ∫ x, φ x * (θ x * g x) = ∫ x, θ x * φ x * g x := by congr 1; ext x; ring
      _ = ∫ x, θ x * φ x * h x := h1
      _ = ∫ x, φ x * (θ x * h x) := by congr 1; ext x; ring
  have := congrFun key y
  have hθy : θ y = 1 := by rw [hθ]; exact bump_eq_one y hr (Metric.mem_closedBall_self hr.le)
  simp only [hθy, one_mul] at this
  exact this

theorem exists_contDiff_of_memSobolev {u : 𝓢'(E, ℂ)} (hu : ∀ t, MemSobolev t 2 u) :
    ∃ g : E → ℂ, ContDiff ℝ ∞ g ∧ ∀ φ : 𝓢(E, ℂ), u φ = ∫ x, φ x • g x := by
  have hk : ∀ k : ℕ, ∃ g : E → ℂ, ContDiff ℝ k g ∧ ∀ φ : 𝓢(E, ℂ), u φ = ∫ x, φ x • g x := by
    intro k
    obtain ⟨g, hg, -, hrep⟩ := sobolev_embedding k
      (s := k + (Module.finrank ℝ E : ℝ) / 2 + 1) (by linarith)
      (SobolevSpace.mk u (hu (k + (Module.finrank ℝ E : ℝ) / 2 + 1)))
    exact ⟨g, hg, fun φ ↦ by simpa using hrep φ⟩
  choose g hg hrep using hk
  refine ⟨g 0, contDiff_infty.2 fun k ↦ ?_, hrep 0⟩
  have : g k = g 0 := eq_of_integral_smul_eq ((hg k).continuous) ((hg 0).continuous)
    fun φ _ ↦ by rw [← hrep k, ← hrep 0]
  rw [← this]; exact hg k

theorem eq_zero_of_local {Λ : 𝓢(E, ℂ) → ℂ} {K : Set E} (hK : IsCompact K) {V : E → Set E}
    (hV : ∀ x ∈ K, V x ∈ nhds x)
    (hloc : ∀ x ∈ K, ∀ φ : 𝓢(E, ℂ), tsupport φ ⊆ V x → tsupport φ ⊆ K → Λ φ = 0)
    (hadd : ∀ φ β : 𝓢(E, ℂ), tsupport φ ⊆ K →
      Λ φ = Λ (SchwartzMap.smulLeftCLM ℂ (β : E → ℂ) φ) + Λ (φ - SchwartzMap.smulLeftCLM ℂ (β : E → ℂ) φ))
    {φ : 𝓢(E, ℂ)} (hφ : tsupport φ ⊆ K) : Λ φ = 0 := by
  classical

  have hr : ∀ x ∈ K, ∃ r > 0, Metric.closedBall x (2 * r) ⊆ V x := by
    intro x hx
    obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.1 (hV x hx)
    exact ⟨ε / 4, by positivity, fun y hy ↦ hsub (by
      rw [Metric.mem_closedBall] at hy; rw [Metric.mem_ball]; linarith)⟩
  choose! r hr0 hrV using hr
  obtain ⟨S, hSK, hcover⟩ := hK.elim_nhds_subcover (fun x ↦ Metric.ball x (r x))
    (fun x hx ↦ Metric.ball_mem_nhds x (hr0 x hx))
  have claim : ∀ T : Finset E, (∀ c ∈ T, c ∈ K) → ∀ ψ : 𝓢(E, ℂ), tsupport ψ ⊆ K →
      tsupport ψ ⊆ ⋃ c ∈ T, Metric.ball c (r c) → Λ ψ = 0 := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro _ ψ hψK hψ
      have hψ0 : ψ = 0 := by
        ext x
        by_contra hx
        have := hψ (subset_tsupport _ hx)
        simp at this
      have h0 := hadd 0 0 (by rw [hψ0] at hψK; exact hψK)
      simp only [map_zero, sub_zero] at h0
      rw [hψ0]; linear_combination (-1 : ℂ) * h0
    | insert c T hc ih =>
      intro hTK ψ hψK hψ
      have hcK : c ∈ K := hTK c (Finset.mem_insert_self c T)
      obtain ⟨β, hβ⟩ : ∃ β : 𝓢(E, ℂ), β = bump c (hr0 c hcK) := ⟨_, rfl⟩
      rw [hadd ψ β hψK]
      have h1 : Λ (SchwartzMap.smulLeftCLM ℂ (β : E → ℂ) ψ) = 0 := by
        apply hloc c hcK
        · rw [SchwartzMap.smulLeftCLM_apply β.hasTemperateGrowth]
          exact (tsupport_smul_subset_left (β : E → ℂ) (ψ : E → ℂ)).trans
            (hβ ▸ (tsupport_bump c _).trans (hrV c hcK))
        · rw [SchwartzMap.smulLeftCLM_apply β.hasTemperateGrowth]
          exact (tsupport_smul_subset_right (β : E → ℂ) (ψ : E → ℂ)).trans hψK
      have h2 : Λ (ψ - SchwartzMap.smulLeftCLM ℂ (β : E → ℂ) ψ) = 0 := by
        have hsupp : tsupport (ψ - SchwartzMap.smulLeftCLM ℂ (β : E → ℂ) ψ : E → ℂ) ⊆
            tsupport ψ ∩ (Metric.ball c (r c))ᶜ := by
          have e : (ψ - SchwartzMap.smulLeftCLM ℂ (β : E → ℂ) ψ : E → ℂ) =
              fun x ↦ (1 - β x) * ψ x := by
            ext x
            simp only [Pi.sub_apply, SchwartzMap.smulLeftCLM_apply_apply β.hasTemperateGrowth,
              smul_eq_mul]
            ring
          rw [e]
          refine Set.subset_inter (tsupport_mul_subset_right) ?_
          refine (tsupport_mul_subset_left).trans (closure_minimal ?_
            Metric.isOpen_ball.isClosed_compl)
          intro x hx hxb
          apply hx
          show 1 - β x = 0
          rw [hβ, bump_eq_one c (hr0 c hcK) (Metric.ball_subset_closedBall hxb), sub_self]
        refine ih (fun c' hc' ↦ hTK c' (Finset.mem_insert_of_mem hc')) _
          (hsupp.trans (Set.inter_subset_left.trans hψK)) ?_
        intro x hx
        obtain ⟨hx1, hx2⟩ := hsupp hx
        have := hψ hx1
        simp only [Finset.set_biUnion_insert, Set.mem_union] at this
        rcases this with h | h
        · exact absurd h hx2
        · exact h
      rw [h1, h2, add_zero]
  exact claim S hSK φ hφ (hφ.trans hcover)

theorem continuous_smul_of_tsupport_subset {g : E → ℂ} {Ω : Set E} (hΩ : IsOpen Ω)
    (hg : ContinuousOn g Ω) {φ : E → ℂ} (hφ : Continuous φ) (hφΩ : tsupport φ ⊆ Ω) :
    Continuous fun x ↦ φ x • g x := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ Ω
  · exact hφ.continuousAt.smul (hg.continuousAt (hΩ.mem_nhds hx))
  · have hx' : x ∉ tsupport φ := fun h ↦ hx (hφΩ h)
    have hev : ∀ᶠ y in nhds x, φ y • g y = 0 := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx'] with y hy
      rw [hy, Pi.zero_apply, zero_smul]
    have h0 : φ x • g x = 0 := hev.self_of_nhds
    exact (continuousAt_const.congr (hev.mono fun y hy ↦ by rw [hy, ← h0])).congr
      (Filter.Eventually.of_forall fun _ ↦ rfl)

theorem integrable_smul_of_tsupport_subset {g : E → ℂ} {Ω : Set E} (hΩ : IsOpen Ω)
    (hg : ContinuousOn g Ω) {φ : 𝓢(E, ℂ)} (hφc : HasCompactSupport φ) (hφΩ : tsupport φ ⊆ Ω) :
    Integrable (fun y ↦ φ y • g y) :=
  (continuous_smul_of_tsupport_subset hΩ hg φ.continuous hφΩ).integrable_of_hasCompactSupport
    (IsCompact.of_isClosed_subset hφc.isCompact (isClosed_tsupport _)
      (tsupport_smul_subset_left (φ : E → ℂ) g))

theorem exists_contDiffOn_of_local {Λ : 𝓢(E, ℂ) → ℂ} {Ω : Set E} (hΩ : IsOpen Ω)
    (hadd : ∀ φ ψ : 𝓢(E, ℂ), HasCompactSupport φ → tsupport φ ⊆ Ω → HasCompactSupport ψ →
      tsupport ψ ⊆ Ω → Λ (φ + ψ) = Λ φ + Λ ψ)
    (h : ∀ x ∈ Ω, ∃ W : Set E, ∃ G : E → ℂ, IsOpen W ∧ x ∈ W ∧ W ⊆ Ω ∧ ContDiff ℝ ∞ G ∧
      ∀ φ : 𝓢(E, ℂ), HasCompactSupport φ → tsupport φ ⊆ W → Λ φ = ∫ y, φ y • G y) :
    ∃ g : E → ℂ, ContDiffOn ℝ ∞ g Ω ∧ ∀ φ : 𝓢(E, ℂ), HasCompactSupport φ → tsupport φ ⊆ Ω →
      Λ φ = ∫ x, φ x • g x := by
  choose! W G hWo hxW hWΩ hG hrep using h
  have hcons : ∀ x ∈ Ω, ∀ y ∈ Ω, Set.EqOn (G x) (G y) (W x ∩ W y) := by
    intro x hx y hy
    refine eqOn_of_integral_smul_eq (hG x hx).continuous (hG y hy).continuous
      ((hWo x hx).inter (hWo y hy)) fun φ hφc hφ ↦ ?_
    rw [← hrep x hx φ hφc (hφ.trans Set.inter_subset_left),
      hrep y hy φ hφc (hφ.trans Set.inter_subset_right)]
  set g : E → ℂ := fun y ↦ G y y
  have hgW : ∀ x ∈ Ω, Set.EqOn g (G x) (W x) := by
    intro x hx y hy
    exact (hcons x hx y (hWΩ x hx hy) ⟨hy, hxW y (hWΩ x hx hy)⟩).symm
  have hgsmooth : ContDiffOn ℝ ∞ g Ω := by
    refine contDiffOn_of_locally_contDiffOn fun x hx ↦ ⟨W x, hWo x hx, hxW x hx, ?_⟩
    exact ((hG x hx).contDiffOn.mono Set.inter_subset_right).congr fun y hy ↦ hgW x hx hy.2
  refine ⟨g, hgsmooth, fun φ hφc hφΩ ↦ ?_⟩
  set Λ' : 𝓢(E, ℂ) → ℂ := fun ψ ↦ Λ ψ - ∫ y, ψ y • g y
  have hcs : ∀ ψ : 𝓢(E, ℂ), tsupport ψ ⊆ tsupport φ → HasCompactSupport ψ := fun ψ hψ ↦
    IsCompact.of_isClosed_subset hφc.isCompact (isClosed_tsupport _) hψ
  have key : Λ' φ = 0 := by
    refine eq_zero_of_local (V := W) hφc.isCompact
      (fun x hx ↦ (hWo x (hφΩ hx)).mem_nhds (hxW x (hφΩ hx))) (fun x hx ψ hψ hψK ↦ ?_)
      (fun ψ β hψ ↦ ?_) subset_rfl
    · have hxΩ := hφΩ hx
      simp only [Λ', sub_eq_zero]
      rw [hrep x hxΩ ψ (hcs ψ hψK) hψ]
      congr 1; ext y
      by_cases hy : ψ y = 0
      · rw [hy, zero_smul, zero_smul]
      · rw [hgW x hxΩ (hψ (subset_tsupport _ hy))]
    · have h1 : tsupport (SchwartzMap.smulLeftCLM ℂ (β : E → ℂ) ψ : E → ℂ) ⊆ tsupport ψ := by
        rw [SchwartzMap.smulLeftCLM_apply β.hasTemperateGrowth]
        exact tsupport_smul_subset_right (β : E → ℂ) (ψ : E → ℂ)
      obtain ⟨a, ha⟩ : ∃ a : 𝓢(E, ℂ), a = SchwartzMap.smulLeftCLM ℂ (β : E → ℂ) ψ := ⟨_, rfl⟩
      rw [← ha] at h1 ⊢
      obtain ⟨b, hb⟩ : ∃ b : 𝓢(E, ℂ), b = ψ - a := ⟨_, rfl⟩
      rw [← hb]
      have hab : a + b = ψ := by rw [hb]; abel
      have h2 : tsupport (b : E → ℂ) ⊆ tsupport ψ := by
        refine closure_minimal (fun y hy ↦ ?_) (isClosed_tsupport _)
        by_contra hy'
        apply hy
        have : ψ y = 0 := image_eq_zero_of_notMem_tsupport hy'
        have ha0 : a y = 0 := by
          rw [ha, SchwartzMap.smulLeftCLM_apply_apply β.hasTemperateGrowth, this, smul_zero]
        rw [hb, sub_apply, this, ha0, sub_zero]
      have hi : ∀ χ : 𝓢(E, ℂ), tsupport χ ⊆ tsupport ψ → Integrable (fun y ↦ χ y • g y) :=
        fun χ hχ ↦ integrable_smul_of_tsupport_subset hΩ hgsmooth.continuousOn
          (hcs χ (hχ.trans hψ)) (hχ.trans (hψ.trans hφΩ))
      have hΛ : Λ ψ = Λ a + Λ b := by
        rw [← hab]
        exact hadd a b (hcs _ (h1.trans hψ)) (h1.trans (hψ.trans hφΩ)) (hcs _ (h2.trans hψ))
          (h2.trans (hψ.trans hφΩ))
      have hI : ∫ y, ψ y • g y = (∫ y, a y • g y) + ∫ y, b y • g y := by
        rw [← integral_add (hi _ h1) (hi _ h2)]
        congr 1; ext y; rw [← hab, add_apply, add_smul]
      show Λ ψ - ∫ y, ψ y • g y = (Λ a - ∫ y, a y • g y) + (Λ b - ∫ y, b y • g y)
      rw [hΛ, hI]; ring
  simp only [Λ', sub_eq_zero] at key
  exact key

theorem exists_contDiffOn_of_locally_memSobolev {u : 𝓢'(E, ℂ)} {Ω : Set E} (hΩ : IsOpen Ω)
    (h : ∀ x ∈ Ω, ∃ ψ : 𝓢(E, ℂ), (∀ᶠ y in nhds x, ψ y = 1) ∧
      ∀ t, MemSobolev t 2 (smulLeftCLM ℂ (ψ : E → ℂ) u)) :
    ∃ g : E → ℂ, ContDiffOn ℝ ∞ g Ω ∧ ∀ φ : 𝓢(E, ℂ), HasCompactSupport φ → tsupport φ ⊆ Ω →
      u φ = ∫ x, φ x • g x := by
  refine exists_contDiffOn_of_local hΩ (fun φ ψ _ _ _ _ ↦ map_add u φ ψ) fun x hx ↦ ?_
  obtain ⟨ψ, hψ1, hψ⟩ := h x hx
  obtain ⟨t, ht1, htopen, hxt⟩ := eventually_nhds_iff.1 hψ1
  obtain ⟨G, hG, hrep⟩ := exists_contDiff_of_memSobolev hψ
  refine ⟨t ∩ Ω, G, htopen.inter hΩ, ⟨hxt, hx⟩, Set.inter_subset_right, hG, fun φ _ hφ ↦ ?_⟩
  rw [← hrep φ, smulLeftCLM_apply_apply]
  congr 1
  ext y
  rw [SchwartzMap.smulLeftCLM_apply_apply ψ.hasTemperateGrowth, smul_eq_mul]
  by_cases hy : φ y = 0
  · rw [hy, mul_zero]
  · rw [ht1 y (hφ (subset_tsupport _ hy)).1, one_mul]

theorem IsEllipticAt.regularity_le {T : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)} {m : ℕ} {x₀ : E}
    (hT : IsEllipticAt T m x₀) (hm : 1 ≤ m) :
    ∃ δ > 0, ∀ δ' ∈ Set.Ioc 0 δ, ∀ (u : 𝓢'(E, ℂ)) (s₀ : ℝ), MemSobolev s₀ 2 u → ∀ F : 𝓢'(E, ℂ),
      (∀ t, MemSobolev t 2 F) → Distribution.IsVanishingOn (T u - F) (Metric.ball x₀ δ') →
      ∀ ψ : 𝓢(E, ℂ), tsupport (ψ : E → ℂ) ⊆ Metric.ball x₀ δ' →
        ∀ t, MemSobolev t 2 (smulLeftCLM ℂ (ψ : E → ℂ) u) := by
  obtain ⟨δ, hδ, hstep⟩ := hT.exists_regularity_radius hm
  refine ⟨δ, hδ, fun δ' ⟨hδ'0, hδ'δ⟩ u s₀ hu F hF hTF ↦ ?_⟩
  have claim : ∀ j : ℕ, ∀ ψ : 𝓢(E, ℂ), tsupport (ψ : E → ℂ) ⊆ Metric.ball x₀ δ' →
      MemSobolev (s₀ + j) 2 (smulLeftCLM ℂ (ψ : E → ℂ) u) := by
    intro j
    induction j with
    | zero => intro ψ _; simpa using memSobolev_smulLeft ψ hu
    | succ j ih =>
      intro ψ hψ
      obtain ⟨ρ, ⟨hρ0, hρδ⟩, hsub⟩ := exists_pos_lt_subset_ball hδ'0 (isClosed_tsupport _) hψ
      have hr₁ : 0 < (2 * ρ + δ') / 3 := by linarith
      have hr₁R : (2 * ρ + δ') / 3 < (ρ + 2 * δ') / 3 := by linarith
      set ψ₁ := bumpG x₀ hr₁ hr₁R
      have hψ₁ : tsupport (ψ₁ : E → ℂ) ⊆ Metric.ball x₀ δ' := by
        refine (tsupport_bumpG x₀ hr₁ hr₁R).trans fun x hx ↦ ?_
        rw [Metric.mem_closedBall] at hx; rw [Metric.mem_ball]; linarith
      set w := smulLeftCLM ℂ (ψ : E → ℂ) u
      have hw : MemSobolev (s₀ + j) 2 w := ih ψ hψ
      have hvan : Distribution.IsVanishingOn w (Metric.closedBall x₀ ρ)ᶜ :=
        (isVanishingOn_smulLeftCLM_compl ψ.hasTemperateGrowth u).mono
          (Set.compl_subset_compl.2 (hsub.trans Metric.ball_subset_closedBall))
      have hψT : smulLeftCLM ℂ (ψ : E → ℂ) (T u) = smulLeftCLM ℂ (ψ : E → ℂ) F := by
        have h0 := smulLeftCLM_eq_zero_of_isVanishingOn ψ.hasTemperateGrowth hTF hψ
        rw [map_sub, sub_eq_zero] at h0
        exact h0
      have hψψ₁ : smulLeftCLM ℂ (ψ : E → ℂ) (smulLeftCLM ℂ (ψ₁ : E → ℂ) u) =
          smulLeftCLM ℂ (ψ : E → ℂ) u := by
        have hfun : ((ψ₁ : E → ℂ) * (ψ : E → ℂ)) = (ψ : E → ℂ) := by
          ext x
          simp only [Pi.mul_apply]
          by_cases hx : ψ x = 0
          · rw [hx, mul_zero]
          · rw [bumpG_eq_one x₀ hr₁ hr₁R, one_mul]
            have := hsub (subset_tsupport _ hx)
            rw [Metric.mem_ball] at this; rw [Metric.mem_closedBall]; linarith
        rw [smulLeftCLM_smulLeftCLM_apply ψ₁.hasTemperateGrowth ψ.hasTemperateGrowth, hfun]
      have hcomm : comm T ψ u = comm T ψ (smulLeftCLM ℂ (ψ₁ : E → ℂ) u) := by
        have hz1 : smulLeftCLM ℂ (ψ : E → ℂ) (u - smulLeftCLM ℂ (ψ₁ : E → ℂ) u) = 0 := by
          rw [map_sub, hψψ₁, sub_self]
        have hz2 : Distribution.IsVanishingOn (u - smulLeftCLM ℂ (ψ₁ : E → ℂ) u)
            (Metric.ball x₀ ((2 * ρ + δ') / 3)) := by
          have := isVanishingOn_smulLeftCLM_sub ψ₁.hasTemperateGrowth
            (V := Metric.ball x₀ ((2 * ρ + δ') / 3))
            (fun x hx ↦ bumpG_eq_one x₀ hr₁ hr₁R (Metric.ball_subset_closedBall hx)) u
          have h2 := isVanishingOn_neg this
          rwa [neg_sub] at h2
        have hz3 : smulLeftCLM ℂ (ψ : E → ℂ) (T (u - smulLeftCLM ℂ (ψ₁ : E → ℂ) u)) = 0 :=
          smulLeftCLM_eq_zero_of_isVanishingOn ψ.hasTemperateGrowth
            (hT.isLocal _ Metric.isOpen_ball _ hz2)
            (hsub.trans (Metric.ball_subset_ball (by linarith)))
        have : comm T ψ (u - smulLeftCLM ℂ (ψ₁ : E → ℂ) u) = 0 := by
          rw [comm_apply, hz1, map_zero, hz3, sub_zero]
        rw [map_sub, sub_eq_zero] at this
        exact this
      have hTw : MemSobolev (s₀ + j - m + 1) 2 (T w) := by
        have e : T w = smulLeftCLM ℂ (ψ : E → ℂ) F + comm T ψ (smulLeftCLM ℂ (ψ₁ : E → ℂ) u) := by
          rw [← hcomm, ← hψT, comm_apply]; abel
        rw [e]
        refine (memSobolev_smulLeft ψ (hF _)).add ?_
        exact (hT.hasOrder_comm ψ).memSobolev' (by ring) (ih ψ₁ hψ₁)
      have := hstep (s₀ + j) w hw ⟨ρ, hρδ.trans_le hδ'δ, hvan⟩ hTw
      simpa [add_assoc] using this
  intro ψ hψ t
  have hj : t ≤ s₀ + (⌈t - s₀⌉₊ : ℕ) := by
    have := Nat.le_ceil (t - s₀); linarith
  exact (claim _ ψ hψ).mono hj

theorem contDiffOn_of_isEllipticAt {T : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)} {m : ℕ} (hm : 1 ≤ m)
    {Ω : Set E} (hΩ : IsOpen Ω) (hT : ∀ x ∈ Ω, IsEllipticAt T m x) {u : 𝓢'(E, ℂ)} {s₀ : ℝ}
    (hu : MemSobolev s₀ 2 u) {F : 𝓢'(E, ℂ)} (hF : ∀ t, MemSobolev t 2 F)
    (hTF : Distribution.IsVanishingOn (T u - F) Ω) :
    ∃ g : E → ℂ, ContDiffOn ℝ ∞ g Ω ∧ ∀ φ : 𝓢(E, ℂ), HasCompactSupport φ → tsupport φ ⊆ Ω →
      u φ = ∫ x, φ x • g x := by
  refine exists_contDiffOn_of_locally_memSobolev hΩ fun x hx ↦ ?_
  obtain ⟨δ, hδ, hreg⟩ := (hT x hx).regularity_le hm
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hΩ x hx
  set δ' := min δ ε
  have hδ' : 0 < δ' := lt_min hδ hε
  have hr : 0 < δ' / 4 := by positivity
  refine ⟨bump x hr, ?_, fun t ↦ hreg δ' ⟨hδ', min_le_left _ _⟩ u s₀ hu F hF
    (hTF.mono ((Metric.ball_subset_ball (min_le_right _ _)).trans hball)) _ ?_ t⟩
  · filter_upwards [Metric.ball_mem_nhds x hr] with y hy
    exact bump_eq_one x hr (Metric.ball_subset_closedBall hy)
  · refine (tsupport_bump x hr).trans fun y hy ↦ ?_
    rw [Metric.mem_closedBall] at hy; rw [Metric.mem_ball]; linarith

end

end GroundTheory.Automorphic.Sobolev
