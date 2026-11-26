module

public import Formalism.UnipotentAdelicQuotients.EllipticRegularity.BaseLevel

@[expose] public section

section -- merged from Formalism.UnipotentAdelicQuotients.EllipticRegularity.KernDil
namespace ZetaZeros.D.EllReg

open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal

noncomputable section

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

lemma norm_fourier_comp_dil (c : V → ℂ) (r : ℝ) (hr : 0 < r) (x0 w : V) :
    ‖𝓕 (fun x => c (r⁻¹ • (x - x0))) w‖ = r ^ Module.finrank ℝ V * ‖𝓕 c (r • w)‖ := by
  have hrw : ∀ y : V, Complex.exp (↑(-2 * Real.pi * inner ℝ (r • y + x0) w) * Complex.I) • c y =
      Complex.exp (↑(-2 * Real.pi * inner ℝ x0 w) * Complex.I) *
        (Complex.exp (↑(-2 * Real.pi * inner ℝ y (r • w)) * Complex.I) • c y) := by
    intro y
    rw [smul_eq_mul, smul_eq_mul, ← mul_assoc, ← Complex.exp_add]
    congr 2
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_right]
    push_cast
    ring
  rw [Real.fourier_eq', Real.fourier_eq']
  have h1 : (∫ v : V, Complex.exp (↑(-2 * Real.pi * inner ℝ v w) * Complex.I) • c (r⁻¹ • (v - x0))) =
      ∫ v : V, (fun y => Complex.exp (↑(-2 * Real.pi * inner ℝ (r • y + x0) w) * Complex.I) • c y)
        (r⁻¹ • v) := by
    rw [← MeasureTheory.integral_add_right_eq_self _ x0]
    congr 1
    funext v
    simp only [add_sub_cancel_right, smul_inv_smul₀ hr.ne']
  have h2 := MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg (MeasureTheory.volume : MeasureTheory.Measure V)
    (fun y => Complex.exp (↑(-2 * Real.pi * inner ℝ (r • y + x0) w) * Complex.I) • c y) hr.le
  rw [h1.trans h2]
  simp only [hrw]
  rw [MeasureTheory.integral_const_mul, norm_smul, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul,
    Real.norm_eq_abs, abs_of_nonneg (by positivity)]

lemma lintegral_dil_weight (r : ℝ) (hr : 0 < r) (D : ℝ) (hD : (Module.finrank ℝ V : ℝ) < D) :
    (∫⁻ w : V, ENNReal.ofReal (r ^ Module.finrank ℝ V * (1 + ‖r • w‖) ^ (-D))) =
      ∫⁻ w : V, ENNReal.ofReal ((1 + ‖w‖) ^ (-D)) := by
  have hr0 : r ≠ 0 := hr.ne'
  have hmeas : Measurable (fun w : V => r • w) := measurable_const_smul r
  have hg : Measurable (fun u : V => ENNReal.ofReal ((1 + ‖u‖) ^ (-D))) := by fun_prop
  have h1 : ∀ w : V, ENNReal.ofReal (r ^ Module.finrank ℝ V * (1 + ‖r • w‖) ^ (-D)) =
      ENNReal.ofReal (r ^ Module.finrank ℝ V) * ENNReal.ofReal ((1 + ‖r • w‖) ^ (-D)) :=
    fun w => ENNReal.ofReal_mul (by positivity)
  simp_rw [h1]
  have hg' : Measurable (fun w : V => ENNReal.ofReal ((1 + ‖r • w‖) ^ (-D))) := hg.comp hmeas
  rw [MeasureTheory.lintegral_const_mul _ hg']
  rw [← MeasureTheory.lintegral_map hg hmeas, MeasureTheory.Measure.map_addHaar_smul _ hr0,
    MeasureTheory.lintegral_smul_measure, smul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
    abs_of_pos (by positivity), mul_inv_cancel₀ (by positivity), ENNReal.ofReal_one, one_mul]

end

end ZetaZeros.D.EllReg
end

section -- merged from Formalism.UnipotentAdelicQuotients.EllipticRegularity.KernDer
section -- merged from Formalism.UnipotentAdelicQuotients.EllipticRegularity.KernGr
namespace ZetaZeros.D.EllReg

open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal

noncomputable section

lemma gr_zero {d : ℕ} (b : E d → ℂ) (hb : ContDiff ℝ ∞ b) (L : ℝ) (hL : ∀ x, ‖fderiv ℝ b x‖ ≤ L)
    (x0 y : E d) (r : ℝ) (hr : 0 < r) : ‖b (x0 + r • y) - b x0‖ ≤ L * (r * ‖y‖) := by
  have hd : Differentiable ℝ b := hb.differentiable (by simp)
  have := Convex.norm_image_sub_le_of_norm_fderiv_le (fun x _ => hd x) (fun x _ => hL x)
    convex_univ (Set.mem_univ x0) (Set.mem_univ (x0 + r • y))
  rwa [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hr.le] at this

lemma gr_pos {d : ℕ} (b : E d → ℂ) (hb : ContDiff ℝ ∞ b) (k : ℕ) (hk0 : 0 < k) (M : ℝ)
    (hM : ∀ x, ‖iteratedFDeriv ℝ k b x‖ ≤ M) (x0 y : E d) (r : ℝ) (hr : 0 < r) :
    ‖iteratedFDeriv ℝ k (fun y => b (x0 + r • y) - b x0) y‖ ≤ M * r ^ k := by
  have hk : k ≠ 0 := hk0.ne'
  have hkle : (k : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) := by exact_mod_cast (ENat.natCast_lt_top k).le
  obtain ⟨g, hg⟩ : ∃ g : E d →L[ℝ] E d, g = r • ContinuousLinearMap.id ℝ (E d) := ⟨_, rfl⟩
  have hshift : ContDiff ℝ ∞ (fun z => b (x0 + z)) := hb.comp (contDiff_const.add contDiff_id)
  have hfun : (fun y => b (x0 + r • y) - b x0) = ((fun z => b (x0 + z)) ∘ g) - fun _ => b x0 := by
    funext y; simp [hg]
  rw [hfun, iteratedFDeriv_sub_apply (((hshift.comp g.contDiff).of_le hkle).contDiffAt)
    contDiffAt_const, iteratedFDeriv_const_of_ne hk, Pi.zero_apply, sub_zero,
    g.iteratedFDeriv_comp_right hshift y hkle, iteratedFDeriv_comp_add_left]
  have hgn : ‖g‖ ≤ r := by
    rw [hg]
    refine (norm_smul_le r _).trans ?_
    rw [Real.norm_of_nonneg hr.le]
    exact mul_le_of_le_one_right hr.le ContinuousLinearMap.norm_id_le
  calc _ ≤ ‖iteratedFDeriv ℝ k b (x0 + g y)‖ * ∏ _i : Fin k, ‖g‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ M * r ^ k := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      exact mul_le_mul (hM _) (pow_le_pow_left₀ (norm_nonneg _) hgn k) (by positivity)
        ((norm_nonneg _).trans (hM 0))

end

end ZetaZeros.D.EllReg
end

namespace ZetaZeros.D.EllReg

open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal

noncomputable section


set_option maxHeartbeats 800000 in
lemma derivL1Norm_rescaled_difference_le {d : ℕ} (ψ : E d → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (b : E d → ℂ) (hb : ContDiff ℝ ∞ b) (hbc : HasCompactSupport b) (x0 : E d) (r0 : ℝ) (n : ℕ) :
    ∃ K : ℝ, ∀ r : ℝ, 0 < r → r ≤ r0 →
      derivL1Norm (fun y => ψ y * (b (x0 + r • y) - b x0)) n ≤ K * r := by
  classical
  have hinf : ∀ m : ℕ, (m : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := fun m => by exact_mod_cast le_top
  have hbnd : ∀ k : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖iteratedFDeriv ℝ k b x‖ ≤ M := by
    intro k
    obtain ⟨M, hM⟩ := (hb.continuous_iteratedFDeriv (hinf k)).norm.bddAbove_range_of_hasCompactSupport
      (hbc.iteratedFDeriv (𝕜 := ℝ) k).norm
    exact ⟨max M 0, le_max_right _ _, fun x => (hM ⟨x, rfl⟩).trans (le_max_left _ _)⟩
  choose M hM0 hM using hbnd
  obtain ⟨L0, hL0⟩ := (hb.continuous_fderiv (by simp)).norm.bddAbove_range_of_hasCompactSupport
    (hbc.fderiv (𝕜 := ℝ)).norm
  have hL : ∀ x, ‖fderiv ℝ b x‖ ≤ max L0 0 := fun x => (hL0 ⟨x, rfl⟩).trans (le_max_left _ _)
  have hLn : 0 ≤ max L0 0 := le_max_right _ _
  have hR1 : 1 ≤ max 1 r0 := le_max_left _ _
  have hsumn : 0 ≤ ∑ k ∈ Finset.range (n + 1), M k * (max 1 r0) ^ k :=
    Finset.sum_nonneg fun k _ => mul_nonneg (hM0 k) (by positivity)
  have hAL : max L0 0 ≤ max L0 0 + ∑ k ∈ Finset.range (n + 1), M k * (max 1 r0) ^ k :=
    le_add_of_nonneg_right hsumn
  have hAk : ∀ k ∈ Finset.range (n + 1), M k * (max 1 r0) ^ k ≤
      max L0 0 + ∑ k ∈ Finset.range (n + 1), M k * (max 1 r0) ^ k := fun k hk =>
    (Finset.single_le_sum (f := fun k => M k * (max 1 r0) ^ k)
      (fun k _ => mul_nonneg (hM0 k) (by positivity)) hk).trans (le_add_of_nonneg_left hLn)
  have hA0 : 0 ≤ max L0 0 + ∑ k ∈ Finset.range (n + 1), M k * (max 1 r0) ^ k := hLn.trans hAL
  set A := max L0 0 + ∑ k ∈ Finset.range (n + 1), M k * (max 1 r0) ^ k with hA
  let h : ℕ → E d → ℝ := fun j y =>
    ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i ψ y‖ * (1 + ‖y‖)
  have hhi : ∀ j, Integrable (h j) := by
    intro j
    show Integrable (fun y =>
      ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i ψ y‖ * (1 + ‖y‖))
    refine MeasureTheory.integrable_finsetSum _ fun i _ => ?_
    have h0 := integrable_iteratedFDeriv hψ hψc 0 i
    have h1 := integrable_iteratedFDeriv hψ hψc 1 i
    have he : (fun y => (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i ψ y‖ * (1 + ‖y‖)) = fun y =>
        (j.choose i : ℝ) * (‖y‖ ^ 0 * ‖iteratedFDeriv ℝ i ψ y‖ + ‖y‖ ^ 1 * ‖iteratedFDeriv ℝ i ψ y‖) := by
      funext y
      ring
    rw [he]
    exact (h0.add h1).const_mul _
  refine ⟨A * ∑ j ∈ Finset.range (n + 1), ∫ y, h j y, fun r hr hr0 => ?_⟩
  have hg : ContDiff ℝ ∞ (fun y => b (x0 + r • y) - b x0) := by
    have h1 : ContDiff ℝ ∞ (fun y : E d => x0 + r • y) := by fun_prop
    exact (hb.comp h1).sub contDiff_const
  have hgb : ∀ k ∈ Finset.range (n + 1), ∀ y,
      ‖iteratedFDeriv ℝ k (fun y => b (x0 + r • y) - b x0) y‖ ≤ r * A * (1 + ‖y‖) := by
    intro k hk y
    have hy : 0 ≤ ‖y‖ := norm_nonneg _
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0
      rw [norm_iteratedFDeriv_zero]
      have h1 := gr_zero b hb (max L0 0) hL x0 y r hr
      nlinarith [mul_le_mul_of_nonneg_left hAL (mul_nonneg hr.le hy), mul_nonneg hr.le hA0]
    · have h1 := gr_pos b hb k hk0 (M k) (hM k) x0 y r hr
      have hrk : r ^ k ≤ r * (max 1 r0) ^ k := by
        calc r ^ k = r * r ^ (k - 1) := by rw [← pow_succ', Nat.sub_add_cancel hk0]
          _ ≤ r * (max 1 r0) ^ (k - 1) :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr.le (hr0.trans (le_max_right _ _)) _) hr.le
          _ ≤ r * (max 1 r0) ^ k :=
            mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hR1 (Nat.sub_le _ _)) hr.le
      have h2 : M k * r ^ k ≤ r * A := by
        calc M k * r ^ k ≤ M k * (r * (max 1 r0) ^ k) := mul_le_mul_of_nonneg_left hrk (hM0 k)
          _ = r * (M k * (max 1 r0) ^ k) := by ring
          _ ≤ r * A := mul_le_mul_of_nonneg_left (hAk k hk) hr.le
      nlinarith [mul_nonneg (mul_nonneg hr.le hA0) hy]
  have hpt : ∀ j ∈ Finset.range (n + 1), ∀ y,
      ‖iteratedFDeriv ℝ j (fun y => ψ y * (b (x0 + r • y) - b x0)) y‖ ≤ r * A * h j y := by
    intro j hj y
    refine (norm_iteratedFDeriv_mul_le hψ hg y (hinf j)).trans ?_
    simp only [h, Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    have hji : j - i ∈ Finset.range (n + 1) :=
      Finset.mem_range.mpr (by have := Finset.mem_range.mp hj; omega)
    have h3 := hgb (j - i) hji y
    have hc : (0 : ℝ) ≤ (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i ψ y‖ := by positivity
    calc (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i ψ y‖ *
          ‖iteratedFDeriv ℝ (j - i) (fun y => b (x0 + r • y) - b x0) y‖
        ≤ (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i ψ y‖ * (r * A * (1 + ‖y‖)) :=
          mul_le_mul_of_nonneg_left h3 hc
      _ = r * A * ((j.choose i : ℝ) * ‖iteratedFDeriv ℝ i ψ y‖ * (1 + ‖y‖)) := by ring
  unfold derivL1Norm
  calc ∑ j ∈ Finset.range (n + 1), ∫ y, ‖iteratedFDeriv ℝ j (fun y => ψ y * (b (x0 + r • y) - b x0)) y‖
      ≤ ∑ j ∈ Finset.range (n + 1), ∫ y, r * A * h j y := by
        refine Finset.sum_le_sum fun j hj => ?_
        exact integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => norm_nonneg _)
          ((hhi j).const_mul _) (Filter.Eventually.of_forall fun y => hpt j hj y)
    _ = (A * ∑ j ∈ Finset.range (n + 1), ∫ y, h j y) * r := by
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [integral_const_mul]
        ring

end

end ZetaZeros.D.EllReg
end

namespace ZetaZeros.D.EllReg

open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal

noncomputable section

lemma exists_smooth_ext {d : ℕ} {U : Set (E d)} {a : E d → ℂ} {x0 : E d} (hU : IsOpen U) (hx0 : x0 ∈ U)
    (ha : ContDiffOn ℝ ∞ a U) :
    ∃ r0 > 0, ball x0 (2 * r0) ⊆ U ∧ ∃ b : E d → ℂ, ContDiff ℝ ∞ b ∧ HasCompactSupport b ∧
      ∀ x ∈ closedBall x0 (2 * r0), b x = a x := by
  obtain ⟨R, hR, hRU⟩ := Metric.isOpen_iff.1 hU x0 hx0
  let χ : ContDiffBump x0 := ⟨R / 2, 3 * R / 4, by positivity, by linarith⟩
  refine ⟨R / 4, by positivity, ?_, fun x => ((χ x : ℝ) : ℂ) * a x, ?_, ?_, ?_⟩
  · exact (Metric.ball_subset_ball (by linarith)).trans hRU
  · have hsub : tsupport χ ⊆ U := by
      rw [χ.tsupport_eq]
      exact (Metric.closedBall_subset_ball (by show 3 * R / 4 < R; linarith)).trans hRU
    refine contDiff_iff_contDiffAt.2 fun x => ?_
    by_cases hx : x ∈ U
    · exact ((Complex.ofRealCLM.contDiff.comp χ.contDiff).contDiffAt).mul
        ((ha x hx).contDiffAt (hU.mem_nhds hx))
    · have hx' : x ∉ tsupport χ := fun h => hx (hsub h)
      have hev : (fun x => ((χ x : ℝ) : ℂ) * a x) =ᶠ[nhds x] fun _ => 0 := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx'] with y hy
        simp [hy]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  · exact (χ.hasCompactSupport.comp_left Complex.ofReal_zero).mul_right
  · intro x hx
    have hx' : x ∈ Metric.closedBall x0 χ.rIn := by
      show x ∈ Metric.closedBall x0 (R / 2)
      exact Metric.closedBall_subset_closedBall (by linarith) hx
    simp [χ.one_of_mem_closedBall hx']

lemma norm_lt_of_psi_ne {d : ℕ} {ψ0 : E d → ℝ} (hψ0s : tsupport ψ0 ⊆ ball 0 2) {r : ℝ} (hr : 0 < r)
    {x x0 : E d} (hz : ψ0 (r⁻¹ • (x - x0)) ≠ 0) : ‖x - x0‖ < 2 * r := by
  have hmem : r⁻¹ • (x - x0) ∈ ball (0 : E d) 2 := hψ0s (subset_tsupport _ hz)
  rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr] at hmem
  rw [inv_mul_lt_iff₀ hr] at hmem
  linarith

theorem frozenKernelSmall : KernelSmall := by
  intro d U a x0 ψ0 hU hx0 ha hψ hψc hψs
  obtain ⟨r0, hr0, hball, b, hb, hbc, hab⟩ := exists_smooth_ext hU hx0 ha
  have hψC : ContDiff ℝ ∞ (fun y : E d => ((ψ0 y : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp hψ
  have hψCc : HasCompactSupport (fun y : E d => ((ψ0 y : ℝ) : ℂ)) := hψc.comp_left Complex.ofReal_zero
  set n := Module.finrank ℝ (E d) + 1 with hn
  obtain ⟨K, hK⟩ := derivL1Norm_rescaled_difference_le (fun y => ((ψ0 y : ℝ) : ℂ)) hψC hψCc b hb hbc x0 r0 n
  set I := ∫⁻ w : E d, ENNReal.ofReal ((1 + ‖w‖) ^ (-((n : ℕ) : ℝ))) with hIdef
  have hI : I < ⊤ := finite_integral_one_add_norm (by rw [hn]; push_cast; linarith)
  let c : ℝ → E d → ℂ := fun r y => ((ψ0 y : ℝ) : ℂ) * (b (x0 + r • y) - b x0)
  have hcs : ∀ r, ContDiff ℝ ∞ (c r) := fun r =>
    hψC.mul ((hb.comp (contDiff_const.add (contDiff_id.const_smul r))).sub contDiff_const)
  have hcc : ∀ r, HasCompactSupport (c r) := fun r => hψCc.mul_right
  have hf_eq : ∀ r : ℝ, 0 < r → r ≤ r0 →
      (fun x => ((ψ0 (r⁻¹ • (x - x0)) : ℝ) : ℂ) * (a x - a x0)) = fun x => c r (r⁻¹ • (x - x0)) := by
    intro r hr hrr
    funext x
    have hx : x0 + r • (r⁻¹ • (x - x0)) = x := by
      rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul, add_sub_cancel]
    simp only [c, hx]
    by_cases hz : ψ0 (r⁻¹ • (x - x0)) = 0
    · simp [hz]
    · have hlt := norm_lt_of_psi_ne hψs hr hz
      have hxm : x ∈ closedBall x0 (2 * r0) := by
        rw [mem_closedBall, dist_eq_norm]; linarith
      rw [hab x hxm, hab x0 (mem_closedBall_self (by linarith))]
  refine ⟨r0, hr0, (2 ^ n * (1 + 2 ^ n)) * K * I.toReal, hball, fun r hr hrr => ⟨?_, fun N => ?_⟩⟩
  · rw [hf_eq r hr hrr]
    have h2 := hK r hr hrr
    have hKr : 0 ≤ K * r := (derivL1Norm_nonneg _ _).trans h2
    have hA : (0 : ℝ) ≤ 2 ^ n * (1 + 2 ^ n) := by positivity
    have hAKr : 0 ≤ 2 ^ n * (1 + 2 ^ n) * K * r := by
      rw [mul_assoc]; exact mul_nonneg hA hKr
    have hpt : ∀ ζ : E d, ‖𝓕 (fun x => c r (r⁻¹ • (x - x0))) ζ‖ₑ ≤
        ENNReal.ofReal (2 ^ n * (1 + 2 ^ n) * K * r) *
          ENNReal.ofReal (r ^ Module.finrank ℝ (E d) * (1 + ‖r • ζ‖) ^ (-((n : ℕ) : ℝ))) := by
      intro ζ
      rw [← ofReal_norm, norm_fourier_comp_dil _ r hr x0 ζ, ← ENNReal.ofReal_mul hAKr]
      apply ENNReal.ofReal_le_ofReal
      have h1 := norm_fourier_le_rpow (hcs r) (hcc r) n (r • ζ)
      have hW : 0 ≤ (1 + ‖r • ζ‖) ^ (-((n : ℕ) : ℝ)) := Real.rpow_nonneg (by positivity) _
      have hrd : 0 ≤ r ^ Module.finrank ℝ (E d) := by positivity
      calc r ^ Module.finrank ℝ (E d) * ‖𝓕 (c r) (r • ζ)‖
          ≤ r ^ Module.finrank ℝ (E d) *
              (2 ^ n * (1 + 2 ^ n) * derivL1Norm (c r) n * (1 + ‖r • ζ‖) ^ (-((n : ℕ) : ℝ))) :=
            mul_le_mul_of_nonneg_left h1 hrd
        _ ≤ r ^ Module.finrank ℝ (E d) *
              (2 ^ n * (1 + 2 ^ n) * (K * r) * (1 + ‖r • ζ‖) ^ (-((n : ℕ) : ℝ))) := by
            gcongr
        _ = 2 ^ n * (1 + 2 ^ n) * K * r *
              (r ^ Module.finrank ℝ (E d) * (1 + ‖r • ζ‖) ^ (-((n : ℕ) : ℝ))) := by ring
    calc (∫⁻ ζ, ‖𝓕 (fun x => c r (r⁻¹ • (x - x0))) ζ‖ₑ)
        ≤ ∫⁻ ζ : E d, ENNReal.ofReal (2 ^ n * (1 + 2 ^ n) * K * r) *
          ENNReal.ofReal (r ^ Module.finrank ℝ (E d) * (1 + ‖r • ζ‖) ^ (-((n : ℕ) : ℝ))) :=
          lintegral_mono hpt
      _ = ENNReal.ofReal (2 ^ n * (1 + 2 ^ n) * K * r) * I := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_dil_weight r hr _ (by rw [hn]; push_cast; linarith)]
      _ = ENNReal.ofReal (2 ^ n * (1 + 2 ^ n) * K * I.toReal * r) := by
          rw [← ENNReal.ofReal_toReal hI.ne, ← ENNReal.ofReal_mul hAKr, ENNReal.toReal_ofReal
            ENNReal.toReal_nonneg]
          ring_nf
  · rw [hf_eq r hr hrr]
    have hsm : ContDiff ℝ ∞ (fun x => c r (r⁻¹ • (x - x0))) :=
      (hcs r).comp ((contDiff_id.sub contDiff_const).const_smul r⁻¹)
    have hsc : HasCompactSupport (fun x => c r (r⁻¹ • (x - x0))) :=
      (hcc r).comp_homeomorph ((Homeomorph.subRight x0).trans (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr.ne')))
    refine lt_of_le_of_lt (lintegral_mono fun ζ => ?_) (lintegral_weight_fourier_lt_top hsm hsc ⌈N + 1⌉₊)
    gcongr
    have h1 : 1 ≤ 1 + ‖ζ‖ := by linarith [norm_nonneg ζ]
    calc ‖ζ‖ * (1 + ‖ζ‖) ^ N ≤ (1 + ‖ζ‖) ^ (1 : ℝ) * (1 + ‖ζ‖) ^ N := by
          rw [Real.rpow_one]; gcongr; linarith
      _ = (1 + ‖ζ‖) ^ (N + 1) := by rw [← Real.rpow_add (by linarith)]; ring_nf
      _ ≤ (1 + ‖ζ‖) ^ ((⌈N + 1⌉₊ : ℕ) : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 (Nat.le_ceil _)
      _ = (1 + ‖ζ‖) ^ ⌈N + 1⌉₊ := Real.rpow_natCast _ _

end

end ZetaZeros.D.EllReg
