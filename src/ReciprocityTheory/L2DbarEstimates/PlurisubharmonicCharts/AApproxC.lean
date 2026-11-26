module

public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.CmpaCHessComp
public import Lemmata.CharacterDirections.Cdir
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.ChartSymmEventuallyEq
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.DifferentiableAtChart

@[expose] public section

section -- merged from ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AApproxC
namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology Complex
open scoped ContDiff ENNReal

noncomputable section

theorem leviV_const_mul {n : ℕ} {f : V n → ℝ} {x : V n} (hf : ContDiffAt ℝ 2 f x) (c d : ℝ)
    (ξ : Fin n → ℂ) :
    leviV n (fun y => ((c * f y + d : ℝ) : ℂ)) x ξ = c * leviV n (fun y => ((f y : ℝ) : ℂ)) x ξ := by
  have hk : ContDiffAt ℝ 2 (fun t : ℝ => c * t + d) (f x) :=
    ((contDiffAt_const.mul contDiffAt_id).add contDiffAt_const)
  have h := leviChain n (fun t : ℝ => c * t + d) f x ξ hf hk
  have hd : deriv (fun t : ℝ => c * t + d) = fun _ => c := by
    funext t; rw [deriv_add_const, deriv_const_mul_field', deriv_id'']; ring
  rw [h, hd]; simp

theorem contDiffAt_two_of_holo {n : ℕ} {g : V n → ℂ} {U : Set (V n)} (hU : IsOpen U)
    (hg : DifferentiableOn ℂ g U) {v : V n} (hv : v ∈ U) : ContDiffAt ℂ 2 g v :=
  ((ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn n g U hU hg).contDiffAt (hU.mem_nhds hv)).of_le (by norm_cast)

namespace WeightedAtlas

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La)

end WeightedAtlas

end

end ReciprocityTheory.L2DbarEstimates.Y
end

section -- merged from ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.IteratedFDerivEqZeroOfIsBigO
namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas Asymptotics Metric Set
open scoped ContDiff ENNReal Pointwise Matrix

noncomputable section

universe u

theorem fderiv_isBigO_of_isBigO_pow {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : V n → F} {U : Set (V n)} {x : V n} (hU : IsOpen U) (hx : x ∈ U)
    (hf : DifferentiableOn ℂ f U) {m : ℕ}
    (hO : f =O[𝓝 x] fun v => ‖v - x‖ ^ (m + 1 + 1)) :
    fderiv ℂ f =O[𝓝 x] fun v => ‖v - x‖ ^ (m + 1) := by
  first | exact Bl.CoprimeDirections.goal1 .. | (apply Bl.CoprimeDirections.goal1 <;> assumption) | (intros; apply Bl.CoprimeDirections.goal1 <;> assumption)

theorem isBigO_succ_of_fderiv_isBigO {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : V n → F} {U : Set (V n)} {x : V n} (hU : IsOpen U) (hx : x ∈ U)
    (hf : DifferentiableOn ℂ f U) (h0 : f x = 0) {m : ℕ}
    (hO : fderiv ℂ f =O[𝓝 x] fun v => ‖v - x‖ ^ m) :
    f =O[𝓝 x] fun v => ‖v - x‖ ^ (m + 1) := by
  obtain ⟨c, hc0, hc⟩ := hO.exists_pos
  rw [isBigOWith_iff] at hc
  obtain ⟨ε, hε0, hε⟩ := Metric.eventually_nhds_iff_ball.1 (hc.and (hU.mem_nhds hx))
  rw [isBigO_iff]
  refine ⟨c, ?_⟩
  filter_upwards [ball_mem_nhds x hε0] with v hv
  rw [norm_pow, norm_norm]
  have hvx : ‖v - x‖ < ε := by rwa [mem_ball, dist_eq_norm] at hv
  have hsub : closedBall x ‖v - x‖ ⊆ ball x ε := closedBall_subset_ball hvx
  have hmv := (convex_closedBall x ‖v - x‖).norm_image_sub_le_of_norm_fderiv_le
    (f := f) (C := c * ‖v - x‖ ^ m)
    (fun w hw => (hf w (hε _ (hsub hw)).2).differentiableAt (hU.mem_nhds (hε _ (hsub hw)).2))
    (fun w hw => by
      calc ‖fderiv ℂ f w‖ ≤ c * ‖‖w - x‖ ^ m‖ := (hε _ (hsub hw)).1
        _ = c * ‖w - x‖ ^ m := by rw [norm_pow, norm_norm]
        _ ≤ c * ‖v - x‖ ^ m := by
          gcongr
          rw [mem_closedBall, dist_eq_norm] at hw; exact hw)
    (mem_closedBall_self (norm_nonneg _)) (mem_closedBall.2 (by rw [dist_eq_norm]))
  rw [h0, sub_zero] at hmv
  calc ‖f v‖ ≤ c * ‖v - x‖ ^ m * ‖v - x‖ := hmv
    _ = c * ‖v - x‖ ^ (m + 1) := by ring

theorem top_ne_zero_withTop : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by
  exact_mod_cast (show (⊤ : ℕ∞) ≠ 0 by simp)

theorem top_add_one_le_top :
    ((⊤ : ℕ∞) : WithTop ℕ∞) + 1 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  exact_mod_cast (le_top : (⊤ : ℕ∞) + 1 ≤ ⊤)

theorem iteratedFDeriv_eq_zero_of_isBigO_alt {n : ℕ} (m : ℕ) : ∀ {F : Type u} [NormedAddCommGroup F]
    [NormedSpace ℂ F] (f : V n → F) (U : Set (V n)) (x : V n), IsOpen U → x ∈ U →
    ContDiffOn ℂ ∞ f U → (f =O[𝓝 x] fun v => ‖v - x‖ ^ (m + 1)) →
    ∀ k ≤ m, iteratedFDeriv ℂ k f x = 0 := by
  induction m with
  | zero =>
    intro F _ _ f U x hU hx hf hO k hk
    obtain rfl : k = 0 := by omega
    rw [← norm_eq_zero, norm_iteratedFDeriv_zero, norm_eq_zero]
    exact hO.eq_zero_of_norm_pow (by omega)
  | succ m ih =>
    intro F _ _ f U x hU hx hf hO k hk
    rcases k with _ | k
    · rw [← norm_eq_zero, norm_iteratedFDeriv_zero, norm_eq_zero]
      exact hO.eq_zero_of_norm_pow (by omega)
    · have hd : ContDiffOn ℂ ∞ (fderiv ℂ f) U := hf.fderiv_of_isOpen hU top_add_one_le_top
      have hO' := fderiv_isBigO_of_isBigO_pow hU hx (hf.differentiableOn top_ne_zero_withTop) hO
      rw [← norm_eq_zero, ← norm_iteratedFDeriv_fderiv, norm_eq_zero]
      exact ih (fderiv ℂ f) U x hU hx hd hO' k (by omega)

theorem isBigO_pow_of_iteratedFDeriv_zero {n : ℕ} (m : ℕ) : ∀ {F : Type u} [NormedAddCommGroup F]
    [NormedSpace ℂ F] (f : V n → F) (U : Set (V n)) (x : V n), IsOpen U → x ∈ U →
    ContDiffOn ℂ ∞ f U → (∀ k < m, iteratedFDeriv ℂ k f x = 0) →
    f =O[𝓝 x] fun v => ‖v - x‖ ^ m := by
  induction m with
  | zero =>
    intro F _ _ f U x hU hx hf _
    simp only [pow_zero]
    exact (hf.continuousOn.continuousAt (hU.mem_nhds hx)).tendsto.isBigO_one ℝ
  | succ m ih =>
    intro F _ _ f U x hU hx hf h
    have h0 : f x = 0 := by
      have := h 0 (by omega)
      rwa [← norm_eq_zero, norm_iteratedFDeriv_zero, norm_eq_zero] at this
    have hd : ContDiffOn ℂ ∞ (fderiv ℂ f) U := hf.fderiv_of_isOpen hU top_add_one_le_top
    have hO := ih (fderiv ℂ f) U x hU hx hd (fun k hk => by
      rw [← norm_eq_zero, norm_iteratedFDeriv_fderiv, norm_eq_zero]
      exact h (k + 1) (by omega))
    exact isBigO_succ_of_fderiv_isBigO hU hx (hf.differentiableOn top_ne_zero_withTop) h0 hO

theorem iteratedFDeriv_eq_zero_of_bound {n : ℕ} (g : V n → ℂ) (U : Set (V n)) (v0 : V n)
    (hU : IsOpen U) (hv : v0 ∈ U) (hg : DifferentiableOn ℂ g U) (m : ℕ)
    (hO : ∃ C : ℝ, ∀ᶠ v in 𝓝 v0, ‖g v‖ ≤ C * ‖v - v0‖ ^ (m + 1)) :
    ∀ k ≤ m, iteratedFDeriv ℂ k g v0 = 0 := by
  intro k hk
  have hc := contDiffOn_of_differentiableOn n g U hU hg
  obtain ⟨C, hC⟩ := hO
  have hO' : g =O[𝓝 v0] fun v => ‖v - v0‖ ^ (m + 1) := by
    rw [isBigO_iff]
    exact ⟨C, hC.mono fun v hv => by rwa [norm_pow, norm_norm]⟩
  exact iteratedFDeriv_eq_zero_of_isBigO_alt m g U v0 hU hv hc hO' k hk

theorem bound_of_iteratedFDeriv_eq_zero {n : ℕ} (g : V n → ℂ) (U : Set (V n)) (v0 : V n)
    (hU : IsOpen U) (hv : v0 ∈ U) (hg : DifferentiableOn ℂ g U) (m : ℕ)
    (h : ∀ k ≤ m, iteratedFDeriv ℂ k g v0 = 0) :
    ∃ C : ℝ, ∀ᶠ v in 𝓝 v0, ‖g v‖ ≤ C * ‖v - v0‖ ^ (m + 1) := by
  have hc := contDiffOn_of_differentiableOn n g U hU hg
  have hb := isBigO_pow_of_iteratedFDeriv_zero (m + 1) g U v0 hU hv hc (fun k hk => h k (by omega))
  obtain ⟨C, hC⟩ := isBigO_iff.1 hb
  exact ⟨C, hC.mono fun v hv => by rwa [norm_pow, norm_norm] at hv⟩

end

end ReciprocityTheory.L2DbarEstimates.Y
end

section -- merged from ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FlatCalcA
namespace ReciprocityTheory.L2DbarEstimates.Y

open Filter Topology Set ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives
open scoped ContDiff

noncomputable section

theorem fc_clm_decomp (n : ℕ) (D : V n →L[ℝ] ℂ) (u : V n) :
    D u = ∑ a, ((D (bas n a) - Complex.I * D (Complex.I • bas n a)) / 2 * u a +
      (D (bas n a) + Complex.I * D (Complex.I • bas n a)) / 2 * (starRingEnd ℂ) (u a)) := by
  have hu : u = ∑ a, ((u a).re • bas n a + (u a).im • (Complex.I • bas n a)) := by
    ext b
    simp [bas, PiLp.single_apply, Finset.sum_add_distrib, Complex.real_smul,
      Pi.single_apply, mul_ite, mul_one, mul_zero]
  conv_lhs => rw [hu]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_add (f := _), map_smul, map_smul, Complex.real_smul, Complex.real_smul]
  have h1 : u a = ((u a).re : ℂ) + ((u a).im : ℂ) * Complex.I := (Complex.re_add_im _).symm
  have h2 : (starRingEnd ℂ) (u a) = ((u a).re : ℂ) - ((u a).im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  linear_combination (-(D (bas n a) - Complex.I * D (Complex.I • bas n a)) / 2) * h1 +
    (-(D (bas n a) + Complex.I * D (Complex.I • bas n a)) / 2) * h2 +
    (((u a).im : ℂ) * D (Complex.I • bas n a)) * Complex.I_mul_I

theorem fc_wdb_holo (n : ℕ) (p : V n → ℂ) (v : V n) (hp : DifferentiableAt ℂ p v) (j : Fin n) :
    wdb n j p v = 0 := by
  unfold wdb
  rw [hp.fderiv_restrictScalars ℝ]
  simp only [ContinuousLinearMap.coe_restrictScalars', map_smul, smul_eq_mul]
  linear_combination (fderiv ℂ p v (bas n j) / 2) * Complex.I_mul_I

theorem fc_wd_sum (n : ℕ) (j : Fin n) {ι : Type*} (s : Finset ι) (f : ι → V n → ℂ) (v : V n)
    (hf : ∀ a ∈ s, DifferentiableAt ℝ (f a) v) :
    wd n j (fun y => ∑ a ∈ s, f a y) v = ∑ a ∈ s, wd n j (f a) v := by
  unfold wd
  have e : (fun y => ∑ a ∈ s, f a y) = ∑ a ∈ s, f a := by
    funext y
    simp
  rw [e, fderiv_sum hf]
  simp only [ContinuousLinearMap.sum_apply]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]

theorem fc_leviV_congr (n : ℕ) (g₁ g₂ : V n → ℂ) (v : V n) (h : g₁ =ᶠ[𝓝 v] g₂)
    (ξ : Fin n → ℂ) : leviV n g₁ v ξ = leviV n g₂ v ξ := by
  unfold leviV
  have hk : ∀ k, wdb n k g₁ =ᶠ[𝓝 v] wdb n k g₂ := fun k =>
    h.eventuallyEq_nhds.mono fun y hy => by
      unfold wdb
      rw [hy.fderiv_eq (𝕜 := ℝ)]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  unfold wd
  rw [(hk k).fderiv_eq (𝕜 := ℝ)]

end

end ReciprocityTheory.L2DbarEstimates.Y
end
