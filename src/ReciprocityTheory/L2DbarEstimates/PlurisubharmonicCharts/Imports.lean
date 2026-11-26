module

public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.BStep

@[expose] public section

section -- merged from ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.SetLIntegralBiUnionLe
section -- merged from ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.ZLocLower
namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Pointwise Matrix

noncomputable section

namespace WeightedAtlas

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]

theorem real_bound {d F Ssq Wsq C1 B2 c m6 : ℝ} {T n : ℕ} (hnT' : n < T) (hd : 0 ≤ d)
    (hF0 : 0 ≤ F) (hF : F ≤ (C1 * d ^ (T - n)) ^ 2 * B2) (hB2 : 0 ≤ B2) (hc : 0 < c)
    (hS : c * d ^ 2 ≤ Ssq) (hm : 0 < m6) (hW : m6 ≤ Wsq) :
    F * Ssq ^ (-((T : ℝ) - 1 / 2)) * Wsq ^ (-(1 / 2 : ℝ)) ≤
      (C1 ^ 2 * B2 * c ^ (-((T : ℝ) - 1 / 2)) * m6 ^ (-(1 / 2 : ℝ))) *
        d ^ (-2 * ((n : ℝ) - 1 / 2)) := by
  have hnT : n ≤ T := hnT'.le
  have hK : 0 ≤ C1 ^ 2 * B2 * c ^ (-((T : ℝ) - 1 / 2)) * m6 ^ (-(1 / 2 : ℝ)) := by positivity
  rcases hd.eq_or_lt with h0 | hdpos
  · subst h0
    have hz : (0:ℝ) ^ (T - n) = 0 := zero_pow (by omega)
    rw [hz, mul_zero] at hF
    have hF' : F = 0 := le_antisymm (by simpa using hF) hF0
    rw [hF', zero_mul, zero_mul]
    positivity
  · have hSpos : 0 < Ssq := lt_of_lt_of_le (by positivity) hS
    have h1 : Ssq ^ (-((T : ℝ) - 1 / 2)) ≤ (c * d ^ 2) ^ (-((T : ℝ) - 1 / 2)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hS (by
        have : (1:ℝ) ≤ T := by exact_mod_cast (show 1 ≤ T by omega)
        linarith)
    have h2 : Wsq ^ (-(1 / 2 : ℝ)) ≤ m6 ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hm hW (by norm_num)
    calc F * Ssq ^ (-((T : ℝ) - 1 / 2)) * Wsq ^ (-(1 / 2 : ℝ))
        ≤ ((C1 * d ^ (T - n)) ^ 2 * B2) * (c * d ^ 2) ^ (-((T : ℝ) - 1 / 2)) *
            m6 ^ (-(1 / 2 : ℝ)) := by
          have hW0 : 0 ≤ Wsq ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (hm.le.trans hW) _
          have hS0 : 0 ≤ Ssq ^ (-((T : ℝ) - 1 / 2)) := Real.rpow_nonneg hSpos.le _
          gcongr
      _ = (C1 ^ 2 * B2 * c ^ (-((T : ℝ) - 1 / 2)) * m6 ^ (-(1 / 2 : ℝ))) *
            d ^ (-2 * ((n : ℝ) - 1 / 2)) := by
          have e1 : (d ^ (T - n)) ^ 2 = d ^ (2 * ((T : ℝ) - n)) := by
            rw [← pow_mul, ← Real.rpow_natCast]
            congr 1
            push_cast [Nat.cast_sub hnT]
            ring
          have e2 : (c * d ^ 2) ^ (-((T : ℝ) - 1 / 2)) =
              c ^ (-((T : ℝ) - 1 / 2)) * d ^ (-2 * ((T : ℝ) - 1 / 2)) := by
            rw [Real.mul_rpow hc.le (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hd]
            push_cast
            ring_nf
          have e3 : d ^ (2 * ((T : ℝ) - n)) * d ^ (-2 * ((T : ℝ) - 1 / 2)) =
              d ^ (-2 * ((n : ℝ) - 1 / 2)) := by
            rw [← Real.rpow_add hdpos]; ring_nf
          rw [mul_pow, e1, e2]
          rw [← e3]
          ring

theorem sqn_s_eq (A : WeightedAtlas n Y ι La) {L : La} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ}
    (hs : ∀ k, A.IsSec L (s k)) {i : ι} {x : Y} (hx : x ∈ (A.chart i).source)
    (hw : w0 i x ≠ 0) :
    A.sqn L s x = ‖w0 i x‖ ^ 2 * Real.exp (-A.ph L i x) * ‖A.zLoc w0 s i (A.chart i x)‖ ^ 2 := by
  unfold sqn
  rw [EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [A.nsq_eq_chart (hs k) hx]
  simp only [zLoc, PiLp.toLp_apply, (A.chart i).left_inv hx, norm_div, div_pow]
  have : ‖w0 i x‖ ^ 2 ≠ 0 := by positivity
  field_simp

theorem zLoc_lower (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ}
    {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} (hD : A.D0 L w w0 s) (hn : 1 ≤ n) {P : Y}
    (hP : P ∈ A.zeroSet s) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ v in 𝓝 (A.chart (A.pick P) P),
      ‖v - A.chart (A.pick P) P‖ ≤ K * ‖A.zLoc w0 s (A.pick P) v‖ := by
  set i := A.pick P
  set vP := A.chart i P
  set zL := A.zLoc w0 s i
  have hdet : (fderiv ℂ zL vP).det ≠ 0 := hD.coord P hP
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hdiff : DifferentiableAt ℂ zL vP := by
    by_contra h
    apply hdet
    rw [fderiv_zero_of_not_differentiableAt h]
    show LinearMap.det ((0 : V n →L[ℂ] V n) : V n →ₗ[ℂ] V n) = 0
    rw [ContinuousLinearMap.toLinearMap_zero, LinearMap.det_zero, finrank_euclideanSpace, Fintype.card_fin]
    exact zero_pow (by omega)
  have hz0 : zL vP = 0 := by
    ext k
    simp only [zL, zLoc, PiLp.toLp_apply, vP, (A.chart i).left_inv (A.mem_pick P)]
    rw [hP k]; simp
  set D := fderiv ℂ zL vP
  set E := (LinearMap.equivOfDetNeZero (D : V n →ₗ[ℂ] V n) hdet).toContinuousLinearEquiv
  obtain ⟨K0, hK0⟩ : ∃ K0 : ℝ, ∀ u, ‖u‖ ≤ K0 * ‖D u‖ := by
    refine ⟨‖(E.symm : V n →L[ℂ] V n)‖, fun u => ?_⟩
    have h := E.antilipschitz.le_mul_dist u 0
    simp only [dist_zero_right, map_zero] at h
    exact h
  set K1 := max K0 1
  have hK1 : 0 < K1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hlo := hdiff.hasFDerivAt.isLittleO
  have hev := hlo.def (show (0:ℝ) < 1 / (2 * K1) by positivity)
  refine ⟨2 * K1, by positivity, ?_⟩
  filter_upwards [hev] with v hv
  rw [hz0, sub_zero] at hv
  have h1 : ‖v - vP‖ ≤ K1 * ‖D (v - vP)‖ :=
    (hK0 _).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have h2 : ‖D (v - vP)‖ ≤ ‖zL v‖ + ‖zL v - D (v - vP)‖ := by
    have := norm_sub_le (zL v) (zL v - D (v - vP))
    rwa [sub_sub_cancel] at this
  have h3 : K1 * (1 / (2 * K1) * ‖v - vP‖) = ‖v - vP‖ / 2 := by field_simp
  nlinarith [norm_nonneg (zL v - D (v - vP)), norm_nonneg (zL v)]

theorem local_int (A : WeightedAtlas n Y ι La) (hMVI : MVIntStatement n) (hn : 2 ≤ n) {L : La}
    {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ}
    (hD : A.D0 L w w0 s) {la : La} {f : ι → Y → ℂ} (hf : A.IsSec la f) {T : ℕ}
    (hT : n + 1 ≤ T) {P : Y} (hP : P ∈ A.zeroSet s) (hv : A.VanishOrd f P (T - n)) :
    ∃ U : Set Y, IsOpen U ∧ P ∈ U ∧
      ∫⁻ y in U, ENNReal.ofReal (A.nsq la f y * A.sqn L s y ^ (-((T : ℝ) - 1 / 2)) *
        A.sqn L w y ^ (-(1 / 2 : ℝ))) ∂A.mu < ⊤ := by
  set i := A.pick P with hi
  set e := A.chart i with he
  set vP := e P with hvP
  have hPs : P ∈ e.source := A.mem_pick P
  have hvt : vP ∈ e.target := e.map_source hPs
  have htn : e.target ∈ 𝓝 vP := e.open_target.mem_nhds hvt
  have hsymm : ContinuousAt e.symm vP := e.continuousAt_symm hvt
  have hsP : e.symm vP = P := e.left_inv hPs
  have cph : ∀ la' : La, ContinuousAt (fun v => A.ph la' i (e.symm v)) vP := fun la' =>
    (A.smooth_ph la' i).continuousOn.continuousAt htn
  have cw0 : ContinuousAt (fun v => w0 i (e.symm v)) vP := by
    have h := (hD.isSection_denom.1 i).continuousOn
    simp only [Set.preimage_univ, Set.inter_univ] at h
    exact h.continuousAt htn
  obtain ⟨C1, hC1⟩ := hv
  obtain ⟨K3, hK3pos, hK3⟩ := A.zLoc_lower hD (by omega) hP
  set B2 := Real.exp (-A.ph la i P) + 1 with hB2
  have hE2 : ∀ᶠ v in 𝓝 vP, Real.exp (-A.ph la i (e.symm v)) < B2 := by
    have hc : ContinuousAt (fun v => Real.exp (-A.ph la i (e.symm v))) vP :=
      Real.continuous_exp.continuousAt.comp (cph la).neg
    exact hc.eventually (eventually_lt_nhds (by simp only [hsP]; linarith))
  set g4 : V n → ℝ := fun v => ‖w0 i (e.symm v)‖ ^ 2 * Real.exp (-A.ph L i (e.symm v)) with hg4
  have g4P : 0 < g4 vP := by
    simp only [g4, hsP]
    have := hD.w0_ne P hP
    positivity
  have hE4 : ∀ᶠ v in 𝓝 vP, g4 vP / 2 < g4 v :=
    ((cw0.norm.pow 2).mul (Real.continuous_exp.continuousAt.comp (cph L).neg)).eventually
      (eventually_gt_nhds (half_lt_self g4P))
  set g6 : V n → ℝ := fun v => A.sqn L w (e.symm v) with hg6
  have g6P : 0 < g6 vP := by
    simp only [g6, hsP]
    obtain ⟨k, hk⟩ := hD.no_common_zero P
    have h0 : 0 < A.nsq L (w k) P := by
      unfold nsq
      have := norm_pos_iff.2 hk
      positivity
    exact lt_of_lt_of_le h0 (Finset.single_le_sum (f := fun j => A.nsq L (w j) P)
      (fun j _ => A.nsq_nonneg L (w j) P) (Finset.mem_univ k))
  have hE6 : ∀ᶠ v in 𝓝 vP, g6 vP / 2 < g6 v :=
    ((A.continuous_sqn hD.sec_w).continuousAt.comp hsymm).eventually
      (eventually_gt_nhds (half_lt_self g6P))
  set B7 := Real.exp (A.ph A.kap i P) + 1 with hB7
  have hE7 : ∀ᶠ v in 𝓝 vP, Real.exp (A.ph A.kap i (e.symm v)) < B7 := by
    have hc : ContinuousAt (fun v => Real.exp (A.ph A.kap i (e.symm v))) vP :=
      Real.continuous_exp.continuousAt.comp (cph A.kap)
    exact hc.eventually (eventually_lt_nhds (by simp only [hsP]; linarith))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1
    ((show ∀ᶠ v in 𝓝 vP, v ∈ e.target from htn).and (hC1.and (hE2.and (hK3.and (hE4.and (hE6.and hE7))))))
  set r := min ε 1 with hr
  set W := Metric.ball vP r with hW
  have hWb : W ⊆ Metric.ball vP ε := Metric.ball_subset_ball (min_le_left _ _)
  have hWt : W ⊆ e.target := fun v hv => (hball v (hWb hv)).1
  have hUo : IsOpen (e.source ∩ e ⁻¹' W) := e.isOpen_inter_preimage Metric.isOpen_ball
  refine ⟨e.source ∩ e ⁻¹' W, hUo, ⟨hPs, Set.mem_preimage.mpr (Metric.mem_ball_self (lt_min hε one_pos))⟩, ?_⟩
  set c := (g4 vP / 2) / K3 ^ 2 with hc
  have hcpos : 0 < c := by positivity
  set m6 := g6 vP / 2 with hm6
  have hm6pos : 0 < m6 := by positivity
  set K := C1 ^ 2 * B2 * c ^ (-((T : ℝ) - 1 / 2)) * m6 ^ (-(1 / 2 : ℝ)) with hK
  have hB2pos : 0 < B2 := by positivity
  have hKnn : 0 ≤ K := by positivity
  set ψ : V n → ℝ≥0∞ := fun v => ENNReal.ofReal ‖v - vP‖ ^ (-2 * ((n : ℝ) - 1 / 2)) with hψ
  have hψc : Continuous ψ :=
    ENNReal.continuous_rpow_const.comp
      (ENNReal.continuous_ofReal.comp (continuous_norm.comp (continuous_id.sub continuous_const)))
  have hpt : ∀ x ∈ e.source ∩ e ⁻¹' W,
      ENNReal.ofReal (A.nsq la f x * A.sqn L s x ^ (-((T : ℝ) - 1 / 2)) *
        A.sqn L w x ^ (-(1 / 2 : ℝ))) ≤ ENNReal.ofReal K * ψ (e x) := by
    rintro x ⟨hxs, hxW⟩
    obtain ⟨-, h1, h2, h3, h4, h6, -⟩ := hball (e x) (hWb hxW)
    have hx : e.symm (e x) = x := e.left_inv hxs
    simp only [g4, g6, hx] at h4 h6
    rw [hx] at h1 h2
    set d := ‖e x - vP‖ with hd
    have hw0 : w0 i x ≠ 0 := by
      intro h
      rw [h, norm_zero] at h4
      have : g4 vP / 2 < 0 := by simpa using h4
      linarith
    have hS : c * d ^ 2 ≤ A.sqn L s x := by
      rw [A.sqn_s_eq hD.sec_s hxs hw0]
      set z := ‖A.zLoc w0 s i (e x)‖
      have hz : d ^ 2 ≤ K3 ^ 2 * z ^ 2 := by
        rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) h3 2
      have hc1 : c * d ^ 2 ≤ (g4 vP / 2) * z ^ 2 := by
        rw [hc, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith [g4P]
      exact hc1.trans (mul_le_mul_of_nonneg_right h4.le (sq_nonneg _))
    have hF : A.nsq la f x ≤ (C1 * d ^ (T - n)) ^ 2 * B2 := by
      rw [A.nsq_eq_chart hf hxs]
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) h1 2) h2.le (Real.exp_pos _).le
        (sq_nonneg _)
    have hR := real_bound (T := T) (n := n) (by omega) (norm_nonneg _) (A.nsq_nonneg la f x) hF
      hB2pos.le hcpos hS hm6pos h6.le
    calc ENNReal.ofReal (A.nsq la f x * A.sqn L s x ^ (-((T : ℝ) - 1 / 2)) *
          A.sqn L w x ^ (-(1 / 2 : ℝ)))
        ≤ ENNReal.ofReal (K * d ^ (-2 * ((n : ℝ) - 1 / 2))) := ENNReal.ofReal_le_ofReal hR
      _ = ENNReal.ofReal K * ENNReal.ofReal (d ^ (-2 * ((n : ℝ) - 1 / 2))) :=
          ENNReal.ofReal_mul hKnn
      _ ≤ ENNReal.ofReal K * ψ (e x) := by
          gcongr
          rcases (norm_nonneg (e x - vP)).eq_or_lt with h0 | hpos
          · rw [← hd] at h0
            rw [← h0, Real.zero_rpow (by
              have : (2:ℝ) ≤ n := by exact_mod_cast hn
              linarith)]
            simp
          · simp only [ψ]
            rw [ENNReal.ofReal_rpow_of_pos hpos]
  have hUm : MeasurableSet (e.source ∩ e ⁻¹' W) := hUo.measurableSet
  calc ∫⁻ y in e.source ∩ e ⁻¹' W, ENNReal.ofReal (A.nsq la f y *
        A.sqn L s y ^ (-((T : ℝ) - 1 / 2)) * A.sqn L w y ^ (-(1 / 2 : ℝ))) ∂A.mu
      ≤ ∫⁻ y in e.source ∩ e ⁻¹' W, ENNReal.ofReal K * ψ (e y) ∂A.mu :=
        setLIntegral_mono' hUm hpt
    _ = ENNReal.ofReal K * ∫⁻ y in e.source ∩ e ⁻¹' W, ψ (e y) ∂A.mu :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal K * (ENNReal.ofReal B7 * ∫⁻ v in W, ψ v) := by
        gcongr
        exact A.lintegral_chart_le i P Metric.isOpen_ball hWt _
          (fun v hv => ENNReal.ofReal_le_ofReal (hball v (hWb hv)).2.2.2.2.2.2.le) ψ hψc
    _ < ⊤ := by
        refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_)
        exact lintegral_ball_rpow_lt_top hMVI (by omega) vP (min_le_right _ _) (by linarith)

end WeightedAtlas

end

end ReciprocityTheory.L2DbarEstimates.Y
end

namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Pointwise Matrix

noncomputable section

namespace WeightedAtlas

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]

theorem sqn_pos_of_ne (A : WeightedAtlas n Y ι La) {la : La} {N : ℕ} {w : Fin N → ι → Y → ℂ}
    {y : Y} (h : ∃ k, w k (A.pick y) y ≠ 0) : 0 < A.sqn la w y := by
  obtain ⟨k, hk⟩ := h
  have h0 : 0 < A.nsq la (w k) y := by
    unfold nsq
    have := norm_pos_iff.2 hk
    positivity
  exact lt_of_lt_of_le h0 (Finset.single_le_sum (f := fun j => A.nsq la (w j) y)
    (fun j _ => A.nsq_nonneg la (w j) y) (Finset.mem_univ k))

theorem sqn_pos_of_notMem (A : WeightedAtlas n Y ι La) {la : La} {N : ℕ} {s : Fin N → ι → Y → ℂ}
    {y : Y} (h : y ∉ A.zeroSet s) : 0 < A.sqn la s y := by
  apply A.sqn_pos_of_ne
  simpa [zeroSet] using h

theorem setLIntegral_biUnion_le {α κ : Type*} [MeasurableSpace α] (μ : Measure α)
    (F : Finset κ) (U : κ → Set α) (G : α → ℝ≥0∞) :
    ∫⁻ y in ⋃ P ∈ F, U P, G y ∂μ ≤ ∑ P ∈ F, ∫⁻ y in U P, G y ∂μ := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | insert a F ha ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
    exact (lintegral_union_le _ _ _).trans (add_le_add le_rfl ih)

theorem start_int (A : WeightedAtlas n Y ι La) (hMVI : MVIntStatement n) (hn : 2 ≤ n) {L : La}
    {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ}
    (hD : A.D0 L w w0 s) {la : La} {f : ι → Y → ℂ} (hf : A.IsSec la f) {T : ℕ}
    (hT : n + 1 ≤ T)
    (hint : ∫⁻ y, ENNReal.ofReal (A.nsq la f y * A.sqn L w y ^ (-(T : ℝ))) ∂A.mu < ⊤)
    (hvan : ∀ P ∈ A.zeroSet s, A.VanishOrd f P (T - n)) :
    ∫⁻ y, ENNReal.ofReal (A.nsq la f y * A.sqn L s y ^ (-((T : ℝ) - 1 / 2)) *
      A.sqn L w y ^ (-(1 / 2 : ℝ))) ∂A.mu < ⊤ := by
  classical
  set G : Y → ℝ≥0∞ := fun y => ENNReal.ofReal (A.nsq la f y * A.sqn L s y ^ (-((T : ℝ) - 1 / 2)) *
      A.sqn L w y ^ (-(1 / 2 : ℝ))) with hG
  have hloc : ∀ P ∈ A.zeroSet s, ∃ U : Set Y, IsOpen U ∧ P ∈ U ∧ ∫⁻ y in U, G y ∂A.mu < ⊤ :=
    fun P hP => A.local_int hMVI hn hD hf hT hP (hvan P hP)
  choose! U hUo hPU hUint using hloc
  set F := hD.finite_S.toFinset
  set V := ⋃ P ∈ F, U P with hV
  have hVo : IsOpen V := isOpen_biUnion (fun P hP => hUo P ((Set.Finite.mem_toFinset _).1 hP))
  have hSV : A.zeroSet s ⊆ V := fun P hP =>
    Set.mem_biUnion ((Set.Finite.mem_toFinset _).2 hP) (hPU P hP)
  obtain ⟨C, hC⟩ := hD.family_le_coords V hVo hSV
  set a : ℝ := (T : ℝ) - 1 / 2 with ha
  have hpt : ∀ y ∈ Vᶜ, G y ≤ ENNReal.ofReal (C ^ a) *
      ENNReal.ofReal (A.nsq la f y * A.sqn L w y ^ (-(T : ℝ))) := by
    intro y hy
    have hyS : y ∉ A.zeroSet s := fun h => hy (hSV h)
    have hs := A.sqn_pos_of_notMem (la := L) hyS
    have hw := A.sqn_pos_of_ne (la := L) (hD.no_common_zero y)
    have hCy := hC y hy
    have hCpos : 0 < C := by
      by_contra hc
      have hc' := not_lt.1 hc
      nlinarith
    have h1 : A.sqn L s y ^ (-a) ≤ (A.sqn L w y / C) ^ (-a) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by rw [div_le_iff₀ hCpos]; linarith)
        (by have : (1:ℝ) ≤ T := by exact_mod_cast (show 1 ≤ T by omega)
            linarith)
    have h2 : (A.sqn L w y / C) ^ (-a) * A.sqn L w y ^ (-(1 / 2 : ℝ)) =
        C ^ a * A.sqn L w y ^ (-(T : ℝ)) := by
      rw [Real.div_rpow hw.le hCpos.le, Real.rpow_neg hCpos.le, div_inv_eq_mul, mul_comm _ (C ^ a),
        mul_assoc, ← Real.rpow_add hw]
      congr 2
      ring
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hn0 := A.nsq_nonneg la f y
    calc A.nsq la f y * A.sqn L s y ^ (-a) * A.sqn L w y ^ (-(1 / 2 : ℝ))
        ≤ A.nsq la f y * (A.sqn L w y / C) ^ (-a) * A.sqn L w y ^ (-(1 / 2 : ℝ)) := by
          have := Real.rpow_nonneg hw.le (-(1 / 2 : ℝ))
          gcongr
      _ = C ^ a * (A.nsq la f y * A.sqn L w y ^ (-(T : ℝ))) := by
          rw [mul_assoc, h2]; ring
  calc ∫⁻ y, G y ∂A.mu = ∫⁻ y in V ∪ Vᶜ, G y ∂A.mu := by
        rw [Set.union_compl_self, Measure.restrict_univ]
    _ ≤ ∫⁻ y in V, G y ∂A.mu + ∫⁻ y in Vᶜ, G y ∂A.mu := lintegral_union_le _ _ _
    _ ≤ ∑ P ∈ F, ∫⁻ y in U P, G y ∂A.mu + ∫⁻ y in Vᶜ, ENNReal.ofReal (C ^ a) *
          ENNReal.ofReal (A.nsq la f y * A.sqn L w y ^ (-(T : ℝ))) ∂A.mu :=
        add_le_add (setLIntegral_biUnion_le _ _ _ _) (setLIntegral_mono' hVo.measurableSet.compl hpt)
    _ ≤ ∑ P ∈ F, ∫⁻ y in U P, G y ∂A.mu + ∫⁻ y, ENNReal.ofReal (C ^ a) *
          ENNReal.ofReal (A.nsq la f y * A.sqn L w y ^ (-(T : ℝ))) ∂A.mu :=
        add_le_add le_rfl (setLIntegral_le_lintegral _ _)
    _ < ⊤ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine ENNReal.add_lt_top.2 ⟨ENNReal.sum_lt_top.2 (fun P hP => hUint P
          ((Set.Finite.mem_toFinset _).1 hP)), ENNReal.mul_lt_top ENNReal.ofReal_lt_top hint⟩

theorem end_int (A : WeightedAtlas n Y ι La) (hn : 1 ≤ n) {L : La}
    {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ}
    (hD : A.D0 L w w0 s) {la : La} {h : ι → Y → ℂ}
    (hint : ∫⁻ y, ENNReal.ofReal (A.nsq la h y * A.sqn L s y ^ (-((n : ℝ) - 1 / 2)) *
      A.sqn L w y ^ (-(1 / 2 : ℝ))) ∂A.mu < ⊤) :
    ∫⁻ y, ENNReal.ofReal (A.nsq la h y * A.sqn L w y ^ (-(n : ℝ))) ∂A.mu < ⊤ := by
  have : NullSingletonClass A.mu := ⟨fun x => A.mu_singleton hn x⟩
  have hS0 : A.mu (A.zeroSet s) = 0 := hD.finite_S.measure_zero A.mu
  obtain ⟨C, hC⟩ := hD.s_le_w
  set a : ℝ := (n : ℝ) - 1 / 2 with ha
  have hae : ∀ᵐ y ∂A.mu, ENNReal.ofReal (A.nsq la h y * A.sqn L w y ^ (-(n : ℝ))) ≤
      ENNReal.ofReal (C ^ a) * ENNReal.ofReal (A.nsq la h y * A.sqn L s y ^ (-a) *
        A.sqn L w y ^ (-(1 / 2 : ℝ))) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hS0] with y hyS
    have hs := A.sqn_pos_of_notMem (la := L) hyS
    have hw := A.sqn_pos_of_ne (la := L) (hD.no_common_zero y)
    have hCy := hC y
    have hCpos : 0 < C := by
      by_contra hc
      have hc' := not_lt.1 hc
      nlinarith
    have hna : 0 ≤ a := by
      have : (1:ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have h1 : (C * A.sqn L w y) ^ (-a) ≤ A.sqn L s y ^ (-a) :=
      Real.rpow_le_rpow_of_nonpos hs hCy (by linarith)
    have h2 : A.sqn L w y ^ (-(n : ℝ)) =
        C ^ a * ((C * A.sqn L w y) ^ (-a) * A.sqn L w y ^ (-(1 / 2 : ℝ))) := by
      rw [Real.mul_rpow hCpos.le hw.le, ← mul_assoc, ← mul_assoc, ← Real.rpow_add hCpos,
        mul_assoc, ← Real.rpow_add hw]
      have e1 : a + -a = 0 := by ring
      have e2 : -a + -(1 / 2 : ℝ) = -(n : ℝ) := by rw [ha]; ring
      rw [e1, e2, Real.rpow_zero, one_mul]
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hn0 := A.nsq_nonneg la h y
    have := Real.rpow_nonneg hw.le (-(1 / 2 : ℝ))
    have := Real.rpow_nonneg hCpos.le a
    rw [h2]
    calc A.nsq la h y * (C ^ a * ((C * A.sqn L w y) ^ (-a) * A.sqn L w y ^ (-(1 / 2 : ℝ))))
        = C ^ a * (A.nsq la h y * (C * A.sqn L w y) ^ (-a) * A.sqn L w y ^ (-(1 / 2 : ℝ))) := by
          ring
      _ ≤ C ^ a * (A.nsq la h y * A.sqn L s y ^ (-a) * A.sqn L w y ^ (-(1 / 2 : ℝ))) := by
          gcongr
  calc ∫⁻ y, ENNReal.ofReal (A.nsq la h y * A.sqn L w y ^ (-(n : ℝ))) ∂A.mu
      ≤ ∫⁻ y, ENNReal.ofReal (C ^ a) * ENNReal.ofReal (A.nsq la h y * A.sqn L s y ^ (-a) *
        A.sqn L w y ^ (-(1 / 2 : ℝ))) ∂A.mu := lintegral_mono_ae hae
    _ < ⊤ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hint

theorem sum_int (A : WeightedAtlas n Y ι La) {la : La} {κ : Type*} (F : Finset κ)
    (h : κ → ι → Y → ℂ) (hh : ∀ q ∈ F, A.IsSec la (h q)) (Wt : Y → ℝ) (hWt : Measurable Wt)
    (hW0 : ∀ y, 0 ≤ Wt y)
    (hint : ∀ q ∈ F, ∫⁻ y, ENNReal.ofReal (A.nsq la (h q) y * Wt y) ∂A.mu < ⊤) :
    ∫⁻ y, ENNReal.ofReal (A.nsq la (fun i y => ∑ q ∈ F, h q i y) y * Wt y) ∂A.mu < ⊤ := by
  have hpt : ∀ y, ENNReal.ofReal (A.nsq la (fun i y => ∑ q ∈ F, h q i y) y * Wt y) ≤
      ENNReal.ofReal (F.card : ℝ) * ∑ q ∈ F, ENNReal.ofReal (A.nsq la (h q) y * Wt y) := by
    intro y
    rw [← ENNReal.ofReal_sum_of_nonneg (fun q _ => mul_nonneg (A.nsq_nonneg _ _ _) (hW0 y)),
      ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [← Finset.sum_mul, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (A.nsq_sum_le la F h y) (hW0 y)
  calc _ ≤ ∫⁻ y, ENNReal.ofReal (F.card : ℝ) *
        ∑ q ∈ F, ENNReal.ofReal (A.nsq la (h q) y * Wt y) ∂A.mu := lintegral_mono hpt
    _ = ENNReal.ofReal (F.card : ℝ) * ∑ q ∈ F, ∫⁻ y, ENNReal.ofReal (A.nsq la (h q) y * Wt y) ∂A.mu := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_finsetSum']
        intro q hq
        exact (ENNReal.measurable_ofReal.comp
          ((A.continuous_nsq (hh q hq)).measurable.mul hWt)).aemeasurable
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.sum_lt_top.2 hint)

end WeightedAtlas

end

end ReciprocityTheory.L2DbarEstimates.Y
end

namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Pointwise Matrix

noncomputable section

universe u

theorem b (n : ℕ) (Y : Type u) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι : Type*) (La : Type*) [AddCommGroup La] (hS : SAll.{u} n) (hE : EXTStatement n) (hN : EXTNullStatement n)
    (hLSE : LSEAll.{u} n) (hMVI : MVIntStatement n) : BStatement n Y ι La := by
  classical
  intro A L mu0 N w w0 s De σ T f hn hD hF hX hσ hpos hT hf hint hvan
  have h0 := A.start_int hMVI hn hD hf hT hint hvan
  have key : ∀ m, m ≤ T - n → ∃ hh : (Fin m → Fin n) → ι → Y → ℂ,
      (∀ q, A.IsSec (mu0 + (T - m) • L) (hh q) ∧
        ∫⁻ y, ENNReal.ofReal (A.nsq (mu0 + (T - m) • L) (hh q) y *
          A.sqn L s y ^ (-(((T - m : ℕ) : ℝ) - 1 / 2)) * A.sqn L w y ^ (-(1 / 2 : ℝ))) ∂A.mu
            < ⊤) ∧
      ∀ i y, y ∈ (A.chart i).source → f i y = ∑ q, (∏ j, s (q j) i y) * hh q i y := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨fun _ => f, fun q => ⟨by simpa using hf, by simpa using h0⟩, fun i y _ => ?_⟩
      simp
    | succ m ih =>
      intro hm
      obtain ⟨hh, hhP, hsum⟩ := ih (by omega)
      have hT' : n + 1 ≤ T - m := by omega
      choose H hH hHsum using fun q =>
        b_step A hS hE hN hLSE hn hD hF hX hσ hpos (T - m) hT' (hh q) (hhP q).1 (hhP q).2
      refine ⟨fun q' => H (Fin.tail q') (q' 0), fun q' => ?_, ?_⟩
      · have e1 : T - (m + 1) = T - m - 1 := by omega
        have e2 : (((T - m - 1 : ℕ) : ℝ) - 1 / 2) = ((T - m : ℕ) : ℝ) - 3 / 2 := by
          rw [Nat.cast_sub (show 1 ≤ T - m by omega)]
          push_cast
          ring
        obtain ⟨h1, h2⟩ := hH (Fin.tail q') (q' 0)
        rw [e1, e2]
        exact ⟨h1, h2⟩
      · intro i y hy
        rw [hsum i y hy, ← (Fin.consEquiv (fun _ => Fin n)).sum_comp, Fintype.sum_prod_type]
        simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun q _ => ?_)
        rw [hHsum q i y hy, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [Fin.tail_cons]
        ring
  obtain ⟨hh, hhP, hsum⟩ := key (T - n) le_rfl
  have eT : T - (T - n) = n := by omega
  rw [eT] at hhP
  set cnt : (Fin (T - n) → Fin n) → Fin n → ℕ :=
    fun q k => (Finset.univ.filter (fun j => q j = k)).card with hcnt
  refine ⟨fun α i y => ∑ q ∈ Finset.univ.filter (fun q => cnt q = α), hh q i y,
    fun α _ => ⟨?_, ?_⟩, ?_⟩
  · exact A.isSec_sum _ (fun q _ => (hhP q).1)
  · exact A.sum_int _ hh (fun q _ => (hhP q).1) (fun y => A.sqn L w y ^ (-(n : ℝ)))
      ((A.continuous_sqn hD.sec_w).measurable.pow_const _)
      (fun y => Real.rpow_nonneg (A.sqn_nonneg _ _ y) _)
      (fun q _ => A.end_int (by omega) hD (hhP q).2)
  · intro i y hy
    rw [hsum i y hy]
    have hmaps : ∀ q ∈ (Finset.univ : Finset (Fin (T - n) → Fin n)),
        cnt q ∈ Finset.Nat.antidiagonalTuple n (T - n) := by
      intro q _
      rw [Finset.Nat.mem_antidiagonalTuple]
      simp only [cnt]
      rw [← Finset.card_eq_sum_card_fiberwise (fun j _ => Finset.mem_univ (q j))]
      simp
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    refine Finset.sum_congr rfl (fun α _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun q hq => ?_)
    have hq' : cnt q = α := (Finset.mem_filter.1 hq).2
    congr 1
    rw [← hq', ← Finset.prod_fiberwise Finset.univ q (fun j => s (q j) i y)]
    refine Finset.prod_congr rfl (fun k _ => ?_)
    rw [Finset.prod_congr rfl (fun j hj => by rw [(Finset.mem_filter.1 hj).2]), Finset.prod_const]

end

end ReciprocityTheory.L2DbarEstimates.Y
