module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.InfRight
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ToMKMulInv

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsMInfNhd
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IdThmB
noncomputable section

open Matrix
open scoped ComplexOrder

namespace ReciprocityTheory.ChartRestriction.DS.S7

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

namespace IdB

lemma quad_norm_le (H : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) :
    ‖star v ⬝ᵥ (H *ᵥ v)‖ ≤ (n : ℝ) * n * (‖v‖ * ‖H‖ * ‖v‖) := by
  have hvi : ∀ i, ‖v i‖ ≤ ‖v‖ := fun i => norm_le_pi_norm v i
  have hH : ∀ i j, ‖H i j‖ ≤ ‖H‖ := fun i j => norm_entry_le_entrywise_sup_norm H
  have key : ∀ i, ‖star (v i) * ∑ j, H i j * v j‖ ≤ ∑ _j : Fin n, ‖v‖ * ‖H‖ * ‖v‖ := by
    intro i
    rw [norm_mul, norm_star]
    refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [norm_mul]
    have h1 := mul_le_mul (hH i j) (hvi j) (norm_nonneg _) (norm_nonneg _)
    calc ‖v i‖ * (‖H i j‖ * ‖v j‖) ≤ ‖v‖ * (‖H‖ * ‖v‖) :=
          mul_le_mul (hvi i) h1 (by positivity) (norm_nonneg _)
      _ = ‖v‖ * ‖H‖ * ‖v‖ := by ring
  have e : star v ⬝ᵥ (H *ᵥ v) = ∑ i, star (v i) * ∑ j, H i j * v j := by
    simp only [dotProduct, mulVec, Pi.star_apply]
  rw [e]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun i _ => key i).trans (le_of_eq ?_))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

lemma quad_scale (x : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) (t : ℝ) :
    (star ((t : ℂ) • v) ⬝ᵥ (x *ᵥ ((t : ℂ) • v))).re = t ^ 2 * (star v ⬝ᵥ (x *ᵥ v)).re := by
  rw [star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul,
    ← mul_assoc]
  have : (t : ℂ) * star (t : ℂ) = ((t ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal]; push_cast; ring
  rw [this, Complex.re_ofReal_mul]

lemma quad_lower {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) :
    ∃ c > 0, ∀ v : Fin n → ℂ, c * ‖v‖ ^ 2 ≤ (star v ⬝ᵥ (x *ᵥ v)).re := by
  have hq : Continuous fun v : Fin n → ℂ => (star v ⬝ᵥ (x *ᵥ v)).re :=
    Complex.continuous_re.comp (continuous_id.star.dotProduct (continuous_const.matrix_mulVec continuous_id))
  have hpos : ∀ v : Fin n → ℂ, v ≠ 0 → 0 < (star v ⬝ᵥ (x *ᵥ v)).re := fun v hv => by
    have h := (Complex.lt_def.mp (hx.dotProduct_mulVec_pos hv)).1
    simpa using h
  have hnorm : ∀ v : Fin n → ℂ, v ≠ 0 → ‖((‖v‖⁻¹ : ℝ) : ℂ) • v‖ = 1 := fun v hv => by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]
  have hback : ∀ v : Fin n → ℂ, v ≠ 0 → ((‖v‖ : ℝ) : ℂ) • (((‖v‖⁻¹ : ℝ) : ℂ) • v) = v := fun v hv => by
    rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv), Complex.ofReal_one,
      one_smul]
  by_cases hS : ∃ u : Fin n → ℂ, ‖u‖ = 1
  · obtain ⟨u, hu⟩ := hS
    have hne : (Metric.sphere (0 : Fin n → ℂ) 1).Nonempty := ⟨u, by simpa using hu⟩
    obtain ⟨u0, hu0, hmin⟩ := (isCompact_sphere (0 : Fin n → ℂ) 1).exists_isMinOn hne hq.continuousOn
    have hu0n : ‖u0‖ = 1 := by simpa using hu0
    have hu00 : u0 ≠ 0 := by
      intro h
      rw [h, norm_zero] at hu0n
      exact zero_ne_one hu0n
    refine ⟨_, hpos u0 hu00, fun v => ?_⟩
    by_cases hv : v = 0
    · subst hv
      simp
    · set u := ((‖v‖⁻¹ : ℝ) : ℂ) • v
      have hum : u ∈ Metric.sphere (0 : Fin n → ℂ) 1 := by
        rw [mem_sphere_zero_iff_norm]
        exact hnorm v hv
      have h1 := hmin hum
      rw [← hback v hv, quad_scale]
      have : ‖((‖v‖ : ℝ) : ℂ) • u‖ = ‖v‖ := by rw [hback v hv]
      rw [this, mul_comm]
      exact mul_le_mul_of_nonneg_left h1 (by positivity)
  · refine ⟨1, one_pos, fun v => ?_⟩
    by_cases hv : v = 0
    · subst hv
      simp
    · exact absurd ⟨_, hnorm v hv⟩ hS

theorem posDef_nhd {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) :
    ∃ δ > 0, ∀ H : Matrix (Fin n) (Fin n) ℂ, H.IsHermitian → ‖H‖ < δ → (x + H).PosDef := by
  obtain ⟨c, hc, hq⟩ := quad_lower hx
  refine ⟨c / ((n : ℝ) * n + 1), by positivity, fun H hH hHn => ?_⟩
  rw [posDef_iff_dotProduct_mulVec]
  refine ⟨hx.isHermitian.add hH, fun v hv => ?_⟩
  rw [Complex.lt_def]
  have him := (hx.isHermitian.add hH).im_star_dotProduct_mulVec_self v
  have e : star v ⬝ᵥ ((x + H) *ᵥ v) = star v ⬝ᵥ (x *ᵥ v) + star v ⬝ᵥ (H *ᵥ v) := by
    rw [add_mulVec, dotProduct_add]
  refine ⟨?_, ?_⟩
  · rw [e, Complex.add_re, Complex.zero_re]
    have h1 := hq v
    have h2 := quad_norm_le H v
    have h3 : -‖star v ⬝ᵥ (H *ᵥ v)‖ ≤ (star v ⬝ᵥ (H *ᵥ v)).re := by
      have := Complex.abs_re_le_norm (star v ⬝ᵥ (H *ᵥ v))
      linarith [neg_abs_le (star v ⬝ᵥ (H *ᵥ v)).re]
    have hv2 : 0 < ‖v‖ ^ 2 := by have := norm_pos_iff.mpr hv; positivity
    have hN : (0 : ℝ) ≤ (n : ℝ) * n := by positivity
    have hHpos : 0 ≤ ‖H‖ := norm_nonneg _
    have hδ : ((n : ℝ) * n + 1) * ‖H‖ < c := by
      rw [lt_div_iff₀ (by positivity)] at hHn
      linarith
    have h4 : 0 < (c - (n : ℝ) * n * ‖H‖) * ‖v‖ ^ 2 := mul_pos (by nlinarith) hv2
    nlinarith
  · rw [Complex.zero_im]
    simpa using him.symm

theorem line_zero {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] (g : ℂ → F)
    (hg : ∀ s : ℂ, ‖s‖ < 2 → DifferentiableAt ℂ g s) (hr : ∀ t : ℝ, |t| < 2 → g t = 0) :
    g Complex.I = 0 := by
  have hDO : DifferentiableOn ℂ g (Metric.ball 0 2) := fun s hs =>
    (hg s (by simpa using hs)).differentiableWithinAt
  have han := hDO.analyticOnNhd Metric.isOpen_ball
  have ht : Filter.Tendsto (fun t : ℝ => (t : ℂ)) (nhdsWithin 0 {0}ᶜ) (nhdsWithin 0 {0}ᶜ) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · simpa using (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
    · exact eventually_nhdsWithin_of_forall fun t ht => by simpa using ht
  have hev : ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) {0}ᶜ, g (t : ℂ) = 0 := by
    have h2 : ∀ᶠ t in nhds (0 : ℝ), |t| < 2 := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) two_pos] with t ht
      simpa [Real.dist_eq] using ht
    exact (Filter.Eventually.filter_mono nhdsWithin_le_nhds h2).mono fun t h => hr t h
  have hfreq : ∃ᶠ s in nhdsWithin (0 : ℂ) {0}ᶜ, g s = 0 := ht.frequently hev.frequently
  have hz := han.eqOn_zero_of_preconnected_of_frequently_eq_zero (convex_ball (0 : ℂ) 2).isPreconnected
    (Metric.mem_ball_self two_pos) hfreq
  have hI : Complex.I ∈ Metric.ball (0 : ℂ) 2 := by
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_I]
    norm_num
  simpa using hz hI

end IdB

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

variable {ε : Fin n → Bool} {lam : Fin n → ℝ}

theorem psM_inf_nhd (T : KType ε (lowK ε lam)) (μ : Fin n → ℤ) (hμ : IsMu lam μ) :
    ∃ U : Set (Matrix (Fin n) (Fin n) ℂ), IsOpen U ∧ posSet n ⊆ U ∧ DifferentiableOn ℂ (psM T μ) U ∧
      ∀ z ∈ U, ∀ Y : Matrix (Fin n) (Fin n) ℂ, IsBlock ε Y →
        fderiv ℂ (psM T μ) z (z * Y) = -(T.dτ Y * psM T μ z) ∧
          fderiv ℂ (psM T μ) z (Y * z) = -(psM T μ z * T.dτ Y) := by
  obtain ⟨U0, hU0o, hpos0, hΩ, hdiff, hfd⟩ := psM_holo (μ := μ) T
  refine ⟨{z | ∃ x : Matrix (Fin n) (Fin n) ℂ, x.PosDef ∧ ∃ r : ℝ, 0 < r ∧ ‖z - x‖ < r ∧
      (∀ w : Matrix (Fin n) (Fin n) ℂ, ‖w - x‖ < 3 * r → w ∈ U0) ∧
      (∀ H : Matrix (Fin n) (Fin n) ℂ, H.IsHermitian → ‖H‖ < 3 * r → (x + H).PosDef)},
      ?_, ?_, ?_, ?_⟩
  · refine Metric.isOpen_iff.mpr ?_
    rintro z ⟨x, hx, r, hr, hzx, hU, hP⟩
    refine ⟨r - ‖z - x‖, sub_pos.mpr hzx, fun z' hz' => ⟨x, hx, r, hr, ?_, hU, hP⟩⟩
    rw [Metric.mem_ball, dist_eq_norm] at hz'
    have h1 : z' - x = (z' - z) + (z - x) := by abel
    rw [h1]
    have h2 := norm_add_le (z' - z) (z - x)
    linarith
  · intro x hx
    have hx' : x.PosDef := hx
    obtain ⟨δ, hδ, hδP⟩ := IdB.posDef_nhd hx'
    obtain ⟨e, he, heU⟩ := Metric.isOpen_iff.mp hU0o x (hpos0 hx)
    have hm : 0 < min δ e / 3 := div_pos (lt_min hδ he) (by norm_num)
    refine ⟨x, hx', min δ e / 3, hm, by rw [sub_self, norm_zero]; exact hm, ?_, ?_⟩
    · intro w hw
      apply heU
      rw [Metric.mem_ball, dist_eq_norm]
      have : min δ e ≤ e := min_le_right δ e
      linarith
    · intro H hH hHn
      apply hδP H hH
      have : min δ e ≤ δ := min_le_left δ e
      linarith
  · refine hdiff.mono ?_
    intro z hz
    obtain ⟨x, hx, r, hr, hzx, hU, hP⟩ := hz
    exact hU z (by linarith)
  · rintro z ⟨x, hx, r, hr, hzx, hU, hP⟩ Y hY
    have hxH : xᴴ = x := hx.1.eq
    have h12 : star (1 / 2 : ℂ) = 1 / 2 := by
      have h := Complex.conj_ofReal (1 / 2 : ℝ)
      push_cast at h
      exact h
    have hsI : star Complex.I = -Complex.I := Complex.conj_I
    have hn12 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
    obtain ⟨A, hA⟩ : ∃ A : Matrix (Fin n) (Fin n) ℂ, A = (1 / 2 : ℂ) • (z + zᴴ) := ⟨_, rfl⟩
    obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin n) (Fin n) ℂ,
        B = (1 / 2 : ℂ) • (Complex.I • (zᴴ - z)) := ⟨_, rfl⟩
    have hAH : A.IsHermitian := by
      rw [Matrix.IsHermitian, hA]
      ext i j
      simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul,
        star_mul', star_add, star_star, h12]
      ring
    have hBH : B.IsHermitian := by
      rw [Matrix.IsHermitian, hB]
      ext i j
      simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul,
        star_mul', star_sub, star_star, h12, hsI]
      ring
    have hAB : A + Complex.I • B = z := by
      rw [hA, hB]
      ext i j
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.conjTranspose_apply,
        smul_eq_mul]
      linear_combination ((1 / 2 : ℂ) * (star (z j i) - z i j)) * Complex.I_sq
    have hAx : A - x = (1 / 2 : ℂ) • ((z - x) + (z - x)ᴴ) := by
      rw [hA, Matrix.conjTranspose_sub, hxH]; module
    have hBx : B = (1 / 2 : ℂ) • (Complex.I • ((z - x)ᴴ - (z - x))) := by
      rw [hB, Matrix.conjTranspose_sub, hxH]; module
    have hAn : ‖A - x‖ ≤ ‖z - x‖ := by
      have h := norm_add_le (z - x) (z - x)ᴴ
      rw [Matrix.norm_conjTranspose] at h
      rw [hAx, norm_smul, hn12]
      linarith
    have hBn : ‖B‖ ≤ ‖z - x‖ := by
      have h := norm_sub_le (z - x)ᴴ (z - x)
      rw [Matrix.norm_conjTranspose] at h
      rw [hBx, norm_smul, norm_smul, hn12, Complex.norm_I]
      linarith
    have hbound : ∀ s : ℂ, ‖s‖ < 2 → ‖A + s • B - x‖ < 3 * r := by
      intro s hs
      have e1 : A + s • B - x = (A - x) + s • B := by abel
      rw [e1]
      have h1 := norm_add_le (A - x) (s • B)
      rw [norm_smul] at h1
      have h2 : ‖s‖ * ‖B‖ ≤ 2 * ‖z - x‖ := mul_le_mul hs.le hBn (norm_nonneg _) (by norm_num)
      linarith
    have key : ∀ s : ℂ, ‖s‖ < 2 → A + s • B ∈ U0 := fun s hs => hU _ (hbound s hs)
    have hposR : ∀ t : ℝ, |t| < 2 → (A + (t : ℂ) • B).PosDef := by
      intro t ht
      have hs : ‖(t : ℂ)‖ < 2 := by rwa [Complex.norm_real, Real.norm_eq_abs]
      have hBt : ((t : ℂ) • B).IsHermitian := by
        rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, hBH.eq]
        rw [show star (t : ℂ) = (t : ℂ) from Complex.conj_ofReal t]
      have hH : (A + (t : ℂ) • B - x).IsHermitian := (hAH.add hBt).sub hx.1
      have := hP _ hH (hbound _ hs)
      simpa using this
    have hI : ‖Complex.I‖ < 2 := by rw [Complex.norm_I]; norm_num
    constructor
    · let g : ℂ → (T.V →L[ℂ] T.V) := fun s =>
        ((Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ)) •
          (∫ k, IdA.dPhi2 μ (toMK k⁻¹ * (A + s • B) * toMK k,
            toMK k⁻¹ * (A * Y + s • (B * Y)) * toMK k) • (T.op k * projW T * T.op k⁻¹) ∂(muK ε))
          + T.dτ Y * psM T μ (A + s • B)
      have hgeq : ∀ s : ℂ, A + s • B ∈ U0 →
          g s = fderiv ℂ (psM T μ) (A + s • B) ((A + s • B) * Y) + T.dτ Y * psM T μ (A + s • B) := by
        intro s hs
        rw [hfd _ hs]
        simp only [g, add_mul, Matrix.smul_mul] <;> rfl
      have hgd : ∀ s : ℂ, ‖s‖ < 2 → DifferentiableAt ℂ g s := by
        intro s hs
        have hw : DifferentiableAt ℂ (fun y : ℂ => A + y • B) s :=
          (differentiableAt_const A).add (differentiableAt_id.smul_const B)
        have hψ := (hdiff.differentiableAt (hU0o.mem_nhds (key s hs))).comp s hw
        exact ((line_int_differentiableAt T μ hU0o hΩ A B (A * Y) (B * Y) (key s hs)).const_smul
          ((Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ))).add (hψ.const_mul (T.dτ Y))
      have hgr : ∀ t : ℝ, |t| < 2 → g t = 0 := by
        intro t ht
        have hs : ‖(t : ℂ)‖ < 2 := by rwa [Complex.norm_real, Real.norm_eq_abs]
        rw [hgeq _ (key _ hs), (psM_inf_right T μ hμ (hposR t ht) hY).1]
        simp
      have h0 := IdB.line_zero g hgd hgr
      rw [hgeq _ (key _ hI), hAB] at h0
      exact eq_neg_of_add_eq_zero_left h0
    · let g : ℂ → (T.V →L[ℂ] T.V) := fun s =>
        ((Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ)) •
          (∫ k, IdA.dPhi2 μ (toMK k⁻¹ * (A + s • B) * toMK k,
            toMK k⁻¹ * (Y * A + s • (Y * B)) * toMK k) • (T.op k * projW T * T.op k⁻¹) ∂(muK ε))
          + psM T μ (A + s • B) * T.dτ Y
      have hgeq : ∀ s : ℂ, A + s • B ∈ U0 →
          g s = fderiv ℂ (psM T μ) (A + s • B) (Y * (A + s • B)) + psM T μ (A + s • B) * T.dτ Y := by
        intro s hs
        rw [hfd _ hs]
        simp only [g, mul_add, Matrix.mul_smul] <;> rfl
      have hgd : ∀ s : ℂ, ‖s‖ < 2 → DifferentiableAt ℂ g s := by
        intro s hs
        have hw : DifferentiableAt ℂ (fun y : ℂ => A + y • B) s :=
          (differentiableAt_const A).add (differentiableAt_id.smul_const B)
        have hψ := (hdiff.differentiableAt (hU0o.mem_nhds (key s hs))).comp s hw
        exact ((line_int_differentiableAt T μ hU0o hΩ A B (Y * A) (Y * B) (key s hs)).const_smul
          ((Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ))).add (hψ.mul_const (T.dτ Y))
      have hgr : ∀ t : ℝ, |t| < 2 → g t = 0 := by
        intro t ht
        have hs : ‖(t : ℂ)‖ < 2 := by rwa [Complex.norm_real, Real.norm_eq_abs]
        rw [hgeq _ (key _ hs), (psM_inf_right T μ hμ (hposR t ht) hY).2]
        simp
      have h0 := IdB.line_zero g hgd hgr
      rw [hgeq _ (key _ hI), hAB] at h0
      exact eq_neg_of_add_eq_zero_left h0

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.LocalB
noncomputable section

open Matrix Filter Topology Set

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {ε : Fin n → Bool} {Λ : Fin n → ℝ}

section PathL
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

lemma lcB_path (z Y : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun s : ℝ => z * NormedSpace.exp ((s : ℂ) • Y)) (z * Y) 0 := by
  have h1 := hasDerivAt_exp_smul_const Y ((0 : ℝ) : ℂ)
  have hof : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 (0 : ℝ) := Complex.ofRealCLM.hasDerivAt
  have h2 := HasDerivAt.scomp (h := fun y : ℝ => (y : ℂ)) (0 : ℝ) h1 hof
  have h3 := h2.const_mul z
  exact h3.congr_deriv (by simp)

end PathL

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

lemma lcB_hasDerivAt (T : KType ε Λ) (μ : Fin n → ℤ) {U : Set (Matrix (Fin n) (Fin n) ℂ)} (hUo : IsOpen U)
    (hdiff : DifferentiableOn ℂ (psM T μ) U) {Y : Matrix (Fin n) (Fin n) ℂ}
    (hid : ∀ z ∈ U, fderiv ℂ (psM T μ) z (z * Y) = -(T.dτ Y * psM T μ z))
    (hY : inK ε Y) (γ : ℝ → KG ε)
    (hγ : ∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • Y)) (hmul : ∀ s t, γ (s + t) = γ s * γ t)
    (A : Matrix (Fin n) (Fin n) ℂ) {t : ℝ} (ht : A * NormedSpace.exp ((t : ℂ) • Y) ∈ U) :
    HasDerivAt (fun s : ℝ => T.op (γ s) * psM T μ (A * NormedSpace.exp ((s : ℂ) • Y))) 0 t := by
  set z := A * NormedSpace.exp ((t : ℂ) • Y) with hz
  have hcomm : ∀ s : ℝ, A * NormedSpace.exp ((s : ℂ) • Y) =
      z * NormedSpace.exp (((s - t : ℝ) : ℂ) • Y) := by
    intro s
    rw [hz, mul_assoc, ← Matrix.exp_add_of_commute _ _
      (((Commute.refl Y).smul_left _).smul_right _), ← add_smul]
    rw [show ((t : ℂ) + ((s - t : ℝ) : ℂ)) = (s : ℂ) by push_cast; ring]
  have h1 := lcB_path z Y
  have h2 := hasDerivAt_iff_tendsto_slope.1 h1
  have h3 : HasDerivAt (fun s : ℝ => z * NormedSpace.exp ((s : ℂ) • Y)) (z * Y) 0 :=
    hasDerivAt_iff_tendsto_slope.2 h2
  have h4 := HasDerivAt.comp_sub_const t t (by rw [sub_self]; exact h3)
  have hp : HasDerivAt (fun s : ℝ => A * NormedSpace.exp ((s : ℂ) • Y)) (z * Y) t := by
    rw [show (fun s : ℝ => A * NormedSpace.exp ((s : ℂ) • Y)) =
      fun s => z * NormedSpace.exp (((s - t : ℝ) : ℂ) • Y) from funext hcomm]
    exact h4
  have hF : HasFDerivAt (psM T μ) (fderiv ℂ (psM T μ) z) z :=
    (hdiff.differentiableAt (hUo.mem_nhds ht)).hasFDerivAt
  have hF' : HasFDerivAt (psM T μ) ((fderiv ℂ (psM T μ) z).restrictScalars ℝ) z :=
    hF.restrictScalars ℝ
  have hq0 := hF'.comp_hasDerivAt t hp
  have e : ((fderiv ℂ (psM T μ) z).restrictScalars ℝ) (z * Y) = -(T.dτ Y * psM T μ z) := hid z ht
  have hq : HasDerivAt (fun s : ℝ => psM T μ (A * NormedSpace.exp ((s : ℂ) • Y)))
      (-(T.dτ Y * psM T μ z)) t := hq0.congr_deriv e
  have ho1 : HasDerivAt (fun s : ℝ => T.op (γ s)) (T.op (γ t) * T.dτ Y) t := by
    have h5 := (T.hasDeriv Y hY γ hγ).const_mul (T.op (γ t))
    have h6 := HasDerivAt.comp_sub_const t t (by rw [sub_self]; exact h5)
    have he : (fun s : ℝ => T.op (γ s)) =
        fun s => T.op (γ t) * ((T.τ (γ (s - t)) : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V) := by
      funext s
      have hs := hmul t (s - t)
      rw [show t + (s - t) = s by ring] at hs
      simp only [KType.op]
      rw [hs, map_mul]
      rfl
    rw [he]
    exact h6
  have hprod := ho1.mul hq
  have hzero : T.op (γ t) * T.dτ Y * psM T μ (A * NormedSpace.exp ((t : ℂ) • Y)) +
      T.op (γ t) * -(T.dτ Y * psM T μ z) = 0 := by
    rw [mul_neg, mul_assoc]
    exact add_neg_cancel _
  exact hzero ▸ hprod

theorem lcB_const (T : KType ε Λ) (μ : Fin n → ℤ) {U : Set (Matrix (Fin n) (Fin n) ℂ)} (hUo : IsOpen U)
    (hdiff : DifferentiableOn ℂ (psM T μ) U) {Y : Matrix (Fin n) (Fin n) ℂ}
    (hid : ∀ z ∈ U, fderiv ℂ (psM T μ) z (z * Y) = -(T.dτ Y * psM T μ z))
    (hY : inK ε Y) (γ : ℝ → KG ε)
    (hγ : ∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • Y)) (hmul : ∀ s t, γ (s + t) = γ s * γ t)
    (A : Matrix (Fin n) (Fin n) ℂ) (hpath : ∀ t ∈ Icc (0 : ℝ) 1, A * NormedSpace.exp ((t : ℂ) • Y) ∈ U) :
    T.op (γ 1) * psM T μ (A * NormedSpace.exp Y) = psM T μ A := by
  have h0 : γ 0 = 1 := by simpa using hmul 0 0
  let g : ℝ → T.V →L[ℂ] T.V := fun t => T.op (γ t) * psM T μ (A * NormedSpace.exp ((t : ℂ) • Y))
  have hd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt g 0 t := fun t ht =>
    lcB_hasDerivAt T μ hUo hdiff hid hY γ hγ hmul A (hpath t ht)
  have hcont : ContinuousOn g (Icc 0 1) := fun t ht => (hd t ht).continuousAt.continuousWithinAt
  have hc := constant_of_has_deriv_right_zero hcont
    (fun t ht => (hd t (Ico_subset_Icc_self ht)).hasDerivWithinAt) 1 ⟨zero_le_one, le_rfl⟩
  simpa [g, h0, KType.op] using hc

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

noncomputable section

open Finset MeasureTheory Matrix Filter Topology Set
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

variable {ε : Fin n → Bool} {lam : Fin n → ℝ}

theorem psiM_local (T : KType ε (lowK ε lam)) (μ : Fin n → ℤ) (hμ : IsMu lam μ) (V : Set (Matrix (Fin n) (Fin n) ℂ))
    (hV : IsOpen V) (hpos : posSet n ⊆ V) {g₀ : Matrix (Fin n) (Fin n) ℂ} (hg₀ : inUJ ε g₀) :
    ∃ (W : Set (Matrix (Fin n) (Fin n) ℂ)) (k₀ : KG ε), IsOpen W ∧ g₀ ∈ W ∧
      (∀ g ∈ W, IsUnit g ∧ g⁻¹ * toMK k₀ ∈ V) ∧
      ∀ g ∈ W, inUJ ε g → PsiM T μ g = T.op k₀ * psM T μ (g⁻¹ * toMK k₀) := by
  classical
  have hexp : Continuous (fun X : Matrix (Fin n) (Fin n) ℂ => NormedSpace.exp X) := by
    letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
    first
      | (letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
         exact NormedSpace.exp_continuous)
      | (letI : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
         exact NormedSpace.exp_continuous)
      | (letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
         letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) :=
           { toAlgebra := by infer_instance
             norm_smul_le := fun q A => by
               rw [← Rat.cast_smul_eq_qsmul ℂ q A]
               refine (norm_smul_le _ _).trans (le_of_eq ?_)
               congr 1
               simp
               first
                 | rw [← Rat.norm_cast_real, Real.norm_eq_abs]
                 | rfl }
         first
           | exact @NormedSpace.exp_continuous _ _ _ (FiniteDimensional.complete ℂ _)
           | exact @NormedSpace.exp_continuous _ _ _ _ (FiniteDimensional.complete ℂ _))
  have hnegP : ∀ X : Matrix (Fin n) (Fin n) ℂ, inP ε X → inP ε (-X) := by
    intro X hX
    obtain ⟨h1, h2⟩ := hX
    have h1' : Xᴴ * Jm ε + Jm ε * X = 0 := h1
    show (-X)ᴴ * Jm ε + Jm ε * (-X) = 0 ∧ (-X) * Jm ε = -(Jm ε * -X)
    refine ⟨?_, ?_⟩
    · rw [Matrix.conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, ← neg_add, h1', neg_zero]
    · rw [Matrix.neg_mul, Matrix.mul_neg, h2]
  have hKun : ∀ A : Matrix (Fin n) (Fin n) ℂ, A ∈ Kset ε → Aᴴ * A = 1 ∧ A * Aᴴ = 1 := by
    intro A hA
    have hA' : A ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ A * Jm ε = Jm ε * A := hA
    refine ⟨?_, ?_⟩
    · rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff'.1 hA'.1
    · rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff.1 hA'.1
  have hKmul : ∀ A B : Matrix (Fin n) (Fin n) ℂ, A ∈ Kset ε → B ∈ Kset ε → Aᴴ * B ∈ Kset ε := by
    intro A B hA hB
    have hA' : A ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ A * Jm ε = Jm ε * A := hA
    have hB' : B ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ B * Jm ε = Jm ε * B := hB
    obtain ⟨hA1, hA2⟩ := hKun A hA
    obtain ⟨_, hB2⟩ := hKun B hB
    have hAJ : Aᴴ * Jm ε = Jm ε * Aᴴ := by
      calc Aᴴ * Jm ε = Aᴴ * Jm ε * (A * Aᴴ) := by rw [hA2, Matrix.mul_one]
        _ = Aᴴ * (Jm ε * A) * Aᴴ := by simp only [Matrix.mul_assoc]
        _ = Aᴴ * (A * Jm ε) * Aᴴ := by rw [hA'.2]
        _ = Jm ε * Aᴴ := by rw [← Matrix.mul_assoc, hA1, Matrix.one_mul]
    show Aᴴ * B ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ Aᴴ * B * Jm ε = Jm ε * (Aᴴ * B)
    refine ⟨?_, ?_⟩
    · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, ← Matrix.mul_assoc B, hB2,
        Matrix.one_mul, hA1]
    · rw [Matrix.mul_assoc, hB'.2, ← Matrix.mul_assoc, hAJ, Matrix.mul_assoc]
  obtain ⟨K, hK⟩ : ∃ K : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ,
      ∀ g, K g = g * NormedSpace.exp (-PolarDecomposition.polar_L g) :=
    ⟨fun g => g * NormedSpace.exp (-PolarDecomposition.polar_L g), fun _ => rfl⟩
  have hkmem : ∀ g, inUJ ε g → K g ∈ Kset ε := by
    intro g hg
    rw [hK]
    exact PolarDecomposition.polar_k_mem hg
  have hinv : ∀ g, inUJ ε g →
      g * (NormedSpace.exp (-PolarDecomposition.polar_L g) * (K g)ᴴ) = 1 := by
    intro g hg
    rw [← Matrix.mul_assoc, ← hK]
    exact (hKun _ (hkmem g hg)).2
  obtain ⟨U, hUo, hPU, hdiff, hU⟩ := psM_inf_nhd T μ hμ
  obtain ⟨ℓ, hℓ0, hℓev⟩ := lcA_exists_klog ε
  obtain ⟨k₀, hk₀⟩ := exists_toMK (hkmem g₀ hg₀)
  have hLt := (lcA_polarL_continuousOn ε g₀ hg₀).tendsto
  have hEt : Tendsto (fun g => NormedSpace.exp (-PolarDecomposition.polar_L g)) (𝓝[{g | inUJ ε g}] g₀)
      (𝓝 (NormedSpace.exp (-PolarDecomposition.polar_L g₀))) :=
    (hexp.tendsto _).comp hLt.neg
  have hKt : Tendsto K (𝓝[{g | inUJ ε g}] g₀) (𝓝 (K g₀)) := by
    have h : Tendsto (fun g => g * NormedSpace.exp (-PolarDecomposition.polar_L g)) (𝓝[{g | inUJ ε g}] g₀)
        (𝓝 (g₀ * NormedSpace.exp (-PolarDecomposition.polar_L g₀))) :=
      (tendsto_id.mono_left nhdsWithin_le_nhds).mul hEt
    have hKfun : K = fun g => g * NormedSpace.exp (-PolarDecomposition.polar_L g) := funext hK
    rw [hKfun]
    exact h
  have hFt : Tendsto (fun g => (K g)ᴴ * K g₀) (𝓝[{g | inUJ ε g}] g₀) (𝓝 1) := by
    have h : Tendsto (fun g => (K g)ᴴ * K g₀) (𝓝[{g | inUJ ε g}] g₀) (𝓝 ((K g₀)ᴴ * K g₀)) :=
      hKt.star.mul tendsto_const_nhds
    rwa [(hKun _ (hkmem g₀ hg₀)).1] at h
  have hℓt : Tendsto (fun g => ℓ ((K g)ᴴ * K g₀)) (𝓝[{g | inUJ ε g}] g₀) (𝓝 0) := hℓ0.comp hFt
  have hev1 := hFt.eventually hℓev
  have hcpt : ∀ᶠ p : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ in
      𝓝 (NormedSpace.exp (-PolarDecomposition.polar_L g₀), (0 : Matrix (Fin n) (Fin n) ℂ)),
      ∀ t ∈ Icc (0 : ℝ) 1, p.1 * NormedSpace.exp ((t : ℂ) • p.2) ∈ U := by
    refine isCompact_Icc.eventually_forall_of_forall_eventually ?_
    intro t _
    have hc : Continuous (fun z : (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ) × ℝ =>
        z.1.1 * NormedSpace.exp ((z.2 : ℂ) • z.1.2)) :=
      continuous_fst.fst.matrix_mul
        (hexp.comp ((Complex.continuous_ofReal.comp continuous_snd).smul continuous_fst.snd))
    have hmem : NormedSpace.exp (-PolarDecomposition.polar_L g₀) *
        NormedSpace.exp ((t : ℂ) • (0 : Matrix (Fin n) (Fin n) ℂ)) ∈ U := by
      rw [smul_zero, NormedSpace.exp_zero, Matrix.mul_one]
      exact hPU (exp_noncompactPart_posDef (hnegP _ (PolarDecomposition.polar_L_inP hg₀)))
    exact hc.continuousAt.preimage_mem_nhds (hUo.mem_nhds hmem)
  have hPt : Tendsto (fun g => (NormedSpace.exp (-PolarDecomposition.polar_L g), ℓ ((K g)ᴴ * K g₀)))
      (𝓝[{g | inUJ ε g}] g₀)
      (𝓝 (NormedSpace.exp (-PolarDecomposition.polar_L g₀), (0 : Matrix (Fin n) (Fin n) ℂ))) := by
    first
      | exact hEt.prodMk_nhds hℓt
      | exact hEt.prod_mk_nhds hℓt
  have hev2 := hPt.eventually hcpt
  obtain ⟨O, hOo, hg₀O, hOsub⟩ := mem_nhdsWithin.1 (hev1.and hev2)
  have hdetO : IsOpen {g : Matrix (Fin n) (Fin n) ℂ | g.det ≠ 0} :=
    isOpen_ne_fun (continuous_id.matrix_det) continuous_const
  have hinvc : ContinuousOn (fun g : Matrix (Fin n) (Fin n) ℂ => g⁻¹ * toMK k₀)
      {g : Matrix (Fin n) (Fin n) ℂ | g.det ≠ 0} := by
    intro g hg
    have hg' : g.det ≠ 0 := hg
    have h1 : ContinuousAt Inv.inv g := by
      refine continuousAt_matrix_inv g ?_
      first
        | (rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ hg')
        | (simp only [show (Ring.inverse : ℂ → ℂ) = Inv.inv from funext Ring.inverse_eq_inv]
           exact continuousAt_inv₀ hg')
    exact (h1.mul continuousAt_const).continuousWithinAt
  have hO₂ : IsOpen ({g : Matrix (Fin n) (Fin n) ℂ | g.det ≠ 0} ∩
      (fun g : Matrix (Fin n) (Fin n) ℂ => g⁻¹ * toMK k₀) ⁻¹' V) :=
    hinvc.isOpen_inter_preimage hdetO hV
  have hinv0 := hinv g₀ hg₀
  have hdet0 : g₀.det ≠ 0 := (Matrix.isUnit_det_of_right_inverse hinv0).ne_zero
  have hV0 : g₀⁻¹ * toMK k₀ ∈ V := by
    rw [Matrix.inv_eq_right_inv hinv0, hk₀, Matrix.mul_assoc, (hKun _ (hkmem g₀ hg₀)).1,
      Matrix.mul_one]
    exact hpos (exp_noncompactPart_posDef (hnegP _ (PolarDecomposition.polar_L_inP hg₀)))
  refine ⟨O ∩ ({g : Matrix (Fin n) (Fin n) ℂ | g.det ≠ 0} ∩
      (fun g : Matrix (Fin n) (Fin n) ℂ => g⁻¹ * toMK k₀) ⁻¹' V), k₀, hOo.inter hO₂,
      ⟨hg₀O, hdet0, hV0⟩, ?_, ?_⟩
  · intro g hg
    have hgd : g.det ≠ 0 := hg.2.1
    exact ⟨(Matrix.isUnit_iff_isUnit_det g).2 (isUnit_iff_ne_zero.2 hgd), hg.2.2⟩
  · intro g hg hgS
    obtain ⟨hq1, hq2⟩ := hOsub ⟨hg.1, hgS⟩
    obtain ⟨hY, hYe⟩ := hq1 (hKmul _ _ (hkmem g hgS) (hkmem g₀ hg₀))
    obtain ⟨γ, -, hγ, hmul⟩ := exists_oneParam ε hY
    have hid : ∀ z ∈ U, fderiv ℂ (psM T μ) z (z * ℓ ((K g)ᴴ * K g₀)) =
        -(T.dτ (ℓ ((K g)ᴴ * K g₀)) * psM T μ z) :=
      fun z hz => (hU z hz _ ((inK_iff ε _).1 hY).2).1
    have hc := lcB_const T μ hUo hdiff hid hY γ hγ hmul
      (NormedSpace.exp (-PolarDecomposition.polar_L g)) hq2
    have hγ1 : toMK (γ 1) = (K g)ᴴ * K g₀ := by
      rw [hγ 1, Complex.ofReal_one, one_smul]
      exact hYe
    have hkA : toMK (k₀ * (γ 1)⁻¹) = K g := by
      rw [toMK_mul', toMK_inv, hγ1, hk₀, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, ← Matrix.mul_assoc, (hKun _ (hkmem g₀ hg₀)).2,
        Matrix.one_mul]
    have hg_eq : g = toMK (k₀ * (γ 1)⁻¹) * NormedSpace.exp (PolarDecomposition.polar_L g) := by
      rw [hkA, hK]
      exact PolarDecomposition.eq_mul_exp_neg_polar_L_mul_exp_polar_L
    have hgi : g⁻¹ * toMK k₀ =
        NormedSpace.exp (-PolarDecomposition.polar_L g) * NormedSpace.exp (ℓ ((K g)ᴴ * K g₀)) := by
      rw [Matrix.inv_eq_right_inv (hinv g hgS), hk₀, hYe, Matrix.mul_assoc]
    have hPsi : PsiM T μ g =
        T.op (k₀ * (γ 1)⁻¹) * psM T μ (NormedSpace.exp (PolarDecomposition.polar_L g)) := by
      rw [← psiM_kexp T μ _ (PolarDecomposition.polar_L_inP hgS), ← hg_eq]
    rw [hPsi, hgi, ← psM_exp_neg T μ (PolarDecomposition.polar_L_inP hgS), ← hc, ← mul_assoc,
      ← op_mul' T, inv_mul_cancel_right]

end ReciprocityTheory.ChartRestriction.DS.S7
