module

public import Development.AutomorphicArithmetic.DedekindLFunctions.LandauZeroFreeCriterion

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.LandauFinite
open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Deduction

theorem landau_finite {Z : Set ℂ} (hiso : ∀ z : ℂ, 0 < z.re → ∀ᶠ w in 𝓝[≠] z, w ∉ Z) {z : ℂ} {r : ℝ}
    (hr : r < z.re) : (Z ∩ Metric.closedBall z r).Finite := by
  have hK : IsCompact (Metric.closedBall z r) := isCompact_closedBall z r
  have hpos : ∀ w ∈ Metric.closedBall z r, 0 < w.re := by
    intro w hw
    have h1 : ‖w - z‖ ≤ r := by simpa [dist_eq_norm] using hw
    have h2 : |(w - z).re| ≤ ‖w - z‖ := Complex.abs_re_le_norm _
    have h3 := (abs_le.mp (h2.trans h1)).1
    simp only [Complex.sub_re] at h3
    linarith
  obtain ⟨t, -, ht⟩ := hK.elim_nhds_subcover (fun w => {v | v ∈ ({w}ᶜ : Set ℂ) → v ∉ Z})
    (fun w hw => eventually_nhdsWithin_iff.mp (hiso w (hpos w hw)))
  refine t.finite_toSet.subset ?_
  rintro v ⟨hvZ, hvK⟩
  obtain ⟨w, hw, hvw⟩ := Set.mem_iUnion₂.mp (ht hvK)
  by_cases h : v = w
  · rw [h]; exact hw
  · exact absurd hvZ (hvw h)

end Deduction

end
end

section -- merged from Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.MellinRamp
open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Deduction

theorem mellin_ramp (n : ℕ) (hn : 1 ≤ n) (s : ℂ) (hs : 1 < s.re) :
    ∫ y in Ioi (1 : ℝ), ((max (y / n - 1) 0 : ℝ) : ℂ) * (y : ℂ) ^ (-s - 1) = (n : ℂ) ^ (-s) / (s * (s - 1)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs0 : s ≠ 0 := by
    intro h; rw [h] at hs; simp at hs; linarith
  have hs1 : s - 1 ≠ 0 := by
    intro h
    have : s = 1 := by linear_combination h
    rw [this] at hs; simp at hs
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (s := Ioi (n : ℝ)) measurableSet_Ioi
    (Ioi_subset_Ioi hn1)]
  swap
  · intro y hy
    have hy' : y ≤ n := by simpa using hy.2
    have : y / n - 1 ≤ 0 := by
      rw [sub_nonpos, div_le_one hn0]; exact hy'
    simp [max_eq_right this]
  have hpt : ∀ y ∈ Ioi (n : ℝ), ((max (y / n - 1) 0 : ℝ) : ℂ) * (y : ℂ) ^ (-s - 1)
      = (n : ℂ)⁻¹ * (y : ℂ) ^ (-s) - (y : ℂ) ^ (-s - 1) := by
    intro y hy
    have hy : (n : ℝ) < y := hy
    have hypos : (0 : ℝ) < y := lt_trans hn0 hy
    have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast hypos.ne'
    have hm : y / n - 1 ≥ 0 := by
      rw [ge_iff_le, sub_nonneg, le_div_iff₀ hn0]; linarith
    rw [max_eq_left hm, cpow_sub _ _ hyC, cpow_one]
    push_cast
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi hpt]
  have ha1 : (-s).re < -1 := by simp; linarith
  have ha2 : (-s - 1).re < -1 := by simp; linarith
  rw [integral_sub ((integrableOn_Ioi_cpow_of_lt ha1 hn0).const_mul _)
    (integrableOn_Ioi_cpow_of_lt ha2 hn0), integral_const_mul,
    integral_Ioi_cpow_of_lt ha1 hn0, integral_Ioi_cpow_of_lt ha2 hn0]
  have hcast : ((n : ℝ) : ℂ) = (n : ℂ) := by push_cast; rfl
  rw [hcast, cpow_add _ _ hnC, cpow_one, sub_add_cancel]
  have h1s : -s + 1 ≠ 0 := by
    intro h; apply hs1; linear_combination -h
  field_simp
  ring

end Deduction

end
end

section -- merged from Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.CharFamilyLFunctionNeZeroOfOneLeRe
open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Deduction

theorem charFamily_LFunction_ne_zero_of_one_le_re (F : CharFamily) (i : F.ι) (s : ℂ) (hs : 1 ≤ s.re) :
    DirichletCharacter.LFunction (F.χ i) s ≠ 0 := by
  haveI := F.nz i
  rcases F.adm i with h | h
  · have key : ∀ (M : ℕ) [NeZero M] (ψ : DirichletCharacter ℂ M), M = 1 →
        DirichletCharacter.LFunction ψ s ≠ 0 := by
      intro M _ ψ hM
      subst hM
      rw [DirichletCharacter.LFunction_modOne_eq]
      exact riemannZeta_ne_zero_of_one_le_re hs
    exact key _ (F.χ i) h
  · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re _ (Or.inl h) hs

end Deduction

end
end

section -- merged from Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.LandauCauchy
open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Deduction

theorem landau_cauchy {Φ : ℂ → ℂ} {z : ℂ} {r r' : ℝ} (hd : DifferentiableOn ℂ Φ (Metric.ball z r))
    (h0 : 0 < r') (h1 : r' < r) :
    ∃ M : ℝ, ∀ k : ℕ, ‖iteratedDeriv k Φ z / (k.factorial : ℂ)‖ ≤ M / r' ^ k := by
  set R : NNReal := ⟨r', h0.le⟩ with hRdef
  have hR : (R : ℝ) = r' := rfl
  refine ⟨(2 * Real.pi)⁻¹ * ∫ θ in (0:ℝ)..2 * Real.pi, ‖Φ (circleMap z r' θ)‖, fun k => ?_⟩
  have hsub : Metric.closedBall z (R : ℝ) ⊆ Metric.ball z r := by
    rw [hR]; exact Metric.closedBall_subset_ball h1
  have hRpos : (0 : NNReal) < R := by
    show (0 : ℝ) < (R : ℝ); rw [hR]; exact h0
  have hp := (hd.mono hsub).hasFPowerSeriesOnBall hRpos
  have key := hp.factorial_smul (1 : ℂ) k
  have hderiv : iteratedDeriv k Φ z / (k.factorial : ℂ) = cauchyPowerSeries Φ z (R : ℝ) k (fun _ => 1) := by
    rw [iteratedDeriv_eq_iteratedFDeriv, ← key, nsmul_eq_mul]
    have hk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    field_simp
  rw [hderiv]
  calc ‖cauchyPowerSeries Φ z (R : ℝ) k (fun _ => 1)‖
      ≤ ‖cauchyPowerSeries Φ z (R : ℝ) k‖ * ∏ _i : Fin k, ‖(1 : ℂ)‖ :=
        ContinuousMultilinearMap.le_opNorm _ _
    _ = ‖cauchyPowerSeries Φ z (R : ℝ) k‖ := by simp
    _ ≤ ((2 * Real.pi)⁻¹ * ∫ θ in (0:ℝ)..2 * Real.pi, ‖Φ (circleMap z (R : ℝ) θ)‖) * |(R : ℝ)|⁻¹ ^ k :=
        norm_cauchyPowerSeries_le _ _ _ _
    _ = _ := by
        rw [hR, abs_of_pos h0, inv_pow, div_eq_mul_inv]

end Deduction

end
end

section -- merged from Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.LFunctionConj
open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Deduction

namespace LFunctionConjugation

open HurwitzZeta

lemma ofReal_cpow_conj {x : ℝ} (hx : 0 ≤ x) (s : ℂ) :
    (x : ℂ) ^ ((starRingEnd ℂ) s) = (starRingEnd ℂ) ((x : ℂ) ^ s) := by
  have h := Complex.conj_cpow (x : ℂ) ((starRingEnd ℂ) s)
    (by rw [Complex.arg_ofReal_of_nonneg hx]; exact Real.pi_pos.ne)
  rwa [Complex.conj_ofReal, Complex.conj_conj] at h

lemma Gammaℝ_conj (s : ℂ) : Gammaℝ ((starRingEnd ℂ) s) = (starRingEnd ℂ) (Gammaℝ s) := by
  have h1 : -(starRingEnd ℂ) s / 2 = (starRingEnd ℂ) (-s / 2) := by
    rw [map_div₀, map_neg, map_ofNat]
  have h2 : (starRingEnd ℂ) s / 2 = (starRingEnd ℂ) (s / 2) := by
    rw [map_div₀, map_ofNat]
  rw [Gammaℝ, Gammaℝ, h1, h2, ofReal_cpow_conj Real.pi_pos.le, Complex.Gamma_conj, map_mul]

lemma hurwitz_conj_of_re {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) {s : ℂ} (hs : 1 < s.re) :
    hurwitzZeta a ((starRingEnd ℂ) s) = (starRingEnd ℂ) (hurwitzZeta a s) := by
  have hs' : 1 < ((starRingEnd ℂ) s).re := by rwa [Complex.conj_re]
  rw [← (hasSum_hurwitzZeta_of_one_lt_re ha hs').tsum_eq,
    ← (hasSum_hurwitzZeta_of_one_lt_re ha hs).tsum_eq, Complex.conj_tsum]
  refine tsum_congr fun n => ?_
  have hn : (0 : ℝ) ≤ (n : ℝ) + a := add_nonneg (Nat.cast_nonneg n) ha.1
  have hc : ((n : ℂ) + (a : ℂ)) = (((n : ℝ) + a : ℝ) : ℂ) := by push_cast; rfl
  rw [map_div₀, map_one, hc, ofReal_cpow_conj hn]

def reg (a : UnitAddCircle) (s : ℂ) : ℂ := hurwitzZeta a s - 1 / (s - 1) / Gammaℝ s

lemma differentiable_reg (a : UnitAddCircle) : Differentiable ℂ (reg a) := by
  intro s
  rcases eq_or_ne s 1 with rfl | hs
  · exact differentiableAt_hurwitzZeta_sub_one_div a
  · have e : reg a = fun z => hurwitzZeta a z - (z - 1)⁻¹ * (Gammaℝ z)⁻¹ := by
      funext z
      rw [reg, one_div, div_eq_mul_inv]
    rw [e]
    exact (differentiableAt_hurwitzZeta a hs).sub
      (((differentiableAt_id.sub_const (1 : ℂ)).inv (sub_ne_zero.mpr hs)).mul
        (differentiable_Gammaℝ_inv s))

lemma pole_conj (s : ℂ) : 1 / ((starRingEnd ℂ) s - 1) / Gammaℝ ((starRingEnd ℂ) s)
    = (starRingEnd ℂ) (1 / (s - 1) / Gammaℝ s) := by
  rw [Gammaℝ_conj]
  simp [map_div₀]

lemma hurwitz_conj_real {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (s : ℂ) :
    hurwitzZeta a ((starRingEnd ℂ) s) = (starRingEnd ℂ) (hurwitzZeta a s) := by
  have hreg : ∀ z : ℂ, 1 < z.re → (starRingEnd ℂ) (reg a ((starRingEnd ℂ) z)) = reg a z := by
    intro z hz
    have h1 := hurwitz_conj_of_re ha (s := (starRingEnd ℂ) z) (by rwa [Complex.conj_re])
    have h2 := pole_conj ((starRingEnd ℂ) z)
    rw [Complex.conj_conj] at h1 h2
    rw [reg, reg, map_sub, h1, h2]
  have hF : Differentiable ℂ (fun z => (starRingEnd ℂ) (reg a ((starRingEnd ℂ) z))) :=
    fun z => differentiableAt_conj_conj_iff.mpr (differentiable_reg a _)
  have heq : (fun z => (starRingEnd ℂ) (reg a ((starRingEnd ℂ) z))) = reg a :=
    AnalyticOnNhd.eq_of_eventuallyEq (z₀ := 2) (hF.differentiableOn.analyticOnNhd isOpen_univ)
      ((differentiable_reg a).differentiableOn.analyticOnNhd isOpen_univ)
      (eventuallyEq_of_mem ((isOpen_lt continuous_const continuous_re).mem_nhds (by norm_num)) hreg)
  have h3 : (starRingEnd ℂ) (reg a ((starRingEnd ℂ) ((starRingEnd ℂ) s))) = reg a ((starRingEnd ℂ) s) :=
    congrFun heq _
  rw [Complex.conj_conj] at h3
  have e : ∀ w, hurwitzZeta a w = reg a w + 1 / (w - 1) / Gammaℝ w := fun w => by
    rw [reg, sub_add_cancel]
  rw [e ((starRingEnd ℂ) s), e s, map_add (f := _), ← h3, pole_conj]

lemma hurwitz_conj (a : UnitAddCircle) (s : ℂ) :
    hurwitzZeta a ((starRingEnd ℂ) s) = (starRingEnd ℂ) (hurwitzZeta a s) := by
  induction a using QuotientAddGroup.induction_on with
  | H b =>
    have hb : ((b : ℝ) : UnitAddCircle) = ((Int.fract b : ℝ) : UnitAddCircle) := by
      rw [QuotientAddGroup.eq]
      exact ⟨-⌊b⌋, by simp only [Int.fract, zsmul_eq_mul, mul_one, Int.cast_neg]; ring⟩
    rw [hb]
    exact hurwitz_conj_real ⟨Int.fract_nonneg b, (Int.fract_lt_one b).le⟩ s

end LFunctionConjugation

theorem LFunction_conj {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ) :
    DirichletCharacter.LFunction χ⁻¹ ((starRingEnd ℂ) s) = (starRingEnd ℂ) (DirichletCharacter.LFunction χ s) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [DirichletCharacter.LFunction, ZMod.LFunction, map_mul, map_sum]
  congr 1
  · have h := LFunctionConjugation.ofReal_cpow_conj (Nat.cast_nonneg N : (0 : ℝ) ≤ N) (-s)
    simpa using h
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [LFunctionConjugation.hurwitz_conj, ← MulChar.star_apply']
    rfl

end Deduction

end
end
