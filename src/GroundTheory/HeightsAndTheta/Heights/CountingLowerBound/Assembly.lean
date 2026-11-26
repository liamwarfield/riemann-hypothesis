module

public import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.PInteriorDichotomy

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.PTailBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBound

open Real MeasureTheory

universe u

theorem TailBound.proof (h1 : MeanCountBound.Statement.{u}) :
    TailBound.Statement.{u} := by
  intro X _ μ lam cnt a ka r hH x hx
  have hprob := hH.isProbability
  set t := exp (-x) * r with ht_def
  have ht_pos : 0 < t := mul_pos (exp_pos _) hH.r_pos
  have ht_le : t ≤ r := by
    have : exp (-x) ≤ 1 := exp_le_one_iff.mpr (by linarith)
    nlinarith [hH.r_pos]
  have hS : MeasurableSet {z | lam z < t} := measurableSet_lt hH.lam_meas measurable_const

  have hmarkov : μ.real {z | lam z < t} ≤ meanCount μ cnt t := by
    rw [← integral_indicator_one hS, meanCount]
    refine integral_mono ((integrable_const (1 : ℝ)).indicator hS) (hH.integrable t ht_pos) ?_
    intro z
    by_cases hz : z ∈ {z | lam z < t}
    · rw [Set.indicator_of_mem hz]
      exact hH.one t ht_pos ht_le z hz
    · rw [Set.indicator_of_notMem hz]
      exact hH.cnt_nonneg t z

  have hscale : meanCount μ cnt t = exp (-x) ^ ka * meanCount μ cnt r :=
    hH.scaling (exp (-x)) r (exp_pos _) hH.r_pos
  have hpow : exp (-x) ^ ka = exp (-(ka * x)) := by
    rw [← exp_mul]; ring_nf
  have hmean := h1 X μ lam cnt a ka r hH
  have hbound : μ.real {z | lam z < t} ≤ 2 * 36 ^ a * exp (-(ka * x)) := by
    calc μ.real {z | lam z < t} ≤ meanCount μ cnt t := hmarkov
      _ = exp (-(ka * x)) * meanCount μ cnt r := by rw [hscale, hpow]
      _ ≤ exp (-(ka * x)) * (2 * 36 ^ a) :=
          mul_le_mul_of_nonneg_left hmean (exp_pos _).le
      _ = 2 * 36 ^ a * exp (-(ka * x)) := by ring
  have hone : μ.real {z | lam z < t} ≤ 1 := measureReal_le_one
  exact le_min hone hbound

end GroundTheory.Heights₂.Heights.LowerBound
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.PShortVectorsOrthogonal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBound

open Real

noncomputable section

universe u

theorem ShortVectorsOrthogonal.rpow_neg_half_mul_self {vr : ℝ} (hvr : 0 < vr) :
    vr ^ (-(1 / 2 : ℝ)) * vr ^ (-(1 / 2 : ℝ)) = vr⁻¹ := by
  rw [← Real.rpow_add hvr]
  norm_num [Real.rpow_neg_one]

end

end GroundTheory.Heights₂.Heights.LowerBound
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.PMeanCuspWeight
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBound

open Real MeasureTheory Filter Topology

noncomputable section

theorem max_zero_add_le_of_nonneg {a b : ℝ} (hb : 0 ≤ b) : max 0 (a + b) ≤ max 0 a + b :=
  max_le (add_nonneg (le_max_left 0 a) hb) (by linarith [le_max_right 0 a])

theorem MeanCuspWeight.proof : MeanCuspWeight.Statement := by
  intro X _ μ U lam f j' vr rd h
  have := h.isProbability
  have hf : (1 : ℝ) ≤ f := by exact_mod_cast h.one_le_f
  have hj : (1 : ℝ) ≤ j' := by exact_mod_cast h.one_le_j'
  have hfj : 0 ≤ (f : ℝ) * j' := by positivity
  have hvr0 : 0 < vr := lt_of_lt_of_le one_pos h.one_le_vr
  have hlogvr : 0 ≤ log vr := Real.log_nonneg h.one_le_vr
  have hr0 : 0 < vr ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hvr0 _
  have hlogr : log (vr ^ (-(1 / 2 : ℝ))) = -(1 / 2) * log vr := Real.log_rpow hvr0 _

  have key : ∀ z, max 0 (log (1 / lam z)) ≤
      max 0 (log (vr ^ (-(1 / 2 : ℝ)) / lam z)) + 1 / 2 * log vr := by
    intro z
    have hl := h.lam_pos z
    have e : log (1 / lam z) = log (vr ^ (-(1 / 2 : ℝ)) / lam z) + 1 / 2 * log vr := by
      rw [Real.log_div one_ne_zero hl.ne', Real.log_div hr0.ne' hl.ne', hlogr, Real.log_one]
      ring
    rw [e]
    exact max_zero_add_le_of_nonneg (by positivity)
  set L : ℝ := log (2 * f * j' * rd) with hL
  set g : X → ℝ := fun z =>
    (f : ℝ) * j' * (2 * (max 0 (log (vr ^ (-(1 / 2 : ℝ)) / lam z)) + 1 / 2 * log vr) + L) with hg
  have hUg : ∀ z, U z ≤ g z := by
    intro z
    refine (h.U_le z).trans (mul_le_mul_of_nonneg_left ?_ hfj)
    linarith [key z]
  have hint_h := h.logPlus_integrable
  have hint : Integrable g μ :=
    (((hint_h.add (integrable_const (1 / 2 * log vr))).const_mul 2).add
      (integrable_const L)).const_mul _
  have hmono : ∫ z, U z ∂μ ≤ ∫ z, g z ∂μ :=
    integral_mono_of_nonneg (ae_of_all _ h.U_nonneg) hint (ae_of_all _ hUg)
  have hval : ∫ z, g z ∂μ = (f : ℝ) * j' *
      (2 * ((∫ z, max 0 (log (vr ^ (-(1 / 2 : ℝ)) / lam z)) ∂μ) + 1 / 2 * log vr) + L) := by
    have h1 : Integrable (fun z => max 0 (log (vr ^ (-(1 / 2 : ℝ)) / lam z)) + 1 / 2 * log vr) μ :=
      hint_h.add (integrable_const _)
    have h2 : Integrable
        (fun z => 2 * (max 0 (log (vr ^ (-(1 / 2 : ℝ)) / lam z)) + 1 / 2 * log vr)) μ :=
      h1.const_mul 2
    rw [hg, integral_const_mul, integral_add h2 (integrable_const L), integral_const_mul,
      integral_add hint_h (integrable_const _), integral_const, integral_const, probReal_univ,
      one_smul, one_smul]
  rw [hval] at hmono
  refine hmono.trans (mul_le_mul_of_nonneg_left ?_ hfj)
  linarith [h.logPlus_mean]

end

end GroundTheory.Heights₂.Heights.LowerBound
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.PPackingCount
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBound

open MeasureTheory Metric

noncomputable section

theorem PackingCount.card_mul_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (T : Finset E) {lam R : ℝ} (hlam : 0 < lam) (hR : 0 ≤ R)
    (hT : ∀ x ∈ T, ‖x‖ < R) (hsep : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → lam ≤ ‖x - y‖) :
    (T.card : ℝ) * (lam / 2) ^ Module.finrank ℝ E ≤ (R + lam / 2) ^ Module.finrank ℝ E := by
  let _ : MeasurableSpace E := borel E
  have _ : BorelSpace E := ⟨rfl⟩
  set μ : Measure E := Measure.addHaar
  set d := Module.finrank ℝ E
  have hd : Set.PairwiseDisjoint (↑T : Set E) (fun x => ball x (lam / 2)) := by
    intro x hx y hy hxy
    apply Metric.ball_disjoint_ball
    rw [dist_eq_norm]
    have := hsep x hx y hy hxy
    linarith
  have hsub : (⋃ x ∈ T, ball x (lam / 2)) ⊆ ball (0 : E) (R + lam / 2) := by
    intro z hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨x, hx, hz⟩ := hz
    rw [mem_ball] at hz ⊢
    have h1 : dist x 0 < R := by rw [dist_zero_right]; exact hT x hx
    have h2 := dist_triangle z x 0
    linarith
  have h2 := measure_mono (μ := μ) hsub
  rw [measure_biUnion_finset hd (fun x _ => measurableSet_ball)] at h2
  rw [Finset.sum_congr rfl (fun x _ => Measure.addHaar_ball_of_pos μ x (half_pos hlam))] at h2
  rw [Finset.sum_const, nsmul_eq_mul, Measure.addHaar_ball_of_pos μ (0 : E) (r := R + lam / 2) (by positivity),
    ← mul_assoc] at h2
  have hc0 : μ (ball 0 1) ≠ 0 := (measure_ball_pos μ (0 : E) one_pos).ne'
  have hc1 : μ (ball 0 1) ≠ ⊤ := measure_ball_lt_top.ne
  rw [ENNReal.mul_le_mul_iff_left hc0 hc1, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul
    (Nat.cast_nonneg _), ENNReal.ofReal_le_ofReal_iff (by positivity)] at h2
  exact h2

theorem PackingCount.proof : PackingCount.Statement := by
  intro V _ _ L W lam r a h
  classical
  have : FiniteDimensional ℝ W :=
    Module.finite_of_finrank_pos (by rw [h.finrank_eq]; exact h.one_le_a)
  have hlam := h.lam_pos
  have hr : 0 < r := lt_of_lt_of_le hlam h.lam_le_r
  set B : ℝ := (1 + 2 * r / lam) ^ a with hB
  set S : Set V := {v | v ∈ L ∧ ‖v‖ < r} with hS

  have key : ∀ T : Finset V, ↑T ⊆ S → (T.card : ℝ) ≤ B := by
    intro T hT
    have hW : ∀ v ∈ T, v ∈ W := fun v hv => h.short_mem v (hT hv).1 (hT hv).2
    set T' : Finset W := T.subtype (· ∈ W)
    have hcard : T'.card = T.card := by
      rw [Finset.card_subtype, Finset.filter_true_of_mem hW]
    have hbd := PackingCount.card_mul_le T' hlam hr.le
      (fun x hx => by
        rw [Finset.mem_subtype] at hx
        rw [Submodule.coe_norm]
        exact (hT hx).2)
      (fun x hx y hy hxy => by
        rw [Finset.mem_subtype] at hx hy
        rw [Submodule.coe_norm, Submodule.coe_sub]
        apply h.lam_le_norm _ (h.sub_mem _ (hT hx).1 _ (hT hy).1)
        intro h0
        exact hxy (Subtype.ext (sub_eq_zero.mp h0)))
    rw [hcard, h.finrank_eq] at hbd
    have hpos : 0 < (lam / 2) ^ a := by positivity
    rw [← le_div_iff₀ hpos, ← div_pow] at hbd
    have he : (r + lam / 2) / (lam / 2) = 1 + 2 * r / lam := by
      field_simp
      ring
    rwa [he] at hbd
  have hfin : S.Finite := by
    by_contra hinf
    obtain ⟨T, hT, hTc⟩ := (Set.not_finite.mp hinf).exists_subset_card_eq (⌈B⌉₊ + 1)
    have := key T hT
    rw [hTc] at this
    push_cast at this
    linarith [Nat.le_ceil B]
  have hsub : {v | v ∈ L ∧ v ≠ 0 ∧ ‖v‖ < r} ⊆ S := fun v hv => ⟨hv.1, hv.2.2⟩
  have hSB : (S.ncard : ℝ) ≤ B := by
    rw [Set.ncard_eq_toFinset_card S hfin]
    exact key _ (by simp)
  have hB3 : B ≤ (3 * r / lam) ^ a := by
    apply pow_le_pow_left₀ (by positivity)
    have : lam ≤ r := h.lam_le_r
    rw [show (1 : ℝ) + 2 * r / lam = (lam + 2 * r) / lam by field_simp]
    exact div_le_div_of_nonneg_right (by linarith) hlam.le
  refine ⟨hfin.subset hsub, ?_⟩
  calc (({v | v ∈ L ∧ v ≠ 0 ∧ ‖v‖ < r} : Set V).ncard : ℝ) ≤ S.ncard := by
        exact_mod_cast Set.ncard_le_ncard hsub hfin
    _ ≤ B := hSB
    _ ≤ (3 * r / lam) ^ a := hB3

end

end GroundTheory.Heights₂.Heights.LowerBound
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.PMeanLogPlus
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBound

open Real MeasureTheory Filter Topology Set

noncomputable section

universe u

theorem lt_max_zero_log_div_iff {t r l : ℝ} (ht : 0 < t) (hr : 0 < r) (hl : 0 < l) :
    t < max 0 (log (r / l)) ↔ l < exp (-t) * r := by
  rw [lt_max_iff, lt_log_iff_exp_lt (div_pos hr hl), lt_div_iff₀ hl, exp_neg,
    ← div_eq_inv_mul, lt_div_iff₀ (exp_pos t), mul_comm l]
  constructor
  · rintro (h | h)
    · exact absurd h (not_lt.2 ht.le)
    · exact h
  · exact Or.inr

theorem log_two_mul_pow_div_add_le {a : ℕ} {k : ℝ} (ha : 1 ≤ a) (hk : 3 * (a : ℝ) ≤ k) :
    log (2 * 36 ^ a) / k + 1 / k ≤ 3 := by
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hk0 : 0 < k := by linarith
  have h2 : log 2 < 1 := by have := log_two_lt_d9; norm_num at this; linarith
  have h36 : log 36 < 4 := by
    rw [log_lt_iff_lt_exp (by norm_num)]
    have he : exp 4 = exp 1 ^ 4 := by rw [← exp_nat_mul]; norm_num
    have h := pow_lt_pow_left₀ exp_one_gt_d9 (by norm_num) (by norm_num : (4 : ℕ) ≠ 0)
    rw [he]; norm_num at h ⊢; linarith
  have hlog : log (2 * 36 ^ a) = log 2 + a * log 36 := by
    rw [log_mul (by norm_num) (by positivity), log_pow]
  rw [← add_div, div_le_iff₀ hk0, hlog]
  nlinarith

theorem MeanLogPlus.proof (h1 : TailBound.Statement.{u}) : MeanLogPlus.Statement.{u} := by
  intro X _ μ lam cnt a ka r h
  have := h.isProbability
  have hk0 : 0 < ka := by
    have : (1 : ℝ) ≤ a := by exact_mod_cast h.one_le_a
    linarith [h.three_a_le_ka]
  set F : X → ℝ := fun z => max 0 (log (r / lam z)) with hF
  have hFm : Measurable F :=
    measurable_const.max (measurable_log.comp (measurable_const.div h.lam_meas))
  have hF0 : ∀ z, 0 ≤ F z := fun z => le_max_left _ _
  set C : ℝ := 2 * 36 ^ a with hC
  have hC1 : 1 ≤ C := by rw [hC]; have : (1 : ℝ) ≤ 36 ^ a := one_le_pow₀ (by norm_num); linarith
  set x0 : ℝ := log C / ka with hx0
  have hx00 : 0 ≤ x0 := div_nonneg (log_nonneg hC1) hk0.le
  set g : ℝ → ℝ := fun t => min 1 (C * exp (-ka * t)) with hg

  have hpt : ∀ t ∈ Ioi (0 : ℝ), μ {z | t < F z} ≤ ENNReal.ofReal (g t) := by
    intro t ht
    have hset : {z | t < F z} = {z | lam z < exp (-t) * r} := by
      ext z; exact lt_max_zero_log_div_iff ht h.r_pos (h.lam_pos z)
    rw [hset, ← ofReal_measureReal]
    apply ENNReal.ofReal_le_ofReal
    have := h1 X μ lam cnt a ka r h t (le_of_lt ht)
    simpa [hg, neg_mul] using this

  have hexp : IntegrableOn (fun t => C * exp (-ka * t)) (Ioi x0) :=
    (exp_neg_integrableOn_Ioi x0 hk0).const_mul C
  have hint : ∫ t in Ioi x0, C * exp (-ka * t) = 1 / ka := by
    rw [integral_const_mul, integral_exp_mul_Ioi (by linarith) x0]
    have : exp (-ka * x0) = C⁻¹ := by
      rw [hx0, show -ka * (log C / ka) = -log C by field_simp, exp_neg,
        exp_log (by linarith)]
    rw [this]; field_simp
  have hL : ∫⁻ z, ENNReal.ofReal (F z) ∂μ ≤ ENNReal.ofReal 3 := by
    rw [lintegral_eq_lintegral_meas_lt μ (ae_of_all _ hF0) hFm.aemeasurable]
    calc ∫⁻ t in Ioi 0, μ {z | t < F z}
        ≤ ∫⁻ t in Ioi 0, ENNReal.ofReal (g t) := setLIntegral_mono' measurableSet_Ioi hpt
      _ ≤ ∫⁻ t in Ioc 0 x0 ∪ Ioi x0, ENNReal.ofReal (g t) := by
          rw [Ioc_union_Ioi_eq_Ioi hx00]
      _ ≤ (∫⁻ t in Ioc 0 x0, ENNReal.ofReal (g t)) + ∫⁻ t in Ioi x0, ENNReal.ofReal (g t) :=
          lintegral_union_le _ _ _
      _ ≤ (∫⁻ t in Ioc 0 x0, 1) + ∫⁻ t in Ioi x0, ENNReal.ofReal (C * exp (-ka * t)) :=
          add_le_add (lintegral_mono fun t => ENNReal.ofReal_le_one.2 (min_le_left _ _))
            (lintegral_mono fun t => ENNReal.ofReal_le_ofReal (min_le_right _ _))
      _ = ENNReal.ofReal x0 + ENNReal.ofReal (1 / ka) := by
          rw [setLIntegral_const, one_mul, Real.volume_Ioc, sub_zero, ← hint,
            ofReal_integral_eq_lintegral_ofReal hexp
              (ae_of_all _ fun t => by positivity)]
      _ = ENNReal.ofReal (x0 + 1 / ka) := (ENNReal.ofReal_add hx00 (by positivity)).symm
      _ ≤ ENNReal.ofReal 3 :=
          ENNReal.ofReal_le_ofReal (log_two_mul_pow_div_add_le h.one_le_a h.three_a_le_ka)
  have hInt : Integrable F μ := by
    refine ⟨hFm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hF0)]
    exact lt_of_le_of_lt hL ENNReal.ofReal_lt_top
  refine ⟨hInt, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hF0) hFm.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal (by norm_num) hL

end

end GroundTheory.Heights₂.Heights.LowerBound
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBound

universe u

theorem PackingCount.full : PackingCount.Statement :=
  PackingCount.proof

theorem MeanCountBound.full : MeanCountBound.Statement.{u} :=
  MeanCountBound.proof

theorem TailBound.full : TailBound.Statement.{u} :=
  TailBound.proof MeanCountBound.full

theorem MeanLogPlus.full : MeanLogPlus.Statement.{u} :=
  MeanLogPlus.proof TailBound.full

theorem MeanCuspWeight.full : MeanCuspWeight.Statement :=
  MeanCuspWeight.proof

end GroundTheory.Heights₂.Heights.LowerBound
