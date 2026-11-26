module

public import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Statements

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.PInteriorDichotomy
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBound

open Real

theorem InteriorDichotomy.proof : InteriorDichotomy.Statement := by
  intro C0 C1 C2 hC0 hC1 hC2
  refine ⟨C0 * (log (3 + C2) + 2) + C1, ?_⟩
  intro h hmu g fj La H
  obtain ⟨hg, hfj, hgexp, hLa, hlow, hup⟩ := H
  have hLa0 : 0 < La := by linarith
  have hfj0 : 0 < fj := by linarith
  have hlog3 : 0 ≤ log (3 + C2) := Real.log_nonneg (by linarith)
  have hCnn : 0 ≤ C0 * (log (3 + C2) + 2) + C1 := by positivity
  by_cases hmu0 : 0 ≤ hmu
  · have : 0 ≤ (C0 * (log (3 + C2) + 2) + C1) * fj * La := by positivity
    linarith
  replace hmu0 : hmu < 0 := lt_of_not_ge hmu0

  have hgLa : 0 ≤ C2 * g * La := by positivity
  have hmax : max h 0 ≤ C2 * g * La := max_le (by linarith) hgLa
  have hpos : 0 < 2 + g + max h 0 := by have := le_max_right h 0; linarith
  have hgLa1 : 1 ≤ g * La := one_le_mul_of_one_le_of_one_le hg hLa
  have hstep1 : 2 + g + max h 0 ≤ (3 + C2) * (g * La) := by
    have : g ≤ g * La := le_mul_of_one_le_right (by linarith) hLa
    nlinarith
  have hLaexp : La ≤ exp La := by have := Real.add_one_le_exp La; linarith
  have hstep2 : g * La ≤ exp (2 * La) := by
    rw [show 2 * La = La + La by ring, Real.exp_add]
    exact mul_le_mul hgexp hLaexp hLa0.le (exp_pos La).le
  have hstep3 : 2 + g + max h 0 ≤ (3 + C2) * exp (2 * La) :=
    hstep1.trans (mul_le_mul_of_nonneg_left hstep2 (by linarith))
  have hlog : log (2 + g + max h 0) ≤ (log (3 + C2) + 2) * La := by
    calc log (2 + g + max h 0) ≤ log ((3 + C2) * exp (2 * La)) := Real.log_le_log hpos hstep3
      _ = log (3 + C2) + 2 * La := by
          rw [Real.log_mul (by linarith) (exp_pos _).ne', Real.log_exp]
      _ ≤ (log (3 + C2) + 2) * La := by nlinarith
  have hC0log : C0 * log (2 + g + max h 0) ≤ C0 * ((log (3 + C2) + 2) * La) :=
    mul_le_mul_of_nonneg_left hlog hC0
  have hin : C0 * log (2 + g + max h 0) + C1 * La ≤ (C0 * (log (3 + C2) + 2) + C1) * La := by
    nlinarith
  have := mul_le_mul_of_nonneg_left hin hfj0.le
  nlinarith

end GroundTheory.Heights₂.Heights.LowerBound
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.PCuspWeightBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBound

open Real

theorem CuspWeightBound.proof : CuspWeightBound.Statement := by
  intro f j' ρ rd lam NI covol h
  have hf : (1 : ℝ) ≤ f := by exact_mod_cast h.one_le_f
  have hj : (1 : ℝ) ≤ j' := by exact_mod_cast h.one_le_j'
  have hρ : (1 : ℝ) ≤ ρ := by exact_mod_cast h.one_le_ρ
  have hρj : (ρ : ℝ) ≤ j' := by exact_mod_cast h.ρ_le_j'
  have hrd := h.one_le_rd
  have hlam := h.lam_pos
  have hNI := h.NI_pos
  have h2fρ : (0 : ℝ) < 2 * f * ρ := by positivity
  have hsq : 0 < √(2 * f * ρ : ℝ) := Real.sqrt_pos.mpr h2fρ

  have hmk : (lam / √(2 * f * ρ : ℝ)) ^ (2 * f * ρ) ≤ NI * rd ^ (f * ρ) :=
    h.covol_eq ▸ h.minkowski
  have hrdp : (0 : ℝ) < rd ^ (f * ρ) := by positivity
  have hlog := Real.log_le_log (by positivity) hmk
  rw [Real.log_pow, Real.log_mul hNI.ne' hrdp.ne', Real.log_pow,
    Real.log_div hlam.ne' hsq.ne', Real.log_sqrt h2fρ.le] at hlog
  push_cast at hlog

  have hρbound : -log NI ≤ f * ρ * (2 * log (1 / lam) + log (2 * f * ρ * rd)) := by
    have hrd0 : rd ≠ 0 := by positivity
    rw [one_div, Real.log_inv, Real.log_mul h2fρ.ne' hrd0]
    nlinarith

  have hB : 0 ≤ 2 * max 0 (log (1 / lam)) + log (2 * f * j' * rd) := by
    have : 0 ≤ log (2 * f * j' * rd) := by
      have h1 : (1 : ℝ) ≤ f * j' := one_le_mul_of_one_le_of_one_le hf hj
      have h2 : (1 : ℝ) ≤ f * j' * rd := one_le_mul_of_one_le_of_one_le h1 hrd
      exact Real.log_nonneg (by linarith)
    have : 0 ≤ max 0 (log (1 / lam)) := le_max_left _ _
    linarith
  have hin : 2 * log (1 / lam) + log (2 * f * ρ * rd) ≤
      2 * max 0 (log (1 / lam)) + log (2 * f * j' * rd) := by
    have h1 : log (1 / lam) ≤ max 0 (log (1 / lam)) := le_max_right _ _
    have h2 : log (2 * f * ρ * rd) ≤ log (2 * f * j' * rd) :=
      Real.log_le_log (by positivity) (by gcongr)
    linarith
  calc -log NI ≤ f * ρ * (2 * log (1 / lam) + log (2 * f * ρ * rd)) := hρbound
    _ ≤ f * ρ * (2 * max 0 (log (1 / lam)) + log (2 * f * j' * rd)) := by
        gcongr
    _ ≤ f * j' * (2 * max 0 (log (1 / lam)) + log (2 * f * j' * rd)) := by
        gcongr

end GroundTheory.Heights₂.Heights.LowerBound
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.PMinkowskiCovolumeBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBound

open Real MeasureTheory Module

universe u

theorem MinkowskiCovolumeBound.proof : MinkowskiCovolumeBound.Statement.{u} := by
  intro V _ _ _ _ _ hm L _ _
  set m := finrank ℝ V with hm_def
  set lam := firstMinimum L with hlam
  set c := lam / √(m : ℝ) with hc

  have hlow : ∀ v ∈ L, v ≠ 0 → lam ≤ ‖v‖ := by
    intro v hv hv0
    exact csInf_le ⟨0, fun x ⟨_, _, _, hx⟩ => hx ▸ norm_nonneg _⟩ ⟨v, hv, hv0, rfl⟩
  have hlam0 : 0 ≤ lam := Real.sInf_nonneg (fun x ⟨_, _, _, hx⟩ => hx ▸ norm_nonneg _)
  have hcov : 0 ≤ ZLattice.covolume L := (ZLattice.covolume_pos L).le
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hc0' : 0 ≤ c := div_nonneg hlam0 (Real.sqrt_nonneg _)
  rcases hc0'.eq_or_lt with hc0 | hc0
  · rw [← hc0, zero_pow (by omega)]
    exact hcov
  by_contra hlt
  push Not at hlt

  let b := stdOrthonormalBasis ℝ V
  let f : V → (Fin m → ℝ) := fun x => WithLp.ofLp (b.repr x)
  have hf : MeasurePreserving f volume volume :=
    (PiLp.volume_preserving_ofLp (Fin m)).comp b.measurePreserving_repr
  let S : Set V := f ⁻¹' Metric.ball 0 c
  have hS_vol : volume S = ENNReal.ofReal ((2 * c) ^ m) := by
    rw [hf.measure_preimage measurableSet_ball.nullMeasurableSet, Real.volume_pi_ball _ hc0,
      Fintype.card_fin]
  have hS_symm : ∀ x ∈ S, -x ∈ S := by
    intro x hx
    simpa [S, f, Metric.mem_ball, dist_zero_right, norm_neg] using hx
  have hS_conv : Convex ℝ S := by
    have hlin : IsLinearMap ℝ f := by
      constructor
      · intro x y; simp [f]
      · intro a x; simp [f]
    exact (convex_ball (0 : Fin m → ℝ) c).is_linear_preimage hlin

  let bZ := Free.chooseBasis ℤ L
  have fund := ZLattice.isAddFundamentalDomain bZ (volume : Measure V)
  have hcovF := ZLattice.covolume_eq_measure_fundamentalDomain L volume fund
  have hF_fin : volume (ZSpan.fundamentalDomain (bZ.ofZLatticeBasis ℝ)) ≠ ⊤ :=
    (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne
  have hbig : volume (ZSpan.fundamentalDomain (bZ.ofZLatticeBasis ℝ)) * 2 ^ finrank ℝ V
      < volume S := by
    rw [hS_vol, ← ENNReal.ofReal_toReal hF_fin, ← ENNReal.ofReal_ofNat 2,
      ← ENNReal.ofReal_pow (by norm_num), ← ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ENNReal.ofReal_lt_ofReal_iff (pow_pos (by positivity) _), mul_pow, ← hm_def,
      mul_comm _ (2 ^ m)]
    have : (volume (ZSpan.fundamentalDomain (bZ.ofZLatticeBasis ℝ))).toReal
        = ZLattice.covolume L := by rw [hcovF]; rfl
    rw [this]
    exact mul_lt_mul_of_pos_left hlt (by positivity)
  have : Countable L.toAddSubgroup := (inferInstance : Countable L)
  obtain ⟨x, hx0, hxS⟩ :=
    exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure (L := L.toAddSubgroup) fund
      hS_symm hS_conv hbig

  have hxL : (x : V) ∈ L := x.2
  have hxne : (x : V) ≠ 0 := fun h => hx0 (Subtype.ext h)
  have hcoord : ∀ i, |b.repr (x : V) i| < c := by
    intro i
    have := hxS
    simp only [S, f, Set.mem_preimage, mem_ball_zero_iff] at this
    exact lt_of_le_of_lt (by simpa [Real.norm_eq_abs] using norm_le_pi_norm (WithLp.ofLp (b.repr (x : V))) i) this
  have hnormsq : ‖(x : V)‖ ^ 2 < lam ^ 2 := by
    rw [← b.repr.norm_map, EuclideanSpace.norm_sq_eq]
    calc ∑ i, ‖b.repr (x : V) i‖ ^ 2 < ∑ _i : Fin m, c ^ 2 := by
          apply Finset.sum_lt_sum_of_nonempty
          · exact Finset.univ_nonempty_iff.mpr ⟨⟨0, hm⟩⟩
          · intro i _
            rw [Real.norm_eq_abs]
            exact pow_lt_pow_left₀ (hcoord i) (abs_nonneg _) (by norm_num)
      _ = lam ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hc, div_pow,
            Real.sq_sqrt hm0.le]
          field_simp
  have := hlow _ hxL hxne
  nlinarith [norm_nonneg (x : V)]

end GroundTheory.Heights₂.Heights.LowerBound
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.PMeanCountBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBound

open Real MeasureTheory Filter Topology Finset

noncomputable section

universe u

theorem MeanCountBound.proof : MeanCountBound.Statement := by
  intro X _ μ lam cnt a ka r h
  have := h.isProbability
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = 1 / 12 := ⟨_, rfl⟩
  have hθ0 : 0 < θ := by rw [hθ]; norm_num
  have hθ1 : θ ≤ 1 := by rw [hθ]; norm_num
  have hθ12 : 12 * θ = 1 := by rw [hθ]; norm_num
  have hr := h.r_pos
  have ha0 : a ≠ 0 := by have := h.one_le_a; omega
  set m := meanCount μ cnt r with hm
  have hm0 : 0 ≤ m := integral_nonneg (h.cnt_nonneg r)
  have hprod : ∀ j : ℕ, (12 : ℝ) ^ j * θ ^ j = 1 := fun j => by
    rw [← mul_pow, hθ12, one_pow]

  have hpt : ∀ (j : ℕ) (z : X), lam z < r → θ ^ (j + 1) * r ≤ lam z →
      cnt r z ≤ (3 * 12 ^ (j + 1)) ^ a := by
    intro j z hlt hle
    have hl := h.lam_pos z
    calc cnt r z ≤ (3 * r / lam z) ^ a := h.count r hr le_rfl z hlt
      _ ≤ (3 * 12 ^ (j + 1)) ^ a := by
        gcongr
        rw [div_le_iff₀ hl]
        calc 3 * r = 3 * 12 ^ (j + 1) * (θ ^ (j + 1) * r) := by
              linear_combination (-(3 * r)) * hprod (j + 1)
          _ ≤ 3 * 12 ^ (j + 1) * lam z := by gcongr

  have hterm : ∀ k : ℕ, (36 * 12 ^ (k + 1) : ℝ) ^ a * meanCount μ cnt (θ ^ (k + 1) * r)
      ≤ 1 / 4 * (1 / 2) ^ k * m := by
    intro k
    have hy0 : 0 < θ ^ (k + 1) := pow_pos hθ0 _
    have hy1 : θ ^ (k + 1) ≤ 1 := pow_le_one₀ hθ0.le hθ1
    rw [h.scaling _ _ hy0 hr, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ hm0
    have hka : (θ ^ (k + 1)) ^ ka ≤ (θ ^ (k + 1)) ^ (3 * a) := by
      rw [← Real.rpow_natCast (θ ^ (k + 1)) (3 * a)]
      apply Real.rpow_le_rpow_of_exponent_ge hy0 hy1
      have := h.three_a_le_ka
      push_cast
      linarith
    have heq : (36 * 12 ^ (k + 1) : ℝ) ^ a * (θ ^ (k + 1)) ^ (3 * a)
        = (36 * (θ ^ (k + 1)) ^ 2) ^ a := by
      rw [pow_mul, ← mul_pow]
      congr 1
      linear_combination (36 * (θ ^ (k + 1)) ^ 2) * hprod (k + 1)
    have hsq : 36 * (θ ^ (k + 1)) ^ 2 = 1 / 4 * (θ ^ 2) ^ k := by
      have : θ ^ 2 = 1 / 144 := by rw [hθ]; norm_num
      rw [← pow_mul, show (k + 1) * 2 = 2 + 2 * k by ring, pow_add, pow_mul, this]
      ring
    have hθ2 : θ ^ 2 ≤ 1 / 2 := by rw [hθ]; norm_num
    have hs1 : 1 / 4 * (θ ^ 2) ^ k ≤ 1 / 4 * (1 / 2) ^ k := by gcongr
    have hs2 : 1 / 4 * (θ ^ 2) ^ k ≤ 1 := by
      calc 1 / 4 * (θ ^ 2) ^ k ≤ 1 / 4 * 1 := by
            gcongr; exact pow_le_one₀ (by positivity) (by linarith)
        _ ≤ 1 := by norm_num
    calc (36 * 12 ^ (k + 1) : ℝ) ^ a * (θ ^ (k + 1)) ^ ka
        ≤ (36 * 12 ^ (k + 1) : ℝ) ^ a * (θ ^ (k + 1)) ^ (3 * a) := by gcongr
      _ = (1 / 4 * (θ ^ 2) ^ k) ^ a := by rw [heq, hsq]
      _ ≤ 1 / 4 * (θ ^ 2) ^ k := pow_le_of_le_one (by positivity) hs2 ha0
      _ ≤ 1 / 4 * (1 / 2) ^ k := hs1

  let S : ℕ → Set X := fun N => {z | θ ^ (N + 1) * r ≤ lam z}
  have hSmeas : ∀ N, MeasurableSet (S N) := fun N =>
    measurableSet_le measurable_const h.lam_meas
  have hSmono : Monotone S := by
    intro N M hNM z hz
    simp only [S, Set.mem_ofPred_eq] at hz ⊢
    have : θ ^ (M + 1) ≤ θ ^ (N + 1) := pow_le_pow_of_le_one hθ0.le hθ1 (by omega)
    nlinarith
  have hSunion : ⋃ N, S N = Set.univ := by
    refine Set.eq_univ_of_forall fun z => ?_
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos (h.lam_pos z) hr)
      (show θ < 1 by rw [hθ]; norm_num)
    refine Set.mem_iUnion.2 ⟨n, ?_⟩
    simp only [S, Set.mem_ofPred_eq]
    have h1 : θ ^ (n + 1) ≤ θ ^ n := pow_le_pow_of_le_one hθ0.le hθ1 (by omega)
    rw [lt_div_iff₀ hr] at hn
    nlinarith

  have hbound : ∀ N, ∫ z in S N, cnt r z ∂μ ≤ 36 ^ a + m / 2 := by
    intro N
    set G : X → ℝ := fun z => 36 ^ a +
      ∑ i ∈ range N, (36 * 12 ^ (i + 1) : ℝ) ^ a * cnt (θ ^ (i + 1) * r) z with hG
    have hint : ∀ i : ℕ, Integrable (cnt (θ ^ (i + 1) * r)) μ := fun i =>
      h.integrable _ (mul_pos (pow_pos hθ0 _) hr)
    have hGi : Integrable G μ :=
      (integrable_const _).add (integrable_finsetSum _ fun i _ => (hint i).const_mul _)
    have hsum_nonneg : ∀ z, 0 ≤ ∑ i ∈ range N, (36 * 12 ^ (i + 1) : ℝ) ^ a *
        cnt (θ ^ (i + 1) * r) z := fun z =>
      sum_nonneg fun i _ => mul_nonneg (by positivity) (h.cnt_nonneg _ _)
    have hG0 : ∀ z, 0 ≤ G z := fun z => add_nonneg (by positivity) (hsum_nonneg z)
    have hle : ∀ z ∈ S N, cnt r z ≤ G z := by
      intro z hz
      simp only [S, Set.mem_ofPred_eq] at hz
      rcases le_or_gt r (lam z) with hrl | hlr
      · rw [h.zero r hr z hrl]; exact hG0 z
      classical
      have hex : ∃ j, θ ^ (j + 1) * r ≤ lam z := ⟨N, hz⟩
      set j := Nat.find hex with hj
      have hjle : j ≤ N := Nat.find_min' hex hz
      have hjspec : θ ^ (j + 1) * r ≤ lam z := Nat.find_spec hex
      rcases Nat.eq_zero_or_eq_succ_pred j with hj0 | hjs
      · calc cnt r z ≤ (3 * 12 ^ (j + 1)) ^ a := hpt j z hlr hjspec
          _ = 36 ^ a := by rw [hj0]; norm_num
          _ ≤ G z := le_add_of_nonneg_right (hsum_nonneg z)
      · set k := j.pred
        have hk : k < N := by omega
        have hnot : ¬ θ ^ (k + 1) * r ≤ lam z := Nat.find_min hex (by omega)
        have hone : 1 ≤ cnt (θ ^ (k + 1) * r) z :=
          h.one _ (mul_pos (pow_pos hθ0 _) hr)
            (mul_le_of_le_one_left hr.le (pow_le_one₀ hθ0.le hθ1)) z (lt_of_not_ge hnot)
        calc cnt r z ≤ (3 * 12 ^ (j + 1)) ^ a := hpt j z hlr hjspec
          _ = (36 * 12 ^ (k + 1) : ℝ) ^ a := by
              rw [hjs, Nat.succ_eq_add_one]; congr 1; ring
          _ ≤ (36 * 12 ^ (k + 1) : ℝ) ^ a * cnt (θ ^ (k + 1) * r) z :=
              le_mul_of_one_le_right (by positivity) hone
          _ ≤ ∑ i ∈ range N, (36 * 12 ^ (i + 1) : ℝ) ^ a * cnt (θ ^ (i + 1) * r) z :=
              single_le_sum (f := fun i => (36 * 12 ^ (i + 1) : ℝ) ^ a *
                cnt (θ ^ (i + 1) * r) z)
                (fun i _ => mul_nonneg (by positivity) (h.cnt_nonneg _ _))
                (mem_range.2 hk)
          _ ≤ G z := le_add_of_nonneg_left (by positivity)
    have hGint : ∫ z, G z ∂μ = 36 ^ a + ∑ i ∈ range N,
        (36 * 12 ^ (i + 1) : ℝ) ^ a * meanCount μ cnt (θ ^ (i + 1) * r) := by
      rw [hG, integral_add (integrable_const _)
        (integrable_finsetSum _ fun i _ => (hint i).const_mul _),
        integral_finsetSum _ fun i _ => (hint i).const_mul _]
      simp [integral_const_mul, meanCount]
    have hgeo : ∑ i ∈ range N, (36 * 12 ^ (i + 1) : ℝ) ^ a *
        meanCount μ cnt (θ ^ (i + 1) * r) ≤ m / 2 := by
      calc _ ≤ ∑ i ∈ range N, 1 / 4 * (1 / 2 : ℝ) ^ i * m := sum_le_sum fun i _ => hterm i
        _ = 1 / 4 * m * ∑ i ∈ range N, (1 / 2 : ℝ) ^ i := by
            rw [mul_sum]; exact sum_congr rfl fun i _ => by ring
        _ ≤ 1 / 4 * m * 2 := by gcongr; exact sum_geometric_two_le N
        _ = m / 2 := by ring
    calc ∫ z in S N, cnt r z ∂μ ≤ ∫ z in S N, G z ∂μ :=
          setIntegral_mono_on (h.integrable r hr).integrableOn hGi.integrableOn (hSmeas N) hle
      _ ≤ ∫ z, G z ∂μ := setIntegral_le_integral hGi (ae_of_all _ hG0)
      _ ≤ 36 ^ a + m / 2 := by rw [hGint]; linarith
  have ht := tendsto_setIntegral_of_monotone hSmeas hSmono
    (by rw [hSunion]; exact (h.integrable r hr).integrableOn)
  rw [hSunion, Measure.restrict_univ] at ht
  have hfin : m ≤ 36 ^ a + m / 2 := le_of_tendsto' ht hbound
  linarith

end

end GroundTheory.Heights₂.Heights.LowerBound
end
