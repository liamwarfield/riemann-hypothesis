module

public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CardToMultisetEqDegree
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EnormPowLeInvMeasureMulLintegralBall
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.NearestPlaneRounding
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.MulConjTransposeEqOneOfOrthonormal

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.GaussianSumOfOneSeparatedOfLe
open Metric MeasureTheory Module Set Real

namespace GlobalTheory

theorem finset_sum_exp_neg_le_of_card_le {ι : Type*} (s : Finset ι) (f : ι → ℝ) {t C : ℝ}
    (hf : ∀ i ∈ s, t ≤ f i)
    (hc : ∀ u, t ≤ u → ((s.filter fun i => f i ≤ u).card : ℝ) ≤ C * exp ((u - t) / 2)) :
    ∑ i ∈ s, exp (-f i) ≤ 2 * C * exp (-t) := by
  have hint : IntegrableOn (fun u : ℝ => exp (-u)) (Ici t) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).2 (integrableOn_exp_neg_Ioi t)
  have h1 : ∀ i ∈ s, exp (-f i) =
      ∫ u in Ici t, (Ici (f i)).indicator (fun u : ℝ => exp (-u)) u := by
    intro i hi
    rw [setIntegral_indicator measurableSet_Ici, Ici_inter_Ici, sup_eq_right.2 (hf i hi),
      integral_Ici_eq_integral_Ioi, integral_exp_neg_Ioi]
  have hint2 : IntegrableOn (fun u : ℝ => exp (-(1 / 2) * u)) (Ici t) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).2 (exp_neg_integrableOn_Ioi t (by norm_num))
  rw [Finset.sum_congr rfl h1, ← MeasureTheory.integral_finsetSum _
    (fun i _ => hint.indicator measurableSet_Ici)]
  calc ∫ u in Ici t, ∑ i ∈ s, (Ici (f i)).indicator (fun u : ℝ => exp (-u)) u
      ≤ ∫ u in Ici t, (C * exp (-t / 2)) * exp (-(1 / 2) * u) := by
        refine setIntegral_mono_on
          (MeasureTheory.integrable_finsetSum _ fun i _ => hint.indicator measurableSet_Ici)
          (hint2.const_mul _) measurableSet_Ici fun u hu => ?_
        have e : ∑ i ∈ s, (Ici (f i)).indicator (fun u : ℝ => exp (-u)) u =
            ((s.filter fun i => f i ≤ u).card : ℝ) * exp (-u) := by
          simp only [indicator, mem_Ici]
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        rw [e]
        calc _ ≤ C * exp ((u - t) / 2) * exp (-u) :=
              mul_le_mul_of_nonneg_right (hc u hu) (exp_pos _).le
          _ = _ := by
              rw [mul_assoc, mul_assoc, ← exp_add, ← exp_add]; congr 2; ring
    _ = 2 * C * exp (-t) := by
        rw [integral_const_mul, integral_Ici_eq_integral_Ioi,
          integral_exp_mul_Ioi (by norm_num)]
        have : exp (-t) = exp (-t / 2) * exp (-(1 / 2) * t) := by
          rw [← exp_add]; congr 1; ring
        rw [this]; ring

theorem summable_exp_neg_of_card_le {ι : Type*} (f : ι → ℝ) {t C : ℝ} (hf : ∀ i, t ≤ f i)
    (hc : ∀ (s : Finset ι) u, t ≤ u → (∀ i ∈ s, f i ≤ u) → (s.card : ℝ) ≤ C * exp ((u - t) / 2)) :
    Summable (fun i => exp (-f i)) ∧ ∑' i, exp (-f i) ≤ 2 * C * exp (-t) := by
  have key : ∀ s : Finset ι, ∑ i ∈ s, exp (-f i) ≤ 2 * C * exp (-t) := fun s =>
    finset_sum_exp_neg_le_of_card_le s f (fun i _ => hf i) fun u hu =>
      hc _ u hu fun i hi => (Finset.mem_filter.1 hi).2
  have hs := summable_of_sum_le (fun i => (exp_pos (-f i)).le) key
  exact ⟨hs, hs.tsum_le_of_sum_le key⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusSplitting.GaussTailOfCardLe
open ReciprocityTheory.ChartRestriction.G.I2

namespace GlobalTheory

theorem gaussTail_of_card_le : Ext.GaussianTailBound := by
  intro ι h g R0 hR0 hg hh hcard
  obtain ⟨t, ht_def⟩ : ∃ t : ℝ, t = R0 ^ 2 / 16 := ⟨_, rfl⟩
  have ht : 0 < t := by rw [ht_def]; positivity
  have ht' : 2 * (g : ℝ) + 1 ≤ t := by rw [ht_def]; linarith

  have key := GlobalTheory.summable_exp_neg_of_card_le (fun i => h i ^ 2 / 16) (t := t) (C := 9 ^ g)
    (fun i => by
      have h1 := hh i
      have h2 : R0 ^ 2 ≤ h i ^ 2 := by nlinarith
      rw [ht_def]
      linarith)
    (fun s u htu hs => by
      have hu0 : 0 < u := lt_of_lt_of_le ht htu
      obtain ⟨R, hR⟩ : ∃ R : ℝ, R = 4 * Real.sqrt u := ⟨_, rfl⟩
      have hsq : Real.sqrt u ^ 2 = u := Real.sq_sqrt hu0.le
      have hR2 : R ^ 2 = 16 * u := by rw [hR, mul_pow, hsq]; norm_num
      have hRnn : 0 ≤ R := by rw [hR]; positivity

      have hle : ∀ x : ℝ, 0 ≤ x → x ^ 2 ≤ 16 * u → x ≤ R := fun x hx hx2 => by
        nlinarith
      have hR0R : R0 ≤ R := hle R0 hR0.le (by rw [ht_def] at htu; linarith)
      have hsS : ∀ i ∈ s, h i ≤ R := fun i hi => by
        have h3 := hs i hi
        exact hle (h i) (hR0.le.trans (hh i)) (by linarith)
      refine (hcard R hR0R s hsS).trans ?_
      have hpow : (3 * R / R0) ^ (2 * g) = 9 ^ g * (u / t) ^ g := by
        rw [pow_mul, ← mul_pow]
        congr 1
        rw [div_pow, mul_pow, hR2, ht_def]
        field_simp
        ring
      rw [hpow]
      apply mul_le_mul_of_nonneg_left _ (by positivity)

      have hx : u / t ≤ Real.exp (u / t - 1) := by
        have := Real.add_one_le_exp (u / t - 1)
        linarith
      have hy : u - t = t * (u / t - 1) := by field_simp
      have hy0 : 0 ≤ u / t - 1 := by
        by_contra hc
        rw [not_le] at hc
        nlinarith
      calc (u / t) ^ g ≤ Real.exp (u / t - 1) ^ g := by gcongr
        _ = Real.exp (g * (u / t - 1)) := by rw [← Real.exp_nat_mul]
        _ ≤ Real.exp ((u - t) / 2) := by
          apply Real.exp_le_exp.mpr
          rw [hy]
          nlinarith [mul_le_mul_of_nonneg_right ht' hy0])
  have e : ∀ i, -(h i) ^ 2 / 16 = -(h i ^ 2 / 16) := fun i => by ring
  simp only [e]
  refine ⟨key.1, key.2.trans_eq ?_⟩
  rw [ht_def, neg_div]

end GlobalTheory
end

open ReciprocityTheory.ChartRestriction.G.I2

namespace GlobalTheory

private theorem ext_ballVolume : _root_.ReciprocityTheory.ChartRestriction.G.I2.Ext.BallVolume := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.I2.Ext.BallVolume
  intro D rr hr
  exact _root_.GlobalTheory.volume_ball_of_finrank_eq_two_mul (by simp) 0 hr

private theorem ext_gHadamard : _root_.ReciprocityTheory.ChartRestriction.G.I2.Ext.GHadamard := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.I2.Ext.GHadamard
  intro n M
  simpa [Real.norm_eq_abs, sq_abs] using _root_.GlobalTheory.Hadamard.norm_det_le_prod_col M

private theorem ext_cauchyBinetMax' : _root_.ReciprocityTheory.ChartRestriction.G.I2.Ext.CauchyBinetMax := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.I2.Ext.CauchyBinetMax
  intro i N r M hM hr
  obtain ⟨S, hS⟩ := _root_.GlobalTheory.exists_two_rpow_le_norm_minor M hM (r := r) (by simpa using hr)
  refine ⟨_root_.GlobalTheory.subsetEnum S, ?_, hS⟩
  unfold _root_.GlobalTheory.subsetEnum
  exact (Finset.orderEmbOfFin _ _).strictMono

private theorem ext_detPerturbation : _root_.ReciprocityTheory.ChartRestriction.G.I2.Ext.DetPerturbation := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.I2.Ext.DetPerturbation
  intro 𝕜 _ i κ _ w σ₀ ε Δmax hΔ
  classical
  set f := (Matrix.detRowAlternating : (Fin i → 𝕜) [⋀^Fin i]→ₗ[𝕜] 𝕜).toMultilinearMap with hf
  have hD : ∀ cols : Fin i → Fin i → 𝕜, (Matrix.of fun a j => cols j a).det = f cols := by
    intro cols
    rw [show (Matrix.of fun a j => cols j a) = (Matrix.of cols).transpose from rfl, Matrix.det_transpose]
    rfl
  have hΔ0 : 0 ≤ Δmax := (norm_nonneg _).trans (hΔ σ₀)
  set coef : Fin i → Option κ → 𝕜 := fun j o => Option.elim o 1 (ε j) with hcoef
  set pick : Fin i → Option κ → κ := fun j o => Option.elim o (σ₀ j) id with hpick
  have hcol : (fun j => w (σ₀ j) + ∑ k, ε j k • w k) = fun j => ∑ o, coef j o • w (pick j o) := by
    funext j
    rw [Fintype.sum_option]
    simp [hcoef, hpick]
  have hexp : f (fun j => w (σ₀ j) + ∑ k, ε j k • w k)
      = ∑ r : Fin i → Option κ, (∏ j, coef j (r j)) • f (fun j => w (pick j (r j))) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hcol, MultilinearMap.map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    exact f.map_smul_univ (fun j => coef j (r j)) (fun j => w (pick j (r j)))
  set r0 : Fin i → Option κ := fun _ => none with hr0
  have hterm0 : (∏ j, coef j (r0 j)) • f (fun j => w (pick j (r0 j))) = f (fun j => w (σ₀ j)) := by
    simp [hr0, hcoef, hpick]
  rw [hD, hD, hexp, ← Finset.add_sum_erase _ _ (Finset.mem_univ r0), hterm0, add_sub_cancel_left]
  have hbound : ∀ r : Fin i → Option κ, ‖(∏ j, coef j (r j)) • f (fun j => w (pick j (r j)))‖
      ≤ (∏ j, ‖coef j (r j)‖) * Δmax := by
    intro r
    rw [norm_smul, norm_prod]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [← hD]
    exact hΔ (fun j => pick j (r j))
  have hsum : ∑ r : Fin i → Option κ, ∏ j, ‖coef j (r j)‖ = ∏ j, (1 + ∑ k, ‖ε j k‖) := by
    have hps : ∏ j, ∑ o, ‖coef j o‖ = ∑ r : Fin i → Option κ, ∏ j, ‖coef j (r j)‖ := by
      rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    rw [← hps]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [Fintype.sum_option]
    simp [hcoef]
  have hone : ∏ j, ‖coef j (r0 j)‖ = 1 := by simp [hr0, hcoef]
  calc ‖∑ r ∈ Finset.univ.erase r0, (∏ j, coef j (r j)) • f (fun j => w (pick j (r j)))‖
      ≤ ∑ r ∈ Finset.univ.erase r0, (∏ j, ‖coef j (r j)‖) * Δmax :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => hbound r)
    _ = (∏ j, (1 + ∑ k, ‖ε j k‖) - 1) * Δmax := by
        rw [← Finset.sum_mul, ← hsum, ← Finset.add_sum_erase _ _ (Finset.mem_univ r0), hone]
        ring

private theorem ext_detPerturbNumeric : _root_.ReciprocityTheory.ChartRestriction.G.I2.Ext.DetPerturbNumeric := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.I2.Ext.DetPerturbNumeric
  intro ρ hρ
  have hρ1 : (1 : ℝ) ≤ ρ := by exact_mod_cast hρ
  have hρ0 : (0 : ℝ) < ρ := by linarith
  have hle : (ρ : ℝ) ^ (-3 / 2 : ℝ) ≤ (ρ : ℝ) ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hρ1 (by norm_num)
  have hmul : (ρ : ℝ) * ((ρ : ℝ) ^ (-3 / 2 : ℝ) / 10) ≤ 1 / 10 := by
    rw [Real.rpow_neg_one] at hle
    have : (ρ : ℝ) * (ρ : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hρ0.ne'
    nlinarith
  have h1 : (1 + (ρ : ℝ) ^ (-3 / 2 : ℝ) / 10) ^ ρ
      ≤ Real.exp ((ρ : ℝ) * ((ρ : ℝ) ^ (-3 / 2 : ℝ) / 10)) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity)
      (by linarith [Real.add_one_le_exp ((ρ : ℝ) ^ (-3 / 2 : ℝ) / 10)]) ρ
  have h2 : Real.exp ((ρ : ℝ) * ((ρ : ℝ) ^ (-3 / 2 : ℝ) / 10)) ≤ Real.exp (1 / 10) :=
    Real.exp_le_exp.2 hmul
  have h3 : Real.exp (1 / 10) ≤ 3 / 2 := by
    have := Real.abs_exp_sub_one_sub_id_le (x := 1 / 10) (by norm_num [abs_of_pos])
    rw [abs_le] at this
    nlinarith [this.2]
  linarith

private theorem two_pow_add_pow_sub_two_pow_mul_le (c : ℕ) (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    ∀ i : ℕ, ((2 : ℝ) ^ c + ε) ^ i - 2 ^ (c * i) ≤ i * ε * (2 ^ c + 1) ^ i := by
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
    have hb : (0 : ℝ) ≤ 2 ^ c := by positivity
    have hB1 : (1 : ℝ) ≤ 2 ^ c + 1 := by linarith
    have hbB : (2 : ℝ) ^ (c * i) ≤ (2 ^ c + 1) ^ (i + 1) := by
      rw [pow_mul]
      have hbase : ((2 : ℝ) ^ c) ^ i ≤ (2 ^ c + 1) ^ i :=
        pow_le_pow_left₀ hb (by linarith) i
      exact hbase.trans (pow_le_pow_right₀ hB1 (Nat.le_succ i))
    have ha : 0 ≤ (2 : ℝ) ^ c + ε := by linarith
    have hpos : 0 ≤ (i : ℝ) * ε * (2 ^ c + 1) ^ i := by positivity
    have e : ((2 : ℝ) ^ c + ε) ^ (i + 1) - 2 ^ (c * (i + 1))
        = (2 ^ c + ε) * ((2 ^ c + ε) ^ i - 2 ^ (c * i)) + ε * 2 ^ (c * i) := by
      rw [mul_add_one, pow_add (2 : ℝ) (c * i) c, pow_succ ((2 : ℝ) ^ c + ε) i]
      ring
    rw [e]
    have k1 := mul_le_mul_of_nonneg_left ih ha
    have k2 := mul_le_mul_of_nonneg_right (show (2 : ℝ) ^ c + ε ≤ 2 ^ c + 1 by linarith) hpos
    have k3 := mul_le_mul_of_nonneg_left hbB h0
    have k4 : ((i + 1 : ℕ) : ℝ) * ε * (2 ^ c + 1) ^ (i + 1)
        = (2 ^ c + 1) * (i * ε * (2 ^ c + 1) ^ i) + ε * (2 ^ c + 1) ^ (i + 1) := by
      rw [Nat.cast_succ, pow_succ ((2 : ℝ) ^ c + 1) i]
      ring
    rw [k4]
    exact add_le_add (k1.trans k2) k3

private theorem ext_detProductRest : _root_.ReciprocityTheory.ChartRestriction.G.I2.Ext.DetProductRest := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.I2.Ext.DetProductRest
  intro i c ε h0 h1
  exact two_pow_add_pow_sub_two_pow_mul_le c ε h0 h1 i

theorem _root_.GlobalTheory.ext_all_inputs : _root_.ReciprocityTheory.ChartRestriction.G.I2.Ext.All := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.I2.Ext.All
  exact ⟨_root_.GlobalTheory.packingCount, _root_.GlobalTheory.gaussTail_of_card_le, ext_ballVolume, ext_gHadamard,
    _root_.GlobalTheory.nearestPlane_rounding, ext_cauchyBinetMax', ext_detPerturbation,
    ext_detPerturbNumeric, ext_detProductRest⟩

end GlobalTheory
