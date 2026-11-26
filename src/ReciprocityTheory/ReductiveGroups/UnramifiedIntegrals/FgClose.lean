module

public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgHonH
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.EndIntegral
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgLevel

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.SemilinNormPowSubPow
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K]

omit [CompleteSpace K] [CharZero K] in
theorem semilin_norm_add_of_lt {a b : K} (h : ‖b‖ < ‖a‖) : ‖a + b‖ = ‖a‖ := by
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h.ne', max_eq_left h.le]

omit [CompleteSpace K] [CharZero K] in
theorem semilin_norm_sub_le {a b : K} {t : ℝ} (ha : ‖a‖ ≤ t) (hb : ‖b‖ ≤ t) : ‖a - b‖ ≤ t := by
  rw [sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha (by rwa [norm_neg]))


omit [CompleteSpace K] [CharZero K] in
theorem semilin_norm_pow_sub_pow {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (n : ℕ) :
    ‖a ^ n - b ^ n‖ ≤ ‖a - b‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : a ^ (n + 1) - b ^ (n + 1) = a * (a ^ n - b ^ n) + (a - b) * b ^ n := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      calc ‖a‖ * ‖a ^ n - b ^ n‖ ≤ 1 * ‖a - b‖ := mul_le_mul ha ih (norm_nonneg _) zero_le_one
        _ = ‖a - b‖ := one_mul _
    · rw [norm_mul, norm_pow]
      calc ‖a - b‖ * ‖b‖ ^ n ≤ ‖a - b‖ * 1 :=
            mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) hb) (norm_nonneg _)
        _ = ‖a - b‖ := mul_one _


omit [CompleteSpace K] [CharZero K] in
theorem FrobField.norm_sq_sub_pow_le {l : ℕ} {σ : K →+* K} (h : FrobField K l σ) (x : K) (hx : ‖x‖ ≤ 1) :
    ‖σ (σ x) - x ^ (l ^ 2)‖ ≤ ‖(l : K)‖ := by
  have hp : x ^ (l ^ 2) = (x ^ l) ^ l := by rw [← pow_mul, sq]
  have e : σ (σ x) - x ^ (l ^ 2) = σ (σ x - x ^ l) + ((σ x) ^ l - (x ^ l) ^ l) := by
    rw [hp, map_sub, map_pow]
    ring
  have h1 : ‖σ x - x ^ l‖ ≤ ‖(l : K)‖ := h.frob x hx
  rw [e]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [h.isom]; exact h1
  · refine (semilin_norm_pow_sub_pow (by rw [h.isom]; exact hx) ?_ l).trans h1
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx


open Polynomial in
theorem semilin_root {l : ℕ} (hR : ResClosed K l) {m : ℕ} (hm : 2 ≤ m) (a b : K) (ha : ‖a‖ ≤ 1)
    (hb : ‖b‖ ≤ 1) : ∃ x : K, ‖x‖ ≤ 1 ∧ ‖x ^ m + a * x + b‖ ≤ ‖(l : K)‖ := by
  have hdeg : (C a * X + C b : K[X]).degree < (X ^ m : K[X]).degree := by
    rw [degree_X_pow]
    exact lt_of_le_of_lt degree_linear_le (by exact_mod_cast hm)
  have hmon : (X ^ m + (C a * X + C b) : K[X]).Monic := monic_X_pow_add (by rwa [degree_X_pow] at hdeg)
  have hnat : (X ^ m + (C a * X + C b) : K[X]).natDegree = m := by
    rw [natDegree_add_eq_left_of_degree_lt hdeg, natDegree_X_pow]
  have hco : ∀ i, ‖(X ^ m + (C a * X + C b) : K[X]).coeff i‖ ≤ 1 := by
    intro i
    simp only [coeff_add, coeff_X_pow, coeff_C_mul_X, coeff_C]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_
      ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_))) <;> split_ifs <;> simp [ha, hb]
  obtain ⟨x, hx, hev⟩ := hR _ hmon (by omega) hco
  refine ⟨x, hx, ?_⟩
  simpa [add_assoc] using hev


open Filter Topology in
theorem lang_semilinear {l : ℕ} {σ : K →+* K} (h : FrobField K l σ) (hR : ResClosed K l)
    (c : K) (hc : ‖c‖ = 1) : ∃ ε : K, ‖ε‖ = 1 ∧ ε = c * σ (σ ε) := by
  have hl2 : 2 ≤ l := h.prime.two_le
  have hc0 : c ≠ 0 := norm_ne_zero_iff.mp (by rw [hc]; norm_num)
  have hcc : c * c⁻¹ = 1 := mul_inv_cancel₀ hc0
  have hci : ‖c⁻¹‖ = 1 := by rw [norm_inv, hc, inv_one]
  have hl0 : (l : K) ≠ 0 := Nat.cast_ne_zero.mpr h.prime.ne_zero
  have hl1 := h.norm_l
  have hq4 : 4 ≤ l ^ 2 := by nlinarith

  let P : ℕ → K → Prop := fun n ε => ‖ε‖ = 1 ∧ ‖ε - c * σ (σ ε)‖ ≤ ‖(l : K)‖ ^ (n + 1)
  have h0 : ∃ ε, P 0 ε := by
    obtain ⟨x, hx, hev⟩ := semilin_root hR (m := l ^ 2 - 1) (by omega) 0 (-c⁻¹) (by simp)
      (by rw [norm_neg, hci])
    rw [zero_mul, add_zero, ← sub_eq_add_neg] at hev
    have hx1 : ‖x‖ = 1 := by
      have h1 : ‖x ^ (l ^ 2 - 1)‖ = 1 := by
        have e : x ^ (l ^ 2 - 1) = c⁻¹ + (x ^ (l ^ 2 - 1) - c⁻¹) := by ring
        rw [e, semilin_norm_add_of_lt (by rw [hci]; exact hev.trans_lt hl1), hci]
      rw [norm_pow] at h1
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by omega)).mp h1
    refine ⟨x, hx1, ?_⟩
    have hxq : x ^ (l ^ 2) = x * x ^ (l ^ 2 - 1) := by
      rw [← pow_succ']; congr 1; omega
    have e : x - c * σ (σ x) = -(c * x) * (x ^ (l ^ 2 - 1) - c⁻¹) - c * (σ (σ x) - x ^ (l ^ 2)) := by
      rw [hxq]
      linear_combination (-x) * hcc
    rw [e, zero_add, pow_one]
    refine semilin_norm_sub_le ?_ ?_
    · rw [norm_mul, norm_neg, norm_mul, hc, hx1, one_mul, one_mul]; exact hev
    · rw [norm_mul, hc, one_mul]; exact h.norm_sq_sub_pow_le x hx
  have hstep : ∀ n ε, P n ε → ∃ ε', P (n + 1) ε' ∧ ‖ε' - ε‖ ≤ ‖(l : K)‖ ^ (n + 1) := by
    rintro n ε ⟨hε1, hε2⟩
    have hlam0 : (l : K) ^ (n + 1) ≠ 0 := pow_ne_zero _ hl0
    have hnl : ‖(l : K) ^ (n + 1)‖ = ‖(l : K)‖ ^ (n + 1) := norm_pow _ _
    have hsm : ‖(l : K)‖ ^ (n + 1) < 1 := pow_lt_one₀ (norm_nonneg _) hl1 (Nat.succ_ne_zero n)
    obtain ⟨ρ, hρ⟩ : ∃ ρ, ε - c * σ (σ ε) = (l : K) ^ (n + 1) * ρ :=
      ⟨(ε - c * σ (σ ε)) / (l : K) ^ (n + 1), by field_simp⟩
    have hρ1 : ‖ρ‖ ≤ 1 := by
      have hpos : 0 < ‖(l : K)‖ ^ (n + 1) := by rw [← hnl]; exact norm_pos_iff.mpr hlam0
      rw [hρ, norm_mul, hnl] at hε2
      exact le_of_mul_le_mul_left (by rwa [mul_one]) hpos
    obtain ⟨δ, hδ, hev⟩ := semilin_root hR (m := l ^ 2) (by omega) (-c⁻¹) (-(c⁻¹ * ρ))
      (by rw [norm_neg, hci]) (by rw [norm_neg, norm_mul, hci, one_mul]; exact hρ1)
    have hσl : σ (σ ((l : K) ^ (n + 1))) = (l : K) ^ (n + 1) := by simp [map_pow, map_natCast]
    have hlδ : ‖(l : K) ^ (n + 1) * δ‖ ≤ ‖(l : K)‖ ^ (n + 1) := by
      rw [norm_mul, hnl]
      calc ‖(l : K)‖ ^ (n + 1) * ‖δ‖ ≤ ‖(l : K)‖ ^ (n + 1) * 1 :=
            mul_le_mul_of_nonneg_left hδ (by positivity)
        _ = _ := mul_one _
    refine ⟨ε + (l : K) ^ (n + 1) * δ, ⟨?_, ?_⟩, ?_⟩
    · rw [semilin_norm_add_of_lt (by rw [hε1]; exact hlδ.trans_lt hsm), hε1]
    · have e : ε + (l : K) ^ (n + 1) * δ - c * σ (σ (ε + (l : K) ^ (n + 1) * δ)) =
          (l : K) ^ (n + 1) * (-c * (δ ^ (l ^ 2) + -c⁻¹ * δ + -(c⁻¹ * ρ)) - c * (σ (σ δ) - δ ^ (l ^ 2))) := by
        rw [map_add (f := _), map_add (f := _), map_mul, map_mul, hσl]
        linear_combination hρ - ((l : K) ^ (n + 1) * ρ + (l : K) ^ (n + 1) * δ) * hcc
      rw [e, norm_mul, hnl, pow_succ ‖(l : K)‖ (n + 1)]
      refine mul_le_mul_of_nonneg_left (semilin_norm_sub_le ?_ ?_) (by positivity)
      · rw [norm_mul, norm_neg, hc, one_mul]; exact hev
      · rw [norm_mul, hc, one_mul]; exact h.norm_sq_sub_pow_le δ hδ
    · rw [add_sub_cancel_left]; exact hlδ

  obtain ⟨ε0, hε0⟩ := h0
  choose g hg using hstep
  let v : (n : ℕ) → {x : K // P n x} := fun n =>
    Nat.rec (motive := fun n => {x : K // P n x}) ⟨ε0, hε0⟩
      (fun n ih => ⟨g n ih.1 ih.2, (hg n ih.1 ih.2).1⟩) n
  let u : ℕ → K := fun n => (v n).1
  have hu : ∀ n, P n (u n) := fun n => (v n).2
  have hud : ∀ n, ‖u (n + 1) - u n‖ ≤ ‖(l : K)‖ ^ (n + 1) := fun n => (hg n (u n) (hu n)).2
  have hcau : CauchySeq u := by
    refine cauchySeq_of_le_geometric ‖(l : K)‖ ‖(l : K)‖ hl1 fun n => ?_
    rw [dist_eq_norm, norm_sub_rev, ← pow_succ']
    exact hud n
  obtain ⟨ε, hlim⟩ := cauchySeq_tendsto_of_complete hcau
  have hσc : Continuous σ := ((AddMonoidHomClass.isometry_iff_norm σ).mpr h.isom).continuous
  have hres : Filter.Tendsto (fun n => u n - c * σ (σ (u n))) Filter.atTop (nhds (ε - c * σ (σ ε))) :=
    hlim.sub ((((hσc.comp hσc).tendsto ε).comp hlim).const_mul c)
  have hres0 : Filter.Tendsto (fun n => u n - c * σ (σ (u n))) Filter.atTop (nhds 0) :=
    squeeze_zero_norm (fun n => (hu n).2.trans (pow_le_pow_of_le_one (norm_nonneg _) hl1.le (Nat.le_succ n)))
      (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hl1)
  have hn : Filter.Tendsto (fun n => ‖u n‖) Filter.atTop (nhds ‖ε‖) := hlim.norm
  have hconst : (fun n => ‖u n‖) = fun _ => (1 : ℝ) := funext fun n => (hu n).1
  rw [hconst] at hn
  exact ⟨ε, tendsto_nhds_unique hn tendsto_const_nhds, sub_eq_zero.mp (tendsto_nhds_unique hres hres0)⟩

end ReciprocityTheory.ChartRestriction.L1
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgFinA
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {l : ℕ} {σ : K →+* K}

theorem FrobField.funEqSetting_sq [CompleteSpace K] (h : FrobField K l σ) :
    FunctionalEquationSetting K l (l ^ 2) (σ.comp σ) :=
  ⟨h.prime, ⟨2, two_pos, rfl⟩, h.norm_l, fun a ha => h.norm_sq_sub_pow_le a ha⟩


omit [IsUltrametricDist K] [CharZero K] in
theorem ltLog_sub_eq_X (hl : 2 ≤ l) (τ : K →+* K) :
    ltLog K l - (l : K)⁻¹ • (PowerSeries.map τ (ltLog K l)).subst ((X : PowerSeries K) ^ (l ^ 2))
      = X := by
  have hq : 2 ≤ l ^ 2 := by nlinarith
  have hq0 : l ^ 2 ≠ 0 := by omega
  have hsub : ∀ (f : PowerSeries K) {k : ℕ} (_ : k ≠ 0) (m : ℕ),
      coeff m (f.subst ((X : PowerSeries K) ^ k)) = if k ∣ m then coeff (m / k) f else 0 := by
    intro f k hk m
    have ha : PowerSeries.HasSubst ((X : PowerSeries K) ^ k) :=
      PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hk])
    rw [PowerSeries.coeff_subst' ha]
    simp only [← pow_mul, PowerSeries.coeff_X_pow]
    split_ifs with hd
    · obtain ⟨q, rfl⟩ := hd
      rw [finsum_eq_single _ q]
      · simp [Nat.mul_div_cancel_left q (Nat.pos_of_ne_zero hk)]
      · intro d hd
        have : k * q ≠ k * d := fun h => hd (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hk) h).symm
        simp [this]
    · rw [finsum_eq_zero_of_forall_eq_zero]
      intro d
      have : m ≠ k * d := fun h => hd ⟨d, h⟩
      simp [this]
  have hpow : ∀ j, coeff ((l ^ 2) ^ j) (ltLog K l) = ((l : K) ^ j)⁻¹ := by
    intro j
    have hex : ∃ i : ℕ, (l ^ 2) ^ j = (l ^ 2) ^ i := ⟨j, rfl⟩
    rw [Formalism.L2.Th1.CM.ltLog, PowerSeries.coeff_mk, dite_eq_left hex]
    have hf : Nat.find hex = j := (Nat.pow_right_injective hq (Nat.find_spec hex)).symm
    rw [hf]
  ext n
  rw [map_sub, PowerSeries.coeff_smul, hsub _ hq0, PowerSeries.coeff_X]
  by_cases hn : ∃ j, n = (l ^ 2) ^ j
  · obtain ⟨j, rfl⟩ := hn
    rcases j with _ | j
    · have h1 : (l ^ 2) ^ 0 = 1 := pow_zero _
      have hnd : ¬ l ^ 2 ∣ (l ^ 2) ^ 0 := by
        rw [h1]
        intro h
        have := Nat.le_of_dvd one_pos h
        omega
      rw [if_neg hnd, hpow 0, h1, if_pos rfl]
      simp
    · have hd : l ^ 2 ∣ (l ^ 2) ^ (j + 1) := dvd_pow_self _ (Nat.succ_ne_zero j)
      have hdiv : (l ^ 2) ^ (j + 1) / l ^ 2 = (l ^ 2) ^ j := by
        rw [pow_succ (l ^ 2) j, Nat.mul_div_cancel _ (by omega)]
      have hne : (l ^ 2) ^ (j + 1) ≠ 1 := by
        have : l ^ 2 ≤ (l ^ 2) ^ (j + 1) := Nat.le_self_pow (Nat.succ_ne_zero j) _
        omega
      rw [if_pos hd, hdiv, PowerSeries.coeff_map, hpow, hpow,
        if_neg hne, map_inv₀, map_pow, map_natCast, pow_succ (l : K) j, mul_inv]
      ring
  · have h0 : coeff n (ltLog K l) = 0 := by rw [Formalism.L2.Th1.CM.ltLog, PowerSeries.coeff_mk, dite_eq_right hn]
    have hX : n ≠ 1 := fun h => hn ⟨0, by rw [h, pow_zero]⟩
    rw [h0, if_neg hX]
    split_ifs with hd
    · obtain ⟨m, rfl⟩ := hd
      have hm : ¬ ∃ j, m = (l ^ 2) ^ j := fun ⟨j, hj⟩ => hn ⟨j + 1, by rw [hj, pow_succ (l ^ 2) j, mul_comm]⟩
      rw [Nat.mul_div_cancel_left m (by omega), PowerSeries.coeff_map, Formalism.L2.Th1.CM.ltLog, PowerSeries.coeff_mk,
        dite_eq_right hm, map_zero]
      simp
    · simp

theorem ltLog_type (hl : 2 ≤ l) (τ : K →+* K) : IsFunEqType l (l ^ 2) τ (ltLog K l) := by
  unfold IsFunEqType
  rw [ltLog_sub_eq_X hl τ]
  exact integralPS_X


omit [IsUltrametricDist K] [CharZero K] in
theorem isFunEqType_of_mv {p q : ℕ} (hq : q ≠ 0) (τ : K →+* K) (f : PowerSeries K)
    (h : IsFunEqTypeMv (ι := Unit) p q hq τ f) : IsFunEqType p q τ f := by
  unfold IsFunEqType IsFunEqTypeMv at *
  have he : (PowerSeries.map τ f).subst ((X : PowerSeries K) ^ q)
      = MvPowerSeries.expand q hq (MvPowerSeries.map τ f) := by
    first
    | rfl
    | exact (MvPowerSeries.expand_eq_subst _ _ _).symm
    | (simp only [MvPowerSeries.expand, PowerSeries.subst]; rfl)
    | (unfold MvPowerSeries.expand; rw [MvPowerSeries.coe_substAlgHom]; rfl)
    | (unfold MvPowerSeries.expand; rw [MvPowerSeries.coe_substAlgHom]; congr 1)
    | (unfold MvPowerSeries.expand; rw [MvPowerSeries.coe_substAlgHom, PowerSeries.subst]; congr 1)
  rw [he]
  unfold IntegralPS
  intro n
  first
  | exact h (Finsupp.single () n)
  | exact (by unfold IntegralMv at h; exact h (Finsupp.single () n))

omit [IsUltrametricDist K] [CharZero K] in
theorem inv_mul_inv_eq_of_eq_mul (c ε t x : K) (hc : c ≠ 0) (h : ε = c * t) :
    x⁻¹ * t⁻¹ = ε⁻¹ * (c / x) := by
  rw [h, mul_inv, div_eq_mul_inv]
  calc x⁻¹ * t⁻¹ = (c⁻¹ * c) * (t⁻¹ * x⁻¹) := by rw [inv_mul_cancel₀ hc, one_mul, mul_comm]
    _ = c⁻¹ * t⁻¹ * (c * x⁻¹) := by ring

theorem fin_integral [CompleteSpace K] (hF : FrobField K l σ) (ex lam : PowerSeries K)
    (hlam0 : constantCoeff lam = 0) (hlam1 : coeff 1 lam = 1) (hex0 : constantCoeff ex = 0)
    (hinv : ex.subst lam = X) (c ε : K) (hc : ‖c‖ = 1) (hε : ‖ε‖ = 1) (hcε : ε = c * σ (σ ε))
    (hT : IntegralPS (lam - (c / (l : K)) •
      (PowerSeries.map (σ.comp σ) lam).subst ((X : PowerSeries K) ^ (l ^ 2)))) :
    IntegralPS (ex.subst (C ε * ltLog K l)) := by
  have hl2 : 2 ≤ l := hF.prime.two_le
  have hq : l ^ 2 ≠ 0 := pow_ne_zero 2 hF.prime.ne_zero
  have hS := hF.funEqSetting_sq
  have hε0 : ε ≠ 0 := fun h => by simp [h] at hε
  have hτε0 : σ (σ ε) ≠ 0 := fun h => hε0 (by rw [hcε, h, mul_zero])
  have hXq : PowerSeries.HasSubst ((X : PowerSeries K) ^ (l ^ 2)) := PowerSeries.HasSubst.X_pow hq

  set f0 : PowerSeries K := ε⁻¹ • lam with hf0
  have hf00 : constantCoeff f0 = 0 := by
    rw [hf0, ← coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_smul,
      coeff_zero_eq_constantCoeff_apply, hlam0, smul_zero]
  have hf0T : IsFunEqType l (l ^ 2) (σ.comp σ) f0 := by
    unfold IsFunEqType
    have e : f0 - (l : K)⁻¹ • (PowerSeries.map (σ.comp σ) f0).subst ((X : PowerSeries K) ^ (l ^ 2))
        = C ε⁻¹ * (lam - (c / (l : K)) •
          (PowerSeries.map (σ.comp σ) lam).subst ((X : PowerSeries K) ^ (l ^ 2))) := by
      have e1 : PowerSeries.map (σ.comp σ) f0 = (σ (σ ε))⁻¹ • PowerSeries.map (σ.comp σ) lam := by
        ext n
        rw [hf0, coeff_map, PowerSeries.coeff_smul, PowerSeries.coeff_smul, coeff_map, smul_eq_mul,
          smul_eq_mul, map_mul, map_inv₀]
        rfl
      rw [e1, PowerSeries.subst_smul hXq, smul_smul, ← smul_eq_C_mul, smul_sub, smul_smul, hf0]
      congr 2
      have hc0 : c ≠ 0 := fun h => by simp [h] at hc
      exact inv_mul_inv_eq_of_eq_mul c ε _ _ hc0 hcε
    rw [e]
    exact integralPS_mul (integralPS_C (by rw [norm_inv, hε, inv_one])) hT

  set α : PowerSeries K := C ε * X with hα
  have hα0 : constantCoeff α = 0 := by rw [hα, map_mul, constantCoeff_X, mul_zero]
  have hαs : PowerSeries.HasSubst α := PowerSeries.HasSubst.of_constantCoeff_zero' hα0
  have hαI : IntegralPS α := integralPS_mul (integralPS_C hε.le) integralPS_X
  set f1 : PowerSeries K := f0.subst α with hf1
  have hf1T : IsFunEqType l (l ^ 2) (σ.comp σ) f1 :=
    isFunEqType_of_mv hq _ _ (Formalism.LT.funEqSubst K l (l ^ 2) hq (σ.comp σ) hS f0 hf00 hf0T Unit α
      hα0 ((integralPS_iff_mv α).1 hαI))
  have hf1e : f1 = ε⁻¹ • PowerSeries.rescale ε lam := by
    rw [hf1, hf0, PowerSeries.subst_smul hαs, PowerSeries.rescale_eq_subst, hα, ← smul_eq_C_mul]
  have hf10 : constantCoeff f1 = 0 := by
    rw [hf1e, ← coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_smul, coeff_rescale,
      coeff_zero_eq_constantCoeff_apply, hlam0]; simp
  have hf11 : coeff 1 f1 = 1 := by
    rw [hf1e, PowerSeries.coeff_smul, coeff_rescale, hlam1, pow_one, mul_one, smul_eq_mul,
      inv_mul_cancel₀ hε0]
  obtain ⟨h, hh0, hhI, hh⟩ := Formalism.LT.funEqHom K l (l ^ 2) (σ.comp σ) hS f1 (ltLog K l) hf10 hf11
    hf1T (ltLog_const l hl2) (ltLog_type hl2 _)
  have hhs : PowerSeries.HasSubst h := PowerSeries.HasSubst.of_constantCoeff_zero' hh0
  have hβ0 : constantCoeff (C ε * h) = 0 := by rw [map_mul, hh0, mul_zero]
  have hβs : PowerSeries.HasSubst (C ε * h) := PowerSeries.HasSubst.of_constantCoeff_zero' hβ0
  have hlams : PowerSeries.HasSubst lam := PowerSeries.HasSubst.of_constantCoeff_zero' hlam0
  have e2 : α.subst h = C ε * h := by
    rw [hα, PowerSeries.subst_mul hhs, PowerSeries.subst_X hhs, PowerSeries.subst_C]; rfl
  have e3 : lam.subst (C ε * h) = C ε * ltLog K l := by
    rw [← hh, hf1, PowerSeries.subst_comp_subst_apply hαs hhs, e2, hf0,
      PowerSeries.subst_smul hβs, smul_eq_C_mul, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hε0,
      map_one, one_mul]
  rw [← e3, ← PowerSeries.subst_comp_subst_apply hlams hβs, hinv, PowerSeries.subst_X hβs]
  exact integralPS_mul (integralPS_C hε.le) hhI

end ReciprocityTheory.ChartRestriction.L1
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.KmuInclDenseRange
section -- merged from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ExistsExtendEndomorphismFractions
section -- merged from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.MuMEvalPowEqZero
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM Polynomial

variable (l : ℕ) [Fact l.Prime]

def muM : Submonoid ℂ_[l] where
  carrier := muP l
  one_mem' := ⟨1, one_pos, fun h => (Fact.out : l.Prime).one_lt.ne' (Nat.dvd_one.1 h), one_pow 1⟩
  mul_mem' := by
    rintro a b ⟨n, hn, hln, ha⟩ ⟨m, hm, hlm, hb⟩
    refine ⟨n * m, Nat.mul_pos hn hm, fun h => ?_, ?_⟩
    · rcases ((Fact.out : l.Prime).dvd_mul).1 h with h | h
      · exact hln h
      · exact hlm h
    · rw [mul_pow, pow_mul, ha, one_pow, mul_comm n m, pow_mul, hb, one_pow, one_mul]

theorem muM_common (S : Finset (muM l)) :
    ∃ n : ℕ, 0 < n ∧ ¬ l ∣ n ∧ ∀ a ∈ S, (a : ℂ_[l]) ^ n = 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_pos, fun h => (Fact.out : l.Prime).one_lt.ne' (Nat.dvd_one.1 h), by simp⟩
  | insert a S _ ih =>
    obtain ⟨n, hn, hln, hS⟩ := ih
    obtain ⟨m, hm, hlm, ha⟩ := a.2
    refine ⟨n * m, Nat.mul_pos hn hm, fun h => ?_, ?_⟩
    · rcases ((Fact.out : l.Prime).dvd_mul).1 h with h | h
      · exact hln h
      · exact hlm h
    · intro b hb
      rcases Finset.mem_insert.1 hb with rfl | hb
      · rw [mul_comm, pow_mul, ha, one_pow]
      · rw [pow_mul, hS b hb, one_pow]

theorem muM_exists_gen (n : ℕ) (hn : 0 < n) :
    ∃ g : ℂ_[l], g ^ n = 1 ∧ ∀ a : ℂ_[l], a ^ n = 1 → ∃ k : ℕ, g ^ k = a := by
  have : NeZero n := ⟨hn.ne'⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_monoid_generator (α := rootsOfUnity n ℂ_[l])
  refine ⟨((g : ℂ_[l]ˣ) : ℂ_[l]), ?_, fun a ha => ?_⟩
  · have := g.2
    rw [mem_rootsOfUnity'] at this
    exact this
  · obtain ⟨k, hk⟩ := hg (rootsOfUnity.mkOfPowEq a ha)
    refine ⟨k, ?_⟩
    have := congrArg (fun x : rootsOfUnity n ℂ_[l] => ((x : ℂ_[l]ˣ) : ℂ_[l])) hk
    simpa using this

theorem muM_eval_pow_eq_zero {K : Type*} [Field K] [CharZero K] (n : ℕ) (hn : 0 < n) (hln : ¬ l ∣ n)
    (g : K) (hg : g ^ n = 1) (p : ℤ[X]) (hp : p.eval₂ (Int.castRingHom K) g = 0) :
    p.eval₂ (Int.castRingHom K) (g ^ l) = 0 := by
  rw [← algebraMap_int_eq, ← aeval_def] at hp ⊢
  have hd : orderOf g ∣ n := orderOf_dvd_of_pow_eq_one hg
  have hd0 : 0 < orderOf g := Nat.pos_of_dvd_of_pos hd hn
  have hprim : IsPrimitiveRoot g (orderOf g) := IsPrimitiveRoot.orderOf g
  have hcop : Nat.Coprime l (orderOf g) :=
    ((Fact.out : l.Prime).coprime_iff_not_dvd).2 fun h => hln (h.trans hd)
  have hdvd : minpoly ℤ g ∣ p := minpoly.isIntegrallyClosed_dvd (hprim.isIntegral hd0) hp
  rw [hprim.minpoly_eq_pow_coprime hcop] at hdvd
  exact aeval_eq_zero_of_dvd_aeval_eq_zero hdvd (minpoly.aeval ℤ (g ^ l))

def phiM : MonoidAlgebra ℤ (muM l) →ₐ[ℤ] ℂ_[l] := MonoidAlgebra.lift ℤ ℂ_[l] (muM l) (muM l).subtype

def psiM : MonoidAlgebra ℤ (muM l) →ₐ[ℤ] ℂ_[l] :=
  MonoidAlgebra.lift ℤ ℂ_[l] (muM l) ((muM l).subtype.comp (powMonoidHom l))

theorem phiM_ker_le (f : MonoidAlgebra ℤ (muM l)) (hf : phiM l f = 0) : psiM l f = 0 := by
  classical
  obtain ⟨n, hn, hln, hS⟩ := muM_common l f.coeff.support
  obtain ⟨g, hg, hgen⟩ := muM_exists_gen l n hn
  have hk : ∀ a : muM l, ∃ k : ℕ, a ∈ f.coeff.support → g ^ k = (a : ℂ_[l]) := by
    intro a
    by_cases ha : a ∈ f.coeff.support
    · obtain ⟨k, hk⟩ := hgen a (hS a ha)
      exact ⟨k, fun _ => hk⟩
    · exact ⟨0, fun h => absurd h ha⟩
  choose k hk using hk
  let p : ℤ[X] := ∑ a ∈ f.coeff.support, C (f.coeff a) * X ^ (k a)
  have h1 : p.eval₂ (Int.castRingHom ℂ_[l]) g = 0 := by
    rw [← hf, phiM, MonoidAlgebra.lift_apply, Finsupp.sum, eval₂_finsetSum]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [eval₂_mul, eval₂_C, eval₂_pow, eval₂_X, hk a ha]
    simp [zsmul_eq_mul]
  have h2 := muM_eval_pow_eq_zero l n hn hln g hg p h1
  rw [← h2, psiM, MonoidAlgebra.lift_apply, Finsupp.sum, eval₂_finsetSum]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [eval₂_mul, eval₂_C, eval₂_pow, eval₂_X, ← pow_mul, mul_comm l, pow_mul, hk a ha]
  simp [zsmul_eq_mul]

theorem phiM_mem (f : MonoidAlgebra ℤ (muM l)) : phiM l f ∈ Rmu l := by
  rw [phiM, MonoidAlgebra.lift_apply]
  exact Subring.sum_mem _ fun a _ => Subring.zsmul_mem _ (Subring.subset_closure a.2) _

theorem psiM_mem (f : MonoidAlgebra ℤ (muM l)) : psiM l f ∈ Rmu l := by
  rw [psiM, MonoidAlgebra.lift_apply]
  exact Subring.sum_mem _ fun a _ => Subring.zsmul_mem _ (Subring.subset_closure (a ^ l).2) _

theorem phiM_surj (x : ℂ_[l]) (hx : x ∈ Rmu l) : ∃ f, phiM l f = x := by
  have : Rmu l ≤ (phiM l : MonoidAlgebra ℤ (muM l) →+* ℂ_[l]).range := by
    refine Subring.closure_le.2 fun ζ hζ => ⟨MonoidAlgebra.single ⟨ζ, hζ⟩ 1, ?_⟩
    simp [phiM]
  exact this hx

theorem rmu_sigma : ∃ s : Rmu l →+* Rmu l,
    ∀ (ζ : ℂ_[l]) (hζ : ζ ∈ muP l), ((s ⟨ζ, Subring.subset_closure hζ⟩ : Rmu l) : ℂ_[l]) = ζ ^ l := by
  let φ : MonoidAlgebra ℤ (muM l) →+* Rmu l :=
    (phiM l : MonoidAlgebra ℤ (muM l) →+* ℂ_[l]).codRestrict (Rmu l) (phiM_mem l)
  let ψ : MonoidAlgebra ℤ (muM l) →+* Rmu l :=
    (psiM l : MonoidAlgebra ℤ (muM l) →+* ℂ_[l]).codRestrict (Rmu l) (psiM_mem l)
  have hφ : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    obtain ⟨f, hf⟩ := phiM_surj l x hx
    exact ⟨f, Subtype.ext hf⟩
  have hker : RingHom.ker φ ≤ RingHom.ker ψ := by
    intro f hf
    rw [RingHom.mem_ker] at hf ⊢
    exact Subtype.ext (phiM_ker_le l f (congrArg Subtype.val hf))
  refine ⟨RingHom.liftOfSurjective φ hφ ⟨ψ, hker⟩, fun ζ hζ => ?_⟩
  have h1 : (⟨ζ, Subring.subset_closure hζ⟩ : Rmu l) = φ (MonoidAlgebra.single ⟨ζ, hζ⟩ 1) :=
    Subtype.ext (by simp [φ, phiM])
  rw [h1, RingHom.liftOfRightInverse_comp_apply]
  simp [ψ, psiM]

theorem rmu_sigma_congr (s : Rmu l →+* Rmu l)
    (hs : ∀ (ζ : ℂ_[l]) (hζ : ζ ∈ muP l),
      ((s ⟨ζ, Subring.subset_closure hζ⟩ : Rmu l) : ℂ_[l]) = ζ ^ l) (x : Rmu l) :
    ∃ r ∈ Rmu l, ((s x : Rmu l) : ℂ_[l]) - (x : ℂ_[l]) ^ l = (l : ℂ_[l]) * r := by
  have hl : l.Prime := Fact.out
  have key : ∀ (y : ℂ_[l]) (hy : y ∈ Rmu l), ∃ r : Rmu l, s ⟨y, hy⟩ - ⟨y, hy⟩ ^ l = (l : Rmu l) * r := by
    intro y hy
    induction hy using Subring.closure_induction with
    | mem ζ hζ => exact ⟨0, Subtype.ext (by simp [hs ζ hζ])⟩
    | zero =>
      refine ⟨0, ?_⟩
      have : (⟨0, zero_mem _⟩ : Rmu l) = 0 := rfl
      rw [this, map_zero, zero_pow hl.ne_zero]; simp
    | one =>
      refine ⟨0, ?_⟩
      have : (⟨1, one_mem _⟩ : Rmu l) = 1 := rfl
      rw [this, map_one, one_pow]; simp
    | add a b ha hb iha ihb =>
      obtain ⟨r, hr⟩ := iha
      obtain ⟨t, ht⟩ := ihb
      obtain ⟨u, hu⟩ := exists_add_pow_prime_eq hl (⟨a, ha⟩ : Rmu l) ⟨b, hb⟩
      refine ⟨r + t - ⟨a, ha⟩ * ⟨b, hb⟩ * u, ?_⟩
      have : (⟨a + b, add_mem ha hb⟩ : Rmu l) = ⟨a, ha⟩ + ⟨b, hb⟩ := rfl
      rw [this, map_add (f := _), hu]
      linear_combination hr + ht
    | neg a ha iha =>
      obtain ⟨r, hr⟩ := iha
      have : (⟨-a, neg_mem ha⟩ : Rmu l) = -⟨a, ha⟩ := rfl
      rw [this, map_neg]
      rcases hl.eq_two_or_odd' with h2 | hodd
      · refine ⟨-r - ⟨a, ha⟩ ^ 2, ?_⟩
        subst h2
        push_cast at hr ⊢
        linear_combination -hr
      · refine ⟨-r, ?_⟩
        rw [hodd.neg_pow]
        linear_combination -hr
    | mul a b ha hb iha ihb =>
      obtain ⟨r, hr⟩ := iha
      obtain ⟨t, ht⟩ := ihb
      refine ⟨r * s ⟨b, hb⟩ + ⟨a, ha⟩ ^ l * t, ?_⟩
      have : (⟨a * b, mul_mem ha hb⟩ : Rmu l) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
      rw [this, map_mul, mul_pow]
      linear_combination s ⟨b, hb⟩ * hr + ⟨a, ha⟩ ^ l * ht
  obtain ⟨r, hr⟩ := key x.1 x.2
  refine ⟨r, r.2, ?_⟩
  have := congrArg (Subtype.val) hr
  simpa using this

end ReciprocityTheory.ChartRestriction.L1
end
end

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM

variable (l : ℕ) [Fact l.Prime]

theorem norm_prime_lt_one_padicField : ‖(l : ℂ_[l])‖ < 1 := by
  rw [norm_l_Cl]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)

theorem norm_prime_pos_padicField : 0 < ‖(l : ℂ_[l])‖ := by
  rw [norm_l_Cl]
  exact inv_pos.mpr (by exact_mod_cast (Fact.out : l.Prime).pos)

theorem frobeniusLift_near_pow (s : Rmu l →+* Rmu l)
    (hs : ∀ (ζ : ℂ_[l]) (hζ : ζ ∈ muP l),
      ((s ⟨ζ, Subring.subset_closure hζ⟩ : Rmu l) : ℂ_[l]) = ζ ^ l) (x : Rmu l) :
    ‖((s x : Rmu l) : ℂ_[l]) - (x : ℂ_[l]) ^ l‖ ≤ ‖(l : ℂ_[l])‖ := by
  obtain ⟨r, hr, h⟩ := rmu_sigma_congr l s hs x
  rw [h, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (rmu_norm_le l hr)

theorem frobeniusLift_norm_one (s : Rmu l →+* Rmu l)
    (hs : ∀ (ζ : ℂ_[l]) (hζ : ζ ∈ muP l),
      ((s ⟨ζ, Subring.subset_closure hζ⟩ : Rmu l) : ℂ_[l]) = ζ ^ l) (x : Rmu l)
    (hx : ‖(x : ℂ_[l])‖ = 1) : ‖((s x : Rmu l) : ℂ_[l])‖ = 1 := by
  have h1 : ‖(x : ℂ_[l]) ^ l‖ = 1 := by rw [norm_pow, hx, one_pow]
  have h2 : ‖((s x : Rmu l) : ℂ_[l]) - (x : ℂ_[l]) ^ l‖ < ‖(x : ℂ_[l]) ^ l‖ := by
    rw [h1]; exact lt_of_le_of_lt (frobeniusLift_near_pow l s hs x) (norm_prime_lt_one_padicField l)
  have h3 := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_lt h2)
  rw [sub_add_cancel, max_eq_right h2.le, h1] at h3
  exact h3

theorem unitBall_eq_frac_normOne {x : ℂ_[l]} (hx : x ∈ Kmu l) (h1 : ‖x‖ ≤ 1) :
    ∃ a ∈ Rmu l, ∃ b ∈ Rmu l, ‖b‖ = 1 ∧ x * b = a := by
  by_cases hx0 : x = 0
  · exact ⟨0, (Rmu l).zero_mem, 1, (Rmu l).one_mem, norm_one, by simp [hx0]⟩
  obtain ⟨m, a, ha, b, hb, hna, hnb, h⟩ := kmu_shape l hx hx0
  have hb0 : b ≠ 0 := by intro h0; rw [h0, norm_zero] at hnb; exact zero_ne_one hnb
  have hn : ‖x‖ = ‖(l : ℂ_[l])‖ ^ m := by
    rw [h, norm_mul, norm_zpow, norm_div, hna, hnb]; simp
  have hm : 0 ≤ m := by
    by_contra hneg
    rw [not_le] at hneg
    have : 1 < ‖(l : ℂ_[l])‖ ^ m :=
      one_lt_zpow_of_neg₀ (norm_prime_pos_padicField l) (norm_prime_lt_one_padicField l) hneg
    rw [← hn] at this
    exact absurd h1 (not_le.mpr this)
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hm
  refine ⟨(l : ℂ_[l]) ^ k * a, (Rmu l).mul_mem ((Rmu l).pow_mem (natCast_mem _ l) k) ha,
    b, hb, hnb, ?_⟩
  rw [h, zpow_natCast]
  field_simp

theorem rmu_sigma_norm (s : Rmu l →+* Rmu l)
    (hs : ∀ (ζ : ℂ_[l]) (hζ : ζ ∈ muP l),
      ((s ⟨ζ, Subring.subset_closure hζ⟩ : Rmu l) : ℂ_[l]) = ζ ^ l) (x : Rmu l) :
    ‖((s x : Rmu l) : ℂ_[l])‖ = ‖(x : ℂ_[l])‖ := by
  by_cases hx0 : x = 0
  · simp [hx0]
  have hx0' : (x : ℂ_[l]) ≠ 0 := fun h => hx0 (Subtype.ext h)
  obtain ⟨m, a, ha, b, hb, hna, hnb, h⟩ := kmu_shape l (rmu_le_kmu l x.2) hx0'
  have hb0 : b ≠ 0 := by intro h0; rw [h0, norm_zero] at hnb; exact zero_ne_one hnb
  have hn : ‖(x : ℂ_[l])‖ = ‖(l : ℂ_[l])‖ ^ m := by
    rw [h, norm_mul, norm_zpow, norm_div, hna, hnb]; simp
  have hm : 0 ≤ m := by
    by_contra hneg
    rw [not_le] at hneg
    have : 1 < ‖(l : ℂ_[l])‖ ^ m :=
      one_lt_zpow_of_neg₀ (norm_prime_pos_padicField l) (norm_prime_lt_one_padicField l) hneg
    rw [← hn] at this
    exact absurd (rmu_norm_le l x.2) (not_le.mpr this)
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hm
  have he : x * (⟨b, hb⟩ : Rmu l) = (l : Rmu l) ^ k * (⟨a, ha⟩ : Rmu l) := by
    apply Subtype.ext
    push_cast
    rw [h, zpow_natCast]
    field_simp
  have hs' := congrArg (fun z : Rmu l => ‖(z : ℂ_[l])‖) (congrArg s he)
  simp only [map_mul, map_pow, map_natCast] at hs'
  push_cast at hs'
  rw [norm_mul, norm_mul, norm_pow, frobeniusLift_norm_one l s hs ⟨b, hb⟩ hnb,
    frobeniusLift_norm_one l s hs ⟨a, ha⟩ hna, mul_one, mul_one] at hs'
  rw [hs', hn, zpow_natCast]

section Generic

variable {K : Type*} [Field K] (R : Subring K) (F : Subfield K) (h : R ≤ F.toSubring)

def subringInclusionSubfield : R →+* F := Subring.inclusion h

theorem subringInclusionSubfield_coe (x : R) : ((subringInclusionSubfield R F h x : F) : K) = (x : K) := rfl

theorem subringInclusionSubfield_injective : Function.Injective (subringInclusionSubfield R F h) := fun x y e =>
  Subtype.ext (by rw [← subringInclusionSubfield_coe R F h, ← subringInclusionSubfield_coe R F h, e])

theorem isFractionRing_subringInclusion (hf : ∀ x ∈ F, ∃ a ∈ R, ∃ b ∈ R, b ≠ 0 ∧ x = a / b) :
    @IsFractionRing R _ F _ (subringInclusionSubfield R F h).toAlgebra := by
  let _ : Algebra R F := (subringInclusionSubfield R F h).toAlgebra
  have : FaithfulSMul R F :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (subringInclusionSubfield_injective R F h)
  apply IsFractionRing.of_field
  intro z
  obtain ⟨a, ha, b, hb, -, e⟩ := hf z z.2
  refine ⟨⟨a, ha⟩, ⟨b, hb⟩, Subtype.ext ?_⟩
  rw [Subfield.coe_div, e]
  rfl

theorem exists_extend_endomorphism_fractions (h : R ≤ F.toSubring) (hf : ∀ x ∈ F, ∃ a ∈ R, ∃ b ∈ R, b ≠ 0 ∧ x = a / b)
    (s : R →+* R) (hsinj : Function.Injective s) :
    ∃ σ : F →+* F, ∀ (x : F) (a b : R), (x : K) * b = a →
      ((σ x : F) : K) * (s b : R) = (s a : R) := by
  let _ : Algebra R F := (subringInclusionSubfield R F h).toAlgebra
  have : IsFractionRing R F := isFractionRing_subringInclusion R F h hf
  have hg : Function.Injective ((subringInclusionSubfield R F h).comp s) := (subringInclusionSubfield_injective R F h).comp hsinj
  have hσ : ∀ x : R, IsFractionRing.lift hg (subringInclusionSubfield R F h x) = subringInclusionSubfield R F h (s x) :=
    fun x => IsFractionRing.lift_algebraMap hg x
  refine ⟨IsFractionRing.lift hg, fun x a b e => ?_⟩
  have h' : x * subringInclusionSubfield R F h b = subringInclusionSubfield R F h a :=
    Subtype.ext (by rw [Subfield.coe_mul, subringInclusionSubfield_coe, subringInclusionSubfield_coe, e])
  have h2 := congrArg (IsFractionRing.lift hg) h'
  rw [map_mul, hσ, hσ] at h2
  rw [← subringInclusionSubfield_coe R F h, ← subringInclusionSubfield_coe R F h, ← Subfield.coe_mul, h2]

end Generic

theorem frobeniusLift_injective (s : Rmu l →+* Rmu l)
    (hs : ∀ (ζ : ℂ_[l]) (hζ : ζ ∈ muP l),
      ((s ⟨ζ, Subring.subset_closure hζ⟩ : Rmu l) : ℂ_[l]) = ζ ^ l) : Function.Injective s := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  have := rmu_sigma_norm l s hs x
  rw [hx, Subring.coe_zero, norm_zero] at this
  exact Subtype.ext (norm_eq_zero.mp this.symm)

theorem norm_unramifiedField_coe (x : Kmu l) : ‖x‖ = ‖(x : ℂ_[l])‖ := rfl

theorem kmu_sigma : ∃ s : Kmu l →+* Kmu l, (∀ x : Kmu l, ‖s x‖ = ‖x‖) ∧
    ∀ x : Kmu l, ‖x‖ ≤ 1 → ‖s x - x ^ l‖ ≤ ‖(l : Kmu l)‖ := by
  obtain ⟨s, hs⟩ := rmu_sigma l
  obtain ⟨σ, key⟩ := exists_extend_endomorphism_fractions (Rmu l) (Kmu l) (fun _ hx => rmu_le_kmu l hx)
    (fun _ hx => kmu_frac l hx) s (frobeniusLift_injective l s hs)
  refine ⟨σ, ?_, ?_⟩
  · intro x
    obtain ⟨a, ha, b, hb, hb0, h⟩ := kmu_frac l x.2
    have h1 : (x : ℂ_[l]) * b = a := by rw [h]; field_simp
    have h2 := key x ⟨a, ha⟩ ⟨b, hb⟩ h1
    have h3 := congrArg norm h2
    have h4 := congrArg norm h1
    rw [norm_mul, rmu_sigma_norm l s hs, rmu_sigma_norm l s hs] at h3
    rw [norm_mul] at h4
    have hb' : ‖b‖ ≠ 0 := norm_ne_zero_iff.mpr hb0
    rw [norm_unramifiedField_coe, norm_unramifiedField_coe]
    exact mul_right_cancel₀ hb' (h3.trans h4.symm)
  · intro x hx
    rw [norm_unramifiedField_coe] at hx
    obtain ⟨a, ha, b, hb, hnb, h1⟩ := unitBall_eq_frac_normOne l x.2 hx
    have h2 := key x ⟨a, ha⟩ ⟨b, hb⟩ h1
    have hsb := frobeniusLift_norm_one l s hs ⟨b, hb⟩ hnb
    have hna := frobeniusLift_near_pow l s hs ⟨a, ha⟩
    have hnb' := frobeniusLift_near_pow l s hs ⟨b, hb⟩
    rw [norm_unramifiedField_coe, norm_unramifiedField_coe, Subfield.coe_sub, SubmonoidClass.coe_pow, SubringClass.coe_natCast]
    generalize ((s ⟨a, ha⟩ : Rmu l) : ℂ_[l]) = sa at h2 hna
    generalize ((s ⟨b, hb⟩ : Rmu l) : ℂ_[l]) = sb at h2 hnb' hsb
    generalize ((σ x : Kmu l) : ℂ_[l]) = y at h2 ⊢
    simp only at hna hnb'
    have e : (y - (x : ℂ_[l]) ^ l) * sb = (sa - a ^ l) + -((x : ℂ_[l]) ^ l * (sb - b ^ l)) := by
      rw [← h1, ← h2]; ring
    have hxl : ‖(x : ℂ_[l]) ^ l‖ ≤ 1 := by
      rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx
    have e2 : ‖(y - (x : ℂ_[l]) ^ l)‖ = ‖(sa - a ^ l) + -((x : ℂ_[l]) ^ l * (sb - b ^ l))‖ := by
      rw [← e, norm_mul, hsb, mul_one]
    rw [e2]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hna ?_)
    rw [norm_neg, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hxl).trans hnb'

end ReciprocityTheory.ChartRestriction.L1
end
end

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM

variable (l : ℕ) [Fact l.Prime]

def kmuIncl : Kmu l →+* MaximalUnramifiedExtension l := Subfield.inclusion (Subfield.le_topologicalClosure (Kmu l))

theorem kmuIncl_norm (x : Kmu l) : ‖kmuIncl l x‖ = ‖x‖ := rfl

theorem kmuIncl_isometry : Isometry (kmuIncl l) :=
  AddMonoidHomClass.isometry_of_norm (kmuIncl l) (fun x => kmuIncl_norm l x)

theorem kmuIncl_denseRange : DenseRange (kmuIncl l) := by
  intro x
  rw [Metric.mem_closure_iff]
  intro e he
  obtain ⟨y, hy, hxy⟩ := kur_approx l x.2 e he
  exact ⟨kmuIncl l ⟨y, hy⟩, ⟨_, rfl⟩, by rw [dist_eq_norm]; exact hxy⟩

theorem kurFrob : ∃ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, FrobField (MaximalUnramifiedExtension l) l σ := by
  obtain ⟨s, hs1, hs2⟩ := kmu_sigma l
  have : CompleteSpace (MaximalUnramifiedExtension l) := kur_complete l
  have hiso : Isometry ((kmuIncl l).comp s) :=
    AddMonoidHomClass.isometry_of_norm _ (fun x => by
      rw [RingHom.comp_apply, kmuIncl_norm, hs1])
  let σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l :=
    IsDenseInducing.extendRingHom (i := kmuIncl l) (f := (kmuIncl l).comp s)
      (kmuIncl_isometry l).isUniformInducing (kmuIncl_denseRange l) hiso.uniformContinuous
  have hdi : IsDenseInducing (kmuIncl l) :=
    (kmuIncl_isometry l).isUniformInducing.isDenseInducing (kmuIncl_denseRange l)
  have hσc : Continuous σ :=
    (uniformContinuous_uniformly_extend (kmuIncl_isometry l).isUniformInducing
      (kmuIncl_denseRange l) hiso.uniformContinuous).continuous
  have hσi : ∀ x : Kmu l, σ (kmuIncl l x) = kmuIncl l (s x) := fun x =>
    hdi.extend_eq hiso.continuous x
  have hl : ‖(l : MaximalUnramifiedExtension l)‖ = ‖(l : ℂ_[l])‖ := rfl
  refine ⟨σ, Fact.out, ?_, ?_, ?_, ?_⟩
  · rw [hl, norm_l_Cl]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  · intro x
    refine (kmuIncl_denseRange l).induction_on (p := fun x => ‖σ x‖ = ‖x‖) x
      (isClosed_eq hσc.norm continuous_norm) (fun y => ?_)
    rw [hσi, kmuIncl_norm, kmuIncl_norm, hs1]
  · intro x hx
    have hopen : IsOpen (Metric.closedBall (0 : MaximalUnramifiedExtension l) 1) :=
      IsUltrametricDist.isOpen_closedBall _ one_ne_zero
    have hmem : x ∈ closure (Metric.closedBall (0 : MaximalUnramifiedExtension l) 1 ∩ Set.range (kmuIncl l)) :=
      (kmuIncl_denseRange l).open_subset_closure_inter hopen (by simpa using hx)
    have hcl : IsClosed {x : MaximalUnramifiedExtension l | ‖σ x - x ^ l‖ ≤ ‖(l : MaximalUnramifiedExtension l)‖} :=
      isClosed_le (hσc.sub (continuous_pow l)).norm continuous_const
    refine closure_minimal ?_ hcl hmem
    rintro _ ⟨hy1, y, rfl⟩
    have hy : ‖y‖ ≤ 1 := by
      rw [mem_closedBall_zero_iff, kmuIncl_norm] at hy1
      exact hy1
    have := hs2 y hy
    show ‖σ (kmuIncl l y) - (kmuIncl l y) ^ l‖ ≤ ‖(l : MaximalUnramifiedExtension l)‖
    rw [hσi, ← map_pow, ← map_sub, kmuIncl_norm]
    exact this
  · intro x hx
    exact kur_discrete l x.2 hx

end ReciprocityTheory.ChartRestriction.L1
end
end

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM

theorem integral_of_map_kur {l : ℕ} [Fact l.Prime] {f : PowerSeries (MaximalUnramifiedExtension l)}
    (h : IntegralPS (PowerSeries.map (MaximalUnramifiedExtension l).subtype f)) : IntegralPS f := fun n => by
  have := h n
  rw [PowerSeries.coeff_map] at this
  exact this

theorem cm3 : CM3 := by
  intro d L _hsq hd hCM l _ hl hld hin ι g2 g3 hg
  obtain ⟨hg2, hg3, hn2, hn3, -, -⟩ := id hg
  have : CompleteSpace (MaximalUnramifiedExtension l) := kur_complete l
  obtain ⟨σ, hσ⟩ := kurFrob l
  have hR := kur_resClosed l
  have hquad : (ι (omegaK d)) ^ 2 - ι (omegaK d) + (((d + 1) / 4 : ℕ) : ℂ_[l]) = 0 := by
    have := congrArg ι (omegaK_quad d hd)
    simpa using this
  obtain ⟨-, ha1, ha', haσ⟩ := kur_quad l d hd (by omega) hld hin _ hquad
  have haσ' := haσ σ hσ
  have h2 : ‖(2 : MaximalUnramifiedExtension l)‖ = 1 := by
    have := norm_natCast_of_coprime (K := MaximalUnramifiedExtension l) hσ.prime hσ.norm_l 2
      (by intro h; have := Nat.le_of_dvd (by norm_num) h; omega)
    simpa using this
  have hlaw := ReciprocityTheory.ChartRestriction.L1.curve_law
    (⟨g2, hg2⟩ : MaximalUnramifiedExtension l) ⟨g3, hg3⟩ hn2 hn3 h2
  have hD : HD σ (lgS (⟨g2, hg2⟩ : MaximalUnramifiedExtension l) ⟨g3, hg3⟩) _
      ((uSer (⟨g2, hg2⟩ : MaximalUnramifiedExtension l) ⟨g3, hg3⟩).subst
        (C (⟨ι (omegaK d), ha'⟩ : MaximalUnramifiedExtension l) * lgS (⟨g2, hg2⟩ : MaximalUnramifiedExtension l) ⟨g3, hg3⟩))
      ⟨ι (omegaK d), ha'⟩ :=
    { toLawD := hlaw
      A0 := mult_const _ _ _
      Aint := integral_of_map_kur (by
        rw [mult_map]
        exact end_integral d L hd hCM l hl hld hin ι g2 g3 hg)
      Alog := mult_log _ _ _
      a_ne := by
        rw [haσ']
        have : ‖((1 - (⟨ι (omegaK d), ha'⟩ : MaximalUnramifiedExtension l) - ⟨ι (omegaK d), ha'⟩ : MaximalUnramifiedExtension l) : ℂ_[l])‖ = 1 := by
          have e : ((1 - (⟨ι (omegaK d), ha'⟩ : MaximalUnramifiedExtension l) - ⟨ι (omegaK d), ha'⟩ : MaximalUnramifiedExtension l) : ℂ_[l])
              = 1 - 2 * ι (omegaK d) := by
            push_cast; ring
          rw [e]; exact ha1
        exact this
      a_sq := by
        rw [haσ', map_sub, map_one, haσ']; ring }
  have he : IntegralPS ((uSer (⟨g2, hg2⟩ : MaximalUnramifiedExtension l) ⟨g3, hg3⟩).subst
      (C ((l : ℕ) : MaximalUnramifiedExtension l) * lgS (⟨g2, hg2⟩ : MaximalUnramifiedExtension l) ⟨g3, hg3⟩)) := by
    obtain ⟨e', h0, hint, hlog⟩ := mulN_integral hlaw l
    rw [← mult_unique _ _ _ e' h0 hlog]
    exact hint
  have hlev : ∃ i, i ≤ l ^ 2 ∧ ‖coeff i ((uSer (⟨g2, hg2⟩ : MaximalUnramifiedExtension l) ⟨g3, hg3⟩).subst
      (C ((l : ℕ) : MaximalUnramifiedExtension l) * lgS (⟨g2, hg2⟩ : MaximalUnramifiedExtension l) ⟨g3, hg3⟩))‖ = 1 := by
    obtain ⟨i, hi, hu⟩ := level_le L l hl ι g2 g3 hg
    refine ⟨i, hi, ?_⟩
    have hm := mult_map (MaximalUnramifiedExtension l).subtype (⟨g2, hg2⟩ : MaximalUnramifiedExtension l) ⟨g3, hg3⟩ ((l : ℕ) : MaximalUnramifiedExtension l)
    have hl' : (MaximalUnramifiedExtension l).subtype ((l : ℕ) : MaximalUnramifiedExtension l) = ((l : ℕ) : ℂ_[l]) := map_natCast _ _
    rw [hl'] at hm
    have hc := congrArg (coeff i) hm
    rw [PowerSeries.coeff_map] at hc
    have : ‖(MaximalUnramifiedExtension l).subtype (coeff i ((uSer (⟨g2, hg2⟩ : MaximalUnramifiedExtension l) ⟨g3, hg3⟩).subst
      (C ((l : ℕ) : MaximalUnramifiedExtension l) * lgS (⟨g2, hg2⟩ : MaximalUnramifiedExtension l) ⟨g3, hg3⟩)))‖ = 1 := by
      rw [hc]; exact hu
    exact this
  obtain ⟨c, hc, hT⟩ := hon_main hσ hD (mult_const _ _ _) he (mult_log _ _ _) hlev
  obtain ⟨ε, hε, hcε⟩ := lang_semilinear hσ hR c hc
  have hfin := fin_integral hσ (uSer (⟨g2, hg2⟩ : MaximalUnramifiedExtension l) ⟨g3, hg3⟩) (lgS (⟨g2, hg2⟩ : MaximalUnramifiedExtension l) ⟨g3, hg3⟩)
    (lgS_const _ _) (lgS_coeff_one _ _) (uSer_const _ _) (uSer_subst_lgS _ _) c ε hc hε hcε hT
  refine ⟨ε, ε.2, hε, fun n => ?_⟩
  have hm := lt_map (MaximalUnramifiedExtension l).subtype (⟨g2, hg2⟩ : MaximalUnramifiedExtension l) ⟨g3, hg3⟩ l (by omega) ε
  have hc' := congrArg (coeff n) hm
  rw [PowerSeries.coeff_map] at hc'
  have hc'' : coeff n ((uSer g2 g3).subst (C (ε : ℂ_[l]) * ltLog ℂ_[l] l))
      = (MaximalUnramifiedExtension l).subtype (coeff n ((uSer (⟨g2, hg2⟩ : MaximalUnramifiedExtension l) ⟨g3, hg3⟩).subst
          (C ε * ltLog (MaximalUnramifiedExtension l) l))) := hc'.symm
  rw [hc'']
  exact ⟨SetLike.coe_mem _, hfin n⟩

end ReciprocityTheory.ChartRestriction.L1
