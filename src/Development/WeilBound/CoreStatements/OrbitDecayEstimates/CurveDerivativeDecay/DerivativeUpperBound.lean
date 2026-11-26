module

public import Development.WeilBound.CoreStatements.OrbitDecayEstimates.CurveDerivativeDecay.HasDerivAtCurve
public import Development.WeilBound.CoreStatements.OrbitDecayEstimates.CurveDerivativeDecay.KFiniteWordBoundIndefUnitary
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.CoefDec
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HeBranching

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.OrbitDecayEstimates.CurveDerivativeDecay.HIntegrability
section -- merged from Development.WeilBound.CoreStatements.OrbitDecayEstimates.CurveDerivativeDecay.IntegrableOfDec
noncomputable section

open Matrix Finset MeasureTheory Formalism.REAL Formalism.MainNotions.S
open scoped InnerProductSpace ENNReal

namespace CompanionTheory.Lime.T3

def nG {m : ℕ} {ε : Fin m → Bool} (g : UJ ε) : ℝ := Real.sqrt (hs (uMat g))

theorem nG_mul {m : ℕ} {ε : Fin m → Bool} (g h : UJ ε) : nG (g * h) ≤ nG g * nG h := sqrt_frobenius_mul_le _ _

theorem one_le_nG {m : ℕ} (hm : 1 ≤ m) {ε : Fin m → Bool} (g : UJ ε) : 1 ≤ nG g :=
  Real.one_le_sqrt.2 (one_le_hsG hm g)

theorem nG_sq {m : ℕ} {ε : Fin m → Bool} (g : UJ ε) : nG g ^ 2 = hs (uMat g) :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity)

theorem nG_inv {m : ℕ} {ε : Fin m → Bool} (g : UJ ε) : nG g⁻¹ = nG g := by
  unfold nG
  rw [uMat_inv, hs_conjJ]

theorem hs_of_compact {m : ℕ} {ε : Fin m → Bool} (hc : ∀ a b, ε a = ε b) (g : UJ ε) : hs (uMat g) = m := by
  have hg : (uMat g)ᴴ * Jm ε * uMat g = Jm ε := g.2
  unfold hs
  rw [Finset.sum_comm]
  have : ∀ j, ∑ i, ‖uMat g i j‖ ^ 2 = 1 := by
    intro j
    have h1 := congrFun (congrFun hg j) j
    simp only [Jm, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] at h1
    have h2 : ∀ i, (if ε i = true then star (uMat g i j) * 1 else star (uMat g i j) * -1) * uMat g i j =
        (if ε j = true then 1 else -1) * ((‖uMat g i j‖ ^ 2 : ℝ) : ℂ) := by
      intro i
      have := Complex.conj_mul' (uMat g i j)
      rw [hc i j]
      split_ifs <;> simp [← this]
    simp only [h2, ← Finset.mul_sum] at h1
    have h3 : (∑ i, ((‖uMat g i j‖ ^ 2 : ℝ) : ℂ)) = 1 := by
      split_ifs at h1
      · simpa using h1
      · linear_combination -h1
    exact_mod_cast h3
  simp [this]

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem dec_low {m N : ℕ} {ε : Fin m → Bool} {lam : Fin m → ℝ} {π : Matrix (Fin m) (Fin m) ℂ → (H →L[ℂ] H)} (hm : 1 ≤ m)
    (hmN : m ≤ N) (hl : Formalism.QuantumDeterminants.IsHCParam lam) (hDS : IsDS ε lam π)
    (hg : Formalism.QuantumDeterminants.GapAtLeast ε lam (200 * (N : ℝ) ^ 3)) {v : H} (hv : v ∈ lowKSub ε lam π) (hv1 : ‖v‖ = 1)
    {A : ℕ} (hA1 : 1 ≤ A) (hA : A ≤ 12 * N ^ 2) (g : UJ ε) :
    ‖⟪v, π (uMat g) v⟫_ℂ‖ ≤ (Real.exp 1 * Real.sqrt m) ^ A * (nG g)⁻¹ ^ A := by
  have : CompleteSpace H := hDS.1
  have hm2 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hN2 : (m : ℝ) ≤ N := by exact_mod_cast hmN
  by_cases hcp : ∀ a b, ε a = ε b
  · have h1 := norm_inner_le_norm (𝕜 := ℂ) v (π (uMat g) v)
    rw [hDS.2.2.1.2.1 _ g.2, hv1, one_mul] at h1
    have h2 : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 (by linarith)
    unfold nG
    rw [hs_of_compact hcp, ← mul_pow, mul_assoc, mul_inv_cancel₀ h2.ne', mul_one]
    exact h1.trans (one_le_pow₀ (Real.one_le_exp zero_le_one))
  have hpq' : (∃ a, ε a = true) ∧ ∃ a, ε a = false := by
    push_neg at hcp
    obtain ⟨a, b, hab⟩ := hcp
    cases ha : ε a <;> cases hb : ε b <;> simp_all <;> exact ⟨⟨_, ‹_›⟩, ⟨_, ‹_›⟩⟩
  obtain ⟨hp, hq⟩ := hpq'
  set h : ℝ := 200 * (N : ℝ) ^ 3 with hh
  have hN3 : (m : ℝ) ^ 3 ≤ N ^ 3 := pow_le_pow_left₀ (by linarith) hN2 3
  have hm3 : (1 : ℝ) ≤ m ^ 3 := one_le_pow₀ hm2
  have hpm : (ReciprocityTheory.ChartRestriction.DS.pOf ε : ℝ) ≤ m := by
    exact_mod_cast (Finset.card_filter_le _ _).trans_eq (Finset.card_fin m)
  have hqm : (ReciprocityTheory.ChartRestriction.DS.qOf ε : ℝ) ≤ m := by
    exact_mod_cast (Finset.card_filter_le _ _).trans_eq (Finset.card_fin m)
  have hq1 : 1 ≤ ReciprocityTheory.ChartRestriction.DS.S7.q0 ε := by
    obtain ⟨a, ha⟩ := hp
    obtain ⟨b, hb⟩ := hq
    exact le_min (Finset.card_pos.2 ⟨a, by simp [ha]⟩) (Finset.card_pos.2 ⟨b, by simp [hb]⟩)
  have hq0 : (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ) ≤ m := le_trans (by exact_mod_cast min_le_left _ _) hpm
  have hq1' : (1 : ℝ) ≤ ReciprocityTheory.ChartRestriction.DS.S7.q0 ε := by exact_mod_cast hq1
  have hmm : (m : ℝ) ^ 2 ≤ m ^ 3 := by nlinarith
  have hpq : (ReciprocityTheory.ChartRestriction.DS.pOf ε : ℝ) * ReciprocityTheory.ChartRestriction.DS.qOf ε ≤ m * m :=
    mul_le_mul hpm hqm (Nat.cast_nonneg _) (by linarith)
  obtain ⟨k, X, hX, e⟩ := ReciprocityTheory.ChartRestriction.DS.S7.polar_exists (ε := ε) (g := uMat g) g.2
  have hd := ReciprocityTheory.ChartRestriction.DS.coef_dec_of_isDS hDS hl hg hq1 (by nlinarith) (by nlinarith) ⟨hv1, hv⟩ k hX
  rw [← e] at hd
  set c := Real.sqrt (2 * (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ)) with hc
  have hc1 : 1 ≤ c := Real.one_le_sqrt.2 (by linarith)
  have hcm : c ≤ 2 * N := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
  set s := Real.sqrt (ReciprocityTheory.ChartRestriction.DS.S7.hs X) with hs_def
  have hsX : ReciprocityTheory.ChartRestriction.DS.S7.hs X = s ^ 2 := (Real.sq_sqrt (ReciprocityTheory.ChartRestriction.DS.S7.hs_nonnegVG X)).symm
  have hG1 := one_le_nG hm g
  have hN : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 (by linarith)
  have hGle : nG g ≤ Real.sqrt m * Real.exp s := by
    unfold nG
    rw [e]
    change Real.sqrt (ReciprocityTheory.ChartRestriction.DS.S7.hs _) ≤ _
    rw [ReciprocityTheory.ChartRestriction.DS.S7.hs_kmulVG, Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have e2 : Real.exp s ^ 2 = Real.exp (2 * s) := by rw [← Real.exp_nat_mul]; norm_num
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg m), e2]
    exact ReciprocityTheory.ChartRestriction.DS.S7.hs_exp_leVG X
  have hA' : (A : ℝ) ≤ 12 * N ^ 2 := by exact_mod_cast hA
  have hA1' : (1 : ℝ) ≤ A := by exact_mod_cast hA1
  have hr := ReciprocityTheory.ChartRestriction.DS.sigZeroDecay_real (h := 8 * c * A) (s := s) (by positivity) hc1 hN (by linarith) hGle
  rw [show 8 * c * A / (8 * c) = (A : ℝ) by field_simp, Real.rpow_neg (by linarith), Real.rpow_natCast,
    Real.rpow_natCast, ← inv_pow] at hr
  rw [hsX] at hd
  have hmin : 0 ≤ min (s ^ 2) (s / c) := le_min (by positivity) (by positivity)
  have hle : 8 * c * A ≤ h := by
    have : c * A ≤ (2 * N) * (12 * N ^ 2) := mul_le_mul hcm hA' (by linarith) (by linarith)
    nlinarith
  refine hd.trans ((Real.exp_le_exp.2 (by nlinarith)).trans (hr.trans (le_of_eq ?_)))
  rw [show Real.exp (A : ℝ) = Real.exp 1 ^ A by rw [← Real.exp_nat_mul, mul_one], ← mul_pow]

theorem dec_conj {m : ℕ} {ε : Fin m → Bool} {π : Matrix (Fin m) (Fin m) ℂ → (H →L[ℂ] H)} (hm : 1 ≤ m)
    (hπ : IsURepOn (UJset ε) π) {v : H} {C : ℝ} (hC : 0 ≤ C) {A : ℕ}
    (hd : ∀ g : UJ ε, ‖⟪v, π (uMat g) v⟫_ℂ‖ ≤ C * (nG g)⁻¹ ^ A) (g₀ g : UJ ε) :
    ‖⟪π (uMat g₀) v, π (uMat g) (π (uMat g₀) v)⟫_ℂ‖ ≤ C * hs (uMat g₀) ^ A * (nG g)⁻¹ ^ A := by
  let U : H →ₗᵢ[ℂ] H := ⟨(π (uMat g₀)).toLinearMap, hπ.2.1 _ g₀.2⟩
  have e : π (uMat g) (π (uMat g₀) v) = π (uMat g₀) (π (uMat (g₀⁻¹ * g * g₀)) v) := by
    have h1 := hπ.1.2 (uMat g) g.2 (uMat g₀) g₀.2
    have h2 := hπ.1.2 (uMat g₀) g₀.2 (uMat (g₀⁻¹ * g * g₀)) (g₀⁻¹ * g * g₀).2
    have h3 : uMat g₀ * uMat (g₀⁻¹ * g * g₀) = uMat g * uMat g₀ := by
      change uMat (g₀ * (g₀⁻¹ * g * g₀)) = uMat (g * g₀)
      congr 1
      group
    rw [← ContinuousLinearMap.comp_apply, ← h1, ← h3, h2, ContinuousLinearMap.comp_apply]
  have e2 := U.inner_map_map v (π (uMat (g₀⁻¹ * g * g₀)) v)
  rw [e]
  change ‖⟪U v, U _⟫_ℂ‖ ≤ _
  rw [e2]
  refine (hd _).trans ?_
  rw [mul_assoc C, ← mul_pow]
  refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by unfold nG; positivity) ?_ A) hC
  have h1 : nG g ≤ nG g₀ * nG (g₀⁻¹ * g * g₀) * nG g₀ := by
    calc nG g = nG (g₀ * (g₀⁻¹ * g * g₀) * g₀⁻¹) := by congr 1; group
      _ ≤ nG (g₀ * (g₀⁻¹ * g * g₀)) * nG g₀⁻¹ := nG_mul _ _
      _ ≤ _ := by rw [nG_inv]; exact mul_le_mul_of_nonneg_right (nG_mul _ _) (by unfold nG; positivity)
  have h2 := one_le_nG hm g
  have h3 := one_le_nG hm (g₀⁻¹ * g * g₀)
  rw [← nG_sq, ← div_eq_mul_inv, le_div_iff₀ (by linarith), inv_mul_le_iff₀ (by linarith)]
  nlinarith

theorem nearSet_lt_top {m : ℕ} (ε : Fin m → Bool) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] : μ (nearSet ε 1) < ⊤ := by
  have hc : IsCompact {g : UJ ε | hsG g ≤ (Real.sqrt m + 1) ^ 2} := by
    have := (isClosedEmbeddingMatrix m ε).1.isCompact_preimage ((hermitian_small_ball m ε).1 ((Real.sqrt m + 1) ^ 2))
    convert this using 1
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, hsG]
    exact ⟨fun h => ⟨g.2, h⟩, fun h => h.2⟩
  refine (measure_mono fun g hg => ?_).trans_lt hc.measure_lt_top
  have h1 := sqrt_frobenius_add_le (1 : Matrix (Fin m) (Fin m) ℂ) (coeMatrixAlt ε g - 1)
  rw [add_sub_cancel, f1auxiliary_hs_one] at h1
  have h2 : Real.sqrt (hs (coeMatrixAlt ε g - 1)) ≤ 1 := Real.sqrt_le_iff.2 ⟨zero_le_one, hg⟩
  show hs (coeMatrixAlt ε g) ≤ _
  rw [← Real.sqrt_le_left (by positivity)]
  linarith

theorem integrable_of_dec {m : ℕ} {ε : Fin m → Bool} (hm : 1 ≤ m) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] {f : UJ ε → ℂ}
    (hf : Continuous f) {C : ℝ} (hC : 0 ≤ C) {A : ℕ} (hA : 2 * m ^ 2 + 1 ≤ A) (hd : ∀ g, ‖f g‖ ≤ C * (nG g)⁻¹ ^ A) :
    Integrable f μ := by
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  have h1 := int_ratio hm ε μ one_pos (by norm_num) hA
  calc ∫⁻ g, ‖f g‖ₑ ∂μ ≤ ∫⁻ g, ENNReal.ofReal C * ENNReal.ofReal ((Real.sqrt (hsG g))⁻¹ ^ A) ∂μ := by
        refine lintegral_mono fun g => ?_
        rw [← ofReal_norm, ← ENNReal.ofReal_mul hC]
        exact ENNReal.ofReal_le_ofReal (hd g)
    _ = ENNReal.ofReal C * ∫⁻ g, ENNReal.ofReal ((Real.sqrt (hsG g))⁻¹ ^ A) ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (h1.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (nearSet_lt_top ε μ)))

end CompanionTheory.Lime.T3
end
end

section -- merged from Development.WeilBound.CoreStatements.OrbitDecayEstimates.CurveDerivativeDecay.OrbitDeriv
noncomputable section

open Matrix Finset MeasureTheory Formalism.REAL Formalism.MainNotions.S Filter Topology
open scoped InnerProductSpace ENNReal

namespace CompanionTheory.Lime.T3

open ReciprocityTheory.ChartRestriction.DS (smD smE actM dS IsSmoothVecU mem_smD_iff isDerivedOn_smE dS_eq_actM)

theorem interp {f f' : ℝ → ℂ} (hf : ∀ s, HasDerivAt f (f' s) s) {M η τ a : ℝ} (hM : 0 ≤ M)
    (hL : ∀ s t, ‖f' s - f' t‖ ≤ M * |s - t|) (hη : ∀ s ∈ Set.Icc (0 : ℝ) 2, ‖f s‖ ≤ η) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (ha : a ∈ Set.Icc (0 : ℝ) 1) : ‖f a - f 0‖ ≤ (2 * η / τ + M * τ) * a := by
  obtain ⟨ha0, ha1⟩ := ha
  have key : ∀ s ∈ Set.Icc (0:ℝ) 1, ‖f' s‖ ≤ 2 * η / τ + M * τ := by
    intro s hs
    obtain ⟨hs0, hs1⟩ := hs
    have hg : ∀ t ∈ Set.Icc (0:ℝ) τ, HasDerivWithinAt (fun t : ℝ => f (s + t) - (t : ℂ) * f' s)
        (f' (s + t) - f' s) (Set.Icc 0 τ) t := by
      intro t _
      have h1 : HasDerivAt (fun t : ℝ => f (s + t)) (f' (s + t)) t := by
        have := (hf (s + t)).scomp t ((hasDerivAt_id' t).const_add s)
        simpa [Function.comp_def] using this
      have h2 : HasDerivAt (fun t : ℝ => (t : ℂ) * f' s) (f' s) t := by
        have := (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const (f' s)
        simpa using this
      exact (h1.sub h2).hasDerivWithinAt
    have hb : ∀ t ∈ Set.Ico (0:ℝ) τ, ‖f' (s + t) - f' s‖ ≤ M * τ := by
      intro t ht
      calc ‖f' (s + t) - f' s‖ ≤ M * |s + t - s| := hL _ _
        _ ≤ M * τ := by
          apply mul_le_mul_of_nonneg_left _ hM
          rw [add_sub_cancel_left, abs_of_nonneg ht.1]
          exact ht.2.le
    have hmv := norm_image_sub_le_of_norm_deriv_le_segment' hg hb τ ⟨hτ.le, le_rfl⟩
    simp only [Complex.ofReal_zero, zero_mul, sub_zero, add_zero] at hmv
    have e1 := hη (s + τ) ⟨by linarith, by linarith⟩
    have e2 := hη s ⟨hs0, by linarith⟩
    have htri : ‖(τ : ℂ) * f' s‖ ≤ ‖f (s + τ) - (τ:ℂ) * f' s - f s‖ + ‖f (s + τ)‖ + ‖f s‖ := by
      calc ‖(τ : ℂ) * f' s‖ = ‖-(f (s + τ) - (τ:ℂ) * f' s - f s) + f (s + τ) - f s‖ := by
            congr 1
            ring
        _ ≤ ‖-(f (s + τ) - (τ:ℂ) * f' s - f s) + f (s + τ)‖ + ‖f s‖ := norm_sub_le _ _
        _ ≤ ‖-(f (s + τ) - (τ:ℂ) * f' s - f s)‖ + ‖f (s + τ)‖ + ‖f s‖ := by
          gcongr
          exact norm_add_le _ _
        _ = _ := by rw [norm_neg]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hτ.le] at htri
    rw [div_add' _ _ _ hτ.ne', le_div_iff₀ hτ]
    nlinarith
  have hg2 : ∀ x ∈ Set.Icc (0:ℝ) a, HasDerivWithinAt f (f' x) (Set.Icc 0 a) x :=
    fun x _ => (hf x).hasDerivWithinAt
  have hb2 : ∀ x ∈ Set.Ico (0:ℝ) a, ‖f' x‖ ≤ 2 * η / τ + M * τ :=
    fun x hx => key x ⟨hx.1, by linarith [hx.2]⟩
  have hfin := norm_image_sub_le_of_norm_deriv_le_segment' hg2 hb2 a ⟨ha0, le_rfl⟩
  simpa using hfin

variable {m : ℕ} {ε : Fin m → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {π : Matrix (Fin m) (Fin m) ℂ → (H →L[ℂ] H)}

theorem orbit_deriv (hπ : IsURepOn (UJset ε) π) (x : smD ε π) {c : ℝ → UJ ε} {Z : Matrix (Fin m) (Fin m) ℂ}
    (h0 : c 0 = 1) (hadd : ∀ s t, c (s + t) = c s * c t) (hc : HasDerivAt (fun t => uMat (c t)) Z 0) (s : ℝ) :
    HasDerivAt (fun t : ℝ => π (uMat (c t)) (x : H)) (π (uMat (c s)) (actM (smE ε π) Z x : smD ε π)) s := by
  have mem : ∀ h : UJ ε, uMat h ∈ UJset ε := fun h => h.2
  have hu0 : uMat (c 0) = 1 := by
    rw [h0]
    rfl
  have hd0 : HasDerivAt (fun t : ℝ => π (uMat (c t)) (x : H)) (actM (smE ε π) Z x : smD ε π) 0 := by
    have hev : ∀ᶠ t : ℝ in 𝓝 0, inUJ ε (uMat (c t)) := Filter.Eventually.of_forall fun t => (c t).2
    have h1 := hasDerivAt_curve hπ x.2 hu0 hc hev
    rwa [dS_eq_actM (isDerivedOn_smE hπ) (inG_of_curve hu0 hc hev) x] at h1
  set L := π (uMat (c s)) with hL
  have h4 : HasDerivAt (fun t : ℝ => π (uMat (c t)) (x : H)) (actM (smE ε π) Z x : smD ε π) (s - s) := by
    rw [sub_self]
    exact hd0
  have h2 : HasDerivAt (fun t : ℝ => L (π (uMat (c (t - s))) (x : H)))
      (L (actM (smE ε π) Z x : smD ε π)) s := by
    have h3 := (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (s - s) h4
    exact h3.comp_sub_const s s
  convert h2 using 1
  funext t
  have e : c t = c s * c (t - s) := by
    rw [← hadd]
    congr 1
    ring
  show π (uMat (c t)) (x : H) = L (π (uMat (c (t - s))) x)
  rw [e, show uMat (c s * c (t - s)) = uMat (c s) * uMat (c (t - s)) from rfl,
    hπ.1.2 _ (mem _) _ (mem _)]
  rfl

theorem coef_interp (hπ : IsURepOn (UJset ε) π) (x : smD ε π) {c : ℝ → UJ ε} {Z : Matrix (Fin m) (Fin m) ℂ}
    (h0 : c 0 = 1) (hadd : ∀ s t, c (s + t) = c s * c t) (hc : HasDerivAt (fun t => uMat (c t)) Z 0) {u : H}
    (hu : ‖u‖ ≤ 1) {M η τ a : ℝ} (hM : ‖actM (smE ε π) Z (actM (smE ε π) Z x)‖ ≤ M)
    (hη : ∀ s ∈ Set.Icc (0 : ℝ) 2, ‖⟪π (uMat (c s)) (x : H), u⟫_ℂ‖ ≤ η) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    ‖⟪π (uMat (c a)) (x : H), u⟫_ℂ - ⟪π (uMat (c 0)) (x : H), u⟫_ℂ‖ ≤ (2 * η / τ + M * τ) * a := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans hM
  set y : smD ε π := actM (smE ε π) Z x with hy
  have hF : ∀ s, HasDerivAt (fun t : ℝ => π (uMat (c t)) (x : H)) (π (uMat (c s)) (y : H)) s :=
    orbit_deriv hπ x h0 hadd hc
  have hG : ∀ s, HasDerivAt (fun t : ℝ => π (uMat (c t)) (y : H))
      (π (uMat (c s)) (actM (smE ε π) Z y : H)) s :=
    orbit_deriv hπ y h0 hadd hc
  have hf : ∀ s, HasDerivAt (fun t : ℝ => ⟪π (uMat (c t)) (x : H), u⟫_ℂ)
      ⟪π (uMat (c s)) (y : H), u⟫_ℂ s := by
    intro s
    have h1 := (hF s).inner ℂ (hasDerivAt_const s u)
    simpa using h1
  have hL : ∀ s t, ‖⟪π (uMat (c s)) (y : H), u⟫_ℂ - ⟪π (uMat (c t)) (y : H), u⟫_ℂ‖ ≤ M * |s - t| := by
    intro s t
    rw [← inner_sub_left]
    have hmv : ‖π (uMat (c s)) (y : H) - π (uMat (c t)) (y : H)‖ ≤ M * ‖s - t‖ := by
      apply Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (fun r _ => (hG r).hasDerivWithinAt) _
        convex_univ (Set.mem_univ _) (Set.mem_univ _)
      intro r _
      rw [hπ.2.1 _ (c r).2 _]
      exact hM
    rw [Real.norm_eq_abs] at hmv
    calc _ ≤ ‖π (uMat (c s)) (y : H) - π (uMat (c t)) (y : H)‖ * ‖u‖ := norm_inner_le_norm _ _
      _ ≤ M * |s - t| * 1 := mul_le_mul hmv hu (norm_nonneg _) (mul_nonneg hM0 (abs_nonneg _))
      _ = M * |s - t| := mul_one _
  exact interp hf hM0 hL hη hτ hτ1 ha

theorem inner_move (hπ : IsURepOn (UJset ε) π) (g k : UJ ε) (a b : H) :
    ⟪π (uMat g) a, π (uMat k) b⟫_ℂ = ⟪a, π (uMat (g⁻¹ * k)) b⟫_ℂ := by
  have mem : ∀ h : UJ ε, uMat h ∈ UJset ε := fun h => h.2
  have hk : uMat k = uMat g * uMat (g⁻¹ * k) := by
    have e : k = g * (g⁻¹ * k) := (mul_inv_cancel_left g k).symm
    conv_lhs => rw [e]
    rfl
  rw [hk, hπ.1.2 _ (mem g) _ (mem _), ContinuousLinearMap.comp_apply]
  let L : H →ₗᵢ[ℂ] H := { toLinearMap := (π (uMat g)).toLinearMap, norm_map' := hπ.2.1 _ (mem g) }
  exact L.inner_map_map a _

theorem low_bounds {lam : Fin m → ℝ} {B : ℝ} (hm : 2 ≤ m) (hl : Formalism.QuantumDeterminants.IsHCParam lam) (hDS : IsDS ε lam π)
    (hB : ∀ a, |lam a| ≤ B) (hg : Formalism.QuantumDeterminants.GapAtLeast ε lam (100 * (m : ℝ) ^ 3)) {v : H} (hv : v ∈ lowKSub ε lam π)
    (hv1 : ‖v‖ = 1) : ∃ x : smD ε π, (x : H) = v ∧ (∀ X, hs X ≤ 1 → ‖actM (smE ε π) X x‖ ≤ 8 * Real.sqrt m * (B + 2)) ∧
      ∀ Z, ‖actM (smE ε π) Z (actM (smE ε π) Z x)‖ ≤ hs Z * (8 * Real.sqrt m * (B + 2)) ^ 2 := by
  obtain ⟨hv_s, hW⟩ := kFiniteWordBound_indefUnitary m ε lam B H π hm hl hDS hB hg v hv
  have hπ : IsURepOn (UJset ε) π := hDS.2.2.1
  have hsm : v ∈ smD ε π := by
    rw [mem_smD_iff]
    intro g₀ hg₀
    obtain ⟨U, F, hU, hgU, hF, hfe⟩ := hv_s g₀ hg₀
    exact ⟨U, F, hU, hgU, hF, fun g hg hgi => hfe g hg hgi⟩
  set x : smD ε π := ⟨v, hsm⟩ with hx
  have hC : ∀ W : List (Matrix (Fin m) (Fin m) ℂ), W.length ≤ 2 → (∀ X ∈ W, hs X ≤ 1) →
      ‖PI.DSInfCharCap.dsigCW ε π W v‖ ≤ (8 * Real.sqrt m * (B + 2)) ^ W.length := by
    intro W hl1 hX
    have h := hW 2 W hl1 hX
    rw [hv1, mul_one] at h
    simpa using h
  have one : ∀ X, hs X ≤ 1 → ‖actM (smE ε π) X x‖ ≤ 8 * Real.sqrt m * (B + 2) := by
    intro X hX
    have h := hC [X] (by simp) (by simpa using hX)
    have e : PI.DSInfCharCap.dsigCW ε π [X] v = (actM (smE ε π) X x : H) := dsigC_eq_actM hπ X x
    rw [e] at h
    simpa using h
  have two : ∀ X, hs X ≤ 1 →
      ‖actM (smE ε π) X (actM (smE ε π) X x)‖ ≤ (8 * Real.sqrt m * (B + 2)) ^ 2 := by
    intro X hX
    have h := hC [X, X] (by simp) (by simp [hX])
    have e : PI.DSInfCharCap.dsigCW ε π [X, X] v = (actM (smE ε π) X (actM (smE ε π) X x) : H) := by
      show PI.DSInfCharCap.dsigC ε π X (PI.DSInfCharCap.dsigC ε π X (x : H)) = _
      rw [dsigC_eq_actM hπ X x, dsigC_eq_actM hπ X]
    rw [e] at h
    simpa using h
  refine ⟨x, rfl, one, ?_⟩
  intro Z
  have hnn : 0 ≤ hs Z := by
    unfold hs
    positivity
  rcases hnn.eq_or_lt with h0 | hpos
  · have hZ0 : Z = 0 := eq_zero_of_hs h0.symm
    subst hZ0
    have hz := actM_smul (actM (smE ε π) 0 x) 0 (0 : Matrix (Fin m) (Fin m) ℂ)
    simp only [Complex.ofReal_zero, zero_smul] at hz
    rw [hz, ← h0]
    simp
  · set a := (Real.sqrt (hs Z))⁻¹ with ha
    have hsq : Real.sqrt (hs Z) ^ 2 = hs Z := Real.sq_sqrt hpos.le
    have hspos : 0 < Real.sqrt (hs Z) := Real.sqrt_pos.mpr hpos
    have ha0 : 0 ≤ a := by positivity
    have ha2 : a * a * hs Z = 1 := by
      rw [ha, ← sq, inv_pow, hsq, inv_mul_cancel₀ hpos.ne']
    have hY : hs ((a : ℂ) • Z) ≤ 1 := by
      rw [hs_smul, ← ha2, sq]
    have h := two _ hY
    rw [actM_smul, actM_smul, map_smul, norm_smul, norm_smul, Complex.norm_real,
      Real.norm_of_nonneg ha0] at h
    have hw0 := norm_nonneg (actM (smE ε π) Z (actM (smE ε π) Z x))
    nlinarith [mul_le_mul_of_nonneg_left h hpos.le]

end CompanionTheory.Lime.T3
end
end

noncomputable section

open Matrix Finset MeasureTheory Formalism.REAL Formalism.MainNotions.S Filter Topology GlobalTheory.CompanionTheory.PairingAnalysis
open scoped InnerProductSpace ENNReal

namespace CompanionTheory.Lime.T3

variable {n : ℕ} {ε : Fin (n + 1) → Bool} {ε' : Fin n → Bool} {e : Fin n ⊕ Unit ≃ Fin (n + 1)}

theorem emb_mul (a b : Matrix (Fin n) (Fin n) ℂ) : emb e (a * b) = emb e a * emb e b := by
  simp [emb, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem emb_one : emb e (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  simp [emb, Matrix.fromBlocks_one]

theorem emb_conjT (a : Matrix (Fin n) (Fin n) ℂ) : (emb e a)ᴴ = emb e aᴴ := by
  simp [emb, Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.fromBlocks_conjTranspose]

theorem emb_J (hF : Fits ε ε' e) : emb e (Jm ε') = Jm ε := by
  ext i j
  obtain ⟨i, rfl⟩ := e.surjective i
  obtain ⟨j, rfl⟩ := e.surjective j
  have h1 : ε (e (Sum.inr ())) = true := hF.1
  rcases i with i | i <;> rcases j with j | j <;> simp [emb, Jm, Matrix.diagonal_apply, hF.2, h1]

theorem hs_block (a : Matrix (Fin n) (Fin n) ℂ) (d : Matrix Unit Unit ℂ) :
    hs (Matrix.reindex e e (Matrix.fromBlocks a 0 0 d)) = hs a + ‖d () ()‖ ^ 2 := by
  unfold hs
  rw [← e.sum_comp]
  simp_rw [← e.sum_comp (fun j => ‖Matrix.reindex e e (Matrix.fromBlocks a 0 0 d) _ j‖ ^ 2)]
  simp [Fintype.sum_sum_type]

theorem col_emb (g : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (a : Matrix (Fin n) (Fin n) ℂ) :
    colSq (g * emb e a) (zi e) = colSq g (zi e) := by
  unfold colSq
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_apply, ← e.sum_comp]
  simp [emb, zi, Fintype.sum_sum_type]

def embG (hF : Fits ε ε' e) : UJ ε' →* UJ ε where
  toFun h := ⟨⟨emb e (uMat h), emb e (uMat h⁻¹), by rw [← emb_mul, ← emb_one (e := e)]; congr 1; exact determinant_character_mul_inv h,
      by rw [← emb_mul, ← emb_one (e := e)]; congr 1; exact (show (h : (Matrix (Fin n) (Fin n) ℂ)ˣ)⁻¹.1 * _ = 1 from Units.inv_mul _)⟩, by
    have hh : (uMat h)ᴴ * Jm ε' * uMat h = Jm ε' := h.2
    show (emb e (uMat h))ᴴ * Jm ε * emb e (uMat h) = Jm ε
    rw [← emb_J hF, emb_conjT, ← emb_mul, ← emb_mul, hh]⟩
  map_one' := Subtype.ext (Units.ext emb_one)
  map_mul' a b := Subtype.ext (Units.ext (emb_mul _ _))

theorem uMat_embG (hF : Fits ε ε' e) (h : UJ ε') : uMat (embG hF h) = emb e (uMat h) := rfl

theorem nG_le_embG (hF : Fits ε ε' e) (h : UJ ε') : nG h ≤ nG (embG hF h) := by
  unfold nG
  rw [uMat_embG, emb, hs_block]
  exact Real.sqrt_le_sqrt (le_add_of_nonneg_right (by positivity))

theorem colSq_le_hs {m : ℕ} (g : Matrix (Fin m) (Fin m) ℂ) (j : Fin m) : colSq g j ≤ hs g :=
  Finset.sum_le_sum fun i _ =>
    Finset.single_le_sum (f := fun k => ‖g i k‖ ^ 2) (fun k _ => by positivity) (Finset.mem_univ j)

theorem colSq_pos {m : ℕ} {η : Fin m → Bool} (g : UJ η) (j : Fin m) : 0 < colSq (uMat g) j := by
  by_contra h
  have h0 : colSq (uMat g) j = 0 := le_antisymm (not_lt.1 h) (Finset.sum_nonneg fun _ _ => by positivity)
  have h1 : ∀ i, uMat g i j = 0 := fun i => by
    have := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => by positivity).1 h0 i (Finset.mem_univ i)
    simpa using this
  have h2 : uMat g⁻¹ * uMat g = 1 := Units.inv_mul (g : (Matrix (Fin m) (Fin m) ℂ)ˣ)
  have h3 := congrFun (congrFun h2 j) j
  simp [Matrix.mul_apply, h1] at h3

theorem rpow_hs {m : ℕ} (hm : 1 ≤ m) {η : Fin m → Bool} (g : UJ η) (k : ℕ) {a : ℝ} (ha : (k : ℝ) ≤ 2 * a) :
    hs (uMat g) ^ (-a) ≤ (nG g)⁻¹ ^ k := by
  have h1 := one_le_nG hm g
  rw [← nG_sq, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith), inv_pow, ← Real.rpow_natCast,
    ← Real.rpow_neg (by linarith)]
  exact Real.rpow_le_rpow_of_exponent_le h1 (by push_cast; linarith)

theorem lint_le {m : ℕ} (hm : 1 ≤ m) {η : Fin m → Bool} (μ : Measure (UJ η)) [μ.IsHaarMeasure] {f : UJ η → ℂ} {C δ : ℝ}
    (hC : 0 ≤ C) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hd : ∀ g, ‖f g‖ ≤ C * (nG g)⁻¹ ^ (2 * m ^ 2 + 1)) :
    ∫⁻ g, ‖f g‖ₑ ∂μ ≤ ENNReal.ofReal (C * (2 * (16 * (m : ℝ) ^ 2 / δ) ^ (2 * m ^ 2))) * μ (nearSet η δ) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hsq : Real.sqrt m ≤ m := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
  calc ∫⁻ g, ‖f g‖ₑ ∂μ ≤ ∫⁻ g, ENNReal.ofReal C * ENNReal.ofReal ((Real.sqrt (hsG g))⁻¹ ^ (2 * m ^ 2 + 1)) ∂μ := by
        refine lintegral_mono fun g => ?_
        rw [← ofReal_norm, ← ENNReal.ofReal_mul hC]
        exact ENNReal.ofReal_le_ofReal (hd g)
    _ = ENNReal.ofReal C * ∫⁻ g, ENNReal.ofReal ((Real.sqrt (hsG g))⁻¹ ^ (2 * m ^ 2 + 1)) ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal (2 * (16 * (m : ℝ) ^ 2 / δ) ^ (2 * m ^ 2)) * μ (nearSet η δ)) := by
        refine mul_le_mul_right ((int_ratio hm η μ hδ (by linarith) le_rfl).trans (mul_le_mul_left ?_ _)) _
        refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ _) zero_le_two)
        exact div_le_div_of_nonneg_right (by nlinarith) hδ.le
    _ = _ := by rw [← mul_assoc, ← ENNReal.ofReal_mul hC]

theorem h_integrability : HInt := by
  intro n ε ε' e ν hν hF hn φ C δ hC hδ hδ1 hd g
  set b : ℕ := 2 * n ^ 2 + 1 with hb
  set a : ℕ := 2 * (n + 1) + 5 with ha
  have hn1 : 1 ≤ n + 1 := by omega
  have hbd : BddBelow (Set.range fun h => nG (g * embG hF h)) := ⟨1, by rintro _ ⟨h, rfl⟩; exact one_le_nG hn1 _⟩
  have hi1 : 1 ≤ ⨅ h, nG (g * embG hF h) := le_ciInf fun h => one_le_nG hn1 _
  obtain ⟨h1, hh1⟩ := exists_lt_of_ciInf_lt (show (⨅ h, nG (g * embG hF h)) < 2 * ⨅ h, nG (g * embG hF h) by linarith)
  set g1 := g * embG hF h1 with hg1
  set y := colSq (uMat g) (zi e) with hy
  have hy0 : 0 < y := colSq_pos g _
  have hG1 := one_le_nG hn1 g1
  have hyG : Real.sqrt y ≤ nG g1 := by
    refine Real.sqrt_le_sqrt ?_
    rw [hy, ← col_emb (e := e) (uMat g) (uMat h1)]
    exact colSq_le_hs _ _
  have hsy : 0 < Real.sqrt y := Real.sqrt_pos.2 hy0
  have hpt : ∀ h : UJ ε', ‖φ (um g * emb e (um (h1 * h)))‖ ≤
      (C * 2 ^ (a + b) * (Real.sqrt y)⁻¹ ^ a) * (nG h)⁻¹ ^ b := by
    intro h
    have e1 : um g * emb e (um (h1 * h)) = uMat (g1 * embG hF h) := by
      rw [hg1, mul_assoc, ← map_mul]; rfl
    set t := nG (g1 * embG hF h) with ht
    have ht1 : 1 ≤ t := one_le_nG hn1 _
    have hh := one_le_nG (by omega : 1 ≤ n) h
    have t1 : nG g1 ≤ 2 * t := by
      have := ciInf_le hbd (h1 * h)
      rw [map_mul, ← mul_assoc] at this
      linarith
    have t2 : nG h ≤ nG g1 * t := by
      refine (nG_le_embG hF h).trans ?_
      have := nG_mul g1⁻¹ (g1 * embG hF h)
      rwa [inv_mul_cancel_left, nG_inv] at this
    have s1 : t⁻¹ ≤ 2 * (nG g1)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ (by linarith), inv_mul_le_iff₀ (by linarith)]; linarith
    have s2 : t⁻¹ ≤ nG g1 * (nG h)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ (by linarith), inv_mul_le_iff₀ (by linarith)]; linarith
    have s3 := rpow_hs hn1 (g1 * embG hF h) (a + b + b) (a := 3 * ((n : ℝ) + 1) ^ 2) (by
      simp only [ha, hb]; push_cast; have : (2 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith)
    have s4 : t⁻¹ ^ (a + b + b) ≤ (2 * (nG g1)⁻¹) ^ (a + b) * (nG g1 * (nG h)⁻¹) ^ b := by
      rw [pow_add _ (a + b)]
      exact mul_le_mul (pow_le_pow_left₀ (by positivity) s1 _) (pow_le_pow_left₀ (by positivity) s2 _) (by positivity)
        (by positivity)
    have s5 : (2 * (nG g1)⁻¹) ^ (a + b) * (nG g1 * (nG h)⁻¹) ^ b = 2 ^ (a + b) * (nG g1)⁻¹ ^ a * (nG h)⁻¹ ^ b := by
      have : (nG g1)⁻¹ ^ b * nG g1 ^ b = 1 := by rw [← mul_pow, inv_mul_cancel₀ (by linarith), one_pow]
      rw [mul_pow, mul_pow, pow_add (nG g1)⁻¹]
      linear_combination (2 ^ (a + b) * (nG g1)⁻¹ ^ a * (nG h)⁻¹ ^ b) * this
    have s6 : (nG g1)⁻¹ ^ a ≤ (Real.sqrt y)⁻¹ ^ a := pow_le_pow_left₀ (by positivity) (inv_anti₀ hsy hyG) a
    rw [e1]
    refine (hd _).trans ?_
    calc C * hs (uMat (g1 * embG hF h)) ^ (-(3 * ((n : ℝ) + 1) ^ 2))
        ≤ C * (2 ^ (a + b) * (Real.sqrt y)⁻¹ ^ a * (nG h)⁻¹ ^ b) := by
          refine mul_le_mul_of_nonneg_left (s3.trans (s4.trans (s5.le.trans ?_))) hC
          gcongr
      _ = _ := by ring
  rw [← lintegral_mul_left_eq_self (fun h : UJ ε' => ‖φ (um g * emb e (um h))‖ₑ) h1]
  refine (lint_le (by omega) ν (by positivity) hδ hδ1 hpt).trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _)
  have e2 : (Real.sqrt y)⁻¹ ^ a = y ^ (-((2 * ((n : ℝ) + 1) + 5) / 2)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hy0.le, ← Real.rpow_natCast, ← Real.rpow_mul hy0.le]
    congr 1
    simp only [ha]; push_cast; ring
  set T : ℝ := 100 * ((n : ℝ) + 1) ^ 2 / δ with hT
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have T1 : 16 * (n : ℝ) ^ 2 / δ ≤ T := div_le_div_of_nonneg_right (by nlinarith) hδ.le
  have T2 : 2 ≤ T := by rw [hT, le_div_iff₀ hδ]; nlinarith
  have T3 : (2 : ℝ) ^ (a + b) * (2 * (16 * (n : ℝ) ^ 2 / δ) ^ (2 * n ^ 2)) ≤ T ^ (10 * (n + 1) ^ 2) := by
    calc _ ≤ T ^ (a + b) * (T * T ^ (2 * n ^ 2)) := by gcongr
      _ = T ^ (a + b + 1 + 2 * n ^ 2) := by ring
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by simp only [ha, hb]; nlinarith)
  rw [e2]
  calc _ = C * (2 ^ (a + b) * (2 * (16 * (n : ℝ) ^ 2 / δ) ^ (2 * n ^ 2))) * y ^ (-((2 * ((n : ℝ) + 1) + 5) / 2)) := by ring
    _ ≤ _ := by gcongr

end CompanionTheory.Lime.T3
end
end

noncomputable section

open Matrix Finset MeasureTheory Formalism.REAL Formalism.MainNotions.S Filter Topology GlobalTheory.CompanionTheory.PairingAnalysis
open scoped InnerProductSpace ENNReal

namespace CompanionTheory.Lime.T3

open ReciprocityTheory.ChartRestriction.DS (smD smE actM)

theorem volume_ratio_bound : VolR := fun _ ε μ _ hm _ _ hδ hδ2 hR => vol_ratio hm ε μ hδ hδ2 hR

theorem decay_estimate : Decay := by
  intro m N ε lam A _ _ _ π hm hmN hl hDS hg v hv hv1 g₀ Y hY g
  have hN : 1 ≤ 12 * N ^ 2 := by have : 1 ≤ N := hm.trans hmN; nlinarith
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have h1 := dec_conj hm hDS.2.2.1 (by positivity) (dec_low hm hmN hl hDS hg hv hv1 hN le_rfl) g₀ g
  have h2 := one_le_nG hm g
  have h3 : 0 ≤ hs (uMat g₀) := by rw [← nG_sq]; positivity
  have e1 : (Real.exp 1 * Real.sqrt m) ^ (12 * N ^ 2) =
      Real.exp (6 * (N : ℝ) ^ 2 * Real.log m + 12 * (N : ℝ) ^ 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hm0, ← Real.exp_add, ← Real.exp_nat_mul]
    congr 1
    push_cast; ring
  have e2 : (nG g)⁻¹ ^ (12 * N ^ 2) = hs (um g) ^ (-(6 * (N : ℝ) ^ 2)) := by
    change _ = hs (uMat g) ^ _
    rw [← nG_sq, ← Real.rpow_natCast (nG g) 2, ← Real.rpow_mul (by linarith), inv_pow, ← Real.rpow_natCast,
      ← Real.rpow_neg (by linarith)]
    congr 1
    push_cast; ring
  rw [e1, e2] at h1
  refine h1.trans ?_
  have h4 : 0 ≤ hs (um g) ^ (-(6 * (N : ℝ) ^ 2)) := by rw [← e2]; positivity
  gcongr

theorem integral_ratio_bound : IntR := by
  intro m ε μ hμ hm φ C a hφ ha hd
  have hC : 0 ≤ C := by
    have h1 := (norm_nonneg _).trans (hd 1)
    have h2 : 0 < hs (um (1 : UJ ε)) ^ (-a) := Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos (one_le_hsG hm 1)) _
    exact nonneg_of_mul_nonneg_left h1 h2
  have hd' : ∀ g, ‖φ g‖ ≤ C * (nG g)⁻¹ ^ (2 * m ^ 2 + 1) := fun g =>
    (hd g).trans (mul_le_mul_of_nonneg_left (rpow_hs hm g _ (by push_cast; linarith)) hC)
  have hI := integrable_of_dec hm μ hφ hC le_rfl hd'
  refine ⟨hI, ?_⟩
  have h1 := lint_le hm μ hC one_pos le_rfl hd'
  rw [integral_norm_eq_lintegral_eNorm hI.1]
  refine (ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (nearSet_lt_top ε μ).ne) h1).trans (le_of_eq ?_)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), div_one]
  rfl

theorem derivative_upper_bound : DUp := by
  intro m ε lam B A _ _ _ π μ d hμ hm hl hDS hB hg hd
  have hπ : IsURepOn (UJset ε) π := hDS.2.2.1
  obtain ⟨S, hS⟩ := hDS.2.2.2.2.2.1
  obtain ⟨v0, hv0, hne, -⟩ := hS.2.2.2.1
  have hn0 : 0 < ‖v0‖ := norm_pos_iff.2 hne
  set v : A := ((‖v0‖⁻¹ : ℝ) : ℂ) • v0 with hvd
  have hv : v ∈ lowKSub ε lam π := Submodule.smul_mem _ _ (le_sSup (s := {S | IsKTypeOf ε π (Formalism.QuantumDeterminants.lowK ε lam) S}) hS hv0)
  have hv1 : ‖v‖ = 1 := by
    rw [hvd, norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity), inv_mul_cancel₀ hn0.ne']
  obtain ⟨x, hx, hb, -⟩ := low_bounds hm hl hDS hB hg hv hv1
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hB0 : 0 ≤ B := by have := le_four_mul hm hl hB; linarith
  set K : ℝ := 100 * m * (B + 1) with hK
  have hK1 : 200 ≤ K := by nlinarith
  have hsq : Real.sqrt m ≤ m := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
  have hnear : ∀ g ∈ nearSet ε (K ^ 2)⁻¹, 1 / 4 ≤ ‖⟪v, π (uMat g) v⟫_ℂ‖ ^ 2 := by
    intro g hgn
    have hδ : (K ^ 2)⁻¹ ≤ 1 / 2 := by rw [inv_le_comm₀ (by positivity) (by norm_num)]; nlinarith
    have h1 := disp_le hπ x hb (by positivity) hδ hgn
    rw [hx] at h1
    have h2 : 7 * (K ^ 2)⁻¹ * (8 * Real.sqrt m * (B + 2)) ≤ 1 / 2 := by
      have a1 : 8 * Real.sqrt m * (B + 2) ≤ K := by
        have : Real.sqrt m * (B + 2) ≤ m * (2 * (B + 1)) := mul_le_mul hsq (by linarith) (by linarith) (by linarith)
        nlinarith
      rw [mul_assoc, ← div_eq_inv_mul, ← mul_div_assoc, div_le_iff₀ (by positivity)]
      nlinarith
    have h3 : ‖⟪v, π (uMat g) v - v⟫_ℂ‖ ≤ 1 / 2 := by
      refine (norm_inner_le_norm _ _).trans ?_
      rw [hv1, one_mul]
      exact h1.trans h2
    rw [inner_sub_right, inner_self_eq_norm_sq_to_K, hv1] at h3
    have h4 := norm_sub_norm_le (1 : ℂ) (1 - ⟪v, π (uMat g) v⟫_ℂ)
    rw [sub_sub_cancel, norm_one, norm_sub_rev] at h4
    have h5 : ‖⟪v, π (uMat g) v⟫_ℂ - 1‖ ≤ 1 / 2 := by simpa using h3
    nlinarith [norm_nonneg ⟪v, π (uMat g) v⟫_ℂ]
  obtain ⟨hI, hE⟩ := hd.2 v v v v
  have e1 : ∀ g : UJ ε, coefOn π v v g * star (coefOn π v v g) = ((‖⟪v, π (uMat g) v⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
    intro g
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rfl
  simp only [e1] at hI hE
  have hI' : Integrable (fun g : UJ ε => ‖⟪v, π (uMat g) v⟫_ℂ‖ ^ 2) μ :=
    hI.re.congr (Filter.Eventually.of_forall fun g => Complex.ofReal_re _)
  rw [integral_complex_ofReal, inner_self_eq_norm_sq_to_K, hv1] at hE
  have hE' : ∫ g : UJ ε, ‖⟪v, π (uMat g) v⟫_ℂ‖ ^ 2 ∂μ = d⁻¹ := by
    have : ((∫ g : UJ ε, ‖⟪v, π (uMat g) v⟫_ℂ‖ ^ 2 ∂μ : ℝ) : ℂ) = ((d⁻¹ : ℝ) : ℂ) := by rw [hE]; simp
    exact_mod_cast this
  have hmeas : MeasurableSet (nearSet ε (K ^ 2)⁻¹) :=
    (isClosed_le (continuous_hs_real_place_taylor.comp ((continuous_coeMatrix ε).sub continuous_const)) continuous_const).measurableSet
  have h6 : ENNReal.ofReal (1 / 4) * μ (nearSet ε (K ^ 2)⁻¹) ≤ ENNReal.ofReal d⁻¹ := by
    rw [← hE', ofReal_integral_eq_lintegral_ofReal hI' (Filter.Eventually.of_forall fun g => by positivity),
      ← lintegral_indicator_const hmeas]
    refine lintegral_mono fun g => ?_
    by_cases hg' : g ∈ nearSet ε (K ^ 2)⁻¹
    · rw [Set.indicator_of_mem hg']; exact ENNReal.ofReal_le_ofReal (hnear g hg')
    · rw [Set.indicator_of_notMem hg']; exact bot_le
  have hd0 := hd.1
  calc ENNReal.ofReal d * μ (nearSet ε (K ^ 2)⁻¹)
      = ENNReal.ofReal (4 * d) * (ENNReal.ofReal (1 / 4) * μ (nearSet ε (K ^ 2)⁻¹)) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]; congr 2; ring
    _ ≤ ENNReal.ofReal (4 * d) * ENNReal.ofReal d⁻¹ := mul_le_mul_right h6 _
    _ = 4 := by
        rw [← ENNReal.ofReal_mul (by positivity), mul_assoc, mul_inv_cancel₀ hd0.ne', mul_one]; simp

end CompanionTheory.Lime.T3
