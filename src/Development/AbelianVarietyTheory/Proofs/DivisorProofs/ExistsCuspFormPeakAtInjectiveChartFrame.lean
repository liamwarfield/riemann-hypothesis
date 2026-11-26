module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHormanderPeakOrthonormalFrameL2Bound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitSumExpPotentialUniformBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoinConvBdd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralUnitaryKernelLeExpPowEight

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareL2InequalityFundamentalSet
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitSumKernelBallMeasureLeIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetNearOneMatrixNormBounds
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetNearOneMatrixNormBounds
open Matrix Polynomial

namespace GlobalTheory

theorem norm_multiset_prod_near_one (s : Multiset ℂ) (hs : ∀ μ ∈ s, ‖μ - 1‖ ≤ 1 / 2) :
    (1 / 2 : ℝ) ^ Multiset.card s ≤ ‖s.prod‖ ∧ ‖s.prod‖ ≤ (3 / 2 : ℝ) ^ Multiset.card s := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have ha := hs a (Multiset.mem_cons_self a s)
    obtain ⟨h1, h2⟩ := ih (fun μ hμ => hs μ (Multiset.mem_cons_of_mem hμ))
    have hlo : (1 / 2 : ℝ) ≤ ‖a‖ := by
      have := norm_sub_norm_le (1 : ℂ) (1 - a)
      rw [norm_one, sub_sub_cancel, norm_sub_rev] at this
      linarith
    have hhi : ‖a‖ ≤ 3 / 2 := by
      have := norm_add_le (a - 1) 1
      rw [sub_add_cancel, norm_one] at this
      linarith
    rw [Multiset.prod_cons, Multiset.card_cons, norm_mul, pow_succ, pow_succ]
    constructor
    · rw [mul_comm ((1 / 2 : ℝ) ^ _)]
      exact mul_le_mul hlo h1 (by positivity) (norm_nonneg _)
    · rw [mul_comm ((3 / 2 : ℝ) ^ _)]
      exact mul_le_mul hhi h2 (norm_nonneg _) (by norm_num)

theorem det_near_one_bounds (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (ε : ℝ)
    (hA : ∀ i j, ‖A i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j‖ ≤ ε) (hn : (n : ℝ) * ε ≤ 1 / 2) :
    (1 / 2 : ℝ) ^ n ≤ ‖A.det‖ ∧ ‖A.det‖ ≤ 2 ^ n := by
  have hroot : ∀ μ ∈ A.charpoly.roots, ‖μ - 1‖ ≤ 1 / 2 := by
    intro μ hμ
    have hr : A.charpoly.IsRoot μ := isRoot_of_mem_roots hμ
    have hev : Module.End.HasEigenvalue (Matrix.toLin' A) μ := by
      rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin']; exact hr
    obtain ⟨k, hk⟩ := eigenvalue_mem_ball hev
    rw [Metric.mem_closedBall, dist_eq_norm] at hk
    have hdiag : ‖A k k - 1‖ ≤ ε := by simpa using hA k k
    have h1n : 1 ≤ n := Fin.pos k
    have hoff : ∑ j ∈ Finset.univ.erase k, ‖A k j‖ ≤ ((n : ℝ) - 1) * ε := by
      have hle : ∀ j ∈ Finset.univ.erase k, ‖A k j‖ ≤ ε := by
        intro j hj
        have hjk : k ≠ j := (Finset.ne_of_mem_erase hj).symm
        simpa [Matrix.one_apply_ne hjk] using hA k j
      calc _ ≤ ∑ _j ∈ Finset.univ.erase k, ε := Finset.sum_le_sum hle
        _ = ((n : ℝ) - 1) * ε := by
          rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub h1n, Nat.cast_one]
    calc ‖μ - 1‖ = ‖(μ - A k k) + (A k k - 1)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖μ - A k k‖ + ‖A k k - 1‖ := norm_add_le _ _
      _ ≤ ((n : ℝ) - 1) * ε + ε := add_le_add (hk.trans hoff) hdiag
      _ = n * ε := by ring
      _ ≤ 1 / 2 := hn
  have hcard : Multiset.card A.charpoly.roots = n := by
    rw [(splits_iff_card_roots).mp (IsAlgClosed.splits _), Matrix.charpoly_natDegree_eq_dim,
      Fintype.card_fin]
  obtain ⟨h1, h2⟩ := norm_multiset_prod_near_one _ hroot
  rw [hcard, ← Matrix.det_eq_prod_roots_charpoly] at h1 h2
  refine ⟨h1, h2.trans ?_⟩
  exact pow_le_pow_left₀ (by norm_num) (by norm_num) n

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetNearOneMatrixNormBoundsStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_near_one_matrix_norm_bounds : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (ε : ℝ), (∀ i j, ‖A i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j‖ ≤ ε) → (n : ℝ) * ε ≤ 1 / 2 → (1 / 2 : ℝ) ^ n ≤ ‖A.det‖ ∧ ‖A.det‖ ≤ 2 ^ n := by
  first | exact @GlobalTheory.det_near_one_bounds | exact GlobalTheory.det_near_one_bounds | (intros; apply GlobalTheory.det_near_one_bounds <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitSumKernelBallMeasureLeIntegral
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory
open scoped ENNReal

namespace GlobalTheory.BallSum

open ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem norm_lminor_Gw_ge (X : Data E r) (w : V (nd X)) (τ : X.Ψ) (hw : 3 * (r : ℝ) * ‖w‖ ≤ 1 / 2) :
    (1 / 2 : ℝ) ^ r ≤ ‖lminor (Gw X w τ) (i0 X)‖ := by
  have hw0 : (r : ℝ) * ‖w‖ ≤ 1 := by nlinarith [norm_nonneg w]
  have hp : X.p0 ≤ r := X.p0_le
  have key := (GlobalTheory.T.det_near_one_matrix_norm_bounds X.p0 ((Gw X w τ).submatrix (Fin.castLE X.p0_le) (Fin.castLE X.p0_le))
    (3 * ‖w‖) (fun i j => ?_) ?_).1
  · unfold lminor
    refine le_trans ?_ key
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hp
  · have hJ : Jd X (Fin.castLE X.p0_le i) (Fin.castLE X.p0_le j) = (1 : Matrix (Fin X.p0) (Fin X.p0) ℂ) i j := by
      simp only [Jd, Matrix.diagonal_apply, Matrix.one_apply, Fin.castLE_inj]
      split_ifs with h
      · subst h; simp [sgn, i.isLt]
      · rfl
    rw [Matrix.submatrix_apply, ← hJ]
    exact GlobalTheory.T.gramChart_sub_form_entry_le E r X w τ _ _ hw0
  · have : (X.p0 : ℝ) ≤ r := by exact_mod_cast hp
    nlinarith [norm_nonneg w]

theorem rhY_cpt_le (X : Data E r) {x0 x : Frame X.Ψ r} (hx0 : IsOrth X x0) (hx : IsOrth X x)
    (hr : 0 < r) (w : V (nd X)) (hw : ‖w‖ ≤ 1 / (100 * (r : ℝ) ^ 2)) :
    rhY X x0 (cpt X x w) ≤ rhY X x0 x + X.Ψ.card * (3 * r * Real.log 2) := by
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hrw : 100 * (r : ℝ) ^ 2 * ‖w‖ ≤ 1 := by
    rw [le_div_iff₀ (by positivity)] at hw; linarith
  have hp : (X.p0 : ℝ) ≤ r := by exact_mod_cast X.p0_le
  have hw3 : 3 * (r : ℝ) * ‖w‖ ≤ 1 / 2 := by nlinarith [norm_nonneg w]
  have hterm : ∀ τ : X.Ψ, -(Real.log ‖dmin X.Gm (cpt X x w) τ (i0 X)‖ -
      2 * Real.log ‖lminor (gM X x0 (cpt X x w) τ) (i0 X)‖) ≤
        -(Real.log ‖dmin X.Gm x τ (i0 X)‖ - 2 * Real.log ‖lminor (gM X x0 x τ) (i0 X)‖) +
          3 * r * Real.log 2 := by
    intro τ
    have hd1 : ‖dmin X.Gm x τ (i0 X)‖ = 1 := norm_dmin_orth' X hx τ _
    have hA : -Real.log ‖dmin X.Gm (cpt X x w) τ (i0 X)‖ ≤ r * Real.log 2 := by
      rw [dmin_cpt_orth X hx]
      have h1 := norm_lminor_Gw_ge X w τ hw3
      have h2 : Real.log ((1 / 2 : ℝ) ^ r) ≤ Real.log ‖lminor (Gw X w τ) (i0 X)‖ :=
        Real.log_le_log (by positivity) h1
      rw [Real.log_pow, one_div, Real.log_inv] at h2
      linarith
    have hM22 := (sumBd_weight (Mq_isUpq X hx0 hx τ)).1
    have hnorm : ∀ y, ‖lminor (gM X x0 y τ) (i0 X)‖ = ‖(Mq X x0 y τ).toBlocks₂₂.det‖ := fun y => by
      rw [det_lowerBlock_eq_conj_minor, Complex.norm_conj]; rfl
    have hPP := GlobalTheory.T.det_near_one_matrix_norm_bounds X.p0 (((Mq X x0 x τ).toBlocks₂₂)⁻¹ * (Mq X x0 x τ).toBlocks₂₁ *
        (Nw X w τ).toBlocks₁₂ + (Nw X w τ).toBlocks₂₂) (((r : ℝ) + 1) * ‖w‖)
        (fun i j => pert_entry X hx0 hx w τ i j) (by nlinarith [norm_nonneg w])
    have hP := hPP.2
    have h0 : 0 < ‖(((Mq X x0 x τ).toBlocks₂₂)⁻¹ * (Mq X x0 x τ).toBlocks₂₁ *
        (Nw X w τ).toBlocks₁₂ + (Nw X w τ).toBlocks₂₂).det‖ := lt_of_lt_of_le (by positivity) hPP.1
    have hpos : 0 < ‖(Mq X x0 x τ).toBlocks₂₂.det‖ := norm_pos_iff.2 hM22
    have hB : Real.log ‖lminor (gM X x0 (cpt X x w) τ) (i0 X)‖ ≤
        Real.log ‖lminor (gM X x0 x τ) (i0 X)‖ + r * Real.log 2 := by
      rw [hnorm, hnorm, Mq_cpt', det_split _ _ hM22, norm_mul]
      rw [Real.log_mul hpos.ne' h0.ne']
      have h2 : Real.log ‖(((Mq X x0 x τ).toBlocks₂₂)⁻¹ * (Mq X x0 x τ).toBlocks₂₁ *
          (Nw X w τ).toBlocks₁₂ + (Nw X w τ).toBlocks₂₂).det‖ ≤ X.p0 * Real.log 2 := by
        rw [← Real.log_pow]; exact Real.log_le_log h0 hP
      have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      nlinarith
    rw [hd1, Real.log_one]
    linarith
  unfold rhY
  rw [← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib]
  calc ∑ τ, -(Real.log ‖dmin X.Gm (cpt X x w) τ (i0 X)‖ - 2 * Real.log ‖lminor (gM X x0 (cpt X x w) τ) (i0 X)‖)
      ≤ ∑ τ : X.Ψ, (-(Real.log ‖dmin X.Gm x τ (i0 X)‖ - 2 * Real.log ‖lminor (gM X x0 x τ) (i0 X)‖) +
          3 * r * Real.log 2) := Finset.sum_le_sum fun τ _ => hterm τ
    _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]

end GlobalTheory.BallSum

namespace GlobalTheory.BallSum

open ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem lintegral_orbit_le (X : Data E r) {x y : Frame X.Ψ r} (hx : IsOrth X x) (hy : IsOrth X y)
    {A : Set (V (nd X))} (hA : MeasurableSet A) (hAO : A ⊆ OmF X x) {φ : Frame X.Ψ r → ℝ≥0∞}
    (hφ : Measurable φ) (hφB : ∀ u ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul u b) = φ u)
    (hinj : ∀ γ ∈ X.Γ, ∀ z ∈ A, ∀ z' ∈ A, ∀ b ∈ Bor X.Ψ r,
      lact γ (cpt X x z) = rmul (cpt X x z') b → γ = 1) :
    ∫⁻ z in A, ∑' γ : X.Γ, φ (lact γ.1 (cpt X x z)) ∂muF X x ≤ ∫⁻ z, φ (cpt X y z) ∂muF X y := by
  classical
  have := FundSetPf.countable_GL (E := E) (r := r)
  have hS := GlobalTheory.Unfold.measurableSet_satFrames X hx hA hAO
  have hc : Measurable (cpt X x) := (FundSetPf.cont_cpt X x).measurable
  let χ : X.Γ → Frame X.Ψ r → ℝ≥0∞ := fun γ =>
    ((fun u => lact (γ.1)⁻¹ u) ⁻¹' GlobalTheory.Unfold.satFrames X x A).indicator φ
  have hχm : ∀ γ, Measurable (χ γ) := fun γ =>
    hφ.indicator ((GlobalTheory.Unfold.continuous_lact X _).measurable hS)
  have hχB : ∀ γ, ∀ u ∈ X.dom, ∀ b ∈ Bor X.Ψ r, χ γ (rmul u b) = χ γ u := by
    intro γ u hu b hb
    simp only [χ, Set.indicator, Set.mem_preimage, FundSetPf.lact_rmul,
      GlobalTheory.Unfold.rmul_mem_satFrames_iff X x A _ hb, hφB u hu b hb]
  have hterm : ∀ γ : X.Γ, ∫⁻ z in A, φ (lact γ.1 (cpt X x z)) ∂muF X x =
      ∫⁻ z, χ γ (cpt X x z) ∂muF X x := by
    intro γ
    rw [measInv_holds r X x (lact γ.1 x) hx (GlobalTheory.Unfold.isOrth_lact X hx γ.2) (χ γ) (hχm γ) (hχB γ),
      GlobalTheory.Unfold.muF_lact X x γ.2, ← lintegral_indicator hA]
    refine lintegral_congr fun z => ?_
    simp only [χ, Set.indicator, Set.mem_preimage, GlobalTheory.Unfold.cpt_lact, FundSetPf.lact_inv,
      GlobalTheory.Unfold.cpt_mem_satFrames_iff X hx]
  have huniq : ∀ (u : Frame X.Ψ r) (γ γ' : X.Γ), lact (γ.1)⁻¹ u ∈ GlobalTheory.Unfold.satFrames X x A →
      lact (γ'.1)⁻¹ u ∈ GlobalTheory.Unfold.satFrames X x A → γ = γ' := by
    intro u γ γ' hm hm'
    obtain ⟨z, hz, b, hb, h⟩ := hm
    obtain ⟨z', hz', b', hb', h'⟩ := hm'
    have hδ : (γ'.1)⁻¹ * γ.1 ∈ X.Γ := X.Γ.mul_mem (X.Γ.inv_mem γ'.2) γ.2
    have e1 : lact ((γ'.1)⁻¹ * γ.1) (rmul (cpt X x z) b) = rmul (cpt X x z') b' := by
      rw [← h, ← h', ← FundSetPf.lact_mul, mul_assoc, mul_inv_cancel, mul_one]
    have e2 : lact ((γ'.1)⁻¹ * γ.1) (cpt X x z) = rmul (cpt X x z') (rmul b' (ExtFPf.invF X b)) := by
      rw [← ExtFPf.rmul_assoc, ← e1, ← FundSetPf.lact_rmul, ExtFPf.rmul_assoc, ExtFPf.rmul_invF X hb,
        ExtFPf.rmul_oneF]
    have h1 := hinj _ hδ z hz z' hz' _ (ExtFPf.mul_mem X hb' (ExtFPf.invF_mem X hb)) e2
    exact Subtype.ext (inv_mul_eq_one.mp h1).symm
  have hpt : ∀ u, ∑' γ : X.Γ, χ γ u ≤ φ u := by
    intro u
    by_cases hT : ∃ γ : X.Γ, lact (γ.1)⁻¹ u ∈ GlobalTheory.Unfold.satFrames X x A
    · obtain ⟨γ0, hγ0⟩ := hT
      rw [tsum_eq_single γ0]
      · exact Set.indicator_le_self _ _ u
      · intro γ hne
        exact Set.indicator_of_notMem (s := (fun u => lact (γ.1)⁻¹ u) ⁻¹' GlobalTheory.Unfold.satFrames X x A)
          (fun hm => hne (huniq u γ γ0 hm hγ0)) φ
    · push_neg at hT
      have h0 : ∀ γ : X.Γ, χ γ u = 0 := fun γ =>
        Set.indicator_of_notMem (s := (fun u => lact (γ.1)⁻¹ u) ⁻¹' GlobalTheory.Unfold.satFrames X x A) (hT γ) φ
      simp [h0]
  calc ∫⁻ z in A, ∑' γ : X.Γ, φ (lact γ.1 (cpt X x z)) ∂muF X x
      = ∑' γ : X.Γ, ∫⁻ z in A, φ (lact γ.1 (cpt X x z)) ∂muF X x :=
        lintegral_tsum fun γ => ((hφ.comp (GlobalTheory.Unfold.continuous_lact X γ.1).measurable).comp hc).aemeasurable
    _ = ∑' γ : X.Γ, ∫⁻ z, χ γ (cpt X x z) ∂muF X x := tsum_congr hterm
    _ = ∫⁻ z, ∑' γ : X.Γ, χ γ (cpt X x z) ∂muF X x :=
        (lintegral_tsum fun γ => ((hχm γ).comp hc).aemeasurable).symm
    _ ≤ ∫⁻ z, φ (cpt X x z) ∂muF X x := lintegral_mono fun z => hpt _
    _ = ∫⁻ z, φ (cpt X y z) ∂muF X y := measInv_holds r X x y hx hy φ hφ hφB

end GlobalTheory.BallSum

namespace GlobalTheory.BallSum

open ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf

theorem const_le (f r : ℕ) : (4 * (f : ℝ) * (r : ℝ) ^ 2 + 1) * ((f : ℝ) * (3 * (r : ℝ) * Real.log 2)) ≤
    15 * ((f : ℝ) * r) ^ 8 := by
  have hl : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
  have hl0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rcases Nat.eq_zero_or_pos f with hf | hf
  · subst hf; simp
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr; simp
  have hf1 : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  set a : ℝ := (f : ℝ) * r with ha
  have ha1 : 1 ≤ a := by nlinarith
  have h3 : a ^ 3 ≤ a ^ 8 := pow_le_pow_right₀ ha1 (by norm_num)
  have h1 : a ≤ a ^ 8 := by
    calc a = a ^ 1 := (pow_one a).symm
      _ ≤ a ^ 8 := pow_le_pow_right₀ ha1 (by norm_num)
  have hfr : (f : ℝ) ^ 2 * (r : ℝ) ^ 3 ≤ a ^ 3 := by
    rw [ha, mul_pow]
    have : (f : ℝ) ^ 2 ≤ (f : ℝ) ^ 3 := pow_le_pow_right₀ hf1 (by norm_num)
    exact mul_le_mul_of_nonneg_right this (by positivity)
  have hx : (4 * (f : ℝ) * (r : ℝ) ^ 2 + 1) * ((f : ℝ) * (3 * (r : ℝ) * Real.log 2)) ≤
      (4 * (f : ℝ) * (r : ℝ) ^ 2 + 1) * ((f : ℝ) * (3 * (r : ℝ))) := by
    have h := mul_le_mul_of_nonneg_left hl (show 0 ≤ 3 * (r : ℝ) by positivity)
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity)) (by positivity)
    linarith
  have he : (4 * (f : ℝ) * (r : ℝ) ^ 2 + 1) * ((f : ℝ) * (3 * (r : ℝ))) =
      12 * ((f : ℝ) ^ 2 * (r : ℝ) ^ 3) + 3 * a := by rw [ha]; ring
  linarith

theorem ballSum_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x y : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r), 0 < X.p0 → X.p0 < r → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X y → (∀ γ ∈ X.Γ, ∀ z z' : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X), ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ‖z'‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ∀ b ∈ Bor X.Ψ r, lact γ (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) = rmul (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z') b → γ = 1) → ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x (Metric.ball (0 : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) (1 / (100 * (r : ℝ) ^ 2)) ∩ ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x) * ∑' γ : X.Γ, ENNReal.ofReal (ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.kaY X x (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) (lact γ.1 y)) ≤ ENNReal.ofReal (Real.exp (C * ((X.Ψ.card : ℝ) * r) ^ 8)) * ∫⁻ z, ENNReal.ofReal (ReciprocityTheory.ChartRestriction.G.AR.Up.kaF X y (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) z) ∂(ReciprocityTheory.ChartRestriction.G.AR.Up.muF X y) := by
  refine ⟨15, by norm_num, ?_⟩
  intro E _ _ _ r X x y hp0 hp0r hx hy hinj
  classical
  haveI := FundSetPf.countable_GL (E := E) (r := r)
  have hr : 0 < r := by omega
  set s : ℝ := 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1 with hs
  have hs0 : 0 ≤ s := by positivity
  set ρ : ℝ := 1 / (100 * (r : ℝ) ^ 2) with hρ
  set A : Set (V (nd X)) := Metric.ball (0 : V (nd X)) ρ ∩ OmF X x with hAdef
  set K : ℝ := (X.Ψ.card : ℝ) * (3 * r * Real.log 2) with hK
  set k : ℝ≥0∞ := ENNReal.ofReal (Real.exp (s * K)) with hk
  set φ : Frame X.Ψ r → ℝ≥0∞ := fun u => ENNReal.ofReal (kaY X y s u) with hφdef
  have hφm : Measurable φ := ENNReal.measurable_ofReal.comp (meas_kaY X y s)
  have hφB : ∀ u ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul u b) = φ u := fun u hu b hb => by
    simp only [hφdef, kaY_rmul X hy hu hb]
  set G : Frame X.Ψ r → ℝ≥0∞ := fun u => ∑' δ : X.Γ, φ (lact δ.1 u) with hGdef

  have hsym : ∑' γ : X.Γ, ENNReal.ofReal (kaY X x s (lact γ.1 y)) = G x := by
    simp only [hGdef]
    rw [← (Equiv.inv X.Γ).tsum_eq (fun δ : X.Γ => φ (lact δ.1 x))]
    refine tsum_congr fun γ => ?_
    have hγi : (γ.1)⁻¹ ∈ X.Γ := X.Γ.inv_mem γ.2
    show ENNReal.ofReal (kaY X x s (lact γ.1 y)) = ENNReal.ofReal (kaY X y s (lact (γ.1)⁻¹ x))
    rw [GlobalTheory.PoinSumBound.kaY_eq_exp X hx (orth_mem_dom X (GlobalTheory.Unfold.isOrth_lact X hy γ.2)),
      GlobalTheory.PoinSumBound.kaY_eq_exp X hy (orth_mem_dom X (GlobalTheory.Unfold.isOrth_lact X hx hγi)),
      GlobalTheory.Up.rhX_lact (X.Γ_stab _ γ.2), GlobalTheory.OrbitSum.rhX_symm X (GlobalTheory.Unfold.isOrth_lact X hx hγi) hy]

  have hHar : ∀ w ∈ A, G x ≤ k * G (cpt X x w) := by
    intro w hw
    simp only [hGdef]
    rw [← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun δ => ?_
    have ho := GlobalTheory.Unfold.isOrth_lact X hx δ.2
    have hwn : ‖w‖ ≤ ρ := (mem_ball_zero_iff.1 hw.1).le
    have h := GlobalTheory.BallSum.rhY_cpt_le X hy ho hr w hwn
    show ENNReal.ofReal (kaY X y s (lact δ.1 x)) ≤ k * ENNReal.ofReal (kaY X y s (lact δ.1 (cpt X x w)))
    rw [← GlobalTheory.Unfold.cpt_lact, hk, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    refine ENNReal.ofReal_le_ofReal ?_
    unfold kaY
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have := mul_le_mul_of_nonneg_left h hs0
    linarith

  have hAm : MeasurableSet A := measurableSet_ball.inter (OntoB.isOpen_OmF X x).measurableSet
  have h1 : muF X x A * G x ≤ k * ∫⁻ z in A, G (cpt X x z) ∂muF X x := by
    rw [mul_comm, ← setLIntegral_const, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact setLIntegral_mono' hAm fun z hz => hHar z hz

  have h2 : ∫⁻ z in A, G (cpt X x z) ∂muF X x ≤ ∫⁻ z, φ (cpt X y z) ∂muF X y :=
    lintegral_orbit_le X hx hy hAm Set.inter_subset_right hφm hφB
      fun γ hγ z hz z' hz' b hb e => hinj γ hγ z z' (mem_ball_zero_iff.1 hz.1).le
        (mem_ball_zero_iff.1 hz'.1).le b hb e
  have h3 : ∫⁻ z, φ (cpt X y z) ∂muF X y = ∫⁻ z, ENNReal.ofReal (kaF X y s z) ∂muF X y := by
    simp only [hφdef, kaY_cpt X hy]
  have hkC : k ≤ ENNReal.ofReal (Real.exp (15 * ((X.Ψ.card : ℝ) * r) ^ 8)) :=
    ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (const_le X.Ψ.card r))
  rw [hsym]
  calc muF X x A * G x ≤ k * ∫⁻ z in A, G (cpt X x z) ∂muF X x := h1
    _ ≤ k * ∫⁻ z, ENNReal.ofReal (kaF X y s z) ∂muF X y := mul_le_mul_of_nonneg_left (h2.trans h3.le) zero_le
    _ ≤ _ := mul_le_mul_of_nonneg_right hkC zero_le

end GlobalTheory.BallSum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitSumKernelBallMeasureLeIntegralStatement
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbitSum_kernel_ballMeasure_le_integral : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x y : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r), 0 < X.p0 → X.p0 < r → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X y → (∀ γ ∈ X.Γ, ∀ z z' : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X), ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ‖z'‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ∀ b ∈ Bor X.Ψ r, lact γ (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) = rmul (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z') b → γ = 1) → ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x (Metric.ball (0 : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) (1 / (100 * (r : ℝ) ^ 2)) ∩ ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x) * ∑' γ : X.Γ, ENNReal.ofReal (ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.kaY X x (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) (lact γ.1 y)) ≤ ENNReal.ofReal (Real.exp (C * ((X.Ψ.card : ℝ) * r) ^ 8)) * ∫⁻ z, ENNReal.ofReal (ReciprocityTheory.ChartRestriction.G.AR.Up.kaF X y (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) z) ∂(ReciprocityTheory.ChartRestriction.G.AR.Up.muF X y) := by
  first | exact @GlobalTheory.BallSum.ballSum_le | exact GlobalTheory.BallSum.ballSum_le | (intros; apply GlobalTheory.BallSum.ballSum_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantMeasureChartBallOrthonormalLowerBound
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantMeasureChartBallOrthonormalLowerBound
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory
open scoped ENNReal

namespace GlobalTheory.BallVol

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem spread_zero (X : Data E r) (hr : 0 < r) (τ : X.Ψ) : X.spread (fun _ _ => 0) τ = 0 := by
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  simp [Data.spread]

theorem nd_le (X : Data E r) : nd X ≤ X.Ψ.card * (r * r) := by
  unfold nd
  rw [Fintype.card_prod, Fintype.card_coe]
  refine Nat.mul_le_mul_left _ ?_
  calc Fintype.card {p : Fin r × Fin r // p.2 < p.1} ≤ Fintype.card (Fin r × Fin r) :=
        Fintype.card_subtype_le _
    _ = r * r := by simp

theorem nat_bound (f r n : ℕ) (hf : 1 ≤ f) (hr : 1 ≤ r) (hn : n ≤ f * (r * r)) :
    2 * n * (200 * r ^ 3 * f) + n * n + 1 ≤ 402 * (f * r) ^ 8 := by
  set a := f * r with ha
  have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have hra : r ≤ a := by rw [ha]; exact Nat.le_mul_of_pos_left r (by omega)
  have hfa : f ≤ a := by rw [ha]; exact Nat.le_mul_of_pos_right f (by omega)
  have hna : n ≤ a * a := hn.trans (by rw [ha, ← Nat.mul_assoc]; exact Nat.mul_le_mul_left _ hra)
  have h1 : 2 * n * (200 * r ^ 3 * f) ≤ 400 * a ^ 8 := by
    have e : 2 * n * (200 * r ^ 3 * f) ≤ 400 * ((a * a) * (a ^ 3 * a)) := by
      have := Nat.mul_le_mul hna (Nat.mul_le_mul (Nat.pow_le_pow_left hra 3) hfa)
      nlinarith
    refine e.trans (Nat.mul_le_mul_left _ ?_)
    calc a * a * (a ^ 3 * a) = a ^ 6 := by ring
      _ ≤ a ^ 8 := Nat.pow_le_pow_right ha1 (by norm_num)
  have h2 : n * n ≤ a ^ 8 := by
    calc n * n ≤ (a * a) * (a * a) := Nat.mul_le_mul hna hna
      _ = a ^ 4 := by ring
      _ ≤ a ^ 8 := Nat.pow_le_pow_right ha1 (by norm_num)
  have h3 : 1 ≤ a ^ 8 := Nat.one_le_pow _ _ ha1
  omega

theorem real_bound (f r n : ℕ) (hf : 1 ≤ f) (hr : 1 ≤ r) (hn : n ≤ f * (r * r)) :
    Real.exp (-(402 * ((f : ℝ) * r) ^ 8)) ≤ Real.exp (-(1 / 10)) *
      (Real.pi ^ n * (1 / (200 * (r : ℝ) ^ 3 * f)) ^ (2 * n) / n.factorial) := by
  set K : ℝ := 200 * (r : ℝ) ^ 3 * f with hK
  have hf' : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hK1 : 1 ≤ K := by
    have : (1 : ℝ) ≤ (r : ℝ) ^ 3 := one_le_pow₀ hr'
    rw [hK]; nlinarith
  have hKpos : 0 < K := by linarith

  have hδ : Real.exp (-K) ≤ 1 / K := by
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ hKpos (by linarith [Real.add_one_le_exp K])
  have hδn : Real.exp (-(2 * n * K)) ≤ (1 / K) ^ (2 * n) := by
    calc Real.exp (-(2 * n * K)) = Real.exp (-K) ^ (2 * n) := by
          rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
      _ ≤ (1 / K) ^ (2 * n) := pow_le_pow_left₀ (Real.exp_pos _).le hδ _
  have hpi : (1 : ℝ) ≤ Real.pi ^ n := one_le_pow₀ (by linarith [Real.pi_gt_three])
  have hfac : (n.factorial : ℝ) ≤ Real.exp ((n : ℝ) * n) := by
    have h1 : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
    have h2 : (n : ℝ) ^ n ≤ Real.exp n ^ n :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith [Real.add_one_le_exp (n : ℝ)]) _
    rw [← Real.exp_nat_mul] at h2
    exact h1.trans h2
  have hfpos : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hN := nat_bound f r n hf hr hn
  have hNR : 2 * (n : ℝ) * K + n * n + 1 ≤ 402 * ((f : ℝ) * r) ^ 8 := by
    rw [hK]; exact_mod_cast hN
  have hmain : Real.exp (-(402 * ((f : ℝ) * r) ^ 8)) ≤
      Real.exp (-(1 / 10)) * (Real.exp (-(2 * n * K)) / Real.exp ((n : ℝ) * n)) := by
    rw [← Real.exp_sub, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  refine hmain.trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
  calc Real.exp (-(2 * n * K)) / Real.exp ((n : ℝ) * n)
      ≤ (1 / K) ^ (2 * n) / n.factorial := div_le_div₀ (by positivity) hδn hfpos hfac
    _ ≤ Real.pi ^ n * (1 / K) ^ (2 * n) / n.factorial := by
        gcongr
        exact le_mul_of_one_le_left (by positivity) hpi

theorem ballvol : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r), 0 < X.p0 → X.p0 < r →
    ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x →
    ENNReal.ofReal (Real.exp (-(C * ((X.Ψ.card : ℝ) * r) ^ 8))) ≤
      ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x (Metric.ball (0 : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X))
        (1 / (100 * (r : ℝ) ^ 2)) ∩ ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x) := by
  refine ⟨402, by norm_num, ?_⟩
  intro E _ _ _ r X x hp0 hpr hx
  have hr : 0 < r := lt_of_le_of_lt (Nat.zero_le _) hpr
  set la : Wt X.Ψ r := fun _ _ => 0 with hla
  set w : ℝ := ∑ τ, X.spread la τ with hw
  have hw0 : w = 0 := Finset.sum_eq_zero fun τ _ => spread_zero X hr τ
  have hcard : ((X.Ψ.card : ℕ) : ℝ) = fdeg E := by
    rw [← Fintype.card_coe, QuadraticCoefficientForms.card_Psi X]
  have hf1 : (1 : ℝ) ≤ (X.Ψ.card : ℝ) := by rw [hcard]; exact one_le_field_half_degree
  have hf1n : 1 ≤ X.Ψ.card := by exact_mod_cast hf1
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  set δ := GlobalTheory.LevGeo.chartRad E r w with hδ
  have hδeq : δ = 1 / (200 * (r : ℝ) ^ 3 * (X.Ψ.card : ℝ)) := by
    rw [hδ, GlobalTheory.LevGeo.chartRad, hw0, zero_add, hcard]
  have hδpos : 0 < δ := by rw [hδeq]; positivity
  have hδle : δ ≤ 1 / (100 * (r : ℝ) ^ 2) := by
    rw [hδeq]
    refine one_div_le_one_div_of_le (by positivity) ?_
    have h3 : (r : ℝ) ^ 2 ≤ (r : ℝ) ^ 3 := pow_le_pow_right₀ hr1 (by norm_num)
    have h4 : (r : ℝ) ^ 3 ≤ (r : ℝ) ^ 3 * (X.Ψ.card : ℝ) := le_mul_of_one_le_right (by positivity) hf1
    nlinarith
  have hnear : ∀ z : V (nd X), ‖z‖ ≤ δ → cpt X x z ∈ X.dom ∧
      Real.exp (-(1 / 20)) ≤ X.nfac la (cpt X x z) ^ 2 ∧ Real.exp (-(1 / 10)) ≤ densF X x z :=
    fun z hz => GlobalTheory.ChartNearOne.chart_near_one E r X la w x hr hx le_rfl z hz
  have hsubO : Metric.ball (0 : V (nd X)) δ ⊆ OmF X x := fun z hz =>
    (hnear z (le_of_lt (mem_ball_zero_iff.1 hz))).1
  have hsub : Metric.ball (0 : V (nd X)) δ ⊆
      Metric.ball 0 (1 / (100 * (r : ℝ) ^ 2)) ∩ OmF X x := fun z hz =>
    ⟨Metric.ball_subset_ball hδle hz, hsubO hz⟩
  refine le_trans ?_ (measure_mono hsub)
  have hm : muF X x (Metric.ball 0 δ) =
      ∫⁻ z in Metric.ball (0 : V (nd X)) δ, ENNReal.ofReal (densF X x z) := by
    rw [muF, withDensity_apply _ measurableSet_ball, Measure.restrict_restrict measurableSet_ball,
      Set.inter_eq_left.2 hsubO]
  rw [hm]
  have hn := nd_le X
  calc ENNReal.ofReal (Real.exp (-(402 * ((X.Ψ.card : ℝ) * r) ^ 8)))
      ≤ ENNReal.ofReal (Real.exp (-(1 / 10))) * volume (Metric.ball (0 : V (nd X)) δ) := by
        rw [GlobalTheory.volume_ball_euclideanSpace_complex 0 hδpos, Fintype.card_fin,
          ← ENNReal.ofReal_mul (Real.exp_pos _).le]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hδeq]
        exact real_bound X.Ψ.card r (nd X) hf1n hr hn
    _ = ∫⁻ z in Metric.ball (0 : V (nd X)) δ, ENNReal.ofReal (Real.exp (-(1 / 10))) := by
        rw [setLIntegral_const, mul_comm]
    _ ≤ _ := setLIntegral_mono' measurableSet_ball fun z hz =>
        ENNReal.ofReal_le_ofReal (hnear z (le_of_lt (mem_ball_zero_iff.1 hz))).2.2

end

end GlobalTheory.BallVol
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantMeasureChartBallOrthonormalLowerBoundStatement
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariantMeasure_chartBall_orthonormal_lower_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r), 0 < X.p0 → X.p0 < r → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → ENNReal.ofReal (Real.exp (-(C * ((X.Ψ.card : ℝ) * r) ^ 8))) ≤ ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x (Metric.ball (0 : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) (1 / (100 * (r : ℝ) ^ 2)) ∩ ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x) := by
  first | exact @GlobalTheory.BallVol.ballvol | exact GlobalTheory.BallVol.ballvol | (intros; apply GlobalTheory.BallVol.ballvol <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareL2InequalityFundamentalSet
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
open ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory
open scoped ENNReal

namespace GlobalTheory.PoincareL2

theorem nfac_pos' {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (la : Wt X.Ψ r)
    {y : Frame X.Ψ r} (hy : y ∈ X.dom) : 0 < X.nfac la y := by
  unfold Data.nfac
  refine Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => Real.rpow_pos_of_pos ?_ _
  exact norm_pos_iff.mpr (div_ne_zero (PoinPf.dmin_ne X hy τ _) (PoinPf.dmin_ne X hy τ _))

theorem poincareNorm_sq_eq_weight_mul_norm_sq {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (la : Wt X.Ψ r)
    (P : Frame X.Ψ r → ℂ) {y : Frame X.Ψ r} (hy : y ∈ X.dom) :
    ENNReal.ofReal (X.pnorm la P y ^ 2) = ENNReal.ofReal (‖P y‖ ^ 2) * IW.Wpsi X la (fun _ => 0) y := by
  have h1 : X.pnorm la P y ^ 2 = ‖P y‖ ^ 2 * Real.exp (-phla X la y) := by
    rw [PoinPf.exp_neg_phla X la (nfac_pos' X la hy)]
    change (‖P y‖ * X.nfac la y) ^ 2 = _
    ring
  have h2 : IW.Wpsi X la (fun _ => 0) y = ENNReal.ofReal (Real.exp (-(phla X la y + 0))) := by
    simp [IW.Wpsi, hy]
  rw [h1, h2, add_zero, ENNReal.ofReal_mul (by positivity)]

theorem sum_le (h1 : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x y : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r), 0 < X.p0 → X.p0 < r → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X y → (∀ γ ∈ X.Γ, ∀ z z' : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X), ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ‖z'‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ∀ b ∈ Bor X.Ψ r, lact γ (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) = rmul (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z') b → γ = 1) → ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x (Metric.ball (0 : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) (1 / (100 * (r : ℝ) ^ 2)) ∩ ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x) * ∑' γ : X.Γ, ENNReal.ofReal (ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.kaY X x (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) (lact γ.1 y)) ≤ ENNReal.ofReal (Real.exp (C * ((X.Ψ.card : ℝ) * r) ^ 8)) * ∫⁻ z, ENNReal.ofReal (ReciprocityTheory.ChartRestriction.G.AR.Up.kaF X y (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) z) ∂(ReciprocityTheory.ChartRestriction.G.AR.Up.muF X y)) (h2 : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (y : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r), 0 < X.p0 → X.p0 < r → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X y → ∫⁻ z, ENNReal.ofReal (ReciprocityTheory.ChartRestriction.G.AR.Up.kaF X y (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) z) ∂(ReciprocityTheory.ChartRestriction.G.AR.Up.muF X y) ≤ ENNReal.ofReal (Real.exp (C * ((X.Ψ.card : ℝ) * r) ^ 8))) (h3 : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r), 0 < X.p0 → X.p0 < r → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → ENNReal.ofReal (Real.exp (-(C * ((X.Ψ.card : ℝ) * r) ^ 8))) ≤ ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x (Metric.ball (0 : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) (1 / (100 * (r : ℝ) ^ 2)) ∩ ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r),
      0 < X.p0 → X.p0 < r → IsOrth X x → (∀ γ ∈ X.Γ, ∀ z z' : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X), ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ‖z'‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ∀ b ∈ Bor X.Ψ r, lact γ (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) = rmul (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z') b → γ = 1) → ∀ y ∈ X.dom,
      ∑' γ : X.Γ, ENNReal.ofReal (PoinPf.kaY X x (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) (lact γ.1 y)) ≤ ENNReal.ofReal (Real.exp (C * ((X.Ψ.card : ℝ) * r) ^ 8)) := by
  obtain ⟨C1, hC1, hS1⟩ := h1
  obtain ⟨C2, hC2, hS2⟩ := h2
  obtain ⟨C3, hC3, hS3⟩ := h3
  refine ⟨C1 + C2 + C3, by positivity, ?_⟩
  intro E _ _ _ r X x hp0 hp0r hx hinj y hy
  have hb := FrameDegreeData.bOf_mem X hy
  have ho : IsOrth X (rmul y (FrameDegreeData.bOf X y)) := FrameDegreeData.ortho_bOf X hy
  set y' := rmul y (FrameDegreeData.bOf X y) with hy'
  have heq : ∑' γ : X.Γ, ENNReal.ofReal (PoinPf.kaY X x (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) (lact γ.1 y)) =
      ∑' γ : X.Γ, ENNReal.ofReal (PoinPf.kaY X x (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) (lact γ.1 y')) := by
    refine tsum_congr fun γ => ?_
    rw [hy', PoinPf.lact_rmul' γ.1 y (FrameDegreeData.bOf X y),
      PoinPf.kaY_rmul X hx ((PairUnfoldPf.lact_mem_dom_iff X γ.2 y).2 hy) hb]
  rw [heq]
  set S := ∑' γ : X.Γ, ENNReal.ofReal (PoinPf.kaY X x (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) (lact γ.1 y'))
  set N : ℝ := ((X.Ψ.card : ℝ) * r) ^ 8
  set M := muF X x (Metric.ball (0 : V (nd X)) (1 / (100 * (r : ℝ) ^ 2)) ∩ OmF X x)
  have e1 : M * S ≤ ENNReal.ofReal (Real.exp (C1 * N)) * ENNReal.ofReal (Real.exp (C2 * N)) :=
    (hS1 E r X x y' hp0 hp0r hx ho hinj).trans (mul_le_mul' le_rfl (hS2 E r X y' hp0 hp0r ho))
  have e3 : ENNReal.ofReal (Real.exp (-(C3 * N))) ≤ M := hS3 E r X x hp0 hp0r hx
  have hone : ENNReal.ofReal (Real.exp (C3 * N)) * ENNReal.ofReal (Real.exp (-(C3 * N))) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), ← Real.exp_add]; simp
  calc S = (ENNReal.ofReal (Real.exp (C3 * N)) * ENNReal.ofReal (Real.exp (-(C3 * N)))) * S := by
          rw [hone, one_mul]
    _ ≤ (ENNReal.ofReal (Real.exp (C3 * N)) * M) * S := by gcongr
    _ = ENNReal.ofReal (Real.exp (C3 * N)) * (M * S) := by ring
    _ ≤ ENNReal.ofReal (Real.exp (C3 * N)) * (ENNReal.ofReal (Real.exp (C1 * N)) * ENNReal.ofReal (Real.exp (C2 * N))) := by
          gcongr
    _ = ENNReal.ofReal (Real.exp ((C1 + C2 + C3) * N)) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), ← Real.exp_add,
            ← Real.exp_add]
          congr 2; ring

end GlobalTheory.PoincareL2

theorem GlobalTheory.PoincareL2.poincare_l2_of_orthogonal (h1 : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field
    E] [NumberField E] [IsCMField E] (r : ℕ) (X
    : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x y
    : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r), 0 < X.p0 → X.p0 < r → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X y → (∀ γ ∈ X.Γ, ∀ z z' : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd
    X), ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ‖z'‖ ≤ 1 / (100 * (r : ℝ) ^
    2) → ∀ b ∈ Bor X.Ψ r, lact γ (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x
    z) = rmul (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x
    z') b → γ = 1) → ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x (Metric.ball (0
    : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) (1 /
    (100 * (r : ℝ) ^ 2)) ∩ ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X
    x) * ∑' γ : X.Γ, ENNReal.ofReal (ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.kaY X x (4 *
    (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) (lact γ.1 y)) ≤ ENNReal.ofReal (Real.exp (C * ((X.Ψ.card : ℝ)
    * r) ^ 8)) * ∫⁻ z, ENNReal.ofReal (ReciprocityTheory.ChartRestriction.G.AR.Up.kaF X y (4 *
    (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) z) ∂(ReciprocityTheory.ChartRestriction.G.AR.Up.muF X y)) (h2
    : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X
    : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (y
    : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r), 0 < X.p0 → X.p0 < r → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X y → ∫⁻ z, ENNReal.ofReal (ReciprocityTheory.ChartRestriction.G.AR.Up.kaF
    X y (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) z) ∂(ReciprocityTheory.ChartRestriction.G.AR.Up.muF X
    y) ≤ ENNReal.ofReal (Real.exp (C * ((X.Ψ.card : ℝ) * r) ^ 8))) (h3 : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X
    : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x
    : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r), 0 < X.p0 → X.p0 < r → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → ENNReal.ofReal (Real.exp
    (-(C * ((X.Ψ.card : ℝ) * r) ^
    8))) ≤ ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x (Metric.ball (0
    : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) (1 /
    (100 * (r : ℝ) ^ 2)) ∩ ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X
    x)) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X
    : Data E r) (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (x x0 : Frame X.Ψ r) (FF
    : Set (ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd
    X))) (F : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd
    X) → ℂ) (P0
    : Frame X.Ψ r → ℂ), 0 < X.p0 → X.p0 < r → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x0 → ReciprocityTheory.ChartRestriction.G.AR.Up.IsFundSet X x0 FF → (∀ γ ∈ X.Γ, ∀ z z' : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd
    X), ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ‖z'‖ ≤ 1 / (100 * (r : ℝ) ^
    2) → ∀ b ∈ Bor X.Ψ r, lact γ (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x
    z) = rmul (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x
    z') b → γ = 1) → DifferentiableOn ℂ F (ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X
    x) → ReciprocityTheory.ChartRestriction.G.AR.Up.IsBEq X la P0 → (∀ z ∈ ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x, P0 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt
    X x z) = F z) → ∫⁻ z in FF, ENNReal.ofReal (X.pnorm la
    (ReciprocityTheory.ChartRestriction.G.AR.Up.poin X la P0)
    (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z) ^
    2) ∂(ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x0) ≤ ENNReal.ofReal (Real.exp (C *
    ((X.Ψ.card : ℝ) * r) ^ 8)) * ∫⁻ z, ENNReal.ofReal (‖F z‖ ^ 2 /
    ReciprocityTheory.ChartRestriction.G.AR.Up.kaF X x (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1)
    z) * ReciprocityTheory.ChartRestriction.G.AR.Up.IW.Wpsi X la (fun _ => 0) (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt
    X x z) ∂(ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x) := by
  obtain ⟨C, hC, hsum⟩ := GlobalTheory.PoincareL2.sum_le h1 h2 h3
  refine ⟨C, hC, ?_⟩
  intro E _ _ _ r X la x x0 FF F P0 hp0 hp0r hx hx0 hFF hinj hFd hP0 hPF
  classical
  set bb : ℝ := (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) with hbbdef
  have hInv : IsInvFn X (fun _ : Frame X.Ψ r => (0 : ℝ)) := fun _ _ _ _ _ _ => rfl
  have hW := (IW.metricW_of GlobalTheory.NormFactor.nfacRmul_holds GlobalTheory.NormFactor.nfacLact_holds ortho_holds
    lu_holds X la (fun _ => 0) hInv (fun _ _ => contDiffOn_const) ⟨0, fun _ _ => le_rfl⟩).1
  set W := IW.Wpsi X la (fun _ => 0) with hWdef
  obtain ⟨D⟩ := ExtFPf.luData_of lu_holds X x0 hx0
  set C1 := ENNReal.ofReal (Real.exp (C * ((X.Ψ.card : ℝ) * r) ^ 8)) with hC1def
  have hsumY := hsum E r X x hp0 hp0r hx hinj
  set Pd := X.dom.indicator P0 with hPd
  have hPdm : Measurable Pd := PairUnfoldPf.meas_indC X hP0.1.continuousOn
  set ψ : Frame X.Ψ r → ℝ≥0∞ := fun y => ‖Pd y‖ₑ ^ 2 * W y / ENNReal.ofReal (PoinPf.kaY X x bb y) with hψ
  have hψm : Measurable ψ :=
    ((hPdm.enorm.pow_const 2).mul hW.1).div (PoinPf.meas_kaY X x bb).ennreal_ofReal
  have hψB : ∀ y ∈ X.dom, ∀ b ∈ Bor X.Ψ r, ψ (rmul y b) = ψ y := by
    intro y hy b hb
    have hyb : rmul y b ∈ X.dom := PoinPf.rmulDom X hb hy
    simp only [hψ, hPd, Set.indicator_of_mem hyb, Set.indicator_of_mem hy, hP0.2 y hy b hb,
      hW.2.1 y hy b hb, PoinPf.kaY_rmul X hx hy hb]
    have hpos : 0 < ‖bchar la b‖ ^ 2 := pow_pos (norm_pos_iff.2 (PoinPf.bchar_ne X la hb)) 2
    have h0 : ENNReal.ofReal (‖bchar la b‖ ^ 2) ≠ 0 := (ENNReal.ofReal_pos.2 hpos).ne'
    have ht : ENNReal.ofReal (‖bchar la b‖ ^ 2) ≠ ⊤ := ENNReal.ofReal_ne_top
    have hc : ‖bchar la b‖ₑ ^ 2 = ENNReal.ofReal (‖bchar la b‖ ^ 2) := by
      rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    rw [enorm_mul, mul_pow, hc]
    congr 1
    rw [ENNReal.div_eq_inv_mul]
    calc ENNReal.ofReal (‖bchar la b‖ ^ 2) * ‖P0 y‖ₑ ^ 2 * ((ENNReal.ofReal (‖bchar la b‖ ^ 2))⁻¹ * W y)
        = (ENNReal.ofReal (‖bchar la b‖ ^ 2) * (ENNReal.ofReal (‖bchar la b‖ ^ 2))⁻¹) *
            (‖P0 y‖ₑ ^ 2 * W y) := by ring
      _ = ‖P0 y‖ₑ ^ 2 * W y := by rw [ENNReal.mul_inv_cancel h0 ht, one_mul]
  have hpt : ∀ z ∈ FF, ENNReal.ofReal (X.pnorm la (poin X la P0) (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z) ^ 2) ≤
      C1 * ∑' γ : X.Γ, ψ (lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z)) := by
    intro z hz
    have hy : ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z ∈ X.dom := hFF.2.1 hz
    rw [GlobalTheory.PoincareL2.poincareNorm_sq_eq_weight_mul_norm_sq X la _ hy]
    have hk0 : ∀ γ : X.Γ, ENNReal.ofReal (PoinPf.kaY X x bb (lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z))) ≠ 0 :=
      fun γ => (ENNReal.ofReal_pos.2 (PoinPf.kaY_pos _ _ _ _)).ne'
    have hkt : ∀ γ : X.Γ, ENNReal.ofReal (PoinPf.kaY X x bb (lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z))) ≠ ⊤ :=
      fun _ => ENNReal.ofReal_ne_top
    have hcs := PoinPf.cs_sq (fun γ : X.Γ => ‖P0 (lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z))‖ₑ)
      (fun γ => ENNReal.ofReal (PoinPf.kaY X x bb (lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z)))) hk0 hkt
    have e1 : ENNReal.ofReal (‖poin X la P0 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z)‖ ^ 2) ≤
        (∑' γ : X.Γ, ‖P0 (lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z))‖ₑ) ^ 2 := by
      rw [ENNReal.ofReal_pow (norm_nonneg _)]
      exact pow_le_pow_left₀ zero_le (PoinPf.enorm_poin_le X la P0 _) 2
    have e2 : ∀ γ : X.Γ, ‖P0 (lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z))‖ₑ ^ 2 /
        ENNReal.ofReal (PoinPf.kaY X x bb (lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z))) * W (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z) =
          ψ (lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z)) := by
      intro γ
      have hγy : lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z) ∈ X.dom := (PairUnfoldPf.lact_mem_dom_iff X γ.2 _).2 hy
      simp only [hψ, hPd, Set.indicator_of_mem hγy, hW.2.2 γ.1 γ.2 _ hy]
      rw [ENNReal.mul_div_right_comm]
    calc ENNReal.ofReal (‖poin X la P0 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z)‖ ^ 2) * W (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z)
        ≤ ((∑' γ : X.Γ, ‖P0 (lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z))‖ₑ ^ 2 /
            ENNReal.ofReal (PoinPf.kaY X x bb (lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z)))) * C1) * W (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z) :=
          mul_le_mul_of_nonneg_right
            (e1.trans (hcs.trans (mul_le_mul_of_nonneg_left (hsumY _ hy) zero_le))) zero_le
      _ = C1 * ∑' γ : X.Γ, ψ (lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z)) := by
          rw [← tsum_congr e2, ENNReal.tsum_mul_right]; ring
  have hmeasγ : ∀ γ : X.Γ, AEMeasurable (fun z => ψ (lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z)))
      ((muF X x0).restrict FF) := fun γ =>
    (hψm.comp ((PairUnfoldPf.lact_cont X γ.1).comp (PairUnfoldPf.cpt_cont X x0)).measurable).aemeasurable
  have hunf := PairUnfoldPf.lunfold D FF measInv_holds hx0 hFF ψ hψm hψB
  have hmi := measInv_holds r X x0 x hx0 hx ψ hψm hψB
  have hrhs : ∫⁻ z, ψ (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) ∂muF X x =
      ∫⁻ z, ENNReal.ofReal (‖F z‖ ^ 2 / kaF X x bb z) * W (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) ∂muF X x := by
    refine lintegral_congr_ae ?_
    filter_upwards [ExtFPf.ae_OmF] with z hz
    have hyd : ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z ∈ X.dom := hz
    simp only [hψ, hPd, Set.indicator_of_mem hyd, hPF z hz, PoinPf.kaY_cpt X hx]
    rw [ENNReal.ofReal_div_of_pos (by unfold kaF; exact Real.exp_pos _), ENNReal.ofReal_pow (norm_nonneg _),
      ofReal_norm, ENNReal.mul_div_right_comm]
  calc ∫⁻ z in FF, ENNReal.ofReal (X.pnorm la (poin X la P0) (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z) ^ 2) ∂muF X x0
      ≤ ∫⁻ z in FF, C1 * ∑' γ : X.Γ, ψ (lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z)) ∂muF X x0 :=
        setLIntegral_mono' hFF.1 hpt
    _ = C1 * ∑' γ : X.Γ, ∫⁻ z in FF, ψ (lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z)) ∂muF X x0 := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_tsum hmeasγ]
    _ = C1 * ∫⁻ z, ψ (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z) ∂muF X x0 := by rw [hunf]
    _ = C1 * ∫⁻ z, ENNReal.ofReal (‖F z‖ ^ 2 / kaF X x bb z) * W (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) ∂muF X x := by
        rw [hmi, hrhs]

theorem GlobalTheory.PoincareL2.poincare_l2_inequality : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (x x0 : Frame X.Ψ r) (FF : Set (ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X))) (F : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X) → ℂ) (P0 : Frame X.Ψ r → ℂ), 0 < X.p0 → X.p0 < r → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x0 → ReciprocityTheory.ChartRestriction.G.AR.Up.IsFundSet X x0 FF → (∀ γ ∈ X.Γ, ∀ z z' : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X), ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ‖z'‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ∀ b ∈ Bor X.Ψ r, lact γ (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) = rmul (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z') b → γ = 1) → DifferentiableOn ℂ F (ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x) → ReciprocityTheory.ChartRestriction.G.AR.Up.IsBEq X la P0 → (∀ z ∈ ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x, P0 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) = F z) → ∫⁻ z in FF, ENNReal.ofReal (X.pnorm la (ReciprocityTheory.ChartRestriction.G.AR.Up.poin X la P0) (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z) ^ 2) ∂(ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x0) ≤ ENNReal.ofReal (Real.exp (C * ((X.Ψ.card : ℝ) * r) ^ 8)) * ∫⁻ z, ENNReal.ofReal (‖F z‖ ^ 2 / ReciprocityTheory.ChartRestriction.G.AR.Up.kaF X x (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) z) * ReciprocityTheory.ChartRestriction.G.AR.Up.IW.Wpsi X la (fun _ => 0) (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) ∂(ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x) :=
  GlobalTheory.PoincareL2.poincare_l2_of_orthogonal GlobalTheory.T.orbitSum_kernel_ballMeasure_le_integral GlobalTheory.T.lintegral_unitaryKernel_le_exp_pow_eight GlobalTheory.T.invariantMeasure_chartBall_orthonormal_lower_bound
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareL2InequalityFundamentalSetStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
open ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.poincare_l2_inequality_fundamental_set : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (x x0 : Frame X.Ψ r) (FF : Set (ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X))) (F : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X) → ℂ) (P0 : Frame X.Ψ r → ℂ), 0 < X.p0 → X.p0 < r → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x0 → ReciprocityTheory.ChartRestriction.G.AR.Up.IsFundSet X x0 FF → (∀ γ ∈ X.Γ, ∀ z z' : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X), ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ‖z'‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ∀ b ∈ Bor X.Ψ r, lact γ (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) = rmul (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z') b → γ = 1) → DifferentiableOn ℂ F (ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x) → ReciprocityTheory.ChartRestriction.G.AR.Up.IsBEq X la P0 → (∀ z ∈ ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x, P0 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) = F z) → ∫⁻ z in FF, ENNReal.ofReal (X.pnorm la (ReciprocityTheory.ChartRestriction.G.AR.Up.poin X la P0) (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z) ^ 2) ∂(ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x0) ≤ ENNReal.ofReal (Real.exp (C * ((X.Ψ.card : ℝ) * r) ^ 8)) * ∫⁻ z, ENNReal.ofReal (‖F z‖ ^ 2 / ReciprocityTheory.ChartRestriction.G.AR.Up.kaF X x (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) z) * ReciprocityTheory.ChartRestriction.G.AR.Up.IW.Wpsi X la (fun _ => 0) (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) ∂(ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x) := by
  first | exact @GlobalTheory.PoincareL2.poincare_l2_inequality | exact GlobalTheory.PoincareL2.poincare_l2_inequality | (intros; apply GlobalTheory.PoincareL2.poincare_l2_inequality <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspFormPeakAtInjectiveChartFrame
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
open ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory
open scoped ENNReal

theorem GlobalTheory.PeakThick.peak : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (x : Frame X.Ψ r), 0 < X.p0 → X.p0 < r → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → (∀ τ (a b : Fin r), (b : ℕ) = a + 1 → (b : ℕ) ≠ X.p0 → C * ((X.Ψ.card : ℝ) * r) ^ 8 ≤ (la τ a : ℝ) - la τ b) → (∀ τ (a b : Fin r), (a : ℕ) = 0 → (b : ℕ) = r - 1 → C * ((X.Ψ.card : ℝ) * r) ^ 8 ≤ (la τ b : ℝ) - la τ a) → (∀ γ ∈ X.Γ, ∀ z z' : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X), ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ‖z'‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ∀ b ∈ Bor X.Ψ r, lact γ (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) = rmul (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z') b → γ = 1) → ∀ (x0 : Frame X.Ψ r) (FF : Set (ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X))), ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x0 → ReciprocityTheory.ChartRestriction.G.AR.Up.IsFundSet X x0 FF → ∃ P ∈ X.SS la, P x ≠ 0 ∧ ENNReal.ofReal (Real.exp (-(C * ((∑ τ, ∑ a, |(la τ a : ℝ)|) + ((X.Ψ.card : ℝ) * r) ^ 8)))) * ∫⁻ z in FF, ENNReal.ofReal (X.pnorm la P (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z) ^ 2) ∂(ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x0) ≤ ENNReal.ofReal (X.pnorm la P x ^ 2) * ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x0 FF := by
  obtain ⟨CH, hCH, hH⟩ := GlobalTheory.T.exists_hormanderPeak_orthonormalFrame_l2Bound
  obtain ⟨CS, hCS, hS⟩ := GlobalTheory.T.poincare_l2_inequality_fundamental_set
  refine ⟨CH + CS + 1, by linarith, ?_⟩
  intro E _ _ _ r X la x hp0 hp0r hx hgap hpair hinj x0 FF hx0 hFF
  classical
  obtain ⟨σ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hΨ : ∃ τ0 : X.Ψ, True := by
    by_cases hσ : σ ∈ X.Ψ
    · exact ⟨⟨σ, hσ⟩, trivial⟩
    · exact ⟨⟨ComplexEmbedding.conjugate σ, by
        by_contra h
        exact hσ ((X.cmType σ).2 h)⟩, trivial⟩
  obtain ⟨τ0, -⟩ := hΨ
  have hcard : (1 : ℝ) ≤ X.Ψ.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨τ0.1, τ0.2⟩
  have hr : (1 : ℝ) ≤ r := by exact_mod_cast (show 1 ≤ r by omega)
  have hN : (1 : ℝ) ≤ (X.Ψ.card : ℝ) * r := by nlinarith
  have hN8 : (1 : ℝ) ≤ ((X.Ψ.card : ℝ) * r) ^ 8 := one_le_pow₀ hN
  have hS0 : 0 ≤ ∑ τ, ∑ a, |(la τ a : ℝ)| := by positivity
  have hgapH : ∀ τ (a b : Fin r), (b : ℕ) = a + 1 → (b : ℕ) ≠ X.p0 →
      CH * ((X.Ψ.card : ℝ) * r) ^ 8 ≤ (la τ a : ℝ) - la τ b := fun τ a b h1 h2 =>
    le_trans (by nlinarith) (hgap τ a b h1 h2)
  have hpairH : ∀ τ (a b : Fin r), (a : ℕ) = 0 → (b : ℕ) = r - 1 →
      CH * ((X.Ψ.card : ℝ) * r) ^ 8 ≤ (la τ b : ℝ) - la τ a := fun τ a b h1 h2 =>
    le_trans (by nlinarith) (hpair τ a b h1 h2)
  obtain ⟨F, P0, hFd, hP0, hagree, hP0x, hvan, hInAt, hbound⟩ :=
    hH E r X la x hp0 hp0r hx hgapH hpairH hinj
  have hInv : IsInvFn X (fun _ : Frame X.Ψ r => (0 : ℝ)) := fun _ _ _ _ _ _ => rfl
  have hW := IW.metricW_of GlobalTheory.NormFactor.nfacRmul_holds GlobalTheory.NormFactor.nfacLact_holds ortho_holds
    lu_holds X la (fun _ => 0) hInv (fun _ _ => contDiffOn_const) ⟨0, fun _ _ => le_rfl⟩
  have hbb : 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1 := by linarith
  have hpoin := poin_holds r X x hx (GlobalTheory.ClosedDiscontinuity.propDisc_closed r X) la _ _ hW.1 hW.2
    hbb F P0 hFd hInAt hP0 hagree
  have hbdd : X.IsBddSec la (poin X la P0) := hpoin.2.1
  have hSS : poin X la P0 ∈ X.SS la := by
    refine cuspStatement_holds r X la τ0 hp0 hp0r (fun i j h1 h2 => ?_) (fun i0 i1 h1 h2 => ?_) _ hbdd
    · have := hgap τ0 i j h1 h2
      have h3 : ((la τ0 j : ℤ) : ℝ) ≤ la τ0 i := by nlinarith
      exact_mod_cast h3
    · have := hpair τ0 i0 i1 h1 h2
      have h3 : ((la τ0 i0 : ℤ) : ℝ) < la τ0 i1 := by nlinarith
      exact_mod_cast h3
  have hchi1 : X.χ la 1 = 1 := by
    have h1 := X.χ_mul la 1 X.Γ.one_mem 1 X.Γ.one_mem
    rw [one_mul] at h1
    have h2 := IC.chi_ne_zero X la X.Γ.one_mem
    have h3 : X.χ la 1 * (X.χ la 1 - 1) = 0 := by linear_combination -h1
    rcases mul_eq_zero.1 h3 with h | h
    · exact absurd h h2
    · linear_combination h
  have hPx : poin X la P0 x = 1 := by
    rw [IC.poin_single X la P0 x X.Γ.one_mem hvan, IW.lact_one X, hP0x, hchi1]
    simp
  have hpn : X.pnorm la (poin X la P0) x = 1 := by
    rw [IC.pnorm_orth X la _ hx, hPx, norm_one]
  refine ⟨poin X la P0, hSS, by rw [hPx]; exact one_ne_zero, ?_⟩

  have hA : MeasurableSet (Metric.ball (0 : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) (1 / (100 * (r : ℝ) ^ 2)) ∩ OmF X x) :=
    Metric.isOpen_ball.measurableSet.inter
      ((IW.isOpen_dom X).preimage (IW.cpt_diff X x).continuous).measurableSet
  have hvol : muF X x (Metric.ball 0 (1 / (100 * (r : ℝ) ^ 2)) ∩ OmF X x) ≤ muF X x0 FF := by
    have h := GlobalTheory.Unfold.lintegral_chart_le_mul_fundSet E r X x0 x FF
      (Metric.ball 0 (1 / (100 * (r : ℝ) ^ 2)) ∩ OmF X x) 1 (fun _ => 1) hx0 hx hFF hA
      Set.inter_subset_right measurable_const (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) (by
        have hsub : {γ : GL (Fin r) E | γ ∈ X.Γ ∧ ∃ z ∈ Metric.ball 0 (1 / (100 * (r : ℝ) ^ 2)) ∩ OmF X x,
            ∃ z' ∈ Metric.ball 0 (1 / (100 * (r : ℝ) ^ 2)) ∩ OmF X x, ∃ b ∈ Bor X.Ψ r,
              lact γ (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) = rmul (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z') b} ⊆ {1} := by
          rintro γ ⟨hγ, z, hz, z', hz', b, hb, he⟩
          have h1 : ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) := le_of_lt (by simpa using hz.1)
          have h2 : ‖z'‖ ≤ 1 / (100 * (r : ℝ) ^ 2) := le_of_lt (by simpa using hz'.1)
          exact hinj γ hγ z z' h1 h2 b hb he
        have := Set.encard_le_encard hsub
        rw [Set.encard_singleton] at this
        exact_mod_cast this)
    simpa [setLIntegral_one] using h
  have hSb := hS E r X la x x0 FF F P0 hp0 hp0r hx hx0 hFF hinj hFd hP0 hagree
  rw [hpn, one_pow, ENNReal.ofReal_one, one_mul]
  calc ENNReal.ofReal (Real.exp (-((CH + CS + 1) * ((∑ τ, ∑ a, |(la τ a : ℝ)|) + ((X.Ψ.card : ℝ) * r) ^ 8))))
        * ∫⁻ z in FF, ENNReal.ofReal (X.pnorm la (poin X la P0) (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z) ^ 2) ∂(muF X x0)
      ≤ ENNReal.ofReal (Real.exp (-((CH + CS + 1) * ((∑ τ, ∑ a, |(la τ a : ℝ)|) + ((X.Ψ.card : ℝ) * r) ^ 8))))
        * (ENNReal.ofReal (Real.exp (CS * ((X.Ψ.card : ℝ) * r) ^ 8)) *
          (ENNReal.ofReal (Real.exp (CH * ((∑ τ, ∑ a, |(la τ a : ℝ)|) + ((X.Ψ.card : ℝ) * r) ^ 8))) * muF X x0 FF)) := by
        gcongr
        exact hSb.trans (mul_le_mul' le_rfl (hbound.trans (mul_le_mul' le_rfl hvol)))
    _ = ENNReal.ofReal (Real.exp (-((CH + CS + 1) * ((∑ τ, ∑ a, |(la τ a : ℝ)|) + ((X.Ψ.card : ℝ) * r) ^ 8)))
          * Real.exp (CS * ((X.Ψ.card : ℝ) * r) ^ 8)
          * Real.exp (CH * ((∑ τ, ∑ a, |(la τ a : ℝ)|) + ((X.Ψ.card : ℝ) * r) ^ 8))) * muF X x0 FF := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
        ring
    _ ≤ 1 * muF X x0 FF := by
        gcongr
        rw [← Real.exp_add, ← Real.exp_add, ENNReal.ofReal_le_one, Real.exp_le_one_iff]
        nlinarith
    _ = muF X x0 FF := one_mul _
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspFormPeakAtInjectiveChartFrameStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cusp_form_peak_at_injective_chart_frame : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (x : Frame X.Ψ r), 0 < X.p0 → X.p0 < r → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → (∀ τ (a b : Fin r), (b : ℕ) = a + 1 → (b : ℕ) ≠ X.p0 → C * ((X.Ψ.card : ℝ) * r) ^ 8 ≤ (la τ a : ℝ) - la τ b) → (∀ τ (a b : Fin r), (a : ℕ) = 0 → (b : ℕ) = r - 1 → C * ((X.Ψ.card : ℝ) * r) ^ 8 ≤ (la τ b : ℝ) - la τ a) → (∀ γ ∈ X.Γ, ∀ z z' : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X), ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ‖z'‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ∀ b ∈ Bor X.Ψ r, lact γ (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) = rmul (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z') b → γ = 1) → ∀ (x0 : Frame X.Ψ r) (FF : Set (ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X))), ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x0 → ReciprocityTheory.ChartRestriction.G.AR.Up.IsFundSet X x0 FF → ∃ P ∈ X.SS la, P x ≠ 0 ∧ ENNReal.ofReal (Real.exp (-(C * ((∑ τ, ∑ a, |(la τ a : ℝ)|) + ((X.Ψ.card : ℝ) * r) ^ 8)))) * ∫⁻ z in FF, ENNReal.ofReal (X.pnorm la P (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z) ^ 2) ∂(ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x0) ≤ ENNReal.ofReal (X.pnorm la P x ^ 2) * ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x0 FF := by
  first | exact @GlobalTheory.PeakThick.peak | exact GlobalTheory.PeakThick.peak | (intros; apply GlobalTheory.PeakThick.peak <;> assumption)
end
