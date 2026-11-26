module

public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Smooth

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.OrbitDecayEstimates.CurveDerivativeDecay.OneLeHsG
open MeasureTheory Matrix Topology Metric Formalism.REAL
open scoped ENNReal

noncomputable section

namespace CompanionTheory.Lime.T3

section frob

open scoped Matrix.Norms.Frobenius

theorem hs_box {n : ℕ} {u : Matrix (Fin n) (Fin n) ℂ} {s : ℝ} (h : ∀ i j, ‖u i j‖ ≤ s) : hs u ≤ (n * s) ^ 2 := by
  unfold hs
  calc ∑ i, ∑ j, ‖u i j‖ ^ 2 ≤ ∑ _i : Fin n, ∑ _j : Fin n, s ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _) (h i j) 2
    _ = (n * s) ^ 2 := by simp; ring

theorem near_one {n : ℕ} {k u v : Matrix (Fin n) (Fin n) ℂ} {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2)
    (hu : hs (u - 1) ≤ t ^ 2) (hv : hs (v - 1) ≤ t ^ 2) (h : k * u = v) : hs (k - 1) ≤ (4 * t) ^ 2 := by
  rw [frobenius_eq_norm_sq] at hu hv ⊢
  have hu' : ‖u - 1‖ ≤ t := (pow_le_pow_iff_left₀ (norm_nonneg _) ht0 two_ne_zero).1 hu
  have hv' : ‖v - 1‖ ≤ t := (pow_le_pow_iff_left₀ (norm_nonneg _) ht0 two_ne_zero).1 hv
  have e : k - 1 = (v - 1) - (k - 1) * (u - 1) - (u - 1) := by rw [← h]; noncomm_ring
  have h1 : ‖k - 1‖ ≤ ‖v - 1‖ + ‖k - 1‖ * ‖u - 1‖ + ‖u - 1‖ := by
    calc ‖k - 1‖ = ‖(v - 1) - (k - 1) * (u - 1) - (u - 1)‖ := by rw [← e]
      _ ≤ ‖(v - 1) - (k - 1) * (u - 1)‖ + ‖u - 1‖ := norm_sub_le _ _
      _ ≤ ‖v - 1‖ + ‖(k - 1) * (u - 1)‖ + ‖u - 1‖ := by gcongr; exact norm_sub_le _ _
      _ ≤ _ := by gcongr; exact Matrix.frobenius_norm_mul _ _
  have h2 : ‖k - 1‖ * ‖u - 1‖ ≤ ‖k - 1‖ * (1 / 2) := mul_le_mul_of_nonneg_left (hu'.trans ht) (norm_nonneg _)
  exact pow_le_pow_left₀ (norm_nonneg _) (by linarith) 2

theorem entry_le {n : ℕ} {g u : Matrix (Fin n) (Fin n) ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hg : hs g ≤ R ^ 2) (hu : hs (u - 1) ≤ (1 / 2) ^ 2) (i j : Fin n) : ‖(g * u) i j‖ ≤ R * (Real.sqrt n + 1) := by
  rw [frobenius_eq_norm_sq] at hg hu
  have hg' : ‖g‖ ≤ R := (pow_le_pow_iff_left₀ (norm_nonneg _) hR two_ne_zero).1 hg
  have hu1 : ‖u - 1‖ ≤ 1 / 2 := (pow_le_pow_iff_left₀ (norm_nonneg _) (by norm_num) two_ne_zero).1 hu
  have hu' : ‖u‖ ≤ Real.sqrt n + 1 := by
    calc ‖u‖ = ‖1 + (u - 1)‖ := by rw [add_sub_cancel]
      _ ≤ ‖(1 : Matrix (Fin n) (Fin n) ℂ)‖ + ‖u - 1‖ := norm_add_le _ _
      _ ≤ _ := by rw [norm_one_matrix_eq_sqrt]; linarith
  have he : ‖(g * u) i j‖ ≤ ‖g * u‖ := by
    have := f1auxiliary_entry_le (g * u) i j
    rw [frobenius_eq_norm_sq] at this
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this
  calc ‖(g * u) i j‖ ≤ ‖g * u‖ := he
    _ ≤ ‖g‖ * ‖u‖ := Matrix.frobenius_norm_mul _ _
    _ ≤ R * (Real.sqrt n + 1) := by gcongr

end frob

def nearSet {n : ℕ} (ε : Fin n → Bool) (δ : ℝ) : Set (UJ ε) := {k | hs (coeMatrixAlt ε k - 1) ≤ δ ^ 2}

theorem vol_ratio {n : ℕ} (hn : 1 ≤ n) (ε : Fin n → Bool) (μ : Measure (UJ ε)) [SFinite μ] [μ.IsMulLeftInvariant]
    {δ R : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 2) (hR0 : 0 ≤ R) :
    μ {g | hsG g ≤ R ^ 2} ≤ ENNReal.ofReal ((4 * n * (Real.sqrt n + 1) * R / δ) ^ (2 * n ^ 2)) * μ (nearSet ε δ) := by
  classical
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  let lam : Measure (MatrixCoordinates n) := Measure.addHaar
  set s : ℝ := δ / (4 * n) with hs_def
  have hs0 : 0 < s := by positivity
  have hns : n * s = δ / 4 := by rw [hs_def]; field_simp
  let O : Set (MatrixCoordinates n) := closedBall (Matrix.of.symm 1) s
  have hO : ∀ x ∈ O, hs (Matrix.of x - 1) ≤ (δ / 4) ^ 2 := by
    intro x hx
    rw [← hns]
    refine hs_box fun i j => ?_
    set o : MatrixCoordinates n := Matrix.of.symm 1 with ho
    have h1 : ‖x - o‖ ≤ s := by rwa [← mem_closedBall_iff_norm]
    exact ((norm_le_pi_norm ((x - o) i) j).trans (norm_le_pi_norm (x - o) i)).trans h1
  have hof : Continuous (fun x : MatrixCoordinates n => Matrix.of x) := continuous_id
  have hofs : Continuous (fun x : Matrix (Fin n) (Fin n) ℂ => (Matrix.of.symm x : MatrixCoordinates n)) := continuous_id
  have hfr : Module.finrank ℝ (MatrixCoordinates n) = 2 * n ^ 2 := by
    simp [MatrixCoordinates, Module.finrank_pi_fintype, Complex.finrank_real_complex]; ring
  have hB_pos : 0 < lam (ball 0 1) := measure_ball_pos lam _ one_pos
  have hB_fin : lam (ball 0 1) < ⊤ := measure_ball_lt_top
  have hOv : lam O = ENNReal.ofReal (s ^ (2 * n ^ 2)) * lam (ball 0 1) := by
    rw [Measure.addHaar_closedBall lam _ hs0.le, hfr]
  set W := nearSet ε δ
  set ρ : ℝ := R * (Real.sqrt n + 1) with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  set S : Set (UJ ε) := {g | hsG g ≤ R ^ 2} with hS
  have hS_meas : MeasurableSet S :=
    (isClosed_le (continuous_hs_real_place_taylor.comp (continuous_coeMatrix ε)) continuous_const).measurableSet
  let Φ : UJ ε × MatrixCoordinates n → MatrixCoordinates n := fun p => leftMulReal (coeMatrixAlt ε p.1⁻¹) p.2
  have hΦ : Continuous Φ := by
    show Continuous fun p : UJ ε × MatrixCoordinates n =>
      (Matrix.of.symm (coeMatrixAlt ε p.1⁻¹ * Matrix.of p.2) : MatrixCoordinates n)
    exact hofs.comp (((continuous_coeMatrix ε).comp (continuous_inv.comp continuous_fst)).matrix_mul
      (hof.comp continuous_snd))
  let T : Set (UJ ε × MatrixCoordinates n) := {p | hsG p.1 ≤ R ^ 2} ∩ Φ ⁻¹' O
  have hT : MeasurableSet T :=
    (isClosed_le ((continuous_hs_real_place_taylor.comp (continuous_coeMatrix ε)).comp continuous_fst)
      continuous_const).measurableSet.inter (isClosed_closedBall.preimage hΦ).measurableSet
  have h1 : (μ.prod lam) T = μ S * lam O := by
    rw [Measure.prod_apply hT]
    have : ∀ g, lam (Prod.mk g ⁻¹' T) = S.indicator (fun _ => lam O) g := by
      intro g
      by_cases hg : g ∈ S
      · rw [Set.indicator_of_mem hg]
        have hdet : LinearMap.det (leftMulReal (coeMatrixAlt ε g⁻¹)) = 1 := det_leftMulReal_eq_one (g⁻¹).2
        have e : Prod.mk g ⁻¹' T = leftMulReal (coeMatrixAlt ε g⁻¹) ⁻¹' O := by
          ext x
          simp only [T, Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq, Φ]
          exact ⟨fun h => h.2, fun h => ⟨hg, h⟩⟩
        rw [e, Measure.addHaar_preimage_linearMap lam (by rw [hdet]; exact one_ne_zero), hdet]
        simp
      · rw [Set.indicator_of_notMem hg]
        have e : Prod.mk g ⁻¹' T = ∅ := by
          ext x
          simp only [T, Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq,
            Set.mem_empty_iff_false, iff_false, not_and]
          exact fun h => absurd h hg
        rw [e, measure_empty]
    simp_rw [this]
    rw [lintegral_indicator_const hS_meas, mul_comm]
  have hq : (δ / 4) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
  have h2 : (μ.prod lam) T ≤ μ W * lam (closedBall 0 ρ) := by
    rw [Measure.prod_apply_symm hT]
    calc ∫⁻ x, μ ((fun g => (g, x)) ⁻¹' T) ∂lam
        ≤ ∫⁻ x, (closedBall (0 : MatrixCoordinates n) ρ).indicator (fun _ => μ W) x ∂lam := by
          refine lintegral_mono fun x => ?_
          by_cases hne : ((fun g => (g, x)) ⁻¹' T).Nonempty
          · obtain ⟨h, hh⟩ := hne
            have hh1 : hsG h ≤ R ^ 2 := hh.1
            have hh2 := hO _ hh.2
            simp only [Φ] at hh2
            rw [of_leftMulReal_apply] at hh2
            have hx : x ∈ closedBall (0 : MatrixCoordinates n) ρ := by
              rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hρ0]
              intro i
              rw [pi_norm_le_iff_of_nonneg hρ0]
              intro j
              have := entry_le (g := coeMatrixAlt ε h) hR0 hh1 (hh2.trans hq) i j
              rw [← Matrix.mul_assoc, determinant_character_mul_inv, Matrix.one_mul] at this
              exact this
            rw [Set.indicator_of_mem hx]
            calc μ ((fun g => (g, x)) ⁻¹' T) ≤ μ ((fun g => h⁻¹ * g) ⁻¹' W) := by
                  refine measure_mono fun g hg => ?_
                  have hg2 := hO _ hg.2
                  simp only [Φ] at hg2
                  rw [of_leftMulReal_apply] at hg2
                  show hs (coeMatrixAlt ε (h⁻¹ * g) - 1) ≤ δ ^ 2
                  have := near_one (k := coeMatrixAlt ε (h⁻¹ * g)) (by positivity) (by linarith) hg2 hh2 (by
                    rw [determinant_character_mul, ← Matrix.mul_assoc, Matrix.mul_assoc (coeMatrixAlt ε h⁻¹),
                      determinant_character_mul_inv, Matrix.mul_one])
                  rwa [show 4 * (δ / 4) = δ by ring] at this
              _ = μ W := measure_preimage_mul μ h⁻¹ W
          · rw [Set.not_nonempty_iff_eq_empty.1 hne, measure_empty]
            exact bot_le
      _ = μ W * lam (closedBall 0 ρ) := lintegral_indicator_const measurableSet_closedBall _
  have h3 : lam (closedBall 0 ρ) = ENNReal.ofReal (ρ ^ (2 * n ^ 2)) * lam (ball 0 1) := by
    rw [Measure.addHaar_closedBall lam _ hρ0, hfr]
  have hO0 : lam O ≠ 0 := by
    rw [hOv]; exact mul_ne_zero (ENNReal.ofReal_pos.2 (by positivity)).ne' hB_pos.ne'
  have hOt : lam O ≠ ⊤ := measure_closedBall_lt_top.ne
  refine (ENNReal.mul_le_mul_iff_left hO0 hOt).1 ?_
  rw [← h1]
  refine h2.trans (le_of_eq ?_)
  have e : ρ ^ (2 * n ^ 2) = (4 * n * (Real.sqrt n + 1) * R / δ) ^ (2 * n ^ 2) * s ^ (2 * n ^ 2) := by
    rw [← mul_pow]
    congr 1
    rw [hρ, hs_def]
    field_simp
  rw [h3, hOv, e, ENNReal.ofReal_mul (by positivity)]
  ring

theorem one_le_hsG {n : ℕ} (hn : 1 ≤ n) {ε : Fin n → Bool} (g : UJ ε) : 1 ≤ hsG g := by
  let j : Fin n := ⟨0, hn⟩
  have hg : inUJ ε (coeMatrixAlt ε g) := g.2
  have h1 := congrFun (congrFun hg j) j
  have h2 : ((coeMatrixAlt ε g)ᴴ * Jm ε * coeMatrixAlt ε g) j j =
      ∑ i, (if ε i then 1 else -1) * (((‖coeMatrixAlt ε g i j‖ ^ 2 : ℝ)) : ℂ) := by
    simp only [Jm, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := Complex.conj_mul' (coeMatrixAlt ε g i j)
    split_ifs <;> simp [← this]
  have h3 : ‖Jm ε j j‖ = 1 := by simp only [Jm, Matrix.diagonal_apply_eq]; split_ifs <;> simp
  have h4 : (1 : ℝ) ≤ ∑ i, ‖coeMatrixAlt ε g i j‖ ^ 2 := by
    rw [← h3, ← h1, h2]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    split_ifs <;> simp
  refine h4.trans ?_
  show _ ≤ ∑ i, ∑ k, ‖coeMatrixAlt ε g i k‖ ^ 2
  exact Finset.sum_le_sum fun i _ =>
    Finset.single_le_sum (f := fun k => ‖coeMatrixAlt ε g i k‖ ^ 2) (fun k _ => by positivity) (Finset.mem_univ j)

theorem int_ratio {n : ℕ} (hn : 1 ≤ n) (ε : Fin n → Bool) (μ : Measure (UJ ε)) [SFinite μ] [μ.IsMulLeftInvariant]
    {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 2) {A : ℕ} (hA : 2 * n ^ 2 + 1 ≤ A) :
    ∫⁻ g, ENNReal.ofReal ((Real.sqrt (hsG g))⁻¹ ^ A) ∂μ ≤
      ENNReal.ofReal (2 * (8 * n * (Real.sqrt n + 1) / δ) ^ (2 * n ^ 2)) * μ (nearSet ε δ) := by
  set c : ℝ := 8 * n * (Real.sqrt n + 1) / δ with hc
  have hc0 : 0 ≤ c := by positivity
  let S : ℕ → Set (UJ ε) := fun j => {g | hsG g ≤ ((2 : ℝ) ^ (j + 1)) ^ 2}
  have hSm : ∀ j, MeasurableSet (S j) := fun j =>
    (isClosed_le (continuous_hs_real_place_taylor.comp (continuous_coeMatrix ε)) continuous_const).measurableSet
  have hpt : ∀ g : UJ ε, ENNReal.ofReal ((Real.sqrt (hsG g))⁻¹ ^ A) ≤
      ∑' j, (S j).indicator (fun _ => ENNReal.ofReal (((2 : ℝ) ^ j)⁻¹ ^ A)) g := by
    intro g
    have h1 : 1 ≤ Real.sqrt (hsG g) := Real.one_le_sqrt.2 (one_le_hsG hn g)
    obtain ⟨j, hj1, hj2⟩ := exists_nat_pow_near h1 (by norm_num : (1 : ℝ) < 2)
    refine le_trans ?_ (ENNReal.le_tsum j)
    have hmem : g ∈ S j := by
      show hsG g ≤ _
      rw [← Real.sq_sqrt (le_trans zero_le_one (one_le_hsG hn g))]
      exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hj2.le 2
    rw [Set.indicator_of_mem hmem]
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity) (inv_anti₀ (by positivity) hj1) A)
  refine (lintegral_mono hpt).trans ?_
  rw [lintegral_tsum fun j => (measurable_const.indicator (hSm j)).aemeasurable]
  have hterm : ∀ j, ∫⁻ g, (S j).indicator (fun _ => ENNReal.ofReal (((2 : ℝ) ^ j)⁻¹ ^ A)) g ∂μ ≤
      ENNReal.ofReal (c ^ (2 * n ^ 2) * (1 / 2) ^ j) * μ (nearSet ε δ) := by
    intro j
    rw [lintegral_indicator_const (hSm j)]
    refine (mul_le_mul_right (vol_ratio hn ε μ hδ hδ2 (by positivity)) _).trans ?_
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
    have e : 4 * n * (Real.sqrt n + 1) * (2 : ℝ) ^ (j + 1) / δ = c * 2 ^ j := by rw [hc]; ring
    have h2 : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    have h3 : ((2 : ℝ) ^ j)⁻¹ ^ A ≤ ((2 : ℝ) ^ j)⁻¹ ^ (2 * n ^ 2 + 1) :=
      pow_le_pow_of_le_one (by positivity) (inv_le_one_of_one_le₀ h2) hA
    have h4 : ((2 : ℝ) ^ j)⁻¹ ^ (2 * n ^ 2 + 1) * (c * 2 ^ j) ^ (2 * n ^ 2) = c ^ (2 * n ^ 2) * (1 / 2) ^ j := by
      rw [mul_pow, pow_succ, inv_pow, one_div, inv_pow]
      field_simp
    rw [e, ← h4]
    exact mul_le_mul_of_nonneg_right h3 (by positivity)
  refine (ENNReal.tsum_le_tsum hterm).trans (le_of_eq ?_)
  rw [ENNReal.tsum_mul_right, ← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity)
    (summable_geometric_two.mul_left _), tsum_mul_left, tsum_geometric_two, mul_comm (c ^ _)]

end CompanionTheory.Lime.T3
end
end

noncomputable section

open Matrix Finset MeasureTheory Formalism.REAL Formalism.MainNotions.S Filter Topology
open scoped InnerProductSpace ENNReal

namespace CompanionTheory.Lime.T3

open ReciprocityTheory.ChartRestriction.DS (smD smE actM dS IsSmoothVecU mem_smD_iff isDerivedOn_smE dS_eq_actM)

variable {m : ℕ} {ε : Fin m → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {π : Matrix (Fin m) (Fin m) ℂ → (H →L[ℂ] H)}

theorem uMat_inv {m : ℕ} {ε : Fin m → Bool} (g : UJ ε) : uMat g⁻¹ = Jm ε * (uMat g)ᴴ * Jm ε := by
  have hg : (uMat g)ᴴ * Jm ε * uMat g = Jm ε := g.2
  have e : uMat g * uMat g⁻¹ = 1 := determinant_character_mul_inv g
  calc uMat g⁻¹ = Jm ε * Jm ε * uMat g⁻¹ := by rw [Jm_mul_self, Matrix.one_mul]
    _ = Jm ε * ((uMat g)ᴴ * Jm ε * uMat g) * uMat g⁻¹ := by rw [hg]
    _ = Jm ε * (uMat g)ᴴ * Jm ε * (uMat g * uMat g⁻¹) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [e, Matrix.mul_one]

theorem hs_conjJ {m : ℕ} (ε : Fin m → Bool) (M : Matrix (Fin m) (Fin m) ℂ) : hs (Jm ε * Mᴴ * Jm ε) = hs M := by
  unfold hs
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply, norm_mul, norm_star]
  split_ifs <;> simp

theorem hs_inv_sub_one {m : ℕ} {ε : Fin m → Bool} (g : UJ ε) : hs (uMat g⁻¹ - 1) = hs (uMat g - 1) := by
  rw [← hs_conjJ ε (uMat g - 1), uMat_inv, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.mul_sub,
    Matrix.sub_mul, Matrix.mul_one, Jm_mul_self]

section Sup

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem inG_of_curve {c : ℝ → Matrix (Fin m) (Fin m) ℂ} {Y : Matrix (Fin m) (Fin m) ℂ} (h0 : c 0 = 1)
    (hc : HasDerivAt c Y 0) (hG : ∀ᶠ s in 𝓝 (0 : ℝ), inUJ ε (c s)) : inG ε Y := by
  unfold inG
  ext i j
  have he : ∀ a b, HasDerivAt (fun s => c s a b) (Y a b) 0 := fun a b =>
    (hasDerivAt_pi.1 (hasDerivAt_pi.1 hc a) b)
  have h1 : HasDerivAt (fun s => ∑ a, star (c s a i) * (if ε a then 1 else -1) * c s a j)
      (∑ a, (star (Y a i) * (if ε a then 1 else -1) * c 0 a j + star (c 0 a i) * (if ε a then 1 else -1) * Y a j)) 0 :=
    HasDerivAt.fun_sum fun a _ => (((he a i).star).mul_const _).mul (he a j)
  have h2 : (fun s => ∑ a, star (c s a i) * (if ε a then 1 else -1) * c s a j) =ᶠ[𝓝 0] fun _ => Jm ε i j := by
    filter_upwards [hG] with s hs
    rw [← congrFun (congrFun hs i) j]
    simp only [Jm, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have h3 := (h1.congr_of_eventuallyEq h2.symm).unique (hasDerivAt_const _ _)
  rw [Matrix.zero_apply, ← h3, h0, Finset.sum_add_distrib]
  simp only [Jm, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply, Matrix.one_apply,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  congr 1
  rw [Finset.sum_eq_single i (fun a _ ha => by simp [ha]) (by simp), if_pos rfl]
  split_ifs <;> simp

theorem hasDerivAt_curve (hπ : IsURepOn (UJset ε) π) {v : H} (hv : v ∈ smD ε π) {c : ℝ → Matrix (Fin m) (Fin m) ℂ}
    {Y : Matrix (Fin m) (Fin m) ℂ} (h0 : c 0 = 1) (hc : HasDerivAt c Y 0) (hG : ∀ᶠ s in 𝓝 (0 : ℝ), inUJ ε (c s)) :
    HasDerivAt (fun s => π (c s) v) (dS π Y v) 0 := by
  have hY := inG_of_curve h0 hc hG
  have h1 : inUJ ε (1 : Matrix (Fin m) (Fin m) ℂ) := by simp [inUJ]
  obtain ⟨U, F, hU, hU1, hF, hE⟩ := (mem_smD_iff ε π v).1 hv 1 h1
  have hFd : HasFDerivAt F (fderiv ℝ F 1) 1 :=
    ((hF.contDiffAt (hU.mem_nhds hU1)).differentiableAt (by simp)).hasFDerivAt
  have key : ∀ d : ℝ → Matrix (Fin m) (Fin m) ℂ, d 0 = 1 → HasDerivAt d Y 0 → (∀ᶠ s in 𝓝 (0 : ℝ), inUJ ε (d s)) →
      HasDerivAt (fun s => π (d s) v) (fderiv ℝ F 1 Y) 0 := by
    intro d d0 hd hdG
    have a1 : HasDerivAt (F ∘ d) (fderiv ℝ F 1 Y) 0 := HasFDerivAt.comp_hasDerivAt_of_eq 0 hFd hd d0.symm
    refine a1.congr_of_eventuallyEq ?_
    have a2 : ∀ᶠ s in 𝓝 (0 : ℝ), d s ∈ U := hd.continuousAt.eventually (hU.mem_nhds (d0 ▸ hU1))
    filter_upwards [a2, hdG] with s s1 s2
    exact hE _ s1 s2
  have hexp : HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • Y)) Y 0 := by
    have a : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • Y)) (NormedSpace.exp ((0 : ℝ) • Y) * Y) 0 := by
      open scoped Matrix.Norms.Frobenius in exact hasDerivAt_exp_smul_const (𝕂 := ℝ) Y 0
    simpa using a
  have b1 := key _ (by simp) hexp (Filter.Eventually.of_forall fun t => exp_indefinite_unitary_holds m ε Y hY t)
  have b2 := ReciprocityTheory.ChartRestriction.DS.hasDerivAt_dS hπ hY ((mem_smD_iff ε π v).1 hv)
  rw [b2.unique b1]
  exact key c h0 hc hG

end Sup

theorem actM_smul (x : smD ε π) (a : ℝ) (Z : Matrix (Fin m) (Fin m) ℂ) :
    actM (smE ε π) ((a : ℂ) • Z) x = (a : ℂ) • actM (smE ε π) Z x := by
  simp only [actM, LinearMap.sum_apply, LinearMap.smul_apply, Matrix.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

theorem hs_smul (a : ℝ) (Y : Matrix (Fin m) (Fin m) ℂ) : hs ((a : ℂ) • Y) = a ^ 2 * hs Y := by
  simp only [hs, Matrix.smul_apply, norm_smul, mul_pow, Finset.mul_sum, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem eq_zero_of_hs {Y : Matrix (Fin m) (Fin m) ℂ} (h : hs Y = 0) : Y = 0 := by
  ext i j
  have := f1auxiliary_entry_le Y i j
  have h2 : ‖Y i j‖ ^ 2 = 0 := le_antisymm (by linarith) (by positivity)
  simpa using h2

theorem scale_le {M : Type*} [NormedAddCommGroup M] [NormedSpace ℂ M] (T : Matrix (Fin m) (Fin m) ℂ → M)
    (hsm : ∀ (a : ℝ) Z, T ((a : ℂ) • Z) = (a : ℂ) • T Z) {C : ℝ} (hC : ∀ X, hs X ≤ 1 → ‖T X‖ ≤ C)
    (Y : Matrix (Fin m) (Fin m) ℂ) : ‖T Y‖ ≤ Real.sqrt (hs Y) * C := by
  have hs0 : 0 ≤ hs Y := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  rcases hs0.eq_or_lt with h | h
  · have hY : Y = ((0 : ℝ) : ℂ) • Y := by rw [eq_zero_of_hs h.symm, smul_zero]
    rw [← h, hY, hsm]
    simp
  · have hr : 0 < Real.sqrt (hs Y) := Real.sqrt_pos.2 h
    have e : Y = ((Real.sqrt (hs Y) : ℝ) : ℂ) • (((Real.sqrt (hs Y))⁻¹ : ℝ) : ℂ) • Y := by
      rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hr.ne']; simp
    have h1 : hs ((((Real.sqrt (hs Y))⁻¹ : ℝ) : ℂ) • Y) ≤ 1 := by
      rw [hs_smul, inv_pow, Real.sq_sqrt hs0, inv_mul_cancel₀ h.ne']
    conv_lhs => rw [e, hsm, norm_smul, Complex.norm_real, Real.norm_of_nonneg hr.le]
    exact mul_le_mul_of_nonneg_left (hC _ h1) hr.le

theorem norm_dS_le (x : smD ε π) {C : ℝ} (hC : ∀ X, hs X ≤ 1 → ‖actM (smE ε π) X x‖ ≤ C)
    (Y : Matrix (Fin m) (Fin m) ℂ) : ‖actM (smE ε π) Y x‖ ≤ Real.sqrt (hs Y) * C :=
  scale_le (fun X => actM (smE ε π) X x) (actM_smul x) hC Y

section Cayley

open scoped Matrix.Norms.Frobenius

theorem norm_mul_near {x M : Matrix (Fin m) (Fin m) ℂ} {a : ℝ} (hx : ‖x - 1‖ ≤ a) : ‖x * M‖ ≤ (1 + a) * ‖M‖ := by
  calc ‖x * M‖ = ‖M + (x - 1) * M‖ := by congr 1; noncomm_ring
    _ ≤ ‖M‖ + ‖x - 1‖ * ‖M‖ := (norm_add_le _ _).trans (by gcongr; exact norm_mul_le _ _)
    _ ≤ _ := by nlinarith [norm_nonneg M]

theorem norm_mul_near' {x M : Matrix (Fin m) (Fin m) ℂ} {a : ℝ} (hx : ‖x - 1‖ ≤ a) : ‖M * x‖ ≤ (1 + a) * ‖M‖ := by
  calc ‖M * x‖ = ‖M + M * (x - 1)‖ := by congr 1; noncomm_ring
    _ ≤ ‖M‖ + ‖M‖ * ‖x - 1‖ := (norm_add_le _ _).trans (by gcongr; exact norm_mul_le _ _)
    _ ≤ _ := by nlinarith [norm_nonneg M]

theorem sqrt_hs_mul_near {x M : Matrix (Fin m) (Fin m) ℂ} {a : ℝ} (hx : Real.sqrt (hs (x - 1)) ≤ a) :
    Real.sqrt (hs (x * M)) ≤ (1 + a) * Real.sqrt (hs M) := by
  simp only [sqrt_frobenius_eq_norm] at hx ⊢
  exact norm_mul_near hx

theorem cay_facts {h : Matrix (Fin m) (Fin m) ℂ} (hh : inUJ ε h) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2)
    (hD : hs (h - 1) ≤ δ ^ 2) :
    ∃ γ γ' : ℝ → Matrix (Fin m) (Fin m) ℂ, γ 0 = 1 ∧ γ 1 = h ∧ (∀ t ∈ Set.Ioo (-1 : ℝ) 2, inUJ ε (γ t)) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt γ (γ' t) t ∧ Real.sqrt (hs (γ t - 1)) ≤ 5 / 4 ∧
        Real.sqrt (hs (γ' t)) ≤ 3 * δ := by
  set D := h - 1 with hDd
  have hDn : ‖D‖ ≤ δ := by
    rw [frobenius_eq_norm_sq] at hD
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hδ0 two_ne_zero).1 hD
  let A : ℝ → Matrix (Fin m) (Fin m) ℂ := fun t => 1 + ((1 + t) / 2) • D
  let B : ℝ → Matrix (Fin m) (Fin m) ℂ := fun t => 1 + ((1 - t) / 2) • D
  have hBu : ∀ t ∈ Set.Ioo (-1 : ℝ) 2, IsUnit (B t) := by
    intro t ht
    have : ‖-(((1 - t) / 2) • D)‖ < 1 := by
      rw [norm_neg, norm_smul, Real.norm_eq_abs]
      have : |(1 - t) / 2| ≤ 1 := abs_le.2 ⟨by linarith [ht.2], by linarith [ht.1]⟩
      nlinarith [norm_nonneg D, abs_nonneg ((1 - t) / 2)]
    have := (Units.oneSub _ this).isUnit
    simpa [B, sub_neg_eq_add] using this
  have hAB : ∀ t, (A t)ᴴ * Jm ε * A t = (B t)ᴴ * Jm ε * B t := by
    intro t
    have e0 : Dᴴ * Jm ε * D = -(Dᴴ * Jm ε) - Jm ε * D := by
      have : hᴴ * Jm ε * h = Jm ε := hh
      rw [show h = D + 1 by rw [hDd, sub_add_cancel], Matrix.conjTranspose_add, Matrix.conjTranspose_one] at this
      have e : (Dᴴ + 1) * Jm ε * (D + 1) = Dᴴ * Jm ε * D + Dᴴ * Jm ε + Jm ε * D + Jm ε := by noncomm_ring
      rw [e] at this
      have e2 : Dᴴ * Jm ε * D = (Dᴴ * Jm ε * D + Dᴴ * Jm ε + Jm ε * D + Jm ε) - Jm ε - Dᴴ * Jm ε - Jm ε * D := by abel
      rw [e2, this]
      abel
    have e1 : ∀ a : ℝ, (1 + a • D)ᴴ * Jm ε * (1 + a • D) = Jm ε + (a - a * a) • (Dᴴ * Jm ε + Jm ε * D) := by
      intro a
      rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.conjTranspose_smul, star_trivial]
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, e0]
      module
    simp only [A, B, e1]
    congr 2
    ring
  refine ⟨fun t => A t * Ring.inverse (B t), fun t => (1 / 2 : ℝ) • D * Ring.inverse (B t) +
    A t * (Ring.inverse (B t) * ((1 / 2 : ℝ) • D) * Ring.inverse (B t)), ?_, ?_, ?_, ?_⟩
  · have : A 0 = B 0 := by simp [A, B]
    simp only [this]
    exact Ring.mul_inverse_cancel _ (hBu 0 (by norm_num))
  · simp [A, B, hDd]
  · intro t ht
    have hu := Ring.mul_inverse_cancel _ (hBu t ht)
    show (A t * Ring.inverse (B t))ᴴ * Jm ε * (A t * Ring.inverse (B t)) = Jm ε
    calc _ = (Ring.inverse (B t))ᴴ * ((A t)ᴴ * Jm ε * A t) * Ring.inverse (B t) := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = (B t * Ring.inverse (B t))ᴴ * Jm ε * (B t * Ring.inverse (B t)) := by
          rw [hAB, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = Jm ε := by rw [hu]; simp
  · intro t ht
    have ht' : t ∈ Set.Ioo (-1 : ℝ) 2 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    obtain ⟨u, hu⟩ := hBu t ht'
    have dA : HasDerivAt A ((1 / 2 : ℝ) • D) t := by
      have := ((((hasDerivAt_id t).const_add 1).div_const 2).smul_const D).const_add 1
      exact this
    have dB : HasDerivAt B (-((1 / 2 : ℝ) • D)) t := by
      have := ((((hasDerivAt_id t).const_sub 1).div_const 2).smul_const D).const_add 1
      refine this.congr_deriv ?_
      rw [neg_div, neg_smul]
    have dR : HasDerivAt (fun s => Ring.inverse (B s)) (Ring.inverse (B t) * ((1 / 2 : ℝ) • D) * Ring.inverse (B t)) t := by
      have := HasFDerivAt.comp_hasDerivAt_of_eq t (hasFDerivAt_ringInverse (𝕜 := ℝ) u) dB hu
      refine this.congr_deriv ?_
      rw [← hu, Ring.inverse_unit]
      simp
    set R := Ring.inverse (B t) with hR
    have hRn : ‖R - 1‖ ≤ δ := by
      have e : R - 1 = -(((1 - t) / 2) • (D * R)) := by
        have := Ring.mul_inverse_cancel _ (hBu t ht')
        simp only [B, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul] at this
        rw [← this]; simp [hR, B]
      have h2 : |(1 - t) / 2| ≤ 1 / 2 := abs_le.2 ⟨by linarith [ht.2], by linarith [ht.1]⟩
      have h3 : ‖D * R‖ ≤ (1 + ‖R - 1‖) * δ :=
        (norm_mul_near' le_rfl).trans (mul_le_mul_of_nonneg_left hDn (by positivity))
      have h1 : ‖R - 1‖ ≤ 1 / 2 * ((1 + ‖R - 1‖) * δ) := by
        conv_lhs => rw [e, norm_neg, norm_smul, Real.norm_eq_abs]
        exact mul_le_mul h2 h3 (norm_nonneg _) (by norm_num)
      nlinarith [norm_nonneg (R - 1)]
    have hAn : ‖A t - 1‖ ≤ δ := by
      have h2 : |(1 + t) / 2| ≤ 1 := abs_le.2 ⟨by linarith [ht.1], by linarith [ht.2]⟩
      simp only [A, add_sub_cancel_left]
      rw [norm_smul, Real.norm_eq_abs]
      nlinarith [norm_nonneg D, abs_nonneg ((1 + t) / 2)]
    have hHn : ‖(1 / 2 : ℝ) • D‖ ≤ δ / 2 := by rw [norm_smul]; norm_num; linarith
    have hR2 : ‖R - 1‖ ≤ 1 / 2 := hRn.trans hδ
    have hA2 : ‖A t - 1‖ ≤ 1 / 2 := hAn.trans hδ
    refine ⟨dA.mul dR, ?_, ?_⟩
    · rw [sqrt_frobenius_eq_norm]
      calc ‖A t * R - 1‖ = ‖(A t - 1) * R + (R - 1)‖ := by congr 1; noncomm_ring
        _ ≤ (1 + 1 / 2) * ‖A t - 1‖ + ‖R - 1‖ := (norm_add_le _ _).trans (by gcongr; exact norm_mul_near' hR2)
        _ ≤ _ := by linarith
    · rw [sqrt_frobenius_eq_norm]
      have b1 := norm_mul_near' (M := (1 / 2 : ℝ) • D) hR2
      have b2 := norm_mul_near (M := (1 / 2 : ℝ) • D) hR2
      have b3 := norm_mul_near' (M := R * ((1 / 2 : ℝ) • D)) hR2
      have b4 := norm_mul_near (M := R * ((1 / 2 : ℝ) • D) * R) hA2
      have b5 := norm_add_le ((1 / 2 : ℝ) • D * R) (A t * (R * ((1 / 2 : ℝ) • D) * R))
      linarith

end Cayley

theorem disp_le (hπ : IsURepOn (UJset ε) π) (x : smD ε π) {C : ℝ}
    (hC : ∀ X, hs X ≤ 1 → ‖actM (smE ε π) X x‖ ≤ C) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2) {g : UJ ε}
    (hg : g ∈ nearSet ε δ) : ‖π (uMat g) x - x‖ ≤ 7 * δ * C := by
  obtain ⟨γ, γ', h0, h1, hG, hd⟩ := cay_facts g.2 hδ0 hδ hg
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 (by simp [hs]))
  have key : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∃ w : H, HasDerivAt (fun s => π (γ s) (x : H)) w t ∧
      ‖w‖ ≤ 7 * δ * C := by
    intro t ht
    have ht' : t ∈ Set.Ioo (-1 : ℝ) 2 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    obtain ⟨u, hu⟩ : γ t ∈ Set.range fun g : UJ ε => uMat g := by
      rw [(isClosedEmbeddingMatrix m ε).2]; exact hG t ht'
    have hu : uMat u = γ t := hu
    have hev : ∀ᶠ s in 𝓝 (0 : ℝ), inUJ ε (γ (t + s)) := by
      have : ∀ᶠ s in 𝓝 (0 : ℝ), t + s ∈ Set.Ioo (-1 : ℝ) 2 :=
        (continuous_const.add continuous_id).continuousAt.eventually (isOpen_Ioo.mem_nhds (by simpa using ht'))
      exact this.mono fun s hs => hG _ hs
    have hmul : ∀ a b : Matrix (Fin m) (Fin m) ℂ, inUJ ε a → inUJ ε b → inUJ ε (a * b) := by
      intro a b ha hb
      unfold inUJ at *
      rw [Matrix.conjTranspose_mul]
      calc bᴴ * aᴴ * Jm ε * (a * b) = bᴴ * (aᴴ * Jm ε * a) * b := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [ha, hb]
    have hinv : uMat u * uMat u⁻¹ = 1 := determinant_character_mul_inv u
    have hinv' : uMat u⁻¹ * uMat u = 1 := by
      have := determinant_character_mul_inv u⁻¹
      rwa [inv_inv] at this
    have d1 : HasDerivAt (fun s => uMat u⁻¹ * γ (t + s)) (uMat u⁻¹ * γ' t) 0 := by
      have a0 : HasDerivAt γ (γ' t) (t + 0) := by rw [add_zero]; exact (hd t ht).1
      open scoped Matrix.Norms.Frobenius in exact (HasDerivAt.comp_const_add t 0 a0).const_mul (uMat u⁻¹)
    have c0 : uMat u⁻¹ * γ (t + 0) = 1 := by rw [add_zero, ← hu, hinv']
    have hev' : ∀ᶠ s in 𝓝 (0 : ℝ), inUJ ε (uMat u⁻¹ * γ (t + s)) := hev.mono fun s hs => hmul _ _ (u⁻¹).2 hs
    have d2 := hasDerivAt_curve hπ x.2 c0 d1 hev'
    have hY := inG_of_curve c0 d1 hev'
    have d3 := ((π (uMat u)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 d2
    have d4 : HasDerivAt (fun s => π (γ (t + s)) (x : H)) (π (uMat u) (dS π (uMat u⁻¹ * γ' t) x)) 0 := by
      refine d3.congr_of_eventuallyEq ?_
      filter_upwards [hev'] with s hs
      have := hπ.1.2 (uMat u) u.2 _ hs
      rw [← Matrix.mul_assoc, hinv, Matrix.one_mul] at this
      simp [this]
    have d5 : HasDerivAt (fun s => π (γ s) (x : H)) (π (uMat u) (dS π (uMat u⁻¹ * γ' t) x)) t := by
      have := HasDerivAt.comp_sub_const t t (f := fun s => π (γ (t + s)) (x : H)) (by rw [sub_self]; exact d4)
      simpa using this
    refine ⟨_, d5, ?_⟩
    rw [hπ.2.1 _ u.2, dS_eq_actM (isDerivedOn_smE hπ) hY x]
    refine (norm_dS_le x hC _).trans (mul_le_mul_of_nonneg_right ?_ hC0)
    have a1 : Real.sqrt (hs (uMat u⁻¹ - 1)) ≤ 5 / 4 := by
      rw [hs_inv_sub_one, hu]
      exact (hd t ht).2.1
    have a2 := sqrt_hs_mul_near (M := γ' t) a1
    have a3 := (hd t ht).2.2
    linarith
  choose! w hw using key
  have := norm_image_sub_le_of_norm_deriv_le_segment_01' (f := fun s => π (γ s) (x : H)) (f' := w)
    (fun t ht => (hw t ht).1.hasDerivWithinAt) (fun t ht => (hw t (Set.Ico_subset_Icc_self ht)).2)
  simp only [h0, h1] at this
  rwa [hπ.1.1, one_apply_eq_self] at this

end CompanionTheory.Lime.T3
