module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PoinStatementPfF
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.MeasInvStatementPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PairUnfoldPf

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PoinStatementPfH
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PoinStatementPfG
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
open scoped ENNReal Matrix ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem map_conj_inv {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) :
    (A.map (starRingEnd ℂ))⁻¹ = A⁻¹.map (starRingEnd ℂ) := by
  have h1 := (starRingEnd ℂ).map_det A
  have h2 := (starRingEnd ℂ).map_adjugate A
  simp only [RingHom.mapMatrix_apply] at h1 h2
  rw [Matrix.inv_def, Matrix.inv_def, ← h1, ← h2]
  ext i j
  simp [Ring.inverse_eq_inv', map_inv₀]

theorem map_units_inv (τ : E →+* ℂ) (γ : GL (Fin r) E) :
    ((↑(γ⁻¹) : Matrix (Fin r) (Fin r) E).map τ) = ((γ : Matrix (Fin r) (Fin r) E).map τ)⁻¹ := by
  have h : ((↑(γ⁻¹) : Matrix (Fin r) (Fin r) E).map τ) * ((γ : Matrix (Fin r) (Fin r) E).map τ) = 1 := by
    rw [← Matrix.map_mul, Units.inv_mul]
    exact Matrix.map_one _ (map_zero τ) (map_one τ)
  exact (Matrix.inv_eq_left_inv h).symm

private theorem gram_eq_lemma (X : Data E r) (τ : X.Ψ) (M : Matrix (Fin r) (Fin r) ℂ) :
    gram τ.1 X.Gm M = M.transpose * Matrix.map X.Gm τ.1 * M.map (starRingEnd ℂ) := by
  ext a b
  simp only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  exact Finset.sum_comm

private theorem det_mat_ne_zero_of_isOrth_data (X : Data E r) {y : Frame X.Ψ r} (hy : IsOrth X y) (τ : X.Ψ) :
    (mat y τ).det ≠ 0 := by
  intro h0
  have h := congrArg Matrix.det (hy τ)
  rw [gram_eq_lemma, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul, zero_mul,
    Matrix.det_diagonal] at h
  exact (Finset.prod_ne_zero_iff.mpr fun a _ => by unfold sgn; split_ifs <;> norm_num) h.symm

theorem gM_lact_mul (X : Data E r) {x0 x : Frame X.Ψ r} (hx0 : IsOrth X x0) (hx : IsOrth X x)
    (γa γb : GL (Fin r) E) (τ : X.Ψ) :
    gM X x0 (lact γb x) τ * (gM X x0 (lact γa x) τ)⁻¹ = gM X x0 (lact (γb * γa⁻¹) x0) τ := by
  have h0 : IsUnit (mat x0 τ).det := isUnit_iff_ne_zero.mpr (det_mat_ne_zero_of_isOrth_data X hx0 τ)
  have h1 : IsUnit (mat x τ).det := isUnit_iff_ne_zero.mpr (det_mat_ne_zero_of_isOrth_data X hx τ)
  show (mat x0 τ)⁻¹ * ((↑γb : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ) *
      ((mat x0 τ)⁻¹ * ((↑γa : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ))⁻¹ =
    (mat x0 τ)⁻¹ * ((↑(γb * γa⁻¹) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x0 τ)
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ h0, Units.val_mul,
    Matrix.map_mul, map_units_inv]
  simp only [Matrix.mul_assoc]
  rw [Matrix.mul_nonsing_inv_cancel_left _ _ h1]

theorem Mq_div (X : Data E r) {x0 x : Frame X.Ψ r} (hx0 : IsOrth X x0) (hx : IsOrth X x)
    (γa γb : GL (Fin r) E) (τ : X.Ψ) :
    Mq X x0 (lact γb x) τ * (Mq X x0 (lact γa x) τ)⁻¹ = Mq X x0 (lact (γb * γa⁻¹) x0) τ := by
  unfold Mq
  rw [Matrix.inv_submatrix_equiv, Matrix.submatrix_mul_equiv, map_conj_inv, ← Matrix.map_mul,
    gM_lact_mul X hx0 hx]

theorem kaSum (X : Data E r) {x0 : Frame X.Ψ r} (hx0 : IsOrth X x0) (hPD : PropDisc X) {s : ℝ}
    (hs : 2 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < s) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ x, IsOrth X x →
      ∑' γ : X.Γ, ENNReal.ofReal (kaY X x0 s (lact γ.1 x)) ≤ C := by
  obtain ⟨c, hc, hsep⟩ := sep X hx0 hPD
  set f := Fintype.card X.Ψ with hf
  set eΨ : Fin f ≃ X.Ψ := (Fintype.equivFin X.Ψ).symm with heΨ
  have hs' : 2 * (f : ℝ) * (((r - X.p0 + X.p0 : ℕ) : ℝ)) ^ 2 < s := by
    rw [Nat.sub_add_cancel X.p0_le, hf, Fintype.card_coe]; exact hs
  obtain ⟨C, hC, hbd⟩ := sumBd_sum (p := r - X.p0) (q := X.p0) (f := f) hs' hc
  refine ⟨C, hC, fun x hx => ?_⟩
  set xx : X.Γ → Fin f → Matrix (Fin (r - X.p0) ⊕ Fin X.p0) (Fin (r - X.p0) ⊕ Fin X.p0) ℂ :=
    fun γ k => Mq X x0 (lact γ.1 x) (eΨ k) with hxx
  have hU : ∀ a k, IsUpq (xx a k) := fun a k =>
    Mq_isUpq X hx0 (PairUnfoldPf.isOrth_lact X a.2 hx) _
  have hS : ∀ a b : X.Γ, a ≠ b → ∃ k i j,
      c ≤ ‖(xx b k * (xx a k)⁻¹) i j -
        (1 : Matrix (Fin (r - X.p0) ⊕ Fin X.p0) (Fin (r - X.p0) ⊕ Fin X.p0) ℂ) i j‖ := by
    intro a b hab
    have hδ : b.1 * a.1⁻¹ ∈ X.Γ := X.Γ.mul_mem b.2 (X.Γ.inv_mem a.2)
    have hne : b.1 * a.1⁻¹ ≠ 1 := fun h => hab (Subtype.ext (mul_inv_eq_one.1 h).symm)
    obtain ⟨τ, i', j', hij⟩ := hsep _ hδ hne
    refine ⟨eΨ.symm τ, (eS X).symm i', (eS X).symm j', ?_⟩
    simp only [hxx, Equiv.apply_symm_apply]
    rw [Mq_div X hx0 hx]
    unfold Mq
    rw [Matrix.submatrix_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply, Matrix.map_apply]
    have h1 : (1 : Matrix (Fin (r - X.p0) ⊕ Fin X.p0) (Fin (r - X.p0) ⊕ Fin X.p0) ℂ)
        ((eS X).symm i') ((eS X).symm j') = starRingEnd ℂ ((1 : Matrix (Fin r) (Fin r) ℂ) i' j') := by
      simp [Matrix.one_apply, apply_ite]
    rw [h1, ← map_sub, Complex.norm_conj]
    exact hij
  have hsum := hbd X.Γ xx hU hS
  refine le_trans (le_of_eq (tsum_congr fun γ => ?_)) hsum
  rw [kaY_orth X hx0 (PairUnfoldPf.isOrth_lact X γ.2 hx) s]
  congr 1
  exact (Fintype.prod_equiv eΨ _ _ (fun k => rfl)).symm

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
open scoped ENNReal Matrix ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem cs_tsum {ι : Type*} (u v : ι → ℝ≥0∞) :
    ∑' i, u i * v i ≤ (∑' i, u i ^ (2 : ℝ)) ^ (1 / 2 : ℝ) * (∑' i, v i ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  calc ∑ i ∈ s, u i * v i
      ≤ (∑ i ∈ s, u i ^ (2 : ℝ)) ^ (1 / 2 : ℝ) * (∑ i ∈ s, v i ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
        first
          | exact ENNReal.inner_le_Lp_mul_Lq s u v .two_two
          | exact ENNReal.inner_le_Lp_mul_Lq s u v Real.HolderConjugate.two_two
    _ ≤ _ := by
        gcongr
        · exact ENNReal.sum_le_tsum s
        · exact ENNReal.sum_le_tsum s

theorem cs_sq {ι : Type*} (a k : ι → ℝ≥0∞) (hk0 : ∀ i, k i ≠ 0) (hkt : ∀ i, k i ≠ ⊤) :
    (∑' i, a i) ^ 2 ≤ (∑' i, a i ^ 2 / k i) * ∑' i, k i := by
  have hh : ∀ S : ℝ≥0∞, (S ^ (1 / 2 : ℝ)) ^ 2 = S := fun S => by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hsq : ∀ i, (k i ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = k i := fun i => by
    rw [← ENNReal.rpow_mul]
    norm_num
  have hne0 : ∀ i, k i ^ (1 / 2 : ℝ) ≠ 0 := fun i =>
    (ENNReal.rpow_pos (pos_iff_ne_zero.2 (hk0 i)) (hkt i)).ne'
  have hneT : ∀ i, k i ^ (1 / 2 : ℝ) ≠ ⊤ := fun i =>
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) (hkt i)
  have hu : ∀ i, a i = (a i / k i ^ (1 / 2 : ℝ)) * k i ^ (1 / 2 : ℝ) := fun i =>
    (ENNReal.div_mul_cancel (hne0 i) (hneT i)).symm
  have hu2 : ∀ i, (a i / k i ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = a i ^ 2 / k i := fun i => by
    rw [ENNReal.div_rpow_of_nonneg _ _ (by norm_num), hsq, ENNReal.rpow_two]
  calc (∑' i, a i) ^ 2 = (∑' i, (a i / k i ^ (1 / 2 : ℝ)) * k i ^ (1 / 2 : ℝ)) ^ 2 := by
        rw [tsum_congr fun i => hu i]
    _ ≤ ((∑' i, (a i / k i ^ (1 / 2 : ℝ)) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
          (∑' i, (k i ^ (1 / 2 : ℝ)) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) ^ 2 := by
        gcongr
        exact cs_tsum _ _
    _ = (∑' i, a i ^ 2 / k i) * ∑' i, k i := by
        simp only [hu2, hsq]
        rw [mul_pow, hh, hh]

theorem cont_mat (X : Data E r) (τ : X.Ψ) : Continuous fun y : Frame X.Ψ r => mat y τ := by
  refine continuous_matrix fun i j => ?_
  simp only [mat, Matrix.of_apply]
  fun_prop

theorem cont_dmin (X : Data E r) (τ : X.Ψ) (i : Fin (r + 1)) :
    Continuous fun y : Frame X.Ψ r => dmin X.Gm y τ i := by
  unfold dmin lminor gram
  refine Continuous.matrix_det (Continuous.matrix_submatrix ?_ _ _)
  refine continuous_matrix fun a b => ?_
  unfold hermC col mat
  simp only [Matrix.of_apply, Matrix.mul_apply]
  fun_prop

theorem cont_lminor_gM (X : Data E r) (x0 : Frame X.Ψ r) (τ : X.Ψ) (i : Fin (r + 1)) :
    Continuous fun y : Frame X.Ψ r => lminor (gM X x0 y τ) i := by
  unfold lminor gM
  exact Continuous.matrix_det (Continuous.matrix_submatrix (continuous_const.matrix_mul (cont_mat X τ)) _ _)

theorem meas_kaY (X : Data E r) (x0 : Frame X.Ψ r) (bb : ℝ) : Measurable (kaY X x0 bb) := by
  unfold kaY rhY
  refine Real.measurable_exp.comp (measurable_const.mul (Finset.measurable_sum _ fun τ _ => ?_).neg)
  exact ((cont_dmin X τ _).measurable.norm.log).sub
    (measurable_const.mul (cont_lminor_gM X x0 τ _).measurable.norm.log)

theorem ff_holds : FFStatement (E := E) := by
  intro r X x0 la W bb F P H FF hFF
  obtain ⟨hx0, hPD, hW, -, hbb, -, hA, hP, hPF⟩ := H
  classical
  obtain ⟨D⟩ := ExtFPf.luData_of lu_holds X x0 hx0
  have hs : 2 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb := by
    have : 0 ≤ 2 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 := by positivity
    linarith
  obtain ⟨C1, hC1, hsum⟩ := kaSum X hx0 hPD hs
  have hsumY : ∀ y ∈ X.dom, ∑' γ : X.Γ, ENNReal.ofReal (kaY X x0 bb (lact γ.1 y)) ≤ C1 := by
    intro y hy
    have hb := FrameDegreeData.bOf_mem X hy
    have ho : IsOrth X (rmul y (FrameDegreeData.bOf X y)) := FrameDegreeData.ortho_bOf X hy
    refine le_trans (le_of_eq (tsum_congr fun γ => ?_)) (hsum _ ho)
    rw [lact_rmul' γ.1 y (FrameDegreeData.bOf X y),
      kaY_rmul X hx0 ((PairUnfoldPf.lact_mem_dom_iff X γ.2 y).2 hy) hb]
  set Pd := X.dom.indicator P with hPd
  have hPdm : Measurable Pd := PairUnfoldPf.meas_indC X hP.1.continuousOn
  set ψ : Frame X.Ψ r → ℝ≥0∞ := fun y => ‖Pd y‖ₑ ^ 2 * W y / ENNReal.ofReal (kaY X x0 bb y) with hψ
  have hψm : Measurable ψ :=
    ((hPdm.enorm.pow_const 2).mul hW.1).div (meas_kaY X x0 bb).ennreal_ofReal
  have hψB : ∀ y ∈ X.dom, ∀ b ∈ Bor X.Ψ r, ψ (rmul y b) = ψ y := by
    intro y hy b hb
    have hyb : rmul y b ∈ X.dom := rmulDom X hb hy
    simp only [hψ, hPd, Set.indicator_of_mem hyb, Set.indicator_of_mem hy, hP.2 y hy b hb,
      hW.2.1 y hy b hb, kaY_rmul X hx0 hy hb]
    have hpos : 0 < ‖bchar la b‖ ^ 2 := pow_pos (norm_pos_iff.2 (bchar_ne X la hb)) 2
    have h0 : ENNReal.ofReal (‖bchar la b‖ ^ 2) ≠ 0 := (ENNReal.ofReal_pos.2 hpos).ne'
    have ht : ENNReal.ofReal (‖bchar la b‖ ^ 2) ≠ ⊤ := ENNReal.ofReal_ne_top
    have hc : ‖bchar la b‖ₑ ^ 2 = ENNReal.ofReal (‖bchar la b‖ ^ 2) := by
      rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    rw [enorm_mul, mul_pow, hc]
    congr 1
    rw [ENNReal.div_eq_inv_mul]
    calc ENNReal.ofReal (‖bchar la b‖ ^ 2) * ‖P y‖ₑ ^ 2 * ((ENNReal.ofReal (‖bchar la b‖ ^ 2))⁻¹ * W y)
        = (ENNReal.ofReal (‖bchar la b‖ ^ 2) * (ENNReal.ofReal (‖bchar la b‖ ^ 2))⁻¹) *
            (‖P y‖ₑ ^ 2 * W y) := by ring
      _ = ‖P y‖ₑ ^ 2 * W y := by rw [ENNReal.mul_inv_cancel h0 ht, one_mul]
  have hpt : ∀ z ∈ FF, ENNReal.ofReal (‖poin X la P (cpt X x0 z)‖ ^ 2) * W (cpt X x0 z) ≤
      C1 * ∑' γ : X.Γ, ψ (lact γ.1 (cpt X x0 z)) := by
    intro z hz
    have hy : cpt X x0 z ∈ X.dom := hFF.2.1 hz
    have hk0 : ∀ γ : X.Γ, ENNReal.ofReal (kaY X x0 bb (lact γ.1 (cpt X x0 z))) ≠ 0 := fun γ =>
      (ENNReal.ofReal_pos.2 (kaY_pos _ _ _ _)).ne'
    have hkt : ∀ γ : X.Γ, ENNReal.ofReal (kaY X x0 bb (lact γ.1 (cpt X x0 z))) ≠ ⊤ := fun _ =>
      ENNReal.ofReal_ne_top
    have hcs := cs_sq (fun γ : X.Γ => ‖P (lact γ.1 (cpt X x0 z))‖ₑ)
      (fun γ => ENNReal.ofReal (kaY X x0 bb (lact γ.1 (cpt X x0 z)))) hk0 hkt
    have h1 : ENNReal.ofReal (‖poin X la P (cpt X x0 z)‖ ^ 2) ≤
        (∑' γ : X.Γ, ‖P (lact γ.1 (cpt X x0 z))‖ₑ) ^ 2 := by
      rw [ENNReal.ofReal_pow (norm_nonneg _)]
      exact pow_le_pow_left₀ zero_le (enorm_poin_le X la P _) 2
    have h2 : ∀ γ : X.Γ, ‖P (lact γ.1 (cpt X x0 z))‖ₑ ^ 2 /
        ENNReal.ofReal (kaY X x0 bb (lact γ.1 (cpt X x0 z))) * W (cpt X x0 z) =
          ψ (lact γ.1 (cpt X x0 z)) := by
      intro γ
      have hγy : lact γ.1 (cpt X x0 z) ∈ X.dom := (PairUnfoldPf.lact_mem_dom_iff X γ.2 _).2 hy
      simp only [hψ, hPd, Set.indicator_of_mem hγy, hW.2.2 γ.1 γ.2 _ hy]
      rw [ENNReal.mul_div_right_comm]
    calc ENNReal.ofReal (‖poin X la P (cpt X x0 z)‖ ^ 2) * W (cpt X x0 z)
        ≤ ((∑' γ : X.Γ, ‖P (lact γ.1 (cpt X x0 z))‖ₑ ^ 2 /
            ENNReal.ofReal (kaY X x0 bb (lact γ.1 (cpt X x0 z)))) * C1) * W (cpt X x0 z) :=
          mul_le_mul_of_nonneg_right
            (h1.trans (hcs.trans (mul_le_mul_of_nonneg_left (hsumY _ hy) zero_le))) zero_le
      _ = C1 * ∑' γ : X.Γ, ψ (lact γ.1 (cpt X x0 z)) := by
          rw [← tsum_congr h2, ENNReal.tsum_mul_right]; ring
  have hmeasγ : ∀ γ : X.Γ, AEMeasurable (fun z => ψ (lact γ.1 (cpt X x0 z)))
      ((muF X x0).restrict FF) := fun γ =>
    (hψm.comp ((PairUnfoldPf.lact_cont X γ.1).comp (PairUnfoldPf.cpt_cont X x0)).measurable).aemeasurable
  have hunf := PairUnfoldPf.lunfold D FF measInv_holds hx0 hFF ψ hψm hψB
  have hrhs : ∫⁻ z, ψ (cpt X x0 z) ∂muF X x0 =
      ∫⁻ z, ENNReal.ofReal (‖F z‖ ^ 2 / kaF X x0 bb z) * W (cpt X x0 z) ∂muF X x0 := by
    refine lintegral_congr_ae ?_
    filter_upwards [ExtFPf.ae_OmF] with z hz
    have hyd : cpt X x0 z ∈ X.dom := hz
    simp only [hψ, hPd, Set.indicator_of_mem hyd, hPF z hz, kaY_cpt X hx0]
    rw [ENNReal.ofReal_div_of_pos (by unfold kaF; exact Real.exp_pos _), ENNReal.ofReal_pow (norm_nonneg _),
      ofReal_norm, ENNReal.mul_div_right_comm]
  unfold InFF
  calc ∫⁻ z in FF, ENNReal.ofReal (‖poin X la P (cpt X x0 z)‖ ^ 2) * W (cpt X x0 z) ∂muF X x0
      ≤ ∫⁻ z in FF, C1 * ∑' γ : X.Γ, ψ (lact γ.1 (cpt X x0 z)) ∂muF X x0 := setLIntegral_mono' hFF.1 hpt
    _ = C1 * ∑' γ : X.Γ, ∫⁻ z in FF, ψ (lact γ.1 (cpt X x0 z)) ∂muF X x0 := by
        rw [lintegral_const_mul' _ _ hC1.ne, lintegral_tsum hmeasγ]
    _ = C1 * ∫⁻ z, ψ (cpt X x0 z) ∂muF X x0 := by rw [hunf]
    _ < ⊤ := ENNReal.mul_lt_top hC1 (by rw [hrhs]; exact hA)

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
end

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
open scoped ENNReal Matrix ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem det_near_one (n : ℕ) : ∃ η > 0, ∀ A : Matrix (Fin n) (Fin n) ℂ,
    (∀ i j, ‖A i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j‖ < η) → 1 / 2 ≤ ‖A.det‖ := by
  set g : (Fin n → Fin n → ℂ) → ℂ :=
    fun A => ∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ • ∏ i, A (σ i) i with hg
  have hgc : Continuous g := by rw [hg]; fun_prop
  have hgdet : ∀ A : Matrix (Fin n) (Fin n) ℂ, A.det = g A := fun A => Matrix.det_apply A
  set I : Fin n → Fin n → ℂ := (1 : Matrix (Fin n) (Fin n) ℂ) with hI
  have hgI : g I = 1 := by rw [← hgdet]; exact Matrix.det_one
  obtain ⟨η, hη, h⟩ := Metric.continuousAt_iff.1 hgc.continuousAt (1 / 2 : ℝ) (by norm_num)
  refine ⟨η, hη, fun A hA => ?_⟩
  have hd : dist (Matrix.of.symm A) I < η :=
    (dist_pi_lt_iff hη).2 fun i => (dist_pi_lt_iff hη).2 fun j => by rw [dist_eq_norm]; exact hA i j
  have h2 := h hd
  have h4 : g (Matrix.of.symm A) = A.det := (hgdet A).symm
  rw [hgI, h4, dist_eq_norm] at h2
  have h3 := norm_sub_norm_le (1 : ℂ) A.det
  rw [norm_sub_rev, norm_one] at h3
  linarith

theorem diag_re {m n : Type*} [Fintype n] (C : Matrix m n ℂ) (i : m) :
    ((C * Cᴴ) i i).re = ∑ j, Complex.normSq (C i j) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show star (C i j) = (starRingEnd ℂ) (C i j) from rfl, Complex.mul_conj, Complex.ofReal_re]

theorem Kc_entry {p q : ℕ} {M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (h : IsUpq M) (i : Fin q)
    (j : Fin p) : ‖((M.toBlocks₂₂)⁻¹ * M.toBlocks₂₁) i j‖ ≤ 1 := by
  set A := M.toBlocks₂₂ with hA
  set B := M.toBlocks₂₁ with hB
  have hAB : A * Aᴴ = 1 + B * Bᴴ := (sumBdIsUpq_blocks h).2.2.2
  have hU : IsUnit A.det := isUnit_iff_ne_zero.2 (sumBd_weight h).1
  have hK : (A⁻¹ * B) * (A⁻¹ * B)ᴴ = 1 - A⁻¹ * (A⁻¹)ᴴ := by
    have e1 : B * Bᴴ = A * Aᴴ - 1 := by rw [hAB]; abel
    have e2 : Aᴴ * (A⁻¹)ᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, Matrix.nonsing_inv_mul _ hU, Matrix.conjTranspose_one]
    calc (A⁻¹ * B) * (A⁻¹ * B)ᴴ = A⁻¹ * (B * Bᴴ) * (A⁻¹)ᴴ := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = A⁻¹ * A * (Aᴴ * (A⁻¹)ᴴ) - A⁻¹ * (A⁻¹)ᴴ := by
          rw [e1, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = 1 - A⁻¹ * (A⁻¹)ᴴ := by rw [e2, Matrix.nonsing_inv_mul _ hU, Matrix.mul_one]
  have hdiag := congrArg (fun C => (C i i).re) hK
  rw [diag_re, Matrix.sub_apply, Complex.sub_re, diag_re, Matrix.one_apply_eq, Complex.one_re] at hdiag
  have hnn : 0 ≤ ∑ l, Complex.normSq ((A⁻¹) i l) := Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  have hle : Complex.normSq ((A⁻¹ * B) i j) ≤ ∑ l, Complex.normSq ((A⁻¹ * B) i l) :=
    Finset.single_le_sum (f := fun l => Complex.normSq ((A⁻¹ * B) i l))
      (fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ j)
  have h1 : ‖(A⁻¹ * B) i j‖ ^ 2 ≤ 1 := by rw [← Complex.normSq_eq_norm_sq]; linarith
  nlinarith [norm_nonneg ((A⁻¹ * B) i j)]

theorem toBlocks_lowerRight_mul {α β : Type*} [Fintype α] [Fintype β] (M N : Matrix (α ⊕ β) (α ⊕ β) ℂ) :
    (M * N).toBlocks₂₂ = M.toBlocks₂₁ * N.toBlocks₁₂ + M.toBlocks₂₂ * N.toBlocks₂₂ := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks M, ← Matrix.fromBlocks_toBlocks N]
  rw [Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₂₂]

theorem det_split {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β] (M N : Matrix (α ⊕ β) (α ⊕ β) ℂ)
    (hM : M.toBlocks₂₂.det ≠ 0) :
    (M * N).toBlocks₂₂.det =
      M.toBlocks₂₂.det * ((M.toBlocks₂₂)⁻¹ * M.toBlocks₂₁ * N.toBlocks₁₂ + N.toBlocks₂₂).det := by
  rw [toBlocks_lowerRight_mul, ← Matrix.det_mul, Matrix.mul_add]
  congr 2
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hM),
    Matrix.one_mul]

theorem nmat_entry (X : Data E r) (w : V (nd X)) (τ : X.Ψ) (a b : Fin r) :
    ‖mat (nmat X w) τ a b - (1 : Matrix (Fin r) (Fin r) ℂ) a b‖ ≤ ‖w‖ := by
  simp only [mat, nmat, Matrix.of_apply, Matrix.one_apply]
  by_cases h : b < a
  · rw [dite_eq_left h, if_neg (ne_of_lt h).symm, sub_zero]
    exact PiLp.norm_apply_le w _
  · rw [dite_eq_right h]
    split_ifs <;> simp

theorem Mq_cpt (X : Data E r) (x0 x : Frame X.Ψ r) (w : V (nd X)) (τ : X.Ψ) :
    Mq X x0 (cpt X x w) τ =
      Mq X x0 x τ * ((mat (nmat X w) τ).map (starRingEnd ℂ)).submatrix (eS X) (eS X) := by
  unfold Mq
  rw [show cpt X x w = rmul x (nmat X w) from rfl, gM_rmul, Matrix.map_mul,
    ← Matrix.submatrix_mul_equiv _ _ _ (eS X) _]

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
open scoped ENNReal Matrix ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def Nw (X : Data E r) (w : V (nd X)) (τ : X.Ψ) :
    Matrix (Fin (r - X.p0) ⊕ Fin X.p0) (Fin (r - X.p0) ⊕ Fin X.p0) ℂ :=
  ((mat (nmat X w) τ).map (starRingEnd ℂ)).submatrix (eS X) (eS X)

theorem Mq_cpt' (X : Data E r) (x0 x : Frame X.Ψ r) (w : V (nd X)) (τ : X.Ψ) :
    Mq X x0 (cpt X x w) τ = Mq X x0 x τ * Nw X w τ := Mq_cpt X x0 x w τ

theorem N_entries (X : Data E r) (w : V (nd X)) (τ : X.Ψ) (u v : Fin (r - X.p0) ⊕ Fin X.p0) :
    ‖Nw X w τ u v - (1 : Matrix (Fin (r - X.p0) ⊕ Fin X.p0) (Fin (r - X.p0) ⊕ Fin X.p0) ℂ) u v‖ ≤ ‖w‖ := by
  have h1 : (1 : Matrix (Fin (r - X.p0) ⊕ Fin X.p0) (Fin (r - X.p0) ⊕ Fin X.p0) ℂ) u v =
      starRingEnd ℂ ((1 : Matrix (Fin r) (Fin r) ℂ) (eS X u) (eS X v)) := by
    simp [Matrix.one_apply, apply_ite]
  rw [Nw, Matrix.submatrix_apply, Matrix.map_apply, h1, ← map_sub, Complex.norm_conj]
  exact nmat_entry X w τ _ _

theorem pert_entry (X : Data E r) {x0 x : Frame X.Ψ r} (hx0 : IsOrth X x0) (hx : IsOrth X x)
    (w : V (nd X)) (τ : X.Ψ) (i j : Fin X.p0) :
    ‖(((Mq X x0 x τ).toBlocks₂₂)⁻¹ * (Mq X x0 x τ).toBlocks₂₁ * (Nw X w τ).toBlocks₁₂ +
      (Nw X w τ).toBlocks₂₂) i j - (1 : Matrix (Fin X.p0) (Fin X.p0) ℂ) i j‖ ≤ ((r : ℝ) + 1) * ‖w‖ := by
  set K := ((Mq X x0 x τ).toBlocks₂₂)⁻¹ * (Mq X x0 x τ).toBlocks₂₁ with hKdef
  have hK : ∀ i l, ‖K i l‖ ≤ 1 := fun i l => Kc_entry (Mq_isUpq X hx0 hx τ) i l
  have hN12 : ∀ l j, ‖(Nw X w τ).toBlocks₁₂ l j‖ ≤ ‖w‖ := fun l j => by
    have := N_entries X w τ (Sum.inl l) (Sum.inr j)
    simpa [Matrix.toBlocks₁₂, Matrix.one_apply] using this
  have hN22 : ‖(Nw X w τ).toBlocks₂₂ i j - (1 : Matrix (Fin X.p0) (Fin X.p0) ℂ) i j‖ ≤ ‖w‖ := by
    have := N_entries X w τ (Sum.inr i) (Sum.inr j)
    simpa [Matrix.toBlocks₂₂, Matrix.one_apply] using this
  rw [Matrix.add_apply, add_sub_assoc, Matrix.mul_apply]
  have hr : ((r - X.p0 : ℕ) : ℝ) ≤ r := by exact_mod_cast Nat.sub_le r X.p0
  calc ‖∑ l, K i l * (Nw X w τ).toBlocks₁₂ l j +
        ((Nw X w τ).toBlocks₂₂ i j - (1 : Matrix (Fin X.p0) (Fin X.p0) ℂ) i j)‖
      ≤ ‖∑ l, K i l * (Nw X w τ).toBlocks₁₂ l j‖ +
          ‖(Nw X w τ).toBlocks₂₂ i j - (1 : Matrix (Fin X.p0) (Fin X.p0) ℂ) i j‖ := norm_add_le _ _
    _ ≤ ∑ _l : Fin (r - X.p0), ‖w‖ + ‖w‖ := by
        refine add_le_add ((norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)) hN22
        rw [norm_mul]
        calc ‖K i l‖ * ‖(Nw X w τ).toBlocks₁₂ l j‖ ≤ 1 * ‖w‖ :=
              mul_le_mul (hK i l) (hN12 l j) (norm_nonneg _) zero_le_one
          _ = ‖w‖ := one_mul _
    _ ≤ ((r : ℝ) + 1) * ‖w‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        nlinarith [norm_nonneg w]

theorem ka_comp (X : Data E r) {x0 : Frame X.Ψ r} (hx0 : IsOrth X x0) {bb : ℝ} (hbb : 0 ≤ bb) :
    ∃ ρ1 > 0, ∀ x, IsOrth X x → ∀ w : V (nd X), ‖w‖ < ρ1 →
      kaY X x0 bb (cpt X x w) ≤ Real.exp (bb * (3 * X.Ψ.card * Real.log 2)) * kaY X x0 bb x := by
  obtain ⟨η, hη, hdet⟩ := det_near_one X.p0
  have e1 : ∀ᶠ w in 𝓝 (0 : V (nd X)), ∀ τ, ‖lminor (Gw X w τ) (i0 X)‖ < 2 := by
    rw [Filter.eventually_all]; intro τ
    exact (cont_lminor X τ (i0 X)).norm.continuousAt.eventually_lt continuousAt_const
      (by rw [norm_lminor_zero]; norm_num)
  obtain ⟨R1, hR1, hR1b⟩ := Metric.eventually_nhds_iff_ball.1 e1
  refine ⟨min R1 (η / ((r : ℝ) + 1)), lt_min hR1 (by positivity), fun x hx w hw => ?_⟩
  have hwR : w ∈ Metric.ball (0 : V (nd X)) R1 :=
    mem_ball_zero_iff.2 (lt_of_lt_of_le hw (min_le_left _ _))
  have hwη : ((r : ℝ) + 1) * ‖w‖ < η := by
    have := lt_of_lt_of_le hw (min_le_right _ _)
    rwa [lt_div_iff₀ (by positivity), mul_comm] at this
  have hterm : ∀ τ, Real.log ‖dmin X.Gm (cpt X x w) τ (i0 X)‖ -
      2 * Real.log ‖lminor (gM X x0 (cpt X x w) τ) (i0 X)‖ ≤
        3 * Real.log 2 - 2 * Real.log ‖lminor (gM X x0 x τ) (i0 X)‖ := by
    intro τ
    have hA : Real.log ‖dmin X.Gm (cpt X x w) τ (i0 X)‖ ≤ Real.log 2 := by
      rw [dmin_cpt_orth X hx]
      rcases eq_or_lt_of_le (norm_nonneg (lminor (Gw X w τ) (i0 X))) with h0 | h0
      · rw [← h0, Real.log_zero]; exact (Real.log_pos (by norm_num)).le
      · exact Real.log_le_log h0 (hR1b w hwR τ).le
    have hM22 := (sumBd_weight (Mq_isUpq X hx0 hx τ)).1
    have hnorm : ∀ y, ‖lminor (gM X x0 y τ) (i0 X)‖ = ‖(Mq X x0 y τ).toBlocks₂₂.det‖ := fun y => by
      rw [det_lowerBlock_eq_conj_minor, Complex.norm_conj]; rfl
    have hP : 1 / 2 ≤ ‖(((Mq X x0 x τ).toBlocks₂₂)⁻¹ * (Mq X x0 x τ).toBlocks₂₁ *
        (Nw X w τ).toBlocks₁₂ + (Nw X w τ).toBlocks₂₂).det‖ :=
      hdet _ (fun i j => lt_of_le_of_lt (pert_entry X hx0 hx w τ i j) hwη)
    have hpos : 0 < ‖(Mq X x0 x τ).toBlocks₂₂.det‖ := norm_pos_iff.2 hM22
    have hB : Real.log ‖lminor (gM X x0 x τ) (i0 X)‖ - Real.log 2 ≤
        Real.log ‖lminor (gM X x0 (cpt X x w) τ) (i0 X)‖ := by
      rw [hnorm, hnorm, Mq_cpt', det_split _ _ hM22, norm_mul,
        Real.log_mul hpos.ne' (by linarith)]
      have h2 : Real.log (1 / 2) ≤ Real.log ‖(((Mq X x0 x τ).toBlocks₂₂)⁻¹ * (Mq X x0 x τ).toBlocks₂₁ *
          (Nw X w τ).toBlocks₁₂ + (Nw X w τ).toBlocks₂₂).det‖ := Real.log_le_log (by norm_num) hP
      rw [one_div, Real.log_inv] at h2
      linarith
    linarith
  have hrh : rhY X x0 x - 3 * X.Ψ.card * Real.log 2 ≤ rhY X x0 (cpt X x w) := by
    unfold rhY
    simp only [norm_dmin_orth' X hx, Real.log_one, zero_sub]
    have hs : ∑ τ, (Real.log ‖dmin X.Gm (cpt X x w) τ (i0 X)‖ -
        2 * Real.log ‖lminor (gM X x0 (cpt X x w) τ) (i0 X)‖) ≤
          ∑ τ, (3 * Real.log 2 - 2 * Real.log ‖lminor (gM X x0 x τ) (i0 X)‖) :=
      Finset.sum_le_sum fun τ _ => hterm τ
    have e2 : ∑ τ : X.Ψ, (3 * Real.log 2 - 2 * Real.log ‖lminor (gM X x0 x τ) (i0 X)‖) =
        (X.Ψ.card : ℝ) * (3 * Real.log 2) - ∑ τ, 2 * Real.log ‖lminor (gM X x0 x τ) (i0 X)‖ := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
    rw [Finset.sum_neg_distrib]
    linarith
  unfold kaY
  calc Real.exp (-bb * rhY X x0 (cpt X x w))
      ≤ Real.exp (-bb * (rhY X x0 x - 3 * X.Ψ.card * Real.log 2)) := by
        refine Real.exp_le_exp.2 ?_
        have := mul_le_mul_of_nonneg_left hrh hbb
        linarith
    _ = Real.exp (bb * (3 * X.Ψ.card * Real.log 2)) * Real.exp (-bb * rhY X x0 x) := by
        rw [← Real.exp_add]; congr 1; ring

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
end

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
open scoped ENNReal Matrix ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def psiF (X : Data E r) (x0 : Frame X.Ψ r) (bb : ℝ) (P : Frame X.Ψ r → ℂ) (W : Frame X.Ψ r → ℝ≥0∞)
    (y : Frame X.Ψ r) : ℝ≥0∞ :=
  ‖X.dom.indicator P y‖ₑ ^ 2 * W y / ENNReal.ofReal (kaY X x0 bb y)

theorem psiF_meas (X : Data E r) (x0 : Frame X.Ψ r) (bb : ℝ) {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ}
    {W : Frame X.Ψ r → ℝ≥0∞} (hP : IsBEq X la P) (hW : IsMetricW X la W) :
    Measurable (psiF X x0 bb P W) := by
  have h1 : Measurable (X.dom.indicator P) :=
    ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf.meas_indC (X := X) hP.1.continuousOn
  unfold psiF
  exact ((h1.enorm.pow_const 2).mul hW.1).div (ENNReal.measurable_ofReal.comp (meas_kaY X x0 bb))

theorem psiF_rmul (X : Data E r) {x0 : Frame X.Ψ r} (hx0 : IsOrth X x0) (bb : ℝ) {la : Wt X.Ψ r}
    {P : Frame X.Ψ r → ℂ} {W : Frame X.Ψ r → ℝ≥0∞} (hP : IsBEq X la P) (hW : IsMetricW X la W) :
    ∀ y ∈ X.dom, ∀ b ∈ Bor X.Ψ r, psiF X x0 bb P W (rmul y b) = psiF X x0 bb P W y := by
  intro y hy b hb
  have hm : rmul y b ∈ X.dom := by
    first
      | exact OrthogonalFrameDomain.rmul_mem_dom X hy hb
      | exact ReciprocityTheory.ChartRestriction.G.FD.OrthogonalFrameDomain.rmul_mem_dom X hy hb
  unfold psiF
  rw [Set.indicator_of_mem hm, Set.indicator_of_mem hy, hP.2 y hy b hb, hW.2.1 y hy b hb,
    kaY_rmul X hx0 hy hb bb]
  congr 1
  rw [enorm_mul, mul_pow]
  have hne : ‖bchar la b‖ₑ ^ 2 ≠ 0 := pow_ne_zero _ (enorm_ne_zero.2 (bchar_ne X la hb))
  have htop : ‖bchar la b‖ₑ ^ 2 ≠ ⊤ := ENNReal.pow_ne_top enorm_ne_top
  have hof : ENNReal.ofReal (‖bchar la b‖ ^ 2) = ‖bchar la b‖ₑ ^ 2 := by
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  rw [hof, ENNReal.div_eq_inv_mul]
  calc ‖bchar la b‖ₑ ^ 2 * ‖P y‖ₑ ^ 2 * ((‖bchar la b‖ₑ ^ 2)⁻¹ * W y)
      = (‖bchar la b‖ₑ ^ 2 * (‖bchar la b‖ₑ ^ 2)⁻¹) * (‖P y‖ₑ ^ 2 * W y) := by ring
    _ = ‖P y‖ₑ ^ 2 * W y := by rw [ENNReal.mul_inv_cancel hne htop, one_mul]

theorem psiF_mul (X : Data E r) (x0 : Frame X.Ψ r) (bb : ℝ) (P : Frame X.Ψ r → ℂ)
    (W : Frame X.Ψ r → ℝ≥0∞) {y : Frame X.Ψ r} (hy : y ∈ X.dom) :
    psiF X x0 bb P W y * ENNReal.ofReal (kaY X x0 bb y) = ‖P y‖ₑ ^ 2 * W y := by
  unfold psiF
  rw [Set.indicator_of_mem hy, ENNReal.div_mul_cancel (ENNReal.ofReal_pos.2 (kaY_pos X x0 bb y)).ne'
    ENNReal.ofReal_ne_top]

theorem psiF_int (X : Data E r) {x0 : Frame X.Ψ r} (hx0 : IsOrth X x0) (bb : ℝ) {P : Frame X.Ψ r → ℂ}
    {W : Frame X.Ψ r → ℝ≥0∞} {F : V (nd X) → ℂ} (hPF : ∀ z ∈ OmF X x0, P (cpt X x0 z) = F z) :
    ∫⁻ z, psiF X x0 bb P W (cpt X x0 z) ∂muF X x0 =
      ∫⁻ z, ENNReal.ofReal (‖F z‖ ^ 2 / kaF X x0 bb z) * W (cpt X x0 z) ∂muF X x0 := by
  refine lintegral_congr_ae ?_
  filter_upwards [ExtFPf.ae_OmF] with z hz
  have hyd : cpt X x0 z ∈ X.dom := hz
  simp only [psiF, Set.indicator_of_mem hyd, hPF z hz, kaY_cpt X hx0]
  rw [ENNReal.ofReal_div_of_pos (by unfold kaF; exact Real.exp_pos _), ENNReal.ofReal_pow (norm_nonneg _),
    ofReal_norm, ENNReal.mul_div_right_comm]

theorem meas_densF' (X : Data E r) (x' : Frame X.Ψ r) :
    Measurable fun w => ENNReal.ofReal (densF X x' w) := by
  refine ENNReal.measurable_ofReal.comp ?_
  unfold densF
  refine Finset.measurable_prod _ fun τ _ => Finset.measurable_prod _ fun i _ => ?_
  have hc : Measurable fun z : V (nd X) => ‖dmin X.Gm (cpt X x' z) τ i.castSucc‖ ^ 2 :=
    (((cont_dmin X τ _).comp (cont_cpt' X x')).norm.pow 2).measurable
  have e : (fun z : V (nd X) => ‖dmin X.Gm (cpt X x' z) τ i.castSucc‖ ^ (-2 : ℤ)) =
      fun z => (‖dmin X.Gm (cpt X x' z) τ i.castSucc‖ ^ 2)⁻¹ := by
    funext z; rw [zpow_neg, zpow_ofNat]
  rw [e]; exact hc.inv

theorem kaY_half (X : Data E r) (x0 : Frame X.Ψ r) (bb : ℝ) (y : Frame X.Ψ r) :
    ENNReal.ofReal (kaY X x0 bb y) ^ (1 / 2 : ℝ) = ENNReal.ofReal (kaY X x0 (bb / 2) y) := by
  unfold kaY
  rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (by norm_num), ← Real.exp_mul]
  congr 2
  ring

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
open scoped ENNReal Matrix ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem sumBall_holds : SumBallStatement (E := E) := by
  intro r X x0 la W bb F P H
  obtain ⟨hx0, hPD, hW, -, hbb, -, hA, hP, hPF⟩ := H
  classical
  have hbb0 : 0 ≤ bb := by
    have : 0 ≤ 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 := by positivity
    linarith
  obtain ⟨ρ1, hρ1, hcomp⟩ := ka_comp X hx0 hbb0
  have e2 : ∀ᶠ w in 𝓝 (0 : V (nd X)), ∀ τ, ∀ i : Fin r, ‖lminor (Gw X w τ) i.castSucc‖ < 2 := by
    rw [Filter.eventually_all]; intro τ; rw [Filter.eventually_all]; intro i
    exact (cont_lminor X τ _).norm.continuousAt.eventually_lt continuousAt_const
      (by rw [norm_lminor_zero]; norm_num)
  obtain ⟨R2, hR2, hR2b⟩ := Metric.eventually_nhds_iff_ball.1 e2
  set ρ0 := min (min ρ1 R2) 1 with hρ0
  have hρ0pos : 0 < ρ0 := lt_min (lt_min hρ1 hR2) one_pos
  have hs : 2 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb / 2 := by linarith
  obtain ⟨C2, hC2, hsum⟩ := kaSum X hx0 hPD hs
  set K := Real.exp (bb * (3 * X.Ψ.card * Real.log 2)) with hK
  set cd : ℝ := ∏ _τ : X.Ψ, ∏ _i : Fin r, (1 / 4 : ℝ) with hcd
  have hcd0 : 0 < cd := Finset.prod_pos fun _ _ => Finset.prod_pos fun _ _ => by norm_num
  set Nn := ∫⁻ z, ENNReal.ofReal (‖F z‖ ^ 2 / kaF X x0 bb z) * W (cpt X x0 z) ∂muF X x0 with hNn
  set c0 : ℝ≥0∞ := ENNReal.ofReal K * ENNReal.ofReal (1 / cd) * Nn with hc0
  have hc0t : c0 ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hA.ne
  have hψm := psiF_meas X x0 bb hP hW
  have hψB := psiF_rmul X hx0 bb hP hW
  refine ⟨ρ0, hρ0pos, min_le_right _ _, c0 ^ (1 / 2 : ℝ) * C2,
    ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hc0t) hC2, fun x hx hxo => ?_⟩
  have hI : ∀ γ : X.Γ, ∫⁻ w in Bset X x ρ0,
      ‖P (lact γ.1 (cpt X x w))‖ₑ ^ 2 * W (lact γ.1 (cpt X x w)) ≤
        c0 * ENNReal.ofReal (kaY X x0 bb (lact γ.1 x)) := by
    intro γ
    set x' := lact γ.1 x with hx'
    have hx'o : IsOrth X x' := PairUnfoldPf.isOrth_lact X γ.2 hxo
    have hcptl : ∀ w, lact γ.1 (cpt X x w) = cpt X x' w := fun w =>
      (PairUnfoldPf.cpt_lact X γ.1 x w).symm
    simp only [hcptl]
    have hdom : ∀ w ∈ Bset X x ρ0, cpt X x' w ∈ X.dom := fun w hw => by
      rw [← hcptl]; exact (PairUnfoldPf.lact_mem_dom_iff X γ.2 _).2 hw.2
    set A := ENNReal.ofReal K * ENNReal.ofReal (kaY X x0 bb x') * ENNReal.ofReal (1 / cd) with hAdef
    have hpt : ∀ w ∈ Bset X x ρ0, ‖P (cpt X x' w)‖ₑ ^ 2 * W (cpt X x' w) ≤
        A * (ENNReal.ofReal (densF X x' w) * psiF X x0 bb P W (cpt X x' w)) := by
      intro w hw
      have hyd := hdom w hw
      have hw1 : ‖w‖ < ρ1 := lt_of_lt_of_le hw.1 ((min_le_left _ _).trans (min_le_left _ _))
      have hw2 : w ∈ Metric.ball (0 : V (nd X)) R2 :=
        mem_ball_zero_iff.2 (lt_of_lt_of_le hw.1 ((min_le_left _ _).trans (min_le_right _ _)))
      have hka := hcomp x' hx'o w hw1
      have hdens : cd ≤ densF X x' w := by
        unfold densF
        refine Finset.prod_le_prod₀ (fun _ _ => by positivity) fun τ _ =>
          Finset.prod_le_prod₀ (fun _ _ => by norm_num) fun i _ => ?_
        rw [dmin_cpt_orth X hx'o]
        have h0 : 0 < ‖lminor (Gw X w τ) i.castSucc‖ := by
          rw [← dmin_cpt_orth X hx'o]; exact norm_pos_iff.2 (dmin_ne X hyd τ _)
        have h2 := hR2b w hw2 τ i
        rw [zpow_neg, zpow_ofNat, show (1 / 4 : ℝ) = ((2 : ℝ) ^ 2)⁻¹ by norm_num]
        exact inv_anti₀ (by positivity) (pow_le_pow_left₀ h0.le h2.le 2)
      have hden : 1 ≤ ENNReal.ofReal (1 / cd) * ENNReal.ofReal (densF X x' w) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_one]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [one_div_mul_eq_div, le_div_iff₀ hcd0]
        linarith
      have hkk : ENNReal.ofReal (kaY X x0 bb (cpt X x' w)) ≤
          ENNReal.ofReal K * ENNReal.ofReal (kaY X x0 bb x') := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]; exact ENNReal.ofReal_le_ofReal hka
      rw [← psiF_mul X x0 bb P W hyd]
      calc psiF X x0 bb P W (cpt X x' w) * ENNReal.ofReal (kaY X x0 bb (cpt X x' w))
          ≤ psiF X x0 bb P W (cpt X x' w) * (ENNReal.ofReal K * ENNReal.ofReal (kaY X x0 bb x')) :=
            mul_le_mul_of_nonneg_left hkk zero_le
        _ = psiF X x0 bb P W (cpt X x' w) * (ENNReal.ofReal K * ENNReal.ofReal (kaY X x0 bb x')) * 1 :=
            (mul_one _).symm
        _ ≤ psiF X x0 bb P W (cpt X x' w) * (ENNReal.ofReal K * ENNReal.ofReal (kaY X x0 bb x')) *
              (ENNReal.ofReal (1 / cd) * ENNReal.ofReal (densF X x' w)) :=
            mul_le_mul_of_nonneg_left hden zero_le
        _ = A * (ENNReal.ofReal (densF X x' w) * psiF X x0 bb P W (cpt X x' w)) := by
            rw [hAdef]; ring
    have hsub : Bset X x ρ0 ⊆ OmF X x' := fun w hw => hdom w hw
    have hAt : A ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top
    calc ∫⁻ w in Bset X x ρ0, ‖P (cpt X x' w)‖ₑ ^ 2 * W (cpt X x' w)
        ≤ ∫⁻ w in Bset X x ρ0, A * (ENNReal.ofReal (densF X x' w) * psiF X x0 bb P W (cpt X x' w)) :=
          setLIntegral_mono' (isOpen_Bset X x ρ0).measurableSet hpt
      _ = A * ∫⁻ w in Bset X x ρ0, ENNReal.ofReal (densF X x' w) * psiF X x0 bb P W (cpt X x' w) :=
          lintegral_const_mul' _ _ hAt
      _ ≤ A * ∫⁻ w in OmF X x', ENNReal.ofReal (densF X x' w) * psiF X x0 bb P W (cpt X x' w) :=
          mul_le_mul_of_nonneg_left (lintegral_mono_set hsub) zero_le
      _ = A * ∫⁻ w, psiF X x0 bb P W (cpt X x' w) ∂muF X x' := by
          have hm : Measurable fun w => psiF X x0 bb P W (cpt X x' w) :=
            hψm.comp (cont_cpt' X x').measurable
          rw [muF, lintegral_withDensity_eq_lintegral_mul _ (meas_densF' X x') hm]
          rfl
      _ = A * Nn := by
          rw [measInv_holds r X x' x0 hx'o hx0 _ hψm hψB, psiF_int X hx0 bb hPF]
      _ = c0 * ENNReal.ofReal (kaY X x0 bb x') := by rw [hAdef, hc0]; ring
  calc ∑' γ : X.Γ, (∫⁻ w in Bset X x ρ0,
        ‖P (lact γ.1 (cpt X x w))‖ₑ ^ 2 * W (lact γ.1 (cpt X x w))) ^ (1 / 2 : ℝ)
      ≤ ∑' γ : X.Γ, (c0 * ENNReal.ofReal (kaY X x0 bb (lact γ.1 x))) ^ (1 / 2 : ℝ) :=
        ENNReal.tsum_le_tsum fun γ => ENNReal.rpow_le_rpow (hI γ) (by norm_num)
    _ = ∑' γ : X.Γ, c0 ^ (1 / 2 : ℝ) * ENNReal.ofReal (kaY X x0 (bb / 2) (lact γ.1 x)) :=
        tsum_congr fun γ => by rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), kaY_half]
    _ = c0 ^ (1 / 2 : ℝ) * ∑' γ : X.Γ, ENNReal.ofReal (kaY X x0 (bb / 2) (lact γ.1 x)) :=
        ENNReal.tsum_mul_left
    _ ≤ c0 ^ (1 / 2 : ℝ) * C2 := mul_le_mul_of_nonneg_left (hsum x hxo) zero_le

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
