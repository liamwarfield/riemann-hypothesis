module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PoinStatementPfD

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PoinStatementPfE
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
open scoped ENNReal Matrix ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def idF (X : Data E r) : Frame X.Ψ r := fun _ => (1 : Matrix (Fin r) (Fin r) ℂ)

theorem idF_mem (X : Data E r) : idF X ∈ Bor X.Ψ r := by
  simp only [Bor, Set.mem_setOf_eq]
  intro τ
  refine ⟨?_, fun a c h => ?_⟩
  · have h1 : mat (idF X) τ = 1 := by
      ext i j
      rfl
    rw [h1, Matrix.det_one]
    exact one_ne_zero
  · simp [idF, Matrix.one_apply, ne_of_gt h]

theorem rmul_idF (X : Data E r) (y : Frame X.Ψ r) : rmul y (idF X) = y := by
  funext τ
  show (mat y τ * mat (idF X) τ : Matrix (Fin r) (Fin r) ℂ) = y τ
  have h1 : mat (idF X) τ = 1 := by
    ext i j
    rfl
  rw [h1, mul_one]
  rfl

theorem bchar_idF (X : Data E r) (la : Wt X.Ψ r) : bchar la (idF X) = 1 := by
  simp [bchar, idF]

theorem bchar_contAt (X : Data E r) (la : Wt X.Ψ r) : ContinuousAt (bchar la) (idF X) := by
  unfold bchar
  refine tendsto_finsetProd _ fun τ _ => tendsto_finsetProd _ fun i _ => ?_
  have hc : Continuous fun b : Frame X.Ψ r => b τ i i := by fun_prop
  exact hc.continuousAt.zpow₀ _ (Or.inl (by simp [idF]))

theorem ball_int_bound (X : Data E r) (la : Wt X.Ψ r) {R0 ρ : ℝ}
    (hgood : ∀ w ∈ Metric.ball (0 : V (nd X)) R0, (∀ τ, (mat (nmat X w) τ).det ≠ 0) ∧
      (∀ τ, ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (lminor (Gw X w τ) i).re) ∧ 1 / 2 < nfw X la w)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) (hxo : IsOrth X x) (P : Frame X.Ψ r → ℂ) :
    Metric.ball (0 : V (nd X)) (min R0 ρ) ⊆ Bset X x ρ ∧
      ∫⁻ z in Metric.ball (0 : V (nd X)) (min R0 ρ), ‖P (cpt X x z)‖ₑ ^ 2 ≤ ENNReal.ofReal 4 *
        ∫⁻ w in Bset X x ρ, ‖P (cpt X x w)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-phla X la (cpt X x w))) := by
  have hgoodR := fun w (hw : w ∈ Metric.ball (0 : V (nd X)) (min R0 ρ)) =>
    hgood w (Metric.ball_subset_ball (min_le_left _ _) hw)
  have hmem : Metric.ball (0 : V (nd X)) (min R0 ρ) ⊆ Bset X x ρ := fun w hw => by
    obtain ⟨h1, h2, -⟩ := hgoodR w hw
    exact ⟨lt_of_lt_of_le (mem_ball_zero_iff.1 hw) (min_le_right _ _), cpt_mem_dom X hx hxo h1 h2⟩
  refine ⟨hmem, ?_⟩
  have hpt : ∀ w ∈ Metric.ball (0 : V (nd X)) (min R0 ρ), ‖P (cpt X x w)‖ₑ ^ 2 ≤ ENNReal.ofReal 4 *
      (‖P (cpt X x w)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-phla X la (cpt X x w)))) := by
    intro w hw
    obtain ⟨-, -, h3⟩ := hgoodR w hw
    have hn : X.nfac la (cpt X x w) = nfw X la w := nfac_cpt_orth X la hxo w
    have he : 1 ≤ ENNReal.ofReal 4 * ENNReal.ofReal (Real.exp (-phla X la (cpt X x w))) := by
      rw [exp_neg_phla X la (by rw [hn]; linarith), hn, ← ENNReal.ofReal_mul (by norm_num),
        ← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (by nlinarith)
    calc ‖P (cpt X x w)‖ₑ ^ 2 = ‖P (cpt X x w)‖ₑ ^ 2 * 1 := (mul_one _).symm
      _ ≤ ‖P (cpt X x w)‖ₑ ^ 2 *
          (ENNReal.ofReal 4 * ENNReal.ofReal (Real.exp (-phla X la (cpt X x w)))) := by gcongr
      _ = _ := by ring
  calc ∫⁻ z in Metric.ball (0 : V (nd X)) (min R0 ρ), ‖P (cpt X x z)‖ₑ ^ 2
      ≤ ∫⁻ z in Metric.ball (0 : V (nd X)) (min R0 ρ), ENNReal.ofReal 4 *
          (‖P (cpt X x z)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-phla X la (cpt X x z)))) :=
        setLIntegral_mono' Metric.isOpen_ball.measurableSet hpt
    _ = ENNReal.ofReal 4 * ∫⁻ z in Metric.ball (0 : V (nd X)) (min R0 ρ),
          ‖P (cpt X x z)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-phla X la (cpt X x z))) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := mul_le_mul_of_nonneg_left (lintegral_mono_set hmem) zero_le

theorem subMeanLoc_of (hLU : LUStatement (E := E)) : SubMeanLocStatement (E := E) := by
  intro r X la ρ hρ hρ1 x hx hxo
  obtain ⟨R0, hR0, hgood⟩ := good_ball X la
  have hR : 0 < min R0 ρ := lt_min hR0 hρ
  obtain ⟨Δ, zOf, bOf, hΔ, -, hz, hb, hdec, hinv⟩ := hLU r X x hxo
  have hx0 : (0 : V (nd X)) ∈ OmF X x := by
    show cpt X x 0 ∈ X.dom
    rw [cpt_zero]; exact hx
  obtain ⟨hΔx, hzx, hbx⟩ := hinv 0 hx0 (idF X) (idF_mem X)
  rw [rmul_idF, cpt_zero] at hΔx hzx hbx
  have hOo : IsOpen {y | y ∈ X.dom ∧ Δ y ≠ 0} :=
    (isOpenDom X).inter (isOpen_ne_fun hΔ.continuous continuous_const)
  have hxO : x ∈ {y | y ∈ X.dom ∧ Δ y ≠ 0} := ⟨hx, hΔx⟩
  have hzc : ContinuousAt zOf x := hz.continuousOn.continuousAt (hOo.mem_nhds hxO)
  have hbc : ContinuousAt (fun y => bchar la (bOf y)) x := by
    have h := bchar_contAt X la
    rw [← hbx] at h
    exact h.comp (hb.continuousOn.continuousAt (hOo.mem_nhds hxO))
  have e1 : ∀ᶠ y in 𝓝 x, y ∈ {y | y ∈ X.dom ∧ Δ y ≠ 0} := hOo.mem_nhds hxO
  have e2 : ∀ᶠ y in 𝓝 x, ‖zOf y‖ < min R0 ρ / 2 :=
    hzc.norm.eventually_lt continuousAt_const (by rw [hzx, norm_zero]; positivity)
  have e3 : ∀ᶠ y in 𝓝 x, ‖bchar la (bOf y)‖ < 2 :=
    hbc.norm.eventually_lt continuousAt_const (by rw [hbx, bchar_idF, norm_one]; norm_num)
  obtain ⟨ε, hε, hall⟩ := Metric.eventually_nhds_iff_ball.1 (e1.and (e2.and e3))
  set v := volume (Metric.ball (0 : V (nd X)) (min R0 ρ / 2)) with hv
  have hvpos : v ≠ 0 := (Metric.measure_ball_pos volume _ (by positivity)).ne'
  have hvtop : v ≠ ⊤ := measure_ball_lt_top.ne
  refine ⟨ε, hε, ENNReal.ofReal 4 * v⁻¹ * ENNReal.ofReal 4,
    ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.inv_lt_top.2 (pos_iff_ne_zero.2 hvpos))) ENNReal.ofReal_lt_top, fun P hP y hy => ?_⟩
  obtain ⟨⟨hyd, hΔy⟩, hzy, hby⟩ := hall y hy
  obtain ⟨hzO, hbB, hyeq⟩ := hdec y hyd hΔy
  have hPy : P y = bchar la (bOf y) * P (cpt X x (zOf y)) := by
    conv_lhs => rw [hyeq]
    exact hP.2 _ hzO _ hbB
  have hsub : Metric.ball (zOf y) (min R0 ρ / 2) ⊆ Metric.ball (0 : V (nd X)) (min R0 ρ) := by
    intro w hw
    rw [mem_ball_zero_iff]
    rw [Metric.mem_ball, dist_eq_norm] at hw
    calc ‖w‖ = ‖(w - zOf y) + zOf y‖ := by rw [sub_add_cancel]
      _ ≤ ‖w - zOf y‖ + ‖zOf y‖ := norm_add_le _ _
      _ < min R0 ρ / 2 + min R0 ρ / 2 := add_lt_add hw hzy
      _ = min R0 ρ := by ring
  obtain ⟨hmemB, hint⟩ := ball_int_bound X la hgood hx hxo P
  have hu : DifferentiableOn ℂ (fun w => P (cpt X x w)) (Metric.ball (zOf y) (min R0 ρ / 2)) :=
    hP.1.comp (diff_cpt X x).differentiableOn fun w hw => (hmemB (hsub hw)).2
  have hmv := ReciprocityTheory.L2DbarEstimates.C.mv (nd X) (zOf y) (min R0 ρ / 2) (fun w => P (cpt X x w)) (fun _ => 1)
    hu measurable_const
  simp only [mul_one, one_mul, lintegral_const, Measure.restrict_apply_univ] at hmv
  rw [Measure.addHaar_ball_center] at hmv
  have hle : ‖P (cpt X x (zOf y))‖ₑ ^ 2 ≤
      v⁻¹ * ∫⁻ w in Metric.ball (zOf y) (min R0 ρ / 2), ‖P (cpt X x w)‖ₑ ^ 2 := by
    rw [← ENNReal.div_eq_inv_mul, ENNReal.le_div_iff_mul_le (Or.inl hvpos) (Or.inl hvtop)]
    exact hmv
  have hbb : ‖bchar la (bOf y)‖ₑ ^ 2 ≤ ENNReal.ofReal 4 := by
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (by nlinarith [norm_nonneg (bchar la (bOf y))])
  calc ‖P y‖ₑ ^ 2 = ‖bchar la (bOf y)‖ₑ ^ 2 * ‖P (cpt X x (zOf y))‖ₑ ^ 2 := by
        rw [hPy, enorm_mul, mul_pow]
    _ ≤ ENNReal.ofReal 4 * (v⁻¹ * (ENNReal.ofReal 4 * ∫⁻ w in Bset X x ρ,
          ‖P (cpt X x w)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-phla X la (cpt X x w))))) := by
        refine mul_le_mul' hbb (hle.trans (mul_le_mul_of_nonneg_left ?_ zero_le))
        exact (lintegral_mono_set hsub).trans hint
    _ = _ := by ring

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
end

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
open scoped ENNReal Matrix ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem signature_add_sub_cancel (X : Data E r) : X.p0 + (r - X.p0) = r := by
  have := X.p0_le
  omega

def eS (X : Data E r) : Fin (r - X.p0) ⊕ Fin X.p0 ≃ Fin r :=
  (Equiv.sumComm _ _).trans (finSumFinEquiv.trans (finCongr (signature_add_sub_cancel X)))

theorem eS_inl (X : Data E r) (i : Fin (r - X.p0)) : ((eS X (Sum.inl i)) : ℕ) = X.p0 + i := by
  simp [eS]

theorem eS_inr (X : Data E r) (j : Fin X.p0) : ((eS X (Sum.inr j)) : ℕ) = j := by
  simp [eS]

def gM (X : Data E r) (x0 x : Frame X.Ψ r) (τ : X.Ψ) : Matrix (Fin r) (Fin r) ℂ := (mat x0 τ)⁻¹ * mat x τ

def Mq (X : Data E r) (x0 x : Frame X.Ψ r) (τ : X.Ψ) :
    Matrix (Fin (r - X.p0) ⊕ Fin X.p0) (Fin (r - X.p0) ⊕ Fin X.p0) ℂ :=
  ((gM X x0 x τ).map (starRingEnd ℂ)).submatrix (eS X) (eS X)

theorem Jd_submatrix (X : Data E r) : (Jd X).submatrix (eS X) (eS X) = -Jf (r - X.p0) X.p0 := by
  ext a b
  rcases a with i | j <;> rcases b with k | l <;>
    simp [Jd, Jf, Matrix.diagonal_apply, Matrix.one_apply, sgn, eS_inl, eS_inr, Equiv.apply_eq_iff_eq]
  all_goals (try split_ifs)
  all_goals (try simp_all)

theorem gM_mul (X : Data E r) {x0 : Frame X.Ψ r} (hx0 : IsOrth X x0) (x : Frame X.Ψ r) (τ : X.Ψ) :
    mat x0 τ * gM X x0 x τ = mat x τ := by
  have hgram : ∀ (y : Frame X.Ψ r) (σ : X.Ψ), gram σ.1 X.Gm (mat y σ) =
      (mat y σ)ᵀ * X.Gm.map σ.1 * (mat y σ).map (starRingEnd ℂ) := by
    intro y σ
    ext a b
    simp only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.map_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hdet : ∀ y : Frame X.Ψ r, IsOrth X y → ∀ σ : X.Ψ, IsUnit (mat y σ).det := by
    intro y hy σ
    have h := congrArg Matrix.det (hy σ)
    rw [hgram, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal] at h
    rw [isUnit_iff_ne_zero]
    intro h0
    rw [h0, zero_mul, zero_mul] at h
    refine (Finset.prod_ne_zero_iff.2 fun a _ => ?_) h.symm
    simp only [sgn]
    split_ifs <;> norm_num
  unfold gM
  rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hdet x0 hx0 τ), Matrix.one_mul]

theorem gM_gram (X : Data E r) {x0 x : Frame X.Ψ r} (hx0 : IsOrth X x0) (hx : IsOrth X x) (τ : X.Ψ) :
    (gM X x0 x τ)ᵀ * Jd X * (gM X x0 x τ).map (starRingEnd ℂ) = Jd X := by
  have hgram : ∀ (y : Frame X.Ψ r) (σ : X.Ψ), gram σ.1 X.Gm (mat y σ) =
      (mat y σ)ᵀ * X.Gm.map σ.1 * (mat y σ).map (starRingEnd ℂ) := by
    intro y σ
    ext a b
    simp only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.map_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hdet : ∀ y : Frame X.Ψ r, IsOrth X y → ∀ σ : X.Ψ, IsUnit (mat y σ).det := by
    intro y hy σ
    have h := congrArg Matrix.det (hy σ)
    rw [hgram, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal] at h
    rw [isUnit_iff_ne_zero]
    intro h0
    rw [h0, zero_mul, zero_mul] at h
    refine (Finset.prod_ne_zero_iff.2 fun a _ => ?_) h.symm
    simp only [sgn]
    split_ifs <;> norm_num
  have hmul : mat x τ = mat x0 τ * gM X x0 x τ := by
    unfold gM
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hdet x0 hx0 τ), Matrix.one_mul]
  have h1 := hx τ
  rw [hgram, hmul, Matrix.transpose_mul, Matrix.map_mul] at h1
  have h0 := hx0 τ
  rw [hgram] at h0
  conv_lhs => rw [show Jd X = (mat x0 τ)ᵀ * X.Gm.map τ.1 * (mat x0 τ).map (starRingEnd ℂ) from h0.symm]
  rw [show Jd X = Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) from rfl, ← h1]
  simp only [Matrix.mul_assoc]

theorem Mq_isUpq (X : Data E r) {x0 x : Frame X.Ψ r} (hx0 : IsOrth X x0) (hx : IsOrth X x) (τ : X.Ψ) :
    IsUpq (Mq X x0 x τ) := by
  have hg := gM_gram X hx0 hx τ
  have hJ := Jd_submatrix X
  unfold IsUpq Mq
  have hJf : Jf (r - X.p0) X.p0 = -(Jd X).submatrix (eS X) (eS X) := by rw [hJ, neg_neg]
  rw [hJf]
  have hct : (((gM X x0 x τ).map (starRingEnd ℂ)).submatrix (eS X) (eS X))ᴴ =
      ((gM X x0 x τ)ᵀ).submatrix (eS X) (eS X) := by
    ext a b
    simp [Matrix.conjTranspose_apply, Matrix.transpose_apply]
  rw [hct, Matrix.mul_neg, Matrix.neg_mul, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, hg]

theorem det_lowerBlock_eq_conj_minor (X : Data E r) (x0 x : Frame X.Ψ r) (τ : X.Ψ) :
    (Mq X x0 x τ).toBlocks₂₂.det =
      starRingEnd ℂ (lminor (gM X x0 x τ) ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩) := by
  unfold lminor
  rw [RingHom.map_det]
  congr 1

theorem lminor_mul_upper {n : ℕ} (A N : Matrix (Fin n) (Fin n) ℂ) (hN : N.BlockTriangular id)
    (i : Fin (n + 1)) :
    lminor (A * N) i = lminor A i * ∏ j : Fin i,
      N (Fin.castLE (Nat.le_of_lt_succ i.isLt) j) (Fin.castLE (Nat.le_of_lt_succ i.isLt) j) := by
  unfold lminor
  set e := Fin.castLE (Nat.le_of_lt_succ i.isLt) with he
  have hsub : (A * N).submatrix e e = A.submatrix e e * N.submatrix e e := by
    ext a c
    simp only [Matrix.submatrix_apply, Matrix.mul_apply]
    refine (Fintype.sum_of_injective e (Fin.castLE_injective _) _ _ (fun k hk => ?_) (fun k => rfl)).symm
    have hk' : (i : ℕ) ≤ k := by
      by_contra h
      push_neg at h
      exact hk ⟨⟨k, h⟩, Fin.ext rfl⟩
    apply mul_eq_zero_of_right
    apply hN
    show e c < k
    rw [Fin.lt_iff_val_lt_val, he, Fin.coe_castLE]
    omega
  have hT : (N.submatrix e e).BlockTriangular id := by
    intro a c hac
    apply hN
    show e c < e a
    rw [Fin.lt_iff_val_lt_val, he, Fin.coe_castLE, Fin.coe_castLE]
    exact hac
  rw [hsub, Matrix.det_mul, Matrix.det_of_upperTriangular hT]
  rfl

theorem lminor_nmat (X : Data E r) (z : V (nd X)) (τ : X.Ψ) (i : Fin (r + 1)) :
    lminor (mat (nmat X z) τ) i = 1 := by
  unfold lminor
  rw [Matrix.det_of_lowerTriangular]
  · refine Finset.prod_eq_one fun a _ => ?_
    simp [mat, nmat]
  · intro a c hac
    have hlt : a < c := OrderDual.toDual_lt_toDual.1 hac
    have hlt' : (a : ℕ) < c := hlt
    have h1 : ¬ (Fin.castLE (Nat.le_of_lt_succ i.isLt) c < Fin.castLE (Nat.le_of_lt_succ i.isLt) a) := by
      rw [Fin.lt_iff_val_lt_val, Fin.coe_castLE, Fin.coe_castLE]
      omega
    have h2 : Fin.castLE (Nat.le_of_lt_succ i.isLt) a ≠ Fin.castLE (Nat.le_of_lt_succ i.isLt) c := by
      intro h
      have h3 := congrArg Fin.val h
      rw [Fin.coe_castLE, Fin.coe_castLE] at h3
      omega
    simp only [Matrix.submatrix_apply, mat, Matrix.of_apply, nmat, dif_neg h1, if_neg h2]

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
open scoped ENNReal Matrix ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def i0 (X : Data E r) : Fin (r + 1) := ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩

def rhY (X : Data E r) (x0 y : Frame X.Ψ r) : ℝ :=
  -∑ τ, (Real.log ‖dmin X.Gm y τ (i0 X)‖ - 2 * Real.log ‖lminor (gM X x0 y τ) (i0 X)‖)

def kaY (X : Data E r) (x0 : Frame X.Ψ r) (bb : ℝ) (y : Frame X.Ψ r) : ℝ := Real.exp (-bb * rhY X x0 y)

theorem rhY_cpt (X : Data E r) {x0 : Frame X.Ψ r} (hx0 : IsOrth X x0) (z : V (nd X)) :
    rhY X x0 (cpt X x0 z) = rhF X x0 z := by
  have hgram : ∀ (y : Frame X.Ψ r) (σ : X.Ψ), gram σ.1 X.Gm (mat y σ) =
      (mat y σ)ᵀ * X.Gm.map σ.1 * (mat y σ).map (starRingEnd ℂ) := by
    intro y σ
    ext a b
    simp only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.map_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hdet : ∀ y : Frame X.Ψ r, IsOrth X y → ∀ σ : X.Ψ, IsUnit (mat y σ).det := by
    intro y hy σ
    have h := congrArg Matrix.det (hy σ)
    rw [hgram, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal] at h
    rw [isUnit_iff_ne_zero]
    intro h0
    rw [h0, zero_mul, zero_mul] at h
    refine (Finset.prod_ne_zero_iff.2 fun a _ => ?_) h.symm
    simp only [sgn]
    split_ifs <;> norm_num
  have hgM : ∀ σ : X.Ψ, gM X x0 (cpt X x0 z) σ = mat (nmat X z) σ := by
    intro σ
    show (mat x0 σ)⁻¹ * (mat x0 σ * mat (nmat X z) σ) = _
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hdet x0 hx0 σ), Matrix.one_mul]
  unfold rhY ReciprocityTheory.ChartRestriction.G.AR.Up.rhF
  simp only [hgM, lminor_nmat, norm_one, Real.log_one, mul_zero, sub_zero]
  rfl

theorem kaY_cpt (X : Data E r) {x0 : Frame X.Ψ r} (hx0 : IsOrth X x0) (bb : ℝ) (z : V (nd X)) :
    kaY X x0 bb (cpt X x0 z) = kaF X x0 bb z := by
  unfold kaY ReciprocityTheory.ChartRestriction.G.AR.Up.kaF
  rw [rhY_cpt X hx0 z]

theorem kaY_pos (X : Data E r) (x0 : Frame X.Ψ r) (bb : ℝ) (y : Frame X.Ψ r) : 0 < kaY X x0 bb y := Real.exp_pos _

theorem normSq_Mq (X : Data E r) (x0 x : Frame X.Ψ r) (τ : X.Ψ) :
    Complex.normSq (Mq X x0 x τ).toBlocks₂₂.det = ‖lminor (gM X x0 x τ) (i0 X)‖ ^ 2 := by
  rw [det_lowerBlock_eq_conj_minor, Complex.normSq_conj, Complex.normSq_eq_norm_sq]
  rfl

theorem lminor_orth_ne (X : Data E r) {x0 x : Frame X.Ψ r} (hx0 : IsOrth X x0) (hx : IsOrth X x)
    (τ : X.Ψ) : lminor (gM X x0 x τ) (i0 X) ≠ 0 := by
  have hU := Mq_isUpq X hx0 hx τ
  have hd := det_lowerBlock_eq_conj_minor X x0 x τ
  intro h0
  have hdet0 : (Mq X x0 x τ).toBlocks₂₂.det = 0 := by
    rw [hd]
    exact (map_eq_zero _).2 h0
  unfold IsUpq at hU
  have h22 := congrArg Matrix.toBlocks₂₂ hU
  rw [← Matrix.fromBlocks_toBlocks (Mq X x0 x τ)] at h22
  simp only [Jf, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₂₂,
    Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_neg, add_zero, zero_add] at h22
  set B := (Mq X x0 x τ).toBlocks₁₂
  set D := (Mq X x0 x τ).toBlocks₂₂
  have hDD : Dᴴ * D = 1 + Bᴴ * B := by
    have h2 : Bᴴ * B - Dᴴ * D = -1 := by
      rw [sub_eq_add_neg]
      simpa [Matrix.neg_mul] using h22
    have h3 := congrArg (fun M => Bᴴ * B - M) h2
    simp only [sub_sub_cancel, sub_neg_eq_add] at h3
    rw [h3, add_comm]
  have hne : (1 + Bᴴ * B).det ≠ 0 := by
    open scoped ComplexOrder in
    exact (Matrix.PosDef.one.add_posSemidef (Matrix.posSemidef_conjTranspose_mul_self B)).det_pos.ne'
  rw [← hDD, Matrix.det_mul, hdet0, mul_zero] at hne
  exact hne rfl

theorem gM_rmul (X : Data E r) (x0 y b : Frame X.Ψ r) (τ : X.Ψ) :
    gM X x0 (rmul y b) τ = gM X x0 y τ * mat b τ := by
  unfold gM
  rw [show mat (rmul y b) τ = mat y τ * mat b τ from rfl, Matrix.mul_assoc]

theorem lminor_gM_rmul (X : Data E r) (x0 y : Frame X.Ψ r) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r)
    (τ : X.Ψ) (i : Fin (r + 1)) :
    lminor (gM X x0 (rmul y b) τ) i = lminor (gM X x0 y τ) i * ∏ j : Fin i,
      mat b τ (Fin.castLE (Nat.le_of_lt_succ i.isLt) j) (Fin.castLE (Nat.le_of_lt_succ i.isLt) j) := by
  rw [gM_rmul]
  exact lminor_mul_upper _ _ (fun a c h => (hb τ).2 a c h) i

theorem prod_bdiag_ne (X : Data E r) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) (τ : X.Ψ) (i : Fin (r + 1)) :
    (∏ j : Fin i, mat b τ (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)
      (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)) ≠ 0 := by
  have hT : (mat b τ).BlockTriangular id := fun a c h => (hb τ).2 a c h
  have hd := (hb τ).1
  rw [Matrix.det_of_upperTriangular hT] at hd
  rw [Finset.prod_ne_zero_iff]
  intro j _
  exact (Finset.prod_ne_zero_iff.mp hd) _ (Finset.mem_univ _)

theorem lminor_gM_ne (X : Data E r) {x0 y : Frame X.Ψ r} (hx0 : IsOrth X x0) (hy : y ∈ X.dom)
    (τ : X.Ψ) : lminor (gM X x0 y τ) (i0 X) ≠ 0 := by
  have hb := FrameDegreeData.bOf_mem X hy
  have ho : IsOrth X (rmul y (FrameDegreeData.bOf X y)) := FrameDegreeData.ortho_bOf X hy
  have h := lminor_orth_ne X hx0 ho τ
  rw [lminor_gM_rmul X x0 y hb] at h
  exact left_ne_zero_of_mul h

theorem dmin_ne (X : Data E r) {y : Frame X.Ψ r} (hy : y ∈ X.dom) (τ : X.Ψ) (i : Fin (r + 1)) :
    dmin X.Gm y τ i ≠ 0 := by
  intro h
  have h2 := (hy τ).2 i
  rw [h, Complex.zero_re, mul_zero] at h2
  exact lt_irrefl _ h2

theorem rhY_rmul (X : Data E r) {x0 y : Frame X.Ψ r} (hx0 : IsOrth X x0) (hy : y ∈ X.dom)
    {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) : rhY X x0 (rmul y b) = rhY X x0 y := by
  have hgram : ∀ (y : Frame X.Ψ r) (σ : X.Ψ), gram σ.1 X.Gm (mat y σ) =
      (mat y σ)ᵀ * X.Gm.map σ.1 * (mat y σ).map (starRingEnd ℂ) := by
    intro y σ
    ext a b
    simp only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.map_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hdet : ∀ y : Frame X.Ψ r, IsOrth X y → ∀ σ : X.Ψ, IsUnit (mat y σ).det := by
    intro y hy σ
    have h := congrArg Matrix.det (hy σ)
    rw [hgram, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal] at h
    rw [isUnit_iff_ne_zero]
    intro h0
    rw [h0, zero_mul, zero_mul] at h
    refine (Finset.prod_ne_zero_iff.2 fun a _ => ?_) h.symm
    simp only [sgn]
    split_ifs <;> norm_num
  have hlt : ∀ (N : Matrix (Fin r) (Fin r) ℂ) (i : Fin (r + 1)), lminor Nᵀ i = lminor N i := by
    intro N i
    unfold lminor
    rw [← Matrix.transpose_submatrix, Matrix.det_transpose]
  have hdm : ∀ σ : X.Ψ, dmin X.Gm (rmul y b) σ (i0 X) = dmin X.Gm y σ (i0 X) *
      (∏ j : Fin (i0 X), mat b σ (Fin.castLE (Nat.le_of_lt_succ (i0 X).isLt) j)
        (Fin.castLE (Nat.le_of_lt_succ (i0 X).isLt) j)) *
      starRingEnd ℂ (∏ j : Fin (i0 X), mat b σ (Fin.castLE (Nat.le_of_lt_succ (i0 X).isLt) j)
        (Fin.castLE (Nat.le_of_lt_succ (i0 X).isLt) j)) := by
    intro σ
    unfold dmin
    have e : gram σ.1 X.Gm (mat (rmul y b) σ) =
        (mat b σ)ᵀ * gram σ.1 X.Gm (mat y σ) * (mat b σ).map (starRingEnd ℂ) := by
      rw [hgram, hgram, show mat (rmul y b) σ = mat y σ * mat b σ from rfl, Matrix.transpose_mul,
        Matrix.map_mul]
      simp only [Matrix.mul_assoc]
    have hTb : ((mat b σ).map (starRingEnd ℂ)).BlockTriangular id := fun a c h => by
      simp [Matrix.map_apply, mat, Matrix.of_apply, (hb σ).2 a c h]
    have hTb' : (mat b σ).BlockTriangular id := fun a c h => (hb σ).2 a c h
    have hL : lminor ((mat b σ)ᵀ * gram σ.1 X.Gm (mat y σ)) (i0 X) =
        lminor (gram σ.1 X.Gm (mat y σ)) (i0 X) *
          ∏ j : Fin (i0 X), mat b σ (Fin.castLE (Nat.le_of_lt_succ (i0 X).isLt) j)
            (Fin.castLE (Nat.le_of_lt_succ (i0 X).isLt) j) := by
      rw [← hlt, Matrix.transpose_mul, Matrix.transpose_transpose, lminor_mul_upper _ _ hTb', hlt]
    rw [e, lminor_mul_upper _ _ hTb, hL, map_prod]
    simp only [Matrix.map_apply]
  unfold rhY
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [hdm σ, lminor_gM_rmul X x0 y hb σ (i0 X)]
  have hP := prod_bdiag_ne X hb σ (i0 X)
  have hd := dmin_ne X hy σ (i0 X)
  have hl := lminor_gM_ne X hx0 hy σ
  rw [norm_mul, norm_mul, norm_mul, RCLike.norm_conj,
    Real.log_mul (by positivity) (norm_ne_zero_iff.2 hP),
    Real.log_mul (norm_ne_zero_iff.2 hd) (norm_ne_zero_iff.2 hP),
    Real.log_mul (norm_ne_zero_iff.2 hl) (norm_ne_zero_iff.2 hP)]
  ring

theorem kaY_rmul (X : Data E r) {x0 y : Frame X.Ψ r} (hx0 : IsOrth X x0) (hy : y ∈ X.dom)
    {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) (bb : ℝ) : kaY X x0 bb (rmul y b) = kaY X x0 bb y := by
  unfold kaY
  rw [rhY_rmul X hx0 hy hb]

theorem kaY_orth (X : Data E r) {x0 x : Frame X.Ψ r} (hx0 : IsOrth X x0) (hx : IsOrth X x) (s : ℝ) :
    kaY X x0 s x = ∏ τ, (Complex.normSq (Mq X x0 x τ).toBlocks₂₂.det)⁻¹ ^ s := by
  have hdmin : ∀ σ : X.Ψ, dmin X.Gm x σ (i0 X) = 1 := by
    intro σ
    unfold dmin lminor
    rw [hx σ, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal]
    refine Finset.prod_eq_one fun a _ => ?_
    have ha : ((Fin.castLE (Nat.le_of_lt_succ (i0 X).isLt) a : Fin r) : ℕ) < X.p0 := by
      rw [Fin.coe_castLE]
      exact a.2
    simp only [Function.comp_apply, sgn, if_pos ha]
    norm_num
  have hpos : ∀ σ : X.Ψ, 0 < ‖lminor (gM X x0 x σ) (i0 X)‖ :=
    fun σ => norm_pos_iff.2 (lminor_orth_ne X hx0 hx σ)
  unfold kaY rhY
  simp only [hdmin, norm_one, Real.log_one, zero_sub, Finset.sum_neg_distrib, neg_neg]
  rw [Finset.mul_sum, Real.exp_sum]
  refine Finset.prod_congr rfl fun σ _ => ?_
  have ht := hpos σ
  rw [normSq_Mq, Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity),
    Real.rpow_def_of_pos (by positivity), Real.log_pow]
  congr 1
  push_cast
  ring

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
open scoped ENNReal Matrix ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem orth_mem_dom (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) : x ∈ X.dom := by
  have hgram : ∀ (y : Frame X.Ψ r) (σ : X.Ψ), gram σ.1 X.Gm (mat y σ) =
      (mat y σ)ᵀ * X.Gm.map σ.1 * (mat y σ).map (starRingEnd ℂ) := by
    intro y σ
    ext a b
    simp only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.map_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hdet : ∀ y : Frame X.Ψ r, IsOrth X y → ∀ σ : X.Ψ, IsUnit (mat y σ).det := by
    intro y hy σ
    have h := congrArg Matrix.det (hy σ)
    rw [hgram, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal] at h
    rw [isUnit_iff_ne_zero]
    intro h0
    rw [h0, zero_mul, zero_mul] at h
    refine (Finset.prod_ne_zero_iff.2 fun a _ => ?_) h.symm
    simp only [sgn]
    split_ifs <;> norm_num
  intro τ
  refine ⟨isUnit_iff_ne_zero.1 (hdet x hx τ), fun i => ?_⟩
  have hd : dmin X.Gm x τ i = ((psgn X.p0 i : ℝ) : ℂ) := by
    unfold dmin lminor
    rw [hx τ, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal, psgn,
      Complex.ofReal_prod, Finset.prod_range]
    simp [Fin.coe_castLE]
  rw [hd, Complex.ofReal_re]
  have hne : psgn X.p0 i ≠ 0 := by
    unfold psgn
    refine Finset.prod_ne_zero_iff.2 fun a _ => ?_
    unfold sgn
    split_ifs <;> norm_num
  exact mul_self_pos.2 hne

theorem sep (X : Data E r) {x0 : Frame X.Ψ r} (hx0 : IsOrth X x0) (hPD : PropDisc X) :
    ∃ c > 0, ∀ δ ∈ X.Γ, δ ≠ 1 → ∃ τ a b,
      c ≤ ‖gM X x0 (lact δ x0) τ a b - (1 : Matrix (Fin r) (Fin r) ℂ) a b‖ := by
  classical
  have hd := orth_mem_dom X hx0
  obtain ⟨U, hU, U', hU', hfin⟩ := hPD x0 hd x0 hd
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hU'
  have hne : ∀ δ ∈ X.Γ, δ ≠ 1 → 0 < dist (lact δ x0) x0 := by
    intro δ hδ h1
    refine dist_pos.2 fun h => h1 (X.Γ_free δ hδ x0 hd (idF X) (idF_mem X) ?_)
    rw [rmul_idF]; exact h
  set T := hfin.toFinset.filter (· ≠ 1) with hTdef
  obtain ⟨ε1, hε1, hT⟩ : ∃ ε1 > 0, ∀ δ ∈ T, ε1 ≤ dist (lact δ x0) x0 := by
    rcases T.eq_empty_or_nonempty with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    · obtain ⟨δ0, hδ0, hmin⟩ := T.exists_min_image (fun δ => dist (lact δ x0) x0) h
      have h0 := Finset.mem_filter.1 hδ0
      exact ⟨_, hne δ0 (hfin.mem_toFinset.1 h0.1).1 h0.2, hmin⟩
  set ε' := min ε ε1 with hε'
  have hε'0 : 0 < ε' := lt_min hε hε1
  have hall : ∀ δ ∈ X.Γ, δ ≠ 1 → ε' ≤ dist (lact δ x0) x0 := by
    intro δ hδ h1
    by_cases hS : δ ∈ T
    · exact (min_le_right _ _).trans (hT δ hS)
    · refine (min_le_left _ _).trans (not_lt.1 fun hlt => hS ?_)
      refine Finset.mem_filter.2 ⟨hfin.mem_toFinset.2 ⟨hδ, x0, mem_of_mem_nhds hU, lact δ x0,
        hball (Metric.mem_ball.2 hlt), idF X, idF_mem X, (rmul_idF X _).symm⟩, h1⟩
  set K0 : ℝ := ∑ τ, ∑ a, ∑ k, ‖x0 τ a k‖ + 1 with hK0def
  have hK0 : ∀ τ a k, ‖x0 τ a k‖ ≤ K0 := by
    intro τ a k
    have h1 : ‖x0 τ a k‖ ≤ ∑ k', ‖x0 τ a k'‖ :=
      Finset.single_le_sum (f := fun k' => ‖x0 τ a k'‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ k)
    have h2 : ∑ k', ‖x0 τ a k'‖ ≤ ∑ a', ∑ k', ‖x0 τ a' k'‖ :=
      Finset.single_le_sum (f := fun a' => ∑ k', ‖x0 τ a' k'‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ a)
    have h3 : ∑ a', ∑ k', ‖x0 τ a' k'‖ ≤ ∑ τ', ∑ a', ∑ k', ‖x0 τ' a' k'‖ :=
      Finset.single_le_sum (f := fun τ' => ∑ a', ∑ k', ‖x0 τ' a' k'‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
        (Finset.mem_univ τ)
    linarith
  have hK0pos : 0 < K0 := by
    have : 0 ≤ ∑ τ, ∑ a, ∑ k, ‖x0 τ a k‖ :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
    linarith
  refine ⟨ε' / ((r : ℝ) * K0 + 1), by positivity, fun δ hδ h1 => ?_⟩
  have hdist := hall δ hδ h1
  by_contra hcon
  push Not at hcon
  have hlt : dist (lact δ x0) x0 < ε' := by
    refine (dist_pi_lt_iff hε'0).2 fun τ => (dist_pi_lt_iff hε'0).2 fun a =>
      (dist_pi_lt_iff hε'0).2 fun b => ?_
    rw [dist_eq_norm]
    have hm := congrFun (congrFun (gM_mul X hx0 (lact δ x0) τ) a) b
    have he : lact δ x0 τ a b - x0 τ a b = ∑ k, x0 τ a k *
        (gM X x0 (lact δ x0) τ k b - (1 : Matrix (Fin r) (Fin r) ℂ) k b) := by
      rw [show lact δ x0 τ a b = mat (lact δ x0) τ a b from rfl, ← hm, Matrix.mul_apply]
      simp only [mul_sub, Finset.sum_sub_distrib, Matrix.one_apply, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rfl
    rw [he]
    calc ‖∑ k, x0 τ a k * (gM X x0 (lact δ x0) τ k b - (1 : Matrix (Fin r) (Fin r) ℂ) k b)‖
        ≤ ∑ k, ‖x0 τ a k * (gM X x0 (lact δ x0) τ k b - (1 : Matrix (Fin r) (Fin r) ℂ) k b)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _k : Fin r, K0 * (ε' / ((r : ℝ) * K0 + 1)) := Finset.sum_le_sum fun k _ => by
          rw [norm_mul]
          exact mul_le_mul (hK0 τ a k) (hcon τ k b).le (norm_nonneg _) hK0pos.le
      _ = ε' * ((r : ℝ) * K0 / ((r : ℝ) * K0 + 1)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
      _ < ε' := mul_lt_of_lt_one_right hε'0 ((div_lt_one (by positivity)).2 (lt_add_one _))
  linarith

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
