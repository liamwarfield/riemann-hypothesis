module

public import GroundTheory.HeightsAndTheta.Heights.Regularisation.PGlueRegularised
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.PExpExtension
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.PosSemidefOfIntQuadNonneg
public import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PAnalyticDerivBound

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.Regularisation.PHodgeDerivative
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open Metric Filter Topology Matrix
open GroundTheory.Heights₂.Heights.MCBounds GroundTheory.Heights₂.Heights.MCDet
open scoped ComplexOrder

noncomputable section

namespace HodgeDerivative

theorem norm_coord_lt {n : ℕ} {z : Fin n → ℂ} (hz : z ∈ ball (0 : Fin n → ℂ) 1) (k : Fin n) :
    ‖z k‖ < 1 :=
  (norm_le_pi_norm z k).trans_lt (mem_ball_zero_iff.mp hz)

theorem isOpen_punctured {n a : ℕ} (h : a ≤ n) :
    IsOpen (puncturedChart h (ball (0 : Fin n → ℂ) 1)) := by
  have e : puncturedChart h (ball (0 : Fin n → ℂ) 1) =
      ball 0 1 ∩ ⋂ j : Fin a, {z : Fin n → ℂ | z (Fin.castLE h j) ≠ 0} := by
    ext z
    simp [puncturedChart, cuspCoord]
  rw [e]
  exact isOpen_ball.inter
    (isOpen_iInter_of_finite fun j => isOpen_ne_fun (continuous_apply _) continuous_const)

theorem logLift_mem {n a : ℕ} (h : a ≤ n) {z : Fin n → ℂ}
    (hz : z ∈ puncturedChart h (ball (0 : Fin n → ℂ) 1)) : logLift a z ∈ logCover h := by
  refine ⟨fun i => ?_, fun k hk => ?_⟩
  · have hi : (Fin.castLE h i).val < a := i.isLt
    have h0 : z (Fin.castLE h i) ≠ 0 := hz.2 i
    simp only [logLift, if_pos hi, Complex.log_re]
    exact Real.log_neg (norm_pos_iff.mpr h0) (norm_coord_lt hz.1 _)
  · simp only [logLift, if_neg (not_lt.mpr hk)]
    exact norm_coord_lt hz.1 k

theorem expCover_logLift {n a : ℕ} (h : a ≤ n) {z : Fin n → ℂ} (hz : ∀ j, cuspCoord h z j ≠ 0) :
    expCover a (logLift a z) = z := by
  funext k
  by_cases hk : k.val < a
  · have e : Fin.castLE h ⟨k.val, hk⟩ = k := Fin.ext rfl
    have h0 : z k ≠ 0 := by
      have := hz ⟨k.val, hk⟩
      rwa [cuspCoord, e] at this
    simp only [expCover, logLift, if_pos hk, Complex.exp_log h0]
  · simp only [expCover, logLift, if_neg hk]

theorem imTau_eq {n a g : ℕ} (P : PeriodPolydisc n a g) {T0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ}
    (hT : P.IsTau0Ext T0) {z : Fin n → ℂ} (hz : z ∈ puncturedChart P.a_le (ball (0 : Fin n → ℂ) 1)) :
    P.imTau z = chartImag P.a_le T0 (fun i => (P.B i).map (Int.cast : ℤ → ℝ)) z := by
  have hw := logLift_mem P.a_le hz
  have h0 : P.tau0 (logLift a z) = T0 z := by
    rw [hT.2 _ hw, expCover_logLift P.a_le hz.2]
  have hτ : P.τ (logLift a z) = T0 z + ∑ i : Fin a,
      (logLift a z (Fin.castLE P.a_le i) / (2 * Real.pi * Complex.I)) •
        (P.B i).map (Int.cast : ℤ → ℂ) := by
    rw [← h0, PeriodPolydisc.tau0, sub_add_cancel]
  ext p q
  simp only [PeriodPolydisc.imTau, hτ, chartImag, map_apply, Matrix.add_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, Complex.add_im, Complex.im_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi : (Fin.castLE P.a_le i).val < a := i.isLt
  simp only [logLift, if_pos hi, Complex.mul_im, Complex.intCast_re, Complex.intCast_im, mul_zero,
    zero_add, im_div_two_pi_I, Complex.log_re, cuspTime, cuspCoord, Real.log_inv]
  ring

theorem logNorm_hasFDerivAt {x : ℂ} (hx : x ≠ 0) :
    ∃ L : ℂ →L[ℝ] ℝ, HasFDerivAt (fun y : ℂ => Real.log ‖y‖) L x ∧ ‖L‖ ≤ ‖x‖⁻¹ := by
  have hx2 : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hx)
  have h1 := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.log hx2).const_mul (2⁻¹ : ℝ)
  have e : (fun y : ℂ => 2⁻¹ * Real.log (‖y‖ ^ 2)) = fun y : ℂ => Real.log ‖y‖ := by
    funext y
    rw [Real.log_pow]
    push_cast
    ring
  rw [e] at h1
  refine ⟨_, h1, ?_⟩
  rw [two_nsmul, ← two_smul ℝ]
  rw [norm_smul, norm_smul, norm_smul, innerSL_apply_norm, Real.norm_eq_abs, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2⁻¹), abs_of_pos (by norm_num : (0:ℝ) < 2),
    abs_of_pos (inv_pos.mpr (by positivity))]
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  apply le_of_eq
  field_simp

theorem cuspTime_hasFDerivAt {n a : ℕ} (h : a ≤ n) (i : Fin a) {z : Fin n → ℂ}
    (hz : cuspCoord h z i ≠ 0) :
    ∃ L : (Fin n → ℂ) →L[ℝ] ℝ, HasFDerivAt (fun y => cuspTime h y i) L z ∧
      ‖L‖ ≤ ‖cuspCoord h z i‖⁻¹ := by
  obtain ⟨L, hL, hLn⟩ := logNorm_hasFDerivAt hz
  have hp : HasFDerivAt (fun y : Fin n → ℂ => y (Fin.castLE h i))
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) (Fin.castLE h i)) z :=
    hasFDerivAt_apply _ _
  have h2 := (hL.comp z hp).const_mul (-(2 * Real.pi)⁻¹)
  have e : (fun y : Fin n → ℂ => -(2 * Real.pi)⁻¹ * (Real.log ‖y (Fin.castLE h i)‖)) =
      fun y => cuspTime h y i := by
    funext y
    simp only [cuspTime, cuspCoord, Real.log_inv]
    ring
  rw [Function.comp_def, e] at h2
  refine ⟨_, h2, ?_⟩
  have hproj : ‖ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) (Fin.castLE h i)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
      simpa using norm_le_pi_norm v (Fin.castLE h i)
  have hpi : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hc : ‖(-(2 * Real.pi)⁻¹ : ℝ)‖ ≤ 1 := by
    rw [norm_neg, Real.norm_eq_abs, abs_of_pos (by positivity)]
    exact inv_le_one_of_one_le₀ hpi
  calc ‖(-(2 * Real.pi)⁻¹ : ℝ) • L.comp _‖
      ≤ ‖(-(2 * Real.pi)⁻¹ : ℝ)‖ * (‖L‖ * 1) := by
        rw [norm_smul]
        gcongr
        exact (L.opNorm_comp_le _).trans (by gcongr)
    _ ≤ 1 * (‖cuspCoord h z i‖⁻¹ * 1) := by gcongr
    _ = ‖cuspCoord h z i‖⁻¹ := by ring

theorem im_hasFDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℂ} {x : E}
    (hf : DifferentiableAt ℝ f x) :
    HasFDerivAt (fun y => (f y).im) (Complex.imCLM.comp (fderiv ℝ f x)) x ∧
      ‖Complex.imCLM.comp (fderiv ℝ f x)‖ ≤ ‖fderiv ℝ f x‖ := by
  refine ⟨Complex.imCLM.hasFDerivAt.comp x hf.hasFDerivAt, ?_⟩
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
  simp only [ContinuousLinearMap.comp_apply, Complex.imCLM_apply, Real.norm_eq_abs]
  exact (Complex.abs_im_le_norm _).trans ((fderiv ℝ f x).le_opNorm v)

theorem one_add_sum_le {n a : ℕ} (h : a ≤ n) {z : Fin n → ℂ}
    (hz : z ∈ puncturedChart h (ball (0 : Fin n → ℂ) 1)) :
    1 + ∑ i, ‖cuspCoord h z i‖⁻¹ ≤ (1 + a) * Real.exp (chartRadius h z / 2) := by
  have hlt : ∀ j, ‖cuspCoord h z j‖ < 1 := fun j => norm_coord_lt hz.1 _
  have hnn : ∀ j, 0 ≤ Real.log (‖cuspCoord h z j‖ ^ 2)⁻¹ := fun j => log_inv_sq_nonneg (hlt j)
  have hr0 : 0 ≤ chartRadius h z :=
    add_nonneg (Real.exp_pos 1).le (Finset.sum_nonneg fun j _ => hnn j)
  have h1 : 1 ≤ Real.exp (chartRadius h z / 2) := Real.one_le_exp (by linarith)
  have hi : ∀ i, ‖cuspCoord h z i‖⁻¹ ≤ Real.exp (chartRadius h z / 2) := by
    intro i
    have hpos : 0 < ‖cuspCoord h z i‖ := norm_pos_iff.mpr (hz.2 i)
    have e1 : Real.log (‖cuspCoord h z i‖ ^ 2)⁻¹ = 2 * Real.log ‖cuspCoord h z i‖⁻¹ := by
      rw [Real.log_inv, Real.log_inv, Real.log_pow]
      push_cast
      ring
    have hs := Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ i)
    have hle : Real.log ‖cuspCoord h z i‖⁻¹ ≤ chartRadius h z / 2 := by
      unfold chartRadius
      rw [e1] at hs
      linarith [Real.exp_pos 1]
    calc ‖cuspCoord h z i‖⁻¹ = Real.exp (Real.log ‖cuspCoord h z i‖⁻¹) :=
          (Real.exp_log (inv_pos.mpr hpos)).symm
      _ ≤ _ := Real.exp_le_exp.mpr hle
  have hs : ∑ i, ‖cuspCoord h z i‖⁻¹ ≤ a * Real.exp (chartRadius h z / 2) := by
    calc ∑ i, ‖cuspCoord h z i‖⁻¹ ≤ ∑ _i : Fin a, Real.exp (chartRadius h z / 2) :=
          Finset.sum_le_sum fun i _ => hi i
      _ = a * Real.exp (chartRadius h z / 2) := by simp
  linarith

theorem one_le_chartRadius {n a : ℕ} (h : a ≤ n) {z : Fin n → ℂ}
    (hz : z ∈ puncturedChart h (ball (0 : Fin n → ℂ) 1)) : 1 ≤ chartRadius h z := by
  have : 0 ≤ ∑ j, Real.log (‖cuspCoord h z j‖ ^ 2)⁻¹ :=
    Finset.sum_nonneg fun j _ => log_inv_sq_nonneg (norm_coord_lt hz.1 _)
  unfold chartRadius
  linarith [Real.add_one_le_exp (1 : ℝ)]

theorem chartImag_entry_deriv {n a g : ℕ} (h : a ≤ n) (T0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ)
    (B : Fin a → Matrix (Fin g) (Fin g) ℝ) (p q : Fin g) {z : Fin n → ℂ}
    (hz : ∀ j, cuspCoord h z j ≠ 0) (hT : DifferentiableAt ℝ (fun y => T0 y p q) z) :
    DifferentiableAt ℝ (fun y => chartImag h T0 B y p q) z ∧
      ‖fderiv ℝ (fun y => chartImag h T0 B y p q) z‖ ≤
        ‖fderiv ℝ (fun y => T0 y p q) z‖ + ∑ i, |B i p q| * ‖cuspCoord h z i‖⁻¹ := by
  have e : (fun y => chartImag h T0 B y p q) =
      fun y => (T0 y p q).im + ∑ i, cuspTime h y i * B i p q := by
    funext y
    simp [chartImag, Matrix.sum_apply]
  choose L hL hLn using fun i => cuspTime_hasFDerivAt h i (hz i)
  obtain ⟨h0, h0n⟩ := im_hasFDerivAt hT
  have hsum : HasFDerivAt (fun y => ∑ i, cuspTime h y i * B i p q) (∑ i, B i p q • L i) z :=
    (HasFDerivAt.sum (u := Finset.univ) (A := fun i y => cuspTime h y i * B i p q)
      fun i _ => (hL i).mul_const (B i p q)).congr_of_eventuallyEq
        (Eventually.of_forall fun y => by simp only [Finset.sum_apply])
  have hall : HasFDerivAt (fun y => (T0 y p q).im + ∑ i, cuspTime h y i * B i p q)
      (Complex.imCLM.comp (fderiv ℝ (fun y => T0 y p q) z) + ∑ i, B i p q • L i) z := h0.add hsum
  rw [e]
  refine ⟨hall.differentiableAt, ?_⟩
  rw [hall.fderiv]
  refine (norm_add_le _ _).trans (add_le_add h0n ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hLn i) (abs_nonneg _)

end HodgeDerivative


open HodgeDerivative in
theorem HodgeDerivative.proof (h0 : ImTauBounds.Statement) (h1 : Tau0Holomorphic.Statement)
    (hAn : AnalyticDerivBound.Statement) (hInv : InvEntryDeriv.Statement)
    (hLDG : LogDetGramDeriv.Statement) : HodgeDerivative.Statement := by
  intro n a g P
  obtain ⟨ρ, c, C, hρ0, hρ1, hc, hb⟩ := h0 n a g P
  obtain ⟨-, T0, hT⟩ := h1 n a g P
  set Bℝ : Fin a → Matrix (Fin g) (Fin g) ℝ := fun i => (P.B i).map (Int.cast : ℤ → ℝ) with hBℝ
  set Y : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℝ := chartImag P.a_le T0 Bℝ with hY
  have hKc : IsCompact (closedBall (0 : Fin n → ℂ) ρ) := isCompact_closedBall _ _
  have hKU : closedBall (0 : Fin n → ℂ) ρ ⊆ ball 0 1 := closedBall_subset_ball hρ1
  have hT0 := fun p q => hAn (fun y => T0 y p q) (ball 0 1) _ isOpen_ball (hT.1 p q) hKc hKU
  choose A hA0 hA using hT0
  set β : ℝ := ∑ i, ∑ p, ∑ q, |Bℝ i p q| with hβ
  set SA : ℝ := ∑ p, ∑ q, A p q with hSA
  set C0 : ℝ := SA + β with hC0
  have hAle : ∀ p q, A p q ≤ SA := fun p q =>
    (Finset.single_le_sum (f := fun q => A p q) (fun q _ => (hA0 p q).le) (Finset.mem_univ q)).trans
      (Finset.single_le_sum (f := fun p => ∑ q, A p q)
        (fun p _ => Finset.sum_nonneg fun q _ => (hA0 p q).le) (Finset.mem_univ p))
  have hBle : ∀ i p q, |Bℝ i p q| ≤ β := fun i p q =>
    ((Finset.single_le_sum (f := fun q => |Bℝ i p q|) (fun q _ => abs_nonneg _)
        (Finset.mem_univ q)).trans
      (Finset.single_le_sum (f := fun p => ∑ q, |Bℝ i p q|)
        (fun p _ => Finset.sum_nonneg fun q _ => abs_nonneg _) (Finset.mem_univ p))).trans
      (Finset.single_le_sum (f := fun i => ∑ p, ∑ q, |Bℝ i p q|)
        (fun i _ => Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun q _ => abs_nonneg _)
        (Finset.mem_univ i))
  have hβ0 : 0 ≤ β := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun p _ =>
    Finset.sum_nonneg fun q _ => abs_nonneg _
  have hSA0 : 0 ≤ SA := Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun q _ => (hA0 p q).le
  have hC00 : 0 ≤ C0 := add_nonneg hSA0 hβ0

  have hpt : ∀ z ∈ closedBall (0 : Fin n → ℂ) ρ, z ∈ puncturedChart P.a_le (ball 0 1) →
      (Y z - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef ∧
      ((max C 1 * chartRadius P.a_le z) • (1 : Matrix (Fin g) (Fin g) ℝ) - Y z).PosSemidef ∧
      (∀ p q, DifferentiableAt ℝ (fun y => Y y p q) z ∧
        ‖fderiv ℝ (fun y => Y y p q) z‖ ≤ C0 * (1 + ∑ i, ‖cuspCoord P.a_le z i‖⁻¹)) ∧
      (∀ p q, (fun y => P.hodge y p q) =ᶠ[𝓝 z] fun y => (Y y)⁻¹ p q) ∧
      (∀ (k : ℕ) (F : (Fin n → ℂ) → Matrix (Fin g) (Fin k) ℂ),
        (fun y => logDetGram (P.imTau y) (F y)) =ᶠ[𝓝 z] fun y => logDetGram (Y y) (F y)) := by
    intro z hzρ hz
    have hw := logLift_mem P.a_le hz
    have hexp := expCover_logLift P.a_le hz.2
    obtain ⟨hlow, hup⟩ := hb _ hw (by rw [hexp]; exact hzρ)
    have hIm : (P.τ (logLift a z)).map Complex.im = Y z := imTau_eq P hT hz
    rw [hIm] at hlow hup
    rw [hexp] at hup
    have hr1 := one_le_chartRadius P.a_le hz
    have hEq : ∀ᶠ y in 𝓝 z, P.imTau y = Y y :=
      Filter.eventually_of_mem ((isOpen_punctured P.a_le).mem_nhds hz) fun y hy => imTau_eq P hT hy
    refine ⟨hlow, ?_, fun p q => ?_, fun p q => hEq.mono fun y hy => ?_,
      fun k F => hEq.mono fun y hy => ?_⟩
    · have e : (max C 1 * chartRadius P.a_le z) • (1 : Matrix (Fin g) (Fin g) ℝ) - Y z =
          ((C * chartRadius P.a_le z) • (1 : Matrix (Fin g) (Fin g) ℝ) - Y z) +
            ((max C 1 - C) * chartRadius P.a_le z) • (1 : Matrix (Fin g) (Fin g) ℝ) := by
        rw [sub_mul, sub_smul]; abel
      rw [e]
      exact hup.add (PosSemidef.one.smul
        (mul_nonneg (sub_nonneg.mpr (le_max_left _ _)) (by linarith)))
    · obtain ⟨hd, hn⟩ := chartImag_entry_deriv P.a_le T0 Bℝ p q hz.2 (hA p q z hzρ).1
      refine ⟨hd, hn.trans ?_⟩
      have hS0 : 0 ≤ ∑ i, ‖cuspCoord P.a_le z i‖⁻¹ :=
        Finset.sum_nonneg fun i _ => inv_nonneg.mpr (norm_nonneg _)
      have h2 : ∑ i, |Bℝ i p q| * ‖cuspCoord P.a_le z i‖⁻¹ ≤
          β * ∑ i, ‖cuspCoord P.a_le z i‖⁻¹ := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_right (hBle i p q) (inv_nonneg.mpr (norm_nonneg _))
      have h3 := (hA p q z hzρ).2.2
      have h4 := hAle p q
      nlinarith
    · simp only [PeriodPolydisc.hodge, hy]
    · simp only [hy]
  refine ⟨ρ, hρ0, hρ1, ⟨(g : ℝ) ^ 2 * c⁻¹ ^ 2 * C0 * (1 + a), fun z hzρ hz p q => ?_⟩, ?_⟩
  · obtain ⟨hYc, -, hYd, hH, -⟩ := hpt z hzρ hz
    have hi := hInv g Y z c _ hc hYc hYd p q
    rw [(hH p q).differentiableAt_iff, (hH p q).fderiv_eq]
    have hS0 : 0 ≤ ∑ i, ‖cuspCoord P.a_le z i‖⁻¹ :=
      Finset.sum_nonneg fun i _ => inv_nonneg.mpr (norm_nonneg _)
    have hk0 : 0 ≤ (g : ℝ) ^ 2 * c⁻¹ ^ 2 * C0 := by positivity
    have ha1 : (1 : ℝ) ≤ 1 + a := by linarith [(Nat.cast_nonneg a : (0 : ℝ) ≤ a)]
    refine ⟨hi.1, hi.2.trans ?_, hi.2.trans ?_⟩
    · rw [← mul_assoc, mul_assoc _ (1 + (a : ℝ))]
      exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (by linarith) ha1) hk0
    · have := one_add_sum_le P.a_le hz
      rw [← mul_assoc, mul_assoc _ (1 + (a : ℝ))]
      exact mul_le_mul_of_nonneg_left this hk0
  · intro k F hF hrank
    obtain ⟨Kc, hKc0, hKmain⟩ := hLDG g k
    have hFb := fun j l => hAn (fun y => F y j l) (ball 0 1) _ isOpen_ball (hF j l) hKc hKU
    choose AF hAF0 hAF using hFb
    set aF : ℝ := ∑ j, ∑ l, AF j l with haF
    have hAFle : ∀ j l, AF j l ≤ aF := fun j l =>
      (Finset.single_le_sum (f := fun l => AF j l) (fun l _ => (hAF0 j l).le)
        (Finset.mem_univ l)).trans
        (Finset.single_le_sum (f := fun j => ∑ l, AF j l)
          (fun j _ => Finset.sum_nonneg fun l _ => (hAF0 j l).le) (Finset.mem_univ j))
    have haF0 : 0 ≤ aF := Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun l _ => (hAF0 j l).le
    obtain ⟨δ, hδ, hδle⟩ : ∃ δ : ℝ, 0 < δ ∧
        ∀ z ∈ closedBall (0 : Fin n → ℂ) ρ, δ ≤ ((F z)ᴴ * F z).det.re := by
      have hcont : ContinuousOn F (closedBall 0 ρ) := by
        rw [continuousOn_iff_continuous_domRestrict]
        exact continuous_matrix fun j l => ((hF j l).continuousOn.mono hKU).domRestrict
      have hc' : ContinuousOn (fun y => ((F y)ᴴ * F y).det.re) (closedBall 0 ρ) := by
        rw [continuousOn_iff_continuous_domRestrict] at hcont ⊢
        exact Complex.continuous_re.comp (hcont.matrix_conjTranspose.matrix_mul hcont).matrix_det
      obtain ⟨z0, hz0, hmin⟩ := hKc.exists_isMinOn ⟨0, mem_closedBall_self hρ0.le⟩ hc'
      exact ⟨_, re_det_pos (gram_posDef _ (hrank z0 (hKU hz0))), fun z hz => hmin hz⟩
    set C1 : ℝ := max C 1 with hC1def
    have hC1 : 0 < C1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    set W : ℝ := Kc * (1 + aF) ^ (2 * k) * (1 + c⁻¹) ^ (k + 1) * C1 ^ k / δ with hW
    have hW0 : 0 ≤ W := by positivity
    set Q : ℝ := W * (1 + C0) with hQ
    have hQ0 : 0 ≤ Q := by positivity
    have ha1 : (1 : ℝ) ≤ 1 + a := by linarith [(Nat.cast_nonneg a : (0 : ℝ) ≤ a)]
    refine ⟨max (Q * (1 + a)) k, fun z hzρ hz => ?_⟩
    obtain ⟨hYc, hYup, hYd, -, hL⟩ := hpt z hzρ hz
    have hr1 := one_le_chartRadius P.a_le hz
    set r := chartRadius P.a_le z with hr
    set S := ∑ i, ‖cuspCoord P.a_le z i‖⁻¹ with hS
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => inv_nonneg.mpr (norm_nonneg _)
    have hYpd := posDef_of_ge hc hYc
    have hl : 0 < C1 * r := by positivity
    have hμle : (C1 * r)⁻¹ ^ k * δ ≤
        ((F z)ᴴ * (Y z)⁻¹.map (fun x : ℝ => (x : ℂ)) * F z).det.re := by
      have h1 := posSemidef_map_ofReal (inv_ge_of_le hl hYpd hYup)
      rw [map_sub_smul_one] at h1
      have h2 := h1.conjTranspose_mul_mul_same (F z)
      rw [conj_sub_smul_one] at h2
      have h3 : ((((C1 * r)⁻¹ : ℝ) : ℂ) • ((F z)ᴴ * F z)).PosSemidef :=
        (posSemidef_conjTranspose_mul_self (F z)).smul
          (Complex.zero_le_real.mpr (inv_nonneg.mpr hl.le))
      have := re_det_mono h3 h2
      simp only [RCLike.re_to_complex] at this
      rw [re_det_ofReal_smul] at this
      exact le_trans (mul_le_mul_of_nonneg_left (hδle z hzρ) (by positivity)) this
    have hFent : ∀ j l, DifferentiableAt ℝ (fun y => F y j l) z ∧ ‖F z j l‖ ≤ aF ∧
        ‖fderiv ℝ (fun y => F y j l) z‖ ≤ aF := fun j l =>
      ⟨(hAF j l z hzρ).1, (hAF j l z hzρ).2.1.trans (hAFle j l),
        (hAF j l z hzρ).2.2.trans (hAFle j l)⟩
    have hm := hKmain F Y z aF (C0 * (1 + S)) c ((C1 * r)⁻¹ ^ k * δ) hc (by positivity) haF0
      (by positivity) hFent hYd hYc hμle
    rw [(hL k F).differentiableAt_iff, (hL k F).fderiv_eq]

    have hX : Kc * (1 + aF) ^ (2 * k) * (1 + c⁻¹) ^ (k + 1) * (1 + C0 * (1 + S)) /
        ((C1 * r)⁻¹ ^ k * δ) ≤ Q * r ^ k * (1 + S) := by
      have e : Kc * (1 + aF) ^ (2 * k) * (1 + c⁻¹) ^ (k + 1) * (1 + C0 * (1 + S)) /
          ((C1 * r)⁻¹ ^ k * δ) = W * r ^ k * (1 + C0 * (1 + S)) := by
        rw [hW, inv_pow, mul_pow]
        field_simp
      rw [e, hQ, mul_assoc W (1 + C0), mul_comm (1 + C0), ← mul_assoc W, mul_assoc (W * r ^ k)]
      exact mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
    have hCf : Q * (1 + a) ≤ max (Q * (1 + a)) k := le_max_left _ _
    have hQf : Q ≤ max (Q * (1 + a)) k := (le_mul_of_one_le_right hQ0 ha1).trans hCf
    have hrk : r ^ k ≤ r ^ (max (Q * (1 + a)) k) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hr1 (le_max_right _ _)
    have hrk0 : 0 ≤ r ^ k := by positivity
    refine ⟨hm.1, hm.2.trans (hX.trans ?_), hm.2.trans (hX.trans ?_)⟩
    · exact mul_le_mul_of_nonneg_right (mul_le_mul hQf hrk hrk0 (by linarith)) (by linarith)
    · have hE := one_add_sum_le P.a_le hz
      calc Q * r ^ k * (1 + S) ≤ Q * r ^ k * ((1 + a) * Real.exp (r / 2)) :=
            mul_le_mul_of_nonneg_left hE (by positivity)
        _ = Q * (1 + a) * r ^ k * Real.exp (r / 2) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
            (mul_le_mul hCf hrk hrk0 (by linarith)) (Real.exp_pos _).le

end

end GroundTheory.Heights₂.Heights.Regular
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Regularisation.PKernelPositive
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open Metric Filter Topology Matrix

noncomputable section

namespace KernelPositive

def cquad {g : ℕ} (v : Fin g → ℝ) (M : Matrix (Fin g) (Fin g) ℂ) : ℂ :=
  (fun k => (v k : ℂ)) ⬝ᵥ M *ᵥ fun k => (v k : ℂ)

theorem cquad_im {g : ℕ} (v : Fin g → ℝ) (M : Matrix (Fin g) (Fin g) ℂ) :
    (cquad v M).im = v ⬝ᵥ (M.map Complex.im *ᵥ v) := by
  simp [cquad, dotProduct, mulVec, Complex.im_sum, Complex.mul_im]

theorem intMat_mulVec_ofReal {g : ℕ} (B : Matrix (Fin g) (Fin g) ℤ) (v : Fin g → ℝ)
    (h : B.map (Int.cast : ℤ → ℝ) *ᵥ v = 0) :
    B.map (Int.cast : ℤ → ℂ) *ᵥ (fun k => (v k : ℂ)) = 0 := by
  funext k
  have hk := congrFun h k
  simp only [mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply] at hk ⊢
  exact_mod_cast hk

theorem im_pos_of_punctured {h : ℂ → ℂ} (hh : AnalyticAt ℂ h 0)
    (hpos : ∀ᶠ t in 𝓝[≠] (0 : ℂ), 0 < (h t).im) : 0 < (h 0).im := by
  by_contra hle
  rw [not_lt] at hle
  rcases hh.eventually_constant_or_nhds_le_map_nhds with hc | hmap
  · obtain ⟨t, ht, hte⟩ := (hpos.and (nhdsWithin_le_nhds hc)).exists
    rw [hte] at ht
    linarith
  · have hH : {w : ℂ | 0 < w.im ∨ w = h 0} ∈ 𝓝 (h 0) := by
      apply hmap
      rw [Filter.mem_map]
      filter_upwards [eventually_nhdsWithin_iff.mp hpos] with t ht
      by_cases h0 : t = 0
      · right
        rw [h0]
      · left
        exact ht h0
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hH
    have hmem : h 0 - ((ε / 2 : ℝ) : ℂ) * Complex.I ∈ ball (h 0) ε := by
      rw [mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_mul, Complex.norm_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
      linarith
    rcases hball hmem with hw | hw
    · simp at hw
      linarith
    · have := congrArg Complex.im hw
      simp at this
      linarith

theorem pos_of_punctured {n a g : ℕ} (P : PeriodPolydisc n a g)
    {T0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ} (hT : P.IsTau0Ext T0) {v : Fin g → ℝ}
    (hv : v ≠ 0) (hB : ∀ i, (P.B i).map (Int.cast : ℤ → ℝ) *ᵥ v = 0) {z : Fin n → ℂ}
    (hz : z ∈ ball (0 : Fin n → ℂ) 1) (hz0 : ∀ k, z k ≠ 0) :
    0 < (cquad v (T0 z)).im := by
  have hzk : ∀ k, ‖z k‖ < 1 := fun k => (norm_le_pi_norm z k).trans_lt (mem_ball_zero_iff.mp hz)
  have hw : logLift a z ∈ logCover P.a_le := by
    refine ⟨fun i => ?_, fun k hk => ?_⟩
    · have hi : (Fin.castLE P.a_le i).val < a := i.isLt
      simp only [logLift, if_pos hi, Complex.log_re]
      exact Real.log_neg (norm_pos_iff.mpr (hz0 _)) (hzk _)
    · simp only [logLift, if_neg (not_lt.mpr hk)]
      exact hzk k
  have hexp : expCover a (logLift a z) = z := by
    funext k
    by_cases hk : k.val < a
    · simp [expCover, logLift, hk, Complex.exp_log (hz0 k)]
    · simp [expCover, logLift, hk]
  have hT0 : T0 z = P.tau0 (logLift a z) := by
    rw [(hT.2 _ hw), hexp]
  have hsum : (∑ i : Fin a, (logLift a z (Fin.castLE P.a_le i) / (2 * Real.pi * Complex.I)) •
      (P.B i).map (Int.cast : ℤ → ℂ)) *ᵥ (fun k => (v k : ℂ)) = 0 := by
    refine Finset.sum_induction _ (fun N => N *ᵥ (fun k => (v k : ℂ)) = 0)
      (fun A B hA hB => by rw [add_mulVec, hA, hB, add_zero]) (zero_mulVec _) (fun i _ => ?_)
    rw [smul_mulVec, intMat_mulVec_ofReal _ _ (hB i), smul_zero]
  have hq : cquad v (T0 z) = cquad v (P.τ (logLift a z)) := by
    rw [hT0, cquad, cquad, PeriodPolydisc.tau0, sub_mulVec, hsum, sub_zero]
  rw [hq, cquad_im]
  simpa using (P.im_posDef _ hw).dotProduct_mulVec_pos hv

def line {n : ℕ} (z : Fin n → ℂ) (t : ℂ) : Fin n → ℂ := z + t • fun _ => (1 : ℂ)

theorem line_apply {n : ℕ} (z : Fin n → ℂ) (t : ℂ) (k : Fin n) : line z t k = z k + t := by
  simp [line]

end KernelPositive


open KernelPositive in
theorem kernelPositive_statement : KernelPositive.Statement := open KernelPositive in by
  intro n a g P T0 hT v hv hB z hz
  rw [← cquad_im]
  have hLa : AnalyticAt ℂ (line z) 0 :=
    analyticAt_const.add (analyticAt_id.smul analyticAt_const)
  have hL0 : line z 0 = z := by simp [line]
  have hG : AnalyticAt ℂ (fun t => cquad v (T0 (line z t))) 0 := by
    have h : (fun t => cquad v (T0 (line z t))) =
        ∑ p, ∑ q, fun t => (v p : ℂ) * (T0 (line z t) p q * (v q : ℂ)) := by
      funext t
      simp [cquad, dotProduct, mulVec, Finset.sum_apply, Finset.mul_sum]
    rw [h]
    refine Finset.analyticAt_sum _ fun p _ => Finset.analyticAt_sum _ fun q _ => ?_
    exact analyticAt_const.mul
      ((AnalyticAt.comp_of_eq (hT.1 p q z hz) hLa hL0).mul analyticAt_const)
  have hball : ∀ᶠ t in 𝓝 (0 : ℂ), line z t ∈ ball (0 : Fin n → ℂ) 1 :=
    hLa.continuousAt.preimage_mem_nhds (isOpen_ball.mem_nhds (by rw [hL0]; exact hz))
  have hne : ∀ᶠ t in 𝓝[≠] (0 : ℂ), ∀ k, line z t k ≠ 0 := by
    refine Filter.eventually_all.mpr fun k => ?_
    by_cases hzk : z k = 0
    · filter_upwards [self_mem_nhdsWithin] with t ht
      rw [line_apply, hzk, zero_add]
      exact ht
    · have hc : ContinuousAt (fun t : ℂ => z k + t) 0 :=
        (continuous_const.add continuous_id).continuousAt
      have := hc.eventually_ne (by simpa using hzk)
      exact nhdsWithin_le_nhds (this.mono fun t ht => by rw [line_apply]; exact ht)
  have hpos : ∀ᶠ t in 𝓝[≠] (0 : ℂ), 0 < (cquad v (T0 (line z t))).im := by
    filter_upwards [nhdsWithin_le_nhds hball, hne] with t ht1 ht2
    exact pos_of_punctured P hT hv hB ht1 ht2
  have := im_pos_of_punctured hG hpos
  simpa only [hL0] using this

end

end GroundTheory.Heights₂.Heights.Regular
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Regularisation.PImTauBounds
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open Metric Matrix Filter Topology

noncomputable section

theorem quad_smul {g : ℕ} (M : Matrix (Fin g) (Fin g) ℝ) (t : ℝ) (v : Fin g → ℝ) :
    (t • v) ⬝ᵥ M *ᵥ (t • v) = t ^ 2 * (v ⬝ᵥ M *ᵥ v) := by
  rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]; ring

theorem dot_self_nonneg {g : ℕ} (v : Fin g → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

def unitSphereDot (g : ℕ) : Set (Fin g → ℝ) := {u | u ⬝ᵥ u = 1}

theorem isCompact_unitSphereDot (g : ℕ) : IsCompact (unitSphereDot g) := by
  have hc : IsClosed (unitSphereDot g) :=
    isClosed_eq (continuous_id.dotProduct continuous_id) continuous_const
  refine (isCompact_closedBall (0 : Fin g → ℝ) 1).of_isClosed_subset hc ?_
  intro u hu
  have hu' : u ⬝ᵥ u = 1 := hu
  rw [mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  rw [Real.norm_eq_abs, abs_le_one_iff_mul_self_le_one]
  have : u i * u i ≤ u ⬝ᵥ u :=
    Finset.single_le_sum (f := fun j => u j * u j) (fun j _ => mul_self_nonneg (u j))
      (Finset.mem_univ i)
  linarith

theorem exists_unit_of_ne_zero {g : ℕ} {v : Fin g → ℝ} (hv : v ≠ 0) :
    ∃ u ∈ unitSphereDot g, ∀ M : Matrix (Fin g) (Fin g) ℝ,
      v ⬝ᵥ M *ᵥ v = (v ⬝ᵥ v) * (u ⬝ᵥ M *ᵥ u) := by
  have hpos : 0 < v ⬝ᵥ v :=
    lt_of_le_of_ne (dot_self_nonneg v) (fun h => hv (dotProduct_self_eq_zero.mp h.symm))
  set s := Real.sqrt (v ⬝ᵥ v) with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hpos
  have hs2 : s ^ 2 = v ⬝ᵥ v := Real.sq_sqrt hpos.le
  have hvu : v = s • (s⁻¹ • v) := by rw [smul_smul, mul_inv_cancel₀ hs0.ne', one_smul]
  refine ⟨s⁻¹ • v, ?_, fun M => ?_⟩
  · show (s⁻¹ • v) ⬝ᵥ (s⁻¹ • v) = 1
    have := quad_smul (1 : Matrix (Fin g) (Fin g) ℝ) s⁻¹ v
    rw [one_mulVec, one_mulVec] at this
    rw [this, ← hs2]; field_simp
  · conv_lhs => rw [hvu]
    rw [quad_smul, hs2]

theorem quad_upper_core {Z : Type*} [TopologicalSpace Z] {g : ℕ} {K : Set Z} (hK : IsCompact K)
    (M : Z → Matrix (Fin g) (Fin g) ℝ) (hM : ContinuousOn M K) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ z ∈ K, ∀ v : Fin g → ℝ, v ⬝ᵥ M z *ᵥ v ≤ A * (v ⬝ᵥ v) := by
  have hΦ : Continuous fun q : Matrix (Fin g) (Fin g) ℝ × (Fin g → ℝ) => q.2 ⬝ᵥ q.1 *ᵥ q.2 :=
    continuous_snd.dotProduct (continuous_fst.matrix_mulVec continuous_snd)
  have hc : ContinuousOn (fun p : Z × (Fin g → ℝ) => p.2 ⬝ᵥ M p.1 *ᵥ p.2)
      (K ×ˢ unitSphereDot g) :=
    hΦ.comp_continuousOn ((hM.comp continuous_fst.continuousOn fun p (hp : p ∈ K ×ˢ unitSphereDot g) => hp.1).prodMk
      continuous_snd.continuousOn)
  obtain ⟨A, hA⟩ := (hK.prod (isCompact_unitSphereDot g)).exists_bound_of_continuousOn hc
  refine ⟨max A 0, le_max_right _ _, fun z hz v => ?_⟩
  by_cases hv : v = 0
  · subst hv; simp
  obtain ⟨u, hu, huM⟩ := exists_unit_of_ne_zero hv
  rw [huM]
  have h1 := hA (z, u) ⟨hz, hu⟩
  have h2 : u ⬝ᵥ M z *ᵥ u ≤ max A 0 :=
    ((le_abs_self _).trans (by simpa [Real.norm_eq_abs] using h1)).trans (le_max_left _ _)
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right h2 (dot_self_nonneg v)

theorem quad_lower_core {Z : Type*} [TopologicalSpace Z] {g : ℕ} {K W : Set Z}
    (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W)
    (M : Z → Matrix (Fin g) (Fin g) ℝ) (hM : ContinuousOn M W)
    (S : Matrix (Fin g) (Fin g) ℝ) (hS : S.PosSemidef)
    (hpos : ∀ z ∈ K, ∀ v : Fin g → ℝ, v ≠ 0 → S *ᵥ v = 0 → 0 < v ⬝ᵥ M z *ᵥ v) :
    ∃ L ε : ℝ, 0 < ε ∧ ∀ z ∈ K, ∀ v : Fin g → ℝ,
      ε * (v ⬝ᵥ v) ≤ L * (v ⬝ᵥ S *ᵥ v) + v ⬝ᵥ M z *ᵥ v := by
  have hSnn : ∀ v : Fin g → ℝ, 0 ≤ v ⬝ᵥ S *ᵥ v := fun v => by
    simpa using (posSemidef_iff_dotProduct_mulVec.mp hS).2 v
  have hΦ : Continuous fun q : Matrix (Fin g) (Fin g) ℝ × (Fin g → ℝ) => q.2 ⬝ᵥ q.1 *ᵥ q.2 :=
    continuous_snd.dotProduct (continuous_fst.matrix_mulVec continuous_snd)
  let F : ℕ → Z × (Fin g → ℝ) → ℝ := fun m p =>
    (m : ℝ) * (p.2 ⬝ᵥ S *ᵥ p.2) + p.2 ⬝ᵥ M p.1 *ᵥ p.2
  have hFc : ∀ m, ContinuousOn (F m) (W ×ˢ Set.univ) := by
    intro m
    have hQ : ContinuousOn (fun p : Z × (Fin g → ℝ) => p.2 ⬝ᵥ M p.1 *ᵥ p.2) (W ×ˢ Set.univ) :=
      hΦ.comp_continuousOn ((hM.comp continuous_fst.continuousOn fun p (hp : p ∈ W ×ˢ Set.univ) => hp.1).prodMk
        continuous_snd.continuousOn)
    have hS' : Continuous fun p : Z × (Fin g → ℝ) => p.2 ⬝ᵥ S *ᵥ p.2 :=
      continuous_snd.dotProduct (continuous_const.matrix_mulVec continuous_snd)
    exact (continuous_const.mul hS').continuousOn.add hQ
  let U : ℕ → Set (Z × (Fin g → ℝ)) := fun m =>
    (W ×ˢ Set.univ) ∩ F m ⁻¹' Set.Ioi (1 / ((m : ℝ) + 1))
  have hUo : ∀ m, IsOpen (U m) := fun m =>
    (hFc m).isOpen_inter_preimage (hW.prod isOpen_univ) isOpen_Ioi
  have hmono : Monotone U := by
    intro m m' hmm' p hp
    refine ⟨hp.1, ?_⟩
    have hp2 : 1 / ((m : ℝ) + 1) < F m p := hp.2
    have hmm : (m : ℝ) ≤ m' := Nat.cast_le.mpr hmm'
    have h1 : F m p ≤ F m' p := by
      have := hSnn p.2
      show (m : ℝ) * (p.2 ⬝ᵥ S *ᵥ p.2) + _ ≤ (m' : ℝ) * (p.2 ⬝ᵥ S *ᵥ p.2) + _
      nlinarith
    have h2 : 1 / ((m' : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := by gcongr
    show 1 / ((m' : ℝ) + 1) < F m' p
    linarith
  have hcover : K ×ˢ unitSphereDot g ⊆ ⋃ m, U m := by
    rintro ⟨z, u⟩ ⟨hz, hu⟩
    have hu' : u ⬝ᵥ u = 1 := hu
    have hu0 : u ≠ 0 := by rintro rfl; simp at hu'
    simp only [Set.mem_iUnion]
    have hm0 : ∀ m : ℕ, (0 : ℝ) ≤ m := fun m => Nat.cast_nonneg m
    by_cases hSu : S *ᵥ u = 0
    · have hQ := hpos z hz u hu0 hSu
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt hQ
      refine ⟨m, ⟨⟨hKW hz, trivial⟩, ?_⟩⟩
      show 1 / ((m : ℝ) + 1) < (m : ℝ) * (u ⬝ᵥ S *ᵥ u) + u ⬝ᵥ M z *ᵥ u
      have := hSnn u
      nlinarith [hm0 m]
    · have hs : 0 < u ⬝ᵥ S *ᵥ u := by
        refine lt_of_le_of_ne (hSnn u) (fun h => hSu ?_)
        have := (hS.dotProduct_mulVec_zero_iff (x := u)).mp
        simp only [star_trivial] at this
        exact this h.symm
      obtain ⟨m, hm⟩ := exists_nat_gt ((1 - u ⬝ᵥ M z *ᵥ u) / (u ⬝ᵥ S *ᵥ u))
      refine ⟨m, ⟨⟨hKW hz, trivial⟩, ?_⟩⟩
      show 1 / ((m : ℝ) + 1) < (m : ℝ) * (u ⬝ᵥ S *ᵥ u) + u ⬝ᵥ M z *ᵥ u
      have h1 : 1 - u ⬝ᵥ M z *ᵥ u < (m : ℝ) * (u ⬝ᵥ S *ᵥ u) := by rwa [div_lt_iff₀ hs] at hm
      have h2 : 1 / ((m : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith [hm0 m]
      linarith
  obtain ⟨m, hm⟩ := (hK.prod (isCompact_unitSphereDot g)).elim_directed_cover U hUo hcover
    hmono.directed_le
  refine ⟨m, 1 / ((m : ℝ) + 1), by positivity, fun z hz v => ?_⟩
  by_cases hv : v = 0
  · subst hv; simp
  obtain ⟨u, hu, huM⟩ := exists_unit_of_ne_zero hv
  have hp : 1 / ((m : ℝ) + 1) < F m (z, u) := (hm ⟨hz, hu⟩).2
  have hvv := dot_self_nonneg v
  rw [huM S, huM (M z)]
  have h := mul_le_mul_of_nonneg_left hp.le hvv
  simp only [F] at h
  nlinarith [h]

namespace PeriodPolydisc

variable {n a g : ℕ} (P : PeriodPolydisc n a g)

def realB (i : Fin a) : Matrix (Fin g) (Fin g) ℝ := (P.B i).map (Int.cast : ℤ → ℝ)

theorem im_tau_eq {T0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ} (hT0 : P.IsTau0Ext T0)
    {w : Fin n → ℂ} (hw : w ∈ logCover P.a_le) :
    (P.τ w).map Complex.im = (T0 (expCover a w)).map Complex.im +
      ∑ i : Fin a, (-(w (Fin.castLE P.a_le i)).re / (2 * Real.pi)) • P.realB i := by
  have hτ : P.τ w = T0 (expCover a w) + ∑ i : Fin a,
      (w (Fin.castLE P.a_le i) / (2 * Real.pi * Complex.I)) • (P.B i).map (Int.cast : ℤ → ℂ) := by
    rw [← hT0.2 w hw, PeriodPolydisc.tau0, sub_add_cancel]
  ext p q
  rw [hτ]
  simp [Matrix.sum_apply, Complex.im_sum, Complex.mul_im, im_div_two_pi_I, realB]

end PeriodPolydisc

theorem quad_add_sum {g a : ℕ} (A : Matrix (Fin g) (Fin g) ℝ) (l : Fin a → ℝ)
    (B : Fin a → Matrix (Fin g) (Fin g) ℝ) (v : Fin g → ℝ) :
    v ⬝ᵥ (A + ∑ i, l i • B i) *ᵥ v = v ⬝ᵥ A *ᵥ v + ∑ i, l i * (v ⬝ᵥ B i *ᵥ v) := by
  rw [Matrix.add_mulVec, dotProduct_add, Matrix.sum_mulVec, dotProduct_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

theorem ImTauBounds.proof (h0 : Tau0Holomorphic.Statement) (h1 : KernelPositive.Statement) :
    ImTauBounds.Statement := by
  intro n a g P
  obtain ⟨hB, T0, hT0⟩ := h0 n a g P
  have hBpsd : ∀ i, (P.realB i).PosSemidef := hB
  have hBnn : ∀ i (v : Fin g → ℝ), 0 ≤ v ⬝ᵥ P.realB i *ᵥ v := fun i v => by
    simpa using (posSemidef_iff_dotProduct_mulVec.mp (hBpsd i)).2 v
  set S := ∑ i, P.realB i with hSdef
  have hSv : ∀ v : Fin g → ℝ, v ⬝ᵥ S *ᵥ v = ∑ i, v ⬝ᵥ P.realB i *ᵥ v := fun v => by
    rw [hSdef, Matrix.sum_mulVec, dotProduct_sum]
  have hS : S.PosSemidef := posSemidef_sum Finset.univ fun i _ => hBpsd i
  set Mz : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℝ := fun z => (T0 z).map Complex.im with hMz
  have hMc : ContinuousOn Mz (ball 0 1) := by
    refine continuousOn_pi.mpr fun p => continuousOn_pi.mpr fun q => ?_
    exact Complex.continuous_im.comp_continuousOn (hT0.1 p q).continuousOn
  have hK : IsCompact (closedBall (0 : Fin n → ℂ) (1 / 2)) := isCompact_closedBall _ _
  have hKW : closedBall (0 : Fin n → ℂ) (1 / 2) ⊆ ball 0 1 :=
    closedBall_subset_ball (by norm_num)
  have hpos : ∀ z ∈ closedBall (0 : Fin n → ℂ) (1 / 2), ∀ v : Fin g → ℝ, v ≠ 0 →
      S *ᵥ v = 0 → 0 < v ⬝ᵥ Mz z *ᵥ v := by
    intro z hz v hv hSv0
    refine h1 n a g P T0 hT0 v hv (fun i => ?_) z (hKW hz)
    have h := hSv v
    rw [hSv0, dotProduct_zero] at h
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hBnn j v)).mp h.symm i
      (Finset.mem_univ i)
    have := ((hBpsd i).dotProduct_mulVec_zero_iff (x := v)).mp
    simp only [star_trivial] at this
    exact this hi
  obtain ⟨L, ε, hε, hlow⟩ := quad_lower_core hK isOpen_ball hKW Mz hMc S hS hpos
  obtain ⟨A, hA0, hA⟩ := quad_upper_core hK Mz (hMc.mono hKW)
  have hBup : ∀ i, ∃ β : ℝ, 0 ≤ β ∧ ∀ v : Fin g → ℝ,
      v ⬝ᵥ P.realB i *ᵥ v ≤ β * (v ⬝ᵥ v) := by
    intro i
    obtain ⟨β, hβ0, hβ⟩ := quad_upper_core hK (fun _ => P.realB i) continuousOn_const
    exact ⟨β, hβ0, hβ 0 (mem_closedBall_self (by norm_num))⟩
  choose β hβ0 hβ using hBup
  refine ⟨min (1 / 2) (Real.exp (-(2 * Real.pi) * L)), ε, A + ∑ i, β i,
    lt_min (by norm_num) (Real.exp_pos _), lt_of_le_of_lt (min_le_left _ _) (by norm_num), hε, ?_⟩
  intro w hw hz
  have hzK : expCover a w ∈ closedBall (0 : Fin n → ℂ) (1 / 2) :=
    closedBall_subset_closedBall (min_le_left _ _) hz
  have hdec := P.im_tau_eq hT0 hw
  set z := expCover a w with hzdef
  set l : Fin a → ℝ := fun i => -(w (Fin.castLE P.a_le i)).re / (2 * Real.pi) with hl
  have hquad : ∀ v : Fin g → ℝ, v ⬝ᵥ (P.τ w).map Complex.im *ᵥ v =
      v ⬝ᵥ Mz z *ᵥ v + ∑ i, l i * (v ⬝ᵥ P.realB i *ᵥ v) := by
    intro v; rw [hdec]; exact quad_add_sum _ _ _ v
  have hzi : ∀ i : Fin a, z (Fin.castLE P.a_le i) = Complex.exp (w (Fin.castLE P.a_le i)) := by
    intro i; simp [hzdef, expCover, i.isLt]
  have hre : ∀ i : Fin a, (w (Fin.castLE P.a_le i)).re < 0 := hw.1
  have hnorm : ∀ i : Fin a,
      Real.exp (w (Fin.castLE P.a_le i)).re ≤ Real.exp (-(2 * Real.pi) * L) := by
    intro i
    have h1 : ‖z (Fin.castLE P.a_le i)‖ ≤ ‖z‖ := norm_le_pi_norm z _
    have h2 : ‖z‖ ≤ min (1 / 2) (Real.exp (-(2 * Real.pi) * L)) := by
      simpa [mem_closedBall, dist_zero_right] using hz
    rw [hzi, Complex.norm_exp] at h1
    exact h1.trans (h2.trans (min_le_right _ _))
  have hlL : ∀ i, L ≤ l i := by
    intro i
    have := Real.exp_le_exp.mp (hnorm i)
    show L ≤ -(w (Fin.castLE P.a_le i)).re / (2 * Real.pi)
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hterm : ∀ j : Fin a,
      Real.log (‖cuspCoord P.a_le z j‖ ^ 2)⁻¹ = -2 * (w (Fin.castLE P.a_le j)).re := by
    intro j
    rw [cuspCoord, hzi, Complex.norm_exp, Real.log_inv, Real.log_pow, Real.log_exp]
    push_cast; ring
  have hsum0 : 0 ≤ ∑ j, Real.log (‖cuspCoord P.a_le z j‖ ^ 2)⁻¹ :=
    Finset.sum_nonneg fun j _ => by rw [hterm j]; linarith [hre j]
  have hr1 : 1 ≤ chartRadius P.a_le z := by
    rw [chartRadius]
    have he : 1 ≤ Real.exp 1 := by have := Real.add_one_le_exp 1; linarith
    linarith
  have hlr : ∀ i, l i ≤ chartRadius P.a_le z := by
    intro i
    rw [chartRadius]
    have hsum : -2 * (w (Fin.castLE P.a_le i)).re ≤
        ∑ j, Real.log (‖cuspCoord P.a_le z j‖ ^ 2)⁻¹ := by
      rw [← hterm i]
      exact Finset.single_le_sum (f := fun j => Real.log (‖cuspCoord P.a_le z j‖ ^ 2)⁻¹)
        (fun j _ => by rw [hterm j]; linarith [hre j]) (Finset.mem_univ i)
    have hli : l i ≤ -2 * (w (Fin.castLE P.a_le i)).re := by
      show -(w (Fin.castLE P.a_le i)).re / (2 * Real.pi) ≤ _
      rw [div_le_iff₀ (by positivity)]
      have := hre i
      nlinarith [Real.pi_gt_three]
    have he : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
    linarith
  have hsymm : ((P.τ w).map Complex.im)ᵀ = (P.τ w).map Complex.im := by
    rw [← Matrix.transpose_map, P.symm w hw]
  refine ⟨?_, ?_⟩
  · rw [posSemidef_iff_dotProduct_mulVec]
    refine ⟨?_, fun v => ?_⟩
    · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, transpose_sub, transpose_smul,
        transpose_one, hsymm]
    · simp only [star_trivial, sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub,
        dotProduct_smul, smul_eq_mul]
      rw [hquad]
      have h1 := hlow z hzK v
      rw [hSv, Finset.mul_sum] at h1
      have h2 : ∑ i, L * (v ⬝ᵥ P.realB i *ᵥ v) ≤ ∑ i, l i * (v ⬝ᵥ P.realB i *ᵥ v) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hlL i) (hBnn i v)
      linarith
  · rw [posSemidef_iff_dotProduct_mulVec]
    refine ⟨?_, fun v => ?_⟩
    · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, transpose_sub, transpose_smul,
        transpose_one, hsymm]
    · simp only [star_trivial, sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub,
        dotProduct_smul, smul_eq_mul]
      rw [hquad]
      have hvv := dot_self_nonneg v
      have h1 := hA z hzK v
      have h2 : ∑ i, l i * (v ⬝ᵥ P.realB i *ᵥ v) ≤
          ∑ i, chartRadius P.a_le z * (β i * (v ⬝ᵥ v)) :=
        Finset.sum_le_sum fun i _ => mul_le_mul (hlr i) (hβ i v) (hBnn i v) (by linarith)
      have h3 : ∑ i, chartRadius P.a_le z * (β i * (v ⬝ᵥ v)) =
          chartRadius P.a_le z * (∑ i, β i) * (v ⬝ᵥ v) := by
        rw [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring
      have h4 : A * (v ⬝ᵥ v) ≤ A * chartRadius P.a_le z * (v ⬝ᵥ v) := by
        have := mul_le_mul_of_nonneg_left hr1 (mul_nonneg hA0 hvv)
        nlinarith
      nlinarith

end

end GroundTheory.Heights₂.Heights.Regular
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

theorem GlueRegularised.full : GlueRegularised.Statement :=
  GlueRegularised.proof

theorem KernelPositive.full : KernelPositive.Statement :=
  kernelPositive_statement

theorem Tau0Holomorphic.cond (hE : RiemannExtensionSlices.Statement)
    (hO : PuncturedExpOrder.Statement) (hD : LogCoverDescent.Statement) :
    Tau0Holomorphic.Statement :=
  Tau0Holomorphic.proof (ExpQuadMonomial.proof hE hO hD)

theorem ImTauBounds.cond (hE : RiemannExtensionSlices.Statement)
    (hO : PuncturedExpOrder.Statement) (hD : LogCoverDescent.Statement) :
    ImTauBounds.Statement :=
  ImTauBounds.proof (Tau0Holomorphic.cond hE hO hD) KernelPositive.full

theorem HodgeDerivative.cond (hE : RiemannExtensionSlices.Statement)
    (hO : PuncturedExpOrder.Statement) (hD : LogCoverDescent.Statement) :
    HodgeDerivative.Statement :=
  have hInv : InvEntryDeriv.Statement := InvEntryDeriv.proof InvEntryBound.proof
  HodgeDerivative.proof (ImTauBounds.cond hE hO hD) (Tau0Holomorphic.cond hE hO hD)
    AnalyticDerivBound.proof hInv
    (LogDetGramDeriv.proof InvEntryBound.proof hInv MatrixDetDeriv.proof GramEntryDeriv.proof)

end GroundTheory.Heights₂.Heights.Regular
