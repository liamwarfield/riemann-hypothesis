module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LeftFubiniNormalizedTower
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpPContPf

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegralNormLeDecay
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.NormLeIntegralFsv
open MeasureTheory Real
open scoped FourierTransform RealInnerProductSpace ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBO

def isoQ : ℂ ≃ₗᵢ[ℝ] ℂ where
  toFun s := conj (Complex.I * s)
  invFun w := -Complex.I * conj w
  map_add' a b := by simp [mul_add]
  map_smul' c a := by
    simp only [RingHom.id_apply, Complex.real_smul, map_mul, Complex.conj_ofReal]
    ring
  left_inv a := by
    simp only [map_mul, Complex.conj_I, Complex.conj_conj]
    ring_nf
    simp
  right_inv w := by
    simp only [map_mul, map_neg, Complex.conj_I, Complex.conj_conj]
    ring_nf
    simp [Complex.I_sq]
  norm_map' s := by simp

theorem isoQ_apply (s : ℂ) : isoQ s = conj (Complex.I * s) := rfl

theorem fsv_smul (s u z : ℂ) : P5.fsv s u * z = 𝐞 (-⟪u, (π⁻¹ : ℝ) • isoQ s⟫) • z := by
  unfold P5.fsv
  simp [Circle.smul_def, isoQ_apply]
  left
  rw [Real.fourierChar_apply]
  congr 1
  have hπ : π ≠ 0 := Real.pi_ne_zero
  apply Complex.ext <;> simp <;> field_simp <;> ring

theorem norm_le_integral_fsv (φ : ℂ → ℂ) (hφ : Continuous φ) (hi : MeasureTheory.Integrable φ)
    (hΞ : MeasureTheory.Integrable (fun s : ℂ => ∫ t : ℂ, P5.fsv s t * φ t)) (t : ℂ) :
    ‖φ t‖ ≤ ∫ s : ℂ, ‖∫ u : ℂ, P5.fsv s u * φ u‖ := by
  have hc : (π⁻¹ : ℝ) ≠ 0 := inv_ne_zero Real.pi_ne_zero
  have hL : ∀ s : ℂ, (∫ u : ℂ, P5.fsv s u * φ u) = 𝓕 φ ((π⁻¹ : ℝ) • isoQ s) := by
    intro s
    rw [fourier_eq]
    exact integral_congr_ae (Filter.Eventually.of_forall fun u => fsv_smul s u (φ u))
  have hmp : MeasurePreserving isoQ := isoQ.measurePreserving
  have hme : MeasurableEmbedding isoQ := isoQ.toHomeomorph.measurableEmbedding
  have hint1 : Integrable (fun s : ℂ => 𝓕 φ ((π⁻¹ : ℝ) • s)) := by
    have h1 : Integrable ((fun s : ℂ => 𝓕 φ ((π⁻¹ : ℝ) • s)) ∘ isoQ) := by
      have h2 := hΞ
      simp_rw [hL] at h2
      exact h2
    exact (hmp.integrable_comp_emb hme).mp h1
  have hint : Integrable (𝓕 φ) := by
    first
      | exact (integrable_comp_smul_iff volume (𝓕 φ) hc).mp hint1
      | exact (MeasureTheory.integrable_comp_smul_iff (volume : Measure ℂ) (𝓕 φ) hc).mp hint1
      | exact (Integrable.comp_smul_iff hc).mp hint1
  have hinv : 𝓕⁻ (𝓕 φ) t = φ t := by
    first
      | exact hi.fourier_inversion hint hφ.continuousAt
      | exact hi.fourierInv_fourier_eq hint hφ.continuousAt
      | exact hφ.fourierInv_fourier_eq hi hint t
      | exact Continuous.fourierInv_fourier_eq hφ hi hint t
      | exact hi.fourierInv_fourier hint hφ.continuousAt
      | exact hφ.fourierInv_fourier hi hint t
      | exact MeasureTheory.Integrable.fourier_inversion hi hint hφ.continuousAt
  have hb : ‖φ t‖ ≤ ∫ w : ℂ, ‖𝓕 φ w‖ := by
    rw [← hinv]
    first
      | rw [fourierInv_eq]
      | rw [Real.fourierInv_eq]
      | rw [fourierInv_eq']
      | rw [fourierInv_eq_fourier_neg, fourier_eq]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    congr 1
    funext w
    first
      | exact Circle.norm_smul _ _
      | simp
  have e1 := hmp.integral_comp hme (fun s : ℂ => ‖𝓕 φ ((π⁻¹ : ℝ) • s)‖)
  have e2 := Measure.integral_comp_smul (volume : Measure ℂ) (fun w : ℂ => ‖𝓕 φ w‖) (π⁻¹ : ℝ)
  try dsimp only at e1
  try dsimp only at e2
  have heq : (∫ s : ℂ, ‖∫ u : ℂ, P5.fsv s u * φ u‖) =
      |((π⁻¹ : ℝ) ^ 2)⁻¹| • ∫ w : ℂ, ‖𝓕 φ w‖ := by
    simp_rw [hL]
    rw [e1, e2, Complex.finrank_real_complex]
  rw [heq, smul_eq_mul]
  have h0 : 0 ≤ ∫ w : ℂ, ‖𝓕 φ w‖ := integral_nonneg fun _ => norm_nonneg _
  have hπ : 1 ≤ |((π⁻¹ : ℝ) ^ 2)⁻¹| := by
    rw [inv_pow, inv_inv, abs_of_pos (by positivity)]
    nlinarith [Real.pi_gt_three]
  nlinarith

end Formalism.FourierDecayAlt.P.PBO
end
end

open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBO

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.P5

theorem norm_fsv (a t : ℂ) : ‖fsv a t‖ = 1 := by
  unfold fsv
  rw [Complex.norm_exp]
  have : (a * t - conj a * conj t).re = 0 := by
    simp [Complex.mul_re, Complex.sub_re, Complex.conj_re, Complex.conj_im]
  rw [this, Real.exp_zero]

theorem continuous_fsv₂ : Continuous (fun q : ℂ × ℂ => fsv q.1 q.2) := by
  unfold fsv
  exact Complex.continuous_exp.comp ((continuous_fst.mul continuous_snd).sub
    ((Complex.continuous_conj.comp continuous_fst).mul (Complex.continuous_conj.comp continuous_snd)))

theorem integrable_fsv_mul {φ : ℂ → ℂ} (hφ : Continuous φ) (hi : Integrable φ) (a : ℂ) :
    Integrable (fun t => fsv a t * φ t) := by
  refine hi.bdd_mul (c := 1) ?_ (Filter.Eventually.of_forall fun t => (norm_fsv a t).le)
  exact (continuous_fsv₂.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable

theorem continuous_transform {φ : ℂ → ℂ} (hφ : Continuous φ) (hi : Integrable φ) :
    Continuous (fun s : ℂ => ∫ t, fsv s t * φ t) := by
  refine continuous_of_dominated (bound := fun t => ‖φ t‖) (fun s => ?_) (fun s => ?_) hi.norm ?_
  · exact ((continuous_fsv₂.comp (continuous_const.prodMk continuous_id)).mul hφ).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun t => by rw [norm_mul, norm_fsv, one_mul]
  · exact Filter.Eventually.of_forall fun t =>
      (continuous_fsv₂.comp (continuous_id.prodMk continuous_const)).mul continuous_const

theorem integrable_decay3' : Integrable (fun s : ℂ => ((1 + ‖s‖) ^ 3)⁻¹) := by
  have hd : Integrable (fun t : ℂ => (1 + ‖t‖) ^ (-(3 : ℝ))) volume := by
    refine integrable_one_add_norm ?_
    rw [Complex.finrank_real_complex]; norm_num
  refine hd.congr (Filter.Eventually.of_forall fun t => ?_)
  have h1 : (0 : ℝ) < 1 + ‖t‖ := by positivity
  simp only []
  rw [Real.rpow_neg h1.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

theorem integral_norm_le_decay {Ξ : ℂ → ℂ} (hΞ : Continuous Ξ) {K : ℝ} (hK : ∀ s, ‖Ξ s‖ ≤ K * ((1 + ‖s‖) ^ 3)⁻¹) :
    Integrable Ξ ∧ ∫ s, ‖Ξ s‖ ≤ K * ∫ s : ℂ, ((1 + ‖s‖) ^ 3)⁻¹ := by
  have hint : Integrable Ξ :=
    Integrable.mono' (integrable_decay3'.const_mul K) hΞ.aestronglyMeasurable (Filter.Eventually.of_forall hK)
  refine ⟨hint, ?_⟩
  rw [← integral_const_mul]
  exact integral_mono hint.norm (integrable_decay3'.const_mul K) hK

theorem fsv_sigma {c : ℂ} (hc : c ≠ 0) :
    fsv (Complex.I * (Real.pi : ℂ) / (2 * c)) c = -1 ∧
      ‖Complex.I * (Real.pi : ℂ) / (2 * c)‖ = Real.pi / (2 * ‖c‖) := by
  constructor
  · unfold fsv
    have e1 : Complex.I * (Real.pi : ℂ) / (2 * c) * c = Complex.I * (Real.pi / 2 : ℝ) := by
      push_cast; field_simp
    have e2 : conj (Complex.I * (Real.pi : ℂ) / (2 * c)) * conj c = -(Complex.I * (Real.pi / 2 : ℝ)) := by
      rw [← map_mul, e1, map_mul, Complex.conj_I, Complex.conj_ofReal]; ring
    rw [e1, e2, sub_neg_eq_add, ← two_mul, show (2 : ℂ) * (Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) =
      Real.pi * Complex.I by push_cast; ring, Complex.exp_pi_mul_I]
  · rw [norm_div, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, Complex.norm_two, one_mul]

theorem rr_eq_form {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par} (p : KB.Pl P Wp Wq)
    (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter) (h : C.LPt)
    (hh : D.IsLocPt h j) :
    p.RR F j w h h = p.form j hj w (KB.slv p.T F j hj w h hh.2) (KB.slv p.T F j hj w h hh.2) := by
  unfold KB.Pl.RR D.RRplace
  rw [dite_eq_left ⟨hh, hh⟩, dite_eq_left hj]
  rfl

theorem bdd_of_tendsto {u : ℕ → ℂ} {x : ℂ} (hu : Tendsto u atTop (𝓝 x)) : ∃ B : ℝ, 0 ≤ B ∧ ∀ n, ‖u n‖ ≤ B := by
  obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.1 (Metric.isBounded_range_of_tendsto u hu)
  exact ⟨max B 0, le_max_right _ _, fun n => (hB _ ⟨n, rfl⟩).trans (le_max_left _ _)⟩

end Formalism.FourierDecayAlt.P.PBO
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.BasePointInChart
open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBP

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

section wirt1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def dz (f : ℂ → E) (τ : ℂ) : E := (1 / 2 : ℂ) • (fderiv ℝ f τ 1 - Complex.I • fderiv ℝ f τ Complex.I)

def dzb (f : ℂ → E) (τ : ℂ) : E := (1 / 2 : ℂ) • (fderiv ℝ f τ 1 + Complex.I • fderiv ℝ f τ Complex.I)

theorem hasFDerivAt_norm1 {τ : ℂ} (hτ : τ ≠ 0) :
    HasFDerivAt (fun σ : ℂ => ‖σ‖) ((1 / (2 * Real.sqrt (‖τ‖ ^ 2))) • (2 • innerSL ℝ τ)) τ := by
  have h2 : HasFDerivAt (fun σ : ℂ => ‖σ‖ ^ 2) (2 • innerSL ℝ τ) τ := (hasStrictFDerivAt_norm_sq τ).hasFDerivAt
  have h1 := h2.sqrt (pow_ne_zero 2 (norm_ne_zero_iff.2 hτ))
  have e : (fun σ : ℂ => Real.sqrt (‖σ‖ ^ 2)) = fun σ => ‖σ‖ := funext fun σ => Real.sqrt_sq (norm_nonneg σ)
  rw [e] at h1
  exact h1

theorem fderiv_norm_apply {τ : ℂ} (hτ : τ ≠ 0) (v : ℂ) :
    fderiv ℝ (fun σ : ℂ => ‖σ‖) τ v = ‖τ‖⁻¹ * (τ.re * v.re + τ.im * v.im) := by
  rw [(hasFDerivAt_norm1 hτ).fderiv]
  have hs : Real.sqrt (‖τ‖ ^ 2) = ‖τ‖ := Real.sqrt_sq (norm_nonneg τ)
  simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply, hs, smul_eq_mul, Complex.inner, nsmul_eq_mul]
  have hn : ‖τ‖ ≠ 0 := norm_ne_zero_iff.2 hτ
  simp only [Complex.conj_re, Complex.conj_im, Complex.mul_re]
  field_simp
  ring

theorem normPow_deriv_apply {τ : ℂ} (hτ : τ ≠ 0) (n : ℕ) (v : ℂ) :
    fderiv ℝ (fun σ : ℂ => ‖σ‖ ^ n) τ v =
      (n : ℝ) * ‖τ‖ ^ (n - 1) * (‖τ‖⁻¹ * (τ.re * v.re + τ.im * v.im)) := by
  rw [((hasFDerivAt_norm1 hτ).pow n).fderiv]
  rw [← (hasFDerivAt_norm1 hτ).fderiv]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, nsmul_eq_mul, fderiv_norm_apply hτ]

theorem gauge_scalar {τ : ℂ} (hτ : τ ≠ 0) (n : ℕ) :
    τ * (1 / 2) * ((((n : ℝ) * ‖τ‖ ^ (n - 1) * (‖τ‖⁻¹ * τ.re) : ℝ) : ℂ) -
        Complex.I * (((n : ℝ) * ‖τ‖ ^ (n - 1) * (‖τ‖⁻¹ * τ.im) : ℝ) : ℂ)) =
      ((‖τ‖ ^ n : ℝ) : ℂ) * ((n : ℂ) / 2) := by
  have hn : ‖τ‖ ≠ 0 := norm_ne_zero_iff.2 hτ
  have hconj : τ * ((τ.re : ℂ) - Complex.I * τ.im) = ((‖τ‖ ^ 2 : ℝ) : ℂ) := by
    have := Complex.mul_conj τ
    rw [Complex.normSq_eq_norm_sq] at this
    rw [← this]
    congr 1
    apply Complex.ext <;> simp
  rcases n with _ | m
  · simp
  · have e : τ * (1 / 2) * ((((((m + 1 : ℕ) : ℝ) * ‖τ‖ ^ (m + 1 - 1) * (‖τ‖⁻¹ * τ.re) : ℝ) : ℂ)) -
        Complex.I * ((((m + 1 : ℕ) : ℝ) * ‖τ‖ ^ (m + 1 - 1) * (‖τ‖⁻¹ * τ.im) : ℝ) : ℂ)) =
        (((((m + 1 : ℕ) : ℝ) * ‖τ‖ ^ m * ‖τ‖⁻¹ / 2 : ℝ) : ℂ)) * (τ * ((τ.re : ℂ) - Complex.I * τ.im)) := by
      push_cast
      ring
    rw [e, hconj]
    push_cast
    field_simp
    ring

theorem dz_gauge {τ : ℂ} (hτ : τ ≠ 0) (n : ℕ) {f : ℂ → E} (hf : DifferentiableAt ℝ f τ) :
    τ • dz (fun σ => ((‖σ‖ ^ n : ℝ) : ℂ) • f σ) τ =
      ((‖τ‖ ^ n : ℝ) : ℂ) • (τ • dz f τ + ((n : ℂ) / 2) • f τ) := by
  have hN : HasFDerivAt (fun σ : ℂ => ((‖σ‖ ^ n : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (fderiv ℝ (fun σ : ℂ => ‖σ‖ ^ n) τ)) τ :=
    Complex.ofRealCLM.hasFDerivAt.comp τ ((hasFDerivAt_norm1 hτ).pow n).differentiableAt.hasFDerivAt
  have hP := hN.smul hf.hasFDerivAt
  have hfun : (fun σ => ((‖σ‖ ^ n : ℝ) : ℂ) • f σ) = (fun σ : ℂ => ((‖σ‖ ^ n : ℝ) : ℂ)) • f := rfl
  unfold dz
  rw [hfun, hP.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, normPow_deriv_apply hτ]
  have key := gauge_scalar hτ n
  simp only [Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add] at *
  linear_combination (norm := module) key • f τ

theorem gauge_scalar_bar {τ : ℂ} (hτ : τ ≠ 0) (n : ℕ) :
    conj τ * (1 / 2) * ((((n : ℝ) * ‖τ‖ ^ (n - 1) * (‖τ‖⁻¹ * τ.re) : ℝ) : ℂ) +
        Complex.I * (((n : ℝ) * ‖τ‖ ^ (n - 1) * (‖τ‖⁻¹ * τ.im) : ℝ) : ℂ)) =
      ((‖τ‖ ^ n : ℝ) : ℂ) * ((n : ℂ) / 2) := by
  have hn : ‖τ‖ ≠ 0 := norm_ne_zero_iff.2 hτ
  have hconj : conj τ * ((τ.re : ℂ) + Complex.I * τ.im) = ((‖τ‖ ^ 2 : ℝ) : ℂ) := by
    have := Complex.mul_conj τ
    rw [Complex.normSq_eq_norm_sq, mul_comm] at this
    rw [← this]
    congr 1
    apply Complex.ext <;> simp
  rcases n with _ | m
  · simp
  · have e : conj τ * (1 / 2) * ((((((m + 1 : ℕ) : ℝ) * ‖τ‖ ^ (m + 1 - 1) * (‖τ‖⁻¹ * τ.re) : ℝ) : ℂ)) +
        Complex.I * ((((m + 1 : ℕ) : ℝ) * ‖τ‖ ^ (m + 1 - 1) * (‖τ‖⁻¹ * τ.im) : ℝ) : ℂ)) =
        (((((m + 1 : ℕ) : ℝ) * ‖τ‖ ^ m * ‖τ‖⁻¹ / 2 : ℝ) : ℂ)) * (conj τ * ((τ.re : ℂ) + Complex.I * τ.im)) := by
      push_cast
      ring
    rw [e, hconj]
    push_cast
    field_simp
    ring

theorem dzb_gauge {τ : ℂ} (hτ : τ ≠ 0) (n : ℕ) {f : ℂ → E} (hf : DifferentiableAt ℝ f τ) :
    conj τ • dzb (fun σ => ((‖σ‖ ^ n : ℝ) : ℂ) • f σ) τ =
      ((‖τ‖ ^ n : ℝ) : ℂ) • (conj τ • dzb f τ + ((n : ℂ) / 2) • f τ) := by
  have hN : HasFDerivAt (fun σ : ℂ => ((‖σ‖ ^ n : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (fderiv ℝ (fun σ : ℂ => ‖σ‖ ^ n) τ)) τ :=
    Complex.ofRealCLM.hasFDerivAt.comp τ ((hasFDerivAt_norm1 hτ).pow n).differentiableAt.hasFDerivAt
  have hP := hN.smul hf.hasFDerivAt
  have hfun : (fun σ => ((‖σ‖ ^ n : ℝ) : ℂ) • f σ) = (fun σ : ℂ => ((‖σ‖ ^ n : ℝ) : ℂ)) • f := rfl
  unfold dzb
  rw [hfun, hP.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, normPow_deriv_apply hτ]
  have key := gauge_scalar_bar hτ n
  simp only [Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add] at *
  linear_combination (norm := module) key • f τ

end wirt1

section read0

variable {k : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def pt0 {n ρ : ℕ} (hn : 1 + ρ = n) (c : Fin ρ → ℂ) (τ : ℂ) : Fin n → ℂ := fun l => PBH.consC τ c (Fin.cast hn.symm l)

def Lz {n : ℕ} : ℂ →L[ℝ] (Fin n → ℂ) :=
  ContinuousLinearMap.pi fun l : Fin n => if l.val = 0 then ContinuousLinearMap.id ℝ ℂ else 0

theorem Lz_apply {n : ℕ} (h0 : 0 < n) (v : ℂ) : (Lz (n := n)) v = Pi.single ⟨0, h0⟩ v := by
  funext l
  by_cases hl : l.val = 0
  · have : l = ⟨0, h0⟩ := Fin.ext hl
    subst this
    simp [Lz]
  · have : l ≠ ⟨0, h0⟩ := fun h => hl (by rw [h])
    simp [Lz, hl, this]

theorem hasFDerivAt_base_point {n ρ : ℕ} (hn : 1 + ρ = n) (c : Fin ρ → ℂ) (τ : ℂ) :
    HasFDerivAt (pt0 hn c) (Lz (n := n)) τ := by
  have e : pt0 hn c = fun σ => Lz (n := n) σ + pt0 hn c 0 := by
    funext σ l
    show PBH.consC σ c (Fin.cast hn.symm l) = (Lz (n := n)) σ l + PBH.consC 0 c (Fin.cast hn.symm l)
    by_cases hl : l.val = 0
    · simp [PBH.consC, Lz, hl]
    · simp [PBH.consC, Lz, hl]
  rw [e]
  exact (Lz (n := n)).hasFDerivAt.add_const _

theorem base_point_zero_coord {n ρ : ℕ} (hn : 1 + ρ = n) (c : Fin ρ → ℂ) (τ : ℂ) :
    pt0 hn c τ ⟨0, by omega⟩ = τ := by
  simp [pt0, PBH.consC]

theorem pointWithZeroSecondCoord_mem_chart_of_restricted {n ρ : ℕ} (hn : 1 + ρ = n) {c : Fin ρ → ℂ} (hc : c ∈ OmX ρ) {τ : ℂ} (hτ : τ ≠ 0) :
    pt0 hn c τ ∈ OmX n := by
  subst hn
  have e : pt0 rfl c τ = PBH.consC τ c := funext fun l => by simp [pt0]
  rw [e]
  exact (PBH.omX_consC hτ c).2 hc

theorem operators_at_base_point {n ρ : ℕ} (hn : 1 + ρ = n) {c : Fin ρ → ℂ} (hc : c ∈ OmX ρ) {τ : ℂ} (hτ : τ ≠ 0)
    (f : (Fin n → ℂ) → E) (hf : DifferentiableAt ℝ f (pt0 hn c τ)) :
    opL (⟨0, by omega⟩ : Fin n) 0 f (pt0 hn c τ) = τ • dz (fun σ => f (pt0 hn c σ)) τ ∧
    opL (⟨0, by omega⟩ : Fin n) 1 f (pt0 hn c τ) = τ • f (pt0 hn c τ) ∧
    opL (⟨0, by omega⟩ : Fin n) 2 f (pt0 hn c τ) = τ⁻¹ • f (pt0 hn c τ) ∧
    opL (⟨0, by omega⟩ : Fin n) 3 f (pt0 hn c τ) = conj τ • dzb (fun σ => f (pt0 hn c σ)) τ ∧
    opL (⟨0, by omega⟩ : Fin n) 4 f (pt0 hn c τ) = conj τ • f (pt0 hn c τ) ∧
    opL (⟨0, by omega⟩ : Fin n) 5 f (pt0 hn c τ) = (conj τ)⁻¹ • f (pt0 hn c τ) := by
  have hmem := pointWithZeroSecondCoord_mem_chart_of_restricted hn hc hτ
  have h0 := base_point_zero_coord hn c τ
  have hd : ∀ v, fderiv ℝ (fun σ => f (pt0 hn c σ)) τ v = fderiv ℝ f (pt0 hn c τ) (Pi.single ⟨0, by omega⟩ v) := by
    intro v
    have h := (hf.hasFDerivAt.comp τ (hasFDerivAt_base_point hn c τ)).fderiv
    change fderiv ℝ (f ∘ pt0 hn c) τ v = _
    rw [h, ContinuousLinearMap.comp_apply, Lz_apply]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · show pOp _ f _ = _
    unfold pOp
    rw [if_pos hmem, h0]
    unfold wirt dz
    rw [hd, hd]
  · show cOp _ f _ = _
    simp only [cOp, h0]
  · show ciOp _ f _ = _
    simp only [ciOp, h0]
  · show pbOp _ f _ = _
    unfold pbOp
    rw [if_pos hmem, h0]
    unfold wirtBar dzb
    rw [hd, hd]
    rfl
  · show cbOp _ f _ = _
    simp only [cbOp, h0]
    rfl
  · show cbiOp _ f _ = _
    simp only [cbiOp, h0]
    rfl

end read0

end Formalism.FourierDecayAlt.P.PBP
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpMContPf
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

noncomputable section

namespace ContPfM

section ring

variable {R : Type*} [Ring R] (a c d : ℕ → R)

def Mi (i : ℕ) : Matrix (Fin 2) (Fin 2) R := !![a i, d i; -c i, 0]

def prodM (lo n : ℕ) : Matrix (Fin 2) (Fin 2) R := ((List.range n).map fun j => Mi a c d (lo + j)).prod

def bus : ℕ → R × R
  | 0 => (1, 0)
  | i + 1 => ((bus i).1 * a i - (bus i).2 * c i, (bus i).1 * d i)

def tds (r : ℕ) : ℕ → Fin 2 → R
  | 0, b => if b = 0 then 1 else 0
  | 1, b => if 1 ≤ r then (if b = 0 then a (r - 1) else d (r - 1)) else 0
  | m + 2, b => if m + 2 ≤ r then a (r - (m + 2)) * tds r (m + 1) b - c (r - (m + 1)) * d (r - (m + 2)) * tds r m b else 0

variable {a c d}

theorem prodM_succ_left (lo n : ℕ) : prodM a c d lo (n + 1) = Mi a c d lo * prodM a c d (lo + 1) n := by
  unfold prodM
  rw [List.range_succ_eq_map, List.map_cons, List.prod_cons, List.map_map]
  congr 2
  exact List.map_congr_left (fun j _ => by
    show Mi a c d (lo + (j + 1)) = Mi a c d (lo + 1 + j)
    congr 1
    omega)

theorem prodM_succ_right (lo n : ℕ) : prodM a c d lo (n + 1) = prodM a c d lo n * Mi a c d (lo + n) := by
  unfold prodM
  rw [List.range_succ, List.map_append, List.prod_append]
  simp

theorem bus_eq : ∀ i, (bus a c d i).1 = prodM a c d 0 i 0 0 ∧ (bus a c d i).2 = prodM a c d 0 i 0 1 := by
  intro i
  induction i with
  | zero => simp [bus, prodM]
  | succ i ih =>
    obtain ⟨h1, h2⟩ := ih
    rw [prodM_succ_right]
    simp only [bus, h1, h2, Matrix.mul_apply, Fin.sum_univ_two, Mi, zero_add]
    simp [sub_eq_add_neg]

theorem tds_eq (hcd : ∀ i, Commute (c (i + 1)) (d i)) (r : ℕ) :
    ∀ m, m ≤ r → ∀ b, tds a c d r m b = prodM a c d (r - m) m 0 b
  | 0, _, b => by fin_cases b <;> simp [tds, prodM]
  | 1, hm, b => by
    rw [prodM_succ_left]
    fin_cases b <;> simp [tds, hm, prodM, Mi]
  | m + 2, hm, b => by
    have ih1 := tds_eq hcd r (m + 1) (by omega) b
    have ih0 := tds_eq hcd r m (by omega) b
    have e1 : r - (m + 2) + 1 = r - (m + 1) := by omega
    have e2 : r - (m + 1) + 1 = r - m := by omega
    show (if m + 2 ≤ r then a (r - (m + 2)) * tds a c d r (m + 1) b -
        c (r - (m + 1)) * d (r - (m + 2)) * tds a c d r m b else 0) = _
    have hL : prodM a c d (r - (m + 1)) (m + 1) = Mi a c d (r - (m + 1)) * prodM a c d (r - m) m := by
      rw [prodM_succ_left, e2]
    have hR : prodM a c d (r - (m + 2)) (m + 2) =
        Mi a c d (r - (m + 2)) * (Mi a c d (r - (m + 1)) * prodM a c d (r - m) m) := by
      rw [prodM_succ_left, e1, hL]
    rw [if_pos hm, ih1, ih0, hL, hR]
    have hc := (hcd (r - (m + 2))).eq
    rw [e1] at hc
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Mi]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, zero_mul, add_zero, neg_mul]
    simp only [hc, mul_neg, mul_assoc, sub_eq_add_neg]

theorem tds_bus (hcd : ∀ i, Commute (c (i + 1)) (d i)) (r : ℕ) :
    tds a c d r r 0 = (bus a c d r).1 ∧ tds a c d r r 1 = (bus a c d r).2 := by
  rw [tds_eq hcd r r le_rfl, tds_eq hcd r r le_rfl, (bus_eq r).1, (bus_eq r).2, Nat.sub_self]
  exact ⟨rfl, rfl⟩

end ring

section ops

open ContPf

variable {r : ℕ} {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]


variable (X) in
def aSv (Y : ℂ) (i : ℕ) : Module.End ℂ (WSm r X) := algebraMap ℂ _ Y - eS X i 3

theorem cp_vABs (Y : ℂ) : ∀ i, i ≤ r → ∀ f : WSm r X,
    (Q.vABs r Y i).1 (f : (Fin r → ℂ) → X) = (((bus (aSv X Y) (eS X · 4) (eS X · 5) i).1 f : WSm r X) : (Fin r → ℂ) → X) ∧
      (Q.vABs r Y i).2 (f : (Fin r → ℂ) → X) = (((bus (aSv X Y) (eS X · 4) (eS X · 5) i).2 f : WSm r X) : (Fin r → ℂ) → X)
  | 0, _, f => ⟨rfl, rfl⟩
  | i + 1, hi, f => by
    have hir : i < r := by omega
    have ih := cp_vABs Y i (by omega)
    simp only [Q.vABs, dif_pos hir, bus]
    refine ⟨?_, ?_⟩
    · have e1 : Y • (f : (Fin r → ℂ) → X) - pbOp ⟨i, hir⟩ (f : (Fin r → ℂ) → X) =
          ((aSv X Y i f : WSm r X) : (Fin r → ℂ) → X) := by
        simp only [aSv, eS, dif_pos hir]
        rfl
      have e2 : cbOp ⟨i, hir⟩ (f : (Fin r → ℂ) → X) = ((eS X i 4 f : WSm r X) : (Fin r → ℂ) → X) := by
        simp only [eS, dif_pos hir]
        rfl
      rw [e1, e2, (ih _).1, (ih _).2]
      rfl
    · have e3 : cbiOp ⟨i, hir⟩ (f : (Fin r → ℂ) → X) = ((eS X i 5 f : WSm r X) : (Fin r → ℂ) → X) := by
        simp only [eS, dif_pos hir]
        rfl
      rw [e3, (ih _).1]
      rfl

theorem cp_tdUv (Y : ℂ) (b : Fin 2) : ∀ m, ∀ f : WSm r X,
    tdUv r Y m b (f : (Fin r → ℂ) → X) = ((tds (aSv X Y) (eS X · 4) (eS X · 5) r m b f : WSm r X) : (Fin r → ℂ) → X)
  | 0, f => by
    fin_cases b <;> simp [tdUv, tds]
  | 1, f => by
    by_cases h1 : 1 ≤ r
    · have hr : r - 1 < r := by omega
      fin_cases b
      · simp only [tdUv, tds, dif_pos h1, if_pos h1, Fin.zero_eta, if_true, aSv, eS, dif_pos hr]
        rfl
      · simp only [tdUv, tds, dif_pos h1, if_pos h1, Fin.mk_one, one_ne_zero, if_false, eS, dif_pos hr]
        rfl
    · simp only [tdUv, tds, dif_neg h1, if_neg h1]
      rfl
  | m + 2, f => by
    by_cases h2 : m + 2 ≤ r
    · have ih1 := cp_tdUv Y b (m + 1) f
      have ih0 := cp_tdUv Y b m f
      have hr2 : r - (m + 2) < r := by omega
      have hr1 : r - (m + 1) < r := by omega
      simp only [tdUv, tds, dif_pos h2, if_pos h2]
      rw [ih1, ih0]
      simp only [aSv, eS, dif_pos hr2, dif_pos hr1]
      rfl
    · simp only [tdUv, tds, dif_neg h2, if_neg h2]
      rfl

end ops

section loc

open ContPf

variable {r : ℕ} {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem loc_pbOp (l : Fin r) : Loc (X := X) (pbOp l) := by
  intro f₁ f₂ x h
  filter_upwards [h.eventuallyEq_nhds] with y hy
  simp only [pbOp, wirtBar, hy.fderiv_eq]

theorem loc_cbOp (l : Fin r) : Loc (X := X) (cbOp l) := by
  intro f₁ f₂ x h
  filter_upwards [h] with y hy
  simp only [cbOp, hy]

theorem loc_cbiOp (l : Fin r) : Loc (X := X) (cbiOp l) := by
  intro f₁ f₂ x h
  filter_upwards [h] with y hy
  simp only [cbiOp, hy]

theorem loc_tdUv (Y : ℂ) (b : Fin 2) : ∀ m, Loc (tdUv (X := X) r Y m b)
  | 0 => by
    unfold tdUv
    split_ifs
    · exact loc_id
    · exact loc_zero
  | 1 => by
    unfold tdUv
    split_ifs
    · exact loc_sub (loc_smul Y loc_id) (loc_pbOp _)
    · exact loc_cbiOp _
    · exact loc_zero
  | m + 2 => by
    have ih1 := loc_tdUv Y b (m + 1)
    have ih0 := loc_tdUv Y b m
    unfold tdUv
    split_ifs
    · exact loc_sub (loc_sub (loc_smul Y ih1) (loc_comp (loc_pbOp _) ih1))
        (loc_comp (loc_cbOp _) (loc_comp (loc_cbiOp _) ih0))
    · exact loc_zero

theorem loc_vABs (Y : ℂ) : ∀ i, Loc (X := X) (Q.vABs r Y i).1 ∧ Loc (X := X) (Q.vABs r Y i).2 := by
  intro i
  induction i with
  | zero => exact ⟨loc_id, loc_zero⟩
  | succ i ih =>
    obtain ⟨h1, h2⟩ := ih
    by_cases hi : i < r
    · simp only [Q.vABs, dif_pos hi]
      exact ⟨loc_sub (loc_comp h1 (loc_sub (loc_smul Y loc_id) (loc_pbOp _))) (loc_comp h2 (loc_cbOp _)),
        loc_comp h1 (loc_cbiOp _)⟩
    · simp only [Q.vABs, dif_neg hi]
      exact ⟨h1, h2⟩

end loc

end ContPfM

open ContPf ContPfM in
theorem mirror_residue_continuity : JDRvCont := by
  intro X _ _ r Y O hO hOm f hf c hc b
  obtain ⟨f', hf'm, hf'e⟩ := cp_cutoff O hO hOm f hf c hc
  have e1 : tdUv r Y r b f c = tdUv r Y r b f' c := ((loc_tdUv Y b r) f f' c hf'e.symm).eq_of_nhds
  have ev := loc_vABs (X := X) (r := r) Y r
  have h3 := cp_tdUv Y b r ⟨f', hf'm⟩
  have h4 := cp_vABs Y r le_rfl ⟨f', hf'm⟩
  have h5 := tds_bus (a := aSv (r := r) X Y) (c := (eS X · 4)) (d := (eS X · 5))
    (fun i => eS_comm (i + 1) i (by omega) 4 5) r
  have hb : b = 0 ∨ b = 1 := by fin_cases b <;> simp
  rcases hb with rfl | rfl
  · have e2 : (Q.vABs r Y r).1 f c = (Q.vABs r Y r).1 f' c := (ev.1 f f' c hf'e.symm).eq_of_nhds
    simp only [Q.cmp, if_true]
    rw [e1, e2]
    change tdUv r Y r 0 ((⟨f', hf'm⟩ : WSm r X) : (Fin r → ℂ) → X) c =
      (Q.vABs r Y r).1 ((⟨f', hf'm⟩ : WSm r X) : (Fin r → ℂ) → X) c
    rw [h3, h4.1, h5.1]
  · have e2 : (Q.vABs r Y r).2 f c = (Q.vABs r Y r).2 f' c := (ev.2 f f' c hf'e.symm).eq_of_nhds
    simp only [Q.cmp, show ¬ ((1 : Fin 2) = 0) by decide, if_false]
    rw [e1, e2]
    change tdUv r Y r 1 ((⟨f', hf'm⟩ : WSm r X) : (Fin r → ℂ) → X) c =
      (Q.vABs r Y r).2 ((⟨f', hf'm⟩ : WSm r X) : (Fin r → ℂ) → X) c
    rw [h3, h4.2, h5.2]

end

end Formalism.FourierDecayAlt.P.CutMP
end
