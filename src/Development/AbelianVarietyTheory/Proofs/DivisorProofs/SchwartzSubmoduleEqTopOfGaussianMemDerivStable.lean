module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOfClosedSubmoduleGaussianConvolution

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemClosureWideGaussianMulSchwartz
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemClosureWideGaussianMulSchwartz
open FourierTransform MeasureTheory Filter Topology
open scoped ContDiff Nat SchwartzMap

noncomputable section

namespace GlobalTheory.GaussCutoff

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def cutErr (c : ℝ) (y : E) : ℂ := GroundTheory.Global.gaussianSchwartz E (c • y) - 1

theorem contDiff_cutErr (c : ℝ) : ContDiff ℝ ∞ (cutErr (E := E) c) :=
  (((GroundTheory.Global.gaussianSchwartz E).smooth ⊤).comp (contDiff_const_smul c)).sub contDiff_const

theorem norm_cutErr_le (c : ℝ) (y : E) : ‖cutErr c y‖ ≤ Real.pi * c ^ 2 * ‖y‖ ^ 2 := by
  unfold cutErr
  rw [GroundTheory.Global.gaussianSchwartz_apply]
  have hx : ‖c • y‖ ^ 2 = c ^ 2 * ‖y‖ ^ 2 := by rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  rw [hx]
  set a := Real.pi * c ^ 2 * ‖y‖ ^ 2 with ha_def
  have ha : 0 ≤ a := by positivity
  have h1 : Real.exp (-Real.pi * (c ^ 2 * ‖y‖ ^ 2)) = Real.exp (-a) := by
    congr 1; rw [ha_def]; ring
  have he : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.2 (neg_nonpos.2 ha)
  rw [h1, show ((Real.exp (-a) : ℝ) : ℂ) - 1 = ((Real.exp (-a) - 1 : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
  linarith [Real.add_one_le_exp (-a)]

theorem norm_iteratedFDeriv_cutErr_le (c : ℝ) {j : ℕ} (hj : j ≠ 0) (y : E) :
    ‖iteratedFDeriv ℝ j (cutErr c) y‖ ≤
      |c| ^ j * SchwartzMap.seminorm ℝ 0 j (GroundTheory.Global.gaussianSchwartz E) := by
  set g := GroundTheory.Global.gaussianSchwartz E with hg
  set L : E →L[ℝ] E := c • ContinuousLinearMap.id ℝ E with hL
  have hgL : ContDiff ℝ ∞ ((g : E → ℂ) ∘ L) := (g.smooth ⊤).comp L.contDiff
  have hfun : cutErr (E := E) c = ((g : E → ℂ) ∘ L) - fun _ => (1 : ℂ) := by
    funext z; simp [cutErr, hL, hg]
  rw [hfun, iteratedFDeriv_sub_apply (hgL.contDiffAt.of_le (by exact_mod_cast le_top)) contDiffAt_const,
    iteratedFDeriv_const_of_ne hj, Pi.zero_apply, sub_zero,
    L.iteratedFDeriv_comp_right (g.smooth ⊤) y (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hLn : ‖L‖ ≤ |c| := by
    rw [hL]; refine (norm_smul_le _ _).trans ?_
    rw [Real.norm_eq_abs]; exact mul_le_of_le_one_right (abs_nonneg c) ContinuousLinearMap.norm_id_le
  have hD : ‖iteratedFDeriv ℝ j g (L y)‖ ≤ SchwartzMap.seminorm ℝ 0 j g := by
    simpa using SchwartzMap.le_seminorm ℝ 0 j g (L y)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_comm]
  exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hLn j) hD (norm_nonneg _)
    (pow_nonneg (abs_nonneg c) j)

theorem norm_iteratedFDeriv_cutErr_le' (c : ℝ) (hc : |c| ≤ 1) (j : ℕ) (y : E) :
    ‖iteratedFDeriv ℝ j (cutErr c) y‖ ≤
      |c| * (Real.pi + SchwartzMap.seminorm ℝ 0 j (GroundTheory.Global.gaussianSchwartz E)) * (1 + ‖y‖) ^ 2 := by
  have hS : 0 ≤ SchwartzMap.seminorm ℝ 0 j (GroundTheory.Global.gaussianSchwartz E) := apply_nonneg _ _
  have hy : 0 ≤ ‖y‖ := norm_nonneg y
  have hc0 : 0 ≤ |c| := abs_nonneg c
  have hpi := Real.pi_pos
  have h1 : 1 ≤ (1 + ‖y‖) ^ 2 := one_le_pow₀ (by linarith)
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [norm_iteratedFDeriv_zero]
    refine (norm_cutErr_le c y).trans ?_
    have hc2 : c ^ 2 ≤ |c| := by rw [← sq_abs]; nlinarith
    have hy2 : ‖y‖ ^ 2 ≤ (1 + ‖y‖) ^ 2 := by nlinarith
    calc Real.pi * c ^ 2 * ‖y‖ ^ 2 ≤ Real.pi * |c| * (1 + ‖y‖) ^ 2 := by gcongr
      _ = |c| * Real.pi * (1 + ‖y‖) ^ 2 := by ring
      _ ≤ _ := by gcongr; linarith
  · refine (norm_iteratedFDeriv_cutErr_le c hj.ne' y).trans ?_
    have hcj : |c| ^ j ≤ |c| := pow_le_of_le_one hc0 hc hj.ne'
    calc |c| ^ j * SchwartzMap.seminorm ℝ 0 j (GroundTheory.Global.gaussianSchwartz E)
        ≤ |c| * SchwartzMap.seminorm ℝ 0 j (GroundTheory.Global.gaussianSchwartz E) := by gcongr
      _ ≤ |c| * (Real.pi + SchwartzMap.seminorm ℝ 0 j (GroundTheory.Global.gaussianSchwartz E)) * 1 := by
          rw [mul_one]; gcongr; linarith
      _ ≤ _ := by gcongr

theorem cut_bound (h : 𝓢(E, ℂ)) (k n : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ c : ℝ, |c| ≤ 1 → ∀ y : E,
    ‖y‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => cutErr c y * h y) y‖ ≤ |c| * K := by
  set S : ℕ → ℝ := fun i => SchwartzMap.seminorm ℝ 0 i (GroundTheory.Global.gaussianSchwartz E) with hS
  set P := (Finset.Iic (k + 2, n)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) h with hP_def
  have hP : 0 ≤ P := apply_nonneg _ _
  have hS0 : ∀ i, 0 ≤ S i := fun i => apply_nonneg _ _
  have hpi := Real.pi_pos
  refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (Real.pi + S i) * (2 ^ (k + 2) * P),
    Finset.sum_nonneg fun i _ => by have := hS0 i; positivity, fun c hc y => ?_⟩
  have hy : 0 ≤ ‖y‖ := norm_nonneg y
  have hL := norm_iteratedFDeriv_mul_le (contDiff_cutErr (E := E) c) (h.smooth ⊤) y (n := n)
    (by exact_mod_cast le_top)
  calc ‖y‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => cutErr c y * h y) y‖
      ≤ ‖y‖ ^ k * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (cutErr c) y‖ *
          ‖iteratedFDeriv ℝ (n - i) h y‖ := by gcongr
    _ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (‖iteratedFDeriv ℝ i (cutErr c) y‖ *
          (‖y‖ ^ k * ‖iteratedFDeriv ℝ (n - i) h y‖)) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; ring
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ((|c| * (Real.pi + S i)) *
          ((1 + ‖y‖) ^ 2 * (‖y‖ ^ k * ‖iteratedFDeriv ℝ (n - i) h y‖))) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have := norm_iteratedFDeriv_cutErr_le' c hc i y
        have h0 : 0 ≤ ‖y‖ ^ k * ‖iteratedFDeriv ℝ (n - i) h y‖ := by positivity
        have e : |c| * (Real.pi + S i) * ((1 + ‖y‖) ^ 2 * (‖y‖ ^ k * ‖iteratedFDeriv ℝ (n - i) h y‖)) =
          (|c| * (Real.pi + S i) * (1 + ‖y‖) ^ 2) * (‖y‖ ^ k * ‖iteratedFDeriv ℝ (n - i) h y‖) := by ring
        rw [e]; gcongr
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ((|c| * (Real.pi + S i)) * (2 ^ (k + 2) * P)) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have hS0i := hS0 i
        have hX : (1 + ‖y‖) ^ 2 * (‖y‖ ^ k * ‖iteratedFDeriv ℝ (n - i) h y‖) ≤ 2 ^ (k + 2) * P := by
          calc (1 + ‖y‖) ^ 2 * (‖y‖ ^ k * ‖iteratedFDeriv ℝ (n - i) h y‖)
              ≤ (1 + ‖y‖) ^ 2 * ((1 + ‖y‖) ^ k * ‖iteratedFDeriv ℝ (n - i) h y‖) := by
                gcongr; linarith
            _ = (1 + ‖y‖) ^ (k + 2) * ‖iteratedFDeriv ℝ (n - i) h y‖ := by ring
            _ ≤ 2 ^ (k + 2) * P :=
                SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k + 2, n)) le_rfl
                  (Nat.sub_le n i) h y
        gcongr
    _ = |c| * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (Real.pi + S i) * (2 ^ (k + 2) * P) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; ring

def cutMap (h : 𝓢(E, ℂ)) (c : ℝ) (hc : |c| ≤ 1) : 𝓢(E, ℂ) where
  toFun y := cutErr c y * h y
  smooth' := (contDiff_cutErr c).mul (h.smooth ⊤)
  decay' k n := by
    obtain ⟨K, -, hK⟩ := cut_bound h k n
    exact ⟨|c| * K, hK c hc⟩

theorem cutMap_apply (h : 𝓢(E, ℂ)) (c : ℝ) (hc : |c| ≤ 1) (y : E) :
    cutMap h c hc y = cutErr c y * h y := rfl

end GlobalTheory.GaussCutoff


open GlobalTheory.GaussCutoff in
theorem GlobalTheory.GaussCutoff.mem_closure_gauss_mul (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (h : SchwartzMap E ℂ) :
    h ∈ closure {u : SchwartzMap E ℂ | ∃ b : ℝ, 0 < b ∧ ∀ y, u y = Complex.exp (-((b * ‖y‖ ^ 2 : ℝ) : ℂ)) * h y} := by
  rw [mem_closure_iff_nhds]
  intro U hU
  obtain ⟨s, r, hr, hsub⟩ := ((schwartz_withSeminorms ℝ E ℂ).mem_nhds_iff h U).1 hU
  choose K hK0 hK using fun m : ℕ × ℕ => cut_bound h m.1 m.2
  set M := ∑ m ∈ s, K m with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun m _ => hK0 m
  set c := min 1 (r / (2 * (M + 1))) with hc_def
  have hcpos : 0 < c := lt_min one_pos (by positivity)
  have hc1 : |c| ≤ 1 := by rw [abs_of_pos hcpos]; exact min_le_left _ _
  have hcr : c * (M + 1) ≤ r / 2 := by
    have := min_le_right 1 (r / (2 * (M + 1)))
    rw [← hc_def] at this
    calc c * (M + 1) ≤ r / (2 * (M + 1)) * (M + 1) := by gcongr
      _ = r / 2 := by field_simp
  refine ⟨h + cutMap h c hc1, hsub ?_, Real.pi * c ^ 2, by positivity, fun y => ?_⟩
  · rw [Seminorm.mem_ball, add_sub_cancel_left]
    refine Seminorm.finset_sup_apply_lt hr fun m hm => ?_
    have h1 : SchwartzMap.seminorm ℝ m.1 m.2 (cutMap h c hc1) ≤ |c| * K m :=
      SchwartzMap.seminorm_le_bound ℝ m.1 m.2 _ (mul_nonneg (abs_nonneg c) (hK0 m)) (hK m c hc1)
    have h2 : K m ≤ M := Finset.single_le_sum (fun m _ => hK0 m) hm
    show SchwartzMap.seminorm ℝ m.1 m.2 (cutMap h c hc1) < r
    rw [abs_of_pos hcpos] at h1
    nlinarith
  · rw [add_apply, cutMap_apply, cutErr, GroundTheory.Global.gaussianSchwartz_apply, Complex.ofReal_exp]
    have e : -Real.pi * ‖c • y‖ ^ 2 = -(Real.pi * c ^ 2 * ‖y‖ ^ 2) := by
      rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]; ring
    rw [e]; push_cast; ring
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemClosureWideGaussianMulSchwartzStatement
open FourierTransform MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_closure_wideGaussian_mul_schwartz : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (h : SchwartzMap E ℂ),
    h ∈ closure {u : SchwartzMap E ℂ | ∃ b : ℝ, 0 < b ∧ ∀ y, u y = Complex.exp (-((b * ‖y‖ ^ 2 : ℝ) : ℂ)) * h y} := by
  first | exact @GlobalTheory.GaussCutoff.mem_closure_gauss_mul | exact GlobalTheory.GaussCutoff.mem_closure_gauss_mul | (intros; apply GlobalTheory.GaussCutoff.mem_closure_gauss_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAllGaussianWidthsOfFourierStableSchwartz
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAllGaussianWidthsOfFourierStableSchwartz
open FourierTransform MeasureTheory Filter Topology

theorem GlobalTheory.GaussWidths.all_widths : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (M : Submodule ℂ (SchwartzMap E ℂ)), IsClosed (M : Set (SchwartzMap E ℂ)) →
    (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ M → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ M) →
    (∀ f ∈ M, 𝓕 f ∈ M) →
    ∀ G : SchwartzMap E ℂ, (∀ y, G y = Complex.exp (-((Real.pi * ‖y‖ ^ 2 : ℝ) : ℂ))) → G ∈ M →
    ∀ (c : ℝ), 0 < c → ∀ g : SchwartzMap E ℂ, (∀ y, g y = Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) → g ∈ M :=
  GlobalTheory.GaussWidths.all_widths_of_conv GlobalTheory.T.mem_of_closedSubmodule_gaussian_convolution
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAllGaussianWidthsOfFourierStableSchwartzStatement
open FourierTransform MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_all_gaussianWidths_of_fourierStable_schwartz : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (M : Submodule ℂ (SchwartzMap E ℂ)), IsClosed (M : Set (SchwartzMap E ℂ)) →
    (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ M → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ M) →
    (∀ f ∈ M, 𝓕 f ∈ M) →
    ∀ G : SchwartzMap E ℂ, (∀ y, G y = Complex.exp (-((Real.pi * ‖y‖ ^ 2 : ℝ) : ℂ))) → G ∈ M →
    ∀ (c : ℝ), 0 < c → ∀ g : SchwartzMap E ℂ, (∀ y, g y = Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) → g ∈ M := by
  first | exact @GlobalTheory.GaussWidths.all_widths | exact GlobalTheory.GaussWidths.all_widths | (intros; apply GlobalTheory.GaussWidths.all_widths <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NarrowGaussConvolutionDense
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NarrowGaussConvolutionDense
open FourierTransform MeasureTheory Filter Topology

namespace GlobalTheory.NarrowGauss

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

noncomputable def gauss (c : ℝ) (hc : 0 < c) : SchwartzMap E ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    ((LinearEquiv.smulOfNeZero ℝ E (Real.sqrt (c / Real.pi))
      (Real.sqrt_ne_zero'.2 (div_pos hc Real.pi_pos))).toContinuousLinearEquiv)
    (GroundTheory.Global.gaussianSchwartz E)

theorem gauss_apply (c : ℝ) (hc : 0 < c) (x : E) :
    gauss c hc x = Complex.exp (-(c : ℂ) * ‖x‖ ^ 2) := by
  rw [gauss, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    GroundTheory.Global.gaussianSchwartz_apply]
  have h : -Real.pi * ‖(LinearEquiv.smulOfNeZero ℝ E (Real.sqrt (c / Real.pi))
      (Real.sqrt_ne_zero'.2 (div_pos hc Real.pi_pos))).toContinuousLinearEquiv x‖ ^ 2
      = -c * ‖x‖ ^ 2 := by
    simp only [LinearEquiv.coe_toContinuousLinearEquiv', LinearEquiv.smulOfNeZero_apply,
      norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      Real.sq_sqrt (div_pos hc Real.pi_pos).le]
    field_simp
  rw [h, Complex.ofReal_exp]
  push_cast
  ring_nf

theorem fourier_gauss (c : ℝ) (hc : 0 < c) (w : E) :
    (𝓕 (gauss (E := E) c hc) : SchwartzMap E ℂ) w = (Real.pi / (c : ℂ)) ^ (Module.finrank ℝ E / 2 : ℂ) *
      Complex.exp (-Real.pi ^ 2 * ‖w‖ ^ 2 / c) := by
  rw [SchwartzMap.fourier_coe]
  have : (⇑(gauss c hc) : E → ℂ) = fun v ↦ Complex.exp (-(c : ℂ) * ‖v‖ ^ 2) :=
    funext (gauss_apply c hc)
  rw [this, fourier_gaussian_innerProductSpace (by simpa using hc)]

theorem fourierInv_gauss_mul_eq (f u : SchwartzMap E ℂ) (b : ℝ) (hb : 0 < b)
    (hu : ∀ y, u y = Complex.exp (-((b * ‖y‖ ^ 2 : ℝ) : ℂ)) * (𝓕 f : SchwartzMap E ℂ) y) :
    ∃ (c : ℝ) (s : ℂ), 0 < c ∧ ∀ y, (𝓕⁻ u : SchwartzMap E ℂ) y =
      s * ∫ a, f a * Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ)) := by
  set c : ℝ := Real.pi ^ 2 / b with hc_def
  have hc : 0 < c := by positivity
  set K : ℂ := (Real.pi / (c : ℂ)) ^ (Module.finrank ℝ E / 2 : ℂ) with hK
  have hK0 : K ≠ 0 := by
    rw [hK]
    exact Complex.cpow_ne_zero_iff.2 (Or.inl (div_ne_zero (by exact_mod_cast Real.pi_ne_zero)
      (by exact_mod_cast hc.ne')))
  set g : SchwartzMap E ℂ := gauss c hc
  set v : SchwartzMap E ℂ := SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) f g
  have huv : u = K⁻¹ • (𝓕 v : SchwartzMap E ℂ) := by
    ext ξ
    rw [SchwartzMap.smul_apply, SchwartzMap.fourier_convolution, SchwartzMap.pairing_apply_apply,
      ContinuousLinearMap.mul_apply', fourier_gauss, ← hK, hu, smul_eq_mul]
    have e : Complex.exp (-Real.pi ^ 2 * ‖ξ‖ ^ 2 / c) = Complex.exp (-((b * ‖ξ‖ ^ 2 : ℝ) : ℂ)) := by
      congr 1
      rw [hc_def]
      push_cast
      field_simp
    rw [e]
    field_simp
  refine ⟨c, K⁻¹, hc, fun y ↦ ?_⟩
  rw [huv, FourierTransform.fourierInv_smul, FourierTransform.fourierInv_fourier_eq,
    SchwartzMap.smul_apply, smul_eq_mul, SchwartzMap.convolution_apply, convolution_def]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun a ↦ ?_)
  simp only [ContinuousLinearMap.mul_apply', g, gauss_apply]
  push_cast
  ring_nf

end GlobalTheory.NarrowGauss

open GlobalTheory.NarrowGauss in
theorem GlobalTheory.narrowGauss_convolution_dense :
    ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : SchwartzMap E ℂ),
    f ∈ closure {u : SchwartzMap E ℂ | ∃ (c : ℝ) (s : ℂ), 0 < c ∧
      ∀ y, u y = s * ∫ a, f a * Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ))} := by
  intro E _ _ _ _ _ f
  have h1 := GlobalTheory.T.mem_closure_wideGaussian_mul_schwartz E (𝓕 f : SchwartzMap E ℂ)
  have h2 := map_mem_closure (f := fun w : SchwartzMap E ℂ ↦ (𝓕⁻ w : SchwartzMap E ℂ))
    (t := {u : SchwartzMap E ℂ | ∃ (c : ℝ) (s : ℂ), 0 < c ∧
      ∀ y, u y = s * ∫ a, f a * Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ))})
    FourierTransform.continuous_fourierInv h1 (fun u hu ↦ by
      obtain ⟨b, hb, hu⟩ := hu
      exact fourierInv_gauss_mul_eq f u b hb hu)
  simpa [FourierTransform.fourierInv_fourier_eq] using h2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NarrowGaussConvolutionDenseStatement
open FourierTransform MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_closure_gaussian_convolutions : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : SchwartzMap E ℂ),
    f ∈ closure {u : SchwartzMap E ℂ | ∃ (c : ℝ) (s : ℂ), 0 < c ∧
      ∀ y, u y = s * ∫ a, f a * Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ))} := by
  first | exact @GlobalTheory.narrowGauss_convolution_dense | exact GlobalTheory.narrowGauss_convolution_dense | (intros; apply GlobalTheory.narrowGauss_convolution_dense <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzDensityTransportLinearEquivChirp
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzDensityTransportLinearEquivChirp
open FourierTransform MeasureTheory Filter Topology

namespace GlobalTheory.GaussTransport

theorem iteratedDeriv_cexp_mul (a : ℂ) (n : ℕ) :
    iteratedDeriv n (fun y : ℝ => Complex.exp (a * y)) = fun y : ℝ => a ^ n * Complex.exp (a * y) := by
  induction n with
  | zero => funext y; simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext y
    have h1 : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 y := by
      simpa using (hasDerivAt_id y).ofReal_comp
    have h : HasDerivAt (fun y : ℝ => a ^ n * Complex.exp (a * y)) (a ^ n * (Complex.exp (a * y) * (a * 1))) y :=
      ((h1.const_mul a).cexp).const_mul (a ^ n)
    rw [h.deriv]; ring

theorem hasTemperateGrowth_expI : Function.HasTemperateGrowth (fun t : ℝ => Complex.exp (Complex.I * t)) := by
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => Complex.exp (Complex.I * y)) :=
    (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp
  refine ⟨hc, fun n => ⟨0, ‖Complex.I‖ ^ n, fun x => ?_⟩⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_cexp_mul, pow_zero, mul_one, norm_mul, norm_pow]
  have h1 : ‖Complex.exp (Complex.I * x)‖ = 1 := by
    rw [mul_comm, Complex.norm_exp_ofReal_mul_I]
  rw [h1, mul_one]

theorem hasTemperateGrowth_chirp {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Q : V →L[ℝ] V →L[ℝ] ℂ) (s : ℝ) :
    Function.HasTemperateGrowth (fun x : V => Complex.exp (Complex.I * ((s * (Q x x).im : ℝ) : ℂ))) := by
  have h1 : Function.HasTemperateGrowth (fun x : V => Q x x) :=
    Q.bilinear_hasTemperateGrowth Function.HasTemperateGrowth.id' Function.HasTemperateGrowth.id'
  have h2 : Function.HasTemperateGrowth (fun x : V => s * (Q x x).im) := by
    have := ((s • Complex.imCLM : ℂ →L[ℝ] ℝ)).hasTemperateGrowth.comp h1
    simpa [Function.comp_def] using this
  exact hasTemperateGrowth_expI.comp h2

end GlobalTheory.GaussTransport

namespace GlobalTheory.GaussTransport


open LineDeriv in
theorem transport : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (A : V ≃L[ℝ] E) (Q : V →L[ℝ] V →L[ℝ] ℂ) (N : Submodule ℂ (SchwartzMap V ℂ)),
    (∀ x, Real.pi * ‖A x‖ ^ 2 = (Q x x).re) →
    (∀ (v : V) (f f₁ : SchwartzMap V ℂ), f ∈ N → (∀ x, f₁ x = fderiv ℝ (⇑f) x v) → f₁ ∈ N) →
    (∀ (ℓ : V →L[ℝ] ℝ) (f f₁ : SchwartzMap V ℂ), f ∈ N → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ N) →
    ∃ N₂ : Submodule ℂ (SchwartzMap E ℂ),
      (∀ (v : E) (f f₁ : SchwartzMap E ℂ), f ∈ N₂ → (∀ x, f₁ x = fderiv ℝ (⇑f) x v) → f₁ ∈ N₂) ∧
      (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ N₂ → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ N₂) ∧
      (∀ (g : SchwartzMap V ℂ) (G : SchwartzMap E ℂ), (∀ x, g x = Complex.exp (-(Q x x))) → g ∈ N →
        (∀ y, G y = Complex.exp (-((Real.pi * ‖y‖ ^ 2 : ℝ) : ℂ))) → G ∈ N₂) ∧
      (Dense (N₂ : Set (SchwartzMap E ℂ)) → Dense (N : Set (SchwartzMap V ℂ))) := by
  intro V _ _ _ E _ _ _ A Q N hQ hD hL
  set χ : V → ℂ := fun x => Complex.exp (Complex.I * ((-1 * (Q x x).im : ℝ) : ℂ)) with hχdef
  set χi : V → ℂ := fun x => Complex.exp (Complex.I * ((1 * (Q x x).im : ℝ) : ℂ)) with hχidef
  have hχ : χ.HasTemperateGrowth := hasTemperateGrowth_chirp Q (-1)
  have hχi : χi.HasTemperateGrowth := hasTemperateGrowth_chirp Q 1
  have hχχi : ∀ x, χ x * χi x = 1 := by
    intro x
    simp only [hχdef, hχidef, ← Complex.exp_add]
    rw [← Complex.exp_zero]; congr 1; push_cast; ring
  let Ψ : SchwartzMap E ℂ →L[ℂ] SchwartzMap V ℂ :=
    (SchwartzMap.smulLeftCLM ℂ χ).comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A)
  have hΨ : ∀ f x, Ψ f x = χ x * f (A x) := by
    intro f x
    simp [Ψ, SchwartzMap.smulLeftCLM_apply_apply hχ]
  refine ⟨N.comap (Ψ : SchwartzMap E ℂ →ₗ[ℂ] SchwartzMap V ℂ), ?_, ?_, ?_, ?_⟩
  · intro w f f₁ hf hf₁
    rw [Submodule.mem_comap] at hf ⊢
    simp only [ContinuousLinearMap.coe_coe] at hf ⊢
    set v : V := A.symm w with hv
    let lam : V →L[ℝ] ℝ := Complex.imCLM.comp (Q.flip v + Q v)
    have hlam : ∀ x, lam x = (Q x v).im + (Q v x).im := by intro x; simp [lam]
    have hlamT : (fun x : V => ((lam x : ℝ) : ℂ)).HasTemperateGrowth :=
      (Complex.ofRealCLM.comp lam).hasTemperateGrowth
    have h1N : ∂_{v} (Ψ f) ∈ N := hD v (Ψ f) _ hf (fun x => SchwartzMap.lineDerivOp_apply_eq_fderiv v (Ψ f) x)
    have h2N : SchwartzMap.smulLeftCLM ℂ (fun x : V => ((lam x : ℝ) : ℂ)) (Ψ f) ∈ N :=
      hL lam (Ψ f) _ hf (fun x => by rw [SchwartzMap.smulLeftCLM_apply_apply hlamT, smul_eq_mul])
    have hder : ∀ x, fderiv ℝ (⇑(Ψ f)) x v =
        χ x * fderiv ℝ (⇑f) (A x) w - Complex.I * ((lam x : ℂ) * (χ x * f (A x))) := by
      intro x
      have hfun : (⇑(Ψ f)) = χ * (fun y => f (A y)) := funext (hΨ f)
      let L : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp ((-1 : ℝ) • Complex.imCLM)
      have hq := Q.hasFDerivAt_of_bilinear (hasFDerivAt_id x) (hasFDerivAt_id x)
      have hu := ((L.hasFDerivAt).comp x hq).const_mul Complex.I
      have hχd : HasFDerivAt χ (Complex.exp (Complex.I * L (Q x x)) • (Complex.I • (L.comp
          (((ContinuousLinearMap.precompR V Q) (id x)) (ContinuousLinearMap.id ℝ V) +
            ((ContinuousLinearMap.precompL V Q) (ContinuousLinearMap.id ℝ V)) (id x))))) x := by
        refine hu.cexp.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
        simp [χ, L]
      have hfA : HasFDerivAt (fun y => f (A y)) ((fderiv ℝ (⇑f) (A x)).comp (A : V →L[ℝ] E)) x :=
        (f.differentiableAt.hasFDerivAt).comp x A.hasFDerivAt
      rw [hfun, (hχd.mul hfA).fderiv]
      have hχx : χ x = Complex.exp (-(Complex.I * ((Q x x).im : ℂ))) := by simp [χ]
      simp [L, v, hlam]
      rw [hχx]
      ring
    have hsum : Ψ f₁ = ∂_{v} (Ψ f) + Complex.I • SchwartzMap.smulLeftCLM ℂ (fun x : V => ((lam x : ℝ) : ℂ)) (Ψ f) := by
      ext x
      rw [SchwartzMap.add_apply, SchwartzMap.smul_apply, SchwartzMap.smulLeftCLM_apply_apply hlamT,
        SchwartzMap.lineDerivOp_apply_eq_fderiv, hder, hΨ, hΨ, hf₁, smul_eq_mul, smul_eq_mul]
      ring
    rw [hsum]
    exact N.add_mem h1N (N.smul_mem _ h2N)
  · intro ℓ f f₁ hf hf₁
    rw [Submodule.mem_comap] at hf ⊢
    simp only [ContinuousLinearMap.coe_coe] at hf ⊢
    refine hL (ℓ.comp (A : V →L[ℝ] E)) (Ψ f) (Ψ f₁) hf (fun x => ?_)
    rw [hΨ, hΨ, hf₁]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
    ring
  · intro g G hg hgN hG
    rw [Submodule.mem_comap]
    simp only [ContinuousLinearMap.coe_coe]
    have hΨG : Ψ G = g := by
      ext x
      rw [hΨ, hG, hg, hχdef]
      simp only
      rw [← Complex.exp_add]
      congr 1
      conv_rhs => rw [← Complex.re_add_im (Q x x)]
      rw [← hQ x]
      push_cast
      ring
    rw [hΨG]; exact hgN
  · intro hd
    have hsurj : Function.Surjective Ψ := by
      intro k
      refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm (SchwartzMap.smulLeftCLM ℂ χi k), ?_⟩
      ext x
      rw [hΨ]
      simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
        ContinuousLinearEquiv.symm_apply_apply, SchwartzMap.smulLeftCLM_apply_apply hχi, smul_eq_mul]
      rw [← mul_assoc, hχχi, one_mul]
    refine (hsurj.denseRange.dense_image Ψ.continuous hd).mono ?_
    rintro _ ⟨f, hf, rfl⟩
    exact hf

end GlobalTheory.GaussTransport
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzDensityTransportLinearEquivChirpStatement
open FourierTransform MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_density_transport_linearEquiv_chirp : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (A : V ≃L[ℝ] E) (Q : V →L[ℝ] V →L[ℝ] ℂ) (N : Submodule ℂ (SchwartzMap V ℂ)),
    (∀ x, Real.pi * ‖A x‖ ^ 2 = (Q x x).re) →
    (∀ (v : V) (f f₁ : SchwartzMap V ℂ), f ∈ N → (∀ x, f₁ x = fderiv ℝ (⇑f) x v) → f₁ ∈ N) →
    (∀ (ℓ : V →L[ℝ] ℝ) (f f₁ : SchwartzMap V ℂ), f ∈ N → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ N) →
    ∃ N₂ : Submodule ℂ (SchwartzMap E ℂ),
      (∀ (v : E) (f f₁ : SchwartzMap E ℂ), f ∈ N₂ → (∀ x, f₁ x = fderiv ℝ (⇑f) x v) → f₁ ∈ N₂) ∧
      (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ N₂ → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ N₂) ∧
      (∀ (g : SchwartzMap V ℂ) (G : SchwartzMap E ℂ), (∀ x, g x = Complex.exp (-(Q x x))) → g ∈ N →
        (∀ y, G y = Complex.exp (-((Real.pi * ‖y‖ ^ 2 : ℝ) : ℂ))) → G ∈ N₂) ∧
      (Dense (N₂ : Set (SchwartzMap E ℂ)) → Dense (N : Set (SchwartzMap V ℂ))) := by
  first | exact @GlobalTheory.GaussTransport.transport | exact GlobalTheory.GaussTransport.transport | (intros; apply GlobalTheory.GaussTransport.transport <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivEuclideanPiMulNormSqEqRe
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivEuclideanPiMulNormSqEqRe
open FourierTransform MeasureTheory Filter Topology

namespace GlobalTheory

theorem exists_equiv_euclidean_pi_mul_norm_sq_eq_re (V : Type) [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] (Q : V →L[ℝ] V →L[ℝ] ℂ) (c : ℝ)
    (hc : 0 < c) (hQ : ∀ x, c * ‖x‖ ^ 2 ≤ (Q x x).re) :
    ∃ A : V ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V)),
      ∀ x, Real.pi * ‖A x‖ ^ 2 = (Q x x).re := by
  classical
  let B : LinearMap.BilinForm ℝ V := LinearMap.mk₂ ℝ (fun x y => (Q x y).re)
    (by intros; simp) (by intros; simp) (by intros; simp) (by intros; simp)
  let q : QuadraticForm ℝ V := B.toQuadraticMap
  have hq : ∀ x, q x = (Q x x).re := fun x => rfl
  obtain ⟨w, ⟨e⟩⟩ := QuadraticForm.equivalent_weightedSumSquares q
  have he : ∀ x, ∑ i, w i * (e x i * e x i) = (Q x x).re := by
    intro x
    have := e.map_app x
    rw [QuadraticMap.weightedSumSquares_apply] at this
    simpa [hq] using this
  have hw : ∀ i, 0 < w i := by
    intro i
    have h1 := he (e.symm (Pi.single i 1))
    have h2 : e (e.symm (Pi.single i 1)) = Pi.single i 1 := e.toLinearEquiv.apply_symm_apply _
    have hne : e.symm (Pi.single i 1) ≠ 0 := by
      intro h
      rw [h, map_zero] at h2
      have := congrFun h2 i
      simp at this
    rw [h2, Finset.sum_eq_single i (by intro j _ hj; simp [hj]) (by simp)] at h1
    have h3 := hQ (e.symm (Pi.single i 1))
    have h4 : 0 < c * ‖e.symm (Pi.single i 1)‖ ^ 2 := by
      have := norm_pos_iff.mpr hne
      positivity
    simp at h1
    linarith
  have hs : ∀ i, Real.sqrt (w i / Real.pi) ≠ 0 := fun i =>
    (Real.sqrt_pos.mpr (div_pos (hw i) Real.pi_pos)).ne'
  let D : (Fin (Module.finrank ℝ V) → ℝ) ≃ₗ[ℝ] (Fin (Module.finrank ℝ V) → ℝ) :=
    LinearEquiv.piCongrRight fun i =>
      LinearEquiv.smulOfNeZero ℝ ℝ (Real.sqrt (w i / Real.pi)) (hs i)
  let A : V ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) :=
    (e.toLinearEquiv.trans D).trans (WithLp.linearEquiv 2 ℝ _).symm
  have hA : ∀ x i, A x i = Real.sqrt (w i / Real.pi) * e x i := fun x i => rfl
  refine ⟨A.toContinuousLinearEquiv, fun x => ?_⟩
  rw [← he, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (A.toContinuousLinearEquiv x) i = Real.sqrt (w i / Real.pi) * e x i := hA x i
  rw [this, Real.norm_eq_abs, sq_abs, mul_pow, Real.sq_sqrt (div_pos (hw i) Real.pi_pos).le]
  have := Real.pi_pos.ne'
  field_simp

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivEuclideanPiMulNormSqEqReStatement
open FourierTransform MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_euclidean_equiv_pi_mul_norm_sq_eq_re : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (Q : V →L[ℝ] V →L[ℝ] ℂ) (c : ℝ),
    0 < c → (∀ x, c * ‖x‖ ^ 2 ≤ (Q x x).re) →
    ∃ A : V ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V)), ∀ x, Real.pi * ‖A x‖ ^ 2 = (Q x x).re := by
  first | exact @GlobalTheory.exists_equiv_euclidean_pi_mul_norm_sq_eq_re | exact GlobalTheory.exists_equiv_euclidean_pi_mul_norm_sq_eq_re | (intros; apply GlobalTheory.exists_equiv_euclidean_pi_mul_norm_sq_eq_re <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFourierStableGaussianSubmodule
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFourierStableGaussianSubmodule
open FourierTransform MeasureTheory Filter Topology

namespace GlobalTheory

theorem exists_fourier_stable_gaussian_submodule :
    ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (N : Submodule ℂ (SchwartzMap E ℂ)) (G : SchwartzMap E ℂ),
    (∀ y, G y = Complex.exp (-((Real.pi * ‖y‖ ^ 2 : ℝ) : ℂ))) → G ∈ N →
    (∀ (v : E) (f f₁ : SchwartzMap E ℂ), f ∈ N → (∀ x, f₁ x = fderiv ℝ (⇑f) x v) → f₁ ∈ N) →
    (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ N → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ N) →
    ∃ W : Submodule ℂ (SchwartzMap E ℂ), W ≤ N ∧ G ∈ W ∧
      (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ W → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ W) ∧
      (∀ f ∈ W, 𝓕 f ∈ W) := by
  intro E _ _ _ _ _ N G hG hGN hD hL
  let S : Set (Submodule ℂ (SchwartzMap E ℂ)) := {K | G ∈ K ∧
    (∀ (v : E) (f f₁ : SchwartzMap E ℂ), f ∈ K → (∀ x, f₁ x = fderiv ℝ (⇑f) x v) → f₁ ∈ K) ∧
    (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ K → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ K)}
  have hWG : G ∈ sInf S := Submodule.mem_sInf.2 fun K hK => hK.1
  have hWD : ∀ (v : E) (f f₁ : SchwartzMap E ℂ), f ∈ sInf S →
      (∀ x, f₁ x = fderiv ℝ (⇑f) x v) → f₁ ∈ sInf S := fun v f f₁ hf h =>
    Submodule.mem_sInf.2 fun K hK => hK.2.1 v f f₁ (Submodule.mem_sInf.1 hf K hK) h
  have hWL : ∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ sInf S →
      (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ sInf S := fun v f f₁ hf h =>
    Submodule.mem_sInf.2 fun K hK => hK.2.2 v f f₁ (Submodule.mem_sInf.1 hf K hK) h
  have htemp : ∀ m : E, Function.HasTemperateGrowth (fun x : E => inner ℝ x m) := by
    intro m
    have : (fun x : E => inner ℝ x m) = (innerSL ℝ m : E →L[ℝ] ℝ) := by
      funext x; simp [real_inner_comm]
    rw [this]; exact (innerSL ℝ m).hasTemperateGrowth
  have hFG : 𝓕 G = G := by
    ext w
    have h1 : (⇑G) = fun v : E => Complex.exp (-(Real.pi : ℂ) * (‖v‖ : ℂ) ^ 2) := by
      funext v; rw [hG]; congr 1; push_cast; ring
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    rw [SchwartzMap.fourier_coe, h1,
      fourier_gaussian_innerProductSpace (by simpa using Real.pi_pos), div_self hpi,
      Complex.one_cpow, one_mul]
    congr 1
    field_simp
  have hK : (sInf S).comap (SchwartzMap.fourierTransformCLM ℂ (V := E) (E := ℂ)).toLinearMap ∈ S := by
    refine ⟨?_, ?_, ?_⟩
    · show 𝓕 G ∈ sInf S
      rw [hFG]; exact hWG
    · intro v f f₁ hf h
      have hf' : 𝓕 f ∈ sInf S := hf
      show 𝓕 f₁ ∈ sInf S
      have h1 : f₁ = LineDeriv.lineDerivOp v f := by
        ext x; rw [h, SchwartzMap.lineDerivOp_apply_eq_fderiv]
      rw [h1, SchwartzMap.fourier_lineDerivOp_eq]
      refine Submodule.smul_mem _ _ (hWL (innerSL ℝ v) _ _ hf' fun x => ?_)
      rw [SchwartzMap.smulLeftCLM_apply_apply (htemp v)]
      simp [real_inner_comm]
    · intro ℓ f f₁ hf h
      have hf' : 𝓕 f ∈ sInf S := hf
      show 𝓕 f₁ ∈ sInf S
      set u : E := (InnerProductSpace.toDual ℝ E).symm ℓ with hu
      have h1 : f₁ = SchwartzMap.smulLeftCLM ℂ (fun x => inner ℝ x u) f := by
        ext x
        rw [h, SchwartzMap.smulLeftCLM_apply_apply (htemp u), real_inner_comm, hu,
          InnerProductSpace.toDual_symm_apply]
        simp
      have h2 : LineDeriv.lineDerivOp u (𝓕 f) ∈ sInf S :=
        hWD u _ _ hf' fun x => SchwartzMap.lineDerivOp_apply_eq_fderiv _ _ _
      rw [SchwartzMap.lineDerivOp_fourier_eq, ← h1, ← SchwartzMap.fourierTransformCLM_apply ℂ,
        map_smul, SchwartzMap.fourierTransformCLM_apply] at h2
      have hc : (-(2 * (Real.pi : ℂ) * Complex.I)) ≠ 0 := by
        simp [Real.pi_ne_zero]
      exact (Submodule.smul_mem_iff _ hc).1 h2
  exact ⟨sInf S, sInf_le ⟨hGN, hD, hL⟩, hWG, hWL, fun f hf => sInf_le hK hf⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFourierStableGaussianSubmoduleStatement
open FourierTransform MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fourier_stable_submodule_containing_gaussian : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (N : Submodule ℂ (SchwartzMap E ℂ)) (G : SchwartzMap E ℂ),
    (∀ y, G y = Complex.exp (-((Real.pi * ‖y‖ ^ 2 : ℝ) : ℂ))) → G ∈ N →
    (∀ (v : E) (f f₁ : SchwartzMap E ℂ), f ∈ N → (∀ x, f₁ x = fderiv ℝ (⇑f) x v) → f₁ ∈ N) →
    (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ N → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ N) →
    ∃ W : Submodule ℂ (SchwartzMap E ℂ), W ≤ N ∧ G ∈ W ∧
      (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ W → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ W) ∧
      (∀ f ∈ W, 𝓕 f ∈ W) := by
  first | exact @GlobalTheory.exists_fourier_stable_gaussian_submodule | exact GlobalTheory.exists_fourier_stable_gaussian_submodule | (intros; apply GlobalTheory.exists_fourier_stable_gaussian_submodule <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzClosureStableLinearFormFourier
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzClosureStableLinearFormFourier
open FourierTransform MeasureTheory Filter Topology

namespace GlobalTheory

theorem topologicalClosure_stable_of_continuousLinearMap {M : Type} [TopologicalSpace M] [AddCommGroup M]
    [Module ℂ M] [ContinuousSMul ℂ M] [ContinuousAdd M] (W : Submodule ℂ M) (T : M →L[ℂ] M)
    (hT : ∀ f ∈ W, T f ∈ W) : ∀ f ∈ W.topologicalClosure, T f ∈ W.topologicalClosure := by
  intro f hf
  have h1 : Submodule.map (T : M →ₗ[ℂ] M) W ≤ W := by
    rintro _ ⟨g, hg, rfl⟩
    exact hT g hg
  have h2 := Submodule.topologicalClosure_map T W
  exact Submodule.topologicalClosure_mono h1 (h2 ⟨f, hf, rfl⟩)

theorem schwartz_closure_stable_linearForm_fourier :
    ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (W : Submodule ℂ (SchwartzMap E ℂ)),
    (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ W → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ W) →
    (∀ f ∈ W, 𝓕 f ∈ W) →
    (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ W.topologicalClosure → (∀ x, f₁ x = (ℓ x : ℂ) * f x) →
      f₁ ∈ W.topologicalClosure) ∧
    (∀ f ∈ W.topologicalClosure, 𝓕 f ∈ W.topologicalClosure) := by
  intro E _ _ _ _ _ W hmul hF
  constructor
  · intro ℓ f f₁ hf hf₁
    have hg : Function.HasTemperateGrowth (fun x : E => ((ℓ x : ℝ) : ℂ)) :=
      (Complex.ofRealCLM.comp ℓ).hasTemperateGrowth
    set T : SchwartzMap E ℂ →L[ℂ] SchwartzMap E ℂ :=
      SchwartzMap.smulLeftCLM ℂ (fun x : E => ((ℓ x : ℝ) : ℂ)) with hTdef
    have hTapp : ∀ g : SchwartzMap E ℂ, ∀ x, T g x = (ℓ x : ℂ) * g x := by
      intro g x
      rw [hTdef, SchwartzMap.smulLeftCLM_apply hg]
      rfl
    have hTW : ∀ g ∈ W, T g ∈ W := fun g hg' => hmul ℓ g (T g) hg' (hTapp g)
    have hf₁T : f₁ = T f := by
      ext x
      rw [hf₁ x, hTapp f x]
    rw [hf₁T]
    exact topologicalClosure_stable_of_continuousLinearMap W T hTW f hf
  · intro f hf
    have hTW : ∀ g ∈ W, SchwartzMap.fourierTransformCLM ℂ g ∈ W := by
      intro g hg
      rw [SchwartzMap.fourierTransformCLM_apply]
      exact hF g hg
    have := topologicalClosure_stable_of_continuousLinearMap W (SchwartzMap.fourierTransformCLM ℂ) hTW f hf
    rwa [SchwartzMap.fourierTransformCLM_apply] at this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzClosureStableLinearFormFourierStatement
open FourierTransform MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topologicalClosure_stable_linearForm_mul_and_fourier : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (W : Submodule ℂ (SchwartzMap E ℂ)),
    (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ W → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ W) →
    (∀ f ∈ W, 𝓕 f ∈ W) →
    (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ W.topologicalClosure → (∀ x, f₁ x = (ℓ x : ℂ) * f x) →
      f₁ ∈ W.topologicalClosure) ∧
    (∀ f ∈ W.topologicalClosure, 𝓕 f ∈ W.topologicalClosure) := by
  first | exact @GlobalTheory.schwartz_closure_stable_linearForm_fourier | exact GlobalTheory.schwartz_closure_stable_linearForm_fourier | (intros; apply GlobalTheory.schwartz_closure_stable_linearForm_fourier <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzSubmoduleEqTopOfGaussianMemDerivStable
open FourierTransform MeasureTheory Filter Topology

namespace GlobalTheory.SchwartzGaussDense

theorem dense_of_stdGaussian_mem : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (N : Submodule ℂ (SchwartzMap E ℂ)) (G : SchwartzMap E ℂ),
    (∀ y, G y = Complex.exp (-((Real.pi * ‖y‖ ^ 2 : ℝ) : ℂ))) → G ∈ N →
    (∀ (v : E) (f f₁ : SchwartzMap E ℂ), f ∈ N → (∀ x, f₁ x = fderiv ℝ (⇑f) x v) → f₁ ∈ N) →
    (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ N → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ N) →
    Dense (N : Set (SchwartzMap E ℂ)) := by
  intro E _ _ _ _ _ N G hG hGN hD hL
  obtain ⟨W, hWN, hGW, hLW, hFW⟩ := GlobalTheory.T.exists_fourier_stable_submodule_containing_gaussian E N G hG hGN hD hL
  obtain ⟨hLM, hFM⟩ := GlobalTheory.T.topologicalClosure_stable_linearForm_mul_and_fourier E W hLW hFW
  set M := W.topologicalClosure with hMdef
  have hcl : IsClosed (M : Set (SchwartzMap E ℂ)) := W.isClosed_topologicalClosure
  have hGM : G ∈ M := W.le_topologicalClosure hGW
  have hgauss := GlobalTheory.T.mem_all_gaussianWidths_of_fourierStable_schwartz E M hcl hLM hFM G hG hGM
  have key : ∀ (h f : SchwartzMap E ℂ), (∃ b : ℝ, 0 < b ∧ ∀ y, f y = Complex.exp (-((b * ‖y‖ ^ 2 : ℝ) : ℂ)) * h y) →
      f ∈ M := by
    rintro h f ⟨b, hb, hf⟩
    have hsub : {u : SchwartzMap E ℂ | ∃ (c : ℝ) (s : ℂ), 0 < c ∧
        ∀ y, u y = s * ∫ a, f a * Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ))} ⊆ (M : Set (SchwartzMap E ℂ)) := by
      rintro u ⟨c, s, hc, hu⟩
      by_cases hs : s = 0
      · have : u = 0 := by ext y; simp [hu y, hs]
        rw [this]; exact M.zero_mem
      · have hu' : ∀ y, (s⁻¹ • u) y = ∫ a, Complex.exp (-((b * ‖a‖ ^ 2 : ℝ) : ℂ)) * h a *
            Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ)) := by
          intro y
          rw [SchwartzMap.smul_apply, hu y, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hs, one_mul]
          congr 1; funext a; rw [hf a]
        have hmem := GlobalTheory.T.mem_of_closedSubmodule_gaussian_convolution E M hcl hLM b c hb hc (hgauss c hc) h (s⁻¹ • u) hu'
        have : u = s • (s⁻¹ • u) := by rw [smul_smul, mul_inv_cancel₀ hs, one_smul]
        rw [this]; exact M.smul_mem s hmem
    exact closure_minimal hsub hcl (GlobalTheory.T.mem_closure_gaussian_convolutions E f)
  have hall : ∀ h : SchwartzMap E ℂ, h ∈ M := by
    intro h
    exact closure_minimal (fun f hf => key h f hf) hcl (GlobalTheory.T.mem_closure_wideGaussian_mul_schwartz E h)
  have htop : N.topologicalClosure = ⊤ := by
    rw [eq_top_iff]
    intro h _
    exact Submodule.topologicalClosure_mono hWN (hall h)
  exact (Submodule.dense_iff_topologicalClosure_eq_top).2 htop

theorem dense_of_gaussian_mem : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (N : Submodule ℂ (SchwartzMap V ℂ))
    (g : SchwartzMap V ℂ) (Q : V →L[ℝ] V →L[ℝ] ℂ) (c : ℝ), 0 < c → (∀ x, c * ‖x‖ ^ 2 ≤ (Q x x).re) →
    (∀ x, g x = Complex.exp (-(Q x x))) → g ∈ N →
    (∀ (v : V) (f f₁ : SchwartzMap V ℂ), f ∈ N → (∀ x, f₁ x = fderiv ℝ (⇑f) x v) → f₁ ∈ N) →
    (∀ (ℓ : V →L[ℝ] ℝ) (f f₁ : SchwartzMap V ℂ), f ∈ N → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ N) →
    Dense (N : Set (SchwartzMap V ℂ)) := by
  intro V _ _ _ N g Q c hc hQ hg hgN hD hL
  obtain ⟨A, hA⟩ := GlobalTheory.T.exists_euclidean_equiv_pi_mul_norm_sq_eq_re V Q c hc hQ
  obtain ⟨N₂, hD₂, hL₂, hG₂, hdense⟩ := GlobalTheory.T.schwartz_density_transport_linearEquiv_chirp V _ A Q N hA hD hL
  apply hdense
  let G := GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ (Fin (Module.finrank ℝ V)))
  have hG : ∀ y, G y = Complex.exp (-((Real.pi * ‖y‖ ^ 2 : ℝ) : ℂ)) := by
    intro y
    simp only [G, GroundTheory.Global.gaussianSchwartz_apply, Complex.ofReal_exp]
    congr 1; push_cast; ring
  exact dense_of_stdGaussian_mem _ N₂ G hG (hG₂ g G hg hgN hG) hD₂ hL₂

end GlobalTheory.SchwartzGaussDense
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzSubmoduleEqTopOfGaussianMemDerivStableStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzSubmodule_eq_top_of_gaussian_mem_derivStable : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (N : Submodule ℂ (SchwartzMap V ℂ))
    (g : SchwartzMap V ℂ) (Q : V →L[ℝ] V →L[ℝ] ℂ) (c : ℝ), 0 < c → (∀ x, c * ‖x‖ ^ 2 ≤ (Q x x).re) →
    (∀ x, g x = Complex.exp (-(Q x x))) → g ∈ N →
    (∀ (v : V) (f f₁ : SchwartzMap V ℂ), f ∈ N → (∀ x, f₁ x = fderiv ℝ (⇑f) x v) → f₁ ∈ N) →
    (∀ (ℓ : V →L[ℝ] ℝ) (f f₁ : SchwartzMap V ℂ), f ∈ N → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ N) →
    Dense (N : Set (SchwartzMap V ℂ)) := by
  first | exact @GlobalTheory.SchwartzGaussDense.dense_of_gaussian_mem | exact GlobalTheory.SchwartzGaussDense.dense_of_gaussian_mem | (intros; apply GlobalTheory.SchwartzGaussDense.dense_of_gaussian_mem <;> assumption)
end
