module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.LocFamPf
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DBoundB
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IteratedDerivGaussianExponentialAtZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AesmIteratedDerivReal
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCyclicVectorOfSeparable
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.LocNbar

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicDecompositionUpperHalfSpace
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicDecompositionUpperHalfSpace
open scoped Matrix

namespace GlobalTheory.CompanionTheory.SiegelPoint

open Matrix PositivityTheory.Rg.Sw

variable {n : ℕ}

theorem block_relations (A B D : Matrix (Fin n) (Fin n) ℂ)
    (h : InG (fromBlocks A B 0 D : M2 n)) : Aᴴ * D = 1 ∧ Bᴴ * D = Dᴴ * B := by
  unfold InG JJ at h
  rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply] at h
  obtain ⟨-, h12, -, h22⟩ := fromBlocks_inj.mp h
  simp only [conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_neg, Matrix.neg_mul, add_zero, zero_add, neg_zero] at h12 h22
  exact ⟨h12, (neg_add_eq_zero.mp h22).symm⟩

theorem levi_inG (a D : Matrix (Fin n) (Fin n) ℂ) (h : aᴴ * D = 1) :
    InG (fromBlocks a 0 0 D : M2 n) := by
  have h' : Dᴴ * a = 1 := by
    have h2 := congrArg conjTranspose h
    rwa [conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_one] at h2
  unfold InG JJ
  rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
  simp only [conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_neg, Matrix.neg_mul, add_zero, zero_add, h, h', neg_zero]

theorem siegel_point :
    ∀ (n : ℕ) (p : PositivityTheory.Rg.Sw.GR n), (PositivityTheory.Rg.Sw.mR p).toBlocks₂₁ = 0 →
      ∃ (nb ma : PositivityTheory.Rg.Sw.GR n) (b a : Matrix (Fin n) (Fin n) ℂ), bᴴ = b ∧ IsUnit a.det ∧
        PositivityTheory.Rg.Sw.mR nb = PositivityTheory.Rg.Sw.nU b ∧ PositivityTheory.Rg.Sw.mR ma = Matrix.fromBlocks a 0 0 (aᴴ)⁻¹ ∧
        p = nb * ma ∧
        ((PositivityTheory.Rg.Sw.mR p).toBlocks₁₁ * (Complex.I • 1) + (PositivityTheory.Rg.Sw.mR p).toBlocks₁₂) *
            ((PositivityTheory.Rg.Sw.mR p).toBlocks₂₁ * (Complex.I • 1) + (PositivityTheory.Rg.Sw.mR p).toBlocks₂₂)⁻¹ =
          b + Complex.I • (a * aᴴ) := by
  intro n p hp
  set A := (mR p).toBlocks₁₁ with hA
  set B := (mR p).toBlocks₁₂ with hB
  set D := (mR p).toBlocks₂₂ with hD
  have hpm : mR p = fromBlocks A B 0 D := by
    rw [← hp]
    exact (fromBlocks_toBlocks (mR p)).symm
  have hG : InG (mR p) := p.2
  rw [hpm] at hG
  obtain ⟨h1, h2⟩ := block_relations A B D hG
  have hDA : D * Aᴴ = 1 := mul_eq_one_comm.mp h1
  have hADh : A * Dᴴ = 1 := by
    have h3 := congrArg conjTranspose hDA
    rwa [conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_one] at h3
  have hinv : (Aᴴ)⁻¹ = D := Matrix.inv_eq_right_inv h1
  have hDinv : D⁻¹ = Aᴴ := Matrix.inv_eq_right_inv hDA
  set b := B * Aᴴ with hb
  have hbh : bᴴ = b := by
    rw [hb, conjTranspose_mul, conjTranspose_conjTranspose]
    calc A * Bᴴ = A * Bᴴ * (D * Aᴴ) := by rw [hDA, Matrix.mul_one]
      _ = A * (Bᴴ * D) * Aᴴ := by simp only [Matrix.mul_assoc]
      _ = A * (Dᴴ * B) * Aᴴ := by rw [h2]
      _ = A * Dᴴ * B * Aᴴ := by simp only [Matrix.mul_assoc]
      _ = B * Aᴴ := by rw [hADh, Matrix.one_mul]
  have hnbG : InG (nU b : M2 n) := by
    unfold InG JJ nU
    rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
    simp only [conjTranspose_zero, conjTranspose_one, Matrix.mul_zero, Matrix.zero_mul,
      Matrix.mul_one, Matrix.one_mul, Matrix.mul_neg, Matrix.neg_mul, add_zero, zero_add, hbh,
      neg_add_cancel, neg_zero]
  have hdet1 : IsUnit (nU b : M2 n).det := by
    unfold nU
    rw [det_fromBlocks_zero₂₁, det_one, mul_one]
    exact isUnit_one
  have hmaG : InG (fromBlocks A 0 0 D : M2 n) := levi_inG A D h1
  have hM : (fromBlocks A 0 0 D : M2 n) * fromBlocks Dᴴ 0 0 Aᴴ = 1 := by
    rw [fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, hADh, hDA, fromBlocks_one]
  have hdet2 : IsUnit (fromBlocks A 0 0 D : M2 n).det := Matrix.isUnit_det_of_right_inverse hM
  refine ⟨⟨Matrix.nonsingInvUnit _ hdet1, hnbG⟩, ⟨Matrix.nonsingInvUnit _ hdet2, hmaG⟩, b, A, hbh,
    Matrix.isUnit_det_of_right_inverse hADh, rfl, ?_, ?_, ?_⟩
  · show (fromBlocks A 0 0 D : M2 n) = fromBlocks A 0 0 (Aᴴ)⁻¹
    rw [hinv]
  · apply Subtype.ext
    apply Units.ext
    show mR p = nU b * fromBlocks A 0 0 D
    rw [hpm]
    unfold nU
    rw [fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, add_zero, zero_add]
    rw [hb, Matrix.mul_assoc, h1, Matrix.mul_one]
  · rw [hp, Matrix.zero_mul, zero_add, hDinv, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul, hb, add_comm]

end GlobalTheory.CompanionTheory.SiegelPoint
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicDecompositionUpperHalfSpaceStatement
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolic_decomposition_upper_half_space : ∀ (n : ℕ) (p : PositivityTheory.Rg.Sw.GR n), (PositivityTheory.Rg.Sw.mR p).toBlocks₂₁ = 0 → ∃ (nb ma : PositivityTheory.Rg.Sw.GR n) (b a : Matrix (Fin n) (Fin n) ℂ), bᴴ = b ∧ IsUnit a.det ∧ PositivityTheory.Rg.Sw.mR nb = PositivityTheory.Rg.Sw.nU b ∧ PositivityTheory.Rg.Sw.mR ma = Matrix.fromBlocks a 0 0 (aᴴ)⁻¹ ∧ p = nb * ma ∧ ((PositivityTheory.Rg.Sw.mR p).toBlocks₁₁ * (Complex.I • 1) + (PositivityTheory.Rg.Sw.mR p).toBlocks₁₂) * ((PositivityTheory.Rg.Sw.mR p).toBlocks₂₁ * (Complex.I • 1) + (PositivityTheory.Rg.Sw.mR p).toBlocks₂₂)⁻¹ = b + Complex.I • (a * aᴴ) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelPoint.siegel_point | exact GlobalTheory.CompanionTheory.SiegelPoint.siegel_point | (intros; apply GlobalTheory.CompanionTheory.SiegelPoint.siegel_point <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HolomorphicParameterIntegralGaussianBound
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HolomorphicParameterIntegralGaussianBound
open MeasureTheory
open scoped Matrix

namespace GlobalTheory.CompanionTheory.HolMean.GaussianFamily

lemma integrable_gauss_complex {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun w : ℂ => Real.exp (-δ * ‖w‖ ^ 2)) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ)
    (b := (δ : ℂ)) (by simpa using hδ) 0 0
  have h2 := h.norm
  refine h2.congr (ae_of_all _ fun w => ?_)
  simp only [zero_mul, add_zero, Complex.norm_exp]
  congr 1
  have : (-(δ : ℂ) * ((‖w‖ : ℝ) : ℂ) ^ 2) = ((-δ * ‖w‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.ofReal_re]

lemma integrable_gauss (m n : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun v : Fin m → Fin n → ℂ => Real.exp (-δ * ∑ a, ∑ j, ‖v a j‖ ^ 2)) := by
  have h1 : Integrable (fun u : Fin n → ℂ => ∏ j, Real.exp (-δ * ‖u j‖ ^ 2))
      (volume : Measure (Fin n → ℂ)) := by
    have := Integrable.fintype_prod (μ := fun _ : Fin n => (volume : Measure ℂ))
      (f := fun _ (w : ℂ) => Real.exp (-δ * ‖w‖ ^ 2)) fun _ => integrable_gauss_complex hδ
    exact this
  have h2 : Integrable (fun v : Fin m → Fin n → ℂ => ∏ a, ∏ j, Real.exp (-δ * ‖v a j‖ ^ 2))
      (volume : Measure (Fin m → Fin n → ℂ)) := by
    have := Integrable.fintype_prod (μ := fun _ : Fin m => (volume : Measure (Fin n → ℂ)))
      (f := fun _ (u : Fin n → ℂ) => ∏ j, Real.exp (-δ * ‖u j‖ ^ 2)) fun _ => h1
    exact this
  refine h2.congr (ae_of_all _ fun v => ?_)
  simp only [← Real.exp_sum, Finset.mul_sum]

theorem main : ∀ (m n : ℕ) (Φ : ℂ → (Fin m → Fin n → ℂ) → ℂ) (ρ C δ : ℝ), 0 < ρ → 0 < δ →
    (∀ v, DifferentiableOn ℂ (fun z => Φ z v) (Metric.ball 0 ρ)) →
    ContinuousOn (fun zv : ℂ × (Fin m → Fin n → ℂ) => Φ zv.1 zv.2)
      (Metric.ball 0 ρ ×ˢ Set.univ) →
    (∀ z ∈ Metric.ball (0 : ℂ) ρ, ∀ v, ‖Φ z v‖ ≤ C * Real.exp (-δ * ∑ a, ∑ j, ‖v a j‖ ^ 2)) →
    ∀ K : (Fin m → Fin n → ℂ) → ℂ, Continuous K → (∀ v, ‖K v‖ ≤ 1) →
    ∃ ρ' : ℝ, 0 < ρ' ∧ DifferentiableOn ℂ (fun z => ∫ v, K v * Φ z v) (Metric.ball 0 ρ') ∧
      ∀ r : ℕ, iteratedDeriv r (fun z => ∫ v, K v * Φ z v) 0 =
          ∫ v, K v * iteratedDeriv r (fun z => Φ z v) 0 ∧
        Continuous (fun v => iteratedDeriv r (fun z => Φ z v) 0) ∧
        ∃ C' : ℝ, ∀ v, ‖iteratedDeriv r (fun z => Φ z v) 0‖ ≤
          C' * Real.exp (-δ * ∑ a, ∑ j, ‖v a j‖ ^ 2) := by
  intro m n Φ ρ C δ hρ hδ hd hc hb K hK hK1
  let G : ℂ → (Fin m → Fin n → ℂ) → ℂ := fun z v => K v * Φ z v
  have hU : IsOpen (Metric.ball (0 : ℂ) ρ) := Metric.isOpen_ball
  have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) ρ := Metric.mem_ball_self hρ
  have hcv : ∀ z ∈ Metric.ball (0 : ℂ) ρ, Continuous (fun v => Φ z v) := fun z hz =>
    hc.comp_continuous (f := fun v : Fin m → Fin n → ℂ => (z, v)) (by fun_prop)
      (fun v => ⟨hz, Set.mem_univ _⟩)
  have hdG : ∀ v, DifferentiableOn ℂ (fun z => G z v) (Metric.ball 0 ρ) := fun v =>
    (hd v).const_mul (K v)
  have hmG : ∀ z ∈ Metric.ball (0 : ℂ) ρ, AEStronglyMeasurable (G z) volume := fun z hz =>
    (hK.mul (hcv z hz)).aestronglyMeasurable
  have hg : Integrable (fun v : Fin m → Fin n → ℂ =>
      C * Real.exp (-δ * ∑ a, ∑ j, ‖v a j‖ ^ 2)) := (integrable_gauss m n hδ).const_mul C
  have hbG : ∀ z₀ ∈ Metric.ball (0 : ℂ) ρ, ∃ V ∈ nhds z₀, ∃ g : (Fin m → Fin n → ℂ) → ℝ,
      Integrable g volume ∧ ∀ z ∈ V ∩ Metric.ball (0 : ℂ) ρ, ∀ v, ‖G z v‖ ≤ g v := by
    intro z₀ _
    refine ⟨Set.univ, Filter.univ_mem, _, hg, fun z hz v => ?_⟩
    calc ‖G z v‖ = ‖K v‖ * ‖Φ z v‖ := norm_mul _ _
      _ ≤ 1 * ‖Φ z v‖ := mul_le_mul_of_nonneg_right (hK1 v) (norm_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact hb z hz.2 v
  have hjoint : ∀ r : ℕ, ContinuousOn
      (fun q : (Fin m → Fin n → ℂ) × ℂ => iteratedDeriv r (fun z => Φ z q.1) q.2)
      (Set.univ ×ˢ Metric.ball 0 ρ) := by
    refine GlobalTheory.CompanionTheory.HolFamily.continuousOn_iteratedDeriv_family (Fin m → Fin n → ℂ)
      (Metric.ball 0 ρ) hU (fun v z => Φ z v) ?_ hd
    exact hc.comp (f := fun q : (Fin m → Fin n → ℂ) × ℂ => (q.2, q.1)) (by fun_prop)
      (fun q hq => ⟨hq.2, Set.mem_univ _⟩)
  refine ⟨ρ, hρ, ?_, fun r => ⟨?_, ?_, ?_⟩⟩
  · intro z hz
    exact ((GlobalTheory.CompanionTheory.HolMean.integral_step hU G hdG hmG hbG).1 z hz).differentiableAt.differentiableWithinAt
  · have key := GlobalTheory.CompanionTheory.HolMean.iteratedDeriv_integral hU r G hdG hmG hbG 0 h0
    refine key.trans (integral_congr_ae (ae_of_all _ fun v => ?_))
    exact iteratedDeriv_const_mul_field (K v) (fun z => Φ z v)
  · exact (hjoint r).comp_continuous (f := fun v : Fin m → Fin n → ℂ => (v, (0 : ℂ)))
      (by fun_prop) (fun v => ⟨Set.mem_univ _, h0⟩)
  · refine ⟨r.factorial * C / (ρ / 2) ^ r, fun v => ?_⟩
    have hR : 0 < ρ / 2 := by positivity
    have hsub : Metric.closedBall (0 : ℂ) (ρ / 2) ⊆ Metric.ball 0 ρ :=
      Metric.closedBall_subset_ball (by linarith)
    have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (c := 0)
      (C := C * Real.exp (-δ * ∑ a, ∑ j, ‖v a j‖ ^ 2)) (f := fun z => Φ z v) r hR
      ((hd v).diffContOnCl_ball hsub)
      (fun z hz => hb z (hsub (Metric.sphere_subset_closedBall hz)) v)
    refine h.trans (le_of_eq ?_)
    ring

end GlobalTheory.CompanionTheory.HolMean.GaussianFamily
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HolomorphicParameterIntegralGaussianBoundStatement
open MeasureTheory
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_parameter_integral_gaussian_bound : ∀ (m n : ℕ) (Φ : ℂ → (Fin m → Fin n → ℂ) → ℂ) (ρ C δ : ℝ), 0 < ρ → 0 < δ → (∀ v, DifferentiableOn ℂ (fun z => Φ z v) (Metric.ball 0 ρ)) → ContinuousOn (fun zv : ℂ × (Fin m → Fin n → ℂ) => Φ zv.1 zv.2) (Metric.ball 0 ρ ×ˢ Set.univ) → (∀ z ∈ Metric.ball (0 : ℂ) ρ, ∀ v, ‖Φ z v‖ ≤ C * Real.exp (-δ * ∑ a, ∑ j, ‖v a j‖ ^ 2)) → ∀ K : (Fin m → Fin n → ℂ) → ℂ, Continuous K → (∀ v, ‖K v‖ ≤ 1) → ∃ ρ' : ℝ, 0 < ρ' ∧ DifferentiableOn ℂ (fun z => ∫ v, K v * Φ z v) (Metric.ball 0 ρ') ∧ ∀ r : ℕ, iteratedDeriv r (fun z => ∫ v, K v * Φ z v) 0 = ∫ v, K v * iteratedDeriv r (fun z => Φ z v) 0 ∧ Continuous (fun v => iteratedDeriv r (fun z => Φ z v) 0) ∧ ∃ C' : ℝ, ∀ v, ‖iteratedDeriv r (fun z => Φ z v) 0‖ ≤ C' * Real.exp (-δ * ∑ a, ∑ j, ‖v a j‖ ^ 2) := by
  first | exact @GlobalTheory.CompanionTheory.HolMean.GaussianFamily.main | exact GlobalTheory.CompanionTheory.HolMean.GaussianFamily.main | (intros; apply GlobalTheory.CompanionTheory.HolMean.GaussianFamily.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IteratedDerivIntegralGaussianExponential
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IteratedDerivIntegralGaussianExponential
open MeasureTheory Filter Topology

namespace GlobalTheory.CompanionTheory.HolMean.DilatedGaussian

lemma integrable_gauss_complex :
    Integrable (fun w : ℂ => Real.exp (-Real.pi * ‖w‖ ^ 2)) := by
  have hb : 0 < ((Real.pi : ℂ)).re := by simpa using Real.pi_pos
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) hb 0 0).norm
  refine h.congr (Filter.Eventually.of_forall fun w => ?_)
  simp only [inner_zero_left, Complex.ofReal_zero, mul_zero, zero_mul, add_zero, Complex.norm_exp]
  rw [← Complex.ofReal_pow, ← Complex.ofReal_neg, ← Complex.ofReal_mul, Complex.ofReal_re]

lemma integrable_gauss (m n : ℕ) :
    Integrable (fun v : Fin m → Fin n → ℂ =>
      Real.exp (-Real.pi * ∑ a, ∑ j, ‖v a j‖ ^ 2)) := by
  have h1 : Integrable (fun u : Fin n → ℂ => ∏ j, Real.exp (-Real.pi * ‖u j‖ ^ 2)) :=
    Integrable.fintype_prod (f := fun (_ : Fin n) (w : ℂ) => Real.exp (-Real.pi * ‖w‖ ^ 2))
      (μ := fun _ => volume) (fun _ => integrable_gauss_complex)
  have h2 : Integrable (fun v : Fin m → Fin n → ℂ => ∏ a, ∏ j, Real.exp (-Real.pi * ‖v a j‖ ^ 2)) :=
    Integrable.fintype_prod (f := fun (_ : Fin m) (u : Fin n → ℂ) => ∏ j, Real.exp (-Real.pi * ‖u j‖ ^ 2))
      (μ := fun _ => volume) (fun _ => h1)
  refine h2.congr (Filter.Eventually.of_forall fun v => ?_)
  simp only [← Real.exp_sum, Finset.mul_sum]

noncomputable def dilated (m n : ℕ) (X : Fin n → ℝ) (v : Fin m → Fin n → ℂ) (z : ℂ) : ℂ :=
  Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ)) *
    Complex.exp (-(2 * Real.pi : ℂ) * ∑ a, ∑ j, Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ))

lemma differentiable_dilated (m n : ℕ) (X : Fin n → ℝ) (v : Fin m → Fin n → ℂ) :
    Differentiable ℂ (dilated m n X v) := by
  unfold dilated
  fun_prop

lemma continuous_dilated (m n : ℕ) (X : Fin n → ℝ) (z : ℂ) :
    Continuous (fun v : Fin m → Fin n → ℂ => dilated m n X v z) := by
  unfold dilated
  first
  | fun_prop
  | exact continuous_const.mul (Continuous.cexp (continuous_const.mul
      (continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun j _ => continuous_const.mul
        (Complex.continuous_ofReal.comp ((continuous_norm.comp ((continuous_apply j).comp (continuous_apply a))).pow 2)))))

lemma eventually_small (m n : ℕ) (X : Fin n → ℝ) :
    ∀ᶠ z : ℂ in 𝓝 0, (∀ j, 1 / 2 ≤ (Complex.exp (2 * z * X j)).re) ∧
      ‖Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ))‖ ≤ 2 := by
  have hre : ∀ j, ∀ᶠ z : ℂ in 𝓝 0, 1 / 2 ≤ (Complex.exp (2 * z * X j)).re := by
    intro j
    have hc : Continuous fun z : ℂ => (Complex.exp (2 * z * X j)).re := by fun_prop
    have h0 : (1 / 2 : ℝ) < (Complex.exp (2 * 0 * X j)).re := by norm_num
    exact ((hc.tendsto 0).eventually (lt_mem_nhds h0)).mono fun z hz => hz.le
  have hn : ∀ᶠ z : ℂ in 𝓝 0, ‖Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ))‖ ≤ 2 := by
    have hc : Continuous fun z : ℂ => ‖Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ))‖ := by fun_prop
    have h0 : ‖Complex.exp ((m : ℂ) * 0 * ∑ j, (X j : ℂ))‖ < 2 := by norm_num
    exact ((hc.tendsto 0).eventually (gt_mem_nhds h0)).mono fun z hz => hz.le
  exact (Filter.eventually_all.2 hre).and hn

lemma norm_dilated_le (m n : ℕ) (X : Fin n → ℝ) (z : ℂ)
    (h1 : ∀ j, 1 / 2 ≤ (Complex.exp (2 * z * X j)).re)
    (h2 : ‖Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ))‖ ≤ 2) (v : Fin m → Fin n → ℂ) :
    ‖dilated m n X v z‖ ≤ 2 * Real.exp (-Real.pi * ∑ a, ∑ j, ‖v a j‖ ^ 2) := by
  unfold dilated
  rw [norm_mul]
  have hre : (-(2 * Real.pi : ℂ) * ∑ a, ∑ j, Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ)).re
      = -(2 * Real.pi) * ∑ a, ∑ j, (Complex.exp (2 * z * X j)).re * ‖v a j‖ ^ 2 := by
    have e : (-(2 * Real.pi : ℂ)) = ((-(2 * Real.pi) : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.re_ofReal_mul, Complex.re_sum]
    simp only [Complex.re_sum, Complex.re_mul_ofReal]
  have hS : ∑ a, ∑ j, (1 / 2 : ℝ) * ‖v a j‖ ^ 2 ≤
      ∑ a, ∑ j, (Complex.exp (2 * z * X j)).re * ‖v a j‖ ^ 2 :=
    Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_right (h1 j) (sq_nonneg _)
  have hT : ∑ a, ∑ j, (1 / 2 : ℝ) * ‖v a j‖ ^ 2 = (1 / 2) * ∑ a, ∑ j, ‖v a j‖ ^ 2 := by
    simp only [Finset.mul_sum]
  have key : -(2 * Real.pi) * ∑ a, ∑ j, (Complex.exp (2 * z * X j)).re * ‖v a j‖ ^ 2 ≤
      -Real.pi * ∑ a, ∑ j, ‖v a j‖ ^ 2 := by
    rw [hT] at hS
    nlinarith [Real.pi_pos]
  refine mul_le_mul h2 ?_ (norm_nonneg _) (by norm_num)
  rw [Complex.norm_exp, hre]
  exact Real.exp_le_exp.2 key

theorem holomorphic_integral (m n : ℕ) (X : Fin n → ℝ) (K : (Fin m → Fin n → ℂ) → ℂ)
    (hK : Continuous K) (hK1 : ∀ v, ‖K v‖ ≤ 1) :
    ∃ ρ : ℝ, 0 < ρ ∧ DifferentiableOn ℂ (fun z : ℂ => ∫ v, K v * (Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ)) * Complex.exp (-(2 * Real.pi : ℂ) * ∑ a, ∑ j, Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ)))) (Metric.ball 0 ρ) ∧ ∀ r : ℕ, iteratedDeriv r (fun z : ℂ => ∫ v, K v * (Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ)) * Complex.exp (-(2 * Real.pi : ℂ) * ∑ a, ∑ j, Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ)))) 0 = ∫ v, K v * iteratedDeriv r (fun z : ℂ => (Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ)) * Complex.exp (-(2 * Real.pi : ℂ) * ∑ a, ∑ j, Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ)))) 0 := by
  have hcm : ∀ (c : ℂ) (f : ℂ → ℂ) (r : ℕ),
      iteratedDeriv r (fun w => c * f w) = fun w => c * iteratedDeriv r f w := by
    intro c f r
    induction r with
    | zero => simp only [iteratedDeriv_zero]
    | succ r ih => rw [iteratedDeriv_succ, ih, deriv_const_mul_field', iteratedDeriv_succ]
  obtain ⟨ρ, hρ, hsmall⟩ := Metric.eventually_nhds_iff_ball.1 (eventually_small m n X)
  have hU : IsOpen (Metric.ball (0 : ℂ) ρ) := Metric.isOpen_ball
  have hd : ∀ v : Fin m → Fin n → ℂ,
      DifferentiableOn ℂ (fun z => K v * dilated m n X v z) (Metric.ball (0 : ℂ) ρ) :=
    fun v => ((differentiable_dilated m n X v).const_mul (K v)).differentiableOn
  have hm : ∀ z ∈ Metric.ball (0 : ℂ) ρ,
      AEStronglyMeasurable (fun v : Fin m → Fin n → ℂ => K v * dilated m n X v z) volume :=
    fun z _ => (hK.mul (continuous_dilated m n X z)).aestronglyMeasurable
  have hb : ∀ z₀ ∈ Metric.ball (0 : ℂ) ρ, ∃ V ∈ 𝓝 z₀, ∃ g : (Fin m → Fin n → ℂ) → ℝ,
      Integrable g volume ∧ ∀ z ∈ V ∩ Metric.ball (0 : ℂ) ρ, ∀ v,
        ‖K v * dilated m n X v z‖ ≤ g v := by
    intro z₀ _
    refine ⟨Set.univ, Filter.univ_mem,
      fun v => 2 * Real.exp (-Real.pi * ∑ a, ∑ j, ‖v a j‖ ^ 2),
      (integrable_gauss m n).const_mul 2, ?_⟩
    intro z hz v
    obtain ⟨h1, h2⟩ := hsmall z hz.2
    rw [norm_mul]
    calc ‖K v‖ * ‖dilated m n X v z‖
        ≤ 1 * (2 * Real.exp (-Real.pi * ∑ a, ∑ j, ‖v a j‖ ^ 2)) :=
          mul_le_mul (hK1 v) (norm_dilated_le m n X z h1 h2 v) (norm_nonneg _) zero_le_one
      _ = 2 * Real.exp (-Real.pi * ∑ a, ∑ j, ‖v a j‖ ^ 2) := one_mul _
  have hstep := integral_step (μ := volume) hU (fun z v => K v * dilated m n X v z) hd hm hb
  refine ⟨ρ, hρ, ?_, ?_⟩
  · intro z hz
    exact (hstep.1 z hz).differentiableAt.differentiableWithinAt
  · intro r
    have h := iteratedDeriv_integral (μ := volume) hU r (fun z v => K v * dilated m n X v z)
      hd hm hb 0 (Metric.mem_ball_self hρ)
    refine h.trans ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    exact congrFun (hcm (K v) _ r) 0

end GlobalTheory.CompanionTheory.HolMean.DilatedGaussian
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IteratedDerivIntegralGaussianExponentialStatement
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iteratedDeriv_integral_gaussian_exponential : ∀ (m n : ℕ) (X : Fin n → ℝ) (K : (Fin m → Fin n → ℂ) → ℂ), Continuous K → (∀ v, ‖K v‖ ≤ 1) → ∃ ρ : ℝ, 0 < ρ ∧ DifferentiableOn ℂ (fun z : ℂ => ∫ v, K v * (Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ)) * Complex.exp (-(2 * Real.pi : ℂ) * ∑ a, ∑ j, Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ)))) (Metric.ball 0 ρ) ∧ ∀ r : ℕ, iteratedDeriv r (fun z : ℂ => ∫ v, K v * (Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ)) * Complex.exp (-(2 * Real.pi : ℂ) * ∑ a, ∑ j, Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ)))) 0 = ∫ v, K v * iteratedDeriv r (fun z : ℂ => (Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ)) * Complex.exp (-(2 * Real.pi : ℂ) * ∑ a, ∑ j, Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ)))) 0 := by
  first | exact @GlobalTheory.CompanionTheory.HolMean.DilatedGaussian.holomorphic_integral | exact GlobalTheory.CompanionTheory.HolMean.DilatedGaussian.holomorphic_integral | (intros; apply GlobalTheory.CompanionTheory.HolMean.DilatedGaussian.holomorphic_integral <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierInjectiveMatrixSpace
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierInjectiveMatrixSpace
open MeasureTheory
open scoped Matrix FourierTransform InnerProductSpace ComplexConjugate

namespace GlobalTheory.CompanionTheory.FourierMat

noncomputable def entries (m n : ℕ) :
    (Fin m → Fin n → ℂ) ≃L[ℝ] EuclideanSpace ℂ (Fin m × Fin n) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun u => WithLp.toLp 2 (fun p => u p.1 p.2)
      invFun := fun x a j => x (a, j)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem entries_apply (m n : ℕ) (u : Fin m → Fin n → ℂ) (p : Fin m × Fin n) :
    entries m n u p = u p.1 p.2 := rfl

theorem pairing {m n : ℕ} {s : ℂ} (hs : s ≠ 0) (w : EuclideanSpace ℂ (Fin m × Fin n))
    (v : Fin m → Fin n → ℂ) :
    (s * Matrix.trace ((Matrix.of fun a j => -(w (a, j)) / conj s)ᴴ * Matrix.of v)).re =
      -(⟪entries m n v, w⟫_ℝ) := by
  have key : s * Matrix.trace ((Matrix.of fun a j => -(w (a, j)) / conj s)ᴴ * Matrix.of v)
      = -(∑ a, ∑ j, conj (w (a, j)) * v a j) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.of_apply]
    rw [Finset.sum_comm, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [star_div₀, star_neg, Complex.star_def, Complex.conj_conj]
    field_simp
  rw [key, PiLp.inner_apply, Fintype.sum_prod_type, Complex.neg_re, Complex.re_sum]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.inner]
  simp only [entries_apply, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

theorem fourier_uniqueness : ∀ (m n : ℕ) (s : ℂ), s ≠ 0 → ∀ g : (Fin m → Fin n → ℂ) → ℂ,
    Continuous g → Integrable g →
    (∀ u : Fin m → Fin n → ℂ, ∫ v, Complex.exp (2 * Real.pi * Complex.I *
      ((s * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re : ℂ)) * g v = 0) → g = 0 := by
  intro m n s hs g hgc hgi hF
  have hemb : MeasurableEmbedding (entries m n) := (entries m n).toHomeomorph.measurableEmbedding
  have hC : (volume : Measure ℂ).IsAddHaarMeasure := inferInstance
  have hV1 : (volume : Measure (Fin n → ℂ)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure (fun _ => volume)
  have hV2 : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure (fun _ => volume)
  have : (Measure.map (entries m n) (volume : Measure (Fin m → Fin n → ℂ))).IsAddHaarMeasure :=
    (entries m n).isAddHaarMeasure_map volume
  have hμ := Measure.isAddLeftInvariant_eq_smul
    (Measure.map (entries m n) (volume : Measure (Fin m → Fin n → ℂ)))
    (volume : Measure (EuclideanSpace ℂ (Fin m × Fin n)))
  have hcpos := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure
    (Measure.map (entries m n) (volume : Measure (Fin m → Fin n → ℂ)))
    (volume : Measure (EuclideanSpace ℂ (Fin m × Fin n)))
  have hcomp : (fun x => g ((entries m n).symm x)) ∘ (entries m n) = g := by
    funext v
    simp
  have hGmap : Integrable (fun x => g ((entries m n).symm x))
      (Measure.map (entries m n) (volume : Measure (Fin m → Fin n → ℂ))) :=
    hemb.integrable_map_iff.mpr (by rw [hcomp]; exact hgi)
  rw [hμ, ← Measure.coe_nnreal_smul] at hGmap
  have hGi : Integrable (fun x => g ((entries m n).symm x))
      (volume : Measure (EuclideanSpace ℂ (Fin m × Fin n))) :=
    (integrable_smul_measure (ENNReal.coe_ne_zero.mpr hcpos.ne') ENNReal.coe_ne_top).mp hGmap
  have hGc : Continuous (fun x => g ((entries m n).symm x)) :=
    hgc.comp (entries m n).symm.continuous
  have hFG : FourierTransform.fourier (fun x => g ((entries m n).symm x)) = 0 := by
    funext w
    rw [Real.fourier_eq', Pi.zero_apply]
    have h0 := hF (fun a j => -(w (a, j)) / conj s)
    have h1 : ∫ x, Complex.exp (↑(-2 * Real.pi * ⟪x, w⟫_ℝ) * Complex.I) • g ((entries m n).symm x)
        ∂(Measure.map (entries m n) (volume : Measure (Fin m → Fin n → ℂ))) = 0 := by
      rw [hemb.integral_map]
      refine Eq.trans ?_ h0
      congr 1
      funext v
      rw [pairing hs w v]
      simp only [ContinuousLinearEquiv.symm_apply_apply, smul_eq_mul]
      congr 2
      push_cast
      ring
    rw [hμ, integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_zero] at h1
    exact h1.resolve_left (by exact_mod_cast hcpos.ne')
  have hinv := Continuous.fourierInv_fourier_eq hGc hGi
    (by rw [hFG]; exact integrable_zero _ _ _)
  rw [hFG] at hinv
  funext v
  have hx := congrFun hinv ((entries m n) v)
  rw [Real.fourierInv_eq'] at hx
  simp only [Pi.zero_apply, smul_zero, integral_zero, ContinuousLinearEquiv.symm_apply_apply] at hx
  rw [Pi.zero_apply]
  exact hx.symm

end GlobalTheory.CompanionTheory.FourierMat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierInjectiveMatrixSpaceStatement
open MeasureTheory
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourier_injective_matrix_space : ∀ (m n : ℕ) (s : ℂ), s ≠ 0 → ∀ g : (Fin m → Fin n → ℂ) → ℂ, Continuous g → Integrable g → (∀ u : Fin m → Fin n → ℂ, ∫ v, Complex.exp (2 * Real.pi * Complex.I * ((s * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re : ℂ)) * g v = 0) → g = 0 := by
  first | exact @GlobalTheory.CompanionTheory.FourierMat.fourier_uniqueness | exact GlobalTheory.CompanionTheory.FourierMat.fourier_uniqueness | (intros; apply GlobalTheory.CompanionTheory.FourierMat.fourier_uniqueness <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IteratedDerivEqOfEqOnRealSegment
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IteratedDerivEqOfEqOnRealSegment
open Filter Topology

namespace GlobalTheory.CompanionTheory.ComplexAnalysis

theorem iteratedDeriv_zero_eq_of_eq_on_real_points (f g : ℂ → ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hf : DifferentiableOn ℂ f (Metric.ball 0 ρ)) (hg : DifferentiableOn ℂ g (Metric.ball 0 ρ))
    (h : ∀ s : ℝ, |s| < ρ → f s = g s) (r : ℕ) :
    iteratedDeriv r f 0 = iteratedDeriv r g 0 := by

  have hU : IsOpen (Metric.ball (0 : ℂ) ρ) := Metric.isOpen_ball
  have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) ρ := Metric.mem_ball_self hρ
  have hreal : ∀ᶠ s : ℝ in 𝓝[≠] 0, f s = g s := by
    have hs : {s : ℝ | |s| < ρ} ∈ 𝓝 (0 : ℝ) :=
      (isOpen_lt continuous_abs continuous_const).mem_nhds (by simpa using hρ)
    exact Filter.mem_of_superset (nhdsWithin_le_nhds hs) fun s hs' => h s hs'
  have htend : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[≠] 0) (𝓝[≠] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hc := Complex.continuous_ofReal.tendsto (0 : ℝ)
      simpa using hc.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      simpa using hs
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), f z = g z := htend.frequently hreal.frequently
  have heq : Set.EqOn f g (Metric.ball 0 ρ) :=
    (hf.analyticOnNhd hU).eqOn_of_preconnected_of_frequently_eq (hg.analyticOnNhd hU)
      (convex_ball (0 : ℂ) ρ).isPreconnected h0 hfreq
  have hev : f =ᶠ[𝓝 0] g := Filter.mem_of_superset (hU.mem_nhds h0) heq
  exact hev.iteratedDeriv_eq r

end GlobalTheory.CompanionTheory.ComplexAnalysis
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IteratedDerivEqOfEqOnRealSegmentStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iteratedDeriv_eq_of_eq_on_real_segment : ∀ (f g : ℂ → ℂ) (ρ : ℝ), 0 < ρ → DifferentiableOn ℂ f (Metric.ball 0 ρ) → DifferentiableOn ℂ g (Metric.ball 0 ρ) → (∀ s : ℝ, |s| < ρ → f s = g s) → ∀ r : ℕ, iteratedDeriv r f 0 = iteratedDeriv r g 0 := by
  first | exact @GlobalTheory.CompanionTheory.ComplexAnalysis.iteratedDeriv_zero_eq_of_eq_on_real_points | exact GlobalTheory.CompanionTheory.ComplexAnalysis.iteratedDeriv_zero_eq_of_eq_on_real_points | (intros; apply GlobalTheory.CompanionTheory.ComplexAnalysis.iteratedDeriv_zero_eq_of_eq_on_real_points <;> assumption)
end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.LocAlgPf
noncomputable section

open scoped Matrix
open MeasureTheory PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Kdil

open PositivityTheory.Rg.Sw.Glob (actZ)
open Matrix

variable {n : ℕ}

theorem up_decomp_pf (p : GR n) (hp : (mR p).toBlocks₂₁ = 0) :
    ∃ (nb ma : GR n) (b a : Matrix (Fin n) (Fin n) ℂ), bᴴ = b ∧ IsUnit a.det ∧ mR nb = nU b ∧ mR ma = mLoc a ∧
      p = nb * ma ∧ actZ p (Complex.I • 1) = b + Complex.I • (a * aᴴ) :=
  GlobalTheory.T.parabolic_decomposition_upper_half_space n p hp

theorem fam_deriv_pf (m : ℕ) (X : Fin n → ℝ) (v : Fin m → Fin n → ℂ) (r : ℕ) :
    iteratedDeriv r (fun z => fam m X z v) 0 = fP ((dil (2 * Real.pi) X ^ r) 1) v :=
  (GlobalTheory.T.iteratedDeriv_gaussian_exponential_at_zero m n X v).2 r

theorem fam_int_hol_pf (m : ℕ) (X : Fin n → ℝ) (K : (Fin m → Fin n → ℂ) → ℂ) (hK : Continuous K)
    (hK1 : ∀ v, ‖K v‖ ≤ 1) :
    ∃ ρ : ℝ, 0 < ρ ∧ DifferentiableOn ℂ (fun z => ∫ v, K v * fam m X z v) (Metric.ball 0 ρ) ∧
      ∀ r : ℕ, iteratedDeriv r (fun z => ∫ v, K v * fam m X z v) 0 =
        ∫ v, K v * iteratedDeriv r (fun z => fam m X z v) 0 :=
  GlobalTheory.T.iteratedDeriv_integral_gaussian_exponential m n X K hK hK1

theorem iteratedDeriv_eq_of_real_pf {f g : ℂ → ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hf : DifferentiableOn ℂ f (Metric.ball 0 ρ))
    (hg : DifferentiableOn ℂ g (Metric.ball 0 ρ)) (hfg : ∀ s : ℝ, |s| < ρ → f s = g s) (r : ℕ) :
    iteratedDeriv r f 0 = iteratedDeriv r g 0 :=
  GlobalTheory.T.iteratedDeriv_eq_of_eq_on_real_segment f g ρ hρ hf hg hfg r

theorem dcell_pf (y : GR n) (hy : ((mR y).toBlocks₂₂).det ≠ 0) :
    ∃ (p nbb : GR n) (c : Matrix (Fin n) (Fin n) ℂ), (mR p).toBlocks₂₁ = 0 ∧ cᴴ = c ∧ mR nbb = nbLoc c ∧ y = p * nbb :=
  GlobalTheory.T.bruhat_cell_parabolic_unipotent_factorization n y hy

theorem hol_int_pf {m : ℕ} (Φ : ℂ → (Fin m → Fin n → ℂ) → ℂ) (ρ C δ : ℝ) (hρ : 0 < ρ) (hδ : 0 < δ)
    (hd : ∀ v, DifferentiableOn ℂ (fun z => Φ z v) (Metric.ball 0 ρ))
    (hc : ContinuousOn (fun zv : ℂ × (Fin m → Fin n → ℂ) => Φ zv.1 zv.2) (Metric.ball 0 ρ ×ˢ Set.univ))
    (hb : ∀ z ∈ Metric.ball (0 : ℂ) ρ, ∀ v, ‖Φ z v‖ ≤ C * Real.exp (-δ * sq v))
    (K : (Fin m → Fin n → ℂ) → ℂ) (hK : Continuous K) (hK1 : ∀ v, ‖K v‖ ≤ 1) :
    ∃ ρ' : ℝ, 0 < ρ' ∧ DifferentiableOn ℂ (fun z => ∫ v, K v * Φ z v) (Metric.ball 0 ρ') ∧
      ∀ r : ℕ, iteratedDeriv r (fun z => ∫ v, K v * Φ z v) 0 = ∫ v, K v * iteratedDeriv r (fun z => Φ z v) 0 ∧
        Continuous (fun v => iteratedDeriv r (fun z => Φ z v) 0) ∧
        ∃ C' : ℝ, ∀ v, ‖iteratedDeriv r (fun z => Φ z v) 0‖ ≤ C' * Real.exp (-δ * sq v) :=
  GlobalTheory.T.holomorphic_parameter_integral_gaussian_bound m n Φ ρ C δ hρ hδ hd hc hb K hK hK1

theorem ft_uniq_pf {m : ℕ} (s : ℂ) (hs : s ≠ 0) (g : (Fin m → Fin n → ℂ) → ℂ) (hg : Continuous g) (hgi : Integrable g)
    (h0 : ∀ u : Fin m → Fin n → ℂ, ∫ v, Complex.exp (2 * Real.pi * Complex.I *
      ((s * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re : ℂ)) * g v = 0) : g = 0 :=
  GlobalTheory.T.fourier_injective_matrix_space m n s hs g hg hgi h0

theorem up_decomp_closed : type_of% @up_decomp_pf := @up_decomp_pf

theorem fam_deriv_closed : type_of% @fam_deriv_pf := @fam_deriv_pf

theorem fam_int_hol_closed : type_of% @fam_int_hol_pf := @fam_int_hol_pf

theorem iteratedDeriv_eq_of_real_closed : type_of% @iteratedDeriv_eq_of_real_pf := @iteratedDeriv_eq_of_real_pf

theorem dcell_closed : type_of% @dcell_pf := @dcell_pf

theorem hol_int_closed : type_of% @hol_int_pf := @hol_int_pf

theorem ft_uniq_closed : type_of% @ft_uniq_pf := @ft_uniq_pf

end PositivityTheory.SiegelWeilFormula.Kdil

end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.LocGaussPf
noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.Kdil

theorem gauss_int_one (δ : ℝ) (hδ : 0 < δ) : Integrable (fun z : ℂ => Real.exp (-δ * ‖z‖ ^ 2)) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) (b := (δ : ℂ))
    (by simpa using hδ) 0 0
  refine h.norm.congr (Filter.Eventually.of_forall fun z => ?_)
  simp only [zero_mul, add_zero, Complex.norm_exp]
  rw [show (-(δ : ℂ) * (‖z‖ : ℂ) ^ 2) = ((-δ * ‖z‖ ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]

theorem gauss_int_row {n : ℕ} (δ : ℝ) (hδ : 0 < δ) :
    Integrable (fun u : Fin n → ℂ => ∏ j, Real.exp (-δ * ‖u j‖ ^ 2)) := by
  exact Integrable.fintype_prod (f := fun _ (z : ℂ) => Real.exp (-δ * ‖z‖ ^ 2))
    (fun _ => gauss_int_one δ hδ)

theorem gauss_int_mat {m n : ℕ} (δ : ℝ) (hδ : 0 < δ) :
    Integrable (fun v : Fin m → Fin n → ℂ => ∏ a, ∏ j, Real.exp (-δ * ‖v a j‖ ^ 2)) := by
  exact Integrable.fintype_prod (f := fun _ (w : Fin n → ℂ) => ∏ j, Real.exp (-δ * ‖w j‖ ^ 2))
    (fun _ => gauss_int_row δ hδ)

theorem gauss_int_pf {m n : ℕ} (δ : ℝ) (hδ : 0 < δ) :
    Integrable (fun v : Fin m → Fin n → ℂ => Real.exp (-δ * sq v)) := by
  refine (gauss_int_mat (m := m) (n := n) δ hδ).congr (Filter.Eventually.of_forall fun v => ?_)
  simp only [PositivityTheory.SiegelWeilFormula.Kdil.sq, Finset.mul_sum, ← Real.exp_sum]

theorem gauss_int_closed : type_of% @gauss_int_pf := @gauss_int_pf

end PositivityTheory.SiegelWeilFormula.Kdil

end
end

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.Kdil

open PositivityTheory.Rg.Sw.Glob (aC ptZ jC gC actZ jF IsSiegel gZf)
open Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem fP_smul_one {m n : ℕ} (c : ℂ) : fP (c • (1 : PX m n)) = fun u => c * fP 1 u := by
  funext u
  simp only [fP, evX, MvPolynomial.smul_eval, map_one]
  ring

theorem fP_one_zero {m n : ℕ} : fP (1 : PX m n) 0 = 1 := by
  simp [fP, evX, gs]

theorem fP_one_of {m n : ℕ} (x : Fin m → Fin n → ℂ) (hx : ∀ i j, x i j = 0) : fP (1 : PX m n) x = 1 := by
  have : x = 0 := funext fun i => funext fun j => hx i j
  rw [this]; exact fP_one_zero

theorem weight_factor_unipotent_one {n : ℕ} (p q : ℕ) (e : ℤ) (y : GR n) (b : Matrix (Fin n) (Fin n) ℂ) (hy : mR y = nU b) :
    F0 p q e y = 1 := by
  simp only [F0, f0, u1, u2, hy, nU, Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂, smul_zero, zero_add,
    neg_zero, Matrix.det_one, _root_.one_zpow, mul_one, Matrix.det_fromBlocks_zero₂₁]

theorem vac_law {d : SD σ} (R : RD d) {w : InfinitePlace F}
    {L : GR d.n → ((Fin d.m → Fin d.n → ℂ) → ℂ) → (Fin d.m → Fin d.n → ℂ) → ℂ}
    (hT : TAll) (hG : GoodAwayEx) (hFP : FPSw) (hL : R.IsLocOp w L)
    {sL : PX d.m d.n →ₗ[ℂ] (GR d.n → ℂ)} {ρ : GR d.n → PX d.m d.n →ₗ[ℂ] PX d.m d.n} {p q : ℕ} {e : ℤ}
    (hLD : LocData (fun _ => true) (2 * Real.pi) (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) p q e sL ρ)
    (hsL : ∀ P y, sL P y = L y (fP P) 0) (hρ : ∀ (k : GR d.n) P, InK (mR k) → L k (fP P) = fP (ρ k P)) (y : GR d.n) :
    L y (fP 1) = fun u => F0 p q e y *
      gZf (fun _ : Fin d.m => true) (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) (2 * Real.pi) (actZ y (Complex.I • 1)) u := by
  obtain ⟨pp, k, hpp, hk, rfl⟩ := PositivityTheory.Rg.Sw.AbsSt.iwa d.n y
  have hk' : InK (mR k) := hk
  obtain ⟨nb, ma, b, a, hb, ha, hnb, hma, hpe, hZ⟩ := up_decomp_closed pp hpp
  obtain ⟨c, -, hcf⟩ := R.locOp_mM hT hG hL
  have hsw1 : IsSw (fP (1 : PX d.m d.n)) := hFP d.m d.n 1
  have hk1 : L k (fP 1) = fun u => F0 p q e k * fP 1 u := by
    rw [hρ k 1 hk', hLD.kvac k hk', fP_smul_one]
  have hma21 : (mR ma).toBlocks₂₁ = 0 := by rw [hma, mLoc, Matrix.toBlocks_fromBlocks₂₁]
  have hnb21 : (mR nb).toBlocks₂₁ = 0 := by rw [hnb, nU, Matrix.toBlocks_fromBlocks₂₁]
  have hca : c a = F0 p q e ma := by
    have h1 := hLD.law 1 ma 1 hma21
    have h0 : fP (1 : PX d.m d.n) (Matrix.of (0 : Fin d.m → Fin d.n → ℂ) * a) = 1 := by
      have e0 : (Matrix.of (0 : Fin d.m → Fin d.n → ℂ) * a : Matrix (Fin d.m) (Fin d.n) ℂ) = 0 := by
        ext i j; simp [Matrix.mul_apply]
      rw [e0]; exact fP_one_zero
    rw [mul_one, hsL, hsL, hcf ma a ha hma _ hsw1, R.locOp_one hT hG hL _ hsw1] at h1
    beta_reduce at h1
    rw [fP_one_of _ (fun i j => by
      show ∑ k, (Matrix.of (0 : Fin d.m → Fin d.n → ℂ)) i k * a k j = 0
      simp), fP_one_zero] at h1
    simpa using h1
  have hF0 : F0 p q e (pp * k) = c a * F0 p q e k := by
    have m1 := ((PositivityTheory.Rg.Sw.AbsSt.mult d.n p q e).2 pp k hpp).1
    have m2 := ((PositivityTheory.Rg.Sw.AbsSt.mult d.n p q e).2 nb ma hnb21).1
    rw [m1, hpe, m2, weight_factor_unipotent_one p q e nb b hnb, one_mul, hca]
  have hZ' : actZ (pp * k) (Complex.I • 1) = b + Complex.I • (a * aᴴ) := by rw [actZ_mul_K pp k hk', hZ]
  have hswk : IsSw (L k (fP 1)) := (hL k _ hsw1).1
  have hswm : IsSw (L ma (L k (fP 1))) := (hL ma _ hswk).1
  rw [R.locOp_mul hT hG hL pp k _ hsw1, hpe, R.locOp_mul hT hG hL nb ma _ hswk, R.locOp_nU hT hG hL nb b hb hnb _ hswm,
    hcf ma a ha hma _ hswk, ← hpe, hF0, hZ', hk1]
  funext u
  rw [gzf_eval (R.sg w) b a hb u]
  ring_nf
  rfl

theorem cont_slice {A B C : Type*} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    (f : A × B × C → ℂ) (s : Set (A × B × C)) (hf : ContinuousOn f s) (a : A) (t : Set (B × C))
    (ht : ∀ x ∈ t, (a, x.1, x.2) ∈ s) : ContinuousOn (fun x : B × C => f (a, x.1, x.2)) t :=
  hf.comp (by fun_prop) ht

theorem cont_slice2 {A B C : Type*} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    (f : A × B × C → ℂ) (s : Set (A × B × C)) (hf : ContinuousOn f s) (c : C) (t : Set (A × B))
    (ht : ∀ x ∈ t, (x.1, x.2, c) ∈ s) : ContinuousOn (fun x : A × B => f (x.1, x.2, c)) t :=
  hf.comp (by fun_prop) ht

def kerFT {m n : ℕ} (s : ℂ) (ξ v : Fin m → Fin n → ℂ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ((s * Matrix.trace ((Matrix.of ξ)ᴴ * Matrix.of v)).re : ℂ))

theorem kerFT_cont {m n : ℕ} (s : ℂ) (ξ : Fin m → Fin n → ℂ) : Continuous (kerFT s ξ) := by
  unfold kerFT
  fun_prop

theorem kerFT_norm {m n : ℕ} (s : ℂ) (ξ v : Fin m → Fin n → ℂ) : ‖kerFT s ξ v‖ ≤ 1 := by
  unfold kerFT
  rw [show (2 * Real.pi * Complex.I * ((s * Matrix.trace ((Matrix.of ξ)ᴴ * Matrix.of v)).re : ℂ)) =
    ((2 * Real.pi * (s * Matrix.trace ((Matrix.of ξ)ᴴ * Matrix.of v)).re : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I]

theorem isAddHaarMeasure_vector_volume (n : ℕ) : (volume : Measure (Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _

theorem isAddHaarMeasure_matrix_volume (m n : ℕ) : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure := by
  haveI := isAddHaarMeasure_vector_volume n
  exact Measure.pi.isAddHaarMeasure _

theorem sw_cont_int {m n : ℕ} {f : (Fin m → Fin n → ℂ) → ℂ} (hf : IsSw f) : Continuous f ∧ Integrable f := by
  obtain ⟨φ, rfl⟩ := hf
  haveI := isAddHaarMeasure_matrix_volume m n
  exact ⟨φ.continuous, φ.integrable⟩

theorem gf_L {d : SD σ} (R : RD d) {w : InfinitePlace F}
    {L : GR d.n → ((Fin d.m → Fin d.n → ℂ) → ℂ) → (Fin d.m → Fin d.n → ℂ) → ℂ}
    (hT : TAll) (hG : GoodAwayEx) (hFP : FPSw) (hL : R.IsLocOp w L)
    {sL : PX d.m d.n →ₗ[ℂ] (GR d.n → ℂ)} {ρ : GR d.n → PX d.m d.n →ₗ[ℂ] PX d.m d.n} {p q : ℕ} {e : ℤ}
    (hLD : LocData (fun _ => true) (2 * Real.pi) (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) p q e sL ρ)
    (hsL : ∀ P y, sL P y = L y (fP P) 0) (hρ : ∀ (k : GR d.n) P, InK (mR k) → L k (fP P) = fP (ρ k P))
    (X : Fin d.n → ℝ) (a : ℝ → GR d.n) (ha : ∀ s, IsDil X s (a s)) (y : GR d.n) (s : ℝ) :
    Gf e p q (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) (m := d.m) X y s = L (y * a s) (fP 1) := by
  rw [gf_real e p q _ X a ha y s, vac_law R hT hG hFP hL hLD hsL hρ (y * a s)]

theorem fam_sw {d : SD σ} (R : RD d) {w : InfinitePlace F}
    {L : GR d.n → ((Fin d.m → Fin d.n → ℂ) → ℂ) → (Fin d.m → Fin d.n → ℂ) → ℂ}
    (hT : TAll) (hG : GoodAwayEx) (hFP : FPSw) (hL : R.IsLocOp w L)
    (X : Fin d.n → ℝ) (a : ℝ → GR d.n) (ha : ∀ s, IsDil X s (a s)) (s : ℝ) :
    IsSw (fun v => fam d.m X s v) := by
  rw [← fam_eq_L_closed R hT hG hFP hL X a ha s]
  exact (hL (a s) (fP 1) (hFP _ _ 1)).1

theorem gf_L_fam {d : SD σ} (R : RD d) {w : InfinitePlace F}
    {L : GR d.n → ((Fin d.m → Fin d.n → ℂ) → ℂ) → (Fin d.m → Fin d.n → ℂ) → ℂ}
    (hT : TAll) (hG : GoodAwayEx) (hFP : FPSw) (hL : R.IsLocOp w L)
    {sL : PX d.m d.n →ₗ[ℂ] (GR d.n → ℂ)} {ρ : GR d.n → PX d.m d.n →ₗ[ℂ] PX d.m d.n} {p q : ℕ} {e : ℤ}
    (hLD : LocData (fun _ => true) (2 * Real.pi) (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) p q e sL ρ)
    (hsL : ∀ P y, sL P y = L y (fP P) 0) (hρ : ∀ (k : GR d.n) P, InK (mR k) → L k (fP P) = fP (ρ k P))
    (X : Fin d.n → ℝ) (a : ℝ → GR d.n) (ha : ∀ s, IsDil X s (a s)) (y : GR d.n) (s : ℝ) :
    Gf e p q (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) (m := d.m) X y s = L y (fun v => fam d.m X s v) := by
  rw [gf_L R hT hG hFP hL hLD hsL hρ X a ha y s, R.locOp_mul hT hG hL y (a s) (fP 1) (hFP _ _ 1),
    fam_eq_L_closed R hT hG hFP hL X a ha s]

theorem der_nbar {d : SD σ} (R : RD d) {w : InfinitePlace F}
    {L : GR d.n → ((Fin d.m → Fin d.n → ℂ) → ℂ) → (Fin d.m → Fin d.n → ℂ) → ℂ}
    (hT : TAll) (hA : AuxiliaryPrimeFunction) (hG : GoodAwayEx) (hFP : FPSw) (hL : R.IsLocOp w L) (hB : GfBound)
    {sL : PX d.m d.n →ₗ[ℂ] (GR d.n → ℂ)} {ρ : GR d.n → PX d.m d.n →ₗ[ℂ] PX d.m d.n} {p q : ℕ} {e : ℤ}
    (hLD : LocData (fun _ => true) (2 * Real.pi) (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) p q e sL ρ)
    (hsL : ∀ P y, sL P y = L y (fP P) 0) (hρ : ∀ (k : GR d.n) P, InK (mR k) → L k (fP P) = fP (ρ k P))
    (X : Fin d.n → ℝ) (a : ℝ → GR d.n) (ha : ∀ s, IsDil X s (a s))
    (nbb : GR d.n) (c : Matrix (Fin d.n) (Fin d.n) ℂ) (hc : cᴴ = c) (hnbb : mR nbb = nbLoc c) (r : ℕ) :
    (fun v => iteratedDeriv r (fun z => Gf e p q (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) (m := d.m) X nbb z v) 0) =
      L nbb (fP ((dil (2 * Real.pi) X ^ r) 1)) := by
  obtain ⟨C, s', κ, ε, hs', hκ, h4, -, hconj, -, -⟩ := R.locOp_nbar hT hA hG hL
  obtain ⟨hhol, hcont, hbd⟩ := hB d.m d.n e p q (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) X (abs_tw R w)
  have h0s : (0 : ℂ) ∈ strip X := fun j => by simp [Real.pi_pos]
  obtain ⟨N, δ, Cb, hN, hδ, hNb⟩ := hbd nbb 0 h0s
  obtain ⟨ρs, hρs, hss⟩ := strip_ball X
  have hev : (fun z : ℂ => (nbb, z)) ⁻¹' N ∈ 𝓝 (0 : ℂ) :=
    (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds hN
  obtain ⟨ρ0, hρ0, hball⟩ := Metric.mem_nhds_iff.1 hev
  set rr := min ρ0 ρs with hrrdef
  have hrr : 0 < rr := lt_min hρ0 hρs
  have hsub : Metric.ball (0 : ℂ) rr ⊆ strip X := (Metric.ball_subset_ball (min_le_right _ _)).trans hss
  have hsubN : ∀ z ∈ Metric.ball (0 : ℂ) rr, (nbb, z) ∈ N := fun z hz =>
    hball (Metric.ball_subset_ball (min_le_left _ _) hz)
  set Φ : ℂ → (Fin d.m → Fin d.n → ℂ) → ℂ := fun z v => Gf e p q (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) X nbb z v with hΦ
  have hΦd : ∀ v, DifferentiableOn ℂ (fun z => Φ z v) (Metric.ball 0 rr) := fun v => (hhol nbb v).mono hsub
  have hΦc : ContinuousOn (fun zv : ℂ × (Fin d.m → Fin d.n → ℂ) => Φ zv.1 zv.2) (Metric.ball 0 rr ×ˢ Set.univ) :=
    cont_slice _ _ hcont nbb _ fun zv hzv => ⟨Set.mem_univ _, hsub hzv.1, Set.mem_univ _⟩
  have hΦb : ∀ z ∈ Metric.ball (0 : ℂ) rr, ∀ v, ‖Φ z v‖ ≤ Cb * Real.exp (-δ * sq v) := by
    intro z hz v
    have h := hNb (nbb, z) (hsubN z hz) (hsub hz) v
    simpa [sq, neg_mul] using h
  have hC : C ≠ 0 := by
    intro hC0
    have h := congrFun (h4 _ (hFP d.m d.n 1)) 0
    simp only [locFT, hC0, zero_mul, Pi.smul_apply, smul_eq_mul, fP_one_zero, mul_one] at h
    exact hκ h.symm
  set P : PX d.m d.n := (dil (2 * Real.pi) X ^ r) 1 with hP
  have hGsw : IsSw (L nbb (fP P)) := (hL nbb _ (hFP _ _ P)).1
  obtain ⟨hGc, hGi⟩ := sw_cont_int hGsw
  obtain ⟨ρ9, hρ9, -, hr9⟩ := hol_int_closed Φ rr Cb δ hrr hδ hΦd hΦc hΦb (kerFT s' 0) (kerFT_cont s' 0) (kerFT_norm s' 0)
  obtain ⟨-, hDc, C', hDb⟩ := hr9 r
  have hDi : Integrable (fun v => iteratedDeriv r (fun z => Φ z v) 0) := by
    refine Integrable.mono' ((gauss_int_closed δ hδ).const_mul C') hDc.aestronglyMeasurable (Filter.Eventually.of_forall fun v => ?_)
    exact hDb v
  have key : ∀ ξ : Fin d.m → Fin d.n → ℂ, ∫ v, kerFT s' ξ v * iteratedDeriv r (fun z => Φ z v) 0 =
      ∫ v, kerFT s' ξ v * L nbb (fP P) v := by
    intro ξ
    obtain ⟨ρ1, hρ1, hd1, hr1⟩ := hol_int_closed Φ rr Cb δ hrr hδ hΦd hΦc hΦb (kerFT s' ξ) (kerFT_cont s' ξ) (kerFT_norm s' ξ)
    obtain ⟨ρ2, hρ2, hd2, hr2⟩ := fam_int_hol_closed d.m X (kerFT s' ξ) (kerFT_cont s' ξ) (kerFT_norm s' ξ)
    set ch : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((R.sg w : ℤ) : ℂ) *
      Matrix.trace (((((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c) * ((Matrix.of ξ)ᴴ * Matrix.of ξ))) with hch
    have hreal : ∀ s : ℝ, |s| < min ρ1 ρ2 → C * (∫ v, kerFT s' ξ v * Φ s v) = ch * (C * ∫ v, kerFT s' ξ v * fam d.m X s v) := by
      intro s _
      have e1 : ∀ v, Φ s v = L nbb (fun v => fam d.m X s v) v := fun v =>
        congrFun (gf_L_fam R hT hG hFP hL hLD hsL hρ X a ha nbb s) v
      simp only [e1]
      exact congrFun (hconj nbb c hc hnbb _ (fam_sw R hT hG hFP hL X a ha s)) ξ
    have hid := iteratedDeriv_eq_of_real_closed (f := fun z => C * ∫ v, kerFT s' ξ v * Φ z v)
      (g := fun z => ch * (C * ∫ v, kerFT s' ξ v * fam d.m X z v)) (ρ := min ρ1 ρ2) (lt_min hρ1 hρ2)
      ((hd1.mono (Metric.ball_subset_ball (min_le_left _ _))).const_mul C)
      (((hd2.mono (Metric.ball_subset_ball (min_le_right _ _))).const_mul C).const_mul ch) hreal r
    rw [iteratedDeriv_const_mul', iteratedDeriv_const_mul', iteratedDeriv_const_mul'] at hid
    beta_reduce at hid
    rw [(hr1 r).1, hr2 r] at hid
    simp only [fam_deriv_closed] at hid
    have h2 : C * ∫ v, kerFT s' ξ v * L nbb (fP P) v = ch * (C * ∫ v, kerFT s' ξ v * fP P v) :=
      congrFun (hconj nbb c hc hnbb _ (hFP _ _ P)) ξ
    exact mul_left_cancel₀ hC (hid.trans h2.symm)
  have hint : ∀ ξ : Fin d.m → Fin d.n → ℂ, ∀ g : (Fin d.m → Fin d.n → ℂ) → ℂ, Integrable g →
      Integrable (fun v => kerFT s' ξ v * g v) := fun ξ g hg =>
    MeasureTheory.Integrable.bdd_mul hg (kerFT_cont s' ξ).aestronglyMeasurable
      (Filter.Eventually.of_forall fun v => kerFT_norm s' ξ v)
  have hfin := ft_uniq_closed s' hs' (fun v => iteratedDeriv r (fun z => Φ z v) 0 - L nbb (fP P) v) (hDc.sub hGc)
    (hDi.sub hGi) (fun ξ => by
      have h := key ξ
      rw [← sub_eq_zero, ← integral_sub (hint ξ _ hDi) (hint ξ _ hGi)] at h
      simpa [kerFT, mul_sub] using h)
  funext v
  exact sub_eq_zero.1 (congrFun hfin v)

theorem gf_der_big {d : SD σ} (R : RD d) {w : InfinitePlace F}
    {L : GR d.n → ((Fin d.m → Fin d.n → ℂ) → ℂ) → (Fin d.m → Fin d.n → ℂ) → ℂ}
    (hT : TAll) (hA : AuxiliaryPrimeFunction) (hG : GoodAwayEx) (hFP : FPSw) (hL : R.IsLocOp w L) (hB : GfBound)
    {sL : PX d.m d.n →ₗ[ℂ] (GR d.n → ℂ)} {ρ : GR d.n → PX d.m d.n →ₗ[ℂ] PX d.m d.n} {p q : ℕ} {e : ℤ}
    (hLD : LocData (fun _ => true) (2 * Real.pi) (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) p q e sL ρ)
    (hsL : ∀ P y, sL P y = L y (fP P) 0) (hρ : ∀ (k : GR d.n) P, InK (mR k) → L k (fP P) = fP (ρ k P))
    (X : Fin d.n → ℝ) (a : ℝ → GR d.n) (ha : ∀ s, IsDil X s (a s)) (y : GR d.n) (hy : ((mR y).toBlocks₂₂).det ≠ 0)
    (r : ℕ) (u : Fin d.m → Fin d.n → ℂ) :
    iteratedDeriv r (fun z => Gf e p q (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) X y z u) 0 =
      L y (fP ((dil (2 * Real.pi) X ^ r) 1)) u := by
  obtain ⟨pp, nbb, c, hpp, hc, hnbb, rfl⟩ := dcell_closed y hy
  obtain ⟨nb', ma', b', a', hb', ha', hnb', hma', hpe', -⟩ := up_decomp_closed pp hpp
  obtain ⟨cm, -, hcf⟩ := R.locOp_mM hT hG hL
  obtain ⟨hhol, -, -⟩ := hB d.m d.n e p q (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) X (abs_tw R w)
  obtain ⟨ρs, hρs, hss⟩ := strip_ball X
  set eb : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((R.sg w : ℤ) : ℂ) *
    Matrix.trace (b' * ((Matrix.of u)ᴴ * Matrix.of u))) with heb
  set w' : Fin d.m → Fin d.n → ℂ := fun i j => (Matrix.of u * a') i j with hw'
  have hform : ∀ f, IsSw f → L (pp * nbb) f u = eb * (cm a' * L nbb f w') := by
    intro f hf
    have h1 : IsSw (L nbb f) := (hL nbb f hf).1
    have h2 : IsSw (L ma' (L nbb f)) := (hL ma' _ h1).1
    rw [R.locOp_mul hT hG hL pp nbb f hf, hpe', R.locOp_mul hT hG hL nb' ma' _ h1,
      R.locOp_nU hT hG hL nb' b' hb' hnb' _ h2, hcf ma' a' ha' hma' _ h1]
    rfl
  have hreal : ∀ s : ℝ, |s| < ρs → Gf e p q (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) X (pp * nbb) s u =
      eb * (cm a' * Gf e p q (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) X nbb s w') := by
    intro s _
    rw [gf_L_fam R hT hG hFP hL hLD hsL hρ X a ha (pp * nbb) s, gf_L_fam R hT hG hFP hL hLD hsL hρ X a ha nbb s]
    exact hform _ (fam_sw R hT hG hFP hL X a ha s)
  have hid := iteratedDeriv_eq_of_real_closed
    (f := fun z => Gf e p q (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) X (pp * nbb) z u)
    (g := fun z => eb * (cm a' * Gf e p q (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) X nbb z w')) (ρ := ρs) hρs
    ((hhol _ u).mono hss) ((((hhol nbb w').mono hss).const_mul _).const_mul _) hreal r
  rw [hid, iteratedDeriv_const_mul', iteratedDeriv_const_mul']
  beta_reduce
  have hdn := congrFun (der_nbar R hT hA hG hFP hL hB hLD hsL hρ X a ha nbb c hc hnbb r) w'
  beta_reduce at hdn
  rw [hdn, hform _ (hFP _ _ _)]

theorem locFamG_of (hT : TAll) (hA : AuxiliaryPrimeFunction) (hG : GoodAwayEx) (hFP : FPSw) (hLI : LocInst) (hB : GfBound) : LocFamG := by
  intro F E _ _ _ _ _ σ d R w L hL X a ha
  obtain ⟨sL, ρ, p, q, e, -, hLD, hsL, hρ⟩ := hLI F E σ d R w L hL
  obtain ⟨hhol, hcont, hbd⟩ := hB d.m d.n e p q _ X (abs_tw R w)
  refine ⟨Gf e p q (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) X, fun y t => gf_L R hT hG hFP hL hLD hsL hρ X a ha y t, hhol,
    fun u => ?_, fun q' hq' => ?_, fun y hy r u => gf_der_big R hT hA hG hFP hL hB hLD hsL hρ X a ha y hy r u⟩
  · exact cont_slice2 _ _ hcont u _ fun q' hq' => ⟨Set.mem_univ _, hq'.2, Set.mem_univ _⟩
  · obtain ⟨N, δ, C, hN, hδ, hNb⟩ := hbd q'.1 q'.2 hq'.2
    refine ⟨N, hN, C, δ, hδ, fun q'' hq'' hs u => ?_⟩
    have h := hNb q'' hq'' hs u
    simpa [sq, neg_mul] using h

theorem gfBound : GfBound := fun m n e p q t X ht =>
  PositivityTheory.Rg.Sw.Glob.dBoundPQ m n (fun _ => true) t (2 * Real.pi) e p q X (by positivity) ht

theorem locFamG_of' (hT : TAll) (hA : AuxiliaryPrimeFunction) (hG : GoodAwayEx) (hFP : FPSw) (hLI : LocInst) : LocFamG :=
  locFamG_of hT hA hG hFP hLI gfBound

end PositivityTheory.SiegelWeilFormula.Kdil

end
