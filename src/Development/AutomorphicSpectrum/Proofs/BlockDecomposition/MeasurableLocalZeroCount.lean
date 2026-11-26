module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicLawOfBlockDet
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussianDetLeviIntegral

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RandomSectionZeroCount
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComplexHessianLogFubiniStudy
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComplexHessianLogFubiniStudy
noncomputable section

open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton Filter Topology
open scoped ENNReal ComplexConjugate

namespace GlobalTheory.CompanionTheory.FSCrofton

variable {n : ℕ}

theorem hessLog_chain {k : ℝ → ℝ} {v : V n → ℝ} {x : V n} (hv : ContDiffAt ℝ 2 v x)
    (hk : ContDiffAt ℝ 2 k (v x)) (j c : Fin n) :
    wd n j (wdb n c (fun y => ((k (v y) : ℝ) : ℂ))) x =
      ((deriv (deriv k) (v x) : ℝ) : ℂ) * wd n j (fun y => ((v y : ℝ) : ℂ)) x *
          conj (wd n c (fun y => ((v y : ℝ) : ℂ)) x) +
        ((deriv k (v x) : ℝ) : ℂ) * wd n j (wdb n c (fun y => ((v y : ℝ) : ℂ))) x := by
  have hv1 : DifferentiableAt ℝ v x := hv.differentiableAt (by simp)
  have hk1 : DifferentiableAt ℝ (deriv k) (v x) := differentiableAt_deriv_of_contDiffAt hk
  have hv' : ContDiffAt ℝ 2 (fun y => ((v y : ℝ) : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hv
  have hvd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ v y := eventually_differentiableAt_of_contDiffAt hv
  have hkd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ k (v y) :=
    hv1.continuousAt.tendsto.eventually (eventually_differentiableAt_of_contDiffAt hk)
  have hE : wdb n c (fun y => ((k (v y) : ℝ) : ℂ)) =ᶠ[𝓝 x]
      fun y => ((deriv k (v y) : ℝ) : ℂ) * wdb n c (fun y => ((v y : ℝ) : ℂ)) y := by
    filter_upwards [hvd, hkd] with y hy1 hy2
    exact wdb_ofReal_comp hy2 hy1
  have hD1 : DifferentiableAt ℝ (fun y => ((deriv k (v y) : ℝ) : ℂ)) x :=
    differentiableAt_ofReal (hk1.comp x hv1)
  rw [wd_congr n j _ _ x hE,
    wd_mul (f := fun y => ((deriv k (v y) : ℝ) : ℂ)) (g := wdb n c (fun y => ((v y : ℝ) : ℂ)))
      hD1 (differentiableAt_wdb hv'),
    wd_ofReal_comp hk1 hv1, wdb_ofReal hv1]

theorem hessLog_normSq {g : V n → ℂ} {x : V n} (hg : ContDiffAt ℂ 2 g x) (j c : Fin n) :
    wd n j (wdb n c (fun y => ((Complex.normSq (g y) : ℝ) : ℂ))) x =
      wd n j g x * conj (wd n c g x) := by
  have hgd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℂ g y :=
    (hg.eventually (by simp)).mono fun _ hy => hy.differentiableAt (by simp)
  have hgx : DifferentiableAt ℂ g x := hg.differentiableAt (by simp)
  have hf : (fun y => ((Complex.normSq (g y) : ℝ) : ℂ)) = fun y => g y * conj (g y) := by
    funext y; rw [Complex.mul_conj]
  have h1 : ContDiffAt ℂ 1 (fderiv ℂ g) x := hg.fderiv_right (by norm_num)
  have hh : DifferentiableAt ℂ (fun y => fderiv ℂ g y (bas n c)) x :=
    (h1.differentiableAt one_ne_zero).clm_apply (differentiableAt_const _)
  have hE : wdb n c (fun y => g y * conj (g y)) =ᶠ[𝓝 x]
      fun y => g y * conj (fderiv ℂ g y (bas n c)) := by
    filter_upwards [hgd] with y hy
    rw [wdb_mul (hy.restrictScalars ℝ) (differentiableAt_conj (hy.restrictScalars ℝ)),
      wdb_of_differentiableAt hy, wdb_conj (hy.restrictScalars ℝ), wd_of_differentiableAt hy]
    ring
  rw [hf, wd_congr n j _ _ x hE, wd_mul (f := g) (g := fun y => conj (fderiv ℂ g y (bas n c)))
    (hgx.restrictScalars ℝ) (differentiableAt_conj (hh.restrictScalars ℝ)),
    wd_conj (hh.restrictScalars ℝ), wdb_of_differentiableAt hh]
  simp [wd_of_differentiableAt hgx]

theorem cHess_log_one_add_sum : ∀ (d : ℕ) (β : Type) [Fintype β] (U : Set (V d)) (f : β → V d → ℂ),
    IsOpen U → (∀ j, DifferentiableOn ℂ (f j) U) → ∀ z ∈ U,
    cHess d (fun v => ((Real.log (1 + ∑ j, ‖f j v‖ ^ 2) : ℝ) : ℂ)) z =
      fsLevi (fun j => f j z) (Matrix.of fun j a => fderiv ℂ (f j) z (EuclideanSpace.single a 1)) := by
  intro d β _ U f hU hf z hz
  have hC : ∀ j, ContDiffAt ℂ 2 (f j) z := fun j =>
    ((contDiffOn_of_differentiableOn d (f j) U hU (hf j)).contDiffAt (hU.mem_nhds hz)).of_le
      ENat.LEInfty.out
  have hu : ∀ j, ContDiffAt ℝ 2 (fun y => Complex.normSq (f j y)) z := fun j =>
    H.contDiffAt_normSq_comp (hC j)
  have hu' : ∀ j, ContDiffAt ℝ 2 (fun y => ((Complex.normSq (f j y) : ℝ) : ℂ)) z := fun j =>
    Complex.ofRealCLM.contDiff.contDiffAt.comp z (hu j)
  have hnorm : ∀ v, (1 + ∑ j, ‖f j v‖ ^ 2 : ℝ) = 1 + ∑ j, Complex.normSq (f j v) := fun v => by
    simp only [Complex.normSq_eq_norm_sq]
  set S : V d → ℝ := fun y => 1 + ∑ j, Complex.normSq (f j y) with hSdef
  have hSpos : 0 < S z :=
    add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _)
  have hS : ContDiffAt ℝ 2 S z := contDiffAt_const.add (ContDiffAt.sum fun j _ => hu j)
  have hlog : ContDiffAt ℝ 2 Real.log (S z) := Real.contDiffAt_log.2 hSpos.ne'
  have hSc : (fun y => ((S y : ℝ) : ℂ)) =
      fun y => 1 + ∑ j, ((Complex.normSq (f j y) : ℝ) : ℂ) := by
    funext y; simp [hSdef]
  have hTd : ∀ {y}, (∀ j, DifferentiableAt ℝ (fun y => ((Complex.normSq (f j y) : ℝ) : ℂ)) y) →
      DifferentiableAt ℝ (fun y => ∑ j, ((Complex.normSq (f j y) : ℝ) : ℂ)) y := fun h =>
    DifferentiableAt.fun_sum fun j _ => h j
  have hwd : ∀ a, wd d a (fun y => ((S y : ℝ) : ℂ)) z =
      ∑ j, wd d a (f j) z * conj (f j z) := fun a => by
    have h1 : ∀ j, DifferentiableAt ℝ (fun y => ((Complex.normSq (f j y) : ℝ) : ℂ)) z := fun j =>
      (hu' j).differentiableAt (by simp)
    rw [hSc, wd_add (differentiableAt_const _) (hTd h1), wd_sum Finset.univ fun j _ => h1 j]
    simp only [fun j => H.wd_normSq_comp (j := a) (hC j)]
    simp [wd]
  have hhess : ∀ a c, wd d a (wdb d c (fun y => ((S y : ℝ) : ℂ))) z =
      ∑ j, wd d a (f j) z * conj (wd d c (f j) z) := fun a c => by
    have hev : wdb d c (fun y => ((S y : ℝ) : ℂ)) =ᶠ[𝓝 z]
        fun y => ∑ j, wdb d c (fun y => ((Complex.normSq (f j y) : ℝ) : ℂ)) y := by
      have : ∀ᶠ y in 𝓝 z, ∀ j,
          DifferentiableAt ℝ (fun y => ((Complex.normSq (f j y) : ℝ) : ℂ)) y := by
        rw [Filter.eventually_all]
        exact fun j => eventually_differentiableAt_of_contDiffAt (hu' j)
      filter_upwards [this] with y hy
      rw [hSc, wdb_add (differentiableAt_const _) (hTd hy), wdb_sum Finset.univ fun j _ => hy j]
      simp [wdb]
    rw [wd_congr d a _ _ z hev, wd_sum Finset.univ fun j _ => differentiableAt_wdb (hu' j)]
    exact Finset.sum_congr rfl fun j _ => hessLog_normSq (hC j) a c
  have hd1 : deriv Real.log (S z) = (S z)⁻¹ := by rw [Real.deriv_log']
  have hd2 : deriv (deriv Real.log) (S z) = -((S z) ^ 2)⁻¹ := by
    rw [Real.deriv_log']; exact deriv_inv
  have hS0 : ((S z : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hSpos.ne'
  ext a c
  have hfun : (fun v => ((Real.log (1 + ∑ j, ‖f j v‖ ^ 2) : ℝ) : ℂ)) =
      fun v => ((Real.log (S v) : ℝ) : ℂ) := by
    funext v; rw [hnorm]
  have hF : ∀ (j : β) (a : Fin d), fderiv ℂ (f j) z (EuclideanSpace.single a 1) = wd d a (f j) z :=
    fun j a => (wd_of_differentiableAt ((hC j).differentiableAt (by simp))).symm
  have hval : ((1 + ∑ j, ‖f j z‖ ^ 2 : ℝ) : ℂ) = ((S z : ℝ) : ℂ) := by rw [hnorm]
  simp only [cHess, fsLevi, Matrix.of_apply, hF, hfun, hval]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hessLog_chain hS hlog a c, hd1, hd2, hwd a, hwd c, hhess a c, map_sum]
  have hconj : ∑ j, conj (wd d c (f j) z * conj (f j z)) = ∑ j, f j z * conj (wd d c (f j) z) :=
    Finset.sum_congr rfl fun j _ => by rw [map_mul, Complex.conj_conj, mul_comm]
  rw [hconj]
  push_cast
  field_simp
  ring

end GlobalTheory.CompanionTheory.FSCrofton
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComplexHessianLogFubiniStudyStatement
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complex_hessian_log_fubini_study : ∀ (d : ℕ) (β : Type) [Fintype β] (U : Set (V d)) (f : β → V d → ℂ), IsOpen U → (∀ j, DifferentiableOn ℂ (f j) U) → ∀ z ∈ U, cHess d (fun v => ((Real.log (1 + ∑ j, ‖f j v‖ ^ 2) : ℝ) : ℂ)) z = fsLevi (fun j => f j z) (Matrix.of fun j a => fderiv ℂ (f j) z (EuclideanSpace.single a 1)) := by
  first | exact @GlobalTheory.CompanionTheory.FSCrofton.cHess_log_one_add_sum | exact GlobalTheory.CompanionTheory.FSCrofton.cHess_log_one_add_sum | (intros; apply GlobalTheory.CompanionTheory.FSCrofton.cHess_log_one_add_sum <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComplexHessianLogDehomogenise
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComplexHessianLogDehomogenise
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate ContDiff

namespace GlobalTheory.CompanionTheory.FSCrofton.HessFrame

private lemma contDiffOn_norm_sq_of_differentiableOn {d : ℕ} {U : Set (V d)} (hU : IsOpen U) {f : V d → ℂ}
    (hf : DifferentiableOn ℂ f U) : ContDiffOn ℝ ∞ (fun v => ‖f v‖ ^ 2) U :=
  (contDiff_norm_sq ℝ).comp_contDiffOn
    ((ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn d f U hU hf).restrict_scalars ℝ)

theorem cHess_log_sum_normSq_eq (d : ℕ) (α : Type) [Fintype α] [DecidableEq α] (j₀ : α)
    (U : Set (V d)) (b : α → V d → ℂ) (hU : IsOpen U) (hb : ∀ j, DifferentiableOn ℂ (b j) U)
    (h0 : ∀ z ∈ U, b j₀ z ≠ 0) : ∀ z ∈ U,
    cHess d (fun v => ((Real.log (∑ j, ‖b j v‖ ^ 2) : ℝ) : ℂ)) z =
      cHess d (fun v => ((Real.log (1 + ∑ j : {j : α // j ≠ j₀}, ‖b j.1 v / b j₀ v‖ ^ 2) : ℝ) : ℂ))
        z := by
  intro z hz
  obtain ⟨R, hRdef⟩ : ∃ R : V d → ℝ,
      R = fun v => 1 + ∑ j : {j : α // j ≠ j₀}, ‖b j.1 v / b j₀ v‖ ^ 2 := ⟨_, rfl⟩
  have hpos : ∀ v ∈ U, 0 < ‖b j₀ v‖ ^ 2 := fun v hv => pow_pos (norm_pos_iff.2 (h0 v hv)) 2
  have hRpos : ∀ v, 0 < R v := fun v => by rw [hRdef]; positivity
  have hp : ContDiffOn ℝ ∞ (fun v => Real.log (‖b j₀ v‖ ^ 2)) U :=
    (contDiffOn_norm_sq_of_differentiableOn hU (hb j₀)).log fun v hv => (hpos v hv).ne'
  have hq : ContDiffOn ℝ ∞ (fun v => Real.log (R v)) U := by
    refine ContDiffOn.log ?_ fun v _ => (hRpos v).ne'
    rw [hRdef]
    exact contDiffOn_const.add
      (ContDiffOn.sum fun j _ => contDiffOn_norm_sq_of_differentiableOn hU (by
        simpa only [div_eq_mul_inv] using (hb j.1).fun_mul ((hb j₀).fun_inv h0)))
  have hsplit : ∀ v ∈ U, ∑ j, ‖b j v‖ ^ 2 = ‖b j₀ v‖ ^ 2 * R v := by
    intro v hv
    have hn : ‖b j₀ v‖ ^ 2 ≠ 0 := (hpos v hv).ne'
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j₀),
      Finset.sum_subtype (F := inferInstance) (Finset.univ.erase j₀) (p := fun j => j ≠ j₀) (by simp),
      hRdef]
    simp only [mul_add, mul_one, Finset.mul_sum, norm_div, div_pow, mul_div_cancel₀ _ hn]
  have hev : (fun v => ((Real.log (∑ j, ‖b j v‖ ^ 2) : ℝ) : ℂ)) =ᶠ[nhds z]
      fun v => ((Real.log (‖b j₀ v‖ ^ 2) + 1 * Real.log (R v) : ℝ) : ℂ) := by
    refine Filter.eventually_of_mem (hU.mem_nhds hz) fun v hv => ?_
    simp only
    rw [hsplit v hv, Real.log_mul (hpos v hv).ne' (hRpos v).ne', one_mul]
  have hzero : cHess d (fun w => ((Real.log (‖b j₀ w‖ ^ 2) : ℝ) : ℂ)) z = 0 := by
    ext j k
    simp only [cHess, Matrix.of_apply, Matrix.zero_apply]
    exact ReciprocityTheory.L2DbarEstimates.Y.cmpa_hess_log hU hz (hb j₀) h0 j k
  rw [ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr hev,
    ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.cHess_add_smul hU hp hq 1 hz, hzero, zero_add, Complex.ofReal_one,
    one_smul, hRdef]

end GlobalTheory.CompanionTheory.FSCrofton.HessFrame
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComplexHessianLogDehomogeniseStatement
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complex_hessian_log_dehomogenise : ∀ (d : ℕ) (α : Type) [Fintype α] [DecidableEq α] (j₀ : α) (U : Set (V d)) (b : α → V d → ℂ), IsOpen U → (∀ j, DifferentiableOn ℂ (b j) U) → (∀ z ∈ U, b j₀ z ≠ 0) → ∀ z ∈ U, cHess d (fun v => ((Real.log (∑ j, ‖b j v‖ ^ 2) : ℝ) : ℂ)) z = cHess d (fun v => ((Real.log (1 + ∑ j : {j : α // j ≠ j₀}, ‖b j.1 v / b j₀ v‖ ^ 2) : ℝ) : ℂ)) z := by
  first | exact @GlobalTheory.CompanionTheory.FSCrofton.HessFrame.cHess_log_sum_normSq_eq | exact GlobalTheory.CompanionTheory.FSCrofton.HessFrame.cHess_log_sum_normSq_eq | (intros; apply GlobalTheory.CompanionTheory.FSCrofton.HessFrame.cHess_log_sum_normSq_eq <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChangeVariablesZeroCount
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChangeVariablesZeroCount
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate

noncomputable section

namespace GlobalTheory.CompanionTheory.FSCrofton

theorem clm_apply_eq_sum {d : ℕ} (T : V d →L[ℂ] ℂ) (v : V d) :
    T v = ∑ a, v a * T (EuclideanSpace.single a 1) := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin d) ℂ).sum_repr v]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum]

theorem abs_det_restrictScalars_toEuclideanCLM {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ) :
    |((Matrix.toEuclideanCLM (𝕜 := ℂ) M : V d →L[ℂ] V d).restrictScalars ℝ).det| =
      ‖M.det‖ ^ 2 := by
  have h1 : ((Matrix.toEuclideanCLM (𝕜 := ℂ) M : V d →L[ℂ] V d).restrictScalars ℝ).det =
      Algebra.norm ℝ (LinearMap.det (Matrix.toEuclideanLin M : V d →ₗ[ℂ] V d)) := by
    rw [← LinearMap.det_restrictScalars]
    rfl
  rw [h1, Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.det_toLin, Algebra.norm_complex_eq]
  simp [Complex.normSq_eq_norm_sq]

theorem area_formula_neg_comb (d : ℕ) (β : Type) [Fintype β] (U A : Set (V d)) (f : β → V d → ℂ)
    (C : Fin d → β → ℂ) (h : (Fin d → ℂ) → ℝ≥0∞) (hU : IsOpen U)
    (hf : ∀ j, DifferentiableOn ℂ (f j) U) (hAU : A ⊆ U) (hA : MeasurableSet A)
    (hh : Measurable h) :
    ∫⁻ c : Fin d → ℂ, h c * (({z ∈ A | ∀ k, c k + ∑ j, C k j * f j z = 0}.encard : ℕ∞) : ℝ≥0∞) =
      ∫⁻ z in A, h (fun k => -∑ j, C k j * f j z) *
        ENNReal.ofReal (‖(Matrix.of C * (Matrix.of fun j a =>
          fderiv ℂ (f j) z (EuclideanSpace.single a 1) : Matrix β (Fin d) ℂ)).det‖ ^ 2) := by
  classical
  let F : V d → Matrix β (Fin d) ℂ := fun z =>
    Matrix.of fun j a => fderiv ℂ (f j) z (EuclideanSpace.single a 1)
  let M : V d → Matrix (Fin d) (Fin d) ℂ := fun z => -(Matrix.of C * F z)
  let g : V d → V d := fun z => WithLp.toLp 2 (fun k => -∑ j, C k j * f j z)
  let L : V d → V d →L[ℂ] V d := fun z => Matrix.toEuclideanCLM (𝕜 := ℂ) (M z)
  let f' : V d → V d →L[ℝ] V d := fun z => (L z).restrictScalars ℝ
  have hderC : ∀ z ∈ A, HasFDerivWithinAt g (L z) A z := by
    intro z hz
    rw [hasFDerivWithinAt_euclidean]
    intro k
    have hj : ∀ j, HasFDerivAt (f j) (fderiv ℂ (f j) z) z := fun j =>
      ((hf j).differentiableAt (hU.mem_nhds (hAU hz))).hasFDerivAt
    have hs : HasFDerivAt (fun w => -∑ j, C k j * f j w)
        (-∑ j, C k j • fderiv ℂ (f j) z) z :=
      (HasFDerivAt.fun_sum fun j _ => (hj j).const_mul (C k j)).neg
    have he : PiLp.proj 2 (fun _ : Fin d => ℂ) k ∘L L z = -∑ j, C k j • fderiv ℂ (f j) z := by
      ext v
      have hv : ∀ j, fderiv ℂ (f j) z v = ∑ a, v a * F z j a := fun j => clm_apply_eq_sum _ v
      change ((Matrix.toEuclideanCLM (𝕜 := ℂ) (M z)) v).ofLp k = _
      rw [Matrix.ofLp_toEuclideanCLM]
      simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.sum_apply,
        ContinuousLinearMap.smul_apply, smul_eq_mul, hv]
      simp only [M, Matrix.mulVec, dotProduct, Matrix.neg_apply, Matrix.mul_apply, Matrix.of_apply,
        neg_mul, Finset.sum_neg_distrib, neg_inj]
      simp_rw [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [he]
    exact hs.hasFDerivWithinAt
  have hder : ∀ z ∈ A, HasFDerivWithinAt g (f' z) A z := fun z hz =>
    (hderC z hz).restrictScalars ℝ
  have hdet : ∀ z, |(f' z).det| = ‖(Matrix.of C * F z).det‖ ^ 2 := by
    intro z
    have := abs_det_restrictScalars_toEuclideanCLM (M z)
    rw [show (M z).det = (-1) ^ Fintype.card (Fin d) * (Matrix.of C * F z).det from
      Matrix.det_neg _] at this
    simpa using this
  have hp : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin d → ℂ))
      (volume : Measure (Fin d → ℂ)) (volume : Measure (V d)) :=
    MeasurePreserving.symm (MeasurableEquiv.toLp 2 (Fin d → ℂ)).symm
      (GlobalTheory.volume_preserving_ofLp_complex (Fin d))
  have hw := (GroundTheory.Heights₂.Heights.AreaMultiplicityWeight.proof (V d) volume A g f' hA hder).2
    (fun y => h y.ofLp) (hh.comp (MeasurableEquiv.toLp 2 (Fin d → ℂ)).symm.measurable)
  have hfib : ∀ c : Fin d → ℂ, {z ∈ A | ∀ k, c k + ∑ j, C k j * f j z = 0} =
      {z ∈ A | g z = WithLp.toLp 2 c} := by
    intro c
    ext z
    simp only [Set.mem_setOf_eq, g]
    refine and_congr_right fun _ => ?_
    rw [(WithLp.toLp_injective 2).eq_iff, funext_iff]
    refine forall_congr' fun k => ?_
    rw [neg_eq_iff_add_eq_zero, add_comm]
  calc ∫⁻ c : Fin d → ℂ, h c * (({z ∈ A | ∀ k, c k + ∑ j, C k j * f j z = 0}.encard : ℕ∞) : ℝ≥0∞)
      = ∫⁻ c : Fin d → ℂ, (fun y : V d => (({z ∈ A | g z = y}.encard : ℕ∞) : ℝ≥0∞) * h y.ofLp)
          (MeasurableEquiv.toLp 2 (Fin d → ℂ) c) := by
        refine lintegral_congr fun c => ?_
        rw [hfib c, mul_comm]
        rfl
    _ = ∫⁻ y : V d, (({z ∈ A | g z = y}.encard : ℕ∞) : ℝ≥0∞) * h y.ofLp :=
        hp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)
          (fun y : V d => (({z ∈ A | g z = y}.encard : ℕ∞) : ℝ≥0∞) * h y.ofLp)
    _ = ∫⁻ z in A, h (g z).ofLp * ENNReal.ofReal |(f' z).det| := hw.symm
    _ = _ := by
        refine lintegral_congr fun z => ?_
        rw [hdet z]

end GlobalTheory.CompanionTheory.FSCrofton
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChangeVariablesZeroCountStatement
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.change_variables_zero_count : ∀ (d : ℕ) (β : Type) [Fintype β] (U A : Set (V d)) (f : β → V d → ℂ) (C : Fin d → β → ℂ) (h : (Fin d → ℂ) → ℝ≥0∞), IsOpen U → (∀ j, DifferentiableOn ℂ (f j) U) → A ⊆ U → MeasurableSet A → Measurable h → ∫⁻ c : Fin d → ℂ, h c * (({z ∈ A | ∀ k, c k + ∑ j, C k j * f j z = 0}.encard : ℕ∞) : ℝ≥0∞) = ∫⁻ z in A, h (fun k => -∑ j, C k j * f j z) * ENNReal.ofReal (‖(Matrix.of C * (Matrix.of fun j a => fderiv ℂ (f j) z (EuclideanSpace.single a 1) : Matrix β (Fin d) ℂ)).det‖ ^ 2) := by
  first | exact @GlobalTheory.CompanionTheory.FSCrofton.area_formula_neg_comb | exact GlobalTheory.CompanionTheory.FSCrofton.area_formula_neg_comb | (intros; apply GlobalTheory.CompanionTheory.FSCrofton.area_formula_neg_comb <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralSplitColumn
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralSplitColumn
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate

namespace GlobalTheory.CompanionTheory.FSCrofton

theorem measurePreserving_funUnique_symm {U : Type} [inst : Fintype U] [Unique U] :
    MeasurePreserving (MeasurableEquiv.funUnique U ℂ).symm (volume : Measure ℂ)
      (Measure.pi fun _ : U => (volume : Measure ℂ)) := by
  obtain rfl : inst = Unique.fintype := Subsingleton.elim _ _
  exact (measurePreserving_funUnique (volume : Measure ℂ) U).symm

theorem measurePreserving_joinEntry {α : Type} [Fintype α] [DecidableEq α] (j₀ : α) :
    MeasurePreserving
      (fun p : ℂ × ({j : α // j ≠ j₀} → ℂ) =>
        (fun j => if h : j = j₀ then p.1 else p.2 ⟨j, h⟩ : α → ℂ))
      ((volume : Measure ℂ).prod (Measure.pi fun _ : {j : α // j ≠ j₀} => (volume : Measure ℂ)))
      (Measure.pi fun _ : α => (volume : Measure ℂ)) := by
  haveI : Unique {j : α // ¬ j ≠ j₀} :=
    { default := ⟨j₀, by simp⟩
      uniq := fun x => Subtype.ext (by simpa using x.2) }
  have h1 := (measurePreserving_piEquivPiSubtypeProd (fun _ : α => (volume : Measure ℂ))
    (fun j => j ≠ j₀)).symm
  have h2 : MeasurePreserving (MeasurableEquiv.funUnique {j : α // ¬ j ≠ j₀} ℂ).symm
      (volume : Measure ℂ) (Measure.pi fun _ : {j : α // ¬ j ≠ j₀} => (volume : Measure ℂ)) :=
    measurePreserving_funUnique_symm
  have h3 := (MeasurePreserving.id
    (Measure.pi fun _ : {j : α // j ≠ j₀} => (volume : Measure ℂ))).prod h2
  have h4 : MeasurePreserving (Prod.swap : ℂ × ({j : α // j ≠ j₀} → ℂ) → _)
      ((volume : Measure ℂ).prod (Measure.pi fun _ : {j : α // j ≠ j₀} => (volume : Measure ℂ)))
      ((Measure.pi fun _ : {j : α // j ≠ j₀} => (volume : Measure ℂ)).prod (volume : Measure ℂ)) :=
    Measure.measurePreserving_swap
  have h5 := h1.comp (h3.comp h4)
  convert h5 using 1
  funext p j
  by_cases h : j = j₀
  · subst h
    simp [MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd]
  · simp [MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, h]

theorem measurePreserving_joinCol (d : ℕ) {α : Type} [Fintype α] [DecidableEq α] (j₀ : α) :
    MeasurePreserving
      (fun p : (Fin d → ℂ) × (Fin d → {j : α // j ≠ j₀} → ℂ) => joinCol j₀ p.1 p.2)
      volume volume := by
  have h1 := (volume_measurePreserving_arrowProdEquivProdArrow ℂ ({j : α // j ≠ j₀} → ℂ) (Fin d)).symm
  have h2 := measurePreserving_pi (fun _ : Fin d => (volume : Measure (ℂ × ({j : α // j ≠ j₀} → ℂ))))
    (fun _ : Fin d => (volume : Measure (α → ℂ))) (fun _ => measurePreserving_joinEntry j₀)
  exact h2.comp h1

theorem lintegral_joinCol : ∀ (d : ℕ) (α : Type) [Fintype α] [DecidableEq α] (j₀ : α) (Φ : (Fin d → α → ℂ) → ℝ≥0∞), Measurable Φ → ∫⁻ C : Fin d → α → ℂ, Φ C = ∫⁻ C' : Fin d → {j : α // j ≠ j₀} → ℂ, ∫⁻ c : Fin d → ℂ, Φ (joinCol j₀ c C') := by
  intro d α _ _ j₀ Φ hΦ
  have hT := measurePreserving_joinCol d j₀
  rw [← hT.lintegral_comp hΦ]
  exact lintegral_prod_symm _ (hΦ.comp hT.measurable).aemeasurable

end GlobalTheory.CompanionTheory.FSCrofton
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralSplitColumnStatement
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_split_column : ∀ (d : ℕ) (α : Type) [Fintype α] [DecidableEq α] (j₀ : α) (Φ : (Fin d → α → ℂ) → ℝ≥0∞), Measurable Φ → ∫⁻ C : Fin d → α → ℂ, Φ C = ∫⁻ C' : Fin d → {j : α // j ≠ j₀} → ℂ, ∫⁻ c : Fin d → ℂ, Φ (joinCol j₀ c C') := by
  first | exact @GlobalTheory.CompanionTheory.FSCrofton.lintegral_joinCol | exact GlobalTheory.CompanionTheory.FSCrofton.lintegral_joinCol | (intros; apply GlobalTheory.CompanionTheory.FSCrofton.lintegral_joinCol <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RandomSectionZeroCount
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate

noncomputable section

namespace GlobalTheory.CompanionTheory.FSCrofton.LocalCrofton

theorem measurable_gW (d : ℕ) (α : Type) [Fintype α] : Measurable (gW d α) := by
  have hc : Continuous fun C : Fin d → α → ℂ => Real.exp (-∑ k, ∑ j, ‖C k j‖ ^ 2) := by
    fun_prop
  exact ENNReal.measurable_ofReal.comp hc.measurable

theorem gW_ne_top (d : ℕ) (α : Type) [Fintype α] (C : Fin d → α → ℂ) : gW d α C ≠ ∞ :=
  ENNReal.ofReal_ne_top

theorem measurable_gauss (d : ℕ) :
    Measurable fun c : Fin d → ℂ => ENNReal.ofReal (Real.exp (-∑ k, ‖c k‖ ^ 2)) := by
  have hc : Continuous fun c : Fin d → ℂ => Real.exp (-∑ k, ‖c k‖ ^ 2) := by
    fun_prop
  exact ENNReal.measurable_ofReal.comp hc.measurable

theorem gW_joinCol {d : ℕ} {α : Type} [Fintype α] [DecidableEq α] (j₀ : α) (c : Fin d → ℂ)
    (C : Fin d → {j : α // j ≠ j₀} → ℂ) :
    gW d α (joinCol j₀ c C) =
      gW d {j : α // j ≠ j₀} C * ENNReal.ofReal (Real.exp (-∑ k, ‖c k‖ ^ 2)) := by
  unfold gW
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  rw [← neg_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Fintype.sum_eq_add_sum_subtype_ne _ j₀, add_comm]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    simp [joinCol, j.2]
  · simp [joinCol]

theorem joinCol_zero_iff {X : Type} {d : ℕ} {α : Type} [Fintype α] [DecidableEq α] (j₀ : α)
    (c : Fin d → ℂ) (C : Fin d → {j : α // j ≠ j₀} → ℂ) (b : α → X → ℂ) (z : X)
    (hz : b j₀ z ≠ 0) :
    (∀ k, ∑ j, joinCol j₀ c C k j * b j z = 0) ↔
      ∀ k, c k + ∑ j : {j : α // j ≠ j₀}, C k j * (b j.1 z / b j₀ z) = 0 := by
  refine forall_congr' fun k => ?_
  have h : ∑ j, joinCol j₀ c C k j * b j z =
      b j₀ z * (c k + ∑ j : {j : α // j ≠ j₀}, C k j * (b j.1 z / b j₀ z)) := by
    rw [Fintype.sum_eq_add_sum_subtype_ne _ j₀, mul_add, Finset.mul_sum]
    congr 1
    · simp [joinCol, mul_comm]
    · refine Finset.sum_congr rfl fun j _ => ?_
      simp only [joinCol, j.2, dite_false]
      field_simp
  rw [h, mul_eq_zero]
  simp [hz]

theorem continuous_kernel (d : ℕ) (β : Type) [Fintype β] :
    Continuous fun q : (Fin d → β → ℂ) × ((β → ℂ) × (β → Fin d → ℂ)) =>
      Real.exp (-∑ k, ‖∑ j, q.1 k j * q.2.1 j‖ ^ 2) *
        ‖(Matrix.of q.1 * (Matrix.of q.2.2 : Matrix β (Fin d) ℂ)).det‖ ^ 2 := by
  have h1 : Continuous fun q : (Fin d → β → ℂ) × ((β → ℂ) × (β → Fin d → ℂ)) =>
      (Matrix.of q.1 : Matrix (Fin d) β ℂ) := continuous_fst
  have h2 : Continuous fun q : (Fin d → β → ℂ) × ((β → ℂ) × (β → Fin d → ℂ)) =>
      (Matrix.of q.2.2 : Matrix β (Fin d) ℂ) := continuous_snd.comp continuous_snd
  have h3 : Continuous fun q : (Fin d → β → ℂ) × ((β → ℂ) × (β → Fin d → ℂ)) =>
      (Matrix.of q.1 * (Matrix.of q.2.2 : Matrix β (Fin d) ℂ)).det :=
    (h1.matrix_mul h2).matrix_det
  have h4 : Continuous fun q : (Fin d → β → ℂ) × ((β → ℂ) × (β → Fin d → ℂ)) =>
      Real.exp (-∑ k, ‖∑ j, q.1 k j * q.2.1 j‖ ^ 2) := by
    refine Real.continuous_exp.comp (continuous_neg.comp ?_)
    refine continuous_finsetSum _ fun k _ => (Continuous.norm ?_).pow 2
    refine continuous_finsetSum _ fun j _ => Continuous.mul ?_ ?_
    · exact (continuous_apply j).comp ((continuous_apply k).comp continuous_fst)
    · exact (continuous_apply j).comp (continuous_fst.comp continuous_snd)
  exact h4.mul (h3.norm.pow 2)

theorem measurable_kernel {X : Type} [MeasurableSpace X] (d : ℕ) (β : Type) [Fintype β]
    (g : β → X → ℂ) (F : β → Fin d → X → ℂ) (hg : ∀ j, Measurable (g j))
    (hF : ∀ j a, Measurable (F j a)) :
    Measurable fun p : (Fin d → β → ℂ) × X =>
      gW d β p.1 * ENNReal.ofReal (Real.exp (-∑ k, ‖∑ j, p.1 k j * g j p.2‖ ^ 2) *
        ‖(Matrix.of p.1 * (Matrix.of fun j a => F j a p.2 : Matrix β (Fin d) ℂ)).det‖ ^ 2) := by
  have hm : Measurable fun p : (Fin d → β → ℂ) × X =>
      ((p.1, (fun j => g j p.2), (fun j a => F j a p.2)) :
        (Fin d → β → ℂ) × ((β → ℂ) × (β → Fin d → ℂ))) := by
    refine measurable_fst.prodMk (Measurable.prodMk ?_ ?_)
    · exact Measurable.of_eval fun j => (hg j).comp measurable_snd
    · exact Measurable.of_eval fun j => Measurable.of_eval fun a =>
        (hF j a).comp measurable_snd
  have hq := (continuous_kernel d β).measurable.comp hm
  exact ((measurable_gW d β).comp measurable_fst).mul (ENNReal.measurable_ofReal.comp hq)

theorem differentiableOn_quot {d : ℕ} {α : Type} (U : Set (V d)) (b : α → V d → ℂ)
    (hb : ∀ j, DifferentiableOn ℂ (b j) U) (j₀ : α) (hne : ∀ z ∈ U, b j₀ z ≠ 0) (j : α) :
    DifferentiableOn ℂ (fun v => b j v / b j₀ v) U := by
  have h : DifferentiableOn ℂ (fun v => b j v * (b j₀ v)⁻¹) U := (hb j).mul ((hb j₀).inv hne)
  simpa only [div_eq_mul_inv] using h

theorem inner_integral (d : ℕ) (α : Type) [Fintype α] [DecidableEq α] (j₀ : α) (U A : Set (V d))
    (b : α → V d → ℂ) (hU : IsOpen U) (hb : ∀ j, DifferentiableOn ℂ (b j) U)
    (hne : ∀ z ∈ U, b j₀ z ≠ 0) (hAU : A ⊆ U) (hAm : MeasurableSet A)
    (g : {j : α // j ≠ j₀} → V d → ℂ) (hgA : ∀ j, ∀ z ∈ A, g j z = b j.1 z / b j₀ z)
    (C : Fin d → {j : α // j ≠ j₀} → ℂ) :
    ∫⁻ c : Fin d → ℂ, gW d α (joinCol j₀ c C) * zeroCnt d A b (joinCol j₀ c C) =
      ∫⁻ z in A, gW d {j : α // j ≠ j₀} C *
        ENNReal.ofReal (Real.exp (-∑ k, ‖∑ j, C k j * g j z‖ ^ 2) *
          ‖(Matrix.of C * (Matrix.of fun j a =>
            fderiv ℂ (fun v => b (j : {j : α // j ≠ j₀}).1 v / b j₀ v) z
              (EuclideanSpace.single a 1) : Matrix {j : α // j ≠ j₀} (Fin d) ℂ)).det‖ ^ 2) := by
  have hf : ∀ j : {j : α // j ≠ j₀}, DifferentiableOn ℂ (fun v => b j.1 v / b j₀ v) U :=
    fun j => differentiableOn_quot U b hb j₀ hne j.1
  have e1 : ∀ c : Fin d → ℂ, gW d α (joinCol j₀ c C) * zeroCnt d A b (joinCol j₀ c C) =
      gW d {j : α // j ≠ j₀} C * (ENNReal.ofReal (Real.exp (-∑ k, ‖c k‖ ^ 2)) *
        (({z ∈ A | ∀ k, c k + ∑ j : {j : α // j ≠ j₀}, C k j * (b j.1 z / b j₀ z) = 0}.encard :
          ℕ∞) : ℝ≥0∞)) := by
    intro c
    have hs : {z ∈ A | ∀ k, ∑ j, joinCol j₀ c C k j * b j z = 0} =
        {z ∈ A | ∀ k, c k + ∑ j : {j : α // j ≠ j₀}, C k j * (b j.1 z / b j₀ z) = 0} := by
      ext z
      simp only [Set.mem_setOf_eq]
      refine and_congr_right fun hz => ?_
      exact joinCol_zero_iff j₀ c C b z (hne z (hAU hz))
    rw [gW_joinCol, mul_assoc]
    unfold zeroCnt
    rw [hs]
  simp_rw [e1]
  rw [lintegral_const_mul' _ _ (gW_ne_top d _ C),
    GlobalTheory.T.change_variables_zero_count d {j : α // j ≠ j₀} U A (fun j v => b j.1 v / b j₀ v) C
      (fun c => ENNReal.ofReal (Real.exp (-∑ k, ‖c k‖ ^ 2))) hU hf hAU hAm (measurable_gauss d),
    ← lintegral_const_mul' _ _ (gW_ne_top d _ C)]
  refine setLIntegral_congr_fun hAm fun z hz => ?_
  simp only [norm_neg]
  rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
  simp only [hgA _ z hz]

theorem const_arith (d m n : ℕ) (hn : n = m + 1) (x : ℝ) :
    ENNReal.ofReal (Real.pi ^ (d * m) * (d.factorial : ℝ) * x) =
      ENNReal.ofReal (Real.pi ^ (d * n)) *
        ENNReal.ofReal ((d.factorial : ℝ) / Real.pi ^ d * x) := by
  rw [← ENNReal.ofReal_mul (pow_nonneg Real.pi_pos.le _)]
  congr 1
  subst hn
  have hp : (Real.pi ^ d) ≠ 0 := pow_ne_zero _ Real.pi_pos.ne'
  rw [Nat.mul_succ, pow_add]
  field_simp

theorem crofton_local : ∀ (d : ℕ) (α : Type) [Fintype α] [DecidableEq α] (j₀ : α) (U A : Set (V d)) (b : α → V d → ℂ), IsOpen U → (∀ j, DifferentiableOn ℂ (b j) U) → (∀ z ∈ U, b j₀ z ≠ 0) → A ⊆ U → IsSigmaCompact A → ∫⁻ C : Fin d → α → ℂ, gW d α C * zeroCnt d A b C = ENNReal.ofReal (Real.pi ^ (d * Fintype.card α)) * ∫⁻ z in A, ENNReal.ofReal ((d.factorial : ℝ) / Real.pi ^ d * (cHess d (fun v => ((Real.log (∑ j, ‖b j v‖ ^ 2) : ℝ) : ℂ)) z).det.re) := by
  intro d α _ _ j₀ U A b hU hb hne hAU hA
  classical
  have hAm : MeasurableSet A := by
    obtain ⟨K, hK, hKA⟩ := hA
    rw [← hKA]
    exact MeasurableSet.iUnion fun n => (hK n).measurableSet
  have hΦ : Measurable fun C : Fin d → α → ℂ => gW d α C * zeroCnt d A b C :=
    (measurable_gW d α).mul (GlobalTheory.T.measurable_zero_count d α U A b (fun j => (hb j).continuousOn) hAU hA)
  have hf : ∀ j : {j : α // j ≠ j₀}, DifferentiableOn ℂ (fun v => b j.1 v / b j₀ v) U :=
    fun j => differentiableOn_quot U b hb j₀ hne j.1
  obtain ⟨g, hg, hgA⟩ : ∃ g : {j : α // j ≠ j₀} → V d → ℂ, (∀ j, Measurable (g j)) ∧
      ∀ j, ∀ z ∈ A, g j z = b j.1 z / b j₀ z := by
    refine ⟨fun j => U.piecewise (fun v => b j.1 v / b j₀ v) (fun _ => 0), fun j => ?_,
      fun j z hz => by simp [Set.piecewise, hAU hz]⟩
    exact (hf j).continuousOn.measurable_piecewise continuousOn_const hU.measurableSet
  have hF : ∀ (j : {j : α // j ≠ j₀}) (a : Fin d), Measurable fun z =>
      fderiv ℂ (fun v => b j.1 v / b j₀ v) z (EuclideanSpace.single a 1) :=
    fun j a => measurable_fderiv_apply_const ℂ _ _
  have hK := measurable_kernel d {j : α // j ≠ j₀} g _ hg hF
  rw [GlobalTheory.T.lintegral_split_column d α j₀ _ hΦ]
  simp_rw [inner_integral d α j₀ U A b hU hb hne hAU hAm g hgA]
  rw [lintegral_lintegral_swap (ν := volume.restrict A) hK.aemeasurable,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun hAm fun z hz => ?_
  have hcard : Fintype.card α = Fintype.card {j : α // j ≠ j₀} + 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
    have : 0 < Fintype.card α := Fintype.card_pos_iff.mpr ⟨j₀⟩
    omega
  have h1 := GlobalTheory.T.gaussian_det_levi_integral d {j : α // j ≠ j₀} (fun j => b j.1 z / b j₀ z)
    (Matrix.of fun j a => fderiv ℂ (fun v => b (j : {j : α // j ≠ j₀}).1 v / b j₀ v) z
      (EuclideanSpace.single a 1))
  rw [GlobalTheory.T.complex_hessian_log_dehomogenise d α j₀ U b hU hb hne z (hAU hz),
    GlobalTheory.T.complex_hessian_log_fubini_study d {j : α // j ≠ j₀} U (fun j v => b j.1 v / b j₀ v) hU hf z (hAU hz),
    ← const_arith d _ _ hcard, ← h1]
  simp only [hgA _ z hz]

end GlobalTheory.CompanionTheory.FSCrofton.LocalCrofton
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RandomSectionZeroCountStatement
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.random_section_zero_count : ∀ (d : ℕ) (α : Type) [Fintype α] [DecidableEq α] (j₀ : α) (U A : Set (V d)) (b : α → V d → ℂ), IsOpen U → (∀ j, DifferentiableOn ℂ (b j) U) → (∀ z ∈ U, b j₀ z ≠ 0) → A ⊆ U → IsSigmaCompact A → ∫⁻ C : Fin d → α → ℂ, gW d α C * zeroCnt d A b C = ENNReal.ofReal (Real.pi ^ (d * Fintype.card α)) * ∫⁻ z in A, ENNReal.ofReal ((d.factorial : ℝ) / Real.pi ^ d * (cHess d (fun v => ((Real.log (∑ j, ‖b j v‖ ^ 2) : ℝ) : ℂ)) z).det.re) := by
  first | exact @GlobalTheory.CompanionTheory.FSCrofton.LocalCrofton.crofton_local | exact GlobalTheory.CompanionTheory.FSCrofton.LocalCrofton.crofton_local | (intros; apply GlobalTheory.CompanionTheory.FSCrofton.LocalCrofton.crofton_local <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableLocalZeroCount
open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.FSCrofton.Chart

theorem measurableSet_of_isSigmaCompact {X : Type*} [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [OpensMeasurableSpace X] {A : Set X} (hA : IsSigmaCompact A) :
    MeasurableSet A := by
  obtain ⟨K, hK, rfl⟩ := hA
  exact MeasurableSet.iUnion fun n => (hK n).measurableSet

variable {Y : Var ℂ} {L : LB Y.X}

noncomputable def chartVal {n : ℕ} (b : Fin n → L.Sec) (c : AlgChart Y.str (RingHom.id ℂ) Y.dim)
    (i : L.ι) (j : Fin n) (v : ReciprocityTheory.L2DbarEstimates.V Y.dim) : ℂ :=
  secVal Y.str (RingHom.id ℂ) (b j) i (c.e.symm v)

theorem encard_eq_zeroCnt {n : ℕ} (b : Fin n → L.Sec) (c : AlgChart Y.str (RingHom.id ℂ) Y.dim)
    (i : L.ι) (A : Set (CxPts Y.str (RingHom.id ℂ))) (hAc : A ⊆ c.e.source)
    (hAi : A ⊆ ptsIn Y.str (RingHom.id ℂ) (L.U i)) (C : Fin Y.dim → Fin n → ℂ) :
    (({y : CxPts Y.str (RingHom.id ℂ) | y ∈ A ∧ ∀ (k : Fin Y.dim) (i' : L.ι),
        y ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i') →
        ∑ j, C k j * secVal Y.str (RingHom.id ℂ) (b j) i' y = 0}.encard : ℕ∞) : ℝ≥0∞) =
      zeroCnt Y.dim (c.e '' A) (chartVal b c i) C := by
  have hinj : Set.InjOn c.e {y : CxPts Y.str (RingHom.id ℂ) | y ∈ A ∧ ∀ (k : Fin Y.dim) (i' : L.ι),
        y ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i') →
        ∑ j, C k j * secVal Y.str (RingHom.id ℂ) (b j) i' y = 0} :=
    c.e.injOn.mono fun y hy => hAc hy.1
  have himg : c.e '' {y : CxPts Y.str (RingHom.id ℂ) | y ∈ A ∧ ∀ (k : Fin Y.dim) (i' : L.ι),
        y ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i') →
        ∑ j, C k j * secVal Y.str (RingHom.id ℂ) (b j) i' y = 0} =
      {z ∈ c.e '' A | ∀ k, ∑ j, C k j * chartVal b c i j z = 0} := by
    ext v
    constructor
    · rintro ⟨y, ⟨hyA, hy⟩, rfl⟩
      refine ⟨⟨y, hyA, rfl⟩, fun k => ?_⟩
      simpa only [chartVal, c.e.left_inv (hAc hyA)] using hy k i (hAi hyA)
    · rintro ⟨⟨y, hyA, rfl⟩, hy⟩
      refine ⟨y, ⟨hyA, fun k i' hi' => ?_⟩, rfl⟩
      have h0 : ∑ j, C k j * secVal Y.str (RingHom.id ℂ) (b j) i y = 0 := by
        simpa only [chartVal, c.e.left_inv (hAc hyA)] using hy k
      have e : ∀ j, secVal Y.str (RingHom.id ℂ) (b j) i' y =
          gv Y.str (RingHom.id ℂ) L i' i y * secVal Y.str (RingHom.id ℂ) (b j) i y :=
        fun j => (secVal_mem (b j)).1 i' i y hi' (hAi hyA)
      simp only [e]
      calc ∑ j, C k j * (gv Y.str (RingHom.id ℂ) L i' i y * secVal Y.str (RingHom.id ℂ) (b j) i y)
          = gv Y.str (RingHom.id ℂ) L i' i y *
              ∑ j, C k j * secVal Y.str (RingHom.id ℂ) (b j) i y := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun j _ => by ring
        _ = 0 := by rw [h0, mul_zero]
  rw [zeroCnt, ← himg, hinj.encard_image]

theorem fsBasis_φ_chart (hL : L.IsLB) {n : ℕ} (b : Fin n → L.Sec) (hb : ⨆ j, nonzeroLocus (b j) = ⊤)
    (c : AlgChart Y.str (RingHom.id ℂ) Y.dim) (i : L.ι) (v : ReciprocityTheory.L2DbarEstimates.V Y.dim) :
    (Weight.fsBasis Y.str (RingHom.id ℂ) hL b hb 1 (by simp)).φ i (c.e.symm v) =
      Real.log (∑ j, ‖chartVal b c i j v‖ ^ 2) := by
  rw [Weight.fsBasis_φ]
  simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]
  rfl

theorem chernPart_eq_lintegral (hL : L.IsLB) {n : ℕ} (b : Fin n → L.Sec)
    (hb : ⨆ j, nonzeroLocus (b j) = ⊤) (c : AlgChart Y.str (RingHom.id ℂ) Y.dim) (i : L.ι)
    (A : Set (CxPts Y.str (RingHom.id ℂ))) (hAm : MeasurableSet A) (hAc : A ⊆ c.e.source)
    (hAi : A ⊆ ptsIn Y.str (RingHom.id ℂ) (L.U i)) (hBm : MeasurableSet (c.e '' A)) :
    (Weight.fsBasis Y.str (RingHom.id ℂ) hL b hb 1 (by simp)).chernPart Y.dim 1 A =
      ∫⁻ z in c.e '' A, ENNReal.ofReal ((Y.dim.factorial : ℝ) / Real.pi ^ Y.dim *
        (ReciprocityTheory.L2DbarEstimates.cHess Y.dim
          (fun v => ((Real.log (∑ j, ‖chartVal b c i j v‖ ^ 2) : ℝ) : ℂ)) z).det.re) := by
  haveI := CxPts.secondCountableTopology_of_isProjOver (σ := RingHom.id ℂ) Y.isProjOver
  have hC := Weight.isCInf_fsBasis (p := Y.str) (σ := RingHom.id ℂ) hL b hb 1 (by simp)
  rw [Weight.chernPart_apply hC 1 c hAm hAc]
  refine setLIntegral_congr_fun hBm fun v hv => ?_
  obtain ⟨y, hy, rfl⟩ := hv
  have hys := c.e.left_inv (hAc hy)
  simp only [hys]
  rw [c.chernDens_eq hC (hAc hy) (hAi hy), AlgChart.hess]
  simp only [fsBasis_φ_chart hL b hb c i, Units.val_one, Int.cast_one, one_mul]

end GlobalTheory.CompanionTheory.FSCrofton.Chart


open GlobalTheory.CompanionTheory.FSCrofton.Chart in
theorem GlobalTheory.CompanionTheory.FSCrofton.crofton_chart : ∀ (Y : Var ℂ) (L : LB Y.X) (hL : L.IsLB) (n : ℕ) (b : Fin n → L.Sec) (hb : ⨆ j, nonzeroLocus (b j) = ⊤) (c : AlgChart Y.str (RingHom.id ℂ) Y.dim) (i : L.ι) (j₀ : Fin n) (A : Set (CxPts Y.str (RingHom.id ℂ))), A ⊆ c.e.source → A ⊆ ptsIn Y.str (RingHom.id ℂ) (L.U i) → (∀ y ∈ A, secVal Y.str (RingHom.id ℂ) (b j₀) i y ≠ 0) → IsSigmaCompact A → Measurable (fun C : Fin Y.dim → Fin n → ℂ => (({y : CxPts Y.str (RingHom.id ℂ) | y ∈ A ∧ ∀ (k : Fin Y.dim) (i' : L.ι), y ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i') → ∑ j, C k j * secVal Y.str (RingHom.id ℂ) (b j) i' y = 0}.encard : ℕ∞) : ℝ≥0∞)) ∧ ∫⁻ C : Fin Y.dim → Fin n → ℂ, gW Y.dim (Fin n) C * (({y : CxPts Y.str (RingHom.id ℂ) | y ∈ A ∧ ∀ (k : Fin Y.dim) (i' : L.ι), y ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i') → ∑ j, C k j * secVal Y.str (RingHom.id ℂ) (b j) i' y = 0}.encard : ℕ∞) : ℝ≥0∞) = ENNReal.ofReal (Real.pi ^ (Y.dim * n)) * (Weight.fsBasis Y.str (RingHom.id ℂ) hL b hb 1 (by simp)).chernPart Y.dim 1 A := by
  intro Y L hL n b hb c i j₀ A hAc hAi hA0 hAs
  have hAm : MeasurableSet A := measurableSet_of_isSigmaCompact hAs
  have hBs : IsSigmaCompact (c.e '' A) :=
    hAs.image_of_continuousOn (c.e.continuousOn.mono hAc)
  have hBm : MeasurableSet (c.e '' A) := measurableSet_of_isSigmaCompact hBs
  have hcnt := encard_eq_zeroCnt b c i A hAc hAi

  set W : Y.X.Opens := L.U i ⊓ nonzeroLocus (b j₀) with hW
  set U : Set (ReciprocityTheory.L2DbarEstimates.V Y.dim) := c.e.target ∩ c.e.symm ⁻¹' ptsIn Y.str (RingHom.id ℂ) W
    with hU
  have hUo : IsOpen U := ChartGlue.isOpen_over c.e (isOpen_ptsIn W)
  have hUi : ∀ v ∈ U, c.e.symm v ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i) := fun v hv =>
    (mem_ptsIn_inf.1 hv.2).1
  have hd : ∀ j, DifferentiableOn ℂ (chartVal b c i j) U := fun j =>
    (c.holo (L.U i) ((b j).f i)).mono fun v hv => ⟨hv.1, hUi v hv⟩
  have h0 : ∀ z ∈ U, chartVal b c i j₀ z ≠ 0 := fun z hz =>
    (secVal_ne_zero_iff (b j₀) (hUi z hz)).2 (mem_ptsIn_inf.1 hz.2).2
  have hBU : c.e '' A ⊆ U := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨c.e.map_source (hAc hy), ?_⟩
    change c.e.symm (c.e y) ∈ ptsIn Y.str (RingHom.id ℂ) W
    rw [c.e.left_inv (hAc hy)]
    exact mem_ptsIn_inf.2 ⟨hAi hy, (secVal_ne_zero_iff (b j₀) (hAi hy)).1 (hA0 y hy)⟩
  refine ⟨?_, ?_⟩
  · simp only [hcnt]
    exact GlobalTheory.T.measurable_zero_count Y.dim (Fin n) U (c.e '' A) (chartVal b c i)
      (fun j => (hd j).continuousOn) hBU hBs
  · simp only [hcnt]
    have key := GlobalTheory.T.random_section_zero_count Y.dim (Fin n) j₀ U (c.e '' A) (chartVal b c i) hUo hd h0 hBU hBs
    rw [key, Fintype.card_fin, chernPart_eq_lintegral hL b hb c i A hAm hAc hAi hBm]
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableLocalZeroCountStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurable_local_zero_count : ∀ (Y : Var ℂ) (L : LB Y.X) (hL : L.IsLB) (n : ℕ) (b : Fin n → L.Sec) (hb : ⨆ j, nonzeroLocus (b j) = ⊤) (c : AlgChart Y.str (RingHom.id ℂ) Y.dim) (i : L.ι) (j₀ : Fin n) (A : Set (CxPts Y.str (RingHom.id ℂ))), A ⊆ c.e.source → A ⊆ ptsIn Y.str (RingHom.id ℂ) (L.U i) → (∀ y ∈ A, secVal Y.str (RingHom.id ℂ) (b j₀) i y ≠ 0) → IsSigmaCompact A → Measurable (fun C : Fin Y.dim → Fin n → ℂ => (({y : CxPts Y.str (RingHom.id ℂ) | y ∈ A ∧ ∀ (k : Fin Y.dim) (i' : L.ι), y ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i') → ∑ j, C k j * secVal Y.str (RingHom.id ℂ) (b j) i' y = 0}.encard : ℕ∞) : ℝ≥0∞)) ∧ ∫⁻ C : Fin Y.dim → Fin n → ℂ, gW Y.dim (Fin n) C * (({y : CxPts Y.str (RingHom.id ℂ) | y ∈ A ∧ ∀ (k : Fin Y.dim) (i' : L.ι), y ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i') → ∑ j, C k j * secVal Y.str (RingHom.id ℂ) (b j) i' y = 0}.encard : ℕ∞) : ℝ≥0∞) = ENNReal.ofReal (Real.pi ^ (Y.dim * n)) * (Weight.fsBasis Y.str (RingHom.id ℂ) hL b hb 1 (by simp)).chernPart Y.dim 1 A := by
  first | exact @GlobalTheory.CompanionTheory.FSCrofton.crofton_chart | exact GlobalTheory.CompanionTheory.FSCrofton.crofton_chart | (intros; apply GlobalTheory.CompanionTheory.FSCrofton.crofton_chart <;> assumption)
end
