module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SobolevInequalityOnGroup
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneMemGoodCT
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveKernelUniqueness
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EnergyIdentityOfLengthFunction
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.AsmKerOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AsmMultMain

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinitePropagationSpeedHolds
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothMonotoneCutoffExists
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothMonotoneCutoffExists
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.SmoothCut

theorem exists_smooth_antitone_cut :
    ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧ (∀ x, deriv χ x ≤ 0) ∧ (∀ x, 0 ≤ χ x) ∧
      (∀ x, x ≤ 0 → χ x = 1) ∧ ∀ x, 1 ≤ x → χ x = 0 := by
  have hanti : Antitone (fun x : ℝ => Real.smoothTransition (1 - x)) := fun a b hab =>
    Real.smoothTransition.monotone (by linarith)
  refine ⟨fun x => Real.smoothTransition (1 - x),
    Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id), ?_,
    fun x => Real.smoothTransition.nonneg _,
    fun x hx => Real.smoothTransition.one_of_one_le (by linarith),
    fun x hx => Real.smoothTransition.zero_of_nonpos (by linarith)⟩
  intro x
  have hneg : Monotone (fun x : ℝ => -Real.smoothTransition (1 - x)) := fun a b hab =>
    neg_le_neg (hanti hab)
  have h := hneg.deriv_nonneg (x := x)
  rw [deriv.fun_neg] at h
  linarith

end GlobalTheory.CompanionTheory.SmoothCut
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothMonotoneCutoffExistsStatement
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_monotone_cutoff_exists : ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧ (∀ x, deriv χ x ≤ 0) ∧ (∀ x, 0 ≤ χ x) ∧ (∀ x, x ≤ 0 → χ x = 1) ∧ ∀ x, 1 ≤ x → χ x = 0 := by
  first | exact @GlobalTheory.CompanionTheory.SmoothCut.exists_smooth_antitone_cut | exact GlobalTheory.CompanionTheory.SmoothCut.exists_smooth_antitone_cut | (intros; apply GlobalTheory.CompanionTheory.SmoothCut.exists_smooth_antitone_cut <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TranslatedLengthBoundedDerivative
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TranslatedLengthBoundedDerivative
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveSpd

variable {n : ℕ}

def lmulCLM (a : Mat n) : Mat n →L[ℝ] Mat n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => a * y
      map_add' := mul_add a
      map_smul' := fun r y => by simp }

theorem lmulCLM_apply (a y : Mat n) : lmulCLM a y = a * y := rfl

theorem inv_mul_mem_GLs {x y : Mat n} (hx : x ∈ GLs n) (hy : y ∈ GLs n) : x⁻¹ * y ∈ GLs n := by
  have hxu : IsUnit x.det := isUnit_iff_ne_zero.2 hx
  have h1 : IsUnit (x⁻¹).det := Matrix.isUnit_nonsing_inv_det x hxu
  show (x⁻¹ * y).det ≠ 0
  rw [Matrix.det_mul]
  exact mul_ne_zero h1.ne_zero hy

theorem lg_left_facts : LgFacts → ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ GLs n,
    ContDiffOn ℝ ∞ (fun y : Mat n => lg (x⁻¹ * y)) (GLs n) ∧
    (∀ R : ℝ, IsCompact {y : G n | lg (x⁻¹ * y.val) ≤ R}) ∧
    ∀ y ∈ GLs n, ∀ p : Ix n, |fderiv ℝ (fun y : Mat n => lg (x⁻¹ * y)) y (y * hm p)| ≤ C := by
  intro hL n
  obtain ⟨-, -, -, hsm, hcpt, -, C₀, hC₀⟩ := hL n
  refine ⟨2 * |C₀|, by positivity, fun x hx => ?_⟩
  have hxu : IsUnit x.det := isUnit_iff_ne_zero.2 hx
  have hsm' : ContDiffOn ℝ ∞ (fun y : Mat n => lg (x⁻¹ * y)) (GLs n) :=
    hsm.comp (lmulCLM x⁻¹).contDiff.contDiffOn (fun y hy => inv_mul_mem_GLs hx hy)
  refine ⟨hsm', fun R => ?_, fun y hy p => ?_⟩
  · have hxU : IsUnit x := (Matrix.isUnit_iff_isUnit_det x).2 hxu
    let X : G n := hxU.unit
    have hXv : (X : Mat n) = x := rfl
    have hXi : ((X⁻¹ : G n) : Mat n) = x⁻¹ := by
      rw [Matrix.coe_units_inv, hXv]
    have hset : {y : G n | lg (x⁻¹ * y.val) ≤ R} = (fun z : G n => X * z) '' {z : G n | lg z.val ≤ R} := by
      ext y
      constructor
      · intro hy
        refine ⟨X⁻¹ * y, ?_, by simp⟩
        show lg ((X⁻¹ * y : G n) : Mat n) ≤ R
        rw [Units.val_mul, hXi]
        exact hy
      · rintro ⟨z, hz, rfl⟩
        show lg (x⁻¹ * ((X * z : G n) : Mat n)) ≤ R
        rw [Units.val_mul, ← hXi, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
        exact hz
    rw [hset]
    exact (hcpt R).image (continuous_const.mul continuous_id)
  · have hw : x⁻¹ * y ∈ GLs n := inv_mul_mem_GLs hx hy
    have hdiff : DifferentiableAt ℝ lg (x⁻¹ * y) :=
      (hsm.contDiffAt (isOpen_GLs.mem_nhds hw)).differentiableAt (by simp)
    have hder : fderiv ℝ (fun y : Mat n => lg (x⁻¹ * y)) y
        = (fderiv ℝ lg (x⁻¹ * y)).comp (lmulCLM x⁻¹) :=
      ((hdiff.hasFDerivAt).comp y (lmulCLM x⁻¹).hasFDerivAt).fderiv
    have hCle : C₀ ≤ |C₀| := le_abs_self C₀
    rw [hder, ContinuousLinearMap.comp_apply, lmulCLM_apply, ← mul_assoc]
    obtain ⟨b, i, j⟩ := p
    have h1 := abs_le.1 (hC₀ _ hw (b, i, j))
    have h2 := abs_le.1 (hC₀ _ hw (b, j, i))
    cases b
    · have e : hm ((false, i, j) : Ix n) = bs (false, i, j) - bs (false, j, i) := by
        simp [hm, bs]
      rw [e, mul_sub, map_sub, abs_le]
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    · have e : hm ((true, i, j) : Ix n) = bs (true, i, j) + bs (true, j, i) := by
        simp [hm, bs]
      rw [e, mul_add, map_add (f := _), abs_le]
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

end GlobalTheory.CompanionTheory.WaveSpd
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TranslatedLengthBoundedDerivativeStatement
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translated_length_bounded_derivative : LgFacts → ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ GLs n, ContDiffOn ℝ ∞ (fun y : Mat n => lg (x⁻¹ * y)) (GLs n) ∧ (∀ R : ℝ, IsCompact {y : G n | lg (x⁻¹ * y.val) ≤ R}) ∧ ∀ y ∈ GLs n, ∀ p : Ix n, |fderiv ℝ (fun y : Mat n => lg (x⁻¹ * y)) y (y * hm p)| ≤ C := by
  first | exact @GlobalTheory.CompanionTheory.WaveSpd.lg_left_facts | exact GlobalTheory.CompanionTheory.WaveSpd.lg_left_facts | (intros; apply GlobalTheory.CompanionTheory.WaveSpd.lg_left_facts <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralRrEqZero
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralRrEqZero
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveSpd

theorem Rd_ofReal_eq {n : ℕ} {Ψ : Mat n → ℝ} (hΨ : ContDiffOn ℝ ∞ Ψ (GLs n)) (X : Mat n)
    {y : Mat n} (hy : y ∈ GLs n) :
    Rd X (fun z => (Ψ z : ℂ)) y = ((Rr X Ψ y : ℝ) : ℂ) := by
  have hd : DifferentiableAt ℝ Ψ y :=
    ((hΨ y hy).contDiffAt (isOpen_GLs.mem_nhds hy)).differentiableAt (by simp)
  have h : HasFDerivAt (fun z => (Ψ z : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ Ψ y)) y :=
    Complex.ofRealCLM.hasFDerivAt.comp y hd.hasFDerivAt
  simp only [Rd, Rr, h.fderiv]
  rfl

theorem integral_Rr_eq_zero : RCalc → ∀ {n : ℕ} [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (Ψ : Mat n → ℝ), ContDiffOn ℝ ∞ Ψ (GLs n) → (∃ R : ℝ, ∀ y ∈ GLs n, R < lg y → Ψ y = 0) → ∀ X : Mat n, ∫ y : G n, Rr X Ψ y.val ∂μ = 0 := by
  intro hR n _ _ μ _ Ψ hΨ hc X
  have hf : ContDiffOn ℝ ∞ (fun z => (Ψ z : ℂ)) (GLs n) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hΨ
  have hcf : Cpt (fun z => (Ψ z : ℂ)) := by
    obtain ⟨R, hR'⟩ := hc
    exact ⟨R, fun y hy h => by simp [hR' y hy h]⟩
  have h0 := (hR n).2.2 μ ℂ (fun z => (Ψ z : ℂ)) hf hcf X
  have h1 : (fun y : G n => Rd X (fun z => (Ψ z : ℂ)) y.val) =
      fun y : G n => ((Rr X Ψ y.val : ℝ) : ℂ) :=
    funext fun y => Rd_ofReal_eq hΨ X (val_mem_GLs y)
  rw [h1, integral_complex_ofReal] at h0
  exact Complex.ofReal_eq_zero.1 h0

end GlobalTheory.CompanionTheory.WaveSpd
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralRrEqZeroStatement
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_right_derivative_zero_alt : RCalc → ∀ {n : ℕ} [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (Ψ : Mat n → ℝ), ContDiffOn ℝ ∞ Ψ (GLs n) → (∃ R : ℝ, ∀ y ∈ GLs n, R < lg y → Ψ y = 0) → ∀ X : Mat n, ∫ y : G n, Rr X Ψ y.val ∂μ = 0 := by
  first | exact @GlobalTheory.CompanionTheory.WaveSpd.integral_Rr_eq_zero | exact GlobalTheory.CompanionTheory.WaveSpd.integral_Rr_eq_zero | (intros; apply GlobalTheory.CompanionTheory.WaveSpd.integral_Rr_eq_zero <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinitePropagationSpeedHolds
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

namespace GlobalTheory.CompanionTheory.WaveSpd

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem locCpt (n : ℕ) : LocallyCompactSpace (G n) := by
  haveI : LocallyCompactSpace (Mat n) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
  haveI : LocallyCompactSpace (Mat n)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

theorem exists_haar (n : ℕ) : ∃ (_ : MeasurableSpace (G n)) (_ : BorelSpace (G n)) (μ : Measure (G n)), μ.IsHaarMeasure := by
  haveI := locCpt n
  letI : MeasurableSpace (G n) := borel _
  haveI : BorelSpace (G n) := ⟨rfl⟩
  exact ⟨inferInstance, inferInstance, Measure.haar, inferInstance⟩

theorem waveEq {n : ℕ} (E : KMod n) (u : ℝ → Mat n → E.V) (hu : IsWave E u) (A : E.V →L[ℂ] E.V)
    (hA : ∀ f ∈ CE E, ∀ g ∈ GLs n, Om f g = (1 / 4 : ℂ) • ∑ p : Ix n, Rd (hm p) (Rd (hm p) f) g + A (f g)) :
    ∀ s, ∀ y ∈ GLs n, dt (dt u) s y = (1 / 4 : ℝ) • ∑ p : Ix n, Rr (hm p) (Rt (hm p) u s) y + (A.restrictScalars ℝ) (u s y) := by
  intro s y hy
  have h := hu.2.2.1 s y hy
  rw [hA _ (hu.2.1 s) y hy] at h
  have h2 : dt (dt u) s y = iteratedDeriv 2 (fun r => u r y) s := by
    simp only [dt, iteratedDeriv_succ, iteratedDeriv_zero]
  rw [h2, h]
  have : (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) := by push_cast; rfl
  rw [this]
  rfl

theorem speed_pos (hL : LgFacts) (hR : RCalc) {n : ℕ} (C₁ : ℝ) (hC₁ : 0 ≤ C₁)
    (hlg : ∀ x ∈ GLs n, ContDiffOn ℝ ∞ (fun y : Mat n => lg (x⁻¹ * y)) (GLs n) ∧ (∀ R : ℝ, IsCompact {y : G n | lg (x⁻¹ * y.val) ≤ R}) ∧ ∀ y ∈ GLs n, ∀ p : Ix n, |fderiv ℝ (fun y : Mat n => lg (x⁻¹ * y)) y (y * hm p)| ≤ C₁)
    (χ : ℝ → ℝ) (h1 : ContDiff ℝ ∞ χ) (h2 : ∀ x, deriv χ x ≤ 0) (h3 : ∀ x, 0 ≤ χ x) (h4 : ∀ x, x ≤ 0 → χ x = 1) (h5 : ∀ x, 1 ≤ x → χ x = 0)
    (E : KMod n) (u : ℝ → Mat n → E.V) (hu : IsWave E u) (t : ℝ) (ht : 0 ≤ t) (x : Mat n) (hx : x ∈ GLs n)
    (C : ℝ) (hC : C₁ * (1 + Fintype.card (Ix n)) ≤ C)
    (h0 : ∀ y ∈ GLs n, lg y ≤ lg (1 : Mat n) + 1 + C * t → u 0 (x * y) = 0) : u t x = 0 := by
  obtain ⟨mG, bG, μ, hμ⟩ := exists_haar n
  letI : InnerProductSpace ℝ E.V := InnerProductSpace.rclikeToReal ℂ E.V
  obtain ⟨A, hA⟩ := GlobalTheory.T.casimir_right_laplacian_formula E
  obtain ⟨l1, l2, l3⟩ := hlg x hx
  have hxu : IsUnit x.det := isUnit_iff_ne_zero.2 hx
  have hxx : x⁻¹ * x = 1 := Matrix.nonsing_inv_mul _ hxu
  have hxx' : x * x⁻¹ = 1 := Matrix.mul_nonsing_inv _ hxu
  have hxi : x⁻¹ ∈ GLs n := by
    have : x⁻¹.det * x.det = 1 := by rw [← Matrix.det_mul, hxx, Matrix.det_one]
    exact left_ne_zero_of_mul_eq_one this |> fun h => h
  have hmul : ∀ y ∈ GLs n, x⁻¹ * y ∈ GLs n := fun y hy => by
    simp only [GLs, Set.mem_setOf_eq, Matrix.det_mul]
    exact mul_ne_zero hxi hy
  have hbp : ∀ Ψ : Mat n → ℝ, ContDiffOn ℝ ∞ Ψ (GLs n) → (∃ R : ℝ, ∀ y ∈ GLs n, R < lg (x⁻¹ * y) → Ψ y = 0) → ∀ X : Mat n, ∫ y : G n, Rr X Ψ y.val ∂μ = 0 := by
    intro Ψ hΨ ⟨R, hRΨ⟩ X
    refine GlobalTheory.T.integral_right_derivative_zero_alt hR μ Ψ hΨ ⟨R + lg x, fun y hy hlt => hRΨ y hy ?_⟩ X
    have := (hL n).1 x hx _ (hmul y hy)
    rw [← mul_assoc, hxx', one_mul] at this
    linarith
  have hv := GlobalTheory.T.energy_identity_of_length_function (W := E.V) μ (fun y => lg (x⁻¹ * y)) l1 l2 C₁ hC₁ l3 hbp χ h1 h2 h3 h5 u hu.1
    (A.restrictScalars ℝ) (waveEq E u hu A hA) C hC (lg (1 : Mat n) + C * t) h4 ?_ ?_ t ht x hx ?_
  · exact hv
  · intro y hy hlt
    have := h0 (x⁻¹ * y) (hmul y hy) (by have h' : lg (x⁻¹ * y) < lg (1 : Mat n) + C * t + 1 := hlt; linarith)
    rwa [← mul_assoc, hxx', one_mul] at this
  · intro y hy
    exact hu.2.2.2 y hy
  · simp only [hxx]
    exact le_refl _

theorem asmSpeed : AsmSpeed := by
  intro hL hU hR n
  obtain ⟨C₁, hC₁, hlg⟩ := GlobalTheory.T.translated_length_bounded_derivative hL n
  obtain ⟨χ, h1, h2, h3, h4, h5⟩ := GlobalTheory.T.smooth_monotone_cutoff_exists
  set C := C₁ * (1 + Fintype.card (Ix n)) with hCdef
  have hC0 : 0 ≤ C := by positivity
  have hl0 : 0 ≤ lg (1 : Mat n) := by
    unfold lg
    apply Real.log_nonneg
    have : 0 ≤ ∑ a, ∑ b, (‖(1 : Mat n) a b‖ ^ 2 + ‖(1 : Mat n)⁻¹ a b‖ ^ 2) := by positivity
    linarith
  refine ⟨C + lg (1 : Mat n) + 1, ?_⟩
  have key : ∀ (E : KMod n) (u : ℝ → Mat n → E.V), IsWave E u → ∀ t : ℝ, 0 ≤ t → ∀ x ∈ GLs n,
      (∀ y ∈ GLs n, lg y ≤ (C + lg (1 : Mat n) + 1) * (1 + t) → u 0 (x * y) = 0) → u t x = 0 := by
    intro E u hu t ht x hx h0
    refine speed_pos hL hR C₁ hC₁ hlg χ h1 h2 h3 h4 h5 E u hu t ht x hx C le_rfl ?_
    intro y hy hle
    refine h0 y hy (hle.trans ?_)
    nlinarith [mul_nonneg hC0 ht, mul_nonneg hl0 ht]
  intro E u hu t x hx h0
  rcases le_total 0 t with ht | ht
  · exact key E u hu t ht x hx (by rwa [abs_of_nonneg ht] at h0)
  · have := key E _ (GlobalTheory.T.wave_time_reversal E u hu) (-t) (by linarith) x hx (by
      intro y hy hle
      simp only [neg_zero]
      exact h0 y hy (by rwa [abs_of_nonpos ht]))
    simpa using this

end GlobalTheory.CompanionTheory.WaveSpd
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinitePropagationSpeedHoldsStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_propagation_speed_holds : PositivityTheory.RgBcC.AsmSpeed := by
  first | exact @GlobalTheory.CompanionTheory.WaveSpd.asmSpeed | exact GlobalTheory.CompanionTheory.WaveSpd.asmSpeed | (intros; apply GlobalTheory.CompanionTheory.WaveSpd.asmSpeed <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraEstimateForRegularity
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraEstimateForRegularity
noncomputable section

open Finset
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.SkewWords

variable {V ι : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [Fintype ι]
  (X : ι → Module.End ℂ V)

def wd (w : List ι) : Module.End ℂ V := (w.map X).prod

def lap : Module.End ℂ V := -∑ i, X i * X i

def bsum (m : ℕ) (u : V) : ℝ := ∑ v : List.Vector ι m, ‖wd X v.1 u‖

def qsum (m : ℕ) (u : V) : ℝ := ∑ j ∈ range (m + 1), ‖(lap X ^ j) u‖

def wspan (m : ℕ) : Submodule ℂ (Module.End ℂ V) :=
  Submodule.span ℂ {T | ∃ w : List ι, w.length = m ∧ T = wd X w}

theorem wd_nil : wd X [] = 1 := by simp [wd]

theorem wd_cons (a : ι) (w : List ι) : wd X (a :: w) = X a * wd X w := by simp [wd]

theorem wd_concat (a : ι) (w : List ι) : wd X (w ++ [a]) = wd X w * X a := by simp [wd]

theorem norm_le_bsum {m : ℕ} (w : List ι) (hw : w.length = m) (u : V) : ‖wd X w u‖ ≤ bsum X m u :=
  let v : List.Vector ι m := ⟨w, hw⟩
  Finset.single_le_sum (s := (univ : Finset (List.Vector ι m))) (f := fun v : List.Vector ι m => ‖wd X v.1 u‖)
    (fun _ _ => norm_nonneg _) (mem_univ v)

theorem bsum_nonneg (m : ℕ) (u : V) : 0 ≤ bsum X m u := sum_nonneg fun _ _ => norm_nonneg _

theorem qsum_le_succ (m : ℕ) (u : V) : qsum X m u ≤ qsum X (m + 1) u := by
  unfold qsum
  rw [sum_range_succ _ (m + 1)]
  exact le_add_of_nonneg_right (norm_nonneg _)

theorem qsum_lap_le (m : ℕ) (u : V) : qsum X m (lap X u) ≤ qsum X (m + 1) u := by
  unfold qsum
  rw [sum_range_succ' _ (m + 1)]
  have : ∀ j, ‖(lap X ^ j) (lap X u)‖ = ‖(lap X ^ (j + 1)) u‖ := fun j => by
    rw [pow_succ, Module.End.mul_apply]
  simp only [this]
  exact le_add_of_nonneg_right (norm_nonneg _)

theorem bound_of_mem {m : ℕ} {T : Module.End ℂ V} (hT : T ∈ wspan X m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u, ‖T u‖ ≤ C * bsum X m u := by
  induction hT using Submodule.span_induction with
  | mem T h =>
    obtain ⟨w, hw, rfl⟩ := h
    exact ⟨1, zero_le_one, fun u => by simpa using norm_le_bsum X w hw u⟩
  | zero => exact ⟨0, le_rfl, fun u => by simp⟩
  | add S T _ _ hS hT =>
    obtain ⟨C, hC, h⟩ := hS
    obtain ⟨D, hD, k⟩ := hT
    refine ⟨C + D, add_nonneg hC hD, fun u => ?_⟩
    calc ‖(S + T) u‖ ≤ ‖S u‖ + ‖T u‖ := norm_add_le _ _
      _ ≤ C * bsum X m u + D * bsum X m u := add_le_add (h u) (k u)
      _ = _ := by ring
  | smul a T _ hT =>
    obtain ⟨C, hC, h⟩ := hT
    refine ⟨‖a‖ * C, by positivity, fun u => ?_⟩
    rw [LinearMap.smul_apply, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h u) (norm_nonneg _)

theorem mul_left_mem {m : ℕ} {T : Module.End ℂ V} (a : ι) (hT : T ∈ wspan X m) :
    X a * T ∈ wspan X (m + 1) := by
  induction hT using Submodule.span_induction with
  | mem T h =>
    obtain ⟨w, hw, rfl⟩ := h
    exact Submodule.subset_span ⟨a :: w, by simp [hw], (wd_cons X a w).symm⟩
  | zero => simp
  | add S T _ _ hS hT => rw [mul_add]; exact add_mem hS hT
  | smul c T _ hT => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hT

theorem mul_right_mem {m : ℕ} {T : Module.End ℂ V} (a : ι) (hT : T ∈ wspan X m) :
    T * X a ∈ wspan X (m + 1) := by
  induction hT using Submodule.span_induction with
  | mem T h =>
    obtain ⟨w, hw, rfl⟩ := h
    exact Submodule.subset_span ⟨w ++ [a], by simp [hw], (wd_concat X a w).symm⟩
  | zero => simp
  | add S T _ _ hS hT => rw [add_mul]; exact add_mem hS hT
  | smul c T _ hT => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ hT

theorem comm_mem (c : ι → ι → ι → ℝ) (hc : ∀ i j, X i * X j - X j * X i = ∑ k, (c i j k : ℂ) • X k)
    (i : ι) (w : List ι) : X i * wd X w - wd X w * X i ∈ wspan X w.length := by
  induction w with
  | nil => simp [wd_nil]
  | cons a w ih =>
    have e : X i * wd X (a :: w) - wd X (a :: w) * X i =
        (X i * X a - X a * X i) * wd X w + X a * (X i * wd X w - wd X w * X i) := by
      rw [wd_cons]; noncomm_ring
    rw [e, hc, Finset.sum_mul]
    refine add_mem (sum_mem fun k _ => ?_) (mul_left_mem X a ih)
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k :: w, by simp, (wd_cons X k w).symm⟩)

theorem lap_comm_mem (c : ι → ι → ι → ℝ) (hc : ∀ i j, X i * X j - X j * X i = ∑ k, (c i j k : ℂ) • X k)
    (w : List ι) : lap X * wd X w - wd X w * lap X ∈ wspan X (w.length + 1) := by
  have h : ∀ i, X i * (X i * wd X w - wd X w * X i) + (X i * wd X w - wd X w * X i) * X i =
      X i * X i * wd X w - wd X w * (X i * X i) := fun i => by noncomm_ring
  have e : lap X * wd X w - wd X w * lap X =
      -∑ i, (X i * (X i * wd X w - wd X w * X i) + (X i * wd X w - wd X w * X i) * X i) := by
    simp only [h, sum_sub_distrib, lap, neg_mul, mul_neg, Finset.sum_mul, Finset.mul_sum]
    abel
  rw [e]
  exact neg_mem (sum_mem fun i _ => add_mem (mul_left_mem X i (comm_mem X c hc i w))
    (mul_right_mem X i (comm_mem X c hc i w)))

theorem lap_comm_bound (c : ι → ι → ι → ℝ)
    (hc : ∀ i j, X i * X j - X j * X i = ∑ k, (c i j k : ℂ) • X k) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : List ι, w.length = m → ∀ u,
      ‖(lap X * wd X w - wd X w * lap X) u‖ ≤ C * bsum X (m + 1) u := by
  have h : ∀ v : List.Vector ι m, ∃ C : ℝ, 0 ≤ C ∧ ∀ u,
      ‖(lap X * wd X v.1 - wd X v.1 * lap X) u‖ ≤ C * bsum X (m + 1) u := fun v => by
    have := lap_comm_mem X c hc v.1
    rw [v.2] at this
    exact bound_of_mem X this
  choose C hC h using h
  refine ⟨∑ v, C v, sum_nonneg fun v _ => hC v, fun w hw u => ?_⟩
  refine (h ⟨w, hw⟩ u).trans (mul_le_mul_of_nonneg_right ?_ (bsum_nonneg X _ u))
  exact Finset.single_le_sum (f := C) (fun v _ => hC v) (mem_univ _)

theorem sum_sq_eq (hs : ∀ i u v, ⟪X i u, v⟫_ℂ = -⟪u, X i v⟫_ℂ) (a : V) :
    ∑ i, ‖X i a‖ ^ 2 = (⟪a, lap X a⟫_ℂ).re := by
  have h : lap X a = -∑ i, X i (X i a) := by
    simp [lap, Module.End.mul_apply, LinearMap.sum_apply]
  rw [h, inner_neg_right, inner_sum, Complex.neg_re, Complex.re_sum, ← Finset.sum_neg_distrib]
  refine sum_congr rfl fun i _ => ?_
  have e : ⟪a, X i (X i a)⟫_ℂ = -⟪X i a, X i a⟫_ℂ := by rw [hs]; simp
  rw [e, Complex.neg_re, neg_neg]
  simpa using (inner_self_eq_norm_sq (𝕜 := ℂ) (X i a)).symm

theorem sq_le_lap (hs : ∀ i u v, ⟪X i u, v⟫_ℂ = -⟪u, X i v⟫_ℂ) (i : ι) (a : V) :
    ‖X i a‖ ^ 2 ≤ (⟪a, lap X a⟫_ℂ).re := by
  rw [← sum_sq_eq X hs]
  exact Finset.single_le_sum (f := fun i => ‖X i a‖ ^ 2) (fun _ _ => by positivity) (mem_univ i)

theorem core (hs : ∀ i u v, ⟪X i u, v⟫_ℂ = -⟪u, X i v⟫_ℂ) (i b : ι) (w : List ι) (u : V) :
    ‖wd X (i :: b :: w) u‖ ^ 2 ≤ ‖wd X (b :: b :: w) u‖ * ‖wd X w (lap X u)‖ +
      ‖wd X (b :: w) u‖ * ‖(lap X * wd X (b :: w) - wd X (b :: w) * lap X) u‖ := by
  set a := wd X (b :: w) u with ha
  set G := lap X * wd X (b :: w) - wd X (b :: w) * lap X with hG
  have e1 : wd X (i :: b :: w) u = X i a := by rw [wd_cons]; rfl
  have e2 : wd X (b :: b :: w) u = X b a := by rw [wd_cons]; rfl
  have e3 : lap X a = X b (wd X w (lap X u)) + G u := by
    simp only [hG, ha, LinearMap.sub_apply, Module.End.mul_apply, wd_cons]
    abel
  rw [e1, e2]
  refine (sq_le_lap X hs i a).trans ?_
  rw [e3, inner_add_right, Complex.add_re]
  have e4 : ⟪a, X b (wd X w (lap X u))⟫_ℂ = -⟪X b a, wd X w (lap X u)⟫_ℂ := by rw [hs]; simp
  refine add_le_add ?_ ((Complex.re_le_norm _).trans (norm_inner_le_norm _ _))
  rw [e4, Complex.neg_re]
  exact (neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _))

theorem bsum_le_of_sq (m : ℕ) (u : V) (D : ℝ) (hD : 0 ≤ D)
    (h : ∀ v : List.Vector ι m, ‖wd X v.1 u‖ ^ 2 ≤ bsum X m u * D) :
    bsum X m u ≤ (Fintype.card (List.Vector ι m) : ℝ) ^ 2 * D := by
  set b := bsum X m u with hb
  set N : ℝ := ((Fintype.card (List.Vector ι m) : ℕ) : ℝ) with hN
  have hb0 : 0 ≤ b := bsum_nonneg X m u
  have h1 : b ^ 2 ≤ N * ∑ v : List.Vector ι m, ‖wd X v.1 u‖ ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (List.Vector ι m)))
      (f := fun v => ‖wd X v.1 u‖)
    simpa [hb, bsum, hN] using this
  have h2 : ∑ v : List.Vector ι m, ‖wd X v.1 u‖ ^ 2 ≤ N * (b * D) := by
    have := Finset.sum_le_card_nsmul (univ : Finset (List.Vector ι m)) (fun v => ‖wd X v.1 u‖ ^ 2)
      (b * D) (fun v _ => h v)
    simpa [hN] using this
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  have h3 : b ^ 2 ≤ N ^ 2 * D * b := by
    calc b ^ 2 ≤ N * (N * (b * D)) := h1.trans (mul_le_mul_of_nonneg_left h2 hN0)
      _ = _ := by ring
  rcases hb0.eq_or_lt with h0 | h0
  · rw [← h0]; positivity
  · exact le_of_mul_le_mul_right (by nlinarith) h0

theorem bsum_le_card (m : ℕ) (u : V) (D : ℝ) (h : ∀ v : List.Vector ι m, ‖wd X v.1 u‖ ≤ D) :
    bsum X m u ≤ (Fintype.card (List.Vector ι m) : ℝ) * D := by
  have := Finset.sum_le_card_nsmul (univ : Finset (List.Vector ι m)) (fun v => ‖wd X v.1 u‖)
      D (fun v _ => h v)
  simpa [bsum] using this

theorem bound_zero : ∃ C : ℝ, 0 ≤ C ∧ ∀ u, bsum X 0 u ≤ C * qsum X 0 u := by
  refine ⟨_, Nat.cast_nonneg (Fintype.card (List.Vector ι 0)), fun u => bsum_le_card X 0 u _ fun v => ?_⟩
  obtain ⟨w, hw⟩ := v
  obtain rfl : w = [] := List.length_eq_zero_iff.mp hw
  simp [wd_nil, qsum]

theorem bound_one (hs : ∀ i u v, ⟪X i u, v⟫_ℂ = -⟪u, X i v⟫_ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u, bsum X 1 u ≤ C * qsum X 1 u := by
  refine ⟨_, Nat.cast_nonneg (Fintype.card (List.Vector ι 1)), fun u => bsum_le_card X 1 u _ fun v => ?_⟩
  obtain ⟨w, hw⟩ := v
  obtain ⟨i, rfl⟩ := List.length_eq_one_iff.mp hw
  have e : wd X [i] u = X i u := by simp [wd]
  have q : qsum X 1 u = ‖u‖ + ‖lap X u‖ := by simp [qsum, sum_range_succ]
  show ‖wd X [i] u‖ ≤ _
  rw [e, q]
  have h1 : ‖X i u‖ ^ 2 ≤ ‖u‖ * ‖lap X u‖ :=
    (sq_le_lap X hs i u).trans ((Complex.re_le_norm _).trans (norm_inner_le_norm _ _))
  have h2 : 0 ≤ ‖u‖ := norm_nonneg _
  have h3 : 0 ≤ ‖lap X u‖ := norm_nonneg _
  exact abs_le_of_sq_le_sq' (by nlinarith) (by positivity) |>.2

theorem bound_step (hs : ∀ i u v, ⟪X i u, v⟫_ℂ = -⟪u, X i v⟫_ℂ) (c : ι → ι → ι → ℝ)
    (hc : ∀ i j, X i * X j - X j * X i = ∑ k, (c i j k : ℂ) • X k) (m : ℕ)
    (h0 : ∃ C : ℝ, 0 ≤ C ∧ ∀ u, bsum X m u ≤ C * qsum X m u)
    (h1 : ∃ C : ℝ, 0 ≤ C ∧ ∀ u, bsum X (m + 1) u ≤ C * qsum X (m + 1) u) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u, bsum X (m + 2) u ≤ C * qsum X (m + 2) u := by
  obtain ⟨C₁, hC₁, k₁⟩ := h0
  obtain ⟨C₂, hC₂, k₂⟩ := h1
  obtain ⟨C₃, hC₃, k₃⟩ := lap_comm_bound X c hc (m + 1)
  set N : ℝ := ((Fintype.card (List.Vector ι (m + 2)) : ℕ) : ℝ) with hN
  refine ⟨N ^ 2 * (C₁ + C₃ * C₂), by positivity, fun u => ?_⟩
  set b := bsum X (m + 2) u with hb
  have hb0 : 0 ≤ b := bsum_nonneg X _ u
  set D := bsum X m (lap X u) + C₃ * bsum X (m + 1) u with hD
  have hD0 : 0 ≤ D := add_nonneg (bsum_nonneg X _ _) (mul_nonneg hC₃ (bsum_nonneg X _ _))
  have key : ∀ v : List.Vector ι (m + 2), ‖wd X v.1 u‖ ^ 2 ≤ b * D := by
    rintro ⟨w₀, hw₀⟩
    rcases w₀ with _ | ⟨i, _ | ⟨a, w⟩⟩
    · simp at hw₀
    · simp at hw₀
    have hw : w.length = m := by simpa using hw₀
    have t1 : ‖wd X (a :: a :: w) u‖ ≤ b := norm_le_bsum X _ (by simp [hw]) u
    have t2 : ‖wd X w (lap X u)‖ ≤ bsum X m (lap X u) := norm_le_bsum X _ hw _
    have t3 : ‖wd X (a :: w) u‖ ≤ bsum X (m + 1) u := norm_le_bsum X _ (by simp [hw]) u
    have t4 := k₃ (a :: w) (by simp [hw]) u
    have s1 := mul_le_mul t1 t2 (norm_nonneg _) hb0
    have s2 := mul_le_mul t3 t4 (norm_nonneg _) (bsum_nonneg X _ u)
    refine (core X hs i a w u).trans ((add_le_add s1 s2).trans (le_of_eq ?_))
    rw [hD]; ring
  have hbD : b ≤ N ^ 2 * D := bsum_le_of_sq X (m + 2) u D hD0 key
  have q1 : qsum X m (lap X u) ≤ qsum X (m + 2) u :=
    (qsum_lap_le X m u).trans (qsum_le_succ X _ u)
  have q2 : qsum X (m + 1) u ≤ qsum X (m + 2) u := qsum_le_succ X _ u
  have d1 : bsum X m (lap X u) ≤ C₁ * qsum X (m + 2) u :=
    (k₁ _).trans (mul_le_mul_of_nonneg_left q1 hC₁)
  have d2 : C₃ * bsum X (m + 1) u ≤ C₃ * (C₂ * qsum X (m + 2) u) :=
    mul_le_mul_of_nonneg_left ((k₂ _).trans (mul_le_mul_of_nonneg_left q2 hC₂)) hC₃
  have hDle : D ≤ (C₁ + C₃ * C₂) * qsum X (m + 2) u := by
    rw [hD]; nlinarith
  calc b ≤ N ^ 2 * D := hbD
    _ ≤ N ^ 2 * ((C₁ + C₃ * C₂) * qsum X (m + 2) u) := mul_le_mul_of_nonneg_left hDle (by positivity)
    _ = _ := by ring

theorem bound_all (hs : ∀ i u v, ⟪X i u, v⟫_ℂ = -⟪u, X i v⟫_ℂ) (c : ι → ι → ι → ℝ)
    (hc : ∀ i j, X i * X j - X j * X i = ∑ k, (c i j k : ℂ) • X k) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u, bsum X m u ≤ C * qsum X m u := by
  have : (∃ C : ℝ, 0 ≤ C ∧ ∀ u, bsum X m u ≤ C * qsum X m u) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ u, bsum X (m + 1) u ≤ C * qsum X (m + 1) u := by
    induction m with
    | zero => exact ⟨bound_zero X, bound_one X hs⟩
    | succ m ih => exact ⟨ih.2, bound_step X hs c hc m ih.1 ih.2⟩
  exact this.1

theorem algEst : PositivityTheory.RgBcC.AlgEst := by
  intro V ι _ _ _ X c hs hc w
  obtain ⟨C, hC, h⟩ := bound_all X hs c hc w.length
  refine ⟨C, fun u => (norm_le_bsum X w rfl u).trans ((h u).trans (le_of_eq ?_))⟩
  rfl

end GlobalTheory.CompanionTheory.SkewWords
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraEstimateForRegularityStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebra_estimate_for_regularity : PositivityTheory.RgBcC.AlgEst := by
  first | exact @GlobalTheory.CompanionTheory.SkewWords.algEst | exact GlobalTheory.CompanionTheory.SkewWords.algEst | (intros; apply GlobalTheory.CompanionTheory.SkewWords.algEst <;> assumption)
end
end

namespace PositivityTheory.RgBcC

theorem wave_existence_speed_multiplicity : WaveEx ∧ WaveSpeed ∧ KerEx ∧ MultAlg := by
  have hL : LgFacts := GlobalTheory.T.length_function_facts_hold
  have hU : Unimod := GlobalTheory.T.general_linear_group_unimodular
  have hS : SobG := GlobalTheory.T.sobolev_inequality_on_group
  have hR : RCalc := GlobalTheory.T.right_derivative_calculus_holds
  have hKU : KerUniq := GlobalTheory.T.wave_kernel_uniqueness
  have hA : AlgEst := GlobalTheory.T.algebra_estimate_for_regularity
  have hsp : WaveSpeed := GlobalTheory.T.finite_propagation_speed_holds hL hU hR
  have hcpt : WaveCpt := Fc.asmCpt hL hU hR hS
  have hex : WaveEx := GlobalTheory.T.wave_solution_existence hL hR hsp hcpt
  have hk1 : KerOne := Fc.asmKerOne hL hU hR hS hA hsp
  exact ⟨hex, hsp, GlobalTheory.T.wave_kernel_existence hL hR hsp hex hKU hk1,
    GlobalTheory.CompanionTheory.WaveMult.asmMult_main hL hU hR hsp hex hKU hk1⟩

end PositivityTheory.RgBcC
