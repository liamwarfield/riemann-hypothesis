module

public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.SchurEigenProjections.EigA
public import Development.WeilBound.CoreStatements.BranchingTraces.HilbertSchmidtTraces.UnitaryMatrixCoefficientDecay

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableMulInner
noncomputable section

open MeasureTheory GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.RgHeA

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [SecondCountableTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ]
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem integrable_smul_rep {ν : Measure Γ} {τ : Γ → (H →L[ℂ] H)} (hτ : IsU τ) {f : Γ → ℂ} (hf : Integrable f ν) (b : H) :
    Integrable (fun g => f g • τ g b) ν := by
  refine (hf.norm.mul_const ‖b‖).mono' (hf.aestronglyMeasurable.smul (hτ.4 b).aestronglyMeasurable)
    (.of_forall fun g => ?_)
  rw [norm_smul, hτ.norm]

theorem integrable_mul_inner {ν : Measure Γ} {τ : Γ → (H →L[ℂ] H)} (hτ : IsU τ) {f : Γ → ℂ} (hf : Integrable f ν) (a b : H) :
    Integrable (fun g => f g * ⟪a, τ g b⟫_ℂ) ν := by
  refine (hf.norm.mul_const (‖a‖ * ‖b‖)).mono'
    (hf.aestronglyMeasurable.mul (continuous_const.inner (hτ.4 b)).aestronglyMeasurable)
    (.of_forall fun g => ?_)
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  calc ‖⟪a, τ g b⟫_ℂ‖ ≤ ‖a‖ * ‖τ g b‖ := norm_inner_le_norm _ _
    _ = ‖a‖ * ‖b‖ := by rw [hτ.norm]

def coefOp (ν : Measure Γ) (τ : Γ → (H →L[ℂ] H)) (hτ : IsU τ) (f : Γ → ℂ) (hf : Integrable f ν) : H →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun := fun b => ∫ g, f g • τ g b ∂ν
      map_add' := fun x y => by
        rw [← integral_add (integrable_smul_rep hτ hf x) (integrable_smul_rep hτ hf y)]
        simp only [map_add (f := _), smul_add]
      map_smul' := fun c x => by
        simp only [RingHom.id_apply]
        rw [← integral_smul]
        simp only [map_smul, smul_comm c] }
    (∫ g, ‖f g‖ ∂ν) fun b => by
      refine (norm_integral_le_of_norm_le (hf.norm.mul_const ‖b‖) (.of_forall fun g => ?_)).trans_eq ?_
      · rw [norm_smul, hτ.norm]
      · rw [integral_mul_const]

theorem coefOp_apply (ν : Measure Γ) (τ : Γ → (H →L[ℂ] H)) (hτ : IsU τ) (f : Γ → ℂ) (hf : Integrable f ν) (b : H) :
    coefOp ν τ hτ f hf b = ∫ g, f g • τ g b ∂ν := rfl

theorem inner_coefOp (ν : Measure Γ) (τ : Γ → (H →L[ℂ] H)) (hτ : IsU τ) (f : Γ → ℂ) (hf : Integrable f ν) (a b : H) :
    ⟪a, coefOp ν τ hτ f hf b⟫_ℂ = ∫ g, f g * ⟪a, τ g b⟫_ℂ ∂ν := by
  rw [coefOp_apply, ← integral_inner (integrable_smul_rep hτ hf b)]
  simp only [inner_smul_right]

end GlobalTheory.CompanionTheory.RgHeA
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalDegreeSchurOrthogonality
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalDegreeSchurOrthogonality
noncomputable section

open MeasureTheory GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods GlobalTheory.CompanionTheory.RgHeA
open scoped InnerProductSpace ComplexConjugate

namespace GlobalTheory.CompanionTheory.RgHeA

private theorem avg_conj_coef_ge_lemma {Γ : Type} [Group Γ] [TopologicalSpace Γ] {B : Type}
    [NormedAddCommGroup B] [InnerProductSpace ℂ B] {ρ : Γ → (B →L[ℂ] B)} (hρ : IsU ρ)
    (g : Γ) (x y : B) : ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ :=
  (⟨(ρ g : B →ₗ[ℂ] B), hρ.norm g⟩ : B →ₗᵢ[ℂ] B).inner_map_map x y

private theorem avg_conj_coef_ge_lemma_2 {Γ : Type} [Group Γ] [TopologicalSpace Γ] {B : Type}
    [NormedAddCommGroup B] [InnerProductSpace ℂ B] {ρ : Γ → (B →L[ℂ] B)} (hρ : IsU ρ)
    (g h : Γ) (x : B) : ρ g (ρ h x) = ρ (g * h) x := by
  rw [hρ.mul]; rfl

private theorem avg_conj_coef_ge_lemma_3 {Γ : Type} [Group Γ] [TopologicalSpace Γ] {B : Type}
    [NormedAddCommGroup B] [InnerProductSpace ℂ B] {ρ : Γ → (B →L[ℂ] B)} (hρ : IsU ρ)
    (g : Γ) (x y : B) : ⟪ρ g x, y⟫_ℂ = ⟪x, ρ g⁻¹ y⟫_ℂ := by
  have e : y = ρ g (ρ g⁻¹ y) := by
    rw [avg_conj_coef_ge_lemma_2 hρ, mul_inv_cancel, hρ.one]; rfl
  conv_lhs => rw [e]
  exact avg_conj_coef_ge_lemma hρ g x _

theorem avg_conj_coef_ge : ∀ {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [LocallyCompactSpace Γ]
    [SecondCountableTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ] (ν : Measure Γ) [ν.IsHaarMeasure] [ν.IsMulRightInvariant] {A B : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A] [NormedAddCommGroup B]
    [InnerProductSpace ℂ B] [CompleteSpace B] (σ : Γ → (A →L[ℂ] A)) (ρ : Γ → (B →L[ℂ] B)) (d : ℝ) (hσ : IsU σ) (hρ : IsU ρ), IsFd ν σ d →
    ∀ w₀ : A, ‖w₀‖ = 1 → ∀ (hc : Integrable (fun g => star ⟪w₀, σ g w₀⟫_ℂ) ν) (i : A →L[ℂ] B), IsIsoMap σ ρ i → ∀ z : B,
    ‖⟪z, i w₀⟫_ℂ‖ ^ 2 / d ≤ (⟪z, coefOp ν ρ hρ (fun g => star ⟪w₀, σ g w₀⟫_ℂ) hc z⟫_ℂ).re := by
  intro Γ _ _ _ _ _ _ _ ν _ _ A B _ _ _ _ _ _ σ ρ d hσ hρ hFd w₀ hw₀ hc i hi z
  obtain ⟨hd, hFd'⟩ := hFd
  have hmap : ∀ g x, i (σ g x) = ρ g (i x) := hi.1
  have hiso : ∀ x, ‖i x‖ = ‖x‖ := hi.2
  set f : Γ → ℂ := fun g => star ⟪w₀, σ g w₀⟫_ℂ with hf
  set T := coefOp ν ρ hρ f hc with hT
  have hw1 : ⟪w₀, w₀⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hw₀]; simp
  set a := ContinuousLinearMap.adjoint i z with ha
  have hA : ⟪i w₀, T z⟫_ℂ = ⟪i w₀, z⟫_ℂ / (d : ℂ) := by
    rw [hT, inner_coefOp]
    have hpt : ∀ g, f g * ⟪i w₀, ρ g z⟫_ℂ = ⟪w₀, σ g a⟫_ℂ * star ⟪w₀, σ g w₀⟫_ℂ := by
      intro g
      have e1 : ⟪i w₀, ρ g z⟫_ℂ = ⟪w₀, σ g a⟫_ℂ := by
        calc ⟪i w₀, ρ g z⟫_ℂ = ⟪ρ g⁻¹ (i w₀), z⟫_ℂ := by
              rw [avg_conj_coef_ge_lemma_3 hρ, inv_inv]
          _ = ⟪i (σ g⁻¹ w₀), z⟫_ℂ := by rw [hmap]
          _ = ⟪σ g⁻¹ w₀, a⟫_ℂ := by rw [ha, ContinuousLinearMap.adjoint_inner_right]
          _ = ⟪w₀, σ g a⟫_ℂ := by rw [avg_conj_coef_ge_lemma_3 hσ, inv_inv]
      rw [e1, hf, mul_comm]
    simp_rw [hpt]
    rw [(hFd' a w₀ w₀ w₀).2, hw1, mul_one, ha, ContinuousLinearMap.adjoint_inner_right]
  have hB1 : ∀ g, ⟪ρ g z, T z⟫_ℂ = ∫ k, f (g * k) * ⟪z, ρ k z⟫_ℂ ∂ν := by
    intro g
    rw [hT, inner_coefOp]
    have e : ∀ h, f h * ⟪ρ g z, ρ h z⟫_ℂ = f (g * (g⁻¹ * h)) * ⟪z, ρ (g⁻¹ * h) z⟫_ℂ := by
      intro h
      rw [mul_inv_cancel_left, avg_conj_coef_ge_lemma_3 hρ, avg_conj_coef_ge_lemma_2 hρ]
    simp_rw [e]
    exact integral_mul_left_eq_self (fun k => f (g * k) * ⟪z, ρ k z⟫_ℂ) g⁻¹
  set φ : Γ → ℂ := fun k => ⟪z, ρ k z⟫_ℂ with hφ
  have hfc : Continuous f := (continuous_const.inner (hσ.cont w₀)).star
  have hφc : Continuous φ := continuous_const.inner (hρ.cont z)
  have hφb : ∀ k, ‖φ k‖ ≤ ‖z‖ ^ 2 := by
    intro k
    calc ‖φ k‖ ≤ ‖z‖ * ‖ρ k z‖ := norm_inner_le_norm _ _
      _ = ‖z‖ ^ 2 := by rw [hρ.norm, sq]
  have hcs : Integrable (fun g => star (f g)) ν :=
    hc.mono (hfc.star.aestronglyMeasurable) (ae_of_all _ fun g => by rw [norm_star])
  have hG : Integrable (fun p : Γ × Γ => f p.1 * star (f (p.1 * p.2))) (ν.prod ν) := by
    have h0 : Integrable (fun p : Γ × Γ => f p.1 * star (f p.2)) (ν.prod ν) := hc.mul_prod hcs
    exact (measurePreserving_prod_mul ν ν).integrable_comp_of_integrable h0
  have hF : Integrable (Function.uncurry fun g k => f g * (star (f (g * k)) * star (φ k))) (ν.prod ν) := by
    refine Integrable.mono' (hG.norm.mul_const (‖z‖ ^ 2)) ?_ (ae_of_all _ fun p => ?_)
    · exact (show Continuous (fun p : Γ × Γ => f p.1 * (star (f (p.1 * p.2)) * star (φ p.2))) from
        (hfc.comp continuous_fst).mul (((hfc.comp (continuous_fst.mul continuous_snd)).star).mul
          ((hφc.comp continuous_snd).star))).aestronglyMeasurable
    · show ‖f p.1 * (star (f (p.1 * p.2)) * star (φ p.2))‖ ≤ ‖f p.1 * star (f (p.1 * p.2))‖ * ‖z‖ ^ 2
      simp only [norm_mul, norm_star]
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hφb _) (norm_nonneg _)) (norm_nonneg _)
  have hinner : ∀ k, ∫ g, f g * star (f (g * k)) ∂ν = star (f k) / (d : ℂ) := by
    intro k
    have e : ∀ g, f g * star (f (g * k)) = ⟪w₀, σ g (σ k w₀)⟫_ℂ * star ⟪w₀, σ g w₀⟫_ℂ := by
      intro g
      simp only [hf, star_star]
      rw [← avg_conj_coef_ge_lemma_2 hσ]
      ring
    simp_rw [e]
    rw [(hFd' (σ k w₀) w₀ w₀ w₀).2, hw1, mul_one]
    simp only [hf, star_star]
  have hB2 : ⟪T z, T z⟫_ℂ = star ⟪z, T z⟫_ℂ / (d : ℂ) := by
    have s1 : ⟪T z, T z⟫_ℂ = ∫ g, f g * ⟪T z, ρ g z⟫_ℂ ∂ν := inner_coefOp ν ρ hρ f hc (T z) z
    have s2 : ∀ g, f g * ⟪T z, ρ g z⟫_ℂ = ∫ k, f g * (star (f (g * k)) * star (φ k)) ∂ν := by
      intro g
      rw [← inner_conj_symm, hB1 g, ← integral_conj, ← integral_const_mul]
      simp only [map_mul, starRingEnd_apply, hφ]
    have s3 : ∀ k, ∫ g, f g * (star (f (g * k)) * star (φ k)) ∂ν = star (f k) / (d : ℂ) * star (φ k) := by
      intro k
      simp_rw [← mul_assoc]
      rw [integral_mul_const, hinner k]
    have s4 : ⟪z, T z⟫_ℂ = ∫ k, f k * φ k ∂ν := inner_coefOp ν ρ hρ f hc z z
    have s5 : ∀ k, star (f k) / (d : ℂ) * star (φ k) = (starRingEnd ℂ) (f k * φ k) / (d : ℂ) := by
      intro k
      rw [map_mul, starRingEnd_apply, starRingEnd_apply]
      ring
    rw [s1]
    simp_rw [s2]
    rw [integral_integral_swap hF]
    simp_rw [s3, s5]
    rw [integral_div, integral_conj, ← s4, starRingEnd_apply]
  have hTn : ⟪T z, T z⟫_ℂ = ((‖T z‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hX : star ⟪z, T z⟫_ℂ = ((d * ‖T z‖ ^ 2 : ℝ) : ℂ) := by
    have h := hB2.symm.trans hTn
    rw [div_eq_iff hdC] at h
    rw [h]
    push_cast
    ring
  have hre : (⟪z, T z⟫_ℂ).re = d * ‖T z‖ ^ 2 := by
    have h := congrArg Complex.re hX
    rw [Complex.ofReal_re] at h
    rw [← h]
    exact (Complex.conj_re _).symm
  have hle : ‖⟪z, i w₀⟫_ℂ‖ ≤ d * ‖T z‖ := by
    have h1' : ‖⟪i w₀, T z⟫_ℂ‖ ≤ ‖T z‖ := by
      calc ‖⟪i w₀, T z⟫_ℂ‖ ≤ ‖i w₀‖ * ‖T z‖ := norm_inner_le_norm _ _
        _ = ‖T z‖ := by rw [hiso, hw₀, one_mul]
    have h2' : ‖⟪z, i w₀⟫_ℂ‖ = d * ‖⟪i w₀, T z⟫_ℂ‖ := by
      rw [hA, norm_div, norm_inner_symm, Complex.norm_real, Real.norm_of_nonneg hd.le]
      field_simp
    rw [h2']
    exact mul_le_mul_of_nonneg_left h1' hd.le
  rw [hre, div_le_iff₀ hd]
  have hsq : ‖⟪z, i w₀⟫_ℂ‖ ^ 2 ≤ (d * ‖T z‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
  nlinarith [hsq]

end GlobalTheory.CompanionTheory.RgHeA
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalDegreeSchurOrthogonalityStatement
open MeasureTheory GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods GlobalTheory.CompanionTheory.RgHeA
open scoped InnerProductSpace ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formal_degree_schur_lower_bound : ∀ {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [LocallyCompactSpace Γ]
    [SecondCountableTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ] (ν : Measure Γ) [ν.IsHaarMeasure] [ν.IsMulRightInvariant] {A B : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A] [NormedAddCommGroup B]
    [InnerProductSpace ℂ B] [CompleteSpace B] (σ : Γ → (A →L[ℂ] A)) (ρ : Γ → (B →L[ℂ] B)) (d : ℝ) (hσ : IsU σ) (hρ : IsU ρ), IsFd ν σ d →
    ∀ w₀ : A, ‖w₀‖ = 1 → ∀ (hc : Integrable (fun g => star ⟪w₀, σ g w₀⟫_ℂ) ν) (i : A →L[ℂ] B), IsIsoMap σ ρ i → ∀ z : B,
    ‖⟪z, i w₀⟫_ℂ‖ ^ 2 / d ≤ (⟪z, coefOp ν ρ hρ (fun g => star ⟪w₀, σ g w₀⟫_ℂ) hc z⟫_ℂ).re := by
  first | exact @GlobalTheory.CompanionTheory.RgHeA.avg_conj_coef_ge | exact GlobalTheory.CompanionTheory.RgHeA.avg_conj_coef_ge | (intros; apply GlobalTheory.CompanionTheory.RgHeA.avg_conj_coef_ge <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalDegreeMatrixCoefficientNorm
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalDegreeMatrixCoefficientNorm
open MeasureTheory GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods GlobalTheory.CompanionTheory.RgHeA
open scoped InnerProductSpace ComplexConjugate ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.RgHeA.CoefHS

section SlopeTestRemainingChoices

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [SecondCountableTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ]
  {ν : Measure Γ} {A B : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B]

theorem memLp_coef {σ : Γ → (A →L[ℂ] A)} (hσ : IsU σ) {d : ℝ} (hd : IsFd ν σ d) (w v : A) :
    MemLp (fun g => ⟪w, σ g v⟫_ℂ) 2 ν := by
  have hm : AEStronglyMeasurable (fun g => ⟪w, σ g v⟫_ℂ) ν :=
    (continuous_const.inner (hσ.cont v)).aestronglyMeasurable
  refine (memLp_two_iff_integrable_sq_norm hm).2 ?_
  refine ((hd.2 v w v w).1.norm).congr (.of_forall fun g => ?_)
  simp only [norm_mul, norm_star, sq]

theorem memLp_diag {ρ : Γ → (B →L[ℂ] B)} (hρ : IsU ρ) (v : B)
    (hm : Integrable (fun g => star ⟪v, ρ g v⟫_ℂ) ν) : MemLp (fun g => ⟪v, ρ g v⟫_ℂ) 2 ν := by
  have hc : Continuous fun g => ⟪v, ρ g v⟫_ℂ := continuous_const.inner (hρ.cont v)
  refine (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).2 ?_
  refine (hm.norm.mul_const (‖v‖ * ‖v‖)).mono' (hc.norm.pow 2).aestronglyMeasurable (.of_forall fun g => ?_)
  have h1 : ‖⟪v, ρ g v⟫_ℂ‖ ≤ ‖v‖ * ‖v‖ := (norm_inner_le_norm _ _).trans (by rw [hρ.norm])
  rw [Real.norm_of_nonneg (by positivity), norm_star, sq]
  exact mul_le_mul_of_nonneg_left h1 (norm_nonneg _)

theorem inner_toLp {f g : Γ → ℂ} (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
    ⟪hf.toLp f, hg.toLp g⟫_ℂ = ∫ x, star (f x) * g x ∂ν := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
  rw [h1, h2]
  simp [RCLike.inner_apply, mul_comm]

theorem orthonormal_coef {σ : Γ → (A →L[ℂ] A)} (hσ : IsU σ) {d : ℝ} (hd : IsFd ν σ d) {ι : Type*} {e : ι → A}
    (he : Orthonormal ℂ e) :
    Orthonormal ℂ fun p : ι × ι => ((√d : ℝ) : ℂ) • (memLp_coef hσ hd (e p.1) (e p.2)).toLp _ := by
  classical
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.1.ne'
  have hs : conj ((√d : ℝ) : ℂ) * ((√d : ℝ) : ℂ) = d := by
    rw [Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt hd.1.le]
  rw [orthonormal_iff_ite]
  rintro ⟨k, l⟩ ⟨k', l'⟩
  rw [inner_smul_left, inner_smul_right, ← mul_assoc, hs, inner_toLp]
  have h := (hd.2 (e l') (e k') (e l) (e k)).2
  have h2 : ∫ x, star ⟪e k, σ x (e l)⟫_ℂ * ⟪e k', σ x (e l')⟫_ℂ ∂ν =
      ⟪e l, e l'⟫_ℂ * ⟪e k', e k⟫_ℂ / (d : ℂ) := by
    rw [← h]
    exact integral_congr_ae (.of_forall fun x => mul_comm _ _)
  simp only []
  rw [h2, orthonormal_iff_ite.1 he l l', orthonormal_iff_ite.1 he k' k]
  by_cases h1 : k = k' <;> by_cases h3 : l = l' <;> simp [h1, h3, hd0, eq_comm]

end SlopeTestRemainingChoices

theorem isHilbertSchmidt_coefOp : ∀ {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [LocallyCompactSpace Γ]
    [SecondCountableTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ] (ν : Measure Γ) [ν.IsHaarMeasure] [ν.IsMulRightInvariant] {A B : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A] [NormedAddCommGroup B]
    [InnerProductSpace ℂ B] [CompleteSpace B] (σ : Γ → (A →L[ℂ] A)) (ρ : Γ → (B →L[ℂ] B)) (d : ℝ) (hσ : IsU σ), IsU ρ → IsFd ν σ d →
    ∀ (v : B) (hm : Integrable (fun g => star ⟪v, ρ g v⟫_ℂ) ν),
    GroundTheory.Automorphic.IsHilbertSchmidt (coefOp ν σ hσ (fun g => star ⟪v, ρ g v⟫_ℂ) hm) := by
  intro Γ _ _ _ _ _ _ _ ν _ _ A B _ _ _ _ _ _ σ ρ d hσ hρ hd v hm
  set T := coefOp ν σ hσ (fun g => star ⟪v, ρ g v⟫_ℂ) hm with hT
  let e := GroundTheory.Automorphic.stdHilbertBasis ℂ A
  have hX := memLp_diag hρ v hm
  have hon := orthonormal_coef hσ hd e.orthonormal
  have hsum := Orthonormal.inner_products_summable (hX.toLp _) hon
  have hsd : √d ^ 2 = d := Real.sq_sqrt hd.1.le
  have key : ∀ p : _ × _, ‖⟪e p.1, T (e p.2)⟫_ℂ‖ ^ 2 =
      d⁻¹ * ‖⟪((√d : ℝ) : ℂ) • (memLp_coef hσ hd (e p.1) (e p.2)).toLp _, hX.toLp _⟫_ℂ‖ ^ 2 := by
    intro p
    have h1 : ⟪e p.1, T (e p.2)⟫_ℂ = ⟪hX.toLp _, (memLp_coef hσ hd (e p.1) (e p.2)).toLp _⟫_ℂ := by
      rw [hT, inner_coefOp, inner_toLp]
    rw [h1, inner_smul_left, norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      mul_pow, hsd, norm_inner_symm, ← mul_assoc, inv_mul_cancel₀ hd.1.ne', one_mul]
  have hs2 : Summable fun p : _ × _ => ‖⟪e p.1, T (e p.2)⟫_ℂ‖ ^ 2 := by
    simp_rw [key]
    exact hsum.mul_left _
  rw [GroundTheory.Automorphic.isHilbertSchmidt_iff e]
  have h3 : ∑' l, ‖T (e l)‖ₑ ^ 2 = ∑' p : _ × _, ENNReal.ofReal (‖⟪e p.1, T (e p.2)⟫_ℂ‖ ^ 2) := by
    simp_rw [GroundTheory.Automorphic.enorm_sq_eq_tsum e (T _)]
    rw [ENNReal.tsum_comm, ← ENNReal.tsum_prod]
    refine tsum_congr fun p => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  rw [h3]
  exact hs2.tsum_ofReal_lt_top

end GlobalTheory.CompanionTheory.RgHeA.CoefHS

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalDegreeMatrixCoefficientNormStatement
open MeasureTheory GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods GlobalTheory.CompanionTheory.RgHeA
open scoped InnerProductSpace ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formal_degree_matrix_coefficient_norm : ∀ {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [LocallyCompactSpace Γ]
    [SecondCountableTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ] (ν : Measure Γ) [ν.IsHaarMeasure] [ν.IsMulRightInvariant] {A B : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A] [NormedAddCommGroup B]
    [InnerProductSpace ℂ B] [CompleteSpace B] (σ : Γ → (A →L[ℂ] A)) (ρ : Γ → (B →L[ℂ] B)) (d : ℝ) (hσ : IsU σ), IsU ρ → IsFd ν σ d →
    ∀ (v : B) (hm : Integrable (fun g => star ⟪v, ρ g v⟫_ℂ) ν),
    GroundTheory.Automorphic.IsHilbertSchmidt (coefOp ν σ hσ (fun g => star ⟪v, ρ g v⟫_ℂ) hm) := by
  first | exact @GlobalTheory.CompanionTheory.RgHeA.CoefHS.isHilbertSchmidt_coefOp | exact GlobalTheory.CompanionTheory.RgHeA.CoefHS.isHilbertSchmidt_coefOp | (intros; apply GlobalTheory.CompanionTheory.RgHeA.CoefHS.isHilbertSchmidt_coefOp <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixCoefficientOrthogonalityRelation
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixCoefficientOrthogonalityRelation
open MeasureTheory GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods GlobalTheory.CompanionTheory.RgHeA
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace GlobalTheory.CompanionTheory.RgHeA

theorem isInvInvariant_of_right_haar {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [μ.IsHaarMeasure] [μ.IsMulRightInvariant] : μ.IsInvInvariant := by
  haveI : IsFiniteMeasureOnCompacts μ.inv :=
    ⟨fun K hK => by rw [Measure.inv_apply]; exact hK.inv.measure_lt_top⟩
  obtain ⟨c, hc⟩ : ∃ c : NNReal, μ.inv = c • μ := ⟨_, Measure.isMulLeftInvariant_eq_smul μ.inv μ⟩
  have hsq : μ = (c * c) • μ := by
    calc μ = μ.inv.inv := (Measure.inv_inv μ).symm
      _ = (c • μ).inv := by rw [hc]
      _ = c • μ.inv := by rw [Measure.inv_def, Measure.inv_def, Measure.map_smul c measurable_inv.aemeasurable]
      _ = (c * c) • μ := by rw [hc, smul_smul]
  let K := Classical.arbitrary (TopologicalSpace.PositiveCompacts G)
  have hpos : μ K ≠ 0 := (Measure.measure_pos_of_nonempty_interior μ K.interior_nonempty).ne'
  have hfin : μ K ≠ ⊤ := K.isCompact.measure_lt_top.ne
  have hK : μ K = ((c * c) • μ) K := by rw [← hsq]
  rw [Measure.smul_apply, Measure.nnreal_smul_coe_apply] at hK
  have h1 : ((c * c : NNReal) : ENNReal) = 1 :=
    ((ENNReal.mul_left_inj hpos hfin).1 (by rw [one_mul]; exact hK.symm))
  have hcc : (c : ℝ) * c = 1 := by exact_mod_cast ENNReal.coe_eq_one.1 h1
  have hc1 : c = 1 := by
    have : (c : ℝ) = 1 := by nlinarith [c.coe_nonneg]
    exact_mod_cast this
  exact ⟨by rw [hc, hc1, one_smul]⟩

theorem isSelfAdjoint_coefOp : ∀ {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [LocallyCompactSpace Γ]
    [SecondCountableTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ] (ν : Measure Γ) [ν.IsHaarMeasure] [ν.IsMulRightInvariant] {A B : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A] [NormedAddCommGroup B]
    [InnerProductSpace ℂ B] [CompleteSpace B] (σ : Γ → (A →L[ℂ] A)) (ρ : Γ → (B →L[ℂ] B)) (hσ : IsU σ), IsU ρ → ∀ (v : B) (hm : Integrable (fun g => star ⟪v, ρ g v⟫_ℂ) ν),
    IsSelfAdjoint (coefOp ν σ hσ (fun g => star ⟪v, ρ g v⟫_ℂ) hm) := by
  intro Γ _ _ _ _ _ _ _ ν _ _ A B _ _ _ _ _ _ σ ρ hσ hρ v hm
  haveI := GlobalTheory.CompanionTheory.RgHeA.isInvInvariant_of_right_haar ν
  obtain ⟨_, hadj, _, _⟩ := PositivityTheory.UnitaryDecomposition.X4.uRep_of hσ
  obtain ⟨_, hρadj, _, _⟩ := PositivityTheory.UnitaryDecomposition.X4.uRep_of hρ
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro a b
  try simp only [ContinuousLinearMap.coe_coe]
  rw [← inner_conj_symm, GlobalTheory.CompanionTheory.RgHeA.inner_coefOp, GlobalTheory.CompanionTheory.RgHeA.inner_coefOp, ← integral_conj]
  calc ∫ g, (starRingEnd ℂ) (star ⟪v, ρ g v⟫_ℂ * ⟪b, σ g a⟫_ℂ) ∂ν
      = ∫ g, star ⟪v, ρ g⁻¹ v⟫_ℂ * ⟪a, σ g⁻¹ b⟫_ℂ ∂ν := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
        have e1 : star ⟪v, ρ g⁻¹ v⟫_ℂ = ⟪v, ρ g v⟫_ℂ := by
          rw [← hρadj]
          exact inner_conj_symm _ _
        have e2 : (starRingEnd ℂ) ⟪b, σ g a⟫_ℂ = ⟪a, σ g⁻¹ b⟫_ℂ := by
          rw [inner_conj_symm, hadj]
        show (starRingEnd ℂ) (star ⟪v, ρ g v⟫_ℂ * ⟪b, σ g a⟫_ℂ) = star ⟪v, ρ g⁻¹ v⟫_ℂ * ⟪a, σ g⁻¹ b⟫_ℂ
        rw [map_mul, e1, e2, starRingEnd_apply, star_star]
    _ = ∫ g, star ⟪v, ρ g v⟫_ℂ * ⟪a, σ g b⟫_ℂ ∂ν :=
        integral_inv_eq_self (fun g => star ⟪v, ρ g v⟫_ℂ * ⟪a, σ g b⟫_ℂ) ν

end GlobalTheory.CompanionTheory.RgHeA
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixCoefficientOrthogonalityRelationStatement
open MeasureTheory GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods GlobalTheory.CompanionTheory.RgHeA
open scoped InnerProductSpace ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_coefficient_orthogonality_relation : ∀ {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [LocallyCompactSpace Γ]
    [SecondCountableTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ] (ν : Measure Γ) [ν.IsHaarMeasure] [ν.IsMulRightInvariant] {A B : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A] [NormedAddCommGroup B]
    [InnerProductSpace ℂ B] [CompleteSpace B] (σ : Γ → (A →L[ℂ] A)) (ρ : Γ → (B →L[ℂ] B)) (hσ : IsU σ), IsU ρ → ∀ (v : B) (hm : Integrable (fun g => star ⟪v, ρ g v⟫_ℂ) ν),
    IsSelfAdjoint (coefOp ν σ hσ (fun g => star ⟪v, ρ g v⟫_ℂ) hm) := by
  first | exact @GlobalTheory.CompanionTheory.RgHeA.isSelfAdjoint_coefOp | exact GlobalTheory.CompanionTheory.RgHeA.isSelfAdjoint_coefOp | (intros; apply GlobalTheory.CompanionTheory.RgHeA.isSelfAdjoint_coefOp <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CyclicVectorIntertwinerDetermined
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CyclicVectorIntertwinerDetermined
noncomputable section

open MeasureTheory GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods GlobalTheory.CompanionTheory.RgHeA
open scoped InnerProductSpace ComplexConjugate

namespace GlobalTheory.CompanionTheory.RgHeA

theorem lower_bound_of_cyclic_coef : ∀ {Γ : Type} [Group Γ] [TopologicalSpace Γ] {A B : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A] [NormedAddCommGroup B]
    [InnerProductSpace ℂ B] [CompleteSpace B] (σ : Γ → (A →L[ℂ] A)) (ρ : Γ → (B →L[ℂ] B)) (d : ℝ), 0 < d → IsU σ → IsU ρ →
    ∀ (w₀ : A) (v : B) (i : A →L[ℂ] B), IsMap σ ρ i → (Submodule.span ℂ (Set.range fun x => σ x w₀)).topologicalClosure = ⊤ →
    ∀ (T : A →L[ℂ] A) (E : B →L[ℂ] B), (∀ x y, ⟪σ x w₀, T (σ y w₀)⟫_ℂ = star ⟪ρ x⁻¹ v, E (ρ y⁻¹ v)⟫_ℂ) →
    (∀ z, ‖⟪z, i w₀⟫_ℂ‖ ^ 2 / d ≤ (⟪z, E z⟫_ℂ).re) → ∀ a, ‖⟪v, i a⟫_ℂ‖ ^ 2 / d ≤ (⟪a, T a⟫_ℂ).re := by
  intro Γ _ _ A B _ _ _ _ _ _ σ ρ d hd hσ hρ w₀ v i hi hcyc T E hTE hE a
  obtain ⟨h1, hmul, hnorm, -⟩ := hρ
  have hρinner : ∀ (g : Γ) (x y : B), ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ := fun g x y =>
    (LinearIsometry.mk (ρ g : B →ₗ[ℂ] B) (hnorm g)).inner_map_map x y
  have hadj : ∀ (g : Γ) (x y : B), ⟪ρ g⁻¹ x, y⟫_ℂ = ⟪x, ρ g y⟫_ℂ := by
    intro g x y
    rw [← hρinner g (ρ g⁻¹ x) y]
    congr 1
    rw [← ContinuousLinearMap.mul_apply, ← hmul, mul_inv_cancel, h1, ContinuousLinearMap.one_apply]
  have hi' : ∀ (g : Γ) (x : A), i (σ g x) = ρ g (i x) := hi
  have hTE' : ∀ x y, ⟪σ x w₀, T (σ y w₀)⟫_ℂ = starRingEnd ℂ ⟪ρ x⁻¹ v, E (ρ y⁻¹ v)⟫_ℂ :=
    fun x y => (hTE x y).trans (starRingEnd_apply _).symm
  have hclosed : IsClosed {a : A | ‖⟪v, i a⟫_ℂ‖ ^ 2 / d ≤ (⟪a, T a⟫_ℂ).re} := by
    apply isClosed_le
    · exact ((continuous_const.inner i.continuous).norm.pow 2).div_const d
    · exact Complex.continuous_re.comp (continuous_id.inner T.continuous)
  have hspan : (Submodule.span ℂ (Set.range fun x => σ x w₀) : Set A) ⊆
      {a : A | ‖⟪v, i a⟫_ℂ‖ ^ 2 / d ≤ (⟪a, T a⟫_ℂ).re} := by
    intro a ha
    rw [SetLike.mem_coe, Finsupp.mem_span_range_iff_exists_finsupp] at ha
    obtain ⟨c, rfl⟩ := ha
    set z : B := c.sum fun y t => starRingEnd ℂ t • ρ y⁻¹ v with hz
    have h1' : ⟪v, i (c.sum fun x t => t • σ x w₀)⟫_ℂ = ⟪z, i w₀⟫_ℂ := by
      rw [hz]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Finsupp.sum, map_sum, map_smul, inner_sum, sum_inner, inner_smul_right,
        inner_smul_left, hi', hadj, Complex.conj_conj, RCLike.conj_conj, starRingEnd_self_apply]
    have h2' : ⟪c.sum fun x t => t • σ x w₀, T (c.sum fun x t => t • σ x w₀)⟫_ℂ =
        starRingEnd ℂ ⟪z, E z⟫_ℂ := by
      rw [hz]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Finsupp.sum, map_sum, map_smul, inner_sum, sum_inner, inner_smul_right,
        inner_smul_left, hTE', map_mul, Complex.conj_conj, RCLike.conj_conj, starRingEnd_self_apply]
    rw [Set.mem_setOf_eq, h1', h2', Complex.conj_re]
    exact hE z
  have ha : a ∈ closure (Submodule.span ℂ (Set.range fun x => σ x w₀) : Set A) := by
    rw [← Submodule.topologicalClosure_coe, hcyc]
    simp
  exact closure_minimal hspan hclosed ha

end GlobalTheory.CompanionTheory.RgHeA
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CyclicVectorIntertwinerDeterminedStatement
open MeasureTheory GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods GlobalTheory.CompanionTheory.RgHeA
open scoped InnerProductSpace ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclic_vector_intertwiner_determined : ∀ {Γ : Type} [Group Γ] [TopologicalSpace Γ] {A B : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A] [NormedAddCommGroup B]
    [InnerProductSpace ℂ B] [CompleteSpace B] (σ : Γ → (A →L[ℂ] A)) (ρ : Γ → (B →L[ℂ] B)) (d : ℝ), 0 < d → IsU σ → IsU ρ →
    ∀ (w₀ : A) (v : B) (i : A →L[ℂ] B), IsMap σ ρ i → (Submodule.span ℂ (Set.range fun x => σ x w₀)).topologicalClosure = ⊤ →
    ∀ (T : A →L[ℂ] A) (E : B →L[ℂ] B), (∀ x y, ⟪σ x w₀, T (σ y w₀)⟫_ℂ = star ⟪ρ x⁻¹ v, E (ρ y⁻¹ v)⟫_ℂ) →
    (∀ z, ‖⟪z, i w₀⟫_ℂ‖ ^ 2 / d ≤ (⟪z, E z⟫_ℂ).re) → ∀ a, ‖⟪v, i a⟫_ℂ‖ ^ 2 / d ≤ (⟪a, T a⟫_ℂ).re := by
  first | exact @GlobalTheory.CompanionTheory.RgHeA.lower_bound_of_cyclic_coef | exact GlobalTheory.CompanionTheory.RgHeA.lower_bound_of_cyclic_coef | (intros; apply GlobalTheory.CompanionTheory.RgHeA.lower_bound_of_cyclic_coef <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixCoefficientIntertwinerAdjoint
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixCoefficientIntertwinerAdjoint
noncomputable section

open MeasureTheory GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods GlobalTheory.CompanionTheory.RgHeA
open scoped InnerProductSpace ComplexConjugate

namespace GlobalTheory.CompanionTheory.RgHeA.TwPf

section Unitary

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] {A : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A]
  {ρ : Γ → (A →L[ℂ] A)}

theorem inner_map_map (hU : IsU ρ) (g : Γ) (x y : A) : ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ := by
  obtain ⟨_, _, hnorm, _⟩ := hU
  let L : A →ₗᵢ[ℂ] A := ⟨(ρ g : A →ₗ[ℂ] A), hnorm g⟩
  exact L.inner_map_map x y

theorem map_mul_apply (hU : IsU ρ) (g h : Γ) (x : A) : ρ (g * h) x = ρ g (ρ h x) := by
  obtain ⟨_, hmul, _, _⟩ := hU
  rw [hmul, ContinuousLinearMap.mul_apply]

theorem inner_translate (hU : IsU ρ) (a g b : Γ) (u : A) :
    ⟪ρ a u, ρ g (ρ b u)⟫_ℂ = ⟪u, ρ (a⁻¹ * g * b) u⟫_ℂ := by
  have h : ρ g (ρ b u) = ρ a (ρ (a⁻¹ * g * b) u) := by
    rw [← GlobalTheory.CompanionTheory.RgHeA.TwPf.map_mul_apply hU, ← GlobalTheory.CompanionTheory.RgHeA.TwPf.map_mul_apply hU, show a * (a⁻¹ * g * b) = g * b by group]
  rw [h, GlobalTheory.CompanionTheory.RgHeA.TwPf.inner_map_map hU]

end Unitary

theorem coefOp_translate {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [LocallyCompactSpace Γ]
    [SecondCountableTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ] (ν : Measure Γ) [ν.IsHaarMeasure] [ν.IsMulRightInvariant] {A B : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A] [NormedAddCommGroup B]
    [InnerProductSpace ℂ B] [CompleteSpace B] (σ : Γ → (A →L[ℂ] A)) (ρ : Γ → (B →L[ℂ] B)) (hσ : IsU σ) (hρ : IsU ρ) (w₀ : A) (v : B)
    (hc : Integrable (fun g => star ⟪w₀, σ g w₀⟫_ℂ) ν) (hm : Integrable (fun g => star ⟪v, ρ g v⟫_ℂ) ν) (x y : Γ) :
    ⟪σ x w₀, coefOp ν σ hσ (fun g => star ⟪v, ρ g v⟫_ℂ) hm (σ y w₀)⟫_ℂ =
      star ⟪ρ x⁻¹ v, coefOp ν ρ hρ (fun g => star ⟪w₀, σ g w₀⟫_ℂ) hc (ρ y⁻¹ v)⟫_ℂ := by
  rw [GlobalTheory.CompanionTheory.RgHeA.inner_coefOp, GlobalTheory.CompanionTheory.RgHeA.inner_coefOp]
  simp_rw [GlobalTheory.CompanionTheory.RgHeA.TwPf.inner_translate hσ, GlobalTheory.CompanionTheory.RgHeA.TwPf.inner_translate hρ, inv_inv]
  have key : ∀ F : Γ → ℂ, ∫ g, F (x⁻¹ * g * y) ∂ν = ∫ g, F g ∂ν := fun F =>
    (integral_mul_left_eq_self (fun h => F (h * y)) x⁻¹).trans (integral_mul_right_eq_self F y)
  have hstar : star (∫ g, star ⟪w₀, σ g w₀⟫_ℂ * ⟪v, ρ (x * g * y⁻¹) v⟫_ℂ ∂ν) =
      ∫ g, ⟪w₀, σ g w₀⟫_ℂ * star ⟪v, ρ (x * g * y⁻¹) v⟫_ℂ ∂ν := by
    have h := (integral_conj (μ := ν)
      (f := fun g => star ⟪w₀, σ g w₀⟫_ℂ * ⟪v, ρ (x * g * y⁻¹) v⟫_ℂ)).symm
    simpa [map_mul] using h
  rw [hstar, ← key (fun g => ⟪w₀, σ g w₀⟫_ℂ * star ⟪v, ρ (x * g * y⁻¹) v⟫_ℂ)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  simp only [show x * (x⁻¹ * g * y) * y⁻¹ = g by group]
  exact mul_comm _ _

end GlobalTheory.CompanionTheory.RgHeA.TwPf
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixCoefficientIntertwinerAdjointStatement
open MeasureTheory GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods GlobalTheory.CompanionTheory.RgHeA
open scoped InnerProductSpace ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_coefficient_intertwiner_adjoint : ∀ {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [LocallyCompactSpace Γ]
    [SecondCountableTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ] (ν : Measure Γ) [ν.IsHaarMeasure] [ν.IsMulRightInvariant] {A B : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A] [NormedAddCommGroup B]
    [InnerProductSpace ℂ B] [CompleteSpace B] (σ : Γ → (A →L[ℂ] A)) (ρ : Γ → (B →L[ℂ] B)) (hσ : IsU σ) (hρ : IsU ρ) (w₀ : A) (v : B)
    (hc : Integrable (fun g => star ⟪w₀, σ g w₀⟫_ℂ) ν) (hm : Integrable (fun g => star ⟪v, ρ g v⟫_ℂ) ν) (x y : Γ),
    ⟪σ x w₀, coefOp ν σ hσ (fun g => star ⟪v, ρ g v⟫_ℂ) hm (σ y w₀)⟫_ℂ =
      star ⟪ρ x⁻¹ v, coefOp ν ρ hρ (fun g => star ⟪w₀, σ g w₀⟫_ℂ) hc (ρ y⁻¹ v)⟫_ℂ := by
  first | exact @GlobalTheory.CompanionTheory.RgHeA.TwPf.coefOp_translate | exact GlobalTheory.CompanionTheory.RgHeA.TwPf.coefOp_translate | (intros; apply GlobalTheory.CompanionTheory.RgHeA.TwPf.coefOp_translate <;> assumption)
end
end

noncomputable section

open MeasureTheory GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods PositivityTheory.RgHe.A
open scoped InnerProductSpace ComplexConjugate

namespace GlobalTheory.CompanionTheory.RgHeA

theorem integrable_star' {Γ : Type} [MeasurableSpace Γ] {ν : Measure Γ} {f : Γ → ℂ} (h : Integrable f ν) :
    Integrable (fun g => star (f g)) ν :=
  h.norm.mono' (continuous_star.comp_aestronglyMeasurable h.1) (.of_forall fun g => by simp)

theorem exists_eig_of_low {A : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A]
    (T : A →L[ℂ] A) (hT : IsCompactOperator T) (hT' : IsSelfAdjoint T) (w₀ : A) (hw₀ : w₀ ≠ 0) (p : A) (d : ℝ) (hd : 0 < d)
    (h : ∀ a, ‖⟪p, a⟫_ℂ‖ ^ 2 / d ≤ (⟪a, T a⟫_ℂ).re) :
    ∃ (w : A) (c : ℝ), w ≠ 0 ∧ ‖p‖ ^ 2 / (2 * d) ≤ c ∧ T w = (c : ℂ) • w := by
  obtain ⟨s, b, l, -, hTb0, hsum0, -⟩ := GroundTheory.Automorphic.CompactSelfAdjoint.exists_hilbertBasis_eigenvectors_hasSum hT hT'
  have hTb : ∀ i, T (b i) = ((l i : ℝ) : ℂ) • b i := hTb0
  have hsum : ∀ x, HasSum (fun i => (((l i : ℝ) : ℂ) * ⟪b i, x⟫_ℂ) • b i) (T x) := hsum0
  have hone : ∀ i, ⟪b i, b i⟫_ℂ = 1 := fun i => by
    rw [inner_self_eq_norm_sq_to_K, b.orthonormal.1 i]; simp
  have hli : ∀ i, 0 ≤ l i := fun i => by
    have h1 := h (b i)
    rw [hTb, inner_smul_right, hone, mul_one, Complex.ofReal_re] at h1
    exact le_trans (by positivity) h1
  by_contra hcon
  push_neg at hcon
  have hlt : ∀ i, l i < ‖p‖ ^ 2 / (2 * d) := fun i => by
    by_contra hh
    push_neg at hh
    exact hcon _ _ (b.orthonormal.ne_zero i) hh (hTb i)
  obtain ⟨i0⟩ : Nonempty s := by
    by_contra hE
    rw [not_nonempty_iff] at hE
    exact hw₀ (inner_self_eq_zero.1 ((b.hasSum_inner_mul_inner w₀ w₀).unique hasSum_empty))
  have hC : 0 < ‖p‖ ^ 2 / (2 * d) := (hli i0).trans_lt (hlt i0)
  have key : ∀ i, ⟪p, b i⟫_ℂ * ⟪b i, p⟫_ℂ = ((‖⟪p, b i⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := fun i => by
    rw [← inner_conj_symm (b i) p, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have key2 : ∀ i, ((l i : ℝ) : ℂ) * ⟪b i, p⟫_ℂ * ⟪p, b i⟫_ℂ = ((l i * ‖⟪p, b i⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := fun i => by
    rw [mul_assoc, mul_comm ⟪b i, p⟫_ℂ, key]; push_cast; ring
  have e : (⟪p, p⟫_ℂ).re = ‖p‖ ^ 2 := by simpa using inner_self_eq_norm_sq (𝕜 := ℂ) p
  have h1 : HasSum (fun i => ‖⟪p, b i⟫_ℂ‖ ^ 2) (‖p‖ ^ 2) := by
    have h0 := Complex.reCLM.hasSum (b.hasSum_inner_mul_inner p p)
    simp only [Complex.reCLM_apply, key, Complex.ofReal_re, e] at h0
    exact h0
  have h2 : HasSum (fun i => l i * ‖⟪p, b i⟫_ℂ‖ ^ 2) (⟪p, T p⟫_ℂ).re := by
    have h0 := Complex.reCLM.hasSum ((innerSL ℂ p).hasSum (hsum p))
    simp only [innerSL_apply_apply, inner_smul_right, Complex.reCLM_apply, key2, Complex.ofReal_re] at h0
    exact h0
  have h3 : (⟪p, T p⟫_ℂ).re ≤ ‖p‖ ^ 2 / (2 * d) * ‖p‖ ^ 2 :=
    hasSum_le (fun i => mul_le_mul_of_nonneg_right (hlt i).le (by positivity)) h2 (h1.mul_left (‖p‖ ^ 2 / (2 * d)))
  have h5 := h p
  have e2 : ‖⟪p, p⟫_ℂ‖ = ‖p‖ ^ 2 := by rw [inner_self_eq_norm_sq_to_K]; simp
  rw [e2] at h5
  have hP : 0 < ‖p‖ ^ 2 := by
    by_contra hh
    have : ‖p‖ ^ 2 = 0 := le_antisymm (not_lt.1 hh) (by positivity)
    rw [this] at hC
    simp at hC
  have e3 : ‖p‖ ^ 2 / (2 * d) * ‖p‖ ^ 2 = (‖p‖ ^ 2) ^ 2 / d / 2 := by field_simp
  have h6 : 0 < (‖p‖ ^ 2) ^ 2 / d := by positivity
  linarith

theorem eigA : EigA := by
  intro Γ _ _ _ _ _ _ _ ν _ _ A B _ _ _ _ _ _ σ ρ d hσ hρ hd w₀ hw₀ hc0 i hi v hm0
  have hm : Integrable (fun g => star ⟪v, ρ g v⟫_ℂ) ν := integrable_star' hm0
  have hc : Integrable (fun g => star ⟪w₀, σ g w₀⟫_ℂ) ν := integrable_star' hc0
  have hne : w₀ ≠ 0 := fun h => by simp [h] at hw₀
  have hdense : (Submodule.span ℂ (Set.range fun x => σ x w₀)).topologicalClosure = ⊤ := by
    rw [Submodule.topologicalClosure_eq_top_iff, eq_bot_iff]
    intro u hu
    refine PositivityTheory.UnitaryDecomposition.X4.eq_zero_of_orth hd hne fun g => ?_
    have hg : σ g w₀ ∈ Submodule.span ℂ (Set.range fun x => σ x w₀) := Submodule.subset_span ⟨g, rfl⟩
    exact Submodule.inner_left_of_mem_orthogonal hg hu
  have hlow := GlobalTheory.T.cyclic_vector_intertwiner_determined σ ρ d hd.1 hσ hρ w₀ v i hi.1 hdense
    (coefOp ν σ hσ (fun g => star ⟪v, ρ g v⟫_ℂ) hm) (coefOp ν ρ hρ (fun g => star ⟪w₀, σ g w₀⟫_ℂ) hc)
    (GlobalTheory.T.matrix_coefficient_intertwiner_adjoint ν σ ρ hσ hρ w₀ v hc hm) (GlobalTheory.T.formal_degree_schur_lower_bound ν σ ρ d hσ hρ hd w₀ hw₀ hc i hi)
  have hlow' : ∀ a, ‖⟪ContinuousLinearMap.adjoint i v, a⟫_ℂ‖ ^ 2 / d ≤
      (⟪a, coefOp ν σ hσ (fun g => star ⟪v, ρ g v⟫_ℂ) hm a⟫_ℂ).re := fun a => by
    rw [ContinuousLinearMap.adjoint_inner_left]
    exact hlow a
  obtain ⟨w, c, hw, hcb, hTw⟩ := exists_eig_of_low _ (GroundTheory.Automorphic.IsHilbertSchmidt.isCompactOperator
    (GlobalTheory.T.formal_degree_matrix_coefficient_norm ν σ ρ d hσ hρ hd v hm)) (GlobalTheory.T.matrix_coefficient_orthogonality_relation ν σ ρ hσ hρ v hm) w₀ hne _ d hd.1 hlow'
  refine ⟨w, c, hw, hcb, fun b => ⟨integrable_mul_inner hσ hm b w, ?_⟩⟩
  rw [← inner_coefOp ν σ hσ _ hm, hTw, inner_smul_right]

end GlobalTheory.CompanionTheory.RgHeA
