module

public import Formalism.SharpRestriction.CuspSpanNormBounds.SGauge

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ExpProdSt
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Metric Formalism.MainNotions.S Formalism.MainNotions.S.Gauge
open scoped Classical

def expR {n : ℕ} (ε : Fin n → Bool) (x : EuclideanSpace ℝ (Fin n × Fin n × Bool)) : Formalism.REAL.UJ ε :=
  if h : Formalism.REAL.inUJ ε (NormedSpace.exp (unrealify x)) then ⟨(Matrix.isUnit_exp (unrealify x)).unit, h⟩ else 1

def ExpProdU : Prop := ∀ (n : ℕ) (ε : Fin n → Bool) (m h : Submodule ℝ (EuclideanSpace ℝ (Fin n × Fin n × Bool))),
    m ⊔ h = gLie ε → (∀ x ∈ m, ∀ y ∈ h, inner ℝ x y = 0) →
    ∀ (ι η : Type) [Fintype ι] [Fintype η] (L₀ : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] m) (L₁ : EuclideanSpace ℝ η ≃ₗᵢ[ℝ] h),
    GaugeDens ε → ∃ r : ℝ, 0 < r ∧ ∃ D : EuclideanSpace ℝ ι × EuclideanSpace ℝ η → ℝ,
      ContinuousAt D 0 ∧ D 0 = gaugeU ε ∧ Measurable D ∧
      ∀ A ⊆ ball (0 : EuclideanSpace ℝ ι × EuclideanSpace ℝ η) r, MeasurableSet A →
        Formalism.REAL.muG ε ((fun p => expR ε (L₀ p.1 : EuclideanSpace ℝ (Fin n × Fin n × Bool)) *
          expR ε (L₁ p.2 : EuclideanSpace ℝ (Fin n × Fin n × Bool))) '' A) =
        ∫⁻ p in A, ENNReal.ofReal (D p)

end PI.AprimeInfW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ChartChg
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology

theorem chart_change {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] {Y : Type} [MeasurableSpace Y]
    (m : Measure Y) (χ : E → Y) (V : Set E) (f : E → ℝ)
    (hχ : ∀ S ⊆ V, MeasurableSet S → m (χ '' S) = ∫⁻ x in S, ENNReal.ofReal (f x) ∂μ)
    (ψ : E → E) (ψ' : E → E →L[ℝ] E) (U : Set E) (hψ : ∀ x ∈ U, HasFDerivWithinAt ψ (ψ' x) U x)
    (hinj : Set.InjOn ψ U) (hψV : ψ '' U ⊆ V) (A : Set E) (hAU : A ⊆ U) (hA : MeasurableSet A) :
    m ((χ ∘ ψ) '' A) = ∫⁻ p in A, ENNReal.ofReal (|(ψ' p).det| * f (ψ p)) ∂μ := by
  have hd : ∀ x ∈ A, HasFDerivWithinAt ψ (ψ' x) A x := fun x hx => (hψ x (hAU hx)).mono hAU
  have hinjA : Set.InjOn ψ A := hinj.mono hAU
  have hmeas : MeasurableSet (ψ '' A) := measurable_image_of_fderivWithin hA hd hinjA
  rw [Set.image_comp, hχ _ ((Set.image_mono hAU).trans hψV) hmeas,
    lintegral_image_eq_lintegral_abs_det_fderiv_mul μ hA hd hinjA]
  refine lintegral_congr fun p => ?_
  rw [ENNReal.ofReal_mul (abs_nonneg _)]

theorem chart_change_cont {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (f : E → ℝ) (ψ : E → E) (ψ' : E → E →L[ℝ] E) (x₀ : E) (hψ : ContinuousAt ψ x₀)
    (hf : ContinuousAt f (ψ x₀)) (hd : ContinuousAt (fun p => (ψ' p).det) x₀) :
    ContinuousAt (fun p => |(ψ' p).det| * f (ψ p)) x₀ := (continuous_abs.continuousAt.comp hd).mul (hf.comp hψ)

end PI.AprimeInfW
end
end

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Metric Formalism.MainNotions.S Formalism.MainNotions.S.Gauge
open scoped Classical

def cayR {n : ℕ} (ε : Fin n → Bool) (x : EuclideanSpace ℝ (Fin n × Fin n × Bool)) : Formalism.REAL.UJ ε :=
  if h : IsUnit ((2 + unrealify x) * (2 - unrealify x)⁻¹) ∧ Formalism.REAL.inUJ ε ((2 + unrealify x) * (2 - unrealify x)⁻¹)
  then ⟨h.1.unit, h.2⟩ else 1

def CayProdU : Prop := ∀ (n : ℕ) (ε : Fin n → Bool) (m h : Submodule ℝ (EuclideanSpace ℝ (Fin n × Fin n × Bool))),
    m ⊔ h = gLie ε → (∀ x ∈ m, ∀ y ∈ h, inner ℝ x y = 0) →
    ∀ (ι η : Type) [Fintype ι] [Fintype η] (L₀ : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] m) (L₁ : EuclideanSpace ℝ η ≃ₗᵢ[ℝ] h),
    GaugeDens ε → ∃ r₀ : ℝ, 0 < r₀ ∧ ∃ f : EuclideanSpace ℝ ι × EuclideanSpace ℝ η → ℝ,
      ContinuousAt f 0 ∧ f 0 = gaugeU ε ∧ Measurable f ∧
      ∀ S ⊆ ball (0 : EuclideanSpace ℝ ι × EuclideanSpace ℝ η) r₀, MeasurableSet S →
        Formalism.REAL.muG ε ((fun p => cayR ε ((L₀ p.1 : EuclideanSpace ℝ (Fin n × Fin n × Bool)) +
          (L₁ p.2 : EuclideanSpace ℝ (Fin n × Fin n × Bool)))) '' S) = ∫⁻ p in S, ENNReal.ofReal (f p)

def CayLiftU : Prop := ∀ (n : ℕ) (ε : Fin n → Bool) (m h : Submodule ℝ (EuclideanSpace ℝ (Fin n × Fin n × Bool))),
    m ⊔ h = gLie ε → (∀ x ∈ m, ∀ y ∈ h, inner ℝ x y = 0) →
    ∀ (ι η : Type) [Fintype ι] [Fintype η] (L₀ : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] m) (L₁ : EuclideanSpace ℝ η ≃ₗᵢ[ℝ] h),
    ∃ U ∈ 𝓝 (0 : EuclideanSpace ℝ ι × EuclideanSpace ℝ η),
    ∃ (ψ : EuclideanSpace ℝ ι × EuclideanSpace ℝ η → EuclideanSpace ℝ ι × EuclideanSpace ℝ η)
      (ψ' : EuclideanSpace ℝ ι × EuclideanSpace ℝ η →
        (EuclideanSpace ℝ ι × EuclideanSpace ℝ η →L[ℝ] EuclideanSpace ℝ ι × EuclideanSpace ℝ η)),
      (∀ p ∈ U, HasFDerivWithinAt ψ (ψ' p) U p) ∧ Set.InjOn ψ U ∧ ψ 0 = 0 ∧ ContinuousAt ψ 0 ∧
      Measurable ψ ∧ Measurable ψ' ∧
      ContinuousAt (fun p => (ψ' p).det) 0 ∧ |(ψ' 0).det| = 1 ∧
      ∀ p ∈ U, cayR ε ((L₀ (ψ p).1 : EuclideanSpace ℝ (Fin n × Fin n × Bool)) +
          (L₁ (ψ p).2 : EuclideanSpace ℝ (Fin n × Fin n × Bool))) =
        expR ε (L₀ p.1 : EuclideanSpace ℝ (Fin n × Fin n × Bool)) *
          expR ε (L₁ p.2 : EuclideanSpace ℝ (Fin n × Fin n × Bool))

theorem expProdU_of (hC : CayProdU) (hL : CayLiftU) : ExpProdU := by
  intro n ε m h hmh horth ι η _ _ L₀ L₁ hG
  haveI hHaar : (volume : Measure (EuclideanSpace ℝ ι × EuclideanSpace ℝ η)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]; infer_instance
  obtain ⟨r₀, hr₀, f, hfc, hf0, hfm, hf⟩ := hC n ε m h hmh horth ι η L₀ L₁ hG
  obtain ⟨U, hU, ψ, ψ', hψ, hinj, hψ0, hψc, hψm, hψ'm, hdc, hd0, heq⟩ := hL n ε m h hmh horth ι η L₀ L₁
  have hpre : ψ ⁻¹' ball 0 r₀ ∈ 𝓝 (0 : EuclideanSpace ℝ ι × EuclideanSpace ℝ η) :=
    hψc.preimage_mem_nhds (by rw [hψ0]; exact ball_mem_nhds _ hr₀)
  obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem hU hpre)
  refine ⟨r, hr, fun p => |(ψ' p).det| * f (ψ p), ?_, ?_, ?_, ?_⟩
  · exact chart_change_cont f ψ ψ' 0 hψc (by rw [hψ0]; exact hfc) hdc
  · simp only; rw [hd0, hψ0, hf0, one_mul]
  · exact (continuous_abs.measurable.comp (ContinuousLinearMap.continuous_det.measurable.comp hψ'm)).mul
      (hfm.comp hψm)
  · intro A hA hAm
    have hAU : A ⊆ ball 0 r := hA
    have e : (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ η =>
        expR ε (L₀ p.1 : EuclideanSpace ℝ (Fin n × Fin n × Bool)) *
          expR ε (L₁ p.2 : EuclideanSpace ℝ (Fin n × Fin n × Bool))) '' A =
        ((fun p => cayR ε ((L₀ p.1 : EuclideanSpace ℝ (Fin n × Fin n × Bool)) +
          (L₁ p.2 : EuclideanSpace ℝ (Fin n × Fin n × Bool)))) ∘ ψ) '' A := by
      refine Set.image_congr fun p hp => ?_
      exact (heq p (hrs (hAU hp)).1).symm
    rw [e]
    exact chart_change volume _ _ (ball 0 r₀) f hf ψ ψ' (ball 0 r)
      (fun p hp => (hψ p (hrs hp).1).mono fun q hq => (hrs hq).1) (hinj.mono fun q hq => (hrs hq).1)
      (by rintro _ ⟨q, hq, rfl⟩; exact (hrs hq).2) A hAU hAm

theorem locChart_of_contDiff {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (ψ : E → E) (hψ : ContDiffAt ℝ 1 ψ 0) (hd : fderiv ℝ ψ 0 = ContinuousLinearMap.id ℝ E) :
    ∃ U ∈ 𝓝 (0 : E), (∀ p ∈ U, HasFDerivWithinAt ψ (fderiv ℝ ψ p) U p) ∧ Set.InjOn ψ U ∧
      ContinuousAt ψ 0 ∧ ContinuousAt (fun p => (fderiv ℝ ψ p).det) 0 ∧ |(fderiv ℝ ψ 0).det| = 1 := by
  have hs : HasStrictFDerivAt ψ ((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E) : E →L[ℝ] E) 0 := by
    have := hψ.hasStrictFDerivAt_fderiv one_ne_zero
    rw [hd, ← ContinuousLinearEquiv.coe_refl] at this
    exact this
  have hev : ∀ᶠ p in 𝓝 (0 : E), ContDiffAt ℝ 1 ψ p := hψ.eventually (by simp)
  refine ⟨(HasStrictFDerivAt.toOpenPartialHomeomorph ψ hs).source ∩ {p | ContDiffAt ℝ 1 ψ p},
    Filter.inter_mem ((HasStrictFDerivAt.toOpenPartialHomeomorph ψ hs).open_source.mem_nhds
      (HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source hs)) hev, ?_, ?_, hψ.continuousAt, ?_, ?_⟩
  · intro p hp
    exact (((show ContDiffAt ℝ 1 ψ p from hp.2).differentiableAt (by simp)).hasFDerivAt).hasFDerivWithinAt
  · have hi := (HasStrictFDerivAt.toOpenPartialHomeomorph ψ hs).injOn
    rw [HasStrictFDerivAt.toOpenPartialHomeomorph_coe] at hi
    exact hi.mono Set.inter_subset_left
  · have hf : ContinuousAt (fderiv ℝ ψ) 0 := (hψ.fderiv_right (m := 0) (by simp)).continuousAt
    exact ContinuousLinearMap.continuous_det.continuousAt.comp hf
  · rw [hd]
    simp [ContinuousLinearMap.det]

def CayPsiU : Prop := ∀ (n : ℕ) (ε : Fin n → Bool) (m h : Submodule ℝ (EuclideanSpace ℝ (Fin n × Fin n × Bool))),
    m ⊔ h = gLie ε → (∀ x ∈ m, ∀ y ∈ h, inner ℝ x y = 0) →
    ∀ (ι η : Type) [Fintype ι] [Fintype η] (L₀ : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] m) (L₁ : EuclideanSpace ℝ η ≃ₗᵢ[ℝ] h),
    ∃ ψ : EuclideanSpace ℝ ι × EuclideanSpace ℝ η → EuclideanSpace ℝ ι × EuclideanSpace ℝ η,
      ContDiffAt ℝ 1 ψ 0 ∧ ψ 0 = 0 ∧ fderiv ℝ ψ 0 = ContinuousLinearMap.id ℝ _ ∧ Measurable ψ ∧
      ∀ᶠ p in 𝓝 0, cayR ε ((L₀ (ψ p).1 : EuclideanSpace ℝ (Fin n × Fin n × Bool)) +
          (L₁ (ψ p).2 : EuclideanSpace ℝ (Fin n × Fin n × Bool))) =
        expR ε (L₀ p.1 : EuclideanSpace ℝ (Fin n × Fin n × Bool)) *
          expR ε (L₁ p.2 : EuclideanSpace ℝ (Fin n × Fin n × Bool))

theorem cayLiftU_of (h : CayPsiU) : CayLiftU := by
  intro n ε m h' hmh horth ι η _ _ L₀ L₁
  obtain ⟨ψ, hc, h0, hd, hmeas, hev⟩ := h n ε m h' hmh horth ι η L₀ L₁
  obtain ⟨U, hU, hder, hinj, hcont, hdet, hdet1⟩ := locChart_of_contDiff ψ hc hd
  exact ⟨U ∩ _, Filter.inter_mem hU hev, ψ, fderiv ℝ ψ,
    fun p hp => (hder p hp.1).mono Set.inter_subset_left, hinj.mono Set.inter_subset_left, h0, hcont,
    hmeas, measurable_fderiv ℝ ψ, hdet, hdet1, fun p hp => hp.2⟩

theorem expProdU_of_psi (hC : CayProdU) (hP : CayPsiU) : ExpProdU := expProdU_of hC (cayLiftU_of hP)

def psiE {n : ℕ} (ε : Fin n → Bool) (m h : Submodule ℝ (EuclideanSpace ℝ (Fin n × Fin n × Bool))) {ι η : Type}
    [Fintype ι] [Fintype η] (L₀ : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] m) (L₁ : EuclideanSpace ℝ η ≃ₗᵢ[ℝ] h)
    (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ η) : EuclideanSpace ℝ ι × EuclideanSpace ℝ η :=
  let M : Matrix (Fin n) (Fin n) ℂ := NormedSpace.exp (unrealify (L₀ p.1 : EuclideanSpace ℝ (Fin n × Fin n × Bool))) *
    NormedSpace.exp (unrealify (L₁ p.2 : EuclideanSpace ℝ (Fin n × Fin n × Bool)))
  let X : Matrix (Fin n) (Fin n) ℂ := (2 : ℂ) • ((M - 1) * (M + 1)⁻¹)
  let v : EuclideanSpace ℝ (Fin n × Fin n × Bool) := (WithLp.equiv 2 _).symm (realifyFun X)
  (L₀.symm (m.orthogonalProjectionOnto v), L₁.symm (h.orthogonalProjectionOnto v))

def PsiSmoothU : Prop := ∀ (n : ℕ) (ε : Fin n → Bool) (m h : Submodule ℝ (EuclideanSpace ℝ (Fin n × Fin n × Bool))),
    m ⊔ h = gLie ε → (∀ x ∈ m, ∀ y ∈ h, inner ℝ x y = 0) →
    ∀ (ι η : Type) [Fintype ι] [Fintype η] (L₀ : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] m) (L₁ : EuclideanSpace ℝ η ≃ₗᵢ[ℝ] h),
    ContDiffAt ℝ 1 (psiE ε m h L₀ L₁) 0 ∧ fderiv ℝ (psiE ε m h L₀ L₁) 0 = ContinuousLinearMap.id ℝ _

def PsiMeasU : Prop := ∀ (n : ℕ) (ε : Fin n → Bool) (m h : Submodule ℝ (EuclideanSpace ℝ (Fin n × Fin n × Bool)))
    (ι η : Type) [Fintype ι] [Fintype η] (L₀ : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] m) (L₁ : EuclideanSpace ℝ η ≃ₗᵢ[ℝ] h),
    Measurable (psiE ε m h L₀ L₁)

def PsiInvU : Prop := ∀ (n : ℕ) (ε : Fin n → Bool) (m h : Submodule ℝ (EuclideanSpace ℝ (Fin n × Fin n × Bool))),
    m ⊔ h = gLie ε → (∀ x ∈ m, ∀ y ∈ h, inner ℝ x y = 0) →
    ∀ (ι η : Type) [Fintype ι] [Fintype η] (L₀ : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] m) (L₁ : EuclideanSpace ℝ η ≃ₗᵢ[ℝ] h),
    ∀ᶠ p in 𝓝 0, cayR ε ((L₀ (psiE ε m h L₀ L₁ p).1 : EuclideanSpace ℝ (Fin n × Fin n × Bool)) +
          (L₁ (psiE ε m h L₀ L₁ p).2 : EuclideanSpace ℝ (Fin n × Fin n × Bool))) =
        expR ε (L₀ p.1 : EuclideanSpace ℝ (Fin n × Fin n × Bool)) *
          expR ε (L₁ p.2 : EuclideanSpace ℝ (Fin n × Fin n × Bool))

theorem unrealify_zero' (n : ℕ) : unrealify (0 : EuclideanSpace ℝ (Fin n × Fin n × Bool)) = 0 := by
  funext i j
  apply Complex.ext <;> simp [unrealify]

theorem psiE_zero {n : ℕ} (ε : Fin n → Bool) (m h : Submodule ℝ (EuclideanSpace ℝ (Fin n × Fin n × Bool)))
    {ι η : Type} [Fintype ι] [Fintype η] (L₀ : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] m) (L₁ : EuclideanSpace ℝ η ≃ₗᵢ[ℝ] h) :
    psiE ε m h L₀ L₁ 0 = 0 := by
  have hr : realifyFun (0 : Matrix (Fin n) (Fin n) ℂ) = 0 := by
    funext q
    simp [realifyFun]
  simp [psiE, unrealify_zero', hr]

theorem cayPsiU_of (hS : PsiSmoothU) (hM : PsiMeasU) (hI : PsiInvU) : CayPsiU := by
  intro n ε m h hmh horth ι η _ _ L₀ L₁
  obtain ⟨hc, hd⟩ := hS n ε m h hmh horth ι η L₀ L₁
  exact ⟨psiE ε m h L₀ L₁, hc, psiE_zero ε m h L₀ L₁, hd, hM n ε m h ι η L₀ L₁,
    hI n ε m h hmh horth ι η L₀ L₁⟩

theorem expProdU_of_parts (hC : CayProdU) (hS : PsiSmoothU) (hM : PsiMeasU) (hI : PsiInvU) : ExpProdU :=
  expProdU_of_psi hC (cayPsiU_of hS hM hI)

end PI.AprimeInfW
