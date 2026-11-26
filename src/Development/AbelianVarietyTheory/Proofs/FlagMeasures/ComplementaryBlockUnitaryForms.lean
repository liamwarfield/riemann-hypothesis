module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalFrameOfIsotropicBlocks
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemIsotropicFlagSelfAdjointLeviIffBlock
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFundIpow
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsRadialMapUnitaryLeviBlockProduct
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaugeMeasureMatrixAlgebraSubgroupLocalAsymptotic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAlgebraIsotropicFlagSelfAdjointLevi

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingWithDensity
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

namespace GlobalTheory.HaarMul

theorem measurePreserving_withDensity {X : Type} [MeasurableSpace X] (μ : Measure X) {f : X → X}
    (hf : Measurable f) {ρ : X → ENNReal} (hρ : Measurable ρ) {c d : ENNReal} (hcd : d * c = 1)
    (hμ : μ.map f = c • μ) (hρf : ∀ x, ρ x = d * ρ (f x)) :
    MeasurePreserving f (μ.withDensity ρ) (μ.withDensity ρ) := by
  refine ⟨hf, ?_⟩
  ext s hs
  rw [Measure.map_apply hf hs, withDensity_apply _ (hf hs), withDensity_apply _ hs]

  have h1 : ∫⁻ x in f ⁻¹' s, ρ x ∂μ = ∫⁻ x, d * s.indicator ρ (f x) ∂μ := by
    rw [← lintegral_indicator (hf hs)]
    congr 1
    funext x
    by_cases hx : f x ∈ s
    · simp [Set.indicator_apply, hx, ← hρf x]
    · simp [Set.indicator_apply, hx]
  rw [h1, lintegral_const_mul d (f := fun x => s.indicator ρ (f x)) ((hρ.indicator hs).comp hf),
    ← lintegral_map (hρ.indicator hs) hf, hμ,
    lintegral_smul_measure, smul_eq_mul, ← mul_assoc, hcd, one_mul, lintegral_indicator hs]

theorem measurePreserving_mul_mul : ∀ (j : ℕ) (a b : Matrix (Fin j) (Fin j) ℂ), a.det ≠ 0 → b.det ≠ 0 →
    MeasurePreserving (fun (x : Fin j → Fin j → ℂ) (r s : Fin j) => (a * Matrix.of x * b) r s)
      (haarLoc j) (haarLoc j) := by
  intro j a b ha hb

  let L : (Fin j → Fin j → ℂ) →ₗ[ℝ] (Fin j → Fin j → ℂ) :=
    { toFun := fun x r s => (a * Matrix.of x * b) r s
      map_add' := fun x y => by
        have h : a * Matrix.of (x + y) * b = a * Matrix.of x * b + a * Matrix.of y * b := by
          rw [show Matrix.of (x + y) = Matrix.of x + Matrix.of y from rfl, Matrix.mul_add, Matrix.add_mul]
        funext r s
        exact congrFun (congrFun h r) s
      map_smul' := fun c x => by
        have h : a * Matrix.of (c • x) * b = c • (a * Matrix.of x * b) := by
          rw [show Matrix.of (c • x) = c • Matrix.of x from rfl, Matrix.mul_smul, Matrix.smul_mul]
        funext r s
        exact congrFun (congrFun h r) s }
  have hdet : LinearMap.det L = ‖a.det‖ ^ (2 * j) * ‖b.det‖ ^ (2 * j) :=
    GlobalTheory.TwoSidedJac.real_jacobians.1 j j a b L (fun T => rfl)
  have hA : ‖a.det‖ ≠ 0 := norm_ne_zero_iff.2 ha
  have hB : ‖b.det‖ ≠ 0 := norm_ne_zero_iff.2 hb
  have hD : 0 < ‖a.det‖ ^ (2 * j) * ‖b.det‖ ^ (2 * j) :=
    mul_pos (pow_pos (norm_pos_iff.2 ha) _) (pow_pos (norm_pos_iff.2 hb) _)
  have hcont : Continuous fun x : Fin j → Fin j → ℂ => (Matrix.of x).det :=
    (continuous_id.matrix_det : Continuous fun A : Matrix (Fin j) (Fin j) ℂ => A.det)
  have hρ : Measurable fun x : Fin j → Fin j → ℂ => ENNReal.ofReal ((‖(Matrix.of x).det‖ ^ 2)⁻¹ ^ j) :=
    ENNReal.measurable_ofReal.comp (((hcont.measurable.norm.pow_const 2).inv).pow_const j)

  haveI : (volume : Measure ℂ).IsAddHaarMeasure := inferInstance
  haveI : (volume : Measure (Fin j → ℂ)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure (fun _ : Fin j => (volume : Measure ℂ))
  haveI : (volume : Measure (Fin j → Fin j → ℂ)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure (fun _ : Fin j => (volume : Measure (Fin j → ℂ)))
  have hμ : (volume : Measure (Fin j → Fin j → ℂ)).map L =
      ENNReal.ofReal |(LinearMap.det L)⁻¹| • volume :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar _ (by rw [hdet]; exact hD.ne')
  have hcd : ENNReal.ofReal (‖a.det‖ ^ (2 * j) * ‖b.det‖ ^ (2 * j)) * ENNReal.ofReal |(LinearMap.det L)⁻¹| = 1 := by
    rw [hdet, abs_of_pos (inv_pos.2 hD), ← ENNReal.ofReal_mul hD.le, mul_inv_cancel₀ hD.ne', ENNReal.ofReal_one]

  have hρf : ∀ x : Fin j → Fin j → ℂ, ENNReal.ofReal ((‖(Matrix.of x).det‖ ^ 2)⁻¹ ^ j) =
      ENNReal.ofReal (‖a.det‖ ^ (2 * j) * ‖b.det‖ ^ (2 * j)) *
        ENNReal.ofReal ((‖(Matrix.of (L x)).det‖ ^ 2)⁻¹ ^ j) := by
    intro x
    rw [← ENNReal.ofReal_mul hD.le]
    congr 1
    rw [show Matrix.of (L x) = a * Matrix.of x * b from rfl, Matrix.det_mul, Matrix.det_mul, norm_mul, norm_mul]
    have hP : (‖a.det‖ ^ 2) ^ j * ((‖a.det‖ ^ 2) ^ j)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero _ (pow_ne_zero _ hA))
    have hQ : (‖b.det‖ ^ 2) ^ j * ((‖b.det‖ ^ 2) ^ j)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero _ (pow_ne_zero _ hB))
    rw [mul_pow, mul_pow, mul_inv, mul_inv, mul_pow, mul_pow, inv_pow (‖a.det‖ ^ 2), inv_pow (‖b.det‖ ^ 2),
      pow_mul, pow_mul]
    linear_combination (-((‖(Matrix.of x).det‖ ^ 2)⁻¹ ^ j * (‖b.det‖ ^ 2) ^ j * ((‖b.det‖ ^ 2) ^ j)⁻¹)) * hP
      - (‖(Matrix.of x).det‖ ^ 2)⁻¹ ^ j * hQ
  unfold haarLoc
  exact measurePreserving_withDensity volume L.continuous_of_finiteDimensional.measurable hρ hcd hμ hρf

end GlobalTheory.HaarMul
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeviChartMapHaarCarriedInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeviChartMapHaarCarriedInvariant
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

namespace GlobalTheory.LeviIso

theorem isClosed_flagM {n a : ℕ} (ε : Fin n → Bool) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) :
    IsClosed (flagM ε W) := by
  have hc : Continuous fun g : Formalism.REAL.UJ ε => uMat g := Units.continuous_val.comp continuous_subtype_val
  have hc' : Continuous fun g : Formalism.REAL.UJ ε => (uMat g)ᴴ := hc.matrix_conjTranspose
  have hset : flagM ε W = ⋂ i, ⋂ y ∈ W i,
      ((fun g : Formalism.REAL.UJ ε => uMat g *ᵥ y) ⁻¹' (W i : Set (Fin n → ℂ)) ∩
        (fun g : Formalism.REAL.UJ ε => (uMat g)ᴴ *ᵥ y) ⁻¹' (W i : Set (Fin n → ℂ))) := by
    ext g
    simp [flagM]
  rw [hset]
  refine isClosed_iInter fun i => isClosed_biInter fun y _ => ?_
  have hW : IsClosed (W i : Set (Fin n → ℂ)) := (W i).closed_of_finiteDimensional
  exact (hW.preimage (hc.matrix_mulVec continuous_const)).inter (hW.preimage (hc'.matrix_mulVec continuous_const))

theorem ae_det_ne_zero {a : ℕ} (j : Fin a → ℕ) (d : Fin a → ℝ) {Y : Type} [MeasurableSpace Y] (ν : Measure Y)
    [SFinite ν] :
    ∀ᵐ z ∂((Measure.pi fun i => ENNReal.ofReal (d i) • haarLoc (j i)).prod ν), ∀ i, (Matrix.of (z.1 i)).det ≠ 0 := by
  have h1 : ∀ᵐ x ∂(Measure.pi fun i => ENNReal.ofReal (d i) • haarLoc (j i)), ∀ i, (Matrix.of (x i)).det ≠ 0 := by
    rw [ae_all_iff]
    intro i
    have h0 : ∀ᵐ y ∂(ENNReal.ofReal (d i) • haarLoc (j i)), (Matrix.of y).det ≠ 0 := by
      have hn := (haarLoc_conj_and_null (j i)).2
      rw [ae_iff, Measure.smul_apply]
      simp [hn]
    exact (Measure.tendsto_eval_ae_ae (μ := fun i => ENNReal.ofReal (d i) • haarLoc (j i)) (i := i)).eventually
      (p := fun y => (Matrix.of y).det ≠ 0) h0
  exact Measure.quasiMeasurePreserving_fst.ae h1

private theorem measurePreserving_smul_measure {X : Type} [MeasurableSpace X] {μ : Measure X} {f : X → X}
    (hf : MeasurePreserving f μ μ) (c : ENNReal) : MeasurePreserving f (c • μ) (c • μ) :=
  ⟨hf.measurable, by rw [Measure.map_smul c hf.measurable.aemeasurable, hf.map_eq]⟩

theorem map_chart_carried_and_invariant : ∀ (n n₀ a : ℕ) (j : Fin a → ℕ) (ε : Fin n → Bool) (ε₀ : Fin n₀ → Bool) (B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (B₀ : Matrix (Fin n) (Fin n₀) ℂ), IsFrame ε ε₀ B B₀ → ∀ W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ), SpansFlag B W → ∀ θ : (∀ i, Fin (j i) → Fin (j i) → ℂ) × Formalism.REAL.UJ ε₀ → Formalism.REAL.UJ ε, Measurable θ → (∀ z, (∀ i, (Matrix.of (z.1 i)).det ≠ 0) → uMat (θ z) = lev ε B B₀ (fun i => Matrix.of (z.1 i)) (uMat z.2)) → ∀ c : ℝ, (((Measure.pi fun i => ENNReal.ofReal (2 ^ (j i ^ 2)) • haarLoc (j i)).prod (ENNReal.ofReal c • Formalism.REAL.muG ε₀)).map θ) (flagM ε W)ᶜ = 0 ∧ ∀ s ∈ flagM ε W, (((Measure.pi fun i => ENNReal.ofReal (2 ^ (j i ^ 2)) • haarLoc (j i)).prod (ENNReal.ofReal c • Formalism.REAL.muG ε₀)).map θ).map (fun g => s * g) = (((Measure.pi fun i => ENNReal.ofReal (2 ^ (j i ^ 2)) • haarLoc (j i)).prod (ENNReal.ofReal c • Formalism.REAL.muG ε₀)).map θ) := by
  intro n n₀ a j ε ε₀ B B₀ hB W hW θ hθ hθl c
  set P := Measure.pi fun i => ENNReal.ofReal (2 ^ (j i ^ 2)) • haarLoc (j i) with hP
  set ν := ENNReal.ofReal c • Formalism.REAL.muG ε₀ with hν
  have hdet : ∀ᵐ z ∂(P.prod ν), ∀ i, (Matrix.of (z.1 i)).det ≠ 0 :=
    ae_det_ne_zero j (fun i => 2 ^ (j i ^ 2)) ν
  have hmem : ∀ z : (∀ i, Fin (j i) → Fin (j i) → ℂ) × Formalism.REAL.UJ ε₀,
      (∀ i, (Matrix.of (z.1 i)).det ≠ 0) → θ z ∈ flagM ε W := fun z hz =>
    (Range.mem_flagM_iff n n₀ a j ε ε₀ B B₀ hB W hW (θ z)).2 ⟨fun i => Matrix.of (z.1 i), z.2, hz, hθl z hz⟩
  have hM : MeasurableSet (flagM ε W) := (isClosed_flagM ε W).measurableSet
  refine ⟨?_, fun s hs => ?_⟩
  · have h : ∀ᵐ m ∂((P.prod ν).map θ), m ∈ flagM ε W :=
      (ae_map_iff hθ.aemeasurable hM).2 (hdet.mono hmem)
    exact measure_mono_null (fun m hm => hm) (ae_iff.1 h)
  · obtain ⟨x, g, hx, hs'⟩ := (Range.mem_flagM_iff n n₀ a j ε ε₀ B B₀ hB W hW s).1 hs
    let T : (∀ i, Fin (j i) → Fin (j i) → ℂ) × Formalism.REAL.UJ ε₀ → (∀ i, Fin (j i) → Fin (j i) → ℂ) × Formalism.REAL.UJ ε₀ :=
      Prod.map (fun (y : ∀ i, Fin (j i) → Fin (j i) → ℂ) (i : Fin a) (r t : Fin (j i)) =>
        (x i * Matrix.of (y i) * (1 : Matrix (Fin (j i)) (Fin (j i)) ℂ)) r t) (fun u => g * u)
    have hT : MeasurePreserving T (P.prod ν) (P.prod ν) := by
      refine MeasurePreserving.prod ?_ ?_
      · exact measurePreserving_pi _ _ fun i =>
          measurePreserving_smul_measure (GlobalTheory.HaarMul.measurePreserving_mul_mul (j i) (x i) 1 (hx i) (by simp)) _
      · exact measurePreserving_smul_measure (measurePreserving_mul_left (Formalism.REAL.muG ε₀) g) _
    have hcomm : ∀ z, (∀ i, (Matrix.of (z.1 i)).det ≠ 0) → s * θ z = θ (T z) := by
      intro z hz
      have hz' : ∀ i, (Matrix.of ((T z).1 i)).det ≠ 0 := by
        intro i
        have : Matrix.of ((T z).1 i) = x i * Matrix.of (z.1 i) := by
          ext r t
          simp [T]
        rw [this, Matrix.det_mul]
        exact mul_ne_zero (hx i) (hz i)
      apply Subtype.ext
      apply Units.ext
      change uMat s * uMat (θ z) = uMat (θ (T z))
      rw [hs', hθl z hz, hθl (T z) hz', ← hB.lev_mul]
      congr 1
      · funext i
        ext r t
        simp [T]
    have hmul : Measurable fun m : Formalism.REAL.UJ ε => s * m := measurable_const_mul s
    calc ((P.prod ν).map θ).map (fun m => s * m)
        = (P.prod ν).map (fun z => s * θ z) := by rw [Measure.map_map hmul hθ]; rfl
      _ = (P.prod ν).map (fun z => θ (T z)) := Measure.map_congr (hdet.mono fun z hz => hcomm z hz)
      _ = ((P.prod ν).map T).map θ := by rw [Measure.map_map hθ hT.measurable]; rfl
      _ = (P.prod ν).map θ := by rw [hT.map_eq]

end GlobalTheory.LeviIso
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeviChartMapHaarCarriedInvariantStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_chart_map_haar_carried_invariant : ∀ (n n₀ a : ℕ) (j : Fin a → ℕ) (ε : Fin n → Bool) (ε₀ : Fin n₀ → Bool) (B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (B₀ : Matrix (Fin n) (Fin n₀) ℂ), IsFrame ε ε₀ B B₀ → ∀ W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ), SpansFlag B W → ∀ θ : (∀ i, Fin (j i) → Fin (j i) → ℂ) × Formalism.REAL.UJ ε₀ → Formalism.REAL.UJ ε, Measurable θ → (∀ z, (∀ i, (Matrix.of (z.1 i)).det ≠ 0) → uMat (θ z) = lev ε B B₀ (fun i => Matrix.of (z.1 i)) (uMat z.2)) → ∀ c : ℝ, (((Measure.pi fun i => ENNReal.ofReal (2 ^ (j i ^ 2)) • haarLoc (j i)).prod (ENNReal.ofReal c • Formalism.REAL.muG ε₀)).map θ) (flagM ε W)ᶜ = 0 ∧ ∀ s ∈ flagM ε W, (((Measure.pi fun i => ENNReal.ofReal (2 ^ (j i ^ 2)) • haarLoc (j i)).prod (ENNReal.ofReal c • Formalism.REAL.muG ε₀)).map θ).map (fun g => s * g) = (((Measure.pi fun i => ENNReal.ofReal (2 ^ (j i ^ 2)) • haarLoc (j i)).prod (ENNReal.ofReal c • Formalism.REAL.muG ε₀)).map θ) := by
  first | exact @GlobalTheory.LeviIso.map_chart_carried_and_invariant | exact GlobalTheory.LeviIso.map_chart_carried_and_invariant | (intros; apply GlobalTheory.LeviIso.map_chart_carried_and_invariant <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalTriangular
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

namespace GlobalTheory.LeviIso.BlockGS

theorem exists_coeff_of_mem_span {ι V : Type} [Fintype ι] [AddCommGroup V] [Module ℂ V]
    (g : ι → V) (s : Set ι) (v : V) (hv : v ∈ Submodule.span ℂ (g '' s)) :
    ∃ c : ι → ℂ, (∀ y, y ∉ s → c y = 0) ∧ v = ∑ y, c y • g y := by
  obtain ⟨l, hl, rfl⟩ := (Finsupp.mem_span_image_iff_linearCombination ℂ).1 hv
  refine ⟨l, fun y hy => ?_, ?_⟩
  · by_contra h
    exact hy (hl (Finsupp.mem_support_iff.2 h))
  · rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    simp

theorem exists_orthonormal_triangular {ι V : Type} [Fintype ι] [LinearOrder ι]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] (f : ι → V) (hf : LinearIndependent ℂ f) :
    ∃ (g : ι → V) (P Q : ι → ι → ℂ), Orthonormal ℂ g ∧ (∀ y x, x < y → P y x = 0 ∧ Q y x = 0) ∧
      (∀ x, f x = ∑ y, P y x • g y) ∧ ∀ x, g x = ∑ y, Q y x • f y := by
  classical
  let _ : LocallyFiniteOrderBot ι := LocallyFiniteOrderBot.ofIic ι (fun x => Finset.univ.filter (· ≤ x)) (by simp)
  have : WellFoundedLT ι := Finite.to_wellFoundedLT
  have hs : ∀ x, Submodule.span ℂ (InnerProductSpace.gramSchmidtNormed ℂ f '' Set.Iic x)
      = Submodule.span ℂ (f '' Set.Iic x) := fun x => by
    rw [InnerProductSpace.span_gramSchmidtNormed, InnerProductSpace.span_gramSchmidt_Iic]
  have h1 : ∀ x, ∃ c : ι → ℂ, (∀ y, y ∉ Set.Iic x → c y = 0) ∧
      f x = ∑ y, c y • InnerProductSpace.gramSchmidtNormed ℂ f y := fun x =>
    exists_coeff_of_mem_span _ _ _ (by
      rw [hs]; exact Submodule.subset_span ⟨x, le_refl x, rfl⟩)
  have h2 : ∀ x, ∃ c : ι → ℂ, (∀ y, y ∉ Set.Iic x → c y = 0) ∧
      InnerProductSpace.gramSchmidtNormed ℂ f x = ∑ y, c y • f y := fun x =>
    exists_coeff_of_mem_span _ _ _ (by
      rw [← hs]; exact Submodule.subset_span ⟨x, le_refl x, rfl⟩)
  choose P hP hP' using h1
  choose Q hQ hQ' using h2
  exact ⟨_, fun y x => P x y, fun y x => Q x y, InnerProductSpace.gramSchmidtNormed_orthonormal hf,
    fun y x h => ⟨hP x y (not_le.2 h), hQ x y (not_le.2 h)⟩, hP', hQ'⟩

theorem linearIndependent_columns (n a : ℕ) (j : Fin a → ℕ)
    (A : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (C : ∀ i, Matrix (Fin (j i)) (Fin n) ℂ)
    (h1 : ∀ i, C i * A i = 1) (h0 : ∀ i k, i ≠ k → C i * A k = 0) :
    LinearIndependent ℂ (fun x : (Σ i, Fin (j i)) =>
      (WithLp.toLp 2 (fun r => A x.1 r x.2) : EuclideanSpace ℂ (Fin n))) := by
  classical
  rw [Fintype.linearIndependent_iff]
  rintro c hc ⟨i, u⟩
  have hr : ∀ r, ∑ x : (Σ i, Fin (j i)), c x * A x.1 r x.2 = 0 := fun r => by
    have := congrArg (fun v : EuclideanSpace ℂ (Fin n) => v r) hc
    simpa using this
  have h : ∑ x : (Σ i, Fin (j i)), c x * (C i * A x.1) u x.2 = 0 := by
    simp only [Matrix.mul_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun r _ => ?_
    have := congrArg (fun z => C i u r * z) (hr r)
    simp only [Finset.mul_sum, mul_zero] at this
    rw [← this]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [Fintype.sum_sigma, Finset.sum_eq_single i] at h
  · simpa [h1, Matrix.one_apply] using h
  · intro k _ hk
    simp [h0 i k hk.symm]
  · simp

theorem block_gramSchmidt : ∀ (n a : ℕ) (j : Fin a → ℕ) (A : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (C : ∀ i, Matrix (Fin (j i)) (Fin n) ℂ), (∀ i, C i * A i = 1) → (∀ i k, i ≠ k → C i * A k = 0) → ∃ (B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (p q : ∀ k i, Matrix (Fin (j k)) (Fin (j i)) ℂ), (∀ i, (B i)ᴴ * B i = 1) ∧ (∀ i k, i ≠ k → (B i)ᴴ * B k = 0) ∧ (∀ k i, i < k → p k i = 0 ∧ q k i = 0) ∧ (∀ i, A i = ∑ k, B k * p k i) ∧ (∀ i, B i = ∑ k, A k * q k i) ∧ ∀ i, p i i * q i i = 1 := by
  classical
  intro n a j A C h1 h0
  let _ : LinearOrder (Σ i, Fin (j i)) := inferInstanceAs (LinearOrder (Σₗ i, Fin (j i)))
  obtain ⟨g, P, Q, hg, htri, hf, hg'⟩ :=
    exists_orthonormal_triangular _ (linearIndependent_columns n a j A C h1 h0)
  let B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ := fun i => Matrix.of fun r u => g ⟨i, u⟩ r
  let p : ∀ k i, Matrix (Fin (j k)) (Fin (j i)) ℂ := fun k i => Matrix.of fun v u => P ⟨k, v⟩ ⟨i, u⟩
  let q : ∀ k i, Matrix (Fin (j k)) (Fin (j i)) ℂ := fun k i => Matrix.of fun v u => Q ⟨k, v⟩ ⟨i, u⟩
  have hBB : ∀ i k u v, ((B i)ᴴ * B k) u v = inner ℂ (g ⟨i, u⟩) (g ⟨k, v⟩) := by
    intro i k u v
    simp [B, Matrix.mul_apply, PiLp.inner_apply, mul_comm]
  have e1 : ∀ i, (B i)ᴴ * B i = 1 := by
    intro i
    ext u v
    rw [hBB, orthonormal_iff_ite.1 hg, Matrix.one_apply]
    simp
  have e2 : ∀ i k, i ≠ k → (B i)ᴴ * B k = 0 := by
    intro i k h
    ext u v
    rw [hBB, orthonormal_iff_ite.1 hg]
    simp [h]
  have e3 : ∀ k i, i < k → p k i = 0 ∧ q k i = 0 := by
    intro k i h
    constructor <;> ext v u
    · exact (htri _ _ (Sigma.Lex.left _ _ h)).1
    · exact (htri _ _ (Sigma.Lex.left _ _ h)).2
  have e4 : ∀ i, A i = ∑ k, B k * p k i := by
    intro i
    ext r u
    have := congrArg (fun v : EuclideanSpace ℂ (Fin n) => v r) (hf ⟨i, u⟩)
    simp only [Matrix.sum_apply, Matrix.mul_apply, B, p, Matrix.of_apply]
    simpa [Fintype.sum_sigma, mul_comm] using this
  have e5 : ∀ i, B i = ∑ k, A k * q k i := by
    intro i
    ext r u
    have := congrArg (fun v : EuclideanSpace ℂ (Fin n) => v r) (hg' ⟨i, u⟩)
    simp only [Matrix.sum_apply, Matrix.mul_apply, B, q, Matrix.of_apply]
    simpa [Fintype.sum_sigma, mul_comm] using this
  refine ⟨B, p, q, e1, e2, e3, e4, e5, fun i => ?_⟩
  have hp : ∀ k, (B i)ᴴ * A k = p i k := by
    intro k
    rw [e4 k, Matrix.mul_sum, Finset.sum_eq_single i]
    · rw [← Matrix.mul_assoc, e1, Matrix.one_mul]
    · intro l _ hl
      rw [← Matrix.mul_assoc, e2 i l hl.symm, Matrix.zero_mul]
    · simp
  have h : (B i)ᴴ * (∑ k, A k * q k i) = 1 := by rw [← e5, e1]
  rw [Matrix.mul_sum, Finset.sum_eq_single i] at h
  · rw [← h, ← Matrix.mul_assoc, hp]
  · intro l _ hl
    rw [← Matrix.mul_assoc, hp]
    rcases lt_or_gt_of_ne hl with hl | hl
    · rw [(e3 i l hl).1, Matrix.zero_mul]
    · rw [(e3 l i hl).2, Matrix.mul_zero]
  · simp

end GlobalTheory.LeviIso.BlockGS
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagStabilizerMulInvLeviComponentMemUnipotent
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagStabilizerMulInvLeviComponentMemUnipotent
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso
open Formalism.REAL (Jm UJ Jm_mul_self Jm_conjTranspose)

namespace GlobalTheory.LeviUnip

variable {n n₀ a : ℕ} {j : Fin a → ℕ}

theorem umul {ε : Fin n → Bool} (g h : UJ ε) : uMat (g * h) = uMat g * uMat h := rfl

theorem uone {ε : Fin n → Bool} : uMat (1 : UJ ε) = 1 := rfl

theorem umul_inv {ε : Fin n → Bool} (g : UJ ε) : uMat g * uMat g⁻¹ = 1 := by rw [← umul, mul_inv_cancel, uone]

theorem uinv_mul {ε : Fin n → Bool} (g : UJ ε) : uMat g⁻¹ * uMat g = 1 := by rw [← umul, inv_mul_cancel, uone]

theorem col_mem {B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ} {W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)}
    (hB : SpansFlag B W) {k : Fin (a + 1)} {i : Fin a} (hi : i.castSucc < k) (u : Fin (j i) → ℂ) :
    B i *ᵥ u ∈ W k := by
  classical
  refine (hB k _).2 ⟨Pi.single i u, fun i' hi' => ?_, ?_⟩
  · have hne : i' ≠ i := by rintro rfl; exact hi' hi
    exact Pi.single_eq_of_ne hne _
  · rw [Finset.sum_eq_single i (fun b _ hb => by rw [Pi.single_eq_of_ne hb, Matrix.mulVec_zero])
      (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same]

theorem map_mem {B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ} {W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)}
    (hB : SpansFlag B W) {k : Fin (a + 1)} (F : Matrix (Fin n) (Fin n) ℂ) (U : Submodule ℂ (Fin n → ℂ))
    (h : ∀ i : Fin a, i.castSucc < k → ∀ u, (F * B i) *ᵥ u ∈ U) {y : Fin n → ℂ} (hy : y ∈ W k) :
    F *ᵥ y ∈ U := by
  obtain ⟨u, hu, rfl⟩ := (hB k y).1 hy
  rw [Matrix.mulVec_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  by_cases hi : i.castSucc < k
  · rw [Matrix.mulVec_mulVec]
    exact h i hi (u i)
  · rw [hu i hi, Matrix.mulVec_zero, Matrix.mulVec_zero]
    exact U.zero_mem

theorem sum_col_mem {B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ} {W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)}
    (hB : SpansFlag B W) {k : Fin (a + 1)} {r : ℕ} (q : ∀ i, Matrix (Fin (j i)) (Fin r) ℂ)
    (hq : ∀ i : Fin a, ¬ i.castSucc < k → q i = 0) (u : Fin r → ℂ) : (∑ i, B i * q i) *ᵥ u ∈ W k := by
  rw [Matrix.sum_mulVec]
  refine (hB k _).2 ⟨fun i => q i *ᵥ u, fun i hi => by
    show q i *ᵥ u = 0
    rw [hq i hi, Matrix.zero_mulVec], ?_⟩
  exact Finset.sum_congr rfl fun i _ => (Matrix.mulVec_mulVec _ _ _).symm

theorem mul_inv_mem_flagN (n n₀ a : ℕ) (j : Fin a → ℕ) (ε : Fin n → Bool) (ε₀ : Fin n₀ → Bool)
    (B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (B₀ : Matrix (Fin n) (Fin n₀) ℂ) (hF : IsFrame ε ε₀ B B₀)
    (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) (A : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ)
    (A₀ : Matrix (Fin n) (Fin n₀) ℂ) (p : ∀ k i, Matrix (Fin (j k)) (Fin (j i)) ℂ)
    (d : ∀ k, Matrix (Fin (j k)) (Fin n₀) ℂ) (s h : Formalism.REAL.UJ ε₀)
    (y : ∀ i, Matrix (Fin (j i)) (Fin (j i)) ℂ) (g m : Formalism.REAL.UJ ε)
    (hA : SpansFlag A W) (hB : SpansFlag B W) (hp : ∀ k i, i < k → p k i = 0) (hpd : ∀ i, (p i i).det ≠ 0)
    (hAB : ∀ i, A i = ∑ k, B k * p k i) (hA₀ : A₀ = B₀ * uMat s + ∑ k, B k * d k)
    (hy : ∀ i, (y i).det ≠ 0) (hg : ∀ i, uMat g * A i = A i * y i) (hg₀ : uMat g * A₀ = A₀ * uMat h)
    (hm : uMat m = lev ε B B₀ (fun i => p i i * y i * (p i i)⁻¹) (uMat (s * h * s⁻¹))) :
    g * m⁻¹ ∈ flagN ε W := by
  classical
  have hpu : ∀ i, IsUnit (p i i).det := fun i => isUnit_iff_ne_zero.2 (hpd i)
  have hyu : ∀ i, IsUnit (y i).det := fun i => isUnit_iff_ne_zero.2 (hy i)
  set x : ∀ i, Matrix (Fin (j i)) (Fin (j i)) ℂ := fun i => p i i * y i * (p i i)⁻¹ with hx
  have hxu : ∀ i, IsUnit (x i).det := by
    intro i
    rw [isUnit_iff_ne_zero]
    simp [hx, Matrix.det_mul, Matrix.det_nonsing_inv, hpd i, hy i]

  have hMB : ∀ i, uMat m⁻¹ * B i = B i * (x i)⁻¹ := by
    intro i
    have h1 : uMat m * B i = B i * x i := by
      rw [hm]
      exact GlobalTheory.LeviIso.IsFrame.lev_mul_B _ _ hF i
    calc uMat m⁻¹ * B i = uMat m⁻¹ * (B i * (x i * (x i)⁻¹)) := by
          rw [Matrix.mul_nonsing_inv _ (hxu i), Matrix.mul_one]
      _ = (uMat m⁻¹ * uMat m) * B i * (x i)⁻¹ := by
          rw [← Matrix.mul_assoc (B i), ← h1]
          simp only [Matrix.mul_assoc]
      _ = B i * (x i)⁻¹ := by rw [uinv_mul, Matrix.one_mul]

  have hG : ∀ k (v : Fin n → ℂ), v ∈ W k → uMat g *ᵥ v ∈ W k := fun k v hv =>
    map_mem hA (uMat g) (W k) (fun i hi u => by
      rw [hg i, ← Matrix.mulVec_mulVec]
      exact col_mem hA hi _) hv
  have hsub : ∀ v : Fin n → ℂ, uMat (g * m⁻¹) *ᵥ v - v = (uMat g * uMat m⁻¹ - 1) *ᵥ v := by
    intro v
    rw [umul, Matrix.sub_mulVec, Matrix.one_mulVec]

  have hNA : ∀ l, (uMat g * uMat m⁻¹ - 1) * A l =
      uMat g * ∑ k, B k * ((x k)⁻¹ * p k l - p k l * (y l)⁻¹) := by
    intro l
    have e1 : uMat m⁻¹ * A l = ∑ k, B k * ((x k)⁻¹ * p k l) := by
      rw [hAB l, Matrix.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Matrix.mul_assoc, hMB k, Matrix.mul_assoc]
    have e2 : uMat g * A l * (y l)⁻¹ = A l := by
      rw [hg l, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hyu l), Matrix.mul_one]
    calc (uMat g * uMat m⁻¹ - 1) * A l = uMat g * (uMat m⁻¹ * A l) - A l := by
          rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
      _ = uMat g * ∑ k, B k * ((x k)⁻¹ * p k l) - uMat g * A l * (y l)⁻¹ := by rw [e1, e2]
      _ = _ := by
          rw [hAB l]
          simp only [Matrix.mul_sub, Finset.sum_sub_distrib, Matrix.mul_sum, Matrix.sum_mul,
            Matrix.mul_assoc]

  have hq0 : ∀ l k, l ≤ k → (x k)⁻¹ * p k l - p k l * (y l)⁻¹ = 0 := by
    intro l k hlk
    rcases hlk.lt_or_eq with h | rfl
    · rw [hp k l h, Matrix.mul_zero, Matrix.zero_mul, sub_zero]
    · have : (x l)⁻¹ * p l l = p l l * (y l)⁻¹ := by
        rw [hx, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (hpu l),
          Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hpu l), Matrix.mul_one]
      rw [this, sub_self]

  have hNB₀ : (uMat g * uMat m⁻¹ - 1) * B₀ =
      (∑ k, B k * d k) * uMat s⁻¹ - uMat g * (∑ k, B k * d k) * (uMat h⁻¹ * uMat s⁻¹) := by
    have hinv : (s * h * s⁻¹)⁻¹ = s * h⁻¹ * s⁻¹ := by group
    have e1 : uMat m⁻¹ * B₀ = B₀ * (uMat s * uMat h⁻¹ * uMat s⁻¹) := by
      have h1 : uMat m * B₀ = B₀ * uMat (s * h * s⁻¹) := by
        rw [hm]
        exact GlobalTheory.LeviIso.IsFrame.lev_mul_B₀ _ _ hF
      calc uMat m⁻¹ * B₀ = uMat m⁻¹ * (B₀ * (uMat (s * h * s⁻¹) * uMat (s * h * s⁻¹)⁻¹)) := by
            rw [umul_inv, Matrix.mul_one]
        _ = (uMat m⁻¹ * uMat m) * B₀ * uMat (s * h * s⁻¹)⁻¹ := by
            rw [← Matrix.mul_assoc B₀, ← h1]
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [uinv_mul, Matrix.one_mul, hinv, umul, umul]
    have e2 : B₀ * uMat s = A₀ - ∑ k, B k * d k := by
      rw [hA₀]
      abel
    calc (uMat g * uMat m⁻¹ - 1) * B₀ = uMat g * (uMat m⁻¹ * B₀) - B₀ := by
          rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
      _ = uMat g * (B₀ * uMat s) * (uMat h⁻¹ * uMat s⁻¹) - B₀ := by
          rw [e1]
          simp only [Matrix.mul_assoc]
      _ = (A₀ * uMat h - uMat g * ∑ k, B k * d k) * (uMat h⁻¹ * uMat s⁻¹) - B₀ := by
          rw [e2, Matrix.mul_sub, hg₀]
      _ = A₀ * uMat s⁻¹ - uMat g * (∑ k, B k * d k) * (uMat h⁻¹ * uMat s⁻¹) - B₀ := by
          rw [Matrix.sub_mul, Matrix.mul_assoc A₀, ← Matrix.mul_assoc (uMat h), umul_inv h,
            Matrix.one_mul]
      _ = (B₀ * uMat s + ∑ k, B k * d k) * uMat s⁻¹
            - uMat g * (∑ k, B k * d k) * (uMat h⁻¹ * uMat s⁻¹) - B₀ := by rw [← hA₀]
      _ = _ := by
          rw [Matrix.add_mul, Matrix.mul_assoc B₀, umul_inv s, Matrix.mul_one]
          abel
  have hlast : ∀ i : Fin a, i.castSucc < Fin.last a := fun i => Fin.castSucc_lt_last i
  have hD : ∀ z, (∑ k, B k * d k) *ᵥ z ∈ W (Fin.last a) := fun z =>
    sum_col_mem hB d (fun i hi => absurd (hlast i) hi) z
  simp only [flagN, Set.mem_ofPred_eq]
  refine ⟨fun i v hv => ?_, fun v hv => ?_⟩
  · rw [hsub]
    refine map_mem hA _ (W i.castSucc) (fun l hl u => ?_) hv
    rw [hNA l, ← Matrix.mulVec_mulVec]
    refine hG _ _ (sum_col_mem hB (fun k => (x k)⁻¹ * p k l - p k l * (y l)⁻¹) (fun k hk => hq0 l k ?_) u)
    rw [Fin.castSucc_lt_castSucc_iff, not_lt] at hk
    rw [Fin.castSucc_lt_succ_iff] at hl
    exact hl.trans hk
  · rw [hsub]

    have hBJ : ∀ i, (B i)ᴴ *ᵥ (Jm ε *ᵥ v) = 0 := by
      intro i
      funext c
      have hc := hv _ (col_mem hB (hlast i) (Pi.single c 1))
      rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec] at hc
      simpa using hc
    have hdec : v = (∑ i, B i *ᵥ ((B i)ᴴ *ᵥ v)) + B₀ *ᵥ (B₀ᴴ *ᵥ v) := by
      have hF' := hF
      unfold IsFrame at hF'
      obtain ⟨-, -, -, -, -, -, hsum⟩ := hF'
      have := congrArg (· *ᵥ v) hsum
      simp only [Matrix.one_mulVec, Matrix.add_mulVec, Matrix.sum_mulVec, ← Matrix.mulVec_mulVec, hBJ,
        Matrix.mulVec_zero, Finset.sum_const_zero, add_zero] at this
      exact this.symm
    rw [hdec, Matrix.mulVec_add]
    refine add_mem ?_ ?_
    · refine map_mem hB _ (W (Fin.last a)) (fun i _ u => ?_)
        ((hB _ _).2 ⟨_, fun i hi => absurd (hlast i) hi, rfl⟩)
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hMB i, Matrix.sub_mulVec]
      refine sub_mem ?_ (col_mem hB (hlast i) u)
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      exact hG _ _ (col_mem hB (hlast i) _)
    · rw [Matrix.mulVec_mulVec, hNB₀, Matrix.sub_mulVec]
      refine sub_mem ?_ ?_
      · rw [← Matrix.mulVec_mulVec]
        exact hD _
      · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
        exact hG _ _ (hD _)

end GlobalTheory.LeviUnip
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagStabilizerMulInvLeviComponentMemUnipotentStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagStabilizer_mul_inv_leviComponent_mem_unipotent : ∀ (n n₀ a : ℕ) (j : Fin a → ℕ) (ε : Fin n → Bool) (ε₀ : Fin n₀ → Bool) (B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (B₀ : Matrix (Fin n) (Fin n₀) ℂ), IsFrame ε ε₀ B B₀ → ∀ (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) (A : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (A₀ : Matrix (Fin n) (Fin n₀) ℂ) (p : ∀ k i, Matrix (Fin (j k)) (Fin (j i)) ℂ) (d : ∀ k, Matrix (Fin (j k)) (Fin n₀) ℂ) (s h : Formalism.REAL.UJ ε₀) (y : ∀ i, Matrix (Fin (j i)) (Fin (j i)) ℂ) (g m : Formalism.REAL.UJ ε), SpansFlag A W → SpansFlag B W → (∀ k i, i < k → p k i = 0) → (∀ i, (p i i).det ≠ 0) → (∀ i, A i = ∑ k, B k * p k i) → A₀ = B₀ * uMat s + ∑ k, B k * d k → (∀ i, (y i).det ≠ 0) → (∀ i, uMat g * A i = A i * y i) → uMat g * A₀ = A₀ * uMat h → uMat m = lev ε B B₀ (fun i => p i i * y i * (p i i)⁻¹) (uMat (s * h * s⁻¹)) → g * m⁻¹ ∈ flagN ε W := by
  first | exact @GlobalTheory.LeviUnip.mul_inv_mem_flagN | exact GlobalTheory.LeviUnip.mul_inv_mem_flagN | (intros; apply GlobalTheory.LeviUnip.mul_inv_mem_flagN <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnBlocksSpanFlagOfBlockTriangular
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnBlocksSpanFlagOfBlockTriangular
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

namespace GlobalTheory.LeviIso

theorem exists_sum_mulVec_of_triangular {n a : ℕ} {j : Fin a → ℕ} (A B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ)
    (p : ∀ k i, Matrix (Fin (j k)) (Fin (j i)) ℂ) (hp : ∀ k i, i < k → p k i = 0)
    (hA : ∀ i, A i = ∑ k, B k * p k i) (l : Fin (a + 1)) (u : ∀ i, Fin (j i) → ℂ)
    (hu : ∀ i : Fin a, ¬ i.castSucc < l → u i = 0) :
    ∃ v : ∀ i, Fin (j i) → ℂ, (∀ i : Fin a, ¬ i.castSucc < l → v i = 0) ∧
      ∑ i, A i *ᵥ u i = ∑ i, B i *ᵥ v i := by
  refine ⟨fun k => ∑ i, p k i *ᵥ u i, ?_, ?_⟩
  · intro k hk
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hik : i < k
    · rw [hp k i hik, Matrix.zero_mulVec]
    · have hki : k ≤ i := not_lt.mp hik
      have hi : ¬ i.castSucc < l := fun hi =>
        hk (lt_of_le_of_lt (Fin.castSucc_le_castSucc_iff.mpr hki) hi)
      rw [hu i hi, Matrix.mulVec_zero]
  · simp_rw [hA, Matrix.sum_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_sum]
    exact Finset.sum_comm

theorem spansFlag_of_triangular (n a : ℕ) (j : Fin a → ℕ) (A B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ)
    (p q : ∀ k i, Matrix (Fin (j k)) (Fin (j i)) ℂ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ))
    (hpq : ∀ k i, i < k → p k i = 0 ∧ q k i = 0) (hA : ∀ i, A i = ∑ k, B k * p k i)
    (hB : ∀ i, B i = ∑ k, A k * q k i) (h : SpansFlag A W) : SpansFlag B W := by
  intro k y
  rw [h k y]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact exists_sum_mulVec_of_triangular A B p (fun k i hik => (hpq k i hik).1) hA k u hu
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨w, hw, he⟩ :=
      exists_sum_mulVec_of_triangular B A q (fun k i hik => (hpq k i hik).2) hB k v hv
    exact ⟨w, hw, he⟩

end GlobalTheory.LeviIso
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnBlocksSpanFlagOfBlockTriangularStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnBlocksSpanFlag_of_block_triangular : ∀ (n a : ℕ) (j : Fin a → ℕ) (A B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (p q : ∀ k i, Matrix (Fin (j k)) (Fin (j i)) ℂ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), (∀ k i, i < k → p k i = 0 ∧ q k i = 0) → (∀ i, A i = ∑ k, B k * p k i) → (∀ i, B i = ∑ k, A k * q k i) → SpansFlag A W → SpansFlag B W := by
  first | exact @GlobalTheory.LeviIso.spansFlag_of_triangular | exact GlobalTheory.LeviIso.spansFlag_of_triangular | (intros; apply GlobalTheory.LeviIso.spansFlag_of_triangular <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMeasurableUnitaryLeviBlockMap
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMeasurableUnitaryLeviBlockMap
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso
open Formalism.REAL (Jm UJ inUJ isClosedEmbeddingMatrix)

noncomputable section

namespace GlobalTheory.LeviIso

theorem measurable_matInv (m : ℕ) :
    Measurable fun x : Fin m → Fin m → ℂ => (fun r s => (Matrix.of x)⁻¹ r s : Fin m → Fin m → ℂ) := by

  have hdet : Continuous fun x : Fin m → Fin m → ℂ => (Matrix.of x).det :=
    (continuous_id (X := Matrix (Fin m) (Fin m) ℂ)).matrix_det
  have hadj : Continuous fun x : Fin m → Fin m → ℂ => (Matrix.of x).adjugate :=
    (continuous_id (X := Matrix (Fin m) (Fin m) ℂ)).matrix_adjugate
  refine Measurable.of_eval fun r => Measurable.of_eval fun s => ?_
  have key : (fun x : Fin m → Fin m → ℂ => (Matrix.of x)⁻¹ r s) =
      fun x => ((Matrix.of x).det)⁻¹ * (Matrix.of x).adjugate r s := by
    funext x
    rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  rw [key]
  exact (hdet.measurable.inv).mul
    (((continuous_apply s).comp ((continuous_apply r).comp hadj)).measurable)

theorem measurableEmbedding_uMat {n : ℕ} (ε : Fin n → Bool) :
    MeasurableEmbedding fun g : UJ ε => (fun r s => uMat g r s : Fin n → Fin n → ℂ) := by

  have h : Topology.IsClosedEmbedding fun g : UJ ε => (fun r s => uMat g r s : Fin n → Fin n → ℂ) :=
    (isClosedEmbeddingMatrix n ε).1
  exact h.measurableEmbedding

theorem measurable_lev {n n₀ a : ℕ} {j : Fin a → ℕ} (ε : Fin n → Bool) (ε₀ : Fin n₀ → Bool)
    (B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (B₀ : Matrix (Fin n) (Fin n₀) ℂ) :
    Measurable fun z : (∀ i, Fin (j i) → Fin (j i) → ℂ) × UJ ε₀ =>
      (fun r s => lev ε B B₀ (fun i => Matrix.of (z.1 i)) (uMat z.2) r s : Fin n → Fin n → ℂ) := by

  let Φ : (∀ i, Fin (j i) → Fin (j i) → ℂ) × (∀ i, Fin (j i) → Fin (j i) → ℂ) × (Fin n₀ → Fin n₀ → ℂ) →
      Fin n → Fin n → ℂ := fun w r s =>
    (∑ i, B i * Matrix.of (w.1 i) * (B i)ᴴ + ∑ i, Jm ε * B i * (Matrix.of (w.2.1 i))ᴴ * (B i)ᴴ * Jm ε +
      B₀ * Matrix.of w.2.2 * B₀ᴴ) r s
  have hΦ : Continuous Φ := by
    refine continuous_pi fun r => continuous_pi fun s => ?_
    refine Continuous.matrix_elem ?_ r s
    refine Continuous.add (Continuous.add ?_ ?_) ?_
    · refine continuous_finsetSum _ fun i _ => ?_
      exact (continuous_const.matrix_mul
        ((continuous_apply i).comp continuous_fst : Continuous fun w : (∀ i, Fin (j i) → Fin (j i) → ℂ) ×
          (∀ i, Fin (j i) → Fin (j i) → ℂ) × (Fin n₀ → Fin n₀ → ℂ) => (Matrix.of (w.1 i)))).matrix_mul
        continuous_const
    · refine continuous_finsetSum _ fun i _ => ?_
      exact ((continuous_const.matrix_mul
        ((continuous_apply i).comp (continuous_fst.comp continuous_snd) : Continuous fun w :
          (∀ i, Fin (j i) → Fin (j i) → ℂ) × (∀ i, Fin (j i) → Fin (j i) → ℂ) × (Fin n₀ → Fin n₀ → ℂ) =>
            (Matrix.of (w.2.1 i))).matrix_conjTranspose).matrix_mul continuous_const).matrix_mul
        continuous_const
    · exact (continuous_const.matrix_mul
        ((continuous_snd.comp continuous_snd) : Continuous fun w : (∀ i, Fin (j i) → Fin (j i) → ℂ) ×
          (∀ i, Fin (j i) → Fin (j i) → ℂ) × (Fin n₀ → Fin n₀ → ℂ) => (Matrix.of w.2.2))).matrix_mul
        continuous_const
  have hinv : Measurable fun z : (∀ i, Fin (j i) → Fin (j i) → ℂ) × UJ ε₀ =>
      (fun i r s => (Matrix.of (z.1 i))⁻¹ r s : ∀ i, Fin (j i) → Fin (j i) → ℂ) :=
    Measurable.of_eval fun i =>
      (measurable_matInv (j i)).comp ((measurable_pi_apply i).comp measurable_fst)
  have hg : Measurable fun z : (∀ i, Fin (j i) → Fin (j i) → ℂ) × UJ ε₀ =>
      (fun r s => uMat z.2 r s : Fin n₀ → Fin n₀ → ℂ) :=
    (measurableEmbedding_uMat ε₀).measurable.comp measurable_snd
  have hcomp := hΦ.measurable.comp (measurable_fst.prodMk (hinv.prodMk hg))
  convert hcomp using 1
  funext z r s
  simp only [Function.comp_apply, Φ, lev]
  rfl

theorem exists_measurable_levMap (n n₀ a : ℕ) (j : Fin a → ℕ) (ε : Fin n → Bool) (ε₀ : Fin n₀ → Bool)
    (B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (B₀ : Matrix (Fin n) (Fin n₀) ℂ) (h : IsFrame ε ε₀ B B₀) :
    ∃ θ : (∀ i, Fin (j i) → Fin (j i) → ℂ) × UJ ε₀ → UJ ε, Measurable θ ∧
      ∀ z, (∀ i, (Matrix.of (z.1 i)).det ≠ 0) →
        uMat (θ z) = lev ε B B₀ (fun i => Matrix.of (z.1 i)) (uMat z.2) := by
  classical

  let S : Set ((∀ i, Fin (j i) → Fin (j i) → ℂ) × UJ ε₀) := {z | ∀ i, (Matrix.of (z.1 i)).det ≠ 0}
  have hex : ∀ z ∈ S, ∃ g : UJ ε, uMat g = lev ε B B₀ (fun i => Matrix.of (z.1 i)) (uMat z.2) := by
    intro z hz
    have hU : inUJ ε (lev ε B B₀ (fun i => Matrix.of (z.1 i)) (uMat z.2)) := h.inUJ_lev _ _ hz z.2.2
    have hr : lev ε B B₀ (fun i => Matrix.of (z.1 i)) (uMat z.2) ∈
        Set.range (fun g : UJ ε => ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) := by
      rw [(isClosedEmbeddingMatrix n ε).2]
      exact hU
    obtain ⟨g, hg⟩ := hr
    exact ⟨g, hg⟩
  let θ : (∀ i, Fin (j i) → Fin (j i) → ℂ) × UJ ε₀ → UJ ε := fun z =>
    if hz : z ∈ S then (hex z hz).choose else 1
  have hθ : ∀ z ∈ S, uMat (θ z) = lev ε B B₀ (fun i => Matrix.of (z.1 i)) (uMat z.2) := by
    intro z hz
    simp only [θ, dif_pos hz]
    exact (hex z hz).choose_spec
  refine ⟨θ, ?_, fun z hz => hθ z hz⟩
  have hdet : ∀ i, Measurable fun z : (∀ i, Fin (j i) → Fin (j i) → ℂ) × UJ ε₀ => (Matrix.of (z.1 i)).det :=
    fun i =>
      have hc : Continuous fun x : Fin (j i) → Fin (j i) → ℂ => (Matrix.of x).det :=
        (continuous_id (X := Matrix (Fin (j i)) (Fin (j i)) ℂ)).matrix_det
      hc.measurable.comp ((measurable_pi_apply i).comp measurable_fst)
  have hS : MeasurableSet S := by
    have : S = ⋂ i, (fun z : (∀ i, Fin (j i) → Fin (j i) → ℂ) × UJ ε₀ => (Matrix.of (z.1 i)).det) ⁻¹' {0}ᶜ := by
      ext z
      simp [S]
    rw [this]
    exact MeasurableSet.iInter fun i => (hdet i) (measurableSet_singleton 0).compl
  rw [← (measurableEmbedding_uMat ε).measurable_comp_iff]
  have heq : ((fun g : UJ ε => (fun r s => uMat g r s : Fin n → Fin n → ℂ)) ∘ θ) = fun z =>
      if z ∈ S then (fun r s => lev ε B B₀ (fun i => Matrix.of (z.1 i)) (uMat z.2) r s : Fin n → Fin n → ℂ)
      else (fun r s => uMat (1 : UJ ε) r s) := by
    funext z
    by_cases hz : z ∈ S
    · simp only [Function.comp_apply, if_pos hz, hθ z hz]
    · simp only [Function.comp_apply, if_neg hz, θ, dif_neg hz]
  rw [heq]
  exact Measurable.ite hS (measurable_lev ε ε₀ B B₀) measurable_const

end GlobalTheory.LeviIso
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMeasurableUnitaryLeviBlockMapStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_measurable_unitaryLeviBlockMap : ∀ (n n₀ a : ℕ) (j : Fin a → ℕ) (ε : Fin n → Bool) (ε₀ : Fin n₀ → Bool) (B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (B₀ : Matrix (Fin n) (Fin n₀) ℂ), IsFrame ε ε₀ B B₀ → ∃ θ : (∀ i, Fin (j i) → Fin (j i) → ℂ) × Formalism.REAL.UJ ε₀ → Formalism.REAL.UJ ε, Measurable θ ∧ ∀ z, (∀ i, (Matrix.of (z.1 i)).det ≠ 0) → uMat (θ z) = lev ε B B₀ (fun i => Matrix.of (z.1 i)) (uMat z.2) := by
  first | exact @GlobalTheory.LeviIso.exists_measurable_levMap | exact GlobalTheory.LeviIso.exists_measurable_levMap | (intros; apply GlobalTheory.LeviIso.exists_measurable_levMap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ComplementaryBlockUnitaryForms
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

noncomputable section

namespace GlobalTheory.LeviIso.Chart

def twist {j : ℕ} (p : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ →+* ℂ) (x : Fin j → Fin j → ℂ) : Fin j → Fin j → ℂ :=
  fun r s => (p * (Matrix.of x).map τ * p⁻¹) r s

theorem of_twist {j : ℕ} (p : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ →+* ℂ) (x : Fin j → Fin j → ℂ) :
    Matrix.of (twist p τ x) = p * (Matrix.of x).map τ * p⁻¹ := rfl

variable {j : ℕ} {p : Matrix (Fin j) (Fin j) ℂ} {τ : ℂ →+* ℂ}

theorem norm_tau (hτ : τ = RingHom.id ℂ ∨ τ = starRingEnd ℂ) (z : ℂ) : ‖τ z‖ = ‖z‖ := by
  rcases hτ with rfl | rfl <;> simp

theorem tau_tau (hτ : τ = RingHom.id ℂ ∨ τ = starRingEnd ℂ) (z : ℂ) : τ (τ z) = z := by
  rcases hτ with rfl | rfl <;> simp

theorem det_map_tau (x : Matrix (Fin j) (Fin j) ℂ) : (x.map τ).det = τ x.det := by
  rw [RingHom.map_det]; rfl

theorem det_twist (hp : p.det ≠ 0) (x : Fin j → Fin j → ℂ) :
    (Matrix.of (twist p τ x)).det = τ (Matrix.of x).det := by
  rw [of_twist, Matrix.det_mul, Matrix.det_mul, mul_right_comm, ← Matrix.det_mul,
    Matrix.mul_nonsing_inv _ (Ne.isUnit hp), Matrix.det_one, one_mul, det_map_tau]

theorem det_twist_ne (hp : p.det ≠ 0) {x : Fin j → Fin j → ℂ} (hx : (Matrix.of x).det ≠ 0) :
    (Matrix.of (twist p τ x)).det ≠ 0 := by
  rw [det_twist hp]
  exact (map_ne_zero τ).2 hx

theorem twist_mul (hp : p.det ≠ 0) (x y : Fin j → Fin j → ℂ) :
    Matrix.of (twist p τ fun r s => (Matrix.of x * Matrix.of y) r s) =
      Matrix.of (twist p τ x) * Matrix.of (twist p τ y) := by
  have e : (Matrix.of fun r s => (Matrix.of x * Matrix.of y) r s) = Matrix.of x * Matrix.of y := rfl
  rw [of_twist, of_twist, of_twist, e, Matrix.map_mul]
  simp only [Matrix.mul_assoc]
  rw [Matrix.nonsing_inv_mul_cancel_left _ _ (Ne.isUnit hp)]

theorem twist_inj (hp : p.det ≠ 0) {x y : Fin j → Fin j → ℂ}
    (h : Matrix.of (twist p τ x) = Matrix.of (twist p τ y)) : x = y := by
  have h2 := congrArg (fun M => p⁻¹ * (M * p)) h
  simp only [of_twist, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (Ne.isUnit hp), Matrix.mul_one,
    Matrix.nonsing_inv_mul_cancel_left _ _ (Ne.isUnit hp)] at h2
  funext r s
  exact τ.injective (congrFun (congrFun h2 r) s)

theorem twist_surj (hτ : τ = RingHom.id ℂ ∨ τ = starRingEnd ℂ) (hp : p.det ≠ 0) (y : Matrix (Fin j) (Fin j) ℂ) :
    ∃ x, Matrix.of (twist p τ x) = y := by
  refine ⟨fun r s => τ ((p⁻¹ * y * p) r s), ?_⟩
  have e : (Matrix.of fun r s => τ ((p⁻¹ * y * p) r s)).map τ = p⁻¹ * y * p := by
    ext r s
    simp only [Matrix.map_apply, Matrix.of_apply, tau_tau hτ]
  rw [of_twist, e]
  simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (Ne.isUnit hp), Matrix.mul_one,
    Matrix.mul_nonsing_inv_cancel_left _ _ (Ne.isUnit hp)]

theorem measurePreserving_twist (hτ : τ = RingHom.id ℂ ∨ τ = starRingEnd ℂ) (hp : p.det ≠ 0) :
    MeasurePreserving (twist p τ) (haarLoc j) (haarLoc j) := by
  have hq : p⁻¹.det ≠ 0 := (Matrix.isUnit_nonsing_inv_det p (Ne.isUnit hp)).ne_zero
  have h1 := GlobalTheory.HaarMul.measurePreserving_mul_mul j p p⁻¹ hp hq
  rcases hτ with rfl | rfl
  · exact h1
  · exact h1.comp (haarLoc_conj_and_null j).1

theorem uMat_injective {n : ℕ} {ε : Fin n → Bool} {g h : Formalism.REAL.UJ ε} (e : uMat g = uMat h) : g = h :=
  Subtype.ext (Units.ext e)

theorem exists_leviChart : ∀ (n n₀ a : ℕ) (j : Fin a → ℕ) (ε : Fin n → Bool) (ε₀ : Fin n₀ → Bool) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) (A : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (C : ∀ i, Matrix (Fin (j i)) (Fin n) ℂ) (A₀ : Matrix (Fin n) (Fin n₀) ℂ) (τ τ₀ : ℂ →+* ℂ), (τ = RingHom.id ℂ ∨ τ = starRingEnd ℂ) → (τ₀ = RingHom.id ℂ ∨ τ₀ = starRingEnd ℂ) → n = n₀ + 2 * ∑ i, j i → (∀ i, C i * A i = 1) → (∀ i k, i ≠ k → C i * A k = 0) → (∀ i k, (A i)ᴴ * Formalism.REAL.Jm ε * A k = 0) → (∀ i, (A i)ᴴ * Formalism.REAL.Jm ε * A₀ = 0) → A₀ᴴ * Formalism.REAL.Jm ε * A₀ = Formalism.REAL.Jm ε₀ → SpansFlag A W → IsIsoFlag ε j W → ∃ θ, IsLeviChart ε ε₀ W A A₀ τ τ₀ θ := by
  intro n n₀ a j ε ε₀ W A C A₀ τ τ₀ hτ hτ₀ hn hC1 hC0 hAA hA0 h00 hsp hiso
  obtain ⟨B, p, q, hB1, hB0, htri, hAB, hBA, hpq⟩ := BlockGS.block_gramSchmidt n a j A C hC1 hC0
  have hspB : SpansFlag B W := GlobalTheory.T.columnBlocksSpanFlag_of_block_triangular n a j A B p q W htri hAB hBA hsp
  have hBJA : ∀ (m : ℕ) (X : Matrix (Fin n) (Fin m) ℂ), (∀ i, (A i)ᴴ * Formalism.REAL.Jm ε * X = 0) →
      ∀ i, (B i)ᴴ * Formalism.REAL.Jm ε * X = 0 := by
    intro m X hX i
    rw [hBA i, Matrix.conjTranspose_sum, Matrix.sum_mul, Matrix.sum_mul]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc (q k i)ᴴ, Matrix.mul_assoc (q k i)ᴴ, hX, Matrix.mul_zero]
  have hBJB : ∀ i k, (B i)ᴴ * Formalism.REAL.Jm ε * B k = 0 := by
    intro i k
    refine hBJA _ _ (fun l => ?_) i
    rw [hBA k, Matrix.mul_sum]
    refine Finset.sum_eq_zero fun m _ => ?_
    rw [← Matrix.mul_assoc, hAA, Matrix.zero_mul]
  obtain ⟨B₀, s, d, hF, hA₀⟩ := GlobalTheory.T.exists_orthonormalFrame_of_isotropicBlocks n n₀ a j ε ε₀ B A₀ hn hB1 hB0 hBJB (hBJA _ _ hA0) h00
  obtain ⟨θ₀, hθm, hθ⟩ := GlobalTheory.T.exists_measurable_unitaryLeviBlockMap n n₀ a j ε ε₀ B B₀ hF
  obtain ⟨C₀, hC₀, hC₀m⟩ := exists_conj_gauge_invariant n₀ ε₀ τ₀ hτ₀
  have hp : ∀ i, (p i i).det ≠ 0 := fun i => (Matrix.isUnit_det_of_right_inverse (hpq i)).ne_zero
  let R : (∀ i, Fin (j i) → Fin (j i) → ℂ) × Formalism.REAL.UJ ε₀ → (∀ i, Fin (j i) → Fin (j i) → ℂ) × Formalism.REAL.UJ ε₀ :=
    Prod.map (fun x i => twist (p i i) τ (x i)) (fun g => s * C₀ g * s⁻¹)
  have hcont : Continuous fun g : Formalism.REAL.UJ ε₀ => s * C₀ g * s⁻¹ :=
    (continuous_const.mul C₀.continuous_toFun).mul continuous_const
  have hR1 : Measurable fun (x : ∀ i, Fin (j i) → Fin (j i) → ℂ) i => twist (p i i) τ (x i) :=
    Measurable.of_eval fun i =>
      (measurePreserving_twist hτ (hp i)).measurable.comp (measurable_pi_apply i)
  have hRm : Measurable R := hR1.prodMap hcont.measurable
  have hθR : ∀ z, (∀ i, (Matrix.of (z.1 i)).det ≠ 0) → uMat (θ₀ (R z)) =
      lev ε B B₀ (fun i => Matrix.of (twist (p i i) τ (z.1 i))) (uMat (s * C₀ z.2 * s⁻¹)) :=
    fun z hz => hθ (R z) fun i => det_twist_ne (hp i) (hz i)
  refine ⟨θ₀ ∘ R, hθm.comp hRm, fun m => ?_, fun z z' hz hz' => ⟨?_, fun e => ?_⟩,
    fun z hz => ⟨fun i => ?_, fun g hg hg0 => ?_⟩, fun μ c hμ hc => ?_⟩
  · rw [GlobalTheory.T.mem_isotropicFlagSelfAdjointLevi_iff_block n n₀ a j ε ε₀ B B₀ hF W hspB m]
    constructor
    · rintro ⟨x, g, hx, hm⟩
      choose y hy using fun i => twist_surj hτ (hp i) (x i)
      have hy0 : ∀ i, (Matrix.of (y i)).det ≠ 0 := by
        intro i h0
        apply hx i
        rw [← hy i, det_twist (hp i), h0, map_zero]
      refine ⟨(y, C₀.symm (s⁻¹ * g * s)), hy0, uMat_injective ?_⟩
      have e : s * C₀ (C₀.symm (s⁻¹ * g * s)) * s⁻¹ = g := by
        rw [ContinuousMulEquiv.apply_symm_apply]; group
      rw [Function.comp_apply, hθR _ hy0, hm]
      simp only [hy, e]
    · rintro ⟨z, hz, rfl⟩
      exact ⟨_, _, fun i => det_twist_ne (hp i) (hz i), hθR z hz⟩
  · apply uMat_injective
    have hzz : ∀ i, (Matrix.of fun r s => (Matrix.of (z.1 i) * Matrix.of (z'.1 i)) r s).det ≠ 0 := by
      intro i
      change (Matrix.of (z.1 i) * Matrix.of (z'.1 i)).det ≠ 0
      rw [Matrix.det_mul]
      exact mul_ne_zero (hz i) (hz' i)
    have e : uMat (s * C₀ (z.2 * z'.2) * s⁻¹) = uMat (s * C₀ z.2 * s⁻¹) * uMat (s * C₀ z'.2 * s⁻¹) := by
      change _ = uMat ((s * C₀ z.2 * s⁻¹) * (s * C₀ z'.2 * s⁻¹))
      congr 1
      rw [map_mul]; group
    change uMat (θ₀ (R z)) * uMat (θ₀ (R z')) = uMat (θ₀ (R _))
    rw [hθR z hz, hθR z' hz', hθR _ hzz, ← hF.lev_mul]
    simp only [twist_mul (hp _), e]
  · have e2 : uMat (θ₀ (R z)) = uMat (θ₀ (R z')) := congrArg uMat e
    rw [hθR z hz, hθR z' hz'] at e2
    obtain ⟨e3, e4⟩ := hF.lev_inj _ _ _ _ e2
    refine Prod.ext (funext fun i => twist_inj (τ := τ) (hp i) (congrFun e3 i)) ?_
    have e5 := uMat_injective e4
    exact C₀.injective (mul_left_cancel (mul_right_cancel e5))
  · rw [Function.comp_apply, Size.locSize_blocks n a j B W hB1 hB0 hspB _
      (fun i => Matrix.of (twist (p i i) τ (z.1 i))) (fun i => det_twist_ne (hp i) (hz i))
      (fun i => by rw [hθR z hz, hF.lev_mul_B]) i, det_twist (hp i), norm_tau hτ]
  · refine GlobalTheory.T.flagStabilizer_mul_inv_leviComponent_mem_unipotent n n₀ a j ε ε₀ B B₀ hF W A A₀ p d s (C₀ z.2) (fun i => (Matrix.of (z.1 i)).map τ) g _
      hsp hspB (fun k i h => (htri k i h).1) hp hAB hA₀ (fun i => ?_) hg (by rw [hC₀]; exact hg0) (hθR z hz)
    rw [det_map_tau]
    exact (map_ne_zero τ).2 (hz i)
  · have hR : MeasurePreserving R
        ((Measure.pi fun i => ENNReal.ofReal (2 ^ (j i ^ 2)) • haarLoc (j i)).prod
          (ENNReal.ofReal c • Formalism.REAL.muG ε₀))
        ((Measure.pi fun i => ENNReal.ofReal (2 ^ (j i ^ 2)) • haarLoc (j i)).prod
          (ENNReal.ofReal c • Formalism.REAL.muG ε₀)) := by
      refine MeasurePreserving.prod ?_ ⟨hcont.measurable, hC₀m s c hc⟩
      exact measurePreserving_pi _ _ fun i => (measurePreserving_twist hτ (hp i)).smul_measure _
    rw [← Measure.map_map hθm hRm, hR.map_eq]
    obtain ⟨g1, g2⟩ := GlobalTheory.T.levi_chart_map_haar_carried_invariant n n₀ a j ε ε₀ B B₀ hF W hspB θ₀ hθm hθ c
    have g3 := GlobalTheory.T.isRadial_map_unitaryLeviBlockProduct n n₀ a j ε ε₀ B B₀ hF θ₀ hθm hθ c hc
    have hν : IsGaugeSub (flagM ε W) (n₀ ^ 2 + 2 * ∑ i, j i ^ 2) _ := ⟨g1, g2, g3⟩
    have hd : n - 2 * ∑ i, j i = n₀ := by omega
    have halg := GlobalTheory.LeviAlgebra.exists_levi_algebra n ε a j W hiso
    rw [hd] at halg
    obtain ⟨𝒜, E, a1, a2, a3, a4⟩ := halg
    rw [a4] at hμ hν
    exact (GlobalTheory.T.gaugeMeasure_matrixAlgebraSubgroup_local_asymptotics n ε 𝒜 _ E a1 a2 a3 _ hν).2.2.1 μ hμ

end GlobalTheory.LeviIso.Chart
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ComplementaryBlockUnitaryFormsStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complementary_block_unitary_forms : ∀ (n n₀ a : ℕ) (j : Fin a → ℕ) (ε : Fin n → Bool) (ε₀ : Fin n₀ → Bool) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) (A : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (C : ∀ i, Matrix (Fin (j i)) (Fin n) ℂ) (A₀ : Matrix (Fin n) (Fin n₀) ℂ) (τ τ₀ : ℂ →+* ℂ), (τ = RingHom.id ℂ ∨ τ = starRingEnd ℂ) → (τ₀ = RingHom.id ℂ ∨ τ₀ = starRingEnd ℂ) → n = n₀ + 2 * ∑ i, j i → (∀ i, C i * A i = 1) → (∀ i k, i ≠ k → C i * A k = 0) → (∀ i k, (A i)ᴴ * Formalism.REAL.Jm ε * A k = 0) → (∀ i, (A i)ᴴ * Formalism.REAL.Jm ε * A₀ = 0) → A₀ᴴ * Formalism.REAL.Jm ε * A₀ = Formalism.REAL.Jm ε₀ → SpansFlag A W → IsIsoFlag ε j W → ∃ θ, IsLeviChart ε ε₀ W A A₀ τ τ₀ θ := by
  first | exact @GlobalTheory.LeviIso.Chart.exists_leviChart | exact GlobalTheory.LeviIso.Chart.exists_leviChart | (intros; apply GlobalTheory.LeviIso.Chart.exists_leviChart <;> assumption)
end
