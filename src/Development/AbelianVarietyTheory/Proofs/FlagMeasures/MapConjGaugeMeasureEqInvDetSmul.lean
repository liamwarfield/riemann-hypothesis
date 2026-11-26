module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaugeMeasureMatrixAlgebraSubgroupLocalAsymptotic

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryJLieCoordsConjLinear
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryJLieCoordsConjLinear
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

noncomputable section

namespace GlobalTheory.UnitaryCoords

open Formalism.REAL

lemma re_trace_eq_zero {n : ℕ} (J Z Y : Matrix (Fin n) (Fin n) ℂ) (hJ : J * J = 1)
    (hZ : Zᴴ * J = J * Z) (hY : Yᴴ * J + J * Y = 0) : ((Z * Yᴴ).trace).re = 0 := by
  have hY' : Yᴴ = -(J * Y * J) := by
    have h1 : Yᴴ * J = -(J * Y) := eq_neg_of_add_eq_zero_left hY
    calc Yᴴ = Yᴴ * J * J := by rw [Matrix.mul_assoc, hJ, Matrix.mul_one]
      _ = _ := by rw [h1, Matrix.neg_mul]
  have hZ' : Zᴴ = J * Z * J := by
    calc Zᴴ = Zᴴ * J * J := by rw [Matrix.mul_assoc, hJ, Matrix.mul_one]
      _ = _ := by rw [hZ]
  have h1 : ((Z * Yᴴ).trace).re = ((Y * Zᴴ).trace).re := by
    have : Y * Zᴴ = (Z * Yᴴ)ᴴ := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    rw [this, Matrix.trace_conjTranspose]
    simp
  have h2 : (Y * Zᴴ).trace = -(Z * Yᴴ).trace := by
    rw [hZ', hY', Matrix.mul_neg, Matrix.trace_neg, neg_neg]
    calc (Y * (J * Z * J)).trace = ((Y * J) * (Z * J)).trace := by simp only [Matrix.mul_assoc]
      _ = ((Z * J) * (Y * J)).trace := Matrix.trace_mul_comm _ _
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [h2, Complex.neg_re] at h1
  linarith

lemma uMat_mul' {n : ℕ} {ε : Fin n → Bool} (a b : UJ ε) : uMat (a * b) = uMat a * uMat b := rfl

lemma uMat_mul_inv' {n : ℕ} {ε : Fin n → Bool} (a : UJ ε) : uMat a * uMat a⁻¹ = 1 := by
  rw [← uMat_mul', mul_inv_cancel]; rfl

lemma conjTranspose_mul_J {n : ℕ} {ε : Fin n → Bool} (a : UJ ε) :
    (uMat a)ᴴ * Jm ε = Jm ε * uMat a⁻¹ := by
  have h : (uMat a)ᴴ * Jm ε * uMat a = Jm ε := a.2
  calc (uMat a)ᴴ * Jm ε = (uMat a)ᴴ * Jm ε * (uMat a * uMat a⁻¹) := by
        rw [uMat_mul_inv', Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, h]

lemma inv_conjTranspose_mul_J {n : ℕ} {ε : Fin n → Bool} (a : UJ ε) :
    (uMat a⁻¹)ᴴ * Jm ε = Jm ε * uMat a := by
  simpa using conjTranspose_mul_J a⁻¹

lemma coord_eq {n : ℕ} {ε : Fin n → Bool} (a : UJ ε) (Y : Matrix (Fin n) (Fin n) ℂ) (hY : inG ε Y) :
    2 * (((uMat a - 1) * Yᴴ).trace).re = (((uMat a - uMat a⁻¹) * Yᴴ).trace).re := by
  have h := re_trace_eq_zero (Jm ε) (uMat a + uMat a⁻¹ - 1 - 1) Y (Jm_mul_self ε) (by
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_add, Matrix.conjTranspose_one,
      Matrix.sub_mul, Matrix.add_mul, Matrix.mul_sub, Matrix.mul_add, conjTranspose_mul_J a,
      inv_conjTranspose_mul_J a, Matrix.one_mul, Matrix.mul_one]
    abel) hY
  simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.trace_sub, Matrix.trace_add, Complex.sub_re,
    Complex.add_re] at h ⊢
  linarith

lemma inG_sub_inv {n : ℕ} {ε : Fin n → Bool} (a : UJ ε) : inG ε (uMat a - uMat a⁻¹) := by
  unfold inG
  simp only [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, conjTranspose_mul_J a,
    inv_conjTranspose_mul_J a]
  abel

lemma coord_sum {n d : ℕ} (E : Fin d → Matrix (Fin n) (Fin n) ℂ)
    (hE : ∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) (t : Fin d → ℝ) (i : Fin d) :
    (((∑ k, t k • E k) * (E i)ᴴ).trace).re = t i := by
  rw [Finset.sum_mul, Matrix.trace_sum, Complex.re_sum]
  simp only [Matrix.smul_mul, Matrix.trace_smul, Complex.smul_re, hE]
  simp

theorem coords_conj : ∀ (n : ℕ) (ε : Fin n → Bool) (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), (∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) → (∀ X, (X ∈ A ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E)) → ∀ (g m : Formalism.REAL.UJ ε) (L : Matrix (Fin d) (Fin d) ℝ), uMat g - 1 ∈ A → uMat g⁻¹ - 1 ∈ A → (∀ k, uMat m * E k * uMat m⁻¹ = ∑ i, L i k • E i) → (fun i => (((uMat (m * g * m⁻¹) - 1) * (E i)ᴴ).trace).re) = L *ᵥ (fun i => (((uMat g - 1) * (E i)ᴴ).trace).re) := by
  intro n ε A d E hE hA g m L hg hg' hL
  have hEG : ∀ i, inG ε (E i) := fun i =>
    ((hA (E i)).2 (Submodule.subset_span ⟨i, rfl⟩)).2
  have hX : uMat g - uMat g⁻¹ ∈ Submodule.span ℝ (Set.range E) := by
    refine (hA _).1 ⟨?_, inG_sub_inv g⟩
    have := A.sub_mem hg hg'
    simpa using this
  obtain ⟨t, ht⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hX
  have h1 : ∀ i, 2 * (((uMat g - 1) * (E i)ᴴ).trace).re = t i := fun i => by
    rw [coord_eq g _ (hEG i), ← ht, coord_sum E hE]
  have h2 : uMat (m * g * m⁻¹) - uMat (m * g * m⁻¹)⁻¹ = ∑ i, (∑ k, L i k * t k) • E i := by
    have e : (m * g * m⁻¹)⁻¹ = m * g⁻¹ * m⁻¹ := by group
    rw [e, uMat_mul', uMat_mul', uMat_mul', uMat_mul', ← Matrix.sub_mul, ← Matrix.mul_sub, ← ht,
      Finset.mul_sum, Finset.sum_mul]
    simp only [Matrix.mul_smul, Matrix.smul_mul, hL, Finset.smul_sum, Finset.sum_smul, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm]
  funext i
  have h3 := coord_eq (m * g * m⁻¹) _ (hEG i)
  rw [h2, coord_sum E hE] at h3
  simp only [Matrix.mulVec, dotProduct]
  have h4 : ∑ k, L i k * t k = 2 * ∑ k, L i k * (((uMat g - 1) * (E k)ᴴ).trace).re := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← h1 k]; ring
  linarith

end GlobalTheory.UnitaryCoords
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryJLieCoordsConjLinearStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryJ_lieCoords_conj_linear : ∀ (n : ℕ) (ε : Fin n → Bool) (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), (∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) → (∀ X, (X ∈ A ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E)) → ∀ (g m : Formalism.REAL.UJ ε) (L : Matrix (Fin d) (Fin d) ℝ), uMat g - 1 ∈ A → uMat g⁻¹ - 1 ∈ A → (∀ k, uMat m * E k * uMat m⁻¹ = ∑ i, L i k • E i) → (fun i => (((uMat (m * g * m⁻¹) - 1) * (E i)ᴴ).trace).re) = L *ᵥ (fun i => (((uMat g - 1) * (E i)ᴴ).trace).re) := by
  first | exact @GlobalTheory.UnitaryCoords.coords_conj | exact GlobalTheory.UnitaryCoords.coords_conj | (intros; apply GlobalTheory.UnitaryCoords.coords_conj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryJMapConjEqSmulOfNormalizing
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryJMapConjEqSmulOfNormalizing
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.ConjScalesMeasure

theorem eq_smul_map_haar {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (M : Subgroup G) [LocallyCompactSpace M] (hM : IsClosed (M : Set G)) (μ : Measure G)
    (hμ : μ (M : Set G)ᶜ = 0)
    (hinv : ∀ s ∈ M, μ.map (fun g => s * g) = μ) [IsFiniteMeasureOnCompacts μ] :
    ∃ c : NNReal, μ = (c : ENNReal) • (Measure.haar : Measure M).map (Subtype.val : M → G) := by
  haveI : SecondCountableTopology M := TopologicalSpace.Subtype.secondCountableTopology (M : Set G)
  have hemb : MeasurableEmbedding (Subtype.val : M → G) := MeasurableEmbedding.subtype_coe hM.measurableSet
  set ν : Measure M := μ.comap Subtype.val with hν
  have hmap : ν.map Subtype.val = μ := by
    rw [hν, hemb.map_comap, Subtype.range_coe]
    exact Measure.restrict_eq_self_of_ae_mem hμ
  have hinj : ∀ ρ : Measure M, (ρ.map (Subtype.val : M → G)).comap Subtype.val = ρ := fun ρ => hemb.comap_map ρ
  haveI : ν.IsMulLeftInvariant := by
    refine ⟨fun s => ?_⟩
    rw [← hinj (ν.map _), Measure.map_map hemb.measurable (measurable_const_mul s)]
    have : (Subtype.val : M → G) ∘ (fun g => s * g) = (fun g => (s : G) * g) ∘ Subtype.val := rfl
    rw [this, ← Measure.map_map (measurable_const_mul _) hemb.measurable, hmap, hinv s s.2]
  haveI : IsFiniteMeasureOnCompacts ν := by
    refine ⟨fun K hK => ?_⟩
    rw [hν, hemb.comap_apply]
    exact (hK.image continuous_subtype_val).measure_lt_top
  have e1 := Measure.isMulLeftInvariant_eq_smul ν (Measure.haar : Measure M)
  refine ⟨Measure.haarScalarFactor ν (Measure.haar : Measure M), ?_⟩
  rw [← Measure.map_smul _ hemb.measurable.aemeasurable]
  conv_lhs => rw [← hmap, e1]
  rfl

theorem map_conj_eq_smul_of_group {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (S : Subgroup G) (μ : Measure G) (hS : IsClosed (S : Set G)) (hμ : μ (S : Set G)ᶜ = 0)
    (hinv : ∀ s ∈ S, μ.map (fun g => s * g) = μ) (hfin : IsFiniteMeasureOnCompacts μ) (h0 : μ ≠ 0)
    (m : G) (hm : ∀ g, g ∈ S ↔ m * g * m⁻¹ ∈ S) :
    ∃ c : NNReal, μ.map (fun u => m * u * m⁻¹) = (c : ENNReal) • μ := by
  haveI : LocallyCompactSpace S := hS.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have hcm : Measurable (fun u : G => m * u * m⁻¹) :=
    ((continuous_const.mul continuous_id).mul continuous_const).measurable
  haveI : IsFiniteMeasureOnCompacts (μ.map (fun u => m * u * m⁻¹)) :=
    Measure.IsFiniteMeasureOnCompacts.map μ ((Homeomorph.mulLeft m).trans (Homeomorph.mulRight m⁻¹))
  obtain ⟨a, ha⟩ := eq_smul_map_haar S hS μ hμ hinv
  obtain ⟨b, hb⟩ := eq_smul_map_haar S hS (μ.map (fun u => m * u * m⁻¹))
    (by
      rw [Measure.map_apply hcm hS.measurableSet.compl]
      convert hμ using 2
      ext g
      exact not_congr (hm g).symm)
    (by
      intro s hs
      have hs' : m⁻¹ * s * m ∈ S := (hm _).2 (by simpa [mul_assoc] using hs)
      rw [Measure.map_map (measurable_const_mul s) hcm]
      have : (fun g => s * g) ∘ (fun u : G => m * u * m⁻¹)
          = (fun u : G => m * u * m⁻¹) ∘ (fun g => (m⁻¹ * s * m) * g) := by
        funext g
        simp [mul_assoc]
      rw [this, ← Measure.map_map hcm (measurable_const_mul _), hinv _ hs'])
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact h0 (by simpa using ha)
  refine ⟨b / a, ?_⟩
  rw [hb]
  conv_rhs => rw [ha]
  rw [smul_smul, ← ENNReal.coe_mul, div_mul_cancel₀ _ ha0]

theorem map_conj_eq_smul : ∀ (n : ℕ) (ε : Fin n → Bool) (S : Subgroup (Formalism.REAL.UJ ε)) (μ : Measure (Formalism.REAL.UJ ε)), IsClosed (S : Set (Formalism.REAL.UJ ε)) → μ (S : Set (Formalism.REAL.UJ ε))ᶜ = 0 → (∀ s ∈ S, μ.map (fun g => s * g) = μ) → IsFiniteMeasureOnCompacts μ → μ ≠ 0 → ∀ m : Formalism.REAL.UJ ε, (∀ g, g ∈ S ↔ m * g * m⁻¹ ∈ S) → ∃ c : NNReal, μ.map (fun u => m * u * m⁻¹) = (c : ENNReal) • μ :=
  fun _ _ S μ hS hμ hinv hfin h0 m hm => map_conj_eq_smul_of_group S μ hS hμ hinv hfin h0 m hm

end GlobalTheory.ConjScalesMeasure
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryJMapConjEqSmulOfNormalizingStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryJ_map_conj_eq_smul_of_normalizing : ∀ (n : ℕ) (ε : Fin n → Bool) (S : Subgroup (Formalism.REAL.UJ ε)) (μ : Measure (Formalism.REAL.UJ ε)), IsClosed (S : Set (Formalism.REAL.UJ ε)) → μ (S : Set (Formalism.REAL.UJ ε))ᶜ = 0 → (∀ s ∈ S, μ.map (fun g => s * g) = μ) → IsFiniteMeasureOnCompacts μ → μ ≠ 0 → ∀ m : Formalism.REAL.UJ ε, (∀ g, g ∈ S ↔ m * g * m⁻¹ ∈ S) → ∃ c : NNReal, μ.map (fun u => m * u * m⁻¹) = (c : ENNReal) • μ := by
  first | exact @GlobalTheory.ConjScalesMeasure.map_conj_eq_smul | exact GlobalTheory.ConjScalesMeasure.map_conj_eq_smul | (intros; apply GlobalTheory.ConjScalesMeasure.map_conj_eq_smul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MapConjGaugeMeasureEqInvDetSmul
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.GaugeConjScale

open Topology Filter

theorem integral_comp_mulVec {d : ℕ} (L : Matrix (Fin d) (Fin d) ℝ) (hL : L.det ≠ 0)
    (φ : (Fin d → ℝ) → ℝ) (hφ : Continuous φ) :
    ∫ t, φ (L *ᵥ t) = |L.det|⁻¹ * ∫ t, φ t := by
  have hc : Continuous (Matrix.toLin' L) := LinearMap.continuous_of_finiteDimensional _
  have h := Real.map_matrix_volume_pi_eq_smul_volume_pi hL
  have h2 : ∫ t, φ t ∂(Measure.map (Matrix.toLin' L) volume) = ∫ t, φ (Matrix.toLin' L t) :=
    integral_map hc.measurable.aemeasurable hφ.aestronglyMeasurable
  rw [h, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _), abs_inv, smul_eq_mul] at h2
  simpa using h2.symm

theorem hasCompactSupport_comp_mulVec {d : ℕ} (L : Matrix (Fin d) (Fin d) ℝ) (hL : L.det ≠ 0)
    (φ : (Fin d → ℝ) → ℝ) (hφ : HasCompactSupport φ) : HasCompactSupport (fun t => φ (L *ᵥ t)) := by
  have hu : IsUnit L.det := isUnit_iff_ne_zero.2 hL
  let e : (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ) :=
    (Matrix.toLinearEquiv' L (Matrix.invertibleOfIsUnitDet L hu)).toContinuousLinearEquiv
  exact hφ.comp_homeomorph e.toHomeomorph

theorem scalar_eq_inv_det {X : Type} [MeasurableSpace X] (μ : Measure X) (T : X → X) (hT : Measurable T)
    (h : X → ℝ) (hh : Measurable h) {d : ℕ} (t : X → Fin d → ℝ) (ht : Measurable t)
    (L : Matrix (Fin d) (Fin d) ℝ) (hL : L.det ≠ 0) (c : NNReal) (hc : μ.map T = (c : ENNReal) • μ)
    (hTt : ∀ᵐ g ∂μ, t (T g) = L *ᵥ t g) (C : ℝ) (hC : 1 ≤ C) (h1 : ∀ g, h (T g) ≤ C * h g)
    (h2 : ∀ g, h g ≤ C * h (T g)) (ρ : ℝ) (hρ : 0 < ρ) (hfin : μ {g | h g < ρ} ≠ ⊤)
    (hlim : ∀ r₁ : ℝ, 0 < r₁ → r₁ ≤ ρ → ∀ φ : (Fin d → ℝ) → ℝ, Continuous φ → HasCompactSupport φ →
      Tendsto (fun r : ℝ => (r ^ d)⁻¹ * ∫ g in {g | h g < r₁}, φ (fun i => t g i / r) ∂μ)
        (𝓝[>] 0) (𝓝 (∫ x, φ x))) :
    (c : ℝ) = |L.det|⁻¹ := by
  have hC0 : 0 < C := lt_of_lt_of_le one_pos hC
  let b : ContDiffBump (0 : Fin d → ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  let φ : (Fin d → ℝ) → ℝ := b
  have hφc : Continuous φ := b.continuous
  have hφs : HasCompactSupport φ := b.hasCompactSupport
  have hφp : 0 < ∫ x, φ x := b.integral_pos
  have hφ0 : ∀ x, 0 ≤ φ x := fun x => b.nonneg
  have hφ1 : ∀ x, φ x ≤ 1 := fun x => b.le_one
  let ψ : (Fin d → ℝ) → ℝ := fun x => φ (L *ᵥ x)
  have hψc : Continuous ψ := hφc.comp (continuous_const.matrix_mulVec continuous_id)
  have hψs : HasCompactSupport ψ := hasCompactSupport_comp_mulVec L hL φ hφs
  have hψi : ∫ x, ψ x = |L.det|⁻¹ * ∫ x, φ x := integral_comp_mulVec L hL φ hφc
  have hr1 : 0 < ρ / C := div_pos hρ hC0
  have hr1' : ρ / C ≤ ρ := div_le_self hρ.le hC
  have hr2 : 0 < ρ / C / C := div_pos hr1 hC0
  have hr2' : ρ / C / C ≤ ρ := (div_le_self hr1.le hC).trans hr1'
  have hB1 : MeasurableSet {g | h g < ρ / C} := measurableSet_lt hh measurable_const
  have hs1 : {g | h g < ρ / C / C} ⊆ T ⁻¹' {g | h g < ρ / C} := by
    intro g hg
    have hg : h g < ρ / C / C := hg
    rw [lt_div_iff₀ hC0] at hg
    have := h1 g
    show h (T g) < ρ / C
    linarith
  have hs2 : T ⁻¹' {g | h g < ρ / C} ⊆ {g | h g < ρ} := by
    intro g hg
    have hg : h (T g) < ρ / C := hg
    rw [lt_div_iff₀ hC0] at hg
    have := h2 g
    show h g < ρ
    linarith
  have hm : ∀ r : ℝ, Measurable (fun g => (fun i => t g i / r : Fin d → ℝ)) := fun r =>
    Measurable.of_eval fun i => ((measurable_pi_apply i).comp ht).div_const r
  have hint : ∀ r : ℝ, IntegrableOn (fun g => ψ (fun i => t g i / r)) {g | h g < ρ} μ := by
    intro r
    refine Measure.integrableOn_of_bounded (M := 1) hfin (hψc.measurable.comp (hm r)).aestronglyMeasurable ?_
    refine Eventually.of_forall fun g => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (hφ0 _)]
    exact hφ1 _
  have key : ∀ r : ℝ, (c : ℝ) * ∫ g in {g | h g < ρ / C}, φ (fun i => t g i / r) ∂μ
      = ∫ g in T ⁻¹' {g | h g < ρ / C}, ψ (fun i => t g i / r) ∂μ := by
    intro r
    have e1 := setIntegral_map (μ := μ) (g := T) (f := fun g => φ (fun i => t g i / r)) hB1
      (hφc.measurable.comp (hm r)).aestronglyMeasurable hT.aemeasurable
    rw [hc, Measure.restrict_smul, integral_smul_measure, ENNReal.coe_toReal, smul_eq_mul] at e1
    rw [e1]
    refine integral_congr_ae (ae_restrict_of_ae (hTt.mono fun g hg => ?_))
    have e2 : ∀ y : Fin d → ℝ, (fun i => y i / r) = r⁻¹ • y := fun y => by
      ext i; simp [div_eq_inv_mul]
    show φ (fun i => t (T g) i / r) = φ (L *ᵥ fun i => t g i / r)
    rw [e2, e2, hg, Matrix.mulVec_smul]
  have l1 := (hlim _ hr1 hr1' φ hφc hφs).const_mul (c : ℝ)
  have l2 := hlim _ hr2 hr2' ψ hψc hψs
  have l3 := hlim _ hρ le_rfl ψ hψc hψs
  have a1 : ∫ x, ψ x ≤ c * ∫ x, φ x := by
    refine le_of_tendsto_of_tendsto l2 l1 ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr : 0 < r := hr
    rw [mul_left_comm, key]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact setIntegral_mono_set ((hint r).mono_set hs2) (Eventually.of_forall fun g => hφ0 _) (Filter.Eventually.of_forall hs1)
  have a2 : c * ∫ x, φ x ≤ ∫ x, ψ x := by
    refine le_of_tendsto_of_tendsto l1 l3 ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr : 0 < r := hr
    rw [mul_left_comm, key]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact setIntegral_mono_set (hint r) (Eventually.of_forall fun g => hφ0 _) (Filter.Eventually.of_forall hs2)
  exact mul_right_cancel₀ hφp.ne' ((le_antisymm a2 a1).trans hψi)

theorem hs_conj_le {n : ℕ} {ε : Fin n → Bool} (m g : Formalism.REAL.UJ ε) :
    Formalism.REAL.hs (uMat (m * g * m⁻¹) - 1) ≤
      Formalism.REAL.hs (uMat m) * Formalism.REAL.hs (uMat m⁻¹) * Formalism.REAL.hs (uMat g - 1) := by
  have a : uMat (m * g * m⁻¹) = uMat m * uMat g * uMat m⁻¹ := rfl
  have b : uMat m * uMat m⁻¹ = 1 := by
    have : uMat m * uMat m⁻¹ = uMat (m * m⁻¹) := rfl
    rw [this, mul_inv_cancel]; rfl
  have e : uMat (m * g * m⁻¹) - 1 = uMat m * (uMat g - 1) * uMat m⁻¹ := by
    rw [a, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, b]
  rw [e]
  refine (Formalism.REAL.frobenius_mul_le _ _).trans ?_
  rw [mul_right_comm]
  exact mul_le_mul_of_nonneg_right (Formalism.REAL.frobenius_mul_le _ _) (Formalism.REAL.frobenius_nonneg _)

theorem map_conj_eq_inv_det_smul (n : ℕ) (ε : Fin n → Bool) (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (d : ℕ)
    (E : Fin d → Matrix (Fin n) (Fin n) ℂ) (S : Subgroup (Formalism.REAL.UJ ε))
    (hA : ∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A)
    (hE : ∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0)
    (hsp : ∀ X, (X ∈ A ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E))
    (hS : ∀ g, g ∈ S ↔ uMat g - 1 ∈ A) (hcl : IsClosed (S : Set (Formalism.REAL.UJ ε)))
    (μ : Measure (Formalism.REAL.UJ ε)) (hμ : IsGaugeSub (S : Set (Formalism.REAL.UJ ε)) d μ)
    (m : Formalism.REAL.UJ ε) (L : Matrix (Fin d) (Fin d) ℝ) (hm : ∀ g, g ∈ S ↔ m * g * m⁻¹ ∈ S)
    (hmL : ∀ k, uMat m * E k * uMat m⁻¹ = ∑ i, L i k • E i) (hL : L.det ≠ 0) :
    μ.map (fun u => m * u * m⁻¹) = ENNReal.ofReal |L.det|⁻¹ • μ := by
  have hSe : (S : Set (Formalism.REAL.UJ ε)) = {g | uMat g - 1 ∈ A} := Set.ext hS
  obtain ⟨-, hK, -, r₀, hr₀, hlim⟩ := GlobalTheory.T.gaugeMeasure_matrixAlgebraSubgroup_local_asymptotics n ε A d E hA hE hsp μ (hSe ▸ hμ)
  obtain ⟨h1, h2, h3⟩ := hμ
  have hp : 0 < volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) := Metric.measure_ball_pos _ _ one_pos
  have hf : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) < ⊤ := measure_ball_lt_top
  obtain ⟨r, ⟨hr1, hr2⟩, hr⟩ :=
    (((h3.eventually (lt_mem_nhds hp)).and (h3.eventually (gt_mem_nhds hf))).and self_mem_nhdsWithin).exists
  have hr : 0 < r := hr
  have hcu : Continuous (fun g : Formalism.REAL.UJ ε => uMat g) :=
    Units.continuous_val.comp continuous_subtype_val
  have hc : Continuous (fun g : Formalism.REAL.UJ ε => Formalism.REAL.hs (uMat g - 1)) := by
    unfold Formalism.REAL.hs
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    exact (((hcu.sub continuous_const).matrix_elem i j).norm).pow 2
  have hne : μ ≠ 0 := by
    rintro rfl
    simp at hr1
  have hfin : μ {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r} ≠ ⊤ := by
    intro h
    rw [h, ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top] at hr2
    exact lt_irrefl _ hr2
  obtain ⟨c, hcμ⟩ := GlobalTheory.T.unitaryJ_map_conj_eq_smul_of_normalizing n ε S μ hcl h1 h2 hK hne m hm
  have hC0 : 0 ≤ Formalism.REAL.hs (uMat m) * Formalism.REAL.hs (uMat m⁻¹) :=
    mul_nonneg (Formalism.REAL.frobenius_nonneg _) (Formalism.REAL.frobenius_nonneg _)
  have hT : Continuous (fun u : Formalism.REAL.UJ ε => m * u * m⁻¹) := by fun_prop
  have ht : Continuous (fun (g : Formalism.REAL.UJ ε) (i : Fin d) => (((uMat g - 1) * (E i)ᴴ).trace).re) :=
    continuous_pi fun i => Complex.continuous_re.comp
      (((hcu.sub continuous_const).matrix_mul continuous_const).matrix_trace)
  have key := scalar_eq_inv_det μ (fun u => m * u * m⁻¹) hT.measurable _ hc.measurable _ ht.measurable L hL c hcμ
    ?_ (Formalism.REAL.hs (uMat m) * Formalism.REAL.hs (uMat m⁻¹) + 1) (by linarith) ?_ ?_ (min r₀ (r ^ 2))
    (lt_min hr₀ (by positivity)) ?_ (fun r₁ a b => hlim r₁ a (b.trans (min_le_left _ _)))
  · rw [hcμ, ← key, ENNReal.ofReal_coe_nnreal]
  · have : ∀ᵐ g ∂μ, g ∈ (S : Set (Formalism.REAL.UJ ε)) := h1
    filter_upwards [this] with g hg
    exact GlobalTheory.T.unitaryJ_lieCoords_conj_linear n ε A d E hE hsp g m L ((hS g).1 hg) ((hS _).1 (S.inv_mem hg)) hmL
  · intro g
    have := hs_conj_le m g
    have := Formalism.REAL.frobenius_nonneg (uMat g - 1)
    linarith
  · intro g
    have h4 := hs_conj_le m⁻¹ (m * g * m⁻¹)
    have e : m⁻¹ * (m * g * m⁻¹) * m⁻¹⁻¹ = g := by group
    rw [e, inv_inv] at h4
    have := Formalism.REAL.frobenius_nonneg (uMat (m * g * m⁻¹) - 1)
    linarith
  · refine ne_top_of_le_ne_top hfin (measure_mono fun g hg => ?_)
    have hg : Formalism.REAL.hs (uMat g - 1) < min r₀ (r ^ 2) := hg
    exact Real.sqrt_le_iff.2 ⟨hr.le, (hg.trans_le (min_le_right _ _)).le⟩

end GlobalTheory.GaugeConjScale
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MapConjGaugeMeasureEqInvDetSmulStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.map_conj_gaugeMeasure_eq_inv_det_smul : ∀ (n : ℕ) (ε : Fin n → Bool) (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ) (S : Subgroup (Formalism.REAL.UJ ε)), (∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) → (∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) → (∀ X, (X ∈ A ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E)) → (∀ g, g ∈ S ↔ uMat g - 1 ∈ A) → IsClosed (S : Set (Formalism.REAL.UJ ε)) → ∀ μ : Measure (Formalism.REAL.UJ ε), IsGaugeSub (S : Set (Formalism.REAL.UJ ε)) d μ → ∀ (m : Formalism.REAL.UJ ε) (L : Matrix (Fin d) (Fin d) ℝ), (∀ g, g ∈ S ↔ m * g * m⁻¹ ∈ S) → (∀ k, uMat m * E k * uMat m⁻¹ = ∑ i, L i k • E i) → L.det ≠ 0 → μ.map (fun u => m * u * m⁻¹) = ENNReal.ofReal |L.det|⁻¹ • μ := by
  first | exact @GlobalTheory.GaugeConjScale.map_conj_eq_inv_det_smul | exact GlobalTheory.GaugeConjScale.map_conj_eq_inv_det_smul | (intros; apply GlobalTheory.GaugeConjScale.map_conj_eq_inv_det_smul <;> assumption)
end
