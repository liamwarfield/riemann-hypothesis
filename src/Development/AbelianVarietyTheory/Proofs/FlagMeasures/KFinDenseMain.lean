module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierXPinsP
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFrameTranslatedPerpOfIsFrame

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsCompactKH
open MeasureTheory Matrix Filter Topology

noncomputable section

namespace GlobalTheory.KFinAvg

instance borelMat (n : ℕ) : BorelSpace (Matrix (Fin n) (Fin n) ℂ) :=
  inferInstanceAs (BorelSpace (Fin n → Fin n → ℂ))

def IsHaarKH (k r : ℕ) (μ : Measure (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) : Prop :=
  IsProbabilityMeasure μ ∧ μ (GlobalTheory.ThA.KH k r)ᶜ = 0 ∧
    (∀ a ∈ GlobalTheory.ThA.KH k r, μ.map (fun g => a * g) = μ) ∧
    ∀ U : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ), IsOpen U → 1 ∈ U → 0 < μ U

def peak (n : ℕ) (g : Matrix (Fin n) (Fin n) ℂ) : ℝ := (1 + (Matrix.trace g).re / n) / 2

def peakN {n : ℕ} (μ : Measure (Matrix (Fin n) (Fin n) ℂ)) (m : ℕ) (g : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  ((peak n g ^ m / ∫ h, peak n h ^ m ∂μ : ℝ) : ℂ)

end GlobalTheory.KFinAvg

namespace GlobalTheory.KFinAvg
open Matrix

theorem isCompact_KH (k r : ℕ) : IsCompact (GlobalTheory.ThA.KH k r) := by
  have hc : IsClosed (PI.UpqRep.UH (PI.UpqRep.Hpk k r)) := by
    show IsClosed {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ | gᴴ * PI.UpqRep.Hpk k r * g = PI.UpqRep.Hpk k r}
    exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
      continuous_const
  exact (GlobalTheory.isCompact_unitaryGroup (Fin (2 * r + k + 1)) ℂ).inter_left hc

end GlobalTheory.KFinAvg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.KFinDense
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DsigWSubAvg
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralTranslateFamilyIsKFiniteHermitian
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralTranslateFamilyIsKFiniteHermitian
open MeasureTheory Matrix Filter Topology

noncomputable section

namespace GlobalTheory.KFinAvg

theorem integrable_smul_orbit {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
    {μ : Measure (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)}
    (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.QuantumDeterminants.UH (PI.UpqRep.Hpk k r)) σ) (hμ : IsHaarKH k r μ)
    {f : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℂ} (hf : Continuous f) (v : H) :
    Integrable (fun g => f g • σ g v) μ := by
  haveI := hμ.1
  have hK := isCompact_KH k r
  have hsub : GlobalTheory.ThA.KH k r ⊆ Formalism.QuantumDeterminants.UH (PI.UpqRep.Hpk k r) := fun g hg => hg.1
  have hc : ContinuousOn (fun g => f g • σ g v) (GlobalTheory.ThA.KH k r) :=
    hf.continuousOn.smul ((hσ.2.2 v).mono hsub)
  have hI : IntegrableOn (fun g => f g • σ g v) (GlobalTheory.ThA.KH k r) μ := hc.integrableOn_compact hK
  have hr : μ.restrict (GlobalTheory.ThA.KH k r) = μ :=
    Measure.restrict_eq_self_of_ae_mem (by rw [ae_iff]; exact hμ.2.1)
  rw [IntegrableOn, hr] at hI
  exact hI

theorem integral_sum_smul_orbit {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
    {μ : Measure (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)}
    (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.QuantumDeterminants.UH (PI.UpqRep.Hpk k r)) σ) (hμ : IsHaarKH k r μ)
    {N : ℕ} {b : Fin N → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℂ} (hb : ∀ j, Continuous (b j))
    (c : Fin N → ℂ) (v : H) :
    ∫ g, (∑ j, c j * b j g) • σ g v ∂μ = ∑ j, c j • ∫ g, b j g • σ g v ∂μ := by
  simp_rw [Finset.sum_smul, mul_smul]
  rw [integral_finsetSum Finset.univ (f := fun j g => c j • (b j g • σ g v)) (fun j _ => (Integrable.smul (c j) (integrable_smul_orbit hσ hμ (hb j) v) :
      Integrable (fun g => c j • (b j g • σ g v)) μ))]
  simp_rw [integral_smul]

end GlobalTheory.KFinAvg

namespace GlobalTheory.KFinAvg

theorem isKFinHpk_integral_translates : ∀ (k r : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (μ : Measure (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)), Formalism.MainNotions.S.IsURepOn (Formalism.QuantumDeterminants.UH (PI.UpqRep.Hpk k r)) σ → GlobalTheory.KFinAvg.IsHaarKH k r μ → ∀ (N : ℕ) (b : Fin N → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℂ), (∀ j, Continuous (b j)) → (∀ (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (j : Fin N), ∃ d : Fin N → ℂ, ∀ g, b j (a * g) = ∑ i, d i * b i g) → ∀ (c : Fin N → ℂ) (v : H), PI.UpqRep.IsKFinHpk (k := k) (r := r) σ (∫ g, (∑ j, c j * b j g) • σ g v ∂μ) := by
  intro k r H _ _ _ σ μ hσ hμ N b hb hinv c v
  obtain ⟨w, hw⟩ : ∃ w : Fin N → H, ∀ j, w j = ∫ g, b j g • σ g v ∂μ := ⟨_, fun _ => rfl⟩
  have key : ∀ c' : Fin N → ℂ, ∫ g, (∑ j, c' j * b j g) • σ g v ∂μ = ∑ j, c' j • w j := by
    intro c'
    rw [integral_sum_smul_orbit hσ hμ hb c' v]
    simp_rw [hw]
  have hmem : ∀ c' : Fin N → ℂ, ∑ j, c' j • w j ∈ Submodule.span ℂ (Set.range w) := fun c' =>
    Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
  refine ⟨Submodule.span ℂ (Set.range w), FiniteDimensional.span_of_finite ℂ (Set.finite_range w), ?_, ?_⟩
  · rw [key]; exact hmem c
  · intro a ha x hx
    have hu : star a * a = 1 := ha.2.1
    have haa : a⁻¹ * a = 1 := by rw [Matrix.inv_eq_left_inv hu]; exact hu
    have hae : ∀ᵐ g ∂μ, g ∈ GlobalTheory.ThA.KH k r := by rw [ae_iff]; exact hμ.2.1
    have hgen : ∀ j, σ a (w j) ∈ Submodule.span ℂ (Set.range w) := by
      intro j
      obtain ⟨d, hd⟩ := hinv a⁻¹ j
      have h1 : σ a (w j) = ∫ g, b j g • σ (a * g) v ∂μ := by
        rw [hw, ← (σ a).integral_comp_comm (integrable_smul_orbit hσ hμ (hb j) v)]
        refine integral_congr_ae ?_
        filter_upwards [hae] with g hg
        rw [map_smul, hσ.1.2 a ha.1 g hg.1]
        rfl
      have hcm : Continuous (fun g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ => a * g) :=
        continuous_const.matrix_mul continuous_id
      have h2 : ∫ g, b j g • σ (a * g) v ∂μ = ∫ g, b j (a⁻¹ * g) • σ g v ∂μ := by
        conv_rhs => rw [← hμ.2.2.1 a ha]
        rw [integral_map hcm.aemeasurable]
        · simp only [← Matrix.mul_assoc, haa, Matrix.one_mul]
        · rw [hμ.2.2.1 a ha]
          exact (integrable_smul_orbit hσ hμ ((hb j).comp (continuous_const.matrix_mul continuous_id)) v).aestronglyMeasurable
      rw [h1, h2]
      simp_rw [hd]
      rw [key]
      exact hmem d
    have hle : Submodule.span ℂ (Set.range w) ≤ (Submodule.span ℂ (Set.range w)).comap (σ a).toLinearMap := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact hgen j
    exact hle hx

end GlobalTheory.KFinAvg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralTranslateFamilyIsKFiniteHermitianStatement
open MeasureTheory Matrix Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_translate_family_isKFinite_hermitian : ∀ (k r : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (μ : Measure (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)), Formalism.MainNotions.S.IsURepOn (Formalism.QuantumDeterminants.UH (PI.UpqRep.Hpk k r)) σ → GlobalTheory.KFinAvg.IsHaarKH k r μ → ∀ (N : ℕ) (b : Fin N → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℂ), (∀ j, Continuous (b j)) → (∀ (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (j : Fin N), ∃ d : Fin N → ℂ, ∀ g, b j (a * g) = ∑ i, d i * b i g) → ∀ (c : Fin N → ℂ) (v : H), PI.UpqRep.IsKFinHpk (k := k) (r := r) σ (∫ g, (∑ j, c j * b j g) • σ g v ∂μ) := by
  first | exact @GlobalTheory.KFinAvg.isKFinHpk_integral_translates | exact GlobalTheory.KFinAvg.isKFinHpk_integral_translates | (intros; apply GlobalTheory.KFinAvg.isKFinHpk_integral_translates <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TendstoIntegralNormalisedPowPeak
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TendstoIntegralNormalisedPowPeak
open MeasureTheory Matrix Filter Topology

namespace GlobalTheory

theorem tendsto_integral_normalised_pow_peak :
    ∀ (X : Type) [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X), IsProbabilityMeasure μ → ∀ (K : Set X) (x₀ : X) (f : X → ℝ), IsCompact K → μ Kᶜ = 0 → x₀ ∈ K → (∀ U : Set X, IsOpen U → x₀ ∈ U → 0 < μ U) → Continuous f → f x₀ = 1 → (∀ x ∈ K, 0 ≤ f x ∧ f x ≤ 1) → (∀ U ∈ 𝓝 x₀, ∃ δ < 1, ∀ x ∈ K, x ∉ U → f x ≤ δ) → ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (F : X → E), ContinuousOn F K → Tendsto (fun m : ℕ => ∫ x, ((f x ^ m / ∫ y, f y ^ m ∂μ : ℝ) : ℂ) • F x ∂μ) atTop (𝓝 (F x₀)) := by
  intro X _ _ _ _ μ hμ K x₀ f hK hKc hx₀ hpos hf hf1 hf01 hsep E _ _ _ F hF
  have hKae : ∀ᵐ x ∂μ, x ∈ K := ae_iff.mpr hKc
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hμK : μ.restrict K = μ := Measure.restrict_eq_self_of_ae_mem hKae
  have hFm : AEStronglyMeasurable F μ := by
    have h := hF.aestronglyMeasurable_of_isCompact (μ := μ) hK hKm
    rwa [hμK] at h
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC x₀ hx₀)

  have hfm_int : ∀ m : ℕ, Integrable (fun x => f x ^ m) μ := by
    intro m
    refine Integrable.of_bound (hf.pow m).aestronglyMeasurable 1 ?_
    filter_upwards [hKae] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hf01 x hx).1 m)]
    exact pow_le_one₀ (hf01 x hx).1 (hf01 x hx).2

  have hlow : ∀ η : ℝ, 0 ≤ η → ∀ m : ℕ,
      η ^ m * μ.real {x | η < f x} ≤ ∫ y, f y ^ m ∂μ := by
    intro η hη m
    have hWm : MeasurableSet {x | η < f x} := measurableSet_lt measurable_const hf.measurable
    have h := integral_indicator_const (μ := μ) (η ^ m) hWm
    rw [smul_eq_mul] at h
    rw [mul_comm, ← h]
    refine integral_mono_ae ((integrable_const (η ^ m)).indicator hWm) (hfm_int m) ?_
    filter_upwards [hKae] with x hx
    by_cases hxW : x ∈ {x | η < f x}
    · rw [Set.indicator_apply, if_pos hxW]
      exact pow_le_pow_left₀ hη (le_of_lt hxW) m
    · rw [Set.indicator_apply, if_neg hxW]
      exact pow_nonneg (hf01 x hx).1 m
  rw [Metric.tendsto_atTop]
  intro ε hε

  obtain ⟨u, hu_open, hx₀u, hu⟩ :=
    mem_nhdsWithin.mp ((hF x₀ hx₀) (Metric.ball_mem_nhds (F x₀) (half_pos hε)))
  obtain ⟨δ, hδ1, hδ⟩ := hsep u (hu_open.mem_nhds hx₀u)
  obtain ⟨d, hd0, hd1, hδd⟩ : ∃ d : ℝ, 0 ≤ d ∧ d < 1 ∧ δ ≤ d :=
    ⟨max δ 0, le_max_right _ _, max_lt hδ1 one_pos, le_max_left _ _⟩
  obtain ⟨η, hη0, hdη, hη1⟩ : ∃ η : ℝ, 0 < η ∧ d < η ∧ η < 1 :=
    ⟨(d + 1) / 2, by linarith, by linarith, by linarith⟩
  have hWpos : 0 < μ {x | η < f x} :=
    hpos _ (isOpen_lt continuous_const hf) (by show η < f x₀; rw [hf1]; exact hη1)
  have hW : 0 < μ.real {x | η < f x} := ENNReal.toReal_pos hWpos.ne' (measure_ne_top μ _)
  have hr : Tendsto (fun m : ℕ => (2 * C + 1) * (d / η) ^ m / μ.real {x | η < f x})
      atTop (𝓝 0) := by
    have h := ((tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hd0 hη0.le)
      ((div_lt_one hη0).mpr hdη)).const_mul (2 * C + 1)).div_const (μ.real {x | η < f x})
    simpa using h
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hr (Iio_mem_nhds (half_pos hε)))
  refine ⟨N, fun m hm => ?_⟩
  have hIpos : 0 < ∫ y, f y ^ m ∂μ :=
    lt_of_lt_of_le (mul_pos (pow_pos hη0 m) hW) (hlow η hη0.le m)
  set c : X → ℂ := fun x => ((f x ^ m / ∫ y, f y ^ m ∂μ : ℝ) : ℂ) with hc
  have hc_cont : Continuous c :=
    Complex.continuous_ofReal.comp ((hf.pow m).div_const _)
  have hcnorm : ∀ x ∈ K, ‖c x‖ = f x ^ m / ∫ y, f y ^ m ∂μ := by
    intro x hx
    rw [hc, Complex.norm_real, Real.norm_of_nonneg
      (div_nonneg (pow_nonneg (hf01 x hx).1 m) hIpos.le)]
  have hcle : ∀ x ∈ K, ‖c x‖ ≤ 1 / ∫ y, f y ^ m ∂μ := by
    intro x hx
    rw [hcnorm x hx]
    exact div_le_div_of_nonneg_right (pow_le_one₀ (hf01 x hx).1 (hf01 x hx).2) hIpos.le
  have hc_int : Integrable c μ := by
    refine Integrable.of_bound hc_cont.aestronglyMeasurable (1 / ∫ y, f y ^ m ∂μ) ?_
    filter_upwards [hKae] with x hx
    exact hcle x hx
  have hcF_int : Integrable (fun x => c x • F x) μ := by
    refine Integrable.of_bound (hc_cont.aestronglyMeasurable.smul hFm)
      (1 / (∫ y, f y ^ m ∂μ) * C) ?_
    filter_upwards [hKae] with x hx
    rw [norm_smul]
    exact mul_le_mul (hcle x hx) (hC x hx) (norm_nonneg _) (by positivity)

  have hint1 : ∫ x, c x ∂μ = 1 := by
    show ∫ x, ((f x ^ m / ∫ y, f y ^ m ∂μ : ℝ) : ℂ) ∂μ = 1
    rw [integral_complex_ofReal, integral_div, div_self hIpos.ne', Complex.ofReal_one]
  have hkey : (∫ x, ((f x ^ m / ∫ y, f y ^ m ∂μ : ℝ) : ℂ) • F x ∂μ) - F x₀
      = ∫ x, c x • (F x - F x₀) ∂μ := by
    simp_rw [smul_sub]
    rw [integral_sub hcF_int (hc_int.smul_const (F x₀)), integral_smul_const, hint1, one_smul]
  set B : ℝ := (2 * C + 1) * d ^ m / ∫ y, f y ^ m ∂μ with hB
  have hB0 : 0 ≤ B := div_nonneg (mul_nonneg (by linarith) (pow_nonneg hd0 m)) hIpos.le
  have hbound : ∀ᵐ x ∂μ, ‖c x • (F x - F x₀)‖
      ≤ (f x ^ m / ∫ y, f y ^ m ∂μ) * (ε / 2) + B := by
    filter_upwards [hKae] with x hx
    have h0 : 0 ≤ f x ^ m / ∫ y, f y ^ m ∂μ :=
      div_nonneg (pow_nonneg (hf01 x hx).1 m) hIpos.le
    rw [norm_smul, hcnorm x hx]
    by_cases hxu : x ∈ u
    · have hlt : ‖F x - F x₀‖ < ε / 2 := by
        have h := hu ⟨hxu, hx⟩
        simpa [dist_eq_norm] using h
      have := mul_le_mul_of_nonneg_left hlt.le h0
      linarith
    · have hfx : f x ≤ d := le_trans (hδ x hx hxu) hδd
      have hpow : f x ^ m ≤ d ^ m := pow_le_pow_left₀ (hf01 x hx).1 hfx m
      have hFd : ‖F x - F x₀‖ ≤ 2 * C + 1 := by
        have := norm_sub_le (F x) (F x₀)
        linarith [hC x hx, hC x₀ hx₀]
      have h1 : f x ^ m / (∫ y, f y ^ m ∂μ) * ‖F x - F x₀‖ ≤ B := by
        calc f x ^ m / (∫ y, f y ^ m ∂μ) * ‖F x - F x₀‖
            = (‖F x - F x₀‖ * f x ^ m) / ∫ y, f y ^ m ∂μ := by ring
          _ ≤ ((2 * C + 1) * d ^ m) / ∫ y, f y ^ m ∂μ :=
            div_le_div_of_nonneg_right
              (mul_le_mul hFd hpow (pow_nonneg (hf01 x hx).1 m) (by linarith)) hIpos.le
      have h2 : 0 ≤ f x ^ m / (∫ y, f y ^ m ∂μ) * (ε / 2) := mul_nonneg h0 (by linarith)
      linarith
  have hBle : B ≤ (2 * C + 1) * (d / η) ^ m / μ.real {x | η < f x} := by
    rw [hB, div_pow, mul_div_assoc', div_div]
    exact div_le_div_of_nonneg_left (mul_nonneg (by linarith) (pow_nonneg hd0 m))
      (mul_pos (pow_pos hη0 m) hW) (hlow η hη0.le m)
  have hBlt : B < ε / 2 := lt_of_le_of_lt hBle (hN m hm)
  have hg_int : Integrable (fun x => (f x ^ m / ∫ y, f y ^ m ∂μ) * (ε / 2) + B) μ :=
    (((hfm_int m).div_const _).mul_const _).add (integrable_const _)
  rw [dist_eq_norm, hkey]
  calc ‖∫ x, c x • (F x - F x₀) ∂μ‖
      ≤ ∫ x, ((f x ^ m / ∫ y, f y ^ m ∂μ) * (ε / 2) + B) ∂μ :=
        norm_integral_le_of_norm_le hg_int hbound
    _ = ε / 2 + B := by
        rw [integral_add (((hfm_int m).div_const _).mul_const _) (integrable_const _),
          integral_mul_const, integral_div, div_self hIpos.ne', integral_const]
        simp
    _ < ε := by linarith

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TendstoIntegralNormalisedPowPeakStatement
open MeasureTheory Matrix Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_integral_normalised_pow_smul_of_unique_peak : ∀ (X : Type) [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X), IsProbabilityMeasure μ → ∀ (K : Set X) (x₀ : X) (f : X → ℝ), IsCompact K → μ Kᶜ = 0 → x₀ ∈ K → (∀ U : Set X, IsOpen U → x₀ ∈ U → 0 < μ U) → Continuous f → f x₀ = 1 → (∀ x ∈ K, 0 ≤ f x ∧ f x ≤ 1) → (∀ U ∈ 𝓝 x₀, ∃ δ < 1, ∀ x ∈ K, x ∉ U → f x ≤ δ) → ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (F : X → E), ContinuousOn F K → Tendsto (fun m : ℕ => ∫ x, ((f x ^ m / ∫ y, f y ^ m ∂μ : ℝ) : ℂ) • F x ∂μ) atTop (𝓝 (F x₀)) := by
  first | exact @GlobalTheory.tendsto_integral_normalised_pow_peak | exact GlobalTheory.tendsto_integral_normalised_pow_peak | (intros; apply GlobalTheory.tendsto_integral_normalised_pow_peak <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsHaarProbabilityMaxCompactHermitian
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsHaarProbabilityMaxCompactHermitian
open MeasureTheory Matrix Filter Topology

noncomputable section

namespace GlobalTheory.KFinAvg

theorem uh_mul {N : ℕ} {H A B : Matrix (Fin N) (Fin N) ℂ} (hA : Aᴴ * H * A = H) (hB : Bᴴ * H * B = H) :
    (A * B)ᴴ * H * (A * B) = H := by
  rw [Matrix.conjTranspose_mul]
  calc Bᴴ * Aᴴ * H * (A * B) = Bᴴ * (Aᴴ * H * A) * B := by simp only [Matrix.mul_assoc]
    _ = H := by rw [hA, hB]

theorem uh_star {N : ℕ} {H A : Matrix (Fin N) (Fin N) ℂ} (hA : Aᴴ * H * A = H) (hu : A * Aᴴ = 1) :
    (Aᴴ)ᴴ * H * Aᴴ = H := by
  rw [Matrix.conjTranspose_conjTranspose]
  calc A * H * Aᴴ = A * (Aᴴ * H * A) * Aᴴ := by rw [hA]
    _ = (A * Aᴴ) * H * (A * Aᴴ) := by simp only [Matrix.mul_assoc]
    _ = H := by rw [hu, Matrix.one_mul, Matrix.mul_one]

def subKH (k r : ℕ) : Subgroup (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ) where
  carrier := {u | (u : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ GlobalTheory.ThA.KH k r}
  mul_mem' := by
    intro a b ha hb
    exact ⟨uh_mul ha.1 hb.1, (a * b).2⟩
  one_mem' := by
    refine ⟨?_, (1 : Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ).2⟩
    show (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ᴴ * Formalism.QuantumDeterminants.Hpk k r * 1 = Formalism.QuantumDeterminants.Hpk k r
    simp
  inv_mem' := by
    intro a ha
    refine ⟨?_, a⁻¹.2⟩
    have hu : (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) *
        (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ᴴ = 1 := by
      have := Matrix.mem_unitaryGroup_iff.mp a.2
      rwa [Matrix.star_eq_conjTranspose] at this
    exact uh_star ha.1 hu

instance (k r : ℕ) : MeasurableSpace (subKH k r) := borel _
instance (k r : ℕ) : BorelSpace (subKH k r) := ⟨rfl⟩

instance (k r : ℕ) : CompactSpace (subKH k r) := by
  have hc : IsClosed ((subKH k r : Set (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ))) := by
    have : ((subKH k r : Set (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ))) =
        (Subtype.val : Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ → _) ⁻¹' GlobalTheory.ThA.KH k r := rfl
    rw [this]
    exact (isCompact_KH k r).isClosed.preimage continuous_subtype_val
  exact isCompact_iff_compactSpace.mp hc.isCompact

def incKH (k r : ℕ) (u : subKH k r) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  ((u : Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ) : Matrix _ _ ℂ)

theorem continuous_incKH (k r : ℕ) : Continuous (incKH k r) :=
  continuous_subtype_val.comp continuous_subtype_val

theorem incKH_mem (k r : ℕ) (u : subKH k r) : incKH k r u ∈ GlobalTheory.ThA.KH k r := u.2

theorem exists_isHaarKH : ∀ k r : ℕ, ∃ μ : Measure (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ),
    GlobalTheory.KFinAvg.IsHaarKH k r μ := by
  intro k r
  let ν : Measure (subKH k r) := Measure.haarMeasure ⊤
  have hmeas : Measurable (incKH k r) := (continuous_incKH k r).measurable
  have hν : IsProbabilityMeasure ν := ⟨by
    have := Measure.haarMeasure_self (G := subKH k r) (K₀ := ⊤)
    simpa using this⟩
  have hKm : MeasurableSet (GlobalTheory.ThA.KH k r) := (isCompact_KH k r).isClosed.measurableSet
  refine ⟨ν.map (incKH k r), ?_, ?_, ?_, ?_⟩
  · infer_instance
  · rw [Measure.map_apply hmeas hKm.compl]
    have : incKH k r ⁻¹' (GlobalTheory.ThA.KH k r)ᶜ = ∅ := by
      ext u
      simp [incKH_mem k r u]
    rw [this, measure_empty]
  · intro a ha
    let au : Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ := ⟨a, ha.2⟩
    let a' : subKH k r := ⟨au, ha⟩
    have h := map_mul_left_eq_self ν a'
    rw [Measure.map_map (measurable_const_mul a) hmeas]
    conv_rhs => rw [← h]
    rw [Measure.map_map hmeas (measurable_const_mul _)]
    rfl
  · intro U hU h1
    rw [Measure.map_apply hmeas hU.measurableSet]
    exact (hU.preimage (continuous_incKH k r)).measure_pos ν ⟨1, h1⟩

end GlobalTheory.KFinAvg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsHaarProbabilityMaxCompactHermitianStatement
open MeasureTheory Matrix Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isHaarProbabilityMaxCompactHermitian : ∀ k r : ℕ, ∃ μ : Measure (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ), GlobalTheory.KFinAvg.IsHaarKH k r μ := by
  first | exact @GlobalTheory.KFinAvg.exists_isHaarKH | exact GlobalTheory.KFinAvg.exists_isHaarKH | (intros; apply GlobalTheory.KFinAvg.exists_isHaarKH <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryRealTraceBumpPeakProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryRealTraceBumpPeakProperties
open MeasureTheory Matrix Filter Topology

noncomputable section

namespace GlobalTheory.KFinAvg

theorem sum_normSq_col {n : ℕ} {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ))) (i : Fin n) :
    ∑ j, ‖g j i‖ ^ 2 = 1 := by
  have h1 : star g * g = 1 := (Matrix.mem_unitaryGroup_iff').1 hg
  have h2 : (star g * g) i i = 1 := by rw [h1]; simp
  rw [Matrix.mul_apply] at h2
  have h3 : ((∑ j, ‖g j i‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← h2]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.star_apply, Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    rfl
  exact_mod_cast h3

theorem norm_entry_le_one {n : ℕ} {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ))) (j i : Fin n) :
    ‖g j i‖ ≤ 1 := by
  have h := sum_normSq_col hg i
  have h2 : ‖g j i‖ ^ 2 ≤ ∑ j, ‖g j i‖ ^ 2 :=
    Finset.single_le_sum (f := fun j => ‖g j i‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j)
  rw [h] at h2
  nlinarith [norm_nonneg (g j i)]

theorem re_trace_eq {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) :
    (Matrix.trace g).re = ∑ i, (g i i).re := by
  simp [Matrix.trace, Complex.re_sum]

theorem eq_one_of_re_trace {n : ℕ} {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)))
    (ht : (Matrix.trace g).re = n) : g = 1 := by
  have hle : ∀ i, (g i i).re ≤ 1 := fun i =>
    (Complex.re_le_norm _).trans (norm_entry_le_one hg i i)
  have hsum : ∑ i : Fin n, (1 - (g i i).re) = 0 := by
    rw [Finset.sum_sub_distrib, ← re_trace_eq, ht]
    simp
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sub_nonneg.2 (hle i))).1 hsum
  have hre : ∀ i, (g i i).re = 1 := fun i => by
    have := hz i (Finset.mem_univ i)
    linarith
  have hnorm : ∀ i, ‖g i i‖ = 1 := fun i => le_antisymm (norm_entry_le_one hg i i)
    (by simpa [hre i] using Complex.re_le_norm (g i i))
  have hdiag : ∀ i, g i i = 1 := fun i => by
    have h1 : ‖g i i‖ ^ 2 = (g i i).re ^ 2 + (g i i).im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
    rw [hnorm i, hre i] at h1
    have him : (g i i).im = 0 := by nlinarith
    exact Complex.ext (by simpa using hre i) (by simpa using him)
  ext j i
  by_cases hji : j = i
  · subst hji
    simp [hdiag j]
  · have hs := sum_normSq_col hg i
    have h0 : ∑ k ∈ Finset.univ.erase i, ‖g k i‖ ^ 2 = 0 := by
      have := Finset.add_sum_erase Finset.univ (fun k => ‖g k i‖ ^ 2) (Finset.mem_univ i)
      rw [hs, hnorm i] at this
      linarith
    have hz2 := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => by positivity)).1 h0
    have := hz2 j (Finset.mem_erase.2 ⟨hji, Finset.mem_univ j⟩)
    have hn : ‖g j i‖ = 0 := by simpa using this
    rw [Matrix.one_apply_ne hji]
    exact norm_eq_zero.1 hn

theorem peak_continuous (n : ℕ) : Continuous (peak n) := by
  unfold peak
  have : Continuous fun g : Matrix (Fin n) (Fin n) ℂ => (Matrix.trace g).re :=
    Complex.continuous_re.comp continuous_id.matrix_trace
  fun_prop

theorem peak_one {n : ℕ} (hn : 0 < n) : peak n 1 = 1 := by
  have : (n : ℝ) ≠ 0 := by positivity
  simp [peak, Matrix.trace_one, this]

theorem abs_re_trace_le {n : ℕ} {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ))) :
    |(Matrix.trace g).re| ≤ n := by
  rw [re_trace_eq]
  calc |∑ i, (g i i).re| ≤ ∑ i, |(g i i).re| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum fun i _ =>
        (Complex.abs_re_le_norm _).trans (norm_entry_le_one hg i i)
    _ = n := by simp

theorem peak_mem_Icc {n : ℕ} (hn : 0 < n) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ))) :
    0 ≤ peak n g ∧ peak n g ≤ 1 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h := abs_le.1 (abs_re_trace_le hg)
  have h1 : -1 ≤ (Matrix.trace g).re / n := by
    rw [le_div_iff₀ hn']; linarith [h.1]
  have h2 : (Matrix.trace g).re / n ≤ 1 := by
    rw [div_le_iff₀ hn']; linarith [h.2]
  unfold peak
  constructor <;> linarith

theorem peak_lt_one {n : ℕ} (hn : 0 < n) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ))) (h1 : g ≠ 1) :
    peak n g < 1 := by
  refine lt_of_le_of_ne (peak_mem_Icc hn hg).2 fun he => h1 (eq_one_of_re_trace hg ?_)
  have hn' : (n : ℝ) ≠ 0 := by positivity
  unfold peak at he
  have : (Matrix.trace g).re / n = 1 := by linarith
  field_simp at this
  linarith

theorem peak_properties : ∀ n : ℕ, 0 < n → Continuous (GlobalTheory.KFinAvg.peak n) ∧ GlobalTheory.KFinAvg.peak n 1 = 1 ∧
    (∀ g ∈ (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)),
      0 ≤ GlobalTheory.KFinAvg.peak n g ∧ GlobalTheory.KFinAvg.peak n g ≤ 1) ∧
    ∀ U ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), ∃ δ < 1,
      ∀ g ∈ (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)),
        g ∉ U → GlobalTheory.KFinAvg.peak n g ≤ δ := by
  intro n hn
  refine ⟨peak_continuous n, peak_one hn, fun g hg => peak_mem_Icc hn hg, fun U hU => ?_⟩
  have hK : IsCompact ((Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) ∩ (interior U)ᶜ) :=
    (GlobalTheory.isCompact_unitaryGroup (Fin n) ℂ).inter_right isOpen_interior.isClosed_compl
  have h1 : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ interior U := mem_interior_iff_mem_nhds.2 hU
  rcases Set.eq_empty_or_nonempty
      ((Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) ∩ (interior U)ᶜ) with he | hne
  · refine ⟨0, by norm_num, fun g hg hgU => ?_⟩
    have : g ∈ (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) ∩ (interior U)ᶜ :=
      ⟨hg, fun hi => hgU (interior_subset hi)⟩
    rw [he] at this
    exact this.elim
  · obtain ⟨g₀, hg₀, hmax⟩ := hK.exists_isMaxOn hne (peak_continuous n).continuousOn
    have hne1 : g₀ ≠ 1 := fun h => hg₀.2 (h ▸ h1)
    refine ⟨peak n g₀, peak_lt_one hn hg₀.1 hne1, fun g hg hgU => ?_⟩
    exact hmax ⟨hg, fun hi => hgU (interior_subset hi)⟩

end GlobalTheory.KFinAvg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryRealTraceBumpPeakPropertiesStatement
open MeasureTheory Matrix Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryRealTraceBump_peak_properties : ∀ n : ℕ, 0 < n → Continuous (GlobalTheory.KFinAvg.peak n) ∧ GlobalTheory.KFinAvg.peak n 1 = 1 ∧ (∀ g ∈ (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)), 0 ≤ GlobalTheory.KFinAvg.peak n g ∧ GlobalTheory.KFinAvg.peak n g ≤ 1) ∧ ∀ U ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), ∃ δ < 1, ∀ g ∈ (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)), g ∉ U → GlobalTheory.KFinAvg.peak n g ≤ δ := by
  first | exact @GlobalTheory.KFinAvg.peak_properties | exact GlobalTheory.KFinAvg.peak_properties | (intros; apply GlobalTheory.KFinAvg.peak_properties <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasDerivAtDerivedActionMaxCompactAverage
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasDerivAtDerivedActionMaxCompactAverage
open MeasureTheory Matrix Filter Topology

noncomputable section

namespace GlobalTheory.KFinAvg

theorem hasDerivAt_exp_integral_dsigW (k r : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H))
    (μ : Measure (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ))
    (φ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℂ) (v : H)
    (D : List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ))
    (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hσ' : Formalism.MainNotions.S.IsURepOn (Formalism.QuantumDeterminants.UH (PI.UpqRep.Hpk k r)) σ) (hμ : GlobalTheory.KFinAvg.IsHaarKH k r μ)
    (hφ : Continuous φ) (hv : Formalism.MainNotions.S.IsSmoothVec (k := k) (r := r) σ v)
    (hD : ∀ Y ∈ D, Formalism.MainNotions.S.InLieHpk k r Y) (hX : Formalism.MainNotions.S.InLieHpk k r X) :
    HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X))
        (∫ g, φ g • Formalism.MainNotions.S.dsigW (k := k) (r := r) σ D (σ g v) ∂μ))
      (∫ g, φ g • Formalism.MainNotions.S.dsigW (k := k) (r := r) σ (X :: D) (σ g v) ∂μ) 0 := by
  have hσ : Formalism.MainNotions.S.IsURepOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) σ := hσ'
  obtain ⟨hprob, hK0, -, -⟩ := hμ
  have hKc := isCompact_KH k r
  have hae : ∀ᵐ g ∂μ, g ∈ GlobalTheory.ThA.KH k r := mem_ae_iff.2 hK0
  have hres : μ.restrict (GlobalTheory.ThA.KH k r) = μ := Measure.restrict_eq_self_of_ae_mem hae
  have hint : ∀ D' : List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ),
      (∀ Y ∈ D', Formalism.MainNotions.S.InLieHpk k r Y) →
      Integrable (fun g => φ g • Formalism.MainNotions.S.dsigW (k := k) (r := r) σ D' (σ g v)) μ := by
    intro D' hD'
    have h1 : ContinuousOn (fun g => φ g • Formalism.MainNotions.S.dsigW (k := k) (r := r) σ D' (σ g v)) (GlobalTheory.ThA.KH k r) :=
      hφ.continuousOn.smul ((Formalism.MainNotions.LowestKTypeMultiplicity.orbit_cont hσ hv D' hD').mono Set.inter_subset_left)
    have h2 : IntegrableOn (fun g => φ g • Formalism.MainNotions.S.dsigW (k := k) (r := r) σ D' (σ g v)) (GlobalTheory.ThA.KH k r) μ :=
      h1.integrableOn_compact hKc
    rwa [IntegrableOn, hres] at h2
  have hXD : ∀ Y ∈ X :: D, Formalism.MainNotions.S.InLieHpk k r Y := by
    intro Y hY
    rcases List.mem_cons.1 hY with h | h
    · rw [h]; exact hX
    · exact hD Y h
  have hexp := Formalism.MainNotions.LowestKTypeMultiplicity.exp_mem_UH hX
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (𝕜 := ℝ) (x₀ := (0 : ℝ))
    (F := fun (t : ℝ) g => σ (NormedSpace.exp ((t : ℂ) • X))
      (φ g • Formalism.MainNotions.S.dsigW (k := k) (r := r) σ D (σ g v)))
    (F' := fun (t : ℝ) g => σ (NormedSpace.exp ((t : ℂ) • X))
      (φ g • Formalism.MainNotions.S.dsigW (k := k) (r := r) σ (X :: D) (σ g v)))
    (bound := fun g => ‖φ g • Formalism.MainNotions.S.dsigW (k := k) (r := r) σ (X :: D) (σ g v)‖) (s := Set.univ)
    Filter.univ_mem
    (Filter.Eventually.of_forall fun t =>
      ((σ (NormedSpace.exp ((t : ℂ) • X))).integrable_comp (hint D hD)).aestronglyMeasurable)
    ((σ _).integrable_comp (hint D hD))
    ((σ _).integrable_comp (hint _ hXD)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun g t _ => (hσ.2.1 _ (hexp t) _).le)
    (hint _ hXD).norm
    (by
      filter_upwards [hae] with g hg t _
      have hsm := Formalism.MainNotions.LowestKTypeMultiplicity.smooth_orbit hσ hv hg.1
      have h0 := (Formalism.MainNotions.LowestKTypeMultiplicity.dsigW_hasDeriv hσ hsm D hD hX).const_smul (φ g)
      have h1 := ((σ (NormedSpace.exp ((t : ℂ) • X))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h0
      rw [← sub_self t] at h1
      have h2 := h1.comp_sub_const t t
      simp only [map_smul]
      convert (preTransparency := .reducible) h2 using 1
      · funext s
        have e : NormedSpace.exp ((s : ℂ) • X) =
            NormedSpace.exp ((t : ℂ) • X) * NormedSpace.exp (((s - t : ℝ) : ℂ) • X) := by
          rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left _).smul_right _), ← add_smul]
          congr 2
          push_cast; ring
        rw [e, hσ.1.2 _ (hexp t) _ (hexp (s - t))]
        simp only [Function.comp, Pi.smul_apply, ContinuousLinearMap.coe_restrictScalars', map_smul]
        rfl
      · simp)
  have h3 := key.2
  simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, hσ.1.1, one_apply_eq_self] at h3
  convert h3 using 1
  funext t
  exact ((σ _).integral_comp_comm (hint D hD)).symm

end GlobalTheory.KFinAvg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasDerivAtDerivedActionMaxCompactAverageStatement
open MeasureTheory Matrix Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDerivAt_derived_action_max_compact_average : ∀ (k r : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (μ : Measure (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (φ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℂ) (v : H) (D : List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ), Formalism.MainNotions.S.IsURepOn (Formalism.QuantumDeterminants.UH (PI.UpqRep.Hpk k r)) σ → GlobalTheory.KFinAvg.IsHaarKH k r μ → Continuous φ → Formalism.MainNotions.S.IsSmoothVec (k := k) (r := r) σ v → (∀ Y ∈ D, Formalism.MainNotions.S.InLieHpk k r Y) → Formalism.MainNotions.S.InLieHpk k r X → HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) (∫ g, φ g • Formalism.MainNotions.S.dsigW (k := k) (r := r) σ D (σ g v) ∂μ)) (∫ g, φ g • Formalism.MainNotions.S.dsigW (k := k) (r := r) σ (X :: D) (σ g v) ∂μ) 0 := by
  first | exact @GlobalTheory.KFinAvg.hasDerivAt_exp_integral_dsigW | exact GlobalTheory.KFinAvg.hasDerivAt_exp_integral_dsigW | (intros; apply GlobalTheory.KFinAvg.hasDerivAt_exp_integral_dsigW <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryRealTraceBumpPowFiniteTranslationStablePo
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryRealTraceBumpPowFiniteTranslationStablePo
open MeasureTheory Matrix Filter Topology

noncomputable section

namespace GlobalTheory.KFinAvg.PeakPoly

def coord (n : ℕ) : Option ((Fin n × Fin n) × Bool) → Matrix (Fin n) (Fin n) ℂ → ℂ
  | none, _ => 1
  | some ((i, j), false), g => g i j
  | some ((i, j), true), g => star (g i j)

theorem continuous_coord (n : ℕ) (d : Option ((Fin n × Fin n) × Bool)) : Continuous (coord n d) := by
  rcases d with _ | ⟨⟨i, j⟩, _ | _⟩
  · exact continuous_const
  · exact continuous_id.matrix_elem i j
  · exact (continuous_id.matrix_elem i j).star

theorem prod_expand {ι D X : Type*} [Fintype ι] [DecidableEq ι] [Fintype D]
    (x : D → X → ℂ) (c : ι → D → ℂ) (g : X) :
    ∏ j, ∑ e, c j e * x e g = ∑ t : ι → D, (∏ j, c j (t j)) * ∏ j, x (t j) g := by
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.prod_mul_distrib]

theorem coord_translate (n : ℕ) (a : Matrix (Fin n) (Fin n) ℂ) (d : Option ((Fin n × Fin n) × Bool)) :
    ∃ T : Option ((Fin n × Fin n) × Bool) → ℂ, ∀ g, coord n d (a * g) = ∑ e, T e * coord n e g := by
  have hmem : (fun g => coord n d (a * g)) ∈ Submodule.span ℂ (Set.range (coord n)) := by
    rcases d with _ | ⟨⟨i, j⟩, _ | _⟩
    · have : (fun g : Matrix (Fin n) (Fin n) ℂ => coord n none (a * g)) = coord n none := by
        funext g; rfl
      rw [this]; exact Submodule.subset_span ⟨none, rfl⟩
    · have : (fun g : Matrix (Fin n) (Fin n) ℂ => coord n (some ((i, j), false)) (a * g)) =
          ∑ l, a i l • coord n (some ((l, j), false)) := by
        funext g; simp [coord, Matrix.mul_apply, Finset.sum_apply]
      rw [this]
      exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
    · have : (fun g : Matrix (Fin n) (Fin n) ℂ => coord n (some ((i, j), true)) (a * g)) =
          ∑ l, star (a i l) • coord n (some ((l, j), true)) := by
        funext g; simp [coord, Matrix.mul_apply, Finset.sum_apply, star_sum]
      rw [this]
      exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  obtain ⟨T, hT⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hmem
  refine ⟨T, fun g => ?_⟩
  have := congrFun hT g
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
  exact this.symm

theorem peak_expand (n : ℕ) :
    ∃ c : Option ((Fin n × Fin n) × Bool) → ℂ, ∀ g, ((peak n g : ℝ) : ℂ) = ∑ e, c e * coord n e g := by
  have hmem : (fun g => ((peak n g : ℝ) : ℂ)) ∈ Submodule.span ℂ (Set.range (coord n)) := by
    have : (fun g => ((peak n g : ℝ) : ℂ)) = (1 / 2 : ℂ) • coord n none +
        ∑ i, (1 / (4 * (n : ℂ))) • (coord n (some ((i, i), false)) + coord n (some ((i, i), true))) := by
      funext g
      simp only [peak, Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, coord]
      push_cast
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Complex.re_eq_add_conj, ← Finset.mul_sum, Finset.sum_add_distrib, Matrix.trace,
        map_sum]
      simp only [Matrix.diag, Complex.star_def]
      ring
    rw [this]
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)) ?_
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.add_mem _ (Submodule.subset_span ⟨_, rfl⟩) (Submodule.subset_span ⟨_, rfl⟩))
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hmem
  refine ⟨c, fun g => ?_⟩
  have := congrFun hc g
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
  exact this.symm

end GlobalTheory.KFinAvg.PeakPoly

namespace GlobalTheory.KFinAvg
open PeakPoly

theorem peak_pow_polynomial : ∀ n m : ℕ, ∃ (N : ℕ) (b : Fin N → Matrix (Fin n) (Fin n) ℂ → ℂ) (c : Fin N → ℂ),
    (∀ j, Continuous (b j)) ∧ (∀ g, ((GlobalTheory.KFinAvg.peak n g ^ m : ℝ) : ℂ) = ∑ j, c j * b j g) ∧
    ∀ (a : Matrix (Fin n) (Fin n) ℂ) (j : Fin N), ∃ d : Fin N → ℂ, ∀ g, b j (a * g) = ∑ i, d i * b i g := by
  intro n m
  classical
  let e := Fintype.equivFin (Fin m → Option ((Fin n × Fin n) × Bool))
  let bS : (Fin m → Option ((Fin n × Fin n) × Bool)) → Matrix (Fin n) (Fin n) ℂ → ℂ :=
    fun s g => ∏ j, coord n (s j) g
  obtain ⟨c0, hc0⟩ := peak_expand n
  refine ⟨Fintype.card (Fin m → Option ((Fin n × Fin n) × Bool)), fun i => bS (e.symm i),
    fun i => ∏ j, c0 (e.symm i j), ?_, ?_, ?_⟩
  · intro i
    exact continuous_finsetProd _ fun j _ => continuous_coord n _
  · intro g
    have h1 : ((peak n g ^ m : ℝ) : ℂ) = ∏ _j : Fin m, ∑ d, c0 d * coord n d g := by
      rw [Complex.ofReal_pow, hc0 g, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [h1, prod_expand (fun d g => coord n d g) (fun _ => c0) g]
    exact (Equiv.sum_comp e.symm (fun t => (∏ j, c0 (t j)) * ∏ j, coord n (t j) g)).symm
  · intro a i
    choose T hT using fun j => coord_translate n a (e.symm i j)
    refine ⟨fun k => ∏ j, T j (e.symm k j), fun g => ?_⟩
    show ∏ j, coord n (e.symm i j) (a * g) = _
    simp_rw [hT]
    rw [prod_expand (fun d g => coord n d g) T g]
    exact (Equiv.sum_comp e.symm (fun t => (∏ j, T j (t j)) * ∏ j, coord n (t j) g)).symm

end GlobalTheory.KFinAvg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryRealTraceBumpPowFiniteTranslationStablePoStatement
open MeasureTheory Matrix Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryRealTraceBump_pow_finite_translation_stable_polys : ∀ n m : ℕ, ∃ (N : ℕ) (b : Fin N → Matrix (Fin n) (Fin n) ℂ → ℂ) (c : Fin N → ℂ), (∀ j, Continuous (b j)) ∧ (∀ g, ((GlobalTheory.KFinAvg.peak n g ^ m : ℝ) : ℂ) = ∑ j, c j * b j g) ∧ ∀ (a : Matrix (Fin n) (Fin n) ℂ) (j : Fin N), ∃ d : Fin N → ℂ, ∀ g, b j (a * g) = ∑ i, d i * b i g := by
  first | exact @GlobalTheory.KFinAvg.peak_pow_polynomial | exact GlobalTheory.KFinAvg.peak_pow_polynomial | (intros; apply GlobalTheory.KFinAvg.peak_pow_polynomial <;> assumption)
end
end

open MeasureTheory Matrix Filter Topology

noncomputable section

namespace GlobalTheory.KFinAvg

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}

theorem dsigW_sub_avg {μ : Measure (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)}
    {φ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℂ} {v : H}
    (hU : Formalism.MainNotions.S.IsURepOn (Formalism.QuantumDeterminants.UH (PI.UpqRep.Hpk k r)) σ) (hv : Formalism.MainNotions.S.IsSmoothVec (k := k) (r := r) σ v)
    (hD' : ∀ (D : List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ))
      (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ),
      (∀ Y ∈ D, Formalism.MainNotions.S.InLieHpk k r Y) → Formalism.MainNotions.S.InLieHpk k r X →
      HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) (∫ g, φ g • Formalism.MainNotions.S.dsigW (k := k) (r := r) σ D (σ g v) ∂μ))
        (∫ g, φ g • Formalism.MainNotions.S.dsigW (k := k) (r := r) σ (X :: D) (σ g v) ∂μ) 0) :
    ∀ D : List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ), (∀ Y ∈ D, Formalism.MainNotions.S.InLieHpk k r Y) →
      Formalism.MainNotions.S.dsigW (k := k) (r := r) σ D (v - ∫ g, φ g • σ g v ∂μ) =
        Formalism.MainNotions.S.dsigW (k := k) (r := r) σ D v - ∫ g, φ g • Formalism.MainNotions.S.dsigW (k := k) (r := r) σ D (σ g v) ∂μ := by
  intro D
  induction D with
  | nil => intro _; rfl
  | cons X D ih =>
    intro hD
    have hX : Formalism.MainNotions.S.InLieHpk k r X := hD X List.mem_cons_self
    have hD1 : ∀ Y ∈ D, Formalism.MainNotions.S.InLieHpk k r Y := fun Y hY => hD Y (List.mem_cons_of_mem _ hY)
    show deriv (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) (Formalism.MainNotions.S.dsigW (k := k) (r := r) σ D _)) 0 = _
    rw [ih hD1]
    simp only [map_sub]
    exact ((Formalism.MainNotions.LowestKTypeMultiplicity.dsigW_hasDeriv hU hv D hD1 hX).sub (hD' D X hD1 hX)).deriv

theorem kDense : Formalism.MainNotions.S.Pv.AmpDD.KDense := by
  intro k r ε lam H _ _ _ σ _ hDS v hv Ws hWs e he
  obtain ⟨-, hU, -⟩ := GlobalTheory.BesselMapOne.rep_of_isDSHpk hDS
  obtain ⟨μ, hμ⟩ := GlobalTheory.T.exists_isHaarProbabilityMaxCompactHermitian k r
  have hv' : Formalism.MainNotions.S.IsSmoothVec (k := k) (r := r) σ v := hv
  obtain ⟨hpc, hp1, hp01, hpδ⟩ := GlobalTheory.T.unitaryRealTraceBump_peak_properties (2 * r + k + 1) (Nat.succ_pos _)
  have hKc : IsCompact (GlobalTheory.ThA.KH k r) := isCompact_KH k r
  have hK1 : (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ GlobalTheory.ThA.KH k r :=
    ⟨by show (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ᴴ * _ * 1 = _; simp,
      one_mem _⟩
  have hpK : ∀ x ∈ GlobalTheory.ThA.KH k r, 0 ≤ peak (2 * r + k + 1) x ∧ peak (2 * r + k + 1) x ≤ 1 :=
    fun x hx => hp01 x hx.2
  have hpU : ∀ U ∈ 𝓝 (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ), ∃ δ < 1,
      ∀ x ∈ GlobalTheory.ThA.KH k r, x ∉ U → peak (2 * r + k + 1) x ≤ δ := fun U hU' => by
    obtain ⟨δ, hδ, h⟩ := hpδ U hU'
    exact ⟨δ, hδ, fun x hx hxU => h x hx.2 hxU⟩
  have hσ1 : σ 1 = 1 := hU.1.1
  have hconv : ∀ w ∈ Ws, Tendsto (fun m : ℕ => ∫ g, peakN μ m g • Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w (σ g v) ∂μ)
      atTop (𝓝 (Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w v)) := by
    intro w hw
    have hc := (Formalism.MainNotions.LowestKTypeMultiplicity.orbit_cont hU hv' w (hWs w hw)).mono
      (Set.inter_subset_left : GlobalTheory.ThA.KH k r ⊆ _)
    have := GlobalTheory.T.tendsto_integral_normalised_pow_smul_of_unique_peak _ μ hμ.1 _ 1 _ hKc hμ.2.1 hK1 hμ.2.2.2 hpc hp1 hpK hpU H _ hc
    rw [hσ1, one_apply_eq_self] at this
    exact this
  set L := Ws.length
  have hε : 0 < e / (L + 1) := by positivity
  have hev : ∀ᶠ m : ℕ in atTop, ∀ w ∈ {w | w ∈ Ws},
      dist (∫ g, peakN μ m g • Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w (σ g v) ∂μ)
        (Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w v) < e / (L + 1) :=
    (Filter.eventually_all_finite Ws.finite_toSet).2 fun w hw => Metric.tendsto_nhds.1 (hconv w hw) _ hε
  obtain ⟨m, hm⟩ := hev.exists
  obtain ⟨N, b, c, hbc, hpoly, htr⟩ := GlobalTheory.T.unitaryRealTraceBump_pow_finite_translation_stable_polys (2 * r + k + 1) m
  set Z : ℝ := ∫ h, peak (2 * r + k + 1) h ^ m ∂μ
  have e1 : ∀ g, peakN μ m g = ∑ j, (c j / (Z : ℂ)) * b j g := fun g => by
    show ((peak (2 * r + k + 1) g ^ m / Z : ℝ) : ℂ) = _
    rw [Complex.ofReal_div, hpoly g, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  refine ⟨∫ g, peakN μ m g • σ g v ∂μ, ?_, ?_⟩
  · have := GlobalTheory.T.integral_translate_family_isKFinite_hermitian k r H σ μ hU hμ N b hbc htr (fun j => c j / (Z : ℂ)) v
    simpa only [← e1] using this
  · have hD' := fun D X hD hX => GlobalTheory.T.hasDerivAt_derived_action_max_compact_average k r H σ μ (peakN μ m) v D X hU hμ
      (by rw [show peakN μ m = fun g => ∑ j, (c j / (Z : ℂ)) * b j g from funext e1]
          exact continuous_finsetSum _ fun j _ => continuous_const.mul (hbc j)) hv' hD hX
    have hterm : ∀ w ∈ Ws, ‖PI.UpqRep.dsigW (k := k) (r := r) σ w (v - ∫ g, peakN μ m g • σ g v ∂μ)‖ ≤ e / (L + 1) := by
      intro w hw
      rw [Formalism.MainNotions.BridgeCS3d.dsigW_eq, dsigW_sub_avg hU hv' hD' w (hWs w hw), norm_sub_rev, ← dist_eq_norm]
      exact (hm w hw).le
    calc (Ws.map fun w => ‖PI.UpqRep.dsigW (k := k) (r := r) σ w (v - ∫ g, peakN μ m g • σ g v ∂μ)‖).sum
        ≤ (Ws.map fun _ => e / (L + 1)).sum := List.sum_le_sum (fun w hw => hterm w hw)
      _ = L * (e / (L + 1)) := by simp [L, List.map_const', List.sum_replicate, nsmul_eq_mul]
      _ < e := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith

end GlobalTheory.KFinAvg
end
end

open Formalism.MainNotions.S

namespace GlobalTheory.KFinDenseDS

theorem kFin_dense : ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)),
    Formalism.QuantumDeterminants.IsHCParam lam → PI.UpqRep.IsDSHpk k r ε lam σ →
    ∀ v ∈ smoothVecs (k := k) (r := r) σ,
    ∀ Ws : List (List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)), (∀ w ∈ Ws, ∀ X ∈ w, InLieHpk k r X) →
    ∀ δ : ℝ, 0 < δ → ∃ a : H, PI.UpqRep.IsKFinHpk (k := k) (r := r) σ a ∧
      (Ws.map fun w => ‖dsigW σ w (v - a)‖).sum < δ := by
  intro k r ε lam H _ _ _ σ hl hds v hv Ws hWs δ hδ
  obtain ⟨a, ha, hs⟩ := GlobalTheory.KFinAvg.kDense k r ε lam H σ hl hds v hv Ws hWs δ hδ
  refine ⟨a, ha, ?_⟩
  simpa only [Formalism.MainNotions.BridgeCS3d.dsigW_eq] using hs

end GlobalTheory.KFinDenseDS
end

namespace GlobalTheory.KFinDenseCarrier

theorem kFinDense_main : Formalism.L2.SG.Pf.CarrierXAll.KFinDense := by
  unfold Formalism.L2.SG.Pf.CarrierXAll.KFinDense
  exact GlobalTheory.KFinDenseDS.kFin_dense

instance : Fact (Formalism.L2.SG.Pf.CarrierXAll.KFinDense) := ⟨kFinDense_main⟩

end GlobalTheory.KFinDenseCarrier
