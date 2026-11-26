module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.DisintegrationDensityContinuous
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsNhdsZeroPrincipalEqZero
public import ReciprocityTheory.Chebotarev.EulerSum

@[expose] public section

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.IntegralAlmostAllPlaces
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.IntegralAlmostAllPlaces
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.GoodInt

theorem valued_algebraMap {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (x : F) :
    Valued.v (algebraMap F (Fv F v) x) = v.valuation F x := by
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x

theorem eventually_le_one {F : Type} [Field F] [NumberField F] (x : F) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, v.valuation F x ≤ 1 := by
  have h := HeightOneSpectrum.Support.finite (𝓞 F) x
  rw [Filter.eventually_cofinite]
  refine h.subset fun v hv => ?_
  exact not_le.mp hv

theorem eventually_eq_one {F : Type} [Field F] [NumberField F] (x : F) (hx : x ≠ 0) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, v.valuation F x = 1 := by
  filter_upwards [eventually_le_one x, eventually_le_one x⁻¹] with v h1 h2
  refine le_antisymm h1 ?_
  rw [map_inv₀] at h2
  have h0 : v.valuation F x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  exact (inv_le_one₀ (zero_lt_iff.mpr h0)).mp h2

theorem repr_inclR {F E : Type} [Field F] [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)
    (R : Type) [CommRing R] [Algebra F R] (x : E) (k : Fin d) :
    (Algebra.TensorProduct.basis R b).repr (inclR R x) k = algebraMap F R (b.repr x k) := by
  change (Algebra.TensorProduct.basis R b).repr ((1 : R) ⊗ₜ[F] x) k = _
  rw [Algebra.TensorProduct.basis_repr_tmul]
  simp

theorem rational_integral_units : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), (∀ x : E, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr (inclR (Fv F v) x) k ∈ v.adicCompletionIntegers F) ∧ ∀ x : F, x ≠ 0 → ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, Valued.v (algebraMap F (Fv F v) x) = 1 := by
  intro F E _ _ _ _ _ σ _ d b
  refine ⟨fun x => ?_, fun x hx => ?_⟩
  · have h : ∀ k : Fin d, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
        v.valuation F (b.repr x k) ≤ 1 := fun k => eventually_le_one _
    filter_upwards [Filter.eventually_all.mpr h] with v hv k
    rw [repr_inclR, HeightOneSpectrum.mem_adicCompletionIntegers, valued_algebraMap]
    exact hv k
  · filter_upwards [eventually_eq_one x hx] with v hv
    rw [valued_algebraMap, hv]

end GlobalTheory.CompanionTheory.SW.GoodInt
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.IntegralAlmostAllPlacesStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_almost_all_places : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), (∀ x : E, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr (inclR (Fv F v) x) k ∈ v.adicCompletionIntegers F) ∧ ∀ x : F, x ≠ 0 → ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, Valued.v (algebraMap F (Fv F v) x) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.SW.GoodInt.rational_integral_units | exact GlobalTheory.CompanionTheory.SW.GoodInt.rational_integral_units | (intros; apply GlobalTheory.CompanionTheory.SW.GoodInt.rational_integral_units <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianOneByOneIsScalar
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianOneByOneIsScalar
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.HermOne

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}

theorem exists_ne (h : IsCMExt F E σ) : ∃ x : E, σ x ≠ x := by
  by_contra hc
  push_neg at hc
  obtain ⟨w⟩ := (inferInstance : Nonempty (NumberField.InfinitePlace E))
  have hreal : w.IsReal := by
    rw [← NumberField.InfinitePlace.mk_embedding w, NumberField.InfinitePlace.isReal_mk_iff,
      NumberField.ComplexEmbedding.isReal_iff]
    refine RingHom.ext fun x ↦ ?_
    rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
    change star (w.embedding x) = w.embedding x
    rw [← h.2.2.2, hc]
  exact NumberField.InfinitePlace.not_isReal_iff_isComplex.2 (h.2.1.isComplex w) hreal

theorem exists_eq_algebraMap (h : IsCMExt F E σ) {x : E} (hx : σ x = x) :
    ∃ β : F, x = algebraMap F E β := by
  by_contra hc
  push_neg at hc
  have hli : LinearIndependent F ![(1 : E), x] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
    have ht : t = 0 := by
      by_contra ht
      have htE : algebraMap F E t ≠ 0 := (map_ne_zero _).2 ht
      apply hc (-(s / t))
      rw [map_neg, map_div₀]
      field_simp
      linear_combination hst
    refine ⟨?_, ht⟩
    rw [ht, map_zero, zero_mul, add_zero] at hst
    exact (map_eq_zero_iff _ (algebraMap F E).injective).1 hst
  have hcard : Fintype.card (Fin 2) = Module.finrank F E := by
    rw [Fintype.card_fin, h.2.2.1]
  obtain ⟨y, hy⟩ := exists_ne h
  have hid : σ.toLinearMap = LinearMap.id := by
    refine (basisOfLinearIndependentOfCardEqFinrank hli hcard).ext fun i ↦ ?_
    fin_cases i <;> simp [hx]
  exact hy (by simpa using LinearMap.congr_fun hid y)

end GlobalTheory.CompanionTheory.SW.HermOne

namespace GlobalTheory.CompanionTheory.SW

theorem hermOne_eq_scal : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (T : Matrix (Fin 1) (Fin 1) E) (hT : ∀ a b, σ (T b a) = T a b), ∃ β : F, T = (fun _ _ => algebraMap F E β) ∧ (T.det ≠ 0 → β ≠ 0) ∧ ∀ (R : Type) [CommRing R] [Algebra F R], hermOf R σ T hT = hermScal R σ (algebraMap F R β) := by
  intro F E _ _ _ _ _ σ h T hT
  obtain ⟨β, hβ⟩ := HermOne.exists_eq_algebraMap h (hT 0 0)
  have hTβ : T = fun _ _ => algebraMap F E β := by
    funext a b
    rw [Subsingleton.elim a 0, Subsingleton.elim b 0]
    exact hβ
  refine ⟨β, hTβ, fun hd hb => hd ?_, fun R _ _ => ?_⟩
  · rw [Matrix.det_fin_one, hβ, hb, map_zero]
  · apply Subtype.ext
    funext a b
    rw [Subsingleton.elim a 0, Subsingleton.elim b 0]
    change inclR R (T 0 0) = (algebraMap F R β) ⊗ₜ[F] (1 : E)
    rw [hβ, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    simp [inclR, TensorProduct.smul_tmul]

end GlobalTheory.CompanionTheory.SW
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianOneByOneIsScalarStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_one_by_one_is_scalar : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (T : Matrix (Fin 1) (Fin 1) E) (hT : ∀ a b, σ (T b a) = T a b), ∃ β : F, T = (fun _ _ => algebraMap F E β) ∧ (T.det ≠ 0 → β ≠ 0) ∧ ∀ (R : Type) [CommRing R] [Algebra F R], hermOf R σ T hT = hermScal R σ (algebraMap F R β) := by
  first | exact @GlobalTheory.CompanionTheory.SW.hermOne_eq_scal | exact GlobalTheory.CompanionTheory.SW.hermOne_eq_scal | (intros; apply GlobalTheory.CompanionTheory.SW.hermOne_eq_scal <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.DisintegrationDensityExists
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.DisintegrationDensityExists
open MeasureTheory Topology Matrix Set
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.SW.FibreUniq

theorem measure_eq_of_lintegral_eq {V : Type} [TopologicalSpace V] [LocallyCompactSpace V]
    [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V]
    (m m' : Measure V) (O : Set V) (hO : IsOpen O) (hm : m Oᶜ = 0) (hm' : m' Oᶜ = 0)
    (h : ∀ φ : V → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ O → (∀ v, 0 ≤ φ v) →
      Integrable φ m ∧ ∫⁻ v, ENNReal.ofReal (φ v) ∂m = ∫⁻ v, ENNReal.ofReal (φ v) ∂m') :
    m = m' := by
  have hK : ∀ K : Set V, IsCompact K → K ⊆ O → m.restrict K = m'.restrict K := by
    intro K hK hKO
    obtain ⟨χ, h1, hc, hs, h01⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hK hO hKO
    have hχm : Measurable fun v => ENNReal.ofReal (χ v) :=
      ENNReal.measurable_ofReal.comp χ.continuous.measurable
    have hint := (h χ χ.continuous hc hs (fun v => (h01 v).1)).1
    haveI : IsFiniteMeasure (m.withDensity fun v => ENNReal.ofReal (χ v)) :=
      isFiniteMeasure_withDensity_ofReal hint.2
    have key : (m.withDensity fun v => ENNReal.ofReal (χ v)) =
        m'.withDensity fun v => ENNReal.ofReal (χ v) := by
      apply ext_of_forall_lintegral_eq_of_IsFiniteMeasure
      intro g
      have hg : Measurable fun v => (g v : ℝ≥0∞) :=
        measurable_coe_nnreal_ennreal.comp g.continuous.measurable
      rw [lintegral_withDensity_eq_lintegral_mul _ hχm hg,
        lintegral_withDensity_eq_lintegral_mul _ hχm hg]
      have := (h (fun v => χ v * (g v : ℝ))
        (χ.continuous.mul (NNReal.continuous_coe.comp g.continuous))
        (HasCompactSupport.mul_right (f := fun v => χ v) hc)
        ((tsupport_mul_subset_left (f := fun v => χ v)).trans hs)
        (fun v => mul_nonneg (h01 v).1 (g v).2)).2
      have e : ∀ v, ENNReal.ofReal (χ v * (g v : ℝ)) = ENNReal.ofReal (χ v) * (g v : ℝ≥0∞) := by
        intro v
        rw [ENNReal.ofReal_mul (h01 v).1, ENNReal.ofReal_coe_nnreal]
      simpa only [e, Pi.mul_apply] using this
    have aux : ∀ n : Measure V, (n.withDensity fun v => ENNReal.ofReal (χ v)).restrict K
        = n.restrict K := by
      intro n
      rw [restrict_withDensity hK.measurableSet]
      have : (fun v => ENNReal.ofReal (χ v)) =ᵐ[n.restrict K] 1 := by
        filter_upwards [ae_restrict_mem hK.measurableSet] with v hv
        simp [h1 hv]
      rw [withDensity_congr_ae this, withDensity_one]
    rw [← aux m, ← aux m', key]
  have hx : ∀ x ∈ O, ∃ K : Set V, K ∈ 𝓝[O] x ∧ IsCompact K ∧ K ⊆ O := by
    intro x hx
    obtain ⟨K, hK1, hK2, hK3⟩ := local_compact_nhds (hO.mem_nhds hx)
    exact ⟨K, mem_nhdsWithin_of_mem_nhds hK1, hK3, hK2⟩
  choose! K hK1 hK2 hK3 using hx
  obtain ⟨s, hsO, hsc, hcov⟩ := TopologicalSpace.countable_cover_nhdsWithin hK1
  have hU : m.restrict (⋃ x ∈ s, K x) = m'.restrict (⋃ x ∈ s, K x) :=
    (Measure.restrict_biUnion_congr hsc).2 fun x hx => hK _ (hK2 x (hsO hx)) (hK3 x (hsO hx))
  have r : ∀ n : Measure V, n Oᶜ = 0 → n.restrict (⋃ x ∈ s, K x) = n := by
    intro n hn
    apply Measure.restrict_eq_self_of_ae_mem
    have : ∀ᵐ v ∂n, v ∈ O := hn
    filter_upwards [this] with v hv using hcov hv
  rw [← r m hm, ← r m' hm', hU]

theorem ae_eq_of_isFibreFamily {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V]
    [TopologicalSpace X] [MeasurableSpace X] {μ : Measure V} {ν : Measure X} {f : V → Y}
    {g : V → X} {ι : X → Y} (hι : Function.Injective ι) (hf : ∀ v, f v = ι (g v))
    {U : Set V} {B : Set X} {fib : X → Measure V}
    (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν B fib) (b : X) :
    ∀ᵐ v ∂(fib b), g v = b ∧ v ∈ U := by
  have : ∀ᵐ v ∂(fib b), v ∈ f ⁻¹' {ι b} ∩ U := h.1 b
  filter_upwards [this] with v hv
  refine ⟨hι ?_, hv.2⟩
  rw [← hf v]
  exact hv.1

theorem lintegral_preimage {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] {μ : Measure V} {ν : Measure X}
    {f : V → Y} {g : V → X} {ι : X → Y} (hι : Function.Injective ι) (hg : Continuous g)
    (hf : ∀ v, f v = ι (g v)) {O U : Set V} {B : Set X} {fib : X → Measure V}
    (hO : IsOpen O) (hU : O ⊆ U) (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν B fib)
    (φ : V → ℝ≥0∞) (hφ : Measurable φ) (hs : ∀ v, v ∉ O → φ v = 0)
    (S : Set X) (hS : MeasurableSet S) :
    ∫⁻ v in O, (g ⁻¹' S).indicator φ v ∂μ = ∫⁻ b in S, ∫⁻ v, φ v ∂(fib b) ∂ν := by
  have h2 := h.2.1 ((g ⁻¹' S).indicator φ) (hφ.indicator (hg.measurable hS))
  have e1 : ∫⁻ v in U, (g ⁻¹' S).indicator φ v ∂μ = ∫⁻ v in O, (g ⁻¹' S).indicator φ v ∂μ := by
    have : (g ⁻¹' S).indicator φ = O.indicator ((g ⁻¹' S).indicator φ) := by
      funext v
      by_cases hv : v ∈ O
      · rw [indicator_of_mem hv]
      · rw [indicator_of_notMem hv]
        exact indicator_apply_eq_zero.2 fun _ => hs v hv
    conv_lhs => rw [this]
    rw [lintegral_indicator hO.measurableSet, Measure.restrict_restrict hO.measurableSet,
      inter_eq_left.2 hU]
  rw [← e1, h2, ← lintegral_indicator hS]
  congr 1
  funext b
  have hb := ae_eq_of_isFibreFamily hι hf h b
  by_cases hbS : b ∈ S
  · rw [indicator_of_mem hbS]
    apply lintegral_congr_ae
    filter_upwards [hb] with v hv
    exact indicator_of_mem (by simpa [mem_preimage, hv.1] using hbS) _
  · rw [indicator_of_notMem hbS, ← lintegral_zero (μ := fib b)]
    apply lintegral_congr_ae
    filter_upwards [hb] with v hv
    exact indicator_of_notMem (by simpa [mem_preimage, hv.1] using hbS) _

theorem fibreFamily_eq (V X Y : Type) [TopologicalSpace V] [LocallyCompactSpace V]
    [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V]
    [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X)
    [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν] [ν.IsOpenPosMeasure]
    (f : V → Y) (g : V → X) (ι : X → Y) (hι : Function.Injective ι) (hg : Continuous g)
    (hf : ∀ v, f v = ι (g v)) (B B' : Set X) (hB : IsOpen B) (hB' : IsOpen B') (hBB : B' ⊆ B)
    (fib fib' : X → Measure V)
    (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' B) ν B fib)
    (h' : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' B') ν B' fib')
    (b : X) (hb : b ∈ B') : fib' b = fib b := by
  have hO : IsOpen (g ⁻¹' B') := hB'.preimage hg
  have hOU : g ⁻¹' B' ⊆ g ⁻¹' B := preimage_mono hBB
  have carried : ∀ n : Measure V, (∀ᵐ v ∂n, g v = b) → n (g ⁻¹' B')ᶜ = 0 := by
    intro n hn
    have : ∀ᵐ v ∂n, v ∈ g ⁻¹' B' := by
      filter_upwards [hn] with v hv
      simpa [mem_preimage, hv] using hb
    exact this
  refine measure_eq_of_lintegral_eq _ _ (g ⁻¹' B') hO
    (carried _ ((ae_eq_of_isFibreFamily hι hf h' b).mono fun _ hv => hv.1))
    (carried _ ((ae_eq_of_isFibreFamily hι hf h b).mono fun _ hv => hv.1)) ?_
  intro φ hφ hc hs h0
  obtain ⟨hi, hc1⟩ := h.2.2 φ hφ hc (hs.trans hOU)
  obtain ⟨hi', hc2⟩ := h'.2.2 φ hφ hc hs
  refine ⟨hi' b hb, ?_⟩
  have hφm : Measurable fun v => ENNReal.ofReal (φ v) :=
    ENNReal.measurable_ofReal.comp hφ.measurable
  have hφ0 : ∀ v, v ∉ g ⁻¹' B' → ENNReal.ofReal (φ v) = 0 := by
    intro v hv
    rw [image_eq_zero_of_notMem_tsupport fun h => hv (hs h), ENNReal.ofReal_zero]
  have c : ContinuousOn (fun b => ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib b)) B' :=
    (ENNReal.continuous_ofReal.comp_continuousOn (hc1.mono hBB)).congr fun b hb =>
      (ofReal_integral_eq_lintegral_ofReal (hi b (hBB hb)) (Filter.Eventually.of_forall h0)).symm
  have c' : ContinuousOn (fun b => ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib' b)) B' :=
    (ENNReal.continuous_ofReal.comp_continuousOn hc2).congr fun b hb =>
      (ofReal_integral_eq_lintegral_ofReal (hi' b hb) (Filter.Eventually.of_forall h0)).symm
  refine GlobalTheory.T.continuous_densities_eq_of_integrals_on_compacts X ν B' hB' _ _ c' c (fun S hS _ => ?_) b hb
  rw [← lintegral_preimage hι hg hf hO subset_rfl h' _ hφm hφ0 S hS.measurableSet,
    ← lintegral_preimage hι hg hf hO hOU h _ hφm hφ0 S hS.measurableSet]

end GlobalTheory.CompanionTheory.SW.FibreUniq
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.DisintegrationDensityExistsStatement
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_family_eq_on_open_subset : ∀ (V X Y : Type) [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X) [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν] [ν.IsOpenPosMeasure] (f : V → Y) (g : V → X) (ι : X → Y), Function.Injective ι → Continuous g → (∀ v, f v = ι (g v)) → ∀ (B B' : Set X), IsOpen B → IsOpen B' → B' ⊆ B → ∀ fib fib' : X → Measure V, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' B) ν B fib → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' B') ν B' fib' → ∀ b ∈ B', fib' b = fib b := by
  first | exact @GlobalTheory.CompanionTheory.SW.FibreUniq.fibreFamily_eq | exact GlobalTheory.CompanionTheory.SW.FibreUniq.fibreFamily_eq | (intros; apply GlobalTheory.CompanionTheory.SW.FibreUniq.fibreFamily_eq <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ArithmeticUnitaryGroupDiscrete
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ArithmeticUnitaryGroupDiscrete
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW

theorem rational_countable_discrete : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → Countable (HFinIn (AF F) σ J) ∧ ∃ U ∈ 𝓝 (1 : HA (AF F) σ J), ∀ h ∈ U, HA.mat (AF F) σ J h ∈ HFin (AF F) σ J → h = 1 := by
  intro F E _ _ _ _ _ σ hσ M J _
  have hfr : Module.finrank F E = 2 := hσ.2.2.1
  have : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  constructor
  · have : Countable E := (Module.finBasis ℚ E).equivFun.toEquiv.injective.countable
    have : Countable (Matrix (Fin M) (Fin M) E) :=
      inferInstanceAs (Countable (Fin M → Fin M → E))
    have : Countable (GL (Fin M) E) :=
      (Units.val_injective : Function.Injective
        (Units.val : GL (Fin M) E → Matrix (Fin M) (Fin M) E)).countable
    have hS : ((HFin (AF F) σ J : Subgroup (GL (Fin M) (AF F ⊗[F] E))) :
        Set (GL (Fin M) (AF F ⊗[F] E))).Countable := by
      unfold HFin
      rw [Subgroup.coe_map]
      exact (Set.to_countable _).image _
    have := hS.to_subtype
    let f : HFinIn (AF F) σ J → (HFin (AF F) σ J : Subgroup (GL (Fin M) (AF F ⊗[F] E))) :=
      fun g => ⟨g.1.1, Subgroup.mem_subgroupOf.1 g.2⟩
    have hf : Function.Injective f := by
      intro x y h
      have h' : (f x).1 = (f y).1 := by rw [h]
      exact Subtype.ext (Subtype.ext h')
    exact hf.countable
  · obtain ⟨W, hW, hWp⟩ := GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero F
    have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
    let b := Module.finBasis F E
    let B := Algebra.TensorProduct.basis (AF F) b
    have hc : ∀ k, Continuous (B.coord k) := fun k => IsModuleTopology.continuous_of_linearMap _
    let m : HA (AF F) σ J → Matrix (Fin M) (Fin M) (AF F ⊗[F] E) :=
      fun h => ((HA.mat (AF F) σ J h : GL (Fin M) (AF F ⊗[F] E)) :
        Matrix (Fin M) (Fin M) (AF F ⊗[F] E))
    have hm : Continuous m := Units.continuous_val.comp continuous_subtype_val
    have hm1 : m 1 = 1 := rfl
    let e : HA (AF F) σ J → Fin M → Fin M → _ → AF F := fun h i j k =>
      B.coord k (m h i j) - B.coord k ((1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j)
    refine ⟨⋂ i, ⋂ j, ⋂ k, (fun h => e h i j k) ⁻¹' W,
      Filter.iInter_mem.2 fun i => Filter.iInter_mem.2 fun j => Filter.iInter_mem.2 fun k => ?_, ?_⟩
    · have hce : Continuous fun h => e h i j k :=
        ((hc k).comp (hm.matrix_elem i j)).sub continuous_const
      refine hce.continuousAt.preimage_mem_nhds ?_
      have : e 1 i j k = 0 := by
        show B.coord k (m 1 i j) - _ = 0
        rw [hm1, sub_self]
      rw [this]; exact hW
    · intro h hU hh
      obtain ⟨γ, -, hγ⟩ := Subgroup.mem_map.1 hh
      have hent : ∀ i j, m h i j = inclR (F := F) (AF F) ((γ : Matrix (Fin M) (Fin M) E) i j) := by
        intro i j
        show ((HA.mat (AF F) σ J h : GL (Fin M) (AF F ⊗[F] E)) :
          Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j = _
        rw [← hγ]
        rfl
      have hco : ∀ (x : E) k, B.coord k (inclR (F := F) (AF F) x) =
          algebraMap F (AF F) (b.repr x k) := by
        intro x k
        show B.repr ((1 : AF F) ⊗ₜ[F] x) k = _
        rw [Algebra.TensorProduct.basis_repr_tmul]
        simp
      have hone : ∀ i j, (1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j =
          inclR (F := F) (AF F) ((1 : Matrix (Fin M) (Fin M) E) i j) := by
        intro i j
        by_cases hij : i = j
        · subst hij; simp
        · simp [Matrix.one_apply_ne hij]
      have hγ1 : (γ : Matrix (Fin M) (Fin M) E) = 1 := by
        ext i j
        refine b.repr.injective (Finsupp.ext fun k => ?_)
        have hk : e h i j k ∈ W := by
          have := Set.mem_iInter.1 (Set.mem_iInter.1 (Set.mem_iInter.1 hU i) j) k
          exact this
        have hk' : algebraMap F (AF F)
            (b.repr ((γ : Matrix (Fin M) (Fin M) E) i j) k -
              b.repr ((1 : Matrix (Fin M) (Fin M) E) i j) k) ∈ W := by
          rw [map_sub, ← hco, ← hco, ← hent, ← hone]
          exact hk
        exact sub_eq_zero.1 (hWp _ hk')
      have hγ2 : γ = 1 := Units.ext hγ1
      have hfin : HA.mat (AF F) σ J h = 1 := by
        rw [← hγ, hγ2, map_one]
      exact Subtype.ext hfin

end GlobalTheory.CompanionTheory.SW
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ArithmeticUnitaryGroupDiscreteStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithmetic_unitary_group_discrete : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → Countable (HFinIn (AF F) σ J) ∧ ∃ U ∈ 𝓝 (1 : HA (AF F) σ J), ∀ h ∈ U, HA.mat (AF F) σ J h ∈ HFin (AF F) σ J → h = 1 := by
  first | exact @GlobalTheory.CompanionTheory.SW.rational_countable_discrete | exact GlobalTheory.CompanionTheory.SW.rational_countable_discrete | (intros; apply GlobalTheory.CompanionTheory.SW.rational_countable_discrete <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LatticeStableAlmostEverywhere
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LatticeStableAlmostEverywhere
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.LatRat

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem eventually_integral (x : F) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      algebraMap F (Fv F v) x ∈ v.adicCompletionIntegers F := by
  have h := HeightOneSpectrum.Support.finite (𝓞 F) x
  filter_upwards [h.compl_mem_cofinite] with v hv
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have h2 : Valued.v (algebraMap F (Fv F v) x) = v.valuation F x :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x
  rw [h2]
  exact not_lt.mp hv

def latR {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) : Set (Fv F v ⊗[F] E) :=
  {y | ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈ v.adicCompletionIntegers F}

def Good {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (e : E) : Prop :=
  ∀ k l, algebraMap F (Fv F v) (b.repr (b k * e) l) ∈ v.adicCompletionIntegers F

theorem repr_mul {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (e : E)
    (y : Fv F v ⊗[F] E) (l : Fin d) :
    (Algebra.TensorProduct.basis (Fv F v) b).repr (y * inclR (Fv F v) e) l =
      ∑ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k *
        algebraMap F (Fv F v) (b.repr (b k * e) l) := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis (Fv F v) b).sum_repr y]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.sum_mul, map_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_mul_assoc, map_smul, Finsupp.smul_apply, smul_eq_mul]
  congr 1
  simp [inclR, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.tmul_mul_tmul,
    Algebra.TensorProduct.basis_repr_tmul]

theorem mul_mem_latR {d : ℕ} {b : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)} {e : E}
    (he : Good b v e) {y : Fv F v ⊗[F] E} (hy : y ∈ latR b v) : y * inclR (Fv F v) e ∈ latR b v := by
  intro l
  rw [repr_mul]
  exact sum_mem fun k _ => mul_mem (hy k) (he k l)

theorem sum_mem_latR {d : ℕ} {b : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)} {ι : Type}
    (s : Finset ι) (f : ι → Fv F v ⊗[F] E) (h : ∀ c ∈ s, f c ∈ latR b v) : ∑ c ∈ s, f c ∈ latR b v := by
  intro k
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finsupp.finsetSum_apply]
  exact sum_mem fun c hc => h c hc k

theorem eventually_good {d : ℕ} (b : Module.Basis (Fin d) F E) (e : E) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, Good b v e :=
  Filter.eventually_all.2 fun _ => Filter.eventually_all.2 fun _ => eventually_integral _

theorem eventually_good_matrix {d m : ℕ} (b : Module.Basis (Fin d) F E) (g : Matrix (Fin m) (Fin m) E) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ i j, Good b v (g i j) :=
  Filter.eventually_all.2 fun _ => Filter.eventually_all.2 fun _ => eventually_good b _

omit [NumberField F] in
theorem rmul_rmul (R : Type) [CommRing R] [Algebra F R] {M n : ℕ} (X : Fin n → Fin M → R ⊗[F] E)
    (A B : Matrix (Fin n) (Fin n) (R ⊗[F] E)) : rmul R (rmul R X A) B = rmul R X (A * B) := by
  funext a i
  simp only [rmul, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

omit [NumberField F] in
theorem rmul_one (R : Type) [CommRing R] [Algebra F R] {M n : ℕ} (X : Fin n → Fin M → R ⊗[F] E) :
    rmul R X 1 = X := by
  funext a i
  simp [rmul, Matrix.one_apply]

theorem rmul_mem {d M n : ℕ} {b : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)}
    {g : Matrix (Fin n) (Fin n) E} (hg : ∀ i j, Good b v (g i j))
    {X : Fin n → Fin M → Fv F v ⊗[F] E} (hX : X ∈ latV b v) :
    rmul (Fv F v) X (g.map (inclR (Fv F v))) ∈ latV b v := by
  intro a i
  exact sum_mem_latR _ _ (fun c _ => mul_mem_latR (hg c a) (fun k => hX c i k))

theorem actTup_mem {d M n : ℕ} {b : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)}
    {g : GL (Fin M) E} (hg : ∀ i j, Good b v ((g : Matrix (Fin M) (Fin M) E) i j))
    {X : Fin n → Fin M → Fv F v ⊗[F] E} (hX : X ∈ latV b v) :
    actTup (Fv F v) (bc (inclR (Fv F v)) g) X ∈ latV b v := by
  intro a i
  have h : actTup (Fv F v) (bc (inclR (Fv F v)) g) X a i =
      ∑ j, X a j * inclR (Fv F v) ((g : Matrix (Fin M) (Fin M) E) i j) := by
    simp only [actTup, Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [h]
  exact sum_mem_latR _ _ (fun j _ => mul_mem_latR (hg i j) (fun k => hX a j k))

omit [NumberField F] in
theorem actTup_inv {M n : ℕ} (R : Type) [CommRing R] [Algebra F R] (g : GL (Fin M) E)
    (X : Fin n → Fin M → R ⊗[F] E) :
    actTup R (bc (inclR R) g⁻¹) (actTup R (bc (inclR R) g) X) = X := by
  funext a
  simp only [actTup, Matrix.mulVec_mulVec]
  rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mulVec]

theorem one_mem_latR {d : ℕ} {b : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)}
    (h : ∀ k, algebraMap F (Fv F v) (b.repr 1 k) ∈ v.adicCompletionIntegers F) :
    (1 : Fv F v ⊗[F] E) ∈ latR b v := by
  intro k
  rw [Algebra.TensorProduct.one_def, Algebra.TensorProduct.basis_repr_tmul]
  simpa using h k

theorem consTup_mem_iff {d M n : ℕ} {b : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)}
    (h : ∀ k, algebraMap F (Fv F v) (b.repr 1 k) ∈ v.adicCompletionIntegers F)
    (X : Fin n → Fin M → Fv F v ⊗[F] E) : consTup X ∈ latV b v ↔ X ∈ latV b v := by
  constructor
  · intro hX a i k
    simpa [consTup] using hX a.succ i.succ k
  · intro hX a
    refine Fin.cases ?_ (fun a => ?_) a
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · intro k
        simpa [consTup] using one_mem_latR h k
      · simp [consTup]
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · simp [consTup]
      · simpa [consTup] using hX a i

theorem latV_rational : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ), (∀ g : Matrix (Fin n) (Fin n) E, g.det ≠ 0 → ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ X : (Fin n → Fin M → Fv F v ⊗[F] E), rmul (Fv F v) X (g.map (inclR (Fv F v))) ∈ latV b v ↔ X ∈ latV b v) ∧ (∀ g : GL (Fin M) E, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ X : (Fin n → Fin M → Fv F v ⊗[F] E), actTup (Fv F v) (bc (inclR (Fv F v)) g) X ∈ latV b v ↔ X ∈ latV b v) ∧ ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ X : (Fin n → Fin M → Fv F v ⊗[F] E), consTup X ∈ latV b v ↔ X ∈ latV b v := by
  intro F E _ _ _ _ _ σ _ d b n M
  refine ⟨fun g hg => ?_, fun g => ?_, ?_⟩
  · filter_upwards [eventually_good_matrix b g, eventually_good_matrix b g⁻¹] with v h1 h2 X
    refine ⟨fun hX => ?_, rmul_mem h1⟩
    have hmul : g.map (inclR (F := F) (E := E) (Fv F v)) * g⁻¹.map (inclR (F := F) (E := E) (Fv F v)) = 1 := by
      rw [← Matrix.map_mul, Matrix.mul_nonsing_inv g (isUnit_iff_ne_zero.2 hg),
        Matrix.map_one _ (map_zero _) (map_one _)]
    have := rmul_mem h2 hX
    rwa [rmul_rmul, hmul, rmul_one] at this
  · filter_upwards [eventually_good_matrix b (g : Matrix (Fin M) (Fin M) E),
      eventually_good_matrix b ((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E)] with v h1 h2 X
    refine ⟨fun hX => ?_, actTup_mem h1⟩
    have := actTup_mem (g := g⁻¹) h2 hX
    rwa [actTup_inv] at this
  · have h0 : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ k,
        algebraMap F (Fv F v) (b.repr 1 k) ∈ v.adicCompletionIntegers F :=
      Filter.eventually_all.2 fun k => eventually_integral (b.repr (1 : E) k)
    filter_upwards [h0] with v h X
    exact consTup_mem_iff h X

end GlobalTheory.CompanionTheory.SW.LatRat
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LatticeStableAlmostEverywhereStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_stable_almost_everywhere : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ), (∀ g : Matrix (Fin n) (Fin n) E, g.det ≠ 0 → ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ X : (Fin n → Fin M → Fv F v ⊗[F] E), rmul (Fv F v) X (g.map (inclR (Fv F v))) ∈ latV b v ↔ X ∈ latV b v) ∧ (∀ g : GL (Fin M) E, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ X : (Fin n → Fin M → Fv F v ⊗[F] E), actTup (Fv F v) (bc (inclR (Fv F v)) g) X ∈ latV b v ↔ X ∈ latV b v) ∧ ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ X : (Fin n → Fin M → Fv F v ⊗[F] E), consTup X ∈ latV b v ↔ X ∈ latV b v := by
  first | exact @GlobalTheory.CompanionTheory.SW.LatRat.latV_rational | exact GlobalTheory.CompanionTheory.SW.LatRat.latV_rational | (intros; apply GlobalTheory.CompanionTheory.SW.LatRat.latV_rational <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsTraceFormGramMatrixInBasis
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsTraceFormGramMatrixInBasis
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.TraceCoord

section Abstract

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {d M : ℕ}

def coord (β : Module.Basis (Fin d) R A) (x : Fin M → A) : Fin M × Fin d → R :=
  fun p => β.repr (x p.1) p.2

def gramB (s : A →+* A) (β : Module.Basis (Fin d) R A) (J : Matrix (Fin M) (Fin M) A) :
    Matrix (Fin M × Fin d) (Fin M × Fin d) R :=
  fun p q => Algebra.trace R A (s (β p.2) * J p.1 q.1 * β q.2)

theorem trace_hform (s : A →+* A) (hs : ∀ (r : R) (a : A), s (r • a) = r • s a)
    (β : Module.Basis (Fin d) R A) (J : Matrix (Fin M) (Fin M) A) (x y : Fin M → A) :
    Algebra.trace R A (hform s J x y) = coord β x ⬝ᵥ (gramB s β J *ᵥ coord β y) := by
  have hx : ∀ i, s (x i) = ∑ k, β.repr (x i) k • s (β k) := by
    intro i
    calc s (x i) = s (∑ k, β.repr (x i) k • β k) := by rw [β.sum_repr]
      _ = ∑ k, β.repr (x i) k • s (β k) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        exact Finset.sum_congr rfl fun k _ => hs _ _
  have hy : ∀ j, y j = ∑ l, β.repr (y j) l • β l := fun j => (β.sum_repr (y j)).symm
  have term : ∀ i j, Algebra.trace R A (s (x i) * J i j * y j) =
      ∑ k, ∑ l, β.repr (x i) k *
        (Algebra.trace R A (s (β k) * J i j * β l) * β.repr (y j) l) := by
    intro i j
    rw [hx i]
    conv_lhs => rw [hy j]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_mul, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_mul_assoc, smul_mul_assoc, mul_smul_comm, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    ring
  unfold hform coord gramB dotProduct Matrix.mulVec dotProduct
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, term, Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Finset.sum_comm

theorem coord_mulVec (β : Module.Basis (Fin d) R A) (H : Matrix (Fin M) (Fin M) A)
    (g : Matrix (Fin M × Fin d) (Fin M × Fin d) R)
    (hg : ∀ p q, g p q = β.repr (H p.1 q.1 * β q.2) p.2) (x : Fin M → A) :
    coord β (H *ᵥ x) = g *ᵥ coord β x := by
  funext p
  have hterm : ∀ j, H p.1 j * x j = ∑ l, β.repr (x j) l • (H p.1 j * β l) := by
    intro j
    conv_lhs => rw [← β.sum_repr (x j)]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => mul_smul_comm _ _ _
  simp only [coord, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, hg]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hterm, map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.smul_apply, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, mul_comm]

theorem coord_surj (β : Module.Basis (Fin d) R A) (u : Fin M × Fin d → R) :
    ∃ x : Fin M → A, coord β x = u := by
  refine ⟨fun i => ∑ k, u (i, k) • β k, ?_⟩
  funext p
  change β.repr (∑ k, u (p.1, k) • β k) p.2 = u p
  rw [Module.Basis.repr_sum_self]

theorem hform_eq (s : A →+* A) (J : Matrix (Fin M) (Fin M) A) (x y : Fin M → A) :
    hform s J x y = (s ∘ x) ⬝ᵥ (J *ᵥ y) := by
  simp only [hform, dotProduct, Matrix.mulVec, Function.comp, Finset.mul_sum, mul_assoc]

theorem dot_mulVec_left {n : Type} [Fintype n] (P : Matrix n n R) (u w : n → R) :
    (P *ᵥ u) ⬝ᵥ w = u ⬝ᵥ (Pᵀ *ᵥ w) := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem hform_mulVec (s : A →+* A) (J H : Matrix (Fin M) (Fin M) A)
    (hH : cT s H * J * H = J) (x y : Fin M → A) :
    hform s J (H *ᵥ x) (H *ᵥ y) = hform s J x y := by
  have h1 : s ∘ (H *ᵥ x) = (H.map s) *ᵥ (s ∘ x) := by
    funext i
    exact RingHom.map_mulVec s H x i
  have h2 : (H.map s)ᵀ * J * H = J := hH
  rw [hform_eq, hform_eq, h1, dot_mulVec_left, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h2]

theorem mat_ext {n : Type} [Fintype n] [DecidableEq n] (P Q : Matrix n n R)
    (h : ∀ u v : n → R, u ⬝ᵥ (P *ᵥ v) = u ⬝ᵥ (Q *ᵥ v)) : P = Q := by
  ext p q
  simpa using h (Pi.single p 1) (Pi.single q 1)

end Abstract

section Concrete

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem sigR_smul (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (r : R) (a : R ⊗[F] E) :
    sigR R σ (r • a) = r • sigR R σ a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [sigR, TensorProduct.smul_tmul']
  | add a c ha hc => simp only [smul_add, map_add (f := _), ha, hc]

theorem trace_one_tmul (R : Type) [CommRing R] [Algebra F R] [Module.Finite F E] (e : E) :
    Algebra.trace R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] e) = algebraMap F R (Algebra.trace F E e) := by
  have h : Algebra.lmul R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] e) =
      LinearMap.baseChange R (Algebra.lmul F E e) := by
    ext y
    simp
  rw [Algebra.trace_apply, Algebra.trace_apply, h]
  exact LinearMap.trace_baseChange _ _

theorem gramB_tensor (R : Type) [CommRing R] [Algebra F R] [Module.Finite F E] {d M : ℕ}
    (σ : E →ₐ[F] E) (b : Module.Basis (Fin d) F E) (J : Matrix (Fin M) (Fin M) E) :
    gramB (sigR R σ) (Algebra.TensorProduct.basis R b) (JR R J) =
      (gramB (σ : E →+* E) b J).map (algebraMap F R) := by
  ext p q
  have h : sigR R σ ((1 : R) ⊗ₜ[F] b p.2) * inclR R (J p.1 q.1) * ((1 : R) ⊗ₜ[F] b q.2) =
      (1 : R) ⊗ₜ[F] (σ (b p.2) * J p.1 q.1 * b q.2) := by
    simp [sigR, inclR]
  simp only [gramB, Matrix.map_apply, Algebra.TensorProduct.basis_apply, JR]
  rw [h, trace_one_tmul]
  rfl

end Concrete

section Number

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sig_smul (σ : E →ₐ[F] E) (r : F) (a : E) :
    (σ : E →+* E) (r • a) = r • (σ : E →+* E) a := by
  simp only [Algebra.smul_def]
  rw [map_mul]
  congr 1
  exact σ.commutes r

theorem sig_sig (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [hσ.2.2.2, hσ.2.2.2, star_star]

theorem gramB_symm (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) {M d : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (b : Module.Basis (Fin d) F E) :
    (gramB (σ : E →+* E) b J).IsSymm := by
  haveI : Module.Finite F E := Module.Finite.of_basis b
  ext p q
  let e : E ≃ₐ[F] E := AlgEquiv.ofBijective σ (Algebra.IsAlgebraic.algHom_bijective σ)
  change Algebra.trace F E (σ (b q.2) * J q.1 p.1 * b p.2) =
    Algebra.trace F E (σ (b p.2) * J p.1 q.1 * b q.2)
  rw [← Algebra.trace_eq_of_algEquiv e (σ (b q.2) * J q.1 p.1 * b p.2)]
  congr 1
  change σ (σ (b q.2) * J q.1 p.1 * b p.2) = _
  rw [map_mul, map_mul, sig_sig σ hσ, hJ.1 p.1 q.1]
  ring

theorem gramB_det (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) {M d : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (b : Module.Basis (Fin d) F E) :
    (gramB (σ : E →+* E) b J).det ≠ 0 := by
  haveI : Module.Finite F E := Module.Finite.of_basis b
  intro h0
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  obtain ⟨y, rfl⟩ := coord_surj (M := M) b v
  have hz : J *ᵥ y = 0 := by
    funext i
    refine (traceForm_nondegenerate F E).1 _ fun a => ?_
    have h1 := trace_hform (σ : E →+* E) (sig_smul σ) b J (Pi.single i (σ a)) y
    rw [hv, dotProduct_zero, hform_eq] at h1
    have h2 : ((σ : E →+* E) ∘ (Pi.single i (σ a) : Fin M → E)) ⬝ᵥ (J *ᵥ y) = a * (J *ᵥ y) i := by
      have h3 : ((σ : E →+* E) ∘ (Pi.single i (σ a) : Fin M → E)) = Pi.single i a := by
        funext j
        by_cases hj : j = i
        · subst hj
          simp [sig_sig σ hσ]
        · simp [Pi.single_eq_of_ne hj]
      rw [h3, single_dotProduct]
    rw [h2] at h1
    rw [Algebra.traceForm_apply, mul_comm]
    exact h1
  have hy : y = 0 := Matrix.eq_zero_of_mulVec_eq_zero hJ.2 hz
  apply hv0
  funext p
  simp [hy, coord]

end Number

theorem exists_trace_coord : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∃ B : Matrix (Fin M × Fin d) (Fin M × Fin d) F, B.IsSymm ∧ B.det ≠ 0 ∧ (∀ x : Fin M → E, Algebra.trace F E (hE σ J x x) = (fun p : Fin M × Fin d => b.repr (x p.1) p.2) ⬝ᵥ (B *ᵥ fun p : Fin M × Fin d => b.repr (x p.1) p.2)) ∧ ∀ (R : Type) [CommRing R] [Algebra F R], (∀ x y : Fin M → R ⊗[F] E, Algebra.trace R (R ⊗[F] E) (hR R σ J x y) = (fun p : Fin M × Fin d => (Algebra.TensorProduct.basis R b).repr (x p.1) p.2) ⬝ᵥ (B.map (algebraMap F R) *ᵥ fun p : Fin M × Fin d => (Algebra.TensorProduct.basis R b).repr (y p.1) p.2)) ∧ ∀ h : HA R σ J, ∀ g : Matrix (Fin M × Fin d) (Fin M × Fin d) R, (∀ p q, g p q = (Algebra.TensorProduct.basis R b).repr ((HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) p.1 q.1 * inclR R (b q.2)) p.2) → gᵀ * B.map (algebraMap F R) * g = B.map (algebraMap F R) ∧ ∀ x : Fin M → R ⊗[F] E, (fun p : Fin M × Fin d => (Algebra.TensorProduct.basis R b).repr (((HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ x) p.1) p.2) = g *ᵥ fun p : Fin M × Fin d => (Algebra.TensorProduct.basis R b).repr (x p.1) p.2 := by
  intro F E _ _ _ _ _ σ hσ M J hJ d b
  haveI : Module.Finite F E := Module.Finite.of_basis b
  refine ⟨gramB (σ : E →+* E) b J, gramB_symm σ hσ J hJ b, gramB_det σ hσ J hJ b, fun x => ?_,
    fun R _ _ => ?_⟩
  · exact trace_hform (σ : E →+* E) (sig_smul σ) b J x x
  · have key : ∀ x y : Fin M → R ⊗[F] E, Algebra.trace R (R ⊗[F] E) (hR R σ J x y) =
        coord (Algebra.TensorProduct.basis R b) x ⬝ᵥ
          ((gramB (σ : E →+* E) b J).map (algebraMap F R) *ᵥ
            coord (Algebra.TensorProduct.basis R b) y) := fun x y => by
      rw [← gramB_tensor]
      exact trace_hform (sigR R σ) (sigR_smul R σ) _ (JR R J) x y
    refine ⟨key, fun h g hg => ?_⟩
    have hact := coord_mulVec (Algebra.TensorProduct.basis R b)
      (HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) g (fun p q => by
        rw [hg, Algebra.TensorProduct.basis_apply]
        rfl)
    refine ⟨?_, hact⟩
    have hU : cT (sigR R σ) (HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J *
        (HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) = JR R J :=
      (show HR R σ J from h).2
    apply mat_ext
    intro u v
    obtain ⟨x, rfl⟩ := coord_surj (M := M) (Algebra.TensorProduct.basis R b) u
    obtain ⟨y, rfl⟩ := coord_surj (M := M) (Algebra.TensorProduct.basis R b) v
    have h1 := key ((HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ x)
      ((HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ y)
    have h2 : hR R σ J ((HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ x)
        ((HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ y) = hR R σ J x y :=
      hform_mulVec _ _ _ hU x y
    rw [h2, key x y, hact x, hact y, dot_mulVec_left, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec] at h1
    exact h1.symm

end GlobalTheory.CompanionTheory.SW.TraceCoord
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsTraceFormGramMatrixInBasisStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_trace_form_gram_matrix_in_basis : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∃ B : Matrix (Fin M × Fin d) (Fin M × Fin d) F, B.IsSymm ∧ B.det ≠ 0 ∧ (∀ x : Fin M → E, Algebra.trace F E (hE σ J x x) = (fun p : Fin M × Fin d => b.repr (x p.1) p.2) ⬝ᵥ (B *ᵥ fun p : Fin M × Fin d => b.repr (x p.1) p.2)) ∧ ∀ (R : Type) [CommRing R] [Algebra F R], (∀ x y : Fin M → R ⊗[F] E, Algebra.trace R (R ⊗[F] E) (hR R σ J x y) = (fun p : Fin M × Fin d => (Algebra.TensorProduct.basis R b).repr (x p.1) p.2) ⬝ᵥ (B.map (algebraMap F R) *ᵥ fun p : Fin M × Fin d => (Algebra.TensorProduct.basis R b).repr (y p.1) p.2)) ∧ ∀ h : HA R σ J, ∀ g : Matrix (Fin M × Fin d) (Fin M × Fin d) R, (∀ p q, g p q = (Algebra.TensorProduct.basis R b).repr ((HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) p.1 q.1 * inclR R (b q.2)) p.2) → gᵀ * B.map (algebraMap F R) * g = B.map (algebraMap F R) ∧ ∀ x : Fin M → R ⊗[F] E, (fun p : Fin M × Fin d => (Algebra.TensorProduct.basis R b).repr (((HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ x) p.1) p.2) = g *ᵥ fun p : Fin M × Fin d => (Algebra.TensorProduct.basis R b).repr (x p.1) p.2 := by
  first | exact @GlobalTheory.CompanionTheory.SW.TraceCoord.exists_trace_coord | exact GlobalTheory.CompanionTheory.SW.TraceCoord.exists_trace_coord | (intros; apply GlobalTheory.CompanionTheory.SW.TraceCoord.exists_trace_coord <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SummableOneDivAbsNormSq
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.Primes

theorem summable_one_div_absNorm_sq :
    ∀ (F : Type) [Field F] [NumberField F],
      Summable fun v : HeightOneSpectrum (𝓞 F) => 1 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2 := by
  intro F _ _
  have h := (ReciprocityTheory.Cheb.summable_absNorm_rpow_ideal F (s := 2) (by norm_num)).comp_injective
    (i := fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal) (fun _ _ h => HeightOneSpectrum.ext h)
  refine h.congr fun v => ?_
  simp only [Function.comp_apply]
  rw [Real.rpow_neg (Nat.cast_nonneg _), one_div]
  norm_num

end GlobalTheory.CompanionTheory.SW.Primes
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresScaling
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresScaling
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.Rescale

theorem isGramFib_rescale : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ), ∀ (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)) (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFib R σ J n μ ν m → ∀ a c : ℝ≥0, a ≠ 0 → c ≠ 0 → IsGramFib R σ J n (a • μ) (c • ν) (fun S => (a / c) • m S) := by
  intro F E _ _ _ _ _ σ _ M J _ R _ _ _ _ _ _ n μ ν m _ _ h a c _ hc
  exact isFibreFamily_rescale _ _ _ μ ν _ _ _ _ m h a c hc

end GlobalTheory.CompanionTheory.SW.Rescale
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresScalingStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_fiber_measures_scaling : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ), ∀ (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)) (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFib R σ J n μ ν m → ∀ a c : ℝ≥0, a ≠ 0 → c ≠ 0 → IsGramFib R σ J n (a • μ) (c • ν) (fun S => (a / c) • m S) := by
  first | exact @GlobalTheory.CompanionTheory.SW.Rescale.isGramFib_rescale | exact GlobalTheory.CompanionTheory.SW.Rescale.isGramFib_rescale | (intros; apply GlobalTheory.CompanionTheory.SW.Rescale.isGramFib_rescale <;> assumption)
end
end
