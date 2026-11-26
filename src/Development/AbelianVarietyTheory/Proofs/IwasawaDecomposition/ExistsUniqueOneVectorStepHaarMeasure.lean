module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdHermitianFibreMeasureInvariantOrbitFiniteNonz
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueStdHermitianFibreProductOfRankGeThre

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilFormulaHaarOrbitStabilizer
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilFormulaHaarOrbitStabilizer
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal Pointwise

namespace GlobalTheory.GaugeWeil

theorem inner_eq {G X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] [MulAction G X] (x₀ : X)
    (μ' : Measure (MulAction.stabilizer G x₀)) [μ'.IsMulLeftInvariant] (f : G → ℝ≥0∞) (a b : G)
    (hab : a • x₀ = b • x₀) :
    ∫⁻ h, f (a * (h : G)) ∂μ' = ∫⁻ h, f (b * (h : G)) ∂μ' := by
  have hc : b⁻¹ * a ∈ MulAction.stabilizer G x₀ := by
    rw [MulAction.mem_stabilizer_iff, mul_smul, hab, inv_smul_smul]
  rw [← lintegral_mul_left_eq_self (μ := μ') (fun h => f (b * (h : G))) ⟨_, hc⟩]
  simp [← mul_assoc]

theorem weil_formula : ∀ (G X : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] [MulAction G X] [ContinuousSMul G X] (x₀ : X), ∀ (μ' : Measure (MulAction.stabilizer G x₀)) (ν : Measure X), μ'.IsHaarMeasure → IsFiniteMeasureOnCompacts ν → ν ≠ 0 → (∀ g : G, ν.map (fun y => g • y) = ν) → ν {y | ¬ ∃ g : G, g • x₀ = y} = 0 → ∃ μ : Measure G, μ.IsHaarMeasure ∧ ∀ f : G → ℝ≥0∞, Measurable f → ∀ s : X → G, (∀ y, (∃ g : G, g • x₀ = y) → s y • x₀ = y) → ∫⁻ g, f g ∂μ = ∫⁻ y, ∫⁻ h, f (s y * (h : G)) ∂μ' ∂ν := by
  intro G X _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x₀ μ' ν hμ' hνc hν0 hinv hnull
  obtain ⟨-, s₀, hs₀m, hs₀⟩ := GlobalTheory.OrbitSection.measurableSet_orbit_and_exists_section G X x₀
  have hcont : Continuous fun g : G => g • x₀ := continuous_id.smul continuous_const
  have hclosed : IsClosed ((MulAction.stabilizer G x₀ : Subgroup G) : Set G) :=
    isClosed_eq hcont continuous_const
  have hemb : IsClosedEmbedding (Subtype.val : MulAction.stabilizer G x₀ → G) :=
    hclosed.isClosedEmbedding_subtypeVal
  have : LocallyCompactSpace (MulAction.stabilizer G x₀) := hemb.locallyCompactSpace
  have : SecondCountableTopology (MulAction.stabilizer G x₀) :=
    hemb.isEmbedding.secondCountableTopology
  have : SigmaCompactSpace (MulAction.stabilizer G x₀) := inferInstance
  have : IsLocallyFiniteMeasure μ' := inferInstance
  have : SigmaFinite μ' := inferInstance
  have hae : ∀ᵐ y ∂ν, ∃ g : G, g • x₀ = y := hnull
  have hΦ : Measurable fun p : X × MulAction.stabilizer G x₀ => s₀ p.1 * (p.2 : G) :=
    (hs₀m.comp measurable_fst).mul (measurable_subtype_coe.comp measurable_snd)
  set μ : Measure G := (ν.prod μ').map
    (fun p : X × MulAction.stabilizer G x₀ => s₀ p.1 * (p.2 : G)) with hμ
  have key0 : ∀ f : G → ℝ≥0∞, Measurable f →
      ∫⁻ g, f g ∂μ = ∫⁻ y, ∫⁻ h, f (s₀ y * (h : G)) ∂μ' ∂ν := by
    intro f hf
    rw [hμ, lintegral_map hf hΦ]
    exact lintegral_prod _ (hf.comp hΦ).aemeasurable
  have hleft : μ.IsMulLeftInvariant := by
    refine ⟨fun g => Measure.ext_of_lintegral _ fun f hf => ?_⟩
    have hF : Measurable fun y => ∫⁻ h, f (s₀ y * (h : G)) ∂μ' :=
      (hf.comp hΦ).lintegral_prod_right'
    rw [lintegral_map hf (measurable_const_mul g), key0 (fun a => f (g * a)) (hf.comp (measurable_const_mul g)),
      key0 f hf]
    conv_rhs => rw [← hinv g, lintegral_map hF (continuous_const_smul g).measurable]
    refine lintegral_congr_ae (hae.mono fun y hy => ?_)
    have h2 : ∃ k : G, k • x₀ = g • y := by
      obtain ⟨k, rfl⟩ := hy
      exact ⟨g * k, mul_smul _ _ _⟩
    have := inner_eq x₀ μ' f (g * s₀ y) (s₀ (g • y)) (by rw [mul_smul, hs₀ y hy, hs₀ _ h2])
    simpa [mul_assoc] using this
  have hfin : IsFiniteMeasureOnCompacts μ := by
    refine ⟨fun K hK => ?_⟩
    have hKm : MeasurableSet K := hK.measurableSet
    have hL : IsCompact ((fun g : G => g • x₀) '' K) := hK.image hcont
    have hM : IsCompact ((Subtype.val : MulAction.stabilizer G x₀ → G) ⁻¹' (K⁻¹ * K)) :=
      hemb.isCompact_preimage (hK.inv.mul hK)
    rw [← lintegral_indicator_one hKm, key0 _ (measurable_one.indicator hKm)]
    calc _ ≤ ∫⁻ y, ((fun g : G => g • x₀) '' K).indicator
            (fun _ => μ' ((Subtype.val : MulAction.stabilizer G x₀ → G) ⁻¹' (K⁻¹ * K))) y ∂ν := by
          refine lintegral_mono_ae (hae.mono fun y hy => ?_)
          by_cases hyK : y ∈ (fun g : G => g • x₀) '' K
          · rw [Set.indicator_of_mem hyK]
            obtain ⟨k, hk, hky⟩ := hyK
            rw [inner_eq x₀ μ' _ (s₀ y) k (by rw [hs₀ y hy]; exact hky.symm),
              ← lintegral_indicator_one hM.measurableSet]
            refine lintegral_mono fun h => ?_
            by_cases hh : k * (h : G) ∈ K
            · have : h ∈ (Subtype.val : MulAction.stabilizer G x₀ → G) ⁻¹' (K⁻¹ * K) :=
                ⟨k⁻¹, by simpa using hk, k * h, hh, by simp⟩
              simp [Set.indicator_of_mem hh, Set.indicator_of_mem this]
            · simp [Set.indicator_of_notMem hh]
          · rw [Set.indicator_of_notMem hyK]
            have : ∀ h : MulAction.stabilizer G x₀, s₀ y * (h : G) ∉ K := fun h hh =>
              hyK ⟨_, hh, by
                have h1 : (h : G) • x₀ = x₀ := h.2
                simp only [mul_smul, h1, hs₀ y hy]⟩
            simp [Set.indicator_of_notMem (this _)]
      _ < ⊤ := by
          rw [lintegral_indicator_const hL.measurableSet]
          exact ENNReal.mul_lt_top hM.measure_lt_top hL.measure_lt_top
  have hne : μ Set.univ ≠ 0 := by
    rw [← lintegral_one, key0 _ measurable_const]
    simp only [lintegral_const, one_mul]
    exact mul_ne_zero (isOpen_univ.measure_ne_zero μ' Set.univ_nonempty)
      (by simpa using hν0)
  obtain ⟨n, hn⟩ : ∃ n, μ (compactCovering G n) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hne
    rw [← iUnion_compactCovering G]
    exact measure_iUnion_null hcon
  have hpos : μ.IsOpenPosMeasure :=
    isOpenPosMeasure_of_mulLeftInvariant_of_compact _ (isCompact_compactCovering G n) hn
  refine ⟨μ, ⟨⟩, fun f hf s hs => ?_⟩
  rw [key0 f hf]
  exact lintegral_congr_ae (hae.mono fun y hy =>
    inner_eq x₀ μ' f _ _ (by rw [hs y hy, hs₀ y hy]))

end GlobalTheory.GaugeWeil
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilFormulaHaarOrbitStabilizerStatement
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_formula_haar_orbit_stabilizer : ∀ (G X : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] [MulAction G X] [ContinuousSMul G X] (x₀ : X), ∀ (μ' : Measure (MulAction.stabilizer G x₀)) (ν : Measure X), μ'.IsHaarMeasure → IsFiniteMeasureOnCompacts ν → ν ≠ 0 → (∀ g : G, ν.map (fun y => g • y) = ν) → ν {y | ¬ ∃ g : G, g • x₀ = y} = 0 → ∃ μ : Measure G, μ.IsHaarMeasure ∧ ∀ f : G → ℝ≥0∞, Measurable f → ∀ s : X → G, (∀ y, (∃ g : G, g • x₀ = y) → s y • x₀ = y) → ∫⁻ g, f g ∂μ = ∫⁻ y, ∫⁻ h, f (s y * (h : G)) ∂μ' ∂ν := by
  first | exact @GlobalTheory.GaugeWeil.weil_formula | exact GlobalTheory.GaugeWeil.weil_formula | (intros; apply GlobalTheory.GaugeWeil.weil_formula <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueOneVectorStepHaarMeasure
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx

theorem exists_unique_stepRel : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (s : StdMeas b) (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (a : F) (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E) (μ' : Measure (HA (AF F) σ J')), 2 ≤ M → StepData σ J x a B J' → μ'.IsHaarMeasure → (∃ μ : Measure (HA (AF F) σ J), μ.IsHaarMeasure ∧ StepRel s σ J x a B J' μ μ') ∧ ∀ μ₁ μ₂ : Measure (HA (AF F) σ J), StepRel s σ J x a B J' μ₁ μ' → StepRel s σ J x a B J' μ₂ μ' → μ₁ = μ₂ := by
  intro F E _ _ _ _ _ σ hcm d b s M J x a B J' μ' hM hsd hμ'
  have : FiniteDimensional F E := Module.Finite.of_basis b
  obtain ⟨ν, hν, hνu⟩ := GlobalTheory.T.existsUnique_stdHermitianFibreProduct_of_rank_ge_three F E σ hcm d b s (M + 1) J a (by omega) hsd.1 hsd.2.1
  obtain ⟨-, ⟨e, he, heu⟩, hcont⟩ := GlobalTheory.T.unitary_stabilizer_anisotropic_vector_equiv_complement F E σ hcm (AF F) M J x a B J' hsd
  obtain ⟨-, hinv, horb, hfin, hne⟩ :=
    GlobalTheory.T.stdHermitianFibreMeasure_invariant_orbit_finite_nonzero F E σ hcm d b s (M + 1) J x a ν hsd.1 hsd.2.1 hsd.2.2.1 hν
  obtain ⟨hc1, hc2⟩ := hcont e he
  constructor
  · have : (μ'.map e.symm).IsHaarMeasure := MulEquiv.isHaarMeasure_map μ' e.symm hc2 hc1
    obtain ⟨μ, hμ, hint⟩ := GlobalTheory.T.weil_formula_haar_orbit_stabilizer (HA (AF F) σ J) (Fin 1 → Fin (M + 1) → AF F ⊗[F] E)
      (ratTup (F := F) (AF F) x) (μ'.map e.symm) ν this hfin hne hinv horb
    refine ⟨μ, hμ, fun ν' hν' e' he' => ?_⟩
    obtain rfl := hνu ν' hν'
    obtain rfl := heu e' he'
    exact hint
  · intro μ₁ μ₂ h₁ h₂
    have k₁ := h₁ ν hν e he
    have k₂ := h₂ ν hν e he
    classical
    let t : (Fin 1 → Fin (M + 1) → AF F ⊗[F] E) → HA (AF F) σ J := fun y =>
      if h : ∃ g : HA (AF F) σ J, g • ratTup (F := F) (AF F) x = y then h.choose else 1
    have ht : ∀ y, (∃ g : HA (AF F) σ J, g • ratTup (F := F) (AF F) x = y) →
        t y • ratTup (F := F) (AF F) x = y := fun y hy => by
      simp only [t, dif_pos hy]
      exact hy.choose_spec
    exact Measure.ext_of_lintegral _ fun f hf => (k₁ f hf t ht).trans (k₂ f hf t ht).symm

end GlobalTheory.GaugeEx
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueOneVectorStepHaarMeasureStatement
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unique_oneVectorStep_haarMeasure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (s : StdMeas b) (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (a : F) (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E) (μ' : Measure (HA (AF F) σ J')), 2 ≤ M → StepData σ J x a B J' → μ'.IsHaarMeasure → (∃ μ : Measure (HA (AF F) σ J), μ.IsHaarMeasure ∧ StepRel s σ J x a B J' μ μ') ∧ ∀ μ₁ μ₂ : Measure (HA (AF F) σ J), StepRel s σ J x a B J' μ₁ μ' → StepRel s σ J x a B J' μ₂ μ' → μ₁ = μ₂ := by
  first | exact @GlobalTheory.GaugeEx.exists_unique_stepRel | exact GlobalTheory.GaugeEx.exists_unique_stepRel | (intros; apply GlobalTheory.GaugeEx.exists_unique_stepRel <;> assumption)
end
