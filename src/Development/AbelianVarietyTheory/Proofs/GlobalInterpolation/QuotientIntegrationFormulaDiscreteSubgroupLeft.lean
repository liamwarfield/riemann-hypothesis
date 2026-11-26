module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RationalVectorsAdelesFundamentalDomainMassOne
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsSummableMajorantRationalVectorsLocallyUnif
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryStabilizerAnisotropicVectorEquivComplemen
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankOrth
public import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.JetMomTA
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VacuumEntireAndNormalizedJetsAlgebraic
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralWeierstrassChartXyUnitSeries

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuotientIntegrationFormulaDiscreteSubgroupLeft
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuotientIntegrationFormulaDiscreteSubgroupLeft
open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal

namespace GlobalTheory.QuotDiscrete

theorem _root_.GlobalTheory.QuotDiscrete.isInvInvariant_of_isMulRightInvariant {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [μ.IsHaarMeasure] [μ.IsMulRightInvariant] : μ.IsInvInvariant := by
  have h1 : μ.inv = Measure.haarScalarFactor μ.inv μ • μ :=
    Measure.isMulLeftInvariant_eq_smul μ.inv μ
  set c := Measure.haarScalarFactor μ.inv μ with hc
  have h2 : μ = (c * c) • μ := by
    calc μ = μ.inv.inv := (Measure.inv_inv μ).symm
      _ = (c • μ).inv := by rw [← h1]
      _ = c • μ.inv := by
          ext s _
          simp [Measure.inv_apply]
      _ = (c * c) • μ := by rw [h1, smul_smul]
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : G)
  have hpos : 0 < μ K := Measure.measure_pos_of_mem_nhds μ hK1
  have hfin : μ K < ∞ := hK.measure_lt_top
  have h3 : ((c * c : NNReal) : ℝ≥0∞) * μ K = 1 * μ K := by
    rw [one_mul]
    conv_rhs => rw [h2]
    rfl
  have h4 : ((c * c : NNReal) : ℝ≥0∞) = 1 :=
    (ENNReal.mul_left_inj hpos.ne' hfin.ne).1 h3
  have h5 : ((c : ℝ) * c) = 1 := by exact_mod_cast h4
  have h6 : c = 1 := by
    have hc0 : (0 : ℝ) ≤ c := c.2
    have : (c : ℝ) = 1 := by nlinarith
    exact_mod_cast this
  exact ⟨by rw [h1, h6, one_smul]⟩

theorem _root_.GlobalTheory.QuotDiscrete.existsUnique_subgroupOf {G : Type} [Group G] {Γ H : Subgroup G} (hΓ : Γ ≤ H) {F : Set G}
    (hF : ∀ x : G, ∃! γ : Γ, γ • x ∈ F) (g : G) (h : H) :
    ∃! γ : Γ.subgroupOf H, γ • h ∈ {h : H | (h : G) * g ∈ F} := by
  obtain ⟨γ, hγ, huniq⟩ := hF (h * g)
  refine ⟨⟨⟨γ, hΓ γ.2⟩, Subgroup.mem_subgroupOf.2 γ.2⟩, ?_, ?_⟩
  · simp only [Set.mem_setOf_eq, Subgroup.smul_def, smul_eq_mul, Subgroup.coe_mul] at hγ ⊢
    simpa [mul_assoc] using hγ
  · intro δ hδ
    have hδ' : (⟨((δ : H) : G), Subgroup.mem_subgroupOf.1 δ.2⟩ : Γ) • ((h : G) * g) ∈ F := by
      simp only [Set.mem_setOf_eq, Subgroup.smul_def, smul_eq_mul, Subgroup.coe_mul] at hδ ⊢
      simpa [mul_assoc] using hδ
    have := huniq _ hδ'
    have h2 : ((δ : H) : G) = (γ : G) := congrArg Subtype.val this
    exact Subtype.ext (Subtype.ext h2)

theorem _root_.GlobalTheory.QuotDiscrete.discreteClause : _root_.GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.DiscreteClause := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.DiscreteClause
  intro G _ _ _ _ _ _ _ _ H _ _ _ _ hH hG hHu dg _ ν _ μ hμ hQ Γ hΓ hd
  haveI : Countable Γ := (TopologicalSpace.separableSpace_iff_countable).1 inferInstance
  haveI : Countable (Γ.subgroupOf H) :=
    Countable.of_equiv _ (Subgroup.subgroupOfEquivOfLe hΓ).toEquiv.symm
  haveI : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology H := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : ν.IsMulRightInvariant := hHu ν inferInstance
  haveI : ν.IsInvInvariant := _root_.GlobalTheory.QuotDiscrete.isInvInvariant_of_isMulRightInvariant ν
  haveI : dg.IsMulRightInvariant := hG dg inferInstance
  haveI : dg.IsInvInvariant := _root_.GlobalTheory.QuotDiscrete.isInvInvariant_of_isMulRightInvariant dg
  obtain ⟨F, hFm, hF⟩ := _root_.GlobalTheory.FundDomDiscrete.exists_measurable_section Γ
  have hFg : ∀ g : G, MeasurableSet {h : H | (h : G) * g ∈ F} := fun g =>
    hFm.preimage (measurable_subtype_coe.mul_const g)
  have hFD : IsFundamentalDomain Γ F dg := IsFundamentalDomain.mk' hFm.nullMeasurableSet hF
  have hFD' : ∀ g : G, IsFundamentalDomain (Γ.subgroupOf H) {h : H | (h : G) * g ∈ F} ν :=
    fun g => IsFundamentalDomain.mk' (hFg g).nullMeasurableSet
      (_root_.GlobalTheory.QuotDiscrete.existsUnique_subgroupOf hΓ hF g)
  refine ⟨⟨F, hFm, hFD⟩, ⟨_, hFg 1, hFD' 1⟩, ?_⟩
  intro D D' hD hD' f hf hinv
  have hFi : Measurable (F.indicator f) := hf.indicator hFm
  have hK : Measurable (fun x : G => F.indicator f x⁻¹) := hFi.comp measurable_inv
  obtain ⟨hcm, hcint⟩ := hQ _ hK
  have he : Continuous (QuotientGroup.quotientRightRelEquivQuotientLeftRel H) := by
    refine (Topology.IsQuotientMap.continuous_iff isQuotientMap_quotient_mk').2 ?_
    have hc : Continuous fun g : G => ((g⁻¹ : G) : G ⧸ H) :=
      continuous_quotient_mk'.comp continuous_inv
    exact hc
  refine ⟨fun q => _root_.GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.fibreIntegral H ν (fun x : G => F.indicator f x⁻¹)
    (QuotientGroup.quotientRightRelEquivQuotientLeftRel H q), hcm.comp he.measurable, ?_, ?_⟩
  · intro g
    show _root_.GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.fibreIntegral H ν (fun x : G => F.indicator f x⁻¹) ((g⁻¹ : G) : G ⧸ H) = _
    rw [_root_.GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.fibreIntegral_mk]
    calc ∫⁻ h : H, F.indicator f (g⁻¹ * (h : G))⁻¹ ∂ν = ∫⁻ h : H, F.indicator f ((h : G) * g) ∂ν := by
          rw [← lintegral_inv_eq_self (μ := ν) (fun h : H => F.indicator f ((h : G) * g))]
          congr 1
          funext h
          simp [mul_inv_rev]
      _ = ∫⁻ h in {h : H | (h : G) * g ∈ F}, f ((h : G) * g) ∂ν := by
          rw [← lintegral_indicator (hFg g)]
          congr 1
      _ = ∫⁻ h in D', f ((h : G) * g) ∂ν := by
          refine (hFD' g).setLIntegral_eq hD' (fun h : H => f ((h : G) * g)) (fun γ h => ?_)
          simp only [Subgroup.smul_def, smul_eq_mul, Subgroup.coe_mul, mul_assoc]
          exact hinv _ (Subgroup.mem_subgroupOf.1 γ.2) _
  · unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.rightMeasure
    calc ∫⁻ x in D, f x ∂dg = ∫⁻ x in F, f x ∂dg :=
          hD.setLIntegral_eq hFD f (fun γ x => hinv _ γ.2 x)
      _ = ∫⁻ x, F.indicator f x ∂dg := (lintegral_indicator hFm f).symm
      _ = ∫⁻ x, F.indicator f x⁻¹ ∂dg := (lintegral_inv_eq_self (μ := dg) (F.indicator f)).symm
      _ = ∫⁻ q, _root_.GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.fibreIntegral H ν (fun x : G => F.indicator f x⁻¹) q ∂μ := hcint
      _ = ∫⁻ q, _root_.GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.fibreIntegral H ν (fun x : G => F.indicator f x⁻¹)
            (QuotientGroup.quotientRightRelEquivQuotientLeftRel H (_root_.GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.invCoset H q)) ∂μ := by
          congr 1
          funext q
          rw [show _root_.GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.invCoset H q =
            (QuotientGroup.quotientRightRelEquivQuotientLeftRel H).symm q from rfl,
            Equiv.apply_symm_apply]
      _ = _ := (lintegral_map (hcm.comp he.measurable)
            (_root_.GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.continuous_invCoset H).measurable).symm

end GlobalTheory.QuotDiscrete
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuotientIntegrationFormulaDiscreteSubgroupLeftStatement
open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotient_integration_formula_discrete_subgroup_left : DiscreteClause := by
  first | exact @GlobalTheory.QuotDiscrete.discreteClause | exact GlobalTheory.QuotDiscrete.discreteClause | (intros; apply GlobalTheory.QuotDiscrete.discreteClause <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RapidDecayAdelicIntegrablePeriodisationContinuou
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RapidDecayAdelicIntegrablePeriodisationContinuou
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory

theorem decay_integrable_periodise : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ), IsTotallyReal F →
    ∀ Φ : (Fin N → AF F) → ℂ, Decay Φ →
      (∀ μ : Measure (Fin N → AF F), μ.IsAddHaarMeasure → Integrable Φ μ) ∧
      (∀ u, Summable fun ξ : Fin N → F => ‖Φ (rat ξ + u)‖) ∧
      Continuous fun u => ∑' ξ : Fin N → F, Φ (rat ξ + u) := by
  intro F _ _ N hF Φ hΦ
  obtain ⟨hc, ⟨K, hK, hKz⟩, hdec⟩ := hΦ
  obtain ⟨k, hk⟩ := GlobalTheory.T.exists_summableMajorant_rationalVectors_locallyUniform F N hF K hK
  obtain ⟨C, hC⟩ := hdec k
  have hsz : ∀ u : Fin N → AF F, 0 ≤ sz u := fun u =>
    Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun w _ => abs_nonneg _
  have hC0 : 0 ≤ C :=
    le_trans (mul_nonneg (norm_nonneg _) (pow_nonneg (by linarith [hsz 0]) k)) (hC 0)
  have key : ∀ ω : Set (Fin N → AF F), IsCompact ω → ∃ c : (Fin N → F) → ℝ, Summable c ∧
      (∀ ξ, 0 ≤ c ξ) ∧ ∀ ξ, ∀ y ∈ ω, ‖Φ (rat ξ + y)‖ ≤ C * c ξ := by
    intro ω hω
    obtain ⟨c, hcs, hc0, hcb⟩ := hk ω hω
    refine ⟨c, hcs, hc0, fun ξ y hy => ?_⟩
    by_cases hmem : fin (rat ξ + y) ∈ K
    · have h1 := hcb ξ y hy hmem
      have h2 := hC (rat ξ + y)
      calc ‖Φ (rat ξ + y)‖ = ‖Φ (rat ξ + y)‖ * 1 := (mul_one _).symm
        _ ≤ ‖Φ (rat ξ + y)‖ * (c ξ * (1 + sz (rat ξ + y)) ^ k) :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
        _ = c ξ * (‖Φ (rat ξ + y)‖ * (1 + sz (rat ξ + y)) ^ k) := by ring
        _ ≤ c ξ * C := mul_le_mul_of_nonneg_left h2 (hc0 ξ)
        _ = C * c ξ := mul_comm _ _
    · rw [hKz _ hmem, norm_zero]
      exact mul_nonneg hC0 (hc0 ξ)
  haveI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ) (M := F)
  refine ⟨?_, ?_, ?_⟩
  · intro μ hμ
    obtain ⟨ν, hν⟩ := GlobalTheory.T.exists_measure_isCov1 F
    obtain ⟨-, -, -, ⟨K₀, hK₀, hcov⟩, -⟩ := GlobalTheory.T.rationalVectors_adeles_fundamentalDomain_mass_one F N ν hν
    obtain ⟨c, hcs, hc0, hcb⟩ := key K₀ hK₀
    refine ⟨hc.aestronglyMeasurable, ?_⟩
    let S : (Fin N → F) → Set (Fin N → AF F) := fun ξ => (fun u => u + -rat ξ) ⁻¹' K₀
    have hSm : ∀ ξ, MeasurableSet (S ξ) := fun ξ =>
      hK₀.measurableSet.preimage (measurable_add_const _)
    have hSμ : ∀ ξ, μ (S ξ) = μ K₀ := fun ξ => measure_preimage_add_right μ (-rat ξ) K₀
    have hpt : ∀ u, ‖Φ u‖ₑ ≤ ∑' ξ, (S ξ).indicator (fun _ => ENNReal.ofReal (C * c ξ)) u := by
      intro u
      obtain ⟨ξ, hξ⟩ := hcov u
      have hu : u ∈ S ξ := by
        show u + -rat ξ ∈ K₀
        rw [← sub_eq_add_neg]; exact hξ
      refine le_trans ?_ (ENNReal.le_tsum ξ)
      rw [Set.indicator_of_mem hu]
      have h3 := hcb ξ (u - rat ξ) hξ
      rw [add_sub_cancel] at h3
      rw [← ofReal_norm_eq_enorm]
      exact ENNReal.ofReal_le_ofReal h3
    have hfin : (∑' ξ, ENNReal.ofReal (C * c ξ)) < ∞ := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun ξ => mul_nonneg hC0 (hc0 ξ)) (hcs.mul_left C)]
      exact ENNReal.ofReal_lt_top
    unfold HasFiniteIntegral
    calc ∫⁻ u, ‖Φ u‖ₑ ∂μ
        ≤ ∫⁻ u, ∑' ξ, (S ξ).indicator (fun _ => ENNReal.ofReal (C * c ξ)) u ∂μ := lintegral_mono hpt
      _ = ∑' ξ, ∫⁻ u, (S ξ).indicator (fun _ => ENNReal.ofReal (C * c ξ)) u ∂μ :=
          lintegral_tsum fun ξ => (measurable_const.indicator (hSm ξ)).aemeasurable
      _ = ∑' ξ, ENNReal.ofReal (C * c ξ) * μ K₀ := by
          congr 1; ext ξ; rw [lintegral_indicator_const (hSm ξ), hSμ]
      _ = (∑' ξ, ENNReal.ofReal (C * c ξ)) * μ K₀ := ENNReal.tsum_mul_right
      _ < ∞ := ENNReal.mul_lt_top hfin hK₀.measure_lt_top
  · intro u
    obtain ⟨c, hcs, hc0, hcb⟩ := key {u} isCompact_singleton
    exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ξ => hcb ξ u rfl) (hcs.mul_left C)
  · refine continuous_iff_continuousAt.2 fun x => ?_
    obtain ⟨ω, hωc, hωn⟩ := exists_compact_mem_nhds x
    obtain ⟨c, hcs, hc0, hcb⟩ := key ω hωc
    have hon : ContinuousOn (fun u => ∑' ξ : Fin N → F, Φ (rat ξ + u)) ω :=
      continuousOn_tsum (fun ξ => (hc.comp (continuous_const.add continuous_id)).continuousOn)
        (hcs.mul_left C) (fun ξ y hy => hcb ξ y hy)
    exact hon.continuousAt hωn

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RapidDecayAdelicIntegrablePeriodisationContinuouStatement
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rapidDecay_adelic_integrable_periodisation_continuous : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ), IsTotallyReal F → ∀ Φ : (Fin N → AF F) → ℂ, Decay Φ → (∀ μ : Measure (Fin N → AF F), μ.IsAddHaarMeasure → Integrable Φ μ) ∧ (∀ u, Summable fun ξ : Fin N → F => ‖Φ (rat ξ + u)‖) ∧ Continuous fun u => ∑' ξ : Fin N → F, Φ (rat ξ + u) := by
  first | exact @GlobalTheory.decay_integrable_periodise | exact GlobalTheory.decay_integrable_periodise | (intros; apply GlobalTheory.decay_integrable_periodise <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryRationalPointsCountableDiscreteFundDomain
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryRationalPointsCountableDiscreteFundDomain
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure MeasureTheory

namespace GlobalTheory.RationalUnitaryDomains

theorem isDiscreteWithDomains_of_discrete {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (Γ : Subgroup G) [hc : Countable Γ] [hd : DiscreteTopology Γ] : IsDiscreteWithDomains Γ := by
  refine ⟨hc, hd, fun μ _ => ?_⟩
  obtain ⟨𝓕, hF, h⟩ := GlobalTheory.FundDomDiscrete.exists_measurable_section Γ
  exact ⟨𝓕, hF, IsFundamentalDomain.mk' hF.nullMeasurableSet h⟩

theorem isDiscreteWithDomains_ratPts' (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) :
    IsDiscreteWithDomains (ratPts (AF F) σ J) := by
  have := (GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary F E σ M J).2.1
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA σ J
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA σ J
  have : Countable (ratPts (AF F) σ J) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma σ J
  have : DiscreteTopology (ratPts (AF F) σ J) := GlobalTheory.RationalDiscrete.discreteTopology_HFinIn σ J
  exact isDiscreteWithDomains_of_discrete _

theorem isDiscreteWithDomains_ratPts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → IsDiscreteWithDomains (ratPts (AF F) σ J) :=
  fun F E _ _ _ _ _ σ _ M J _ => isDiscreteWithDomains_ratPts' F E σ M J

end GlobalTheory.RationalUnitaryDomains
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryRationalPointsCountableDiscreteFundDomainStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryRationalPoints_countable_discrete_fundDomains_cm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → IsDiscreteWithDomains (ratPts (AF F) σ J) := by
  first | exact @GlobalTheory.RationalUnitaryDomains.isDiscreteWithDomains_ratPts | exact GlobalTheory.RationalUnitaryDomains.isDiscreteWithDomains_ratPts | (intros; apply GlobalTheory.RationalUnitaryDomains.isDiscreteWithDomains_ratPts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdelicUnitaryGroupStabilisersUnimodular
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdelicUnitaryGroupStabilisersUnimodular
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure GlobalTheory.GaugeEx
open GlobalTheory.UnitVectorStabiliser GlobalTheory.HermLineZeros
open scoped TensorProduct Matrix

namespace GlobalTheory.AdelicStabUnimod

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}

theorem exists_stepData (h : IsCMExt F E σ) {M : ℕ} {J : Matrix (Fin (M + 1)) (Fin (M + 1)) E}
    (hJ : IsHermND σ J) (x : Fin 1 → Fin (M + 1) → E) (hx : hE σ J (x 0) (x 0) ≠ 0) :
    ∃ (a : F) (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E),
      StepData σ J x a B J' := by
  have herm := hf_herm (σ : E →+* E) J (conj_invol h) hJ.1
  obtain ⟨a, ha⟩ := exists_of_fixed h (hE σ J (x 0) (x 0)) (herm _ _)
  let φ := hfLin (σ : E →+* E) J (x 0)
  have hφ : φ ≠ 0 := fun h0 => hx (LinearMap.congr_fun h0 (x 0))
  have hk : Module.finrank E (LinearMap.ker φ) = M := by
    have := Module.Dual.finrank_ker_add_one_of_ne_zero hφ
    rw [Module.finrank_fin_fun] at this
    omega
  let b := Module.finBasisOfFinrankEq E _ hk
  let B : Matrix (Fin (M + 1)) (Fin M) E := Matrix.of fun i j => (b j : Fin (M + 1) → E) i
  have hG : ∀ i j, (Formalism.UG.cT (σ : E →+* E) B * J * B) i j =
      Formalism.UG.hform (σ : E →+* E) J (b i) (b j) := fun i j => by
    simp only [Formalism.UG.hform, Formalism.UG.cT, Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    rfl
  refine ⟨a, B, _, hJ, ?_, ha.symm, fun j => (b j).2, rfl, fun i j => ?_, fun hd => ?_⟩
  · rintro rfl
    exact hx (by rw [← ha, map_zero])
  · rw [hG, hG]
    exact herm _ _
  · obtain ⟨c, hc, hc0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hd
    let y : LinearMap.ker φ := ∑ j, c j • b j
    have h1 : ∀ i, hfLin (σ : E →+* E) J y (b i) = 0 := fun i => by
      have h2 : hfLin (σ : E →+* E) J (b i) y = 0 := by
        rw [← show _ = (0 : E) from congrFun hc0 i]
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [y, Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul, Matrix.mulVec,
          dotProduct, hG, smul_eq_mul]
        exact Finset.sum_congr rfl fun j _ => mul_comm _ _
      exact (herm _ _).symm.trans ((congrArg _ h2).trans (map_zero _))
    have h3 : ∀ z : LinearMap.ker φ, hfLin (σ : E →+* E) J y z = 0 := fun z =>
      LinearMap.congr_fun (b.ext (f₁ := hfLin (σ : E →+* E) J y ∘ₗ Submodule.subtype _) (f₂ := 0) h1) z
    have h4 : hfLin (σ : E →+* E) J y (x 0) = 0 :=
      (herm _ _).symm.trans ((congrArg _ (show Formalism.UG.hform _ J (x 0) y = 0 from y.2)).trans (map_zero _))
    obtain ⟨t, p, hp, -⟩ := exists_proj (σ : E →+* E) J (x 0) hx.isUnit (LinearMap.ker φ) fun _ => Iff.rfl
    have h5 : ∀ z, Formalism.UG.hform (σ : E →+* E) J z y = 0 := fun z => by
      have : hfLin (σ : E →+* E) J y z = 0 := by
        rw [hp z, map_add (f := _), map_smul, h3, h4, smul_zero, add_zero]
      exact (herm _ _).symm.trans ((congrArg _ this).trans (map_zero _))
    have h6 : J *ᵥ (y : Fin (M + 1) → E) = 0 := funext fun i => by
      have := h5 (Pi.single i 1)
      rw [hf_eq] at this
      simpa [dotProduct, Pi.single_apply, apply_ite] using this
    have h7 : y = 0 := Subtype.ext (Matrix.eq_zero_of_mulVec_eq_zero hJ.2 h6)
    exact hc (funext (Fintype.linearIndependent_iff.1 b.linearIndependent c h7))

theorem isUnimodularLC_of_equiv {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] [Group H] [TopologicalSpace H] [MeasurableSpace H]
    (hH : IsUnimodularLC H) (e : G ≃* H) (h1 : Continuous e) (h2 : Continuous e.symm) :
    IsUnimodularLC G := by
  obtain ⟨_, _, _, _, _, -, hH⟩ := hH
  let e' : G ≃ₜ H := ⟨e.toEquiv, h1, h2⟩
  haveI := e'.isEmbedding.t2Space
  haveI := e'.isClosedEmbedding.locallyCompactSpace
  haveI := e'.secondCountableTopology
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨Measure.haar, inferInstance⟩, fun μ hμ => ⟨fun g => ?_⟩⟩
  haveI := hH _ (MulEquiv.isHaarMeasure_map μ e h1 h2)
  have h3 := congrArg (Measure.map e.symm) (map_mul_right_eq_self (μ.map e) (e g))
  rw [Measure.map_map h2.measurable h1.measurable,
    Measure.map_map (measurable_mul_const _) h1.measurable,
    Measure.map_map h2.measurable ((measurable_mul_const _).comp h1.measurable)] at h3
  convert h3 using 1
  · congr 1
    funext y
    simp
  · rw [show e.symm ∘ e = id from funext fun y => by simp, Measure.map_id]

theorem unimodularOver_of_forall (h : IsCMExt F E σ) (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R]
    [SecondCountableTopology R]
    (hR : ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
      ∀ μ : Measure (HA R σ J), μ.IsHaarMeasure → μ.IsMulRightInvariant)
    (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) : UnimodularOver R σ J := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have key : ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → IsUnimodularLC (HA R σ J) :=
    fun M J hJ => ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      ⟨Measure.haar, inferInstance⟩, hR M J hJ⟩
  refine ⟨key M J hJ, fun x hx => ?_⟩
  cases M with
  | zero => exact absurd (by simp [hE, Formalism.UG.hform]) hx
  | succ M =>
    obtain ⟨a, B, J', hS⟩ := exists_stepData h hJ x hx
    borelize R
    obtain ⟨-, ⟨e, he, -⟩, hc⟩ := GlobalTheory.FrameStep.frameStep F E σ h R M J x a B J' hS
    exact isUnimodularLC_of_equiv (key M J' hS.2.2.2.2.2) e (hc e he).1 (hc e he).2

theorem unimodularOver_adele : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → UnimodularOver (AF F) σ J := by
  intro F E _ _ _ _ _ σ h
  obtain ⟨d, hd⟩ := exists_conj_ne h
  exact unimodularOver_of_forall h (AF F) fun M J hJ μ _ =>
    GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_adelic σ (conj_invol h) (sub_ne_zero.2 hd)
      (by rw [map_sub, conj_invol h, neg_sub]) hJ μ

end GlobalTheory.AdelicStabUnimod
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdelicUnitaryGroupStabilisersUnimodularStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_unitaryGroup_stabilisers_unimodular : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → UnimodularOver (AF F) σ J := by
  first | exact @GlobalTheory.AdelicStabUnimod.unimodularOver_adele | exact GlobalTheory.AdelicStabUnimod.unimodularOver_adele | (intros; apply GlobalTheory.AdelicStabUnimod.unimodularOver_adele <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsEqStandardAdeleCharRationalDilate
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsEqStandardAdeleCharRationalDilate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex

namespace GlobalTheory.AdelicCharDilate

theorem exists_eq_std_dilate : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [StarRing E] (σ : E →ₐ[F] E), IsCMExt F E σ → (∀ x : E, star x = σ x) → Formalism.HermitianLatticesTheory.IsCMUnram E →
    ∀ ψ₀, IsStdChar F ψ₀ → ∀ ψ, IsCharAF F ψ →
      ∃ a : F, a ≠ 0 ∧ ∀ x, ψ x = ψ₀ (algebraMap F (AF F) a * x) := by
  intro F E _ _ _ _ _ _ σ hCM _ _ ψ₀ h₀ ψ h
  haveI := hCM.1
  exact GlobalTheory.T.exists_ne_zero_adele_char_eq_comp_mul_totally_real F ψ₀ ψ h₀.1 h

end GlobalTheory.AdelicCharDilate
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsEqStandardAdeleCharRationalDilateStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eq_standardAdeleChar_rational_dilate : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (σ : E →ₐ[F] E), IsCMExt F E σ → (∀ x : E, star x = σ x) → Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ ψ₀, IsStdChar F ψ₀ → ∀ ψ, IsCharAF F ψ → ∃ a : F, a ≠ 0 ∧ ∀ x, ψ x = ψ₀ (algebraMap F (AF F) a * x) := by
  first | exact @GlobalTheory.AdelicCharDilate.exists_eq_std_dilate | exact GlobalTheory.AdelicCharDilate.exists_eq_std_dilate | (intros; apply GlobalTheory.AdelicCharDilate.exists_eq_std_dilate <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslateMomentsAllOfJetMomR
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.PlaceComponents GlobalTheory.QuadSubfield
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

namespace GlobalTheory.MomT.FromComb

variable {D : D7} {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p])

variable {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
  {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}

theorem chi_mem {χ : IdE D → ℂ} (hχ : IsChi D χ) {𝔞 : IdE D} (ha : N1 D 𝔞) : χ 𝔞 ∈ Qbar := by
  let _ := D.host.cmStar
  obtain ⟨k, hk, z, hz, hspan⟩ := CU.pow_unitary D ha
  have hzu : z ∈ unitary D.host.E := by
    rw [Unitary.mem_iff, CU.star_conj]
    exact ⟨by rw [mul_comm]; exact hz, hz⟩
  have h := hχ.2 ⟨z, hzu⟩
  simp only at h
  rw [← hspan, CU.chi_pow D χ hχ ha k hk] at h
  refine mem_algebraicClosure_iff.2 (IsAlgebraic.of_pow (by omega : 0 < k) (mem_algebraicClosure_iff.1 ?_))
  rw [h]
  exact prod_mem fun τ _ => inv_mem (emb_mem D _ _)

theorem chiFac_mem {χ : IdE D → ℂ} (hχ : IsChi D χ) (hA : admitted D N N' L L') : Base.chiFac χ N N' L L' ∈ Qbar :=
  mul_mem (zpow_mem (chi_mem hχ (relative_determinant_norm_one D N _ L hA.1 (GlobalTheory.FourthRootStd.stdL_isSD D N) hA.2.2.1)) _)
    (zpow_mem (chi_mem hχ (relative_determinant_norm_one D N' _ L' hA.2.1 (GlobalTheory.FourthRootStd.stdL_isSD D N') hA.2.2.2)) _)

end GlobalTheory.MomT.FromComb
end
end
