module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.IwasawaUnitaryAdelic.IUAIwa
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntertwinerOfKFiniteVectors
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SqIntIrrPerm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMapInfFinEquivEqProd
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.AdmissibleOfIwasawa
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieOneLMemZalg
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedCechToCatCochainsOneApplyValueAtSubset
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeCharacterExistsUnique
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalOfL2CuspidalMem
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalOfL2CuspidalMem
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
open scoped ENNReal Pointwise

noncomputable section

namespace GlobalTheory.CompanionTheory.CuspL2

theorem exists_lintegral_enorm_lift_le {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G)
    [DiscreteTopology Γ] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {C : Set G} (hC : IsCompact C) :
    ∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ F : L2 Γ μ, ∫⁻ g in C, ‖lift Γ F g‖ₑ ∂μ ≤ M * ‖F‖ₑ := by
  have hS : {γ : Γ | (γ : G) ∈ C * C⁻¹}.Finite := finite_mem_compact (hC.mul hC.inv)
  obtain ⟨N, hNdef⟩ : ∃ N : ℝ≥0∞, N = ({γ : Γ | (γ : G) ∈ C * C⁻¹}.encard : ℝ≥0∞) := ⟨_, rfl⟩
  have hN : N ≠ ∞ := by simpa [hNdef] using hS
  have hfin : μ C ≠ ∞ := hC.measure_lt_top.ne
  refine ⟨N ^ (1 / 2 : ℝ) * μ C ^ (1 / 2 : ℝ), ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hN)
    (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hfin), fun F => ?_⟩
  have hm : AEStronglyMeasurable (lift Γ F) μ :=
    aestronglyMeasurable_quotMeasure_iff_lift.1 (Lp.aestronglyMeasurable F)
  have h2 : ∫⁻ g in C, ‖lift Γ F g‖ₑ ^ (2 : ℝ≥0∞).toReal ∂μ ≤
      N * ∫⁻ q, ‖F q‖ₑ ^ (2 : ℝ≥0∞).toReal ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ := by
    rw [← lintegral_indicator hC.measurableSet,
      lintegral_eq_lintegral_tsum (Γ := Γ) ((hm.enorm.pow_const _).indicator hC.measurableSet),
      ← lintegral_const_mul' _ _ hN]
    refine lintegral_mono fun q => ?_
    rw [hNdef]
    refine le_trans (le_of_eq (tsum_congr fun γ => ?_)) (GlobalTheory.AutomorphicL2Local.tsum_indicator_le Γ C q.out _)
    by_cases hγ : (γ : G) * q.out ∈ C
    · rw [Set.indicator_of_mem hγ, Set.indicator_of_mem hγ]
      simp only [GlobalTheory.AutomorphicL2Unitary.lift, mk_mul, Quotient.out_eq]
    · rw [Set.indicator_of_notMem hγ, Set.indicator_of_notMem hγ]
  have h3 : eLpNorm (lift Γ F) 2 (μ.restrict C) ≤ N ^ (1 / 2 : ℝ) * ‖F‖ₑ := by
    rw [Lp.enorm_def, eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp) (by simp),
      eLpNorm_eq_lintegral_rpow_enorm_toReal (f := F) (by simp) (by simp)]
    refine (ENNReal.rpow_le_rpow h2 (by simp)).trans (le_of_eq ?_)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by simp)]
    simp
    exact Lp.aestronglyMeasurable F
    exact hm.restrict
  have h4 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := μ.restrict C) (p := 1) (q := 2) (by norm_num) hm.restrict
  have e : (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) = (1 / 2 : ℝ) := by norm_num
  rw [eLpNorm_one_eq_lintegral_enorm, e, Measure.restrict_apply_univ] at h4
  calc _ ≤ N ^ (1 / 2 : ℝ) * ‖F‖ₑ * μ C ^ (1 / 2 : ℝ) := h4.trans (by gcongr)
    _ = _ := by ring
  exact hm.restrict

section Adelic

variable {E : Type} [Field E] [NumberField E] {a r : ℕ}

theorem exists_mem_apply_unip_eq {X : Type*} {u : GA E a → X} (hl : ∀ γ g, u (ratGL E a γ * g) = u g)
    {K : Set (BlockIx a r → Ad E)} (hcov : ∀ x, ∃ γ ∈ ratN E a r, γ + x ∈ K) (x : BlockIx a r → Ad E) :
    ∃ k ∈ K, ∀ g, u (unip x * g) = u (unip k * g) := by
  obtain ⟨_, ⟨y, rfl⟩, hk⟩ := hcov x
  refine ⟨_, hk, fun g => ?_⟩
  rw [unip_add, mul_assoc]
  exact ((congrArg (fun v => u (v * _)) (unip_algebraMap y)).trans (hl _ _)).symm

variable [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)]

theorem lintegral_constTerm_le [_root_.NumberField.IsTotallyComplex E] (μ : Measure (GA E a)) [μ.IsHaarMeasure]
    (ν : Measure (BlockIx a r → Ad E)) {𝓕 : Set (BlockIx a r → Ad E)} (hν𝓕 : ν 𝓕 ≠ ∞)
    {K : Set (BlockIx a r → Ad E)} (hK : IsCompact K) (hcov : ∀ x, ∃ γ ∈ ratN E a r, γ + x ∈ K) {C : Set (GA E a)}
    (hC : IsCompact C) {u : GA E a → ℂ} (hc : Continuous u) (hl : ∀ γ g, u (ratGL E a γ * g) = u g) :
    ∫⁻ g in C, ‖∫ x in 𝓕, u (unip x * g) ∂ν‖ₑ ∂μ ≤ ν 𝓕 * ∫⁻ g in (unip '' K) * C, ‖u g‖ₑ ∂μ := by
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
  haveI : IsFiniteMeasure (ν.restrict 𝓕) := isFiniteMeasure_restrict.2 hν𝓕
  haveI : IsFiniteMeasure (μ.restrict C) := isFiniteMeasure_restrict.2 hC.measure_lt_top.ne
  have hC' : IsCompact ((unip '' K) * C) := (hK.image continuous_unip).mul hC
  have hb : ∀ x, ∫⁻ g in C, ‖u (unip x * g)‖ₑ ∂μ ≤ ∫⁻ g in (unip '' K) * C, ‖u g‖ₑ ∂μ := fun x => by
    obtain ⟨k, hk, e⟩ := exists_mem_apply_unip_eq hl hcov x
    simp only [e]
    rw [← (measurePreserving_mul_left μ (unip k)).setLIntegral_comp_preimage hC'.measurableSet
      hc.enorm.measurable]
    exact lintegral_mono_set fun g hg => Set.mul_mem_mul ⟨k, hk, rfl⟩ hg
  have hj : Continuous fun p : GA E a × (BlockIx a r → Ad E) => ‖u (unip p.2 * p.1)‖ₑ :=
    (hc.comp ((continuous_unip.comp continuous_snd).mul continuous_fst)).enorm
  calc ∫⁻ g in C, ‖∫ x in 𝓕, u (unip x * g) ∂ν‖ₑ ∂μ
      ≤ ∫⁻ g in C, ∫⁻ x in 𝓕, ‖u (unip x * g)‖ₑ ∂ν ∂μ :=
        lintegral_mono fun g => enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ x in 𝓕, ∫⁻ g in C, ‖u (unip x * g)‖ₑ ∂μ ∂ν := by
      set_option synthInstance.maxHeartbeats 200000 in
      exact lintegral_lintegral_swap hj.aemeasurable
    _ ≤ ∫⁻ x in 𝓕, (∫⁻ g in (unip '' K) * C, ‖u g‖ₑ ∂μ) ∂ν := lintegral_mono hb
    _ = _ := by rw [setLIntegral_const, mul_comm]

theorem continuous_constTerm [_root_.NumberField.IsTotallyComplex E] (ν : Measure (BlockIx a r → Ad E)) {𝓕 : Set (BlockIx a r → Ad E)}
    (hν𝓕 : ν 𝓕 ≠ ∞) {K : Set (BlockIx a r → Ad E)} (hK : IsCompact K) (hcov : ∀ x, ∃ γ ∈ ratN E a r, γ + x ∈ K)
    {u : GA E a → ℂ} (hc : Continuous u) (hl : ∀ γ g, u (ratGL E a γ * g) = u g) :
    Continuous fun g => ∫ x in 𝓕, u (unip x * g) ∂ν := by
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
  haveI : IsFiniteMeasure (ν.restrict 𝓕) := isFiniteMeasure_restrict.2 hν𝓕
  refine continuous_iff_continuousAt.2 fun g₀ => ?_
  obtain ⟨C, hC, hg⟩ := exists_compact_mem_nhds g₀
  obtain ⟨B, hB⟩ := ((hK.image continuous_unip).mul hC).exists_bound_of_continuousOn hc.continuousOn
  refine continuousAt_of_dominated (bound := fun _ => B)
    (.of_forall fun g => (hc.comp (continuous_unip.mul continuous_const)).aestronglyMeasurable) ?_
    (integrable_const _) (.of_forall fun x => (hc.comp (continuous_const.mul continuous_id)).continuousAt)
  filter_upwards [hg] with g hg'
  refine .of_forall fun x => ?_
  obtain ⟨k, hk, e⟩ := exists_mem_apply_unip_eq hl hcov x
  rw [e]
  exact hB _ (Set.mul_mem_mul ⟨k, hk, rfl⟩ hg')

end Adelic

theorem isCuspidal_of_toL2_mem : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (φ : GA E a → ℂ), Continuous φ →
    (∀ γ g, φ (ratGL E a γ * g) = φ g) → (∀ t g, φ (splitCentre E a t * g) = φ g) →
    ∀ h : MemL2Quotient (latticeGL E a) μ φ, h.toL2 ∈ L2cusp μ → IsCuspidal φ := by
  intro E _ _ _ a μ _ _ φ hc hl hs h hF r h0 h1 _ _ ν 𝓕 hν h𝓕 g
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
  haveI := GlobalTheory.ConstNotCusp.discreteTopology_ratN E a r
  haveI : Countable (ratN E a r) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.ConstNotCusp.exists_compact_ratN E a r
  have hν𝓕 : ν 𝓕 ≠ ∞ := (GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact _ hK hcov ν h𝓕).ne
  have hcont := continuous_constTerm ν hν𝓕 hK hcov hc hl
  have key : ∀ C : Set (GA E a), IsCompact C → ∫⁻ g in C, ‖∫ x in 𝓕, φ (unip x * g) ∂ν‖ₑ ∂μ = 0 := fun C hC => by
    obtain ⟨M, hM, hb⟩ := exists_lintegral_enorm_lift_le (latticeGL E a) μ ((hK.image continuous_unip).mul hC)
    have step : ∀ F' ∈ cuspContinuousL2 μ, ∫⁻ g in C, ‖∫ x in 𝓕, φ (unip x * g) ∂ν‖ₑ ∂μ ≤ ν 𝓕 * (M * ‖h.toL2 - F'‖ₑ) := by
      rintro F' ⟨ψ, hψ, e⟩
      have hcomp : ∀ g, ∫ x in 𝓕, (φ (unip x * g) - ψ (unip x * g)) ∂ν = ∫ x in 𝓕, φ (unip x * g) ∂ν := fun g => by
        rw [integral_sub (integrableOn_unip hc hl ν h𝓕 g) (integrableOn_unip hψ.1 hψ.2.1 ν h𝓕 g),
          hψ.2.2.2 r h0 h1 ν 𝓕 hν h𝓕 g, sub_zero]
      have h2 := lintegral_constTerm_le μ ν hν𝓕 hK hcov hC (u := fun g => φ g - ψ g) (hc.sub hψ.1)
        (fun γ g => by rw [hl, hψ.2.1])
      simp only [hcomp] at h2
      have e' : lift (latticeGL E a) (h.toL2 - F') =ᵐ[μ] fun g => φ g - ψ g :=
        Filter.EventuallyEq.trans (ae_quotMeasure_iff.1 (Lp.coeFn_sub h.toL2 F')) (h.lift_toL2_ae_eq.sub e)
      refine h2.trans ?_
      gcongr
      refine le_trans (le_of_eq (lintegral_congr_ae (ae_restrict_of_ae ?_))) (hb (h.toL2 - F'))
      exact e'.mono fun g eg => by rw [eg]
    obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.1 (show h.toL2 ∈ closure (cuspContinuousL2 μ : Set _) from hF)
    have ht : Filter.Tendsto (fun n => ν 𝓕 * (M * ‖h.toL2 - u n‖ₑ)) Filter.atTop (𝓝 0) := by
      have h3 : Filter.Tendsto (fun n => h.toL2 - u n) Filter.atTop (𝓝 0) := by
        simpa using (tendsto_const_nhds (x := h.toL2)).sub hlim
      have h4 : Filter.Tendsto (fun n => ‖h.toL2 - u n‖ₑ) Filter.atTop (𝓝 0) := by
        simpa [Function.comp_def] using (continuous_enorm.tendsto _).comp h3
      simpa using ENNReal.Tendsto.const_mul (ENNReal.Tendsto.const_mul h4 (Or.inr hM)) (Or.inr hν𝓕)
    exact le_antisymm (ge_of_tendsto' ht fun n => step _ (hu n)) zero_le
  have hae : (fun g => ∫ x in 𝓕, φ (unip x * g) ∂ν) =ᵐ[μ] 0 := by
    set_option synthInstance.maxHeartbeats 200000 in
    have h5 : ∀ n, ∀ᵐ g ∂μ.restrict (compactCovering (GA E a) n), ∫ x in 𝓕, φ (unip x * g) ∂ν = 0 := fun n => by
      have := (lintegral_eq_zero_iff' hcont.enorm.aemeasurable).1 (key _ (isCompact_compactCovering _ n))
      exact this.mono fun g eg => by simpa using eg
    have h6 := ae_restrict_iUnion_iff _ _ |>.2 h5
    rwa [iUnion_compactCovering, Measure.restrict_univ] at h6
  exact congrFun ((Continuous.ae_eq_iff_eq μ hcont continuous_zero).1 hae) g

end GlobalTheory.CompanionTheory.CuspL2

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalOfL2CuspidalMemStatement
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_of_L2_cuspidal_mem : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (φ : GA E a → ℂ), Continuous φ → (∀ γ g, φ (ratGL E a γ * g) = φ g) → (∀ t g, φ (splitCentre E a t * g) = φ g) → ∀ h : MemL2Quotient (latticeGL E a) μ φ, h.toL2 ∈ L2cusp μ → IsCuspidal φ := by
  first | exact @GlobalTheory.CompanionTheory.CuspL2.isCuspidal_of_toL2_mem | exact GlobalTheory.CompanionTheory.CuspL2.isCuspidal_of_toL2_mem | (intros; apply GlobalTheory.CompanionTheory.CuspL2.isCuspidal_of_toL2_mem <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleOfLinearReductive
open MeasureTheory Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.AdmIwa

open CompanionTheory.D.gk.admitted

variable {n : ℕ}

def Gp (G : Set (Matrix (Fin n) (Fin n) ℂ)) : Type := {g : Matrix (Fin n) (Fin n) ℂ // g ∈ G}

variable {G : Set (Matrix (Fin n) (Fin n) ℂ)}

instance : TopologicalSpace (Gp G) := instTopologicalSpaceSubtype
instance : T2Space (Gp G) := inferInstanceAs (T2Space {g : Matrix (Fin n) (Fin n) ℂ // g ∈ G})
instance : SecondCountableTopology (Gp G) :=
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  inferInstanceAs (SecondCountableTopology {g : Matrix (Fin n) (Fin n) ℂ // g ∈ G})

def Gp.m (g : Gp G) : Matrix (Fin n) (Fin n) ℂ := g.1

theorem Gp.ext {a b : Gp G} (h : a.m = b.m) : a = b := Subtype.ext h

theorem continuous_m : Continuous (Gp.m : Gp G → Matrix (Fin n) (Fin n) ℂ) := continuous_subtype_val

theorem isEmbedding_m : Topology.IsEmbedding (Gp.m : Gp G → Matrix (Fin n) (Fin n) ℂ) :=
  Topology.IsEmbedding.subtypeVal

variable [hG : Fact (GlobalTheory.LinRed.IsLinRed G)]

instance : Group (Gp G) where
  mul a b := ⟨a.1 * b.1, hG.out.mul_mem _ a.2 _ b.2⟩
  one := ⟨1, hG.out.one_mem⟩
  inv a := ⟨a.1⁻¹, hG.out.inv_mem _ a.2⟩
  mul_assoc a b c := Subtype.ext (Matrix.mul_assoc _ _ _)
  one_mul a := Subtype.ext (Matrix.one_mul _)
  mul_one a := Subtype.ext (Matrix.mul_one _)
  inv_mul_cancel a := Subtype.ext
    (Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (hG.out.isUnit _ a.2)))

instance : IsTopologicalGroup (Gp G) where
  continuous_mul := by
    refine isEmbedding_m.continuous_iff.2 ?_
    exact (continuous_m.comp continuous_fst).matrix_mul (continuous_m.comp continuous_snd)
  continuous_inv := by
    refine isEmbedding_m.continuous_iff.2 ?_
    have h : ((Gp.m : Gp G → _) ∘ fun a : Gp G => a⁻¹) =
        fun a : Gp G => (a.m.det)⁻¹ • a.m.adjugate := by
      funext a
      show (a.m)⁻¹ = _
      rw [Matrix.inv_def, Ring.inverse_eq_inv']
    rw [h]
    refine Continuous.smul (Continuous.inv₀ continuous_m.matrix_det fun a => ?_)
      continuous_m.matrix_adjugate
    exact ((Matrix.isUnit_iff_isUnit_det _).1 (hG.out.isUnit _ a.2)).ne_zero

def Kc (G : Set (Matrix (Fin n) (Fin n) ℂ)) [hG : Fact (GlobalTheory.LinRed.IsLinRed G)] : Subgroup (Gp G) where
  carrier := {g | g.m ∈ Matrix.unitaryGroup (Fin n) ℂ}
  one_mem' := Submonoid.one_mem (Matrix.unitaryGroup (Fin n) ℂ)
  mul_mem' ha hb := Submonoid.mul_mem (Matrix.unitaryGroup (Fin n) ℂ) ha hb
  inv_mem' {a} ha := by
    show (a.m)⁻¹ ∈ Matrix.unitaryGroup (Fin n) ℂ
    rw [Matrix.inv_eq_left_inv (Matrix.mem_unitaryGroup_iff'.1 ha)]
    exact Unitary.star_mem ha

theorem mem_Kc {k : Gp G} : k ∈ Kc G ↔ k.m ∈ Matrix.unitaryGroup (Fin n) ℂ := Iff.rfl

theorem isCompact_maxCpt : IsCompact (GlobalTheory.LinRed.maxCpt G) := by
  have hbd : GlobalTheory.LinRed.maxCpt G ⊆ Set.pi Set.univ fun _ : Fin n => Set.pi Set.univ fun _ : Fin n =>
      Metric.closedBall (0 : ℂ) 1 := by
    intro g hg i _ j _
    simpa using entry_norm_bound_of_unitary hg.2 i j
  have hcmp : IsCompact (Set.pi Set.univ fun _ : Fin n => Set.pi Set.univ fun _ : Fin n =>
      Metric.closedBall (0 : ℂ) 1 : Set (Fin n → Fin n → ℂ)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  refine IsCompact.of_isClosed_subset hcmp ?_ hbd
  refine isClosed_of_closure_subset fun g hg => ?_
  have hU : IsClosed (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) := by
    have : (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) = {m | mᴴ * m = 1} := by
      ext m
      exact Matrix.mem_unitaryGroup_iff'
    rw [this]
    exact isClosed_eq (continuous_id.matrix_conjTranspose.matrix_mul continuous_id) continuous_const
  have hgU : g ∈ Matrix.unitaryGroup (Fin n) ℂ :=
    hU.closure_subset_iff.2 Set.inter_subset_right (closure_mono (le_refl _) hg)
  have hgu : IsUnit g := IsUnit.of_mul_eq_one _ (Matrix.mem_unitaryGroup_iff.1 hgU)
  exact ⟨hG.out.closed g hgu (closure_mono Set.inter_subset_left hg), hgU⟩

instance : CompactSpace (Kc G) := by
  refine isCompact_univ_iff.1 ?_
  have he : Topology.IsEmbedding fun k : Kc G => (k.1).m :=
    isEmbedding_m.comp Topology.IsEmbedding.subtypeVal
  rw [he.isCompact_iff, Set.image_univ]
  have : Set.range (fun k : Kc G => (k.1).m) = GlobalTheory.LinRed.maxCpt G := by
    ext m
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k.1.2, mem_Kc.1 k.2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨⟨m, h1⟩, mem_Kc.2 h2⟩, rfl⟩
  rw [this]
  exact isCompact_maxCpt

instance : MeasurableSpace (Kc G) := borel _
instance : BorelSpace (Kc G) := ⟨rfl⟩

def homG {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : Formalism.MainNotions.S.IsURepOn G σ) : Gp G →* (H →L[ℂ] H) where
  toFun g := σ g.m
  map_one' := hσ.1.1
  map_mul' a b := hσ.1.2 _ a.2 _ b.2

def stdG (G : Set (Matrix (Fin n) (Fin n) ℂ)) [hG : Fact (GlobalTheory.LinRed.IsLinRed G)]
    {U : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    Gp G →* Matrix (Fin n) (Fin n) ℂ where
  toFun g := Uᴴ * g.m * U
  map_one' := by
    have h1 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hU
    show Uᴴ * 1 * U = 1
    rw [Matrix.mul_one, h1]
  map_mul' a b := by
    have h1 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hU
    show Uᴴ * (a.m * b.m) * U = _
    calc Uᴴ * (a.m * b.m) * U = Uᴴ * a.m * (U * Uᴴ) * b.m * U := by
          rw [h1]; simp only [Matrix.mul_assoc, Matrix.one_mul]
      _ = _ := by simp only [Matrix.mul_assoc]


omit hG in
theorem admissible_of_polynomial_identity (h1 : FinOfPI) (h2 : GoodPI) (h3 : Transfer) (h4 : ExistsAvg)
    (hLR : GlobalTheory.LinRed.IsLinRed G) (h5 : PositivityTheory.Tls2.Iua.IwaOn G) : PositivityTheory.Tls2.Iua.AdmG G := by
  haveI : Fact (GlobalTheory.LinRed.IsLinRed G) := ⟨hLR⟩
  intro H _ _ _ σ hσ hirr S _ hS v hv
  obtain ⟨U, hU, hiwa⟩ := h5
  let μ : Measure (Kc G) := (Measure.haar : Measure (Kc G)).inv
  have hμ : IsFiniteMeasure μ := CompactSpace.isFiniteMeasure
  have hsc : SecondCountableTopology (Kc G) := TopologicalSpace.Subtype.secondCountableTopology _
  have hiso : ∀ g u, ‖homG hσ g u‖ = ‖u‖ := fun g u => hσ.2.1 _ g.2 u
  have hc : ∀ u, Continuous fun g => homG hσ g u := fun u =>
    (hσ.2.2 u).comp_continuous continuous_m fun g => g.2
  obtain ⟨e, E, he, hfin, hE, hEv⟩ := h4 (Kc G) μ H ((homG hσ).comp (Kc G).subtype) (fun k u => hiso k u)
    (fun u => (hc u).comp continuous_subtype_val) S (fun k u hu => hS _ ⟨k.1.2, mem_Kc.1 k.2⟩ u hu) v hv
  let st : Gp G → Gp G := fun g => ⟨g.mᴴ, hLR.star_mem _ g.2⟩
  let Tr : Set (Gp G) := {s | (stdG G hU s).BlockTriangular id}
  have hgood : IsGood st Tr (stdG G hU) := by
    refine ⟨(continuous_const.matrix_mul continuous_m).matrix_mul continuous_const, fun g => ?_,
      Fin.val, Fin.val_injective, fun s hs i j hij => hs hij⟩
    show Uᴴ * g.mᴴ * U = (Uᴴ * g.m * U)ᴴ
    simp [Matrix.mul_assoc]
  have hinj : Function.Injective (stdG G hU) := by
    intro a b hab
    have h1 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hU
    have key : ∀ g : Gp G, U * stdG G hU g * Uᴴ = g.m := fun g => by
      show U * (Uᴴ * g.m * U) * Uᴴ = _
      calc U * (Uᴴ * g.m * U) * Uᴴ = (U * Uᴴ) * g.m * (U * Uᴴ) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [h1, Matrix.one_mul, Matrix.mul_one]
    exact Gp.ext ((key a).symm.trans (hab ▸ key b))
  have hKS : ∀ g : Gp G, ∃ k ∈ Kc G, ∃ s ∈ Tr, g = k * s := by
    intro g
    obtain ⟨k, hk, s, hs, hg, ht⟩ := hiwa g.m g.2
    exact ⟨⟨k, hk.1⟩, mem_Kc.2 hk.2, ⟨s, hs⟩, ht, Gp.ext hg⟩
  have hPI : ∀ g : Fin (Module.finrank ℂ S ^ 2 + 1) → Gp G, stdPoly E (fun i => homG hσ (g i)) = 0 := fun g =>
    h3 (Gp G) (Kc G) μ st Tr (Fin n) (stdG G hU) hgood hinj e he _ g
      (fun ι _ _ ρ hρ E' hE' => h2 (Gp G) (Kc G) μ st Tr hKS e _ _ he hfin (Nat.lt_succ_self _) ι ρ hρ E' hE' g)
      H (homG hσ) hc E hE
  obtain ⟨hfd, hrk⟩ := h1 (Gp G) H (homG hσ) hiso (fun S' hcl hS' => hirr S' hcl fun g hg u hu =>
    hS' ⟨g, hg⟩ u hu) E _ hPI
  refine ⟨_, hfd, hrk, ⟨v, hEv⟩, ?_⟩
  rintro T hT _ ⟨u, rfl⟩
  refine ⟨T u, ?_⟩
  show E (T u) = T (E u)
  rw [hE, hE, ← T.integral_comp_comm]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    show e k • σ k.1.1 (T u) = T (e k • σ k.1.1 u)
    rw [map_smul, hT _ ⟨k.1.2, mem_Kc.1 k.2⟩ u]
  · exact (he.smul ((hc u).comp continuous_subtype_val)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

theorem RamifiedPrimeLengthBound {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} (hLR : GlobalTheory.LinRed.IsLinRed G)
    (h : PositivityTheory.Tls2.Iua.IwaOn G) : PositivityTheory.Tls2.Iua.AdmG G :=
  admissible_of_polynomial_identity finite_rank_of_irreducible_unitary (goodPI_of small_irreducible_representation) transfer_holds exists_averaging_operator hLR h

end GlobalTheory.CompanionTheory.AdmIwa
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothVectorCompactUnipotentFixer
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothVectorCompactUnipotentFixer
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open GroundTheory.Automorphic.GLnLocal
open scoped TensorProduct Topology

namespace GlobalTheory.CompanionTheory.Rodier.OpenBump

theorem exists_smInd_bump {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup W] [Module ℂ W] (H K : Subgroup G) (hK : IsOpen (K : Set G))
    (σ : Representation ℂ H W) (v : W) (hv : ∀ c : H, (c : G) ∈ K → σ c v = v) :
    ∃ f : smoothPart (ind H σ), (∀ g, f.1.1 g ≠ 0 → ∃ p ∈ H, ∃ κ ∈ K, g = p * κ) ∧
      ∀ κ ∈ K, f.1.1 κ = v := by
  classical
  have key : ∀ p q : H, (p : G)⁻¹ * q ∈ K → σ q v = σ p v := by
    intro p q hpq
    have h1 : σ (p⁻¹ * q) v = v := hv _ (by simpa using hpq)
    have h2 : q = p * (p⁻¹ * q) := by group
    calc σ q v = σ (p * (p⁻¹ * q)) v := by rw [← h2]
      _ = σ p (σ (p⁻¹ * q) v) := by rw [map_mul]; rfl
      _ = σ p v := by rw [h1]
  let S : G → Prop := fun x => ∃ p : H, (p : G)⁻¹ * x ∈ K
  let pick : G → H := fun x => if h : S x then h.choose else 1
  have pick_spec : ∀ x, S x → ((pick x : H) : G)⁻¹ * x ∈ K := by
    intro x h
    simp only [pick, dif_pos h]
    exact h.choose_spec
  let F : G → W := fun x => if S x then σ (pick x) v else 0
  have F_pos : ∀ x, S x → F x = σ (pick x) v := fun x h => if_pos h
  have F_neg : ∀ x, ¬ S x → F x = 0 := fun x h => if_neg h
  have S_left : ∀ (q : H) x, S x → S (q * x) := by
    rintro q x ⟨p, hp⟩
    exact ⟨q * p, by simpa [mul_assoc] using hp⟩
  have S_right : ∀ c ∈ K, ∀ x, S x → S (x * c) := by
    rintro c hc x ⟨p, hp⟩
    exact ⟨p, by simpa [mul_assoc] using K.mul_mem hp hc⟩
  have hlaw : F ∈ indSpace H σ := by
    intro q x
    by_cases hx : S x
    · have hqx := S_left q x hx
      rw [F_pos _ hqx, F_pos _ hx, ← Module.End.mul_apply, ← map_mul]
      refine key _ _ ?_
      have h3 := K.mul_mem (pick_spec x hx) (K.inv_mem (pick_spec _ hqx))
      convert h3 using 1
      simp only [Subgroup.coe_mul]
      group
    · have hqx : ¬ S (q * x) := fun h => hx (by
        have := S_left q⁻¹ _ h
        simpa using this)
      rw [F_neg _ hqx, F_neg _ hx, map_zero]
  have hfix : ∀ c ∈ K, ∀ x, F (x * c) = F x := by
    intro c hc x
    by_cases hx : S x
    · have hxc := S_right c hc x hx
      rw [F_pos _ hxc, F_pos _ hx]
      refine key _ _ ?_
      have h3 := K.mul_mem (K.mul_mem (pick_spec x hx) hc) (K.inv_mem (pick_spec _ hxc))
      convert h3 using 1
      group
    · have hxc : ¬ S (x * c) := fun h => hx (by
        have := S_right c⁻¹ (K.inv_mem hc) _ h
        simpa using this)
      rw [F_neg _ hxc, F_neg _ hx]
  have hfix' : ∀ c ∈ K, ind H σ c ⟨F, hlaw⟩ = ⟨F, hlaw⟩ :=
    fun c hc => Subtype.ext (funext fun x => hfix c hc x)
  have hsm : (⟨F, hlaw⟩ : indSpace H σ) ∈ smoothPart (ind H σ) :=
    mem_smoothPart_of_nhds (Filter.mem_of_superset (hK.mem_nhds K.one_mem) fun c hc => hfix' c hc)
  refine ⟨⟨⟨F, hlaw⟩, hsm⟩, fun g hg => ?_, fun κ hκ => ?_⟩
  · have hS : S g := by
      by_contra hS
      exact hg (F_neg g hS)
    exact ⟨pick g, (pick g).2, _, pick_spec g hS, by group⟩
  · have hS : S κ := ⟨1, by simpa using hκ⟩
    show F κ = v
    rw [F_pos κ hS]
    refine hv _ ?_
    have h3 := K.mul_mem hκ (K.inv_mem (pick_spec κ hS))
    simpa using h3

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem eq_one_of_mem_parab_of_mem_lower {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
    [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
    (e : (Σ a, m a) ≃ n) {x : GL n k} (h1 : x ∈ parab k e) (h2 : x ∈ unipRadLower k e) : x = 1 := by
  obtain ⟨h3, h4⟩ := (mem_unipRadLower k).1 h2
  refine Units.ext (Matrix.ext fun i j => ?_)
  obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective i
  obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective j
  have hne : ∀ c : α, ∀ (i' : m c) (b' : α) (j' : m b'), c ≠ b' →
      (1 : Matrix n n k) (e ⟨c, i'⟩) (e ⟨b', j'⟩) = 0 := by
    intro c i' b' j' hcb
    refine Matrix.one_apply_ne fun h' => hcb ?_
    have := e.injective h'
    exact congrArg Sigma.fst this
  rcases lt_trichotomy a b with hab | rfl | hab
  · rw [(mem_parabLower_iff k).1 h3 a b i j hab, Units.val_one, hne a i b j hab.ne]
  · rw [h4 a i j, Units.val_one]
    by_cases e' : i = j
    · subst e'; simp
    · rw [Matrix.one_apply_ne e', Matrix.one_apply_ne]
      intro h'
      exact e' (by simpa using e.injective h')
  · rw [mem_parab_iff.1 h1 a b i j hab, Units.val_one, hne a i b j hab.ne']

theorem exists_parab_mul_lower {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) {m : ℕ} (hm : 1 ≤ m)
    {κ : GL (Fin N) k} (hκ : κ ∈ congruenceSubgroup k N m) :
    ∃ q ∈ parab k (stdBlocks d hd), ∃ z ∈ congruenceSubgroup k N m,
      z ∈ unipRadLower k (stdBlocks d hd) ∧ κ = q * z := by
  obtain ⟨x, hx, y, hy, z, hz, rfl⟩ :=
    GroundTheory.Automorphic.Parabolic.congruenceSubgroup_iwahoriFactorization' (blk (stdBlocks d hd)) hm κ hκ
  have up : ∀ g ∈ GroundTheory.Automorphic.Iwasawa.blockUpper k N (blk (stdBlocks d hd)), g ∈ parab k (stdBlocks d hd) :=
    fun g hg => (GroundTheory.Automorphic.Iwasawa.mem_blockUpper k N).1 hg
  refine ⟨x * y, (parab k _).mul_mem (up _ (GroundTheory.Automorphic.Parabolic.unipotentRadical_le_blockUpper hx.2))
    (up _ (GroundTheory.Automorphic.Parabolic.levi_le_blockUpper hy.2)), z, hz.1, ?_, rfl⟩
  obtain ⟨h1, h2⟩ := GroundTheory.Automorphic.Parabolic.mem_unipotentRadical.1 hz.2
  have h1' := (GroundTheory.Automorphic.Iwasawa.mem_blockUpper k N).1 h1
  refine (mem_unipRadLower k).2 ⟨(mem_parabLower_iff k).2 fun a b i j hab => h1' ?_, fun a i j => ?_⟩
  · simpa [blk] using hab
  · rw [h2 _ _ (by simp [blk])]
    by_cases e' : i = j
    · subst e'; simp
    · rw [Matrix.one_apply_ne e', Matrix.one_apply_ne]
      intro h'
      exact e' (by simpa using (stdBlocks d hd).injective h')

theorem exists_level (ψ : AddChar k Circle) (hψ : Continuous ψ) {h N : ℕ} (d : Fin h → ℕ)
    (hd : ∑ a, d a = N) {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W) (hρ : IsSmooth ρ) (v : W) :
    ∃ m, 1 ≤ m ∧ (∀ c : parab k (stdBlocks d hd), (c : GL (Fin N) k) ∈ congruenceSubgroup k N m →
        ((GlobalTheory.SmGL.twist ρ (deltaHalf k fun a => Fin (d a))).comp (leviProj k (stdBlocks d hd))) c v = v) ∧
      ∀ (l : GL (Fin N) k) (hl : l ∈ unipB k (Fin N)), l ∈ congruenceSubgroup k N m →
        whitChar ψ N ⟨l, hl⟩ = 1 := by
  have hs := isSmooth_twist hρ (isSmoothChar_deltaHalf k (m := fun a => Fin (d a))) v
  have hpre := hs.preimage (ProdIrr.continuous_leviProj (stdBlocks d hd))
  obtain ⟨U, hU, hUe⟩ := isOpen_induced_iff.1 hpre
  have hw : IsOpen ((whitChar ψ N).ker : Set (unipB k (Fin N))) :=
    GlobalTheory.Whittaker.isSmoothChar_whitChar hψ
  obtain ⟨U₂, hU₂, hUe₂⟩ := isOpen_induced_iff.1 hw
  have h1 : (1 : GL (Fin N) k) ∈ U := by
    have h2 : (1 : parab k (stdBlocks d hd)) ∈ Subtype.val ⁻¹' U := by
      rw [hUe]
      simp
    exact h2
  have h1₂ : (1 : GL (Fin N) k) ∈ U₂ := by
    have h2 : (1 : unipB k (Fin N)) ∈ Subtype.val ⁻¹' U₂ := by
      rw [hUe₂]
      exact one_mem _
    exact h2
  obtain ⟨m, -, hm⟩ := (hasBasis_nhds_one k N).mem_iff.1 ((hU.inter hU₂).mem_nhds ⟨h1, h1₂⟩)
  refine ⟨m + 1, by omega, fun c hc => ?_, fun l hl hlK => ?_⟩
  · have h2 : c ∈ Subtype.val ⁻¹' U := (hm (congruenceSubgroup_antitone k N (Nat.le_succ m) hc)).1
    rw [hUe] at h2
    exact h2
  · have h2 : (⟨l, hl⟩ : unipB k (Fin N)) ∈ Subtype.val ⁻¹' U₂ :=
      (hm (congruenceSubgroup_antitone k N (Nat.le_succ m) hlK)).2
    rw [hUe₂] at h2
    exact h2

theorem exists_openFns_bump : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W), IsSmooth ρ → ∀ v : W, ∃ L₀ : Subgroup (GL (Fin N) k), L₀ ≤ unipU k d hd ∧ IsCompact (L₀ : Set (GL (Fin N) k)) ∧ (∃ O : Set (GL (Fin N) k), IsOpen O ∧ O ∩ (unipU k d hd : Set (GL (Fin N) k)) = L₀) ∧ (∀ (l : GL (Fin N) k) (hl : l ∈ unipB k (Fin N)), l ∈ L₀ → whitChar ψ N ⟨l, hl⟩ = 1) ∧ ∃ f ∈ openFns d hd ρ, (∀ u ∈ L₀, f.1.1 (pm k (wOpen d hd) * u) = v) ∧ ∀ u ∈ unipU k d hd, u ∉ L₀ → f.1.1 (pm k (wOpen d hd) * u) = 0 := by
  intro k _ _ _ _ ψ hψ h N d hd W _ _ ρ hρ v
  obtain ⟨m, hm1, hσ, hW⟩ := exists_level ψ hψ d hd ρ hρ v
  obtain ⟨hI1, -, hI3⟩ := GlobalTheory.T.open_cell_unipotent_uniqueness_closed k h N d hd
  have hKo := isOpen_congruenceSubgroup k N m
  have hKc := isCompact_congruenceSubgroup k N m
  set K := congruenceSubgroup k N m with hKdef
  set w := pm k (wOpen d hd) with hwdef
  have hwI : w ∈ integralGL k N := GroundTheory.Automorphic.Parabolic.permGL_mem_integralGL _
  have hconj : ∀ x ∈ K, w * x * w⁻¹ ∈ K := fun x hx => conj_mem_congruenceSubgroup k N hwI hx
  have hconj' : ∀ x ∈ K, w⁻¹ * x * w ∈ K := fun x hx => by
    simpa using conj_mem_congruenceSubgroup k N ((integralGL k N).inv_mem hwI) hx
  obtain ⟨f₀, hsup, hval⟩ := exists_smInd_bump (parab k (stdBlocks d hd)) K hKo
    ((GlobalTheory.SmGL.twist ρ (deltaHalf k fun a => Fin (d a))).comp (leviProj k (stdBlocks d hd))) v hσ
  let f : IndSp (stdBlocks d hd) ρ := smInd (parab k (stdBlocks d hd))
    ((GlobalTheory.SmGL.twist ρ (deltaHalf k fun a => Fin (d a))).comp (leviProj k (stdBlocks d hd))) w⁻¹ f₀
  have hf : ∀ g, f.1.1 g = f₀.1.1 (g * w⁻¹) := fun _ => rfl
  let L₀ : Subgroup (GL (Fin N) k) := unipU k d hd ⊓ K.comap (MulAut.conj w).toMonoidHom
  have memL : ∀ u, u ∈ L₀ ↔ u ∈ unipU k d hd ∧ w * u * w⁻¹ ∈ K := fun u => Iff.rfl
  have memU : ∀ u ∈ unipU k d hd, w * u * w⁻¹ ∈ unipRadLower k (stdBlocks d hd) :=
    fun u hu => hu.2
  have hcont : Continuous fun g : GL (Fin N) k => w⁻¹ * g * w := by fun_prop
  have hcont' : Continuous fun g : GL (Fin N) k => w * g * w⁻¹ := by fun_prop
  refine ⟨L₀, inf_le_left, ?_, ⟨(fun g => w * g * w⁻¹) ⁻¹' (K : Set _), hKo.preimage hcont', ?_⟩,
    ?_, f, ?_, ?_, ?_⟩
  · have hset : (L₀ : Set (GL (Fin N) k)) =
        ((fun g => w⁻¹ * g * w) '' (K : Set (GL (Fin N) k))) ∩ (unipU k d hd : Set _) := by
      ext u
      constructor
      · intro hu
        exact ⟨⟨_, ((memL u).1 hu).2, by group⟩, ((memL u).1 hu).1⟩
      · rintro ⟨⟨x, hx, rfl⟩, hu⟩
        refine (memL _).2 ⟨hu, ?_⟩
        have : w * (w⁻¹ * x * w) * w⁻¹ = x := by group
        rw [this]
        exact hx
    rw [hset]
    exact (hKc.image hcont).inter_right hI3
  · ext u
    exact ⟨fun hu => (memL u).2 ⟨hu.2, hu.1⟩, fun hu => ⟨((memL u).1 hu).2, ((memL u).1 hu).1⟩⟩
  · intro l hl hlL
    refine hW l hl ?_
    have := hconj' _ ((memL l).1 hlL).2
    have e : w⁻¹ * (w * l * w⁻¹) * w = l := by group
    rwa [e] at this
  · intro g hg
    rw [hf] at hg
    obtain ⟨p, hp, κ, hκ, e⟩ := hsup _ hg
    obtain ⟨q, hq, z, hz, hzl, rfl⟩ := exists_parab_mul_lower d hd hm1 hκ
    refine ⟨p * q, (parab k _).mul_mem hp hq, w⁻¹ * z * w, (hI1 z hzl).1, ?_⟩
    have e2 : g = p * (q * z) * w := by
      rw [← e]
      group
    show g = p * q * w * (w⁻¹ * z * w)
    rw [e2]
    group
  · intro u hu
    have := hval _ ((memL u).1 hu).2
    rw [hf]
    exact this
  · intro u hu huL
    rw [hf]
    by_contra hne
    obtain ⟨p, hp, κ, hκ, e⟩ := hsup _ hne
    obtain ⟨q, hq, z, hz, hzl, rfl⟩ := exists_parab_mul_lower d hd hm1 hκ
    have hx := memU u hu
    have h1 : (w * u * w⁻¹) * z⁻¹ = 1 := by
      refine eq_one_of_mem_parab_of_mem_lower (stdBlocks d hd) ?_
        ((unipRadLower k _).mul_mem hx ((unipRadLower k _).inv_mem hzl))
      rw [e]
      have : p * (q * z) * z⁻¹ = p * q := by group
      rw [this]
      exact (parab k _).mul_mem hp hq
    have h2 : w * u * w⁻¹ = z := by rwa [mul_inv_eq_one] at h1
    exact huL ((memL u).2 ⟨hu, h2 ▸ hz⟩)

end GlobalTheory.CompanionTheory.Rodier.OpenBump

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothVectorCompactUnipotentFixerStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bump_section_on_compact_unipotent : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W), IsSmooth ρ → ∀ v : W, ∃ L₀ : Subgroup (GL (Fin N) k), L₀ ≤ unipU k d hd ∧ IsCompact (L₀ : Set (GL (Fin N) k)) ∧ (∃ O : Set (GL (Fin N) k), IsOpen O ∧ O ∩ (unipU k d hd : Set (GL (Fin N) k)) = L₀) ∧ (∀ (l : GL (Fin N) k) (hl : l ∈ unipB k (Fin N)), l ∈ L₀ → whitChar ψ N ⟨l, hl⟩ = 1) ∧ ∃ f ∈ openFns d hd ρ, (∀ u ∈ L₀, f.1.1 (pm k (wOpen d hd) * u) = v) ∧ ∀ u ∈ unipU k d hd, u ∉ L₀ → f.1.1 (pm k (wOpen d hd) * u) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Rodier.OpenBump.exists_openFns_bump | exact GlobalTheory.CompanionTheory.Rodier.OpenBump.exists_openFns_bump | (intros; apply GlobalTheory.CompanionTheory.Rodier.OpenBump.exists_openFns_bump <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DominantHeckeOperatorsCommute
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DominantHeckeOperatorsCommute
open GlobalTheory.PRep PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.CassHecke

theorem isHeckeOpG_mul_mem {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ G V} {K : Subgroup G} {g c : G} (hc : c ∈ K)
    {T : Module.End ℂ (fixed π K)} (h : PositivityTheory.Lbc.IsHeckeOpG π K g T) :
    PositivityTheory.Lbc.IsHeckeOpG π K (g * c) T := by
  intro v f hf
  have hv : π c (v : V) = v := by simpa using v.2 ⟨c, hc⟩
  rw [map_mul, Module.End.mul_apply, hv]
  exact h v f hf

theorem heckeOp_commute : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (D : PositivityTheory.SphericalProduct.CassData G), (∀ a ∈ D.T, ∀ b ∈ D.T, a * b * a⁻¹ * b⁻¹ ∈ D.J) →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π →
    ∀ t t' : D.T, D.IsDom t → D.IsDom t' → ∀ U U' : Module.End ℂ (fixed π D.J),
    PositivityTheory.Lbc.IsHeckeOpG π D.J (t : G) U → PositivityTheory.Lbc.IsHeckeOpG π D.J (t' : G) U' → U * U' = U' * U := by
  intro G _ _ _ D hcomm V _ _ π hπ t t' ht ht' U U' hU hU'
  have h1 := GlobalTheory.T.casselman_first_property G D V π hπ t t' ht ht' U U' hU hU'
  have h2 := GlobalTheory.T.casselman_first_property G D V π hπ t' t ht' ht U' U hU' hU
  have hc : (t' : G)⁻¹ * (t : G)⁻¹ * (t' : G) * (t : G) ∈ D.J := by
    have := hcomm (t' : G)⁻¹ (D.T.inv_mem t'.2) (t : G)⁻¹ (D.T.inv_mem t.2)
    simpa using this
  have h3 : PositivityTheory.Lbc.IsHeckeOpG π D.J ((t : G) * t') (U' * U) := by
    have := isHeckeOpG_mul_mem (D.J.inv_mem hc) h2
    have e : (t' : G) * (t : G) * ((t' : G)⁻¹ * (t : G)⁻¹ * (t' : G) * (t : G))⁻¹ = (t : G) * t' := by
      group
    rwa [e] at this
  exact (GlobalTheory.T.hecke_character_exists_unique G D.J D.isOpen_J D.isCompact_J V π hπ ((t : G) * t')).unique h1 h3

end GlobalTheory.CompanionTheory.CassHecke
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DominantHeckeOperatorsCommuteStatement
open GlobalTheory.PRep PositivityTheory.SphericalProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dominant_hecke_operators_commute : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (D : PositivityTheory.SphericalProduct.CassData G), (∀ a ∈ D.T, ∀ b ∈ D.T, a * b * a⁻¹ * b⁻¹ ∈ D.J) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π → ∀ t t' : D.T, D.IsDom t → D.IsDom t' → ∀ U U' : Module.End ℂ (fixed π D.J), PositivityTheory.Lbc.IsHeckeOpG π D.J (t : G) U → PositivityTheory.Lbc.IsHeckeOpG π D.J (t' : G) U' → U * U' = U' * U := by
  first | exact @GlobalTheory.CompanionTheory.CassHecke.heckeOp_commute | exact GlobalTheory.CompanionTheory.CassHecke.heckeOp_commute | (intros; apply GlobalTheory.CompanionTheory.CassHecke.heckeOp_commute <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedFunctionAtOne
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedFunctionAtOne
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ModelS

theorem one_mem_GLs (n : ℕ) : (1 : Mat n) ∈ GLs n :=
  unit_mem (1 : Matrix.unitaryGroup (Fin n) ℂ)

theorem ini_injective {n : ℕ} (j : Fin n) : Function.Injective (ini j) :=
  Fin.castLE_injective j.isLt

theorem lm_one {n : ℕ} (j : Fin n) : lm j (1 : Mat n) = 1 := by
  delta lm
  rw [Matrix.submatrix_one _ (ini_injective j), Matrix.det_one]

theorem gm_one {n : ℕ} (j : Fin n) : gm j (1 : Mat n) = 1 := by
  delta gm
  rw [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_one,
    ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, Matrix.mul_one,
    Matrix.submatrix_one _ (ini_injective j), Matrix.det_one]

theorem fRaw_one (n : ℕ) (lam : Fin n → ℤ) (lev : Fin n → ℕ) : fRaw lam lev 1 = 1 := by
  delta fRaw
  rw [Set.indicator_of_mem (one_mem_GLs n)]
  simp [lm_one, gm_one]

end GlobalTheory.CompanionTheory.ModelS
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedFunctionAtOneStatement
theorem GlobalTheory.T.inducedFunction_at_one :
    ∀ (n : ℕ) (lam : Fin n → ℤ) (lev : Fin n → ℕ),
      GlobalTheory.CompanionTheory.ModelS.fRaw lam lev 1 = 1 :=
  GlobalTheory.CompanionTheory.ModelS.fRaw_one
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactPartDiagonalMap
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactPartDiagonalMap
open GlobalTheory.BCT PositivityTheory.Rg.BcB.G8.Fin
open scoped Classical

namespace GlobalTheory.CompanionTheory.CptDiag

theorem isCompact_closure_zpowers_image {G G' : Type} [Group G] [Group G'] [TopologicalSpace G] [TopologicalSpace G']
    [T2Space G'] (φ : G →* G') (hφ : Continuous φ) (t : G)
    (ht : IsCompact (closure (Subgroup.zpowers t : Set G))) :
    IsCompact (closure (Subgroup.zpowers (φ t) : Set G')) := by
  have hK : IsCompact (φ '' closure (Subgroup.zpowers t : Set G)) := ht.image hφ
  refine hK.of_isClosed_subset isClosed_closure ?_
  refine closure_minimal ?_ hK.isClosed
  intro x hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  exact ⟨t ^ k, subset_closure (Subgroup.zpow_mem_zpowers t k), map_zpow φ t k⟩

theorem cptPart_diag : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] (Z : Subgroup H), cptPart (Z.map ((MonoidHom.id H).prod (MonoidHom.id H))) = (cptPart Z).map ((MonoidHom.id H).prod (MonoidHom.id H)) := by
  intro H _ _ _ _ Z
  unfold cptPart
  rw [MonoidHom.map_closure]
  congr 1
  ext u
  constructor
  · rintro ⟨hu, hc⟩
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hu
    refine ⟨t, ⟨ht, ?_⟩, rfl⟩
    have := isCompact_closure_zpowers_image (MonoidHom.fst H H) continuous_fst _ hc
    simpa using this
  · rintro ⟨t, ⟨ht, hc⟩, rfl⟩
    have hcont : Continuous ((MonoidHom.id H).prod (MonoidHom.id H)) := by
      show Continuous fun x : H => (x, x)
      exact continuous_id.prodMk continuous_id
    exact ⟨Subgroup.mem_map_of_mem _ ht, isCompact_closure_zpowers_image _ hcont t hc⟩

end GlobalTheory.CompanionTheory.CptDiag
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactPartDiagonalMapStatement
open GlobalTheory.BCT PositivityTheory.Rg.BcB.G8.Fin
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_part_diagonal_map : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] (Z : Subgroup H), cptPart (Z.map ((MonoidHom.id H).prod (MonoidHom.id H))) = (cptPart Z).map ((MonoidHom.id H).prod (MonoidHom.id H)) := by
  first | exact @GlobalTheory.CompanionTheory.CptDiag.cptPart_diag | exact GlobalTheory.CompanionTheory.CptDiag.cptPart_diag | (intros; apply GlobalTheory.CompanionTheory.CptDiag.cptPart_diag <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryBorelSplitting
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryBorelSplitting
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BorelSplit

theorem borelSplitU : PositivityTheory.SphericalProduct.BorelSplitU := by
  intro L _ _ σ n _ b hb
  have hbT : ((b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).BlockTriangular id :=
    (Formalism.UG.P.spherical_upper_iff _).1 hb
  let qb : GlobalTheory.LGrp.blockQ L (id : Fin n → Fin n) := ⟨(b : GL (Fin n) L), hbT⟩
  have htG : GlobalTheory.LGrp.blockProj id qb ∈ GU σ n :=
    GlobalTheory.LGrp.blockProj_mem_GU σ (GlobalTheory.LGrp.selfDualBlocks_id n) qb b.2
  let t : GU σ n := ⟨GlobalTheory.LGrp.blockProj id qb, htG⟩
  have hdiag : ∀ i, ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i =
      ((b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i := by
    intro i
    show (GlobalTheory.LGrp.blockProj id qb).val i i = _
    rw [GlobalTheory.LGrp.blockProj_val]
    simp [GlobalTheory.LGrp.blockPart, qb]
  have hoff : ∀ i j, i ≠ j → ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0 := by
    intro i j hij
    show (GlobalTheory.LGrp.blockProj id qb).val i j = _
    rw [GlobalTheory.LGrp.blockProj_val]
    simp [GlobalTheory.LGrp.blockPart, hij]
  have htT : ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).BlockTriangular id :=
    fun i j h => hoff i j (ne_of_gt h)
  have htiT := Formalism.UG.P.spherical_upper_inv _ htT
  refine ⟨t, t⁻¹ * b, hoff, ⟨?_, ?_⟩, by group⟩
  · refine (Formalism.UG.P.spherical_upper_iff _).2 ?_
    show ((((t : GL (Fin n) L))⁻¹ * (b : GL (Fin n) L) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).BlockTriangular id
    exact Formalism.UG.P.spherical_upper_mul _ _ htiT hbT
  · intro i
    show ((((t : GL (Fin n) L))⁻¹ * (b : GL (Fin n) L) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i = 1
    have h1 : ((((t : GL (Fin n) L))⁻¹ * (t : GL (Fin n) L) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i = 1 := by
      rw [inv_mul_cancel, Units.val_one, Matrix.one_apply_eq]
    rw [Units.val_mul, Formalism.UG.P.spherical_diag_mul _ _ htiT hbT, ← hdiag]
    rwa [Units.val_mul, Formalism.UG.P.spherical_diag_mul _ _ htiT htT] at h1

end GlobalTheory.CompanionTheory.BorelSplit
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryBorelSplittingStatement
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_borel_splitting : PositivityTheory.SphericalProduct.BorelSplitU := by
  first | exact @GlobalTheory.CompanionTheory.BorelSplit.borelSplitU | exact GlobalTheory.CompanionTheory.BorelSplit.borelSplitU | (intros; apply GlobalTheory.CompanionTheory.BorelSplit.borelSplitU <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCompactConjugacyTransversal
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCompactConjugacyTransversal
open GlobalTheory.BCT PositivityTheory.Rg.BcB.G8.Fin
open scoped Classical

namespace GlobalTheory.CompanionTheory.OrbitalCount

theorem exists_compact_reps_of_finite_doubleCosets :
    ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (K : Subgroup H) (N : H),
      IsCompact (K : Set H) →
      (∀ C : Set H, IsCompact C →
        {q : DoubleCoset.Quotient (twCent (MonoidHom.id H) N : Set H) (K : Set H) |
          ∃ k ∈ K, (Quotient.out q * k)⁻¹ * N * MonoidHom.id H (Quotient.out q * k) ∈ C}.Finite) →
      ∀ C : Set H, IsCompact C →
        ∃ D : Set H, IsCompact D ∧ ∀ x : H, x⁻¹ * N * x ∈ C →
          ∃ t ∈ twCent (MonoidHom.id H) N, ∃ d ∈ D, x = t * d := by
  intro H _ _ _ K N hK hfin C hC
  refine ⟨⋃ q ∈ {q : DoubleCoset.Quotient (twCent (MonoidHom.id H) N : Set H) (K : Set H) |
      ∃ k ∈ K, (Quotient.out q * k)⁻¹ * N * MonoidHom.id H (Quotient.out q * k) ∈ C},
      (fun k => Quotient.out q * k) '' (K : Set H), ?_, ?_⟩
  · exact (hfin C hC).isCompact_biUnion fun q _ =>
      hK.image (continuous_const.mul continuous_id)
  · intro x hx
    obtain ⟨h, hh, k, hk, hout⟩ :=
      DoubleCoset.mk_out_eq_mul (twCent (MonoidHom.id H) N) K x
    have hcomm : h * N = N * h := hh
    have hconj : (h * x)⁻¹ * N * (h * x) = x⁻¹ * N * x := by
      have : h⁻¹ * N * h = N := by
        rw [mul_assoc, ← hcomm, inv_mul_cancel_left]
      calc (h * x)⁻¹ * N * (h * x) = x⁻¹ * (h⁻¹ * N * h) * x := by group
        _ = x⁻¹ * N * x := by rw [this]
    set q := DoubleCoset.mk (twCent (MonoidHom.id H) N) K x with hq
    have hd : Quotient.out q * k⁻¹ = h * x := by
      rw [hout]; group
    refine ⟨h⁻¹, inv_mem hh, Quotient.out q * k⁻¹, ?_, ?_⟩
    · refine Set.mem_biUnion (x := q) ?_ ⟨k⁻¹, inv_mem hk, rfl⟩
      refine ⟨k⁻¹, inv_mem hk, ?_⟩
      rw [MonoidHom.id_apply, hd, hconj]
      exact hx
    · rw [hd, inv_mul_cancel_left]

end GlobalTheory.CompanionTheory.OrbitalCount
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCompactConjugacyTransversalStatement
open GlobalTheory.BCT PositivityTheory.Rg.BcB.G8.Fin
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compact_conjugacy_transversal : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (K : Subgroup H) (N : H), IsCompact (K : Set H) →
  (∀ C : Set H, IsCompact C → {q : DoubleCoset.Quotient (twCent (MonoidHom.id H) N : Set H) (K : Set H) |
    ∃ k ∈ K, (Quotient.out q * k)⁻¹ * N * MonoidHom.id H (Quotient.out q * k) ∈ C}.Finite) →
  ∀ C : Set H, IsCompact C → ∃ D : Set H, IsCompact D ∧ ∀ x : H, x⁻¹ * N * x ∈ C → ∃ t ∈ twCent (MonoidHom.id H) N, ∃ d ∈ D, x = t * d := by
  first | exact @GlobalTheory.CompanionTheory.OrbitalCount.exists_compact_reps_of_finite_doubleCosets | exact GlobalTheory.CompanionTheory.OrbitalCount.exists_compact_reps_of_finite_doubleCosets | (intros; apply GlobalTheory.CompanionTheory.OrbitalCount.exists_compact_reps_of_finite_doubleCosets <;> assumption)
end
end
