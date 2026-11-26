module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleFiniteLength
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerHeredity
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAutFunOfMemCusp
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IkedaPartialFourierIntegralMemAdelicSchwartz
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrameValuesPolynomialDetStableHomogeneous
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullOfValuesSesq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CodimOneIntegralSubschemeDim
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.CProps
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeOperatorJacquetEigenLeft
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeOperatorJacquetEigenRight
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnlinkedCommuteOfIrreducible

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFibreMeasureExtensionByOne
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFibreMeasureExtensionByOne
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.StageF.ToOld

theorem linearIndependent_of_isUnit_gram {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (X : Fin n → Fin M → R ⊗[F] E)
    (h : IsUnit (gramR R σ J X).det) : LinearIndependent (R ⊗[F] E) X := by
  rw [Fintype.linearIndependent_iff]
  intro w hw
  have hj : ∀ j, ∑ b, w b * X b j = 0 := fun j => by
    have := congrFun hw j
    simpa [Finset.sum_apply] using this
  have hmul : (gramR R σ J X).mulVec w = 0 := by
    funext a
    show ∑ b, hform (sigR R σ) (JR R J) (X a) (X b) * w b = 0
    simp only [hform, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    have : ∑ b, sigR R σ (X a i) * JR R J i j * X b j * w b =
        sigR R σ (X a i) * JR R J i j * ∑ b, w b * X b j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun b _ => by ring
    rw [this, hj j, mul_zero]
  have h1 := congrArg (Matrix.mulVec (gramR R σ J X)⁻¹) hmul
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ h, Matrix.one_mulVec, Matrix.mulVec_zero] at h1
  exact fun i => congrFun h1 i


open Classical in
theorem isFibreFamily_restrict {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [TopologicalSpace X]
    [MeasurableSpace X] (μ : Measure V) (f : V → Y) (ι : X → Y) (U W : Set V) (ν : Measure X)
    (B : Set X) (fib : X → Measure V) (hUW : U ⊆ W) (hU : MeasurableSet U)
    (hUB : ∀ v b, f v = ι b → (v ∈ U ↔ b ∈ B))
    (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι W ν Set.univ fib) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν B (fun b => if b ∈ B then fib b else 0) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun b => ?_, fun φ hφ => ?_, fun φ hc hs ht => ?_⟩
  · by_cases hb : b ∈ B
    · simp only [hb, if_true]
      refine measure_mono_null (Set.compl_subset_compl.2 fun v (hv : v ∈ f ⁻¹' {ι b} ∩ W) => ⟨hv.1, ?_⟩) (h1 b)
      exact (hUB v b hv.1).2 hb
    · simp [hb]
  · have key := h2 (U.indicator φ) (hφ.indicator hU)
    rw [lintegral_indicator hU, Measure.restrict_restrict hU, Set.inter_eq_left.2 hUW] at key
    rw [key]
    refine lintegral_congr fun b => ?_
    have hae : ∀ᵐ v ∂(fib b), f v = ι b := by
      have : ∀ᵐ v ∂(fib b), v ∈ f ⁻¹' {ι b} ∩ W := mem_ae_iff.2 (h1 b)
      filter_upwards [this] with v hv using hv.1
    by_cases hb : b ∈ B
    · simp only [hb, if_true]
      refine lintegral_congr_ae ?_
      filter_upwards [hae] with v hv
      exact Set.indicator_of_mem ((hUB v b hv).2 hb) φ
    · simp only [hb, if_false, lintegral_zero_measure]
      refine (lintegral_congr_ae (g := fun _ => 0) ?_).trans lintegral_zero
      filter_upwards [hae] with v hv
      exact Set.indicator_of_notMem (fun hvU => hb ((hUB v b hv).1 hvU)) φ
  · obtain ⟨k1, k2⟩ := h3 φ hc hs (ht.trans hUW)
    refine ⟨fun b hb => ?_, ?_⟩
    · simpa only [hb, if_true] using k1 b (Set.mem_univ b)
    · exact (k2.mono (Set.subset_univ B)).congr fun b hb => by simp only [hb, if_true]

theorem stageData_of_stageDataF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), HermitianMeasureData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∃ m₀ : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E), StageData σ J t n b lam m₁ m₀ s B₀ a κ₁ cm := by
  intro F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm D
  obtain ⟨iTR, iLC, iSC, iT2, -⟩ := id D.hR
  haveI := iTR; haveI := iLC; haveI := iSC; haveI := iT2
  obtain ⟨kTR, kLC, kSC, kT2, -, -, -, kB, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ D.hCM R
  haveI := kTR; haveI := kLC; haveI := kSC; haveI := kT2
  haveI := kB n M
  obtain ⟨-, -, -, -, hg⟩ := GlobalTheory.T.hermitian_matrices_locally_compact_borel F E σ D.hCM R n
  obtain ⟨g, gc, hgg⟩ := hg M J D.hJ
  have hopen : IsOpen (Unt σ R n) := by
    have hu : IsOpen {x : R ⊗[F] E | IsUnit x} := by
      have := (GlobalTheory.T.units_open_embedding_local_tensor F E σ D.hCM R D.hR).isOpen_range
      convert this using 1
      ext x
      simp [IsUnit]
    have hc : Continuous fun S : HermR R σ n => (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det :=
      continuous_subtype_val.matrix_det
    exact hu.preimage hc
  have hset : {X | IsUnit (gramR R σ J X).det} = g ⁻¹' (Unt σ R n) := by
    ext X
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Unt, hgg X]
  have hmeas : MeasurableSet {X : Fin n → Fin M → R ⊗[F] E | IsUnit (gramR R σ J X).det} := by
    rw [hset]
    exact (hopen.preimage gc).measurableSet
  have hfam := isFibreFamily_restrict (coordW R b lam n M) (gramR R σ J) Subtype.val
    {X | IsUnit (gramR R σ J X).det} {X | LinearIndependent (R ⊗[F] E) X} (coordHerm R σ b lam n)
    {S | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det} m'
    (fun X hX => linearIndependent_of_isUnit_gram R σ J X hX) hmeas
    (fun X S hX => by simp only [Set.mem_setOf_eq, hX]) D.hm'
  exact ⟨_, { hCM := D.hCM, hJ := D.hJ, ht := D.ht, hR := D.hR, hlam := D.hlam, hm₁ := D.hm₁, hm' := hfam,
              hs := D.hs, hsec := D.hsec, hcpt := D.hcpt, hB₀ := D.hB₀, htB := D.htB, hac := D.hac,
              hoff := D.hoff, hsq := D.hsq, ha1 := D.ha1, hκc := D.hκc, hκ1 := D.hκ1, hscale := D.hscale,
              hcmc := D.hcmc, hmod := D.hmod }⟩

end GlobalTheory.CompanionTheory.SW.StageF.ToOld
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFibreMeasureExtensionByOneStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_fibre_measure_extension_by_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), HermitianMeasureData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∃ m₀ : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E), StageData σ J t n b lam m₁ m₀ s B₀ a κ₁ cm := by
  first | exact @GlobalTheory.CompanionTheory.SW.StageF.ToOld.stageData_of_stageDataF | exact GlobalTheory.CompanionTheory.SW.StageF.ToOld.stageData_of_stageDataF | (intros; apply GlobalTheory.CompanionTheory.SW.StageF.ToOld.stageData_of_stageDataF <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreIntegralContinuousInParameter
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreIntegralContinuousInParameter
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.FibreJointOpen

theorem continuousOn_fibre_integral_of_subset : ∀ (V X Y : Type) [TopologicalSpace V] [LocallyCompactSpace V] [T2Space V] [MeasurableSpace V] [BorelSpace V] [TopologicalSpace X] [LocallyCompactSpace X] [MeasurableSpace X] (μ : Measure V) (ν : Measure X) (f : V → Y) (ι : X → Y) (U : Set V), IsOpen U → ∀ (B : Set X), IsOpen B → ∀ fib : X → Measure V, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν B fib → ∀ (P : Type) [TopologicalSpace P] (W : Set P) (Φ : P → V → ℝ), ContinuousOn (fun p : P × V => Φ p.1 p.2) (W ×ˢ Set.univ) → IsOpen W → ∀ C : Set V, IsCompact C → C ⊆ U → (∀ p ∈ W, ∀ v, v ∉ C → Φ p v = 0) → ContinuousOn (fun q : P × X => ∫ v, Φ q.1 v ∂(fib q.2)) (W ×ˢ B) := by
  intro V X Y _ _ _ _ _ _ _ _ μ ν f ι U hU B hB fib hF P _ W Φ hΦ hW C hC hCU hsupp
  obtain ⟨-, -, h3⟩ := hF

  have hAt : ∀ p ∈ W, ∀ v, ContinuousAt (fun p : P × V => Φ p.1 p.2) (p, v) := fun p hp v =>
    hΦ.continuousAt ((hW.prod isOpen_univ).mem_nhds ⟨hp, Set.mem_univ v⟩)
  have hslice : ∀ p ∈ W, Continuous (Φ p) := fun p hp =>
    continuous_iff_continuousAt.2 fun v =>
      ContinuousAt.comp (f := fun v : V => (p, v)) (g := fun p : P × V => Φ p.1 p.2)
        (hAt p hp v) (by fun_prop)
  have hcs : ∀ p ∈ W, HasCompactSupport (Φ p) := fun p hp =>
    HasCompactSupport.intro hC (hsupp p hp)
  have hts : ∀ p ∈ W, tsupport (Φ p) ⊆ U := fun p hp => by
    refine (closure_minimal ?_ hC.isClosed).trans hCU
    intro v hv
    by_contra hvC
    exact hv (hsupp p hp v hvC)
  have hint : ∀ p ∈ W, ∀ b ∈ B, Integrable (Φ p) (fib b) := fun p hp b hb =>
    (h3 (Φ p) (hslice p hp) (hcs p hp) (hts p hp)).1 b hb

  have hbd : ∀ D : Set X, IsCompact D → D ⊆ B → ∃ c : ℝ≥0, ∀ b ∈ D, fib b C ≤ c := by
    intro D hD hDB
    obtain ⟨φ, hc, hcs', hs, h0, -, hone⟩ := GlobalTheory.CompanionTheory.SW.FibreFam.exists_bump hC hU hCU
    obtain ⟨hi, hco⟩ := h3 φ hc hcs' hs
    obtain ⟨M, hM⟩ := hD.exists_bound_of_continuousOn (hco.mono hDB)
    refine ⟨M.toNNReal, fun b hb => ?_⟩
    calc fib b C ≤ ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib b) :=
          GlobalTheory.CompanionTheory.SW.FibreFam.le_lintegral_bump _ hC h0 hone
      _ = ENNReal.ofReal (∫ v, φ v ∂(fib b)) :=
          (ofReal_integral_eq_lintegral_ofReal (hi b (hDB hb))
            (Filter.Eventually.of_forall h0)).symm
      _ ≤ ENNReal.ofReal M := ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hM b hb))
      _ = (M.toNNReal : ℝ≥0∞) := rfl
  rintro ⟨p₀, b₀⟩ ⟨hp₀, hb₀⟩
  simp only [Set.mem_prod] at hp₀ hb₀ ⊢
  refine ContinuousAt.continuousWithinAt ?_
  obtain ⟨D, hDn, hDB, hDc⟩ := local_compact_nhds (hB.mem_nhds hb₀)
  obtain ⟨c, hc⟩ := hbd D hDc hDB
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  set δ : ℝ := ε / (2 * ((c : ℝ) + 1)) with hδ
  have hc0 : (0 : ℝ) ≤ c := c.2
  have hδ0 : 0 < δ := by positivity

  have htube : ∀ᶠ p in 𝓝 p₀, ∀ v ∈ C, |Φ p v - Φ p₀ v| < δ := by
    refine hC.eventually_forall_of_forall_eventually fun v _ => ?_
    have h1 : ContinuousAt (fun z : P × V => Φ z.1 z.2 - Φ p₀ z.2) (p₀, v) :=
      (hAt p₀ hp₀ v).sub
        (ContinuousAt.comp (f := fun z : P × V => z.2) (g := Φ p₀)
          (hslice p₀ hp₀).continuousAt continuousAt_snd)
    have h2 : Filter.Tendsto (fun z : P × V => Φ z.1 z.2 - Φ p₀ z.2) (𝓝 (p₀, v)) (𝓝 0) := by
      have h3 := h1.tendsto
      simp only [sub_self] at h3
      exact h3
    have h4 := (Metric.tendsto_nhds.1 h2) δ hδ0
    filter_upwards [h4] with z hz
    simpa [Real.dist_eq] using hz
  have hb : ∀ᶠ b in 𝓝 b₀,
      |∫ v, Φ p₀ v ∂(fib b) - ∫ v, Φ p₀ v ∂(fib b₀)| < ε / 2 := by
    have h1 := (((h3 (Φ p₀) (hslice p₀ hp₀) (hcs p₀ hp₀) (hts p₀ hp₀)).2).continuousAt
      (hB.mem_nhds hb₀)).tendsto
    have h2 := (Metric.tendsto_nhds.1 h1) (ε / 2) (by positivity)
    filter_upwards [h2] with b hb
    simpa [Real.dist_eq] using hb
  rw [nhds_prod_eq]
  have hp : ∀ᶠ p in 𝓝 p₀, p ∈ W ∧ ∀ v ∈ C, |Φ p v - Φ p₀ v| < δ :=
    Filter.Eventually.and (hW.mem_nhds hp₀) htube
  have hbb : ∀ᶠ b in 𝓝 b₀, b ∈ D ∧
      |∫ v, Φ p₀ v ∂(fib b) - ∫ v, Φ p₀ v ∂(fib b₀)| < ε / 2 := Filter.Eventually.and hDn hb
  filter_upwards [hp.prod_mk hbb] with q hq
  obtain ⟨⟨hqW, hqt⟩, hqD, hqb⟩ := hq
  obtain ⟨p, b⟩ := q
  simp only at hqW hqt hqD hqb ⊢
  have hbB : b ∈ B := hDB hqD
  have hfin : fib b C < ∞ := (hc b hqD).trans_lt ENNReal.coe_lt_top
  have hdiff : ∫ v, Φ p v ∂(fib b) - ∫ v, Φ p₀ v ∂(fib b)
      = ∫ v in C, (Φ p v - Φ p₀ v) ∂(fib b) := by
    rw [← integral_sub (hint p hqW b hbB) (hint p₀ hp₀ b hbB)]
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun v hv => ?_).symm
    rw [hsupp p hqW v hv, hsupp p₀ hp₀ v hv, sub_zero]
  have hreal : (fib b).real C ≤ c := by
    have := ENNReal.toReal_mono ENNReal.coe_ne_top (hc b hqD)
    simpa [Measure.real] using this
  have hle : |∫ v, Φ p v ∂(fib b) - ∫ v, Φ p₀ v ∂(fib b)| ≤ δ * (c : ℝ) := by
    rw [hdiff, ← Real.norm_eq_abs]
    have h5 : ‖∫ v in C, (Φ p v - Φ p₀ v) ∂(fib b)‖ ≤ δ * (fib b).real C :=
      norm_setIntegral_le_of_norm_le_const (C := δ) hfin fun v hv => by
        rw [Real.norm_eq_abs]; exact (hqt v hv).le
    exact h5.trans (mul_le_mul_of_nonneg_left hreal hδ0.le)
  have hδc : δ * (c : ℝ) ≤ ε / 2 := by
    rw [hδ, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  rw [Real.dist_eq]
  calc |∫ v, Φ p v ∂(fib b) - ∫ v, Φ p₀ v ∂(fib b₀)|
      = |(∫ v, Φ p v ∂(fib b) - ∫ v, Φ p₀ v ∂(fib b))
          + (∫ v, Φ p₀ v ∂(fib b) - ∫ v, Φ p₀ v ∂(fib b₀))| := by congr 1; ring
    _ ≤ _ := abs_add_le _ _
    _ < ε := by linarith

end GlobalTheory.CompanionTheory.SW.FibreJointOpen
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreIntegralContinuousInParameterStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_integral_continuous_in_parameter : ∀ (V X Y : Type) [TopologicalSpace V] [LocallyCompactSpace V] [T2Space V] [MeasurableSpace V] [BorelSpace V] [TopologicalSpace X] [LocallyCompactSpace X] [MeasurableSpace X] (μ : Measure V) (ν : Measure X) (f : V → Y) (ι : X → Y) (U : Set V), IsOpen U → ∀ (B : Set X), IsOpen B → ∀ fib : X → Measure V, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν B fib → ∀ (P : Type) [TopologicalSpace P] (W : Set P) (Φ : P → V → ℝ), ContinuousOn (fun p : P × V => Φ p.1 p.2) (W ×ˢ Set.univ) → IsOpen W → ∀ C : Set V, IsCompact C → C ⊆ U → (∀ p ∈ W, ∀ v, v ∉ C → Φ p v = 0) → ContinuousOn (fun q : P × X => ∫ v, Φ q.1 v ∂(fib q.2)) (W ×ˢ B) := by
  first | exact @GlobalTheory.CompanionTheory.SW.FibreJointOpen.continuousOn_fibre_integral_of_subset | exact GlobalTheory.CompanionTheory.SW.FibreJointOpen.continuousOn_fibre_integral_of_subset | (intros; apply GlobalTheory.CompanionTheory.SW.FibreJointOpen.continuousOn_fibre_integral_of_subset <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReducibleCuspidalPairNongenericSubquotient
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinrankEqProdOfNonemptyEquiv
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.WhitRank

theorem finrank_piTensorProduct_eq_prod {ι : Type} [Fintype ι] (E : ι → Type) [∀ i, AddCommGroup (E i)]
    [∀ i, Module ℂ (E i)] : Module.finrank ℂ (⨂[ℂ] i, E i) = ∏ i, Module.finrank ℂ (E i) := by
  open Module in
  rw [Module.finrank_eq_nat_card_basis (Basis.piTensorProduct fun i => Module.Free.chooseBasis ℂ (E i)),
    Nat.card_pi]
  exact Finset.prod_congr rfl fun i _ => (Module.finrank_eq_nat_card_basis (Module.Free.chooseBasis ℂ (E i))).symm

theorem finrank_eq_prod_of_nonempty_equiv {ι A : Type} [Fintype ι] [AddCommGroup A] [Module ℂ A] (E : ι → Type)
    [∀ i, AddCommGroup (E i)] [∀ i, Module ℂ (E i)] (e : Nonempty (A ≃ₗ[ℂ] ⨂[ℂ] i, E i)) :
    Module.finrank ℂ A = ∏ i, Module.finrank ℂ (E i) := by
  obtain ⟨f⟩ := e
  rw [f.finrank_eq, finrank_piTensorProduct_eq_prod]

theorem whitRankProd_of_heredity : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], WhitHeredity k → WhitRankProd k := by
  intro k _ _ _ _ hW ψ hψ hψ1 h N x hd
  obtain ⟨f⟩ := hW ψ hψ hψ1 h N (fun a => (x a).fst) hd (fun a => (x a).snd.rep.V) (fun a => (x a).rep)
    (fun a => (x a).snd.rep.smooth)
  exact finrank_eq_prod_of_nonempty_equiv _ ⟨f⟩

end GlobalTheory.CompanionTheory.WhitRank

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReducibleCuspidalPairNongenericSubquotient
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir Zc

noncomputable section

namespace GlobalTheory.CompanionTheory.CuspPair

section General

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem apply_mem_twKer {σ : Representation ℂ G V} {τ : Representation ℂ G W} (q : σ.IntertwiningMap τ)
    (H : Subgroup G) (χ : H →* ℂˣ) {v : V} (hv : v ∈ twKer σ H χ) : q v ∈ twKer τ H χ := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨n, u, rfl⟩ := hx
    refine Submodule.subset_span ⟨n, q u, ?_⟩
    rw [map_sub, map_smul, q.isIntertwining]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem exists_subquotient_subsingleton [TopologicalSpace G] [IsTopologicalGroup G] (π : Representation ℂ G V)
    (H : Subgroup G) (χ : H →* ℂˣ) (hs : IsSmooth π) (hf : HasFiniteLength π) (hn : ¬ π.IsIrreducible)
    (h1 : Module.finrank ℂ (TwJacquet π H χ) = 1)
    (hr : ∀ (S : Subrepresentation π) (v : S.toSubmodule), (v : V) ∈ twKer π H χ → v ∈ twKer S.toRepresentation H χ) :
    ∃ τ : IrrRep G, IsSubquotient τ.ρ π ∧ Subsingleton (TwJacquet τ.ρ H χ) := by
  have hq1 : Nontrivial (TwJacquet π H χ) := Module.nontrivial_of_finrank_pos (R := ℂ) (by omega)
  have hV : Nontrivial V := (Submodule.mkQ_surjective (twKer π H χ)).nontrivial
  have hbt : (⊥ : Subrepresentation π) ≠ ⊤ := by
    intro h
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    have hmem : x ∈ (⊤ : Subrepresentation π).toSubmodule := Submodule.mem_top
    rw [← h] at hmem
    exact hx ((Submodule.mem_bot ℂ).1 hmem)
  obtain ⟨S, hS0, hST⟩ : ∃ S : Subrepresentation π, S ≠ ⊥ ∧ S ≠ ⊤ := by
    by_contra hc
    push Not at hc
    exact hn { exists_pair_ne := ⟨⊥, ⊤, hbt⟩
               eq_bot_or_eq_top := fun S => (eq_or_ne S ⊥).imp_right (hc S) }
  by_cases hSK : S.toSubmodule ≤ twKer π H χ
  · let i : S.toRepresentation.IntertwiningMap π := ⟨S.toSubmodule.subtype, fun g => rfl⟩
    have hi : Function.Injective i := Subtype.val_injective
    have hsq := IsSubquotient.of_injective i hi
    have hSn : Nontrivial S.toSubmodule := Submodule.nontrivial_iff_ne_bot.2 fun h =>
      hS0 (by ext v; rw [h]; rfl)
    obtain ⟨Y, _, _, τ, hτs, hτi, q, hq⟩ := GlobalTheory.SmGL.IrrQuot.exists_irreducible_smooth_quotient S.toRepresentation
      (hsq.isSmooth hs) (GlobalTheory.ProdLength.hasFiniteLength_of_injective i hi hf) hSn
    refine ⟨⟨Y, τ, hτs, hτi⟩, ⟨S, q, hq⟩, ?_⟩
    refine Submodule.Quotient.subsingleton_iff.2 (eq_top_iff.2 fun w _ => ?_)
    obtain ⟨v, rfl⟩ := hq w
    exact apply_mem_twKer q H χ (hr S v (hSK v.2))
  · obtain ⟨s, hsS, hsK⟩ := IsConcreteLE.not_le_iff_exists.1 hSK
    have hs0 : (Submodule.mkQ (twKer π H χ)) s ≠ 0 := fun h => hsK ((Submodule.Quotient.mk_eq_zero _).1 h)
    have hline := (finrank_eq_one_iff_of_nonzero' _ hs0).1 h1
    let U : Submodule ℂ V := S.toSubmodule
    have hU : ∀ g, U ≤ U.comap (π g) := fun g v hv => S.apply_mem_toSubmodule g hv
    let σ : Representation ℂ G (V ⧸ U) := π.quotient U hU
    let p : π.IntertwiningMap σ := ⟨U.mkQ, fun g => by ext v; rfl⟩
    have hp : Function.Surjective p := Submodule.mkQ_surjective U
    have hsq := IsSubquotient.of_surjective p hp
    have hUn : Nontrivial (V ⧸ U) := Submodule.Quotient.nontrivial_iff.2 fun h =>
      hST (by ext v; rw [show S.toSubmodule = ⊤ from h]; rfl)
    have hfq : HasFiniteLength σ := IsFiniteLength.of_surjective hf
      (f := Representation.IntertwiningMap.equivLinearMapAsModule π σ p) hp
    obtain ⟨Y, _, _, τ, hτs, hτi, q, hq⟩ := GlobalTheory.SmGL.IrrQuot.exists_irreducible_smooth_quotient σ
      (hsq.isSmooth hs) hfq hUn
    refine ⟨⟨Y, τ, hτs, hτi⟩, (IsSubquotient.of_surjective q hq).trans hsq, ?_⟩
    refine Submodule.Quotient.subsingleton_iff.2 (eq_top_iff.2 fun w _ => ?_)
    obtain ⟨b, rfl⟩ := hq w
    obtain ⟨v, rfl⟩ := hp b
    obtain ⟨c, hc⟩ := hline (Submodule.mkQ _ v)
    have hk : v - c • s ∈ twKer π H χ := by
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul]
      exact sub_eq_zero.2 hc.symm
    have hpe : p v = p (v - c • s) := by
      have h0 : p (c • s) = 0 := (Submodule.Quotient.mk_eq_zero U).2 (U.smul_mem c hsS)
      have h2 : v = (v - c • s) + c • s := by abel
      conv_lhs => rw [h2, map_add (f := _), h0, add_zero]
    rw [hpe]
    exact apply_mem_twKer q H χ (apply_mem_twKer p H χ hk)

end General

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem finrank_twJacquet_of_isCusp (hW : WhitRankIrr k) {ψ : AddChar k Circle} (hc : Continuous ψ) (h1 : ψ ≠ 1)
    {x : IrrGL (k := k)} (hx : x.IsCusp) :
    Module.finrank ℂ (TwJacquet x.rep (unipB k (Fin x.1)) (whitChar ψ x.1)) = 1 := by
  obtain ⟨d, c⟩ := x
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by have := hx.1; simp at this; omega⟩
  have hV : Nontrivial c.rep.V := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    obtain ⟨a, b, hab⟩ := c.rep.irr.exists_pair_ne
    refine hab ?_
    ext v
    rw [Subsingleton.elim v 0]
    exact ⟨fun _ => b.toSubmodule.zero_mem, fun _ => a.toSubmodule.zero_mem⟩
  have hg : IsGenericFor ψ c.rep.ρ := GlobalTheory.T.cuspidal_is_generic k ψ hc h1 n _ c.rep.ρ hx.2 hV
  have hle := hW ψ hc h1 (n + 1) _ c.rep.ρ c.rep.smooth c.rep.irr
  haveI : Nontrivial (TwJacquet c.rep.ρ (unipB k (Fin (n + 1))) (whitChar ψ (n + 1))) := hg
  exact Module.finrank_eq_of_rank_eq (le_antisymm hle (Cardinal.one_le_iff_pos.2 rank_pos))

theorem exists_nongeneric_subquotient : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    WhitRankIrr k → ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 →
    ∀ (x y : IrrGL (k := k)) (N : ℕ) (hd : ∑ a, (![x, y] a).1 = N), x.IsCusp → y.IsCusp →
      ¬ (prodIrr ![x, y] hd).IsIrreducible →
      ∃ τ : IrrRep (GL (Fin N) k), IsSubquotient τ.ρ (prodIrr ![x, y] hd) ∧ ¬ IsGenericFor ψ τ.ρ := by
  intro k _ _ _ _ hW ψ hc h1 x y N hd hx hy hn
  have hcusp : ∀ a, (![x, y] a).IsCusp := Fin.forall_fin_two.2 ⟨hx, hy⟩
  have hP := GlobalTheory.CompanionTheory.WhitRank.whitRankProd_of_heredity k (GlobalTheory.T.whittaker_heredity k) ψ hc h1 2 N ![x, y] hd
  have hrank : Module.finrank ℂ (TwJacquet (prodIrr ![x, y] hd) (unipB k (Fin N)) (whitChar ψ N)) = 1 :=
    hP.trans (Finset.prod_eq_one fun a _ => finrank_twJacquet_of_isCusp hW hc h1 (hcusp a))
  have hf : HasFiniteLength (prodIrr ![x, y] hd) :=
    GlobalTheory.ProdFiniteLength.multiProd_hasFiniteLength GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness k 2 N
      (fun a => (![x, y] a).1) (fun a => GlobalTheory.SplitRead.Irr.ofIrrRep (![x, y] a).2.rep) _
  have hs := isSmooth_prodIrr ![x, y] hd
  obtain ⟨τ, hτ, hsub⟩ := exists_subquotient_subsingleton (prodIrr ![x, y] hd) (unipB k (Fin N)) (whitChar ψ N) hs hf hn hrank
    fun S v hv => by
      let i : S.toRepresentation.IntertwiningMap (prodIrr ![x, y] hd) := ⟨S.toSubmodule.subtype, fun g => rfl⟩
      exact GlobalTheory.CompanionTheory.PRep.WhitExact.twKer_whitChar_reflect k ψ hc N S.toRepresentation (prodIrr ![x, y] hd)
        ((IsSubquotient.of_injective i Subtype.val_injective).isSmooth hs) hs S.toSubmodule.subtype
        Subtype.val_injective (fun g v => rfl) v hv
  exact ⟨τ, hτ, not_nontrivial_iff_subsingleton.2 hsub⟩

end Local

end GlobalTheory.CompanionTheory.CuspPair

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReducibleCuspidalPairNongenericSubquotientStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir Zc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reducible_cuspidal_pair_nongeneric_subquotient : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    WhitRankIrr k → ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 →
    ∀ (x y : IrrGL (k := k)) (N : ℕ) (hd : ∑ a, (![x, y] a).1 = N), x.IsCusp → y.IsCusp →
      ¬ (prodIrr ![x, y] hd).IsIrreducible →
      ∃ τ : IrrRep (GL (Fin N) k), IsSubquotient τ.ρ (prodIrr ![x, y] hd) ∧ ¬ IsGenericFor ψ τ.ρ := by
  first | exact @GlobalTheory.CompanionTheory.CuspPair.exists_nongeneric_subquotient | exact GlobalTheory.CompanionTheory.CuspPair.exists_nongeneric_subquotient | (intros; apply GlobalTheory.CompanionTheory.CuspPair.exists_nongeneric_subquotient <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableSchwartzAHaar
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableSchwartzAHaar
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.CompanionTheory.WSum
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WSum

theorem integrable_schwartzA_haar : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m n : ℕ) (μ : Measure (Mx D m n))
    [μ.IsAddHaarMeasure] (φ : Mx D m n → ℂ), φ ∈ schwartzA θ m n → Integrable φ μ := by
  intro D θ hθ m n μ _ φ hφ
  induction hφ using Submodule.span_induction with
  | mem φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    haveI : IsModuleTopology (Af D.host.F) (GlobalTheory.RegSch.IkSchwartz.AEf D) := ⟨rfl⟩
    haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
    haveI : IsTopologicalRing (GlobalTheory.RegSch.IkSchwartz.AEf D) := IsModuleTopology.isTopologicalRing (Af D.host.F) _
    haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele D.host.F
    haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele D.host.F
    haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField D.host.F
    obtain ⟨e0⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := D.host.F) (E := D.host.E) (Af D.host.F)
    haveI : LocallyCompactSpace (GlobalTheory.RegSch.IkSchwartz.AEf D) := e0.isClosedEmbedding.locallyCompactSpace
    haveI : SecondCountableTopology (GlobalTheory.RegSch.IkSchwartz.AEf D) := e0.secondCountableTopology
    haveI : T2Space (GlobalTheory.RegSch.IkSchwartz.AEf D) := e0.isEmbedding.t2Space
    letI : MeasurableSpace (Fin m → Fin n → GlobalTheory.RegSch.IkSchwartz.AEf D) := borel _
    haveI : BorelSpace (Fin m → Fin n → GlobalTheory.RegSch.IkSchwartz.AEf D) := ⟨rfl⟩
    haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
    haveI := (GlobalTheory.TowerRestrict.lattice_Mx D m n).1
    obtain ⟨e, he⟩ := GlobalTheory.RegSch.IkSchwartz.exists_split hθ m n
    let μr : Measure (D.what₂.Tau → Fin m → Fin n → ℂ) := Measure.addHaar
    let ν : Measure (Fin m → Fin n → GlobalTheory.RegSch.IkSchwartz.AEf D) := Measure.addHaar
    obtain ⟨c, hc⟩ := GlobalTheory.PartialIntegral.exists_integral_split e μ μr ν
    have h := (hc f g (f.integrable) (hg.1.continuous.integrable_of_hasCompactSupport hg.2)).1
    simpa only [he] using h
  | zero => exact integrable_zero _ _ _
  | add φ ψ _ _ h1 h2 => exact h1.add h2
  | smul c φ _ h => exact h.smul c

end GlobalTheory.CompanionTheory.WSum

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableSchwartzAHaarStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.CompanionTheory.WSum
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_of_mem_schwartzA : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m n : ℕ) (μ : Measure (Mx D m n)) [μ.IsAddHaarMeasure] (φ : Mx D m n → ℂ), φ ∈ schwartzA θ m n → Integrable φ μ := by
  first | exact @GlobalTheory.CompanionTheory.WSum.integrable_schwartzA_haar | exact GlobalTheory.CompanionTheory.WSum.integrable_schwartzA_haar | (intros; apply GlobalTheory.CompanionTheory.WSum.integrable_schwartzA_haar <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullbackSchwartzLinearIndependent
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullbackSchwartzLinearIndependent
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.PullSch

theorem exists_mul_eq_one_of_linearIndependent {K : Type} [Field K] {r n : ℕ} (c : Matrix (Fin r) (Fin n) K)
    (hc : LinearIndependent K c) : ∃ d : Matrix (Fin n) (Fin r) K, c * d = 1 := by
  have hinj : Function.Injective (Matrix.toLin' cᵀ) := by
    intro v w hvw
    have h1 : ∀ u : Fin r → K, Matrix.toLin' cᵀ u = ∑ i, u i • c i := by
      intro u
      funext j
      simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
    rw [h1, h1] at hvw
    have h2 := Fintype.linearIndependent_iff.1 hc (v - w) (by
      simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, hvw, sub_self])
    funext i
    exact sub_eq_zero.1 (h2 i)
  obtain ⟨h, hh⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' cᵀ) (LinearMap.ker_eq_bot.2 hinj)
  refine ⟨(LinearMap.toMatrix' h)ᵀ, ?_⟩
  have e : LinearMap.toMatrix' h * cᵀ = 1 := by
    rw [← LinearMap.toMatrix'_toLin' cᵀ, ← LinearMap.toMatrix'_comp, hh, LinearMap.toMatrix'_id]
  rw [← Matrix.transpose_transpose c, ← Matrix.transpose_mul, e, Matrix.transpose_one]

theorem mul_map_finPart (D : D7) {m r n : ℕ} (x : Mx D m r) (C : Mx D r n) (Dm : Mx D n r) (hCD : C * Dm = 1) :
    (x * C).map (finPart D) * Dm.map (finPart D) = x.map (finPart D) := by
  have e1 : x = x * C * Dm := by rw [Matrix.mul_assoc, hCD, Matrix.mul_one]
  conv_rhs => rw [e1]
  simp only [Matrix.map_mul]

theorem exists_finPart_section (D : D7) :
    ∃ s : Af D.host.F ⊗[D.host.F] D.host.E → AE D, Continuous s ∧ ∀ a, finPart D (s a) = a := by
  obtain ⟨e, he, -, hes⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  refine ⟨fun a => e.symm (0, a), hes.comp (continuous_const.prodMk continuous_id), fun a => ?_⟩
  have h := (he (e.symm (0, a))).2
  have h2 : (e (e.symm (0, a))).2 = a := by simp
  exact h.symm.trans h2

theorem continuous_lift_mul (D : D7) {m n r : ℕ} (Dm : Mx D n r) (s : Af D.host.F ⊗[D.host.F] D.host.E → AE D)
    (hs : Continuous s) :
    Continuous (fun z : Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) => (z.map s * Dm).map (finPart D)) :=
  ((continuous_id.matrix_map hs).matrix_mul continuous_const).matrix_map (GlobalTheory.Member.continuous_finPart D)

def mulR (D : D7) (m : ℕ) {r n : ℕ} (C : Mx D r n) : Mx D m r →+ Mx D m n where
  toFun y := y * C
  map_zero' := Matrix.zero_mul _
  map_add' a b := Matrix.add_mul a b C

theorem mulR_apply (D : D7) (m : ℕ) {r n : ℕ} (C : Mx D r n) (y : Mx D m r) : mulR D m C y = y * C := rfl

theorem continuous_mulR (D : D7) (m : ℕ) {r n : ℕ} (C : Mx D r n) : Continuous (mulR D m C) :=
  continuous_id.matrix_mul continuous_const

theorem injective_mulR (D : D7) (m : ℕ) {r n : ℕ} (C : Mx D r n) (Dm : Mx D n r) (hCD : C * Dm = 1) :
    Function.Injective (mulR D m C) := fun a b h => by
  have h' : a * C * Dm = b * C * Dm := congrArg (· * Dm) h
  rwa [Matrix.mul_assoc, Matrix.mul_assoc, hCD, Matrix.mul_one, Matrix.mul_one] at h'

theorem isRealParam_mulR_comp (D : D7) {m r n k : ℕ} (C : Mx D r n) (L : (Fin k → ℝ) →+ Mx D m r)
    (hL : GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsRealParam L) : GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsRealParam ((mulR D m C).comp L) := by
  refine ⟨(continuous_mulR D m C).comp hL.1, fun t => ?_⟩
  rw [AddMonoidHom.comp_apply, mulR_apply, Matrix.map_mul, hL.2 t, Matrix.zero_mul]

theorem injective_comp (D : D7) {m r n k : ℕ} (C : Mx D r n) (Dm : Mx D n r) (hCD : C * Dm = 1)
    (L : (Fin k → ℝ) →+ Mx D m r) (hL : Function.Injective L) : Function.Injective ((mulR D m C).comp L) := by
  intro a b h
  exact hL (injective_mulR D m C Dm hCD h)

theorem pullSchLI : PositivityTheory.GramSchwartzFunctions.PullSchLI := by
  intro D θ hθ m r n c hc φ hφ
  obtain ⟨d, hcd⟩ := exists_mul_eq_one_of_linearIndependent c hc
  rw [← GlobalTheory.SchwartzIff.isSchwartzBruhat_iff_mem_schwartzA D θ hθ] at hφ ⊢
  set C : Mx D r n := c.map (incA D) with hC
  set Dm : Mx D n r := d.map (incA D) with hD
  have hCD : C * Dm = 1 := by
    rw [hC, hD, ← Matrix.map_mul, hcd, Matrix.map_one _ (map_zero _) (map_one _)]
  have hpull : ∀ y, pull c φ y = φ (mulR D m C y) := fun y => rfl
  obtain ⟨hlev, hsupp, hsch⟩ := hφ
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨U, hUo, hU⟩ := hlev
    refine ⟨U.comap (mulR D m C), hUo.preimage (continuous_mulR D m C), fun u hu h0 x => ?_⟩
    have h0' : (mulR D m C u).map (infPart D) = 0 := by
      rw [mulR_apply, Matrix.map_mul, h0, Matrix.zero_mul]
    rw [hpull, hpull, map_add (f := _), hU _ hu h0']
  · obtain ⟨K, hK, hKs⟩ := hsupp
    obtain ⟨s, hs, hfs⟩ := exists_finPart_section D
    have h1 : ∀ y : Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E), (y.map s).map (finPart D) = y :=
      fun y => by
        ext i j
        simp [hfs]
    refine ⟨(fun z => (z.map s * Dm).map (finPart D)) '' K, hK.image (continuous_lift_mul D Dm s hs),
      fun x hx => ⟨(mulR D m C x).map (finPart D), hKs _ hx, ?_⟩⟩
    rw [mulR_apply]
    show ((((x * C).map (finPart D)).map s) * Dm).map (finPart D) = x.map (finPart D)
    rw [Matrix.map_mul (L := ((x * C).map (finPart D)).map s), h1]
    exact mul_map_finPart D x C Dm hCD
  · intro k L hL hLinj x
    obtain ⟨g, hg⟩ := hsch k ((mulR D m C).comp L) (isRealParam_mulR_comp D C L hL)
      (injective_comp D C Dm hCD L hLinj) (mulR D m C x)
    exact ⟨g, fun t => by rw [hg, hpull, map_add (f := _), AddMonoidHom.comp_apply]⟩

end GlobalTheory.CompanionTheory.PullSch
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullbackSchwartzLinearIndependentStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_schwartz_linear_independent : PositivityTheory.GramSchwartzFunctions.PullSchLI := by
  first | exact @GlobalTheory.CompanionTheory.PullSch.pullSchLI | exact GlobalTheory.CompanionTheory.PullSch.pullSchLI | (intros; apply GlobalTheory.CompanionTheory.PullSch.pullSchLI <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCurveIntersectionFormula
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCurveIntersectionFormula
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts

namespace GlobalTheory.CompanionTheory.MixZ

theorem curveInt : CurveInt := by
  intro Z _ q hq L M r hr
  refine ⟨fun σ => ?_, GlobalTheory.ArchDimZero.main ℤ Z q hq M L r hr⟩
  have := GlobalTheory.ArchDimZero.isProper hq
  have := GlobalTheory.ArchDimZero.finite_cxPts hq σ
  have h₁ : (L.φ σ).chernPart 0 1 = Measure.count := Measure.ext_iff_singleton.2 fun y => by
    rw [GlobalTheory.ArchDimZero.chernPart_singleton hq L σ 1 y, Measure.count_singleton]
    simp
  have h₂ : (L.φ σ).chernPart 0 (-1) = 0 := Measure.ext_iff_singleton.2 fun y => by
    rw [GlobalTheory.ArchDimZero.chernPart_singleton hq L σ (-1) y]
    simp
  refine ⟨?_, ?_⟩
  · rw [h₁]
    exact (Integrable.of_finite (μ := Measure.count) (f := logNorm (M.φ σ) r)).integrableOn
  · rw [h₂]
    exact (integrable_zero_measure : Integrable (logNorm (M.φ σ) r) 0).integrableOn

end GlobalTheory.CompanionTheory.MixZ
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCurveIntersectionFormulaStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixed_curve_intersection_formula : GlobalTheory.CompanionTheory.MixZ.CurveInt := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.curveInt | exact GlobalTheory.CompanionTheory.MixZ.curveInt | (intros; apply GlobalTheory.CompanionTheory.MixZ.curveInt <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCycleCodimensionOne
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCycleCodimensionOne
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace GlobalTheory.CompanionTheory.MixZ

theorem codimOne_holds : CodimOne := by
  intro X _ p D hD z hz
  let C : Closeds X := ⟨closure {z}, isClosed_closure⟩
  let I := Scheme.IdealSheafData.vanishingIdeal C
  haveI : IsReduced I.subscheme := GlobalTheory.ReducedSubgroup.isReduced_subscheme_vanishingIdeal C
  have hrange : Set.range I.subschemeι = closure {z} := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    rfl
  have hemb : Topology.IsEmbedding I.subschemeι := I.subschemeι.isClosedEmbedding.isEmbedding
  haveI : IrreducibleSpace I.subscheme := by
    have hs : IsIrreducible (Set.range I.subschemeι) := by
      rw [hrange]; exact isIrreducible_singleton.closure
    haveI := Subtype.irreducibleSpace hs
    have h2 := (IrreducibleSpace.isIrreducible_univ (Set.range I.subschemeι)).image
      hemb.toHomeomorph.symm hemb.toHomeomorph.symm.continuous.continuousOn
    rw [Set.image_univ_of_surjective hemb.toHomeomorph.symm.surjective] at h2
    exact (irreducibleSpace_def _).2 h2
  haveI : IsIntegral I.subscheme := isIntegral_of_irreducibleSpace_of_isReduced _
  have hgen : I.subschemeι (genericPoint I.subscheme) = z := by
    have h1 := (genericPoint_spec I.subscheme).image I.subschemeι.continuous
    rw [Set.image_univ, hrange, closure_closure] at h1
    exact h1.eq isGenericPoint_closure
  have key := GlobalTheory.PrimeDivDim.dim_eq_of_coheight_eq_one ℤ X p D hD I.subscheme I.subschemeι
    (by rw [hgen]; exact hz)
  calc topologicalKrullDim (closure ({z} : Set X))
      = topologicalKrullDim I.subscheme := GlobalTheory.topologicalKrullDim_eq_of_isEmbedding hemb hrange
    _ = D := key

end GlobalTheory.CompanionTheory.MixZ
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCycleCodimensionOneStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixed_cycle_codimension_one : GlobalTheory.CompanionTheory.MixZ.CodimOne := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.codimOne_holds | exact GlobalTheory.CompanionTheory.MixZ.codimOne_holds | (intros; apply GlobalTheory.CompanionTheory.MixZ.codimOne_holds <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BasicCharacterLocalComponent
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BasicCharacterLocalComponent
noncomputable section

namespace GlobalTheory.CompanionTheory.AdelicCharLocal

open NumberField IsDedekindDomain

theorem continuous_singleV (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (HeckeCharacterZeroLocus.SiegelWeilU.singleV F v) := by
  classical
  have hS : Filter.cofinite ≤ Filter.principal ({v}ᶜ : Set (HeightOneSpectrum (𝓞 F))) :=
    Filter.le_principal_iff.2 (Set.finite_singleton v).compl_mem_cofinite
  let f : HeckeCharacterZeroLocus.SiegelWeilU.Fv F v → RestrictedProduct (fun u : HeightOneSpectrum (𝓞 F) => u.adicCompletion F)
      (fun u => (u.adicCompletionIntegers F : Set (u.adicCompletion F))) (Filter.principal {v}ᶜ) :=
    fun a => ⟨Pi.single v a, fun u hu => by
      rw [Set.mem_setOf_eq, Pi.single_eq_of_ne hu]; exact zero_mem _⟩
  have hf : Continuous f := RestrictedProduct.continuous_rng_of_principal.2 (continuous_single v)
  exact (RestrictedProduct.continuous_inclusion hS).comp hf

theorem psiBasic : PositivityTheory.SiegelWeilFormula.Gunr.PsiBasic := by
  intro F _ _ ψ hψ v
  classical
  refine ⟨fun x y => ?_, ?_, ?_⟩
  · simp only [HeckeCharacterZeroLocus.SiegelWeilU.psiV, ← AddChar.map_add_eq_mul]
    congr 1
    refine Prod.ext (add_zero _).symm ?_
    exact Subtype.ext (Pi.single_add v x y)
  · have h0 : HeckeCharacterZeroLocus.SiegelWeilU.pairA F 0 (HeckeCharacterZeroLocus.SiegelWeilU.singleV F v 0) = 0 := by
      refine Prod.ext rfl ?_
      exact Subtype.ext (Pi.single_zero v)
    simp only [HeckeCharacterZeroLocus.SiegelWeilU.psiV, h0]
    exact AddChar.map_zero_eq_one ψ
  · exact hψ.1.comp (Continuous.prodMk continuous_const (continuous_singleV F v))

end GlobalTheory.CompanionTheory.AdelicCharLocal

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BasicCharacterLocalComponentStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.basic_character_unramified : PositivityTheory.SiegelWeilFormula.Gunr.PsiBasic := by
  first | exact @GlobalTheory.CompanionTheory.AdelicCharLocal.psiBasic | exact GlobalTheory.CompanionTheory.AdelicCharLocal.psiBasic | (intros; apply GlobalTheory.CompanionTheory.AdelicCharLocal.psiBasic <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeSpectralOfStrictExponent
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeSpectralOfStrictExponent
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.HeckeBound

theorem norm_lt_of_norm_mul_cpow_lt (q e : ℕ) (hq : 0 < q) (μ : ℂ)
    (h : ‖μ * (q : ℂ) ^ ((e : ℂ) / 2)‖ < 1) : ‖μ‖ < (q : ℝ) ^ (-((e : ℝ) / 2)) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hre : (((e : ℂ) / 2)).re = (e : ℝ) / 2 := by
    have : ((e : ℂ) / 2) = (((e : ℝ) / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.ofReal_re]
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos hq, hre] at h
  have hp : 0 < (q : ℝ) ^ ((e : ℝ) / 2) := Real.rpow_pos_of_pos hq' _
  rw [Real.rpow_neg hq'.le, ← one_div, lt_div_iff₀ hp]
  exact h

theorem heckeSpectral_of_maxExpStrict (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth π) (hi : π.IsIrreducible)
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hF : GlobalTheory.Published.StandardFunctorsFiniteLength)
    (hM : Zls.MaxExpStrict π) : Zls.HeckeSpectral π := by
  intro m hm j hj hjN T hT μ hμ
  have hq : 0 < Nat.card 𝓀[k] := Nat.card_pos
  by_cases hμ0 : μ = 0
  · subst hμ0
    simpa using Real.rpow_pos_of_pos (by exact_mod_cast hq : (0 : ℝ) < (Nat.card 𝓀[k] : ℝ)) _
  obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
  let d : Fin 2 → ℕ := ![j, N - j]
  have hd : ∑ a, d a = N := by
    simp only [d, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  have d0 : d 0 = j := rfl
  have d1 : d 1 = N - j := rfl
  have hd0 : 0 < d 0 := hj
  have hd1 : 0 < d 1 := by rw [d1]; omega
  have hT' : Zls.IsHeckeOp π m (Zls.diagPow k N (Zls.omegaVec N (d 0))) T := hT
  have hTw : T w = μ • w := hw.apply_eq_smul
  have hmk : (Submodule.Quotient.mk (w : V) : Jacquet π (unipRad k (stdBlocks d hd))) ≠ 0 := by
    intro h0
    obtain ⟨r, hr⟩ := GlobalTheory.T.hecke_operator_jacquet_eigen_left k N V π hs m hm d hd hd0 hd1 T hT' w h0
    rw [hw.pow_apply r] at hr
    exact (smul_ne_zero (pow_ne_zero r hμ0) hw.2) hr
  have hjac := GlobalTheory.T.hecke_operator_jacquet_eigen_right k N V π hs m hm d hd hd0 hd1 T hT' w
  have heig : (Submodule.Quotient.mk (π (Zls.diagPow k N (Zls.omegaVec N (d 0))) (w : V)) :
      Jacquet π (unipRad k (stdBlocks d hd))) =
      μ • (Submodule.Quotient.mk (w : V) : Jacquet π (unipRad k (stdBlocks d hd))) := by
    rw [← hjac, hTw]
    rfl
  obtain ⟨x, hx, hxd, hjm, hs0, c1, hs1⟩ :=
    GlobalTheory.T.jacquet_quotient_eigenvector k N V π hs hi hA hF d hd hd0 hd1 μ w hmk heig
  have hpos : ∀ a, 0 < (x a).1 := by
    intro a
    rw [hxd a]
    fin_cases a
    · exact hd0
    · exact hd1
  have hE := hM x hx hpos hjm
  have hc := (hE (Zls.unifU k) (GlobalTheory.T.uniformizer_pow_tendsto_zero k)
    ![μ * (Nat.card 𝓀[k] : ℂ) ^ (((d 0 * d 1 : ℕ) : ℂ) / 2), c1]
    (by
      intro i
      fin_cases i
      · exact hs0
      · exact hs1)).1 0 (by simp)
  have hfil : Finset.univ.filter (· ≤ (0 : Fin 2)) = {0} := by decide
  rw [hfil, Finset.prod_singleton] at hc
  have := norm_lt_of_norm_mul_cpow_lt (Nat.card 𝓀[k]) (d 0 * d 1) hq μ hc
  simpa [d0, d1] using this

end GlobalTheory.CompanionTheory.HeckeBound
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeSpectralOfStrictExponentStatement
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_spectral_of_strict_exponent : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → π.IsIrreducible → GlobalTheory.Published.IrreducibleAdmissibleGL → GlobalTheory.Published.StandardFunctorsFiniteLength → Zls.MaxExpStrict π → Zls.HeckeSpectral π := by
  first | exact @GlobalTheory.CompanionTheory.HeckeBound.heckeSpectral_of_maxExpStrict | exact GlobalTheory.CompanionTheory.HeckeBound.heckeSpectral_of_maxExpStrict | (intros; apply GlobalTheory.CompanionTheory.HeckeBound.heckeSpectral_of_maxExpStrict <;> assumption)
end
end
