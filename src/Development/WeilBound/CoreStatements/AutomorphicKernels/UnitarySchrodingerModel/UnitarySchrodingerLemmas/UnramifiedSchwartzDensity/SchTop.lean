module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.LowRankSiegelDensities.Reduce
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanSection

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DensityIntegralStatement
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DensityIntegral
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.DensInt

theorem exists_cutoff (V : Type) [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] :
    ∃ χ : ℕ → V → ℝ, (∀ k, Continuous (χ k)) ∧ (∀ k, HasCompactSupport (χ k)) ∧
      (∀ k x, 0 ≤ χ k x ∧ χ k x ≤ 1) ∧ ∀ x, ∀ᶠ k in Filter.atTop, χ k x = 1 := by
  have h : ∀ k : ℕ, ∃ f : C(V, ℝ), Set.EqOn f 1 (compactCovering V k) ∧ Set.EqOn f 0 (∅ : Set V) ∧
      HasCompactSupport f ∧ ∀ x, f x ∈ Set.Icc (0 : ℝ) 1 := fun k =>
    exists_continuous_one_zero_of_isCompact (isCompact_compactCovering V k) isClosed_empty
      (Set.disjoint_empty _)
  choose f h1 _ h3 h4 using h
  refine ⟨fun k => f k, fun k => (f k).continuous, h3, fun k x => h4 k x, fun x => ?_⟩
  obtain ⟨k₀, hk₀⟩ := exists_mem_compactCovering x
  filter_upwards [Filter.eventually_ge_atTop k₀] with k hk
  exact h1 k (compactCovering_subset V hk hk₀)

theorem density_limit {V X Y : Type} [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V]
    [T2Space V] [MeasurableSpace V] [BorelSpace V] [TopologicalSpace X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] (μ : Measure V) (ν : Measure X) [IsFiniteMeasureOnCompacts ν] (f : V → Y) (ι : X → Y)
    (B : Set X) (m : X → Measure V)
    (H : ∀ ψ : V → ℂ, Continuous ψ → HasCompactSupport ψ →
      HeckeCharacterZeroLocus.SiegelWeilU.IsContDensityOn μ f ι ν B ψ (fun S => ∫ x, ψ x ∂(m S)) ∧ ∀ S, Integrable ψ (m S))
    (φ : V → ℂ) (hφc : Continuous φ) (hφ : Integrable φ μ) (hφS : ∀ S ∈ B, Integrable φ (m S))
    (hD : ContinuousOn (fun S => ∫ x, ‖φ x‖ ∂(m S)) B) (K : Set X) (hK : IsCompact K) (hKB : K ⊆ B) :
    ∫ v in f ⁻¹' (ι '' K), φ v ∂μ = ∫ b in K, (∫ x, φ x ∂(m b)) ∂ν := by
  obtain ⟨χ, hχc, hχs, hχb, hχ1⟩ := exists_cutoff V
  set ψ : ℕ → V → ℂ := fun k x => φ x * (χ k x : ℂ) with hψ
  have hψc : ∀ k, Continuous (ψ k) := fun k =>
    hφc.mul (Complex.continuous_ofReal.comp (hχc k))
  have hψs : ∀ k, HasCompactSupport (ψ k) := fun k => by
    have : HasCompactSupport (fun x => (χ k x : ℂ)) := (hχs k).comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
    exact this.mul_left
  have hψn : ∀ k x, ‖ψ k x‖ ≤ ‖φ x‖ := fun k x => by
    simp only [hψ, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hχb k x).1]
    exact mul_le_of_le_one_right (norm_nonneg _) (hχb k x).2
  have hψl : ∀ x, Filter.Tendsto (fun k => ψ k x) Filter.atTop (𝓝 (φ x)) := fun x => by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hχ1 x] with k hk
    simp [hψ, hk]
  have hmeas : ∀ k (ρ : Measure V), AEStronglyMeasurable (ψ k) ρ := fun k ρ =>
    (hψc k).aestronglyMeasurable

  have hL : Filter.Tendsto (fun k => ∫ v in f ⁻¹' (ι '' K), ψ k v ∂μ) Filter.atTop
      (𝓝 (∫ v in f ⁻¹' (ι '' K), φ v ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun x => ‖φ x‖) (fun k => hmeas k _) hφ.norm.integrableOn
      (fun k => Filter.Eventually.of_forall (hψn k)) (Filter.Eventually.of_forall hψl)

  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ S ∈ K, ‖∫ x, ‖φ x‖ ∂(m S)‖ ≤ C :=
    hK.exists_bound_of_continuousOn (hD.mono hKB)
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hR : Filter.Tendsto (fun k => ∫ b in K, (∫ x, ψ k x ∂(m b)) ∂ν) Filter.atTop
      (𝓝 (∫ b in K, (∫ x, φ x ∂(m b)) ∂ν)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => C) (fun k => ?_) ?_ (fun k => ?_) ?_
    · exact ((H _ (hψc k) (hψs k)).1.1.mono hKB).aestronglyMeasurable hKm
    · haveI : IsFiniteMeasure (ν.restrict K) := ⟨by simpa using hK.measure_lt_top (μ := ν)⟩
      exact integrable_const _
    · refine (ae_restrict_iff' hKm).2 (Filter.Eventually.of_forall fun S hS => ?_)
      calc ‖∫ x, ψ k x ∂(m S)‖ ≤ ∫ x, ‖ψ k x‖ ∂(m S) := norm_integral_le_integral_norm _
        _ ≤ ∫ x, ‖φ x‖ ∂(m S) := integral_mono ((H _ (hψc k) (hψs k)).2 S).norm (hφS S (hKB hS)).norm (hψn k)
        _ ≤ ‖∫ x, ‖φ x‖ ∂(m S)‖ := Real.le_norm_self _
        _ ≤ C := hC S hS
    · refine (ae_restrict_iff' hKm).2 (Filter.Eventually.of_forall fun S hS => ?_)
      exact tendsto_integral_of_dominated_convergence (fun x => ‖φ x‖) (fun k => hmeas k _)
        (hφS S (hKB hS)).norm (fun k => Filter.Eventually.of_forall (hψn k))
        (Filter.Eventually.of_forall hψl)
  refine tendsto_nhds_unique hL (hR.congr fun k => ?_)
  exact ((H _ (hψc k) (hψs k)).1.2 K hK hKB).symm


set_option maxHeartbeats 1000000 in
theorem density_identity_inf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n : ℕ) (μ : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (ν : Measure (HermR (Ainf F) σ n)) (m : HermR (Ainf F) σ n → Measure (Fin n → Fin M → Ainf F ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFib (Ainf F) σ J n μ ν m → ∀ φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ, Continuous φ → Integrable φ μ → (∀ S : HermR (Ainf F) σ n, IsUnit (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det → Integrable φ (m S)) → ContinuousOn (fun S => ∫ X, ‖φ X‖ ∂(m S)) {S : HermR (Ainf F) σ n | IsUnit (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det} → ∀ K : Set (HermR (Ainf F) σ n), IsCompact K → K ⊆ {S | IsUnit (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det} → ∫ X in gramR (Ainf F) σ J ⁻¹' (Subtype.val '' K), φ X ∂μ = ∫ S in K, (∫ X, φ X ∂(m S)) ∂ν := by
  intro F E _ _ _ _ _ σ hσ M J hJ n μ ν m hμ hν hfib φ hφc hφ hφS hD K hK hKB
  have hR : IsLocR (Ainf F) := GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hσ.1
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨hTR, hLC, hSC, hT2, -, -, -, -⟩ := id hR
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  obtain ⟨iTR, iLC, iSC, iT2, -, -, -, iB, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Ainf F)
  haveI := iB n M
  haveI := iTR
  haveI := iLC
  haveI := iSC
  haveI := iT2
  obtain ⟨jLC, jSC, jT2, jB, -⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hσ (Ainf F) n
  haveI := jLC
  haveI := jSC
  haveI := jT2
  haveI := jB
  exact density_limit μ ν (gramR (Ainf F) σ J) Subtype.val _ m
    (fun ψ h1 h2 => GlobalTheory.CompanionTheory.SW.GramDensity.isContDensityOn_gram F E σ hσ M J hJ (Ainf F) hR n μ ν m hμ hν hfib ψ h1 h2)
    φ hφc hφ hφS hD K hK hKB

end GlobalTheory.CompanionTheory.SW.DensInt
end

noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.density_integral : PositivityTheory.PfSWUS.SchInf.DensInt := by
  first | exact @GlobalTheory.CompanionTheory.SW.DensInt.density_identity_inf | exact GlobalTheory.CompanionTheory.SW.DensInt.density_identity_inf | (intros; apply GlobalTheory.CompanionTheory.SW.DensInt.density_identity_inf <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanScaling
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsContinuousScale
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.HaarScale

variable {V P : Type*} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [LocallyCompactSpace V] [T2Space V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
  [TopologicalSpace P] [LocallyCompactSpace P]

def addEquivOf (T Ti : V → V) (hadd : ∀ x y, T (x + y) = T x + T y)
    (hl : ∀ x, Ti (T x) = x) (hr : ∀ x, T (Ti x) = x) : V ≃+ V where
  toFun := T
  invFun := Ti
  left_inv := hl
  right_inv := hr
  map_add' := hadd

theorem map_eq_smul (μ : Measure V) [μ.IsAddHaarMeasure] (T Ti : V → V) (hT : Continuous T)
    (hTi : Continuous Ti) (hadd : ∀ x y, T (x + y) = T x + T y)
    (hl : ∀ x, Ti (T x) = x) (hr : ∀ x, T (Ti x) = x) :
    ∃ c : ℝ≥0, μ.map T = c • μ := by
  haveI : (μ.map T).IsAddHaarMeasure :=
    (addEquivOf T Ti hadd hl hr).isAddHaarMeasure_map μ hT hTi
  exact ⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩

theorem exists_continuous_scale (μ : Measure V) [μ.IsAddHaarMeasure] (T Ti : P → V → V)
    (hT : Continuous (Function.uncurry T)) (hTi : Continuous (Function.uncurry Ti))
    (hadd : ∀ p x y, T p (x + y) = T p x + T p y)
    (hl : ∀ p x, Ti p (T p x) = x) (hr : ∀ p x, T p (Ti p x) = x) :
    ∃ A : P → ℝ≥0, Continuous A ∧ ∀ p, μ.map (T p) = A p • μ := by
  have hTp : ∀ p, Continuous (T p) := fun p => hT.comp (Continuous.prodMk_right p)
  have hTip : ∀ p, Continuous (Ti p) := fun p => hTi.comp (Continuous.prodMk_right p)
  choose A hform using fun p =>
    map_eq_smul μ (T p) (Ti p) (hTp p) (hTip p) (hadd p) (hl p) (hr p)
  refine ⟨A, ?_, hform⟩
  obtain ⟨f, hf1, -, hfc, hf01⟩ := exists_continuous_one_zero_of_isCompact (X := V)
    (s := {0}) (t := ∅) isCompact_singleton isClosed_empty (by simp)
  have hf0 : (0 : V → ℝ) ≤ f := fun x => (hf01 x).1
  have hpos : 0 < ∫ x, f x ∂μ := by
    refine f.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hfc hf0 (x := 0) ?_
    rw [hf1 (Set.mem_singleton 0)]; exact one_ne_zero
  have hval : ∀ p, (A p : ℝ) = (∫ x, f (T p x) ∂μ) / ∫ x, f x ∂μ := by
    intro p
    have h1 : ∫ x, f x ∂(μ.map (T p)) = ∫ x, f (T p x) ∂μ :=
      integral_map (hTp p).aemeasurable f.continuous.aestronglyMeasurable
    have h2 : ∫ x, f x ∂(μ.map (T p)) = (A p : ℝ) * ∫ x, f x ∂μ := by
      conv_lhs => rw [hform p]
      rw [integral_smul_nnreal_measure]
      simp [NNReal.smul_def]
    rw [eq_div_iff hpos.ne', ← h2, h1]
  refine continuous_induced_rng.2 ?_
  have hI : Continuous fun p => ∫ x, f (T p x) ∂μ := by
    refine continuous_iff_continuousAt.2 fun p₀ => ?_
    obtain ⟨C, hCc, hCn⟩ := exists_compact_mem_nhds p₀
    have hk : IsCompact (Function.uncurry Ti '' (C ×ˢ tsupport f)) :=
      (hCc.prod hfc).image hTi
    have hcont : ContinuousOn (fun p x => f (T p x)).uncurry (C ×ˢ Set.univ) :=
      (f.continuous.comp hT).continuousOn
    refine (continuousOn_integral_of_compact_support hk hcont ?_).continuousAt hCn
    intro p x hp hx
    by_contra hne
    exact hx ⟨(p, T p x), ⟨hp, subset_tsupport _ hne⟩, hl p x⟩
  exact (hI.div_const _).congr fun p => (hval p).symm

end GlobalTheory.CompanionTheory.SW.HaarScale

namespace GlobalTheory.CompanionTheory.SW.HaarScale

section Mat

variable {K : Type*} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {n : ℕ}

theorem continuous_inv_unitMat (hu : IsOpenEmbedding (Units.val : Kˣ → K)) :
    Continuous fun g : {g : Matrix (Fin n) (Fin n) K // IsUnit g.det} => (g.1)⁻¹ := by
  have hdet : Continuous fun g : {g : Matrix (Fin n) (Fin n) K // IsUnit g.det} => g.1.det :=
    Continuous.matrix_det continuous_subtype_val
  have hunit : Continuous fun g : {g : Matrix (Fin n) (Fin n) K // IsUnit g.det} => g.2.unit :=
    hu.isEmbedding.continuous_iff.2 (by simpa [Function.comp_def] using hdet)
  have hinv : Continuous fun g : {g : Matrix (Fin n) (Fin n) K // IsUnit g.det} =>
      ((g.2.unit⁻¹ : Kˣ) : K) := Units.continuous_val.comp hunit.inv
  have hadj : Continuous fun g : {g : Matrix (Fin n) (Fin n) K // IsUnit g.det} => g.1.adjugate :=
    Continuous.matrix_adjugate continuous_subtype_val
  refine (hinv.smul hadj).congr fun g => ?_
  have hr : Ring.inverse g.1.det = ((g.2.unit⁻¹ : Kˣ) : K) := by
    have h := Ring.inverse_unit g.2.unit
    rwa [IsUnit.unit_spec] at h
  rw [Matrix.inv_def, hr]
  rfl

theorem locallyCompact_unitMat [LocallyCompactSpace K] (hu : IsOpenEmbedding (Units.val : Kˣ → K)) :
    LocallyCompactSpace {g : Matrix (Fin n) (Fin n) K // IsUnit g.det} := by
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) K) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → K))
  have hset : {g : Matrix (Fin n) (Fin n) K | IsUnit g.det} =
      (fun g : Matrix (Fin n) (Fin n) K => g.det) ⁻¹' Set.range (Units.val : Kˣ → K) := by
    ext g; simp [IsUnit]
  have hopen : IsOpen {g : Matrix (Fin n) (Fin n) K | IsUnit g.det} := by
    rw [hset]
    exact hu.isOpen_range.preimage (Continuous.matrix_det continuous_id)
  exact hopen.isOpenEmbedding_subtypeVal.locallyCompactSpace

theorem continuousOn_extend (A : {g : Matrix (Fin n) (Fin n) K // IsUnit g.det} → ℝ≥0)
    (hA : Continuous A) [∀ g : Matrix (Fin n) (Fin n) K, Decidable (IsUnit g.det)] :
    ContinuousOn (fun g : Matrix (Fin n) (Fin n) K => if h : IsUnit g.det then A ⟨g, h⟩ else 0)
      {g | IsUnit g.det} := by
  rw [continuousOn_iff_continuous_restrict]
  refine hA.congr fun g => ?_
  simp [Set.restrict, g.2]

end Mat

section Tup

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

theorem rmul_rmul {M n : ℕ} (X : Fin n → Fin M → R ⊗[F] E) (g h : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    rmul R (rmul R X g) h = rmul R X (g * h) := by
  funext a i
  simp only [rmul, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring

theorem rmul_one {M n : ℕ} (X : Fin n → Fin M → R ⊗[F] E) : rmul R X 1 = X := by
  funext a i
  simp [rmul, Matrix.one_apply]

theorem rmul_add {M n : ℕ} (X Y : Fin n → Fin M → R ⊗[F] E) (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    rmul R (X + Y) g = rmul R X g + rmul R Y g := by
  funext a i
  simp [rmul, add_mul, Finset.sum_add_distrib]

end Tup

section Herm

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

def conjT (σ : E →ₐ[F] E) {n : ℕ} (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    Matrix (Fin n) (Fin n) (R ⊗[F] E) :=
  (g.map (sigR R σ))ᵀ

theorem conjT_mul (σ : E →ₐ[F] E) {n : ℕ} (g h : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    conjT R σ (g * h) = conjT R σ h * conjT R σ g := by
  simp only [conjT, Matrix.map_mul, Matrix.transpose_mul]

theorem conjT_one (σ : E →ₐ[F] E) {n : ℕ} :
    conjT R σ (1 : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = 1 := by
  ext a b
  by_cases h : a = b
  · subst h; simp [conjT]
  · simp [conjT, Matrix.one_apply, h, Ne.symm h]

theorem mem_hermR_iff (σ : E →ₐ[F] E) {n : ℕ} (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    S ∈ HermR R σ n ↔ conjT R σ S = S := by
  constructor
  · intro h; ext a b; exact h a b
  · intro h a b
    exact congrFun (congrFun h a) b

theorem conjT_conjT {σ : E →ₐ[F] E} (hs : ∀ x, σ (σ x) = x) {n : ℕ}
    (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) : conjT R σ (conjT R σ g) = g := by
  ext a b
  simp [conjT, GlobalTheory.CompanionTheory.SW.HermTop.sigR_sigR R hs]

theorem conj_mem {σ : E →ₐ[F] E} (hs : ∀ x, σ (σ x) = x) {n : ℕ}
    (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) (S : HermR R σ n) :
    conjT R σ g * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * g ∈ HermR R σ n := by
  rw [mem_hermR_iff, conjT_mul, conjT_mul, conjT_conjT R hs, (mem_hermR_iff R σ _).1 S.2, Matrix.mul_assoc]

end Herm

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_scale_tuples (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (hR : IsLocR R) (n M : ℕ)
    (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (hμ : μ.IsAddHaarMeasure) :
    ∃ A : Matrix (Fin n) (Fin n) (R ⊗[F] E) → ℝ≥0, ContinuousOn A {g | IsUnit g.det} ∧
      ∀ g, IsUnit g.det → μ.map (fun X => rmul R X g) = A g • μ := by
  classical
  obtain ⟨hTR, hLC, hSC, hT2, -, -, -, -⟩ := id hR
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  have hu : IsOpenEmbedding (Units.val : (R ⊗[F] E)ˣ → R ⊗[F] E) := GlobalTheory.T.units_open_embedding_local_tensor F E σ hσ R hR
  obtain ⟨iTR, iLC, iSC, iT2, -, -, -, iB, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ R
  haveI := iB n M
  haveI := iTR
  haveI := iLC
  haveI := iSC
  haveI := iT2
  haveI := locallyCompact_unitMat (n := n) hu
  have hcont : ∀ {Q : Type} [TopologicalSpace Q] (G : Q → Matrix (Fin n) (Fin n) (R ⊗[F] E)),
      Continuous G → Continuous (Function.uncurry fun (q : Q) (X : Fin n → Fin M → R ⊗[F] E) => rmul R X (G q)) := by
    intro Q _ G hG
    refine continuous_pi fun a => continuous_pi fun i => ?_
    simp only [Function.uncurry_def, rmul]
    refine continuous_finsetSum _ fun c _ => ?_
    have h1 : Continuous fun p : Q × (Fin n → Fin M → R ⊗[F] E) => p.2 c i :=
      (continuous_apply_apply c i).comp continuous_snd
    have h2 : Continuous fun p : Q × (Fin n → Fin M → R ⊗[F] E) => G p.1 c a :=
      (hG.comp continuous_fst).matrix_elem c a
    exact h1.mul h2
  obtain ⟨A, hA, hform⟩ := exists_continuous_scale μ
    (P := {g : Matrix (Fin n) (Fin n) (R ⊗[F] E) // IsUnit g.det})
    (fun g X => rmul R X g.1) (fun g X => rmul R X (g.1)⁻¹)
    (hcont _ continuous_subtype_val) (hcont _ (continuous_inv_unitMat hu))
    (fun g X Y => rmul_add R X Y g.1)
    (fun g X => by rw [rmul_rmul, Matrix.mul_nonsing_inv _ g.2, rmul_one])
    (fun g X => by rw [rmul_rmul, Matrix.nonsing_inv_mul _ g.2, rmul_one])
  refine ⟨_, continuousOn_extend A hA, fun g hg => ?_⟩
  simpa [hg] using hform ⟨g, hg⟩

theorem exists_scale_herm (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (hR : IsLocR R) (n : ℕ)
    (ν : Measure (HermR R σ n)) (hν : ν.IsAddHaarMeasure) :
    ∃ B : Matrix (Fin n) (Fin n) (R ⊗[F] E) → ℝ≥0, ContinuousOn B {g | IsUnit g.det} ∧
      ∀ g, IsUnit g.det → ∀ τ : HermR R σ n → HermR R σ n,
        (∀ S, (τ S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) =
          conjT R σ g * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * g) → ν.map τ = B g • ν := by
  classical
  obtain ⟨hTR, hLC, hSC, hT2, -, -, -, -⟩ := id hR
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  have hu : IsOpenEmbedding (Units.val : (R ⊗[F] E)ˣ → R ⊗[F] E) := GlobalTheory.T.units_open_embedding_local_tensor F E σ hσ R hR
  obtain ⟨iTR, iLC, iSC, iT2, hsig, -, -, -, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ R
  haveI := iTR
  haveI := iLC
  haveI := iSC
  haveI := iT2
  obtain ⟨jLC, jSC, jT2, jB, -⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hσ R n
  haveI := jLC
  haveI := jSC
  haveI := jT2
  haveI := jB
  haveI := locallyCompact_unitMat (n := n) hu
  have hs : ∀ x, σ (σ x) = x := GlobalTheory.CompanionTheory.SW.HermTop.sigma_sigma hσ
  have hcont : ∀ {Q : Type} [TopologicalSpace Q] (G : Q → Matrix (Fin n) (Fin n) (R ⊗[F] E)),
      Continuous G → Continuous (Function.uncurry fun (q : Q) (S : HermR R σ n) =>
        (⟨conjT R σ (G q) * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * G q, conj_mem R hs _ S⟩ : HermR R σ n)) := by
    intro Q _ G hG
    refine Continuous.subtype_mk ?_ _
    have h1 : Continuous fun p : Q × HermR R σ n => conjT R σ (G p.1) :=
      ((hG.comp continuous_fst).matrix_map hsig).matrix_transpose
    have h2 : Continuous fun p : Q × HermR R σ n => (p.2 : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :=
      continuous_subtype_val.comp continuous_snd
    exact (h1.matrix_mul h2).matrix_mul (hG.comp continuous_fst)
  have hinvl : ∀ g h : Matrix (Fin n) (Fin n) (R ⊗[F] E), g * h = 1 → ∀ S : Matrix (Fin n) (Fin n) (R ⊗[F] E),
      conjT R σ h * (conjT R σ g * S * g) * h = S := by
    intro g h hgh S
    have h1 : conjT R σ h * conjT R σ g = 1 := by rw [← conjT_mul, hgh, conjT_one]
    calc conjT R σ h * (conjT R σ g * S * g) * h
        = (conjT R σ h * conjT R σ g) * S * (g * h) := by simp only [Matrix.mul_assoc]
      _ = S := by rw [h1, hgh, Matrix.one_mul, Matrix.mul_one]
  obtain ⟨B, hB, hform⟩ := exists_continuous_scale ν
    (P := {g : Matrix (Fin n) (Fin n) (R ⊗[F] E) // IsUnit g.det})
    (fun g S => ⟨conjT R σ g.1 * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * g.1, conj_mem R hs _ S⟩)
    (fun g S => ⟨conjT R σ (g.1)⁻¹ * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * (g.1)⁻¹, conj_mem R hs _ S⟩)
    (hcont _ continuous_subtype_val) (hcont _ (continuous_inv_unitMat hu))
    (fun g S T => Subtype.ext (by simp [Matrix.mul_add, Matrix.add_mul]))
    (fun g S => Subtype.ext (hinvl _ _ (Matrix.mul_nonsing_inv _ g.2) _))
    (fun g S => Subtype.ext (hinvl _ _ (Matrix.nonsing_inv_mul _ g.2) _))
  refine ⟨_, continuousOn_extend B hB, fun g hg τ hτ => ?_⟩
  have hτ' : τ = fun S => ⟨conjT R σ g * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * g, conj_mem R hs _ S⟩ :=
    funext fun S => Subtype.ext (hτ S)
  rw [hτ']
  simpa [hg] using hform ⟨g, hg⟩

end Main

end GlobalTheory.CompanionTheory.SW.HaarScale
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanScaling
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.HaarScale

theorem scaleInf : PositivityTheory.PfSWUS.SchInf.ScaleInf := by
  intro F E _ _ _ _ _ σ hσ n M μ ν hμ hν
  classical
  have hR : IsLocR (Ainf F) := GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hσ.1
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨A, hA, hAf⟩ := exists_scale_tuples σ hσ (Ainf F) hR n M μ hμ
  obtain ⟨B, hB, hBf⟩ := exists_scale_herm σ hσ (Ainf F) hR n ν hν
  obtain ⟨hTR, hLC, hSC, hT2, -, -, -, -⟩ := id hR
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  obtain ⟨iTR, iLC, iSC, iT2, hsig, -, -, iB, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Ainf F)
  haveI := iB n M
  haveI := iTR
  haveI := iT2
  obtain ⟨jLC, jSC, jT2, jB, -⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hσ (Ainf F) n
  haveI := jB
  haveI := jT2
  have hs : ∀ x, σ (σ x) = x := GlobalTheory.CompanionTheory.SW.HermTop.sigma_sigma hσ
  refine ⟨A, B, hA, hB, fun g hg => ?_⟩
  have hTc : Continuous fun X : Fin n → Fin M → Ainf F ⊗[F] E => rmul (Ainf F) X g := by
    refine continuous_pi fun a => continuous_pi fun i => ?_
    simp only [rmul]
    exact continuous_finsetSum _ fun c _ => ((continuous_apply_apply c i).mul continuous_const)
  have hTm : Measurable fun X : Fin n → Fin M → Ainf F ⊗[F] E => rmul (Ainf F) X g := hTc.measurable
  let τ₀ : HermR (Ainf F) σ n → HermR (Ainf F) σ n := fun S =>
    ⟨conjT (Ainf F) σ g * (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) * g, conj_mem (Ainf F) hs _ S⟩
  have hτ₀c : Continuous τ₀ := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const
  have hcT : ∀ S : HermR (Ainf F) σ n, ((τ₀ S : HermR (Ainf F) σ n) : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) =
      cT (sigR (Ainf F) σ) g * (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) * g := fun S => rfl
  have hB0 := hBf g hg τ₀ (fun S => rfl)
  refine ⟨?_, ?_, hAf g hg, fun τ hτ => ?_⟩
  · intro h0
    have h1 := hAf g hg
    rw [h0, zero_smul, Measure.map_eq_zero_iff hTm.aemeasurable] at h1
    exact (Measure.IsAddHaarMeasure.toIsOpenPosMeasure (μ := μ)).open_pos Set.univ isOpen_univ Set.univ_nonempty
      (by rw [h1]; simp)
  · intro h0
    rw [h0, zero_smul, Measure.map_eq_zero_iff hτ₀c.measurable.aemeasurable] at hB0
    exact (Measure.IsAddHaarMeasure.toIsOpenPosMeasure (μ := ν)).open_pos Set.univ isOpen_univ Set.univ_nonempty
      (by rw [hB0]; simp)
  · have : τ = τ₀ := funext fun S => Subtype.ext ((hτ S).trans (hcT S).symm)
    rw [this]
    exact hB0

end GlobalTheory.CompanionTheory.SW.HaarScale
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanScalingStatement
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_scaling : PositivityTheory.PfSWUS.SchInf.ScaleInf := by
  first | exact @GlobalTheory.CompanionTheory.SW.HaarScale.scaleInf | exact GlobalTheory.CompanionTheory.SW.HaarScale.scaleInf | (intros; apply GlobalTheory.CompanionTheory.SW.HaarScale.scaleInf <;> assumption)
end
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanFamilyContinuity
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanFamilyContinuity
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace GlobalTheory.CompanionTheory.PushFam

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable [MeasurableSpace E] [BorelSpace E]

lemma decay_comp_of_norm_le (g : E → ℂ) (k : ℕ) (C : ℝ)
    (hC : ∀ y, ‖g y‖ ≤ C * (1 + ‖y‖) ^ (-(k : ℝ))) (K : ℝ) :
    ∃ C' : ℝ, ∀ x y : E, ‖y‖ ≤ K * ‖x‖ → ‖g x‖ ≤ C' * (1 + ‖y‖) ^ (-(k : ℝ)) := by
  refine ⟨max C 0 * (1 + |K|) ^ k, fun x y hxy => ?_⟩
  have hx : 0 ≤ ‖x‖ := norm_nonneg _
  have h2 : 1 + ‖y‖ ≤ (1 + |K|) * (1 + ‖x‖) := by
    have h3 : K * ‖x‖ ≤ |K| * ‖x‖ := mul_le_mul_of_nonneg_right (le_abs_self K) hx
    have h4 : 0 ≤ |K| := abs_nonneg K
    nlinarith
  have h3 : (1 + ‖x‖) ^ (-(k : ℝ)) ≤ (1 + |K|) ^ k * (1 + ‖y‖) ^ (-(k : ℝ)) := by
    rw [Real.rpow_neg (by positivity), Real.rpow_neg (by positivity), Real.rpow_natCast,
      Real.rpow_natCast, ← div_eq_mul_inv, inv_eq_one_div,
      div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    calc (1 + ‖y‖) ^ k ≤ ((1 + |K|) * (1 + ‖x‖)) ^ k := pow_le_pow_left₀ (by positivity) h2 k
      _ = (1 + |K|) ^ k * (1 + ‖x‖) ^ k := mul_pow _ _ _
  calc ‖g x‖ ≤ C * (1 + ‖x‖) ^ (-(k : ℝ)) := hC x
    _ ≤ max C 0 * (1 + ‖x‖) ^ (-(k : ℝ)) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ ≤ max C 0 * ((1 + |K|) ^ k * (1 + ‖y‖) ^ (-(k : ℝ))) :=
        mul_le_mul_of_nonneg_left h3 (le_max_right _ _)
    _ = max C 0 * (1 + |K|) ^ k * (1 + ‖y‖) ^ (-(k : ℝ)) := by ring

theorem integrable_continuousAt_clm_comp (m : Measure E) (k : ℕ)
    (hW : Integrable (fun y : E => (1 + ‖y‖) ^ (-(k : ℝ))) m)
    (g : E → ℂ) (hg : Continuous g) (C : ℝ) (hC : ∀ y, ‖g y‖ ≤ C * (1 + ‖y‖) ^ (-(k : ℝ)))
    (A₀ : E →L[ℝ] E) (M : ℝ) (hM : 0 < M) (hA₀ : ∀ y, ‖y‖ ≤ M * ‖A₀ y‖) :
    (∀ᶠ A in 𝓝 A₀, Integrable (fun y => g (A y)) m) ∧
      ContinuousAt (fun A : E →L[ℝ] E => ∫ y, g (A y) ∂m) A₀ := by
  have hev : ∀ᶠ A in 𝓝 A₀, ∀ y, ‖y‖ ≤ (2 * M) * ‖A y‖ := by
    filter_upwards [Metric.ball_mem_nhds A₀ (show (0 : ℝ) < 1 / (2 * M) by positivity)] with A hA y
    rw [Metric.mem_ball, dist_eq_norm] at hA
    have e1 : A₀ y = A y - (A - A₀) y := by simp
    have h2 : ‖A₀ y‖ ≤ ‖A y‖ + 1 / (2 * M) * ‖y‖ := by
      calc ‖A₀ y‖ = ‖A y - (A - A₀) y‖ := by rw [← e1]
        _ ≤ ‖A y‖ + ‖(A - A₀) y‖ := norm_sub_le _ _
        _ ≤ ‖A y‖ + ‖A - A₀‖ * ‖y‖ := by gcongr; exact (A - A₀).le_opNorm y
        _ ≤ ‖A y‖ + 1 / (2 * M) * ‖y‖ := by
            gcongr
    have h3 : M * (1 / (2 * M) * ‖y‖) = ‖y‖ / 2 := by field_simp
    have h4 := hA₀ y
    have h5 : M * ‖A₀ y‖ ≤ M * ‖A y‖ + ‖y‖ / 2 := by
      rw [← h3, ← mul_add]; exact mul_le_mul_of_nonneg_left h2 hM.le
    linarith
  obtain ⟨C', hC'⟩ := decay_comp_of_norm_le g k C hC (2 * M)
  refine ⟨?_, ?_⟩
  · filter_upwards [hev] with A hA
    exact (hW.const_mul C').mono' (hg.comp A.continuous).aestronglyMeasurable
      (ae_of_all _ fun y => hC' _ _ (hA y))
  · refine tendsto_integral_filter_of_dominated_convergence
      (fun y => C' * (1 + ‖y‖) ^ (-(k : ℝ))) ?_ ?_ (hW.const_mul C') (ae_of_all _ fun y => ?_)
    · exact Eventually.of_forall fun A => (hg.comp A.continuous).aestronglyMeasurable
    · filter_upwards [hev] with A hA
      exact ae_of_all _ fun y => hC' _ _ (hA y)
    · exact (hg.comp (continuous_id.clm_apply continuous_const)).continuousAt.tendsto

end GlobalTheory.CompanionTheory.PushFam

namespace GlobalTheory.CompanionTheory.PushFam

theorem integrable_continuousAt_of_linear_push : PositivityTheory.PfSWUS.SchInf.FamCont := by
  intro N X _ μ' hμ' n c O hO hcO hfin hL g hg hdecay
  haveI := hμ'
  set k : ℕ := N + 1 with hk
  set W : (Fin N → ℝ) → ℝ := fun y => (1 + ‖y‖) ^ (-(k : ℝ)) with hWdef
  have hWnonneg : ∀ y, 0 ≤ W y := fun y => by positivity
  have hWμ : Integrable W μ' :=
    integrable_one_add_norm (by rw [Module.finrank_fin_fun, hk]; push_cast; linarith)
  have hWmeas : Measurable W := (measurable_const.add measurable_norm).pow_const _
  obtain ⟨s0, hs0O, hs0fin⟩ := hfin (fun y => ENNReal.ofReal (W y))
    (ENNReal.measurable_ofReal.comp hWmeas)
    ((hasFiniteIntegral_iff_ofReal (ae_of_all _ hWnonneg)).1 hWμ.2).ne O hO ⟨c, hcO⟩
  have hWm : Integrable W (n s0) := ⟨hWmeas.aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (ae_of_all _ hWnonneg)).2 (lt_top_iff_ne_top.2 hs0fin)⟩
  obtain ⟨L, Linv, Λ, hLc, _hLinvc, hΛc, hinv, hpush⟩ := hL s0 hs0O
  obtain ⟨C, hC⟩ := hdecay k
  have hA₀ : ∀ y, ‖y‖ ≤ (‖Linv c‖ + 1) * ‖L c y‖ := fun y => by
    calc ‖y‖ = ‖Linv c (L c y)‖ := by rw [hinv c hcO]
      _ ≤ ‖Linv c‖ * ‖L c y‖ := (Linv c).le_opNorm _
      _ ≤ (‖Linv c‖ + 1) * ‖L c y‖ := by gcongr; linarith
  obtain ⟨hint, hcont⟩ := integrable_continuousAt_clm_comp (n s0) k hWm g hg C hC (L c)
    (‖Linv c‖ + 1) (by positivity) hA₀
  have hint' : ∀ᶠ s in 𝓝 c, Integrable (fun y => g (L s y)) (n s0) := hLc.eventually hint
  have hO' : O ∈ 𝓝 c := hO.mem_nhds hcO
  refine ⟨?_, ?_⟩
  · filter_upwards [hint', hO'] with s hs hsO
    rw [hpush s hsO]
    exact ((integrable_map_measure hg.aestronglyMeasurable
      (L s).continuous.aemeasurable).2 hs).smul_measure_nnreal
  · have hH : ContinuousAt (fun s => (Λ s : ℝ) • ∫ y, g (L s y) ∂(n s0)) c :=
      (NNReal.continuous_coe.continuousAt.comp hΛc).smul
        (ContinuousAt.comp (f := L) (g := fun A : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) =>
          ∫ y, g (A y) ∂(n s0)) hcont hLc)
    refine hH.congr ?_
    filter_upwards [hO'] with s hs
    rw [hpush s hs, integral_smul_nnreal_measure,
      integral_map (L s).continuous.aemeasurable hg.aestronglyMeasurable, NNReal.smul_def]

end GlobalTheory.CompanionTheory.PushFam
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanFamilyContinuityStatement
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_family_continuity : PositivityTheory.PfSWUS.SchInf.FamCont := by
  first | exact @GlobalTheory.CompanionTheory.PushFam.integrable_continuousAt_of_linear_push | exact GlobalTheory.CompanionTheory.PushFam.integrable_continuousAt_of_linear_push | (intros; apply GlobalTheory.CompanionTheory.PushFam.integrable_continuousAt_of_linear_push <;> assumption)
end
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinitePartOpen
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinitePartOpen
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.FinOpenGram

theorem finOpen : PositivityTheory.PfSWUS.SchInf.FinOpen := by
  intro F E _ _ _ _ _ σ hCM M J hJ n μ ν m hμ hν hm f hf hfin U hU hne
  have : BorelSpace (HermR (Ainf F) σ n) := ⟨rfl⟩
  by_contra hcon
  push Not at hcon
  have hpos : ν U ≠ 0 := (hU.measure_pos ν hne).ne'
  have h2 := hm
  unfold GlobalTheory.CompanionTheory.SW.IsGramFib Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily at h2
  have hfib := h2.2.1 f hf
  have hle : (⊤ : ℝ≥0∞) * ν U ≤ ∫⁻ S, ∫⁻ X, f X ∂(m S) ∂ν := by
    rw [← lintegral_indicator_const hU.measurableSet]
    refine lintegral_mono fun S => ?_
    by_cases hS : S ∈ U
    · rw [Set.indicator_of_mem hS, hcon S hS]
    · rw [Set.indicator_of_notMem hS]
      exact bot_le
  rw [ENNReal.top_mul hpos, top_le_iff, ← hfib] at hle
  exact hfin (top_le_iff.1 (hle ▸ setLIntegral_le_lintegral _ _))

end GlobalTheory.CompanionTheory.SW.FinOpenGram
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinitePartOpenStatement
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_part_open : PositivityTheory.PfSWUS.SchInf.FinOpen := by
  first | exact @GlobalTheory.CompanionTheory.SW.FinOpenGram.finOpen | exact GlobalTheory.CompanionTheory.SW.FinOpenGram.finOpen | (intros; apply GlobalTheory.CompanionTheory.SW.FinOpenGram.finOpen <;> assumption)
end
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanCoordinates
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanCoordinates
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.CoordR

theorem coordInf : PositivityTheory.PfSWUS.SchInf.CoordInf := by
  intro F E _ _ _ _ _ σ hσ n M
  obtain ⟨-, e, -, he, -⟩ := GlobalTheory.T.infinite_adele_haar_map_eq_scaled_volume F hσ.1
  let eh : Ainf F ≃ₜ (InfinitePlace F → ℝ) := he.homeomorph _
  have heh : ∀ y, eh y = e y := fun _ => rfl
  haveI : SecondCountableTopology (Ainf F) := eh.secondCountableTopology
  haveI : T2Space (Ainf F) := eh.symm.t2Space
  obtain ⟨i1, i2, i3, i4, -, -, hb, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Ainf F)
  let d := Module.finrank F E
  let b : Module.Basis (Fin d) F E := Module.finBasis F E
  let B := Algebra.TensorProduct.basis (Ainf F) b
  let Hs : (Ainf F ⊗[F] E) ≃ₜ (Fin d → Ainf F) := (hb d b).homeomorph _
  have hHs : ∀ y k, Hs y k = B.repr y k := fun _ _ => rfl
  let I := Fin n × Fin M × Fin d × InfinitePlace F
  let q : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let eH : (Fin n → Fin M → Ainf F ⊗[F] E) ≃ₜ (Fin (Fintype.card I) → ℝ) :=
    { toFun := fun X t => eh (Hs (X (q.symm t).1 (q.symm t).2.1) (q.symm t).2.2.1) (q.symm t).2.2.2
      invFun := fun y a j => Hs.symm fun k => eh.symm fun w => y (q (a, j, k, w))
      left_inv := fun X => by simp
      right_inv := fun y => by
        funext t
        simp
      continuous_toFun := continuous_pi fun t =>
        (continuous_apply _).comp (eh.continuous.comp ((continuous_apply _).comp
          (Hs.continuous.comp ((continuous_apply _).comp (continuous_apply _)))))
      continuous_invFun := continuous_pi fun a => continuous_pi fun j =>
        Hs.symm.continuous.comp (continuous_pi fun k => eh.symm.continuous.comp
          (continuous_pi fun w => continuous_apply _)) }
  have hadd : ∀ X Y, eH (X + Y) = eH X + eH Y := by
    intro X Y
    funext t
    change eh (Hs (X _ _ + Y _ _) _) _ = eh (Hs (X _ _) _) _ + eh (Hs (Y _ _) _) _
    simp only [hHs, heh, map_add (f := _), Finsupp.add_apply, Pi.add_apply]
  let eV : (Fin n → Fin M → Ainf F ⊗[F] E) ≃+ (Fin (Fintype.card I) → ℝ) :=
    { eH.toEquiv with map_add' := hadd }
  have hV : ∀ X, eV X = eH X := fun _ => rfl
  have hVs : ∀ y, eV.symm y = eH.symm y := fun _ => rfl
  have hc : Continuous fun p : (Fin n → Fin M → Ainf F ⊗[F] E) × Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E) =>
      rmul (Ainf F) p.1 p.2 := by
    refine continuous_pi fun a => continuous_pi fun i => continuous_finsetSum _ fun c _ => ?_
    have h1 : Continuous fun p : (Fin n → Fin M → Ainf F ⊗[F] E) ×
        Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E) => p.1 c i :=
      (continuous_apply i).comp ((continuous_apply c).comp continuous_fst)
    exact h1.mul (continuous_snd.matrix_elem c a)
  have hrad : ∀ (g : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) (X Y : Fin n → Fin M → Ainf F ⊗[F] E),
      rmul (Ainf F) (X + Y) g = rmul (Ainf F) X g + rmul (Ainf F) Y g := by
    intro g X Y
    funext a i
    simp [rmul, add_mul, Finset.sum_add_distrib]
  let L0 : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E) → (Fin (Fintype.card I) → ℝ) →+ (Fin (Fintype.card I) → ℝ) :=
    fun g => AddMonoidHom.mk' (fun y => eV (rmul (Ainf F) (eV.symm y) g)) fun y z => by
      rw [map_add (f := _), hrad, map_add (f := _)]
  have hL0 : ∀ g, Continuous (L0 g) := fun g =>
    eH.continuous.comp (hc.comp (eH.symm.continuous.prodMk continuous_const))
  let L : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E) → (Fin (Fintype.card I) → ℝ) →L[ℝ] (Fin (Fintype.card I) → ℝ) :=
    fun g => (L0 g).toRealLinearMap (hL0 g)
  refine ⟨Fintype.card I, eV, eH.continuous, eH.symm.continuous, L, ?_, ?_⟩
  · refine continuous_clm_apply.2 fun y => ?_
    exact eH.continuous.comp (hc.comp (continuous_const.prodMk continuous_id))
  · intro g X
    change eV _ = eV (rmul (Ainf F) (eV.symm (eV X)) g)
    rw [AddEquiv.symm_apply_apply]

end GlobalTheory.CompanionTheory.SW.CoordR

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanCoordinatesStatement
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_coordinates : PositivityTheory.PfSWUS.SchInf.CoordInf := by
  first | exact @GlobalTheory.CompanionTheory.SW.CoordR.coordInf | exact GlobalTheory.CompanionTheory.SW.CoordR.coordInf | (intros; apply GlobalTheory.CompanionTheory.SW.CoordR.coordInf <;> assumption)
end
end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.UnramifiedSchwartzDensity.Assemble
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace PositivityTheory.PfSWUS.SchInf

open GlobalTheory.CompanionTheory.SW

theorem schwartz_decay {N : ℕ} (g : SchwartzMap (Fin N → ℝ) ℂ) (k : ℕ) :
    ∃ C : ℝ, ∀ y, ‖g y‖ ≤ C * (1 + ‖y‖) ^ (-(k : ℝ)) := by
  set B : ℝ := 2 ^ k * ((Finset.Iic (k, 0)).sup fun m => SchwartzMap.seminorm ℝ m.1 m.2) g with hB
  refine ⟨B, fun y => ?_⟩
  have h1 := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, 0)) (k := k) (n := 0) le_rfl le_rfl g y
  rw [norm_iteratedFDeriv_zero] at h1
  have hy : 0 < 1 + ‖y‖ := by positivity
  rw [Real.rpow_neg hy.le, Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  calc ‖g y‖ * (1 + ‖y‖) ^ k = (1 + ‖y‖) ^ k * ‖g y‖ := by ring
    _ ≤ B := h1

theorem schwartzDensInf_of (hA : FamCont) (hB : SecInf) (hC : CoordInf) (hD : ScaleInf) (hE : FinOpen)
    (hF : DensInt) : PositivityTheory.PfSWUS.HMass.SchwartzDensInf := by
  intro F E _ _ _ _ _ σ hσ M J hJ n μ ν m hμ hν hm φ hφ
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  have hloc : IsLocR (Ainf F) := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hσ.1
  obtain ⟨i1, i2, i3, i4, -, -, -, hBor, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Ainf F)
  have := i1
  have := i2
  have := i3
  have := i4
  have := hBor n M
  obtain ⟨-, hcomp, hone, hmem, -⟩ := GlobalTheory.CompanionTheory.SW.GramAlg.gram_algebra F E σ hσ M J hJ (Ainf F) n
  obtain ⟨N, eV, heV, heVs, L, hL, hLe⟩ := hC F E σ hσ n M
  obtain ⟨g, hg⟩ := hφ N eV heV heVs
  have hφeq : ∀ X, φ X = g (eV X) := fun X => by rw [hg, AddEquiv.symm_apply_apply]
  let T : (Fin n → Fin M → Ainf F ⊗[F] E) ≃ₜ (Fin N → ℝ) :=
    { toEquiv := eV.toEquiv, continuous_toFun := heV, continuous_invFun := heVs }
  have hTm : MeasurableEmbedding eV := T.measurableEmbedding
  have hμ' : (μ.map eV).IsAddHaarMeasure := eV.isAddHaarMeasure_map μ heV heVs
  have key : ∀ c : HermR (Ainf F) σ n, IsUnit (c : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det →
      ∀ g' : (Fin N → ℝ) → ℂ, Continuous g' → (∀ k : ℕ, ∃ C : ℝ, ∀ y, ‖g' y‖ ≤ C * (1 + ‖y‖) ^ (-(k : ℝ))) →
      (∀ᶠ S in 𝓝 c, Integrable g' ((m S).map eV)) ∧
        ContinuousAt (fun S => ∫ y, g' y ∂((m S).map eV)) c := by
    intro c hc g' hg'c hg'd
    obtain ⟨O, hO, hcO, hsec⟩ := hB F E σ hσ n c hc
    obtain ⟨A, C, hAc, hCc, hAC⟩ := hD F E σ hσ n M μ ν hμ hν
    refine hA N (HermR (Ainf F) σ n) (μ.map eV) hμ' (fun S => (m S).map eV) c O hO hcO ?_ ?_ g' hg'c hg'd
    · intro f hf hfin U hU hne
      rw [lintegral_map hf hTm.measurable] at hfin
      obtain ⟨S, hS, hS'⟩ := hE F E σ hσ M J hJ n μ ν m hμ hν hm (fun X => f (eV X))
        (hf.comp hTm.measurable) hfin U hU hne
      exact ⟨S, hS, by rwa [lintegral_map hf hTm.measurable]⟩
    · intro s₀ hs₀
      obtain ⟨h, hinv, hhc, hhic, hhS⟩ := hsec s₀ hs₀
      have hunit : ∀ S ∈ O, IsUnit (h S).det := fun S hS =>
        Matrix.isUnit_det_of_right_inverse (hhS S hS).1
      have hcn : O ∈ 𝓝 c := hO.mem_nhds hcO
      have hh_at : ContinuousAt h c := hhc.continuousAt hcn
      have hhi_at : ContinuousAt hinv c := hhic.continuousAt hcn
      have hU_ev : ∀ᶠ S in 𝓝 c, h S ∈ {g : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E) | IsUnit g.det} :=
        Filter.mem_of_superset hcn fun S hS => hunit S hS
      have htends : Filter.Tendsto h (𝓝 c)
          (𝓝[{g : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E) | IsUnit g.det}] (h c)) :=
        tendsto_nhdsWithin_iff.2 ⟨hh_at, hU_ev⟩
      have hA_at : ContinuousAt (fun S => A (h S)) c := (hAc (h c) (hunit c hcO)).tendsto.comp htends
      have hC_at : ContinuousAt (fun S => C (h S)) c := (hCc (h c) (hunit c hcO)).tendsto.comp htends
      refine ⟨fun S => L (h S), fun S => L (hinv S), fun S => C (h S) * (A (h S))⁻¹,
        hL.continuousAt.comp hh_at, hL.continuousAt.comp hhi_at,
        hC_at.mul (hA_at.inv₀ (hAC _ (hunit c hcO)).1), ?_, ?_⟩
      · intro S hS y
        obtain ⟨X, rfl⟩ := eV.surjective y
        show L (hinv S) (L (h S) (eV X)) = eV X
        rw [← hLe, ← hLe, hcomp, (hhS S hS).1, hone]
      · intro S hS
        have hu := hunit S hS
        obtain ⟨hA0, -, hAm, hCm⟩ := hAC (h S) hu
        let τ : HermR (Ainf F) σ n → HermR (Ainf F) σ n := fun S' =>
          ⟨cT (sigR (Ainf F) σ) (h S) * (S' : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) * h S, hmem S' (h S)⟩
        have hτ : ∀ S', (τ S' : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) =
            cT (sigR (Ainf F) σ) (h S) * S' * h S := fun _ => rfl
        have hk := GlobalTheory.T.gram_fiber_measures_rmul_equivariant F E σ hσ M J hJ (Ainf F) hloc n μ ν m hμ hν hm (h S) hu τ hτ
          (A (h S)) (C (h S)) hAm (hCm τ hτ) s₀
        have hτs : τ s₀ = S := Subtype.ext (hhS S hS).2.2.symm
        rw [hτs] at hk
        have hmS : m S = (C (h S) * (A (h S))⁻¹) • (m s₀).map (fun X : Fin n → Fin M → Ainf F ⊗[F] E => rmul (Ainf F) X (h S)) := by
          rw [mul_comm, ← smul_smul, ← hk, smul_smul, inv_mul_cancel₀ hA0, one_smul]
        have hrm : Measurable (fun X : Fin n → Fin M → Ainf F ⊗[F] E => rmul (Ainf F) X (h S)) := by
          have : (fun X : Fin n → Fin M → Ainf F ⊗[F] E => rmul (Ainf F) X (h S)) = fun X => eV.symm (L (h S) (eV X)) := by
            funext X
            rw [← hLe, AddEquiv.symm_apply_apply]
          rw [this]
          exact (heVs.comp ((L (h S)).continuous.comp heV)).measurable
        show (m S).map eV = _
        rw [hmS, Measure.map_smul, Measure.map_map hTm.measurable hrm,
          Measure.map_map (L (h S)).continuous.measurable hTm.measurable]
        congr 2
        funext X
        exact hLe (h S) X
        exact hTm.measurable.aemeasurable
  have hgk : ∀ k : ℕ, ∃ C : ℝ, ∀ y, ‖g y‖ ≤ C * (1 + ‖y‖) ^ (-(k : ℝ)) := schwartz_decay g
  have hng : ∀ k : ℕ, ∃ C : ℝ, ∀ y, ‖((‖g y‖ : ℝ) : ℂ)‖ ≤ C * (1 + ‖y‖) ^ (-(k : ℝ)) := by
    intro k
    obtain ⟨C, hC⟩ := hgk k
    exact ⟨C, fun y => by simpa using hC y⟩
  have hngc : Continuous fun y => ((‖g y‖ : ℝ) : ℂ) := Complex.continuous_ofReal.comp g.continuous.norm
  have hφc : Continuous φ := by
    rw [show φ = fun X => g (eV X) from funext hφeq]
    exact g.continuous.comp heV
  have hIntS : ∀ S : HermR (Ainf F) σ n, IsUnit (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det →
      Integrable φ (m S) := by
    intro S hS
    have h1 := ((key S hS g g.continuous hgk).1).self_of_nhds
    rw [hTm.integrable_map_iff] at h1
    rwa [show φ = (⇑g ∘ ⇑eV) from funext hφeq]
  have hcont : ContinuousOn (fun S => ∫ X, φ X ∂(m S))
      {S : HermR (Ainf F) σ n | IsUnit (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det} := by
    intro S hS
    refine ((key S hS g g.continuous hgk).2.congr (Filter.Eventually.of_forall fun S' => ?_)).continuousWithinAt
    show ∫ y, g y ∂((m S').map eV) = ∫ X, φ X ∂(m S')
    rw [hTm.integral_map]
    simp only [hφeq]
  have hcontn : ContinuousOn (fun S => ∫ X, ‖φ X‖ ∂(m S))
      {S : HermR (Ainf F) σ n | IsUnit (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det} := by
    intro S hS
    have h3 : ContinuousAt (fun S' => (∫ y, ((‖g y‖ : ℝ) : ℂ) ∂((m S').map eV)).re) S :=
      Complex.continuous_re.continuousAt.comp (key S hS _ hngc hng).2
    refine (h3.congr (Filter.Eventually.of_forall fun S' => ?_)).continuousWithinAt
    show (∫ y, ((‖g y‖ : ℝ) : ℂ) ∂((m S').map eV)).re = ∫ X, ‖φ X‖ ∂(m S')
    rw [hTm.integral_map, integral_complex_ofReal, Complex.ofReal_re]
    simp only [hφeq]
  have hφμ : Integrable φ μ := by
    obtain ⟨C0, hC0⟩ := hgk (Module.finrank ℝ (Fin N → ℝ) + 1)
    have hW : Integrable (fun y : Fin N → ℝ => (1 + ‖y‖) ^ (-((Module.finrank ℝ (Fin N → ℝ) + 1 : ℕ) : ℝ)))
        (μ.map eV) := integrable_one_add_norm (by push_cast; linarith)
    have hgμ : Integrable g (μ.map eV) :=
      Integrable.mono' (hW.const_mul C0) g.continuous.aestronglyMeasurable (ae_of_all _ hC0)
    rw [hTm.integrable_map_iff] at hgμ
    rwa [show φ = (⇑g ∘ ⇑eV) from funext hφeq]
  exact ⟨hφc, ⟨hcont, fun K hK hKB => hF F E σ hσ M J hJ n μ ν m hμ hν hm φ hφc hφμ hIntS hcontn K hK hKB⟩,
    hIntS⟩

end PositivityTheory.PfSWUS.SchInf

end
end

theorem PositivityTheory.PfSWUS.SchInf.schwartzDensInf : PositivityTheory.PfSWUS.HMass.SchwartzDensInf :=
  PositivityTheory.PfSWUS.SchInf.schwartzDensInf_of GlobalTheory.T.archimedean_family_continuity GlobalTheory.T.archimedean_section GlobalTheory.T.archimedean_coordinates GlobalTheory.T.archimedean_scaling GlobalTheory.T.finite_part_open
    GlobalTheory.T.density_integral
