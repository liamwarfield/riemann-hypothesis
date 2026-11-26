module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocalDensityOfSelfDualLatticeLemmas
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicHaarMeasureScaling
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.StandardAdelicCharacter
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaAverageExpectedCount
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaSeriesSummable

@[expose] public section

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.PureAdelicFunctionMeasurable
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.PureAdelicFunctionMeasurable
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.PureMeas

theorem borelSpace_ainf (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (n M : ℕ) :
    BorelSpace (Fin n → Fin M → Ainf F ⊗[F] E) := by
  obtain ⟨⟨-, scA, -⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  have scA' : SecondCountableTopology (Ainf F × Af F) := scA
  haveI : SecondCountableTopology (Ainf F) :=
    (isEmbedding_prodMkLeft (0 : Af F)).secondCountableTopology
  haveI : T2Space (Ainf F) := GlobalTheory.CompanionTheory.AdeleTop.t2Space_infiniteAdeleRing_of_numberField_field F
  exact (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Ainf F)).2.2.2.2.2.2.2.1 n M

theorem borelSpace_af (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (n M : ℕ) :
    BorelSpace (Fin n → Fin M → AF F ⊗[F] E) := by
  obtain ⟨⟨lcA, scA, t2A⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI := lcA
  haveI := scA
  haveI := t2A
  exact (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (AF F)).2.2.2.2.2.2.2.1 n M

theorem borelSpace_fv (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (n M : ℕ) (v : HeightOneSpectrum (𝓞 F)) :
    BorelSpace (Fin n → Fin M → Fv F v ⊗[F] E) := by
  haveI := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
  haveI : LocallyCompactSpace (Fv F v) := inferInstance
  haveI : SecondCountableTopology (Fv F v) := inferInstance
  haveI : T2Space (Fv F v) := inferInstance
  exact (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)).2.2.2.2.2.2.2.1 n M

theorem measurable_pureL : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (S : Finset (HeightOneSpectrum (𝓞 F))) (φinf : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞) (φ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℝ≥0∞), Measurable φinf → (∀ v, Measurable (φ v)) → Measurable (pureL b S φinf φ) := by
  intro F E _ _ _ _ _ σ hσ d b n M S φinf φ hφinf hφ
  obtain ⟨hpi, hpf, hpv, -, hint, -⟩ := GlobalTheory.CompanionTheory.SW.MeasProj.proj_props F E σ hσ d b n M
  haveI := borelSpace_af F E σ hσ n M
  haveI := borelSpace_ainf F E σ hσ n M
  haveI : ∀ v, BorelSpace (Fin n → Fin M → Fv F v ⊗[F] E) := fun v => borelSpace_fv F E σ hσ n M v
  refine Measurable.indicator ?_ (hint S).measurableSet
  refine (hφinf.comp hpi.measurable).mul ?_
  refine Finset.measurable_prod _ fun v _ => ?_
  exact (hφ v).comp ((hpv v).comp hpf).measurable

end GlobalTheory.CompanionTheory.SW.PureMeas
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.PureAdelicFunctionMeasurableStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pure_adelic_function_measurable : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (S : Finset (HeightOneSpectrum (𝓞 F))) (φinf : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞) (φ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℝ≥0∞), Measurable φinf → (∀ v, Measurable (φ v)) → Measurable (pureL b S φinf φ) := by
  first | exact @GlobalTheory.CompanionTheory.SW.PureMeas.measurable_pureL | exact GlobalTheory.CompanionTheory.SW.PureMeas.measurable_pureL | (intros; apply GlobalTheory.CompanionTheory.SW.PureMeas.measurable_pureL <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.StandardLocalHaarProperties
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.StandardLocalHaarProperties
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.Vol

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem isCompact_integers : IsCompact (v.adicCompletionIntegers F : Set (Fv F v)) :=
  isCompact_iff_compactSpace.2 (GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v)

theorem isOpen_integers : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) :=
  Valued.isOpen_valuationSubring _

def mulAdd (c : Fv F v) (hc : c ≠ 0) : Fv F v ≃+ Fv F v where
  toFun t := c * t
  invFun t := c⁻¹ * t
  left_inv t := by simp [hc]
  right_inv t := by simp [hc]
  map_add' := mul_add c

theorem mulAdd_continuous (c : Fv F v) (hc : c ≠ 0) : Continuous (mulAdd v c hc) :=
  continuous_const.mul continuous_id

theorem mulAdd_symm_continuous (c : Fv F v) (hc : c ≠ 0) : Continuous (mulAdd v c hc).symm :=
  continuous_const.mul continuous_id

theorem vol_lt_one (lam : Measure (Fv F v)) (h : IsStdV v lam) :
    lam {t | Valued.v t < 1} = (Ideal.absNorm v.asIdeal : ℝ≥0∞)⁻¹ := by
  haveI := h.1
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  have key := GlobalTheory.ResidueBoxVolume.measureReal_residueBox F v (Fv F v) lam Unit
    (ContinuousLinearEquiv.funUnique Unit (Fv F v) (Fv F v)).symm {0}
  have e1 : {x : Fv F v | ∃ y : Unit → v.adicCompletionIntegers F,
      (∀ i, (ContinuousLinearEquiv.funUnique Unit (Fv F v) (Fv F v)).symm x i = (y i : Fv F v)) ∧
      (fun i => IsLocalRing.residue (v.adicCompletionIntegers F) (y i)) ∈
        ({0} : Set (Unit → IsLocalRing.ResidueField (v.adicCompletionIntegers F)))} =
      {t | Valued.v t < 1} := by
    ext x
    simp only [Set.mem_setOf_eq, ← GlobalTheory.ResidueBoxVolume.exists_residue_eq_zero_iff v x]
    constructor
    · rintro ⟨y, h1, h2⟩
      exact ⟨y (), h1 (), congrFun h2 ()⟩
    · rintro ⟨y, h1, h2⟩
      exact ⟨fun _ => y, fun _ => h1, funext fun _ => h2⟩
  have e2 : {x : Fv F v | ∀ i, (ContinuousLinearEquiv.funUnique Unit (Fv F v) (Fv F v)).symm x i ∈
      v.adicCompletionIntegers F} = (v.adicCompletionIntegers F : Set (Fv F v)) := by
    ext x
    simp
  rw [e1, e2, GroundTheory.Global.natCard_residueField_adicCompletionIntegers v] at key
  simp only [Fintype.card_unit, pow_one, Set.ncard_singleton, Nat.cast_one, one_mul] at key
  have hO : lam.real (v.adicCompletionIntegers F : Set (Fv F v)) = 1 := by
    simp [measureReal_def, h.2]
  rw [hO] at key
  have hfin : lam {t | Valued.v t < 1} ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := lam (v.adicCompletionIntegers F : Set (Fv F v))) ?_ ?_
    · rw [h.2]; exact ENNReal.one_ne_top
    · exact measure_mono fun t (ht : Valued.v t < 1) => (le_of_lt ht : Valued.v t ≤ 1)
  refine ENNReal.eq_inv_of_mul_eq_one_left ?_
  refine (ENNReal.toReal_eq_one_iff _).1 ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast]
  exact key

theorem absNorm_ne_zero : (Ideal.absNorm v.asIdeal : ℝ≥0∞) ≠ 0 := by
  have : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  exact_mod_cast this

theorem map_unit (lam : Measure (Fv F v)) (h : IsStdV v lam) (u : Fv F v) (hu : Valued.v u = 1) :
    lam.map (fun t => u * t) = lam := by
  haveI := h.1
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨_, hl, hs, ht, _⟩ := GlobalTheory.T.completion_is_local_ring F v
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hu
  refine (GlobalTheory.T.map_addHaar_addEquiv_eq_smul_and_eq_of_compact_open (Fv F v) (Fv F v) lam lam (mulAdd v u hu0) (mulAdd_continuous v u hu0)
    (mulAdd_symm_continuous v u hu0)).2 (v.adicCompletionIntegers F : Set (Fv F v))
    (v.adicCompletionIntegers F : Set (Fv F v)) (isCompact_integers v) (isOpen_integers v)
    ⟨0, zero_mem _⟩ (fun x => ?_) rfl
  change Valued.v (u * x) ≤ 1 ↔ Valued.v x ≤ 1
  rw [map_mul, hu, one_mul]

theorem exp_neg_one_mul_lt_one_iff (a : WithZero (Multiplicative ℤ)) :
    WithZero.exp (-1 : ℤ) * a < 1 ↔ a ≤ 1 := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · rw [← WithZero.exp_log ha, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_lt_exp,
      WithZero.exp_le_exp]
    omega

theorem map_unif (lam : Measure (Fv F v)) (h : IsStdV v lam) (π : Fv F v)
    (hπ : Valued.v π = WithZero.exp (-1 : ℤ)) :
    lam.map (fun t => π * t) = (Ideal.absNorm v.asIdeal : ℝ≥0∞) • lam := by
  haveI := h.1
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨_, hl, hs, ht, _⟩ := GlobalTheory.T.completion_is_local_ring F v
  have hq0 := absNorm_ne_zero v
  have hqt : (Ideal.absNorm v.asIdeal : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hπ0 : π ≠ 0 := by
    rintro rfl
    simp at hπ
    exact WithZero.exp_ne_zero hπ.symm
  haveI : ((Ideal.absNorm v.asIdeal : ℝ≥0∞) • lam).IsAddHaarMeasure :=
    Measure.IsAddHaarMeasure.smul lam hq0 hqt
  refine (GlobalTheory.T.map_addHaar_addEquiv_eq_smul_and_eq_of_compact_open (Fv F v) (Fv F v) lam ((Ideal.absNorm v.asIdeal : ℝ≥0∞) • lam)
    (mulAdd v π hπ0) (mulAdd_continuous v π hπ0) (mulAdd_symm_continuous v π hπ0)).2
    (v.adicCompletionIntegers F : Set (Fv F v)) {t | Valued.v t < 1} (isCompact_integers v)
    (isOpen_integers v) ⟨0, zero_mem _⟩ (fun x => ?_) ?_
  · change Valued.v (π * x) < 1 ↔ Valued.v x ≤ 1
    rw [map_mul, hπ]
    exact exp_neg_one_mul_lt_one_iff _
  · rw [h.2, Measure.smul_apply, vol_lt_one v lam h, smul_eq_mul, ENNReal.mul_inv_cancel hq0 hqt]

theorem volumes_in_completion : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → lam {t | Valued.v t < 1} = (Ideal.absNorm v.asIdeal : ℝ≥0∞)⁻¹ ∧ (∀ π : Fv F v, Valued.v π = WithZero.exp (-1 : ℤ) → lam.map (fun t => π * t) = (Ideal.absNorm v.asIdeal : ℝ≥0∞) • lam) ∧ (∀ u : Fv F v, Valued.v u = 1 → lam.map (fun t => u * t) = lam) ∧ Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) = Ideal.absNorm v.asIdeal :=
  fun F _ _ v lam h => ⟨vol_lt_one v lam h, map_unif v lam h, map_unit v lam h,
    GroundTheory.Global.natCard_residueField_adicCompletionIntegers v⟩

end GlobalTheory.CompanionTheory.SW.Vol
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.StandardLocalHaarPropertiesStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standard_local_haar_properties : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → lam {t | Valued.v t < 1} = (Ideal.absNorm v.asIdeal : ℝ≥0∞)⁻¹ ∧ (∀ π : Fv F v, Valued.v π = WithZero.exp (-1 : ℤ) → lam.map (fun t => π * t) = (Ideal.absNorm v.asIdeal : ℝ≥0∞) • lam) ∧ (∀ u : Fv F v, Valued.v u = 1 → lam.map (fun t => u * t) = lam) ∧ Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) = Ideal.absNorm v.asIdeal := by
  first | exact @GlobalTheory.CompanionTheory.SW.Vol.volumes_in_completion | exact GlobalTheory.CompanionTheory.SW.Vol.volumes_in_completion | (intros; apply GlobalTheory.CompanionTheory.SW.Vol.volumes_in_completion <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicHaarMeasureLinearChange
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicHaarMeasureLinearChange
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.Core.PiScale

section Abstract

variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [MeasurableSpace R]
  [BorelSpace R] [SecondCountableTopology R] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem continuous_mulVec_left (M : Matrix ι ι R) : Continuous (fun x : ι → R => M *ᵥ x) :=
  Continuous.matrix_mulVec continuous_const continuous_id

theorem image_mulVec_eq_preimage (M N : Matrix ι ι R) (h1 : M * N = 1) (h2 : N * M = 1)
    (s : Set (ι → R)) : (fun x => M *ᵥ x) '' s = (fun x => N *ᵥ x) ⁻¹' s := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [Matrix.mulVec_mulVec, h2] using hx
  · intro hy
    exact ⟨N *ᵥ y, hy, by simp [Matrix.mulVec_mulVec, h1]⟩

theorem pi_image_mul (lf : Measure R) [SigmaFinite lf] (u v : ι → R) (huv : ∀ i, u i * v i = 1)
    (c : ι → ℝ≥0)
    (hc : ∀ i (s : Set R), MeasurableSet s → lf ((fun x => u i * x) '' s) = (c i : ℝ≥0∞) * lf s)
    (s : Set (ι → R)) (hs : MeasurableSet s) :
    (Measure.pi fun _ : ι => lf) ((fun x i => u i * x i) '' s) =
      (∏ i, (c i : ℝ≥0∞)) * (Measure.pi fun _ : ι => lf) s := by
  have hT : Measurable (fun (x : ι → R) i => v i * x i) :=
    (continuous_pi fun i => continuous_const.mul (continuous_apply i)).measurable
  have himg : (fun (x : ι → R) i => u i * x i) '' s = (fun (x : ι → R) i => v i * x i) ⁻¹' s := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have : (fun i => v i * (u i * x i)) = x := by
        funext i
        rw [← mul_assoc, mul_comm (v i), huv, one_mul]
      simpa [this] using hx
    · intro hy
      refine ⟨_, hy, ?_⟩
      funext i
      show u i * (v i * y i) = y i
      rw [← mul_assoc, huv, one_mul]
  have hpre : ∀ i (t : Set R), (fun x => v i * x) ⁻¹' t = (fun x => u i * x) '' t := by
    intro i t
    ext y
    constructor
    · intro hy
      exact ⟨_, hy, by simp only; rw [← mul_assoc, huv, one_mul]⟩
    · rintro ⟨x, hx, rfl⟩
      have : v i * (u i * x) = x := by rw [← mul_assoc, mul_comm (v i), huv, one_mul]
      simpa [this] using hx
  have e1 : Measure.pi (fun i => c i • lf) =
      (Measure.pi fun _ : ι => lf).map (fun (x : ι → R) i => v i * x i) := by
    refine Measure.pi_eq fun t ht => ?_
    rw [Measure.map_apply hT (MeasurableSet.univ_pi ht)]
    have : (fun (x : ι → R) i => v i * x i) ⁻¹' Set.pi Set.univ t =
        Set.pi Set.univ fun i => (fun x => u i * x) '' t i := by
      ext x
      simp only [Set.mem_preimage, Set.mem_univ_pi, ← hpre]
    rw [this, Measure.pi_pi]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hc i _ (ht i)]
    rfl
  have e2 : Measure.pi (fun i => c i • lf) =
      (∏ i, (c i : ℝ≥0∞)) • (Measure.pi fun _ : ι => lf) := by
    refine Measure.pi_eq fun t ht => ?_
    rw [Measure.smul_apply, Measure.pi_pi, smul_eq_mul, ← Finset.prod_mul_distrib]
    rfl
  rw [himg, ← Measure.map_apply hT hs, ← e1, e2, Measure.smul_apply, smul_eq_mul]

theorem measurePreserving_transvection (lf : Measure R) [SigmaFinite lf] [lf.IsAddLeftInvariant]
    (i j : ι) (hij : i ≠ j) (c : R) :
    MeasurePreserving (fun x : ι → R => transvection i j c *ᵥ x)
      (Measure.pi fun _ : ι => lf) (Measure.pi fun _ : ι => lf) := by
  have ht : Measurable (fun x : ι → R => transvection i j c *ᵥ x) :=
    (continuous_mulVec_left _).measurable
  refine ⟨ht, ?_⟩
  refine (Measure.pi_eq fun s hs ↦ ?_).symm
  have h2s : MeasurableSet (Set.univ.pi s) := .pi Set.countable_univ fun i _ ↦ hs i
  simp_rw [← Measure.pi_pi, ← lintegral_indicator_one h2s]
  rw [lintegral_map (measurable_one.indicator h2s) ht]
  refine lintegral_eq_of_lmarginal_eq {i} ((measurable_one.indicator h2s).comp ht)
    (measurable_one.indicator h2s) ?_
  simp_rw [lmarginal_singleton]
  ext x
  have hup : ∀ xi : R, transvection i j c *ᵥ Function.update x i xi =
      Function.update x i (xi + c * x j) := by
    intro xi
    funext k
    by_cases hk : k = i
    · subst hk
      simp [transvection, add_mulVec, single_mulVec, hij.symm]
    · simp [transvection, add_mulVec, single_mulVec, hk, hij.symm]
  simp only [Function.comp_apply, hup]
  exact lintegral_add_right_eq_self
    (fun xᵢ ↦ Set.indicator (Set.univ.pi s) 1 (Function.update x i xᵢ)) (c * x j)

end Abstract

section Global

variable {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem Bf_mul (g h : Matrix ι ι F) : Bf (g * h) = Bf g * Bf h := by
  simp [Bf, Matrix.map_mul]

theorem Bf_one : Bf (1 : Matrix ι ι F) = 1 := by
  simp [Bf]

theorem Bf_inv_mul (g : Matrix ι ι F) (hg : g.det ≠ 0) : Bf g⁻¹ * Bf g = 1 := by
  rw [← Bf_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hg), Bf_one]

theorem Bf_mul_inv (g : Matrix ι ι F) (hg : g.det ≠ 0) : Bf g * Bf g⁻¹ = 1 := by
  rw [← Bf_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hg), Bf_one]

end Global

theorem pi_scale : ∀ (F : Type) [Field F] [NumberField F], ∀ [MeasurableSpace (A F)] [BorelSpace (A F)] (lf : Measure (A F)), lf.IsAddHaarMeasure → lf (Oh F) = 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι], (∀ g : Matrix ι ι F, g.det ≠ 0 → ∀ s : Set (ι → A F), MeasurableSet s → (Measure.pi fun _ : ι => lf) ((fun x => Bf g *ᵥ x) '' s) = ENNReal.ofReal (|((Algebra.norm ℚ g.det : ℚ) : ℝ)|⁻¹) * (Measure.pi fun _ : ι => lf) s) ∧ ∀ (a : (A F)ˣ) (s : Set (ι → A F)), MeasurableSet s → (Measure.pi fun _ : ι => lf) ((fun x => (a : A F) • x) '' s) = lf ((fun x => (a : A F) * x) '' Oh F) ^ Fintype.card ι * (Measure.pi fun _ : ι => lf) s := by
  intro F _ _ _ _ lf hH h1 ι _ _
  obtain ⟨hlc, hsc, ht2, hOc, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  obtain ⟨hF, -, hU⟩ := GlobalTheory.T.adelic_haar_measure_scaling F lf hH h1
  haveI := hlc
  haveI := hsc
  haveI := ht2
  haveI : SigmaFinite lf := inferInstance
  have hmeas : ∀ (g : Matrix ι ι F), g.det ≠ 0 → ∀ s : Set (ι → A F), MeasurableSet s →
      MeasurableSet ((fun x => Bf g *ᵥ x) '' s) := by
    intro g hg s hs
    rw [image_mulVec_eq_preimage _ _ (Bf_mul_inv g hg) (Bf_inv_mul g hg)]
    exact (continuous_mulVec_left _).measurable hs
  refine ⟨?_, ?_⟩
  · intro g hg
    refine diagonal_transvection_induction_of_det_ne_zero
      (fun g => ∀ s : Set (ι → A F), MeasurableSet s →
        (Measure.pi fun _ : ι => lf) ((fun x => Bf g *ᵥ x) '' s) =
          ENNReal.ofReal (|((Algebra.norm ℚ g.det : ℚ) : ℝ)|⁻¹) *
            (Measure.pi fun _ : ι => lf) s) g hg ?_ ?_ ?_
    · intro D hD s hs
      have hD' : ∀ i, D i ≠ 0 := by
        intro i
        rw [det_diagonal] at hD
        exact Finset.prod_ne_zero_iff.1 hD i (Finset.mem_univ i)
      have hfun : (fun x : ι → A F => Bf (diagonal D) *ᵥ x) =
          fun x i => algebraMap F (A F) (D i) * x i := by
        funext x i
        have : Bf (diagonal D) = diagonal (fun i => algebraMap F (A F) (D i)) := by
          ext a b
          by_cases hab : a = b
          · subst hab; simp [Bf]
          · simp [Bf, hab]
        rw [this, mulVec_diagonal]
      rw [hfun, pi_image_mul lf (fun i => algebraMap F (A F) (D i))
        (fun i => algebraMap F (A F) (D i)⁻¹) ?_
        (fun i => Real.toNNReal (|((Algebra.norm ℚ (D i) : ℚ) : ℝ)|⁻¹)) ?_ s hs]
      · congr 1
        rw [det_diagonal, map_prod, Rat.cast_prod, Finset.abs_prod, ← Finset.prod_inv_distrib,
          ENNReal.ofReal_prod_of_nonneg fun i _ => inv_nonneg.2 (abs_nonneg _)]
        rfl
      · intro i
        rw [← map_mul, mul_inv_cancel₀ (hD' i), map_one]
      · intro i t ht
        exact hF (D i) (hD' i) t ht
    · intro t s hs
      have hdet : t.toMatrix.det = 1 := t.det
      have hinv : Bf t.toMatrix * Bf (transvection t.i t.j (-t.c)) = 1 := by
        rw [← Bf_mul, TransvectionStruct.toMatrix, transvection_mul_transvection_same _ _ t.hij]
        simp [Bf_one]
      have hinv' : Bf (transvection t.i t.j (-t.c)) * Bf t.toMatrix = 1 := by
        rw [← Bf_mul, TransvectionStruct.toMatrix, transvection_mul_transvection_same _ _ t.hij]
        simp [Bf_one]
      have hB : Bf (transvection t.i t.j (-t.c)) =
          transvection t.i t.j (algebraMap F (A F) (-t.c)) := by
        simp [Bf, transvection, Matrix.map_add (f := _), Matrix.map_one]
      rw [image_mulVec_eq_preimage _ _ hinv hinv', hB,
        (measurePreserving_transvection lf t.i t.j t.hij _).measure_preimage hs.nullMeasurableSet,
        hdet]
      simp
    · intro P Q hP hQ IP IQ s hs
      have himg : (fun x => Bf (P * Q) *ᵥ x) '' s =
          (fun x => Bf P *ᵥ x) '' ((fun x => Bf Q *ᵥ x) '' s) := by
        rw [Set.image_image]
        simp [Bf_mul, Matrix.mulVec_mulVec]
      rw [himg, IP _ (hmeas Q hQ s hs), IQ s hs, ← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 (abs_nonneg _)),
        det_mul, map_mul, Rat.cast_mul, abs_mul, mul_inv]
  · intro a s hs
    have hfin : lf ((fun x => (a : A F) * x) '' Oh F) ≠ ∞ :=
      (hOc.image (continuous_const.mul continuous_id)).measure_lt_top.ne
    have hfun : (fun x : ι → A F => (a : A F) • x) = fun x i => (a : A F) * x i := by
      funext x i
      rfl
    rw [hfun, pi_image_mul lf (fun _ => (a : A F)) (fun _ => ((a⁻¹ : (A F)ˣ) : A F)) (fun _ => by simp)
      (fun _ => (lf ((fun x => (a : A F) * x) '' Oh F)).toNNReal) ?_ s hs]
    · simp [ENNReal.coe_toNNReal hfin]
    · intro _ t ht
      rw [ENNReal.coe_toNNReal hfin]
      exact hU a t ht

end GlobalTheory.CompanionTheory.SW.Core.PiScale
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicHaarMeasureLinearChangeStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_haar_measure_linear_change : ∀ (F : Type) [Field F] [NumberField F], ∀ [MeasurableSpace (A F)] [BorelSpace (A F)] (lf : Measure (A F)), lf.IsAddHaarMeasure → lf (Oh F) = 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι], (∀ g : Matrix ι ι F, g.det ≠ 0 → ∀ s : Set (ι → A F), MeasurableSet s → (Measure.pi fun _ : ι => lf) ((fun x => Bf g *ᵥ x) '' s) = ENNReal.ofReal (|((Algebra.norm ℚ g.det : ℚ) : ℝ)|⁻¹) * (Measure.pi fun _ : ι => lf) s) ∧ ∀ (a : (A F)ˣ) (s : Set (ι → A F)), MeasurableSet s → (Measure.pi fun _ : ι => lf) ((fun x => (a : A F) • x) '' s) = lf ((fun x => (a : A F) * x) '' Oh F) ^ Fintype.card ι * (Measure.pi fun _ : ι => lf) s := by
  first | exact @GlobalTheory.CompanionTheory.SW.Core.PiScale.pi_scale | exact GlobalTheory.CompanionTheory.SW.Core.PiScale.pi_scale | (intros; apply GlobalTheory.CompanionTheory.SW.Core.PiScale.pi_scale <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ContDiffOnChartGlobalWhittakerCoefficient
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ContDiffOnChartGlobalWhittakerCoefficient
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.LatCpt

theorem latV_compact_open : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (v : HeightOneSpectrum (𝓞 F)), IsCompact (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) ∧ IsOpen (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) := by
  intro F E _ _ _ _ _ σ hCM d b n M v
  haveI := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
  haveI : LocallyCompactSpace (Fv F v) := inferInstance
  haveI : SecondCountableTopology (Fv F v) := inferInstance
  haveI : T2Space (Fv F v) := inferInstance
  haveI : IsTopologicalRing (Fv F v) := inferInstance
  obtain ⟨-, -, -, -, -, -, hH, -, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Fv F v)
  have hcoord := hH d b
  let H : (Fin n → Fin M → Fv F v ⊗[F] E) ≃ₜ (Fin n → Fin M → Fin d → Fv F v) :=
    Homeomorph.piCongrRight fun _ => Homeomorph.piCongrRight fun _ => hcoord.homeomorph
  let O : Set (Fv F v) := (v.adicCompletionIntegers F : Set (Fv F v))
  have hOc : IsCompact O := GroundTheory.Global.isCompact_adicCompletionIntegers v
  have hOo : IsOpen O := Valued.isOpen_valuationSubring _
  let P : Set (Fin n → Fin M → Fin d → Fv F v) :=
    Set.univ.pi fun _ => Set.univ.pi fun _ => Set.univ.pi fun _ => O
  have hE : (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) = H ⁻¹' P := by
    ext Y
    simp only [latV, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_univ_pi, P, O, SetLike.mem_coe]
    rfl
  have hPc : IsCompact P :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hOc
  have hPo : IsOpen P :=
    isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ =>
      isOpen_set_pi Set.finite_univ fun _ _ => hOo
  rw [hE]
  exact ⟨H.isCompact_preimage.2 hPc, hPo.preimage H.continuous⟩

end GlobalTheory.CompanionTheory.SW.LatCpt
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ContDiffOnChartGlobalWhittakerCoefficientStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiffOn_chart_globalWhittakerCoefficient : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (v : HeightOneSpectrum (𝓞 F)), IsCompact (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) ∧ IsOpen (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.LatCpt.latV_compact_open | exact GlobalTheory.CompanionTheory.SW.LatCpt.latV_compact_open | (intros; apply GlobalTheory.CompanionTheory.SW.LatCpt.latV_compact_open <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.WeilOperatorIntegralInvariance
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.WeilOperatorIntegralInvariance
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.FstarPer

theorem oh_mul {F : Type} [Field F] [NumberField F] {x y : A F} (hx : x ∈ Oh F) (hy : y ∈ Oh F) :
    x * y ∈ Oh F :=
  fun v => mul_mem (hx v) (hy v)

theorem continuous_qf {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι]
    (h : A F) (B : Matrix ι ι (A F)) : Continuous (qf h B) := by
  unfold qf
  exact continuous_const.mul (continuous_id.dotProduct ((continuous_const (y := B)).matrix_mulVec continuous_id))

theorem fstar_periodic : ∀ (F : Type) [Field F] [NumberField F] [MeasurableSpace (A F)] [BorelSpace (A F)] (lf : Measure (A F)), lf.IsAddHaarMeasure → lf (Oh F) = 1 → ∀ ψ : AddChar (A F) ℂ, IsStdChar F ψ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → ∀ φ : (ι → A F) → ℂ, SB φ → ∃ N : ℕ, 0 < N ∧ ∀ x ∈ Oh F, opU ψ (hf F) (Bf B) ((N : A F) * x) φ = φ ∧ ∀ y : A F, fstar ψ (hf F) (Bf B) (muF B lf) φ (y + (N : A F) * x) = fstar ψ (hf F) (Bf B) (muF B lf) φ y := by
  intro F _ _ _ _ lf _ _ ψ hψ ι _ _ M B ρ P _ φ hφ
  have hK : IsCompact (qf (hf F) (Bf B) '' tsupport φ) :=
    IsCompact.image hφ.2 (continuous_qf _ _)
  obtain ⟨N, hN, hNK⟩ := (GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F).2.2.2.2.2.2.2.2.1 _ hK
  have htriv := ((GlobalTheory.T.standard_adelic_character F).2 ψ hψ).2.1
  have key : ∀ x ∈ Oh F, opU ψ (hf F) (Bf B) ((N : A F) * x) φ = φ := by
    intro x hx
    funext u
    by_cases hu : u ∈ tsupport φ
    · have h1 := hNK _ (Set.mem_image_of_mem _ hu)
      have h2 : (N : A F) * x * qf (hf F) (Bf B) u ∈ Oh F := by
        have h3 := oh_mul hx h1
        have h4 : (N : A F) * x * qf (hf F) (Bf B) u = x * ((N : A F) * qf (hf F) (Bf B) u) := by
          ring
        rwa [h4]
      simp [opU, htriv _ h2]
    · have h0 : φ u = 0 := image_eq_zero_of_notMem_tsupport hu
      simp [opU, h0]
  refine ⟨N, hN, fun x hx => ⟨key x hx, fun y => ?_⟩⟩
  unfold fstar
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  have h5 := congrFun (key x hx) u
  simp only [opU] at h5 ⊢
  rw [add_mul, AddChar.map_add_eq_mul, mul_assoc, h5]

end GlobalTheory.CompanionTheory.SW.FstarPer
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.WeilOperatorIntegralInvarianceStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_operator_integral_invariance : ∀ (F : Type) [Field F] [NumberField F] [MeasurableSpace (A F)] [BorelSpace (A F)] (lf : Measure (A F)), lf.IsAddHaarMeasure → lf (Oh F) = 1 → ∀ ψ : AddChar (A F) ℂ, IsStdChar F ψ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → ∀ φ : (ι → A F) → ℂ, SB φ → ∃ N : ℕ, 0 < N ∧ ∀ x ∈ Oh F, opU ψ (hf F) (Bf B) ((N : A F) * x) φ = φ ∧ ∀ y : A F, fstar ψ (hf F) (Bf B) (muF B lf) φ (y + (N : A F) * x) = fstar ψ (hf F) (Bf B) (muF B lf) φ y := by
  first | exact @GlobalTheory.CompanionTheory.SW.FstarPer.fstar_periodic | exact GlobalTheory.CompanionTheory.SW.FstarPer.fstar_periodic | (intros; apply GlobalTheory.CompanionTheory.SW.FstarPer.fstar_periodic <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TraceFormRationalThetaIdentity
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TraceFormRationalThetaIdentity
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.BB.ThetaGauss

theorem continuous_gaussQ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) {M d : ℕ} (b : Module.Basis (Fin d) F E)
    (e : Ainf F ≃+* (InfinitePlace F → ℝ)) (hom : IsHomeomorph e)
    (Pm : InfinitePlace F → Matrix (Fin M × Fin d) (Fin M × Fin d) ℝ) :
    Continuous (gaussQ e b Pm) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hσ.1
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := h4
  obtain ⟨-, -, -, -, -, -, hco, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Ainf F)
  have hxw : ∀ w p, Continuous fun X : Fin 1 → Fin M → Ainf F ⊗[F] E => xw e b X w p := by
    intro w p
    have h := (hco d b).continuous
    exact (continuous_apply w).comp (hom.continuous.comp ((continuous_apply p.2).comp
      (h.comp ((continuous_apply p.1).comp (continuous_apply 0)))))
  have hxw' : ∀ w, Continuous fun X : Fin 1 → Fin M → Ainf F ⊗[F] E => xw e b X w := fun w =>
    continuous_pi (hxw w)
  unfold gaussQ
  refine Real.continuous_exp.comp (continuous_const.mul (continuous_finsetSum _ fun w _ => ?_))
  exact (hxw' w).dotProduct (Continuous.matrix_mulVec continuous_const (hxw' w))

theorem lintegral_thetaMeas_gauss : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (B : Matrix (Fin M × Fin d) (Fin M × Fin d) F), (∀ x : Fin M → E, Algebra.trace F E (hE σ J x x) = (fun p : Fin M × Fin d => b.repr (x p.1) p.2) ⬝ᵥ (B *ᵥ fun p : Fin M × Fin d => b.repr (x p.1) p.2)) → ∀ (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ)), IsHomeomorph e → (∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x) → ∀ (Pm : InfinitePlace F → Matrix (Fin M × Fin d) (Fin M × Fin d) ℝ) (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ (a : ℕ), 0 < a → ∀ β : F, ∫⁻ X in {X | ∀ v, projV v (projFin X) ∈ {X : (Fin 1 → Fin M → Fv F v ⊗[F] E) | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v}}, ENNReal.ofReal (gaussQ e b Pm (projInf X)) ∂(thetaMeas σ J μ 𝓕 {X : Fin 1 → Fin M → E | gramE σ J X = fun _ _ => algebraMap F E β}) = ∫⁻ ω, ∑' x : {x : Fin M × Fin d → F // (1 / 2 : F) * (x ⬝ᵥ (B *ᵥ x)) = β}, Set.indicator {x : Fin M × Fin d → F | ∀ i v, ((a : Af F) * (gfin σ J b ω *ᵥ fun j => algebraMap F (Af F) (x j)) i) v ∈ v.adicCompletionIntegers F} (fun x => ENNReal.ofReal (Real.exp (-Real.pi * ∑ w, (ginf e σ J b ω w *ᵥ fun j => ρ w (x j)) ⬝ᵥ (Pm w *ᵥ (ginf e σ J b ω w *ᵥ fun j => ρ w (x j)))))) x.1 ∂(prH μ 𝓕) := by
  intro F E _ _ _ _ _ σ hσ M J hJ d b B hB ρ e hom hρ Pm μ 𝓕 hμ h𝓕 a ha β
  obtain ⟨⟨h1, h2, h3⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable F
  obtain ⟨hR, -, -, -, -, -, -, hBor, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (AF F)
  haveI := hBor 1 M
  have hA := GlobalTheory.T.measurable_finite_level_lattice_set F E σ hσ d M b a
  have hproj : Continuous (projInf : (Fin 1 → Fin M → AF F ⊗[F] E) → _) :=
    (GlobalTheory.T.adelic_tuple_projections F E σ hσ d b 1 M).1
  have hG : Continuous fun X : Fin 1 → Fin M → AF F ⊗[F] E =>
      ENNReal.ofReal (gaussQ e b Pm (projInf X)) :=
    ENNReal.continuous_ofReal.comp ((continuous_gaussQ σ hσ b e hom Pm).comp hproj)
  rw [← lintegral_indicator hA]
  rw [GlobalTheory.T.theta_integral_over_coordinates F E σ hσ M J hJ d b μ 𝓕 hμ h𝓕
    {x | (1 / 2 : F) * (x ⬝ᵥ (B *ᵥ x)) = β}
    {X | gramE σ J X = fun _ _ => algebraMap F E β}
    (fun x => (GlobalTheory.T.coordinate_bijection_trace_form F E σ hσ M J hJ d b).2.2 B hB β x) _
    (hG.measurable.indicator hA)]
  refine lintegral_congr fun ω => tsum_congr fun x => ?_
  obtain ⟨hinf, hfin⟩ := GlobalTheory.T.infinite_component_coordinates_action F E σ hσ M J hJ d b ρ e hρ ω x.1
  have hmem := GlobalTheory.T.finite_adelic_lattice_membership_iff F E d M b a (projFin (actW (AF F) σ J ω⁻¹ (ratTup (AF F) (ofF b x.1))))
  rw [hfin] at hmem
  have hgauss : gaussQ e b Pm (projInf (actW (AF F) σ J ω⁻¹ (ratTup (AF F) (ofF b x.1)))) =
      Real.exp (-Real.pi * ∑ w, (ginf e σ J b ω w *ᵥ fun j => ρ w (x.1 j)) ⬝ᵥ
        (Pm w *ᵥ (ginf e σ J b ω w *ᵥ fun j => ρ w (x.1 j)))) := by
    simp only [gaussQ, hinf]
  by_cases hx : ∀ i v, ((a : Af F) * (gfin σ J b ω *ᵥ fun j => algebraMap F (Af F) (x.1 j)) i) v ∈
      v.adicCompletionIntegers F
  · rw [Set.indicator_of_mem (by exact hmem.2 hx), Set.indicator_of_mem (by exact hx), hgauss]
  · rw [Set.indicator_of_notMem, Set.indicator_of_notMem]
    all_goals first | exact hx | exact fun h => hx (hmem.1 h)

end GlobalTheory.CompanionTheory.SW.BB.ThetaGauss
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TraceFormRationalThetaIdentityStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_form_rational_theta_identity : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (B : Matrix (Fin M × Fin d) (Fin M × Fin d) F), (∀ x : Fin M → E, Algebra.trace F E (hE σ J x x) = (fun p : Fin M × Fin d => b.repr (x p.1) p.2) ⬝ᵥ (B *ᵥ fun p : Fin M × Fin d => b.repr (x p.1) p.2)) → ∀ (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ)), IsHomeomorph e → (∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x) → ∀ (Pm : InfinitePlace F → Matrix (Fin M × Fin d) (Fin M × Fin d) ℝ) (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ (a : ℕ), 0 < a → ∀ β : F, ∫⁻ X in {X | ∀ v, projV v (projFin X) ∈ {X : (Fin 1 → Fin M → Fv F v ⊗[F] E) | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v}}, ENNReal.ofReal (gaussQ e b Pm (projInf X)) ∂(thetaMeas σ J μ 𝓕 {X : Fin 1 → Fin M → E | gramE σ J X = fun _ _ => algebraMap F E β}) = ∫⁻ ω, ∑' x : {x : Fin M × Fin d → F // (1 / 2 : F) * (x ⬝ᵥ (B *ᵥ x)) = β}, Set.indicator {x : Fin M × Fin d → F | ∀ i v, ((a : Af F) * (gfin σ J b ω *ᵥ fun j => algebraMap F (Af F) (x j)) i) v ∈ v.adicCompletionIntegers F} (fun x => ENNReal.ofReal (Real.exp (-Real.pi * ∑ w, (ginf e σ J b ω w *ᵥ fun j => ρ w (x j)) ⬝ᵥ (Pm w *ᵥ (ginf e σ J b ω w *ᵥ fun j => ρ w (x j)))))) x.1 ∂(prH μ 𝓕) := by
  first | exact @GlobalTheory.CompanionTheory.SW.BB.ThetaGauss.lintegral_thetaMeas_gauss | exact GlobalTheory.CompanionTheory.SW.BB.ThetaGauss.lintegral_thetaMeas_gauss | (intros; apply GlobalTheory.CompanionTheory.SW.BB.ThetaGauss.lintegral_thetaMeas_gauss <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaAverageIntegralFormula
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaAverageIntegralFormula
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

namespace GlobalTheory.CompanionTheory.SW.Core.ThetaIntegral

theorem thTerm_zero {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ)
    (gf : Matrix ι ι (A F)) (gi : InfinitePlace F → Matrix ι ι ℝ) (φ : (ι → A F) → ℂ)
    (τ : InfinitePlace F → ℂ) : thTerm B ρ P gf gi φ τ 0 = φ 0 := by
  have h1 : (fun j : ι => algebraMap F (A F) ((0 : ι → F) j)) = 0 := by
    funext j; simp
  have h2 : ∀ w, (fun j : ι => ρ w ((0 : ι → F) j)) = 0 := by
    intro w; funext j; simp
  simp only [thTerm, gauss, h1, h2, mulVec_zero]
  simp

theorem main : ∀ (F : Type) [Field F] [NumberField F] [MeasurableSpace (A F)] [BorelSpace (A F)] (lf : Measure (A F)), lf.IsAddHaarMeasure → lf (Oh F) = 1 → ∀ ψ : AddChar (A F) ℂ, IsStdChar F ψ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → ∀ (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) (gf : Ω → Matrix ι ι (A F)) (gi : Ω → InfinitePlace F → Matrix ι ι ℝ), CountData M B ρ Pr gf gi → ∀ φ τ, SB φ → (∀ w, 0 < (τ w).im) → Integrable (fun ω => theta B ρ P (gf ω) (gi ω) φ τ) Pr ∧ ENNReal.ofReal ‖(∫ ω, theta B ρ P (gf ω) (gi ω) φ τ ∂Pr) - φ 0‖ ≤ ∫⁻ ω, ∑' x : {x : ι → F // x ≠ 0}, ‖thTerm B ρ P (gf ω) (gi ω) φ τ x.1‖ₑ ∂Pr := by
  intro F _ _ _ _ lf _ _ ψ _ ι _ _ M B ρ P hQ Ω _ Pr gf gi hC φ τ hφ hτ
  haveI : IsProbabilityMeasure Pr := hC.1
  have horth : ∀ ω, IsOrth B ρ (gf ω) (gi ω) := hC.2.2.2.1
  haveI : Countable F :=
    Function.Injective.countable (Module.finBasis ℚ F).equivFun.injective
  obtain ⟨w0, -, h0⟩ := Finset.exists_min_image Finset.univ (fun w => (τ w).im) Finset.univ_nonempty
  obtain ⟨w1, -, h1⟩ := Finset.exists_max_image Finset.univ (fun w => (τ w).im) Finset.univ_nonempty
  have ht : 0 < (τ w0).im := hτ w0
  have hs : 0 < (τ w1).im := hτ w1
  obtain ⟨C, hCb⟩ := GlobalTheory.T.weighted_theta_average_le_of_countData F ι M B ρ P hQ Ω Pr gf gi hC φ hφ
    ((τ w0).im / (τ w1).im) (τ w0).im (div_pos ht hs) ht
  obtain ⟨hmeas, hbd⟩ := hCb τ (fun w => h0 w (Finset.mem_univ w)) (by
    intro v w
    have hw : (τ w).im ≤ (τ w1).im := h1 w (Finset.mem_univ w)
    have hv : (τ w0).im ≤ (τ v).im := h0 v (Finset.mem_univ v)
    calc (τ w0).im / (τ w1).im * (τ w).im ≤ (τ w0).im / (τ w1).im * (τ w1).im :=
          mul_le_mul_of_nonneg_left hw (div_pos ht hs).le
      _ = (τ w0).im := div_mul_cancel₀ _ hs.ne'
      _ ≤ (τ v).im := hv)
  have hwt : 0 < wt M τ := Finset.prod_pos fun w _ => pow_pos (Real.sqrt_pos.2 (hτ w)) M
  have hfin : (∫⁻ ω, ∑' x : {x : ι → F // x ≠ 0}, ‖thTerm B ρ P (gf ω) (gi ω) φ τ x.1‖ₑ ∂Pr) ≠ ∞ := by
    intro h
    rw [h, ENNReal.mul_top (by simpa using hwt)] at hbd
    simp at hbd
  have hsum : ∀ ω, Summable (thTerm B ρ P (gf ω) (gi ω) φ τ) := fun ω =>
    ((GlobalTheory.T.theta_series_summable F ι M B ρ P hQ (gf ω) (gi ω) (horth ω) τ hτ).1 φ hφ).of_norm
  have hsub : ∀ ω, Summable fun x : {x : ι → F // x ≠ 0} => thTerm B ρ P (gf ω) (gi ω) φ τ x.1 :=
    fun ω => (hsum ω).subtype _
  set g : Ω → ℂ := fun ω => ∑' x : {x : ι → F // x ≠ 0}, thTerm B ρ P (gf ω) (gi ω) φ τ x.1 with hg
  have hsplit : ∀ ω, theta B ρ P (gf ω) (gi ω) φ τ = φ 0 + g ω := by
    intro ω
    have h := (hsum ω).tsum_subtype_add_tsum_subtype_compl ({0} : Set (ι → F))
    rw [tsum_singleton, thTerm_zero] at h
    exact h.symm
  have hgm : Measurable g :=
    measurable_of_tendsto_metrizable' Filter.atTop
      (f := fun (s : Finset {x : ι → F // x ≠ 0}) ω => ∑ x ∈ s, thTerm B ρ P (gf ω) (gi ω) φ τ x.1)
      (fun s => Finset.measurable_sum _ fun x _ => hmeas x.1)
      (tendsto_pi_nhds.2 fun ω => (hsub ω).hasSum)
  have hgI : ∫⁻ ω, ‖g ω‖ₑ ∂Pr ≤
      ∫⁻ ω, ∑' x : {x : ι → F // x ≠ 0}, ‖thTerm B ρ P (gf ω) (gi ω) φ τ x.1‖ₑ ∂Pr :=
    lintegral_mono fun ω => enorm_tsum_le_tsum_enorm
  have hgint : Integrable g Pr := ⟨hgm.aestronglyMeasurable, lt_of_le_of_lt hgI hfin.lt_top⟩
  have hth : (fun ω => theta B ρ P (gf ω) (gi ω) φ τ) = fun ω => φ 0 + g ω := funext hsplit
  refine ⟨by rw [hth]; exact (integrable_const _).add hgint, ?_⟩
  have hint : (∫ ω, theta B ρ P (gf ω) (gi ω) φ τ ∂Pr) - φ 0 = ∫ ω, g ω ∂Pr := by
    rw [hth, integral_add (integrable_const _) hgint]
    simp
  rw [hint, ofReal_norm_eq_enorm]
  exact (enorm_integral_le_lintegral_enorm g).trans hgI

end GlobalTheory.CompanionTheory.SW.Core.ThetaIntegral
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaAverageIntegralFormulaStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_average_integral_formula : ∀ (F : Type) [Field F] [NumberField F] [MeasurableSpace (A F)] [BorelSpace (A F)] (lf : Measure (A F)), lf.IsAddHaarMeasure → lf (Oh F) = 1 → ∀ ψ : AddChar (A F) ℂ, IsStdChar F ψ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → ∀ (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) (gf : Ω → Matrix ι ι (A F)) (gi : Ω → InfinitePlace F → Matrix ι ι ℝ), CountData M B ρ Pr gf gi → ∀ φ τ, SB φ → (∀ w, 0 < (τ w).im) → Integrable (fun ω => theta B ρ P (gf ω) (gi ω) φ τ) Pr ∧ ENNReal.ofReal ‖(∫ ω, theta B ρ P (gf ω) (gi ω) φ τ ∂Pr) - φ 0‖ ≤ ∫⁻ ω, ∑' x : {x : ι → F // x ≠ 0}, ‖thTerm B ρ P (gf ω) (gi ω) φ τ x.1‖ₑ ∂Pr := by
  first | exact @GlobalTheory.CompanionTheory.SW.Core.ThetaIntegral.main | exact GlobalTheory.CompanionTheory.SW.Core.ThetaIntegral.main | (intros; apply GlobalTheory.CompanionTheory.SW.Core.ThetaIntegral.main <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.EulerProductMeasureTransport
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.EulerProductMeasureTransport
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.EulerMove

theorem borel_ainf (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (n M : ℕ) :
    BorelSpace (Fin n → Fin M → Ainf F ⊗[F] E) := by
  obtain ⟨⟨-, scA, -⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  have scA' : SecondCountableTopology (Ainf F × Af F) := scA
  haveI : SecondCountableTopology (Ainf F) :=
    (isEmbedding_prodMkLeft (0 : Af F)).secondCountableTopology
  haveI : T2Space (Ainf F) := GlobalTheory.CompanionTheory.AdeleTop.t2Space_infiniteAdeleRing_of_numberField_field F
  exact (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Ainf F)).2.2.2.2.2.2.2.1 n M

theorem borel_af (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (n M : ℕ) :
    BorelSpace (Fin n → Fin M → AF F ⊗[F] E) := by
  obtain ⟨⟨lcA, scA, t2A⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI := lcA
  haveI := scA
  haveI := t2A
  exact (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (AF F)).2.2.2.2.2.2.2.1 n M

theorem borel_fv (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (n M : ℕ) (v : HeightOneSpectrum (𝓞 F)) :
    BorelSpace (Fin n → Fin M → Fv F v ⊗[F] E) := by
  haveI := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
  haveI : LocallyCompactSpace (Fv F v) := inferInstance
  haveI : SecondCountableTopology (Fv F v) := inferInstance
  haveI : T2Space (Fv F v) := inferInstance
  exact (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)).2.2.2.2.2.2.2.1 n M

theorem euler_move : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (I : Measure (Fin n → Fin M → AF F ⊗[F] E)) (minf minf' : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (m m' : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (e : (Fin n → Fin M → AF F ⊗[F] E) → (Fin n → Fin M → AF F ⊗[F] E)) (einf : (Fin n → Fin M → Ainf F ⊗[F] E) → (Fin n → Fin M → Ainf F ⊗[F] E)) (ev : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → (Fin n → Fin M → Fv F v ⊗[F] E)), Measurable e → Measurable einf → (∀ v, Measurable (ev v)) → (∀ X, projInf (e X) = einf (projInf X) ∧ ∀ v, projV v (projFin (e X)) = ev v (projV v (projFin X))) → (∀ᶠ v in Filter.cofinite, ∀ X, ev v X ∈ latV b v ↔ X ∈ latV b v) → ∀ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c → minf.map einf = cinf • minf' → (∀ v, (m v).map (ev v) = c v • m' v) → (∀ v, m' v (latV b v) < ⊤) → IsEulerProd b I 1 minf m → IsEulerProd b (I.map e) 1 minf' m' := by
  intro F E _ _ _ _ _ σ hσ d b n M I minf minf' m m' e einf ev he heinf hev hcomm hgood cinf c hU
    hinf hloc hfin hE
  classical
  obtain ⟨-, hsum, S₀, hS₀⟩ := hE
  obtain ⟨hpi, hpf, hpv, hlat, hint, -⟩ := GlobalTheory.CompanionTheory.SW.MeasProj.proj_props F E σ hσ d b n M
  haveI := borel_af F E σ hσ n M
  haveI := borel_ainf F E σ hσ n M
  haveI : ∀ v, BorelSpace (Fin n → Fin M → Fv F v ⊗[F] E) := fun v => borel_fv F E σ hσ n M v
  obtain ⟨S₁, hS₁⟩ := (GlobalTheory.CompanionTheory.SW.UnitProdAlg.main F cinf cinf c c hU hU).2.2.2.2.2.2.2
  let S₂ : Finset (HeightOneSpectrum (𝓞 F)) := (Filter.eventually_cofinite.1 hgood).toFinset
  have hS₂ : ∀ v, v ∉ S₂ → ∀ X, ev v X ∈ latV b v ↔ X ∈ latV b v := by
    intro v hv
    by_contra h
    exact hv (by simpa [S₂] using h)
  have hlatM : ∀ v, MeasurableSet (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) :=
    fun v => (hlat v).2.measurableSet
  have hcv : ∀ v, v ∉ S₁ ∪ S₂ → c v = 1 := fun v hv =>
    ((hS₁ (S₁ ∪ S₂) Finset.subset_union_left).1 v hv)
  have hmm : ∀ v, v ∉ S₁ ∪ S₂ → m' v (latV b v) = m v (latV b v) := by
    intro v hv
    have hv₂ : v ∉ S₂ := fun h => hv (Finset.mem_union_right _ h)
    have h1 := congrArg (fun μ => μ (latV b v)) (hloc v)
    simp only [Measure.map_apply (hev v) (hlatM v), hcv v hv, one_smul] at h1
    rw [← h1]
    congr 1
    ext X
    exact hS₂ v hv₂ X
  refine ⟨hfin, ?_, S₀ ∪ (S₁ ∪ S₂), ?_⟩
  · refine hsum.congr_cofinite ?_
    have hfinite : (↑(S₁ ∪ S₂) : Set (HeightOneSpectrum (𝓞 F))).Finite := Finset.finite_toSet (S₁ ∪ S₂)
    filter_upwards [hfinite.compl_mem_cofinite] with v hv
    rw [hmm v (by simpa using hv)]
  · intro S hS φinf φ hφinf hφ
    have hSS₀ : S₀ ⊆ S := Finset.union_subset_left hS
    have hSS₃ : S₁ ∪ S₂ ⊆ S := Finset.union_subset_right hS
    have hSS₁ : S₁ ⊆ S := Finset.union_subset_left hSS₃
    have hnot : ∀ v, v ∉ S → v ∉ S₁ ∪ S₂ := fun v hv h => hv (hSS₃ h)
    have hpm : Measurable (pureL b S φinf φ) := by
      refine Measurable.indicator ?_ (hint S).measurableSet
      refine (hφinf.comp hpi.measurable).mul ?_
      refine Finset.measurable_prod _ fun v _ => ?_
      exact (hφ v).comp ((hpv v).comp hpf).measurable
    have hmem : ∀ X, e X ∈ intOff b S ↔ X ∈ intOff b S := by
      intro X
      refine forall_congr' fun v => ?_
      refine imp_congr_right fun hv => ?_
      rw [(hcomm X).2 v]
      exact hS₂ v (fun h => hnot v hv (Finset.mem_union_right _ h)) _
    have hfun : (fun X => pureL b S φinf φ (e X)) =
        pureL b S (fun Y => φinf (einf Y)) (fun v Y => φ v (ev v Y)) := by
      funext X
      unfold pureL
      by_cases hX : X ∈ intOff b S
      · rw [Set.indicator_of_mem ((hmem X).2 hX), Set.indicator_of_mem hX, (hcomm X).1]
        congr 1
        exact Finset.prod_congr rfl fun v _ => by rw [(hcomm X).2 v]
      · rw [Set.indicator_of_notMem (fun h => hX ((hmem X).1 h)), Set.indicator_of_notMem hX]
    have hinfI : ∫⁻ Y, φinf (einf Y) ∂minf = (cinf : ℝ≥0∞) * ∫⁻ Y, φinf Y ∂minf' := by
      rw [← lintegral_map hφinf heinf, hinf, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]
    have hvI : ∀ v, ∫⁻ Y, φ v (ev v Y) ∂(m v) = (c v : ℝ≥0∞) * ∫⁻ Y, φ v Y ∂(m' v) := by
      intro v
      rw [← lintegral_map (hφ v) (hev v), hloc v, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]
    have hone : (cinf : ℝ≥0∞) * ∏ v ∈ S, (c v : ℝ≥0∞) = 1 := by
      have := (hS₁ S hSS₁).2
      exact_mod_cast this
    have htail : (∏' v : {v // v ∉ S}, (m v.1 (latV b v.1)).toReal) =
        ∏' v : {v // v ∉ S}, (m' v.1 (latV b v.1)).toReal :=
      tprod_congr fun v => by rw [hmm v.1 (hnot v.1 v.2)]
    rw [lintegral_map hpm he, hfun,
      hS₀ S hSS₀ (fun Y => φinf (einf Y)) (fun v Y => φ v (ev v Y)) (hφinf.comp heinf)
        (fun v => (hφ v).comp (hev v)), hinfI, htail]
    simp only [hvI]
    rw [Finset.prod_mul_distrib]
    congr 2
    calc (cinf : ℝ≥0∞) * (∫⁻ Y, φinf Y ∂minf') *
          ((∏ v ∈ S, (c v : ℝ≥0∞)) * ∏ v ∈ S, ∫⁻ Y, φ v Y ∂(m' v))
        = ((cinf : ℝ≥0∞) * ∏ v ∈ S, (c v : ℝ≥0∞)) *
            ((∫⁻ Y, φinf Y ∂minf') * ∏ v ∈ S, ∫⁻ Y, φ v Y ∂(m' v)) := by ring
      _ = _ := by rw [hone, one_mul]

end GlobalTheory.CompanionTheory.SW.EulerMove
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.EulerProductMeasureTransportStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.euler_product_measure_transport : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (I : Measure (Fin n → Fin M → AF F ⊗[F] E)) (minf minf' : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (m m' : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (e : (Fin n → Fin M → AF F ⊗[F] E) → (Fin n → Fin M → AF F ⊗[F] E)) (einf : (Fin n → Fin M → Ainf F ⊗[F] E) → (Fin n → Fin M → Ainf F ⊗[F] E)) (ev : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → (Fin n → Fin M → Fv F v ⊗[F] E)), Measurable e → Measurable einf → (∀ v, Measurable (ev v)) → (∀ X, projInf (e X) = einf (projInf X) ∧ ∀ v, projV v (projFin (e X)) = ev v (projV v (projFin X))) → (∀ᶠ v in Filter.cofinite, ∀ X, ev v X ∈ latV b v ↔ X ∈ latV b v) → ∀ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c → minf.map einf = cinf • minf' → (∀ v, (m v).map (ev v) = c v • m' v) → (∀ v, m' v (latV b v) < ⊤) → IsEulerProd b I 1 minf m → IsEulerProd b (I.map e) 1 minf' m' := by
  first | exact @GlobalTheory.CompanionTheory.SW.EulerMove.euler_move | exact GlobalTheory.CompanionTheory.SW.EulerMove.euler_move | (intros; apply GlobalTheory.CompanionTheory.SW.EulerMove.euler_move <;> assumption)
end
end
