module

public import Development.WeilBound.CoreStatements.ThetaDilations.SdTransport
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FibreMassEq
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ArchimedeanFrameKTypeDecomposition
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanBinaryGramDensity
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullOWOverComp

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanBinaryGramIntegral
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanBinaryGramIntegral
open PositivityTheory.Rg.Mass
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped TensorProduct ENNReal NNReal

noncomputable section
namespace GlobalTheory.CompanionTheory.BinaryDil

theorem fibre_unit_dilation : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 0 < M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)), laminf.IsAddHaarMeasure → ∀ (minf : HermR (Ainf F) σ 1 → Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)), GlobalTheory.CompanionTheory.SW.IsGramFib (Ainf F) σ J 1 (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b laminf 1 M) (GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf 1) minf → ∀ (e : Ainf F ≃+* (InfinitePlace F → ℝ)), IsHomeomorph e → ∀ s t : Ainf F, IsUnit t → minf (GlobalTheory.CompanionTheory.SW.hermScal (Ainf F) σ (t ^ 2 * s)) = ((∏ w, ‖e t w‖₊) ^ (2 * M - 2)) • (minf (GlobalTheory.CompanionTheory.SW.hermScal (Ainf F) σ s)).map (fun X p i => algebraMap (Ainf F) (Ainf F ⊗[F] E) t * X p i) := by
  intro F E _ _ _ _ _ σ hσ M J hJ hM d b lam hlam m hm e he s t ht
  have hloc : GlobalTheory.CompanionTheory.SW.IsLocR (Ainf F) := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hσ.1
  obtain ⟨i1, i2, i3, i4, i5, -, -, hB, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Ainf F)
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI : BorelSpace (Ainf F ⊗[F] E) := ⟨rfl⟩
  obtain ⟨-, hW, hH⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hσ (Ainf F) d b lam hlam
  have hd : d = 2 := by
    rw [← hσ.2.2.1, Module.finrank_eq_card_basis b, Fintype.card_fin]
  subst hd
  set N : ℝ≥0 := ∏ w, ‖e t w‖₊ with hN
  have hN0 : N ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun w _ => ?_
    have : IsUnit (e t) := ht.map e
    exact nnnorm_ne_zero_iff.2 (Pi.isUnit_iff.1 this w).ne_zero
  have hN2 : ∏ w, ‖e (t ^ 2) w‖₊ = N ^ 2 := by
    rw [hN, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun w _ => ?_
    simp [map_pow]
  have hs1 := GlobalTheory.T.archimedean_haar_scaling_norm F e he lam hlam t ht
  have hs2 := GlobalTheory.T.archimedean_haar_scaling_norm F e he lam hlam (t ^ 2) (ht.pow 2)
  rw [hN2] at hs2
  have hk := GlobalTheory.T.coordinate_measure_scaling_tensor F E σ hσ M 2 b lam hlam t ht _ hs1
  let g : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E) := Matrix.of fun _ _ => algebraMap (Ainf F) (Ainf F ⊗[F] E) t
  have hg : IsUnit g.det := by
    rw [Matrix.det_fin_one]
    exact ht.map (algebraMap (Ainf F) (Ainf F ⊗[F] E))
  have hrm : (fun X : Fin 1 → Fin M → Ainf F ⊗[F] E => GlobalTheory.CompanionTheory.SW.rmul (Ainf F) X g) =
      fun X p i => algebraMap (Ainf F) (Ainf F ⊗[F] E) t * X p i := by
    funext X p i
    simp only [GlobalTheory.CompanionTheory.SW.rmul, Fin.sum_univ_one, g, Matrix.of_apply]
    rw [Subsingleton.elim p 0, mul_comm]
  have hsig : sigR (Ainf F) σ (algebraMap (Ainf F) (Ainf F ⊗[F] E) t) = algebraMap (Ainf F) (Ainf F ⊗[F] E) t := by
    simp [sigR, Algebra.TensorProduct.algebraMap_apply]
  let τ : HermR (Ainf F) σ 1 → HermR (Ainf F) σ 1 := fun S =>
    ⟨fun i j => algebraMap (Ainf F) (Ainf F ⊗[F] E) (t ^ 2) * (S : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)) i j, by
      intro i j
      have := S.2 i j
      show sigR (Ainf F) σ (_ * _) = _ * _
      rw [map_mul, this, map_pow, map_pow, hsig]⟩
  have hτe : ∀ S i j, (τ S : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)) i j =
      algebraMap (Ainf F) (Ainf F ⊗[F] E) (t ^ 2) * (S : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)) i j := fun _ _ _ => rfl
  have hτm : Measurable τ := by
    haveI : BorelSpace (HermR (Ainf F) σ 1) := ⟨rfl⟩
    have : Continuous τ := by
      refine Continuous.subtype_mk ?_ _
      refine continuous_pi fun i => continuous_pi fun j => ?_
      exact continuous_const.mul ((continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val))
    exact this.measurable
  have hc := GlobalTheory.T.hermitian_measure_scaling_transform F E σ hσ 2 b lam hlam (t ^ 2) (ht.pow 2) _ hs2 τ hτm hτe
  have hτ : ∀ S, (τ S : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)) = HeckeCharacterZeroLocus.SiegelWeilU.cT (sigR (Ainf F) σ) g * S * g := by
    intro S
    ext i j
    rw [hτe, map_pow, GlobalTheory.CompanionTheory.SW.Dil.cT_scalar _ _ hsig]
  have key := GlobalTheory.T.gram_fiber_measures_rmul_equivariant F E σ hσ M J hJ (Ainf F) hloc 1 (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b lam 1 M)
    (GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b lam 1) m (hW 1 M) (hH 1) hm g hg τ hτ _ _
    (by rw [hrm]; exact hk) hc (GlobalTheory.CompanionTheory.SW.hermScal (Ainf F) σ s)
  have hτs : τ (GlobalTheory.CompanionTheory.SW.hermScal (Ainf F) σ s) = GlobalTheory.CompanionTheory.SW.hermScal (Ainf F) σ (t ^ 2 * s) := by
    apply Subtype.ext
    funext i j
    change algebraMap (Ainf F) (Ainf F ⊗[F] E) (t ^ 2) * (s ⊗ₜ[F] (1 : E)) = (t ^ 2 * s) ⊗ₜ[F] (1 : E)
    simp [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]
  rw [hτs, hrm] at key
  have e1 : (N ^ (2 * M)) * (N⁻¹ ^ (2 * M)) = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hN0, one_pow]
  have e2 : (N ^ (2 * M)) * (N ^ 2)⁻¹ = N ^ (2 * M - 2) := by
    obtain ⟨k, rfl⟩ : ∃ k, M = k + 1 := ⟨M - 1, by omega⟩
    have : 2 * (k + 1) = 2 * k + 2 := by ring
    rw [this, pow_add, mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hN0), mul_one]
    simp
  have key2 := congrArg (fun μ' => (N ^ (2 * M)) • μ') key
  simp only [smul_smul] at key2
  rw [e1, e2, one_smul] at key2
  exact key2

theorem dilation_inf_binary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (J : Matrix (Fin 2) (Fin 2) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (li : Measure (Ainf F)), IsStdInf li →
  ∀ (mi : HermR (Ainf F) σ 1 → Measure (Fin 1 → Fin 2 → Ainf F ⊗[F] E)),
  IsGramFib (Ainf F) σ J 1 (coordW (Ainf F) b li 1 2) (coordHerm (Ainf F) σ b li 1) mi →
  ∀ θ : ℝ →+* Ainf F, Continuous θ → ∀ ε : ℝ, 0 < ε → ∀ (s : Ainf F) (φ : (Fin 1 → Fin 2 → Ainf F ⊗[F] E) → ℝ), Continuous φ →
  ENNReal.ofReal (ε ^ (4 * Module.finrank ℚ F)) * ∫⁻ X, ENNReal.ofReal (φ (PositivityTheory.Rg.Mass.dil θ ε X)) ∂(mi (hermScal (Ainf F) σ s)) =
    ENNReal.ofReal ((ε ^ 2) ^ Module.finrank ℚ F) * ∫⁻ X, ENNReal.ofReal (φ X) ∂(mi (hermScal (Ainf F) σ (θ (ε ^ 2) * s))) := by
  intro F E _ _ _ _ _ σ hσ J hJ d b li hli mi hm θ hθ ε hε s φ hφ
  obtain ⟨-, e, -, he, -, habs, -⟩ := GlobalTheory.T.infinite_adele_haar_map_eq_scaled_volume F hσ.1
  obtain ⟨i1, i2, i3, i4, -, -, -, hB, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Ainf F)
  haveI : BorelSpace (Fin 1 → Fin 2 → Ainf F ⊗[F] E) := hB 1 2
  set t : Ainf F := θ ε with ht_def
  have ht : IsUnit t := (isUnit_iff_ne_zero.2 hε.ne').map θ
  have key := fibre_unit_dilation F E σ hσ 2 J hJ (by norm_num) d b li hli.1 mi hm e he s t ht
  set n := Module.finrank ℚ F with hn
  have hw : ∀ w, ‖e t w‖₊ = ε.toNNReal := by
    intro w
    have h1 := (PositivityTheory.PlacePermOperatorBicommutantSpan.theta_real F hσ.1).2 θ hθ ε w
    have h2 := habs t w
    apply NNReal.eq
    rw [coe_nnnorm, Real.norm_eq_abs, h2, Real.coe_toNNReal _ hε.le]
    rw [show ‖t w‖ = ‖θ ε w‖ from rfl, h1, abs_of_pos hε]
  have hN : ∏ w, ‖e t w‖₊ = ε.toNNReal ^ n := by
    have hc : Fintype.card (InfinitePlace F) = n := by
      have := hσ.1
      rw [hn, IsTotallyReal.finrank F, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
        IsTotallyReal.nrComplexPlaces_eq_zero, add_zero]
    rw [Finset.prod_congr rfl fun w _ => hw w, Finset.prod_const, Finset.card_univ, hc]
  have hs : θ (ε ^ 2) * s = t ^ 2 * s := by rw [map_pow]
  have hD : Continuous (fun (X : Fin 1 → Fin 2 → Ainf F ⊗[F] E) p i => algebraMap (Ainf F) (Ainf F ⊗[F] E) t * X p i) :=
    continuous_pi fun p => continuous_pi fun i =>
      continuous_const.mul ((continuous_apply i).comp (continuous_apply p))
  have hf : Measurable (fun X => ENNReal.ofReal (φ X)) := hφ.measurable.ennreal_ofReal
  rw [hs, key, lintegral_smul_measure, lintegral_map hf hD.measurable, hN]
  have hdil : ∀ X, PositivityTheory.Rg.Mass.dil θ ε X = fun p i => algebraMap (Ainf F) (Ainf F ⊗[F] E) t * X p i := by
    intro X
    funext p i
    simp [PositivityTheory.Rg.Mass.dil, Algebra.TensorProduct.algebraMap_apply, ht_def]
  simp only [hdil]
  rw [ENNReal.smul_def, smul_eq_mul, ← mul_assoc]
  congr 1
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  simp only [NNReal.coe_pow, Real.coe_toNNReal _ hε.le]
  ring

end GlobalTheory.CompanionTheory.BinaryDil

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanBinaryGramIntegralStatement
open PositivityTheory.Rg.Mass
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped TensorProduct ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_binary_gram_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (J : Matrix (Fin 2) (Fin 2) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (li : Measure (Ainf F)), IsStdInf li →
  ∀ (mi : HermR (Ainf F) σ 1 → Measure (Fin 1 → Fin 2 → Ainf F ⊗[F] E)),
  IsGramFib (Ainf F) σ J 1 (coordW (Ainf F) b li 1 2) (coordHerm (Ainf F) σ b li 1) mi →
  ∀ θ : ℝ →+* Ainf F, Continuous θ → ∀ ε : ℝ, 0 < ε → ∀ (s : Ainf F) (φ : (Fin 1 → Fin 2 → Ainf F ⊗[F] E) → ℝ), Continuous φ →
  ENNReal.ofReal (ε ^ (4 * Module.finrank ℚ F)) * ∫⁻ X, ENNReal.ofReal (φ (PositivityTheory.Rg.Mass.dil θ ε X)) ∂(mi (hermScal (Ainf F) σ s)) =
    ENNReal.ofReal ((ε ^ 2) ^ Module.finrank ℚ F) * ∫⁻ X, ENNReal.ofReal (φ X) ∂(mi (hermScal (Ainf F) σ (θ (ε ^ 2) * s))) := by
  first | exact @GlobalTheory.CompanionTheory.BinaryDil.dilation_inf_binary | exact GlobalTheory.CompanionTheory.BinaryDil.dilation_inf_binary | (intros; apply GlobalTheory.CompanionTheory.BinaryDil.dilation_inf_binary <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalBinaryGramDensity
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarMeasureNonunitsNull
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_measure_nonunits_null : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 1 ≤ M → ∀ (v : HeightOneSpectrum (𝓞 F)) (μ : Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)) (ν : Measure (Fv F v)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ν {c | ¬ IsUnit c} = 0 ∧ μ {X | ¬ IsUnit ((fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (Fv F v) σ J (X 0)) X)} = 0 := by
  first | exact @GlobalTheory.CompanionTheory.SW.NullV.null_nonunits | exact GlobalTheory.CompanionTheory.SW.NullV.null_nonunits | (intros; apply GlobalTheory.CompanionTheory.SW.NullV.null_nonunits <;> assumption)
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalBinaryGramDensity
open PositivityTheory.Rg.Mass
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped TensorProduct ENNReal NNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.StdLat

theorem fibre_masses_standard_lattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (J : Matrix (Fin 2) (Fin 2) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
  (lam : Measure (Fv F v)), IsStdV v lam → ∀ (m : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin 2 → Fv F v ⊗[F] E)),
  IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b lam 1 2) (coordHerm (Fv F v) σ b lam 1) m →
  ContinuousOn (fun s : Fv F v => (m (hermScal (Fv F v) σ s) (latV b v)).toReal) {0}ᶜ ∧
  ∫ s, (m (hermScal (Fv F v) σ s) (latV b v)).toReal ∂lam = 1 := by
  intro F E _ _ _ _ _ σ hCM J hJ d b v lam hlam m hm
  classical
  have hloc : IsLocR (Fv F v) := GlobalTheory.T.completion_is_local_ring F v
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI : IsTopologicalRing (Fv F v) := hloc.1
  haveI : LocallyCompactSpace (Fv F v) := hloc.2.1
  haveI : SecondCountableTopology (Fv F v) := hloc.2.2.1
  haveI : T2Space (Fv F v) := hloc.2.2.2.1
  haveI := hlam.1
  obtain ⟨-, -, -, hT2K, -, htr, -, hBorW, -, hgr⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (Fv F v)
  haveI := hT2K
  obtain ⟨-, hW, hH⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hCM (Fv F v) d b lam hlam.1
  obtain ⟨hLc, hLo, -, hL1⟩ := GlobalTheory.T.local_lattice_compact_open_unit_volume F E σ hCM d b 1 2 v
  obtain ⟨hSh, -, hSm⟩ := GlobalTheory.CompanionTheory.SW.hermScal_main F E σ hCM (Fv F v) d b
  haveI : BorelSpace (Fin 1 → Fin 2 → Fv F v ⊗[F] E) := hBorW 1 2
  haveI : BorelSpace (HermR (Fv F v) σ 1) := ⟨rfl⟩
  have hLm : MeasurableSet (latV (M := 2) (n := 1) b v) := hLo.measurableSet
  obtain ⟨φ, hφ⟩ : ∃ φ : (Fin 1 → Fin 2 → Fv F v ⊗[F] E) → ℂ,
      φ = (latV b v).indicator (fun _ => (1 : ℂ)) := ⟨_, rfl⟩
  have hcl : IsClopen (latV (M := 2) (n := 1) b v) := ⟨hLc.isClosed, hLo⟩
  have hφc : Continuous φ := by
    rw [hφ]
    exact Continuous.indicator (fun a ha => by
      rw [hcl.frontier_eq] at ha; exact absurd ha (Set.notMem_empty a)) continuous_const
  have hφs : HasCompactSupport φ := by
    rw [hφ]
    exact HasCompactSupport.intro hLc (fun x hx => Set.indicator_of_notMem hx _)
  obtain ⟨⟨hgc, -⟩, -⟩ := GlobalTheory.T.gram_fiber_integral_isContDensityOn F E σ hCM 2 J hJ (Fv F v) hloc 1
    (coordW (Fv F v) b lam 1 2) (coordHerm (Fv F v) σ b lam 1) m (hW 1 2) (hH 1) hm φ hφc hφs
  have hval : ∀ T, ∫ X, φ X ∂(m T) = (((m T (latV b v)).toReal : ℝ) : ℂ) := fun T => by
    rw [hφ, integral_indicator_const (1 : ℂ) hLm]
    simp [Measure.real]
  have hunit : ∀ z ∈ ({0}ᶜ : Set (Fv F v)),
      hermScal (Fv F v) σ z ∈
        {S : HermR (Fv F v) σ 1 | IsUnit (S : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)).det} := by
    intro z hz
    show IsUnit (Matrix.det _)
    rw [Matrix.det_fin_one]
    exact FibreRatio.isUnit_tmul (Fv F v) hz
  have hcont : ContinuousOn (fun z => (m (hermScal (Fv F v) σ z) (latV b v)).toReal) {0}ᶜ := by
    have h1 := hgc.comp hSh.continuous.continuousOn hunit
    have h2 := Complex.continuous_re.comp_continuousOn h1
    refine h2.congr fun z _ => ?_
    simp [hval]
  refine ⟨hcont, ?_⟩
  have hfin : ∀ S, m S (latV b v) < ⊤ := fun S => by
    haveI := (GlobalTheory.T.gram_fiber_measure_locallyFinite_and_ne_zero_of_isOpen F E σ hCM 2 J hJ (Fv F v) hloc 1 _ _ m (hW 1 2) (hH 1) hm S).1
    exact hLc.measure_lt_top
  obtain ⟨n1, n2⟩ := GlobalTheory.T.haar_measure_nonunits_null F E σ hCM 2 J hJ (by norm_num) v (coordW (Fv F v) b lam 1 2) lam (hW 1 2) hlam.1
  have n1' : lam ({0}ᶜ : Set (Fv F v))ᶜ = 0 := by
    refine measure_mono_null (fun c hc => ?_) n1
    have : c = 0 := by simpa using hc
    simp [this]
  have hres : lam.restrict ({0}ᶜ : Set (Fv F v)) = lam :=
    Measure.restrict_eq_self_of_ae_mem (by rw [ae_iff]; exact n1')
  have hcq : Continuous fun X : Fin 1 → Fin 2 → Fv F v ⊗[F] E =>
      algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (gramR (Fv F v) σ J X 0 0) :=
    continuous_const.mul (htr.comp ((hgr 1 2 J).matrix_elem 0 0))
  have hVm : MeasurableSet ({0}ᶜ : Set (Fv F v)) := (measurableSet_singleton 0).compl
  have hP : MeasurableSet {S | FibreRatio.qS (Fv F v) σ S ∈ ({0}ᶜ : Set (Fv F v))} :=
    (FibreRatio.continuous_qS (Fv F v) htr).measurable hVm
  have hmass := FibreRatio.mass_eq_lintegral (Fv F v) hCM hJ hm hLm (V := {0}ᶜ) (by simp) (hcq.measurable hVm) hP
  have hconull : coordW (Fv F v) b lam 1 2 {X : Fin 1 → Fin 2 → Fv F v ⊗[F] E | algebraMap F (Fv F v) (1 / 2) *
      Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (gramR (Fv F v) σ J X 0 0) ∈ ({0}ᶜ : Set (Fv F v))}ᶜ = 0 := by
    refine measure_mono_null (fun X hX => ?_) n2
    have h0 : algebraMap F (Fv F v) (1 / 2) *
      Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (gramR (Fv F v) σ J X 0 0) = 0 := by simpa using hX
    intro hu
    exact hu.ne_zero h0
  rw [measure_inter_conull hconull, hL1 lam hlam, ← hSm lam hlam.1] at hmass
  have hEmb : MeasurableEmbedding (hermScal (Fv F v) σ) :=
    (hSh.homeomorph _).isClosedEmbedding.measurableEmbedding
  rw [hEmb.restrict_map, hEmb.lintegral_map] at hmass
  have hpre : hermScal (Fv F v) σ ⁻¹' {S | FibreRatio.qS (Fv F v) σ S ∈ ({0}ᶜ : Set (Fv F v))} = {0}ᶜ := by
    ext s
    simp only [Set.mem_preimage, Set.mem_setOf_eq, FibreRatio.qS_hermScal (Fv F v) hCM s]
  rw [hpre, hres] at hmass
  have hae : AEMeasurable (fun s : Fv F v => m (hermScal (Fv F v) σ s) (latV b v)) lam := by
    have h1 : AEMeasurable (fun s : Fv F v => ENNReal.ofReal (m (hermScal (Fv F v) σ s) (latV b v)).toReal)
        (lam.restrict ({0}ᶜ : Set (Fv F v))) :=
      (ENNReal.continuous_ofReal.comp_continuousOn hcont).aemeasurable hVm
    rw [hres] at h1
    refine h1.congr (Eventually.of_forall fun s => ?_)
    exact ENNReal.ofReal_toReal (hfin _).ne
  rw [integral_toReal hae (Eventually.of_forall fun s => hfin _), ← hmass]
  simp

end GlobalTheory.CompanionTheory.SW.StdLat
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalBinaryGramDensityStatement
open PositivityTheory.Rg.Mass
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped TensorProduct ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_binary_gram_density : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (J : Matrix (Fin 2) (Fin 2) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
  (lam : Measure (Fv F v)), IsStdV v lam → ∀ (m : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin 2 → Fv F v ⊗[F] E)),
  IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b lam 1 2) (coordHerm (Fv F v) σ b lam 1) m →
  ContinuousOn (fun s : Fv F v => (m (hermScal (Fv F v) σ s) (latV b v)).toReal) {0}ᶜ ∧
  ∫ s, (m (hermScal (Fv F v) σ s) (latV b v)).toReal ∂lam = 1 := by
  first | exact @GlobalTheory.CompanionTheory.SW.StdLat.fibre_masses_standard_lattice | exact GlobalTheory.CompanionTheory.SW.StdLat.fibre_masses_standard_lattice | (intros; apply GlobalTheory.CompanionTheory.SW.StdLat.fibre_masses_standard_lattice <;> assumption)
end
end

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped TensorProduct ENNReal NNReal

noncomputable section

namespace PositivityTheory.Rg.Mass.LiteralAutomorphy

open PositivityTheory.Rg.Mass

theorem srside : MeanVal → LocMass → RSide := by
  intro hMV hLM F E _ _ _ _ _ σ J d b li lam μ 𝓕 mi m hCM hJ hAn hli hlam hμ h𝓕 hmi hm θ hθ
  obtain ⟨C, hC⟩ := hLM F E σ J d b li lam μ 𝓕 mi m hCM hJ hAn hli hlam hμ h𝓕 hmi hm
  have hfin := Filter.eventually_cofinite.1 hC
  refine ⟨hfin.toFinset, fun S hS φ A hT => ?_⟩
  obtain ⟨hφc, hφs, hφ0, hφU, hAS, hAL⟩ := hT
  obtain ⟨hGc, hGs, hGl, hGi⟩ := GlobalTheory.T.archimedean_binary_gram_density F E σ hCM J hJ d b li hli mi hmi φ hφc hφs hφ0 hφU
  have hG0 : ∀ y : Ainf F, 0 ≤ ∫ X, φ X ∂(mi (hermScal (Ainf F) σ y)) := fun y => integral_nonneg fun X => hφ0 X
  have hP := fun v (hv : v ∉ S) => not_not.1 (fun h => hv (hS (hfin.mem_toFinset.2 h)))
  have key := hMV F hCM.1 θ hθ li lam hli hlam S (fun s => ∫ X, φ X ∂(mi (hermScal (Ainf F) σ s)))
    (fun v s => (m v (hermScal (Fv F v) σ s) (A v)).toReal) C hGc hGs hG0 (fun v y => ENNReal.toReal_nonneg)
    (fun v hv => by
      obtain ⟨h1, h2, h3⟩ := hAS v hv
      obtain ⟨c1, c2, -⟩ := GlobalTheory.T.local_binary_gram_integral F E σ hCM J hJ d b v (lam v) (hlam v) (m v) (hm v) (A v) h1 h2 h3
      exact ⟨c1, c2⟩)
    (fun v hv => by
      obtain ⟨p1, p2, p3⟩ := hP v hv
      obtain ⟨l1, l2⟩ := GlobalTheory.T.local_binary_gram_density F E σ hCM J hJ d b v (lam v) (hlam v) (m v) (hm v)
      simp only [hAL v hv]
      refine ⟨l1, fun s hs => ?_, p2, p3, l2⟩
      have hs0 : s ≠ 0 := fun h => hs (h ▸ (v.adicCompletionIntegers F).zero_mem)
      rw [p1 s hs hs0]
      rfl)
  beta_reduce at key
  have hlim : ENNReal.ofReal ((∫ y, (∫ X, φ X ∂(mi (hermScal (Ainf F) σ y))) ∂li) *
      ∏ v ∈ S, ∫ s, (m v (hermScal (Fv F v) σ s) (A v)).toReal ∂(lam v)) = vol b li lam S φ A := by
    rw [ENNReal.ofReal_mul (integral_nonneg fun s => hG0 s),
      ENNReal.ofReal_prod_of_nonneg (fun v _ => integral_nonneg fun s => ENNReal.toReal_nonneg), hGi]
    unfold vol
    congr 1
    refine Finset.prod_congr rfl fun v hv => ?_
    obtain ⟨h1, h2, h3⟩ := hAS v hv
    exact (GlobalTheory.T.local_binary_gram_integral F E σ hCM J hJ d b v (lam v) (hlam v) (m v) (hm v) (A v) h1 h2 h3).2.2
  rw [hlim] at key
  have hsq : Tendsto (fun ε : ℝ => ε ^ 2) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h0 : Tendsto (fun ε : ℝ => ε ^ 2) (𝓝 0) (𝓝 ((0 : ℝ) ^ 2)) := (continuous_pow 2).tendsto 0
      simpa using h0.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε (hε : (0 : ℝ) < ε) using Set.mem_Ioi.2 (pow_pos hε 2)
  refine (key.comp hsq).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : (0 : ℝ) < ε)
  simp only [Function.comp_apply]
  rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun β => ?_
  have h1 := GlobalTheory.T.archimedean_binary_gram_integral F E σ hCM J hJ d b li hli mi hmi θ hθ ε hε (algebraMap F (Ainf F) β.1) φ hφc
  rw [← mul_assoc, h1, hGl, mul_assoc, ← ENNReal.ofReal_mul (hG0 _), map_pow]

end PositivityTheory.Rg.Mass.LiteralAutomorphy
