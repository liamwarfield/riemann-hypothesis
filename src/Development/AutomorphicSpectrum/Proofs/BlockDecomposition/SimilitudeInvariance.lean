module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelOperatorsSpanEventually
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCyclicVectorOfSeparable
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianMatrixEulerProduct

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimilitudeScalingHermitianMeasure
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimilitudeScalingHermitianMeasure
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.MassSimil.ScalModule

theorem map_eq_sqrt_smul {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (e : G ≃ₜ+ G) (ν : Measure G) [ν.IsAddHaarMeasure] (c : ℝ≥0)
    (h : ν.map (e ∘ e) = c • ν) : ν.map e = NNReal.sqrt c • ν := by
  haveI : (ν.map e).IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map ν e
  obtain ⟨b, hb⟩ : ∃ b : ℝ≥0, ν.map e = b • ν :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul (ν.map e) ν⟩
  have he : Measurable e := e.continuous.measurable
  have h2 : ν.map (e ∘ e) = (b * b) • ν := by
    rw [← Measure.map_map he he, hb, Measure.map_smul b he.aemeasurable, hb, smul_smul]
  obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds (0 : G)
  have hpos : ν K ≠ 0 := (Measure.measure_pos_of_mem_nhds ν hK0).ne'
  have hfin : ν K ≠ ∞ := hK.measure_lt_top.ne
  have hbc : b * b = c := by
    have h3 : ((b * b : ℝ≥0) • ν) K = (c • ν) K := by rw [← h2, h]
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h3
    exact_mod_cast (ENNReal.mul_left_inj hpos hfin).1 h3
  rw [hb, ← hbc, NNReal.sqrt_mul_self]

theorem scalH_scalH {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {n : ℕ} (a b : R) (S : HermR R σ n) :
    scalH R σ a (scalH R σ b S) = scalH R σ (a * b) S := by
  apply Subtype.ext
  simp only [scalH_coe, smul_smul, map_mul]

theorem scalH_one {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {n : ℕ} (S : HermR R σ n) : scalH R σ 1 S = S := by
  apply Subtype.ext
  simp only [scalH_coe, map_one, one_smul]

def scalEquiv {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R]
    (n : ℕ) (l : F) (hl : l ≠ 0) : HermR R σ n ≃ₜ+ HermR R σ n :=
  have hc : ∀ a : R, Continuous (scalH R σ (n := n) a) := fun a => by
    obtain ⟨iTR, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm R
    haveI := iTR
    exact Continuous.subtype_mk ((continuous_const_smul _).comp continuous_subtype_val) _
  have hm : algebraMap F R l * algebraMap F R l⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hl, map_one]
  { toFun := scalH R σ (algebraMap F R l)
    invFun := scalH R σ (algebraMap F R l⁻¹)
    left_inv := fun S => by rw [scalH_scalH, mul_comm, hm, scalH_one]
    right_inv := fun S => by rw [scalH_scalH, hm, scalH_one]
    map_add' := fun S T => by
      apply Subtype.ext
      simp [scalH_coe]
    continuous_toFun := hc _
    continuous_invFun := hc _ }

def oneByOne {F E : Type} [Field F] [Field E] [Algebra F E] (l : F) : Matrix (Fin 1) (Fin 1) E :=
  Matrix.of fun _ _ => algebraMap F E l

theorem action_eq {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) (l : F) (S : HermR R σ 1) :
    ((scalH R σ (algebraMap F R l) (scalH R σ (algebraMap F R l) S) : HermR R σ 1) :
        Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) =
      cT (sigR R σ) ((oneByOne l : Matrix (Fin 1) (Fin 1) E).map (inclR R)) *
        (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) *
        (oneByOne l : Matrix (Fin 1) (Fin 1) E).map (inclR R) := by
  have h1 : inclR R (algebraMap F E l) = algebraMap R (R ⊗[F] E) (algebraMap F R l) := by
    rw [← IsScalarTower.algebraMap_apply]
    exact (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E).commutes l
  have h2 : sigR R σ (algebraMap R (R ⊗[F] E) (algebraMap F R l)) =
      algebraMap R (R ⊗[F] E) (algebraMap F R l) := by
    simp [sigR, Algebra.TensorProduct.algebraMap_apply]
  ext i j
  simp only [scalH_coe, cT, oneByOne, Matrix.mul_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.transpose_apply,
    Matrix.of_apply, Finset.univ_unique, Finset.sum_singleton, smul_eq_mul, h1, h2]
  have hi : i = default := Subsingleton.elim _ _
  have hj : j = default := Subsingleton.elim _ _
  subst hi hj
  ring

theorem local_scal {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (hR : IsLocR R) (l : F) (hl : l ≠ 0) (c : ℝ≥0)
    (ν : Measure (HermR R σ 1)) (hν : ν.IsAddHaarMeasure)
    (h : ∀ τ : HermR R σ 1 → HermR R σ 1, (∀ S, (τ S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) =
      cT (sigR R σ) ((oneByOne l : Matrix (Fin 1) (Fin 1) E).map (inclR R)) *
        (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) *
        (oneByOne l : Matrix (Fin 1) (Fin 1) E).map (inclR R)) → ν.map τ = c • ν) :
    ν.map (scalH R σ (algebraMap F R l)) = NNReal.sqrt c • ν := by
  obtain ⟨hTR, hLC, hSC, hT2, -, -, -, -⟩ := id hR
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  obtain ⟨iTR, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm R
  haveI := iTR
  obtain ⟨jLC, jSC, jT2, jB, -⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hcm R 1
  haveI := jLC
  haveI := jSC
  haveI := jT2
  haveI := jB
  exact map_eq_sqrt_smul (scalEquiv σ hcm R 1 l hl) ν c (h _ (action_eq R σ l))

theorem scal_module : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ l : F, l ≠ 0 → ∃ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c ∧ (∀ ν : Measure (HermR (Ainf F) σ 1), ν.IsAddHaarMeasure → ν.map (GlobalTheory.CompanionTheory.SW.MassSimil.scalH (Ainf F) σ (algebraMap F (Ainf F) l)) = cinf • ν) ∧ ∀ v : HeightOneSpectrum (𝓞 F), ∀ ν : Measure (HermR (Fv F v) σ 1), ν.IsAddHaarMeasure → ν.map (GlobalTheory.CompanionTheory.SW.MassSimil.scalH (Fv F v) σ (algebraMap F (Fv F v) l)) = c v • ν := by
  intro F E _ _ _ _ _ σ hcm l hl
  have hdet : (oneByOne l : Matrix (Fin 1) (Fin 1) E).det ≠ 0 := by
    rw [Matrix.det_fin_one]
    exact (map_ne_zero (algebraMap F E)).2 hl
  obtain ⟨ci, c, hu, hi, hv⟩ := GlobalTheory.T.hermitian_matrix_euler_product F E σ hcm 1 (oneByOne l) hdet
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI : ∀ v, BorelSpace (Fv F v) := fun _ => ⟨rfl⟩
  refine ⟨NNReal.sqrt ci, fun v => NNReal.sqrt (c v), (PositivityTheory.PlacePermOperatorBicommutantSpan.up_alg F ci ci c c hu hu).2.2.2.2.2.1, ?_, ?_⟩
  · intro ν hν
    exact local_scal σ hcm (Ainf F) (GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hcm.1) l hl ci ν hν (hi ν hν)
  · intro v ν hν
    exact local_scal σ hcm (Fv F v) (GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v) l hl (c v) ν hν (hv v ν hν)

end GlobalTheory.CompanionTheory.SW.MassSimil.ScalModule

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimilitudeScalingHermitianMeasureStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.similitude_scaling_hermitian_measure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ l : F, l ≠ 0 → ∃ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c ∧ (∀ ν : Measure (HermR (Ainf F) σ 1), ν.IsAddHaarMeasure → ν.map (GlobalTheory.CompanionTheory.SW.MassSimil.scalH (Ainf F) σ (algebraMap F (Ainf F) l)) = cinf • ν) ∧ ∀ v : HeightOneSpectrum (𝓞 F), ∀ ν : Measure (HermR (Fv F v) σ 1), ν.IsAddHaarMeasure → ν.map (GlobalTheory.CompanionTheory.SW.MassSimil.scalH (Fv F v) σ (algebraMap F (Fv F v) l)) = c v • ν := by
  first | exact @GlobalTheory.CompanionTheory.SW.MassSimil.ScalModule.scal_module | exact GlobalTheory.CompanionTheory.SW.MassSimil.ScalModule.scal_module | (intros; apply GlobalTheory.CompanionTheory.SW.MassSimil.ScalModule.scal_module <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimilitudeBetweenNonemptySpheres
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimilitudeBetweenNonemptySpheres
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SimilExists

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def frame (σ : E →ₐ[F] E) (J : Matrix (Fin 2) (Fin 2) E) (x : Fin 2 → E) : Matrix (Fin 2) (Fin 2) E :=
  !![x 0, -(σ (x 0) * J 0 1 + σ (x 1) * J 1 1); x 1, σ (x 0) * J 0 0 + σ (x 1) * J 1 0]

theorem frame_det (σ : E →ₐ[F] E) (J : Matrix (Fin 2) (Fin 2) E) (x : Fin 2 → E) :
    (frame σ J x).det = hE σ J x x := by
  simp [frame, Matrix.det_fin_two, hE, hform, Fin.sum_univ_two]
  ring

theorem frame_gram {σ : E →ₐ[F] E} (hσ : ∀ e, σ (σ e) = e) {J : Matrix (Fin 2) (Fin 2) E}
    (hJ : IsHermND σ J) (x : Fin 2 → E) :
    cT (σ : E →+* E) (frame σ J x) * J * frame σ J x =
      hE σ J x x • Matrix.diagonal ![1, J.det] := by
  have h00 : σ (J 0 0) = J 0 0 := hJ.1 0 0
  have h11 : σ (J 1 1) = J 1 1 := hJ.1 1 1
  have h01 : σ (J 1 0) = J 0 1 := hJ.1 0 1
  have h10 : σ (J 0 1) = J 1 0 := hJ.1 1 0
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [frame, cT, Matrix.mul_apply, Fin.sum_univ_two, hE, hform, Matrix.det_fin_two, hσ, h00, h11,
      h01, h10] <;> ring

theorem exists_similitude_of_vectors {σ : E →ₐ[F] E} (hσ : ∀ e, σ (σ e) = e)
    {J : Matrix (Fin 2) (Fin 2) E} (hJ : IsHermND σ J) {x x' : Fin 2 → E} {b b' : E}
    (hx : hE σ J x x = b) (hx' : hE σ J x' x' = b') (hb : b ≠ 0) (hb' : b' ≠ 0) :
    ∃ γ : GL (Fin 2) E, cT (σ : E →+* E) (γ : Matrix (Fin 2) (Fin 2) E) * J *
      (γ : Matrix (Fin 2) (Fin 2) E) = (b' / b) • J := by
  set P := frame σ J x with hP
  set P' := frame σ J x' with hP'
  have hdet : P.det = b := by rw [hP, frame_det, hx]
  have hdet' : P'.det = b' := by rw [hP', frame_det, hx']
  have hu : IsUnit P.det := by rw [hdet]; exact hb.isUnit
  have hinv : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hu
  have hc : cT (σ : E →+* E) P⁻¹ * cT (σ : E →+* E) P = 1 := by
    rw [← cT_mul, hinv, cT_one]
  have hg : cT (σ : E →+* E) P * J * P = b • Matrix.diagonal ![1, J.det] := by
    rw [hP, frame_gram hσ hJ, hx]
  have hg' : cT (σ : E →+* E) P' * J * P' = b' • Matrix.diagonal ![1, J.det] := by
    rw [hP', frame_gram hσ hJ, hx']
  have hJ' : J = b • (cT (σ : E →+* E) P⁻¹ * Matrix.diagonal ![1, J.det] * P⁻¹) := by
    calc J = (cT (σ : E →+* E) P⁻¹ * cT (σ : E →+* E) P) * J * (P * P⁻¹) := by
          rw [hc, hinv, Matrix.one_mul, Matrix.mul_one]
      _ = cT (σ : E →+* E) P⁻¹ * (cT (σ : E →+* E) P * J * P) * P⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [hg, Matrix.mul_smul, Matrix.smul_mul]
  have hdetG : (P' * P⁻¹).det ≠ 0 := by
    rw [Matrix.det_mul, Matrix.det_nonsing_inv, hdet', hdet]
    simpa using ⟨hb', hb⟩
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (P' * P⁻¹) hdetG, ?_⟩
  change cT (σ : E →+* E) (P' * P⁻¹) * J * (P' * P⁻¹) = (b' / b) • J
  calc cT (σ : E →+* E) (P' * P⁻¹) * J * (P' * P⁻¹)
      = cT (σ : E →+* E) P⁻¹ * (cT (σ : E →+* E) P' * J * P') * P⁻¹ := by
        rw [cT_mul]; simp only [Matrix.mul_assoc]
    _ = b' • (cT (σ : E →+* E) P⁻¹ * Matrix.diagonal ![1, J.det] * P⁻¹) := by
        rw [hg', Matrix.mul_smul, Matrix.smul_mul]
    _ = (b' / b) • (b • (cT (σ : E →+* E) P⁻¹ * Matrix.diagonal ![1, J.det] * P⁻¹)) := by
        rw [smul_smul, div_mul_cancel₀ _ hb]
    _ = (b' / b) • J := by rw [← hJ']

theorem exists_similitude : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ J : Matrix (Fin 2) (Fin 2) E, IsHermND σ J → ∀ β β' : F, β ≠ 0 → β' ≠ 0 → (PositivityTheory.Rg.Mass.sph σ J β).Nonempty → (PositivityTheory.Rg.Mass.sph σ J β').Nonempty → ∃ γ : GL (Fin 2) E, cT (σ : E →+* E) (γ : Matrix (Fin 2) (Fin 2) E) * J * (γ : Matrix (Fin 2) (Fin 2) E) = (algebraMap F E (β' / β)) • J := by
  intro F E _ _ _ _ _ σ hcm J hJ β β' hβ hβ' ⟨X, hX⟩ ⟨X', hX'⟩
  have hσ : ∀ e, σ (σ e) = e := fun e => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hcm.2.2.2, hcm.2.2.2]
    simp
  have hx : hE σ J (X 0) (X 0) = algebraMap F E β := congrFun (congrFun hX 0) 0
  have hx' : hE σ J (X' 0) (X' 0) = algebraMap F E β' := congrFun (congrFun hX' 0) 0
  have hb : algebraMap F E β ≠ 0 := by simpa using hβ
  have hb' : algebraMap F E β' ≠ 0 := by simpa using hβ'
  rw [map_div₀]
  exact exists_similitude_of_vectors hσ hJ hx hx' hb hb'

end GlobalTheory.CompanionTheory.SimilExists

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimilitudeBetweenNonemptySpheresStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.similitude_between_nonempty_spheres : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ J : Matrix (Fin 2) (Fin 2) E, IsHermND σ J → ∀ β β' : F, β ≠ 0 → β' ≠ 0 → (PositivityTheory.Rg.Mass.sph σ J β).Nonempty → (PositivityTheory.Rg.Mass.sph σ J β').Nonempty → ∃ γ : GL (Fin 2) E, cT (σ : E →+* E) (γ : Matrix (Fin 2) (Fin 2) E) * J * (γ : Matrix (Fin 2) (Fin 2) E) = (algebraMap F E (β' / β)) • J := by
  first | exact @GlobalTheory.CompanionTheory.SimilExists.exists_similitude | exact GlobalTheory.CompanionTheory.SimilExists.exists_similitude | (intros; apply GlobalTheory.CompanionTheory.SimilExists.exists_similitude <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimilitudeInvariance
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.MassSimil

theorem JR_sim {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (γ : GL (Fin M) E) (l : F)
    (hγ : cT (σ : E →+* E) (γ : Matrix (Fin M) (Fin M) E) * J * (γ : Matrix (Fin M) (Fin M) E) = (algebraMap F E l) • J) :
    cT (sigR R σ) ((bc (inclR R) γ : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J *
        ((bc (inclR R) γ : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) =
      (algebraMap R (R ⊗[F] E) (algebraMap F R l)) • JR R J := by
  rw [← GlobalTheory.CompanionTheory.SW.HIsom.JR_conj, hγ]
  ext i j
  change inclR R (algebraMap F E l * J i j) = algebraMap R (R ⊗[F] E) (algebraMap F R l) * inclR R (J i j)
  rw [map_mul]
  congr 1
  rw [← IsScalarTower.algebraMap_apply]
  exact (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E).commutes l

theorem simil : PositivityTheory.Rg.Mass.Simil := by
  intro F E _ _ _ _ _ σ J d b li lam μ 𝓕 mi m hcm hJ _ hli hlam hμ h𝓕 hmi hm β β' hβ hβ' hs hs' c hc
  have hl0 : β' / β ≠ 0 := div_ne_zero hβ' hβ
  obtain ⟨γ, hγ⟩ := GlobalTheory.T.similitude_between_nonempty_spheres F E σ hcm J hJ β β' hβ hβ' hs hs'
  obtain ⟨μ', 𝓕', hμ', h𝓕', hth⟩ := GlobalTheory.T.theta_measure_similitude F E σ hcm 2 J hJ μ 𝓕 hμ h𝓕 γ (β' / β) hl0 hγ
  have hT : (fun _ _ => algebraMap F E β' : Matrix (Fin 1) (Fin 1) E) =
      (algebraMap F E (β' / β)) • (fun _ _ => algebraMap F E β : Matrix (Fin 1) (Fin 1) E) := by
    funext a b'
    change algebraMap F E β' = algebraMap F E (β' / β) * algebraMap F E β
    rw [← map_mul, div_mul_cancel₀ _ hβ]
  have hth1 := hth 1 _ _ hT
  have hind := GlobalTheory.T.theta_measure_independent_choices F E σ hcm 2 J hJ μ μ' 𝓕 𝓕' hμ h𝓕 hμ' h𝓕' 1 (fun _ _ => algebraMap F E β)
  change (thetaMeas σ J μ' 𝓕' (PositivityTheory.Rg.Mass.sph σ J β)).map _ = thetaMeas σ J μ 𝓕 (PositivityTheory.Rg.Mass.sph σ J β') at hth1
  change thetaMeas σ J μ 𝓕 (PositivityTheory.Rg.Mass.sph σ J β) = thetaMeas σ J μ' 𝓕' (PositivityTheory.Rg.Mass.sph σ J β) at hind
  obtain ⟨ai, a, hau, hai, hav⟩ := GlobalTheory.T.haar_modulus_gl_action_product_formula F E σ hcm 1 2 γ
  obtain ⟨ci, cv, hcu, hci, hcv⟩ := GlobalTheory.T.similitude_scaling_hermitian_measure F E σ hcm (β' / β) hl0
  obtain ⟨-, -, -, -, hq, -⟩ := PositivityTheory.PlacePermOperatorBicommutantSpan.up_alg F ai ci a cv hau hcu
  obtain ⟨⟨i1, i2, i3⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  have hLi : IsLocR (Ainf F) := GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hcm.1
  have hLv : ∀ v, IsLocR (Fv F v) := fun v => GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI : ∀ v, BorelSpace (Fv F v) := fun _ => ⟨rfl⟩
  have hWi := SWIsom.haar_of_loc σ hcm (Ainf F) hLi b li hli.1 1 2
  have hWv := fun v => SWIsom.haar_of_loc σ hcm (Fv F v) (hLv v) b (lam v) (hlam v).1 1 2
  have hJR : ∀ (R : Type) [CommRing R] [Algebra F R],
      cT (sigR R σ) ((bc (inclR R) γ : GL (Fin 2) (R ⊗[F] E)) : Matrix (Fin 2) (Fin 2) (R ⊗[F] E)) * JR R J *
        ((bc (inclR R) γ : GL (Fin 2) (R ⊗[F] E)) : Matrix (Fin 2) (Fin 2) (R ⊗[F] E)) =
        (algebraMap R (R ⊗[F] E) (algebraMap F R (β' / β))) • JR R J := fun R _ _ => JR_sim R σ J γ _ hγ
  have hunit : ∀ (R : Type) [CommRing R] [Algebra F R] [Nontrivial R], IsUnit (algebraMap F R (β' / β)) :=
    fun R _ _ _ => (IsUnit.mk0 _ hl0).map _
  have sInf := GlobalTheory.T.gram_fibre_measure_local F E σ hcm 2 J hJ (Ainf F) hLi 1 _ _ mi hWi.1 hWi.2 hmi _ _ (hunit _) (hJR _) ai ci
    (hai _ hWi.1) (hci _ hWi.2)
  have sV := fun v => GlobalTheory.T.gram_fibre_measure_local F E σ hcm 2 J hJ (Fv F v) (hLv v) 1 _ _ (m v) (hWv v).1 (hWv v).2 (hm v) _ _ (hunit _)
    (hJR _) (a v) (cv v) (hav v _ (hWv v).1) (hcv v _ (hWv v).2)
  have hS : ∀ (R : Type) [CommRing R] [Algebra F R], scalH R σ (algebraMap F R (β' / β))
      (hermScal R σ (algebraMap F R β)) = hermScal R σ (algebraMap F R β') := fun R _ _ => by
    rw [scalH_hermScal, ← map_mul, div_mul_cancel₀ _ hβ]
  have hproj : ∀ X : Fin 1 → Fin 2 → AF F ⊗[F] E,
      projInf (actTup (AF F) (bc (inclR (AF F)) γ) X) =
          actTup (Ainf F) (bc (inclR (Ainf F)) γ) (projInf X) ∧
        ∀ v, projV v (projFin (actTup (AF F) (bc (inclR (AF F)) γ) X)) =
          actTup (Fv F v) (bc (inclR (Fv F v)) γ) (projV v (projFin X)) := by
    intro X
    refine ⟨?_, fun v => ?_⟩
    · funext a i
      exact SWIsom.map_actTup (fstA F) γ X a i
    · have h1 : projFin (actTup (AF F) (bc (inclR (AF F)) γ) X) =
          actTup (Af F) (bc (inclR (Af F)) γ) (projFin X) := by
        funext a i
        exact SWIsom.map_actTup (sndA F) γ X a i
      rw [h1]
      funext a i
      exact SWIsom.map_actTup (evalV F v) γ (projFin X) a i
  have hfin : ∀ v, m v (hermScal (Fv F v) σ (algebraMap F _ β')) (latV b v) < ⊤ := by
    intro v
    haveI := (GlobalTheory.T.gram_fiber_measure_locallyFinite_and_ne_zero_of_isOpen F E σ hcm 2 J hJ (Fv F v) (hLv v) 1 _ _ (m v) (hWv v).1 (hWv v).2 (hm v)
      (hermScal (Fv F v) σ (algebraMap F _ β'))).1
    exact ((GlobalTheory.T.adelic_tuple_projections F E σ hcm d b 1 2).2.2.2.1 v).1.measure_lt_top
  have key := euler_move_c F E σ hcm d b 1 2 (thetaMeas σ J μ' 𝓕' (PositivityTheory.Rg.Mass.sph σ J β)) (mi (hermScal (Ainf F) σ (algebraMap F _ β)))
    (mi (hermScal (Ainf F) σ (algebraMap F _ β')))
    (fun v => m v (hermScal (Fv F v) σ (algebraMap F _ β)))
    (fun v => m v (hermScal (Fv F v) σ (algebraMap F _ β')))
    (actTup (AF F) (bc (inclR (AF F)) γ))
    (actTup (Ainf F) (bc (inclR (Ainf F)) γ)) (fun v => actTup (Fv F v) (bc (inclR (Fv F v)) γ))
    (SWIsom.measurable_actTup σ hcm (AF F) _) (SWIsom.measurable_of_loc σ hcm (Ainf F) hLi _)
    (fun v => SWIsom.measurable_of_loc σ hcm (Fv F v) (hLv v) _) hproj
    ((GlobalTheory.CompanionTheory.SW.LatRat.latV_rational F E σ hcm d b 1 2).2.1 γ) (ai / ci) (fun v => a v / cv v) hq
    (by rw [sInf, hS]) (fun v => by rw [sV v, hS]) hfin c
  unfold PositivityTheory.Rg.Mass.EP at hc ⊢
  rw [hind] at hc
  rw [← hth1]
  exact key hc

end GlobalTheory.CompanionTheory.SW.MassSimil

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimilitudeInvarianceStatement
open PositivityTheory.Rg.Mass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.similitude_invariance : Simil := by
  first | exact @GlobalTheory.CompanionTheory.SW.MassSimil.simil | exact GlobalTheory.CompanionTheory.SW.MassSimil.simil | (intros; apply GlobalTheory.CompanionTheory.SW.MassSimil.simil <;> assumption)
end
