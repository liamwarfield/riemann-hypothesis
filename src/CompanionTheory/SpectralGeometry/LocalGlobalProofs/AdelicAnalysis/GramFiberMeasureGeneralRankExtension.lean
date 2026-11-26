module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicUnitaryGroupLocallyCompact
public import GroundTheory.GlobalFields.TateThesis.AdelicCharDual
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.DisintegrationDensityUnique
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DiagHermitian
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianOrbitLocalSectionSubgroup
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitaryActionPreservesHaarLocal

@[expose] public section

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasureGeneralRankExtension
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasureGeneralRankExtension
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂

theorem gramFib_basic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (N n : ℕ) (J₂ : Matrix (Fin N) (Fin N) E), IsHermND σ J₂ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → ∀ m : HermR R σ n → Measure (Fin n → Fin N → R ⊗[F] E), IsGramFib R σ J₂ n (coordW R b lam n N) (coordHerm R σ b lam n) m → IsOpen (Unt σ R n) ∧ (∀ S, IsLocallyFiniteMeasure (m S)) ∧ (∀ S, S ∉ Unt σ R n → m S = 0) ∧ (∀ A : Set (Fin n → Fin N → R ⊗[F] E), MeasurableSet A → Measurable fun S => m S A) ∧ (∀ (C : Set (Fin n → Fin N → R ⊗[F] E)) (D : Set (HermR R σ n)), IsCompact C → IsCompact D → D ⊆ Unt σ R n → ∃ c : ℝ≥0, ∀ S ∈ D, m S C ≤ c) ∧ ∀ S : HermR R σ n, ∀ᵐ X ∂(m S), gramR R σ J₂ X = (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) := by
  intro F E _ _ _ _ _ σ hCM N n J₂ hJ R _ _ _ _ _ hR d b lam hlam m hm
  obtain ⟨iTR, iLC, iSC, iT2, -⟩ := id hR
  haveI := iTR; haveI := iLC; haveI := iSC; haveI := iT2
  obtain ⟨kTR, kLC, kSC, kT2, -, -, -, kB, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM R
  haveI := kTR; haveI := kLC; haveI := kSC; haveI := kT2
  haveI := kB n N
  obtain ⟨hLC, hSC, hT2, hB, hg⟩ := GlobalTheory.T.hermitian_matrices_locally_compact_borel F E σ hCM R n
  haveI := hLC; haveI := hSC; haveI := hT2; haveI := hB
  obtain ⟨g, gc, hgg⟩ := hg N J₂ hJ
  obtain ⟨-, hW, hH⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hCM R d b lam hlam
  haveI := hW n N
  haveI := hH n
  have hopen : IsOpen (Unt σ R n) := by
    have hu : IsOpen {x : R ⊗[F] E | IsUnit x} := by
      have := (GlobalTheory.T.units_open_embedding_local_tensor F E σ hCM R hR).isOpen_range
      convert this using 1
      ext x
      simp [IsUnit]
    have hc : Continuous fun S : HermR R σ n => (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det :=
      continuous_subtype_val.matrix_det
    exact hu.preimage hc
  have hset : {X | IsUnit (gramR R σ J₂ X).det} = g ⁻¹' (Unt σ R n) := by
    ext X
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Unt, hgg X]
  have hm' : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily (coordW R b lam n N) (gramR R σ J₂) Subtype.val
      (g ⁻¹' (Unt σ R n)) (coordHerm R σ b lam n) (Unt σ R n) m := by
    rw [← hset]
    exact hm
  obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.CompanionTheory.SW.FibreFam.fibre_family_basic _ _ _ (coordW R b lam n N)
    (coordHerm R σ b lam n) (gramR R σ J₂) g Subtype.val Subtype.val_injective gc hgg (Unt σ R n) hopen m hm'
  refine ⟨hopen, h1, h2, h3, h4, fun S => ?_⟩
  have h0 := hm'.1 S
  have : ∀ᵐ X ∂(m S), X ∈ gramR R σ J₂ ⁻¹' {((S : HermR R σ n) : Matrix (Fin n) (Fin n) (R ⊗[F] E))} ∩ g ⁻¹' (Unt σ R n) :=
    mem_ae_iff.2 h0
  filter_upwards [this] with X hX
  exact hX.1

end GlobalTheory.CompanionTheory.SW.PiLocalization₂
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasureGeneralRankExtensionStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_fiber_measure_locally_finite_measurable_supported : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (N n : ℕ) (J₂ : Matrix (Fin N) (Fin N) E), IsHermND σ J₂ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → ∀ m : HermR R σ n → Measure (Fin n → Fin N → R ⊗[F] E), IsGramFib R σ J₂ n (coordW R b lam n N) (coordHerm R σ b lam n) m → IsOpen (Unt σ R n) ∧ (∀ S, IsLocallyFiniteMeasure (m S)) ∧ (∀ S, S ∉ Unt σ R n → m S = 0) ∧ (∀ A : Set (Fin n → Fin N → R ⊗[F] E), MeasurableSet A → Measurable fun S => m S A) ∧ (∀ (C : Set (Fin n → Fin N → R ⊗[F] E)) (D : Set (HermR R σ n)), IsCompact C → IsCompact D → D ⊆ Unt σ R n → ∃ c : ℝ≥0, ∀ S ∈ D, m S C ≤ c) ∧ ∀ S : HermR R σ n, ∀ᵐ X ∂(m S), gramR R σ J₂ X = (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.PiLocalization₂.gramFib_basic | exact GlobalTheory.CompanionTheory.SW.PiLocalization₂.gramFib_basic | (intros; apply GlobalTheory.CompanionTheory.SW.PiLocalization₂.gramFib_basic <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsEqAdelicCharMul
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.CharDual

variable {F : Type} [Field F] [NumberField F]

def toCircle (ψ : AddChar (AF F) ℂ) (h : ∀ x, ‖ψ x‖ = 1) : AddChar (AF F) Circle where
  toFun x := ⟨ψ x, by simpa [Submonoid.unitSphere, mem_sphere_zero_iff_norm] using h x⟩
  map_zero_eq_one' := by
    apply Circle.ext
    simp
  map_add_eq_mul' a b := by
    apply Circle.ext
    exact ψ.map_add_eq_mul a b

theorem coe_toCircle (ψ : AddChar (AF F) ℂ) (h : ∀ x, ‖ψ x‖ = 1) (x : AF F) :
    ((toCircle ψ h x : Circle) : ℂ) = ψ x := rfl

theorem continuous_toCircle (ψ : AddChar (AF F) ℂ) (h : ∀ x, ‖ψ x‖ = 1) (hc : Continuous ψ) :
    Continuous (toCircle ψ h) :=
  Continuous.subtype_mk hc _

theorem exists_eq_adelicChar_mul (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ) :
    ∃ ξ : F, ξ ≠ 0 ∧ ∀ x : AF F,
      ψ x = ((GroundTheory.Global.adelicChar F (algebraMap F (AF F) ξ * x) : Circle) : ℂ) := by
  obtain ⟨hc, hn, hF, x₀, hx₀⟩ := hψ
  obtain ⟨ξ, hξ, -⟩ := GroundTheory.Global.existsUnique_eq_adelicChar_mul (toCircle ψ hn)
    (continuous_toCircle ψ hn hc) (fun k => Circle.ext (by simpa [coe_toCircle] using hF k))
  have key : ∀ x : AF F,
      ψ x = ((GroundTheory.Global.adelicChar F (algebraMap F (AF F) ξ * x) : Circle) : ℂ) := fun x => by
    rw [← hξ x, coe_toCircle]
  refine ⟨ξ, ?_, key⟩
  rintro rfl
  apply hx₀
  rw [key x₀]
  simp

theorem exists_scalar (ψ ψ' : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ) (hψ' : IsCharAF F ψ') :
    ∃ a : F, a ≠ 0 ∧ ∀ x, ψ' x = ψ (algebraMap F (AF F) a * x) := by
  obtain ⟨ξ, hξ0, hξ⟩ := exists_eq_adelicChar_mul ψ hψ
  obtain ⟨η, hη0, hη⟩ := exists_eq_adelicChar_mul ψ' hψ'
  refine ⟨η / ξ, div_ne_zero hη0 hξ0, fun x => ?_⟩
  have hc : ξ * (η / ξ) = η := by field_simp
  rw [hη x, hξ, ← mul_assoc, ← map_mul, hc]

end GlobalTheory.CompanionTheory.SW.CharDual

theorem GlobalTheory.CompanionTheory.SW.char_dual : ∀ (F : Type) [Field F] [NumberField F] (ψ ψ' : AddChar (AF F) ℂ),
    IsCharAF F ψ → IsCharAF F ψ' →
      ∃ a : F, a ≠ 0 ∧ ∀ x, ψ' x = ψ (algebraMap F (AF F) a * x) :=
  fun _ _ _ ψ ψ' hψ hψ' => GlobalTheory.CompanionTheory.SW.CharDual.exists_scalar ψ ψ' hψ hψ'
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresTransitivity
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresTransitivity
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.GramDensity

theorem isContDensityOn_gram : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ), ∀ (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)) (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFib R σ J n μ ν m → ∀ φ : (Fin n → Fin M → R ⊗[F] E) → ℂ, Continuous φ → HasCompactSupport φ → IsContDensityOn μ (gramR R σ J) Subtype.val ν {S | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det} φ (fun S => ∫ X, φ X ∂(m S)) ∧ ∀ S, Integrable φ (m S) := by
  intro F E _ _ _ _ _ σ hσ M J hJ R _ _ _ _ _ hR n μ ν m hμ hν hfib φ hφ hφc
  have hunits : IsOpenEmbedding (Units.val : (R ⊗[F] E)ˣ → R ⊗[F] E) := GlobalTheory.T.units_open_embedding_local_tensor F E σ hσ R hR
  obtain ⟨hTR, hLC, hSC, hT2, -, -, -, -⟩ := hR
  have := hTR
  have := hLC
  have := hSC
  have := hT2
  obtain ⟨iTR, iLC, iSC, iT2, -, -, -, iB, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ R
  have := iB n M
  have := iTR
  have := iLC
  have := iSC
  have := iT2
  obtain ⟨jLC, jSC, jT2, jB, hlift⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hσ R n
  have := jLC
  have := jSC
  have := jT2
  have := jB
  obtain ⟨g, hg, hgram⟩ := hlift M J hJ
  have hB : IsOpen {S : HermR R σ n | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det} := by
    have hdet : Continuous fun S : HermR R σ n => (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det :=
      Continuous.matrix_det continuous_subtype_val
    have hset : {S : HermR R σ n | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det} =
        (fun S : HermR R σ n => (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det) ⁻¹'
          Set.range (Units.val : (R ⊗[F] E)ˣ → R ⊗[F] E) := by
      ext S
      simp [IsUnit]
    rw [hset]
    exact hunits.isOpen_range.preimage hdet
  have hpre : {X : Fin n → Fin M → R ⊗[F] E | IsUnit (gramR R σ J X).det} =
      g ⁻¹' {S : HermR R σ n | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det} := by
    ext X
    simp [hgram X]
  have hfib' : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ (gramR R σ J) Subtype.val
      (g ⁻¹' {S : HermR R σ n | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det}) ν
      {S : HermR R σ n | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det} m := by
    rw [← hpre]
    exact hfib
  exact GlobalTheory.CompanionTheory.SW.FibreDensity.isContDensityOn_fibreIntegral _ _ _ μ ν (gramR R σ J) g Subtype.val
    Subtype.val_injective hg hgram _ hB m hfib' φ hφ hφc

end GlobalTheory.CompanionTheory.SW.GramDensity
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresTransitivityStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_fiber_integral_isContDensityOn : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ), ∀ (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)) (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFib R σ J n μ ν m → ∀ φ : (Fin n → Fin M → R ⊗[F] E) → ℂ, Continuous φ → HasCompactSupport φ → IsContDensityOn μ (gramR R σ J) Subtype.val ν {S | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det} φ (fun S => ∫ X, φ X ∂(m S)) ∧ ∀ S, Integrable φ (m S) := by
  first | exact @GlobalTheory.CompanionTheory.SW.GramDensity.isContDensityOn_gram | exact GlobalTheory.CompanionTheory.SW.GramDensity.isContDensityOn_gram | (intros; apply GlobalTheory.CompanionTheory.SW.GramDensity.isContDensityOn_gram <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresUniqueAe
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresUniqueAe
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.GramFib

theorem fibre_unique : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ), ∀ (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)) (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFib R σ J n μ ν m → ∀ m', IsGramFib R σ J n μ ν m' → ∀ S, m S = m' S := by
  intro F E _ _ _ _ _ σ hσ M J hJ R _ _ _ _ _ hR n μ ν m hμ hν hm m' hm' S
  have hU := GlobalTheory.CompanionTheory.SW.KUnits.units_val_isOpenEmbedding F E σ hσ R hR
  obtain ⟨hTR, hLC, hSC, hT2, -⟩ := id hR
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  obtain ⟨hTK, hLK, hSK, hTK2, -, -, -, hBor, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ R
  haveI := hTK
  haveI := hLK
  haveI := hSK
  haveI := hTK2
  haveI := hBor n M
  obtain ⟨hL, hS2, hT, hB, hg⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hσ R n
  haveI := hL
  haveI := hS2
  haveI := hT
  haveI := hB
  obtain ⟨g, hgc, hgf⟩ := hg M J hJ
  let B : Set (HermR R σ n) := {S | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det}
  have hBo : IsOpen B := by
    have h1 : Continuous fun S : HermR R σ n => (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det :=
      Continuous.matrix_det continuous_subtype_val
    have h2 : B = (fun S : HermR R σ n => (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det) ⁻¹'
        Set.range (Units.val : (R ⊗[F] E)ˣ → R ⊗[F] E) := by
      ext S
      simp [B, IsUnit]
    rw [h2]
    exact hU.isOpen_range.preimage h1
  have hUB : {X | IsUnit (gramR R σ J X).det} = g ⁻¹' B := by
    ext X
    simp [B, hgf X]
  have hι : Function.Injective (Subtype.val : HermR R σ n → Matrix (Fin n) (Fin n) (R ⊗[F] E)) :=
    Subtype.val_injective
  have h1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ (gramR R σ J) Subtype.val (g ⁻¹' B) ν B m := by
    rw [← hUB]; exact hm
  have h2 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ (gramR R σ J) Subtype.val (g ⁻¹' B) ν B m' := by
    rw [← hUB]; exact hm'
  by_cases hS : S ∈ B
  · exact (GlobalTheory.CompanionTheory.SW.FibreUniq.fibreFamily_eq _ _ _ μ ν (gramR R σ J) g Subtype.val hι hgc hgf
      B B hBo hBo subset_rfl m' m h2 h1 S hS)
  · have a := (GlobalTheory.CompanionTheory.SW.FibreFam.fibre_family_basic _ _ _ μ ν (gramR R σ J) g Subtype.val hι hgc hgf
      B hBo m h1).2.1 S hS
    have b := (GlobalTheory.CompanionTheory.SW.FibreFam.fibre_family_basic _ _ _ μ ν (gramR R σ J) g Subtype.val hι hgc hgf
      B hBo m' h2).2.1 S hS
    rw [a, b]

end GlobalTheory.CompanionTheory.SW.GramFib
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresUniqueAeStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_fiber_measures_unique : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ), ∀ (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)) (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFib R σ J n μ ν m → ∀ m', IsGramFib R σ J n μ ν m' → ∀ S, m S = m' S := by
  first | exact @GlobalTheory.CompanionTheory.SW.GramFib.fibre_unique | exact GlobalTheory.CompanionTheory.SW.GramFib.fibre_unique | (intros; apply GlobalTheory.CompanionTheory.SW.GramFib.fibre_unique <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberConsProductIntegral
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberConsProductIntegral
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂.Coord

theorem schurM_mem {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) (hinv : ∀ y : R ⊗[F] E, sigR R σ (sigR R σ y) = y) {n : ℕ} (t : F) (a : R → Rˣ)
    (S : HermR R σ (n + 1)) :
    schurM R σ t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ HermR R σ n := by
  intro i j
  have hS := S.2 i.succ j.succ
  have ht : sigR R σ (inclR R (algebraMap F E t)) = inclR R (algebraMap F E t) := by
    simp [sigR, inclR]
  simp only [schurM, map_sub, map_mul, hinv, ht]
  rw [hS]
  ring

theorem coords : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → Continuous (fun S : HermR R σ (n + 1) => s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) ∧ ContinuousOn (fun S : HermR R σ (n + 1) => (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))))) {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀} ∧ ContinuousOn (fun S : HermR R σ (n + 1) => cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀} ∧ ContinuousOn (fun S : HermR R σ (n + 1) => schur R σ t a S) {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀} ∧ IsOpen (Bset R σ t a B₀ : Set (HermR R σ (n + 1))) := by
  intro F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm D
  obtain ⟨hTR, hLC, hSC, hT2, hAr, hRed, hUR, -⟩ := D.hR
  have hK := GlobalTheory.T.tensor_locally_compact_ring F E σ D.hCM R
  obtain ⟨hKR, -, -, -, hsig, htr, -⟩ := hK
  have hinv := (GlobalTheory.CompanionTheory.SW.KAlg.algebra_tensor_invol F E σ D.hCM R).2.2.2.1
  have hopenU := GlobalTheory.T.units_open_embedding_local_tensor F E σ D.hCM R D.hR

  have hs0 : Continuous (fun S : HermR R σ (n + 1) =>
      s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) := by
    unfold s0
    have h1 : Continuous (fun S : HermR R σ (n + 1) =>
        (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) 0 0) :=
      (continuous_apply_apply 0 0).comp continuous_subtype_val
    exact continuous_const.mul (htr.comp h1)
  have hA : IsOpen {S : HermR R σ (n + 1) |
      s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀} := D.hB₀.preimage hs0
  have ha : ContinuousOn (fun S : HermR R σ (n + 1) =>
      a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))))
      {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀} :=
    D.hac.comp hs0.continuousOn (fun S hS => hS)

  have hleft : Continuous (fun r : R => r ⊗ₜ[F] (1 : E)) := by
    have : (fun r : R => r ⊗ₜ[F] (1 : E)) = fun r : R => r • (1 : R ⊗[F] E) := by
      funext r
      simp [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul']
    rw [this]
    exact (continuous_id (X := R)).smul (continuous_const (y := (1 : R ⊗[F] E)))
  have hc : ContinuousOn (fun S : HermR R σ (n + 1) =>
      cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))
      {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀} := by
    refine continuousOn_pi.2 fun j => ?_
    have hent : Continuous (fun S : HermR R σ (n + 1) =>
        (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) 0 j.succ) :=
      (continuous_apply_apply 0 j.succ).comp continuous_subtype_val
    have hu : ContinuousOn (fun S : HermR R σ (n + 1) =>
        ((((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))))⁻¹ : Rˣ) : R)))
        {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀} :=
      (Units.continuous_val (M := R)).comp_continuousOn ha.inv
    have hfac : (fun S : HermR R σ (n + 1) =>
        cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) j) =
        fun S : HermR R σ (n + 1) =>
        (((((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))))⁻¹ : Rˣ) : R) ⊗ₜ[F] (1 : E)) *
          ((1 : R) ⊗ₜ[F] (algebraMap F E t⁻¹))) *
          (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) 0 j.succ := by
      funext S
      simp [cvec, Algebra.TensorProduct.tmul_mul_tmul]
    rw [hfac]
    exact ((hleft.comp_continuousOn hu).mul continuousOn_const).mul hent.continuousOn

  have hM : ContinuousOn (fun S : HermR R σ (n + 1) =>
      schurM R σ t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))
      {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀} := by
    refine continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => ?_
    have hent : Continuous (fun S : HermR R σ (n + 1) =>
        (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) i.succ j.succ) :=
      (continuous_apply_apply i.succ j.succ).comp continuous_subtype_val
    have hci := (continuous_apply i).comp_continuousOn hc
    have hcj := (continuous_apply j).comp_continuousOn hc
    exact hent.continuousOn.sub (((hsig.comp_continuousOn hci).mul continuousOn_const).mul hcj)
  have hsc : ∀ S : HermR R σ (n + 1),
      (schur R σ t a S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) =
        schurM R σ t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) :=
    fun S => schur_coe R σ t a S (schurM_mem R σ hinv t a S)
  have hcoe : ContinuousOn (fun S : HermR R σ (n + 1) =>
      (schur R σ t a S : Matrix (Fin n) (Fin n) (R ⊗[F] E)))
      {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀} := by
    simpa only [hsc] using hM
  have hschur : ContinuousOn (fun S : HermR R σ (n + 1) => schur R σ t a S)
      {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀} :=
    (Topology.IsInducing.subtypeVal.continuousOn_iff).2 hcoe
  refine ⟨hs0, ha, hc, hschur, ?_⟩

  have hdet : ContinuousOn (fun S : HermR R σ (n + 1) =>
      (schur R σ t a S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det)
      {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀} :=
    (continuous_id.matrix_det).comp_continuousOn hcoe
  have hU : IsOpen {y : R ⊗[F] E | IsUnit y} := by
    have : {y : R ⊗[F] E | IsUnit y} = Set.range (Units.val : (R ⊗[F] E)ˣ → R ⊗[F] E) := by
      ext y; simp [IsUnit]
    rw [this]
    exact hopenU.isOpen_range
  have := hdet.isOpen_inter_preimage hA hU
  exact this

end GlobalTheory.CompanionTheory.SW.PiLocalization₂.Coord
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberConsProductIntegralStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuousOn_schur_coordinates_and_isOpen_Bset : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → Continuous (fun S : HermR R σ (n + 1) => s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) ∧ ContinuousOn (fun S : HermR R σ (n + 1) => (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))))) {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀} ∧ ContinuousOn (fun S : HermR R σ (n + 1) => cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀} ∧ ContinuousOn (fun S : HermR R σ (n + 1) => schur R σ t a S) {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀} ∧ IsOpen (Bset R σ t a B₀ : Set (HermR R σ (n + 1))) := by
  first | exact @GlobalTheory.CompanionTheory.SW.PiLocalization₂.Coord.coords | exact GlobalTheory.CompanionTheory.SW.PiLocalization₂.Coord.coords | (intros; apply GlobalTheory.CompanionTheory.SW.PiLocalization₂.Coord.coords <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberConsProductMeasurable
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramBlockOneFirstVectorFormula
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramBlockOneFirstVectorFormula
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

section GramVec

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem hR_blockOne_cons (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (t : E) (x₀ y₀ : R ⊗[F] E) (x y : Fin M → R ⊗[F] E) :
    hR R σ (blockOne t J) (Fin.cons x₀ x : Fin (M + 1) → R ⊗[F] E) (Fin.cons y₀ y) =
      sigR R σ x₀ * inclR R t * y₀ + hR R σ J x y := by
  simp only [hR, hform, JR, Fin.sum_univ_succ, blockOne, Matrix.map_apply, Matrix.of_apply,
    Fin.cons_zero, Fin.cons_succ, map_zero, mul_zero, zero_mul, Finset.sum_const_zero, add_zero,
    zero_add]

theorem hR_zero_left (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (y : Fin M → R ⊗[F] E) :
    hR R σ J (fun _ => 0) y = 0 := by
  simp [hR, hform]

theorem sigR_tmul_one (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (u : R) :
    sigR R σ (u ⊗ₜ[F] (1 : E)) = u ⊗ₜ[F] (1 : E) := by
  simp [sigR]

theorem tmul_one_mul_inclR (R : Type) [CommRing R] [Algebra F R] (u : R) (e : E) :
    (u ⊗ₜ[F] (1 : E)) * inclR R e = u ⊗ₜ[F] e := by
  simp [inclR, Algebra.TensorProduct.tmul_mul_tmul]

theorem tmul_algebraMap (R : Type) [CommRing R] [Algebra F R] (u : R) (t : F) :
    u ⊗ₜ[F] (algebraMap F E t) = (u * algebraMap F R t) ⊗ₜ[F] (1 : E) := by
  rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
    Algebra.smul_def, mul_comm]

theorem gramR_vec (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ)
    (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] (u : R)
    (c : Fin n → R ⊗[F] E) (X : Fin n → Fin M → R ⊗[F] E) :
    gramR R σ (blockOne (algebraMap F E t) J) (vec (u ⊗ₜ[F] (1 : E)) c X) 0 0 =
        (u ^ 2 * algebraMap F R t) ⊗ₜ[F] (1 : E) ∧
      (∀ j : Fin n, gramR R σ (blockOne (algebraMap F E t) J) (vec (u ⊗ₜ[F] (1 : E)) c X) 0 j.succ =
        (u ⊗ₜ[F] (algebraMap F E t)) * c j) ∧
      ∀ i j : Fin n, gramR R σ (blockOne (algebraMap F E t) J) (vec (u ⊗ₜ[F] (1 : E)) c X) i.succ j.succ =
        sigR R σ (c i) * inclR R (algebraMap F E t) * c j + gramR R σ J X i j := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [gramR, vec, Fin.cons_zero]
    rw [hR_blockOne_cons, hR_zero_left, add_zero, sigR_tmul_one, tmul_one_mul_inclR,
      tmul_algebraMap, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    congr 1
    ring
  · intro j
    simp only [gramR, vec, Fin.cons_zero, Fin.cons_succ]
    rw [hR_blockOne_cons, hR_zero_left, add_zero, sigR_tmul_one, tmul_one_mul_inclR]
  · intro i j
    simp only [gramR, vec, Fin.cons_succ]
    rw [hR_blockOne_cons]

end GramVec

end GlobalTheory.CompanionTheory.SW.PiLocalization₂
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramBlockOneFirstVectorFormulaStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_block_one_first_vector_formula : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] (u : R) (c : Fin n → R ⊗[F] E) (X : Fin n → Fin M → R ⊗[F] E), gramR R σ (blockOne (algebraMap F E t) J) (vec (u ⊗ₜ[F] (1 : E)) c X) 0 0 = (u ^ 2 * algebraMap F R t) ⊗ₜ[F] (1 : E) ∧ (∀ j : Fin n, gramR R σ (blockOne (algebraMap F E t) J) (vec (u ⊗ₜ[F] (1 : E)) c X) 0 j.succ = (u ⊗ₜ[F] (algebraMap F E t)) * c j) ∧ ∀ i j : Fin n, gramR R σ (blockOne (algebraMap F E t) J) (vec (u ⊗ₜ[F] (1 : E)) c X) i.succ j.succ = sigR R σ (c i) * inclR R (algebraMap F E t) * c j + gramR R σ J X i j := by
  first | exact @GlobalTheory.CompanionTheory.SW.PiLocalization₂.gramR_vec | exact GlobalTheory.CompanionTheory.SW.PiLocalization₂.gramR_vec | (intros; apply GlobalTheory.CompanionTheory.SW.PiLocalization₂.gramR_vec <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberConsProductMeasurable
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂.GramCoord

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

section Alg

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

theorem corner_half_trace_of_pure_tensor (hfr : Module.finrank F E = 2) {n : ℕ}
    (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) (r : R)
    (h : S 0 0 = r ⊗ₜ[F] (1 : E)) : s0 R S = r := by
  rcases subsingleton_or_nontrivial R with h' | h'
  · exact Subsingleton.elim _ _
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  have hK : Module.finrank R (R ⊗[F] E) = 2 := by rw [Module.finrank_baseChange]; exact hfr
  have hc : (r ⊗ₜ[F] (1 : E) : R ⊗[F] E) = algebraMap R (R ⊗[F] E) r := rfl
  have h2 : algebraMap F R (1 / 2) * 2 = 1 := by
    have : (2 : R) = algebraMap F R 2 := (map_ofNat (algebraMap F R) 2).symm
    rw [this, ← map_mul]; simp
  unfold s0
  rw [h, hc, Algebra.trace_algebraMap, hK, two_nsmul, ← two_mul, ← mul_assoc, h2, one_mul]

variable [NumberField E]

theorem gram_symm (σ : E →ₐ[F] E) (hinv : ∀ y, sigR R σ (sigR R σ y) = y) {M n : ℕ}
    {J : Matrix (Fin M) (Fin M) E} (hJ : ∀ i j, σ (J j i) = J i j)
    (X : Fin n → Fin M → R ⊗[F] E) (p q : Fin n) :
    sigR R σ (gramR R σ J X q p) = gramR R σ J X p q := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gramR, hR, hform, JR, map_sum, map_mul, hinv, Matrix.map_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h : sigR R σ (inclR R (J j i)) = inclR R (J i j) := by
    rw [← hJ i j]; simp [sigR, inclR]
  rw [h]; ring

theorem schurM_mem (σ : E →ₐ[F] E) (hinv : ∀ y, sigR R σ (sigR R σ y) = y) {n : ℕ} (t : F) (a : R → Rˣ)
    (S : HermR R σ (n + 1)) :
    schurM R σ t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ HermR R σ n := by
  intro i j
  have hS : sigR R σ ((S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) j.succ i.succ) =
      (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) i.succ j.succ := S.2 i.succ j.succ
  have hi : sigR R σ (inclR R (algebraMap F E t)) = inclR R (algebraMap F E t) := by
    simp [sigR, inclR]
  simp only [schurM, map_sub, map_mul, hinv, hS, hi]
  ring

end Alg

theorem unit_tmul {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
    {t : F} (ht : t ≠ 0) (u : Rˣ) :
    ((((u⁻¹ : Rˣ) : R) ⊗ₜ[F] (algebraMap F E t⁻¹)) * (((u : Rˣ) : R) ⊗ₜ[F] (algebraMap F E t)) : R ⊗[F] E) = 1 := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, Units.inv_mul, ← map_mul, inv_mul_cancel₀ ht, map_one]
  rfl

theorem coords : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → (∀ x ∈ B₀, ∀ (c : Fin n → R ⊗[F] E) (X : Fin n → Fin M → R ⊗[F] E) (S : HermR R σ (n + 1)), (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) = gramR R σ (blockOne (algebraMap F E t) J) (vec (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E)) c X) → s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) = x ∧ cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) = c ∧ (schur R σ t a S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = gramR R σ J X) ∧ (∀ (S : HermR R σ (n + 1)) (X : Fin n → Fin M → R ⊗[F] E), s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀ → gramR R σ J X = (schur R σ t a S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) → gramR R σ (blockOne (algebraMap F E t) J) (vec (((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) : R) ⊗ₜ[F] (1 : E)) (cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) X) = (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) := by
  intro F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm D
  obtain ⟨-, -, -, -, hart, hred, -⟩ := D.hR
  haveI := hart
  haveI := hred
  obtain ⟨-, -, -, hinv, -, hfix, -⟩ := GlobalTheory.CompanionTheory.SW.KAlg.algebra_tensor_invol F E σ D.hCM R
  have hfr : Module.finrank F E = 2 := D.hCM.2.2.1
  have ht : t ≠ 0 := D.ht
  have hJ' := GlobalTheory.T.block_one_scalar_preserves_nondegenerate F E σ M J D.hJ t ht
  refine ⟨?_, ?_⟩
  · intro x hx c X S hS
    obtain ⟨h00, h0j, hij⟩ := GlobalTheory.T.gram_block_one_first_vector_formula F E σ M J t n R ((a x : Rˣ) : R) c X
    rw [← hS] at h00 h0j hij
    have hx0 : (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) 0 0 = x ⊗ₜ[F] (1 : E) := by
      rw [h00, ← D.hsq x hx]
    have hs0 := corner_half_trace_of_pure_tensor R hfr _ x hx0
    have hc : cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) = c := by
      funext j
      simp only [cvec]
      rw [hs0, h0j j, ← mul_assoc, unit_tmul ht, one_mul]
    refine ⟨hs0, hc, ?_⟩
    rw [schur_coe R σ t a S (schurM_mem R σ hinv t a S)]
    ext i j
    simp only [schurM]
    rw [hc, hij i j, add_sub_cancel_left]
  · intro S X hB hX
    obtain ⟨h00, h0j, hij⟩ := GlobalTheory.T.gram_block_one_first_vector_formula F E σ M J t n R
      ((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) : Rˣ) : R)
      (cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) X
    have hH := gram_symm R σ hinv hJ'.1 (vec
      (((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) : Rˣ) : R) ⊗ₜ[F] (1 : E))
      (cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) X)
    obtain ⟨r, hr⟩ := hfix ((S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) 0 0) (S.2 0 0)
    have hsr := corner_half_trace_of_pure_tensor R hfr _ r hr
    have hrow : ∀ j : Fin n, gramR R σ (blockOne (algebraMap F E t) J) (vec
        (((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) : Rˣ) : R) ⊗ₜ[F] (1 : E))
        (cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) X) 0 j.succ =
        (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) 0 j.succ := by
      intro j
      rw [h0j j]
      simp only [cvec]
      rw [← mul_assoc, mul_comm (_ ⊗ₜ[F] (algebraMap F E t)), unit_tmul ht, one_mul]
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases ?_ (fun j => ?_) j
      · rw [h00, hr, ← D.hsq _ hB, hsr]
      · exact hrow j
    · refine Fin.cases ?_ (fun j => ?_) j
      · rw [← hH i.succ 0, hrow i]
        exact S.2 i.succ 0
      · rw [hij i j, congrFun (congrFun hX i) j, schur_coe R σ t a S (schurM_mem R σ hinv t a S)]
        simp only [schurM]
        rw [add_sub_cancel]

end GlobalTheory.CompanionTheory.SW.PiLocalization₂.GramCoord
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberConsProductMeasurableStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_block_one_schur_coordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → (∀ x ∈ B₀, ∀ (c : Fin n → R ⊗[F] E) (X : Fin n → Fin M → R ⊗[F] E) (S : HermR R σ (n + 1)), (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) = gramR R σ (blockOne (algebraMap F E t) J) (vec (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E)) c X) → s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) = x ∧ cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) = c ∧ (schur R σ t a S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = gramR R σ J X) ∧ (∀ (S : HermR R σ (n + 1)) (X : Fin n → Fin M → R ⊗[F] E), s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀ → gramR R σ J X = (schur R σ t a S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) → gramR R σ (blockOne (algebraMap F E t) J) (vec (((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) : R) ⊗ₜ[F] (1 : E)) (cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) X) = (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) := by
  first | exact @GlobalTheory.CompanionTheory.SW.PiLocalization₂.GramCoord.coords | exact GlobalTheory.CompanionTheory.SW.PiLocalization₂.GramCoord.coords | (intros; apply GlobalTheory.CompanionTheory.SW.PiLocalization₂.GramCoord.coords <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianFormDiagonalizesOverField
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.AlgDiag

theorem diag_hermitian : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E), IsHermND σ T → ∃ (g : GL (Fin n) E) (D : Fin n → Fˣ), cT (σ : E →+* E) (g : Matrix (Fin n) (Fin n) E) * T * g = Matrix.diagonal fun i => algebraMap F E (D i : F) :=
  _root_.UpperTheory.Reformulated.B.Gka4.diag_hermitian

end GlobalTheory.CompanionTheory.SW.AlgDiag
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianLocalContinuousCongruenceSection
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianLocalContinuousCongruenceSection
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section
namespace GlobalTheory.CompanionTheory.SW

theorem exists_local_section : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ) (S : HermR R σ n), IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det → ∃ (B : Set (HermR R σ n)) (g : HermR R σ n → GL (Fin n) (R ⊗[F] E)), IsOpen B ∧ S ∈ B ∧ ContinuousOn g B ∧ g S = 1 ∧ ∀ S' ∈ B, (S' : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = cT (sigR R σ) (g S' : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * (g S' : Matrix (Fin n) (Fin n) (R ⊗[F] E)) := by
  intro F E _ _ _ _ _ σ hσ R _ _ _ _ _ hR n S hS
  obtain ⟨Q, o, -, -, ho, hform⟩ := GlobalTheory.T.hermitian_orbit_local_section_subgroup F E σ hσ R hR n S hS
  have hc : cT (sigR R σ) (1 : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = 1 := by
    ext i j
    by_cases h : i = j
    · subst h; simp [cT]
    · simp [cT, Matrix.one_apply, h, Ne.symm h]
  have ho1 : o 1 = S := by
    apply Subtype.ext
    rw [hform]
    simp [hc]
  have hinv : Function.LeftInverse (Function.invFun o) o := Function.leftInverse_invFun ho.injective
  refine ⟨Set.range o, fun S' => ((Function.invFun o S' : Q) : GL (Fin n) (R ⊗[F] E)),
    ho.isOpen_range, ⟨1, ho1⟩, ?_, ?_, ?_⟩
  · have hcont : ContinuousOn (Function.invFun o) (Set.range o) := by
      rw [continuousOn_iff_continuous_restrict]
      have h1 : (fun y : Set.range o => Function.invFun o y.1) = ho.isEmbedding.toHomeomorph.symm := by
        funext y
        obtain ⟨_, x, rfl⟩ := y
        show Function.invFun o (o x) = _
        rw [hinv x]
        exact ho.isEmbedding.toHomeomorph.eq_symm_apply.2 (Subtype.ext rfl)
      have h2 : Continuous (fun y : Set.range o => Function.invFun o y.1) := by
        rw [h1]
        exact Homeomorph.continuous _
      exact h2
    exact continuous_subtype_val.comp_continuousOn hcont
  · show ((Function.invFun o S : Q) : GL (Fin n) (R ⊗[F] E)) = 1
    rw [← ho1, hinv 1]
    rfl
  · rintro _ ⟨x, rfl⟩
    simp only [hinv x]
    exact hform x

end GlobalTheory.CompanionTheory.SW
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianLocalContinuousCongruenceSectionStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_local_continuous_congruence_section : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ) (S : HermR R σ n), IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det → ∃ (B : Set (HermR R σ n)) (g : HermR R σ n → GL (Fin n) (R ⊗[F] E)), IsOpen B ∧ S ∈ B ∧ ContinuousOn g B ∧ g S = 1 ∧ ∀ S' ∈ B, (S' : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = cT (sigR R σ) (g S' : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * (g S' : Matrix (Fin n) (Fin n) (R ⊗[F] E)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.exists_local_section | exact GlobalTheory.CompanionTheory.SW.exists_local_section | (intros; apply GlobalTheory.CompanionTheory.SW.exists_local_section <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasureOrthogonalExtension
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasureOrthogonalExtension
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.TupFubini

variable {T : Type} [MeasurableSpace T]

theorem measurable_cons_tail {A : Type} [MeasurableSpace A] {n : ℕ} (x : A) :
    Measurable (fun Y : Fin n → A => (Fin.cons x Y : Fin (n + 1) → A)) := by
  refine measurable_pi_iff.2 fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simpa using measurable_pi_apply j

theorem piFinSuccAbove_symm_apply {A : Type} [MeasurableSpace A] {n : ℕ} (x : A) (Y : Fin n → A) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => A) 0).symm (x, Y) = Fin.cons x Y := by
  apply (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => A) 0).injective
  rw [MeasurableEquiv.apply_symm_apply]
  simp [MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv]

theorem lintegral_tuple_succ (m : Measure T) [SigmaFinite m] (n N : ℕ)
    (ψ : (Fin (n + 1) → Fin N → T) → ℝ≥0∞) (hψ : Measurable ψ) :
    ∫⁻ X, ψ X ∂(Measure.pi fun _ : Fin (n + 1) => Measure.pi fun _ : Fin N => m) =
      ∫⁻ y : Fin 1 → Fin N → T, ∫⁻ Y : Fin n → Fin N → T, ψ (Fin.cons (y 0) Y)
        ∂(Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin N => m)
        ∂(Measure.pi fun _ : Fin 1 => Measure.pi fun _ : Fin N => m) := by
  set P : Measure (Fin N → T) := Measure.pi fun _ : Fin N => m with hP
  have h1 := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => P) 0
  have h2 := measurePreserving_funUnique P (Fin 1)
  have hg : Measurable fun p : (Fin N → T) × (Fin n → Fin N → T) =>
      ψ ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Fin N → T) 0).symm p) :=
    hψ.comp (MeasurableEquiv.measurable _)
  rw [← h1.symm.lintegral_comp hψ, lintegral_prod _ hg.aemeasurable,
    ← h2.lintegral_comp hg.lintegral_prod_right']
  refine lintegral_congr fun y => lintegral_congr fun Y => ?_
  rw [piFinSuccAbove_symm_apply]
  rfl

theorem lintegral_tuple_first_coord (m : Measure T) [SigmaFinite m] (n M : ℕ)
    (ψ : (Fin n → Fin (M + 1) → T) → ℝ≥0∞) (hψ : Measurable ψ) :
    ∫⁻ Y, ψ Y ∂(Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin (M + 1) => m) =
      ∫⁻ c : Fin n → T, ∫⁻ X : Fin n → Fin M → T, ψ (fun a => Fin.cons (c a) (X a))
        ∂(Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin M => m)
        ∂(Measure.pi fun _ : Fin n => m) := by
  let e₁ := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (M + 1) => T) 0
  have h₁ : MeasurePreserving e₁ (Measure.pi fun _ : Fin (M + 1) => m)
      (m.prod (Measure.pi fun _ : Fin M => m)) :=
    measurePreserving_piFinSuccAbove (fun _ : Fin (M + 1) => m) 0
  have h₂ := measurePreserving_pi (fun _ : Fin n => Measure.pi fun _ : Fin (M + 1) => m)
    (fun _ : Fin n => m.prod (Measure.pi fun _ : Fin M => m)) (f := fun _ => e₁) (fun _ => h₁)
  have h₃ := measurePreserving_arrowProdEquivProdArrow T (Fin M → T) (Fin n) (fun _ => m)
    (fun _ => Measure.pi fun _ : Fin M => m)
  have h₄ := h₃.comp h₂
  let g : (Fin n → T) × (Fin n → Fin M → T) → Fin n → Fin (M + 1) → T :=
    fun p a => e₁.symm (p.1 a, p.2 a)
  have hg : Measurable g := by
    refine measurable_pi_iff.2 fun a => e₁.symm.measurable.comp ?_
    exact ((measurable_pi_apply a).comp measurable_fst).prodMk
      ((measurable_pi_apply a).comp measurable_snd)
  have hgi : ∀ Y, g ((MeasurableEquiv.arrowProdEquivProdArrow T (Fin M → T) (Fin n) ∘
      fun Y a => e₁ (Y a)) Y) = Y := by
    intro Y
    funext a
    exact e₁.symm_apply_apply (Y a)
  have hψg : Measurable (ψ ∘ g) := hψ.comp hg
  calc ∫⁻ Y, ψ Y ∂(Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin (M + 1) => m)
      = ∫⁻ Y, (ψ ∘ g) ((MeasurableEquiv.arrowProdEquivProdArrow T (Fin M → T) (Fin n) ∘
          fun Y a => e₁ (Y a)) Y) ∂(Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin (M + 1) => m) :=
        lintegral_congr fun Y => by simp only [Function.comp_apply (f := ψ), hgi]
    _ = _ := h₄.lintegral_comp hψg
    _ = _ := lintegral_prod _ hψg.aemeasurable
    _ = _ := by
      refine lintegral_congr fun c => lintegral_congr fun X => ?_
      simp only [Function.comp_apply, g]
      congr 1
      funext a
      exact piFinSuccAbove_symm_apply (c a) (X a)

end GlobalTheory.CompanionTheory.SW.TupFubini

namespace GlobalTheory.CompanionTheory.SW

theorem lintegral_tuple_moving_frame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ (lam : Measure R), lam.IsAddHaarMeasure → ∀ (n : ℕ) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ J), Measurable s → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∫⁻ X, φ X ∂(coordW R b lam (n + 1) (M + 1)) = ∫⁻ y, ∫⁻ c : Fin n → R ⊗[F] E, ∫⁻ X : Fin n → Fin M → R ⊗[F] E, φ (Fin.cons (y 0) (actW R σ J (s y) (fun a => Fin.cons (c a) (X a)))) ∂(coordW R b lam n M) ∂(Measure.pi fun _ => coordK R b lam) ∂(coordW R b lam 1 (M + 1)) := by
  intro F E _ _ _ _ _ σ hCM M J hJ R _ _ _ _ _ hR d b lam hlam n s _ φ hφ
  obtain ⟨i₁, i₂, i₃, i₄, -⟩ := id hR
  obtain ⟨k₁, k₂, k₃, k₄, -, -, -, hBorel, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM R
  obtain ⟨hK, hW, -⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hCM R d b lam hlam
  have : SigmaFinite (coordK R b lam) := inferInstance
  have hact : ∀ h : HA R σ J, Measurable (actW R σ J h :
      (Fin n → Fin (M + 1) → R ⊗[F] E) → Fin n → Fin (M + 1) → R ⊗[F] E) := by
    intro h
    have := hBorel n (M + 1)
    have hc := ((GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hCM (M + 1) J hJ R).2.2.2.2.2 n).1
    exact (hc.comp (Continuous.prodMk_right h)).measurable
  have key : ∀ y : Fin 1 → Fin (M + 1) → R ⊗[F] E,
      ∫⁻ Y : Fin n → Fin (M + 1) → R ⊗[F] E, φ (Fin.cons (y 0) Y) ∂(coordW R b lam n (M + 1)) =
      ∫⁻ c : Fin n → R ⊗[F] E, ∫⁻ X : Fin n → Fin M → R ⊗[F] E,
        φ (Fin.cons (y 0) (actW R σ J (s y) (fun a => Fin.cons (c a) (X a))))
        ∂(coordW R b lam n M) ∂(Measure.pi fun _ => coordK R b lam) := by
    intro y
    have hinv := GlobalTheory.T.unitary_action_preserves_haar_local F E σ hCM (M + 1) J hJ R hR n (coordW R b lam n (M + 1)) (hW n (M + 1)) (s y)
    have hf : Measurable fun Y : Fin n → Fin (M + 1) → R ⊗[F] E =>
        φ (Fin.cons (y 0) Y) := hφ.comp (TupFubini.measurable_cons_tail (y 0))
    calc ∫⁻ Y : Fin n → Fin (M + 1) → R ⊗[F] E, φ (Fin.cons (y 0) Y) ∂(coordW R b lam n (M + 1))
        = ∫⁻ Y, φ (Fin.cons (y 0) Y) ∂((coordW R b lam n (M + 1)).map (actW R σ J (s y))) := by
          rw [hinv]
      _ = ∫⁻ Y, φ (Fin.cons (y 0) (actW R σ J (s y) Y)) ∂(coordW R b lam n (M + 1)) :=
          lintegral_map hf (hact (s y))
      _ = _ := TupFubini.lintegral_tuple_first_coord (coordK R b lam) n M _ (hf.comp (hact (s y)))
  calc ∫⁻ X, φ X ∂(coordW R b lam (n + 1) (M + 1))
      = ∫⁻ y, ∫⁻ Y : Fin n → Fin (M + 1) → R ⊗[F] E, φ (Fin.cons (y 0) Y)
          ∂(coordW R b lam n (M + 1)) ∂(coordW R b lam 1 (M + 1)) :=
        TupFubini.lintegral_tuple_succ (coordK R b lam) n (M + 1) φ hφ
    _ = _ := lintegral_congr key

end GlobalTheory.CompanionTheory.SW
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasureOrthogonalExtensionStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_coordW_succ_eq_iterated_of_unitary_section : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ (lam : Measure R), lam.IsAddHaarMeasure → ∀ (n : ℕ) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ J), Measurable s → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∫⁻ X, φ X ∂(coordW R b lam (n + 1) (M + 1)) = ∫⁻ y, ∫⁻ c : Fin n → R ⊗[F] E, ∫⁻ X : Fin n → Fin M → R ⊗[F] E, φ (Fin.cons (y 0) (actW R σ J (s y) (fun a => Fin.cons (c a) (X a)))) ∂(coordW R b lam n M) ∂(Measure.pi fun _ => coordK R b lam) ∂(coordW R b lam 1 (M + 1)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.lintegral_tuple_moving_frame | exact GlobalTheory.CompanionTheory.SW.lintegral_tuple_moving_frame | (intros; apply GlobalTheory.CompanionTheory.SW.lintegral_tuple_moving_frame <;> assumption)
end
end
