module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalDensitiesBoundedAlmostAll
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompactAdelesRationalPointsFiniteEventuallyZero

@[expose] public section

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.EulerProductLocalDensitiesConverges
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.EulerProductLocalDensitiesConverges
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW

theorem mass_fibre_summable :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n : ℕ), n = 0 ∨ n + 2 ≤ M → ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), (∀ v, IsStdV v (lam v)) → ∀ (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ n → Measure (Fin n → Fin M → Fv F v ⊗[F] E)), (∀ v, IsGramFib (Fv F v) σ J n (coordW (Fv F v) b (lam v) n M) (coordHerm (Fv F v) σ b (lam v) n) (m v)) → (∀ v, m v (hermOf (Fv F v) σ T hT) (latV b v) < ⊤) ∧ Summable fun v => |(m v (hermOf (Fv F v) σ T hT) (latV b v)).toReal - 1| := by
  intro F E _ _ _ _ _ σ hCM M J hJ n hn T hT hdet d b lam hlam m hm
  refine ⟨?_, ?_⟩
  · intro v
    have hloc : IsLocR (Fv F v) := GlobalTheory.T.completion_is_local_ring F v
    obtain ⟨hTR, hLC, hSC, hT2, -⟩ := id hloc
    haveI := hTR
    haveI := hLC
    haveI := hSC
    haveI := hT2
    haveI : BorelSpace (Fv F v) := ⟨rfl⟩
    have hh := GlobalTheory.T.coordinate_haar_measure F E σ hCM (Fv F v) d b (lam v) (hlam v).1
    haveI hW := hh.2.1 n M
    haveI hH := hh.2.2 n
    have hlf := (GlobalTheory.T.gram_fiber_measure_locallyFinite_and_ne_zero_of_isOpen F E σ hCM M J hJ (Fv F v) hloc n _ _ (m v) hW hH (hm v)
      (hermOf (Fv F v) σ T hT)).1
    exact (GlobalTheory.T.local_lattice_compact_open_unit_volume F E σ hCM d b n M v).1.measure_lt_top
  · obtain ⟨C, hC⟩ := GlobalTheory.T.local_densities_bounded_almost_all F E σ hCM M J hJ n hn T hT hdet d b
    refine Summable.of_norm_bounded_eventually
      (g := fun v : HeightOneSpectrum (𝓞 F) => C * (1 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2))
      ((GlobalTheory.CompanionTheory.SW.Primes.summable_one_div_absNorm_sq F).mul_left C) ?_
    filter_upwards [hC] with v hv
    have := hv (lam v) (hlam v) (m v) (hm v)
    rw [Real.norm_eq_abs, abs_abs]
    simpa [div_eq_mul_inv] using this

end GlobalTheory.CompanionTheory.SW
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.EulerProductLocalDensitiesConvergesStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.euler_product_local_densities_converges : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n : ℕ), n = 0 ∨ n + 2 ≤ M → ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), (∀ v, IsStdV v (lam v)) → ∀ (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ n → Measure (Fin n → Fin M → Fv F v ⊗[F] E)), (∀ v, IsGramFib (Fv F v) σ J n (coordW (Fv F v) b (lam v) n M) (coordHerm (Fv F v) σ b (lam v) n) (m v)) → (∀ v, m v (hermOf (Fv F v) σ T hT) (latV b v) < ⊤) ∧ Summable fun v => |(m v (hermOf (Fv F v) σ T hT) (latV b v)).toReal - 1| := by
  first | exact @GlobalTheory.CompanionTheory.SW.mass_fibre_summable | exact GlobalTheory.CompanionTheory.SW.mass_fibre_summable | (intros; apply GlobalTheory.CompanionTheory.SW.mass_fibre_summable <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdeleRingCocompactDiscreteNumberField
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdeleRingCocompactDiscreteNumberField
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.Adelic.FieldCocompact

theorem discrete_cocompact : ∀ (F : Type) [Field F] [NumberField F],
    (∃ C : Set (AdeleRing (𝓞 F) F), IsCompact C ∧
      ∀ y, ∃ l : F, y - algebraMap F (AdeleRing (𝓞 F) F) l ∈ C) ∧
    (∀ C : Set (AdeleRing (𝓞 F) F), IsCompact C →
      {l : F | algebraMap F (AdeleRing (𝓞 F) F) l ∈ C}.Finite) ∧
    NoncompactSpace (AdeleRing (𝓞 F) F) := by
  intro F _ _
  have hfin : ∀ C : Set (AdeleRing (𝓞 F) F), IsCompact C →
      {l : F | algebraMap F (AdeleRing (𝓞 F) F) l ∈ C}.Finite := fun C hC =>
    GlobalTheory.Eis.Conv.Discr.finite_of_isCompact (algebraMap F (AdeleRing (𝓞 F) F))
      (GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero F) hC
  refine ⟨GlobalTheory.AdeleCocompact.exists_compact_adele F, hfin, ⟨fun h => ?_⟩⟩
  have h1 := hfin Set.univ h
  simp only [Set.mem_univ, Set.setOf_true] at h1
  exact Set.infinite_univ h1

end GlobalTheory.CompanionTheory.Adelic.FieldCocompact
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdeleRingCocompactDiscreteNumberFieldStatement
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adele_ring_cocompact_discrete_number_field : ∀ (F : Type) [Field F] [NumberField F], (∃ C : Set (AdeleRing (𝓞 F) F), IsCompact C ∧ ∀ y, ∃ l : F, y - algebraMap F (AdeleRing (𝓞 F) F) l ∈ C) ∧ (∀ C : Set (AdeleRing (𝓞 F) F), IsCompact C → {l : F | algebraMap F (AdeleRing (𝓞 F) F) l ∈ C}.Finite) ∧ NoncompactSpace (AdeleRing (𝓞 F) F) := by
  first | exact @GlobalTheory.CompanionTheory.Adelic.FieldCocompact.discrete_cocompact | exact GlobalTheory.CompanionTheory.Adelic.FieldCocompact.discrete_cocompact | (intros; apply GlobalTheory.CompanionTheory.Adelic.FieldCocompact.discrete_cocompact <;> assumption)
end
end
