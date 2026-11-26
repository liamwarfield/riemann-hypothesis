module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.EulerProductLocalDensitiesConverges
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteProductRenormalization
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilOrbitalMeasure
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsUnipotentInvariantCompactlySupportedWeight

@[expose] public section

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RationalTuplesDiscreteCocompactAdelic
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RationalTuplesDiscreteCocompactAdelic
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.CocW

theorem repr_inclR {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    {d : ℕ} (b : Module.Basis (Fin d) F E) (e : E) (k : Fin d) :
    (Algebra.TensorProduct.basis R b).repr (inclR R e) k = algebraMap F R (b.repr e k) := by
  have : inclR (F := F) R e = (1 : R) ⊗ₜ[F] e := rfl
  rw [this, Algebra.TensorProduct.basis_repr_tmul]
  simp

theorem scalar (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) :
    (∃ C : Set (AF F ⊗[F] E), IsCompact C ∧ ∀ y, ∃ e : E, y - inclR (AF F) e ∈ C) ∧
    (∀ C : Set (AF F ⊗[F] E), IsCompact C → {e : E | inclR (AF F) e ∈ C}.Finite) ∧
    NoncompactSpace (AF F ⊗[F] E) := by
  obtain ⟨⟨hlc, hsc, ht2⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  obtain ⟨hC, hfin, hnc⟩ := GlobalTheory.T.adele_ring_cocompact_discrete_number_field F
  obtain ⟨-, -, -, -, -, -, hb, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ h (AF F)
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have hd : 0 < Module.finrank F E := by rw [h.2.2.1]; norm_num
  let b := Module.finBasis F E
  let φ : AF F ⊗[F] E → Fin (Module.finrank F E) → AF F :=
    fun y k => (Algebra.TensorProduct.basis (AF F) b).repr y k
  have hφ : IsHomeomorph φ := hb _ b
  have hcont : ∀ k, Continuous fun y => φ y k := fun k => (continuous_apply k).comp hφ.continuous
  have hsub : ∀ y e k, φ (y - inclR (AF F) e) k = φ y k - algebraMap F (AF F) (b.repr e k) := by
    intro y e k
    simp only [φ, map_sub, Finsupp.sub_apply, repr_inclR]
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨C, hCc, hCy⟩ := hC
    refine ⟨φ ⁻¹' Set.pi Set.univ fun _ => C, ?_, ?_⟩
    · exact (hφ.homeomorph φ).isCompact_preimage.2 (isCompact_univ_pi fun _ => hCc)
    · intro y
      choose l hl using fun k => hCy (φ y k)
      refine ⟨∑ k, l k • b k, ?_⟩
      intro k _
      rw [hsub, b.repr_sum_self]
      exact hl k
  · intro C hCc
    have hS : ∀ k, {l : F | algebraMap F (AF F) l ∈ (fun y => φ y k) '' C}.Finite :=
      fun k => hfin _ (hCc.image (hcont k))
    refine ((Set.Finite.pi hS).preimage (f := fun (e : E) k => b.repr e k) ?_).subset ?_
    · intro x _ y _ hxy
      apply b.repr.injective
      ext k
      exact congrFun hxy k
    · intro e he k _
      refine ⟨inclR (AF F) e, he, ?_⟩
      exact repr_inclR (AF F) b e k
  · refine ⟨fun hK => hnc.noncompact_univ ?_⟩
    have hsurj : Function.Surjective fun y => φ y ⟨0, hd⟩ := by
      intro r
      obtain ⟨y, hy⟩ := hφ.surjective fun _ => r
      exact ⟨y, congrFun hy _⟩
    have := hK.image (hcont ⟨0, hd⟩)
    rwa [Set.image_univ, hsurj.range_eq] at this

theorem main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n M : ℕ), (∃ C : Set (Fin n → Fin M → AF F ⊗[F] E), IsCompact C ∧ ∀ y, ∃ X : Fin n → Fin M → E, y - ratTup (AF F) X ∈ C) ∧ (∀ C : Set (Fin n → Fin M → AF F ⊗[F] E), IsCompact C → {X : Fin n → Fin M → E | ratTup (AF F) X ∈ C}.Finite) ∧ (0 < n → 0 < M → NoncompactSpace (Fin n → Fin M → AF F ⊗[F] E)) := by
  intro F E _ _ _ _ _ σ h n M
  obtain ⟨⟨C, hCc, hCy⟩, hfin, hnc⟩ := scalar F E σ h
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => C,
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hCc, ?_⟩
    intro y
    choose X hX using fun a i => hCy (y a i)
    exact ⟨X, fun a _ i _ => hX a i⟩
  · intro C hCc
    have hcont : ∀ a i, Continuous fun Y : Fin n → Fin M → AF F ⊗[F] E => Y a i :=
      fun a i => (continuous_apply i).comp (continuous_apply a)
    have hS : ∀ a i, {e : E | inclR (AF F) e ∈ (fun Y : Fin n → Fin M → AF F ⊗[F] E => Y a i) '' C}.Finite :=
      fun a i => hfin _ (hCc.image (hcont a i))
    refine (Set.Finite.pi fun a => Set.Finite.pi (hS a)).subset ?_
    intro X hX a _ i _
    exact ⟨ratTup (AF F) X, hX, rfl⟩
  · intro hn hM
    refine ⟨fun hK => hnc.noncompact_univ ?_⟩
    have hsurj : Function.Surjective fun Y : Fin n → Fin M → AF F ⊗[F] E => Y ⟨0, hn⟩ ⟨0, hM⟩ :=
      fun r => ⟨fun _ _ => r, rfl⟩
    have hc : Continuous fun Y : Fin n → Fin M → AF F ⊗[F] E => Y ⟨0, hn⟩ ⟨0, hM⟩ :=
      (continuous_apply (⟨0, hM⟩ : Fin M)).comp (continuous_apply (⟨0, hn⟩ : Fin n))
    have := hK.image hc
    rwa [Set.image_univ, hsurj.range_eq] at this

end GlobalTheory.CompanionTheory.SW.CocW
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RationalTuplesDiscreteCocompactAdelicStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_tuples_discrete_cocompact_adelic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n M : ℕ), (∃ C : Set (Fin n → Fin M → AF F ⊗[F] E), IsCompact C ∧ ∀ y, ∃ X : Fin n → Fin M → E, y - ratTup (AF F) X ∈ C) ∧ (∀ C : Set (Fin n → Fin M → AF F ⊗[F] E), IsCompact C → {X : Fin n → Fin M → E | ratTup (AF F) X ∈ C}.Finite) ∧ (0 < n → 0 < M → NoncompactSpace (Fin n → Fin M → AF F ⊗[F] E)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.CocW.main | exact GlobalTheory.CompanionTheory.SW.CocW.main | (intros; apply GlobalTheory.CompanionTheory.SW.CocW.main <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilFormulaRange
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilFormulaRange
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.Fact

theorem exists_test_set {α : Type} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ] (h : μ ≠ 0) :
    ∃ s, MeasurableSet s ∧ μ s ≠ 0 ∧ μ s ≠ ⊤ := by
  by_contra hcon
  push Not at hcon
  apply h
  apply Measure.measure_univ_eq_zero.mp
  rw [← iUnion_spanningSets μ]
  refine measure_iUnion_null fun i => ?_
  by_contra h0
  exact (measure_spanningSets_lt_top μ i).ne (hcon _ (measurableSet_spanningSets μ i) h0)

theorem fib_facts {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J)
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R]
    (hR : IsLocR R) {n : ℕ} (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b)
    (hdet : T.det ≠ 0) {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R)
    (hlam : lam.IsAddHaarMeasure) (mm : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E))
    (hm : IsGramFib R σ J n (coordW R b lam n M) (coordHerm R σ b lam n) mm) :
    SigmaFinite (mm (hermOf R σ T hT)) ∧
      (mm (hermOf R σ T hT) = 0 → ∀ X, gramR R σ J X ≠ T.map (inclR R)) := by
  have hR' := hR
  obtain ⟨h1, h2, h3, h4, -⟩ := hR'
  have hk := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM R
  have hh := GlobalTheory.T.coordinate_haar_measure F E σ hCM R d b lam hlam
  have hsc : SecondCountableTopology (R ⊗[F] E) := hk.2.2.1
  have hloc := GlobalTheory.T.gram_fiber_measure_locallyFinite_and_ne_zero_of_isOpen F E σ hCM M J hJ R hR n _ _ mm (hh.2.1 n M) (hh.2.2 n) hm
    (hermOf R σ T hT)
  obtain ⟨hlf, hpos⟩ := hloc
  refine ⟨inferInstance, fun h0 X hX => ?_⟩
  have hunit : IsUnit (gramR R σ J X).det := by
    rw [hX]
    have : (T.map (inclR R : E →+* R ⊗[F] E)).det = inclR R T.det :=
      (RingHom.map_det (inclR R : E →+* R ⊗[F] E) T).symm
    rw [this]
    exact (isUnit_iff_ne_zero.mpr hdet).map _
  exact hpos Set.univ isOpen_univ ⟨X, Set.mem_univ _, hX, hunit⟩ (by simp [h0])

theorem borel_tup {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    (hR : IsLocR R) (n M : ℕ) : BorelSpace (Fin n → Fin M → R ⊗[F] E) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := hR
  exact (GlobalTheory.T.tensor_locally_compact_ring F E σ hCM R).2.2.2.2.2.2.2.1 n M

theorem pureL_insert {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d M n : ℕ}
    (b : Module.Basis (Fin d) F E) [DecidableEq (HeightOneSpectrum (𝓞 F))]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S)
    (φinf : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞)
    (φ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℝ≥0∞)
    (X : Fin n → Fin M → AF F ⊗[F] E) :
    pureL b (insert v S) φinf (Function.update φ v ((latV b v).indicator 1)) X = pureL b S φinf φ X := by
  have hprod : ∏ w ∈ S, (Function.update φ v ((latV b v).indicator 1)) w (projV w (projFin X)) =
      ∏ w ∈ S, φ w (projV w (projFin X)) :=
    Finset.prod_congr rfl fun w hw => by
      have hne : w ≠ v := fun h => hv (h ▸ hw)
      rw [Function.update_of_ne hne]
  have hmem : X ∈ intOff b S ↔
      X ∈ intOff b (insert v S) ∧ projV v (projFin X) ∈ latV b v := by
    constructor
    · intro h
      exact ⟨fun w hw => h w (fun hs => hw (Finset.mem_insert_of_mem hs)), h v hv⟩
    · rintro ⟨h1, h2⟩ w hw
      by_cases hwv : w = v
      · subst hwv; exact h2
      · exact h1 w (by simp [Finset.mem_insert, hwv, hw])
  unfold pureL
  by_cases h1 : X ∈ intOff b (insert v S)
  · by_cases h2 : projV v (projFin X) ∈ latV b v
    · rw [Set.indicator_of_mem h1, Set.indicator_of_mem (hmem.2 ⟨h1, h2⟩), Finset.prod_insert hv,
        Function.update_self, hprod, Set.indicator_of_mem h2]
      simp
    · rw [Set.indicator_of_mem h1, Set.indicator_of_notMem (fun h => h2 (hmem.1 h).2),
        Finset.prod_insert hv, Function.update_self, Set.indicator_of_notMem h2]
      simp
  · rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem (fun h => h1 (hmem.1 h).1)]

theorem exists_isEulerProd : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n : ℕ), n = 0 ∨ n + 2 ≤ M → ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf laminf → (∀ v, IsStdV v (lam v)) → ∀ (minf : HermR (Ainf F) σ n → Measure (Fin n → Fin M → Ainf F ⊗[F] E)), IsGramFib (Ainf F) σ J n (coordW (Ainf F) b laminf n M) (coordHerm (Ainf F) σ b laminf n) minf → ∀ (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ n → Measure (Fin n → Fin M → Fv F v ⊗[F] E)), (∀ v, IsGramFib (Fv F v) σ J n (coordW (Fv F v) b (lam v) n M) (coordHerm (Fv F v) σ b (lam v) n) (m v)) → ∀ I : Measure (Fin n → Fin M → AF F ⊗[F] E), IsLocallyFiniteMeasure I → (∀ h : HA (AF F) σ J, I.map (actW (AF F) σ J h) = I) → I {X | gramR (AF F) σ J X = T.map (inclR (AF F))}ᶜ = 0 → ∃ c : ℝ≥0, IsEulerProd b I c (minf (hermOf (Ainf F) σ T hT)) (fun v => m v (hermOf (Fv F v) σ T hT)) := by
  intro F E _ _ _ _ _ σ hCM M J hJ n hn T hT hdet d b laminf lam hinf hlam minf hminf m hm I hIf hIinv hIsupp
  classical
  have hLi : IsLocR (Ainf F) := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hCM.1
  have hLv : ∀ v, IsLocR (Fv F v) := GlobalTheory.T.completion_is_local_ring F
  haveI hBi : BorelSpace (Ainf F) := ⟨rfl⟩
  have hFi := fib_facts σ hCM J hJ (Ainf F) hLi T hT hdet b laminf hinf.1 minf hminf
  have hFv : ∀ v, SigmaFinite (m v (hermOf (Fv F v) σ T hT)) ∧
      (m v (hermOf (Fv F v) σ T hT) = 0 →
        ∀ X, gramR (Fv F v) σ J X ≠ T.map (inclR (Fv F v))) := fun v => by
    haveI : BorelSpace (Fv F v) := ⟨rfl⟩
    exact fib_facts σ hCM J hJ (Fv F v) (hLv v) T hT hdet b (lam v) (hlam v).1 (m v) (hm v)
  obtain ⟨hfin, hsum⟩ := GlobalTheory.T.euler_product_local_densities_converges F E σ hCM M J hJ n hn T hT hdet d b lam hlam m hm
  by_cases h0 : minf (hermOf (Ainf F) σ T hT) = 0 ∨ ∃ v, m v (hermOf (Fv F v) σ T hT) = 0
  · have hempty : {X | gramR (AF F) σ J X = T.map (inclR (AF F))} = ∅ := by
      ext X
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hX
      have hloc := (GlobalTheory.T.gram_matrix_local_global F E σ hCM M J hJ n X T).1.1 hX
      rcases h0 with h | ⟨v, h⟩
      · exact hFi.2 h _ hloc.1
      · exact (hFv v).2 h _ (hloc.2 v)
    rw [hempty, Set.compl_empty] at hIsupp
    rw [Measure.measure_univ_eq_zero.mp hIsupp]
    exact ⟨0, (GlobalTheory.T.euler_product_measure_zero F E σ hCM d b n M 0 0 _ _).2.2 hfin hsum h0⟩
  · push Not at h0
    obtain ⟨hinf0, hv0⟩ := h0
    choose c hc using GlobalTheory.T.siegel_weil_orbital_measure F E σ hCM M J hJ n T hT hdet d b laminf lam hinf hlam minf hminf m hm
      I hIf hIinv hIsupp
    obtain ⟨A, hAm, hA0, hAt⟩ := @exists_test_set _ _ (minf (hermOf (Ainf F) σ T hT)) hFi.1 hinf0
    choose B hBm hB0 hBt using fun v =>
      @exists_test_set _ _ (m v (hermOf (Fv F v) σ T hT)) (hFv v).1 (hv0 v)
    have hstep : ∀ S : Finset (HeightOneSpectrum (𝓞 F)), ∅ ⊆ S → ∀ v, v ∉ S →
        (c S : ℝ) = c (insert v S) * (m v (hermOf (Fv F v) σ T hT) (latV b v)).toReal := by
      intro S _ v hv
      have hlatm : MeasurableSet (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) := by
        haveI := borel_tup σ hCM (Fv F v) (hLv v) n M
        exact ((GlobalTheory.T.adelic_tuple_projections F E σ hCM d b n M).2.2.2.1 v).2.measurableSet
      let φ0 : ∀ w : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F w ⊗[F] E) → ℝ≥0∞ :=
        fun w => (B w).indicator 1
      let φ1 := Function.update φ0 v ((latV b v).indicator 1)
      have hφ0 : ∀ w, Measurable (φ0 w) := fun w => measurable_one.indicator (hBm w)
      have hφ1 : ∀ w, Measurable (φ1 w) := by
        intro w
        by_cases hw : w = v
        · subst hw
          simpa [φ1] using measurable_one.indicator hlatm
        · simpa [φ1, Function.update_of_ne hw] using hφ0 w
      have hAφ : Measurable (A.indicator (1 : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞)) := measurable_one.indicator hAm
      have e1 := hc S _ φ0 hAφ hφ0
      have e2 := hc (insert v S) _ φ1 hAφ hφ1
      have e3 : ∫⁻ X, pureL b (insert v S) (A.indicator 1) φ1 X ∂I =
          ∫⁻ X, pureL b S (A.indicator 1) φ0 X ∂I :=
        lintegral_congr fun X => pureL_insert b S v hv _ φ0 X
      rw [e3, e1, Finset.prod_insert hv] at e2
      have hp : ∏ w ∈ S, ∫⁻ X, φ1 w X ∂(m w (hermOf (Fv F w) σ T hT)) =
          ∏ w ∈ S, ∫⁻ X, φ0 w X ∂(m w (hermOf (Fv F w) σ T hT)) :=
        Finset.prod_congr rfl fun w hw => by
          have hne : w ≠ v := fun h => hv (h ▸ hw)
          simp only [φ1, Function.update_of_ne hne]
      have hL : ∫⁻ X, φ1 v X ∂(m v (hermOf (Fv F v) σ T hT)) =
          m v (hermOf (Fv F v) σ T hT) (latV b v) := by
        simp only [φ1, Function.update_self]
        exact lintegral_indicator_one hlatm
      have hB : ∀ w, ∫⁻ X, φ0 w X ∂(m w (hermOf (Fv F w) σ T hT)) =
          m w (hermOf (Fv F w) σ T hT) (B w) := fun w => lintegral_indicator_one (hBm w)
      have hA : ∫⁻ X, A.indicator (1 : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞) X ∂(minf (hermOf (Ainf F) σ T hT)) =
          minf (hermOf (Ainf F) σ T hT) A := lintegral_indicator_one hAm
      rw [hp, hL, hA] at e2
      simp only [hB] at e2
      set Q := ∏ w ∈ S, m w (hermOf (Fv F w) σ T hT) (B w) with hQ
      set a := minf (hermOf (Ainf F) σ T hT) A with ha
      set L := m v (hermOf (Fv F v) σ T hT) (latV b v) with hLdef
      have hQ0 : Q ≠ 0 := Finset.prod_ne_zero_iff.mpr fun w _ => hB0 w
      have hQt : Q ≠ ⊤ := ENNReal.prod_ne_top fun w _ => hBt w
      have hP0 : a * Q ≠ 0 := mul_ne_zero hA0 hQ0
      have hPt : a * Q ≠ ⊤ := ENNReal.mul_ne_top hAt hQt
      have e4 : (c S : ℝ≥0∞) * (a * Q) = ((c (insert v S) : ℝ≥0∞) * L) * (a * Q) := by
        rw [e2]; ring
      have e5 := (ENNReal.mul_left_inj hP0 hPt).mp e4
      have e6 := congrArg ENNReal.toReal e5
      simpa [ENNReal.toReal_mul] using e6
    obtain ⟨c₀, S₀, -, hS₀⟩ := GlobalTheory.T.infinite_product_renormalization _ (fun v => (m v (hermOf (Fv F v) σ T hT) (latV b v)).toReal) c ∅
      (fun _ => ENNReal.toReal_nonneg) hsum hstep
    refine ⟨c₀, hfin, hsum, S₀, fun S hS φinf φ hφi hφ => ?_⟩
    rw [hc S φinf φ hφi hφ]
    have hcS : (c S : ℝ≥0∞) = (c₀ : ℝ≥0∞) *
        ENNReal.ofReal (∏' v : {v // v ∉ S}, (m v.1 (hermOf (Fv F v.1) σ T hT) (latV b v.1)).toReal) := by
      rw [← ENNReal.ofReal_coe_nnreal (p := c S), (hS₀ S hS).2, ENNReal.ofReal_mul (NNReal.coe_nonneg _),
        ENNReal.ofReal_coe_nnreal]
    rw [hcS]
    ring

end GlobalTheory.CompanionTheory.SW.Fact
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilFormulaRangeStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isEulerProd_of_invariant_of_fiber_supported : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n : ℕ), n = 0 ∨ n + 2 ≤ M → ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf laminf → (∀ v, IsStdV v (lam v)) → ∀ (minf : HermR (Ainf F) σ n → Measure (Fin n → Fin M → Ainf F ⊗[F] E)), IsGramFib (Ainf F) σ J n (coordW (Ainf F) b laminf n M) (coordHerm (Ainf F) σ b laminf n) minf → ∀ (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ n → Measure (Fin n → Fin M → Fv F v ⊗[F] E)), (∀ v, IsGramFib (Fv F v) σ J n (coordW (Fv F v) b (lam v) n M) (coordHerm (Fv F v) σ b (lam v) n) (m v)) → ∀ I : Measure (Fin n → Fin M → AF F ⊗[F] E), IsLocallyFiniteMeasure I → (∀ h : HA (AF F) σ J, I.map (actW (AF F) σ J h) = I) → I {X | gramR (AF F) σ J X = T.map (inclR (AF F))}ᶜ = 0 → ∃ c : ℝ≥0, IsEulerProd b I c (minf (hermOf (Ainf F) σ T hT)) (fun v => m v (hermOf (Fv F v) σ T hT)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.Fact.exists_isEulerProd | exact GlobalTheory.CompanionTheory.SW.Fact.exists_isEulerProd | (intros; apply GlobalTheory.CompanionTheory.SW.Fact.exists_isEulerProd <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsUnitScalingSelfdualAdelicMeasures
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsUnitScalingSelfdualAdelicMeasures
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.SdTuples

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

section Coord

variable {F E : Type} [Field F] [Field E] [Algebra F E]
  (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
  {d : ℕ} (b : Module.Basis (Fin d) F E)

def cf (y : R ⊗[F] E) (k : Fin d) : R := (Algebra.TensorProduct.basis R b).repr y k

variable {R b}

def tupE (hc : IsHomeomorph (cf (F := F) (E := E) R b)) (n M : ℕ) :
    (Fin n → Fin M → R ⊗[F] E) ≃ₜ+ ((Fin M × Fin d) × Fin n → R) where
  toFun X p := cf R b (X p.2 p.1.1) p.1.2
  invFun Y a i := hc.homeomorph.symm (fun k => Y ((i, k), a))
  left_inv X := by
    funext a i
    exact hc.homeomorph.symm_apply_apply (X a i)
  right_inv Y := by
    funext p
    obtain ⟨⟨i, k⟩, a⟩ := p
    exact congrFun (hc.homeomorph.apply_symm_apply (fun k => Y ((i, k), a))) k
  map_add' X Y := by
    funext p
    simp [cf]
  continuous_toFun := by
    refine continuous_pi fun p => ?_
    exact (continuous_apply p.1.2).comp (hc.continuous.comp
      ((continuous_apply p.1.1).comp (continuous_apply p.2)))
  continuous_invFun := by
    refine continuous_pi fun a => continuous_pi fun i => ?_
    exact hc.homeomorph.symm.continuous.comp
      (continuous_pi fun k => continuous_apply ((i, k), a))

end Coord

section Meas

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {R : Type} [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R]
  {d : ℕ} {b : Module.Basis (Fin d) F E}


omit [NumberField F] [NumberField E] [IsTopologicalRing R] [LocallyCompactSpace R] [T2Space R] in
theorem coordK_preimage (hc : IsHomeomorph (cf (F := F) (E := E) R b)) (lam : Measure R)
    (T : Set (Fin d → R)) :
    coordK R b lam (cf R b ⁻¹' T) = Measure.pi (fun _ => lam) T := by
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  have he : MeasurableEmbedding (cf (F := F) (E := E) R b) := hc.homeomorph.measurableEmbedding
  have := he.comap_apply (Measure.pi fun _ : Fin d => lam) (cf R b ⁻¹' T)
  rw [Set.image_preimage_eq _ hc.surjective] at this
  exact this

theorem map_coordW (hCM : IsCMExt F E σ) (hc : IsHomeomorph (cf (F := F) (E := E) R b))
    (lam : Measure R) (hlam : lam.IsAddHaarMeasure) (n M : ℕ) :
    (coordW R b lam n M).map (tupE hc n M) = Measure.pi fun _ : (Fin M × Fin d) × Fin n => lam := by
  obtain ⟨h1, h2, h3, h4, -, -, -, hB, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM R
  haveI := h1; haveI := h2; haveI := h3; haveI := h4
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  haveI := hB n M
  haveI := (GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hCM R d b lam hlam).1
  have hm : Measurable (tupE hc n M) := (map_continuous (tupE hc n M)).measurable
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have hpre : (tupE hc n M) ⁻¹' Set.univ.pi s = Set.univ.pi fun a : Fin n => Set.univ.pi fun i : Fin M =>
      cf R b ⁻¹' (Set.univ.pi fun k : Fin d => s ((i, k), a)) := by
    ext X
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, Prod.forall]
    exact ⟨fun h a i k => h i k a, fun h i k a => h a i k⟩
  rw [hpre]
  unfold coordW
  rw [Measure.pi_pi]
  simp_rw [Measure.pi_pi, coordK_preimage hc, Measure.pi_pi]
  rw [Fintype.prod_prod_type_right]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [Fintype.prod_prod_type]


omit [NumberField F] [NumberField E] [IsTopologicalRing R] [LocallyCompactSpace R]
  [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R] in
theorem BR_eq (hc : IsHomeomorph (cf (F := F) (E := E) R b)) {M n : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (B : Matrix (Fin M × Fin d) (Fin M × Fin d) F)
    (hB : ∀ x y : Fin M → R ⊗[F] E, Algebra.trace R (R ⊗[F] E) (hR R σ J x y) =
      (fun p : Fin M × Fin d => (Algebra.TensorProduct.basis R b).repr (x p.1) p.2) ⬝ᵥ
        (B.map (algebraMap F R) *ᵥ fun p : Fin M × Fin d =>
          (Algebra.TensorProduct.basis R b).repr (y p.1) p.2))
    (X Y : Fin n → Fin M → R ⊗[F] E) :
    BR R σ J X Y = tupE hc n M X ⬝ᵥ
      ((Matrix.blockDiagonal fun _ : Fin n => B).map (algebraMap F R) *ᵥ tupE hc n M Y) := by
  rw [Matrix.blockDiagonal_map _ _ (map_zero _)]
  unfold BR
  simp_rw [hB]
  simp only [dotProduct, Matrix.mulVec, Fintype.sum_prod_type_right (f := fun p : (Fin M × Fin d) × Fin n => _)]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun p _ => ?_
  have hs : ∑ c : Fin n, ∑ q : Fin M × Fin d,
      Matrix.blockDiagonal (fun _ : Fin n => B.map (algebraMap F R)) (p, a) (q, c) *
        tupE hc n M Y (q, c) =
      ∑ q : Fin M × Fin d, B.map (algebraMap F R) p q *
        (Algebra.TensorProduct.basis R b).repr (Y a q.1) q.2 := by
    rw [Finset.sum_eq_single a]
    · refine Finset.sum_congr rfl fun q _ => ?_
      rw [Matrix.blockDiagonal_apply_eq]
      rfl
    · intro c _ hca
      refine Finset.sum_eq_zero fun q _ => ?_
      rw [Matrix.blockDiagonal_apply_ne _ _ _ (Ne.symm hca), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ a) h
  rw [hs]
  rfl

theorem sdW_iff (hCM : IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (B : Matrix (Fin M × Fin d) (Fin M × Fin d) F)
    (hB : ∀ x y : Fin M → R ⊗[F] E, Algebra.trace R (R ⊗[F] E) (hR R σ J x y) =
      (fun p : Fin M × Fin d => (Algebra.TensorProduct.basis R b).repr (x p.1) p.2) ⬝ᵥ
        (B.map (algebraMap F R) *ᵥ fun p : Fin M × Fin d =>
          (Algebra.TensorProduct.basis R b).repr (y p.1) p.2))
    (lam : Measure R) (hlam : lam.IsAddHaarMeasure) (ψR : R → ℂ) (n : ℕ) (cc : ℝ≥0)
    (hmain : ∀ μ : Measure ((Fin M × Fin d) × Fin n → R),
      SelfDual μ (fun x y => ψR (x ⬝ᵥ
        ((Matrix.blockDiagonal fun _ : Fin n => B).map (algebraMap F R) *ᵥ y))) ↔
        μ = cc • Measure.pi fun _ => lam)
    (μ : Measure (Fin n → Fin M → R ⊗[F] E)) :
    SdW F E σ M J R ψR n μ ↔ μ = cc • coordW R b lam n M := by
  obtain ⟨h1, h2, h3, h4, -, -, hcc, hBor, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM R
  haveI := h1
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  haveI := hBor n M
  have hc : IsHomeomorph (cf (F := F) (E := E) R b) := hcc d b
  set e := tupE hc n M with he
  have hm : Measurable e := (map_continuous e).measurable
  have hm' : Measurable e.symm := (map_continuous e.symm).measurable
  have inj : ∀ ν : Measure (Fin n → Fin M → R ⊗[F] E), (ν.map e).map e.symm = ν := by
    intro ν
    rw [Measure.map_map hm' hm]
    have : (e.symm ∘ e) = id := by funext X; exact e.symm_apply_apply X
    rw [this, Measure.map_id]
  have key := GlobalTheory.T.selfdual_measure_transport_equiv _ _ e μ (fun x y => ψR (x ⬝ᵥ
        ((Matrix.blockDiagonal fun _ : Fin n => B).map (algebraMap F R) *ᵥ y)))
  have hform : SdW F E σ M J R ψR n μ ↔ SelfDual μ (fun X Y => ψR (e X ⬝ᵥ
        ((Matrix.blockDiagonal fun _ : Fin n => B).map (algebraMap F R) *ᵥ e Y))) := by
    unfold SdW
    have : (fun X Y => ψR (BR R σ J X Y)) = (fun X Y : Fin n → Fin M → R ⊗[F] E => ψR (e X ⬝ᵥ
        ((Matrix.blockDiagonal fun _ : Fin n => B).map (algebraMap F R) *ᵥ e Y))) := by
      funext X Y
      rw [BR_eq hc J B hB X Y]
    rw [this]
  rw [hform, key, hmain]
  constructor
  · intro h
    rw [← inj μ, h, ← map_coordW hCM hc lam hlam n M, ← Measure.map_smul, inj]
    exact hm.aemeasurable
  · intro h
    rw [h, Measure.map_smul, map_coordW hCM hc lam hlam n M]
    exact hm.aemeasurable

end Meas

theorem sdW_coord : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf laminf → (∀ v, IsStdV v (lam v)) → ∀ ψ, IsCharAF F ψ → ∀ n : ℕ, ∃ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c ∧ (∀ μ, SdW F E σ M J (Ainf F) (psiInf F ψ) n μ ↔ μ = cinf • coordW (Ainf F) b laminf n M) ∧ ∀ v : HeightOneSpectrum (𝓞 F), (∀ μ, SdW F E σ M J (Fv F v) (psiV F ψ v) n μ ↔ μ = c v • coordW (Fv F v) b (lam v) n M) := by
  intro F E _ _ _ _ _ σ hCM M J hJ d b laminf lam hinf hv ψ hψ n
  obtain ⟨B, hsym, hdet, -, hR'⟩ := GlobalTheory.CompanionTheory.SW.TraceCoord.exists_trace_coord F E σ hCM M J hJ d b
  have hsym' : (Matrix.blockDiagonal fun _ : Fin n => B).IsSymm := by
    unfold Matrix.IsSymm
    rw [Matrix.blockDiagonal_transpose]
    simp only [hsym.eq]
  have hdet' : (Matrix.blockDiagonal fun _ : Fin n => B).det ≠ 0 := by
    rw [Matrix.det_blockDiagonal]
    exact Finset.prod_ne_zero_iff.mpr fun _ _ => hdet
  obtain ⟨cinf, c, hU, h1, h2⟩ := GlobalTheory.T.exists_unipotentInvariant_compactlySupported_weight F hCM.1 laminf lam hinf hv ψ hψ
    ((Fin M × Fin d) × Fin n) (Matrix.blockDiagonal fun _ : Fin n => B) hsym' hdet'
  refine ⟨cinf, c, hU, ?_, fun v => ?_⟩
  · obtain ⟨t1, t2, t3, t4, -⟩ := GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hCM.1
    haveI := t1; haveI := t2; haveI := t3; haveI := t4
    haveI : BorelSpace (Ainf F) := ⟨rfl⟩
    exact fun μ => sdW_iff hCM J B (hR' (Ainf F)).1 laminf hinf.1 (psiInf F ψ) n cinf h1 μ
  · obtain ⟨t1, t2, t3, t4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
    haveI := t1; haveI := t2; haveI := t3; haveI := t4
    haveI : BorelSpace (Fv F v) := ⟨rfl⟩
    exact fun μ => sdW_iff hCM J B (hR' (Fv F v)).1 (lam v) (hv v).1 (psiV F ψ v) n (c v) (h2 v) μ

end GlobalTheory.CompanionTheory.SW.SdTuples
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsUnitScalingSelfdualAdelicMeasuresStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_scaling_selfdual_adelic_measures : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf laminf → (∀ v, IsStdV v (lam v)) → ∀ ψ, IsCharAF F ψ → ∀ n : ℕ, ∃ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c ∧ (∀ μ, SdW F E σ M J (Ainf F) (psiInf F ψ) n μ ↔ μ = cinf • coordW (Ainf F) b laminf n M) ∧ ∀ v : HeightOneSpectrum (𝓞 F), (∀ μ, SdW F E σ M J (Fv F v) (psiV F ψ v) n μ ↔ μ = c v • coordW (Fv F v) b (lam v) n M) := by
  first | exact @GlobalTheory.CompanionTheory.SW.SdTuples.sdW_coord | exact GlobalTheory.CompanionTheory.SW.SdTuples.sdW_coord | (intros; apply GlobalTheory.CompanionTheory.SW.SdTuples.sdW_coord <;> assumption)
end
end
