module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsGramFiberMeasures
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RankOneLocalDensityAlmostAll
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalDensitiesCongruentTargetAlmostAll
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalDensityBlockOneProductStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LatticeGramScalarAlmostAll

@[expose] public section

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalDensitiesBlockOneAlmostAll
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalDensitiesBlockOneAlmostAll
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.GoodStep

theorem blockOne_zero_zero {K : Type} [Zero K] {M : ℕ} (t : K) (A : Matrix (Fin M) (Fin M) K) :
    blockOne t A 0 0 = t := rfl

theorem blockOne_zero_succ {K : Type} [Zero K] {M : ℕ} (t : K) (A : Matrix (Fin M) (Fin M) K) (j : Fin M) :
    blockOne t A 0 j.succ = 0 := rfl

theorem blockOne_succ_zero {K : Type} [Zero K] {M : ℕ} (t : K) (A : Matrix (Fin M) (Fin M) K) (i : Fin M) :
    blockOne t A i.succ 0 = 0 := rfl

theorem blockOne_succ_succ {K : Type} [Zero K] {M : ℕ} (t : K) (A : Matrix (Fin M) (Fin M) K) (i j : Fin M) :
    blockOne t A i.succ j.succ = A i j := rfl

theorem det_blockOne {K : Type} [CommRing K] {M : ℕ} (t : K) (A : Matrix (Fin M) (Fin M) K) :
    (blockOne t A).det = t * A.det := by
  have hs : (blockOne t A).submatrix Fin.succ (Fin.succAbove 0) = A := by
    ext i j
    simp [blockOne_succ_succ]
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ, hs]
  simp [blockOne_zero_zero, blockOne_zero_succ]

theorem isHermND_blockOne {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (t : F) (ht : t ≠ 0) :
    IsHermND σ (blockOne (algebraMap F E t) J) := by
  refine ⟨fun i j => ?_, ?_⟩
  · refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simp [blockOne_zero_zero]
    · simp [blockOne_zero_succ, blockOne_succ_zero]
    · simp [blockOne_zero_succ, blockOne_succ_zero]
    · simpa [blockOne_succ_succ] using hJ.1 i j
  · rw [det_blockOne]
    exact mul_ne_zero (by simpa using ht) hJ.2

theorem gram_mulVec_e0 {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (t : F) :
    gramR R σ (blockOne (algebraMap F E t) J)
        (fun _ : Fin 1 => (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → R ⊗[F] E)) =
      (hermScal R σ (algebraMap F R t) : HermR R σ 1) := by
  ext a c
  show hR R σ _ _ _ = algebraMap F R t ⊗ₜ[F] (1 : E)
  simp only [hR, hform, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, map_one, map_zero, one_mul,
    mul_zero, zero_mul, mul_one, Finset.sum_const_zero, add_zero, JR, Matrix.map_apply,
    blockOne_zero_zero]
  show (1 : R) ⊗ₜ[F] (algebraMap F E t) = _
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
    TensorProduct.smul_tmul']

section Place

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem consTup_mem_latV {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (h1 : ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr (1 : Fv F v ⊗[F] E) k ∈
      v.adicCompletionIntegers F) {n M : ℕ} (X : Fin n → Fin M → Fv F v ⊗[F] E) :
    consTup X ∈ latV b v ↔ X ∈ latV b v := by
  constructor
  · intro h a i k
    exact h a.succ i.succ k
  · intro h a i k
    refine Fin.cases ?_ (fun a => ?_) a <;> refine Fin.cases ?_ (fun i => ?_) i
    · exact h1 k
    · show (Algebra.TensorProduct.basis (Fv F v) b).repr (0 : Fv F v ⊗[F] E) k ∈ _
      simp [zero_mem]
    · show (Algebra.TensorProduct.basis (Fv F v) b).repr (0 : Fv F v ⊗[F] E) k ∈ _
      simp [zero_mem]
    · exact h a i k

theorem e0_mem_latV {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (h1 : ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr (1 : Fv F v ⊗[F] E) k ∈
      v.adicCompletionIntegers F) {M : ℕ} :
    (fun _ : Fin 1 => (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → Fv F v ⊗[F] E)) ∈ latV b v := by
  intro a i k
  refine Fin.cases ?_ (fun i => ?_) i
  · exact h1 k
  · show (Algebra.TensorProduct.basis (Fv F v) b).repr (0 : Fv F v ⊗[F] E) k ∈ _
    simp [zero_mem]

theorem incl_mul_eq_smul (R : Type) [CommRing R] [Algebra F R] (t : F) (y : R ⊗[F] E) :
    inclR R (algebraMap F E t) * y = algebraMap F R t • y := by
  have : inclR R (algebraMap F E t) = algebraMap F R t • (1 : R ⊗[F] E) := by
    show (1 : R) ⊗ₜ[F] (algebraMap F E t) = _
    rw [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    simp
  rw [this, smul_mul_assoc, one_mul]

theorem coordK_map_unit [NumberField E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ)
    (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)) (hlam : IsStdV v lam) (t : F) (ht : t ≠ 0)
    (htv : Valued.v (algebraMap F (Fv F v) t) = 1) (d : ℕ) (b : Module.Basis (Fin d) F E) :
    (coordK (Fv F v) b lam).map (fun y => inclR (Fv F v) (algebraMap F E t) * y) =
      (1 : ℝ≥0) • coordK (Fv F v) b lam := by
  obtain ⟨r1, r2, r3, r4, -⟩ := GlobalTheory.T.completion_is_local_ring F v
  haveI := r1
  haveI := r2
  haveI := r3
  haveI := r4
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨i1, i2, i3, i4, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (Fv F v)
  haveI := i1
  haveI := i2
  haveI := i3
  haveI := i4
  haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI := hlam.1
  haveI := (GlobalTheory.T.coordinate_haar_measure F E σ hCM (Fv F v) d b lam hlam.1).1
  have hinv : inclR (F := F) (Fv F v) (algebraMap F E t) * inclR (F := F) (Fv F v) (algebraMap F E t⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ ht, map_one, map_one]
  let e : (Fv F v ⊗[F] E) ≃+ (Fv F v ⊗[F] E) :=
    { toFun := fun y => inclR (F := F) (Fv F v) (algebraMap F E t) * y
      invFun := fun y => inclR (F := F) (Fv F v) (algebraMap F E t⁻¹) * y
      left_inv := fun y => by
        show _ * (_ * y) = y
        rw [← mul_assoc, mul_comm (inclR (F := F) (Fv F v) (algebraMap F E t⁻¹)), hinv, one_mul]
      right_inv := fun y => by
        show _ * (_ * y) = y
        rw [← mul_assoc, hinv, one_mul]
      map_add' := fun x y => mul_add _ x y }
  have he : Continuous e := continuous_const.mul continuous_id
  have he' : Continuous e.symm := continuous_const.mul continuous_id
  let L : Set (Fv F v ⊗[F] E) := {y | ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈
    v.adicCompletionIntegers F}
  obtain ⟨c1, c2, c3, -⟩ := GlobalTheory.T.local_lattice_compact_open_unit_volume F E σ hCM d b 1 1 v
  have hLc : IsCompact L := by
    have : L = (fun X : Fin 1 → Fin 1 → Fv F v ⊗[F] E => X 0 0) '' latV b v := by
      ext y
      constructor
      · intro hy
        exact ⟨fun _ _ => y, fun _ _ k => hy k, rfl⟩
      · rintro ⟨X, hX, rfl⟩
        exact fun k => hX 0 0 k
    rw [this]
    exact c1.image (by fun_prop)
  have hLo : IsOpen L := by
    have : L = (fun (y : Fv F v ⊗[F] E) (_ : Fin 1) (_ : Fin 1) => y) ⁻¹' latV b v := by
      ext y
      exact ⟨fun hy _ _ k => hy k, fun hy k => hy 0 0 k⟩
    rw [this]
    exact c2.preimage (by fun_prop)
  have hL0 : L.Nonempty := ⟨0, fun k => c3 0 0 k⟩
  have hmem : ∀ x : Fv F v, algebraMap F (Fv F v) t * x ∈ v.adicCompletionIntegers F ↔
      x ∈ v.adicCompletionIntegers F := by
    intro x
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.mem_adicCompletionIntegers,
      map_mul, htv, one_mul]
  have hL : ∀ y, e y ∈ L ↔ y ∈ L := by
    intro y
    have hk : ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr (e y) k =
        algebraMap F (Fv F v) t * (Algebra.TensorProduct.basis (Fv F v) b).repr y k := by
      intro k
      show (Algebra.TensorProduct.basis (Fv F v) b).repr (inclR (F := F) (Fv F v) (algebraMap F E t) * y) k = _
      rw [incl_mul_eq_smul, map_smul, Finsupp.smul_apply, smul_eq_mul]
    constructor
    · intro h k
      exact (hmem _).1 (hk k ▸ h k)
    · intro h k
      exact hk k ▸ (hmem _).2 (h k)
  have := (GlobalTheory.T.map_addHaar_addEquiv_eq_smul_and_eq_of_compact_open _ _ (coordK (Fv F v) b lam) (coordK (Fv F v) b lam) e he he').2 L L hLc hLo hL0 hL rfl
  rw [one_smul]
  exact this

end Place

theorem blockFibre_mass : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (t : F), t ≠ 0 → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 → ∀ (hT' : ∀ a b, σ (blockOne (algebraMap F E t) T b a) = blockOne (algebraMap F E t) T a b), ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ lam, IsStdV v lam → ∀ m m₁ m', IsGramFib (Fv F v) σ (blockOne (algebraMap F E t) J) (n + 1) (coordW (Fv F v) b lam (n + 1) (M + 1)) (coordHerm (Fv F v) σ b lam (n + 1)) m → IsGramFib (Fv F v) σ (blockOne (algebraMap F E t) J) 1 (coordW (Fv F v) b lam 1 (M + 1)) (coordHerm (Fv F v) σ b lam 1) m₁ → IsGramFib (Fv F v) σ J n (coordW (Fv F v) b lam n M) (coordHerm (Fv F v) σ b lam n) m' → m (hermOf (Fv F v) σ _ hT') (latV b v) = m₁ (hermScal (Fv F v) σ (algebraMap F _ t)) (latV b v) * m' (hermOf (Fv F v) σ T hT) (latV b v) := by
  intro F E _ _ _ _ _ σ hCM M J hJ t ht n T hT hdet hT' d b
  have hJ' := isHermND_blockOne σ J hJ t ht
  filter_upwards [GlobalTheory.T.lattice_gram_scalar_almost_all F E σ hCM (M + 1) _ hJ' t ht d b,
    (GlobalTheory.T.integral_almost_all_places F E σ hCM d b).1 1, (GlobalTheory.T.integral_almost_all_places F E σ hCM d b).2 t ht] with v hgt h1' htv
  intro lam hlam m m₁ m' hm hm₁ hm'
  have h1 : ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr (1 : Fv F v ⊗[F] E) k ∈
      v.adicCompletionIntegers F := by
    intro k
    simpa using h1' k
  have hlocR := GlobalTheory.T.completion_is_local_ring F v
  obtain ⟨r1, r2, r3, r4, -⟩ := id hlocR
  haveI := r1
  haveI := r2
  haveI := r3
  haveI := r4
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨-, -, -, -, -, -, -, hB, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (Fv F v)
  have hmeas : ∀ p q : ℕ, MeasurableSet (latV (M := q) (n := p) b v) := by
    intro p q
    haveI := hB p q
    exact (GlobalTheory.T.local_lattice_compact_open_unit_volume F E σ hCM d b p q v).2.1.measurableSet
  have hc := coordK_map_unit σ hCM v lam hlam t ht htv d b
  let φ : (Fin (n + 1) → Fin (M + 1) → Fv F v ⊗[F] E) → ℝ≥0∞ := (latV b v).indicator 1
  have hφ : Measurable φ := measurable_one.indicator (hmeas _ _)
  obtain ⟨Ψ, -, hΨ, hint⟩ := GlobalTheory.T.local_density_block_one_product F E σ hCM M J hJ t ht n T hT hdet hT' (Fv F v) hlocR d b lam
    hlam.1 m m₁ m' hm hm₁ hm' 1 hc φ hφ
  have hae : Ψ =ᵐ[m₁ (hermScal (Fv F v) σ (algebraMap F _ t))]
      (latV b v).indicator (fun _ => m' (hermOf (Fv F v) σ T hT) (latV b v)) := by
    filter_upwards [mem_ae_iff.2 (hm₁.1 (hermScal (Fv F v) σ (algebraMap F _ t)))] with y hy
    have hg : gramR (Fv F v) σ (blockOne (algebraMap F E t) J) y =
        (hermScal (Fv F v) σ (algebraMap F _ t) : HermR (Fv F v) σ 1) := hy.1
    have hu : IsUnit (gramR (Fv F v) σ (blockOne (algebraMap F E t) J) y).det := hy.2
    have hg0 := gram_mulVec_e0 (Fv F v) σ J t
    by_cases hyL : y ∈ latV b v
    · obtain ⟨h, hh, hpres⟩ := hgt _ y (e0_mem_latV b v h1) hyL hg0 (hg.trans hg0.symm)
      rw [Set.indicator_of_mem hyL, ← hh, hΨ h]
      have : (fun X => φ (actW (Fv F v) σ _ h (consTup X))) = (latV b v).indicator 1 := by
        funext X
        by_cases hX : X ∈ latV b v
        · rw [Set.indicator_of_mem hX]
          exact Set.indicator_of_mem ((hpres _ _).2 ((consTup_mem_latV b v h1 X).2 hX)) _
        · rw [Set.indicator_of_notMem hX]
          exact Set.indicator_of_notMem (fun hc' => hX ((consTup_mem_latV b v h1 X).1 ((hpres _ _).1 hc'))) _
      rw [this, lintegral_indicator_one (hmeas _ _)]
    · obtain ⟨h, hh⟩ := GlobalTheory.T.witt_extension_artinian_ring F E σ hCM (M + 1) _ hJ' (Fv F v) 1 _ y (hg0.trans hg.symm)
        (by rw [hg0, ← hg]; exact hu)
      rw [Set.indicator_of_notMem hyL, ← hh, hΨ h]
      have : (fun X => φ (actW (Fv F v) σ _ h (consTup X))) = 0 := by
        funext X
        refine Set.indicator_of_notMem (fun hc' => hyL ?_) _
        intro a i k
        have ha : a = 0 := Subsingleton.elim _ _
        subst ha
        rw [← hh]
        exact hc' 0 i k
      rw [this, lintegral_zero_fun]
  have e1 : ∫⁻ X, φ X ∂(m (hermOf (Fv F v) σ _ hT')) = m (hermOf (Fv F v) σ _ hT') (latV b v) :=
    lintegral_indicator_one (hmeas _ _)
  rw [← e1, hint, lintegral_congr_ae hae, lintegral_indicator_const (hmeas _ _)]
  simp [mul_comm]

end GlobalTheory.CompanionTheory.SW.GoodStep
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalDensitiesBlockOneAlmostAllStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_densities_block_one_almost_all : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (t : F), t ≠ 0 → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 → ∀ (hT' : ∀ a b, σ (blockOne (algebraMap F E t) T b a) = blockOne (algebraMap F E t) T a b), ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ lam, IsStdV v lam → ∀ m m₁ m', IsGramFib (Fv F v) σ (blockOne (algebraMap F E t) J) (n + 1) (coordW (Fv F v) b lam (n + 1) (M + 1)) (coordHerm (Fv F v) σ b lam (n + 1)) m → IsGramFib (Fv F v) σ (blockOne (algebraMap F E t) J) 1 (coordW (Fv F v) b lam 1 (M + 1)) (coordHerm (Fv F v) σ b lam 1) m₁ → IsGramFib (Fv F v) σ J n (coordW (Fv F v) b lam n M) (coordHerm (Fv F v) σ b lam n) m' → m (hermOf (Fv F v) σ _ hT') (latV b v) = m₁ (hermScal (Fv F v) σ (algebraMap F _ t)) (latV b v) * m' (hermOf (Fv F v) σ T hT) (latV b v) := by
  first | exact @GlobalTheory.CompanionTheory.SW.GoodStep.blockFibre_mass | exact GlobalTheory.CompanionTheory.SW.GoodStep.blockFibre_mass | (intros; apply GlobalTheory.CompanionTheory.SW.GoodStep.blockFibre_mass <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalGramFiberMeasuresAgreeAlmostAll
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianFormsIntegrallyEquivalentAlmostAll
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianFormsIntegrallyEquivalentAlmostAll
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.GoodIso

theorem exists_gl_to_one (A : Type) [CommRing A] [Finite (MaximalSpectrum A)] (σ : A →+* A)
    (hσ : ∀ y, σ (σ y) = y) (h2 : IsUnit (2 : A)) (hδ : ∃ δ : A, IsUnit δ ∧ σ δ = -δ)
    (hN : ∀ β : A, IsUnit β → σ β = β → ∃ a : A, a * σ a = β)
    (m : ℕ) (J : Matrix (Fin m) (Fin m) A) (hJ : ∀ i j, σ (J j i) = J i j) (hd : IsUnit J.det) :
    ∃ h : GL (Fin m) A,
      cT σ (h : Matrix (Fin m) (Fin m) A) * J * (h : Matrix (Fin m) (Fin m) A) = 1 := by
  obtain ⟨g, d, hg, hdd, hgJ⟩ := GlobalTheory.T.hermitian_unit_form_diagonalizes A σ hσ
    (fun m J hJ hu => GlobalTheory.T.hermitian_unit_form_represents_unit A σ hσ h2 hδ m J hJ hu) m J hJ hd
  choose a ha using fun i => hN (d i) (hdd i).1 (hdd i).2
  have hau : ∀ i, IsUnit (a i) := fun i =>
    isUnit_of_mul_isUnit_left (y := σ (a i)) (by rw [ha i]; exact (hdd i).1)
  choose c hc using fun i => (hau i).exists_right_inv
  have hcu : ∀ i, IsUnit (c i) := fun i => IsUnit.of_mul_eq_one (a i) (by rw [mul_comm]; exact hc i)
  have hdet : IsUnit (g * Matrix.diagonal c).det := by
    rw [Matrix.det_mul, Matrix.det_diagonal]
    exact hg.mul (IsUnit.prod_univ_iff.2 hcu)
  refine ⟨((Matrix.isUnit_iff_isUnit_det _).2 hdet).unit, ?_⟩
  rw [IsUnit.unit_spec, cT_mul]
  have hD : cT σ (Matrix.diagonal c) = Matrix.diagonal (fun i => σ (c i)) := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [cT]
    · simp [cT, Matrix.diagonal_apply, hij, Ne.symm hij]
  calc cT σ (Matrix.diagonal c) * cT σ g * J * (g * Matrix.diagonal c)
      = cT σ (Matrix.diagonal c) * (cT σ g * J * g) * Matrix.diagonal c := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by
        rw [hgJ, hD, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
        congr 1
        funext i
        have h1 : σ (c i) * σ (a i) = 1 := by rw [← map_mul, mul_comm, hc i, map_one]
        rw [← ha i]
        calc σ (c i) * (a i * σ (a i)) * c i = (σ (c i) * σ (a i)) * (a i * c i) := by ring
          _ = 1 := by rw [h1, hc i, one_mul]

theorem exists_gl_equiv (A : Type) [CommRing A] [Finite (MaximalSpectrum A)] (σ : A →+* A)
    (hσ : ∀ y, σ (σ y) = y) (h2 : IsUnit (2 : A)) (hδ : ∃ δ : A, IsUnit δ ∧ σ δ = -δ)
    (hN : ∀ β : A, IsUnit β → σ β = β → ∃ a : A, a * σ a = β)
    (m : ℕ) (J J' : Matrix (Fin m) (Fin m) A) (hJ : ∀ i j, σ (J j i) = J i j) (hd : IsUnit J.det)
    (hJ' : ∀ i j, σ (J' j i) = J' i j) (hd' : IsUnit J'.det) :
    ∃ G : GL (Fin m) A,
      J' = cT σ (G : Matrix (Fin m) (Fin m) A) * J * (G : Matrix (Fin m) (Fin m) A) := by
  obtain ⟨h, hh⟩ := exists_gl_to_one A σ hσ h2 hδ hN m J hJ hd
  obtain ⟨k, hk⟩ := exists_gl_to_one A σ hσ h2 hδ hN m J' hJ' hd'
  refine ⟨h * k⁻¹, ?_⟩
  have hkk : (k : Matrix (Fin m) (Fin m) A) * ((k⁻¹ : GL (Fin m) A) : Matrix (Fin m) (Fin m) A) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hck : cT σ ((k⁻¹ : GL (Fin m) A) : Matrix (Fin m) (Fin m) A) * cT σ (k : Matrix (Fin m) (Fin m) A) = 1 := by
    rw [← cT_mul, hkk, cT_one]
  set K : Matrix (Fin m) (Fin m) A := (k : Matrix (Fin m) (Fin m) A)
  set L : Matrix (Fin m) (Fin m) A := ((k⁻¹ : GL (Fin m) A) : Matrix (Fin m) (Fin m) A)
  set H : Matrix (Fin m) (Fin m) A := (h : Matrix (Fin m) (Fin m) A)
  have e1 : J' = cT σ L * (cT σ K * J' * K) * L := by
    calc J' = (cT σ L * cT σ K) * J' * (K * L) := by rw [hck, hkk, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  have e2 : cT σ (H * L) * J * (H * L) = cT σ L * (cT σ H * J * H) * L := by
    rw [cT_mul]; simp only [Matrix.mul_assoc]
  rw [Units.val_mul]
  change J' = cT σ (H * L) * J * (H * L)
  rw [e2, hh, ← hk, ← e1]

theorem exists_gl_sub {R : Type} [CommRing R] (s : R →+* R) (hs : ∀ y, s (s y) = y) (O : Subring R)
    (hO : ∀ y ∈ O, s y ∈ O) [Finite (MaximalSpectrum O)] (h2 : IsUnit (2 : O))
    (hδ : ∃ δ : O, IsUnit δ ∧ s (δ : R) = -(δ : R))
    (hN : ∀ β : O, IsUnit β → s (β : R) = β → ∃ a : O, (a : R) * s a = β)
    (m : ℕ) (K K' : Matrix (Fin m) (Fin m) R)
    (hK : ∀ i j, s (K j i) = K i j) (hK' : ∀ i j, s (K' j i) = K' i j)
    (iK : ∀ i j, K i j ∈ O) (iK' : ∀ i j, K' i j ∈ O)
    (wK : ∃ w ∈ O, K.det * w = 1) (wK' : ∃ w ∈ O, K'.det * w = 1) :
    ∃ g : GL (Fin m) R, K' = cT s (g : Matrix (Fin m) (Fin m) R) * K * (g : Matrix (Fin m) (Fin m) R) ∧
      (∀ i j, (g : Matrix (Fin m) (Fin m) R) i j ∈ O) ∧
      ∀ i j, ((g⁻¹ : GL (Fin m) R) : Matrix (Fin m) (Fin m) R) i j ∈ O := by
  let σO : O →+* O := (s.comp O.subtype).codRestrict O (fun y => hO y y.2)
  have hσO : ∀ y : O, ((σO y : O) : R) = s (y : R) := fun y => rfl
  have lift : ∀ (P : Matrix (Fin m) (Fin m) R) (iP : ∀ i j, P i j ∈ O), (∃ w ∈ O, P.det * w = 1) →
      ∃ Q : Matrix (Fin m) (Fin m) O, Q.map O.subtype = P ∧ IsUnit Q.det := by
    intro P iP ⟨w, hw, hPw⟩
    refine ⟨Matrix.of fun i j => ⟨P i j, iP i j⟩, by ext i j; rfl, ?_⟩
    have hdet : ((Matrix.of fun i j => (⟨P i j, iP i j⟩ : O)).det : O).1 = P.det := by
      have := RingHom.map_det O.subtype (Matrix.of fun i j => (⟨P i j, iP i j⟩ : O))
      exact this
    refine IsUnit.of_mul_eq_one ⟨w, hw⟩ (Subtype.ext ?_)
    simpa [hdet] using hPw
  obtain ⟨Q, rfl, uQ⟩ := lift K iK wK
  obtain ⟨Q', rfl, uQ'⟩ := lift K' iK' wK'
  have herm : ∀ (Q : Matrix (Fin m) (Fin m) O), (∀ i j, s ((Q.map O.subtype) j i) = (Q.map O.subtype) i j) →
      ∀ i j, σO (Q j i) = Q i j := fun Q h i j => Subtype.ext (h i j)
  obtain ⟨G, hG⟩ := exists_gl_equiv O σO (fun y => Subtype.ext (hs _)) h2
    (by obtain ⟨δ, h1, h3⟩ := hδ; exact ⟨δ, h1, Subtype.ext h3⟩)
    (fun β hβ hβ' => by
      obtain ⟨a, ha⟩ := hN β hβ (congrArg Subtype.val hβ')
      exact ⟨a, Subtype.ext ha⟩)
    m Q Q' (herm Q hK) uQ (herm Q' hK') uQ'
  have hcT : ∀ P : Matrix (Fin m) (Fin m) O,
      cT s (P.map O.subtype) = (cT σO P).map O.subtype := fun P => by ext i j; rfl
  refine ⟨bc O.subtype G, ?_, ?_, ?_⟩
  · have hv : ((bc O.subtype G : GL (Fin m) R) : Matrix (Fin m) (Fin m) R) =
        (G : Matrix (Fin m) (Fin m) O).map O.subtype := rfl
    rw [hv, hcT, hG, Matrix.map_mul, Matrix.map_mul]
  · intro i j
    exact (G.val i j).2
  · intro i j
    rw [← map_inv]
    exact ((G⁻¹).val i j).2

theorem sigma_sigma {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2]
  simp

theorem sigR_sigR {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) (h : ∀ x, σ (σ x) = x) (y : R ⊗[F] E) : sigR R σ (sigR R σ y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [sigR, h]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem mulVec_mem {R : Type} [CommRing R] (O : Subring R) {m : ℕ} (P : Matrix (Fin m) (Fin m) R)
    (hP : ∀ i j, P i j ∈ O) (x : Fin m → R) (hx : ∀ i, x i ∈ O) (i : Fin m) : P.mulVec x i ∈ O := by
  change ∑ j, P i j * x j ∈ O
  exact O.sum_mem fun j _ => O.mul_mem (hP i j) (hx j)

theorem good_iso : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (J' : Matrix (Fin M) (Fin M) E), IsHermND σ J' → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∃ g : GL (Fin M) (Fv F v ⊗[F] E), JR (Fv F v) J' = cT (sigR (Fv F v) σ) (g : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) * JR (Fv F v) J * (g : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) ∧ ∀ (n : ℕ) (X : Fin n → Fin M → Fv F v ⊗[F] E), actTup (Fv F v) g X ∈ latV b v ↔ X ∈ latV b v := by
  intro F E _ _ _ _ _ σ hCM M J hJ J' hJ' d b
  have h1 := (GlobalTheory.T.integral_almost_all_places F E σ hCM d b).1
  have ent : ∀ P : Matrix (Fin M) (Fin M) E, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ∀ i j k, (Algebra.TensorProduct.basis (Fv F v) b).repr (inclR (F := F) (Fv F v) (P i j)) k ∈
        v.adicCompletionIntegers F := fun P =>
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => h1 (P i j)
  filter_upwards [GlobalTheory.T.tensor_integer_ring_almost_all_places F E σ hCM d b, ent J, ent J', h1 (J.det)⁻¹, h1 (J'.det)⁻¹]
    with v hv eJ eJ' dJ dJ'
  obtain ⟨O, hmem, hst, hfin, h2, hδ, -, hN⟩ := hv
  have wit : ∀ P : Matrix (Fin M) (Fin M) E, P.det ≠ 0 →
      (∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr (inclR (F := F) (Fv F v) (P.det)⁻¹) k ∈
        v.adicCompletionIntegers F) → ∃ w ∈ O, (JR (Fv F v) P).det * w = 1 := by
    intro P hP hk
    refine ⟨inclR (F := F) (Fv F v) (P.det)⁻¹, (hmem _).2 hk, ?_⟩
    have : (JR (Fv F v) P).det = inclR (F := F) (Fv F v) P.det := (RingHom.map_det (inclR (F := F) (Fv F v)) P).symm
    rw [this, ← map_mul, mul_inv_cancel₀ hP, map_one]
  obtain ⟨g, hg, ig, ig'⟩ := exists_gl_sub (sigR (Fv F v) σ)
    (sigR_sigR (Fv F v) σ (sigma_sigma σ hCM)) O hst h2 hδ hN M (JR (Fv F v) J) (JR (Fv F v) J')
    (map_mem_HermR (Fv F v) σ J hJ.1) (map_mem_HermR (Fv F v) σ J' hJ'.1)
    (fun i j => (hmem _).2 (eJ i j)) (fun i j => (hmem _).2 (eJ' i j))
    (wit J hJ.2 dJ) (wit J' hJ'.2 dJ')
  refine ⟨g, hg, fun n X => ?_⟩
  have lat : ∀ Y : Fin n → Fin M → Fv F v ⊗[F] E, Y ∈ latV b v ↔ ∀ a i, Y a i ∈ O := fun Y =>
    ⟨fun h a i => (hmem _).2 (h a i), fun h a i => (hmem _).1 (h a i)⟩
  rw [lat, lat]
  constructor
  · intro h a i
    have e : X a = ((g⁻¹ : GL (Fin M) (Fv F v ⊗[F] E)) : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)).mulVec
        (actTup (Fv F v) g X a) := by
      simp only [actTup, Matrix.mulVec_mulVec]
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    rw [e]
    exact mulVec_mem O _ ig' _ (h a) i
  · intro h a i
    exact mulVec_mem O _ ig _ (h a) i

end GlobalTheory.CompanionTheory.SW.GoodIso
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianFormsIntegrallyEquivalentAlmostAllStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_forms_integrally_equivalent_almost_all : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (J' : Matrix (Fin M) (Fin M) E), IsHermND σ J' → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∃ g : GL (Fin M) (Fv F v ⊗[F] E), JR (Fv F v) J' = cT (sigR (Fv F v) σ) (g : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) * JR (Fv F v) J * (g : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) ∧ ∀ (n : ℕ) (X : Fin n → Fin M → Fv F v ⊗[F] E), actTup (Fv F v) g X ∈ latV b v ↔ X ∈ latV b v := by
  first | exact @GlobalTheory.CompanionTheory.SW.GoodIso.good_iso | exact GlobalTheory.CompanionTheory.SW.GoodIso.good_iso | (intros; apply GlobalTheory.CompanionTheory.SW.GoodIso.good_iso <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalGramFiberMeasuresAgreeAlmostAll
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW

theorem lattice_mass_fibre_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (J' : Matrix (Fin M) (Fin M) E), IsHermND σ J' → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ n : ℕ, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ lam, IsStdV v lam → ∀ m m', IsGramFib (Fv F v) σ J n (coordW (Fv F v) b lam n M) (coordHerm (Fv F v) σ b lam n) m → IsGramFib (Fv F v) σ J' n (coordW (Fv F v) b lam n M) (coordHerm (Fv F v) σ b lam n) m' → ∀ S, m S (latV b v) = m' S (latV b v) := by
  intro F E _ _ _ _ _ σ hσ M J hJ J' hJ' d b n
  filter_upwards [GlobalTheory.T.hermitian_forms_integrally_equivalent_almost_all F E σ hσ M J hJ J' hJ' d b] with v hv
  intro lam hlam m m' hm hm' S
  obtain ⟨g, hg, hlat⟩ := hv
  have hL := GlobalTheory.T.completion_is_local_ring F v
  obtain ⟨h1, h2, h3, h4, -⟩ := id hL
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := h4
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨t1, t2, t3, t4, -, -, -, t8, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Fv F v)
  haveI := t1
  haveI := t2
  haveI := t3
  haveI := t4
  haveI := t8 n M
  haveI := hlam.1
  obtain ⟨-, c2, c3⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hσ (Fv F v) d b lam hlam.1
  haveI := c2 n M
  obtain ⟨a1, a2, a3, -⟩ := GlobalTheory.T.local_lattice_compact_open_unit_volume F E σ hσ d b n M v
  have hcont : ∀ k : GL (Fin M) (Fv F v ⊗[F] E),
      Continuous (actTup (Fv F v) (n := n) k) := by
    intro k
    refine continuous_pi fun a => ?_
    exact Continuous.matrix_mulVec continuous_const ((continuous_apply a))
  have hinv : ∀ (k l : GL (Fin M) (Fv F v ⊗[F] E)), k * l = 1 → ∀ X : Fin n → Fin M → Fv F v ⊗[F] E,
      actTup (Fv F v) k (actTup (Fv F v) l X) = X := by
    intro k l hkl X
    funext a
    have h : (k : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) * (l : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) = 1 := by
      rw [← Units.val_mul, hkl, Units.val_one]
    simp only [actTup, Matrix.mulVec_mulVec, h, Matrix.one_mulVec]
  let e : (Fin n → Fin M → Fv F v ⊗[F] E) ≃+ (Fin n → Fin M → Fv F v ⊗[F] E) :=
    { toFun := actTup (Fv F v) g
      invFun := actTup (Fv F v) g⁻¹
      left_inv := hinv g⁻¹ g (inv_mul_cancel g)
      right_inv := hinv g g⁻¹ (mul_inv_cancel g)
      map_add' := by
        intro X Y
        funext a
        simp only [actTup, Pi.add_apply, Matrix.mulVec_add] }
  have hmap : (coordW (Fv F v) b lam n M).map e = coordW (Fv F v) b lam n M :=
    (GlobalTheory.T.map_addHaar_addEquiv_eq_smul_and_eq_of_compact_open _ _ (coordW (Fv F v) b lam n M) (coordW (Fv F v) b lam n M) e (hcont g)
      (hcont g⁻¹)).2 (latV b v) (latV b v) a1 a2 ⟨0, a3⟩ (hlat n) rfl
  have hfib := GlobalTheory.T.gram_fiber_measures_change_of_form F E σ hσ M J hJ J' hJ' (Fv F v) hL n (coordW (Fv F v) b lam n M)
    (coordHerm (Fv F v) σ b lam n) m (c2 n M) (c3 n) hm (coordW (Fv F v) b lam n M) m' (c2 n M) hm' g hg 1
    (by rw [one_smul]; exact hmap) S
  have hval := congrArg (fun μ => μ (latV b v)) hfib
  simp only [one_smul] at hval
  rw [Measure.map_apply (hcont g).measurable a2.measurableSet] at hval
  have hpre : actTup (Fv F v) (n := n) g ⁻¹' latV (M := M) (n := n) b v = latV b v := by
    ext X
    exact hlat n X
  rw [hpre] at hval
  exact hval.symm

end GlobalTheory.CompanionTheory.SW
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalGramFiberMeasuresAgreeAlmostAllStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_gram_fiber_measures_agree_almost_all : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (J' : Matrix (Fin M) (Fin M) E), IsHermND σ J' → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ n : ℕ, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ lam, IsStdV v lam → ∀ m m', IsGramFib (Fv F v) σ J n (coordW (Fv F v) b lam n M) (coordHerm (Fv F v) σ b lam n) m → IsGramFib (Fv F v) σ J' n (coordW (Fv F v) b lam n M) (coordHerm (Fv F v) σ b lam n) m' → ∀ S, m S (latV b v) = m' S (latV b v) := by
  first | exact @GlobalTheory.CompanionTheory.SW.lattice_mass_fibre_eq | exact GlobalTheory.CompanionTheory.SW.lattice_mass_fibre_eq | (intros; apply GlobalTheory.CompanionTheory.SW.lattice_mass_fibre_eq <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RankZeroGramFiberMeasure
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RankZeroGramFiberMeasure
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.GramEmpty

theorem fibre_eq_dirac_of_unique {V X : Type} [MeasurableSpace V] [MeasurableSpace X] [Subsingleton V]
    [Subsingleton X] (μ : Measure V) (ν : Measure X) (m : X → Measure V) (x₀ : V)
    (hμ : μ Set.univ = 1) (hν : ν Set.univ = 1)
    (h : ∀ φ : V → ℝ≥0∞, Measurable φ → ∫⁻ v, φ v ∂μ = ∫⁻ b, ∫⁻ v, φ v ∂(m b) ∂ν) (S : X) :
    m S = Measure.dirac x₀ := by
  have h1 := h (fun _ => 1) measurable_const
  have hc : (fun b => ∫⁻ _, (1 : ℝ≥0∞) ∂(m b)) = fun _ => m S Set.univ := by
    funext b
    rw [Subsingleton.elim b S]
    simp
  rw [hc] at h1
  simp only [lintegral_const, one_mul, hμ, hν, mul_one] at h1
  ext s _
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  · rw [Subsingleton.eq_univ_of_nonempty hs, ← h1]
    simp

end GlobalTheory.CompanionTheory.SW.GramEmpty

open GlobalTheory.CompanionTheory.SW.GramEmpty in
theorem GlobalTheory.CompanionTheory.SW.GramEmpty.fibre_gram_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ (lam : Measure R), lam.IsAddHaarMeasure → ∀ m, IsGramFib R σ J 0 (coordW R b lam 0 M) (coordHerm R σ b lam 0) m → ∀ S, m S = Measure.dirac (fun a => a.elim0) := by
  intro F E _ _ _ _ _ σ _ M J _ R _ _ _ _ _ _ d b lam _ m hm S
  obtain ⟨-, h2, -⟩ := hm
  haveI : Subsingleton (HermR R σ 0) :=
    ⟨fun x y => Subtype.ext (Subsingleton.elim _ _)⟩
  haveI : IsEmpty {p : Fin 0 × Fin 0 // p.1 < p.2} := ⟨fun p => p.1.1.elim0⟩
  have hU : {X : Fin 0 → Fin M → R ⊗[F] E | IsUnit (gramR R σ J X).det} = Set.univ := by
    ext X
    simp
  have hμ : coordW R b lam 0 M Set.univ = 1 := by
    unfold coordW
    rw [Measure.pi_of_empty]
    simp
  have hν : coordHerm R σ b lam 0 Set.univ = 1 := by
    unfold coordHerm
    rw [Measure.comap_apply _ (Function.injective_of_subsingleton _)
      (fun s _ => Subsingleton.measurableSet) _ MeasurableSet.univ]
    have : (Set.univ : Set ((Fin 0 → R) × ({p : Fin 0 × Fin 0 // p.1 < p.2} → R ⊗[F] E))) =
        Set.univ ×ˢ Set.univ := by simp
    rw [Set.image_univ_of_surjective, this, Measure.prod_prod, Measure.pi_of_empty, Measure.pi_of_empty]
    · simp
    · intro y
      exact ⟨0, Subsingleton.elim _ _⟩
  refine fibre_eq_dirac_of_unique _ _ m _ hμ hν (fun φ hφ => ?_) S
  have := h2 φ hφ
  rw [hU, Measure.restrict_univ] at this
  exact this
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RankZeroGramFiberMeasureStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_zero_gram_fiber_measure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ (lam : Measure R), lam.IsAddHaarMeasure → ∀ m, IsGramFib R σ J 0 (coordW R b lam 0 M) (coordHerm R σ b lam 0) m → ∀ S, m S = Measure.dirac (fun a => a.elim0) := by
  first | exact @GlobalTheory.CompanionTheory.SW.GramEmpty.fibre_gram_zero | exact GlobalTheory.CompanionTheory.SW.GramEmpty.fibre_gram_zero | (intros; apply GlobalTheory.CompanionTheory.SW.GramEmpty.fibre_gram_zero <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalDensitiesBoundedAlmostAll
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.GoodMass

section Alg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}

theorem exists_moved (hcm : IsCMExt F E σ) : ∃ c : E, σ c ≠ c := by
  by_contra h
  push_neg at h
  obtain ⟨-, htc, -, hconj⟩ := hcm
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  have hc : w.IsComplex := htc.isComplex w
  have hr : w.IsReal := by
    rw [InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    ext x
    have := hconj w.embedding x
    rw [h x] at this
    simp only [ComplexEmbedding.conjugate_coe_eq]
    exact this.symm
  exact InfinitePlace.not_isReal_iff_isComplex.2 hc hr

theorem fixed_mem (hcm : IsCMExt F E σ) (x : E) (hx : σ x = x) : ∃ t : F, algebraMap F E t = x := by
  obtain ⟨c, hc⟩ := exists_moved hcm
  have hfr : Module.finrank F E = 2 := hcm.2.2.1
  haveI : IsSimpleOrder (Subalgebra F E) :=
    Subalgebra.isSimpleOrder_of_finrank_prime F E (by rw [hfr]; exact Nat.prime_two)
  rcases eq_bot_or_eq_top (AlgHom.equalizer σ (AlgHom.id F E)) with h | h
  · have hm : x ∈ AlgHom.equalizer σ (AlgHom.id F E) := by
      simpa [AlgHom.mem_equalizer] using hx
    rw [h, Algebra.mem_bot] at hm
    exact hm
  · have hm : c ∈ AlgHom.equalizer σ (AlgHom.id F E) := by rw [h]; trivial
    exact absurd (by simpa [AlgHom.mem_equalizer] using hm) hc

theorem hE_add_left {n : ℕ} (T : Matrix (Fin n) (Fin n) E) (x x' y : Fin n → E) :
    hE σ T (x + x') y = hE σ T x y + hE σ T x' y := by
  simp [hE, hform, add_mul, Finset.sum_add_distrib]

theorem hE_add_right {n : ℕ} (T : Matrix (Fin n) (Fin n) E) (x y y' : Fin n → E) :
    hE σ T x (y + y') = hE σ T x y + hE σ T x y' := by
  simp [hE, hform, mul_add, Finset.sum_add_distrib]

theorem hE_smul_left {n : ℕ} (T : Matrix (Fin n) (Fin n) E) (c : E) (x y : Fin n → E) :
    hE σ T (c • x) y = σ c * hE σ T x y := by
  simp [hE, hform, Finset.mul_sum, mul_assoc]

theorem hE_smul_right {n : ℕ} (T : Matrix (Fin n) (Fin n) E) (c : E) (x y : Fin n → E) :
    hE σ T x (c • y) = c * hE σ T x y := by
  simp only [hE, hform, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hE_single {n : ℕ} (T : Matrix (Fin n) (Fin n) E) (i j : Fin n) :
    hE σ T (Pi.single i 1) (Pi.single j 1) = T i j := by
  simp [hE, hform, Pi.single_apply]

theorem hE_self_fixed {n : ℕ} (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b)
    (x : Fin n → E) (hinv : ∀ y, σ (σ y) = y) : σ (hE σ T x x) = hE σ T x x := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hE, hform, map_sum, map_mul, RingHom.coe_coe]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hinv, hT]
  ring

end Alg

section Alg2

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}

theorem exists_aniso (hcm : IsCMExt F E σ) {n : ℕ} (T : Matrix (Fin (n + 1)) (Fin (n + 1)) E)
    (hT : ∀ a b, σ (T b a) = T a b) (hdet : T.det ≠ 0) :
    ∃ (x : Fin (n + 1) → E) (t : F), t ≠ 0 ∧ hE σ T x x = algebraMap F E t := by
  by_contra hno
  push_neg at hno
  have hinv : ∀ y, σ (σ y) = y := by
    intro y
    obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
    apply w.embedding.injective
    rw [hcm.2.2.2, hcm.2.2.2, star_star]
  have h1 : ∀ x, hE σ T x x = 0 := by
    intro x
    obtain ⟨t, ht⟩ := fixed_mem hcm _ (hE_self_fixed T hT x hinv)
    by_cases h0 : t = 0
    · rw [← ht, h0, map_zero]
    · exact absurd ht.symm (hno x t h0)
  have h2 : ∀ x y, hE σ T x y + hE σ T y x = 0 := by
    intro x y
    have := h1 (x + y)
    rw [hE_add_left, hE_add_right, hE_add_right, h1 x, h1 y] at this
    linear_combination this
  obtain ⟨c, hc⟩ := exists_moved hcm
  have h3 : ∀ x y, hE σ T x y = 0 := by
    intro x y
    have e := h2 (c • x) y
    rw [hE_smul_left, hE_smul_right] at e
    have e' : (σ c - c) * hE σ T x y = 0 := by
      linear_combination e - c * h2 x y
    exact (mul_eq_zero.1 e').resolve_left (sub_ne_zero.2 hc)
  apply hdet
  have hz : T = 0 := by
    ext i j
    rw [← hE_single (σ := σ) T i j, h3]
    rfl
  rw [hz, Matrix.det_zero]

theorem blockOne_herm {M : ℕ} (a : E) (ha : σ a = a) (A : Matrix (Fin M) (Fin M) E)
    (hA : ∀ i j, σ (A j i) = A i j) : ∀ i j, σ (blockOne a A j i) = blockOne a A i j := by
  intro i j
  refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j
  · simpa [blockOne] using ha
  · simp [blockOne]
  · simp [blockOne]
  · simpa [blockOne] using hA i' j'

theorem one_hermND (M : ℕ) : IsHermND σ (1 : Matrix (Fin M) (Fin M) E) := by
  refine ⟨fun i j => ?_, by simp⟩
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h)]

theorem blockOne_hermND {M : ℕ} (t : F) (ht : t ≠ 0) :
    IsHermND σ (blockOne (algebraMap F E t) (1 : Matrix (Fin M) (Fin M) E)) := by
  refine ⟨blockOne_herm _ (σ.commutes t) _ (one_hermND M).1, ?_⟩
  rw [AlgSplit.det_blockOne]
  simpa using ht

end Alg2

theorem arith {x y q C : ℝ} {k : ℕ} (hq : 1 ≤ q) (hk : 2 ≤ k) (hx : |x - 1| ≤ 2 / q ^ k)
    (hy : |y - 1| ≤ C / q ^ 2) : |x * y - 1| ≤ (3 * |C| + 2) / q ^ 2 := by
  have hq0 : 0 < q ^ 2 := by positivity
  set e : ℝ := 1 / q ^ 2 with he
  have he0 : 0 < e := by positivity
  have he1 : e ≤ 1 := by
    rw [he, div_le_one hq0]
    nlinarith
  have hx' : |x - 1| ≤ 2 * e := by
    refine hx.trans ?_
    rw [he, mul_one_div]
    exact div_le_div_of_nonneg_left (by norm_num) hq0 (pow_le_pow_right₀ hq hk)
  have hy' : |y - 1| ≤ |C| * e := by
    refine hy.trans ?_
    rw [he, mul_one_div]
    exact div_le_div_of_nonneg_right (le_abs_self C) hq0.le
  have hC : 0 ≤ |C| := abs_nonneg C
  have hdec : x * y - 1 = (x - 1) * (y - 1) + (x - 1) + (y - 1) := by ring
  have hprod : |(x - 1) * (y - 1)| ≤ 2 * |C| * e := by
    rw [abs_mul]
    calc |x - 1| * |y - 1| ≤ (2 * e) * (|C| * e) :=
          mul_le_mul hx' hy' (abs_nonneg _) (by positivity)
      _ = 2 * |C| * e * e := by ring
      _ ≤ 2 * |C| * e * 1 := by
          exact mul_le_mul_of_nonneg_left he1 (by positivity)
      _ = 2 * |C| * e := by ring
  have htri : |x * y - 1| ≤ |(x - 1) * (y - 1)| + |x - 1| + |y - 1| := by
    rw [hdec]
    exact (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)
  have hfin : (3 * |C| + 2) / q ^ 2 = (3 * |C| + 2) * e := by rw [he, mul_one_div]
  rw [hfin]
  nlinarith

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}

theorem exists_family (hcm : IsCMExt F E σ) {M : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (hJ : IsHermND σ J) {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (lam : Measure (Fv F v)) (hl : IsStdV v lam) (n : ℕ) :
    ∃ m, IsGramFib (Fv F v) σ J n (coordW (Fv F v) b lam n M) (coordHerm (Fv F v) σ b lam n) m := by
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  have hloc : IsLocR (Fv F v) := GlobalTheory.T.completion_is_local_ring F v
  obtain ⟨h1, h2, h3, h4, -⟩ := hloc
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := h4
  haveI := hl.1
  obtain ⟨-, hW, hH⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hcm (Fv F v) d b lam hl.1
  haveI := hW n M
  haveI := hH n
  exact GlobalTheory.T.exists_gram_fiber_measures F E σ hcm M J hJ (Fv F v) (GlobalTheory.T.completion_is_local_ring F v) n _ _ (hW n M) (hH n)

theorem absNorm_one_le (v : HeightOneSpectrum (𝓞 F)) : (1 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := by
  have : 0 < Ideal.absNorm v.asIdeal :=
    Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot)
  exact_mod_cast this

theorem key (hcm : IsCMExt F E σ) : ∀ (n M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    (n = 0 ∨ n + 2 ≤ M) → ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b),
    T.det ≠ 0 → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∃ C : ℝ,
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ lam, IsStdV v lam → ∀ m,
      IsGramFib (Fv F v) σ J n (coordW (Fv F v) b lam n M) (coordHerm (Fv F v) σ b lam n) m →
      |(m (hermOf (Fv F v) σ T hT) (latV b v)).toReal - 1| ≤
        C / (Ideal.absNorm v.asIdeal : ℝ) ^ 2 := by
  intro n
  induction n with
  | zero =>
    intro M J hJ _ T hT _ d b
    refine ⟨0, Filter.Eventually.of_forall ?_⟩
    intro v lam hl m hm
    haveI : BorelSpace (Fv F v) := ⟨rfl⟩
    have h0 := GlobalTheory.T.rank_zero_gram_fiber_measure F E σ hcm M J hJ (Fv F v) (GlobalTheory.T.completion_is_local_ring F v) d b lam hl.1 m hm
      (hermOf (Fv F v) σ T hT)
    have hU : (latV b v : Set (Fin 0 → Fin M → Fv F v ⊗[F] E)) = Set.univ := by
      ext Y
      simp [latV]
    rw [h0, hU, measure_univ]
    simp
  | succ n ih =>
    intro M J hJ hn T hT hdet d b
    have hM : n + 3 ≤ M := by omega
    obtain ⟨M₁, rfl⟩ : ∃ M₁, M = M₁ + 1 := ⟨M - 1, by omega⟩
    obtain ⟨x, t, ht, hx⟩ := exists_aniso hcm T hT hdet
    obtain ⟨g, T₁, hT₁, hblock, -⟩ :=
      AlgSplit.split_anisotropic F E σ hcm n T ⟨hT, hdet⟩ t x ht hx
    have hbh : ∀ a b, σ (blockOne (algebraMap F E t) T₁ b a) = blockOne (algebraMap F E t) T₁ a b :=
      blockOne_herm _ (σ.commutes t) _ hT₁.1
    have hgdet : (g : Matrix (Fin (n + 1)) (Fin (n + 1)) E).det ≠ 0 :=
      ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero
    have hone : IsHermND σ (1 : Matrix (Fin M₁) (Fin M₁) E) := one_hermND M₁
    have hJ' : IsHermND σ (blockOne (algebraMap F E t) (1 : Matrix (Fin M₁) (Fin M₁) E)) :=
      blockOne_hermND t ht
    obtain ⟨C₁, hC₁⟩ := ih M₁ 1 hone (Or.inr (by omega)) T₁ hT₁.1 hT₁.2 d b
    refine ⟨3 * |C₁| + 2, ?_⟩
    have e1 := GlobalTheory.T.local_densities_congruent_target_almost_all F E σ hcm (M₁ + 1) J hJ (n + 1) T hT hdet g hgdet _ hbh hblock d b
    have e2 := GlobalTheory.T.local_gram_fiber_measures_agree_almost_all F E σ hcm (M₁ + 1) J hJ _ hJ' d b (n + 1)
    have e3 := GlobalTheory.T.local_densities_block_one_almost_all F E σ hcm M₁ 1 hone t ht n T₁ hT₁.1 hT₁.2 hbh d b
    have e4 := GlobalTheory.T.rank_one_local_density_almost_all F E σ hcm (M₁ + 1) _ hJ' (by omega) d b
    have e5 := (GlobalTheory.T.integral_almost_all_places F E σ hcm d b).2 t ht
    filter_upwards [e1, e2, e3, e4, e5, hC₁] with v h1 h2 h3 h4 h5 h6 lam hl m hm
    obtain ⟨m', hm'⟩ := exists_family hcm hJ' b v lam hl (n + 1)
    obtain ⟨m₁, hm₁⟩ := exists_family hcm hJ' b v lam hl 1
    obtain ⟨m₂, hm₂⟩ := exists_family hcm hone b v lam hl n
    have a1 := h1 lam hl m hm
    have a2 := h2 lam hl m m' hm hm' (hermOf (Fv F v) σ _ hbh)
    have a3 := h3 lam hl m' m₁ m₂ hm' hm₁ hm₂
    have hint : algebraMap F (Fv F v) t ∈ v.adicCompletionIntegers F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      exact h5.le
    have hne : algebraMap F (Fv F v) t ≠ 0 := by
      intro h0
      rw [h0] at h5
      simp at h5
    have a4 := h4 lam hl m₁ hm₁ _ hint hne
    have a6 := h6 lam hl m₂ hm₂
    rw [← a1, a2, a3, ENNReal.toReal_mul]
    exact arith (absNorm_one_le v) (by omega) a4 a6

end Main

theorem mass_fibre_good : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n : ℕ), n = 0 ∨ n + 2 ≤ M → ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∃ C : ℝ, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ lam, IsStdV v lam → ∀ m, IsGramFib (Fv F v) σ J n (coordW (Fv F v) b lam n M) (coordHerm (Fv F v) σ b lam n) m → |(m (hermOf (Fv F v) σ T hT) (latV b v)).toReal - 1| ≤ C / (Ideal.absNorm v.asIdeal : ℝ) ^ 2 := by
  intro F E _ _ _ _ _ σ hcm M J hJ n hn T hT hdet d b
  exact key hcm n M J hJ hn T hT hdet d b

end GlobalTheory.CompanionTheory.SW.GoodMass
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalDensitiesBoundedAlmostAllStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_densities_bounded_almost_all : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n : ℕ), n = 0 ∨ n + 2 ≤ M → ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∃ C : ℝ, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ lam, IsStdV v lam → ∀ m, IsGramFib (Fv F v) σ J n (coordW (Fv F v) b lam n M) (coordHerm (Fv F v) σ b lam n) m → |(m (hermOf (Fv F v) σ T hT) (latV b v)).toReal - 1| ≤ C / (Ideal.absNorm v.asIdeal : ℝ) ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.SW.GoodMass.mass_fibre_good | exact GlobalTheory.CompanionTheory.SW.GoodMass.mass_fibre_good | (intros; apply GlobalTheory.CompanionTheory.SW.GoodMass.mass_fibre_good <;> assumption)
end
