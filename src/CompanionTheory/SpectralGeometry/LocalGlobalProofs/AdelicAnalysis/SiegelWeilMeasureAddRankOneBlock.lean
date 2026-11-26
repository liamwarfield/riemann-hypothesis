module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalMeasuresOrthogonalSumAlmostAllPlaces
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureRankOne
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarFundamentalDomainOrthogonalSum

@[expose] public section

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ScalarMultiplicationEulerProduct
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ScalarMultiplicationEulerProduct
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.PfK

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

section

variable {F E : Type} [Field F] [Field E] [Algebra F E]
  (R : Type) [CommRing R] [Algebra F R]

theorem repr_inclR_mul {d : ℕ} (b : Module.Basis (Fin d) F E) (t : E) (y : R ⊗[F] E) :
    (fun k => (Algebra.TensorProduct.basis R b).repr (inclR R t * y) k) =
      (Algebra.leftMulMatrix b t).map (algebraMap F R) *ᵥ
        (fun k => (Algebra.TensorProduct.basis R b).repr y k) := by
  induction y using TensorProduct.induction_on with
  | zero => funext k; simp [Matrix.mulVec, dotProduct]
  | tmul r e =>
    have h1 : inclR R t * (r ⊗ₜ[F] e) = r ⊗ₜ[F] (t * e) := by
      simp [inclR, Algebra.TensorProduct.tmul_mul_tmul]
    have h2 : (fun j => ((Algebra.TensorProduct.basis R b).repr (r ⊗ₜ[F] e)) j) =
        r • (algebraMap F R ∘ b.repr e) := by
      funext j
      simp [Algebra.TensorProduct.basis_repr_tmul]
    rw [h1, h2, Matrix.mulVec_smul]
    funext k
    rw [Pi.smul_apply, ← RingHom.map_mulVec, Algebra.leftMulMatrix_mulVec_repr]
    simp [Algebra.TensorProduct.basis_repr_tmul]
  | add y1 y2 h1 h2 =>
    have e1 : (fun k => ((Algebra.TensorProduct.basis R b).repr (y1 + y2)) k) =
        (fun k => ((Algebra.TensorProduct.basis R b).repr y1) k) +
          (fun k => ((Algebra.TensorProduct.basis R b).repr y2) k) := by
      funext k; simp
    have e2 : (fun k => ((Algebra.TensorProduct.basis R b).repr (inclR R t * (y1 + y2))) k) =
        (fun k => ((Algebra.TensorProduct.basis R b).repr (inclR R t * y1)) k) +
          (fun k => ((Algebra.TensorProduct.basis R b).repr (inclR R t * y2)) k) := by
      funext k; simp [mul_add]
    rw [e1, e2, Matrix.mulVec_add, h1, h2]

variable [TopologicalSpace R] [IsTopologicalRing R] [SecondCountableTopology R]
  [MeasurableSpace R] [BorelSpace R]

theorem map_inclR_mul [Module.Finite F E] {d : ℕ} (b : Module.Basis (Fin d) F E) (t : E) (c : ℝ≥0)
    (h : ∀ μ : Measure (Fin d → R), μ.IsAddHaarMeasure →
      μ.map (fun x => (Algebra.leftMulMatrix b t).map (algebraMap F R) *ᵥ x) = c • μ)
    (μ : Measure (R ⊗[F] E)) (hμ : μ.IsAddHaarMeasure) :
    μ.map (fun y => inclR R t * y) = c • μ := by
  have : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (R ⊗[F] E) := TopK.isTopRing R
  let L : (R ⊗[F] E) ≃L[R] (Fin d → R) :=
    { toLinearEquiv := (Algebra.TensorProduct.basis R b).equivFun,
      continuous_toFun := (TopK.coordHomeo R b).continuous,
      continuous_invFun := (TopK.coordHomeo R b).symm.continuous }
  have hL : ∀ y, L y = fun k => ((Algebra.TensorProduct.basis R b).repr y) k := fun y =>
    Module.Basis.equivFun_apply _ _
  have : (μ.map L).IsAddHaarMeasure := L.isAddHaarMeasure_map μ
  have hν := h (μ.map L) inferInstance
  have hA : Continuous fun x : Fin d → R => (Algebra.leftMulMatrix b t).map (algebraMap F R) *ᵥ x :=
    continuous_const.matrix_mulVec continuous_id
  have hmul : (fun y => inclR R t * y) =
      L.symm ∘ (fun x => (Algebra.leftMulMatrix b t).map (algebraMap F R) *ᵥ x) ∘ L := by
    funext y
    apply L.injective
    simp only [Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply]
    rw [hL, hL]
    exact repr_inclR_mul R b t y
  have hid : (μ.map L).map L.symm = μ := by
    rw [Measure.map_map L.symm.continuous.measurable L.continuous.measurable]
    have : (L.symm ∘ L) = id := funext fun y => L.symm_apply_apply y
    rw [this, Measure.map_id]
  rw [hmul, ← Measure.map_map L.symm.continuous.measurable (hA.comp L.continuous).measurable,
    ← Measure.map_map hA.measurable L.continuous.measurable, hν, Measure.map_smul, hid]
  exact L.symm.continuous.measurable.aemeasurable

end

end GlobalTheory.CompanionTheory.SW.PfK


open GlobalTheory.CompanionTheory.SW.PfK in
theorem GlobalTheory.CompanionTheory.SW.map_inclR_prodFormula : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ t : E, t ≠ 0 → ∃ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c ∧ (∀ μ : Measure (Ainf F ⊗[F] E), μ.IsAddHaarMeasure → μ.map (fun y => inclR (Ainf F) t * y) = cinf • μ) ∧ ∀ v : HeightOneSpectrum (𝓞 F), (∀ μ : Measure (Fv F v ⊗[F] E), μ.IsAddHaarMeasure → μ.map (fun y => inclR (Fv F v) t * y) = c v • μ) := by
  intro F E _ _ _ _ _ σ hCM t ht
  have hfin : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨cinf, c, hU, hinf, hv⟩ := T.addHaar_map_mulVec_eq_smul_at_all_places F (Fin (Module.finrank F E))
    (Algebra.leftMulMatrix (Module.finBasis F E) t) (by
      rw [← Algebra.norm_eq_matrix_det]
      exact Algebra.norm_ne_zero_iff.2 ht)
  refine ⟨cinf, c, hU, fun μ hμ => ?_, fun v μ hμ => ?_⟩
  · have : BorelSpace (Ainf F) := ⟨rfl⟩
    exact map_inclR_mul (Ainf F) (Module.finBasis F E) t cinf hinf μ hμ
  · have : SecondCountableTopology (Fv F v) := (LocFv.isLocR_Fv F v).2.2.1
    have : BorelSpace (Fv F v) := ⟨rfl⟩
    exact map_inclR_mul (Fv F v) (Module.finBasis F E) t (c v) (hv v) μ hμ
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ScalarMultiplicationEulerProductStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scalar_multiplication_euler_product : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ t : E, t ≠ 0 → ∃ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c ∧ (∀ μ : Measure (Ainf F ⊗[F] E), μ.IsAddHaarMeasure → μ.map (fun y => inclR (Ainf F) t * y) = cinf • μ) ∧ ∀ v : HeightOneSpectrum (𝓞 F), (∀ μ : Measure (Fv F v ⊗[F] E), μ.IsAddHaarMeasure → μ.map (fun y => inclR (Fv F v) t * y) = c v • μ) := by
  first | exact @GlobalTheory.CompanionTheory.SW.map_inclR_prodFormula | exact GlobalTheory.CompanionTheory.SW.map_inclR_prodFormula | (intros; apply GlobalTheory.CompanionTheory.SW.map_inclR_prodFormula <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalDensityBlockOneEventually
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalDensityBlockOneEventually
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.GoodMass

theorem continuous_act_consTup {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] [TopologicalSpace R] (hring : IsTopologicalRing (R ⊗[F] E)) (σ : E →ₐ[F] E) {M n : ℕ}
    (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (h : HA R σ J) :
    Continuous fun X : Fin n → Fin M → R ⊗[F] E => actW R σ J h (consTup X) := by
  refine continuous_pi fun a => continuous_pi fun i => ?_
  simp only [actW, actTup, Matrix.mulVec, dotProduct]
  refine continuous_finsetSum _ fun j _ => continuous_const.mul ?_
  refine Fin.cases ?_ (fun a' => ?_) a
  · refine Fin.cases ?_ (fun j' => ?_) j <;> simpa [consTup] using continuous_const
  · refine Fin.cases ?_ (fun j' => ?_) j
    · simpa [consTup] using continuous_const
    · have hc : Continuous fun X : Fin n → Fin M → R ⊗[F] E => X a' j' :=
        (continuous_apply j').comp (continuous_apply a')
      simpa [consTup] using hc

theorem good_mass : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ t : F, t ≠ 0 → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 → ∀ (hT' : ∀ a b, σ (blockOne (algebraMap F E t) T b a) = blockOne (algebraMap F E t) T a b) (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ lam : Measure (Fv F v), lam.IsAddHaarMeasure → ∀ m m₁ m', IsGramFib (Fv F v) σ (blockOne (algebraMap F E t) J) (n + 1) (coordW (Fv F v) b lam (n + 1) (M + 1)) (coordHerm (Fv F v) σ b lam (n + 1)) m → IsGramFib (Fv F v) σ (blockOne (algebraMap F E t) J) 1 (coordW (Fv F v) b lam 1 (M + 1)) (coordHerm (Fv F v) σ b lam 1) m₁ → IsGramFib (Fv F v) σ J n (coordW (Fv F v) b lam n M) (coordHerm (Fv F v) σ b lam n) m' → ∀ c : ℝ≥0, (coordK (Fv F v) b lam).map (fun y => inclR (Fv F v) (algebraMap F E t) * y) = c • coordK (Fv F v) b lam → m (hermOf (Fv F v) σ _ hT') (latV b v) = (c : ℝ≥0∞) ^ n * (m' (hermOf (Fv F v) σ T hT) (latV b v) * m₁ (hermScal (Fv F v) σ (algebraMap F (Fv F v) t)) (latV b v)) := by
  intro F E _ _ _ _ _ σ hCM M J hJ t ht n T hT hdetT hT' d b
  obtain ⟨hdet, hherm, -, -⟩ := BlockAlg.block_alg F E σ hCM M J t
  have hND : IsHermND σ (blockOne (algebraMap F E t) J) :=
    ⟨hherm hJ.1, by
      rw [hdet]
      exact mul_ne_zero (by simpa using ht) hJ.2⟩
  filter_upwards [StageGood.stage_good F E σ hCM M J hJ t ht n T hT hdetT d b] with v hv
  intro lam hlam m m₁ m' hm hm₁ hm' c hc
  have hLoc := LocFv.isLocR_Fv F v
  obtain ⟨i1, i2, i3, i4, i5, i6, -⟩ := id hLoc
  have : BorelSpace (Fv F v) := ⟨rfl⟩
  have hH := coord_measures_haar F E σ hCM (Fv F v) d b lam hlam
  obtain ⟨hring, -, -, -, -, -, -, hB, -, -⟩ := TopK.topTens_props F E σ hCM (Fv F v)
  have hlat : ∀ n' M' : ℕ, MeasurableSet (latV b v : Set (Fin n' → Fin M' → Fv F v ⊗[F] E)) := by
    intro n' M'
    haveI := hB n' M'
    exact ((MeasProj.proj_props F E σ hCM d b n' M').2.2.2.1 v).2.measurableSet
  obtain ⟨Ψ, -, hΨ, hint⟩ := GlobalTheory.T.local_density_block_one_product F E σ hCM M J hJ t ht n T hT hdetT hT' (Fv F v) hLoc d b lam hlam
    m m₁ m' hm hm₁ hm' c hc ((latV b v).indicator 1) (measurable_one.indicator (hlat _ _))
  set A := m' (hermOf (Fv F v) σ T hT) (latV b v) with hA
  have hae : Ψ =ᵐ[m₁ (hermScal (Fv F v) σ (algebraMap F (Fv F v) t))] (latV b v).indicator (fun _ => A) := by
    filter_upwards [mem_ae_iff.2 (hm₁.1 (hermScal (Fv F v) σ (algebraMap F (Fv F v) t)))] with y hy
    obtain ⟨hy1, hy2⟩ := hy
    have hg : gramR (Fv F v) σ (blockOne (algebraMap F E t) J)
        (fun _ : Fin 1 => (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → Fv F v ⊗[F] E)) =
        gramR (Fv F v) σ (blockOne (algebraMap F E t) J) y :=
      (StageGood.gram_first (Fv F v) σ J t).trans hy1.symm
    obtain ⟨h, rfl⟩ := GlobalTheory.T.witt_extension_artinian_ring F E σ hCM (M + 1) _ hND (Fv F v) 1 _ y hg
      (by rw [hg]; exact hy2)
    rw [hΨ h]
    haveI := hB n M
    haveI := hB (n + 1) (M + 1)
    have hS : MeasurableSet {X : Fin n → Fin M → Fv F v ⊗[F] E |
        actW (Fv F v) σ _ h (consTup X) ∈ latV b v} :=
      (continuous_act_consTup (Fv F v) hring σ _ h).measurable (hlat _ _)
    have hfun : (fun X : Fin n → Fin M → Fv F v ⊗[F] E =>
        (latV b v).indicator (1 : (Fin (n + 1) → Fin (M + 1) → Fv F v ⊗[F] E) → ℝ≥0∞) (actW (Fv F v) σ _ h (consTup X))) =
        {X | actW (Fv F v) σ _ h (consTup X) ∈ latV b v}.indicator 1 := by
      funext X
      rfl
    rw [hfun, lintegral_indicator_one hS, hv _ _ m' (hH.2.1 n M) (hH.2.2 n) hm' h]
  rw [← lintegral_indicator_one (hlat _ _), hint, lintegral_congr_ae hae,
    lintegral_indicator_const (hlat _ _)]

end GlobalTheory.CompanionTheory.SW.GoodMass
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalDensityBlockOneEventuallyStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_density_block_one_eventually : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ t : F, t ≠ 0 → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 → ∀ (hT' : ∀ a b, σ (blockOne (algebraMap F E t) T b a) = blockOne (algebraMap F E t) T a b) (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ lam : Measure (Fv F v), lam.IsAddHaarMeasure → ∀ m m₁ m', IsGramFib (Fv F v) σ (blockOne (algebraMap F E t) J) (n + 1) (coordW (Fv F v) b lam (n + 1) (M + 1)) (coordHerm (Fv F v) σ b lam (n + 1)) m → IsGramFib (Fv F v) σ (blockOne (algebraMap F E t) J) 1 (coordW (Fv F v) b lam 1 (M + 1)) (coordHerm (Fv F v) σ b lam 1) m₁ → IsGramFib (Fv F v) σ J n (coordW (Fv F v) b lam n M) (coordHerm (Fv F v) σ b lam n) m' → ∀ c : ℝ≥0, (coordK (Fv F v) b lam).map (fun y => inclR (Fv F v) (algebraMap F E t) * y) = c • coordK (Fv F v) b lam → m (hermOf (Fv F v) σ _ hT') (latV b v) = (c : ℝ≥0∞) ^ n * (m' (hermOf (Fv F v) σ T hT) (latV b v) * m₁ (hermScal (Fv F v) σ (algebraMap F (Fv F v) t)) (latV b v)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.GoodMass.good_mass | exact GlobalTheory.CompanionTheory.SW.GoodMass.good_mass | (intros; apply GlobalTheory.CompanionTheory.SW.GoodMass.good_mass <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicUnitaryFiniteSetDecomposition
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicUnitaryFiniteSetDecomposition
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.PureH

theorem map_consTup {K L : Type} [Zero K] [One K] [Zero L] [One L] (f : K → L) (h0 : f 0 = 0)
    (h1 : f 1 = 1) {M n : ℕ} (X : Fin n → Fin M → K) :
    (fun a i => f (consTup X a i)) = consTup (fun a i => f (X a i)) := by
  funext a i
  induction a using Fin.cases with
  | zero =>
    induction i using Fin.cases with
    | zero => simp [consTup, h1]
    | succ i => simp [consTup, h0]
  | succ a =>
    induction i using Fin.cases with
    | zero => simp [consTup, h0]
    | succ i => simp [consTup]

theorem consTup_empty {K : Type} [Zero K] [One K] {M : ℕ} (X : Fin 0 → Fin M → K) :
    (consTup X : Fin (0 + 1) → Fin (M + 1) → K) = fun _ : Fin 1 => Fin.cons 1 (fun _ => 0) := by
  funext a
  induction a using Fin.cases with
  | zero => simp [consTup]
  | succ a => exact a.elim0

section Glob

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem projInf_consTup {M n : ℕ} (X : Fin n → Fin M → AF F ⊗[F] E) :
    projInf (consTup X) = consTup (projInf X) :=
  map_consTup (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) (map_zero _) (map_one _) X

theorem projFin_consTup {M n : ℕ} (X : Fin n → Fin M → AF F ⊗[F] E) :
    projFin (consTup X) = consTup (projFin X) :=
  map_consTup (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)) (map_zero _) (map_one _) X

theorem projV_consTup (v : HeightOneSpectrum (𝓞 F)) {M n : ℕ} (X : Fin n → Fin M → Af F ⊗[F] E) :
    projV v (consTup X) = consTup (projV v X) :=
  map_consTup (Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E)) (map_zero _) (map_one _) X

theorem consTup_mem_latV {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) {M n : ℕ}
    (h0 : ∀ X₀ : Fin 0 → Fin M → Fv F v ⊗[F] E, consTup X₀ ∈ latV b v)
    (X : Fin n → Fin M → Fv F v ⊗[F] E) : consTup X ∈ latV b v ↔ X ∈ latV b v := by
  constructor
  · intro h a i k
    simpa [consTup] using h a.succ i.succ k
  · intro h a i k
    induction a using Fin.cases with
    | zero => simpa [consTup] using h0 (fun a => a.elim0) 0 i k
    | succ a =>
      induction i using Fin.cases with
      | zero => simp [consTup, zero_mem]
      | succ i => simpa [consTup] using h a i k

end Glob

end GlobalTheory.CompanionTheory.SW.PureH

namespace GlobalTheory.CompanionTheory.SW.PureH

section Core

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  [DecidableEq (HeightOneSpectrum (𝓞 F))]

theorem prod_union_split {ι : Type} [DecidableEq ι] (S Sh : Finset ι) (A B : ι → ℝ≥0∞) (P : ι → Prop)
    [DecidablePred P] (hS : ∀ v, P v ↔ v ∈ S) :
    ∏ v ∈ S ∪ Sh, (if P v then A v else B v) = (∏ v ∈ S, A v) * ∏ v ∈ Sh \ S, B v := by
  rw [← Finset.union_sdiff_self_eq_union, Finset.prod_union Finset.disjoint_sdiff]
  congr 1
  · exact Finset.prod_congr rfl fun v hv => if_pos ((hS v).2 hv)
  · exact Finset.prod_congr rfl fun v hv => if_neg fun h => (Finset.mem_sdiff.1 hv).2 ((hS v).1 h)

variable {d M : ℕ} (b : Module.Basis (Fin d) F E) (σ : E →ₐ[F] E)
  (Jp : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (h : HA (AF F) σ Jp) (ginf : HA (Ainf F) σ Jp)
  (g : ∀ v : HeightOneSpectrum (𝓞 F), HA (Fv F v) σ Jp) (S Sh : Finset (HeightOneSpectrum (𝓞 F)))


include b in
theorem pureL_act
    (hinf : ∀ (n : ℕ) (X : Fin n → Fin (M + 1) → AF F ⊗[F] E),
      projInf (actW (AF F) σ Jp h X) = actW (Ainf F) σ Jp ginf (projInf X))
    (hfin : ∀ (n : ℕ) (X : Fin n → Fin (M + 1) → AF F ⊗[F] E) (v : HeightOneSpectrum (𝓞 F)),
      projV v (projFin (actW (AF F) σ Jp h X)) = actW (Fv F v) σ Jp (g v) (projV v (projFin X)))
    (hSh : ∀ v, v ∉ Sh → ∀ (n : ℕ) (X : Fin n → Fin (M + 1) → Fv F v ⊗[F] E),
      actW (Fv F v) σ Jp (g v) X ∈ latV b v ↔ X ∈ latV b v)
    (hS : ∀ v, v ∉ S → ∀ X₀ : Fin 0 → Fin M → Fv F v ⊗[F] E, consTup X₀ ∈ latV b v)
    {n : ℕ} (φinf : (Fin (n + 1) → Fin (M + 1) → Ainf F ⊗[F] E) → ℝ≥0∞)
    (φ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin (n + 1) → Fin (M + 1) → Fv F v ⊗[F] E) → ℝ≥0∞)
    (X : Fin n → Fin M → AF F ⊗[F] E) :
    pureL b S φinf φ (actW (AF F) σ Jp h (consTup X)) =
      pureL b (S ∪ Sh) (fun Y => φinf (actW (Ainf F) σ Jp ginf (consTup Y)))
        (fun v Y => if v ∈ S then φ v (actW (Fv F v) σ Jp (g v) (consTup Y))
          else (latV b v).indicator 1 (actW (Fv F v) σ Jp (g v) (consTup Y))) X := by
  have hP : projInf (actW (AF F) σ Jp h (consTup X)) =
      actW (Ainf F) σ Jp ginf (consTup (projInf X)) := by
    rw [hinf, projInf_consTup]
  have hV : ∀ v, projV v (projFin (actW (AF F) σ Jp h (consTup X))) =
      actW (Fv F v) σ Jp (g v) (consTup (projV v (projFin X))) := fun v => by
    rw [hfin, projFin_consTup, projV_consTup]
  have key : ∀ v, v ∉ S → v ∉ Sh →
      (actW (Fv F v) σ Jp (g v) (consTup (projV v (projFin X))) ∈ latV b v ↔
        projV v (projFin X) ∈ latV b v) := fun v h1 h2 =>
    (hSh v h2 _ _).trans (consTup_mem_latV b v (hS v h1) _)
  have hprod := prod_union_split S Sh
    (fun v => φ v (actW (Fv F v) σ Jp (g v) (consTup (projV v (projFin X)))))
    (fun v => ((latV b v).indicator 1 (actW (Fv F v) σ Jp (g v) (consTup (projV v (projFin X)))) : ℝ≥0∞))
    (fun v => v ∈ S) (fun _ => Iff.rfl)
  unfold pureL
  by_cases hX : X ∈ intOff b (S ∪ Sh)
  · rw [Set.indicator_of_mem hX, hprod]
    by_cases hA : ∀ v ∈ Sh \ S, actW (Fv F v) σ Jp (g v) (consTup (projV v (projFin X))) ∈ latV b v
    · have hY : actW (AF F) σ Jp h (consTup X) ∈ intOff b S := by
        intro v hv
        rw [hV]
        by_cases hvh : v ∈ Sh
        · exact hA v (Finset.mem_sdiff.2 ⟨hvh, hv⟩)
        · exact (key v hv hvh).2 (hX v (by simp [hv, hvh]))
      rw [Set.indicator_of_mem hY, hP, Finset.prod_eq_one
        (f := fun v => ((latV b v).indicator 1
          (actW (Fv F v) σ Jp (g v) (consTup (projV v (projFin X)))) : ℝ≥0∞))
        (fun v hv => by simp [Set.indicator_of_mem (hA v hv)])]
      simp only [mul_one, hV]
    · push Not at hA
      obtain ⟨v, hv, hvl⟩ := hA
      have hY : actW (AF F) σ Jp h (consTup X) ∉ intOff b S := by
        intro hm
        have := hm v (Finset.mem_sdiff.1 hv).2
        rw [hV] at this
        exact hvl this
      rw [Set.indicator_of_notMem hY, Finset.prod_eq_zero hv (by simp [Set.indicator_of_notMem hvl])]
      simp
  · have hY : actW (AF F) σ Jp h (consTup X) ∉ intOff b S := by
      intro hm
      apply hX
      intro v hv
      have hv' : v ∉ S ∧ v ∉ Sh := by simpa using hv
      have := hm v hv'.1
      rw [hV] at this
      exact (key v hv'.1 hv'.2).1 this
    rw [Set.indicator_of_notMem hX, Set.indicator_of_notMem hY]


include b in
theorem pureL_act_vec
    (hinf : ∀ (n : ℕ) (X : Fin n → Fin (M + 1) → AF F ⊗[F] E),
      projInf (actW (AF F) σ Jp h X) = actW (Ainf F) σ Jp ginf (projInf X))
    (hfin : ∀ (n : ℕ) (X : Fin n → Fin (M + 1) → AF F ⊗[F] E) (v : HeightOneSpectrum (𝓞 F)),
      projV v (projFin (actW (AF F) σ Jp h X)) = actW (Fv F v) σ Jp (g v) (projV v (projFin X)))
    (hSh : ∀ v, v ∉ Sh → ∀ (n : ℕ) (X : Fin n → Fin (M + 1) → Fv F v ⊗[F] E),
      actW (Fv F v) σ Jp (g v) X ∈ latV b v ↔ X ∈ latV b v)
    (hS : ∀ v, v ∉ S → ∀ X₀ : Fin 0 → Fin M → Fv F v ⊗[F] E, consTup X₀ ∈ latV b v)
    (Ψinf : (Fin 1 → Fin (M + 1) → Ainf F ⊗[F] E) → ℝ≥0∞)
    (Ψ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin 1 → Fin (M + 1) → Fv F v ⊗[F] E) → ℝ≥0∞) :
    pureL b S Ψinf Ψ (actW (AF F) σ Jp h (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0))) =
      (Ψinf (actW (Ainf F) σ Jp ginf (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0))) *
        ∏ v ∈ S, Ψ v (actW (Fv F v) σ Jp (g v) (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0)))) *
        ∏ v ∈ Sh \ S, (latV b v).indicator 1
          (actW (Fv F v) σ Jp (g v) (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0))) := by
  let X₀ : Fin 0 → Fin M → AF F ⊗[F] E := fun a => a.elim0
  have h1 := pureL_act (n := 0) b σ Jp h ginf g S Sh hinf hfin hSh hS Ψinf Ψ X₀
  have hmem : X₀ ∈ intOff b (S ∪ Sh) := fun v _ a => a.elim0
  unfold pureL at h1
  rw [Set.indicator_of_mem hmem] at h1
  rw [consTup_empty] at h1
  simp only [consTup_empty] at h1
  rw [prod_union_split S Sh _ _ (fun v => v ∈ S) (fun _ => Iff.rfl)] at h1
  rw [mul_assoc]
  unfold pureL
  exact h1

end Core

theorem pure_h : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [DecidableEq (HeightOneSpectrum (𝓞 F))] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ t : F, t ≠ 0 → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∃ S₁ : Finset (HeightOneSpectrum (𝓞 F)), ∀ h : HA (AF F) σ (blockOne (algebraMap F E t) J), ∃ (ginf : HA (Ainf F) σ (blockOne (algebraMap F E t) J)) (g : ∀ v : HeightOneSpectrum (𝓞 F), HA (Fv F v) σ (blockOne (algebraMap F E t) J)) (Sh : Finset (HeightOneSpectrum (𝓞 F))), ∀ S, S₁ ⊆ S → (∀ (n : ℕ) (φinf : (Fin (n + 1) → Fin (M + 1) → Ainf F ⊗[F] E) → ℝ≥0∞) (φ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin (n + 1) → Fin (M + 1) → Fv F v ⊗[F] E) → ℝ≥0∞) (X : Fin n → Fin M → AF F ⊗[F] E), pureL b S φinf φ (actW (AF F) σ _ h (consTup X)) = pureL b (S ∪ Sh) (fun Y => φinf (actW (Ainf F) σ _ ginf (consTup Y))) (fun v Y => if v ∈ S then φ v (actW (Fv F v) σ _ (g v) (consTup Y)) else (latV b v).indicator 1 (actW (Fv F v) σ _ (g v) (consTup Y))) X) ∧ ∀ (Ψinf : (Fin 1 → Fin (M + 1) → Ainf F ⊗[F] E) → ℝ≥0∞) (Ψ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin 1 → Fin (M + 1) → Fv F v ⊗[F] E) → ℝ≥0∞), pureL b S Ψinf Ψ (actW (AF F) σ _ h (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0))) = (Ψinf (actW (Ainf F) σ _ ginf (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0))) * ∏ v ∈ S, Ψ v (actW (Fv F v) σ _ (g v) (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0)))) * ∏ v ∈ Sh \ S, (latV b v).indicator 1 (actW (Fv F v) σ _ (g v) (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0))) := by
  intro F E _ _ _ _ _ _ σ hCM M J hJ t ht d b
  have hba := GlobalTheory.CompanionTheory.SW.BlockAlg.block_alg F E σ hCM M J t
  have hJ' : IsHermND σ (blockOne (algebraMap F E t) J) :=
    ⟨hba.2.1 hJ.1, by
      rw [hba.1]
      exact mul_ne_zero ((map_ne_zero _).2 ht) hJ.2⟩
  obtain ⟨pinf, p, hcomp, hlat, -⟩ := GlobalTheory.CompanionTheory.SW.HProj.components F E σ hCM (M + 1) _ hJ'
  have hcons := (GlobalTheory.CompanionTheory.SW.LatRat.latV_rational F E σ hCM d b 0 M).2.2
  let S₁ : Finset (HeightOneSpectrum (𝓞 F)) := (Filter.eventually_cofinite.1 hcons).toFinset
  refine ⟨S₁, fun h => ?_⟩
  have hlat' := hlat d b h
  let Sh : Finset (HeightOneSpectrum (𝓞 F)) := (Filter.eventually_cofinite.1 hlat').toFinset
  have hSh : ∀ v, v ∉ Sh → ∀ (n : ℕ) (X : Fin n → Fin (M + 1) → Fv F v ⊗[F] E),
      actW (Fv F v) σ _ (p v h) X ∈ latV b v ↔ X ∈ latV b v := fun v hv => by
    simpa [Sh] using hv
  refine ⟨pinf h, fun v => p v h, Sh, fun S hS => ?_⟩
  have hS' : ∀ v, v ∉ S → ∀ X₀ : Fin 0 → Fin M → Fv F v ⊗[F] E, consTup X₀ ∈ latV b v := by
    intro v hv X₀
    have hv₁ : v ∉ S₁ := fun hm => hv (hS hm)
    have : ∀ X : Fin 0 → Fin M → Fv F v ⊗[F] E, consTup X ∈ latV b v ↔ X ∈ latV b v := by
      simpa [S₁] using hv₁
    exact (this X₀).2 fun a => a.elim0
  have hinf := fun (n : ℕ) (X : Fin n → Fin (M + 1) → AF F ⊗[F] E) => (hcomp n h X).1
  have hfin := fun (n : ℕ) (X : Fin n → Fin (M + 1) → AF F ⊗[F] E) (v : HeightOneSpectrum (𝓞 F)) =>
    (hcomp n h X).2 v
  exact ⟨fun n φinf φ X => pureL_act b σ _ h (pinf h) (fun v => p v h) S Sh hinf hfin hSh hS' φinf φ X,
    fun Ψinf Ψ => pureL_act_vec b σ _ h (pinf h) (fun v => p v h) S Sh hinf hfin hSh hS' Ψinf Ψ⟩

end GlobalTheory.CompanionTheory.SW.PureH
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicUnitaryFiniteSetDecompositionStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_unitary_finite_set_decomposition : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [DecidableEq (HeightOneSpectrum (𝓞 F))] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ t : F, t ≠ 0 → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∃ S₁ : Finset (HeightOneSpectrum (𝓞 F)), ∀ h : HA (AF F) σ (blockOne (algebraMap F E t) J), ∃ (ginf : HA (Ainf F) σ (blockOne (algebraMap F E t) J)) (g : ∀ v : HeightOneSpectrum (𝓞 F), HA (Fv F v) σ (blockOne (algebraMap F E t) J)) (Sh : Finset (HeightOneSpectrum (𝓞 F))), ∀ S, S₁ ⊆ S → (∀ (n : ℕ) (φinf : (Fin (n + 1) → Fin (M + 1) → Ainf F ⊗[F] E) → ℝ≥0∞) (φ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin (n + 1) → Fin (M + 1) → Fv F v ⊗[F] E) → ℝ≥0∞) (X : Fin n → Fin M → AF F ⊗[F] E), pureL b S φinf φ (actW (AF F) σ _ h (consTup X)) = pureL b (S ∪ Sh) (fun Y => φinf (actW (Ainf F) σ _ ginf (consTup Y))) (fun v Y => if v ∈ S then φ v (actW (Fv F v) σ _ (g v) (consTup Y)) else (latV b v).indicator 1 (actW (Fv F v) σ _ (g v) (consTup Y))) X) ∧ ∀ (Ψinf : (Fin 1 → Fin (M + 1) → Ainf F ⊗[F] E) → ℝ≥0∞) (Ψ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin 1 → Fin (M + 1) → Fv F v ⊗[F] E) → ℝ≥0∞), pureL b S Ψinf Ψ (actW (AF F) σ _ h (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0))) = (Ψinf (actW (Ainf F) σ _ ginf (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0))) * ∏ v ∈ S, Ψ v (actW (Fv F v) σ _ (g v) (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0)))) * ∏ v ∈ Sh \ S, (latV b v).indicator 1 (actW (Fv F v) σ _ (g v) (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0))) := by
  first | exact @GlobalTheory.CompanionTheory.SW.PureH.pure_h | exact GlobalTheory.CompanionTheory.SW.PureH.pure_h | (intros; apply GlobalTheory.CompanionTheory.SW.PureH.pure_h <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitaryActionConsTupleMeasurable
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitaryActionConsTupleMeasurable
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.Fact

theorem continuous_consTup {K : Type} [Zero K] [One K] [TopologicalSpace K] (n M : ℕ) :
    Continuous (fun X : Fin n → Fin M → K => (consTup X : Fin (n + 1) → Fin (M + 1) → K)) := by
  refine continuous_pi fun a => continuous_pi fun i => ?_
  refine Fin.cases ?_ (fun a => ?_) a
  · exact continuous_const
  · refine Fin.cases ?_ (fun i => ?_) i
    · exact continuous_const
    · exact (continuous_apply i).comp (continuous_apply a)

theorem measurable_actW_consTup : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (g : HA R σ J), Measurable (fun X : Fin n → Fin M → R ⊗[F] E => actW R σ J g (consTup X)) := by
  intro F E _ _ _ _ _ σ hCM R _ _ _ _ _ hR n M J g
  obtain ⟨h1, h2, h3, h4, -⟩ := hR
  have hk := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM R
  haveI : IsTopologicalRing (R ⊗[F] E) := hk.1
  haveI : BorelSpace (Fin n → Fin M → R ⊗[F] E) := hk.2.2.2.2.2.2.2.1 n M
  haveI : BorelSpace (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) := hk.2.2.2.2.2.2.2.1 (n + 1) (M + 1)
  have hc : Continuous (fun X : Fin n → Fin M → R ⊗[F] E => actW R σ J g (consTup X)) := by
    refine continuous_pi fun a => continuous_pi fun i => ?_
    simp only [actW, actTup, Matrix.mulVec, dotProduct]
    refine continuous_finsetSum _ fun j _ => continuous_const.mul ?_
    exact (continuous_apply j).comp ((continuous_apply a).comp (continuous_consTup n M))
  exact hc.measurable

end GlobalTheory.CompanionTheory.SW.Fact
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitaryActionConsTupleMeasurableStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_action_cons_tuple_measurable : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (g : HA R σ J), Measurable (fun X : Fin n → Fin M → R ⊗[F] E => actW R σ J g (consTup X)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.Fact.measurable_actW_consTup | exact GlobalTheory.CompanionTheory.SW.Fact.measurable_actW_consTup | (intros; apply GlobalTheory.CompanionTheory.SW.Fact.measurable_actW_consTup <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureAddRankOneBlock
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.Step

theorem of_cofinite {α : Type} {p : α → Prop} (h : ∀ᶠ v in Filter.cofinite, p v) {S : Finset α}
    (hS : (Filter.eventually_cofinite.1 h).toFinset ⊆ S) {v : α} (hv : v ∉ S) : p v := by
  by_contra hx
  exact hv (hS (by simpa using hx))

theorem lattice_measurable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E) (n M : ℕ)
    (v : HeightOneSpectrum (𝓞 F)) : MeasurableSet (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := GlobalTheory.T.completion_is_local_ring F v
  haveI := (GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (Fv F v)).2.2.2.2.2.2.2.1 n M
  exact (((GlobalTheory.T.adelic_tuple_projections F E σ hCM d b n M).2.2.2.1 v).2).measurableSet

theorem theta_hypothesis : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ t : F, t ≠ 0 → ∀ (n d : ℕ) (b : Module.Basis (Fin d) F E) (I : Measure (Fin n → Fin M → AF F ⊗[F] E)) (minf : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (m : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)), IsEulerProd b I 1 minf m → ∃ S₂ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S, S₂ ⊆ S → ∀ (φinf : (Fin (n + 1) → Fin (M + 1) → Ainf F ⊗[F] E) → ℝ≥0∞) (φ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin (n + 1) → Fin (M + 1) → Fv F v ⊗[F] E) → ℝ≥0∞) (Ψinf : (Fin 1 → Fin (M + 1) → Ainf F ⊗[F] E) → ℝ≥0∞) (Ψ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin 1 → Fin (M + 1) → Fv F v ⊗[F] E) → ℝ≥0∞), Measurable φinf → (∀ v, Measurable (φ v)) → (∀ g : HA (Ainf F) σ (blockOne (algebraMap F E t) J), Ψinf (actW (Ainf F) σ _ g (fun _ => Fin.cons 1 (fun _ => 0))) = ∫⁻ X, φinf (actW (Ainf F) σ _ g (consTup X)) ∂minf) → (∀ v, ∀ g : HA (Fv F v) σ (blockOne (algebraMap F E t) J), Ψ v (actW (Fv F v) σ _ g (fun _ => Fin.cons 1 (fun _ => 0))) = ∫⁻ X, φ v (actW (Fv F v) σ _ g (consTup X)) ∂(m v)) → (∀ v, v ∉ S → ∀ g : HA (Fv F v) σ (blockOne (algebraMap F E t) J), m v {X | actW (Fv F v) σ _ g (consTup X) ∈ latV b v} = (latV b v).indicator (fun _ => m v (latV b v)) (actW (Fv F v) σ _ g (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0)))) → ∀ h : HA (AF F) σ (blockOne (algebraMap F E t) J), ENNReal.ofReal (∏' v : {v // v ∉ S}, (m v.1 (latV b v.1)).toReal) * pureL b S Ψinf Ψ (actW (AF F) σ _ h (fun _ => Fin.cons 1 (fun _ => 0))) = ∫⁻ X, pureL b S φinf φ (actW (AF F) σ _ h (consTup X)) ∂I := by
  intro F E _ _ _ _ _ σ hCM M J hJ t ht n d b I minf m hE
  classical
  have hLi : IsLocR (Ainf F) := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hCM.1
  have hLv : ∀ v, IsLocR (Fv F v) := GlobalTheory.T.completion_is_local_ring F
  haveI hBi : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI hBv : ∀ v, BorelSpace (Fv F v) := fun v => ⟨rfl⟩
  obtain ⟨hfin, hsum, S₀, hS₀⟩ := hE
  obtain ⟨S₁, hS₁⟩ := GlobalTheory.T.adelic_unitary_finite_set_decomposition F E σ hCM M J hJ t ht d b
  refine ⟨S₀ ∪ S₁, fun S hS φinf φ Ψinf Ψ hφinf hφ hΨinf hΨ hG h => ?_⟩
  have hS0 : S₀ ⊆ S := fun x hx => hS (by simp [hx])
  have hS1 : S₁ ⊆ S := fun x hx => hS (by simp [hx])
  obtain ⟨ginf, g, Sh, hh⟩ := hS₁ h
  obtain ⟨hi, hii⟩ := hh S hS1
  have hmi : Measurable fun Y : Fin n → Fin M → Ainf F ⊗[F] E =>
      actW (Ainf F) σ _ ginf (consTup Y) := GlobalTheory.T.unitary_action_cons_tuple_measurable F E σ hCM (Ainf F) hLi n M _ ginf
  have hmv : ∀ v, Measurable fun Y : Fin n → Fin M → Fv F v ⊗[F] E =>
      actW (Fv F v) σ _ (g v) (consTup Y) := fun v => GlobalTheory.T.unitary_action_cons_tuple_measurable F E σ hCM (Fv F v) (hLv v) n M _ (g v)
  have hlatm : ∀ v, MeasurableSet (latV b v : Set (Fin (n + 1) → Fin (M + 1) → Fv F v ⊗[F] E)) := fun v => lattice_measurable σ hCM b (n + 1) (M + 1) v
  simp_rw [hi]
  have hmψ : ∀ v, Measurable (fun Y : Fin n → Fin M → Fv F v ⊗[F] E => if v ∈ S then φ v (actW (Fv F v) σ _ (g v) (consTup Y)) else (latV b v).indicator 1 (actW (Fv F v) σ _ (g v) (consTup Y))) := fun v => by
    by_cases hv : v ∈ S
    · simp only [hv, if_true]; exact (hφ v).comp (hmv v)
    · simp only [hv, if_false]; exact (measurable_one.indicator (hlatm v)).comp (hmv v)
  have hsplit : ∏ v ∈ S ∪ Sh, ∫⁻ X, (if v ∈ S then φ v (actW (Fv F v) σ _ (g v) (consTup X)) else (latV b v).indicator 1 (actW (Fv F v) σ _ (g v) (consTup X))) ∂(m v) =
      (∏ v ∈ S, Ψ v (actW (Fv F v) σ _ (g v) (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0)))) *
        ((∏ v ∈ Sh \ S, (latV b v).indicator 1 (actW (Fv F v) σ _ (g v) (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0)))) * ∏ v ∈ Sh \ S, m v (latV b v)) := by
    rw [Finset.union_comm, ← Finset.sdiff_union_self_eq_union, Finset.prod_union Finset.sdiff_disjoint, mul_comm, ← Finset.prod_mul_distrib]
    congr 1
    · refine Finset.prod_congr rfl fun v hv => ?_
      simp only [hv, if_true]; exact (hΨ v (g v)).symm
    · refine Finset.prod_congr rfl fun v hv => ?_
      have hvS : v ∉ S := (Finset.mem_sdiff.1 hv).2
      simp only [hvS, if_false]
      have e1 : ∫⁻ X, (latV b v).indicator 1 (actW (Fv F v) σ _ (g v) (consTup X)) ∂(m v) =
          m v {X | actW (Fv F v) σ _ (g v) (consTup X) ∈ latV b v} := by
        have : (fun X : Fin n → Fin M → Fv F v ⊗[F] E => (latV b v).indicator (1 : (Fin (n + 1) → Fin (M + 1) → Fv F v ⊗[F] E) → ℝ≥0∞) (actW (Fv F v) σ _ (g v) (consTup X))) =
            {X | actW (Fv F v) σ _ (g v) (consTup X) ∈ latV b v}.indicator 1 := by
          funext X; simp [Set.indicator]
        rw [this]; exact lintegral_indicator_one ((hmv v) (hlatm v))
      rw [e1, hG v hvS (g v)]
      simp [Set.indicator]
  have hmφ : Measurable (fun Y : Fin n → Fin M → Ainf F ⊗[F] E => φinf (actW (Ainf F) σ _ ginf (consTup Y))) := hφinf.comp hmi
  have htail := GlobalTheory.T.tprod_complement_split_finset (HeightOneSpectrum (𝓞 F)) (fun v => (m v (latV b v)).toReal) S (S ∪ Sh) hsum Finset.subset_union_left
  rw [Finset.union_sdiff_left] at htail
  have hτ : ENNReal.ofReal (∏' v : {v // v ∉ S}, (m v.1 (latV b v.1)).toReal) = (∏ v ∈ Sh \ S, m v (latV b v)) *
      ENNReal.ofReal (∏' v : {v // v ∉ S ∪ Sh}, (m v.1 (latV b v.1)).toReal) := by
    rw [htail, ENNReal.ofReal_mul (Finset.prod_nonneg fun _ _ => ENNReal.toReal_nonneg),
      ENNReal.ofReal_prod_of_nonneg (fun _ _ => ENNReal.toReal_nonneg)]
    congr 1
    exact Finset.prod_congr rfl fun v _ => ENNReal.ofReal_toReal (hfin v).ne
  rw [hS₀ (S ∪ Sh) (hS0.trans Finset.subset_union_left) _ _ hmφ hmψ, hii, hsplit, hτ, hΨinf ginf]
  simp only [ENNReal.coe_one, one_mul]
  ring

theorem loc_families {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J)
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R]
    (hR : IsLocR R) {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R)
    (hlam : lam.IsAddHaarMeasure) (n : ℕ) :
    ∃ m, IsGramFib R σ J n (coordW R b lam n M) (coordHerm R σ b lam n) m := by
  have hR' := hR
  obtain ⟨h1, h2, h3, h4, -⟩ := hR'
  have hh := GlobalTheory.T.coordinate_haar_measure F E σ hCM R d b lam hlam
  exact GlobalTheory.T.exists_gram_fiber_measures F E σ hCM M J hJ R hR n _ _ (hh.2.1 n M) (hh.2.2 n)

theorem blockOne_step : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ t : F, t ≠ 0 → ∀ n : ℕ, n + 2 ≤ M → ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 → ∀ (hT' : ∀ a b, σ (blockOne (algebraMap F E t) T b a) = blockOne (algebraMap F E t) T a b), SWMeas σ J T hT → SWMeas σ (blockOne (algebraMap F E t) J) (blockOne (algebraMap F E t) T) hT' := by
  intro F E _ _ _ _ _ σ hCM M J hJ t ht n hn T hT hdet hT' hSW d b laminf lam hinf hlam μ 𝓕 hμ h𝓕 minf m hminf hm
  classical
  have hLi : IsLocR (Ainf F) := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hCM.1
  have hLv : ∀ v, IsLocR (Fv F v) := GlobalTheory.T.completion_is_local_ring F
  haveI hBi : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI hBv : ∀ v, BorelSpace (Fv F v) := fun v => ⟨rfl⟩
  have hta : algebraMap F E t ≠ 0 := by simpa using ht
  obtain ⟨hdetb, hhermb, -, -⟩ := GlobalTheory.T.block_one_det_hermitian_gram F E σ hCM M J t
  have hJ' : IsHermND σ (blockOne (algebraMap F E t) J) :=
    ⟨hhermb hJ.1, by rw [hdetb]; exact mul_ne_zero hta hJ.2⟩
  have hdet' : (blockOne (algebraMap F E t) T).det ≠ 0 := by
    rw [(GlobalTheory.T.block_one_det_hermitian_gram F E σ hCM n T t).1]; exact mul_ne_zero hta hdet

  obtain ⟨m₁inf, hm₁inf⟩ := loc_families σ hCM _ hJ' (Ainf F) hLi b laminf hinf.1 1
  obtain ⟨m'inf, hm'inf⟩ := loc_families σ hCM J hJ (Ainf F) hLi b laminf hinf.1 n
  choose m₁ hm₁ using fun v => loc_families σ hCM _ hJ' (Fv F v) (hLv v) b (lam v) (hlam v).1 1
  choose m' hm' using fun v => loc_families σ hCM J hJ (Fv F v) (hLv v) b (lam v) (hlam v).1 n
  obtain ⟨⟨μ₁, hμ₁⟩, hFV⟩ := GlobalTheory.T.unitary_group_finite_volume F E σ hCM M J hJ
  obtain ⟨⟨𝓕₁, h𝓕₁⟩, -⟩ := hFV μ₁ hμ₁

  obtain ⟨cinf, c, hc, hcinf, hcv⟩ := GlobalTheory.T.scalar_multiplication_euler_product F E σ hCM (algebraMap F E t) hta
  have hKi : (coordK (Ainf F) b laminf).map (fun y => inclR (Ainf F) (algebraMap F E t) * y) =
      cinf • coordK (Ainf F) b laminf := by
    obtain ⟨h1, h2, h3, h4, -⟩ := hLi
    exact hcinf _ (GlobalTheory.T.coordinate_haar_measure F E σ hCM (Ainf F) d b laminf hinf.1).1
  have hKv : ∀ v, (coordK (Fv F v) b (lam v)).map (fun y => inclR (Fv F v) (algebraMap F E t) * y) =
      c v • coordK (Fv F v) b (lam v) := fun v => by
    obtain ⟨h1, h2, h3, h4, -⟩ := hLv v
    exact hcv v _ (GlobalTheory.T.coordinate_haar_measure F E σ hCM (Fv F v) d b (lam v) (hlam v).1).1
  obtain ⟨-, -, -, -, -, -, -, S₃, hS₃⟩ := GlobalTheory.T.unit_product_closure_properties F cinf 1 c (fun _ => 1) hc ⟨by simp, by simp⟩

  have hE' := hSW d b laminf lam hinf hlam μ₁ 𝓕₁ hμ₁ h𝓕₁ m'inf (fun v => m' v) hm'inf hm'
  let T1 : Matrix (Fin 1) (Fin 1) E := fun _ _ => algebraMap F E t
  have hT1 : ∀ a b, σ (T1 b a) = T1 a b := fun a b => by simp [T1]
  have hdet1 : T1.det ≠ 0 := by rw [Matrix.det_fin_one]; exact hta
  have hE₁ := GlobalTheory.T.siegel_weil_measure_rank_one F E σ hCM (M + 1) _ hJ' (by omega) T1 hT1 hdet1 d b laminf lam hinf hlam μ 𝓕 hμ h𝓕
    m₁inf m₁ hm₁inf hm₁
  obtain ⟨β, hβ1, -, hβ2⟩ := GlobalTheory.T.hermitian_one_by_one_is_scalar F E σ hCM T1 hT1
  have hβ : β = t := (algebraMap F E).injective (congrFun (congrFun hβ1 0) 0).symm
  rw [hβ] at hβ2
  simp only [hβ2] at hE₁
  obtain ⟨-, hsum₁, S₁, hS₁⟩ := hE₁
  have hsum' := hE'.2.1
  have hgood := GlobalTheory.T.euler_product_local_densities_converges F E σ hCM (M + 1) _ hJ' (n + 1) (Or.inr (by omega)) _ hT' hdet' d b lam hlam m hm
  refine ⟨hgood.1, hgood.2, ?_⟩
  obtain ⟨S₂, hS₂⟩ := theta_hypothesis F E σ hCM M J hJ t ht n d b _ _ _ hE'
  have hG := GlobalTheory.T.local_density_block_one_eventually F E σ hCM M J hJ t ht n T hT hdet hT' d b
  have hSG := GlobalTheory.T.local_measures_orthogonal_sum_almost_all_places F E σ hCM M J hJ t ht n T hT hdet d b
  refine ⟨S₁ ∪ S₂ ∪ S₃ ∪ (Filter.eventually_cofinite.1 hG).toFinset ∪ (Filter.eventually_cofinite.1 hSG).toFinset,
    fun S hS φinf φ hφinf hφ => ?_⟩
  have hS1 : S₁ ⊆ S := fun x hx => hS (by simp [hx])
  have hS2 : S₂ ⊆ S := fun x hx => hS (by simp [hx])
  have hS3 : S₃ ⊆ S := fun x hx => hS (by simp [hx])
  have hS4 : (Filter.eventually_cofinite.1 hG).toFinset ⊆ S := fun x hx => hS (by
    simp only [Finset.mem_union]; exact Or.inl (Or.inr hx))
  have hS5 : (Filter.eventually_cofinite.1 hSG).toFinset ⊆ S := fun x hx => hS (by
    simp only [Finset.mem_union]; exact Or.inr hx)
  obtain ⟨hc1, hc2⟩ := hS₃ S hS3
  obtain ⟨Ψinf, hΨinfm, hΨinf1, hΨinf2⟩ := GlobalTheory.T.local_density_block_one_product F E σ hCM M J hJ t ht n T hT hdet hT' (Ainf F) hLi d b
    laminf hinf.1 minf m₁inf m'inf hminf hm₁inf hm'inf cinf hKi φinf hφinf
  choose Ψ hΨm hΨ1 hΨ2 using fun v => GlobalTheory.T.local_density_block_one_product F E σ hCM M J hJ t ht n T hT hdet hT' (Fv F v) (hLv v) d b
    (lam v) (hlam v).1 (m v) (m₁ v) (m' v) (hm v) (hm₁ v) (hm' v) (c v) (hKv v) (φ v) (hφ v)
  have hHv : ∀ v, (coordW (Fv F v) b (lam v) n M).IsAddHaarMeasure ∧ (coordHerm (Fv F v) σ b (lam v) n).IsAddHaarMeasure := fun v => by
    obtain ⟨h1, h2, h3, h4, -⟩ := hLv v
    have hh := GlobalTheory.T.coordinate_haar_measure F E σ hCM (Fv F v) d b (lam v) (hlam v).1
    exact ⟨hh.2.1 n M, hh.2.2 n⟩
  have hHyp := hS₂ S hS2 φinf φ Ψinf Ψ hφinf hφ hΨinf1 hΨ1 (fun v hv g =>
    of_cofinite hSG hS5 hv _ _ (m' v) (hHv v).1 (hHv v).2 (hm' v) g)
  set τ' := ENNReal.ofReal (∏' v : {v // v ∉ S}, (m' v.1 (hermOf (Fv F v.1) σ T hT) (latV b v.1)).toReal) with hτ'
  have hPm : Measurable (pureL b S Ψinf Ψ) := GlobalTheory.T.pure_adelic_function_measurable F E σ hCM d b 1 (M + 1) S Ψinf Ψ hΨinfm hΨm
  have hth := GlobalTheory.T.lintegral_thetaMeas_block_one_eq_rank_one F E σ hCM M J hJ t ht n T μ 𝓕 hμ h𝓕 μ₁ 𝓕₁ hμ₁ h𝓕₁ (pureL b S φinf φ)
    (fun y => τ' * pureL b S Ψinf Ψ y) (GlobalTheory.T.pure_adelic_function_measurable F E σ hCM d b (n + 1) (M + 1) S φinf φ hφinf hφ)
    (hPm.const_mul τ') hHyp
  have hone := hS₁ S hS1 Ψinf Ψ hΨinfm hΨm
  rw [hth, lintegral_const_mul _ hPm]
  have hone' : ∫⁻ X, pureL b S Ψinf Ψ X ∂(thetaMeas σ _ μ 𝓕 {y : Fin 1 → Fin (M + 1) → E | gramE σ (blockOne (algebraMap F E t) J) y = fun _ _ => algebraMap F E t}) = _ := hone
  rw [hone']
  have hprod : (∫⁻ X, φinf X ∂(minf (hermOf (Ainf F) σ _ hT'))) * ∏ v ∈ S, ∫⁻ X, φ v X ∂(m v (hermOf (Fv F v) σ _ hT')) =
      (∫⁻ y, Ψinf y ∂(m₁inf (hermScal (Ainf F) σ (algebraMap F (Ainf F) t)))) *
        ∏ v ∈ S, ∫⁻ y, Ψ v y ∂(m₁ v (hermScal (Fv F v) σ (algebraMap F (Fv F v) t))) := by
    have hone2 : (cinf : ℝ≥0∞) * ∏ v ∈ S, (c v : ℝ≥0∞) = 1 := by exact_mod_cast hc2
    rw [hΨinf2, Finset.prod_congr rfl (fun v _ => hΨ2 v), Finset.prod_mul_distrib, Finset.prod_pow]
    calc _ = ((cinf : ℝ≥0∞) * ∏ v ∈ S, (c v : ℝ≥0∞)) ^ n * ((∫⁻ y, Ψinf y ∂(m₁inf (hermScal (Ainf F) σ (algebraMap F (Ainf F) t)))) *
        ∏ v ∈ S, ∫⁻ y, Ψ v y ∂(m₁ v (hermScal (Fv F v) σ (algebraMap F (Fv F v) t)))) := by rw [mul_pow]; ring
      _ = _ := by rw [hone2, one_pow, one_mul]
  have htail : ENNReal.ofReal (∏' v : {v // v ∉ S}, (m v.1 (hermOf (Fv F v.1) σ _ hT') (latV b v.1)).toReal) =
      τ' * ENNReal.ofReal (∏' v : {v // v ∉ S}, (m₁ v.1 (hermScal (Fv F v.1) σ (algebraMap F (Fv F v.1) t)) (latV b v.1)).toReal) := by
    have hA := GlobalTheory.T.infinite_product_multipliable {v // v ∉ S} (fun v => (m' v.1 (hermOf (Fv F v.1) σ T hT) (latV b v.1)).toReal)
      (hsum'.subtype _)
    have hB := GlobalTheory.T.infinite_product_multipliable {v // v ∉ S} (fun v => (m₁ v.1 (hermScal (Fv F v.1) σ (algebraMap F (Fv F v.1) t)) (latV b v.1)).toReal)
      (hsum₁.subtype _)
    have hcong : ∀ v : {v // v ∉ S}, (m v.1 (hermOf (Fv F v.1) σ _ hT') (latV b v.1)).toReal =
        (m' v.1 (hermOf (Fv F v.1) σ T hT) (latV b v.1)).toReal * (m₁ v.1 (hermScal (Fv F v.1) σ (algebraMap F (Fv F v.1) t)) (latV b v.1)).toReal := fun v => by
      rw [of_cofinite hG hS4 v.2 (lam v.1) (hlam v.1).1 (m v.1) (m₁ v.1) (m' v.1) (hm v.1) (hm₁ v.1) (hm' v.1) (c v.1) (hKv v.1), hc1 v.1 v.2]
      simp [ENNReal.toReal_mul]
    rw [tprod_congr hcong, hA.1.tprod_mul hB.1, ENNReal.ofReal_mul (hA.2.2.2 fun _ => ENNReal.toReal_nonneg)]
  rw [hprod, htail]
  simp only [ENNReal.coe_one, one_mul]
  ring

end GlobalTheory.CompanionTheory.SW.Step
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureAddRankOneBlockStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_weil_measure_add_rank_one_block : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ t : F, t ≠ 0 → ∀ n : ℕ, n + 2 ≤ M → ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 → ∀ (hT' : ∀ a b, σ (blockOne (algebraMap F E t) T b a) = blockOne (algebraMap F E t) T a b), SWMeas σ J T hT → SWMeas σ (blockOne (algebraMap F E t) J) (blockOne (algebraMap F E t) T) hT' := by
  first | exact @GlobalTheory.CompanionTheory.SW.Step.blockOne_step | exact GlobalTheory.CompanionTheory.SW.Step.blockOne_step | (intros; apply GlobalTheory.CompanionTheory.SW.Step.blockOne_step <;> assumption)
end
