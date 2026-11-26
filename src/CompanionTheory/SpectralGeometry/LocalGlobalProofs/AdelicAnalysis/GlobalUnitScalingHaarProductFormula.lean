module

public import GroundTheory.GlobalFields.TateThesis.AdeleScaling
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.BoxMulA
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasureGeneralRankExtension

@[expose] public section

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GlobalUnitScalingHaarProductFormula
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GlobalUnitScalingHaarProductFormula
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.ProdFormula

open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix Pointwise

section Infinite

variable {F : Type} [Field F] [NumberField F]

theorem map_mul_left_infinite {m : MeasurableSpace (InfiniteAdeleRing F)}
    (hm : @BorelSpace _ _ m) (b : (InfiniteAdeleRing F)ˣ) (μ : Measure (InfiniteAdeleRing F))
    (hμ : μ.IsAddHaarMeasure) :
    μ.map (fun y => (b : InfiniteAdeleRing F) * y) =
      ENNReal.ofReal ‖((b⁻¹ : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F)‖ • μ := by
  obtain rfl : m = GroundTheory.Global.measurableSpace_infiniteAdeleRing F :=
    hm.measurable_eq.trans (GroundTheory.Global.borelSpace_infiniteAdeleRing (K := F)).measurable_eq.symm
  have h := Measure.isAddLeftInvariant_eq_smul μ (GroundTheory.Global.infiniteAdeleMeasure F)
  rw [h, Measure.map_smul, GroundTheory.Global.map_mul_left_infiniteAdeleMeasure, smul_comm]
  exact (continuous_const_mul (b : InfiniteAdeleRing F)).measurable.aemeasurable

theorem norm_algebraMap_infinite (a : F) :
    ‖algebraMap F (InfiniteAdeleRing F) a‖ = ∏ w : InfinitePlace F, w a ^ w.mult := by
  rw [InfiniteAdeleRing.norm_def]
  refine Finset.prod_congr rfl fun w _ => ?_
  congr 1
  rw [InfiniteAdeleRing.algebraMap_apply]
  exact AbsoluteValue.Completion.norm_coe (WithAbs.toAbs w.1 a)

end Infinite

section Finite

open HeckeCharacterZeroLocus.SiegelWeilU

variable {F : Type} [Field F] [NumberField F]

theorem distribHaarChar_eq_nnnorm (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v) (ha : a ≠ 0) :
    distribHaarChar (Fv F v) (Units.mk0 a ha) = ‖a‖₊ := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  let ϖ : Fv F v := (π : Fv F v)
  have hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ) := by
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ]
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hϖ; exact WithZero.exp_ne_zero hϖ.symm
  have hva : Valued.v a ≠ 0 := (Valuation.ne_zero_iff _).2 ha
  set k : ℤ := WithZero.log (Valued.v a) with hk
  have hu0 : a * ϖ ^ k ≠ 0 := mul_ne_zero ha (zpow_ne_zero _ hϖ0)
  have hu : Valued.v (a * ϖ ^ k) = 1 := by
    rw [map_mul, map_zpow₀, hϖ, ← WithZero.exp_log hva, ← WithZero.exp_zsmul, ← WithZero.exp_add,
      ← hk, ← WithZero.exp_zero]
    congr 1
    simp
  have hU : Units.mk0 (a * ϖ ^ k) hu0 = Units.mk0 a ha * (Units.mk0 ϖ hϖ0) ^ k := by
    ext; simp [Units.val_zpow_eq_zpow_val]
  have h1 := PI.UnitaryGroupMassFormula.LocJacTyp.BM.dhc_unit v _ hu hu0
  rw [hU, map_mul, map_zpow, PI.UnitaryGroupMassFormula.LocJacTyp.BM.dhc_unif v ϖ hϖ hϖ0, inv_zpow] at h1
  have hq : ((Ideal.absNorm v.asIdeal : ℝ≥0)) ^ k ≠ 0 :=
    zpow_ne_zero _ (by exact_mod_cast PI.UnitaryGroupMassFormula.LocJacTyp.BM.q_ne_zero v)
  have h2 : distribHaarChar (Fv F v) (Units.mk0 a ha) = ((Ideal.absNorm v.asIdeal : ℝ≥0)) ^ k :=
    (mul_inv_eq_one₀ hq).1 h1
  rw [h2]
  apply NNReal.coe_injective
  rw [coe_nnnorm, ← GroundTheory.Global.normalizedAbv_apply, GroundTheory.Global.normalizedAbv_eq_zpow v ha, ← hk]
  simp

theorem map_mul_left_finite (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v) (ha : a ≠ 0)
    (μ : Measure (Fv F v)) (hμ : μ.IsAddHaarMeasure) :
    μ.map (fun x => a * x) = (‖a‖₊)⁻¹ • μ := by
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI := PI.UnitaryGroupMassFormula.LocJacTyp.BM.secondCountable_Fv v
  haveI : μ.Regular := inferInstance
  ext S hS
  rw [Measure.map_apply (continuous_const_mul _).measurable hS, Measure.smul_apply]
  have h := distribHaarChar_mul μ (Units.mk0 a ha)⁻¹ S
  have e : (fun x => a * x) ⁻¹' S = (Units.mk0 a ha)⁻¹ • S :=
    Set.preimage_smul (Units.mk0 a ha) S
  rw [e, ← h, map_inv, distribHaarChar_eq_nnnorm]
  rfl

end Finite

section Main

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW

theorem unitProd_scalar : ∀ (F : Type) [Field F] [NumberField F] (a : F), a ≠ 0 →
    ∃ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c ∧
      (∀ μ : Measure (Ainf F), μ.IsAddHaarMeasure →
        μ.map (fun x => algebraMap F (Ainf F) a * x) = cinf • μ) ∧
      ∀ v : HeightOneSpectrum (𝓞 F), ∀ μ : Measure (Fv F v), μ.IsAddHaarMeasure →
        μ.map (fun x => algebraMap F (Fv F v) a * x) = c v • μ := by
  intro F _ _ a ha
  have hA : 0 < ∏ w : InfinitePlace F, w a ^ w.mult :=
    Finset.prod_pos fun w _ => pow_pos (InfinitePlace.pos_iff.2 ha) _
  have hfin : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      ‖algebraMap F (Fv F v) a‖).Finite :=
    (FinitePlace.hasFiniteMulSupport ha).preimage
      (FinitePlace.equivHeightOneSpectrum (K := F)).symm.injective.injOn
  have hprod : (∏ w : InfinitePlace F, w a ^ w.mult) *
      ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖algebraMap F (Fv F v) a‖ = 1 := by
    rw [← prod_abs_eq_one ha, ← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm]
    rfl
  refine ⟨((∏ w : InfinitePlace F, w a ^ w.mult)⁻¹).toNNReal,
    fun v => (‖algebraMap F (Fv F v) a‖₊)⁻¹, ⟨?_, ?_⟩, ?_, ?_⟩
  · filter_upwards [hfin.eventually_cofinite_notMem] with v hv
    have h1 : ‖algebraMap F (Fv F v) a‖ = 1 := by simpa using hv
    have h2 : ‖algebraMap F (Fv F v) a‖₊ = 1 := NNReal.coe_injective h1
    rw [h2, inv_one]
  · apply NNReal.coe_injective
    have e : ((∏ᶠ v : HeightOneSpectrum (𝓞 F), (‖algebraMap F (Fv F v) a‖₊)⁻¹ : ℝ≥0) : ℝ) =
        (∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖algebraMap F (Fv F v) a‖)⁻¹ := by
      rw [finprod_inv_distrib]
      rw [NNReal.coe_inv]
      congr 1
      exact NNReal.toRealHom.map_finprod_of_injective NNReal.coe_injective _
    rw [NNReal.coe_mul, e, NNReal.coe_one, Real.coe_toNNReal _ (inv_pos.2 hA).le, ← mul_inv, hprod, inv_one]
  · intro μ hμ
    have hb : (((Units.map (algebraMap F (Ainf F)).toMonoidHom (Units.mk0 a ha))⁻¹ : (Ainf F)ˣ) : Ainf F) =
        algebraMap F (Ainf F) a⁻¹ := by
      simp
    have h := map_mul_left_infinite (F := F) (m := measAinf) ⟨rfl⟩
      (Units.map (algebraMap F (Ainf F)).toMonoidHom (Units.mk0 a ha)) μ hμ
    rw [hb, norm_algebraMap_infinite] at h
    have e : ∏ w : InfinitePlace F, w a⁻¹ ^ w.mult = (∏ w : InfinitePlace F, w a ^ w.mult)⁻¹ := by
      rw [← Finset.prod_inv_distrib]
      exact Finset.prod_congr rfl fun w _ => by rw [map_inv₀, inv_pow]
    rw [e] at h
    exact h
  · intro v μ hμ
    exact map_mul_left_finite v _ ((map_ne_zero _).2 ha) μ hμ

end Main

end GlobalTheory.CompanionTheory.SW.ProdFormula
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GlobalUnitScalingHaarProductFormulaStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.global_unit_scaling_haar_product_formula : ∀ (F : Type) [Field F] [NumberField F] (a : F), a ≠ 0 → ∃ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c ∧ (∀ μ : Measure (Ainf F), μ.IsAddHaarMeasure → μ.map (fun x => algebraMap F (Ainf F) a * x) = cinf • μ) ∧ ∀ v : HeightOneSpectrum (𝓞 F), ∀ μ : Measure (Fv F v), μ.IsAddHaarMeasure → μ.map (fun x => algebraMap F (Fv F v) a * x) = c v • μ := by
  first | exact @GlobalTheory.CompanionTheory.SW.ProdFormula.unitProd_scalar | exact GlobalTheory.CompanionTheory.SW.ProdFormula.unitProd_scalar | (intros; apply GlobalTheory.CompanionTheory.SW.ProdFormula.unitProd_scalar <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresSupport
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresSupport
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.FibScale

theorem fib_rmul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ), ∀ (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)) (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFib R σ J n μ ν m → ∀ (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)), IsUnit g.det → ∀ τ : HermR R σ n → HermR R σ n, (∀ S, (τ S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = cT (sigR R σ) g * S * g) → ∀ a c : ℝ≥0, μ.map (fun X => rmul R X g) = a • μ → ν.map τ = c • ν → ∀ S, a • m (τ S) = c • (m S).map (fun X => rmul R X g) := by
  intro F E _ _ _ _ _ σ hσ M J hJ R _ _ _ _ _ hR n μ ν m hμ hν hm g hg τ hτ a c hmu hnu S
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
  obtain ⟨hLH, hSH, hT2H, hBH, hG⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hσ R n
  haveI := hLH
  haveI := hSH
  haveI := hT2H
  haveI := hBH
  obtain ⟨G, hGc, hGe⟩ := hG M J hJ
  obtain ⟨halg, hcomp, hone, hmem, -⟩ := GlobalTheory.CompanionTheory.SW.GramAlg.gram_algebra F E σ hσ M J hJ R n
  have hKu := GlobalTheory.CompanionTheory.SW.KUnits.units_val_isOpenEmbedding F E σ hσ R hR
  have hg1 : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g hg
  have hg2 : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul g hg
  have hgi : IsUnit (g⁻¹).det := Matrix.isUnit_nonsing_inv_det g hg
  have hrc : ∀ h : Matrix (Fin n) (Fin n) (R ⊗[F] E),
      Continuous fun X : Fin n → Fin M → R ⊗[F] E => rmul R X h := by
    intro h
    refine continuous_pi fun b => continuous_pi fun i => ?_
    simp only [rmul]
    refine continuous_finsetSum _ fun k _ => ?_
    have h1 : Continuous fun Y : Fin n → Fin M → R ⊗[F] E => Y k i :=
      (continuous_apply i).comp (continuous_apply k)
    exact h1.mul continuous_const
  let e : (Fin n → Fin M → R ⊗[F] E) ≃ₜ (Fin n → Fin M → R ⊗[F] E) :=
    { toFun := fun X => rmul R X g
      invFun := fun X => rmul R X g⁻¹
      left_inv := fun X => by simp only [hcomp, hg1, hone]
      right_inv := fun X => by simp only [hcomp, hg2, hone]
      continuous_toFun := hrc g
      continuous_invFun := hrc g⁻¹ }
  have hc1 : cT (sigR R σ) (1 : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = 1 := by
    unfold cT
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]
  have key : ∀ (h h' A : Matrix (Fin n) (Fin n) (R ⊗[F] E)), h * h' = 1 →
      cT (sigR R σ) h' * (cT (sigR R σ) h * A * h) * h' = A := by
    intro h h' A hh
    have h1 : cT (sigR R σ) h' * cT (sigR R σ) h = 1 := by
      rw [← cT_mul, hh, hc1]
    calc cT (sigR R σ) h' * (cT (sigR R σ) h * A * h) * h'
        = (cT (sigR R σ) h' * cT (sigR R σ) h) * A * (h * h') := by
          simp only [Matrix.mul_assoc]
      _ = A := by rw [h1, hh, Matrix.one_mul, Matrix.mul_one]
  let τ' : HermR R σ n → HermR R σ n := fun S =>
    ⟨cT (sigR R σ) g⁻¹ * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * g⁻¹, hmem S g⁻¹⟩
  have hcj : ∀ h : Matrix (Fin n) (Fin n) (R ⊗[F] E), Continuous fun S : HermR R σ n =>
      cT (sigR R σ) h * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * h := fun h =>
    (continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const
  let τh : HermR R σ n ≃ₜ HermR R σ n :=
    { toFun := τ
      invFun := τ'
      left_inv := fun S => Subtype.ext (by
        show cT (sigR R σ) g⁻¹ * ((τ S : HermR R σ n) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * g⁻¹ = S
        rw [hτ]
        exact key _ _ _ hg1)
      right_inv := fun S => Subtype.ext (by
        rw [hτ]
        exact key _ _ _ hg2)
      continuous_toFun := by
        refine Topology.IsInducing.subtypeVal.continuous_iff.2 ?_
        exact (hcj g).congr fun S => (hτ S).symm
      continuous_invFun := (hcj g⁻¹).subtype_mk _ }
  let B : Set (HermR R σ n) := {S | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det}
  have hBo : IsOpen B := by
    have : B = (fun S : HermR R σ n => (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det) ⁻¹'
        Set.range (Units.val : (R ⊗[F] E)ˣ → R ⊗[F] E) := by
      ext S
      rfl
    rw [this]
    exact hKu.isOpen_range.preimage continuous_subtype_val.matrix_det
  have hdet : ∀ h A : Matrix (Fin n) (Fin n) (R ⊗[F] E), IsUnit h.det → IsUnit A.det →
      IsUnit (cT (sigR R σ) h * A * h).det := by
    intro h A hh hA
    have h1 : (cT (sigR R σ) h).det = sigR R σ h.det := by
      rw [RingHom.map_det]
      simp [cT, Matrix.det_transpose]
    rw [Matrix.det_mul, Matrix.det_mul, h1]
    exact ((hh.map (sigR R σ)).mul hA).mul hh
  have hBτ : τh '' B = B := by
    ext S'
    constructor
    · rintro ⟨S, hS, rfl⟩
      show IsUnit ((τ S : HermR R σ n) : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det
      rw [hτ]
      exact hdet _ _ hg hS
    · intro hS'
      exact ⟨τh.symm S', hdet _ _ hgi hS', τh.apply_symm_apply _⟩
  have hU : G ⁻¹' B = {X | IsUnit (gramR R σ J X).det} := by
    ext X
    show IsUnit _ ↔ IsUnit _
    rw [hGe]
  have hfam : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ (gramR R σ J) Subtype.val (G ⁻¹' B) ν B m := by
    rw [hU]
    exact hm
  have hcomm : ∀ X, G (e X) = τh (G X) := by
    intro X
    apply Subtype.ext
    show ((G (rmul R X g) : HermR R σ n) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) =
      ((τ (G X) : HermR R σ n) : Matrix (Fin n) (Fin n) (R ⊗[F] E))
    rw [← hGe, hτ, ← hGe]
    exact halg X g
  have htr := GlobalTheory.CompanionTheory.SW.isFibreFamily_transport _ _ _ μ ν (gramR R σ J) G Subtype.val
    Subtype.val_injective hGc hGe _ (gramR R σ J) G hGc hGe e τh hcomm B hBo m hfam
  rw [hBτ, hU] at htr
  have hmu' : μ.map e = a • μ := hmu
  have hnu' : ν.map τh = c • ν := hnu
  rw [hmu', hnu'] at htr
  have hnew : IsGramFib R σ J n (a • μ) (c • ν) (fun b => (m (τh.symm b)).map e) := htr
  have ha0 : a ≠ 0 := by
    rintro rfl
    have h0 : μ.map e = 0 := by rw [hmu', zero_smul]
    have h1 : (μ.map e) Set.univ = μ Set.univ := by
      rw [e.measurableEmbedding.map_apply, Set.preimage_univ]
    rw [h0] at h1
    exact (isOpen_univ.measure_pos μ Set.univ_nonempty).ne h1
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h0 : ν.map τh = 0 := by rw [hnu', zero_smul]
    have h1 : (ν.map τh) Set.univ = ν Set.univ := by
      rw [τh.measurableEmbedding.map_apply, Set.preimage_univ]
    rw [h0] at h1
    exact (isOpen_univ.measure_pos ν Set.univ_nonempty).ne h1
  haveI hμa : (a • μ).IsAddHaarMeasure := Measure.IsAddHaarMeasure.nnreal_smul μ ha0
  haveI hνc : (c • ν).IsAddHaarMeasure := Measure.IsAddHaarMeasure.nnreal_smul ν hc0
  have hres := GlobalTheory.T.gram_fiber_measures_scaling F E σ hσ M J hJ R hR n μ ν m hμ hν hm a c ha0 hc0
  have huq := GlobalTheory.T.gram_fiber_measures_unique F E σ hσ M J hJ R hR n (a • μ) (c • ν) _ hμa hνc hres _ hnew (τ S)
  have hs : τh.symm (τ S) = S := τh.symm_apply_apply S
  simp only [hs] at huq
  have hfin : (m S).map (fun X => rmul R X g) = (a / c) • m (τ S) := huq.symm
  rw [hfin, smul_smul, mul_div_cancel₀ a hc0]

end GlobalTheory.CompanionTheory.SW.FibScale
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresSupportStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_fiber_measures_rmul_equivariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ), ∀ (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)) (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFib R σ J n μ ν m → ∀ (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)), IsUnit g.det → ∀ τ : HermR R σ n → HermR R σ n, (∀ S, (τ S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = cT (sigR R σ) g * S * g) → ∀ a c : ℝ≥0, μ.map (fun X => rmul R X g) = a • μ → ν.map τ = c • ν → ∀ S, a • m (τ S) = c • (m S).map (fun X => rmul R X g) := by
  first | exact @GlobalTheory.CompanionTheory.SW.FibScale.fib_rmul | exact GlobalTheory.CompanionTheory.SW.FibScale.fib_rmul | (intros; apply GlobalTheory.CompanionTheory.SW.FibScale.fib_rmul <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresInvariant
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresInvariant
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.FibreInv

theorem map_actW_fibre : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ), ∀ (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)) (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFib R σ J n μ ν m → ∀ (h : HA R σ J) (S : HermR R σ n), (m S).map (actW R σ J h) = m S := by
  intro F E _ _ _ _ _ σ hσ M J hJ R _ _ _ _ _ hR n μ ν m hμ hν hm h S
  have hR' := hR
  obtain ⟨_, _, _, _, -, -, -, -⟩ := hR'
  obtain ⟨_, _, _, _, -, -, -, hbor, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ R
  have hbor' := hbor n M
  obtain ⟨_, _, _, _, hlift⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hσ R n
  obtain ⟨g, hgc, hgf⟩ := hlift M J hJ
  obtain ⟨_, -, -, -, -, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hσ M J hJ R
  obtain ⟨hcont, hone, hmul, hgr⟩ := hact n
  have hcg : ∀ k : HA R σ J, Continuous (actW R σ J k : (Fin n → Fin M → R ⊗[F] E) → _) := fun k =>
    hcont.comp (Continuous.prodMk_right k)
  let e : (Fin n → Fin M → R ⊗[F] E) ≃ₜ (Fin n → Fin M → R ⊗[F] E) :=
    { toFun := actW R σ J h
      invFun := actW R σ J h⁻¹
      left_inv := fun X => by rw [← hmul, inv_mul_cancel, hone]
      right_inv := fun X => by rw [← hmul, mul_inv_cancel, hone]
      continuous_toFun := hcg h
      continuous_invFun := hcg h⁻¹ }
  have he : (e : (Fin n → Fin M → R ⊗[F] E) → _) = actW R σ J h := rfl
  let B : Set (HermR R σ n) := {S | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det}
  have hB : IsOpen B := by
    have hop := (GlobalTheory.T.units_open_embedding_local_tensor F E σ hσ R hR).isOpen_range
    have hBe : B = (fun S : HermR R σ n => (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det) ⁻¹'
        Set.range (Units.val : (R ⊗[F] E)ˣ → R ⊗[F] E) := by
      ext T
      simp [B, IsUnit]
    rw [hBe]
    exact hop.preimage (Continuous.matrix_det continuous_subtype_val)
  have hU : {X | IsUnit (gramR R σ J X).det} = g ⁻¹' B := by
    ext X
    simp only [Set.mem_setOf_eq, Set.mem_preimage, B, hgf]
  have hm' : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ (gramR R σ J) Subtype.val (g ⁻¹' B) ν B m := by
    rw [← hU]
    exact hm
  have hgi : ∀ X, g (e X) = (Homeomorph.refl (HermR R σ n)) (g X) := by
    intro X
    apply Subtype.ext
    show (g (actW R σ J h X) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = g X
    rw [← hgf, ← hgf, hgr]
  have ht := GlobalTheory.CompanionTheory.SW.isFibreFamily_transport _ (HermR R σ n) _ μ ν (gramR R σ J) g Subtype.val
    Subtype.val_injective hgc hgf _ (gramR R σ J) g hgc hgf e (Homeomorph.refl _) hgi B hB m hm'
  have himg : (Homeomorph.refl (HermR R σ n)) '' B = B := by simp
  have hνm : ν.map (Homeomorph.refl (HermR R σ n)) = ν := by
    simpa using Measure.map_id (μ := ν)
  have hμm : μ.map e = μ := GlobalTheory.T.unitary_action_preserves_haar_local F E σ hσ M J hJ R hR n μ hμ h
  rw [himg, hνm, hμm, ← hU] at ht
  exact (GlobalTheory.T.gram_fiber_measures_unique F E σ hσ M J hJ R hR n μ ν _ hμ hν ht m hm S)

end GlobalTheory.CompanionTheory.SW.FibreInv
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresInvariantStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_fiber_measures_invariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ), ∀ (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)) (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFib R σ J n μ ν m → ∀ (h : HA R σ J) (S : HermR R σ n), (m S).map (actW R σ J h) = m S := by
  first | exact @GlobalTheory.CompanionTheory.SW.FibreInv.map_actW_fibre | exact GlobalTheory.CompanionTheory.SW.FibreInv.map_actW_fibre | (intros; apply GlobalTheory.CompanionTheory.SW.FibreInv.map_actW_fibre <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberConsProductFubini
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology ProbabilityTheory
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂

theorem isSFiniteKernel_of_forall_univ_lt_top {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
    (η : Kernel α β) (h : ∀ a, η a Set.univ < ⊤) : IsSFiniteKernel η := by
  classical
  have hmeas : Measurable fun a => η a Set.univ := η.measurable_coe MeasurableSet.univ
  let g : α → ℕ := fun a => ⌊(η a Set.univ).toReal⌋₊
  have hg : Measurable g := Nat.measurable_floor.comp hmeas.ennreal_toReal
  have hB : ∀ j : ℕ, MeasurableSet (g ⁻¹' {j}) := fun j => hg (measurableSet_singleton j)
  let ηs : ℕ → Kernel α β := fun j => Kernel.piecewise (hB j) η 0
  have hfin : ∀ j, IsFiniteKernel (ηs j) := by
    intro j
    refine ⟨⟨(j : ℝ≥0∞) + 1, by simp [ENNReal.add_lt_top], fun a => ?_⟩⟩
    by_cases ha : a ∈ g ⁻¹' {j}
    · have hj : g a = j := ha
      have h1 : (η a Set.univ).toReal < (j : ℝ) + 1 := by
        have := Nat.lt_floor_add_one (η a Set.univ).toReal
        simpa [g, hj] using this
      have h2 : η a Set.univ = ENNReal.ofReal (η a Set.univ).toReal :=
        (ENNReal.ofReal_toReal (h a).ne).symm
      simp only [ηs, Kernel.piecewise_apply, if_pos ha]
      rw [h2]
      refine ENNReal.ofReal_le_of_le_toReal ?_
      rw [ENNReal.toReal_add (by simp) (by simp)]
      simpa using h1.le
    · have ha' : ¬ g a = j := ha
      simp [ηs, Kernel.piecewise_apply, ha']
  have hsum : η = Kernel.sum ηs := by
    ext a s hs
    rw [Kernel.sum_apply, Measure.sum_apply _ hs, tsum_eq_single (g a)]
    · simp [ηs, Kernel.piecewise_apply]
    · intro j hj
      have ha' : ¬ g a = j := fun h' => hj h'.symm
      simp [ηs, Kernel.piecewise_apply, ha']
  rw [hsum]
  exact ⟨⟨fun j => ηs j, hfin, rfl⟩⟩

theorem isSFiniteKernel_of_locallyFinite {α β : Type} [MeasurableSpace α] [TopologicalSpace β]
    [MeasurableSpace β] [BorelSpace β] [T2Space β] [SigmaCompactSpace β]
    (κ : Kernel α β) (h : ∀ a, IsLocallyFiniteMeasure (κ a)) : IsSFiniteKernel κ := by
  let C : ℕ → Set β := disjointed (compactCovering β)
  have hCm : ∀ k, MeasurableSet (C k) := fun k =>
    MeasurableSet.disjointed (fun i => (isCompact_compactCovering β i).measurableSet) k
  have hCd : Pairwise (Function.onFun Disjoint C) := disjoint_disjointed _
  have hCu : ⋃ k, C k = Set.univ := by
    simp only [C, iUnion_disjointed]
    exact iUnion_compactCovering β
  have hCf : ∀ a k, κ a (C k) < ⊤ := fun a k => by
    haveI := h a
    exact (measure_mono (disjointed_subset _ k)).trans_lt
      (isCompact_compactCovering β k).measure_lt_top
  have hk : ∀ k, IsSFiniteKernel (Kernel.restrict κ (hCm k)) := fun k =>
    isSFiniteKernel_of_forall_univ_lt_top _ (fun a => by
      rw [Kernel.restrict_apply]
      simpa using hCf a k)
  have hsum : κ = Kernel.sum fun k => Kernel.restrict κ (hCm k) := by
    ext a s hs
    rw [Kernel.sum_apply]
    simp only [Kernel.restrict_apply]
    rw [← Measure.restrict_iUnion hCd hCm, hCu, Measure.restrict_univ]
  rw [hsum]
  infer_instance

theorem measurable_vec_triple {K : Type} [Zero K] [MeasurableSpace K] {M n : ℕ} :
    Measurable (fun p : K × (Fin n → K) × (Fin n → Fin M → K) =>
      (vec p.1 p.2.1 p.2.2 : Fin (n + 1) → Fin (M + 1) → K)) := by
  refine Measurable.of_eval fun a => Measurable.of_eval fun i => ?_
  induction a using Fin.cases with
  | zero =>
    induction i using Fin.cases with
    | zero => simpa [vec] using measurable_fst
    | succ i => simpa [vec] using measurable_const
  | succ j =>
    induction i using Fin.cases with
    | zero =>
      simp only [vec, Fin.cons_succ, Fin.cons_zero]
      exact (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)
    | succ i =>
      simp only [vec, Fin.cons_succ]
      exact (measurable_pi_apply i).comp
        ((measurable_pi_apply j).comp (measurable_snd.comp measurable_snd))

theorem measurable_Pint (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R]
    [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ)
    (b : Module.Basis (Fin d) F E) (lam : Measure R)
    (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E))
    (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E))
    (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J))
    (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0)
    (D : StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm)
    (φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞) (hφ : Measurable φ) :
    Measurable (fun z : R × (Fin n → R ⊗[F] E) × HermR R σ n =>
      Pint σ J t m₁ m' s φ z.1 z.2.1 z.2.2) := by
  obtain ⟨iTR, iLR, iSR, iTR2, -⟩ := D.hR
  haveI := iTR
  haveI := iLR
  haveI := iSR
  haveI := iTR2
  obtain ⟨iTK, iLK, iSK, iT2K, -, -, -, iBor, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ D.hCM R
  haveI := iTK
  haveI := iLK
  haveI := iSK
  haveI := iT2K
  have hJ' := GlobalTheory.T.block_one_scalar_preserves_nondegenerate F E σ M J D.hJ t D.ht
  obtain ⟨-, hloc, -, hmeas, -, -⟩ :=
    GlobalTheory.T.gram_fiber_measure_locally_finite_measurable_supported F E σ D.hCM M n J D.hJ R D.hR d b lam D.hlam m' D.hm'
  obtain ⟨-, hloc₁, -⟩ :=
    GlobalTheory.T.gram_fiber_measure_locally_finite_measurable_supported F E σ D.hCM (M + 1) 1 _ hJ' R D.hR d b lam D.hlam m₁ D.hm₁
  obtain ⟨-, -, iSH, -, iBH, hH⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ D.hCM (M + 1) _ hJ' R
  haveI := iSH
  haveI := iBH
  haveI : BorelSpace (Fin n → Fin M → R ⊗[F] E) := iBor n M
  haveI : BorelSpace (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) := iBor (n + 1) (M + 1)
  haveI : BorelSpace (Fin 1 → Fin (M + 1) → R ⊗[F] E) := iBor 1 (M + 1)
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  have hact := (hH (n + 1)).1
  have hten : Measurable (fun r : R => r ⊗ₜ[F] (1 : E)) := by
    haveI : ContinuousSMul R (R ⊗[F] E) := IsModuleTopology.toContinuousSMul R (R ⊗[F] E)
    have hc : Continuous (fun r : R => r • (1 : R ⊗[F] E)) :=
      Continuous.smul (f := fun r : R => r) (g := fun _ : R => (1 : R ⊗[F] E))
        continuous_id continuous_const
    have he : (fun r : R => r ⊗ₜ[F] (1 : E)) = fun r : R => r • (1 : R ⊗[F] E) := by
      funext r
      simp [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul']
    rw [he]
    exact hc.measurable
  let κ : Kernel (HermR R σ n) (Fin n → Fin M → R ⊗[F] E) :=
    ⟨m', Measure.measurable_of_measurable_coe _ hmeas⟩
  haveI : IsSFiniteKernel κ := isSFiniteKernel_of_locallyFinite κ hloc
  let κ' : Kernel ((R × (Fin n → R ⊗[F] E) × HermR R σ n) × (Fin 1 → Fin (M + 1) → R ⊗[F] E))
      (Fin n → Fin M → R ⊗[F] E) :=
    κ.comap (fun p => p.1.2.2) (measurable_snd.comp (measurable_snd.comp measurable_fst))
  haveI := hloc₁ (hermScal R σ (algebraMap F R t))
  have hvec : Measurable (fun q : ((R × (Fin n → R ⊗[F] E) × HermR R σ n) ×
      (Fin 1 → Fin (M + 1) → R ⊗[F] E)) × (Fin n → Fin M → R ⊗[F] E) =>
        (vec (q.1.1.1 ⊗ₜ[F] (1 : E)) q.1.1.2.1 q.2 : Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)) :=
    measurable_vec_triple.comp ((hten.comp (measurable_fst.comp (measurable_fst.comp measurable_fst))).prodMk
      (((measurable_fst.comp (measurable_snd.comp (measurable_fst.comp measurable_fst)))).prodMk
        measurable_snd))
  have hΦ : Measurable (fun q : ((R × (Fin n → R ⊗[F] E) × HermR R σ n) ×
      (Fin 1 → Fin (M + 1) → R ⊗[F] E)) × (Fin n → Fin M → R ⊗[F] E) =>
        actW R σ (blockOne (algebraMap F E t) J) (s q.1.2)
          (vec (q.1.1.1 ⊗ₜ[F] (1 : E)) q.1.1.2.1 q.2)) :=
    hact.measurable.comp ((D.hs.comp (measurable_snd.comp measurable_fst)).prodMk hvec)
  have hinner := Measurable.lintegral_kernel_prod_right' (κ := κ') (hφ.comp hΦ)
  exact Measurable.lintegral_prod_right' (ν := m₁ (hermScal R σ (algebraMap F R t))) hinner

end GlobalTheory.CompanionTheory.SW.PiLocalization₂
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberConsProductNormalization
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberConsProductNormalization
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂

theorem measurable_vec {K : Type} [Zero K] [MeasurableSpace K] {M n : ℕ} (α : K) (c : Fin n → K) :
    Measurable (fun X : Fin n → Fin M → K => vec α c X) := by
  refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun k => ?_
  induction i using Fin.cases with
  | zero => simpa [vec] using (measurable_const : Measurable fun _ : Fin n → Fin M → K =>
      (Fin.cons α (fun _ => 0) : Fin (M + 1) → K) k)
  | succ i =>
    induction k using Fin.cases with
    | zero => simpa [vec] using (measurable_const : Measurable fun _ : Fin n → Fin M → K => c i)
    | succ k =>
      have h : Measurable fun X : Fin n → Fin M → K => X i k :=
        (measurable_pi_apply k).comp (measurable_pi_apply i)
      simpa [vec] using h

theorem fibS_support : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ S : HermR R σ (n + 1), fibS σ J t m₁ m' s B₀ a κ₁ cm S (gramR R σ (blockOne (algebraMap F E t) J) ⁻¹' {(S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))} ∩ gramR R σ (blockOne (algebraMap F E t) J) ⁻¹' (Subtype.val '' (Bset R σ t a B₀ : Set (HermR R σ (n + 1)))))ᶜ = 0 := by
  intro F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm D S
  by_cases hS : S ∈ Bset R σ t a B₀
  swap
  · simp [fibS, hS]
  obtain ⟨h1, h2, h3, h4, -⟩ := id D.hR
  have hk := GlobalTheory.T.tensor_locally_compact_ring F E σ D.hCM R
  have hJ' := GlobalTheory.T.block_one_scalar_preserves_nondegenerate F E σ M J D.hJ t D.ht
  have hH := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ D.hCM (M + 1) _ hJ' R
  obtain ⟨-, -, hscH, -, hbH, hactH⟩ := hH
  obtain ⟨-, -, hscK, hT2K, -, -, -, hbor, -, hgram⟩ := hk
  obtain ⟨hcont, -, -, hpres⟩ := hactH (n + 1)
  have hcoord := (GlobalTheory.T.gram_block_one_schur_coordinates F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D).2
  have hker' := GlobalTheory.T.gram_fiber_measure_locally_finite_measurable_supported F E σ D.hCM M n J D.hJ R D.hR d b lam D.hlam m' D.hm'
  have hker₁ := GlobalTheory.T.gram_fiber_measure_locally_finite_measurable_supported F E σ D.hCM (M + 1) 1 _ hJ' R D.hR d b lam D.hlam m₁ D.hm₁
  obtain ⟨-, hlf', -, -, -, hfib'⟩ := hker'
  obtain ⟨-, hlf₁, -⟩ := hker₁
  haveI := hbor (n + 1) (M + 1)
  haveI := hbor n M
  haveI := hbor 1 (M + 1)
  haveI := hlf₁ (hermScal R σ (algebraMap F R t))
  haveI := hlf' (schur R σ t a S)
  let α : R ⊗[F] E := ((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) : Rˣ) : R) ⊗ₜ[F] (1 : E)
  let c := cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))
  let f : (Fin 1 → Fin (M + 1) → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) → (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) :=
    fun p => actW R σ (blockOne (algebraMap F E t) J) (s p.1) (vec α c p.2)
  have hfm : Measurable f := by
    have := hcont.measurable.comp
      ((D.hs.comp measurable_fst).prodMk ((measurable_vec α c).comp measurable_snd))
    exact this
  have hcl : MeasurableSet ((gramR R σ (blockOne (algebraMap F E t) J) ⁻¹' {(S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))})ᶜ) :=
    ((isClosed_singleton.preimage (hgram (n + 1) (M + 1) (blockOne (algebraMap F E t) J))).measurableSet).compl
  have hae : ∀ᵐ p ∂((m₁ (hermScal R σ (algebraMap F R t))).prod (m' (schur R σ t a S))),
      gramR R σ (blockOne (algebraMap F E t) J) (f p) = (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) := by
    have h := (Measure.quasiMeasurePreserving_snd (μ := m₁ (hermScal R σ (algebraMap F R t)))
      (ν := m' (schur R σ t a S))).ae (hfib' (schur R σ t a S))
    filter_upwards [h] with p hp
    change gramR R σ (blockOne (algebraMap F E t) J)
      (actW R σ (blockOne (algebraMap F E t) J) (s p.1) (vec α c p.2)) = _
    rw [hpres]
    exact hcoord S p.2 hS.1 hp
  have hsub : (gramR R σ (blockOne (algebraMap F E t) J) ⁻¹' {(S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))} ∩
      gramR R σ (blockOne (algebraMap F E t) J) ⁻¹' (Subtype.val '' (Bset R σ t a B₀ : Set (HermR R σ (n + 1)))))ᶜ ⊆
      (gramR R σ (blockOne (algebraMap F E t) J) ⁻¹' {(S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))})ᶜ := by
    intro x hx hxS
    exact hx ⟨hxS, ⟨S, hS, (Set.mem_singleton_iff.1 hxS).symm⟩⟩
  refine measure_mono_null hsub ?_
  have hmap : (((m₁ (hermScal R σ (algebraMap F R t))).prod (m' (schur R σ t a S))).map f)
      ((gramR R σ (blockOne (algebraMap F E t) J) ⁻¹' {(S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))})ᶜ) = 0 := by
    rw [Measure.map_apply hfm hcl]
    refine measure_mono_null ?_ (ae_iff.1 hae)
    intro p hp hpS
    exact hp hpS
  unfold fibS
  rw [Set.indicator_of_mem hS, Measure.smul_apply]
  change _ • (((m₁ (hermScal R σ (algebraMap F R t))).prod (m' (schur R σ t a S))).map f) _ = 0
  rw [hmap, smul_zero]

end GlobalTheory.CompanionTheory.SW.PiLocalization₂
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberConsProductNormalizationStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_fiber_cons_concentrated_on_fiber : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ S : HermR R σ (n + 1), fibS σ J t m₁ m' s B₀ a κ₁ cm S (gramR R σ (blockOne (algebraMap F E t) J) ⁻¹' {(S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))} ∩ gramR R σ (blockOne (algebraMap F E t) J) ⁻¹' (Subtype.val '' (Bset R σ t a B₀ : Set (HermR R σ (n + 1)))))ᶜ = 0 := by
  first | exact @GlobalTheory.CompanionTheory.SW.PiLocalization₂.fibS_support | exact GlobalTheory.CompanionTheory.SW.PiLocalization₂.fibS_support | (intros; apply GlobalTheory.CompanionTheory.SW.PiLocalization₂.fibS_support <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresChangeOfForm
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresChangeOfForm
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.LocIsom

theorem fibre_map_isometry : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (J' : Matrix (Fin M) (Fin M) E), IsHermND σ J' → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ), ∀ (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)) (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFib R σ J n μ ν m → ∀ (μ' : Measure (Fin n → Fin M → R ⊗[F] E)) m', μ'.IsAddHaarMeasure → IsGramFib R σ J' n μ' ν m' → ∀ g : GL (Fin M) (R ⊗[F] E), JR R J' = cT (sigR R σ) (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J * (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) → ∀ a : ℝ≥0, μ'.map (actTup R g) = a • μ → ∀ S, (m' S).map (actTup R g) = a • m S := by
  intro F E _ _ _ _ _ σ hcm M J hJ J' hJ' R _ _ _ _ _ hR n μ ν m hμ hν hm μ' m' hμ' hm' g hg a ha S
  have hR' := hR
  obtain ⟨hTR, hLC, hSC, hT2, -, -, -, -⟩ := hR'
  obtain ⟨hK1, hK2, hK3, hK4, -, -, -, hK8, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm R
  haveI := hK8 n M
  obtain ⟨hH1, hH2, hH3, hH4, hlift⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hcm R n
  obtain ⟨l, hlc, hl⟩ := hlift M J hJ
  obtain ⟨l', hlc', hl'⟩ := hlift M J' hJ'
  have hact : ∀ X, gramR R σ J (actTup R g X) = gramR R σ J' X :=
    (GlobalTheory.CompanionTheory.SW.GramAlg.gram_algebra F E σ hcm M J hJ R n).2.2.2.2 J' g hg
  have hcont : ∀ h : GL (Fin M) (R ⊗[F] E),
      Continuous (actTup R h : (Fin n → Fin M → R ⊗[F] E) → (Fin n → Fin M → R ⊗[F] E)) := by
    intro h
    refine continuous_pi fun b => ?_
    exact continuous_const.matrix_mulVec (continuous_apply b)
  let e : (Fin n → Fin M → R ⊗[F] E) ≃ₜ (Fin n → Fin M → R ⊗[F] E) :=
    { toFun := actTup R g
      invFun := actTup R g⁻¹
      left_inv := fun X => by
        funext b
        simp [actTup, Matrix.mulVec_mulVec]
      right_inv := fun X => by
        funext b
        simp [actTup, Matrix.mulVec_mulVec]
      continuous_toFun := hcont g
      continuous_invFun := hcont g⁻¹ }
  have he : (e : (Fin n → Fin M → R ⊗[F] E) → _) = actTup R g := rfl
  let B : Set (HermR R σ n) := {S | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det}
  have hB : IsOpen B := by
    have hu := (GlobalTheory.T.units_open_embedding_local_tensor F E σ hcm R hR).isOpen_range
    have hd : Continuous fun S : HermR R σ n => (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det :=
      Continuous.matrix_det continuous_subtype_val
    have := hu.preimage hd
    convert this using 1
    ext S
    simp [B, IsUnit]
  have hset : {X | IsUnit (gramR R σ J X).det} = l ⁻¹' B := by
    ext X
    simp [B, hl X]
  have hset' : {X | IsUnit (gramR R σ J' X).det} = l' ⁻¹' B := by
    ext X
    simp [B, hl' X]
  have hm'' : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ' (gramR R σ J') Subtype.val (l' ⁻¹' B) ν B m' := by
    have := hm'
    unfold IsGramFib at this
    rw [hset'] at this
    exact this
  have hcompat : ∀ X, l (e X) = (Homeomorph.refl _) (l' X) := by
    intro X
    apply Subtype.ext
    show ((l (e X) : HermR R σ n) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = (l' X : HermR R σ n)
    rw [← hl, ← hl']
    exact hact X
  have hT := GlobalTheory.CompanionTheory.SW.isFibreFamily_transport _ _ _ μ' ν (gramR R σ J') l' Subtype.val
    Subtype.val_injective hlc' hl' _ (gramR R σ J) l hlc hl e (Homeomorph.refl _) hcompat B hB m' hm''
  have himg : (Homeomorph.refl (HermR R σ n)) '' B = B := by simp
  have hνm : ν.map (Homeomorph.refl (HermR R σ n)) = ν := by
    simp
  rw [himg, hνm, he, ha, ← hset] at hT
  have hfib : IsGramFib R σ J n (a • μ) ν (fun S => (m' S).map (actTup R g)) := hT
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_smul] at ha
    have h0 : μ' ≠ 0 := by
      intro h
      have := isOpen_univ.measure_pos μ' Set.univ_nonempty
      simp [h] at this
    apply h0
    rw [← he] at ha
    have := congrArg (fun ρ : Measure _ => ρ Set.univ) ha
    simp only [Measure.coe_zero, Pi.zero_apply] at this
    rw [Measure.map_apply e.continuous.measurable MeasurableSet.univ] at this
    simpa using this
  have hHaar : (a • μ).IsAddHaarMeasure := Measure.IsAddHaarMeasure.nnreal_smul μ ha0
  have h1 := GlobalTheory.T.gram_fiber_measures_scaling F E σ hcm M J hJ R hR n μ ν m hμ hν hm a 1 ha0 one_ne_zero
  rw [one_smul] at h1
  simp only [div_one] at h1
  exact GlobalTheory.T.gram_fiber_measures_unique F E σ hcm M J hJ R hR n (a • μ) ν _ hHaar hν hfib _ h1 S

end GlobalTheory.CompanionTheory.SW.LocIsom
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresChangeOfFormStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_fiber_measures_change_of_form : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (J' : Matrix (Fin M) (Fin M) E), IsHermND σ J' → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ), ∀ (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)) (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFib R σ J n μ ν m → ∀ (μ' : Measure (Fin n → Fin M → R ⊗[F] E)) m', μ'.IsAddHaarMeasure → IsGramFib R σ J' n μ' ν m' → ∀ g : GL (Fin M) (R ⊗[F] E), JR R J' = cT (sigR R σ) (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J * (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) → ∀ a : ℝ≥0, μ'.map (actTup R g) = a • μ → ∀ S, (m' S).map (actTup R g) = a • m S := by
  first | exact @GlobalTheory.CompanionTheory.SW.LocIsom.fibre_map_isometry | exact GlobalTheory.CompanionTheory.SW.LocIsom.fibre_map_isometry | (intros; apply GlobalTheory.CompanionTheory.SW.LocIsom.fibre_map_isometry <;> assumption)
end
end
