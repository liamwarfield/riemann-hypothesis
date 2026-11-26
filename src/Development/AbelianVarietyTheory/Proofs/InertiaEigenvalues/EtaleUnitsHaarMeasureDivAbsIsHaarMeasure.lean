module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousDistribHaarCharUnits
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletedLatticeStabilizerCompactOpen
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankH1DualPair
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CupProductFiniteClassesCoboundary
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateDualityDegreeOneContinuousCocycles
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankH1fDeRham

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleUnitsHaarMeasureDivAbsIsHaarMeasure
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleUnitsHaarMeasureDivAbsIsHaarMeasure
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open scoped NNReal ENNReal Pointwise

noncomputable section

namespace GlobalTheory.JR.UnitsHaar

theorem secondCountable_base (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] : SecondCountableTopology F := by
  haveI : LocallyCompactSpace F := @Unram.lcF F E _ _ _ _ ‹_›
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F (E := F)
  infer_instance

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  [Unram F E] (A : Et F E)

theorem top_K : T2Space A.K ∧ SecondCountableTopology A.K := by
  haveI := secondCountable_base F E
  let e := (Module.finBasis F A.K).equivFun
  have h1 : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have h2 : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  let h : A.K ≃ₜ (Fin _ → F) := ⟨e.toEquiv, h1, h2⟩
  exact ⟨h.isEmbedding.t2Space, h.isEmbedding.isInducing.secondCountableTopology⟩

omit [Unram F E] in
theorem openUnits : IsOpenUnits A.K :=
  GlobalTheory.GaugeEx.isOpenUnits_of_basis (Module.finBasis F A.K)

omit [Unram F E] in
theorem absK_eq (t : A.K) : A.absK t = (GlobalTheory.GaugeEx.modu A.K t : ℝ) := by
  unfold Et.absK GlobalTheory.GaugeEx.modu; split_ifs <;> simp

omit [Unram F E] in
theorem borel_units : BorelSpace A.Kˣ := by
  have hemb := (openUnits A).isOpenEmbedding_unitsVal
  refine ⟨?_⟩
  rw [hemb.isEmbedding.isInducing.eq_induced, borel_comap, ← BorelSpace.measurable_eq]
  rfl

omit [Unram F E] in
theorem modu_mul_left (c : A.Kˣ) (t : A.K) :
    GlobalTheory.GaugeEx.modu A.K ((c : A.K) * t) = GlobalTheory.GaugeEx.modu A.K c * GlobalTheory.GaugeEx.modu A.K t := by
  classical
  by_cases ht : IsUnit t
  · obtain ⟨u, rfl⟩ := ht
    rw [← Units.val_mul, GlobalTheory.GaugeEx.modu_units, GlobalTheory.GaugeEx.modu_units, GlobalTheory.GaugeEx.modu_units, map_mul]
  · have hct : ¬ IsUnit ((c : A.K) * t) := fun h => ht (IsUnit.mul_iff.1 h).2
    simp [GlobalTheory.GaugeEx.modu, ht, hct]

omit [Unram F E] in
theorem modu_units_inv (u : A.Kˣ) :
    (GlobalTheory.GaugeEx.modu A.K u)⁻¹ = distribHaarChar A.K u⁻¹ := by
  rw [GlobalTheory.GaugeEx.modu_units, map_inv]

def dens (t : A.K) : ℝ≥0 := (GlobalTheory.GaugeEx.modu A.K t)⁻¹

omit [Unram F E] in
theorem unitsMeas_eq (μK : Measure A.K) :
    LinDesc.unitsMeas A μK = (μK.withDensity fun t => (dens A t : ℝ≥0∞)).comap Units.val := by
  have : ∀ t, ENNReal.ofReal (A.absK t)⁻¹ = (dens A t : ℝ≥0∞) := fun t => by
    rw [absK_eq, dens, ← NNReal.coe_inv, ENNReal.ofReal_coe_nnreal]
  unfold LinDesc.unitsMeas
  simp only [this]

theorem finiteRing_sq_sub_mul_sq_eq_of_card (μK : Measure A.K) (hμ : μK.IsAddHaarMeasure) :
    BorelSpace A.Kˣ ∧ (LinDesc.unitsMeas A μK).IsHaarMeasure ∧ ∀ h : A.K → ℂ,
      ∫ s, h (s : A.K) ∂(LinDesc.unitsMeas A μK) = ∫ t in {t : A.K | IsUnit t}, h t * ((A.absK t : ℂ))⁻¹ ∂μK := by
  classical
  obtain ⟨hT2, hSC⟩ := top_K A
  have hOU := openUnits A
  haveI hB := borel_units A
  have hemb := hOU.isOpenEmbedding_unitsVal
  have hme : MeasurableEmbedding (Units.val : A.Kˣ → A.K) := hemb.measurableEmbedding
  have hU : IsOpen {t : A.K | IsUnit t} := hemb.isOpen_range
  have hmod : Measurable (GlobalTheory.GaugeEx.modu A.K) := by
    have hc := (GlobalTheory.GaugeEx.modu_basic A.K).2.2.2 hOU
    have := hc.measurable_piecewise (g := fun _ => 0) continuousOn_const hU.measurableSet
    convert this using 1
    funext u
    by_cases hu : IsUnit u
    · simp [Set.piecewise, hu]
    · simp [Set.piecewise, GlobalTheory.GaugeEx.modu, hu]
  have hdm : Measurable (dens A) := hmod.inv
  set ν := μK.withDensity fun t => (dens A t : ℝ≥0∞) with hν
  rw [unitsMeas_eq]
  refine ⟨hB, ?_, ?_⟩
  swap
  · intro h
    have hr : Set.range (Units.val : A.Kˣ → A.K) = {t : A.K | IsUnit t} := Set.ext fun _ => Iff.rfl
    rw [← hme.integral_map, hme.map_comap, hr, restrict_withDensity hU.measurableSet,
      integral_withDensity_eq_integral_smul hdm]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    simp only
    rw [NNReal.smul_def, Complex.real_smul, absK_eq, dens, NNReal.coe_inv, Complex.ofReal_inv, mul_comm]
  haveI := hμ
  have hc0 : ∀ c : A.Kˣ, 0 < GlobalTheory.GaugeEx.modu A.K c := fun c => ((GlobalTheory.GaugeEx.modu_basic A.K).1 c c.isUnit).1
  have hscale : ∀ (c : A.Kˣ) (G : A.K → ℝ≥0∞),
      ∫⁻ t, G t ∂μK = (GlobalTheory.GaugeEx.modu A.K c : ℝ≥0∞) * ∫⁻ t, G ((c : A.K) * t) ∂μK := by
    intro c G
    have e := ((GlobalTheory.GaugeEx.modu_basic A.K).1 c c.isUnit).2 μK hμ
    have hm : MeasurableEmbedding (fun z : A.K => (c : A.K) * z) := (Homeomorph.smul c).measurableEmbedding
    conv_lhs => rw [e]
    rw [lintegral_smul_measure, hm.lintegral_map]
    rfl
  have hinv : ∀ (c : A.Kˣ) (T : Set A.K), MeasurableSet T → ν ((fun t => (c : A.K) * t) ⁻¹' T) = ν T := by
    intro c T hT
    have hT' : MeasurableSet ((fun t => (c : A.K) * t) ⁻¹' T) := (measurable_const_mul _) hT
    rw [hν, withDensity_apply _ hT, withDensity_apply _ hT', ← lintegral_indicator hT, ← lintegral_indicator hT']
    conv_rhs => rw [hscale c]
    rw [← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
    refine lintegral_congr fun t => ?_
    by_cases ht : (c : A.K) * t ∈ T
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem (show t ∈ (fun t => (c : A.K) * t) ⁻¹' T from ht)]
      rw [← ENNReal.coe_mul, ENNReal.coe_inj, dens, dens, modu_mul_left, mul_inv, ← mul_assoc,
        mul_inv_cancel₀ (hc0 c).ne', one_mul]
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem (show t ∉ (fun t => (c : A.K) * t) ⁻¹' T from ht),
        mul_zero]
  have hL : (ν.comap Units.val).IsMulLeftInvariant := by
    refine ⟨fun c => ?_⟩
    ext S hS
    rw [Measure.map_apply (measurable_const_mul c) hS, hme.comap_apply, hme.comap_apply]
    have hset : Units.val '' ((fun x => c * x) ⁻¹' S) = (fun t : A.K => (c : A.K) * t) ⁻¹' (Units.val '' S) := by
      ext t; constructor
      · rintro ⟨u, hu, rfl⟩; exact ⟨c * u, hu, Units.val_mul c u⟩
      · rintro ⟨s, hs, hst⟩
        refine ⟨c⁻¹ * s, by simpa [Set.mem_preimage] using hs, ?_⟩
        rw [Units.val_mul, hst, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
    rw [hset, hinv c _ (hme.measurableSet_image.2 hS)]
  have hF : IsFiniteMeasureOnCompacts (ν.comap Units.val) := by
    refine ⟨fun C hC => ?_⟩
    rw [hme.comap_apply]
    have hcont : Continuous fun u : A.Kˣ => distribHaarChar A.K u⁻¹ :=
      (GlobalTheory.GaugeEx.continuous_distribHaarChar_units A.K).comp continuous_inv
    obtain ⟨M, hM⟩ := (hC.image hcont).bddAbove
    have hC' : IsCompact (Units.val '' C) := hC.image Units.continuous_val
    calc ν (Units.val '' C) = ∫⁻ t in Units.val '' C, (dens A t : ℝ≥0∞) ∂μK :=
          withDensity_apply _ hC'.measurableSet
      _ ≤ ∫⁻ t in Units.val '' C, (M : ℝ≥0∞) ∂μK := by
          refine setLIntegral_mono measurable_const fun t ht => ?_
          obtain ⟨u, hu, rfl⟩ := ht
          rw [ENNReal.coe_le_coe, dens, modu_units_inv]
          exact hM ⟨u, hu, rfl⟩
      _ = M * μK (Units.val '' C) := setLIntegral_const _ _
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.coe_lt_top hC'.measure_lt_top
  have hP : (ν.comap Units.val).IsOpenPosMeasure := by
    refine ⟨fun U hUo hne => ?_⟩
    rw [hme.comap_apply]
    have hVo : IsOpen (Units.val '' U) := hemb.isOpenMap U hUo
    intro h0
    rw [hν, withDensity_apply _ hVo.measurableSet, lintegral_eq_zero_iff hdm.coe_nnreal_ennreal] at h0
    have h1 : ∀ᵐ t ∂(μK.restrict (Units.val '' U)), False := by
      filter_upwards [h0, ae_restrict_mem hVo.measurableSet] with t ht hV
      obtain ⟨u, -, rfl⟩ := hV
      have : (dens A u : ℝ≥0∞) ≠ 0 := by
        rw [ENNReal.coe_ne_zero, dens, modu_units_inv]; exact distribHaarChar_pos.ne'
      exact this (by simpa using ht)
    have h2 : μK.restrict (Units.val '' U) = 0 := ae_eq_bot.1 (eventually_false_iff_eq_bot.1 h1)
    rw [Measure.restrict_eq_zero] at h2
    exact (hVo.measure_pos μK (hne.image _)).ne' h2
  exact { toIsFiniteMeasureOnCompacts := hF, toIsMulLeftInvariant := hL, toIsOpenPosMeasure := hP }

end GlobalTheory.JR.UnitsHaar

namespace GlobalTheory.JR.LinDesc

theorem unitsMeas_isHaar : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (μK : Measure A.K), μK.IsAddHaarMeasure → BorelSpace A.Kˣ ∧ (LinDesc.unitsMeas A μK).IsHaarMeasure ∧ ∀ h : A.K → ℂ, ∫ s, h (s : A.K) ∂(LinDesc.unitsMeas A μK) = ∫ t in {t : A.K | IsUnit t}, h t * ((A.absK t : ℂ))⁻¹ ∂μK :=
  fun _ _ _ _ _ _ _ A μK hμ => GlobalTheory.JR.UnitsHaar.finiteRing_sq_sub_mul_sq_eq_of_card A μK hμ

end GlobalTheory.JR.LinDesc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleUnitsHaarMeasureDivAbsIsHaarMeasureStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleUnitsHaarMeasureDivAbs_isHaarMeasure : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (μK : Measure A.K), μK.IsAddHaarMeasure → BorelSpace A.Kˣ ∧ (LinDesc.unitsMeas A μK).IsHaarMeasure ∧ ∀ h : A.K → ℂ, ∫ s, h (s : A.K) ∂(LinDesc.unitsMeas A μK) = ∫ t in {t : A.K | IsUnit t}, h t * ((A.absK t : ℂ))⁻¹ ∂μK := by
  first | exact @GlobalTheory.JR.LinDesc.unitsMeas_isHaar | exact GlobalTheory.JR.LinDesc.unitsMeas_isHaar | (intros; apply GlobalTheory.JR.LinDesc.unitsMeas_isHaar <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IteratedColumnTransformEqGlobalWhittaker
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IteratedColumnTransformEqGlobalWhittaker
open NumberField Matrix GlobalTheory.CuspRep

noncomputable section

open MeasureTheory GroundTheory.Automorphic.FourierWhittaker

namespace GlobalTheory.CuspGeneric.WhitEq

theorem avg_eq_setIntegral {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [m : MeasurableSpace G] [hB : BorelSpace G]
    (Γ : AddSubgroup G) [Countable Γ] (μ : Measure G) [μ.IsAddHaarMeasure] (D : Set G)
    (hD : IsAddFundamentalDomain Γ D μ) (h1 : μ D = 1) (Φ : G → ℂ)
    (hΦ : ∀ γ ∈ Γ, ∀ x, Φ (γ + x) = Φ x) :
    avg Γ Φ = ∫ x in D, Φ x ∂μ := by
  obtain ⟨rfl⟩ := hB
  letI : MeasurableSpace G := borel G
  haveI : BorelSpace G := ⟨rfl⟩
  have hex : ∃ p : Measure G × Set G, p.1.IsAddHaarMeasure ∧ IsAddFundamentalDomain Γ p.2 p.1 ∧ p.1 p.2 = 1 :=
    ⟨(μ, D), inferInstance, hD, h1⟩
  unfold avg
  rw [dite_eq_left hex]
  obtain ⟨hH, hD', h1'⟩ := hex.choose_spec
  set ν := hex.choose.1
  set D' := hex.choose.2
  have hν : ν = Measure.addHaarScalarFactor ν μ • μ := Measure.isAddLeftInvariant_eq_smul ν μ
  have hc0 : Measure.addHaarScalarFactor ν μ ≠ 0 := by
    intro h0
    have : ν = 0 := by rw [hν, h0, zero_smul]
    have hpos : 0 < ν Set.univ := IsOpen.measure_pos ν isOpen_univ ⟨0, trivial⟩
    rw [this] at hpos
    simp at hpos
  have hac : μ ≪ ν := by
    rw [hν]
    exact Measure.absolutelyContinuous_smul (by exact_mod_cast hc0)
  have hDμ : IsAddFundamentalDomain Γ D' μ := hD'.mono hac
  have hμD' : μ D' = 1 := by rw [hDμ.measure_eq hD, h1]
  have hc1 : Measure.addHaarScalarFactor ν μ = 1 := by
    have := h1'
    rw [hν, Measure.smul_apply, hμD', ENNReal.smul_def, smul_eq_mul, mul_one] at this
    exact_mod_cast this
  have hνμ : ν = μ := by rw [hν, hc1, one_smul]
  rw [hνμ]
  exact hDμ.setIntegral_eq hD fun g x => hΦ g g.2 x

def colIx {a k : ℕ} (hk : k < a) : UnipotentBlockColumnIndex a k k ≃ Fin k where
  toFun t := ⟨t.1.1.val, t.2.1⟩
  invFun i := ⟨(⟨i.val, by omega⟩, ⟨k, hk⟩), i.2, le_rfl, le_rfl⟩
  left_inv t := by
    obtain ⟨⟨i, j⟩, h1, h2, h3⟩ := t
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Fin.ext
      show k = (j : ℕ)
      simp only at h2 h3
      omega
  right_inv i := rfl

theorem blkU_eq_colGL {R : Type} [CommRing R] {a k : ℕ} (hk : k < a) (x : UnipotentBlockColumnIndex a k k → R) :
    (blkU x : GL (Fin a) R) = colGL (n := a) k (fun i => x ((colIx hk).symm i)) := by
  apply Units.ext
  ext i j
  change (1 + posM Subtype.val x : Matrix (Fin a) (Fin a) R) i j = uMat (colX (n := a) k _) i j
  rw [uMat_apply, Matrix.add_apply, posM, Matrix.sum_apply, Matrix.one_apply]
  by_cases hij : (i : ℕ) < k ∧ (j : ℕ) = k
  · have hne : i ≠ j := fun h => by rw [h] at hij; omega
    have hlt : i < j := by rw [Fin.lt_def]; omega
    rw [Finset.sum_eq_single (⟨(i, j), hij.1, hij.2.ge, hij.2.le⟩ : UnipotentBlockColumnIndex a k k)]
    · rw [if_neg hne, if_neg hne, dite_eq_left hlt, colX_apply, dite_eq_left hij.2, Matrix.single_apply_same, zero_add]
      congr 1
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · apply Fin.ext
        show (j : ℕ) = k
        exact hij.2
    · intro t _ ht
      rw [Matrix.single_apply_of_ne]
      rintro ⟨h1, h2⟩
      exact ht (Subtype.ext (Prod.ext h1 h2))
    · simp
  · rw [Finset.sum_eq_zero]
    · rw [add_zero]
      split_ifs with h1 h2
      · rfl
      · rw [colX_apply, dite_eq_right]
        intro h3
        exact hij ⟨by rw [← h3]; exact h2, h3⟩
      · rfl
    · intro t _
      rw [Matrix.single_apply_of_ne]
      rintro ⟨h1, h2⟩
      apply hij
      have := t.2
      rw [← h1, ← h2]
      omega

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem dot_eLast {k : ℕ} (hk : k < a) (x : UnipotentBlockColumnIndex a k k → Ad E) :
    dot (eLast a k) x = pair (lastVec k) (fun i => x ((colIx hk).symm i)) := by
  unfold dot pair
  refine Fintype.sum_equiv (colIx hk) _ _ fun t => ?_
  dsimp only
  rw [Equiv.symm_apply_apply]
  rfl

theorem colT_eq_stepCoeff {k : ℕ} (hk : k < a) (f : GA E a → ℂ)
    (hf : ∀ (ξ : Fin k → E) g, f (ratGL E a (colGL k ξ) * g) = f g) (g : GA E a) :
    colT (Circle.coeHom.compAddChar (GroundTheory.Global.adelicChar E)) k f g = stepCoeff k f g := by
  set ψ₀ : AddChar (Ad E) ℂ := Circle.coeHom.compAddChar (GroundTheory.Global.adelicChar E)
  have hψ : ∀ y, ψ₀ y = (GroundTheory.Global.adelicChar E y : ℂ) := fun y => rfl
  set Φ : (UnipotentBlockColumnIndex a k k → Ad E) → ℂ := fun x => ψ₀ (-dot (eLast a k) x) * f (blkU x * g) with hΦdef
  have hΦ : ∀ γ ∈ ratV E (UnipotentBlockColumnIndex a k k), ∀ x, Φ (γ + x) = Φ x := by
    rintro _ ⟨c, rfl⟩ x
    have e1 : (AddMonoidHom.compLeft (algebraMap E (Ad E)).toAddMonoidHom (UnipotentBlockColumnIndex a k k)) c =
        fun t => algebraMap E (Ad E) (c t) := rfl
    rw [e1]
    have hU : f (blkU ((fun t => algebraMap E (Ad E) (c t)) + x) * g) = f (blkU x * g) := by
      change f (posU _ _ * g) = _
      rw [posU_add, mul_assoc]
      change f (blkU _ * _) = _
      rw [← ratGL_blkU, blkU_eq_colGL hk, hf]
      rfl
    have hD : dot (eLast a k) ((fun t => algebraMap E (Ad E) (c t)) + x) =
        algebraMap E (Ad E) (∑ t, eLast a k t * c t) + dot (eLast a k) x := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib, map_sum, map_mul]
    simp only [Φ]
    rw [hU, hD, neg_add, AddChar.map_add_eq_mul, hψ (-(algebraMap E (Ad E) _)), ← map_neg,
      GroundTheory.Global.adelicChar_algebraMap, Circle.coe_one, one_mul]
  haveI : Countable (ratV E (UnipotentBlockColumnIndex a k k)) := countable_vecLattice
  have hA : avg (ratV E (UnipotentBlockColumnIndex a k k)) Φ = ∫ x in vecDomain E (UnipotentBlockColumnIndex a k k), Φ x ∂vecMeasure E (UnipotentBlockColumnIndex a k k) :=
    avg_eq_setIntegral (ratV E (UnipotentBlockColumnIndex a k k)) (vecMeasure E (UnipotentBlockColumnIndex a k k)) (vecDomain E (UnipotentBlockColumnIndex a k k))
      isAddFundamentalDomain_vecDomain vecMeasure_vecDomain Φ hΦ
  change avg (ratV E (UnipotentBlockColumnIndex a k k)) Φ = _
  rw [hA]
  let Em := MeasurableEquiv.piCongrLeft (fun _ : Fin k => Ad E) (colIx hk)
  have hE : MeasurePreserving Em (vecMeasure E (UnipotentBlockColumnIndex a k k)) (vecMeasure E (Fin k)) :=
    measurePreserving_piCongrLeft (fun _ : Fin k => GroundTheory.Global.adeleMeasure E) (colIx hk)
  have hEx : ∀ x : UnipotentBlockColumnIndex a k k → Ad E, Em x = fun i => x ((colIx hk).symm i) := by
    intro x
    funext i
    simp [Em, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft]
  have hpre : Em ⁻¹' vecDomain E (Fin k) = vecDomain E (UnipotentBlockColumnIndex a k k) := by
    ext x
    simp only [Set.mem_preimage, hEx, vecDomain, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro h t
      have := h (colIx hk t)
      rwa [Equiv.symm_apply_apply] at this
    · intro h i
      exact h _
  rw [stepCoeff, vecCoeff, ← hE.setIntegral_preimage_emb Em.measurableEmbedding, hpre]
  refine setIntegral_congr_fun measurableSet_vecDomain fun x _ => ?_
  simp only [Φ, hEx, hψ]
  rw [blkU_eq_colGL hk, dot_eLast hk, mul_comm]

theorem whit_partialCoeff (F : GA E a → ℂ) (hl : ∀ (γ : GL (Fin a) E) (g : GA E a), F (ratGL E a γ * g) = F g) :
    ∀ m, m + 1 ≤ a → whit (Circle.coeHom.compAddChar (GroundTheory.Global.adelicChar E)) m (partialCoeff F (m + 1)) =
      partialCoeff F 1 := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
    intro hm
    have hk : m + 1 < a := by omega
    rw [whit_succ]
    have hcol : colT (Circle.coeHom.compAddChar (GroundTheory.Global.adelicChar E)) (m + 1) (partialCoeff F (m + 1 + 1)) =
        partialCoeff F (m + 1) := by
      funext g
      rw [colT_eq_stepCoeff hk _ (fun ξ g => partialCoeff_succ_diagonal_colGL (K := E) (n := a) hl hk ξ g),
        partialCoeff_of_lt F hk]
    rw [hcol]
    exact ih (by omega)

theorem whit_eq_whittaker : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (F : GA E a → ℂ), 0 < a → Continuous F →
    (∀ (γ : GL (Fin a) E) (g : GA E a), F (ratGL E a γ * g) = F g) →
    GlobalTheory.CuspGeneric.whit (Circle.coeHom.compAddChar (GroundTheory.Global.adelicChar E)) (a - 1) F = GlobalTheory.JSW.whit F := by
  intro E _ _ a F ha hc hl
  have h := whit_partialCoeff F hl (a - 1) (by omega)
  rw [Nat.sub_add_cancel ha, partialCoeff_self] at h
  rw [h]
  funext g
  exact (whittaker_eq_partialCoeff hc ha g).symm

end GlobalTheory.CuspGeneric.WhitEq
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IteratedColumnTransformEqGlobalWhittakerStatement
open NumberField Matrix GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iteratedColumnTransform_eq_globalWhittaker : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (F : GA E a → ℂ), 0 < a → Continuous F → (∀ (γ : GL (Fin a) E) (g : GA E a), F (ratGL E a γ * g) = F g) → GlobalTheory.CuspGeneric.whit (Circle.coeHom.compAddChar (GroundTheory.Global.adelicChar E)) (a - 1) F = GlobalTheory.JSW.whit F := by
  first | exact @GlobalTheory.CuspGeneric.WhitEq.whit_eq_whittaker | exact GlobalTheory.CuspGeneric.WhitEq.whit_eq_whittaker | (intros; apply GlobalTheory.CuspGeneric.WhitEq.whit_eq_whittaker <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoExactAnnihilatorsPeriodDatum
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoExactAnnihilatorsPeriodDatum
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.BlochKatoAnn

section Abstract

variable {k Z Z' : Type} [Field k] [AddCommGroup Z] [Module k Z] [AddCommGroup Z'] [Module k Z']
  [FiniteDimensional k Z] [FiniteDimensional k Z']

def rorth (β : Z →ₗ[k] Z' →ₗ[k] k) (W : Submodule k Z) : Submodule k Z' :=
  (W.map β).dualCoannihilator

theorem mem_rorth (β : Z →ₗ[k] Z' →ₗ[k] k) (W : Submodule k Z) (b : Z') :
    b ∈ rorth β W ↔ ∀ a ∈ W, β a b = 0 := by
  unfold rorth
  rw [Submodule.mem_dualCoannihilator]
  constructor
  · intro h a ha
    exact h _ ⟨a, ha, rfl⟩
  · rintro h _ ⟨a, ha, rfl⟩
    exact h a ha

theorem finrank_rorth (β : Z →ₗ[k] Z' →ₗ[k] k) (W : Submodule k Z) (hW : LinearMap.ker β ≤ W) :
    finrank k (rorth β W) + finrank k W = finrank k Z' + finrank k (LinearMap.ker β) := by
  have h1 := Subspace.finrank_add_finrank_dualCoannihilator_eq (W.map β)
  have h2 := LinearMap.finrank_range_add_finrank_ker (β.domRestrict W)
  have h3 : LinearMap.range (β.domRestrict W) = W.map β := by
    rw [LinearMap.range_domRestrict]
  have h4 : LinearMap.ker (β.domRestrict W) = (LinearMap.ker β).comap W.subtype := by
    rw [LinearMap.ker_domRestrict]
  have h5 : finrank k ((LinearMap.ker β).comap W.subtype) = finrank k (LinearMap.ker β) :=
    (Submodule.comapSubtypeEquivOfLe hW).finrank_eq
  rw [h3, h4, h5] at h2
  unfold rorth
  linarith

theorem rorth_top (β : Z →ₗ[k] Z' →ₗ[k] k) : rorth β ⊤ = LinearMap.ker β.flip := by
  ext b
  rw [mem_rorth, LinearMap.mem_ker]
  constructor
  · intro h
    ext a
    exact h a trivial
  · intro h a _
    have := LinearMap.congr_fun h a
    simpa using this

theorem exact_ann (β : Z →ₗ[k] Z' →ₗ[k] k) (W : Submodule k Z) (W' : Submodule k Z')
    (hW : LinearMap.ker β ≤ W) (hW' : LinearMap.ker β.flip ≤ W')
    (hort : ∀ a ∈ W, ∀ b ∈ W', β a b = 0)
    (hdim : finrank k W + finrank k W' = finrank k Z + finrank k (LinearMap.ker β.flip)) :
    rorth β W = W' ∧ rorth β.flip W' = W := by
  have hT := finrank_rorth β ⊤ (le_top)
  rw [rorth_top, finrank_top] at hT
  have hA := finrank_rorth β W hW
  have hB := finrank_rorth β.flip W' hW'
  have l1 : W' ≤ rorth β W := fun b hb => (mem_rorth β W b).2 fun a ha => hort a ha b hb
  have l2 : W ≤ rorth β.flip W' := fun a ha => (mem_rorth β.flip W' a).2 fun b hb => by
    rw [LinearMap.flip_apply]; exact hort a ha b hb
  constructor
  · exact (Submodule.eq_of_le_of_finrank_eq l1 (by omega)).symm
  · exact (Submodule.eq_of_le_of_finrank_eq l2 (by omega)).symm

end Abstract

end GlobalTheory.BlochKatoAnn

namespace GlobalTheory.BlochKatoAnn

section Concrete

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] {O : Type} [CommRing O]
    [Algebra O LL]

theorem galoisCoboundaries_le_continuousCocycles (A : GRep G Qp LL O) : B1 A.ρ ≤ continuousCocycles A.ρ := by
  rintro _ ⟨x, rfl⟩
  refine ⟨?_, fun g h => ?_⟩
  · have : (cob A.ρ x : G → A.V) = fun g => A.ρ g x + (-x) := by
      funext g
      simp [cob, sub_eq_add_neg]
    rw [this]
    exact (A.cont x).add continuous_const
  · simp only [cob, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply, map_mul,
      Module.End.mul_apply, map_sub]
    abel

theorem B1_le_Z1f (A : GRep G Qp LL O) : B1 A.ρ ≤ finiteCocycles PD A.ρ := by
  intro c hc
  refine ⟨galoisCoboundaries_le_continuousCocycles A hc, ?_⟩
  obtain ⟨x, rfl⟩ := hc
  refine ⟨x ⊗ₜ[Qp] (1 : B), fun g => ?_⟩
  simp [cob, actVB, sub_tmul]

theorem blochKatoFiniteCocycles_le_continuousCocycles (A : GRep G Qp LL O) : finiteCocycles PD A.ρ ≤ continuousCocycles A.ρ := fun _ h => h.1

theorem finite_continuous_cocycles_localGaloisRep (A : GRep G Qp LL O) (h : Module.Finite LL (H1V A.ρ)) :
    FiniteDimensional LL (continuousCocycles A.ρ) := by
  haveI : FiniteDimensional LL (B1 A.ρ) := LinearMap.finiteDimensional_range (cob A.ρ)
  have hK : FiniteDimensional LL ((B1 A.ρ).comap (continuousCocycles A.ρ).subtype) :=
    Module.Finite.equiv (Submodule.comapSubtypeEquivOfLe (galoisCoboundaries_le_continuousCocycles A)).symm
  show Module.Finite LL (continuousCocycles A.ρ)
  rw [Module.finite_def]
  apply Submodule.fg_of_fg_map_of_fg_inf_ker ((B1 A.ρ).comap (continuousCocycles A.ρ).subtype).mkQ
  · rw [Submodule.map_top, Submodule.range_mkQ]
    exact Module.finite_def.1 h
  · rw [top_inf_eq, Submodule.ker_mkQ]
    exact Module.Finite.iff_fg.1 hK

theorem finrank_H1V (A : GRep G Qp LL O) [FiniteDimensional LL (continuousCocycles A.ρ)] :
    finrank LL (H1V A.ρ) + finrank LL (B1 A.ρ) = finrank LL (continuousCocycles A.ρ) := by
  have e := Submodule.finrank_quotient_add_finrank ((B1 A.ρ).comap (continuousCocycles A.ρ).subtype)
  rw [(Submodule.comapSubtypeEquivOfLe (galoisCoboundaries_le_continuousCocycles A)).finrank_eq] at e
  exact e

theorem finrank_H1fV (A : GRep G Qp LL O) [FiniteDimensional LL (continuousCocycles A.ρ)] :
    finrank LL (FiniteCohomology PD A.ρ) + finrank LL (B1 A.ρ) =
      finrank LL ((finiteCocycles PD A.ρ).comap (continuousCocycles A.ρ).subtype) := by
  have eW := (Submodule.comapSubtypeEquivOfLe (blochKatoFiniteCocycles_le_continuousCocycles PD A))
  haveI : FiniteDimensional LL (finiteCocycles PD A.ρ) := Module.Finite.equiv eW
  have e := Submodule.finrank_quotient_add_finrank ((B1 A.ρ).comap (finiteCocycles PD A.ρ).subtype)
  rw [(Submodule.comapSubtypeEquivOfLe (B1_le_Z1f PD A)).finrank_eq] at e
  rw [eW.finrank_eq]
  exact e

end Concrete

end GlobalTheory.BlochKatoAnn

namespace GlobalTheory.BlochKatoAnn

theorem bkA_exact_annihilators : Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK →
    ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
      ∀ K : FinExt l, bkACore (P.PD K) := by
  intro hTD hEC l _ P AI hT K
  intro LL _ _ _ O _ _ hO A A' m hdr hdual
  have hdual' : IsDual1 (P.PD K) A'.ρ A.ρ m.flip := by
    obtain ⟨h1, h2, h3, h4⟩ := hdual
    refine ⟨fun g y x => ?_, fun y hy => h3 y hy, fun x hx => h2 x hx, h4.symm⟩
    simp only [LinearMap.flip_apply]
    exact h1 g x y
  obtain ⟨hdrd, hfd⟩ := GlobalTheory.T.de_rham_filtration_duality l P AI hT K
  have hdr' : IsDR (P.PD K) A'.ρ := hdrd LL O hO A A' m hdr hdual
  have hfil := hfd LL O hO A A' m hdr hdual
  obtain ⟨hH1fin, hH1⟩ := GlobalTheory.T.finrank_H1_dual_pair hTD hEC l P K LL O hO A A' m hdual
  obtain ⟨hH1fin', -⟩ := GlobalTheory.T.finrank_H1_dual_pair hTD hEC l P K LL O hO A' A m.flip hdual'
  obtain ⟨-, hf⟩ := GlobalTheory.T.finrank_H1f_de_rham l P AI hT K LL O hO A hdr
  obtain ⟨-, hf'⟩ := GlobalTheory.T.finrank_H1f_de_rham l P AI hT K LL O hO A' hdr'
  have hort := GlobalTheory.T.cup_product_finite_classes_coboundary l P AI hT K LL O hO A A' m hdr hdual
  obtain ⟨β, hβ, hl, hr⟩ := GlobalTheory.T.tateDuality_degreeOne_continuous_cocycles hTD l P K LL O hO A A' m hdual
  haveI := finite_continuous_cocycles_localGaloisRep A hH1fin
  haveI := finite_continuous_cocycles_localGaloisRep A' hH1fin'
  have hkl : LinearMap.ker β = (B1 A.ρ).comap (continuousCocycles A.ρ).subtype := by
    ext a
    rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply, ← hl a]
    constructor
    · intro h b
      rw [h]
      rfl
    · intro h
      ext b
      exact h b
  have hkr : LinearMap.ker β.flip = (B1 A'.ρ).comap (continuousCocycles A'.ρ).subtype := by
    ext b
    rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply, ← hr b]
    constructor
    · intro h a
      have := LinearMap.congr_fun h a
      simpa using this
    · intro h
      ext a
      simpa using h a
  have hW : LinearMap.ker β ≤ (finiteCocycles (P.PD K) A.ρ).comap (continuousCocycles A.ρ).subtype := by
    rw [hkl]
    exact Submodule.comap_mono (B1_le_Z1f (P.PD K) A)
  have hW' : LinearMap.ker β.flip ≤ (finiteCocycles (P.PD K) A'.ρ).comap (continuousCocycles A'.ρ).subtype := by
    rw [hkr]
    exact Submodule.comap_mono (B1_le_Z1f (P.PD K) A')
  have horth : ∀ a ∈ (finiteCocycles (P.PD K) A.ρ).comap (continuousCocycles A.ρ).subtype,
      ∀ b ∈ (finiteCocycles (P.PD K) A'.ρ).comap (continuousCocycles A'.ρ).subtype, β a b = 0 := by
    intro a ha b hb
    rw [hβ]
    exact hort a.1 ha b.1 hb
  have eZ := finrank_H1V A
  have eW := finrank_H1fV (P.PD K) A
  have eW' := finrank_H1fV (P.PD K) A'
  have eKl : finrank LL (LinearMap.ker β) = finrank LL (B1 A.ρ) := by
    rw [hkl]
    exact (Submodule.comapSubtypeEquivOfLe (galoisCoboundaries_le_continuousCocycles A)).finrank_eq
  have eKr : finrank LL (LinearMap.ker β.flip) = finrank LL (B1 A'.ρ) := by
    rw [hkr]
    exact (Submodule.comapSubtypeEquivOfLe (galoisCoboundaries_le_continuousCocycles A')).finrank_eq
  have hdV := hdual.2.2.2
  unfold IsDR at hdr hdr'
  rw [← hdV] at hdr'
  have hdim : finrank LL ((finiteCocycles (P.PD K) A.ρ).comap (continuousCocycles A.ρ).subtype) +
      finrank LL ((finiteCocycles (P.PD K) A'.ρ).comap (continuousCocycles A'.ρ).subtype) =
      finrank LL (continuousCocycles A.ρ) + finrank LL (LinearMap.ker β.flip) := by
    rw [eKr]
    zify at eZ eW eW' hH1 hfil hdr hdr' ⊢
    linarith
  obtain ⟨h1, h2⟩ := exact_ann β _ _ hW hW' horth hdim
  constructor
  · intro a ha
    change (⟨a, ha⟩ : continuousCocycles A.ρ) ∈ (finiteCocycles (P.PD K) A.ρ).comap (continuousCocycles A.ρ).subtype ↔ _
    rw [← h2, mem_rorth]
    constructor
    · intro h b hb
      have := h ⟨b, hb.1⟩ hb
      rw [LinearMap.flip_apply, hβ] at this
      exact this
    · intro h b hb
      rw [LinearMap.flip_apply, hβ]
      exact h b.1 hb
  · intro b hb
    change (⟨b, hb⟩ : continuousCocycles A'.ρ) ∈ (finiteCocycles (P.PD K) A'.ρ).comap (continuousCocycles A'.ρ).subtype ↔ _
    rw [← h1, mem_rorth]
    constructor
    · intro h a ha
      have := h ⟨a, ha.1⟩ ha
      rw [hβ] at this
      exact this
    · intro h a ha
      rw [hβ]
      exact h a.1 ha

end GlobalTheory.BlochKatoAnn
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoExactAnnihilatorsPeriodDatumStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blochKato_exact_annihilators_periodDatum : Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ K : FinExt l, bkACore (P.PD K) := by
  first | exact @GlobalTheory.BlochKatoAnn.bkA_exact_annihilators | exact GlobalTheory.BlochKatoAnn.bkA_exact_annihilators | (intros; apply GlobalTheory.BlochKatoAnn.bkA_exact_annihilators <;> assumption)
end
end
