module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsZeroLocusDimH
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PPiQuotCokerFiniteLength
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem PiQuotCokerFiniteLength.proof : PiQuotCokerFiniteLength.Statement := by
  intro B _ _ _ J hJ hQ
  have : Finite J.minimalPrimes := (J.finite_minimalPrimes_of_isNoetherianRing B).to_subtype
  let : Fintype J.minimalPrimes := Fintype.ofFinite _
  classical
  have hfac : ∀ (P : J.minimalPrimes) (x : B),
      quotToPiMinimalPrimes J (Submodule.Quotient.mk x) P = Ideal.Quotient.mk (P : Ideal B) x :=
    fun _ _ => rfl
  refine ⟨(injective_iff_map_eq_zero _).mpr fun y hy => ?_, ?_⟩
  · obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    have hxP : ∀ P : J.minimalPrimes, x ∈ (P : Ideal B) := fun P => by
      have h1 := congrFun hy P
      rwa [hfac, Pi.zero_apply, Ideal.Quotient.eq_zero_iff_mem] at h1
    have hx : x ∈ sInf J.minimalPrimes := Submodule.mem_sInf.mpr fun p hp => hxP ⟨p, hp⟩
    rw [Ideal.sInf_minimalPrimes, hJ.radical] at hx
    exact (Submodule.Quotient.mk_eq_zero _).mpr hx

  have hkey : ∀ Q : Ideal B, Q.IsPrime → ∀ P P' : J.minimalPrimes, P ≠ P' →
      (P : Ideal B) ≤ Q → (P' : Ideal B) ≤ Q → Q = IsLocalRing.maximalIdeal B := by
    intro Q hQp P P' hne hPQ hP'Q
    rcases hQ Q hQp (P.2.1.2.trans hPQ) with hmin | hm
    · exfalso
      apply hne
      have e1 : (P : Ideal B) = Q := le_antisymm hPQ (hmin.2 P.2.1 hPQ)
      have e2 : (P' : Ideal B) = Q := le_antisymm hP'Q (hmin.2 P'.2.1 hP'Q)
      exact Subtype.ext (e1.trans e2.symm)
    · exact hm
  let IP : J.minimalPrimes → Ideal B := fun P =>
    (Finset.univ.filter (· ≠ P)).inf fun P' : J.minimalPrimes => (P' : Ideal B)
  let I : Ideal B := Finset.univ.inf fun P => IP P ⊔ (P : Ideal B)
  have hI : ∀ Q : Ideal B, Q.IsPrime → I ≤ Q → Q = IsLocalRing.maximalIdeal B := by
    intro Q hQp hIQ
    obtain ⟨P, -, hPQ⟩ := hQp.inf_le'.mp hIQ
    obtain ⟨P', hP', hP'Q⟩ := hQp.inf_le'.mp (le_sup_left.trans hPQ)
    exact hkey Q hQp P P' (Finset.mem_filter.mp hP').2.symm (le_sup_right.trans hPQ) hP'Q
  have htors : Module.IsTorsionBySet B
      (((P : J.minimalPrimes) → B ⧸ (P : Ideal B)) ⧸ LinearMap.range (quotToPiMinimalPrimes J))
      (I : Set B) := by
    intro c z
    obtain ⟨y, hy⟩ := z
    show y • c = 0
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ c
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    have hyP : ∀ P, y ∈ IP P ⊔ (P : Ideal B) := fun P =>
      Submodule.mem_finsetInf.mp hy P (Finset.mem_univ _)
    choose a ha b hb hab using fun P => Submodule.mem_sup.mp (hyP P)
    choose x hx using fun P => Ideal.Quotient.mk_surjective (v P)
    refine ⟨Submodule.Quotient.mk (∑ P, a P * x P), ?_⟩
    funext Q
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hfac, Pi.smul_apply, ← hx Q, map_sum, Finset.sum_eq_single Q]
    · rw [← hab Q, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, map_add (f := _), map_mul,
        Ideal.Quotient.eq_zero_iff_mem.mpr (hb Q), add_zero]
    · intro P _ hPQ
      have hle : IP P ≤ (Q : Ideal B) :=
        Finset.inf_le (Finset.mem_filter.mpr ⟨Finset.mem_univ Q, hPQ.symm⟩)
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_mem_right _ _ (hle (ha P)))
    · intro h
      exact absurd (Finset.mem_univ Q) h
  by_cases hItop : I = ⊤
  · haveI : Subsingleton
        (((P : J.minimalPrimes) → B ⧸ (P : Ideal B)) ⧸ LinearMap.range (quotToPiMinimalPrimes J)) :=
      ⟨fun c d => by
        have hc := @htors c ⟨1, by rw [hItop]; trivial⟩
        have hd := @htors d ⟨1, by rw [hItop]; trivial⟩
        rw [one_smul] at hc hd
        rw [hc, hd]⟩
    exact IsFiniteLength.of_subsingleton
  have hmax : IsLocalRing.maximalIdeal B ∈ I.minimalPrimes :=
    ⟨⟨inferInstance, IsLocalRing.le_maximalIdeal hItop⟩, fun q hq _ => (hI q hq.1 hq.2).ge⟩
  have : IsArtinianRing (B ⧸ I) :=
    IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing I hmax
  rw [isFiniteLength_iff_isNoetherian_isArtinian]
  refine ⟨inferInstance, ?_⟩
  let := htors.module
  have : IsScalarTower B (B ⧸ I)
      (((P : J.minimalPrimes) → B ⧸ (P : Ideal B)) ⧸ LinearMap.range (quotToPiMinimalPrimes J)) :=
    htors.isScalarTower
  have : Module.Finite (B ⧸ I)
      (((P : J.minimalPrimes) → B ⧸ (P : Ideal B)) ⧸ LinearMap.range (quotToPiMinimalPrimes J)) :=
    Module.Finite.of_restrictScalars_finite B _ _
  have : IsArtinian (B ⧸ I)
      (((P : J.minimalPrimes) → B ⧸ (P : Ideal B)) ⧸ LinearMap.range (quotToPiMinimalPrimes J)) :=
    isArtinian_of_fg_of_artinian'
  exact isArtinian_of_surjective_algebraMap (R := B ⧸ I) Ideal.Quotient.mk_surjective

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.SphereMeanVol
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Measure Set
open scoped Pointwise

noncomputable section

namespace SphereMean

theorem setAverage_smul_measure {α : Type*} [MeasurableSpace α] (μ : Measure α) {c : ENNReal}
    (hc0 : c ≠ 0) (hct : c ≠ ⊤) (s : Set α) (g : α → ℝ) :
    ⨍ x in s, g x ∂(c • μ) = ⨍ x in s, g x ∂μ := by
  have hc : 0 < c.toReal := ENNReal.toReal_pos hc0 hct
  rw [setAverage_eq, setAverage_eq, Measure.restrict_smul, integral_smul_measure, measureReal_def,
    measureReal_def]
  simp only [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul]
  rw [mul_inv]
  field_simp

section Linear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

theorem setAverage_comp_linearEquiv (μ : Measure E) [μ.IsAddHaarMeasure] (ν : Measure F)
    [ν.IsAddHaarMeasure] (L : E ≃L[ℝ] F) (s : Set F) (g : F → ℝ) :
    ⨍ x in L ⁻¹' s, g (L x) ∂μ = ⨍ y in s, g y ∂ν := by
  have hmap : (map L μ).IsAddHaarMeasure := L.isAddHaarMeasure_map μ
  have hmp : MeasurePreserving L μ (map L μ) := ⟨L.continuous.measurable, rfl⟩
  have he : MeasurableEmbedding L := L.toHomeomorph.measurableEmbedding
  have h1 : ⨍ x in L ⁻¹' s, g (L x) ∂μ = ⨍ y in s, g y ∂(map L μ) := by
    rw [setAverage_eq, setAverage_eq, hmp.setIntegral_preimage_emb he, measureReal_def,
      measureReal_def, he.map_apply]
  have h2 : map L μ = addHaarScalarFactor (map L μ) ν • ν := isAddLeftInvariant_eq_smul _ _
  have hpos := addHaarScalarFactor_pos_of_isAddHaarMeasure (map L μ) ν
  rw [h1, h2]
  rw [show (addHaarScalarFactor (map L μ) ν • ν) =
      ((addHaarScalarFactor (map L μ) ν : ENNReal) • ν) from rfl]
  exact setAverage_smul_measure ν (by simpa using hpos.ne') ENNReal.coe_ne_top s g

end Linear

def sqNorm {n : ℕ} (x : Fin n → ℂ) : ℝ := ∑ j, ‖x j‖ ^ 2

def ballSet (n : ℕ) (s : ℝ) : Set (Fin n → ℂ) := {x | sqNorm x < s}

theorem sqNorm_nonneg {n : ℕ} (x : Fin n → ℂ) : 0 ≤ sqNorm x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem continuous_sqNorm (n : ℕ) : Continuous (sqNorm (n := n)) := by
  unfold sqNorm
  fun_prop

theorem measurable_sqNorm (n : ℕ) : Measurable (sqNorm (n := n)) :=
  (continuous_sqNorm n).measurable

theorem isOpen_ballSet (n : ℕ) (s : ℝ) : IsOpen (ballSet n s) :=
  isOpen_lt (continuous_sqNorm n) continuous_const

theorem measurableSet_ballSet (n : ℕ) (s : ℝ) : MeasurableSet (ballSet n s) :=
  (isOpen_ballSet n s).measurableSet

theorem sqNorm_smul {n : ℕ} (c : ℝ) (x : Fin n → ℂ) : sqNorm (c • x) = c ^ 2 * sqNorm x := by
  simp only [sqNorm, Pi.smul_apply, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, Finset.mul_sum]

theorem ballSet_eq_smul {n : ℕ} {s : ℝ} (hs : 0 < s) : ballSet n s = √s • ballSet n 1 := by
  have h : 0 < √s := Real.sqrt_pos.mpr hs
  ext x
  rw [mem_smul_set_iff_inv_smul_mem₀ h.ne']
  simp only [ballSet, mem_ofPred_eq, sqNorm_smul, inv_pow, Real.sq_sqrt hs.le]
  rw [inv_mul_lt_iff₀ hs, mul_one]

theorem finrank_fun_complex (n : ℕ) : Module.finrank ℝ (Fin n → ℂ) = 2 * n := by
  rw [Module.finrank_pi_fintype]
  simp [Complex.finrank_real_complex, mul_comm]

theorem volume_ballSet {n : ℕ} {s : ℝ} (hs : 0 < s) :
    volume (ballSet n s) = ENNReal.ofReal (s ^ n) * volume (ballSet n 1) := by
  rw [ballSet_eq_smul hs, addHaar_smul, finrank_fun_complex, pow_mul, Real.sq_sqrt hs.le,
    abs_of_nonneg (pow_nonneg hs.le n)]

theorem ballSet_subset_closedBall (n : ℕ) : ballSet n 1 ⊆ Metric.closedBall 0 1 := by
  intro x hx
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
  intro j
  have h1 : ‖x j‖ ^ 2 ≤ sqNorm x :=
    Finset.single_le_sum (f := fun j => ‖x j‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
  have h2 : ‖x j‖ ^ 2 < 1 := lt_of_le_of_lt h1 hx
  nlinarith [norm_nonneg (x j)]

theorem volume_ballSet_one_ne_top (n : ℕ) : volume (ballSet n 1) ≠ ⊤ :=
  (measure_mono (ballSet_subset_closedBall n)).trans_lt measure_closedBall_lt_top |>.ne

theorem volume_ballSet_one_pos (n : ℕ) : 0 < volume (ballSet n 1) :=
  (isOpen_ballSet n 1).measure_pos volume ⟨0, by simp [ballSet, sqNorm]⟩

end SphereMean

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsAreaFormulaInj
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Module

open scoped ENNReal

def AreaFormulaInj.Statement : Prop :=
  ∀ (E F : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] (k : ℕ),
    finrank ℝ E = k →
    ∀ (U A : Set E) (f : E → F) (g : F → ℝ≥0∞),
      IsOpen U → ContDiffOn ℝ 1 f U → A ⊆ U → MeasurableSet A → Set.InjOn f A → Measurable g →
        ∫⁻ y in f '' A, g y ∂(μH[(k : ℝ)]) =
          ∫⁻ x in A, g (f x) * ENNReal.ofReal (areaJacobian (fderiv ℝ f x : E →ₗ[ℝ] F))
            ∂(μH[(k : ℝ)])

end GroundTheory.Heights₂.Heights
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsAreaFormulaLocal
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Module

open scoped ENNReal

def AreaFormulaLocal.Statement : Prop :=
  ∀ (E F : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] (k : ℕ),
    finrank ℝ E = k →
    ∀ (U : Set E) (f : E → F) (x₀ : E),
      IsOpen U → ContDiffOn ℝ 1 f U → x₀ ∈ U → Function.Injective (fderiv ℝ f x₀) →
        ∃ V : Set E, IsOpen V ∧ x₀ ∈ V ∧ V ⊆ U ∧ ∀ B ⊆ V, MeasurableSet B →
          μH[(k : ℝ)] (f '' B) =
            ∫⁻ x in B, ENNReal.ofReal (areaJacobian (fderiv ℝ f x : E →ₗ[ℝ] F)) ∂(μH[(k : ℝ)])

end GroundTheory.Heights₂.Heights
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ChartGramHess
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open scoped InnerProductSpace
open Filter Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem ChartGram.hasFDerivAt_re_inner {u w : E → F} {y : E} {u' w' : E →L[ℝ] F}
    (hu : HasFDerivAt u u' y) (hw : HasFDerivAt w w' y) :
    HasFDerivAt (fun y' => (⟪u y', w y'⟫_ℂ).re)
      (Complex.reCLM.comp ((fderivInnerCLM ℂ (u y, w y)).comp (u'.prod w'))) y :=
  Complex.reCLM.hasFDerivAt.comp y (HasFDerivAt.inner ℂ hu hw)

theorem ChartGram.re_inner_self_pos {x : F} (h0 : x ≠ 0) : 0 < (⟪x, x⟫_ℂ).re := by
  have h := inner_self_eq_norm_sq (𝕜 := ℂ) x
  have h' : (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 := h
  rw [h']; positivity

theorem ChartGram.re_inner_comm (x z : F) : (⟪x, z⟫_ℂ).re = (⟪z, x⟫_ℂ).re := by
  rw [← inner_conj_symm x z, Complex.conj_re]

theorem ChartGram.fderiv_half_log_apply {u : E → F} {y : E}
    (hu : DifferentiableAt ℂ u y) (h0 : u y ≠ 0) (b : E) :
    fderiv ℝ (fun y' => 2⁻¹ * Real.log (⟪u y', u y'⟫_ℂ).re) y b =
      (⟪u y, fderiv ℂ u y b⟫_ℂ).re * ((⟪u y, u y⟫_ℂ).re)⁻¹ := by
  have h1 : HasFDerivAt u ((fderiv ℂ u y).restrictScalars ℝ) y := hu.hasFDerivAt.restrictScalars ℝ
  have h4 := HasFDerivAt.const_mul (HasFDerivAt.log (ChartGram.hasFDerivAt_re_inner h1 h1)
    (ChartGram.re_inner_self_pos h0).ne') 2⁻¹
  rw [h4.fderiv]
  simp only [FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, fderivInnerCLM_apply, ContinuousLinearMap.coe_restrictScalars',
    Complex.reCLM_apply, Complex.add_re, smul_eq_mul]
  rw [ChartGram.re_inner_comm (fderiv ℂ u y b)]
  ring

theorem ChartGram.hessian_half_log_apply [CompleteSpace F] {u : E → F} {y : E}
    (hu : ∀ᶠ y' in 𝓝 y, AnalyticAt ℂ u y') (h0 : u y ≠ 0) (a b : E) :
    fderiv ℝ (fderiv ℝ (fun y' => 2⁻¹ * Real.log (⟪u y', u y'⟫_ℂ).re)) y a b =
      ((⟪u y, fderiv ℂ (fderiv ℂ u) y a b⟫_ℂ).re + (⟪fderiv ℂ u y a, fderiv ℂ u y b⟫_ℂ).re) *
          ((⟪u y, u y⟫_ℂ).re)⁻¹ -
        (⟪u y, fderiv ℂ u y b⟫_ℂ).re * (2 * (⟪u y, fderiv ℂ u y a⟫_ℂ).re) *
          (((⟪u y, u y⟫_ℂ).re) ^ 2)⁻¹ := by
  set ψ : E → ℝ := fun y' => 2⁻¹ * Real.log (⟪u y', u y'⟫_ℂ).re with hψ
  have hy : AnalyticAt ℂ u y := hu.self_of_nhds
  have hN := ChartGram.re_inner_self_pos h0

  have hc : ContDiffAt ℝ 2 ψ y := by
    have hu2 : ContDiffAt ℝ 2 u y := (hy.contDiffAt (n := 2)).restrict_scalars ℝ
    have hi : ContDiffAt ℝ 2 (fun y' => (⟪u y', u y'⟫_ℂ).re) y :=
      Complex.reCLM.contDiff.contDiffAt.comp y (ContDiffAt.inner ℂ hu2 hu2)
    exact contDiffAt_const.mul (hi.log hN.ne')
  have hd : DifferentiableAt ℝ (fderiv ℝ ψ) y :=
    (hc.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h2 : fderiv ℝ (fderiv ℝ ψ) y a b = fderiv ℝ (fun y' => fderiv ℝ ψ y' b) y a := by
    rw [fderiv_clm_apply hd (differentiableAt_const b)]
    simp
  rw [h2]

  have hev : (fun y' => fderiv ℝ ψ y' b) =ᶠ[𝓝 y]
      fun y' => (⟪u y', fderiv ℂ u y' b⟫_ℂ).re * ((⟪u y', u y'⟫_ℂ).re)⁻¹ := by
    filter_upwards [hu, hy.continuousAt.eventually_ne h0] with y' h1 h2
    exact ChartGram.fderiv_half_log_apply h1.differentiableAt h2 b
  rw [hev.fderiv_eq]
  have hu1 : HasFDerivAt u ((fderiv ℂ u y).restrictScalars ℝ) y :=
    hy.differentiableAt.hasFDerivAt.restrictScalars ℝ
  have hW : HasFDerivAt (fun y' => fderiv ℂ u y' b)
      (((fderiv ℂ u y).comp (0 : E →L[ℂ] E) + (fderiv ℂ (fderiv ℂ u) y).flip b).restrictScalars ℝ) y :=
    (hy.fderiv.differentiableAt.hasFDerivAt.clm_apply (hasFDerivAt_const b y)).restrictScalars ℝ
  have hI := (hasDerivAt_inv hN.ne').comp_hasFDerivAt y (ChartGram.hasFDerivAt_re_inner hu1 hu1)
  have hg := HasFDerivAt.mul (ChartGram.hasFDerivAt_re_inner hu1 hW) hI
  have hg' : HasFDerivAt (fun y' => (⟪u y', fderiv ℂ u y' b⟫_ℂ).re * ((⟪u y', u y'⟫_ℂ).re)⁻¹) _ y := hg
  rw [hg'.fderiv]
  simp only [FunLike.coe_smul, Pi.smul_apply, add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, fderivInnerCLM_apply,
    ContinuousLinearMap.coe_restrictScalars', Complex.reCLM_apply, Complex.add_re, smul_eq_mul,
    zero_apply, map_zero, ContinuousLinearMap.flip_apply,
    zero_add, Function.comp_apply]
  rw [ChartGram.re_inner_comm (fderiv ℂ u y a) (u y)]
  ring


open ReciprocityTheory.ChartRestriction.G.Geo (cxHessian) in
theorem ChartGram.cxHessian_half_log [CompleteSpace F] {D : ℕ} {u : (Fin D → ℂ) → F}
    {y : Fin D → ℂ} (hu : ∀ᶠ y' in 𝓝 y, AnalyticAt ℂ u y') (h0 : u y ≠ 0) (i j : Fin D) :
    cxHessian (fun y' => 2⁻¹ * Real.log (⟪u y', u y'⟫_ℂ).re) y i j =
      (⟪u y, u y⟫_ℂ * ⟪fderiv ℂ u y (Pi.single j 1), fderiv ℂ u y (Pi.single i 1)⟫_ℂ -
          ⟪u y, fderiv ℂ u y (Pi.single i 1)⟫_ℂ * ⟪fderiv ℂ u y (Pi.single j 1), u y⟫_ℂ) /
        (2 * ⟪u y, u y⟫_ℂ ^ 2) := by
  have hN := ChartGram.re_inner_self_pos h0
  have hNc : ⟪u y, u y⟫_ℂ = ((⟪u y, u y⟫_ℂ).re : ℂ) := by
    rw [← inner_self_ofReal_re (𝕜 := ℂ)]; rfl
  unfold cxHessian
  simp only [ChartGram.hessian_half_log_apply hu h0, map_smul, smul_apply,
    inner_smul_right, inner_smul_left, Complex.conj_I]
  rw [← inner_conj_symm (fderiv ℂ u y (Pi.single j 1)) (u y),
    ← inner_conj_symm (fderiv ℂ u y (Pi.single j 1)) (fderiv ℂ u y (Pi.single i 1)), hNc]
  generalize ⟪u y, fderiv ℂ (fderiv ℂ u) y (Pi.single i 1) (Pi.single j 1)⟫_ℂ = Q
  generalize ⟪fderiv ℂ u y (Pi.single i 1), fderiv ℂ u y (Pi.single j 1)⟫_ℂ = P
  generalize ⟪u y, fderiv ℂ u y (Pi.single i 1)⟫_ℂ = p
  generalize ⟪u y, fderiv ℂ u y (Pi.single j 1)⟫_ℂ = q
  generalize (⟪u y, u y⟫_ℂ).re = N at hN ⊢
  have hN' : N ≠ 0 := hN.ne'
  apply Complex.ext <;>
    simp [sq, Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im] <;>
    field_simp <;> ring

end GroundTheory.Heights₂.Heights
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PKernelProjMeasurable
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Filter Topology ContinuousLinearMap

noncomputable section

namespace KernelProjMeasurable

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace E] [CompleteSpace F]

def shifted (A : E →L[ℂ] F) (ε : ℝ) : E →L[ℂ] E :=
  (ContinuousLinearMap.adjoint A) ∘L A + (ε : ℂ) • (1 : E →L[ℂ] E)

theorem re_inner_shifted (A : E →L[ℂ] F) (ε : ℝ) (u : E) :
    RCLike.re (inner ℂ u (shifted A ε u)) = ‖A u‖ ^ 2 + ε * ‖u‖ ^ 2 := by
  simp only [shifted, add_apply, comp_apply, smul_apply, one_apply, inner_add_right,
    inner_smul_right, adjoint_inner_right, inner_self_eq_norm_sq_to_K, map_add]
  simp [← Complex.ofReal_pow]

theorem inner_shifted_of_apply_eq_zero (A : E →L[ℂ] F) (ε : ℝ) (u : E) {z : E} (hz : A z = 0) :
    inner ℂ z (shifted A ε u) = (ε : ℂ) * inner ℂ z u := by
  simp [shifted, inner_add_right, inner_smul_right, adjoint_inner_right, hz]

theorem shifted_apply_of_apply_eq_zero (A : E →L[ℂ] F) (ε : ℝ) {z : E} (hz : A z = 0) :
    shifted A ε z = (ε : ℂ) • z := by
  simp [shifted, hz]

theorem mul_norm_le_norm_shifted (A : E →L[ℂ] F) {ε : ℝ} (hε : 0 < ε) (u : E) :
    ε * ‖u‖ ≤ ‖shifted A ε u‖ := by
  have h1 := re_inner_shifted A ε u
  have h2 := re_inner_le_norm (𝕜 := ℂ) u (shifted A ε u)
  rcases eq_or_lt_of_le (norm_nonneg u) with h | h
  · rw [← h, mul_zero]; exact norm_nonneg _
  · have h3 : (ε * ‖u‖) * ‖u‖ ≤ ‖shifted A ε u‖ * ‖u‖ := by
      nlinarith [sq_nonneg ‖A u‖]
    exact le_of_mul_le_mul_right h3 h

theorem isUnit_shifted (A : E →L[ℂ] F) {ε : ℝ} (hε : 0 < ε) : IsUnit (shifted A ε) := by
  have hinj : Function.Injective (shifted A ε : E →ₗ[ℂ] E) := by
    intro a b hab
    have h := mul_norm_le_norm_shifted A hε (a - b)
    have hab' : shifted A ε a = shifted A ε b := hab
    rw [map_sub, hab', sub_self, norm_zero] at h
    have h0 : ‖a - b‖ = 0 := le_antisymm (by nlinarith [norm_nonneg (a - b)]) (norm_nonneg _)
    exact sub_eq_zero.1 (norm_eq_zero.1 h0)
  refine ⟨(LinearEquiv.ofInjectiveEndo _ hinj).toContinuousLinearEquiv.toUnit, ?_⟩
  ext v
  rfl

theorem exists_norm_le_norm_shifted (A : E →L[ℂ] F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 ≤ ε → ∀ u ∈ (LinearMap.ker (A : E →ₗ[ℂ] F))ᗮ, ‖u‖ ≤ C * ‖shifted A ε u‖ := by
  set K := LinearMap.ker (A : E →ₗ[ℂ] F)
  have hinj : Function.Injective ((A : E →ₗ[ℂ] F).comp Kᗮ.subtype) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    have h1 : (u : E) ∈ K := hu
    have h2 : (u : E) ∈ K ⊓ Kᗮ := ⟨h1, u.2⟩
    rw [K.inf_orthogonal_eq_bot, Submodule.mem_bot] at h2
    exact Subtype.ext h2
  obtain ⟨c, -, hc⟩ := ((A : E →ₗ[ℂ] F).comp Kᗮ.subtype).injective_iff_antilipschitz.1 hinj
  refine ⟨(c : ℝ) ^ 2, sq_nonneg _, fun ε hε u hu => ?_⟩
  have h1 : ‖u‖ ≤ c * ‖A u‖ := by
    simpa using hc.le_mul_norm (map_zero _) ⟨u, hu⟩
  have h2 := re_inner_shifted A ε u
  have h3 := re_inner_le_norm (𝕜 := ℂ) u (shifted A ε u)
  have hc0 : (0 : ℝ) ≤ c := c.2
  rcases eq_or_lt_of_le (norm_nonneg u) with h | h
  · rw [← h]; positivity
  · have hAu : ‖u‖ ^ 2 ≤ (c : ℝ) ^ 2 * ‖A u‖ ^ 2 := by
      have := mul_le_mul h1 h1 (norm_nonneg _) (by positivity)
      nlinarith
    have h4 : (c : ℝ) ^ 2 * ‖A u‖ ^ 2 ≤ (c : ℝ) ^ 2 * (‖u‖ * ‖shifted A ε u‖) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      nlinarith [mul_nonneg hε (sq_nonneg ‖u‖)]
    have h5 : ‖u‖ * ‖u‖ ≤ ((c : ℝ) ^ 2 * ‖shifted A ε u‖) * ‖u‖ := by nlinarith
    exact le_of_mul_le_mul_right h5 h

def resolvent (A : E →L[ℂ] F) (ε : ℝ) : E →L[ℂ] E :=
  (ε : ℂ) • Ring.inverse (shifted A ε)

theorem exists_norm_resolvent_sub_le (A : E →L[ℂ] F) :
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε →
      ‖resolvent A ε - (LinearMap.ker (A : E →ₗ[ℂ] F)).starProjection‖ ≤ C * ε := by
  obtain ⟨C, hC, hCb⟩ := exists_norm_le_norm_shifted A
  refine ⟨2 * C, fun ε hε => ?_⟩
  set K := LinearMap.ker (A : E →ₗ[ℂ] F)
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  set u := (resolvent A ε - K.starProjection) v with hu_def
  have hinv : shifted A ε (Ring.inverse (shifted A ε) v) = v := by
    have := Ring.mul_inverse_cancel _ (isUnit_shifted A hε)
    exact congrArg (fun T : E →L[ℂ] E => T v) this
  have hPv : A (K.starProjection v) = 0 := K.starProjection_apply_mem v
  have hTu : shifted A ε u = (ε : ℂ) • (v - K.starProjection v) := by
    rw [hu_def, resolvent, sub_apply, smul_apply, map_sub, map_smul, hinv,
      shifted_apply_of_apply_eq_zero A ε hPv, smul_sub]
  have hu : u ∈ Kᗮ := by
    rw [Submodule.mem_orthogonal]
    intro z hz
    have h1 := inner_shifted_of_apply_eq_zero A ε u hz
    rw [hTu, inner_smul_right,
      (Submodule.mem_orthogonal _ _).1 (K.sub_starProjection_mem_orthogonal v) z hz, mul_zero] at h1
    have hε' : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
    exact (mul_eq_zero.1 h1.symm).resolve_left hε'
  have hvP : ‖v - K.starProjection v‖ ≤ 2 * ‖v‖ :=
    (norm_sub_le _ _).trans (by linarith [K.norm_starProjection_apply_le v])
  calc ‖u‖ ≤ C * ‖shifted A ε u‖ := hCb ε hε.le u hu
    _ = C * (ε * ‖v - K.starProjection v‖) := by
      rw [hTu, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
    _ ≤ C * (ε * (2 * ‖v‖)) := by gcongr
    _ = 2 * C * ε * ‖v‖ := by ring

theorem tendsto_resolvent (A : E →L[ℂ] F) :
    Tendsto (fun j : ℕ => resolvent A (1 / ((j : ℝ) + 1))) atTop
      (𝓝 (LinearMap.ker (A : E →ₗ[ℂ] F)).starProjection) := by
  obtain ⟨C, hC⟩ := exists_norm_resolvent_sub_le A
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun j => hC _ (by positivity)) ?_
  simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul C

theorem continuous_resolvent {X : Type*} [TopologicalSpace X] {A : X → E →L[ℂ] F} (hA : Continuous A) {ε : ℝ} (hε : 0 < ε) :
    Continuous fun x => resolvent (A x) ε := by
  have hadj : Continuous fun x => ContinuousLinearMap.adjoint (A x) :=
    ContinuousLinearMap.adjoint.continuous.comp hA
  have hT : Continuous fun x => shifted (A x) ε := by
    simp only [shifted]
    exact (hadj.clm_comp hA).add continuous_const
  have hI : Continuous fun x => Ring.inverse (shifted (A x) ε) := by
    refine continuous_iff_continuousAt.2 fun x => ?_
    have h := NormedRing.inverse_continuousAt (isUnit_shifted (A x) hε).unit
    rw [IsUnit.unit_spec] at h
    exact ContinuousAt.comp (g := Ring.inverse) (f := fun x => shifted (A x) ε) h hT.continuousAt
  show Continuous fun x => (ε : ℂ) • Ring.inverse (shifted (A x) ε)
  exact hI.const_smul (ε : ℂ)

end KernelProjMeasurable

theorem KernelProjMeasurable.proof : KernelProjMeasurable.Statement := by
  intro X _ _ _ n k L hL
  let A : X → EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin k) :=
    fun x => LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (L x))
  have hA : Continuous A := by
    rw [continuous_clm_apply]
    intro v
    change Continuous fun x => (WithLp.toLp 2 (Matrix.mulVec (L x) (WithLp.ofLp v)) : EuclideanSpace ℂ (Fin k))
    exact (PiLp.continuous_toLp 2 _).comp (hL.matrix_mulVec continuous_const)
  refine measurable_of_tendsto_metrizable
    (f := fun j x => KernelProjMeasurable.resolvent (A x) (1 / ((j : ℝ) + 1)))
    (fun j => (KernelProjMeasurable.continuous_resolvent hA (by positivity)).measurable) ?_
  rw [tendsto_pi_nhds]
  intro x
  exact KernelProjMeasurable.tendsto_resolvent (A x)

end

end GroundTheory.Heights₂.Heights
end
