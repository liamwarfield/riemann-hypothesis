module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ShiftOf
public import GroundTheory.AutomorphicForms.GL2.InnerProductParamHolo

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ArchimedeanDerivatives.TestEx
open MeasureTheory Set Filter Topology Metric
open scoped ContDiff

namespace UpperTheory.V.Z.Inf

private theorem testEx_gen {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]
    {U : Set E} (hU : IsOpen U) {f : E → ℂ} (hf : ContinuousOn f U) {A : E → ℝ} (hA : Continuous A)
    (hA0 : ∀ x ∈ U, 0 < A x) {x₀ : E} (hx₀ : x₀ ∈ U) (h0 : f x₀ ≠ 0) :
    ∃ Φ : E → ℂ, (ContDiff ℝ ∞ Φ ∧ HasCompactSupport Φ ∧ tsupport Φ ⊆ U) ∧
      (Differentiable ℂ fun s : ℂ => ∫ x, Φ x * f x * ((A x : ℝ) : ℂ) ^ s ∂μ) ∧
      ∃ s : ℂ, ∫ x, Φ x * f x * ((A x : ℝ) : ℂ) ^ s ∂μ ≠ 0 := by
  haveI : ProperSpace E := FiniteDimensional.proper ℝ E
  set c : ℂ := starRingEnd ℂ (f x₀) with hc
  have hre : 0 < (c * f x₀).re := by
    rw [hc, mul_comm, Complex.mul_conj, Complex.ofReal_re]
    exact Complex.normSq_pos.2 h0
  have hca : ContinuousAt (fun x => (c * f x).re) x₀ :=
    Complex.continuous_re.continuousAt.comp (continuousAt_const.mul (hf.continuousAt (hU.mem_nhds hx₀)))
  have hW : U ∩ {x | 0 < (c * f x).re} ∈ 𝓝 x₀ :=
    inter_mem (hU.mem_nhds hx₀) (hca.eventually (lt_mem_nhds hre))
  obtain ⟨ε, hε, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.1 hW
  let ψ : ContDiffBump x₀ := ⟨ε / 2, ε, by positivity, by linarith⟩
  have hψz : ∀ x, x ∉ closedBall x₀ ε → ψ x = 0 := fun x hx => by
    by_contra h
    have : x ∈ Function.support ψ := h
    rw [ψ.support_eq] at this
    exact hx (ball_subset_closedBall this)
  have hKc : IsCompact (closedBall x₀ ε) := isCompact_closedBall _ _
  have hKU : closedBall x₀ ε ⊆ U := fun x hx => (hball hx).1
  let F : ℂ → E → ℂ := fun s x => (ψ x : ℂ) * f x * ((A x : ℝ) : ℂ) ^ s
  have hFz : ∀ s x, x ∉ closedBall x₀ ε → F s x = 0 := fun s x hx => by
    simp only [F, hψz x hx, Complex.ofReal_zero, zero_mul]
  have hts : ∀ {G : E → ℂ}, (∀ x, x ∉ closedBall x₀ ε → G x = 0) → tsupport G ⊆ closedBall x₀ ε := fun h =>
    closure_minimal (fun x hx => by by_contra h'; exact hx (h x h')) isClosed_closedBall
  have hJ : ContinuousOn (fun p : ℂ × E => F p.1 p.2) (univ ×ˢ U) := by
    refine ContinuousOn.mul (ContinuousOn.mul ?_ ?_) ?_
    · exact (Complex.continuous_ofReal.comp (ψ.continuous.comp continuous_snd)).continuousOn
    · exact hf.comp continuousOn_snd fun p hp => hp.2
    · exact ContinuousOn.cpow (Complex.continuous_ofReal.comp (hA.comp continuous_snd)).continuousOn
        continuousOn_fst fun p hp => Complex.ofReal_mem_slitPlane.2 (hA0 _ hp.2)
  have hFc : ∀ s, Continuous (F s) := fun s => by
    have : ContinuousOn (F s) U :=
      hJ.comp (f := fun x : E => (s, x)) (by fun_prop) fun x hx => ⟨trivial, hx⟩
    exact this.continuous_of_tsupport_subset hU ((hts (hFz s)).trans hKU)
  have hFi : ∀ s, Integrable (F s) μ := fun s =>
    (hFc s).integrable_of_hasCompactSupport (HasCompactSupport.intro hKc (hFz s))
  have hΦz : ∀ x, x ∉ closedBall x₀ ε → (ψ x : ℂ) = 0 := fun x hx => by
    rw [hψz x hx, Complex.ofReal_zero]
  refine ⟨fun x => (ψ x : ℂ), ⟨?_, HasCompactSupport.intro hKc hΦz, (hts hΦz).trans hKU⟩, ?_, 0, ?_⟩
  · exact Complex.ofRealCLM.contDiff.comp ψ.contDiff
  · rw [← differentiableOn_univ]
    refine GroundTheory.Automorphic.PseudoEisenstein.differentiableOn_integral_of_bound (F := F) isOpen_univ
      (fun x => ?_) (fun s _ => (hFc s).aestronglyMeasurable) fun s₀ _ => ?_
    · by_cases hx : x ∈ closedBall x₀ ε
      · refine Differentiable.differentiableOn ?_
        exact (differentiable_id.const_cpow (Or.inl (by exact_mod_cast (hA0 x (hKU hx)).ne'))).const_mul _
      · simp only [hFz _ x hx]
        exact differentiableOn_const _
    · obtain ⟨C, hC⟩ := ((isCompact_closedBall s₀ 1).prod hKc).exists_bound_of_continuousOn
        (hJ.mono (prod_mono (subset_univ _) hKU))
      refine ⟨1, one_pos, subset_univ _, (closedBall x₀ ε).indicator fun _ => C, ?_, fun s hs x => ?_⟩
      · rw [integrable_indicator_iff isClosed_closedBall.measurableSet]
        exact integrableOn_const hKc.measure_lt_top.ne
      · by_cases hx : x ∈ closedBall x₀ ε
        · rw [indicator_of_mem hx]
          exact hC (s, x) ⟨hs, hx⟩
        · rw [indicator_of_notMem hx, hFz s x hx, norm_zero]
  · intro hz
    change ∫ x, F 0 x ∂μ = 0 at hz
    have hr : ∀ x, (c * F 0 x).re = ψ x * (c * f x).re := fun x => by
      simp only [F, Complex.cpow_zero, mul_one]
      rw [mul_left_comm, Complex.re_ofReal_mul]
    have hrc : Continuous fun x => (c * F 0 x).re :=
      Complex.continuous_re.comp (continuous_const.mul (hFc 0))
    have hr0 : 0 ≤ fun x => (c * F 0 x).re := fun x => by
      change 0 ≤ (c * F 0 x).re
      by_cases hx : x ∈ closedBall x₀ ε
      · rw [hr]
        exact mul_nonneg ψ.nonneg (le_of_lt (hball hx).2)
      · rw [hFz 0 x hx]; simp
    have hri : Integrable (fun x => (c * F 0 x).re) μ := ((hFi 0).const_mul c).re
    have hpos : 0 < ∫ x, (c * F 0 x).re ∂μ := by
      rw [integral_pos_iff_support_of_nonneg hr0 hri]
      refine hrc.isOpen_support.measure_pos μ ⟨x₀, ?_⟩
      change (c * F 0 x₀).re ≠ 0
      rw [hr, ψ.one_of_mem_closedBall (mem_closedBall_self ψ.rIn_pos.le), one_mul]
      exact hre.ne'
    have h1 := integral_re ((hFi 0).const_mul c)
    simp only [RCLike.re_to_complex] at h1
    rw [h1, integral_const_mul, hz, mul_zero, Complex.zero_re] at hpos
    exact lt_irrefl _ hpos

end UpperTheory.V.Z.Inf

theorem UpperTheory.V.Z.Inf.testEx :
    UpperTheory.V.Z.Inf.TestEx := by
  intro K _ _ _ n f hf ⟨x₀, hx₀, h0⟩
  haveI : Measure.IsAddHaarMeasure (volume : Measure (Fin n → GlobalTheory.CuspRep.Cinf K)) := Measure.pi.isAddHaarMeasure _
  haveI : Measure.IsAddHaarMeasure (volume : Measure (GlobalTheory.CuspRep.Lie K n)) := Measure.pi.isAddHaarMeasure _
  refine UpperTheory.V.Z.Inf.testEx_gen volume GlobalTheory.CuspRep.isOpen_invSet hf (A := UpperTheory.V.Z.Inf.nrm) ?_ ?_ hx₀ h0
  · unfold UpperTheory.V.Z.Inf.nrm
    refine continuous_finsetProd _ fun w _ => Continuous.pow (Continuous.norm ?_) 2
    exact (continuous_apply w).comp (Continuous.matrix_det continuous_id)
  · intro x hx
    have hu : IsUnit (Matrix.of x).det := (Matrix.isUnit_iff_isUnit_det _).1 hx
    unfold UpperTheory.V.Z.Inf.nrm
    refine Finset.prod_pos fun w _ => pow_pos (norm_pos_iff.2 ?_) 2
    exact (hu.map (Pi.evalMonoidHom _ w)).ne_zero
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ArchimedeanDerivatives.IsOpenEmbeddingVal
noncomputable section

open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GroundTheory.Automorphic

namespace UpperTheory.V.Z.Inf

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

private def lm (y : Lie K n) : Lie K n →ₗ[ℝ] Lie K n :=
  LinearMap.mulLeft ℝ (A := Matrix (Fin n) (Fin n) (InfinitePlace K → ℂ)) (Matrix.of y)

private def placeOut (K : Type) [Field K] [NumberField K] (n : ℕ) :
    Lie K n ≃ₗ[ℝ] (InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) where
  toFun x v := Matrix.of fun i j => x i j v
  invFun y i j v := y v i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

private theorem det_lm (y : Lie K n) : LinearMap.det (lm y) = nrm y ^ n := by
  classical
  set e := placeOut K n
  have hc : e.toLinearMap ∘ₗ lm y ∘ₗ e.symm.toLinearMap =
      LinearMap.pi (fun v => ((LinearMap.mulLeft ℂ (e y v)).restrictScalars ℝ) ∘ₗ LinearMap.proj v) := by
    apply LinearMap.ext; intro x
    funext v i j
    show (Matrix.of y * Matrix.of (fun i j v => x v i j)) i j v = ∑ k, y i k v * x v k j
    rw [Matrix.mul_apply, Finset.sum_apply]
    rfl
  rw [← LinearMap.det_conj _ e, hc, LinearMap.det_pi, nrm, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [det_restrictScalars_mulLeft, Fintype.card_fin]
  congr 3
  rw [show (Matrix.of y).det v = Pi.evalRingHom _ v (Matrix.of y).det from rfl, RingHom.map_det]
  rfl

private theorem nrm_lm (y x : Lie K n) : nrm (lm y x) = nrm y * nrm x := by
  show ∏ w, ‖(Matrix.of y * Matrix.of x).det w‖ ^ 2 = _
  simp only [nrm, Matrix.det_mul, Pi.mul_apply, norm_mul, mul_pow, Finset.prod_mul_distrib]

private theorem nrm_nonneg (x : Lie K n) : 0 ≤ nrm x :=
  Finset.prod_nonneg fun _ _ => by positivity

private theorem nrm_pos_iff (x : Lie K n) : 0 < nrm x ↔ x ∈ invSet K n := by
  have h : x ∈ invSet K n ↔ IsUnit (Matrix.of x).det := Matrix.isUnit_iff_isUnit_det (Matrix.of x)
  rw [h, Pi.isUnit_iff, (nrm_nonneg x).lt_iff_ne, ne_comm, nrm, Finset.prod_ne_zero_iff]
  simp

private theorem continuous_nrm : Continuous (nrm : Lie K n → ℝ) := by
  refine continuous_finsetProd _ fun w _ => (Continuous.norm ?_).pow 2
  exact (continuous_apply w).comp
    (continuous_id (X := Matrix (Fin n) (Fin n) (InfinitePlace K → ℂ))).matrix_det

private theorem isOpenEmbedding_val :
    Topology.IsOpenEmbedding (Units.val : GL (Fin n) (Cinf K) → Matrix (Fin n) (Fin n) (Cinf K)) := by
  refine ⟨Units.isEmbedding_val_mk' (f := fun x => Ring.inverse x.det • x.adjugate) ?_ ?_, ?_⟩
  · intro x hx
    have hd : IsUnit x.det := (Matrix.isUnit_iff_isUnit_det x).1 hx
    refine ContinuousAt.continuousWithinAt ?_
    refine ContinuousAt.smul (M := Cinf K) (f := fun x : Matrix (Fin n) (Fin n) (Cinf K) => Ring.inverse x.det) ?_
      ((continuous_id (X := Matrix (Fin n) (Fin n) (Cinf K))).matrix_adjugate).continuousAt
    exact ContinuousAt.comp_of_eq (NormedRing.inverse_continuousAt hd.unit)
      ((continuous_id (X := Matrix (Fin n) (Fin n) (Cinf K))).matrix_det).continuousAt hd.unit_spec.symm
  · intro u
    rw [Matrix.coe_units_inv, Matrix.inv_def]
  · have : Set.range (Units.val : GL (Fin n) (Cinf K) → Matrix (Fin n) (Fin n) (Cinf K)) = {x | IsUnit x} := by
      ext x; exact ⟨fun ⟨u, hu⟩ => hu ▸ u.isUnit, fun h => ⟨h.unit, h.unit_spec⟩⟩
    rw [this]
    exact isOpen_invSet (E := K) (a := n)

private theorem addHaar_vol : (volume : Measure (Lie K n)).IsAddHaarMeasure := by
  haveI : (volume : Measure (Cinf K)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure (Fin n → Cinf K)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  exact Measure.pi.isAddHaarMeasure _

private theorem measurable_dens : Measurable fun x : Lie K n => ENNReal.ofReal ((nrm x)⁻¹ ^ n) :=
  ENNReal.measurable_ofReal.comp (continuous_nrm.measurable.inv.pow_const _)

private theorem map_lm (y : Lie K n) (hy : y ∈ invSet K n) :
    Measure.map (lm y) ((volume : Measure (Lie K n)).withDensity fun x => ENNReal.ofReal ((nrm x)⁻¹ ^ n)) =
      (volume : Measure (Lie K n)).withDensity fun x => ENNReal.ofReal ((nrm x)⁻¹ ^ n) := by
  haveI := addHaar_vol (K := K) (n := n)
  have hp := (nrm_pos_iff y).2 hy
  have hdet : LinearMap.det (lm y) ≠ 0 := by rw [det_lm]; positivity
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (Lie K n)) hdet
  refine map_withDensity_eq_of_scale (volume : Measure (Lie K n)) measurable_dens (lm y)
    (ENNReal.ofReal_pos.2 (abs_pos.2 (inv_ne_zero hdet))).ne' ENNReal.ofReal_ne_top hmap fun x => ?_
  rw [det_lm, nrm_lm, abs_of_pos (by positivity), ← ENNReal.ofReal_mul (by positivity), mul_inv, mul_pow,
    inv_pow (nrm y)]

end UpperTheory.V.Z.Inf

open UpperTheory.V.Z.Inf in
theorem UpperTheory.V.Z.Inf.haarL :
    UpperTheory.V.Z.Inf.HaarL := by
  intro K _ _ _ n _ _
  haveI := addHaar_vol (K := K) (n := n)
  set w : Lie K n → ENNReal := fun x => ENNReal.ofReal ((nrm x)⁻¹ ^ n) with hw
  set μL : Measure (Lie K n) := (volume : Measure (Lie K n)).withDensity w with hμL
  set e : GL (Fin n) (Cinf K) → Lie K n := fun g => toL g.val with he
  have hOE : Topology.IsOpenEmbedding e := isOpenEmbedding_val
  have hE : MeasurableEmbedding e := hOE.measurableEmbedding
  have hwm : Measurable w := measurable_dens
  have happ : ∀ s, Measure.comap e μL s = μL (e '' s) := fun s => hE.comap_apply _ s
  have hmem : ∀ g, e g ∈ invSet K n := fun g => g.isUnit
  have hpos : ∀ g, 0 < nrm (e g) := fun g => (nrm_pos_iff _).2 (hmem g)
  refine ⟨Measure.comap e μL, ?_, ?_⟩
  · refine { lt_top_of_isCompact := ?_, map_mul_left_eq_self := ?_, open_pos := ?_ }
    · intro C hC
      rw [happ]
      have hC' : IsCompact (e '' C) := hC.image hOE.continuous
      have hmeas : MeasurableSet (e '' C) := hC'.isClosed.measurableSet
      have hcont : Continuous (fun g : GL (Fin n) (Cinf K) => (nrm (e g))⁻¹ ^ n) :=
        ((continuous_nrm.comp hOE.continuous).inv₀ fun g => (hpos g).ne').pow _
      obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn hcont.continuousOn
      rw [hμL, withDensity_apply _ hmeas]
      calc ∫⁻ x in e '' C, w x ∂volume
          ≤ ∫⁻ _ in e '' C, ENNReal.ofReal B ∂volume := by
            refine setLIntegral_mono' hmeas fun x hx => ?_
            obtain ⟨g, hg, rfl⟩ := hx
            exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hB g hg))
        _ = ENNReal.ofReal B * volume (e '' C) := setLIntegral_const _ _
        _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hC'.measure_lt_top
    · intro g
      ext s hs
      have hm : Measurable (fun h : GL (Fin n) (Cinf K) => g * h) :=
        (continuous_const.mul continuous_id).measurable
      rw [Measure.map_apply hm hs, happ, happ]
      have hmeas : MeasurableSet (e '' s) := hE.measurableSet_image.2 hs
      have h1 : e '' ((fun h => g * h) ⁻¹' s) = (lm (e g)) ⁻¹' (e '' s) :=
        image_val_preimage_mul_left g s
      rw [h1, ← Measure.map_apply (lm (e g)).continuous_of_finiteDimensional.measurable hmeas,
        map_lm _ (hmem g)]
    · intro U hU hne
      rw [happ, ne_eq, hμL, withDensity_apply_eq_zero' hwm.aemeasurable]
      have hsub : {x | w x ≠ 0} ∩ e '' U = e '' U := by
        refine Set.inter_eq_right.2 ?_
        rintro _ ⟨g, _, rfl⟩
        exact (ENNReal.ofReal_pos.2 (pow_pos (inv_pos.2 (hpos g)) _)).ne'
      rw [hsub]
      exact (hOE.isOpenMap U hU).measure_ne_zero volume (hne.image _)
  · have hr : Set.range e = invSet K n := by
      ext x
      exact ⟨fun ⟨g, hg⟩ => hg ▸ hmem g, fun h => ⟨IsUnit.unit h, rfl⟩⟩
    rw [hE.map_comap, hr, hμL, restrict_withDensity isOpen_invSet.measurableSet]
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ArchimedeanDerivatives.ShiftOf
open NumberField MeasureTheory Matrix Polynomial GlobalTheory.CuspRep
open scoped ContDiff

noncomputable section

namespace UpperTheory.V.Z.Inf

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

omit [NumberField K] in
private theorem coord_cases (τ : K →+* ℂ) :
    (∀ z : Cinf K, coord τ z = z (InfinitePlace.mk τ)) ∨
      ∀ z : Cinf K, coord τ z = starRingEnd ℂ (z (InfinitePlace.mk τ)) := by
  unfold coord
  split_ifs
  · exact Or.inl fun _ => rfl
  · exact Or.inr fun _ => rfl

private theorem det_ne_zero {x : Lie K n} (hx : x ∈ invSet K n) (w : InfinitePlace K) :
    (Matrix.of x).det w ≠ 0 := by
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det _).1 hx
  have h := congrFun u.mul_inv w
  rw [hu] at h
  exact left_ne_zero_of_mul_eq_one h

private theorem detAt_ne_zero {x : Lie K n} (hx : x ∈ invSet K n) (τ : K →+* ℂ) : detAt τ x ≠ 0 := by
  rcases coord_cases τ with h | h
  · rw [detAt, h]; exact det_ne_zero hx _
  · rw [detAt, h]; exact (_root_.map_ne_zero _).2 (det_ne_zero hx _)

private theorem contDiff_det_at (w : InfinitePlace K) :
    ContDiff ℝ ∞ (fun x : Lie K n => (Matrix.of x).det w) := by
  simp only [Matrix.det_apply', Finset.sum_apply, Pi.mul_apply, Finset.prod_apply, Matrix.of_apply]
  refine ContDiff.sum fun p _ => contDiff_const.mul (contDiff_prod fun i _ => ?_)
  fun_prop

private theorem contDiff_detAt (τ : K →+* ℂ) : ContDiff ℝ ∞ (fun x : Lie K n => detAt τ x) := by
  rcases coord_cases τ with h | h
  · simp only [detAt, h]; exact contDiff_det_at _
  · simp only [detAt, h]; exact Complex.conjCLE.contDiff.comp (contDiff_det_at _)

private theorem nrm_pos {x : Lie K n} (hx : x ∈ invSet K n) : 0 < nrm x :=
  Finset.prod_pos fun w _ => pow_pos (norm_pos_iff.2 (det_ne_zero hx w)) _

private theorem contDiff_nrm : ContDiff ℝ ∞ (fun x : Lie K n => nrm x) :=
  contDiff_prod fun w _ => (contDiff_det_at w).norm_sq ℂ

private theorem contDiffOn_wt (u : ℂ) (e : (K →+* ℂ) → ℕ) : ContDiffOn ℝ ∞ (wt (n := n) u e) (invSet K n) := by
  have h0 : ContDiffOn ℝ ∞ (fun x : Lie K n => Real.log (nrm x)) (invSet K n) :=
    Real.contDiffOn_log.comp contDiff_nrm.contDiffOn (fun x hx => (nrm_pos hx).ne')
  have h1 : ContDiffOn ℝ ∞ (fun x : Lie K n => Complex.exp ((Real.log (nrm x) : ℂ) * u)) (invSet K n) :=
    ((Complex.ofRealCLM.contDiff.comp_contDiffOn h0).mul contDiffOn_const).cexp
  have h2 : ContDiffOn ℝ ∞ (fun x : Lie K n => ((nrm x : ℝ) : ℂ) ^ u) (invSet K n) :=
    h1.congr fun x hx => by
      rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (nrm_pos hx).ne'), ← Complex.ofReal_log (nrm_pos hx).le]
  exact h2.mul (contDiffOn_prod fun σ _ =>
    ((contDiff_detAt σ).contDiffOn.inv fun x hx => detAt_ne_zero hx σ).pow _)

private theorem prod_coord [_root_.NumberField.IsTotallyComplex K] (z : Cinf K) :
    ∏ σ : K →+* ℂ, coord σ z = ((∏ w, ‖z w‖ ^ 2 : ℝ) : ℂ) := by
  classical
  rw [← Finset.prod_fiberwise Finset.univ InfinitePlace.mk, Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun w _ => ?_
  have hne : w.embedding ≠ ComplexEmbedding.conjugate w.embedding := fun h =>
    InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w)
      (InfinitePlace.isReal_iff.2 (ComplexEmbedding.isReal_iff.2 h.symm))
  have hf : (Finset.univ.filter fun σ : K →+* ℂ => InfinitePlace.mk σ = w) =
      {w.embedding, ComplexEmbedding.conjugate w.embedding} := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro h
      rcases InfinitePlace.mk_eq_iff.1 (w.mk_embedding.trans h.symm) with h | h
      · exact Or.inl h.symm
      · exact Or.inr h.symm
    · rintro (rfl | rfl)
      · exact w.mk_embedding
      · rw [InfinitePlace.mk_conjugate_eq, w.mk_embedding]
  have h1 : coord w.embedding z = z w := by
    unfold coord
    rw [InfinitePlace.mk_embedding, if_pos rfl]
    rfl
  have h2 : coord (ComplexEmbedding.conjugate w.embedding) z = starRingEnd ℂ (z w) := by
    unfold coord
    rw [InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding, if_neg hne]
    rfl
  rw [hf, Finset.prod_pair hne, h1, h2, Complex.mul_conj, Complex.normSq_eq_norm_sq]

private theorem integral_congr_inv {Ψ : Lie K n → ℂ} (hΨ : tsupport Ψ ⊆ invSet K n) {F G : Lie K n → ℂ}
    (h : ∀ x ∈ invSet K n, F x = G x) : ∫ x, Ψ x * F x = ∫ x, Ψ x * G x := by
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ invSet K n
  · simp only [h x hx]
  · simp only [image_eq_zero_of_notMem_tsupport (fun h' => hx (hΨ h')), zero_mul]

private theorem integral_mul_const_in (Ψ F : Lie K n → ℂ) (c : ℂ) :
    ∫ x, Ψ x * (c * F x) = c * ∫ x, Ψ x * F x := by
  rw [← integral_const_mul]; congr 1; funext x; ring

attribute [local instance] Classical.propDecidable

private theorem wt_succ (u : ℂ) (e : (K →+* ℂ) → ℕ) (τ : K →+* ℂ) (x : Lie K n) :
    wt u (e + Pi.single τ 1) x = wt u e x * (detAt τ x)⁻¹ := by
  simp only [wt, Pi.add_apply, pow_add, Finset.prod_mul_distrib, mul_assoc]
  congr 2
  rw [Finset.prod_eq_single τ (fun σ _ h => by simp [Pi.single_eq_of_ne h]) (by simp)]
  simp

private theorem list_shift [_root_.NumberField.IsTotallyComplex K] (hP : Ptw) (hI : Parts) (φ : Sm K n)
    (m : (K →+* ℂ) → Multiset ℂ) (hm : ∀ τ u, cap τ u φ = ((m τ).map (u + ·)).prod • φ) (g : GA K n) (u : ℂ) :
    ∀ l : List (K →+* ℂ), l.Nodup → ∀ (e : (K →+* ℂ) → ℕ) (Ψ : Lie K n → ℂ), IsTest Ψ →
      IsTest (l.foldr detD Ψ) ∧
      ∫ x, l.foldr detD Ψ x * (chart φ.1 g x * wt u e x) =
        ((-1) ^ n) ^ l.length * (l.map fun τ => ((m τ).map (u - e τ + ((n : ℂ) - 1) / 2 + ·)).prod).prod *
          ∫ x, Ψ x * (chart φ.1 g x * wt u (fun σ => e σ + if σ ∈ l then 1 else 0) x) := by
  intro l
  induction l with
  | nil =>
    intro _ e Ψ hΨ
    exact ⟨hΨ, by simp⟩
  | cons τ l ih =>
    intro hl e Ψ hΨ
    have hτ : τ ∉ l := (List.nodup_cons.1 hl).1
    obtain ⟨hT, hJ⟩ := ih (List.nodup_cons.1 hl).2 (e + Pi.single τ 1) Ψ hΨ
    obtain ⟨hT', hp⟩ := hI K n τ _ hT
    refine ⟨hT', ?_⟩
    have hlow : (fun σ => (e + Pi.single τ 1 : (K →+* ℂ) → ℕ) σ + if σ ∈ l then 1 else 0) =
        fun σ => e σ + if σ ∈ τ :: l then 1 else 0 := by
      funext σ
      by_cases h : σ = τ
      · subst h; simp [hτ]
      · simp [h]
    have hmap : (l.map fun σ => ((m σ).map
          (u - ((e + Pi.single τ 1 : (K →+* ℂ) → ℕ) σ : ℕ) + ((n : ℂ) - 1) / 2 + ·)).prod) =
        l.map fun σ => ((m σ).map (u - e σ + ((n : ℂ) - 1) / 2 + ·)).prod :=
      List.map_congr_left fun σ hσ => by
        rw [Pi.add_apply, Pi.single_eq_of_ne (fun h : σ = τ => hτ (h ▸ hσ)), add_zero]
    have hpt : ∀ x ∈ invSet K n, detD τ (fun y => chart φ.1 g y * wt u e y) x =
        ((m τ).map (u - e τ + ((n : ℂ) - 1) / 2 + ·)).prod * (chart φ.1 g x * wt u (e + Pi.single τ 1) x) :=
      fun x hx => by rw [hP K n τ φ (m τ) (hm τ) g u e x hx, wt_succ, mul_assoc]
    rw [List.foldr_cons, hp _ ((φ.2 g).mul (contDiffOn_wt u e)), integral_congr_inv hT.2.2 hpt,
      integral_mul_const_in, hJ, hlow, hmap, List.map_cons, List.prod_cons, List.length_cons]
    ring

private theorem linPoly_sum {ι : Type} (s : Finset ι) (m : ι → Multiset ℂ) :
    linPoly (∑ i ∈ s, m i) = ∏ i ∈ s, linPoly (m i) := by
  refine Finset.induction_on s (by simp [linPoly]) ?_
  intro a s ha ih
  rw [Finset.sum_insert ha, Finset.prod_insert ha, ← ih]
  simp [linPoly, Multiset.map_add (f := _), Multiset.prod_add]

private theorem wt_one [_root_.NumberField.IsTotallyComplex K] (u : ℂ) {x : Lie K n} (hx : x ∈ invSet K n) :
    wt u (fun _ => 1) x = ((nrm x : ℝ) : ℂ) ^ (u - 1) := by
  have h : ∏ σ, detAt σ x = ((nrm x : ℝ) : ℂ) := prod_coord _
  rw [Complex.cpow_sub _ _ (by exact_mod_cast (nrm_pos hx).ne'), Complex.cpow_one, wt, div_eq_mul_inv, ← h,
    ← Finset.prod_inv_distrib]
  simp

end UpperTheory.V.Z.Inf

open UpperTheory.V.Z.Inf in
theorem UpperTheory.V.Z.Inf.shiftOf :
    UpperTheory.V.Z.Inf.ShiftOf := by
  intro hP hI K _ _ _ n
  classical
  refine ⟨((-1) ^ n) ^ (Finset.univ : Finset (K →+* ℂ)).toList.length, by simp, fun φ m hm Φ hΦ => ?_⟩
  have hnd : (Finset.univ : Finset (K →+* ℂ)).toList.Nodup := Finset.nodup_toList _
  refine ⟨(list_shift hP hI φ m hm 1 0 _ hnd 0 Φ hΦ).1, fun g s => ?_⟩
  obtain ⟨_, h⟩ := list_shift hP hI φ m hm g (s + 1 + ((n : ℂ) - 1) / 2 - n) _ hnd 0 Φ hΦ
  have hone : (fun σ : K →+* ℂ => (0 : (K →+* ℂ) → ℕ) σ +
      if σ ∈ (Finset.univ : Finset (K →+* ℂ)).toList then 1 else 0) = fun _ => 1 := by
    funext σ; simp
  have hR : ∀ x ∈ invSet K n, chart φ.1 g x * wt (s + 1 + ((n : ℂ) - 1) / 2 - n) (fun _ => 1) x =
      chart φ.1 g x * ((nrm x : ℝ) : ℂ) ^ (s + ((n : ℂ) - 1) / 2 - n) := fun x hx => by
    rw [wt_one _ hx]; congr 2; ring
  have hL : ∀ x : Lie K n, wt (s + 1 + ((n : ℂ) - 1) / 2 - n) 0 x =
      ((nrm x : ℝ) : ℂ) ^ (s + 1 + ((n : ℂ) - 1) / 2 - n) := fun x => by simp [wt]
  simp only [hL] at h
  rw [hone, integral_congr_inv hΦ.2.2 hR, Finset.prod_map_toList] at h
  simp only [mul_assoc (_ : ℂ) (chart φ.1 g _)]
  rw [detAll, h, linPoly_sum, Polynomial.eval_prod]
  congr 2
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [linPoly, Polynomial.eval_multiset_prod, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun z _ => ?_
  simp only [Function.comp_apply, eval_add, eval_X, eval_C, Pi.zero_apply, Nat.cast_zero]
  ring
end
end
