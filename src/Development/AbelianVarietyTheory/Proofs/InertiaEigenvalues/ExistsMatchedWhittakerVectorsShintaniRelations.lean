module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWhittakerBumpExtensionSchurComplement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSmoothOfChartDerivativesAtIdentity

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockEmbeddingGLTorusElementZeroPaddedStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockEmbeddingGLTorusElementZeroPadded
noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.JSW

namespace GlobalTheory.JSW

section Block

variable {R S : Type} [CommRing R] [CommRing S] {j n : ℕ}

theorem blockGL_cornerGL (hj : j ≤ n) (s : R →ₙ+* S) (g : GL (Fin j) R) :
    GroundTheory.Automorphic.FourierWhittaker.blockGL hj (cornerGL j s g) =
      cornerGL n s (GroundTheory.Automorphic.FourierWhittaker.blockGL hj g) := by
  ext a b
  change GroundTheory.Automorphic.FourierWhittaker.blockMat hj
      ((1 : Matrix (Fin j) (Fin j) S) - (1 : Matrix (Fin j) (Fin j) R).map s + (g : Matrix (Fin j) (Fin j) R).map s) a b =
    (1 : Matrix (Fin n) (Fin n) S) a b - s ((1 : Matrix (Fin n) (Fin n) R) a b) +
      s (GroundTheory.Automorphic.FourierWhittaker.blockMat hj (g : Matrix (Fin j) (Fin j) R) a b)
  rw [GroundTheory.Automorphic.FourierWhittaker.blockMat_apply, GroundTheory.Automorphic.FourierWhittaker.blockMat_apply]
  by_cases ha : a.val < j
  · by_cases hb : b.val < j
    · simp only [dif_pos ha, dif_pos hb, Matrix.add_apply, Matrix.sub_apply, Matrix.map_apply, Matrix.one_apply,
        Fin.ext_iff]
    · have hab : a ≠ b := fun h => hb (h ▸ ha)
      simp [ha, hb, hab, Matrix.one_apply]
  · by_cases hab : a = b
    · subst hab; simp [ha, Matrix.one_apply]
    · simp [ha, hab, Matrix.one_apply]

theorem blockGL_diagPow (hj : j ≤ n) (ϖ : Rˣ) (v : Fin j → ℕ) :
    GroundTheory.Automorphic.FourierWhittaker.blockGL hj (diagPow ϖ v) = diagPow ϖ (GlobalTheory.RSnmUnf.padNat (n := n) v) := by
  ext a b
  rw [GroundTheory.Automorphic.FourierWhittaker.coe_blockGL, GroundTheory.Automorphic.FourierWhittaker.blockMat_apply]
  simp only [diagPow, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, Matrix.diagonalRingHom_apply]
  by_cases ha : a.val < j
  · by_cases hb : b.val < j
    · simp [ha, hb, Matrix.diagonal_apply, GlobalTheory.RSnmUnf.padNat, Fin.ext_iff, MulEquiv.piUnits]
    · have hab : a ≠ b := fun h => hb (h ▸ ha)
      simp [ha, hb, hab, Matrix.diagonal_apply]
  · by_cases hab : a = b
    · subst hab; simp [ha, Matrix.diagonal_apply, GlobalTheory.RSnmUnf.padNat, MulEquiv.piUnits]
    · simp [ha, hab, Matrix.diagonal_apply]

theorem padNat_eq_zero_iff {m n : ℕ} (hmn : m ≤ n) (v : Fin m → ℕ) :
    GlobalTheory.RSnmUnf.padNat (n := n) v = 0 ↔ v = 0 := by
  constructor
  · intro h
    funext i
    have := congrFun h ⟨i.val, by omega⟩
    simpa [GlobalTheory.RSnmUnf.padNat, i.isLt] using this
  · rintro rfl
    exact GlobalTheory.RSnmUnf.padNat_zero

end Block

theorem blockGL_tl {E : Type} [Field E] [NumberField E] (m r : ℕ)
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ) (l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ)) :
    GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) (GlobalTheory.JSW.tl ϖ l) =
      GlobalTheory.JSW.tl ϖ (l.mapRange GlobalTheory.RSnmUnf.padNat GlobalTheory.RSnmUnf.padNat_zero) := by
  have hsupp : (l.mapRange (GlobalTheory.RSnmUnf.padNat (n := m + r + 1 + 1)) GlobalTheory.RSnmUnf.padNat_zero).support = l.support := by
    ext w
    simp only [Finsupp.mem_support_iff, Finsupp.mapRange_apply, ne_eq]
    rw [padNat_eq_zero_iff (by omega)]
  unfold tl
  rw [hsupp, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro w _
  simp only [Function.comp_apply, Finsupp.mapRange_apply]
  rw [finGL, locGL, blockGL_cornerGL, blockGL_cornerGL, blockGL_diagPow]
  rfl

end GlobalTheory.JSW
end
end

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockEmbeddingGL_torus_element_zero_padded : ∀ (E : Type) [Field E] [NumberField E] (m r : ℕ)
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ) (l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ)),
    GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) (GlobalTheory.JSW.tl ϖ l) =
      GlobalTheory.JSW.tl ϖ (l.mapRange GlobalTheory.RSnmUnf.padNat GlobalTheory.RSnmUnf.padNat_zero) := by
  first | (exact @GlobalTheory.JSW.blockGL_tl) | (exact GlobalTheory.JSW.blockGL_tl) | (intros; apply GlobalTheory.JSW.blockGL_tl  <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnipotentInvariantCompactlySupportedWeight
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
open Matrix
open GlobalTheory.WhitBump

noncomputable section

namespace GlobalTheory.KappaCut

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem decomp (h : GA E a) :
    h = infGL E a (GeneralLinearGroup.map (pInf E) h) * finGL E a (GeneralLinearGroup.map (pFin E) h) := by
  refine ga_ext ?_ ?_ <;> simp

theorem continuous_of_chart (b : GA E a → ℂ) (U : Subgroup (GL (Fin a) (Af E))) (hU : IsOpen (U : Set (GL (Fin a) (Af E))))
    (hR : ∀ u ∈ U, ∀ g, b (g * finGL E a u) = b g) (hC : ∀ g, ContDiffOn ℝ ∞ (chart b g) (invSet E a)) :
    Continuous b := by
  rw [continuous_iff_continuousAt]
  intro g
  let pI : GA E a → GL (Fin a) (Cinf E) := fun h => GeneralLinearGroup.map (pInf E) h
  let pF : GA E a → GL (Fin a) (Af E) := fun h => GeneralLinearGroup.map (pFin E) h
  have hpI : Continuous pI := ContAut.continuous_map_pInf E a
  have hpF : Continuous pF := ContAut.continuous_map_pFin E a
  let F : GA E a → Lie E a := fun g' => toL ((pI (g⁻¹ * g') : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E))
  have hF : Continuous F := (Units.continuous_val (M := Matrix (Fin a) (Fin a) (Cinf E))).comp (hpI.comp (continuous_const.mul continuous_id))
  have hFmem : ∀ g', F g' ∈ invSet E a := fun g' => show IsUnit (Matrix.of (F g')) from (pI (g⁻¹ * g')).isUnit
  have heq : ∀ g', pF (g⁻¹ * g') ∈ U → b g' = chart b g (F g') := by
    intro g' hg'
    have hx : IsUnit (Matrix.of (F g')) := (pI (g⁻¹ * g')).isUnit
    rw [chart, dif_pos hx]
    have hu : hx.unit = pI (g⁻¹ * g') := Units.ext rfl
    rw [hu]
    have e : g' = g * infGL E a (pI (g⁻¹ * g')) * finGL E a (pF (g⁻¹ * g')) := by
      rw [mul_assoc, ← decomp, mul_inv_cancel_left]
    rw [show b g' = b (g * infGL E a (pI (g⁻¹ * g')) * finGL E a (pF (g⁻¹ * g'))) from congrArg b e, hR _ hg']
  have hopen : {g' | pF (g⁻¹ * g') ∈ U} ∈ nhds g := by
    refine (hU.preimage (hpF.comp (continuous_const.mul continuous_id))).mem_nhds ?_
    simp [pF, U.one_mem]
  have hcont : ContinuousAt (fun g' => chart b g (F g')) g := by
    have h1 : ContinuousWithinAt (chart b g) (invSet E a) (F g) := (hC g).continuousOn _ (hFmem g)
    have h2 : ContinuousWithinAt (chart b g ∘ F) Set.univ g :=
      h1.comp hF.continuousAt.continuousWithinAt (fun x _ => hFmem x)
    rwa [continuousWithinAt_univ] at h2
  exact hcont.congr (Filter.eventuallyEq_of_mem hopen (fun g' hg' => (heq g' hg').symm))

theorem contDiff_normSq_ofReal : ContDiff ℝ ∞ (fun z : ℂ => ((Complex.normSq z : ℝ) : ℂ)) := by
  have h : ContDiff ℝ ∞ (fun z : ℂ => ‖z‖ ^ 2) := contDiff_norm_sq ℝ
  have e : (fun z : ℂ => ((Complex.normSq z : ℝ) : ℂ)) = fun z => Complex.ofRealCLM (‖z‖ ^ 2) := by
    funext z; simp [Complex.normSq_eq_norm_sq]
  rw [e]
  exact Complex.ofRealCLM.contDiff.comp h

end GlobalTheory.KappaCut


open GlobalTheory.KappaCut in
theorem GlobalTheory.KappaCut.exists_kappa : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (x₀ : GA E (m + 1)),
    ∃ κ : GA E (m + 1) → ℝ, Continuous κ ∧ (∀ h, 0 ≤ κ h) ∧ (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ h, κ (u * h) = κ h) ∧
      (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ h, κ h ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * h ∈ C) ∧
      (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧
        ∀ u ∈ U, ∀ h, κ (h * finGL E (m + 1) u) = κ h) ∧
      (∀ g, ContDiffOn ℝ ∞ (chart (fun h => (κ h : ℂ)) g) (invSet E (m + 1))) ∧ 0 < κ x₀ := by
  intro E _ _ _ m x₀
  obtain ⟨b, hb1, hbN, ⟨C, hC, hCs⟩, ⟨U, hU, hUr⟩, hbc⟩ := GlobalTheory.WhitBump.exists_bump_glob E m
  have hbcont : Continuous b := continuous_of_chart b U hU hUr hbc
  let pI : GA E (m + 1) → GL (Fin (m + 1)) (Cinf E) := fun h => GeneralLinearGroup.map (pInf E) h
  let pF : GA E (m + 1) → GL (Fin (m + 1)) (Af E) := fun h => GeneralLinearGroup.map (pFin E) h
  have hconjF : ∀ k, x₀ * finGL E (m + 1) k * x₀⁻¹ = finGL E (m + 1) (pF x₀ * k * (pF x₀)⁻¹) := by
    intro k; refine ga_ext ?_ ?_ <;> simp [pF]
  have hconjI : ∀ y, x₀ * infGL E (m + 1) y * x₀⁻¹ = infGL E (m + 1) (pI x₀ * y * (pI x₀)⁻¹) := by
    intro y; refine ga_ext ?_ ?_ <;> simp [pI]
  refine ⟨fun h => Complex.normSq (b (h * x₀⁻¹)), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Complex.continuous_normSq.comp (hbcont.comp (continuous_id.mul continuous_const))
  · intro h; exact Complex.normSq_nonneg _
  · intro u hu h
    show Complex.normSq (b (u * h * x₀⁻¹)) = Complex.normSq (b (h * x₀⁻¹))
    rw [mul_assoc, hbN u hu, map_mul, GlobalTheory.JSW.psiN, Circle.normSq_coe, one_mul]
  · refine ⟨(fun c => c * x₀) '' C, hC.image (continuous_id.mul continuous_const), fun h hh => ?_⟩
    have hb : b (h * x₀⁻¹) ≠ 0 := fun e => hh (by simp [e])
    obtain ⟨u, hu, huC⟩ := hCs _ hb
    exact ⟨u, hu, ⟨_, huC, by group⟩⟩
  · refine ⟨U.comap (MulAut.conj (pF x₀)).toMonoidHom, ?_, ?_⟩
    · rw [Subgroup.coe_comap]
      exact hU.preimage ((continuous_const.mul continuous_id).mul continuous_const)
    · intro u hu h
      have hu' : pF x₀ * u * (pF x₀)⁻¹ ∈ U := hu
      show Complex.normSq (b (h * finGL E (m + 1) u * x₀⁻¹)) = Complex.normSq (b (h * x₀⁻¹))
      have e : h * finGL E (m + 1) u * x₀⁻¹ = h * x₀⁻¹ * finGL E (m + 1) (pF x₀ * u * (pF x₀)⁻¹) := by
        rw [← hconjF]; group
      rw [e, hUr _ hu']
  · intro g
    set A : GL (Fin (m + 1)) (Cinf E) := pI x₀ with hA
    let L0 : Lie E (m + 1) →ₗ[ℝ] Lie E (m + 1) :=
      { toFun := fun x => toL ((A : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) * Matrix.of x *
          ((A⁻¹ : GL (Fin (m + 1)) (Cinf E)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)))
        map_add' := fun x y => by
          show toL (_ * (Matrix.of x + Matrix.of y) * _) = _
          rw [Matrix.mul_add, Matrix.add_mul]; rfl
        map_smul' := fun c x => by
          show toL (_ * (c • Matrix.of x) * _) = _
          rw [Matrix.mul_smul, Matrix.smul_mul]; rfl }
    let L : Lie E (m + 1) →L[ℝ] Lie E (m + 1) := LinearMap.toContinuousLinearMap L0
    have hLx : ∀ x : Lie E (m + 1), Matrix.of (L x) = (A : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) * Matrix.of x *
        ((A⁻¹ : GL (Fin (m + 1)) (Cinf E)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) := by
      intro x
      simp only [L]
      erw [LinearMap.coe_toContinuousLinearMap']
      rfl
    have hmaps : Set.MapsTo L (invSet E (m + 1)) (invSet E (m + 1)) := fun x hx => by
      have hx' : IsUnit (Matrix.of x) := hx
      show IsUnit (Matrix.of (L x))
      rw [hLx]
      exact (A.isUnit.mul hx').mul (A⁻¹).isUnit
    have h2 : ContDiffOn ℝ ∞ (fun x => chart b (g * x₀⁻¹) (L x)) (invSet E (m + 1)) :=
      (hbc (g * x₀⁻¹)).comp L.contDiff.contDiffOn hmaps
    have h3 := contDiff_normSq_ofReal.comp_contDiffOn h2
    refine h3.congr fun x hx => ?_
    have hx' : IsUnit (Matrix.of x) := hx
    have hL' : IsUnit (Matrix.of (L x)) := hmaps hx
    simp only [Function.comp, chart, dif_pos hx', dif_pos hL']
    congr 3
    have hu : hL'.unit = A * hx'.unit * A⁻¹ := Units.ext (by rw [IsUnit.unit_spec, hLx]; simp)
    rw [hu, ← hconjI]; group
  · simp [hb1]

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContDiffOnChartGlobalWhittakerCoefficient
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
open Matrix

noncomputable section

namespace GlobalTheory.JSW.WhitSmooth

open GroundTheory.Automorphic.FourierWhittaker GlobalTheory.ConstTermSmooth

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem chart_oneL (F : GA E a → ℂ) (g : GA E a) : chart F g (oneL E a) = F g := by
  have := chart_val F g 1
  simpa using this

theorem chart_whit (F : GA E a → ℂ) (g : GA E a) :
    chart (GlobalTheory.JSW.whit F) g = fun y => ∫ X in vecDomain E (Pos a),
      chart F (uGL X * g) y * (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ) ∂vecMeasure E (Pos a) := by
  funext y
  by_cases h : IsUnit (Matrix.of y)
  · simp only [chart, dif_pos h, GlobalTheory.JSW.WhitAlg.whit_eq, mul_assoc]
  · simp only [chart, dif_neg h, zero_mul, integral_zero]

theorem hasFDerivAt_chart_whit {φ : Sm E a} (h : Good φ) (g : GA E a) :
    HasFDerivAt (chart (GlobalTheory.JSW.whit φ.1) g)
      (∫ X in vecDomain E (Pos a), (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ) •
        fderiv ℝ (chart φ.1 (uGL X * g)) (oneL E a) ∂vecMeasure E (Pos a)) (oneL E a) := by
  rw [chart_whit]
  have hy : oneL E a ∈ invSet E a := isUnit_one
  obtain ⟨S, hSy, hSU, hS⟩ := local_compact_nhds (isOpen_invSet.mem_nhds hy)
  have hm : Continuous fun p : (Pos a → Ad E) × Lie E a => ((uGL p.1 * g, p.2) : GA E a × Lie E a) :=
    ((continuous_uGL.comp continuous_fst).mul continuous_const).prodMk continuous_snd
  have hmt : Set.MapsTo (fun p : (Pos a → Ad E) × Lie E a => ((uGL p.1 * g, p.2) : GA E a × Lie E a))
      (Set.univ ×ˢ invSet E a) (Set.univ ×ˢ invSet E a) := fun p hp => ⟨Set.mem_univ _, hp.2⟩
  have hc := h.continuousOn_fderiv.comp hm.continuousOn hmt
  have hc0 := h.continuousOn_chart.comp hm.continuousOn hmt
  obtain ⟨C, hC⟩ := (isCompact_closure_vecDomain.prod hS).exists_bound_of_continuousOn
    (hc.mono (Set.prod_mono (Set.subset_univ _) hSU))
  have hint : ∀ z ∈ invSet E a, Integrable (fun X => chart φ.1 (uGL X * g) z *
      (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ)) ((vecMeasure E (Pos a)).restrict (vecDomain E (Pos a))) :=
    fun z hz => ((((hc0.comp_continuous (continuous_id.prodMk continuous_const) fun _ => ⟨trivial, hz⟩)).mul
      GlobalTheory.JSW.WhitAlg.continuous_psiNeg).continuousOn.integrableOn_compact isCompact_closure_vecDomain).mono_set
      subset_closure
  have hint' : Integrable (fun X => (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ) •
      fderiv ℝ (chart φ.1 (uGL X * g)) (oneL E a)) ((vecMeasure E (Pos a)).restrict (vecDomain E (Pos a))) :=
    ((GlobalTheory.JSW.WhitAlg.continuous_psiNeg.smul (hc.comp_continuous (continuous_id.prodMk continuous_const)
      fun _ => ⟨trivial, hy⟩)).continuousOn.integrableOn_compact isCompact_closure_vecDomain).mono_set subset_closure
  haveI : IsFiniteMeasure ((vecMeasure E (Pos a)).restrict (vecDomain E (Pos a))) :=
    ⟨by rw [Measure.restrict_apply_univ, vecMeasure_vecDomain]; exact ENNReal.one_lt_top⟩
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun _ => C)
    (F' := fun z X => (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ) • fderiv ℝ (chart φ.1 (uGL X * g)) z) hSy
    (Filter.eventually_of_mem (isOpen_invSet.mem_nhds hy) fun z hz => (hint z hz).1) (hint _ hy) hint'.1
    ?_ (integrable_const C) ?_
  · filter_upwards [ae_restrict_mem measurableSet_vecDomain] with X hX z hz
    rw [norm_smul, Circle.norm_coe, one_mul]
    exact hC (X, z) ⟨subset_closure hX, hz⟩
  · refine .of_forall fun X z hz => ?_
    exact ((contDiffAt_chart φ.2 _ (hSU hz)).differentiableAt (by simp)).hasFDerivAt.mul_const _

theorem hasFDerivAt_chart_whit' {φ : Sm E a} (h : Good φ) (g : GA E a) :
    HasFDerivAt (chart (GlobalTheory.JSW.whit φ.1) g)
      (∑ i, GlobalTheory.JSW.whit (lie E a (Module.finBasis ℝ (Lie E a) i) φ).1 g • coef i (oneL E a)) (oneL E a) := by
  refine (hasFDerivAt_chart_whit h g).congr_fderiv ?_
  have hy : oneL E a ∈ invSet E a := isUnit_one
  have e : ∀ X : Pos a → Ad E, (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ) •
      fderiv ℝ (chart φ.1 (uGL X * g)) (oneL E a) = ∑ i,
        (chart (lie E a (Module.finBasis ℝ (Lie E a) i) φ).1 (uGL X * g) (oneL E a) *
          (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ)) • coef i (oneL E a) := fun X => by
    rw [fderiv_chart φ _ hy, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, mul_comm]
  simp_rw [e]
  rw [integral_finsetSum _ fun i _ => ?_]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_smul_const, ← congrFun (chart_whit _ g) (oneL E a), chart_oneL]
  · have hl := h.lie (Module.finBasis ℝ (Lie E a) i)
    refine (Integrable.smul_const ?_ _)
    simp_rw [chart_oneL]
    exact GlobalTheory.JSW.WhitAlg.integrableOn_whit (ContAut.continuous_of_isOpen_stab E a _ hl.2) g

theorem whit_mem_Sm (φ : Sm E a) (h : Good φ) : GlobalTheory.JSW.whit φ.1 ∈ Sm E a := by
  refine GlobalTheory.SmOfDeriv.mem_Sm_of_hasFDerivAt E a {f | ∃ ψ : Sm E a, Good ψ ∧ f = GlobalTheory.JSW.whit ψ.1} ?_ _
    ⟨φ, h, rfl⟩
  rintro f ⟨ψ, hψ, rfl⟩
  exact ⟨_, inferInstance, fun i => GlobalTheory.JSW.whit (lie E a (Module.finBasis ℝ (Lie E a) i) ψ).1,
    fun i => coef i (oneL E a), fun i => ⟨_, hψ.lie _, rfl⟩, hasFDerivAt_chart_whit' hψ⟩

theorem whit_contDiffOn : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a),
    IsAutForm φ → ∀ g, ContDiffOn ℝ ∞ (chart (GlobalTheory.JSW.whit φ.1) g) (invSet E a) := by
  intro E _ _ _ a φ hφ g
  exact whit_mem_Sm φ ⟨hφ.left, hφ.level⟩ g

end GlobalTheory.JSW.WhitSmooth
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockGLSupportedMemMirabolicSupported
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockGLSupportedMemMirabolicSupported
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
open Matrix

namespace GlobalTheory.BlockMirabolic

theorem blockGL_mem_mirS : ∀ (E : Type) [Field E] [NumberField E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))),
    ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S,
      GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h ∈ (GlobalTheory.JSW.supS (E := E) (a := (m + r + 1) + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) (m + r + 1)) := by
  intro E _ _ m r S h hh
  constructor
  · intro w hw
    have hw1 := congrArg Units.val (hh w hw)
    apply Units.ext
    simp only [Units.val_one] at hw1 ⊢
    change ((GroundTheory.Automorphic.FourierWhittaker.blockMat _ h.val).map _) = 1
    change (h.val.map _) = 1 at hw1
    rw [GroundTheory.Automorphic.FourierWhittaker.map_blockMat, hw1, GroundTheory.Automorphic.FourierWhittaker.blockMat_one]
  · intro j
    change GroundTheory.Automorphic.FourierWhittaker.blockMat _ h.val (Fin.last (m + r + 1)) j = _
    rw [GroundTheory.Automorphic.FourierWhittaker.blockMat_apply, dite_eq_right (by simp)]
    simp only [eq_comm]

end GlobalTheory.BlockMirabolic
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockGLSupportedMemMirabolicSupportedStatement
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockGL_supported_mem_mirabolic_supported : ∀ (E : Type) [Field E] [NumberField E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))),
    ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S,
      GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h ∈ (GlobalTheory.JSW.supS (E := E) (a := (m + r + 1) + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) (m + r + 1)) := by
  first | (exact @GlobalTheory.BlockMirabolic.blockGL_mem_mirS) | (exact GlobalTheory.BlockMirabolic.blockGL_mem_mirS) | (intros; apply GlobalTheory.BlockMirabolic.blockGL_mem_mirS  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMatchedWhittakerVectorsShintaniRelations
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
open Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.Tx.exists_unipotentInvariant_compactlySupported_weight : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (x₀ : GA E (m + 1)),
    ∃ κ : GA E (m + 1) → ℝ, Continuous κ ∧ (∀ h, 0 ≤ κ h) ∧ (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ h, κ (u * h) = κ h) ∧
      (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ h, κ h ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * h ∈ C) ∧
      (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧
        ∀ u ∈ U, ∀ h, κ (h * finGL E (m + 1) u) = κ h) ∧
      (∀ g, ContDiffOn ℝ ∞ (chart (fun h => (κ h : ℂ)) g) (invSet E (m + 1))) ∧ 0 < κ x₀ := by
  first
  | exact @GlobalTheory.KappaCut.exists_kappa
  | exact GlobalTheory.KappaCut.exists_kappa
  | (intros; apply GlobalTheory.KappaCut.exists_kappa <;> assumption)
end

section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
open Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.Tx.contDiffOn_chart_globalWhittakerCoefficient : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a),
    IsAutForm φ → ∀ g, ContDiffOn ℝ ∞ (chart (GlobalTheory.JSW.whit φ.1) g) (invSet E a) := by
  first | (exact @GlobalTheory.JSW.WhitSmooth.whit_contDiffOn) | (exact GlobalTheory.JSW.WhitSmooth.whit_contDiffOn) | (intros; apply GlobalTheory.JSW.WhitSmooth.whit_contDiffOn  <;> assumption)
end

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
open Matrix

namespace GlobalTheory.JSW.MatchedVec

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem mem_mspanR_of_mem (π : CuspSub E a) {φ : Sm E a} (hφ : φ ∈ π.V) : φ.1 ∈ GlobalTheory.JSW.mspanR π :=
  Submodule.mem_sInf.2 fun _ hS => hS.1 φ hφ

def stab (φ : Sm E a) : Subgroup (GL (Fin a) (Af E)) where
  carrier := {k | finRep E a k φ = φ}
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at *
    rw [map_mul, Module.End.mul_apply, hy, hx]
  inv_mem' := by
    intro x hx
    simp only [Set.mem_setOf_eq] at *
    conv_lhs => rw [← hx]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem exists_level (φ : Sm E a) (hφ : IsAutForm φ) :
    ∃ U : Subgroup (GL (Fin a) (Af E)), IsOpen (U : Set (GL (Fin a) (Af E))) ∧
      ∀ u ∈ U, ∀ g, φ.1 (g * finGL E a u) = φ.1 g :=
  ⟨stab φ, hφ.level, fun u hu g => congrArg (fun ψ : Sm E a => ψ.1 g) (show finRep E a u φ = φ from hu)⟩

theorem chart_mul (f f' : GA E a → ℂ) (g : GA E a) (x : Lie E a) :
    chart (fun h => f h * f' h) g x = chart f g x * chart f' g x := by
  unfold chart
  split_ifs <;> simp

end GlobalTheory.JSW.MatchedVec


open GlobalTheory.JSW.MatchedVec in
theorem GlobalTheory.JSW.MatchedVec.matched_vectors : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))),
    (∀ w ∉ S, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w (x * y))) : ℂ) = 1) ↔ x ∈ Ov E w) →
    ∀ (π : CuspSub E (m + r + 1 + 1)) (π' : CuspSub E (m + 1)), π.IsUnitary → π'.IsUnitary →
    ∀ (α : HeightOneSpectrum (𝓞 E) → Fin (m + r + 1 + 1) → ℂˣ) (β : HeightOneSpectrum (𝓞 E) → Fin (m + 1) → ℂˣ),
    (∀ w ∉ S, HasSatGL w (π.locRep w) (Finset.univ.val.map (α w))) →
    (∀ w ∉ S, HasSatGL w (π'.locRep w) (Finset.univ.val.map (β w))) →
    ∃ (φ : GA E (m + r + 1 + 1) → ℂ) (φ' : GA E (m + 1) → ℂ) (κ : GA E (m + 1) → ℝ),
      φ ∈ GlobalTheory.JSW.mspanR π ∧ φ' ∈ GlobalTheory.JSW.mspanR π' ∧
      (∃ U : Subgroup (GL (Fin (m + r + 1 + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + r + 1 + 1)) (Af E))) ∧
        ∀ u ∈ U, ∀ g, φ (g * finGL E (m + r + 1 + 1) u) = φ g) ∧
      (∀ w ∉ S, ∀ k ∈ KGL w (n := (m + r + 1 + 1)), ∀ g,
        φ (g * finGL E (m + r + 1 + 1) (locGL E (m + r + 1 + 1) w k)) = φ g) ∧
      (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧
        ∀ u ∈ U, ∀ g, φ' (g * finGL E (m + 1) u) = φ' g) ∧
      (∀ w ∉ S, ∀ k ∈ KGL w (n := (m + 1)), ∀ g, φ' (g * finGL E (m + 1) (locGL E (m + 1) w k)) = φ' g) ∧
      (∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
        ∀ l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ), (∀ w ∈ l.support, w ∉ S) →
        ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S,
          GlobalTheory.JSW.whit φ' (h * GlobalTheory.JSW.tl ϖ l) =
            (∏ w ∈ l.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (β w i : ℂ)) (l w)) * GlobalTheory.JSW.whit φ' h) ∧
      (∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
        ∀ l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ), (∀ w ∈ l.support, w ∉ S) →
        ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S,
          GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1)
                       (h * GlobalTheory.JSW.tl ϖ l)) =
            (∏ w ∈ l.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (α w i : ℂ)) (GlobalTheory.RSnmUnf.padNat (l w))) *
              GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h)) ∧
      (∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S,
        GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h) =
          (κ h : ℂ) * GlobalTheory.JSW.whit φ' h) ∧
      Continuous κ ∧ (∀ h, 0 ≤ κ h) ∧ (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ h, κ (u * h) = κ h) ∧
      (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, κ h ≠ 0 →
        ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * h ∈ C) ∧
      (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧
        ∀ u ∈ U, ∀ h, κ (h * finGL E (m + 1) u) = κ h) ∧
      ∃ h₀ ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, 0 < κ h₀ ∧ GlobalTheory.JSW.whit φ' h₀ ≠ 0 := by
  intro E _ _ _ m r S hcond π π' hπu hπ'u α β hα hβ
  obtain ⟨φ', hφ'V, hφ'K, x₀, hx₀S, hx₀⟩ := GlobalTheory.T.exists_spherical_cuspForm_whittaker_ne_zero E m S hcond π' β hβ
  obtain ⟨φ₀, hφ₀V, hφ₀K, x₁, hx₁S, hx₁⟩ := GlobalTheory.T.exists_spherical_cuspForm_whittaker_ne_zero E (m + r + 1) S hcond π α hα
  obtain ⟨κ, hκc, hκ0, hκN, ⟨C, hC, hκC⟩, ⟨Uκ, hUκo, hUκ⟩, hκsm, hκx₀⟩ := GlobalTheory.Tx.exists_unipotentInvariant_compactlySupported_weight E m x₀
  have haut' : IsAutForm φ' := (π'.cusp φ' hφ'V).1
  obtain ⟨U', hU'o, hU'⟩ := exists_level φ' haut'
  have hWN : ∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, GlobalTheory.JSW.whit φ'.1 (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ'.1 g :=
    fun u hu g => GlobalTheory.JSW.WhitModel.whit_mul haut'.continuous (fun γ g => haut'.left γ g) hu g
  have hWU : ∀ u ∈ U', ∀ g, GlobalTheory.JSW.whit φ'.1 (g * finGL E (m + 1) u) = GlobalTheory.JSW.whit φ'.1 g := by
    intro u hu g
    rw [← GlobalTheory.JSW.KirSemi.whit_rt]
    congr 1
    funext y
    exact hU' u hu y
  have hWsm := GlobalTheory.Tx.contDiffOn_chart_globalWhittakerCoefficient E (m + 1) φ' haut'
  set βf : GA E (m + 1) → ℂ := fun h => (κ h : ℂ) * GlobalTheory.JSW.whit φ'.1 h with hβf
  have hβN : ∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, βf (u * g) = GlobalTheory.JSW.psiN u * βf g := by
    intro u hu g
    simp only [hβf, hκN u hu g, hWN u hu g]
    ring
  have hβC : ∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, βf h ≠ 0 →
      ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * h ∈ C := by
    refine ⟨C, hC, fun h _ hne => hκC h ?_⟩
    intro h0
    apply hne
    simp [hβf, h0]
  have hβU : ∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧
      ∀ u ∈ U, ∀ g, βf (g * finGL E (m + 1) u) = βf g := by
    refine ⟨Uκ ⊓ U', hUκo.inter hU'o, fun u hu g => ?_⟩
    simp only [hβf, hUκ u hu.1 g, hWU u hu.2 g]
  have hβsm : ∀ g, ContDiffOn ℝ ∞ (chart βf g) (invSet E (m + 1)) := by
    intro g
    have e : chart βf g = fun x => chart (fun h => (κ h : ℂ)) g x * chart (GlobalTheory.JSW.whit φ'.1) g x :=
      funext fun x => chart_mul _ _ g x
    rw [e]
    exact (hκsm g).mul (hWsm g)
  obtain ⟨b, hbN, hbC, hbU, hbsm, hbblk⟩ := GlobalTheory.T.exists_whittaker_bump_extension_schur_complement E m r S βf hβN hβC hβU hβsm
  obtain ⟨F, hFspan, hFb, hFU, hFinv, hFeig⟩ :=
    GlobalTheory.T.kirillov_semilocal_smooth_bump E (m + r + 1) S b hbN hbC hbU hbsm π φ₀ hφ₀V ⟨x₁, hx₁S, hx₁⟩
  refine ⟨F, φ'.1, κ, hFspan, mem_mspanR_of_mem π' hφ'V, hFU, ?_, ⟨U', hU'o, hU'⟩, ?_, ?_, ?_, ?_,
    hκc, hκ0, hκN, ⟨C, hC, fun h _ hne => hκC h hne⟩, ⟨Uκ, hUκo, hUκ⟩, ⟨x₀, hx₀S, hκx₀, hx₀⟩⟩
  · intro w hw k hk g
    refine hFinv _ (pInf_finGL _) ?_ ?_ g
    · intro w' hw'
      have hne : w' ≠ w := fun h => hw (h ▸ hw')
      rw [GlobalTheory.JSW.BumpShintani.map_comp_eq, pFin_finGL]
      exact pLoc_locGL_of_ne hne _
    · intro g'
      exact congrArg (fun ψ : Sm E (m + r + 1 + 1) => ψ.1 g') (hφ₀K w hw k hk)
  · intro w hw k hk g
    exact congrArg (fun ψ : Sm E (m + 1) => ψ.1 g) (hφ'K w hw k hk)
  · intro ϖ hϖ l hl h hh
    exact GlobalTheory.T.whittaker_mul_torus_iterated_factorisation E (m + 1) S hcond π' β hβ φ' hφ'V hφ'K ϖ hϖ l hl h hh
  · intro ϖ hϖ l hl h hh
    set l' : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + r + 1 + 1) → ℕ) :=
      l.mapRange GlobalTheory.RSnmUnf.padNat GlobalTheory.RSnmUnf.padNat_zero with hl'
    have hsupp : l'.support = l.support := by
      ext w
      simp only [hl', Finsupp.mem_support_iff, Finsupp.mapRange_apply, ne_eq]
      constructor
      · intro h1 h2
        apply h1
        rw [h2, GlobalTheory.RSnmUnf.padNat_zero]
      · intro h1 h2
        apply h1
        funext i
        have := congrFun h2 ⟨i, by omega⟩
        simpa [GlobalTheory.RSnmUnf.padNat, i.2] using this
    have hl's : ∀ w ∈ l'.support, w ∉ S := fun w hw => hl w (hsupp ▸ hw)
    have hC := GlobalTheory.T.whittaker_mul_torus_iterated_factorisation E (m + r + 1 + 1) S hcond π α hα φ₀ hφ₀V hφ₀K ϖ hϖ l' hl's
    have hS : ∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) (GlobalTheory.JSW.tl ϖ l') = 1 :=
      fun w hw => GlobalTheory.JSW.BumpShintani.loc_tl ϖ l' w (fun h => hl's w h hw)
    have hmir := GlobalTheory.T.blockGL_supported_mem_mirabolic_supported E m r S h hh
    rw [map_mul, GlobalTheory.T.blockEmbeddingGL_torus_element_zero_padded E m r ϖ l, hFeig _ _ (GlobalTheory.JSW.BumpShintani.pInf_tl ϖ l') hS hC _ hmir.1, hsupp]
    rfl
  · intro h hh
    clear hβsm hβU hβC hβN hWsm hWU hWN hFeig hFinv
    exact (hFb _ (GlobalTheory.T.blockGL_supported_mem_mirabolic_supported E m r S h hh)).trans (hbblk h hh)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMatchedWhittakerVectorsShintaniRelationsStatement
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_matchedWhittakerVectors_shintaniRelations : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))),
    (∀ w ∉ S, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w (x * y))) : ℂ) = 1) ↔ x ∈ Ov E w) →
    ∀ (π : CuspSub E (m + r + 1 + 1)) (π' : CuspSub E (m + 1)), π.IsUnitary → π'.IsUnitary →
    ∀ (α : HeightOneSpectrum (𝓞 E) → Fin (m + r + 1 + 1) → ℂˣ) (β : HeightOneSpectrum (𝓞 E) → Fin (m + 1) → ℂˣ),
    (∀ w ∉ S, HasSatGL w (π.locRep w) (Finset.univ.val.map (α w))) →
    (∀ w ∉ S, HasSatGL w (π'.locRep w) (Finset.univ.val.map (β w))) →
    ∃ (φ : GA E (m + r + 1 + 1) → ℂ) (φ' : GA E (m + 1) → ℂ) (κ : GA E (m + 1) → ℝ),
      φ ∈ GlobalTheory.JSW.mspanR π ∧ φ' ∈ GlobalTheory.JSW.mspanR π' ∧
      (∃ U : Subgroup (GL (Fin (m + r + 1 + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + r + 1 + 1)) (Af E))) ∧
        ∀ u ∈ U, ∀ g, φ (g * finGL E (m + r + 1 + 1) u) = φ g) ∧
      (∀ w ∉ S, ∀ k ∈ KGL w (n := (m + r + 1 + 1)), ∀ g,
        φ (g * finGL E (m + r + 1 + 1) (locGL E (m + r + 1 + 1) w k)) = φ g) ∧
      (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧
        ∀ u ∈ U, ∀ g, φ' (g * finGL E (m + 1) u) = φ' g) ∧
      (∀ w ∉ S, ∀ k ∈ KGL w (n := (m + 1)), ∀ g, φ' (g * finGL E (m + 1) (locGL E (m + 1) w k)) = φ' g) ∧
      (∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
        ∀ l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ), (∀ w ∈ l.support, w ∉ S) →
        ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S,
          GlobalTheory.JSW.whit φ' (h * GlobalTheory.JSW.tl ϖ l) =
            (∏ w ∈ l.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (β w i : ℂ)) (l w)) * GlobalTheory.JSW.whit φ' h) ∧
      (∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
        ∀ l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ), (∀ w ∈ l.support, w ∉ S) →
        ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S,
          GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1)
                       (h * GlobalTheory.JSW.tl ϖ l)) =
            (∏ w ∈ l.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (α w i : ℂ)) (GlobalTheory.RSnmUnf.padNat (l w))) *
              GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h)) ∧
      (∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S,
        GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h) =
          (κ h : ℂ) * GlobalTheory.JSW.whit φ' h) ∧
      Continuous κ ∧ (∀ h, 0 ≤ κ h) ∧ (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ h, κ (u * h) = κ h) ∧
      (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, κ h ≠ 0 →
        ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * h ∈ C) ∧
      (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧
        ∀ u ∈ U, ∀ h, κ (h * finGL E (m + 1) u) = κ h) ∧
      ∃ h₀ ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, 0 < κ h₀ ∧ GlobalTheory.JSW.whit φ' h₀ ≠ 0 := by
  first | (exact @GlobalTheory.JSW.MatchedVec.matched_vectors) | (exact GlobalTheory.JSW.MatchedVec.matched_vectors) | (intros; apply GlobalTheory.JSW.MatchedVec.matched_vectors  <;> assumption)
end
