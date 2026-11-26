module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemBddFormsOfWithSmoothings
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsComplexLinearExtensionCoefficientMap
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftDatumThetaSeriesRightInvariantCoreLevel
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MellinIntegralRapidDecayEntireOfLeOne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegrableInfMeasure
noncomputable section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.ThetaPoisson GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped ComplexConjugate nonZeroDivisors ContDiff
open GlobalTheory.RSTheta GlobalTheory.ShortVecDecay GlobalTheory.Petersson GlobalTheory.CuspQuot Topology

namespace GlobalTheory.RSThetaLow

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem continuous_invT {R : Type} [CommRing R] [TopologicalSpace R] : Continuous (invT a R) :=
  Units.continuous_iff.2 ⟨Units.continuous_coe_inv.matrix_transpose, Units.continuous_val.matrix_transpose⟩

theorem invT_invT {R : Type} [CommRing R] (g : GL (Fin a) R) : invT a R (invT a R g) = g :=
  Units.ext (transpose_transpose _)

theorem decays_invT_smoothInf {F : GA E a → ℂ} (hF : Decays fun g => F (invT a (Ad E) g)) {f : Lie E a → ℂ}
    (hf : IsTest (invSet E a) f) : Decays fun g => GlobalTheory.JSW.smoothInf f F (invT a (Ad E) g) := by
  intro L hL C₀ hC₀ N
  have hK : IsCompact ((fun y : GL (Fin a) (Cinf E) => toL y.val) ⁻¹' tsupport f) :=
    isOpenEmbedding_val.isInducing.isCompact_preimage' hf.2.1 fun x hx => hf.2.2 hx
  obtain ⟨C, h⟩ := hF L hL _ (hC₀.mul ((hK.image continuous_infGL).image continuous_invT)) N
  have hi : Integrable f := hf.1.continuous.integrable_of_hasCompactSupport hf.2.1
  refine ⟨(∫ x, ‖f x‖) * C, fun g c hcC ξ hξ hm => ?_⟩
  rw [mul_assoc, ← integral_mul_const]
  refine norm_integral_le_of_norm_le (hi.norm.mul_const _) (.of_forall fun x => ?_)
  by_cases hx : x ∈ tsupport f
  · obtain ⟨u, hu⟩ := hf.2.2 hx
    obtain rfl : x = toL u.val := hu.symm
    rw [norm_mul, chart_val]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have h1 := h g _ (Set.mul_mem_mul hcC ⟨_, ⟨u, hx, rfl⟩, rfl⟩) ξ hξ hm
    simpa only [map_mul, invT_invT, mul_assoc] using h1
  · simp [image_eq_zero_of_notMem_tsupport hx]

theorem decays_invT {π : CuspSub E a} (hπ : π.IsUnitary) {φ : Sm E a} (hφ : φ ∈ withSmoothings π) :
    Decays fun g => φ.1 (invT a (Ad E) g) := by
  let D : Submodule ℂ (Sm E a) :=
    { carrier := {φ | Decays fun g => φ.1 (invT a (Ad E) g)}
      add_mem' := fun {φ ψ} h h' => Decays.add (F := fun g => φ.1 (invT a (Ad E) g)) (G := fun g => ψ.1 (invT a (Ad E) g)) h h'
      zero_mem' := Decays.zero
      smul_mem' := fun z φ h => Decays.smul (F := fun g => φ.1 (invT a (Ad E) g)) h z }
  have h0 : π.V ≤ D := fun ψ hψ =>
    decays_of_mem (CuspSub.IsUnitary.contra hπ) (φ := UpperTheory.V.TC.dualFn E a ψ) ⟨ψ, hψ, rfl⟩
  refine (sup_le h0 (Submodule.span_le.2 ?_) : withSmoothings π ≤ D) hφ
  rintro F ⟨f, ψ, hf, hψ, e⟩
  change Decays fun g => F.1 (invT a (Ad E) g)
  rw [e]
  exact decays_invT_smoothInf (h0 hψ) hf

theorem continuous_bounded {π : CuspSub E a} (hπ : π.IsUnitary) {φ : Sm E a} (hφ : φ ∈ withSmoothings π) :
    Continuous φ.1 ∧ ∃ C : ℝ, ∀ g, ‖φ.1 g‖ ≤ C := by
  obtain ⟨χ, hω, h⟩ := hπ
  have := mem_bddForms_of_withSmoothings (GlobalTheory.CuspBoundSiegel.cuspFormsBounded_of_rapidDecay
    (GlobalTheory.cuspRapidDecaySiegelGL_of_finite GlobalTheory.automorphicFormsFiniteGL)) hω (CuspSub.hasCentral_iff.1 h) hφ
  exact ⟨this.1, this.2.2.2⟩


omit [_root_.NumberField.IsTotallyComplex E] in
def rowInv (ℓ : Fin a) (y : Fin a → Cinf E) : Lie E a := invL (toL (rowMat ℓ y))

omit [_root_.NumberField.IsTotallyComplex E] in
theorem contDiff_rowMat (ℓ : Fin a) : ContDiff ℝ ∞ fun y : Fin a → Cinf E => toL (rowMat ℓ y) := by
  refine contDiff_pi.2 fun i => ?_
  by_cases h : i = ℓ
  · subst h
    have : (fun y : Fin a → Cinf E => toL (rowMat i y) i) = id := funext fun y => updateRow_self
    rw [this]; exact contDiff_id
  · have : (fun y : Fin a → Cinf E => toL (rowMat ℓ y) i) = fun _ => (1 : Matrix (Fin a) (Fin a) (Cinf E)) i :=
      funext fun y => updateRow_ne h
    rw [this]; exact contDiff_const

omit [_root_.NumberField.IsTotallyComplex E] in
theorem contDiffAt_rowInv {ℓ : Fin a} {y : Fin a → Cinf E} (hy : y ∈ rowSet E ℓ) : ContDiffAt ℝ ∞ (rowInv ℓ) y :=
  (contDiffAt_invL (isUnit_rowMat_iff.2 (isUnit_of_mem_rowSet hy))).comp y (contDiff_rowMat ℓ).contDiffAt

omit [_root_.NumberField.IsTotallyComplex E] in
theorem rowInv_eq {ℓ : Fin a} {y : Fin a → Cinf E} (hy : y ∈ rowSet E ℓ) : rowInv ℓ y = toL ((rowGL ℓ y)⁻¹).val := by
  rw [rowInv, ← val_rowGL (isUnit_of_mem_rowSet hy), invL_val]

theorem chart_rowInv (F : GA E a → ℂ) (g : GA E a) {ℓ : Fin a} {y : Fin a → Cinf E} (hy : y ∈ rowSet E ℓ) :
    F (g * (infGL E a (rowGL ℓ y))⁻¹) = chart F g (rowInv ℓ y) := by
  rw [rowInv_eq hy, chart_val, map_inv]

theorem contDiffAt_translate (F : Sm E a) (g : GA E a) {ℓ : Fin a} {y : Fin a → Cinf E} (hy : y ∈ rowSet E ℓ) :
    ContDiffAt ℝ ∞ (fun y => F.1 (g * (infGL E a (rowGL ℓ y))⁻¹)) y :=
  ((contDiffAt_chart F.2 g (rowInv_eq hy ▸ val_mem_invSet _)).comp y (contDiffAt_rowInv hy)).congr_of_eventuallyEq
    (Filter.eventually_of_mem ((isOpen_rowSet ℓ).mem_nhds hy) fun _ hz => chart_rowInv _ g hz)


omit [_root_.NumberField.IsTotallyComplex E] in
def rowCoef (ℓ : Fin a) (v : Fin a → Cinf E) (β : Fin (Module.finrank ℝ (Lie E a))) (y : Fin a → Cinf E) : ℂ :=
  ((Module.finBasis ℝ (Lie E a)).coord β (toL (rowMat ℓ y * Matrix.of (fderiv ℝ (rowInv ℓ) y v))) : ℝ)

omit [_root_.NumberField.IsTotallyComplex E] in
theorem contDiffOn_rowCoef (ℓ : Fin a) (v : Fin a → Cinf E) (β : Fin (Module.finrank ℝ (Lie E a))) :
    ContDiffOn ℝ ∞ (rowCoef ℓ v β) (rowSet E ℓ) := fun y hy => by
  refine ContDiffAt.contDiffWithinAt (Complex.ofRealCLM.contDiff.contDiffAt.comp y
    ((LinearMap.toContinuousLinearMap ((Module.finBasis ℝ (Lie E a)).coord β)).contDiff.contDiffAt.comp y ?_))
  have h1 : ContDiffAt ℝ ∞ (fun y => fderiv ℝ (rowInv ℓ) y v) y :=
    ((contDiffAt_rowInv hy).fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const
  have h2 := (contDiff_rowMat (E := E) ℓ).contDiffAt (x := y)
  refine contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun j => ?_
  change ContDiffAt ℝ ∞ (fun y => ∑ k, toL (rowMat ℓ y) i k * fderiv ℝ (rowInv ℓ) y v k j) y
  exact ContDiffAt.sum fun k _ => (contDiffAt_pi.1 (contDiffAt_pi.1 h2 i) k).mul
    (contDiffAt_pi.1 (contDiffAt_pi.1 h1 k) j)

theorem fderiv_translate (F : Sm E a) (g : GA E a) {ℓ : Fin a} {y : Fin a → Cinf E} (hy : y ∈ rowSet E ℓ)
    (v : Fin a → Cinf E) : fderiv ℝ (fun y => F.1 (g * (infGL E a (rowGL ℓ y))⁻¹)) y v =
      ∑ β, rowCoef ℓ v β y * (lie E a (Module.finBasis ℝ (Lie E a) β) F).1 (g * (infGL E a (rowGL ℓ y))⁻¹) := by
  have hm : rowInv ℓ y ∈ invSet E a := rowInv_eq hy ▸ val_mem_invSet _
  have e : (fun y => F.1 (g * (infGL E a (rowGL ℓ y))⁻¹)) =ᶠ[𝓝 y] chart F.1 g ∘ rowInv ℓ :=
    Filter.eventually_of_mem ((isOpen_rowSet ℓ).mem_nhds hy) fun _ hz => chart_rowInv _ g hz
  set X : Lie E a := toL (rowMat ℓ y * Matrix.of (fderiv ℝ (rowInv ℓ) y v)) with hX
  have h1 : rmul X (rowInv ℓ y) = fderiv ℝ (rowInv ℓ) y v := by
    rw [rowInv_eq hy, hX, ← val_rowGL (isUnit_of_mem_rowSet hy)]
    exact Units.inv_mul_cancel_left (rowGL ℓ y) (Matrix.of (fderiv ℝ (rowInv ℓ) y v))
  rw [e.fderiv_eq, fderiv_comp _ ((contDiffAt_chart F.2 g hm).differentiableAt (by simp))
    ((contDiffAt_rowInv hy).differentiableAt (by simp)), ContinuousLinearMap.comp_apply, ← h1, ← chart_lieD F.2 X g hm,
    ← chart_rowInv _ g hy]
  change fderiv ℝ (chart F.1 _) (oneL E a) X = _
  set_option synthInstance.maxHeartbeats 100000 in
    conv_lhs => rw [← (Module.finBasis ℝ (Lie E a)).sum_repr X, map_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [map_smul, Complex.real_smul]
  rfl

theorem isTest_rsInf {ℓ : Fin a} (F F' : Sm E a) {Φ : (Fin a → Cinf E) → ℂ} (hΦ : IsTest (rowSet E ℓ) Φ) (g : GA E a) :
    IsTest (rowSet E ℓ) (rsInf ℓ F.1 F'.1 Φ g) := by
  have hs : tsupport (rsInf ℓ F.1 F'.1 Φ g) ⊆ tsupport Φ := tsupport_mul_subset_right
  refine ⟨contDiff_iff_contDiffAt.2 fun y => ?_, hΦ.2.1.mul_left, hs.trans hΦ.2.2⟩
  by_cases hy : y ∈ tsupport Φ
  · exact ((contDiffAt_translate F g (hΦ.2.2 hy)).mul (Complex.conjCLE.contDiff.contDiffAt.comp y
      (contDiffAt_translate F' g (hΦ.2.2 hy)))).mul hΦ.1.contDiffAt
  · exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.1 fun h => hy (hs h))

theorem fderiv_rsInf {ℓ : Fin a} (F F' : Sm E a) {Φ : (Fin a → Cinf E) → ℂ} (hΦ : IsTest (rowSet E ℓ) Φ) (g : GA E a)
    (y v : Fin a → Cinf E) : fderiv ℝ (rsInf ℓ F.1 F'.1 Φ g) y v =
      ∑ β, rsInf ℓ (lie E a (Module.finBasis ℝ (Lie E a) β) F).1 F'.1 (fun y => rowCoef ℓ v β y * Φ y) g y +
      ∑ β, rsInf ℓ F.1 (lie E a (Module.finBasis ℝ (Lie E a) β) F').1 (fun y => rowCoef ℓ v β y * Φ y) g y +
      rsInf ℓ F.1 F'.1 (fun y => fderiv ℝ Φ y v) g y := by
  by_cases hy : y ∈ tsupport Φ
  · have h1 := ((contDiffAt_translate F g (hΦ.2.2 hy)).differentiableAt (by simp)).hasFDerivAt
    have h2 := ((contDiffAt_translate F' g (hΦ.2.2 hy)).differentiableAt (by simp)).hasFDerivAt
    have h3 := (hΦ.1.differentiable (by simp) y).hasFDerivAt
    have h4 := ((h1.mul (Complex.conjCLE.hasFDerivAt.comp y h2)).mul h3).fderiv
    refine (congrArg (· v) h4).trans ?_
    have hc : ∀ β, conj (rowCoef ℓ v β y) = rowCoef ℓ v β y := fun β => Complex.conj_ofReal _
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      fderiv_translate _ g (hΦ.2.2 hy), rsInf, smul_eq_mul, Pi.mul_apply, Function.comp_apply,
      ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, map_sum, map_mul, hc, Finset.mul_sum, mul_add]
    rw [add_comm, add_comm (∑ _, _)]
    congr 2 <;> exact Finset.sum_congr rfl fun _ _ => by ring
  · have h0 : Φ y = 0 := image_eq_zero_of_notMem_tsupport hy
    have h1 : fderiv ℝ Φ y = 0 := by
      rw [(notMem_tsupport_iff_eventuallyEq.1 hy).fderiv_eq]; simp
    have h2 : fderiv ℝ (rsInf ℓ F.1 F'.1 Φ g) y = 0 := by
      have hs : tsupport (rsInf ℓ F.1 F'.1 Φ g) ⊆ tsupport Φ := tsupport_mul_subset_right
      rw [(notMem_tsupport_iff_eventuallyEq.1 fun h => hy (hs h)).fderiv_eq]
      simp
    rw [h2]
    simp [rsInf, h0, h1]

omit [_root_.NumberField.IsTotallyComplex E] in
theorem isTest_rowCoef_mul {ℓ : Fin a} {Φ : (Fin a → Cinf E) → ℂ} (hΦ : IsTest (rowSet E ℓ) Φ) (v : Fin a → Cinf E)
    (β : Fin (Module.finrank ℝ (Lie E a))) : IsTest (rowSet E ℓ) fun y => rowCoef ℓ v β y * Φ y := by
  have hs : tsupport (fun y => rowCoef ℓ v β y * Φ y) ⊆ tsupport Φ := tsupport_mul_subset_right
  refine ⟨contDiff_iff_contDiffAt.2 fun y => ?_, hΦ.2.1.mul_left, hs.trans hΦ.2.2⟩
  by_cases hy : y ∈ tsupport Φ
  · exact ((contDiffOn_rowCoef ℓ v β).contDiffAt ((isOpen_rowSet ℓ).mem_nhds (hΦ.2.2 hy))).mul hΦ.1.contDiffAt
  · exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.1 fun h => hy (hs h))

omit [_root_.NumberField.IsTotallyComplex E] in
theorem integrable_infMeasure {f : (Fin a → Cinf E) → ℂ} (h : Continuous f) (hc : HasCompactSupport f) :
    Integrable f (infMeasure E a) :=
  (h.integrable_of_hasCompactSupport hc).smul_measure (by simp)

def famSpan {ι : Type} (ℓ : Fin a) (S S' : Submodule ℂ (Sm E a)) (g : ι → GA E a) :
    Submodule ℂ (ι → (Fin a → Cinf E) → ℂ) :=
  Submodule.span ℂ {f | ∃ F ∈ S, ∃ F' ∈ S', ∃ Φ, IsTest (rowSet E ℓ) Φ ∧ f = fun i => rsInf ℓ F.1 F'.1 Φ (g i)}

theorem famSpan_bound {ι : Type} {ℓ : Fin a} {S S' : Submodule ℂ (Sm E a)} {g : ι → GA E a} {w : ι → ℝ}
    (hS : ∀ F ∈ S, ∀ C₀ : Set (GA E a), IsCompact C₀ → ∃ C : ℝ, ∀ i, ∀ c ∈ C₀, ‖F.1 (g i * c)‖ ≤ C * w i)
    (hS' : ∀ F ∈ S', ∃ C : ℝ, ∀ x, ‖F.1 x‖ ≤ C) : ∀ f ∈ famSpan ℓ S S' g,
      (∀ i, ContDiff ℝ ∞ (f i) ∧ HasCompactSupport (f i)) ∧ ∃ C : ℝ, ∀ i, ∫ y, ‖f i y‖ ∂(infMeasure E a) ≤ C * w i := by
  intro f hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨F, hF, F', hF', Φ, hΦ, rfl⟩ := hf
    refine ⟨fun i => ⟨(isTest_rsInf F F' hΦ _).1, (isTest_rsInf F F' hΦ _).2.1⟩, ?_⟩
    obtain ⟨C, hC⟩ := hS F hF _ (hΦ.2.1.isCompact.image_of_continuousOn ((continuousOn_inv_rowGL ℓ).mono hΦ.2.2))
    obtain ⟨D, hD⟩ := hS' F' hF'
    refine ⟨(∫ y, ‖Φ y‖ ∂(infMeasure E a)) * (D * C), fun i => ?_⟩
    rw [mul_assoc, ← integral_mul_const]
    refine integral_mono_of_nonneg (.of_forall fun _ => norm_nonneg _)
      ((integrable_infMeasure hΦ.1.continuous hΦ.2.1).norm.mul_const _) (.of_forall fun y => ?_)
    by_cases hy : y ∈ tsupport Φ
    · have h1 := hC i _ ⟨y, hy, rfl⟩
      simp only [rsInf, norm_mul, Complex.norm_conj]
      rw [mul_comm, mul_assoc D, mul_comm D]
      exact mul_le_mul_of_nonneg_left (mul_le_mul h1 (hD _) (norm_nonneg _) ((norm_nonneg _).trans h1)) (norm_nonneg _)
    · simp [rsInf, image_eq_zero_of_notMem_tsupport hy]
  | zero => exact ⟨fun i => ⟨contDiff_const, HasCompactSupport.zero⟩, 0, fun i => by simp⟩
  | add f f' _ _ h h' =>
    obtain ⟨h1, C, h2⟩ := h
    obtain ⟨h1', C', h2'⟩ := h'
    refine ⟨fun i => ⟨(h1 i).1.add (h1' i).1, (h1 i).2.add (h1' i).2⟩, C + C', fun i => ?_⟩
    have k := (integrable_infMeasure (h1 i).1.continuous (h1 i).2).norm
    have k' := (integrable_infMeasure (h1' i).1.continuous (h1' i).2).norm
    rw [add_mul]
    refine le_trans ?_ (add_le_add (h2 i) (h2' i))
    rw [← integral_add k k']
    exact integral_mono_of_nonneg (.of_forall fun _ => norm_nonneg _) (k.add k') (.of_forall fun y => norm_add_le _ _)
  | smul z f _ h =>
    obtain ⟨h1, C, h2⟩ := h
    refine ⟨fun i => ⟨(h1 i).1.const_smul z, (h1 i).2.smul_left (f := fun _ => z)⟩, ‖z‖ * C, fun i => ?_⟩
    simp only [Pi.smul_apply, norm_smul, integral_const_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h2 i) (norm_nonneg _)

theorem famSpan_fderiv {ι : Type} {ℓ : Fin a} {S S' : Submodule ℂ (Sm E a)} {g : ι → GA E a}
    (hS : ∀ X, ∀ F ∈ S, lie E a X F ∈ S) (hS' : ∀ X, ∀ F ∈ S', lie E a X F ∈ S') : ∀ f ∈ famSpan ℓ S S' g,
      (∀ i, Differentiable ℝ (f i)) ∧ ∀ v, (fun i y => fderiv ℝ (f i) y v) ∈ famSpan ℓ S S' g := by
  intro f hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨F, hF, F', hF', Φ, hΦ, rfl⟩ := hf
    refine ⟨fun i => (isTest_rsInf F F' hΦ _).1.differentiable (by simp), fun v => ?_⟩
    have e : (fun i y => fderiv ℝ (rsInf ℓ F.1 F'.1 Φ (g i)) y v) =
        ∑ β, (fun i => rsInf ℓ (lie E a (Module.finBasis ℝ (Lie E a) β) F).1 F'.1
          (fun y => rowCoef ℓ v β y * Φ y) (g i)) +
        ∑ β, (fun i => rsInf ℓ F.1 (lie E a (Module.finBasis ℝ (Lie E a) β) F').1
          (fun y => rowCoef ℓ v β y * Φ y) (g i)) +
        fun i => rsInf ℓ F.1 F'.1 (fun y => fderiv ℝ Φ y v) (g i) := by
      funext i y
      simp only [Pi.add_apply, Finset.sum_apply]
      exact fderiv_rsInf F F' hΦ _ y v
    rw [e]
    exact add_mem (add_mem
      (Submodule.sum_mem _ fun β _ => Submodule.subset_span ⟨_, hS _ F hF, F', hF', _, isTest_rowCoef_mul hΦ v β, rfl⟩)
      (Submodule.sum_mem _ fun β _ => Submodule.subset_span ⟨F, hF, _, hS' _ F' hF', _, isTest_rowCoef_mul hΦ v β, rfl⟩))
      (Submodule.subset_span ⟨F, hF, F', hF', _, hΦ.fderiv v, rfl⟩)
  | zero =>
    refine ⟨fun i => differentiable_const _, fun v => ?_⟩
    convert zero_mem (famSpan ℓ S S' g) using 1
    funext i y
    simp
  | add f f' _ _ h h' =>
    refine ⟨fun i => (h.1 i).add (h'.1 i), fun v => ?_⟩
    convert add_mem (h.2 v) (h'.2 v) using 1
    funext i y
    rw [Pi.add_apply, fderiv_add (h.1 i y) (h'.1 i y)]
    rfl
  | smul z f _ h =>
    refine ⟨fun i => (h.1 i).const_smul z, fun v => ?_⟩
    convert Submodule.smul_mem _ z (h.2 v) using 1
    funext i y
    rw [Pi.smul_apply, fderiv_const_smul (h.1 i y)]
    rfl

end GlobalTheory.RSThetaLow
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FourierTransformUniformRapidDecayFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FourierTransformUniformRapidDecayFamily
open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.ThetaPoisson GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped ComplexConjugate nonZeroDivisors ContDiff

noncomputable section

open Real Complex
open scoped FourierTransform

namespace GlobalTheory.FourierDecay

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ}

def pairL (u : Fin n → Cinf E) : (Fin n → Cinf E) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => ∑ i, ∑ w, 2 * (x i w * u i w).re
      map_add' := fun x y => by
        simp only [Pi.add_apply, add_mul, Complex.add_re, mul_add, Finset.sum_add_distrib]
      map_smul' := fun r x => by
        simp only [Pi.smul_apply, Complex.real_smul, mul_assoc, Complex.re_ofReal_mul, RingHom.id_apply,
          smul_eq_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun w _ => by ring }

theorem pairL_apply (u x : Fin n → Cinf E) : pairL u x = ∑ i, ∑ w, 2 * (x i w * u i w).re := rfl

instance isAddHaarMeasure_volume : (volume : Measure (Fin n → Cinf E)).IsAddHaarMeasure :=
  Measure.pi.isAddHaarMeasure _

instance isAddHaarMeasure_infMeasure : (infMeasure E n).IsAddHaarMeasure :=
  Measure.IsAddHaarMeasure.smul _ (by simp) (by simp)

theorem hasFDerivAt_kernel (u x : Fin n → Cinf E) :
    HasFDerivAt (fun y => (𝐞 (-pairL u y) : ℂ))
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (2 * π * I * 𝐞 (-pairL u x))).comp (-pairL u)) x :=
  by
    have h1 := (Real.hasDerivAt_fourierChar (-pairL u x)).hasFDerivAt
    have h2 : HasFDerivAt (fun y => -pairL u y) (-pairL u) x := (pairL u).hasFDerivAt.neg
    exact h1.comp x h2

theorem fderiv_kernel (u x v : Fin n → Cinf E) :
    fderiv ℝ (fun y => (𝐞 (-pairL u y) : ℂ)) x v = -(2 * π * I * (pairL u v : ℂ)) * 𝐞 (-pairL u x) := by
  rw [(hasFDerivAt_kernel u x).fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.one_apply, Complex.real_smul]
  push_cast
  ring

theorem continuous_kernel (u : Fin n → Cinf E) : Continuous (fun y => (𝐞 (-pairL u y) : ℂ)) :=
  continuous_iff_continuousAt.2 fun x => (hasFDerivAt_kernel u x).continuousAt

theorem infFourier_fderiv {f : (Fin n → Cinf E) → ℂ} (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f)
    (v u : Fin n → Cinf E) :
    infFourier (fun y => fderiv ℝ f y v) u = (2 * π * I * (pairL u v : ℂ)) * infFourier f u := by
  have hfc : Continuous f := hf.continuous
  have hd : Differentiable ℝ f := hf.differentiable (by simp)
  have hf'c : Continuous (fun y => fderiv ℝ f y v) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hf's : HasCompactSupport (fun y => fderiv ℝ f y v) :=
    (hs.fderiv (𝕜 := ℝ)).comp_left (g := fun L : (Fin n → Cinf E) →L[ℝ] ℂ => L v) rfl
  have hgc := continuous_kernel u
  have h1 : Integrable (fun x => fderiv ℝ f x v * (𝐞 (-pairL u x) : ℂ)) (infMeasure E n) :=
    (hf'c.mul hgc).integrable_of_hasCompactSupport hf's.mul_right
  have h2 : Integrable (fun x => f x * fderiv ℝ (fun y => (𝐞 (-pairL u y) : ℂ)) x v) (infMeasure E n) := by
    simp only [fderiv_kernel]
    exact (hfc.mul (continuous_const.mul hgc)).integrable_of_hasCompactSupport hs.mul_right
  have h3 : Integrable (fun x => f x * (𝐞 (-pairL u x) : ℂ)) (infMeasure E n) :=
    (hfc.mul hgc).integrable_of_hasCompactSupport hs.mul_right
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable h1 h2 h3 (fun x _ => hd x)
    (fun x _ => (hasFDerivAt_kernel u x).differentiableAt)
  simp only [fderiv_kernel] at key
  have e : ∫ x, f x * (-(2 * π * I * (pairL u v : ℂ)) * (𝐞 (-pairL u x) : ℂ)) ∂infMeasure E n =
      -(2 * π * I * (pairL u v : ℂ)) * ∫ x, f x * (𝐞 (-pairL u x) : ℂ) ∂infMeasure E n := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  show ∫ x, fderiv ℝ f x v * (𝐞 (-pairL u x) : ℂ) ∂infMeasure E n =
    (2 * π * I * (pairL u v : ℂ)) * ∫ x, f x * (𝐞 (-pairL u x) : ℂ) ∂infMeasure E n
  linear_combination key - e


open Classical in
def dirv (k : Fin n × InfinitePlace E × Bool) : Fin n → Cinf E :=
  Pi.single k.1 (Pi.single k.2.1 (if k.2.2 then I else 1))

theorem pairL_dirv (u : Fin n → Cinf E) (k : Fin n × InfinitePlace E × Bool) :
    pairL u (dirv k) = 2 * ((if k.2.2 then I else 1) * u k.1 k.2.1).re := by
  classical
  obtain ⟨i, w, b⟩ := k
  rw [pairL_apply, Finset.sum_eq_single i, Finset.sum_eq_single w]
  · simp [dirv]
  · intro w' _ hw
    simp [dirv, Pi.single_apply, hw]
  · simp
  · intro j _ hj
    simp [dirv, Pi.single_apply, hj]
  · simp

theorem norm_le_sum_pairL (u : Fin n → Cinf E) : ‖u‖ ≤ ∑ k, |pairL u (dirv k)| := by
  have hcoord : ∀ i w, ‖u i w‖ ≤ |pairL u (dirv (i, w, false))| + |pairL u (dirv (i, w, true))| := by
    intro i w
    rw [pairL_dirv, pairL_dirv]
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul, Complex.I_mul_re, abs_mul, abs_neg, abs_two]
    have := Complex.norm_le_abs_re_add_abs_im (u i w)
    nlinarith [abs_nonneg (u i w).re, abs_nonneg (u i w).im]
  have hS : ∑ k, |pairL u (dirv k)| =
      ∑ i, ∑ w, (|pairL u (dirv (i, w, false))| + |pairL u (dirv (i, w, true))|) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Fintype.sum_bool]
    ring
  rw [hS]
  have h0 : 0 ≤ ∑ i, ∑ w, (|pairL u (dirv (i, w, false))| + |pairL u (dirv (i, w, true))|) := by positivity
  refine (pi_norm_le_iff_of_nonneg h0).2 fun i => (pi_norm_le_iff_of_nonneg h0).2 fun w => ?_
  refine (hcoord i w).trans ?_
  have hi := Finset.single_le_sum (f := fun i => ∑ w, (|pairL u (dirv (i, w, false))| + |pairL u (dirv (i, w, true))|))
    (fun i _ => by positivity) (Finset.mem_univ i)
  have hw := Finset.single_le_sum (f := fun w => (|pairL u (dirv (i, w, false))| + |pairL u (dirv (i, w, true))|))
    (fun w _ => by positivity) (Finset.mem_univ w)
  exact hw.trans hi

end GlobalTheory.FourierDecay


open GlobalTheory.FourierDecay in
theorem GlobalTheory.fourier_decay_family : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ) (ι : Type)
    (w : ι → ℝ) (𝒞 : Set (ι → (Fin n → Cinf E) → ℂ)),
    (∀ f ∈ 𝒞, (∀ i, ContDiff ℝ ∞ (f i) ∧ HasCompactSupport (f i)) ∧ ∃ C : ℝ, ∀ i, ∫ y, ‖f i y‖ ∂(infMeasure E n) ≤ C * w i) →
    (∀ f ∈ 𝒞, ∀ v : Fin n → Cinf E, (fun i y => fderiv ℝ (f i) y v) ∈ 𝒞) →
    ∀ M : ℕ, ∀ f ∈ 𝒞, ∃ C : ℝ, ∀ i u, ‖infFourier (f i) u‖ * (1 + ‖u‖) ^ M ≤ C * w i := by
  intro E _ _ _ n ι w 𝒞 hC hD M
  induction M with
  | zero =>
    intro f hf
    obtain ⟨C, hC'⟩ := (hC f hf).2
    refine ⟨C, fun i u => ?_⟩
    rw [pow_zero, mul_one]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq_of_le ?_ (hC' i))
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show ‖f i x * _‖ = ‖f i x‖
    rw [norm_mul, Circle.norm_coe, mul_one]
  | succ M ih =>
    intro f hf
    choose C hC' using fun k : Fin n × InfinitePlace E × Bool => ih _ (hD f hf (dirv k))
    obtain ⟨C₀, h₀⟩ := ih f hf
    refine ⟨C₀ + ∑ k, C k / (2 * π), fun i u => ?_⟩
    obtain ⟨hsm, hcs⟩ := (hC f hf).1 i
    have hrel : ∀ k, ‖infFourier (f i) u‖ * (1 + ‖u‖) ^ M * |pairL u (dirv k)| =
        ‖infFourier (fun y => fderiv ℝ (f i) y (dirv k)) u‖ * (1 + ‖u‖) ^ M / (2 * π) := by
      intro k
      rw [infFourier_fderiv hsm hcs, norm_mul]
      have : ‖(2 * π * I * (pairL u (dirv k) : ℂ))‖ = 2 * π * |pairL u (dirv k)| := by
        simp [norm_mul, Complex.norm_real, abs_of_pos pi_pos]
      rw [this]
      field_simp
    have hN := norm_le_sum_pairL u
    have hA : 0 ≤ ‖infFourier (f i) u‖ * (1 + ‖u‖) ^ M := by positivity
    calc ‖infFourier (f i) u‖ * (1 + ‖u‖) ^ (M + 1)
        = ‖infFourier (f i) u‖ * (1 + ‖u‖) ^ M + ‖infFourier (f i) u‖ * (1 + ‖u‖) ^ M * ‖u‖ := by ring
      _ ≤ ‖infFourier (f i) u‖ * (1 + ‖u‖) ^ M + ‖infFourier (f i) u‖ * (1 + ‖u‖) ^ M * ∑ k, |pairL u (dirv k)| :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left hN hA)
      _ = ‖infFourier (f i) u‖ * (1 + ‖u‖) ^ M +
            ∑ k, ‖infFourier (fun y => fderiv ℝ (f i) y (dirv k)) u‖ * (1 + ‖u‖) ^ M / (2 * π) := by
          rw [Finset.mul_sum]
          exact congrArg _ (Finset.sum_congr rfl fun k _ => hrel k)
      _ ≤ C₀ * w i + ∑ k, C k * w i / (2 * π) :=
          add_le_add (h₀ i u) (Finset.sum_le_sum fun k _ => div_le_div_of_nonneg_right (hC' k i u) (by positivity))
      _ = (C₀ + ∑ k, C k / (2 * π)) * w i := by
          rw [add_mul, Finset.sum_mul]
          congr 1
          exact Finset.sum_congr rfl fun k _ => by ring
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FourierTransformUniformRapidDecayFamilyStatement
open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.ThetaPoisson GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped ComplexConjugate nonZeroDivisors ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierTransform_uniformRapidDecay_family : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ) (ι : Type) (w : ι → ℝ) (𝒞 : Set (ι → (Fin n → Cinf E) → ℂ)), (∀ f ∈ 𝒞, (∀ i, ContDiff ℝ ∞ (f i) ∧ HasCompactSupport (f i)) ∧ ∃ C : ℝ, ∀ i, ∫ y, ‖f i y‖ ∂(infMeasure E n) ≤ C * w i) → (∀ f ∈ 𝒞, ∀ v : Fin n → Cinf E, (fun i y => fderiv ℝ (f i) y v) ∈ 𝒞) → ∀ M : ℕ, ∀ f ∈ 𝒞, ∃ C : ℝ, ∀ i u, ‖infFourier (f i) u‖ * (1 + ‖u‖) ^ M ≤ C * w i := by
  first | exact @GlobalTheory.fourier_decay_family | exact GlobalTheory.fourier_decay_family | (intros; apply GlobalTheory.fourier_decay_family <;> assumption)
end
end

noncomputable section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.ThetaPoisson GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped ComplexConjugate nonZeroDivisors ContDiff
open GlobalTheory.RSTheta GlobalTheory.ShortVecDecay GlobalTheory.Petersson GlobalTheory.CuspQuot Topology GroundTheory.Automorphic.GJMatrix

namespace GlobalTheory.RSThetaLow

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def rsHat (ℓ : Fin a) (φ φ' : GA E a → ℂ) (Φ : (Fin a → Cinf E) → ℂ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ)
    (η : Fin a → Af E) (g : GA E a) (y : Fin a → Ad E) : ℂ :=
  adelicFourierPi E (rsPsi ℓ φ φ' Φ J η g) y


omit [_root_.NumberField.IsTotallyComplex E] in
variable (E a) in
def lowSet : Set (GA E a) := {g | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}

omit [_root_.NumberField.IsTotallyComplex E] in
theorem continuous_absDet : Continuous fun g : GA E a => (ideleModule E (GeneralLinearGroup.det g) : ℝ) :=
  continuous_subtype_val.comp (continuous_ideleModule.comp GeneralLinearGroup.continuous_det)

omit [_root_.NumberField.IsTotallyComplex E] in
theorem absDet_invT (g : GA E a) : (ideleModule E (GeneralLinearGroup.det (invT a (Ad E) g)) : ℝ) =
    (ideleModule E (GeneralLinearGroup.det g) : ℝ)⁻¹ := by
  have h : GeneralLinearGroup.det (invT a (Ad E) g) = GeneralLinearGroup.det g⁻¹ := Units.ext (det_transpose _)
  rw [h, map_inv, map_inv]
  rfl

variable {ℓ : Fin a} {Φ : (Fin a → Cinf E) → ℂ} (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E)

theorem rsPsi_zero (φ φ' : GA E a → ℂ) (hs : tsupport Φ ⊆ rowSet E ℓ) (g : GA E a) : rsPsi ℓ φ φ' Φ J η g 0 = 0 := by
  have h : Φ 0 = 0 := image_eq_zero_of_notMem_tsupport fun h => hs h (Classical.arbitrary _) rfl
  have e : (fun i => pInf E ((0 : Fin a → Ad E) i)) = 0 := funext fun _ => map_zero _
  simp only [rsPsi, thetaFn, rsInf, e, h, mul_zero, zero_mul]

theorem rsPsi_mem (F F' : Sm E a) (hΦ : IsTest (rowSet E ℓ) Φ) (g : GA E a) :
    rsPsi ℓ F.1 F'.1 Φ J η g ∈ schwartzBruhatPi (K := E) (ι := Fin a) :=
  thetaFn_mem ((isTest_rsInf F F' hΦ g).2.1.toSchwartzMap (isTest_rsInf F F' hΦ g).1) J η

theorem rsHat_eq (F F' : Sm E a) (hΦ : IsTest (rowSet E ℓ) Φ) (g : GA E a) (y : Fin a → Ad E) :
    rsHat ℓ F.1 F'.1 Φ J η g y =
      infFourier (rsInf ℓ F.1 F'.1 Φ g) (fun i => pInf E (y i)) * (finiteAdelicChar E (∑ i, η i * pFin E (y i)) : ℂ) *
        (latt a (traceDualIdeal E J)).indicator 1 (fun i => pFin E (y i)) *
        ((finiteMeasurePi E (latt a J)).toReal : ℂ) :=
  adelicFourierPi_thetaFn ((isTest_rsInf F F' hΦ g).2.1.toSchwartzMap (isTest_rsInf F F' hΦ g).1) J η y

theorem stronglyMeasurable_rsHat {F F' : Sm E a} (h : Continuous F.1) (h' : Continuous F'.1)
    (hΦ : IsTest (rowSet E ℓ) Φ) {y : GA E a → Fin a → Ad E} (hy : Continuous y) :
    StronglyMeasurable fun g => rsHat ℓ F.1 F'.1 Φ J η g (y g) := by
  simp only [rsHat_eq J η F F' hΦ]
  have h1 : ∀ i, Continuous fun g => pInf E (y g i) := fun i =>
    CuspRep.continuous_pInf.comp ((continuous_apply i).comp hy)
  have h2 : ∀ i, Continuous fun g => pFin E (y g i) := fun i =>
    (continuous_snd : Continuous (pFin E)).comp ((continuous_apply i).comp hy)
  have h3 : Continuous ((latt a (traceDualIdeal E J)).indicator (1 : (Fin a → Af E) → ℂ)) :=
    (IsClopen.continuous_indicator ⟨isClosed_latt _, isOpen_latt _⟩ continuous_const)
  haveI : SFinite (infMeasure E a) := by unfold infMeasure; infer_instance
  have h4 : Continuous fun p : GA E a × (Fin a → Cinf E) => rsInf ℓ F.1 F'.1 Φ p.1 p.2 *
      (Real.fourierChar (-∑ i, ∑ w, 2 * (p.2 i w * pInf E (y p.1 i) w).re) : ℂ) := by
    refine (continuous_rsInf h h' hΦ.1.continuous hΦ.2.2).mul (continuous_subtype_val.comp
      (Real.continuous_fourierChar.comp (Continuous.neg (continuous_finsetSum _ fun i _ =>
        continuous_finsetSum _ fun w _ => continuous_const.mul (Complex.continuous_re.comp (Continuous.mul ?_ ?_))))))
    · fun_prop
    · exact (continuous_apply w).comp ((h1 i).comp continuous_fst)
  refine ((h4.stronglyMeasurable.integral_prod_right'.mul (Continuous.stronglyMeasurable ?_)).mul
    (h3.comp (continuous_pi h2)).stronglyMeasurable).mul stronglyMeasurable_const
  exact continuous_subtype_val.comp (continuous_finiteAdelicChar.comp
    (continuous_finsetSum _ fun i _ => continuous_const.mul (h2 i)))

theorem exists_norm_rsHat_le {ι : Type} {S S' : Submodule ℂ (Sm E a)} {g : ι → GA E a} {w : ι → ℝ}
    (hL : ∀ X, ∀ F ∈ S, lie E a X F ∈ S) (hL' : ∀ X, ∀ F ∈ S', lie E a X F ∈ S')
    (hS : ∀ F ∈ S, ∀ C₀ : Set (GA E a), IsCompact C₀ → ∃ C : ℝ, ∀ i, ∀ c ∈ C₀, ‖F.1 (g i * c)‖ ≤ C * w i)
    (hS' : ∀ F ∈ S', ∃ C : ℝ, ∀ x, ‖F.1 x‖ ≤ C) {F F' : Sm E a} (hF : F ∈ S) (hF' : F' ∈ S')
    (hΦ : IsTest (rowSet E ℓ) Φ) (M : ℕ) : ∃ C : ℝ, ∀ i y,
      ‖rsHat ℓ F.1 F'.1 Φ J η (g i) y‖ * (1 + ‖fun j => pInf E (y j)‖) ^ M ≤ C * w i := by
  obtain ⟨C, hC⟩ := GlobalTheory.T.fourierTransform_uniformRapidDecay_family E a ι w (famSpan ℓ S S' g) (famSpan_bound hS hS')
    (fun f hf => (famSpan_fderiv hL hL' f hf).2) M _ (Submodule.subset_span ⟨F, hF, F', hF', Φ, hΦ, rfl⟩)
  refine ⟨(finiteMeasurePi E (latt a J)).toReal * C, fun i y => ?_⟩
  have h1 := hC i fun j => pInf E (y j)
  have h2 : ‖(latt a (traceDualIdeal E J)).indicator (1 : (Fin a → Af E) → ℂ) fun i => pFin E (y i)‖ ≤ 1 :=
    (norm_indicator_le_norm_self _ _).trans (by simp)
  rw [rsHat_eq J η F F' hΦ, norm_mul, norm_mul, norm_mul, Circle.norm_coe, mul_one, Complex.norm_real,
    Real.norm_of_nonneg ENNReal.toReal_nonneg, mul_comm _ (ENNReal.toReal _), mul_assoc, mul_assoc _ C]
  refine mul_le_mul_of_nonneg_left (le_trans ?_ h1) ENNReal.toReal_nonneg
  exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (norm_nonneg _) h2) (by positivity)

variable {π π' : CuspSub E a} {φ φ' : Sm E a}

theorem exists_norm_rsHat_le_const (hπ : π.IsUnitary) (hπ' : π'.IsUnitary) (hφ : φ ∈ withSmoothings π)
    (hφ' : φ' ∈ withSmoothings π') (hΦ : IsTest (rowSet E ℓ) Φ) :
    ∃ C : ℝ, ∀ g y, ‖rsHat ℓ φ.1 φ'.1 Φ J η g y‖ ≤ C := by
  obtain ⟨C, h⟩ := exists_norm_rsHat_le J η (g := id) (w := fun _ => 1) (fun X _ => lie_mem_withSmoothings X)
    (fun X _ => lie_mem_withSmoothings X)
    (fun F hF _ _ => (continuous_bounded hπ hF).2.imp fun C h _ _ _ => (h _).trans_eq (mul_one _).symm)
    (fun F hF => (continuous_bounded hπ' hF).2) hφ hφ' hΦ 0
  exact ⟨C, fun g y => by simpa using h g y⟩

theorem exists_tsum_norm_rsHat_le (hπ : π.IsUnitary) (hπ' : π'.IsUnitary) (hφ : φ ∈ withSmoothings π)
    (hφ' : φ' ∈ withSmoothings π') (hΦ : IsTest (rowSet E ℓ) Φ) (K : ℕ) : ∃ C : ℝ, ∀ g ∈ lowSet E a,
      ∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, ‖rsHat ℓ φ.1 φ'.1 Φ J η g
        ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* (g⁻¹).valᵀ)‖ ≤
        C * (ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ K := by
  set N := K + Module.finrank ℝ (Fin a → Cinf E) with hN
  have had : 1 ≤ a * Module.finrank ℚ E := Nat.mul_pos ℓ.pos Module.finrank_pos
  obtain ⟨M, C₁, h₁⟩ := GlobalTheory.T.summable_nonzeroRationalVector_le_shortestVector E a (traceDualIdeal E J) (a * Module.finrank ℚ E * N)
    ((Nat.le_add_left _ K).trans (Nat.le_mul_of_pos_left _ had))
  obtain ⟨C₂, h₂⟩ := exists_norm_rsHat_le J η
    (ι := {p : GA E a × (Fin a → E) // p.2 ≠ 0 ∧
      (fun i => pFin E (((fun j => algebraMap E (Ad E) (p.2 j)) ᵥ* p.1.val) i)) ∈ latt a (traceDualIdeal E J)})
    (g := fun p => invT a (Ad E) p.1.1)
    (w := fun p => (‖fun i => pInf E (((fun j => algebraMap E (Ad E) (p.1.2 j)) ᵥ* p.1.1.val) i)‖ ^
      (a * Module.finrank ℚ E) / (ideleModule E (GeneralLinearGroup.det p.1.1) : ℝ)) ^ N)
    (fun X _ => lie_mem_withSmoothings X) (fun X _ => lie_mem_withSmoothings X)
    (fun F hF C₀ hC₀ => (decays_invT hπ hF _ (isCompact_latt _) _ (hC₀.image continuous_invT) N).imp
      fun C h p c hc => by simpa only [map_mul, invT_invT] using h p.1.1 _ ⟨c, hc, rfl⟩ p.1.2 p.2.1 p.2.2)
    (fun F hF => (continuous_bounded hπ' hF).2) hφ hφ' hΦ M
  refine ⟨|C₁| * |C₂|, fun g hg => ?_⟩
  set δ : ℝ := (ideleModule E (GeneralLinearGroup.det g) : ℝ) with hδ
  have hδ0 : 0 < δ := (ideleModule E _).2
  have h := (h₁ (invT a (Ad E) g) (|C₂| * δ ^ N)
    (fun ξ => rsHat ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* (g⁻¹).valᵀ)) (by positivity)
    (fun ξ hξ => by
      rw [rsHat_eq J η φ φ' hΦ]
      exact mul_eq_zero_of_left (mul_eq_zero_of_right _ (Set.indicator_of_notMem hξ _)) _)
    (fun ξ ξ' h0 hξ' => by
      have h3 := h₂ ⟨(invT a (Ad E) g, ξ'), h0, hξ'⟩ ((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* (g⁻¹).valᵀ)
      simp only [invT_invT, absDet_invT, ← hδ, div_inv_eq_mul, mul_pow, ← pow_mul] at h3
      refine h3.trans ?_
      rw [mul_assoc |C₂|, mul_comm (δ ^ N)]
      exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))).2
  refine h.trans ?_
  rw [mul_assoc]
  refine mul_le_mul (le_abs_self _) (mul_le_mul_of_nonneg_left
    (pow_le_pow_of_le_one hδ0.le hg (Nat.le_add_right _ _)) (abs_nonneg _)) (by positivity) (abs_nonneg _)

theorem poisson_rsPsi (F F' : Sm E a) (hΦ : IsTest (rowSet E ℓ) Φ) (g : GA E a) :
    Summable (fun ξ : Fin a → E => ‖rsPsi ℓ F.1 F'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val)‖) ∧
    Summable (fun ξ : {ξ : Fin a → E // ξ ≠ 0} =>
      ‖rsHat ℓ F.1 F'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* (g⁻¹).valᵀ)‖) ∧
    ∑' ξ : Fin a → E, rsPsi ℓ F.1 F'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val) =
      ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ)⁻¹ * (rsHat ℓ F.1 F'.1 Φ J η g 0 +
        ∑' ξ : {ξ : Fin a → E // ξ ≠ 0},
          rsHat ℓ F.1 F'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* (g⁻¹).valᵀ)) := by
  obtain ⟨h1, h2, h3⟩ := poisson_vecMul g (rsPsi_mem J η F F' hΦ g)
  refine ⟨h1, h2.subtype _, h3.trans ?_⟩
  rw [Complex.ofReal_inv, ← h2.of_norm.tsum_subtype_add_tsum_subtype_compl {0}, tsum_singleton 0 fun ξ : Fin a → E =>
    adelicFourierPi E (rsPsi ℓ F.1 F'.1 Φ J η g) ((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* (g⁻¹).valᵀ)]
  have e : (fun j => algebraMap E (Ad E) ((0 : Fin a → E) j)) = 0 := funext fun _ => map_zero _
  rw [e, zero_vecMul]
  rfl

theorem tsum_rsPsi_eq_tsum_ne_zero (φ φ' : GA E a → ℂ) (hs : tsupport Φ ⊆ rowSet E ℓ) (g : GA E a) :
    ∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, rsPsi ℓ φ φ' Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val) =
      ∑' ξ : Fin a → E, rsPsi ℓ φ φ' Φ J η g ((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val) := by
  refine tsum_subtype_eq_of_support_subset (s := {ξ | ξ ≠ 0})
    (f := fun ξ : Fin a → E => rsPsi ℓ φ φ' Φ J η g ((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val)) ?_
  rintro ξ hξ rfl
  have e : (fun j => algebraMap E (Ad E) ((0 : Fin a → E) j)) = 0 := funext fun _ => map_zero _
  exact hξ (by simp only [e, zero_vecMul, rsPsi_zero J η φ φ' hs])

def partA (ℓ : Fin a) (φ φ' : GA E a → ℂ) (Φ : (Fin a → Cinf E) → ℂ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ)
    (η : Fin a → Af E) (μ : Measure (GA E a)) (𝓕 : Set (GA E a)) (s : ℂ) : ℂ :=
  ∫ g in 𝓕 ∩ lowSet E a, rsHat ℓ φ φ' Φ J η g 0 * ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (s - 1) ∂μ

def partB (ℓ : Fin a) (φ φ' : GA E a → ℂ) (Φ : (Fin a → Cinf E) → ℂ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ)
    (η : Fin a → Af E) (μ : Measure (GA E a)) (𝓕 : Set (GA E a)) (s : ℂ) : ℂ :=
  ∫ g in 𝓕 ∩ lowSet E a, (∑' ξ : {ξ : Fin a → E // ξ ≠ 0},
    rsHat ℓ φ φ' Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* (g⁻¹).valᵀ)) *
      ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (s - 1) ∂μ

variable {μ : Measure (GA E a)} [μ.IsHaarMeasure] {𝓕 : Set (GA E a)}

theorem integrableOn_partA (hπ : π.IsUnitary) (hπ' : π'.IsUnitary) (hφ : φ ∈ withSmoothings π)
    (hφ' : φ' ∈ withSmoothings π') (hΦ : IsTest (rowSet E ℓ) Φ) (h𝓕 : IsFundamentalDomain (ratGL E a).range 𝓕 μ)
    {s : ℂ} (hs : 1 < s.re) : IntegrableOn (fun g => rsHat ℓ φ.1 φ'.1 Φ J η g 0 *
      ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (s - 1)) (𝓕 ∩ lowSet E a) μ := by
  obtain ⟨C, hC⟩ := exists_norm_rsHat_le_const J η hπ hπ' hφ hφ' hΦ
  refine ((GlobalTheory.T.integrableOn_absDet_rpow_le_one_fundamentalDomain E a ℓ.pos μ 𝓕 h𝓕 (s.re - 1) (by linarith)).const_mul C).mono'
    ((stronglyMeasurable_rsHat J η (continuous_bounded hπ hφ).1 (continuous_bounded hπ' hφ').1 hΦ
      continuous_const).aestronglyMeasurable.mul
      ((Complex.measurable_ofReal.comp continuous_absDet.measurable).pow_const _).aestronglyMeasurable)
    (.of_forall fun g => ?_)
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (ideleModule E _).2, Complex.sub_re, Complex.one_re]
  exact mul_le_mul_of_nonneg_right (hC g 0) (Real.rpow_nonneg (ideleModule E _).2.le _)

theorem partB_entire (hπ : π.IsUnitary) (hπ' : π'.IsUnitary) (hφ : φ ∈ withSmoothings π)
    (hφ' : φ' ∈ withSmoothings π') (hΦ : IsTest (rowSet E ℓ) Φ) (h𝓕 : IsFundamentalDomain (ratGL E a).range 𝓕 μ) :
    (∀ x : ℝ, IntegrableOn (fun g => (∑' ξ : {ξ : Fin a → E // ξ ≠ 0},
      ‖rsHat ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* (g⁻¹).valᵀ)‖) *
        (ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x - 1)) (𝓕 ∩ lowSet E a) μ) ∧
    (∀ s : ℂ, IntegrableOn (fun g => (∑' ξ : {ξ : Fin a → E // ξ ≠ 0},
      rsHat ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* (g⁻¹).valᵀ)) *
        ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (s - 1)) (𝓕 ∩ lowSet E a) μ) ∧
    Differentiable ℂ (partB ℓ φ.1 φ'.1 Φ J η μ 𝓕) := by
  haveI : Countable E := Finsupp.Countable.of_moduleFinite (R := ℚ)
  have hm : ∀ ξ : {ξ : Fin a → E // ξ ≠ 0}, AEStronglyMeasurable (fun g : GA E a =>
      rsHat ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* (g⁻¹).valᵀ)) (μ.restrict (𝓕 ∩ lowSet E a)) :=
    fun ξ => (stronglyMeasurable_rsHat J η (continuous_bounded hπ hφ).1 (continuous_bounded hπ' hφ').1 hΦ
      (continuous_const.matrix_vecMul Units.continuous_coe_inv.matrix_transpose)).aestronglyMeasurable
  have hlow : ∀ᵐ g ∂μ.restrict (𝓕 ∩ lowSet E a), g ∈ lowSet E a :=
    ae_restrict_of_ae_restrict_of_subset Set.inter_subset_right
      (ae_restrict_mem (isClosed_le continuous_absDet continuous_const).measurableSet)
  have hδ := hlow.mono (q := fun g => 0 < (ideleModule E (GeneralLinearGroup.det g) : ℝ) ∧
    (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1) fun g hg => ⟨(ideleModule E _).2, hg⟩
  have hi := GlobalTheory.T.integrableOn_absDet_rpow_le_one_fundamentalDomain E a ℓ.pos μ 𝓕 h𝓕 1 one_pos
  simp only [Real.rpow_one] at hi
  have hb := exists_tsum_norm_rsHat_le J η hπ hπ' hφ hφ' hΦ
  have h1 := GlobalTheory.T.mellin_integral_rapidDecay_entire_of_le_one _ _ _ _ continuous_absDet.measurable hδ hi (AEStronglyMeasurable.tsum hm) fun K =>
    (hb K).imp fun C h => hlow.mono fun g hg =>
      (norm_tsum_le_tsum_norm (poisson_rsPsi J η φ φ' hΦ g).2.1).trans (h g hg)
  have h2 := GlobalTheory.T.mellin_integral_rapidDecay_entire_of_le_one _ _ _ _ continuous_absDet.measurable hδ hi
    (Complex.continuous_ofReal.comp_aestronglyMeasurable (AEStronglyMeasurable.tsum fun ξ => (hm ξ).norm)) fun K =>
    (hb K).imp fun C h => hlow.mono fun g hg => by
      rw [Complex.norm_real, Real.norm_of_nonneg (tsum_nonneg fun _ => norm_nonneg _)]
      exact h g hg
  refine ⟨fun x => ((h2.1 ((x - 1 : ℝ) : ℂ)).norm).congr (.of_forall fun g => ?_), fun s => h1.1 _,
    h1.2.comp (differentiable_id.sub_const 1)⟩
  simp only [norm_mul, Complex.norm_real, Complex.norm_cpow_eq_rpow_re_of_pos (ideleModule E _).2, Complex.ofReal_re]
  rw [Real.norm_of_nonneg (tsum_nonneg fun _ => norm_nonneg _)]

theorem integral_low_eq (hπ : π.IsUnitary) (hπ' : π'.IsUnitary) (hφ : φ ∈ withSmoothings π)
    (hφ' : φ' ∈ withSmoothings π') (hΦ : IsTest (rowSet E ℓ) Φ) (h𝓕 : IsFundamentalDomain (ratGL E a).range 𝓕 μ)
    {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun g => (∑' ξ : Fin a → E, rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val)) *
      ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ s) (𝓕 ∩ lowSet E a) μ ∧
    ∫ g in 𝓕 ∩ lowSet E a, (∑' ξ : Fin a → E, rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val)) *
      ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ s ∂μ =
      partA ℓ φ.1 φ'.1 Φ J η μ 𝓕 s + partB ℓ φ.1 φ'.1 Φ J η μ 𝓕 s := by
  have hA := integrableOn_partA J η hπ hπ' hφ hφ' hΦ h𝓕 hs
  have hB := (partB_entire J η hπ hπ' hφ hφ' hΦ h𝓕).2.1 s
  have e : ∀ g : GA E a, (∑' ξ : Fin a → E, rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val)) *
      ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ s =
      rsHat ℓ φ.1 φ'.1 Φ J η g 0 * ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (s - 1) +
      (∑' ξ : {ξ : Fin a → E // ξ ≠ 0},
        rsHat ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* (g⁻¹).valᵀ)) *
        ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (s - 1) := fun g => by
    rw [(poisson_rsPsi J η φ φ' hΦ g).2.2, Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.2 (ideleModule E _).2.ne'),
      Complex.cpow_one]
    ring
  simp only [e]
  exact ⟨hA.add hB, integral_add hA hB⟩

end GlobalTheory.RSThetaLow
